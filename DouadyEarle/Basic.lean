/-
# Conformal naturality and the conformal barycenter (Section 1 and 2)

Statement-level formalization of Douady–Earle, "Conformally natural extension
of homeomorphisms of the circle" (Acta Math. 157 (1986), 23–48).

* The conformal automorphism group `G` of the disk, and its orientation
  preserving subgroup `G₊`             — `diskAut`, `IsDiskAutPlus`, `IsDiskAut`
* The Poisson kernel and harmonic measure of `z ∈ D`
                                        — `poissonKernelDisk`
* Vector fields on `D` associated to a probability density on `S¹`
                                        — `xiField`
* Proposition 1 and Definition: the conformal barycenter
                                        — `conformal_barycenter_existsUnique`,
                                          `conformalBarycenter`
* Lemma 1                              — `lemma1_re_xiField_pos`

We model a (necessarily nonatomic, since it has a continuous density) Borel
probability measure `μ` on `S¹` by its density `ρ : ℝ → ℝ` with respect to
normalized angular Lebesgue measure `dθ/2π`, i.e. `dμ = ρ(θ) dθ/(2π)`; this is
exactly the class of measures that arises as `φ_*(η_z)` for `φ` a homeomorphism
of `S¹` and `η_z` the harmonic measure of a point `z ∈ D` (see `Extension.lean`).
Every statement in this file is proved: it contains no `sorry`.
-/
import Mathlib

open MeasureTheory Real Set Complex

noncomputable section

/-! ## Section 1: the conformal automorphism group of the disk -/

/-- `g_a(z) = (z - a)/(1 - conj(a) z)`, the standard disk automorphism taking
`a` to `0` and `0` to `-a` (formula (1.1)). -/
def diskAut (a z : ℂ) : ℂ := (z - a) / (1 - star a * z)

/-- The orientation-preserving conformal automorphism group `G₊` of `D`:
`z ↦ λ · g_a(z)` with `|λ| = 1` and `|a| < 1`. -/
def IsDiskAutPlus (g : ℂ → ℂ) : Prop :=
  ∃ lam a : ℂ, ‖lam‖ = 1 ∧ ‖a‖ < 1 ∧ ∀ z : ℂ, g z = lam * diskAut a z

/-- The full conformal automorphism group `G` of `D`: `G₊` together with the
orientation-reversing maps `z ↦ (an element of G₊)(star z)`. -/
def IsDiskAut (g : ℂ → ℂ) : Prop :=
  IsDiskAutPlus g ∨ IsDiskAutPlus (fun z => g (star z))

theorem isDiskAutPlus_id : IsDiskAutPlus id := by
  refine ⟨1, 0, by simp, by norm_num, fun z => ?_⟩
  simp [diskAut]

theorem diskAut_maps_disk_to_disk (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskAut a z‖ < 1 := by
  have hna : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnz : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  -- The classical identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`.
  have key : Complex.normSq (1 - star a * z) - Complex.normSq (z - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
    simp only [Complex.star_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have hsq : ‖z - a‖ ^ 2 < ‖1 - star a * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg (z - a)]
  have hpos : 0 < ‖1 - star a * z‖ := by
    nlinarith [norm_nonneg (1 - star a * z), norm_nonneg (z - a)]
  rw [diskAut, norm_div, div_lt_one hpos]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

/-- `g_a` maps the exterior of the disk to the exterior. -/
theorem diskAut_norm_gt_one (a z : ℂ) (ha : ‖a‖ < 1) (hz : 1 < ‖z‖)
    (hden : (1:ℂ) - star a * z ≠ 0) : 1 < ‖diskAut a z‖ := by
  have hna : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnz : 1 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have key : Complex.normSq (1 - star a * z) - Complex.normSq (z - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
    simp only [Complex.star_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have hlt : ‖1 - star a * z‖ < ‖z - a‖ := by
    have h1 : Complex.normSq (1 - star a * z) < Complex.normSq (z - a) := by nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]
  have hpos : 0 < ‖1 - star a * z‖ := norm_pos_iff.2 hden
  rw [diskAut, norm_div, lt_div_iff₀ hpos, one_mul]
  exact hlt

/-- `G₊` is not closed under composition *as a set of functions on all of `ℂ`*:
at the pole of `h` Lean's `x / 0 = 0` makes `g (h z)` take a value inside the
disk, whereas a genuine Möbius automorphism sends `|z| > 1` outside it. -/
theorem isDiskAutPlus_comp_false :
    ¬ ∀ (g h : ℂ → ℂ), IsDiskAutPlus g → IsDiskAutPlus h → IsDiskAutPlus (g ∘ h) := by
  intro hcomp
  have hhalf : IsDiskAutPlus (diskAut (1/2 : ℂ)) := by
    refine ⟨1, 1/2, by simp, ?_, fun z => by simp⟩
    rw [show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  obtain ⟨lam, c, hlam, hc, hform⟩ := hcomp _ _ hhalf hhalf
  have hval : (diskAut (1/2 : ℂ) ∘ diskAut (1/2 : ℂ)) 2 = -(1/2) := by simp [diskAut]
  have h2 : lam * diskAut c 2 = -(1/2) := by rw [← hform 2, hval]
  have hnorm2 : (1:ℝ) < ‖(2:ℂ)‖ := by simp
  by_cases hden : (1:ℂ) - star c * 2 = 0
  · rw [diskAut, hden, div_zero, mul_zero] at h2
    norm_num at h2
  · have hgt := diskAut_norm_gt_one c 2 hc hnorm2 hden
    have : ‖lam * diskAut c 2‖ = ‖diskAut c 2‖ := by rw [norm_mul, hlam, one_mul]
    rw [h2] at this
    rw [show ‖(-(1/2) : ℂ)‖ = 1/2 by
      rw [norm_neg, show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
      norm_num] at this
    linarith [hgt, this]

/-- The denominator of `g_a` does not vanish on the closed disk. -/
theorem diskAut_denom_ne_zero (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - star a * z ≠ 0 := by
  intro hzero
  have h1 : star a * z = 1 := (sub_eq_zero.1 hzero).symm
  have hn : ‖star a * z‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_star] at hn
  nlinarith [norm_nonneg a, norm_nonneg z]

/-- The difference identity for a disk automorphism:
`g_a z₁ - g_a z₂ = (1 - |a|²)(z₁ - z₂)/((1 - āz₁)(1 - āz₂))`.  Everything
quantitative about how `g_a` moves points — the two-sided Lipschitz bounds of
`Estimates.lean`, and the uniform estimate behind Lemma 2 in `Extension.lean` —
is read off this one formula. -/
theorem diskAut_sub_diskAut (a z₁ z₂ : ℂ) (ha : ‖a‖ < 1) (h1 : ‖z₁‖ ≤ 1) (h2 : ‖z₂‖ ≤ 1) :
    diskAut a z₁ - diskAut a z₂
      = ((1 - star a * a) * (z₁ - z₂)) / ((1 - star a * z₁) * (1 - star a * z₂)) := by
  have d1 : (1:ℂ) - star a * z₁ ≠ 0 := diskAut_denom_ne_zero a z₁ ha h1
  have d2 : (1:ℂ) - star a * z₂ ≠ 0 := diskAut_denom_ne_zero a z₂ ha h2
  simp only [diskAut]
  rw [div_sub_div _ _ d1 d2]
  congr 1
  ring

/-- The conjugate denominator likewise. -/
theorem diskAut_denom_star_ne_zero (a w : ℂ) (h1 : (1:ℂ) - star a * w ≠ 0) :
    (1:ℂ) - a * star w ≠ 0 := by
  intro hz
  apply h1
  have := congrArg star hz
  simpa [star_sub, star_mul, star_star, mul_comm] using this

/-- `1 - |a|² ≠ 0` for `a` in the open disk. -/
theorem one_sub_self_mul_star_ne_zero (a : ℂ) (ha : ‖a‖ < 1) : (1:ℂ) - a * star a ≠ 0 := by
  intro hzero
  have h1 : a * star a = 1 := (sub_eq_zero.1 hzero).symm
  have hn : ‖a * star a‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_star] at hn
  nlinarith [norm_nonneg a]

/-- `star λ · λ = 1` for unimodular `λ`. -/
theorem star_mul_self_of_norm_one {lam : ℂ} (hlam : ‖lam‖ = 1) : star lam * lam = 1 := by
  have h : Complex.normSq lam = 1 := by rw [Complex.normSq_eq_norm_sq, hlam]; norm_num
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h, Complex.ofReal_one]

/-- `g_a` is holomorphic on the closed disk. -/
theorem diskAut_differentiableAt (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    DifferentiableAt ℂ (diskAut a) z := by
  unfold diskAut
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (diskAut_denom_ne_zero a z ha hz)

/-- Every element of `G₊` is holomorphic on `D`. -/
theorem isDiskAutPlus_differentiableAt (g : ℂ → ℂ) (hg : IsDiskAutPlus g) (z : ℂ)
    (hz : ‖z‖ < 1) : DifferentiableAt ℂ g z := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  rw [show g = fun w => lam * diskAut a w from funext hform]
  exact (diskAut_differentiableAt a z ha hz.le).const_mul lam

/-- Every element of `G₊` maps `D` into `D`. -/
theorem isDiskAutPlus_mapsTo_disk (g : ℂ → ℂ) (hg : IsDiskAutPlus g) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖g z‖ < 1 := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  rw [hform z, norm_mul, hlam, one_mul]
  exact diskAut_maps_disk_to_disk a z ha hz

/-- `g_a` preserves the unit circle. -/
theorem diskAut_norm_eq_one (a ζ : ℂ) (ha : ‖a‖ < 1) (hζ : ‖ζ‖ = 1) :
    ‖diskAut a ζ‖ = 1 := by
  have hna : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnz : Complex.normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num
  have key : Complex.normSq (1 - star a * ζ) - Complex.normSq (ζ - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq ζ) := by
    simp only [Complex.star_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [hnz] at key
  have heq : ‖ζ - a‖ = ‖1 - star a * ζ‖ := by
    have h2 : Complex.normSq (ζ - a) = Complex.normSq (1 - star a * ζ) := by linarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg (ζ - a), norm_nonneg (1 - star a * ζ)]
  rw [diskAut, norm_div, heq,
    div_self (norm_ne_zero_iff.2 (diskAut_denom_ne_zero a ζ ha hζ.le))]

/-- Elements of `G` map `S¹` onto `S¹`. -/
theorem isDiskAut_maps_circle_to_circle (g : ℂ → ℂ) (hg : IsDiskAut g) (ζ : Circle) :
    g (ζ : ℂ) ∈ Submonoid.unitSphere ℂ := by
  have hplus : ∀ G : ℂ → ℂ, IsDiskAutPlus G → ∀ u : ℂ, ‖u‖ = 1 → ‖G u‖ = 1 := by
    rintro G ⟨lam, a, hlam, ha, hform⟩ u hu
    rw [hform u, norm_mul, hlam, one_mul]
    exact diskAut_norm_eq_one a u ha hu
  refine mem_sphere_zero_iff_norm.2 ?_
  rcases hg with h | h
  · exact hplus g h _ (Circle.norm_coe ζ)
  · have := hplus _ h (star (ζ : ℂ)) (by rw [norm_star]; exact Circle.norm_coe ζ)
    simpa using this

/-- The restriction to `S¹` of an element `g ∈ G`, as a homeomorphism of `S¹`. -/
def diskAutToCircle (g : ℂ → ℂ) (hg : IsDiskAut g) : Circle → Circle :=
  fun ζ => ⟨g (ζ : ℂ), isDiskAut_maps_circle_to_circle g hg ζ⟩

/-- `g_a` takes `a` to `0` and `0` to `-a`. -/
theorem diskAut_self (a : ℂ) (ha : ‖a‖ < 1) : diskAut a a = 0 := by
  simp [diskAut]

theorem diskAut_zero (a : ℂ) : diskAut a 0 = -a := by
  simp [diskAut]

/-! ### The group law on `D̄` -/

theorem one_add_ne_zero_of_norm_lt_one {x : ℂ} (h : ‖x‖ < 1) : (1:ℂ) + x ≠ 0 := by
  intro hz
  have : x = -1 := by linear_combination hz
  rw [this] at h
  simp at h

/-- `g_b` maps the closed disk into the closed disk. -/
theorem diskAut_norm_le_one (b z : ℂ) (hb : ‖b‖ < 1) (hz : ‖z‖ ≤ 1) : ‖diskAut b z‖ ≤ 1 := by
  rcases lt_or_eq_of_le hz with h | h
  · exact le_of_lt (diskAut_maps_disk_to_disk b z hb h)
  · exact le_of_eq (diskAut_norm_eq_one b z hb h)

/-- Möbius addition: `‖(a+b)/(1+a b̄)‖ < 1`. -/
theorem norm_mobius_add_lt_one (a b : ℂ) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖(a + b) / (1 + a * star b)‖ < 1 := by
  have hprod : ‖a * star b‖ < 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hD : (1:ℂ) + a * star b ≠ 0 := one_add_ne_zero_of_norm_lt_one hprod
  have hna : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnb : Complex.normSq b < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg b]
  have key : Complex.normSq (1 + a * star b) - Complex.normSq (a + b)
      = (1 - Complex.normSq a) * (1 - Complex.normSq b) := by
    simp only [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have hlt : ‖a + b‖ < ‖1 + a * star b‖ := by
    have h1 : Complex.normSq (a + b) < Complex.normSq (1 + a * star b) := by nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (a + b), norm_nonneg (1 + a * star b)]
  rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) hlt)]
  exact hlt

/-- Pulling a unimodular factor out of `g_a`. -/
theorem diskAut_mul_left (lam a w : ℂ) (hlam : star lam * lam = 1)
    (hden : (1:ℂ) - star a * (lam * w) ≠ 0) :
    diskAut a (lam * w) = lam * diskAut (star lam * a) w := by
  have hden' : (1:ℂ) - star (star lam * a) * w = 1 - star a * (lam * w) := by
    rw [star_mul, star_star]; ring
  rw [diskAut, diskAut, hden', mul_div_assoc']
  rw [div_eq_div_iff hden hden]
  linear_combination (a * (1 - star a * (lam * w))) * hlam

/-- The composition law for `g_a ∘ g_b` on the closed disk. -/
theorem diskAut_comp_diskAut (a b z : ℂ) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskAut a (diskAut b z)
      = ((1 + a * star b) / (1 + star a * b)) * diskAut ((a + b) / (1 + a * star b)) z := by
  have hprod : ‖a * star b‖ < 1 := by
    rw [norm_mul, norm_star]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hprod' : ‖star a * b‖ < 1 := by
    rw [norm_mul, norm_star]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hD : (1:ℂ) + a * star b ≠ 0 := one_add_ne_zero_of_norm_lt_one hprod
  have hE : (1:ℂ) + star a * b ≠ 0 := one_add_ne_zero_of_norm_lt_one hprod'
  have h1 : (1:ℂ) - star b * z ≠ 0 := diskAut_denom_ne_zero b z hb hz
  have h2 : (1:ℂ) - star a * diskAut b z ≠ 0 :=
    diskAut_denom_ne_zero a _ ha (diskAut_norm_le_one b z hb hz)
  have hc : ‖(a + b) / (1 + a * star b)‖ < 1 := norm_mobius_add_lt_one a b ha hb
  have h3 : (1:ℂ) - star ((a + b) / (1 + a * star b)) * z ≠ 0 :=
    diskAut_denom_ne_zero _ z hc hz
  have hstarc : star ((a + b) / (1 + a * star b)) = (star a + star b) / (1 + star a * b) := by
    rw [star_div₀, star_add, star_add, star_mul, star_star, star_one]
    ring_nf
  simp only [diskAut] at h2
  rw [hstarc] at h3
  have hkey2 : ((1 - star b * z) - star a * (z - b)) / (1 - star b * z)
      = 1 - star a * ((z - b) / (1 - star b * z)) := by
    rw [sub_div, div_self h1, mul_div_assoc]
  have h2' : (1 - star b * z) - star a * (z - b) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hkey2
    exact h2 hkey2.symm
  have hkey3 : ((1 + star a * b) - (star a + star b) * z) / (1 + star a * b)
      = 1 - ((star a + star b) / (1 + star a * b)) * z := by
    rw [sub_div, div_self hE, div_mul_eq_mul_div]
  have h3' : (1 + star a * b) - (star a + star b) * z ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hkey3
    exact h3 hkey3.symm
  have h3'' : (1 + star a * b) - (star a + star b) * z ≠ 0 := h3'
  have hquot : ∀ N M c : ℂ, c ≠ 0 → M ≠ 0 → (N / c) / (M / c) = N / M := by
    intro N M c hc hM
    rw [div_div_div_cancel_right₀]
    exact hc
  have hnum : ((z - b) - a * (1 - star b * z)) / (1 - star b * z)
      = (z - b) / (1 - star b * z) - a := by
    rw [sub_div, mul_div_assoc, div_self h1, mul_one]
  have hnum2 : ((1 + a * star b) * z - (a + b)) / (1 + a * star b)
      = z - (a + b) / (1 + a * star b) := by
    rw [sub_div, mul_comm, mul_div_assoc, div_self hD, mul_one]
  have hL : diskAut a (diskAut b z)
      = ((z - b) - a * (1 - star b * z)) / ((1 - star b * z) - star a * (z - b)) := by
    rw [diskAut, diskAut, ← hnum, ← hkey2, hquot _ _ _ h1 h2']
  have hR : ((1 + a * star b) / (1 + star a * b)) * diskAut ((a + b) / (1 + a * star b)) z
      = ((1 + a * star b) * z - (a + b)) / ((1 + star a * b) - (star a + star b) * z) := by
    rw [diskAut, hstarc, ← hkey3, ← hnum2]
    field_simp
  rw [hL, hR, div_eq_div_iff h2' h3']
  ring

/-- The complex derivative of `g_a` on the closed disk. -/
theorem hasDerivAt_diskAut {a : ℂ} (ha : ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasDerivAt (diskAut a) ((1 - star a * a) / (1 - star a * w) ^ 2) w := by
  have hden : (1 : ℂ) - star a * w ≠ 0 := diskAut_denom_ne_zero a w ha hw
  have hc : HasDerivAt (fun y : ℂ => y - a) 1 w := (hasDerivAt_id w).sub_const a
  have hd : HasDerivAt (fun y : ℂ => 1 - star a * y) (-star a) w := by
    simpa using ((hasDerivAt_id w).const_mul (star a)).const_sub 1
  have h := hc.fun_div hd hden
  convert h using 1
  · rfl
  · congr 1
    ring

/-- `g_a ∘ g_{-a} = id` on the closed disk: the inverse of `g_a` in `G₊` is `g_{-a}`. -/
theorem diskAut_neg_left_inv {a : ℂ} (ha : ‖a‖ < 1) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    diskAut a (diskAut (-a) u) = u := by
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  have h1 : (1 : ℂ) - star (-a) * u ≠ 0 := diskAut_denom_ne_zero (-a) u hna hu
  have hA : (1 : ℂ) + star a * u ≠ 0 := by
    intro hz; apply h1; rw [star_neg]; linear_combination hz
  have hA' : (1 : ℂ) + u * star a ≠ 0 := by rwa [mul_comm u (star a)]
  have h2 : (1 : ℂ) - a * star a ≠ 0 := one_sub_self_mul_star_ne_zero a ha
  have h2' : (1 : ℂ) - star a * a ≠ 0 := by rwa [mul_comm (star a) a]
  have hnum : diskAut (-a) u = (u + a) / (1 + star a * u) := by
    simp only [diskAut, star_neg]
    congr 1 <;> ring
  have hd2 : (1 : ℂ) - star a * ((u + a) / (1 + star a * u))
      = (1 - a * star a) / (1 + star a * u) := by
    rw [eq_div_iff hA]; field_simp; ring
  have hn2 : (u + a) / (1 + star a * u) - a = u * (1 - a * star a) / (1 + star a * u) := by
    rw [eq_div_iff hA]; field_simp; ring
  rw [diskAut, hnum, hd2, hn2]
  field_simp

/-! ### Inverses in `G₊`, and the induced homeomorphism of `S¹` -/

/-- The inverse of `z ↦ lam · g_a(z)` is `w ↦ g_{-a}(lam⁻¹ w)`, and it is again
in `G₊`. -/
theorem isDiskAutPlus_inv (g : ℂ → ℂ) (hg : IsDiskAutPlus g) :
    ∃ g' : ℂ → ℂ, IsDiskAutPlus g' ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → g' (g z) = z) ∧ (∀ w : ℂ, ‖w‖ ≤ 1 → g (g' w) = w) := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hlam' : star lam * lam = 1 := star_mul_self_of_norm_one hlam
  have hlam'' : lam * star lam = 1 := by rw [mul_comm]; exact hlam'
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  refine ⟨fun w => diskAut (-a) (star lam * w), ?_, ?_, ?_⟩
  · refine ⟨star lam, -(lam * a), by rwa [norm_star], ?_, fun w => ?_⟩
    · rw [norm_neg, norm_mul, hlam, one_mul]; exact ha
    · have hd : (1:ℂ) - star (-(lam * a)) * w = 1 - star (-a) * (star lam * w) := by
        simp only [star_neg, star_mul]
        ring
      simp only [diskAut]
      rw [hd, ← mul_div_assoc]
      congr 1
      linear_combination (-a) * hlam'
  · intro z hz
    show diskAut (-a) (star lam * g z) = z
    rw [hform z, ← mul_assoc, hlam', one_mul]
    have h := diskAut_neg_left_inv (a := -a) hna (u := z) hz
    rw [neg_neg] at h
    exact h
  · intro w hw
    show g (diskAut (-a) (star lam * w)) = w
    have hsw : ‖star lam * w‖ ≤ 1 := by rw [norm_mul, norm_star, hlam, one_mul]; exact hw
    rw [hform, diskAut_neg_left_inv ha hsw, ← mul_assoc, hlam'', one_mul]

/-- The restriction of an element of `G₊` to `S¹` is a bijection of `S¹`. -/
theorem bijective_diskAutToCircle (g : ℂ → ℂ) (hgp : IsDiskAutPlus g) (hg : IsDiskAut g) :
    Function.Bijective (diskAutToCircle g hg) := by
  obtain ⟨g', hg'p, hleft, hright⟩ := isDiskAutPlus_inv g hgp
  constructor
  · intro ζ₁ ζ₂ hz
    have h : g (ζ₁ : ℂ) = g (ζ₂ : ℂ) := congrArg Subtype.val hz
    have h1 := hleft (ζ₁ : ℂ) (by simp)
    have h2 := hleft (ζ₂ : ℂ) (by simp)
    exact Subtype.ext (by rw [← h1, ← h2, h])
  · intro η
    have hmem : g' (η : ℂ) ∈ Submonoid.unitSphere ℂ :=
      isDiskAut_maps_circle_to_circle g' (Or.inl hg'p) η
    refine ⟨⟨g' (η : ℂ), hmem⟩, Subtype.ext ?_⟩
    exact hright (η : ℂ) (by simp)

theorem coe_circle_inv (ζ : Circle) : ((ζ⁻¹ : Circle) : ℂ) = star ((ζ : Circle) : ℂ) := by
  rw [Circle.coe_inv]
  exact (Complex.inv_eq_conj (Circle.norm_coe ζ)).trans rfl

/-- The restriction to `S¹` of *any* element of `G` is a bijection of `S¹`.  In
the orientation-reversing case it is the orientation-preserving one composed
with `ζ ↦ ζ⁻¹`, which is a bijection of `S¹` because `S¹` is a group. -/
theorem bijective_diskAutToCircle_of_isDiskAut (g : ℂ → ℂ) (hg : IsDiskAut g) :
    Function.Bijective (diskAutToCircle g hg) := by
  rcases hg with hp | hm
  · exact bijective_diskAutToCircle g hp _
  · have hcomp : diskAutToCircle g (Or.inr hm)
        = (diskAutToCircle (fun z => g (star z)) (Or.inl hm)) ∘ (fun ζ : Circle => ζ⁻¹) := by
      funext ζ
      refine Subtype.ext ?_
      show g ((ζ : ℂ)) = g (star ((ζ⁻¹ : Circle) : ℂ))
      rw [coe_circle_inv, star_star]
    have hb : Function.Bijective (diskAutToCircle g (Or.inr hm)) := by
      rw [hcomp]
      exact (bijective_diskAutToCircle _ hm _).comp inv_involutive.bijective
    exact hb

theorem diskAutToCircle_coe (g : ℂ → ℂ) (hg : IsDiskAut g) (ζ : Circle) :
    g (ζ : ℂ) = ((diskAutToCircle g hg ζ : Circle) : ℂ) := rfl

/-- An element of `G₊` has nonvanishing derivative on the closed disk. -/
theorem hasDerivAt_isDiskAutPlus (g : ℂ → ℂ) (hg : IsDiskAutPlus g) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ c : ℂ, c ≠ 0 ∧ HasDerivAt g c w := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hden : (1 : ℂ) - star a * w ≠ 0 := diskAut_denom_ne_zero a w ha hw
  have hnum : (1 : ℂ) - star a * a ≠ 0 := by
    have := one_sub_self_mul_star_ne_zero a ha
    rwa [mul_comm a (star a)] at this
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h] at hlam; simp at hlam
  refine ⟨lam * ((1 - star a * a) / (1 - star a * w) ^ 2), ?_, ?_⟩
  · exact mul_ne_zero hlam0 (div_ne_zero hnum (pow_ne_zero 2 hden))
  · have h := (hasDerivAt_diskAut ha hw).const_mul lam
    rw [show g = fun z => lam * diskAut a z from funext hform]
    exact h

theorem deriv_isDiskAutPlus_ne_zero (g : ℂ → ℂ) (hg : IsDiskAutPlus g) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    deriv g w ≠ 0 := by
  obtain ⟨c, hc, hd⟩ := hasDerivAt_isDiskAutPlus g hg hw
  rw [hd.deriv]; exact hc

/-- `G₊` is a group under composition **as a set of maps of `D̄`**: `g ∘ h`
agrees on the closed disk with an element of `G₊`, namely `λ g_c` with
`c = (a + λ₂b)/(λ₂ + a b̄)` and `λ = λ₁(λ₂ + a b̄)/(1 + ā λ₂ b)`, for
`g = λ₁ g_a` and `h = λ₂ g_b`.

It is *not* closed under composition as a set of functions on all of `ℂ`: at the
pole of `h` the junk value `x / 0 = 0` puts `g (h z)` inside the disk.  See
`isDiskAutPlus_comp_false`. -/
theorem isDiskAutPlus_comp {g h : ℂ → ℂ} (hg : IsDiskAutPlus g) (hh : IsDiskAutPlus h) :
    ∃ f : ℂ → ℂ, IsDiskAutPlus f ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → (g ∘ h) z = f z := by
  obtain ⟨lam₁, a, hlam₁, ha, hgform⟩ := hg
  obtain ⟨lam₂, b, hlam₂, hb, hhform⟩ := hh
  have hL2 : star lam₂ * lam₂ = 1 := star_mul_self_of_norm_one hlam₂
  set a' : ℂ := star lam₂ * a with ha'def
  have ha' : ‖a'‖ < 1 := by
    rw [ha'def, norm_mul, norm_star, hlam₂, one_mul]; exact ha
  have hprod : ‖a' * star b‖ < 1 := by
    rw [norm_mul, norm_star]; nlinarith [norm_nonneg a', norm_nonneg b]
  have hD : (1:ℂ) + a' * star b ≠ 0 := one_add_ne_zero_of_norm_lt_one hprod
  have hconj : (1:ℂ) + star a' * b = star (1 + a' * star b) := by
    simp only [star_add, star_one, star_mul, star_star]
    ring
  set c : ℂ := (a' + b) / (1 + a' * star b) with hcdef
  have hc : ‖c‖ < 1 := norm_mobius_add_lt_one a' b ha' hb
  set lam : ℂ := lam₁ * lam₂ * ((1 + a' * star b) / (1 + star a' * b)) with hlamdef
  have hlam : ‖lam‖ = 1 := by
    rw [hlamdef, norm_mul, norm_mul, hlam₁, hlam₂, one_mul, one_mul, norm_div, hconj, norm_star,
      div_self (norm_ne_zero_iff.2 hD)]
  refine ⟨fun z => lam * diskAut c z, ⟨lam, c, hlam, hc, fun z => rfl⟩, fun z hz => ?_⟩
  have hbz : ‖diskAut b z‖ ≤ 1 := diskAut_norm_le_one b z hb hz
  have hden : (1:ℂ) - star a * (lam₂ * diskAut b z) ≠ 0 := by
    refine diskAut_denom_ne_zero a _ ha ?_
    rw [norm_mul, hlam₂, one_mul]; exact hbz
  calc (g ∘ h) z = lam₁ * diskAut a (lam₂ * diskAut b z) := by
        simp only [Function.comp_apply, hgform, hhform]
    _ = lam₁ * (lam₂ * diskAut a' (diskAut b z)) := by
        rw [diskAut_mul_left lam₂ a _ hL2 hden]
    _ = lam₁ * lam₂ * (((1 + a' * star b) / (1 + star a' * b)) * diskAut c z) := by
        rw [diskAut_comp_diskAut a' b z ha' hb hz]; ring
    _ = lam * diskAut c z := by rw [hlamdef]; ring

/-! ### Conformal naturality of the Möbius difference quotient

The algebraic identity behind every naturality statement in the paper: for
`g = λ g_a` in `G₊`, `g_{g(w)} ∘ g = c · g_w` with `|c| = 1`.  Both the
conformal naturality of the barycenter (Section 2) and that of the barycentric
equation (3.1) reduce to it. -/

theorem star_diskAut (a w : ℂ) : star (diskAut a w) = (star w - star a) / (1 - a * star w) := by
  simp [diskAut, star_div₀, star_sub, star_mul, mul_comm]

theorem diskAut_sub (lam a w u : ℂ) (h1 : (1:ℂ) - star a * w ≠ 0)
    (h2 : (1:ℂ) - star a * u ≠ 0) :
    lam * diskAut a u - lam * diskAut a w
      = lam * (1 - a * star a) * (u - w) / ((1 - star a * u) * (1 - star a * w)) := by
  have h1' : (1:ℂ) - w * star a ≠ 0 := by rwa [mul_comm]
  have h2' : (1:ℂ) - u * star a ≠ 0 := by rwa [mul_comm]
  simp only [diskAut]
  field_simp
  ring

theorem diskAut_one_sub (lam a w u : ℂ) (hlam : star lam * lam = 1)
    (h1 : (1:ℂ) - star a * w ≠ 0) (h2 : (1:ℂ) - star a * u ≠ 0)
    (h1' : (1:ℂ) - a * star w ≠ 0) :
    1 - star (lam * diskAut a w) * (lam * diskAut a u)
      = (1 - a * star a) * (1 - star w * u) / ((1 - a * star w) * (1 - star a * u)) := by
  have h2' : (1:ℂ) - u * star a ≠ 0 := by rwa [mul_comm]
  have h1'' : (1:ℂ) - star w * a ≠ 0 := by rwa [mul_comm]
  have hstep : 1 - star (lam * diskAut a w) * (lam * diskAut a u)
      = 1 - star (diskAut a w) * diskAut a u := by
    rw [star_mul]
    linear_combination (-(star (diskAut a w) * diskAut a u)) * hlam
  rw [hstep, star_diskAut, diskAut]
  field_simp
  ring

/-- **Conformal naturality of `g_w`**: `g_{g(w)}(g(u)) = c · g_w(u)`, where
`c = λ·conj(1 - āw)/(1 - āw)` is unimodular. -/
theorem diskAut_apply_diskAut (lam a w u : ℂ) (hlam : star lam * lam = 1)
    (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ ≤ 1) :
    diskAut (lam * diskAut a w) (lam * diskAut a u)
      = lam * ((1 - a * star w) / (1 - star a * w)) * diskAut w u := by
  have h1 := diskAut_denom_ne_zero a w ha hw.le
  have h2 := diskAut_denom_ne_zero a u ha hu
  have h3 := diskAut_denom_ne_zero w u hw hu
  have h1' := diskAut_denom_star_ne_zero a w h1
  have ha2 := one_sub_self_mul_star_ne_zero a ha
  rw [diskAut, diskAut_sub lam a w u h1 h2, diskAut_one_sub lam a w u hlam h1 h2 h1', diskAut]
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div]
  field_simp

/-! ## Harmonic measure and the Poisson kernel of the disk -/

/-- The Poisson kernel of the disk at `z`, evaluated at a boundary point `ζ`:
`(1 - |z|²)/|z - ζ|²`. -/
def poissonKernelDisk (z ζ : ℂ) : ℝ := (1 - ‖z‖ ^ 2) / ‖z - ζ‖ ^ 2

/-- The harmonic measure `η_z` of `z ∈ D`, i.e. the map that integrates a
(continuous, say) function `F : S¹ → ℂ` against `η_z`:
`⨍ F dη_z = (2π)⁻¹ ∫₀^{2π} F(e^{iθ}) P_z(e^{iθ}) dθ`. -/
def harmonicMeasureAvg (z : ℂ) (F : Circle → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
    F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)

/-- At the centre, harmonic measure is the uniform measure: `P_0 ≡ 1` on `S¹`,
so `⨍ F dη_0` is the plain mean of `F`. -/
theorem harmonicMeasureAvg_zero_eq (F : Circle → ℂ) :
    harmonicMeasureAvg 0 F
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), F (Circle.exp θ) := by
  rw [harmonicMeasureAvg]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [poissonKernelDisk]

/-- `η_z` is a probability measure: `⨍ 1 dη_z = 1`. -/
theorem harmonicMeasureAvg_const_one (z : ℂ) (hz : ‖z‖ < 1) :
    harmonicMeasureAvg z (fun _ => 1) = 1 := by
  -- This is the Poisson integral formula of `Mathlib.Analysis.Complex.Poisson`
  -- applied to the constant function `1` on the unit disk.
  have hzb : z ∈ Metric.ball (0:ℂ) 1 := by simpa using hz
  have hconst : DiffContOnCl ℂ (fun _ : ℂ => (1:ℂ)) (Metric.ball (0:ℂ) 1) :=
    (differentiable_const (1:ℂ)).diffContOnCl
  have key := hconst.circleAverage_poissonKernel_smul hzb
  rw [Real.circleAverage_def] at key
  -- The paper's kernel `(1 - |z|²)/|z - ζ|²` on `S¹` is Mathlib's `poissonKernel 0 z`.
  have hint : ∀ θ : ℝ,
      (1:ℂ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)
        = (poissonKernel 0 z • (fun _ : ℂ => (1:ℂ))) (circleMap 0 1 θ) := by
    intro θ
    simp [poissonKernelDisk, poissonKernel, circleMap, Circle.coe_exp,
      norm_sub_rev, Complex.real_smul]
  rw [harmonicMeasureAvg]
  simp only [hint]
  rw [← Complex.real_smul]
  exact key

/-- **Poisson integral formula**: `⨍ f dη_z = f z` for `f` holomorphic on `D`
and continuous on `D̄`.  (`harmonicMeasureAvg_const_one` is the case `f ≡ 1`.) -/
theorem harmonicMeasureAvg_eq_of_diffContOnCl (f : ℂ → ℂ) (z : ℂ) (hz : ‖z‖ < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball (0:ℂ) 1)) :
    harmonicMeasureAvg z (fun ζ => f (ζ : ℂ)) = f z := by
  have hzb : z ∈ Metric.ball (0:ℂ) 1 := by simpa using hz
  have key := hf.circleAverage_poissonKernel_smul hzb
  rw [Real.circleAverage_def] at key
  have hint : ∀ θ : ℝ, f ((Circle.exp θ : ℂ)) * (poissonKernelDisk z (Circle.exp θ) : ℂ)
      = (poissonKernel 0 z • f) (circleMap 0 1 θ) := by
    intro θ
    simp [poissonKernelDisk, poissonKernel, circleMap, Circle.coe_exp, norm_sub_rev,
      Complex.real_smul, mul_comm]
  rw [harmonicMeasureAvg]
  simp only [hint]
  rw [← Complex.real_smul]
  exact key

/-- Elements of `G₊` are holomorphic on `D` and continuous on `D̄`. -/
theorem isDiskAutPlus_diffContOnCl (g : ℂ → ℂ) (hg : IsDiskAutPlus g) :
    DiffContOnCl ℂ g (Metric.ball (0:ℂ) 1) := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  refine DifferentiableOn.diffContOnCl ?_
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by
    rw [closure_ball (0:ℂ) one_ne_zero] at hz
    simpa using hz
  rw [show g = fun w => lam * diskAut a w from funext hform]
  exact ((diskAut_differentiableAt a z ha hz').const_mul lam).differentiableWithinAt

/-- Pulling a constant out of `⨍ · dη_z`. -/
theorem harmonicMeasureAvg_const_mul (z c : ℂ) (F : Circle → ℂ) :
    harmonicMeasureAvg z (fun ζ => c * F ζ) = c * harmonicMeasureAvg z F := by
  simp only [harmonicMeasureAvg, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- `G` maps `D` into `D`. -/
theorem isDiskAut_mapsTo_disk (g : ℂ → ℂ) (hg : IsDiskAut g) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖g z‖ < 1 := by
  rcases hg with h | h
  · exact isDiskAutPlus_mapsTo_disk g h z hz
  · have := isDiskAutPlus_mapsTo_disk _ h (star z) (by rwa [norm_star])
    simpa using this

/-- `g_{w̄}(ū) = conj(g_w(u))`, the mirror of `diskAut_apply_diskAut` used for
the orientation-reversing elements of `G`. -/
theorem diskAut_star (w u : ℂ) : diskAut (star w) (star u) = star (diskAut w u) := by
  rw [star_diskAut, diskAut, star_star]

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, (starRingEnd ℂ) (f x) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- `⨍ · dη_z` commutes with conjugation, the Poisson kernel being real. -/
theorem harmonicMeasureAvg_star (z : ℂ) (F : Circle → ℂ) :
    harmonicMeasureAvg z (fun ζ => star (F ζ)) = star (harmonicMeasureAvg z F) := by
  simp only [harmonicMeasureAvg, Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [← intervalIntegral_conj]
  simp only [map_mul, Complex.conj_ofReal]

/-- Naturality of harmonic measure holds for holomorphic boundary data: both
sides equal `f (g z)` by the Poisson integral formula, applied to `f` at `g z`
and to `f ∘ g` at `z`. -/
theorem harmonicMeasureAvg_naturality_holomorphic (g : ℂ → ℂ) (hg : IsDiskAutPlus g)
    (z : ℂ) (hz : ‖z‖ < 1) (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (Metric.ball (0:ℂ) 1)) :
    harmonicMeasureAvg (g z) (fun ζ => f (ζ : ℂ))
      = harmonicMeasureAvg z (fun ζ => f (g (ζ : ℂ))) := by
  have hgz : ‖g z‖ < 1 := isDiskAutPlus_mapsTo_disk g hg z hz
  rw [harmonicMeasureAvg_eq_of_diffContOnCl f (g z) hgz hf]
  have hcomp : DiffContOnCl ℂ (f ∘ g) (Metric.ball (0:ℂ) 1) := by
    refine hf.comp (isDiskAutPlus_diffContOnCl g hg) ?_
    intro w hw
    exact mem_ball_zero_iff.2 (isDiskAutPlus_mapsTo_disk g hg w (mem_ball_zero_iff.1 hw))
  have := harmonicMeasureAvg_eq_of_diffContOnCl (f ∘ g) z hz hcomp
  simpa [Function.comp] using this.symm

/-- ... and hence for conjugates of holomorphic boundary data. -/
theorem harmonicMeasureAvg_naturality_conj (g : ℂ → ℂ) (hg : IsDiskAutPlus g)
    (z : ℂ) (hz : ‖z‖ < 1) (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (Metric.ball (0:ℂ) 1)) :
    harmonicMeasureAvg (g z) (fun ζ => star (f (ζ : ℂ)))
      = harmonicMeasureAvg z (fun ζ => star (f (g (ζ : ℂ)))) := by
  rw [harmonicMeasureAvg_star, harmonicMeasureAvg_star,
    harmonicMeasureAvg_naturality_holomorphic g hg z hz f hf]

/-- The integrand of the barycentric equation (3.1) is continuous. -/
theorem continuous_diskAut_comp (w : ℂ) (hw : ‖w‖ < 1) (φ : Circle → Circle)
    (hφ : Continuous φ) : Continuous fun u : Circle => diskAut w ((φ u : ℂ)) := by
  have hden : ∀ u : Circle, (1 : ℂ) - star w * ((φ u : ℂ)) ≠ 0 := fun u =>
    diskAut_denom_ne_zero w _ hw (le_of_eq (Circle.norm_coe (φ u)))
  simp only [diskAut]
  exact Continuous.div (by fun_prop) (by fun_prop) hden

theorem continuous_poissonKernelDisk_exp {z : ℂ} (hz : ‖z‖ < 1) :
    Continuous fun θ : ℝ => poissonKernelDisk z (Circle.exp θ) := by
  have hne : ∀ θ : ℝ, z - (Circle.exp θ : ℂ) ≠ 0 := by
    intro θ hzero
    have : z = (Circle.exp θ : ℂ) := by linear_combination hzero
    rw [this, Circle.norm_coe] at hz
    exact lt_irrefl 1 hz
  simp only [poissonKernelDisk]
  apply Continuous.div continuous_const
  · exact (continuous_norm.comp (continuous_const.sub Circle.exp.continuous.subtype_val)).pow 2
  · intro θ
    simpa [pow_eq_zero_iff] using hne θ

theorem poissonKernelDisk_nonneg {z ζ : ℂ} (hz : ‖z‖ < 1) : 0 ≤ poissonKernelDisk z ζ := by
  apply div_nonneg
  · nlinarith [norm_nonneg z]
  · positivity

/-- On the circle the Poisson kernel of an interior point is *strictly*
positive.  This is what makes the vanishing of a weighted integral force the
weight to vanish pointwise — see `norm_harmonicMeasureAvg_sq_lt_one`. -/
theorem poissonKernelDisk_pos {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ = 1) :
    0 < poissonKernelDisk z ζ := by
  have hne : z - ζ ≠ 0 := by
    intro h
    have hzz : z = ζ := by linear_combination h
    rw [hzz, hζ] at hz
    exact lt_irrefl 1 hz
  have hnp : 0 < ‖z - ζ‖ := norm_pos_iff.2 hne
  rw [poissonKernelDisk]
  apply div_pos (by nlinarith [norm_nonneg z]) (by positivity)

/-- The Poisson kernel integrates to `2π`. -/
theorem integral_poissonKernel {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), poissonKernelDisk z (Circle.exp θ) = 2 * Real.pi := by
  have hint : IntervalIntegrable (fun θ : ℝ => poissonKernelDisk z (Circle.exp θ))
      volume 0 (2 * Real.pi) := (continuous_poissonKernelDisk_exp hz).intervalIntegrable _ _
  have hre := Complex.ofRealCLM.intervalIntegral_comp_comm hint
  simp only [Complex.ofRealCLM_apply] at hre
  have h1 := harmonicMeasureAvg_const_one z hz
  rw [harmonicMeasureAvg] at h1
  simp only [one_mul] at h1
  rw [hre] at h1
  have h2 : ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
      poissonKernelDisk z (Circle.exp θ) : ℝ) = 1 := by exact_mod_cast h1
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  field_simp at h2
  linarith

/-- The integrand of `⨍ · dη_z` is interval integrable for continuous `F`. -/
theorem integrable_harmonicMeasureAvg {z : ℂ} (hz : ‖z‖ < 1) {F : Circle → ℂ}
    (hF : Continuous F) :
    IntervalIntegrable (fun θ : ℝ => F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  ((hF.comp Circle.exp.continuous).mul
    (Complex.continuous_ofReal.comp (continuous_poissonKernelDisk_exp hz))).intervalIntegrable _ _

theorem harmonicMeasureAvg_add {z : ℂ} (hz : ‖z‖ < 1) {F G : Circle → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    harmonicMeasureAvg z (fun ζ => F ζ + G ζ)
      = harmonicMeasureAvg z F + harmonicMeasureAvg z G := by
  simp only [harmonicMeasureAvg]
  rw [← mul_add, ← intervalIntegral.integral_add (integrable_harmonicMeasureAvg hz hF)
    (integrable_harmonicMeasureAvg hz hG)]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring

theorem harmonicMeasureAvg_sub {z : ℂ} (hz : ‖z‖ < 1) {F G : Circle → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    harmonicMeasureAvg z (fun ζ => F ζ - G ζ)
      = harmonicMeasureAvg z F - harmonicMeasureAvg z G := by
  have hneg : harmonicMeasureAvg z (fun ζ => -G ζ) = -harmonicMeasureAvg z G := by
    have := harmonicMeasureAvg_const_mul z (-1) G
    simpa using this
  have := harmonicMeasureAvg_add hz hF hG.fun_neg
  simp only [hneg] at this
  simpa [sub_eq_add_neg] using this

/-- `⨍ · dη_z` is bounded by the sup norm. -/
theorem harmonicMeasureAvg_norm_le {z : ℂ} (hz : ‖z‖ < 1) {F : Circle → ℂ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ ζ : Circle, ‖F ζ‖ ≤ C) : ‖harmonicMeasureAvg z F‖ ≤ C := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1)
  have hcontF : Continuous fun θ : ℝ =>
      F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ) :=
    (hF.comp Circle.exp.continuous).mul
      (Complex.continuous_ofReal.comp (continuous_poissonKernelDisk_exp hz))
  have hbound : ∀ᵐ θ ∂volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
      ‖F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)‖
        ≤ C * poissonKernelDisk z (Circle.exp θ) := by
    filter_upwards with θ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonKernelDisk_nonneg (ζ := (Circle.exp θ : ℂ)) hz)]
    exact mul_le_mul_of_nonneg_right (hC _) (poissonKernelDisk_nonneg hz)
  have hle : ‖∫ θ in (0:ℝ)..(2 * Real.pi),
      F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)‖
      ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), C * poissonKernelDisk z (Circle.exp θ) :=
    intervalIntegral.norm_integral_le_of_norm_le hpi.le hbound
      ((continuous_const.mul (continuous_poissonKernelDisk_exp hz)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_poissonKernel hz] at hle
  rw [harmonicMeasureAvg, norm_mul]
  have hnorm : ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi),
        F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)‖
      ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C := by field_simp

/-- The conjugate `w ↦ star (g (star w))` of an element of `G₊` is again in `G₊`. -/
theorem isDiskAutPlus_starComp (g : ℂ → ℂ) (hg : IsDiskAutPlus g) :
    IsDiskAutPlus (fun w => star (g (star w))) := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  refine ⟨star lam, star a, by rwa [norm_star], by rwa [norm_star], fun z => ?_⟩
  simp only [hform, diskAut, star_mul, star_div₀, star_sub, star_star, star_one]
  ring

/-- Naturality of harmonic measure for `ζ ↦ ζ ^ m`, `m : ℕ`. -/
theorem harmonicMeasureAvg_naturality_pow (g : ℂ → ℂ) (hg : IsDiskAut g) (z : ℂ) (hz : ‖z‖ < 1)
    (m : ℕ) :
    harmonicMeasureAvg (g z) (fun ζ => ((ζ : ℂ)) ^ m)
      = harmonicMeasureAvg z (fun ζ => (g (ζ : ℂ)) ^ m) := by
  have hpow : DiffContOnCl ℂ (fun w : ℂ => w ^ m) (Metric.ball (0:ℂ) 1) :=
    (differentiable_pow m).diffContOnCl
  rcases hg with hp | hm
  · exact harmonicMeasureAvg_naturality_holomorphic g hp z hz _ hpow
  · set G : ℂ → ℂ := fun w => g (star w) with hGdef
    set Gs : ℂ → ℂ := fun w => star (G (star w)) with hGsdef
    have hGs : IsDiskAutPlus Gs := isDiskAutPlus_starComp G hm
    have hgstar : ∀ w : ℂ, g w = star (Gs w) := by
      intro w
      simp [hGsdef, hGdef]
    have hgz : ‖g z‖ < 1 := isDiskAut_mapsTo_disk g (Or.inr hm) z hz
    have hL : harmonicMeasureAvg (g z) (fun ζ => ((ζ : ℂ)) ^ m) = (g z) ^ m :=
      harmonicMeasureAvg_eq_of_diffContOnCl (fun w => w ^ m) (g z) hgz hpow
    have hcomp : DiffContOnCl ℂ (fun w : ℂ => (Gs w) ^ m) (Metric.ball (0:ℂ) 1) := by
      refine hpow.comp (isDiskAutPlus_diffContOnCl Gs hGs) ?_
      intro w hw
      exact mem_ball_zero_iff.2 (isDiskAutPlus_mapsTo_disk Gs hGs w (mem_ball_zero_iff.1 hw))
    have hR : harmonicMeasureAvg z (fun ζ => (g (ζ : ℂ)) ^ m)
        = star ((Gs z) ^ m) := by
      have hfun : (fun ζ : Circle => (g (ζ : ℂ)) ^ m)
          = fun ζ : Circle => star ((Gs (ζ : ℂ)) ^ m) := by
        funext ζ
        rw [hgstar, star_pow]
      rw [hfun, harmonicMeasureAvg_star]
      congr 1
      exact harmonicMeasureAvg_eq_of_diffContOnCl (fun w => (Gs w) ^ m) z hz hcomp
    rw [hL, hR, hgstar z]
    simp [hGsdef]

theorem zpow_neg_eq_star_pow {u : ℂ} (hu : ‖u‖ = 1) (m : ℕ) : u ^ (-(m:ℤ)) = star (u ^ m) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h1 : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hinv : u⁻¹ = star u := inv_eq_of_mul_eq_one_right h1
  rw [zpow_neg, zpow_natCast, ← inv_pow, hinv, star_pow]

/-- Naturality for `ζ ↦ ζ ^ n`, `n : ℤ`. -/
theorem harmonicMeasureAvg_naturality_zpow (g : ℂ → ℂ) (hg : IsDiskAut g) (z : ℂ) (hz : ‖z‖ < 1)
    (n : ℤ) :
    harmonicMeasureAvg (g z) (fun ζ => ((ζ : ℂ)) ^ n)
      = harmonicMeasureAvg z (fun ζ => (g (ζ : ℂ)) ^ n) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simpa only [zpow_natCast] using harmonicMeasureAvg_naturality_pow g hg z hz m
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := by
      refine ⟨(-n).toNat, ?_⟩
      omega
    have hgcirc : ∀ ζ : Circle, ‖g (ζ : ℂ)‖ = 1 := by
      intro ζ
      exact mem_sphere_zero_iff_norm.1 (isDiskAut_maps_circle_to_circle g hg ζ)
    have hL : (fun ζ : Circle => ((ζ : ℂ)) ^ (-(m:ℤ)))
        = fun ζ : Circle => star (((ζ : ℂ)) ^ m) := by
      funext ζ; exact zpow_neg_eq_star_pow (Circle.norm_coe ζ) m
    have hR : (fun ζ : Circle => (g (ζ : ℂ)) ^ (-(m:ℤ)))
        = fun ζ : Circle => star ((g (ζ : ℂ)) ^ m) := by
      funext ζ; exact zpow_neg_eq_star_pow (hgcirc ζ) m
    rw [hL, hR, harmonicMeasureAvg_star, harmonicMeasureAvg_star,
      harmonicMeasureAvg_naturality_pow g hg z hz m]

/-- `⨍ · dη_z` commutes with finite sums. -/
theorem harmonicMeasureAvg_finset_sum {z : ℂ} (hz : ‖z‖ < 1) (s : Finset ℤ) (c : ℤ → ℂ)
    (Fs : ℤ → Circle → ℂ) (hFs : ∀ n, Continuous (Fs n)) :
    harmonicMeasureAvg z (fun ζ => ∑ n ∈ s, c n * Fs n ζ)
      = ∑ n ∈ s, c n * harmonicMeasureAvg z (Fs n) := by
  induction s using Finset.induction with
  | empty => simp [harmonicMeasureAvg]
  | insert n s hns ih =>
    have hcont : Continuous fun ζ : Circle => ∑ m ∈ s, c m * Fs m ζ :=
      continuous_finsetSum _ fun m _ => continuous_const.mul (hFs m)
    rw [Finset.sum_insert hns]
    have hsplit : (fun ζ : Circle => ∑ m ∈ insert n s, c m * Fs m ζ)
        = fun ζ : Circle => c n * Fs n ζ + ∑ m ∈ s, c m * Fs m ζ := by
      funext ζ; rw [Finset.sum_insert hns]
    rw [hsplit, harmonicMeasureAvg_add (F := fun ζ : Circle => c n * Fs n ζ)
      (G := fun ζ : Circle => ∑ m ∈ s, c m * Fs m ζ) hz
      (continuous_const.mul (hFs n)) hcont, harmonicMeasureAvg_const_mul, ih]

theorem fourier_eq_zpow (n : ℤ) (y : AddCircle (2 * Real.pi)) :
    fourier n y = ((AddCircle.homeomorphCircle' y : Circle) : ℂ) ^ n := by
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    rw [fourier_coe_apply, AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp,
      ← Complex.exp_int_mul]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      simpa using Real.pi_ne_zero
    field_simp
    push_cast
    ring

/-- Trigonometric polynomials are dense in `C(S¹, ℂ)`. -/
theorem exists_trigPoly_approx (F : Circle → ℂ) (hF : Continuous F) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ),
      ∀ ζ : Circle, ‖F ζ - ∑ n ∈ s, c n * (ζ : ℂ) ^ n‖ < ε := by
  set e : AddCircle (2 * Real.pi) ≃ₜ Circle := AddCircle.homeomorphCircle' with he
  set F' : C(AddCircle (2 * Real.pi), ℂ) := ⟨fun y => F (e y), hF.comp e.continuous⟩ with hF'
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have htop : (Submodule.span ℂ (Set.range (@fourier (2 * Real.pi)))).topologicalClosure = ⊤ :=
    span_fourier_closure_eq_top
  have hmem : F' ∈ closure ((Submodule.span ℂ (Set.range (@fourier (2 * Real.pi)))) : Set _) := by
    have h2 : F' ∈ (Submodule.span ℂ (Set.range (@fourier (2 * Real.pi)))).topologicalClosure := by
      rw [htop]; trivial
    exact h2
  obtain ⟨Q', hQ'mem, hQ'⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hQ'mem
  refine ⟨cf.support, fun n => cf n, fun ζ => ?_⟩
  have hval : Q' (e.symm ζ) = ∑ n ∈ cf.support, cf n * (ζ : ℂ) ^ n := by
    rw [← hcf]
    simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourier_eq_zpow, Homeomorph.apply_symm_apply]
  have hbound : ‖F' (e.symm ζ) - Q' (e.symm ζ)‖ < ε := by
    refine lt_of_le_of_lt ?_ hQ'
    have := ContinuousMap.norm_coe_le_norm (F' - Q') (e.symm ζ)
    simpa [dist_eq_norm] using this
  rw [hval] at hbound
  have hF'val : F' (e.symm ζ) = F ζ := by
    simp [hF', Homeomorph.apply_symm_apply]
  rwa [hF'val] at hbound

theorem continuous_isDiskAut_circle (g : ℂ → ℂ) (hg : IsDiskAut g) :
    Continuous fun ζ : Circle => g (ζ : ℂ) := by
  have hplus : ∀ G : ℂ → ℂ, IsDiskAutPlus G → Continuous fun ζ : Circle => G (ζ : ℂ) := by
    rintro G ⟨lam, a, hlam, ha, hform⟩
    simp only [hform]
    exact continuous_const.mul (continuous_diskAut_comp a ha id continuous_id)
  rcases hg with h | h
  · exact hplus g h
  · have hc := (hplus _ h).comp (continuous_inv (G := Circle))
    refine hc.congr fun ζ => ?_
    simp only [Function.comp_apply, Circle.coe_inv]
    rw [inv_eq_of_mul_eq_one_right (by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num : (ζ : ℂ) * star (ζ : ℂ) = 1)]
    rw [star_star]

theorem continuous_zpow_circle (n : ℤ) : Continuous fun ζ : Circle => ((ζ : ℂ)) ^ n := by
  refine continuous_subtype_val.zpow₀ n fun ζ => Or.inl ?_
  intro hzero
  have := Circle.norm_coe ζ
  rw [hzero] at this
  simp at this

/-- Conformal naturality of the harmonic measure: for `g ∈ G` an automorphism
of `D` with boundary values `g|_{S¹}`, `⨍ F dη_{g(z)} = ⨍ (F ∘ g|_{S¹}) dη_z`.

`F` is required to be continuous: for a non-integrable `F` both sides are `0`
by the junk-value convention on integrals, but nothing about `F` transfers
along `g` without a change of variables, so the unrestricted statement is not
the paper's claim.

The proof is by density: naturality holds for every Laurent monomial
`ζ ↦ ζ ^ n` (`harmonicMeasureAvg_naturality_zpow`), both sides are linear in `F`
and bounded by `‖F‖_∞`, and the span of those monomials is dense in `C(S¹, ℂ)`
(`exists_trigPoly_approx`, from Mathlib's `span_fourier_closure_eq_top`). -/
theorem harmonicMeasureAvg_naturality (g : ℂ → ℂ) (hg : IsDiskAut g)
    (z : ℂ) (hz : ‖z‖ < 1) (F : Circle → ℂ) (hF : Continuous F) :
    harmonicMeasureAvg (g z) F =
      harmonicMeasureAvg z (fun ζ => F ⟨g (ζ : ℂ), isDiskAut_maps_circle_to_circle g hg ζ⟩) := by
  have hgz : ‖g z‖ < 1 := isDiskAut_mapsTo_disk g hg z hz
  set gh : Circle → Circle := fun ζ => ⟨g (ζ : ℂ), isDiskAut_maps_circle_to_circle g hg ζ⟩
    with hgh
  have hghc : Continuous gh := continuous_induced_rng.2 (continuous_isDiskAut_circle g hg)
  have key : ∀ ε : ℝ, 0 < ε →
      ‖harmonicMeasureAvg (g z) F - harmonicMeasureAvg z (fun ζ => F (gh ζ))‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨s, c, happ⟩ := exists_trigPoly_approx F hF hε
    set Q : Circle → ℂ := fun ζ => ∑ n ∈ s, c n * (ζ : ℂ) ^ n with hQdef
    have hQc : Continuous Q :=
      continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_zpow_circle n)
    have hDc : Continuous fun ζ : Circle => F ζ - Q ζ := hF.sub hQc
    have hQnat : harmonicMeasureAvg (g z) Q = harmonicMeasureAvg z (fun ζ => Q (gh ζ)) := by
      rw [hQdef]
      rw [harmonicMeasureAvg_finset_sum hgz s c (fun n ζ => ((ζ : ℂ)) ^ n)
        (fun n => continuous_zpow_circle n)]
      rw [show (fun ζ : Circle => ∑ n ∈ s, c n * ((gh ζ : Circle) : ℂ) ^ n)
          = fun ζ : Circle => ∑ n ∈ s, c n * (g (ζ : ℂ)) ^ n from rfl]
      rw [harmonicMeasureAvg_finset_sum hz s c (fun n ζ => (g (ζ : ℂ)) ^ n)
        (fun n => (continuous_isDiskAut_circle g hg).zpow₀ n fun ζ => Or.inl (by
          intro hzero
          have := mem_sphere_zero_iff_norm.1 (isDiskAut_maps_circle_to_circle g hg ζ)
          rw [hzero] at this
          simp at this))]
      exact Finset.sum_congr rfl fun n _ => by
        rw [harmonicMeasureAvg_naturality_zpow g hg z hz n]
    have hsplitL : harmonicMeasureAvg (g z) F
        = harmonicMeasureAvg (g z) Q + harmonicMeasureAvg (g z) (fun ζ => F ζ - Q ζ) := by
      rw [← harmonicMeasureAvg_add (F := Q) (G := fun ζ : Circle => F ζ - Q ζ) hgz hQc hDc]
      congr 1
      funext ζ; ring
    have hsplitR : harmonicMeasureAvg z (fun ζ => F (gh ζ))
        = harmonicMeasureAvg z (fun ζ => Q (gh ζ))
          + harmonicMeasureAvg z (fun ζ => F (gh ζ) - Q (gh ζ)) := by
      rw [← harmonicMeasureAvg_add (F := fun ζ : Circle => Q (gh ζ))
        (G := fun ζ : Circle => F (gh ζ) - Q (gh ζ)) hz (hQc.comp hghc) (hDc.comp hghc)]
      congr 1
      funext ζ; ring
    rw [hsplitL, hsplitR, hQnat]
    have hb1 : ‖harmonicMeasureAvg (g z) (fun ζ => F ζ - Q ζ)‖ ≤ ε :=
      harmonicMeasureAvg_norm_le hgz hDc (fun ζ => le_of_lt (happ ζ))
    have hb2 : ‖harmonicMeasureAvg z (fun ζ => F (gh ζ) - Q (gh ζ))‖ ≤ ε :=
      harmonicMeasureAvg_norm_le hz (hDc.comp hghc) (fun ζ => le_of_lt (happ (gh ζ)))
    calc ‖(harmonicMeasureAvg z (fun ζ => Q (gh ζ))
              + harmonicMeasureAvg (g z) (fun ζ => F ζ - Q ζ))
            - (harmonicMeasureAvg z (fun ζ => Q (gh ζ))
              + harmonicMeasureAvg z (fun ζ => F (gh ζ) - Q (gh ζ)))‖
        = ‖harmonicMeasureAvg (g z) (fun ζ => F ζ - Q ζ)
            - harmonicMeasureAvg z (fun ζ => F (gh ζ) - Q (gh ζ))‖ := by ring_nf
      _ ≤ ε + ε := norm_sub_le_of_le hb1 hb2
      _ = 2 * ε := by ring
  have hzero : harmonicMeasureAvg (g z) F - harmonicMeasureAvg z (fun ζ => F (gh ζ)) = 0 := by
    by_contra hne
    have hpos : 0 < ‖harmonicMeasureAvg (g z) F - harmonicMeasureAvg z (fun ζ => F (gh ζ))‖ :=
      norm_pos_iff.2 hne
    have := key (‖harmonicMeasureAvg (g z) F
      - harmonicMeasureAvg z (fun ζ => F (gh ζ))‖ / 4) (by linarith)
    linarith
  exact sub_eq_zero.1 hzero

/-! ## Section 2: the conformal barycenter -/

/-- A continuous probability density on `S¹` with respect to `dθ/(2π)`, i.e.
the class of densities `dμ = ρ(θ) dθ/(2π)` of a Borel probability measure `μ`
on `S¹` that arises as a pushforward `φ_*(η_z)` of harmonic measure under a
homeomorphism `φ` of `S¹`. -/
def IsProbabilityDensity (ρ : ℝ → ℝ) : Prop :=
  Continuous ρ ∧ (∀ θ : ℝ, 0 ≤ ρ θ) ∧ (∀ θ : ℝ, ρ (θ + 2 * Real.pi) = ρ θ) ∧
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 1

/-- The vector field `ξ_μ` on `D` associated to a probability density `ρ`
(formula (2.3)):
`ξ_μ(w) = (1 - |w|²) ⨍ (ζ - w)/(1 - conj(w) ζ) dμ(ζ)`. -/
def xiField (ρ : ℝ → ℝ) (w : ℂ) : ℂ :=
  (1 - ‖w‖ ^ 2) * (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
    (((Circle.exp θ : ℂ) - w) / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ)

/-- `ξ_μ(0) = ∫ ζ dμ(ζ)` (formula (2.2)). -/
theorem xiField_zero (ρ : ℝ → ℝ) :
    xiField ρ 0 = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (Circle.exp θ : ℂ) * (ρ θ : ℂ) := by
  simp [xiField]

/-- A continuous nonnegative function that is positive at an interior point has
positive integral. -/
theorem intervalIntegral_pos_of_pos_at {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {a b x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) (hpos : 0 < f x₀) :
    0 < ∫ x in a..b, f x := by
  obtain ⟨ha, hb⟩ := hx₀
  have hopen : IsOpen {x : ℝ | f x₀ / 2 < f x} := isOpen_lt continuous_const hf
  have hmem : x₀ ∈ {x : ℝ | f x₀ / 2 < f x} := by simp; linarith
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hopen x₀ hmem
  set δ := min (ε / 2) (min ((x₀ - a) / 2) ((b - x₀) / 2)) with hδdef
  have hδ : 0 < δ := by
    refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδa : a < x₀ - δ := by
    have := min_le_right (ε / 2) (min ((x₀ - a) / 2) ((b - x₀) / 2))
    have h2 := min_le_left ((x₀ - a) / 2) ((b - x₀) / 2)
    have : δ ≤ (x₀ - a) / 2 := le_trans (min_le_right _ _) h2
    linarith
  have hδb : x₀ + δ < b := by
    have h2 := min_le_right ((x₀ - a) / 2) ((b - x₀) / 2)
    have : δ ≤ (b - x₀) / 2 := le_trans (min_le_right _ _) h2
    linarith
  have hmid : 0 < ∫ x in (x₀ - δ)..(x₀ + δ), f x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _) ?_ (by linarith)
    intro x hx
    have hdist : dist x x₀ < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hx.1]; linarith [hx.2]]
    have := hsub hdist
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have h1 : 0 ≤ ∫ x in a..(x₀ - δ), f x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hnn x)
  have h2 : 0 ≤ ∫ x in (x₀ + δ)..b, f x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hnn x)
  have hsplit : (∫ x in a..(x₀ - δ), f x) + (∫ x in (x₀ - δ)..(x₀ + δ), f x)
      + (∫ x in (x₀ + δ)..b, f x) = ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  linarith

/-- There is an interior point of `(0, 2π)` where a probability density is
positive and `sin` does not vanish. -/
theorem exists_pos_of_isProbabilityDensity (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    ∃ θ₀ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), 0 < ρ θ₀ ∧ Real.sin θ₀ ≠ 0 := by
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hpi := Real.pi_pos
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hρtot
    linarith
  -- some interior point has ρ > 0
  have hex : ∃ θ₀ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), 0 < ρ θ₀ := by
    by_contra hcon
    have hcon' : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), ρ θ ≤ 0 :=
      fun θ hθ => not_lt.1 (fun h => hcon ⟨θ, hθ, h⟩)
    have hclosed : IsClosed {x : ℝ | ρ x ≤ 0} := isClosed_le hρc continuous_const
    have hsub : Set.Icc (0:ℝ) (2 * Real.pi) ⊆ {x : ℝ | ρ x ≤ 0} := by
      rw [← closure_Ioo (by positivity : (0:ℝ) ≠ 2 * Real.pi)]
      exact hclosed.closure_subset_iff.2 hcon'
    have hneg : 0 ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), -ρ θ :=
      intervalIntegral.integral_nonneg (by positivity) (fun x hx => by
        have := hsub hx; simp only [Set.mem_ofPred_eq] at this; linarith)
    rw [intervalIntegral.integral_neg] at hneg
    linarith
  obtain ⟨θ₀, hθ₀mem, hθ₀pos⟩ := hex
  by_cases hs : Real.sin θ₀ = 0
  · -- then θ₀ = π; perturb to a nearby point where sin ≠ 0
    have hθπ : θ₀ = Real.pi := by
      have hshift : Real.sin (θ₀ - Real.pi) = 0 := by
        rw [Real.sin_sub]
        simp [hs]
      have h1 : -Real.pi < θ₀ - Real.pi := by linarith [hθ₀mem.1]
      have h2 : θ₀ - Real.pi < Real.pi := by linarith [hθ₀mem.2]
      have := (Real.sin_eq_zero_iff_of_lt_of_lt h1 h2).1 hshift
      linarith
    subst hθπ
    have hcont := hρc.continuousAt (x := Real.pi)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont (ρ Real.pi / 2) (by linarith)
    set y : ℝ := min δ Real.pi / 2 with hy
    have hy0 : 0 < y := by
      have : 0 < min δ Real.pi := lt_min hδ hpi
      linarith
    have hyδ : y < δ := by
      have : min δ Real.pi ≤ δ := min_le_left _ _
      linarith
    have hyπ : y < Real.pi := by
      have : min δ Real.pi ≤ Real.pi := min_le_right _ _
      linarith
    refine ⟨Real.pi + y, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · have hd : dist (Real.pi + y) Real.pi < δ := by
        rw [Real.dist_eq]
        simp only [add_sub_cancel_left]
        rwa [abs_of_pos hy0]
      have := hball hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    · rw [Real.sin_add]
      simp only [Real.sin_pi, Real.cos_pi, zero_mul, neg_one_mul, zero_add]
      have := Real.sin_pos_of_pos_of_lt_pi hy0 hyπ
      linarith
  · exact ⟨θ₀, hθ₀mem, hθ₀pos, hs⟩

/-! ### The Jacobian of `ξ_μ` at `0` (formula (2.4))

The Jacobian of a real-differentiable `F : ℂ → ℂ` is `|F_w|² - |F_w̄|²` with
`F_w = (dF(1) - i·dF(i))/2`, *not* `‖dF(1)‖² - ‖dF(i)‖²`.  The latter is `0`
for the uniform density (`jacobian_xiField_zero_pos_false` below), so
`jacobian_xiField_zero_pos` is stated as `|ξ_w̄| < |ξ_w|`, which is the paper's
`J ξ_μ(0) > 0`. -/

/-- The uniform density is a probability density. -/
theorem isProbabilityDensity_one : IsProbabilityDensity (fun _ => 1) := by
  refine ⟨continuous_const, fun _ => zero_le_one, fun _ => rfl, ?_⟩
  simp
  field_simp

/-- For the uniform density, `ξ_μ(w) = -w(1 - |w|²)`: the mean of `g_w` over
`S¹` is `g_w(0) = -w` by the Poisson formula. -/
theorem xiField_one (w : ℂ) (hw : ‖w‖ < 1) :
    xiField (fun _ => 1) w = (1 - (‖w‖:ℂ) ^ 2) * (-w) := by
  have hplus : IsDiskAutPlus (diskAut w) := ⟨1, w, by simp, hw, by simp⟩
  have hmean : harmonicMeasureAvg 0 (fun ζ => diskAut w ((ζ : ℂ))) = diskAut w 0 :=
    harmonicMeasureAvg_eq_of_diffContOnCl (diskAut w) 0 (by simp)
      (isDiskAutPlus_diffContOnCl _ hplus)
  rw [diskAut_zero] at hmean
  rw [xiField]
  have hP : ∀ θ : ℝ, (poissonKernelDisk 0 (Circle.exp θ) : ℂ) = 1 := by
    intro θ
    simp [poissonKernelDisk]
  rw [harmonicMeasureAvg] at hmean
  simp only [hP, mul_one] at hmean
  simp only [diskAut] at hmean
  rw [mul_assoc]
  simp only [Complex.ofReal_one, mul_one]
  rw [hmean]

theorem hasFDerivAt_xiField_one :
    HasFDerivAt (xiField (fun _ => 1)) (-(ContinuousLinearMap.id ℝ ℂ)) 0 := by
  have key : HasFDerivAt (fun w : ℂ => (1 - (‖w‖:ℂ) ^ 2) * (-w))
      (-(ContinuousLinearMap.id ℝ ℂ)) 0 := by
    rw [hasFDerivAt_iff_isLittleO]
    have hrw : (fun w : ℂ => (1 - (‖w‖:ℂ) ^ 2) * (-w) - (1 - (‖(0:ℂ)‖:ℂ) ^ 2) * (-(0:ℂ))
        - (-(ContinuousLinearMap.id ℝ ℂ)) (w - 0)) = fun w : ℂ => ((‖w‖:ℂ) ^ 2) * w := by
      funext w
      simp
      ring
    rw [hrw, Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (lt_min one_pos hc)] with w hw
    have h1 : ‖w‖ < min 1 c := by simpa using hw
    have h2 : ‖w‖ ≤ 1 := le_of_lt (lt_of_lt_of_le h1 (min_le_left _ _))
    have h3 : ‖w‖ < c := lt_of_lt_of_le h1 (min_le_right _ _)
    have hnorm : ‖((‖w‖:ℂ) ^ 2) * w‖ = ‖w‖ ^ 2 * ‖w‖ := by simp
    rw [hnorm]
    simp only [sub_zero]
    nlinarith [norm_nonneg w]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) one_pos] with w hw
  exact xiField_one w (by simpa using hw)

/-- The naive reading of (2.4) is false: for the uniform density the
differential at `0` is `v ↦ -v`, so `‖dξ(1)‖² - ‖dξ(i)‖² = 1 - 1 = 0`. -/
theorem jacobian_xiField_zero_pos_false :
    ¬ ∀ (ρ : ℝ → ℝ), IsProbabilityDensity ρ →
      (0:ℝ) < ‖(fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) 1‖ ^ 2 -
        ‖(fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) Complex.I‖ ^ 2 := by
  intro h
  have hbad := h (fun _ => 1) isProbabilityDensity_one
  rw [hasFDerivAt_xiField_one.fderiv] at hbad
  simp at hbad

/-- The exact second-order remainder in the expansion of the integrand of
`ξ_μ` at `w = 0`: the paper's `o(w)` is `w̄·(w² - 2wζ + w̄ζ³)/(1 - w̄ζ)`, of
modulus `≤ 7‖w‖²` for `‖w‖ ≤ 1/2` and `‖ζ‖ = 1`. -/
theorem xiField_integrand_remainder (w ζ : ℂ) (hden : (1:ℂ) - star w * ζ ≠ 0) :
    (1 - (star w * w)) * ((ζ - w) / (1 - star w * ζ)) - (ζ - w + ζ ^ 2 * star w)
      = star w * (w ^ 2 - 2 * w * ζ + star w * ζ ^ 3) / (1 - star w * ζ) := by
  field_simp
  ring

/-! ### The Wirtinger decomposition of a real-linear map of `ℂ`

Every `ℝ`-linear `L : ℂ → ℂ` is `w ↦ p·w + q·w̄` with `p = (L1 - i·Li)/2` and
`q = (L1 + i·Li)/2`; those two numbers are the Wirtinger derivatives when `L`
is a differential.  This is what makes `L1 ± i·Li` — the combinations appearing
in `jacobian_of_deriv_form`, in `jacobian_xiField_zero_pos` and in the Jacobian
half of Theorem 1 — the right things to compare. -/

theorem clm_apply_re_im (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = w.re • L 1 + w.im • L Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w.re • (1:ℂ) + w.im • Complex.I by
    simp [Complex.real_smul]]
  rw [map_add, map_smul, map_smul]

theorem clm_apply_eq_wirt (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = ((L 1 - Complex.I * L Complex.I) / 2) * w
        + ((L 1 + Complex.I * L Complex.I) / 2) * star w := by
  have h2 : (2:ℂ) * L w
      = (L 1 - Complex.I * L Complex.I) * w + (L 1 + Complex.I * L Complex.I) * star w := by
    rw [clm_apply_re_im L w]
    simp only [Complex.real_smul, Complex.star_def]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im] <;> ring
  linear_combination h2 / 2

/-- If the differential of `ξ_μ` at `0` is `v ↦ -v + c·v̄` — the expansion
`ξ_μ(w) = ξ_μ(0) - w + w̄∫ζ²dμ + o(w)` of the paper — then its Wirtinger
derivatives are `ξ_w = -1` and `ξ_w̄ = c`, so `J ξ_μ(0) = 1 - |c|²`. -/
theorem jacobian_of_deriv_form (c : ℂ) (L : ℂ →L[ℝ] ℂ) (hL : ∀ v : ℂ, L v = -v + c * star v) :
    ‖L 1 + Complex.I * L Complex.I‖ = 2 * ‖c‖ ∧ ‖L 1 - Complex.I * L Complex.I‖ = 2 := by
  have h1 : L 1 = -1 + c := by rw [hL]; simp
  have h2 : L Complex.I = -Complex.I - c * Complex.I := by
    rw [hL]; simp; ring
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
    have hval : (-1 + c) + Complex.I * (-Complex.I - c * Complex.I) = 2 * c := by
      linear_combination (-1 - c) * Complex.I_mul_I
    rw [hval, norm_mul]
    simp
  · rw [h1, h2]
    have hval : (-1 + c) - Complex.I * (-Complex.I - c * Complex.I) = -2 := by
      linear_combination (1 + c) * Complex.I_mul_I
    rw [hval]
    simp

/-- `⨍ ζ² dμ(ζ)`: the coefficient of `w̄` in the expansion of `ξ_μ` at `0`. -/
noncomputable def xiCoeff (ρ : ℝ → ℝ) : ℂ :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), (Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)

/-- The candidate differential of `ξ_μ` at `0`: `v ↦ -v + c·v̄`. -/
noncomputable def xiDeriv (c : ℂ) : ℂ →L[ℝ] ℂ :=
  -(ContinuousLinearMap.id ℝ ℂ) + c • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

@[simp]
theorem xiDeriv_apply (c v : ℂ) : xiDeriv c v = -v + c * star v := by
  simp [xiDeriv]

/-- The exact first-order expansion of `ξ_μ` at `0`: the error term
`ξ_μ(w) - ξ_μ(0) - (-w + w̄ ⨍ζ²dμ)` is the average of the remainder supplied by
`xiField_integrand_remainder`. -/
theorem xiField_sub_linear (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) (w : ℂ) (hw : ‖w‖ < 1) :
    xiField ρ w - xiField ρ 0 - (-w + xiCoeff ρ * star w)
      = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi),
          (star w * (w ^ 2 - 2 * w * (Circle.exp θ : ℂ) + star w * (Circle.exp θ : ℂ) ^ 3)
            / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ) := by
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hexp : Continuous fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ) := by fun_prop
  have hρC : Continuous fun θ : ℝ => ((ρ θ : ℝ) : ℂ) := Complex.continuous_ofReal.comp hρc
  have hden : ∀ θ : ℝ, (1:ℂ) - star w * ((Circle.exp θ : Circle) : ℂ) ≠ 0 :=
    fun θ => diskAut_denom_ne_zero w _ hw (by simp)
  have h1i : IntervalIntegrable (fun θ : ℝ => (Circle.exp θ : ℂ) * (ρ θ : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := (hexp.mul hρC).intervalIntegrable _ _
  have h2i : IntervalIntegrable (fun θ : ℝ => (-w) * (ρ θ : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := (continuous_const.mul hρC).intervalIntegrable _ _
  have h3i : IntervalIntegrable (fun θ : ℝ => star w * ((Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul ((hexp.pow 2).mul hρC)).intervalIntegrable _ _
  have hRi : IntervalIntegrable (fun θ : ℝ =>
      (star w * (w ^ 2 - 2 * w * (Circle.exp θ : ℂ) + star w * (Circle.exp θ : ℂ) ^ 3)
        / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ((Continuous.div (by fun_prop) (by fun_prop) hden).mul hρC).intervalIntegrable _ _
  have hstar : ((1:ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) = 1 - star w * w := by
    rw [Complex.star_def, Complex.conj_mul']
  have hrho1 : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), ((ρ θ : ℝ) : ℂ) = 1 := by
    have hint : IntervalIntegrable ρ MeasureTheory.volume 0 (2 * Real.pi) :=
      hρc.intervalIntegrable _ _
    have h := (Complex.ofRealCLM.intervalIntegral_comp_comm hint).symm
    simp only [Complex.ofRealCLM_apply] at h
    rw [← h, ← Complex.ofReal_mul, hρtot]
    norm_num
  have hpt : ∀ θ : ℝ, ((1:ℂ) - star w * w) *
      (((Circle.exp θ : ℂ) - w) / (1 - star w * (Circle.exp θ : ℂ)) * (ρ θ : ℂ))
      = ((Circle.exp θ : ℂ) * (ρ θ : ℂ) + (-w) * (ρ θ : ℂ)
          + star w * ((Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)))
        + (star w * (w ^ 2 - 2 * w * (Circle.exp θ : ℂ) + star w * (Circle.exp θ : ℂ) ^ 3)
            / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ) := by
    intro θ
    have h := xiField_integrand_remainder w (Circle.exp θ : ℂ) (hden θ)
    field_simp at h ⊢
    linear_combination (ρ θ : ℂ) * h
  have e1 : xiField ρ w = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi),
      (((1:ℂ) - star w * w) *
        (((Circle.exp θ : ℂ) - w) / (1 - star w * (Circle.exp θ : ℂ)) * (ρ θ : ℂ))) := by
    rw [xiField, intervalIntegral.integral_const_mul, ← hstar]; ring
  rw [e1, intervalIntegral.integral_congr (fun θ _ => hpt θ),
    intervalIntegral.integral_add ((h1i.add h2i).add h3i) hRi,
    intervalIntegral.integral_add (h1i.add h2i) h3i,
    intervalIntegral.integral_add h1i h2i,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    xiField_zero, xiCoeff]
  linear_combination (-w) * hrho1

/-- The remainder in the expansion of `ξ_μ` at `0` is `O(‖w‖²)` uniformly in the
density: `‖ξ_μ(w) - ξ_μ(0) + w - w̄ ⨍ζ²dμ‖ ≤ 7‖w‖²` for `‖w‖ ≤ 1/2`. -/
theorem xiField_remainder_bound (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) (w : ℂ)
    (hw : ‖w‖ ≤ 1 / 2) :
    ‖xiField ρ w - xiField ρ 0 - (-w + xiCoeff ρ * star w)‖ ≤ 7 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := by linarith
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hρtot; linarith
  have hden : ∀ θ : ℝ, (1:ℂ) - star w * ((Circle.exp θ : Circle) : ℂ) ≠ 0 :=
    fun θ => diskAut_denom_ne_zero w _ hw1 (by simp)
  have hbound : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
      ‖(star w * (w ^ 2 - 2 * w * (Circle.exp θ : ℂ) + star w * (Circle.exp θ : ℂ) ^ 3)
          / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ)‖ ≤ (7 * ‖w‖ ^ 2) * ρ θ := by
    filter_upwards with θ _
    set ζ : ℂ := ((Circle.exp θ : Circle) : ℂ) with hζ
    have hζn : ‖ζ‖ = 1 := by rw [hζ]; simp
    have hdenlb : (1:ℝ) / 2 ≤ ‖1 - star w * ζ‖ := by
      have h1 : ‖star w * ζ‖ = ‖w‖ := by rw [norm_mul, hζn, norm_star, mul_one]
      have h2 := norm_sub_norm_le (1 : ℂ) (star w * ζ)
      simp only [norm_one, h1] at h2
      linarith
    have hdenpos : (0:ℝ) < ‖1 - star w * ζ‖ := by linarith
    have hnum : ‖w ^ 2 - 2 * w * ζ + star w * ζ ^ 3‖ ≤ ‖w‖ ^ 2 + 3 * ‖w‖ := by
      have t1 : ‖w ^ 2 - 2 * w * ζ + star w * ζ ^ 3‖
          ≤ ‖w ^ 2 - 2 * w * ζ‖ + ‖star w * ζ ^ 3‖ := norm_add_le _ _
      have t2 : ‖w ^ 2 - 2 * w * ζ‖ ≤ ‖w ^ 2‖ + ‖2 * w * ζ‖ := norm_sub_le _ _
      have t3 : ‖(2:ℂ) * w * ζ‖ = 2 * ‖w‖ := by rw [norm_mul, norm_mul, hζn]; simp
      have t4 : ‖star w * ζ ^ 3‖ = ‖w‖ := by rw [norm_mul, norm_pow, hζn, norm_star]; simp
      have t5 : ‖w ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow]
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρnn θ)]
    refine mul_le_mul_of_nonneg_right ?_ (hρnn θ)
    rw [norm_div, norm_mul, norm_star, div_le_iff₀ hdenpos]
    nlinarith [norm_nonneg w, norm_nonneg (w ^ 2 - 2 * w * ζ + star w * ζ ^ 3), hdenpos]
  have hle := intervalIntegral.norm_integral_le_of_norm_le hpi.le hbound
    ((continuous_const.mul hρc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, htot] at hle
  rw [xiField_sub_linear ρ ⟨hρc, hρnn, hρper, hρtot⟩ w hw1, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi),
        (star w * (w ^ 2 - 2 * w * (Circle.exp θ : ℂ) + star w * (Circle.exp θ : ℂ) ^ 3)
          / (1 - star w * (Circle.exp θ : ℂ))) * (ρ θ : ℂ)‖
      ≤ (2 * Real.pi)⁻¹ * (7 * ‖w‖ ^ 2 * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 7 * ‖w‖ ^ 2 := by field_simp

/-- The paper's expansion `ξ_μ(w) = ξ_μ(0) - w + w̄ ⨍ζ²dμ + o(w)`, read as a
statement about the real differential of `ξ_μ` at `0`. -/
theorem hasFDerivAt_xiField_zero (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    HasFDerivAt (xiField ρ) (xiDeriv (xiCoeff ρ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hr : (0:ℝ) < min (1 / 2) (c / 7) := lt_min (by norm_num) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with w hw
  have hw' : ‖w‖ < min (1 / 2) (c / 7) := by simpa using hw
  have h1 : ‖w‖ ≤ 1 / 2 := le_of_lt (lt_of_lt_of_le hw' (min_le_left _ _))
  have h2 : ‖w‖ ≤ c / 7 := le_of_lt (lt_of_lt_of_le hw' (min_le_right _ _))
  simp only [sub_zero, xiDeriv_apply]
  have hb := xiField_remainder_bound ρ hρ w h1
  have hfin : 7 * ‖w‖ ^ 2 ≤ c * ‖w‖ := by nlinarith [norm_nonneg w]
  simpa [Real.norm_eq_abs] using le_trans hb hfin

/-- `⨍ ζ² dμ(ζ)` has modulus at most `1`, `μ` being a probability measure. -/
theorem norm_xiCoeff_le_one (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) : ‖xiCoeff ρ‖ ≤ 1 := by
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hρtot; linarith
  have hbound : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
      ‖(Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)‖ ≤ 1 * ρ θ := by
    filter_upwards with θ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρnn θ)]
    simp
  have hle := intervalIntegral.norm_integral_le_of_norm_le hpi.le hbound
    ((continuous_const.mul hρc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, htot] at hle
  rw [xiCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi), (Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)‖
      ≤ (2 * Real.pi)⁻¹ * (1 * (2 * Real.pi)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := by field_simp

/-- A unit complex number with real part `1` is `1`. -/
theorem eq_one_of_norm_one_of_re_one {z : ℂ} (h1 : ‖z‖ = 1) (h2 : z.re = 1) : z = 1 := by
  have h3 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.normSq_apply, h2] at h3
  have him : z.im = 0 := by nlinarith
  exact Complex.ext h2 (by simpa using him)

/-- The strict bound `|⨍ ζ² dμ(ζ)| < 1`.  Equality would force
`Re(conj(c)·ζ²) = 1` throughout an interval on which `ρ > 0`, i.e. `ζ²`
constant there, which the injectivity of `θ ↦ e^{2iθ}` on a short arc forbids.
This is the paper's positivity of `½ ⨌ |z² - ζ²|² dμ(ζ) dμ(z)`. -/
theorem norm_xiCoeff_lt_one (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) : ‖xiCoeff ρ‖ < 1 := by
  by_contra hcon
  have hle := norm_xiCoeff_le_one ρ hρ
  have hone : ‖xiCoeff ρ‖ = 1 := le_antisymm hle (not_lt.1 hcon)
  set c : ℂ := xiCoeff ρ with hc
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hpi := Real.pi_pos
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hρtot; linarith
  have hexp : Continuous fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ) := by fun_prop
  have hρC : Continuous fun θ : ℝ => ((ρ θ : ℝ) : ℂ) := Complex.continuous_ofReal.comp hρc
  set f : ℝ → ℝ := fun θ => (1 - (star c * (Circle.exp θ : ℂ) ^ 2).re) * ρ θ with hf
  have hfc : Continuous f := by
    rw [hf]
    exact ((continuous_const.sub
      (Complex.continuous_re.comp (continuous_const.mul (hexp.pow 2)))).mul hρc)
  have hre_le : ∀ θ : ℝ, (star c * (Circle.exp θ : ℂ) ^ 2).re ≤ 1 := by
    intro θ
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, norm_pow, norm_star, hone]
    simp
  have hfnn : ∀ θ : ℝ, 0 ≤ f θ := fun θ => mul_nonneg (by linarith [hre_le θ]) (hρnn θ)
  have hI2 : ∫ θ in (0:ℝ)..(2 * Real.pi), (Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * c := by
    rw [hc, xiCoeff, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt h2pi), Complex.ofReal_one, one_mul]
  have hreint : ∫ θ in (0:ℝ)..(2 * Real.pi), (star c * (Circle.exp θ : ℂ) ^ 2).re * ρ θ
      = 2 * Real.pi := by
    have hcont : Continuous fun θ : ℝ => star c * ((Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ)) :=
      continuous_const.mul ((hexp.pow 2).mul hρC)
    have hcomm := (Complex.reCLM.intervalIntegral_comp_comm
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))).symm
    simp only [Complex.reCLM_apply] at hcomm
    have hpt : ∀ θ : ℝ, (star c * (Circle.exp θ : ℂ) ^ 2).re * ρ θ
        = (star c * ((Circle.exp θ : ℂ) ^ 2 * (ρ θ : ℂ))).re := by
      intro θ
      rw [← mul_assoc, Complex.mul_re]
      simp
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), ← hcomm,
      intervalIntegral.integral_const_mul, hI2]
    have hval : star c * (((2 * Real.pi : ℝ) : ℂ) * c) = ((2 * Real.pi : ℝ) : ℂ) := by
      have hcc : star c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.conj_mul']
      rw [show star c * (((2 * Real.pi : ℝ) : ℂ) * c) = ((2 * Real.pi : ℝ) : ℂ) * (star c * c) by
        ring, hcc, hone]
      norm_num
    rw [hval]
    simp
  have hfint : ∫ θ in (0:ℝ)..(2 * Real.pi), f θ = 0 := by
    have hsplit : ∀ θ : ℝ, f θ = ρ θ - (star c * (Circle.exp θ : ℂ) ^ 2).re * ρ θ := by
      intro θ; rw [hf]; ring
    have hg : Continuous fun θ : ℝ => (star c * (Circle.exp θ : ℂ) ^ 2).re * ρ θ :=
      (Complex.continuous_re.comp (continuous_const.mul (hexp.pow 2))).mul hρc
    rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ),
      intervalIntegral.integral_sub
        (hρc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
        (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi)),
      htot, hreint]
    ring
  have hfzero : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), f θ = 0 := by
    intro θ hθ
    by_contra hne
    have hpos : 0 < f θ := lt_of_le_of_ne (hfnn θ) (Ne.symm hne)
    have hgt := intervalIntegral_pos_of_pos_at hfc hfnn hθ hpos
    rw [hfint] at hgt
    exact lt_irrefl _ hgt
  have key : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), 0 < ρ θ →
      star c * (Circle.exp θ : ℂ) ^ 2 = 1 := by
    intro θ hθ hpos
    have h0 : (1 - (star c * (Circle.exp θ : ℂ) ^ 2).re) * ρ θ = 0 := hfzero θ hθ
    have hz : (1 - (star c * (Circle.exp θ : ℂ) ^ 2).re) = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h (ne_of_gt hpos)
    refine eq_one_of_norm_one_of_re_one ?_ (by linarith)
    rw [norm_mul, norm_pow, norm_star, hone]
    simp
  obtain ⟨θ₀, hθ₀mem, hθ₀pos, -⟩ :=
    exists_pos_of_isProbabilityDensity ρ ⟨hρc, hρnn, hρper, hρtot⟩
  have hopen : IsOpen ({θ : ℝ | 0 < ρ θ} ∩ Set.Ioo (0:ℝ) (2 * Real.pi)) :=
    (isOpen_lt continuous_const hρc).inter isOpen_Ioo
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hopen θ₀ ⟨hθ₀pos, hθ₀mem⟩
  set s : ℝ := min (ε / 2) (Real.pi / 2) with hsdef
  have hs : 0 < s := lt_min (by linarith) (by linarith)
  have hsε : s < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsπ : s ≤ Real.pi / 2 := min_le_right _ _
  have hmem2 : θ₀ + s ∈ {θ : ℝ | 0 < ρ θ} ∩ Set.Ioo (0:ℝ) (2 * Real.pi) := by
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hs] using hsε
  have e1 := key θ₀ hθ₀mem hθ₀pos
  have e2 := key (θ₀ + s) hmem2.2 hmem2.1
  have hcne : star c ≠ 0 := by
    intro h
    rw [h] at e1
    simp at e1
  have hsq : ((Circle.exp θ₀ : ℂ)) ^ 2 = ((Circle.exp (θ₀ + s) : ℂ)) ^ 2 :=
    mul_left_cancel₀ hcne (e1.trans e2.symm)
  have hconv : ∀ θ : ℝ, ((Circle.exp θ : Circle) : ℂ) ^ 2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    intro θ
    rw [Circle.coe_exp, ← Complex.exp_nat_mul]
    norm_num
    ring_nf
  rw [hconv θ₀, hconv (θ₀ + s), Complex.exp_eq_exp_iff_exists_int] at hsq
  obtain ⟨n, hn⟩ := hsq
  have hreal : 2 * θ₀ = 2 * (θ₀ + s) + (n : ℝ) * (2 * Real.pi) := by
    have hcast : (((2 * θ₀ : ℝ)) : ℂ) = (((2 * (θ₀ + s) + (n : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) := by
      field_simp at hn
      push_cast
      push_cast at hn
      linear_combination hn
    exact_mod_cast hcast
  have hsn : s = -((n : ℝ) * Real.pi) := by linarith
  rcases lt_trichotomy n 0 with h | h | h
  · have hn1 : n ≤ -1 := by omega
    have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
    nlinarith [Real.pi_pos]
  · rw [h] at hsn
    simp at hsn
    linarith
  · have hnr : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast h.le
    nlinarith [Real.pi_pos]

/-- The Jacobian formula (2.4): `J ξ_μ(0) = ½ ⨌ |z² - ζ²|² dμ(ζ) dμ(z) > 0`
whenever `ρ` is a genuine probability density (in particular not supported at
a single point).  Equivalently `|ξ_w̄| < |ξ_w|` for the Wirtinger derivatives
of `ξ_μ` at `0`, which is how it is stated here.

The proof goes through `hasFDerivAt_xiField_zero`, which identifies the
differential at `0` with `v ↦ -v + c·v̄` for `c = ⨍ ζ² dμ(ζ)`, and
`norm_xiCoeff_lt_one`, which is the paper's positivity of
`½ ⨌ |z² - ζ²|² dμ(ζ) dμ(z)`. -/
theorem jacobian_xiField_zero_pos (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    ‖(fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) 1
        + Complex.I * (fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) Complex.I‖
      < ‖(fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) 1
        - Complex.I * (fderiv ℝ (xiField ρ) 0 : ℂ →L[ℝ] ℂ) Complex.I‖ := by
  rw [(hasFDerivAt_xiField_zero ρ hρ).fderiv]
  obtain ⟨h1, h2⟩ := jacobian_of_deriv_form (xiCoeff ρ) (xiDeriv (xiCoeff ρ)) (xiDeriv_apply _)
  rw [h1, h2]
  linarith [norm_xiCoeff_lt_one ρ hρ]

/-- `Re ξ_μ(0) = ⨍ cos θ dμ`. -/
theorem re_xiField_zero (ρ : ℝ → ℝ) (hρc : Continuous ρ) :
    (xiField ρ 0).re
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos θ * ρ θ := by
  rw [xiField_zero]
  have hint : IntervalIntegrable (fun θ : ℝ => (Circle.exp θ : ℂ) * (ρ θ : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hre := (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  simp only [Complex.reCLM_apply] at hre
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre]
  simp only [zero_mul, sub_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [Circle.coe_exp, Complex.mul_re, Complex.exp_ofReal_mul_I_re]

/-- `cos θ ≥ √2/2 = cos(π/4)` on the arc `|θ| ≤ π/4`. -/
theorem cos_ge_on_arc {θ : ℝ} (h1 : -(Real.pi/4) ≤ θ) (h2 : θ ≤ Real.pi/4) :
    Real.sqrt 2 / 2 ≤ Real.cos θ := by
  have hpi := Real.pi_pos
  rw [← Real.cos_pi_div_four]
  rcases le_total 0 θ with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi h (by linarith) h2
  · rw [← Real.cos_neg θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

/-- **Lemma 1**: `Re ξ_μ(0) > 0` provided `μ` gives mass `≥ 2/3` to the short
arc `{e^{iθ} : θ ∈ [-π/4, π/4]}`.  The paper's estimate
`Re ξ_μ(0) ≥ (-1)·(1/3) + (√2/2)·(2/3) > 0`: on the arc `cos θ ≥ √2/2`, off it
`cos θ ≥ -1`, and the two masses are `≥ 2/3` and `≤ 1/3`. -/
theorem lemma1_re_xiField_pos (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ)
    (hmass : (2 * Real.pi)⁻¹ * ∫ θ in (-(Real.pi / 4))..(Real.pi / 4), ρ θ ≥ 2 / 3) :
    0 < (xiField ρ 0).re := by
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  have hpi := Real.pi_pos
  set a : ℝ := -(Real.pi / 4) with ha
  set b : ℝ := Real.pi / 4 with hb
  set M : ℝ := ∫ θ in a..b, ρ θ with hM
  have hIρ : ∀ u v : ℝ, IntervalIntegrable ρ MeasureTheory.volume u v :=
    fun u v => hρc.intervalIntegrable u v
  have hIF : ∀ u v : ℝ,
      IntervalIntegrable (fun θ => Real.cos θ * ρ θ) MeasureTheory.volume u v := by
    intro u v; exact (Real.continuous_cos.mul hρc).intervalIntegrable u v
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hρtot
    linarith
  have hperF : Function.Periodic (fun θ => Real.cos θ * ρ θ) (2 * Real.pi) := by
    intro x
    simp only []
    rw [hρper x, Real.cos_add_two_pi]
  have hperρ : Function.Periodic ρ (2 * Real.pi) := hρper
  have hshiftF : ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos θ * ρ θ
      = ∫ θ in a..(a + 2 * Real.pi), Real.cos θ * ρ θ := by
    have := hperF.intervalIntegral_add_eq 0 a
    simpa using this
  have hshiftρ : ∫ θ in (0:ℝ)..(2 * Real.pi), ρ θ = ∫ θ in a..(a + 2 * Real.pi), ρ θ := by
    have := hperρ.intervalIntegral_add_eq 0 a
    simpa using this
  have hmasssplit : M + ∫ θ in b..(a + 2 * Real.pi), ρ θ = 2 * Real.pi := by
    rw [hM, intervalIntegral.integral_add_adjacent_intervals (hIρ a b) (hIρ b _), ← hshiftρ, htot]
  have hbound1 : Real.sqrt 2 / 2 * M ≤ ∫ θ in a..b, Real.cos θ * ρ θ := by
    rw [hM, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by rw [ha, hb]; linarith)
      ((hIρ a b).const_mul _) (hIF a b) ?_
    intro θ hθ
    exact mul_le_mul_of_nonneg_right (cos_ge_on_arc hθ.1 hθ.2) (hρnn θ)
  have hbound2 : -(∫ θ in b..(a + 2 * Real.pi), ρ θ) ≤ ∫ θ in b..(a + 2 * Real.pi),
      Real.cos θ * ρ θ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on (by rw [ha, hb]; linarith)
      (hIρ b _).neg (hIF b _) ?_
    intro θ _
    have := Real.neg_one_le_cos θ
    nlinarith [hρnn θ]
  have hsplitF : ∫ θ in a..(a + 2 * Real.pi), Real.cos θ * ρ θ
      = (∫ θ in a..b, Real.cos θ * ρ θ) + ∫ θ in b..(a + 2 * Real.pi), Real.cos θ * ρ θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hIF a b) (hIF b _)).symm
  have hMlb : M ≥ 4 * Real.pi / 3 := by
    have h2 : (0:ℝ) < 2 * Real.pi := by positivity
    rw [ge_iff_le, ← sub_nonneg] at hmass ⊢
    nlinarith [hmass]
  have hsqrt : (1:ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hIpos : 0 < ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos θ * ρ θ := by
    rw [hshiftF, hsplitF]
    nlinarith [hbound1, hbound2, hmasssplit, hMlb, hsqrt]
  rw [re_xiField_zero ρ hρc]
  positivity

/-! ### Uniqueness of the barycenter along the real diameter

Remark (4) of Section 2 gives a second proof of uniqueness: `ξ_μ` is the
Poincaré gradient of `h_μ`, whose restriction to a geodesic is strictly
concave.  In the normalized position — the geodesic being the real diameter —
that strict monotonicity is elementary and is proved here: for a boundary
point `ζ ≠ ±1` the quantity `Re g_t(ζ)` is strictly decreasing in `t`, because

`Re g_{t₁}(ζ) - Re g_{t₂}(ζ) = 2(t₂-t₁)(1-Re ζ²)(1-t₁t₂) / (|1-t₁ζ|²|1-t₂ζ|²)`.

Averaging against `μ` gives `xiField_zero_unique_on_diameter`. -/

theorem re_diskAut_real (t : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (ht : |t| < 1) :
    (diskAut (t : ℂ) ζ).re = ((1 + t ^ 2) * ζ.re - 2 * t) / (1 - 2 * t * ζ.re + t ^ 2) := by
  have hns : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq ζ
    rw [hζ] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [h]
  have hcre : |ζ.re| ≤ 1 := by nlinarith [sq_nonneg ζ.im, sq_abs ζ.re, abs_nonneg ζ.re]
  have hden : (0:ℝ) < 1 - 2 * t * ζ.re + t ^ 2 := by
    have h1 : t * ζ.re ≤ |t| := by
      calc t * ζ.re ≤ |t * ζ.re| := le_abs_self _
      _ = |t| * |ζ.re| := abs_mul t ζ.re
      _ ≤ |t| * 1 := by nlinarith [abs_nonneg t]
      _ = |t| := mul_one _
    nlinarith [abs_nonneg t, sq_abs t]
  have hden1 : (0:ℝ) < (1 - ζ.re * t) ^ 2 + (t * ζ.im) ^ 2 := by nlinarith [hns, hden]
  rw [diskAut, Complex.div_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring_nf
  have hAB : 1 - ζ.re * t * 2 + ζ.re ^ 2 * t ^ 2 + t ^ 2 * ζ.im ^ 2 = 1 - ζ.re * t * 2 + t ^ 2 := by
    linear_combination t ^ 2 * hns
  rw [hAB]
  have hB : (1 - ζ.re * t * 2 + t ^ 2) ≠ 0 := by nlinarith [hden]
  field_simp
  linear_combination (-t) * hns


theorem diskAut_re_den_pos {t : ℝ} (ht : |t| < 1) {c : ℝ} (hc : |c| ≤ 1) :
    (0:ℝ) < 1 - 2 * t * c + t ^ 2 := by
  have h1 : t * c ≤ |t| := by
    calc t * c ≤ |t * c| := le_abs_self _
    _ = |t| * |c| := abs_mul t c
    _ ≤ |t| * 1 := by nlinarith [abs_nonneg t]
    _ = |t| := mul_one _
  nlinarith [abs_nonneg t, sq_abs t]

/-- Along the real diameter `Re g_t(ζ)` is strictly decreasing in `t`, for every
boundary point other than `±1`.  This is the mechanism behind the uniqueness
half of Proposition 1. -/
theorem re_diskAut_strictAnti {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1) (hlt : t₁ < t₂)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hne : ζ.re ^ 2 < 1) :
    (diskAut (t₂ : ℂ) ζ).re < (diskAut (t₁ : ℂ) ζ).re := by
  have hcabs : |ζ.re| ≤ 1 := by nlinarith [abs_nonneg ζ.re, sq_abs ζ.re]
  have hD1 := diskAut_re_den_pos h1 hcabs
  have hD2 := diskAut_re_den_pos h2 hcabs
  rw [re_diskAut_real t₁ ζ hζ h1, re_diskAut_real t₂ ζ hζ h2, div_lt_div_iff₀ hD2 hD1]
  have key : ((1 + t₁ ^ 2) * ζ.re - 2 * t₁) * (1 - 2 * t₂ * ζ.re + t₂ ^ 2)
      - ((1 + t₂ ^ 2) * ζ.re - 2 * t₂) * (1 - 2 * t₁ * ζ.re + t₁ ^ 2)
      = 2 * (t₂ - t₁) * (1 - ζ.re ^ 2) * (1 - t₁ * t₂) := by ring
  have ht12 : t₁ * t₂ < 1 := by
    nlinarith [abs_nonneg t₁, abs_nonneg t₂, le_abs_self t₁, le_abs_self t₂,
      neg_abs_le t₁, neg_abs_le t₂]
  have hA : (0:ℝ) < t₂ - t₁ := by linarith
  have hB : (0:ℝ) < 1 - ζ.re ^ 2 := by linarith
  have hC : (0:ℝ) < 1 - t₁ * t₂ := by linarith
  have hprod : (0:ℝ) < 2 * (t₂ - t₁) * (1 - ζ.re ^ 2) * (1 - t₁ * t₂) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hA) hB) hC
  linarith [key, hprod]


theorem re_diskAut_antitone {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1) (hle : t₁ ≤ t₂)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (diskAut (t₂ : ℂ) ζ).re ≤ (diskAut (t₁ : ℂ) ζ).re := by
  have hcabs : |ζ.re| ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq ζ
    rw [hζ] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [sq_nonneg ζ.im, sq_abs ζ.re, abs_nonneg ζ.re]
  have hD1 := diskAut_re_den_pos h1 hcabs
  have hD2 := diskAut_re_den_pos h2 hcabs
  rw [re_diskAut_real t₁ ζ hζ h1, re_diskAut_real t₂ ζ hζ h2, div_le_div_iff₀ hD2 hD1]
  have key : ((1 + t₁ ^ 2) * ζ.re - 2 * t₁) * (1 - 2 * t₂ * ζ.re + t₂ ^ 2)
      - ((1 + t₂ ^ 2) * ζ.re - 2 * t₂) * (1 - 2 * t₁ * ζ.re + t₁ ^ 2)
      = 2 * (t₂ - t₁) * (1 - ζ.re ^ 2) * (1 - t₁ * t₂) := by ring
  have hB : (0:ℝ) ≤ 1 - ζ.re ^ 2 := by nlinarith [sq_abs ζ.re, hcabs, abs_nonneg ζ.re]
  have hC : (0:ℝ) < 1 - t₁ * t₂ := by
    nlinarith [abs_nonneg t₁, abs_nonneg t₂, le_abs_self t₁, le_abs_self t₂,
      neg_abs_le t₁, neg_abs_le t₂]
  have hprod : (0:ℝ) ≤ 2 * (t₂ - t₁) * (1 - ζ.re ^ 2) * (1 - t₁ * t₂) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 hle)) hB) hC.le
  linarith [key, hprod]


theorem continuous_re_diskAut_exp {t : ℝ} (ht : |t| < 1) (ρ : ℝ → ℝ) (hρc : Continuous ρ) :
    Continuous fun θ : ℝ => (diskAut (t : ℂ) (Circle.exp θ)).re * ρ θ := by
  have hnorm : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have h1 : Continuous fun u : Circle => diskAut (t : ℂ) ((id u : Circle) : ℂ) :=
    continuous_diskAut_comp (t : ℂ) hnorm id continuous_id
  exact ((Complex.continuous_re.comp (h1.comp Circle.exp.continuous)).mul hρc)

theorem re_xiField_real (ρ : ℝ → ℝ) (hρc : Continuous ρ) (t : ℝ) (ht : |t| < 1) :
    (xiField ρ (t : ℂ)).re = (1 - t ^ 2) * ((2 * Real.pi)⁻¹ *
      ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t : ℂ) (Circle.exp θ)).re * ρ θ) := by
  have hnorm : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hcont : Continuous fun θ : ℝ =>
      ((Circle.exp θ : ℂ) - (t:ℂ)) / (1 - star (t:ℂ) * (Circle.exp θ : ℂ)) * (ρ θ : ℂ) := by
    have h1 : Continuous fun u : Circle => diskAut (t : ℂ) ((id u : Circle) : ℂ) :=
      continuous_diskAut_comp (t : ℂ) hnorm id continuous_id
    exact (h1.comp Circle.exp.continuous).mul (Complex.continuous_ofReal.comp hρc)
  have hint : IntervalIntegrable (fun θ : ℝ =>
      ((Circle.exp θ : ℂ) - (t:ℂ)) / (1 - star (t:ℂ) * (Circle.exp θ : ℂ)) * (ρ θ : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi) := hcont.intervalIntegrable _ _
  have hre := (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  simp only [Complex.reCLM_apply] at hre
  have hcast : ((‖(t:ℂ)‖ : ℝ) : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by
    norm_cast
    rw [Real.norm_eq_abs, sq_abs]
  have hSre : ((1 - ((‖(t:ℂ)‖ : ℝ) : ℂ) ^ 2) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ)).re
      = (1 - t ^ 2) * (2 * Real.pi)⁻¹ := by
    rw [hcast, show ((1:ℂ) - ((t ^ 2 : ℝ) : ℂ)) = (((1 - t ^ 2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hSim : ((1 - ((‖(t:ℂ)‖ : ℝ) : ℂ) ^ 2) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ)).im = 0 := by
    rw [hcast, show ((1:ℂ) - ((t ^ 2 : ℝ) : ℂ)) = (((1 - t ^ 2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_im]
  rw [xiField, Complex.mul_re, hSre, hSim]
  simp only [zero_mul, sub_zero]
  rw [hre, mul_assoc]
  congr 2
  apply intervalIntegral.integral_congr
  intro θ _
  simp [diskAut, Complex.mul_re]


theorem re_xiField_integral_strictAnti (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ)
    {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1) (hlt : t₁ < t₂) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t₂ : ℂ) (Circle.exp θ)).re * ρ θ)
      < ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t₁ : ℂ) (Circle.exp θ)).re * ρ θ := by
  have hρc := hρ.1
  have hρnn := hρ.2.1
  obtain ⟨θ₀, hθ₀mem, hθ₀pos, hθ₀sin⟩ := exists_pos_of_isProbabilityDensity ρ hρ
  have hc1 := continuous_re_diskAut_exp h1 ρ hρc
  have hc2 := continuous_re_diskAut_exp h2 ρ hρc
  have hFcont : Continuous fun θ : ℝ => (diskAut (t₁ : ℂ) (Circle.exp θ)).re * ρ θ
      - (diskAut (t₂ : ℂ) (Circle.exp θ)).re * ρ θ := hc1.sub hc2
  have hFnn : ∀ θ : ℝ, 0 ≤ (diskAut (t₁ : ℂ) (Circle.exp θ)).re * ρ θ
      - (diskAut (t₂ : ℂ) (Circle.exp θ)).re * ρ θ := by
    intro θ
    have := re_diskAut_antitone h1 h2 hlt.le (Circle.exp θ) (Circle.norm_coe _)
    have := mul_le_mul_of_nonneg_right this (hρnn θ)
    linarith
  have hFpos : 0 < (diskAut (t₁ : ℂ) (Circle.exp θ₀)).re * ρ θ₀
      - (diskAut (t₂ : ℂ) (Circle.exp θ₀)).re * ρ θ₀ := by
    have hre : ((Circle.exp θ₀ : ℂ)).re = Real.cos θ₀ := by simp [Circle.coe_exp]
    have hcos : ((Circle.exp θ₀ : ℂ)).re ^ 2 < 1 := by
      rw [hre]
      nlinarith [Real.sin_sq_add_cos_sq θ₀, sq_pos_of_ne_zero hθ₀sin]
    have hstrict := re_diskAut_strictAnti h1 h2 hlt (Circle.exp θ₀) (Circle.norm_coe _) hcos
    nlinarith [hθ₀pos]
  have hpos := intervalIntegral_pos_of_pos_at hFcont hFnn hθ₀mem hFpos
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    at hpos
  linarith

/-- **Uniqueness of the conformal barycenter along the real diameter**: `ξ_μ`
has at most one zero on `(-1, 1)`. -/
theorem xiField_zero_unique_on_diameter (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ)
    {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1)
    (hz1 : xiField ρ (t₁ : ℂ) = 0) (hz2 : xiField ρ (t₂ : ℂ) = 0) : t₁ = t₂ := by
  have hρc := hρ.1
  have key : ∀ t : ℝ, |t| < 1 → xiField ρ (t : ℂ) = 0 →
      (∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t : ℂ) (Circle.exp θ)).re * ρ θ) = 0 := by
    intro t ht hz
    have h := re_xiField_real ρ hρc t ht
    rw [hz] at h
    simp only [Complex.zero_re] at h
    have h1t : (0:ℝ) < 1 - t ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t, le_abs_self t, neg_abs_le t]
    have hpiinv : (0:ℝ) < (2 * Real.pi)⁻¹ := by positivity
    rcases mul_eq_zero.1 h.symm with hA | hB
    · exact absurd hA (by linarith)
    · rcases mul_eq_zero.1 hB with hC | hD
      · exact absurd hC (by linarith)
      · exact hD
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · have := re_xiField_integral_strictAnti ρ hρ h1 h2 hlt
    rw [key t₁ h1 hz1, key t₂ h2 hz2] at this
    exact absurd this (lt_irrefl 0)
  · exact heq
  · have := re_xiField_integral_strictAnti ρ hρ h2 h1 hgt
    rw [key t₁ h1 hz1, key t₂ h2 hz2] at this
    exact absurd this (lt_irrefl 0)

/-! ### Proposition 1: the conformal barycenter exists and is unique

Both halves are proved below for an arbitrary *boundary family* `u`, that is,
a continuous unit-modulus `u : ℝ → ℂ` injective on `(0, 2π)`.  The standard
family `θ ↦ e^{iθ}` gives Proposition 1 as stated in the paper; the extension
operator of Section 3 needs `θ ↦ φ(e^{iθ})` for a homeomorphism `φ` of `S¹`,
which is the pushforward measure `φ_*(η_z)` written without ever asking for a
density of its own.  That generality costs nothing here and is what makes
`barycenter_existsUnique` reachable: a circle homeomorphism need not carry
harmonic measure to an absolutely continuous measure, so there is no density
on `S¹` to feed the special case.

*Uniqueness* rests on the strict monotonicity of `t ↦ Re g_t(ζ)` along the real
diameter (`re_diskAut_strictAnti`), averaged against `μ` transported by a disk
automorphism (`re_diskAut_integral_strictAnti`).  Two zeros `w₁, w₂` of the
average are moved to `0` and `a = g_{w₁}(w₂)` by `g_{w₁}`, and
`diskAut_apply_diskAut` turns the second equation into the vanishing of the
same average at `|a|` after a rotation; strict monotonicity then forces
`a = 0`.  No change of variables on `S¹` is needed: the transported measure
only ever appears inside integrals `⨍ F(g_{w₁}(u θ)) ρ(θ) dθ`, never through a
density of its own.

*Existence* is a one-dimensional argument.  For each direction `α` the function
`t ↦ Re ⨍ g_t dμ_α`, where `μ_α` is `μ` rotated by `α` — which for a boundary
family means replacing `u` by `e^{-iα}u` (`rotFam`), leaving the density
untouched — is strictly decreasing and tends to `∓1` as `t → ±1` (dominated
convergence; `μ` has no atoms because `u` is injective on `(0, 2π)`), so it has
a unique zero `T(α)`; `T` is continuous because the sign of the function at
`T(α₀) ∓ ε` persists for nearby `α`.  The remaining component
`Q(α) = Im ⨍ g_{T(α)} dμ_α` satisfies `Q(α + π) = -Q(α)`, so it vanishes at
some `α*` by the intermediate value theorem, and `w = T(α*)·e^{iα*}` is a zero
of the average.  This replaces the paper's degree-theoretic index count, which
Mathlib has no machinery for. -/

section Proposition1

open Topology Filter

/-! ### Part A: the normalized average over a boundary family -/

/-- A *boundary family*: a continuous unit-modulus `u : ℝ → ℂ` that is injective
on `(0, 2π)`.  The standard one is `θ ↦ e^{iθ}`; the extension operator of
Section 3 needs `θ ↦ φ(e^{iθ})` for a homeomorphism `φ` of `S¹`. -/
def IsBoundaryFamily (u : ℝ → ℂ) : Prop :=
  Continuous u ∧ (∀ θ, ‖u θ‖ = 1) ∧
    ∀ θ θ' : ℝ, θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) → θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi) →
      u θ = u θ' → θ = θ'

/-- `⨍ g_w(u θ) ρ(θ) dθ/2π`. -/
def avgDiskAut (u : ℝ → ℂ) (ρ : ℝ → ℝ) (w : ℂ) : ℂ :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), diskAut w (u θ) * (ρ θ : ℂ)

theorem continuous_diskAut_family {w : ℂ} (hw : ‖w‖ < 1) {u : ℝ → ℂ} (huc : Continuous u)
    (hu1 : ∀ θ, ‖u θ‖ = 1) : Continuous fun θ : ℝ => diskAut w (u θ) := by
  have hden : ∀ θ : ℝ, (1:ℂ) - star w * u θ ≠ 0 :=
    fun θ => diskAut_denom_ne_zero _ _ hw (le_of_eq (hu1 θ))
  simp only [diskAut]
  exact Continuous.div (by fun_prop) (by fun_prop) hden

theorem continuous_diskAut_family_mul {w : ℂ} (hw : ‖w‖ < 1) {u : ℝ → ℂ} (huc : Continuous u)
    (hu1 : ∀ θ, ‖u θ‖ = 1) {ρ : ℝ → ℝ} (hρc : Continuous ρ) :
    Continuous fun θ : ℝ => diskAut w (u θ) * (ρ θ : ℂ) :=
  (continuous_diskAut_family hw huc hu1).mul (Complex.continuous_ofReal.comp hρc)

/-- The vector field `ξ_μ` is the average of `g_w` over the standard boundary
family, stripped of its factor `1 - |w|²`. -/
theorem xiField_eq_avgDiskAut (ρ : ℝ → ℝ) (w : ℂ) :
    xiField ρ w
      = (1 - ((‖w‖ : ℝ) : ℂ) ^ 2)
        * avgDiskAut (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) ρ w := by
  rw [xiField, avgDiskAut]
  simp only [diskAut]
  ring

theorem xiField_eq_zero_iff (ρ : ℝ → ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    xiField ρ w = 0
      ↔ avgDiskAut (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) ρ w = 0 := by
  rw [xiField_eq_avgDiskAut]
  have hne : (1 - ((‖w‖ : ℝ) : ℂ) ^ 2) ≠ 0 := by
    intro h
    have : ((‖w‖ : ℝ) : ℂ) ^ 2 = 1 := by linear_combination -h
    have h2 : ((‖w‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination this
    have h3 : ‖w‖ ^ 2 = 1 := by exact_mod_cast h2
    nlinarith [norm_nonneg w]
  constructor
  · intro h; rcases mul_eq_zero.1 h with h | h
    · exact absurd h hne
    · exact h
  · intro h; rw [h, mul_zero]

/-- The real part of `⨍ g_t(ζ) dμ(ζ)` for real `t`. -/
theorem re_avgDiskAut_real (ρ : ℝ → ℝ) (hρc : Continuous ρ) (u : ℝ → ℂ) (huc : Continuous u)
    (hu1 : ∀ θ, ‖u θ‖ = 1) {t : ℝ} (ht : |t| < 1) :
    ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi),
        diskAut (t : ℂ) (u θ) * (ρ θ : ℂ)).re
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t : ℂ) (u θ)).re * ρ θ := by
  have hnorm : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hden : ∀ θ : ℝ, (1:ℂ) - star (t:ℂ) * u θ ≠ 0 :=
    fun θ => diskAut_denom_ne_zero _ _ hnorm (le_of_eq (hu1 θ))
  have hcont : Continuous fun θ : ℝ => diskAut (t : ℂ) (u θ) * (ρ θ : ℂ) := by
    refine Continuous.mul ?_ (Complex.continuous_ofReal.comp hρc)
    simp only [diskAut]
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  have hre := (Complex.reCLM.intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))).symm
  simp only [Complex.reCLM_apply] at hre
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [Complex.mul_re]

theorem re_avgDiskAut_eq {u : ℝ → ℂ} (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1)
    {ρ : ℝ → ℝ} (hρc : Continuous ρ) {t : ℝ} (ht : |t| < 1) :
    (avgDiskAut u ρ (t : ℂ)).re
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t : ℂ) (u θ)).re * ρ θ :=
  re_avgDiskAut_real ρ hρc u huc hu1 ht

/-! ### Part B: uniqueness -/

theorem diskAut_inj {a : ℂ} (ha : ‖a‖ < 1) {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (h : diskAut a z = diskAut a z') : z = z' := by
  have h1 := diskAut_denom_ne_zero a z ha hz
  have h2 := diskAut_denom_ne_zero a z' ha hz'
  have hna : star a * a ≠ 1 := by
    intro hcon
    have : ((‖a‖:ℝ):ℂ) ^ 2 = 1 := by rw [← Complex.conj_mul']; exact hcon
    have h3 : ‖a‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg a]
  rw [diskAut, diskAut, div_eq_div_iff h1 h2] at h
  have hkey : (z - z') * (1 - star a * a) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hkey with h4 | h4
  · exact sub_eq_zero.1 h4
  · exact absurd (by linear_combination -h4 : star a * a = 1) hna

theorem eq_one_or_neg_one_of_re_sq_one {z : ℂ} (h1 : ‖z‖ = 1) (h2 : z.re ^ 2 = 1) :
    z = 1 ∨ z = -1 := by
  have hns : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [h1] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [h]
  have him : z.im = 0 := by nlinarith
  have hfac : (z.re - 1) * (z.re + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 hfac with h | h
  · exact Or.inl (Complex.ext (by simp; linarith) (by simpa using him))
  · exact Or.inr (Complex.ext (by simp; linarith) (by simpa using him))

/-- If `u` takes unit values and is injective on `(0, 2π)`, then the density is
positive at some interior point where `u` avoids `±1`.  Three points of an
interval on which `ρ > 0` cannot all land in the two-element set `{1, -1}`. -/
theorem exists_pos_re_sq_lt_one (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ)
    (u : ℝ → ℂ) (hu1 : ∀ θ, ‖u θ‖ = 1)
    (huinj : ∀ θ θ' : ℝ, θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) → θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi) →
      u θ = u θ' → θ = θ') :
    ∃ θ₀ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), 0 < ρ θ₀ ∧ (u θ₀).re ^ 2 < 1 := by
  obtain ⟨hρc, hρnn, hρper, hρtot⟩ := hρ
  obtain ⟨θ₀, hθ₀mem, hθ₀pos, -⟩ :=
    exists_pos_of_isProbabilityDensity ρ ⟨hρc, hρnn, hρper, hρtot⟩
  have hopen : IsOpen ({θ : ℝ | 0 < ρ θ} ∩ Set.Ioo (0:ℝ) (2 * Real.pi)) :=
    (isOpen_lt continuous_const hρc).inter isOpen_Ioo
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hopen θ₀ ⟨hθ₀pos, hθ₀mem⟩
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hmem : ∀ k : ℝ, 0 ≤ k → k ≤ 2 →
      θ₀ + k * δ ∈ {θ : ℝ | 0 < ρ θ} ∩ Set.Ioo (0:ℝ) (2 * Real.pi) := by
    intro k hk0 hk2
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have : |θ₀ + k * δ - θ₀| = k * δ := by
      rw [show θ₀ + k * δ - θ₀ = k * δ by ring, abs_of_nonneg (by positivity)]
    rw [this]
    nlinarith
  by_contra hcon
  push Not at hcon
  have hval : ∀ k : ℝ, 0 ≤ k → k ≤ 2 → u (θ₀ + k * δ) = 1 ∨ u (θ₀ + k * δ) = -1 := by
    intro k hk0 hk2
    have hm := hmem k hk0 hk2
    have h1 := hcon _ hm.2 hm.1
    have hle : (u (θ₀ + k * δ)).re ^ 2 ≤ 1 := by
      have := Complex.normSq_eq_norm_sq (u (θ₀ + k * δ))
      rw [hu1] at this
      simp only [Complex.normSq_apply] at this
      nlinarith [sq_nonneg (u (θ₀ + k * δ)).im]
    exact eq_one_or_neg_one_of_re_sq_one (hu1 _) (le_antisymm hle h1)
  have hinj2 : ∀ k k' : ℝ, 0 ≤ k → k ≤ 2 → 0 ≤ k' → k' ≤ 2 →
      u (θ₀ + k * δ) = u (θ₀ + k' * δ) → k = k' := by
    intro k k' hk0 hk2 hk'0 hk'2 h
    have := huinj _ _ (hmem k hk0 hk2).2 (hmem k' hk'0 hk'2).2 h
    have hd : k * δ = k' * δ := by linarith
    exact mul_right_cancel₀ (ne_of_gt hδ) hd
  have h0 := hval 0 le_rfl (by norm_num)
  have h1 := hval 1 (by norm_num) (by norm_num)
  have h2 := hval 2 (by norm_num) le_rfl
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
  · exact absurd (hinj2 0 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (e0.trans e1.symm))
      (by norm_num)
  · exact absurd (hinj2 0 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (e0.trans e1.symm))
      (by norm_num)
  · exact absurd (hinj2 0 2 le_rfl (by norm_num) (by norm_num) le_rfl (e0.trans e2.symm))
      (by norm_num)
  · exact absurd (hinj2 1 2 (by norm_num) (by norm_num) (by norm_num) le_rfl (e1.trans e2.symm))
      (by norm_num)
  · exact absurd (hinj2 1 2 (by norm_num) (by norm_num) (by norm_num) le_rfl (e1.trans e2.symm))
      (by norm_num)
  · exact absurd (hinj2 0 2 le_rfl (by norm_num) (by norm_num) le_rfl (e0.trans e2.symm))
      (by norm_num)
  · exact absurd (hinj2 0 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (e0.trans e1.symm))
      (by norm_num)
  · exact absurd (hinj2 0 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (e0.trans e1.symm))
      (by norm_num)

theorem continuous_re_diskAut_comp {t : ℝ} (ht : |t| < 1) (ρ : ℝ → ℝ) (hρc : Continuous ρ)
    (u : ℝ → ℂ) (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1) :
    Continuous fun θ : ℝ => (diskAut (t : ℂ) (u θ)).re * ρ θ := by
  have hnorm : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hden : ∀ θ : ℝ, (1:ℂ) - star (t:ℂ) * u θ ≠ 0 :=
    fun θ => diskAut_denom_ne_zero _ _ hnorm (le_of_eq (hu1 θ))
  have h1 : Continuous fun θ : ℝ => diskAut (t : ℂ) (u θ) := by
    simp only [diskAut]
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  exact (Complex.continuous_re.comp h1).mul hρc

/-- The mechanism behind uniqueness: averaged against any probability density,
`Re g_t` is strictly decreasing in `t` along any continuous unit-modulus family
`u` that avoids `±1` somewhere on the support. -/
theorem re_diskAut_integral_strictAnti (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ)
    (u : ℝ → ℂ) (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1)
    {θ₀ : ℝ} (hθ₀mem : θ₀ ∈ Set.Ioo (0:ℝ) (2 * Real.pi)) (hθ₀pos : 0 < ρ θ₀)
    (hθ₀re : (u θ₀).re ^ 2 < 1)
    {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1) (hlt : t₁ < t₂) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t₂ : ℂ) (u θ)).re * ρ θ)
      < ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (t₁ : ℂ) (u θ)).re * ρ θ := by
  have hρc := hρ.1
  have hρnn := hρ.2.1
  have hc1 := continuous_re_diskAut_comp h1 ρ hρc u huc hu1
  have hc2 := continuous_re_diskAut_comp h2 ρ hρc u huc hu1
  have hFcont : Continuous fun θ : ℝ => (diskAut (t₁ : ℂ) (u θ)).re * ρ θ
      - (diskAut (t₂ : ℂ) (u θ)).re * ρ θ := hc1.sub hc2
  have hFnn : ∀ θ : ℝ, 0 ≤ (diskAut (t₁ : ℂ) (u θ)).re * ρ θ
      - (diskAut (t₂ : ℂ) (u θ)).re * ρ θ := by
    intro θ
    have hmono := re_diskAut_antitone h1 h2 hlt.le (u θ) (hu1 θ)
    have := mul_le_mul_of_nonneg_right hmono (hρnn θ)
    linarith
  have hFpos : 0 < (diskAut (t₁ : ℂ) (u θ₀)).re * ρ θ₀
      - (diskAut (t₂ : ℂ) (u θ₀)).re * ρ θ₀ := by
    have hstrict := re_diskAut_strictAnti h1 h2 hlt (u θ₀) (hu1 θ₀) hθ₀re
    nlinarith [hθ₀pos]
  have hpos := intervalIntegral_pos_of_pos_at hFcont hFnn hθ₀mem hFpos
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    at hpos
  linarith

section Aux
variable (ρ : ℝ → ℝ)

theorem diskAut_zero_left (z : ℂ) : diskAut 0 z = z := by simp [diskAut]

theorem re_integral_zero_of_integral_zero (hρc : Continuous ρ)
    (v : ℝ → ℂ) (hvc : Continuous v)
    (h : ∫ θ in (0:ℝ)..(2 * Real.pi), v θ * (ρ θ : ℂ) = 0) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), (v θ).re * ρ θ = 0 := by
  have hcont : Continuous fun θ : ℝ => v θ * ((ρ θ : ℝ) : ℂ) :=
    hvc.mul (Complex.continuous_ofReal.comp hρc)
  have hre := (Complex.reCLM.intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))).symm
  simp only [Complex.reCLM_apply] at hre
  have h2 : (∫ θ in (0:ℝ)..(2 * Real.pi), v θ * ((ρ θ : ℝ) : ℂ)).re = 0 := by rw [h]; simp
  rw [hre] at h2
  refine Eq.trans ?_ h2
  apply intervalIntegral.integral_congr
  intro θ _
  simp [Complex.mul_re]

end Aux

/-- `Circle.exp` is injective on `(0, 2π)`. -/
theorem circle_exp_inj_on {θ θ' : ℝ} (h : θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi))
    (h' : θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi))
    (heq : ((Circle.exp θ : Circle) : ℂ) = ((Circle.exp θ' : Circle) : ℂ)) : θ = θ' := by
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have hreal : θ = θ' + (n : ℝ) * (2 * Real.pi) := by
    have hcast : ((θ : ℝ) : ℂ) = (((θ' + (n : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) := by
      field_simp at hn
      push_cast
      linear_combination hn
    exact_mod_cast hcast
  have hpi := Real.pi_pos
  rcases lt_trichotomy n 0 with hlt | heq0 | hgt
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith [h.1, h'.2]
  · rw [heq0] at hreal; simpa using hreal
  · have : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (1:ℤ) ≤ n)
    nlinarith [h.2, h'.1]

/-- `g_a(λ·η) = λ·g_r(η)` when `a = λ·r` with `r` real and `|λ| = 1`: a
rotation conjugates `g_a` into the real-diameter automorphism `g_r`. -/
theorem diskAut_rotate {lam : ℂ} (hlam : star lam * lam = 1) (r : ℝ) (η : ℂ) :
    diskAut (lam * (r : ℂ)) (lam * η) = lam * diskAut (r : ℂ) η := by
  have hden : (1:ℂ) - star (lam * (r : ℂ)) * (lam * η) = 1 - (r : ℂ) * η := by
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Complex.star_def] at hlam
    linear_combination (-(r : ℂ) * η) * hlam
  rw [diskAut, diskAut, hden]
  rw [show lam * η - lam * (r : ℂ) = lam * (η - (r : ℂ)) by ring]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [mul_div_assoc]

/-- **Uniqueness in Proposition 1**, for an arbitrary boundary family. -/
theorem avgDiskAut_zero_unique {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {ρ : ℝ → ℝ} (hρ : IsProbabilityDensity ρ)
    {w₁ w₂ : ℂ} (hw1 : ‖w₁‖ < 1) (hw2 : ‖w₂‖ < 1)
    (hz1 : avgDiskAut u ρ w₁ = 0) (hz2 : avgDiskAut u ρ w₂ = 0) : w₁ = w₂ := by
  obtain ⟨huc, hu1, huinj⟩ := hu
  have hρc := hρ.1
  have hC : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    positivity
  have hI : ∀ w : ℂ, avgDiskAut u ρ w = 0 →
      ∫ θ in (0:ℝ)..(2 * Real.pi), diskAut w (u θ) * (ρ θ : ℂ) = 0 := by
    intro w hz
    rw [avgDiskAut] at hz
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' hC
    · exact h'
  have hI1 := hI w₁ hz1
  have hI2 := hI w₂ hz2
  set a : ℂ := diskAut w₁ w₂ with hadef
  have hanorm : ‖a‖ < 1 := diskAut_maps_disk_to_disk w₁ w₂ hw1 hw2
  suffices hzero : a = 0 by
    rw [hadef, diskAut, div_eq_zero_iff] at hzero
    rcases hzero with h | h
    · exact (sub_eq_zero.1 h).symm
    · exact absurd h (diskAut_denom_ne_zero w₁ w₂ hw1 hw2.le)
  by_contra hane
  set r : ℝ := ‖a‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.2 hane
  set lam : ℂ := a / (r : ℂ) with hlamdef
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hr0)
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlamdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← hrdef]
    exact div_self (ne_of_gt hr0)
  have hlamstar : star lam * lam = 1 := star_mul_self_of_norm_one hlamnorm
  have halam : a = lam * (r : ℂ) := by rw [hlamdef]; field_simp
  set v : ℝ → ℂ := fun θ => star lam * diskAut w₁ (u θ) with hvdef
  have hv1 : ∀ θ, ‖v θ‖ = 1 := by
    intro θ
    rw [hvdef]
    simp only [norm_mul, norm_star, hlamnorm, one_mul]
    exact diskAut_norm_eq_one w₁ _ hw1 (hu1 θ)
  have hvc : Continuous v := continuous_const.mul (continuous_diskAut_family hw1 huc hu1)
  have hlamne : lam ≠ 0 := by
    intro hc; rw [hc] at hlamstar; simp at hlamstar
  have hlamsne : star lam ≠ 0 := by
    intro hc; rw [hc] at hlamstar; simp at hlamstar
  have hvinj : ∀ θ θ' : ℝ, θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) →
      θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi) → v θ = v θ' → θ = θ' := by
    intro θ θ' hθ hθ' h
    rw [hvdef] at h
    simp only at h
    have h2 := mul_left_cancel₀ hlamsne h
    exact huinj θ θ' hθ hθ'
      (diskAut_inj hw1 (le_of_eq (hu1 θ)) (le_of_eq (hu1 θ')) h2)
  obtain ⟨θ₀, hθ₀mem, hθ₀pos, hθ₀re⟩ := exists_pos_re_sq_lt_one ρ hρ v hv1 hvinj
  have key0 : ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (0 : ℂ) (v θ)).re * ρ θ = 0 := by
    have hstep : ∫ θ in (0:ℝ)..(2 * Real.pi), v θ * (ρ θ : ℂ) = 0 := by
      rw [show (fun θ : ℝ => v θ * (ρ θ : ℂ))
          = fun θ : ℝ => star lam * (diskAut w₁ (u θ) * (ρ θ : ℂ)) by
        funext θ; rw [hvdef]; ring]
      rw [intervalIntegral.integral_const_mul, hI1, mul_zero]
    have hzz := re_integral_zero_of_integral_zero ρ hρc v hvc hstep
    refine Eq.trans ?_ hzz
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [diskAut_zero_left]
  have keyr : ∫ θ in (0:ℝ)..(2 * Real.pi), (diskAut (r : ℂ) (v θ)).re * ρ θ = 0 := by
    have hnat : ∀ θ : ℝ, diskAut (r : ℂ) (v θ)
        = (star lam * ((1 - w₁ * star w₂) / (1 - star w₁ * w₂))) * diskAut w₂ (u θ) := by
      intro θ
      have hbase := diskAut_apply_diskAut 1 w₁ w₂ (u θ) (by simp) hw1 hw2 (le_of_eq (hu1 θ))
      simp only [one_mul] at hbase
      have hlu : lam * v θ = diskAut w₁ (u θ) := by
        rw [hvdef]
        simp only
        rw [← mul_assoc, mul_comm lam (star lam), hlamstar, one_mul]
      have hrot : diskAut a (lam * v θ) = lam * diskAut (r : ℂ) (v θ) := by
        rw [halam]; exact diskAut_rotate hlamstar r (v θ)
      rw [hlu, hadef] at hrot
      rw [hbase] at hrot
      have : lam * diskAut (r : ℂ) (v θ)
          = lam * ((star lam * ((1 - w₁ * star w₂) / (1 - star w₁ * w₂))) * diskAut w₂ (u θ)) := by
        rw [← hrot]
        rw [show lam * ((star lam * ((1 - w₁ * star w₂) / (1 - star w₁ * w₂)))
            * diskAut w₂ (u θ))
            = (lam * star lam) * (((1 - w₁ * star w₂) / (1 - star w₁ * w₂))
              * diskAut w₂ (u θ)) by ring,
          mul_comm lam (star lam), hlamstar, one_mul]
      exact mul_left_cancel₀ hlamne this
    have hstep : ∫ θ in (0:ℝ)..(2 * Real.pi), diskAut (r : ℂ) (v θ) * (ρ θ : ℂ) = 0 := by
      rw [show (fun θ : ℝ => diskAut (r : ℂ) (v θ) * (ρ θ : ℂ))
          = fun θ : ℝ => (star lam * ((1 - w₁ * star w₂) / (1 - star w₁ * w₂)))
              * (diskAut w₂ (u θ) * (ρ θ : ℂ)) by
        funext θ; rw [hnat θ]; ring]
      rw [intervalIntegral.integral_const_mul, hI2, mul_zero]
    refine re_integral_zero_of_integral_zero ρ hρc _ ?_ hstep
    have hnorm : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hanorm
    exact continuous_diskAut_family hnorm hvc hv1
  have hrabs : |r| < 1 := by rwa [abs_of_pos hr0]
  have := re_diskAut_integral_strictAnti ρ hρ v hvc hv1 hθ₀mem hθ₀pos hθ₀re
    (t₁ := 0) (t₂ := r) (by norm_num) hrabs hr0
  simp only [Complex.ofReal_zero] at this
  rw [key0, keyr] at this
  exact lt_irrefl 0 this

/-! ### Part C: existence -/

theorem coe_circle_exp_add (x y : ℝ) :
    ((Circle.exp (x + y) : Circle) : ℂ)
      = ((Circle.exp x : Circle) : ℂ) * ((Circle.exp y : Circle) : ℂ) := by
  simp only [Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coe_circle_exp_two_pi : ((Circle.exp (2 * Real.pi) : Circle) : ℂ) = 1 := by
  rw [Circle.coe_exp]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem coe_circle_exp_pi : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
  rw [Circle.coe_exp]
  rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem coe_circle_exp_add_two_pi (x : ℝ) :
    ((Circle.exp (x + 2 * Real.pi) : Circle) : ℂ) = ((Circle.exp x : Circle) : ℂ) := by
  rw [coe_circle_exp_add, coe_circle_exp_two_pi, mul_one]

theorem star_coe_circle_exp_mul (α : ℝ) :
    star ((Circle.exp α : Circle) : ℂ) * ((Circle.exp α : Circle) : ℂ) = 1 := by
  have h := Complex.conj_mul' ((Circle.exp α : Circle) : ℂ)
  rw [← Complex.star_def] at h
  rw [h, Circle.norm_coe]
  norm_num

/-- `g_t(ζ) - g_s(ζ) = (t-s)(ζ² - 1)/((1-tζ)(1-sζ))`, hence a Lipschitz bound in
`t` that is uniform in the boundary point. -/
theorem norm_diskAut_sub_le {s t : ℝ} (hs : |s| < 1) (ht : |t| < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖diskAut (t : ℂ) ζ - diskAut (s : ℂ) ζ‖ ≤ |t - s| * 2 / ((1 - |t|) * (1 - |s|)) := by
  have hns : ‖(s : ℂ)‖ < 1 := by simpa using hs
  have hnt : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hds := diskAut_denom_ne_zero (s : ℂ) ζ hns hζ.le
  have hdt := diskAut_denom_ne_zero (t : ℂ) ζ hnt hζ.le
  have hkey : diskAut (t : ℂ) ζ - diskAut (s : ℂ) ζ
      = ((t : ℂ) - (s : ℂ)) * (ζ ^ 2 - 1)
        / ((1 - star (t : ℂ) * ζ) * (1 - star (s : ℂ) * ζ)) := by
    rw [diskAut, diskAut, div_sub_div _ _ hdt hds]
    simp only [Complex.star_def, Complex.conj_ofReal]
    congr 1
    ring
  have hlb : ∀ r : ℝ, |r| < 1 → 1 - |r| ≤ ‖1 - star (r : ℂ) * ζ‖ := by
    intro r hr
    have h1 : ‖star (r : ℂ) * ζ‖ = |r| := by
      rw [norm_mul, hζ, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_one]
    have h2 := norm_sub_norm_le (1 : ℂ) (star (r : ℂ) * ζ)
    simp only [norm_one, h1] at h2
    linarith
  have hnum : ‖((t : ℂ) - (s : ℂ)) * (ζ ^ 2 - 1)‖ ≤ |t - s| * 2 := by
    rw [norm_mul]
    have h1 : ‖((t : ℂ) - (s : ℂ))‖ = |t - s| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖ζ ^ 2 - 1‖ ≤ 2 := by
      calc ‖ζ ^ 2 - 1‖ ≤ ‖ζ ^ 2‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hζ]; norm_num
    rw [h1]
    nlinarith [abs_nonneg (t - s), norm_nonneg (ζ ^ 2 - 1)]
  have habt := abs_nonneg t
  have habs := abs_nonneg s
  have hdpos : (0:ℝ) < (1 - |t|) * (1 - |s|) := mul_pos (by linarith) (by linarith)
  have hb1 := hlb t ht
  have hb2 := hlb s hs
  have h3 : (1 - |t|) * (1 - |s|)
      ≤ ‖1 - star (t : ℂ) * ζ‖ * ‖1 - star (s : ℂ) * ζ‖ :=
    mul_le_mul hb1 hb2 (by linarith) (by linarith)
  rw [hkey, norm_div, norm_mul (1 - star (t : ℂ) * ζ) (1 - star (s : ℂ) * ζ),
    div_le_div_iff₀ (by rw [← norm_mul]; exact norm_pos_iff.2 (mul_ne_zero hdt hds)) hdpos]
  calc ‖((t : ℂ) - (s : ℂ)) * (ζ ^ 2 - 1)‖ * ((1 - |t|) * (1 - |s|))
      ≤ (|t - s| * 2) * ((1 - |t|) * (1 - |s|)) :=
        mul_le_mul_of_nonneg_right hnum hdpos.le
    _ ≤ (|t - s| * 2) * (‖1 - star (t : ℂ) * ζ‖ * ‖1 - star (s : ℂ) * ζ‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

theorem diskAut_one_of_ne {ζ : ℂ} (hζ : ζ ≠ 1) : diskAut (1 : ℂ) ζ = -1 := by
  rw [diskAut, star_one, one_mul]
  rw [show ζ - 1 = -(1 - ζ) by ring, neg_div, div_self (sub_ne_zero.2 (Ne.symm hζ))]

/-! ### Rotating the boundary family -/

/-- Rotating the measure: `u` composed with `ζ ↦ e^{-iα}ζ`. -/
def rotFam (u : ℝ → ℂ) (α : ℝ) : ℝ → ℂ :=
  fun θ => star ((Circle.exp α : Circle) : ℂ) * u θ

theorem rotFam_zero (u : ℝ → ℂ) : rotFam u 0 = u := by
  funext θ
  simp [rotFam]

theorem isBoundaryFamily_rotFam {u : ℝ → ℂ} (hu : IsBoundaryFamily u) (α : ℝ) :
    IsBoundaryFamily (rotFam u α) := by
  obtain ⟨huc, hu1, huinj⟩ := hu
  have hne : star ((Circle.exp α : Circle) : ℂ) ≠ 0 := by
    intro hc
    have h := star_coe_circle_exp_mul α
    rw [hc, zero_mul] at h
    exact zero_ne_one h
  refine ⟨continuous_const.mul huc, fun θ => ?_, fun θ θ' hθ hθ' h => ?_⟩
  · show ‖star ((Circle.exp α : Circle) : ℂ) * u θ‖ = 1
    rw [norm_mul, norm_star, Circle.norm_coe, one_mul]
    exact hu1 θ
  · exact huinj θ θ' hθ hθ' (mul_left_cancel₀ hne h)

/-- `g_{te^{iα}}` averaged over `u` is `e^{iα}` times `g_t` averaged over the
rotated family. -/
theorem avgDiskAut_rot (u : ℝ → ℂ) (ρ : ℝ → ℝ) (t α : ℝ) :
    avgDiskAut u ρ ((t : ℂ) * ((Circle.exp α : Circle) : ℂ))
      = ((Circle.exp α : Circle) : ℂ) * avgDiskAut (rotFam u α) ρ (t : ℂ) := by
  set e : ℂ := ((Circle.exp α : Circle) : ℂ) with hedef
  have hestar : star e * e = 1 := star_coe_circle_exp_mul α
  have hes : e * star e = 1 := by rw [mul_comm]; exact hestar
  have hpt : ∀ θ : ℝ, diskAut ((t : ℂ) * e) (u θ) = e * diskAut (t : ℂ) (rotFam u α θ) := by
    intro θ
    have h := diskAut_rotate hestar t (star e * u θ)
    rw [show e * (star e * u θ) = u θ by rw [← mul_assoc, hes, one_mul]] at h
    rw [show ((t : ℂ) * e) = e * (t : ℂ) by ring]
    exact h
  simp only [avgDiskAut]
  rw [intervalIntegral.integral_congr
      (g := fun θ : ℝ => e * (diskAut (t : ℂ) (rotFam u α θ) * (ρ θ : ℂ)))
      (fun θ _ => by rw [hpt θ]; ring),
    intervalIntegral.integral_const_mul]
  ring

theorem rotFam_add_pi (u : ℝ → ℂ) (α : ℝ) :
    rotFam u (α + Real.pi) = fun θ => -(rotFam u α θ) := by
  funext θ
  show star ((Circle.exp (α + Real.pi) : Circle) : ℂ) * u θ
      = -(star ((Circle.exp α : Circle) : ℂ) * u θ)
  rw [coe_circle_exp_add, coe_circle_exp_pi]
  simp only [star_mul, star_neg, star_one]
  ring

theorem diskAut_neg_arg (t : ℝ) (η : ℂ) :
    diskAut ((t : ℝ) : ℂ) (-η) = - diskAut ((-t : ℝ) : ℂ) η := by
  simp only [diskAut, Complex.ofReal_neg, star_neg, Complex.star_def, Complex.conj_ofReal]
  rw [show (-η - (t : ℂ)) = -(η - -(t : ℂ)) by ring,
    show (1 : ℂ) - (t : ℂ) * -η = 1 - -(t : ℂ) * η by ring, neg_div]

/-- The antipodal symmetry `Ψ(α + π, t) = -Ψ(α, -t)`. -/
theorem avgDiskAut_rot_antipode (u : ℝ → ℂ) (ρ : ℝ → ℝ) (t α : ℝ) :
    avgDiskAut (rotFam u (α + Real.pi)) ρ ((t : ℝ) : ℂ)
      = - avgDiskAut (rotFam u α) ρ ((-t : ℝ) : ℂ) := by
  simp only [avgDiskAut]
  rw [rotFam_add_pi]
  rw [intervalIntegral.integral_congr
      (g := fun θ : ℝ => -(diskAut ((-t : ℝ) : ℂ) (rotFam u α θ) * (ρ θ : ℂ)))
      (fun θ _ => by rw [diskAut_neg_arg]; ring),
    intervalIntegral.integral_neg]
  ring

/-! ### Continuity in the radial parameter -/

theorem norm_avgDiskAut_sub_le {u : ℝ → ℂ} (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) {s t : ℝ} (hs : |s| < 1) (ht : |t| < 1) :
    ‖avgDiskAut u σ (t : ℂ) - avgDiskAut u σ (s : ℂ)‖
      ≤ |t - s| * 2 / ((1 - |t|) * (1 - |s|)) := by
  obtain ⟨hσc, hσnn, hσper, hσtot⟩ := hσ
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have htot : ∫ θ in (0:ℝ)..(2 * Real.pi), σ θ = 2 * Real.pi := by
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hσtot; linarith
  set K : ℝ := |t - s| * 2 / ((1 - |t|) * (1 - |s|)) with hKdef
  have habt := abs_nonneg t
  have habs := abs_nonneg s
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : (0:ℝ) < (1 - |t|) * (1 - |s|) := mul_pos (by linarith) (by linarith)
    positivity
  have hcont : ∀ r : ℝ, |r| < 1 →
      Continuous fun θ : ℝ => diskAut (r : ℂ) (u θ) * (σ θ : ℂ) := fun r hr =>
    continuous_diskAut_family_mul (by simpa using hr) huc hu1 hσc
  have hsub : avgDiskAut u σ (t : ℂ) - avgDiskAut u σ (s : ℂ)
      = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi),
          (diskAut (t : ℂ) (u θ) - diskAut (s : ℂ) (u θ)) * (σ θ : ℂ) := by
    rw [avgDiskAut, avgDiskAut, ← mul_sub, ← intervalIntegral.integral_sub
      (((hcont t ht).intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi)))
      (((hcont s hs).intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi)))]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  have hbound : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
      ‖(diskAut (t : ℂ) (u θ) - diskAut (s : ℂ) (u θ)) * (σ θ : ℂ)‖ ≤ K * σ θ := by
    filter_upwards with θ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσnn θ)]
    exact mul_le_mul_of_nonneg_right (norm_diskAut_sub_le hs ht (hu1 θ)) (hσnn θ)
  have hle := intervalIntegral.norm_integral_le_of_norm_le hpi.le hbound
    ((continuous_const.mul hσc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, htot] at hle
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi),
        (diskAut (t : ℂ) (u θ) - diskAut (s : ℂ) (u θ)) * (σ θ : ℂ)‖
      ≤ (2 * Real.pi)⁻¹ * (K * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = K := by field_simp

theorem continuousAt_avgDiskAut {u : ℝ → ℂ} (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) {t₀ : ℝ} (ht₀ : |t₀| < 1) :
    ContinuousAt (fun t : ℝ => avgDiskAut u σ (t : ℂ)) t₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hab0 := abs_nonneg t₀
  set c : ℝ := (1 + |t₀|) / 2 with hcdef
  have hc1 : |t₀| < c := by rw [hcdef]; linarith
  have hc2 : c < 1 := by rw [hcdef]; linarith
  set K : ℝ := 2 / ((1 - c) * (1 - |t₀|)) with hKdef
  have hd1 : (0:ℝ) < (1 - c) * (1 - |t₀|) := mul_pos (by linarith) (by linarith)
  have hK : 0 < K := by rw [hKdef]; positivity
  refine ⟨min (c - |t₀|) (ε / K), lt_min (by linarith) (by positivity), ?_⟩
  intro t hdist
  rw [Real.dist_eq] at hdist
  have h1 : |t - t₀| < c - |t₀| := lt_of_lt_of_le hdist (min_le_left _ _)
  have h2 : |t - t₀| < ε / K := lt_of_lt_of_le hdist (min_le_right _ _)
  have habt : |t| < c := by
    have := abs_sub_abs_le_abs_sub t t₀
    linarith
  have hbd := norm_avgDiskAut_sub_le huc hu1 hσ (s := t₀) (t := t) ht₀ (lt_trans habt hc2)
  have hd2 : (1 - c) * (1 - |t₀|) ≤ (1 - |t|) * (1 - |t₀|) := by nlinarith
  rw [dist_eq_norm]
  calc ‖avgDiskAut u σ (t : ℂ) - avgDiskAut u σ (t₀ : ℂ)‖
      ≤ |t - t₀| * 2 / ((1 - |t|) * (1 - |t₀|)) := hbd
    _ ≤ |t - t₀| * 2 / ((1 - c) * (1 - |t₀|)) := by gcongr
    _ = K * |t - t₀| := by rw [hKdef]; ring
    _ < K * (ε / K) := mul_lt_mul_of_pos_left h2 hK
    _ = ε := by field_simp

theorem re_avgDiskAut_strictAnti {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) {t₁ t₂ : ℝ} (h1 : |t₁| < 1) (h2 : |t₂| < 1)
    (hlt : t₁ < t₂) : (avgDiskAut u σ (t₂ : ℂ)).re < (avgDiskAut u σ (t₁ : ℂ)).re := by
  obtain ⟨huc, hu1, huinj⟩ := hu
  obtain ⟨θ₀, hθ₀mem, hθ₀pos, hθ₀re⟩ := exists_pos_re_sq_lt_one σ hσ u hu1 huinj
  have hkey := re_diskAut_integral_strictAnti σ hσ u huc hu1 hθ₀mem hθ₀pos hθ₀re h1 h2 hlt
  rw [re_avgDiskAut_eq huc hu1 hσ.1 h1, re_avgDiskAut_eq huc hu1 hσ.1 h2]
  exact mul_lt_mul_of_pos_left hkey (by positivity)


/-! ### Existence -/

/-- A boundary family hits `1` at most once in `(0, 2π)`, so `u θ ≠ 1` almost
everywhere. -/
theorem ae_ne_one_of_isBoundaryFamily {u : ℝ → ℂ} (hu : IsBoundaryFamily u) :
    ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) → u θ ≠ 1 := by
  obtain ⟨huc, hu1, huinj⟩ := hu
  have hsub : Set.Subsingleton {θ : ℝ | θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) ∧ u θ = 1} := by
    rintro a ⟨ha, hua⟩ b ⟨hb, hub⟩
    exact huinj a b ha hb (hua.trans hub.symm)
  have hS : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      {θ : ℝ | θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) ∧ u θ = 1} = 0 := hsub.measure_zero _
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (fun θ hθ => ?_) hS
  simp only [Set.mem_ofPred_eq, Classical.not_imp, not_not] at hθ ⊢
  exact hθ

/-- As `t → 1⁻` the average `⨍ g_t dμ` tends to `-1`: the automorphisms `g_t`
collapse the circle onto `-1` away from the single point `1`, and `μ` has no
atom there. -/
theorem exists_re_avgDiskAut_neg {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) :
    ∃ t : ℝ, |t| < 1 ∧ (avgDiskAut u σ (t : ℂ)).re < 0 := by
  have huc := hu.1
  have hu1 := hu.2.1
  have hane := ae_ne_one_of_isBoundaryFamily hu
  obtain ⟨hσc, hσnn, hσper, hσtot⟩ := hσ
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hIoo : Set.Ioo (-1:ℝ) 1 ∈ nhdsWithin (1:ℝ) (Set.Iio 1) := by
    rw [← Set.Ioi_inter_Iio]
    exact Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num)))
      self_mem_nhdsWithin
  have hlim : Filter.Tendsto (fun t : ℝ => ∫ θ in (0:ℝ)..(2 * Real.pi),
      diskAut ((t : ℝ) : ℂ) (u θ) * (σ θ : ℂ))
      (nhdsWithin (1:ℝ) (Set.Iio 1))
      (𝓝 (∫ θ in (0:ℝ)..(2 * Real.pi), (-1 : ℂ) * (σ θ : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence σ ?_ ?_
      (hσc.intervalIntegrable _ _) ?_
    · filter_upwards [hIoo] with t ht
      have hnt : ‖((t : ℝ) : ℂ)‖ < 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨ht.1, ht.2⟩
      exact (continuous_diskAut_family_mul hnt huc hu1 hσc).aestronglyMeasurable
    · filter_upwards [hIoo] with t ht
      filter_upwards with θ _
      have hnt : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσnn θ),
        diskAut_norm_eq_one _ _ (by simpa using hnt) (hu1 θ), one_mul]
    · have hae : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          θ ≠ 2 * Real.pi := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hae, hane] with θ hθ hθ1 hmem
      rw [Set.uIoc_of_le hpi.le] at hmem
      have hne : u θ ≠ 1 := hθ1 ⟨hmem.1, lt_of_le_of_ne hmem.2 hθ⟩
      have hcont : ContinuousAt (fun t : ℝ => diskAut ((t : ℝ) : ℂ) (u θ)) 1 := by
        simp only [diskAut]
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simp only [Complex.ofReal_one, star_one, one_mul]
        exact sub_ne_zero.2 (Ne.symm hne)
      have h1 : Filter.Tendsto
          (fun t : ℝ => diskAut ((t : ℝ) : ℂ) (u θ)) (𝓝 1) (𝓝 (-1)) := by
        have hc := hcont
        rw [ContinuousAt, show diskAut (((1:ℝ) : ℝ) : ℂ) (u θ) = -1 by
          rw [Complex.ofReal_one]; exact diskAut_one_of_ne hne] at hc
        exact hc
      exact (h1.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
  have hsig : ∫ θ in (0:ℝ)..(2 * Real.pi), ((σ θ : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    have hint : IntervalIntegrable σ MeasureTheory.volume 0 (2 * Real.pi) :=
      hσc.intervalIntegrable _ _
    have h := (Complex.ofRealCLM.intervalIntegral_comp_comm hint).symm
    simp only [Complex.ofRealCLM_apply] at h
    rw [← h]
    congr 1
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hσtot; linarith
  have hlimval : ∫ θ in (0:ℝ)..(2 * Real.pi), (-1 : ℂ) * (σ θ : ℂ)
      = -((2 * Real.pi : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, hsig]; ring
  rw [hlimval] at hlim
  have hlim2 : Filter.Tendsto (fun t : ℝ => avgDiskAut u σ ((t : ℝ) : ℂ))
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (𝓝 (-1)) := by
    have := (tendsto_const_nhds (x := (((2 * Real.pi)⁻¹ : ℝ) : ℂ))
      (f := nhdsWithin (1:ℝ) (Set.Iio 1))).mul hlim
    rw [show (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * -((2 * Real.pi : ℝ) : ℂ) = -1 by
      rw [mul_neg, ← Complex.ofReal_mul,
        show ((2 * Real.pi)⁻¹ : ℝ) * (2 * Real.pi) = 1 by field_simp]
      norm_num] at this
    exact this
  have hre : Filter.Tendsto (fun t : ℝ => (avgDiskAut u σ ((t : ℝ) : ℂ)).re)
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (𝓝 (-1)) := by
    have hcomp := (Complex.continuous_re.tendsto (-1 : ℂ)).comp hlim2
    simp only [Function.comp_def, Complex.neg_re, Complex.one_re] at hcomp
    exact hcomp
  have hev : ∀ᶠ t in nhdsWithin (1:ℝ) (Set.Iio 1), (avgDiskAut u σ ((t : ℝ) : ℂ)).re < 0 :=
    hre.eventually_lt_const (by norm_num)
  obtain ⟨t, ht1, ht2⟩ := ((hev.and (Filter.eventually_of_mem hIoo (fun x hx => hx))).exists)
  exact ⟨t, abs_lt.2 ⟨ht2.1, ht2.2⟩, ht1⟩

theorem exists_re_avgDiskAut_pos {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) :
    ∃ t : ℝ, |t| < 1 ∧ 0 < (avgDiskAut u σ (t : ℂ)).re := by
  obtain ⟨t, ht1, ht2⟩ :=
    exists_re_avgDiskAut_neg (isBoundaryFamily_rotFam hu Real.pi) hσ
  have hkey := avgDiskAut_rot_antipode u σ t 0
  rw [zero_add, rotFam_zero] at hkey
  refine ⟨-t, by rwa [abs_neg], ?_⟩
  rw [hkey] at ht2
  simp only [Complex.neg_re] at ht2
  push_cast at ht2 ⊢
  linarith

theorem existsUnique_re_avgDiskAut_zero {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {σ : ℝ → ℝ} (hσ : IsProbabilityDensity σ) :
    ∃! t : ℝ, |t| < 1 ∧ (avgDiskAut u σ (t : ℂ)).re = 0 := by
  have huc := hu.1
  have hu1 := hu.2.1
  obtain ⟨tp, hp1, hp2⟩ := exists_re_avgDiskAut_neg hu hσ
  obtain ⟨tm, hm1, hm2⟩ := exists_re_avgDiskAut_pos hu hσ
  have hlt : tm < tp := by
    rcases lt_trichotomy tm tp with h | h | h
    · exact h
    · rw [h] at hm2; linarith
    · have := re_avgDiskAut_strictAnti hu hσ hp1 hm1 h
      linarith
  have hsub : Set.Icc tm tp ⊆ Set.Ioo (-1:ℝ) 1 := by
    intro x hx
    have h1 := (abs_lt.1 hm1).1
    have h2 := (abs_lt.1 hp1).2
    exact ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h2⟩
  have hcont : ContinuousOn (fun t : ℝ => (avgDiskAut u σ (t : ℂ)).re) (Set.Icc tm tp) := by
    intro x hx
    have hx1 : |x| < 1 := abs_lt.2 ⟨(hsub hx).1, (hsub hx).2⟩
    exact ((Complex.continuous_re.continuousAt).comp
      (continuousAt_avgDiskAut huc hu1 hσ hx1)).continuousWithinAt
  have hmem : (0:ℝ) ∈ Set.Icc ((fun t : ℝ => (avgDiskAut u σ (t : ℂ)).re) tp)
      ((fun t : ℝ => (avgDiskAut u σ (t : ℂ)).re) tm) := ⟨hp2.le, hm2.le⟩
  obtain ⟨t, htmem, hteq⟩ := intermediate_value_Icc' hlt.le hcont hmem
  have ht1 : |t| < 1 := abs_lt.2 ⟨(hsub htmem).1, (hsub htmem).2⟩
  have hteq' : (avgDiskAut u σ (t : ℂ)).re = 0 := hteq
  refine ⟨t, ⟨ht1, hteq'⟩, ?_⟩
  rintro s ⟨hs1, hs2⟩
  rcases lt_trichotomy s t with h | h | h
  · have := re_avgDiskAut_strictAnti hu hσ hs1 ht1 h
    rw [hs2, hteq'] at this
    exact absurd this (lt_irrefl 0)
  · exact h
  · have := re_avgDiskAut_strictAnti hu hσ ht1 hs1 h
    rw [hs2, hteq'] at this
    exact absurd this (lt_irrefl 0)

theorem continuous_avgDiskAut_rotFam {u : ℝ → ℂ} (huc : Continuous u) (hu1 : ∀ θ, ‖u θ‖ = 1)
    {ρ : ℝ → ℝ} (hρc : Continuous ρ) {t : ℝ} (ht : |t| < 1) :
    Continuous fun α : ℝ => avgDiskAut (rotFam u α) ρ (t : ℂ) := by
  have hnt : ‖((t : ℝ) : ℂ)‖ < 1 := by simpa using ht
  have hE : Continuous fun p : ℝ × ℝ => star ((Circle.exp p.1 : Circle) : ℂ) * u p.2 := by
    refine Continuous.mul ?_ (huc.comp continuous_snd)
    exact continuous_star.comp
      ((by fun_prop : Continuous fun α : ℝ => ((Circle.exp α : Circle) : ℂ)).comp continuous_fst)
  have hden : ∀ p : ℝ × ℝ,
      (1:ℂ) - star ((t : ℝ) : ℂ) * (star ((Circle.exp p.1 : Circle) : ℂ) * u p.2) ≠ 0 := by
    intro p
    refine diskAut_denom_ne_zero _ _ hnt (le_of_eq ?_)
    rw [norm_mul, norm_star, Circle.norm_coe, one_mul]
    exact hu1 p.2
  simp only [avgDiskAut, rotFam]
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun α θ => diskAut ((t : ℝ) : ℂ) (star ((Circle.exp α : Circle) : ℂ) * u θ)
      * ((ρ θ : ℝ) : ℂ)) ?_ 0 (2 * Real.pi)
  have h1 : Continuous fun p : ℝ × ℝ =>
      diskAut ((t : ℝ) : ℂ) (star ((Circle.exp p.1 : Circle) : ℂ) * u p.2) := by
    simp only [diskAut]
    exact Continuous.div (hE.sub continuous_const)
      (continuous_const.sub (continuous_const.mul hE)) hden
  exact h1.mul (Complex.continuous_ofReal.comp (hρc.comp continuous_snd))

/-- Joint continuity of `(α, t) ↦ ⨍ g_t dμ_α` at every point with `|t| < 1`:
continuity in `α` is a parametric-integral statement, and continuity in `t` is
uniform in `α` by the Lipschitz bound `norm_avgDiskAut_sub_le`. -/
theorem continuousAt_avgDiskAut_pair {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {ρ : ℝ → ℝ} (hρ : IsProbabilityDensity ρ) {p₀ : ℝ × ℝ} (h₀ : |p₀.2| < 1) :
    ContinuousAt (fun p : ℝ × ℝ => avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ)) p₀ := by
  have huc := hu.1
  have hu1 := hu.2.1
  obtain ⟨α₀, t₀⟩ := p₀
  simp only at h₀ ⊢
  have hab0 := abs_nonneg t₀
  set c : ℝ := (1 + |t₀|) / 2 with hcdef
  have hc1 : |t₀| < c := by rw [hcdef]; linarith
  have hc2 : c < 1 := by rw [hcdef]; linarith
  set K : ℝ := 2 / ((1 - c) * (1 - |t₀|)) with hKdef
  have hd1 : (0:ℝ) < (1 - c) * (1 - |t₀|) := mul_pos (by linarith) (by linarith)
  have hK : 0 < K := by rw [hKdef]; positivity
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hAcont : Continuous fun α : ℝ => avgDiskAut (rotFam u α) ρ ((t₀ : ℝ) : ℂ) :=
    continuous_avgDiskAut_rotFam huc hu1 hρ.1 h₀
  obtain ⟨δ₁, hδ₁, hδ₁spec⟩ :=
    Metric.continuousAt_iff.1 (hAcont.continuousAt (x := α₀)) (ε / 2) (by linarith)
  refine ⟨min δ₁ (min (c - |t₀|) (ε / (2 * K))), lt_min hδ₁ (lt_min (by linarith) (by positivity)),
    ?_⟩
  intro p hp
  have hp1 : dist p.1 α₀ < δ₁ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_of_eq (Prod.dist_eq (x := p) (y := (α₀, t₀))).symm))
      (lt_of_lt_of_le hp (min_le_left _ _))
  have hp2' : dist p.2 t₀ < min (c - |t₀|) (ε / (2 * K)) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_of_eq (Prod.dist_eq (x := p) (y := (α₀, t₀))).symm))
      (lt_of_lt_of_le hp (min_le_right _ _))
  rw [Real.dist_eq] at hp2'
  have hA : |p.2 - t₀| < c - |t₀| := lt_of_lt_of_le hp2' (min_le_left _ _)
  have hB : |p.2 - t₀| < ε / (2 * K) := lt_of_lt_of_le hp2' (min_le_right _ _)
  have habp : |p.2| < c := by
    have := abs_sub_abs_le_abs_sub p.2 t₀
    linarith
  have hrot := isBoundaryFamily_rotFam hu p.1
  have hlip := norm_avgDiskAut_sub_le hrot.1 hrot.2.1 hρ
    (s := t₀) (t := p.2) h₀ (lt_trans habp hc2)
  have hd2 : (1 - c) * (1 - |t₀|) ≤ (1 - |p.2|) * (1 - |t₀|) := by nlinarith
  have hstep1 : ‖avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ)
      - avgDiskAut (rotFam u p.1) ρ ((t₀ : ℝ) : ℂ)‖ < ε / 2 := by
    calc ‖avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ)
          - avgDiskAut (rotFam u p.1) ρ ((t₀ : ℝ) : ℂ)‖
        ≤ |p.2 - t₀| * 2 / ((1 - |p.2|) * (1 - |t₀|)) := hlip
      _ ≤ |p.2 - t₀| * 2 / ((1 - c) * (1 - |t₀|)) := by gcongr
      _ = K * |p.2 - t₀| := by rw [hKdef]; ring
      _ < K * (ε / (2 * K)) := mul_lt_mul_of_pos_left hB hK
      _ = ε / 2 := by field_simp
  have hstep2 : ‖avgDiskAut (rotFam u p.1) ρ ((t₀ : ℝ) : ℂ)
      - avgDiskAut (rotFam u α₀) ρ ((t₀ : ℝ) : ℂ)‖ < ε / 2 := by
    have := hδ₁spec hp1
    rwa [dist_eq_norm] at this
  calc dist (avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ))
        (avgDiskAut (rotFam u α₀) ρ ((t₀ : ℝ) : ℂ))
      = ‖(avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ)
          - avgDiskAut (rotFam u p.1) ρ ((t₀ : ℝ) : ℂ))
        + (avgDiskAut (rotFam u p.1) ρ ((t₀ : ℝ) : ℂ)
          - avgDiskAut (rotFam u α₀) ρ ((t₀ : ℝ) : ℂ))‖ := by
        rw [dist_eq_norm]; ring_nf
    _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hstep1 hstep2
    _ = ε := by ring

/-- **Existence in Proposition 1**, for an arbitrary boundary family.  Along
each diameter the real part of `⨍ g_t dμ` decreases strictly from `+1` to `-1`,
so it has a unique zero `T(α)`, depending continuously on the direction `α`;
the remaining imaginary part `Q(α)` satisfies `Q(α + π) = -Q(α)`, so it
vanishes somewhere by the intermediate value theorem. -/
theorem exists_avgDiskAut_zero {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {ρ : ℝ → ℝ} (hρ : IsProbabilityDensity ρ) :
    ∃ w : ℂ, ‖w‖ < 1 ∧ avgDiskAut u ρ w = 0 := by
  have huc := hu.1
  have hu1 := hu.2.1
  have hex : ∀ α : ℝ, ∃ t : ℝ, |t| < 1 ∧ (avgDiskAut (rotFam u α) ρ (t : ℂ)).re = 0 :=
    fun α => (existsUnique_re_avgDiskAut_zero (isBoundaryFamily_rotFam hu α) hρ).exists
  choose T hT using hex
  have hTuniq : ∀ (α t : ℝ), |t| < 1 →
      (avgDiskAut (rotFam u α) ρ (t : ℂ)).re = 0 → t = T α := by
    intro α t h1 h2
    obtain ⟨s, -, hsu⟩ := existsUnique_re_avgDiskAut_zero (isBoundaryFamily_rotFam hu α) hρ
    rw [hsu t ⟨h1, h2⟩, hsu (T α) ⟨(hT α).1, (hT α).2⟩]
  have hTcont : Continuous T := by
    rw [continuous_iff_continuousAt]
    intro α₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have ht₀ : |T α₀| < 1 := (hT α₀).1
    have hab0 := abs_nonneg (T α₀)
    set ε' : ℝ := min ε ((1 - |T α₀|) / 2) with hε'def
    have hε'0 : 0 < ε' := lt_min hε (by linarith)
    have hεle : ε' ≤ ε := min_le_left _ _
    have hε'2 : ε' ≤ (1 - |T α₀|) / 2 := min_le_right _ _
    have haabs : |T α₀ - ε'| < 1 := by
      rw [abs_lt]
      exact ⟨by nlinarith [neg_abs_le (T α₀)], by nlinarith [le_abs_self (T α₀)]⟩
    have hbabs : |T α₀ + ε'| < 1 := by
      rw [abs_lt]
      exact ⟨by nlinarith [neg_abs_le (T α₀)], by nlinarith [le_abs_self (T α₀)]⟩
    have hApos : 0 < (avgDiskAut (rotFam u α₀) ρ ((T α₀ - ε' : ℝ) : ℂ)).re := by
      have hs := re_avgDiskAut_strictAnti (isBoundaryFamily_rotFam hu α₀) hρ
        haabs ht₀ (by linarith)
      rw [(hT α₀).2] at hs
      exact hs
    have hBneg : (avgDiskAut (rotFam u α₀) ρ ((T α₀ + ε' : ℝ) : ℂ)).re < 0 := by
      have hs := re_avgDiskAut_strictAnti (isBoundaryFamily_rotFam hu α₀) hρ
        ht₀ hbabs (by linarith)
      rw [(hT α₀).2] at hs
      exact hs
    have hevA : ∀ᶠ α in 𝓝 α₀, 0 < (avgDiskAut (rotFam u α) ρ ((T α₀ - ε' : ℝ) : ℂ)).re :=
      (Complex.continuous_re.comp
        (continuous_avgDiskAut_rotFam huc hu1 hρ.1 haabs)).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds hApos)
    have hevB : ∀ᶠ α in 𝓝 α₀, (avgDiskAut (rotFam u α) ρ ((T α₀ + ε' : ℝ) : ℂ)).re < 0 :=
      (Complex.continuous_re.comp
        (continuous_avgDiskAut_rotFam huc hu1 hρ.1 hbabs)).continuousAt.preimage_mem_nhds
          (Iio_mem_nhds hBneg)
    obtain ⟨δ, hδ, hδspec⟩ := Metric.eventually_nhds_iff.1 (hevA.and hevB)
    refine ⟨δ, hδ, ?_⟩
    intro α hα
    obtain ⟨hA, hB⟩ := hδspec hα
    have hgt : T α₀ - ε' < T α := by
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with h | h
      · rw [← h, (hT α).2] at hA; exact lt_irrefl 0 hA
      · have hs := re_avgDiskAut_strictAnti (isBoundaryFamily_rotFam hu α) hρ
          (hT α).1 haabs h
        rw [(hT α).2] at hs
        linarith
    have hlt2 : T α < T α₀ + ε' := by
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with h | h
      · rw [h, (hT α).2] at hB; exact lt_irrefl 0 hB
      · have hs := re_avgDiskAut_strictAnti (isBoundaryFamily_rotFam hu α) hρ
          hbabs (hT α).1 h
        rw [(hT α).2] at hs
        linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  set Q : ℝ → ℝ := fun α => (avgDiskAut (rotFam u α) ρ ((T α : ℝ) : ℂ)).im with hQdef
  have hQcont : Continuous Q := by
    have hmap : Continuous fun α : ℝ => ((α, T α) : ℝ × ℝ) := continuous_id.prodMk hTcont
    have hon : ContinuousOn (fun p : ℝ × ℝ => avgDiskAut (rotFam u p.1) ρ ((p.2 : ℝ) : ℂ))
        {p : ℝ × ℝ | |p.2| < 1} :=
      fun p hp => (continuousAt_avgDiskAut_pair hu hρ hp).continuousWithinAt
    have hpair := hon.comp_continuous hmap (fun α => (hT α).1)
    rw [hQdef]
    exact Complex.continuous_im.comp hpair
  have hTanti : ∀ α : ℝ, T (α + Real.pi) = - T α := by
    intro α
    refine (hTuniq (α + Real.pi) (-(T α)) (by rw [abs_neg]; exact (hT α).1) ?_).symm
    have h := avgDiskAut_rot_antipode u ρ (-(T α)) α
    push_cast at h ⊢
    rw [h, neg_neg, Complex.neg_re]
    rw [show ((T α : ℝ) : ℂ) = ((T α : ℝ) : ℂ) from rfl]
    rw [(hT α).2, neg_zero]
  have hQanti : ∀ α : ℝ, Q (α + Real.pi) = - Q α := by
    intro α
    rw [hQdef]
    simp only
    rw [hTanti α]
    have h := avgDiskAut_rot_antipode u ρ (-(T α)) α
    push_cast at h ⊢
    rw [h, neg_neg, Complex.neg_im]
  have hQ0 : Q Real.pi = - Q 0 := by
    have h := hQanti 0
    rwa [zero_add] at h
  obtain ⟨αs, -, hαs⟩ : ∃ α ∈ Set.Icc (0:ℝ) Real.pi, Q α = 0 := by
    rcases le_or_gt (Q 0) 0 with h | h
    · have h2 : 0 ≤ Q Real.pi := by rw [hQ0]; linarith
      obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Icc Real.pi_pos.le hQcont.continuousOn ⟨h, h2⟩
      exact ⟨x, hx, hxv⟩
    · have h2 : Q Real.pi ≤ 0 := by rw [hQ0]; linarith
      obtain ⟨x, hx, hxv⟩ :=
        intermediate_value_Icc' Real.pi_pos.le hQcont.continuousOn ⟨h2, h.le⟩
      exact ⟨x, hx, hxv⟩
  have hαs' : (avgDiskAut (rotFam u αs) ρ ((T αs : ℝ) : ℂ)).im = 0 := hαs
  refine ⟨((T αs : ℝ) : ℂ) * ((Circle.exp αs : Circle) : ℂ), ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    exact (hT αs).1
  · rw [avgDiskAut_rot u ρ (T αs) αs]
    have hzero : avgDiskAut (rotFam u αs) ρ ((T αs : ℝ) : ℂ) = 0 := by
      refine Complex.ext ?_ ?_
      · simpa using (hT αs).2
      · simpa using hαs'
    rw [hzero, mul_zero]

end Proposition1

/-- **Proposition 1 for a boundary family**: for a continuous unit-modulus
`u` injective on `(0, 2π)` and a probability density `ρ`, the average
`w ↦ ⨍ g_w(u θ) ρ(θ) dθ/2π` has exactly one zero in `D`. -/
theorem avgDiskAut_zero_existsUnique {u : ℝ → ℂ} (hu : IsBoundaryFamily u)
    {ρ : ℝ → ℝ} (hρ : IsProbabilityDensity ρ) :
    ∃! w : ℂ, ‖w‖ < 1 ∧ avgDiskAut u ρ w = 0 := by
  obtain ⟨w, hw, hz⟩ := exists_avgDiskAut_zero hu hρ
  refine ⟨w, ⟨hw, hz⟩, ?_⟩
  rintro y ⟨hy, hyz⟩
  exact avgDiskAut_zero_unique hu hρ hy hw hyz hz

/-- The standard boundary family `θ ↦ e^{iθ}`. -/
theorem isBoundaryFamily_circleExp :
    IsBoundaryFamily (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) :=
  ⟨by fun_prop, fun θ => Circle.norm_coe _, fun _ _ h h' heq => circle_exp_inj_on h h' heq⟩

/-- **Proposition 1 and Definition**: if `ρ` is a probability density on `S¹`,
the vector field `ξ_ρ` has a unique zero in `D`.

This is `avgDiskAut_zero_existsUnique` for the standard boundary family
`θ ↦ e^{iθ}`; see the section header above for the shape of both arguments. -/
theorem conformal_barycenter_existsUnique (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    ∃! w : ℂ, ‖w‖ < 1 ∧ xiField ρ w = 0 := by
  obtain ⟨w, ⟨hw, hz⟩, huniq⟩ := avgDiskAut_zero_existsUnique isBoundaryFamily_circleExp hρ
  refine ⟨w, ⟨hw, (xiField_eq_zero_iff ρ hw).2 hz⟩, ?_⟩
  rintro y ⟨hy, hyz⟩
  exact huniq y ⟨hy, (xiField_eq_zero_iff ρ hy).1 hyz⟩

/-- Auxiliary conditional existence, in the style of a Classical-choice
extension operator: there is a point `w` which, whenever `ρ` is a genuine
probability density, is the (unique) zero of `ξ_ρ` in `D`. -/
private theorem conformalBarycenter_aux (ρ : ℝ → ℝ) :
    ∃ w : ℂ, IsProbabilityDensity ρ → (‖w‖ < 1 ∧ xiField ρ w = 0) := by
  by_cases hρ : IsProbabilityDensity ρ
  · obtain ⟨w, hw⟩ := (conformal_barycenter_existsUnique ρ hρ).exists
    exact ⟨w, fun _ => hw⟩
  · exact ⟨0, fun h' => absurd h' hρ⟩

/-- The conformal barycenter `B(μ)` of the probability density `ρ`: the
unique zero of `ξ_ρ` in `D` (junk-valued if `ρ` is not a genuine probability
density). -/
def conformalBarycenter (ρ : ℝ → ℝ) : ℂ := Classical.choose (conformalBarycenter_aux ρ)

theorem conformalBarycenter_mem_disk (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    ‖conformalBarycenter ρ‖ < 1 :=
  (Classical.choose_spec (conformalBarycenter_aux ρ) hρ).1

theorem conformalBarycenter_isZero (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    xiField ρ (conformalBarycenter ρ) = 0 :=
  (Classical.choose_spec (conformalBarycenter_aux ρ) hρ).2

/-- `B(μ) = 0` iff `μ` has mean value zero, formula (2.1).

Both directions are immediate from `xiField_zero` — the normalization (2.2),
`ξ_μ(0) = ∫ ζ dμ` — together with the defining property of `B(μ)`: forwards
because `B(μ) = 0` makes `ξ_μ(0) = 0`, backwards because a vanishing mean makes
`0` a zero of `ξ_μ` in `D`, which is `B(μ)` by the uniqueness half of
Proposition 1. -/
theorem conformalBarycenter_eq_zero_iff (ρ : ℝ → ℝ) (hρ : IsProbabilityDensity ρ) :
    conformalBarycenter ρ = 0 ↔
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (Circle.exp θ : ℂ) * (ρ θ : ℂ) = 0 := by
  constructor
  · intro h
    have hz := conformalBarycenter_isZero ρ hρ
    rw [h] at hz
    exact (xiField_zero ρ).symm.trans hz
  · intro h
    obtain ⟨w, -, huniq⟩ := conformal_barycenter_existsUnique ρ hρ
    have h0 : ‖(0:ℂ)‖ < 1 ∧ xiField ρ 0 = 0 := ⟨by norm_num, (xiField_zero ρ).trans h⟩
    have hB : ‖conformalBarycenter ρ‖ < 1 ∧ xiField ρ (conformalBarycenter ρ) = 0 :=
      ⟨conformalBarycenter_mem_disk ρ hρ, conformalBarycenter_isZero ρ hρ⟩
    exact (huniq _ hB).trans (huniq _ h0).symm

end
