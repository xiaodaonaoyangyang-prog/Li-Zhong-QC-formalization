import LiZhongQC.Lemmas.ExpStripBasic
import LiZhongQC.Lemmas.StripAutomorphism
import LiZhongQC.Lemmas.AnnulusDescent

/-!
# The deck-transformation pivot: `exists_periodic_of_conformal` (Theorem 2.1 case (iii))
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The deck transformation `z ↦ z + 2πi` of `expStrip A`. -/
def deckT (z : ℂ) : ℂ := z + 2 * (Real.pi : ℂ) * I

/-- Its inverse `z ↦ z - 2πi`. -/
def deckTinv (z : ℂ) : ℂ := z - 2 * (Real.pi : ℂ) * I

theorem re_two_pi_mul_I : (2 * (Real.pi : ℂ) * I).re = 0 := by simp [Complex.mul_re]

theorem exp_add_two_pi (z : ℂ) : Complex.exp (z + 2 * (Real.pi : ℂ) * I) = Complex.exp z :=
  Complex.exp_periodic z

theorem exp_sub_two_pi (z : ℂ) : Complex.exp (z - 2 * (Real.pi : ℂ) * I) = Complex.exp z := by
  have h := Complex.exp_periodic (z - 2 * (Real.pi : ℂ) * I)
  rw [show z - 2 * (Real.pi : ℂ) * I + 2 * (Real.pi : ℂ) * I = z by ring] at h
  exact h.symm

theorem deckT_mem_expStrip {A : Set ℂ} {z : ℂ} (hz : z ∈ expStrip A) : deckT z ∈ expStrip A := by
  refine ⟨?_, ?_⟩
  · show 0 < (z + 2 * (Real.pi : ℂ) * I).re
    rw [Complex.add_re, re_two_pi_mul_I, add_zero]
    exact hz.1
  · show Complex.exp (z + 2 * (Real.pi : ℂ) * I) ∈ A
    rw [exp_add_two_pi]
    exact hz.2

theorem deckTinv_mem_expStrip {A : Set ℂ} {z : ℂ} (hz : z ∈ expStrip A) :
    deckTinv z ∈ expStrip A := by
  refine ⟨?_, ?_⟩
  · show 0 < (z - 2 * (Real.pi : ℂ) * I).re
    rw [Complex.sub_re, re_two_pi_mul_I, sub_zero]
    exact hz.1
  · show Complex.exp (z - 2 * (Real.pi : ℂ) * I) ∈ A
    rw [exp_sub_two_pi]
    exact hz.2

theorem isConformalOnto_deckT (A : Set ℂ) : IsConformalOnto deckT (expStrip A) (expStrip A) := by
  refine stripAux_isConformalOnto_of_leftInverse (g := deckTinv) ?_ ?_ ?_ ?_ ?_
  · intro z _
    have : DifferentiableAt ℂ deckT z := by unfold deckT; fun_prop
    exact this.differentiableWithinAt
  · exact fun z hz => deckT_mem_expStrip hz
  · exact fun z hz => deckTinv_mem_expStrip hz
  · intro z _
    show z - 2 * (Real.pi : ℂ) * I + 2 * (Real.pi : ℂ) * I = z
    ring
  · intro z _
    show z + 2 * (Real.pi : ℂ) * I - 2 * (Real.pi : ℂ) * I = z
    ring

/-! ## Part 5: `deckH := g ∘ deckT ∘ g⁻¹`, an automorphism of `strip d`, fixed-point-free -/

theorem mem_image_of_mem_strip {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ}
    (hg : IsConformalOnto g (expStrip A) (strip d)) {w : ℂ} (hw : w ∈ strip d) :
    w ∈ g '' expStrip A := by rw [hg.2.2]; exact hw

theorem gInv_right {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hg : IsConformalOnto g (expStrip A) (strip d))
    {w : ℂ} (hw : w ∈ strip d) : g (Function.invFunOn g (expStrip A) w) = w :=
  Function.invFunOn_eq (mem_image_of_mem_strip hg hw)

theorem gInv_mem {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hg : IsConformalOnto g (expStrip A) (strip d))
    {w : ℂ} (hw : w ∈ strip d) : Function.invFunOn g (expStrip A) w ∈ expStrip A :=
  Function.invFunOn_mem (mem_image_of_mem_strip hg hw)

theorem isConformalOnto_gInv {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    IsConformalOnto (Function.invFunOn g (expStrip A)) (strip d) (expStrip A) :=
  hg.symm (isOpen_expStrip hAo)

/-- The deck-induced automorphism of `strip d`. -/
def deckH (A : Set ℂ) (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  g (deckT (Function.invFunOn g (expStrip A) w))

theorem isConformalOnto_deckH {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    IsConformalOnto (deckH A g) (strip d) (strip d) :=
  hg.comp ((isConformalOnto_deckT A).comp (isConformalOnto_gInv hAo hg))

theorem two_pi_mul_I_ne_zero : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

theorem deckH_ne_self {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {w : ℂ} (hw : w ∈ strip d) :
    deckH A g w ≠ w := by
  intro heq
  have hgw : g (Function.invFunOn g (expStrip A) w) = w := gInv_right hg hw
  have hmem : Function.invFunOn g (expStrip A) w ∈ expStrip A := gInv_mem hg hw
  have hTmem : deckT (Function.invFunOn g (expStrip A) w) ∈ expStrip A :=
    deckT_mem_expStrip hmem
  have heq2 : g (deckT (Function.invFunOn g (expStrip A) w))
      = g (Function.invFunOn g (expStrip A) w) := by
    show deckH A g w = g (Function.invFunOn g (expStrip A) w)
    rw [heq, hgw]
  have hfix := hg.2.1 hTmem hmem heq2
  apply two_pi_mul_I_ne_zero
  have : Function.invFunOn g (expStrip A) w + 2 * (Real.pi : ℂ) * I
      = Function.invFunOn g (expStrip A) w := hfix
  linear_combination this

/-! ## Part 6: transport `deckH` to the disc, Blaschke-classify it, and put its two fixed points
on the unit circle via a self-inversive polynomial identity -/

def deckH_disc (A : Set ℂ) (d : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  stripDisc d (deckH A g (stripDiscInv d z))

theorem isConformalOnto_deckH_disc {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    IsConformalOnto (deckH_disc A d g) unitDisc unitDisc :=
  (isConformalOnto_stripDisc hd).comp ((isConformalOnto_deckH hAo hg).comp
    (isConformalOnto_stripDiscInv hd))

theorem deckH_disc_ne_self {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {z : ℂ} (hz : z ∈ unitDisc) :
    deckH_disc A d g z ≠ z := by
  intro heq
  have hmem : stripDiscInv d z ∈ strip d := (isConformalOnto_stripDiscInv hd).mapsTo hz
  have hTmem : deckH A g (stripDiscInv d z) ∈ strip d :=
    (isConformalOnto_deckH hAo hg).mapsTo hmem
  have h1 : stripDisc d (deckH A g (stripDiscInv d z)) = z := heq
  have h2 : deckH A g (stripDiscInv d z) = stripDiscInv d z := by
    have hc := congrArg (stripDiscInv d) h1
    rwa [stripDiscInv_stripDisc hd hTmem] at hc
  exact deckH_ne_self hAo hg hmem h2

/-- The Blaschke coefficients of `deckH_disc`. -/
theorem exists_blaschke_deckH_disc {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧ EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc :=
  exists_rotation_blaschke_of_isConformalOnto_unitDisc (isConformalOnto_deckH_disc hd hAo hg)

/-- The polynomial (cleared of the `blaschke` denominator) whose roots are `deckH_disc`'s fixed
points on `closedBall 0 1`. -/
def fixedPointPoly (c a : ℂ) (z : ℂ) : ℂ := conj a * z ^ 2 + (c - 1) * z - c * a

theorem deckH_disc_eq_self_iff_fixedPointPoly {c a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    c * blaschke a z = z ↔ fixedPointPoly c a z = 0 := by
  have hden : (1 : ℂ) - conj a * z ≠ 0 := by
    intro hcon
    have h1 : conj a * z = 1 := by linear_combination -hcon
    have h2 : ‖conj a * z‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_conj] at h2
    have h3 : ‖a‖ * ‖z‖ < 1 := by
      calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
        _ = ‖a‖ := by ring
        _ < 1 := ha
    linarith
  rw [blaschke, show c * ((z - a) / (1 - conj a * z)) = (c * (z - a)) / (1 - conj a * z) from by
    ring, div_eq_iff hden, fixedPointPoly]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Self-inversive identity: if `p` is a root, so is `1/conj p`. -/
theorem fixedPointPoly_inv_conj {c a : ℂ} (hc : ‖c‖ = 1) {p : ℂ} (hp0 : p ≠ 0)
    (hp : fixedPointPoly c a p = 0) : fixedPointPoly c a (1 / conj p) = 0 := by
  have hpc0 : conj p ≠ 0 := fun h => hp0 (by simpa using congrArg conj h)
  have hcc : c * conj c = 1 := by
    have h1 : Complex.normSq c = 1 := by
      rw [← Complex.sq_norm, hc]; norm_num
    have h2 := Complex.mul_conj c
    rw [h1] at h2
    simpa using h2
  have key : (conj p) ^ 2 * fixedPointPoly c a (1 / conj p)
      = -c * conj (fixedPointPoly c a p) := by
    simp only [fixedPointPoly, map_add, map_sub, map_mul, map_pow, map_one, Complex.conj_conj]
    field_simp
    linear_combination (-conj a + conj p) * hcc
  rw [hp, map_zero, mul_zero] at key
  have h0 : (conj p) ^ 2 * fixedPointPoly c a (1 / conj p) = 0 := key
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1) hpc0
  · exact h1

theorem a_ne_zero_of_deckH_disc {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ}
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc) : a ≠ 0 := by
  intro ha0
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have h1 : deckH_disc A d g 0 = c * blaschke a 0 := heqOn h0mem
  rw [ha0] at h1
  simp only [blaschke, sub_zero, map_zero, zero_div, mul_zero] at h1
  exact deckH_disc_ne_self hd hAo hg h0mem h1

theorem norm_eq_one_of_fixedPointPoly_eq_zero {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d)
    (hAo : IsOpen A) (hg : IsConformalOnto g (expStrip A) (strip d)) {c a p : ℂ} (hc : ‖c‖ = 1)
    (ha : ‖a‖ < 1) (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (hp0 : p ≠ 0) (hp : fixedPointPoly c a p = 0) : ‖p‖ = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : p ∈ unitDisc := mem_ball_zero_iff.mpr hlt
    have h1 : c * blaschke a p = p := (deckH_disc_eq_self_iff_fixedPointPoly ha hlt.le).mpr hp
    exact deckH_disc_ne_self hd hAo hg hmem (by rw [heqOn hmem]; exact h1)
  · set q := 1 / conj p with hqdef
    have hqp : fixedPointPoly c a q = 0 := fixedPointPoly_inv_conj hc hp0 hp
    have hpnorm_pos : (0 : ℝ) < ‖p‖ := lt_trans one_pos hgt
    have hqnorm : ‖q‖ < 1 := by
      rw [hqdef, norm_div, Complex.norm_conj, norm_one, div_lt_one hpnorm_pos]
      exact hgt
    have hqmem : q ∈ unitDisc := mem_ball_zero_iff.mpr hqnorm
    have h1 : c * blaschke a q = q := (deckH_disc_eq_self_iff_fixedPointPoly ha hqnorm.le).mpr hqp
    exact deckH_disc_ne_self hd hAo hg hqmem (by rw [heqOn hqmem]; exact h1)

theorem discriminant_eq {c a p : ℂ} (ha0 : a ≠ 0)
    (hp : fixedPointPoly c a p = 0) : (2 * conj a * p + (c - 1)) ^ 2
      = (c - 1) ^ 2 + 4 * conj a * c * a := by
  have hane : conj a ≠ 0 := fun h => ha0 (by simpa using congrArg conj h)
  have h4 : conj a * fixedPointPoly c a p = 0 := by rw [hp, mul_zero]
  rw [fixedPointPoly] at h4
  linear_combination 4 * h4

theorem exists_fixedPointPoly_root {c a : ℂ} (ha0 : a ≠ 0) :
    ∃ p : ℂ, fixedPointPoly c a p = 0 := by
  have hane : conj a ≠ 0 := fun h => ha0 (by simpa using congrArg conj h)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((c - 1) ^ 2 + 4 * conj a * c * a)
  refine ⟨(-(c - 1) + s) / (2 * conj a), ?_⟩
  rw [fixedPointPoly]
  have h2ane : (2 : ℂ) * conj a ≠ 0 := mul_ne_zero two_ne_zero hane
  field_simp
  linear_combination -hs

/-- The other root, via Vieta's sum. -/
theorem other_root_eq_zero {c a p : ℂ} (ha0 : a ≠ 0) (hp : fixedPointPoly c a p = 0) :
    fixedPointPoly c a ((1 - c) / conj a - p) = 0 := by
  have hane : conj a ≠ 0 := fun h => ha0 (by simpa using congrArg conj h)
  rw [fixedPointPoly] at hp ⊢
  field_simp
  linear_combination conj a * hp

/-- On the unit circle away from `1`, `stripCayleyInv` is real. -/
theorem conj_stripCayleyInv_eq {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    conj (stripCayleyInv w) = stripCayleyInv w := by
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hww : w * conj w = 1 := by
    have h1 : Complex.normSq w = 1 := by rw [← Complex.sq_norm, hw]; norm_num
    have h2 := Complex.mul_conj w
    rw [h1] at h2
    simpa using h2
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hcw1 : conj w ≠ 1 := fun h => hw1 (by simpa using congrArg conj h)
  have hdenc : (1 : ℂ) - conj w ≠ 0 := sub_ne_zero.mpr (Ne.symm hcw1)
  rw [stripCayleyInv]
  simp only [map_div₀, map_mul, Complex.conj_I, map_add, map_one, map_sub]
  rw [div_eq_div_iff hdenc hden]
  have hcwne : conj w ≠ 0 := fun h => hwne (by simpa using congrArg conj h)
  field_simp
  linear_combination 2 * hww

/-! ## Part 9: boundary round-trip facts for `stripCayley`/`stripCayleyInv` (valid at any `w ≠ 1`,
not just inside the disc) -/

theorem stripCayley_cayleyInv_of_ne_one {w : ℂ} (hw : w ≠ 1) :
    stripCayley (stripCayleyInv w) = w := by
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h1 : stripCayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [stripCayleyInv]; field_simp; ring
  have h2 : stripCayleyInv w + I = I * 2 / (1 - w) := by
    rw [stripCayleyInv]; field_simp; ring
  have h2ne : stripCayleyInv w + I ≠ 0 := by
    rw [h2]; exact div_ne_zero (by simp) hden
  rw [stripCayley, div_eq_iff h2ne, h1, h2]
  field_simp

theorem continuousAt_stripCayleyInv_of_ne_one {w : ℂ} (hw : w ≠ 1) :
    ContinuousAt stripCayleyInv w := by
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h1 : ContinuousAt (fun v : ℂ => I * (1 + v)) w := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => (1 : ℂ) - v) w := by fun_prop
  exact h1.div h2 hden

theorem continuousAt_mobiusFn {a b c d z : ℂ} (hden : c * z + d ≠ 0) :
    ContinuousAt (mobiusFn a b c d) z := by
  have h1 : ContinuousAt (fun v : ℂ => a * v + b) z := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => c * v + d) z := by fun_prop
  exact h1.div h2 hden

theorem continuousAt_stripCayley_real (r : ℝ) : ContinuousAt stripCayley (r : ℂ) := by
  have hden : (r : ℂ) + I ≠ 0 := by
    intro hcon
    have h1 := congrArg Complex.im hcon
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im, zero_add] at h1
    norm_num at h1
  have h1 : ContinuousAt (fun v : ℂ => v - I) (r : ℂ) := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => v + I) (r : ℂ) := by fun_prop
  exact h1.div h2 hden

/-! ## Part 10: the hyperbolic construction, generic case (`P, Q ≠ 1`) -/

theorem real_of_conj_eq {z : ℂ} (h : conj z = z) : ∃ r : ℝ, z = (r : ℂ) := by
  refine ⟨z.re, Complex.ext rfl ?_⟩
  have h2 := congrArg Complex.im h
  simp only [Complex.conj_im] at h2
  simp only [Complex.ofReal_im]
  linarith

theorem hden_ne_of_blaschke {a : ℂ} (ha1 : ‖a‖ < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    (1 : ℂ) - conj a * ζ ≠ 0 := by
  intro hcon
  have h1 : conj a * ζ = 1 := by linear_combination -hcon
  have h2 : ‖conj a * ζ‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_conj] at h2
  have h3 : ‖a‖ * ‖ζ‖ < 1 := by
    calc ‖a‖ * ‖ζ‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hζ (norm_nonneg a)
      _ = ‖a‖ := by ring
      _ < 1 := ha1
  linarith

theorem continuousAt_blaschke_of_le_one {c a : ℂ} (ha1 : ‖a‖ < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    ContinuousAt (fun ζ => c * blaschke a ζ) ζ := by
  have hden := hden_ne_of_blaschke ha1 hζ
  have h1 : ContinuousAt (fun v : ℂ => v - a) ζ := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => (1 : ℂ) - conj a * v) ζ := by fun_prop
  exact continuousAt_const.mul (h1.div h2 hden)

theorem key_construction {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    {P Q : ℂ} (hPn : ‖P‖ = 1) (hQn : ‖Q‖ = 1) (hP1 : P ≠ 1) (hQ1 : Q ≠ 1)
    (hPfix : c * blaschke a P = P) (hQfix : c * blaschke a Q = Q)
    {p' q' : ℝ} (hp'eq : stripCayleyInv P = (p' : ℂ)) (hq'eq : stripCayleyInv Q = (q' : ℂ))
    (hgt : q' < p') :
    ∃ (g' : ℂ → ℂ) (s : ℝ), IsConformalOnto g' (expStrip A) (strip d) ∧ 0 < s ∧
      ∀ z ∈ expStrip A, g' (z + 2 * (Real.pi : ℂ) * I) = g' z + (s : ℂ) * I := by
  set φ : ℂ → ℂ := mobiusFn 1 (-(p' : ℂ)) 1 (-(q' : ℂ)) with hφdef
  set φInv : ℂ → ℂ := mobiusFn (-(q' : ℂ)) (p' : ℂ) (-1) 1 with hφInvdef
  have hdet : (1 : ℝ) * (-q') - (-p') * 1 = p' - q' := by ring
  have hdetpos : (0 : ℝ) < 1 * (-q') - (-p') * 1 := by rw [hdet]; linarith
  have hφconf : IsConformalOnto φ upperHalf upperHalf := by
    have := isConformalOnto_mobius_upperHalf (a := (1 : ℝ)) (b := -p') (c := (1 : ℝ)) (d := -q')
      (by exact_mod_cast hdetpos)
    convert this using 2 <;> push_cast <;> ring
  have hdetne : (1 : ℂ) * (-(q' : ℂ)) - (-(p' : ℂ)) * 1 ≠ 0 := by
    have hne : (p' : ℝ) - q' ≠ 0 := by linarith
    have hne' : (p' : ℂ) - q' ≠ 0 := by exact_mod_cast hne
    intro hcon
    apply hne'
    linear_combination hcon
  have hφInv_left : ∀ z : ℂ, 1 * z + (-(q' : ℂ)) ≠ 0 → φInv (φ z) = z := by
    intro z hz
    have := mobiusFn_inv_apply (a := (1 : ℂ)) (b := -(p' : ℂ)) (c := (1 : ℂ)) (d := -(q' : ℂ))
      hdetne hz
    simpa [hφdef, hφInvdef] using this
  have hφ0 : φ (p' : ℂ) = 0 := by
    simp only [hφdef, mobiusFn]
    rw [one_mul, div_eq_zero_iff]
    left; ring
  have hφInv0 : φInv 0 = (p' : ℂ) := by
    simp only [hφInvdef, mobiusFn]
    norm_num
  have hφInvconf : IsConformalOnto φInv upperHalf upperHalf := by
    have hdetpos' : (0 : ℝ) < (-q') * 1 - p' * (-1) := by linarith
    have := isConformalOnto_mobius_upperHalf (a := -q') (b := (p' : ℝ)) (c := (-1 : ℝ))
      (d := (1 : ℝ)) (by exact_mod_cast hdetpos')
    convert this using 2 <;> push_cast <;> ring
  have hcbconf : IsConformalOnto (fun z => c * blaschke a z) unitDisc unitDisc := by
    obtain ⟨hdo, hinj, himg⟩ := isConformalOnto_deckH_disc hd hAo hg
    refine ⟨hdo.congr heqOn.symm, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hinj hx hy ((heqOn hx).trans (hxy.trans (heqOn hy).symm))
    · have hstep : (fun z => c * blaschke a z) '' unitDisc = deckH_disc A d g '' unitDisc := by
        apply Set.image_congr
        intro x hx
        exact (heqOn hx).symm
      rw [hstep, himg]
  set ψAssembled : ℂ → ℂ :=
      fun w => φ (stripCayleyInv (c * blaschke a (stripCayley (φInv w)))) with hψdef
  have hψconf : IsConformalOnto ψAssembled upperHalf upperHalf :=
    hφconf.comp (isConformalOnto_stripCayleyInv.comp
      (hcbconf.comp (isConformalOnto_stripCayley.comp hφInvconf)))
  -- continuity chase at `0`
  have hψ0 : Tendsto ψAssembled (𝓝[upperHalf] (0 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto φInv (𝓝[upperHalf] (0 : ℂ)) (𝓝 (p' : ℂ)) := by
      have hc : ContinuousAt φInv (0 : ℂ) := by
        rw [hφInvdef]; exact continuousAt_mobiusFn (by norm_num)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[upperHalf] (0 : ℂ) ≤ 𝓝 0)
      rwa [hφInv0] at this
    have h2 : Tendsto stripCayley (𝓝 (p' : ℂ)) (𝓝 P) := by
      have hcont := (continuousAt_stripCayley_real p').tendsto
      have hval : stripCayley (p' : ℂ) = P := by
        rw [← hp'eq]; exact stripCayley_cayleyInv_of_ne_one hP1
      rwa [hval] at hcont
    have h3 : Tendsto (fun z => c * blaschke a z) (𝓝 P) (𝓝 P) := by
      have := (continuousAt_blaschke_of_le_one (c := c) ha (le_of_eq hPn)).tendsto
      rwa [hPfix] at this
    have h4 : Tendsto stripCayleyInv (𝓝 P) (𝓝 (p' : ℂ)) := by
      have := (continuousAt_stripCayleyInv_of_ne_one hP1).tendsto
      rwa [hp'eq] at this
    have h5 : Tendsto φ (𝓝 (p' : ℂ)) (𝓝 0) := by
      have hne2 : (p' : ℂ) - q' ≠ 0 := by
        have hne : (p' : ℝ) - q' ≠ 0 := by linarith
        exact_mod_cast hne
      have hc : ContinuousAt φ (p' : ℂ) := by
        rw [hφdef]
        apply continuousAt_mobiusFn
        rw [one_mul]
        intro hcon
        exact hne2 (by linear_combination hcon)
      have := hc.tendsto
      rwa [hφ0] at this
    exact h5.comp (h4.comp (h3.comp (h2.comp h1)))
  -- continuity chase at `∞`
  have hψinf : Tendsto (fun w => ‖ψAssembled w‖)
      (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    have h1 : Tendsto φInv (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (𝓝 (q' : ℂ)) := by
      have hcb : Tendsto φInv (cobounded ℂ) (𝓝 (q' : ℂ)) := by
        rw [hφInvdef]
        have := tendsto_mobiusFn_cobounded_of_ne (a := -(q' : ℂ)) (b := (p' : ℂ)) (d := (1 : ℂ))
          (show (-1 : ℂ) ≠ 0 by norm_num)
        simpa using this
      rw [← comap_norm_atTop] at hcb
      exact hcb.mono_left inf_le_left
    have h2 : Tendsto stripCayley (𝓝 (q' : ℂ)) (𝓝 Q) := by
      have hcont := (continuousAt_stripCayley_real q').tendsto
      have hval : stripCayley (q' : ℂ) = Q := by
        rw [← hq'eq]; exact stripCayley_cayleyInv_of_ne_one hQ1
      rwa [hval] at hcont
    have h3 : Tendsto (fun z => c * blaschke a z) (𝓝 Q) (𝓝 Q) := by
      have := (continuousAt_blaschke_of_le_one (c := c) ha (le_of_eq hQn)).tendsto
      rwa [hQfix] at this
    have h4 : Tendsto stripCayleyInv (𝓝 Q) (𝓝 (q' : ℂ)) := by
      have := (continuousAt_stripCayleyInv_of_ne_one hQ1).tendsto
      rwa [hq'eq] at this
    have hplain : Tendsto (stripCayleyInv ∘ (fun z => c * blaschke a z) ∘ stripCayley ∘ φInv)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (𝓝 (q' : ℂ)) :=
      h4.comp (h3.comp (h2.comp h1))
    have hMapsTo : ∀ w ∈ upperHalf,
        stripCayleyInv ((fun z => c * blaschke a z) (stripCayley (φInv w))) ∈ upperHalf := by
      intro w hw
      have hw1 : φInv w ∈ upperHalf := hφInvconf.mapsTo hw
      have hw2 : stripCayley (φInv w) ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw1
      have hw3 : (fun z => c * blaschke a z) (stripCayley (φInv w)) ∈ unitDisc :=
        hcbconf.mapsTo hw2
      exact isConformalOnto_stripCayleyInv.mapsTo hw3
    have hev : ∀ᶠ w in (Filter.comap norm atTop ⊓ 𝓟 upperHalf), w ∈ upperHalf :=
      Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.2 (fun w hw => hw))
    have hne_ev : ∀ᶠ w in (Filter.comap norm atTop ⊓ 𝓟 upperHalf),
        stripCayleyInv ((fun z => c * blaschke a z) (stripCayley (φInv w))) ≠ (q' : ℂ) := by
      filter_upwards [hev] with w hw hcon
      have hmem := hMapsTo w hw
      rw [hcon] at hmem
      have h0 : (0 : ℝ) < ((q' : ℂ)).im := hmem
      simp at h0
    have h4'' : Tendsto (stripCayleyInv ∘ (fun z => c * blaschke a z) ∘ stripCayley ∘ φInv)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (𝓝[≠] (q' : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hplain, hne_ev⟩
    have h5 : Tendsto φ (𝓝[≠] (q' : ℂ)) (cobounded ℂ) := by
      have hne3 : (1 : ℂ) * (q' : ℂ) + (-(q' : ℂ)) = 0 := by ring
      have := tendsto_mobiusFn_pole (a := (1 : ℂ)) (b := -(p' : ℂ)) (c := (1 : ℂ))
        (d := -(q' : ℂ)) hdetne hne3
      rwa [hφdef]
    rw [← tendsto_norm_atTop_iff_cobounded] at h5
    exact h5.comp h4''
  obtain ⟨lam, hlam_pos, hlam⟩ := upperHalf_automorphism_eq_dilate hψconf hψ0 hψinf
  -- `stripToHalf (deckH A g (halfToStrip d w)) = stripCayleyInv (c * blaschke a (stripCayley w))`
  have hSTH : ∀ w ∈ upperHalf,
      stripToHalf d (deckH A g (halfToStrip d w)) = stripCayleyInv (c * blaschke a (stripCayley w)) := by
    intro w hw
    have hcw : stripCayley w ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw
    have h1 : stripDiscInv d (stripCayley w) = halfToStrip d w := by
      rw [stripDiscInv, stripCayleyInv_cayley hw]
    have h2 : deckH_disc A d g (stripCayley w) = stripDisc d (deckH A g (halfToStrip d w)) := by
      rw [deckH_disc, h1]
    have h3 : deckH_disc A d g (stripCayley w) = c * blaschke a (stripCayley w) := heqOn hcw
    have h4 : stripDisc d (deckH A g (halfToStrip d w)) = c * blaschke a (stripCayley w) := by
      rw [← h2, h3]
    have h5 : stripToHalf d (deckH A g (halfToStrip d w))
        ∈ upperHalf := stripToHalf_mem_upperHalf hd
        ((isConformalOnto_deckH hAo hg).mapsTo (halfToStrip_mem_strip hd hw))
    have h6 := congrArg stripCayleyInv h4
    rwa [stripDisc, stripCayleyInv_cayley h5] at h6
  have hgdeckT : ∀ z ∈ expStrip A, deckH A g (g z) = g (deckT z) := by
    intro z hz
    have hzeq : Function.invFunOn g (expStrip A) (g z) = z := hg.2.1.leftInvOn_invFunOn hz
    show g (deckT (Function.invFunOn g (expStrip A) (g z))) = g (deckT z)
    rw [hzeq]
  have hχdeck : ∀ v ∈ strip d,
      halfToStrip d (φ (stripToHalf d (deckH A g v)))
        = halfToStrip d (φ (stripToHalf d v)) + (-(d / Real.pi) * Real.log lam : ℝ) * I := by
    intro v hv
    set w : ℂ := stripToHalf d v with hwdef
    have hw : w ∈ upperHalf := stripToHalf_mem_upperHalf hd hv
    have hveq : v = halfToStrip d w := (halfToStrip_stripToHalf hd hv).symm
    have hstep1 : stripToHalf d (deckH A g v) = stripCayleyInv (c * blaschke a (stripCayley w)) := by
      rw [hveq]; exact hSTH w hw
    have hφw : φ w ∈ upperHalf := hφconf.mapsTo hw
    have hwneq' : (1 : ℂ) * w + (-(q' : ℂ)) ≠ 0 := by
      intro hcon
      have h0 : w.im = 0 := by
        have : w = (q' : ℂ) := by linear_combination hcon
        rw [this]; simp
      have h0' : 0 < w.im := hw
      linarith
    have hφInvφ : φInv (φ w) = w := hφInv_left w hwneq'
    have hlamw := hlam (φ w) hφw
    rw [hψdef] at hlamw
    simp only [hφInvφ] at hlamw
    rw [hstep1, hlamw]
    set u : ℂ := halfToStrip d (φ w) with hudef
    have hu : u ∈ strip d := halfToStrip_mem_strip hd hφw
    have hφwne : φ w ≠ 0 := fun h => absurd (h ▸ hφw) (by simp [upperHalf])
    have huφw : φ w = stripToHalf d u := (stripToHalf_halfToStrip hd hφwne).symm
    rw [huφw, halfToStrip_lam_mul_stripToHalf hd hlam_pos hu]
  set s : ℝ := -(d / Real.pi) * Real.log lam with hsdef
  set g' : ℂ → ℂ := fun z => halfToStrip d (φ (stripToHalf d (g z))) with hg'def
  have hTconf : IsConformalOnto (fun w => halfToStrip d (φ (stripToHalf d w))) (strip d)
      (strip d) := (isConformalOnto_halfToStrip hd).comp (hφconf.comp
        (isConformalOnto_stripToHalf hd))
  have hg'conf : IsConformalOnto g' (expStrip A) (strip d) := hTconf.comp hg
  have hper : ∀ z ∈ expStrip A, g' (deckT z) = g' z + (s : ℂ) * I := by
    intro z hz
    have hgz : g z ∈ strip d := by rw [← hg.2.2]; exact Set.mem_image_of_mem g hz
    show halfToStrip d (φ (stripToHalf d (g (deckT z))))
        = halfToStrip d (φ (stripToHalf d (g z))) + (s : ℂ) * I
    rw [← hgdeckT z hz]
    exact hχdeck (g z) hgz
  have hmemhalf : ((d / 2 : ℝ) : ℂ) ∈ strip d := by
    constructor
    · show (0 : ℝ) < ((d / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
    · show (((d / 2 : ℝ) : ℂ)).re < d
      rw [Complex.ofReal_re]; linarith
  have hlamne1 : lam ≠ 1 := by
    intro hlam1
    have hs0 : s = 0 := by rw [hsdef, hlam1, Real.log_one]; ring
    have hmemimg : ((d / 2 : ℝ) : ℂ) ∈ g '' expStrip A := by rw [hg.2.2]; exact hmemhalf
    obtain ⟨z0, hz0mem, _⟩ := hmemimg
    have hz0Tmem : deckT z0 ∈ expStrip A := deckT_mem_expStrip hz0mem
    have heqz : g' (deckT z0) = g' z0 := by rw [hper z0 hz0mem, hs0]; simp
    have hdT : deckT z0 = z0 := hg'conf.2.1 hz0Tmem hz0mem heqz
    have h2 : (2 : ℂ) * (Real.pi : ℂ) * I = 0 := by
      have := hdT
      unfold deckT at this
      linear_combination this
    exact two_pi_mul_I_ne_zero h2
  rcases lt_or_gt_of_ne hlamne1 with hlt | hlt
  · have hlog : Real.log lam < 0 := Real.log_neg hlam_pos hlt
    refine ⟨g', s, hg'conf, ?_, ?_⟩
    · rw [hsdef]
      have : 0 < d / Real.pi := div_pos hd Real.pi_pos
      nlinarith
    · intro z hz
      have := hper z hz
      rwa [deckT] at this
  · have hlog : 0 < Real.log lam := Real.log_pos hlt
    have hrefl : IsConformalOnto (fun w : ℂ => (d : ℂ) - w) (strip d) (strip d) := by
      refine ⟨?_, ?_, ?_⟩
      · fun_prop
      · intro x _ y _ hxy
        have hxy' : (d : ℂ) - x = (d : ℂ) - y := hxy
        linear_combination -hxy'
      · ext w
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨?_, ?_⟩
          · show (0 : ℝ) < ((d : ℂ) - x).re
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hx.2]
          · show ((d : ℂ) - x).re < d
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hx.1]
        · intro hw
          refine ⟨(d : ℂ) - w, ⟨?_, ?_⟩, ?_⟩
          · show (0 : ℝ) < ((d : ℂ) - w).re
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hw.2]
          · show ((d : ℂ) - w).re < d
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hw.1]
          · ring
    refine ⟨fun z => (d : ℂ) - g' z, -s, hrefl.comp hg'conf, ?_, ?_⟩
    · rw [hsdef]
      have : 0 < d / Real.pi := div_pos hd Real.pi_pos
      nlinarith
    · intro z hz
      have hstep := hper z hz
      rw [deckT] at hstep
      show (d : ℂ) - g' (z + 2 * (Real.pi : ℂ) * I) = (d : ℂ) - g' z + (-s : ℝ) * I
      rw [hstep]
      push_cast
      ring

/-- **Degenerate edge case of `key_construction`**: one of the deck transformation's two
circle fixed points is exactly `1` (the Cayley-degenerate point whose `stripCayleyInv` value
is `∞`, i.e. one fixed point sits at the strip's own vertical end rather than at a finite
boundary point).  `φ` is then a plain translation instead of a genuine two-point Möbius
normalization, so the `hψinf` chase goes through `tendsto_stripCayley_cobounded` /
`tendsto_stripCayleyInv_cobounded_of_ne_one` directly instead of the pole/eventually-≠ dance. -/
theorem key_construction_edge {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (h1fix : c * blaschke a 1 = 1)
    {R : ℂ} (hRn : ‖R‖ = 1) (hR1 : R ≠ 1) (hRfix : c * blaschke a R = R)
    {r' : ℝ} (hr'eq : stripCayleyInv R = (r' : ℂ)) :
    ∃ (g' : ℂ → ℂ) (s : ℝ), IsConformalOnto g' (expStrip A) (strip d) ∧ 0 < s ∧
      ∀ z ∈ expStrip A, g' (z + 2 * (Real.pi : ℂ) * I) = g' z + (s : ℂ) * I := by
  set φ : ℂ → ℂ := mobiusFn 1 (-(r' : ℂ)) 0 1 with hφdef
  set φInv : ℂ → ℂ := mobiusFn 1 (r' : ℂ) 0 1 with hφInvdef
  have hdetne : (1 : ℂ) * 1 - (-(r' : ℂ)) * 0 ≠ 0 := by norm_num
  have hφconf : IsConformalOnto φ upperHalf upperHalf := by
    have hdetpos : (0 : ℝ) < 1 * 1 - (-r') * 0 := by norm_num
    have := isConformalOnto_mobius_upperHalf (a := (1 : ℝ)) (b := -r') (c := (0 : ℝ))
      (d := (1 : ℝ)) hdetpos
    convert this using 2 <;> push_cast <;> ring
  have hφInv_left : ∀ z : ℂ, φInv (φ z) = z := by
    intro z
    have := mobiusFn_inv_apply (a := (1 : ℂ)) (b := -(r' : ℂ)) (c := (0 : ℂ)) (d := (1 : ℂ))
      hdetne (show (0 : ℂ) * z + 1 ≠ 0 by norm_num)
    simpa [hφdef, hφInvdef] using this
  have hφ0 : φ (r' : ℂ) = 0 := by
    simp only [hφdef, mobiusFn]; norm_num
  have hφInv0 : φInv 0 = (r' : ℂ) := by
    simp only [hφInvdef, mobiusFn]; norm_num
  have hφInvconf : IsConformalOnto φInv upperHalf upperHalf := by
    have hdetpos' : (0 : ℝ) < 1 * 1 - r' * 0 := by norm_num
    have := isConformalOnto_mobius_upperHalf (a := (1 : ℝ)) (b := (r' : ℝ)) (c := (0 : ℝ))
      (d := (1 : ℝ)) hdetpos'
    convert this using 2 <;> push_cast <;> ring
  have hcbconf : IsConformalOnto (fun z => c * blaschke a z) unitDisc unitDisc := by
    obtain ⟨hdo, hinj, himg⟩ := isConformalOnto_deckH_disc hd hAo hg
    refine ⟨hdo.congr heqOn.symm, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hinj hx hy ((heqOn hx).trans (hxy.trans (heqOn hy).symm))
    · have hstep : (fun z => c * blaschke a z) '' unitDisc = deckH_disc A d g '' unitDisc := by
        apply Set.image_congr
        intro x hx
        exact (heqOn hx).symm
      rw [hstep, himg]
  set ψAssembled : ℂ → ℂ :=
      fun w => φ (stripCayleyInv (c * blaschke a (stripCayley (φInv w)))) with hψdef
  have hψconf : IsConformalOnto ψAssembled upperHalf upperHalf :=
    hφconf.comp (isConformalOnto_stripCayleyInv.comp
      (hcbconf.comp (isConformalOnto_stripCayley.comp hφInvconf)))
  have hψ0 : Tendsto ψAssembled (𝓝[upperHalf] (0 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto φInv (𝓝[upperHalf] (0 : ℂ)) (𝓝 (r' : ℂ)) := by
      have hcont : ContinuousAt φInv (0 : ℂ) := by
        rw [hφInvdef]; exact continuousAt_mobiusFn (by norm_num)
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[upperHalf] (0 : ℂ) ≤ 𝓝 0)
      rwa [hφInv0] at this
    have h2 : Tendsto stripCayley (𝓝 (r' : ℂ)) (𝓝 R) := by
      have hcont := (continuousAt_stripCayley_real r').tendsto
      have hval : stripCayley (r' : ℂ) = R := by
        rw [← hr'eq]; exact stripCayley_cayleyInv_of_ne_one hR1
      rwa [hval] at hcont
    have h3 : Tendsto (fun z => c * blaschke a z) (𝓝 R) (𝓝 R) := by
      have := (continuousAt_blaschke_of_le_one (c := c) ha (le_of_eq hRn)).tendsto
      rwa [hRfix] at this
    have h4 : Tendsto stripCayleyInv (𝓝 R) (𝓝 (r' : ℂ)) := by
      have := (continuousAt_stripCayleyInv_of_ne_one hR1).tendsto
      rwa [hr'eq] at this
    have h5 : Tendsto φ (𝓝 (r' : ℂ)) (𝓝 0) := by
      have hcont : ContinuousAt φ (r' : ℂ) := by
        rw [hφdef]; exact continuousAt_mobiusFn (by norm_num)
      have := hcont.tendsto
      rwa [hφ0] at this
    exact h5.comp (h4.comp (h3.comp (h2.comp h1)))
  have hψinf : Tendsto (fun w => ‖ψAssembled w‖)
      (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    have h1 : Tendsto φInv (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (cobounded ℂ) := by
      have hcb : Tendsto φInv (cobounded ℂ) (cobounded ℂ) := by
        have heq : φInv = fun z => (1 : ℂ) * z + (r' : ℂ) := by
          rw [hφInvdef]; funext z; simp [mobiusFn]
        rw [heq]; exact tendsto_affine_cobounded one_ne_zero _
      exact (hcb.mono_left comap_norm_atTop.le).mono_left inf_le_left
    have h2 : Tendsto stripCayley (cobounded ℂ) (𝓝 (1 : ℂ)) := tendsto_stripCayley_cobounded
    have h3 : Tendsto (fun z => c * blaschke a z) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ)) := by
      have := (continuousAt_blaschke_of_le_one (c := c) ha
        (le_of_eq (by norm_num : ‖(1 : ℂ)‖ = 1))).tendsto
      rwa [h1fix] at this
    have hMapsTo : ∀ w ∈ upperHalf,
        c * blaschke a (stripCayley (φInv w)) ∈ unitDisc := by
      intro w hw
      have hw1 : φInv w ∈ upperHalf := hφInvconf.mapsTo hw
      have hw2 : stripCayley (φInv w) ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw1
      exact hcbconf.mapsTo hw2
    have hev : ∀ᶠ w in (Filter.comap norm atTop ⊓ 𝓟 upperHalf), w ∈ upperHalf :=
      Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.2 (fun w hw => hw))
    have hne_ev : ∀ᶠ w in (Filter.comap norm atTop ⊓ 𝓟 upperHalf),
        (fun z => c * blaschke a z) (stripCayley (φInv w)) ≠ (1 : ℂ) := by
      filter_upwards [hev] with w hw hcon
      have hmem := hMapsTo w hw
      rw [hcon] at hmem
      simp [unitDisc, Metric.mem_ball, Complex.dist_eq] at hmem
    have hplain : Tendsto ((fun z => c * blaschke a z) ∘ stripCayley ∘ φInv)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (𝓝 (1 : ℂ)) :=
      h3.comp (h2.comp h1)
    have h34 : Tendsto ((fun z => c * blaschke a z) ∘ stripCayley ∘ φInv)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (𝓝[≠] (1 : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hplain, hne_ev⟩
    have h4' : Tendsto (stripCayleyInv ∘ (fun z => c * blaschke a z) ∘ stripCayley ∘ φInv)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) (cobounded ℂ) :=
      tendsto_stripCayleyInv_cobounded_of_ne_one.comp h34
    have h5 : Tendsto φ (cobounded ℂ) (cobounded ℂ) := by
      have heq : φ = fun z => (1 : ℂ) * z + (-(r' : ℂ)) := by
        rw [hφdef]; funext z; simp [mobiusFn]
      rw [heq]; exact tendsto_affine_cobounded one_ne_zero _
    rw [← tendsto_norm_atTop_iff_cobounded] at h5
    exact h5.comp h4'
  obtain ⟨lam, hlam_pos, hlam⟩ := upperHalf_automorphism_eq_dilate hψconf hψ0 hψinf
  have hSTH : ∀ w ∈ upperHalf,
      stripToHalf d (deckH A g (halfToStrip d w)) = stripCayleyInv (c * blaschke a (stripCayley w)) := by
    intro w hw
    have hcw : stripCayley w ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw
    have h1 : stripDiscInv d (stripCayley w) = halfToStrip d w := by
      rw [stripDiscInv, stripCayleyInv_cayley hw]
    have h2 : deckH_disc A d g (stripCayley w) = stripDisc d (deckH A g (halfToStrip d w)) := by
      rw [deckH_disc, h1]
    have h3 : deckH_disc A d g (stripCayley w) = c * blaschke a (stripCayley w) := heqOn hcw
    have h4 : stripDisc d (deckH A g (halfToStrip d w)) = c * blaschke a (stripCayley w) := by
      rw [← h2, h3]
    have h5 : stripToHalf d (deckH A g (halfToStrip d w))
        ∈ upperHalf := stripToHalf_mem_upperHalf hd
        ((isConformalOnto_deckH hAo hg).mapsTo (halfToStrip_mem_strip hd hw))
    have h6 := congrArg stripCayleyInv h4
    rwa [stripDisc, stripCayleyInv_cayley h5] at h6
  have hgdeckT : ∀ z ∈ expStrip A, deckH A g (g z) = g (deckT z) := by
    intro z hz
    have hzeq : Function.invFunOn g (expStrip A) (g z) = z := hg.2.1.leftInvOn_invFunOn hz
    show g (deckT (Function.invFunOn g (expStrip A) (g z))) = g (deckT z)
    rw [hzeq]
  have hχdeck : ∀ v ∈ strip d,
      halfToStrip d (φ (stripToHalf d (deckH A g v)))
        = halfToStrip d (φ (stripToHalf d v)) + (-(d / Real.pi) * Real.log lam : ℝ) * I := by
    intro v hv
    set w : ℂ := stripToHalf d v with hwdef
    have hw : w ∈ upperHalf := stripToHalf_mem_upperHalf hd hv
    have hveq : v = halfToStrip d w := (halfToStrip_stripToHalf hd hv).symm
    have hstep1 : stripToHalf d (deckH A g v) = stripCayleyInv (c * blaschke a (stripCayley w)) := by
      rw [hveq]; exact hSTH w hw
    have hφw : φ w ∈ upperHalf := hφconf.mapsTo hw
    have hφInvφ : φInv (φ w) = w := hφInv_left w
    have hlamw := hlam (φ w) hφw
    rw [hψdef] at hlamw
    simp only [hφInvφ] at hlamw
    rw [hstep1, hlamw]
    set u : ℂ := halfToStrip d (φ w) with hudef
    have hu : u ∈ strip d := halfToStrip_mem_strip hd hφw
    have hφwne : φ w ≠ 0 := fun h => absurd (h ▸ hφw) (by simp [upperHalf])
    have huφw : φ w = stripToHalf d u := (stripToHalf_halfToStrip hd hφwne).symm
    rw [huφw, halfToStrip_lam_mul_stripToHalf hd hlam_pos hu]
  set s : ℝ := -(d / Real.pi) * Real.log lam with hsdef
  set g' : ℂ → ℂ := fun z => halfToStrip d (φ (stripToHalf d (g z))) with hg'def
  have hTconf : IsConformalOnto (fun w => halfToStrip d (φ (stripToHalf d w))) (strip d)
      (strip d) := (isConformalOnto_halfToStrip hd).comp (hφconf.comp
        (isConformalOnto_stripToHalf hd))
  have hg'conf : IsConformalOnto g' (expStrip A) (strip d) := hTconf.comp hg
  have hper : ∀ z ∈ expStrip A, g' (deckT z) = g' z + (s : ℂ) * I := by
    intro z hz
    have hgz : g z ∈ strip d := by rw [← hg.2.2]; exact Set.mem_image_of_mem g hz
    show halfToStrip d (φ (stripToHalf d (g (deckT z))))
        = halfToStrip d (φ (stripToHalf d (g z))) + (s : ℂ) * I
    rw [← hgdeckT z hz]
    exact hχdeck (g z) hgz
  have hmemhalf : ((d / 2 : ℝ) : ℂ) ∈ strip d := by
    constructor
    · show (0 : ℝ) < ((d / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
    · show (((d / 2 : ℝ) : ℂ)).re < d
      rw [Complex.ofReal_re]; linarith
  have hlamne1 : lam ≠ 1 := by
    intro hlam1
    have hs0 : s = 0 := by rw [hsdef, hlam1, Real.log_one]; ring
    have hmemimg : ((d / 2 : ℝ) : ℂ) ∈ g '' expStrip A := by rw [hg.2.2]; exact hmemhalf
    obtain ⟨z0, hz0mem, _⟩ := hmemimg
    have hz0Tmem : deckT z0 ∈ expStrip A := deckT_mem_expStrip hz0mem
    have heqz : g' (deckT z0) = g' z0 := by rw [hper z0 hz0mem, hs0]; simp
    have hdT : deckT z0 = z0 := hg'conf.2.1 hz0Tmem hz0mem heqz
    have h2 : (2 : ℂ) * (Real.pi : ℂ) * I = 0 := by
      have := hdT
      unfold deckT at this
      linear_combination this
    exact two_pi_mul_I_ne_zero h2
  rcases lt_or_gt_of_ne hlamne1 with hlt | hlt
  · have hlog : Real.log lam < 0 := Real.log_neg hlam_pos hlt
    refine ⟨g', s, hg'conf, ?_, ?_⟩
    · rw [hsdef]
      have : 0 < d / Real.pi := div_pos hd Real.pi_pos
      nlinarith
    · intro z hz
      have := hper z hz
      rwa [deckT] at this
  · have hlog : 0 < Real.log lam := Real.log_pos hlt
    have hrefl : IsConformalOnto (fun w : ℂ => (d : ℂ) - w) (strip d) (strip d) := by
      refine ⟨?_, ?_, ?_⟩
      · fun_prop
      · intro x _ y _ hxy
        have hxy' : (d : ℂ) - x = (d : ℂ) - y := hxy
        linear_combination -hxy'
      · ext w
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨?_, ?_⟩
          · show (0 : ℝ) < ((d : ℂ) - x).re
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hx.2]
          · show ((d : ℂ) - x).re < d
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hx.1]
        · intro hw
          refine ⟨(d : ℂ) - w, ⟨?_, ?_⟩, ?_⟩
          · show (0 : ℝ) < ((d : ℂ) - w).re
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hw.2]
          · show ((d : ℂ) - w).re < d
            rw [Complex.sub_re, Complex.ofReal_re]
            linarith [hw.1]
          · ring
    refine ⟨fun z => (d : ℂ) - g' z, -s, hrefl.comp hg'conf, ?_, ?_⟩
    · rw [hsdef]
      have : 0 < d / Real.pi := div_pos hd Real.pi_pos
      nlinarith
    · intro z hz
      have hstep := hper z hz
      rw [deckT] at hstep
      show (d : ℂ) - g' (z + 2 * (Real.pi : ℂ) * I) = (d : ℂ) - g' z + (-s : ℝ) * I
      rw [hstep]
      push_cast
      ring


/-! ## Part 11: the parabolic case — coefficient algebra for the translate identity

`hparab : c = 1 - 2 * conj a` is exactly "1 is a repeated root of `fixedPointPoly c a`", i.e.
the deck transform's disc-conjugate is parabolic with its (unique) fixed point AT the
Cayley-degenerate point `1`.  Under this hypothesis,
`stripCayleyInv (c * blaschke a (stripCayley w)) = w + β` for a REAL `β`. -/

theorem cross_lemma {a c ζ : ℂ} (hden1 : (1:ℂ) - conj a * ζ ≠ 0) :
    (1 - c * blaschke a ζ) * (1 - conj a * ζ) = (1 + c*a) - (c + conj a)*ζ := by
  simp only [blaschke, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden1]
  ring

theorem cross_lemma2 {a c ζ : ℂ} (hden1 : (1:ℂ) - conj a * ζ ≠ 0) :
    (1 + c * blaschke a ζ) * (1 - conj a * ζ) = (1 - c*a) + (c - conj a)*ζ := by
  simp only [blaschke, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden1]
  ring

/-- Pure Möbius composition, `ζ` opaque. -/
theorem stripCayleyInv_blaschke_eq_zeta {a c ζ : ℂ}
    (hden1 : (1:ℂ) - conj a * ζ ≠ 0)
    (hden2 : (1:ℂ) - c * blaschke a ζ ≠ 0) :
    stripCayleyInv (c * blaschke a ζ)
      = I * ((1 - c*a) + (c - conj a)*ζ) / ((1 + c*a) - (c + conj a)*ζ) := by
  have hden3 : (1 + c*a) - (c + conj a)*ζ ≠ 0 := by
    rw [← cross_lemma hden1]
    exact mul_ne_zero hden2 hden1
  rw [stripCayleyInv, div_eq_div_iff hden2 hden3, ← cross_lemma2 hden1, ← cross_lemma hden1]
  ring

theorem hcc_of_parab {a c : ℂ} (hc : ‖c‖ = 1) (hparab : c = 1 - 2 * conj a) :
    conj a + a = 2 * (a * conj a) := by
  have h1 : c * conj c = 1 := by
    have hns : Complex.normSq c = 1 := by rw [← Complex.sq_norm, hc]; norm_num
    have h2 := Complex.mul_conj c
    rw [hns] at h2
    simpa using h2
  have hconjc : conj c = 1 - 2 * a := by
    have := congrArg conj hparab
    simpa [Complex.conj_conj, map_ofNat] using this
  rw [hconjc, hparab] at h1
  linear_combination (-1/2 : ℂ) * h1

/-- Substituting `ζ = stripCayley w` and using `hparab`, the composition becomes an honest
translation of `w`. -/
theorem stripCayleyInv_blaschke_stripCayley_eq_translate_raw {a c w : ℂ} (hwI : w + I ≠ 0)
    (hparab : c = 1 - 2 * conj a)
    (hcc : conj a + a = 2*(a*conj a)) (haone : (1:ℂ) - conj a ≠ 0)
    (hden3 : (1 + c*a) - (c + conj a)*((w-I)/(w+I)) ≠ 0) :
    I * ((1 - c*a) + (c - conj a)*((w-I)/(w+I)))
      / ((1 + c*a) - (c + conj a)*((w-I)/(w+I)))
    = w + 2*I*conj a/(1 - conj a) := by
  have hNum : (I * ((1 - c*a) + (c - conj a)*((w-I)/(w+I)))) * (w+I)
      = I * ((1 - c*a)*(w+I) + (c - conj a)*(w-I)) := by
    field_simp
  have hDen : (((1 + c*a) - (c + conj a)*((w-I)/(w+I)))) * (w+I)
      = (1 + c*a)*(w+I) - (c + conj a)*(w-I) := by
    field_simp
  rw [show I * ((1 - c*a) + (c - conj a)*((w-I)/(w+I)))
        / ((1 + c*a) - (c + conj a)*((w-I)/(w+I)))
      = (I * ((1 - c*a) + (c - conj a)*((w-I)/(w+I))) * (w+I))
        / (((1 + c*a) - (c + conj a)*((w-I)/(w+I))) * (w+I)) from
      (mul_div_mul_right _ _ hwI).symm,
    hNum, hDen]
  have hDen' : (1 + c*a)*(w+I) - (c + conj a)*(w-I) ≠ 0 := by
    rw [← hDen]; exact mul_ne_zero hden3 hwI
  rw [div_eq_iff hDen', hparab]
  field_simp
  linear_combination (1 + conj a - 2*I*w + w^2*conj a - w^2) * hcc
    + (-conj a + conj a * a - conj a^2 + 2*conj a^2*a - a) * Complex.I_sq

theorem re_eq_normSq_of_parab {a : ℂ} (hcc : conj a + a = 2 * (a * conj a)) :
    a.re = a.re^2 + a.im^2 := by
  have h1 : conj a + a = ((2*a.re:ℝ):ℂ) := by rw [add_comm]; exact Complex.add_conj a
  have h2 : a * conj a = ((Complex.normSq a : ℝ):ℂ) := Complex.mul_conj a
  rw [h1, h2] at hcc
  have h3 : (2*a.re:ℝ) = 2 * Complex.normSq a := by exact_mod_cast hcc
  rw [Complex.normSq_apply] at h3
  nlinarith [h3]

theorem re_ne_one_of_parab {a : ℂ} (ha : ‖a‖ < 1) (hcc : conj a + a = 2 * (a * conj a)) :
    a.re ≠ 1 := by
  have hre2 := re_eq_normSq_of_parab hcc
  have hnormsq : a.re^2 + a.im^2 < 1 := by
    have h4 : Complex.normSq a < 1 := by
      rw [← Complex.sq_norm]
      nlinarith [ha, norm_nonneg a]
    rw [Complex.normSq_apply] at h4
    nlinarith [h4]
  intro h
  rw [h] at hre2
  have h5 : a.im^2 = 0 := by linarith
  have him0 : a.im = 0 := by nlinarith [sq_nonneg a.im]
  rw [h, him0] at hnormsq
  norm_num at hnormsq

theorem conj_a_ne_one_of_parab {a : ℂ} (ha : ‖a‖ < 1) (hcc : conj a + a = 2 * (a * conj a)) :
    (1:ℂ) - conj a ≠ 0 := by
  intro hcon
  apply re_ne_one_of_parab ha hcc
  have h1 := congrArg Complex.re hcon
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h1
  linarith

theorem two_I_conj_div_eq_real {a : ℂ} (ha : ‖a‖ < 1) (hcc : conj a + a = 2 * (a * conj a)) :
    2 * I * conj a / (1 - conj a) = ((2 * a.im / (1 - a.re) : ℝ) : ℂ) := by
  have hre2 := re_eq_normSq_of_parab hcc
  have hane1 := re_ne_one_of_parab ha hcc
  have haoneC := conj_a_ne_one_of_parab ha hcc
  rw [div_eq_iff haoneC]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    field_simp
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    field_simp
    linarith [hre2]

/-- **The parabolic-at-1 translate identity.** -/
theorem stripCayleyInv_blaschke_stripCayley_eq_translate {a c w : ℂ} (ha : ‖a‖ < 1)
    (hc : ‖c‖ = 1) (hparab : c = 1 - 2 * conj a) (hw : w ∈ upperHalf) :
    stripCayleyInv (c * blaschke a (stripCayley w)) = w + ((2 * a.im / (1 - a.re) : ℝ) : ℂ) := by
  have hwI : w + I ≠ 0 := by
    intro h
    have hwneg : w = -I := by linear_combination h
    rw [hwneg] at hw
    simp only [upperHalf, Set.mem_setOf_eq, Complex.neg_im, Complex.I_im] at hw
    linarith
  have hcc := hcc_of_parab hc hparab
  have hcne : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hcc' : c * conj c = 1 := by
    have hns : Complex.normSq c = 1 := by rw [← Complex.sq_norm, hc]; norm_num
    have h2 := Complex.mul_conj c
    rw [hns] at h2; simpa using h2
  have hrot : IsConformalOnto (fun z => c * z) unitDisc unitDisc := by
    refine ⟨by fun_prop, ?_, ?_⟩
    · intro x _ y _ hxy
      exact mul_left_cancel₀ hcne hxy
    · ext z
      simp only [Set.mem_image, unitDisc, mem_ball_zero_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩; rwa [norm_mul, hc, one_mul]
      · intro hz
        refine ⟨conj c * z, ?_, ?_⟩
        · rw [norm_mul, Complex.norm_conj, hc, one_mul]; exact hz
        · rw [show c * (conj c * z) = (c * conj c) * z from by ring, hcc']; ring
  have hcbconf : IsConformalOnto (fun z => c * blaschke a z) unitDisc unitDisc :=
    hrot.comp (isConformalOnto_blaschke ha)
  have hζ : stripCayley w ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw
  have hζnorm : ‖stripCayley w‖ < 1 := mem_ball_zero_iff.mp hζ
  have hden1 : (1:ℂ) - conj a * stripCayley w ≠ 0 := hden_ne_of_blaschke ha hζnorm.le
  have hden2 : (1:ℂ) - c * blaschke a (stripCayley w) ≠ 0 := by
    have hmapsto : c * blaschke a (stripCayley w) ∈ unitDisc := hcbconf.mapsTo hζ
    intro hcon
    have hcon' : c * blaschke a (stripCayley w) = 1 := by linear_combination -hcon
    rw [hcon'] at hmapsto
    simp [unitDisc, Metric.mem_ball] at hmapsto
  have haone : (1:ℂ) - conj a ≠ 0 := conj_a_ne_one_of_parab ha hcc
  rw [stripCayleyInv_blaschke_eq_zeta hden1 hden2, ← two_I_conj_div_eq_real ha hcc]
  have hden3 : (1 + c*a) - (c + conj a)*(stripCayley w) ≠ 0 := by
    rw [← cross_lemma hden1]
    exact mul_ne_zero hden2 hden1
  rw [stripCayley] at hden3 ⊢
  exact stripCayleyInv_blaschke_stripCayley_eq_translate_raw hwI hparab hcc haone hden3

/-! ## Part 12: the descent, towards excluding the parabolic case entirely -/

theorem hSTH_general {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ}
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc) :
    ∀ w ∈ upperHalf,
      stripToHalf d (deckH A g (halfToStrip d w)) = stripCayleyInv (c * blaschke a (stripCayley w)) := by
  intro w hw
  have hcw : stripCayley w ∈ unitDisc := isConformalOnto_stripCayley.mapsTo hw
  have h1 : stripDiscInv d (stripCayley w) = halfToStrip d w := by
    rw [stripDiscInv, stripCayleyInv_cayley hw]
  have h2 : deckH_disc A d g (stripCayley w) = stripDisc d (deckH A g (halfToStrip d w)) := by
    rw [deckH_disc, h1]
  have h3 : deckH_disc A d g (stripCayley w) = c * blaschke a (stripCayley w) := heqOn hcw
  have h4 : stripDisc d (deckH A g (halfToStrip d w)) = c * blaschke a (stripCayley w) := by
    rw [← h2, h3]
  have h5 : stripToHalf d (deckH A g (halfToStrip d w))
      ∈ upperHalf := stripToHalf_mem_upperHalf hd
      ((isConformalOnto_deckH hAo hg).mapsTo (halfToStrip_mem_strip hd hw))
  have h6 := congrArg stripCayleyInv h4
  rwa [stripDisc, stripCayleyInv_cayley h5] at h6

theorem hgdeckT_general {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hg : IsConformalOnto g (expStrip A) (strip d)) :
    ∀ z ∈ expStrip A, deckH A g (g z) = g (deckT z) := by
  intro z hz
  have hzeq : Function.invFunOn g (expStrip A) (g z) = z := hg.2.1.leftInvOn_invFunOn hz
  show g (deckT (Function.invFunOn g (expStrip A) (g z))) = g (deckT z)
  rw [hzeq]

/-- The periodicity of `h := stripToHalf d ∘ g` under the deck shift, forced by the
parabolic-at-1 translate identity. -/
theorem stripToHalf_g_periodic {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (hparab : c = 1 - 2 * conj a) :
    ∀ z ∈ expStrip A,
      stripToHalf d (g (deckT z)) = stripToHalf d (g z) + ((2 * a.im / (1 - a.re) : ℝ) : ℂ) := by
  intro z hz
  have hgz : g z ∈ strip d := by rw [← hg.2.2]; exact Set.mem_image_of_mem g hz
  rw [← hgdeckT_general hg z hz]
  have hw : stripToHalf d (g z) ∈ upperHalf := stripToHalf_mem_upperHalf hd hgz
  have hSTH := hSTH_general hd hAo hg heqOn (stripToHalf d (g z)) hw
  rw [halfToStrip_stripToHalf hd hgz] at hSTH
  rw [hSTH]
  exact stripCayleyInv_blaschke_stripCayley_eq_translate ha hc hparab hw

theorem beta_ne_zero_of_parab {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d)) {c a : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (hparab : c = 1 - 2 * conj a) :
    (2 * a.im / (1 - a.re) : ℝ) ≠ 0 := by
  intro hβ0
  have hmemhalf : ((d / 2 : ℝ) : ℂ) ∈ strip d := by
    constructor
    · show (0 : ℝ) < ((d / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
    · show (((d / 2 : ℝ) : ℂ)).re < d
      rw [Complex.ofReal_re]; linarith
  have hmemimg : ((d / 2 : ℝ) : ℂ) ∈ g '' expStrip A := by rw [hg.2.2]; exact hmemhalf
  obtain ⟨z0, hz0mem, hz0eq⟩ := hmemimg
  have hper := stripToHalf_g_periodic hd hAo hg ha hc heqOn hparab z0 hz0mem
  rw [hβ0] at hper
  simp only [Complex.ofReal_zero, add_zero] at hper
  have hz0Tmem : deckT z0 ∈ expStrip A := deckT_mem_expStrip hz0mem
  have heqz : g (deckT z0) = g z0 := by
    have hinj : InjOn (stripToHalf d) (strip d) := (isConformalOnto_stripToHalf hd).2.1
    have hgTmem : g (deckT z0) ∈ strip d := by rw [← hg.2.2]; exact Set.mem_image_of_mem g hz0Tmem
    have hgmem : g z0 ∈ strip d := by rw [← hg.2.2]; exact Set.mem_image_of_mem g hz0mem
    exact hinj hgTmem hgmem hper
  have hinjg : InjOn g (expStrip A) := hg.2.1
  have : deckT z0 = z0 := hinjg hz0Tmem hz0mem heqz
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * I = 0 := by
    have hthis := this
    unfold deckT at hthis
    linear_combination hthis
  exact two_pi_mul_I_ne_zero h2

/-! ## Part 14: general translate-identity helpers and `parabolic_excluded_at_one` -/

theorem halfToStrip_im_formula (d : ℝ) (ξ : ℂ) :
    (halfToStrip d ξ).im = -(d / Real.pi) * (Complex.log ξ).re := by
  rw [halfToStrip]
  simp [Complex.mul_im, Complex.mul_re]

theorem halfToStrip_mem_upperHalf_of_ne_zero {d : ℝ} (hd : 0 < d) {ξ : ℂ} (hξ0 : ξ ≠ 0)
    (hξ1 : ‖ξ‖ < 1) : halfToStrip d ξ ∈ upperHalf := by
  show 0 < (halfToStrip d ξ).im
  rw [halfToStrip_im_formula, Complex.log_re]
  have hlt : Real.log ‖ξ‖ < 0 := Real.log_neg (norm_pos_iff.mpr hξ0) hξ1
  have hdpi : 0 < d / Real.pi := div_pos hd Real.pi_pos
  nlinarith

theorem norm_stripToHalf' (d : ℝ) (z : ℂ) :
    ‖stripToHalf d z‖ = Real.exp (-(Real.pi / d) * z.im) := by
  rw [stripToHalf, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

theorem stripToHalf_add (d : ℝ) (u v : ℂ) :
    stripToHalf d (u + v) = stripToHalf d u * stripToHalf d v := by
  rw [stripToHalf, stripToHalf, stripToHalf, ← Complex.exp_add]
  ring_nf

theorem exp_int_two_pi_mul_I (n : ℤ) : Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
  have h := (Complex.exp_periodic.int_mul n) 0
  simpa using h

theorem exp_hInv_shift_abs_beta {β : ℝ} (hβne0 : β ≠ 0) {hInv : ℂ → ℂ}
    (hInv_int : ∀ w ∈ upperHalf, ∀ n : ℤ,
      hInv (w + (n : ℂ) * (β : ℂ)) = hInv w + (n : ℂ) * (2 * (Real.pi : ℂ) * I))
    {X : ℂ} (hX : X ∈ upperHalf) (n : ℤ) :
    Complex.exp (hInv (X + ((|β| * (n : ℝ) : ℝ) : ℂ))) = Complex.exp (hInv X) := by
  rcases lt_or_gt_of_ne hβne0 with hβneg | hβpos
  · have habs : (|β| : ℝ) = -β := abs_of_neg hβneg
    have heq : X + ((|β| * (n : ℝ) : ℝ) : ℂ) = X + (((-n : ℤ) : ℂ)) * (β : ℂ) := by
      rw [habs]; push_cast; ring
    rw [heq, hInv_int X hX (-n), Complex.exp_add, exp_int_two_pi_mul_I, mul_one]
  · have habs : (|β| : ℝ) = β := abs_of_pos hβpos
    have heq : X + ((|β| * (n : ℝ) : ℝ) : ℂ) = X + ((n : ℤ) : ℂ) * (β : ℂ) := by
      rw [habs]; push_cast; ring
    rw [heq, hInv_int X hX n, Complex.exp_add, exp_int_two_pi_mul_I, mul_one]

theorem stripToHalf_int_beta_eq_one {β : ℝ} (hβne0 : β ≠ 0) (m : ℤ) :
    stripToHalf (|β| / 2) ((m : ℂ) * (β : ℂ)) = 1 := by
  rcases lt_or_gt_of_ne hβne0 with hβneg | hβpos
  · have habs : (|β| : ℝ) = -β := abs_of_neg hβneg
    show Complex.exp (I * ((m : ℂ) * (β : ℂ)) * (Real.pi / (|β| / 2) : ℝ)) = 1
    have harg : I * ((m : ℂ) * (β : ℂ)) * (Real.pi / (|β| / 2) : ℝ)
        = (((-m : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
      rw [habs]
      have hβne : (β : ℂ) ≠ 0 := by exact_mod_cast hβne0
      push_cast
      field_simp
    rw [harg]
    have h := (Complex.exp_periodic.int_mul (-m)) 0
    simpa using h
  · have habs : (|β| : ℝ) = β := abs_of_pos hβpos
    show Complex.exp (I * ((m : ℂ) * (β : ℂ)) * (Real.pi / (|β| / 2) : ℝ)) = 1
    have harg : I * ((m : ℂ) * (β : ℂ)) * (Real.pi / (|β| / 2) : ℝ)
        = (m : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [habs]
      have hβne : (β : ℂ) ≠ 0 := by exact_mod_cast hβne0
      push_cast
      field_simp
    rw [harg]
    have h := (Complex.exp_periodic.int_mul m) 0
    simpa using h

/-- **The parabolic case, root at `1`, is impossible.** -/
theorem parabolic_excluded_at_one {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d))
    (hAbdd : Bornology.IsBounded A) (hball : closedBall 0 1 ⊆ A) (hAcompl : IsPathConnected Aᶜ)
    {c a : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (hparab : c = 1 - 2 * conj a) : False := by
  set β : ℝ := 2 * a.im / (1 - a.re) with hβdef
  have hβne0 : β ≠ 0 := beta_ne_zero_of_parab hd hAo hg ha hc heqOn hparab
  have hβabspos : (0:ℝ) < |β| / 2 := by positivity
  have hper : ∀ z ∈ expStrip A,
      stripToHalf d (g (deckT z)) = stripToHalf d (g z) + (β : ℂ) :=
    stripToHalf_g_periodic hd hAo hg ha hc heqOn hparab
  set h : ℂ → ℂ := fun z => stripToHalf d (g z) with hhdef
  have hhconf : IsConformalOnto h (expStrip A) upperHalf :=
    (isConformalOnto_stripToHalf hd).comp hg
  set hInv : ℂ → ℂ := Function.invFunOn h (expStrip A) with hInvdef
  have hInvconf : IsConformalOnto hInv upperHalf (expStrip A) := hhconf.symm (isOpen_expStrip hAo)
  have hInv_step : ∀ w ∈ upperHalf, hInv (w + (β : ℂ)) = hInv w + 2 * (Real.pi : ℂ) * I := by
    intro w hw
    have hzmem : hInv w ∈ expStrip A := hInvconf.mapsTo hw
    have hhz : h (hInv w) = w := by
      have himg : w ∈ h '' expStrip A := by rw [hhconf.2.2]; exact hw
      exact Function.invFunOn_eq himg
    have hzTmem : deckT (hInv w) ∈ expStrip A := deckT_mem_expStrip hzmem
    have hstep : h (deckT (hInv w)) = w + (β : ℂ) := by
      show stripToHalf d (g (deckT (hInv w))) = w + (β : ℂ)
      have hhz' : stripToHalf d (g (hInv w)) = w := hhz
      rw [hper (hInv w) hzmem, hhz']
    have heq : hInv (w + (β : ℂ)) = deckT (hInv w) := by
      rw [← hstep]
      exact hhconf.2.1.leftInvOn_invFunOn hzTmem
    rw [heq]
    rfl
  have hInv_int : ∀ w ∈ upperHalf, ∀ n : ℤ,
      hInv (w + (n : ℂ) * (β : ℂ)) = hInv w + (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    intro w hw n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih =>
      push_cast
      push_cast at ih
      have hXim : ((i : ℂ) * (β : ℂ)).im = 0 := by rw [Complex.mul_im]; simp
      have hmem : w + (i : ℂ) * (β : ℂ) ∈ upperHalf := by
        show 0 < (w + (i : ℂ) * (β : ℂ)).im
        rw [Complex.add_im, hXim, add_zero]; exact hw
      have hstep := hInv_step (w + (i : ℂ) * (β : ℂ)) hmem
      have harg : w + (i : ℂ) * (β : ℂ) + (β : ℂ) = w + ((i : ℂ) + 1) * (β : ℂ) := by ring
      rw [harg] at hstep
      rw [hstep, ih]; ring
    | pred i ih =>
      push_cast
      push_cast at ih
      have hXim : ((-(i : ℂ) - 1) * (β : ℂ)).im = 0 := by rw [Complex.mul_im]; simp
      have hmem : w + (-(i : ℂ) - 1) * (β : ℂ) ∈ upperHalf := by
        show 0 < (w + (-(i : ℂ) - 1) * (β : ℂ)).im
        rw [Complex.add_im, hXim, add_zero]; exact hw
      have hstep := hInv_step (w + (-(i : ℂ) - 1) * (β : ℂ)) hmem
      have harg : w + (-(i : ℂ) - 1) * (β : ℂ) + (β : ℂ) = w + (-(i : ℂ)) * (β : ℂ) := by ring
      rw [harg] at hstep
      have hstep2 : hInv (w + (-(i : ℂ) - 1) * (β : ℂ))
          = hInv (w + (-(i : ℂ)) * (β : ℂ)) - 2 * (Real.pi : ℂ) * I := by rw [hstep]; ring
      rw [hstep2, ih]; ring
  set Finv : ℂ → ℂ := fun ξ => Complex.exp (hInv (halfToStrip (|β| / 2) ξ)) with hFinvdef
  have hFinv_mem : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 → Finv ξ ∈ A \ closedBall 0 1 := by
    intro ξ hξ0 hξ1
    have hw : halfToStrip (|β| / 2) ξ ∈ upperHalf :=
      halfToStrip_mem_upperHalf_of_ne_zero hβabspos hξ0 hξ1
    have hmem : hInv (halfToStrip (|β| / 2) ξ) ∈ expStrip A := hInvconf.mapsTo hw
    rw [← exp_expStrip_eq A]
    exact ⟨_, hmem, rfl⟩
  have hFinv_inj : InjOn Finv puncturedDisc := by
    rintro ξ1 ⟨hξ11, hξ11'⟩ ξ2 ⟨hξ21, hξ21'⟩ heq
    have hξ10 : ξ1 ≠ 0 := norm_pos_iff.mp hξ11
    have hξ20 : ξ2 ≠ 0 := norm_pos_iff.mp hξ21
    have hw1 : halfToStrip (|β| / 2) ξ1 ∈ upperHalf :=
      halfToStrip_mem_upperHalf_of_ne_zero hβabspos hξ10 hξ11'
    have hw2 : halfToStrip (|β| / 2) ξ2 ∈ upperHalf :=
      halfToStrip_mem_upperHalf_of_ne_zero hβabspos hξ20 hξ21'
    have heq' : Complex.exp (hInv (halfToStrip (|β| / 2) ξ1))
        = Complex.exp (hInv (halfToStrip (|β| / 2) ξ2)) := heq
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq'
    have hInv2 := hInv_int (halfToStrip (|β| / 2) ξ2) hw2 m
    have hXim : ((m : ℂ) * (β : ℂ)).im = 0 := by rw [Complex.mul_im]; simp
    have hmem2 : halfToStrip (|β| / 2) ξ2 + (m : ℂ) * (β : ℂ) ∈ upperHalf := by
      show 0 < (halfToStrip (|β| / 2) ξ2 + (m : ℂ) * (β : ℂ)).im
      rw [Complex.add_im, hXim, add_zero]; exact hw2
    have hval : hInv (halfToStrip (|β| / 2) ξ2 + (m : ℂ) * (β : ℂ))
        = hInv (halfToStrip (|β| / 2) ξ1) := by rw [hInv2, ← hm]
    have hPeq : halfToStrip (|β| / 2) ξ2 + (m : ℂ) * (β : ℂ) = halfToStrip (|β| / 2) ξ1 :=
      hInvconf.2.1 hmem2 hw1 hval
    have hstA : stripToHalf (|β| / 2) (halfToStrip (|β| / 2) ξ1) = ξ1 :=
      stripToHalf_halfToStrip hβabspos hξ10
    have hstA2 : stripToHalf (|β| / 2) (halfToStrip (|β| / 2) ξ2) = ξ2 :=
      stripToHalf_halfToStrip hβabspos hξ20
    rw [← hPeq, stripToHalf_add, hstA2, stripToHalf_int_beta_eq_one hβne0, mul_one] at hstA
    exact hstA.symm
  have hFinv_diff : ∀ ξ₀ ∈ puncturedDisc, DifferentiableAt ℂ Finv ξ₀ := by
    intro ξ₀ hξ₀
    have hξ₀0 : ξ₀ ≠ 0 := norm_pos_iff.mp hξ₀.1
    set θ : ℝ := ξ₀.arg with hθdef
    have hrot0 : Complex.exp (-I * (θ : ℂ)) * ξ₀ = (‖ξ₀‖ : ℂ) := rotate_self_eq_norm ξ₀ hξ₀0
    have hξ₀_slit : Complex.exp (-I * (θ : ℂ)) * ξ₀ ∈ Complex.slitPlane := by
      rw [hrot0]; exact Or.inl (by exact_mod_cast norm_pos_iff.mpr hξ₀0)
    set V : Set ℂ :=
        {ζ : ℂ | Complex.exp (-I * (θ : ℂ)) * ζ ∈ Complex.slitPlane} ∩ {ζ : ℂ | ζ ≠ 0} ∩
          {ζ : ℂ | ‖ζ‖ < 1} with hVdef
    have hVo : IsOpen V :=
      ((isOpen_rotSet θ).inter isOpen_ne).inter (isOpen_lt continuous_norm continuous_const)
    have hξ₀V : ξ₀ ∈ V := ⟨⟨hξ₀_slit, hξ₀0⟩, hξ₀.2⟩
    set scaledLocal : ℝ → ℂ → ℂ := fun θ' ζ => ((|β| / 2 / Real.pi : ℝ) : ℂ) * (-I) *
      localLogBranch θ' ζ with hscaledLocaldef
    have heq_on_V : ∀ ζ ∈ V, Finv ζ = Complex.exp (hInv (scaledLocal θ ζ)) := by
      intro ζ hζ
      obtain ⟨⟨hζslit, hζ0⟩, hζnorm⟩ := hζ
      have hexpL : Complex.exp (localLogBranch θ ζ) = ζ := exp_localLogBranch hζslit
      have hexplog : Complex.exp (Complex.log ζ) = ζ := Complex.exp_log hζ0
      have hdiffexp : Complex.exp (localLogBranch θ ζ) = Complex.exp (Complex.log ζ) := by
        rw [hexpL, hexplog]
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hdiffexp
      have hζw : halfToStrip (|β| / 2) ζ ∈ upperHalf :=
        halfToStrip_mem_upperHalf_of_ne_zero hβabspos hζ0 hζnorm
      have hkey : scaledLocal θ ζ
          = halfToStrip (|β| / 2) ζ + ((|β| * (n : ℝ) : ℝ) : ℂ) := by
        show ((|β| / 2 / Real.pi : ℝ) : ℂ) * (-I) * localLogBranch θ ζ
          = halfToStrip (|β| / 2) ζ + ((|β| * (n : ℝ) : ℝ) : ℂ)
        rw [hn, halfToStrip]
        push_cast
        field_simp
        linear_combination (-2 : ℂ) * (|β| : ℝ) * (Real.pi : ℝ) * (n : ℤ) * Complex.I_sq
      show Complex.exp (hInv (halfToStrip (|β| / 2) ζ)) = Complex.exp (hInv (scaledLocal θ ζ))
      rw [hkey, exp_hInv_shift_abs_beta hβne0 hInv_int hζw]
    have hLmem0 : scaledLocal θ ξ₀ ∈ upperHalf := by
      have hζw : halfToStrip (|β| / 2) ξ₀ ∈ upperHalf :=
        halfToStrip_mem_upperHalf_of_ne_zero hβabspos hξ₀0 hξ₀.2
      have hexpL : Complex.exp (localLogBranch θ ξ₀) = ξ₀ := exp_localLogBranch hξ₀_slit
      have hexplog : Complex.exp (Complex.log ξ₀) = ξ₀ := Complex.exp_log hξ₀0
      have hdiffexp : Complex.exp (localLogBranch θ ξ₀) = Complex.exp (Complex.log ξ₀) := by
        rw [hexpL, hexplog]
      obtain ⟨n0, hn0⟩ := Complex.exp_eq_exp_iff_exists_int.mp hdiffexp
      have hkey : scaledLocal θ ξ₀ = halfToStrip (|β| / 2) ξ₀ + ((|β| * (n0 : ℝ) : ℝ) : ℂ) := by
        show ((|β| / 2 / Real.pi : ℝ) : ℂ) * (-I) * localLogBranch θ ξ₀
          = halfToStrip (|β| / 2) ξ₀ + ((|β| * (n0 : ℝ) : ℝ) : ℂ)
        rw [hn0, halfToStrip]
        push_cast
        field_simp
        linear_combination (-2 : ℂ) * (|β| : ℝ) * (Real.pi : ℝ) * (n0 : ℤ) * Complex.I_sq
      rw [hkey]
      show 0 < (halfToStrip (|β| / 2) ξ₀ + ((|β| * (n0 : ℝ) : ℝ) : ℂ)).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact hζw
    have hUpperHalfOpen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
    have hdiff_local : DifferentiableAt ℂ (fun ζ => Complex.exp (hInv (scaledLocal θ ζ))) ξ₀ := by
      have hL : DifferentiableAt ℂ (localLogBranch θ) ξ₀ :=
        differentiableAt_localLogBranch hξ₀_slit
      have hscaled : DifferentiableAt ℂ (scaledLocal θ) ξ₀ := by
        show DifferentiableAt ℂ
          (fun ζ => ((|β| / 2 / Real.pi : ℝ) : ℂ) * (-I) * localLogBranch θ ζ) ξ₀
        exact (differentiableAt_const _).mul hL
      have hInvdiff : DifferentiableAt ℂ hInv (scaledLocal θ ξ₀) :=
        hInvconf.1.differentiableAt (hUpperHalfOpen.mem_nhds hLmem0)
      have hcomp : DifferentiableAt ℂ (fun ζ => hInv (scaledLocal θ ζ)) ξ₀ :=
        hInvdiff.comp ξ₀ hscaled
      exact Complex.differentiable_exp.differentiableAt.comp ξ₀ hcomp
    have heqf : Finv =ᶠ[𝓝 ξ₀] (fun ζ => Complex.exp (hInv (scaledLocal θ ζ))) :=
      Filter.eventuallyEq_of_mem (hVo.mem_nhds hξ₀V) heq_on_V
    exact (Filter.EventuallyEq.differentiableAt_iff heqf).2 hdiff_local
  have hFinv_surj : ∀ ζ ∈ A \ closedBall 0 1, ∃ ξ ∈ puncturedDisc, Finv ξ = ζ := by
    intro ζ hζ
    obtain ⟨z, hzmem, hzeq⟩ : ζ ∈ Complex.exp '' expStrip A := by
      rw [exp_expStrip_eq A]; exact hζ
    set w : ℂ := h z with hwdef
    have hw : w ∈ upperHalf := hhconf.mapsTo hzmem
    have hzinv : hInv w = z := hhconf.2.1.leftInvOn_invFunOn hzmem
    set ξ : ℂ := stripToHalf (|β| / 2) w with hξdef
    have hξ0 : ξ ≠ 0 := stripToHalf_ne_zero _ _
    have hξ1 : ‖ξ‖ < 1 := by
      show ‖stripToHalf (|β| / 2) w‖ < 1
      rw [norm_stripToHalf']
      have hwim : 0 < w.im := hw
      have : (0:ℝ) < Real.pi / (|β| / 2) * w.im := mul_pos (div_pos Real.pi_pos hβabspos) hwim
      calc Real.exp (-(Real.pi / (|β| / 2)) * w.im) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hround : stripToHalf (|β| / 2) (halfToStrip (|β| / 2) ξ) = ξ :=
      stripToHalf_halfToStrip hβabspos hξ0
    have heq2 : stripToHalf (|β| / 2) (halfToStrip (|β| / 2) ξ)
        = stripToHalf (|β| / 2) w := by rw [hround]
    have heq2' : Complex.exp (I * (halfToStrip (|β| / 2) ξ) * (Real.pi / (|β| / 2) : ℝ))
        = Complex.exp (I * w * (Real.pi / (|β| / 2) : ℝ)) := heq2
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq2'
    have hπne : (Real.pi / (|β| / 2) : ℝ) ≠ 0 := by positivity
    have hπneC : ((Real.pi / (|β| / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπne
    have hshift : halfToStrip (|β| / 2) ξ = w + ((|β| * (m : ℝ) : ℝ) : ℂ) := by
      have hβ2ne : (|β| / 2 : ℝ) ≠ 0 := hβabspos.ne'
      have hβabsne : (|β| : ℝ) ≠ 0 := abs_ne_zero.mpr hβne0
      have hstep : ((|β| / 2 / Real.pi : ℝ) : ℂ) * (I * halfToStrip (|β| / 2) ξ *
            (Real.pi / (|β| / 2) : ℝ))
          = ((|β| / 2 / Real.pi : ℝ) : ℂ) *
            (I * w * (Real.pi / (|β| / 2) : ℝ) + (m : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
        rw [hm]
      have hlhs : ((|β| / 2 / Real.pi : ℝ) : ℂ) * (I * halfToStrip (|β| / 2) ξ *
            (Real.pi / (|β| / 2) : ℝ)) = I * halfToStrip (|β| / 2) ξ := by
        push_cast
        field_simp [hβabsne]
      have hrhs : ((|β| / 2 / Real.pi : ℝ) : ℂ) *
            (I * w * (Real.pi / (|β| / 2) : ℝ) + (m : ℂ) * (2 * (Real.pi : ℂ) * I))
          = I * w + I * ((|β| * (m : ℝ) : ℝ) : ℂ) := by
        push_cast
        field_simp [hβabsne]
      rw [hlhs, hrhs] at hstep
      have hI : I ≠ 0 := Complex.I_ne_zero
      apply mul_left_cancel₀ hI
      linear_combination hstep
    refine ⟨ξ, ⟨norm_pos_iff.mpr hξ0, hξ1⟩, ?_⟩
    show Complex.exp (hInv (halfToStrip (|β| / 2) ξ)) = ζ
    rw [hshift, exp_hInv_shift_abs_beta hβne0 hInv_int hw, hzinv, ← hzeq]
  obtain ⟨R, hR⟩ := hAbdd.subset_closedBall (0 : ℂ)
  have hRnonneg : (0:ℝ) ≤ R := by
    have h0A : (0:ℂ) ∈ A := hball (mem_closedBall_self (by norm_num))
    have := hR h0A
    rwa [mem_closedBall_zero_iff, norm_zero] at this
  have hPD : ball (0 : ℂ) 1 \ {0} = puncturedDisc := by
    ext z
    simp only [mem_diff, mem_ball_zero_iff, mem_singleton_iff, puncturedDisc, annulus,
      mem_setOf_eq, norm_pos_iff]
    tauto
  have hsub : puncturedDisc ⊆ ball (0 : ℂ) 1 := by rw [← hPD]; exact diff_subset
  have hball1 : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  have hFinvDon : DifferentiableOn ℂ Finv puncturedDisc := fun x hx =>
    (hFinv_diff x hx).differentiableWithinAt
  have hbdd' : BddAbove (norm ∘ Finv '' (ball (0 : ℂ) 1 \ {0})) := by
    refine ⟨R, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hPD] at hz
    have hzA := (hFinv_mem z (norm_pos_iff.mp hz.1) hz.2).1
    have := hR hzA
    rwa [mem_closedBall_zero_iff] at this
  set Fext := Function.update Finv 0 (limUnder (𝓝[≠] (0 : ℂ)) Finv) with hFextdef
  have hFextd : DifferentiableOn ℂ Fext (ball 0 1) :=
    differentiableOn_update_limUnder_of_bddAbove hball1 (by rwa [hPD]) hbdd'
  have hFextF : ∀ ζ ∈ puncturedDisc, Fext ζ = Finv ζ := fun ζ hζ => by
    rw [← hPD] at hζ
    exact Function.update_of_ne (mem_singleton_iff.not.1 hζ.2) _ _
  have hnear : ∀ s ⊆ ball (0 : ℂ) 1, ∀ w ∈ Fext '' s, w ≠ Fext 0 →
      ∃ u ∈ s, u ∈ puncturedDisc ∧ Finv u = w := by
    rintro s hs w ⟨u, hu, rfl⟩ hne
    have hu0 : u ≠ 0 := by rintro rfl; exact hne rfl
    have hu' : u ∈ puncturedDisc := by
      rw [← hPD]; exact ⟨hs hu, mem_singleton_iff.not.2 hu0⟩
    exact ⟨u, hu, hu', (hFextF u hu').symm⟩
  have hga : AnalyticOnNhd ℂ Fext (ball 0 1) := hFextd.analyticOnNhd isOpen_ball
  rcases hga.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨wc, hwc⟩ | hopen
  · have hm₁ : (1 / 2 : ℂ) ∈ puncturedDisc := by norm_num [puncturedDisc, annulus]
    have hm₂ : (-(1 / 2) : ℂ) ∈ puncturedDisc := by norm_num [puncturedDisc, annulus]
    have e : Finv (1 / 2) = Finv (-(1 / 2)) := by
      rw [← hFextF _ hm₁, ← hFextF _ hm₂, hwc _ (hsub hm₁), hwc _ (hsub hm₂)]
    have := hFinv_inj hm₁ hm₂ e
    norm_num at this
  by_cases hcA : Fext 0 ∈ A \ closedBall 0 1
  · obtain ⟨z₁, hz₁, hfz₁⟩ := hFinv_surj (Fext 0) hcA
    have hz₁0 : 0 < ‖z₁‖ := hz₁.1
    have hz₁1 : ‖z₁‖ < 1 := hz₁.2
    set ρ := ‖z₁‖ / 2 with hρ
    have hρ0 : 0 < ρ := half_pos hz₁0
    have hs₀ : ball (0 : ℂ) ρ ⊆ ball 0 1 := ball_subset_ball (by linarith)
    have hs₁ : ball z₁ ρ ∩ ball 0 1 ⊆ ball 0 1 := inter_subset_right
    have hdisj : ∀ u ∈ ball (0 : ℂ) ρ, u ∉ ball z₁ ρ := by
      intro u hu hu'
      rw [mem_ball_zero_iff] at hu
      rw [mem_ball, dist_eq_norm] at hu'
      have := norm_sub_norm_le z₁ u
      rw [norm_sub_rev] at this
      linarith
    have hW : Fext '' ball (0 : ℂ) ρ ∩ Fext '' (ball z₁ ρ ∩ ball 0 1) ∈ 𝓝 (Fext 0) := by
      refine inter_mem ((hopen _ hs₀ isOpen_ball).mem_nhds
        (mem_image_of_mem Fext (mem_ball_self hρ0))) ?_
      exact (hopen _ hs₁ (isOpen_ball.inter isOpen_ball)).mem_nhds
        ⟨z₁, ⟨mem_ball_self hρ0, hsub hz₁⟩, (hFextF z₁ hz₁).trans hfz₁⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
    have hwmem : Fext 0 + ((ε / 2 : ℝ) : ℂ) ∈ ball (Fext 0) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hwne : Fext 0 + ((ε / 2 : ℝ) : ℂ) ≠ Fext 0 := by
      intro heqc
      have h' : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination heqc
      exact (half_pos hε).ne' (by exact_mod_cast h')
    obtain ⟨hw₀, hw₁⟩ := hεW hwmem
    obtain ⟨u₀, hu₀, hu₀', hfu₀⟩ := hnear _ hs₀ _ hw₀ hwne
    obtain ⟨u₁, hu₁, hu₁', hfu₁⟩ := hnear _ hs₁ _ hw₁ hwne
    have e := hFinv_inj hu₀' hu₁' (hfu₀.trans hfu₁.symm)
    subst e
    exact hdisj u₀ hu₀ hu₁.1
  · by_cases hcB : Fext 0 ∈ closedBall (0 : ℂ) 1
    · have hV : Fext '' ball (0 : ℂ) 1 ∈ 𝓝 (Fext 0) :=
        (hopen _ subset_rfl isOpen_ball).mem_nhds (mem_image_of_mem Fext (mem_ball_self one_pos))
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
      have hn1 : ‖Fext 0‖ ≤ 1 := by rwa [mem_closedBall_zero_iff] at hcB
      obtain ⟨w, hwball, hwlt1, hwne⟩ : ∃ w, w ∈ ball (Fext 0) ε ∧ ‖w‖ < 1 ∧ w ≠ Fext 0 := by
        by_cases hz0 : Fext 0 = 0
        · refine ⟨((min (ε / 2) (1 / 2) : ℝ) : ℂ), ?_, ?_, ?_⟩
          · rw [mem_ball, hz0, dist_eq_norm, sub_zero, norm_real, Real.norm_eq_abs,
              abs_of_pos (lt_min (half_pos hε) (by norm_num : (0:ℝ) < 1 / 2))]
            calc min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
              _ < ε := half_lt_self hε
          · rw [norm_real, Real.norm_eq_abs,
              abs_of_pos (lt_min (half_pos hε) (by norm_num : (0:ℝ) < 1 / 2))]
            calc min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
              _ < 1 := by norm_num
          · rw [hz0]
            intro hc0
            have : (min (ε / 2) (1 / 2) : ℝ) = 0 := by exact_mod_cast hc0
            have hpos : (0:ℝ) < min (ε / 2) (1 / 2) :=
              lt_min (half_pos hε) (by norm_num)
            linarith
        · have hn0 : 0 < ‖Fext 0‖ := norm_pos_iff.2 hz0
          set δ : ℝ := min (1 / 2) (ε / (2 * ‖Fext 0‖)) with hδ
          have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
          have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
          refine ⟨Fext 0 * ((1 - δ : ℝ) : ℂ), ?_, ?_, ?_⟩
          · rw [mem_ball, dist_eq_norm,
              show Fext 0 * ((1 - δ : ℝ) : ℂ) - Fext 0 = -(Fext 0 * ((δ : ℝ) : ℂ)) by
                push_cast; ring,
              norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
            calc ‖Fext 0‖ * δ ≤ ‖Fext 0‖ * (ε / (2 * ‖Fext 0‖)) := by
                  gcongr; exact min_le_right _ _
              _ = ε / 2 := by field_simp
              _ < ε := half_lt_self hε
          · rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - δ)]
            nlinarith [hn1, hδ0]
          · intro heqc
            have : Fext 0 * ((δ:ℝ):ℂ) = 0 := by
              have := heqc
              push_cast at this ⊢
              linear_combination -this
            rcases mul_eq_zero.1 this with h1 | h2
            · exact hz0 h1
            · have : (δ:ℝ) = 0 := by exact_mod_cast h2
              linarith
      obtain ⟨u, -, hu', hfu⟩ := hnear _ subset_rfl _ (hεV hwball) hwne
      have := (hFinv_mem u (norm_pos_iff.mp hu'.1) hu'.2).2
      rw [mem_closedBall_zero_iff] at this
      rw [hfu] at this
      linarith
    · have hcAc : Fext 0 ∈ Aᶜ := by
        intro hmemA
        by_cases hin : Fext 0 ∈ closedBall (0 : ℂ) 1
        · exact hcB hin
        · exact hcA ⟨hmemA, hin⟩
      have hV : Fext '' ball (0 : ℂ) 1 ∈ 𝓝 (Fext 0) :=
        (hopen _ subset_rfl isOpen_ball).mem_nhds (mem_image_of_mem Fext (mem_ball_self one_pos))
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
      have hisolated : ball (Fext 0) ε \ {Fext 0} ⊆ A := by
        rintro w ⟨hwball, hwne⟩
        rw [mem_singleton_iff] at hwne
        obtain ⟨u, -, hu', hfu⟩ := hnear _ subset_rfl _ (hεV hwball) hwne
        rw [← hfu]
        exact (hFinv_mem u (norm_pos_iff.mp hu'.1) hu'.2).1
      set p := Fext 0 with hpdef
      have hq : ∃ q : ℂ, q ∈ Aᶜ ∧ ε / 2 < dist q p := by
        refine ⟨((R + ‖p‖ + ε + 1 : ℝ) : ℂ), ?_, ?_⟩
        · intro hqA
          have := hR hqA
          rw [mem_closedBall_zero_iff, norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < R + ‖p‖ + ε + 1)] at this
          linarith [norm_nonneg p, hε]
        · rw [dist_eq_norm]
          have h1 : ‖((R + ‖p‖ + ε + 1 : ℝ) : ℂ)‖ - ‖p‖ ≤ ‖((R + ‖p‖ + ε + 1 : ℝ) : ℂ) - p‖ :=
            norm_sub_norm_le _ _
          rw [norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < R + ‖p‖ + ε + 1)] at h1
          linarith [hRnonneg]
      obtain ⟨q, hqAc, hqdist⟩ := hq
      have hsep : (Aᶜ ∩ (ball p ε ∩ (closedBall p (ε / 2))ᶜ)).Nonempty := by
        have huv : Aᶜ ⊆ ball p ε ∪ (closedBall p (ε / 2))ᶜ := by
          intro z hz
          by_cases hzε : dist z p < ε
          · exact Or.inl hzε
          · exact Or.inr (fun hzc => hzε (lt_of_le_of_lt
              (mem_closedBall.mp hzc) (by linarith [half_lt_self hε])))
        have hu' : (Aᶜ ∩ ball p ε).Nonempty := ⟨p, hcAc, mem_ball_self hε⟩
        have hv' : (Aᶜ ∩ (closedBall p (ε / 2))ᶜ).Nonempty := ⟨q, hqAc, by
          rw [mem_compl_iff, mem_closedBall]
          intro hcon
          linarith [hqdist]⟩
        have hprec : IsPreconnected Aᶜ := hAcompl.isConnected.isPreconnected
        have := hprec (ball p ε) (closedBall p (ε / 2))ᶜ isOpen_ball
          (isOpen_compl_iff.2 isClosed_closedBall) huv hu' hv'
        simpa [inter_assoc] using this
      obtain ⟨z, hzAc, hzball, hzv⟩ := hsep
      have hzin : z ∈ A := by
        have hzne : z ≠ p := by
          intro hzeq
          apply hzv
          rw [mem_closedBall, hzeq, dist_self]
          linarith
        exact hisolated ⟨hzball, mem_singleton_iff.not.2 hzne⟩
      exact hzAc hzin

/-! ## Part 15: the rotation reduction, general root `p` down to `parabolic_excluded_at_one` -/

theorem isConformalOnto_rotation {c : ℂ} (hc : ‖c‖ = 1) :
    IsConformalOnto (fun z => c * z) unitDisc unitDisc := by
  have hcne : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hcc' : c * conj c = 1 := by
    have hns : Complex.normSq c = 1 := by rw [← Complex.sq_norm, hc]; norm_num
    have h2 := Complex.mul_conj c
    rw [hns] at h2; simpa using h2
  refine ⟨by fun_prop, ?_, ?_⟩
  · intro x _ y _ hxy
    exact mul_left_cancel₀ hcne hxy
  · ext z
    simp only [Set.mem_image, unitDisc, mem_ball_zero_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [norm_mul, hc, one_mul]
    · intro hz
      refine ⟨conj c * z, ?_, ?_⟩
      · rw [norm_mul, Complex.norm_conj, hc, one_mul]; exact hz
      · rw [show c * (conj c * z) = (c * conj c) * z from by ring, hcc']; ring

theorem blaschke_rotate {a p ζ : ℂ} (hp : ‖p‖ = 1) :
    blaschke a (p * ζ) = p * blaschke (a / p) ζ := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hpp : p * conj p = 1 := by
    have hns : Complex.normSq p = 1 := by rw [← Complex.sq_norm, hp]; norm_num
    have h2 := Complex.mul_conj p
    rw [hns] at h2; simpa using h2
  have hcpne : conj p ≠ 0 := by intro h; rw [h] at hpp; simp at hpp
  have hconjap : conj (a / p) = conj a * p := by
    rw [map_div₀, div_eq_iff hcpne]
    linear_combination (-(conj a)) * hpp
  simp only [blaschke, hconjap]
  field_simp

theorem parabolic_excluded {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ} (hd : 0 < d) (hAo : IsOpen A)
    (hg : IsConformalOnto g (expStrip A) (strip d))
    (hAbdd : Bornology.IsBounded A) (hball : closedBall 0 1 ⊆ A) (hAcompl : IsPathConnected Aᶜ)
    {c a p : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (heqOn : EqOn (deckH_disc A d g) (fun z => c * blaschke a z) unitDisc)
    (hparab : c = 1 - 2 * conj a * p) : False := by
  have hpne : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hpconjp : p * conj p = 1 := by
    have hns : Complex.normSq p = 1 := by rw [← Complex.sq_norm, hp]; norm_num
    have h2 := Complex.mul_conj p
    rw [hns] at h2; simpa using h2
  have hconjpp : conj p * p = 1 := by rw [mul_comm]; exact hpconjp
  have hconjpnorm : ‖conj p‖ = 1 := by rw [Complex.norm_conj]; exact hp
  set R : ℂ → ℂ := fun z => conj p * z with hRdef
  set Rinv : ℂ → ℂ := fun z => p * z with hRinvdef
  have hRconf : IsConformalOnto R unitDisc unitDisc := isConformalOnto_rotation hconjpnorm
  have hRinvconf : IsConformalOnto Rinv unitDisc unitDisc := isConformalOnto_rotation hp
  have hRRinv : ∀ z, R (Rinv z) = z := fun z => by
    show conj p * (p * z) = z
    rw [show conj p * (p * z) = (conj p * p) * z from by ring, hconjpp]; ring
  have hRinvR : ∀ z, Rinv (R z) = z := fun z => by
    show p * (conj p * z) = z
    rw [show p * (conj p * z) = (p * conj p) * z from by ring, hpconjp]; ring
  set T : ℂ → ℂ := stripDiscInv d ∘ R ∘ stripDisc d with hTdef
  set Tinv : ℂ → ℂ := stripDiscInv d ∘ Rinv ∘ stripDisc d with hTinvdef
  have hTconf : IsConformalOnto T (strip d) (strip d) :=
    (isConformalOnto_stripDiscInv hd).comp (hRconf.comp (isConformalOnto_stripDisc hd))
  have hTinvconf : IsConformalOnto Tinv (strip d) (strip d) :=
    (isConformalOnto_stripDiscInv hd).comp (hRinvconf.comp (isConformalOnto_stripDisc hd))
  have hTTinv : ∀ w ∈ strip d, T (Tinv w) = w := by
    intro w hw
    show stripDiscInv d (R (stripDisc d (stripDiscInv d (Rinv (stripDisc d w))))) = w
    have h1 : stripDisc d w ∈ unitDisc := (isConformalOnto_stripDisc hd).mapsTo hw
    have h2 : Rinv (stripDisc d w) ∈ unitDisc := hRinvconf.mapsTo h1
    rw [stripDisc_stripDiscInv hd h2, hRRinv, stripDiscInv_stripDisc hd hw]
  have hTinvT : ∀ w ∈ strip d, Tinv (T w) = w := by
    intro w hw
    show stripDiscInv d (Rinv (stripDisc d (stripDiscInv d (R (stripDisc d w))))) = w
    have h1 : stripDisc d w ∈ unitDisc := (isConformalOnto_stripDisc hd).mapsTo hw
    have h2 : R (stripDisc d w) ∈ unitDisc := hRconf.mapsTo h1
    rw [stripDisc_stripDiscInv hd h2, hRinvR, stripDiscInv_stripDisc hd hw]
  set g_rot : ℂ → ℂ := T ∘ g with hgrotdef
  have hg_rot : IsConformalOnto g_rot (expStrip A) (strip d) := hTconf.comp hg
  have hginvrot : ∀ w ∈ strip d,
      Function.invFunOn g_rot (expStrip A) w = Function.invFunOn g (expStrip A) (Tinv w) := by
    intro w hw
    have hTinvw : Tinv w ∈ strip d := hTinvconf.mapsTo hw
    have h2 : Function.invFunOn g (expStrip A) (Tinv w) ∈ expStrip A :=
      Function.invFunOn_mem (mem_image_of_mem_strip hg hTinvw)
    have h1 : g_rot (Function.invFunOn g (expStrip A) (Tinv w)) = w := by
      show T (g (Function.invFunOn g (expStrip A) (Tinv w))) = w
      rw [Function.invFunOn_eq (mem_image_of_mem_strip hg hTinvw), hTTinv w hw]
    have himg : w ∈ g_rot '' expStrip A := mem_image_of_mem_strip hg_rot hw
    have h3 : g_rot (Function.invFunOn g_rot (expStrip A) w) = w := Function.invFunOn_eq himg
    exact hg_rot.2.1 (Function.invFunOn_mem himg) h2 (h3.trans h1.symm)
  have hdeckHrot : ∀ w ∈ strip d, deckH A g_rot w = T (deckH A g (Tinv w)) := by
    intro w hw
    show g_rot (deckT (Function.invFunOn g_rot (expStrip A) w))
        = T (g (deckT (Function.invFunOn g (expStrip A) (Tinv w))))
    rw [hginvrot w hw]
    rfl
  have heqOn_rot : EqOn (deckH_disc A d g_rot) (fun z => c * blaschke (a / p) z) unitDisc := by
    intro z hz
    show stripDisc d (deckH A g_rot (stripDiscInv d z)) = c * blaschke (a / p) z
    have hzstrip : stripDiscInv d z ∈ strip d := (isConformalOnto_stripDiscInv hd).mapsTo hz
    rw [hdeckHrot (stripDiscInv d z) hzstrip]
    have hTinvz : Tinv (stripDiscInv d z) = stripDiscInv d (Rinv z) := by
      show stripDiscInv d (Rinv (stripDisc d (stripDiscInv d z))) = stripDiscInv d (Rinv z)
      rw [stripDisc_stripDiscInv hd hz]
    rw [hTinvz]
    have hRinvzmem : Rinv z ∈ unitDisc := hRinvconf.mapsTo hz
    have hX : stripDisc d (deckH A g (stripDiscInv d (Rinv z))) = deckH_disc A d g (Rinv z) := rfl
    show stripDisc d (T (deckH A g (stripDiscInv d (Rinv z)))) = c * blaschke (a / p) z
    have hTX : T (deckH A g (stripDiscInv d (Rinv z)))
        = stripDiscInv d (R (stripDisc d (deckH A g (stripDiscInv d (Rinv z))))) := rfl
    rw [hTX, hX]
    have hmemD : deckH_disc A d g (Rinv z) ∈ unitDisc :=
      (isConformalOnto_deckH_disc hd hAo hg).mapsTo hRinvzmem
    have hRstepmem : R (deckH_disc A d g (Rinv z)) ∈ unitDisc := hRconf.mapsTo hmemD
    rw [stripDisc_stripDiscInv hd hRstepmem, heqOn hRinvzmem]
    show conj p * (c * blaschke a (p * z)) = c * blaschke (a / p) z
    rw [blaschke_rotate hp]
    rw [show conj p * (c * (p * blaschke (a / p) z))
        = c * ((conj p * p) * blaschke (a / p) z) from by ring, hconjpp]
    ring
  have hparab_rot : c = 1 - 2 * conj (a / p) := by
    have hcpne : conj p ≠ 0 := by intro h; rw [h] at hconjpp; simp at hconjpp
    have hconjap : conj (a / p) = conj a * p := by
      rw [map_div₀, div_eq_iff hcpne]
      linear_combination (-(conj a)) * hpconjp
    rw [hconjap]
    linear_combination hparab
  have hap : ‖a / p‖ < 1 := by rwa [norm_div, hp, div_one]
  exact parabolic_excluded_at_one hd hAo hg_rot hAbdd hball hAcompl hap hc heqOn_rot hparab_rot


/-- **TOP-LEVEL ASSEMBLY (FROZEN STATEMENT).**  Classifies the deck transformation `h` as
hyperbolic (two distinct circle fixed points, handled by `key_construction` /
`key_construction_edge`) or parabolic (one repeated fixed point, EXCLUDED — not yet built,
needs the removable-singularity + open-mapping argument). -/
theorem exists_periodic_of_conformal {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ}
    (hAo : IsOpen A) (hAbdd : Bornology.IsBounded A) (hball : closedBall 0 1 ⊆ A)
    (hAcompl : IsPathConnected Aᶜ) (hd : 0 < d)
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    ∃ (g' : ℂ → ℂ) (s : ℝ), IsConformalOnto g' (expStrip A) (strip d) ∧ 0 < s ∧
      ∀ z ∈ expStrip A, g' (z + 2 * (Real.pi : ℂ) * I) = g' z + (s : ℂ) * I := by
  obtain ⟨c, a, hc, ha, heqOn⟩ := exists_blaschke_deckH_disc hd hAo hg
  have hcne : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have haz : a ≠ 0 := a_ne_zero_of_deckH_disc hd hAo hg heqOn
  obtain ⟨p, hp⟩ := exists_fixedPointPoly_root haz
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp only [fixedPointPoly] at hp
    have hca : c * a = 0 := by linear_combination -hp
    rcases mul_eq_zero.1 hca with h | h
    · exact hcne h
    · exact haz h
  set q := (1 - c) / conj a - p with hqdef
  have hq : fixedPointPoly c a q = 0 := other_root_eq_zero haz hp
  by_cases hpq : p = q
  · -- **PARABOLIC case** (repeated fixed point): EXCLUDED via `parabolic_excluded`.
    have hpn : ‖p‖ = 1 := norm_eq_one_of_fixedPointPoly_eq_zero hd hAo hg hc ha heqOn hp0 hp
    have haconj : conj a ≠ 0 := fun h => haz (by simpa using congrArg conj h)
    have hparab : c = 1 - 2 * conj a * p := by
      have hpq' : p = (1 - c) / conj a - p := hqdef ▸ hpq
      field_simp [haconj] at hpq'
      linear_combination hpq'
    exact (parabolic_excluded hd hAo hg hAbdd hball hAcompl ha hc hpn heqOn hparab).elim
  · have hq0 : q ≠ 0 := by
      intro h0
      rw [h0] at hq
      simp only [fixedPointPoly] at hq
      have hca : c * a = 0 := by linear_combination -hq
      rcases mul_eq_zero.1 hca with h | h
      · exact hcne h
      · exact haz h
    have hpn : ‖p‖ = 1 := norm_eq_one_of_fixedPointPoly_eq_zero hd hAo hg hc ha heqOn hp0 hp
    have hqn : ‖q‖ = 1 := norm_eq_one_of_fixedPointPoly_eq_zero hd hAo hg hc ha heqOn hq0 hq
    have hpfix : c * blaschke a p = p := (deckH_disc_eq_self_iff_fixedPointPoly ha hpn.le).mpr hp
    have hqfix : c * blaschke a q = q := (deckH_disc_eq_self_iff_fixedPointPoly ha hqn.le).mpr hq
    by_cases hp1 : p = 1
    · have hq1 : q ≠ 1 := by rw [← hp1]; exact Ne.symm hpq
      obtain ⟨r', hr'eq⟩ : ∃ r' : ℝ, stripCayleyInv q = (r' : ℂ) :=
        real_of_conj_eq (conj_stripCayleyInv_eq hqn hq1)
      have h1fix : c * blaschke a 1 = 1 := by rw [← hp1]; exact hpfix
      exact key_construction_edge hd hAo hg hc ha heqOn h1fix hqn hq1 hqfix hr'eq
    · by_cases hq1 : q = 1
      · have hp1' : p ≠ 1 := by rw [← hq1]; exact hpq
        obtain ⟨r', hr'eq⟩ : ∃ r' : ℝ, stripCayleyInv p = (r' : ℂ) :=
          real_of_conj_eq (conj_stripCayleyInv_eq hpn hp1')
        have h1fix : c * blaschke a 1 = 1 := by rw [← hq1]; exact hqfix
        exact key_construction_edge hd hAo hg hc ha heqOn h1fix hpn hp1' hpfix hr'eq
      · obtain ⟨p', hp'eq⟩ : ∃ p' : ℝ, stripCayleyInv p = (p' : ℂ) :=
          real_of_conj_eq (conj_stripCayleyInv_eq hpn hp1)
        obtain ⟨q', hq'eq⟩ : ∃ q' : ℝ, stripCayleyInv q = (q' : ℂ) :=
          real_of_conj_eq (conj_stripCayleyInv_eq hqn hq1)
        have hp'q' : p' ≠ q' := by
          intro heq
          apply hpq
          have h1 : stripCayleyInv p = stripCayleyInv q := by rw [hp'eq, hq'eq, heq]
          have e1 := stripCayley_cayleyInv_of_ne_one hp1
          have e2 := stripCayley_cayleyInv_of_ne_one hq1
          rw [← e1, ← e2, h1]
        rcases lt_or_gt_of_ne hp'q' with hlt | hgt
        · exact key_construction hd hAo hg hc ha heqOn hqn hpn hq1 hp1 hqfix hpfix hq'eq hp'eq hlt
        · exact key_construction hd hAo hg hc ha heqOn hpn hqn hp1 hq1 hpfix hqfix hp'eq hq'eq hgt
end LiZhongQC
