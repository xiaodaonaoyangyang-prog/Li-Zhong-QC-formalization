import LiZhongQC.Lemmas.DiscAutomorphism
import LiZhongQC.Lemmas.ExpStripBasic

/-!
# Automorphisms of the vertical strip fix `2πi`-translations (Theorem 2.1 case (iii), piece C)
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## Part 0: end-fixing (frozen; `strip` now in ExpStripBasic) -/

/-- Local copy of `S14_PoincareMetric.isConformalOnto_of_leftInverse` (a Ch-file this leaf
cannot import): a differentiable map with an explicit two-sided inverse on the target/source
sets is conformal onto. -/
theorem stripAux_isConformalOnto_of_leftInverse {D D' : Set ℂ} {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hfmaps : MapsTo f D D') (hgmaps : MapsTo g D' D)
    (hfg : ∀ w ∈ D', f (g w) = w) (hgf : ∀ z ∈ D, g (f z) = z) : IsConformalOnto f D D' := by
  refine ⟨hf, fun z₁ h₁ z₂ h₂ heq => ?_, ?_⟩
  · rw [← hgf z₁ h₁, ← hgf z₂ h₂, heq]
  · exact subset_antisymm (image_subset_iff.2 hfmaps) fun w hw => ⟨g w, hgmaps hw, hfg w hw⟩

def FixesTopEnd (d : ℝ) (f : ℂ → ℂ) : Prop :=
  Tendsto (fun z => (f z).im) (atTop.comap Complex.im ⊓ 𝓟 (strip d)) atTop

def FixesBotEnd (d : ℝ) (f : ℂ → ℂ) : Prop :=
  Tendsto (fun z => (f z).im) (atBot.comap Complex.im ⊓ 𝓟 (strip d)) atBot

/-! ## Part 1: `stripToHalf`/`halfToStrip`, the strip's own biholomorphism onto `upperHalf` -/

/-- `z ↦ exp(iπz/d)` : the strip `{0 < Re z < d}` conformally onto `upperHalf`. -/
def stripToHalf (d : ℝ) (z : ℂ) : ℂ := Complex.exp (I * z * (Real.pi / d : ℝ))

/-- Its inverse on `upperHalf`: `w ↦ (d/(iπ)) log w`. -/
def halfToStrip (d : ℝ) (w : ℂ) : ℂ := (d / Real.pi : ℝ) * (-I) * Complex.log w

theorem stripToHalf_re (d : ℝ) (z : ℂ) :
    (stripToHalf d z).re
      = Real.exp (-(Real.pi / d) * z.im) * Real.cos ((Real.pi / d) * z.re) := by
  have hu_re : (I * z * (Real.pi / d : ℝ)).re = -(Real.pi / d) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  have hu_im : (I * z * (Real.pi / d : ℝ)).im = (Real.pi / d) * z.re := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [stripToHalf, Complex.exp_re, hu_re, hu_im]

theorem stripToHalf_im (d : ℝ) (z : ℂ) :
    (stripToHalf d z).im
      = Real.exp (-(Real.pi / d) * z.im) * Real.sin ((Real.pi / d) * z.re) := by
  have hu_re : (I * z * (Real.pi / d : ℝ)).re = -(Real.pi / d) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  have hu_im : (I * z * (Real.pi / d : ℝ)).im = (Real.pi / d) * z.re := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [stripToHalf, Complex.exp_im, hu_re, hu_im]

theorem stripToHalf_mem_upperHalf {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : z ∈ strip d) :
    stripToHalf d z ∈ upperHalf := by
  show 0 < (stripToHalf d z).im
  rw [stripToHalf_im]
  have hxpos : 0 < (Real.pi / d) * z.re := mul_pos (div_pos Real.pi_pos hd) hz.1
  have hxlt : (Real.pi / d) * z.re < Real.pi := by
    have h2 := hz.2
    calc (Real.pi / d) * z.re < (Real.pi / d) * d :=
          mul_lt_mul_of_pos_left h2 (div_pos Real.pi_pos hd)
      _ = Real.pi := by field_simp
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hxpos hxlt)

theorem stripToHalf_ne_zero (d : ℝ) (z : ℂ) : stripToHalf d z ≠ 0 := Complex.exp_ne_zero _

theorem halfToStrip_stripToHalf {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : z ∈ strip d) :
    halfToStrip d (stripToHalf d z) = z := by
  have hu_im : (I * z * (Real.pi / d : ℝ)).im = (Real.pi / d) * z.re := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  have hbranch1 : -Real.pi < (I * z * (Real.pi / d : ℝ)).im := by
    rw [hu_im]
    have h1 : 0 < (Real.pi / d) * z.re := mul_pos (div_pos Real.pi_pos hd) hz.1
    linarith [Real.pi_pos]
  have hbranch2 : (I * z * (Real.pi / d : ℝ)).im ≤ Real.pi := by
    rw [hu_im]
    have hxlt := hz.2
    have h3 : (Real.pi / d) * z.re < (Real.pi / d) * d :=
      mul_lt_mul_of_pos_left hxlt (div_pos Real.pi_pos hd)
    rw [show (Real.pi / d) * d = Real.pi by field_simp] at h3
    linarith
  rw [halfToStrip, stripToHalf, Complex.log_exp hbranch1 hbranch2]
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpine : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem stripToHalf_halfToStrip {d : ℝ} (hd : 0 < d) {w : ℂ} (hw : w ≠ 0) :
    stripToHalf d (halfToStrip d w) = w := by
  rw [stripToHalf, halfToStrip]
  have heq : I * ((d / Real.pi : ℝ) * (-I) * Complex.log w) * (Real.pi / d : ℝ)
      = Complex.log w := by
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hpine : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  rw [heq, Complex.exp_log hw]

theorem halfToStrip_mem_strip {d : ℝ} (hd : 0 < d) {w : ℂ} (hw : w ∈ upperHalf) :
    halfToStrip d w ∈ strip d := by
  have hwim : 0 < w.im := hw
  have harg_nonneg : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.2 hwim.le
  have harg_ne : Complex.arg w ≠ 0 := by
    intro h
    have := Complex.arg_eq_zero_iff.mp h
    linarith [this.2]
  have harg_pos : 0 < Complex.arg w := harg_nonneg.lt_of_ne (Ne.symm harg_ne)
  have harg_lt : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr hwim.ne')
  show (halfToStrip d w).re ∈ Ioo (0 : ℝ) d
  have hre : (halfToStrip d w).re = (d / Real.pi) * Complex.arg w := by
    rw [halfToStrip]
    have hlogim : (Complex.log w).im = Complex.arg w := Complex.log_im w
    simp [Complex.mul_re, Complex.mul_im, hlogim]
  rw [hre]
  constructor
  · exact mul_pos (div_pos hd Real.pi_pos) harg_pos
  · calc (d / Real.pi) * Complex.arg w < (d / Real.pi) * Real.pi :=
          mul_lt_mul_of_pos_left harg_lt (div_pos hd Real.pi_pos)
      _ = d := by field_simp

theorem isConformalOnto_stripToHalf {d : ℝ} (hd : 0 < d) :
    IsConformalOnto (stripToHalf d) (strip d) upperHalf := by
  refine stripAux_isConformalOnto_of_leftInverse (g := halfToStrip d) ?_ ?_ ?_ ?_ ?_
  · intro z _
    have hd' : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (I * z * (Real.pi / d : ℝ))) z := by
      fun_prop
    exact hd'.differentiableWithinAt
  · exact fun z hz => stripToHalf_mem_upperHalf hd hz
  · exact fun w hw => halfToStrip_mem_strip hd hw
  · intro w hw
    have hwim : 0 < w.im := hw
    have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
    exact stripToHalf_halfToStrip hd hwne
  · exact fun z hz => halfToStrip_stripToHalf hd hz

theorem isConformalOnto_halfToStrip {d : ℝ} (hd : 0 < d) :
    IsConformalOnto (halfToStrip d) upperHalf (strip d) := by
  refine stripAux_isConformalOnto_of_leftInverse (g := stripToHalf d) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    have hwim : 0 < w.im := hw
    have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
    have harg_lt : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr hwim.ne')
    have hmem : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.mpr ⟨harg_lt.ne, hwne⟩
    have hlogd : DifferentiableAt ℂ Complex.log w := DifferentiableAt.clog differentiableAt_id hmem
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (d / Real.pi : ℝ) * (-I)) w :=
      differentiableAt_const _
    unfold halfToStrip
    exact (hc.mul hlogd).differentiableWithinAt
  · exact fun w hw => halfToStrip_mem_strip hd hw
  · exact fun z hz => stripToHalf_mem_upperHalf hd hz
  · exact fun z hz => halfToStrip_stripToHalf hd hz
  · intro w hw
    have hwim : 0 < w.im := hw
    have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
    exact stripToHalf_halfToStrip hd hwne

/-! ## Part 2: the Cayley transform `upperHalf → unitDisc` (copied from
`Lemmas/ImageQuad.lean:246-312`, renamed `stripCayley*` — `Lemmas/` cannot import the file that
owns the original names, since it would cycle back through `S05 → ... → S02`, and `S02` is where
this leaf itself will be consumed). -/

/-- The Cayley transform `stripCayley z = (z - i)/(z + i)`, upper half-plane to unit disc. -/
def stripCayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `stripCayleyInv w = i(1 + w)/(1 - w)`. -/
def stripCayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem stripCayley_den_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro hcon
  have him := congrArg Complex.im hcon
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem stripCayleyInv_den_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro hcon
  rw [show w = 1 by linear_combination -hcon] at hw
  simp at hw

theorem stripCayleyInv_mem_upperHalf {w : ℂ} (hw : ‖w‖ < 1) : stripCayleyInv w ∈ upperHalf := by
  have hden := stripCayleyInv_den_ne_zero hw
  have hpos : 0 < normSq (1 - w) := normSq_pos.mpr hden
  have hws : normSq w < 1 := normSq_lt_one_iff.mpr hw
  have hval : (stripCayleyInv w).im = (1 - normSq w) / normSq (1 - w) := by
    rw [stripCayleyInv, Complex.div_im]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      normSq_apply]
    field_simp
    ring
  show 0 < (stripCayleyInv w).im
  rw [hval]
  exact div_pos (by linarith) hpos

theorem stripCayley_cayleyInv {w : ℂ} (hw : ‖w‖ < 1) : stripCayley (stripCayleyInv w) = w := by
  have hden := stripCayleyInv_den_ne_zero hw
  have h1 : stripCayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [stripCayleyInv]; field_simp; ring
  have h2 : stripCayleyInv w + I = I * 2 / (1 - w) := by
    rw [stripCayleyInv]; field_simp; ring
  have h2ne : stripCayleyInv w + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [stripCayley, div_eq_iff h2ne, h1, h2]
  field_simp

theorem stripCayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : stripCayleyInv (stripCayley z) = z := by
  have hden := stripCayley_den_ne_zero hz
  have h1 : (1 : ℂ) + stripCayley z = 2 * z / (z + I) := by
    rw [stripCayley]; field_simp; ring
  have h2 : (1 : ℂ) - stripCayley z = 2 * I / (z + I) := by
    rw [stripCayley]; field_simp; ring
  have h2ne : (1 : ℂ) - stripCayley z ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [stripCayleyInv, div_eq_iff h2ne, h1, h2]
  field_simp

theorem stripCayley_mem_unitDisc {z : ℂ} (hz : 0 < z.im) : stripCayley z ∈ unitDisc := by
  have hden := stripCayley_den_ne_zero hz
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  have hlt : normSq (z - I) < normSq (z + I) := by
    have h : normSq (z + I) - normSq (z - I) = 4 * z.im := by
      simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.I_re, Complex.I_im]
      ring
    linarith
  rw [unitDisc, mem_ball_zero_iff, ← normSq_lt_one_iff, stripCayley, normSq_div, div_lt_one hpos]
  exact hlt

theorem isConformalOnto_stripCayley : IsConformalOnto stripCayley upperHalf unitDisc := by
  refine stripAux_isConformalOnto_of_leftInverse (g := stripCayleyInv) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    have hden := stripCayley_den_ne_zero hz
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v - I) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun v : ℂ => v + I) z := by fun_prop
    exact (h1.div h2 hden).differentiableWithinAt
  · exact fun z hz => stripCayley_mem_unitDisc hz
  · exact fun w hw => stripCayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
  · exact fun w hw => stripCayley_cayleyInv (mem_ball_zero_iff.mp hw)
  · exact fun z hz => stripCayleyInv_cayley hz

/-! ## Part 3: `Φ := stripCayley ∘ stripToHalf d`, the strip's biholomorphism onto `unitDisc` -/

def stripDisc (d : ℝ) (z : ℂ) : ℂ := stripCayley (stripToHalf d z)

def stripDiscInv (d : ℝ) (w : ℂ) : ℂ := halfToStrip d (stripCayleyInv w)

theorem isConformalOnto_stripDisc {d : ℝ} (hd : 0 < d) :
    IsConformalOnto (stripDisc d) (strip d) unitDisc :=
  isConformalOnto_stripCayley.comp (isConformalOnto_stripToHalf hd)

theorem isConformalOnto_stripCayleyInv : IsConformalOnto stripCayleyInv unitDisc upperHalf := by
  refine stripAux_isConformalOnto_of_leftInverse (g := stripCayley) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hden := stripCayleyInv_den_ne_zero hwn
    have h1 : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun v : ℂ => (1 : ℂ) - v) w := by fun_prop
    exact (h1.div h2 hden).differentiableWithinAt
  · exact fun w hw => stripCayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
  · exact fun z hz => stripCayley_mem_unitDisc hz
  · exact fun z hz => stripCayleyInv_cayley hz
  · exact fun w hw => stripCayley_cayleyInv (mem_ball_zero_iff.mp hw)

theorem isConformalOnto_stripDiscInv {d : ℝ} (hd : 0 < d) :
    IsConformalOnto (stripDiscInv d) unitDisc (strip d) :=
  (isConformalOnto_halfToStrip hd).comp isConformalOnto_stripCayleyInv

theorem stripDisc_stripDiscInv {d : ℝ} (hd : 0 < d) {w : ℂ} (hw : w ∈ unitDisc) :
    stripDisc d (stripDiscInv d w) = w := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hmem : stripCayleyInv w ∈ upperHalf := stripCayleyInv_mem_upperHalf hwn
  rw [stripDisc, stripDiscInv, stripToHalf_halfToStrip hd (by
    have h0 : 0 < (stripCayleyInv w).im := hmem
    exact fun h => by rw [h] at h0; simp at h0), stripCayley_cayleyInv hwn]

theorem stripDiscInv_stripDisc {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : z ∈ strip d) :
    stripDiscInv d (stripDisc d z) = z := by
  have hmem : stripToHalf d z ∈ upperHalf := stripToHalf_mem_upperHalf hd hz
  rw [stripDiscInv, stripDisc, stripCayleyInv_cayley hmem, halfToStrip_stripToHalf hd hz]

/-! ## Part 4a: the asymptotics of `stripToHalf`/`halfToStrip` at the two ends -/

theorem norm_stripToHalf (d : ℝ) (z : ℂ) :
    ‖stripToHalf d z‖ = Real.exp (-(Real.pi / d) * z.im) := by
  have hu_re : (I * z * (Real.pi / d : ℝ)).re = -(Real.pi / d) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [stripToHalf, Complex.norm_exp, hu_re]

theorem im_halfToStrip (d : ℝ) (w : ℂ) :
    (halfToStrip d w).im = -(d / Real.pi) * Real.log ‖w‖ := by
  have hlogre : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  rw [halfToStrip]
  simp only [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hlogre]
  ring

theorem tendsto_stripToHalf_atTop_nhds_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (stripToHalf d) (atTop.comap Complex.im) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun z => ‖stripToHalf d z‖) = (fun z : ℂ => Real.exp (-(Real.pi / d) * z.im)) := by
    ext z; exact norm_stripToHalf d z
  rw [heq]
  have h1 : Tendsto (fun z : ℂ => -(Real.pi / d) * z.im) (atTop.comap Complex.im) atBot :=
    (tendsto_comap : Tendsto Complex.im (atTop.comap Complex.im) atTop).const_mul_atTop_of_neg
      (by linarith [div_pos Real.pi_pos hd])
  exact Real.tendsto_exp_atBot.comp h1

theorem tendsto_stripToHalf_atBot_norm_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (fun z => ‖stripToHalf d z‖) (atBot.comap Complex.im) atTop := by
  have heq : (fun z => ‖stripToHalf d z‖) = (fun z : ℂ => Real.exp (-(Real.pi / d) * z.im)) := by
    ext z; exact norm_stripToHalf d z
  rw [heq]
  have h1 : Tendsto (fun z : ℂ => -(Real.pi / d) * z.im) (atBot.comap Complex.im) atTop :=
    (tendsto_comap : Tendsto Complex.im (atBot.comap Complex.im) atBot).const_mul_atBot_of_neg
      (by linarith [div_pos Real.pi_pos hd])
  exact Real.tendsto_exp_atTop.comp h1

theorem tendsto_halfToStrip_nhdsWithin_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (halfToStrip d) (𝓝[upperHalf] (0 : ℂ))
      (atTop.comap Complex.im ⊓ 𝓟 (strip d)) := by
  refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
  · rw [tendsto_comap_iff]
    have heq : (Complex.im ∘ halfToStrip d) = (fun w : ℂ => -(d / Real.pi) * Real.log ‖w‖) := by
      ext w; exact im_halfToStrip d w
    rw [heq]
    have hnorm : Tendsto (fun w : ℂ => ‖w‖) (𝓝[upperHalf] (0 : ℂ)) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        have hwim : 0 < w.im := hw
        have hwne : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
        exact norm_pos_iff.mpr hwne
    have hlog : Tendsto (fun w : ℂ => Real.log ‖w‖) (𝓝[upperHalf] (0 : ℂ)) atBot :=
      Real.tendsto_log_nhdsGT_zero.comp hnorm
    exact hlog.const_mul_atBot_of_neg (by linarith [div_pos hd Real.pi_pos])
  · apply tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact halfToStrip_mem_strip hd hw

theorem tendsto_halfToStrip_atTop_atBot {d : ℝ} (hd : 0 < d) :
    Tendsto (halfToStrip d) (Filter.comap norm atTop ⊓ 𝓟 upperHalf)
      (atBot.comap Complex.im ⊓ 𝓟 (strip d)) := by
  refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
  · rw [tendsto_comap_iff]
    have heq : (Complex.im ∘ halfToStrip d) = (fun w : ℂ => -(d / Real.pi) * Real.log ‖w‖) := by
      ext w; exact im_halfToStrip d w
    rw [heq]
    have hnorm : Tendsto (fun w : ℂ => ‖w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop :=
      tendsto_inf_left tendsto_comap
    have hlog : Tendsto (fun w : ℂ => Real.log ‖w‖)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop :=
      Real.tendsto_log_atTop.comp hnorm
    exact hlog.const_mul_atTop_of_neg (by linarith [div_pos hd Real.pi_pos])
  · apply tendsto_principal.2
    exact Filter.Eventually.filter_mono inf_le_right
      (Filter.eventually_principal.2 (fun w hw => halfToStrip_mem_strip hd hw))

/-! ## Part 4b: automorphisms of `upperHalf` fixing `0` and `∞` are dilations -/

theorem stripCayley_zero : stripCayley 0 = -1 := by
  rw [stripCayley]; simp

theorem stripCayleyInv_neg_one : stripCayleyInv (-1) = 0 := by
  rw [stripCayleyInv]; norm_num

theorem continuousAt_stripCayley_zero : ContinuousAt stripCayley 0 := by
  have hden : (0 : ℂ) + I ≠ 0 := by simp
  have h1 : ContinuousAt (fun v : ℂ => v - I) (0 : ℂ) := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => v + I) (0 : ℂ) := by fun_prop
  exact h1.div h2 hden

theorem continuousAt_stripCayleyInv_neg_one : ContinuousAt stripCayleyInv (-1) := by
  have hden : (1 : ℂ) - (-1) ≠ 0 := by norm_num
  have h1 : ContinuousAt (fun v : ℂ => I * (1 + v)) (-1 : ℂ) := by fun_prop
  have h2 : ContinuousAt (fun v : ℂ => (1 : ℂ) - v) (-1 : ℂ) := by fun_prop
  exact h1.div h2 hden

theorem stripCayleyInv_eq_mobiusFn : stripCayleyInv = mobiusFn I I (-1) 1 := by
  funext z
  simp only [stripCayleyInv, mobiusFn]
  ring_nf

theorem tendsto_stripCayleyInv_cobounded_of_ne_one :
    Tendsto stripCayleyInv (𝓝[≠] (1 : ℂ)) (cobounded ℂ) := by
  rw [stripCayleyInv_eq_mobiusFn]
  exact tendsto_mobiusFn_pole (by norm_num) (by ring)

theorem stripCayley_eq_mobiusFn : stripCayley = mobiusFn 1 (-I) 1 I := by
  funext z
  simp only [stripCayley, mobiusFn, one_mul, sub_eq_add_neg]

theorem tendsto_stripCayley_cobounded : Tendsto stripCayley (cobounded ℂ) (𝓝 1) := by
  rw [stripCayley_eq_mobiusFn]
  have h := tendsto_mobiusFn_cobounded_of_ne (a := (1 : ℂ)) (b := -I) (d := I) one_ne_zero
  simpa using h

theorem upperHalf_automorphism_eq_dilate {G : ℂ → ℂ}
    (hG : IsConformalOnto G upperHalf upperHalf)
    (hG0 : Tendsto G (𝓝[upperHalf] (0 : ℂ)) (𝓝 0))
    (hGinf : Tendsto (fun w => ‖G w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ upperHalf, G z = (lam : ℂ) * z := by
  set H : ℂ → ℂ := stripCayley ∘ G ∘ stripCayleyInv with hHdef
  have hH : IsConformalOnto H unitDisc unitDisc :=
    isConformalOnto_stripCayley.comp (hG.comp isConformalOnto_stripCayleyInv)
  obtain ⟨c, a, hc1, ha1, heqH⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hH
  -- continuity of `c * blaschke a` on the closed disc (denominator never vanishes there)
  have hden_ne : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (1 : ℂ) - conj a * ζ ≠ 0 := by
    intro ζ hζ hcon
    have h1 : conj a * ζ = 1 := by linear_combination -hcon
    have h2 : ‖conj a * ζ‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_conj] at h2
    have h3 : ‖a‖ * ‖ζ‖ < 1 := by
      calc ‖a‖ * ‖ζ‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hζ (norm_nonneg a)
        _ = ‖a‖ := by ring
        _ < 1 := ha1
    linarith
  have hcont_blaschke : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ContinuousAt (fun ζ => c * blaschke a ζ) ζ := by
    intro ζ hζ
    have hden := hden_ne ζ hζ
    have h1 : ContinuousAt (fun v : ℂ => v - a) ζ := by fun_prop
    have h2 : ContinuousAt (fun v : ℂ => (1 : ℂ) - conj a * v) ζ := by fun_prop
    have h3 : ContinuousAt (blaschke a) ζ := h1.div h2 hden
    exact (continuousAt_const).mul h3
  -- transport `hG0` to `H`'s behaviour at `ζ = -1`
  have htendsto_cayleyInv_neg1 : Tendsto stripCayleyInv (𝓝[unitDisc] (-1 : ℂ)) (𝓝[upperHalf] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have := continuousAt_stripCayleyInv_neg_one.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[unitDisc] (-1 : ℂ) ≤ 𝓝 (-1))
      rwa [stripCayleyInv_neg_one] at this
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact isConformalOnto_stripCayleyInv.mapsTo hζ
  have hH_neg1 : Tendsto H (𝓝[unitDisc] (-1 : ℂ)) (𝓝 (-1 : ℂ)) := by
    have h1 : Tendsto (G ∘ stripCayleyInv) (𝓝[unitDisc] (-1 : ℂ)) (𝓝 0) :=
      hG0.comp htendsto_cayleyInv_neg1
    have h2 : Tendsto stripCayley (𝓝 (0 : ℂ)) (𝓝 (-1 : ℂ)) := by
      have := continuousAt_stripCayley_zero.tendsto
      rwa [stripCayley_zero] at this
    exact h2.comp h1
  have hH_neg1' : Tendsto H (𝓝[unitDisc] (-1 : ℂ)) (𝓝 (c * blaschke a (-1))) := by
    have h1 : Tendsto (fun ζ => c * blaschke a ζ) (𝓝[unitDisc] (-1 : ℂ))
        (𝓝 (c * blaschke a (-1))) :=
      (hcont_blaschke (-1) (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : H =ᶠ[𝓝[unitDisc] (-1 : ℂ)] (fun ζ => c * blaschke a ζ) := by
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact heqH hζ
    exact h1.congr' h2.symm
  have hNeBot1 : (𝓝[unitDisc] (-1 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, unitDisc, closure_ball (0 : ℂ) one_ne_zero]
    simp
  have heq1 : c * blaschke a (-1) = -1 := tendsto_nhds_unique hH_neg1' hH_neg1
  -- symmetric argument at `ζ = 1`, using `hGinf` and the pole of `stripCayleyInv` at `1`
  have hmapsto_one : Tendsto stripCayleyInv (𝓝[unitDisc] (1 : ℂ))
      (Filter.comap norm atTop ⊓ 𝓟 upperHalf) := by
    refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
    · have hsub : unitDisc ⊆ ({1}ᶜ : Set ℂ) := by
        intro z hz hz1
        rw [Set.mem_singleton_iff] at hz1
        rw [hz1] at hz
        simp [unitDisc] at hz
      have h1 : Tendsto stripCayleyInv (𝓝[unitDisc] (1 : ℂ)) (cobounded ℂ) :=
        tendsto_stripCayleyInv_cobounded_of_ne_one.mono_left (nhdsWithin_mono _ hsub)
      rw [← tendsto_norm_atTop_iff_cobounded] at h1
      exact tendsto_comap_iff.2 h1
    · apply tendsto_principal.2
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact isConformalOnto_stripCayleyInv.mapsTo hζ
  have hH_one : Tendsto H (𝓝[unitDisc] (1 : ℂ)) (𝓝 (1 : ℂ)) := by
    have h1 : Tendsto (fun ζ => ‖G (stripCayleyInv ζ)‖) (𝓝[unitDisc] (1 : ℂ)) atTop :=
      hGinf.comp hmapsto_one
    have h2 : Tendsto (G ∘ stripCayleyInv) (𝓝[unitDisc] (1 : ℂ)) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      exact h1
    exact tendsto_stripCayley_cobounded.comp h2
  have hH_one' : Tendsto H (𝓝[unitDisc] (1 : ℂ)) (𝓝 (c * blaschke a 1)) := by
    have h1 : Tendsto (fun ζ => c * blaschke a ζ) (𝓝[unitDisc] (1 : ℂ))
        (𝓝 (c * blaschke a 1)) :=
      (hcont_blaschke 1 (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : H =ᶠ[𝓝[unitDisc] (1 : ℂ)] (fun ζ => c * blaschke a ζ) := by
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact heqH hζ
    exact h1.congr' h2.symm
  have hNeBot2 : (𝓝[unitDisc] (1 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, unitDisc, closure_ball (0 : ℂ) one_ne_zero]
    simp
  have heq2 : c * blaschke a 1 = 1 := tendsto_nhds_unique hH_one' hH_one
  -- solve: `c = 1` and `a` is real
  have hden1 : (1 : ℂ) + conj a ≠ 0 := by
    intro hcon
    have : conj a = -1 := by linear_combination hcon
    have hna : ‖conj a‖ = 1 := by rw [this]; simp
    rw [Complex.norm_conj] at hna
    linarith [ha1]
  have hden2 : (1 : ℂ) - conj a ≠ 0 := by
    intro hcon
    have : conj a = 1 := by linear_combination -hcon
    have hna : ‖conj a‖ = 1 := by rw [this]; simp
    rw [Complex.norm_conj] at hna
    linarith [ha1]
  have heq1' : c * (1 + a) = 1 + conj a := by
    have hb : blaschke a (-1) = -(1 + a) / (1 + conj a) := by
      rw [blaschke]; ring_nf
    rw [hb, mul_div_assoc'] at heq1
    field_simp at heq1
    linear_combination -heq1
  have heq2' : c * (1 - a) = 1 - conj a := by
    have hb : blaschke a 1 = (1 - a) / (1 - conj a) := by
      rw [blaschke]; ring_nf
    rw [hb, mul_div_assoc'] at heq2
    field_simp at heq2
    linear_combination heq2
  have hc_eq : c = 1 := by linear_combination (heq1' + heq2') / 2
  have ha_real : a = conj a := by
    have := heq2'
    rw [hc_eq, one_mul] at this
    linear_combination -this
  have ha_im : a.im = 0 := by
    have h1 := congrArg Complex.im ha_real
    simp only [Complex.conj_im] at h1
    linarith
  set a0 : ℝ := a.re with ha0def
  have ha_eq : a = (a0 : ℂ) := by
    apply Complex.ext
    · simp [ha0def]
    · simp [ha_im]
  have ha0_lt1 : a0 < 1 := by
    have : |a0| < 1 := by
      have h1 : ‖a‖ = |a0| := by rw [ha_eq]; simp
      rw [← h1]; exact ha1
    exact lt_of_abs_lt this
  have ha0_gt : -1 < a0 := by
    have : |a0| < 1 := by
      have h1 : ‖a‖ = |a0| := by rw [ha_eq]; simp
      rw [← h1]; exact ha1
    linarith [abs_lt.mp this |>.1]
  refine ⟨(1 - a0) / (1 + a0), div_pos (by linarith) (by linarith), ?_⟩
  intro z hz
  set w : ℂ := stripCayley z with hwdef
  have hwmem : w ∈ unitDisc := stripCayley_mem_unitDisc hz
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hwmem
  have hstripInv_w : stripCayleyInv w = z := stripCayleyInv_cayley hz
  have hHw : H w = blaschke a w := by
    have h0 := heqH hwmem
    simp only [hc_eq, one_mul] at h0
    exact h0
  have hHw' : H w = stripCayley (G z) := by
    rw [hHdef]
    simp only [Function.comp_apply]
    rw [hwdef, stripCayleyInv_cayley hz]
  have hkey : stripCayley (G z) = blaschke a w := by rw [← hHw', hHw]
  have hGz_mem : G z ∈ upperHalf := hG.mapsTo hz
  have hGz : G z = stripCayleyInv (blaschke a w) := by
    have := congrArg stripCayleyInv hkey
    rwa [stripCayleyInv_cayley hGz_mem] at this
  rw [hGz]
  have hden_bl : (1 : ℂ) - a * w ≠ 0 := by
    intro hcon
    have h1 : a * w = 1 := by linear_combination -hcon
    have h2 : ‖a * w‖ = 1 := by rw [h1]; simp
    rw [norm_mul] at h2
    have h3 : ‖a‖ * ‖w‖ < 1 := by
      calc ‖a‖ * ‖w‖ < 1 * 1 := by
            apply mul_lt_mul'' ha1 hwn (norm_nonneg _) (norm_nonneg _)
        _ = 1 := by ring
    linarith
  have hw1 : (1 : ℂ) + w ≠ 0 := by
    intro hcon
    have : w = -1 := by linear_combination hcon
    rw [this] at hwn; simp at hwn
  have hw2 : (1 : ℂ) - w ≠ 0 := by
    intro hcon
    have : w = 1 := by linear_combination -hcon
    rw [this] at hwn; simp at hwn
  have hp1 : (1 : ℝ) - a0 ≠ 0 := by linarith
  have hp2 : (1 : ℝ) + a0 ≠ 0 := by linarith
  have hp1' : (1 : ℂ) - (a0 : ℂ) ≠ 0 := by exact_mod_cast hp1
  have hp2' : (1 : ℂ) + (a0 : ℂ) ≠ 0 := by exact_mod_cast hp2
  rw [← hstripInv_w]
  rw [ha_eq] at hden_bl ⊢
  have h1plus : (1 : ℂ) + blaschke (a0 : ℂ) w = (1 - (a0 : ℂ)) * (w + 1) / (1 - (a0 : ℂ) * w) := by
    rw [eq_div_iff hden_bl]
    rw [blaschke, Complex.conj_ofReal]
    rw [add_mul, div_mul_cancel₀ _ hden_bl]
    ring
  have h1minus : (1 : ℂ) - blaschke (a0 : ℂ) w = (1 + (a0 : ℂ)) * (1 - w) / (1 - (a0 : ℂ) * w) := by
    rw [eq_div_iff hden_bl]
    rw [blaschke, Complex.conj_ofReal]
    rw [sub_mul, div_mul_cancel₀ _ hden_bl]
    ring
  unfold stripCayleyInv
  rw [h1plus, h1minus]
  push_cast
  field_simp [hden_bl, hp2', hw2]
  ring

/-! ## Part 4c: assembling `strip_automorphism_eq_translate` -/

theorem halfToStrip_lam_mul_stripToHalf {d : ℝ} (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ strip d) :
    halfToStrip d ((lam : ℂ) * stripToHalf d z) = z + (-(d / Real.pi) * Real.log lam : ℝ) * I := by
  have hu_im : (I * z * (Real.pi / d : ℝ)).im = (Real.pi / d) * z.re := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  have hbranch1 : -Real.pi < (I * z * (Real.pi / d : ℝ)).im := by
    rw [hu_im]
    have h1 : 0 < (Real.pi / d) * z.re := mul_pos (div_pos Real.pi_pos hd) hz.1
    linarith [Real.pi_pos]
  have hbranch2 : (I * z * (Real.pi / d : ℝ)).im ≤ Real.pi := by
    rw [hu_im]
    have hxlt := hz.2
    have h3 : (Real.pi / d) * z.re < (Real.pi / d) * d :=
      mul_lt_mul_of_pos_left hxlt (div_pos Real.pi_pos hd)
    rw [show (Real.pi / d) * d = Real.pi by field_simp] at h3
    linarith
  have hlamexp : (lam : ℂ) = Complex.exp (((Real.log lam : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hlam]
  have hkey : (lam : ℂ) * stripToHalf d z
      = Complex.exp (((Real.log lam : ℝ) : ℂ) + I * z * (Real.pi / d : ℝ)) := by
    rw [hlamexp, stripToHalf, ← Complex.exp_add]
  rw [halfToStrip, hkey]
  have hbranch1' : -Real.pi < (((Real.log lam : ℝ) : ℂ) + I * z * (Real.pi / d : ℝ)).im := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact hbranch1
  have hbranch2' : (((Real.log lam : ℝ) : ℂ) + I * z * (Real.pi / d : ℝ)).im ≤ Real.pi := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact hbranch2
  rw [Complex.log_exp hbranch1' hbranch2']
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpine : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination (-(Real.pi : ℂ) * z) * Complex.I_sq

theorem strip_automorphism_eq_translate {d : ℝ} (hd : 0 < d) {f : ℂ → ℂ}
    (hf : IsConformalOnto f (strip d) (strip d))
    (hf_top : FixesTopEnd d f) (hf_bot : FixesBotEnd d f) :
    ∃ t : ℝ, ∀ z ∈ strip d, f z = z + (t : ℂ) * I := by
  set G : ℂ → ℂ := fun w => stripToHalf d (f (halfToStrip d w)) with hGdef
  have hG : IsConformalOnto G upperHalf upperHalf :=
    (isConformalOnto_stripToHalf hd).comp (hf.comp (isConformalOnto_halfToStrip hd))
  have hG0 : Tendsto G (𝓝[upperHalf] (0 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun w => (f (halfToStrip d w)).im) (𝓝[upperHalf] (0 : ℂ)) atTop :=
      hf_top.comp (tendsto_halfToStrip_nhdsWithin_zero hd)
    have h2 : Tendsto (fun w => f (halfToStrip d w)) (𝓝[upperHalf] (0 : ℂ))
        (atTop.comap Complex.im) := tendsto_comap_iff.2 h1
    exact (tendsto_stripToHalf_atTop_nhds_zero hd).comp h2
  have hGinf : Tendsto (fun w => ‖G w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    have h1 : Tendsto (fun w => (f (halfToStrip d w)).im)
        (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atBot :=
      hf_bot.comp (tendsto_halfToStrip_atTop_atBot hd)
    have h2 : Tendsto (fun w => f (halfToStrip d w)) (Filter.comap norm atTop ⊓ 𝓟 upperHalf)
        (atBot.comap Complex.im) := tendsto_comap_iff.2 h1
    exact (tendsto_stripToHalf_atBot_norm_atTop hd).comp h2
  obtain ⟨lam, hlam_pos, hlam⟩ := upperHalf_automorphism_eq_dilate hG hG0 hGinf
  refine ⟨-(d / Real.pi) * Real.log lam, fun z hz => ?_⟩
  have hmem : stripToHalf d z ∈ upperHalf := stripToHalf_mem_upperHalf hd hz
  have h1 : G (stripToHalf d z) = (lam : ℂ) * stripToHalf d z := hlam (stripToHalf d z) hmem
  have h2 : G (stripToHalf d z) = stripToHalf d (f z) := by
    rw [hGdef]
    simp only
    rw [halfToStrip_stripToHalf hd hz]
  rw [h2] at h1
  have h3 : halfToStrip d (stripToHalf d (f z)) = f z := halfToStrip_stripToHalf hd (hf.mapsTo hz)
  rw [h1] at h3
  rw [halfToStrip_lam_mul_stripToHalf hd hlam_pos hz] at h3
  exact h3.symm

theorem strip_automorphism_eq_id_of_fixed {d : ℝ} (hd : 0 < d) {f : ℂ → ℂ}
    (hf : IsConformalOnto f (strip d) (strip d))
    (hf_top : FixesTopEnd d f) (hf_bot : FixesBotEnd d f)
    {z₀ : ℂ} (hz₀ : z₀ ∈ strip d) (hfix : f z₀ = z₀) :
    ∀ z ∈ strip d, f z = z := by
  obtain ⟨t, ht⟩ := strip_automorphism_eq_translate hd hf hf_top hf_bot
  have ht0 : t = 0 := by
    have := ht z₀ hz₀
    rw [hfix] at this
    have h2 : (t : ℂ) * I = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h2 with h | h
    · exact_mod_cast h
    · exact absurd h I_ne_zero
  intro z hz
  rw [ht z hz, ht0]
  simp
end LiZhongQC
