import LiZhongQC.Basic

/-!
# Fractional linear transformations of the extended plane

Auxiliary results used in the proofs (starting with §1):

* `mobiusExt a b c d` agrees with `z ↦ (az+b)/(cz+d)` off the pole, sends the pole to `∞`
  and `∞` to `a/c` (or to `∞` when `c = 0`);
* `mobiusExt d (-b) (-c) a` is its inverse, and `mobiusExt a b c d` is continuous, hence a
  homeomorphism of `ℂ̄` (`mobiusHomeomorph`);
* a Möbius transformation with real coefficients and positive determinant maps the upper
  half-plane conformally onto itself;
* conformal maps compose, and homeomorphic boundary extensions compose with homeomorphisms
  of `ℂ̄`.
-/

open Complex Set Metric Filter Topology Bornology

noncomputable section

namespace LiZhongQC

/-- The formula `z ↦ (a z + b)/(c z + d)`. -/
def mobiusFn (a b c d : ℂ) (z : ℂ) : ℂ := (a * z + b) / (c * z + d)

section Evaluation

variable {a b c d : ℂ}

theorem mobiusExt_coe {z : ℂ} (h : c * z + d ≠ 0) :
    mobiusExt a b c d (z : ExtPlane) = ((mobiusFn a b c d z : ℂ) : ExtPlane) := by
  simp [mobiusExt, mobiusFn, h]

theorem mobiusExt_coe_of_eq_zero {z : ℂ} (h : c * z + d = 0) :
    mobiusExt a b c d (z : ExtPlane) = extInf := by
  simp [mobiusExt, h]

theorem mobiusExt_infty_of_ne (h : c ≠ 0) :
    mobiusExt a b c d extInf = ((a / c : ℂ) : ExtPlane) := by
  simp [mobiusExt, h]

theorem mobiusExt_infty_of_eq (h : c = 0) : mobiusExt a b c d extInf = extInf := by
  simp [mobiusExt, h]

theorem mobiusFn_mul_den {z : ℂ} (hz : c * z + d ≠ 0) :
    mobiusFn a b c d z * (c * z + d) = a * z + b :=
  div_mul_cancel₀ _ hz

theorem mobiusFn_inv_den_eq {z : ℂ} (hz : c * z + d ≠ 0) :
    -c * mobiusFn a b c d z + a = (a * d - b * c) / (c * z + d) := by
  rw [eq_div_iff hz]
  linear_combination (-c) * mobiusFn_mul_den (a := a) (b := b) hz

/-- The denominator of the inverse transformation does not vanish. -/
theorem mobiusFn_inv_den_ne_zero (h : a * d - b * c ≠ 0) {z : ℂ} (hz : c * z + d ≠ 0) :
    -c * mobiusFn a b c d z + a ≠ 0 := by
  rw [mobiusFn_inv_den_eq hz]
  exact div_ne_zero h hz

/-- `z ↦ (dz - b)/(-cz + a)` inverts `z ↦ (az + b)/(cz + d)`. -/
theorem mobiusFn_inv_apply (h : a * d - b * c ≠ 0) {z : ℂ} (hz : c * z + d ≠ 0) :
    mobiusFn d (-b) (-c) a (mobiusFn a b c d z) = z := by
  have e₁ : d * mobiusFn a b c d z + -b = (a * d - b * c) * z / (c * z + d) := by
    rw [eq_div_iff hz]
    linear_combination d * mobiusFn_mul_den (a := a) (b := b) hz
  rw [mobiusFn, e₁, mobiusFn_inv_den_eq hz, div_eq_iff (div_ne_zero h hz)]
  ring

/-- `mobiusExt d (-b) (-c) a` is a left inverse of `mobiusExt a b c d`. -/
theorem mobiusExt_inv_apply (h : a * d - b * c ≠ 0) (w : ExtPlane) :
    mobiusExt d (-b) (-c) a (mobiusExt a b c d w) = w := by
  induction w using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq (neg_eq_zero.mpr hc)]
    · rw [mobiusExt_infty_of_ne hc, mobiusExt_coe_of_eq_zero]
      rw [neg_mul, mul_div_cancel₀ a hc, neg_add_cancel]
  | coe z =>
    by_cases hz : c * z + d = 0
    · have hc : c ≠ 0 := by
        rintro rfl
        apply h
        have hd : d = 0 := by simpa using hz
        simp [hd]
      rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_infty_of_ne (neg_ne_zero.mpr hc)]
      congr 1
      rw [div_eq_iff (neg_ne_zero.mpr hc)]
      linear_combination hz
    · rw [mobiusExt_coe hz, mobiusExt_coe (mobiusFn_inv_den_ne_zero h hz),
        mobiusFn_inv_apply h hz]

end Evaluation

/-! ## Continuity -/

section Continuity

variable {a b c d : ℂ}

theorem tendsto_affine_cobounded {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    Tendsto (fun z : ℂ => c * z + d) (cobounded ℂ) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hlow : ∀ z : ℂ, ‖c‖ * ‖z‖ - ‖d‖ ≤ ‖c * z + d‖ := by
    intro z
    have := norm_sub_norm_le (c * z) (-d)
    simpa [norm_mul, sub_neg_eq_add] using this
  have h1 : Tendsto (fun z : ℂ => ‖c‖ * ‖z‖) (cobounded ℂ) atTop :=
    tendsto_norm_cobounded_atTop.const_mul_atTop (norm_pos_iff.2 hc)
  have h2 : Tendsto (fun z : ℂ => ‖c‖ * ‖z‖ - ‖d‖) (cobounded ℂ) atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-‖d‖) h1
  exact tendsto_atTop_mono hlow h2

theorem tendsto_mobiusFn_cobounded_of_eq_zero (h : a * d - b * c ≠ 0) (hc : c = 0) :
    Tendsto (mobiusFn a b c d) (cobounded ℂ) (cobounded ℂ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    apply h
    simp [hc]
  have ha : a ≠ 0 := by
    rintro rfl
    apply h
    simp [hc]
  have e : mobiusFn a b c d = fun z => (a / d) * z + b / d := by
    funext z
    simp only [mobiusFn, hc, zero_mul, zero_add]
    rw [div_eq_iff hd]
    field_simp
  rw [e]
  exact tendsto_affine_cobounded (div_ne_zero ha hd) _

theorem tendsto_mobiusFn_cobounded_of_ne (hc : c ≠ 0) :
    Tendsto (mobiusFn a b c d) (cobounded ℂ) (𝓝 (a / c)) := by
  have hlin := tendsto_affine_cobounded hc d
  have hinv : Tendsto (fun z : ℂ => (c * z + d)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp hlin
  have hne : ∀ᶠ z in cobounded ℂ, c * z + d ≠ 0 := hlin.eventually (eventually_ne_cobounded 0)
  have heq : (fun z : ℂ => a / c + ((b * c - a * d) / c) * (c * z + d)⁻¹) =ᶠ[cobounded ℂ]
      mobiusFn a b c d := by
    filter_upwards [hne] with z hz
    have hinv' : (c * z + d)⁻¹ * (c * z + d) = 1 := inv_mul_cancel₀ hz
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    simp only [mobiusFn]
    rw [eq_div_iff hz]
    linear_combination ((b * c - a * d) / c) * hinv' + (a * z + b) * hcc
  have hlim : Tendsto (fun z : ℂ => a / c + ((b * c - a * d) / c) * (c * z + d)⁻¹)
      (cobounded ℂ) (𝓝 (a / c)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  exact hlim.congr' heq

theorem tendsto_mobiusFn_pole (h : a * d - b * c ≠ 0) {z₀ : ℂ} (hz₀ : c * z₀ + d = 0) :
    Tendsto (mobiusFn a b c d) (𝓝[≠] z₀) (cobounded ℂ) := by
  have hc : c ≠ 0 := by
    rintro rfl
    apply h
    have hd : d = 0 := by simpa using hz₀
    simp [hd]
  have hnum : a * z₀ + b ≠ 0 := by
    intro hab
    apply h
    linear_combination a * hz₀ - c * hab
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hcontnum : Continuous fun z : ℂ => ‖a * z + b‖ := by fun_prop
  have hcontden : Continuous fun z : ℂ => c * z + d := by fun_prop
  have h1 : Tendsto (fun z : ℂ => ‖a * z + b‖) (𝓝[≠] z₀) (𝓝 ‖a * z₀ + b‖) :=
    (hcontnum.tendsto z₀).mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun z : ℂ => c * z + d) (𝓝[≠] z₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hcontden.tendsto z₀
      rw [hz₀] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro h0
      apply hz
      have h0' : c * z + d = 0 := h0
      have : c * (z - z₀) = 0 := by linear_combination h0' - hz₀
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  have h2 : Tendsto (fun z : ℂ => ‖(c * z + d)⁻¹‖) (𝓝[≠] z₀) atTop :=
    tendsto_norm_inv_nhdsNE_zero_atTop.comp hden
  have := h1.pos_mul_atTop (norm_pos_iff.2 hnum) h2
  simpa [mobiusFn, div_eq_mul_inv, norm_mul] using this

/-- A fractional linear transformation is continuous on `ℂ̄`. -/
theorem continuous_mobiusExt (h : a * d - b * c ≠ 0) : Continuous (mobiusExt a b c d) := by
  have hcontden : Continuous fun z : ℂ => c * z + d := by fun_prop
  rw [OnePoint.continuous_iff]
  constructor
  · by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        rintro rfl
        apply h
        simp [hc]
      have heq : (fun z : ℂ => mobiusExt a b c d (z : ExtPlane)) =
          fun z => ((mobiusFn a b c d z : ℂ) : ExtPlane) := by
        funext z
        exact mobiusExt_coe (by simp [hc, hd])
      rw [heq, mobiusExt_infty_of_eq hc]
      have := tendsto_mobiusFn_cobounded_of_eq_zero h hc
      rw [cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at this
      exact OnePoint.tendsto_coe_infty.comp this
    · rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact]
      have hne : ∀ᶠ z in cobounded ℂ, c * z + d ≠ 0 :=
        (tendsto_affine_cobounded hc d).eventually (eventually_ne_cobounded 0)
      have heq : (fun z : ℂ => ((mobiusFn a b c d z : ℂ) : ExtPlane)) =ᶠ[cobounded ℂ]
          fun z => mobiusExt a b c d (z : ExtPlane) := by
        filter_upwards [hne] with z hz
        exact (mobiusExt_coe hz).symm
      rw [mobiusExt_infty_of_ne hc]
      exact ((OnePoint.continuous_coe.tendsto _).comp
        (tendsto_mobiusFn_cobounded_of_ne hc)).congr' heq
  · refine continuous_iff_continuousAt.2 fun z₀ => ?_
    by_cases hz₀ : c * z₀ + d = 0
    · show Tendsto (fun z : ℂ => mobiusExt a b c d (z : ExtPlane)) (𝓝 z₀)
        (𝓝 (mobiusExt a b c d (z₀ : ExtPlane)))
      rw [mobiusExt_coe_of_eq_zero hz₀, OnePoint.nhds_infty_eq, ← nhdsNE_sup_pure z₀]
      refine Tendsto.sup ?_ ?_
      · have hc : c ≠ 0 := by
          rintro rfl
          apply h
          have hd : d = 0 := by simpa using hz₀
          simp [hd]
        have heq : (fun z : ℂ => ((mobiusFn a b c d z : ℂ) : ExtPlane)) =ᶠ[𝓝[≠] z₀]
            fun z => mobiusExt a b c d (z : ExtPlane) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          refine (mobiusExt_coe fun h0 => hz ?_).symm
          have : c * (z - z₀) = 0 := by linear_combination h0 - hz₀
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
        have hpole := tendsto_mobiusFn_pole h hz₀
        rw [cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hpole
        exact ((tendsto_map.comp hpole).mono_right le_sup_left).congr' heq
      · exact tendsto_pure_left.2 fun s hs => by
          rw [mobiusExt_coe_of_eq_zero hz₀]
          exact mem_pure.1 (mem_sup.1 hs).2
    · have hcontfn : ContinuousAt (fun z : ℂ => (a * z + b) / (c * z + d)) z₀ :=
        ((show Continuous fun z : ℂ => a * z + b by fun_prop).continuousAt).div
          hcontden.continuousAt hz₀
      have hcont : ContinuousAt (fun z : ℂ => ((mobiusFn a b c d z : ℂ) : ExtPlane)) z₀ :=
        OnePoint.continuous_coe.continuousAt.comp hcontfn
      have hne : ∀ᶠ z in 𝓝 z₀, c * z + d ≠ 0 := hcontden.continuousAt.eventually_ne hz₀
      have heq : (fun z : ℂ => ((mobiusFn a b c d z : ℂ) : ExtPlane)) =ᶠ[𝓝 z₀]
          fun z => mobiusExt a b c d (z : ExtPlane) := by
        filter_upwards [hne] with z hz
        exact (mobiusExt_coe hz).symm
      exact hcont.congr heq

/-- A fractional linear transformation as a homeomorphism of `ℂ̄`. -/
def mobiusHomeomorph (a b c d : ℂ) (h : a * d - b * c ≠ 0) : ExtPlane ≃ₜ ExtPlane :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    { toFun := mobiusExt a b c d
      invFun := mobiusExt d (-b) (-c) a
      left_inv := mobiusExt_inv_apply h
      right_inv := fun w => by
        have h' : d * a - -b * -c ≠ 0 := by
          rwa [show d * a - -b * -c = a * d - b * c by ring]
        simpa only [neg_neg] using mobiusExt_inv_apply h' w })
    (continuous_mobiusExt h)

@[simp] theorem mobiusHomeomorph_apply (h : a * d - b * c ≠ 0) (w : ExtPlane) :
    mobiusHomeomorph a b c d h w = mobiusExt a b c d w := rfl

end Continuity

/-! ## Real transformations of the upper half-plane -/

section Real

theorem mobiusExt_ofReal_coe {a b c d x : ℝ} (h : c * x + d ≠ 0) :
    mobiusExt a b c d ((x : ℂ) : ExtPlane) =
      ((((a * x + b) / (c * x + d) : ℝ) : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by exact_mod_cast h)]
  congr 1
  simp [mobiusFn]

theorem mobiusExt_ofReal_coe_of_eq_zero {a b c d x : ℝ} (h : c * x + d = 0) :
    mobiusExt a b c d ((x : ℂ) : ExtPlane) = extInf :=
  mobiusExt_coe_of_eq_zero (by exact_mod_cast h)

theorem mobiusExt_ofReal_infty {a b c d : ℝ} (h : c ≠ 0) :
    mobiusExt a b c d extInf = (((a / c : ℝ) : ℂ) : ExtPlane) := by
  rw [mobiusExt_infty_of_ne (by exact_mod_cast h)]
  congr 1
  simp

theorem mobiusFn_im_real (a b c d : ℝ) (z : ℂ) :
    (mobiusFn a b c d z).im = (a * d - b * c) * z.im / Complex.normSq (c * z + d) := by
  simp only [mobiusFn, Complex.div_im, Complex.add_im, Complex.add_re, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem mobiusFn_den_ne_zero_real {a b c d : ℝ} (h : a * d - b * c ≠ 0) {z : ℂ}
    (hz : 0 < z.im) : (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him : c * z.im = 0 := by simpa using congrArg Complex.im h0
  have hc : c = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 hz.ne'
  have hd : d = 0 := by simpa [hc] using congrArg Complex.re h0
  exact h (by simp [hc, hd])

theorem mobiusFn_mem_upperHalf {a b c d : ℝ} (h : 0 < a * d - b * c) {z : ℂ}
    (hz : z ∈ upperHalf) : mobiusFn a b c d z ∈ upperHalf := by
  show 0 < (mobiusFn a b c d z).im
  rw [mobiusFn_im_real]
  exact div_pos (mul_pos h hz) (Complex.normSq_pos.2 (mobiusFn_den_ne_zero_real h.ne' hz))

/-- A Möbius transformation with real coefficients and positive determinant maps the upper
half-plane conformally onto itself. -/
theorem isConformalOnto_mobius_upperHalf {a b c d : ℝ} (h : 0 < a * d - b * c) :
    IsConformalOnto (mobiusFn a b c d) upperHalf upperHalf := by
  have hne : ((a : ℂ) * d - b * c) ≠ 0 := by exact_mod_cast h.ne'
  have h' : 0 < d * a - (-b) * (-c) := by linarith
  refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, ?_⟩
  · have hden := mobiusFn_den_ne_zero_real h.ne' hz
    have hnum : DifferentiableAt ℂ (fun z : ℂ => (a : ℂ) * z + b) z := by fun_prop
    have hdd : DifferentiableAt ℂ (fun z : ℂ => (c : ℂ) * z + d) z := by fun_prop
    exact (hnum.div hdd hden).differentiableWithinAt
  · have e₁ := mobiusFn_inv_apply hne (mobiusFn_den_ne_zero_real h.ne' hz₁)
    have e₂ := mobiusFn_inv_apply hne (mobiusFn_den_ne_zero_real h.ne' hz₂)
    rw [← e₁, ← e₂, heq]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mobiusFn_mem_upperHalf h hz
    · intro hw
      have hmem := mobiusFn_mem_upperHalf h' hw
      refine ⟨mobiusFn d (-b : ℝ) (-c : ℝ) a w, hmem, ?_⟩
      have hne' : ((d : ℂ) * a - -b * -c) ≠ 0 := by
        rw [show (d : ℂ) * a - -b * -c = a * d - b * c by ring]
        exact hne
      have hden : (-c : ℂ) * w + a ≠ 0 := by
        have := mobiusFn_den_ne_zero_real h'.ne' hw
        simpa using this
      have := mobiusFn_inv_apply hne' hden
      simpa only [neg_neg, Complex.ofReal_neg] using this

theorem mobiusExt_image_toExt_upperHalf {a b c d : ℝ} (h : 0 < a * d - b * c) :
    mobiusExt a b c d '' toExt upperHalf = toExt upperHalf := by
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [mobiusExt_coe (mobiusFn_den_ne_zero_real h.ne' hz)]
    exact ⟨_, mobiusFn_mem_upperHalf h hz, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rw [← (isConformalOnto_mobius_upperHalf h).2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, mobiusExt_coe (mobiusFn_den_ne_zero_real h.ne' hz)⟩

end Real

/-! ## Composition -/

theorem IsConformalOnto.mapsTo {f : ℂ → ℂ} {U V : Set ℂ} (hf : IsConformalOnto f U V) :
    MapsTo f U V := fun _ hz => hf.2.2 ▸ mem_image_of_mem f hz

theorem IsConformalOnto.comp {f g : ℂ → ℂ} {U V W : Set ℂ} (hg : IsConformalOnto g V W)
    (hf : IsConformalOnto f U V) : IsConformalOnto (g ∘ f) U W := by
  have hmaps := hf.mapsTo
  obtain ⟨hfd, hfi, hfs⟩ := hf
  obtain ⟨hgd, hgi, hgs⟩ := hg
  exact ⟨hgd.comp hfd hmaps, hgi.comp hfi hmaps, by rw [image_comp, hfs, hgs]⟩

theorem IsHomeoExtension.comp {f g : ℂ → ℂ} {U V W : Set ℂ} {F G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g V W G) (hF : IsHomeoExtension f U V F) (hfU : MapsTo f U V) :
    IsHomeoExtension (g ∘ f) U W (G ∘ F) := by
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hG1, hG2, hG3, hG4⟩ := hG
  have hmaps : MapsTo F (closure (toExt U)) (closure (toExt V)) := fun p hp =>
    hF4 ▸ mem_image_of_mem F hp
  refine ⟨fun z hz => ?_, hG2.comp hF2 hmaps, hG3.comp hF3 hmaps, ?_⟩
  · simp only [Function.comp_apply, hF1 z hz, hG1 (f z) (hfU hz)]
  · rw [image_comp, hF4, hG4]

theorem IsHomeoExtension.comp_homeomorph {f g : ℂ → ℂ} {U V W : Set ℂ}
    {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F) (hfU : MapsTo f U V)
    (e : ExtPlane ≃ₜ ExtPlane) (he : ∀ w ∈ V, e (w : ExtPlane) = ((g w : ℂ) : ExtPlane))
    (himg : e '' toExt V = toExt W) :
    IsHomeoExtension (g ∘ f) U W (e ∘ F) := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  refine ⟨fun z hz => ?_, e.continuous.comp_continuousOn h2, e.injective.comp_injOn h3, ?_⟩
  · simp only [Function.comp_apply, h1 z hz, he (f z) (hfU hz)]
  · rw [image_comp, h4, e.image_closure, himg]

/-! ### Norms on the unit disc -/

/-- On the disc, `normSq` and the norm cut at the same place. -/
theorem normSq_lt_one_iff {z : ℂ} : normSq z < 1 ↔ ‖z‖ < 1 := by
  rw [← Complex.sq_norm]
  constructor
  · intro h
    nlinarith [norm_nonneg z]
  · intro h
    nlinarith [norm_nonneg z]

end LiZhongQC
