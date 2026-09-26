import Mathlib

/-!
# Entire functions with linear growth at infinity

If `f` is entire and `f(z)/z → 1` as `z → ∞`, then `f(z) = z + f(0)` for every `z`; in particular,
if additionally `f(0) = 0`, then `f = id`. Route: `g z := f z - z - f 0` is entire with `g 0 = 0`
and `g z / z → 0` along `cocompact ℂ`; `dslope g 0` is entire, agrees with `fun z => g z / z` away
from `0`, and hence also tends to `0` along `cocompact ℂ` — so it is bounded (continuity handles a
compact neighbourhood of `0`, the tendsto handles the rest), and Liouville's theorem
(`Differentiable.exists_const_forall_eq_of_bounded`) forces it to be the constant `0`. This gives
`g ≡ 0`, i.e. `f z = z + f 0` everywhere.

Extracted as a Mathlib-only leaf: the technique is already used inline (not as a reusable lemma) in
`LiZhongQC/Ch02/S12_Existence.lean` (`thm12_2`'s existence proof, around `hfun`/`dslope hfun 0`),
driven there by an explicit growth *bound* rather than a `Tendsto ... (cocompact ℂ) (𝓝 1)`
hypothesis; here the growth bound is derived from the tendsto hypothesis instead.
-/

open Filter Metric Topology Complex

namespace LiZhongQC

/-- If `f` is entire and `f(z)/z → 1` as `z → ∞` (along `cocompact ℂ`), then `f` is exactly the
affine map `z ↦ z + f(0)`. -/
theorem entire_eq_add_const_of_tendsto_div {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1)) :
    ∀ z, f z = z + f 0 := by
  set g : ℂ → ℂ := fun z => f z - z - f 0 with hgdef
  have hgDiff : Differentiable ℂ g := (hf.sub differentiable_id).sub (differentiable_const _)
  have hg0 : g 0 = 0 := by simp [hgdef]
  -- `f 0 / z → 0` along `cocompact ℂ`
  have hf0z : Tendsto (fun z : ℂ => f 0 / z) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_div]
    have h1 : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun x : ℝ => ‖f 0‖ * x⁻¹) atTop (𝓝 (‖f 0‖ * 0)) :=
      tendsto_inv_atTop_zero.const_mul (‖f 0‖)
    rw [mul_zero] at h2
    simpa [div_eq_mul_inv, Function.comp_def] using h2.comp h1
  have hne0 : {(0 : ℂ)}ᶜ ∈ cocompact ℂ :=
    mem_cocompact.mpr ⟨{0}, isCompact_singleton, subset_rfl⟩
  -- `z / z → 1` along `cocompact ℂ` (in fact `z / z = 1` eventually, since `z ≠ 0` eventually)
  have hzz : Tendsto (fun z : ℂ => z / z) (cocompact ℂ) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hne0] with z hz
    exact (div_self (by simpa using hz)).symm
  have hgzero_lim : Tendsto (fun z => g z / z) (cocompact ℂ) (𝓝 0) := by
    have heq : (fun z : ℂ => g z / z) =ᶠ[cocompact ℂ] fun z => (f z / z - z / z) - f 0 / z := by
      filter_upwards [hne0] with z hz
      have hzne : z ≠ 0 := by simpa using hz
      rw [hgdef]
      field_simp
    rw [Filter.tendsto_congr' heq]
    have := (h.sub hzz).sub hf0z
    simpa using this
  -- `dslope g 0` agrees with `fun z => g z / z` for `z ≠ 0`, hence also tends to `0`
  have heq_pt : ∀ z : ℂ, z ≠ 0 → dslope g 0 z = g z / z := by
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_module, sub_zero, hg0, sub_zero, smul_eq_mul,
      ← div_eq_inv_mul]
  have hdslope_lim : Tendsto (dslope g 0) (cocompact ℂ) (𝓝 0) := by
    apply hgzero_lim.congr'
    filter_upwards [hne0] with z hz
    exact (heq_pt z (by simpa using hz)).symm
  have hdslopeDiff : Differentiable ℂ (dslope g 0) :=
    differentiableOn_univ.mp ((differentiableOn_dslope (Filter.univ_mem)).mpr
      (differentiableOn_univ.mpr hgDiff))
  -- bounded: eventually (outside a compact set) close to `0`, continuous on the compact set
  have hdslopeBdd : Bornology.IsBounded (Set.range (dslope g 0)) := by
    have hev : ∀ᶠ z in cocompact ℂ, dslope g 0 z ∈ closedBall (0 : ℂ) 1 :=
      hdslope_lim.eventually (closedBall_mem_nhds (0 : ℂ) one_pos)
    obtain ⟨K, hKcompact, hKsub⟩ := mem_cocompact.mp hev
    obtain ⟨C, hC⟩ := (hKcompact.image hdslopeDiff.continuous.norm).bddAbove
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max 1 C, ?_⟩
    rintro x ⟨z, rfl⟩
    by_cases hz : z ∈ K
    · exact (hC (Set.mem_image_of_mem _ hz)).trans (le_max_right _ _)
    · have : dslope g 0 z ∈ closedBall (0 : ℂ) 1 := hKsub hz
      rw [mem_closedBall, dist_eq_norm, sub_zero] at this
      exact this.trans (le_max_left _ _)
  obtain ⟨c, hc⟩ := hdslopeDiff.exists_const_forall_eq_of_bounded hdslopeBdd
  have hc0 : c = 0 := by
    have h1 : Tendsto (dslope g 0) (cocompact ℂ) (𝓝 c) :=
      tendsto_const_nhds.congr (fun z => (hc z).symm)
    exact tendsto_nhds_unique h1 hdslope_lim
  have hgeq0 : ∀ z, g z = 0 := by
    intro z
    rcases eq_or_ne z 0 with rfl | hzne
    · exact hg0
    · have hz1 := hc z
      rw [hc0] at hz1
      rw [heq_pt z hzne] at hz1
      exact (div_eq_zero_iff.mp hz1).resolve_right hzne
  intro z
  have hz0 := hgeq0 z
  rw [hgdef] at hz0
  linear_combination hz0

/-- If in addition `f 0 = 0`, an entire `f` with `f(z)/z → 1` at infinity is the identity. -/
theorem entire_eq_id_of_tendsto_div {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1)) (h0 : f 0 = 0) :
    f = id := by
  funext z
  have := entire_eq_add_const_of_tendsto_div hf h z
  rw [h0, add_zero] at this
  exact this

end LiZhongQC
