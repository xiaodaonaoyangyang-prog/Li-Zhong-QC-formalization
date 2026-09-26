import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.ExpStripBasic
import LiZhongQC.Lemmas.AnnulusDescent
import LiZhongQC.Lemmas.StripAutomorphism
import LiZhongQC.Lemmas.AnnulusPeriod
import LiZhongQC.Lemmas.ExpStripLift
import LiZhongQC.Lemmas.AnnulusModel

/-!
# §2 双连通区域的共形模 — The conformal modulus of a doubly connected domain

* Theorem 2.1 (the three canonical domains)       — `thm2_1_canonical_form`,
                                                     `thm2_1_canonical_unique_*`
  (cases (i)/(ii) are proved in `LiZhongQC.Lemmas.CanonicalForm`; case (iii) is
  `thm2_1_canonical_form_annulus`, not proved)
* two annuli are conformally equivalent iff they are similar
                                                   — `annulus_conformallyEquivalent_iff`
  (with `dcModulus_eq_of_equiv`, `dcModulus_annulus`: proved in
  `LiZhongQC.Ch01.S04_ModulusExtremalLength`, since the proof uses §4.6)
* Definition 2.1 (modulus `M(B)`)                 — `dcModulus`
* Theorem 2.2 (conformal invariance)              — `thm2_2_dcModulus_conformal_invariant`

Doubly connected domains are open connected subsets of `ℂ` whose complement in `ℂ̄` has
two components (`IsDoublyConnected`, defined in `LiZhongQC.Basic`).
-/

open Complex Set Metric Filter Topology
open scoped ENNReal Real

noncomputable section

namespace LiZhongQC

/-- **Theorem 2.1, case (iii)**: a doubly connected domain neither of whose complementary
components is a single point is conformally equivalent to an annulus `{r₁ < |z| < r₂}`.

Not proved (kept as `sorry`): the book maps `B ∪ C₂` onto the disc, then onto a strip normalized
at prime ends (Carathéodory), and uses uniqueness to show the map is `2πi`-periodic; LZ2.txt's
alternative needs the Perron solution of the Dirichlet problem, Green's identity on level-set
domains and the argument principle — none available. -/
theorem thm2_1_canonical_form_annulus {B : Set ℂ} (hB : IsDoublyConnected B)
    (hnd : ∀ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ {x}) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂) := by
  obtain ⟨K, Phi, hKsub, hKc, hKconn, hKnt, hBK, hPhid, hPhibij, hJord, hsep,
          A, Bext, hAo, hBo, hAc, hBc, hABd, hAcd, hBcd, hcov, hAbdd, hBunb,
          hAeq, hAconn, hcollar, hball, hAcompl⟩ :=
    exists_analytic_annulus_model_of_isDoublyConnected hB hnd
  have hBA : ConformallyEquivalent B (A \ closedBall 0 1) :=
    conformallyEquivalent_sdiff_closedBall hBK hPhid hPhibij hAeq
  obtain ⟨d, hd, g, hg⟩ :=
    exists_conformal_expStrip_strip hAo hAconn hAbdd hcollar hball hAcompl
  obtain ⟨g', s, hg', hs, hper⟩ :=
    exists_periodic_of_conformal hAo hAbdd hball hAcompl hd hg
  have hann := conformallyEquivalent_annulus_of_periodic hAo hd hs hg' hper
  refine ⟨1, Real.exp (2 * Real.pi * d / s), one_pos, ?_, hBA.trans hann⟩
  have hpos : (0:ℝ) < 2 * Real.pi * d / s := by positivity
  calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (2 * Real.pi * d / s) := Real.exp_lt_exp.2 hpos

/-- **Theorem 2.1** (existence part).  A doubly connected domain is conformally equivalent
to one of: (i) `ℂ ∖ {0}`, (ii) `{0 < |z| < 1}`, (iii) an annulus `{r₁ < |z| < r₂}`,
`0 < r₁ < r₂ < ∞`.

Cases (i) and (ii), in which some component of `ℂ̄ ∖ B` is a single point, are proved in
`LiZhongQC.Lemmas.CanonicalForm` (`canonical_form_of_degenerate_component`); case (iii) is
`thm2_1_canonical_form_annulus`, which is not proved. -/
theorem thm2_1_canonical_form {B : Set ℂ} (hB : IsDoublyConnected B) :
    ConformallyEquivalent B puncturedPlane ∨ ConformallyEquivalent B puncturedDisc ∨
      ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂) := by
  by_cases hdeg : ∃ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x = {x}
  · obtain ⟨x, hx, hxpt⟩ := hdeg
    rcases canonical_form_of_degenerate_component hB hx hxpt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hdeg
    exact Or.inr (Or.inr (thm2_1_canonical_form_annulus hB hdeg))

/-- The key step of the uniqueness part of **Theorem 2.1**: a bounded holomorphic function on
`ℂ ∖ {0}` cannot be injective.  (The point `0` is a removable singularity, so the function
extends to a bounded entire function, which is constant by Liouville's theorem.) -/
theorem not_injOn_punctured_of_bounded {f : ℂ → ℂ} {M : ℝ}
    (hd : DifferentiableOn ℂ f puncturedPlane) (hinj : InjOn f puncturedPlane)
    (hb : ∀ z ∈ puncturedPlane, ‖f z‖ ≤ M) : False := by
  have hd' : DifferentiableOn ℂ f (univ \ {0}) := by
    rwa [← compl_eq_univ_diff]
  have hbdd : BddAbove (norm ∘ f '' (univ \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hb z hz.2
  set g := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f) with hg
  have hgd : Differentiable ℂ g :=
    differentiableOn_univ.1 (differentiableOn_update_limUnder_of_bddAbove univ_mem hd' hbdd)
  have hgb : Bornology.IsBounded (range g) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max M ‖g 0‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall_zero_iff]
    by_cases hz : z = 0
    · subst hz
      exact le_max_right _ _
    · rw [hg, Function.update_of_ne hz]
      exact le_max_of_le_left (hb z hz)
  have hconst : g 1 = g (-1) := liouville_theorem_aux hgd hgb 1 (-1)
  have h1 : g 1 = f 1 := Function.update_of_ne one_ne_zero _ _
  have hm1 : g (-1) = f (-1) := Function.update_of_ne (neg_ne_zero.2 one_ne_zero) _ _
  have hmem1 : (1 : ℂ) ∈ puncturedPlane := by simp [puncturedPlane]
  have hmemm1 : (-1 : ℂ) ∈ puncturedPlane := by simp [puncturedPlane]
  have := hinj hmem1 hmemm1 (by rw [← h1, ← hm1, hconst])
  norm_num at this

/-- **Theorem 2.1** (uniqueness part, (i) vs (ii)).  A conformal map of `ℂ ∖ {0}` into the
punctured disc would be bounded, hence constant by Liouville's theorem. -/
theorem thm2_1_canonical_unique_plane_disc :
    ¬ ConformallyEquivalent puncturedPlane puncturedDisc := by
  rintro ⟨f, hd, hinj, himg⟩
  refine not_injOn_punctured_of_bounded hd hinj (M := 1) fun z hz => ?_
  have hmem : f z ∈ puncturedDisc := himg.subset (mem_image_of_mem f hz)
  exact hmem.2.le

/-- **Theorem 2.1** (uniqueness part, (i) vs (iii)).  A conformal map of `ℂ ∖ {0}` onto an annulus
would be bounded, hence constant by Liouville's theorem. -/
theorem thm2_1_canonical_unique_plane_annulus {r₁ r₂ : ℝ} (_h₁ : 0 < r₁) (_h₂ : r₁ < r₂) :
    ¬ ConformallyEquivalent puncturedPlane (annulus r₁ r₂) := by
  rintro ⟨f, hd, hinj, himg⟩
  refine not_injOn_punctured_of_bounded hd hinj (M := r₂) fun z hz => ?_
  have hmem : f z ∈ annulus r₁ r₂ := himg.subset (mem_image_of_mem f hz)
  exact hmem.2.le

/-- **Theorem 2.1** (uniqueness part, (ii) vs (iii)).  `0` is a removable singularity of a conformal
map `f` of `{0 < |z| < 1}` onto `{r₁ < |w| < r₂}`; its extension `g` is an open map (and not
constant).  Then `c = g(0)` can neither be a boundary point of the annulus (a neighbourhood of `c`
would consist of values of `f`) nor a point `f(z₁)` of the annulus (`f` would take a value near `c`
both near `0` and near `z₁`).
(Source note: the book argues via the reflection principle; this proof is self-contained.) -/
theorem thm2_1_canonical_unique_disc_annulus {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    ¬ ConformallyEquivalent puncturedDisc (annulus r₁ r₂) := by
  rintro ⟨f, hd, hinj, himg⟩
  have hPD : ball (0 : ℂ) 1 \ {0} = puncturedDisc := by
    ext z
    simp only [mem_diff, mem_ball_zero_iff, mem_singleton_iff, puncturedDisc, annulus,
      mem_setOf_eq, norm_pos_iff]
    tauto
  have hsub : puncturedDisc ⊆ ball (0 : ℂ) 1 := by
    rw [← hPD]
    exact diff_subset
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  have hfA : ∀ z ∈ puncturedDisc, f z ∈ annulus r₁ r₂ := fun z hz =>
    himg.subset (mem_image_of_mem f hz)
  -- `0` is a removable singularity
  have hbdd : BddAbove (norm ∘ f '' (ball (0 : ℂ) 1 \ {0})) := by
    refine ⟨r₂, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hPD] at hz
    exact (hfA z hz).2.le
  set g := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    differentiableOn_update_limUnder_of_bddAbove hball (by rwa [hPD]) hbdd
  have hgf : ∀ z ∈ puncturedDisc, g z = f z := fun z hz => by
    rw [← hPD] at hz
    exact Function.update_of_ne (mem_singleton_iff.not.1 hz.2) _ _
  -- `c = g(0)` lies on the closed annulus
  have hc : ‖g 0‖ ∈ Icc r₁ r₂ := by
    have hcont : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
      (hgd.differentiableAt hball).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine isClosed_Icc.mem_of_tendsto ((continuous_norm.tendsto _).comp hcont) ?_
    filter_upwards [diff_mem_nhdsWithin_compl hball {0}] with z hz
    rw [hPD] at hz
    show ‖g z‖ ∈ Icc r₁ r₂
    rw [hgf z hz]
    exact ⟨(hfA z hz).1.le, (hfA z hz).2.le⟩
  have hc0 : g 0 ≠ 0 := by
    intro h0
    have := hc.1
    rw [h0, norm_zero] at this
    linarith
  -- a value `w ≠ c` of `g` is a value of `f`
  have hnear : ∀ s ⊆ ball (0 : ℂ) 1, ∀ w ∈ g '' s, w ≠ g 0 →
      ∃ u ∈ s, u ∈ puncturedDisc ∧ f u = w := by
    rintro s hs w ⟨u, hu, rfl⟩ hne
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hne rfl
    have hu' : u ∈ puncturedDisc := by
      rw [← hPD]
      exact ⟨hs hu, mem_singleton_iff.not.2 hu0⟩
    exact ⟨u, hu, hu', (hgf u hu').symm⟩
  -- open mapping theorem
  have hga : AnalyticOnNhd ℂ g (ball 0 1) := hgd.analyticOnNhd isOpen_ball
  rcases hga.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | hopen
  · have hm₁ : (1 / 2 : ℂ) ∈ puncturedDisc := by norm_num [puncturedDisc, annulus]
    have hm₂ : (-(1 / 2) : ℂ) ∈ puncturedDisc := by norm_num [puncturedDisc, annulus]
    have e : f (1 / 2) = f (-(1 / 2)) := by
      rw [← hgf _ hm₁, ← hgf _ hm₂, hw _ (hsub hm₁), hw _ (hsub hm₂)]
    have := hinj hm₁ hm₂ e
    norm_num at this
  by_cases hcA : g 0 ∈ annulus r₁ r₂
  · -- `c = f(z₁)` with `z₁ ≠ 0`: `g` takes the values near `c` near `0` and near `z₁`
    rw [← himg] at hcA
    obtain ⟨z₁, hz₁, hfz₁⟩ := hcA
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
    have hW : g '' ball (0 : ℂ) ρ ∩ g '' (ball z₁ ρ ∩ ball 0 1) ∈ 𝓝 (g 0) := by
      refine inter_mem ((hopen _ hs₀ isOpen_ball).mem_nhds
        (mem_image_of_mem g (mem_ball_self hρ0))) ?_
      exact (hopen _ hs₁ (isOpen_ball.inter isOpen_ball)).mem_nhds
        ⟨z₁, ⟨mem_ball_self hρ0, hsub hz₁⟩, (hgf z₁ hz₁).trans hfz₁⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
    have hwmem : g 0 + ((ε / 2 : ℝ) : ℂ) ∈ ball (g 0) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hwne : g 0 + ((ε / 2 : ℝ) : ℂ) ≠ g 0 := by
      intro h
      have h' : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination h
      exact (half_pos hε).ne' (by exact_mod_cast h')
    obtain ⟨hw₀, hw₁⟩ := hεW hwmem
    obtain ⟨u₀, hu₀, hu₀', hfu₀⟩ := hnear _ hs₀ _ hw₀ hwne
    obtain ⟨u₁, hu₁, hu₁', hfu₁⟩ := hnear _ hs₁ _ hw₁ hwne
    have e := hinj hu₀' hu₁' (hfu₀.trans hfu₁.symm)
    subst e
    exact hdisj u₀ hu₀ hu₁.1
  · -- `|c| = r₁` or `|c| = r₂`: points near `c` off the closed annulus are values of `f`
    have hcases : ‖g 0‖ = r₁ ∨ ‖g 0‖ = r₂ := by
      by_contra hne
      push Not at hne
      exact hcA ⟨lt_of_le_of_ne hc.1 hne.1.symm, lt_of_le_of_ne hc.2 hne.2⟩
    have hV : g '' ball (0 : ℂ) 1 ∈ 𝓝 (g 0) :=
      (hopen _ subset_rfl isOpen_ball).mem_nhds (mem_image_of_mem g (mem_ball_self one_pos))
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
    have hn0 : 0 < ‖g 0‖ := norm_pos_iff.2 hc0
    set δ : ℝ := min (1 / 2) (ε / (2 * ‖g 0‖)) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hδε : δ * ‖g 0‖ < ε := by
      have hle : δ ≤ ε / (2 * ‖g 0‖) := min_le_right _ _
      calc δ * ‖g 0‖ ≤ ε / (2 * ‖g 0‖) * ‖g 0‖ := by gcongr
        _ = ε / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hn0.ne']
        _ < ε := half_lt_self hε
    obtain ⟨t, ht, htne, htA⟩ :
        ∃ t : ℝ, |t - 1| = δ ∧ t ≠ 1 ∧ g 0 * (t : ℂ) ∉ annulus r₁ r₂ := by
      rcases hcases with h | h
      · refine ⟨1 - δ, by rw [show 1 - δ - 1 = -δ by ring, abs_neg, abs_of_pos hδ0],
          by linarith, ?_⟩
        rintro ⟨h1, -⟩
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 1 - δ by linarith), h] at h1
        nlinarith [mul_pos h₁ hδ0]
      · refine ⟨1 + δ, by rw [add_sub_cancel_left, abs_of_pos hδ0], by linarith, ?_⟩
        rintro ⟨-, h2⟩
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 1 + δ by linarith), h] at h2
        nlinarith [mul_pos (h₁.trans h₂) hδ0]
    have hwball : g 0 * (t : ℂ) ∈ ball (g 0) ε := by
      rw [mem_ball, dist_eq_norm, show g 0 * (t : ℂ) - g 0 = g 0 * ((t - 1 : ℝ) : ℂ) by
        push_cast; ring, norm_mul, norm_real, Real.norm_eq_abs, ht, mul_comm]
      exact hδε
    have hwne : g 0 * (t : ℂ) ≠ g 0 := by
      intro h
      apply htne
      have h' : g 0 * ((t - 1 : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination h
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact absurd h0 hc0
      · have : t - 1 = 0 := by exact_mod_cast h0
        linarith
    obtain ⟨u, -, hu', hfu⟩ := hnear _ subset_rfl _ (hεV hwball) hwne
    exact htA (by rw [← hfu]; exact hfA u hu')

open scoped Classical in
/-- **Definition 2.1** (双连通区域的共形模).  If `B` is conformally equivalent to the annulus
`{r₁ < |z| < r₂}` (`0 < r₁ < r₂ < ∞`) then `M(B) = ln (r₂ / r₁)`; if `B` is conformally
equivalent to `ℂ ∖ {0}` or to `{0 < |z| < 1}` then `M(B) = ∞`. -/
def dcModulus (B : Set ℂ) : ℝ≥0∞ :=
  if ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂) then
    ⨆ (r₁ : ℝ) (r₂ : ℝ) (_ : 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂)),
      ENNReal.ofReal (Real.log (r₂ / r₁))
  else ⊤

/-- An annulus is open. -/
theorem isOpen_annulus (r₁ r₂ : ℝ) : IsOpen (annulus r₁ r₂) :=
  isOpen_Ioo.preimage continuous_norm

/-- **Theorem 2.2**: the modulus of a doubly connected domain is a conformal invariant.  (`B` and `B'`
are conformally equivalent to exactly the same annuli.) -/
theorem thm2_2_dcModulus_conformal_invariant {B B' : Set ℂ} (hB : IsDoublyConnected B)
    (h : ConformallyEquivalent B B') : dcModulus B = dcModulus B' := by
  have key : ∀ r₁ r₂ : ℝ,
      ConformallyEquivalent B (annulus r₁ r₂) ↔ ConformallyEquivalent B' (annulus r₁ r₂) :=
    fun r₁ r₂ => ⟨fun hB' => (h.symm hB.1).trans hB', fun hB' => h.trans hB'⟩
  have hex : (∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂)) ↔
      ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B' (annulus r₁ r₂) := by
    simp only [key]
  unfold dcModulus
  by_cases hc : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ConformallyEquivalent B (annulus r₁ r₂)
  · rw [if_pos hc, if_pos (hex.1 hc)]
    simp only [key]
  · rw [if_neg hc, if_neg (mt hex.2 hc)]

end LiZhongQC
