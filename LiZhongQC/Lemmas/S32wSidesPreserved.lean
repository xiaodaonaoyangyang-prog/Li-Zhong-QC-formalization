import LiZhongQC.Lemmas.S32wBdryFixedPoints
import LiZhongQC.Ch04.S17_BoundaryValues

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- A diagonal matrix with `|a| ≠ 1` is hyperbolic. -/
theorem s32w_diag_hyperbolic (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h01 : M 0 1 = 0) (h10 : M 1 0 = 0)
    (habs : |M 0 0| ≠ 1) : 2 < |M 0 0 + M 1 1| := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe M
    rw [Matrix.det_fin_two, h01, h10] at h
    linarith
  have hne : M 0 0 - M 1 1 ≠ 0 := by
    intro h0
    apply habs
    have : M 0 0 = M 1 1 := by linarith
    rw [← this] at hdet
    have h2 : |M 0 0| ^ 2 = 1 := by rw [sq_abs]; nlinarith
    nlinarith [abs_nonneg (M 0 0)]
  have h4 : 4 < (M 0 0 + M 1 1) ^ 2 := by
    have : 0 < (M 0 0 - M 1 1) ^ 2 := by positivity
    nlinarith
  by_contra hcon
  push_neg at hcon
  nlinarith [abs_nonneg (M 0 0 + M 1 1), sq_abs (M 0 0 + M 1 1)]

/-- The boundary extension of a map commuting with a diagonal hyperbolic `M` fixes `0` and `∞`. -/
theorem s32w_diag_fix_ends {f : UpperHalfPlane ≃ₜ UpperHalfPlane} {Φ : ExtPlane → ExtPlane}
    (hΦ : IsHomeoExtension (liftToC f) upperHalf upperHalf Φ) (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (habs : |M 0 0| ≠ 1)
    (hcomm : ∀ τ, f (M • τ) = M • f τ) :
    Φ extInf = extInf ∧ Φ (((0 : ℂ)) : ExtPlane) = (((0 : ℂ)) : ExtPlane) := by
  have hhyp := s32w_diag_hyperbolic M h01 h10 habs
  have hR : RepresentsConj f M M := by
    intro τ
    rw [hcomm, Homeomorph.apply_symm_apply]
  obtain ⟨ha, hr⟩ := s32w_bdry_fixed_points hΦ hR hhyp hhyp
  have hfa : attractingFixedPoint M = if 1 < |M 0 0| then extInf else (((0 : ℝ) : ℂ) : ExtPlane) := by
    unfold attractingFixedPoint
    simp [h10, h01]
  have hfr : repellingFixedPoint M = if 1 < |M 0 0| then (((0 : ℝ) : ℂ) : ExtPlane) else extInf := by
    unfold repellingFixedPoint
    simp [h10, h01]
  by_cases h1 : 1 < |M 0 0|
  · rw [hfa, if_pos h1] at ha
    rw [hfr, if_pos h1] at hr
    exact ⟨ha, by simpa using hr⟩
  · rw [hfa, if_neg h1] at ha
    rw [hfr, if_neg h1] at hr
    exact ⟨hr, by simpa using ha⟩

/-- **L4a.**  A `K`-q.c. self-map `f` of `ℍ` commuting with a diagonal hyperbolic `M` and preserving the imaginary
axis (`Re τ = 0 ↔ Re (f τ) = 0`) maps the right quadrant half `{Re > 0}` into itself: the boundary extension
fixes `0, ∞`, its values on `ℝ` are increasing (`b4_qs_monotone`), so they preserve `ℝ₊`. -/
theorem s32w_sides_preserved {K : ℝ} (f : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hK : IsKQC (liftToC f) upperHalf K) (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (habs : |M 0 0| ≠ 1) (hcomm : ∀ τ, f (M • τ) = M • f τ)
    (hax : ∀ τ : UpperHalfPlane, (τ : ℂ).re = 0 ↔ ((f τ : UpperHalfPlane) : ℂ).re = 0) :
    ∀ τ : UpperHalfPlane, 0 < (τ : ℂ).re → 0 < ((f τ : UpperHalfPlane) : ℂ).re := by
  have himg : liftToC f '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [h23l_liftToC_eq f hz]
      exact (f _).im_pos
    · intro hw
      have hw' : 0 < w.im := hw
      refine ⟨((f.symm ⟨w, hw'⟩ : UpperHalfPlane) : ℂ), (f.symm ⟨w, hw'⟩).im_pos, ?_⟩
      rw [h23l_liftToC_eq f (f.symm ⟨w, hw'⟩).im_pos]
      simp
  obtain ⟨Φ, hΦ⟩ := thm13_3_boundary_correspondence isJordanDomain_upperHalf isJordanDomain_upperHalf
    ⟨K, hK⟩ himg
  obtain ⟨hinf, h0⟩ := s32w_diag_fix_ends hΦ M h01 h10 habs hcomm
  set h : ℝ → ℝ := fun x => (abR_t_fin Φ x).re with hh
  have hhx : ∀ x : ℝ, Φ ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
    intro x
    have hspec := s13x_rf_fin_spec hΦ hinf (z := (x : ℂ)) (by simp)
    have him := s13x_rf_fin_im_eq_zero hΦ himg hinf (x := (x : ℂ)) (by simp)
    rw [hspec.1]
    congr 1
    exact Complex.ext (by simp [hh]) (by simpa using him)
  have hQ : HasQCExtensionH h (liftToC f) K := ⟨hK, himg, Φ, hΦ, hinf, hhx⟩
  have hmono := (b4_qs_monotone hQ).1
  have h00 : h 0 = 0 := by
    have h0' := hhx 0
    simp only [Complex.ofReal_zero] at h0'
    rw [h0] at h0'
    have := OnePoint.coe_injective h0'
    exact Complex.ofReal_eq_zero.mp this.symm
  have h1pos : 0 < h 1 := by rw [← h00]; exact hmono one_pos
  intro τ hτ
  set S : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im} with hS
  have hSc : IsPreconnected S :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hSU : S ⊆ upperHalf := fun z hz => hz.2
  have hcont : ContinuousOn (liftToC f) S := (h23l_liftToC_continuousOn f.continuous).mono hSU
  have hsplit : liftToC f '' S ⊆ {w : ℂ | 0 < w.re} ∨ liftToC f '' S ⊆ {w : ℂ | w.re < 0} := by
    refine (hSc.image _ hcont).subset_or_subset (isOpen_lt continuous_const continuous_re)
      (isOpen_lt continuous_re continuous_const) ?_ ?_
    · refine Set.disjoint_left.2 fun z h₁ h₂ => ?_
      exact lt_asymm (show 0 < z.re from h₁) (show z.re < 0 from h₂)
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : 0 < z.im := hz.2
      have e := hax ⟨z, hz'⟩
      have hne : ((f ⟨z, hz'⟩ : UpperHalfPlane) : ℂ).re ≠ 0 := by
        intro h0'
        have := e.mpr h0'
        exact absurd this (show (z : ℂ).re ≠ 0 from (show 0 < z.re from hz.1).ne')
      have hl : liftToC f z = ((f ⟨z, hz'⟩ : UpperHalfPlane) : ℂ) := h23l_liftToC_coe f ⟨z, hz'⟩
      rw [hl]
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
  have hτS : (τ : ℂ) ∈ S := ⟨hτ, τ.im_pos⟩
  have himgτ : liftToC f (τ : ℂ) = ((f τ : UpperHalfPlane) : ℂ) := h23l_liftToC_coe f τ
  rcases hsplit with hu | hv
  · have := hu ⟨(τ : ℂ), hτS, rfl⟩
    rw [himgτ] at this
    exact this
  · exfalso
    -- the approach `1 + i/(n+1) → 1`
    obtain ⟨ε, hε0, hεt⟩ : ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) :=
      ⟨fun n => 1 / ((n : ℝ) + 1), fun n => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩
    set zs : ℕ → ℂ := fun n => (1 : ℂ) + Complex.I * ((ε n : ℝ) : ℂ) with hzs
    have hzS : ∀ n, zs n ∈ S := fun n => by
      refine ⟨?_, ?_⟩
      · show 0 < (zs n).re
        simp [hzs]
      · show 0 < (zs n).im
        simpa [hzs] using hε0 n
    have hz1 : Tendsto zs atTop (𝓝 ((1 : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun n : ℕ => ((ε n : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp hεt
      have := (tendsto_const_nhds (x := (1 : ℂ))).add (tendsto_const_nhds (x := Complex.I) |>.mul h1)
      simpa [hzs] using this
    have hcl : ∀ n, ((zs n : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := fun n =>
      s13x_rf_coe_mem_closure (le_of_lt (hzS n).2)
    have hT : Tendsto (fun n => Φ ((zs n : ℂ) : ExtPlane)) atTop (𝓝 (Φ (((1 : ℝ) : ℂ) : ExtPlane))) := by
      have hcw : Tendsto (fun n => ((zs n : ℂ) : ExtPlane)) atTop
          (𝓝[closure (toExt upperHalf)] (((1 : ℝ) : ℂ) : ExtPlane)) :=
        tendsto_nhdsWithin_iff.2 ⟨(OnePoint.continuous_coe.tendsto _).comp hz1,
          Eventually.of_forall hcl⟩
      exact (hΦ.2.1 _ (s13x_rf_coe_mem_closure (by simp))).tendsto.comp hcw
    have hT' : Tendsto (fun n => ((liftToC f (zs n) : ℂ) : ExtPlane)) atTop
        (𝓝 ((((h 1 : ℝ) : ℂ)) : ExtPlane)) := by
      rw [← hhx 1]
      refine hT.congr fun n => ?_
      exact hΦ.1 _ (hSU (hzS n))
    have hT'' : Tendsto (fun n => liftToC f (zs n)) atTop (𝓝 ((h 1 : ℝ) : ℂ)) :=
      OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 hT'
    have hre : Tendsto (fun n => (liftToC f (zs n)).re) atTop (𝓝 (h 1)) := by
      have := (Complex.continuous_re.tendsto _).comp hT''
      simpa [Function.comp_def] using this
    have hev := hre.eventually (lt_mem_nhds h1pos)
    obtain ⟨n, hn⟩ := hev.exists
    have := hv ⟨zs n, hzS n, rfl⟩
    exact absurd hn (not_lt.2 (le_of_lt this))

end LiZhongQC
