import LiZhongQC.Lemmas.D1OrdinaryIsolation
import LiZhongQC.Lemmas.D1SphericalStabilizer

/-! Complete D1 I producer. Actual hosts only; no interface stub import. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- I. PRODUCE precise ordinary-orbit isolation inside the chosen V. The
charts extend across their spherical centers; their punctured finite lifts lie in
Ω and are holomorphic. At infinity use an inversion coordinate. Reuse s36x_fin
and the approved D0 ordinary-stabilizer theorem, with spherical transfer at
infinity. The factor-two source disk leaves room for compact annuli later. -/
theorem s36d1_orbit_isolation (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {k : ℕ} (a : Fin k → ExtPlane)
    (hseed : ∀ i, a i = extInf ∨ ∃ s ∈ E, a i = ((s : ℂ) : ExtPlane)) (hord : ∀ i, a i ∈ ordinarySet Γ)
    (hsep : ∀ i j γ, γ ∈ Γ → mobiusSL (slRealToComplex γ) (a i) = a j → i = j)
    (hcomplete : ∀ p : ExtPlane, p ∈ ordinarySet Γ →
      (p = extInf ∨ ∃ s ∈ E, p = ((s : ℂ) : ExtPlane)) →
      ∃ i, ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) (a i))
    (V : Set ExtPlane) (hVo : IsOpen V) (hVa : ∀ i, a i ∈ V) :
    ∃ (e : Fin k → OpenPartialHomeomorph ℂ ExtPlane) (ζ : Fin k → ℂ → ℂ),
      (∀ i, e i 0 = a i) ∧
      (∀ i, (e i).source = ball (0 : ℂ) 2) ∧
      (∀ i, (e i).target ⊆ V) ∧
      (∀ i, (e i).target ⊆ (fuchsianLimitSet Γ)ᶜ) ∧
      (∀ i p, p ∈ (e i).target →
        ((∃ γ ∈ Γ, ∃ s ∈ E, p = mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane)) ∨
          ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) extInf) → p = a i) ∧
      (∀ i j γ, γ ∈ Γ →
        ((mobiusSL (slRealToComplex γ) '' (e i).target) ∩ (e j).target).Nonempty →
        i = j ∧ (γ = 1 ∨ γ = -1)) ∧
      (∀ i w, w ≠ 0 → ‖w‖ < 2 → ζ i w ∈ Ω ∧ (ζ i w : ExtPlane) = e i w) ∧
      (∀ i, DifferentiableOn ℂ (ζ i) {w | w ≠ 0 ∧ ‖w‖ < 2}) := by
  classical
  -- The complete ordinary-seed representative data already records the part of
  -- hE needed below; the frozen hE premise is retained.
  have _ := hE
  have _ := hseed
  obtain ⟨U, hUa, hUO, hUprec⟩ :=
    s36d1_precise_ordinary_neighborhoods hΓ a (fun i => (hord i).2) hsep
      (fun i γ hγ hfix => s36d1_spherical_stabilizer hΓ hfree (hord i) hγ hfix)
      V hVo hVa
  have hsign : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      g = 1 ∨ g = -1 → ∀ p : ExtPlane, mobiusSL (slRealToComplex g) p = p := by
    intro g hg p
    rcases hg with rfl | rfl
    · rw [k24_slReal_one, k24_mobiusSL_one]
    · induction p using OnePoint.rec with
      | infty =>
        rw [k24_mobiusSL_real, mobiusExt_infty_of_eq (by simp)]
      | coe z =>
        have hd : ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
            (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 ≠ 0 := by norm_num
        have hm : mobiusSL (slRealToComplex (-1)) (z : ExtPlane) =
            ((h36p_m (-1) z : ℂ) : ExtPlane) := s36x_msl_coe (-1) hd
        rw [hm, h36p_a_m_neg, h36p_a_m_one]
  have hUdel : ∀ i p, p ∈ U i →
      ((∃ γ ∈ Γ, ∃ s ∈ E, p = mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane)) ∨
        ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) extInf) → p = a i := by
    intro i p hp hdel
    obtain ⟨t, htseed, htR, γ, hγ, hpt⟩ :
        ∃ t : ExtPlane, (t = extInf ∨ ∃ s ∈ E, t = ((s : ℂ) : ExtPlane)) ∧
          t ∈ extRealLine ∧ ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) t := by
      rcases hdel with ⟨γ, hγ, s, hs, heq⟩ | ⟨γ, hγ, heq⟩
      · refine ⟨((s : ℂ) : ExtPlane), Or.inr ⟨s, hs, rfl⟩, Or.inl ?_, γ, hγ, heq⟩
        exact ⟨(s : ℂ), by change (s : ℂ).im = 0; exact Complex.ofReal_im s, rfl⟩
      · exact ⟨extInf, Or.inl rfl, Or.inr rfl, γ, hγ, heq⟩
    have htO : t ∈ ordinarySet Γ := by
      refine ⟨htR, ?_⟩
      intro ht
      have hm : mobiusSL (slRealToComplex γ) t ∈ fuchsianLimitSet Γ :=
        k22_t_limitSet_smul (Subgroup.mem_map_of_mem _ hγ) ht
      exact (hUO i hp).2 (hpt.symm ▸ hm)
    obtain ⟨j, δ, hδ, htj⟩ := hcomplete t htO htseed
    have hpj : p = mobiusSL (slRealToComplex (γ * δ)) (a j) := by
      rw [k24_slReal_mul, k24_mobiusSL_mul, ← htj]
      exact hpt
    obtain ⟨hji, hgsign⟩ := hUprec j i (γ * δ) (Γ.mul_mem hγ hδ)
      ⟨p, ⟨a j, mem_of_mem_nhds (hUa j), hpj.symm⟩, hp⟩
    exact hpj.trans ((hsign (γ * δ) hgsign (a j)).trans (congrArg a hji))
  -- h36q_d_exists_base chooses a translation at a finite real center and
  -- z ↦ -1/z at infinity. Rescaling the input gives the required disk charts.
  choose H hH using fun i => h36q_d_exists_base (hord i).1
  have hpre : ∀ i, {z : ℂ | mobiusSL (slRealToComplex (H i)) (z : ExtPlane) ∈ U i} ∈ 𝓝 0 := by
    intro i
    have hc : Continuous (fun z : ℂ => mobiusSL (slRealToComplex (H i)) (z : ExtPlane)) :=
      (k24_mobiusSLHomeo (slRealToComplex (H i))).continuous.comp OnePoint.continuous_coe
    apply hc.continuousAt
    show U i ∈ 𝓝 (mobiusSL (slRealToComplex (H i)) ((0 : ℂ) : ExtPlane))
    rw [hH i]
    exact hUa i
  choose ε hε hεU using fun i => Metric.mem_nhds_iff.mp (hpre i)
  let r : Fin k → ℝ := fun i => ε i / 2
  have hr : ∀ i, 0 < r i := fun i => half_pos (hε i)
  have hrC : ∀ i, (r i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hr i).ne'
  let F : Fin k → ℂ → ExtPlane := fun i w =>
    mobiusSL (slRealToComplex (H i)) (((r i : ℂ) * w : ℂ) : ExtPlane)
  have hF0 : ∀ i, F i 0 = a i := by
    intro i
    change mobiusSL (slRealToComplex (H i)) (((r i : ℂ) * 0 : ℂ) : ExtPlane) = _
    rw [mul_zero, hH i]
  have hFU : ∀ i w, ‖w‖ < 2 → F i w ∈ U i := by
    intro i w hw
    apply hεU i
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr i)]
    change ε i / 2 * ‖w‖ < ε i
    have h := mul_lt_mul_of_pos_left hw (half_pos (hε i))
    linarith
  have hFemb : ∀ i, Topology.IsOpenEmbedding (F i) := by
    intro i
    exact (k24_mobiusSLHomeo (slRealToComplex (H i))).isOpenEmbedding.comp
      (OnePoint.isOpenEmbedding_coe.comp (Homeomorph.mulLeft₀ (r i : ℂ) (hrC i)).isOpenEmbedding)
  let e : Fin k → OpenPartialHomeomorph ℂ ExtPlane := fun i =>
    ((hFemb i).toOpenPartialHomeomorph (F i)).restrOpen (ball (0 : ℂ) 2) isOpen_ball
  have heapp : ∀ i w, e i w = F i w := by intro i w; rfl
  have hesrc : ∀ i, (e i).source = ball (0 : ℂ) 2 := by
    intro i
    change univ ∩ ball (0 : ℂ) 2 = ball (0 : ℂ) 2
    exact univ_inter _
  have hetarget : ∀ i, (e i).target ⊆ U i := by
    intro i p hp
    have hs := (e i).map_target hp
    rw [hesrc i] at hs
    have hu := hFU i ((e i).symm p) (mem_ball_zero_iff.mp hs)
    rw [← heapp, (e i).right_inv hp] at hu
    exact hu
  have havoid : ∀ i w, w ≠ 0 → ‖w‖ < 2 →
      ¬ ((∃ γ ∈ Γ, ∃ s ∈ E, F i w = mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane)) ∨
        ∃ γ ∈ Γ, F i w = mobiusSL (slRealToComplex γ) extInf) := by
    intro i w hw hw2 hdel
    have heq := hUdel i (F i w) (hFU i w hw2) hdel
    exact hw ((hFemb i).injective (heq.trans (hF0 i).symm))
  have hden : ∀ i w, w ≠ 0 → ‖w‖ < 2 →
      ((H i) 1 0 : ℂ) * ((r i : ℂ) * w) + (H i) 1 1 ≠ 0 := by
    intro i w hw hw2 hd
    have hi : F i w = extInf := s36x_msl_inf (H i) hd
    apply havoid i w hw hw2
    refine Or.inr ⟨1, Γ.one_mem, ?_⟩
    rw [k24_slReal_one, k24_mobiusSL_one]
    exact hi
  let ζ : Fin k → ℂ → ℂ := fun i w => h36p_m (H i) ((r i : ℂ) * w)
  have hζcoe : ∀ i w, w ≠ 0 → ‖w‖ < 2 → (ζ i w : ExtPlane) = F i w := by
    intro i w hw hw2
    exact (s36x_msl_coe (H i) (hden i w hw hw2)).symm
  have hζΩ : ∀ i w, w ≠ 0 → ‖w‖ < 2 → ζ i w ∈ Ω := by
    intro i w hw hw2
    apply (hΩ (ζ i w)).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [hζcoe i w hw hw2]
      exact (hUO i (hFU i w hw2)).2
    · intro γ hγ s hs hd heq
      have hdC : (γ 1 0 : ℂ) * (s : ℂ) + γ 1 1 ≠ 0 := by exact_mod_cast hd
      have hm : mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane) =
          ((h36p_m γ (s : ℂ) : ℂ) : ExtPlane) := s36x_msl_coe γ hdC
      apply havoid i w hw hw2
      exact Or.inl ⟨γ, hγ, s, hs, (hζcoe i w hw hw2).symm.trans
        ((congrArg (fun z : ℂ => (z : ExtPlane)) heq).trans hm.symm)⟩
    · intro γ hγ hc heq
      have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
      have hm : mobiusSL (slRealToComplex γ) extInf =
          (((γ 0 0 / γ 1 0 : ℝ) : ℂ) : ExtPlane) := by
        rw [k24_mobiusSL_real, mobiusExt_infty_of_ne hcC]
        congr 1
        exact (Complex.ofReal_div _ _).symm
      apply havoid i w hw hw2
      exact Or.inr ⟨γ, hγ, (hζcoe i w hw hw2).symm.trans
        ((congrArg (fun z : ℂ => (z : ExtPlane)) heq).trans hm.symm)⟩
  refine ⟨e, ζ, ?_, hesrc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (heapp i 0).trans (hF0 i)
  · intro i p hp
    exact (hUO i (hetarget i hp)).1
  · intro i p hp
    exact (hUO i (hetarget i hp)).2
  · intro i p hp hdel
    exact hUdel i p (hetarget i hp) hdel
  · intro i j γ hγ hmeet
    obtain ⟨p, ⟨z, hz, heq⟩, hp⟩ := hmeet
    exact hUprec i j γ hγ ⟨p, ⟨z, hetarget i hz, heq⟩, hetarget j hp⟩
  · intro i w hw hw2
    exact ⟨hζΩ i w hw hw2, (hζcoe i w hw hw2).trans (heapp i w).symm⟩
  · intro i w hw
    have hd := (s36x_m_hasDerivAt (H i) (hden i w hw.1 hw.2)).differentiableAt
    have hl : DifferentiableAt ℂ (fun w : ℂ => (r i : ℂ) * w) w :=
      differentiableAt_id.const_mul (r i : ℂ)
    exact (hd.comp w hl).differentiableWithinAt

end LiZhongQC
