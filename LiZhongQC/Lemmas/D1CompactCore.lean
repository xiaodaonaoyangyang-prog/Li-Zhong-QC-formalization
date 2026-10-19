import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D1 K producer: compact remainder and puncture-tail coverage. No stub imports. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- K. PRODUCE a compact core from the compact ordinary spherical L and the
isolated puncture charts. Remove from L the OPEN saturation of e_i(ball 0 (1/2)).
The closed remainder is compact and avoids every deleted orbit, including the
orbit of infinity. Transfer it to affine Ω and map by P. This proves both
compactness and the explicit coverage alternative on L; neither is assumed. -/
theorem s36d1_compact_core {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hΓ : IsFuchsian Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {P : ℂ → S} (hPsurj : P '' Ω = univ)
    (hPfib : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPloc : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {k : ℕ} (a : Fin k → ExtPlane)
    (hseed : ∀ i, a i = extInf ∨ ∃ s ∈ E, a i = ((s : ℂ) : ExtPlane)) (hord : ∀ i, a i ∈ ordinarySet Γ)
    (hsep : ∀ i j γ, γ ∈ Γ → mobiusSL (slRealToComplex γ) (a i) = a j → i = j)
    (hcomplete : ∀ p : ExtPlane, p ∈ ordinarySet Γ →
      (p = extInf ∨ ∃ s ∈ E, p = ((s : ℂ) : ExtPlane)) →
      ∃ i, ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) (a i))
    (e : Fin k → OpenPartialHomeomorph ℂ ExtPlane) (ζ : Fin k → ℂ → ℂ)
    (he0 : ∀ i, e i 0 = a i)
    (hesrc : ∀ i, (e i).source = ball (0 : ℂ) 2)
    (heord : ∀ i, (e i).target ⊆ (fuchsianLimitSet Γ)ᶜ)
    (hedel : ∀ i p, p ∈ (e i).target →
      ((∃ γ ∈ Γ, ∃ s ∈ E, p = mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane)) ∨
        ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) extInf) → p = a i)
    (heprec : ∀ i j γ, γ ∈ Γ →
      ((mobiusSL (slRealToComplex γ) '' (e i).target) ∩ (e j).target).Nonempty →
      i = j ∧ (γ = 1 ∨ γ = -1))
    (heeq : ∀ i w, w ≠ 0 → ‖w‖ < 2 → ζ i w ∈ Ω ∧ (ζ i w : ExtPlane) = e i w)
    (hehol : ∀ i, DifferentiableOn ℂ (ζ i) {w | w ≠ 0 ∧ ‖w‖ < 2})
    (ψ : Fin k → ℂ → S) (hψeq : ∀ i w, w ≠ 0 → ‖w‖ < 1 → ψ i w = P (ζ i w))
    (L : Set ExtPlane) (hL : IsCompact L) (hLord : L ⊆ (fuchsianLimitSet Γ)ᶜ) :
    ∃ K : Set S, IsCompact K ∧ (∀ z ∈ Ω, (z : ExtPlane) ∈ L → P z ∈ K ∨
      ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ (1 / 2 : ℝ) ∧ ψ i w = P z) := by
  classical
  -- The core construction needs the extended disks and complete representatives;
  -- precise invariance and holomorphicity have already served the chart producer.
  have _ := hsep
  have _ := heord
  have _ := hedel
  have _ := heprec
  have _ := hehol
  let T : Set ExtPlane := ⋃ g : Γ, ⋃ i : Fin k,
    mobiusSL (slRealToComplex g.val) '' (e i '' ball (0 : ℂ) (1 / 2 : ℝ))
  have hTmem : ∀ p : ExtPlane, p ∈ T ↔
      ∃ γ ∈ Γ, ∃ i : Fin k, ∃ w : ℂ, ‖w‖ < (1 / 2 : ℝ) ∧
        p = mobiusSL (slRealToComplex γ) (e i w) := by
    intro p
    constructor
    · intro hp
      obtain ⟨g, hg⟩ := mem_iUnion.mp hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hg
      obtain ⟨q, ⟨w, hw, rfl⟩, heq⟩ := hi
      exact ⟨g.val, g.property, i, w, mem_ball_zero_iff.mp hw, heq.symm⟩
    · rintro ⟨γ, hγ, i, w, hw, heq⟩
      exact mem_iUnion.mpr ⟨⟨γ, hγ⟩, mem_iUnion.mpr
        ⟨i, ⟨e i w, ⟨w, mem_ball_zero_iff.mpr hw, rfl⟩, heq.symm⟩⟩⟩
  have hTo : IsOpen T := by
    apply isOpen_iUnion
    intro g
    apply isOpen_iUnion
    intro i
    apply (k24_mobiusSLHomeo (slRealToComplex g.val)).isOpenMap
    apply (e i).isOpen_image_of_subset_source isOpen_ball
    intro w hw
    rw [hesrc i]
    exact mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hw).trans (by norm_num))
  have hseedT : ∀ t : ExtPlane, t ∈ ordinarySet Γ →
      (t = extInf ∨ ∃ s ∈ E, t = ((s : ℂ) : ExtPlane)) →
      ∀ γ ∈ Γ, mobiusSL (slRealToComplex γ) t ∈ T := by
    intro t htO htseed γ hγ
    obtain ⟨i, δ, hδ, hti⟩ := hcomplete t htO htseed
    apply (hTmem _).mpr
    refine ⟨γ * δ, Γ.mul_mem hγ hδ, i, 0, by norm_num, ?_⟩
    rw [he0 i, k24_slReal_mul, k24_mobiusSL_mul, ← hti]
  have hdeletedT : ∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ →
      ((∃ γ ∈ Γ, ∃ s ∈ E, p = mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane)) ∨
        ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) extInf) → p ∈ T := by
    intro p hp hdel
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
      exact hp (hpt.symm ▸ hm)
    exact hpt.symm ▸ hseedT t htO htseed γ hγ
  let M : Set ExtPlane := L \ T
  have hM : IsCompact M := hL.diff hTo
  have hMrange : M ⊆ Set.range ((↑) : ℂ → ExtPlane) := by
    intro p hp
    induction p using OnePoint.rec with
    | infty =>
      exfalso
      apply hp.2
      apply hdeletedT extInf (hLord hp.1)
      exact Or.inr ⟨1, Γ.one_mem, by rw [k24_slReal_one, k24_mobiusSL_one]⟩
    | coe z => exact ⟨z, rfl⟩
  let K₀ : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' M
  have hK₀ : IsCompact K₀ :=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage_iff hMrange).mpr hM
  have hKΩ : K₀ ⊆ Ω := by
    intro z hz
    have hzM : (z : ExtPlane) ∈ M := hz
    apply (hΩ z).mpr
    refine ⟨hLord hzM.1, ?_, ?_⟩
    · intro γ hγ s hs hd heq
      have hdC : (γ 1 0 : ℂ) * (s : ℂ) + γ 1 1 ≠ 0 := by exact_mod_cast hd
      have hm : mobiusSL (slRealToComplex γ) ((s : ℂ) : ExtPlane) =
          ((h36p_m γ (s : ℂ) : ℂ) : ExtPlane) := s36x_msl_coe γ hdC
      exact hzM.2 (hdeletedT (z : ExtPlane) (hLord hzM.1)
        (Or.inl ⟨γ, hγ, s, hs, (congrArg (fun w : ℂ => (w : ExtPlane)) heq).trans hm.symm⟩))
    · intro γ hγ hc heq
      have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
      have hm : mobiusSL (slRealToComplex γ) extInf =
          (((γ 0 0 / γ 1 0 : ℝ) : ℂ) : ExtPlane) := by
        rw [k24_mobiusSL_real, mobiusExt_infty_of_ne hcC]
        congr 1
        exact (Complex.ofReal_div _ _).symm
      exact hzM.2 (hdeletedT (z : ExtPlane) (hLord hzM.1)
        (Or.inr ⟨γ, hγ, (congrArg (fun w : ℂ => (w : ExtPlane)) heq).trans hm.symm⟩))
  have hPcont : ContinuousOn P K₀ := by
    intro z hz
    obtain ⟨d, hzd, hdΩ, hPd, hd, hdi⟩ := hPloc z (hKΩ hz)
    have hevent : P =ᶠ[𝓝 z] d := by
      filter_upwards [d.open_source.mem_nhds hzd] with w hw
      exact hPd hw
    exact ((d.continuousOn.continuousAt (d.open_source.mem_nhds hzd)).congr_of_eventuallyEq
      hevent).continuousWithinAt
  have hact := (s36a_omega hΓ hΩ).2.2
  have hnotseed : ∀ i z, z ∈ Ω → (z : ExtPlane) ≠ a i := by
    intro i z hz heq
    rcases hseed i with hinf | ⟨s, hs, has⟩
    · exact OnePoint.coe_ne_infty z (heq.trans hinf)
    · have hzs : z = (s : ℂ) := OnePoint.coe_injective (heq.trans has)
      exact ((hΩ z).mp hz).2.1 1 Γ.one_mem s hs (by norm_num)
        (hzs.trans (h36p_a_m_one (s : ℂ)).symm)
  refine ⟨P '' K₀, hK₀.image_of_continuousOn hPcont, ?_⟩
  intro z hz hzL
  by_cases hzT : (z : ExtPlane) ∈ T
  · obtain ⟨γ, hγ, i, w, hw, hzw⟩ := (hTmem _).mp hzT
    have hw0 : w ≠ 0 := by
      intro hw0
      subst w
      rw [he0 i] at hzw
      have hvi := hact γ⁻¹ (Γ.inv_mem hγ) z hz
      have hback : mobiusSL (slRealToComplex γ⁻¹) (z : ExtPlane) = a i := by
        rw [hzw, k24_slReal_inv, k24_mobiusSL_inv_apply]
      have hm : mobiusSL (slRealToComplex γ⁻¹) (z : ExtPlane) =
          ((h36p_m γ⁻¹ z : ℂ) : ExtPlane) := s36x_msl_coe γ⁻¹ hvi.1
      exact hnotseed i (h36p_m γ⁻¹ z) hvi.2 (hm.symm.trans hback)
    have hw1 : ‖w‖ < 1 := hw.trans (by norm_num)
    have hw2 : ‖w‖ < 2 := hw.trans (by norm_num)
    have hζ := heeq i w hw0 hw2
    have hm : mobiusSL (slRealToComplex γ) (ζ i w : ExtPlane) =
        ((h36p_m γ (ζ i w) : ℂ) : ExtPlane) :=
      s36x_msl_coe γ (hact γ hγ (ζ i w) hζ.1).1
    have hzrep : z = h36p_m γ (ζ i w) :=
      OnePoint.coe_injective (hzw.trans ((congrArg (mobiusSL (slRealToComplex γ))
        hζ.2.symm).trans hm))
    have hP : P (ζ i w) = P z :=
      (hPfib (ζ i w) hζ.1 z hz).mpr ⟨γ, hγ, hzrep⟩
    exact Or.inr ⟨i, w, hw0, hw.le, (hψeq i w hw0 hw1).trans hP⟩
  · exact Or.inl ⟨z, ⟨hzL, hzT⟩, rfl⟩

end LiZhongQC
