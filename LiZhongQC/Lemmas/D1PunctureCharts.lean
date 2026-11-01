import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.D1OrdinarySeparation
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D1 P producer: actual puncture charts and escape, with no stub imports. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- P. Construct the k puncture charts by P composed with the finite lifts.
The escape conclusion uses local quotient sheets and proper discontinuity; it is
not inferred from open embeddings alone. No F1 data is consumed. -/
theorem s36d1_puncture_charts {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
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
    (hehol : ∀ i, DifferentiableOn ℂ (ζ i) {w | w ≠ 0 ∧ ‖w‖ < 2}) :
    ∃ ψ : Fin k → ℂ → S, (∀ i w, w ≠ 0 → ‖w‖ < 1 → ψ i w = P (ζ i w)) ∧
      (∀ i, InjOn (ψ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ψ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (ψ i '' V)) ∧
      (∀ i j, i ≠ j →
      Disjoint (ψ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (ψ j '' {w | w ≠ 0 ∧ ‖w‖ < 1})) ∧
      (∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i w, w ≠ 0 → ‖w‖ < 1 → ψ i w ∈ N → δ ≤ ‖w‖) := by
  classical
  -- Completeness and the extra isolated-target certificates are used by I/K;
  -- P needs the seed locations, holomorphic lifts and precise invariance.
  have _ := hE
  have _ := hsep
  have _ := hcomplete
  have _ := heord
  have _ := hedel
  let D : Set ℂ := {w | w ≠ 0 ∧ ‖w‖ < 1}
  have hsrc : ∀ i w, w ∈ D → w ∈ (e i).source := by
    intro i w hw
    rw [hesrc i]
    exact mem_ball_zero_iff.mpr (hw.2.trans (by norm_num))
  have hlift : ∀ i w, w ∈ D →
      ζ i w ∈ Ω ∧ (ζ i w : ExtPlane) = e i w := by
    intro i w hw
    exact heeq i w hw.1 (hw.2.trans (by norm_num))
  have hact := (s36a_omega hΓ hΩ).2.2
  have hPdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) P Ω := by
    intro z hz
    obtain ⟨d, hzd, hdΩ, hPd, hd, hdi⟩ := hPloc z hz
    have hevent : P =ᶠ[𝓝 z] d := by
      filter_upwards [d.open_source.mem_nhds hzd] with w hw
      exact hPd hw
    exact ((hd.mdifferentiableAt (d.open_source.mem_nhds hzd)).congr_of_eventuallyEq
      hevent).mdifferentiableWithinAt
  have hPopen : ∀ W : Set ℂ, IsOpen W → W ⊆ Ω → IsOpen (P '' W) := by
    intro W hWo hWΩ
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨d, hzd, hdΩ, hPd, hd, hdi⟩ := hPloc z (hWΩ hz)
    have hop : IsOpen (d '' (W ∩ d.source)) :=
      d.isOpen_image_of_subset_source (hWo.inter d.open_source) inter_subset_right
    have hmem : P z ∈ d '' (W ∩ d.source) :=
      ⟨z, ⟨hz, hzd⟩, (hPd hzd).symm⟩
    apply Filter.mem_of_superset (hop.mem_nhds hmem)
    rintro y ⟨w, hw, rfl⟩
    exact ⟨w, hw.1, hPd hw.2⟩
  have hζopen : ∀ i (W : Set ℂ), IsOpen W → W ⊆ D → IsOpen (ζ i '' W) := by
    intro i W hWo hWD
    have hop : IsOpen (e i '' W) :=
      (e i).isOpen_image_of_subset_source hWo (fun w hw => hsrc i w (hWD hw))
    have heq : ζ i '' W = ((↑) : ℂ → ExtPlane) ⁻¹' (e i '' W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, ((hlift i w (hWD hw)).2).symm⟩
      · rintro ⟨w, hw, hew⟩
        exact ⟨w, hw, OnePoint.coe_injective (((hlift i w (hWD hw)).2).trans hew)⟩
    rw [heq]
    exact hop.preimage OnePoint.continuous_coe
  have hrel : ∀ i j w w', w ∈ D → w' ∈ D → P (ζ i w) = P (ζ j w') →
      i = j ∧ ∃ γ ∈ Γ, (γ = 1 ∨ γ = -1) ∧ ζ j w' = h36p_m γ (ζ i w) := by
    intro i j w w' hw hw' hP
    obtain ⟨γ, hγ, heq⟩ :=
      (hPfib (ζ i w) (hlift i w hw).1 (ζ j w') (hlift j w' hw').1).mp hP
    have hm : mobiusSL (slRealToComplex γ) (e i w) = e j w' := by
      rw [← (hlift i w hw).2, ← (hlift j w' hw').2]
      have hm' : mobiusSL (slRealToComplex γ) (ζ i w : ExtPlane) =
          ((h36p_m γ (ζ i w) : ℂ) : ExtPlane) :=
        s36x_msl_coe γ (hact γ hγ (ζ i w) (hlift i w hw).1).1
      exact hm'.trans (congrArg (fun z : ℂ => (z : ExtPlane)) heq.symm)
    obtain ⟨hij, hsign⟩ := heprec i j γ hγ
      ⟨e j w', ⟨e i w, (e i).map_source (hsrc i w hw), hm⟩,
        (e j).map_source (hsrc j w' hw')⟩
    exact ⟨hij, γ, hγ, hsign, heq⟩
  refine ⟨(fun i w => P (ζ i w)), ?_, ?_, ?_, ?_⟩
  · intro i w hw hw1
    rfl
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro w hw w' hw' heq
      obtain ⟨hii, γ, hγ, hsign, hζ⟩ := hrel i i w w' hw hw' heq
      have hζeq : ζ i w' = ζ i w := by
        rcases hsign with rfl | rfl
        · simpa only [h36p_a_m_one] using hζ
        · simpa only [h36p_a_m_neg, h36p_a_m_one] using hζ
      apply (e i).injOn (hsrc i w hw) (hsrc i w' hw')
      exact ((hlift i w hw).2).symm.trans
        ((congrArg (fun z : ℂ => (z : ExtPlane)) hζeq.symm).trans (hlift i w' hw').2)
    · change MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (P ∘ ζ i) D
      exact hPdiff.comp ((hehol i).mono (by exact fun w hw => ⟨hw.1, hw.2.trans (by norm_num)⟩)).mdifferentiableOn
        (fun w hw => (hlift i w hw).1)
    · intro W hWo hWD
      have hop := hPopen (ζ i '' W) (hζopen i W hWo hWD) (by
        rintro z ⟨w, hw, rfl⟩
        exact (hlift i w (hWD hw)).1)
      simpa only [Set.image_image, Function.comp_apply] using hop
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨w, hw, hew⟩ ⟨w', hw', hew'⟩
    exact hij (hrel i j w w' hw hw' (hew.trans hew'.symm)).1
  · intro x
    have hx : x ∈ P '' Ω := by rw [hPsurj]; exact mem_univ x
    obtain ⟨v, hv, hPv⟩ := hx
    have hnotseed : ∀ i z, z ∈ Ω → (z : ExtPlane) ≠ a i := by
      intro i z hz heq
      rcases hseed i with hinf | ⟨s, hs, has⟩
      · exact OnePoint.coe_ne_infty z (heq.trans hinf)
      · have hzs : z = (s : ℂ) := OnePoint.coe_injective (heq.trans has)
        exact ((hΩ z).mp hz).2.1 1 Γ.one_mem s hs (by norm_num)
          (hzs.trans (h36p_a_m_one (s : ℂ)).symm)
    have horbit : ∀ i γ, γ ∈ Γ →
        mobiusSL (slRealToComplex γ) (a i) ≠ (v : ExtPlane) := by
      intro i γ hγ heq
      have hback : a i = mobiusSL (slRealToComplex γ⁻¹) (v : ExtPlane) := by
        calc
          a i = mobiusSL (slRealToComplex γ⁻¹)
              (mobiusSL (slRealToComplex γ) (a i)) := by
            rw [k24_slReal_inv, k24_mobiusSL_inv_apply]
          _ = mobiusSL (slRealToComplex γ⁻¹) (v : ExtPlane) := congrArg _ heq
      have hvi := hact γ⁻¹ (Γ.inv_mem hγ) v hv
      have hm : mobiusSL (slRealToComplex γ⁻¹) (v : ExtPlane) =
          ((h36p_m γ⁻¹ v : ℂ) : ExtPlane) := s36x_msl_coe γ⁻¹ hvi.1
      exact hnotseed i (h36p_m γ⁻¹ v) hvi.2 (hback.trans hm).symm
    have hseparate : ∀ i, ∃ U ∈ 𝓝 (a i), ∃ V ∈ 𝓝 (v : ExtPlane),
        ∀ γ ∈ Γ, Disjoint (mobiusSL (slRealToComplex γ) '' U) V := by
      intro i
      exact s36d1_ordinary_orbit_separation hΓ (hord i).2 ((hΩ v).mp hv).1 (horbit i)
    choose U hU V hV hUV using hseparate
    let W : Set ℂ := ⋂ i, ((↑) : ℂ → ExtPlane) ⁻¹' V i
    have hW : W ∈ 𝓝 v :=
      iInter_mem.mpr (fun i => OnePoint.continuous_coe.continuousAt (hV i))
    obtain ⟨d, hvd, hdΩ, hPd, hd, hdi⟩ := hPloc v hv
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hW (d.open_source.mem_nhds hvd))
    have hballΩ : ball v ε ⊆ Ω := fun z hz => hdΩ (hεW hz).2
    have hN : P '' ball v ε ∈ 𝓝 x := by
      rw [← hPv]
      exact (hPopen (ball v ε) isOpen_ball hballΩ).mem_nhds
        ⟨v, mem_ball_self hε, rfl⟩
    have hevent : ∀ᶠ w : ℂ in 𝓝 0, ∀ i, e i w ∈ U i := by
      apply Filter.eventually_all.mpr
      intro i
      have h0 : (0 : ℂ) ∈ (e i).source := by
        rw [hesrc i]
        exact mem_ball_self (by norm_num)
      have hc : ContinuousAt (e i) 0 :=
        (e i).continuousOn.continuousAt ((e i).open_source.mem_nhds h0)
      apply hc
      rw [he0 i]
      exact hU i
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hevent
    refine ⟨P '' ball v ε, hN, δ, hδ, ?_⟩
    intro i w hw hw1 hwN
    by_contra hδw
    have hwδ : ‖w‖ < δ := lt_of_not_ge hδw
    have hwU : e i w ∈ U i := hδU (mem_ball_zero_iff.mpr hwδ) i
    obtain ⟨y, hy, hPy⟩ := hwN
    have hyV : (y : ExtPlane) ∈ V i := mem_iInter.mp (hεW hy).1 i
    obtain ⟨γ, hγ, heq⟩ :=
      (hPfib (ζ i w) (hlift i w ⟨hw, hw1⟩).1 y (hballΩ hy)).mp hPy.symm
    have hm : mobiusSL (slRealToComplex γ) (e i w) = (y : ExtPlane) := by
      rw [← (hlift i w ⟨hw, hw1⟩).2]
      have hm' : mobiusSL (slRealToComplex γ) (ζ i w : ExtPlane) =
          ((h36p_m γ (ζ i w) : ℂ) : ExtPlane) :=
        s36x_msl_coe γ (hact γ hγ (ζ i w) (hlift i w ⟨hw, hw1⟩).1).1
      exact hm'.trans (congrArg (fun z : ℂ => (z : ExtPlane)) heq.symm)
    exact Set.disjoint_left.mp (hUV i γ hγ) ⟨e i w, hwU, hm⟩ hyV

end LiZhongQC
