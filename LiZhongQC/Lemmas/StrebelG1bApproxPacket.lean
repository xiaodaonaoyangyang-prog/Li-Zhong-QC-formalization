import LiZhongQC.Ch11.S36_Hamilton
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Calculus.Deriv.Star
import LiZhongQC.Lemmas.StrebelGammaBounds
import LiZhongQC.Lemmas.StrebelDoubleDomain
import LiZhongQC.Lemmas.S36BersRepairApprox
import LiZhongQC.Lemmas.S36BersRepairTheta

/-! Approved approximation-packet contract. Source-only proof, not compiled.
The split Bers producers are owned by worker4 and staged by Root. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

theorem s36a_approx_packet (hΓ : IsFuchsian Γ)
    (hsecond : (ordinarySet Γ).Nonempty) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε < ⊤) :
    ∃ (E : Finset ℝ) (Ω : Set ℂ) (ψ : ℂ → ℂ),
      (∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ) ∧
      (∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
        ∀ i ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ j ∈ ({e₁, e₂, e₃} : Finset ℝ),
          ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 →
            h36p_m γ (i : ℂ) = (j : ℂ) → i = j) ∧
      (∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
        (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
        (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) ∧
      DifferentiableOn ℂ ψ Ω ∧
      (∀ γ ∈ Γ, ∀ z ∈ Ω, ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z) ∧
      ψ ∈ integrableAutomorphicQD Γ F ∧
      (fun z => conj (ψ (conj z))) ∈ integrableAutomorphicQD Γ F ∧
      phiArea (φ - ψ) F < ε ∧
      phiArea (fun z => conj (ψ (conj z))) F < ε ∧
      phiArea ψ F ≤ phiArea φ F + ε ∧
      phiArea φ F ≤ phiArea ψ F + ε := by
  classical
  let D : Set ℝ := {x : ℝ | (((x : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ}
  have hD : Dense D := s36a_ordinary_dense hΓ hsecond
  obtain ⟨x₀, hx₀R, hx₀O⟩ := hsecond
  have hclosed : IsClosed (fuchsianLimitSet Γ) := by
    have heq : fuchsianLimitSet Γ =
        k22_t_orbitLim (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) x₀ :=
      (k22_t_limitSet_subset_orbitLim hx₀O).antisymm (k22_t_orbitLim_subset x₀)
    rw [heq]
    exact k22_t_orbitLim_closed ⟨x₀, hx₀O⟩ x₀
  have hDo : IsOpen D :=
    (hclosed.preimage (OnePoint.continuous_coe.comp Complex.continuous_ofReal)).isOpen_compl
  have hDn : D.Nonempty := hD.nonempty
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  let M : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)
  let embed : ℝ → ExtPlane := fun x => ((x : ℂ) : ExtPlane)
  have hembed : Function.Injective embed :=
    OnePoint.coe_injective.comp Complex.ofReal_injective
  let O : ℝ → Set ℝ := fun x =>
    embed ⁻¹' Set.range (fun γ : Γ => mobiusSL (M γ.1) (embed x))
  have hOc : ∀ x : ℝ, (O x).Countable := fun x =>
    (Set.countable_range (fun γ : Γ => mobiusSL (M γ.1) (embed x))).preimage hembed
  have hself : ∀ x : ℝ, x ∈ O x := by
    intro x
    refine ⟨⟨1, Γ.one_mem⟩, ?_⟩
    change mobiusSL (M 1) (embed x) = embed x
    rw [map_one, k22_t_mobiusSL_one]
  have hrev : ∀ x y : ℝ, y ∈ O x → x ∈ O y := by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := hxy
    refine ⟨γ⁻¹, ?_⟩
    change mobiusSL (M (γ.1⁻¹)) (embed y) = embed x
    rw [map_inv, ← hγ, k22_t_mobiusSL_inv_apply]
  obtain ⟨a, ha⟩ := id hDn
  obtain ⟨b, hb, hba⟩ := ((hOc a).dense_compl ℝ).inter_open_nonempty D hDo hDn
  obtain ⟨c, hc, hcO⟩ := (((hOc a).union (hOc b)).dense_compl ℝ).inter_open_nonempty D hDo hDn
  have hca : c ∉ O a := fun h => hcO (Or.inl h)
  have hcb : c ∉ O b := fun h => hcO (Or.inr h)
  have hab : a ≠ b := by
    intro h
    apply hba
    rw [← h]
    exact hself a
  have hac : a ≠ c := by
    intro h
    apply hca
    rw [← h]
    exact hself a
  have hbc : b ≠ c := by
    intro h
    apply hcb
    rw [← h]
    exact hself b
  have horbits : ∀ i ∈ ({a, b, c} : Finset ℝ), ∀ j ∈ ({a, b, c} : Finset ℝ),
      ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 →
        h36p_m γ (i : ℂ) = (j : ℂ) → i = j := by
    intro i hi j hj γ hγ hden heq
    have hji : j ∈ O i := by
      refine ⟨⟨γ, hγ⟩, ?_⟩
      change mobiusSL (M γ) (embed i) = embed j
      rw [s36a_mext γ (by exact_mod_cast hden), heq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · rfl
    · exact (hba hji).elim
    · exact (hca hji).elim
    · exact (hba (hrev _ _ hji)).elim
    · rfl
    · exact (hcb hji).elim
    · exact (hca (hrev _ _ hji)).elim
    · exact (hcb (hrev _ _ hji)).elim
    · rfl
  obtain ⟨T, w, hT, hclose, hsmall₀⟩ :=
    s36b_bers_two_sided hΓ hF hD hab hac hbc hφ hε
  let E : Finset ℝ := {a, b, c} ∪ T
  let Ω : Set ℂ := {z : ℂ | ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
    (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
    (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))}
  let ψ : ℂ → ℂ := fun z => ∑ t ∈ T, w t *
    h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z
  have hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    · exact (hT e he).1
  have haE : a ∈ E := Finset.mem_union_left _ (by simp)
  have hbE : b ∈ E := Finset.mem_union_left _ (by simp)
  have hcE : c ∈ E := Finset.mem_union_left _ (by simp)
  have hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))) := fun _ => Iff.rfl
  have hterm : ∀ t ∈ T,
      DifferentiableOn ℂ (h36p_theta Γ
        (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) Ω ∧
      ∀ γ ∈ Γ, ∀ z ∈ Ω, h36p_theta Γ
        (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (h36p_m γ z) /
          ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z := by
    intro t ht
    let Ωt : Set ℂ := {z : ℂ | ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ ({a, b, c, t} : Finset ℝ),
        (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))}
    have hsub : Ω ⊆ Ωt := by
      intro z hz
      refine ⟨hz.1, fun γ hγ s hs hden => ?_, hz.2.2⟩
      apply hz.2.1 γ hγ s
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl | rfl
        · exact haE
        · exact hbE
        · exact hcE
        · exact Finset.mem_union_right _ ht
      · exact hden
    obtain ⟨hd, hΓt⟩ := s36x_theta_mero hΓ hab hac hbc (hT t ht).2.1
      (hT t ht).2.2.1 (hT t ht).2.2.2 (Ω := Ωt) (fun _ => Iff.rfl)
    exact ⟨hd.mono hsub, fun γ hγ z hz => hΓt γ hγ z (hsub hz)⟩
  have hψd : DifferentiableOn ℂ ψ Ω := by
    exact DifferentiableOn.fun_sum fun t ht => (hterm t ht).1.const_mul (w t)
  have hψΓ : ∀ γ ∈ Γ, ∀ z ∈ Ω,
      ψ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z := by
    intro γ hγ z hz
    change (∑ t ∈ T, w t *
      h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (h36p_m γ z)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_div_assoc, (hterm t ht).2 γ hγ z hz]
  obtain ⟨hΩH, hΩc, -⟩ := s36a_omega hΓ hΩ
  have hψup : DifferentiableOn ℂ ψ upperHalf :=
    hψd.mono fun z hz => hΩH z (ne_of_gt hz)
  have hψlo : DifferentiableOn ℂ ψ lowerHalf :=
    hψd.mono fun z hz => hΩH z (ne_of_lt hz)
  have hψsd : DifferentiableOn ℂ (fun z => conj (ψ (conj z))) upperHalf := by
    intro z hz
    have hcz : conj z ∈ lowerHalf := by
      show (conj z).im < 0
      rw [Complex.conj_im]
      exact neg_neg_of_pos hz
    have hd := (hψlo.differentiableAt (isOpen_lowerHalf.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at hd
    exact hd.differentiableWithinAt
  have hψsΓ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      conj (ψ (conj (h36p_m γ z))) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        conj (ψ (conj z)) := by
    intro γ hγ z hz
    have h := congrArg conj (hψΓ γ hγ (conj z) (hΩc z (hΩH z (ne_of_gt hz))))
    have hmc : h36p_m γ (conj z) = conj (h36p_m γ z) := b33_e_mobius_conj γ z
    rw [hmc, map_div₀, map_pow] at h
    rw [← h]
    have hden : conj ((γ 1 0 : ℂ) * conj z + γ 1 1) = (γ 1 0 : ℂ) * z + γ 1 1 := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_conj]
    rw [hden]
  -- Norm transfer uses a measurable extension on the two nonreal halves only.
  let U : Set ℂ := {z : ℂ | z.im ≠ 0}
  have hUo : IsOpen U := isOpen_ne_fun continuous_im continuous_const
  have hψU : ContinuousOn ψ U := (hψd.mono hΩH).continuousOn
  let W : ℂ → ℝ≥0∞ := U.piecewise (fun z => ENNReal.ofReal ‖ψ z‖) (fun _ => 0)
  have hWm : Measurable W :=
    ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn (continuous_norm.comp_continuousOn hψU))
      continuousOn_const hUo.measurableSet
  have hW : ∀ z ∈ U, W z = ENNReal.ofReal ‖ψ z‖ := fun z hz =>
    Set.piecewise_eq_of_mem _ _ _ hz
  have hconjF : ((starRingEnd ℂ) '' F : Set ℂ) = (fun z : ℂ => conj z) ⁻¹' F := by
    ext z
    constructor
    · rintro ⟨w₀, hw₀, rfl⟩
      show conj (conj w₀) ∈ F
      rw [Complex.conj_conj]
      exact hw₀
    · intro hz
      exact ⟨conj z, hz, Complex.conj_conj z⟩
  have hconjFm : MeasurableSet ((starRingEnd ℂ) '' F) := by
    rw [hconjF]
    exact Complex.continuous_conj.measurable hF.2.1
  have hpre : (fun z : ℂ => conj z) ⁻¹' ((starRingEnd ℂ) '' F) = F := by
    rw [hconjF]
    ext z
    simp only [mem_preimage, Complex.conj_conj]
  have hnormmirror : phiArea (fun z => conj (ψ (conj z))) F =
      phiArea ψ ((starRingEnd ℂ) '' F) := by
    have hchange := gzE_conj_measurePreserving.setLIntegral_comp_preimage hconjFm hWm
    rw [hpre] at hchange
    change (∫⁻ z in F, ENNReal.ofReal ‖conj (ψ (conj z))‖) =
      ∫⁻ z in (starRingEnd ℂ) '' F, ENNReal.ofReal ‖ψ z‖
    simp only [Complex.norm_conj]
    calc
      (∫⁻ z in F, ENNReal.ofReal ‖ψ (conj z)‖) = ∫⁻ z in F, W (conj z) := by
        refine setLIntegral_congr_fun hF.2.1 fun z hz => ?_
        symm
        apply hW
        show (conj z).im ≠ 0
        rw [Complex.conj_im]
        exact neg_ne_zero.2 (ne_of_gt (hF.1 hz))
      _ = ∫⁻ z in (starRingEnd ℂ) '' F, W z := hchange
      _ = _ := by
        refine setLIntegral_congr_fun hconjFm fun z hz => ?_
        obtain ⟨v, hv, rfl⟩ := hz
        apply hW
        show (conj v).im ≠ 0
        rw [Complex.conj_im]
        exact neg_ne_zero.2 (ne_of_gt (hF.1 hv))
  have hsmall : phiArea (fun z => conj (ψ (conj z))) F < ε := by
    rw [hnormmirror]
    exact hsmall₀
  have hdist : phiArea (φ - ψ) F < ε := hclose
  have hnormest : ∀ f g : ℂ → ℂ,
      DifferentiableOn ℂ f upperHalf → DifferentiableOn ℂ g upperHalf →
      phiArea f F ≤ phiArea g F + phiArea (f - g) F := by
    intro f g hfd hgd
    have hm : AEMeasurable (fun z => ENNReal.ofReal ‖g z‖) (volume.restrict F) :=
      ((hgd.continuousOn.mono hF.1).aestronglyMeasurable hF.2.1).aemeasurable.norm.ennreal_ofReal
    unfold phiArea
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have heq : f z = g z + (f z - g z) := by ring
    calc ‖f z‖ = ‖g z + (f z - g z)‖ := congrArg norm heq
      _ ≤ ‖g z‖ + ‖f z - g z‖ := norm_add_le _ _
  have hreverse : phiArea (ψ - φ) F = phiArea (φ - ψ) F := by
    unfold phiArea
    exact lintegral_congr fun z => by
      simp only [Pi.sub_apply, norm_sub_rev]
  have hupper : phiArea ψ F ≤ phiArea φ F + ε :=
    (hnormest ψ φ hψup hφ.1).trans (by rw [hreverse]; exact add_le_add le_rfl hdist.le)
  have hlower : phiArea φ F ≤ phiArea ψ F + ε :=
    (hnormest φ ψ hφ.1 hψup).trans (add_le_add le_rfl hdist.le)
  have hψfin : phiArea ψ F < ⊤ :=
    hupper.trans_lt (ENNReal.add_lt_top.2 ⟨hφ.2.1, hεfin⟩)
  have hψmem : ψ ∈ integrableAutomorphicQD Γ F :=
    ⟨hψup, hψfin, fun γ hγ z hz => hψΓ γ hγ z (hΩH z (ne_of_gt hz))⟩
  have hψsmem : (fun z => conj (ψ (conj z))) ∈ integrableAutomorphicQD Γ F :=
    ⟨hψsd, hsmall.trans hεfin, hψsΓ⟩
  exact ⟨E, Ω, ψ, hE, ⟨a, haE, b, hbE, c, hcE, hab, hac, hbc, horbits⟩,
    hΩ, hψd, hψΓ, hψmem, hψsmem, hdist, hsmall, hupper, hlower⟩

end LiZhongQC
