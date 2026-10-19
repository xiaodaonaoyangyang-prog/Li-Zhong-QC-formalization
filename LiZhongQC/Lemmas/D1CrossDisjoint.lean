import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D1 X producer: puncture chart images are disjoint from both cusp families.
Uses only the quotient fibres, the avoidance set V, and the actual cusp ranges. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- X. Cross-disjointness of the ordinary puncture charts and the two cusp
families. Use the spherical avoidance neighborhood and the actual ranges of both
families, together with the quotient-fibre description; no end-identification
assumption is added. -/
theorem s36d1_cross_disjoint {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
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
    {k c : ℕ} (A : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (e : Fin k → OpenPartialHomeomorph ℂ ExtPlane) (ζ : Fin k → ℂ → ℂ)
    (hesrc : ∀ i, (e i).source = ball (0 : ℂ) 2)
    (heeq : ∀ i w, w ≠ 0 → ‖w‖ < 2 → ζ i w ∈ Ω ∧ (ζ i w : ExtPlane) = e i w)
    (V : Set ExtPlane) (heV : ∀ i, (e i).target ⊆ V)
    (hVu : Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ i : Fin c, ∃ τ : UpperHalfPlane,
      1 < τ.im ∧ p = (((γ • (A i • τ) : UpperHalfPlane) : ℂ) : ExtPlane)})
    (hVl : Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ i : Fin c, ∃ τ : UpperHalfPlane,
      1 < τ.im ∧ p = ((conj (((γ • (A i • τ)) : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane)})
    (ψ : Fin k → ℂ → S) (hψeq : ∀ i w, w ≠ 0 → ‖w‖ < 1 → ψ i w = P (ζ i w))
    (χ : (Fin c ⊕ Fin c) → ℂ → S) (hχrange : (∀ i w, w ≠ 0 → ‖w‖ < 1 → ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ χ (Sum.inl i) w = P ((A i • τ : UpperHalfPlane) : ℂ)) ∧
      (∀ i w, w ≠ 0 → ‖w‖ < 1 → ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ χ (Sum.inr i) w = P (conj ((A i • τ : UpperHalfPlane) : ℂ)))) :
    ∀ i j, Disjoint (ψ i '' {w | w ≠ 0 ∧ ‖w‖ < 1})
      (χ j '' {w | w ≠ 0 ∧ ‖w‖ < 1}) := by
  -- Surjectivity and local sheets are used by the chart producers; this
  -- disjointness only needs the fibre description and the avoidance set V.
  have _ := hE
  have _ := hPsurj
  have _ := hPloc
  have hup := (s36a_omega hΓ hΩ).1
  intro i j
  rw [Set.disjoint_left]
  rintro x ⟨w, ⟨hw0, hw1⟩, rfl⟩ ⟨w', ⟨hw0', hw1'⟩, hx⟩
  have hw2 : ‖w‖ < 2 := hw1.trans (by norm_num)
  obtain ⟨hζΩ, hζe⟩ := heeq i w hw0 hw2
  have hmemV : ((ζ i w : ℂ) : ExtPlane) ∈ V := by
    rw [hζe]
    apply heV i
    apply (e i).map_source
    rw [hesrc i]
    exact mem_ball_zero_iff.2 hw2
  rw [hψeq i w hw0 hw1] at hx
  rcases j with j | j
  · obtain ⟨τ, hτ, hχ⟩ := hχrange.1 j w' hw0' hw1'
    have hAΩ : ((A j • τ : UpperHalfPlane) : ℂ) ∈ Ω := hup _ (A j • τ).im_pos.ne'
    obtain ⟨γ, hγ, hγeq⟩ := (hPfib _ hAΩ _ hζΩ).1 (hχ.symm.trans hx)
    apply Set.disjoint_left.1 hVu hmemV
    refine ⟨γ, hγ, j, τ, hτ, ?_⟩
    rw [hγeq, h36p_m_coe]
  · obtain ⟨τ, hτ, hχ⟩ := hχrange.2 j w' hw0' hw1'
    have hAΩ : conj ((A j • τ : UpperHalfPlane) : ℂ) ∈ Ω := by
      apply hup
      rw [Complex.conj_im]
      exact neg_ne_zero.2 (A j • τ).im_pos.ne'
    obtain ⟨γ, hγ, hγeq⟩ := (hPfib _ hAΩ _ hζΩ).1 (hχ.symm.trans hx)
    apply Set.disjoint_left.1 hVl hmemV
    refine ⟨γ, hγ, j, τ, hτ, ?_⟩
    have hc : h36p_m γ (conj ((A j • τ : UpperHalfPlane) : ℂ)) =
        conj (h36p_m γ ((A j • τ : UpperHalfPlane) : ℂ)) := b33_e_mobius_conj γ _
    rw [hγeq, hc, h36p_m_coe]

end LiZhongQC
