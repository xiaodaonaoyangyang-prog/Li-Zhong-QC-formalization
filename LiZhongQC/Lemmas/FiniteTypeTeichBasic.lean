import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

theorem ft_marked_equiv_equivalence {g n m : ℕ} :
    Equivalence (MarkedFiniteTypeRS.Equiv (S₀ := S₀) (g := g) (n := n) (m := m)) := by
  refine ⟨fun a => ?_, fun {a b} h => ?_, fun {a b c} h₁ h₂ => ?_⟩
  · refine ⟨Homeomorph.refl _, isBiholomorphic_id, ?_⟩
    exact ContinuousMap.Homotopic.refl _
  · obtain ⟨c, hc, hh⟩ := h
    refine ⟨c.symm, hc.homeomorph_symm, ?_⟩
    have h1 := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (c.symm : C(b.X.carrier, a.X.carrier))) hh
    have h2 : ((c.symm : C(b.X.carrier, a.X.carrier)).comp
        ((a.marking.trans c : S₀ ≃ₜ b.X.carrier) : C(S₀, b.X.carrier))) =
        (a.marking : C(S₀, a.X.carrier)) := by
      ext x; simp
    have h3 : ((c.symm : C(b.X.carrier, a.X.carrier)).comp (b.marking : C(S₀, b.X.carrier))) =
        ((b.marking.trans c.symm : S₀ ≃ₜ a.X.carrier) : C(S₀, a.X.carrier)) := rfl
    rw [h2, h3] at h1
    exact h1.symm
  · obtain ⟨c₁, hc₁, hh₁⟩ := h₁
    obtain ⟨c₂, hc₂, hh₂⟩ := h₂
    refine ⟨c₁.trans c₂, hc₂.comp hc₁, ?_⟩
    have h4 : ((c₂ : C(b.X.carrier, c.X.carrier)).comp ((a.marking.trans c₁ : S₀ ≃ₜ b.X.carrier) :
        C(S₀, b.X.carrier))) =
        (((a.marking.trans (c₁.trans c₂)) : S₀ ≃ₜ c.X.carrier) : C(S₀, c.X.carrier)) := rfl
    rw [← h4]
    exact (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (c₂ : C(b.X.carrier, c.X.carrier))) hh₁).trans hh₂

theorem ft_quotient_exact {g n m : ℕ} (A C : MarkedFiniteTypeRS S₀ g n m) :
    (Quot.mk _ A : TeichSpaceFiniteType S₀ g n m) = Quot.mk _ C ↔ MarkedFiniteTypeRS.Equiv A C := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    exact (ft_marked_equiv_equivalence.eqvGen_iff).1 h'
  · exact Quot.sound

end LiZhongQC

end
