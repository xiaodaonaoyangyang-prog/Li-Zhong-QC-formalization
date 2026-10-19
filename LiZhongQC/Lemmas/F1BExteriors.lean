import LiZhongQC.Lemmas.FoundationConnectedCore
import LiZhongQC.Lemmas.F1RegularRadius
import LiZhongQC.Lemmas.F1BExposedGeometry
import LiZhongQC.Lemmas.F1BElementary
import LiZhongQC.Lemmas.F1BExposedGraph
import LiZhongQC.Lemmas.F1BLiftCycles
import LiZhongQC.Lemmas.F1BFillHoles

/-!
# F1 B final assembly: `ft1gb_periodic_exteriors`

B2 (F1BExposedGraph), B4 (F1BLiftCycles) and B6 (F1BFillHoles) are imported; A1/A2/B1/B3/B5/B7 come from accepted
modules. The statement is byte-identical to F1BExteriorsIface_v1 (23fa91aa).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Frozen B endpoint; no additional hypotheses are inserted. -/
theorem ft1gb_periodic_exteriors (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hfg : Γ.FG) :
    (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    ∃ (N : ℕ) (C : Set UpperHalfPlane) (W : Fin N → Set UpperHalfPlane)
      (ρ : Fin N → ℝ → UpperHalfPlane)
      (h : Fin N → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      let U : Set UpperHalfPlane := ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C
      IsCompact C ∧ IsConnected U ∧ IsClosed U ∧
      (∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ Disjoint U (W j) ∧
        frontier (W j) = Set.range (ρ j)) ∧
      (∀ j, Topology.IsEmbedding (ρ j) ∧
        ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact ((ρ j) ⁻¹' L)) ∧
      (∀ j, h j ∈ Γ ∧ h j ≠ 1 ∧ h j ≠ -1 ∧
        (∀ t : ℝ, ρ j (t + 1) = h j • ρ j t) ∧
        (fun τ : UpperHalfPlane => h j • τ) '' W j = W j) ∧
      (∀ i j γ, γ ∈ Γ →
        (((fun τ : UpperHalfPlane => γ • τ) '' W i) ∩ W j).Nonempty →
        i = j ∧ ∃ k : ℤ, γ = h i ^ k ∨ γ = -h i ^ k) ∧
      Uᶜ = ⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' W j := by
  classical
  by_cases htriv : ∀ γ ∈ Γ, γ = 1 ∨ γ = -1
  · exact Or.inl htriv
  right
  right
  have hnt : ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 := by
    push_neg at htriv
    obtain ⟨γ, hγ, h1, h2⟩ := htriv
    exact ⟨γ, hγ, h1, h2⟩
  obtain ⟨R₁, -, hR₁, hA1⟩ := ft1ga_connected_ball_saturation hΓ hfg 0
  obtain ⟨R, hRR₁, hR, hpair, hlevel⟩ := ft1ga_regular_orbit_radius hΓ R₁
  obtain ⟨hK, hUconn, hUc, hUi, hLf⟩ := hA1 R hRR₁
  set U : Set UpperHalfPlane :=
    ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R with hU
  obtain ⟨V, hV, hfront, hflat⟩ :=
    ft1gb_exposed_frontier hΓ hfree R hR hU hUc hUconn hUi hLf hpair hlevel
  obtain ⟨n, a, σ, d, -, hgraph⟩ :=
    ft1gb_exposed_transition_graph hΓ hfree hnt R hR hU hUc hUconn hUi hLf hpair hlevel
  obtain ⟨L, N, κ, ρ, h, hcurves, -⟩ :=
    ft1gb_lift_boundary_cycles hΓ hfree hUc hUconn hUi hflat n a σ d hgraph
  have hUb : ¬ Bornology.IsBounded U := by
    intro hb
    have hUn : U.Nonempty := hUconn.nonempty
    exact (by
      obtain ⟨γ, hγ, h1, h2⟩ := hnt
      rcases ft1gb_bounded_invariant_trivial hΓ hfree hUn hb hUi γ hγ with h | h
      · exact h1 h
      · exact h2 h)
  obtain ⟨H, C, W, hH, hC, hCc, hU₁conn, hU₁c, hU₁i, -, hW, hcompl⟩ :=
    ft1gb_fill_compact_holes hΓ hfree hK rfl hUc hUconn hUb hUi hflat L N κ ρ h hcurves
  obtain ⟨-, hρ, hhper, -, hprim, -, -⟩ := hcurves
  obtain ⟨hWi, hWint⟩ := ft1gb_exterior_stabilizers hU₁i N W ρ h hW
    (fun j => ⟨(hhper j).1, (hhper j).2.2.2⟩) hprim
  refine ⟨N, C, W, ρ, h, hCc, hU₁conn, hU₁c, fun j => ⟨(hW j).1, (hW j).2.1, (hW j).2.2.1,
    (hW j).2.2.2.1⟩, fun j => ⟨(hρ j).1, (hρ j).2.1⟩, fun j => ⟨(hhper j).1, (hhper j).2.1,
    (hhper j).2.2.1, (hhper j).2.2.2, hWi j⟩, hWint, hcompl⟩

end LiZhongQC
