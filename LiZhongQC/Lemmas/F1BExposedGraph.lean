import LiZhongQC.Lemmas.F1BExposedGeometry
import LiZhongQC.Lemmas.F1BGraphBasic
import LiZhongQC.Lemmas.F1BCircleArcs
import LiZhongQC.Lemmas.F1BEndpointIncidence

/-!
# F1 B2: the exposed transition graph `ft1gb_exposed_transition_graph`

Assembly of B2a/B2b (F1BCircleArcs) and B2c (F1BEndpointIncidence) with B1 (F1BExposedGeometry) and
the graph algebra (F1BGraphBasic). The statement is byte-identical to F1BExteriorsIface_v1 (23fa91aa).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- B2. Construct exposed arcs on the central orbit circle and the actual finite
successor permutation with SL(2,R) transition labels. Whole-circle isolation is excluded
by nontriviality, connectedness and free action, not silently treated as an embedded interval. -/
theorem ft1gb_exposed_transition_graph (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hnt : ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1)
    (R : ℝ) (hR : 0 < R) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hUc : IsClosed U) (hUconn : IsConnected U)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
      dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2) :
    ∃ (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
      (σ : Equiv.Perm (Fin n))
      (d : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R) ∧
      ((∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ frontier U) ∧
      frontier U = (⋃ γ ∈ Γ, ⋃ i, (fun τ : UpperHalfPlane => γ • τ) '' Set.range (a i)) ∧
      (∀ i j γ, γ ∈ Γ → ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
        ∀ s : unitInterval, γ • a i t = a j s →
          i = j ∧ (γ = 1 ∨ γ = -1) ∧ t = s) ∧
      (∀ i, d i ∈ Γ ∧ a i 1 = d i • a (σ i) 0) ∧
      (∀ i j γ, γ ∈ Γ → a i 1 = γ • a j 0 →
        j = σ i ∧ (γ = d i ∨ γ = -d i))) := by
  -- The noncentrality input is retained from the frozen contract. B2a explicitly
  -- subdivides full circles as well; no nontrivial whole circle is treated as an interval.
  have _hnt := hnt
  obtain ⟨V, hV, hfront, hflat⟩ :=
    ft1gb_exposed_frontier hΓ hfree R hR hU hUc hUconn hUi hLf hpair hlevel
  obtain ⟨m, a, _, _, hshape, hcover, hsep, havoid⟩ :=
    ft1gb_circle_subdivision R hR V (fun p hp => ((hV p).1 hp).1)
  obtain ⟨n, j, haF, hcentral⟩ :=
    ft1gb_select_exposed_arcs hR hU hLf hpair hlevel hfront V hV
      m a hshape hsep havoid hcover
  let b : Fin n → unitInterval → UpperHalfPlane := fun i => a (j i)
  have hshapeB : ∀ i, Topology.IsEmbedding (b i) ∧
      Set.range (b i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (b i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ) := fun i => hshape (j i)
  have hsepB : ∀ i k (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      b i t = b k s → i = k ∧ t = s := by
    intro i k t s ht0 ht1 heq
    obtain ⟨hik, hts⟩ := hsep (j i) (j k) t s ht0 ht1 heq
    exact ⟨j.injective hik, hts⟩
  have havoidB : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → b i t ∉ V :=
    fun i => havoid (j i)
  obtain ⟨hout, hin⟩ := ft1gb_oriented_endpoint_incidence hfree hR hU hLf hpair hlevel
    hUi hUc hfront hflat V hV n b hshapeB hsepB havoidB haF hcentral
  obtain ⟨σ, d, hd, huniq⟩ := ft1gb_successor_of_incidence n b hout hin
  have hglobal := ft1gb_translate_central_frontier R hUi
    (fun p hp => (ft1gb_frontier_distances R hU hUc hp).1) n b haF hcentral
  have hrigid := ft1gb_arc_interior_rigidity hfree R V hV n b
    (fun i => (hshapeB i).2.1) havoidB hsepB
  refine ⟨n, b, σ, d, fun i => (hshapeB i).2.1, ?_, hglobal, hrigid, hd, huniq⟩
  intro i
  exact ⟨(hshapeB i).1, haF i⟩

end LiZhongQC
