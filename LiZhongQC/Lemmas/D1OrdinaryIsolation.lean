import LiZhongQC.Lemmas.S36BersOrdinary

/-! Precise finite-family ordinary neighborhoods for D1 I. No stub imports. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Simultaneously shrink finitely many inequivalent ordinary centers. Compact
neighborhoods reduce all possible translated collisions to a finite set; finite
intersections then force a collision to come from an actual center stabilizer.
The stabilizer premise is an internal input supplied from D0, not a new D1 premise. -/
theorem s36d1_precise_ordinary_neighborhoods (hΓ : IsFuchsian Γ)
    {k : ℕ} (a : Fin k → ExtPlane)
    (hord : ∀ i, a i ∉ fuchsianLimitSet Γ)
    (hsep : ∀ i j γ, γ ∈ Γ → mobiusSL (slRealToComplex γ) (a i) = a j → i = j)
    (hfix : ∀ i γ, γ ∈ Γ → mobiusSL (slRealToComplex γ) (a i) = a i →
      γ = 1 ∨ γ = -1)
    (V : Set ExtPlane) (hVo : IsOpen V) (hVa : ∀ i, a i ∈ V) :
    ∃ U : Fin k → Set ExtPlane, (∀ i, U i ∈ 𝓝 (a i)) ∧
      (∀ i, U i ⊆ V ∩ (fuchsianLimitSet Γ)ᶜ) ∧
      ∀ i j γ, γ ∈ Γ → ((mobiusSL (slRealToComplex γ) '' U i) ∩ U j).Nonempty →
        i = j ∧ (γ = 1 ∨ γ = -1) := by
  classical
  have hopen := hVo.inter (s36x_limitSet_closed hΓ).isOpen_compl
  choose K hK haK hKV using fun i => exists_compact_subset hopen ⟨hVa i, hord i⟩
  let C : Set ExtPlane := ⋃ i, K i
  have hC : IsCompact C := isCompact_iUnion hK
  have hCO : ∀ p ∈ C, p ∉ fuchsianLimitSet Γ := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact (hKV i hi).2
  let bad : Set Γ :=
    {γ | (mobiusSL (slRealToComplex γ.val) '' C ∩ C).Nonempty}
  have hbad : bad.Finite := s36x_fin hΓ hC hCO
  have hpair : ∀ i j (g : Γ),
      ∃ u ∈ 𝓝 (mobiusSL (slRealToComplex g.val) (a i)), ∃ v ∈ 𝓝 (a j),
      (mobiusSL (slRealToComplex g.val) (a i) ≠ a j → Disjoint u v) := by
    intro i j g
    by_cases heq : mobiusSL (slRealToComplex g.val) (a i) = a j
    · exact ⟨univ, univ_mem, univ, univ_mem, fun h => (h heq).elim⟩
    · obtain ⟨u, v, hu, hv, hd⟩ := t2_separation_nhds heq
      exact ⟨u, hu, v, hv, fun _ => hd⟩
  choose u hu v hv huv using hpair
  let U : Fin k → Set ExtPlane := fun i =>
    K i ∩ ((⋂ g ∈ bad, ⋂ j, mobiusSL (slRealToComplex g.val) ⁻¹' u i j g) ∩
      (⋂ g ∈ bad, ⋂ j, v j i g))
  have hUa : ∀ i, U i ∈ 𝓝 (a i) := by
    intro i
    refine inter_mem (mem_interior_iff_mem_nhds.mp (haK i)) (inter_mem ?_ ?_)
    · refine (biInter_mem hbad).mpr ?_
      intro g hg
      refine iInter_mem.mpr ?_
      intro j
      exact (k24_mobiusSLHomeo (slRealToComplex g.val)).continuous.continuousAt (hu i j g)
    · refine (biInter_mem hbad).mpr ?_
      intro g hg
      exact iInter_mem.mpr (fun j => hv j i g)
  refine ⟨U, hUa, (fun i p hp => hKV i hp.1), ?_⟩
  intro i j γ hγ hmeet
  obtain ⟨p, ⟨z, hz, rfl⟩, hγz⟩ := hmeet
  let g : Γ := ⟨γ, hγ⟩
  have hg : g ∈ bad := by
    refine ⟨_, ⟨z, mem_iUnion.mpr ⟨i, hz.1⟩, rfl⟩, ?_⟩
    exact mem_iUnion.mpr ⟨j, hγz.1⟩
  have hcent : mobiusSL (slRealToComplex γ) (a i) = a j := by
    by_contra hne
    exact (huv i j g hne).le_bot
      ⟨mem_iInter.mp (mem_iInter₂.mp hz.2.1 g hg) j,
        mem_iInter.mp (mem_iInter₂.mp hγz.2.2 g hg) i⟩
  have hij : i = j := hsep i j γ hγ hcent
  subst j
  exact ⟨rfl, hfix i γ hγ hcent⟩

end LiZhongQC
