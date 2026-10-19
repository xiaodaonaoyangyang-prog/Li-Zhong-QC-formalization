import LiZhongQC.Lemmas.S36BersOrdinary

/-! Ordinary spherical orbit separation for D1 I/P. No stub imports. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Two distinct ordinary spherical orbits have neighborhoods whose translates
are disjoint. This is the finite-compact-intersection argument underlying the
Hausdorff quotient theorem, expressed for the installed Mobius action. -/
theorem s36d1_ordinary_orbit_separation (hΓ : IsFuchsian Γ)
    {a b : ExtPlane} (ha : a ∉ fuchsianLimitSet Γ) (hb : b ∉ fuchsianLimitSet Γ)
    (hab : ∀ γ ∈ Γ, mobiusSL (slRealToComplex γ) a ≠ b) :
    ∃ U ∈ 𝓝 a, ∃ V ∈ 𝓝 b, ∀ γ ∈ Γ,
      Disjoint (mobiusSL (slRealToComplex γ) '' U) V := by
  classical
  have hopen : IsOpen (fuchsianLimitSet Γ)ᶜ := (s36x_limitSet_closed hΓ).isOpen_compl
  obtain ⟨K, hK, haK, hKO⟩ := exists_compact_subset hopen ha
  obtain ⟨L, hL, hbL, hLO⟩ := exists_compact_subset hopen hb
  let bad : Set Γ := {γ | (mobiusSL (slRealToComplex γ.val) '' K ∩ L).Nonempty}
  have hbad : bad.Finite := by
    refine (s36x_fin hΓ (hK.union hL) ?_).subset ?_
    · intro p hp
      rcases hp with hp | hp
      · exact hKO hp
      · exact hLO hp
    · intro γ hγ
      obtain ⟨p, ⟨z, hz, heq⟩, hpL⟩ := hγ
      exact ⟨p, ⟨z, Or.inl hz, heq⟩, Or.inr hpL⟩
  choose u v hu hv huv using fun γ : Γ =>
    t2_separation_nhds (hab γ.val γ.property)
  let U : Set ExtPlane :=
    (⋂ γ ∈ bad, mobiusSL (slRealToComplex γ.val) ⁻¹' u γ) ∩ K
  let V : Set ExtPlane := (⋂ γ ∈ bad, v γ) ∩ L
  have hUa : U ∈ 𝓝 a := by
    apply inter_mem
    · refine (biInter_mem hbad).mpr ?_
      intro γ hγ
      exact (k24_mobiusSLHomeo (slRealToComplex γ.val)).continuous.continuousAt (hu γ)
    · exact mem_interior_iff_mem_nhds.mp haK
  have hVb : V ∈ 𝓝 b := by
    exact inter_mem ((biInter_mem hbad).mpr (fun γ _ => hv γ))
      (mem_interior_iff_mem_nhds.mp hbL)
  refine ⟨U, hUa, V, hVb, ?_⟩
  intro γ hγ
  apply Set.disjoint_left.mpr
  intro p hpU hpV
  obtain ⟨z, hzU, rfl⟩ := hpU
  let g : Γ := ⟨γ, hγ⟩
  have hg : g ∈ bad := ⟨_, ⟨z, hzU.2, rfl⟩, hpV.2⟩
  exact (huv g).le_bot
    ⟨mem_iInter₂.mp hzU.1 g hg, mem_iInter₂.mp hpV.1 g hg⟩

end LiZhongQC
