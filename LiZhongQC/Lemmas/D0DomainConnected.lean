import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain
import LiZhongQC.Lemmas.StrebelGammaBounds

/-! Approved D0-C source candidate. Reuses the shared ordinary-density theorem;
no new end assumptions and no compiler invocation. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- D0-C. The second-kind domain remains connected after deleting the real pole
orbits: both half-planes remain, and an ordinary real interval contains a point
outside the countable deleted set. Vertical paths through that point join the
half-planes; every other retained real point joins the upper half-plane. -/
theorem s36d0_domain_connected (hΓ : IsFuchsian Γ)
    (hsecond : (ordinarySet Γ).Nonempty) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ) {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    IsConnected Ω := by
  classical
  have _hE := hE
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  let D : Set ℝ := {x : ℝ | (((x : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ}
  have hD : Dense D := s36a_ordinary_dense hΓ hsecond
  have hDo : IsOpen D :=
    (s36x_limitSet_closed hΓ).isOpen_compl.preimage
      (OnePoint.continuous_coe.comp Complex.continuous_ofReal)
  -- Include junk affine images in the countable exclusion: this only makes
  -- the set to avoid larger, and no such image is used as an actual orbit.
  let B : Set ℝ :=
    Set.range (fun p : Γ × ↥E => (h36p_m p.1.1 (p.2 : ℝ)).re) ∪
      Set.range (fun γ : Γ => γ.1 0 0 / γ.1 1 0)
  have hBc : B.Countable := (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨x, hxD, hxB⟩ := (hBc.dense_compl ℝ).inter_open_nonempty D hDo hD.nonempty
  have hxΩ : (x : ℂ) ∈ Ω := by
    refine (hΩ (x : ℂ)).2 ⟨hxD, ?_, ?_⟩
    · intro γ hγ t ht _ he
      apply hxB
      refine Or.inl ⟨(⟨γ, hγ⟩, ⟨t, ht⟩), ?_⟩
      simpa only [Complex.ofReal_re] using (congrArg Complex.re he).symm
    · intro γ hγ _ he
      exact hxB (Or.inr ⟨⟨γ, hγ⟩, (Complex.ofReal_injective he).symm⟩)
  have hnonreal := (s36a_omega hΓ hΩ).1
  have hxU : (x : ℂ) ∈ closure upperHalf := by
    change (x : ℂ) ∈ closure {z : ℂ | 0 < z.im}
    rw [Complex.closure_setOfPred_lt_im]
    simp
  have hxL : (x : ℂ) ∈ closure lowerHalf := by
    change (x : ℂ) ∈ closure {z : ℂ | z.im < 0}
    rw [Complex.closure_setOfPred_im_lt]
    simp
  have hU : IsConnected (insert (x : ℂ) upperHalf) :=
    isConnected_upperHalf.subset_closure (subset_insert _ _) (by
      intro z hz
      rcases hz with he | hz
      · simpa only [he] using hxU
      · exact subset_closure hz)
  have hL : IsConnected (insert (x : ℂ) lowerHalf) :=
    bA_isConnected_lowerHalf.subset_closure (subset_insert _ _) (by
      intro z hz
      rcases hz with he | hz
      · simpa only [he] using hxL
      · exact subset_closure hz)
  have hK : IsConnected (insert (x : ℂ) upperHalf ∪ insert (x : ℂ) lowerHalf) :=
    IsConnected.union ⟨(x : ℂ), Or.inl rfl, Or.inl rfl⟩ hU hL
  refine hK.subset_closure ?_ ?_
  · intro z hz
    rcases hz with hz | hz
    · rcases hz with he | hz
      · simpa only [he] using hxΩ
      · exact hnonreal z (ne_of_gt hz)
    · rcases hz with he | hz
      · simpa only [he] using hxΩ
      · exact hnonreal z (ne_of_lt hz)
  · intro z _
    by_cases hz : 0 ≤ z.im
    · apply closure_mono (show upperHalf ⊆ insert (x : ℂ) upperHalf ∪ insert (x : ℂ) lowerHalf
        from fun w hw => Or.inl (Or.inr hw))
      change z ∈ closure {w : ℂ | 0 < w.im}
      rw [Complex.closure_setOfPred_lt_im]
      exact hz
    · apply closure_mono (show lowerHalf ⊆ insert (x : ℂ) upperHalf ∪ insert (x : ℂ) lowerHalf
        from fun w hw => Or.inr (Or.inr hw))
      change z ∈ closure {w : ℂ | w.im < 0}
      rw [Complex.closure_setOfPred_im_lt]
      exact (lt_of_not_ge hz).le

end LiZhongQC
