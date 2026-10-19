import LiZhongQC.Ch11.S36_Hamilton

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- `f^ν` is `(1 + c)/(1 - c)`-q.c. on `ℍ` with `c = ‖ν‖∞`, and maps `ℍ` onto `ℍ`. -/
theorem str_fMu_facts (ν : BeltramiGamma Γ) :
    IsKQC (fMuSym ν.1.1) upperHalf ((1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1)) ∧
      fMuSym ν.1.1 '' upperHalf = upperHalf := by
  obtain ⟨k, hk0, hk1, hν⟩ := bg_beltramiH_upper ν.1
  exact ⟨(c36_c_fMuSym_spec ν.1 (c36_c_normH_lt_one ν.1) le_rfl).2.2,
    (fMuSym_upperHalf hk0 hk1 hν).1⟩

/-- `g = (f^ν)⁻¹ ∘ f^μ` commutes with `Γ` on `ℍ` when `ν ∼ μ`. -/
theorem str_comm (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∀ z ∈ upperHalf, (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) (h36p_m γ z) =
      h36p_m γ ((Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  obtain ⟨A, hA⟩ := b33_d_def μ hγ
  have hB := c36_c_rel_of_equiv hrel hγ hA
  obtain ⟨hKν, hνs⟩ := str_fMu_facts ν
  obtain ⟨hKμ, hμs⟩ := str_fMu_facts μ
  set f := fMuSym ν.1.1 with hf
  set f₀ := fMuSym μ.1.1 with hf₀
  have hinj : InjOn f upperHalf := hKν.2.2.1.2.1
  intro z hz
  have hf₀z : f₀ z ∈ upperHalf := hμs ▸ mem_image_of_mem _ hz
  have hex : ∃ w ∈ upperHalf, f w = f₀ z := by
    have : f₀ z ∈ f '' upperHalf := by rw [hνs]; exact hf₀z
    obtain ⟨w, hw, hw'⟩ := this
    exact ⟨w, hw, hw'⟩
  have hgz : Function.invFunOn f upperHalf (f₀ z) ∈ upperHalf := Function.invFunOn_mem hex
  have hfgz : f (Function.invFunOn f upperHalf (f₀ z)) = f₀ z := Function.invFunOn_eq hex
  set w := Function.invFunOn f upperHalf (f₀ z) with hw
  have hγw : h36p_m γ w ∈ upperHalf := h36p_m_mem γ hgz
  have h1 : f (h36p_m γ w) = mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (f₀ z) := by
    have := hB w hgz
    rw [hfgz] at this
    exact this
  have h2 : f₀ (h36p_m γ z) = mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (f₀ z) := hA z hz
  show Function.invFunOn f upperHalf (f₀ (h36p_m γ z)) = h36p_m γ (Function.invFunOn f upperHalf (f₀ z))
  rw [h2, ← h1]
  exact hinj.leftInvOn_invFunOn hγw

/-- `g = (f^ν)⁻¹ ∘ f^μ` is a q.c. self-map of `ℍ` onto `ℍ` commuting with `Γ`. -/
theorem str_g_facts (μ ν : BeltramiGamma Γ) (hrel : teichSetoidGamma Γ ν μ) :
    ∃ K : ℝ, IsKQC (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) upperHalf K ∧
      (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) '' upperHalf = upperHalf ∧
      ∀ γ ∈ Γ, ∀ z ∈ upperHalf, (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) (h36p_m γ z) =
        h36p_m γ ((Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  obtain ⟨hK, hfs⟩ := str_fMu_facts ν
  obtain ⟨hK₀, hf₀s⟩ := str_fMu_facts μ
  set K := (1 + beltramiNormH ν.1.1) / (1 - beltramiNormH ν.1.1) with hKdef
  set f := fMuSym ν.1.1 with hf
  set f₀ := fMuSym μ.1.1 with hf₀
  set a := Function.invFunOn f upperHalf with hadef
  have haK : IsKQC a upperHalf K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hfi : InjOn f upperHalf := hK.2.2.1.2.1
  have hgK := thm7_1_comp hK₀ haK hf₀s.subset
  have hgimg : (a ∘ f₀) '' upperHalf = upperHalf := by
    rw [image_comp, hf₀s]
    conv_lhs => rw [← hfs]
    exact hfi.leftInvOn_invFunOn.image_image
  exact ⟨_, hgK, hgimg, fun γ hγ z hz => str_comm μ ν hrel hγ z hz⟩

end LiZhongQC
