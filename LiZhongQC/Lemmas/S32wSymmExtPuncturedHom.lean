import LiZhongQC.Lemmas.S32wSymmExtPunctured

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Pointwise ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- **(b5')** Quasiconformality-free version of `s32w_symm_ext_punctured`: symmetric extensions of homotopic
maps are homotopic on the punctured doubles. -/
theorem s32w_symm_ext_punctured_homotopy {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0)
    (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier}
    {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f f' : S₀ ≃ₜ S}
    {fd fd' : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) (hfd' : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f' fd')
    (hhom : ContinuousMap.Homotopic (f : C(S₀, S)) (f' : C(S₀, S))) :
    ∃ fdp fdp' : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁,
      (∀ y, (fdp y : Xd₁.carrier) = fd y) ∧ (∀ y, (fdp' y : Xd₁.carrier) = fd' y) ∧
      ContinuousMap.Homotopic (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
        (fdp' : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) := by
  classical
  obtain ⟨fdp, hfdp⟩ := s32w_double_punctured_restrict F₀ F₁ hd₀ hd₁ hfd
  obtain ⟨fdp', hfdp'⟩ := s32w_double_punctured_restrict F₀ F₁ hd₀ hd₁ hfd'
  refine ⟨fdp, fdp', hfdp, hfdp', ?_⟩
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  haveI : ConnectedSpace (puncturedOpens Pd₁) := s32w_punctured_connectedSpace Pd₁
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ := ((finiteType_hyperbolic F₀ hex).2 hm Xd₀ J₀ ιd₀ Pd₀ hd₀)
  obtain ⟨Γ₁, p₁, hΓ₁, hfree₁, hp₁⟩ := ((finiteType_hyperbolic F₁ hex).2 hm Xd₁ J₁ ιd₁ Pd₁ hd₁)
  obtain ⟨hP₀loc, hP₀hol, hfib₀, hinv₀⟩ := s32w_P_facts hp₀
  obtain ⟨hAc, -, -⟩ := s32w_punctured_facts F₀ hd₀
  obtain ⟨ya, hya⟩ := hAc.nonempty
  obtain ⟨τa, hτa⟩ := hp₀.2.2.1 ya
  -- the lifts of `fdp` and `fdp'`
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (fdp (p₀ τa))
  obtain ⟨F, hF, -⟩ := exists_lift hp₀ hp₁ fdp τa τ₁ hτ₁
  obtain ⟨τ₁', hτ₁'⟩ := hp₁.2.2.1 (fdp' (p₀ τa))
  obtain ⟨F', hF', -⟩ := exists_lift hp₀ hp₁ fdp' τa τ₁' hτ₁'
  -- the lift of the reflection
  obtain ⟨Jd₀, hJd₀⟩ := s32w_restrict_reflection hd₀
  obtain ⟨τJ, hτJ⟩ := hp₀.2.2.1 (Jd₀ (p₀ τa))
  obtain ⟨Jt, hJt, -⟩ := exists_lift hp₀ hp₀ Jd₀ τa τJ hτJ
  have hlift : ∀ τ, ((p₀ (Jt τ) : puncturedOpens Pd₀) : Xd₀.carrier) =
      J₀ ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) := fun τ => by
    rw [hJt τ, hJd₀]
  -- the maximal piece `C` of the lifted half through `τa`
  have hτaQ : ((p₀ τa : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀ := by
    rw [hτa]; exact hya
  set Q : Set UpperHalfPlane := {τ | ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀} with hQdef
  set C : Set UpperHalfPlane := connectedComponentIn Q τa with hCdef
  have hτaC : τa ∈ C := mem_connectedComponentIn hτaQ
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCconn : IsConnected C := ⟨⟨τa, hτaC⟩, hCpre⟩
  have hCQ : ∀ τ ∈ C, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀ :=
    fun τ hτ => connectedComponentIn_subset Q τa hτ
  have hCmax : ∀ D : Set UpperHalfPlane, IsPreconnected D →
      (∀ τ ∈ D, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀) → (D ∩ C).Nonempty → D ⊆ C := by
    intro D hD hDQ hne
    obtain ⟨y, hyD, hyC⟩ := hne
    have h1 : connectedComponentIn Q y = C := (connectedComponentIn_eq hyC).symm
    rw [← h1]
    exact hD.subset_connectedComponentIn hyD (fun τ hτ => hDQ τ hτ)
  -- (b2): the deck homomorphisms of `F` and `F'` agree up to `γ₁` on the stabiliser of `C`
  have hfdp_half : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x →
      (fdp y : Xd₁.carrier) = ιd₁ (f x) := fun y x hy => by
    rw [hfdp y, hy]; exact hfd.1 x
  have hfdp'_half : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x →
      (fdp' y : Xd₁.carrier) = ιd₁ (f' x) := fun y x hy => by
    rw [hfdp' y, hy]; exact hfd'.1 x
  obtain ⟨γ₁, hγ₁, hconj⟩ := s32w_half_deck_agree F₁ hd₀.embedding hd₁ hfree₁ hp₀ hp₁ hhom
    hfdp_half hfdp'_half hF hF' hCconn hCQ
  have hfdpJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y →
      (fdp y' : Xd₁.carrier) = J₁ (fdp y) := fun y y' hy => by
    rw [hfdp y', hfdp y, hy]; exact hfd.2 y
  have hfdpJ' : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y →
      (fdp' y' : Xd₁.carrier) = J₁ (fdp' y) := fun y y' hy => by
    rw [hfdp' y', hfdp' y, hy]; exact hfd'.2 y
  -- `G' = γ₁ F'` and `Φ = G'⁻¹ F`
  set G' : UpperHalfPlane ≃ₜ UpperHalfPlane := F'.trans (Homeomorph.smul γ₁) with hG'def
  have hG'app : ∀ τ, G' τ = γ₁ • F' τ := fun τ => rfl
  have hG'symm : ∀ σ, G'.symm σ = F'.symm (γ₁⁻¹ • σ) := fun σ => by
    apply G'.injective
    rw [G'.apply_symm_apply, hG'app, F'.apply_symm_apply, smul_inv_smul]
  set Φ : UpperHalfPlane ≃ₜ UpperHalfPlane := F.trans G'.symm with hΦdef
  have hΦapp : ∀ τ, Φ τ = G'.symm (F τ) := fun τ => rfl
  have hstab : ∀ g ∈ Γ₀, g • C = C → ∀ τ, Φ (g • τ) = g • Φ τ := by
    intro g hg hgC τ
    have h1 := hconj g hg hgC (F τ)
    rw [F.symm_apply_apply] at h1
    have h2 : F (g • τ) = G' (g • G'.symm (F τ)) := by
      rw [h1, hG'app, hG'symm]
    rw [hΦapp, hΦapp, h2, G'.symm_apply_apply]
  have hrefl : ∀ J' : UpperHalfPlane ≃ₜ UpperHalfPlane,
      (∀ τ, ((p₀ (J' τ) : puncturedOpens Pd₀) : Xd₀.carrier) = J₀ ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier)) →
      (∃ τ ∈ closure C, J' τ = τ) → ∀ τ, Φ (J' τ) = J' (Φ τ) := by
    intro J' hJ' hfix τ
    obtain ⟨q, hq, hqfix⟩ := hfix
    have h1 := s32w_boundary_reflection_agree F₀ F₁ hd₀ hd₁ hΓ₀ hfree₀ hfree₁ hp₀ hp₁ hfdpJ hfdpJ'
      hF hF' hγ₁ hCpre hCQ hCmax hconj hJ' hq hqfix (F τ)
    rw [F.symm_apply_apply] at h1
    have h2 : F (J' τ) = G' (J' (G'.symm (F τ))) := by
      rw [h1, hG'app, hG'symm]
    rw [hΦapp, hΦapp, h2, G'.symm_apply_apply]
  have hgen := s32w_tile_generation F₀ hd₀ hΓ₀ hfree₀ hP₀loc hP₀hol (fun τ => (p₀ τ).2) hfib₀ hinv₀ hlift
    ⟨τa, hτaC⟩ hCpre hCQ hCmax hstab hrefl
  refine (thm23_1_homotopy_iff hp₀ hp₁ fdp fdp' hF hF').2 ⟨γ₁, hγ₁, fun γ hγ τ => ?_⟩
  have h1 := hgen γ hγ (F.symm τ)
  rw [hΦapp, hΦapp, F.apply_symm_apply] at h1
  have h2 : F (γ • F.symm τ) = G' (γ • G'.symm τ) := by
    have := congrArg G' h1
    rwa [G'.apply_symm_apply] at this
  rw [h2, hG'app, hG'symm]

end LiZhongQC
