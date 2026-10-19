import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.S32wFoldPush
import LiZhongQC.Lemmas.S32wReflectionsAgree

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold Pointwise

noncomputable section
namespace LiZhongQC

universe u

/-- In a freely acting group two elements that agree at one point agree as maps. -/
theorem s32w_deck_eq_of_pt {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfree : ActsFreely Γ)
    {a b : Matrix.SpecialLinearGroup (Fin 2) ℝ} (ha : a ∈ Γ) (hb : b ∈ Γ) {x : UpperHalfPlane}
    (h : a • x = b • x) : ∀ y : UpperHalfPlane, a • y = b • y := by
  have h1 : (a⁻¹ * b) • x = x := by
    rw [mul_smul, ← h, inv_smul_smul]
  rcases hfree (a⁻¹ * b) (Γ.mul_mem (Γ.inv_mem ha) hb) x h1 with h2 | h2
  · intro y
    have : a⁻¹ * b = 1 := h2
    have hab : b = a := by
      calc b = a * (a⁻¹ * b) := by group
        _ = a := by rw [this, mul_one]
    rw [hab]
  · intro y
    have : a⁻¹ * b = -1 := h2
    have hab : b = -a := by
      calc b = a * (a⁻¹ * b) := by group
        _ = -a := by rw [this]; simp
    rw [hab, s32w_neg_smul]

/-- **(b2)** The lifts of two homotopic-on-the-half maps have, on any connected `Γ₀`-stable piece `C` of the lifted
half, deck homomorphisms conjugate by one `γ₁ ∈ Γ₁`. -/
theorem s32w_half_deck_agree {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] {S : Type u}
    [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier}
    {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : Topology.IsOpenEmbedding ιd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfree₁ : ActsFreely Γ₁)
    {p₀ : UpperHalfPlane → puncturedOpens Pd₀} {p₁ : UpperHalfPlane → puncturedOpens Pd₁}
    (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {f f' : S₀ ≃ₜ S} (hhom : ContinuousMap.Homotopic (f : C(S₀, S)) (f' : C(S₀, S)))
    {fdp fdp' : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁}
    (hfdp : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x → (fdp y : Xd₁.carrier) = ιd₁ (f x))
    (hfdp' : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x → (fdp' y : Xd₁.carrier) = ιd₁ (f' x))
    {F F' : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ fdp F) (hF' : IsLift p₀ p₁ fdp' F')
    {C : Set UpperHalfPlane} (hC : IsConnected C)
    (hCQ : ∀ τ ∈ C, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) ∈ range ιd₀) :
    ∃ γ₁ ∈ Γ₁, ∀ g ∈ Γ₀, g • C = C → ∀ τ, F (g • F.symm τ) = γ₁ • F' (g • F'.symm (γ₁⁻¹ • τ)) := by
  classical
  haveI : ConnectedSpace ↥C := Subtype.connectedSpace hC
  obtain ⟨H⟩ := hhom
  obtain ⟨τ₀, hτ₀⟩ := hC.nonempty
  -- the half as a subspace
  let φ₀ : S₀ ≃ₜ range ιd₀ := hd₀.isEmbedding.toHomeomorph
  let u : C(↥C, S₀) :=
    ⟨fun τ => φ₀.symm ⟨((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier), hCQ τ τ.2⟩,
      φ₀.symm.continuous.comp (Continuous.subtype_mk
        (continuous_subtype_val.comp (hp₀.1.continuous.comp continuous_subtype_val)) _)⟩
  have hu : ∀ τ : ↥C, ((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier) = ιd₀ (u τ) := fun τ => by
    have := φ₀.apply_symm_apply ⟨((p₀ τ : puncturedOpens Pd₀) : Xd₀.carrier), hCQ τ τ.2⟩
    exact (congrArg Subtype.val this).symm
  have hoff : ∀ x : S, ιd₁ x ∉ (↑Pd₁ : Set Xd₁.carrier) := s32w_double_range_off_Pd F₁ hd₁
  let K : C(unitInterval × ↥C, puncturedOpens Pd₁) :=
    ⟨fun x => ⟨ιd₁ (H (x.1, u x.2)), fun h => hoff _ h⟩,
      Continuous.subtype_mk (hd₁.embedding.continuous.comp
        (H.toContinuousMap.continuous.comp (continuous_fst.prodMk (u.continuous.comp continuous_snd)))) _⟩
  have hKapp : ∀ t τ, ((K (t, τ) : puncturedOpens Pd₁) : Xd₁.carrier) = ιd₁ (H (t, u τ)) := fun _ _ => rfl
  have hK0 : ∀ τ : ↥C, K (0, τ) = p₁ (F τ) := by
    intro τ
    apply Subtype.ext
    rw [hKapp, H.apply_zero, hF τ]
    exact (hfdp (p₀ τ) (u τ) (hu τ)).symm
  have hK1 : ∀ τ : ↥C, K (1, τ) = p₁ (F' τ) := by
    intro τ
    apply Subtype.ext
    rw [hKapp, H.apply_one, hF' τ]
    exact (hfdp' (p₀ τ) (u τ) (hu τ)).symm
  let F₀' : C(↥C, UpperHalfPlane) := ⟨fun τ => F τ, F.continuous.comp continuous_subtype_val⟩
  have hK0' : ∀ τ : ↥C, K (0, τ) = p₁ (F₀' τ) := hK0
  set Ht := hp₁.1.liftHomotopy K F₀' hK0' with hHt
  have hlift : ∀ t τ, p₁ (Ht (t, τ)) = K (t, τ) :=
    fun t τ => congrFun (hp₁.1.liftHomotopy_lifts K F₀' hK0') (t, τ)
  have hzero : ∀ τ : ↥C, Ht (0, τ) = F τ := fun τ =>
    hp₁.1.liftHomotopy_zero K F₀' hK0' τ
  -- the end of the lifted homotopy is `γ₁ F'`
  obtain ⟨γ₁, hγ₁Γ, hγ₁τ₀⟩ := (hp₁.2.2.2 (F' τ₀) (Ht (1, ⟨τ₀, hτ₀⟩))).1 (by
    rw [hlift, hK1 ⟨τ₀, hτ₀⟩]) 
  have hend : ∀ τ : ↥C, Ht (1, τ) = γ₁ • F' τ := by
    have h := hp₁.1.eq_of_comp_eq (f := p₁)
      (g₁ := fun τ : ↥C => Ht (1, τ)) (g₂ := fun τ : ↥C => γ₁ • F' τ)
      (Ht.continuous.comp (continuous_const.prodMk continuous_id))
      ((continuous_const_smul γ₁).comp (F'.continuous.comp continuous_subtype_val))
      (by
        funext τ
        simp only [Function.comp_apply]
        rw [hlift, hK1]
        exact ((hp₁.2.2.2 (F' τ) (γ₁ • F' τ)).2 ⟨γ₁, hγ₁Γ, rfl⟩))
      ⟨τ₀, hτ₀⟩ hγ₁τ₀.symm
    exact fun τ => congrFun h τ
  refine ⟨γ₁, hγ₁Γ, fun g hg hgC τ => ?_⟩
  have hgmem : ∀ x : ↥C, g • (x : UpperHalfPlane) ∈ C := fun x => by
    have h := Set.smul_mem_smul_set (a := g) x.2
    rwa [hgC] at h
  let gC : ↥C → ↥C := fun x => ⟨g • (x : UpperHalfPlane), hgmem x⟩
  have hgCcont : Continuous gC :=
    Continuous.subtype_mk ((continuous_const_smul g).comp continuous_subtype_val) _
  have hpg : ∀ x : UpperHalfPlane, p₀ (g • x) = p₀ x := fun x =>
    ((hp₀.2.2.2 x (g • x)).2 ⟨g, hg, rfl⟩).symm
  have hugC : ∀ x : ↥C, u (gC x) = u x := by
    intro x
    show φ₀.symm ⟨((p₀ (g • (x : UpperHalfPlane)) : puncturedOpens Pd₀) : Xd₀.carrier), _⟩ =
      φ₀.symm ⟨((p₀ x : puncturedOpens Pd₀) : Xd₀.carrier), _⟩
    congr 1
    exact Subtype.ext (by simp only [hpg])
  obtain ⟨δF, hδFΓ, hδF⟩ := h23l_deck hp₀ hp₁ hF hg
  obtain ⟨δF', hδF'Γ, hδF'⟩ := h23l_deck hp₀ hp₁ hF' hg
  have hdeck : ∀ (t : unitInterval) (x : ↥C), Ht (t, gC x) = δF • Ht (t, x) := by
    have h := hp₁.1.eq_of_comp_eq (f := p₁)
      (g₁ := fun x : unitInterval × ↥C => Ht (x.1, gC x.2)) (g₂ := fun x : unitInterval × ↥C => δF • Ht x)
      (Ht.continuous.comp (continuous_fst.prodMk (hgCcont.comp continuous_snd)))
      ((continuous_const_smul δF).comp Ht.continuous)
      (by
        funext x
        simp only [Function.comp_apply]
        have e : K (x.1, gC x.2) = K (x.1, x.2) := by
          apply Subtype.ext
          rw [hKapp, hKapp, hugC]
        have h2 : p₁ (δF • Ht x) = p₁ (Ht x) :=
          ((hp₁.2.2.2 (Ht x) (δF • Ht x)).2 ⟨δF, hδFΓ, rfl⟩).symm
        rw [hlift, e, h2]
        exact (hlift x.1 x.2).symm)
      (0, ⟨τ₀, hτ₀⟩) (by
        show Ht (0, gC ⟨τ₀, hτ₀⟩) = δF • Ht (0, ⟨τ₀, hτ₀⟩)
        rw [hzero, hzero]
        exact hδF τ₀)
    exact fun t x => congrFun h (t, x)
  -- at `t = 1`: `γ₁ δF' γ₁⁻¹` and `δF` agree at a point, hence everywhere
  have h1 := hdeck 1 ⟨τ₀, hτ₀⟩
  have hgτ₀ : Ht (1, gC ⟨τ₀, hτ₀⟩) = γ₁ • δF' • F' τ₀ := by
    rw [hend]
    show γ₁ • F' (g • τ₀) = _
    rw [hδF']
  rw [hgτ₀, hend] at h1
  have hconj : ∀ y : UpperHalfPlane, (γ₁ * δF' * γ₁⁻¹) • y = δF • y := by
    refine s32w_deck_eq_of_pt hfree₁ (Γ₁.mul_mem (Γ₁.mul_mem hγ₁Γ hδF'Γ) (Γ₁.inv_mem hγ₁Γ)) hδFΓ
      (x := γ₁ • F' τ₀) ?_
    rw [mul_smul, mul_smul, inv_smul_smul]
    exact h1
  rw [hδF, F.apply_symm_apply, hδF', F'.apply_symm_apply, ← hconj τ, mul_smul, mul_smul]

end LiZhongQC
