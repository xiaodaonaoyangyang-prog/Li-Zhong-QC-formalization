import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.S32wFoldPush

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- A symmetric extension of a homeomorphism maps the punctures of the source double into those of the target. -/
theorem s32w_symm_ext_maps_Pd {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) :
    ∀ p ∈ Pd₀, fd p ∈ Pd₁ := by
  classical
  obtain ⟨e, heP, hetend, -, -, hPd⟩ := s31pp_endpoints_exhaust F₀ hd₀
  have hJ₁ : ∀ x, J₁ (J₁ x) = x := hd₁.involution.1
  have hJ₀ : ∀ x, J₀ (J₀ x) = x := hd₀.involution.1
  -- a fixed point of `J₀` is not a puncture
  have hFix₀ : ∀ x : Xd₀.carrier, J₀ x = x → x ∉ (↑Pd₀ : Set Xd₀.carrier) := fun x hx => by
    have : x ∈ {x | J₀ x = x} := hx
    rw [hd₀.fixed_curves] at this
    exact this.2
  have hmain : ∀ q : (↑F₀.P : Set F₀.X.carrier), fd (e q) ∈ Pd₁ := by
    intro q
    letI := s31eg_puncture_neBot F₀ (Finset.mem_coe.1 q.2)
    have hcl : e q ∈ closure (range ιd₀) :=
      mem_closure_of_tendsto (hetend q) (Eventually.of_forall fun s => mem_range_self s)
    have hnot : e q ∉ range ιd₀ := fun ⟨s, hs⟩ =>
      s32w_double_range_off_Pd F₀ hd₀ s (hs ▸ Finset.mem_coe.2 (heP q))
    -- `fd (e q)` is in the closure of `range ιd₁` but not in it
    have hcl' : fd (e q) ∈ closure (range ιd₁) := by
      have h1 : fd '' range ιd₀ ⊆ range ιd₁ := by
        rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨f s, (hfd.1 s).symm⟩
      have h2 := image_closure_subset_closure_image fd.continuous (s := range ιd₀)
      exact closure_mono h1 (h2 ⟨_, hcl, rfl⟩)
    have hnot' : fd (e q) ∉ range ιd₁ := by
      rintro ⟨s', hs'⟩
      obtain ⟨s, rfl⟩ := f.surjective s'
      have : fd (ιd₀ s) = fd (e q) := by rw [hfd.1, hs']
      exact hnot ⟨s, fd.injective this⟩
    by_contra hnP
    have hfr : fd (e q) ∈ frontier (range ιd₁) := by
      rw [hd₁.embedding.isOpen_range.frontier_eq]
      exact ⟨hcl', hnot'⟩
    have hfix : fd (e q) ∈ {x | J₁ x = x} := by
      rw [hd₁.fixed_curves]
      exact ⟨hfr, hnP⟩
    have hfix' : J₁ (fd (e q)) = fd (e q) := hfix
    rw [← hfd.2] at hfix'
    have := fd.injective hfix'
    exact hFix₀ (e q) this (Finset.mem_coe.2 (heP q))
  intro p hp
  rw [hPd] at hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 h
    exact hmain q
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 h
    rw [hfd.2]
    have := hd₁.Pd_invariant
    have hm : J₁ (fd (e q)) ∈ J₁ '' (↑Pd₁ : Set Xd₁.carrier) := ⟨_, Finset.mem_coe.2 (hmain q), rfl⟩
    rw [this] at hm
    exact Finset.mem_coe.1 hm

/-- **(b1)** A symmetric extension restricts to a homeomorphism of the punctured doubles. -/
theorem s32w_double_punctured_restrict {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) :
    ∃ fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁, ∀ y, (fdp y : Xd₁.carrier) = fd y := by
  classical
  have hfwd := s32w_symm_ext_maps_Pd F₀ F₁ hd₀ hd₁ hfd
  have hsymm : IsSymmetricExtension J₁ J₀ ιd₁ ιd₀ f.symm fd.symm := by
    refine ⟨fun s => ?_, fun y => ?_⟩
    · have := hfd.1 (f.symm s)
      rw [f.apply_symm_apply] at this
      rw [← this, fd.symm_apply_apply]
    · apply fd.injective
      rw [fd.apply_symm_apply, hfd.2, fd.apply_symm_apply]
  have hbwd := s32w_symm_ext_maps_Pd F₁ F₀ hd₁ hd₀ hsymm
  refine ⟨{ toFun := fun y => ⟨fd y, fun h => y.2 ?_⟩
            invFun := fun y => ⟨fd.symm y, fun h => y.2 ?_⟩
            left_inv := fun y => Subtype.ext (fd.symm_apply_apply _)
            right_inv := fun y => Subtype.ext (fd.apply_symm_apply _)
            continuous_toFun := Continuous.subtype_mk (fd.continuous.comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (fd.symm.continuous.comp continuous_subtype_val) _ },
    fun y => rfl⟩
  · have := hbwd _ (Finset.mem_coe.1 h)
    rwa [fd.symm_apply_apply] at this
  · have := hfwd _ (Finset.mem_coe.1 h)
    rwa [fd.apply_symm_apply] at this

end LiZhongQC
