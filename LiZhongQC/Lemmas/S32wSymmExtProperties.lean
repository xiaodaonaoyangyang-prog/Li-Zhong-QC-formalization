import LiZhongQC.Lemmas.S32wHomotopyExtend
import LiZhongQC.Lemmas.S32wSymmetricExtension
import LiZhongQC.Lemmas.S32wSymmExtPuncturedHom

/-!
# Book helper for `symmetric_extension_properties` (S32:580, `s32wh_`)

Conjuncts 1-3 from `s32w_symmetric_extension`; conjunct 4 from `s32w_symm_ext_punctured_homotopy` and
`s32w_homotopy_extend_punctures`.
-/

open Complex Set Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Book helper for `symmetric_extension_properties` (S32, §32.2)**, statement identical: conjuncts 1–3 from
`s32w_symmetric_extension` (W1.3); conjunct 4 from the punctured-double homotopy
`s32w_symm_ext_punctured_homotopy` and its extension over the punctures `s32w_homotopy_extend_punctures` (b6), whose
genus-`0` hypothesis `3 ≤ |Pd₀|` holds since `(0, n, 1)` is non-exceptional only for `n ≥ 2`. -/
theorem s32wh_symmetric_extension_properties {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ fd : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd ∧ IsQCRS fd ∧
      maxDilatationRS fd = maxDilatationRS f ∧
      ∀ f' : S₀ ≃ₜ S, ∀ fd' : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f' fd' →
        ContinuousMap.Homotopic (f : C(S₀, S)) (f' : C(S₀, S)) →
        ContinuousMap.Homotopic (fd : C(Xd₀.carrier, Xd₁.carrier)) (fd' : C(Xd₀.carrier, Xd₁.carrier)) := by
  obtain ⟨fd, hfd, hq, hK⟩ := s32w_symmetric_extension hm F₀ F₁ hd₀ hd₁ f hf
  refine ⟨fd, hfd, hq, hK, fun f' fd' hfd' hhom => ?_⟩
  obtain ⟨fdp, fdp', hp, hp', hh⟩ := s32w_symm_ext_punctured_homotopy hm hex F₀ F₁ hd₀ hd₁ hfd hfd' hhom
  have hP : 2 * g + m - 1 ≠ 0 ∨ 3 ≤ Pd₀.card := by
    by_cases hG : 2 * g + m - 1 = 0
    · right
      rw [hd₀.card_Pd]
      obtain ⟨rfl, rfl⟩ : g = 0 ∧ m = 1 := by omega
      by_contra hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> exact hex (by simp [IsExceptionalType])
    · exact Or.inl hG
  exact s32w_homotopy_extend_punctures hd₀.genus hd₁.genus hP hp hp' hh

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.2: quasiconformal maps, homotopies and admissible differentials extend symmetrically to the
doubles; `K[f^d] = K[f]`, `f ≃ f₀` implies `f^d ≃ f₀^d`, and the extension of a Teichmüller map with
admissible differential `ω` is a Teichmüller map with differential `ω^d`.

**Correction (2026-09-27).**  The hypothesis `hex` was added: for the exceptional types `(0, 0, 1)` and
`(0, 0, 2)` an orientation-reversing map homotopic to `f` on the open surface has a symmetric extension that is
not homotopic to `f^d` (refuted in Lean, s31t). -/
theorem symmetric_extension_properties {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ fd : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd ∧ IsQCRS fd ∧
      maxDilatationRS fd = maxDilatationRS f ∧
      ∀ f' : S₀ ≃ₜ S, ∀ fd' : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f' fd' →
        ContinuousMap.Homotopic (f : C(S₀, S)) (f' : C(S₀, S)) →
        ContinuousMap.Homotopic (fd : C(Xd₀.carrier, Xd₁.carrier)) (fd' : C(Xd₀.carrier, Xd₁.carrier)) := by
  exact s32wh_symmetric_extension_properties hm hex F₀ F₁ hd₀ hd₁ f hf

end RelocatedS32

end LiZhongQC
