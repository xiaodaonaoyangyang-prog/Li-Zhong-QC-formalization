import LiZhongQC.Lemmas.HurwitzOrbitTopology

/-! Descent of actual open local models to the actual orbit space. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- Restrict the actual quotient projection to an open set and its image. -/
def h84g_localOrbitMap {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (V : Set X) : V → h84g_orbitMap ρ '' V :=
  fun x => ⟨h84g_orbitMap ρ x, ⟨x, x.property, rfl⟩⟩

/-- Every open source restriction still maps openly onto its actual quotient image. -/
theorem h84g_localOrbitMap_isOpenQuotientMap {G X : Type*}
    [Group G] [TopologicalSpace X] (ρ : G →* (X ≃ₜ X))
    (V : Set X) (hV : IsOpen V) :
    IsOpenQuotientMap (h84g_localOrbitMap ρ V) := by
  have hq := h84g_orbitMap_isOpenQuotientMap ρ
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx, he⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  · exact (hq.continuous.comp continuous_subtype_val).subtype_mk _
  · exact hq.isOpenMap.mapsToRestrict hV (mapsTo_image _ _)

/-- Two actual quotient maps with the same fibers yield a homeomorphism of their
targets. The equality on representatives is part of the conclusion. -/
theorem h84g_homeomorph_of_same_fibers {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (q : A → B) (f : A → C) (hq : IsQuotientMap q) (hf : IsQuotientMap f)
    (hker : ∀ x y, q x = q y ↔ f x = f y) :
    ∃ E : B ≃ₜ C, ∀ x, E (q x) = f x := by
  let qc : C(A, B) := ⟨q, hq.continuous⟩
  let fc : C(A, C) := ⟨f, hf.continuous⟩
  have hqc : IsQuotientMap qc := hq
  have hfc : IsQuotientMap fc := hf
  let K : Quotient (Setoid.ker qc) ≃ₜ Quotient (Setoid.ker fc) :=
    Homeomorph.Quotient.congrRight hker
  let E := (hqc.homeomorph.symm.trans K).trans hfc.homeomorph
  refine ⟨E, ?_⟩
  intro x
  change hfc.homeomorph (K (hqc.homeomorph.symm
    (hqc.homeomorph (Quotient.mk (Setoid.ker qc) x)))) = f x
  rw [hqc.homeomorph.symm_apply_apply]
  rfl

/-- A homeomorphism between two nonempty open subspaces extends to an open partial
homeomorphism with exactly those source and target sets. -/
theorem h84g_open_subspaces_chart {Q : Type*} [TopologicalSpace Q]
    (W : Set Q) (D : Set ℂ) (hW : IsOpen W) (hD : IsOpen D)
    (hWne : W.Nonempty) (hDne : D.Nonempty) (E : W ≃ₜ D) :
    ∃ b : OpenPartialHomeomorph Q ℂ,
      b.source = W ∧ b.target = D ∧ ∀ x : W, b x = (E x : ℂ) := by
  classical
  letI : Nonempty W := hWne.to_subtype
  letI : Nonempty D := hDne.to_subtype
  let j := (⟨D, hD⟩ : TopologicalSpace.Opens ℂ).openPartialHomeomorphSubtypeCoe
    (inferInstance : Nonempty D)
  let a := E.toOpenPartialHomeomorph.trans j
  have haS : a.source = univ := by
    ext x
    simp only [a, j, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      preimage_univ, inter_self]
  have haT : a.target = D := by
    ext z
    simp only [a, j, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
      preimage_univ, inter_univ]
    rfl
  let b := a.lift_openEmbedding hW.isOpenEmbedding_subtypeVal
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_source, haS]
    rw [image_univ]
    exact Subtype.range_coe
  · exact haT
  · intro x
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl

/-- An open local power model with exactly the actual orbit fibers descends to a
genuine open quotient chart. No inverse branch is chosen on the punctured disk. -/
theorem h84g_quotient_chart_of_local_model {G X : Type*}
    [Group G] [TopologicalSpace X] (ρ : G →* (X ≃ₜ X))
    (V : Set X) (hV : IsOpen V) (hVne : V.Nonempty)
    (D : Set ℂ) (hD : IsOpen D) (f : V → D)
    (hf : IsOpenQuotientMap f)
    (hker : ∀ x y : V, h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔ f x = f y) :
    ∃ b : OpenPartialHomeomorph (h84g_OrbitSpace ρ) ℂ,
      b.source = h84g_orbitMap ρ '' V ∧ b.target = D ∧
      ∀ x : V, b (h84g_orbitMap ρ x) = (f x : ℂ) := by
  have hq := h84g_localOrbitMap_isOpenQuotientMap ρ V hV
  have hk : ∀ x y : V,
      h84g_localOrbitMap ρ V x = h84g_localOrbitMap ρ V y ↔ f x = f y := by
    intro x y
    rw [Subtype.ext_iff]
    exact hker x y
  obtain ⟨E, hE⟩ := h84g_homeomorph_of_same_fibers
    (h84g_localOrbitMap ρ V) f hq.isQuotientMap hf.isQuotientMap hk
  have hW := (h84g_orbitMap_isOpenQuotientMap ρ).isOpenMap V hV
  have hWne : (h84g_orbitMap ρ '' V).Nonempty := hVne.image _
  have hDne : D.Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨f ⟨x, hx⟩, (f ⟨x, hx⟩).property⟩
  obtain ⟨b, hbS, hbT, hb⟩ :=
    h84g_open_subspaces_chart _ D hW hD hWne hDne E
  refine ⟨b, hbS, hbT, ?_⟩
  intro x
  have he := hb (h84g_localOrbitMap ρ V x)
  rw [hE] at he
  exact he

end LiZhongQC

