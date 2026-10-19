import LiZhongQC.Lemmas.HurwitzStabilizerAction

/-! The actual topological orbit space of a finite surface action.
No complex structure or global quotient property is included in its definition. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- The equivalence relation given by the actual homeomorphism action. -/
def h84g_orbitSetoid {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) : Setoid X where
  r x y := ∃ g : G, ρ g x = y
  iseqv := by
    constructor
    · intro x
      exact ⟨1, by rw [map_one, Homeomorph.one_apply]⟩
    · intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      refine ⟨g⁻¹, ?_⟩
      rw [← Homeomorph.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Homeomorph.one_apply]
    · intro x y z hxy hyz
      obtain ⟨g, rfl⟩ := hxy
      obtain ⟨h, rfl⟩ := hyz
      exact ⟨h * g, by rw [map_mul, Homeomorph.mul_apply]⟩

/-- The actual orbit quotient, with the standard quotient topology. -/
abbrev h84g_OrbitSpace {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) := Quotient (h84g_orbitSetoid ρ)

/-- Projection to the actual orbit quotient. -/
def h84g_orbitMap {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) : X → h84g_OrbitSpace ρ := Quotient.mk _

/-- Equality in the quotient means equality up to an actual group element. -/
theorem h84g_orbitMap_eq_iff {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (x y : X) :
    h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔ ∃ g : G, ρ g x = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    change Quotient.mk (h84g_orbitSetoid ρ) x = Quotient.mk (h84g_orbitSetoid ρ) y
    exact Quotient.sound h

/-- Every quotient point is represented by an actual surface point. -/
theorem h84g_orbitMap_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) : Function.Surjective (h84g_orbitMap ρ) :=
  Quotient.mk_surjective

/-- Saturation is exactly the union of the translates of the original set. -/
theorem h84g_saturation_eq {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (U : Set X) :
    (h84g_orbitMap ρ) ⁻¹' (h84g_orbitMap ρ '' U) = ⋃ g : G, ρ g '' U := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨g, hg⟩ := (h84g_orbitMap_eq_iff ρ y x).mp he
    exact mem_iUnion.mpr ⟨g, y, hy, hg⟩
  · intro hx
    obtain ⟨g, y, hy, hg⟩ := mem_iUnion.mp hx
    exact ⟨y, hy, (h84g_orbitMap_eq_iff ρ y x).mpr ⟨g, hg⟩⟩

/-- The actual projection is an open quotient map. Finiteness is not needed here. -/
theorem h84g_orbitMap_isOpenQuotientMap {G X : Type*}
    [Group G] [TopologicalSpace X] (ρ : G →* (X ≃ₜ X)) :
    IsOpenQuotientMap (h84g_orbitMap ρ) := by
  have hq : IsQuotientMap (h84g_orbitMap ρ) := isQuotientMap_quotient_mk'
  apply IsOpenQuotientMap.of_isOpenMap_isQuotientMap _ hq
  intro U hU
  apply hq.isOpen_preimage.mp
  rw [h84g_saturation_eq]
  exact isOpen_iUnion (fun g => (ρ g).isOpenMap U hU)

/-- A finite union of closed homeomorphism graphs is the actual orbit relation. -/
theorem h84g_orbit_relation_closed {G X : Type*}
    [Group G] [Finite G] [TopologicalSpace X] [T2Space X]
    (ρ : G →* (X ≃ₜ X)) : IsClosed {z : X × X | ∃ g : G, ρ g z.1 = z.2} := by
  have he : {z : X × X | ∃ g : G, ρ g z.1 = z.2} =
      ⋃ g : G, {z : X × X | ρ g z.1 = z.2} := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
  rw [he]
  exact isClosed_iUnion_of_finite
    (fun g => isClosed_eq ((ρ g).continuous.comp continuous_fst) continuous_snd)

/-- The genuine finite-action orbit quotient is Hausdorff. -/
theorem h84g_orbitSpace_t2 {G X : Type*}
    [Group G] [Finite G] [TopologicalSpace X] [T2Space X]
    (ρ : G →* (X ≃ₜ X)) : T2Space (h84g_OrbitSpace ρ) := by
  apply (t2Space_iff_of_isOpenQuotientMap
    (h84g_orbitMap_isOpenQuotientMap ρ)).mpr
  simpa only [h84g_orbitMap_eq_iff] using h84g_orbit_relation_closed ρ

/-- Compactness descends through the actual quotient projection. -/
theorem h84g_orbitSpace_compact {G X : Type*}
    [Group G] [TopologicalSpace X] [CompactSpace X]
    (ρ : G →* (X ≃ₜ X)) : CompactSpace (h84g_OrbitSpace ρ) := inferInstance

/-- Connectedness descends through the actual quotient projection. -/
theorem h84g_orbitSpace_connected {G X : Type*}
    [Group G] [TopologicalSpace X] [ConnectedSpace X]
    (ρ : G →* (X ≃ₜ X)) : ConnectedSpace (h84g_OrbitSpace ρ) := inferInstance

/-- A neighborhood of p can be separated from its translate by any element not fixing p. -/
theorem h84g_separate_translate {G X : Type*}
    [Group G] [TopologicalSpace X] [T2Space X]
    (ρ : G →* (X ≃ₜ X)) (p : X) (g : G) (hg : ρ g p ≠ p) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U, ρ g x ≠ y := by
  obtain ⟨A, B, hAo, hBo, hpA, hgpB, hAB⟩ := t2_separation hg.symm
  refine ⟨A ∩ (ρ g) ⁻¹' B, hAo.inter (hBo.preimage (ρ g).continuous),
    ⟨hpA, hgpB⟩, ?_⟩
  intro x hx y hy hxy
  exact Set.disjoint_left.mp hAB hy.1 (hxy ▸ hx.2)

/-- Actual stabilizer slices: global orbit identifications inside V are stabilizer
identifications. V is constructed by finite intersections and is stabilizer invariant. -/
theorem h84g_exists_stabilizer_slice {G X : Type*}
    [Group G] [Finite G] [TopologicalSpace X] [T2Space X]
    (ρ : G →* (X ≃ₜ X)) (p : X) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      (∀ k : h84a_pointStabilizer ρ p, MapsTo (ρ (k : G)) V V) ∧
      (∀ g : G, ∀ x ∈ V, ∀ y ∈ V, ρ g x = y → ρ g p = p) := by
  classical
  have hU : ∀ g : G, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      (ρ g p ≠ p → ∀ x ∈ U, ∀ y ∈ U, ρ g x ≠ y) := by
    intro g
    by_cases hg : ρ g p = p
    · exact ⟨univ, isOpen_univ, mem_univ _, fun hn => (hn hg).elim⟩
    · obtain ⟨U, hUo, hpU, hsep⟩ := h84g_separate_translate ρ p g hg
      exact ⟨U, hUo, hpU, fun _ => hsep⟩
  choose U hUo hpU hUsep using hU
  let W : Set X := ⋂ g : G, U g
  have hWo : IsOpen W := isOpen_iInter_of_finite hUo
  have hpW : p ∈ W := mem_iInter.mpr hpU
  let K := h84a_pointStabilizer ρ p
  let V : Set X := ⋂ k : K, (ρ (k : G)) ⁻¹' W
  have hVo : IsOpen V :=
    isOpen_iInter_of_finite (fun k => hWo.preimage (ρ (k : G)).continuous)
  have hpV : p ∈ V := by
    apply mem_iInter.mpr
    intro k
    change ρ (k : G) p ∈ W
    rw [k.property]
    exact hpW
  have hVW : V ⊆ W := by
    intro x hx
    have h := mem_iInter.mp hx (1 : K)
    change ρ 1 x ∈ W at h
    simpa only [map_one, Homeomorph.one_apply] using h
  refine ⟨V, hVo, hpV, ?_, ?_⟩
  · intro k x hx
    apply mem_iInter.mpr
    intro l
    have h := mem_iInter.mp hx (l * k)
    change ρ ((l : G) * (k : G)) x ∈ W at h
    change ρ (l : G) (ρ (k : G) x) ∈ W
    simpa only [map_mul, Homeomorph.mul_apply] using h
  · intro g x hx y hy hxy
    by_contra hg
    exact hUsep g hg x (mem_iInter.mp (hVW hx) g)
      y (mem_iInter.mp (hVW hy) g) hxy

/-- On a stabilizer slice, quotient fibers are precisely the stabilizer orbits. -/
theorem h84g_slice_fiber_iff {G X : Type*}
    [Group G] [TopologicalSpace X] (ρ : G →* (X ≃ₜ X)) (p : X)
    (V : Set X)
    (hV : ∀ g : G, ∀ x ∈ V, ∀ y ∈ V, ρ g x = y → ρ g p = p)
    {x y : X} (hx : x ∈ V) (hy : y ∈ V) :
    h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔
      ∃ k : h84a_pointStabilizer ρ p, ρ (k : G) x = y := by
  rw [h84g_orbitMap_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨⟨g, hV g x hx y hy hg⟩, hg⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩

end LiZhongQC

