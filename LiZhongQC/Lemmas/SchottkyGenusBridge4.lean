import LiZhongQC.Lemmas.SchottkyNonOrientable7

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology
open scoped Manifold ContDiff

namespace LiZhongQC

universe u

/-- **Genus from the topological classification.**  A closed Riemann surface which, by the
classification of surfaces, is homeomorphic to the sphere or to a polygon quotient, has a genus,
once the nonorientable odd cases (`p = 1` and odd `p ≥ 3`) are excluded. -/
theorem s78dg_has_genus_of_cls {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [CompactSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    (hcls : Nonempty (S ≃ₜ SphereRepresentative) ∨
      (∃ p n : ℕ, (1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
      (∃ p n : ℕ, 1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))))
    (hodd : ∀ p : ℕ, 3 ≤ p → Odd p → ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p 0)))
    (hone : ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel 1 0))) :
    ∃ g : ℕ, HasGenus S g := by
  have hS : ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
    fun x => s78dg_riemann_plane_nbhd S x
  rcases hcls with h0 | ⟨p, n, hpn, h1⟩ | ⟨p, n, hp, h2⟩
  · obtain ⟨φ⟩ := h0
    exact ⟨0, inferInstance, fun x => s78dg_pi1_transport φ (fun y => s78dg_sphere_pi1 y) x⟩
  · obtain ⟨φ⟩ := h1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hp : 1 ≤ p := hpn.resolve_right (by norm_num)
      exact ⟨p, inferInstance, fun x =>
        s78dg_pi1_transport φ (fun y => s78dg_cs_pi1_closed p hp y) x⟩
    · exact (s78dg_no_orientable_boundary hS p n hn φ).elim
  · obtain ⟨φ⟩ := h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.even_or_odd p with he | ho
      · exact (s78dg_no_nonorientable_even p hp he φ).elim
      · rcases eq_or_lt_of_le hp with h1 | h3
        · subst h1
          exact (hone ⟨φ⟩).elim
        · exact (hodd p (by obtain ⟨k, hk⟩ := ho; omega) ho ⟨φ⟩).elim
    · exact (s78dg_no_nonorientable_boundary hS p n hn φ).elim

end LiZhongQC
