import LiZhongQC.Lemmas.SchottkyNonOrientableSmall
import LiZhongQC.Lemmas.SchottkyNonOrientableIndexTwo
import LiZhongQC.Lemmas.SchottkyNonOrientableCover
import LiZhongQC.Lemmas.SchottkyNonOrientable6

/-!
# A closed Riemann surface is not non-orientable

`s78no_not_homeo_nonOrientable`: a closed Riemann surface is not homeomorphic to any closed
non-orientable normal form `N_p = Quot (NonOrientableRel p 0)`, `p ≥ 1`.

* `p = 1`: `s78no_not_homeo_rp2` (genus `0` forces simple connectivity).
* `p ≥ 2`: the index-two subgroup `K ≤ π₁(N_p)` of `s78no_indexTwo_finrank` has
  `dim_ℝ Hom(K, ℝ) = 2p - 3`, odd; the corresponding finite cover of the Riemann surface
  (`s78no_finiteIndex_cover`) is a closed Riemann surface `X` with `π₁(X) ≅ Kᵐᵒᵖ`, so
  `dim_ℝ Hom(π₁ X, ℝ) = 2 · genus X` is even (`s78no_finrank_hom_eq_two_genus`).
-/

open LeanEval.Topology.ClassificationOfSurfaces Set Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

/-- Real characters are transported along group isomorphisms. -/
theorem s78no_finrank_hom_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Module.finrank ℝ (Additive G →+ ℝ) = Module.finrank ℝ (Additive H →+ ℝ) := by
  let L : (Additive G →+ ℝ) ≃ₗ[ℝ] (Additive H →+ ℝ) :=
    { toFun := fun φ => φ.comp (MulEquiv.toAdditive e.symm).toAddMonoidHom
      invFun := fun ψ => ψ.comp (MulEquiv.toAdditive e).toAddMonoidHom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => AddMonoidHom.ext fun g => by simp
      right_inv := fun ψ => AddMonoidHom.ext fun g => by simp }
  exact L.finrank_eq

/-- Real characters of `Gᵐᵒᵖ` and of `G` agree (`ℝ` is commutative). -/
theorem s78no_finrank_hom_mulOpposite (G : Type*) [Group G] :
    Module.finrank ℝ (Additive Gᵐᵒᵖ →+ ℝ) = Module.finrank ℝ (Additive G →+ ℝ) := by
  let L : (Additive Gᵐᵒᵖ →+ ℝ) ≃ₗ[ℝ] (Additive G →+ ℝ) :=
    { toFun := fun φ =>
        { toFun := fun g => φ (Additive.ofMul (MulOpposite.op (Additive.toMul g)))
          map_zero' := by simpa using φ.map_zero
          map_add' := fun a b => by
            rw [toMul_add, MulOpposite.op_mul, ofMul_mul, map_add, add_comm] }
      invFun := fun ψ =>
        { toFun := fun g => ψ (Additive.ofMul (MulOpposite.unop (Additive.toMul g)))
          map_zero' := by simpa using ψ.map_zero
          map_add' := fun a b => by
            rw [toMul_add, MulOpposite.unop_mul, ofMul_mul, map_add, add_comm] }
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => AddMonoidHom.ext fun g => rfl
      right_inv := fun ψ => AddMonoidHom.ext fun g => rfl }
  exact L.finrank_eq

/-- **`p ≥ 2`.**  A closed Riemann surface is not homeomorphic to `N_p`: the index-two cover
would be a closed Riemann surface with an odd-dimensional space of real characters. -/
theorem s78no_not_homeo_nonOrientable_two_le (S : Type u) [TopologicalSpace S] [T2Space S]
    [CompactSpace S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    (p : ℕ) (hp : 2 ≤ p) : ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p 0)) := by
  rintro ⟨φ⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨e₂⟩ := s78dg_nonor_pi1 p (by omega) (φ x₀)
  let E := (fundamentalGroupMulEquivOfHomeomorph φ (x := x₀) rfl).trans e₂
  obtain ⟨K, hKi, hKdim⟩ := s78no_indexTwo_finrank p hp
  set K' : Subgroup (FundamentalGroup S x₀) := K.map (E.symm : _ →* FundamentalGroup S x₀)
    with hK'
  have hK'i : K'.index = 2 := by rw [hK', Subgroup.index_map_equiv]; exact hKi
  haveI : K'.FiniteIndex := ⟨by rw [hK'i]; norm_num⟩
  obtain ⟨X, tX, cX, hT2, hC, hConn, hMan, x, ⟨eX⟩⟩ := s78no_finiteIndex_cover S x₀ K'
  have h1 := s78no_finrank_hom_eq_two_genus X x
  have h2 := s78no_finrank_hom_congr eX
  have h3 := s78no_finrank_hom_mulOpposite K'
  have h4 := s78no_finrank_hom_congr (E.symm.subgroupMap K)
  rw [← hK'] at h4
  omega

/-- **A closed Riemann surface is not homeomorphic to a closed non-orientable normal form**
`N_p = Quot (NonOrientableRel p 0)`, `p ≥ 1`. -/
theorem s78no_not_homeo_nonOrientable (S : Type u) [TopologicalSpace S] [T2Space S]
    [CompactSpace S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    (p : ℕ) (hp : 1 ≤ p) : ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p 0)) := by
  rcases Nat.lt_or_ge p 2 with h | h
  · obtain rfl : p = 1 := by omega
    exact s78no_not_homeo_rp2 S (s78dg_nonor_pi1 1 le_rfl)
  · exact s78no_not_homeo_nonOrientable_two_le S p h

end LiZhongQC
