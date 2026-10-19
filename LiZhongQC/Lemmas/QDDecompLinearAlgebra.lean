import Mathlib

open Complex Set Metric Filter Topology
noncomputable section
namespace LiZhongQC
universe u

/-- (S4) Linear algebra: a real involution `T` anticommuting with a complex structure `j`
(`j ∘ j = -1`) splits the space into its `±1` eigenspaces, exchanged by `j`, so the real dimension is twice
that of the fixed space. -/
theorem s31qd_conj_involution_finrank {V : Type*} [AddCommGroup V] [Module ℝ V] (T j : V →ₗ[ℝ] V)
    (hT : ∀ v, T (T v) = v) (hj : ∀ v, j (j v) = -v) (hTj : ∀ v, T (j v) = -(j (T v))) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) := by
  classical
  have hK : ∀ v, v ∈ LinearMap.ker (T - LinearMap.id) ↔ T v = v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hK' : ∀ v, v ∈ LinearMap.ker (T + LinearMap.id) ↔ T v = -v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  -- `V ≃ K × K'`
  let e : V ≃ₗ[ℝ] (LinearMap.ker (T - LinearMap.id)) × (LinearMap.ker (T + LinearMap.id)) :=
    { toFun := fun v =>
        (⟨(2⁻¹ : ℝ) • (v + T v), by
            rw [hK, map_smul, map_add, hT]
            rw [add_comm]⟩,
         ⟨(2⁻¹ : ℝ) • (v - T v), by
            rw [hK', map_smul, map_sub, hT]
            module⟩)
      map_add' := fun v w => by
        apply Prod.ext <;> apply Subtype.ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add,
          Submodule.coe_add] <;> module
      map_smul' := fun c v => by
        apply Prod.ext <;> apply Subtype.ext <;> simp only [map_smul, Prod.smul_fst, Prod.smul_snd,
          Submodule.coe_smul, RingHom.id_apply] <;> module
      invFun := fun p => p.1.1 + p.2.1
      left_inv := fun v => by
        simp only
        module
      right_inv := fun p => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
        have ha' := (hK a).1 ha
        have hb' := (hK' b).1 hb
        have hab : T (a + b) = a - b := by rw [map_add, ha', hb', sub_eq_add_neg]
        apply Prod.ext <;> apply Subtype.ext <;> simp only [hab] <;> module }
  -- `K' ≃ K` through `j`
  let f : (LinearMap.ker (T + LinearMap.id)) ≃ₗ[ℝ] (LinearMap.ker (T - LinearMap.id)) :=
    { toFun := fun x => ⟨j x.1, by
        have hx := (hK' x.1).1 x.2
        rw [hK, hTj, hx, map_neg, neg_neg]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add]
      map_smul' := fun c x => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
      invFun := fun y => ⟨-j y.1, by
        have hy := (hK y.1).1 y.2
        rw [hK', map_neg, hTj, hy]⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp only [map_neg, hj, neg_neg]
      right_inv := fun y => by
        apply Subtype.ext
        simp only [map_neg, hj, neg_neg] }
  by_cases hfin : Module.Finite ℝ (LinearMap.ker (T - LinearMap.id))
  · haveI : Module.Finite ℝ (LinearMap.ker (T + LinearMap.id)) :=
      Module.Finite.equiv f.symm
    rw [e.finrank_eq, Module.finrank_prod, f.finrank_eq]
    ring
  · have hV : ¬ Module.Finite ℝ V := by
      intro hV
      exact hfin (Module.Finite.of_injective (LinearMap.ker (T - LinearMap.id)).subtype
        (LinearMap.ker (T - LinearMap.id)).injective_subtype)
    rw [Module.finrank_of_not_finite hV, Module.finrank_of_not_finite hfin]

end LiZhongQC
