import LiZhongQC.Lemmas.SchottkyNonOrientable6
import LiZhongQC.Lemmas.SchottkyNonOrientableSmall
import LiZhongQC.Lemmas.SchottkyClosedSurface12

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval
open scoped Manifold ContDiff

universe u

namespace LiZhongQC
/-- Additive real characters of the nonorientable surface group are the real vectors with zero sum
(`2 Σ vᵢ = 0`), so they form a space of dimension `p - 1`. -/
theorem s78dg_no_hom_dim (p : ℕ) (hp : 1 ≤ p) :
    FiniteDimensional ℝ (Additive (PresentedGroup ({(List.ofFn fun i : Fin p =>
      FreeGroup.of i ^ 2).prod} : Set (FreeGroup (Fin p)))) →+ ℝ) ∧
    Module.finrank ℝ (Additive (PresentedGroup ({(List.ofFn fun i : Fin p =>
      FreeGroup.of i ^ 2).prod} : Set (FreeGroup (Fin p)))) →+ ℝ) = p - 1 := by
  let R : Set (FreeGroup (Fin p)) := {(List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod}
  let G := PresentedGroup R
  -- the value of the relator under a homomorphism
  have hψ : ∀ v : Fin p → ℝ, FreeGroup.lift (fun i => Multiplicative.ofAdd (v i))
      (List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod =
        Multiplicative.ofAdd (∑ i, 2 * v i) := by
    intro v
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn, ofAdd_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [pow_two, ← ofAdd_add]
    ring_nf
  let L : (Additive G →+ ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    { toFun := fun χ i => χ (Additive.ofMul (PresentedGroup.of i : G))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective L := by
    intro χ ψ h
    have hm : χ.toMultiplicativeRight = ψ.toMultiplicativeRight := by
      apply PresentedGroup.ext
      intro i
      change Multiplicative.ofAdd (χ (Additive.ofMul (PresentedGroup.of i : G))) =
        Multiplicative.ofAdd (ψ (Additive.ofMul (PresentedGroup.of i : G)))
      exact congrArg Multiplicative.ofAdd (congrFun h i)
    exact AddMonoidHom.toMultiplicativeRight.injective hm
  let S : (Fin p → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin p, LinearMap.proj i
  have hS : ∀ v, S v = ∑ i, v i := by
    intro v
    simp [S]
  have hrange : LinearMap.range L = LinearMap.ker S := by
    ext v
    constructor
    · rintro ⟨χ, rfl⟩
      rw [LinearMap.mem_ker, hS]
      let g : G →* Multiplicative ℝ := χ.toMultiplicativeRight
      have h1 : g (PresentedGroup.mk R (List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod) = 1 := by
        rw [PresentedGroup.one_of_mem (Set.mem_singleton _)]
        exact map_one g
      have h2 : g.comp (PresentedGroup.mk R) = FreeGroup.lift (fun i => Multiplicative.ofAdd (L χ i)) := by
        apply FreeGroup.ext_hom
        intro i
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
        rfl
      have h3 := DFunLike.congr_fun h2 (List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod
      rw [MonoidHom.comp_apply, h1, hψ] at h3
      have h4 : (∑ i, 2 * L χ i) = 0 := by
        have := congrArg Multiplicative.toAdd h3
        simpa using this.symm
      rw [← Finset.mul_sum] at h4
      linarith
    · intro hv
      rw [LinearMap.mem_ker, hS] at hv
      let f : Fin p → Multiplicative ℝ := fun i => Multiplicative.ofAdd (v i)
      have hrel : ∀ r ∈ R, FreeGroup.lift f r = 1 := by
        intro r hr
        rw [Set.mem_singleton_iff] at hr
        subst hr
        rw [hψ, ← Finset.mul_sum, hv]
        simp
      let φ : G →* Multiplicative ℝ := PresentedGroup.toGroup hrel
      refine ⟨φ.toAdditiveLeft, ?_⟩
      funext i
      change (φ (PresentedGroup.of i : G)).toAdd = v i
      exact congrArg Multiplicative.toAdd (PresentedGroup.toGroup.of hrel)
  have hfin : FiniteDimensional ℝ (Additive G →+ ℝ) :=
    FiniteDimensional.of_injective L hinj
  refine ⟨hfin, ?_⟩
  have hsurj : Function.Surjective S := by
    intro r
    refine ⟨Pi.single ⟨0, hp⟩ r, ?_⟩
    rw [hS]
    simp
  have hrk := LinearMap.finrank_range_add_finrank_ker S
  have hrange_top : LinearMap.range S = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [hrange_top, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hrk
  have hl : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ (Additive G →+ ℝ) :=
    LinearMap.finrank_range_of_inj hinj
  rw [← hl, hrange]
  omega

/-- **Even nonorientable surfaces are not Riemann surfaces.**  If a closed Riemann surface were
homeomorphic to `Quot (NonOrientableRel p 0)` with `p` even, the dimension of its real period space
`2 · genus` would equal `p - 1`, which is odd. -/
theorem s78dg_no_nonorientable_even {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (p : ℕ) (hp : 1 ≤ p) (hpe : Even p) (φ : X ≃ₜ Quot (NonOrientableRel p 0)) : False := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨e⟩ := s78dg_pi1_transport φ (fun y => s78dg_nonor_pi1 p hp y) x
  obtain ⟨hfin, hdim⟩ := s78dg_no_hom_dim p hp
  let T : (Additive (FundamentalGroup X x) →+ ℝ) ≃ₗ[ℝ]
      (Additive (PresentedGroup ({(List.ofFn fun i : Fin p => FreeGroup.of i ^ 2).prod} :
        Set (FreeGroup (Fin p)))) →+ ℝ) :=
    { toFun := fun χ => χ.comp e.symm.toMonoidHom.toAdditive
      invFun := fun ψ => ψ.comp e.toMonoidHom.toAdditive
      left_inv := by
        intro χ
        apply AddMonoidHom.ext
        intro z
        change χ (Additive.ofMul (e.symm (e z.toMul))) = χ z
        rw [e.symm_apply_apply]
        rfl
      right_inv := by
        intro ψ
        apply AddMonoidHom.ext
        intro z
        change ψ (Additive.ofMul (e (e.symm z.toMul))) = ψ z
        rw [e.apply_symm_apply]
        rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have h1 := T.finrank_eq
  have h2 := s78no_finrank_hom_eq_two_genus X x
  rw [hdim] at h1
  rw [h2] at h1
  obtain ⟨k, hk⟩ := hpe
  omega


end LiZhongQC
