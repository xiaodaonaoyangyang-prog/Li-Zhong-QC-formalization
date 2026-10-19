import LiZhongQC.Ch06.S22_RiemannSurfaces
import LiZhongQC.Lemmas.UniformizedUniqueness
import Jacobians.RiemannRoch
import Jacobians.ProperDegree.DegreeOneSphere
import Jacobians.SphereTopology.SphereSimplyConnected
import Jacobians.SphereTopology.VanKampen
import LiZhongExternal.Classification.SchottkyClassification01

/-!
# The projective plane carries no Riemann surface structure

A closed Riemann surface is not homeomorphic to the closed non-orientable normal form `N₁ = ℝP²`
(`Quot (NonOrientableRel 1 0)`), given the presentation `π₁(N₁) = ⟨a | a²⟩`.

* `s78no_finrank_hom_eq_two_genus`: `dim_ℝ Hom(π₁ X, ℝ) = 2 · genus X` (S22 real period map).
* `s78no_genus_eq_zero_of_hom_eq_zero`, `s78no_simplyConnected_of_genus_zero`: no real characters
  forces genus `0`, and genus `0` forces `X ≃ₜ S²` (Riemann–Roch), hence simple connectivity.
* `s78no_rp2Group_hom_eq_zero`, `s78no_rp2Group_of_ne_one`: `⟨a | a²⟩` has no real characters
  and is nontrivial.
* `s78no_not_homeo_rp2`: the exclusion.
-/

open Complex Set Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

/-- For a compact Riemann surface `X`, the real vector space of real characters of `π₁(X, x)` has
dimension `2 · genus X`.  (The real period map of S22 is an `ℝ`-linear bijection
`(Fin (genus X) → ℂ) → Hom(π₁(X, x), ℝ)`: `k22rr_exists_real_period_map`, `k22rr_pi_injective`,
`k22rr_pd_surjective`.) -/
theorem s78no_finrank_hom_eq_two_genus (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x : X) :
    Module.finrank ℝ (Additive (FundamentalGroup X x) →+ ℝ) = 2 * genus X := by
  obtain ⟨P, hP⟩ := k22rr_exists_real_period_map (X := X) x
  have hinj := k22rr_pi_injective x P hP
  have hsurj := k22rr_pd_surjective x P hP
  let e := LinearEquiv.ofBijective P ⟨hinj, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- A compact Riemann surface without nonzero real characters of `π₁` has genus `0`. -/
theorem s78no_genus_eq_zero_of_hom_eq_zero (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x : X)
    (h : ∀ φ : Additive (FundamentalGroup X x) →+ ℝ, φ = 0) : genus X = 0 := by
  have h1 := s78no_finrank_hom_eq_two_genus X x
  have : Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) :=
    ⟨fun a b => (h a).trans (h b).symm⟩
  rw [Module.finrank_zero_of_subsingleton] at h1
  omega

/-- A compact Riemann surface of genus `0` is simply connected: Riemann–Roch gives a meromorphic
function with a single simple pole, hence `X ≃ₜ S²`, and `S²` is simply connected. -/
theorem s78no_simplyConnected_of_genus_zero (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (hg : genus X = 0) : SimplyConnectedSpace X := by
  obtain ⟨P, f, hf⟩ := Jacobians.exists_singleSimplePole_of_genus_zero_of_rr (X := X) hg
  obtain ⟨e⟩ := Jacobians.nonempty_homeo_sphere_of_singleSimplePole f hf
  have := Jacobians.RiemannSphere.simplyConnectedSpace_sphere_of_vanKampen
    Jacobians.RiemannSphere.VanKampen.twoOpenVanKampen_holds
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- In `⟨a | a²⟩` the generator squares to `1`. -/
theorem s78no_rp2Group_of_sq :
    (PresentedGroup.of (0 : Fin 1) :
      PresentedGroup ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
        Set (FreeGroup (Fin 1)))) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} : Set (FreeGroup (Fin 1))))
    (x := (List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod) rfl
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    map_pow] at h
  exact h

/-- `⟨a | a²⟩` has no nonzero real characters. -/
theorem s78no_rp2Group_hom_eq_zero
    (φ : Additive (PresentedGroup ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
      Set (FreeGroup (Fin 1)))) →+ ℝ) : φ = 0 := by
  set G := PresentedGroup ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
      Set (FreeGroup (Fin 1)))
  have hgen : φ (Additive.ofMul (PresentedGroup.of (0 : Fin 1) : G)) = 0 := by
    have h2 : φ (Additive.ofMul ((PresentedGroup.of (0 : Fin 1) : G) ^ 2)) = 0 := by
      rw [s78no_rp2Group_of_sq]; exact φ.map_zero
    rw [ofMul_pow, φ.map_nsmul] at h2
    simpa using h2
  refine AddMonoidHom.ext fun g => ?_
  change φ g = 0
  have hall : ∀ g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 1 → G)),
      φ (Additive.ofMul g) = 0 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [Subsingleton.elim i 0]; exact hgen
    | one => exact φ.map_zero
    | mul x y _ _ hx hy => rw [ofMul_mul, φ.map_add, hx, hy, add_zero]
    | inv x _ hx => rw [ofMul_inv, φ.map_neg, hx, neg_zero]
  exact hall (Additive.toMul g) (by rw [PresentedGroup.closure_range_of]; trivial)

/-- The generator of `⟨a | a²⟩` is not `1` (map to `ℤˣ`, `a ↦ -1`). -/
theorem s78no_rp2Group_of_ne_one :
    (PresentedGroup.of (0 : Fin 1) :
      PresentedGroup ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
        Set (FreeGroup (Fin 1)))) ≠ 1 := by
  intro h
  have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
      Set (FreeGroup (Fin 1))), FreeGroup.lift (fun _ : Fin 1 => (-1 : ℤˣ)) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    simp [List.ofFn_succ]
  have := congrArg (PresentedGroup.toGroup hrel) h
  rw [PresentedGroup.toGroup.of, map_one] at this
  exact absurd this (by decide)

/-- **A closed Riemann surface is not homeomorphic to `ℝP² = Quot (NonOrientableRel 1 0)`**, given
`π₁(ℝP²) ≅ ⟨a | a²⟩` at every basepoint.  If `S ≃ₜ ℝP²`, then `π₁ S ≅ ⟨a | a²⟩` has no real
characters, so `genus S = 0`, so `S` is simply connected; but `⟨a | a²⟩` is nontrivial. -/
theorem s78no_not_homeo_rp2 (S : Type u) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    (hpi : ∀ x : Quot (LeanEval.Topology.ClassificationOfSurfaces.NonOrientableRel 1 0),
      Nonempty (FundamentalGroup
        (Quot (LeanEval.Topology.ClassificationOfSurfaces.NonOrientableRel 1 0)) x ≃*
        PresentedGroup ({(List.ofFn fun i : Fin 1 => FreeGroup.of i ^ 2).prod} :
          Set (FreeGroup (Fin 1))))) :
    ¬ Nonempty (S ≃ₜ Quot (LeanEval.Topology.ClassificationOfSurfaces.NonOrientableRel 1 0)) := by
  rintro ⟨h⟩
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨e₂⟩ := hpi (h s₀)
  let E := (fundamentalGroupMulEquivOfHomeomorph h (x := s₀) rfl).trans e₂
  have hzero : ∀ φ : Additive (FundamentalGroup S s₀) →+ ℝ, φ = 0 := by
    intro φ
    have h0 := s78no_rp2Group_hom_eq_zero (φ.comp E.symm.toAdditive.toAddMonoidHom)
    refine AddMonoidHom.ext fun g => ?_
    have := congrArg (fun ψ => ψ (Additive.ofMul (E (Additive.toMul g)))) h0
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
    simpa using this
  have := s78no_simplyConnected_of_genus_zero S (s78no_genus_eq_zero_of_hom_eq_zero S s₀ hzero)
  apply s78no_rp2Group_of_ne_one
  have : E.symm (PresentedGroup.of 0) = E.symm 1 := Subsingleton.elim _ _
  exact E.symm.injective this

end LiZhongQC
