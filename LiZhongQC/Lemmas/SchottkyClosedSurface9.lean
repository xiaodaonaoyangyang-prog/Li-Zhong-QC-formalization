import LiZhongExternal.DifferentialGeometry.SchottkyVanKampen
import LiZhongQC.Lemmas.SchottkyClosedSurface2
import LiZhongQC.Lemmas.SchottkyClosedSurface5
import LiZhongQC.Lemmas.SchottkyClosedSurface7
import LiZhongQC.Lemmas.SchottkyClosedSurface8

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

theorem s78dg_cs_Y_union (p : ℕ) (hp : 1 ≤ p) (S T : Set ℝ) :
    s78dg_cs_Y p hp (S ∪ T) = s78dg_cs_Y p hp S ∪ s78dg_cs_Y p hp T := by
  ext q
  constructor
  · rintro ⟨a, ha | ha, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩

theorem s78dg_cs_Y_inter (p : ℕ) (hp : 1 ≤ p) (S T : Set ℝ)
    (hS : (∀ u, u + ((4 * p : ℕ) : ℝ) ∈ S ↔ u ∈ S) ∧
      (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + x ∈ S ↔ 4 * (i : ℝ) + 3 - x ∈ S)) ∧
      (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + 1 + x ∈ S ↔ 4 * (i : ℝ) + 4 - x ∈ S)))
    (hT : (∀ u, u + ((4 * p : ℕ) : ℝ) ∈ T ↔ u ∈ T) ∧
      (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + x ∈ T ↔ 4 * (i : ℝ) + 3 - x ∈ T)) ∧
      (∀ (i : Fin p) (x : ℝ), 0 ≤ x → x ≤ 1 → (4 * (i : ℝ) + 1 + x ∈ T ↔ 4 * (i : ℝ) + 4 - x ∈ T))) :
    s78dg_cs_Y p hp S ∩ s78dg_cs_Y p hp T = s78dg_cs_Y p hp (S ∩ T) := by
  ext q
  constructor
  · rintro ⟨hqS, hqT⟩
    obtain ⟨a, ha, rfl⟩ := hqS
    have hT' := (s78dg_cs_Y_mem p hp T hT.1 hT.2.1 hT.2.2 a).1 hqT
    exact ⟨a, ⟨ha, hT'⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩


/-- `mapOfEq` of a map inducing a bijection is a bijection. -/
theorem s78dg_pi1_mapOfEq_bijective {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
    (f : C(A, Z)) (a₀ : A) (z₀ : Z) (h : f a₀ = z₀) (hb : Function.Bijective (FundamentalGroup.map f a₀)) :
    Function.Bijective (FundamentalGroup.mapOfEq f h) := by
  subst h
  have : (FundamentalGroup.mapOfEq f rfl : FundamentalGroup A a₀ →* FundamentalGroup Z (f a₀)) =
      FundamentalGroup.map f a₀ := by
    ext p
    rw [FundamentalGroup.mapOfEq_apply]
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  rw [this]; exact hb

/-- `mapOfEq` on the class of a loop is the class of any loop with the image values. -/
theorem s78dg_pi1_mapOfEq_mk {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z))
    (y₀ : Y) (z₀ : Z) (h : f y₀ = z₀) (ℓ : Path y₀ y₀) (L : Path z₀ z₀)
    (hL : ∀ t, L t = f (ℓ t)) :
    FundamentalGroup.mapOfEq f h (Path.Homotopic.Quotient.mk ℓ) = Path.Homotopic.Quotient.mk L := by
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.mk (ℓ.map f.continuous)).cast h.symm h.symm = _
  rw [← Path.Homotopic.Quotient.mk_cast]
  congr 1
  ext t
  rw [hL t]
  rfl

open DifferentialGeometry.Topology.VanKampen in
/-- **Wedge step, loop form.**  If the two open pieces of `X` are (up to maps inducing isomorphisms on `π₁`)
spaces `A`, `B` with `π₁(A) ≅ F(α)`, `π₁(B) ≅ F(β)`, then `π₁(X) ≅ F(α ⊕ β)`, and a loop of `X` whose
values are those of the image of a loop of `A` (resp. `B`) goes to the corresponding word. -/
theorem s78dg_wedge_step_loops {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace (↑(U ∩ V))] {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (fA : C(A, ↥U)) (a₀ : A) (hA : fA a₀ = leftBasepoint U x₀ hx₀.1)
    (hAb : Function.Bijective (FundamentalGroup.map fA a₀)) {α : Type}
    (eA : FundamentalGroup A a₀ ≃* FreeGroup α)
    (fB : C(B, ↥V)) (b₀ : B) (hB : fB b₀ = rightBasepoint V x₀ hx₀.2)
    (hBb : Function.Bijective (FundamentalGroup.map fB b₀)) {β : Type}
    (eB : FundamentalGroup B b₀ ≃* FreeGroup β) :
    ∃ e : FundamentalGroup X x₀ ≃* FreeGroup (α ⊕ β),
      (∀ (ℓ : Path a₀ a₀) (L : Path x₀ x₀), (∀ t, L t = ((fA (ℓ t) : ↥U) : X)) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
          FreeGroup.map Sum.inl (eA (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)))) ∧
      (∀ (ℓ : Path b₀ b₀) (L : Path x₀ x₀), (∀ t, L t = ((fB (ℓ t) : ↥V) : X)) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
          FreeGroup.map Sum.inr (eB (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)))) := by
  let mA := FundamentalGroup.mapOfEq fA hA
  let mB := FundamentalGroup.mapOfEq fB hB
  let eU : fundamentalGroupFactor U V x₀ hx₀ false ≃* FreeGroup α :=
    (MulEquiv.ofBijective mA (s78dg_pi1_mapOfEq_bijective fA a₀ _ hA hAb)).symm.trans eA
  let eV : fundamentalGroupFactor U V x₀ hx₀ true ≃* FreeGroup β :=
    (MulEquiv.ofBijective mB (s78dg_pi1_mapOfEq_bijective fB b₀ _ hB hBb)).symm.trans eB
  obtain ⟨e, he1, he2⟩ := s78dg_wedge_free_step_gen U V hU hV hcover x₀ hx₀ eU eV
  refine ⟨e, fun ℓ L hL => ?_, fun ℓ L hL => ?_⟩
  · have hℓ : ((FundamentalGroup.mapOfEq fA hA) (Path.Homotopic.Quotient.mk ℓ) :
        FundamentalGroup ↥U (leftBasepoint U x₀ hx₀.1)) =
        Path.Homotopic.Quotient.mk ((ℓ.map fA.continuous).cast hA.symm hA.symm) :=
      s78dg_pi1_mapOfEq_mk fA a₀ _ hA ℓ _ (fun t => rfl)
    have hL' : (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
        (Path.Homotopic.Quotient.mk ((ℓ.map fA.continuous).cast hA.symm hA.symm)) =
        Path.Homotopic.Quotient.mk L :=
      s78dg_pi1_mapOfEq_mk (subsetToAmbient U) (leftBasepoint U x₀ hx₀.1) x₀
        (leftBasepoint_toAmbient U x₀ hx₀.1) _ L (fun t => hL t)
    have h1 := he1 (mA (Path.Homotopic.Quotient.mk ℓ))
    have key : eU (mA (Path.Homotopic.Quotient.mk ℓ)) = eA (Path.Homotopic.Quotient.mk ℓ) :=
      congrArg eA ((MulEquiv.ofBijective mA (s78dg_pi1_mapOfEq_bijective fA a₀ _ hA hAb)).symm_apply_apply
        (Path.Homotopic.Quotient.mk ℓ))
    rw [key] at h1
    rw [show mA (Path.Homotopic.Quotient.mk ℓ) = Path.Homotopic.Quotient.mk
      ((ℓ.map fA.continuous).cast hA.symm hA.symm) from hℓ, hL'] at h1
    exact h1
  · have hℓ : ((FundamentalGroup.mapOfEq fB hB) (Path.Homotopic.Quotient.mk ℓ) :
        FundamentalGroup ↥V (rightBasepoint V x₀ hx₀.2)) =
        Path.Homotopic.Quotient.mk ((ℓ.map fB.continuous).cast hB.symm hB.symm) :=
      s78dg_pi1_mapOfEq_mk fB b₀ _ hB ℓ _ (fun t => rfl)
    have hL' : (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
        (Path.Homotopic.Quotient.mk ((ℓ.map fB.continuous).cast hB.symm hB.symm)) =
        Path.Homotopic.Quotient.mk L :=
      s78dg_pi1_mapOfEq_mk (subsetToAmbient V) (rightBasepoint V x₀ hx₀.2) x₀
        (rightBasepoint_toAmbient V x₀ hx₀.2) _ L (fun t => hL t)
    have h1 := he2 (mB (Path.Homotopic.Quotient.mk ℓ))
    have key : eV (mB (Path.Homotopic.Quotient.mk ℓ)) = eB (Path.Homotopic.Quotient.mk ℓ) :=
      congrArg eB ((MulEquiv.ofBijective mB (s78dg_pi1_mapOfEq_bijective fB b₀ _ hB hBb)).symm_apply_apply
        (Path.Homotopic.Quotient.mk ℓ))
    rw [key] at h1
    rw [show mB (Path.Homotopic.Quotient.mk ℓ) = Path.Homotopic.Quotient.mk
      ((ℓ.map fB.continuous).cast hB.symm hB.symm) from hℓ, hL'] at h1
    exact h1

end LiZhongQC
