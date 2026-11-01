import LiZhongQC.Lemmas.SchottkyHalfRetraction
import LiZhongQC.Lemmas.SchottkyBoundaryCircleMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

open Set Metric CategoryTheory

namespace LiZhongQC

universe u v

/-- Exact basepoint bookkeeping for composition of two actual induced
fundamental-group maps. Both endpoint casts are retained explicitly. -/
theorem s78dg_fundamental_mapOfEq_comp {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (a : A) (b : B) (c : C)
    (hf : f a = b) (hg : g b = c) (γ : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf γ) =
      FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) γ := by
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    ← Path.Homotopic.Quotient.map_comp]

/-- A genuine retraction and an actual homotopy from id to inclusion
after retraction give an isomorphism on the actual fundamental groups.
Its inverse is exactly the induced retraction with its basepoint cast.
The map is not replaced by a chosen abstract group isomorphism. -/
theorem s78dg_retraction_fundamental_equiv {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : C(X, Y)) (r : C(Y, X)) (hre : ∀ x, r (e x) = x)
    (H : ContinuousMap.Homotopy (ContinuousMap.id Y) (e.comp r)) (x : X) :
    ∃ E : FundamentalGroup X x ≃* FundamentalGroup Y (e x),
      (∀ γ, E γ = FundamentalGroup.map e x γ) ∧
      (∀ δ, E.symm δ = FundamentalGroup.mapOfEq r (hre x) δ) := by
  have hleftMap : r.comp e = ContinuousMap.id X := by
    ext a
    exact hre a
  let htop : ContinuousMap.HomotopyEquiv X Y := {
    toFun := e
    invFun := r
    left_inv := by
      rw [hleftMap]
    right_inv := ⟨H.symm⟩ }
  let G := FundamentalGroupoidFunctor.equivOfHomotopyEquiv htop
  have hbij : Function.Bijective (FundamentalGroup.map e x) := by
    have hG :=
      G.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)
    exact End.homEquiv.symm.bijective.comp (hG.comp End.homEquiv.bijective)
  let E : FundamentalGroup X x ≃* FundamentalGroup Y (e x) := {
    toEquiv := Equiv.ofBijective (FundamentalGroup.map e x) hbij
    map_mul' := (FundamentalGroup.map e x).map_mul' }
  have hleft (γ : FundamentalGroup X x) :
      FundamentalGroup.mapOfEq r (hre x) (FundamentalGroup.map e x γ) = γ := by
    obtain ⟨γ⟩ := γ
    rw [FundamentalGroup.mapOfEq_apply]
    refine Quotient.inductionOn γ ?_
    intro p
    apply CategoryTheory.End.ext
    change Path.Homotopic.Quotient.mk
      (((p.map e.continuous).map r.continuous).cast (hre x).symm (hre x).symm) =
        Path.Homotopic.Quotient.mk p
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact hre (p t)
  refine ⟨E, fun _ => rfl, ?_⟩
  intro δ
  obtain ⟨γ, rfl⟩ := E.surjective δ
  rw [E.symm_apply_apply]
  exact (hleft γ).symm

/-- Compatibility of the inverse half/core group isomorphism with a
strict boundary-map triangle, at an explicitly identified basepoint. -/
theorem s78dg_retraction_boundary_triangle {T X Y : Type*}
    [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    (e : C(X, Y)) (r : C(Y, X)) (hre : ∀ x, r (e x) = x)
    (c : C(T, X)) (f : C(T, Y)) (htri : r.comp f = c)
    (ζ : T) (x : X) (hc : c ζ = x) (hf : f ζ = e x)
    (E : FundamentalGroup X x ≃* FundamentalGroup Y (e x))
    (hE : ∀ δ, E.symm δ = FundamentalGroup.mapOfEq r (hre x) δ)
    (γ : FundamentalGroup T ζ) :
    E.symm (FundamentalGroup.mapOfEq f hf γ) = FundamentalGroup.mapOfEq c hc γ := by
  rw [hE, s78dg_fundamental_mapOfEq_comp f r ζ (e x) x hf (hre x)]
  subst c
  rfl

/-- Apply the accepted actual strong deformation to either literal
thickened half. No retraction, homotopy or group equivalence is an input. -/
theorem s78dg_actual_half_core_equiv
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j) (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (b : Bool) :
    let N : Fin m → Set (s31dt_Core F) := fun j =>
      Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j))
    let U : Set (s31dt_Double F) :=
      range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ j, N j)
    ∃ (r : C(U, s31dt_Core F)) (e : C(s31dt_Core F, U)) (hre : ∀ x, r (e x) = x),
      (∀ q, r q = s31dt_project F q.val) ∧
      (∀ x, (e x).val = s31dt_side F b x) ∧
      (∀ x, ∃ E : FundamentalGroup (s31dt_Core F) x ≃* FundamentalGroup U (e x),
        (∀ γ, E γ = FundamentalGroup.map e x γ) ∧
        (∀ δ, E.symm δ = FundamentalGroup.mapOfEq r (hre x) δ)) := by
  obtain ⟨r, e, H, hr, he, hre, _, _⟩ :=
    s31dt_actual_half_strong_deformation F v R hR hs hD hdisj b
  exact ⟨r, e, hre, hr, he, fun x => s78dg_retraction_fundamental_equiv e r hre H x⟩

/-- The accepted boundary circles map into both actual halves, and
their induced groups agree with the same actual core boundary map under
the half/core isomorphisms. All coordinates and seam points are retained.
This is the peripheral-map compatibility needed by the stable-letter
presentation, without assuming a core canonical presentation. -/
theorem s78dg_actual_boundary_core_compatibility
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j) (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (p : Fin m → s31dt_Core F) (hp : ∀ j, (p j).val ∈ frontier (F.D j)) (j : Fin m) :
    let T := ↥(sphere (0 : ℂ) 1)
    let N : Fin m → Set (s31dt_Core F) := fun k =>
      Subtype.val ⁻¹' (v k '' ball (0 : ℂ) (R k))
    let U : Bool → Set (s31dt_Double F) := fun b =>
      range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ k, N k)
    ∃ (c : C(T, s31dt_Core F)) (ζ : T) (hcp : c ζ = p j)
      (f : ∀ b, C(T, U b)),
      (∀ z, (c z).val = v j z.val) ∧ (∀ z, c z ∈ s31dt_boundary F) ∧
      (∀ b, ∃ (e : C(s31dt_Core F, U b))
        (E : FundamentalGroup (s31dt_Core F) (p j) ≃* FundamentalGroup (U b) (e (p j)))
        (hbase : f b ζ = e (p j)),
        (∀ x, (e x).val = s31dt_side F b x) ∧
        (∀ γ : FundamentalGroup T ζ,
          E (FundamentalGroup.mapOfEq c hcp γ) = FundamentalGroup.mapOfEq (f b) hbase γ)) := by
  let T := ↥(sphere (0 : ℂ) 1)
  let N : Fin m → Set (s31dt_Core F) := fun k =>
    Subtype.val ⁻¹' (v k '' ball (0 : ℂ) (R k))
  let U : Bool → Set (s31dt_Double F) := fun b =>
    range (s31dt_side F b) ∪ s31dt_project F ⁻¹' (⋃ k, N k)
  obtain ⟨c, ζ, w, i, r₀, hcval, hcB, hcp, _, hwfalse, hwtrue, hi, _, _⟩ :=
    s31dt_boundary_circle_maps F v R hR hs hD p hp j
  let f : ∀ b, C(T, U b) := fun b => (i b).comp w
  refine ⟨c, ζ, hcp, f, hcval, hcB, ?_⟩
  intro b
  obtain ⟨r, e, hre, hr, he, hEquiv⟩ := s78dg_actual_half_core_equiv F v R hR hs hD hdisj b
  obtain ⟨E, _, hEinv⟩ := hEquiv (p j)
  have hw (z : T) : (w z).val = s31dt_side F b (c z) := by
    cases b
    · exact hwfalse z
    · exact hwtrue z
  have hbase : f b ζ = e (p j) := by
    apply Subtype.ext
    change (i b (w ζ)).val = (e (p j)).val
    rw [hi, hw, hcp, he]
  have htri : r.comp (f b) = c := by
    refine ContinuousMap.ext fun z => ?_
    change r (i b (w z)) = c z
    rw [hr, hi, hwfalse]
    exact s31dt_project_side F false (c z)
  refine ⟨e, E, hbase, he, ?_⟩
  intro γ
  apply E.symm.injective
  rw [E.symm_apply_apply]
  exact (s78dg_retraction_boundary_triangle e r hre c (f b) htri ζ (p j) hcp hbase
    E hEinv γ).symm

end LiZhongQC
