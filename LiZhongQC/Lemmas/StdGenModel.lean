import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import LiZhongQC.Lemmas.SchottkyClosedSurface12
import LiZhongQC.Lemmas.SchottkyClosedGenus
import LiZhongQC.Lemmas.SchottkyGenusBridge9

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Metric Filter Topology unitInterval
open DifferentialGeometry.Topology.VanKampen
open scoped Manifold ContDiff

/-!
# Model pieces of `s83sg_geometric_system` (R83, S27; 下属1)

* `s83sg_model_homeo` [T1]: a closed Riemann surface of genus `g > 1` is homeomorphic to the normal form `Q g`.
* `s83sg_tracked_pi1` [A]: generator-tracking `π₁` of `Q p` at the vertex.
-/

noncomputable section
namespace LiZhongQC

universe u

/-! Sub-stubs of `s83sg_geometric_system` (R83, S27).  `Q p := Quot (OrientableRel p 0)`.
Petal `j` (`j < 2p`): the loop `t ↦ Ψ (1, E j + fract t)` at the vertex `v₀ = Ψ (1, 0)`, `Ψ = s78dg_cs_Psi_fun`;
petal `2i` is the edge `a_i` and petal `2i+1` the edge `b_i` of the word `a₁b₁a₁⁻¹b₁⁻¹ ⋯`. -/

/-- **[T1]** classification: a closed Riemann surface of genus `g` is homeomorphic to the normal form. -/
theorem s83sg_model_homeo {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀]
    [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    Nonempty (S₀ ≃ₜ Quot (OrientableRel g 0)) := by
  have hc : CompactSpace S₀ := hS.1
  obtain ⟨cs⟩ := s78dg_halfspace_chartedSpace S₀
  have hcls :=
    letI := cs
    classification_of_surfaces S₀
  have hloc : ∀ x : S₀, ∃ U : Set S₀, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
    fun x => s78dg_riemann_plane_nbhd S₀ x
  rcases hcls with ⟨φ⟩ | ⟨p, n, ⟨hpn, ⟨φ⟩⟩ | ⟨hp, ⟨φ⟩⟩⟩
  · -- the sphere has genus `0`
    obtain ⟨φ⟩ := φ
    have h0 : HasGenus S₀ 0 := ⟨hc, fun x => s78dg_pi1_transport φ (fun y => s78dg_sphere_pi1 y) x⟩
    have := closed_surface_genus_unique hS h0
    omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hp : 1 ≤ p := hpn.resolve_right (by norm_num)
      have hp' : HasGenus S₀ p := ⟨hc, fun x => s78dg_pi1_transport φ (fun y => s78dg_cs_pi1_closed p hp y) x⟩
      obtain rfl := closed_surface_genus_unique hS hp'
      exact ⟨φ⟩
    · exact (s78dg_no_orientable_boundary hloc p n hn φ).elim
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (s78no_not_homeo_nonOrientable S₀ p hp ⟨φ⟩).elim
    · exact (s78dg_no_nonorientable_boundary hloc p n hn φ).elim

/-- **[A]** generator-tracking `π₁` of the closed normal form: petal `2i` is sent to `a_i⁻¹`, petal `2i+1` to
`b_i⁻¹` (the sign comes from `θ` in `s78dg_cs_pi1_closed_base`). -/
theorem s83sg_tracked_pi1 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1) :
    ∃ e : FundamentalGroup (Quot (OrientableRel p 0))
        ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ≃*
        surfaceGroup p,
      ∀ (i : Fin p) (L : Path ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
          ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))),
        ((∀ t : I, L t = ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E (2 * i) + Int.fract (t : ℝ)) :
            ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) →
          e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
            (PresentedGroup.of (Sum.inl i : Fin p ⊕ Fin p) : surfaceGroup p)⁻¹) ∧
        ((∀ t : I, L t = ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E (2 * i + 1) + Int.fract (t : ℝ)) :
            ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) →
          e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
            (PresentedGroup.of (Sum.inr i : Fin p ⊕ Fin p) : surfaceGroup p)⁻¹) := by
  classical
  let half : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hhalf : (half : ℝ) = 1 / 2 := rfl
  obtain ⟨e, he⟩ := s78dg_cs_pi1_free p hp one hone
  obtain ⟨β, hβ, hW⟩ := s78dg_cs_boundary_word p hp one hone e he
  obtain ⟨b, γ, hγv, hγgen⟩ := s78dg_cs_overlap_generator p 0
  obtain ⟨θ, hθa, hθb⟩ := s78dg_free_equiv_double p
  obtain ⟨T, hT⟩ := s78dg_free_presented_empty (Fin p ⊕ Fin p)
  have : PathConnectedSpace ↥(s78dg_cs_U p 0) := s78dg_cs_U_pathConnected p hp
  have := s78dg_cs_V_contractible p 0
  have := s78dg_cs_overlap_pathConnected p hp
  have hx₀ : (b : Quot (OrientableRel p 0)) ∈ s78dg_cs_U p 0 ∩ s78dg_cs_V p 0 := b.2
  let x₁ : ↥(s78dg_cs_U p 0) := ⟨(b : Quot (OrientableRel p 0)), hx₀.1⟩
  let c : Path x₁ x₁ :=
    { toFun := fun t => ⟨((γ t : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)) : Quot (OrientableRel p 0)),
        (γ t).2.1⟩
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp γ.continuous) _
      source' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0) =>
        (x : Quot (OrientableRel p 0))) γ.source)
      target' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0) =>
        (x : Quot (OrientableRel p 0))) γ.target) }
  have hc : ∀ t : I, c t = s78dg_cs_Psi_fun p hp (half, 4 * (p : ℝ) * (t : ℝ)) := by
    intro t
    obtain ⟨x, hx, hxq⟩ := hγv t
    obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp half (4 * (p : ℝ) * (t : ℝ))
    have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
    have hzx : z = x := by
      apply Subtype.ext
      rw [hz, hx, Complex.real_smul, Circle.coe_exp]
      have h1 : (4 * (p : ℝ) * (t : ℝ)) / (4 * p) = t := by field_simp
      rw [h1]
      congr 1
      congr 1
      push_cast; ring
    apply Subtype.ext
    rw [hz']
    show ((γ t : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)) : Quot (OrientableRel p 0)) = _
    rw [hxq, hzx]
  obtain ⟨r, hr⟩ := s78dg_cs_circle_conj p hp one hone half hhalf x₁ c hc β hβ
  let E : FundamentalGroup ↥(s78dg_cs_U p 0) x₁ ≃* FreeGroup (Fin p ⊕ Fin p) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath r).trans (e.trans θ.symm)
  let eU : fundamentalGroupFactor (s78dg_cs_U p 0) (s78dg_cs_V p 0) (b : Quot (OrientableRel p 0)) hx₀
      false ≃* PresentedGroup (∅ : Set (FreeGroup (Fin p ⊕ Fin p))) := E.trans T
  let γ' : FundamentalGroup ↑(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)
      (overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0) (b : Quot (OrientableRel p 0)) hx₀) :=
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹
  have hγ' : ∀ z, z ∈ Subgroup.zpowers γ' := fun z => by
    have := hγgen z
    rwa [← Subgroup.zpowers_inv] at this
  let w : FreeGroup (Fin p ⊕ Fin p) :=
    (List.ofFn fun i : Fin p =>
        FreeGroup.of (Sum.inl i : Fin p ⊕ Fin p) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod
  have hθw : θ w = (List.ofFn fun i : Fin p =>
      ((FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ : FreeGroup (Fin (2 * p)))⁻¹ *
        (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)⁻¹ * FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ *
          FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)).prod := by
    simp only [w, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp [hθa i, hθb i]
  have hw : PresentedGroup.mk (∅ : Set (FreeGroup (Fin p ⊕ Fin p))) w =
      eU (fundamentalGroupAmalgamation (s78dg_cs_U p 0) (s78dg_cs_V p 0)
        (b : Quot (OrientableRel p 0)) hx₀ false γ') := by
    have h2 : FundamentalGroup.mapOfEq (interToLeft (s78dg_cs_U p 0) (s78dg_cs_V p 0))
        (interToLeft_overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0)
          (b : Quot (OrientableRel p 0)) hx₀) (Path.Homotopic.Quotient.mk γ) =
        Path.Homotopic.Quotient.mk c :=
      s78dg_pi1_mapOfEq_mk (interToLeft _ _) _ _
        (interToLeft_overlapBasepoint _ _ _ hx₀) γ c (fun t => rfl)
    have h1 : fundamentalGroupAmalgamation (s78dg_cs_U p 0) (s78dg_cs_V p 0)
        (b : Quot (OrientableRel p 0)) hx₀ false γ' =
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ :=
      (map_inv (FundamentalGroup.mapOfEq (interToLeft (s78dg_cs_U p 0) (s78dg_cs_V p 0))
        (interToLeft_overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0)
          (b : Quot (OrientableRel p 0)) hx₀)) _).trans (congrArg _ h2)
    rw [h1]
    have h3 : eU (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ =
        T (θ.symm ((e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹)) := by
      show T (E _) = _
      rw [map_inv]
      show T ((θ.symm (e (FundamentalGroup.fundamentalGroupMulEquivOfPath r
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)))))⁻¹) = _
      rw [hr, map_inv, map_inv]
      exact (map_inv T _).symm
    rw [h3, hW, ← hT, ← hθw]
    simp
  -- `E` sends the overlap generator to the relator `w`
  have hEw : E (fundamentalGroupAmalgamation (s78dg_cs_U p 0) (s78dg_cs_V p 0)
      (b : Quot (OrientableRel p 0)) hx₀ false γ') = w := by
    apply T.injective
    rw [hT w]
    exact hw.symm
  -- van Kampen, kernel form
  obtain ⟨hs, hk⟩ := s78dg_svk_kernel (s78dg_cs_U p 0) (s78dg_cs_V p 0) (s78dg_cs_U_open p 0)
    (s78dg_cs_V_open p 0) (s78dg_cs_cover p 0) (b : Quot (OrientableRel p 0)) hx₀
  set ι := (fundamentalGroupLeftToAmbient (s78dg_cs_U p 0) (b : Quot (OrientableRel p 0)) hx₀.1).hom with hι
  let τ : FundamentalGroup ↥(s78dg_cs_U p 0) x₁ →* surfaceGroup p :=
    (PresentedGroup.mk _).comp E.toMonoidHom
  have hτs : Function.Surjective τ := (PresentedGroup.mk_surjective _).comp E.surjective
  have hnc : ∀ a g : FundamentalGroup ↥(s78dg_cs_U p 0) x₁,
      g ∈ Subgroup.normalClosure ({a} : Set _) ↔ E g ∈ Subgroup.normalClosure ({E a} : Set _) := by
    intro a g
    have hm := Subgroup.map_normalClosure ({a} : Set (FundamentalGroup ↥(s78dg_cs_U p 0) x₁))
      E.toMonoidHom E.surjective
    rw [Set.image_singleton] at hm
    constructor
    · intro hg
      have h1 := Subgroup.mem_map_of_mem E.toMonoidHom hg
      rw [hm] at h1
      exact h1
    · intro hg
      have hg' : E g ∈ (Subgroup.normalClosure ({a} : Set _)).map E.toMonoidHom := by
        rw [hm]
        exact hg
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hg'
      have hxg : x = g := E.injective hxe
      rw [← hxg]
      exact hx
  have hker : ι.ker = τ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hk g, s78dg_range_normalClosure _ γ' hγ', hnc, hEw]
    show _ ↔ PresentedGroup.mk _ (E g) = 1
    rw [PresentedGroup.mk_eq_one_iff]
  -- the tracked isomorphism at `b`
  let A := QuotientGroup.quotientKerEquivOfSurjective ι hs
  let B := QuotientGroup.quotientKerEquivOfSurjective τ hτs
  let Φb : FundamentalGroup (Quot (OrientableRel p 0)) (b : Quot (OrientableRel p 0)) ≃* surfaceGroup p :=
    A.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans B)
  have hΦb : ∀ g, Φb (ι g) = τ g := by
    intro g
    have h1 : A.symm (ι g) = QuotientGroup.mk g := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show B (QuotientGroup.quotientMulEquivOfEq hker (A.symm (ι g))) = τ g
    rw [h1]
    rfl
  -- `ι` is the map induced by the inclusion
  let incl : C(↥(s78dg_cs_U p 0), Quot (OrientableRel p 0)) := ⟨Subtype.val, continuous_subtype_val⟩
  have hιmap : ∀ u, ι u = FundamentalGroup.map incl x₁ u := by
    intro u
    induction u using Quotient.inductionOn with
    | h ℓ =>
      exact (s78dg_pi1_mapOfEq_mk (subsetToAmbient (s78dg_cs_U p 0)) _ _
        (leftBasepoint_toAmbient (s78dg_cs_U p 0) (b : Quot (OrientableRel p 0)) hx₀.1) ℓ
        (ℓ.map incl.continuous) (fun t => rfl)).trans rfl
  -- transport to the vertex
  let rQ := r.map incl.continuous
  have hpetal : ∀ (j : ℕ) (hj : j < 2 * p)
      (L : Path ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
        ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))),
      (∀ t : I, L t = ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) :
        ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) →
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath rQ).symm.trans Φb)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
        PresentedGroup.mk _ (θ.symm (FreeGroup.of ⟨j, hj⟩)) := by
    intro j hj L hL
    have hLU : ∀ t : I, L t ∈ s78dg_cs_U p 0 := fun t => by
      rw [hL t]
      exact (s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ))).2
    let LU : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)) :=
      { toFun := fun t => ⟨L t, hLU t⟩
        continuous_toFun := L.continuous.subtype_mk hLU
        source' := Subtype.ext L.source
        target' := Subtype.ext L.target }
    have heL := he j hj LU (fun t => hL t)
    set u := (FundamentalGroup.fundamentalGroupMulEquivOfPath r).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk LU)) with hu
    have hN : FundamentalGroup.fundamentalGroupMulEquivOfPath rQ (ι u) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L) := by
      rw [hιmap, ← s78dg_conj_nat incl r u, hu, MulEquiv.apply_symm_apply]
      rfl
    have h1 : (FundamentalGroup.fundamentalGroupMulEquivOfPath rQ).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = ι u := by
      rw [MulEquiv.symm_apply_eq, hN]
    show Φb ((FundamentalGroup.fundamentalGroupMulEquivOfPath rQ).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))) = _
    rw [h1, hΦb]
    show PresentedGroup.mk _ (θ.symm (e (FundamentalGroup.fundamentalGroupMulEquivOfPath r u))) = _
    rw [hu, MulEquiv.apply_symm_apply, heL]
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath rQ).symm.trans Φb, fun i L => ⟨fun hL => ?_, fun hL => ?_⟩⟩
  · rw [hpetal (2 * i) (by omega) L hL]
    have h2 : θ.symm (FreeGroup.of ⟨2 * (i : ℕ), by omega⟩) = (FreeGroup.of (Sum.inl i))⁻¹ := by
      rw [MulEquiv.symm_apply_eq, map_inv, hθa, inv_inv]
    rw [h2, map_inv]
    rfl
  · rw [hpetal (2 * i + 1) (by omega) L hL]
    have h2 : θ.symm (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩) = (FreeGroup.of (Sum.inr i))⁻¹ := by
      rw [MulEquiv.symm_apply_eq, map_inv, hθb, inv_inv]
    rw [h2, map_inv]
    rfl

end LiZhongQC
