import LiZhongQC.Lemmas.SchottkyGenusBridge5
import LiZhongQC.Lemmas.SchottkyGenusBridge7
import LiZhongQC.Lemmas.SchottkyClosedSurface10
import LiZhongQC.Lemmas.SchottkyClosedSurface11

open Set Metric Topology unitInterval DifferentialGeometry.Topology.VanKampen

universe u

namespace LiZhongQC

/-- **One disc attached, kernel form, in a disc chart.**  `W₁ = W₀ ∪ v(B(0,R))`, the overlap being the
annulus `v(1/R < |z| < R)`.  Then `π₁(W₀, v 1) → π₁(W₁, v 1)` is onto, with kernel the normal
closure of the class of the loop `t ↦ v(e^{2πit})`. -/
theorem s78dg_chain_step {X : Type u} [TopologicalSpace X]
    (v : OpenPartialHomeomorph ℂ X) (R : ℝ) (hR : 1 < R)
    (hs : closedBall (0 : ℂ) R ⊆ v.source) (W0 W1 : Set X) (hW0 : IsOpen W0)
    (hsub : W0 ⊆ W1) (hunion : W1 = W0 ∪ v '' ball (0 : ℂ) R)
    (hinter : W0 ∩ v '' ball (0 : ℂ) R = v '' {z : ℂ | 1 / R < ‖z‖ ∧ ‖z‖ < R})
    (hpc : PathConnectedSpace ↥W0) (y : ↥W0) (hy : (y : X) = v 1) :
    ∃ ℓ : Path y y, (∀ t : I, ((ℓ t : ↥W0) : X) = v (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) ∧
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(↥W0, ↥W1)) y) ∧
      ∀ δ, FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(↥W0, ↥W1)) y δ = 1 ↔
        δ ∈ Subgroup.normalClosure
          ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} :
            Set (FundamentalGroup ↥W0 y)) := by
  classical
  have hball : ball (0 : ℂ) R ⊆ v.source := ball_subset_closedBall.trans hs
  let Vj : Set X := v '' ball (0 : ℂ) R
  have hVo : IsOpen Vj := v.isOpen_image_of_subset_source isOpen_ball hball
  have hVsub : Vj ⊆ W1 := by rw [hunion]; exact subset_union_right
  let Sset : Set ℂ := {z : ℂ | 1 / R < ‖z‖ ∧ ‖z‖ < R}
  have hR0 : 0 < R := by linarith
  have hSball : Sset ⊆ ball (0 : ℂ) R := fun z hz => mem_ball_zero_iff.mpr hz.2
  let U : Set ↥W1 := Subtype.val ⁻¹' W0
  let V : Set ↥W1 := Subtype.val ⁻¹' Vj
  have hU : IsOpen U := hW0.preimage continuous_subtype_val
  have hV : IsOpen V := hVo.preimage continuous_subtype_val
  have hcover : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    exact (Set.ext_iff.1 hunion x.1).1 x.2
  have hexp1 : ∀ t : ℝ, (Circle.exp (2 * Real.pi * t) : ℂ) ∈ Sset := by
    intro t
    have hn : ‖(Circle.exp (2 * Real.pi * t) : ℂ)‖ = 1 := Circle.norm_coe _
    refine ⟨?_, ?_⟩
    · rw [hn]; exact (div_lt_one hR0).mpr hR
    · rw [hn]; exact hR
  have h1S : (1 : ℂ) ∈ Sset := by
    have := hexp1 0
    simpa using this
  have hy1 : (y : X) ∈ Vj := ⟨1, mem_ball_zero_iff.mpr (by simpa using hR), hy.symm⟩
  let x₀ : ↥W1 := ⟨y.1, hsub y.2⟩
  have hx₀ : x₀ ∈ U ∩ V := ⟨y.2, hy1⟩
  obtain ⟨eU, heU⟩ := s78dg_sub_homeo W0 hsub
  obtain ⟨eV, heV⟩ := s78dg_sub_homeo Vj hVsub
  obtain ⟨eUV, heUV⟩ := s78dg_sub_homeo (W0 ∩ Vj) (inter_subset_left.trans hsub)
  haveI hUpc : PathConnectedSpace ↥U := eU.symm.pathConnectedSpace
  let eVb : ↥V ≃ₜ ↥(ball (0 : ℂ) R) :=
    eV.trans (v.homeomorphOfImageSubsetSource hball rfl).symm
  haveI hballc : ContractibleSpace ↥(ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, mem_ball_self hR0⟩
  haveI hVct : ContractibleSpace ↥V := eVb.contractibleSpace_iff.mpr hballc
  haveI hVsc : SimplyConnectedSpace ↥V := inferInstance
  haveI hVpc : PathConnectedSpace ↥V := by
    haveI : PathConnectedSpace ↥(ball (0 : ℂ) R) :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_ball (0 : ℂ) R).isPathConnected ⟨0, mem_ball_self hR0⟩)
    exact eVb.symm.pathConnectedSpace
  obtain ⟨Φann, hΦann⟩ := s78dg_annulus_homeo R hR
  let eS : ↥Sset ≃ₜ ↥(v '' Sset) := v.homeomorphOfImageSubsetSource (hSball.trans hball) rfl
  let ΦUV : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} ≃ₜ ↥(U ∩ V) :=
    ((Φann.trans eS).trans (Homeomorph.setCongr hinter.symm)).trans eUV.symm
  haveI hPpc := s78dg_punctured_pc
  haveI hUVpc : PathConnectedSpace ↥(U ∩ V) := ΦUV.pathConnectedSpace
  have hΦval : ∀ w, ((((ΦUV w : ↥(U ∩ V)) : ↥W1)) : X) = v ((Φann w : ℂ)) := by
    intro w
    exact heUV ((Homeomorph.setCongr hinter.symm) (eS (Φann w)))
  obtain ⟨b, γ, ⟨w₀, hw₀, hb⟩, hγt, hgen⟩ := s78dg_punctured_gen ΦUV
  have hΦ1 : ((Φann w₀ : ↥Sset) : ℂ) = 1 := by
    have hn : ‖(w₀ : ℂ)‖ = 1 / 2 := by
      rw [hw₀]
      simp
    rw [(hΦann w₀).2, hn, hw₀]
    have : (R : ℝ) ^ (2 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
    rw [this]
    simp
  have hb' : b = overlapBasepoint U V x₀ hx₀ := by
    rw [hb]
    apply Subtype.ext
    apply Subtype.ext
    rw [hΦval, hΦ1]
    exact hy.symm
  subst hb'
  have hmemW0 : ∀ t : ℝ, v (Circle.exp (2 * Real.pi * t) : ℂ) ∈ W0 := by
    intro t
    have h : v (Circle.exp (2 * Real.pi * t) : ℂ) ∈ v '' Sset := mem_image_of_mem _ (hexp1 t)
    rw [← hinter] at h
    exact h.1
  have hsrc : ∀ t : ℝ, (Circle.exp (2 * Real.pi * t) : ℂ) ∈ v.source := by
    intro t
    exact hs (mem_closedBall_zero_iff.mpr (by rw [Circle.norm_coe _]; exact hR.le))
  have hc0 : (Circle.exp (2 * Real.pi * ((0 : I) : ℝ)) : ℂ) = 1 := by
    rw [Set.Icc.coe_zero, mul_zero, Circle.exp_zero]; rfl
  have hc1 : (Circle.exp (2 * Real.pi * ((1 : I) : ℝ)) : ℂ) = 1 := by
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; rfl
  let ℓ : Path y y :=
    { toFun := fun t => ⟨v (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ), hmemW0 t⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact v.continuousOn.comp_continuous (by fun_prop) (fun t => hsrc t)
      source' := Subtype.ext (by show v _ = y.1; rw [hc0, hy])
      target' := Subtype.ext (by show v _ = y.1; rw [hc1, hy]) }
  have hA : eU.symm y = leftBasepoint U x₀ hx₀.1 := Subtype.ext (Subtype.ext (heU y))
  have hℓ : ∀ t, ((eU.symm (ℓ t) : ↥U) : ↥W1) = (((γ t : ↥(U ∩ V))) : ↥W1) := by
    intro t
    apply Subtype.ext
    obtain ⟨w, hw, hγw⟩ := hγt t
    rw [hγw, hΦval]
    have h1 := heU (ℓ t)
    change (((eU.symm (ℓ t) : ↥U) : ↥W1) : X) = _
    rw [h1]
    change v (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) = _
    congr 1
    rw [(hΦann w).2]
    have hn : ‖(w : ℂ)‖ = 1 / 2 := by
      rw [hw, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
      norm_num
    rw [hn, hw]
    have : (R : ℝ) ^ (2 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
    rw [this, smul_smul]
    have h2 : (1 : ℝ) / (1 / 2) * (1 / 2) = 1 := by norm_num
    rw [h2, one_smul]
  obtain ⟨hs1, hk1⟩ := s78dg_svk_kernel_gen U V hU hV hcover x₀ hx₀ (A := ↥W0) eU.symm y hA γ
    hgen ℓ hℓ
  refine ⟨ℓ, fun t => rfl, ?_⟩
  let ι : C(↥W0, ↥W1) := ⟨Set.inclusion hsub, continuous_inclusion hsub⟩
  have hg : (⟨fun a => ((eU.symm a : ↥U) : ↥W1),
      continuous_subtype_val.comp eU.symm.continuous⟩ : C(↥W0, ↥W1)) = ι := by
    ext a
    exact heU a
  have key : ∀ (g' : C(↥W0, ↥W1)) (hg' : g' = ι) (h : g' y = x₀),
      (Function.Surjective (FundamentalGroup.mapOfEq g' h) ∧ ∀ δ,
        FundamentalGroup.mapOfEq g' h δ = 1 ↔ δ ∈ Subgroup.normalClosure
          ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} :
            Set (FundamentalGroup ↥W0 y))) →
      (Function.Surjective (FundamentalGroup.map ι y) ∧ ∀ δ,
        FundamentalGroup.map ι y δ = 1 ↔ δ ∈ Subgroup.normalClosure
          ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} :
            Set (FundamentalGroup ↥W0 y))) := by
    intro g' hg' h H
    subst hg'
    have hm : (FundamentalGroup.mapOfEq ι h : FundamentalGroup ↥W0 y →* _) =
        FundamentalGroup.map ι y := by
      ext p
      rw [FundamentalGroup.mapOfEq_apply]
      exact Path.Homotopic.Quotient.cast_rfl_rfl _
    rw [hm] at H
    exact H
  exact key _ hg (congrArg Subtype.val hA) ⟨hs1, hk1⟩

theorem s78dg_trans_symm_trans {X : Type u} [TopologicalSpace X] {x y w : X}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient x w) :
    a.trans (a.symm.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

/-- Conjugation by a path, on classes of loops. -/
theorem s78dg_conj_mk {Z : Type u} [TopologicalSpace Z] {x y : Z} (p : Path x y) (c : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.symm.trans (c.trans p))) := by
  apply s78dg_pi1_conj p c _
  apply Path.Homotopic.Quotient.eq.mp
  show (Path.Homotopic.Quotient.mk p).trans ((Path.Homotopic.Quotient.mk p).symm.trans
    ((Path.Homotopic.Quotient.mk c).trans (Path.Homotopic.Quotient.mk p))) =
    (Path.Homotopic.Quotient.mk c).trans (Path.Homotopic.Quotient.mk p)
  exact s78dg_trans_symm_trans _ _

/-- Base change commutes with induced maps. -/
theorem s78dg_conj_nat {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z'] (f : C(Z, Z'))
    {x y : Z} (p : Path x y) (c : FundamentalGroup Z x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath p c) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x c) := by
  induction c using Quotient.inductionOn with
  | h c0 =>
    have h1 := s78dg_conj_mk p c0
    have h2 : FundamentalGroup.map f x (Path.Homotopic.Quotient.mk c0) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (c0.map f.continuous)) := rfl
    have h3 := s78dg_conj_mk (p.map f.continuous) (c0.map f.continuous)
    erw [h1, h2, h3]
    show FundamentalGroup.map f y (Path.Homotopic.Quotient.mk _) = _
    show Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    congr 1
    simp [Path.map_trans, Path.map_symm]

/-- **Base change for the kernel statement.** -/
theorem s78dg_bc_kernel {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z'] (f : C(Z, Z'))
    {x y : Z} (p : Path x y) (ℓ : Path y y)
    (hsurj : Function.Surjective (FundamentalGroup.map f y))
    (hker : ∀ δ, FundamentalGroup.map f y δ = 1 ↔ δ ∈ Subgroup.normalClosure
      ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} : Set (FundamentalGroup Z y))) :
    Function.Surjective (FundamentalGroup.map f x) ∧ ∀ δ, FundamentalGroup.map f x δ = 1 ↔
      δ ∈ Subgroup.normalClosure
        ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((p.trans ℓ).trans p.symm))} :
          Set (FundamentalGroup Z x)) := by
  let Φ := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let Ψ := FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
  have hnat := s78dg_conj_nat f p
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨d, hd⟩ := hsurj (Ψ e)
    refine ⟨Φ.symm d, ?_⟩
    apply Ψ.injective
    rw [← hnat, Φ.apply_symm_apply, hd]
  · intro δ
    set c : FundamentalGroup Z x := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((p.trans ℓ).trans p.symm)) with hc
    have hΦ : Φ c = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ) := by
      have := s78dg_conj_mk p ((p.trans ℓ).trans p.symm)
      refine this.trans ?_
      congr 1
      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
        Path.Homotopic.Quotient.trans_refl, s78dg_gen_cancel2]
    have hN : Subgroup.normalClosure
        ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} : Set (FundamentalGroup Z y)) =
        (Subgroup.normalClosure ({c} : Set (FundamentalGroup Z x))).map Φ.toMonoidHom := by
      rw [Subgroup.map_normalClosure _ _ Φ.surjective, Set.image_singleton]
      congr 2
      exact hΦ.symm
    have h1 : FundamentalGroup.map f x δ = 1 ↔ FundamentalGroup.map f y (Φ δ) = 1 := by
      rw [hnat, ← map_one Ψ, Ψ.injective.eq_iff]
    rw [h1, hker, hN]
    exact Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective

end LiZhongQC
