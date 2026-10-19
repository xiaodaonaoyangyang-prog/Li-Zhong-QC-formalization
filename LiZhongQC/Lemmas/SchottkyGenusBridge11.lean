import LiZhongQC.Lemmas.SchottkyGenusBridge10
import LiZhongQC.Lemmas.SchottkyNonOrientableSmall
import LiZhongQC.Lemmas.SchottkyCollarGeometry
import LiZhongQC.Lemmas.SchottkyCollarConnectivity

open Set Metric Topology unitInterval

universe u

namespace LiZhongQC

/-- The core is the complement of the open unit discs of the disc charts. -/
theorem s78dg_core_eq {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j) :
    s31dt_coreSet F = (⋃ j, v j '' ball (0 : ℂ) 1)ᶜ := by
  have hint : ∀ j, interior (F.D j) = v j '' ball (0 : ℂ) 1 := by
    intro j
    have hu : closedBall (0 : ℂ) 1 ⊆ (v j).source :=
      (closedBall_subset_closedBall (hR j).le).trans (hs j)
    obtain ⟨-, him, -⟩ := s31sd_disc_coordinate_sets (v j) hu (hD j)
    ext y
    constructor
    · intro hy
      have hyD : y ∈ F.D j := interior_subset hy
      obtain ⟨w, hw, rfl⟩ := (hD j).symm ▸ hyD
      have := (him (hu hw)).mp hy
      rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
      exact ⟨w, this, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ interior (closedBall (0 : ℂ) 1) := by
        rw [interior_closedBall (0 : ℂ) one_ne_zero]; exact hw
      exact (him (hu (interior_subset hw'))).mpr hw'
  show (⋃ j, interior (F.D j))ᶜ = _
  simp only [hint]

/-- The `j`-th boundary circle of the core, parametrised periodically by `t ↦ v_j(e^{2πit})`. -/
theorem s78dg_core_circle {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j))) (j : Fin m) :
    ∃ β : C(ℝ, s31dt_Core F), (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧
      range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} ∧
      ∀ t, (β t).val = v j (Circle.exp (2 * Real.pi * t) : ℂ) := by
  have hcore := s78dg_core_eq F v R hR hs hD
  have hu : closedBall (0 : ℂ) 1 ⊆ (v j).source :=
    (closedBall_subset_closedBall (hR j).le).trans (hs j)
  have hsets := s31sd_disc_coordinate_sets (v j) hu (hD j)
  have hball : ∀ i, ball (0 : ℂ) (R i) ⊆ (v i).source := fun i =>
    ball_subset_closedBall.trans (hs i)
  have hunit : ∀ t : ℝ, ‖(Circle.exp (2 * Real.pi * t) : ℂ)‖ = 1 := fun t => Circle.norm_coe _
  have hmem : ∀ t : ℝ, v j (Circle.exp (2 * Real.pi * t) : ℂ) ∈ s31dt_coreSet F := by
    intro t
    rw [hcore]
    intro hmem
    obtain ⟨i, w', hw', hww⟩ := mem_iUnion.mp hmem
    have hw1 : (Circle.exp (2 * Real.pi * t) : ℂ) ∈ ball (0 : ℂ) (R j) := by
      rw [mem_ball_zero_iff, hunit]; exact hR j
    by_cases hij : i = j
    · subst hij
      have h1 : w' = (Circle.exp (2 * Real.pi * t) : ℂ) :=
        (v i).injOn (hball i (ball_subset_ball (hR i).le hw')) (hball i hw1) hww
      rw [h1, mem_ball_zero_iff, hunit] at hw'
      exact lt_irrefl _ hw'
    · exact Set.disjoint_left.mp
        ((hdisj hij).mono (image_mono ball_subset_closedBall) (image_mono ball_subset_closedBall))
        ⟨w', ball_subset_ball (hR i).le hw', hww⟩ ⟨_, hw1, rfl⟩
  have hcexp : Continuous fun t : ℝ => (Circle.exp (2 * Real.pi * t) : ℂ) := by fun_prop
  let β : C(ℝ, s31dt_Core F) :=
    ⟨fun t => ⟨v j (Circle.exp (2 * Real.pi * t) : ℂ), hmem t⟩,
      Continuous.subtype_mk ((v j).continuousOn.comp_continuous hcexp
        (fun t => hu (mem_closedBall_zero_iff.mpr (hunit t).le))) hmem⟩
  have hinj : ∀ s t : ℝ, v j (Circle.exp (2 * Real.pi * s) : ℂ) = v j (Circle.exp (2 * Real.pi * t) : ℂ) →
      (Circle.exp (2 * Real.pi * s) : ℂ) = (Circle.exp (2 * Real.pi * t) : ℂ) := by
    intro s t h
    exact (v j).injOn (hu (mem_closedBall_zero_iff.mpr (hunit s).le))
      (hu (mem_closedBall_zero_iff.mpr (hunit t).le)) h
  refine ⟨β, fun t => ?_, ?_, ?_, fun t => rfl⟩
  · apply Subtype.ext
    show v j (Circle.exp (2 * Real.pi * (t + 1)) : ℂ) = v j (Circle.exp (2 * Real.pi * t) : ℂ)
    rw [mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one]
  · intro s hs' t ht hst
    have h1 := hinj s t (congrArg Subtype.val hst)
    rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_eq_exp_iff_exists_int] at h1
    obtain ⟨k, hk⟩ := h1
    have h2 : (s : ℂ) = t + k := by
      have h3 : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
        · exact Complex.I_ne_zero
      apply mul_right_cancel₀ h3
      push_cast at hk ⊢
      linear_combination hk
    have h4 : s = t + k := by exact_mod_cast h2
    have h5 : (k : ℝ) < 1 := by linarith [hs'.2, ht.1]
    have h6 : (-1 : ℝ) < k := by linarith [hs'.1, ht.2]
    have h7 : k = 0 := by
      have : k < 1 := by exact_mod_cast h5
      have : -1 < k := by exact_mod_cast h6
      omega
    rw [h4, h7]; simp
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      show v j (Circle.exp (2 * Real.pi * t) : ℂ) ∈ frontier (F.D j)
      apply (hsets.2.2 (hu (mem_closedBall_zero_iff.mpr (hunit t).le))).mpr
      rw [frontier_closedBall (0 : ℂ) one_ne_zero]
      exact mem_sphere_zero_iff_norm.mpr (hunit t)
    · intro hx
      have hxD : x.val ∈ F.D j := by
        have hc := frontier_subset_closure hx
        rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
      obtain ⟨w, hw, hwx⟩ := (hD j).symm ▸ hxD
      have hwf : w ∈ frontier (closedBall (0 : ℂ) 1) := (hsets.2.2 (hu hw)).mp (by rw [hwx]; exact hx)
      rw [frontier_closedBall (0 : ℂ) one_ne_zero] at hwf
      have hwn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hwf
      have hexp : (Circle.exp (Complex.arg w) : ℂ) = w := by
        rw [Circle.coe_exp]
        have := Complex.norm_mul_exp_arg_mul_I w
        rwa [hwn, Complex.ofReal_one, one_mul] at this
      refine ⟨Complex.arg w / (2 * Real.pi), Subtype.ext ?_⟩
      show v j (Circle.exp (2 * Real.pi * (Complex.arg w / (2 * Real.pi))) : ℂ) = x.val
      have h2 : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by
        field_simp
      rw [h2, hexp]
      exact hwx


/-- **(iii-a) The kernel of the boundary characters has dimension `2g`.**  -/
theorem s78dg_core_kernel_dim {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (x₀ : s31dt_Core F) :
    ∃ (c : Fin m → FundamentalGroup (s31dt_Core F) x₀)
      (L : (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) →ₗ[ℝ] (Fin m → ℝ)),
      (∀ ψ j, L ψ j = ψ (Additive.ofMul (c j))) ∧
      Module.finrank ℝ (LinearMap.ker L) = 2 * g ∧
      ∀ j, ∃ (β : C(ℝ, s31dt_Core F)) (ℓ : Path (β 0) (β 0)) (a : Path x₀ (β 0)),
        (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧
        range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} ∧
        (∀ t : unitInterval, ℓ t = β t) ∧
        c j = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)) := by
  obtain ⟨v, R, hv, hd⟩ := s31sd_disjoint_disc_coordinates F
  have hR := fun k => (hv k).1
  have hs := fun k => (hv k).2.1
  have hD := fun k => (hv k).2.2.1
  have hcore := s78dg_core_eq F v R hR hs hD
  haveI hCpc' : PathConnectedSpace (s31dt_Core F) := s31dt_core_pathConnected F v R hR hs hD hd
  have hCpc : IsPathConnected (s31dt_coreSet F) := isPathConnected_iff_pathConnectedSpace.mpr hCpc'
  choose β hβper hβinj hβrange hβval using fun j => s78dg_core_circle F v R hR hs hD hd j
  let z : Fin m → s31dt_Core F := fun j => β j 0
  have hz : ∀ j, ((z j : s31dt_Core F) : F.X.carrier) = v j 1 := by
    intro j
    show ((β j 0 : s31dt_Core F) : F.X.carrier) = _
    have h1 : (Circle.exp (2 * Real.pi * 0) : ℂ) = 1 := by
      rw [mul_zero, Circle.exp_zero]; rfl
    rw [hβval j 0, h1]
  let ℓ : ∀ j : Fin m, Path (z j) (z j) := fun j =>
    { toFun := fun t => β j t
      continuous_toFun := (β j).continuous.comp continuous_subtype_val
      source' := by
        show β j ((0 : I) : ℝ) = β j 0
        rw [Set.Icc.coe_zero]
      target' := by
        show β j ((1 : I) : ℝ) = β j 0
        rw [Set.Icc.coe_one]
        have := hβper j 0
        rwa [zero_add] at this }
  let a : ∀ j : Fin m, Path x₀ (z j) := fun j => PathConnectedSpace.somePath x₀ (z j)
  have hℓ : ∀ (j : Fin m) (t : I),
      ((ℓ j t : s31dt_Core F) : F.X.carrier) = v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) :=
    fun j t => hβval j t
  obtain ⟨hsurj, hker⟩ := s78dg_core_kernel_generic v R hR hs hd (s31dt_coreSet F) hcore hCpc x₀ z hz
    a ℓ hℓ
  let c : Fin m → FundamentalGroup (s31dt_Core F) x₀ := fun j =>
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (((a j).trans (ℓ j)).trans (a j).symm))
  let L : (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun ψ j => ψ (Additive.ofMul (c j))
      map_add' := fun ψ φ => rfl
      map_smul' := fun r ψ => rfl }
  refine ⟨c, L, fun ψ j => rfl, ?_, fun j => ⟨β j, ℓ j, a j, hβper j, hβinj j, hβrange j,
    fun t => rfl, rfl⟩⟩
  let valC : C(s31dt_Core F, F.X.carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  let P : FundamentalGroup (s31dt_Core F) x₀ →* FundamentalGroup F.X.carrier x₀.val :=
    FundamentalGroup.map valC x₀
  have hPc : ∀ j, P (c j) = 1 := fun j =>
    (hker (c j)).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
  let Θ : (Additive (FundamentalGroup F.X.carrier x₀.val) →+ ℝ) →ₗ[ℝ]
      (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) :=
    { toFun := fun ψ => ψ.comp P.toAdditive
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΘinj : Function.Injective Θ := by
    intro ψ φ h
    apply AddMonoidHom.ext
    intro y
    obtain ⟨x, hx⟩ := hsurj y.toMul
    have h1 := DFunLike.congr_fun h (Additive.ofMul x)
    have e : P.toAdditive (Additive.ofMul x) = y := by
      show Additive.ofMul (P x) = y
      rw [show P x = y.toMul from hx]
      rfl
    have h2 : ψ (P.toAdditive (Additive.ofMul x)) = φ (P.toAdditive (Additive.ofMul x)) := h1
    rw [e] at h2
    exact h2
  have hrange : LinearMap.range Θ = LinearMap.ker L := by
    ext χ
    constructor
    · rintro ⟨ψ, rfl⟩
      rw [LinearMap.mem_ker]
      funext j
      show ψ (P.toAdditive (Additive.ofMul (c j))) = 0
      have : P.toAdditive (Additive.ofMul (c j)) = 0 := by
        show Additive.ofMul (P (c j)) = 0
        rw [hPc j]
        rfl
      rw [this, map_zero]
    · intro hχ
      rw [LinearMap.mem_ker] at hχ
      have hχj : ∀ j, χ (Additive.ofMul (c j)) = 0 := fun j => congrFun hχ j
      let χ' : FundamentalGroup (s31dt_Core F) x₀ →* Multiplicative ℝ :=
        AddMonoidHom.toMultiplicativeRight χ
      have hle : P.ker ≤ χ'.ker := by
        intro x hx
        have hx' := (hker x).1 hx
        have hN : Subgroup.normalClosure {t : FundamentalGroup (s31dt_Core F) x₀ | ∃ j : Fin m,
            t = c j} ≤ χ'.ker := by
          haveI := MonoidHom.normal_ker χ'
          refine Subgroup.normalClosure_le_normal ?_
          rintro t ⟨j, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker]
          show Multiplicative.ofAdd (χ (Additive.ofMul (c j))) = 1
          rw [hχj j]
          rfl
        exact hN hx'
      let ψ' : FundamentalGroup F.X.carrier x₀.val →* Multiplicative ℝ :=
        MonoidHom.liftOfSurjective P hsurj ⟨χ', hle⟩
      let ψ : Additive (FundamentalGroup F.X.carrier x₀.val) →+ ℝ :=
        { toFun := fun y => Multiplicative.toAdd (ψ' y.toMul)
          map_zero' := by
            show Multiplicative.toAdd (ψ' 1) = 0
            rw [map_one]
            rfl
          map_add' := fun y w => by
            show Multiplicative.toAdd (ψ' (y.toMul * w.toMul)) =
              Multiplicative.toAdd (ψ' y.toMul) + Multiplicative.toAdd (ψ' w.toMul)
            rw [map_mul]
            rfl }
      refine ⟨ψ, ?_⟩
      apply AddMonoidHom.ext
      intro y
      show Multiplicative.toAdd (ψ' (P y.toMul)) = χ y
      exact MonoidHom.liftOfRightInverse_comp_apply P (Function.surjInv hsurj)
        (Function.rightInverse_surjInv hsurj) ⟨χ', hle⟩ y.toMul
  let e1 : (Additive (FundamentalGroup F.X.carrier x₀.val) →+ ℝ) ≃ₗ[ℝ] LinearMap.ker L :=
    (LinearEquiv.ofInjective Θ hΘinj).trans (LinearEquiv.ofEq _ _ hrange)
  rw [← e1.finrank_eq, s78no_finrank_hom_eq_two_genus F.X.carrier x₀.val,
    k22rr_genus_eq F.genus]

end LiZhongQC
