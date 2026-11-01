import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.Contractible

open unitInterval

namespace LiZhongQC

/-- Integers map to zero in the circle `ℝ / ℤ`. -/
theorem s78dg_circ_int_coe (m : ℤ) : (((m : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

/-- A real number mapping to zero in `ℝ / ℤ` is an integer. -/
theorem s78dg_circ_fiber (r : ℝ) (h : (r : AddCircle (1 : ℝ)) = 0) : ∃ m : ℤ, r = (m : ℝ) := by
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by simpa using hm.symm⟩

/-- Lifts of a path through `ℝ → ℝ / ℤ` starting at points differing by an integer differ by it. -/
theorem s78dg_circ_lift_shift (γ : C(I, AddCircle (1 : ℝ))) (e e' : ℝ) (m : ℤ) (hm : e' = e + m)
    (h : γ 0 = (e : AddCircle (1 : ℝ))) (h' : γ 0 = (e' : AddCircle (1 : ℝ))) (t : I) :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath γ e' h' t =
      (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath γ e h t + m := by
  subst hm
  have cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let L := cov.liftPath γ e h
  let Γ : C(I, ℝ) := ⟨fun t => L t + m, L.continuous.add continuous_const⟩
  have hΓ : Γ = cov.liftPath γ (e + m) h' := by
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · funext t
      have h1 := congr_fun (cov.liftPath_lifts γ e h) t
      simp only [Function.comp_apply] at h1 ⊢
      change ((L t + m : ℝ) : AddCircle (1 : ℝ)) = γ t
      rw [AddCircle.coe_add, s78dg_circ_int_coe, add_zero]
      exact h1
    · change L 0 + m = e + m
      rw [cov.liftPath_zero]
  exact (congr_fun (congr_arg DFunLike.coe hΓ) t).symm

/-- **S0 (with generator).**  The fundamental group of the circle `ℝ / ℤ` is `ℤ`, and the loop `t ↦ t`
corresponds to `1`. -/
theorem s78dg_circle_core :
    ∃ φ : FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ,
      ∃ γ : Path (0 : AddCircle (1 : ℝ)) 0,
        (∀ t : I, γ t = ((t : ℝ) : AddCircle (1 : ℝ))) ∧
          φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = Multiplicative.ofAdd 1 := by
  have cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let e₀ : ((fun r : ℝ => (r : AddCircle (1 : ℝ))) ⁻¹' {0}) := ⟨0, by simp⟩
  let N : FundamentalGroup (AddCircle (1 : ℝ)) 0 → ℝ := fun γ => (cov.monodromy γ.asHom e₀).1
  have hN : ∀ γ, ∃ m : ℤ, N γ = m := fun γ =>
    s78dg_circ_fiber _ (Set.mem_singleton_iff.mp (cov.monodromy γ.asHom e₀).2)
  have hmono : ∀ (γ : Path (0 : AddCircle (1 : ℝ)) 0)
      (e : ((fun r : ℝ => (r : AddCircle (1 : ℝ))) ⁻¹' {0})),
      (cov.monodromy (Path.Homotopic.Quotient.mk γ) e).1 =
        cov.liftPath γ e (γ.source.trans e.2.symm) 1 := fun γ e => rfl
  have hequiv : ∀ (γ : FundamentalGroup (AddCircle (1 : ℝ)) 0) (m : ℤ),
      (cov.monodromy γ.asHom ⟨(m : ℝ), s78dg_circ_int_coe m⟩).1 = N γ + m := by
    intro γ m
    obtain ⟨γ⟩ := γ
    induction γ using Quotient.inductionOn with
    | h γ =>
      have h1 := hmono γ ⟨(m : ℝ), s78dg_circ_int_coe m⟩
      have h2 := hmono γ e₀
      have h3 := s78dg_circ_lift_shift γ 0 (m : ℝ) m (by simp) (γ.source.trans e₀.2.symm)
        (γ.source.trans (s78dg_circ_int_coe m).symm) 1
      exact h1.trans (h3.trans (by rw [← h2]; rfl))
  have hone : N 1 = 0 := by
    change (cov.monodromy (Path.Homotopic.Quotient.refl (0 : AddCircle (1 : ℝ))) e₀).1 = 0
    rw [cov.monodromy_refl]
    rfl
  have hmul : ∀ γ₁ γ₂, N (γ₁ * γ₂) = N γ₁ + N γ₂ := by
    intro γ₁ γ₂
    obtain ⟨m, hm⟩ := hN γ₂
    have h1 : cov.monodromy (γ₁ * γ₂).asHom e₀ = cov.monodromy γ₁.asHom (cov.monodromy γ₂.asHom e₀) := by
      rw [FundamentalGroup.mul_def]
      exact cov.monodromy_trans_apply γ₂.asHom γ₁.asHom e₀
    have h2 : cov.monodromy γ₂.asHom e₀ = ⟨(m : ℝ), s78dg_circ_int_coe m⟩ := Subtype.ext hm
    change (cov.monodromy (γ₁ * γ₂).asHom e₀).1 = _ + _
    rw [h1, h2, hequiv γ₁ m, hm]
  let φ : FundamentalGroup (AddCircle (1 : ℝ)) 0 →* Multiplicative ℤ :=
    MonoidHom.mk' (fun γ => Multiplicative.ofAdd ⌊N γ⌋) (fun γ₁ γ₂ => by
      obtain ⟨m₁, h₁⟩ := hN γ₁
      obtain ⟨m₂, h₂⟩ := hN γ₂
      rw [hmul, h₁, h₂, ← Int.cast_add]
      simp [Int.floor_intCast])
  have hφ : ∀ γ, ((Multiplicative.toAdd (φ γ) : ℤ) : ℝ) = N γ := by
    intro γ
    obtain ⟨m, hm⟩ := hN γ
    change ((⌊N γ⌋ : ℤ) : ℝ) = N γ
    rw [hm, Int.floor_intCast]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hN0 : N γ = 0 := by
      rw [← hφ γ, hγ]; simp
    obtain ⟨γ⟩ := γ
    induction γ using Quotient.inductionOn with
    | h γ =>
      have h1 : cov.liftPath γ e₀ (γ.source.trans e₀.2.symm) 1 = 0 := (hmono γ e₀).symm.trans hN0
      have hΓ0 : cov.liftPath γ e₀ (γ.source.trans e₀.2.symm) 0 = 0 := cov.liftPath_zero ..
      let Γp : Path (0 : ℝ) 0 := ⟨cov.liftPath γ e₀ (γ.source.trans e₀.2.symm), hΓ0, h1⟩
      have hhom : Path.Homotopic Γp (Path.refl 0) := SimplyConnectedSpace.paths_homotopic _ _
      have h4 : (cov.liftPath γ e₀ (γ.source.trans e₀.2.symm)).HomotopicRel
          (ContinuousMap.const I (0 : ℝ)) {0, 1} := hhom
      have h5 := (cov.homotopicRel_iff_comp (f₀ := cov.liftPath γ e₀ (γ.source.trans e₀.2.symm))
        (f₁ := ContinuousMap.const I (0 : ℝ)) (S := {0, 1}) ⟨0, Or.inl rfl, by simpa using hΓ0⟩).mp h4
      have hc : ContinuousMap.comp ⟨(fun r : ℝ => (r : AddCircle (1 : ℝ))), cov.continuous⟩
          (cov.liftPath γ e₀ (γ.source.trans e₀.2.symm)) = (γ : C(I, AddCircle (1 : ℝ))) :=
        ContinuousMap.ext fun t => congr_fun (cov.liftPath_lifts γ e₀ (γ.source.trans e₀.2.symm)) t
      have hc2 : ContinuousMap.comp ⟨(fun r : ℝ => (r : AddCircle (1 : ℝ))), cov.continuous⟩
          (ContinuousMap.const I (0 : ℝ)) = ((Path.refl (0 : AddCircle (1 : ℝ))) :
            C(I, AddCircle (1 : ℝ))) := by
        ext t; simp
      rw [hc, hc2] at h5
      apply CategoryTheory.End.ext
      change Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl 0)
      rw [Path.Homotopic.Quotient.eq]
      exact h5
  have hsurj' : ∀ z : Multiplicative ℤ, ∃ γ₀ : Path (0 : AddCircle (1 : ℝ)) 0,
      (∀ t : I, γ₀ t = (((Multiplicative.toAdd z : ℤ) : ℝ) * (t : ℝ) : ℝ)) ∧
        φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀)) = z := by
    intro z
    let k : ℤ := Multiplicative.toAdd z
    let ρ : C(I, ℝ) := ⟨fun t => (k : ℝ) * (t : ℝ), by fun_prop⟩
    let γ₀ : Path (0 : AddCircle (1 : ℝ)) 0 :=
      ⟨ContinuousMap.comp ⟨(fun r : ℝ => (r : AddCircle (1 : ℝ))), cov.continuous⟩ ρ,
        by simp [ρ], by simp [ρ]⟩
    have hρ : ρ = cov.liftPath γ₀ e₀ (γ₀.source.trans e₀.2.symm) := by
      rw [cov.eq_liftPath_iff']
      exact ⟨rfl, by simp [ρ, e₀]⟩
    have hNk : N (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀)) = k := by
      have := hmono γ₀ e₀
      change (cov.monodromy (Path.Homotopic.Quotient.mk γ₀) e₀).1 = _ at this
      change (cov.monodromy (Path.Homotopic.Quotient.mk γ₀) e₀).1 = _
      rw [this, ← hρ]
      simp [ρ]
    refine ⟨γ₀, fun t => rfl, ?_⟩
    change Multiplicative.ofAdd ⌊N (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))⌋ = z
    rw [hNk, Int.floor_intCast]
    rfl
  have hsurj : Function.Surjective φ := fun z => by
    obtain ⟨γ₀, _, h⟩ := hsurj' z
    exact ⟨_, h⟩
  obtain ⟨γ₁, hγ₁, hφ₁⟩ := hsurj' (Multiplicative.ofAdd 1)
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, γ₁, fun t => ?_, hφ₁⟩
  rw [hγ₁ t]
  simp

/-- **S0.** The fundamental group of the circle `ℝ / ℤ` is `ℤ`. -/
theorem s78dg_circle_fundamentalGroup :
    Nonempty (FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ) := by
  obtain ⟨φ, _⟩ := s78dg_circle_core
  exact ⟨φ⟩

/-- The loop `t ↦ t` generates the fundamental group of the circle. -/
theorem s78dg_circle_generator :
    ∃ γ : Path (0 : AddCircle (1 : ℝ)) 0, (∀ t : I, γ t = ((t : ℝ) : AddCircle (1 : ℝ))) ∧
      ∀ z : FundamentalGroup (AddCircle (1 : ℝ)) 0,
        z ∈ Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  obtain ⟨φ, γ, hγ, hφ⟩ := s78dg_circle_core
  refine ⟨γ, hγ, fun z => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, φ z = Multiplicative.ofAdd m := ⟨Multiplicative.toAdd (φ z), rfl⟩
  refine ⟨m, ?_⟩
  apply φ.injective
  rw [map_zpow, hφ, hm]
  apply Multiplicative.toAdd.injective
  simp

end LiZhongQC
