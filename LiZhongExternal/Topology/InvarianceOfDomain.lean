/-
Unconditional invariance-of-domain adapters, 2026-10-14.
The imported harfe proof is MIT-licensed; the conditional proof is adapted from
Kai Lam's Apache-2.0-licensed PR36770. See the preserved vendor license files.
-/
import LiZhongExternal.Topology.BrouwerClosedBall
import LiZhongExternal.Topology.ConditionalInvarianceOfDomain

namespace LiZhongExternal.Topology

/-- Invariance of domain for finite-dimensional real inner product spaces, including dimension zero. -/
theorem invariance_of_domain_innerProduct {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) :
    IsOpen (f '' U) := by
  exact invariance_of_domain_open_map_of_brouwer
    (fun F hF => brouwer_closedBall F hF) f U hU hf_cont hf_inj

/-- Invariance of domain for any finite-dimensional real normed space. -/
theorem invariance_of_domain_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) :
    IsOpen (f '' U) := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let h := e.toHomeomorph
  let V := h.symm ⁻¹' U
  let g := fun x => h (f (h.symm x))
  have hV : IsOpen V := hU.preimage h.symm.continuous
  have hg_cont : ContinuousOn g V :=
    h.continuous.comp_continuousOn
      (hf_cont.comp h.symm.continuous.continuousOn (by intro x hx; exact hx))
  have hg_inj : Set.InjOn g V := by
    intro x hx y hy hxy
    apply h.symm.injective
    apply hf_inj hx hy
    exact h.injective hxy
  have hg_open : IsOpen (g '' V) :=
    invariance_of_domain_innerProduct g V hV hg_cont hg_inj
  have himage : f '' U = h ⁻¹' (g '' V) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨h y, ?_, ?_⟩
      · change h.symm (h y) ∈ U
        simpa using hy
      · change h (f (h.symm (h y))) = h (f y)
        rw [h.symm_apply_apply]
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨h.symm y, hy, h.injective hxy⟩
  rw [himage]
  exact hg_open.preimage h.continuous

end LiZhongExternal.Topology
