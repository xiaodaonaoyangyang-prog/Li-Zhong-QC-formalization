import References.Common.RiemannSurface
import LiZhongQC.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Shared layer: the Riemann sphere

The Riemann sphere `ℙ¹` as a charted space over `ℂ`, for the books of the `References` program that treat meromorphic
functions as holomorphic maps into `ℙ¹` (Forster §1.5(c), 1.15; Farkas–Kra; Imayoshi–Taniguchi; Nag; Hubbard). It is an
`abbrev` of `LiZhongQC.ExtPlane = OnePoint ℂ`; the charted-space and manifold structures are `scoped` instances (open
scoped `References`), so files that do not open them are unaffected. The two charts are those of Forster 1.5(c): `chart₀ = id` on `ℂ`
and `chartInf z = 1/z`, `∞ ↦ 0`. The convention for Riemann surfaces is that of `References/Common/RiemannSurface.lean`.

* Shared notion (the Riemann sphere `ℙ¹`, with its two charts and the `ChartedSpace ℂ` structure) — `RiemannSphere`,
  `RiemannSphere.chart₀`, `RiemannSphere.chartInf`
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace References

/-- **The Riemann sphere `ℙ¹`** (Forster 1.5(c)): the one-point compactification of `ℂ`, as an abbreviation of
`LiZhongQC.ExtPlane`. -/
abbrev RiemannSphere : Type := LiZhongQC.ExtPlane

namespace RiemannSphere

/-- The finite points: the inclusion `ℂ → ℙ¹`. -/
def ofComplex (z : ℂ) : RiemannSphere := (OnePoint.some z : OnePoint ℂ)

/-- The point `∞` of `ℙ¹`. -/
def infty : RiemannSphere := (OnePoint.infty : OnePoint ℂ)

/-- The chart of `ℙ¹` at the finite points: the identity of `ℂ` (defined on `ℙ¹ ∖ {∞}`). -/
def chart₀ : OpenPartialHomeomorph RiemannSphere ℂ where
  toFun x := OnePoint.elim (x : OnePoint ℂ) 0 id
  invFun z := ofComplex z
  source := {x | x ≠ infty}
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun z _ => by
    show (OnePoint.some z : OnePoint ℂ) ≠ OnePoint.infty
    exact OnePoint.coe_ne_infty z
  left_inv' := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z => rfl
  right_inv' := fun z _ => rfl
  open_source := by
    show IsOpen {x : OnePoint ℂ | x ≠ OnePoint.infty}
    exact isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z =>
      show ContinuousAt (fun p : OnePoint ℂ => OnePoint.elim p 0 id) (OnePoint.some z)
      rw [OnePoint.continuousAt_coe]
      exact continuousAt_id
  continuousOn_invFun := OnePoint.continuous_coe.continuousOn

/-- The chart of `ℙ¹` at `∞`: `z ↦ 1/z` with `∞ ↦ 0` (defined on `ℙ¹ ∖ {0}`). -/
def chartInf : OpenPartialHomeomorph RiemannSphere ℂ where
  toFun x := OnePoint.elim (x : OnePoint ℂ) 0 fun z => z⁻¹
  invFun z := if z = 0 then infty else ofComplex z⁻¹
  source := {x | x ≠ ofComplex 0}
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := by
    intro z _
    by_cases hz : z = 0
    · simp only [hz, ite_true]
      show (OnePoint.infty : OnePoint ℂ) ≠ OnePoint.some 0
      exact (OnePoint.coe_ne_infty 0).symm
    · simp only [hz, ite_false]
      show (OnePoint.some z⁻¹ : OnePoint ℂ) ≠ OnePoint.some 0
      intro h
      exact inv_ne_zero hz (OnePoint.coe_injective h)
  left_inv' := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => simp [infty]
    | coe z =>
      have hz : z ≠ 0 := fun h => hx (by rw [h]; rfl)
      simp [hz, ofComplex]
  right_inv' := by
    intro z _
    by_cases hz : z = 0
    · simp [hz, infty]
    · simp [hz, ofComplex]
  open_source := by
    show IsOpen {x : OnePoint ℂ | x ≠ OnePoint.some 0}
    exact isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    induction x using OnePoint.rec with
    | infty =>
      show ContinuousAt (fun p : OnePoint ℂ => OnePoint.elim p 0 fun z : ℂ => z⁻¹) OnePoint.infty
      rw [OnePoint.continuousAt_infty']
      have h1 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded
      rw [← coclosedCompact_eq_cocompact] at h1
      exact h1
    | coe z =>
      have hz : z ≠ 0 := fun h => hx (by rw [h]; rfl)
      show ContinuousAt (fun p : OnePoint ℂ => OnePoint.elim p 0 fun z : ℂ => z⁻¹) (OnePoint.some z)
      rw [OnePoint.continuousAt_coe]
      exact continuousAt_inv₀ hz
  continuousOn_invFun := by
    refine continuous_iff_continuousAt.2 (fun z => ?_) |>.continuousOn
    show ContinuousAt (fun z : ℂ => if z = 0 then (OnePoint.infty : OnePoint ℂ) else OnePoint.some z⁻¹) z
    by_cases hz : z = 0
    · subst hz
      show Tendsto _ (𝓝 0) (𝓝 (if (0 : ℂ) = 0 then (OnePoint.infty : OnePoint ℂ) else OnePoint.some (0 : ℂ)⁻¹))
      rw [show (if (0 : ℂ) = 0 then (OnePoint.infty : OnePoint ℂ) else OnePoint.some (0 : ℂ)⁻¹) = OnePoint.infty by simp,
        ← nhdsNE_sup_pure (0 : ℂ)]
      refine Tendsto.sup ?_ (tendsto_pure_left.2 fun s hs => ?_)
      · have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
          rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
          simpa using tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ)
        have h2 := (OnePoint.tendsto_coe_infty (X := ℂ)).comp h1
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz'
        have hz'' : z ≠ 0 := hz'
        simp [hz'']
      · simpa using mem_of_mem_nhds hs
    · have : (fun z : ℂ => if z = 0 then (OnePoint.infty : OnePoint ℂ) else OnePoint.some z⁻¹) =ᶠ[𝓝 z]
          fun z => OnePoint.some z⁻¹ := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with y hy
        simp only [mem_compl_iff, mem_singleton_iff] at hy
        simp [hy]
      refine ContinuousAt.congr ?_ this.symm
      exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)

end RiemannSphere

open RiemannSphere

open scoped Classical in
/-- The Riemann sphere is a charted space over `ℂ` with the atlas `{chart₀, chartInf}`. -/
scoped instance : ChartedSpace ℂ RiemannSphere where
  atlas := {chart₀, chartInf}
  chartAt x := if x = infty then chartInf else chart₀
  mem_chart_source x := by
    by_cases hx : x = infty
    · simp only [hx, ite_true]
      show (OnePoint.infty : OnePoint ℂ) ≠ OnePoint.some 0
      exact (OnePoint.coe_ne_infty 0).symm
    · simp only [hx, ite_false]
      exact hx
  chart_mem_atlas x := by
    by_cases hx : x = infty
    · simp [hx]
    · simp [hx]

/-- The Riemann sphere is a complex manifold: the transition maps are `z ↦ z` and `z ↦ 1/z` on `ℂ*`. -/
scoped instance : IsManifold 𝓘(ℂ) ω RiemannSphere := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω RiemannSphere ?_
  intro e e' he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    Function.comp_id, Function.id_comp]
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := contDiffOn_inv ℂ
  have hchi : ∀ z : ℂ, (chartInf.symm z) = if z = 0 then infty else ofComplex z⁻¹ := fun z => rfl
  have hsrc0 : ∀ z ∈ (chartInf.symm ≫ₕ chart₀).source, z ≠ 0 := by
    intro z hz h
    have : chartInf.symm z ∈ chart₀.source := hz.2
    rw [hchi, h] at this
    exact this (by simp)
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · exact contDiffOn_id.congr fun z _ => rfl
  · have hsrc : ∀ z ∈ (chart₀.symm ≫ₕ chartInf).source, z ≠ 0 := by
      intro z hz h
      have : chart₀.symm z ∈ chartInf.source := hz.2
      exact this (by rw [h]; rfl)
    exact (hinv.mono hsrc).congr fun z _ => rfl
  · refine (hinv.mono (fun z hz => hsrc0 z hz)).congr fun z hz => ?_
    have hz0 := hsrc0 z hz
    show OnePoint.elim ((chartInf.symm z : RiemannSphere) : OnePoint ℂ) 0 id = z⁻¹
    rw [hchi]
    simp [hz0, ofComplex]
  · refine contDiffOn_id.congr fun z _ => ?_
    show OnePoint.elim ((chartInf.symm z : RiemannSphere) : OnePoint ℂ) 0 (fun z : ℂ => z⁻¹) = z
    rw [hchi]
    by_cases hz : z = 0
    · simp [hz, infty]
    · simp [hz, ofComplex]

end References

end
