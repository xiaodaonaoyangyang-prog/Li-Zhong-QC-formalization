import Mathlib
import Jacobians.Surface.ContMDiffOmegaAnalytic

/-! Hurwitz surface identity bridge, reusing the installed chart-analyticity theorem. -/

open Set Filter Metric
open scoped Manifold Topology ContDiff

namespace LiZhongQC

/-- The locus where two complex-analytic manifold maps have the same germ is closed.
At a closure point continuity gives equal values, so one target chart represents both
maps. The scalar difference is analytic on a small connected ball; an interior germ
equality witness forces that difference to vanish on the whole ball. No continuation
or clopenness hypothesis is assumed. -/
theorem h84s_isClosed_germEq
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y]
    {f g : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    IsClosed {x : X | f =ᶠ[𝓝 x] g} := by
  classical
  let S : Set X := {x | f =ᶠ[𝓝 x] g}
  change IsClosed S
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm ?_ subset_closure
  intro x hx
  have hSsub : S ⊆ {y : X | f y = g y} := by
    intro y hy
    exact hy.self_of_nhds
  have heqClosed : IsClosed {y : X | f y = g y} :=
    isClosed_eq hf.continuous hg.continuous
  have hfxgx : f x = g x :=
    heqClosed.closure_subset (closure_mono hSsub hx)
  let c := chartAt ℂ x
  let d := chartAt ℂ (f x)
  let F : ℂ → ℂ := d ∘ f ∘ c.symm
  let G : ℂ → ℂ := d ∘ g ∘ c.symm
  let D : ℂ → ℂ := fun z => F z - G z
  have hFA : AnalyticAt ℂ F (c x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hf x
  have hGA : AnalyticAt ℂ G (c x) := by
    have h :=
      Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hg x
    rw [← hfxgx] at h
    exact h
  have hDA : AnalyticAt ℂ D (c x) := hFA.sub hGA
  obtain ⟨r, hr, hDon⟩ := hDA.exists_ball_analyticOnNhd
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hfx : f x ∈ d.source := mem_chart_source ℂ (f x)
  have hgx : g x ∈ d.source := by rw [← hfxgx]; exact hfx
  let V : Set X :=
    (c.source ∩ c ⁻¹' Metric.ball (c x) r) ∩
      (f ⁻¹' d.source ∩ g ⁻¹' d.source)
  have hpre : IsOpen (c.source ∩ c ⁻¹' Metric.ball (c x) r) :=
    c.continuousOn_toFun.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hVopen : IsOpen V :=
    hpre.inter ((d.open_source.preimage hf.continuous).inter
      (d.open_source.preimage hg.continuous))
  have hxV : x ∈ V := ⟨⟨hcx, Metric.mem_ball_self hr⟩, hfx, hgx⟩
  obtain ⟨w, hwV, hwS⟩ := mem_closure_iff.mp hx V hVopen hxV
  obtain ⟨W₀, hW₀sub, hW₀open, hwW₀⟩ := mem_nhds_iff.mp hwS
  let W : Set X := W₀ ∩ c.source
  have hWopen : IsOpen W := hW₀open.inter c.open_source
  have hWsub : W ⊆ c.source := fun _ hy => hy.2
  have hwW : w ∈ W := ⟨hwW₀, hwV.1.1⟩
  have hCWopen : IsOpen (c '' W) :=
    c.isOpen_image_of_subset_source hWopen hWsub
  have hcwCW : c w ∈ c '' W := ⟨w, hwW, rfl⟩
  have hDnear : D =ᶠ[𝓝 (c w)] (fun _ => 0) := by
    refine Filter.eventually_of_mem (hCWopen.mem_nhds hcwCW) ?_
    rintro z ⟨y, hyW, hyz⟩
    have hinv : c.symm z = y := by
      rw [← hyz]
      exact c.left_inv (hWsub hyW)
    change d (f (c.symm z)) - d (g (c.symm z)) = 0
    rw [hinv, hW₀sub hyW.1, sub_self]
  have hBconnected : IsPreconnected (Metric.ball (c x) r) :=
    (convex_ball (c x) r).isPreconnected
  have hDzero : EqOn D (fun _ => 0) (Metric.ball (c x) r) :=
    hDon.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hBconnected hwV.1.2 hDnear
  have hVeq : ∀ y ∈ V, f y = g y := by
    intro y hy
    have hDvalue := hDzero hy.1.2
    change d (f (c.symm (c y))) - d (g (c.symm (c y))) = 0 at hDvalue
    rw [c.left_inv hy.1.1] at hDvalue
    exact d.injOn hy.2.1 hy.2.2 (sub_eq_zero.mp hDvalue)
  exact Filter.eventually_of_mem (hVopen.mem_nhds hxV) hVeq

/-- The identity principle for maps between connected complex-analytic surfaces.
One genuine germ equality propagates globally, using the proved closed germ locus
and the standard openness of a neighborhood predicate. Compactness is unnecessary. -/
theorem h84s_contMDiff_eq_of_germ
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [ConnectedSpace X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y]
    {f g : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) {x₀ : X}
    (hseed : f =ᶠ[𝓝 x₀] g) :
    f = g := by
  let S : Set X := {x | f =ᶠ[𝓝 x] g}
  have hSclosed : IsClosed S := h84s_isClosed_germEq hf hg
  have hSopen : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSnonempty : S.Nonempty := ⟨x₀, hseed⟩
  have hSuniv : S = Set.univ := by
    rcases (isClopen_iff (s := S)).mp ⟨hSclosed, hSopen⟩ with hEmpty | hUniv
    · exact False.elim (hSnonempty.ne_empty hEmpty)
    · exact hUniv
  funext x
  have hxS : x ∈ S := by rw [hSuniv]; exact mem_univ x
  exact hxS.self_of_nhds

/-- A continuous self-map fixing p is the identity germ if its chart expression is.
Source and target membership are supplied on actual neighborhoods before using chart
injectivity, so off-chart total-function values never enter this argument. -/
theorem h84s_germ_eq_id_of_chart_germ
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → X} {p : X} (hf : Continuous f) (hfix : f p = p)
    (hchart :
      ((chartAt ℂ p) ∘ f ∘ (chartAt ℂ p).symm) =ᶠ[𝓝 ((chartAt ℂ p) p)] id) :
    f =ᶠ[𝓝 p] id := by
  let c := chartAt ℂ p
  have hp : p ∈ c.source := mem_chart_source ℂ p
  have hc : ContinuousAt c p :=
    c.continuousOn_toFun.continuousAt (c.open_source.mem_nhds hp)
  have hcoord := hc.tendsto.eventually hchart
  have hpF : f p ∈ c.source := by rw [hfix]; exact hp
  have hFsource : ∀ᶠ y in 𝓝 p, f y ∈ c.source :=
    (c.open_source.preimage hf).mem_nhds hpF
  have hsource : ∀ᶠ y in 𝓝 p, y ∈ c.source := c.open_source.mem_nhds hp
  filter_upwards [hcoord, hFsource, hsource] with y hcy hfy hy
  change f y = y
  change c (f (c.symm (c y))) = c y at hcy
  rw [c.left_inv hy] at hcy
  exact c.injOn hfy hy hcy

/-- The surface bridge needed after finite-order chart-germ rigidity:
a complex-analytic self-map of a connected surface with one identity chart germ is
globally identity. The local rigidity hypothesis can be supplied by the already
proved h84l_analytic_periodic_germ_eq_id block; no cyclicity or RH assumption occurs. -/
theorem h84s_surface_eq_id_of_chart_germ
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
    {f : X → X} {p : X} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hfix : f p = p)
    (hchart :
      ((chartAt ℂ p) ∘ f ∘ (chartAt ℂ p).symm) =ᶠ[𝓝 ((chartAt ℂ p) p)] id) :
    f = id := by
  have hgerm := h84s_germ_eq_id_of_chart_germ hf.continuous hfix hchart
  exact h84s_contMDiff_eq_of_germ hf contMDiff_id hgerm

end LiZhongQC

