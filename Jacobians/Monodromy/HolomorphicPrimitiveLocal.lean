/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Local primitives of holomorphic 1-forms (Wall A, step 0)

The chart-local holomorphic Poincaré lemma on a Riemann surface: every point has a
path-connected open neighbourhood on which a given holomorphic 1-form `η` has a holomorphic
primitive (`IsLocalPrimitiveOn η F U`, the value-wise `dF = η`), and two primitives on a
preconnected open set differ by a constant.

Built from three existing bridges:
* the chart coefficient `Montel.localRep η x₀ ∘ chart⁻¹` is analytic on the chart target
  (`localRep_analyticOn_chartTarget`), so it has a primitive `G` on any ball
  (`exists_primitive_of_convex`); `F := G ∘ chart` is the local primitive;
* `toFun_eq_localRep_smul` (the 1-form side) and `mfderiv_apply_symmL_eq_deriv` (the
  derivative side) reduce the value-wise identity `η = dF` on the 1-dimensional tangent
  space to the single scalar equation `localRep η x₀ = (F ∘ chart⁻¹)'` — the frame lemma
  `oneForm_eq_mfderiv_of_frame_eq`.

Reference: Forster, *Lectures on Riemann Surfaces*, §10.5; Miranda Ch. IV §1.
-/
import Jacobians.CanonicalForms.CanonicalFormDifferential
import Jacobians.Path.Primitive
noncomputable section

open scoped Manifold ContDiff Topology
open Set Metric

namespace Jacobians


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `F` is a **holomorphic primitive of `η` on `U`**: at every point of `U` the function `F`
is manifold-differentiable and its intrinsic differential reads `η` on every tangent vector
(the value-wise `dF = η` of `HasHolomorphicPrimitives`). -/
def IsLocalPrimitiveOn (η : HolomorphicOneForms X) (F : X → ℂ) (U : Set X) : Prop :=
  ∀ y ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y ∧
    ∀ v : TangentSpace 𝓘(ℂ) y, η.toFun y v = mfderiv 𝓘(ℂ) 𝓘(ℂ) F y v

/-! ### The frame lemma: `dF = η` at `y` ⟺ one scalar equation in the chart at `x₀` -/

/-- **The frame lemma.**  For `y` in the chart source at `x₀` where `F` is differentiable, if
the chart-pullback derivative of `F` matches the local representative of `η` (a single scalar
equation), then `dF = η` holds at `y` on **every** tangent vector: both sides are ℂ-linear on
the 1-dimensional `T_y X`, and they agree on the spanning vector `symmL ℂ y 1` —
`η.toFun y (symmL 1) = localRep η x₀ y` by definition,
`mfderiv F y (symmL 1) = (F ∘ chart⁻¹)′(chart y)` by `mfderiv_apply_symmL_eq_deriv`. -/
theorem oneForm_eq_mfderiv_of_frame_eq (η : HolomorphicOneForms X) (F : X → ℂ) {x₀ y : X}
    (hy : y ∈ (chartAt ℂ x₀).source) (hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y)
    (hfr : Montel.localRep η x₀ y = deriv (F ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) y)) :
    ∀ v : TangentSpace 𝓘(ℂ) y, η.toFun y v = mfderiv 𝓘(ℂ) 𝓘(ℂ) F y v := by
  intro v
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with he
  have hyb : y ∈ e.baseSet := by
    rw [he, Montel.baseSet_eq_chartAt_source x₀]; exact hy
  set φ := e.continuousLinearEquivAt ℂ y hyb with hφ
  -- decompose `v = (φ v) • symmL ℂ y 1`
  have hv_eq : v = (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ) y) (φ v) :=
    (ContinuousLinearEquiv.symm_apply_apply φ v).symm
  have hφv_smul : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ) y) (φ v) =
      (φ v) • ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ) y) 1) := by
    have h1 : (φ v : ℂ) = (φ v) • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [h1]
    exact (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ) y).map_smul (φ v) 1
  have h_symmL : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ) y) = e.symmL ℂ y :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq' e hyb
  have hvfin : v = (φ v) • (e.symmL ℂ y 1) := by
    rw [← h_symmL, ← hφv_smul, ← hv_eq]
  -- both sides on the frame vector
  have hframe : η.toFun y (e.symmL ℂ y 1) = mfderiv 𝓘(ℂ) 𝓘(ℂ) F y (e.symmL ℂ y 1) := by
    have hL : η.toFun y (e.symmL ℂ y 1) = Montel.localRep η x₀ y := rfl
    have hR : mfderiv 𝓘(ℂ) 𝓘(ℂ) F y (e.symmL ℂ y 1)
        = deriv (F ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) y) :=
      Dolbeault.mfderiv_apply_symmL_eq_deriv F hy hF
    rw [hL, hR, hfr]
  -- linearity transports the frame identity to `v`
  have hη : η.toFun y v = (φ v) • η.toFun y (e.symmL ℂ y 1) := by
    conv_lhs => rw [hvfin]
    exact (η.toFun y).map_smul (φ v) _
  have hμ : mfderiv 𝓘(ℂ) 𝓘(ℂ) F y v
      = (φ v) • mfderiv 𝓘(ℂ) 𝓘(ℂ) F y (e.symmL ℂ y 1) := by
    conv_lhs => rw [hvfin]
    exact (mfderiv 𝓘(ℂ) 𝓘(ℂ) F y).map_smul (φ v) _
  rw [hη, hμ, hframe]
  rfl

/-! ### Existence: a primitive on a chart-ball neighbourhood of every point -/

/-- **Chart-local existence of holomorphic primitives** (the holomorphic Poincaré lemma on a
Riemann surface): every point has a path-connected open neighbourhood carrying a primitive of
`η`.  The chart coefficient of `η` is analytic on the chart target, hence has a primitive `G`
on a ball around the chart centre (`exists_primitive_of_convex`); `F := G ∘ chart` works on
the preimage of the ball. -/
theorem exists_isLocalPrimitiveOn (η : HolomorphicOneForms X) (x₀ : X) :
    ∃ (U : Set X) (F : X → ℂ), IsOpen U ∧ x₀ ∈ U ∧ IsPathConnected U ∧
      IsLocalPrimitiveOn η F U := by
  -- a ball inside the chart target around the chart centre
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball ((chartAt ℂ x₀) x₀) r ⊆ (chartAt ℂ x₀).target :=
    Metric.mem_nhds_iff.mp
      ((chartAt ℂ x₀).open_target.mem_nhds (mem_chart_target ℂ x₀))
  -- the chart coefficient is analytic on the target, hence differentiable on the ball
  have hcoeff : DifferentiableOn ℂ
      (fun z : ℂ => Montel.localRep η x₀ ((chartAt ℂ x₀).symm z))
      (ball ((chartAt ℂ x₀) x₀) r) :=
    ((Montel.localRep_analyticOn_chartTarget η x₀).mono hball).differentiableOn
  -- the convex primitive on the ball
  obtain ⟨G, hG⟩ := exists_primitive_of_convex (convex_ball _ _) isOpen_ball hcoeff
  refine ⟨(chartAt ℂ x₀).source ∩ (chartAt ℂ x₀) ⁻¹' ball ((chartAt ℂ x₀) x₀) r,
    G ∘ (chartAt ℂ x₀), (chartAt ℂ x₀).isOpen_inter_preimage isOpen_ball,
    ⟨mem_chart_source ℂ x₀, Set.mem_preimage.mpr (mem_ball_self hr)⟩, ?_, ?_⟩
  · -- path-connectedness: the set is the `chart⁻¹` image of the convex ball
    have himg : (chartAt ℂ x₀).symm '' ball ((chartAt ℂ x₀) x₀) r
        = (chartAt ℂ x₀).source ∩ (chartAt ℂ x₀) ⁻¹' ball ((chartAt ℂ x₀) x₀) r :=
      (chartAt ℂ x₀).symm_image_eq_source_inter_preimage hball
    rw [← himg]
    exact ((convex_ball _ _).isPathConnected
      ⟨(chartAt ℂ x₀) x₀, mem_ball_self hr⟩).image'
      ((chartAt ℂ x₀).continuousOn_symm.mono hball)
  · -- the primitive property at each point of the set
    rintro y ⟨hys, hyb⟩
    have hzy : (chartAt ℂ x₀) y ∈ ball ((chartAt ℂ x₀) x₀) r := hyb
    -- the chart pullback of `F` agrees with `G` near `chart y`
    have hgerm : (G ∘ (chartAt ℂ x₀)) ∘ (chartAt ℂ x₀).symm =ᶠ[𝓝 ((chartAt ℂ x₀) y)] G := by
      filter_upwards [isOpen_ball.mem_nhds hzy] with z hz
      have : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z :=
        (chartAt ℂ x₀).right_inv (hball hz)
      simp [Function.comp_apply, this]
    have hGdiff : DifferentiableAt ℂ G ((chartAt ℂ x₀) y) := (hG _ hzy).differentiableAt
    have hpull : DifferentiableAt ℂ ((G ∘ (chartAt ℂ x₀)) ∘ (chartAt ℂ x₀).symm)
        ((chartAt ℂ x₀) y) := hGdiff.congr_of_eventuallyEq hgerm
    have hMD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (chartAt ℂ x₀)) y := by
      have h := Dolbeault.mdifferentiableAt_of_differentiableAt_comp
        (G ∘ (chartAt ℂ x₀)) (hball hzy) hpull
      rwa [(chartAt ℂ x₀).left_inv hys] at h
    refine ⟨hMD, ?_⟩
    -- frame equation: `(F ∘ chart⁻¹)′(chart y) = G′(chart y) = localRep η x₀ y`
    refine oneForm_eq_mfderiv_of_frame_eq η (G ∘ (chartAt ℂ x₀)) hys hMD ?_
    have hderiv : deriv ((G ∘ (chartAt ℂ x₀)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) y)
        = deriv G ((chartAt ℂ x₀) y) := Filter.EventuallyEq.deriv_eq hgerm
    rw [hderiv, (hG _ hzy).deriv]
    rw [(chartAt ℂ x₀).left_inv hys]

/-! ### Rigidity: two primitives on a preconnected open set differ by a constant -/

/-- **Chart-pullback differentiability from manifold differentiability** (the converse of
`mdifferentiableAt_of_differentiableAt_comp`): if `f` is `MDifferentiableAt y` for `y` in the
chart source at `x`, then `f ∘ chart⁻¹` is `DifferentiableAt (chart y)`. -/
theorem differentiableAt_comp_chart_symm {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {f : X → ℂ} {x y : X}
    (hy : y ∈ (chartAt ℂ x).source) (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    DifferentiableAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := by
  have hyt : (chartAt ℂ x) y ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hy
  have hytE : (chartAt ℂ x) y ∈ (extChartAt 𝓘(ℂ) x).target := by
    rw [extChartAt_target, ModelWithCorners.range_eq_univ]
    simpa using hyt
  have hsymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm ((chartAt ℂ x) y) := by
    have h1 := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := x) hytE
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h1
  have hfy : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f ((extChartAt 𝓘(ℂ) x).symm ((chartAt ℂ x) y)) := by
    have hpt : (extChartAt 𝓘(ℂ) x).symm ((chartAt ℂ x) y) = y := by
      show (chartAt ℂ x).symm ((chartAt ℂ x) y) = y
      exact (chartAt ℂ x).left_inv hy
    rwa [hpt]
  have hcomp := MDifferentiableAt.comp ((chartAt ℂ x) y) hfy hsymm
  exact mdifferentiableAt_iff_differentiableAt.mp hcomp

/-- On an open set, the difference of two primitives of the same form is **locally constant**:
near every point it is constant on a chart ball (its chart pullback is differentiable with
vanishing derivative on a convex set). -/
theorem isLocalPrimitiveOn_sub_locally_const {η : HolomorphicOneForms X} {F F' : X → ℂ}
    {U : Set X} (hU : IsOpen U) (hF : IsLocalPrimitiveOn η F U)
    (hF' : IsLocalPrimitiveOn η F' U) {y : X} (hy : y ∈ U) :
    ∀ᶠ w in 𝓝 y, F w - F' w = F y - F' y := by
  set e := chartAt ℂ y with he
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hz₀ : e y ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source (mem_chart_source ℂ y), by
      rw [Set.mem_preimage, e.left_inv (mem_chart_source ℂ y)]; exact hy⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hz₀)
  set g : ℂ → ℂ := fun z => F (e.symm z) - F' (e.symm z) with hg
  have hgcomp : ((F - F') ∘ e.symm) = g := by funext w; rfl
  -- on the ball, `g` is differentiable with vanishing derivative
  have hpt : ∀ z ∈ ball (e y) r, DifferentiableAt ℂ g z ∧ fderiv ℂ g z = 0 := by
    intro z hz
    obtain ⟨hzt, hzU⟩ := hball hz
    have hws : e.symm z ∈ e.source := e.map_target hzt
    have hFd := (hF _ hzU).1
    have hF'd := (hF' _ hzU).1
    have hsub : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F - F') (e.symm z) := hFd.sub hF'd
    have hdz : DifferentiableAt ℂ ((F - F') ∘ e.symm) (e (e.symm z)) :=
      differentiableAt_comp_chart_symm (x := y) hws hsub
    rw [e.right_inv hzt, hgcomp] at hdz
    refine ⟨hdz, ?_⟩
    -- the intrinsic differential of the difference vanishes on `U`
    have hmf0 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (F - F') (e.symm z) = 0 := by
      have hmfeq : mfderiv 𝓘(ℂ) 𝓘(ℂ) F (e.symm z) = mfderiv 𝓘(ℂ) 𝓘(ℂ) F' (e.symm z) :=
        ContinuousLinearMap.ext fun v => ((hF _ hzU).2 v).symm.trans ((hF' _ hzU).2 v)
      rw [mfderiv_sub hFd hF'd, hmfeq]
      exact sub_self _
    have hder := (Dolbeault.mfderiv_apply_symmL_eq_deriv (F - F') hws hsub).symm
    rw [hmf0] at hder
    simp only [ContinuousLinearMap.zero_apply] at hder
    rw [e.right_inv hzt, hgcomp] at hder
    -- `hder : deriv g z = 0`; convert to a vanishing Fréchet derivative
    have hHD : HasDerivAt g 0 z := by
      have h := hdz.hasDerivAt
      rwa [hder] at h
    have hHF : HasFDerivAt g (0 : ℂ →L[ℂ] ℂ) z := by
      have h := hHD.hasFDerivAt
      convert h using 1
      ext
      simp
    exact hHF.fderiv
  -- constancy on the convex ball
  have hconst : ∀ z ∈ ball (e y) r, g z = g (e y) :=
    fun z hz => Convex.is_const_of_fderivWithin_eq_zero (convex_ball _ _)
      (fun w hw => ((hpt w hw).1).differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen isOpen_ball hw]; exact (hpt w hw).2)
      hz (mem_ball_self hr)
  -- transfer back to a neighbourhood of `y` in `X`
  have hVopen : IsOpen (e.source ∩ e ⁻¹' ball (e y) r) := e.isOpen_inter_preimage isOpen_ball
  have hyV : y ∈ e.source ∩ e ⁻¹' ball (e y) r :=
    ⟨mem_chart_source ℂ y, Set.mem_preimage.mpr (mem_ball_self hr)⟩
  filter_upwards [hVopen.mem_nhds hyV] with w hw
  obtain ⟨hws, hwb⟩ := hw
  have h1 : g (e w) = g (e y) := hconst _ hwb
  have h2 : g (e w) = F w - F' w := by
    show F (e.symm (e w)) - F' (e.symm (e w)) = F w - F' w
    rw [e.left_inv hws]
  have h3 : g (e y) = F y - F' y := by
    show F (e.symm (e y)) - F' (e.symm (e y)) = F y - F' y
    rw [e.left_inv (mem_chart_source ℂ y)]
  rw [← h2, h1, h3]

/-- **Rigidity**: two primitives of `η` on a preconnected open set differ by a constant —
their difference is locally constant (`isLocalPrimitiveOn_sub_locally_const`), and a locally
constant function on a preconnected set takes one value (clopen argument). -/
theorem isLocalPrimitiveOn_sub_const {η : HolomorphicOneForms X} {F F' : X → ℂ}
    {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) (hF : IsLocalPrimitiveOn η F U)
    (hF' : IsLocalPrimitiveOn η F' U) {a b : X} (ha : a ∈ U) (hb : b ∈ U) :
    F a - F' a = F b - F' b := by
  set f : X → ℂ := fun w => F w - F' w with hf
  have hloc : ∀ w ∈ U, ∀ᶠ u in 𝓝 w, f u = f w :=
    fun w hw => isLocalPrimitiveOn_sub_locally_const hU hF hF' hw
  -- separate `U` by the interiors of the level set of `f b` and of its complement
  set W₁ : Set X := interior {u | f u = f b} with hW₁
  set W₂ : Set X := interior {u | f u ≠ f b} with hW₂
  have hsub : U ⊆ W₁ ∪ W₂ := by
    intro w hw
    rcases eq_or_ne (f w) (f b) with hwb | hwb
    · left
      rw [hW₁, mem_interior_iff_mem_nhds]
      filter_upwards [hloc w hw] with u hu
      show f u = f b
      rw [hu, hwb]
    · right
      rw [hW₂, mem_interior_iff_mem_nhds]
      filter_upwards [hloc w hw] with u hu
      show f u ≠ f b
      rw [hu]
      exact hwb
  have hbW₁ : b ∈ U ∩ W₁ := ⟨hb, by
    rw [hW₁, mem_interior_iff_mem_nhds]
    filter_upwards [hloc b hb] with u hu
    show f u = f b
    exact hu⟩
  by_contra hne
  have haW₂ : a ∈ U ∩ W₂ := ⟨ha, by
    rw [hW₂, mem_interior_iff_mem_nhds]
    filter_upwards [hloc a ha] with u hu
    show f u ≠ f b
    rw [hu]
    exact hne⟩
  obtain ⟨u, _, hu₁, hu₂⟩ :=
    hUc W₁ W₂ isOpen_interior isOpen_interior hsub ⟨b, hbW₁⟩ ⟨a, haW₂⟩
  rw [hW₁] at hu₁
  rw [hW₂] at hu₂
  have h₁ : u ∈ {w | f w = f b} := interior_subset hu₁
  have h₂ : u ∈ {w | f w ≠ f b} := interior_subset hu₂
  exact h₂ h₁

end Jacobians
