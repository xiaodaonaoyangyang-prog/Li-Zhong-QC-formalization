/-
  The ω₀-factorization of meromorphic pair-forms (Miranda Ch. VI pp. 186–188).

  A meromorphic 1-form on the compact Riemann surface `X` is represented as a PAIR `(g₀, h)` of
  meromorphic functions meaning `h·dg₀`.  To feed it into the 1-form residue theorem
  `residueTheorem_unconditional` (which is typed at `ω₀·g` with `ω₀ : HolomorphicOneForms X`
  HOLOMORPHIC), we factor `dg₀ = q·ω₀` through any nonzero holomorphic 1-form `ω₀` (existence =
  `0 < genus X`), where the quotient

    `derivQuotient ω₀ g₀ : X → ℂ`,  `y ↦ (dg₀-coefficient at y)/(ω₀-coefficient at y)`

  (both read in `y`'s OWN canonical chart) is a GLOBAL meromorphic function.  Then
  `h·dg₀ = (h·q)·ω₀` and the pair-form residue theorem reduces to the 1-form one.

  Contents:
  * **Identity-theorem atoms** for a nonzero holomorphic 1-form (analytic continuation on the
    connected `X`, clopen argument): `eq_zero_of_coeffAt_eventually_zero` (global propagation),
    `coeffAt_eventually_ne_zero` (zeros are isolated), `finite_localRep_self_eq_zero` (the zero
    set is FINITE — the `div(ω₀) ≥ 0` finiteness atom).
  * **`chartTransitionFactor` = transition derivative**
    (`chartTransitionFactor_eq_deriv_transition`): the Montel chart-transition factor of the tangent
    bundle is the honest `deriv` of the chart-transition map — the bridge that makes the
    dg₀-coefficient (chain rule) and the ω₀-coefficient (`localRep_chart_transition`) transform with
    the SAME factor, so their ratio is chart-coherent.
  * **The quotient** `derivQuotient`/`derivQuotientFn`: its chart-coherence
    (`derivQuotient_eventuallyEq_chart`) and global meromorphy (`isMeromorphic_derivQuotient`,
    via Mathlib's `MeromorphicAt.deriv` + `MeromorphicAt.div` + germ invariance).

  Everything here is complete and depends on no unproved lemma.
-/
import Jacobians.Cech.MeromorphicAnalyticBadSet
import Jacobians.Finiteness.CechModelManifold
import Jacobians.ResidueCalculus.FormCoeff
open scoped Manifold ContDiff Topology
open Bundle Filter Metric


namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Generic helpers: residue of an analytic germ, punctured chart transfers, finite avoidance -/

/-- `Res_c(f) = 0` for `f` analytic AT `c` (point version of
`resAt_eq_zero_of_differentiableOn_ball`; analyticity spreads to a small ball). -/
theorem resAt_eq_zero_of_analyticAt {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    resAt f c = 0 := by
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball c ρ, DifferentiableAt ℂ f z := by
    have hev := hf.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

/-- The canonical chart maps the punctured neighbourhood filter of its centre to the punctured
neighbourhood filter of the centre's image (continuity + injectivity on the source). -/
theorem tendsto_chart_nhdsNE {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    Tendsto (chartAt (H := ℂ) x) (𝓝[≠] x) (𝓝[≠] ((chartAt (H := ℂ) x) x)) := by
  have hx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((chartAt (H := ℂ) x).continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hx)] with y hy hysrc
  exact fun heq => hy ((chartAt (H := ℂ) x).injOn hysrc hx heq)

/-- The inverse canonical chart maps the punctured neighbourhood filter of the centre's image to
the punctured neighbourhood filter of the centre. -/
theorem tendsto_chart_symm_nhdsNE {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    Tendsto (chartAt (H := ℂ) x).symm (𝓝[≠] ((chartAt (H := ℂ) x) x)) (𝓝[≠] x) := by
  have hx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  have hxt : (chartAt (H := ℂ) x) x ∈ (chartAt (H := ℂ) x).target :=
    (chartAt (H := ℂ) x).map_source hx
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont := ((chartAt (H := ℂ) x).continuousAt_symm hxt).tendsto
    rw [(chartAt (H := ℂ) x).left_inv hx] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((chartAt (H := ℂ) x).open_target.mem_nhds hxt)] with w hw hwt
    intro heq
    apply hw
    have hr : (chartAt (H := ℂ) x) ((chartAt (H := ℂ) x).symm w) = w :=
      (chartAt (H := ℂ) x).right_inv hwt
    rw [Set.mem_singleton_iff.mp heq] at hr
    exact hr.symm

/-- A finite set is eventually avoided on every punctured neighbourhood (T1 space). -/
theorem eventually_nhdsNE_notMem_of_finite {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {S : Set Y} (hS : S.Finite) (x : Y) : ∀ᶠ y in 𝓝[≠] x, y ∉ S := by
  have hopen : IsOpen (S \ {x})ᶜ := (hS.subset Set.diff_subset).isClosed.isOpen_compl
  have hx : x ∈ (S \ {x})ᶜ := fun hmem => hmem.2 rfl
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hx)] with y hy hyc
  exact fun hyS => hyc ⟨hyS, hy⟩

/-! ### Existence of a nonzero holomorphic 1-form from `0 < genus` -/

/-- **Positive genus yields a nonzero holomorphic 1-form** (`genus X = dim_ℂ Ω(X) > 0`). -/
theorem exists_holomorphicOneForm_ne_zero (hgenus : 0 < genus X) :
    ∃ ω₀ : HolomorphicOneForms X, ω₀ ≠ 0 := by
  have : Nontrivial (HolomorphicOneForms X) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) hgenus
  exact exists_ne 0

/-! ### Identity-theorem atoms for holomorphic 1-forms

A nonzero holomorphic 1-form does not vanish on any open set (analytic continuation on the
connected `X`, clopen argument), hence its zeros are isolated and — `X` compact — finite. -/

/-- A vanishing 1-form value kills every local representative (the representative is the form
paired with a tangent vector). -/
theorem localRep_eq_zero_of_toFun_eq_zero (α : HolomorphicOneForms X) (x₀ : X) {y : X}
    (h : α.toFun y = 0) : Jacobians.Montel.localRep α x₀ y = 0 := by
  unfold Jacobians.Montel.localRep
  rw [h]
  exact ContinuousLinearMap.zero_apply _

/-- Conversely, on the chart source a vanishing local representative kills the 1-form value: the
transported unit tangent spans the 1-dimensional fibre (off-centre generalization of the
`exists_localRep_self_ne_zero` argument). -/
theorem toFun_eq_zero_of_localRep_eq_zero (α : HolomorphicOneForms X) {x₀ y : X}
    (hy : y ∈ (chartAt (H := ℂ) x₀).source)
    (h : Jacobians.Montel.localRep α x₀ y = 0) : α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with he
  have hybase : y ∈ e.baseSet := hy
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.zero_apply]
  have hv : e.symmL ℂ y (e.continuousLinearMapAt ℂ y v) = v :=
    e.symmL_continuousLinearMapAt hybase v
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ)
    rwa [smul_eq_mul, mul_one] at h2
  calc α.toFun y v = α.toFun y (e.symmL ℂ y c) := by rw [hv]
    _ = α.toFun y (c • e.symmL ℂ y 1) := by rw [hsm]
    _ = c • α.toFun y (e.symmL ℂ y 1) := by rw [(α.toFun y).map_smul]
    _ = c • Jacobians.Montel.localRep α x₀ y := rfl
    _ = 0 := by rw [h, smul_zero]

/-- Chart-side eventual vanishing of the coefficient pushes to manifold-side eventual vanishing
of the 1-form (the fibres are 1-dimensional, spanned by the chart tangent). -/
theorem toFun_eventually_zero_of_coeffAt_eventually_zero (α : HolomorphicOneForms X) {p : X}
    (h : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) p) p), coeffAt α p w = 0) :
    ∀ᶠ y in 𝓝 p, α.toFun y = 0 := by
  have hp : p ∈ (chartAt (H := ℂ) p).source := mem_chart_source ℂ p
  have hcont : ContinuousAt (chartAt (H := ℂ) p) p := (chartAt (H := ℂ) p).continuousAt hp
  filter_upwards [hcont.eventually h,
    (chartAt (H := ℂ) p).open_source.mem_nhds hp] with y hy hysrc
  have hcoeff : coeffAt α p ((chartAt (H := ℂ) p) y) = Jacobians.Montel.localRep α p y := by
    simp only [coeffAt]
    rw [(chartAt (H := ℂ) p).left_inv hysrc]
  rw [hcoeff] at hy
  exact toFun_eq_zero_of_localRep_eq_zero α hysrc hy

/-- **Identity theorem for holomorphic 1-forms (global propagation).**  If the canonical-chart
coefficient of `α` vanishes on a neighbourhood of one chart centre, then `α = 0` — the set where
`α` vanishes locally is clopen (openness is trivial; closedness is the one-variable isolated-zeros
dichotomy applied to the analytic coefficient), and `X` is connected. -/
theorem eq_zero_of_coeffAt_eventually_zero (α : HolomorphicOneForms X) {x : X}
    (h : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) x) x), coeffAt α x w = 0) : α = 0 := by
  classical
  set S := {p : X | ∀ᶠ y in 𝓝 p, α.toFun y = 0} with hSdef
  have hopen : IsOpen S := isOpen_setOf_eventually_nhds
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    -- the coefficient at `p` is not eventually zero (else `p ∈ S`) …
    have hno : ¬ ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) p) p), coeffAt α p w = 0 := fun hev =>
      hp (toFun_eventually_zero_of_coeffAt_eventually_zero α hev)
    have hpt : (chartAt (H := ℂ) p) p ∈ (chartAt (H := ℂ) p).target :=
      (chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p)
    -- … so by the isolated-zeros dichotomy it is eventually NONZERO on the punctured chart nbhd
    have hne : ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) p) p), coeffAt α p w ≠ 0 :=
      ((coeffAt_analyticAt α p hpt).eventually_eq_zero_or_eventually_ne_zero).resolve_left hno
    -- transfer to `X`: punctured-near `p`, the form does not vanish, so no point lies in `S`
    have h1 := (tendsto_chart_nhdsNE p).eventually hne
    have h2 : ∀ᶠ y in 𝓝[≠] p, y ∈ (chartAt (H := ℂ) p).source :=
      eventually_nhdsWithin_of_eventually_nhds
        ((chartAt (H := ℂ) p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hXne : ∀ᶠ y in 𝓝[≠] p, y ∈ Sᶜ := by
      filter_upwards [h1, h2] with y hy hysrc
      intro hyS
      apply hy
      have hzero : α.toFun y = 0 :=
        (show ∀ᶠ z in 𝓝 y, α.toFun z = 0 from hyS).self_of_nhds
      show coeffAt α p ((chartAt (H := ℂ) p) y) = 0
      simp only [coeffAt]
      rw [(chartAt (H := ℂ) p).left_inv hysrc]
      exact localRep_eq_zero_of_toFun_eq_zero α p hzero
    rw [eventually_nhdsWithin_iff] at hXne
    rw [← Filter.eventually_mem_set]
    filter_upwards [hXne] with y hy
    by_cases hyp : y = p
    · subst hyp; exact hp
    · exact hy (by simpa using hyp)
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with hempty | huniv
  · exfalso
    have hxS : x ∈ S := toFun_eventually_zero_of_coeffAt_eventually_zero α h
    rw [hempty] at hxS
    exact hxS
  · refine ContMDiffSection.ext fun y => ?_
    have hyS : y ∈ S := by rw [huniv]; trivial
    exact (show ∀ᶠ z in 𝓝 y, α.toFun z = 0 from hyS).self_of_nhds

/-- **Isolated zeros of a nonzero holomorphic 1-form**: at every chart centre, the canonical-chart
coefficient is eventually nonzero on the punctured neighbourhood. -/
theorem coeffAt_eventually_ne_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) (x : X) :
    ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) x) x), coeffAt α x w ≠ 0 := by
  have hpt : (chartAt (H := ℂ) x) x ∈ (chartAt (H := ℂ) x).target :=
    (chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x)
  refine ((coeffAt_analyticAt α x hpt).eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
  exact fun hz => hα (eq_zero_of_coeffAt_eventually_zero α hz)

/-- **The zero set of a nonzero holomorphic 1-form is FINITE** (the `div(ω₀) ≥ 0` finiteness atom:
zeros are isolated by `coeffAt_eventually_ne_zero` + the chart-transition comparison, and `X` is
compact). -/
theorem finite_localRep_self_eq_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    {x : X | Jacobians.Montel.localRep α x x = 0}.Finite := by
  refine Jacobians.finite_of_forall_eventually_nhdsNE_notMem fun x => ?_
  have h1 := (tendsto_chart_nhdsNE x).eventually (coeffAt_eventually_ne_zero α hα x)
  have h2 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt (H := ℂ) x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt (H := ℂ) x).open_source.mem_nhds (mem_chart_source ℂ x))
  filter_upwards [h1, h2] with y hy hysrc
  intro hzero
  -- the coefficient in `x`'s chart is nonzero at `y` …
  have hxy : Jacobians.Montel.localRep α x y ≠ 0 := by
    have hcoeff : coeffAt α x ((chartAt (H := ℂ) x) y) = Jacobians.Montel.localRep α x y := by
      simp only [coeffAt]
      rw [(chartAt (H := ℂ) x).left_inv hysrc]
    rwa [hcoeff] at hy
  -- … and differs from the own-chart coefficient by the nonzero transition factor
  have htrans := Jacobians.Montel.localRep_chart_transition α x y y (mem_chart_source ℂ y) hysrc
  rw [hzero] at htrans
  rcases mul_eq_zero.mp htrans.symm with hc | hl
  · exact Jacobians.Montel.chartTransitionFactor_ne_zero (X := X) x y y hc
  · exact hxy hl

/-! ### The chart-transition factor is the transition derivative -/

/-- **`chartTransitionFactor` = derivative of the chart transition.**  The Montel tangent-bundle
transition factor at `y` (converting `x₀'`-chart tangent coordinates to `x₀`-chart ones) is the
honest one-variable derivative of the chart-transition map `chartAt x₀ ∘ (chartAt x₀').symm` at
`chartAt x₀' y`.  Unwinds `tangentBundleCore_coordChange_achart`; this is the bridge that makes
the `dg₀`-coefficient (chain rule) and the `ω₀`-coefficient (`localRep_chart_transition`)
transform with the SAME factor. -/
theorem chartTransitionFactor_eq_deriv_transition {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {x₀ x₀' y : X}
    (h' : y ∈ (chartAt (H := ℂ) x₀').source) (h : y ∈ (chartAt (H := ℂ) x₀).source) :
    Jacobians.Montel.chartTransitionFactor x₀ x₀' y
      = deriv ((chartAt (H := ℂ) x₀) ∘ (chartAt (H := ℂ) x₀').symm)
          ((chartAt (H := ℂ) x₀') y) := by
  unfold Jacobians.Montel.chartTransitionFactor
  have hb : y ∈ (tangentBundleCore 𝓘(ℂ) X).baseSet (achart ℂ x₀') ∩
      (tangentBundleCore 𝓘(ℂ) X).baseSet (achart ℂ x₀) := by
    simp only [tangentBundleCore_baseSet, coe_achart]
    exact ⟨h', h⟩
  have h1 : Trivialization.coordChangeL ℂ
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) y 1
      = (tangentBundleCore 𝓘(ℂ) X).coordChange (achart ℂ x₀') (achart ℂ x₀) y 1 :=
    (tangentBundleCore 𝓘(ℂ) X).localTriv_coordChange_eq (achart ℂ x₀') (achart ℂ x₀) hb 1
  rw [h1, tangentBundleCore_coordChange_achart x₀' x₀ y]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    fderivWithin_univ]
  exact fderiv_apply_one_eq_deriv

/-! ### The quotient `q = dg₀/ω₀` -/

/-- **The quotient `dg₀/ω₀` as a function on `X`** (Miranda Ch. VI p. 186: any meromorphic 1-form
is a meromorphic-function multiple of a fixed nonzero ω₀).  Value at `y`: the `dg₀`-coefficient
`deriv (g₀ ∘ chart_y⁻¹)` over the `ω₀`-coefficient `localRep ω₀ y`, both read in `y`'s OWN
canonical chart at its centre (junk `0` where the denominator vanishes, matching repo
`div`-conventions). -/
noncomputable def derivQuotient (ω₀ : HolomorphicOneForms X) (g₀ : MeromorphicFunction X) :
    X → ℂ := fun y =>
  deriv (fun w => g₀.toFun ((chartAt (H := ℂ) y).symm w)) ((chartAt (H := ℂ) y) y)
    / Jacobians.Montel.localRep ω₀ y y

/-- **Chart-coherence of the quotient.**  Near any chart centre `chartAt x x` (off the centre),
the pullback of `derivQuotient ω₀ g₀` agrees with the single-chart quotient
`deriv (g₀ ∘ chart_x⁻¹) / coeffAt ω₀ x`: at each nearby point both the numerator (chain rule) and
the denominator (`localRep_chart_transition`) pick up the SAME nonzero transition-derivative
factor (`chartTransitionFactor_eq_deriv_transition`), which cancels in the ratio.  The finitely
many points where `g₀`'s own-chart pullback fails honest analyticity are avoided eventually
(`MeromorphicFunction.finite_nonAnalyticAt`). -/
theorem derivQuotient_eventuallyEq_chart (ω₀ : HolomorphicOneForms X)
    (g₀ : MeromorphicFunction X) (x : X) :
    (fun z => derivQuotient ω₀ g₀ ((chartAt (H := ℂ) x).symm z))
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) x) x)]
      fun z => deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z / coeffAt ω₀ x z := by
  have hx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  have hxt : (chartAt (H := ℂ) x) x ∈ (chartAt (H := ℂ) x).target :=
    (chartAt (H := ℂ) x).map_source hx
  -- (a) eventually, the pulled-back point avoids `g₀`'s finite analytic-bad set
  have hbadX : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ
      (fun w => g₀.toFun ((chartAt (H := ℂ) y).symm w)) ((chartAt (H := ℂ) y) y) := by
    filter_upwards [eventually_nhdsNE_notMem_of_finite g₀.finite_nonAnalyticAt x] with y hy
    exact not_not.mp hy
  have hbad := (tendsto_chart_symm_nhdsNE x).eventually hbadX
  -- (b) eventually, `z` lies in the chart target
  have htgt : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) x) x), z ∈ (chartAt (H := ℂ) x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt (H := ℂ) x).open_target.mem_nhds hxt)
  filter_upwards [hbad, htgt] with z hzbad hztgt
  set y := (chartAt (H := ℂ) x).symm z with hydef
  have hysrc : y ∈ (chartAt (H := ℂ) x).source := (chartAt (H := ℂ) x).map_target hztgt
  have hchart_y : (chartAt (H := ℂ) x) y = z := (chartAt (H := ℂ) x).right_inv hztgt
  have hyy : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
  -- transport `g₀`'s own-chart analyticity at `y` to `x`'s chart
  have hg₀x : AnalyticAt ℂ (g₀.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) y) := by
    refine analyticAt_chart_change_to hysrc ?_
    simpa [Function.comp_def] using hzbad
  -- the transition `σ = chart_x ∘ chart_y⁻¹` and its value at the centre image
  have hσ : AnalyticAt ℂ ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) := transition_analyticAt_of_mem hyy hysrc
  have hσpt : ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)
      = (chartAt (H := ℂ) x) y := by
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hyy]
  -- own-chart pullback = x-chart pullback ∘ σ near the centre image
  have hFeq : (fun w => g₀.toFun ((chartAt (H := ℂ) y).symm w))
      =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)]
      (g₀.toFun ∘ (chartAt (H := ℂ) x).symm) ∘
        ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm) := by
    have hyyt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
      (chartAt (H := ℂ) y).map_source hyy
    have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y),
        (chartAt (H := ℂ) y).symm w ∈ (chartAt (H := ℂ) x).source := by
      refine ((chartAt (H := ℂ) y).continuousAt_symm hyyt).eventually ?_
      rw [(chartAt (H := ℂ) y).left_inv hyy]
      exact (chartAt (H := ℂ) x).open_source.mem_nhds hysrc
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
  -- numerator chain rule: D_y = D_x(z) · c
  have hD : deriv (fun w => g₀.toFun ((chartAt (H := ℂ) y).symm w)) ((chartAt (H := ℂ) y) y)
      = deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z
          * Jacobians.Montel.chartTransitionFactor x y y := by
    rw [hFeq.deriv_eq, deriv_comp _ (hσpt ▸ hg₀x.differentiableAt) hσ.differentiableAt]
    rw [hσpt, hchart_y, chartTransitionFactor_eq_deriv_transition hyy hysrc]
    rfl
  -- denominator transition: C_y = c · C_x(z)
  have hC : Jacobians.Montel.localRep ω₀ y y
      = Jacobians.Montel.chartTransitionFactor x y y * Jacobians.Montel.localRep ω₀ x y :=
    Jacobians.Montel.localRep_chart_transition ω₀ x y y hyy hysrc
  have hcoeff : coeffAt ω₀ x z = Jacobians.Montel.localRep ω₀ x y := rfl
  -- assemble: (c·D)/(c·C) = D/C, the factor `c ≠ 0` cancels
  show derivQuotient ω₀ g₀ y = _
  rw [derivQuotient, hD, hC, hcoeff,
    mul_comm (deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z)
      (Jacobians.Montel.chartTransitionFactor x y y)]
  exact mul_div_mul_left _ _ (Jacobians.Montel.chartTransitionFactor_ne_zero x y y)

/-- **The quotient `dg₀/ω₀` is globally meromorphic**: at each chart centre it agrees off the
centre with `deriv (g₀ ∘ chart_x⁻¹) / coeffAt ω₀ x` (chart-coherence), which is meromorphic by
`MeromorphicAt.deriv` + `MeromorphicAt.div`, and meromorphy is a punctured-germ invariant. -/
theorem isMeromorphic_derivQuotient (ω₀ : HolomorphicOneForms X) (g₀ : MeromorphicFunction X) :
    IsMeromorphic X (derivQuotient ω₀ g₀) := by
  intro x
  have hnum : MeromorphicAt (deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)))
      ((chartAt (H := ℂ) x) x) := (g₀.meromorphic x).deriv
  have hden : MeromorphicAt (coeffAt ω₀ x) ((chartAt (H := ℂ) x) x) :=
    (coeffAt_analyticAt ω₀ x
      ((chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x))).meromorphicAt
  exact (hnum.div hden).congr (derivQuotient_eventuallyEq_chart ω₀ g₀ x).symm

/-- The quotient `dg₀/ω₀` bundled as a `MeromorphicFunction`. -/
noncomputable def derivQuotientFn (ω₀ : HolomorphicOneForms X) (g₀ : MeromorphicFunction X) :
    MeromorphicFunction X :=
  ⟨derivQuotient ω₀ g₀, isMeromorphic_derivQuotient ω₀ g₀⟩

@[simp] theorem derivQuotientFn_toFun (ω₀ : HolomorphicOneForms X)
    (g₀ : MeromorphicFunction X) :
    (derivQuotientFn ω₀ g₀).toFun = derivQuotient ω₀ g₀ := rfl

end Jacobians.Dolbeault
