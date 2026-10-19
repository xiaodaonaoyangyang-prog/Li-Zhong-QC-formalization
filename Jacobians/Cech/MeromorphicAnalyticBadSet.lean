/-
  The product of meromorphic functions, and FINITENESS of the analytic-bad set of a global
  meromorphic function (the points where the chart pullback fails honest `AnalyticAt`).

  ## Why this exists (Miranda Ch. VI pp. 186–188)

  The unconditional 1-form residue theorem `residueTheorem_unconditional`
  consumes a meromorphic numerator `g` through the hypothesis "`g`'s chart pullback is honestly
  `AnalyticAt` at every point off the chosen finite `poles`".  A `MeromorphicFunction` carries
  removable-singularity `toFun`-junk, so this hypothesis is *not* automatic off the genuine poles —
  but the set where it fails IS finite:

  * `MeromorphicFunction.eventually_analyticAt_ownChart` — around every point, a global
    meromorphic function is honestly analytic (in each point's OWN canonical chart) on a punctured
    neighbourhood.  Mathlib's `MeromorphicAt.eventually_analyticAt` gives this in the fixed chart
    at the centre; the repo chart-invariance `analyticAt_chart_change` (`CechH0`) transports it to
    each nearby point's own chart.
  * `MeromorphicFunction.finite_nonAnalyticAt` — hence the bad set is isolated, and on the compact
    `X` it is finite (`finite_of_forall_eventually_nhdsNE_notMem`).

  This is what lets the pair-form residue theorem (`PairFormResidueTheorem`) enlarge its pole
  set by a *finite* bad set before invoking the residue-theorem engine.

  Also here: the pointwise product `f * g` of meromorphic functions (`Mul (MeromorphicFunction X)`),
  which Mathlib's `MeromorphicAt.mul` makes immediate (`Jacobians.LinearSystem` provides only
  the ℂ-module structure).
-/
import Jacobians.Cech.CechH0

open scoped Manifold ContDiff Topology
open Filter

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pointwise product of meromorphic functions -/

section Mul
-- The product needs only the charted-space structure (mirror of `IsMeromorphic.add`).

/-- Meromorphy is preserved by pointwise products (`MeromorphicAt.mul` in every chart). -/
theorem IsMeromorphic.mul {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {f g : X → ℂ}
    (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f * g) := fun x => (hf x).mul (hg x)

/-- The pointwise product of meromorphic functions. -/
noncomputable instance {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] :
    Mul (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun * g.toFun, f.meromorphic.mul g.meromorphic⟩⟩

@[simp] theorem MeromorphicFunction.mul_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f g : MeromorphicFunction X) :
    (f * g).toFun = f.toFun * g.toFun := rfl

end Mul

/-! ### An isolated set in a compact space is finite -/

/-- **A set avoided by a punctured neighbourhood of every point is finite** (in a compact space).
The indicator of `S` then has locally finite support, and `LocallyFiniteSupport`'s compactness
lemma finishes.  (This is the `exists_form_divisor` finiteness pattern, extracted for sets.) -/
theorem finite_of_forall_eventually_nhdsNE_notMem {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] {S : Set Y} (h : ∀ x : Y, ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Finite := by
  have hloc : LocallyFiniteSupport (S.indicator (fun _ => (1 : ℕ))) := by
    intro z
    have hz := h z
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hz
    obtain ⟨t, ht, htopen, hzt⟩ := hz
    refine ⟨t, htopen.mem_nhds hzt, (Set.finite_singleton z).subset ?_⟩
    rintro y ⟨hyt, hysupp⟩
    by_contra hne
    have hyS : y ∈ S := by
      by_contra hyS
      exact hysupp (Set.indicator_of_notMem hyS _)
    exact ht y hyt (by simpa using hne) hyS
  have hfin := hloc.finite_inter_support_of_isCompact (isCompact_univ (X := Y))
  rw [Set.univ_inter] at hfin
  refine hfin.subset fun y hy => ?_
  rw [Function.mem_support, Set.indicator_of_mem hy]
  exact one_ne_zero

/-! ### The analytic-bad set of a meromorphic function is finite -/

/-- **Honest analyticity on a punctured neighbourhood, in each point's own chart.**  Around every
`x`, a global meromorphic function is `AnalyticAt` (junk-free, value included) at every nearby
point `y ≠ x`, read in `y`'s OWN canonical chart.  Mathlib's `MeromorphicAt.eventually_analyticAt`
gives analyticity in the chart at `x`; the chart-transition analyticity
(`Jacobians.Dolbeault.analyticAt_chart_change`) transports it to `y`'s chart. -/
theorem MeromorphicFunction.eventually_analyticAt_ownChart (f : MeromorphicFunction X) (x : X) :
    ∀ᶠ y in 𝓝[≠] x,
      AnalyticAt ℂ (fun z => f.toFun ((chartAt (H := ℂ) y).symm z)) ((chartAt (H := ℂ) y) y) := by
  set φ := chartAt (H := ℂ) x with hφ
  have hx_src : x ∈ φ.source := mem_chart_source ℂ x
  have hx_tgt : φ x ∈ φ.target := φ.map_source hx_src
  -- analyticity of the chart-`x` pullback on a punctured neighbourhood of `φ x`
  have h1 : ∀ᶠ w in 𝓝[≠] φ x, AnalyticAt ℂ (f.toFun ∘ φ.symm) w :=
    (f.meromorphic x).eventually_analyticAt
  -- rewrite the point as `(φ ∘ φ.symm) w` (identity on the target) to transfer through the chart
  have h2 : ∀ᶠ w in 𝓝[≠] φ x,
      AnalyticAt ℂ (f.toFun ∘ φ.symm) (((φ : X → ℂ) ∘ φ.symm) w) := by
    filter_upwards [h1, nhdsWithin_le_nhds (φ.open_target.mem_nhds hx_tgt)] with w hw hw_tgt
    rw [Function.comp_apply, φ.right_inv hw_tgt]
    exact hw
  have h3 : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ (f.toFun ∘ φ.symm) (φ y) :=
    (MeromorphicFunction.eventually_comp_chart_iff (φ : X → ℂ) x
      (AnalyticAt ℂ (f.toFun ∘ φ.symm))).mp h2
  have h4 : ∀ᶠ y in 𝓝[≠] x, y ∈ φ.source :=
    eventually_nhdsWithin_of_eventually_nhds (φ.open_source.mem_nhds hx_src)
  filter_upwards [h3, h4] with y hy hy_src
  have hown := Jacobians.Dolbeault.analyticAt_chart_change (h := f.toFun) hy_src hy
  simpa [Function.comp_def] using hown

/-- **The analytic-bad set of a meromorphic function is FINITE.**  The set of points where the
chart pullback of `f` fails honest `AnalyticAt` (genuine poles AND removable-singularity
`toFun`-junk) is isolated (`eventually_analyticAt_ownChart`), hence finite on the compact `X`.
This is the finite enlargement that feeds a `MeromorphicFunction` into the analyticity hypothesis
of `residueTheorem_unconditional`. -/
theorem MeromorphicFunction.finite_nonAnalyticAt (f : MeromorphicFunction X) :
    {x : X | ¬ AnalyticAt ℂ (fun z => f.toFun ((chartAt (H := ℂ) x).symm z))
      ((chartAt (H := ℂ) x) x)}.Finite := by
  refine finite_of_forall_eventually_nhdsNE_notMem fun x => ?_
  filter_upwards [f.eventually_analyticAt_ownChart x] with y hy
  exact fun hbad => hbad hy

end Jacobians
