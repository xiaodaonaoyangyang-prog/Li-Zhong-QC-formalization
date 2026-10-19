import References.GarnettMarshall2005.Ch01.S03_CaratheodoryTheorem
import References.Common.ExtPlaneBorel

/-!
# Garnett–Marshall, Chapter II §1: The Schwarz alternating method

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. II §1 (pp. 37–41;
`full.md` P1:1783–1917).

Conventions as in Chapter I. A finitely connected Jordan domain is a domain `Ω` of `ℂ*` (it may contain `∞`: Green's
function `g(z, ∞)` of §2) whose boundary in `ℂ*` is the union of `p ≥ 1` pairwise disjoint Jordan curves of `ℂ*`.
Boundary functions `f` are real-valued functions on `ℂ*` read on `∂Ω` (the book takes `f` real, P1:1816). "`u` is
harmonic on `Ω`" is `HarmonicOnExt u Ω` (harmonicity in the charts of `ℂ*`), and "`lim_{z→ζ} u(z)`" is the limit along
`𝓝[Ω] ζ` in `ℂ*`. Borel sets and measures on `ℂ*` use the Borel σ-algebra of the shared layer (`open scoped
References`). Harmonic measure is a measure on `ℂ*` (leader ruling D1): the book's set function of P1:1856–1866 is
defined literally (`harmonicMeasureFCSet`), and `harmonicMeasureFC Ω z` is the Borel measure that agrees with it; the
measures are compared in `[0, ∞]`.

* Definition (finitely connected Jordan domain, §1) — `IsFCJordanDomain`
* Definition (piecewise continuous bounded function on `∂Ω`, §1) — `IsPiecewiseContinuousOn`
* Definition (the solution `u_f` of Theorem 1.1: a bounded harmonic function on `Ω` with the boundary values (1.1) at
  the points of continuity of `f`, §1) — `IsBoundedDirichletSolution`, `dirichletSolution`
* Theorem 1.1 (§1) — `thm2_1_1`
* Definition (harmonic measure `ω(z, E, Ω)` of a finitely connected Jordan domain: the set function of P1:1856–1866
  and the Borel measure that agrees with it, §1) — `harmonicMeasureFCSet`, `harmonicMeasureFC`
* Formula (1.2) (§1, P1:1868–1872): `ω(z, ·)` is a Borel measure on `∂Ω`, and `u_f(z) = ∫ f dω(z, ·)` for
  continuous `f` — `eq2_1_2`
* Unlabelled (§1, P1:1874): when `Ω` is simply connected, this harmonic measure agrees with (I.3.3) —
  `harmonicMeasureFC_eq_jordan`
* Formula (1.3) (§1, P1:1876–1882; Harnack's inequality for `ω`) — `eq2_1_3`
* Definition ((1.4), the solution `u_f` of the Dirichlet problem for `f ∈ L¹(∂Ω, dω)`, §1) — `dirichletSolutionL1`
* Formula (1.4) (§1, P1:1882–1910): for `f ∈ L¹(dω)`, `u_f` is harmonic on `Ω`, and `sup |u_f| ≤ ‖f‖_{L^∞(dω)}`
  for bounded `f` — `eq2_1_4`

Helper (not a book notion): `IsDisjointUnionOf` (a set is the union of finitely many, at least one, pairwise disjoint
sets with a given property; used for boundaries made of Jordan curves, analytic Jordan curves, …).

Not stated (inventory U−): the map `f ↦ u_f(z)` is a bounded linear functional on `C(∂Ω)` (P1:1856, immediate from
Theorem 1.1); the approximation steps after (1.4) (density of `C(∂Ω)` in `L¹(dω)`, Harnack's principle, P1:1882–1906);
for bounded `f` continuous at `ζ`, (1.1) holds at `ζ` (P1:1912; the book defers the proof to Theorem 2.7 and
Exercise 1(b), and does not cite it); the remark that the alternating method needs piecewise continuous data
(P1:1914). The proof of Theorem 1.1 (the alternating sequence `u₁ ≥ u₁' ≥ u₂ ≥ …`) is not stated.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane IsJordanCurve)
open References (IsDomainExt IsJordanDomainExt)

/-- `B` is the union of finitely many, at least one, pairwise disjoint sets `Γ₁, …, Γ_p`, each with the property `P`
(helper, not a book notion): `∂Ω = Γ₁ ∪ … ∪ Γ_p`, P1:1791–1795. -/
def IsDisjointUnionOf {X : Type*} (P : Set X → Prop) (B : Set X) : Prop :=
  ∃ (p : ℕ) (Γ : Fin p → Set X), 0 < p ∧ (∀ j, P (Γ j)) ∧ (Pairwise fun i j => Disjoint (Γ i) (Γ j)) ∧
    B = ⋃ j, Γ j

/-- **Definition** (finitely connected Jordan domain, Ch. II §1, P1:1791–1797). A domain `Ω` such that `∂Ω` is a
finite union of pairwise disjoint Jordan curves, `∂Ω = Γ₁ ∪ Γ₂ ∪ … ∪ Γ_p`.
Modelling: `Ω` is a domain of `ℂ*` and the `Γ_j` are Jordan curves of `ℂ*` (the book's "plane domain" may contain
`∞`, as Green's function `g(z, ∞)` in §2 shows; "we may assume `Ω` is bounded", P1:1811); `p ≥ 1`. -/
def IsFCJordanDomain (Ω : Set ExtPlane) : Prop :=
  IsDomainExt Ω ∧ IsDisjointUnionOf IsJordanCurve (frontier Ω)

/-- **Definition** (piecewise continuous function, Ch. II §1, P1:1797). A bounded function `f` on `∂Ω` is piecewise
continuous if there is a finite set `E ⊆ ∂Ω` such that `f` is continuous on `∂Ω \ E` and `f` has left and right
limits at each point of `E`.
Modelling: `f` is real-valued on `ℂ*` and read on `∂Ω`; the left and right limits at `ζ ∈ E` are the one-sided limits
along a loop parametrization (`LehtoVirtanen1973.IsLoopParam`) of the boundary curve through `ζ`, the component of
`∂Ω` containing `ζ`, at every parameter of `ζ`. -/
def IsPiecewiseContinuousOn (Ω : Set ExtPlane) (f : ExtPlane → ℝ) : Prop :=
  (∃ M : ℝ, ∀ ζ ∈ frontier Ω, |f ζ| ≤ M) ∧
    ∃ E : Set ExtPlane, E.Finite ∧ E ⊆ frontier Ω ∧ ContinuousOn f (frontier Ω \ E) ∧
      ∀ ζ ∈ E, ∃ γ : ℝ → ExtPlane, LehtoVirtanen1973.IsLoopParam (connectedComponentIn (frontier Ω) ζ) γ ∧
        ∀ t : ℝ, γ t = ζ →
          (∃ L : ℝ, Tendsto (fun s => f (γ s)) (𝓝[<] t) (𝓝 L)) ∧ ∃ R : ℝ, Tendsto (fun s => f (γ s)) (𝓝[>] t) (𝓝 R)

/-- **Definition** (the function `u_f` of Theorem 1.1, Ch. II §1, P1:1799–1805). `u` is bounded and harmonic on `Ω`,
and (1.1) `lim_{z→ζ} u(z) = f(ζ)` at every point of continuity `ζ ∈ ∂Ω` of `f`.
Modelling: "point of continuity of `f`" is continuity of `f` as a function on `∂Ω`; only the values of `u` on `Ω`
matter. -/
def IsBoundedDirichletSolution (Ω : Set ExtPlane) (f u : ExtPlane → ℝ) : Prop :=
  (∃ M : ℝ, ∀ z ∈ Ω, |u z| ≤ M) ∧ HarmonicOnExt u Ω ∧
    ∀ ζ ∈ frontier Ω, ContinuousWithinAt f (frontier Ω) ζ → Tendsto u (𝓝[Ω] ζ) (𝓝 (f ζ))

/-- **Definition** (the solution `u_f(z)`, Ch. II §1, P1:1799, used for continuous `f` from P1:1856 on). The value at
`z ∈ Ω` of the unique bounded harmonic function with the boundary values (1.1) (`thm2_1_1`).
Modelling: the value over all such functions (the registered "value over all maps" pattern): by the uniqueness in
Theorem 1.1 the set of values is a single point for `z ∈ Ω` and piecewise continuous `f`. Junk: `0` when there is no
such function or when `z ∉ Ω` (then the values are unconstrained), and the supremum of several values (`0` when
they are unbounded) when the bounded solution is not unique, e.g. for `f` continuous at no point of `∂Ω`, where
(1.1) is vacuous and every bounded harmonic function qualifies; never used there. -/
def dirichletSolution (Ω : Set ExtPlane) (f : ExtPlane → ℝ) (z : ExtPlane) : ℝ :=
  sSup {r : ℝ | ∃ u : ExtPlane → ℝ, IsBoundedDirichletSolution Ω f u ∧ u z = r}

/-- Helper (Ch. II §1, ℂ̄ infrastructure). The inversion `ζ ↦ a + 1/ζ` (`0 ↦ ∞`) is continuous from `ℂ` to `ℂ̄`. -/
theorem gm21_inversion_continuous (a : ℂ) :
    Continuous (fun ζ : ℂ => if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane)) := by
  rw [continuous_iff_continuousAt]
  intro ζ
  by_cases h0 : ζ = 0
  · subst h0
    show Tendsto _ (𝓝 0) (𝓝 (if (0 : ℂ) = 0 then LiZhongQC.extInf else ((a + (0 : ℂ)⁻¹ : ℂ) : ExtPlane)))
    rw [show (if (0 : ℂ) = 0 then LiZhongQC.extInf else ((a + (0 : ℂ)⁻¹ : ℂ) : ExtPlane)) = LiZhongQC.extInf by simp, ← nhdsNE_sup_pure (0 : ℂ)]
    refine Tendsto.sup ?_ (tendsto_pure_left.2 fun s hs => ?_)
    · have h1 : Tendsto (fun ζ : ℂ => a + ζ⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
        rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
        have h2 : Tendsto (fun ζ : ℂ => ‖ζ⁻¹‖) (𝓝[≠] 0) atTop := tendsto_norm_inv_nhdsNE_zero_atTop
        refine tendsto_atTop_mono' _ ?_ (h2.atTop_add (tendsto_const_nhds (x := -‖a‖)))
        filter_upwards with ζ
        have h := norm_sub_norm_le ζ⁻¹ (-a)
        rw [norm_neg, sub_neg_eq_add, add_comm] at h
        show ‖ζ⁻¹‖ + -‖a‖ ≤ ‖a + ζ⁻¹‖
        linarith
      have h3 := (OnePoint.tendsto_coe_infty (X := ℂ)).comp h1
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      have hζ' : ζ ≠ 0 := hζ
      simp [hζ']
    · simp at hs ⊢
      exact mem_of_mem_nhds hs
  · have : (fun ζ : ℂ => if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane)) =ᶠ[𝓝 ζ]
        fun ζ => ((a + ζ⁻¹ : ℂ) : ExtPlane) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds h0] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      simp [hy]
    refine ContinuousAt.congr ?_ this.symm
    exact OnePoint.continuous_coe.continuousAt.comp ((continuousAt_const.add (continuousAt_id.inv₀ h0)))

/-- Helper (Ch. II §1, ℂ̄ infrastructure). `z ↦ 1/(z − a)` (`∞ ↦ 0`) is a left inverse of the inversion
`ζ ↦ a + 1/ζ`. -/
theorem gm21_inversion_left (a ζ : ℂ) :
    OnePoint.elim (if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane)) 0 (fun y : ℂ => (y - a)⁻¹) = ζ := by
  by_cases h : ζ = 0
  · subst h; simp [LiZhongQC.extInf]
  · simp [h]

/-- Helper (Ch. II §1, ℂ̄ infrastructure). `z ↦ 1/(z − a)` is a right inverse of the inversion `ζ ↦ a + 1/ζ` off the
point `a`. -/
theorem gm21_inversion_right (a : ℂ) {x : ExtPlane} (hx : x ≠ (a : ExtPlane)) :
    (if OnePoint.elim x 0 (fun y : ℂ => (y - a)⁻¹) = 0 then LiZhongQC.extInf
      else ((a + (OnePoint.elim x 0 (fun y : ℂ => (y - a)⁻¹))⁻¹ : ℂ) : ExtPlane)) = x := by
  induction x using OnePoint.rec with
  | infty => simp [LiZhongQC.extInf]
  | coe y =>
    have hya : y - a ≠ 0 := sub_ne_zero.2 fun h => hx (by rw [h])
    simp [hya]

/-- Helper (Ch. II §1, ℂ̄ infrastructure). `z ↦ 1/(z − a)` (`∞ ↦ 0`) is continuous on `ℂ̄ ∖ {a}`. -/
theorem gm21_inversion_inv_continuousOn (a : ℂ) :
    ContinuousOn (fun x : ExtPlane => OnePoint.elim x 0 (fun y : ℂ => (y - a)⁻¹)) {x | x ≠ (a : ExtPlane)} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty']
    have h1 : Tendsto (fun y : ℂ => y - a) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight a).isClosedEmbedding.tendsto_cocompact
    have h2 : Tendsto (fun y : ℂ => (y - a)⁻¹) (coclosedCompact ℂ) (𝓝 0) := by
      rw [coclosedCompact_eq_cocompact]
      exact tendsto_inv₀_cobounded.comp (by rwa [cobounded_eq_cocompact])
    exact h2
  | coe y =>
    rw [OnePoint.continuousAt_coe]
    have hya : y - a ≠ 0 := sub_ne_zero.2 fun h => hx (by rw [h])
    exact ((continuousAt_id.sub continuousAt_const).inv₀ hya)

/-- Helper (Ch. II §1, ℂ̄ infrastructure). Harmonicity is invariant under holomorphic changes of variable: if `u` is
harmonic at `f x` and `f` is holomorphic at `x`, then `u ∘ f` is harmonic at `x` (locally `u = Re F` with `F`
holomorphic). -/
theorem gm21_harmonicAt_comp_analyticAt {u : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hu : InnerProductSpace.HarmonicAt u (f x)) (hf : AnalyticAt ℂ f x) :
    InnerProductSpace.HarmonicAt (fun y => u (f y)) x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := u)) (f x) hu
  obtain ⟨F, hFa, hFre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (f := u) (z := f x) (R := r) (fun y hy => hball hy)
  have hfc : ContinuousAt f x := hf.continuousAt
  have hev : ∀ᶠ y in 𝓝 x, f y ∈ Metric.ball (f x) r := hfc.eventually (Metric.ball_mem_nhds _ hr)
  have hFf : AnalyticAt ℂ (fun y => F (f y)) x :=
    (hFa (f x) (Metric.mem_ball_self hr)).comp hf
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 hFf.harmonicAt_re
  filter_upwards [hev] with y hy
  exact hFre hy

/-- Helper (Ch. II §1, ℂ̄ infrastructure). Transfer of harmonicity through the inversion `ζ ↦ a + 1/ζ` (`0 ↦ ∞`): if `u`
is harmonic on `Ω ⊆ ℂ̄` in the sense of `HarmonicOnExt`, then `ζ ↦ u (a + 1/ζ)` is harmonic at every point `ζ` of the
plane with `a + 1/ζ ∈ Ω` (at `ζ = 0` this is the chart of `ℂ̄` at `∞`). -/
theorem gm21_harmonicOnNhd_inversion {u : ExtPlane → ℝ} {Ω : Set ExtPlane}
    (hu : HarmonicOnExt u Ω) (a : ℂ) :
    InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => u (if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane)))
      {ζ : ℂ | (if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane)) ∈ Ω} := by
  intro ζ₀ hζ₀
  by_cases h0 : ζ₀ = 0
  · -- the chart of `ℂ̄` at `∞`, composed with `ζ ↦ ζ / (1 + a ζ)`
    subst h0
    have hinf : LiZhongQC.extInf ∈ Ω := by simpa using hζ₀
    have hch := hu _ hinf
    have hη : AnalyticAt ℂ (fun ζ : ℂ => ζ / (1 + a * ζ)) 0 := by
      refine analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) ?_
      simp
    have hc := gm21_harmonicAt_comp_analyticAt (u := u ∘ LehtoVirtanen1973.extChartInv LiZhongQC.extInf)
      (f := fun ζ : ℂ => ζ / (1 + a * ζ)) (x := 0) (by simpa using hch) hη
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 hc
    have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), 1 + a * ζ ≠ 0 := by
      refine ContinuousAt.eventually_ne (by fun_prop) ?_
      simp
    filter_upwards [hev] with ζ hζ
    by_cases hz : ζ = 0
    · subst hz
      simp [LehtoVirtanen1973.extChartInv]
    · have hη' : ζ / (1 + a * ζ) ≠ 0 := div_ne_zero hz hζ
      simp only [Function.comp_apply, LehtoVirtanen1973.extChartInv, OnePoint.elim_infty, hη', hz, ite_false]
      congr 2
      field_simp
      ring
  · -- a finite point: translate the chart and compose with `ζ ↦ a + 1/ζ`
    have hmem : ((a + ζ₀⁻¹ : ℂ) : LiZhongQC.ExtPlane) ∈ Ω := by simpa [h0] using hζ₀
    have hch := hu _ hmem
    have hfin : InnerProductSpace.HarmonicAt (fun y : ℂ => u (y : LiZhongQC.ExtPlane)) (a + ζ₀⁻¹) := by
      have h1 : InnerProductSpace.HarmonicAt (fun ζ : ℂ => u ((a + ζ₀⁻¹ + ζ : ℂ) : LiZhongQC.ExtPlane)) 0 := hch
      have h2 := gm21_harmonicAt_comp_analyticAt (u := fun ζ : ℂ => u ((a + ζ₀⁻¹ + ζ : ℂ) : LiZhongQC.ExtPlane))
        (f := fun y : ℂ => y - (a + ζ₀⁻¹)) (x := a + ζ₀⁻¹) (by simpa using h1)
        (analyticAt_id.sub analyticAt_const)
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h2
      exact Filter.Eventually.of_forall fun y => by simp
    have hg : AnalyticAt ℂ (fun ζ : ℂ => a + ζ⁻¹) ζ₀ :=
      analyticAt_const.add (analyticAt_id.inv h0)
    have hc := gm21_harmonicAt_comp_analyticAt (u := fun y : ℂ => u (y : LiZhongQC.ExtPlane))
      (f := fun ζ : ℂ => a + ζ⁻¹) (x := ζ₀) hfin hg
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 hc
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with ζ hζ
    simp only [mem_compl_iff, mem_singleton_iff] at hζ
    simp [hζ]

/-- Helper (Ch. II §1, ℂ̄ infrastructure). **Maximum principle on `ℂ̄`.** Let `Ω` be a domain of `ℂ̄` with a finite
point `a ∉ Ω̄` (so `Ω` may contain `∞`), and `u` harmonic on `Ω` (`HarmonicOnExt`) with limit `0` at every boundary point.
Then `u = 0` on `Ω` (the inversion `z ↦ 1/(z − a)` makes `Ω` bounded; the plane maximum principle
`eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier` applies). -/
theorem gm21_eqOn_zero_of_tendsto_frontier {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) {a : ℂ}
    (ha : (a : ExtPlane) ∉ closure Ω) {u : ExtPlane → ℝ} (hu : HarmonicOnExt u Ω)
    (hbd : ∀ ζ ∈ frontier Ω, Tendsto u (𝓝[Ω] ζ) (𝓝 0)) : ∀ z ∈ Ω, u z = 0 := by
  obtain ⟨hΩo, hΩc⟩ := hΩ
  set φ : ℂ → ExtPlane := fun ζ => if ζ = 0 then LiZhongQC.extInf else ((a + ζ⁻¹ : ℂ) : ExtPlane) with hφdef
  set T : ExtPlane → ℂ := fun x => OnePoint.elim x 0 (fun y : ℂ => (y - a)⁻¹) with hTdef
  have hφc : Continuous φ := gm21_inversion_continuous a
  set V : Set ℂ := φ ⁻¹' Ω with hVdef
  have hVo : IsOpen V := hΩo.preimage hφc
  have hna : ∀ x ∈ Ω, x ≠ (a : ExtPlane) := fun x hx h => ha (h ▸ subset_closure hx)
  -- `V` is the image of `Ω` under `T`
  have hTV : T '' Ω = V := by
    ext ζ
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ (T x) ∈ Ω
      rw [show φ (T x) = x from gm21_inversion_right a (hna x hx)]
      exact hx
    · intro hζ
      refine ⟨φ ζ, hζ, ?_⟩
      exact gm21_inversion_left a ζ
  have hTc : ContinuousOn T Ω := (gm21_inversion_inv_continuousOn a).mono fun x hx => hna x hx
  have hVc : IsPreconnected V := by
    rw [← hTV]
    exact hΩc.isPreconnected.image T hTc
  -- `V` is bounded
  have hVb : Bornology.IsBounded V := by
    have hcl : (closure Ω)ᶜ ∈ 𝓝 (a : ExtPlane) := isClosed_closure.isOpen_compl.mem_nhds ha
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
      (OnePoint.continuous_coe.continuousAt.preimage_mem_nhds (x := a) hcl)
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / r)).subset fun ζ hζ => ?_
    rw [mem_closedBall_zero_iff]
    by_cases h0 : ζ = 0
    · rw [h0, norm_zero]; positivity
    · have hmem : ((a + ζ⁻¹ : ℂ) : ExtPlane) ∈ Ω := by
        have hζ' : φ ζ ∈ Ω := hζ
        simpa [hφdef, h0] using hζ'
      by_contra hlt
      push Not at hlt
      have : a + ζ⁻¹ ∈ Metric.ball a r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv]
        have hpos : 0 < ‖ζ‖ := norm_pos_iff.2 h0
        rw [inv_lt_comm₀ hpos hr]
        simpa [one_div] using hlt
      exact hball this (subset_closure hmem)
  have hv := gm21_harmonicOnNhd_inversion hu a
  have hfront : ∀ ζ ∈ frontier V, Tendsto (fun ζ => u (φ ζ)) (𝓝[V] ζ) (𝓝 0) := by
    intro ζ₀ hζ₀
    have hfr : φ ζ₀ ∈ frontier Ω := hφc.frontier_preimage_subset Ω hζ₀
    have h1 := hbd _ hfr
    have h2 : Tendsto φ (𝓝[V] ζ₀) (𝓝[Ω] φ ζ₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hφc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun ζ hζ => hζ⟩
    exact h1.comp h2
  have hzero := LiZhongQC.eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier hVo hVb hVc hv hfront
  intro z hz
  have hzV : T z ∈ V := hTV ▸ mem_image_of_mem T hz
  have h1 : u (φ (T z)) = 0 := hzero (T z) hzV
  have hφT : φ (T z) = z := gm21_inversion_right a (hna z hz)
  rw [hφT] at h1
  exact h1

/-- Helper (Ch. II §1, ℂ̄ infrastructure). **A Jordan domain of `ℂ̄` misses a finite point of its closure** (sphere
Jordan curve theorem, corollary): `Ω` is a complementary component of its boundary curve, and the other component
contains a finite point. -/
theorem gm21_exists_finite_not_mem_closure {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) :
    ∃ a : ℂ, (a : ExtPlane) ∉ closure Ω := by
  obtain ⟨⟨hΩo, hΩc⟩, hJ⟩ := hΩ
  -- a finite point `q` of `Ω`
  obtain ⟨q, hq⟩ : ∃ q : ℂ, (q : ExtPlane) ∈ Ω := by
    obtain ⟨x, hx⟩ := hΩc.nonempty
    exact OnePoint.denseRange_coe.exists_mem_open hΩo ⟨x, hx⟩
  set J : Set ExtPlane := frontier Ω with hJdef
  set φ : ℂ → ExtPlane := fun ζ => if ζ = 0 then LiZhongQC.extInf else ((q + ζ⁻¹ : ℂ) : ExtPlane) with hφdef
  set T : ExtPlane → ℂ := fun x => OnePoint.elim x 0 (fun y : ℂ => (y - q)⁻¹) with hTdef
  have hφc : Continuous φ := gm21_inversion_continuous q
  have hTc : ContinuousOn T {x | x ≠ (q : ExtPlane)} := gm21_inversion_inv_continuousOn q
  have hL : ∀ ζ, T (φ ζ) = ζ := fun ζ => gm21_inversion_left q ζ
  have hR : ∀ x, x ≠ (q : ExtPlane) → φ (T x) = x := fun x hx => gm21_inversion_right q hx
  have hφne : ∀ ζ, φ ζ ≠ (q : ExtPlane) := by
    intro ζ h
    by_cases h0 : ζ = 0
    · simp [hφdef, h0, LiZhongQC.extInf] at h
    · simp only [hφdef, h0, ite_false] at h
      have := OnePoint.coe_injective h
      exact inv_ne_zero h0 (by simpa using this)
  have hqJ : (q : ExtPlane) ∉ J := by
    rw [hJdef, hΩo.frontier_eq]
    exact fun h => h.2 hq
  have hJne : ∀ x ∈ J, x ≠ (q : ExtPlane) := fun x hx h => hqJ (h ▸ hx)
  obtain ⟨γ, hγc, hγi, hγr⟩ := hJ
  have hγq : ∀ s, γ s ≠ (q : ExtPlane) := fun s => hJne _ (hγr ▸ mem_range_self s)
  have hTγ : Continuous fun s => T (γ s) := hTc.comp_continuous hγc hγq
  set C : Set ℂ := T '' J with hCdef
  have hCJ : LiZhongQC.IsJordanCurve (LiZhongQC.toExt C) := by
    refine ⟨fun s => ((T (γ s) : ℂ) : ExtPlane), OnePoint.continuous_coe.comp hTγ, ?_, ?_⟩
    · intro s t h
      have h1 : T (γ s) = T (γ t) := OnePoint.coe_injective h
      apply hγi
      rw [← hR _ (hγq s), ← hR _ (hγq t), h1]
    · ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨T (γ s), ⟨γ s, hγr ▸ mem_range_self s, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        rw [← hγr] at hj
        obtain ⟨s, rfl⟩ := hj
        exact ⟨s, rfl⟩
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩ :=
    LiZhongQC.jordan_curve_theorem_complex_bounded hCJ
  have hCb : Bornology.IsBounded C := by
    have : C = Set.range fun s => T (γ s) := by
      rw [hCdef, ← hγr]; exact (Set.range_comp T γ).symm
    rw [this]
    exact (isCompact_range hTγ).isBounded
  obtain ⟨R, hR1, hRB⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ ζ : ℂ, R < ‖ζ‖ → ζ ∈ B := by
    obtain ⟨R0, hR0⟩ := hCb.subset_closedBall (0 : ℂ)
    obtain ⟨R1, hR1⟩ := hAb.subset_closedBall (0 : ℂ)
    refine ⟨max (max R0 R1) 1 + 1, by linarith [le_max_right (max R0 R1) 1], fun ζ hζ => ?_⟩
    have hζ0 : ζ ∉ C := fun h => by
      have := mem_closedBall_zero_iff.1 (hR0 h)
      linarith [le_max_left R0 R1, le_max_left (max R0 R1) 1]
    have hζ1 : ζ ∉ A := fun h => by
      have := mem_closedBall_zero_iff.1 (hR1 h)
      linarith [le_max_right R0 R1, le_max_left (max R0 R1) 1]
    have : ζ ∈ A ∪ B ∪ C := huniv ▸ mem_univ ζ
    rcases this with (h | h) | h
    · exact absurd h hζ1
    · exact h
    · exact absurd h hζ0
  have hφopen : ∀ S : Set ℂ, IsOpen S → IsOpen (φ '' S) := by
    intro S hS
    have : φ '' S = {x | x ≠ (q : ExtPlane)} ∩ T ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨ζ, hζ, rfl⟩
        exact ⟨hφne ζ, by simpa [hL] using hζ⟩
      · rintro ⟨hx, hTx⟩
        exact ⟨T x, hTx, hR x hx⟩
    rw [this]
    exact hTc.isOpen_inter_preimage isOpen_compl_singleton hS
  set UA : Set ExtPlane := φ '' A with hUA
  set UB : Set ExtPlane := φ '' B ∪ {(q : ExtPlane)} with hUB
  have hUAo : IsOpen UA := hφopen A hAo
  have hUBo : IsOpen UB := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hx with hx | hx
    · exact Filter.mem_of_superset ((hφopen B hBo).mem_nhds hx) (subset_union_left)
    · rw [mem_singleton_iff] at hx
      subst hx
      have hN : IsOpen (((↑) : ℂ → ExtPlane) '' Metric.ball q (1 / R)) :=
        OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
      refine Filter.mem_of_superset (hN.mem_nhds ⟨q, Metric.mem_ball_self (by positivity), rfl⟩) ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyq : y = q
      · rw [hyq]; exact Or.inr rfl
      · left
        have hyq' : y - q ≠ 0 := sub_ne_zero.2 hyq
        have hpos : 0 < ‖y - q‖ := norm_pos_iff.2 hyq'
        have hyd : ‖y - q‖ < 1 / R := by simpa [dist_eq_norm] using hy
        refine ⟨(y - q)⁻¹, hRB _ ?_, ?_⟩
        · rw [norm_inv]
          rw [lt_inv_comm₀ (by linarith) hpos]
          simpa [one_div] using hyd
        · simp [hφdef, hyq']
  -- the complement of the curve is covered by `UA` and `UB`
  have hcover : ∀ x, x ∉ J → x ∈ UA ∪ UB := by
    intro x hx
    by_cases hxq : x = (q : ExtPlane)
    · exact Or.inr (Or.inr hxq)
    · have hTxC : T x ∉ C := by
        rintro ⟨j, hj, hjx⟩
        apply hx
        have := hR j (hJne j hj)
        rw [hjx, hR x hxq] at this
        exact this ▸ hj
      have : T x ∈ A ∪ B ∪ C := huniv ▸ mem_univ _
      rcases this with (h | h) | h
      · exact Or.inl ⟨T x, h, hR x hxq⟩
      · exact Or.inr (Or.inl ⟨T x, h, hR x hxq⟩)
      · exact absurd h hTxC
  have hdisj : Disjoint UA UB := by
    rw [Set.disjoint_left]
    rintro _ ⟨ζ, hζ, rfl⟩ (⟨η, hη, hηζ⟩ | h)
    · have : η = ζ := by rw [← hL η, hηζ, hL ζ]
      exact Set.disjoint_left.1 hAB hζ (this ▸ hη)
    · exact hφne ζ h
  have hΩJ : ∀ x ∈ Ω, x ∉ J := by
    intro x hx hxJ
    rw [hJdef, hΩo.frontier_eq] at hxJ
    exact hxJ.2 hx
  have hΩsub : Ω ⊆ UB := by
    have := hΩc.isPreconnected.subset_right_of_subset_union hUAo hUBo hdisj
      (fun x hx => hcover x (hΩJ x hx)) ⟨(q : ExtPlane), hq, Or.inr rfl⟩
    exact this
  -- a finite point of `UA`
  obtain ⟨ζ, hζA, hζ0⟩ : ∃ ζ ∈ A, ζ ≠ 0 := by
    obtain ⟨ζ₀, hζ₀⟩ := hAc.nonempty
    obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hAo ζ₀ hζ₀
    by_cases h0 : ζ₀ = 0
    · refine ⟨(r / 2 : ℝ), hrA ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, h0, sub_zero, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · exact_mod_cast (by positivity : (r / 2 : ℝ) ≠ 0)
    · exact ⟨ζ₀, hζ₀, h0⟩
  refine ⟨q + ζ⁻¹, fun hcl => ?_⟩
  have hmemA : ((q + ζ⁻¹ : ℂ) : ExtPlane) ∈ UA := ⟨ζ, hζA, by simp [hφdef, hζ0]⟩
  have hcl' : ((q + ζ⁻¹ : ℂ) : ExtPlane) ∈ Ω ∨ ((q + ζ⁻¹ : ℂ) : ExtPlane) ∈ J := by
    by_cases hx : ((q + ζ⁻¹ : ℂ) : ExtPlane) ∈ Ω
    · exact Or.inl hx
    · exact Or.inr (by rw [hJdef, hΩo.frontier_eq]; exact ⟨hcl, hx⟩)
  rcases hcl' with h | h
  · exact Set.disjoint_left.1 hdisj hmemA (hΩsub h)
  · apply Set.disjoint_left.1 hAC hζA
    refine ⟨((q + ζ⁻¹ : ℂ) : ExtPlane), h, ?_⟩
    have : φ ζ = ((q + ζ⁻¹ : ℂ) : ExtPlane) := by simp [hφdef, hζ0]
    rw [← this, hL]

/-- **Theorem 1.1** (Ch. II §1). Let `Ω` be a finitely connected Jordan domain, and let `f` be a bounded piecewise
continuous function on `∂Ω`. Then there is a unique function `u(z) = u_f(z)`, bounded and harmonic on `Ω`, such that
(1.1) `lim_{z→ζ} u(z) = f(ζ)` at every point of continuity `ζ` of `f`. Moreover, `sup_Ω |u| ≤ sup_{∂Ω} |f|`.
Modelling: uniqueness is on `Ω`; the bound `sup_Ω |u| ≤ sup_{∂Ω} |f|` is written "every bound `M` of `|f|` on `∂Ω`
bounds `|u|` on `Ω`". -/
theorem thm2_1_1 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {f : ExtPlane → ℝ}
    (hf : IsPiecewiseContinuousOn Ω f) :
    ∃ u : ExtPlane → ℝ, IsBoundedDirichletSolution Ω f u ∧
      (∀ v : ExtPlane → ℝ, IsBoundedDirichletSolution Ω f v → EqOn v u Ω) ∧
      ∀ M : ℝ, (∀ ζ ∈ frontier Ω, |f ζ| ≤ M) → ∀ z ∈ Ω, |u z| ≤ M := by
  sorry

/-- **Definition** (the set function `ω(z, E, Ω)`, Ch. II §1, P1:1856–1866). For a relatively open subset
`U ⊆ ∂Ω`, `ω(z, U) = sup {u_f(z) : f ∈ C(∂Ω), 0 ≤ f ≤ χ_U}`, and for an arbitrary subset `E` of `∂Ω`,
`ω(z, E) = inf {ω(z, U) : U open in ∂Ω, U ⊇ E}`.
Modelling: one formula for both steps (for relatively open `E` the infimum is attained at `U = E`, since `ω(z, U)`
increases with `U`); values in `[0, ∞]`; `f ∈ C(∂Ω)` is a real function on `ℂ*` continuous on `∂Ω`, and
`0 ≤ f ≤ χ_U` is required on `∂Ω`. Junk: `⊤` for `E ⊄ ∂Ω` (no relatively open `U ⊇ E`); never used there. -/
def harmonicMeasureFCSet (Ω : Set ExtPlane) (z : ExtPlane) (E : Set ExtPlane) : ℝ≥0∞ :=
  ⨅ (U : Set ExtPlane) (_ : (∃ V : Set ExtPlane, IsOpen V ∧ U = V ∩ frontier Ω) ∧ E ⊆ U),
    ⨆ (f : ExtPlane → ℝ)
      (_ : ContinuousOn f (frontier Ω) ∧ ∀ ζ ∈ frontier Ω, 0 ≤ f ζ ∧ f ζ ≤ U.indicator (fun _ => (1 : ℝ)) ζ),
      ENNReal.ofReal (dirichletSolution Ω f z)

/-- **Definition** (harmonic measure `ω(z, ·, Ω)` of a finitely connected Jordan domain, Ch. II §1, P1:1856–1872). The
Borel measure on `∂Ω` whose values on the Borel sets `E ⊆ ∂Ω` are those of the set function `harmonicMeasureFCSet`
("this procedure, which mimics the usual proof of the Riesz representation theorem, shows `ω(z, E)` is a Borel
measure on `∂Ω`", `eq2_1_2`).
Modelling (leader ruling D1): a measure on `ℂ*` carried by `∂Ω`, written as the supremum of the set of Borel measures
that vanish off `∂Ω` and agree with the set function on the Borel subsets of `∂Ω`; that set has at most one element
(two such measures agree on every Borel set), and exactly one for `z ∈ Ω` by `eq2_1_2`. Junk: the zero measure when
no measure agrees with the set function; never used there. -/
def harmonicMeasureFC (Ω : Set ExtPlane) (z : ExtPlane) : Measure ExtPlane :=
  sSup {μ : Measure ExtPlane | μ (frontier Ω)ᶜ = 0 ∧
    ∀ E : Set ExtPlane, MeasurableSet E → E ⊆ frontier Ω → μ E = harmonicMeasureFCSet Ω z E}

/-- **Formula (1.2)** (Ch. II §1, P1:1868–1872; cited at P1:2174, 2226). Let `Ω` be a finitely connected Jordan
domain and `z ∈ Ω`. Then `ω(z, E)` is a Borel measure on `∂Ω` such that (1.2) `u_f(z) = ∫_{∂Ω} f(ζ) dω(z, ζ)` for
continuous `f`.
Modelling: the measure `harmonicMeasureFC Ω z` vanishes off `∂Ω` and has the values of the set function on the Borel
subsets of `∂Ω`; `f` is continuous on `∂Ω`. -/
theorem eq2_1_2 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {z : ExtPlane} (hz : z ∈ Ω) :
    harmonicMeasureFC Ω z (frontier Ω)ᶜ = 0 ∧
      (∀ E : Set ExtPlane, MeasurableSet E → E ⊆ frontier Ω →
        harmonicMeasureFC Ω z E = harmonicMeasureFCSet Ω z E) ∧
      ∀ f : ExtPlane → ℝ, ContinuousOn f (frontier Ω) →
        dirichletSolution Ω f z = ∫ ζ in frontier Ω, f ζ ∂(harmonicMeasureFC Ω z) := by
  sorry

/-- **Unlabelled** (Ch. II §1, P1:1874; the identification of the two definitions, used in substance at P1:4098).
When `Ω` is simply connected, this definition of harmonic measure agrees with the earlier definition (I.3.3).
Modelling: a simply connected finitely connected Jordan domain is a Jordan domain of `ℂ*` (`p = 1`), so the hypothesis
is `IsJordanDomainExt Ω`; the two measures on `ℂ*` are equal. -/
theorem harmonicMeasureFC_eq_jordan {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {z : ExtPlane} (hz : z ∈ Ω) :
    harmonicMeasureFC Ω z = harmonicMeasureJordan Ω z := by
  sorry

/-- **Formula (1.3)** (Ch. II §1, P1:1876–1882; cited at P1:1900, 1906). For every `z₁, z₂ ∈ Ω` there exists a
constant `c = c(z₁, z₂)` such that (1.3) `(1/c) ω(z₁, E) ≤ ω(z₂, E) ≤ c ω(z₁, E)`, and the constants `c(z₁, z₂)`
remain uniformly bounded if `z₁` and `z₂` remain in a compact subset of `Ω`.
Modelling: one statement for both claims: for every compact `K ⊆ Ω` there is one `c > 0` for all `z₁, z₂ ∈ K` (the
pointwise claim is the case `K = {z₁, z₂}`); `E` is any subset of `∂Ω` (the measures' outer values, which are the
book's infima over relatively open supersets); the ratio is multiplied out and compared in `[0, ∞]`. -/
theorem eq2_1_3 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {K : Set ExtPlane} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ z₁ ∈ K, ∀ z₂ ∈ K, ∀ E ⊆ frontier Ω,
      (c : ℝ≥0∞)⁻¹ * harmonicMeasureFC Ω z₁ E ≤ harmonicMeasureFC Ω z₂ E ∧
        harmonicMeasureFC Ω z₂ E ≤ c * harmonicMeasureFC Ω z₁ E := by
  sorry

/-- **Definition** ((1.4), the solution to the Dirichlet problem for `f ∈ L¹(∂Ω, dω)`, Ch. II §1, P1:1896–1906).
`u(z) = u_f(z) = ∫ f(ζ) dω(z, ζ)`.
Modelling: a separate name from `dirichletSolution` (Theorem 1.1's `u_f`), with which it agrees for continuous `f` by
(1.2). Junk: `0` when `f` is not integrable for `ω(z, ·)` (every statement assumes integrability). -/
def dirichletSolutionL1 (Ω : Set ExtPlane) (f : ExtPlane → ℝ) (z : ExtPlane) : ℝ :=
  ∫ ζ, f ζ ∂(harmonicMeasureFC Ω z)

/-- **Formula (1.4)** (Ch. II §1, P1:1882–1910; "the discussion following (1.4)" is cited at P1:2220). If
`f ∈ L¹(∂Ω, dω)`, and in particular if `f` is bounded and Borel, then `u(z) = u_f(z) = ∫ f(ζ) dω(z, ζ)` (1.4) is
harmonic on `Ω` (the solution to the Dirichlet problem for `f` on `Ω`). If `f` is bounded, then
`sup_{z∈Ω} |u_f(z)| ≤ ‖f‖_{L^∞(dω)}`.
Modelling: `L¹(∂Ω, dω)` and `L^∞(dω)` are taken with respect to `ω(z₀, ·)` for a fixed `z₀ ∈ Ω` (the book's
"for some fixed `z₀ ∈ Ω`"; by (1.3) the choice does not matter); "bounded" is bounded on `∂Ω`. -/
theorem eq2_1_4 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) {f : ExtPlane → ℝ}
    (hf : Integrable f (harmonicMeasureFC Ω z₀)) :
    HarmonicOnExt (dirichletSolutionL1 Ω f) Ω ∧
      ((∃ M : ℝ, ∀ ζ ∈ frontier Ω, |f ζ| ≤ M) →
        ∀ z ∈ Ω, ‖dirichletSolutionL1 Ω f z‖ₑ ≤ eLpNorm f ⊤ (harmonicMeasureFC Ω z₀)) := by
  sorry

end GarnettMarshall2005
