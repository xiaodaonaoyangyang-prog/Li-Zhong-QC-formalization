import References.LehtoVirtanen1973.Ch01.S02_ConformalMappings
import LiZhongQC.Ch01.S07_GeometricDefinition

/-!
# Lehto–Virtanen, Chapter I §3: Definition of a quasiconformal mapping

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §3
(pp. 16–19; `full.md` P1:369–468).

Quasiconformal mappings are sense-preserving homeomorphisms between domains of `ℂ̄` (the geometric definition of
Pfluger and Ahlfors); the dilatations are `ℝ≥0∞`-valued, since they may be infinite.

* Definition (dilatation of a quadrilateral under `w`; maximal dilatation `K(G)`, §3.1; also for open sets, §8.3) —
  `quadDilatation`, `maxDilatationK`
* Definition (quasiconformal, `K`-quasiconformal mapping; the Definition of §3.2) — `IsKQuasiconformal`,
  `IsQuasiconformalMap`
* Definition (anti-quasiconformal mapping, §3.2) — `IsAntiQuasiconformalMap`
* Unlabelled (§3.1–3.2, P1:381, 391): a conformal mapping is `1`-quasiconformal — moved to Ch01/S05, after the
  converse bridge (conformal_isKQuasiconformal_one)
* Unlabelled (§3.2, P1:397): the inverse of a `K`-quasiconformal mapping is `K`-quasiconformal; composition —
  moved to Ch01/S05, after the converse bridge (kqc_inv, kqc_comp)
* Definition (directional derivative `∂_α w`, dilatation quotient `D` (3.1); regular and regular `K`-quasiconformal
  mappings (Grötzsch), extended to `ℂ̄` by auxiliary linear transformations, §3.3) — `dirDeriv`, `dilQuotient`,
  `dilQuot`, `IsRegularKQuasiconformal`, `IsRegularQuasiconformal`
* Unlabelled (§3.3, P1:423): composition of regular quasiconformal mappings, `D₃(z) ≤ D₁(w₂(z)) D₂(z)` —
  `dilQuot_comp_le`
* Theorem 3.1 (Grötzsch's inequality, §3.4) — `thm1_3_1`
* Unlabelled (§3.4, P1:467, Remark): quadrilaterals with `M(Q′) = K M(Q)` admit a homeomorphism which is
  `K`-quasiconformal in the interior — `exists_kqc_quadHomeo_of_module_eq`

The claim of the remark closing §3.4 is stated because Ch. II cites it (P1:2092, 2443, 3177); its affine
sub-claim and the immediate `K(G) ≥ 1` (P1:379) are not stated (inventory: omitted). Not stated either (U−): P1:421
(for a conformal map `∂_α w` does not depend on `α` and `D = 1`) and P1:463 (the forward reference to Theorem 9.3).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §3.1 Dilatation of a quadrilateral under a homeomorphism -/

/-- **Definition** (dilatation of a quadrilateral, Ch. I §3.1). For a sense-preserving homeomorphism `w`, the
quadrilateral `Q` is mapped onto a quadrilateral `Q′ = w(Q)` with vertices `w(zᵢ)`; the ratio `M(Q′)/M(Q)` is called
the dilatation of `Q` under `w`. Junk: for a sense-reversing homeomorphism the image vertices are in the negative
order and `quadModule` of the image data is `0`; every statement assumes sense-preservation. -/
def quadDilatation (w : ExtPlane → ExtPlane) (Q : Quadrilateral) : ℝ :=
  quadModule (w '' Q.dom) (w ∘ Q.vert) / Q.module

/-- **Definition** (maximal dilatation, Ch. I §3.1; for open sets §8.3). `K(G) = sup_{Q̄ ⊂ G} M(Q′)/M(Q)`, the
supremum of the dilatations of the quadrilaterals `Q` with `Q̄ ⊂ G`.
Modelling: `ℝ≥0∞`-valued. The value is only meaningful for sense-preserving `w`, as in the book; for a
sense-reversing homeomorphism every dilatation has the junk value `0` (see `quadDilatation`), and every statement
assumes sense-preservation. -/
def maxDilatationK (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (Q : Quadrilateral) (_ : closure Q.dom ⊆ G), ENNReal.ofReal (quadDilatation w Q)

/-! ## §3.2 Quasiconformal mapping -/

/-- **Definition** (Ch. I §3.2). A sense-preserving homeomorphism `w` of the domain `G` is `K`-quasiconformal if its
maximal dilatation satisfies `K(G) ≤ K`. -/
def IsKQuasiconformal (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (K : ℝ) : Prop :=
  IsDomainExt G ∧ IsSensePreservingOn w G ∧ maxDilatationK w G ≤ ENNReal.ofReal K

/-- **Definition** (Ch. I §3.2). A sense-preserving homeomorphism `w` of the domain `G` is quasiconformal if its
maximal dilatation `K(G)` is finite. -/
def IsQuasiconformalMap (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  IsDomainExt G ∧ IsSensePreservingOn w G ∧ maxDilatationK w G < ⊤

/-- **Definition** (anti-quasiconformal mapping, Ch. I §3.2): a quasiconformal mapping followed by a reflection.
Modelling: the reflection is taken to be `z ↦ z̄` (on `ℂ̄`); every reflection in a circle is `z ↦ z̄` followed by a
linear transformation, which is conformal, and a reflection is an involution, so `w` is anti-quasiconformal iff
`z̄ ∘ w` is quasiconformal. -/
def IsAntiQuasiconformalMap (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  IsQuasiconformalMap (OnePoint.map (starRingEnd ℂ) ∘ w) G

/-! ## §3.3 Regular quasiconformal mappings -/

/-- **Definition** (directional derivative, Ch. I §3.3). `∂_α w(z) = lim_{r → 0} (w(z + r e^{iα}) - w(z))/(r e^{iα})`.
Modelling: the book uses `∂_α w` only at points where `w` is differentiable, where the limit is
`w′(z)(e^{iα}) e^{-iα}` (`fderiv`). -/
def dirDeriv (f : ℂ → ℂ) (z : ℂ) (α : ℝ) : ℂ := fderiv ℝ f z (exp (α * I)) * exp (-(α * I))

/-- **Definition** (dilatation quotient (3.1), Ch. I §3.3): `D(z) = max_α |∂_α w(z)| / min_α |∂_α w(z)|`, for a
finite function. Used by the book only at regular points, where the minimum is positive. -/
def dilQuotient (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (⨆ α : ℝ, ‖dirDeriv f z α‖) / ⨅ α : ℝ, ‖dirDeriv f z α‖

/-- **Definition** (dilatation quotient at any point of `ℂ̄`, Ch. I §3.3 and §9.4): `D(z)` of the local representation
of `w` at `z`. At a finite point with a finite value this is the book's `D(z)`; at `z = ∞` or where `w(z) = ∞` it is
the book's definition "by means of an auxiliary linear transformation" (the charts `ζ ↦ 1/ζ`, `D` being conformally
invariant). -/
def dilQuot (w : ExtPlane → ExtPlane) (z : ExtPlane) : ℝ := dilQuotient (localRep w z) 0

/-- **Definition** (regular `K`-quasiconformal mapping, Ch. I §3.3). A sense-preserving homeomorphism `w` of the
domain `G` which is regular at every point of `G` with continuous partial derivatives (in the charts at `∞` and at
the poles, as the book extends the definition to arbitrary domains), and whose dilatation quotient satisfies
`sup_{z ∈ G} D(z) ≤ K`. -/
def IsRegularKQuasiconformal (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (K : ℝ) : Prop :=
  IsDomainExt G ∧ IsSensePreservingOn w G ∧
    (∀ z ∈ G, IsRegularPointOf w G z ∧ ∃ U ∈ 𝓝 (0 : ℂ), ContDiffOn ℝ 1 (localRep w z) U) ∧
      ∀ z ∈ G, dilQuot w z ≤ K

/-- **Definition** (regular quasiconformal mapping, Ch. I §3.3): the dilatation quotient is bounded in `G`. -/
def IsRegularQuasiconformal (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  ∃ K : ℝ, IsRegularKQuasiconformal w G K

/-- **Unlabelled** (Ch. I §3.3, P1:423). The composition `w₃ = w₁ ∘ w₂` of two regular quasiconformal mappings is
regular quasiconformal and `D₃(z) ≤ D₁(w₂(z)) D₂(z)`; equality holds when `w₁` or `w₂` is conformal (then
`D₃(z) = D₂(z)`, resp. `D₃(z) = D₁(w₂(z))`). -/
theorem dilQuot_comp_le {w₁ w₂ : ExtPlane → ExtPlane} {G : Set ExtPlane} (h₂ : IsRegularQuasiconformal w₂ G)
    (h₁ : IsRegularQuasiconformal w₁ (w₂ '' G)) :
    IsRegularQuasiconformal (w₁ ∘ w₂) G ∧ (∀ z ∈ G, dilQuot (w₁ ∘ w₂) z ≤ dilQuot w₁ (w₂ z) * dilQuot w₂ z) ∧
      (IsConformalMap w₁ (w₂ '' G) → ∀ z ∈ G, dilQuot (w₁ ∘ w₂) z = dilQuot w₂ z) ∧
      (IsConformalMap w₂ G → ∀ z ∈ G, dilQuot (w₁ ∘ w₂) z = dilQuot w₁ (w₂ z)) := by
  sorry

/-! ## §3.4 Grötzsch's inequality -/

/-- **Theorem 3.1** (Ch. I §3.4, Grötzsch). Between the maximal dilatation and the dilatation quotient of a regular
quasiconformal mapping we have the inequality `K(G) ≤ sup_{z ∈ G} D(z)` (3.2). -/
theorem thm1_3_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsRegularQuasiconformal w G) :
    maxDilatationK w G ≤ ⨆ z ∈ G, ENNReal.ofReal (dilQuot w z) := by
  sorry

/-- **Unlabelled** (Ch. I §3.4, P1:467, Remark). For every pair of quadrilaterals `Q` and `Q′` with
`M(Q′) = K M(Q)` (`K ≥ 1`) there exists a homeomorphism of `Q` onto `Q′` which is `K`-quasiconformal in the interior
of `Q`. (The book obtains it from the affine map `x + iy ↦ Kx + iy` between the canonical rectangles; cited in
Ch. II.) -/
theorem exists_kqc_quadHomeo_of_module_eq (Q Q' : Quadrilateral) {K : ℝ} (hK : 1 ≤ K)
    (h : Q'.module = K * Q.module) :
    ∃ w : ExtPlane → ExtPlane, IsQuadHomeo w Q Q' ∧ IsKQuasiconformal w Q.dom K := by
  sorry

/-! ## Bridge to Li Zhong's `IsKQC`, stage 1: orientation (prefix `lv13_`)

The forward bridge `IsKQuasiconformal ⇒ LiZhongQC.IsKQC` needs LV's orientation (positive boundary parametrizations,
§1.4) to agree with Li Zhong's (boundary values of a conformal map onto `ℍ` in cyclic order). Stage 1 proves the two
reusable facts: an LV-positive parametrization winds once around the interior
(`lv13_winding_of_isPositiveBoundaryParam`), and the canonical parametrization through a conformal map onto `ℍ` is
LV-positive and meets the boundary in the order of the real coordinates (`lv13_canonical_param`,
`lv13_isPositivelyOrdered_of_isTopQuad`). Windings are changes of continuous logarithms over `[0, 1]`, as in
`LiZhongQC.lift_change_eq_of_homotopy`. -/

/-- Helper (bridge, stage 1). The winding of a closed curve `g` around `z` (the change over `[0, 1]` of a continuous
logarithm of `g − z`) is the same for all points `z` of a preconnected set avoiding the curve: it is locally constant
(`LiZhongQC.lift_change_eq_of_norm_sub_lt`). -/
theorem lv13_lift_change_const {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1)) (hg1 : g 1 = g 0) {S : Set ℂ}
    (hS : IsPreconnected S) (hSg : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ z) {z z' : ℂ} (hz : z ∈ S) (hz' : z' ∈ S)
    {L L' : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1)) (hL' : ContinuousOn L' (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = g t - z) (hL'e : ∀ t ∈ Icc (0 : ℝ) 1, exp (L' t) = g t - z') :
    L 1 - L 0 = L' 1 - L' 0 := by
  -- the winding of a point off the compact curve `C` is a locally constant function on `Cᶜ`
  set C : Set ℂ := g '' Icc 0 1 with hCdef
  have hlift : ∀ w : ℂ, w ∉ C → ∃ M : ℝ → ℂ, ContinuousOn M (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, exp (M t) = g t - w := fun w hw =>
    LiZhongQC.exists_continuousOn_log_lift hg fun t ht h => hw ⟨t, ht, h⟩
  let n : ↥Cᶜ → ℂ := fun w => (hlift w w.2).choose 1 - (hlift w w.2).choose 0
  have hn : ∀ (w : ↥Cᶜ) (M : ℝ → ℂ), ContinuousOn M (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, exp (M t) = g t - w) → M 1 - M 0 = n w := fun w M hM hMe =>
    LiZhongQC.lift_change_eq_of_lifts hM (hlift w w.2).choose_spec.1 hMe (hlift w w.2).choose_spec.2
  have hloc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    -- `δ = dist(w, C) > 0`
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
      ((hg.sub continuousOn_const).norm (f := fun t => g t - (w : ℂ)))
    have hδ : 0 < ‖g t₀ - (w : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => w.2 ⟨t₀, ht₀, h⟩)
    have hball : ∀ᶠ w' : ↥Cᶜ in 𝓝 w, (w' : ℂ) ∈ Metric.ball (w : ℂ) ‖g t₀ - (w : ℂ)‖ :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hball] with w' hw'
    obtain ⟨M', hM', hM'e⟩ := hlift w' w'.2
    obtain ⟨M, hM, hMe⟩ := hlift w w.2
    rw [← hn w' M' hM' hM'e, ← hn w M hM hMe]
    refine LiZhongQC.lift_change_eq_of_norm_sub_lt (γ := fun t => g t - w') (β := fun t => g t - w)
      (hg.sub continuousOn_const) (hg.sub continuousOn_const) (by simp only [hg1]) (by simp only [hg1])
      (fun t ht => ?_) hM' hM hM'e hMe
    have e : g t - (w' : ℂ) - (g t - w) = (w : ℂ) - w' := by ring
    rw [e, ← dist_eq_norm, dist_comm]
    exact lt_of_lt_of_le (Metric.mem_ball.1 hw') (hmin ht)
  -- `S` is a preconnected subset of `Cᶜ`
  have hSC : S ⊆ Cᶜ := by
    rintro w hw ⟨t, ht, h⟩
    exact hSg w hw t ht h
  have hpre : IsPreconnected ((↑) ⁻¹' S : Set ↥Cᶜ) := by
    have h := (Topology.IsInducing.subtypeVal (t := Cᶜ)).isPreconnected_image (s := (↑) ⁻¹' S)
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hSC] at h
    exact h.1 hS
  have heq := hloc.apply_eq_of_isPreconnected hpre (x := ⟨z, hSC hz⟩) (y := ⟨z', hSC hz'⟩) hz hz'
  rw [hn ⟨z, hSC hz⟩ L hL hLe, hn ⟨z', hSC hz'⟩ L' hL' hL'e]
  exact heq

/-- Helper (bridge, stage 1). A closed curve has winding `0` around the points of an unbounded preconnected set
avoiding it (far away, `g − z` stays in a half-plane, where the principal logarithm is a lift). -/
theorem lv13_lift_change_eq_zero {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1)) (hg1 : g 1 = g 0) {S : Set ℂ}
    (hS : IsPreconnected S) (hSb : ¬ Bornology.IsBounded S) (hSg : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ z)
    {z : ℂ} (hz : z ∈ S) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = g t - z) :
    L 1 - L 0 = 0 := by
  -- a point `z'` of `S` far from the curve
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨z', hz'S, hz'R⟩ : ∃ z' ∈ S, 2 * R + 1 < ‖z'‖ := by
    by_contra h
    push Not at h
    exact hSb (isBounded_iff_forall_norm_le.2 ⟨2 * R + 1, fun x hx => h x hx⟩)
  have hz'0 : z' ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz'R
    linarith
  -- there `(g − z')/(−z')` stays in the right half-plane: the principal logarithm is a lift
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, (g t - z') / (-z') ∈ slitPlane := fun t ht => by
    have e : (g t - z') / (-z') = 1 - g t / z' := by
      field_simp
      ring
    rw [e]
    left
    have h1 : ‖g t / z'‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one (norm_pos_iff.2 hz'0)).2 (by linarith [hR t ht])
    have h2 := Complex.re_le_norm (g t / z')
    simp only [sub_re, one_re]
    linarith
  have hM : ContinuousOn (fun t => log (-z') + log ((g t - z') / (-z'))) (Icc 0 1) :=
    continuousOn_const.add (((hg.sub continuousOn_const).div_const _).clog hslit)
  have hMe : ∀ t ∈ Icc (0 : ℝ) 1, exp (log (-z') + log ((g t - z') / (-z'))) = g t - z' := fun t ht => by
    rw [exp_add, exp_log (neg_ne_zero.2 hz'0), exp_log (slitPlane_ne_zero (hslit t ht))]
    field_simp
  rw [lv13_lift_change_const hg hg1 hS hSg hz hz'S hL hM hLe hMe, hg1, sub_self]

/-- Helper (bridge, stage 1; B4). An LV-positive parametrization of the boundary of a bounded Jordan domain `U` winds
once around every point of `U`, whatever the admissible Möbius transformation `t` of `IsPositiveBoundaryParam`: with
`t(ζ) = c (ζ − ζ₀)/(ζ − ζ_p)`, `ζ₀ = t⁻¹(0) ∈ U` and the pole `ζ_p ∉ Ū` (winding `0`, `lv13_lift_change_eq_zero` on
the connected unbounded exterior), so the winding around `ζ₀`, hence around every `z ∈ U`
(`lv13_lift_change_const`), is `1`. The book's remark that the choice of `t` does not matter is not needed. -/
theorem lv13_winding_of_isPositiveBoundaryParam {U : Set ℂ} (hU : LiZhongQC.IsJordanDomain U)
    (hb : Bornology.IsBounded U) {γ : ℝ → ExtPlane} (hγ : IsPositiveBoundaryParam (toExt U) γ) {z : ℂ}
    (hz : z ∈ U) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = finiteValue (γ t) - z) :
    L 1 - L 0 = 2 * Real.pi * I := by
  obtain ⟨⟨hγc, hγp, -, hγr⟩, t, ⟨a, b, c, d, hdet, rfl⟩, U', hU', hU'b, hU'0, Lt, hLtc, hLte, hLt1⟩ := hγ
  obtain ⟨hUo, hUc, hUJ⟩ := hU
  -- the curve is finite: `γ s = g s` with `g s ∈ ∂U`
  have hfr : frontier (toExt U) = toExt (frontier U) := LiZhongQC.frontier_toExt_of_isBounded hb hUo
  have hγfin : ∀ s, γ s = ((finiteValue (γ s) : ℂ) : ExtPlane) ∧ finiteValue (γ s) ∈ frontier U := fun s => by
    have hs : γ s ∈ frontier (toExt U) := hγr ▸ mem_range_self s
    rw [hfr] at hs
    obtain ⟨w, hw, hws⟩ := hs
    rw [← hws]
    exact ⟨rfl, hw⟩
  set g : ℝ → ℂ := fun s => finiteValue (γ s) with hgdef
  have hg : Continuous g := by
    have e : ((↑) : ℂ → ExtPlane) ∘ g = γ := funext fun s => ((hγfin s).1).symm
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuous_iff, e]
    exact hγc
  have hg1 : g 1 = g 0 := by
    show finiteValue (γ 1) = finiteValue (γ 0)
    rw [show (1 : ℝ) = 0 + 1 by norm_num, hγp 0]
  have hgU : ∀ s, g s ∈ closure U := fun s => frontier_subset_closure (hγfin s).2
  have hgnot : ∀ s, g s ∉ U := fun s h => by
    have := (hγfin s).2
    rw [hUo.frontier_eq] at this
    exact this.2 h
  -- the values of `t ∘ γ`
  have hval : ∀ s, c * g s + d ≠ 0 ∧ (a * g s + b) / (c * g s + d) = exp (Lt s) := fun s => by
    have h := hLte s
    rw [(hγfin s).1] at h
    by_cases h0 : c * g s + d = 0
    · rw [LiZhongQC.mobiusExt_coe_of_eq_zero h0] at h
      exact absurd h (OnePoint.infty_ne_coe _)
    · rw [LiZhongQC.mobiusExt_coe h0] at h
      exact ⟨h0, OnePoint.coe_injective h⟩
  -- the point `ζ₀ ∈ U` sent to `0`, with `a ζ₀ + b = 0`, `a ≠ 0`
  obtain ⟨ζ₀, hζ₀U, hζ₀⟩ : ∃ ζ₀ ∈ U, LiZhongQC.mobiusExt a b c d (ζ₀ : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    have h0 : ((0 : ℂ) : ExtPlane) ∈ LiZhongQC.mobiusExt a b c d '' toExt U := by
      rw [hU']
      exact ⟨0, hU'0, rfl⟩
    obtain ⟨_, ⟨ζ, hζ, rfl⟩, hζ0⟩ := h0
    exact ⟨ζ, hζ, hζ0⟩
  have hab : a * ζ₀ + b = 0 := by
    by_cases h0 : c * ζ₀ + d = 0
    · rw [LiZhongQC.mobiusExt_coe_of_eq_zero h0] at hζ₀
      exact absurd hζ₀ (OnePoint.infty_ne_coe _)
    · rw [LiZhongQC.mobiusExt_coe h0] at hζ₀
      have h1 := OnePoint.coe_injective hζ₀
      rw [LiZhongQC.mobiusFn, div_eq_zero_iff] at h1
      exact h1.resolve_right h0
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, zero_add] at hab
    apply hdet
    rw [ha0, hab]
    ring
  -- a lift of `g − ζ₀` with change `2πi`
  obtain ⟨N, hN, hNe, hN1⟩ : ∃ N : ℝ → ℂ, ContinuousOn N (Icc 0 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, exp (N s) = g s - ζ₀) ∧ N 1 - N 0 = 2 * Real.pi * I := by
    by_cases hc : c = 0
    · -- `t` is affine: `g − ζ₀ = (d/a) e^{L}`
      have hd : d ≠ 0 := by
        intro hd0
        apply hdet
        rw [hc, hd0]
        ring
      refine ⟨fun s => Lt s + log (d / a), hLtc.continuousOn.add continuousOn_const, fun s _ => ?_, ?_⟩
      · obtain ⟨-, hv⟩ := hval s
        rw [hc, zero_mul, zero_add] at hv
        rw [exp_add, exp_log (div_ne_zero hd ha), ← hv]
        field_simp
        linear_combination hab
      · simp only
        rw [← hLt1]
        ring
    · -- the pole `ζ_p = −d/c` lies outside `Ū`; the winding around it is `0`
      obtain ⟨ζp, hζpdef⟩ : ∃ ζp : ℂ, ζp = -d / c := ⟨_, rfl⟩
      have hpole : ζp ∉ closure U := by
        intro hp
        have hinf : LiZhongQC.mobiusExt a b c d (ζp : ExtPlane) = extInf :=
          LiZhongQC.mobiusExt_coe_of_eq_zero (by rw [hζpdef]; field_simp; ring)
        have hmem : (ζp : ExtPlane) ∈ closure (toExt U) := by
          rw [LiZhongQC.closure_toExt_of_isBounded hb]
          exact ⟨ζp, hp, rfl⟩
        have himg := image_closure_subset_closure_image (LiZhongQC.continuous_mobiusExt hdet)
          (mem_image_of_mem _ hmem)
        rw [hinf, hU', LiZhongQC.closure_toExt_of_isBounded hU'b] at himg
        obtain ⟨_, -, h⟩ := himg
        exact OnePoint.coe_ne_infty _ h
      have hgp : ∀ s, g s ≠ ζp := fun s h => hpole (h ▸ hgU s)
      obtain ⟨Mp, hMp, hMpe⟩ := LiZhongQC.exists_continuousOn_log_lift hg.continuousOn
        (fun s _ => hgp s)
      have hJ : LiZhongQC.IsJordanCurve (toExt (frontier U)) := hfr ▸ hUJ
      obtain ⟨hext, hextb⟩ := LiZhongQC.isConnected_compl_closure_of_isJordanCurve_frontier hUo hUc hb hJ
      have hMp1 : Mp 1 - Mp 0 = 0 :=
        lv13_lift_change_eq_zero hg.continuousOn hg1 hext.isPreconnected hextb
          (fun w hw s _ h => hw (h ▸ hgU s)) hpole hMp hMpe
      refine ⟨fun s => Lt s + Mp s + log (c / a), (hLtc.continuousOn.add hMp).add continuousOn_const,
        fun s hs => ?_, ?_⟩
      · obtain ⟨hden, hv⟩ := hval s
        rw [exp_add, exp_add, exp_log (div_ne_zero hc ha), hMpe s hs, ← hv]
        have hc' : c * g s + d = c * (g s - ζp) := by
          rw [hζpdef]
          field_simp
          ring
        have hgp' : g s - ζp ≠ 0 := sub_ne_zero.2 (hgp s)
        have e1 : (a * g s + b) / (c * (g s - ζp)) * (g s - ζp) * (c / a) = (a * g s + b) / a := by
          field_simp
        rw [hc', e1]
        field_simp
        linear_combination hab
      · simp only
        linear_combination hLt1 + hMp1
  -- constancy of the winding over `U`
  rw [lv13_lift_change_const hg.continuousOn hg1 hUc.isPreconnected (fun w hw s _ h => hgnot s (h ▸ hw)) hz hζ₀U
    hL hN hLe hNe, hN1]

/-- Helper (bridge, stage 1). The Möbius map `M(ζ) = (a ζ + p)/(1 − ζ)`, `a = i Im p − Re p` (that is,
`M(ζ) = Re p + Im p · i(1 + ζ)/(1 − ζ)`), has `Im M(ζ) = Im p (1 − |ζ|²)/|1 − ζ|²` off `ζ = 1`. -/
theorem lv13_cayley_im (p ζ : ℂ) :
    (((I * p.im - p.re) * ζ + p) / (-1 * ζ + 1)).im = p.im * (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  have e : -1 * ζ + 1 = 1 - ζ := by ring
  rw [e, Complex.div_im]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.normSq_apply]
  ring

/-- Helper (bridge, stage 1). The point `e^{2πiσ(x)}`, `σ(x) = 1/2 + arctan((x − Re p)/Im p)/π`, of the unit circle is
sent by the Möbius map `M` of `lv13_cayley_im` to the real number `x`: with `u = (x − Re p)/Im p`,
`e^{2πiσ} = −(1 + iu)/(1 − iu)`, so `1 − ζ = 2/(1 − iu)` and `M(ζ) = Re p + u Im p = x`. -/
theorem lv13_cayley_sigma {p : ℂ} (hp : 0 < p.im) (x : ℝ) :
    LiZhongQC.mobiusExt (I * p.im - p.re) p (-1) 1
        ((exp (2 * Real.pi * I * ((1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi : ℝ) : ℂ)) : ℂ) : ExtPlane) =
      ((x : ℂ) : ExtPlane) := by
  obtain ⟨x0, y0, rfl⟩ : ∃ x0 y0 : ℝ, p = x0 + y0 * I := ⟨p.re, p.im, (Complex.re_add_im p).symm⟩
  have hre : ((x0 : ℂ) + y0 * I).re = x0 := by simp
  have him : ((x0 : ℂ) + y0 * I).im = y0 := by simp
  rw [him] at hp
  simp only [hre, him]
  set u : ℝ := (x - x0) / y0 with hudef
  set θ : ℝ := Real.arctan u with hθdef
  have hsq : 0 < 1 + u ^ 2 := by positivity
  have hs : Real.sqrt (1 + u ^ 2) ≠ 0 := (Real.sqrt_pos.2 hsq).ne'
  have hss : (Real.sqrt (1 + u ^ 2) : ℂ) ^ 2 = 1 + (u : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hsq.le]
    push_cast
    ring
  -- `e^{iθ} = (1 + iu)/√(1 + u²)`
  have hE : exp (θ * I) = (1 + u * I) / Real.sqrt (1 + u ^ 2) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hθdef, Real.cos_arctan, Real.sin_arctan]
    push_cast
    field_simp
  have hζ : exp (2 * Real.pi * I * ((1 / 2 + θ / Real.pi : ℝ) : ℂ)) = -(exp (θ * I)) ^ 2 := by
    have e : 2 * Real.pi * I * ((1 / 2 + θ / Real.pi : ℝ) : ℂ) = Real.pi * I + 2 * (θ * I) := by
      push_cast
      field_simp
    rw [e, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
    push_cast
    ring
  have hiu : (1 : ℂ) - u * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  set q : ℂ := (1 + u * I) / (1 - u * I) with hqdef
  have hq : q * (1 - u * I) = 1 + u * I := div_mul_cancel₀ _ hiu
  have hζ' : exp (2 * Real.pi * I * ((1 / 2 + θ / Real.pi : ℝ) : ℂ)) = -q := by
    rw [hζ, hE, div_pow, hss, hqdef]
    congr 1
    rw [div_eq_div_iff (by rw [← hss]; exact pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hs)) hiu]
    linear_combination (-(1 + (u : ℂ) * I) * (u : ℂ) ^ 2) * Complex.I_sq
  have hden : -1 * exp (2 * Real.pi * I * ((1 / 2 + θ / Real.pi : ℝ) : ℂ)) + 1 ≠ 0 := by
    rw [hζ']
    intro h
    have h2 : q * (1 - u * I) + (1 - u * I) = 0 := by
      have : q + 1 = 0 := by linear_combination h
      rw [← add_one_mul, this, zero_mul]
    rw [hq] at h2
    have := congrArg Complex.re h2
    simp at this
  rw [LiZhongQC.mobiusExt_coe hden, LiZhongQC.mobiusFn]
  congr 1
  rw [div_eq_iff hden, hζ']
  have hy0 : (y0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
  have hpu : (x : ℂ) = x0 + u * y0 := by
    rw [hudef]
    push_cast
    field_simp
    ring
  rw [hpu]
  linear_combination (-(y0 : ℂ) * I) * hq + (-(y0 : ℂ) * (q * u + u)) * Complex.I_sq

/-- Helper (bridge, stage 1). A closed curve with a continuous logarithm over `[0, 1]` of winding `1` has a continuous
logarithm on all of `ℝ`: extend by `L(s) = f(fract s) + 2πis`, `f(t) = L₀(t) − 2πit` (`ContinuousOn.comp_fract''`). -/
theorem lv13_lift_extend {h : ℝ → ℂ} {z : ℂ} (hper : Function.Periodic h 1) {L₀ : ℝ → ℂ}
    (hL₀ : ContinuousOn L₀ (Icc 0 1)) (hL₀e : ∀ t ∈ Icc (0 : ℝ) 1, exp (L₀ t) = h t - z)
    (hL₀1 : L₀ 1 - L₀ 0 = 2 * Real.pi * I) :
    ∃ L : ℝ → ℂ, Continuous L ∧ (∀ s, exp (L s) = h s - z) ∧ L 1 - L 0 = 2 * Real.pi * I := by
  set f : ℝ → ℂ := fun t => L₀ t - 2 * Real.pi * I * t with hfdef
  have hf : ContinuousOn f (Icc 0 1) := hL₀.sub (continuousOn_const.mul Complex.continuous_ofReal.continuousOn)
  have hf01 : f 0 = f 1 := by
    simp only [hfdef]
    push_cast
    linear_combination -hL₀1
  refine ⟨fun s => f (Int.fract s) + 2 * Real.pi * I * s,
    ((hf.comp_fract'' hf01).add (continuous_const.mul Complex.continuous_ofReal)), fun s => ?_, ?_⟩
  · have hfr : Int.fract s ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
    have hhs : h (Int.fract s) = h s := by
      rw [show Int.fract s = s - (⌊s⌋ : ℤ) * (1 : ℝ) by rw [Int.fract]; ring]
      exact hper.sub_int_mul_eq ⌊s⌋
    simp only [hfdef]
    have hfs : ((Int.fract s : ℝ) : ℂ) = (s : ℂ) - ((⌊s⌋ : ℤ) : ℂ) := by
      rw [Int.fract]
      push_cast
      ring
    rw [show L₀ (Int.fract s) - 2 * Real.pi * I * ((Int.fract s : ℝ) : ℂ) + 2 * Real.pi * I * s =
      L₀ (Int.fract s) + (⌊s⌋ : ℤ) * (2 * Real.pi * I) by rw [hfs]; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one, hL₀e _ hfr, hhs]
  · simp only [Int.fract_one, Int.fract_zero]
    push_cast
    ring

/-- Helper (bridge, stage 1; B2). The canonical parametrization of the boundary of a bounded Jordan domain `U` with a
conformal map `φ` onto `ℍ` and its homeomorphic extension `Φ`: `c(s) = Φ⁻¹(M(e^{2πis}))`, `M` the Möbius map of the
unit disc onto `ℍ` with `M(0) = φ(z₁)`. It is LV-positive (with `t` the translation by `−z₁`; winding `1` by the
radial homotopy to a small circle, where `Φ⁻¹ ∘ M` is conformal), it meets `Φ⁻¹(∞)` at `0`, and it meets `Φ⁻¹(x)`
(`x ∈ ℝ`) at a parameter `σ(x) ∈ (0, 1)` increasing in `x`. -/
theorem lv13_canonical_param {U : Set ℂ} (hU : LiZhongQC.IsJordanDomain U) (hb : Bornology.IsBounded U)
    {φ : ℂ → ℂ} {Φ : ExtPlane → ExtPlane} (hφ : LiZhongQC.IsConformalOnto φ U LiZhongQC.upperHalf)
    (hΦ : LiZhongQC.IsHomeoExtension φ U LiZhongQC.upperHalf Φ) :
    ∃ c : ℝ → ExtPlane, IsPositiveBoundaryParam (toExt U) c ∧ Φ (c 0) = extInf ∧
      ∃ σ : ℝ → ℝ, StrictMono σ ∧ (∀ x, σ x ∈ Ioo (0 : ℝ) 1) ∧ ∀ x : ℝ, Φ (c (σ x)) = ((x : ℂ) : ExtPlane) := by
  obtain ⟨hUo, hUc, -⟩ := hU
  obtain ⟨z₁, hz₁⟩ := hUc.nonempty
  have hpH' : φ z₁ ∈ LiZhongQC.upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hz₁
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ, p = φ z₁ := ⟨_, rfl⟩
  have hpH : p ∈ LiZhongQC.upperHalf := hpdef ▸ hpH'
  have hp : 0 < p.im := hpH
  -- the Möbius map `M` of the closed unit disc onto `ℍ̄`, `M(0) = p`
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = I * p.im - p.re := ⟨_, rfl⟩
  have hdet : a * 1 - p * (-1) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    rw [hadef] at h'
    simp at h'
    linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ExtPlane → ExtPlane, M = LiZhongQC.mobiusExt a p (-1) 1 := ⟨_, rfl⟩
  have hMinj : Function.Injective M := fun x y hxy => by
    have h := congrArg (LiZhongQC.mobiusExt 1 (-p) (-(-1)) a) hxy
    rwa [hMdef, LiZhongQC.mobiusExt_inv_apply hdet, LiZhongQC.mobiusExt_inv_apply hdet] at h
  have hMcont : Continuous M := hMdef ▸ LiZhongQC.continuous_mobiusExt hdet
  have hden_ne : ∀ ζ : ℂ, ζ ≠ 1 → -1 * ζ + 1 ≠ 0 := fun ζ h h0 => h (by linear_combination -h0)
  have hM_coe : ∀ ζ : ℂ, ζ ≠ 1 → M ζ = (((a * ζ + p) / (-1 * ζ + 1) : ℂ) : ExtPlane) := fun ζ h => by
    rw [hMdef, LiZhongQC.mobiusExt_coe (hden_ne ζ h)]
    rfl
  have him : ∀ ζ : ℂ, ((a * ζ + p) / (-1 * ζ + 1)).im =
      p.im * (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := fun ζ => by
    rw [hadef]
    exact lv13_cayley_im p ζ
  have hne1 : ∀ ζ : ℂ, ‖ζ‖ < 1 → ζ ≠ 1 := fun ζ hζ h => by
    rw [h, norm_one] at hζ
    exact lt_irrefl _ hζ
  have hM_in : ∀ ζ : ℂ, ‖ζ‖ < 1 → (a * ζ + p) / (-1 * ζ + 1) ∈ LiZhongQC.upperHalf := fun ζ hζ => by
    show 0 < ((a * ζ + p) / (-1 * ζ + 1)).im
    rw [him ζ]
    have hn : Complex.normSq ζ < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ζ]
    have hd : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.2 (sub_ne_zero.2 (Ne.symm (hne1 ζ hζ)))
    exact div_pos (mul_pos hp (by linarith)) hd
  have hM_fr : ∀ ζ : ℂ, ‖ζ‖ = 1 → M ζ ∈ frontier (toExt LiZhongQC.upperHalf) := fun ζ hζ => by
    rw [← LiZhongQC.range_realToExtPlane]
    by_cases h1 : ζ = 1
    · refine ⟨OnePoint.infty, ?_⟩
      rw [LiZhongQC.realToExtPlane_infty, h1, hMdef, LiZhongQC.mobiusExt_coe_of_eq_zero (by ring)]
    · refine ⟨((((a * ζ + p) / (-1 * ζ + 1)).re : ℝ) : OnePoint ℝ), ?_⟩
      rw [LiZhongQC.realToExtPlane_coe, hM_coe ζ h1]
      congr 1
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im, him ζ, Complex.normSq_eq_norm_sq ζ, hζ]
        simp
  have hM_cl : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → M ζ ∈ closure (toExt LiZhongQC.upperHalf) := fun ζ hζ => by
    rcases hζ.lt_or_eq with h | h
    · rw [hM_coe ζ (hne1 ζ h)]
      exact subset_closure ⟨_, hM_in ζ h, rfl⟩
    · exact frontier_subset_closure (hM_fr ζ h)
  have hinf_cl : extInf ∈ closure (toExt LiZhongQC.upperHalf) := by
    refine frontier_subset_closure ?_
    rw [← LiZhongQC.range_realToExtPlane]
    exact ⟨OnePoint.infty, LiZhongQC.realToExtPlane_infty⟩
  have hreal_cl : ∀ x : ℝ, ((x : ℂ) : ExtPlane) ∈ closure (toExt LiZhongQC.upperHalf) := fun x => by
    refine frontier_subset_closure ?_
    rw [← LiZhongQC.range_realToExtPlane]
    exact ⟨(x : OnePoint ℝ), LiZhongQC.realToExtPlane_coe x⟩
  -- the inverse boundary extension `Φ⁻¹`
  obtain ⟨hinv1, hinvc, hinvi, hinvimg⟩ := LiZhongQC.isHomeoExtension_invFunOn hφ hΦ
  obtain ⟨Φinv, hΦinvdef⟩ : ∃ Φinv : ExtPlane → ExtPlane, Φinv = Function.invFunOn Φ (closure (toExt U)) :=
    ⟨_, rfl⟩
  rw [← hΦinvdef] at hinv1 hinvc hinvi hinvimg
  have hφinv := hφ.symm hUo
  have hclU : closure (toExt U) = toExt (closure U) := LiZhongQC.closure_toExt_of_isBounded hb
  have hΦΦinv : ∀ y ∈ closure (toExt LiZhongQC.upperHalf), Φ (Φinv y) = y := fun y hy => by
    rw [hΦinvdef]
    rw [← hΦ.2.2.2] at hy
    exact Function.invFunOn_eq hy
  -- `ψ = Φ⁻¹ ∘ M` on the closed unit disc, with finite values
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = fun ζ : ℂ => finiteValue (Φinv (M (ζ : ExtPlane))) := ⟨_, rfl⟩
  have hψfin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → Φinv (M ζ) = ((ψ ζ : ℂ) : ExtPlane) ∧ ψ ζ ∈ closure U := fun ζ hζ => by
    have hmem : Φinv (M ζ) ∈ closure (toExt U) := by
      rw [← hinvimg]
      exact mem_image_of_mem _ (hM_cl ζ hζ)
    rw [hclU] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    rw [hψdef]
    show Φinv (M ζ) = ((finiteValue (Φinv (M ζ)) : ℂ) : ExtPlane) ∧ finiteValue (Φinv (M ζ)) ∈ closure U
    rw [← hwe]
    exact ⟨rfl, hw⟩
  have hball1 : ∀ ζ : ℂ, ζ ∈ Metric.closedBall (0 : ℂ) 1 → ‖ζ‖ ≤ 1 := fun ζ h => by simpa using h
  have hψc : ContinuousOn ψ (Metric.closedBall 0 1) := by
    have hc : ContinuousOn (fun ζ : ℂ => Φinv (M ζ)) (Metric.closedBall 0 1) :=
      hinvc.comp (hMcont.comp OnePoint.continuous_coe).continuousOn fun ζ hζ => hM_cl ζ (hball1 ζ hζ)
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuousOn_iff]
    exact hc.congr fun ζ hζ => (hψfin ζ (hball1 ζ hζ)).1.symm
  have hψi : InjOn ψ (Metric.closedBall 0 1) := fun ζ hζ ζ' hζ' h => by
    have h1 : Φinv (M ζ) = Φinv (M ζ') := by
      rw [(hψfin ζ (hball1 ζ hζ)).1, (hψfin ζ' (hball1 ζ' hζ')).1, h]
    exact OnePoint.coe_injective (hMinj (hinvi (hM_cl ζ (hball1 ζ hζ)) (hM_cl ζ' (hball1 ζ' hζ')) h1))
  have hM0 : M ((0 : ℂ) : ExtPlane) = (p : ExtPlane) := by
    rw [hM_coe 0 zero_ne_one]
    congr 1
    simp
  have hψ0 : ψ 0 = z₁ := by
    have h := (hψfin 0 (by simp)).1
    rw [hM0, hinv1 p hpH, hpdef, hφ.2.1.leftInvOn_invFunOn hz₁] at h
    exact (OnePoint.coe_injective h).symm
  -- on the open disc `ψ` is the conformal map `A = φ⁻¹ ∘ M`; its local winding at `0` is `1`
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℂ, A = fun ζ => Function.invFunOn φ U ((a * ζ + p) / (-1 * ζ + 1)) := ⟨_, rfl⟩
  have hAψ : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, A ζ = ψ ζ := fun ζ hζ => by
    have hζ' : ‖ζ‖ < 1 := by simpa using hζ
    have h := (hψfin ζ hζ'.le).1
    rw [hM_coe ζ (hne1 ζ hζ'), hinv1 _ (hM_in ζ hζ')] at h
    rw [hAdef]
    exact OnePoint.coe_injective h
  have hAd : DifferentiableOn ℂ A (Metric.ball 0 1) := by
    rw [hAdef]
    refine hφinv.1.comp (DifferentiableOn.div (by fun_prop) (by fun_prop) fun ζ hζ => hden_ne ζ
      (hne1 ζ (by simpa using hζ))) fun ζ hζ => hM_in ζ (by simpa using hζ)
  have hAi : InjOn A (Metric.ball 0 1) :=
    (hψi.mono Metric.ball_subset_closedBall).congr fun ζ hζ => (hAψ ζ hζ).symm
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hA' : deriv A 0 ≠ 0 := LiZhongQC.deriv_ne_zero_of_injOn Metric.isOpen_ball hAd hAi h0ball
  have hAdiff : DifferentiableAt ℂ A 0 := hAd.differentiableAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hJ : 0 < LiZhongQC.jacobian A 0 := by
    rw [LiZhongQC.jacobian, LiZhongQC.dz_eq_deriv hAdiff, (LiZhongQC.cauchyRiemann_iff.1 hAdiff).2, norm_zero]
    have := norm_pos_iff.2 hA'
    nlinarith
  obtain ⟨ρ₁, hρ₁, hloc⟩ := LiZhongQC.lift_change_circle_eq_two_pi_I_of_jacobian_pos
    (hAdiff.restrictScalars ℝ) hJ
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ℝ, ρ₀ = min (ρ₁ / 2) (1 / 2) := ⟨_, rfl⟩
  have hρ₀ : 0 < ρ₀ := by rw [hρ₀def]; exact lt_min (by linarith) (by norm_num)
  have hρ₀1 : ρ₀ < ρ₁ := by rw [hρ₀def]; linarith [min_le_left (ρ₁ / 2) (1 / 2)]
  have hρ₀h : ρ₀ < 1 := by rw [hρ₀def]; linarith [min_le_right (ρ₁ / 2) (1 / 2)]
  -- the circle parameter `e(t) = e^{2πit}`
  obtain ⟨e, hedef⟩ : ∃ e : ℝ → ℂ, e = fun t : ℝ => exp (2 * Real.pi * I * (t : ℂ)) := ⟨_, rfl⟩
  have hecont : Continuous e := by
    rw [hedef]
    fun_prop
  have hen : ∀ t, ‖e t‖ = 1 := fun t => by
    rw [hedef, Complex.norm_exp]
    simp
  have heper : Function.Periodic e 1 := fun t => by
    rw [hedef]
    simp only
    rw [show 2 * Real.pi * I * ((t + 1 : ℝ) : ℂ) = 2 * Real.pi * I * t + 2 * Real.pi * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have he1 : e 1 = e 0 := by rw [← zero_add (1 : ℝ), heper 0]
  -- the radial homotopy from the small circle of radius `ρ₀` to the unit circle
  have hrad : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ t, ‖(((ρ₀ + (1 - ρ₀) * σ : ℝ) : ℂ) * e t)‖ = ρ₀ + (1 - ρ₀) * σ := by
    intro σ hσ t
    rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [hσ.1])]
  have hradle : ∀ σ ∈ Icc (0 : ℝ) 1, ρ₀ + (1 - ρ₀) * σ ≤ 1 := fun σ hσ => by nlinarith [hσ.2]
  set H : ℝ → ℝ → ℂ := fun σ t => ψ ((((ρ₀ + (1 - ρ₀) * σ : ℝ) : ℂ)) * e t) with hHdef
  have hHc : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have hg : Continuous fun q : ℝ × ℝ => (((ρ₀ + (1 - ρ₀) * q.1 : ℝ) : ℂ)) * e q.2 := by fun_prop
    refine hψc.comp hg.continuousOn fun q hq => ?_
    rw [Metric.mem_closedBall, dist_zero_right, hrad q.1 hq.1 q.2]
    exact hradle q.1 hq.1
  have hHper : ∀ σ ∈ Icc (0 : ℝ) 1, H σ 1 = H σ 0 := fun σ _ => by
    simp only [hHdef, he1]
  have hHne : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H σ t ≠ z₁ := fun σ hσ t _ h => by
    rw [← hψ0] at h
    have hmem : (((ρ₀ + (1 - ρ₀) * σ : ℝ) : ℂ)) * e t ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hrad σ hσ t]
      exact hradle σ hσ
    have h0 := hψi hmem (Metric.mem_closedBall_self zero_le_one) h
    have := hrad σ hσ t
    rw [h0, norm_zero] at this
    nlinarith [hσ.1]
  have hH0c : ContinuousOn (fun t => H 0 t) (Icc 0 1) :=
    hHc.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht => ⟨⟨le_rfl, zero_le_one⟩, ht⟩
  have hH1c : ContinuousOn (fun t => H 1 t) (Icc 0 1) :=
    hHc.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht => ⟨⟨zero_le_one, le_rfl⟩, ht⟩
  obtain ⟨L₀, hL₀, hL₀e⟩ := LiZhongQC.exists_continuousOn_log_lift hH0c
    fun t ht => hHne 0 ⟨le_rfl, zero_le_one⟩ t ht
  obtain ⟨L₁, hL₁, hL₁e⟩ := LiZhongQC.exists_continuousOn_log_lift hH1c
    fun t ht => hHne 1 ⟨zero_le_one, le_rfl⟩ t ht
  have hL₀1 : L₀ 1 - L₀ 0 = 2 * Real.pi * I := by
    refine hloc ρ₀ hρ₀ hρ₀1 L₀ hL₀ fun t ht => ?_
    rw [hL₀e t ht]
    have hmem : ((ρ₀ : ℝ) : ℂ) * e t ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ₀]
      exact hρ₀h
    simp only [hHdef, mul_zero, add_zero, zero_add]
    rw [← hAψ _ hmem, hAdef, ← hψ0, ← hAψ 0 h0ball, hAdef, hedef]
  have hL₁1 : L₁ 1 - L₁ 0 = 2 * Real.pi * I :=
    (LiZhongQC.lift_change_eq_of_homotopy hHc hHper hHne hL₀ hL₁ hL₀e hL₁e).symm.trans hL₀1
  have hH1 : ∀ t, H 1 t = ψ (e t) := fun t => by
    simp only [hHdef, mul_one, add_sub_cancel, Complex.ofReal_one, one_mul]
  -- the parametrization `c(s) = ψ(e(s))`
  have hψe : ∀ s, Φinv (M (e s)) = ((ψ (e s) : ℂ) : ExtPlane) ∧ ψ (e s) ∈ closure U := fun s =>
    hψfin (e s) (hen s).le
  have hσmem : ∀ x : ℝ, 1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi ∈ Ioo (0 : ℝ) 1 := fun x => by
    have h1 := Real.neg_pi_div_two_lt_arctan ((x - p.re) / p.im)
    have h2 := Real.arctan_lt_pi_div_two ((x - p.re) / p.im)
    constructor
    · have : -(1 / 2) < Real.arctan ((x - p.re) / p.im) / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]
        linarith
      linarith
    · have : Real.arctan ((x - p.re) / p.im) / Real.pi < 1 / 2 := by
        rw [div_lt_iff₀ Real.pi_pos]
        linarith
      linarith
  have hc0 : Φ ((ψ (e 0) : ℂ) : ExtPlane) = extInf := by
    rw [← (hψe 0).1]
    have : M (e 0) = extInf := by
      rw [hedef, hMdef]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      exact LiZhongQC.mobiusExt_coe_of_eq_zero (by ring)
    rw [this, hΦΦinv _ hinf_cl]
  have hcσ : ∀ x : ℝ, Φ ((ψ (e (1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi)) : ℂ) : ExtPlane) =
      ((x : ℂ) : ExtPlane) := fun x => by
    rw [← (hψe _).1]
    have : M (e (1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi)) = ((x : ℂ) : ExtPlane) := by
      rw [hedef, hMdef, hadef]
      exact lv13_cayley_sigma hp x
    rw [this, hΦΦinv _ (hreal_cl x)]
  -- `Φ⁻¹` maps `∂ℍ` to `∂U` and back
  have hUo' : IsOpen (toExt U) := OnePoint.isOpen_image_coe.2 hUo
  have hHo' : IsOpen (toExt LiZhongQC.upperHalf) :=
    OnePoint.isOpen_image_coe.2 (isOpen_lt continuous_const Complex.continuous_im)
  have hrange : range (fun s => ((ψ (e s) : ℂ) : ExtPlane)) = frontier (toExt U) := by
    apply subset_antisymm
    · rintro _ ⟨s, rfl⟩
      beta_reduce
      rw [hUo'.frontier_eq]
      have hy := hM_fr (e s) (hen s)
      rw [hHo'.frontier_eq] at hy
      refine ⟨?_, fun hmem => ?_⟩
      · rw [← (hψe s).1, ← hinvimg]
        exact mem_image_of_mem _ hy.1
      · obtain ⟨z, hz, hze⟩ := hmem
        apply hy.2
        rw [← hΦΦinv _ hy.1, (hψe s).1, ← hze, hΦ.1 z hz]
        exact ⟨φ z, hφ.2.2 ▸ mem_image_of_mem φ hz, rfl⟩
    · intro q hq
      rw [hUo'.frontier_eq] at hq
      have hΦq : Φ q ∈ frontier (toExt LiZhongQC.upperHalf) := by
        rw [hHo'.frontier_eq]
        refine ⟨?_, fun hmem => ?_⟩
        · rw [← hΦ.2.2.2]
          exact mem_image_of_mem _ hq.1
        · obtain ⟨w, hw, hwe⟩ := hmem
          rw [← hφ.2.2] at hw
          obtain ⟨z, hz, rfl⟩ := hw
          apply hq.2
          have hzc : (z : ExtPlane) ∈ closure (toExt U) := subset_closure ⟨z, hz, rfl⟩
          have := hΦ.2.2.1 hzc hq.1 (by rw [hΦ.1 z hz, hwe])
          rw [← this]
          exact ⟨z, hz, rfl⟩
      rw [← LiZhongQC.range_realToExtPlane] at hΦq
      obtain ⟨y, hy⟩ := hΦq
      have hcl : ∀ s, ((ψ (e s) : ℂ) : ExtPlane) ∈ closure (toExt U) := fun s => by
        rw [hclU]
        exact ⟨_, (hψe s).2, rfl⟩
      induction y using OnePoint.rec with
      | infty =>
        refine ⟨0, hΦ.2.2.1 (hcl 0) hq.1 ?_⟩
        rw [hc0, ← hy, LiZhongQC.realToExtPlane_infty]
      | coe x =>
        refine ⟨1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi, hΦ.2.2.1 (hcl _) hq.1 ?_⟩
        rw [hcσ x, ← hy, LiZhongQC.realToExtPlane_coe]
  -- the global lift and LV positivity (`t` the translation by `−z₁`)
  obtain ⟨L, hLc, hLe, hL1⟩ := lv13_lift_extend (h := fun s => ψ (e s)) (z := z₁)
    (fun s => by simp only [heper s]) hL₁ (fun t ht => by rw [hL₁e t ht, hH1]) hL₁1
  refine ⟨fun s => ((ψ (e s) : ℂ) : ExtPlane), ⟨⟨OnePoint.continuous_coe.comp
    (hψc.comp_continuous hecont fun s => by rw [Metric.mem_closedBall, dist_zero_right]; exact (hen s).le),
    fun s => by simp only [heper s], ?_, hrange⟩, LiZhongQC.mobiusExt 1 (-z₁) 0 1,
    ⟨1, -z₁, 0, 1, by norm_num, rfl⟩, (fun z => z - z₁) '' U, ?_, ?_, ⟨z₁, hz₁, sub_self z₁⟩, L, hLc,
    fun s => ?_, hL1⟩, hc0, fun x => 1 / 2 + Real.arctan ((x - p.re) / p.im) / Real.pi, ?_, hσmem, hcσ⟩
  · -- injective on one period
    intro s hs s' hs' h
    have h1 := hψi (by rw [Metric.mem_closedBall, dist_zero_right]; exact (hen s).le)
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact (hen s').le) (OnePoint.coe_injective h)
    rw [hedef] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
    have hn' : s = s' + n := by
      have := congrArg Complex.im hn
      simp at this
      nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      have h1 : (n : ℝ) < 1 := by linarith [hs.1, hs.2, hs'.1, hs'.2]
      have h2 : (-1 : ℝ) < n := by linarith [hs.1, hs.2, hs'.1, hs'.2]
      have h3 : n < 1 := by exact_mod_cast h1
      have h4 : -1 < n := by exact_mod_cast h2
      omega
    rw [hn', hn0, Int.cast_zero, add_zero]
  · -- `t(U)` is the translate of `U`
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z - z₁, ⟨z, hz, rfl⟩, by rw [LiZhongQC.mobiusExt_coe (by simp)]; simp [LiZhongQC.mobiusFn, sub_eq_add_neg]⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨z, hz, rfl⟩, by rw [LiZhongQC.mobiusExt_coe (by simp)]; simp [LiZhongQC.mobiusFn, sub_eq_add_neg]⟩
  · obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
    refine isBounded_iff_forall_norm_le.2 ⟨R + ‖z₁‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hR z hz])
  · rw [LiZhongQC.mobiusExt_coe (by simp), hLe s]
    simp [LiZhongQC.mobiusFn, sub_eq_add_neg]
  · intro x y hxy
    have h1 : (x - p.re) / p.im < (y - p.re) / p.im := div_lt_div_of_pos_right (by linarith) hp
    have h2 := Real.arctan_strictMono h1
    have h3 : Real.arctan ((x - p.re) / p.im) / Real.pi < Real.arctan ((y - p.re) / p.im) / Real.pi :=
      div_lt_div_of_pos_right h2 Real.pi_pos
    linarith

/-- Helper (bridge, stage 1; B2). A bounded Li Zhong quadrilateral is positively ordered in LV's sense: its vertices
have cyclically increasing real coordinates, so the canonical parametrization (`lv13_canonical_param`) meets them in
order within one turn. -/
theorem lv13_isPositivelyOrdered_of_isTopQuad {D : Set ℂ} {v : Fin 4 → ExtPlane} (h : LiZhongQC.IsTopQuad D v)
    (hb : Bornology.IsBounded D) : IsPositivelyOrdered (toExt D) v := by
  obtain ⟨hJ, hvfr, φ, Φ, x, hφ, hΦ, ⟨k, hk⟩, hx⟩ := h
  obtain ⟨c, hc, -, σ, hσ, hσ01, hcσ⟩ := lv13_canonical_param hJ hb hφ hΦ
  have hrange := hc.1.2.2.2
  have hper := hc.1.2.1
  have hcl : ∀ s, c s ∈ closure (toExt D) := fun s =>
    frontier_subset_closure (hrange ▸ mem_range_self s)
  -- the canonical parametrization meets `vᵢ` at `σ(xᵢ)`
  have hcv : ∀ i, c (σ (x i)) = v i := fun i =>
    hΦ.2.2.1 (hcl _) (frontier_subset_closure (hvfr i)) (by rw [hcσ, hx])
  have hb : ∀ i, 0 < σ (x i) ∧ σ (x i) < 1 := fun i => hσ01 (x i)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  -- shift the parameters of the vertices before `k` by one period
  obtain ⟨s, hs, hsI, hsv⟩ : ∃ s : Fin 4 → ℝ, StrictMono s ∧ (∀ i, s i ∈ Ico (σ (x 0)) (σ (x 0) + 1)) ∧
      ∀ i, s i = σ (x i) ∨ s i = σ (x i) + 1 := by
    have F0 := hσ (hk (show (0 : Fin 4) < 1 by decide))
    have F1 := hσ (hk (show (1 : Fin 4) < 2 by decide))
    have F2 := hσ (hk (show (2 : Fin 4) < 3 by decide))
    fin_cases k
    · -- `x₀ < x₁ < x₂ < x₃`
      simp at F0 F1 F2
      refine ⟨fun i => σ (x i), ?_, fun i => ?_, fun i => Or.inl rfl⟩
      · rw [Fin.strictMono_iff_lt_succ]
        intro i
        fin_cases i <;> simpa
      · fin_cases i <;> simp <;> constructor <;> linarith
    · -- `x₁ < x₂ < x₃ < x₀`
      simp at F0 F1 F2
      refine ⟨![σ (x 0), σ (x 1) + 1, σ (x 2) + 1, σ (x 3) + 1], ?_, fun i => ?_, fun i => ?_⟩
      · rw [Fin.strictMono_iff_lt_succ]
        intro i
        fin_cases i <;> simp <;> linarith
      · fin_cases i <;> simp <;> constructor <;> linarith
      · fin_cases i <;> simp
    · -- `x₂ < x₃ < x₀ < x₁`
      simp at F0 F1 F2
      refine ⟨![σ (x 0), σ (x 1), σ (x 2) + 1, σ (x 3) + 1], ?_, fun i => ?_, fun i => ?_⟩
      · rw [Fin.strictMono_iff_lt_succ]
        intro i
        fin_cases i <;> simp <;> linarith
      · fin_cases i <;> simp <;> constructor <;> linarith
      · fin_cases i <;> simp
    · -- `x₃ < x₀ < x₁ < x₂`
      simp at F0 F1 F2
      refine ⟨![σ (x 0), σ (x 1), σ (x 2), σ (x 3) + 1], ?_, fun i => ?_, fun i => ?_⟩
      · rw [Fin.strictMono_iff_lt_succ]
        intro i
        fin_cases i <;> simp <;> linarith
      · fin_cases i <;> simp <;> constructor <;> linarith
      · fin_cases i <;> simp
  refine ⟨c, hc, σ (x 0), s, hs, hsI, fun i => ?_⟩
  rcases hsv i with e | e
  · rw [e, hcv]
  · rw [e, hper, hcv]

/-! ## Bridge to Li Zhong's `IsKQC`, stage 2: images of quadrilaterals and the main theorem

On the finite core `{z ∈ ℂ : z ∈ G, w(z) ≠ ∞}` of a `K`-quasiconformal `w`, `finiteMap w` is a homeomorphism
(`lv13_finiteCore_homeo`). It maps Li Zhong's quadrilaterals onto quadrilaterals with the image vertices: LV's
sense-preservation of triples is carried to the real coordinates of a uniformizer of the image by
`lv13_same_order` (`lv13_image_isTopQuad`). The module inequality is LV's (`lv13_modulus_le`), whence
`LiZhongQC.IsKQC` (`lv13_isKQC_of_isKQuasiconformal`). -/

/-- Helper (bridge, stage 2). A plane Jordan domain is a Jordan domain of `ℂ̄`. -/
theorem lv13_isJordanDomainExt_toExt {D : Set ℂ} (hD : LiZhongQC.IsJordanDomain D) :
    IsJordanDomainExt (toExt D) := by
  obtain ⟨hDo, hDc, hJ⟩ := hD
  exact ⟨⟨OnePoint.isOpen_image_coe.2 hDo, hDc.image _ OnePoint.continuous_coe.continuousOn⟩, hJ⟩

/-- Helper (bridge, stage 2; B1). For a homeomorphism `w` of an open set `G ⊆ ℂ̄`, the finite core
`{z ∈ ℂ : z ∈ G, w(z) ≠ ∞}` is open and `finiteMap w` is a homeomorphism of it onto its image (continuous and
injective there; the inverse is continuous by invariance of domain). -/
theorem lv13_finiteCore_homeo {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G)
    (hw : IsHomeoOn w G (w '' G)) :
    IsOpen {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} ∧
      LiZhongQC.IsHomeomorphOnto (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}
        (finiteMap w '' {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}) := by
  obtain ⟨hwc, hwi, -, -⟩ := hw
  obtain ⟨D, hDdef⟩ : ∃ D : Set ℂ, D = {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} := ⟨_, rfl⟩
  rw [← hDdef]
  have hDo : IsOpen D := by
    have h := hwc.isOpen_inter_preimage hG (isOpen_compl_singleton (x := extInf))
    have e : D = ((↑) : ℂ → ExtPlane) ⁻¹' (G ∩ w ⁻¹' {extInf}ᶜ) := by
      ext z
      simp [hDdef]
    rw [e]
    exact h.preimage OnePoint.continuous_coe
  have hfin : ∀ z ∈ D, w z = ((finiteMap w z : ℂ) : ExtPlane) := fun z hz => by
    rw [hDdef] at hz
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hz.2
    show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
    rw [← hu]
    rfl
  have hDG : ∀ z ∈ D, (z : ExtPlane) ∈ G := fun z hz => by
    rw [hDdef] at hz
    exact hz.1
  have hfc : ContinuousOn (finiteMap w) D := by
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuousOn_iff]
    exact (hwc.comp OnePoint.continuous_coe.continuousOn hDG).congr fun z hz => (hfin z hz).symm
  have hfi : InjOn (finiteMap w) D := fun z hz z' hz' h => by
    have h' : w z = w z' := by rw [hfin z hz, hfin z' hz', h]
    exact OnePoint.coe_injective (hwi (hDG z hz) (hDG z' hz') h')
  refine ⟨hDo, hfc, hfi, rfl, ?_⟩
  -- the inverse is continuous: images of small open sets are open (invariance of domain)
  have hleft : ∀ z ∈ D, Function.invFunOn (finiteMap w) D (finiteMap w z) = z := fun z hz =>
    hfi.leftInvOn_invFunOn hz
  rintro _ ⟨z, hz, rfl⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hVo : IsOpen (D ∩ Metric.ball z ε) := hDo.inter Metric.isOpen_ball
  have hfVo : IsOpen (finiteMap w '' (D ∩ Metric.ball z ε)) :=
    LiZhongQC.isOpen_image_of_continuousOn_injOn hVo (hfc.mono inter_subset_left) (hfi.mono inter_subset_left)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfVo (finiteMap w z)
    (mem_image_of_mem _ ⟨hz, Metric.mem_ball_self hε⟩)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨z', hz', rfl⟩ hdist
  obtain ⟨z'', hz''V, hz''eq⟩ := hball hdist
  have hz'' : z'' = z' := hfi hz''V.1 hz' hz''eq
  rw [hleft z' hz', hleft z hz, ← hz'']
  exact hz''V.2

/-- Helper (bridge, stage 2). A continuous logarithm `M` of `g − z` on `ℝ`, `g` `1`-periodic, is quasi-periodic:
`M(s + 1) − M(s)` lies in `2πiℤ` and is continuous, hence constant. -/
theorem lv13_lift_quasiperiodic {g : ℝ → ℂ} (hper : Function.Periodic g 1) {z : ℂ} {M : ℝ → ℂ}
    (hM : Continuous M) (hMe : ∀ s, exp (M s) = g s - z) (s : ℝ) : M (s + 1) - M s = M 1 - M 0 := by
  have hint : ∀ r : ℝ, ∃ n : ℤ, M (r + 1) - M r = n * (2 * Real.pi * I) := fun r => by
    have h1 : exp (M (r + 1) - M r) = 1 := by
      rw [Complex.exp_sub, hMe, hMe, hper r, div_self]
      intro h0
      have := hMe r
      rw [h0] at this
      exact Complex.exp_ne_zero _ this
    exact Complex.exp_eq_one_iff.1 h1
  -- `f(r) = Im(M(r + 1) − M(r))/(2π)` is continuous and integer-valued
  set f : ℝ → ℝ := fun r => (M (r + 1) - M r).im / (2 * Real.pi) with hfdef
  have hfc : Continuous f :=
    (Complex.continuous_im.comp ((hM.comp (continuous_id.add continuous_const)).sub hM)).div_const _
  have hfint : ∀ r, ∃ n : ℤ, f r = n ∧ M (r + 1) - M r = n * (2 * Real.pi * I) := fun r => by
    obtain ⟨n, hn⟩ := hint r
    refine ⟨n, ?_, hn⟩
    simp only [hfdef, hn]
    simp [Real.pi_ne_zero]
  obtain ⟨n₀, hn₀, he₀⟩ := hfint 0
  obtain ⟨n, hn, he⟩ := hfint s
  have hfz : (0 : ℝ) + 1 = 1 := zero_add 1
  rw [he, show M 1 - M 0 = M (0 + 1) - M 0 by rw [hfz], he₀]
  congr 1
  by_contra hne
  have hne' : n ≠ n₀ := fun h => hne (by rw [h])
  -- an intermediate non-integer value contradicts integrality
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · obtain ⟨r, -, hr⟩ := intermediate_value_uIcc (a := s) (b := 0) hfc.continuousOn
      (show (n : ℝ) + 1 / 2 ∈ uIcc (f s) (f 0) by
        rw [hn, hn₀]
        have : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hlt
        exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
    obtain ⟨m, hm, -⟩ := hfint r
    rw [hm] at hr
    have h1 : (n : ℝ) < m := by linarith
    have h2 : (m : ℝ) < n + 1 := by linarith
    have h1' : n < m := by exact_mod_cast h1
    have h2' : m < n + 1 := by exact_mod_cast h2
    omega
  · obtain ⟨r, -, hr⟩ := intermediate_value_uIcc (a := 0) (b := s) hfc.continuousOn
      (show (n₀ : ℝ) + 1 / 2 ∈ uIcc (f 0) (f s) by
        rw [hn, hn₀]
        have : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hgt
        exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
    obtain ⟨m, hm, -⟩ := hfint r
    rw [hm] at hr
    have h1 : (n₀ : ℝ) < m := by linarith
    have h2 : (m : ℝ) < n₀ + 1 := by linarith
    have h1' : n₀ < m := by exact_mod_cast h1
    have h2' : m < n₀ + 1 := by exact_mod_cast h2
    omega

/-- Helper (bridge, stage 2; B3). The cyclic order of boundary points does not depend on the LV-positive
parametrization: if `γ₁` meets `p₀, p₁, p₂` at increasing parameters within one turn, so does every LV-positive `γ₂`.
`γ₂⁻¹ ∘ γ₁` lifts (through `AddCircle 1`) to a continuous `h̃` on `[0, 1]` with `γ₂ ∘ h̃ = γ₁` and
`h̃(1) = h̃(0) + d`, `d ∈ ℤ`. The winding of `γ₁` is `d` times that of `γ₂`, and both are `1`
(`lv13_winding_of_isPositiveBoundaryParam`). So `d = 1`, and `h̃` increases. -/
theorem lv13_same_order {U : Set ℂ} (hU : LiZhongQC.IsJordanDomain U) (hb : Bornology.IsBounded U)
    {γ₁ γ₂ : ℝ → ExtPlane} (h₁ : IsPositiveBoundaryParam (toExt U) γ₁)
    (h₂ : IsPositiveBoundaryParam (toExt U) γ₂) {p : Fin 3 → ExtPlane} {a : ℝ} {s : Fin 3 → ℝ}
    (hs : StrictMono s) (hsI : ∀ i, s i ∈ Ico a (a + 1)) (hγ : ∀ i, γ₁ (s i) = p i) :
    ∃ (b : ℝ) (s' : Fin 3 → ℝ), StrictMono s' ∧ (∀ i, s' i ∈ Ico b (b + 1)) ∧ ∀ i, γ₂ (s' i) = p i := by
  -- the finite curves `gᵢ = finiteValue ∘ γᵢ`
  have hfr : frontier (toExt U) = toExt (frontier U) := LiZhongQC.frontier_toExt_of_isBounded hb hU.1
  have hfin : ∀ γ : ℝ → ExtPlane, IsPositiveBoundaryParam (toExt U) γ →
      (∀ s, γ s = ((finiteValue (γ s) : ℂ) : ExtPlane) ∧ finiteValue (γ s) ∈ frontier U) ∧
        Continuous (fun s => finiteValue (γ s)) := fun γ hγ => by
    obtain ⟨⟨hγc, -, -, hγr⟩, -⟩ := hγ
    have h1 : ∀ s, γ s = ((finiteValue (γ s) : ℂ) : ExtPlane) ∧ finiteValue (γ s) ∈ frontier U := fun s => by
      have hs : γ s ∈ frontier (toExt U) := hγr ▸ mem_range_self s
      rw [hfr] at hs
      obtain ⟨w, hw, hws⟩ := hs
      rw [← hws]
      exact ⟨rfl, hw⟩
    refine ⟨h1, ?_⟩
    have e : ((↑) : ℂ → ExtPlane) ∘ (fun s => finiteValue (γ s)) = γ := funext fun s => ((h1 s).1).symm
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuous_iff, e]
    exact hγc
  obtain ⟨hf₁, hg₁c⟩ := hfin γ₁ h₁
  obtain ⟨hf₂, hg₂c⟩ := hfin γ₂ h₂
  obtain ⟨g₁, hg₁def⟩ : ∃ g : ℝ → ℂ, g = fun s => finiteValue (γ₁ s) := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂def⟩ : ∃ g : ℝ → ℂ, g = fun s => finiteValue (γ₂ s) := ⟨_, rfl⟩
  rw [← hg₁def] at hg₁c
  rw [← hg₂def] at hg₂c
  have hγ₁g : ∀ s, γ₁ s = ((g₁ s : ℂ) : ExtPlane) := fun s => by rw [hg₁def]; exact (hf₁ s).1
  have hγ₂g : ∀ s, γ₂ s = ((g₂ s : ℂ) : ExtPlane) := fun s => by rw [hg₂def]; exact (hf₂ s).1
  have hg₁per : Function.Periodic g₁ 1 := fun s => by rw [hg₁def]; simp only [h₁.1.2.1 s]
  have hg₂per : Function.Periodic g₂ 1 := fun s => by rw [hg₂def]; simp only [h₂.1.2.1 s]
  have hg₁inj : InjOn g₁ (Ico 0 1) := fun s hs t ht h => h₁.1.2.2.1 hs ht (by rw [hγ₁g, hγ₁g, h])
  have hg₂inj : InjOn g₂ (Ico 0 1) := fun s hs t ht h => h₂.1.2.2.1 hs ht (by rw [hγ₂g, hγ₂g, h])
  have hfract : ∀ {g : ℝ → ℂ}, Function.Periodic g 1 → ∀ t, g (Int.fract t) = g t := fun {g} hg t => by
    rw [show Int.fract t = t - (⌊t⌋ : ℤ) * (1 : ℝ) by rw [Int.fract]; ring]
    exact hg.sub_int_mul_eq ⌊t⌋
  have hfractI : ∀ t : ℝ, Int.fract t ∈ Ico (0 : ℝ) 1 := fun t => ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
  -- `g₂` induces a homeomorphism of the circle `AddCircle 1` onto the curve
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G₂ : AddCircle (1 : ℝ) → ℂ, ∀ t : ℝ, G₂ (t : AddCircle (1 : ℝ)) = g₂ t :=
    ⟨hg₂per.lift, fun t => rfl⟩
  have hG₂c : Continuous G₂ := by
    rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
    exact (show G₂ ∘ QuotientAddGroup.mk = g₂ from funext hG₂) ▸ hg₂c
  have hcoe_fract : ∀ t : ℝ, ((Int.fract t : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := fun t => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    exact ⟨⌊t⌋, by rw [zsmul_one, Int.fract]; ring⟩
  have hG₂i : Function.Injective G₂ := by
    intro x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H s =>
      induction y using QuotientAddGroup.induction_on with
      | H t =>
        rw [← hcoe_fract s, ← hcoe_fract t]
        congr 1
        refine hg₂inj (hfractI s) (hfractI t) ?_
        rw [hfract hg₂per, hfract hg₂per, ← hG₂, ← hG₂]
        exact hxy
  have hemb := (hG₂c.isClosedEmbedding hG₂i).isEmbedding
  have hmem : ∀ t, g₁ t ∈ range G₂ := fun t => by
    have h := h₂.1.2.2.2
    have hm : γ₁ t ∈ range γ₂ := by rw [h, ← h₁.1.2.2.2]; exact mem_range_self t
    obtain ⟨u, hu⟩ := hm
    exact ⟨u, by rw [hG₂]; exact OnePoint.coe_injective (by rw [← hγ₂g, ← hγ₁g, hu])⟩
  set Hc : ℝ → AddCircle (1 : ℝ) := fun t => hemb.toHomeomorph.symm ⟨g₁ t, hmem t⟩ with hHcdef
  have hHcc : Continuous Hc := hemb.toHomeomorph.symm.continuous.comp (hg₁c.subtype_mk hmem)
  have hGH : ∀ t, G₂ (Hc t) = g₁ t := fun t =>
    congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨g₁ t, hmem t⟩)
  -- lift through the circle: `η` with `γ₂ ∘ η = γ₁`
  set E : ℝ → ℂ := fun t => ((AddCircle.toCircle (Hc t) : Circle) : ℂ) with hEdef
  have hEc : Continuous E := by
    rw [hEdef]
    exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hHcc)
  obtain ⟨L, hL, hLe⟩ := LiZhongQC.exists_continuousOn_log_lift hEc.continuousOn
    (w := 0) fun t _ => Circle.coe_ne_zero _
  have hLre : ∀ t ∈ Icc (0 : ℝ) 1, (L t).re = 0 := fun t ht => by
    have h := congrArg (fun x : ℂ => ‖x‖) (hLe t ht)
    simp only [Complex.norm_exp, sub_zero, hEdef, Circle.norm_coe] at h
    exact Real.exp_eq_one_iff _ |>.1 h
  set η : ℝ → ℝ := fun t => (L t).im / (2 * Real.pi) with hηdef
  have hηc : ContinuousOn η (Icc 0 1) := (Complex.continuous_im.comp_continuousOn hL).div_const _
  have hηH : ∀ t ∈ Icc (0 : ℝ) 1, ((η t : ℝ) : AddCircle (1 : ℝ)) = Hc t := fun t ht => by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    have h := hLe t ht
    rw [sub_zero] at h
    show exp (((2 * Real.pi / 1 * η t : ℝ) : ℂ) * I) = E t
    rw [← h]
    congr 1
    apply Complex.ext
    · simp [hLre t ht]
    · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
        add_zero]
      simp only [hηdef]
      field_simp
  have hg₂η : ∀ t ∈ Icc (0 : ℝ) 1, g₂ (η t) = g₁ t := fun t ht => by
    rw [← hG₂, hηH t ht, hGH]
  -- `η(1) = η(0) + d`
  obtain ⟨d, hd⟩ : ∃ d : ℤ, η 1 = η 0 + d := by
    have h01 : Hc 1 = Hc 0 := by
      simp only [hHcdef]
      congr 2
      rw [show (1 : ℝ) = 0 + 1 by norm_num, hg₁per 0]
    have h := (hηH 1 ⟨zero_le_one, le_rfl⟩).trans (h01.trans (hηH 0 ⟨le_rfl, zero_le_one⟩).symm)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨-k, by rw [zsmul_one] at hk; push_cast; linarith⟩
  -- winding: the global lift `M₂` of `γ₂ − z` composed with `η` is a lift of `γ₁ − z`, so `d = 1`
  obtain ⟨z, hz⟩ := hU.2.1.nonempty
  have hgz : ∀ {γ : ℝ → ExtPlane}, IsPositiveBoundaryParam (toExt U) γ → ∀ t, finiteValue (γ t) ≠ z :=
    fun {γ} hγ t h => by
      have := ((hfin γ hγ).1 t).2
      rw [hU.1.frontier_eq, h] at this
      exact this.2 hz
  obtain ⟨M₀, hM₀, hM₀e⟩ := LiZhongQC.exists_continuousOn_log_lift hg₂c.continuousOn
    fun t _ => by rw [hg₂def]; exact hgz h₂ t
  have hM₀1 := lv13_winding_of_isPositiveBoundaryParam hU hb h₂ hz hM₀ (fun t ht => by rw [hM₀e t ht, hg₂def])
  obtain ⟨M₂, hM₂c, hM₂e, hM₂1⟩ := lv13_lift_extend hg₂per hM₀ hM₀e hM₀1
  have hq := lv13_lift_quasiperiodic hg₂per hM₂c hM₂e
  have hqZ : ∀ (s : ℝ) (k : ℤ), M₂ (s + k) = M₂ s + k * (2 * Real.pi * I) := fun s k => by
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have := hq (s + k)
      push_cast at this ⊢
      rw [show s + (k + 1) = s + k + 1 by ring]
      linear_combination this + ih + hM₂1
    | pred k ih =>
      have := hq (s + (-(k : ℝ) - 1))
      push_cast at this ih ⊢
      rw [show s + (-(k : ℝ) - 1) + 1 = s + -(k : ℝ) by ring] at this
      linear_combination -this + ih - hM₂1
  have hd1 : d = 1 := by
    have hL₁ := lv13_winding_of_isPositiveBoundaryParam hU hb h₁ hz (L := fun t => M₂ (η t))
      (hM₂c.comp_continuousOn hηc) (fun t ht => by
        show exp (M₂ (η t)) = finiteValue (γ₁ t) - z
        rw [hM₂e, hg₂η t ht, hg₁def])
    rw [hd, hqZ, add_sub_cancel_left] at hL₁
    have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hd' : (d : ℂ) = 1 := by
      have := mul_right_cancel₀ h2pi (hL₁.trans (one_mul _).symm)
      exact this
    exact_mod_cast hd'
  rw [hd1, Int.cast_one] at hd
  -- `η` is injective on `[0, 1]`, hence strictly increasing there
  have hηi : InjOn η (Icc 0 1) := by
    intro t ht t' ht' h
    have hg : g₁ t = g₁ t' := by rw [← hg₂η t ht, ← hg₂η t' ht', h]
    have h10 : g₁ 1 = g₁ 0 := by rw [show (1 : ℝ) = 0 + 1 by norm_num, hg₁per 0]
    rcases eq_or_lt_of_le ht.2 with e | e <;> rcases eq_or_lt_of_le ht'.2 with e' | e'
    · rw [e, e']
    · exfalso
      rw [e, h10] at hg
      have := hg₁inj ⟨le_rfl, zero_lt_one⟩ ⟨ht'.1, e'⟩ hg
      rw [e, ← this] at h
      linarith
    · exfalso
      rw [e', h10] at hg
      have := hg₁inj ⟨ht.1, e⟩ ⟨le_rfl, zero_lt_one⟩ hg
      rw [e', this] at h
      linarith
    · exact hg₁inj ⟨ht.1, e⟩ ⟨ht'.1, e'⟩ hg
  have hηm := hηc.strictMonoOn_of_injOn_Icc zero_le_one (by linarith) hηi
  -- the quasi-periodic extension `H̃(t) = η(fract t) + ⌊t⌋`
  set H : ℝ → ℝ := fun t => η (Int.fract t) + ⌊t⌋ with hHdef
  have hfI : ∀ t : ℝ, Int.fract t ∈ Icc (0 : ℝ) 1 := fun t => ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hHmono : StrictMono H := by
    intro t t' htt'
    simp only [hHdef]
    rcases lt_or_eq_of_le (Int.floor_le_floor htt'.le) with hlt | heq
    · have h1 : η (Int.fract t) < η 1 := hηm (hfI t) ⟨zero_le_one, le_rfl⟩ (Int.fract_lt_one t)
      have h2 : η 0 ≤ η (Int.fract t') :=
        hηm.monotoneOn ⟨le_rfl, zero_le_one⟩ (hfI t') (Int.fract_nonneg t')
      have h3 : ((⌊t⌋ : ℤ) : ℝ) + 1 ≤ ⌊t'⌋ := by exact_mod_cast hlt
      linarith
    · rw [heq]
      have hf : Int.fract t < Int.fract t' := by
        rw [Int.fract, Int.fract, heq]
        linarith
      linarith [hηm (hfI t) (hfI t') hf]
  have hHg : ∀ t, g₂ (H t) = g₁ t := fun t => by
    simp only [hHdef]
    rw [show η (Int.fract t) + (⌊t⌋ : ℝ) = η (Int.fract t) + ((⌊t⌋ : ℤ) : ℝ) * 1 by ring,
      hg₂per.int_mul ⌊t⌋, hg₂η _ (hfI t), hfract hg₁per]
  have hH1 : ∀ t, H (t + 1) = H t + 1 := fun t => by
    simp only [hHdef, Int.fract_add_one, Int.floor_add_one]
    push_cast
    ring
  refine ⟨H a, fun i => H (s i), hHmono.comp hs, fun i => ⟨hHmono.monotone (hsI i).1, ?_⟩, fun i => ?_⟩
  · rw [← hH1]
    exact hHmono (hsI i).2
  · rw [hγ₂g, hHg, ← hγ₁g, hγ]

/-- Helper (bridge, stage 2). Three numbers `t₀, t₁, t₂ ∈ [0, 1)` met, modulo `1`, at increasing parameters within one
turn are in cyclic order. -/
theorem lv13_cyclic3 {t : Fin 3 → ℝ} (ht : ∀ i, t i ∈ Ico (0 : ℝ) 1) {b : ℝ} {s : Fin 3 → ℝ} (hs : StrictMono s)
    (hsI : ∀ i, s i ∈ Ico b (b + 1)) (hst : ∀ i, ∃ n : ℤ, s i = t i + n) :
    (t 0 < t 1 ∧ t 1 < t 2) ∨ (t 1 < t 2 ∧ t 2 < t 0) ∨ (t 2 < t 0 ∧ t 0 < t 1) := by
  obtain ⟨n0, h0⟩ := hst 0
  obtain ⟨n1, h1⟩ := hst 1
  obtain ⟨n2, h2⟩ := hst 2
  have h01 := hs (show (0 : Fin 3) < 1 by decide)
  have h12 := hs (show (1 : Fin 3) < 2 by decide)
  have hb0 := hsI 0
  have hb2 := hsI 2
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have hd1 : n1 - n0 = 0 ∨ n1 - n0 = 1 := by
    have a1 : ((n1 - n0 : ℤ) : ℝ) < 2 := by
      push_cast
      linarith [hb0.1, hb2.2, ht0.1, ht1.2, ht0.2, ht1.1]
    have a2 : (-1 : ℝ) < ((n1 - n0 : ℤ) : ℝ) := by
      push_cast
      linarith [ht0.1, ht1.2, ht0.2, ht1.1]
    have a1' : n1 - n0 < 2 := by exact_mod_cast a1
    have a2' : -1 < n1 - n0 := by exact_mod_cast a2
    omega
  have hd2 : n2 - n0 = 0 ∨ n2 - n0 = 1 := by
    have a1 : ((n2 - n0 : ℤ) : ℝ) < 2 := by
      push_cast
      linarith [hb0.1, hb2.2, ht0.1, ht2.2, ht0.2, ht2.1]
    have a2 : (-1 : ℝ) < ((n2 - n0 : ℤ) : ℝ) := by
      push_cast
      linarith [ht0.1, ht2.2, ht0.2, ht2.1, hb0.1, hb2.2]
    have a1' : n2 - n0 < 2 := by exact_mod_cast a1
    have a2' : -1 < n2 - n0 := by exact_mod_cast a2
    omega
  rcases hd1 with e1 | e1 <;> rcases hd2 with e2 | e2
  · have e1' : (n1 : ℝ) = n0 := by exact_mod_cast (by omega : n1 = n0)
    have e2' : (n2 : ℝ) = n0 := by exact_mod_cast (by omega : n2 = n0)
    left
    constructor <;> linarith
  · have e1' : (n1 : ℝ) = n0 := by exact_mod_cast (by omega : n1 = n0)
    have e2' : (n2 : ℝ) = n0 + 1 := by exact_mod_cast (by omega : n2 = n0 + 1)
    right
    right
    constructor <;> linarith [hb0.1, hb2.2]
  · exfalso
    have e1' : (n1 : ℝ) = n0 + 1 := by exact_mod_cast (by omega : n1 = n0 + 1)
    have e2' : (n2 : ℝ) = n0 := by exact_mod_cast (by omega : n2 = n0)
    linarith [ht1.1, ht2.2]
  · have e1' : (n1 : ℝ) = n0 + 1 := by exact_mod_cast (by omega : n1 = n0 + 1)
    have e2' : (n2 : ℝ) = n0 + 1 := by exact_mod_cast (by omega : n2 = n0 + 1)
    right
    left
    constructor <;> linarith [hb0.1, hb2.2]

/-- Helper (bridge, stage 2). Four reals whose triples `(y₀, y₁, y₂)` and `(y₀, y₂, y₃)` are in cyclic order are in
cyclic order. -/
theorem lv13_cyclicStrictMono_of_triples {y : Fin 4 → ℝ}
    (h₁ : (y 0 < y 1 ∧ y 1 < y 2) ∨ (y 1 < y 2 ∧ y 2 < y 0) ∨ (y 2 < y 0 ∧ y 0 < y 1))
    (h₂ : (y 0 < y 2 ∧ y 2 < y 3) ∨ (y 2 < y 3 ∧ y 3 < y 0) ∨ (y 3 < y 0 ∧ y 0 < y 2)) :
    LiZhongQC.CyclicStrictMono y := by
  rcases h₁ with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h₂ with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩
  · exact LiZhongQC.cyclicStrictMono_of_chain 0 (by simpa using a) (by simpa using b) (by simpa using d)
  · exfalso
    linarith
  · exact LiZhongQC.cyclicStrictMono_of_chain 3 (by simpa using c) (by simpa using a) (by simpa using b)
  · exfalso
    linarith
  · exact LiZhongQC.cyclicStrictMono_of_chain 1 (by simpa using a) (by simpa using c) (by simpa using d)
  · exfalso
    linarith
  · exfalso
    linarith
  · exact LiZhongQC.cyclicStrictMono_of_chain 2 (by simpa using c) (by simpa using d) (by simpa using b)
  · exfalso
    linarith

/-- Helper (bridge, stage 2; B5). A sense-preserving homeomorphism `w` of an open `G ⊆ ℂ̄` maps a Li Zhong
quadrilateral `Q` with `Q̄` in the finite core onto the quadrilateral `f(Q)(f(z₁), …, f(z₄))`, `f = finiteMap w`.
- The triples `(z₁, z₂, z₃)` and `(z₁, z₃, z₄)` are LV-positive (`lv13_isPositivelyOrdered_of_isTopQuad`), hence so
  are their images (sense-preservation).
- So they are in cyclic order along the canonical parametrization of `f(Q)` (`lv13_same_order`), that is, in the real
  coordinates of a uniformizer of `f(Q)` (`lv13_cyclic3`, `lv13_cyclicStrictMono_of_triples`). -/
theorem lv13_image_isTopQuad {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G)
    (hw : IsSensePreservingOn w G) (Q : LiZhongQC.TopQuad)
    (hQ : closure (toExt Q.dom) ⊆ toExt {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}) :
    ∃ Q' : LiZhongQC.TopQuad, Q.IsImageUnder Q' (finiteMap w) := by
  obtain ⟨hDo, hfc, hfi, -, -⟩ := lv13_finiteCore_homeo hG hw.1
  have hQJ := Q.isTopQuad.1
  have hQdomD : Q.dom ⊆ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} := fun z hz => by
    obtain ⟨u, hu, hue⟩ := hQ (subset_closure ⟨z, hz, rfl⟩)
    rw [← OnePoint.coe_injective hue]
    exact hu
  have hQo : IsOpen (finiteMap w '' Q.dom) :=
    LiZhongQC.isOpen_image_of_continuousOn_injOn hQJ.1 (hfc.mono hQdomD) (hfi.mono hQdomD)
  obtain ⟨hJD, -, hfr⟩ := LiZhongQC.image_isJordanDomain_of_open hDo hfc hfi hQ hQo
  have hbQ : Bornology.IsBounded Q.dom := LiZhongQC.isBounded_of_extInf_notMem_closure_toExt fun h => by
    obtain ⟨z, -, hz⟩ := hQ h
    exact OnePoint.coe_ne_infty z hz
  have hb' : Bornology.IsBounded (finiteMap w '' Q.dom) := by
    apply LiZhongQC.isBounded_of_extInf_notMem_closure_toExt
    intro hmem
    obtain ⟨u, -, hu⟩ := LiZhongQC.closure_toExt_image_subset hfc hQ subset_rfl hmem
    exact OnePoint.coe_ne_infty u hu
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := LiZhongQC.exists_conformalOnto_upperHalf_of_isJordanDomain hJD hb'
  have hvfr : ∀ i, (OnePoint.map (finiteMap w) ∘ Q.vert) i ∈ frontier (toExt (finiteMap w '' Q.dom)) :=
    fun i => by
      rw [hfr]
      exact mem_image_of_mem _ (Q.isTopQuad.2.1 i)
  obtain ⟨ψ', Ψ', y, hψ', hΨ', hΨ'v⟩ := LiZhongQC.exists_uniformizer_finite_vertices hQo hψ hΨ hvfr
  suffices hy : LiZhongQC.CyclicStrictMono y from
    ⟨⟨finiteMap w '' Q.dom, OnePoint.map (finiteMap w) ∘ Q.vert, hJD, hvfr, ψ', Ψ', y, hψ', hΨ', hy, hΨ'v⟩,
      rfl, fun i => rfl⟩
  -- `w = OnePoint.map (finiteMap w)` on `Q̄`
  have hwfin : ∀ z : ℂ, (z : ExtPlane) ∈ closure (toExt Q.dom) →
      w z = OnePoint.map (finiteMap w) (z : ExtPlane) := fun z hz => by
    obtain ⟨u, hu, hue⟩ := hQ hz
    rw [OnePoint.coe_injective hue] at hu
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hu.2
    show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
    rw [← hv]
    rfl
  have hwv : ∀ i, w (Q.vert i) = OnePoint.map (finiteMap w) (Q.vert i) := fun i => by
    have hcl : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    obtain ⟨z, -, hz⟩ := hQ hcl
    rw [← hz] at hcl ⊢
    exact hwfin z hcl
  have hwQ : w '' toExt Q.dom = toExt (finiteMap w '' Q.dom) := by
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hwfin z (subset_closure ⟨z, hz, rfl⟩)]
      exact ⟨finiteMap w z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, ⟨z, hz, rfl⟩, ?_⟩
      rw [hwfin z (subset_closure ⟨z, hz, rfl⟩)]
      rfl
  -- the LV-positive vertex triples of `Q` and their images
  obtain ⟨γ, hγ, a, s, hs, hsI, hγs⟩ := lv13_isPositivelyOrdered_of_isTopQuad Q.isTopQuad hbQ
  have hQclG : closure (toExt Q.dom) ⊆ G := hQ.trans (by rintro _ ⟨z, hz, rfl⟩; exact hz.1)
  have hpres := hw.2 (toExt Q.dom) (lv13_isJordanDomainExt_toExt hQJ) hQclG
  have htriple : ∀ e : Fin 3 → Fin 4, StrictMono e → IsPositivelyOrdered (toExt (finiteMap w '' Q.dom))
      (fun j => OnePoint.map (finiteMap w) (Q.vert (e j))) := fun e he => by
    have h1 : IsPositivelyOrdered (toExt Q.dom) (Q.vert ∘ e) :=
      ⟨γ, hγ, a, s ∘ e, hs.comp he, fun j => hsI (e j), fun j => hγs (e j)⟩
    have h2 := hpres (Q.vert ∘ e) h1
    rw [hwQ] at h2
    have e1 : (fun j => OnePoint.map (finiteMap w) (Q.vert (e j))) = w ∘ (Q.vert ∘ e) :=
      funext fun j => (hwv (e j)).symm
    rw [e1]
    exact h2
  -- the canonical parametrization of `f(Q)` through the uniformizer `Ψ′`
  obtain ⟨c, hc, -, σ, hσ, hσ01, hcσ⟩ := lv13_canonical_param hJD hb' hψ' hΨ'
  have hcl : ∀ t, c t ∈ closure (toExt (finiteMap w '' Q.dom)) := fun t =>
    frontier_subset_closure (hc.1.2.2.2 ▸ mem_range_self t)
  have hcv : ∀ i, c (σ (y i)) = OnePoint.map (finiteMap w) (Q.vert i) := fun i =>
    hΨ'.2.2.1 (hcl _) (frontier_subset_closure (hvfr i)) (by rw [hcσ]; exact (hΨ'v i).symm)
  have hcmod : ∀ t t', c t = c t' → ∃ n : ℤ, t = t' + n := fun t t' h => by
    have hpf : ∀ u, c (Int.fract u) = c u := fun u => by
      rw [show Int.fract u = u - (⌊u⌋ : ℤ) * (1 : ℝ) by rw [Int.fract]; ring]
      exact hc.1.2.1.sub_int_mul_eq ⌊u⌋
    have h' := hc.1.2.2.1 ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ ⟨Int.fract_nonneg t', Int.fract_lt_one t'⟩
      (by rw [hpf, hpf, h])
    refine ⟨⌊t⌋ - ⌊t'⌋, ?_⟩
    rw [Int.fract, Int.fract] at h'
    push_cast
    linarith
  -- each increasing index triple has its real coordinates in cyclic order
  have hcyc : ∀ e : Fin 3 → Fin 4, StrictMono e →
      (y (e 0) < y (e 1) ∧ y (e 1) < y (e 2)) ∨ (y (e 1) < y (e 2) ∧ y (e 2) < y (e 0)) ∨
        (y (e 2) < y (e 0) ∧ y (e 0) < y (e 1)) := fun e he => by
    obtain ⟨γ', hγ', b₀, s₀, hs₀, hs₀I, hγ's₀⟩ := htriple e he
    obtain ⟨b, s', hs', hs'I, hcs'⟩ := lv13_same_order hJD hb' hγ' hc hs₀ hs₀I hγ's₀
    have hst : ∀ j, ∃ n : ℤ, s' j = σ (y (e j)) + n := fun j =>
      hcmod _ _ ((hcs' j).trans (hcv (e j)).symm)
    have h := lv13_cyclic3 (t := fun j => σ (y (e j))) (fun j => ⟨(hσ01 _).1.le, (hσ01 _).2⟩) hs' hs'I hst
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩
    · exact Or.inr (Or.inl ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩)
    · exact Or.inr (Or.inr ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩)
  have h012 := hcyc ![0, 1, 2] (by decide)
  have h023 := hcyc ![0, 2, 3] (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h012 h023
  exact lv13_cyclicStrictMono_of_triples h012 h023

/-- Helper (bridge, stage 2; B6). The module bound: for a `K`-quasiconformal `w`, a Li Zhong quadrilateral `Q` with
`Q̄` in the finite core and its image `Q′` satisfy `M(Q′) ≤ K M(Q)`. This is LV's dilatation bound for the LV
quadrilateral `(toExt Q, z)`, with the modules identified by `lv12_quadModule_toExt`. -/
theorem lv13_modulus_le {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    {Q Q' : LiZhongQC.TopQuad}
    (hQ : closure (toExt Q.dom) ⊆ toExt {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf})
    (hQ' : Q.IsImageUnder Q' (finiteMap w)) : Q'.modulus ≤ K * Q.modulus := by
  obtain ⟨hGd, hwsp, hK⟩ := hw
  obtain ⟨hQd, hQv⟩ := hQ'
  have hQG : closure (toExt Q.dom) ⊆ G := hQ.trans (by rintro _ ⟨z, hz, rfl⟩; exact hz.1)
  have hbQ : Bornology.IsBounded Q.dom := LiZhongQC.isBounded_of_extInf_notMem_closure_toExt fun h => by
    obtain ⟨z, -, hz⟩ := hQ h
    exact OnePoint.coe_ne_infty z hz
  obtain ⟨hQJ, hQfr, -⟩ := Q.isTopQuad
  let QLV : Quadrilateral := ⟨toExt Q.dom, Q.vert, lv13_isJordanDomainExt_toExt hQJ, hQfr,
    lv13_isPositivelyOrdered_of_isTopQuad Q.isTopQuad hbQ⟩
  have hle : ENNReal.ofReal (quadDilatation w QLV) ≤ ENNReal.ofReal K :=
    (le_iSup₂ (f := fun (R : Quadrilateral) (_ : closure R.dom ⊆ G) => ENNReal.ofReal (quadDilatation w R))
      QLV hQG).trans hK
  -- the modules of `Q` and of `Q′` are LV's
  have hmodQ : QLV.module = Q.modulus := lv12_quadModule_toExt hQJ.1 hQJ.2.1 Q.vert
  obtain ⟨hQ'J, -, -⟩ := Q'.isTopQuad
  have hfinv : ∀ i, w (Q.vert i) = Q'.vert i := fun i => by
    obtain ⟨z, hz, hze⟩ := hQ (frontier_subset_closure (hQfr i))
    rw [hQv i, ← hze]
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hz.2
    show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
    rw [← hu]
    rfl
  have hdom : w '' toExt Q.dom = toExt Q'.dom := by
    rw [hQd]
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzD := hQ (subset_closure ⟨z, hz, rfl⟩)
      obtain ⟨z', hz', hz'e⟩ := hzD
      rw [OnePoint.coe_injective hz'e] at hz'
      obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hz'.2
      refine ⟨finiteMap w z, ⟨z, hz, rfl⟩, ?_⟩
      show ((finiteValue (w z) : ℂ) : ExtPlane) = w z
      rw [← hu]
      rfl
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzD := hQ (subset_closure ⟨z, hz, rfl⟩)
      obtain ⟨z', hz', hz'e⟩ := hzD
      rw [OnePoint.coe_injective hz'e] at hz'
      obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hz'.2
      refine ⟨z, ⟨z, hz, rfl⟩, ?_⟩
      show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
      rw [← hu]
      rfl
  have hmodQ' : quadModule (w '' QLV.dom) (w ∘ QLV.vert) = Q'.modulus := by
    show quadModule (w '' toExt Q.dom) (w ∘ Q.vert) = Q'.modulus
    rw [hdom, show w ∘ Q.vert = Q'.vert from funext hfinv]
    exact lv12_quadModule_toExt hQ'J.1 hQ'J.2.1 Q'.vert
  have hpos := LiZhongQC.modulus_pos Q
  have hpos' := LiZhongQC.modulus_pos Q'
  rw [quadDilatation, hmodQ', hmodQ] at hle
  rcases (ENNReal.ofReal_le_ofReal_iff' ).1 hle with h | h
  · rwa [div_le_iff₀ hpos] at h
  · exact absurd h (not_le.2 (div_pos hpos' hpos))

/-- Helper (bridge to Li Zhong, main theorem). A `K`-quasiconformal mapping `w` of a domain `G ⊆ ℂ̄` (Ch. I §3) is, on
its finite core `{z ∈ ℂ : z ∈ G, w(z) ≠ ∞}`, a `K`-quasiconformal mapping in Li Zhong's sense (Definition 7.1,
`LiZhongQC.IsKQC`).
- `1 ≤ K`: a quadrilateral and its relabelling, since `M(Q(z₂,z₃,z₄,z₁)) = 1/M(Q)`.
- The rest is `lv13_finiteCore_homeo`, `lv13_image_isTopQuad` and `lv13_modulus_le`. -/
theorem lv13_isKQC_of_isKQuasiconformal {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hw : IsKQuasiconformal w G K) :
    LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K := by
  obtain ⟨hGd, hwsp, hK⟩ := hw
  obtain ⟨hDo, hhom⟩ := lv13_finiteCore_homeo hGd.1 hwsp.1
  refine ⟨hDo, ?_, hhom, fun Q hQ => ?_⟩
  · -- `1 ≤ K`: a quadrilateral in the finite core and its relabelling
    obtain ⟨g, hg⟩ := hGd.2.nonempty
    obtain ⟨z, hz⟩ := OnePoint.denseRange_coe.exists_mem_open hGd.1 ⟨g, hg⟩
    have hzo : IsOpen (((↑) : ℂ → ExtPlane) ⁻¹' G) := hGd.1.preimage OnePoint.continuous_coe
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hzo z hz
    have hz' : ((z + ε / 2 : ℂ) : ExtPlane) ∈ G := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [show (ε / 2 : ℂ) = ((ε / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith)
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, (z₀ : ExtPlane) ∈ G ∧ w z₀ ≠ extInf := by
      by_cases h : w z = extInf
      · refine ⟨z + ε / 2, hz', fun h' => ?_⟩
        have := hwsp.1.2.1 hz hz' (h.trans h'.symm)
        have h2 := OnePoint.coe_injective this
        have : (ε / 2 : ℂ) = 0 := by linear_combination -h2
        have : ε = 0 := by exact_mod_cast (by linear_combination 2 * this : (ε : ℂ) = 0)
        linarith
      · exact ⟨z, hz, h⟩
    obtain ⟨Q, -, hQ⟩ := LiZhongQC.exists_topQuad_mem_closure_subset hDo hz₀
    obtain ⟨Q', hQ'⟩ := lv13_image_isTopQuad hGd.1 hwsp Q hQ
    have h1 := lv13_modulus_le ⟨hGd, hwsp, hK⟩ hQ hQ'
    have h2 := lv13_modulus_le ⟨hGd, hwsp, hK⟩ (Q := Q.rotate) (Q' := Q'.rotate) hQ
      ⟨hQ'.1, fun i => hQ'.2 (i + 1)⟩
    rw [LiZhongQC.thm1_2_modulus_rotate Q, LiZhongQC.thm1_2_modulus_rotate Q'] at h1
    have hp := LiZhongQC.modulus_pos Q.rotate
    have hp' := LiZhongQC.modulus_pos Q'.rotate
    have h1' : Q.rotate.modulus ≤ K * Q'.rotate.modulus := by
      calc Q.rotate.modulus = 1 / Q'.rotate.modulus * (Q.rotate.modulus * Q'.rotate.modulus) := by
            field_simp
        _ ≤ K * (1 / Q.rotate.modulus) * (Q.rotate.modulus * Q'.rotate.modulus) :=
            mul_le_mul_of_nonneg_right h1 (mul_pos hp hp').le
        _ = K * Q'.rotate.modulus := by
            field_simp
    have hK0 : 0 ≤ K := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hK0]
  · obtain ⟨Q', hQ'⟩ := lv13_image_isTopQuad hGd.1 hwsp Q hQ
    exact ⟨Q', hQ', lv13_modulus_le ⟨hGd, hwsp, hK⟩ hQ hQ'⟩

/-! ## Converse bridge, stage 1: LV quadrilaterals as Li Zhong quadrilaterals -/

/-- Helper (converse bridge C1). An LV quadrilateral `Q` whose closure avoids `∞` is a Li Zhong quadrilateral: its
domain is `toExt D` for a bounded plane Jordan domain `D`, and its vertices `z₁, …, z₄` are in Li Zhong's cyclic order
(the converse of `lv13_isPositivelyOrdered_of_isTopQuad`). The LV-positive triples `(z₁, z₂, z₃)`, `(z₁, z₃, z₄)` are
carried to the canonical parametrization of `D` by `lv13_same_order`, whence the cyclic order of the real coordinates
of a uniformizer (`lv13_cyclic3`, `lv13_cyclicStrictMono_of_triples`). -/
theorem lv13_isTopQuad_of_quadrilateral (Q : Quadrilateral) (hQ : extInf ∉ closure Q.dom) :
    ∃ D : Set ℂ, Q.dom = toExt D ∧ Bornology.IsBounded D ∧ LiZhongQC.IsTopQuad D Q.vert := by
  -- the finite part `D` of `Q`
  set D : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' Q.dom with hDdef
  have hinf : extInf ∉ Q.dom := fun h => hQ (subset_closure h)
  have hQD : Q.dom = toExt D := by
    ext q
    induction q using OnePoint.rec with
    | infty =>
      constructor
      · intro h
        exact absurd h hinf
      · rintro ⟨x, -, hx⟩
        exact absurd hx (OnePoint.coe_ne_infty x)
    | coe x =>
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        rw [← OnePoint.coe_injective hyx]
        exact hy
  have hb : Bornology.IsBounded D := LiZhongQC.isBounded_of_extInf_notMem_closure_toExt (by rwa [← hQD])
  -- `D` is a plane Jordan domain
  obtain ⟨⟨hGo, hGc⟩, hGJ⟩ := Q.isJordanDomain
  have hJD : LiZhongQC.IsJordanDomain D := by
    refine ⟨hGo.preimage OnePoint.continuous_coe, ?_, by rw [← hQD]; exact hGJ⟩
    rw [hQD] at hGc
    exact ⟨hGc.1.of_image, OnePoint.isOpenEmbedding_coe.toIsInducing.isPreconnected_image.1 hGc.2⟩
  have hvfr : ∀ i, Q.vert i ∈ frontier (toExt D) := fun i => hQD ▸ Q.vert_mem i
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := LiZhongQC.exists_conformalOnto_upperHalf_of_isJordanDomain hJD hb
  obtain ⟨ψ', Ψ', y, hψ', hΨ', hΨ'v⟩ := LiZhongQC.exists_uniformizer_finite_vertices hJD.1 hψ hΨ hvfr
  suffices hy : LiZhongQC.CyclicStrictMono y from ⟨D, hQD, hb, hJD, hvfr, ψ', Ψ', y, hψ', hΨ', hy, hΨ'v⟩
  -- the LV-positive vertex triples of `Q`
  obtain ⟨γ, hγ, a, s, hs, hsI, hγs⟩ := Q.positive
  rw [hQD] at hγ
  -- the canonical parametrization of `D` through the uniformizer `Ψ′`
  obtain ⟨c, hc, -, σ, hσ, hσ01, hcσ⟩ := lv13_canonical_param hJD hb hψ' hΨ'
  have hcl : ∀ t, c t ∈ closure (toExt D) := fun t =>
    frontier_subset_closure (hc.1.2.2.2 ▸ mem_range_self t)
  have hcv : ∀ i, c (σ (y i)) = Q.vert i := fun i =>
    hΨ'.2.2.1 (hcl _) (frontier_subset_closure (hvfr i)) (by rw [hcσ]; exact (hΨ'v i).symm)
  have hcmod : ∀ t t', c t = c t' → ∃ n : ℤ, t = t' + n := fun t t' h => by
    have hpf : ∀ u, c (Int.fract u) = c u := fun u => by
      rw [show Int.fract u = u - (⌊u⌋ : ℤ) * (1 : ℝ) by rw [Int.fract]; ring]
      exact hc.1.2.1.sub_int_mul_eq ⌊u⌋
    have h' := hc.1.2.2.1 ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ ⟨Int.fract_nonneg t', Int.fract_lt_one t'⟩
      (by rw [hpf, hpf, h])
    refine ⟨⌊t⌋ - ⌊t'⌋, ?_⟩
    rw [Int.fract, Int.fract] at h'
    push_cast
    linarith
  -- each increasing index triple has its real coordinates in cyclic order
  have hcyc : ∀ e : Fin 3 → Fin 4, StrictMono e →
      (y (e 0) < y (e 1) ∧ y (e 1) < y (e 2)) ∨ (y (e 1) < y (e 2) ∧ y (e 2) < y (e 0)) ∨
        (y (e 2) < y (e 0) ∧ y (e 0) < y (e 1)) := fun e he => by
    obtain ⟨b, s', hs', hs'I, hcs'⟩ := lv13_same_order hJD hb hγ hc (hs.comp he) (fun j => hsI (e j))
      (p := Q.vert ∘ e) (fun j => hγs (e j))
    have hst : ∀ j, ∃ n : ℤ, s' j = σ (y (e j)) + n := fun j =>
      hcmod _ _ ((hcs' j).trans (hcv (e j)).symm)
    have h := lv13_cyclic3 (t := fun j => σ (y (e j))) (fun j => ⟨(hσ01 _).1.le, (hσ01 _).2⟩) hs' hs'I hst
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩
    · exact Or.inr (Or.inl ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩)
    · exact Or.inr (Or.inr ⟨hσ.lt_iff_lt.1 h1, hσ.lt_iff_lt.1 h2⟩)
  have h012 := hcyc ![0, 1, 2] (by decide)
  have h023 := hcyc ![0, 2, 3] (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h012 h023
  exact lv13_cyclicStrictMono_of_triples h012 h023

end LehtoVirtanen1973
