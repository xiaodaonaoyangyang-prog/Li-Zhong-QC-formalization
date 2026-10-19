import References.GarnettMarshall2005.Ch02.S03_ConjugateFunctions

/-!
# Garnett–Marshall, Chapter II §4: Boundary smoothness

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. II §4 (pp. 59–66;
`full.md` P1:2696–2947).

Standing assumption of the section (P1:2698): `Ω` is a Jordan domain with boundary `Γ`, and `φ` is a conformal
mapping from `𝔻` onto `Ω`, extended to a homeomorphism of `∂𝔻` onto the Jordan curve `Γ = ∂Ω`.
Modelling (leader ruling Q10): `Ω` is a bounded plane Jordan domain (`LiZhongQC.IsJordanDomain`, bounded), since
the objects of the section (`φ ∈ C^α(∂𝔻)`, `C^{k+α}(𝔻̄)`, tangents, arc length of `Γ`) need finite values; `φ` is
`LiZhongQC.IsConformalOnto φ 𝔻 Ω` and `Φ` its continuous extension to `𝔻̄` (the bundle `IsJordanDiscMap Ω φ Φ`).
`arg` of a zero-free function `q` on `𝔻` is a continuous branch `v` with `e^{iv} = q/|q|` (`IsArgBranch`); two
branches differ by a constant `2πk`, so the statements do not depend on the branch. Corollaries 4.6 and 4.7 are for
finitely connected domains bounded by `C^{k+α}` Jordan curves `Γ_1, …, Γ_p`, taken as explicit hypotheses so that
conditions "on each component" can be stated. Conventions of §1–§3 otherwise.

* Theorem 4.1 (§4) — `thm2_4_1`
* Definition ((4.1), (4.2): tangent and unit tangent vector of a parametrized arc; continuous tangent of a Jordan
  curve, §4, P1:2706–2718) — `HasTangentAt`, `HasContinuousTangent` (B-cand. Pommerenke1992.IsTangentDirection, the
  same two limits required at every parameter at once; Pommerenke1992.HasTangentAt, a corner of opening π at the
  image of one boundary point of the disc; Pommerenke1992.IsSmoothJordanCurve, a regular C¹ parametrization, equal to
  a continuously varying tangent by the Pommerenke claim eq3_2_1)
* Theorem 4.2 (§4; (4.3), (4.4)) — `thm2_4_2_i`, `thm2_4_2_ii`, `thm2_4_2_iii` (B-cand. for the first part
  Pommerenke1992.thm3_7 at α = 1, Lindelöf's theorem for a corner of opening π, Pommerenke1992.HasTangentAt, at the
  image of one boundary point, for a locally connected boundary; for the second part Pommerenke1992.thm3_2_a,
  stated for smooth curves)
* Definition (`C^{k+α}` for functions of a real variable, used for the arc length parametrization, P1:2826, and in
  Lemma 4.4, §4) — `MemCkAlphaOn`
* Definition (curve of class `C^{k+α}`, §4, P1:2820–2826) — `IsArcLengthParam`, `IsCurveOfClass` (B-cand.
  Pommerenke1992.IsJordanCurveCnAlpha, some regular periodic parametrization with Hölder n-th derivative: equivalent
  after reparametrization by arc length, a lemma)
* Theorem 4.3 (Kellogg, §4) — `thm2_4_3` (B-cand. Pommerenke1992.thm3_6, the implication from a C^{n,α} curve to a
  Hölder continuous n-th derivative on the closed disc, without the zero-freeness of the derivative;
  Pommerenke1992.kellogg_warschawski, the C^∞ form)
* Lemma 4.4 (§4) — `lemma2_4_4`
* Definition (`f ∈ C^{l+β}(Γ)` for a curve `Γ` of class `C^{k+α}`, §4, P1:2884) — `MemCkAlphaOnCurve`
* Definition (`F ∈ C^{n+σ}(Ω̄)` for analytic `F` on `Ω`, §4, Corollary 4.5, the analogue of `C^{k+α}(𝔻̄)`) —
  `MemCkAlphaClosure`
* Corollary 4.5 (§4) — `cor2_4_5`
* Corollary 4.6 (§4) — `cor2_4_6`
* Corollary 4.7 (§4; (4.8), (4.9)) — `cor2_4_7`

Helpers (not book notions): `IsJordanDiscMap` (the standing assumption), `IsArgBranch` (a continuous branch of `arg`).

Not stated (inventory U−): the results do not depend on the choice of `φ` (P1:2700, a remark: any other map is `φ ∘ T`,
`T` a Möbius self-map of `𝔻`); the existence of a tangent and its value do not depend on the parametrization, up to
orientation (P1:2718); the example of a Jordan domain with continuous tangent but `φ ∉ C¹(∂𝔻)` (P1:2734); the bound
(4.5) inside the proof of Theorem 4.2, reused in the proof of Theorem 4.3 (a proof step with proof-local constants);
for `α = 0` and `k ≥ 1`, (a) ⇔ (b) in Kellogg's theorem but (a) does not imply (c) (P1:2836, not cited); the remark
that Corollary 4.5 holds for finitely connected Jordan domains without conjugates (P1:2890; Corollary 4.6 is that
form); for `C¹` boundaries `ω` is absolutely continuous to arc length with a density that may be discontinuous,
unbounded or not bounded below (P1:2944, Exercise 14), and the pointer to Exercise 20 (P1:2946). (4.6) and (4.7) are
steps of the proof of Theorem 4.3.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open References (IsDomainExt)

/-- The standing assumption of Ch. II §4 (P1:2698; helper): `Ω` is a bounded Jordan domain, `φ` maps `𝔻` conformally
onto `Ω`, and `Φ` is the continuous extension of `φ` to `𝔻̄` (by Carathéodory's theorem a homeomorphism of `𝔻̄` onto
`Ω̄` mapping `∂𝔻` onto `Γ = ∂Ω`). -/
def IsJordanDiscMap (Ω : Set ℂ) (φ Φ : ℂ → ℂ) : Prop :=
  LiZhongQC.IsJordanDomain Ω ∧ Bornology.IsBounded Ω ∧ IsConformalOnto φ unitDisc Ω ∧
    ContinuousOn Φ (closedBall 0 1) ∧ EqOn Φ φ unitDisc

/-- **Theorem 4.1** (Ch. II §4; cited at P1:2900). Let `Ω₁` and `Ω₂` be Jordan domains such that `Ω₁ ⊆ Ω₂` and let
`γ ⊆ ∂Ω₁ ∩ ∂Ω₂` be an open subarc. Let `φ_j` be a conformal map of `𝔻` onto `Ω_j`. Then `ψ = φ₂⁻¹ ∘ φ₁` has an
analytic continuation across `φ₁⁻¹(γ)`, and `ψ' ≠ 0` on `φ₁⁻¹(γ)`.
Modelling: bounded Jordan domains (standing assumption); `γ` is an open Jordan arc; `φ₁⁻¹(γ)` is the set of
`ζ ∈ ∂𝔻` with `Φ₁(ζ) ∈ γ` for the continuous extension `Φ₁`; the continuation `Ψ` is analytic on an open set
containing `𝔻 ∪ φ₁⁻¹(γ)` and equals `φ₂⁻¹ ∘ φ₁` on `𝔻`, written `Ψ(𝔻) ⊆ 𝔻` and `φ₂ ∘ Ψ = φ₁` on `𝔻`. -/
theorem thm2_4_1 {Ω₁ Ω₂ : Set ℂ} {φ₁ Φ₁ φ₂ Φ₂ : ℂ → ℂ} (h₁ : IsJordanDiscMap Ω₁ φ₁ Φ₁)
    (h₂ : IsJordanDiscMap Ω₂ φ₂ Φ₂) (h₁₂ : Ω₁ ⊆ Ω₂) {γ : Set ℂ}
    (hγ : LehtoVirtanen1973.IsOpenJordanArc (toExt γ)) (hγΩ : γ ⊆ frontier Ω₁ ∩ frontier Ω₂) :
    ∃ (U : Set ℂ) (Ψ : ℂ → ℂ), IsOpen U ∧ unitDisc ∪ {ζ ∈ sphere (0 : ℂ) 1 | Φ₁ ζ ∈ γ} ⊆ U ∧
      AnalyticOnNhd ℂ Ψ U ∧ (∀ z ∈ unitDisc, Ψ z ∈ unitDisc ∧ φ₂ (Ψ z) = φ₁ z) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, Φ₁ ζ ∈ γ → deriv Ψ ζ ≠ 0 := by
  sorry

/-- **Definition** ((4.1), (4.2), tangent, Ch. II §4, P1:2706–2718). Let `Γ` be an arc parametrized as
`{ζ(t) : a < t < b}`. `Γ` has a tangent at `ζ₀ = ζ(t₀)` if (4.1) `lim_{t↓t₀} (ζ(t) − ζ₀)/|ζ(t) − ζ₀| = e^{iτ}` and
(4.2) `lim_{t↑t₀} (ζ(t) − ζ₀)/|ζ(t) − ζ₀| = −e^{iτ}`; then `Γ` has unit tangent vector `e^{iτ}` at `ζ₀`.
Modelling: a predicate on the parametrization `ζ : ℝ → ℂ`, the parameter `t₀` and the angle `τ`. -/
def HasTangentAt (ζ : ℝ → ℂ) (t₀ τ : ℝ) : Prop :=
  Tendsto (fun t => (ζ t - ζ t₀) / (‖ζ t - ζ t₀‖ : ℂ)) (𝓝[>] t₀) (𝓝 (Complex.exp (τ * I))) ∧
    Tendsto (fun t => (ζ t - ζ t₀) / (‖ζ t - ζ t₀‖ : ℂ)) (𝓝[<] t₀) (𝓝 (-Complex.exp (τ * I)))

/-- **Definition** (continuous tangent, Ch. II §4, P1:2718). The Jordan curve `Γ` has a continuous tangent if `Γ` has
a tangent at each `ζ ∈ Γ` and if `e^{iτ(ζ)}` is continuous on `Γ`.
Modelling: `Γ ⊆ ℂ`, with a tangent at every point for one loop parametrization (`LehtoVirtanen1973.IsLoopParam`) and
the unit tangent vector `e^{iτ(ζ)}`, as a function of the point `ζ ∈ Γ`, continuous on `Γ`. -/
def HasContinuousTangent (Γ : Set ℂ) : Prop :=
  ∃ (γ : ℝ → ℂ) (τ : ℂ → ℝ), LehtoVirtanen1973.IsLoopParam (toExt Γ) (fun t => (γ t : ExtPlane)) ∧
    (∀ t : ℝ, HasTangentAt γ t (τ (γ t))) ∧ ContinuousOn (fun w => Complex.exp (τ w * I)) Γ

/-- A continuous branch of `arg q` on `U` (helper, Ch. II §4): `v` is continuous on `U` and `e^{iv(z)} = q(z)/|q(z)|`
for `z ∈ U` (which forces `q ≠ 0` on `U`). -/
def IsArgBranch (v : ℂ → ℝ) (q : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ContinuousOn v U ∧ ∀ z ∈ U, Complex.exp (v z * I) = q z / (‖q z‖ : ℂ)

/-- **Theorem 4.2** (Ch. II §4), first part ((4.3), (4.4); cited at P1:2870, in V, P1:7554, and in VI, P2:801, 1081).
The curve `Γ` has a tangent at `ζ = φ(e^{iθ})` if and only if the limit (4.3)
`lim_{𝔻∋z→e^{iθ}} arg((φ(z) − ζ)/(z − e^{iθ}))` exists and is finite. In that case (4.4) the limit is
`τ(ζ) − θ − π/2`.
Modelling: the parametrization of `Γ` is `t ↦ φ(e^{it})` (the extension `Φ` on `∂𝔻`; the tangent does not depend on
the parametrization, P1:2718), so `τ` is measured for the counterclockwise orientation; `arg` is a continuous branch
on `𝔻` of the zero-free function `(φ(z) − ζ)/(z − e^{iθ})`, and (4.4) holds modulo `2π` (the branch and `τ` are
determined up to `2πk`). The formula (4.4) was checked against the equation image. -/
theorem thm2_4_2_i {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ) (θ : ℝ) :
    ((∃ τ : ℝ, HasTangentAt (fun t => Φ (circleMap 0 1 t)) θ τ) ↔
      ∃ v : ℂ → ℝ, IsArgBranch v (fun z => (φ z - Φ (circleMap 0 1 θ)) / (z - circleMap 0 1 θ)) unitDisc ∧
        ∃ L : ℝ, Tendsto v (𝓝[unitDisc] (circleMap 0 1 θ)) (𝓝 L)) ∧
    ∀ τ : ℝ, HasTangentAt (fun t => Φ (circleMap 0 1 t)) θ τ →
      ∀ v : ℂ → ℝ, IsArgBranch v (fun z => (φ z - Φ (circleMap 0 1 θ)) / (z - circleMap 0 1 θ)) unitDisc →
        ∀ L : ℝ, Tendsto v (𝓝[unitDisc] (circleMap 0 1 θ)) (𝓝 L) → ∃ m : ℤ, L = τ - θ - π / 2 + 2 * π * m := by
  sorry

/-- **Theorem 4.2** (Ch. II §4), second part. The curve `Γ` has a continuous tangent if and only if `arg φ'(z)` has a
continuous extension to `𝔻̄`.
Modelling: `arg φ'` is a continuous branch on `𝔻` of `arg` of the zero-free derivative `φ'`, and it extends
continuously to the closed disc. -/
theorem thm2_4_2_ii {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ) :
    HasContinuousTangent (frontier Ω) ↔
      ∃ v : ℂ → ℝ, IsArgBranch v (deriv φ) unitDisc ∧
        ∃ V : ℂ → ℝ, ContinuousOn V (closedBall 0 1) ∧ EqOn V v unitDisc := by
  sorry

/-- **Theorem 4.2** (Ch. II §4), third part. If `Γ` has a continuous tangent, then `φ ∈ C^α(∂𝔻)` for all `α < 1`
and `Γ` is rectifiable.
Modelling: `φ` on `∂𝔻` is the extension `Φ`, and `C^α` is the Lipschitz class of §3 (for complex values), for every
`α ∈ (0, 1)` (the book's range of `C^α`); rectifiable is finite variation of the parametrization `θ ↦ φ(e^{iθ})`
over a period. -/
theorem thm2_4_2_iii {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ)
    (hΓ : HasContinuousTangent (frontier Ω)) :
    (∀ α : ℝ, 0 < α → α < 1 → MemLipschitzClass α Φ) ∧
      BoundedVariationOn (fun θ : ℝ => Φ (circleMap 0 1 θ)) (Icc 0 (2 * π)) := by
  sorry

/-- **Definition** (`C^{k+α}` for a function of a real variable, Ch. II §4, P1:2826 and Lemma 4.4, P1:2838; the
analogue for intervals of `C^{k+α}(∂𝔻)`, §3). For an integer `k ≥ 0` and `0 ≤ α < 1`, `f` is `k` times continuously
differentiable on `s` and its `k`-th derivative is in `C^α` (Hölder of exponent `α`) if `α > 0`.
Modelling: derivatives within `s` (one-sided at the ends of a closed interval); the Hölder condition with one
constant on all of `s` (for the `ℓ`-periodic arc length parametrization, `s = ℝ`). -/
def MemCkAlphaOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (α : ℝ) (f : ℝ → V) (s : Set ℝ) :
    Prop :=
  ContDiffOn ℝ k f s ∧ (0 < α → ∃ C : ℝ, ∀ x ∈ s, ∀ y ∈ s,
    ‖iteratedDerivWithin k f s x - iteratedDerivWithin k f s y‖ ≤ C * |x - y| ^ α)

/-- The arc length parametrization of a closed rectifiable curve (Ch. II §4, P1:2822; helper):
`Γ = {γ(s) : 0 ≤ s ≤ ℓ(Γ) = length(Γ)}`, with `γ` extended `ℓ`-periodically, one-to-one on `[0, ℓ)`, and the length of
`γ` on `[s₁, s₂]` equal to `s₂ − s₁`. -/
def IsArcLengthParam (Γ : Set ℂ) (ℓ : ℝ) (γ : ℝ → ℂ) : Prop :=
  0 < ℓ ∧ Function.Periodic γ ℓ ∧ InjOn γ (Ico 0 ℓ) ∧ γ '' Ico 0 ℓ = Γ ∧
    ∀ s₁ s₂ : ℝ, s₁ ≤ s₂ → eVariationOn γ (Icc s₁ s₂) = ENNReal.ofReal (s₂ - s₁)

/-- **Definition** (curve of class `C^{k+α}`, Ch. II §4, P1:2820–2826). Let `k` be a non-negative integer and let
`0 ≤ α < 1`. The curve `Γ` is of class `C^{k+α}` if `Γ` is rectifiable and if, in the arc length parametrization
`Γ = {γ(s) : 0 ≤ s ≤ ℓ(Γ)}`, the function `γ` is `k` times continuously differentiable and `d^kγ/ds^k ∈ C^α` if
`α > 0`.
Modelling: a Jordan curve in `ℂ` (the book's curves are the boundary curves of Jordan domains); the arc length
parametrization is `ℓ(Γ)`-periodic, so the smoothness includes the closing point. -/
def IsCurveOfClass (k : ℕ) (α : ℝ) (Γ : Set ℂ) : Prop :=
  ∃ (ℓ : ℝ) (γ : ℝ → ℂ), IsArcLengthParam Γ ℓ γ ∧ MemCkAlphaOn k α γ univ

/-- **Theorem 4.3** (Kellogg; Ch. II §4; cited at P1:2854, 2888, 2942, in the Notes P1:2950, and in App. B, P3:2736,
App. C, P3:3019). Let `k ≥ 1` and `0 < α < 1`. Then the following conditions are equivalent: (a) `Γ` is of class
`C^{k+α}`; (b) `arg φ' ∈ C^{k−1+α}(∂𝔻)`; (c) `φ ∈ C^{k+α}(𝔻̄)` and `φ' ≠ 0` on `𝔻̄`.
Modelling: (b) a continuous branch of `arg φ'` on `𝔻` extends continuously to `𝔻̄`, and its boundary function is in
`C^{k−1+α}(∂𝔻)`; (c) `φ' ≠ 0` on `𝔻̄` is the zero-freeness of the continuous extension of `φ'`. -/
theorem thm2_4_3 {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ) {k : ℕ} (hk : 1 ≤ k) {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    List.TFAE [IsCurveOfClass k α (frontier Ω),
      ∃ v : ℂ → ℝ, ContinuousOn v (closedBall 0 1) ∧ IsArgBranch v (deriv φ) unitDisc ∧
        MemCkAlphaCircle (k - 1) α v,
      MemCkAlphaClosedDisc k α φ ∧ ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧ EqOn G (deriv φ) unitDisc ∧
        ∀ z ∈ closedBall (0 : ℂ) 1, G z ≠ 0] := by
  sorry

/-- Helper (Ch. II §4, Lemma 4.4). A Lipschitz function on a compact interval is `α`-Hölder for `0 < α < 1`. -/
theorem gm24_lip_holder {a b : ℝ} (hab : a < b) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {v : ℝ → ℝ} {L : ℝ}
    (hv : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |v x - v y| ≤ L * |x - y|) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |v x - v y| ≤ C * |x - y| ^ α := by
  have hL : 0 ≤ L := by
    have := hv a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    have h2 : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab.ne)
    by_contra hneg
    push Not at hneg
    nlinarith [abs_nonneg (v a - v b)]
  refine ⟨L * (b - a) ^ (1 - α), fun x hx y hy => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simp [Real.zero_rpow hα₀.ne']
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have hle : |x - y| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have h1 : |x - y| = |x - y| ^ α * |x - y| ^ (1 - α) := by
    rw [← Real.rpow_add hpos]; simp
  have h2 : |x - y| ^ (1 - α) ≤ (b - a) ^ (1 - α) :=
    Real.rpow_le_rpow hpos.le hle (by linarith)
  calc |v x - v y| ≤ L * |x - y| := hv x hx y hy
    _ = L * (|x - y| ^ α * |x - y| ^ (1 - α)) := by rw [← h1]
    _ ≤ L * (|x - y| ^ α * (b - a) ^ (1 - α)) := by
        gcongr
    _ = L * (b - a) ^ (1 - α) * |x - y| ^ α := by ring

/-- Helper (Ch. II §4, Lemma 4.4). Congruence on the interval (proved form). -/
theorem gm24_congr_aux {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} {u v : ℝ → ℝ} (huv : EqOn u v (Icc a b))
    (hu : MemCkAlphaOn m α u (Icc a b)) : MemCkAlphaOn m α v (Icc a b) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨h1.congr huv.symm, fun hα => ?_⟩
  obtain ⟨C, hC⟩ := h2 hα
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← iteratedDerivWithin_congr huv hx, ← iteratedDerivWithin_congr huv hy]
  exact hC x hx y hy

/-- Helper (Ch. II §4, Lemma 4.4). A `C¹` function on a compact interval is Lipschitz. -/
theorem gm24_lip {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg1 : ContDiffOn ℝ 1 g (Icc a b)) :
    ∃ L : ℝ, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g x - g y| ≤ L * |x - y| := by
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hd : DifferentiableOn ℝ g (Icc a b) := hg1.differentiableOn (by simp)
  have hc : ContinuousOn (derivWithin g (Icc a b)) (Icc a b) := hg1.continuousOn_derivWithin hs le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc
  refine ⟨M, fun x hx y hy => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℝ) (f := g) (s := Icc a b) hd hM
    (convex_Icc a b) hy hx
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- Helper (Ch. II §4, Lemma 4.4). Sums of `C^{m+α}` functions are `C^{m+α}`. -/
theorem gm24_add_aux {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} {u v : ℝ → ℝ}
    (hu : MemCkAlphaOn m α u (Icc a b)) (hv : MemCkAlphaOn m α v (Icc a b)) :
    MemCkAlphaOn m α (fun x => u x + v x) (Icc a b) := by
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  obtain ⟨h1, h2⟩ := hu
  obtain ⟨h1', h2'⟩ := hv
  refine ⟨h1.add h1', fun hα => ?_⟩
  obtain ⟨C, hC⟩ := h2 hα
  obtain ⟨C', hC'⟩ := h2' hα
  refine ⟨C + C', fun x hx y hy => ?_⟩
  rw [iteratedDerivWithin_fun_add hx hs (h1 x hx) (h1' x hx), iteratedDerivWithin_fun_add hy hs (h1 y hy) (h1' y hy)]
  have e1 := hC x hx y hy
  have e2 := hC' x hx y hy
  have e3 := norm_add_le (iteratedDerivWithin m u (Icc a b) x - iteratedDerivWithin m u (Icc a b) y)
    (iteratedDerivWithin m v (Icc a b) x - iteratedDerivWithin m v (Icc a b) y)
  have e4 : iteratedDerivWithin m u (Icc a b) x + iteratedDerivWithin m v (Icc a b) x -
      (iteratedDerivWithin m u (Icc a b) y + iteratedDerivWithin m v (Icc a b) y) =
      (iteratedDerivWithin m u (Icc a b) x - iteratedDerivWithin m u (Icc a b) y) +
        (iteratedDerivWithin m v (Icc a b) x - iteratedDerivWithin m v (Icc a b) y) := by ring
  rw [e4]
  nlinarith [e1, e2, e3]

/-- Helper (Ch. II §4, Lemma 4.4). `C^{m+1+α}` on a compact interval means: differentiable, with derivative in
`C^{m+α}`. -/
theorem gm24_succ_iff {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} {u : ℝ → ℝ} :
    MemCkAlphaOn (m + 1) α u (Icc a b) ↔
      DifferentiableOn ℝ u (Icc a b) ∧ MemCkAlphaOn m α (derivWithin u (Icc a b)) (Icc a b) := by
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  unfold MemCkAlphaOn
  have hc : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u (Icc a b) ↔
      DifferentiableOn ℝ u (Icc a b) ∧ ContDiffOn ℝ (m : WithTop ℕ∞) (derivWithin u (Icc a b)) (Icc a b) := by
    have := contDiffOn_succ_iff_derivWithin (n := (m : WithTop ℕ∞)) (f := u) hs
    push_cast
    rw [this]
    simp
  have hit : ∀ x ∈ Icc a b, iteratedDerivWithin (m + 1) u (Icc a b) x =
      iteratedDerivWithin m (derivWithin u (Icc a b)) (Icc a b) x := fun x hx =>
    by rw [iteratedDerivWithin_succ']
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨hd, hcd⟩ := hc.1 h1
    refine ⟨hd, hcd, fun hα => ?_⟩
    obtain ⟨C, hC⟩ := h2 hα
    exact ⟨C, fun x hx y hy => by rw [← hit x hx, ← hit y hy]; exact hC x hx y hy⟩
  · rintro ⟨hd, hcd, h2⟩
    refine ⟨hc.2 ⟨hd, hcd⟩, fun hα => ?_⟩
    obtain ⟨C, hC⟩ := h2 hα
    exact ⟨C, fun x hx y hy => by rw [hit x hx, hit y hy]; exact hC x hx y hy⟩

/-- Helper (Ch. II §4, Lemma 4.4). A `C^{m+1}` function on a compact interval is in `C^{m+α}` for `α < 1`: its `m`-th
derivative is Lipschitz, hence Hölder. -/
theorem gm24_of_contDiff {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} (hα₁ : α < 1) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (m + 1) u (Icc a b)) : MemCkAlphaOn m α u (Icc a b) := by
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hcm : ContDiffOn ℝ (m : WithTop ℕ∞) u (Icc a b) := hu.of_le (by exact_mod_cast Nat.le_succ m)
  refine ⟨hcm, fun hα => ?_⟩
  set v : ℝ → ℝ := iteratedDerivWithin m u (Icc a b) with hv
  have hvd : DifferentiableOn ℝ v (Icc a b) :=
    hu.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self m) hs
  have hvc : ContinuousOn (derivWithin v (Icc a b)) (Icc a b) := by
    have h1 : ContinuousOn (iteratedDerivWithin (m + 1) u (Icc a b)) (Icc a b) :=
      hu.continuousOn_iteratedDerivWithin le_rfl hs
    refine h1.congr (fun x hx => ?_)
    rw [hv, iteratedDerivWithin_succ]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hvc
  have hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |v x - v y| ≤ M * |x - y| := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℝ) (f := v) (s := Icc a b) hvd hM
      (convex_Icc a b) hy hx
    simpa [Real.norm_eq_abs, abs_sub_comm] using this
  exact gm24_lip_holder hab hα hα₁ hlip

/-- Helper (Ch. II §4, Lemma 4.4). Products of `C^{m+α}` functions on a compact interval are in `C^{m+α}`. -/
theorem gm24_mul {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} (hα₁ : α < 1) {u v : ℝ → ℝ}
    (hu : MemCkAlphaOn m α u (Icc a b)) (hv : MemCkAlphaOn m α v (Icc a b)) :
    MemCkAlphaOn m α (fun x => u x * v x) (Icc a b) := by
  induction m generalizing u v with
  | zero =>
    obtain ⟨h1, h2⟩ := hu
    obtain ⟨h1', h2'⟩ := hv
    refine ⟨h1.mul h1', fun hα => ?_⟩
    simp only [iteratedDerivWithin_zero]
    obtain ⟨C, hC⟩ := h2 hα
    obtain ⟨C', hC'⟩ := h2' hα
    simp only [iteratedDerivWithin_zero] at hC hC'
    obtain ⟨Bu, hBu⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn h1.continuousOn
    obtain ⟨Bv, hBv⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn h1'.continuousOn
    have hab' : (a : ℝ) ∈ Icc a b := ⟨le_rfl, hab.le⟩
    have hbb' : (b : ℝ) ∈ Icc a b := ⟨hab.le, le_rfl⟩
    have hpos : 0 < |a - b| ^ α := Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hab.ne)) _
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push Not at hneg
      have := hC a hab' b hbb'
      rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg (u a - u b)]
    have hC'0 : 0 ≤ C' := by
      by_contra hneg
      push Not at hneg
      have := hC' a hab' b hbb'
      rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg (v a - v b)]
    refine ⟨Bu * C' + Bv * C, fun x hx y hy => ?_⟩
    have e1 := hC x hx y hy
    have e2 := hC' x hx y hy
    rw [Real.norm_eq_abs] at e1 e2 ⊢
    have hB1 := hBu x hx
    have hB2 := hBv y hy
    rw [Real.norm_eq_abs] at hB1 hB2
    have key : u x * v x - u y * v y = u x * (v x - v y) + v y * (u x - u y) := by ring
    rw [key]
    have ht : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
    calc |u x * (v x - v y) + v y * (u x - u y)| ≤ |u x * (v x - v y)| + |v y * (u x - u y)| := abs_add_le _ _
      _ = |u x| * |v x - v y| + |v y| * |u x - u y| := by rw [abs_mul, abs_mul]
      _ ≤ Bu * (C' * |x - y| ^ α) + Bv * (C * |x - y| ^ α) := by
          have hBu0 : 0 ≤ Bu := le_trans (norm_nonneg _) (hBu x hx)
          have hBv0 : 0 ≤ Bv := le_trans (norm_nonneg _) (hBv y hy)
          refine add_le_add ?_ ?_
          · exact mul_le_mul hB1 e2 (abs_nonneg _) hBu0
          · exact mul_le_mul hB2 e1 (abs_nonneg _) hBv0
      _ = (Bu * C' + Bv * C) * |x - y| ^ α := by ring
  | succ m ih =>
    have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
    obtain ⟨hud, hu'⟩ := (gm24_succ_iff hab).1 hu
    obtain ⟨hvd, hv'⟩ := (gm24_succ_iff hab).1 hv
    have hum : MemCkAlphaOn m α u (Icc a b) := gm24_of_contDiff hab hα₁ hu.1
    have hvm : MemCkAlphaOn m α v (Icc a b) := gm24_of_contDiff hab hα₁ hv.1
    refine (gm24_succ_iff hab).2 ⟨hud.mul hvd, ?_⟩
    have hsum := gm24_add_aux hab (ih hu' hvm) (ih hum hv')
    refine gm24_congr_aux hab (fun x hx => ?_) hsum
    exact (derivWithin_fun_mul (hud x hx) (hvd x hx)).symm

/-- Helper (Ch. II §4, Lemma 4.4). Composition of `C^{m+α}` functions (the inner one also `C¹`). -/
theorem gm24_comp {a b c d : ℝ} (hab : a < b) (hcd : c < d) {m : ℕ} {α : ℝ} (hα₁ : α < 1) {u g : ℝ → ℝ}
    (hu : MemCkAlphaOn m α u (Icc c d)) (hg : MemCkAlphaOn m α g (Icc a b)) (hg1 : ContDiffOn ℝ 1 g (Icc a b))
    (hmaps : MapsTo g (Icc a b) (Icc c d)) : MemCkAlphaOn m α (fun x => u (g x)) (Icc a b) := by
  induction m generalizing u with
  | zero =>
    obtain ⟨h1, h2⟩ := hu
    obtain ⟨L, hL⟩ := gm24_lip hab hg1
    refine ⟨contDiffOn_zero.2 ((contDiffOn_zero.1 h1).comp hg1.continuousOn hmaps), fun hα => ?_⟩
    simp only [iteratedDerivWithin_zero]
    obtain ⟨C, hC⟩ := h2 hα
    simp only [iteratedDerivWithin_zero] at hC
    have hab' : (a : ℝ) ∈ Icc a b := ⟨le_rfl, hab.le⟩
    have hbb' : (b : ℝ) ∈ Icc a b := ⟨hab.le, le_rfl⟩
    have hL0 : 0 ≤ L := by
      have := hL a hab' b hbb'
      have h2 : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab.ne)
      by_contra hneg
      push Not at hneg
      nlinarith [abs_nonneg (g a - g b)]
    have hC0 : 0 ≤ C := by
      have hcd' : (c : ℝ) ∈ Icc c d := ⟨le_rfl, hcd.le⟩
      have hdd' : (d : ℝ) ∈ Icc c d := ⟨hcd.le, le_rfl⟩
      have hpos : 0 < |c - d| ^ α := Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hcd.ne)) _
      by_contra hneg
      push Not at hneg
      have := hC c hcd' d hdd'
      rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg (u c - u d)]
    refine ⟨C * L ^ α, fun x hx y hy => ?_⟩
    have e1 := hC (g x) (hmaps hx) (g y) (hmaps hy)
    rw [Real.norm_eq_abs] at e1 ⊢
    have e2 : |g x - g y| ^ α ≤ (L * |x - y|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (hL x hx y hy) hα.le
    rw [Real.mul_rpow hL0 (abs_nonneg _)] at e2
    calc |u (g x) - u (g y)| ≤ C * |g x - g y| ^ α := e1
      _ ≤ C * (L ^ α * |x - y| ^ α) := mul_le_mul_of_nonneg_left e2 hC0
      _ = C * L ^ α * |x - y| ^ α := by ring
  | succ m ih =>
    have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
    have ht : UniqueDiffOn ℝ (Icc c d) := uniqueDiffOn_Icc hcd
    obtain ⟨hud, hu'⟩ := (gm24_succ_iff hcd).1 hu
    obtain ⟨hgd, hg'⟩ := (gm24_succ_iff hab).1 hg
    have hgm : MemCkAlphaOn m α g (Icc a b) := gm24_of_contDiff hab hα₁ hg.1
    refine (gm24_succ_iff hab).2 ⟨?_, ?_⟩
    · exact (hud.comp hgd hmaps)
    · have hprod := gm24_mul hab hα₁ (ih hu' hgm) hg'
      refine gm24_congr_aux hab (fun x hx => ?_) hprod
      exact (derivWithin_comp x (hud (g x) (hmaps hx)) (hgd x hx) hmaps).symm

/-- Helper (Ch. II §4, Lemma 4.4). Composition of a `C^{m+1}` function with a `C^{m+α}` function. -/
theorem gm24_comp_smooth {a b c d : ℝ} (hab : a < b) (hcd : c < d) {m : ℕ} {α : ℝ} (hα₁ : α < 1) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (m + 1) u (Icc c d)) (hg : MemCkAlphaOn m α g (Icc a b))
    (hmaps : MapsTo g (Icc a b) (Icc c d)) : MemCkAlphaOn m α (fun x => u (g x)) (Icc a b) := by
  cases m with
  | zero =>
    obtain ⟨h1, h2⟩ := hg
    obtain ⟨L, hL⟩ := gm24_lip hcd (by simpa using hu)
    refine ⟨contDiffOn_zero.2 ((hu.continuousOn).comp (contDiffOn_zero.1 h1) hmaps), fun hα => ?_⟩
    simp only [iteratedDerivWithin_zero]
    obtain ⟨C, hC⟩ := h2 hα
    simp only [iteratedDerivWithin_zero] at hC
    have hcd' : (c : ℝ) ∈ Icc c d := ⟨le_rfl, hcd.le⟩
    have hdd' : (d : ℝ) ∈ Icc c d := ⟨hcd.le, le_rfl⟩
    have hL0 : 0 ≤ L := by
      have := hL c hcd' d hdd'
      have h2 : 0 < |c - d| := abs_pos.2 (sub_ne_zero.2 hcd.ne)
      by_contra hneg
      push Not at hneg
      nlinarith [abs_nonneg (u c - u d)]
    refine ⟨L * C, fun x hx y hy => ?_⟩
    have e1 := hC x hx y hy
    rw [Real.norm_eq_abs] at e1 ⊢
    calc |u (g x) - u (g y)| ≤ L * |g x - g y| := hL _ (hmaps hx) _ (hmaps hy)
      _ ≤ L * (C * |x - y| ^ α) := mul_le_mul_of_nonneg_left e1 hL0
      _ = L * C * |x - y| ^ α := by ring
  | succ m' =>
    exact gm24_comp hab hcd hα₁ (gm24_of_contDiff hcd hα₁ hu) hg
      (hg.1.of_le (by exact_mod_cast Nat.succ_pos m')) hmaps

/-- Helper (Ch. II §4, Lemma 4.4). The inverse of a `C¹` function with positive derivative on `[a, b]`: it is `C¹`,
has derivative `1/f'(g(y))`, and `g (f x) = x`. -/
theorem gm24_inverse {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b))
    (hf' : ∀ x ∈ Icc a b, 0 < derivWithin f (Icc a b) x)
    (hg : ∀ y ∈ Icc (f a) (f b), g y ∈ Icc a b ∧ f (g y) = y) :
    f a < f b ∧ (∀ x ∈ Icc a b, f x ∈ Icc (f a) (f b) ∧ g (f x) = x) ∧ ContDiffOn ℝ 1 g (Icc (f a) (f b)) ∧
      ∀ y ∈ Icc (f a) (f b), derivWithin g (Icc (f a) (f b)) y = 1 / derivWithin f (Icc a b) (g y) := by
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hfd : DifferentiableOn ℝ f (Icc a b) := hf.differentiableOn (by simp)
  have hfc : ContinuousOn f (Icc a b) := hf.continuousOn
  have hmono : StrictMonoOn f (Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) hfc (fun x hx => ?_)
    rw [interior_Icc] at hx
    have : deriv f x = derivWithin f (Icc a b) x :=
      (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
    rw [this]
    exact hf' x (Ioo_subset_Icc_self hx)
  have hlt : f a < f b := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hmaps : ∀ x ∈ Icc a b, f x ∈ Icc (f a) (f b) := fun x hx =>
    ⟨hmono.monotoneOn ⟨le_rfl, hab.le⟩ hx hx.1, hmono.monotoneOn hx ⟨hab.le, le_rfl⟩ hx.2⟩
  have hgf : ∀ x ∈ Icc a b, g (f x) = x := by
    intro x hx
    obtain ⟨hg1, hg2⟩ := hg (f x) (hmaps x hx)
    exact hmono.injOn hg1 hx hg2
  have hgmaps : MapsTo g (Icc (f a) (f b)) (Icc a b) := fun y hy => (hg y hy).1
  have hgmono : StrictMonoOn g (Icc (f a) (f b)) := by
    intro y1 hy1 y2 hy2 h12
    by_contra hge
    push Not at hge
    have := hmono.monotoneOn (hg y2 hy2).1 (hg y1 hy1).1 hge
    rw [(hg y2 hy2).2, (hg y1 hy1).2] at this
    exact absurd h12 (not_lt.2 this)
  -- continuity of `g`
  haveI : Nonempty ℝ := ⟨0⟩
  have himg : f '' Icc a b = Icc (f a) (f b) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmaps x hx
    · intro hy
      exact ⟨g y, (hg y hy).1, (hg y hy).2⟩
  have hinvc : ContinuousOn (Function.invFunOn f (Icc a b)) (Icc (f a) (f b)) := by
    have := LiZhongQC.continuousOn_invFunOn_image_of_isCompact (isCompact_Icc (a := a) (b := b)) hfc hmono.injOn
    rwa [himg] at this
  have hgeq : ∀ y ∈ Icc (f a) (f b), g y = Function.invFunOn f (Icc a b) y := by
    intro y hy
    have h1 := Function.invFunOn_pos (f := f) (s := Icc a b) (b := y) ⟨g y, (hg y hy).1, (hg y hy).2⟩
    exact hmono.injOn (hg y hy).1 h1.1 ((hg y hy).2.trans h1.2.symm)
  have hgc : ContinuousOn g (Icc (f a) (f b)) := hinvc.congr hgeq
  -- derivative
  have hderiv : ∀ y ∈ Icc (f a) (f b), HasDerivWithinAt g (1 / derivWithin f (Icc a b) (g y))
      (Icc (f a) (f b)) y := by
    intro y0 hy0
    set x0 := g y0 with hx0
    have hx0m : x0 ∈ Icc a b := (hg y0 hy0).1
    have hfx0 : HasDerivWithinAt f (derivWithin f (Icc a b) x0) (Icc a b) x0 :=
      (hfd x0 hx0m).hasDerivWithinAt
    have hpos := hf' x0 hx0m
    rw [hasDerivWithinAt_iff_tendsto_slope] at hfx0 ⊢
    have hgt : Tendsto g (𝓝[Icc (f a) (f b) \ {y0}] y0) (𝓝[Icc a b \ {x0}] x0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((hgc y0 hy0).tendsto.mono_left (nhdsWithin_mono _ Set.diff_subset))
      · filter_upwards [self_mem_nhdsWithin] with y hy
        refine ⟨hgmaps hy.1, fun h => hy.2 ?_⟩
        have : g y = g y0 := h
        exact hgmono.injOn hy.1 hy0 this
    have h1 := (hfx0.comp hgt).inv₀ hpos.ne'
    refine (h1.congr' ?_).trans (by rw [one_div])
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyne : y - y0 ≠ 0 := sub_ne_zero.2 hy.2
    have hxne : g y - x0 ≠ 0 := by
      intro h0
      exact hy.2 (hgmono.injOn hy.1 hy0 (sub_eq_zero.1 h0))
    simp only [Function.comp, slope_def_field, hx0]
    have e1 : f (g y) = y := (hg y hy.1).2
    have e2 : f (g y0) = y0 := (hg y0 hy0).2
    rw [e1, e2]
    field_simp
  have hgd : ∀ y ∈ Icc (f a) (f b), derivWithin g (Icc (f a) (f b)) y = 1 / derivWithin f (Icc a b) (g y) :=
    fun y hy => (hderiv y hy).derivWithin (uniqueDiffOn_Icc hlt y hy)
  have hgdiff : DifferentiableOn ℝ g (Icc (f a) (f b)) := fun y hy => (hderiv y hy).differentiableWithinAt
  have hfdc : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) := hf.continuousOn_derivWithin hs le_rfl
  have hgdc : ContinuousOn (derivWithin g (Icc (f a) (f b))) (Icc (f a) (f b)) := by
    have : ContinuousOn (fun y => 1 / derivWithin f (Icc a b) (g y)) (Icc (f a) (f b)) :=
      continuousOn_const.div (hfdc.comp hgc hgmaps) (fun y hy => (hf' _ (hgmaps hy)).ne')
    exact this.congr hgd
  refine ⟨hlt, fun x hx => ⟨hmaps x hx, hgf x hx⟩, ?_, hgd⟩
  have := (contDiffOn_succ_iff_derivWithin (n := (0 : WithTop ℕ∞)) (f := g) (uniqueDiffOn_Icc hlt)).2
    ⟨hgdiff, by simp, contDiffOn_zero.2 hgdc⟩
  simpa using this

/-- Helper (Ch. II §4, Lemma 4.4). Congruence on the interval. -/
theorem gm24_congr {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} {u v : ℝ → ℝ} (huv : EqOn u v (Icc a b))
    (hu : MemCkAlphaOn m α u (Icc a b)) : MemCkAlphaOn m α v (Icc a b) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨h1.congr huv.symm, fun hα => ?_⟩
  obtain ⟨C, hC⟩ := h2 hα
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← iteratedDerivWithin_congr huv hx, ← iteratedDerivWithin_congr huv hy]
  exact hC x hx y hy

/-- Helper (Ch. II §4, Lemma 4.4). Reciprocals of positive `C^{m+α}` functions are `C^{m+α}`. -/
theorem gm24_inv {a b : ℝ} (hab : a < b) {m : ℕ} {α : ℝ} (hα₁ : α < 1) {v : ℝ → ℝ}
    (hv : MemCkAlphaOn m α v (Icc a b)) {c : ℝ} (hc : 0 < c) (hvc : ∀ x ∈ Icc a b, c ≤ v x) :
    MemCkAlphaOn m α (fun x => (v x)⁻¹) (Icc a b) := by
  have hvcont : ContinuousOn v (Icc a b) := hv.1.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hvcont
  have hcd : c < max M (c + 1) := lt_max_of_lt_right (by linarith)
  have hmaps : MapsTo v (Icc a b) (Icc c (max M (c + 1))) := fun x hx =>
    ⟨hvc x hx, (le_trans (le_abs_self _) (hM x hx)).trans (le_max_left _ _)⟩
  have hu : ContDiffOn ℝ (m + 1) (fun x : ℝ => x⁻¹) (Icc c (max M (c + 1))) :=
    (contDiffOn_inv ℝ).mono (fun x hx => ne_of_gt (lt_of_lt_of_le hc hx.1))
  exact gm24_comp_smooth hab hcd hα₁ hu hv hmaps

/-- Helper (Ch. II §4, Lemma 4.4). The derivative of the inverse is `1/(f' ∘ g)`; one step of the induction. -/
theorem gm24_deriv_step {a b : ℝ} (hab : a < b) {α : ℝ} (hα₁ : α < 1) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hf' : ∀ x ∈ Icc a b, 0 < derivWithin f (Icc a b) x)
    (hg : ∀ y ∈ Icc (f a) (f b), g y ∈ Icc a b ∧ f (g y) = y) {m : ℕ}
    (hD : MemCkAlphaOn m α (derivWithin f (Icc a b)) (Icc a b))
    (hgm : MemCkAlphaOn m α g (Icc (f a) (f b))) :
    MemCkAlphaOn m α (derivWithin g (Icc (f a) (f b))) (Icc (f a) (f b)) := by
  obtain ⟨hlt, hgf, hg1, hgd⟩ := gm24_inverse hab hf hf' hg
  have hmaps : MapsTo g (Icc (f a) (f b)) (Icc a b) := fun y hy => (hg y hy).1
  have hcont : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    (nonempty_Icc.2 hab.le) hcont
  have hc : 0 < derivWithin f (Icc a b) x0 := hf' x0 hx0
  have hv : MemCkAlphaOn m α (fun y => derivWithin f (Icc a b) (g y)) (Icc (f a) (f b)) :=
    gm24_comp hlt hab hα₁ hD hgm hg1 hmaps
  have hinv := gm24_inv hlt hα₁ hv hc (fun y hy => hmin (hmaps hy))
  refine gm24_congr hlt (fun y hy => ?_) hinv
  rw [hgd y hy, one_div]

/-- Helper (Ch. II §4, Lemma 4.4). The inverse of a `C^{k+α}` function with positive derivative is `C^{k+α}`
(`k ≥ 1`). -/
theorem gm24_dir {a b : ℝ} (hab : a < b) {α : ℝ} (hα₁ : α < 1) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hf' : ∀ x ∈ Icc a b, 0 < derivWithin f (Icc a b) x)
    (hg : ∀ y ∈ Icc (f a) (f b), g y ∈ Icc a b ∧ f (g y) = y) {k : ℕ} (hk : 1 ≤ k)
    (hfk : MemCkAlphaOn k α f (Icc a b)) : MemCkAlphaOn k α g (Icc (f a) (f b)) := by
  obtain ⟨hlt, hgf, hg1, hgd⟩ := gm24_inverse hab hf hf' hg
  induction k, hk using Nat.le_induction with
  | base =>
    have hD : MemCkAlphaOn 0 α (derivWithin f (Icc a b)) (Icc a b) := ((gm24_succ_iff hab).1 hfk).2
    have hgm : MemCkAlphaOn 0 α g (Icc (f a) (f b)) := gm24_of_contDiff hlt hα₁ hg1
    exact (gm24_succ_iff hlt).2 ⟨hg1.differentiableOn (by simp), gm24_deriv_step hab hα₁ hf hf' hg hD hgm⟩
  | succ k hk ih =>
    have hfk' : MemCkAlphaOn k α f (Icc a b) := gm24_of_contDiff hab hα₁ hfk.1
    have hD : MemCkAlphaOn k α (derivWithin f (Icc a b)) (Icc a b) := ((gm24_succ_iff hab).1 hfk).2
    have hgm := ih hfk'
    exact (gm24_succ_iff hlt).2 ⟨hg1.differentiableOn (by simp), gm24_deriv_step hab hα₁ hf hf' hg hD hgm⟩

/-- **Lemma 4.4** (Ch. II §4; cited at P1:2862, 2888). Let `k` be a positive integer, and let `0 ≤ α < 1`. Let
`f ∈ C¹([0, 1])` satisfy `f' > 0` and let `g ≡ f⁻¹`. Then `g ∈ C^{k+α}` if and only if `f ∈ C^{k+α}`.
Modelling: `f' > 0` on `[0, 1]` (one-sided derivatives at the ends); `g` is the inverse of `f` on `[f(0), f(1)]`,
characterized by `g(y) ∈ [0, 1]` and `f(g(y)) = y`; the classes are taken on `[f(0), f(1)]` and on `[0, 1]`. -/
theorem lemma2_4_4 {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 1)) (hf' : ∀ x ∈ Icc (0 : ℝ) 1, 0 < derivWithin f (Icc 0 1) x)
    (hg : ∀ y ∈ Icc (f 0) (f 1), g y ∈ Icc (0 : ℝ) 1 ∧ f (g y) = y) :
    MemCkAlphaOn k α g (Icc (f 0) (f 1)) ↔ MemCkAlphaOn k α f (Icc 0 1) := by
  have _ := hα₀
  have hab : (0 : ℝ) < 1 := one_pos
  obtain ⟨hlt, hgf, hg1, hgd⟩ := gm24_inverse hab hf hf' hg
  have hgf0 : g (f 0) = 0 := (hgf 0 ⟨le_rfl, zero_le_one⟩).2
  have hgf1 : g (f 1) = 1 := (hgf 1 ⟨zero_le_one, le_rfl⟩).2
  constructor
  · intro hgk
    have hg' : ∀ y ∈ Icc (f 0) (f 1), 0 < derivWithin g (Icc (f 0) (f 1)) y := fun y hy => by
      rw [hgd y hy]
      exact one_div_pos.2 (hf' _ (hg y hy).1)
    have hinv : ∀ x ∈ Icc (g (f 0)) (g (f 1)), f x ∈ Icc (f 0) (f 1) ∧ g (f x) = x := by
      rw [hgf0, hgf1]
      exact hgf
    have := gm24_dir hlt hα₁ hg1 hg' hinv hk hgk
    rwa [hgf0, hgf1] at this
  · intro hfk
    exact gm24_dir hab hα₁ hf hf' hg hk hfk

/-- **Definition** (`f ∈ C^{l+β}(Γ)`, Ch. II §4, P1:2884). Let `l` be a non-negative integer and let `0 ≤ β < 1`. If
`Γ` is of class `C^{k+α}` and if `f ∈ C(Γ)`, we say `f ∈ C^{l+β}(Γ)` if `f(γ(s)) ∈ C^{l+β}`, when viewed as a function
of arc length on `Γ`.
Modelling: `f` is continuous on `Γ` and `s ↦ f(γ(s))` is in `C^{l+β}` on `ℝ` for an arc length parametrization `γ` of
`Γ` (`ℓ(Γ)`-periodic). -/
def MemCkAlphaOnCurve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (l : ℕ) (β : ℝ) (Γ : Set ℂ)
    (f : ℂ → V) : Prop :=
  ContinuousOn f Γ ∧ ∃ (ℓ : ℝ) (γ : ℝ → ℂ), IsArcLengthParam Γ ℓ γ ∧ MemCkAlphaOn l β (fun s => f (γ s)) univ

/-- **Definition** (`F ∈ C^{n+σ}(Ω̄)`, Ch. II §4, Corollary 4.5, P1:2886; the class `C^{k+α}(𝔻̄)` of §3 with `Ω` in
place of `𝔻`). For `F` analytic on `Ω`: `F` and its first `n` derivatives extend continuously to `Ω̄`, and the
extension of `F^{(n)}` satisfies `|F^{(n)}(z₁) − F^{(n)}(z₂)| ≤ C |z₁ − z₂|^σ` on `Ω̄`. -/
def MemCkAlphaClosure (n : ℕ) (σ : ℝ) (Ω : Set ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F Ω ∧
    (∀ j ≤ n, ∃ G : ℂ → ℂ, ContinuousOn G (closure Ω) ∧ EqOn G (iteratedDeriv j F) Ω) ∧
    ∃ G : ℂ → ℂ, ContinuousOn G (closure Ω) ∧ EqOn G (iteratedDeriv n F) Ω ∧
      ∃ C : ℝ, ∀ z₁ ∈ closure Ω, ∀ z₂ ∈ closure Ω, ‖G z₁ - G z₂‖ ≤ C * ‖z₁ - z₂‖ ^ σ

/-- **Corollary 4.5** (Ch. II §4; cited at P1:2900 and in App. B, P3:2575, 2589, 2685). Suppose `Γ` is of class
`C^{k+α}`, where `k + α > 1`, and suppose `f ∈ C^{l+β}(Γ)`. Set `n + σ = min(k + α, l + β)`, where `0 < σ < 1` and
`n` is a non-negative integer. Let `φ` be a conformal map of `𝔻` onto `Ω`, let `G` be the Herglotz integral of
`f ∘ φ`, and let `F = G ∘ φ⁻¹`. Then `F ∈ C^{n+σ}(Ω̄)`.
Modelling: `0 ≤ α, β < 1` (the ranges in the definitions of the classes); `f` is real (the Herglotz integral of §3 is
for real functions) and `f ∘ φ` on `∂𝔻` is `f ∘ Φ`; `F` is any function with `F(φ(z)) = G(z)` for `z ∈ 𝔻`, which
determines it on `Ω`. -/
theorem cor2_4_5 {Ω : Set ℂ} {φ Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω φ Φ) {k l n : ℕ} {α β σ : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hkα : 1 < k + α)
    (hnσ : (n : ℝ) + σ = min (k + α) (l + β)) (hΓ : IsCurveOfClass k α (frontier Ω)) {f : ℂ → ℝ}
    (hf : MemCkAlphaOnCurve l β (frontier Ω) f) {F : ℂ → ℂ}
    (hF : ∀ z ∈ unitDisc, F (φ z) = herglotzIntegral (fun ζ => f (Φ ζ)) z) :
    MemCkAlphaClosure n σ Ω F := by
  sorry

/-- **Corollary 4.6** (Ch. II §4; cited at P1:2908, 2942, and in App. B, P3:2589, 2679, App. C, P3:3073, App. H,
P3:4622). Let `∂Ω` be a finite union of pairwise disjoint `C^{k+α}` Jordan curves, where `k + α > 1`, and let
`f ∈ C(∂Ω)` be a `C^{l+β}` function of arc length on each component of `∂Ω`. Set `n + σ = min(k + α, l + β)`, where
`0 < σ < 1` and `n` is a non-negative integer. Then `u(z) = u_f(z)` and its first `n` partial derivatives extend
continuously to `Ω̄` and `|D^n u(z₁) − D^n u(z₂)| ≤ K |z₁ − z₂|^σ` for all `z₁, z₂ ∈ Ω̄`, where `D^n` denotes any
`n`-th partial derivative.
Modelling: `Ω` is a bounded plane domain (standing assumption of §4) with `∂Ω = Γ₁ ∪ … ∪ Γ_p`; `u_f` is the solution
`dirichletSolution` of Theorem 1.1 on `Ω ⊆ ℂ*`; the partial derivatives of order `j` are the `j`-th real derivative
`iteratedFDeriv ℝ j u`, and the Hölder bound is for the norm of the difference of the extended `n`-th derivatives
(equivalent to the bound for each `n`-th partial derivative, `K` being existential). -/
theorem cor2_4_6 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω) {p : ℕ}
    (hp : 0 < p) {Γ : Fin p → Set ℂ} {k l n : ℕ} {α β σ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 ≤ β)
    (hβ₁ : β < 1) (hΓ : ∀ j, IsCurveOfClass k α (Γ j)) (hdisj : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (hΩΓ : frontier Ω = ⋃ j, Γ j) (hkα : 1 < k + α) (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hnσ : (n : ℝ) + σ = min (k + α) (l + β)) {f : ExtPlane → ℝ} (hf : ContinuousOn f (frontier (toExt Ω)))
    (hfΓ : ∀ j, MemCkAlphaOnCurve l β (Γ j) fun x : ℂ => f x) :
    (∀ j ≤ n, ∃ H : ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) ℝ, ContinuousOn H (closure Ω) ∧
        EqOn H (iteratedFDeriv ℝ j fun x : ℂ => dirichletSolution (toExt Ω) f x) Ω) ∧
      ∃ H : ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin n => ℂ) ℝ, ContinuousOn H (closure Ω) ∧
        EqOn H (iteratedFDeriv ℝ n fun x : ℂ => dirichletSolution (toExt Ω) f x) Ω ∧
        ∃ K : ℝ, ∀ z₁ ∈ closure Ω, ∀ z₂ ∈ closure Ω, ‖H z₁ - H z₂‖ ≤ K * ‖z₁ - z₂‖ ^ σ := by
  sorry

/-- **Corollary 4.7** (Ch. II §4; answers Question 2, P1:2908). If `∂Ω` consists of finitely many pairwise disjoint
Jordan curves of class `C^{1+α}`, where `α > 0`, then (4.8) `dω(z, ζ) = −(∂g(z, ζ)/∂n_ζ) ds(ζ)/2π`. In other words,
harmonic measure for `z ∈ Ω` is absolutely continuous to arc length on `∂Ω`, and the density
`dω/ds = −(1/2π) ∂g(ζ, z)/∂n_ζ` is of class `C^α(∂Ω)` and satisfies (4.9) `c₁ < dω/ds < c₂` for positive constants
`c₁` and `c₂`.
Modelling: `Ω` is a domain of `ℂ*` with `∂Ω = Γ₁ ∪ … ∪ Γ_p`, `Γ_j ⊆ ℂ` of class `C^{1+α}` (`α < 1`, the range in the
definition of the class); nothing here needs `Ω` bounded. As Question 2 asks, the normal derivative of `g(z, ·)`
exists at every boundary point; (4.8) is written as for (2.14) in Corollary 2.6, with `g(z, ζ)` as printed, and the
density is the Poisson kernel `P_z(ζ) = −(1/2π) ∂g(ζ, z)/∂n_ζ` as printed; "of class `C^α(∂Ω)`" is `C^α` as a
function of arc length on each `Γ_j`; `c₁, c₂` depend on `Ω` and `z`. -/
theorem cor2_4_7 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) {p : ℕ} (hp : 0 < p) {Γ : Fin p → Set ℂ} {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hΓ : ∀ j, IsCurveOfClass 1 α (Γ j))
    (hdisj : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hΩΓ : frontier Ω = ⋃ j, toExt (Γ j)) {z : ExtPlane}
    (hz : z ∈ Ω) :
    (∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω → ∃ L : ℝ, HasOuterNormalDeriv Ω (fun w => greenFunction Ω z w) ζ L) ∧
      harmonicMeasureFC Ω z = ((arcLengthOn Ω).withDensity fun ζ =>
          ENNReal.ofReal (-(1 / (2 * π)) * outerNormalDeriv Ω (fun w => greenFunction Ω z w) ζ)).map
          ((↑) : ℂ → ExtPlane) ∧
      (∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω →
        -(1 / (2 * π)) * outerNormalDeriv Ω (fun w => greenFunction Ω z w) ζ = poissonKernelFC Ω z ζ) ∧
      (∀ j, MemCkAlphaOnCurve 0 α (Γ j) (poissonKernelFC Ω z)) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω →
        c₁ < poissonKernelFC Ω z ζ ∧ poissonKernelFC Ω z ζ < c₂ := by
  sorry

end GarnettMarshall2005
