import References.GardinerLakic2000.Ch04.S02_GeodesicTrajectories

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.3 The minimal norm property

Source `teichmuller.txt`, lines 3819–3955. The standing assumption of §4.1 (finite analytic type) is kept.

* Definition (`ℓ_ψ(α) = ∫_α |√ψ dz|` for a locally integrable quadratic differential `ψ`, l. 3820–3829) — exists:
  `LiZhongQC.phiLengthPath` (the same formula; it needs no holomorphy)
* Definition (unit-speed vertical trajectory, the vertical shift `ζ ↦ ζ + iτ` of l. 3844, 3852) —
  `IsUnitVerticalTraj`, `verticalShift`
* Theorem 1 (the minimal norm property (4.6), l. 3831) — `thm4_1`
* Lemma 3 ((4.7), l. 3844) — `lemma4_3`
* Theorem 2 ((4.13) and the equality case, l. 3930) — `thm4_2`

Not items (DESIGN §3): the critical set `a_φ` (l. 3841), a null set used in the proofs (in the statements the
exceptional horizontal segments are those through a null set `N`, and the vertical shift carries a junk value
there), the remark after Theorem 1 (l. 3928).

**Misprints and corrections.**
- Theorem 1 [misprint]: printed "for almost every noncritical vertical segment `α`, `ℓ_φ(α) ≤ ℓ_ψ(β) + M`" (also
  GL8:3722). The proof (l. 3896–3902) and its application in Theorem 3 (l. 3987) use horizontal segments `α` and
  `ℓ_ψ(α)`. Lemma 3 [misprint]: `R − b_φ` is `R − a_φ` (GL8:3734).
- Theorem 2, the equality case [CORRECTION]: printed "`ψ ≡ cφ` with `|c| = 1`". This is false for non-holomorphic
  `ψ`. For `ψ = e^{iθ(z)} φ` with any measurable real `θ`, `ℓ_ψ = ℓ_φ` on every arc, so the hypothesis holds with
  `M = 0` and `‖ψ‖ = ‖φ‖`, but `ψ` is not a constant multiple of `φ`. The proof gives `|√ψ| = c|√φ|` with `|c| = 1`
  (l. 3950–3954), i.e. `|ψ| = |φ|` almost everywhere; this is the stated conclusion.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Definition** (§4.3, l. 3844, 3852). `c : ℝ → R` is a unit-speed vertical trajectory of `φ`: in every chart at
the points of `c`, `z = chart(c(t))` satisfies `φ(z) (dz/dt)² = −1`, i.e. `dζ = i dt` in a natural parameter. -/
def IsUnitVerticalTraj (φ : R → ℂ → ℂ) (c : ℝ → R) : Prop :=
  Continuous c ∧ ∀ t : ℝ, ∀ x : R, c t ∈ (chartAt ℂ x).source →
    ∃ v : ℂ, HasDerivAt (fun s => chartAt ℂ x (c s)) v t ∧ φ x (chartAt ℂ x (c t)) * v ^ 2 = -1

open Classical in
/-- The vertical shift `p ↦ p + iτ` of §4.3 (l. 3844, 3852: `ζ ↦ ζ + iτ` in a natural parameter): the point at
`φ`-distance `τ` from `p` along a unit-speed vertical trajectory through `p`. Off the critical set (a null set) such
a trajectory exists for all times and is unique up to orientation; `h(ζ) = g(ζ + iτ) + g(ζ − iτ)` in Lemma 3 does not
depend on the orientation. Junk value `p` where no such trajectory exists (never read by Lemma 3's integrals). -/
def verticalShift (φ : R → ℂ → ℂ) (τ : ℝ) (p : R) : R :=
  if h : ∃ c : ℝ → R, IsUnitVerticalTraj φ c ∧ c 0 = p then h.choose τ else p

/-- **Theorem 1** (the minimal norm property, (4.6), §4.3, l. 3831). Let `R` be of finite analytic type, `φ` a
holomorphic quadratic differential with `‖φ‖ < ∞`, and `ψ` a locally integrable quadratic differential. Assume there
is a constant `M` with `ℓ_φ(α) ≤ ℓ_ψ(α) + M` for almost every noncritical horizontal segment `α` of `φ`. Then
`‖φ‖ ≤ ∬_R |√φ| |√ψ| dx dy`. Modelling: "almost every" means all horizontal segments whose midpoint lies off a set
`N` that is null in every chart; the integrand is `|φ| · (|ψ|/|φ|)^{1/2}` against `LiZhongQC.surfaceIntegral` (where
`φ = 0` both sides vanish). [misprint: vertical/`β`, see the module docstring] -/
theorem thm4_1 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    (hφn : LiZhongQC.quadDiffNorm φ < ⊤) {ψ : R → ℂ → ℂ} (hψ : LiZhongQC.IsDiffFamilyAE 2 0 ψ)
    (hψi : ∀ x : R, LocallyIntegrableOn (ψ x) (chartAt ℂ x).target) {M : ℝ} {N : Set R}
    (hN : ∀ x : R, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0)
    (hM : ∀ (a b : R) (α : Path a b), LiZhongQC.IsHorizontalArcRS φ α → α.extend (1 / 2) ∉ N →
      LiZhongQC.phiLengthPath φ α ≤ LiZhongQC.phiLengthPath ψ α + ENNReal.ofReal M) :
    LiZhongQC.quadDiffNorm φ ≤
      LiZhongQC.surfaceIntegral φ fun x z => ENNReal.ofReal (Real.sqrt (‖ψ x z‖ / ‖φ x z‖)) := by
  sorry

/-- **Lemma 3** ((4.7), §4.3, l. 3844). Let `g ≥ 0` be integrable with respect to `|φ| dx dy`, `‖φ‖ < ∞`, and `τ`
real. Then `h(p) = g(p + iτ) + g(p − iτ)` (vertical shifts in a natural parameter) satisfies
`∬_R h dξ dη = 2 ∬_R g dξ dη`. Modelling: `dξ dη = |φ| dx dy`, i.e. `LiZhongQC.surfaceIntegral φ`; `g` a function on
`R`, measurable in charts. [misprint `b_φ`] -/
theorem lemma4_3 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    (hφn : LiZhongQC.quadDiffNorm φ < ⊤) {G : R → ℝ≥0∞}
    (hG : ∀ x : R, Measurable fun z => G ((chartAt ℂ x).symm z))
    (hGi : LiZhongQC.surfaceIntegral φ (fun x z => G ((chartAt ℂ x).symm z)) < ⊤) (τ : ℝ) :
    LiZhongQC.surfaceIntegral φ (fun x z => G (verticalShift φ τ ((chartAt ℂ x).symm z)) +
        G (verticalShift φ (-τ) ((chartAt ℂ x).symm z))) =
      2 * LiZhongQC.surfaceIntegral φ (fun x z => G ((chartAt ℂ x).symm z)) := by
  sorry

/-- **Theorem 2** ((4.13), §4.3, l. 3930). Under the hypotheses of Theorem 1, `‖φ‖ ≤ ‖ψ‖`; if equality holds, then
`|ψ| = |φ|` almost everywhere. [CORRECTION: the book's "`ψ ≡ cφ`, `|c| = 1`" is false, see the module docstring.] -/
theorem thm4_2 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    (hφn : LiZhongQC.quadDiffNorm φ < ⊤) {ψ : R → ℂ → ℂ} (hψ : LiZhongQC.IsDiffFamilyAE 2 0 ψ)
    (hψi : ∀ x : R, LocallyIntegrableOn (ψ x) (chartAt ℂ x).target) {M : ℝ} {N : Set R}
    (hN : ∀ x : R, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0)
    (hM : ∀ (a b : R) (α : Path a b), LiZhongQC.IsHorizontalArcRS φ α → α.extend (1 / 2) ∉ N →
      LiZhongQC.phiLengthPath φ α ≤ LiZhongQC.phiLengthPath ψ α + ENNReal.ofReal M) :
    LiZhongQC.quadDiffNorm φ ≤ LiZhongQC.quadDiffNorm ψ ∧
      (LiZhongQC.quadDiffNorm φ = LiZhongQC.quadDiffNorm ψ →
        ∀ x : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target), ‖ψ x z‖ = ‖φ x z‖) := by
  sorry

end GardinerLakic2000
