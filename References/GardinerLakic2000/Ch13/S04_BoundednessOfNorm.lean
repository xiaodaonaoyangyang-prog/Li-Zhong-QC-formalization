import References.GardinerLakic2000.Ch13.S03_SmoothingContours

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.4 Boundedness of the norm

Source `teichmuller.txt`, lines 9621–9686.

* Definition (width, l. 9627) — `qdWidth`
* Definition (`Λ(β, S)`, the extremal length of the curves freely homotopic to `β`, l. 9644) — `IsConformalMetricRS`,
  `extremalLengthLoopRS`
* Lemma 1 (l. 9634) — `lemma13_1`
* Lemma 2 (l. 9659) — `lemma13_2`
* Theorem 3 (finite analytic type, l. 9667) — `thm13_3`
* Definition (`J`-symmetric quadratic differential: `φ dz²` real on the border, l. 9683) — `IsJSymmetricQD`
* Theorem 4 (finite topological type, l. 9685) — `thm13_4`

Not items (DESIGN §3): the generalization paragraph (l. 9683, it is Theorem 4) and the string of inequalities before
Lemma 2 (l. 9648–9655, proof).

**Modelling (calibration D0.5, D0.1).** `width_φ(β) = inf ∫_β̃ |Re(√φ dz)|` equals the height for `−φ`, since
`|Re(√φ dz)| = |Im(√(−φ) dz)|`. A conformal metric `ρ|dz|` on a surface is given by `q = ρ²`, a nonnegative real
`(1, 1)`-family (`LiZhongQC.IsDiffFamily 1 1`); its `ρ`-length of a curve is `LiZhongQC.phiLengthPath q` and its area
is `∬ ρ² = LiZhongQC.surfaceIntegral q 1`. `Λ(β, S)` is the supremum, over the metrics of total mass `1`, of the
square of the infimum of the `ρ`-lengths of the curves freely homotopic to `β` (the book's description, l. 9648).
Its plane counterpart is `LiZhongQC.extremalLength`. In Lemma 2, "the points `(g, S_g)` of `T(S)`" are the
quasiconformal `g : S → S_g` with Beltrami coefficient `μ`, and `K₀(g)` is Part A's `minimalDilatation` of `[μ]`.
Theorem 3 ("the numbers `M_f` are bounded") is `M < ∞` for the supremum (13.1). The hypotheses of Theorem 3 are
printed twice [OCR]; the extra condition "each component contains at least two points" is kept. Theorem 4 (finite
topological type) is stated on the double (calibration D0.1): `S` is the surface of finite analytic type `S^d`, `J`
its anticonformal involution, and `φ`, `E` and the family are `J`-symmetric ("`f` maps the border of `S` to the border
of `S_f`", "`φ dz²` real on the border") [reading].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop FreelyHomotopic quadDiffNorm IsQCRS surfaceIntegral IsDiffFamily phiLengthPath IsFuchsian
  IsUniformization IsAnticonformalInvolution localMapExpr)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- **Definition** (width, §13.4, l. 9627). `width_φ(β) = inf ∫_β̃ |Re(φ^{1/2} dz)|` over the curves `β̃` freely
homotopic to `β`; it is the height `h_{−φ}[β]`. -/
def qdWidth (φ : S → ℂ → ℂ) (β : Loop S) : ℝ≥0∞ := qdHeight (fun x z => -φ x z) β

/-- Helper (§13.4, l. 9648). `q = ρ²` for a conformal metric `ρ|dz|`: a measurable, nonnegative real `(1, 1)`-family
of chart densities. -/
def IsConformalMetricRS (q : S → ℂ → ℂ) : Prop :=
  IsDiffFamily 1 1 q ∧ (∀ x, Measurable (q x)) ∧ ∀ x z, (q x z).im = 0 ∧ 0 ≤ (q x z).re

/-- **Definition** (`Λ(β, S)`, §13.4, l. 9644, 9648). The extremal length of the family of closed curves freely
homotopic to `β`: the supremum, over conformal metrics `ρ|dz|` with `∬_S ρ² = 1`, of `(inf_{β̃ ≃ β} ∫_β̃ ρ|dz|)²`.
The plane counterpart is `LiZhongQC.extremalLength`. -/
def extremalLengthLoopRS (β : Loop S) : ℝ≥0∞ :=
  ⨆ (q : S → ℂ → ℂ) (_ : IsConformalMetricRS q ∧ surfaceIntegral q (fun _ _ => 1) = 1),
    (⨅ (β' : Loop S) (_ : FreelyHomotopic β' β), phiLengthPath q β'.2) ^ 2

/-- **Definition** (§13.4, l. 9683). `φ` is symmetric under the anticonformal involution `J`:
`φ(z) dz² = conj (J^*(φ dz²))`, i.e. in charts `φ_x(z) = conj (φ_{Jx}(T z)) · (∂_z (conj ∘ T))²` with `T` the local
expression of `J`. For the double of a bordered surface this is "`φ dz²` real on the border". -/
def IsJSymmetricQD (J : S ≃ₜ S) (φ : S → ℂ → ℂ) : Prop :=
  ∀ x : S, ∀ z ∈ (chartAt ℂ x).target, (chartAt ℂ x).symm z ∈ J ⁻¹' (chartAt ℂ (J x)).source →
    φ x z = conj (φ (J x) (localMapExpr J x z)) * deriv (fun w => conj (localMapExpr J x w)) z ^ 2

variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Lemma 1** (§13.4, l. 9634). On a surface of finite analytic type there are finitely many simple closed curves
`βₖ` and `c > 0` such that every holomorphic quadratic differential `φ` with `∬_S |φ| = 1` has
`width_φ(βₖ) ≥ c` for at least one `k`. -/
theorem lemma13_1 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) :
    ∃ (N : ℕ) (β : Fin N → Loop S) (c : ℝ), (∀ k, IsSimpleLoop (β k)) ∧ 0 < c ∧
      ∀ φ ∈ integrableHolQDSet S, quadDiffNorm φ = 1 → ∃ k, ENNReal.ofReal c ≤ qdWidth φ (β k) := by
  sorry

/-- **Lemma 2** (§13.4, l. 9659). There are `c > 0` and finitely many simple closed curves `βₖ` on `S` such that
for all points `(g, S_g)` of `T(S)`, `K₀(g) ≤ c⁻² sup_k Λ(g(βₖ), S_g)`. -/
theorem lemma13_2 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {p : UpperHalfPlane → S}
    (hp : ∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p) :
    ∃ (N : ℕ) (β : Fin N → Loop S) (c : ℝ), (∀ k, IsSimpleLoop (β k)) ∧ 0 < c ∧
      ∀ (μ : beltramiBall S) (Y : RSBundle.{u}) (G : S ≃ₜ Y.carrier), IsQCRS G → HasBeltramiCoeff G μ.1 →
        minimalDilatation p (Quot.mk (teichRel p) μ) ≤
          ENNReal.ofReal (1 / c ^ 2) * ⨆ k, extremalLengthLoopRS (loopMap G (β k)) := by
  sorry

/-- **Theorem 3** (§13.4, l. 9667). Let `S` be of finite analytic type, `E ⊆ S` an obstacle set whose components each
contain at least two points, and `φ` of finite norm. Then the numbers `M_f`, `(f, S_f) ∈ 𝓕`, are bounded:
`M < ∞` in (13.1). -/
theorem thm13_3 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S)
    {E : Set S} (hE : IsObstacleSet E) (hE2 : ∀ x ∈ E, (connectedComponentIn E x).Nontrivial) :
    obstacleSup φ E < ⊤ := by
  sorry

/-- **Theorem 4** (§13.4, l. 9685). Let `S` be of finite topological type, `E ⊆ S` an obstacle set, `φ` of finite
norm with `φ dz²` real on the border, and consider the `(f, S_f) ∈ 𝓕` with `f` mapping the border of `S` to the
border of `S_f`. Then the numbers `M_f` are bounded. Stated on the double `S^d` with its anticonformal involution `J`
(see the module docstring): the members are `J`-symmetric for anticonformal involutions `J_f` of the `S_f`. -/
theorem thm13_4 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {J : S ≃ₜ S} (hJ : IsAnticonformalInvolution J)
    {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S) (hφJ : IsJSymmetricQD J φ) {E : Set S} (hE : IsObstacleSet E)
    (hEJ : J '' E = E) (hE2 : ∀ x ∈ E, (connectedComponentIn E x).Nontrivial) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ (Y : RSBundle.{u}) (JY : Y.carrier ≃ₜ Y.carrier) (f : S → Y.carrier)
      (G : S ≃ₜ Y.carrier), IsObstacleFamilyMember E f G → IsAnticonformalInvolution JY →
        (∀ x, G (J x) = JY (G x)) → (∀ x ∉ E, f (J x) = JY (f x)) → obstacleValue φ G ≤ M := by
  sorry

end GardinerLakic2000
