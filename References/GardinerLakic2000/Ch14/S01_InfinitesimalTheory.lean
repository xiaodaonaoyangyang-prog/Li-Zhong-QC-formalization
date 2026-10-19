import References.GardinerLakic2000.Ch13.S09_TrajectoriesAroundObstacle

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.1 The infinitesimal theory (with the chapter introduction)

Chapter 14 *Asymptotic Teichmüller space*; source `teichmuller.txt`, lines 9897–10041.

* Definition (asymptotically conformal map, l. 9903) — `IsAsymConformalRS`
* Definition (`AT(R)`: Teichmüller equivalence with "conformal" replaced by "asymptotically conformal", l. 9903) —
  `IsAsymEquiv`, `asymRel`, `AsymTeichSpace`
* Definition (asymptotically conformal mapping class; `T₀ = π⁻¹[id]`, l. 9903, 9906) — `IsInT0`
* Definition (`β(V)`, l. 9930) — exists: `GardinerLakic2000.betaSeminorm`
* Definition (`q(V)`, l. 9938) — `qNorm`
* Formulas (14.1), (14.2) (`b(V)`, `b*(μ)`, l. 9945, 9953) — exists: `GardinerLakic2000.infBoundaryDilatation`
  `GardinerLakic2000.boundaryDilatationStar`
* Theorem 1 (`β = q = b`, l. 9958) — `thm14_1`
* Definition 1 (harmonic Beltrami coefficient vanishing at infinity, l. 9979) — `IsVanishingAtInfinity`
* Lemma 1 (l. 9981) — `lemma14_1`
* Corollary 1 (l. 10029) — `opNormZ`, `cor14_1_1`

Not items (DESIGN §3): the introduction's list of goals (l. 9911–9916, restated in Theorems 6, 10, 11 and
Corollaries 2–3), the remarks on finite dimension (l. 9904), and the quotient map `π : T → AT` (l. 9906: it is
`[μ] ↦ [μ]`, written out where used).

**Modelling (calibration D0.8).** `f` is asymptotically conformal iff `H*(f) ≤ 1` for B's `boundaryDilatationStarK`
of its Beltrami coefficient (`∀ ε ∃` compact `E` with `K_z(f) < 1 + ε` a.e. off `E`), and a mapping class is
asymptotically conformal iff B's `boundaryDilatationH` of it is `≤ 1` (the book's "for every `ε` a representative"),
which is `T₀`. `IsAsymEquiv` is Part A's `IsTeichEquiv` with the conformal `c` replaced by a quasiconformal,
asymptotically conformal `c`; `AT(R)` is the `Quot` of `M(R)` (no equivalence proof). `q(V)` is the distance in `Z`
from `V` to `Z₀` (in `ℝ≥0∞`). Harmonic Beltrami coefficients `ρ⁻² ψ̄` are read on the Fuchsian model through Part A's
`liftBeltrami` and B's `IsHarmonicBeltrami`. The bounded operators of Corollary 1 are maps on functionals that are
linear on `Z`, map `Z` into `Z` and `Z₀` into `Z₀`, with finite operator norm `opNormZ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS ExtPlane extRealLine IsFuchsian IsUniformization upperHalf)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (asymptotically conformal, §14 intro, l. 9903). For every `ε > 0` there is a compact `E` with
`K_z(f) < 1 + ε` for `z ∉ E`: `H*(f) ≤ 1`. -/
def IsAsymConformalRS {R' : Type*} [TopologicalSpace R'] [ChartedSpace ℂ R'] (f : R → R') : Prop :=
  boundaryDilatationStarK (beltramiCoeffRS f) ≤ 1

/-- **Definition** (§14 intro, l. 9901–9903). `f₀ : R → R₀` and `f₁ : R → R₁` are asymptotically equivalent: the
condition of `IsTeichEquiv` with an asymptotically conformal (quasiconformal) `c : R₀ → R₁` in place of a conformal
one. -/
def IsAsymEquiv (p : UpperHalfPlane → R) {Y₀ Y₁ : RSBundle.{u}} (f₀ : R ≃ₜ Y₀.carrier) (f₁ : R ≃ₜ Y₁.carrier) :
    Prop :=
  ∃ c : Y₀.carrier ≃ₜ Y₁.carrier, IsQCRS c ∧ IsAsymConformalRS (c : Y₀.carrier → Y₁.carrier) ∧
    ∃ (H : R → unitInterval → R) (Ht : UpperHalfPlane → unitInterval → UpperHalfPlane)
      (G : ExtPlane → unitInterval → ExtPlane),
      Continuous (fun x : R × unitInterval => H x.1 x.2) ∧ (∀ x, H x 0 = x) ∧ (∀ x, H x 1 = f₁.symm (c (f₀ x))) ∧
      (∀ t, ∃ e : R ≃ₜ R, (⇑e = fun x => H x t) ∧ IsQCRS e) ∧
      (∀ τ t, p (Ht τ t) = H (p τ) t) ∧ Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2) ∧
      (∀ (τ : UpperHalfPlane) t, G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane)) ∧
      ∀ x ∈ extRealLine, ∀ t, G x t = x

/-- **Definition** (§14 intro, l. 9903), the relation on `M(R)`. -/
def asymRel (p : UpperHalfPlane → R) (μ ν : beltramiBall R) : Prop :=
  ∃ (Y₀ Y₁ : RSBundle.{u}) (f₀ : R ≃ₜ Y₀.carrier) (f₁ : R ≃ₜ Y₁.carrier), IsQCRS f₀ ∧ IsQCRS f₁ ∧
    HasBeltramiCoeff f₀ μ.1 ∧ HasBeltramiCoeff f₁ ν.1 ∧ IsAsymEquiv p f₀ f₁

/-- **Definition** (§14 intro, l. 9903). The asymptotic Teichmüller space `AT(R)`. -/
def AsymTeichSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] (p : UpperHalfPlane → R) : Type u :=
  Quot (asymRel p)

/-- **Definition** (§14 intro, l. 9903, 9906). The mapping class `P ∈ T(R)` is asymptotically conformal (`P ∈ T₀`):
for every `ε > 0` some representative has dilatation `< 1 + ε` off a compact set, i.e. `H(P) ≤ 1`. -/
def IsInT0 (p : UpperHalfPlane → R) (P : TeichSpace R p) : Prop := boundaryDilatationH p P ≤ 1

/-- **Definition** (§14.1, l. 9938). `q(V) = inf {‖V − u‖ : u ∈ Z₀}`. -/
def qNorm (V : (R → ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (u : (R → ℂ → ℂ) → ℂ) (_ : u ∈ zZeroSpace R), ENNReal.ofReal (zNorm (V - u))

/-- **Definition 1** (§14.1, l. 9979). The harmonic Beltrami coefficient `μ` (`ρ⁻² ψ̄` on the Fuchsian model) vanishes
at infinity: `b*(μ) = 0`. -/
def IsVanishingAtInfinity (p : UpperHalfPlane → R) (μ : R → ℂ → ℂ) : Prop :=
  IsHarmonicBeltrami upperHalf (liftBeltrami p μ) ∧ boundaryDilatationStar μ = 0

/-- Helper (§14.1, l. 10029). The operator norm `‖L‖ = sup {‖L V‖ : V ∈ Z, ‖V‖ = 1}` of a map `L : Z → Z`. -/
def opNormZ (L : ((R → ℂ → ℂ) → ℂ) → (R → ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨆ (V : (R → ℂ → ℂ) → ℂ) (_ : V ∈ zSpace R ∧ zNorm V = 1), ENNReal.ofReal (zNorm (L V))

variable [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 1** (§14.1, l. 9958; [EGL98b]). For every `V ∈ Z`, `β(V) = q(V) = b(V)`. -/
theorem thm14_1 {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) :
    betaSeminorm V = qNorm V ∧ qNorm V = infBoundaryDilatation V := by
  sorry

/-- **Lemma 1** (§14.1, l. 9981; [EGL98b]). If `μ` represents an element of `Z₀`, then its harmonic representative
`ρ⁻² ψ̄` vanishes at infinity. -/
theorem lemma14_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R)
    (hμ0 : (fun φ => pairingRS φ μ) ∈ zZeroSpace R) {ν : R → ℂ → ℂ} (hν : ν ∈ beltramiSpace R)
    (hνh : IsHarmonicBeltrami upperHalf (liftBeltrami p ν))
    (hνμ : ∀ φ ∈ integrableHolQDSet R, pairingRS φ ν = pairingRS φ μ) :
    IsVanishingAtInfinity p ν := by
  sorry

/-- **Corollary 1** (§14.1, l. 10029). For a bounded linear operator `L : Z → Z` with `L(Z₀) ⊆ Z₀` and any `V ∈ Z`,
`β(L(V)) ≤ ‖L‖ β(V)`. -/
theorem cor14_1_1 {L : ((R → ℂ → ℂ) → ℂ) → (R → ℂ → ℂ) → ℂ}
    (hLadd : ∀ V ∈ zSpace R, ∀ W ∈ zSpace R, L (V + W) = L V + L W)
    (hLsmul : ∀ c : ℂ, ∀ V ∈ zSpace R, L (c • V) = c • L V) (hLZ : ∀ V ∈ zSpace R, L V ∈ zSpace R)
    (hLZ0 : ∀ V ∈ zZeroSpace R, L V ∈ zZeroSpace R) (hLb : opNormZ L < ⊤) {V : (R → ℂ → ℂ) → ℂ}
    (hV : V ∈ zSpace R) :
    betaSeminorm (L V) ≤ opNormZ L * betaSeminorm V := by
  sorry

end GardinerLakic2000
