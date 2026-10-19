import References.GardinerLakic2000.Ch15.S04_AsymptoticBeltramiCoefficients

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.1 Quasisymmetric homeomorphisms (with the chapter introduction)

Source `teichmuller.txt`, lines 11915–11964 (Chapter 16, introduction and §16.1).

* Definition (quasisymmetric homeomorphism of `S¹`, (16.1), l. 11922–11928) — exists:
  `Pommerenke1992.IsSensePreservingCircleHomeo` `Pommerenke1992.IsQuasisymmetricA` (equal chords ⇒ bounded ratio of
  the image chords: the same notion as (16.1), the lower bound following by symmetry)
* Definition (`M`-condition, the constant of quasisymmetry, (16.1), l. 11928) — `IsMCondition`
* Definition (`K`-condition, l. 11930) — `HasKCondition`
* Definition (`Φ(h) = [h̃]`, l. 11934) — `IsDiscBoundaryExt`, `IsQCExtCoeff`, `IsPhiQS`
* Theorem 1 (l. 11936) — `thm16_1`
* Definition (`A_h`, the Möbius map sending `h(1), h(i), h(−1)` to `1, i, −1`, l. 11941) — `IsNormalizingMobius`
* Corollary 1 (l. 11940) — `cor16_1_1`
* Definition (the neighbourhood systems `U(ε)`, `V(ε)` of the identity, l. 11949–11958) — `qsNbhdU`, `qsNbhdV`
* Unlabelled (the systems are Hausdorff, cofinal and satisfy (a), (b), l. 11959–11963; used in §16.2–16.3) —
  `para16_1_qs_system`

Not items: "QS is a group" (l. 11932, U−); "`T(Δ) ≅ QS mod PSL(2, ℝ)`" (l. 11947, the proof of Cor 1 restated).
Modelling (leader calibration of Part E, E0.1, E0.2, E0.4): circle maps are `h : ℂ → ℂ` read on `S¹ = sphere 0 1`;
the constant-free "quasisymmetric" is Pommerenke's pair of predicates (no second predicate), and `IsMCondition h M`
carries the book's constant in the `e^{i(x ± t)}` form. `T(Δ)` is batch A's `TeichSpace` of the Riemann surface
`LiZhongQC.unitDiscOpens` for a uniformization `p` (E0.1). `Φ` is a relation: `P` is the class of the coefficient of a
quasiconformal self-map `g` of `Δ` whose boundary values (limits at points of `S¹`) are `h`. The disc Möbius group
`G` is `Pommerenke1992.mobDisc` (acting on `ℂ̂`). Corollary 1 [reading, E0.4] is the bijection `h ↦ (A_h, Φ(h))` of
QS onto `G × T(Δ)` (modulo equality on `S¹`); the manifold structure it induces is not captured. `h⁻¹` on `S¹` is
`Function.invFunOn h (sphere 0 1)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC IsQCRS unitDisc unitDiscOpens ExtPlane)

/-- **Definition** (`M`-condition, (16.1), §16.1, l. 11922–11928). For all `x` and all `t` not a multiple of `2π`,
`1/M ≤ |h(e^{i(x+t)}) − h(e^{ix})| / |h(e^{ix}) − h(e^{i(x−t)})| ≤ M`. The constant-free notion is
`Pommerenke1992.IsQuasisymmetricA`. -/
def IsMCondition (h : ℂ → ℂ) (M : ℝ) : Prop :=
  ∀ x t : ℝ, (∀ k : ℤ, t ≠ 2 * π * k) →
    1 / M ≤ ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ / ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ∧
      ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ / ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ≤ M

/-- **Definition** (`K`-condition, §16.1, l. 11930). `h` has a `K`-quasiconformal extension to `Δ`: a `K`-q.c. map
of `Δ` onto `Δ`, continuous on `Δ̄`, equal to `h` on `S¹`. -/
def HasKCondition (h : ℂ → ℂ) (K : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, IsKQC F unitDisc K ∧ F '' unitDisc = unitDisc ∧ ContinuousOn F (closedBall 0 1) ∧
    ∀ z ∈ sphere (0 : ℂ) 1, F z = h z

/-- Helper (§16.1, l. 11934). The self-map `g` of `Δ` has boundary values `h` on `S¹`. -/
def IsDiscBoundaryExt (g : unitDiscOpens → unitDiscOpens) (h : ℂ → ℂ) : Prop :=
  ∀ z ∈ sphere (0 : ℂ) 1, Tendsto (fun w : unitDiscOpens => ((g w : unitDiscOpens) : ℂ))
    (comap (fun w : unitDiscOpens => (w : ℂ)) (𝓝 z)) (𝓝 (h z))

/-- Helper (§16.1, l. 11934). `μ` is the Beltrami coefficient of a quasiconformal self-map of `Δ` with boundary
values `h`. -/
def IsQCExtCoeff (h : ℂ → ℂ) (μ : unitDiscOpens → ℂ → ℂ) : Prop :=
  ∃ g : unitDiscOpens ≃ₜ unitDiscOpens, IsQCRS g ∧ HasBeltramiCoeff (g : unitDiscOpens → unitDiscOpens) μ ∧
    IsDiscBoundaryExt g h

/-- **Definition** (`Φ(h) = [h̃]`, §16.1, l. 11934). `P ∈ T(Δ)` is the class of the Beltrami coefficient of a
quasiconformal self-map of `Δ` extending `h`. -/
def IsPhiQS (p : UpperHalfPlane → unitDiscOpens) (h : ℂ → ℂ) (P : TeichSpace unitDiscOpens p) : Prop :=
  ∃ μ : beltramiBall unitDiscOpens, Quot.mk (teichRel p) μ = P ∧ IsQCExtCoeff h μ.1

/-- **Theorem 1** (§16.1, l. 11936). `Φ : QS → T(Δ)` is well defined, surjective, and `Φ(h₁) = Φ(h₂)` if and only if
`A ∘ h₂ = h₁` for a Möbius transformation `A` (preserving `Δ`). -/
theorem thm16_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : UpperHalfPlane → unitDiscOpens} (hp : LiZhongQC.IsUniformization Γ p) :
    (∀ h : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo h → Pommerenke1992.IsQuasisymmetricA h →
      (∃ P, IsPhiQS p h P) ∧ ∀ P Q, IsPhiQS p h P → IsPhiQS p h Q → P = Q) ∧
    (∀ P : TeichSpace unitDiscOpens p, ∃ h : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo h ∧
      Pommerenke1992.IsQuasisymmetricA h ∧ IsPhiQS p h P) ∧
    ∀ (h₁ h₂ : ℂ → ℂ) (P₁ P₂ : TeichSpace unitDiscOpens p), IsPhiQS p h₁ P₁ → IsPhiQS p h₂ P₂ →
      (P₁ = P₂ ↔ ∃ A ∈ Pommerenke1992.mobDisc, ∀ z ∈ sphere (0 : ℂ) 1, ((h₁ z : ℂ) : ExtPlane) = A (h₂ z)) := by
  sorry

/-- **Definition** (`A_h`, §16.1, l. 11941). `A` is the Möbius transformation of `Δ` mapping `h(1)`, `h(i)`, `h(−1)`
to `1`, `i`, `−1`. -/
def IsNormalizingMobius (h : ℂ → ℂ) (A : ExtPlane → ExtPlane) : Prop :=
  A ∈ Pommerenke1992.mobDisc ∧ A (h 1) = ((1 : ℂ) : ExtPlane) ∧ A (h I) = ((I : ℂ) : ExtPlane) ∧
    A (h (-1)) = ((-1 : ℂ) : ExtPlane)

/-- **Corollary 1** (§16.1, l. 11940). `QS` is isomorphic to `PSL(2, ℝ) × T(Δ)` via `h ↦ (A_h, Φ(h))`: for every
`A ∈ G` and `P ∈ T(Δ)` there is `h ∈ QS` with `A_h = A` and `Φ(h) = P`, unique on `S¹`. -/
theorem cor16_1_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : UpperHalfPlane → unitDiscOpens} (hp : LiZhongQC.IsUniformization Γ p) :
    (∀ A ∈ Pommerenke1992.mobDisc, ∀ P : TeichSpace unitDiscOpens p, ∃ h : ℂ → ℂ,
      Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetricA h ∧
        IsNormalizingMobius h A ∧ IsPhiQS p h P) ∧
    ∀ (h₁ h₂ : ℂ → ℂ) (A : ExtPlane → ExtPlane) (P : TeichSpace unitDiscOpens p),
      Pommerenke1992.IsSensePreservingCircleHomeo h₁ → Pommerenke1992.IsSensePreservingCircleHomeo h₂ →
      IsNormalizingMobius h₁ A → IsNormalizingMobius h₂ A → IsPhiQS p h₁ P → IsPhiQS p h₂ P →
        ∀ z ∈ sphere (0 : ℂ) 1, h₁ z = h₂ z := by
  sorry

/-- **Definition** (`U(ε)`, §16.1, l. 11949–11952). The quasisymmetric `h` with `|h(z) − z|, |h⁻¹(z) − z| < ε` on
`S¹` satisfying an `M`-condition with `M = 1 + ε`. -/
def qsNbhdU (ε : ℝ) : Set (ℂ → ℂ) :=
  {h | Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetricA h ∧
    (∀ z ∈ sphere (0 : ℂ) 1, ‖h z - z‖ < ε ∧ ‖Function.invFunOn h (sphere 0 1) z - z‖ < ε) ∧ IsMCondition h (1 + ε)}

/-- **Definition** (`V(ε)`, §16.1, l. 11954–11956). As `U(ε)`, with a `K`-condition with `K = 1 + ε` in place of the
`M`-condition. -/
def qsNbhdV (ε : ℝ) : Set (ℂ → ℂ) :=
  {h | Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetricA h ∧
    (∀ z ∈ sphere (0 : ℂ) 1, ‖h z - z‖ < ε ∧ ‖Function.invFunOn h (sphere 0 1) z - z‖ < ε) ∧ HasKCondition h (1 + ε)}

/-- **Unlabelled** (§16.1, l. 11959–11963; used in §16.2–16.3). The systems `U(ε)`, `V(ε)` are Hausdorff (only the
identity lies in all of them), cofinal with each other, and satisfy (a) `U(δ) ∘ U(δ) ⊆ U(ε)`, (b) `U(δ)⁻¹ ⊆ U(ε)`;
the same for `V`. -/
theorem para16_1_qs_system :
    (∀ h : ℂ → ℂ, (∀ ε > 0, h ∈ qsNbhdU ε) → ∀ z ∈ sphere (0 : ℂ) 1, h z = z) ∧
    (∀ h : ℂ → ℂ, (∀ ε > 0, h ∈ qsNbhdV ε) → ∀ z ∈ sphere (0 : ℂ) 1, h z = z) ∧
    (∀ ε > 0, ∃ δ > 0, qsNbhdV δ ⊆ qsNbhdU ε ∧ qsNbhdU δ ⊆ qsNbhdV ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, ∀ g ∈ qsNbhdU δ, f ∘ g ∈ qsNbhdU ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, Function.invFunOn f (sphere 0 1) ∈ qsNbhdU ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdV δ, ∀ g ∈ qsNbhdV δ, f ∘ g ∈ qsNbhdV ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdV δ, Function.invFunOn f (sphere 0 1) ∈ qsNbhdV ε) := by
  sorry

end GardinerLakic2000
