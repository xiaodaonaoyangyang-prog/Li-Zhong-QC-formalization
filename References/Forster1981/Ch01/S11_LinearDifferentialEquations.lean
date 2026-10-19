import References.Forster1981.Ch01.S10_TheIntegrationOfDifferentialForms

/-!
# Forster, Chapter 1 §11: Linear differential equations

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §11 (`full.md` F1:3271–3984).

Conventions: a system `dw = Aw` on a Riemann surface has `A` a matrix of holomorphic 1-forms (`Form1Matrix`) and `w` a
vector of functions; `dw = Aw` means that in every preferred chart `∂(w ∘ φ⁻¹)/∂z` is the `dz`-coefficient of `A` times
`w ∘ φ⁻¹`. On an open subset of `ℂ` (the punctured disc), the system `w′ = Aw` with `A` a matrix of functions is the system
with `coordForm A = A dz`. "The universal covering" quantifies over every universal covering; the logarithm of the punctured
disc `X = {0 < |z| < R}` is data `IsLogData p lg σ` (11.7). `z^ρ := exp (ρ log z)`. `exp A` is `NormedSpace.exp` on matrices.

* Notation 11.1 (`M(n × m, 𝒪(X))`, `GL(n, 𝒪(X))`, F1:3275) — `IsHolomorphicMatrix`, `IsHolomorphicGL`
* Theorem 11.2 (F1:3283) — `thm11_2`
* Paragraph 11.3 (`dw = Aw`, F1:3399) — `Form1Matrix`, `Form1Matrix.IsHolomorphic`, `Form1Matrix.pullback`, `IsSolutionODE`
* Theorem 11.4 (F1:3413) — `thm11_4`
* Corollary 11.5 (F1:3445) — `cor11_5`
* Paragraph 11.6 (factors of automorphy, F1:3453) — `solutionSpaceODE`, `IsFundamentalSystem`, `IsFactorOfAutomorphy`,
  `para11_6_a`, `para11_6_b`, `para11_6_c`
* Paragraph 11.7 (the logarithm on the universal covering of the punctured disc, F1:3509) — `punctDisc`, `IsLogData`,
  `para11_7`
* Paragraph 11.8(a), (b) (the exponential of matrices, F1:3541) — exists: `NormedSpace.exp`, `Matrix.exp_add_of_commute`,
  `Matrix.exp_conj`
* Paragraph 11.8(c) (F1:3541) — `para11_8_c`
* Paragraph 11.9 (F1:3591) — `dMulRight`, `dMulLeft`, `para11_9`
* Theorem 11.10 (F1:3607) — `coordForm`, `thm11_10`
* Theorem 11.11 (F1:3641) — `thm11_11`
* Paragraph 11.12 (regular singular point, F1:3671) — `extendPunct`, `IsRegularSingularPoint`
* Theorem 11.13 (F1:3673) and its lemmas (1), (2) — `thm11_13`, `lemma11_13_1`, `lemma11_13_2`
* Theorem 11.14 (F1:3785) — `secondOrderSystem`, `thm11_14`

Omitted (U−): 11.3 reduction to 11.2 in a chart, the Jordan normal form remark after 11.7, the log-series construction in the
proof of 11.8(c), the remark after 11.10, Bessel's equation (11.15).
-/

open scoped Manifold ContDiff Topology Matrix
open Set Filter

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **`M(n × m, 𝒪(X))`** (11.1, Ch. 1 §11, F1:3275): matrices of holomorphic functions. -/
def IsHolomorphicMatrix {n m : ℕ} (A : X → Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∀ i j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => A x i j)

/-- **`GL(n, 𝒪(X))`** (11.1, Ch. 1 §11, F1:3275): holomorphic matrices with invertible values. -/
def IsHolomorphicGL {n : ℕ} (A : X → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsHolomorphicMatrix A ∧ ∀ x, IsUnit (A x)

/-- **Matrices of 1-forms** (11.3, Ch. 1 §11, F1:3399): `M(n × n, Ω(X))` once `Form1Matrix.IsHolomorphic`. -/
abbrev Form1Matrix (X : Type) (n : ℕ) : Type := Fin n → Fin n → Form1 X

/-- A matrix of holomorphic 1-forms on `X` (11.3, Ch. 1 §11, F1:3399). -/
def Form1Matrix.IsHolomorphic {n : ℕ} (A : Form1Matrix X n) : Prop :=
  ∀ i j, (A i j).IsForm ∧ (A i j).IsHolomorphicOn univ

/-- The entrywise pull-back of a matrix of 1-forms (11.5, Ch. 1 §11, F1:3445). -/
noncomputable def Form1Matrix.pullback {Xt : Type} [TopologicalSpace Xt] [ChartedSpace ℂ Xt] {n : ℕ} (p : Xt → X)
    (A : Form1Matrix X n) : Form1Matrix Xt n := fun i j => Form1.pullback p (A i j)

/-- **The system `dw = Aw`** (11.3, Ch. 1 §11, F1:3399): in every preferred chart, the derivative of `w ∘ φ⁻¹` is the
`dz`-coefficient of `A` applied to `w ∘ φ⁻¹`. -/
def IsSolutionODE {n : ℕ} (A : Form1Matrix X n) (w : X → Fin n → ℂ) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target →
    HasDerivAt (fun u => w ((chartAt ℂ x).symm u))
      (fun i => ∑ j, (A i j).1 x z * w ((chartAt ℂ x).symm z) j) z

/-- **The solution space `L_A`** (11.6, Ch. 1 §11, F1:3453): holomorphic solutions on `X̃` of the pulled-back system
`dw = (p^*A) w` (the set is a ℂ-subspace; it is taken as a span). -/
noncomputable def solutionSpaceODE {Xt : Type} [TopologicalSpace Xt] [ChartedSpace ℂ Xt] {n : ℕ} (p : Xt → X)
    (A : Form1Matrix X n) : Submodule ℂ (Xt → Fin n → ℂ) :=
  Submodule.span ℂ {w | (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun y => w y i)) ∧ IsSolutionODE (Form1Matrix.pullback p A) w}

/-- **Fundamental systems** (11.6, Ch. 1 §11, F1:3453): a holomorphic `Φ : X̃ → GL(n, ℂ)` whose columns lie in `L_A`. -/
def IsFundamentalSystem {Xt : Type} [TopologicalSpace Xt] [ChartedSpace ℂ Xt] {n : ℕ} (p : Xt → X)
    (A : Form1Matrix X n) (Φ : Xt → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsHolomorphicGL Φ ∧ ∀ j, (fun y i => Φ y i j) ∈ solutionSpaceODE p A

/-- **Factors of automorphy** (11.6, Ch. 1 §11, F1:3453): `σΦ = Φ T_σ`, i.e. `Φ ∘ σ⁻¹ = Φ T_σ`, for every covering
transformation `σ`. -/
def IsFactorOfAutomorphy {Xt : Type} [TopologicalSpace Xt] {Z : Type} [TopologicalSpace Z] {n : ℕ} (p : Xt → Z)
    (Φ : Xt → Matrix (Fin n) (Fin n) ℂ) (T : ↥(deck p) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (σ : ↥(deck p)) (y : Xt), Φ (σ.1.symm y) = Φ y * T σ

end Defs

/-- **The punctured disc** `{0 < |z| < R}`, `0 < R ≤ ∞` (11.7, Ch. 1 §11, F1:3509), as an open subset of `ℂ`. -/
noncomputable def punctDisc (R : ENNReal) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.eball 0 R \ {0}, Metric.isOpen_eball.sdiff isClosed_singleton⟩

/-- **Logarithm data on the universal covering of the punctured disc** (11.7, Ch. 1 §11, F1:3509): a holomorphic
`log : X̃ → ℂ` with `exp ∘ log = p` and a generator `σ` of `Deck(X̃/X) ≅ ℤ` with `log ∘ σ⁻¹ = log + 2πi`. -/
def IsLogData {R : ENNReal} {Xt : Type} [TopologicalSpace Xt] [ChartedSpace ℂ Xt] (p : Xt → ↥(punctDisc R))
    (lg : Xt → ℂ) (σ : ↥(deck p)) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) lg ∧ (∀ y, ((p y : ↥(punctDisc R)) : ℂ) = Complex.exp (lg y)) ∧
    Subgroup.zpowers σ = ⊤ ∧ ∀ y, lg (σ.1.symm y) = lg y + 2 * Real.pi * Complex.I

/-- **The product `dA · B`** of the differential of a matrix of functions with a matrix of functions (11.9, Ch. 1 §11,
F1:3591). -/
noncomputable def dMulRight {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ}
    (A B : X → Matrix (Fin n) (Fin n) ℂ) : Form1Matrix X n :=
  fun i j => ∑ k, Form1.smulFun (fun x => B x k j) (dForm fun x => A x i k)

/-- **The product `A · dB`** (11.9, Ch. 1 §11, F1:3591). -/
noncomputable def dMulLeft {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ}
    (A B : X → Matrix (Fin n) (Fin n) ℂ) : Form1Matrix X n :=
  fun i j => ∑ k, Form1.smulFun (fun x => A x i k) (dForm fun x => B x k j)

/-- **The form `A dz`** of a matrix of functions on an open subset `X ⊆ ℂ` (11.10, Ch. 1 §11, F1:3607): the chart
coordinate of the open subset is `z`, so this is the system `w′ = Aw`. -/
noncomputable def coordForm {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℂ) : Form1Matrix X n :=
  fun i j => (fun x => (chartAt ℂ x).target.indicator (fun u => A ((chartAt ℂ x).symm u) i j), 0)

open scoped Classical in
/-- The extension by `0` of a function on the punctured disc to `ℂ`. -/
noncomputable def extendPunct {R : ENNReal} (f : ↥(punctDisc R) → ℂ) : ℂ → ℂ :=
  fun z => if h : z ∈ (punctDisc R : Set ℂ) then f ⟨z, h⟩ else 0

/-- **Regular singular point** (11.12, Ch. 1 §11, F1:3671). The origin is a regular singular point of `w′ = Aw` on the
punctured disc if there are a constant matrix `B` and `Ψ ∈ GL(n, 𝒪(X))` with only a pole at `0` such that
`Φ = (Ψ ∘ p) exp(B log)` is a fundamental system (as in 11.11).
Modelling: for the given logarithm data `p`, `log` (the property does not depend on the choice). -/
def IsRegularSingularPoint {R : ENNReal} {Xt : Type} [TopologicalSpace Xt] [ChartedSpace ℂ Xt]
    (p : Xt → ↥(punctDisc R)) (lg : Xt → ℂ) {n : ℕ} (A : ↥(punctDisc R) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (B : Matrix (Fin n) (Fin n) ℂ) (Ψ : ↥(punctDisc R) → Matrix (Fin n) (Fin n) ℂ), IsHolomorphicGL Ψ ∧
    IsFundamentalSystem p (coordForm A) (fun y => Ψ (p y) * NormedSpace.exp (lg y • B)) ∧
      ∀ i j, MeromorphicAt (extendPunct (fun x => Ψ x i j)) 0

/-- The first order system of `w″ + (a(z)/z) w′ + (b(z)/z²) w = 0` for `w = (φ, φ′)` (11.14, Ch. 1 §11, F1:3785). -/
noncomputable def secondOrderSystem {R : ENNReal} (a b : ℂ → ℂ) : ↥(punctDisc R) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun x => !![0, 1; -(b x / (x : ℂ) ^ 2), -(a x / (x : ℂ))]

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 11.2** (Ch. 1 §11, F1:3283). Let `A` be a matrix of holomorphic functions on the disc `D = {|z| < R}`,
`0 < R ≤ ∞`, and `w₀ ∈ ℂⁿ`. Then there is exactly one holomorphic `w : D → ℂⁿ` with `w′ = Aw` and `w(0) = w₀`.
Modelling: uniqueness is on `D` (values outside `D` are not constrained). -/
theorem thm11_2 {n : ℕ} {R : ENNReal} (hR : 0 < R) {A : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.eball 0 R)) (w₀ : Fin n → ℂ) :
    ∃ w : ℂ → Fin n → ℂ, DifferentiableOn ℂ w (Metric.eball 0 R) ∧
      (∀ z ∈ Metric.eball (0 : ℂ) R, HasDerivAt w (A z *ᵥ w z) z) ∧ w 0 = w₀ ∧
      ∀ w' : ℂ → Fin n → ℂ, DifferentiableOn ℂ w' (Metric.eball 0 R) →
        (∀ z ∈ Metric.eball (0 : ℂ) R, HasDerivAt w' (A z *ᵥ w' z) z) → w' 0 = w₀ →
          ∀ z ∈ Metric.eball (0 : ℂ) R, w' z = w z := by
  sorry

/-- **Theorem 11.4** (Ch. 1 §11, F1:3413). Let `X` be a simply connected Riemann surface, `A ∈ M(n × n, Ω(X))`,
`x₀ ∈ X` and `c ∈ ℂⁿ`. Then there is exactly one holomorphic `w : X → ℂⁿ` with `dw = Aw` and `w(x₀) = c`. -/
theorem thm11_4 [SimplyConnectedSpace X] {n : ℕ} {A : Form1Matrix X n} (hA : A.IsHolomorphic) (x₀ : X)
    (c : Fin n → ℂ) :
    ∃! w : X → Fin n → ℂ, (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => w x i)) ∧ IsSolutionODE A w ∧ w x₀ = c := by
  sorry

/-- **Corollary 11.5** (Ch. 1 §11, F1:3445). Let `p : X̃ → X` be the universal covering, `y₀ ∈ X̃`, `c ∈ ℂⁿ`. Then
`dw = (p^*A) w` has exactly one holomorphic solution `w` on `X̃` with `w(y₀) = c`. -/
theorem cor11_5 {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {n : ℕ}
    {A : Form1Matrix X n} (hA : A.IsHolomorphic) (y₀ : Xt) (c : Fin n → ℂ) :
    ∃! w : Xt → Fin n → ℂ, (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun y => w y i)) ∧
      IsSolutionODE (Form1Matrix.pullback p A) w ∧ w y₀ = c := by
  sorry

/-- **Paragraph 11.6(a)** (Ch. 1 §11, F1:3453). The solution space `L_A` is an `n`-dimensional ℂ-vector space, and
`w₁, …, wₙ ∈ L_A` are linearly independent if and only if `w₁(a), …, wₙ(a)` are, for any `a ∈ X̃`. -/
theorem para11_6_a {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {n : ℕ}
    {A : Form1Matrix X n} (hA : A.IsHolomorphic) :
    Module.finrank ℂ (solutionSpaceODE p A) = n ∧
      ∀ (ws : Fin n → ↥(solutionSpaceODE p A)) (a : Xt),
        LinearIndependent ℂ ws ↔ LinearIndependent ℂ (fun i => (ws i : Xt → Fin n → ℂ) a) := by
  sorry

/-- **Paragraph 11.6(b)** (Ch. 1 §11, F1:3453). For a fundamental system `Φ` and `σ ∈ Deck(X̃/X)` there is a unique
`T_σ ∈ GL(n, ℂ)` with `σΦ = ΦT_σ`, and `T_{τσ} = T_τ T_σ`: a homomorphism `Deck(X̃/X) → GL(n, ℂ)`. -/
theorem para11_6_b {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {n : ℕ}
    {A : Form1Matrix X n} (hA : A.IsHolomorphic) {Φ : Xt → Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsFundamentalSystem p A Φ) :
    (∀ σ : ↥(deck p), ∃! T : Matrix (Fin n) (Fin n) ℂ, ∀ y, Φ (σ.1.symm y) = Φ y * T) ∧
      ∀ T : ↥(deck p) → Matrix (Fin n) (Fin n) ℂ, IsFactorOfAutomorphy p Φ T →
        ∀ σ τ : ↥(deck p), IsUnit (T σ) ∧ T (τ * σ) = T τ * T σ := by
  sorry

/-- **Paragraph 11.6(c)** (Ch. 1 §11, F1:3453). Conversely, for a homomorphism `T : Deck(X̃/X) → GL(n, ℂ)` and a
holomorphic `Φ : X̃ → GL(n, ℂ)` with `σΦ = ΦT_σ` there is `A ∈ M(n × n, Ω(X))` with `p^*A = dΦ · Φ⁻¹`, and `Φ` is a
fundamental system of `dw = Aw`. -/
theorem para11_6_c {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {n : ℕ}
    (T : ↥(deck p) →* Matrix.GeneralLinearGroup (Fin n) ℂ) {Φ : Xt → Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsHolomorphicGL Φ) (hT : IsFactorOfAutomorphy p Φ (fun σ => ((T σ : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ))) :
    ∃ A : Form1Matrix X n, A.IsHolomorphic ∧
      (∀ i j, Form1.pullback p (A i j) =
        ∑ k, Form1.smulFun (fun y => (Φ y)⁻¹ k j) (dForm fun y => Φ y i k)) ∧ IsFundamentalSystem p A Φ := by
  sorry

/-- **Paragraph 11.7** (Ch. 1 §11, F1:3509). For the punctured disc `X = {0 < |z| < R}` and its universal covering there are
a holomorphic `log : X̃ → ℂ` with `exp ∘ log = p` and a generator `σ` of `Deck(X̃/X) ≅ ℤ` with `log ∘ σ⁻¹ = log + 2πi`. -/
theorem para11_7 {R : ENNReal} (hR : 0 < R) {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt]
    [ChartedSpace ℂ Xt] [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → ↥(punctDisc R)} (hp : IsUniversalCovering p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) : ∃ (lg : Xt → ℂ) (σ : ↥(deck p)), IsLogData p lg σ := by
  sorry

/-- **Paragraph 11.8(c)** (Ch. 1 §11, F1:3541). Every `B ∈ GL(n, ℂ)` is of the form `exp A` for some `A ∈ M(n × n, ℂ)`.
Modelling: (a) `AB = BA ⇒ exp(A + B) = exp A exp B` and (b) `exp(S⁻¹AS) = S⁻¹(exp A)S` exist as `Matrix.exp_add_of_commute`,
`Matrix.exp_conj`. -/
theorem para11_8_c {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp A = B := by
  sorry

/-- **Paragraph 11.9** (Ch. 1 §11, F1:3591). If `A` is a holomorphic matrix, so is `exp A`; if moreover
`A · dA = dA · A`, then `d(exp A) = dA · exp A = exp A · dA`. -/
theorem para11_9 {n : ℕ} {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : IsHolomorphicMatrix A) :
    IsHolomorphicMatrix (fun x => NormedSpace.exp (A x)) ∧
      (dMulLeft A A = dMulRight A A →
        (fun i j => dForm fun x => NormedSpace.exp (A x) i j) = dMulRight A (fun x => NormedSpace.exp (A x)) ∧
        (fun i j => dForm fun x => NormedSpace.exp (A x) i j) = dMulLeft (fun x => NormedSpace.exp (A x)) A) := by
  sorry

/-- **Theorem 11.10** (Ch. 1 §11, F1:3607). Let `T ∈ GL(n, ℂ)` and `B` with `exp(2πiB) = T`, and let `p`, `log`, `σ` be as
in 11.7 for `X = {0 < |z| < R}`. Then `Φ₀ := exp(B log)` is a fundamental system of `w′ = (1/z)Bw` on `X̃`, and
`σΦ₀ = Φ₀T`. -/
theorem thm11_10 {R : ENNReal} {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → ↥(punctDisc R)} (hp : IsUniversalCovering p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {lg : Xt → ℂ} {σ : ↥(deck p)} (hlg : IsLogData p lg σ) {n : ℕ}
    {T B : Matrix (Fin n) (Fin n) ℂ} (hT : IsUnit T) (hB : NormedSpace.exp ((2 * Real.pi * Complex.I) • B) = T) :
    IsFundamentalSystem p (coordForm (fun x : ↥(punctDisc R) => ((x : ℂ))⁻¹ • B))
        (fun y => NormedSpace.exp (lg y • B)) ∧
      ∀ y, NormedSpace.exp (lg (σ.1.symm y) • B) = NormedSpace.exp (lg y • B) * T := by
  sorry

/-- **Theorem 11.11** (Ch. 1 §11, F1:3641). Let `A ∈ M(n × n, 𝒪(X))` on the punctured disc `X`. Then `w′ = Aw` has a
fundamental system `Φ = ΨΦ₀`, `Φ₀ = exp(B log)` for a constant matrix `B`, with `Ψ` invariant under the covering
transformations, i.e. `Ψ = Ψ₀ ∘ p` for some `Ψ₀ ∈ GL(n, 𝒪(X))`. -/
theorem thm11_11 {R : ENNReal} {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → ↥(punctDisc R)} (hp : IsUniversalCovering p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {lg : Xt → ℂ} {σ : ↥(deck p)} (hlg : IsLogData p lg σ) {n : ℕ}
    {A : ↥(punctDisc R) → Matrix (Fin n) (Fin n) ℂ} (hA : IsHolomorphicMatrix A) :
    ∃ (Φ : Xt → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (Ψ₀ : ↥(punctDisc R) → Matrix (Fin n) (Fin n) ℂ),
      IsFundamentalSystem p (coordForm A) Φ ∧ IsHolomorphicGL Ψ₀ ∧
        ∀ y, Φ y = Ψ₀ (p y) * NormedSpace.exp (lg y • B) := by
  sorry

/-- **Lemma (1) in the proof of Theorem 11.13** (Ch. 1 §11, F1:3677). Let `K ≥ 0` and `F : ]0, r₀] → ℝ_{>0}` be `C^1` with
`|F′(r)| ≤ (K/r) F(r)`. Then `F(r) ≤ F(r₀) (r/r₀)^{−K}` for `0 < r ≤ r₀`. -/
theorem lemma11_13_1 {K r₀ : ℝ} (hK : 0 ≤ K) (hr₀ : 0 < r₀) {F : ℝ → ℝ} (hpos : ∀ r ∈ Ioc 0 r₀, 0 < F r)
    (hF : ContDiffOn ℝ 1 F (Ioc 0 r₀)) (hd : ∀ r ∈ Ioc 0 r₀, |deriv F r| ≤ K / r * F r) :
    ∀ r ∈ Ioc 0 r₀, F r ≤ F r₀ * (r / r₀) ^ (-K) := by
  sorry

/-- **Lemma (2) in the proof of Theorem 11.13** (Ch. 1 §11, F1:3719). For `f` holomorphic on an open `U ⊆ ℂ \ {0}`,
the radial derivative of `|f|²` satisfies `|∂/∂r |f|²| ≤ 2 |f| |f′|`. -/
theorem lemma11_13_2 {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U)
    (hz0 : z ≠ 0) :
    |deriv (fun r : ℝ => ‖f (r * (z / ‖z‖))‖ ^ 2) ‖z‖| ≤ 2 * ‖f z‖ * ‖deriv f z‖ := by
  sorry

/-- **Theorem 11.13** (Ch. 1 §11, F1:3673). If `A ∈ M(n × n, 𝒪(X))` has at most a pole of first order at `0`, then `0` is a
regular singular point of `w′ = Aw`. -/
theorem thm11_13 {R : ENNReal} {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → ↥(punctDisc R)} (hp : IsUniversalCovering p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {lg : Xt → ℂ} {σ : ↥(deck p)} (hlg : IsLogData p lg σ) {n : ℕ}
    {A : ↥(punctDisc R) → Matrix (Fin n) (Fin n) ℂ} (hA : IsHolomorphicMatrix A)
    (hpole : ∀ i j, MeromorphicAt (extendPunct (fun x => A x i j)) 0 ∧
      -1 ≤ meromorphicOrderAt (extendPunct (fun x => A x i j)) 0) :
    IsRegularSingularPoint p lg A := by
  sorry

/-- **Theorem 11.14** (Ch. 1 §11, F1:3785). Let `a, b` be holomorphic on the disc `D = {|z| < R}`. On the universal
covering of `D \ {0}`, the equation `w″ + (a(z)/z) w′ + (b(z)/z²) w = 0` has a fundamental system `(φ₁, φ₂)` of either the
form `φ_j = z^{ρ_j} ψ_j` or the form `φ₁ = z^ρ ψ₁`, `φ₂ = z^ρ (ψ₁ log z + ψ₂)`, with `ρ, ρ_j ∈ ℂ` and `ψ_j ∈ 𝒪(D)`.
Modelling: solutions of the second order equation are the first components of the solutions `(φ, φ′)` of the system
`secondOrderSystem`; `z^ρ = exp (ρ log z)` and the `ψ_j` are pulled back to `X̃` by `p`. -/
theorem thm11_14 {R : ENNReal} (hR : 0 < R) {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt]
    [ChartedSpace ℂ Xt] [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → ↥(punctDisc R)} (hp : IsUniversalCovering p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {lg : Xt → ℂ} {σ : ↥(deck p)} (hlg : IsLogData p lg σ) {a b : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a (Metric.eball 0 R)) (hb : DifferentiableOn ℂ b (Metric.eball 0 R)) :
    ∃ φ₁ φ₂ φ₁' φ₂' : Xt → ℂ,
      IsFundamentalSystem p (coordForm (secondOrderSystem (R := R) a b))
        (fun y => !![φ₁ y, φ₂ y; φ₁' y, φ₂' y]) ∧
      ((∃ (ρ₁ ρ₂ : ℂ) (ψ₁ ψ₂ : ℂ → ℂ), DifferentiableOn ℂ ψ₁ (Metric.eball 0 R) ∧
          DifferentiableOn ℂ ψ₂ (Metric.eball 0 R) ∧
          (∀ y, φ₁ y = Complex.exp (ρ₁ * lg y) * ψ₁ ((p y : ↥(punctDisc R)) : ℂ)) ∧
          (∀ y, φ₂ y = Complex.exp (ρ₂ * lg y) * ψ₂ ((p y : ↥(punctDisc R)) : ℂ))) ∨
        (∃ (ρ : ℂ) (ψ₁ ψ₂ : ℂ → ℂ), DifferentiableOn ℂ ψ₁ (Metric.eball 0 R) ∧
          DifferentiableOn ℂ ψ₂ (Metric.eball 0 R) ∧
          (∀ y, φ₁ y = Complex.exp (ρ * lg y) * ψ₁ ((p y : ↥(punctDisc R)) : ℂ)) ∧
          (∀ y, φ₂ y = Complex.exp (ρ * lg y) * (ψ₁ ((p y : ↥(punctDisc R)) : ℂ) * lg y +
            ψ₂ ((p y : ↥(punctDisc R)) : ℂ))))) := by
  sorry

end Statements

end Forster1981
