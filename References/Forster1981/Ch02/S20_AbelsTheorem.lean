import References.Forster1981.Ch02.S19_HarmonicDifferentialForms

/-!
# Forster, Chapter 2 §20: Abel's theorem

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §20 (`full.md` F1:7164–7508).

Conventions (ruling B0.10): `IsWeakSolution` is literal (20.1); 1-chains are `Chain1 X := C([0,1], X) →₀ ℤ`; `∂c = D` is the
relation `IsChainBoundary` (this avoids a local finiteness proof); `∫_c ω` is `HasChainIntegral`, built on Part A's
`HasClosedFormIntegral`; `Z₁(X)` is `IsCycle`. The first homology group `H₁(X)` is not defined (it appears only in remarks).
The logarithmic derivative `df/f` is `dlogForm f`, with junk values where `f` vanishes. The 2-forms `df/f ∧ σ` have a
singularity of type `1/z` at the zeros and poles of `f`, integrable and compactly supported; their integral is
`HasIntegral2`.
Reading: in 20.1, "the product `f₁/f₂` is not defined" is `f₁f₂` [misprint].

* Paragraph 20.1 (functions with prescribed divisors, weak solutions, F1:7168) — `IsWeakSolution`, `para20_1`
* Paragraph 20.2 (logarithmic differentiation, F1:7192) — `dlogForm`, `para20_2`
* Lemma 20.3 (F1:7212) — `lemma20_3`
* Paragraph 20.4 (chains, cycles, F1:7250) — `Chain1`, `IsChainBoundary`, `HasChainIntegral`, `IsCycle`, `para20_4`
* Lemma 20.5 (F1:7294) — `lemma20_5`
* Corollary 20.6 (F1:7338) — `cor20_6`
* Abel's theorem 20.7 (F1:7366) — `thm20_7`, `thm20_7_rem`

Omitted (U−): side claims of 20.1, 20.2 and 20.4 (`deg ∂c = 0`, homology), 20.8 (not cited).
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Weak solutions of a divisor** (20.1, Ch. 2 §20, F1:7168): a function `f` differentiable on `X_D = {x : D(x) ≥ 0}`
such that near every point `a` there are a coordinate neighbourhood `(U, z)` with `z(a) = 0` and a differentiable
`ψ` on `U` with `ψ(a) ≠ 0` and `f = ψ z^k` on `U ∩ X_D`, `k = D(a)`. -/
def IsWeakSolution (f : X → ℂ) (D : Function.locallyFinsupp X ℤ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {x | 0 ≤ D x} ∧
    ∀ a : X, ∃ e : OpenPartialHomeomorph X ℂ, e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ a ∈ e.source ∧ e a = 0 ∧
      ∃ ψ : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ e.source ∧ ψ a ≠ 0 ∧
        ∀ x ∈ e.source ∩ {x | 0 ≤ D x}, f x = ψ x * (e x) ^ (D a)

/-- **The logarithmic derivative** `df/f` (20.2, Ch. 2 §20, F1:7192): the 1-form with coefficients `f_z/f`, `f_z̄/f` in the
preferred charts (junk where `f` vanishes). -/
noncomputable def dlogForm (f : X → ℂ) : Form1 X :=
  (fun x z => (dForm f).1 x z / f ((chartAt ℂ x).symm z), fun x z => (dForm f).2 x z / f ((chartAt ℂ x).symm z))

/-- **1-chains** (20.4, Ch. 2 §20, F1:7250): formal finite integer combinations of curves `[0, 1] → X`. -/
abbrev Chain1 (X : Type) [TopologicalSpace X] : Type := C(unitInterval, X) →₀ ℤ

open scoped Classical in
/-- **The boundary** `∂c = D` (20.4, Ch. 2 §20, F1:7250): `∂γ = 0` for a closed curve, else `+1` at `γ(1)` and `−1` at `γ(0)`;
`∂ (Σ n_j c_j) = Σ n_j ∂c_j`. -/
def IsChainBoundary (c : Chain1 X) (D : Function.locallyFinsupp X ℤ) : Prop :=
  ∀ x, D x = ∑ γ ∈ c.support, c γ * ((if γ 0 ≠ γ 1 ∧ γ 1 = x then 1 else 0) - (if γ 0 ≠ γ 1 ∧ γ 0 = x then 1 else 0))

/-- **The integral over a chain** (20.4, Ch. 2 §20, F1:7250): `∫_c ω = Σ n_j ∫_{c_j} ω` for a closed 1-form `ω`. -/
def HasChainIntegral (w : Form1 X) (c : Chain1 X) (v : ℂ) : Prop :=
  ∃ vs : C(unitInterval, X) → ℂ, (∀ γ ∈ c.support, HasClosedFormIntegral w γ (vs γ)) ∧
    v = ∑ γ ∈ c.support, (c γ : ℂ) * vs γ

/-- **1-cycles** `Z₁(X)` (20.4, Ch. 2 §20, F1:7250): chains with `∂c = 0`. -/
def IsCycle (c : Chain1 X) : Prop := IsChainBoundary c 0

end Defs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Paragraph 20.1** (Ch. 2 §20, F1:7168). Two weak solutions of `D` differ by a differentiable factor which never
vanishes; if `f₁`, `f₂` are weak solutions of `D₁`, `D₂`, then `f₁f₂` (extended by continuity) is a weak solution of
`D₁ + D₂` and `f₁/f₂` (extended by continuity) is a weak solution of `D₁ − D₂`. -/
theorem para20_1 {D D₁ D₂ : Function.locallyFinsupp X ℤ} :
    (∀ f g, IsWeakSolution f D → IsWeakSolution g D → ∃ φ : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ φ ∧ (∀ x, φ x ≠ 0) ∧
      ∀ x, 0 ≤ D x → g x = φ x * f x) ∧
    (∀ f₁ f₂, IsWeakSolution f₁ D₁ → IsWeakSolution f₂ D₂ →
      (∃ f, IsWeakSolution f (D₁ + D₂) ∧ ∀ x, 0 ≤ D₁ x → 0 ≤ D₂ x → f x = f₁ x * f₂ x) ∧
      (∃ f, IsWeakSolution f (D₁ - D₂) ∧ ∀ x, 0 ≤ D₁ x → 0 ≤ D₂ x → f₂ x ≠ 0 → f x = f₁ x / f₂ x)) := by
  sorry

/-- **Paragraph 20.2** (Ch. 2 §20, F1:7192). For a weak solution `f` of `D`, the 1-form `d″f/f` extends to a differentiable
`(0, 1)`-form on all of `X`. -/
theorem para20_2 {D : Function.locallyFinsupp X ℤ} {f : X → ℂ} (hf : IsWeakSolution f D) :
    ∃ σ ∈ smoothForms01On X ⊤, Form1.EqOn σ (0, (dlogForm f).2) {x | 0 ≤ D x ∧ f x ≠ 0} := by
  sorry

open scoped Classical in
/-- **Lemma 20.3** (Ch. 2 §20, F1:7212). Let `a_1, …, a_n` be distinct points, `k_1, …, k_n ∈ ℤ`, `D` the divisor with
`D(a_j) = k_j` and `0` elsewhere, and `f` a weak solution of `D`. Then for any `g ∈ 𝓔(X)` with compact support:
`(1/2πi) ∬_X df/f ∧ dg = Σ k_j g(a_j)`. -/
theorem lemma20_3 {n : ℕ} {a : Fin n → X} (ha : Function.Injective a) (k : Fin n → ℤ)
    {D : Function.locallyFinsupp X ℤ} (hD : ∀ x, D x = ∑ j, if a j = x then k j else 0) {f : X → ℂ}
    (hf : IsWeakSolution f D) {g : X → ℂ} (hg : g ∈ smoothFunOn X ⊤) (hc : HasCompactSupport g) :
    HasIntegral2 (Form1.wedge (dlogForm f) (dForm g)) (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * g (a j)) := by
  sorry

/-- **Paragraph 20.4** (Ch. 2 §20, F1:7250). On a compact Riemann surface, for every divisor `D` with `deg D = 0` there is a
1-chain `c` with `∂c = D`. -/
theorem para20_4 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : divDeg D = 0) :
    ∃ c : Chain1 X, IsChainBoundary c D := by
  sorry

/-- **Lemma 20.5** (Ch. 2 §20, F1:7294). Let `c : [0, 1] → X` be a curve and `U` a relatively compact open neighbourhood of
`c([0, 1])`. Then there is a weak solution `f` of the divisor `∂c` with `f|(X ∖ U) = 1` such that for every closed
differentiable 1-form `ω`: `∫_c ω = (1/2πi) ∬_X df/f ∧ ω`. -/
theorem lemma20_5 (γ : C(unitInterval, X)) {U : Set X} (hU : IsOpen U) (hrel : IsCompact (closure U))
    (hγ : range γ ⊆ U) :
    ∃ (D : Function.locallyFinsupp X ℤ) (f : X → ℂ), IsChainBoundary (Finsupp.single γ 1) D ∧ IsWeakSolution f D ∧
      (∀ x, x ∉ U → f x = 1) ∧
      ∀ w ∈ smoothForms1On X ⊤, Form2.VanishOn w.d ⊤ → ∃ v, HasIntegral2 (Form1.wedge (dlogForm f) w) v ∧
        HasClosedFormIntegral w γ ((2 * Real.pi * Complex.I)⁻¹ * v) := by
  sorry

/-- **Corollary 20.6** (Ch. 2 §20, F1:7338). On a compact Riemann surface, for every closed curve `α` there is a unique
harmonic 1-form `σ_α ∈ Harm¹(X)` with `∫_α ω = ∬_X σ_α ∧ ω` for every closed 1-form `ω`. -/
theorem cor20_6 [CompactSpace X] {x₀ : X} (α : Path x₀ x₀) :
    ∃! σ : Form1 X, σ ∈ harmForms X ∧ ∀ w ∈ smoothForms1On X ⊤, Form2.VanishOn w.d ⊤ →
      ∃ v, HasClosedFormIntegral w α.toContinuousMap v ∧ HasIntegral2 (Form1.wedge σ w) v := by
  sorry

/-- **Abel's Theorem 20.7** (Ch. 2 §20, F1:7366). Let `D` be a divisor of degree `0` on a compact Riemann surface. Then `D`
has a solution (`D = (f)` for a meromorphic function) if and only if there is a 1-chain `c` with `∂c = D` and `∫_c ω = 0`
for every `ω ∈ Ω(X)`. -/
theorem thm20_7 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : divDeg D = 0) :
    IsPrincipalDivisor D ↔ ∃ c : Chain1 X, IsChainBoundary c D ∧ ∀ w ∈ holFormsOn X ⊤, HasChainIntegral w c 0 := by
  sorry

/-- **Remark to Abel's Theorem** (Ch. 2 §20, F1:7366). If `γ` is any 1-chain with `∂γ = D`, the condition of 20.7 reads:
there is a cycle `α ∈ Z₁(X)` with `∫_γ ω = ∫_α ω` for every `ω ∈ Ω(X)`. -/
theorem thm20_7_rem [CompactSpace X] {D : Function.locallyFinsupp X ℤ} {γ : Chain1 X} (hγ : IsChainBoundary γ D) :
    (∃ c : Chain1 X, IsChainBoundary c D ∧ ∀ w ∈ holFormsOn X ⊤, HasChainIntegral w c 0) ↔
      ∃ α : Chain1 X, IsCycle α ∧ ∀ w ∈ holFormsOn X ⊤, ∀ v, HasChainIntegral w γ v → HasChainIntegral w α v := by
  sorry

end Statements

end Forster1981
