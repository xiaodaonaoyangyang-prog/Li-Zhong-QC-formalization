import References.Pommerenke1992.Ch04.S02_BlochFunctions

/-!
# Pommerenke 1992, Ch. 4 §4.3 The Angular Derivative

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §4.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3323–3543.

* Definition (angular derivative, (4.3.1); cited at l. 4307) — `HasAngularDerivative`
* Proposition 4.7 — `prop4_7`
* Proposition 4.8 — `prop4_8`
* Proposition 4.9 — `prop4_9`
* Definition (conformal at `ζ ∈ 𝕋`; isogonal at `ζ`, (4.3.5); cited at l. 4333) — `IsConformalAtBoundary`,
  `IsIsogonalAt`
* Formula (4.3.6) (cited "(6)" after Proposition 4.12) — `eq4_3_6`
* Formula (4.3.7) (cited "(7)" after Proposition 4.12) — `eq4_3_7`
* Proposition 4.10 — `prop4_10`
* Proposition 4.11 (with the Visser–Ostrowski condition (4.3.8), cited at l. 4333) — `prop4_11`
* Proposition 4.12 (the Jordan-domain form; the quasidisk form is `prop4_12_quasidisk` in §5.4) — `prop4_12`
* Proposition 4.13 (Julia–Wolff) — `prop4_13`
* Theorem 4.14 (Carathéodory, Lelong-Ferrand) — `thm4_14`

Not items (DESIGN §3): the forward reference to Theorem 5.5 (l. 3331); the remarks after Propositions 4.11 and 4.12;
the remark after Theorem 4.14 on Jordan domains and the comparison-curve application (l. 3509, 3522; not cited).

**Conventions.** As in §4.2. Angular limits and Stolz angles are those of §1.2 (`HasAngularLimit`, `stolzAngleP`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- **Definition (4.3.1)** (§4.3; cited at l. 4307). The analytic function `f` has the angular derivative
`f'(ζ) ∈ Ĉ` at `ζ ∈ 𝕋`: the angular limit `f(ζ) ≠ ∞` exists and `(f(z) - f(ζ))/(z - ζ) → f'(ζ)` as `z → ζ`, `z ∈ Δ`,
for each Stolz angle `Δ` at `ζ` (the value `f'(ζ) = ∞` is allowed). -/
def HasAngularDerivative (f : ℂ → ℂ) (ζ : ℂ) (a : ExtPlane) : Prop :=
  ∃ fζ : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ ∧
    HasAngularLimit (fun z => ((f z - fζ) / (z - ζ) : ℂ)) ζ a

/-- **Proposition 4.7** (§4.3). The analytic function `f` has a finite angular derivative `f'(ζ)` if and only if `f'`
has the finite angular limit `f'(ζ)` at `ζ`. -/
theorem prop4_7 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (a : ℂ) :
    HasAngularDerivative f ζ a ↔ HasAngularLimit (fun z => ((deriv f z : ℂ) : ExtPlane)) ζ a := by
  sorry

/-- **Proposition 4.8** (§4.3; the book omits the proof). Let `h` be analytic in `𝔻`. If `Im h(z)` has a finite
angular limit at `ζ ∈ 𝕋`, then `(z - ζ) h'(z)` has the angular limit `0` at `ζ`. -/
theorem prop4_8 {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {c : ℝ}
    (hc : ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
      Tendsto (fun z => (h z).im) (𝓝[stolzAngleP ζ α ρ] ζ) (𝓝 c)) :
    HasAngularLimit (fun z => ((z - ζ) * deriv h z : ℂ)) ζ (0 : ℂ) := by
  sorry

/-- **Proposition 4.9** (§4.3). Let `f` map `𝔻` conformally into `ℂ` and let `f` have an angular limit `f(ζ) ≠ ∞` at
`ζ ∈ 𝕋`. If (4.3.3) `(f(z) - f(ζ))/(z - ζ) → a` as `z → ζ`, `z ∈ Γ`, for some curve `Γ` in `𝔻` ending at `ζ`, or if
(4.3.4) `f'(z) → a ≠ ∞` as `z → ζ`, `z ∈ Γ`, then `f'(ζ) = a` exists.
Modelling: in (4.3.3) `a ∈ Ĉ`, as the book does not exclude `∞` there. -/
theorem prop4_9 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) {fζ : ℂ} (hfζ : HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ) {Γ : Set ℂ}
    (hΓ : IsCurveEndingAt Γ ζ) :
    (∀ a : ExtPlane, Tendsto (fun z => ((f z - fζ) / (z - ζ) : ℂ) : ℂ → ExtPlane) (𝓝[Γ] ζ) (𝓝 a) →
      HasAngularDerivative f ζ a) ∧
    ∀ a : ℂ, Tendsto (deriv f) (𝓝[Γ] ζ) (𝓝 a) → HasAngularDerivative f ζ a := by
  sorry

/-- **Definition** (§4.3). `f` is conformal at `ζ ∈ 𝕋`: the angular derivative `f'(ζ)` exists and is `≠ 0, ∞`. -/
def IsConformalAtBoundary (f : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ HasAngularDerivative f ζ a

/-- **Definition (4.3.5)** (§4.3; cited at l. 4333). `f` is isogonal at `ζ ∈ 𝕋`: there is a finite angular limit
`f(ζ)` and `arg[(f(z) - f(ζ))/(z - ζ)] → γ` as `z → ζ`, `z ∈ Δ`, for some finite `γ` and every Stolz angle `Δ`.
Modelling: a limit of directions, `q/|q| → e^{iγ}` for `q = (f(z) - f(ζ))/(z - ζ)`. -/
def IsIsogonalAt (f : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ fζ : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ ∧ ∃ γ : ℝ,
    HasAngularLimit (fun z => ((f z - fζ) / (z - ζ) / (‖(f z - fζ) / (z - ζ)‖ : ℂ) : ℂ)) ζ (exp (γ * I))

/-- **Formula (4.3.6)** (§4.3; cited "(6)" after Proposition 4.12). `f` conformal at `ζ` implies `f` isogonal at `ζ`.
-/
theorem eq4_3_6 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hc : IsConformalAtBoundary f ζ) : IsIsogonalAt f ζ := by
  sorry

/-- **Formula (4.3.7)** (§4.3; cited "(7)" after Proposition 4.12). If `∂f(𝔻)` is locally connected, then, by Theorem
3.7 with `α = 1`, `∂G` has a tangent at `f(ζ)` ⇒ `f` is isogonal at `ζ`.
Modelling: the setting of §3.4 (`IsBoundarySetting`), a tangent being a corner of opening `π` (`HasTangentAt`, which
includes that `f(ζ)` is finite), `ζ = e^{iϑ}`. -/
theorem eq4_3_7 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ β : ℝ}
    (ht : HasTangentAt F ϑ β) : IsIsogonalAt f (exp (ϑ * I)) := by
  sorry

/-- **Proposition 4.10** (§4.3). If the conformal map `f` is isogonal at `ζ ∈ 𝕋`, then smooth curves in a Stolz angle
at `ζ` are mapped onto smooth curves, and the angles between curves are preserved.
Modelling: a smooth curve `Γ_j : z_j(τ)`, `0 ≤ τ ≤ 1`, in a Stolz angle `Δ` ending at `ζ` is a continuously
differentiable `z_j` with `z_j' ≠ 0`, `z_j(τ) ∈ Δ` for `τ < 1` and `z_j(1) = ζ`. Its image `w_j(τ) = f(z_j(τ))`
(with `w_j(1) = f(ζ)`, the angular limit) is smooth: it has a continuous tangent direction angle `θ_j` on `[0, 1]`
(the direction of `w_j'(τ)` for `τ < 1`, and the direction of `w_j(1) - w_j(τ)` as `τ → 1-`), and
`θ₁(1) - θ₂(1) ≡ arg z₁'(1) - arg z₂'(1)` modulo `2π`. Derivatives on `[0, 1]` are one-sided at the end points
(`derivWithin` on `Icc 0 1`).
The later uses (l. 6028, 6194, 6258; P2 l. 3311) apply the proposition to the sides of sectors or triangles at `ζ`
inside a Stolz angle, which are smooth curves of this kind. -/
theorem prop4_10 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) (hiso : IsIsogonalAt f ζ) {fζ : ℂ}
    (hfζ : HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ) {α ρ : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 2 * Real.cos α) {z₁ z₂ : ℝ → ℂ}
    (hz : ∀ j ∈ ({z₁, z₂} : Set (ℝ → ℂ)), ContDiffOn ℝ 1 j (Icc 0 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, derivWithin j (Icc 0 1) τ ≠ 0) ∧ (∀ τ ∈ Ico (0 : ℝ) 1, j τ ∈ stolzAngleP ζ α ρ) ∧
      j 1 = ζ) :
    ∃ θ₁ θ₂ : ℝ → ℝ, ContinuousOn θ₁ (Icc 0 1) ∧ ContinuousOn θ₂ (Icc 0 1) ∧
      (∀ τ ∈ Ico (0 : ℝ) 1, derivWithin (fun s => f (z₁ s)) (Icc 0 1) τ =
        (‖derivWithin (fun s => f (z₁ s)) (Icc 0 1) τ‖ : ℂ) * exp (θ₁ τ * I) ∧
          derivWithin (fun s => f (z₁ s)) (Icc 0 1) τ ≠ 0) ∧
      (∀ τ ∈ Ico (0 : ℝ) 1, derivWithin (fun s => f (z₂ s)) (Icc 0 1) τ =
        (‖derivWithin (fun s => f (z₂ s)) (Icc 0 1) τ‖ : ℂ) * exp (θ₂ τ * I) ∧
          derivWithin (fun s => f (z₂ s)) (Icc 0 1) τ ≠ 0) ∧
      Tendsto (fun τ => (fζ - f (z₁ τ)) / (‖fζ - f (z₁ τ)‖ : ℂ)) (𝓝[<] 1) (𝓝 (exp (θ₁ 1 * I))) ∧
      Tendsto (fun τ => (fζ - f (z₂ τ)) / (‖fζ - f (z₂ τ)‖ : ℂ)) (𝓝[<] 1) (𝓝 (exp (θ₂ 1 * I))) ∧
      exp ((θ₁ 1 - θ₂ 1) * I) =
        derivWithin z₁ (Icc 0 1) 1 / (‖derivWithin z₁ (Icc 0 1) 1‖ : ℂ) /
          (derivWithin z₂ (Icc 0 1) 1 / (‖derivWithin z₂ (Icc 0 1) 1‖ : ℂ)) := by
  sorry

/-- **Proposition 4.11** (§4.3). The conformal map `f` is isogonal at `ζ ∈ 𝕋` if and only if `f` and `arg f'` have
finite angular limits at `ζ`. In this case (4.3.8) `(z - ζ) f'(z)/(f(z) - f(ζ)) → 1` as `z → ζ` in every Stolz
angle.
Modelling: `arg f'` is `Im L` for a holomorphic logarithm `L` of `f'`. -/
theorem prop4_11 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) :
    (IsIsogonalAt f ζ ↔ (∃ fζ : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ) ∧
      ∃ c : ℝ, ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
        Tendsto (fun z => (L z).im) (𝓝[stolzAngleP ζ α ρ] ζ) (𝓝 c)) ∧
    (IsIsogonalAt f ζ → ∀ fζ : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ fζ →
      HasAngularLimit (fun z => ((z - ζ) * deriv f z / (f z - fζ) : ℂ)) ζ (1 : ℂ)) := by
  sorry

/-- **Proposition 4.12** (§4.3; proved in §8.6), the Jordan-domain form. There is a conformal map onto a Jordan
domain that is nowhere isogonal, and thus nowhere conformal, on `𝕋`.
Modelling: "(even a quasidisk)" is `prop4_12_quasidisk` in §5.4, where quasidisks are defined. -/
theorem prop4_12 :
    ∃ f : ℂ → ℂ, LiZhongQC.IsJordanDomain (f '' unitDisc) ∧ IsConformalOnto f unitDisc (f '' unitDisc) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, ¬ IsIsogonalAt f ζ := by
  sorry

/-- **Proposition 4.13** (§4.3; the Julia–Wolff lemma). Let `φ` be analytic in `𝔻` with an angular limit `φ(ζ)` at
`ζ ∈ 𝕋`. If `φ(𝔻) ⊆ 𝔻` and `φ(ζ) ∈ 𝕋`, then the angular derivative `φ'(ζ)` exists and (4.3.10)
`0 < ζ φ'(ζ)/φ(ζ) = sup_{z ∈ 𝔻} (1 - |z|²)/|ζ - z|² · |φ(ζ) - φ(z)|²/(1 - |φ(z)|²) ≤ +∞`.
Modelling: either `φ'(ζ)` is finite, `ζφ'(ζ)/φ(ζ)` is a positive real number and equals the supremum (in
`ℝ≥0∞`), or `φ'(ζ) = ∞` and the supremum is `∞`. -/
theorem prop4_13 {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hφD : MapsTo φ unitDisc unitDisc) {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) {φζ : ℂ} (hlim : HasAngularLimit (fun z => (φ z : ExtPlane)) ζ φζ)
    (hφζ : φζ ∈ sphere (0 : ℂ) 1) :
    (∃ a : ℂ, HasAngularDerivative φ ζ a ∧ 0 < (ζ * a / φζ).re ∧ (ζ * a / φζ).im = 0 ∧
      ENNReal.ofReal (ζ * a / φζ).re =
        ⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2 * (‖φζ - φ z‖ ^ 2 / (1 - ‖φ z‖ ^ 2)))) ∨
    (HasAngularDerivative φ ζ extInf ∧
      (⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2 * (‖φζ - φ z‖ ^ 2 / (1 - ‖φ z‖ ^ 2)))) = ⊤) := by
  sorry

/-- **Theorem 4.14** (§4.3; Carathéodory, Lelong-Ferrand). For `j = 1, 2` let `f_j` map `𝔻` conformally onto `G_j`,
where `G₁ ⊆ G₂`. Let `Γ` be a Jordan arc in `G₁` ending at `ω ∈ ∂G₁ ∩ ∂G₂` and let `Γ_j = f_j⁻¹(Γ)` end at
`ζ_j ∈ 𝕋`. If the angular derivative `f₁'(ζ₁) ≠ ∞` exists, then `f₂'(ζ₂) ≠ ∞` exists and
`|f₂'(ζ₂)| = c |f₁'(ζ₁)|` with `0 ≤ c < ∞`.
Modelling: `G_j ⊆ ℂ`; `Γ = w((0, 1])` for a continuous injective `w` with `w(t) → ω` as `t → 0+`; the preimages end at
`ζ_j`: `f_j⁻¹(w(t)) → ζ_j` as `t → 0+`. -/
theorem thm4_14 {f₁ f₂ : ℂ → ℂ} {G₁ G₂ : Set ℂ} (hf₁ : IsConformalOnto f₁ unitDisc G₁)
    (hf₂ : IsConformalOnto f₂ unitDisc G₂) (hG : G₁ ⊆ G₂) {w : ℝ → ℂ} (hwc : ContinuousOn w (Ioc 0 1))
    (hwi : InjOn w (Ioc 0 1)) (hwG : MapsTo w (Ioc 0 1) G₁) {ω : ℂ} (hω : ω ∈ frontier G₁ ∩ frontier G₂)
    (hwω : Tendsto w (𝓝[>] 0) (𝓝 ω)) {ζ₁ ζ₂ : ℂ} (hζ₁ : ζ₁ ∈ sphere (0 : ℂ) 1) (hζ₂ : ζ₂ ∈ sphere (0 : ℂ) 1)
    (hΓ₁ : Tendsto (Function.invFunOn f₁ unitDisc ∘ w) (𝓝[>] 0) (𝓝 ζ₁))
    (hΓ₂ : Tendsto (Function.invFunOn f₂ unitDisc ∘ w) (𝓝[>] 0) (𝓝 ζ₂)) {a₁ : ℂ}
    (ha₁ : HasAngularDerivative f₁ ζ₁ a₁) :
    ∃ a₂ : ℂ, HasAngularDerivative f₂ ζ₂ a₂ ∧ ∃ c : ℝ, 0 ≤ c ∧ ‖a₂‖ = c * ‖a₁‖ := by
  sorry

end Pommerenke1992
