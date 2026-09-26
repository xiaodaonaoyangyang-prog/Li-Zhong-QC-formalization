import Mathlib

/-!
# Common definitions

Basic objects used throughout the statement-level formalization of

  李忠《拟共形映射及其在黎曼曲面论中的应用》
  (Li Zhong, *Quasiconformal mappings and Teichmüller spaces*).

* the extended plane `ℂ̄ = OnePoint ℂ`, Jordan curves and Jordan domains;
* conformal maps between plane domains and their homeomorphic boundary extensions;
* the standard domains: half-planes, the unit disc, rectangles, annuli;
* fractional linear (Möbius) transformations;
* the formal (Wirtinger) derivatives, the complex dilatation, the dilatation
  quotient and the Jacobian (§6.1–6.2 of the book);
* separation of two sets by a plane domain.

## Conventions of the whole project

* Every definition is genuine (no `sorry`); every theorem of the book is stated
  with a `sorry` proof.
* Plane domains are subsets of `ℂ`; points at infinity (vertices of quadrilaterals,
  boundary points of half-planes, …) live in `ℂ̄ = OnePoint ℂ`.  In particular a
  "Jordan domain" never contains `∞` in its interior, although `∞` may lie on its
  boundary (as for the upper half-plane).
* The symbol `∞` of `ℝ≥0∞` is written `⊤`, and the point at infinity of `ℂ̄` is
  `extInf`, to avoid the notational clash between the two.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ## The extended plane -/

/-- The extended complex plane `ℂ̄ = ℂ ∪ {∞}`. -/
abbrev ExtPlane := OnePoint ℂ

/-- The point at infinity of `ℂ̄`. -/
abbrev extInf : ExtPlane := OnePoint.infty

/-- The image in `ℂ̄` of a subset of `ℂ`. -/
def toExt (s : Set ℂ) : Set ExtPlane := ((↑) : ℂ → ExtPlane) '' s

/-- A Jordan curve in `ℂ̄`: a homeomorphic image of the unit circle. -/
def IsJordanCurve (C : Set ExtPlane) : Prop :=
  ∃ γ : Circle → ExtPlane, Continuous γ ∧ Function.Injective γ ∧ range γ = C

/-- A Jordan domain: a connected open subset of `ℂ` whose boundary in `ℂ̄` is a
Jordan curve.  (Half-planes are Jordan domains in this sense; `∞` is a boundary point.) -/
def IsJordanDomain (D : Set ℂ) : Prop :=
  IsOpen D ∧ IsConnected D ∧ IsJordanCurve (frontier (toExt D))

/-! ## Standard domains -/

/-- The upper half-plane `ℍ = {z : Im z > 0}`. -/
def upperHalf : Set ℂ := {z | 0 < z.im}

/-- The lower half-plane `𝕃 = {z : Im z < 0}`. -/
def lowerHalf : Set ℂ := {z | z.im < 0}

/-- The unit disc `Δ = {|z| < 1}`. -/
def unitDisc : Set ℂ := ball 0 1

/-- The exterior of the unit disc `Δ* = {|z| > 1}` (as a subset of `ℂ`). -/
def unitDiscExterior : Set ℂ := {z | 1 < ‖z‖}

/-- The open rectangle `R = {x + iy : 0 < x < a, 0 < y < b}`. -/
def rectangle (a b : ℝ) : Set ℂ := {z | 0 < z.re ∧ z.re < a ∧ 0 < z.im ∧ z.im < b}

/-- The annulus `{r₁ < |z| < r₂}` (for `r₁ = 0` a punctured disc). -/
def annulus (r₁ r₂ : ℝ) : Set ℂ := {z | r₁ < ‖z‖ ∧ ‖z‖ < r₂}

/-- The annulus `{r₁ < |z - a| < r₂}` centred at `a`. -/
def annulusAt (a : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {z | r₁ < ‖z - a‖ ∧ ‖z - a‖ < r₂}

/-- The punctured plane `ℂ ∖ {0}`. -/
def puncturedPlane : Set ℂ := {0}ᶜ

/-- The punctured unit disc `{0 < |z| < 1}`. -/
def puncturedDisc : Set ℂ := annulus 0 1

/-! ## Conformal maps -/

/-- `f` maps the domain `U` conformally onto `V`: `f` is holomorphic and injective on `U`
and `f '' U = V`.  (An injective holomorphic map has non-vanishing derivative.) -/
def IsConformalOnto (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U ∧ f '' U = V

/-- Two plane domains are conformally equivalent. -/
def ConformallyEquivalent (U V : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsConformalOnto f U V

/-- `F : ℂ̄ → ℂ̄` extends `f : U → V` to a homeomorphism of the closure of `U` in `ℂ̄`
onto the closure of `V` in `ℂ̄`. -/
def IsHomeoExtension (f : ℂ → ℂ) (U V : Set ℂ) (F : ExtPlane → ExtPlane) : Prop :=
  (∀ z ∈ U, F (z : ExtPlane) = ((f z : ℂ) : ExtPlane)) ∧
    ContinuousOn F (closure (toExt U)) ∧ InjOn F (closure (toExt U)) ∧
    F '' closure (toExt U) = closure (toExt V)

/-- `f` is a homeomorphism of the open set `U` onto the open set `V`. -/
def IsHomeomorphOnto (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  ContinuousOn f U ∧ InjOn f U ∧ f '' U = V ∧ ContinuousOn (Function.invFunOn f U) V

/-! ## Fractional linear transformations -/

/-- The fractional linear transformation `z ↦ (a z + b)/(c z + d)` acting on `ℂ̄`. -/
def mobiusExt (a b c d : ℂ) (w : ExtPlane) : ExtPlane :=
  OnePoint.elim w (if c = 0 then extInf else (((a / c : ℂ)) : ExtPlane))
    (fun z => if c * z + d = 0 then extInf else (((a * z + b) / (c * z + d) : ℂ) : ExtPlane))

/-- `F : ℂ̄ → ℂ̄` is a fractional linear transformation. -/
def IsMobius (F : ExtPlane → ExtPlane) : Prop :=
  ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ F = mobiusExt a b c d

/-- `f : ℂ → ℂ` agrees, off its pole, with a fractional linear transformation. -/
def IsMobiusOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ U, c * z + d ≠ 0 → f z = (a * z + b) / (c * z + d)

/-- A similarity `z ↦ a z + b` (`a ≠ 0`). -/
def IsSimilarity (f : ℂ → ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b

/-- A Euclidean rigid motion (orientation preserving) `z ↦ e^{iθ} z + b`. -/
def IsRigidMotion (f : ℂ → ℂ) : Prop :=
  ∃ (θ : ℝ) (b : ℂ), ∀ z, f z = exp (θ * I) * z + b

/-! ## Formal derivatives (§6.1, §6.2) -/

/-- The formal derivative `∂_z f = (f'_x - i f'_y)/2`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2

/-- The formal derivative `∂_{z̄} f = (f'_x + i f'_y)/2`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

/-- The complex characteristic (complex dilatation) `μ_f = ∂_{z̄} f / ∂_z f` (6.6). -/
def complexDilatation (f : ℂ → ℂ) (z : ℂ) : ℂ := dzbar f z / dz f z

/-- The dilatation quotient `D_f = (1 + |μ_f|)/(1 - |μ_f|)` (6.7). -/
def dilatationQuotient (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (1 + ‖complexDilatation f z‖) / (1 - ‖complexDilatation f z‖)

/-- The Jacobian `J_f = |∂_z f|² - |∂_{z̄} f|²`. -/
def jacobian (f : ℂ → ℂ) (z : ℂ) : ℝ := ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2

/-- The classical partial derivative `f'_x(z)` (derivative along the horizontal line). -/
def partialX (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv (fun t : ℝ => f (z + t)) 0

/-- The classical partial derivative `f'_y(z)` (derivative along the vertical line). -/
def partialY (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv (fun t : ℝ => f (z + t * I)) 0

/-! ## Separation -/

/-- The plane domain `B` separates `E₁` from `E₂`: the two sets lie in two different
connected components of `ℂ̄ ∖ B`. -/
def SeparatesSets (B : Set ℂ) (E₁ E₂ : Set ExtPlane) : Prop :=
  ∃ x₁ ∈ (toExt B)ᶜ, ∃ x₂ ∈ (toExt B)ᶜ,
    E₁ ⊆ connectedComponentIn (toExt B)ᶜ x₁ ∧ E₂ ⊆ connectedComponentIn (toExt B)ᶜ x₂ ∧
    connectedComponentIn (toExt B)ᶜ x₁ ≠ connectedComponentIn (toExt B)ᶜ x₂

/-- The set `A ⊆ ℂ` is `n`-connected: a connected open set whose complement in `ℂ̄`
has exactly `n` connected components (§2.1). -/
def IsNConnected (A : Set ℂ) (n : ℕ) : Prop :=
  IsOpen A ∧ IsConnected A ∧ Nat.card (ConnectedComponents ↥((toExt A)ᶜ)) = n

/-- A doubly connected domain (§2.1). -/
def IsDoublyConnected (B : Set ℂ) : Prop := IsNConnected B 2

end LiZhongQC
