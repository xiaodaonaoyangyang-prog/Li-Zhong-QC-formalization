import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch01.S08_FirstClassification

/-!
# Hubbard 2006, Chapter 3 §3.3: The hyperbolic metric on a hyperbolic Riemann surface

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2198–2355.

**Conventions.** A hyperbolic surface `X` is given with a uniformization `p : ℍ → X` by a torsion-free Fuchsian group
`Γ`
(`IsFuchsian Γ`, `ActsFreely Γ`, `IsUniformization Γ p`; `ℍ ≅ 𝔻`, see `Ch01/S08`). The metric, distance and length
are `References.hypNormSurf`, `hypDistSurf` and `hypPathLength` of `Common/HyperbolicSurface.lean` (curvature `−1`,
`ρ_ℍ = |dz| / Im z`). A tangent vector `ξ ∈ T_x X` is a complex number in the preferred chart
(`TangentSpace 𝓘(ℂ) x = ℂ`).
Closed geodesics are the algebraic ones of the shared file (`IsSimpleClosedGeodesicOf`).

* Proposition and Definition 3.3.1 (independence of the hyperbolic norm of the lift and of the uniformization) —
  `prop3_3_1_a`
* Proposition and Definition 3.3.1 (independence of the hyperbolic distance of the uniformization) — `prop3_3_1_b`
* Proposition and Definition 3.3.1 (`d_X` is the infimum of the lengths of curves) — `prop3_3_1_c`
* Example 3.3.2 (the hyperbolic metric of `𝔻*`) — `ex3_3_2`
* Proposition 3.3.3 (naturality: coverings are local isometries) — `prop3_3_3`
* Proposition 3.3.4 (a) (holomorphic maps do not expand the hyperbolic metric) — `prop3_3_4_a`
* Proposition 3.3.4 (b) (an infinitesimal isometry at one point is a covering) — `prop3_3_4_b`
* Example 3.3.5 (a) (`ρ_U ≤ 2/δ`) — `ex3_3_5_a`
* Example 3.3.5 (b) (`ρ_U ≥ 1/(2δ)` for simply connected `U`) — `ex3_3_5_b`
* Exercise 3.3.6 — omitted: exercise
* Proposition 3.3.7 (modulus and length of the closed geodesic of a cylinder) — `prop3_3_7`
* Definition (primitive closed curve, H1:2300) — `IsPrimitiveLoop`, `IsGeodesicLoop`
* Proposition 3.3.8 (uniqueness of geodesics) — `prop3_3_8`
* Proposition 3.3.9 (1) (a geodesic homotopic to a simple closed curve is simple) — `prop3_3_9_a`
* Proposition 3.3.9 (3) (a simple closed geodesic has a neighbourhood missing every disjoint simple closed geodesic) —
  `prop3_3_9_c`
* Proposition 3.3.9 (2) (geodesics realize the minimal number of transverse intersections) — deferred: needs
  transversality and an intersection count on a surface (no `C¹` curve theory on Riemann surfaces in the project)
* Definition 3.3.10 (minimal position) — deferred: same reason as Prop. 3.3.9 (2)
-/

open Set
open scoped Manifold ContDiff Topology ENNReal Real References
open LiZhongQC References

namespace Hubbard2006

/-- The punctured unit disc `𝔻* = {0 < |z| < 1}` as an open subset of `ℂ` (a Riemann surface). Helper for `ex3_3_2` and
the later files of Chapter 3. -/
def punctDiscOpens : TopologicalSpace.Opens ℂ := ⟨puncturedDisc, isOpen_annulus _ _⟩

/-- **Primitive closed curve** (Ch. 3 §3.3, H1:2300). A loop `α` is primitive if it is not freely homotopic to a proper
power `β^n`, `n ≥ 2`, of any loop `β` (the power is the concatenation `LiZhongQC.loopNatPow`). -/
def IsPrimitiveLoop {X : Type*} [TopologicalSpace X] (α : Loop X) : Prop :=
  ∀ (β : Loop X) (n : ℕ), 2 ≤ n → ¬ FreelyHomotopic α ⟨β.1, loopNatPow β n⟩

/-- **Geodesic loop** on `X = ℍ/Γ` (Ch. 3 §3.3): a loop that is not null-homotopic and is a shortest curve in its free
homotopy class (`poincareLengthLoop p β = freeHomotopyLength p β`). -/
def IsGeodesicLoop {X : Type*} [TopologicalSpace X] (p : UpperHalfPlane → X) (β : Loop X) : Prop :=
  poincareLengthLoop p β = freeHomotopyLength p β ∧ ¬ FreelyHomotopic β ⟨β.1, Path.refl β.1⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Proposition 3.3.1 (a)** (Ch. 3 §3.3, H1:2204). The hyperbolic norm `ρ_X(ξ) = ρ_ℍ([Dp(z)]⁻¹ ξ)` of a tangent vector
`ξ ∈ T_x X` does not depend on the point `z ∈ p⁻¹(x)` nor on the choice of the uniformization: for two uniformizations
`(Γ, p)`, `(Γ', p')` of `X` and `p z = p' z'`, `hypNormSurf p z ξ = hypNormSurf p' z' ξ`. -/
theorem prop3_3_1_a {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p p' : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hp' : IsUniformization Γ' p')
    (z z' : UpperHalfPlane) (h : p z = p' z') (ξ : ℂ) :
    hypNormSurf p z ξ = hypNormSurf p' z' ξ := by
  sorry

/-- **Proposition 3.3.1 (b)** (Ch. 3 §3.3, H1:2204). The hyperbolic distance `d_X(x, y)` does not depend on the choice
of
the uniformization. -/
theorem prop3_3_1_b {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p p' : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hp' : IsUniformization Γ' p') (x y : X) :
    hypDistSurf p x y = hypDistSurf p' x y := by
  sorry

/-- **Proposition 3.3.1 (c)** (Ch. 3 §3.3, H1:2204). `d_X(x, y)` is the infimum of the hyperbolic lengths of the curves
from
`x` to `y`. Modelling: the length is the length in the metric space `(X, d_X)` (`hypPathLength`), which equals the
integral of the hyperbolic norm along a piecewise smooth curve. -/
theorem prop3_3_1_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (x y : X) :
    ENNReal.ofReal (hypDistSurf p x y) = ⨅ γ : Path x y, hypPathLength p γ := by
  sorry

/-- **Example 3.3.2** (hyperbolic metric near a puncture, Ch. 3 §3.3, H1:2216). For `D* = 𝔻 ∖ {0}` and the universal
covering `π(z) = e^{iz} : ℍ → D*`, the hyperbolic metric of `D*` is `ρ_{D*}(w) = |dw| / (|w| |ln |w||)` (3.3.3).
Modelling:
`p` is any uniformization of `D*` with `p z = e^{iz}` (its group is generated by `z ↦ z + 2π`); the norm of the tangent
vector `ξ` at `w = e^{iz}` is `‖ξ‖ / (‖w‖ |ln ‖w‖|)`. -/
theorem ex3_3_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : UpperHalfPlane → punctDiscOpens)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hexp : ∀ z : UpperHalfPlane, ((p z : punctDiscOpens) : ℂ) = Complex.exp (Complex.I * z))
    (z : UpperHalfPlane) (ξ : ℂ) :
    hypNormSurf p z ξ =
      ‖ξ‖ / (‖Complex.exp (Complex.I * z)‖ * |Real.log ‖Complex.exp (Complex.I * z)‖|) := by
  sorry

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Proposition 3.3.3** (naturality of the hyperbolic metric, Ch. 3 §3.3, H1:2244). A holomorphic covering map
`f : X → Y` of hyperbolic Riemann surfaces is a local isometry: it preserves the hyperbolic norm of tangent vectors
(`η = Df(x) ξ` has the same norm as `ξ`). The uniqueness of the functor `X ↦ ρ_X` with this property is a categorical
reformulation of Prop. 3.3.1 and is not stated. -/
theorem prop3_3_3 {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    {q : UpperHalfPlane → Y} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hq : IsUniformization Γ' q)
    {f : X → Y} (hf : IsCoveringMap f) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (z w : UpperHalfPlane) (hzw : f (p z) = q w) (ξ η : ℂ) (hη : η = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (p z) ξ) :
    hypNormSurf q w η = hypNormSurf p z ξ := by
  sorry

/-- **Proposition 3.3.4 (a)** (contraction properties, Ch. 3 §3.3, H1:2250). A holomorphic map `f : X → Y` of hyperbolic
Riemann surfaces does not expand the hyperbolic metric: `‖Df ξ‖_Y ≤ ‖ξ‖_X`, and `d_Y(f x, f x') ≤ d_X(x, x')`. -/
theorem prop3_3_4_a {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    {q : UpperHalfPlane → Y} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hq : IsUniformization Γ' q)
    {f : X → Y} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    (∀ (z w : UpperHalfPlane), f (p z) = q w → ∀ ξ η : ℂ, η = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (p z) ξ →
      hypNormSurf q w η ≤ hypNormSurf p z ξ) ∧
    ∀ x x' : X, hypDistSurf q (f x) (f x') ≤ hypDistSurf p x x' := by
  sorry

/-- **Proposition 3.3.4 (b)** (Ch. 3 §3.3, H1:2250). If a holomorphic map `f : X → Y` of hyperbolic Riemann surfaces is
an
infinitesimal isometry at a single point (`‖Df ξ‖ = ‖ξ‖` for some `ξ ≠ 0` at some point), then `f` is a covering map. -/
theorem prop3_3_4_b {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    {q : UpperHalfPlane → Y} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hq : IsUniformization Γ' q)
    {f : X → Y} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hiso : ∃ (z w : UpperHalfPlane) (ξ η : ℂ), f (p z) = q w ∧ ξ ≠ 0 ∧
      η = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (p z) ξ ∧ hypNormSurf q w η = hypNormSurf p z ξ) :
    IsCoveringMap f := by
  sorry

/-- **Example 3.3.5 (a)** (Ch. 3 §3.3, H1:2266). Let `U ⊆ ℂ` be a domain whose complement has at least two points, `ρ_U`
its
hyperbolic metric and `δ(z) = dist(z, ℂ ∖ U)`. Then `ρ_U(z) ≤ 2 / δ(z)`. Modelling: `ρ_U(z)` is the norm of the tangent
vector `1` at `z`, `hypNormSurf p w 1` for a uniformization `p : ℍ → U` (so `U` is connected) and `p w = z`. -/
theorem ex3_3_5_a {U : TopologicalSpace.Opens ℂ} (hU : ∃ a b : ℂ, a ∉ U ∧ b ∉ U ∧ a ≠ b)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → U} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (w : UpperHalfPlane) :
    hypNormSurf p w (1 : ℂ) ≤ 2 / Metric.infDist ((p w : U) : ℂ) (Uᶜ : Set ℂ) := by
  sorry

/-- **Example 3.3.5 (b)** (Ch. 3 §3.3, H1:2266, formula (3.3.7)). If moreover `U` is simply connected, then
`ρ_U(z) ≥ 1 / (2 δ(z))` (the Koebe `1/4` bound). -/
theorem ex3_3_5_b {U : TopologicalSpace.Opens ℂ} (hU : ∃ a b : ℂ, a ∉ U ∧ b ∉ U ∧ a ≠ b)
    [SimplyConnectedSpace U] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → U}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (w : UpperHalfPlane) :
    1 / (2 * Metric.infDist ((p w : U) : ℂ) (Uᶜ : Set ℂ)) ≤ hypNormSurf p w (1 : ℂ) := by
  sorry

/-- **Proposition 3.3.7** (modulus and length of geodesics, Ch. 3 §3.3, H1:2296). A cylinder `X` (an annulus) of finite
modulus `M` (`HasModulus X M`: `X ≅ {1 < |z| < e^{2πM}}`) has a unique simple closed geodesic `C`, and its hyperbolic
length
is `π / M`: every hyperbolic `g ∈ Γ` with `C = p '' axisH g` and the simplicity property of `IsSimpleClosedGeodesicOf`
has
translation length `π / M`. -/
theorem prop3_3_7 {M : ℝ} (hM : HasModulus X M) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → X} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    (∃! C : Set X, IsSimpleClosedGeodesicOf Γ p C) ∧
      ∀ C : Set X, IsSimpleClosedGeodesicOf Γ p C → ∀ g ∈ Γ, IsHyperbolic g → C = p '' axisH g →
        (∀ z ∈ axisH g, ∀ w ∈ axisH g, p z = p w → ∃ n : ℤ, w = g ^ n • z) → translationLength g = π / M := by
  sorry

/-- **Proposition 3.3.8** (uniqueness of geodesics, Ch. 3 §3.3, H1:2302). Let `α` be a primitive closed curve on a
hyperbolic Riemann surface `X = ℍ/Γ` (`α` null-homotopic or primitive: `IsPrimitiveLoop` itself excludes null-homotopic
loops, which would make alternative (2) unreachable). Then (1) there is a unique geodesic freely homotopic to `α` (a geodesic loop
freely
homotopic to `α`, and any two such have the same image), or (2) `α` is null-homotopic, or (3) `α` is homotopic to a
simple
closed curve bounding a region isomorphic to `𝔻*` (a punctured-disc neighbourhood of a puncture,
`LiZhongQC.IsPunctureNbhd`, whose frontier is the curve). -/
theorem prop3_3_8 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (α : Loop X) (hα : FreelyHomotopic α ⟨α.1, Path.refl α.1⟩ ∨ IsPrimitiveLoop α) :
    (∃ γ : Loop X, IsGeodesicLoop p γ ∧ FreelyHomotopic α γ ∧
      ∀ γ' : Loop X, IsGeodesicLoop p γ' → FreelyHomotopic α γ' →
        range (γ'.2 : unitInterval → X) = range (γ.2 : unitInterval → X)) ∨
    FreelyHomotopic α ⟨α.1, Path.refl α.1⟩ ∨
    ∃ (β : Loop X) (U : Set X) (φ : X → ℂ), GardinerLakic2000.IsSimpleLoop β ∧ FreelyHomotopic α β ∧
      IsPunctureNbhd U φ ∧ frontier U = range (β.2 : unitInterval → X) := by
  sorry

/-- **Proposition 3.3.9 (1)** (geodesics and minimal position, Ch. 3 §3.3, H1:2326). A geodesic homotopic to a simple
closed
curve is simple: the image of a geodesic loop freely homotopic to a simple loop is a simple closed geodesic of
`X = ℍ/Γ`. -/
theorem prop3_3_9_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (γ β : Loop X)
    (hγ : IsGeodesicLoop p γ) (hβ : GardinerLakic2000.IsSimpleLoop β) (hh : FreelyHomotopic γ β) :
    IsSimpleClosedGeodesicOf Γ p (range (γ.2 : unitInterval → X)) := by
  sorry

/-- **Proposition 3.3.9 (3)** (Ch. 3 §3.3, H1:2326). Every simple closed geodesic `C` has a neighbourhood containing no
point
of any simple closed geodesic disjoint from `C`. -/
theorem prop3_3_9_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {C : Set X}
    (hC : IsSimpleClosedGeodesicOf Γ p C) :
    ∃ U : Set X, IsOpen U ∧ C ⊆ U ∧ ∀ D : Set X, IsSimpleClosedGeodesicOf Γ p D → Disjoint C D → Disjoint U D := by
  sorry

end Hubbard2006
