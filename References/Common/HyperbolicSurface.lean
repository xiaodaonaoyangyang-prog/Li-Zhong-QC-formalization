import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import References.Common.RiemannSphere
import References.Common.HypConvex
import References.Lehto1987.Ch04.S04_GroupsOfMobiusTransformations
import References.GardinerLakic2000.Ch11.S01_AdmissibleSystems

/-!
# Shared layer: hyperbolic geometry of Riemann surfaces

Notions on a hyperbolic Riemann surface `X = ℍ/Γ` that are used by Hubbard 2006 (Ch. 3, 7) and by the Teichmüller
books of the program (Imayoshi–Taniguchi Ch. 3, 7, 8, Nag): hyperbolic distance and length, closed geodesics,
multicurves, geodesic-boundary surfaces and trousers, annuli and moduli, non-elementary groups (DESIGN §2, shared
layer; registry `refs_lean\FOUNDATIONS.md`). Everything is a genuine definition; no `sorry`. The notions are purely
geometric: Fenchel–Nielsen lengths and twists are in `Common/FenchelNielsen.lean`.

**Convention (relative to a uniformization).** A hyperbolic Riemann surface is given together with a uniformization
`p : ℍ → X` by a torsion-free Fuchsian group `Γ ⊆ SL(2, ℝ)` (`LiZhongQC.IsFuchsian`, `ActsFreely`,
`IsUniformization`, the project's idiom). All geometry is read off `ℍ` with its hyperbolic metric of curvature `−1`
(`ρ_ℍ = |dz| / Im z`, Mathlib's `dist` on `UpperHalfPlane`, the same normalization as `LiZhongQC.hypLength`;
`ρ_𝔻 = 2 / (1 − |z|²)`; Lehto's metric `|dz| / (2 Im z)` is half of it). Independence of the notions below from `p`
is a statement of Hubbard Prop. 3.3.1, not assumed here. Every statement about these notions carries
`IsUniformization Γ p` (so `p` is onto and `p⁻¹(x)` is a `Γ`-orbit); a definition that is junk when `p` misses a
point says so in its docstring.

**Closed geodesics are algebraic.** The closed geodesic of a hyperbolic `g ∈ Γ` is `p '' axisH g`, where
`axisH g` is the set of points of `ℍ` that `g` moves by exactly its translation length (the axis, the geodesic
joining the fixed points of `g`).

**Geodesic boundary.** A hyperbolic surface with geodesic boundary is a pair `(Γ, C)`: a torsion-free Fuchsian group
and a closed convex `Γ`-invariant region `C ⊆ ℍ` with non-empty interior whose frontier is a union of complete
geodesic lines. The surface is `C/Γ`; completeness is automatic, `C` being closed.

**Near misses and reuse (dupcheck, 2026-10-09).**
(a) Reused, not restated: a simple loop (injective on `[0, 1)`) and a null-homotopic loop are
  `GardinerLakic2000.IsSimpleLoop` and `GardinerLakic2000.IsTrivialLoop` (Ch. 11 §1); `IsNonElementary` is
  `Lehto1987.IsElementary` negated, through the complexification of `Γ`.
(b) Different notions: `Lehto1987.hypDistRS` is the infimum over curves of `hypLengthRS`, in Lehto's metric
  `|dz| / (2 Im z)`, which is **half** of the metric here, so `hypDistSurf = 2 · hypDistRS` (the constants of Hubbard
  Prop. 3.3.7 and Thm 3.8.3 depend on the normalization); `GardinerLakic2000.annulusModulusRS` is a `sSup`-valued
  function on subsets of a surface with the same normalization as `HasModulus` (`(log r) / 2π`) but relative to a
  parametrization `IsAnnulusMap` and with choice junk; `LiZhongQC.dcModulus` is `ln (r₂ / r₁) = 2π M`;
  `GardinerLakic2000.IsEssentialLoop` also excludes loops around punctures (Hubbard's multicurves may contain
  them, see the proof of Thm 3.6.2) and `GardinerLakic2000.IsMulticurve` is a finite family of loops whose members may
  be homotopic; `Pommerenke1992.IsClosedHalfplane` is a Euclidean half-plane of `ℂ`; `LiZhongQC.limitSet`
  (base-point-free, for `SL(2, ℂ)`), `Katok1992.limitSet`, `Katok1992.axis` (a different group type,
  `PSL(2, ℝ)`), `Lehto1987.IsKleinian` (non-empty ordinary set, not discreteness), `LiZhongQC.IsFundamentalDomainH`
  and `LiZhongQC.TopQuad.modulus` (quadrilaterals) are unrelated or different.


* Shared notion (hyperbolic distance on `X = ℍ/Γ` through a uniformization) — `hypDistSurf`
* Shared notion (hyperbolic length of a path, from `hypDistSurf` by partitions) — `hypPathLength`
* Shared notion (hyperbolic norm of a tangent vector, `‖(Dp)⁻¹ ξ‖ / Im z`) — `hypNormSurf`
* Shared notion (axis of a hyperbolic element) — `axisH`
* Shared notion (simple closed geodesic of `X = ℍ/Γ`) — `IsSimpleClosedGeodesicOf`
* Simple loop and null-homotopic loop — exists: `GardinerLakic2000.IsSimpleLoop`, `GardinerLakic2000.IsTrivialLoop`
  (the same definitions; Ch. 11 §1 of Gardiner–Lakic)
* Shared notion (essential simple closed curve, not homotopic to a point) — `IsEssentialSimpleClosedCurve`
* Shared notion (multicurve, Hubbard 3.6.1; maximal multicurve; geodesic multicurve) — `IsMulticurve`,
  `IsMaximalMulticurve`, `IsGeodesicMulticurve`
* Shared notion (geodesic line of `ℍ`; hyperbolic convexity; convex core of a Fuchsian group, Hubbard 3.4.2;
  closed half-plane of `ℍ`) — `IsGeodesicLine`, `convexCore`, `IsClosedHalfPlaneH` (`HypConvex` is in `Common/HypConvex.lean`)
* Shared notion (hyperbolic surface with geodesic boundary, as a pair `(Γ, C)`; its interior quotient) —
  `HypSurfBdry`, `HypSurfBdry.interiorQuot`
* Shared notion (the side of an axis; boundary length; trouser, Hubbard 3.5.1; trouser with its boundary
  classes and lengths, Hubbard 3.5.8) — `leftForm`, `IsBoundaryLength`, `IsTrouserCore`,
  `IsTrouserCoreWithLengths`
* Shared notion (round annulus `{1 < |z| < e^{2πM}}`, Hubbard 3.2.1; `M` is the modulus of an annulus) —
  `roundAnnulus`, `HasModulus`
* Shared notion (non-elementary subgroup of `SL(2, ℝ)`, Hubbard 3.1.2(4)) — `IsNonElementary`
-/

open Set Metric Topology
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace References

open LiZhongQC

/-! ## Distance, length and norm on `X = ℍ/Γ` -/

section Metric

variable {X : Type*}

/-- **Hyperbolic distance on `X = ℍ/Γ`** (Hubbard Prop. 3.3.1, `d_X`), through a uniformization `p : ℍ → X`: the
infimum of the hyperbolic distances of lifts, `d_X(x, y) = inf { d_ℍ(z, w) | p z = x, p w = y }`. It is an infimum
over a subtype (no `∈`-binder junk), over a set of non-negative reals. *Junk:* the value is `0` exactly when the
subtype is empty, i.e. when `p` misses `x` or `y`; every statement carries `IsUniformization Γ p` (so `p` is onto)
and uses points `x y : X`. -/
def hypDistSurf (p : UpperHalfPlane → X) (x y : X) : ℝ :=
  ⨅ q : {q : UpperHalfPlane × UpperHalfPlane // p q.1 = x ∧ p q.2 = y}, dist q.1.1 q.1.2

/-- **Hyperbolic length of a path on `X`** (Hubbard Prop. 3.3.1, the length of a curve), by partitions: the
supremum, over monotone partitions `t₀ ≤ ⋯ ≤ t_n` of `[0, 1]`, of the sums `∑ d_X(γ(tᵢ), γ(tᵢ₊₁))` with `d_X` =
`hypDistSurf p`. This is the length in the metric space `(X, d_X)` and needs no derivative of `γ`; it is `⊤` for a
non-rectifiable path. The empty partition (`n = 0`) gives the sum `0`, so the supremum is never over an empty
family. -/
def hypPathLength [TopologicalSpace X] (p : UpperHalfPlane → X) {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : Fin (n + 1) → unitInterval) (_ : Monotone t),
    ∑ i : Fin n, ENNReal.ofReal (hypDistSurf p (γ (t i.castSucc)) (γ (t i.succ)))

/-- **Hyperbolic norm of a tangent vector on `X`** (Hubbard Prop. 3.3.1, `ρ_X(ξ) = ρ_ℍ([Dp(z)]⁻¹ ξ)`): for
`z ∈ ℍ` and `ξ ∈ T_{p z} X` (the tangent space in the preferred chart is `ℂ`), the norm of the preimage under
`Dp(z)`, divided by `Im z`. *Junk:* if `Dp(z)` is not invertible the continuous-linear inverse is `0` and the
value is `0`; for a uniformization (a local biholomorphism) `Dp(z)` is invertible at every `z`. -/
def hypNormSurf [TopologicalSpace X] [ChartedSpace ℂ X] (p : UpperHalfPlane → X) (z : UpperHalfPlane)
    (ξ : TangentSpace 𝓘(ℂ) (p z)) : ℝ :=
  ‖(show ℂ from (mfderiv 𝓘(ℂ) 𝓘(ℂ) p z).inverse ξ)‖ / z.im

end Metric

/-! ## Axes and closed geodesics -/

/-- **The axis of an element of `SL(2, ℝ)`**: the set of `z ∈ ℍ` moved by exactly the translation length,
`{z | d_ℍ(z, g z) = ℓ(g)}`. For a hyperbolic `g` this is the geodesic line of `ℍ` joining the two fixed points of
`g` (the minimum of the displacement function). *Junk:* for `g` not hyperbolic the set is not an axis (for parabolic
`g`, `ℓ(g) = 0` and it is the empty set; for elliptic `g` it is empty or the fixed point set); every use assumes
`IsHyperbolic g`. -/
def axisH (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set UpperHalfPlane :=
  {z | dist z (g • z) = translationLength g}

/-- **Simple closed geodesic of `X = ℍ/Γ`** (Hubbard 3.3.7–3.3.9, 3.8): `C ⊆ X` is the image under `p` of the axis
of a hyperbolic `g ∈ Γ`, and the closed geodesic is simple: two points of the axis with the same image differ by a
power of `g`. Simplicity forces `g` to be primitive modulo `±1` (for `g = h²` the points `z` and `h z` of the axis
have the same image and differ by no power of `g`). The conclusion `w = g ^ n • z` is the action, so `g` and `-g`
define the same closed geodesic. -/
def IsSimpleClosedGeodesicOf {X : Type*} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → X) (C : Set X) : Prop :=
  ∃ g ∈ Γ, IsHyperbolic g ∧ C = p '' axisH g ∧
    ∀ z ∈ axisH g, ∀ w ∈ axisH g, p z = p w → ∃ n : ℤ, w = g ^ n • z

/-! ## Simple closed curves and multicurves -/

section Curves

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Essential simple closed curve**: a subset `C ⊆ X` that is the range of a simple loop
(`GardinerLakic2000.IsSimpleLoop`: injective on `[0, 1)`) which is not homotopic to a point
(`¬ GardinerLakic2000.IsTrivialLoop`). Two simple loops with the same range differ by orientation and
parametrization, so the condition does not depend on the loop chosen. Loops around a puncture are admitted. -/
def IsEssentialSimpleClosedCurve (C : Set X) : Prop :=
  ∃ α : Loop X, GardinerLakic2000.IsSimpleLoop α ∧ Set.range (α.2 : unitInterval → X) = C ∧
    ¬ GardinerLakic2000.IsTrivialLoop α

/-- **Multicurve** (Hubbard Def. 3.6.1): a family `Y` of simple closed curves on a surface that are pairwise
disjoint, none homotopic to a point, and no two homotopic to each other (as unoriented curves: neither
orientation of the second is freely homotopic to the first). -/
def IsMulticurve (Y : Set (Set X)) : Prop :=
  (∀ C ∈ Y, IsEssentialSimpleClosedCurve C) ∧ Y.Pairwise Disjoint ∧
    ∀ C ∈ Y, ∀ D ∈ Y, C ≠ D → ∀ α β : Loop X, GardinerLakic2000.IsSimpleLoop α → GardinerLakic2000.IsSimpleLoop β →
      Set.range (α.2 : unitInterval → X) = C → Set.range (β.2 : unitInterval → X) = D →
        ¬ FreelyHomotopic α β ∧ ¬ FreelyHomotopic α ⟨β.1, β.2.symm⟩

/-- **Maximal multicurve**: a multicurve that is maximal for inclusion among multicurves (no multicurve strictly
contains it). -/
def IsMaximalMulticurve (Y : Set (Set X)) : Prop :=
  IsMulticurve Y ∧ ∀ Y' : Set (Set X), IsMulticurve Y' → Y ⊆ Y' → Y' = Y

/-- **Geodesic multicurve** on `X = ℍ/Γ` (Hubbard Def. 3.6.1, second sentence): a multicurve all of whose
elements are simple closed geodesics. -/
def IsGeodesicMulticurve {Y₀ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → Y₀) (Y : Set (Set Y₀)) : Prop :=
  IsMulticurve Y ∧ ∀ C ∈ Y, IsSimpleClosedGeodesicOf Γ p C

end Curves

/-! ## Convexity and geodesic boundary in `ℍ` -/

/-- A **complete geodesic line of `ℍ`**: the image of an isometric embedding `ℝ → ℍ` (for the hyperbolic metric of
`ℍ`, `ℍ` being uniquely geodesic). -/
def IsGeodesicLine (l : Set UpperHalfPlane) : Prop :=
  ∃ f : ℝ → UpperHalfPlane, Isometry f ∧ Set.range f = l

/-- **Convex core of a Fuchsian group** (Hubbard 3.4.2: the hyperbolic convex hull of the limit set, intersected
with the disc): the smallest non-empty closed hyperbolically convex `Γ`-invariant subset of `ℍ`, defined as the
intersection of all such subsets. For a torsion-free `Γ` this is the convex hull of the limit set (it is empty for a
parabolic cyclic group, the axis for a hyperbolic cyclic group, and the hull of the limit set for a non-elementary
group). For the trivial group every point of `ℍ` is a non-empty closed convex invariant set, so the intersection of all
of them is `∅` (equal to `Hull(∅)`); the same empty value arises whenever two disjoint such sets exist. No statement of
the program uses `convexCore` of the trivial group. *Caveat:* it agrees with the book's `Hull(Λ_Γ) ∩ 𝔻` exactly for torsion-free `Γ` (every statement in the
program carries `ActsFreely Γ`); with elliptic elements the smallest closed convex `Γ`-invariant set can be a
point (finite `Γ`), so the book's convention is not claimed for groups with torsion. -/
def convexCore (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set UpperHalfPlane :=
  ⋂₀ {C : Set UpperHalfPlane | C.Nonempty ∧ IsClosed C ∧ HypConvex C ∧ ∀ γ ∈ Γ, ∀ z ∈ C, γ • z ∈ C}

/-- A **closed half-plane of `ℍ`**: a closed hyperbolically convex set with non-empty interior whose frontier is a
single complete geodesic line (one of the two closed sides of that line). -/
def IsClosedHalfPlaneH (C : Set UpperHalfPlane) : Prop :=
  IsClosed C ∧ HypConvex C ∧ (interior C).Nonempty ∧ ∃ l, IsGeodesicLine l ∧ frontier C = l

/-- **A hyperbolic surface with geodesic boundary, as a pair `(Γ, C)`** (Hubbard §3.5): a torsion-free Fuchsian
group `Γ ⊆ SL(2, ℝ)` and a closed hyperbolically convex `Γ`-invariant set `C ⊆ ℍ` with non-empty interior whose
frontier is a union of complete geodesic lines. The surface is `C/Γ` (quotient by the action of `Γ` on `C`); it is
complete because `C` is closed; the boundary points have neighbourhoods isometric to neighbourhoods of a boundary
point of a closed half-plane because `C` is convex with geodesic frontier. -/
structure HypSurfBdry where
  /-- the covering group -/
  Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)
  /-- the region of `ℍ` covering the surface -/
  C : Set UpperHalfPlane
  isFuchsian : IsFuchsian Γ
  actsFreely : ActsFreely Γ
  isClosed : IsClosed C
  convex : HypConvex C
  invariant : ∀ γ ∈ Γ, ∀ z ∈ C, γ • z ∈ C
  interior_nonempty : (interior C).Nonempty
  frontier_lines : ∃ L : Set (Set UpperHalfPlane), (∀ l ∈ L, IsGeodesicLine l) ∧ frontier C = ⋃₀ L

/-- The **interior of the surface `C/Γ`**: the quotient of `interior C` by the action of `Γ`, with the quotient
topology. -/
abbrev HypSurfBdry.interiorQuot (S : HypSurfBdry) : Type :=
  Quot (fun z w : interior S.C => ∃ γ ∈ S.Γ, γ • (z : UpperHalfPlane) = (w : UpperHalfPlane))

/-- **The side form of an element of `SL(2, ℝ)`** (the left side of the axis). For `g = (a b; c d)` with
`tr g ≠ 0`, `leftForm g z = sign(a + d) · (c |z|² + (d − a) Re z − b)`. For hyperbolic `g` this vanishes exactly on
`axisH g`, is positive on the open half-plane **to the left of the direction in which `g` translates** along its
axis and negative on the right (checked on `g = diag(λ, 1/λ)`, whose axis `i ℝ₊` is traversed upwards for `λ > 1`
and has `Re z < 0` on its left, and conjugation-equivariant). The factor `sign(a + d)` makes it invariant under
`g ↦ -g` (which has the same axis and translation direction). *Junk:* `0` for `tr g = 0`; used for hyperbolic `g`
only. -/
def leftForm (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : UpperHalfPlane) : ℝ :=
  (SignType.sign (slTrace g) : ℝ) *
    (g 1 0 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) + (g 1 1 - g 0 0) * (z : ℂ).re - g 0 1)

/-- **`ℓ` is the boundary length of the element `g`**: `g` is hyperbolic with translation length `ℓ`, or `g` is
parabolic (a cusp) and `ℓ = 0` (Hubbard Remark after Thm 3.5.8: length `0` stands for a puncture). -/
def IsBoundaryLength (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ℓ : ℝ) : Prop :=
  (IsHyperbolic g ∧ ℓ = translationLength g) ∨ (IsParabolic g ∧ ℓ = 0)

/-- **Trouser core** (Hubbard Def. 3.5.1): a hyperbolic surface with geodesic boundary `C/Γ` that is the convex core
of `Γ` (so no funnels: every end is a geodesic boundary component or a cusp) and whose interior is homeomorphic to
the complement of three points of the sphere `ℙ¹`. Modelling: the book's "complete surface with geodesic boundary"
admits ends that are funnels, but its trousers (Fig. 3.5.1, Thm 3.5.8, "boundary components have drifted off to
infinity" for cusps) have only geodesic boundary components and cusps; funnels are excluded by `C = convexCore Γ`.
-/
def IsTrouserCore (S : HypSurfBdry) : Prop :=
  S.C = convexCore S.Γ ∧
    ∃ T : Set RiemannSphere, T.encard = 3 ∧ Nonempty (S.interiorQuot ≃ₜ ↥Tᶜ)

/-- **A trouser with its three boundary classes and lengths** (Hubbard Thm 3.5.8, in the form asked by Imayoshi–
Taniguchi §3.4–3.5): `S` is a trouser core, `A B C ∈ Γ` generate `Γ` with `A B C = ±1`, each is hyperbolic or
parabolic, `a b c ≥ 0` are their boundary lengths (`IsBoundaryLength`), and every hyperbolic one has its axis in the
frontier of `C` with the interior of `C` on its left (`0 < leftForm`); parabolic ones are the cusps. Thus `A, B, C`
are the boundary components (or cusps), each oriented with the surface on its left, in the cyclic order of the
relation `ABC = ±1`. *Modelling:* the sign `±1` is the lift ambiguity from `PSL(2, ℝ)` to `SL(2, ℝ)`. -/
def IsTrouserCoreWithLengths (S : HypSurfBdry) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b c : ℝ) : Prop :=
  IsTrouserCore S ∧ A ∈ S.Γ ∧ B ∈ S.Γ ∧ C ∈ S.Γ ∧ S.Γ = Subgroup.closure {A, B} ∧
    (A * B * C = 1 ∨ A * B * C = -1) ∧
    IsBoundaryLength A a ∧ IsBoundaryLength B b ∧ IsBoundaryLength C c ∧
    (∀ g ∈ ({A, B, C} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)), IsHyperbolic g →
      axisH g ⊆ frontier S.C ∧ ∀ z ∈ interior S.C, 0 < leftForm g z)

/-! ## Annuli and moduli -/

/-- **The round annulus `A_M = {1 < |z| < e^{2πM}}`** (Hubbard 3.2.1), as an open subset of `ℂ`
(a Riemann surface). It reuses `LiZhongQC.annulus` and `isOpen_annulus`. -/
def roundAnnulus (M : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨annulus 1 (Real.exp (2 * Real.pi * M)), isOpen_annulus _ _⟩

/-- **`M` is the modulus of the annulus `A`** (Hubbard 3.2.1, `M = Mod A`): `0 < M` and `A` is conformally
equivalent to `A_M = {1 < |z| < e^{2πM}}`. A predicate rather than a function (no choice junk); the uniqueness of
`M` is a statement of Hubbard Prop. 3.2.1. *Normalization:* `M = LiZhongQC.dcModulus A / (2π)` (LZ's modulus of a
doubly connected domain is `ln (r₂ / r₁) = 2πM`), so the LZ notion is a different normalization and Hubbard's
statements (`ℓ = π / M` for the closed geodesic of an annulus of modulus `M`) are written with this one. Annuli of
infinite modulus (`ℂ∖{0}`, `𝔻*`) have no `M`. -/
def HasModulus (A : Type*) [TopologicalSpace A] [ChartedSpace ℂ A] (M : ℝ) : Prop :=
  0 < M ∧ RSConformallyEquivalent A (roundAnnulus M)

/-! ## Non-elementary groups -/

/-- **Non-elementary subgroup of `SL(2, ℝ)`** (Hubbard 3.1.2(4): not finite, not consisting of elliptic and
parabolic elements, with no hyperbolic element generating a subgroup of finite index): the negation of
`Lehto1987.IsElementary` (limit set with at most two points) applied to the image of `Γ` in `SL(2, ℂ)`. For
Fuchsian groups the two descriptions agree (Hubbard Prop. 3.1.2 and Lehto Ch. IV §4.3); the near miss
`Katok1992.IsElementary` (some orbit in `ℍ̃` finite) is a definition for `PSL(2, ℝ)`. -/
def IsNonElementary (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ¬ Lehto1987.IsElementary (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))

end References
