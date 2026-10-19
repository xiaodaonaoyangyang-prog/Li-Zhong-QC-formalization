import References.Hubbard2006.Ch03.S04_LimitSets
import References.Katok1992.Ch01.S05_HyperbolicTrigonometry

/-!
# Hubbard 2006, Chapter 3 §3.5: Trousers

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2410–2516.

**Conventions.** A hyperbolic surface with geodesic boundary is a pair `(Γ, C)`, `References.HypSurfBdry` (a
torsion-free
Fuchsian group and a closed convex `Γ`-invariant region of `ℍ` with non-empty interior and geodesic frontier); the
surface is
`C/Γ` (`fullQuot`). A trouser is `References.IsTrouserCore` (no funnels: every end is a geodesic boundary component
or a cusp), and with its three boundary classes and lengths `References.IsTrouserCoreWithLengths`. Two such surfaces are
**isometric** (`IsIsometricSurf`) iff an isometry of `ℍ` carries `C` onto `C'` and conjugates `Γ` onto `Γ'`: an
isometry of the quotients lifts to an isometry of the convex universal covers, and an isometry between convex sets with
non-empty interior extends to `ℍ`. The models of the remaining surfaces of Prop. 3.5.3 are `IsHalfAnnulusModel`,
`IsPuncturedDiscModel`, `IsDiscModel`.
A right-angled hexagon is a convex hexagon of `ℍ` with all six angles equal to `π/2` (`IsRightAngledHexagon`, through
`Katok1992.IsHypPolygon` and `Katok1992.polygonAngle`).

* Definition (hyperbolic surface with geodesic boundary, H1:2414) — exists: `References.HypSurfBdry`
* Definition 3.5.1 (trouser) — exists: `References.IsTrouserCore`
* Definition (isometry of surfaces with geodesic boundary; the quotient `C/Γ`) — `fullQuot`,
  `IsIsometricSurf`
* Definition (models for Prop. 3.5.3) — `IsHalfAnnulusModel`, `IsPuncturedDiscModel`, `IsDiscModel`
* Proposition 3.5.2 (a compact surface with geodesic boundary and no interior simple closed geodesic is a trouser) —
  `prop3_5_2`
* Proposition 3.5.3 (the noncompact surfaces with only trivial or peripheral simple curves) — `prop3_5_3`
* Definition (right-angled hexagon, §3.5, H1:2464) — `IsRightAngledHexagon`
* Proposition 3.5.4 (SSS for hyperbolic right-angled hexagons) — `prop3_5_4`
* Exercises 3.5.5, 3.5.6, 3.5.7 — omitted: exercises (3.5.7 is the hexagon formula, used only through Prop. 3.5.4)
* Theorem 3.5.8 (a trouser is determined by the lengths of its boundary components) — `thm3_5_8`
-/

open Set
open scoped Manifold ContDiff Topology Real
open LiZhongQC References

namespace Hubbard2006

/-- The **surface `C/Γ`** of a hyperbolic surface with geodesic boundary (including the boundary): the quotient of `C`
by
the action of `Γ`, with the quotient topology. -/
abbrev fullQuot (S : HypSurfBdry) : Type :=
  Quot (fun z w : S.C => ∃ γ ∈ S.Γ, γ • (z : UpperHalfPlane) = (w : UpperHalfPlane))

/-- **Isometry of surfaces with geodesic boundary** (Ch. 3 §3.5): `S ≅ S'` iff an isometry `f` of `ℍ` (possibly
orientation
reversing) maps `C` onto `C'` and conjugates `Γ` onto `Γ'` (`f γ f⁻¹ ∈ Γ'` and `f⁻¹ γ' f ∈ Γ`, as actions on `ℍ`). -/
def IsIsometricSurf (S S' : HypSurfBdry) : Prop :=
  ∃ f : UpperHalfPlane ≃ᵢ UpperHalfPlane, f '' S.C = S'.C ∧
    (∀ γ ∈ S.Γ, ∃ γ' ∈ S'.Γ, ∀ z, f (γ • z) = γ' • f z) ∧
    (∀ γ' ∈ S'.Γ, ∃ γ ∈ S.Γ, ∀ z, f (γ • z) = γ' • f z)

/-- **Half-annulus model** (Prop. 3.5.3 (2), Thm 3.6.2 (2)): `S = C/⟨g⟩` for a hyperbolic `g`, `C` one of the two closed
half-planes bounded by the axis of `g`. This is the half-annulus `{|z| ≥ 1}` of the annulus `{1/R < |z| < R}` with its
hyperbolic metric (a funnel bounded by the closed geodesic). -/
def IsHalfAnnulusModel (S : HypSurfBdry) : Prop :=
  ∃ g ∈ S.Γ, IsHyperbolic g ∧ (∀ h ∈ S.Γ, ∃ n : ℤ, h = g ^ n ∨ h = -g ^ n) ∧ IsClosedHalfPlaneH S.C ∧
    frontier S.C = axisH g

/-- **Punctured disc model** (Prop. 3.5.3 (3)): `S = ℍ/⟨g⟩` for a parabolic `g`, without boundary: the hyperbolic
punctured disc `𝔻*`. -/
def IsPuncturedDiscModel (S : HypSurfBdry) : Prop :=
  ∃ g ∈ S.Γ, IsParabolic g ∧ (∀ h ∈ S.Γ, ∃ n : ℤ, h = g ^ n ∨ h = -g ^ n) ∧ S.C = univ

/-- **Disc model** (Prop. 3.5.3 (4)): `S = ℍ`, the hyperbolic disc (trivial group, no boundary). -/
def IsDiscModel (S : HypSurfBdry) : Prop :=
  (∀ h ∈ S.Γ, h = 1 ∨ h = -1) ∧ S.C = univ

/-- A **simple loop** in a topological space (injective on `[0, 1)`); `GardinerLakic2000.IsSimpleLoop` needs a charted
space, which `C/Γ` is not at its boundary. -/
def IsSimpleLoopTop {R : Type*} [TopologicalSpace R] (α : Loop R) : Prop :=
  Set.InjOn (α.2 : unitInterval → R) {t | (t : ℝ) < 1}

/-- **Proposition 3.5.2** (Ch. 3 §3.5, H1:2420). A compact connected hyperbolic surface `X = C/Γ` with geodesic
boundary, all
of whose simple closed geodesics are boundary components, is homeomorphic to a trouser. Modelling: a simple closed
geodesic of `X` is the axis of a hyperbolic `g ∈ Γ`, lying in `C` and simple modulo `⟨g⟩` in `X` (two points of the axis
in
the same `Γ`-orbit differ by a power of `g`); it is a boundary component if the axis lies in the frontier of `C`. The
conclusion is that there is a trouser `S'` (`IsTrouserCore S'`) with `fullQuot S ≃ₜ fullQuot S'`. Connectedness is
automatic (`C` is convex). -/
theorem prop3_5_2 (S : HypSurfBdry) [CompactSpace (fullQuot S)]
    (h : ∀ g ∈ S.Γ, IsHyperbolic g → axisH g ⊆ S.C →
      (∀ z ∈ axisH g, ∀ w ∈ axisH g, (∃ γ ∈ S.Γ, γ • z = w) → ∃ n : ℤ, w = g ^ n • z) → axisH g ⊆ frontier S.C) :
    ∃ S' : HypSurfBdry, IsTrouserCore S' ∧ Nonempty (fullQuot S ≃ₜ fullQuot S') := by
  sorry

/-- **Proposition 3.5.3** (Ch. 3 §3.5, H1:2442). A noncompact complete hyperbolic surface `X = C/Γ` with compact
(perhaps
empty) geodesic boundary, all of whose simple closed curves are null-homotopic, bound a punctured disc, or are homotopic
to
a boundary component, is isometric to (1) a trouser with one to three cusps, (2) a half-annulus `{1 ≤ |z| < R}`, (3)
`𝔻*`,
or (4) `𝔻`. Modelling: curves are loops of the quotient `fullQuot S`; "bounds a punctured disc" is an open set `U` with
frontier the curve that is homeomorphic to the punctured disc `𝔻*`; "homotopic to a boundary component" is free
homotopy to a loop in the image of `frontier C`; a trouser with `1..3` cusps is a trouser with a boundary length equal
to `0` (`IsTrouserCoreWithLengths`). The model (1) is read through isometry. -/
theorem prop3_5_3 (S : HypSurfBdry) (hnc : ¬ CompactSpace (fullQuot S))
    (hbd : IsCompact ((fun z : S.C => (Quot.mk _ z : fullQuot S)) '' {z | (z : UpperHalfPlane) ∈ frontier S.C}))
    (hsimple : ∀ α : Loop (fullQuot S), IsSimpleLoopTop α →
      FreelyHomotopic α ⟨α.1, Path.refl α.1⟩ ∨
      (∃ U : Set (fullQuot S), IsOpen U ∧ frontier U = range (α.2 : unitInterval → fullQuot S) ∧
        Nonempty (U ≃ₜ ↥(puncturedDisc))) ∨
      ∃ β : Loop (fullQuot S), FreelyHomotopic α β ∧ range (β.2 : unitInterval → fullQuot S) ⊆
        (fun z : S.C => (Quot.mk _ z : fullQuot S)) '' {z | (z : UpperHalfPlane) ∈ frontier S.C}) :
    (∃ (S' : HypSurfBdry) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b c : ℝ),
        IsTrouserCoreWithLengths S' A B C a b c ∧ (a = 0 ∨ b = 0 ∨ c = 0) ∧ IsIsometricSurf S S') ∨
      (∃ S' : HypSurfBdry, IsHalfAnnulusModel S' ∧ IsIsometricSurf S S') ∨
      (∃ S' : HypSurfBdry, IsPuncturedDiscModel S' ∧ IsIsometricSurf S S') ∨
      ∃ S' : HypSurfBdry, IsDiscModel S' ∧ IsIsometricSurf S S' := by
  sorry

/-- **Right-angled hexagon** (Ch. 3 §3.5, H1:2464): six points `v 0, …, v 5` of `ℍ` (indices mod `6`) that are the
vertices, in
cyclic order, of a convex hyperbolic polygon `P` (`Katok1992.IsHypPolygon P v`) all of whose six angles are right angles
(`Katok1992.polygonAngle`, the angle between the two sides at the vertex; the angle at an ideal vertex is `0`, so a
polygon
with right angles has all its vertices in `ℍ`). -/
def IsRightAngledHexagon (v : Fin 6 → UpperHalfPlane) : Prop :=
  ∃ P : Set UpperHalfPlane, Katok1992.IsHypPolygon P (fun i => Katok1992.toExtH (v i)) ∧ HypConvex P ∧
    ∀ i, Katok1992.polygonAngle (fun i => Katok1992.toExtH (v i)) i = π / 2

/-- **Proposition 3.5.4** (SSS for hyperbolic right-angled hexagons, Ch. 3 §3.5, H1:2464). A right-angled hexagon in `ℍ`
is determined up to isometry by the lengths of three alternating sides, and these can be any three positive numbers: for
all `a, b, c > 0` there is a right-angled hexagon with `d(v 0, v 1) = a`, `d(v 2, v 3) = b`, `d(v 4, v 5) = c`, and any
two such
hexagons are related by an isometry of `ℍ` mapping `v i` to `v' i`. -/
theorem prop3_5_4 :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → ∃ v : Fin 6 → UpperHalfPlane, IsRightAngledHexagon v ∧
      dist (v 0) (v 1) = a ∧ dist (v 2) (v 3) = b ∧ dist (v 4) (v 5) = c) ∧
    ∀ v v' : Fin 6 → UpperHalfPlane, IsRightAngledHexagon v → IsRightAngledHexagon v' →
      dist (v 0) (v 1) = dist (v' 0) (v' 1) → dist (v 2) (v 3) = dist (v' 2) (v' 3) →
      dist (v 4) (v 5) = dist (v' 4) (v' 5) → ∃ f : UpperHalfPlane ≃ᵢ UpperHalfPlane, ∀ i, f (v i) = v' i := by
  sorry

/-- **Theorem 3.5.8** (a trouser is determined by the lengths of its boundary components, Ch. 3 §3.5, H1:2501). Given
`a, b, c ≥ 0` there is a trouser with boundary components labelled `A, B, C` of lengths `a, b, c` (length `0` is a
cusp), and
it is unique: the labelled, oriented triple `(A, B, C)` (`ABC = ±1`, boundary classes oriented with the surface on the
left)
is unique up to conjugation in `SL(2, ℝ)` (and the signs of the lifts to `SL(2, ℝ)`) as soon as one of `a, b, c` is
positive. *Correction:* for three cusps (`a = b = c = 0`) the orientation of the cusps is not recorded in
`IsTrouserCoreWithLengths` (only hyperbolic generators carry the condition `0 < leftForm`), and the triples `(A, B, C)`
and `(A⁻¹, B⁻¹, BA)` of `Γ(2)` are not `SL(2, ℝ)`-conjugate (the lower-left entry of a conjugate of
`[[1, t], [0, 1]]` has the sign of `−t`); there the conjugating element is taken in `GL(2, ℝ)` (an isometry of `ℍ`
possibly reversing orientation), which is the book's "unique up to isometry". This implies the book's statement and the
`SL(2, ℝ)` form is the one needed by Imayoshi–Taniguchi §3.5 (there `a, b, c > 0`). -/
theorem thm3_5_8 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ (S : HypSurfBdry) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ), IsTrouserCoreWithLengths S A B C a b c) ∧
    ∀ (S S' : HypSurfBdry) (A B C A' B' C' : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsTrouserCoreWithLengths S A B C a b c → IsTrouserCoreWithLengths S' A' B' C' a b c →
        (¬ (a = 0 ∧ b = 0 ∧ c = 0) →
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
            (g * A * g⁻¹ = A' ∨ g * A * g⁻¹ = -A') ∧ (g * B * g⁻¹ = B' ∨ g * B * g⁻¹ = -B') ∧
            (g * C * g⁻¹ = C' ∨ g * C * g⁻¹ = -C')) ∧
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) ℝ,
          (g * Matrix.SpecialLinearGroup.toGL A * g⁻¹ = Matrix.SpecialLinearGroup.toGL A' ∨
            g * Matrix.SpecialLinearGroup.toGL A * g⁻¹ = Matrix.SpecialLinearGroup.toGL (-A')) ∧
          (g * Matrix.SpecialLinearGroup.toGL B * g⁻¹ = Matrix.SpecialLinearGroup.toGL B' ∨
            g * Matrix.SpecialLinearGroup.toGL B * g⁻¹ = Matrix.SpecialLinearGroup.toGL (-B')) ∧
          (g * Matrix.SpecialLinearGroup.toGL C * g⁻¹ = Matrix.SpecialLinearGroup.toGL C' ∨
            g * Matrix.SpecialLinearGroup.toGL C * g⁻¹ = Matrix.SpecialLinearGroup.toGL (-C')) := by
  sorry

end Hubbard2006
