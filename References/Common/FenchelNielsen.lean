import References.Common.HyperbolicSurface
import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

/-!
# Shared layer: Fenchel–Nielsen lengths and twists

The geometric computation behind Fenchel–Nielsen coordinates (Hubbard 2006 §7.6, Imayoshi–Taniguchi §3.4–3.6, Nag):
the **length** of a closed curve of a marked surface and the **twist** of a triple of loops, read off a
uniformization. The topological side (which multicurves and which arcs make a Fenchel–Nielsen datum, Hubbard
Thm 7.6.3) is *not* in this file: it belongs to the individual works. The file is geometric and uses the
conventions of `Common/HyperbolicSurface.lean`; it adds no theorem. Everything is a genuine definition.

**Twist (algebraic, Hubbard Def. 7.6.1 and Remark 7.6.2).** After a marking and a uniformization `(Γ, p)` the arcs and
curves of Hubbard's construction become three elements `g, a, b ∈ Γ`: `g` the class of the curve `γ`, and `a, b` the
classes of the two boundary curves joined by the arc `γ′`, all based at a common lift of the base point `p_γ`. The
twist is the signed distance on `axisH g` between the feet of the common perpendiculars from `axisH a` and from
`axisH b` (for a parabolic `a`, from its fixed point), positive when the path from the surface to `γ` turns right.
Two definitions are exported, as asked by the Imayoshi–Taniguchi lane:
(i) `footDisp g a b`, the **oriented** displacement along `axisH g`, in the direction in which `g` translates, from the
  foot of `a` to the foot of `b` (`footDisp g⁻¹ a b = − footDisp g a b`);
(ii) `twistLength g a b = ε · footDisp g a b` with `ε = −1` if `a` lies to the left of `axisH g` and `+1` if it lies to
  the right ("turn right = positive"). It does not depend on the orientation of the axis, nor on the sign of the lift
  `g ↦ −g` to `SL(2, ℝ)`. Imayoshi–Taniguchi's twist `θ_j` is stated by that lane as `± 2π · footDisp g a b / ℓ(g)`
  with its own sign written out (their sign is opposite to Wolpert's), so the sign is never hidden in `twistLength`.

**The foot of the common perpendicular, without ideal-boundary charts.** For an ideal point `ξ` of `ℍ` let the
Busemann function be `b_ξ(z) = log (|z − ξ|² / Im z)` (`−log Im z` for `ξ = ∞`). On a geodesic line not ending at `ξ`
it has a unique minimum, at the foot of the perpendicular from `ξ`. For a hyperbolic `a` the sum `b_{ξ₁} + b_{ξ₂}`
over its two fixed points is minimal on `axisH g` exactly at the foot of the common perpendicular of `axisH a` and
`axisH g` (checked on `g = diag(λ, 1/λ)`: the minimum is at `y² = x₁x₂`), so one definition covers hyperbolic and
parabolic `a`. No attracting/repelling labelling of fixed points is needed.

**Junk and hypotheses.** `footPt g a` is a `Classical.epsilon` choice of a minimizer; it is *the* minimizer exactly
when the minimizer is unique, which holds when `g` is hyperbolic, `a` is hyperbolic or parabolic, and `a` has no
fixed point in common with `g` (the axes are disjoint and not asymptotic). Every statement of the program that uses
`footDisp` / `twistLength` carries these hypotheses. IT allows `a` and `b` to be conjugate in the same trouser; no
distinctness is assumed. For `a = ±1` the fixed-point set is all of `ℙ¹(ℝ)` and the finite sums are junk `0`.

**Lengths and twists of marked surfaces.** `IsLengthOfLoop σ ℓ` says that `ℓ` is the length of the geodesic in the
free homotopy class of the loop `σ` on a hyperbolic surface (`LiZhongQC.freeHomotopyLength` for a uniformization),
and `IsTwistOfLoops σg σa σb t` that `t` is the twist of the three loops (all based at a point `y`), computed in a
uniformization from lifts of the loops starting at one point over `y`. Both are **relations**: `Quot` has no
choice-free evaluation. That the relations are single valued (independent of the uniformization and, for the twist,
of the lift) is a statement of Hubbard §7.6, not assumed here. The representative-level relations `markedLength`,
`markedTwist` (closed surfaces `LiZhongQC.MarkedRS`) and `markedLengthFT`, `markedTwistFT` (finite type without
boundary discs, `LiZhongQC.MarkedFiniteTypeRS S₀ g n 0`) push the loops of `S₀` forward by the marking; `lengthOf`,
`twistOf` (on `LiZhongQC.TeichSpace S₀`) and `lengthOfFT`, `twistOfFT` (on `LiZhongQC.TeichSpaceFiniteType S₀ g n 0`)
are the thin wrappers on the Teichmüller space: some marked surface representing the class has the relation.
Hubbard's `T_S` for a surface with ideal boundary (`rel I(S)`, 6.4.1) is not modelled.

* Shared notion (Busemann function of an ideal point of `ℍ`) — `busemann`
* Shared notion (fixed points of an element of `SL(2, ℝ)` on the boundary `ℙ¹(ℝ)`; Busemann sum over them;
  foot point on an axis) — `fixedPtsH`, `busemannSum`, `IsFootPoint`, `footPt`
* Shared notion (oriented displacement along an axis; the oriented displacement between the feet) —
  `signedAxisDisp`, `footDisp`
* Shared notion (side of an axis for an ideal point; side sign of an element) — `leftFormIdeal`, `sideSign`
* Shared notion (twist length, Hubbard Def. 7.6.1) — `twistLength`
* Shared notion (lift of a loop; length of a loop; twist of three loops) — `LiftsTo`, `IsLengthOfLoop`,
  `IsTwistOfLoops`
* Shared notion (length and twist relations at the level of a marked surface) — `markedLength`, `markedTwist`,
  `markedLengthFT`, `markedTwistFT`
* Shared notion (length and twist relations on the Teichmüller space; Hubbard (7.6.1), Def. 7.6.1) —
  `lengthOf`, `twistOf`, `lengthOfFT`, `twistOfFT`
-/

open Set Metric Topology
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace References

open LiZhongQC

/-! ## The foot of a perpendicular and the twist -/

/-- **Busemann function** of an ideal point `ξ ∈ ℙ¹(ℝ) = ℝ ∪ {∞}` of `ℍ`, at `z ∈ ℍ`: `log (|z − ξ|² / Im z)` for
`ξ ∈ ℝ` and `−log (Im z)` for `ξ = ∞` (the horocycle height). The argument of `log` is positive since `Im z > 0`:
no `log 0` junk. -/
def busemann (ξ : OnePoint ℝ) (z : UpperHalfPlane) : ℝ :=
  ξ.elim (-Real.log z.im) (fun x => Real.log ((((z : ℂ).re - x) ^ 2 + z.im ^ 2) / z.im))

/-- The **fixed points of `g ∈ SL(2, ℝ)` on the boundary** `ℙ¹(ℝ) = OnePoint ℝ` of `ℍ` (Mathlib's action of
`GL(2, ℝ)` on `OnePoint ℝ`, through `Matrix.SpecialLinearGroup.mapGL`). Two points for a hyperbolic `g`, one for a
parabolic `g`, none for an elliptic `g`, all of them for `g = ±1`. -/
def fixedPtsH (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set (OnePoint ℝ) :=
  {ξ | Matrix.SpecialLinearGroup.mapGL ℝ g • ξ = ξ}

/-- The **sum of the Busemann functions over the fixed points of `a`** (a finite sum for `a ≠ ±1`). -/
def busemannSum (a : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑ᶠ ξ ∈ fixedPtsH a, busemann ξ z

/-- **`q` is a foot point of `a` on the axis of `g`**: `q ∈ axisH g` minimizes `busemannSum a` on `axisH g`. When
the axes are disjoint and not asymptotic this is the foot of the common perpendicular of `axisH a` and `axisH g`
(for hyperbolic `a`) or of the perpendicular from the fixed point of `a` (for parabolic `a`). -/
def IsFootPoint (g a : Matrix.SpecialLinearGroup (Fin 2) ℝ) (q : UpperHalfPlane) : Prop :=
  q ∈ axisH g ∧ ∀ q' ∈ axisH g, busemannSum a q ≤ busemannSum a q'

/-- **The foot point of `a` on the axis of `g`**: a point satisfying `IsFootPoint g a` (`Classical.epsilon`). It is
*the* foot point exactly when the minimizer is unique (see the module docstring); otherwise it is an arbitrary
point. -/
def footPt (g a : Matrix.SpecialLinearGroup (Fin 2) ℝ) : UpperHalfPlane :=
  Classical.epsilon (IsFootPoint g a)

/-- The **oriented displacement along the axis of `g`** from `q₁` to `q₂` (two points of `axisH g`): `d(q₁, q₂)`,
with sign `+` if `q₂` is ahead of `q₁` in the direction in which `g` translates and `−` if it is behind. The sign is
that of `d(q₂, g⁻¹ q₁) − d(q₂, g q₁)`: for `q₂ = q₁ + δ` along the axis, with translation length `ℓ > 0`, this is
`|δ + ℓ| − |δ − ℓ|`, which has the sign of `δ`. *Junk:* the sign is meaningful only for `q₁, q₂ ∈ axisH g` with `g`
hyperbolic. -/
def signedAxisDisp (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (q₁ q₂ : UpperHalfPlane) : ℝ :=
  (SignType.sign (dist q₂ (g⁻¹ • q₁) - dist q₂ (g • q₁)) : ℝ) * dist q₁ q₂

/-- **The oriented displacement between the feet** (`footDisp` of the module docstring): the displacement along
`axisH g`, in the direction in which `g` translates, from the foot point of `a` to the foot point of `b`. For
hyperbolic `g` and `a`, `b` hyperbolic or parabolic with no fixed point in common with `g`, `footDisp g⁻¹ a b =
- footDisp g a b`, and `footDisp (-g) a b = footDisp g a b`. -/
def footDisp (g a b : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  signedAxisDisp g (footPt g a) (footPt g b)

/-- The **side form at an ideal point**: `leftForm g` extended to the boundary, `sign(a + d) · (c ξ² + (d − a) ξ − b)`
for `ξ ∈ ℝ` and `sign(a + d) · c` for `ξ = ∞`. Positive on the ideal points to the left of the direction in which
a hyperbolic `g` translates, negative on the right, zero at the fixed points of `g`. -/
def leftFormIdeal (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : OnePoint ℝ) : ℝ :=
  (SignType.sign (slTrace g) : ℝ) *
    ξ.elim (g 1 0) (fun x => g 1 0 * x ^ 2 + (g 1 1 - g 0 0) * x - g 0 1)

/-- The **side sign of `a` relative to the axis of `g`**: `+1` if the fixed points of `a` lie to the left of the
direction in which `g` translates, `−1` if they lie to the right (all fixed points of `a` lie on the same side when
`axisH a` and `axisH g` are disjoint), `0` otherwise (junk). -/
def sideSign (g a : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  (SignType.sign (∑ᶠ ξ ∈ fixedPtsH a, (SignType.sign (leftFormIdeal g ξ) : ℝ)) : ℝ)

/-- **Twist length** (Hubbard Def. 7.6.1 and Remark 7.6.2): `ε · footDisp g a b` with `ε = −sideSign g a`, i.e. the
signed distance between the feet along `axisH g`, counted positive if the path coming from `a` to `axisH g` turns
right. Independent of the orientation of the axis (`g ↦ g⁻¹` flips both `footDisp` and `sideSign`) and of the sign
of the lift (`g ↦ −g`); symmetric in `a, b` when `a` and `b` lie on opposite sides of `axisH g`, which is the
content of Remark 7.6.2. -/
def twistLength (g a b : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  - sideSign g a * footDisp g a b

/-! ## Lengths and twists of loops on a surface -/

section Loops

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **`G` lifts the loop `σ` from `z₀`**: the lift of `σ` to `ℍ` starting at `z₀` ends at `G z₀`. -/
def LiftsTo (p : UpperHalfPlane → Y) (z₀ : UpperHalfPlane) (G : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {y : Y} (σ : Path y y) : Prop :=
  ∃ c : unitInterval → UpperHalfPlane, Continuous c ∧ c 0 = z₀ ∧ (∀ s, p (c s) = σ s) ∧ c 1 = G • z₀

/-- **`ℓ` is the length of the closed geodesic of the loop `σ`** on a hyperbolic surface `Y`: for some
uniformization `(Γ, p)` of `Y` by a torsion-free Fuchsian group, `ℓ` is the length of the shortest curve in the free
homotopy class of `σ` (`LiZhongQC.freeHomotopyLength`; `ℓ ≥ 0` is a real number, so the length is finite). A
relation, not a function; single-valuedness is Hubbard §7.6. -/
def IsLengthOfLoop (σ : Loop Y) (ℓ : ℝ) : Prop :=
  0 ≤ ℓ ∧ ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → Y),
    IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p ∧ ENNReal.ofReal ℓ = freeHomotopyLength p σ

/-- **`t` is the twist of the three loops** `σg, σa, σb` at `y` on a hyperbolic surface `Y`: for some uniformization
`(Γ, p)` and a point `z₀` over `y`, the lifts of the three loops from `z₀` end at `G z₀, A z₀, B z₀` with
`G, A, B ∈ Γ`, and `t = twistLength G A B`. The elements are determined up to the sign `±1` by `z₀`, and
`twistLength` does not see the sign. A relation, not a function; single-valuedness (independence of `p` and `z₀`) is
Hubbard §7.6. -/
def IsTwistOfLoops {y : Y} (σg σa σb : Path y y) (t : ℝ) : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → Y),
    IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p ∧ ∃ z₀ : UpperHalfPlane, p z₀ = y ∧
      ∃ G ∈ Γ, ∃ A ∈ Γ, ∃ B ∈ Γ, LiftsTo p z₀ G σg ∧ LiftsTo p z₀ A σa ∧ LiftsTo p z₀ B σb ∧
        t = twistLength G A B

end Loops

section Marked

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **The length of the closed geodesic of `γ` on a marked closed surface** (Hubbard (7.6.1), `l_γ`): `ℓ` is the
length of the geodesic in the free homotopy class of `marking ∘ γ` on `m.X`. -/
def markedLength (m : MarkedRS S₀) (γ : Loop S₀) (ℓ : ℝ) : Prop :=
  IsLengthOfLoop (Y := m.X.carrier) ⟨m.marking γ.1, γ.2.map m.marking.continuous⟩ ℓ

/-- **The twist of three loops of `S₀` based at `x` on a marked closed surface** (Hubbard Def. 7.6.1). -/
def markedTwist (m : MarkedRS S₀) {x : S₀} (g a b : Path x x) (t : ℝ) : Prop :=
  IsTwistOfLoops (Y := m.X.carrier) (g.map m.marking.continuous) (a.map m.marking.continuous)
    (b.map m.marking.continuous) t

/-- As `markedLength`, for a marked surface of finite type `(g, n, 0)` (without boundary discs). -/
def markedLengthFT {g n : ℕ} (m : MarkedFiniteTypeRS S₀ g n 0) (γ : Loop S₀) (ℓ : ℝ) : Prop :=
  IsLengthOfLoop (Y := m.X.carrier) ⟨m.marking γ.1, γ.2.map m.marking.continuous⟩ ℓ

/-- As `markedTwist`, for a marked surface of finite type `(g, n, 0)`. -/
def markedTwistFT {g n : ℕ} (m : MarkedFiniteTypeRS S₀ g n 0) {x : S₀} (g' a b : Path x x) (t : ℝ) : Prop :=
  IsTwistOfLoops (Y := m.X.carrier) (g'.map m.marking.continuous) (a.map m.marking.continuous)
    (b.map m.marking.continuous) t

/-- **The length relation on the Teichmüller space `T(S₀)`** (Hubbard (7.6.1), `l_γ(τ)`): some marked surface
representing `τ` has `ℓ` as the length of the geodesic of `γ`. -/
def lengthOf (τ : TeichSpace S₀) (γ : Loop S₀) (ℓ : ℝ) : Prop :=
  ∃ m : MarkedRS S₀, Quot.mk _ m = τ ∧ markedLength m γ ℓ

/-- **The twist relation on the Teichmüller space `T(S₀)`** (Hubbard Def. 7.6.1, `t_γ(τ)`). -/
def twistOf (τ : TeichSpace S₀) {x : S₀} (g a b : Path x x) (t : ℝ) : Prop :=
  ∃ m : MarkedRS S₀, Quot.mk _ m = τ ∧ markedTwist m g a b t

/-- The length relation on `T_{g,n,0}(S₀)` (finite type, no boundary discs). -/
def lengthOfFT {g n : ℕ} (τ : TeichSpaceFiniteType S₀ g n 0) (γ : Loop S₀) (ℓ : ℝ) : Prop :=
  ∃ m : MarkedFiniteTypeRS S₀ g n 0, Quot.mk _ m = τ ∧ markedLengthFT m γ ℓ

/-- The twist relation on `T_{g,n,0}(S₀)` (finite type, no boundary discs). -/
def twistOfFT {g n : ℕ} (τ : TeichSpaceFiniteType S₀ g n 0) {x : S₀} (g' a b : Path x x) (t : ℝ) : Prop :=
  ∃ m : MarkedFiniteTypeRS S₀ g n 0, Quot.mk _ m = τ ∧ markedTwistFT m g' a b t

end Marked

end References
