import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.9: Boundary values of quasiconformal maps (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 4944–5160 and `H2` lines 1–80.

**Conventions.** `ℙ¹ = LiZhongQC.ExtPlane` (the one-point compactification of `ℂ`). The hyperbolic distance in `𝔻`
is `LiZhongQC.discPoincareDist` (the normalization with curvature `−4`; bounded distances are unaffected by the factor
`2`). A *reflection* is read as a global involution of `ℙ¹` (Definition 4.9.11); the installed
`LiZhongQC.IsQCReflection`
is the one-sided variant, a near miss.

* Thm 4.9.1 (every `K`-quasiconformal self-map of `ℍ` extends to a homeomorphism of the closed half plane, and the
  reflected map is `K`-quasiconformal) — `thm4_9_1`
* Cor. 4.9.2 (a quasiconformal map of `𝔻` onto a Jordan domain extends to the closure) — `cor4_9_2`
* Def. 4.9.3 (`ℝ`-quasisymmetry with modulus `M`, for increasing homeomorphisms) — exists: `LiZhongQC.IsQuasisymmetric`
* Cor. 4.9.4 (boundary values of `K`-quasiconformal self-maps of `ℍ` fixing `∞` are `ℝ`-quasisymmetric with modulus
  depending only on `K`) — `cor4_9_4`
* Thm 4.9.5 (a quasisymmetric homeomorphism of `ℝ` extends to a quasiconformal self-map of `ℍ`) — exists:
  `LiZhongQC.thm17_2_beurling_ahlfors`
* Prop. 4.9.6 (a quasiconformal self-map of `𝔻` sends a geodesic to a curve at bounded hyperbolic distance from a
  geodesic) — `discGeod`, `prop4_9_6`
* Cor. 4.9.7 (compactness of the normalized `ℝ`-quasisymmetric homeomorphisms of modulus `M`) — `stereo`, `cor4_9_7`
* Def. 4.9.8 (`K`-quasidisc, `K`-quasicircle) — exists: `LiZhongQC.IsKQuasicircle`, `LiZhongQC.IsKQuasidisc`
* Def. 4.9.8 (`K`-quasiarc) — `IsKQuasiarc`
* Prop. 4.9.9 (a homeomorphism that is `K`-quasiconformal off a quasiarc is `K`-quasiconformal) — `prop4_9_9`
* Def. 4.9.10 (`K`-anti-quasiconformal) — `IsKAntiQC`
* Def. 4.9.11 (reflection in a simple closed curve; `K`-quasireflection) — `IsCurveReflection`, `IsKQuasireflection`
* Prop. 4.9.12 (a simple closed curve admits a quasireflection iff it is a quasicircle) — `prop4_9_12`
* Prop. 4.9.13 (distance estimates for a quasireflection in a curve through `∞`) — `IsKQuasireflectionC`,
  `prop4_9_13`
* Prop. 4.9.14 (`Γ` is a quasicircle iff `f⁻¹ ∘ f*` is `ℝ`-quasisymmetric) — `prop4_9_14`
* Thm 4.9.15 (Ahlfors' three point criterion for quasicircles through `∞`) — `thm4_9_15`
* Lemma 4.9.17, 4.9.18 (annulus estimates in the proof of Thm 4.9.15) — omitted: proof step
* Exercise 4.9.16 — omitted: exercise
-/

open Set Metric MeasureTheory Filter
open scoped Topology

namespace Hubbard2006

open LiZhongQC

/-- The reflected extension of a self-map `f` of `ℍ` with boundary values `G`: `f` on `ℍ`, `G` on `ℝ`, and
`z ↦ conj (f (conj z))` on the lower half plane (Theorem 4.9.1). -/
noncomputable def reflectExt (f : ℂ → ℂ) (G : ExtPlane → ExtPlane) (z : ℂ) : ℂ :=
  if 0 < z.im then f z else if z.im = 0 then extToC (G (z : ExtPlane)) else (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

/-- **Theorem 4.9.1** (H1:4944). Every `K`-quasiconformal homeomorphism `f : ℍ → ℍ` extends continuously as a
homeomorphism of the closed half plane `ℝ̄ ∪ ℍ` (`IsHomeoExtension f ℍ ℍ G`), and if the extension fixes `∞` the
reflected extension `f(z̄) := conj f(z)` (`reflectExt`) is `K`-quasiconformal on `ℂ`. *Reading:* for `G ∞ ≠ ∞` the
second half is the same statement after a Möbius change of the target; it is stated for `G ∞ = ∞`. -/
theorem thm4_9_1 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f upperHalf K) (himg : f '' upperHalf = upperHalf) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf upperHalf G ∧
      (G extInf = extInf → IsKQC (reflectExt f G) univ K) := by
  sorry

/-- **Corollary 4.9.2** (H1:4973). If `U` is a Jordan domain and `f : 𝔻 → U` is a quasiconformal homeomorphism, then
`f` extends to a homeomorphism `𝔻̄ → Ū` of the closures (in `ℙ¹`; for bounded `U`, in `ℂ`). -/
theorem cor4_9_2 {U : Set ℂ} (hU : IsJordanDomain U) {f : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc)
    (himg : f '' unitDisc = U) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc U G := by
  sorry

/-- **Corollary 4.9.4** (H1:4985). For every `K ≥ 1` there is `M` such that every `K`-quasiconformal homeomorphism
`f : ℍ → ℍ` whose boundary extension fixes `∞` has, on `ℝ`, boundary values `h : ℝ → ℝ` that are `ℝ`-quasisymmetric
with modulus `M` (`LiZhongQC.IsQuasisymmetric h M`). (The extension exists by Theorem 4.9.1; the installed
`LiZhongQC.thm17_1_quasisymmetric` assumes it, a near miss.) -/
theorem cor4_9_4 {K : ℝ} (hK : 1 ≤ K) :
    ∃ M : ℝ, ∀ (f : ℂ → ℂ), IsKQC f upperHalf K → f '' upperHalf = upperHalf →
      ∀ G : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf upperHalf G → G extInf = extInf →
        ∃ h : ℝ → ℝ, (∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane)) ∧ IsQuasisymmetric h M := by
  sorry

/-- **The hyperbolic geodesic of `𝔻` joining two boundary points** `x ≠ y` of the unit circle: the diameter if
`y = −x`, otherwise the arc inside `𝔻` of the circle with centre `c = (x + y) / (1 + Re (x ȳ))` (the pole of the chord)
and radius `√(|c|² − 1)`, orthogonal to the unit circle. -/
noncomputable def discGeod (x y : ℂ) : Set ℂ :=
  {z | z ∈ unitDisc ∧
    (if 1 + (x * (starRingEnd ℂ) y).re = 0 then ∃ t : ℝ, z = t * x
      else ‖z - (x + y) / (1 + (x * (starRingEnd ℂ) y).re)‖ ^ 2 =
        ‖(x + y) / (1 + (x * (starRingEnd ℂ) y).re)‖ ^ 2 - 1)}

/-- **Proposition 4.9.6** (H1:5018). Let `γ` be the geodesic joining `x`, `y ∈ ∂𝔻` and `f : 𝔻 → 𝔻` a
`K`-quasiconformal homeomorphism with continuous extension `F` to the closed disc. Then `f(γ)` remains a bounded
hyperbolic distance (depending only on `K`) from the geodesic joining `F x` to `F y`: every point of `f(γ)` is within
`C` of a point of `discGeod (F x) (F y)`. -/
theorem prop4_9_6 {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, ∀ (f F : ℂ → ℂ), IsKQC f unitDisc K → f '' unitDisc = unitDisc →
      ContinuousOn F (closedBall 0 1) → EqOn F f unitDisc →
      ∀ x y : ℂ, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y →
        ∀ z ∈ discGeod x y, ∃ w ∈ discGeod (F x) (F y), discPoincareDist (f z) w ≤ C := by
  sorry

/-- The stereographic coordinate of a point of `ℝ ∪ {∞}`: `x ↦ ((x² − 1) + 2 x i) / (x² + 1)` on the unit circle, so
that
uniform convergence of homeomorphisms of `ℝ̄` is uniform convergence of `stereo ∘ h` on `ℝ` (the value at `∞` is the
limit `1`). -/
noncomputable def stereo (x : ℝ) : ℂ :=
  (((x ^ 2 - 1) / (x ^ 2 + 1) : ℝ) : ℂ) + ((2 * x / (x ^ 2 + 1) : ℝ) : ℂ) * Complex.I

/-- **Corollary 4.9.7** (H1:5034). The space of `ℝ`-quasisymmetric homeomorphisms `h : ℝ → ℝ` of modulus `M` with
`h(0) = 0`, `h(1) = 1` is compact for the topology of uniform convergence on `ℝ̄` (uniform convergence of
`stereo ∘ h`, a function on `ℝ` with the uniform structure `ℝ →ᵤ ℂ`). -/
theorem cor4_9_7 (M : ℝ) :
    IsCompact ((fun h : ℝ → ℝ => UniformFun.ofFun (stereo ∘ h)) ''
      {h : ℝ → ℝ | IsQuasisymmetric h M ∧ h 0 = 0 ∧ h 1 = 1}) := by
  sorry

/-- **`K`-quasiarc** (Definition 4.9.8, H1:5052): the image of a closed line segment `[0, 1] ⊂ ℝ ⊂ ℂ` by a
`K`-quasiconformal map `f : ℂ → ℂ` (of `ℙ¹`, fixing `∞`). -/
def IsKQuasiarc (A : Set ℂ) (K : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsKQC f univ K ∧ f '' univ = univ ∧ A = f '' ((fun t : ℝ => (t : ℂ)) '' Icc (0 : ℝ) 1)

/-- **Proposition 4.9.9** (H1:5052). If `U`, `V ⊂ ℂ` are open, `Γ` is a quasiarc in `ℂ` and `f : U → V` is a
homeomorphism that is `K`-quasiconformal on `U ∖ Γ`, then `f` is `K`-quasiconformal on `U`. -/
theorem prop4_9_9 {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {Γ : Set ℂ} {K₀ : ℝ} (hΓ : IsKQuasiarc Γ K₀)
    {f : ℂ → ℂ} (hhom : IsHomeomorphOnto f U V) {K : ℝ} (hK : IsKQC f (U \ Γ) K) : IsKQC f U K := by
  sorry

/-- **`K`-anti-quasiconformal map** (Definition 4.9.10, H1:5060): `f : U → ℂ` is `K`-anti-quasiconformal if the complex
conjugate map `z ↦ conj (f z)` is `K`-quasiconformal on `U`. (Target `ℂ`; maps into `ℙ¹` are read on the part of `U`
where the value is finite.) -/
def IsKAntiQC (f : ℂ → ℂ) (U : Set ℂ) (K : ℝ) : Prop := IsKQC (fun z => (starRingEnd ℂ) (f z)) U K

/-- **Reflection in a simple closed curve** (Definition 4.9.11, H1:5070): `ψ : ℙ¹ → ℙ¹` is an orientation reversing
involutive homeomorphism with fixed locus the Jordan curve `Γ` that exchanges the two complementary components `A₁`,
`A₂` (the fixed locus equal to `Γ` and the exchange of the sides force orientation reversal). -/
def IsCurveReflection (Γ A₁ A₂ : Set ExtPlane) (ψ : ExtPlane → ExtPlane) : Prop :=
  AreComplementaryComponents Γ A₁ A₂ ∧ Continuous ψ ∧ (∀ p, ψ (ψ p) = p) ∧ {p | ψ p = p} = Γ ∧ ψ '' A₁ = A₂

/-- **`K`-quasireflection** (Definition 4.9.11): a reflection that is `K`-anti-quasiconformal, i.e. `z ↦ conj ψ(z)` is
`K`-quasiconformal on the open set of `z ∈ ℂ` with `ψ z ≠ ∞` (the exceptional points `∞`, `ψ(∞)` are removable). -/
def IsKQuasireflection (Γ A₁ A₂ : Set ExtPlane) (ψ : ExtPlane → ExtPlane) (K : ℝ) : Prop :=
  IsCurveReflection Γ A₁ A₂ ψ ∧ IsKAntiQC (fun z : ℂ => extToC (ψ (z : ExtPlane))) {z : ℂ | ψ (z : ExtPlane) ≠ extInf} K

/-- **Proposition 4.9.12** (H1:5072). A simple closed curve `Γ ⊂ ℙ¹` admits a quasireflection if and only if it is a
quasicircle. -/
theorem prop4_9_12 {Γ A₁ A₂ : Set ExtPlane} (hΓ : AreComplementaryComponents Γ A₁ A₂) :
    (∃ (K : ℝ) (ψ : ExtPlane → ExtPlane), IsKQuasireflection Γ A₁ A₂ ψ K) ↔ IsQuasicircle Γ := by
  sorry

/-- **`K`-quasireflection in a curve through `∞`** (Definition 4.9.11, planar form): a continuous involution `ψ` of `ℂ`
(its fixed set `Γ`, a simple closed curve through `∞` in `ℙ¹`) such that `z ↦ conj ψ(z)` is `K`-quasiconformal on `ℂ`.
(Such a `ψ` is an orientation reversing involution, so its fixed set is a properly embedded line.) -/
def IsKQuasireflectionC (Γ : Set ℂ) (ψ : ℂ → ℂ) (K : ℝ) : Prop :=
  Continuous ψ ∧ (∀ z, ψ (ψ z) = z) ∧ {z | ψ z = z} = Γ ∧ IsKAntiQC ψ univ K

/-- **Proposition 4.9.13** (H1:5086). Let `z ↦ z*` be a `K`-quasireflection in a simple closed curve `Γ` through `∞`,
and
`δ(z)` the distance from `z` to `Γ`. There is a constant `C` depending only on `K` such that (1) `|z − w| ≤ C |z* − w|`
for all `z ∈ ℂ`, `w ∈ Γ`, and (2) for all `z ∉ Γ`, `|z − z*|² / (δ(z) δ(z*)) ≤ (1 + C)²`. -/
theorem prop4_9_13 {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, ∀ (Γ : Set ℂ) (ψ : ℂ → ℂ), IsKQuasireflectionC Γ ψ K →
      (∀ z : ℂ, ∀ w ∈ Γ, ‖z - w‖ ≤ C * ‖ψ z - w‖) ∧
        ∀ z ∉ Γ, ‖z - ψ z‖ ^ 2 / (infDist z Γ * infDist (ψ z) Γ) ≤ (1 + C) ^ 2 := by
  sorry

/-- **Proposition 4.9.14** (H1:5122). Let `Γ ⊂ ℙ¹` be a simple closed curve through `∞` and `f : ℍ → U`, `f* : ℍ* → U*`
conformal isomorphisms onto the two components of `ℙ¹ ∖ Γ` (`ℍ*` the lower half plane) with continuous boundary
extensions `G`, `G*` fixing `∞` (Carathéodory) and `h : ℝ → ℝ` the homeomorphism with `G h(x) = G* x`, i.e. the
boundary map of `f⁻¹ ∘ f*` on `ℝ`. Then `Γ` is a quasicircle if and only if `h` is `ℝ`-quasisymmetric (for some
modulus). -/
theorem prop4_9_14 {Γ : Set ExtPlane} {U U' : Set ℂ} (hΓ : AreComplementaryComponents Γ (toExt U) (toExt U'))
    {f f' : ℂ → ℂ} {G G' : ExtPlane → ExtPlane} (hf : IsConformalOnto f upperHalf U)
    (hf' : IsConformalOnto f' lowerHalf U')
    (hG : IsHomeoExtension f upperHalf U G) (hG' : IsHomeoExtension f' lowerHalf U' G') (hGinf : G extInf = extInf)
    (hGinf' : G' extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ x : ℝ, G (((h x : ℝ) : ℂ) : ExtPlane) = G' ((x : ℂ) : ExtPlane)) :
    IsQuasicircle Γ ↔ ∃ M : ℝ, IsQuasisymmetric h M := by
  sorry

/-- **Theorem 4.9.15 (Ahlfors' three point criterion)** (H1:5144). Let `Γ = γ(ℝ) ∪ {∞} ⊂ ℙ¹` be a simple closed curve
through `∞` (`γ : ℝ → ℂ` a proper embedding). Then `Γ` is a quasicircle if and only if there is a constant `C` with
`|z₁ − z₂| ≤ C |z₁ − z₃|` for any three points `z_i = γ(t_i)`, `t₁ < t₂ < t₃`, appearing in that order on `Γ`. (The
installed `LiZhongQC.thm16_1_three_point` is the necessity for the image of `ℝ` and `LiZhongQC.thm18_1` concerns
curves not through `∞`, near misses.) -/
theorem thm4_9_15 {γ : ℝ → ℂ} (hγ : Topology.IsEmbedding γ) (hproper : Tendsto (fun t => ‖γ t‖) (cocompact ℝ) atTop) :
    IsQuasicircle (toExt (range γ) ∪ {extInf}) ↔
      ∃ C : ℝ, ∀ t₁ t₂ t₃ : ℝ, t₁ < t₂ → t₂ < t₃ → ‖γ t₁ - γ t₂‖ ≤ C * ‖γ t₁ - γ t₃‖ := by
  sorry

end Hubbard2006
