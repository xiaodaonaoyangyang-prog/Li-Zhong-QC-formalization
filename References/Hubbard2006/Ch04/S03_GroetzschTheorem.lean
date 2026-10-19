import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.3: Grötzsch's theorem and moduli of cylinders (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 3460–3640.

**Conventions.** The band `B_m = {0 < Im z < m}` is `bandB m`. The cylinder `A_m = B_m / ℤ` is modelled by the round
annulus `{1 < |w| < e^{2πm}}` of `References.roundAnnulus m` (Hubbard's modulus normalization, `HasModulus`) through the
covering `covA : z ↦ e^{−2πi z}` (a map `B_m → A_m` with deck group `z ↦ z + 1`); Exercise 3.2.4 is this identification.
A map of cylinders `f` *lifts* to `f̃ : B_m → B_{m'}` when `f (covA z) = covA (f̃ z)`.

* Def. 4.3.1 (the band `B_m` and the cylinder `A_m`) — `bandB`, `covA`
* Thm 4.3.2 (Grötzsch: `1/K ≤ m/m' ≤ K` for a `K`-quasiconformal map `A_m → A_m'`) — `thm4_3_2_a`
* Thm 4.3.2 (equality forces the affine map `x + iy ↦ x + x₀ + i (m'/m) y`, or its boundary-swapping form; lifts) —
  `affA`, `affB`, `IsCylinderLift`, `thm4_3_2_b`
* Thm 4.3.2 (the affine maps are quasiconformal with `K = max(m/m', m'/m)`) — `thm4_3_2_c`
* Cor. 4.3.3 (there is no quasiconformal map `𝔻 → ℂ`) — `cor4_3_3`
* Cor. 4.3.6 (the same inequality for Riemann surfaces isomorphic to cylinders) — `cor4_3_6`
* Thm 4.3.4–4.3.5 (the proof of Grötzsch's theorem: the area/extremal-length step) — omitted: proof step
* Exercise 4.3.7 — omitted: exercise
-/

open Set
open scoped Real

namespace Hubbard2006

open LiZhongQC References

/-- **The band `B_m = {z | 0 < Im z < m}`** (Definition 4.3.1, H1:3462). -/
def bandB (m : ℝ) : Set ℂ := {z | 0 < z.im ∧ z.im < m}

/-- **The covering `B_m → A_m`** (Definition 4.3.1): `z ↦ e^{−2πi z}`, from the band `B_m` onto the round annulus
`{1 < |w| < e^{2πm}}`, invariant exactly under the translation `z ↦ z + 1`. -/
noncomputable def covA (z : ℂ) : ℂ := Complex.exp (-(2 * π * Complex.I) * z)

/-- **Theorem 4.3.2 (Grötzsch), inequality** (H1:3474). If `f : A_m → A_m'` is a `K`-quasiconformal homeomorphism of
cylinders, then `1/K ≤ m/m' ≤ K`. -/
theorem thm4_3_2_a {m m' K : ℝ} (hm : 0 < m) (hm' : 0 < m')
    (f : ↥(roundAnnulus m) ≃ₜ ↥(roundAnnulus m')) (hf : IsKQCRS f K) : K⁻¹ ≤ m / m' ∧ m / m' ≤ K := by
  sorry

/-- **The affine lift of Theorem 4.3.2**: `x + i y ↦ x + x₀ + i (m'/m) y`, a map of the band `B_m` onto `B_{m'}`. -/
noncomputable def affA (m m' x₀ : ℝ) (z : ℂ) : ℂ := ((z.re + x₀ : ℝ) : ℂ) + ((m' / m * z.im : ℝ) : ℂ) * Complex.I

/-- **The boundary-swapping affine lift** `x + i y ↦ x₀ − x + i (m' − (m'/m) y)` (the map `affA` composed with the
half-turn `z ↦ i m − z` of `B_m`): it exchanges the two boundary components of the cylinder and is orientation
preserving, with the same dilatation. For `m = m'` it lifts `w ↦ R / w` on `{1 < |w| < R}`. -/
noncomputable def affB (m m' x₀ : ℝ) (z : ℂ) : ℂ :=
  ((x₀ - z.re : ℝ) : ℂ) + ((m' - m' / m * z.im : ℝ) : ℂ) * Complex.I

/-- **`F` is a lift of `f`** through the coverings `covA` of `B_m → A_m` and `B_{m'} → A_{m'}`:
`f (covA z) = covA (F z)` for `z ∈ B_m`. -/
def IsCylinderLift {m m' : ℝ} (f : ↥(roundAnnulus m) → ↥(roundAnnulus m')) (F : ℂ → ℂ) : Prop :=
  ∀ (w : ↥(roundAnnulus m)) (z : ℂ), z ∈ bandB m → covA z = (w : ℂ) → ((f w : ↥(roundAnnulus m')) : ℂ) = covA (F z)

/-- **Theorem 4.3.2 (Grötzsch), equality case** (H1:3474). If equality is realized (`m / m' = K` or `m' / m = K`),
then `f` lifts to the affine map `f̃ (x + i y) = x + x₀ + i (m'/m) y` of `B_m` onto `B_{m'}` (`affA`), for a real
constant `x₀`, **or to its boundary-swapping form `affB`**. *Correction to the book:* the book lists only the first
form, but the half-turn of the cylinder (e.g. `w ↦ R / w` for `m = m'`) is an orientation-preserving extremal map
that is not of that form. -/
theorem thm4_3_2_b {m m' K : ℝ} (hm : 0 < m) (hm' : 0 < m')
    (f : ↥(roundAnnulus m) ≃ₜ ↥(roundAnnulus m')) (hf : IsKQCRS f K) (heq : m / m' = K ∨ m' / m = K) :
    ∃ x₀ : ℝ, IsCylinderLift f (affA m m' x₀) ∨ IsCylinderLift f (affB m m' x₀) := by
  sorry

/-- **Theorem 4.3.2 (Grötzsch), the extremal maps** (H1:3474). A homeomorphism `A_m → A_m'` lifting to `affA` or
`affB` is `K`-quasiconformal with `K = max (m/m', m'/m)` (the "equality is realized" half of the statement). -/
theorem thm4_3_2_c {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m') (f : ↥(roundAnnulus m) ≃ₜ ↥(roundAnnulus m')) (x₀ : ℝ)
    (hlift : IsCylinderLift f (affA m m' x₀) ∨ IsCylinderLift f (affB m m' x₀)) :
    IsKQCRS f (max (m / m') (m' / m)) := by
  sorry

/-- **Corollary 4.3.3** (H1:3490). There is no quasiconformal map `f : 𝔻 → ℂ`: no `K`-quasiconformal map of the
unit disc (`LiZhongQC.IsKQC`, a homeomorphism onto its image) has image all of `ℂ`. -/
theorem cor4_3_3 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K) : f '' unitDisc ≠ univ := by
  sorry

/-- **Corollary 4.3.6** (H1:3615). Let `A`, `A'` be Riemann surfaces isomorphic to cylinders of finite modulus `M`, `M'`
(`References.HasModulus`) and `f : A → A'` a `K`-quasiconformal homeomorphism. Then `1/K ≤ M / M' ≤ K`. -/
theorem cor4_3_6 {A A' : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace A']
    [ChartedSpace ℂ A'] {M M' K : ℝ} (hA : HasModulus A M) (hA' : HasModulus A' M') (f : A ≃ₜ A')
    (hf : IsKQCRS f K) : K⁻¹ ≤ M / M' ∧ M / M' ≤ K := by
  sorry

end Hubbard2006
