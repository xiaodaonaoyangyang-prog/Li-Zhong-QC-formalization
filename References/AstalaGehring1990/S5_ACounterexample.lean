import References.AstalaGehring1990.S1_Introduction

/-!
# Astala–Gehring 1990, §5 A counterexample

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), §5; source `full.md` of `Astala-CricketsZippersBers-1990.pdf-e9a341c8…`, lines 441–561.

* Definition (the space `T₁` of logarithmic derivatives, the norm (5.1), the closure `T̄₁`, §5) — `setT1`, `normStarU`,
  `closureStar`
* Definition (the map `π(φ) = φ' - φ²/2`, l. 449) — `piMap`
* Theorem 5.2 — `thm5_2`
* Definition (open disk or half-plane; boundaries meeting in acute exterior angles; used in Lemma 5.3) —
  `IsOpenDiskOrHalfPlane`, `MeetInAcuteExteriorAngles`
* Lemma 5.3 — `lemma5_3`

Not items (DESIGN §3):
- the facts quoted from [AG] at l. 449 (`π` is a continuous map of `T₁` into `T`, and `π(T̄₁) ⊆ T̄`), which are not
  cited later (U−);
- the history of [AG, Corollary 3.19] (l. 449);
- the proofs, including the Koebe distortion theorem quoted inside the proof of 5.3.

**Conventions.**
- As in §1, the functions of these spaces vanish off `U`.
- "Conformal mapping of `U` into `ℂ`" is a holomorphic injective map.
- `dist(z, ∂G)` is `Metric.infDist`. It is positive on `G`, which is open and is not `ℂ`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace AstalaGehring1990

open LiZhongQC
open LehtoVirtanen1973 (IsQuasiconformalMap)

/-- **Definition (5.1)** (§5). The norm `‖φ‖*_U = sup_{z ∈ U} |φ(z)| (1 - |z|²)`. -/
def normStarU (φ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ unitDisc, ENNReal.ofReal (‖φ z‖ * (1 - ‖z‖ ^ 2))

/-- **Definition** (§5). The set `T₁` of the logarithmic derivatives `f''/f'` of the conformal mappings `f` of `U` into
`ℂ` which have a quasiconformal extension to `ℂ̄` (the alternative model of `T` from [AG]).
Modelling: `f` is holomorphic and injective in `U` (so `f' ≠ 0`); the extension is a quasiconformal self-mapping `F`
of `ℂ̄` (`LehtoVirtanen1973.IsQuasiconformalMap F univ`) with `F = f` in `U`, as for `setT`; `f''/f'` is restricted to
`U` by `unitDisc.indicator`. -/
def setT1 : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧
    (∃ F : ExtPlane → ExtPlane, IsQuasiconformalMap F univ ∧ ∀ z ∈ unitDisc, F z = f z) ∧
    φ = unitDisc.indicator (fun z => deriv (deriv f) z / deriv f z)}

/-- **Definition** (§5). The closure of a set `A` of functions in `U` for the norm (5.1) (for `A = T₁`: the closure
`T̄₁`): the functions vanishing off `U` which are limits in (5.1) of elements of `A`. -/
def closureStar (A : Set (ℂ → ℂ)) : Set (ℂ → ℂ) :=
  {φ | unitDisc.indicator φ = φ ∧ ∀ ε > (0 : ℝ), ∃ ψ ∈ A, normStarU (φ - ψ) < ENNReal.ofReal ε}

/-- **Definition** (§5, l. 449). The map `π(φ) = φ' - ½ φ²` (so that `π(f''/f') = S_f`), restricted to `U`. -/
def piMap (φ : ℂ → ℂ) : ℂ → ℂ :=
  unitDisc.indicator (fun z => deriv φ z - φ z ^ 2 / 2)

/-- **Theorem 5.2** (§5). There exists a conformal mapping `f` of `U` into `ℂ` for which `S_f` is in `T̄ ∖ π(T̄₁)`.
Modelling: `T̄` is `closureE setT` (§1) and `π(T̄₁)` is the image of `closureStar setT1` under `piMap`. -/
theorem thm5_2 :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧
      unitDisc.indicator (schwarzian f) ∈ closureE setT ∧
        unitDisc.indicator (schwarzian f) ∉ piMap '' closureStar setT1 := by
  sorry

/-- **Definition** (§5, l. 455). `B'` is an open disk or an open half-plane of `ℂ`; the half-plane
`{z : Re((z - p) ν̄) < 0}` has outward normal direction `ν`. -/
def IsOpenDiskOrHalfPlane (B' : Set ℂ) : Prop :=
  (∃ (w : ℂ) (ρ : ℝ), 0 < ρ ∧ B' = ball w ρ) ∨ ∃ p ν : ℂ, ν ≠ 0 ∧ B' = {z : ℂ | ((z - p) * conj ν).re < 0}

/-- **Definition** (§5, l. 455). The boundaries of the open disk `B = B(z₁, r₁)` and of `B'` meet in acute exterior
angles.
Modelling:
- They meet in exactly two points.
- At each of them the outward normals `n` of `B` and `n'` of `B'` satisfy `Re(n n̄') < 0`. The exterior angle of
  `B ∪ B'` there is `π` minus the angle between the normals, so it is acute exactly when the normals make an obtuse
  angle.
- The outward normal of `B` at `x` has the direction `x - z₁`. That of a disk `B(w, ρ)` has the direction `x - w`, and
  that of the half-plane of `IsOpenDiskOrHalfPlane` is `ν`. The sign does not depend on the representation of `B'`. -/
def MeetInAcuteExteriorAngles (z₁ : ℂ) (r₁ : ℝ) (B' : Set ℂ) : Prop :=
  (sphere z₁ r₁ ∩ frontier B').ncard = 2 ∧ ∀ x ∈ sphere z₁ r₁ ∩ frontier B',
    (∀ (w : ℂ) (ρ : ℝ), 0 < ρ → B' = ball w ρ → ((x - z₁) * conj (x - w)).re < 0) ∧
      ∀ p ν : ℂ, ν ≠ 0 → B' = {z : ℂ | ((z - p) * conj ν).re < 0} → ((x - z₁) * conj ν).re < 0

/-- **Lemma 5.3** (§5). Suppose that `G = B ∪ B'` where `B` is an open disk, `B'` is an open disk or half-plane, and
`∂B` and `∂B'` meet in acute exterior angles. If `h` is a homeomorphism of `Ḡ` which maps `G` conformally into `ℂ`
and if (5.4) `|h''/h'(z)| ≤ c dist(z, ∂G)⁻¹` for `z` in `G`, where `0 < c < 1`, then (5.5)
`dia(h(C))/|h(a) - h(b)| ≥ (1 - c)/16 · (dia(C)/|a - b|)^{1-c} - 1`, where `C = ∂B ∖ B'` and `{a, b} = ∂B ∩ ∂B'`.
Modelling:
- `B = B(z₁, r₁)` with `r₁ > 0`, so that `∂B` is the circle `sphere z₁ r₁`.
- `Ḡ` is the closure in `ℂ`, and "homeomorphism of `Ḡ`" is `LiZhongQC.IsHomeomorphOnto` onto the image.
- `dia` is `Metric.diam`; the sets `C` and `h(C)` are compact. -/
theorem lemma5_3 {z₁ : ℂ} {r₁ : ℝ} (hr₁ : 0 < r₁) {B' : Set ℂ} (hB' : IsOpenDiskOrHalfPlane B')
    (hacute : MeetInAcuteExteriorAngles z₁ r₁ B') {h : ℂ → ℂ}
    (hh : IsHomeomorphOnto h (closure (ball z₁ r₁ ∪ B')) (h '' closure (ball z₁ r₁ ∪ B')))
    (hconf : DifferentiableOn ℂ h (ball z₁ r₁ ∪ B')) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (h54 : ∀ z ∈ ball z₁ r₁ ∪ B',
      ‖deriv (deriv h) z / deriv h z‖ ≤ c / infDist z (frontier (ball z₁ r₁ ∪ B')))
    {a b : ℂ} (hab : sphere z₁ r₁ ∩ frontier B' = {a, b}) :
    (1 - c) / 16 * (diam (sphere z₁ r₁ \ B') / ‖a - b‖) ^ (1 - c) - 1 ≤
      diam (h '' (sphere z₁ r₁ \ B')) / ‖h a - h b‖ := by
  sorry

end AstalaGehring1990
