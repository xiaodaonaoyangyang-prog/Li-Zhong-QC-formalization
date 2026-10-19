import References.Pommerenke1992.Ch07.S03_SmirnovDomainsAndAhlforsRegularity

/-!
# Pommerenke 1992, Ch. 7 §7.4 Lavrentiev Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 7 *Smirnov and Lavrentiev Domains*, §7.4;
source `full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 7002–7198.

* Definition (Lavrentiev curve, (7.4.1) = (7.1.3), "quasismooth", "chord-arc"; Lavrentiev domain, its inner domain;
  "are called Lavrentiev domains" at l. 4563; cited in the proof of Theorem 7.9 and at l. 7375) —
  `IsLavrentievCurve`, `IsLavrentievDomain`
* Proposition 7.7 (cited at l. 7233 and in Exercise 7.4.4) — `prop7_7`
* Theorem 7.8 (Zin85; (7.4.2); cited in the proofs of Theorem 7.11, Corollary 7.12, Proposition 7.13) — `thm7_8`
* Remark after Theorem 7.8, (7.4.3) (cited in the proof of Corollary 7.12, l. 7295) — `eq7_4_3`
* Definition (bilipschitz map, (7.4.4); used in Theorems 7.9, 7.10; restated in Exercise 10.2.1) — `IsBilipschitzOn`
* Theorem 7.9 (Tuk80, Tuk81, JeKe82b) — `thm7_9`
* Theorem 7.10 (Tuk80, Tuk81; cited in the proof of Theorem 7.9) — `thm7_10`

Not items (DESIGN §3): the Lipschitz-graph example of a Lavrentiev domain (l. 7012); the remarks after Theorem 7.8
(the example `f(z) = (1 - z)²`, "(7.4.2) implies that `G` is an Ahlfors-regular John domain", Pom82, Zin85; quoted,
not cited); "a sense-preserving bilipschitz map of `ℂ` onto `ℂ` is quasiconformal but not vice versa" and the
quasidisk example (l. 7076; not cited); (7.4.5)–(7.4.10) (steps of the proof of Theorem 7.10, which reuses
`thm5_15_partB` and `prop5_21_crossRatio` of Ch. 5); the proof of Theorem 7.8 uses Proposition 1.6, printed there
for Corollary 1.6 (recorded in Part A).

**Conventions.** As in §7.1. A Jordan curve `J ⊆ ℂ` is `IsJordanCurve (toExt J)`; a rectifiable Jordan curve is
`LehtoVirtanen1973.IsRectifiableJordanCurve J`, as in Ch. 6 (a Jordan curve of finite linear measure; its length is
`Λ(J)`, Prop. 6.2). For `a ≠ b` in `J`, the two arcs of `J` between `a` and `b`
are (up to their endpoints, which have linear measure `0`) the two components of `J ∖ {a, b}`, as in the project's
bounded turning; the shorter arc satisfies a length bound if and only if one of the two arcs does. The inner domain
is `innerDomain J` (Ch. 1). The mean over `I(z)` in (7.4.3) is the `ℝ≥0∞`-average over its parameter interval, as in
`HasArcMeanBound`. A map "of `ℂ` onto `ℂ`" is a surjective map `ℂ → ℂ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve)

/-- **Definition (7.4.1)** (§7.4; = (7.1.3); cited in the proof of Theorem 7.9 and at l. 7375). A Lavrentiev curve
("quasismooth", "chord-arc") is a rectifiable Jordan curve `J` such that `Λ(J(a, b)) ≤ M₁ |a - b|` for `a, b ∈ J`,
where `J(a, b)` is the shorter arc of `J` between `a` and `b`.
Modelling: `J ⊆ ℂ` with `LehtoVirtanen1973.IsRectifiableJordanCurve J`; for `a ≠ b` the bound is asked for one of
the two components of `J ∖ {a, b}` (equivalent to the shorter arc, see the file header; for `a = b` the book's arc is
a point); `M₁` depends on `J`. -/
def IsLavrentievCurve (J : Set ℂ) : Prop :=
  LehtoVirtanen1973.IsRectifiableJordanCurve J ∧ ∃ M₁ : ℝ, ∀ a ∈ J, ∀ b ∈ J, a ≠ b →
    ∃ p ∈ J \ {a, b}, μH[1] (connectedComponentIn (J \ {a, b}) p) ≤ ENNReal.ofReal (M₁ * ‖a - b‖)

/-- **Definition** (§7.4, l. 7010; "are called Lavrentiev domains" at l. 4563). The inner domain of a Lavrentiev
curve is a Lavrentiev domain. -/
def IsLavrentievDomain (G : Set ℂ) : Prop :=
  ∃ J : Set ℂ, IsLavrentievCurve J ∧ G = innerDomain J

/-- **Proposition 7.7** (§7.4; cited at l. 7233 and in Exercise 7.4.4). A domain is a Lavrentiev domain if and only if
it is an Ahlfors-regular quasidisk.
Modelling: "Ahlfors-regular quasidisk" is a quasidisk (§5.1) that is an Ahlfors-regular domain (§7.3); for a quasidisk
`∂G` is the quasicircle, which is locally connected, so this says that the quasicircle is Ahlfors-regular, as in the
proof. -/
theorem prop7_7 {G : Set ℂ} : IsLavrentievDomain G ↔ IsQuasidisk G ∧ IsAhlforsRegularDomain G := by
  sorry

/-- **Theorem 7.8** (§7.4; Zin85; (7.4.2) cited at l. 7237; cited in the proofs of Theorem 7.11, Corollary 7.12,
Proposition 7.13). Let `f` map `𝔻` conformally onto the inner domain `G` of a rectifiable Jordan curve. Then `G` is a
Lavrentiev domain if and only if `G` is linearly connected and
`(1/Λ(I(z))) ∫_{I(z)} |f'(ζ)| |dζ| ≤ M₂ |f'(z)|` for `z ∈ 𝔻`.
Modelling: (7.4.2) is `HasArcMeanBound f 1` (the condition (7.3.10) with `q = 1`). -/
theorem thm7_8 {J : Set ℂ} (hJ : LehtoVirtanen1973.IsRectifiableJordanCurve J) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) :
    IsLavrentievDomain (innerDomain J) ↔ IsLinearlyConnected (innerDomain J) ∧ HasArcMeanBound f 1 := by
  sorry

/-- **Remark after Theorem 7.8, (7.4.3)** (§7.4; cited in the proof of Corollary 7.12, l. 7295). The opposite
inequality `|f'(z)| ≤ (K₃/Λ(I(z))) ∫_{I(z)} |f'(ζ)| |dζ|` (`z ∈ 𝔻`) holds for all conformal maps, because
`Λ(I(z)) |f'(z)| ≤ K₃ diam f(I(z))` by Proposition 4.19.
[CORRECTION] It is stated for the conformal maps `f` of `𝔻` into `ℂ` with `f' ∈ H¹`; "for all conformal maps" is
false. The argument needs, besides Proposition 4.19, `diam f(I) ≤ ∫_I |f'(ζ)| |dζ|`, which holds when `f' ∈ H¹`:
then `f` extends continuously to `𝔻̄` and is absolutely continuous on `𝕋` (Dur70, Thm. 3.11; for a Jordan domain this
is (6.3.2), `Λ(f(I)) = ∫_I |f'(ζ)| |dζ|`).
Counterexample: let `μ` be Piranian's singular Zygmund measure (Pir66; the measure of the book's example (7.3.5),
(7.3.6)), `g(z) = ∫_𝕋 (ζ + z)/(ζ - z) dμ(ζ)` the Bloch function of (7.2.8) (`Re g > 0`, so `g ∈ Hᵖ` for
`p < 1`, and `g`, hence `F'`, has finite angular limits almost everywhere), and
`F(z) = ∫₀^z exp(+a g(ζ)) dζ` with `a = 1/(2‖g‖_B)` (the sign of (7.3.6) flipped). Then
`(1 - |z|²)|F''(z)/F'(z)| = a(1 - |z|²)|g'(z)| ≤ 1/2`, so `F` maps `𝔻` conformally onto a quasidisk (Becker's
criterion, Corollary 5.23). Since `μ` is singular, `Re g(rζ) → 0` for almost all `ζ ∈ 𝕋` (as in (7.3.7)), so
`|F'(ζ)| = exp(a Re g(ζ)) = 1` almost everywhere on `𝕋` and the right side of (7.4.3) equals `K₃` for every `z`; but
`Re g(rζ) → +∞` at the `μ`-almost all points where `μ*' = ∞`, so `|F'|` is unbounded in `𝔻`. The only use of (7.4.3),
in the proof of Corollary 7.12, is for Lavrentiev domains, where `f' ∈ H¹`.
Modelling: `K₃` is absolute (`∃ K₃, ∀ f`); `H¹` is `GarnettMarshall2005.MemHardy 1`; `f'(ζ)` is a boundary function
`φ` of `f'` (it exists, `f'` being in `H¹`); the mean over `I(z)` is the `ℝ≥0∞`-average over its parameter
interval. -/
theorem eq7_4_3 : ∃ K₃ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
    GarnettMarshall2005.MemHardy 1 (deriv f) →
    ∃ φ : ℂ → ℂ, IsAngularBoundaryFun (deriv f) φ ∧ ∀ z ∈ unitDisc,
      ‖deriv f z‖ₑ ≤ ENNReal.ofReal K₃ *
        ⨍⁻ t in Icc (arg z - π * (1 - ‖z‖)) (arg z + π * (1 - ‖z‖)), ‖φ (exp (t * I))‖ₑ ∂volume := by
  sorry

/-- **Definition (7.4.4)** (§7.4; used in Theorems 7.9, 7.10; restated in Exercise 10.2.1). `h` is a bilipschitz map
of `A` into `ℂ`: `M₅⁻¹ |z₁ - z₂| ≤ |h(z₁) - h(z₂)| ≤ M₅ |z₁ - z₂|` for `z₁, z₂ ∈ A`.
Modelling: one constant `M₅ > 0` for both inequalities, as in the book (Mathlib has `LipschitzOnWith` and
`AntilipschitzWith`, but no bilipschitz predicate on a set); "of `ℂ` onto `ℂ`" adds `A = ℂ` and surjectivity. -/
def IsBilipschitzOn (h : ℂ → ℂ) (A : Set ℂ) : Prop :=
  ∃ M₅ : ℝ, 0 < M₅ ∧ ∀ z₁ ∈ A, ∀ z₂ ∈ A,
    M₅⁻¹ * ‖z₁ - z₂‖ ≤ ‖h z₁ - h z₂‖ ∧ ‖h z₁ - h z₂‖ ≤ M₅ * ‖z₁ - z₂‖

/-- **Theorem 7.9** (§7.4; Tuk80, Tuk81, JeKe82b). The curve `J` is a Lavrentiev curve if and only if there is a
bilipschitz map `h` of `ℂ` onto `ℂ` such that `J = h(𝕋)`. -/
theorem thm7_9 {J : Set ℂ} :
    IsLavrentievCurve J ↔ ∃ h : ℂ → ℂ, IsBilipschitzOn h univ ∧ Function.Surjective h ∧ J = h '' sphere 0 1 := by
  sorry

/-- **Theorem 7.10** (§7.4; Tuk80, Tuk81; cited in the proof of Theorem 7.9). Every bilipschitz map `h` of `𝕋` into
`ℂ` can be extended to a bilipschitz map of `ℂ` onto `ℂ`. -/
theorem thm7_10 {h : ℂ → ℂ} (hh : IsBilipschitzOn h (sphere 0 1)) :
    ∃ H : ℂ → ℂ, IsBilipschitzOn H univ ∧ Function.Surjective H ∧ EqOn H h (sphere 0 1) := by
  sorry

end Pommerenke1992
