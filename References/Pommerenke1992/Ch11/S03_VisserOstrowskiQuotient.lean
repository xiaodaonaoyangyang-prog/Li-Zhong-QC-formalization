import References.Pommerenke1992.Ch11.S02_AsymptoticallyConformalCurvesAndB0

/-!
# Pommerenke 1992, Ch. 11 §11.3 The Visser-Ostrowski Quotient

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 11 *Local Boundary Behaviour*, §11.3; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 2955–3205.

* Definition (well-accessible point, (11.3.1), "is called"; used in Theorem 11.3 (i), at P2 l. 3003, in the proofs
  of Theorems 11.3 and 11.5, P2 l. 2983, 3080, and in Exercise 11.3.1) — `IsWellAccessible`
* Theorem 11.3 (Pom64; "a local version of Theorem 5.2"; cited in the proof of Theorem 11.5, P2 l. 3080) — `thm11_3`
* Definition (the Visser-Ostrowski quotient, (11.3.3); used in (11.3.4), at P2 l. 2997, in the proof of Proposition
  11.4 and in Exercises 11.3.1–11.3.3) — `visserOstrowskiQuotient`
* Definition (the Visser-Ostrowski condition, (11.3.4); named at P1 l. 3415 for (4.3.8); used in Proposition 11.4,
  Theorems 11.5, 11.7, in the proofs of Theorems 11.5–11.7 and 11.9 and at P2 l. 3126, 3236) —
  `SatisfiesVisserOstrowski`
* Recalled result (P2 l. 3005: "We saw in Proposition 4.11 that `f` satisfies the Visser-Ostrowski condition (4) if
  `f` is isogonal at `ζ`"; used in the proofs of Theorems 11.6 and 11.9, P2 l. 3116, 3311) — exists:
  `Pommerenke1992.prop4_11` (its second conjunct is (4.3.8), literally the condition (11.3.4), for every finite
  angular limit of the isogonal conformal map f at ζ; the branch L of log f' that it takes exists for every conformal
  f, since f' has no zeros in the disc)
* Proposition 11.4 ("a partial local analogue of Theorem 11.1"; cited in the proof of Theorem 11.5, P2 l. 3104) —
  `prop11_4`
* Theorem 11.5 (RoWa80; Fig. 11.3) — `thm11_5`
* Theorem 11.6 (Ost36; see Fer42, War67, JenOi77; forward reference at P1 l. 3387; Exercise 11.3.6) — `thm11_6`
* Definition (the crosscut `Q(ρ)` of §11.3, P2 l. 3126, Fig. 11.4; used in Theorem 11.7; helper) —
  `radialLevelCrosscut`
* Theorem 11.7 (Ost36; see LeF55, Chapt. IV, EkWa69; "a regularity theorem that we will use in the next section";
  cited at P2 l. 3236 and in the proof of Theorem 11.9, P2 l. 3311) — `thm11_7`

Not items (DESIGN §3): the standing assumption of the section, the recall of `d_f(z) = dist(f(z), ∂G)` and "let
`M₁, M₂, …` denote suitable constants" (P2 l. 2957; conventions of §11.1, `distToBoundary` of §1.3); "Every boundary
point of a John domain is well-accessible by Corollary 5.3" and "a local version of the notion of a John domain"
(P2 l. 2965; not cited); the proof of Theorem 11.3 with (11.3.2) (Corollary 4.18, the Gehring–Hayman theorem (4.5.6),
Corollary 1.6, (5.2.8), (5.2.9)); "If `Re q(rζ) ≥ c > 0` for `r₀ ≤ r < 1` … `|f(rζ) - f(ζ)|` strictly decreases",
`diam f([rζ, ζ]) ≤ |f(rζ) - f(ζ)| ≤ c⁻¹(1 - r)|f'(rζ)|` and "`f(ζ)` is well-accessible" (P2 l. 2997–3003; not cited,
Exercise 11.3.1 is related); the remark of P2 l. 3011 ((4) holds uniformly for all `ζ ∈ 𝕋` when `∂G` is asymptotically
conformal, by Theorem 11.1 (iii); the map (11.2.6) is isogonal almost nowhere; "(4) is much weaker than
isogonality"; not cited); the proof of Proposition 11.4 (Proposition 4.8; "as in the proof of (ii) ⇒ (iii) in Theorem
11.1") and the references RoWa84, RoWa80; the proof of Theorem 11.5 with (11.3.7)–(11.3.10), "`α(λt) - α(t) → 0`" and
the kernel convergence (Theorem 1.8); the proof of Theorem 11.6; the claims of P2 l. 3126 that under (11.3.4)
`|f(rζ) - f(ζ)|` is decreasing for `r` close to `1` and that, by Proposition 2.14, the crosscut `Q(ρ)` exists and is
unique for small `ρ` (the set-up of Theorem 11.7; with `radialLevelCrosscut` its statement needs neither claim, and
the monotonicity is shown again in the proof of Theorem 11.5, P2 l. 3047); the proof of Theorem 11.7 with
(11.3.13)–(11.3.16) ((11.3.15) prints `e^{-ε} > |1 - z|/(1 - r) < e^{ε}`, crop ✓, for `<` [misprint?]); Exercises
11.3.1–11.3.6.

**Conventions.** As in §11.1. Standing assumption of §11.3 (P2 l. 2957): `f` maps `𝔻` conformally onto `G ⊆ ℂ` and
has the finite angular limit `ω = f(ζ)` at the given `ζ ∈ 𝕋`; it is explicit in every statement (`hf`, `hω`). Radial
points `rζ` are `(r : ℂ) * ζ`. "A curve `C ⊆ 𝔻` ending at `ζ`" with `f(C) : ω + te^{iα(t)}`, `0 < t ≤ t₁`, is a map
`γ : (0, t₁] → 𝔻`, continuous, with `γ(t) → ζ` as `t → 0+` and `f(γ(t)) = ω + te^{iα(t)}` (so `C` is parametrized by
`t = |f(z) - ω|`); `α` is a real function, determined modulo `2π` by `γ`, and the conditions (A), (B) see it only
through `e^{iα(t)}` (no continuity of `α` is asked). `∂G` is the frontier of `G` in `ℂ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)

/-- **Definition (11.3.1)** (§11.3, "is called"; P2 l. 2959–2965; used in Theorem 11.3 (i), at P2 l. 3003 and in the
proofs of Theorems 11.3 and 11.5). The point `f(ζ)` (`ζ ∈ 𝕋`) is well-accessible if there is a Jordan arc `C ⊆ 𝔻`
ending at `ζ` such that `diam f(C(z)) ≤ M₁ d_f(z)` for `z ∈ C`, where `C(z)` is the arc of `C` from `z` to `ζ`.
Modelling: `C` is an injective half-open curve `φ(t)`, `α ≤ t < β` (`HalfOpenCurve`, §1.1) in `𝔻` ending at `ζ`;
with its end point `ζ ∉ 𝔻` it is a Jordan arc (a continuous injective map of the compact `[α, β]`). For `z = φ(t)` the
arc `C(z)` is `φ([t, β))`; adding its end point `ζ` does not change the diameter of the image. The diameter is
`Metric.ediam` (in `ℝ≥0∞`, so an unbounded image has diameter `∞` and fails the bound). `M₁` depends on `f` and `ζ`.
The angular limit `f(ζ)` is the standing hypothesis of the statements (P2 l. 2957), not part of the definition. -/
def IsWellAccessible (f : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ M₁ : ℝ, ∃ C : HalfOpenCurve, InjOn C.toFun (Ico C.α C.β) ∧ C.toFun '' Ico C.α C.β ⊆ unitDisc ∧
    C.EndsAt (ζ : ExtPlane) ∧ ∀ t ∈ Ico C.α C.β,
      Metric.ediam (f '' (C.toFun '' Ico t C.β)) ≤ ENNReal.ofReal (M₁ * distToBoundary f (C.toFun t))

/-- **Theorem 11.3** (§11.3; Pom64; "a local version of Theorem 5.2"; P2 l. 2967–2981; cited in the proof of Theorem
11.5, P2 l. 3080). The following three conditions are equivalent:
(i) `f(ζ)` is well-accessible;
(ii) there exists `α > 0` with `|f'(ρζ)| ≤ M₂ |f'(rζ)| ((1 - ρ)/(1 - r))^{α-1}` for `0 ≤ r ≤ ρ < 1`;
(iii) there exists `α > 0` with `|f(ρζ) - f(ζ)| ≤ M₃ d_f(rζ) ((1 - ρ)/(1 - r))^α` for `0 ≤ r ≤ ρ < 1`.
Modelling: under the standing assumption of §11.3 (`f(ζ) = ω`). The constants `M₂`, `M₃` depend on `f`, `ζ` and `α`
(`∃ α > 0, ∃ M`); the powers are real powers of the positive base `(1 - ρ)/(1 - r) ∈ (0, 1]`. -/
theorem thm11_3 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) :
    List.TFAE [IsWellAccessible f ζ,
      ∃ α > (0 : ℝ), ∃ M₂ : ℝ, ∀ r ρ : ℝ, 0 ≤ r → r ≤ ρ → ρ < 1 →
        ‖deriv f (ρ * ζ)‖ ≤ M₂ * ‖deriv f (r * ζ)‖ * ((1 - ρ) / (1 - r)) ^ (α - 1),
      ∃ α > (0 : ℝ), ∃ M₃ : ℝ, ∀ r ρ : ℝ, 0 ≤ r → r ≤ ρ → ρ < 1 →
        ‖f (ρ * ζ) - ω‖ ≤ M₃ * distToBoundary f (r * ζ) * ((1 - ρ) / (1 - r)) ^ α] := by
  sorry

/-- **Definition (11.3.3)** (§11.3; P2 l. 2991–2995; used in (11.3.4), at P2 l. 2997, in the proof of Proposition 11.4
and in Exercises 11.3.1–11.3.3). The Visser-Ostrowski quotient `q(z) = (z - ζ) f'(z)/(f(z) - ω)` for `z ∈ 𝔻`.
Modelling: `ω` is the finite angular limit of the standing assumption. There is no junk on `𝔻`, where `f(z) ≠ ω`
(`ω ∈ ∂G`, §11.1); the values off `𝔻` are never used (the condition (11.3.4) looks only at Stolz angles). -/
def visserOstrowskiQuotient (f : ℂ → ℂ) (ζ ω z : ℂ) : ℂ :=
  (z - ζ) * deriv f z / (f z - ω)

/-- **Definition (11.3.4)** (§11.3; P2 l. 3005–3009; named at P1 l. 3415 for (4.3.8); used in Proposition 11.4,
Theorems 11.5 and 11.7, in the proofs of Theorems 11.5–11.7 and 11.9 and at P2 l. 3126, 3236). `f` satisfies the
Visser-Ostrowski condition at `ζ`: `q(z) = (z - ζ) f'(z)/(f(z) - ω) → 1` as `z → ζ` in every Stolz angle.
Modelling: the finite angular limit `ω` of `f` at `ζ` (unique, and the standing assumption of the section) is part of
the condition, which is then literally the form (4.3.8) of `prop4_11`. -/
def SatisfiesVisserOstrowski (f : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ ω : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω ∧
    HasAngularLimit (fun z => (visserOstrowskiQuotient f ζ ω z : ExtPlane)) ζ (1 : ℂ)

/-- **Proposition 11.4** (§11.3; "a partial local analogue of Theorem 11.1"; P2 l. 3013–3019; cited in the proof of
Theorem 11.5, P2 l. 3104). The Visser-Ostrowski condition at `ζ` is equivalent to (11.3.5)
`(z - ζ) f''(z)/f'(z) → 0` as `z → ζ` in every Stolz angle.
Modelling: under the standing assumption of §11.3; `f' ≠ 0` in `𝔻`. -/
theorem prop11_4 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) :
    SatisfiesVisserOstrowski f ζ ↔
      HasAngularLimit (fun z => ((z - ζ) * deriv (deriv f) z / deriv f z : ℂ)) ζ (0 : ℂ) := by
  sorry

/-- **Theorem 11.5** (§11.3; RoWa80; Fig. 11.3; P2 l. 3031–3043). The Visser-Ostrowski condition (11.3.4) holds at `ζ`
if and only if there is a curve `C ⊆ 𝔻` ending at `ζ` such that (11.3.6) `f(C) : ω + te^{iα(t)}`, `0 < t ≤ t₁`, and
the following conditions are both satisfied:
(A) `{w : Re[e^{-iα(t)}(w - ω)] > εt, |w - ω| < t/ε} ⊆ G` for `0 < ε < 1`, `0 < t < t₀(ε)`;
(B) there are points `ω_t^± ∈ ∂G` with `e^{-iα(t)}(ω_t^± - ω) ∼ ±it` as `t → 0`.
Modelling: under the standing assumption of §11.3; the curve is `γ : (0, t₁] → 𝔻` as in the file header. In (A),
`t₀(ε)` may be taken `≤ t₁` (it can be decreased), so `α(t)` is defined. In (B), `t ↦ ω_t^±` are functions on
`(0, t₁]`, and `∼` is `Asymptotics.IsEquivalent` along `t → 0+`. -/
theorem thm11_5 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) :
    SatisfiesVisserOstrowski f ζ ↔
      ∃ t₁ > (0 : ℝ), ∃ (γ : ℝ → ℂ) (α : ℝ → ℝ), ContinuousOn γ (Ioc 0 t₁) ∧ MapsTo γ (Ioc 0 t₁) unitDisc ∧
        Tendsto γ (𝓝[>] 0) (𝓝 ζ) ∧ (∀ t ∈ Ioc 0 t₁, f (γ t) = ω + t * exp (α t * I)) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ t₀ ∈ Ioc 0 t₁, ∀ t ∈ Ioo 0 t₀,
          {w : ℂ | ε * t < (exp (-(α t * I)) * (w - ω)).re ∧ ‖w - ω‖ < t / ε} ⊆ G) ∧
        ∃ ωp ωm : ℝ → ℂ, (∀ t ∈ Ioc 0 t₁, ωp t ∈ frontier G ∧ ωm t ∈ frontier G) ∧
          Asymptotics.IsEquivalent (𝓝[>] 0) (fun t : ℝ => exp (-(α t * I)) * (ωp t - ω)) (fun t : ℝ => I * t) ∧
          Asymptotics.IsEquivalent (𝓝[>] 0) (fun t : ℝ => exp (-(α t * I)) * (ωm t - ω))
            (fun t : ℝ => -(I * t)) := by
  sorry

/-- **Theorem 11.6** (§11.3; Ost36; see Fer42, War67, JenOi77; P2 l. 3106–3114). The function `f` is isogonal at `ζ` if
and only if there is a curve `C ⊆ 𝔻` ending at `ζ` such that (11.3.11) `f(C) : ω + te^{iα}`, `0 < t ≤ t₁`, satisfies
(A) and (B) with `α(t) ≡ α`.
Modelling: as `thm11_5`, with a constant `α`; `f(C)` is then a radial segment ending at `ω`. -/
theorem thm11_6 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) :
    IsIsogonalAt f ζ ↔
      ∃ t₁ > (0 : ℝ), ∃ (γ : ℝ → ℂ) (α : ℝ), ContinuousOn γ (Ioc 0 t₁) ∧ MapsTo γ (Ioc 0 t₁) unitDisc ∧
        Tendsto γ (𝓝[>] 0) (𝓝 ζ) ∧ (∀ t ∈ Ioc 0 t₁, f (γ t) = ω + t * exp (α * I)) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ t₀ ∈ Ioc 0 t₁, ∀ t ∈ Ioo 0 t₀,
          {w : ℂ | ε * t < (exp (-(α * I)) * (w - ω)).re ∧ ‖w - ω‖ < t / ε} ⊆ G) ∧
        ∃ ωp ωm : ℝ → ℂ, (∀ t ∈ Ioc 0 t₁, ωp t ∈ frontier G ∧ ωm t ∈ frontier G) ∧
          Asymptotics.IsEquivalent (𝓝[>] 0) (fun t : ℝ => exp (-(α * I)) * (ωp t - ω)) (fun t : ℝ => I * t) ∧
          Asymptotics.IsEquivalent (𝓝[>] 0) (fun t : ℝ => exp (-(α * I)) * (ωm t - ω))
            (fun t : ℝ => -(I * t)) := by
  sorry

/-- The crosscut `Q(ρ)` of §11.3 (P2 l. 3126, Fig. 11.4; used in Theorem 11.7; helper): for `r < 1` and
`ρ = |f(rζ) - ω|`, the component through `rζ` of `{z ∈ 𝔻 : |f(z) - ω| = ρ}`.
Modelling: the book defines `Q(ρ)`, for small `ρ > 0`, as "the unique crosscut `Q(ρ)` of `𝔻` that intersects `[0, ζ)`
and is mapped onto an arc of `∂D(f(ζ), ρ)` where `ρ = |f(rζ) - f(ζ)|`" (its existence and uniqueness come from the
Visser-Ostrowski condition and Proposition 2.14). The helper is the preimage of the component of `G ∩ ∂D(ω, ρ)`
through `f(rζ)`: an open arc of the circle (the whole circle cannot lie in the simply connected `G ∌ ω`) with end
points on `∂G`, whose preimage is a crosscut of `𝔻` through `rζ`. It is the book's `Q(ρ)` whenever that is defined,
and it is indexed by `r` instead of `ρ` (`ρ → 0` if and only if `r → 1`). -/
def radialLevelCrosscut (f : ℂ → ℂ) (ζ ω : ℂ) (r : ℝ) : Set ℂ :=
  connectedComponentIn {z | z ∈ unitDisc ∧ ‖f z - ω‖ = ‖f (r * ζ) - ω‖} (r * ζ)

/-- **Theorem 11.7** (§11.3; Ost36; see LeF55, Chapt. IV, and EkWa69; P2 l. 3128–3132; cited at P2 l. 3236 and in the
proof of Theorem 11.9, P2 l. 3311). If `f` satisfies the Visser-Ostrowski condition at `ζ` then (11.3.12)
`|ζ - z| ∼ 1 - r` as `z ∈ Q(ρ)`, `|f(rζ) - ω| = ρ → 0`.
Modelling: under the standing assumption of §11.3; `Q(ρ)` is `radialLevelCrosscut f ζ ω r`. "`ρ → 0`" is "`r → 1-`":
`ρ(r) = |f(rζ) - ω|` is positive and continuous on `[0, 1)` with limit `0` at `1` (the radial limit is `ω`), so it is
bounded below on every `[0, r₁]`, `r₁ < 1`. The asymptotic equality is uniform on `Q(ρ)`: for every `ε > 0`, `r` close
to `1` and every `z ∈ Q(ρ)`, `||ζ - z|/(1 - r) - 1| < ε`. -/
theorem thm11_7 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {ζ ω : ℂ}
    (hω : HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω) (hVO : SatisfiesVisserOstrowski f ζ) :
    ∀ ε > (0 : ℝ), ∃ r₀ < (1 : ℝ), ∀ r : ℝ, r₀ < r → r < 1 → ∀ z ∈ radialLevelCrosscut f ζ ω r,
      |‖ζ - z‖ / (1 - r) - 1| < ε := by
  sorry

end Pommerenke1992
