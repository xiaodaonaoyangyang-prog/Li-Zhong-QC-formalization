import References.Lehto1987.Ch02.S03_ConformalMappingsWithQuasiconformalExtensions

/-!
# Lehto, Chapter II §4: Univalence and quasiconformal extensibility of meromorphic functions

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. II §4 (`full.md`
P1:2972–3249).

Conventions (see §1, §3 and the root file). Quasiconformal reflections are `IsKQCReflection` (I.6.2), quasicircles
and quasidiscs are `LiZhongQC.IsKQuasicircle`, `IsKQuasidiscExt`, `References.IsQuasidiskExt`. "`f` meromorphic in
`A` with `‖S_f‖_A` small" presupposes that `f` is locally injective (otherwise `S_f` has poles and the norm is
infinite; root Corrections, reading (4)): `IsLocUnivMeroExt f A`. "Univalent in `A`" is `Gehring1978.IsConformalExt`.
Linear local connectivity is the project's `LiZhongQC.IsKLocallyConnected` (I.6.4), for domains of the finite plane.
`|dψ(z)/dz|` for a reflection `ψ` is the norm of its real derivative (the largest stretching, as in (6.4) of I.6.2).

* Formula (4.1) (§4.1) — omitted: an invariance used only to extend (4.2) to all reflections
* Formula (4.2) (§4.1) — `eq2_4_2`
* Formula (4.3) (§4.1) — omitted: an invariance used only for (4.4)
* Unlabelled (§4.1, P1:3030–3038): the estimate (4.4) for a suitable reflection in a `K`-quasicircle — `para2_4_1`
* Theorem 4.1 (§4.2, Ahlfors) — `thm2_4_1`
* Formula (4.7)–(4.9) (§4.2–§4.3) — omitted: steps of the proof of Theorem 4.1
* Definition (Schwarzian domain, `ε`-Schwarzian domain, §4.4, Gehring) — `IsEpsSchwarzianDomain`,
  `IsSchwarzianDomain`
* Lemma 4.1 (§4.5) — `lemma2_4_1`
* Formula (4.11)–(4.14) (§4.5) — omitted: steps of the proof of Lemma 4.1
* Theorem 4.2 (§4.6, Gehring) — `thm2_4_2`
* Formula (4.15), (4.16) and "`K(a)`" (§4.6) — omitted: steps of the proof of Theorem 4.2
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt schwarzian IsKQuasicircle IsKLocallyConnected)
open References (finitePart IsQuasidiskExt)
open LehtoVirtanen1973 (complexDilatationLV finiteMap finiteValue JordanCurveBounds)
open Gehring1978 (hypNorm IsHypSimplyConnectedExt IsConformalExt)

/-! ## §4.1 Quasiconformal reflections under Möbius transformations -/

/-- **Formula (4.2)** (Ch. II §4.1). For every `K`-quasiconformal reflection `ψ` in a quasicircle `C` and every finite
point `z₀ ∈ C`, `limsup_{z → z₀} |ψ(z) − z₀|/|z − z₀| ≤ c₁(K)`, with a finite constant `c₁(K)` depending only on `K`
(the book proves it for `C ∋ ∞` from (6.2) of I.6.2 and transfers it to all reflections by the invariance (4.1)).
Modelling: `∀ K, ∃ c₁`; the `limsup` over the punctured neighbourhoods of `z₀` is taken in `[0, ∞]` (`ψ` is finite
near the finite point `ψ(z₀) = z₀`). -/
theorem eq2_4_2 (K : ℝ) :
    ∃ c : ℝ, ∀ (C A₁ A₂ : Set ExtPlane) (ψ : ExtPlane → ExtPlane), IsKQCReflection C A₁ A₂ K ψ →
      ∀ z₀ : ℂ, (z₀ : ExtPlane) ∈ C →
        limsup (fun z : ℂ => ENNReal.ofReal (‖finiteValue (ψ z) - z₀‖ / ‖z - z₀‖)) (𝓝[≠] z₀) ≤
          ENNReal.ofReal c := by
  sorry

/-- **Unlabelled** (Ch. II §4.1, P1:3030–3038). Let `C` be a `K`-quasicircle bounding the domains `A₁` and `A₂`. There
exists a quasiconformal reflection `ψ` in `C` such that, for every function `f` meromorphic and locally injective in
`A₂`, `|ψ(z) − z|² |dψ(z)/dz| |S_f(ψ(z))| ≤ c(K) ‖S_f‖_{A₂}` (4.4) at each point `z ∈ A₁`, `z ≠ ∞, ψ⁻¹(∞)`, where the
finite constant `c(K)` depends only on `K`.
Modelling: `∀ K, ∃ c`; `ψ` is a quasiconformal reflection with some constant, continuously differentiable at the finite
points of `A₁` with finite image (the book's `ψ` is smooth off `C`), and `|dψ/dz|` is the norm of its real
derivative; the inequality is taken in `[0, ∞]`. -/
theorem para2_4_1 (K : ℝ) :
    ∃ c : ℝ, ∀ C A₁ A₂ : Set ExtPlane, IsKQuasicircle C K → JordanCurveBounds C A₁ A₂ →
      ∃ ψ : ExtPlane → ExtPlane, (∃ K' : ℝ, IsKQCReflection C A₁ A₂ K' ψ) ∧
        ContDiffOn ℝ 1 (finiteMap ψ) {z : ℂ | (z : ExtPlane) ∈ A₁ ∧ ψ z ≠ extInf} ∧
        ∀ f : ℂ → ℂ, IsLocUnivMeroExt f A₂ → ∀ z : ℂ, (z : ExtPlane) ∈ A₁ → ψ z ≠ extInf →
          ENNReal.ofReal (‖finiteValue (ψ z) - z‖ ^ 2 * ‖fderiv ℝ (finiteMap ψ) z‖ *
            ‖schwarzian f (finiteValue (ψ z))‖) ≤ ENNReal.ofReal c * hypNorm (schwarzian f) A₂ := by
  sorry

/-! ## §4.2 Quasiconformal extension of conformal mappings -/

/-- **Theorem 4.1** (Ch. II §4.2, Ahlfors). Let `A` be a `K`-quasidisc. Then there is a constant `ε(K) > 0`, depending
only on `K`, such that every function `f` meromorphic in `A` with `‖S_f‖_A < ε(K)` (4.5) is univalent in `A` and can be
extended to a quasiconformal mapping of the plane whose complex dilatation satisfies `‖μ‖∞ ≤ ‖S_f‖_A / ε(K)` (4.6).
Modelling: `∀ K, ∃ ε > 0, ∀ A f`; `f` is locally injective meromorphic in `A` (module docstring); the extension is
`IsQCExtensionOf`; (4.6) is taken in `[0, ∞]`. -/
theorem thm2_4_1 (K : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (A : Set ExtPlane) (f : ℂ → ℂ), IsKQuasidiscExt A K → IsLocUnivMeroExt f A →
      hypNorm (schwarzian f) A < ENNReal.ofReal ε →
        IsConformalExt f A ∧ ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f A ∧
          eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume ≤ hypNorm (schwarzian f) A / ENNReal.ofReal ε := by
  sorry

/-! ## §4.4 Definition of Schwarzian domains -/

/-- **Definition** (`ε`-Schwarzian domain, Ch. II §4.4, Gehring). A simply connected domain `A` with more than one
boundary point such that every meromorphic function `f` with `‖S_f‖_A ≤ ε` is univalent in `A`.
Modelling: `f` ranges over the locally injective meromorphic functions (module docstring). -/
def IsEpsSchwarzianDomain (A : Set ExtPlane) (ε : ℝ) : Prop :=
  IsHypSimplyConnectedExt A ∧
    ∀ f : ℂ → ℂ, IsLocUnivMeroExt f A → hypNorm (schwarzian f) A ≤ ENNReal.ofReal ε → IsConformalExt f A

/-- **Definition** (Schwarzian domain, Ch. II §4.4): an `ε`-Schwarzian domain for some `ε > 0`. -/
def IsSchwarzianDomain (A : Set ExtPlane) : Prop := ∃ ε : ℝ, 0 < ε ∧ IsEpsSchwarzianDomain A ε

/-! ## §4.5 Domains not linearly locally connected -/

/-- **Lemma 4.1** (Ch. II §4.5). Let `A` be a simply connected domain which is not linearly locally connected for a
constant `c > 1`. Then there are two distinct points `z₁ ≠ z₂` of `A` and two distinct finite points `w₁ ≠ w₂` outside `A` such that the
function `h(z) = log((z − w₁)/(z − w₂))` satisfies `|h(z₁) − h(z₂) − 2πi| ≤ 4/(c − 1)` (4.10).
Modelling: `A` is a simply connected domain of the finite plane with more than one boundary point (§4.4–§4.6); `h` is
a continuous branch of the logarithm in `A` (it exists, `A` being simply connected and `w₁, w₂ ∉ A`; the difference
`h(z₁) − h(z₂)` does not depend on the branch). *Correction (audit):* `w₁ ≠ w₂` and `z₁ ≠ z₂` are required; for `w₁ = w₂` the function `h` is constant and
the conclusion is trivial for `1 < c ≤ 1 + 2/π`. -/
theorem lemma2_4_1 {A : Set ℂ} (hA : IsHypSimplyConnectedExt (toExt A)) {c : ℝ} (hc : 1 < c)
    (hnot : ¬ IsKLocallyConnected A c) :
    ∃ z₁ ∈ A, ∃ z₂ ∈ A, z₁ ≠ z₂ ∧ ∃ w₁ w₂ : ℂ, w₁ ∉ A ∧ w₂ ∉ A ∧ w₁ ≠ w₂ ∧ ∃ h : ℂ → ℂ, ContinuousOn h A ∧
      (∀ z ∈ A, Complex.exp (h z) = (z - w₁) / (z - w₂)) ∧
      ‖h z₁ - h z₂ - 2 * Real.pi * I‖ ≤ 4 / (c - 1) := by
  sorry

/-! ## §4.6 Schwarzian domains and quasidiscs -/

/-- **Theorem 4.2** (Ch. II §4.6, Gehring). A Schwarzian domain is a quasidisc. -/
theorem thm2_4_2 {A : Set ExtPlane} (hA : IsSchwarzianDomain A) : IsQuasidiskExt A := by
  sorry

end Lehto1987
