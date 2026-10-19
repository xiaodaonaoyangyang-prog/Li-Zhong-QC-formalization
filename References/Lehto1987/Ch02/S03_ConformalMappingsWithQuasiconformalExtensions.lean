import References.Lehto1987.Ch02.S02_DistanceBetweenSimplyConnectedDomains

/-!
# Lehto, Chapter II §3: Conformal mappings with quasiconformal extensions

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. II §3 (`full.md`
P1:2553–2971).

Conventions (see §1 and the root file). A quasiconformal mapping of the plane is LV's
`LehtoVirtanen1973.IsQuasiconformalMap F univ` with `F : ℂ̄ → ℂ̄`; its complex dilatation is LV's
`complexDilatationLV F`, read at the finite points (the point `∞` is null), and `‖μ‖∞` is
`MeasureTheory.eLpNorm μ ⊤ volume`. Such an `F` *extends* a meromorphic `f` given in a domain `A` of `ℂ̄` when it
agrees with `f` (read in `ℂ̄`, `LiZhongQC.meroToExt`) at the finite points of `A` (`IsQCExtensionOf`). The book's
mapping `z ↦ f(z, w)` "with complex dilatation `wμ` and `f(z, w) − z → 0` as `z → ∞`" is stated relationally: the
statements hold for every family `F w` of such normalized solutions (`IsNormalizedSolutionLV`; they exist and are
unique by Theorems I.4.4 and I.4.2). The disc `|w| < 1/‖μ‖∞` is written `‖w‖ ‖μ‖∞ < 1` (all of `ℂ` when `μ = 0`).
The class `Σ` is `IsClassSigma0` (§1.5), its coefficients `bₙ` are Pommerenke's `sigmaCoeff`, and
`E = {|z| > 1}` is `exteriorDiscE`.

Helpers (not book notions): `IsQCExtensionOf`, `IsNormalizedSolutionLV`, `sigmaData` (the finitely many data on which
an analytic functional depends).

* Theorem 3.1 (§3.2) — `thm2_3_1_i`, `thm2_3_1_ii`
* Unlabelled (§3.2, P1:2609): the coefficients `bₙ(w)` of `z ↦ f(z, w)` at `∞` depend holomorphically on `w` —
  `para2_3_2`
* Corollary 3.1 (§3.2) — `cor2_3_1_i`, `cor2_3_1_ii`
* Remark (§3.2, P1:2661–2671): the dilatation `wμ` may be replaced by `wμ + ν` — `rem2_3_2_i`, `rem2_3_2_ii`
* Theorem 3.2 (§3.3) — `thm2_3_2`
* Unlabelled (§3.3, P1:2703–2715): the disc case `‖S_{f|A}‖ ≤ 6‖μ‖∞` (Kühnau, Lehto), sharp by (3.3) —
  `para2_3_3`
* Theorem 3.3 (§3.3) — `thm2_3_3`
* Unlabelled (§3.3, P1:2727): the sharp bound in (3.4) is unknown and at least `6(K − 1)/(K + 1)` — omitted: a
  remark, not cited
* Definition (class `Σ_k`, §3.4) — `IsClassSigmaK`
* Theorem 3.4 (§3.4) — `thm2_3_4`
* Corollary 3.2 (§3.4) — `cor2_3_2_i`, `cor2_3_2_ii`
* Unlabelled (§3.4, P1:2785–2789): `|f(0)| ≤ 2k` in `Σ_k`, with the extremal mappings (Kühnau, Lehto) — omitted:
  quoted, not cited
* Theorem 3.5 (§3.4) — `thm2_3_5_i`, `thm2_3_5_ii`
* Unlabelled (§3.5, P1:2859–2864): (3.12) `|f(z) − z| ≤ 1/(|z| − 1)` in `Σ`; `Σ` and every `Σ_k` are closed normal
  families — `para2_3_5`
* Definition (continuous functional, analytic functional, `M(k)`, §3.5) — `IsContinuousFunctional`,
  `IsAnalyticFunctionalSigma`, `majorantM`
* Unlabelled (§3.5, P1:2868): extremal functions for `|Φ|` exist in `Σ_k` — omitted: used only to write `M(k)` as a
  maximum (here a supremum)
* Theorem 3.6 (§3.5) — `thm2_3_6`
* Corollary 3.3 (§3.5, Majorant principle) — `cor2_3_3_i`, `cor2_3_3_ii`
* Formula (3.15) and the values `max |b₁| = k`, `max |b₂| = 2k/3` (§3.6) — omitted: instances of (3.13), not cited
  [misprint: "`a_n = 2k/(n + 1)` for the extremal (3.16) in Theorem 3.4" (P1:2920) reads `bₙ` and (3.10) in
  Theorem 3.5; a remark]
* Theorem 3.7 (§3.6) — `thm2_3_7`, `thm2_3_7_sharp`
* Formula (3.17) (§3.6) — omitted: a step of the proof of Theorem 3.7
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt unitDisc upperHalf schwarzian meroToExt)
open References (finitePart)
open LehtoVirtanen1973 (IsQuasiconformalMap complexDilatationLV finiteMap)
open Gehring1978 (hypNorm IsHypSimplyConnectedExt IsConformalExt)

/-! ## §3.2 Dependence of a mapping on its complex dilatation -/

/-- Helper. `F` is a quasiconformal extension to `ℂ̄` of the meromorphic function `f` given in the domain `A`: a
quasiconformal mapping of the plane which agrees with `f` (read in `ℂ̄`) at the finite points of `A`. (At `∞ ∈ A`,
continuity of `F` fixes its value.) -/
def IsQCExtensionOf (F : ExtPlane → ExtPlane) (f : ℂ → ℂ) (A : Set ExtPlane) : Prop :=
  IsQuasiconformalMap F univ ∧ ∀ z ∈ finitePart A, F z = meroToExt f z

/-- Helper. `F` is the normalized solution with complex dilatation `μ` (Theorem 3.1, Theorem I.4.3): a
quasiconformal mapping of the plane whose complex dilatation is `μ` almost everywhere, which fixes `∞`, and for
which `F(z) − z → 0` as `z → ∞`. -/
def IsNormalizedSolutionLV (F : ExtPlane → ExtPlane) (μ : ℂ → ℂ) : Prop :=
  IsQuasiconformalMap F univ ∧ (∀ᵐ z : ℂ, complexDilatationLV F z = μ z) ∧ F extInf = extInf ∧
    Tendsto (fun z : ℂ => finiteMap F z - z) (cocompact ℂ) (𝓝 0)

/-- **Theorem 3.1** (Ch. II §3.2), first part. Let `μ` be a measurable function in the plane with bounded support and
`‖μ‖∞ < 1`, and let `z ↦ f(z, w)` be the quasiconformal mapping of the plane with complex dilatation `wμ` and
`lim (f(z, w) − z) = 0` as `z → ∞`. Then, for every fixed `z ≠ ∞`, the function `w ↦ f(z, w)` is holomorphic in the
disc `|w| < 1/‖μ‖∞`.
Modelling: relational (see the module docstring); `F w` is given for the `w` of the disc. -/
theorem thm2_3_1_i {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1)
    (hsupp : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → μ z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 → IsNormalizedSolutionLV (F w) fun z => w * μ z)
    (z : ℂ) :
    DifferentiableOn ℂ (fun w => finiteMap (F w) z) {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1} := by
  sorry

/-- **Theorem 3.1** (Ch. II §3.2), second part. For every fixed `z` outside the support of `μ`, the derivatives of the
analytic function `z ↦ f(z, w)` depend holomorphically on `w` for `|w| < 1/‖μ‖∞`.
Modelling: as in `thm2_3_1_i`; "outside the support" means that `μ = 0` a.e. in a neighbourhood of `z`; the
derivatives are the iterated complex derivatives at `z`. -/
theorem thm2_3_1_ii {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1)
    (hsupp : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → μ z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 → IsNormalizedSolutionLV (F w) fun z => w * μ z)
    {z : ℂ} (hz : ∃ U ∈ 𝓝 z, ∀ᵐ ζ ∂(volume.restrict U), μ ζ = 0) (n : ℕ) :
    DifferentiableOn ℂ (fun w => iteratedDeriv n (finiteMap (F w)) z)
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1} := by
  sorry

/-- **Unlabelled** (Ch. II §3.2, P1:2609). In the situation of Theorem 3.1, let `f(z, w) = z + Σ_{n ≥ 1} bₙ(w) z⁻ⁿ`
in a neighbourhood of `∞`. Then the coefficients `w ↦ bₙ(w)` are holomorphic in `|w| < 1/‖μ‖∞`.
Modelling: `μ` vanishes outside `|z| ≤ R`, where `z ↦ f(z, w)` is holomorphic; `bₙ(w)` is its Laurent coefficient at
`∞`, `bₙ(w) = (2πi)⁻¹ ∮_{|ζ| = R + 1} f(ζ, w) ζ^{n − 1} dζ`. -/
theorem para2_3_2 {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 → IsNormalizedSolutionLV (F w) fun z => w * μ z)
    {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ
      (fun w => (2 * Real.pi * I)⁻¹ * circleIntegral (fun ζ => finiteMap (F w) ζ * ζ ^ ((n : ℤ) - 1)) 0 (R + 1))
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1} := by
  sorry

/-- **Corollary 3.1** (Ch. II §3.2), first part. Let `μ` be a measurable function in the plane which vanishes in the
upper half-plane and for which `‖μ‖∞ < 1`. Let `f_{wμ}` be the quasiconformal mapping of the plane with complex
dilatation `wμ` which keeps the points `0, 1, ∞` fixed. Then `w ↦ f_{wμ}(z)` is holomorphic in `|w| < 1/‖μ‖∞` for
every finite `z`.
Modelling: relational, as in Theorem 3.1. -/
theorem cor2_3_1_i {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1)
    (hH : ∀ z ∈ upperHalf, μ z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 → IsQuasiconformalMap (F w) univ ∧
      (∀ᵐ z : ℂ, complexDilatationLV (F w) z = w * μ z) ∧ F w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      F w ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ F w extInf = extInf)
    (z : ℂ) :
    DifferentiableOn ℂ (fun w => finiteMap (F w) z) {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1} := by
  sorry

/-- **Corollary 3.1** (Ch. II §3.2), second part (P1:2655). For every `z` in the upper half-plane, the derivatives of
`z ↦ f_{wμ}(z)` depend holomorphically on `w` in the disc `|w| < 1/‖μ‖∞`.
Modelling: as in `cor2_3_1_i`; the derivatives are the iterated complex derivatives at `z`. -/
theorem cor2_3_1_ii {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1)
    (hH : ∀ z ∈ upperHalf, μ z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 → IsQuasiconformalMap (F w) univ ∧
      (∀ᵐ z : ℂ, complexDilatationLV (F w) z = w * μ z) ∧ F w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      F w ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ F w extInf = extInf)
    {z : ℂ} (hz : z ∈ upperHalf) (n : ℕ) :
    DifferentiableOn ℂ (fun w => iteratedDeriv n (finiteMap (F w)) z)
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1} := by
  sorry

/-- **Remark** (Ch. II §3.2, P1:2661–2667). Let `μ` and `ν` be measurable, vanish outside a disc, and satisfy
`‖μ‖∞ < 1`, `‖ν‖∞ < 1`. Then for every finite `z`, the function `w ↦ f(z, wμ + ν)` is holomorphic in the disc
`|w| < (1 − ‖ν‖∞)/‖μ‖∞`.
Modelling: `f(·, wμ + ν)` is the normalized solution with complex dilatation `wμ + ν` (relational, as in
Theorem 3.1); the disc is `‖w‖ ‖μ‖∞ < 1 − ‖ν‖∞`. -/
theorem rem2_3_2_i {μ ν : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hνm : AEStronglyMeasurable ν volume)
    (hμ : eLpNorm μ ⊤ volume < 1) (hν : eLpNorm ν ⊤ volume < 1)
    (hsupp : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → μ z = 0 ∧ ν z = 0) {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 - (eLpNorm ν ⊤ volume).toReal →
      IsNormalizedSolutionLV (F w) fun z => w * μ z + ν z)
    (z : ℂ) :
    DifferentiableOn ℂ (fun w => finiteMap (F w) z)
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 - (eLpNorm ν ⊤ volume).toReal} := by
  sorry

/-- **Remark** (Ch. II §3.2, P1:2669–2671). In Corollary 3.1 the complex dilatation `wμ` can be replaced by `wμ + ν`:
if `μ` and `ν` vanish in the upper half-plane and `‖μ‖∞, ‖ν‖∞ < 1`, and `f_{wμ+ν}` fixes `0, 1, ∞`, then
`w ↦ f_{wμ+ν}(z)` is holomorphic in `|w| < (1 − ‖ν‖∞)/‖μ‖∞` for every finite `z`, and so are the derivatives of
`z ↦ f_{wμ+ν}(z)` at the points of the upper half-plane.
Modelling: relational, as in Corollary 3.1. -/
theorem rem2_3_2_ii {μ ν : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hνm : AEStronglyMeasurable ν volume)
    (hμ : eLpNorm μ ⊤ volume < 1) (hν : eLpNorm ν ⊤ volume < 1) (hH : ∀ z ∈ upperHalf, μ z = 0 ∧ ν z = 0)
    {F : ℂ → ExtPlane → ExtPlane}
    (hF : ∀ w : ℂ, ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 - (eLpNorm ν ⊤ volume).toReal →
      IsQuasiconformalMap (F w) univ ∧ (∀ᵐ z : ℂ, complexDilatationLV (F w) z = w * μ z + ν z) ∧
      F w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ F w ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
      F w extInf = extInf) :
    (∀ z : ℂ, DifferentiableOn ℂ (fun w => finiteMap (F w) z)
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 - (eLpNorm ν ⊤ volume).toReal}) ∧
    ∀ z ∈ upperHalf, ∀ n : ℕ, DifferentiableOn ℂ (fun w => iteratedDeriv n (finiteMap (F w)) z)
      {w : ℂ | ‖w‖ * (eLpNorm μ ⊤ volume).toReal < 1 - (eLpNorm ν ⊤ volume).toReal} := by
  sorry

/-! ## §3.3 Schwarzian derivatives and complex dilatations -/

/-- **Theorem 3.2** (Ch. II §3.3). Let `f` be a quasiconformal mapping of the plane which has the complex dilatation
`μ` and which is conformal in a simply connected domain `A` with at least two boundary points. Then
`‖S_{f|A}‖_A ≤ σ₀(A) ‖μ‖∞` (3.2).
Modelling: the mapping of the plane is `F`, and `f|A` is a function `f` conformal in `A` (`IsConformalExt`) which `F`
extends; the product is taken in `[0, ∞]` (`σ₀(A) ≤ 12` is finite, Theorem 2.4). [OCR] `‖μ‖∞` is printed
`‖_İ‖_α`. -/
theorem thm2_3_2 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {F : ExtPlane → ExtPlane} {f : ℂ → ℂ}
    (hF : IsQCExtensionOf F f A) (hf : IsConformalExt f A) :
    hypNorm (schwarzian f) A ≤ outerRadiusUniv A * eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume := by
  sorry

/-- **Unlabelled** (Ch. II §3.3, P1:2703–2715, Kühnau, Lehto). If `A` is a disc, (3.2) takes the form
`‖S_{f|A}‖ ≤ 6 ‖μ‖∞`. The bound is sharp: for each `k`, `0 ≤ k < 1`, the function `z + k/z` of `A = {|z| > 1}` has
an extension (3.3) with `‖μ‖∞ = k` and `‖S_{f|A}‖ = 6k`.
Modelling: the extension (3.3), `z + k z̄` in `|z| ≤ 1`, is asserted to exist with these properties. -/
theorem para2_3_3 :
    (∀ (A : Set ExtPlane) (F : ExtPlane → ExtPlane) (f : ℂ → ℂ), IsDiscExt A → IsQCExtensionOf F f A →
      IsConformalExt f A →
        hypNorm (schwarzian f) A ≤ 6 * eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume) ∧
    ∀ k : ℝ, 0 ≤ k → k < 1 → ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F (fun z => z + k / z) exteriorDiscE ∧
      eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume = ENNReal.ofReal k ∧
      hypNorm (schwarzian fun z : ℂ => z + k / z) exteriorDiscE = ENNReal.ofReal (6 * k) := by
  sorry

/-- **Theorem 3.3** (Ch. II §3.3). If `A` is a `K`-quasidisc, then `δ(A) ≤ 6 (K² − 1)/(K² + 1)` (3.4). -/
theorem thm2_3_3 {A : Set ExtPlane} {K : ℝ} (hA : IsKQuasidiscExt A K) :
    discDistance A ≤ ENNReal.ofReal (6 * (K ^ 2 - 1) / (K ^ 2 + 1)) := by
  sorry

/-! ## §3.4 Asymptotic estimates -/

/-- **Definition** (class `Σ_k`, Ch. II §3.4): the functions `f ∈ Σ` with a quasiconformal extension to the plane
whose complex dilatation satisfies `‖μ‖∞ ≤ k`. -/
def IsClassSigmaK (g : ℂ → ℂ) (k : ℝ) : Prop :=
  IsClassSigma0 g ∧ ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F g exteriorDiscE ∧
    eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume ≤ ENNReal.ofReal k

/-- **Theorem 3.4** (Ch. II §3.4). Let `f ∈ Σ_k` and `k < k₀ < 1`. As `k → 0`,
`f(z) = z − (1/π) ∬_D μ(ζ)/(ζ − z) dξ dη + O(k²)` (3.6) in the whole plane, where `|O(k²)| ≤ c k²`, the constant `c`
depending only on `k₀`.
Modelling: `∀ k₀ < 1, ∃ c`; `f` in the whole plane is its extension `F` (any extension with `‖μ‖∞ ≤ k`), `μ` its
complex dilatation, `D` the unit disc. -/
theorem thm2_3_4 {k₀ : ℝ} (hk₀ : k₀ < 1) :
    ∃ c : ℝ, ∀ (k : ℝ) (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), 0 ≤ k → k < k₀ → IsClassSigma0 f →
      IsQCExtensionOf F f exteriorDiscE →
      eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume ≤ ENNReal.ofReal k → ∀ z : ℂ,
        ‖finiteMap F z - z + ((1 / Real.pi : ℝ) : ℂ) * ∫ ζ : ℂ in unitDisc, complexDilatationLV F ζ / (ζ - z)‖ ≤
          c * k ^ 2 := by
  sorry

/-- **Corollary 3.2** (Ch. II §3.4), first part. The functions `f ∈ Σ_k` satisfy the asymptotic inequality
`|f(z) − z| ≤ (k/π) ∬_D dξ dη/|ζ − z| + c k²` (3.7).
Modelling: as in `thm2_3_4`, with the constant `c = c(k₀)` of Theorem 3.4. -/
theorem cor2_3_2_i {k₀ : ℝ} (hk₀ : k₀ < 1) :
    ∃ c : ℝ, ∀ (k : ℝ) (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), 0 ≤ k → k < k₀ → IsClassSigma0 f →
      IsQCExtensionOf F f exteriorDiscE →
      eLpNorm (fun z : ℂ => complexDilatationLV F z) ⊤ volume ≤ ENNReal.ofReal k → ∀ z : ℂ,
        ‖finiteMap F z - z‖ ≤ k / Real.pi * (∫ ζ in unitDisc, 1 / ‖ζ - z‖) + c * k ^ 2 := by
  sorry

/-- **Corollary 3.2** (Ch. II §3.4), second part. If `μ(ζ) = k e^{iθ} (ζ − z)/|ζ − z|` a.e. (3.8), then
`|f(z) − z| = (k/π) ∬_D dξ dη/|ζ − z| + O(k²)`.
Modelling: (3.8) holds a.e. in `D` for the fixed point `z` (outside `D` the extension is conformal); `|O(k²)| ≤ c k²`
with `c = c(k₀)`. -/
theorem cor2_3_2_ii {k₀ : ℝ} (hk₀ : k₀ < 1) :
    ∃ c : ℝ, ∀ (k θ : ℝ) (z : ℂ) (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), 0 ≤ k → k < k₀ → IsClassSigma0 f →
      IsQCExtensionOf F f exteriorDiscE →
      (∀ᵐ ζ : ℂ ∂(volume.restrict unitDisc),
        complexDilatationLV F ζ = (k : ℂ) * Complex.exp (θ * I) * ((ζ - z) / (‖ζ - z‖ : ℂ))) →
      |‖finiteMap F z - z‖ - k / Real.pi * ∫ ζ in unitDisc, 1 / ‖ζ - z‖| ≤ c * k ^ 2 := by
  sorry

/-- **Theorem 3.5** (Ch. II §3.4), first part. In the class `Σ_k`, `|bₙ| ≤ 2k/(n + 1) + c k²`, `n = 1, 2, …` (3.9),
with `c ≤ n^{−1/2} (1 − k)^{−1}`.
Modelling: `0 ≤ k < 1`; the bound is stated with `c = n^{−1/2}(1 − k)^{−1}`. -/
theorem thm2_3_5_i {f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hf : IsClassSigmaK f k) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖Pommerenke1992.sigmaCoeff f n‖ ≤ 2 * k / (n + 1) + k ^ 2 / (Real.sqrt n * (1 - k)) := by
  sorry

/-- **Theorem 3.5** (Ch. II §3.4), second part. The function `fₙ` of (3.10),
`fₙ(z) = (z^{(n+1)/2} + k z^{−(n+1)/2})^{2/(n+1)}` in `|z| > 1`, belongs to `Σ_k`, and `bₙ = 2k/(n + 1)`.
Modelling: `0 ≤ k < 1`, `n ≥ 1`; the branch of `fₙ` is the one asymptotic to `z` at `∞`, i.e. `fₙ ∈ Σ` with
`fₙ(z)^{n+1} = z^{n+1} + 2k + k² z^{−(n+1)}`, which determines it. -/
theorem thm2_3_5_ii {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : ℂ → ℂ, IsClassSigmaK f k ∧
      (∀ z : ℂ, 1 < ‖z‖ → f z ^ (n + 1) = z ^ (n + 1) + 2 * k + (k : ℂ) ^ 2 / z ^ (n + 1)) ∧
      Pommerenke1992.sigmaCoeff f n = 2 * k / (n + 1) := by
  sorry

/-! ## §3.5 Majorant principle -/

/-- **Unlabelled** (Ch. II §3.5, P1:2859–2864). For `f ∈ Σ`, `|f(z) − z| ≤ 1/(|z| − 1)` (3.12) in `|z| > 1`; `Σ` is a
closed normal family, and so is every `Σ_k`.
Modelling: "closed normal family": every sequence of the class has a subsequence converging locally uniformly in
`|z| > 1` to a member of the class; `0 ≤ k < 1`. -/
theorem para2_3_5 :
    (∀ f : ℂ → ℂ, IsClassSigma0 f → ∀ z : ℂ, 1 < ‖z‖ → ‖f z - z‖ ≤ 1 / (‖z‖ - 1)) ∧
    (∀ fn : ℕ → ℂ → ℂ, (∀ n, IsClassSigma0 (fn n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, IsClassSigma0 f ∧
      TendstoLocallyUniformlyOn (fun n => fn (φ n)) f atTop {z : ℂ | 1 < ‖z‖}) ∧
    ∀ (k : ℝ) (fn : ℕ → ℂ → ℂ), 0 ≤ k → k < 1 → (∀ n, IsClassSigmaK (fn n) k) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ℂ → ℂ, IsClassSigmaK f k ∧ TendstoLocallyUniformlyOn (fun n => fn (φ n)) f atTop {z : ℂ | 1 < ‖z‖} := by
  sorry

/-- **Definition** (continuous functional on `Σ`, Ch. II §3.5): `Φ(fₙ) → Φ(f)` whenever `fₙ → f` locally uniformly
in `E`, for `fₙ, f ∈ Σ`. -/
def IsContinuousFunctional (Φ : (ℂ → ℂ) → ℂ) : Prop :=
  ∀ (fn : ℕ → ℂ → ℂ) (f : ℂ → ℂ), (∀ n, IsClassSigma0 (fn n)) → IsClassSigma0 f →
    TendstoLocallyUniformlyOn fn f atTop {z : ℂ | 1 < ‖z‖} → Tendsto (fun n => Φ (fn n)) atTop (𝓝 (Φ f))

/-- Helper: the finitely many data of `f` on which an analytic functional depends: the coefficients `b₁, …, b_N`
and the values `f^{(l)}(zⱼ)`, `0 ≤ l ≤ m`, at the points `z₁, …, z_p`. -/
def sigmaData (N p m : ℕ) (pts : Fin p → ℂ) (f : ℂ → ℂ) : Fin N ⊕ (Fin p × Fin (m + 1)) → ℂ :=
  Sum.elim (fun j => Pommerenke1992.sigmaCoeff f (j + 1)) fun q => iteratedDeriv q.2 f (pts q.1)

/-- **Definition** (analytic functional on `Σ`, Ch. II §3.5): `Φ(f)` is a holomorphic function of finitely many of
the coefficients of `f` and of the values of `f, f′, …, f^{(m)}` at finitely many given points of `E`.
Modelling: `Φ(f) = G(data of f)` for every `f ∈ Σ`, where `G` is holomorphic (complex differentiable) in an open set
`U` of the data space containing the data of every `f ∈ Σ`. -/
def IsAnalyticFunctionalSigma (Φ : (ℂ → ℂ) → ℂ) : Prop :=
  ∃ (N p m : ℕ) (pts : Fin p → ℂ) (U : Set (Fin N ⊕ (Fin p × Fin (m + 1)) → ℂ))
    (G : (Fin N ⊕ (Fin p × Fin (m + 1)) → ℂ) → ℂ),
    (∀ j, 1 < ‖pts j‖) ∧ IsOpen U ∧ DifferentiableOn ℂ G U ∧
      ∀ f : ℂ → ℂ, IsClassSigma0 f → sigmaData N p m pts f ∈ U ∧ Φ f = G (sigmaData N p m pts f)

/-- **Definition** (`M(k) = max_{f ∈ Σ_k} |Φ(f)|`, Ch. II §3.5), as a supremum in `[0, ∞]`. -/
def majorantM (Φ : (ℂ → ℂ) → ℂ) (k : ℝ) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : IsClassSigmaK f k), (‖Φ f‖₊ : ℝ≥0∞)

/-- **Theorem 3.6** (Ch. II §3.5, Lehto). Let `Φ` be an analytic functional on `Σ` which vanishes for the identity
mapping. Then `M(k)/k` is non-decreasing on the interval `(0, 1)`.
Modelling: `M(k)/k ≤ M(k′)/k′` for `0 < k < k′ < 1`, multiplied out in `[0, ∞]`. -/
theorem thm2_3_6 {Φ : (ℂ → ℂ) → ℂ} (hΦ : IsAnalyticFunctionalSigma Φ) (hid : Φ (fun z => z) = 0) {k k' : ℝ}
    (hk : 0 < k) (hkk' : k < k') (hk' : k' < 1) :
    ENNReal.ofReal k' * majorantM Φ k ≤ ENNReal.ofReal k * majorantM Φ k' := by
  sorry

/-- **Corollary 3.3** (Ch. II §3.5, Majorant principle), inequality. If `Φ` is an analytic functional on `Σ` which
vanishes for the identity mapping, then `max_{f ∈ Σ_k} |Φ(f)| ≤ k max_{f ∈ Σ} |Φ(f)|` (3.13).
Modelling: `0 ≤ k < 1`; the maxima are suprema in `[0, ∞]`. -/
theorem cor2_3_3_i {Φ : (ℂ → ℂ) → ℂ} (hΦ : IsAnalyticFunctionalSigma Φ) (hid : Φ (fun z => z) = 0) {k : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    majorantM Φ k ≤ ENNReal.ofReal k * ⨆ (f : ℂ → ℂ) (_ : IsClassSigma0 f), (‖Φ f‖₊ : ℝ≥0∞) := by
  sorry

/-- **Corollary 3.3** (Ch. II §3.5), equality. If equality holds in (3.13) for one value `k ∈ (0, 1)`, then it holds
for all values of `k`.
Modelling: for all `k′ ∈ (0, 1)` (for `k′ = 0` both sides vanish). -/
theorem cor2_3_3_ii {Φ : (ℂ → ℂ) → ℂ} (hΦ : IsAnalyticFunctionalSigma Φ) (hid : Φ (fun z => z) = 0) {k : ℝ}
    (hk0 : 0 < k) (hk : k < 1)
    (heq : majorantM Φ k = ENNReal.ofReal k * ⨆ (f : ℂ → ℂ) (_ : IsClassSigma0 f), (‖Φ f‖₊ : ℝ≥0∞)) {k' : ℝ}
    (hk'0 : 0 < k') (hk' : k' < 1) :
    majorantM Φ k' = ENNReal.ofReal k' * ⨆ (f : ℂ → ℂ) (_ : IsClassSigma0 f), (‖Φ f‖₊ : ℝ≥0∞) := by
  sorry

/-! ## §3.6 Coefficient estimates -/

/-- **Theorem 3.7** (Ch. II §3.6, Kühnau, Lehto). In the class `Σ_k`, `Σ_{n ≥ 1} n |bₙ|² ≤ k²` (3.16).
Modelling: `0 ≤ k < 1`; the series is summed in `[0, ∞]`, as in Pommerenke's `area_theorem`. [OCR] (3.16) is printed
with `hₙ` for `bₙ`. -/
theorem thm2_3_7 {f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hf : IsClassSigmaK f k) :
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * (‖Pommerenke1992.sigmaCoeff f (n + 1)‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (k ^ 2) := by
  sorry

/-- **Theorem 3.7** (Ch. II §3.6), sharpness. The estimate (3.16) is sharp: equality holds for `f(z) = z + k e^{iθ}/z`
in `|z| > 1` (extended by `z + k e^{iθ} z̄` in `|z| ≤ 1`). -/
theorem thm2_3_7_sharp {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (θ : ℝ) :
    IsClassSigmaK (fun z => z + k * Complex.exp (θ * I) / z) k ∧
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) *
        (‖Pommerenke1992.sigmaCoeff (fun z => z + k * Complex.exp (θ * I) / z) (n + 1)‖₊ : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (k ^ 2) := by
  sorry

end Lehto1987
