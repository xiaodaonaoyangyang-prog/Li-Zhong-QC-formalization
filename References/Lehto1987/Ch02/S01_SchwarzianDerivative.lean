import References.Lehto1987.Ch01.S06_Quasidiscs
import References.LehtoVirtanen1973.Ch01.S08_ExtensionTheorems
import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem
import LiZhongQC.Lemmas.Koebe

/-!
# Lehto, Chapter II §1: Schwarzian derivative

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. II §1 (`full.md`
P1:1854–2207).

Conventions of Chapter II, as modelled here. Functions are maps `f : ℂ → ℂ`, meromorphic functions read in `ℂ̄`
through `LiZhongQC.meroToExt` (`∞` at a pole). "Meromorphic and locally injective" in a set of the finite plane is
the project's `LiZhongQC.IsLocUnivMero`; in a domain `A` of `ℂ̄` it is `IsLocUnivMeroExt` below (at `∞ ∈ A` in the
chart `z ↦ f(1/z)`). "Conformal", "univalent", "injective meromorphic" in a domain `A` of `ℂ̄` is Gehring's
`Gehring1978.IsConformalExt`, with image `Gehring1978.imageExt f A`. The Schwarzian derivative is
`LiZhongQC.schwarzian` (at a simple pole it is `S_{1/f}`, as in the book); its value at `∞` is never needed, because
the norm (1.8) is Gehring's `Gehring1978.hypNorm`, the supremum of `|φ| η⁻²` over the finite points of `A`, with the
Poincaré density `η_A = |f′|/(1 − |f|²)` of I.1.1 (`Gehring1978.hypDensity`, curvature `−4`; every constant of the
chapter, 6, 2, 12, …, is for this normalization). "A simply connected domain conformally equivalent to a disc" (a
simply connected domain of `ℂ̄` with more than one boundary point) is `Gehring1978.IsHypSimplyConnectedExt`. A Möbius
transformation is `z ↦ (az + b)/(cz + d)`, `ad − bc ≠ 0` (on `ℂ̄`: `LiZhongQC.mobiusExt a b c d`). A disc (P1:2184) is
a component of the complement of a circle or line of `ℂ̄` (`IsDiscExt`); `E = {|z| > 1}` contains `∞`
(`exteriorDiscE`).

* Definition (Schwarzian derivative `S_f`, (1.1), §1.1) — exists: `LiZhongQC.schwarzian` (the formula (1.1) where f is
  holomorphic, and S_{1/f} at a simple pole)
* Definition (meromorphic, locally injective, univalent, §1.1) — exists: `LiZhongQC.IsLocUnivMero`,
  `LiZhongQC.IsUnivMero`, `Gehring1978.IsConformalExt` (in sets of the finite plane, resp. univalence in a domain
  of the extended plane)
* Definition (locally injective meromorphic function in a domain of `ℂ̄`, §1.1) — `IsLocUnivMeroExt`
* Formula (1.2) (§1.1): a Möbius transformation satisfies `S_f = 0` — exists: `LiZhongQC.schwarzian_mobius`
* Formula (1.2) (§1.1): every solution of `S_f = 0` is a Möbius transformation — `eq2_1_2_b`
* Unlabelled (§1.1, P1:1882–1888): `S_f = S_{1/f}`; `S_f` is holomorphic for a locally injective meromorphic `f` —
  exists: `LiZhongQC.schwarzian_inv`, `LiZhongQC.schwarzian_holomorphic` (the first at a point where f is holomorphic
  with f′ ≠ 0; the second in an open set)
* Formula (1.3) (§1.1) — `eq2_1_3`
* Formula (1.4) (§1.1) — `eq2_1_4`
* Unlabelled (§1.1, P1:1908): `S_f` is holomorphic at `∞` with a zero of order `≥ 4` — `para2_1_1_a`
* Unlabelled (§1.1, P1:1915): `S_{f∘g} = S_g` for a Möbius transformation `f` — exists:
  `LiZhongQC.schwarzian_mobius_comp` (post-composition of a locally injective meromorphic function with a Möbius
  transformation)
* Unlabelled (§1.1, P1:1918, Martio–Sarvas): approximation by Möbius transformations — omitted: a remark, not cited
* Theorem 1.1 (§1.2), existence — exists: `LiZhongQC.thm19_1_exists` (a locally injective meromorphic f with S_f = φ
  in a simply connected plane domain)
* Theorem 1.1 (§1.2), uniqueness — exists: `LiZhongQC.thm19_1_unique` (two solutions differ by a Möbius
  transformation, equality where both sides are finite, i.e. as meromorphic functions)
* Unlabelled (§1.2, P1:1968): for solutions `w₁, w₂` of (1.6) with non-vanishing Wronskian, `S_{w₁/w₂} = φ` —
  `para2_1_2`
* Formula (1.5)–(1.7) (§1.2) — omitted: steps of the proof of Theorem 1.1
* Unlabelled (§1.2, P1:1974): Theorem 1.1 for domains containing `∞` — omitted: a remark, not cited
* Definition (norm `‖φ‖_A`, (1.8), §1.3) — exists: `Gehring1978.hypNorm` (the supremum of |φ| η⁻² over the finite
  points of A, with the Poincaré density of I.1.1)
* Formula (1.9) (§1.3) — `eq2_1_9`
* Unlabelled (§1.3, P1:2011): `‖S_f − S_g‖_A = ‖S_{f∘h} − S_{g∘h}‖_B` — `para2_1_3`
* Formula (1.10) (§1.3) — `eq2_1_10`
* Formula (1.11) (§1.3) — `eq2_1_11`
* Formula (1.12) (§1.3) — `eq2_1_12`
* Unlabelled (§1.4, P1:2036): locally uniform convergence of locally injective meromorphic functions implies locally
  uniform convergence of their Schwarzians — `para2_1_4`
* Example (§1.4, P1:2048): `z + r/z → z + 1/z` uniformly in `|z| > 1`, but `‖S_f − S_{fₙ}‖ ≥ 6` — `example2_1_4_a`
* Example (§1.4, P1:2064): the sectors `z^{aₙ}` in the upper half-plane — omitted: an illustration, not cited
* Example (§1.4, P1:2082): `‖S_{z^{1/n}} − S_{log}‖_H = 2/n²` — `example2_1_4_c`
* Unlabelled (§1.4, P1:2074–2102): the normalized example, the application to normal families, the analogy with
  complex dilatations — omitted: remarks, not cited
* Definition (`E = {|z| > 1}` of `ℂ̄`, §1.4–§1.5) — `exteriorDiscE`
* Theorem 1.2 (§1.5, Area theorem) — exists: `Pommerenke1992.area_theorem` (the functions univalent in |z| > 1 with
  the expansion (1.14) are Pommerenke's class Σ; the sum is taken in the extended nonnegative reals; sharpness by its
  equality case)
* Formula (1.16) (§1.5) — exists: `Pommerenke1992.area_theorem` (|b₁|² ≤ 1, and |b₁| = 1 exactly for
  z + b₀ + e^{iθ}/z) [misprint: the book omits b₀, which (1.14) allows; see the root Corrections]
* Definition (class `Σ`, §1.5) — `IsClassSigma0`
* Definition (class `S`, §1.5) — exists: `LiZhongQC.knHyp` (holomorphic and injective in the unit disc, f(0) = 0,
  f′(0) = 1)
* Formula (1.17) (§1.5) — exists: `LiZhongQC.koebe_bieberbach` (|f″(0)| ≤ 4, i.e. |a₂| ≤ 2)
* Formula (1.17) (§1.5): equality only for the Koebe functions — `eq2_1_17_eq`
* Formula (1.18) and the estimates after it (§1.5) — exists: `Pommerenke1992.eq1_3_12`,
  `LiZhongQC.kb_koebe_transform_ineq`, `Pommerenke1992.thm1_3` (the Koebe transform lies in S; the inequality
  |(1 − |z|²)f″/f′ − 2z̄| ≤ 4; the growth bound; the Koebe one-quarter theorem is stated in Ch. I §1)
* Formula (1.19) (§1.6) — omitted: an example of an infinite norm, not cited
* Definition (disc, §1.6) — `IsDiscExt`
* Theorem 1.3 (§1.6, Kraus) — `thm2_1_3`, `thm2_1_3_sharp`
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt unitDisc upperHalf schwarzian IsLocUnivMero meroToExt mobiusExt knHyp)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsGenCircle sphericalDist)
open Gehring1978 (hypDensity hypNorm IsHypSimplyConnectedExt IsConformalExt imageExt)

/-! ## §1.1 Definition and transformation rules -/

/-- **Definition** (locally injective meromorphic function in a domain of `ℂ̄`, Ch. II §1.1). `f` is meromorphic and
locally injective at the finite points of `A`, and, if `∞ ∈ A`, the function `φ(z) = f(1/z)` is meromorphic and
locally injective in a neighbourhood of the origin.
Modelling: `φ` is a function equal to `f(1/z)` on a punctured disc `0 < |z| < r` (its value at `0` is the limit, which
Lean's `f(1/0)` does not give). -/
def IsLocUnivMeroExt (f : ℂ → ℂ) (A : Set ExtPlane) : Prop :=
  IsLocUnivMero f (finitePart A) ∧
    (extInf ∈ A → ∃ r > (0 : ℝ), ∃ φ : ℂ → ℂ, IsLocUnivMero φ (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → φ z = f z⁻¹)

/-- **Formula (1.2)** (Ch. II §1.1), converse. Every solution of `S_f = 0` is a Möbius transformation.
Modelling: `f` is a locally injective meromorphic function in a domain `A` of the finite plane (so that `S_f` is
defined); it is Möbius as a map into `ℂ̄`: `f = (az + b)/(cz + d)` at every point of `A`, poles included (near miss:
`LiZhongQC.thm19_1_unique` with `g = id` compares values only where both sides are finite). -/
theorem eq2_1_2_b {A : Set ℂ} (hA : IsOpen A) (hAc : IsConnected A) {f : ℂ → ℂ} (hf : IsLocUnivMero f A)
    (hS : ∀ z ∈ A, schwarzian f z = 0) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ A, meroToExt f z = mobiusExt a b c d z := by
  sorry

/-- **Formula (1.3)** (Ch. II §1.1). The transformation rule `S_{f∘g} = (S_f ∘ g) g′² + S_g`.
Modelling: `f` is locally injective meromorphic in an open set `B` of the finite plane, and the rule is stated at a
point `z` where `g` is holomorphic with `g′(z) ≠ 0` and `g(z) ∈ B` (`f` may have a pole at `g(z)`); at a pole of `g`
the right-hand side of (1.3) has no meaning (near miss: `LiZhongQC.eq19_1_chain_rule` needs `f` holomorphic at
`g(z)`). -/
theorem eq2_1_3 {f g : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B) (hf : IsLocUnivMero f B) {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0) (hgz : g z ∈ B) :
    schwarzian (f ∘ g) z = schwarzian f (g z) * deriv g z ^ 2 + schwarzian g z := by
  sorry

/-- **Formula (1.4)** (Ch. II §1.1). If `g` is a Möbius transformation, `S_{f∘g} = (S_f ∘ g) g′²`.
Modelling: `g(z) = (az + b)/(cz + d)`, `ad − bc ≠ 0`, at a point `z` with `cz + d ≠ 0`, where
`g′(z) = (ad − bc)/(cz + d)²`; `f` is locally injective meromorphic in an open set `B ∋ g(z)`. -/
theorem eq2_1_4 {f : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B) (hf : IsLocUnivMero f B) {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0) {z : ℂ} (hz : c * z + d ≠ 0) (hzB : (a * z + b) / (c * z + d) ∈ B) :
    schwarzian (fun w => f ((a * w + b) / (c * w + d))) z =
      schwarzian f ((a * z + b) / (c * z + d)) * ((a * d - b * c) / (c * z + d) ^ 2) ^ 2 := by
  sorry

/-- **Unlabelled** (Ch. II §1.1, P1:1908). If `f` is meromorphic and locally injective in a domain containing `∞`,
then `S_f` is holomorphic at `∞` and has a zero of order `≥ 4` there: `S_f(1/ζ) = ζ⁴ S_φ(ζ)`, `φ(ζ) = f(1/ζ)`, with
`S_φ` holomorphic at `0`.
Modelling: in the chart `ζ = 1/z` at `∞`, `S_f(1/ζ) = ζ⁴ ψ(ζ)` near `ζ = 0` for a function `ψ` holomorphic at `0`. -/
theorem para2_1_1_a {f : ℂ → ℂ} {A : Set ExtPlane} (hA : IsDomainExt A) (hinf : extInf ∈ A)
    (hf : IsLocUnivMeroExt f A) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), schwarzian f ζ⁻¹ = ζ ^ 4 * ψ ζ := by
  sorry

/-! ## §1.2 Existence and uniqueness -/

/-- **Unlabelled** (Ch. II §1.2, P1:1968). Let `φ` be holomorphic in `A`, and let `w₁`, `w₂` be linearly independent
holomorphic solutions of `w″ + ½ φ w = 0` (1.6) in `A`. Then `f = w₁/w₂` is a locally injective meromorphic function
in `A` and `S_f = φ`.
Modelling: `A` is an open set of the finite plane; linear independence is the non-vanishing of the Wronskian
`w₁w₂′ − w₂w₁′` (a constant on each component of `A`; the proof of Theorem 4.1 normalizes it to `1`). -/
theorem para2_1_2 {A : Set ℂ} (hA : IsOpen A) {φ w₁ w₂ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ A)
    (hw₁ : DifferentiableOn ℂ w₁ A) (hw₂ : DifferentiableOn ℂ w₂ A)
    (h₁ : ∀ z ∈ A, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0) (h₂ : ∀ z ∈ A, deriv (deriv w₂) z + φ z / 2 * w₂ z = 0)
    (hW : ∀ z ∈ A, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z ≠ 0) :
    IsLocUnivMero (fun z => w₁ z / w₂ z) A ∧ ∀ z ∈ A, schwarzian (fun z => w₁ z / w₂ z) z = φ z := by
  sorry

/-! ## §1.3 Norm of the Schwarzian derivative -/

/-- **Formula (1.9)** (Ch. II §1.3). Let `f` and `g` be meromorphic in the domain `A` and `h : B → A` a conformal
mapping. If `w = h(z)`, then `|S_f(w) − S_g(w)|/η_A(w)² = |S_{f∘h}(z) − S_{g∘h}(z)|/η_B(z)²`.
Modelling: `A` is simply connected with more than one boundary point, `f`, `g` are locally injective (so that the
Schwarzians are defined), `h` is conformal in `B` with `h(B) = A`; the identity is stated at the finite points `z`
with finite image `w = h(z)`. -/
theorem eq2_1_9 {A B : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {f g h : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    (hg : IsLocUnivMeroExt g A) (hh : IsConformalExt h B) (hhB : imageExt h B = A) {z : ℂ}
    (hz : (z : ExtPlane) ∈ B) (hhz : AnalyticAt ℂ h z) :
    ‖schwarzian f (h z) - schwarzian g (h z)‖ / hypDensity A (h z) ^ 2 =
      ‖schwarzian (f ∘ h) z - schwarzian (g ∘ h) z‖ / hypDensity B z ^ 2 := by
  sorry

/-- **Unlabelled** (Ch. II §1.3, P1:2011). In the situation of (1.9), `‖S_f − S_g‖_A = ‖S_{f∘h} − S_{g∘h}‖_B`.
[OCR] `S_θ` is printed for `S_g`. -/
theorem para2_1_3 {A B : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {f g h : ℂ → ℂ}
    (hf : IsLocUnivMeroExt f A) (hg : IsLocUnivMeroExt g A) (hh : IsConformalExt h B) (hhB : imageExt h B = A) :
    hypNorm (fun w => schwarzian f w - schwarzian g w) A =
      hypNorm (fun z => schwarzian (f ∘ h) z - schwarzian (g ∘ h) z) B := by
  sorry

/-- **Formula (1.10)** (Ch. II §1.3). If `g` is a conformal mapping of `A`, then `‖S_f − S_g‖_A = ‖S_{f∘g⁻¹}‖_{g(A)}`.
Modelling: `g⁻¹` is a function `ginv` conformal in `g(A)` with `ginv(g(z)) = z` at the finite points `z ∈ A` where
`g` is finite (this fixes `ginv` in `g(A)` up to its values at the at most two exceptional points, which the germ-wise
Schwarzian does not see). [OCR] `θ` is printed for `g`. -/
theorem eq2_1_10 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {f g ginv : ℂ → ℂ}
    (hf : IsLocUnivMeroExt f A) (hg : IsConformalExt g A) (hginv : IsConformalExt ginv (imageExt g A))
    (hinv : ∀ z : ℂ, (z : ExtPlane) ∈ A → AnalyticAt ℂ g z → ginv (g z) = z) :
    hypNorm (fun z => schwarzian f z - schwarzian g z) A = hypNorm (schwarzian (f ∘ ginv)) (imageExt g A) := by
  sorry

/-- **Formula (1.11)** (Ch. II §1.3). For a conformal mapping `g` of `A`, `‖S_g‖_A = ‖S_{g⁻¹}‖_{g(A)}`.
Modelling: `g⁻¹` as in (1.10). -/
theorem eq2_1_11 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {g ginv : ℂ → ℂ} (hg : IsConformalExt g A)
    (hginv : IsConformalExt ginv (imageExt g A)) (hinv : ∀ z : ℂ, (z : ExtPlane) ∈ A → AnalyticAt ℂ g z → ginv (g z) = z) :
    hypNorm (schwarzian g) A = hypNorm (schwarzian ginv) (imageExt g A) := by
  sorry

/-- **Formula (1.12)** (Ch. II §1.3). If `g` is a Möbius transformation, `‖S_f‖_A = ‖S_{f∘g⁻¹}‖_{g(A)}`.
Modelling: `g(z) = (az + b)/(cz + d)`, `ad − bc ≠ 0`, `g⁻¹(w) = (dw − b)/(−cw + a)`, `g(A)` the image in `ℂ̄`. -/
theorem eq2_1_12 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    hypNorm (schwarzian f) A =
      hypNorm (schwarzian fun w => f ((d * w - b) / (-c * w + a))) (mobiusExt a b c d '' A) := by
  sorry

/-! ## §1.4 Convergence of Schwarzian derivatives -/

/-- **Unlabelled** (Ch. II §1.4, P1:2036). If meromorphic, locally injective functions `fₙ` converge locally uniformly
in a domain `A` to a locally injective meromorphic function `f`, then `S_{fₙ} → S_f` locally uniformly in `A`.
Modelling: the convergence of the meromorphic functions is uniform convergence in the spherical metric on the compact
subsets of the finite part of `A`; the conclusion is stated at the finite points (at `∞` the chart `1/z` would be
used). -/
theorem para2_1_4 {A : Set ExtPlane} (hA : IsDomainExt A) {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfn : ∀ n, IsLocUnivMero (fn n) (finitePart A)) (hf : IsLocUnivMero f (finitePart A))
    (hconv : ∀ C ⊆ finitePart A, IsCompact C → ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C,
      sphericalDist (meroToExt (fn n) z) (meroToExt f z) < ε) :
    TendstoLocallyUniformlyOn (fun n => schwarzian (fn n)) (schwarzian f) atTop (finitePart A) := by
  sorry

/-- The disc `E = {z | |z| > 1}` of `ℂ̄` (the point `∞` included). -/
def exteriorDiscE : Set ExtPlane := insert extInf (toExt {z : ℂ | 1 < ‖z‖})

/-- **Example** (Ch. II §1.4, P1:2048). For `0 < r < 1`, the functions `z ↦ z + r/z` and `f(z) = z + 1/z` are
injective meromorphic in `E = {|z| > 1}`, `|(z + r/z) − f(z)| < 1 − r` in `E`, and yet
`‖S_f − S_{z + r/z}‖_E ≥ 6`; so with `rₙ → 1`, uniform convergence does not give convergence in norm. -/
theorem example2_1_4_a {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsConformalExt (fun w : ℂ => w + r / w) exteriorDiscE ∧ IsConformalExt (fun w : ℂ => w + 1 / w) exteriorDiscE ∧
      (∀ z : ℂ, 1 < ‖z‖ → ‖(z + r / z) - (z + 1 / z)‖ < 1 - r) ∧
      6 ≤ hypNorm (fun z => schwarzian (fun w : ℂ => w + 1 / w) z - schwarzian (fun w : ℂ => w + r / w) z)
        exteriorDiscE := by
  sorry

/-- **Example** (Ch. II §1.4, P1:2082). In the upper half-plane `H`, `‖S_{z^{1/n}} − S_{log z}‖_H = 2/n²`.
Modelling: `z^{1/n}` and `log z` are the principal branches (holomorphic in `H`). -/
theorem example2_1_4_c {n : ℕ} (hn : 1 ≤ n) :
    hypNorm (fun z => schwarzian (fun w : ℂ => w ^ ((1 : ℂ) / n)) z - schwarzian Complex.log z) (toExt upperHalf) =
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  sorry

/-! ## §1.5 Area theorem -/

/-- **Definition** (class `Σ`, Ch. II §1.5): the functions univalent in `{|z| > 1}` with an expansion
`f(z) = z + Σ_{n ≥ 1} bₙ z⁻ⁿ`, i.e. those of the Area theorem with `b₀ = 0`: Pommerenke's class `Σ` with
`f(z) − z → 0` as `z → ∞`. -/
def IsClassSigma0 (g : ℂ → ℂ) : Prop :=
  Pommerenke1992.IsClassSigma g ∧ Tendsto (fun ζ => g ζ - ζ) (cocompact ℂ) (𝓝 0)

/-- **Formula (1.17)** (Ch. II §1.5), equality case. For `f ∈ S`, `|a₂| = 2` only for the Koebe functions
`z ↦ z/(1 + e^{iθ} z)²`.
Modelling: `a₂ = f″(0)/2`; the Koebe function is compared with `f` in the unit disc. -/
theorem eq2_1_17_eq {f : ℂ → ℂ} (hf : knHyp f) (h2 : ‖deriv (deriv f) 0 / 2‖ = 2) :
    ∃ θ : ℝ, ∀ z ∈ unitDisc, f z = z / (1 + Complex.exp (θ * I) * z) ^ 2 := by
  sorry

/-! ## §1.6 Conformal mappings of a disc -/

/-- **Definition** (disc, Ch. II §1.6): a domain bounded by a circle or a straight line, i.e. a component of the
complement of a circle of `ℂ̄` (LV's `IsGenCircle`, lines included). -/
def IsDiscExt (A : Set ExtPlane) : Prop :=
  ∃ Γ : Set ExtPlane, IsGenCircle Γ ∧ ∃ p ∈ Γᶜ, A = connectedComponentIn Γᶜ p

/-- **Theorem 1.3** (Ch. II §1.6, Kraus). If `f` is a conformal mapping of a disc `A`, then `‖S_f‖_A ≤ 6` (1.20). -/
theorem thm2_1_3 {A : Set ExtPlane} (hA : IsDiscExt A) {f : ℂ → ℂ} (hf : IsConformalExt f A) :
    hypNorm (schwarzian f) A ≤ 6 := by
  sorry

/-- **Theorem 1.3** (Ch. II §1.6), sharpness. The bound `6` is attained: for the Koebe functions
`z ↦ z/(1 + e^{iθ} z)²` in the unit disc, `‖S_f‖ = 6`. -/
theorem thm2_1_3_sharp (θ : ℝ) :
    hypNorm (schwarzian fun z : ℂ => z / (1 + Complex.exp (θ * I) * z) ^ 2) (toExt unitDisc) = 6 := by
  sorry

end Lehto1987
