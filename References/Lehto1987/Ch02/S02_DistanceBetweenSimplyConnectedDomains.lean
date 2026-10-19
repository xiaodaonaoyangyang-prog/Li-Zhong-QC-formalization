import References.Lehto1987.Ch02.S01_SchwarzianDerivative

/-!
# Lehto, Chapter II §2: Distance between simply connected domains

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. II §2 (`full.md`
P1:2208–2552).

Conventions (see §1): domains are subsets of `ℂ̄`; "conformally equivalent to a disc" is
`Gehring1978.IsHypSimplyConnectedExt`; conformal mappings are `Gehring1978.IsConformalExt` with images
`Gehring1978.imageExt`; the norm is `Gehring1978.hypNorm`; discs are `IsDiscExt`. The domain constants `δ(A)`,
`σ₀(A)`, `δ(A, A′)` and the boundary rotation are `[0, ∞]`-valued suprema or infima over the conformal mappings
concerned (the book's "well defined" is `para2_2_1_a`). In §2.3–§2.4 the domains are subsets of the finite plane
(P1:2276, 2290), and the conformal mappings `f : D → A` are holomorphic injective maps of the unit disc onto `A`. The
Stieltjes measure `dψ` of a function `ψ` of bounded variation on `[0, 2π]` is written as the difference `νp − νn` of
two mutually singular finite measures on `[0, 2π]`, so that `∫ dψ = νp[0, 2π] − νn[0, 2π]` and
`∫ |dψ| = νp[0, 2π] + νn[0, 2π]`; `ψ` is non-decreasing when `νn = 0`.

* Definition (distance `δ(A)` of a domain from a disc, §2.1) — `discDistance`
* Unlabelled (§2.1, P1:2218): `‖S_f‖_A` is the same for all conformal mappings `f` of `A` onto a disc —
  `para2_2_1_a`
* Unlabelled (§2.1, P1:2220): `δ(A) = 0` if and only if `A` is a disc — `para2_2_1_b`
* Unlabelled (§2.1, P1:2220): `δ(A) ≤ 6` — `para2_2_1_c`
* Unlabelled (§2.1, P1:2228): the exterior of an ellipse has `δ(A) = 6k`, and `δ` takes every value in `[0, 6]` —
  omitted: an illustration, not cited
* Formula (2.1) (§2.1) — `eq2_2_1`
* Formula (2.2) (§2.2) — `eq2_2_2`
* Formula (2.3) (§2.2) — `eq2_2_3`
* Definition (boundary rotation of a domain bounded by a regular Jordan curve, (2.4), (2.5), §2.3; by exhaustion for
  general domains) — omitted: the book states that the analytic expression (2.7) gives the same value, and all later
  items use (2.7)
* Definition (boundary rotation by the analytic formula (2.6)–(2.7), §2.3) — `boundaryRotation`
* Formula (2.8) (§2.3) — `eq2_2_8`
* Unlabelled (§2.3, P1:2312): the converse of (2.8) for `k ≤ 4` — omitted: not cited
* Unlabelled (§2.3, P1:2314): convex ⇔ boundary rotation `2π` ⇔ `u > 0` ⇔ `ψ` non-decreasing — `para2_2_3`
* Definition (Möbius equivalent domains, §2.4) — `IsMobiusEquivalent`
* Theorem 2.1 (§2.4) — `thm2_2_1`, `thm2_2_1_eq`
* Formula (2.10), (2.11) (§2.4) — omitted: steps of the proof of Theorem 2.1
* Theorem 2.2 (§2.4) — `thm2_2_2`, `thm2_2_2_sharp`
* Theorem 2.3 (§2.5) — `thm2_2_3`, `thm2_2_3_sharp`
* Formula (2.14) (§2.5) — omitted: a step of the proof of Theorem 2.3
* Unlabelled (§2.5, P1:2435): `δ(A)` is half the supremum of `‖S_f‖_A` over the conformal self-mappings of `A` —
  omitted: not cited
* Definition (outer radius of univalence `σ₀(A)`, §2.6) — `outerRadiusUniv`
* Theorem 2.4 (§2.6) — `thm2_2_4`
* Unlabelled (§2.6, P1:2475–2477): the bounds `2k² + 4`, `8`, `12` derived from Theorem 2.4 — omitted: immediate
  consequences of Theorem 2.4, not cited
* Example (§2.6, P1:2485–2503): in `E = {|w| > 1}`, `‖S_{w+1/w} − S_{w−1/w}‖_E = 12` — `example2_2_6`
* Definition (distance `δ(A, A′)` between domains, §2.7) — `domainDistance`
* Unlabelled (§2.7, P1:2521–2552): the estimates `|δ(A) − δ(A′)| ≤ δ(A, A′) ≤ δ(A) + δ(A′)`, the sector example, the
  space `Ω` and the open problems — omitted: not cited (open problems are not items)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt unitDisc upperHalf schwarzian knHyp IsMobius)
open Gehring1978 (hypDensity hypNorm IsHypSimplyConnectedExt IsConformalExt imageExt)

/-! ## §2.1 Distance from a disc -/

/-- **Definition** (distance `δ(A)` of `A` from a disc, Ch. II §2.1): `δ(A) = ‖S_f‖_A` for a conformal mapping `f` of
`A` onto a disc.
Modelling: the supremum of these norms over all such `f` (they are all equal, `para2_2_1_a`), in `[0, ∞]`. Junk: `0`
for a domain without a conformal mapping onto a disc (not a domain of the book). -/
def discDistance (A : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : IsConformalExt f A ∧ IsDiscExt (imageExt f A)), hypNorm (schwarzian f) A

/-- **Unlabelled** (Ch. II §2.1, P1:2218). The norm `‖S_f‖_A` is the same for all conformal mappings `f` of `A` onto
a disc, so that `δ(A)` is well defined. -/
theorem para2_2_1_a {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {f g : ℂ → ℂ} (hf : IsConformalExt f A)
    (hfA : IsDiscExt (imageExt f A)) (hg : IsConformalExt g A) (hgA : IsDiscExt (imageExt g A)) :
    hypNorm (schwarzian f) A = hypNorm (schwarzian g) A := by
  sorry

/-- **Unlabelled** (Ch. II §2.1, P1:2220). `δ(A) = 0` if and only if `A` is a disc. -/
theorem para2_2_1_b {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : discDistance A = 0 ↔ IsDiscExt A := by
  sorry

/-- **Unlabelled** (Ch. II §2.1, P1:2220). `δ(A) ≤ 6` for all domains `A` (by Theorem 1.3 and (1.11)). -/
theorem para2_2_1_c {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : discDistance A ≤ 6 := by
  sorry

/-- **Formula (2.1)** (Ch. II §2.1). For the angular domain `A = {z | 0 < arg z < kπ}`, `0 < k ≤ 2`,
`δ(A) = 2|k² − 1|`.
Modelling: `A = {r e^{it} | r > 0, 0 < t < kπ}` (for `k > 1` the angle exceeds `π`, beyond the principal argument). -/
theorem eq2_2_1 {k : ℝ} (hk0 : 0 < k) (hk2 : k ≤ 2) :
    discDistance (toExt ((fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I)) '' (Ioi 0 ×ˢ Ioo 0 (k * Real.pi)))) =
      ENNReal.ofReal (2 * |k ^ 2 - 1|) := by
  sorry

/-! ## §2.2 Distance function and coefficient problems -/

/-- **Formula (2.2)** (Ch. II §2.2). `δ(A) = sup {|S_f(0)| | f : D → A conformal}`. -/
theorem eq2_2_2 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) :
    discDistance A = ⨆ (f : ℂ → ℂ) (_ : IsConformalExt f (toExt unitDisc) ∧ imageExt f (toExt unitDisc) = A),
      (‖schwarzian f 0‖₊ : ℝ≥0∞) := by
  sorry

/-- **Formula (2.3)** (Ch. II §2.2). For `f ∈ S`, `f(z) = z + a₂z² + a₃z³ + …`, `S_f(0) = 6(a₃ − a₂²)`.
Modelling: `aₙ` is Pommerenke's `sCoeff f n`. -/
theorem eq2_2_3 {f : ℂ → ℂ} (hf : knHyp f) :
    schwarzian f 0 = 6 * (Pommerenke1992.sCoeff f 3 - Pommerenke1992.sCoeff f 2 ^ 2) := by
  sorry

/-! ## §2.3 Boundary rotation -/

/-- **Definition** (boundary rotation, Ch. II §2.3, (2.6)–(2.7)). For a domain `A` of the plane conformally
equivalent to a disc and a conformal mapping `f` of the unit disc onto `A`, with `u(z) = 1 + Re(z f″(z)/f′(z))`
(2.6), the boundary rotation of `A` is `lim_{r → 1} ∫₀^{2π} |u(re^{iφ})| dφ` (2.7).
Modelling: the integral increases with `r` (`|u|` is subharmonic), so the limit is the supremum over `0 < r < 1`;
the value does not depend on `f`, and the infimum over the conformal mappings `f` is taken (value `⊤`, junk, for a
domain which is not the conformal image of the disc). [OCR] The label (2.6) is printed "(2.€)". -/
def boundaryRotation (A : Set ℂ) : ℝ≥0∞ :=
  ⨅ (f : ℂ → ℂ) (_ : DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f '' unitDisc = A),
    ⨆ r ∈ Ioo (0 : ℝ) 1, ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal |1 + ((r : ℂ) * Complex.exp (φ * I) * deriv (deriv f) ((r : ℂ) * Complex.exp (φ * I)) /
        deriv f ((r : ℂ) * Complex.exp (φ * I))).re|

/-- **Formula (2.8)** (Ch. II §2.3). Suppose that `A` has finite boundary rotation `kπ`, and `f` maps the unit disc
conformally onto `A`. Then `f′(z) = f′(0) exp(−∫₀^{2π} log(1 − z e^{−iθ}) dψ(θ))`, where `ψ` is a function of bounded
variation with `∫₀^{2π} dψ = 2` (2.4) and `∫₀^{2π} |dψ| = k` (2.5).
Modelling: `dψ = νp − νn` as in the conventions; `log` is the principal branch (`Re(1 − z e^{−iθ}) > 0`). -/
theorem eq2_2_8 {A : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hfA : f '' unitDisc = A) {k : ℝ} (hk : boundaryRotation A = ENNReal.ofReal (k * Real.pi)) :
    ∃ νp νn : Measure ℝ, IsFiniteMeasure νp ∧ IsFiniteMeasure νn ∧ νp.MutuallySingular νn ∧
      νp (Icc 0 (2 * Real.pi))ᶜ = 0 ∧ νn (Icc 0 (2 * Real.pi))ᶜ = 0 ∧
      (νp univ).toReal - (νn univ).toReal = 2 ∧ (νp univ).toReal + (νn univ).toReal = k ∧
      ∀ z ∈ unitDisc, deriv f z = deriv f 0 *
        Complex.exp (-((∫ θ, Complex.log (1 - z * Complex.exp (-(θ * I))) ∂νp) -
          ∫ θ, Complex.log (1 - z * Complex.exp (-(θ * I))) ∂νn)) := by
  sorry

/-- **Unlabelled** (Ch. II §2.3, P1:2314). For a conformal mapping `f` of the unit disc onto `A`, the following are
equivalent: `A` is convex; `A` has boundary rotation `2π`; the function `u` of (2.6) is positive in `D`; the function
`ψ` of (2.8) is non-decreasing.
Modelling: "`ψ` non-decreasing" is the representation (2.8) with a (positive) measure `ν = dψ` of total mass `2`. -/
theorem para2_2_3 {A : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hfA : f '' unitDisc = A) :
    List.TFAE [Convex ℝ A, boundaryRotation A = ENNReal.ofReal (2 * Real.pi),
      ∀ z ∈ unitDisc, 0 < 1 + (z * deriv (deriv f) z / deriv f z).re,
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν (Icc 0 (2 * Real.pi))ᶜ = 0 ∧ ν univ = 2 ∧
        ∀ z ∈ unitDisc, deriv f z = deriv f 0 *
          Complex.exp (-∫ θ, Complex.log (1 - z * Complex.exp (-(θ * I))) ∂ν)] := by
  sorry

/-! ## §2.4 Domains of bounded boundary rotation -/

/-- Two domains of `ℂ̄` are Möbius equivalent if a Möbius transformation maps one onto the other. -/
def IsMobiusEquivalent (A B : Set ExtPlane) : Prop := ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ M '' A = B

/-- **Theorem 2.1** (Ch. II §2.4). If `A` is Möbius equivalent to a convex domain, then `δ(A) ≤ 2` (2.9).
Modelling: the convex domain is a set `B` of the finite plane; `A` is simply connected with more than one boundary
point (so `B` is not the plane). -/
theorem thm2_2_1 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A)
    (hconv : ∃ B : Set ℂ, Convex ℝ B ∧ IsMobiusEquivalent (toExt B) A) : discDistance A ≤ 2 := by
  sorry

/-- **Theorem 2.1** (Ch. II §2.4), equality. Equality holds in (2.9) if `A` is the image of a parallel strip under a
Möbius transformation.
Modelling: the strip `{z | c₁ < Im(e^{iα} z) < c₂}`, `c₁ < c₂`. -/
theorem thm2_2_1_eq {M : ExtPlane → ExtPlane} (hM : IsMobius M) {α c₁ c₂ : ℝ} (hc : c₁ < c₂) :
    discDistance (M '' toExt {z : ℂ | c₁ < (Complex.exp (α * I) * z).im ∧ (Complex.exp (α * I) * z).im < c₂}) =
      2 := by
  sorry

/-- **Theorem 2.2** (Ch. II §2.4). Let `A` be Möbius equivalent to a domain with boundary rotation `≤ kπ`. If
`k ≤ 4`, then `δ(A) ≤ (2k + 4)/(6 − k)` (2.12).
Modelling: the domain of bounded boundary rotation is a set `B` of the finite plane. -/
theorem thm2_2_2 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {k : ℝ} (hk : k ≤ 4)
    (hB : ∃ B : Set ℂ, IsMobiusEquivalent (toExt B) A ∧ boundaryRotation B ≤ ENNReal.ofReal (k * Real.pi)) :
    discDistance A ≤ ENNReal.ofReal ((2 * k + 4) / (6 - k)) := by
  sorry

/-- **Theorem 2.2** (Ch. II §2.4), sharpness. The bound (2.12) is sharp: for every `k`, `2 ≤ k ≤ 4`, some domain with
boundary rotation `≤ kπ` has `δ = (2k + 4)/(6 − k)`.
Modelling: `2 ≤ k`, since every boundary rotation is at least `2π` (2.4), so for `k < 2` there is no such domain. -/
theorem thm2_2_2_sharp {k : ℝ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    ∃ B : Set ℂ, IsHypSimplyConnectedExt (toExt B) ∧ boundaryRotation B ≤ ENNReal.ofReal (k * Real.pi) ∧
      discDistance (toExt B) = ENNReal.ofReal ((2 * k + 4) / (6 - k)) := by
  sorry

/-! ## §2.5 Upper estimate for the Schwarzian derivative -/

/-- **Theorem 2.3** (Ch. II §2.5). Let `A` and `A′` be domains conformally equivalent to a disc and `f : A → A′` a
conformal mapping. Then `‖S_f‖_A ≤ δ(A) + δ(A′)` (2.13). -/
theorem thm2_2_3 {A A' : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hA' : IsHypSimplyConnectedExt A')
    {f : ℂ → ℂ} (hf : IsConformalExt f A) (hfA : imageExt f A = A') :
    hypNorm (schwarzian f) A ≤ discDistance A + discDistance A' := by
  sorry

/-- **Theorem 2.3** (Ch. II §2.5), sharpness. The estimate (2.13) is sharp for any given pair of domains `A` and
`A′`: the supremum of `‖S_f‖_A` over the conformal mappings `f : A → A′` is `δ(A) + δ(A′)`. -/
theorem thm2_2_3_sharp {A A' : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hA' : IsHypSimplyConnectedExt A') :
    ⨆ (f : ℂ → ℂ) (_ : IsConformalExt f A ∧ imageExt f A = A'), hypNorm (schwarzian f) A =
      discDistance A + discDistance A' := by
  sorry

/-! ## §2.6 Outer radius of univalence -/

/-- **Definition** (outer radius of univalence, Ch. II §2.6): `σ₀(A) = sup {‖S_f‖_A | f univalent in A}`, in
`[0, ∞]`. -/
def outerRadiusUniv (A : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : IsConformalExt f A), hypNorm (schwarzian f) A

/-- **Theorem 2.4** (Ch. II §2.6). For a domain `A` conformally equivalent to a disc, `σ₀(A) = δ(A) + 6` (2.15). -/
theorem thm2_2_4 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : outerRadiusUniv A = discDistance A + 6 := by
  sorry

/-- **Example** (Ch. II §2.6, P1:2485–2503). In the disc `E = {|w| > 1}`,
`‖S_{w + 1/w} − S_{w − 1/w}‖_E = 12` (the maximum `12` of `‖S_{f_θ}‖` for the self-mappings `f_θ` of the complement
of `[−1, 1]`, attained at `θ = π`).
Modelling: the book's `h_θ(w) = (w + e^{iθ}/w)/2` for `θ = 0, π`; the factor `1/2` does not change the
Schwarzian. -/
theorem example2_2_6 :
    hypNorm (fun w => schwarzian (fun v : ℂ => v + 1 / v) w - schwarzian (fun v : ℂ => v - 1 / v) w) exteriorDiscE =
      12 := by
  sorry

/-! ## §2.7 Distance between arbitrary domains -/

/-- **Definition** (distance between domains, Ch. II §2.7):
`δ(A, A′) = inf {‖S_f‖_A | f : A → A′ conformal}`, in `[0, ∞]` (junk `⊤` when there is no such `f`). -/
def domainDistance (A A' : Set ExtPlane) : ℝ≥0∞ :=
  ⨅ (f : ℂ → ℂ) (_ : IsConformalExt f A ∧ imageExt f A = A'), hypNorm (schwarzian f) A

end Lehto1987
