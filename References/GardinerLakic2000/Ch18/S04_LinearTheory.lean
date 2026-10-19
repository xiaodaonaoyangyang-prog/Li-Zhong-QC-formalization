import References.GardinerLakic2000.Ch18.S03_SimpleEarthquakesAndBends

/-!
# Gardiner–Lakic 2000, Ch. 18 §18.4 The linear theory

Source `teichmuller.txt`, lines 13452–13550 (Chapter 18, §18.4).

* Definition (`𝒵`, Zygmund bounded vector fields on `ℝ̄` modulo quadratic polynomials, with the cross-ratio norm
  `‖V‖_cr = sup_Q |V{Q}|`, l. 13453–13465) — exists: `GardinerLakic2000.zCrSet` `GardinerLakic2000.crNorm`
  `GardinerLakic2000.crDistortion` (batch A, `Λ = ℝ̄`)
* Definition (the infinitesimal Teichmüller norm `‖V‖_T`, l. 13467–13474) — exists:
  `GardinerLakic2000.teichNormVF` (batch A)
* Definition (`𝓜`, real Borel measures on the lines of `ℍ`, and their norm `‖σ‖`, l. 13487, 13521) —
  `signedIntegral`, `signedIntegralC`, `IsLineMeasure`, `earthquakeMeasureNorm`
* Formulas (18.7), (18.8) (the maps `E`, `B`, l. 13495–13502) — `earthquakeOp`, `bendOp`
* Formula (18.9) (`φ_ab = (a − b)²/((z − a)²(z − b)²)` and `Θ`, l. 13505–13517) — `phiAB`, `thetaOp`
* Definition (`I(V) = (V + iHV)‴`, l. 13519, [CORRECTION] `(V − iHV)‴`; `𝓑`, l. 13519–13521) — `IsIOp` (`𝓑` exists:
  `GardinerLakic2000.boundedCuspForms` for the trivial group on the upper half-plane)
* Theorem 4 (l. 13523) — `thm18_4`

Not items: the tangent vector of an earthquake curve (l. 13480, U−, see §18.5); (18.10) and the Carleson grid (proof);
"`I : 𝒵 → 𝒵` is an isomorphism" in the proof (l. 13525) = `𝒵 → 𝓑` [misprint]. Modelling: vector fields on `ℝ̄` are
real functions on `ℝ` (as `ℂ → ℂ` functions, real on `ℝ`, for batch A's cross-ratio norm); "modulo quadratic
polynomials" is stated explicitly. A measure of `𝓜` is a pair of real measures: `σ` on the pairs `(a, b)`, `a < b`,
of `ℝ²` (the lines between finite points) and `σ∞` on `ℝ` (the lines from `a` to `∞`, with
`E_{a∞}(x) = (x − a)⁺`, `B_{a∞}(x) = (x − a) log|x − a|`, `φ_{a∞}(z) = 1/(z − a)²`, the limits of (18.5), (18.6),
(18.9) modulo linear polynomials). [CORRECTION] (AUDIT5_GL1518 G15-6) A real measure `σ` is given by the pair
`(σ⁺, σ⁻)` of measures (Mathlib `SignedMeasure`s are finite, while the measures of `𝓜` are only of finite Thurston norm,
e.g. `Σ_{a ∈ ℤ} δ_{(a, a+1)}`, the measure of the periodic bumps `Σ E_{a,a+1}`, has infinite mass); `E` and `B` integrate
kernels normalized at `0`, `1` (the book's integrals converge only modulo linear polynomials). **Norm** [reading, leader calibration E0.8]: the book uses `‖σ‖` but never defines
it; it is taken to be Thurston's norm (W. P. Thurston, *Earthquakes in two-dimensional hyperbolic geometry*, 1986),
normalized as in the proof of Lemma 18.10 (l. 13583, `I = [−2, −1]`, `J = [1, 2]`): the supremum of `|σ|([a, b] ×
[c, d])` over `a < b < c < d` with `(d − c)(b − a)/((c − b)(d − a)) = 1/8` (the value for `−2, −1, 1, 2`), together
with the boxes `[a, b] × [c, ∞]` with `(b − a)/(c − b) = 1/8` (the limit `d → ∞`). Theorem 4 [reading, E0.4]: the
maps are well defined into the stated spaces, bounded (`‖·‖ ≤ C‖·‖`), surjective, and `H`, `I` are bijective with
bounded inverses (modulo quadratic polynomials); the Banach-space structure is not otherwise captured.
**[CORRECTION]** (computed for general `a < b`; signs re-checked 2026-10-05): `F(z) = q(z) log((z − a)/(z − b))`,
`q = (z − a)(z − b)/(a − b)`, is holomorphic in `ℍ` with `F|ℝ = B_ab − iπE_ab` and `F‴ = −φ_ab`. The book's `H`
((16.23)/(16.24), kernel `1/(ξ − x)`) is minus the standard Hilbert transform (for which `Im F = H(Re F)`), so
`H ∘ B = πE` (printed `H ∘ B = E`, l. 13523; "the Hilbert transform of `B` is `E`", l. 13499; the standard sign
gives `−πE`). In this sign the boundary values of a function holomorphic in `ℍ` are `V − iHV`, so `I(V)` is
`(V − iHV)‴` (printed `(V + iHV)‴`, l. 13519, the standard-sign formula), and `I ∘ E = −(i/π) Θ` (printed
`I ∘ E = Θ`): `Ê − iHÊ ≡ (i/π)(B − iπE)`. The printed "`(B_ab + iE_ab)‴ = φ_ab`" (l. 13502) is
`(B_ab − iπE_ab)‴ = −φ_ab`. `H` acts on the normalized representative `zNormalize` (l. 12537), as in §16.7 and §18.3.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (extRealLine upperHalf)

/-- Helper (§18.4). The integral of a real function against a real measure `σ = σ⁺ − σ⁻` given as the pair
`(σ⁺, σ⁻)` of (possibly infinite, locally finite) measures: `∫ f dσ⁺ − ∫ f dσ⁻`. -/
def signedIntegral {X : Type*} [MeasurableSpace X] (σ : Measure X × Measure X) (f : X → ℝ) : ℝ :=
  (∫ x, f x ∂σ.1) - ∫ x, f x ∂σ.2

/-- Helper (§18.4). The integral of a complex function against a real measure given as a pair `(σ⁺, σ⁻)`. -/
def signedIntegralC {X : Type*} [MeasurableSpace X] (σ : Measure X × Measure X) (f : X → ℂ) : ℂ :=
  (∫ x, f x ∂σ.1) - ∫ x, f x ∂σ.2

/-- Helper (§18.4). `σ` lives on the pairs `(a, b)` with `a < b`. -/
def IsLineMeasure (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) : Prop :=
  σ.1 {p | p.2 ≤ p.1} = 0 ∧ σ.2 {p | p.2 ≤ p.1} = 0

/-- **Definition** (the norm of `𝓜`, §18.4, l. 13487, 13521; E0.8). Thurston's norm, normalized by the quadruple
`−2, −1, 1, 2`, of `σ⁺ + σ⁻` (an upper bound for the norm of `|σ⁺ − σ⁻|`, equal to it for mutually singular parts). -/
def earthquakeMeasureNorm (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ) : ℝ≥0∞ :=
  (⨆ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (_ : a < b ∧ b < c ∧ c < d ∧ (d - c) * (b - a) / ((c - b) * (d - a)) = 1 / 8),
      (σ.1 + σ.2) (Icc a b ×ˢ Icc c d)) ⊔
    ⨆ (a : ℝ) (b : ℝ) (c : ℝ) (_ : a < b ∧ b < c ∧ (b - a) / (c - b) = 1 / 8),
      (σ.1 + σ.2) (Icc a b ×ˢ Ici c) + (σinf.1 + σinf.2) (Icc a b)

/-- **Formula (18.7)** (§18.4, l. 13495). `Eσ(x) = ∬ E_ab(x) dσ(a, b)`, modulo linear polynomials: the kernel is
normalized to vanish at `0` and `1` (`Ê_ab(x) = E_ab(x) − E_ab(0)(1 − x) − E_ab(1)x`), so that the integral converges
for every `σ` of finite norm (lines enclosing `0`, `1`, `x` at scale `R` contribute `O(1/R)`). -/
def earthquakeOp (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ) (x : ℝ) : ℝ :=
  signedIntegral σ (fun p => earthquakeVF p.1 p.2 x - earthquakeVF p.1 p.2 0 * (1 - x) - earthquakeVF p.1 p.2 1 * x) +
    signedIntegral σinf (fun a => max (x - a) 0 - max (-a) 0 * (1 - x) - max (1 - a) 0 * x)

/-- **Formula (18.8)** (§18.4, l. 13502). `Bσ(x) = ∬ B_ab(x) dσ(a, b)`, modulo linear polynomials, with the kernel
normalized at `0` and `1` as in `earthquakeOp`. -/
def bendOp (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ) (x : ℝ) : ℝ :=
  signedIntegral σ (fun p => bendVF p.1 p.2 x - bendVF p.1 p.2 0 * (1 - x) - bendVF p.1 p.2 1 * x) +
    signedIntegral σinf (fun a => (x - a) * Real.log |x - a| - -a * Real.log |-a| * (1 - x) -
      (1 - a) * Real.log |1 - a| * x)

/-- **Formula** (§18.4, l. 13509). `φ_ab(z) = (a − b)²/((z − a)²(z − b)²)`. -/
def phiAB (a b : ℝ) (z : ℂ) : ℂ := (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2)

/-- **Formula (18.9)** (§18.4, l. 13515). `Θσ(z) = ∬ φ_ab(z) dσ(a, b)`. -/
def thetaOp (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ) (z : ℂ) : ℂ :=
  signedIntegralC σ (fun p => phiAB p.1 p.2 z) + signedIntegralC σinf (fun a => 1 / (z - a) ^ 2)

/-- **Definition** (`I`, §18.4, l. 13519). `φ = I(V) = (V̂ − iHV̂)‴`, `V̂ = zNormalize V`: the third derivative in `ℍ`
of the holomorphic function with boundary values `V̂ − iHV̂` [CORRECTION: the printed `(V + iHV)‴` is the
standard-sign formula; with the book's (16.24) the values `V̂ + iHV̂` are boundary values from `ℍ*`]. The third
derivative does not see the quadratic normalization. -/
def IsIOp (V φ : ℂ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F upperHalf ∧
    (∀ x : ℝ, Tendsto F (𝓝[upperHalf] (x : ℂ)) (𝓝 (zNormalize V x - I * hilbertPV (zNormalize V) x))) ∧
    ∀ z ∈ upperHalf, φ z = iteratedDeriv 3 F z

/-- **Theorem 4** (§18.4, l. 13523). `H : 𝒵 → 𝒵` and `I : 𝒵 → 𝓑` are Banach space isomorphisms, `B`, `E` and `Θ` are
bounded linear surjections from `𝓜` onto `𝒵`, `𝒵` and `𝓑`, and `H ∘ B = πE`, `I ∘ E = −(i/π) Θ` [CORRECTION]
(`H` acts on the normalized representative `zNormalize`). -/
theorem thm18_4 :
    -- `H` is bounded, with bounded inverse, on `𝒵`
    (∃ C : ℝ, ∀ V : ℂ → ℂ, (∀ x : ℝ, (V x).im = 0) → V ∈ zCrSet extRealLine →
      ∃ W ∈ zCrSet extRealLine, (∀ x : ℝ, W x = hilbertPV (zNormalize V) x) ∧
        crNorm extRealLine W ≤ ENNReal.ofReal C * crNorm extRealLine V ∧
        crNorm extRealLine V ≤ ENNReal.ofReal C * crNorm extRealLine W) ∧
    (∀ W : ℂ → ℂ, (∀ x : ℝ, (W x).im = 0) → W ∈ zCrSet extRealLine → ∃ V ∈ zCrSet extRealLine,
      (∀ x : ℝ, (V x).im = 0) ∧ ∃ a b c : ℂ, ∀ x : ℝ,
        hilbertPV (zNormalize V) x = W x + a * x ^ 2 + b * x + c) ∧
    -- `I` is bounded, injective modulo quadratic polynomials and onto `𝓑`
    (∃ C : ℝ, ∀ V : ℂ → ℂ, (∀ x : ℝ, (V x).im = 0) → V ∈ zCrSet extRealLine →
      ∃ φ ∈ boundedCuspForms ⊥ upperHalf, IsIOp V φ ∧ cuspNorm upperHalf φ ≤ ENNReal.ofReal C * crNorm extRealLine V) ∧
    (∀ V V' φ : ℂ → ℂ, IsIOp V φ → IsIOp V' φ → ∃ a b c : ℂ, ∀ x : ℝ, V x - V' x = a * x ^ 2 + b * x + c) ∧
    (∀ φ ∈ boundedCuspForms ⊥ upperHalf, ∃ V ∈ zCrSet extRealLine, (∀ x : ℝ, (V x).im = 0) ∧ IsIOp V φ) ∧
    -- `E`, `B`, `Θ` are bounded and onto
    (∃ C : ℝ, ∀ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ), IsLineMeasure σ →
      earthquakeMeasureNorm σ σinf < ⊤ →
        (fun z : ℂ => ((earthquakeOp σ σinf z.re : ℝ) : ℂ)) ∈ zCrSet extRealLine ∧
        crNorm extRealLine (fun z : ℂ => ((earthquakeOp σ σinf z.re : ℝ) : ℂ)) ≤
          ENNReal.ofReal C * earthquakeMeasureNorm σ σinf ∧
        (fun z : ℂ => ((bendOp σ σinf z.re : ℝ) : ℂ)) ∈ zCrSet extRealLine ∧
        crNorm extRealLine (fun z : ℂ => ((bendOp σ σinf z.re : ℝ) : ℂ)) ≤
          ENNReal.ofReal C * earthquakeMeasureNorm σ σinf ∧
        thetaOp σ σinf ∈ boundedCuspForms ⊥ upperHalf ∧
        cuspNorm upperHalf (thetaOp σ σinf) ≤ ENNReal.ofReal C * earthquakeMeasureNorm σ σinf) ∧
    (∀ V : ℂ → ℂ, (∀ x : ℝ, (V x).im = 0) → V ∈ zCrSet extRealLine →
      (∃ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ),
          IsLineMeasure σ ∧ earthquakeMeasureNorm σ σinf < ⊤ ∧
        ∃ a b c : ℝ, ∀ x : ℝ, earthquakeOp σ σinf x = (V x).re + a * x ^ 2 + b * x + c) ∧
      ∃ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ),
          IsLineMeasure σ ∧ earthquakeMeasureNorm σ σinf < ⊤ ∧
        ∃ a b c : ℝ, ∀ x : ℝ, bendOp σ σinf x = (V x).re + a * x ^ 2 + b * x + c) ∧
    (∀ φ ∈ boundedCuspForms ⊥ upperHalf, ∃ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ),
      IsLineMeasure σ ∧ earthquakeMeasureNorm σ σinf < ⊤ ∧ ∀ z ∈ upperHalf, thetaOp σ σinf z = φ z) ∧
    -- `H ∘ B = π E` and `I ∘ E = −(i/π) Θ` [CORRECTION]
    ∀ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ), IsLineMeasure σ →
      earthquakeMeasureNorm σ σinf < ⊤ →
      (∃ a b c : ℂ, ∀ x : ℝ, hilbertPV (zNormalize fun z : ℂ => ((bendOp σ σinf z.re : ℝ) : ℂ)) x =
        (π : ℂ) * earthquakeOp σ σinf x + a * x ^ 2 + b * x + c) ∧
      IsIOp (fun z : ℂ => ((earthquakeOp σ σinf z.re : ℝ) : ℂ)) (fun z => -(I / π) * thetaOp σ σinf z) := by
  sorry

end GardinerLakic2000
