import References.ImayoshiTaniguchi1992.Ch03.S04_ThurstonCompactification
import References.Lehto1987.Ch05.S05_ComplexStructuresOnTeichmullerSpaces

/-!
# Imayoshi–Taniguchi, Chapter 7 §7.3: The Weil–Petersson metric

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 7 §7.3 (`full.md` IT2:520–1395,
folder `An Introduction to Teichmuller Spaces … 0ac64ea2`), with the notions of §7.1–§7.2 it needs.

Conventions (Ch. 7, IT1:6486): `Γ` is a Fuchsian model on `ℍ = H` of a closed Riemann surface of genus `g ≥ 2`
(`IsFuchsian`, `IsCocompact`), `λ_H(z) = 1/Im z`, `F` a relatively compact fundamental domain
(`LiZhongQC.IsFundamentalDomainH`), `N = 3g - 3`. **Chart-wise statements (IT-D5):** no complex-manifold structure is put on
`T(Γ)`; the Weil–Petersson metric is stated in the Bers chart `t ↦ [w^{ν(t)}]`, `ν(t) = Σ t^j ν_j`, `ν_j = μ[φ_j]`, `t ∈ D ⊆ ℂ^N`
(`nuOf`), `w^ν` being `LiZhongQC.fMuSym ν` (the normalized quasiconformal self-map of `ℍ`). `B(H, Γ)` is `Lehto1987.LinfG Γ`
(bounded measurable `Γ`-automorphic differentials, `0` off `ℍ`); `A₂(H, Γ)` is `A2 Γ` (holomorphic automorphic forms of
weight 4 with `|φ| (Im z)² ` bounded; for closed surfaces this is the space of integrable ones). The Bergman projection
is not defined: the book's `φ[μ] = β₂(λ_H² μ̄)` (7.16) is the explicit integral `phiOf` (holomorphic in `z`; the book's (7.15) `-2 Φ̇_o[μ](z̄)` is its complex conjugate, see `phiOf`).
`h_{jk̄}(t)` is the relation `IsWPInnerProduct` (the Hermitian product `h^{ν}(H^{ν} L^{ν}[ν_j], H^{ν} L^{ν}[ν_k])`
(7.34) on the deformed group `Γ^ν`); Wirtinger derivatives are `wirtinger`, `wirtingerBar`.

* Definition (`A₂(H, Γ)`, `μ[φ]` (7.14), `φ[μ]` (7.15)–(7.16), `H[μ]` (7.17), `(μ, φ)_R`; §7.1–§7.2) — `A2`, `harmBeltrami`, `phiOf`,
  `harmProj`, `pairingR`
* Definition (Hermitian product `h` (7.31), IT2:527) — `hProd`
* Lemma 7.12 (a) ((7.32), IT2:539) — `lemma7_12_a`
* Lemma 7.12 (b) ((7.33), IT2:545) — `lemma7_12_b`
* Definition (Weil–Petersson metric `h_WP`, `h_{jk̄}` (7.34)–(7.35), IT2:569) — `nuOf`, `mobH`, `IsDeformedGroup`,
  `IsLTransport`, `IsWPInnerProduct`
* Theorem 7.13 (`h_{jk̄}` is `C^∞`, IT2:611) — `thm7_13`
* Theorem 7.14 (`h_WP` is `Mod(Γ)`-invariant, IT2:623) — `IsPullbackCoeff`, `thm7_14`
* Definition (`g_WP`, `ω_WP` (7.36), IT2:627) — `gWPCoord`, `omegaWPCoord`
* Definition (Kähler (7.37), IT2:657) — `wirtinger`, `wirtingerBar`, `IsKahlerCoeff`
* Theorem 7.15 (Ahlfors: `h_WP` is Kähler, IT2:673) — `thm7_15`
* Unlabelled (Remark 1 (ii): `ℓ_j`, `τ_j` are real-analytic on `T(Γ)`, IT2:787) — exists: `ImayoshiTaniguchi1992.lemma3_9`
  (lengths and branches of the twisting parameters; τ_j = ℓ_j θ_j/2π)
* Unlabelled (Remark 2: `f^t` is `C^∞` in `(z, t)`, IT2:795) — `rem7_3_2_smooth`
* Lemma 7.16 (first variation of the hyperbolic area element, IT2:885) — `rhoFn`, `lemma7_16`
* Definition (curvatures (7.49)–(7.51), IT2:961) — `hInvUp`, `christoffel`, `curvR`, `ricci`, `curvLow`, `ricciCurv`,
  `holSectional`, `scalarCurv`
* Theorem 7.17 (a) (Ricci curvature is negative, IT2:1003) — `thm7_17_a`
* Theorem 7.17 (b) (scalar curvature is negative, IT2:1003) — `thm7_17_b`
* Theorem 7.17 (c) (holomorphic sectional curvature is negative, IT2:1003) — `thm7_17_c`
* Definition (WP metric of `T₁`, §7.3.5, IT2:1135) — omitted: garbled in the OCR and not cited later
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (upperHalf fMuSym dz dzbar complexDilatation IsFundamentalDomainH IsFuchsian IsCocompact BeltramiGamma
  mobiusFn)
open GardinerLakic2000 (qcNormalizer)

/-! ## §7.1–§7.2 notions -/

/-- The Möbius action of `γ ∈ SL(2, ℝ)` on `ℂ`, `z ↦ (a z + b)/(c z + d)`. -/
def mobH (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ := mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z

/-- **`A₂(H, Γ)`** (Ch. 7 §7.1): holomorphic quadratic differentials for `Γ` on `H`, i.e. holomorphic `φ` on `ℍ` with
`φ(γ z) γ'(z)² = φ(z)` (`γ'(z)² = (cz+d)^{-4}`) and `|φ(z)| (Im z)²` bounded. Modelling: for closed surfaces boundedness is
integrability. -/
def A2 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ upperHalf ∧
    (∀ γ ∈ Γ, ∀ z ∈ upperHalf, φ (mobH γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) ∧
    ∃ C : ℝ, ∀ z ∈ upperHalf, ‖φ z‖ * z.im ^ 2 ≤ C}

/-- **Harmonic Beltrami differential `μ[φ] = λ_H^{-2} φ̄`** (7.14), extended by `0` off `ℍ`. -/
def harmBeltrami (φ : ℂ → ℂ) (z : ℂ) : ℂ := if 0 < z.im then (z.im : ℂ) ^ 2 * conj (φ z) else 0

/-- **`φ[μ] = β₂(λ_H² μ̄)`** (7.16): `φ[μ](z) = (12/π) ∬_H conj(μ(ζ))/(z - ζ̄)⁴ dξ dη`, a *holomorphic* quadratic differential
in `z ∈ ℍ` (the Bergman projection of `λ_H² μ̄`; kernel `(12/π)(z - ζ̄)⁻⁴` for the weight `(Im ζ)²`), so that `φ[μ[φ]] = φ`.
**Correction** (IT-fix2, audit AUDIT3_IT finding 1). The book's (7.15) `φ[μ](z) = -2 Φ̇_o[μ](z̄)` and (7.16) differ by a complex
conjugation: `Φ̇_o[μ]` is holomorphic on `ℍ*` (Ch. 6 §2.2), so `-2 Φ̇_o[μ](z̄)` is antiholomorphic in `z` and equals
`conj (φ[μ](z))`. The earlier reading `(12/π) ∬ μ(ζ)/(z̄ - ζ)⁴` was that conjugate (it sent `μ[φ₀]` to `conj φ₀`); the correct
`φ[μ](z) = -2 conj (Φ̇_o[μ](z̄))`. *Junk:* `0` if the integral does not converge (it converges for bounded `μ`). -/
def phiOf (μ : ℂ → ℂ) (z : ℂ) : ℂ := (12 / (Real.pi : ℂ)) * ∫ ζ in upperHalf, conj (μ ζ) / (z - conj ζ) ^ 4

/-- **`H[μ] = λ_H^{-2} conj(φ[μ])`** (7.17), the harmonic Beltrami differential induced by `μ`, extended by `0` off `ℍ`. -/
def harmProj (μ : ℂ → ℂ) (z : ℂ) : ℂ := harmBeltrami (phiOf μ) z

/-- **The pairing `(μ, φ)_R = ∬_F μ φ dx dy`** (Ch. 7 §7.2.1). -/
def pairingR (F : Set ℂ) (μ φ : ℂ → ℂ) : ℂ := ∫ z in F, μ z * φ z

/-- **The Hermitian product `h(μ₁, μ₂) = ∬_F λ_H² μ₁ μ̄₂ dx dy`** (7.31). -/
def hProd (F : Set ℂ) (μ₁ μ₂ : ℂ → ℂ) : ℂ := ∫ z in F, ((1 / z.im ^ 2 : ℝ) : ℂ) * (μ₁ z * conj (μ₂ z))

/-- **Lemma 7.12 (a)** ((7.32), Ch. 7 §7.3.1). For `μ₁, μ₂ ∈ B(H, Γ)`:
`h(H[μ₁], H[μ₂]) = h(H[μ₁], μ₂) = h(μ₁, H[μ₂])`. -/
theorem lemma7_12_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F)) {μ₁ μ₂ : ℂ → ℂ}
    (h₁ : μ₁ ∈ Lehto1987.LinfG Γ) (h₂ : μ₂ ∈ Lehto1987.LinfG Γ) :
    hProd F (harmProj μ₁) (harmProj μ₂) = hProd F (harmProj μ₁) μ₂ ∧
      hProd F (harmProj μ₁) μ₂ = hProd F μ₁ (harmProj μ₂) := by
  sorry

/-- **Lemma 7.12 (b)** ((7.33), Ch. 7 §7.3.1). For `μ₁, μ₂ ∈ B(H, Γ)`:
`h(H[μ₁], H[μ₂]) = (H[μ₁], φ[μ₂])_R = (μ₁, φ[μ₂])_R`. -/
theorem lemma7_12_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFc : IsCompact (closure F)) {μ₁ μ₂ : ℂ → ℂ}
    (h₁ : μ₁ ∈ Lehto1987.LinfG Γ) (h₂ : μ₂ ∈ Lehto1987.LinfG Γ) :
    hProd F (harmProj μ₁) (harmProj μ₂) = pairingR F (harmProj μ₁) (phiOf μ₂) ∧
      pairingR F (harmProj μ₁) (phiOf μ₂) = pairingR F μ₁ (phiOf μ₂) := by
  sorry

/-! ## §7.3.1 The Weil–Petersson metric -/

/-- **`ν(t) = Σ_j t^j ν_j`, `ν_j = μ[φ_j]`** (Ch. 7 §7.3.1): the Beltrami coefficient of the Bers chart at `t`. -/
def nuOf {N : ℕ} (φs : Fin N → ℂ → ℂ) (t : Fin N → ℂ) : ℂ → ℂ := fun z => ∑ j, t j * harmBeltrami (φs j) z

/-- **`Γ^ν = w^ν Γ (w^ν)⁻¹`** (Ch. 7 §7.2.3): `Γ'` is the group of the Möbius maps `A` with
`A ∘ w^ν = w^ν ∘ γ` on `ℍ` for some `γ ∈ Γ`. -/
def IsDeformedGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ν : ℂ → ℂ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, A ∈ Γ' ↔ ∃ γ ∈ Γ, ∀ z ∈ upperHalf, mobH A (fMuSym ν z) = fMuSym ν (mobH γ z)

/-- **`κ = L^ν[μ]`** (7.26): `L^ν[μ] = ((w^ν)_z/\overline{(w^ν)_z} · μ/(1 - |ν|²)) ∘ (w^ν)⁻¹` on `H` (and `0` off `ℍ`), as the
relation `κ(w^ν(z)) = ((w^ν)_z/\overline{(w^ν)_z}) μ(z)/(1 - |ν(z)|²)` for `z ∈ ℍ`. -/
def IsLTransport (ν μ κ : ℂ → ℂ) : Prop :=
  (∀ z ∈ upperHalf, κ (fMuSym ν z) = (dz (fMuSym ν) z / conj (dz (fMuSym ν) z)) * (μ z / (1 - ((‖ν z‖ ^ 2 : ℝ) : ℂ)))) ∧
    ∀ z : ℂ, z.im ≤ 0 → κ z = 0

/-- **The Weil–Petersson inner product** `c = h^ν(H^ν L^ν[μ₁], H^ν L^ν[μ₂])` of two tangent vectors `μ₁, μ₂ ∈ B(H, Γ)` at the
point `p = [w^ν]` (Ch. 7 §7.3.1, (7.34)): the product (7.31) of the harmonic Beltrami differentials of the transported
vectors on a (relatively compact) fundamental domain of the deformed group `Γ^ν`. A relation (the value is single valued). -/
def IsWPInnerProduct (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ν μ₁ μ₂ : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F' : Set ℂ) (κ₁ κ₂ : ℂ → ℂ), IsDeformedGroup Γ ν Γ' ∧
    IsFundamentalDomainH Γ' F' ∧ IsCompact (closure F') ∧ IsLTransport ν μ₁ κ₁ ∧ IsLTransport ν μ₂ κ₂ ∧
      c = hProd F' (harmProj κ₁) (harmProj κ₂)

/-- **Theorem 7.13** (Ch. 7 §7.3.1). Take a basis `φ_1, …, φ_{3g-3}` of `A₂(H, Γ)` and `ν(t) = Σ t^j μ[φ_j]`, `t ∈ D`, `D` an open
neighbourhood of `0` in `ℂ^{3g-3}` on which `‖ν(t)‖_∞ < 1` (the Bers chart). Then the coefficients `h_{jk̄}(t) = h^{ν(t)}(H^{ν(t)}[ν_j(t)],
H^{ν(t)}[ν_k(t)])` (7.34) of the Weil–Petersson metric are `C^∞` on `D`. -/
theorem thm7_13 {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) (hli : LinearIndependent ℂ φs)
    (hspan : ∀ φ ∈ A2 Γ, φ ∈ Submodule.span ℂ (range φs)) {D : Set (Fin (3 * g - 3) → ℂ)} (hD : IsOpen D)
    (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t) :
    ∃ h : (Fin (3 * g - 3) → ℂ) → Fin (3 * g - 3) → Fin (3 * g - 3) → ℂ,
      (∀ t ∈ D, ∀ j k, IsWPInnerProduct Γ (nuOf φs t) (harmBeltrami (φs j)) (harmBeltrami (φs k)) (h t j k)) ∧
        ContDiffOn ℝ ∞ h D := by
  sorry

/-- **Pull-back of Beltrami coefficients by a quasiconformal self-map** `ω` of `ℍ` (Ch. 7 §7.3.1, the action of `Mod(Γ)`): `ν'` is the
complex dilatation of `w^ν ∘ ω` a.e. on `ℍ`. -/
def IsPullbackCoeff (w ν ν' : ℂ → ℂ) : Prop :=
  ∀ᵐ z ∂(volume.restrict upperHalf), ν' z = complexDilatation (fMuSym ν ∘ w) z

/-- **Theorem 7.14** (Ch. 7 §7.3.1). The Weil–Petersson metric is invariant under the Teichmüller modular group (`ν ∈ B(H, Γ)₁`,
`μ₁, μ₂ ∈ B(H, Γ)` as in the book; without them `fMuSym ν` is the junk value `id` for `‖ν‖_∞ ≥ 1`, IT-fix3, AUDITR2_IT R2-IT-02): for
`ω ∈ N_qc(Γ)` (`ω^*[ν] = [ν']`, `ν'` the dilatation of `w^ν ∘ ω`) the differential of `[ω]_*` takes the tangent vectors `μ_i`
at `[ν]` (represented by the paths `s ↦ ν + sμ_i`) to the vectors `μ_i' = ∂_s ν'_s|_{s=0}` at `[ν']`, and
`h^{ν'}(μ₁', μ₂') = h^{ν}(μ₁, μ₂)`. -/
theorem thm7_14 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hco : IsCocompact Γ) {w : ℂ → ℂ}
    (hw : w ∈ qcNormalizer Γ) {ν ν' μ₁ μ₂ μ₁' μ₂' : ℂ → ℂ} (hν : ∃ m : BeltramiGamma Γ, m.1.1 = ν)
    (hμ₁ : μ₁ ∈ Lehto1987.LinfG Γ) (hμ₂ : μ₂ ∈ Lehto1987.LinfG Γ) (hν' : IsPullbackCoeff w ν ν')
    (νs₁ νs₂ : ℝ → ℂ → ℂ) (h₁ : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), IsPullbackCoeff w (fun z => ν z + (s : ℂ) * μ₁ z) (νs₁ s))
    (h₂ : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), IsPullbackCoeff w (fun z => ν z + (s : ℂ) * μ₂ z) (νs₂ s))
    (h₁' : ∀ᵐ z ∂(volume.restrict upperHalf), HasDerivAt (fun s : ℝ => νs₁ s z) (μ₁' z) 0)
    (h₂' : ∀ᵐ z ∂(volume.restrict upperHalf), HasDerivAt (fun s : ℝ => νs₂ s z) (μ₂' z) 0) (c : ℂ) :
    IsWPInnerProduct Γ ν μ₁ μ₂ c ↔ IsWPInnerProduct Γ ν' μ₁' μ₂' c := by
  sorry

/-- **The Riemannian metric `g_WP(X, Y) = 2 Re h_WP(X, Y)`** (Ch. 7 §7.3.2, (7.35)), for the coordinate matrix `h_{jk̄}` and
tangent vectors `X, Y ∈ ℂ^N` (`h(X, Y) = Σ h_{jk̄} X^j \bar{Y^k}`). -/
def gWPCoord {N : ℕ} (h : Fin N → Fin N → ℂ) (X Y : Fin N → ℂ) : ℝ := 2 * (∑ j, ∑ k, X j * conj (Y k) * h j k).re

/-- **The Weil–Petersson form `ω_WP(X, Y) = g_WP(iX, Y) = -2 Im h_WP(X, Y)`** (Ch. 7 §7.3.2, (7.36)). -/
def omegaWPCoord {N : ℕ} (h : Fin N → Fin N → ℂ) (X Y : Fin N → ℂ) : ℝ :=
  -2 * (∑ j, ∑ k, X j * conj (Y k) * h j k).im

/-- **Wirtinger derivative** `∂f/∂t^ℓ = (∂_x - i ∂_y)/2` of a function of `t ∈ ℂ^N` at `t`. -/
def wirtinger {N : ℕ} (f : (Fin N → ℂ) → ℂ) (t : Fin N → ℂ) (ℓ : Fin N) : ℂ :=
  (fderiv ℝ f t (Pi.single ℓ 1) - Complex.I * fderiv ℝ f t (Pi.single ℓ Complex.I)) / 2

/-- **Wirtinger derivative** `∂f/∂\bar t^ℓ = (∂_x + i ∂_y)/2`. -/
def wirtingerBar {N : ℕ} (f : (Fin N → ℂ) → ℂ) (t : Fin N → ℂ) (ℓ : Fin N) : ℂ :=
  (fderiv ℝ f t (Pi.single ℓ 1) + Complex.I * fderiv ℝ f t (Pi.single ℓ Complex.I)) / 2

/-- **Kähler condition** (7.37) for the coefficient matrix `h` on `D`: `∂h_{jk̄}/∂t^ℓ = ∂h_{ℓk̄}/∂t^j` for all `j, k, ℓ`. -/
def IsKahlerCoeff {N : ℕ} (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (D : Set (Fin N → ℂ)) : Prop :=
  ∀ t ∈ D, ∀ j k ℓ, wirtinger (fun s => h s j k) t ℓ = wirtinger (fun s => h s ℓ k) t j

/-- **Theorem 7.15 (Ahlfors)** (Ch. 7 §7.3.2). The Weil–Petersson metric is Kähler: in the Bers chart around the base point
the coefficients `h_{jk̄}` satisfy (7.37). (Hypotheses as in Theorem 7.13, with `h` its `C^∞` coefficient matrix.) -/
theorem thm7_15 {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) (hli : LinearIndependent ℂ φs)
    (hspan : ∀ φ ∈ A2 Γ, φ ∈ Submodule.span ℂ (range φs)) {D : Set (Fin (3 * g - 3) → ℂ)} (hD : IsOpen D)
    (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t)
    (h : (Fin (3 * g - 3) → ℂ) → Fin (3 * g - 3) → Fin (3 * g - 3) → ℂ)
    (hh : ∀ t ∈ D, ∀ j k, IsWPInnerProduct Γ (nuOf φs t) (harmBeltrami (φs j)) (harmBeltrami (φs k)) (h t j k))
    (hsm : ContDiffOn ℝ ∞ h D) : IsKahlerCoeff h D := by
  sorry

/-- **Unlabelled claim (Remark 2)** (Ch. 7 §7.3.2, IT2:795). The normalized quasiconformal self-map `f^t = w^{ν(t)}` of `H` is
`C^∞` in `(z, t) ∈ H × D`. Modelling: the finer statement for `f_{t,s}` (`C^∞` in `(z, t, s)`, `f^t = f_{t, \bar t}`) is not
repeated. -/
theorem rem7_3_2_smooth {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) {D : Set (Fin (3 * g - 3) → ℂ)}
    (hD : IsOpen D) (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (3 * g - 3) → ℂ) => fMuSym (nuOf φs p.2) p.1) (upperHalf ×ˢ D) := by
  sorry

/-- **The function `ρ_t(z) = (|(f^t)_z|² - |(f^t)_{\bar z}|²) λ_H(f^t(z))²`** (7.42). -/
def rhoFn {N : ℕ} (φs : Fin N → ℂ → ℂ) (t : Fin N → ℂ) (z : ℂ) : ℝ :=
  (‖dz (fMuSym (nuOf φs t)) z‖ ^ 2 - ‖dzbar (fMuSym (nuOf φs t)) z‖ ^ 2) / (fMuSym (nuOf φs t) z).im ^ 2

/-- **Lemma 7.16** (Ch. 7 §7.3.3). With `ρ_t` as in (7.42), `∂ρ_t/∂t^j |_{t=0} = 0` for `j = 1, …, 3g - 3`: the first variation of
the hyperbolic area element vanishes. (`ρ_t(z)` is differentiable at `t = 0` for each `z ∈ ℍ`.) -/
theorem lemma7_16 {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) {D : Set (Fin (3 * g - 3) → ℂ)}
    (hD : IsOpen D) (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t) :
    ∀ z ∈ upperHalf, DifferentiableAt ℝ (fun t => rhoFn φs t z) 0 ∧
      ∀ j, wirtinger (fun t => ((rhoFn φs t z : ℝ) : ℂ)) 0 j = 0 := by
  sorry

/-! ## §7.3.4 Curvatures -/

section Curvature

variable {N : ℕ}

/-- The inverse matrix `(h^{j\bar m})` with `Σ_m h^{j\bar m} h_{k\bar m} = δ_{jk}`: `((h_{k\bar m})ᵀ)⁻¹`. *Junk:* `0` if `h(t)` is
singular (it is positive definite for the Weil–Petersson metric). -/
def hInvUp (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.of fun k m => h t k m).transpose⁻¹

/-- **Christoffel symbols** `Γ^j_{kℓ} = Σ_m h^{j\bar m} ∂h_{k\bar m}/∂t^ℓ` (Ch. 7 §7.3.4). -/
def christoffel (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) (j k ℓ : Fin N) : ℂ :=
  ∑ m, hInvUp h t j m * wirtinger (fun s => h s k m) t ℓ

/-- **Curvature** `R^j_{kℓ\bar m} = -∂Γ^j_{kℓ}/∂\bar t^m`. -/
def curvR (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) (j k ℓ m : Fin N) : ℂ :=
  -wirtingerBar (fun s => christoffel h s j k ℓ) t m

/-- **Ricci tensor** `R_{j\bar k} = Σ_ℓ R^ℓ_{jℓ\bar k}`. -/
def ricci (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) (j k : Fin N) : ℂ := ∑ ℓ, curvR h t ℓ j ℓ k

/-- **Lowered curvature tensor** `R_{j\bar kℓ\bar m} = -Σ_n h_{j\bar n} \overline{R^n_{km\bar ℓ}}`. -/
def curvLow (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) (j k ℓ m : Fin N) : ℂ :=
  -∑ n, h t j n * conj (curvR h t n k m ℓ)

/-- **Ricci curvature** `R_p(V) = Σ R_{j\bar k} v^j \bar v^k` (7.49). -/
def ricciCurv (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t V : Fin N → ℂ) : ℂ :=
  ∑ j, ∑ k, ricci h t j k * V j * conj (V k)

/-- **Holomorphic sectional curvature** `K_p(V) = -Σ R_{j\bar kℓ\bar m} v^j \bar v^k v^ℓ \bar v^m` (7.50). -/
def holSectional (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t V : Fin N → ℂ) : ℂ :=
  -∑ j, ∑ k, ∑ ℓ, ∑ m, curvLow h t j k ℓ m * V j * conj (V k) * V ℓ * conj (V m)

/-- **Scalar curvature** `R = Σ_{j,k} h^{j\bar k} R_{j\bar k}` (7.51); in coordinates with `h(p) = 1` this is `Σ_j R_{j\bar j}`. -/
def scalarCurv (h : (Fin N → ℂ) → Fin N → Fin N → ℂ) (t : Fin N → ℂ) : ℂ :=
  ∑ j, ∑ k, hInvUp h t j k * ricci h t j k

end Curvature

/-- **Theorem 7.17 (a)** (Ch. 7 §7.3.4). The Ricci curvatures of the Weil–Petersson metric are negative at every point of `T(Γ)`:
in the Bers chart, `R_p(V) < 0` for every `h`-unit vector `V` (`Σ h_{j\bar k} V^j \bar V^k = 1`) at every `t ∈ D`.
[OCR?: the end of the book's proof is garbled; the statement is clean.] -/
theorem thm7_17_a {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) (hli : LinearIndependent ℂ φs)
    (hspan : ∀ φ ∈ A2 Γ, φ ∈ Submodule.span ℂ (range φs)) {D : Set (Fin (3 * g - 3) → ℂ)} (hD : IsOpen D)
    (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t)
    (h : (Fin (3 * g - 3) → ℂ) → Fin (3 * g - 3) → Fin (3 * g - 3) → ℂ)
    (hh : ∀ t ∈ D, ∀ j k, IsWPInnerProduct Γ (nuOf φs t) (harmBeltrami (φs j)) (harmBeltrami (φs k)) (h t j k))
    (hsm : ContDiffOn ℝ ∞ h D) :
    ∀ t ∈ D, ∀ V : Fin (3 * g - 3) → ℂ, ∑ j, ∑ k, h t j k * V j * conj (V k) = 1 → (ricciCurv h t V).re < 0 := by
  sorry

/-- **Theorem 7.17 (b)** (Ch. 7 §7.3.4). The scalar curvature of the Weil–Petersson metric is negative on `T(Γ)`. -/
theorem thm7_17_b {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) (hli : LinearIndependent ℂ φs)
    (hspan : ∀ φ ∈ A2 Γ, φ ∈ Submodule.span ℂ (range φs)) {D : Set (Fin (3 * g - 3) → ℂ)} (hD : IsOpen D)
    (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t)
    (h : (Fin (3 * g - 3) → ℂ) → Fin (3 * g - 3) → Fin (3 * g - 3) → ℂ)
    (hh : ∀ t ∈ D, ∀ j k, IsWPInnerProduct Γ (nuOf φs t) (harmBeltrami (φs j)) (harmBeltrami (φs k)) (h t j k))
    (hsm : ContDiffOn ℝ ∞ h D) : ∀ t ∈ D, (scalarCurv h t).re < 0 := by
  sorry

/-- **Theorem 7.17 (c)** (Ch. 7 §7.3.4). The holomorphic sectional curvatures of the Weil–Petersson metric are negative on `T(Γ)`:
`K_p(V) < 0` for every `h`-unit vector `V`. -/
theorem thm7_17_c {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hg : 1 < g) (hΓ : IsFuchsian Γ)
    (hco : IsCocompact Γ) {φs : Fin (3 * g - 3) → ℂ → ℂ} (hφ : ∀ j, φs j ∈ A2 Γ) (hli : LinearIndependent ℂ φs)
    (hspan : ∀ φ ∈ A2 Γ, φ ∈ Submodule.span ℂ (range φs)) {D : Set (Fin (3 * g - 3) → ℂ)} (hD : IsOpen D)
    (h0 : (0 : Fin (3 * g - 3) → ℂ) ∈ D) (hν : ∀ t ∈ D, ∃ m : BeltramiGamma Γ, m.1.1 = nuOf φs t)
    (h : (Fin (3 * g - 3) → ℂ) → Fin (3 * g - 3) → Fin (3 * g - 3) → ℂ)
    (hh : ∀ t ∈ D, ∀ j k, IsWPInnerProduct Γ (nuOf φs t) (harmBeltrami (φs j)) (harmBeltrami (φs k)) (h t j k))
    (hsm : ContDiffOn ℝ ∞ h D) :
    ∀ t ∈ D, ∀ V : Fin (3 * g - 3) → ℂ, ∑ j, ∑ k, h t j k * V j * conj (V k) = 1 → (holSectional h t V).re < 0 := by
  sorry

end ImayoshiTaniguchi1992
