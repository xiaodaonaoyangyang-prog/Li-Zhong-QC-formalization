import References.Lehto1987.Ch05.S06_TeichmullerSpaceOfATorus
import References.GardinerLakic2000.Ch03.S02_PoincareThetaSeries

/-!
# Lehto, Chapter V §7: Extremal mappings of Riemann surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §7 (`full.md`
P2:994–1463).

Conventions (see §3–§5). Lehto takes the unit disc `D` as universal covering surface. Here the project's model is
used: `ℍ`, with `G = Γ ≤ SL(2, ℝ)` Fuchsian and acting freely, and a measurable fundamental domain `F` of `Γ`
(`LiZhongQC.IsFundamentalDomainH`) for the Dirichlet region `N`. The spaces and norms are the existing ones:
- `L^∞(G)` is `GardinerLakic2000.beltramiSpaceGamma`;
- `L¹(G)` is `GardinerLakic2000.integrableAutomorphicL1`;
- `A(G)` is `LiZhongQC.integrableAutomorphicQD`, with the norm `‖φ‖ = ∫_F |φ|` (`LiZhongQC.phiArea φ F`);
- the pairing is `LiZhongQC.beltramiPairing F`, and `‖μ‖*_G` is `LiZhongQC.hamiltonNorm`;
- `‖μ‖∞` over `ℍ` is `LiZhongQC.beltramiNormH`;
- extremality in a class of `T_S` is `LiZhongQC.IsExtremalModBoundary`;
- `Θ` is `GardinerLakic2000.thetaGL`, and `A(1)` is the integrable holomorphic functions on `ℍ`;
- `s_μ = S_{f_μ|E}` is the mirrored `LiZhongQC.bersFunction` on `𝕃`, with Lehto's norm `Gehring1978.hypNorm`.

* Definition (`L^∞(G)`, §7.1) — exists: `GardinerLakic2000.beltramiSpaceGamma`
* Definition (quadratic differentials of `G`, the space `L¹(G)` and its norm, §7.1) — exists:
  `GardinerLakic2000.integrableAutomorphicL1`, `LiZhongQC.phiArea`
* Unlabelled (§7.1, P2:1014): the norm does not depend on `N` — `para5_7_1_a`
* Unlabelled (§7.1, P2:1016–1022): `μ ↦ λ_μ` is an isomorphism of `L^∞(G)` onto the dual of `L¹(G)` — `para5_7_1_b`
* Definition (the space `A(G)`, §7.2) — exists: `LiZhongQC.integrableAutomorphicQD`
* Unlabelled (§7.2, P2:1026–1032): `A(G)` is closed in `L¹(G)`, hence a Banach space — `para5_7_2_a`
* Formula (7.1) (§7.2) — omitted: the mean value inequality, a step
* Definition (weak convergence in `A(G)`, §7.2) — `IsWeaklyConvergentAG`
* Formula (7.2) (§7.2) — `eq5_7_2`
* Unlabelled (§7.2, P2:1041): convergence implies weak convergence, not conversely — omitted: U−
* Unlabelled (§7.2, P2:1050): for compact `S`, `A(G)` and `Q(G)` have the same elements — `para5_7_2_b`
* Unlabelled (§7.2, P2:1052–1066): `Q(G) ⊂ A(G)` for finite area, `A(1) ⊊ Q(1)` — omitted: not cited
* Definition (Poincaré theta series `Θ`, the space `A(1)`, §7.3) — exists: `GardinerLakic2000.thetaGL`
* Theorem 7.1 (§7.3) — exists: `GardinerLakic2000.thm3_4_b`
* Formula (7.3) (§7.3) — `eq5_7_3`
* Definition (infinitesimally trivial differentials, the space `N(G)`, §7.4) — `infinitesimallyTrivial`
* Definition (trivial differentials, §7.4) — exists: `LiZhongQC.IsTrivialBeltrami`
* Unlabelled (§7.4, P2:1122–1128): the normalization of `f_μ` in the disc — omitted: the model's convention (B0.2)
* Theorem 7.2 (§7.4) — exists: `LiZhongQC.lemma36_2_kernel_orthogonal`, `LiZhongQC.lemma36_2_bers_analytic` (jointly:
  orthogonality to A(G) is the vanishing of the derivative of the Bers map at 0)
* Formula (7.4) (§7.4) — omitted: a step of the proof of Theorem 7.2
* Unlabelled (§7.4, P2:1188–1196): `Tμ = 0` in `E`; `N(G)` is the kernel of `DΛ(0)` — omitted: remarks
* Theorem 7.3 (§7.5) — `thm5_7_3`
* Formula (7.5) (§7.5) — `thm5_7_3`
* Unlabelled (§7.5, P2:1225–1236): equality in (7.5) for `z + k²/z` — omitted: an example
* Lemma 7.1 (§7.5) — `lemma5_7_1` [OCR: `42t²` is `12t²`]
* Lemma 7.2 (§7.6) — `lemma5_7_2`
* Formula (7.6) (§7.6) — omitted: a step of the proof of Lemma 7.2
* Definition (the functional `l_μ` and the norm `‖μ‖*_G`, §7.6) — exists: `LiZhongQC.beltramiPairing`,
  `LiZhongQC.hamiltonNorm`
* Theorem 7.4 (§7.6, Hamilton–Krushkal) — exists: `LiZhongQC.thm36_2_hamilton`
* Formula (7.7) (§7.6) — exists: `LiZhongQC.thm36_2_hamilton`
* Unlabelled (§7.6, P2:1334–1344, Kra): `‖Θ‖ < 1` forces an extremal `μ ≠ 0` for the trivial group out of `L^∞(G)` —
  `para5_7_6`
* Definition (Hamilton sequence, degenerate Hamilton sequence, §7.7) — `IsHamiltonSeqG`, `IsDegenerateHamiltonSeqG`
* Theorem 7.5 (§7.7, Strebel, Reich) — `thm5_7_5`
* Formula (7.8) (§7.7) — `thm5_7_5`
* Formula (7.9) (§7.7) — omitted: a step of the proof of Theorem 7.5
* Formula (7.10) (§7.7) — omitted: a step of the proof of Theorem 7.5
* Formula (7.11) (§7.7) — omitted: a step of the proof of Theorem 7.5
* Definition (Teichmüller mapping, §7.7) — `IsTeichmullerDil`
* Unlabelled (§7.7, P2:1434–1440): the geodesic ray `t ↦ [tφ̄/|φ|]`; `tφ̄/|φ|` is extremal — `para5_7_7`
* Theorem 7.6 (§7.8, Teichmüller's existence theorem) — `thm5_7_6`
* Unlabelled (§7.8, P2:1454): on a torus the extremals are Teichmüller mappings — omitted: Theorem 6.3 (`thm5_6_3`)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (toExt upperHalf lowerHalf IsUniformization IsFuchsian ActsFreely BeltramiGamma TeichGamma
  teichSetoidGamma teichDistanceGamma bersFunction phiArea integrableAutomorphicQD beltramiPairing beltramiNormH
  IsExtremalModBoundary IsFundamentalDomainH IsGammaCompatible)
open GardinerLakic2000 (beltramiSpaceGamma integrableAutomorphicL1 thetaGL IsBoundedFunctionalOn dualNormOn)
open Gehring1978 (hypNorm)

/-! ## §7.1 Dual Banach spaces -/

/-- **Unlabelled** (Ch. V §7.1, P2:1014). The `L¹`-norm `∫_N |φ|` of a quadratic differential of `G` does not depend on
the choice of the Dirichlet region (fundamental domain) `N`. -/
theorem para5_7_1_a {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F F' : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (hF' : IsFundamentalDomainH Γ F') {φ : ℂ → ℂ}
    (hφm : AEStronglyMeasurable φ (volume.restrict upperHalf))
    (hφ : ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict upperHalf),
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    phiArea φ F = phiArea φ F' := by
  sorry

/-- **Unlabelled** (Ch. V §7.1, P2:1016–1022). `μ ↦ λ_μ`, `λ_μ(φ) = ∫_N μφ`, is an isomorphism of `L^∞(G)` onto the
dual of `L¹(G)`: every bounded linear functional on `L¹(G)` is `λ_μ` for a `μ ∈ L^∞(G)`, unique a.e., with
`‖λ_μ‖ = ‖μ‖∞`. -/
theorem para5_7_1_b {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {V : (ℂ → ℂ) → ℂ}
    (hV : IsBoundedFunctionalOn (integrableAutomorphicL1 Γ F) (fun φ => phiArea φ F) V) :
    ∃ μ ∈ beltramiSpaceGamma Γ, (∀ φ ∈ integrableAutomorphicL1 Γ F, V φ = beltramiPairing F μ φ) ∧
      eLpNorm μ ⊤ (volume.restrict upperHalf) =
        ENNReal.ofReal (dualNormOn (integrableAutomorphicL1 Γ F) (fun φ => phiArea φ F) V) ∧
      ∀ ν ∈ beltramiSpaceGamma Γ, (∀ φ ∈ integrableAutomorphicL1 Γ F, V φ = beltramiPairing F ν φ) →
        ∀ᵐ z ∂(volume.restrict upperHalf), ν z = μ z := by
  sorry

/-! ## §7.2 Space of integrable holomorphic quadratic differentials -/

/-- **Unlabelled** (Ch. V §7.2, P2:1026–1032). `A(G)` is closed in `L¹(G)`: an `L¹(G)`-limit of elements of `A(G)` is
(a.e. equal to) an element of `A(G)`. -/
theorem para5_7_2_a {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φn : ℕ → ℂ → ℂ} {φ : ℂ → ℂ} (hφn : ∀ n, φn n ∈ integrableAutomorphicQD Γ F)
    (hφ : φ ∈ integrableAutomorphicL1 Γ F) (hlim : Tendsto (fun n => phiArea (φn n - φ) F) atTop (𝓝 0)) :
    ∃ ψ ∈ integrableAutomorphicQD Γ F, ∀ᵐ z ∂(volume.restrict upperHalf), ψ z = φ z := by
  sorry

/-- **Definition** (weak convergence in `A(G)`, Ch. V §7.2): the norms are uniformly bounded and the functions converge
locally uniformly in the half-plane. -/
def IsWeaklyConvergentAG (F : Set ℂ) (φn : ℕ → ℂ → ℂ) (φ : ℂ → ℂ) : Prop :=
  (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, phiArea (φn n) F ≤ C) ∧ TendstoLocallyUniformlyOn φn φ atTop upperHalf

/-- **Formula (7.2)** (Ch. V §7.2). A bounded set of `A(G)` is a normal family: every bounded sequence `φₙ` has a
subsequence converging locally uniformly to some `φ ∈ A(G)`, and `‖φ‖ ≤ liminf ‖φ_{nᵢ}‖`. -/
theorem eq5_7_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φn : ℕ → ℂ → ℂ} (hφn : ∀ n, φn n ∈ integrableAutomorphicQD Γ F)
    (hb : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, phiArea (φn n) F ≤ C) :
    ∃ (s : ℕ → ℕ) (φ : ℂ → ℂ), StrictMono s ∧ φ ∈ integrableAutomorphicQD Γ F ∧
      IsWeaklyConvergentAG F (φn ∘ s) φ ∧ phiArea φ F ≤ liminf (fun i => phiArea (φn (s i)) F) atTop := by
  sorry

/-- **Unlabelled** (Ch. V §7.2, P2:1050). If `S` is compact, `A(G)` and `Q(G)` have the same elements: a holomorphic
quadratic differential of `G` has finite `L¹`-norm if and only if it has finite hyperbolic sup norm.
Modelling: both on `ℍ` (Lehto's `D`); the sup norm is `Gehring1978.hypNorm` of `ℍ`. -/
theorem para5_7_2_b {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (haut : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    phiArea φ F < ⊤ ↔ hypNorm φ (toExt upperHalf) < ⊤ := by
  sorry

/-! ## §7.3 Poincaré theta series -/

/-- **Formula (7.3)** (Ch. V §7.3). For `μ ∈ L^∞(G)` and `f ∈ A(1)`, `∫_D μ f = ∫_N μ Θf`. -/
theorem eq5_7_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {μ : ℂ → ℂ} (hμ : μ ∈ beltramiSpaceGamma Γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfi : phiArea f upperHalf < ⊤) :
    ∫ z in upperHalf, μ z * f z = beltramiPairing F μ (thetaGL Γ f) := by
  sorry

/-! ## §7.4 Infinitesimally trivial differentials -/

/-- **Definition** (infinitesimally trivial differentials, the space `N(G)`, Ch. V §7.4): the elements of `L^∞(G)`
orthogonal to `A(G)`: `∫_N μφ = 0` for every `φ ∈ A(G)` (near miss: `LiZhongQC.IsLocallyTrivialBeltrami`, the
characterization of Theorem 7.2). -/
def infinitesimallyTrivial (Γ : Subgroup SL(2, ℝ)) (F : Set ℂ) : Set (ℂ → ℂ) :=
  {μ | μ ∈ beltramiSpaceGamma Γ ∧ ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F μ φ = 0}

/-! ## §7.5 Mappings with infinitesimally trivial dilatations -/

/-- **Theorem 7.3** (Ch. V §7.5). If `f_μ` has an infinitesimally trivial complex dilatation, then
`‖S_{f_μ|E}‖_q ≤ 6 ‖μ‖∞²` (7.5).
Modelling: mirrored (`𝕃` for `E`), Lehto's norm. -/
theorem thm5_7_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ) (hμ : μ.1.1 ∈ infinitesimallyTrivial Γ F) :
    hypNorm (bersFunction μ.1.1) (toExt lowerHalf) ≤ ENNReal.ofReal (6 * beltramiNormH μ.1.1 ^ 2) := by
  sorry

/-- **Lemma 7.1** (Ch. V §7.5). Let `ν ∈ N(G)` and `‖ν‖∞ < 2`. Then, for `0 ≤ t ≤ 1/4`, there is `σ(t) ∈ [tν]` such
that `‖σ(t)‖∞ ≤ 12t²`.
[OCR] The bound is printed `42t²`; the proof gives `½ · 24t² = 12t²`.
Modelling: `tν` as an element of `B(G)` (`tν′`). -/
theorem lemma5_7_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {ν : ℂ → ℂ} (hν : ν ∈ infinitesimallyTrivial Γ F)
    (h2 : eLpNorm ν ⊤ (volume.restrict upperHalf) < 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 4))
    (tν : BeltramiGamma Γ) (htν : tν.1.1 = fun z => (t : ℂ) * ν z) :
    ∃ σ : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) σ = Quotient.mk (teichSetoidGamma Γ) tν ∧
      beltramiNormH σ.1.1 ≤ 12 * t ^ 2 := by
  sorry

/-! ## §7.6 Complex dilatations of extremal mappings -/

/-- **Lemma 7.2** (Ch. V §7.6). Let `f^μ` be extremal in its equivalence class. If `μ − κ ∈ N(G)`, then
`‖μ‖∞ ≤ ‖κ‖∞`. -/
theorem lemma5_7_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {μ : BeltramiGamma Γ} (hμ : IsExtremalModBoundary Γ μ) {κ : ℂ → ℂ}
    (hκ : κ ∈ beltramiSpaceGamma Γ) (hN : (μ.1.1 - κ) ∈ infinitesimallyTrivial Γ F) :
    beltramiNormH μ.1.1 ≤ beltramiNormH κ := by
  sorry

/-- **Unlabelled** (Ch. V §7.6, P2:1334–1344, Kra). Let `f^μ` be extremal for its boundary values among all
quasiconformal mappings (the trivial group). If the operator `Θ : A(1) → A(G)` has norm `< 1`, then `μ ≠ 0` is not in
`L^∞(G)`.
Modelling: the norm bound `‖Θf‖ ≤ c ‖f‖`, `c < 1`, on `A(1)`. -/
theorem para5_7_6 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {c : ℝ} (hc : c < 1)
    (hΘ : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf → phiArea f upperHalf < ⊤ →
      phiArea (thetaGL Γ f) F ≤ ENNReal.ofReal c * phiArea f upperHalf)
    {μ : BeltramiGamma ⊥} (hμ : IsExtremalModBoundary ⊥ μ) (hne : ¬ ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = 0) :
    μ.1.1 ∉ beltramiSpaceGamma Γ := by
  sorry

/-! ## §7.7 Teichmüller mappings -/

/-- **Definition** (Hamilton sequence, Ch. V §7.7): `φₙ ∈ A(G)` with `‖φₙ‖ = 1` and `∫_N μφₙ → ‖μ‖∞` (near miss:
`LiZhongQC.IsHamiltonSequence`, the disc and the trivial group). -/
def IsHamiltonSeqG (Γ : Subgroup SL(2, ℝ)) (F : Set ℂ) (μ : ℂ → ℂ) (φn : ℕ → ℂ → ℂ) : Prop :=
  (∀ n, φn n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φn n) F = 1) ∧
    Tendsto (fun n => beltramiPairing F μ (φn n)) atTop (𝓝 (beltramiNormH μ : ℂ))

/-- **Definition** (degenerate Hamilton sequence, Ch. V §7.7): a Hamilton sequence converging weakly to `0`. -/
def IsDegenerateHamiltonSeqG (Γ : Subgroup SL(2, ℝ)) (F : Set ℂ) (μ : ℂ → ℂ) (φn : ℕ → ℂ → ℂ) : Prop :=
  IsHamiltonSeqG Γ F μ φn ∧ IsWeaklyConvergentAG F φn 0

/-- **Theorem 7.5** (Ch. V §7.7, Strebel, Reich). Let `μ` be an extremal complex dilatation for which no Hamilton
sequence is degenerate. If `‖μ‖∞ > 0`, then every weakly convergent Hamilton sequence tends in `L¹(G)` to the same
holomorphic quadratic differential `φ`, and `μ = ‖μ‖∞ φ̄/|φ|` (7.8) (near miss: `LiZhongQC.thm35_7`, the disc). -/
theorem thm5_7_5 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {μ : BeltramiGamma Γ} (hμ : IsExtremalModBoundary Γ μ)
    (hnd : ∀ φn : ℕ → ℂ → ℂ, ¬ IsDegenerateHamiltonSeqG Γ F μ.1.1 φn) (hpos : 0 < beltramiNormH μ.1.1) :
    ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1 ∧
      (∀ φn : ℕ → ℂ → ℂ, ∀ ψ : ℂ → ℂ, IsHamiltonSeqG Γ F μ.1.1 φn → IsWeaklyConvergentAG F φn ψ →
        Tendsto (fun n => phiArea (φn n - φ) F) atTop (𝓝 0)) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = beltramiNormH μ.1.1 * conj (φ z) / ‖φ z‖ := by
  sorry

/-- **Definition** (Teichmüller mapping, Ch. V §7.7): a quasiconformal mapping which is conformal or whose complex
dilatation is `k φ̄/|φ|` (7.8) with `0 < k < 1` and `φ ∈ A(G)`.
Modelling: the lifted model: a property of the coefficient `μ ∈ B(G)`. -/
def IsTeichmullerDil (Γ : Subgroup SL(2, ℝ)) (F : Set ℂ) (μ : ℂ → ℂ) : Prop :=
  (∀ᵐ z ∂(volume.restrict upperHalf), μ z = 0) ∨
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧ ∃ φ ∈ integrableAutomorphicQD Γ F, (¬ ∀ z ∈ upperHalf, φ z = 0) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), μ z = k * conj (φ z) / ‖φ z‖

/-- **Unlabelled** (Ch. V §7.7, P2:1434–1440). If an extremal for `[μ] ∈ T_S` is a Teichmüller mapping with `μ` of the
form (7.8), then `t ↦ [tφ̄/|φ|]`, `0 ≤ t < 1`, is a geodesic ray from the origin through `[μ]`, and `tφ̄/|φ|` is
extremal in its class for every `t`.
Modelling: for the coefficients `μₜ = tφ̄/|φ|` given in `B(G)`: each is extremal and
`τ_S(0, [μₜ]) = ½ log((1 + t)/(1 − t))`. -/
theorem para5_7_7 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    (hne : ¬ ∀ z ∈ upperHalf, φ z = 0) {μt : ℝ → BeltramiGamma Γ}
    (hμt : ∀ t ∈ Ico (0 : ℝ) 1, ∀ᵐ z ∂(volume.restrict upperHalf), (μt t).1.1 z = t * conj (φ z) / ‖φ z‖)
    (hext : ∃ t ∈ Ioo (0 : ℝ) 1, IsExtremalModBoundary Γ (μt t)) :
    ∀ t ∈ Ico (0 : ℝ) 1, IsExtremalModBoundary Γ (μt t) ∧
      teichDistanceGamma (TeichGamma.origin Γ) (Quotient.mk (teichSetoidGamma Γ) (μt t)) =
        (1 / 2) * Real.log ((1 + t) / (1 - t)) := by
  sorry

/-! ## §7.8 Extremal mappings of compact surfaces -/

/-- **Theorem 7.6** (Ch. V §7.8, Teichmüller's existence theorem). On a compact Riemann surface, a quasiconformal
mapping with the smallest maximal dilatation in its homotopy class is a Teichmüller mapping.
Modelling: genus `> 1` (the disc as universal covering surface; the torus is Theorem 6.3); in the lifted model, an
extremal `μ ∈ B(G)` satisfies `IsTeichmullerDil` (near miss: `LiZhongQC.thm27_2_existence`). -/
theorem thm5_7_6 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {μ : BeltramiGamma Γ} (hμ : IsExtremalModBoundary Γ μ) : IsTeichmullerDil Γ F μ.1.1 := by
  sorry

end Lehto1987
