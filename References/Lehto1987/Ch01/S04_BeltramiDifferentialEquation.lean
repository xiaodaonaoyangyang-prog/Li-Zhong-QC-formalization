import References.Lehto1987.Ch01.S03_AnalyticDefinitionOfQuasiconformalMappings
import References.LehtoVirtanen1973.Ch05.S01_ExistenceTheorem
import References.LehtoVirtanen1973.Ch03.S07_HilbertTransformation
import LiZhongQC.Ch02.S11b_HilbertNorm
import LiZhongQC.Ch02.S13_Representation

/-!
# Lehto, Chapter I §4: Beltrami differential equation

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §4 (`full.md`
P1:933–1204).

Conventions (see §1–§3): the complex dilatation `μ_f` of a quasiconformal mapping is LV's
`LehtoVirtanen1973.complexDilatationLV`, a function on the finite plane, determined almost everywhere; `‖μ‖∞` is
`eLpNorm μ ⊤` of the area measure (on the finite part of the domain), the book's hypotheses `‖μ‖∞ < 1`, `|μ| ≤ k`
a.e. being read literally (`∀ᵐ`); "measurable" is `AEStronglyMeasurable`. The generalized derivatives `f_z`, `f_{z̄}`
of a function with `L^p`-derivatives are `LiZhongQC.genDz`, `LiZhongQC.genDzbar` of its partial derivatives
`LiZhongQC.partialX`, `LiZhongQC.partialY`, as in LV III.6–7. The operators are the project's: `T` is
`LiZhongQC.cauchyT` (the integral (4.6)), `H` on `L^p` is `LiZhongQC.hilbertH`, on `C_0^∞` the principal value
`LiZhongQC.hilbertHSmooth`, and `‖H‖_p` is `LiZhongQC.hilbertNorm p`. The Neumann terms `φᵢ` of (4.12) are
`LiZhongQC.beltramiIter μ (i − 1)`.

* Formula (4.1) (§4.1) — exists: `LehtoVirtanen1973.eq4_5_2` (at a finite point of differentiability with a finite
  value, (3.1) is equivalent to (K + 1)|∂̄f| ≤ (K − 1)|∂f|)
* Definition (complex dilatation `μ = ∂̄f/∂f`, §4.1) — exists: `LehtoVirtanen1973.complexDilatationLV`
* Formula (4.2) (§4.1) — exists: `LehtoVirtanen1973.eq4_5_5` (at every finite regular point with a finite value,
  where μ is defined, (K + 1)|μ| ≤ K − 1, which gives |μ| ≤ (K − 1)/(K + 1) < 1)
* Unlabelled (§4.1, P1:954–966): Borel measurability of `μ`; the geometric interpretation of `μ` — omitted:
  remarks, not cited
* Definition (Beltrami equation (4.3), `L^p`-solution, §4.2) — exists: `LehtoVirtanen1973.IsGeneralizedLpSolution`
  (L^p-derivatives and (4.3) almost everywhere)
* Theorem 4.1 (§4.2) — `thm1_4_1`
* Formula (4.4) (§4.2) — exists: `LehtoVirtanen1973.eq4_5_9` (the same formula for almost all z; the factor
  (∂g/|∂g|)² is e^{2i arg ∂g})
* Theorem 4.2 (§4.2, uniqueness theorem) — exists: `LehtoVirtanen1973.uniqueness_theorem` (f = φ ∘ g with φ
  conformal in g(A), i.e. f ∘ g⁻¹ = φ is conformal)
* Unlabelled (§4.2, P1:997): conversely, if `f ∘ g⁻¹` is conformal, `f` and `g` have the same complex dilatation —
  exists: `LehtoVirtanen1973.eq4_5_7` (with w = g and the conformal, hence quasiconformal, mapping f ∘ g⁻¹, whose
  composition with g is f in A)
* Formula (4.5) (§4.3, generalized Cauchy formula) — exists: `LehtoVirtanen1973.lemma3_7_1` (the same formula, the
  area integral a Cauchy principal value)
* Unlabelled (§4.3, P1:1009): a function with `L¹`-derivatives and `∂̄f = 0` a.e. is analytic — `para1_4_3_a`
* Definition (the operator `T`, (4.6), §4.3) — exists: `LiZhongQC.cauchyT` [OCR: the display (4.6)–(4.7) is lost
  in the text layer and was read from its page image]
* Formula (4.7) (§4.3) — `eq1_4_7`
* Definition (the Hilbert transformation `H`, §4.3) — exists: `LiZhongQC.hilbertHSmooth`, `LiZhongQC.hilbertH` (the
  principal value on C_0^∞ and its extension to L^p)
* Formula (4.8) (§4.3) [OCR, reconstructed] — exists: `LiZhongQC.eq11_17` (for ω of class C_0^∞: ∂Tω = Hω, and
  ∂̄Tω = ω, Tω continuously differentiable). The display (4.8) is missing from the text layer and from the page
  images; it is reconstructed from the text (P1:1029–1036) and LV III.7.3 as ∂Tω = Hω
* Formula (4.9) (§4.3, Calderón–Zygmund inequality) — exists: `LiZhongQC.eq11_16`,
  `LiZhongQC.hilbertNorm_bddAbove` (the inequality with A_p = ‖H‖_p for every ω ∈ L^p, 1 < p < ∞, and the finiteness
  of ‖H‖_p)
* Unlabelled (§4.3, P1:1051): (4.8) holds a.e. for every `ω ∈ L^p` — `para1_4_3_b`
* Unlabelled (§4.3, P1:1051): `‖H‖_p` depends continuously on `p` — exists: `LiZhongQC.hilbertNorm_continuousOn`
  (continuity on 1 < p; the norm is LiZhongQC.hilbertNorm)
* Unlabelled (§4.3, P1:1059): `H` is an isometry of `L²`, `‖H‖₂ = 1` — exists: `LiZhongQC.thm11_3_isometry`,
  `LiZhongQC.thm11_3_cor1`
* Unlabelled (§4.4, P1:1063–1086): the normalization `f(∞) = ∞`, `f(z) = z + Σ bₙz⁻ⁿ`; (4.10), (4.11), (4.14) —
  omitted: steps of the proof of Theorem 4.3; (4.11) is a hypothesis of (4.15)
* Definition (the Neumann terms `φᵢ`, (4.12), §4.4) — exists: `LiZhongQC.beltramiIter` (φᵢ is the term with index
  i − 1: μ, μHμ, μH(μHμ), …)
* Formula (4.13) (§4.4) — `eq1_4_13`
* Theorem 4.3 (§4.4, Bojarski) — `thm1_4_3`
* Formula (4.15) (§4.4) — `eq1_4_15`
* Unlabelled (§4.4, P1:1129): the partial derivatives of a quasiconformal mapping are locally in `L^p` for some
  `p > 2` — omitted: not cited (LV Theorem V.5.1)
* Theorem 4.4 (§4.5, existence theorem) — `thm1_4_4`
* Unlabelled (§4.5, P1:1141): a quasiconformal mapping with locally Hölder continuous complex dilatation is a
  diffeomorphism — `para1_4_5`
* Unlabelled (§4.5, P1:1143–1147): generalized Riemann mapping theorem; continuous `μ` need not give `C¹`
  solutions — omitted: not cited (LV Ch. V §1.4)
* Unlabelled (§4.6, P1:1151): no connection between `μₙ` and `μ` in general — omitted: a remark (LV p. 186)
* Theorem 4.5 (§4.6) — exists: `LehtoVirtanen1973.thm4_5_2` (the same statement: the limit function of the complex
  dilatations is μ almost everywhere)
* Theorem 4.6 (§4.6) — `thm1_4_6`
* Theorem 4.7 (§4.7) — `thm1_4_7`
* Formula (4.16) (§4.7) — `eq1_4_16`
* Formula (4.17) (§4.7) — `eq1_4_17`
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt unitDisc cauchyT hilbertH hilbertNorm beltramiIter partialX partialY genDz
  genDzbar dz dzbar)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap finiteMap finiteCore complexDilatationLV
  IsGeneralizedLpSolution IsHomeoOn HasLpDerivatives HasCauchyTPV maxDilatationK sphericalDist)

/-! ## §4.2 Quasiconformal mappings and the Beltrami equation -/

/-- **Theorem 4.1** (Ch. I §4.2). A homeomorphism `f` is `K`-quasiconformal if and only if `f` is an `L²`-solution of
an equation `∂̄f = μ ∂f`, where `μ` satisfies (4.2) for almost all `z`.
Modelling: `f` is a homeomorphism of the domain `A` of `ℂ̄` onto `f(A)`; `1 ≤ K` is the standing convention; `μ` is
measurable (it is the coefficient of a Beltrami equation, P1:970), and (4.2), `|μ| ≤ (K − 1)/(K + 1)`, is multiplied
by `K + 1 > 0`. -/
theorem thm1_4_1 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K : ℝ} (hA : IsDomainExt A) (hK : 1 ≤ K)
    (hf : IsHomeoOn f A (f '' A)) :
    IsKQuasiconformal f A K ↔ ∃ μ : ℂ → ℂ, AEStronglyMeasurable μ (volume.restrict (finitePart A)) ∧
      (∀ᵐ z ∂(volume.restrict (finitePart A)), (K + 1) * ‖μ z‖ ≤ K - 1) ∧ IsGeneralizedLpSolution f μ A 2 := by
  sorry

/-! ## §4.3 Singular integrals -/

/-- **Unlabelled** (Ch. I §4.3, P1:1009). A function `f` with `L¹`-derivatives in a domain `A` is analytic if
`∂̄f = 0` a.e. in `A`.
Modelling: `A` is a domain of the finite plane; `∂̄f` is the generalized derivative built from the partial
derivatives. -/
theorem para1_4_3_a {f : ℂ → ℂ} {A : Set ℂ} (hA : IsOpen A ∧ IsConnected A) (hf : HasLpDerivatives f A 1)
    (h : ∀ᵐ z ∂(volume.restrict A), genDzbar (partialX f) (partialY f) z = 0) : DifferentiableOn ℂ f A := by
  sorry

/-- **Formula (4.7)** (Ch. I §4.3). Suppose that `f` has `L¹`-derivatives in the complex plane and that `f(z) → 0` as
`z → ∞`. Then `f = T ∂̄f`.
Modelling: the book obtains (4.7) from (4.5) for the discs `|ζ| < R` by letting `R → ∞`; `T ∂̄f(z)` is read
accordingly as the limit, as `R → ∞`, of the Cauchy principal values of (4.5) over these discs
(`LehtoVirtanen1973.HasCauchyTPV`), since `∂̄f` need not be integrable against `1/(ζ − z)` over the plane.
[OCR] The display is lost in the text layer and was read from its page image. -/
theorem eq1_4_7 {f : ℂ → ℂ} (hf : HasLpDerivatives f univ 1) (hlim : Tendsto f (cocompact ℂ) (𝓝 0)) (z : ℂ) :
    ∃ L : ℝ → ℂ, (∀ R : ℝ, ‖z‖ < R → HasCauchyTPV (Metric.ball 0 R) (genDzbar (partialX f) (partialY f)) z (L R)) ∧
      Tendsto L atTop (𝓝 (f z)) := by
  sorry

/-- **Unlabelled** (Ch. I §4.3, P1:1051). For `1 < p < ∞`, (4.8) holds a.e. for every `ω ∈ L^p`: the generalized
derivatives of `Tω` are `∂̄Tω = ω` and `∂Tω = Hω`.
Modelling: `Tω` is the integral (4.6), which is taken where it exists: the integrand `ω(ζ)/(ζ − z)` is assumed
integrable for almost every `z` (it is for `p < 2`, and for `ω` with bounded support when `p > 2`). The generalized
derivatives are the distributional ones: `Tω` is locally integrable and `∬ Tω ∂̄φ = −∬ ω φ`,
`∬ Tω ∂φ = −∬ (Hω) φ` for every test function `φ ∈ C_0^∞`. -/
theorem para1_4_3_b {p : ℝ} (hp : 1 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hT : ∀ᵐ z, Integrable (fun ζ => ω ζ / (ζ - z))) :
    LocallyIntegrable (cauchyT ω) ∧ ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∫ z, cauchyT ω z * dzbar φ z) = -∫ z, ω z * φ z ∧ (∫ z, cauchyT ω z * dz φ z) = -∫ z, hilbertH ω z * φ z := by
  sorry

/-! ## §4.4 Representation of quasiconformal mappings -/

/-- **Formula (4.13)** (Ch. I §4.4). Suppose that `μ(z) = 0` if `|z| > R`, and let `φᵢ` be defined by (4.12). Then
`‖φᵢ‖_p ≤ (πR²)^{1/p} ‖H‖_p^{i−1} (‖μ‖∞)^i`.
Modelling: `μ` is a measurable Beltrami coefficient of the plane (`‖μ‖∞ < 1`, P1:970), `R > 0`, `1 < p < ∞`;
`φᵢ = beltramiIter μ (i − 1)`, written with `n = i − 1 ≥ 0`; the conclusion asserts `φᵢ ∈ L^p`, so that its norm is
the real number of the book. -/
theorem eq1_4_13 {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμ : eLpNorm μ ⊤ volume < 1) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    MemLp (beltramiIter μ n) (ENNReal.ofReal p) ∧
      (eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)).toReal ≤
        (Real.pi * R ^ 2) ^ (1 / p) * hilbertNorm p ^ n * (eLpNorm μ ⊤ volume).toReal ^ (n + 1) := by
  sorry

/-- **Theorem 4.3** (Ch. I §4.4, Bojarski). Let `f` be a quasiconformal mapping of the plane whose complex dilatation
`μ` has a bounded support and which satisfies `lim_{z → ∞} (f(z) − z) = 0`. Then `f(z) = z + Σᵢ Tφᵢ(z)`, with `φᵢ`
as in (4.12). The series is absolutely and uniformly convergent in the plane.
Modelling: `μ = complexDilatationLV f`, which vanishes a.e. outside a disc; the normalization gives `f(∞) = ∞`,
stated so that `f(z)` is the finite value `finiteMap f z`; `φᵢ = beltramiIter μ (i − 1)` (the sum starts at
index `0`). Absolute convergence: `Σ |Tφᵢ(z)|` converges at every `z`; uniform convergence: of the partial sums. -/
theorem thm1_4_3 {f : ExtPlane → ExtPlane} (hf : IsQuasiconformalMap f univ)
    (hsupp : ∃ R : ℝ, ∀ᵐ z : ℂ, R < ‖z‖ → complexDilatationLV f z = 0) (hinf : f extInf = extInf)
    (hnorm : Tendsto (fun z : ℂ => finiteMap f z - z) (cocompact ℂ) (𝓝 0)) :
    (∀ z : ℂ, Summable fun i => ‖cauchyT (beltramiIter (fun w : ℂ => complexDilatationLV f w) i) z‖) ∧
      (∀ z : ℂ, finiteMap f z = z + ∑' i, cauchyT (beltramiIter (fun w : ℂ => complexDilatationLV f w) i) z) ∧
      TendstoUniformly
        (fun N z => ∑ i ∈ Finset.range N, cauchyT (beltramiIter (fun w : ℂ => complexDilatationLV f w) i) z)
        (fun z => ∑' i, cauchyT (beltramiIter (fun w : ℂ => complexDilatationLV f w) i) z) atTop := by
  sorry

/-- **Formula (4.15)** (Ch. I §4.4). For `p > 2` with `‖μ‖∞ ‖H‖_p < 1` (4.11),
`|Tφᵢ(z)| ≤ c′_p (‖H‖_p ‖μ‖∞)^i`, where `c′_p` depends only on `p` and `R`.
Modelling: `∀ p R, ∃ c`, for all measurable `μ` with `‖μ‖∞ < 1` vanishing outside `|z| ≤ R` and satisfying (4.11);
`φᵢ = beltramiIter μ (i − 1)`, written with `n = i − 1`. -/
theorem eq1_4_15 {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, ∀ μ : ℂ → ℂ, AEStronglyMeasurable μ volume → eLpNorm μ ⊤ volume < 1 → (∀ z : ℂ, R < ‖z‖ → μ z = 0) →
      (eLpNorm μ ⊤ volume).toReal * hilbertNorm p < 1 → ∀ (n : ℕ) (z : ℂ),
        ‖cauchyT (beltramiIter μ n) z‖ ≤ c * (hilbertNorm p * (eLpNorm μ ⊤ volume).toReal) ^ (n + 1) := by
  sorry

/-! ## §4.5 Existence theorem -/

/-- **Theorem 4.4** (Ch. I §4.5, existence theorem). Let `μ` be a measurable function in a domain `A` with
`‖μ‖∞ < 1`. Then there is a quasiconformal mapping of `A` whose complex dilatation agrees with `μ` a.e.
Modelling: `μ` is given on the finite part of `A`, the point `∞` being null; `‖μ‖∞` is the essential supremum over
`A`. -/
theorem thm1_4_4 {A : Set ExtPlane} (hA : IsDomainExt A) {μ : ℂ → ℂ}
    (hμm : AEStronglyMeasurable μ (volume.restrict (finitePart A)))
    (hμ : eLpNorm μ ⊤ (volume.restrict (finitePart A)) < 1) :
    ∃ f : ExtPlane → ExtPlane, IsQuasiconformalMap f A ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart A)), complexDilatationLV f z = μ z := by
  sorry

/-- **Unlabelled** (Ch. I §4.5, P1:1141). A quasiconformal mapping whose complex dilatation is locally Hölder
continuous is a diffeomorphism.
Modelling: the complex dilatation agrees a.e. with a function `μ` which is locally Hölder continuous at the finite
points of `A`; the conclusion is stated at the finite points with finite values (`finiteCore f A`), where `f` is
continuously differentiable with nonzero Jacobian (its inverse is then continuously differentiable too). -/
theorem para1_4_5 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} (hf : IsQuasiconformalMap f A) {μ : ℂ → ℂ}
    (hμ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart A)), complexDilatationLV f z = μ z)
    (hHol : ∀ z ∈ finitePart A, ∃ U ∈ 𝓝 z, ∃ C α : ℝ, 0 < α ∧ ∀ x ∈ U, ∀ y ∈ U, ‖μ x - μ y‖ ≤ C * ‖x - y‖ ^ α) :
    ContDiffOn ℝ 1 (finiteMap f) (finiteCore f A) ∧
      ∀ z ∈ finiteCore f A, LinearMap.det (fderiv ℝ (finiteMap f) z : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
  sorry

/-! ## §4.6 Convergence of complex dilatations -/

/-- **Theorem 4.6** (Ch. I §4.6). Let `μ` and `μₙ` be measurable functions in the plane such that `‖μₙ‖∞ ≤ k < 1` and
`lim μₙ(z) = μ(z)` a.e. If `f` and `fₙ` are the quasiconformal mappings of the plane which fix the points `0, 1` and
`∞` and have the complex dilatations `μ` and `μₙ`, then `f(z) = lim fₙ(z)` uniformly in the plane in the spherical
metric.
Modelling: relational — the statement is made for every such `f` and `fₙ` (they exist and are unique by Theorems 4.4
and 4.2). -/
theorem thm1_4_6 {μ : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμm : AEStronglyMeasurable μ volume)
    (hμnm : ∀ n, AEStronglyMeasurable (μn n) volume) (hμn : ∀ n, eLpNorm (μn n) ⊤ volume ≤ ENNReal.ofReal k)
    (hlim : ∀ᵐ z : ℂ, Tendsto (fun n => μn n z) atTop (𝓝 (μ z))) {f : ExtPlane → ExtPlane}
    {fn : ℕ → ExtPlane → ExtPlane}
    (hf : IsQuasiconformalMap f univ ∧ f ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      f ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ f extInf = extInf ∧
      ∀ᵐ z : ℂ, complexDilatationLV f z = μ z)
    (hfn : ∀ n, IsQuasiconformalMap (fn n) univ ∧ fn n ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      fn n ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ fn n extInf = extInf ∧
      ∀ᵐ z : ℂ, complexDilatationLV (fn n) z = μn n z) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ExtPlane, sphericalDist (fn n z) (f z) < ε := by
  sorry

/-! ## §4.7 Decomposition of quasiconformal mappings -/

/-- **Theorem 4.7** (Ch. I §4.7). Let `f` be a quasiconformal mapping with maximal dilatation `K`, and `0 < t < 1`.
Then `f = f₂ ∘ f₁`, where `f₁` is `K^t`-quasiconformal and `f₂` is `K^{1−t}`-quasiconformal.
Modelling: `f` is a quasiconformal mapping of the domain `A` with `K(A) = K`; `f₁` is a mapping of `A`, `f₂` of
`f₁(A)`, and `f = f₂ ∘ f₁` in `A`. -/
theorem thm1_4_7 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K t : ℝ} (hf : IsQuasiconformalMap f A)
    (hK : maxDilatationK f A = ENNReal.ofReal K) (ht₀ : 0 < t) (ht₁ : t < 1) :
    ∃ f₁ f₂ : ExtPlane → ExtPlane, IsKQuasiconformal f₁ A (K ^ t) ∧ IsKQuasiconformal f₂ (f₁ '' A) (K ^ (1 - t)) ∧
      ∀ z ∈ A, f z = f₂ (f₁ z) := by
  sorry

/-- **Formula (4.16)** (Ch. I §4.7). If `μ₁` is the point on the line segment from `0` to `μ` for which
`h(0, μ₁) = t h(0, μ)`, `h` the hyperbolic distance in the unit disc, then
`(1 + |μ₁|)/(1 − |μ₁|) = ((1 + |μ|)/(1 − |μ|))^t`.
Modelling: `μ, μ₁` are points of the unit disc and `0 < t < 1`; `h` is the distance of the metric
`|dz|/(1 − |z|²)`, `Pommerenke1992.hypDistD`, whose formula is (1.1). -/
theorem eq1_4_16 {μ μ₁ : ℂ} (hμ : μ ∈ unitDisc) (hseg : μ₁ ∈ segment ℝ 0 μ) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hh : Pommerenke1992.hypDistD 0 μ₁ = t * Pommerenke1992.hypDistD 0 μ) :
    (1 + ‖μ₁‖) / (1 - ‖μ₁‖) = ((1 + ‖μ‖) / (1 - ‖μ‖)) ^ t := by
  sorry

/-- **Formula (4.17)** (Ch. I §4.7). If `f` is a `K`-quasiconformal mapping and `ε > 0` is given, then
`f = fₙ ∘ ⋯ ∘ f₂ ∘ f₁`, where each mapping `fᵢ` is `(1 + ε)`-quasiconformal.
Modelling: `F i = fᵢ ∘ ⋯ ∘ f₁` (`F 0` the identity); `fᵢ₊₁` is a `(1 + ε)`-quasiconformal mapping of `F i (A)` with
`F (i + 1) = fᵢ₊₁ ∘ F i` in `A`, and `F n = f` in `A`. -/
theorem eq1_4_17 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K : ℝ} (hf : IsKQuasiconformal f A K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (F : ℕ → ExtPlane → ExtPlane), (∀ z ∈ A, F 0 z = z) ∧
      (∀ i < n, ∃ g : ExtPlane → ExtPlane, IsKQuasiconformal g (F i '' A) (1 + ε) ∧ ∀ z ∈ A, F (i + 1) z = g (F i z)) ∧
      ∀ z ∈ A, F n z = f z := by
  sorry

end Lehto1987
