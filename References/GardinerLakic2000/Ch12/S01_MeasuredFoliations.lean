import References.GardinerLakic2000.Ch11.S07_TwoDirections

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.1 Definition of a measured foliation (with the chapter introduction)

Chapter 12 *Measured foliations*; source `teichmuller.txt`, lines 8822–8997.

* Definition (essential simple closed curve: the elements of `𝒮`, l. 8936) — `IsEssentialLoop`
* Definition (measured foliation, l. 8900–8920) — `IsMeasuredFoliation`
* Definition (height `h_v(γ)` and `h_v[γ]`, l. 8922–8932) — `folLength`, `folHeight`
* Definition (measure equivalence, l. 8934) — `AreMeasureEquiv`
* Definition (`h_φ[γ]`, the height for a quadratic differential, l. 8957–8963, 8976–8982) — `imLengthOn`,
  `imLengthLoop`, `qdHeight`, `qdHeightSimple`
* Theorem 1 (Hubbard–Masur, l. 8974) — `thm12_1_a` (existence and uniqueness), `thm12_1_b` (`Φ` a homeomorphism)
* Formula (12.5) (the Dirichlet problem `M(|dv|)`, l. 8986) — `IsContinuousQD`, `dirichletM`
* Theorem 2 (the Dirichlet principle, l. 8990) — `thm12_2`
* Theorem 3 (injectivity of the heights map, l. 8994) — `thm12_3`

Not items (DESIGN §3): the introduction (l. 8822–8895: (12.1)–(12.3), the extremal length of a foliation, the
product functional, translation lengths; motivation, not cited later); `𝓜𝓕` and the heights map `h*` as objects
(l. 8936–8948; the quotient is not formed, see below); the map `Φ` of (12.4), written out where used.

**Modelling (calibration D0.2–D0.4).** Surfaces of finite analytic type are batch B's `IsFiniteAnalyticType` with a
`LiZhongQC.FiniteTypeStructure` `F` (the closed surface `F.X`, the punctures `F.P`). There is no foliation or
loop-height notion in `LiZhongQC`, hence the new definitions. A measured foliation is a plain predicate on an atlas
`(Uᵢ, vᵢ)` with singular set `Sing ⊆ F.X` and orders `k`; "measure equivalence" is "equal heights on every essential
simple loop" (a relation, not a type). Heights of foliations are total variations along chart pieces
(`eVariationOn`; the `vᵢ` are continuous by the local models). Heights of quadratic differentials integrate
`|Im(√φ dz)|` along Lipschitz chart pieces, as `LiZhongQC.phiLengthOn` integrates `|φ|^{1/2}|dz|`; the square root is
the principal `(·)^{1/2}`, and `|Im(·)|` does not depend on the branch. "`Φ` is a homeomorphism" is read sequentially
(norm convergence in the finite-dimensional `A(Ṙ)` iff convergence of all heights) [reading]. `A(Ṙ)` is Part A's
`integrableHolQDSet R` (finite norm is equivalent to at most simple poles at the punctures, batch B's
`para4_1_simple_poles`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop FreelyHomotopic IsHolQuadDiff quadDiffNorm surfaceIntegral IsDiffFamily HasGenPartials IsKQC)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§12.1, l. 8936). An essential simple closed curve: simple, not homotopically trivial and not
homotopic to a puncture (its free homotopy class is an element of `𝒮`). -/
def IsEssentialLoop (β : Loop R) : Prop :=
  IsSimpleLoop β ∧ ¬ IsTrivialLoop β ∧ ¬ IsPeripheralLoop β

/-- **Definition** (measured foliation, §12.1, l. 8900–8920). `(U, v)` is a measured foliation `|dv|` on `Ṙ = F.X ∖ F.P`
with singular points `Sing` and orders `k`:
* (l. 8900) the `Uᵢ` are open and cover `Ṙ` minus the singular points;
* (1, l. 8903) on overlaps `vᵢ = ±vⱼ + const` locally;
* (l. 8900) each `vᵢ` has locally `L²` first partial derivatives (in charts);
* (2, l. 8904–8908) at each point `q` of the closed surface there are a neighbourhood `V` and a quasiconformal chart
  `ζ` (`ζ(q) = 0`) with `|dvᵢ| = |Im(ζ^{k/2} dζ)|`: `vᵢ = ±Im h(ζ) + c` locally, `h′² = ζ^k` (a branch of a primitive of
  `ζ^{k/2}`);
* (3, l. 8916) `k = 0` if `q` is not singular; (l. 8918) `k > 0` if `q` is singular and not a puncture; (l. 8920)
  `k ≥ −1`, `k ≠ 0` if `q` is a singular puncture. -/
def IsMeasuredFoliation {g n : ℕ} (F : LiZhongQC.FiniteTypeStructure R g n 0) {ι : Type*} (U : ι → Set R)
    (v : ι → R → ℝ) (Sing : Set F.X.carrier) (k : F.X.carrier → ℤ) : Prop :=
  Sing.Finite ∧ (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = (F.ι ⁻¹' Sing)ᶜ ∧
    (∀ i j, ∀ x ∈ U i ∩ U j, ∃ s c : ℝ, (s = 1 ∨ s = -1) ∧ ∀ᶠ y in 𝓝 x, v i y = s * v j y + c) ∧
    (∀ i, ∀ x : R, ∃ gx hx : ℂ → ℂ, HasGenPartials (fun z => (v i ((chartAt ℂ x).symm z) : ℂ)) gx hx
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U i) 2) ∧
    (∀ q : F.X.carrier, ∃ (V : Set F.X.carrier) (ζ : F.X.carrier → ℂ), IsOpen V ∧ q ∈ V ∧ ζ q = 0 ∧
      InjOn ζ V ∧ ContinuousOn ζ V ∧ IsOpen (ζ '' V) ∧
      (∀ x : F.X.carrier, ∃ K : ℝ,
        IsKQC (fun z => ζ ((chartAt ℂ x).symm z)) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' V) K) ∧
      ∀ i, ∀ y ∈ U i, F.ι y ∈ V → ∃ (s c : ℝ) (h : ℂ → ℂ), (s = 1 ∨ s = -1) ∧
        (∀ᶠ w in 𝓝 (ζ (F.ι y)), DifferentiableAt ℂ h w ∧ deriv h w ^ 2 = w ^ k q) ∧
        ∀ᶠ y' in 𝓝 y, v i y' = s * (h (ζ (F.ι y'))).im + c) ∧
    (∀ q, q ∉ Sing → k q = 0) ∧ (∀ q ∈ Sing, q ∉ (F.P : Set F.X.carrier) → 0 < k q) ∧
    ∀ q ∈ Sing, q ∈ (F.P : Set F.X.carrier) → -1 ≤ k q ∧ k q ≠ 0

/-- **Definition** (height of an arc, §12.1, l. 8922). `h_v(γ) = ∫_γ |dv|`: the infimum, over the subdivisions of
`[0, 1]` into pieces lying in atlas sets `U_{i_k}`, of the sum of the total variations of `v_{i_k} ∘ γ` on the
pieces (`⊤` if there is no such subdivision). -/
def folLength {ι : Type*} (U : ι → Set R) (v : ι → R → ℝ) (β : Loop R) : ℝ≥0∞ :=
  ⨅ (m : ℕ) (τ : Fin (m + 1) → ℝ) (j : Fin m → ι)
    (_ : τ 0 = 0 ∧ τ (Fin.last m) = 1 ∧ Monotone τ ∧
      ∀ l : Fin m, β.2.extend '' Icc (τ l.castSucc) (τ l.succ) ⊆ U (j l)),
    ∑ l : Fin m, eVariationOn (fun t => v (j l) (β.2.extend t)) (Icc (τ l.castSucc) (τ l.succ))

/-- **Definition** (height of a homotopy class, §12.1, l. 8928–8932). `h_v[γ] = inf h_v(γ′)` over the simple closed
curves `γ′` freely homotopic to `γ`. -/
def folHeight {ι : Type*} (U : ι → Set R) (v : ι → R → ℝ) (β : Loop R) : ℝ≥0∞ :=
  ⨅ (β' : Loop R) (_ : IsSimpleLoop β' ∧ FreelyHomotopic β' β), folLength U v β'

/-- **Definition** (measure equivalence, §12.1, l. 8934). Two measured foliations are measure equivalent if they have
the same heights on every essential simple closed curve (a relation; `𝓜𝓕` is not formed as a type). -/
def AreMeasureEquiv {ι κ : Type*} (U : ι → Set R) (v : ι → R → ℝ) (U' : κ → Set R) (v' : κ → R → ℝ) : Prop :=
  ∀ β : Loop R, IsEssentialLoop β → folHeight U v β = folHeight U' v' β

/-- **Definition** (§12.1, l. 8957–8963). `∫ |Im(√φ dz)|` along `γ|[s, t]`, computed on Lipschitz chart pieces (the
pattern of `LiZhongQC.phiLengthOn`). -/
def imLengthOn (φ : R → ℂ → ℂ) {a b : R} (γ : Path a b) (s t : ℝ) : ℝ≥0∞ :=
  ⨅ (m : ℕ) (τ : Fin (m + 1) → ℝ) (x : Fin m → R)
    (_ : τ 0 = s ∧ τ (Fin.last m) = t ∧ Monotone τ ∧
      ∀ i : Fin m, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (fun w : ℝ => chartAt ℂ (x i) (γ.extend w))
          (Icc (τ i.castSucc) (τ i.succ))),
    ∑ i : Fin m, ∫⁻ w in Ioo (τ i.castSucc) (τ i.succ),
      ENNReal.ofReal |((φ (x i) (chartAt ℂ (x i) (γ.extend w))) ^ (1 / 2 : ℂ) *
        deriv (fun w' : ℝ => chartAt ℂ (x i) (γ.extend w')) w).im|

/-- `∫_β |Im(√φ dz)|` for a closed curve `β`. -/
def imLengthLoop (φ : R → ℂ → ℂ) (β : Loop R) : ℝ≥0∞ := imLengthOn φ β.2 0 1

/-- **Definition** (§12.1, l. 8957–8963). `h_φ[γ]`: the infimum of `∫ |Im(√φ dz)|` over the closed curves freely
homotopic to `γ`. -/
def qdHeight (φ : R → ℂ → ℂ) (β : Loop R) : ℝ≥0∞ :=
  ⨅ (β' : Loop R) (_ : FreelyHomotopic β' β), imLengthLoop φ β'

/-- **Definition** (§12.1, l. 8976–8982). `h_ψ[γ]` with the infimum over the simple closed curves homotopic to `γ`
(the side conditions of (12.5)). -/
def qdHeightSimple (ψ : R → ℂ → ℂ) (β : Loop R) : ℝ≥0∞ :=
  ⨅ (β' : Loop R) (_ : IsSimpleLoop β' ∧ FreelyHomotopic β' β), imLengthLoop ψ β'

/-- Helper for (12.5) (l. 8976). A continuous quadratic differential: a `(2, 0)` chart family, continuous in charts. -/
def IsContinuousQD (ψ : R → ℂ → ℂ) : Prop :=
  IsDiffFamily 2 0 ψ ∧ ∀ x : R, ContinuousOn (ψ x) (chartAt ℂ x).target

/-- **Formula (12.5)** (§12.1, l. 8986). `M(|dv|) = inf ∬ |ψ|` over the continuous quadratic differentials `ψ` with
`h_ψ[γ] ≥ h_v[γ]` for all `γ ∈ 𝒮`. -/
def dirichletM {ι : Type*} (U : ι → Set R) (v : ι → R → ℝ) : ℝ≥0∞ :=
  ⨅ (ψ : R → ℂ → ℂ) (_ : IsContinuousQD ψ ∧
      ∀ β : Loop R, IsEssentialLoop β → folHeight U v β ≤ qdHeightSimple ψ β), quadDiffNorm ψ

variable [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 1** (Hubbard–Masur, §12.1, l. 8974), existence and uniqueness. Given a measured foliation `|dv|` on `Ṙ`
(and the complex structure of `Ṙ`), there is a unique `φ ∈ A(Ṙ) ∖ {0}` whose horizontal foliation
`|Im(√φ dz)|` is measure equivalent to `|dv|`. -/
theorem thm12_1_a {g n : ℕ} (hR : IsFiniteAnalyticType R g n) (F : LiZhongQC.FiniteTypeStructure R g n 0)
    {ι : Type*} {U : ι → Set R} {v : ι → R → ℝ} {Sing : Set F.X.carrier} {k : F.X.carrier → ℤ}
    (hv : IsMeasuredFoliation F U v Sing k) :
    ∃! φ : R → ℂ → ℂ, φ ∈ integrableHolQDSet R ∧ φ ≠ 0 ∧
      ∀ β : Loop R, IsEssentialLoop β → qdHeight φ β = folHeight U v β := by
  sorry

/-- **Theorem 1** (Hubbard–Masur, §12.1, l. 8974), the homeomorphism. `Φ : A(Ṙ) ∖ {0} → 𝓜𝓕` is a homeomorphism for
the product topology on heights: for `φₙ, φ ∈ A(Ṙ) ∖ {0}`, `‖φₙ − φ‖ → 0` if and only if `h_{φₙ}[γ] → h_φ[γ]` for
every `γ ∈ 𝒮` (surjectivity is `thm12_1_a`) [reading]. -/
theorem thm12_1_b {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φs : ℕ → R → ℂ → ℂ} {φ : R → ℂ → ℂ}
    (hφs : ∀ m, φs m ∈ integrableHolQDSet R ∧ φs m ≠ 0) (hφ : φ ∈ integrableHolQDSet R) (hφ0 : φ ≠ 0) :
    Tendsto (fun m => quadDiffNorm (φs m - φ)) atTop (𝓝 0) ↔
      ∀ β : Loop R, IsEssentialLoop β → Tendsto (fun m => qdHeight (φs m) β) atTop (𝓝 (qdHeight φ β)) := by
  sorry

/-- **Theorem 2** (the Dirichlet principle, §12.1, l. 8990). For a measured foliation `|dv|` on `Ṙ` of finite
analytic type, the infimum (12.5) is realized by a unique quadratic differential `φ`; it is holomorphic on `Ṙ` with at
most simple poles at the punctures (`φ ∈ A(Ṙ)`), and `h_φ[γ] = h_v[γ]` for every `γ ∈ 𝒮`. -/
theorem thm12_2 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) (F : LiZhongQC.FiniteTypeStructure R g n 0)
    {ι : Type*} {U : ι → Set R} {v : ι → R → ℝ} {Sing : Set F.X.carrier} {k : F.X.carrier → ℤ}
    (hv : IsMeasuredFoliation F U v Sing k) :
    ∃ φ : R → ℂ → ℂ, φ ∈ integrableHolQDSet R ∧ IsContinuousQD φ ∧
      (∀ β : Loop R, IsEssentialLoop β → folHeight U v β ≤ qdHeightSimple φ β) ∧
      quadDiffNorm φ = dirichletM U v ∧
      (∀ β : Loop R, IsEssentialLoop β → qdHeight φ β = folHeight U v β) ∧
      ∀ ψ : R → ℂ → ℂ, IsContinuousQD ψ → (∀ β : Loop R, IsEssentialLoop β → folHeight U v β ≤ qdHeightSimple ψ β) →
        quadDiffNorm ψ = dirichletM U v → ∀ x : R, EqOn (ψ x) (φ x) (chartAt ℂ x).target := by
  sorry

/-- **Theorem 3** (injectivity of the heights map, §12.1, l. 8994). The map `A(Ṙ) → ℝ^𝒮`, `φ ↦ (h_φ[γ])_{γ ∈ 𝒮}`, is
injective. -/
theorem thm12_3 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hψ : ψ ∈ integrableHolQDSet R) (h : ∀ β : Loop R, IsEssentialLoop β → qdHeight φ β = qdHeight ψ β) :
    φ = ψ := by
  sorry

end GardinerLakic2000
