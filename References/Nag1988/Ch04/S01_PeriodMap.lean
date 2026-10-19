import References.FarkasKra1992.Ch03.S03_BilinearRelations
import References.Nag1988.Ch05.S01_BersFiberSpace

/-!
# Nag, Chapter 4 §4.1: The period map and Torelli space

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 4 §4.1 (`full.md` N2:2540–3000,
folder
`The Complex Analytic Theory … c10f6cd1`; cited `N2:<line>`). New items only; the classical facts on compact surfaces
(homology bases, normalized differentials, bilinear relations) are the Farkas–Kra notions of `FarkasKra1992.Ch03`.

**Model.** `X = S` is a compact Riemann surface of genus `g ≥ 2` uniformized by a torsion-free Fuchsian group
`Γ ≤ SL(2, ℝ)` (`IsUniformization Γ p`), `M(X)` is `LiZhongQC.BeltramiGamma Γ`, `T(X) = T(g, 0)` is
`LiZhongQC.TeichGamma Γ`, with the equivalence with the marked-surface version of `LiZhongQC.TeichSpace S`
characterized as in `LiZhongQC.s33v_teichGamma_equiv_teichSpace`: the class of `μ` is the marked surface `m` iff the
normalized lift of the marking has the boundary values `f^μ` (`IsMarkingOfClass`). A canonical homology basis `(a,
b)` of
`S` is transported to a marked surface by the marking (`mapCycle`); the canonical period matrix `Π(S) = (π_ij)`,
`π_ij = ∫_{β_j} φ_i`, for the normalized basis `φ_i` of holomorphic 1-forms (`∫_{α_j} φ_i = δ_ij`) is
`IsPeriodMatrixOfMarked`; `𝔖_g` is the Siegel space `IsSiegel` (symmetric with positive definite imaginary part). **No
complex-manifold instance is put on `T(g, 0)`** (ruling): "holomorphic on `T(g, 0)`" is read through the Bers embedding,
i.e. as a Banach-holomorphic function (`Nag1988.IsBHolOn` for the cusp norm) of `bersFunctionGamma μ ∈ bersImage Γ`.
Genus `1` (`T(1, 0) = ℍ`, where `π` is the identity) has no hyperbolic uniformizing group and is not modelled. Nag's
`∬ ω`
of a `(1,1)` form is the integral of the form with `dz ∧ dz̄ = −2i dx dy`, so every pairing below carries the factor
`−2i`
relative to `dx dy`.

* Torelli's theorem (4.1.2: two compact surfaces of genus `g ≥ 1` with period matrices `(Π₀, Π₁)`, `(Π₀', Π₁')` for
  arbitrary
  homology bases with intersection matrices `J`, `J'` are equivalent iff `(Π₀, Π₁) = A (Π₀', Π₁') Σ`, `J = Σᵗ J' Σ`) —
  `IsZBasisH1`, `IsHolBasis`, `thm4_1_2`
* Proposition 4.1.3 (the Riemann bilinear relations for closed smooth 1-forms) — exists: `FarkasKra1992.prop3_2_3`
  (near miss: Farkas–Kra state it for compact Riemann surfaces with a canonical homology basis, Nag for orientable
  differentiable surfaces of genus g; every later use is on a Riemann surface)
* Corollary 4.1.3 (both sides of (1.7) vanish for holomorphic forms) — exists: `FarkasKra1992.prop3_3_1`
* 4.1.4 (every class of `T(G)` has a real-analytic Beltrami representative) — `para4_1_4`
* Definition of the period maps `π`, `#π` (4.1.1, (1.3)–(1.5)) — `mapCycle`, `IsMarkingOfClass`,
  `IsPeriodMatrixOfMarked`,
  `IsPeriodMatrixOfClass`, `periodMatrix`, `IsSiegel`
* Theorem 4.1.5 (the period map `T(g, 0) → 𝔖_g` is well defined and takes values in the Siegel space) — `thm4_1_5_a`
* Theorem 4.1.5 (the period map is holomorphic) — `matNorm`, `thm4_1_5_b`
* Theorem 4.1.5 (the rank of the derivative: `3g − 3` at non-hyperelliptic points and for `g = 2`, `2g − 1` at
  hyperelliptic
  points for `g ≥ 3`) — `IsHyperellipticRS`, `IsHyperellipticClass`, `thm4_1_5_c`
* Proposition 4.1.6 (Rauch's variational formula, (1.27)–(1.28): `d_X π_ij⟨μ⟩ = ⟨φ_i ⊗ φ_j, μ⟩`) — `IsFormLift`,
  `prop4_1_6`
* Noether's theorem (`H⁰(κ) ⊗ H⁰(κ) = H⁰(κ²)` for non-hyperelliptic `X`; 4.1.8) — omitted: classical algebraic geometry,
  quoted from Farkas–Kra, only used to count the rank in the proof of 4.1.5
* Proposition 4.1.10 (the complex structure of `T(g, 0)` is the unique one making `π` holomorphic) — omitted: there
  is no
  type-level complex structure on `T(g, 0)` to quantify over
* Exercises (4.1.4, 4.1.8, 4.1.9) and Examples — omitted: exercise
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace Nag1988

open LiZhongQC GardinerLakic2000 FarkasKra1992 Forster1981

/-! ## Torelli's theorem -/

section Torelli

variable {S S' : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S']

/-- **`c` is a `ℤ`-basis of `H₁`** (helper): every class of `H₁ = Abelianization(π₁)` is uniquely `∏ c_j ^ m_j`. -/
def IsZBasisH1 {M : Type} [TopologicalSpace M] {x₀ : M} {n : ℕ}
    (c : Fin n → Abelianization (FundamentalGroup M x₀)) : Prop :=
  ∀ h : Abelianization (FundamentalGroup M x₀), ∃! m : Fin n → ℤ, h = ∏ j, c j ^ m j

/-- **`ω` is a `ℂ`-basis of the holomorphic 1-forms** (helper). -/
def IsHolBasis {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] {g : ℕ} (om : Fin g → Form1 M) : Prop :=
  (∀ i, IsAbelianDiff1 (om i)) ∧ LinearIndependent ℂ om ∧
    ∀ w : Form1 M, IsAbelianDiff1 w → ∃ c : Fin g → ℂ, Form1.EqOn w (∑ i, c i • om i) univ

/-- **Torelli's theorem** (4.1.2, N2:2591). Let `S`, `S'` be compact Riemann surfaces of genus `g ≥ 1`; let `(Π₀, Π₁)`,
`(Π₀', Π₁')` be their period matrices (a `g × 2g` matrix `Π`, `Π_{ij} = ∫_{c_j} ω_i`) with respect to arbitrary homology
bases `c`, `c'` (with integer intersection matrices `J`, `J'`) and arbitrary bases `ω`, `ω'` of the holomorphic 1-forms.
Then `S` is biholomorphically equivalent to `S'` if and only if `Π = A Π' Σ` and `J = Σᵗ J' Σ` for some `A ∈ GL(g,
ℂ)` and
`Σ ∈ GL(2g, ℤ)`. -/
theorem thm4_1_2 [CompactSpace S] [CompactSpace S'] {g : ℕ} (hg : 1 ≤ g) (hS : HasGenus S g) (hS' : HasGenus S' g)
    {x₀ : S} {x₀' : S'} {c : Fin (2 * g) → Abelianization (FundamentalGroup S x₀)}
    {c' : Fin (2 * g) → Abelianization (FundamentalGroup S' x₀')} (hc : IsZBasisH1 c) (hc' : IsZBasisH1 c')
    {om : Fin g → Form1 S} {om' : Fin g → Form1 S'} (hom : IsHolBasis om) (hom' : IsHolBasis om')
    {J J' : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hJ : ∀ i j, IsIntersectionNumber (c i) (c j) (J i j)) (hJ' : ∀ i j, IsIntersectionNumber (c' i) (c' j) (J' i j))
    {P : Matrix (Fin g) (Fin (2 * g)) ℂ} {P' : Matrix (Fin g) (Fin (2 * g)) ℂ}
    (hP : ∀ i j, IsPeriodOf (om i) (c j) (P i j)) (hP' : ∀ i j, IsPeriodOf (om' i) (c' j) (P' i j)) :
    RSConformallyEquivalent S S' ↔
      ∃ (A : Matrix (Fin g) (Fin g) ℂ) (Sg : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ), IsUnit A.det ∧ IsUnit Sg.det ∧
        P = A * P' * Sg.map (Int.cast : ℤ → ℂ) ∧ J = (Matrix.transpose Sg) * J' * Sg := by
  sorry

end Torelli

/-! ## The period map -/

section PeriodMap

variable {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  {x₀ : S} {g : ℕ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **The siegel upper half-space `𝔖_g`** (4.1.1, N2:2552): the symmetric `g × g` complex matrices with positive
definite
imaginary part. -/
def IsSiegel (P : Matrix (Fin g) (Fin g) ℂ) : Prop := P.IsSymm ∧ (P.map Complex.im).PosDef

/-- **The homology class transported by a homeomorphism** (helper): `f_* a ∈ H₁(Y, f x₀)` for `a ∈ H₁(S, x₀)`. -/
def mapCycle {Y : Type} [TopologicalSpace Y] (f : S ≃ₜ Y) (x₀ : S) :
    Abelianization (FundamentalGroup S x₀) →* Abelianization (FundamentalGroup Y (f x₀)) :=
  Abelianization.map (FundamentalGroup.map (f : C(S, Y)) x₀)

/-- **`P` is the canonical period matrix of a marked surface** (4.1.1, (1.3)): for the marked surface `[X, f, S]` (here
the marking `m.marking : S ≃ₜ m.X.carrier`), `P_{ij} = ∫_{β_j} φ_i` with respect to the homology basis transported by
the
marking and the normalized basis `φ_i` of the holomorphic 1-forms of `m.X` (`∫_{α_j} φ_i = δ_{ij}`). -/
def IsPeriodMatrixOfMarked (x₀ : S) (a b : Fin g → Abelianization (FundamentalGroup S x₀)) (m : MarkedRS S)
    (P : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∃ ζ : Fin g → Form1 m.X.carrier, IsNormalizedBasis (fun j => mapCycle m.marking x₀ (a j)) ζ ∧
    ∀ i j, IsPeriodOf (ζ j) (mapCycle m.marking x₀ (b i)) (P i j)

/-- **The marked surface `m` is the point `[μ]` of `T(Γ)`** (as in `LiZhongQC.s33v_teichGamma_equiv_teichSpace`): `m.X`
is uniformized by a Fuchsian group `Γ'` through `p'`, and the normalized lift `F` of the marking has the boundary values
`f^μ` on `ℝ`. -/
def IsMarkingOfClass (p : UpperHalfPlane → S) (μ : BeltramiGamma Γ) (m : MarkedRS S) : Prop :=
  ∃ (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p' : UpperHalfPlane → m.X.carrier)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
    IsUniformization Γ' p' ∧ IsNormalizedLift p p' m.marking F G ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((fMuSym μ.1.1 x : ℂ) : ExtPlane)

/-- **The canonical period matrix of the class of `μ`** (relation): `P` is the canonical period matrix of a marked
surface
that is the point `[μ]` of `T(Γ)`. -/
def IsPeriodMatrixOfClass (p : UpperHalfPlane → S) (a b : Fin g → Abelianization (FundamentalGroup S x₀))
    (μ : BeltramiGamma Γ) (P : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∃ m : MarkedRS S, IsMarkingOfClass p μ m ∧ IsPeriodMatrixOfMarked x₀ a b m P

/-- **The period map** `π : T(g, 0) → 𝔖_g`, composed with the projection `μ ↦ [μ]` (a choice among the matrices of the
relation; unique by `thm4_1_5_a`). -/
noncomputable def periodMatrix (p : UpperHalfPlane → S) (a b : Fin g → Abelianization (FundamentalGroup S x₀))
    (μ : BeltramiGamma Γ) : Matrix (Fin g) (Fin g) ℂ :=
  Classical.epsilon (IsPeriodMatrixOfClass p a b μ)

/-- **4.1.4** (N2:2985). The fundamental projection `Φ : L^∞(U, G)₁ → T(G)` restricted to the real-analytic Beltrami
differentials is still onto: every point of `T(G)` has a real-analytic representative. -/
theorem para4_1_4 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (hΓ : IsFuchsian Γ) (τ : TeichGamma Γ) :
    ∃ μ : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) μ = τ ∧ AnalyticOnNhd ℝ μ.1.1 upperHalf := by
  sorry

variable [CompactSpace S]

/-- **Theorem 4.1.5, well-definedness** (N2:2701). For a compact surface of genus `g ≥ 2` uniformized by `Γ` and a
canonical
homology basis `(a, b)`: every point `[μ]` of `T(g, 0)` has exactly one canonical period matrix; it depends only on the
class of `μ`, and it lies in the Siegel space `𝔖_g`. -/
theorem thm4_1_5_a (hS : HasGenus S g) (hg : 2 ≤ g) {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {a b : Fin g → Abelianization (FundamentalGroup S x₀)}
    (hab : IsCanonicalHomologyBasis a b) :
    (∀ μ : BeltramiGamma Γ, ∃! P, IsPeriodMatrixOfClass p a b μ P) ∧
      (∀ (μ : BeltramiGamma Γ) P, IsPeriodMatrixOfClass p a b μ P → IsSiegel P) ∧
      ∀ μ ν : BeltramiGamma Γ, (teichSetoidGamma Γ).r μ ν → periodMatrix p a b μ = periodMatrix p a b ν := by
  sorry

/-- The norm on `g × g` complex matrices, `max |P_ij|` (helper, with values in `[0, ∞]`). -/
def matNorm (P : Matrix (Fin g) (Fin g) ℂ) : ℝ≥0∞ := ⨆ (i) (j), ENNReal.ofReal ‖P i j‖

/-- **Theorem 4.1.5, holomorphy** (N2:2701; the derivatives exist and are `ℂ`-linear, N2:2879–2972). The period map is
holomorphic on `T(g, 0)`, read through the Bers embedding: there is a Banach-holomorphic function `Π` on
`T_B(Γ) = bersImage Γ ⊆ B(Γ)` (`IsBHolOn` for the cusp norm) with `Π(Ψ[μ]) = π[μ]`. -/
theorem thm4_1_5_b (hS : HasGenus S g) (hg : 2 ≤ g) {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {a b : Fin g → Abelianization (FundamentalGroup S x₀)}
    (hab : IsCanonicalHomologyBasis a b) :
    ∃ Pm' : (ℂ → ℂ) → Matrix (Fin g) (Fin g) ℂ,
      (∀ μ : BeltramiGamma Γ, Pm' (bersFunctionGamma μ) = periodMatrix p a b μ) ∧
      IsBHolOn (cuspNorm lowerHalf) matNorm (bersImage Γ) Pm' := by
  sorry

/-- **Hyperelliptic surfaces** (helper): a compact surface of genus `g` with a holomorphic involution with exactly
`2g + 2`
fixed points (the hyperelliptic involution; by Riemann–Hurwitz its quotient is the sphere). -/
def IsHyperellipticRS (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] (g : ℕ) : Prop :=
  ∃ h : Y → Y, IsBiholomorphic h ∧ (∀ y, h (h y) = y) ∧ Set.ncard {y | h y = y} = 2 * g + 2

/-- **`[μ]` is a hyperelliptic point of `T(g, 0)`** (the set `H_g`): the marked surface of the class is
hyperelliptic. -/
def IsHyperellipticClass (p : UpperHalfPlane → S) (μ : BeltramiGamma Γ) (g : ℕ) : Prop :=
  ∃ m : MarkedRS S, IsMarkingOfClass p μ m ∧ IsHyperellipticRS m.X.carrier g

open scoped Classical in
/-- **Theorem 4.1.5, rank of the derivative** (N2:2701, N2:2896). Let `Π'` be the holomorphic function of
`thm4_1_5_b`. At a point `[μ]` where `Π'` has the derivative `L` (a `ℂ`-linear map of the cusp forms `B(Γ) = Q(Γ, 𝕃)`,
`LiZhongQC.automorphicQD Γ`), the rank of `L` is `3g − 3`, except at the hyperelliptic points of a surface of genus
`g ≥ 3`, where it is `2g − 1` (for `g = 2`, `2g − 1 = 3g − 3`). -/
theorem thm4_1_5_c (hS : HasGenus S g) (hg : 2 ≤ g) {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {a b : Fin g → Abelianization (FundamentalGroup S x₀)}
    (hab : IsCanonicalHomologyBasis a b) {Pm' : (ℂ → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hPm : ∀ μ : BeltramiGamma Γ, Pm' (bersFunctionGamma μ) = periodMatrix p a b μ) (μ : BeltramiGamma Γ)
    {L : (ℂ → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ}
    (hL : HasBDerivAt (cuspNorm lowerHalf) matNorm (bersImage Γ) Pm' (bersFunctionGamma μ) L) :
    Module.finrank ℂ (Submodule.map L (automorphicQD Γ)) =
      if 3 ≤ g ∧ IsHyperellipticClass p μ g then 2 * g - 1 else 3 * g - 3 := by
  sorry

/-- **The lift to `ℍ` of a 1-form on `S`** (helper): `p^* w = f(z) dz` with `f(z) = w₁(p z) · (chart ∘ p)'(z)` in the
preferred
chart at `p z`. -/
def IsFormLift (p : UpperHalfPlane → S) (w : Form1 S) (f : ℂ → ℂ) : Prop :=
  ∀ z : UpperHalfPlane, f z = w.1 (p z) (chartAt ℂ (p z) (p z)) *
    deriv (fun u : ℂ => chartAt ℂ (p z) (p (UpperHalfPlane.ofComplex u))) (z : ℂ)

/-- **Proposition 4.1.6 (Rauch's variational formula)** (N2:2735, (1.27)–(1.28)). Let `ζ` be the normalized basis of
the holomorphic
1-forms of `S`, `f_i` the lifts of `ζ_i` to `ℍ`, `F` a fundamental domain of `Γ`, `μ ∈ M(X)` a Beltrami differential and
`t ↦ ν_t` a family with `ν_t = t μ` near `t = 0`. Then `t ↦ π_{ij}[ν_t]` is differentiable at `0` with derivative
`⟨φ_i ⊗ φ_j, μ⟩ = −2i ∬_F f_i f_j μ dx dy` (`dz ∧ dz̄ = −2i dx dy`). -/
theorem prop4_1_6 (hS : HasGenus S g) (hg : 2 ≤ g) {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {a b : Fin g → Abelianization (FundamentalGroup S x₀)}
    (hab : IsCanonicalHomologyBasis a b) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {ζ : Fin g → Form1 S} (hζ : IsNormalizedBasis a ζ) {f : Fin g → ℂ → ℂ} (hf : ∀ i, IsFormLift p (ζ i) (f i))
    (μ : BeltramiGamma Γ) (ν : ℂ → BeltramiGamma Γ)
    (hν : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ᵐ z ∂(volume.restrict upperHalf), (ν t).1.1 z = t * μ.1.1 z) (i j : Fin g) :
    HasDerivAt (fun t => periodMatrix p a b (ν t) i j) ((-2 * Complex.I) * ∫ z in F, f i z * f j z * μ.1.1 z) 0 := by
  sorry

end PeriodMap

end Nag1988
