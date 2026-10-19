import References.Nag1988.Ch02.S05_FrickeCoordinatesFiniteType
import References.Nag1988.Ch05.S02_UniversalFamily
import References.Lehto1987.Ch05.S05_ComplexStructuresOnTeichmullerSpaces
import LiZhongQC.Ch11.S36_Hamilton

/-!
# Nag, Chapter 3 §3.2: Complex structures on target spaces

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 3 §3.2 (`full.md` N1:5229–5356 and
N2:1–66; folders `10dae1e9` and `c10f6cd1`, cited `N1:<line>` / `N2:<line>`).

**Model.** A *complex structure on a finite-dimensional real vector space region* `Ω ⊆ F` (here `F = ℝ^{6g-6+2n}`, the
Fricke space) compatible with its `C^k` structure is given by a set `𝒜` of charts `F ⇀ ℂ^d` (`IsComplexAtlasOn`): `C^k`
diffeomorphisms onto open sets of `ℂ^d` with holomorphic transitions; no instance is put on `Ω`. Two such structures coincide
iff the union of the two atlases is again an atlas (maximal atlases agree); this is how "unique" is read. A map `f : X → Ω`
from a complex Banach manifold `X` (modelled on `B`) is *holomorphic for `𝒜`* if its composite with every chart is
holomorphic (`IsHolWrt`); its being a `C¹` submersion onto `Ω` is `IsC1SubmersionOnto`; and `f` *induces a well-defined almost
complex structure* if the complex structure of `T_xX` pushes forward to one operator `J_y` of `T_yΩ`, independently of
`x ∈ f⁻¹(y)` (`InducesAlmostComplex`). For the application, `X` is the unit ball `L^∞(U, G)₁` (`beltramiSet Γ` with the norm
`essNorm`, the "Banach-style" predicates `IsBHolOn`, `HasBDerivAt` of Chapter 5); `F̃ = F ∘ Φ` is `Ft` below.

**Normalization.** Nag's Poincaré metric `λ_D(z)|dz|` has curvature `−4`: `λ_𝔻(z) = 1/(1 − |z|²)`, `λ_U(z) = 1/(2 Im z)`;
this is `GardinerLakic2000.poincareDensityGL`, and half of `LiZhongQC.poincareDensity` (curvature `−1`). The Bers differentials
of the upper half-plane are `v_j = φ̄_j λ_U^{-2} = 4 (Im z)² conj φ_j` (formula (2.9)).

* Definition (a map `f` induces a well-defined almost complex structure; compatible complex structure; N1:5240–5252) —
  `InducesAlmostComplex`, `IsComplexAtlasOn`, `IsHolWrt`, `IsC1SubmersionOnto`
* Lemma 3.2.1 (uniqueness of a compatible complex structure making `f` holomorphic; N1:5256) — `lemma3_2_1`
* Theorem 3.2.2 (existence of the complex structure iff `f` induces a well-defined almost complex structure; N1:5266) — `thm3_2_2`
* Section 3.2.3 (the Fricke image `Im F` has a unique compatible complex structure making `F ∘ Φ` a holomorphic submersion;
  N1:5330) — `IsFrickeHolAtlas`, `thm3_2_3` (the claim `F ∘ ξ_θ = F_θ` and the kernel computations are proof steps)
* Definition 3.2.4 (the Fricke homeomorphism pulls the structure back to `T(X)`: the canonical complex structure; N1:5348) —
  omitted: definition; in the project the complex structure of `T(G)` is read through the Bers embedding (N-D1), and
  Proposition 3.3.2 (`Ch03/S03`) identifies the two
* Proposition 3.2.5 (`Mod(X)` acts by biholomorphic automorphisms of `T(X)`; N2:19) — exists: `Lehto1987.thm5_5_6`
* Theorem 3.2.6 (Bers local coordinates `(z₁..z_N) ↦ Φ(Σ z_j v_j)`; N2:49) — `thm3_2_6`
* Remarks 1, 2 (the fibres are complex submanifolds modelled on `A₂(X)^⊥`; independence of the Fricke map; N1:5340, N2:12) —
  omitted: remarks
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (TeichGamma BeltramiGamma IsFuchsian upperHalf lowerHalf bersMapGamma bersFunctionGamma
  integrableAutomorphicQD IsFundamentalDomainH)
open GardinerLakic2000 (cuspNorm cuspFormsL)

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedSpace ℝ B] [IsScalarTower ℝ ℂ B]
  {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

variable (B) in
/-- **`f` is a surjective `C¹` submersion onto `Ω`** (§3.2.1; N1:5240): `f : X → F` is `C¹` for the underlying real structure of
the complex Banach manifold `X`, has image `Ω`, and its differential is surjective at every point. -/
def IsC1SubmersionOnto (f : X → F) (Ω : Set F) : Prop :=
  ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, F) 1 f ∧ range f = Ω ∧ ∀ x, Function.Surjective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, F) f x)

variable (B) in
/-- **`f` induces a well-defined almost complex structure on `Ω`** (§3.2.1; N1:5244): for every `y ∈ Ω` there is one real linear
operator `J_y` of the tangent space such that `d_x f ∘ i = J_y ∘ d_x f` for every `x ∈ f⁻¹(y)` (so that
`ker d_x f` is a complex subspace and `T_yΩ` inherits the same complex structure from every `x`). -/
def InducesAlmostComplex (f : X → F) (Ω : Set F) : Prop :=
  ∀ y ∈ Ω, ∃ J : F →ₗ[ℝ] F, ∀ x, f x = y → ∀ v : B,
    J (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, F) f x v) = mfderiv 𝓘(ℝ, B) 𝓘(ℝ, F) f x (Complex.I • v)

/-- **Complex structure on `Ω` compatible with the `C^k` structure** (§3.2.1; N1:5248): a set `𝒜` of charts with source in `Ω`
covering `Ω`, `C^k` diffeomorphisms onto open subsets of `ℂ^d`, with holomorphic transition maps. -/
structure IsComplexAtlasOn (Ω : Set F) (d : ℕ) (k : WithTop ℕ∞)
    (𝒜 : Set (OpenPartialHomeomorph F (EuclideanSpace ℂ (Fin d)))) : Prop where
  source_sub : ∀ c ∈ 𝒜, c.source ⊆ Ω
  cover : ∀ y ∈ Ω, ∃ c ∈ 𝒜, y ∈ c.source
  smooth : ∀ c ∈ 𝒜, ContDiffOn ℝ k c c.source ∧ ContDiffOn ℝ k c.symm c.target
  holo : ∀ c ∈ 𝒜, ∀ c' ∈ 𝒜, DifferentiableOn ℂ (c.symm.trans c') (c.symm.trans c').source

variable (B) in
/-- **`f` is holomorphic for the atlas `𝒜`** (§3.2.1): the composite of `f` with every chart is a holomorphic map of the
complex Banach manifold `X` into `ℂ^d`. -/
def IsHolWrt {d : ℕ} (f : X → F) (𝒜 : Set (OpenPartialHomeomorph F (EuclideanSpace ℂ (Fin d)))) : Prop :=
  ∀ c ∈ 𝒜, ∀ x, f x ∈ c.source →
    MDifferentiableAt 𝓘(ℂ, B) 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) (fun x => c (f x)) x

/-- **Lemma 3.2.1** (§3.2.1; N1:5256). Let `f : X → Y` be a surjective `C¹` submersion from a complex Banach manifold onto a
`2d`-dimensional real manifold `Y = Ω`. If two complex structures compatible with the `C¹` structure make `f` holomorphic, they
coincide (the union of the two atlases is an atlas); moreover `f` then induces a well-defined almost complex structure on `Ω`. -/
theorem lemma3_2_1 [IsManifold 𝓘(ℂ, B) ω X] {f : X → F} {Ω : Set F} {d : ℕ} (hd : Module.finrank ℝ F = 2 * d)
    (hf : IsC1SubmersionOnto B f Ω) {𝒜 𝒜' : Set (OpenPartialHomeomorph F (EuclideanSpace ℂ (Fin d)))}
    (h𝒜 : IsComplexAtlasOn Ω d 1 𝒜) (h𝒜' : IsComplexAtlasOn Ω d 1 𝒜') (hol : IsHolWrt B f 𝒜) (hol' : IsHolWrt B f 𝒜') :
    IsComplexAtlasOn Ω d 1 (𝒜 ∪ 𝒜') ∧ InducesAlmostComplex B f Ω := by
  sorry

/-- **Theorem 3.2.2** (§3.2.2; N1:5266). Let `f : X → Ω` be a surjective `C¹` submersion from a complex Banach manifold onto a
`2d`-dimensional `C¹` manifold. There is a complex structure on `Ω`, compatible with its `C¹` structure, making `f` holomorphic
iff `f` induces a well-defined almost complex structure on `Ω`. (The structure is unique by Lemma 3.2.1.) -/
theorem thm3_2_2 [IsManifold 𝓘(ℂ, B) ω X] {f : X → F} {Ω : Set F} {d : ℕ} (hd : Module.finrank ℝ F = 2 * d)
    (hf : IsC1SubmersionOnto B f Ω) :
    (∃ 𝒜 : Set (OpenPartialHomeomorph F (EuclideanSpace ℂ (Fin d))), IsComplexAtlasOn Ω d 1 𝒜 ∧ IsHolWrt B f 𝒜) ↔
      InducesAlmostComplex B f Ω := by
  sorry

end Generic

/-- **The complex atlas of §3.2.3**: a complex structure of dimension `d = 3g - 3 + n` on the Fricke image `Im F`, compatible with
its real analytic structure, for which `F̃ = F ∘ Φ` (`Ft`: the Fricke coordinates of a Beltrami coefficient) is a holomorphic
submersion: holomorphic on the unit ball `L^∞(U, Γ)₁` (Banach-style `IsBHolOn` for the norm `essNorm`) in every chart, with a
derivative onto `ℂ^d` at every point: every `w ∈ ℂ^d` is `L v` for a direction `v` of `L^∞(U, Γ)` (the span of
`beltramiSet Γ − μ`).
[CORRECTION] (AUDIT1_Nag M4, AUDIT3_Nag B7, AUDITR2_Nag R2N-2) `v` ranged over all finite-norm functions; `L` is fixed by
`HasBDerivAt` only on the directions of `beltramiSet Γ`, so an extension of `L` off them (e.g. integrals over compact subsets
of `𝕃`, which vanish on every `Γ`-compatible coefficient) made the clause hold for free. -/
def IsFrickeHolAtlas {Γ : Subgroup SL2R} {g n : ℕ} (G : FrickeGenerators Γ g n 0) (Ft : (ℂ → ℂ) → FrickeSpace g n 0)
    (𝒜 : Set (OpenPartialHomeomorph (FrickeSpace g n 0) (EuclideanSpace ℂ (Fin (3 * g + n - 3))))) : Prop :=
  IsComplexAtlasOn {c | ∃ μ, IsFrickeCoords G μ c} (3 * g + n - 3) ω 𝒜 ∧
    ∀ c ∈ 𝒜, IsBHolOn essNorm (fun v : EuclideanSpace ℂ (Fin (3 * g + n - 3)) => ENNReal.ofReal ‖v‖)
        {μ | μ ∈ beltramiSet Γ ∧ Ft μ ∈ c.source} (fun μ => c (Ft μ)) ∧
      ∀ μ ∈ beltramiSet Γ, Ft μ ∈ c.source → ∃ L : (ℂ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (3 * g + n - 3)),
        HasBDerivAt essNorm (fun v : EuclideanSpace ℂ (Fin (3 * g + n - 3)) => ENNReal.ofReal ‖v‖)
          {μ | μ ∈ beltramiSet Γ ∧ Ft μ ∈ c.source} (fun μ => c (Ft μ)) μ L ∧
        ∀ w, ∃ v ∈ Submodule.span ℂ ((fun ν => ν - μ) '' beltramiSet Γ), L v = w

/-- **Theorem** (§3.2.3; N1:5330). Let `X = ℍ/Γ` be of finite conformal type `(g, n)`, `2g - 2 + n > 0` (`n > 3` if `g = 0`), `G` a
Fricke system and `Ft : L^∞(U, Γ)₁ → ℝ^{6g-6+2n}` the Fricke map composed with the fundamental projection (`F̃ = F ∘ Φ`,
`Ft μ` the Fricke coordinates of `μ`). There is a complex structure of dimension `d = 3g - 3 + n` on the Fricke image `Im F`
(`IsFrickeHolAtlas`), and it is unique: any two such atlases have an atlas as union. -/
theorem thm3_2_3 {Γ : Subgroup SL2R} {g n : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n 0)
    (hχ : 0 < 2 * (g : ℤ) - 2 + n) (h0 : g = 0 → 3 < n) (G : FrickeGenerators Γ g n 0)
    (hd : Module.finrank ℝ (FrickeSpace g n 0) = 2 * (3 * g + n - 3))
    (Ft : (ℂ → ℂ) → FrickeSpace g n 0) (hFt : ∀ μ : BeltramiGamma Γ, IsFrickeCoords G μ (Ft μ.1.1)) :
    (∃ 𝒜, IsFrickeHolAtlas G Ft 𝒜) ∧ ∀ 𝒜 𝒜', IsFrickeHolAtlas G Ft 𝒜 → IsFrickeHolAtlas G Ft 𝒜' →
      IsComplexAtlasOn {c | ∃ μ, IsFrickeCoords G μ c} (3 * g + n - 3) ω (𝒜 ∪ 𝒜') := by
  sorry

/-- **Theorem 3.2.6** (Bers local coordinates; N2:49). Let `X = ℍ/Γ` be of finite type `(g, n)`, `F` a fundamental domain for `Γ`,
`φ_1, …, φ_N` (`N = 3g - 3 + n`) a basis of `A₂(X)` (the integrable holomorphic quadratic differentials on `F`) and
`v_j = 4 (Im z)² conj φ_j` on `ℍ`, `0` elsewhere (the Bers Beltrami differentials, formula (2.9)). For `(z₁, …, z_N)` in a
neighbourhood of `0 ∈ ℂ^N` the map `(z_j) ↦ Φ(Σ z_j v_j)` is a local holomorphic coordinate system of `T(X)`; read through the
Bers embedding: there are `ε > 0` and `Ψ : ℂ^N → B₂(𝕃, Γ)` with `Ψ(z) = β[Σ z_j v_j]` for `‖z‖ < ε`, biholomorphic from the ball onto an open
subset of the Bers image. -/
theorem thm3_2_6 {Γ : Subgroup SL2R} {g n : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n 0)
    (hχ : 0 < 2 * (g : ℤ) - 2 + n) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (φ : Fin (3 * g + n - 3) → ℂ → ℂ)
    (hφ : LinearIndependent ℂ φ ∧ Submodule.span ℂ (range φ) = Submodule.span ℂ (integrableAutomorphicQD Γ F)) :
    let v : Fin (3 * g + n - 3) → ℂ → ℂ := fun j z => if 0 < z.im then 4 * (z.im : ℂ) ^ 2 * conj (φ j z) else 0
    ∃ ε > (0 : ℝ), ∃ Ψ : EuclideanSpace ℂ (Fin (3 * g + n - 3)) → ℂ → ℂ,
      (∀ z : EuclideanSpace ℂ (Fin (3 * g + n - 3)), ‖z‖ < ε → ∃ μ : BeltramiGamma Γ, μ.1.1 = ∑ j, z j • v j) ∧
      (∀ (z : EuclideanSpace ℂ (Fin (3 * g + n - 3))) (μ : BeltramiGamma Γ), ‖z‖ < ε → μ.1.1 = ∑ j, z j • v j →
          Ψ z = bersMapGamma Γ (Quotient.mk _ μ)) ∧
      ∃ V : Set (ℂ → ℂ), V ⊆ LiZhongQC.bersImage Γ ∧ IsBOpen (cuspNorm lowerHalf) (cuspFormsL Γ) V ∧
        IsBBiholOn (fun v : EuclideanSpace ℂ (Fin (3 * g + n - 3)) => ENNReal.ofReal ‖v‖) (cuspNorm lowerHalf)
          (Metric.ball 0 ε) V Ψ := by
  sorry

end Nag1988
