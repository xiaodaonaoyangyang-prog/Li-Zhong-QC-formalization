import References.GardinerLakic2000.Ch10.S01_MCGForCoveringGroup
import References.GardinerLakic2000.Ch06.S04_ManifoldStructure
import LiZhongQC.Ch10.S34_BersFiberSpace

/-!
# Nag, Chapter 5 §5.1: The Bers fiber space `F(G)` over `T(G)`

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 5 §5.1 (`full.md` N2:4356–4600,
folder `The Complex Analytic Theory … c10f6cd1`).

Conventions (see the root file `Nag1988.lean`): `G = Γ` is a Fuchsian group acting on `ℍ = U`; Nag's `L` is `𝕃`.
`T(G)` is identified with the Bers image `LiZhongQC.bersImage Γ ⊆ B(G)` (`GardinerLakic2000.cuspFormsL Γ`), `M(G)` is
`LiZhongQC.BeltramiGamma Γ`, `w^μ` is `LiZhongQC.normalizedSolution μ`, and `F(G)` is `LiZhongQC.BersFiberSpace Γ`.
No `ChartedSpace`/`NormedSpace` instance is put on these spaces; instead, openness, continuity and holomorphy are written
with the cusp norm (`pairNorm`, `GardinerLakic2000.cuspNorm`), in the style of `GardinerLakic2000.IsHolBMap` and
`Lehto1987.IsHolomorphicFn`.

* Definition (Bers fiber space `F(G)`, projection `F`, §5.1.1, N2:4374) — exists: `LiZhongQC.BersFiberSpace`,
  `LiZhongQC.bersDisc`, `LiZhongQC.bersImage` (the set `{(φ, z) : φ ∈ T_B(G), z ∈ D_φ}`; the projection is `Prod.fst`)
* Unlabelled (§5.1.1, N2:4392): `F(G)` is open and `F` is a holomorphic split submersion — `para5_1_1_open`
* Proposition 5.1.1 (`F(G) ≅ T(G) × U` over `T(G)`, N2:4396) — `prop5_1_1`
* Theorem 5.1.2 (a) (`ω^*` is a biholomorphic automorphism of `F(G)` over `ω^*` of `T(G)`, N2:4412) — `thm5_1_2_a`
* Theorem 5.1.2 (b) (anti-action `(ω₁ ∘ ω₂)^* = ω₂^* ∘ ω₁^*`, N2:4452) — `thm5_1_2_b`
* Theorem 5.1.2 (c) (`G` acts fiberwise, N2:4414) — `thm5_1_2_c`
* Lemma 5.1.3 (N2:4436) — `lemma5_1_3`
* Subtheorem 5.1.4 (holomorphic dependence, N2:4468) — `subthm5_1_4`
* Lemma 5.1.4 (`ω^*` is a homeomorphism, N2:4474) — `lemma5_1_4`
* Proposition 5.1.5 (holomorphy of `∂W/∂x`, N2:4500) — `prop5_1_5`
* Lemma 5.1.6 (real-analytic representatives, N2:4558) — `lemma5_1_6`
* Proposition 5.1.6 (real-analytic holomorphic families, N2:4570) — `prop5_1_6`
* Definition (`mod(G)`, extended modular group, N1:3849, recalled) — `modExtended`
* Definition (`N_qc(G)`, N1:3846, recalled) — exists: `GardinerLakic2000.qcNormalizer`
* Definition (`Mod(G) = mod(G)/G`, N1:3849, recalled) — exists: `GardinerLakic2000.mcgGamma`

Helpers (not book notions): `pairNorm`, `HasBDerivAt`, `IsBHolOn`, `IsBContOn`, `IsBBiholOn`, `IsBHomeoOn`, `IsBOpen`,
`IsHolFiberSpace`, `IsHolFiberEquiv`, `IsOmegaPullback`, `modStarFiber`, `modStarT`, `IsNormalizedConformalOnto`,
`beltramiSet`, `essNorm` (generic Banach-style predicates; see their docstrings).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Nag1988

open LiZhongQC (upperHalf lowerHalf BeltramiGamma TeichGamma bersFunctionGamma bersImage BersFiberSpace bersFiberAction
  normalizedSolution complexDilatation IsFuchsian teichSetoidGamma mobiusFn IsConformalOnto fMuSym)
open GardinerLakic2000 (cuspNorm cuspFormsL qcNormalizer)

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Banach-style predicates on spaces of functions

The concrete Banach spaces of the chapter (`B_2(L, G)`, `B_2(L, G) × ℂ`, `L^∞(U, G)`) are spaces of functions with a norm
given as a function into `ℝ≥0∞` (no normed-space instance). The following predicates are the book's notions of derivative,
holomorphy, continuity, biholomorphy and openness written for such a norm. -/

/-- The norm on `B(G) × ℂ`: the cusp norm on `𝕃` of the first coordinate plus the absolute value of the second. -/
def pairNorm (p : (ℂ → ℂ) × ℂ) : ℝ≥0∞ := cuspNorm lowerHalf p.1 + ENNReal.ofReal ‖p.2‖

/-- The (essential sup) norm on `L^∞(U, G)`: `‖μ‖_∞ = eLpNorm μ ⊤` on the plane (the coefficients vanish off `ℍ`). -/
def essNorm (μ : ℂ → ℂ) : ℝ≥0∞ := eLpNorm μ ⊤ volume

/-- The set of Beltrami coefficients `M(G) = L^∞(U, G)₁`, as functions on the plane. -/
def beltramiSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  range fun m : BeltramiGamma Γ => m.1.1

/-- **Derivative** (Banach-style, §1.6.1 / §3.2.1 recalled). `L` is a complex-linear map, bounded for the norms `nE`, `nF`,
with `nF (f (x + h) - f x - L h) = o (nE h)` as `h → 0` with `x + h ∈ U`. Modelling: for norms given as functions into
`ℝ≥0∞` on a module of functions, as in `Lehto1987.IsHolomorphicFn`; `L` is only constrained through the norms. -/
def HasBDerivAt {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] (nE : E → ℝ≥0∞)
    (nF : F → ℝ≥0∞) (U : Set E) (f : E → F) (x : E) (L : E →ₗ[ℂ] F) : Prop :=
  (∃ C : ℝ, ∀ h, nF (L h) ≤ ENNReal.ofReal C * nE h) ∧
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ h, nE h < ENNReal.ofReal δ → x + h ∈ U →
      nF (f (x + h) - f x - L h) ≤ ENNReal.ofReal ε * nE h

/-- **Holomorphic map** on `U` (Banach-style): `f` has a derivative at every point of `U` (`HasBDerivAt`). -/
def IsBHolOn {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] (nE : E → ℝ≥0∞)
    (nF : F → ℝ≥0∞) (U : Set E) (f : E → F) : Prop :=
  ∀ x ∈ U, ∃ L : E →ₗ[ℂ] F, HasBDerivAt nE nF U f x L

/-- **Continuity** on `U` for the norms `nE`, `nF` (`ε`–`δ`). -/
def IsBContOn {E F : Type*} [AddCommGroup E] [AddCommGroup F] (nE : E → ℝ≥0∞) (nF : F → ℝ≥0∞) (U : Set E)
    (f : E → F) : Prop :=
  ∀ x ∈ U, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y ∈ U, nE (y - x) < ENNReal.ofReal δ → nF (f y - f x) < ENNReal.ofReal ε

/-- **Biholomorphic map** of `U` onto `V`: a bijection `U → V`, holomorphic, with holomorphic inverse. -/
def IsBBiholOn {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] (nE : E → ℝ≥0∞)
    (nF : F → ℝ≥0∞) (U : Set E) (V : Set F) (f : E → F) : Prop :=
  BijOn f U V ∧ IsBHolOn nE nF U f ∧ ∃ g : F → E, IsBHolOn nF nE V g ∧ ∀ x ∈ U, g (f x) = x

/-- **Homeomorphism** of `U` onto `V` for the norms `nE`, `nF`: a bijection `U → V`, continuous with continuous inverse. -/
def IsBHomeoOn {E F : Type*} [AddCommGroup E] [AddCommGroup F] (nE : E → ℝ≥0∞) (nF : F → ℝ≥0∞) (U : Set E)
    (V : Set F) (f : E → F) : Prop :=
  BijOn f U V ∧ IsBContOn nE nF U f ∧ ∃ g : F → E, IsBContOn nF nE V g ∧ ∀ x ∈ U, g (f x) = x

/-- **Open set** of the Banach space `D` (a set of directions, e.g. `B(G)` or `B(G) × ℂ`): `U ⊆ D` and every point of
`U` has a norm ball of `D` around it inside `U`. -/
def IsBOpen {E : Type*} [AddCommGroup E] (nE : E → ℝ≥0∞) (D U : Set E) : Prop :=
  U ⊆ D ∧ ∀ x ∈ U, ∃ δ > (0 : ℝ), ∀ y ∈ D, nE (y - x) < ENNReal.ofReal δ → y ∈ U

/-- **Holomorphic fiber space** (§5.2.1 definition recalled in §5.1.1, N2:4662): `p : E → B` between open subsets of
Banach spaces is holomorphic, surjective and a split submersion: at every `x ∈ E` it has a derivative `L` which has a
bounded linear right inverse `R` on the tangent spaces: for every direction `v` of the base (the span of `Bbase − p x`),
`R v` is a direction of the total space (the span of `Etot − x`) and `L (R v) = v`; `R` is bounded. Openness of `E` and `B` is
a separate hypothesis (`IsBOpen`).
[CORRECTION] (AUDIT1_Nag M4, AUDIT3_Nag B7, AUDITR2_Nag R2N-2) The right inverse was asked on *all* finite-norm `v`, with
`R v` anywhere; since `HasBDerivAt` fixes `L` only on the directions of `Etot`, any bounded extension of `L` off them satisfied
the clause, whether or not `p` is a submersion. Both `v` and `R v` now range over the tangent directions. -/
def IsHolFiberSpace {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] (nE : E → ℝ≥0∞)
    (nF : F → ℝ≥0∞) (Etot : Set E) (Bbase : Set F) (p : E → F) : Prop :=
  p '' Etot = Bbase ∧ ∀ x ∈ Etot, ∃ (L : E →ₗ[ℂ] F) (R : F →ₗ[ℂ] E), HasBDerivAt nE nF Etot p x L ∧
    (∃ C : ℝ, ∀ v, nE (R v) ≤ ENNReal.ofReal C * nF v) ∧
    ∀ v ∈ Submodule.span ℂ ((fun b => b - p x) '' Bbase),
      R v ∈ Submodule.span ℂ ((fun e => e - x) '' Etot) ∧ L (R v) = v

/-- **Complex analytic equivalence of holomorphic fiber spaces** (§5.2.1, N2:4666): biholomorphisms `Fe : E₁ → E₂` and
`fb : B₁ → B₂` with `p₂ ∘ Fe = fb ∘ p₁` on `E₁`. -/
def IsHolFiberEquiv {E₁ E₂ B₁ B₂ : Type*} [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂] (nE₁ : E₁ → ℝ≥0∞) (nE₂ : E₂ → ℝ≥0∞)
    (nB₁ : B₁ → ℝ≥0∞) (nB₂ : B₂ → ℝ≥0∞) (S₁ : Set E₁) (T₁ : Set B₁) (S₂ : Set E₂) (T₂ : Set B₂) (p₁ : E₁ → B₁)
    (p₂ : E₂ → B₂) (Fe : E₁ → E₂) (fb : B₁ → B₂) : Prop :=
  IsBBiholOn nE₁ nE₂ S₁ S₂ Fe ∧ IsBBiholOn nB₁ nB₂ T₁ T₂ fb ∧ ∀ e ∈ S₁, p₂ (Fe e) = fb (p₁ e)

/-! ## The modular action on `F(G)` -/

/-- **Coefficient of `w^μ ∘ ω`** (N2:4412–4420). `ν ∈ M(G)` is the complex dilatation, a.e. on `U = ℍ`, of the composite
`w^μ ∘ ω` for the quasiconformal self-map `ω` of `U`. (The dilatation of `w^μ ∘ ω` is that of `w_μ ∘ ω`, since `w^μ`
and `w_μ` differ by a conformal map.) -/
def IsOmegaPullback (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ω : ℂ → ℂ) (μ ν : BeltramiGamma Γ) : Prop :=
  ∀ᵐ z ∂(volume.restrict upperHalf), ν.1.1 z = complexDilatation (normalizedSolution μ.1.1 ∘ ω) z

/-- **`ω^*` on `T(G)`** in Bers coordinates (N2:4416): `ω^*[μ] = [ν]`, `ν` the dilatation of `w_μ ∘ ω`. As a relation
between Bers images (`φ = φ_μ`, `ψ = φ_ν`); well definedness is part of `thm5_1_2_a`. -/
def modStarT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ω : ℂ → ℂ) (φ ψ : ℂ → ℂ) : Prop :=
  ∃ μ ν : BeltramiGamma Γ, bersFunctionGamma μ = φ ∧ bersFunctionGamma ν = ψ ∧ IsOmegaPullback Γ ω μ ν

/-- **`ω^*` on `F(G)`** (formulas (1.3), (1.4), N2:4416–4420): `ω^*([μ], z) = ([ν], z₁)` with `[ν]` as in `modStarT` and
`z₁ = w^ν ∘ ω⁻¹ ∘ (w^μ)⁻¹ (z)`. Modelling: a relation on pairs (no inverse functions are used): `z = w^μ(u)`,
`ω y = u` and `z₁ = w^ν(y)` for some `u, y ∈ ℍ`, for representatives `μ, ν` of the two Bers coordinates. That it is the
graph of a function independent of the representatives is the content of `thm5_1_2_a` and `lemma5_1_3`. -/
def modStarFiber (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ω : ℂ → ℂ) (p q : (ℂ → ℂ) × ℂ) : Prop :=
  ∃ μ ν : BeltramiGamma Γ, bersFunctionGamma μ = p.1 ∧ bersFunctionGamma ν = q.1 ∧ IsOmegaPullback Γ ω μ ν ∧
    ∃ u ∈ upperHalf, ∃ y ∈ upperHalf, ω y = u ∧ p.2 = normalizedSolution μ.1.1 u ∧ q.2 = normalizedSolution ν.1.1 y

/-- **Extended modular group `mod(G) = N_qc(G)/(N_qc(G) ∩ Q₀(G))`** (N1:3849, recalled): the quasiconformal self-maps of
`U` normalizing `G`, modulo those with the same boundary values on `ℝ` (the boundary maps `GardinerLakic2000.qcBdry`, in
`ℂ̂`). Near miss `GardinerLakic2000.mcgGamma`, which is the
further quotient by `Γ` (Nag's `Mod(G) = mod(G)/G`). Modelling: classes of boundary values, as a `Quot` of `N_qc(G)`. -/
def modExtended (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quot fun h₁ h₂ : qcNormalizer Γ => ∀ x : ℝ, GardinerLakic2000.qcBdry h₁.1 ((x : ℂ) : LiZhongQC.ExtPlane) =
    GardinerLakic2000.qcBdry h₂.1 ((x : ℂ) : LiZhongQC.ExtPlane)

/-- A normalized conformal map between two (quasi)disks `U`, `V ⊆ ℂ`: conformal of `U` onto `V`, with continuous boundary
extension fixing `0`, `1`, `∞` (`g 0 = 0`, `g 1 = 1`, `g z → ∞` as `z → ∞` in `closure U`). Modelling: `∞` is handled by
the filter `cobounded ℂ ⊓ 𝓟 (closure U)`. -/
def IsNormalizedConformalOnto (U V : Set ℂ) (g : ℂ → ℂ) : Prop :=
  IsConformalOnto g U V ∧ ContinuousOn g (closure U) ∧ g 0 = 0 ∧ g 1 = 1 ∧
    Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 (closure U)) (Bornology.cobounded ℂ)

/-! ## §5.1 -/

/-- **Unlabelled claim** (§5.1.1, N2:4392). `F(G)` is open in `T(G) × ℂ` (here: in `B(G) × ℂ`, `T_B(G)` being open in
`B(G)`), and `F : F(G) → T(G)` is a holomorphic split submersion. Modelling: `T(G)` carries no topology instance; it is
identified with the Bers image, open in `B(G)` (Bers' theorem, recalled in Nag Ch. 3), so openness in `T(G) × ℂ` is
openness in `B(G) × ℂ`, written with `pairNorm`. -/
theorem para5_1_1_open (hΓ : IsFuchsian Γ) :
    IsBOpen pairNorm (cuspFormsL Γ ×ˢ univ) (BersFiberSpace Γ) ∧
      IsHolFiberSpace pairNorm (cuspNorm lowerHalf) (BersFiberSpace Γ) (bersImage Γ) Prod.fst := by
  sorry

/-- **Proposition 5.1.1** (Ch. 5 §5.1.1). `F(G)` is homeomorphic to `T(G) × U` by a homeomorphism commuting with the
projections to `T(G)`. Modelling: the topology of `F(G)` is that of `B(G) × ℂ` (`pairNorm`); `U = ℍ`. -/
theorem prop5_1_1 (hΓ : IsFuchsian Γ) :
    ∃ H : (ℂ → ℂ) × ℂ → (ℂ → ℂ) × ℂ, IsBHomeoOn pairNorm pairNorm (bersImage Γ ×ˢ upperHalf) (BersFiberSpace Γ) H ∧
      ∀ p ∈ bersImage Γ ×ˢ upperHalf, (H p).1 = p.1 := by
  sorry

/-- **Theorem 5.1.2 (a)** (Ch. 5 §5.1.2). For `ω ∈ N_qc(G)`, `ω^*([μ], z) = ([ν], z₁)` (1.3)–(1.4) is a well-defined
biholomorphic automorphism of `F(G)`, lying over the modular transformation `ω^*` of `T(G)`, and depending only on the
class of `ω` in `mod(G)` (the boundary values of `ω` on `ℝ`). Modelling: `modStarFiber` is the graph of the automorphism. -/
theorem thm5_1_2_a (hΓ : IsFuchsian Γ) {ω : ℂ → ℂ} (hω : ω ∈ qcNormalizer Γ) :
    ∃ Ω : (ℂ → ℂ) × ℂ → (ℂ → ℂ) × ℂ, IsBBiholOn pairNorm pairNorm (BersFiberSpace Γ) (BersFiberSpace Γ) Ω ∧
      (∀ p ∈ BersFiberSpace Γ, modStarFiber Γ ω p (Ω p)) ∧
      ∀ ω' ∈ qcNormalizer Γ, (∀ x : ℝ, GardinerLakic2000.qcBdry ω' ((x : ℂ) : LiZhongQC.ExtPlane) =
        GardinerLakic2000.qcBdry ω ((x : ℂ) : LiZhongQC.ExtPlane)) →
        ∀ p ∈ BersFiberSpace Γ, modStarFiber Γ ω' p (Ω p) := by
  sorry

/-- **Theorem 5.1.2 (b)** (Ch. 5 §5.1.2, (1.6)). `mod(G)` acts on `F(G)` as an ANTI-action (the convention is opposite to
Bers'): `(ω₁ ∘ ω₂)^* = ω₂^* ∘ ω₁^*`, i.e. `(ω₁ ∘ ω₂)^*` takes `p` to `r` iff `ω₁^*` takes `p` to some `q` which `ω₂^*`
takes to `r`. -/
theorem thm5_1_2_b (hΓ : IsFuchsian Γ) {ω₁ ω₂ : ℂ → ℂ} (h₁ : ω₁ ∈ qcNormalizer Γ) (h₂ : ω₂ ∈ qcNormalizer Γ) :
    ∀ p ∈ BersFiberSpace Γ, ∀ r ∈ BersFiberSpace Γ,
      modStarFiber Γ (ω₁ ∘ ω₂) p r ↔ ∃ q ∈ BersFiberSpace Γ, modStarFiber Γ ω₁ p q ∧ modStarFiber Γ ω₂ q r := by
  sorry

/-- **Theorem 5.1.2 (c)** (Ch. 5 §5.1.2; proof detail N2:4676). For `g ∈ G ⊆ N_qc(G)`, `g^*` is fiber preserving: it
fixes the base point `[μ]` and acts on the fiber `U^μ` by `(g⁻¹)^μ = w^μ ∘ g⁻¹ ∘ (w^μ)⁻¹` (`bersFiberAction`). -/
theorem thm5_1_2_c (hΓ : IsFuchsian Γ) {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : g ∈ Γ) :
    ∀ p ∈ BersFiberSpace Γ, ∀ q : (ℂ → ℂ) × ℂ,
      modStarFiber Γ (mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1)) p q → q.1 = p.1 ∧ q.2 = bersFiberAction Γ g⁻¹ p.1 p.2 := by
  sorry

/-- **Lemma 5.1.3** (Ch. 5 §5.1.3). For `[μ] ∈ T(G)` and `[ω] ∈ mod(G)`, the map `g = w^ν ∘ ω⁻¹ ∘ (w^μ)⁻¹ : U^μ → U^ν`
of (1.4) is a conformal map of `U^μ` onto `U^ν`; a conformal map between these quasidisks is determined by the
normalization `0, 1, ∞ ↦ 0, 1, ∞` of its boundary extension. Hence `z ↦ z₁` depends only on `[μ]` and `[ω]` (the
boundary values of `ω`).
[CORRECTION] (AUDIT1 A2, AUDIT3_Nag B5) The book (N2:4436) says that `g` itself is the conformal map fixing `0, 1, ∞`.
On the boundary `g(0) = w^ν(ω⁻¹(0))`, which is `0` only when `ω(0) = 0`. Counterexample: `Γ = {1}`, `μ = ν = 0`,
`ω(z) = z + 1` gives `g(u) = u − 1`. So the first conjunct states only that `g` is conformal onto (no normalization). The
uniqueness conjunct (normalized maps agree) is the book's uniqueness claim. -/
theorem lemma5_1_3 (hΓ : IsFuchsian Γ) {ω : ℂ → ℂ} (hω : ω ∈ qcNormalizer Γ) (μ ν : BeltramiGamma Γ)
    (hν : IsOmegaPullback Γ ω μ ν) :
    (∃ g : ℂ → ℂ, IsConformalOnto g (normalizedSolution μ.1.1 '' upperHalf)
        (normalizedSolution ν.1.1 '' upperHalf) ∧
        ∀ u ∈ upperHalf, ∀ y ∈ upperHalf, ω y = u → g (normalizedSolution μ.1.1 u) = normalizedSolution ν.1.1 y) ∧
      (∀ g₁ g₂ : ℂ → ℂ,
        IsNormalizedConformalOnto (normalizedSolution μ.1.1 '' upperHalf) (normalizedSolution ν.1.1 '' upperHalf) g₁ →
        IsNormalizedConformalOnto (normalizedSolution μ.1.1 '' upperHalf) (normalizedSolution ν.1.1 '' upperHalf) g₂ →
        ∀ z ∈ normalizedSolution μ.1.1 '' upperHalf, g₁ z = g₂ z) ∧
      ∀ (μ' ν' : BeltramiGamma Γ) (ω' : ℂ → ℂ), teichSetoidGamma Γ μ μ' → ω' ∈ qcNormalizer Γ →
        (∀ x : ℝ, GardinerLakic2000.qcBdry ω' ((x : ℂ) : LiZhongQC.ExtPlane) =
          GardinerLakic2000.qcBdry ω ((x : ℂ) : LiZhongQC.ExtPlane)) → IsOmegaPullback Γ ω' μ' ν' →
        ∀ u ∈ upperHalf, ∀ y ∈ upperHalf, ω y = u → ∀ u' ∈ upperHalf, ∀ y' ∈ upperHalf, ω' y' = u' →
          normalizedSolution μ.1.1 u = normalizedSolution μ'.1.1 u' →
            normalizedSolution ν.1.1 y = normalizedSolution ν'.1.1 y' := by
  sorry

/-- **Subtheorem 5.1.4** (Ch. 5 §5.1.4). For `ω ∈ N_qc(G)` and fixed `z`, the map `μ ↦ w^ν ∘ ω⁻¹ ∘ (w^μ)⁻¹ (z)`
(`ν` the dilatation of `w_μ ∘ ω`) is holomorphic in `μ ∈ L^∞(U, G)₁` near any `μ₀` with `z ∈ U^{μ₀}`. Modelling: on a
`‖·‖_∞`-ball `N` around `μ₀` in `M(G)`, `z ∈ U^μ`, and a function `Z : (ℂ → ℂ) → ℂ` agreeing with the formula is
holomorphic (`IsBHolOn`) on `N`. -/
theorem subthm5_1_4 (hΓ : IsFuchsian Γ) {ω : ℂ → ℂ} (hω : ω ∈ qcNormalizer Γ) (μ₀ : BeltramiGamma Γ) {z : ℂ}
    (hz : z ∈ normalizedSolution μ₀.1.1 '' upperHalf) :
    ∃ r > (0 : ℝ), ∃ Z : (ℂ → ℂ) → ℂ,
      (∀ m : BeltramiGamma Γ, essNorm (m.1.1 - μ₀.1.1) < ENNReal.ofReal r →
        z ∈ normalizedSolution m.1.1 '' upperHalf ∧
          ∀ ν : BeltramiGamma Γ, IsOmegaPullback Γ ω m ν → ∀ u ∈ upperHalf, ∀ y ∈ upperHalf, ω y = u →
            z = normalizedSolution m.1.1 u → Z m.1.1 = normalizedSolution ν.1.1 y) ∧
      IsBHolOn essNorm (fun w : ℂ => ENNReal.ofReal ‖w‖) {μ | μ ∈ beltramiSet Γ ∧ essNorm (μ - μ₀.1.1) < ENNReal.ofReal r}
        Z := by
  sorry

/-- **Lemma 5.1.4** (Ch. 5 §5.1.4). Each `ω^*` (`ω ∈ N_qc(G)`) is a homeomorphism of `F(G)` onto itself (for the
topology of `B(G) × ℂ`). -/
theorem lemma5_1_4 (hΓ : IsFuchsian Γ) {ω : ℂ → ℂ} (hω : ω ∈ qcNormalizer Γ) :
    ∃ Ω : (ℂ → ℂ) × ℂ → (ℂ → ℂ) × ℂ, IsBHomeoOn pairNorm pairNorm (BersFiberSpace Γ) (BersFiberSpace Γ) Ω ∧
      ∀ p ∈ BersFiberSpace Γ, modStarFiber Γ ω p (Ω p) := by
  sorry

/-- **Proposition 5.1.5** (Ch. 5 §5.1.5). Let `W(t, x)` be complex valued on `{|t| < R} × (a, b)`, holomorphic in `t` for
each `x` and `C¹` in `x` for each `t`. Suppose that for every compact `K ⊂ (a, b)` there is `B_K` with
`|∂W/∂x| ≤ B_K` for all `t` and `x ∈ K`. Then `∂W/∂x` is holomorphic in `t` for each fixed `x`. Modelling: `∂W/∂x` is
`deriv (W t) x`; there is no junk value since `W t` is `C¹` on `(a, b)`. -/
theorem prop5_1_5 {R a b : ℝ} (hR : 0 < R) (hab : a < b) (W : ℂ → ℝ → ℂ)
    (hhol : ∀ x ∈ Ioo a b, DifferentiableOn ℂ (fun t : ℂ => W t x) (ball 0 R))
    (hC1 : ∀ t ∈ ball (0 : ℂ) R, ContDiffOn ℝ 1 (W t) (Ioo a b))
    (hbd : ∀ K : Set ℝ, K ⊆ Ioo a b → IsCompact K →
      ∃ B : ℝ, ∀ t ∈ ball (0 : ℂ) R, ∀ x ∈ K, ‖deriv (W t) x‖ ≤ B) :
    ∀ x ∈ Ioo a b, DifferentiableOn ℂ (fun t : ℂ => deriv (W t) x) (ball 0 R) := by
  sorry

/-- **Lemma 5.1.6** (Ch. 5 §5.1.6). Every `[μ] ∈ T(G)` has a real-analytic representative `μ` (on `U = ℍ`). -/
theorem lemma5_1_6 (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    ∃ ν : BeltramiGamma Γ, teichSetoidGamma Γ μ ν ∧ AnalyticOnNhd ℝ ν.1.1 upperHalf := by
  sorry

/-- **Proposition 5.1.6** (Ch. 5 §5.1.6). Let `t ↦ σ_t ∈ L^∞(U, G)₁` be holomorphic on `|t| < R`. Then there are
`0 < R₀ ≤ R` and a holomorphic family `t ↦ μ_t` on `|t| < R₀` such that (i) `μ_t(z)` is real-analytic in `z ∈ U`,
(ii) `μ_t` and its `z, z̄`-partials (all real derivatives of every order) are bounded on compact `z`-sets, independently of
`t`, and (iii) `[μ_t] = [σ_t]` in `T(G)`. Modelling: the order `n` of the book's (ii) is unspecified in the OCR; it is read as
"every order `n`, with one `R₀`" (the Ahlfors–Weill construction gives all orders at once). [OCR?] -/
theorem prop5_1_6 (hΓ : IsFuchsian Γ) {R : ℝ} (hR : 0 < R) (σ : ℂ → BeltramiGamma Γ)
    (hσ : IsBHolOn (fun t : ℂ => ENNReal.ofReal ‖t‖) essNorm (ball 0 R) fun t => (σ t).1.1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ R₀ ≤ R ∧ ∃ μ : ℂ → BeltramiGamma Γ,
      IsBHolOn (fun t : ℂ => ENNReal.ofReal ‖t‖) essNorm (ball 0 R₀) (fun t => (μ t).1.1) ∧
      (∀ t ∈ ball (0 : ℂ) R₀, AnalyticOnNhd ℝ (μ t).1.1 upperHalf) ∧
      (∀ n : ℕ, ∀ K : Set ℂ, K ⊆ upperHalf → IsCompact K →
        ∃ B : ℝ, ∀ t ∈ ball (0 : ℂ) R₀, ∀ z ∈ K, ‖iteratedFDeriv ℝ n (μ t).1.1 z‖ ≤ B) ∧
      ∀ t ∈ ball (0 : ℂ) R₀, teichSetoidGamma Γ (μ t) (σ t) := by
  sorry

end Nag1988
