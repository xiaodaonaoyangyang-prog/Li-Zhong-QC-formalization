import References.Lehto1987.Ch05.S02_DefinitionsOfTeichmullerSpace
import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Lehto, Chapter V §3: Teichmüller space and lifted mappings

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §3 (`full.md`
P1:6283–6358, P2:1–119).

Conventions (see §1–§2; decisions B0.2, B0.5). The lifted model of `T_S` is the project's:
- `T_S` is `LiZhongQC.TeichGamma Γ`, the classes of `μ ∈ LiZhongQC.BeltramiGamma Γ` (Beltrami coefficients on `ℍ`
  compatible with `Γ`) under `f^μ|ℝ = f^ν|ℝ`;
- `τ_S` is `LiZhongQC.teichDistanceGamma` (Lehto's ½-normalization);
- the origin is `LiZhongQC.TeichGamma.origin`.

Lehto takes the lower half-plane `H′` as covering surface and `f_μ` conformal in `H`. In the project's model the
roles are exchanged (decision B0.2): `μ` lives in `ℍ`, `f^μ = LiZhongQC.fMuSym μ`, and `f_μ =
LiZhongQC.normalizedSolution μ` is conformal in `𝕃`; the quasidiscs `A_μ`, `A′_μ` are `f_μ(𝕃)`, `f_μ(ℍ)`. The
surface-model coefficient `μ` of §2 lifts to `GardinerLakic2000.liftBeltrami p μ`. Möbius maps of `ℂ̄` are read through
`OnePoint.map`.

* Definition (`f^μ`, `f_μ`, the lifted Teichmüller space, §3.1–§3.2) — exists: `LiZhongQC.TeichGamma`,
  `LiZhongQC.teichDistanceGamma`, `LiZhongQC.fMuSym`, `LiZhongQC.normalizedSolution` (decision B0.5)
* Theorem 3.1 (§3.1) — `thm5_3_1`
* Unlabelled (§3.2, P2:6311): `G₁ ⊂ G₂` implies `T_{S₂} ⊂ T_{S₁} ⊂ T` — `para5_3_2`
* Formula (3.1) (§3.2) — `eq5_3_1`
* Unlabelled (§3.2, P1:6319–6323): Strebel's examples `τ|T_S < τ_S` — omitted: quoted
* Unlabelled (§3.3, P1:6327–6331): Lemma III.2.2 holds in `T_S` — `para5_3_3`
* Theorem 3.2 (§3.3) — `thm5_3_2`
* Lemma 3.1 (§3.3) — `lemma5_3_1`
* Theorem 3.3 (§3.4) — `thm5_3_3`
* Definition (quasiconformal deformation of a Fuchsian group, §3.4) — `IsQCDeformation`
* Unlabelled (P2:4 [OCR gap]): for `G` of the first kind the limit set of `G_μ` is the boundary of `f_μ(H′)` —
  `para5_3_4`
* Unlabelled (P2:6–10): Klein's invariant Jordan domain which is not a quasidisc; Abikoff's example — omitted: quoted
* Formula (3.2) (§3.5) — `compatReflection`
* Unlabelled (§3.5, P2:30–44): `λ ∘ g_μ = g_μ ∘ λ`, the relation (3.3), and its converse — `para5_3_5`
* Formula (3.3) (§3.5) — `para5_3_5`
* Definition (the space `X(G)` of quasisymmetric functions compatible with `G`, §3.6) — `qsXG`
* Theorem 3.4 (§3.6, Tukia, Douady–Earle) — `thm5_3_4`
* Unlabelled (§3.6, P2:74, Douady–Earle, quoted): every Teichmüller space is contractible — `para5_3_6`
* Theorem 3.5 (§3.6) — `thm5_3_5`
* Formula (3.4) (§3.6) — `thm5_3_5` (the homeomorphism)
* Unlabelled (§3.6, P2:92): Mostow–Kuusalo dichotomy — omitted: quoted
* Definition (the class `F_h(G)`, §3.7) — `familyFhG`
* Formula (3.5) (§3.7) — `familyFhG` (the isomorphism `θ`)
* Formula (3.6) (§3.7) — `para5_3_7`
* Formula (3.7) (§3.7) — `para5_3_7`
* Unlabelled (§3.7, P2:106–118): a unique extremal in `F_h` lies in `F_h(G)` and realizes `τ = τ_S` — `para5_3_7`
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (ExtPlane extRealLine toExt upperHalf lowerHalf IsUniformization IsFuchsian ActsFreely BeltramiH
  BeltramiGamma TeichGamma teichSetoidGamma teichDistanceGamma fMuSym normalizedSolution UniversalTeichmuller
  teichSetoid mobiusSL slRealToComplex limitSet IsHomeoExtension IsQuasiconformal maxDilatation dz dzbar)
open GardinerLakic2000 (beltramiBall teichRel liftBeltrami)

/-! ## §3.1 Equivalent Beltrami differentials -/

/-- **Theorem 3.1** (Ch. V §3.1). The Beltrami differentials `μ` and `ν` of `S` are equivalent if and only if
`f^μ|ℝ = f^ν|ℝ`, or if and only if `f_μ|H = f_ν|H`.
Modelling: `μ`, `ν` on the surface (`GardinerLakic2000.beltramiBall`), lifted to `μ′`, `ν′ ∈ B(Γ)` (a.e. equal to
`GardinerLakic2000.liftBeltrami`); `f_μ` is conformal in `𝕃` (decision B0.2). Near misses: `LiZhongQC.thm27_1`,
`LiZhongQC.teichGamma_equiv_teichSpace` (closed surfaces). -/
theorem thm5_3_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {μ ν : beltramiBall S} {μ' ν' : BeltramiGamma Γ}
    (hμ' : ∀ᵐ z ∂(volume.restrict upperHalf), μ'.1.1 z = liftBeltrami p μ.1 z)
    (hν' : ∀ᵐ z ∂(volume.restrict upperHalf), ν'.1.1 z = liftBeltrami p ν.1 z) :
    (Quot.mk (teichRel p) μ = Quot.mk (teichRel p) ν ↔ ∀ x : ℝ, fMuSym μ'.1.1 x = fMuSym ν'.1.1 x) ∧
      ((∀ x : ℝ, fMuSym μ'.1.1 x = fMuSym ν'.1.1 x) ↔
        EqOn (normalizedSolution μ'.1.1) (normalizedSolution ν'.1.1) lowerHalf) := by
  sorry

/-! ## §3.2 Teichmüller space as a subset of the universal space -/

/-- **Unlabelled** (Ch. V §3.2, P2:6311). If `G₁` is a subgroup of `G₂`, then `T_{S₂} ⊂ T_{S₁}`; in particular every
`T_S` is a subset of the universal Teichmüller space `T`.
Modelling: the maps induced by the inclusions of coefficients are injective. -/
theorem para5_3_2 {Γ₁ Γ₂ : Subgroup SL(2, ℝ)} (h : Γ₁ ≤ Γ₂) :
    (∃ ι : TeichGamma Γ₂ → TeichGamma Γ₁, Function.Injective ι ∧
      ∀ (μ : BeltramiGamma Γ₂) (μ₁ : BeltramiGamma Γ₁), μ₁.1 = μ.1 →
        ι (Quotient.mk (teichSetoidGamma Γ₂) μ) = Quotient.mk (teichSetoidGamma Γ₁) μ₁) ∧
    ∃ j : TeichGamma Γ₁ → UniversalTeichmuller, Function.Injective j ∧
      ∀ μ : BeltramiGamma Γ₁, j (Quotient.mk (teichSetoidGamma Γ₁) μ) = Quotient.mk teichSetoid μ.1 := by
  sorry

/-- **Formula (3.1)** (Ch. V §3.2). `τ|T_S ≤ τ_S`: the distance of the universal space is at most that of `T_S`. -/
theorem eq5_3_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (μ ν : BeltramiGamma Γ) :
    teichDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) ≤
      teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) := by
  sorry

/-! ## §3.3 Completeness of Teichmüller spaces -/

/-- **Unlabelled** (Ch. V §3.3, P1:6327–6331). Lemma III.2.2 in `T_S`: a Cauchy sequence of `(T_S, τ_S)` contains a
subsequence with representatives `μₙ ∈ B(G)` such that `μₙ → μ` a.e. with `μ ∈ B(G)`, `[μₙ] → [μ]` for `τ_S`,
`f_{μₙ} → f_μ` uniformly in the spherical metric and `f^{μₙ} → f^μ` locally uniformly in the half-plane. -/
theorem para5_3_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {pn : ℕ → TeichGamma Γ}
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, teichDistanceGamma (pn m) (pn n) < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (μn : ℕ → BeltramiGamma Γ) (μ : BeltramiGamma Γ),
      (∀ n, Quotient.mk (teichSetoidGamma Γ) (μn n) = pn (φ n)) ∧
      (∀ᵐ z : ℂ, Tendsto (fun n => (μn n).1.1 z) atTop (𝓝 (μ.1.1 z))) ∧
      Tendsto (fun n => teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) (μn n))
        (Quotient.mk (teichSetoidGamma Γ) μ)) atTop (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ℂ,
        LehtoVirtanen1973.sphericalDist (normalizedSolution (μn n).1.1 z) (normalizedSolution μ.1.1 z) < ε) ∧
      TendstoLocallyUniformlyOn (fun n => fMuSym (μn n).1.1) (fMuSym μ.1.1) atTop upperHalf := by
  sorry

/-- **Theorem 3.2** (Ch. V §3.3). The Teichmüller space `(T_S, τ_S)` is complete (near miss:
`LiZhongQC.thm29_2_complete`, closed surfaces). -/
theorem thm5_3_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {pn : ℕ → TeichGamma Γ}
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, teichDistanceGamma (pn m) (pn n) < ε) :
    ∃ q : TeichGamma Γ, Tendsto (fun n => teichDistanceGamma (pn n) q) atTop (𝓝 0) := by
  sorry

/-- **Lemma 3.1** (Ch. V §3.3). Let `[μₙ] → [μ]` in `T_S`, `‖μₙ‖∞ ≤ k < 1`, and `μₙ → ν` a.e. Then `[μ] = [ν]`. -/
theorem lemma5_3_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {μn : ℕ → BeltramiGamma Γ} {μ ν : BeltramiGamma Γ}
    {k : ℝ} (hk : k < 1) (hb : ∀ n, eLpNorm (μn n).1.1 ⊤ volume ≤ ENNReal.ofReal k)
    (hconv : Tendsto (fun n => teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) (μn n))
      (Quotient.mk (teichSetoidGamma Γ) μ)) atTop (𝓝 0))
    (hae : ∀ᵐ z : ℂ, Tendsto (fun n => (μn n).1.1 z) atTop (𝓝 (ν.1.1 z))) :
    Quotient.mk (teichSetoidGamma Γ) μ = Quotient.mk (teichSetoidGamma Γ) ν := by
  sorry

/-! ## §3.4 Quasi-Fuchsian groups -/

/-- **Theorem 3.3** (Ch. V §3.4). The mapping `g ↦ f_μ ∘ g ∘ f_μ⁻¹` defines an isomorphism of the covering group `G`
onto a group `G_μ` of Möbius transformations acting on the quasidisc `f_μ(H′)`.
Modelling: mirrored (`f_μ(ℍ)`); `G_μ ≤ SL(2, ℂ)`; every `g ∈ G` corresponds to `g_μ ∈ G_μ` with
`f_μ ∘ g = g_μ ∘ f_μ` on `ℂ̄`, every `g_μ` arises, and `g_μ` maps `f_μ(ℍ)` onto itself.
**Correction** (Lehto-fix1, audit AUDIT2_Lehto finding 5): "isomorphism" is now stated: the correspondence `g ↦ g_μ` is
multiplicative and is well defined and injective on Möbius maps (equivalently an isomorphism modulo `±1`, the lifts to `SL`
being determined up to sign): `g_μ ∘ f_μ = f_μ ∘ g` determines the Möbius map `g_μ`, and two elements correspond to the same
Möbius map iff their partners do. -/
theorem thm5_3_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ) :
    ∃ Gμ : Subgroup SL(2, ℂ),
      (∀ γ ∈ Γ, ∃ g ∈ Gμ, ∀ z : ExtPlane, OnePoint.map (normalizedSolution μ.1.1)
        (mobiusSL (slRealToComplex γ) z) = mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)) ∧
      (∀ g ∈ Gμ, ∃ γ ∈ Γ, ∀ z : ExtPlane, OnePoint.map (normalizedSolution μ.1.1)
        (mobiusSL (slRealToComplex γ) z) = mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)) ∧
      (∀ g ∈ Gμ, mobiusSL g '' toExt (normalizedSolution μ.1.1 '' upperHalf) =
        toExt (normalizedSolution μ.1.1 '' upperHalf)) ∧
      (∀ (γ₁ γ₂ : SL(2, ℝ)) (g₁ g₂ : SL(2, ℂ)),
        (∀ z : ExtPlane, OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ₁) z) =
          mobiusSL g₁ (OnePoint.map (normalizedSolution μ.1.1) z)) →
        (∀ z : ExtPlane, OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ₂) z) =
          mobiusSL g₂ (OnePoint.map (normalizedSolution μ.1.1) z)) →
        (∀ z : ExtPlane, OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex (γ₁ * γ₂)) z) =
          mobiusSL (g₁ * g₂) (OnePoint.map (normalizedSolution μ.1.1) z)) ∧
        (mobiusSL g₁ = mobiusSL g₂ ↔ mobiusSL (slRealToComplex γ₁) = mobiusSL (slRealToComplex γ₂))) := by
  sorry

/-- **Definition** (quasiconformal deformation of a Fuchsian group, Ch. V §3.4): the quasi-Fuchsian group
`G_μ = {f_μ ∘ g ∘ f_μ⁻¹ | g ∈ G}` for some `μ ∈ B(G)`. -/
def IsQCDeformation (Γ : Subgroup SL(2, ℝ)) (G : Subgroup SL(2, ℂ)) : Prop :=
  ∃ μ : BeltramiGamma Γ, ∀ g : SL(2, ℂ), g ∈ G ↔ ∃ γ ∈ Γ, ∀ z : ExtPlane,
    OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ) z) =
      mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)

/-- **Unlabelled** (Ch. V §3.4, P2:4 [OCR gap]). If `G` is of the first kind, the limit set of `G_μ` is the whole
boundary of `f_μ(H′)` (and by Theorem IV.4.2 this boundary is a circle or a quasicircle without tangent on a dense
set).
Modelling: mirrored (`f_μ(ℍ)`); the surviving claim of the OCR gap. -/
theorem para5_3_4 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hfirst : GardinerLakic2000.IsFirstKind Γ) {Gμ : Subgroup SL(2, ℂ)} (μ : BeltramiGamma Γ)
    (hG : ∀ g : SL(2, ℂ), g ∈ Gμ ↔ ∃ γ ∈ Γ, ∀ z : ExtPlane,
      OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ) z) =
        mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)) :
    limitSet Gμ = frontier (toExt (normalizedSolution μ.1.1 '' upperHalf)) := by
  sorry

/-! ## §3.5 Quasiconformal reflections compatible with a group -/

/-- **Definition** (the reflection (3.2), Ch. V §3.5): `λ = f_μ ∘ j ∘ f_μ⁻¹`, `j(z) = z̄`, a quasiconformal reflection
in the quasicircle `f_μ(ℝ)`. -/
def compatReflection (μ : ℂ → ℂ) : ℂ → ℂ :=
  normalizedSolution μ ∘ conj ∘ Function.invFun (normalizedSolution μ)

/-- **Unlabelled** (Ch. V §3.5, P2:30–44). The reflection `λ` of (3.2) commutes with the elements of `G_μ`, so that its
complex dilatation `κ_λ = ∂λ/∂̄λ` satisfies `(κ_λ ∘ g_μ)(g_μ′/conj g_μ′) = κ_λ` (3.3). Conversely, a quasiconformal
reflection `λ` in `f_μ(ℝ)` satisfying (3.3) for `G_μ` is of the form (3.2) for some `ν` equivalent to `μ`.
Modelling: `G_μ` given as in `thm5_3_3`; the finite part of `λ`; `g_μ(z) = (az + b)/(cz + d)` with
`g_μ′(z) = (cz + d)⁻²`; (3.3) a.e. -/
theorem para5_3_5 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    {Gμ : Subgroup SL(2, ℂ)}
    (hG : ∀ g : SL(2, ℂ), g ∈ Gμ ↔ ∃ γ ∈ Γ, ∀ z : ExtPlane,
      OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ) z) =
        mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)) :
    (∀ g ∈ Gμ, ∀ z : ℂ, g 1 0 * z + g 1 1 ≠ 0 →
      compatReflection μ.1.1 ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) =
        mobiusSL g (compatReflection μ.1.1 z)) ∧
    ∀ (K : ℝ) (Λ : ExtPlane → ExtPlane) (l : ℂ → ℂ),
      IsKQCReflection (toExt (normalizedSolution μ.1.1 '' {z | z.im = 0}) ∪ {LiZhongQC.extInf})
        (toExt (normalizedSolution μ.1.1 '' upperHalf)) (toExt (normalizedSolution μ.1.1 '' lowerHalf)) K Λ →
      (∀ z : ℂ, Λ z = l z) →
      (∀ g ∈ Gμ, ∀ᵐ z : ℂ, dz l ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) /
          dzbar l ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) *
          (((g 1 0 * z + g 1 1) ^ 2)⁻¹ / conj (((g 1 0 * z + g 1 1) ^ 2)⁻¹)) = dz l z / dzbar l z) →
      ∃ ν : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) ν = Quotient.mk (teichSetoidGamma Γ) μ ∧
        ∀ z : ℂ, l z = compatReflection ν.1.1 z := by
  sorry

/-! ## §3.6 Quasisymmetric functions compatible with a group -/

/-- **Definition** (the space `X(G)`, Ch. V §3.6): the normalized quasisymmetric functions `h` for which
`h ∘ g ∘ h⁻¹` is the restriction to `ℝ` of a Möbius transformation for every `g ∈ G`.
Modelling: `h ∘ g = M ∘ h` on `ℝ` off the poles, cross-multiplied (`M` real, `ad − bc ≠ 0`). -/
def qsXG (Γ : Subgroup SL(2, ℝ)) : Set (ℝ → ℝ) :=
  {h | h ∈ qsX ∧ ∀ γ ∈ Γ, ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ x : ℝ, γ 1 0 * x + γ 1 1 ≠ 0 →
    (c * h ((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1)) - a) * h x =
      b - d * h ((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1))}

/-- **Theorem 3.4** (Ch. V §3.6, Tukia; Douady–Earle). Every quasisymmetric function `h ∈ X(G)` has a quasiconformal
extension `f` to the half-plane such that `f ∘ g ∘ f⁻¹` is conformal (a Möbius transformation) for every `g ∈ G`. -/
theorem thm5_3_4 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {h : ℝ → ℝ} (hh : h ∈ qsXG Γ) :
    ∃ (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), IsQuasiconformal f upperHalf ∧ f '' upperHalf = upperHalf ∧
      IsHomeoExtension f upperHalf upperHalf F ∧ (∀ x : ℝ, F (x : ℂ) = ((h x : ℝ) : ℂ)) ∧
      ∀ γ ∈ Γ, ∃ δ : SL(2, ℝ), ∀ z : ℍ, f ((γ • z : ℍ) : ℂ) = ((δ • (UpperHalfPlane.ofComplex (f z)) : ℍ) : ℂ) := by
  sorry

/-- **Unlabelled** (Ch. V §3.6, P2:74, Douady–Earle, quoted). Every Teichmüller space is contractible.
Modelling: a homotopy `H : T_S × [0, 1] → T_S` from the identity to the constant origin, continuous for `τ_S`
(`ε–δ`). -/
theorem para5_3_6 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    ∃ H : TeichGamma Γ → ℝ → TeichGamma Γ, (∀ p, H p 0 = p) ∧ (∀ p, H p 1 = TeichGamma.origin Γ) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, teichDistanceGamma p q < δ →
        |s - t| < δ → teichDistanceGamma (H p t) (H q s) < ε := by
  sorry

/-- **Theorem 3.5** (Ch. V §3.6). The mapping `[μ] ↦ f^μ|ℝ` (3.4) is a homeomorphism of `(T_S, τ_S)` onto
`(X(G), ρ)`.
Modelling: a map `Φ` with `Φ([μ]) = f^μ|ℝ` (real on `ℝ`), bijective onto `X(G)`, continuous both ways (`ε–δ`; `ρ` is
`rhoDist` of III.3.1). -/
theorem thm5_3_5 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    ∃ Φ : TeichGamma Γ → ℝ → ℝ,
      (∀ (μ : BeltramiGamma Γ) (x : ℝ), ((Φ (Quotient.mk (teichSetoidGamma Γ) μ) x : ℝ) : ℂ) = fMuSym μ.1.1 x) ∧
      BijOn Φ univ (qsXG Γ) ∧
      (∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, teichDistanceGamma p q < δ → rhoDist (Φ p) (Φ q) < ε) ∧
      ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, rhoDist (Φ p) (Φ q) < δ → teichDistanceGamma p q < ε := by
  sorry

/-! ## §3.7 Unique extremality and Teichmüller metrics -/

/-- **Definition** (the class `F_h(G)`, Ch. V §3.7). For `h ∈ X(G)` with `h ∘ g ∘ h⁻¹ = θ(g)|ℝ` (3.5), the
quasiconformal self-maps `f` of the half-plane with boundary values `h` and `f ∘ g ∘ f⁻¹ = θ(g)|H`.
Modelling: `θ` as a map `Γ → SL(2, ℝ)` (Lehto's `θ(g)`), the relations written `f ∘ g = θ(g) ∘ f`. -/
def familyFhG (Γ : Subgroup SL(2, ℝ)) (h : ℝ → ℝ) (θ : SL(2, ℝ) → SL(2, ℝ)) : Set (ℂ → ℂ) :=
  {f | IsQuasiconformal f upperHalf ∧ f '' upperHalf = upperHalf ∧
    (∃ F : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf upperHalf F ∧ ∀ x : ℝ, F (x : ℂ) = ((h x : ℝ) : ℂ)) ∧
    ∀ γ ∈ Γ, ∀ z : ℍ, f ((γ • z : ℍ) : ℂ) = ((θ γ • (UpperHalfPlane.ofComplex (f z)) : ℍ) : ℂ)}

/-- **Unlabelled** (Ch. V §3.7, P2:106–118). Let `h ∈ X(G)` with (3.5). If the extremal `f₁` in `F_h` (the
quasiconformal self-maps of `H` with boundary values `h`) is unique, then `f₁ ∘ g ∘ f₁⁻¹ = θ(g)|H` (3.7), i.e.
`f₁ ∈ F_h(G)`, `f₁` is extremal in `F_h(G)`, and by (3.6), `τ(0, [μ₁]) = τ_S(0, [μ₁])`.
Modelling: for the complex dilatation `μ₁` of `f₁` as an element of `B(G)` (`μ₁` given with its two readings). -/
theorem para5_3_7 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {h : ℝ → ℝ}
    {θ : SL(2, ℝ) → SL(2, ℝ)} (hθ : ∀ γ ∈ Γ, ∀ x : ℝ, γ 1 0 * x + γ 1 1 ≠ 0 →
      ((θ γ) 1 0 * h x + (θ γ) 1 1) * h ((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1)) =
        (θ γ) 0 0 * h x + (θ γ) 0 1)
    {f₁ : ℂ → ℂ} (hf₁ : f₁ ∈ familyFhG ⊥ h fun _ => 1)
    (huniq : ∀ f ∈ familyFhG ⊥ h (fun _ => 1), maxDilatation f upperHalf ≤ maxDilatation f₁ upperHalf →
      EqOn f f₁ upperHalf)
    {μ₁ : BeltramiGamma Γ} (hμ₁ : ∀ᵐ z ∂(volume.restrict upperHalf), μ₁.1.1 z = LiZhongQC.complexDilatation f₁ z) :
    f₁ ∈ familyFhG Γ h θ ∧
      (∀ f ∈ familyFhG Γ h θ, maxDilatation f₁ upperHalf ≤ maxDilatation f upperHalf) ∧
      teichDist UniversalTeichmuller.origin (Quotient.mk teichSetoid μ₁.1) =
        teichDistanceGamma (TeichGamma.origin Γ) (Quotient.mk (teichSetoidGamma Γ) μ₁) := by
  sorry

end Lehto1987
