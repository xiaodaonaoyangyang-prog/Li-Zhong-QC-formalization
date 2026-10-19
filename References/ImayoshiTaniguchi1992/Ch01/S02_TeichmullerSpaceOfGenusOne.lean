import LiZhongQC.Ch07.S27_TeichmullerExistence
import References.Lehto1987.Ch05.S06_TeichmullerSpaceOfATorus
import References.FarkasKra1992.Ch03.S01_IntersectionTheory

/-!
# Imayoshi–Taniguchi, Chapter 1 §1.2: Moduli and Teichmüller space of tori

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 1 §1.2 (`full.md` IT1:300–620,
folder `An Introduction to Teichmuller Spaces … ef13744b`), with the definitions of markings of §1.1.3 and §1.3 it needs.

Conventions: the fundamental group is Mathlib's `FundamentalGroup`; a *canonical system of generators* `{[A_j], [B_j]}` of
`π₁(R, p)` (IT1:270) is an oriented family `(a_j, b_j)` of `2g` elements which is the image of the standard generators of the surface
group `⟨a₁, b₁, …, a_g, b_g | ∏ [a_j, b_j]⟩` (`LiZhongQC.surfaceGroup g`) under an isomorphism, **oriented**: the homology classes
form a canonical homology basis (`FarkasKra1992.IsCanonicalHomologyBasis`, intersection numbers `a_j · b_k = δ_{jk}`, `a_j · a_k = 0 =
b_j · b_k`; `IsCanonicalSystem`). The isomorphism alone does not see the orientation (an orientation-reversing homeomorphism of the
surface maps a canonical system to one satisfying the same relation), the intersection numbers do. The change of base point along a curve `C` is
`T_C`, Mathlib's `FundamentalGroup.fundamentalGroupMulEquivOfPath C`. Markings of surfaces `S`, `S'` are *equivalent* in `T_g` when some
biholomorphic map `h` carries the first, up to a change of base point, to the second (`MarkedEquiv`). **Reading:** orientation
preserving diffeomorphisms `f : R → S` of IT are quasiconformal homeomorphisms (`LiZhongQC.IsQCRS`; the two models of `T(R)`
agree by the Corollary to Theorem 6.9, `cor6_9_b`); the push-forward of a marking by `f` is `FundamentalGroup.map f`.

* Theorem 1.1 (tori `R_τ`, `R_τ′` are biholomorphic iff `τ′` is in the `SL(2, ℤ)`-orbit of `τ`, IT1:339) — exists:
  `LiZhongQC.torus_conformal_iff`
* Theorem 1.2 (`[R_τ, Σ(τ)] = [R_τ′, Σ(τ′)]` in `T₁` iff `τ = τ′`, IT1:418) — exists: `Lehto1987.thm5_6_4`
  (Lehto's model of the Teichmüller space of a torus as the upper half-plane)
* Definition (canonical system of generators, IT1:270) — `IsCanonicalSystem`
* Definition (marking equivalence, IT1:416) — `MarkedEquiv`
* Theorem 1.3 (marked tori coincide iff `g ∘ f⁻¹` is homotopic to a biholomorphic map, IT1:426) — `thm1_3`
-/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (surfaceGroup IsQCRS IsBiholomorphic HasGenus)

/-- **Canonical system of generators** of `π₁(R, p)` (Ch. 1 §1.1.3): `(a_j, b_j)_{j < g}` is the image of the standard
generators of the surface group of genus `g` under an isomorphism `surfaceGroup g ≃* π₁(R, p)`, whose homology classes form a
canonical (oriented) homology basis. -/
def IsCanonicalSystem {R : Type} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (g : ℕ) {p : R} (a b : Fin g → FundamentalGroup R p) : Prop :=
  (∃ e : surfaceGroup g ≃* FundamentalGroup R p, ∀ j : Fin g,
    e (PresentedGroup.of (Sum.inl j)) = a j ∧ e (PresentedGroup.of (Sum.inr j)) = b j) ∧
    FarkasKra1992.IsCanonicalHomologyBasis (fun j => Abelianization.of (a j)) (fun j => Abelianization.of (b j))

/-- **Equivalence of marked surfaces** (Ch. 1 §1.2.2, §1.3): `(S, p, a, b)` and `(S', p', a', b')` define the same point of
`T_g` if there are a biholomorphic map `h : S → S'` and a curve `C` from `h(p)` to `p'` such that `T_C ∘ h_*` carries
`(a_j, b_j)` to `(a'_j, b'_j)`. -/
def MarkedEquiv {S S' : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S'] [ChartedSpace ℂ S'] (g : ℕ)
    {p : S} {p' : S'} (a b : Fin g → FundamentalGroup S p) (a' b' : Fin g → FundamentalGroup S' p') : Prop :=
  ∃ h : S ≃ₜ S', IsBiholomorphic h ∧ ∃ C : Path (h p) p', ∀ j : Fin g,
    FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map (h : C(S, S')) p (a j)) = a' j ∧
      FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map (h : C(S, S')) p (b j)) = b' j

variable {R S S' : Type} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
  [CompactSpace R] [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S']
  [CompactSpace S']

/-- **Theorem 1.3** (Ch. 1 §1.2.2). Let `R`, `S`, `S'` be tori, `Σ = {[A₁], [B₁]}` a canonical system of generators of `π₁(R, p)`
and `f : R → S`, `g : R → S'` orientation-preserving (quasiconformal) homeomorphisms. Then `[S, f_*(Σ)] = [S', g_*(Σ)]` in `T₁`
if and only if `g ∘ f⁻¹ : S → S'` is homotopic to a biholomorphic map `h : S → S'`. -/
theorem thm1_3 (hR : HasGenus R 1) (hS : HasGenus S 1) (hS' : HasGenus S' 1) {p : R} {a b : Fin 1 → FundamentalGroup R p}
    (hcan : IsCanonicalSystem 1 a b) (f : R ≃ₜ S) (g : R ≃ₜ S') (hf : IsQCRS f) (hg : IsQCRS g) :
    MarkedEquiv 1 (fun j => FundamentalGroup.map (f : C(R, S)) p (a j)) (fun j => FundamentalGroup.map (f : C(R, S)) p (b j))
        (fun j => FundamentalGroup.map (g : C(R, S')) p (a j)) (fun j => FundamentalGroup.map (g : C(R, S')) p (b j)) ↔
      ∃ h : S ≃ₜ S', IsBiholomorphic h ∧
        ContinuousMap.Homotopic (h : C(S, S')) ((f.symm.trans g : S ≃ₜ S') : C(S, S')) := by
  sorry

end ImayoshiTaniguchi1992
