import References.FarkasKra1992.Ch05.S01_HurwitzTheorem
import References.FarkasKra1992.Ch03.S05_ApplicationsOfRiemannRoch

/-!
# Farkas–Kra, Chapter V §1 (continued): Weierstrass points and automorphisms

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. V §1.2 and §1.7 (`full.md` FK2:3218–3235, 3580–3606).

Sibling of `Ch05/S01_HurwitzTheorem` (which contains the items of Ch. V §1 that do not involve Weierstrass points); the
conventions are those of that file: `M` is a compact Riemann surface of genus `g` (`LiZhongQC.HasGenus`), `Aut M` is the set of
homeomorphisms `T : M ≃ₜ M` with `LiZhongQC.IsBiholomorphic (T : M → M)`, `ν(T)` is `fixedPointCount T`. The set
`W(M)` of Weierstrass points is `weierstrassSet M g` (Ch. III §5.9, `Ch03/S05`: the points where the Wronskian of a basis of the
holomorphic abelian differentials vanishes, `Forster1981.IsWeierstrassPoint`). Hyperelliptic is `Forster1981.IsHyperelliptic`
(genus `> 1` and a double covering of `ℙ¹`; FK's `IsGammaHyperelliptic M 0`, with genus `≥ 2` in the cases below). The homomorphism
`λ : Aut M → Perm(W(M))` is not a declaration (`Aut M` and `Perm` carry no group instances here): its existence is the
Proposition, its injectivity and kernel are stated for the restriction of automorphisms to `W(M)`.

* Proposition V.1.2 (`T(W(M)) = W(M)`) — `prop5_1_2`
* Corollary V.1.2, part 1 (`λ` is injective unless `M` is hyperelliptic, in which case its kernel is `⟨J⟩`) — `cor5_1_2_a`
* Theorem V.1.7 (`ν(T) > 4` implies that every fixed point of `T` is a Weierstrass point) — `thm5_1_7`
-/

open scoped Manifold ContDiff Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsBiholomorphic HasGenus)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Proposition V.1.2** (Ch. V §1.2). Let `M` be a compact surface of genus `g ≥ 2`. If `T ∈ Aut M`, then
`T(W(M)) = W(M)`. -/
theorem prop5_1_2 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) :
    (T : M → M) '' weierstrassSet M g = weierstrassSet M g := by
  sorry

/-- **Corollary V.1.2, part 1** (Ch. V §1.2). The homomorphism `λ : Aut M → Perm(W(M))`, the restriction of automorphisms to
the (finite) set `W(M)`, is injective unless `M` is hyperelliptic, in which case its kernel is `⟨J⟩`, `J` the hyperelliptic
involution. Stated as: `W(M)` is finite; two automorphisms agreeing on `W(M)` coincide unless `M` is hyperelliptic; and if `M`
is hyperelliptic there is a non-trivial involution `J` of a double covering of `ℙ¹` (`π ∘ J = π`) such that the
automorphisms fixing `W(M)` pointwise are exactly `1` and `J`. -/
theorem cor5_1_2_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) :
    (weierstrassSet M g).Finite ∧
      (¬Forster1981.IsHyperelliptic M → ∀ T₁ T₂ : M ≃ₜ M, IsBiholomorphic (T₁ : M → M) → IsBiholomorphic (T₂ : M → M) →
        (∀ p ∈ weierstrassSet M g, T₁ p = T₂ p) → T₁ = T₂) ∧
      (Forster1981.IsHyperelliptic M → ∃ J : M ≃ₜ M, IsBiholomorphic (J : M → M) ∧ J ≠ 1 ∧
        (∃ π : M → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ Forster1981.IsHolomorphicCovering π 2 ∧
          ∀ x, π (J x) = π x) ∧
        ∀ T : M ≃ₜ M, IsBiholomorphic (T : M → M) → ((∀ p ∈ weierstrassSet M g, T p = p) ↔ (T = 1 ∨ T = J))) := by
  sorry

/-- **Theorem V.1.7** (Ch. V §1.7). Let `M` be a compact surface of genus `g ≥ 2` and `1 ≠ T ∈ Aut M`. If `ν(T) > 4`, then every
fixed point of `T` is a Weierstrass point. -/
theorem thm5_1_7 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1)
    (hv : 4 < fixedPointCount T) : ∀ x, T x = x → x ∈ weierstrassSet M g := by
  sorry

end FarkasKra1992
