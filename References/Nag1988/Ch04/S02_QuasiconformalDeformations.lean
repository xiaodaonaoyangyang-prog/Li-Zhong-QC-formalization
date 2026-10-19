import References.Hubbard2006.Ch06.S12_QuasiFuchsian
import References.GardinerLakic2000.Ch07.S02_TeichmullerKobayashi

/-!
# Nag, Chapter 4 §4.2: Intrinsic global moduli by "stratification"

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 4 §4.2 (`full.md` N2:2993–3300,
folder
`The Complex Analytic Theory … c10f6cd1`; cited `N2:<line>`). New items only.

**Model.** `G = Γ` is a Fuchsian group in `SL(2, ℝ)`. A Beltrami coefficient of `L^∞(ℂ, G)₁` (compatible with `G`, on
all of
`ℂ`) is, by Nag's own decomposition `L^∞(ℂ, G) = L^∞(U, G) ⊕ L^∞(L, G)` (4.2.2), a pair `(μ₁, μ₂)` of elements of
`LiZhongQC.BeltramiGamma Γ`, `μ₁` on the upper half plane and `μ₂` the *reflection* `z ↦ conj μ₂'(z̄)` of a coefficient
`μ₂'` on `𝕃` (`Hubbard2006.pairCoeff`); so the class of `μ₂` in `T(L, G)` is recorded as the point `[μ₂] ∈ T(U, G)`
of the
reflected coefficient (Nag's "canonical anti-biholomorphic equivalence", which is by construction). The normalized
solution `w^μ` is `Hubbard2006.qfSol`; `M^μ(g) = w^μ g (w^μ)⁻¹` (2.2) is the relation `Hubbard2006.IsQFConj` (a matrix
`A ∈ SL(2, ℂ)` with `w^μ ∘ g = A ∘ w^μ` on `ℙ¹`). `Def(G)` is the set of equivalence classes (`DefEquiv`: `M^μ =
M^ν`) and
carries no topology or manifold instance; its complex structure is that of `T(U, G) × T(L, G)` (the product of the Bers
structures): holomorphy is read through holomorphic discs (`GardinerLakic2000.holDiscsT`; the second factor is
anti-holomorphic in the coordinates of `T(U, G)`). "Finitely generated of the first kind" is `IsFGFirstKind Γ`.

* Definition (the quasiconformal deformation space `Def(G)`, 4.2.1: classes of `μ ∈ L^∞(ℂ, G)₁` with `M^μ = M^ν`) —
  `DefEquiv`, `DefSpace`
* Lemma 4.2.1 (`μ ∼ ν` iff `w^μ = w^ν` on `Λ(G) = ℝ̂`; `μ` is trivial iff `w^μ` is the identity on `ℝ`) —
  `lemma4_2_1_a`,
  `lemma4_2_1_b`
* Proposition 4.2.2 (`Def(G) ≅ T(G) × T(L, G)`) — `prop4_2_2_a`
* Proposition 4.2.2 (`T(L, G) ≅ T(G')` biholomorphically for `G' = h G h⁻¹`, `h(z) = −z`, and `T(L, G)` is
  antiholomorphic to
  `T(G)`) — `prop4_2_2_b`
* Theorem 4.2.3 (for a compact surface of genus `g ≥ 2` there are `6g − 6` real numbers `x_j` such that
  `[μ] ↦ (w^μ(x_1), …, w^μ(x_N))` is a well-defined biholomorphism of `Def(G)` onto a domain of `ℂ^N`) — `defCoord`,
  `thm4_2_3`
* 4.2.4 (for symmetric `μ`, `w^μ = w_{μ₁}`: the real diagonal) — `para4_2_4`
* 4.2.4 (the complex diagonal and Earle's coordinates), 4.2.5 (the coordinates of `T(g, n)`, the map `ψ`,
  Teichmüller's lemma for
  `T(g, n)`) — omitted: remarks, descriptions of constructions in the proof and of work of Earle and Nag, without a
  precise statement independent of the cited papers (4.2.5 (2.16)–(2.22) are formulas used for Teichmüller's lemma,
  which is
  stated at Nag's §3.1)
* Remark 4.2.1 and Exercises — omitted: exercise
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Manifold ContDiff ComplexConjugate

noncomputable section

namespace Nag1988

open LiZhongQC GardinerLakic2000

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Finitely generated Fuchsian group of the first kind** (helper): `Γ` is finitely generated and its limit set (in
`SL(2, ℂ)`) is the real line `ℝ̂`. -/
def IsFGFirstKind (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  Γ.FG ∧ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) = extRealLine

/-- **Equivalence of quasiconformal deformations** (4.2.1, N2:3010): the elements `μ = (μ₁, μ₂)` and `ν` of
`L^∞(ℂ, G)₁` are equivalent if `M^μ = M^ν`, i.e. the Möbius transformations `M^μ(g)`, `M^ν(g)` agree for every `g ∈
G`. -/
def DefEquiv (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ ν : BeltramiGamma Γ × BeltramiGamma Γ) : Prop :=
  ∀ γ ∈ Γ, ∀ A B : Matrix.SpecialLinearGroup (Fin 2) ℂ, Hubbard2006.IsQFConj μ.1 μ.2 γ A →
    Hubbard2006.IsQFConj ν.1 ν.2 γ B → mobiusSL A = mobiusSL B

/-- **The quasiconformal deformation space `Def(G)`** (4.2.1, (2.3)): the set of equivalence classes. -/
def DefSpace (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type := Quot (DefEquiv Γ)

/-- **Lemma 4.2.1 (a)** (N2:3003). For a finitely generated Fuchsian group of the first kind (`Λ(G) = ℝ̂`), `μ` and
`ν` are
equivalent if and only if `w^μ` and `w^ν` coincide on `Λ(G)`, i.e. on the real axis. -/
theorem lemma4_2_1_a (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ)
    (μ ν : BeltramiGamma Γ × BeltramiGamma Γ) :
    DefEquiv Γ μ ν ↔ ∀ x : ℝ, Hubbard2006.qfSol μ.1 μ.2 x = Hubbard2006.qfSol ν.1 ν.2 x := by
  sorry

/-- **Lemma 4.2.1 (b)** (N2:3003). `μ` is trivial (`M^μ` is the identity: `M^μ(g) = g` for every `g ∈ G`) if and only if
`w^μ` is the identity on the real axis. -/
theorem lemma4_2_1_b (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ)
    (μ : BeltramiGamma Γ × BeltramiGamma Γ) :
    (∀ γ ∈ Γ, Hubbard2006.IsQFConj μ.1 μ.2 γ (slRealToComplex γ)) ↔ ∀ x : ℝ, Hubbard2006.qfSol μ.1 μ.2 x = x := by
  sorry

/-- **Proposition 4.2.2 (a)** (N2:3041). For a finitely generated Fuchsian group of the first kind the canonical map
`Def(G) → T(U, G) × T(L, G)`, `[μ] ↦ ([μ₁], [μ₂])`, is a bijection (`T(L, G)` recorded through the reflected
coefficient, see the module docstring). -/
theorem prop4_2_2_a (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ) :
    ∃ e : DefSpace Γ ≃ TeichGamma Γ × TeichGamma Γ, ∀ μ ν : BeltramiGamma Γ,
      e (Quot.mk _ (μ, ν)) = (Quotient.mk (teichSetoidGamma Γ) μ, Quotient.mk (teichSetoidGamma Γ) ν) := by
  sorry

/-- **Proposition 4.2.2 (b)** (N2:3041). Let `G'` be the group `h G h⁻¹`, `h(z) = −z` (the matrices
`[[a, −b], [−c, d]]` for `[[a, b], [c, d]] ∈ G`). The identification of `T(L, G)` with `T(G')`, `[μ₂] ↦ [μ̃]`,
`μ̃(z) = μ₂(−z)`, is, in the coordinates of the reflected coefficients `ν = μ₂*`, the map `[ν] ↦ [z ↦ conj ν(−z̄)]`;
it is
a well defined bijection `T(G) → T(G')` carrying holomorphic discs to antiholomorphic ones (`E (f (t̄))` is a
holomorphic
disc for every holomorphic disc `f`). -/
theorem prop4_2_2_b {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ')
    (hconj : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ' ↔ ∃ δ ∈ Γ, γ 0 0 = δ 0 0 ∧ γ 0 1 = -δ 0 1 ∧
      γ 1 0 = -δ 1 0 ∧ γ 1 1 = δ 1 1) :
    ∃ E : TeichGamma Γ ≃ TeichGamma Γ',
      (∀ (ν : BeltramiGamma Γ) (ν' : BeltramiGamma Γ'),
        (∀ᵐ z ∂(volume.restrict upperHalf), ν'.1.1 z = conj (ν.1.1 (-conj z))) →
          E (Quotient.mk (teichSetoidGamma Γ) ν) = Quotient.mk (teichSetoidGamma Γ') ν') ∧
      ∀ f ∈ holDiscsT Γ, (fun t => E (f (conj t))) ∈ holDiscsT Γ' := by
  sorry

/-- **The coordinates `(w^μ(x_1), …, w^μ(x_N))`** (4.2.3, (2.6)) as a function of the representatives. -/
def defCoord {N : ℕ} (x : Fin N → ℝ) (μ : BeltramiGamma Γ × BeltramiGamma Γ) : Fin N → ℂ :=
  fun j => Hubbard2006.qfSol μ.1 μ.2 (x j)

/-- **Theorem 4.2.3** (N2:3087). Let `Γ` be a torsion-free Fuchsian group uniformizing a compact surface `X` of genus
`g ≥ 2`, with canonical generators `A_j, B_j` (`∏ [A_j, B_j] = 1`, up to the sign of `SL`) normalized by (2.5): the
commutator
`C₁ = [A₁, B₁]` has attractive fixed point `0` and repulsive fixed point `∞` and `A₁(0) = 1`. Then there are `N = 6g
− 6` real
numbers `x_1, …, x_N` such that `[μ] ↦ (w^μ(x_j))_j` is well defined on `Def(G)` (depends only on the class),
injective, has
open image in `ℂ^N`, and is holomorphic on holomorphic discs of `T(U, G) × T(L, G)` (the second coordinate being a disc
antiholomorphic in the coordinates of `T(U, G)`); so it is a biholomorphism of `Def(G)` onto a domain of `ℂ^N`
(a holomorphic injection between manifolds of the same dimension). -/
theorem thm4_2_3 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] {g : ℕ} (hg : 2 ≤ g) (hS : HasGenus S g) {p : UpperHalfPlane → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {A B : Fin g → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : ∀ j, A j ∈ Γ) (hB : ∀ j, B j ∈ Γ)
    (hgen : ∀ γ ∈ Γ, γ ∈ Subgroup.closure (range A ∪ range B ∪ {-1}))
    (hrel : (List.ofFn fun j => A j * B j * (A j)⁻¹ * (B j)⁻¹).prod = 1 ∨
      (List.ofFn fun j => A j * B j * (A j)⁻¹ * (B j)⁻¹).prod = -1)
    (hC : (A ⟨0, by omega⟩ * B ⟨0, by omega⟩ * (A ⟨0, by omega⟩)⁻¹ * (B ⟨0, by omega⟩)⁻¹) 0 1 = 0 ∧
      (A ⟨0, by omega⟩ * B ⟨0, by omega⟩ * (A ⟨0, by omega⟩)⁻¹ * (B ⟨0, by omega⟩)⁻¹) 1 0 = 0 ∧
      |(A ⟨0, by omega⟩ * B ⟨0, by omega⟩ * (A ⟨0, by omega⟩)⁻¹ * (B ⟨0, by omega⟩)⁻¹) 0 0| < 1)
    (hA0 : (A ⟨0, by omega⟩) 0 1 = (A ⟨0, by omega⟩) 1 1) :
    ∃ x : Fin (6 * g - 6) → ℝ,
      (∀ μ ν : BeltramiGamma Γ × BeltramiGamma Γ, DefEquiv Γ μ ν → defCoord x μ = defCoord x ν) ∧
      (∀ μ ν : BeltramiGamma Γ × BeltramiGamma Γ, defCoord x μ = defCoord x ν → DefEquiv Γ μ ν) ∧
      IsOpen (range (defCoord (Γ := Γ) x)) ∧
      ∀ (f₁ f₂ : ℂ → TeichGamma Γ), f₁ ∈ holDiscsT Γ → (fun t => f₂ (conj t)) ∈ holDiscsT Γ →
        ∀ μ ν : ℂ → BeltramiGamma Γ, (∀ t ∈ Metric.ball (0 : ℂ) 1, Quotient.mk (teichSetoidGamma Γ) (μ t) = f₁ t ∧
            Quotient.mk (teichSetoidGamma Γ) (ν t) = f₂ t) →
          ∀ j, DifferentiableOn ℂ (fun t => defCoord x (μ t, ν t) j) (Metric.ball (0 : ℂ) 1) := by
  sorry

/-- **4.2.4, the real diagonal** (N2:3169). For a symmetric pair (`μ₂* = μ₁`, i.e. `μ₂(z̄) = conj μ₁(z)`), `w^μ =
w_{μ₁}`
(§1.2.14): the normalized solution of the pair is the Fuchsian one, `f^{μ₁}` of `LiZhongQC.fMuSym`. -/
theorem para4_2_4 (μ : BeltramiGamma Γ) : Hubbard2006.qfSol μ μ = fMuSym μ.1.1 := by
  sorry

end Nag1988
