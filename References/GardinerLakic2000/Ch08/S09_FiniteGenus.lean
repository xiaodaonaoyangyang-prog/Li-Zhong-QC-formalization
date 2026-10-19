import References.GardinerLakic2000.Ch08.S08_IsometryTheoremGenusZero

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.9 Riemann surfaces of finite genus

Source `teichmuller.txt`, lines 7068–7190 (Chapter 8, §8.9).

* Definition (`R(W, Λ)`: integrable meromorphic quadratic differentials on `W` with finitely many poles, all in `Λ`,
  l. 7069) — `IsPoleQD`, `ratSpaceRS`
* Theorem 13 (the generalized Bers approximation theorem, l. 7071) — `thm8_13`
* Theorem 14 (l. 7079) — `thm8_14`
* The Noether gap theorem (quoted, [FK80], [Fos81], l. 7083) — `noether_gap`
* Lemma 5 (l. 7089) — `IsNonsimpleZeroQD`, `lemma8_5`
* Lemma 6 (l. 7098) — `lemma8_6`
* Definition 5 (the sets `F` and `V` on a surface, l. 7108) — `nonsimpleZeroSetRS`, `vSetRS`

Not items: the Steps I–XI of the proof of Theorem 14 (l. 7120–7189); "if `X₁ − X` is finite then `A(X)` is finite
dimensional" (l. 7075, U−). Modelling: surface level; open subsets `V ⊆ W` are `TopologicalSpace.Opens W` with the
restricted charts, and a chart family on `W` restricts to `V` by `x ↦ φ x.1` (the chart at `x ∈ V` is the chart of
`W` at `x` restricted). A pole of a quadratic differential is a point where the local coefficient has no removable
singularity (`IsPoleQD`). Meromorphic functions on a compact surface and their orders are the project's
`LiZhongQC.IsMeromorphicRS`, `LiZhongQC.ordRS`; divisors and `D₀[−α]` are `LiZhongQC.Divisor`,
`LiZhongQC.meroFunctionSpace`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsMeroQuadDiff quadDiffNorm IsBiholomorphic HasGenus meroFunctionSpace IsMeromorphicRS ordRS)

/-- Helper (§8.9). `p` is a pole of the quadratic differential `q`: the local coefficient at `p` has no removable
singularity at `p`. -/
def IsPoleQD {W : Type*} [TopologicalSpace W] [ChartedSpace ℂ W] (q : W → ℂ → ℂ) (p : W) : Prop :=
  ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (chartAt ℂ p p) ∧ ∀ᶠ w in 𝓝[≠] (chartAt ℂ p p), q p w = g w

/-- **Definition** (§8.9, l. 7069). `R(W, Λ)`: the meromorphic quadratic differentials `φ` on `W` with
`∫_W |φ| < ∞` and finitely many poles, all of them in `Λ`. -/
def ratSpaceRS (W : Type u) [TopologicalSpace W] [ChartedSpace ℂ W] (Λ : Set W) : Set (W → ℂ → ℂ) :=
  {φ | IsMeroQuadDiff φ ∧ quadDiffNorm φ < ⊤ ∧ {p | IsPoleQD φ p}.Finite ∧ {p | IsPoleQD φ p} ⊆ Λ}

/-- **Theorem 13** (the generalized Bers approximation theorem, §8.9, l. 7071). Let `V` be an open subset of `W`. If
`Λ` is dense in `W − V`, then `R(W, Λ)` is dense in `A(V)`. -/
theorem thm8_13 {W : Type u} [TopologicalSpace W] [T2Space W] [ConnectedSpace W] [ChartedSpace ℂ W]
    [IsManifold 𝓘(ℂ) ω W] (V : TopologicalSpace.Opens W) {Λ : Set W} (hΛ : Λ ⊆ (V : Set W)ᶜ)
    (hdense : (V : Set W)ᶜ ⊆ closure Λ) {φ : V → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet V) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ψ ∈ ratSpaceRS W Λ, quadDiffNorm (fun x : V => φ x - ψ x.1) < ε := by
  sorry

/-- **Theorem 14** (§8.9, l. 7079). If `X` and `Y` are subsets of compact Riemann surfaces `X₁`, `Y₁` and `X₁ − X` is
infinite, every linear isometry of `A(X)` onto `A(Y)` is the pull-back by a conformal map of `Y` onto `X` times a
constant of modulus one. -/
theorem thm8_14 {X Y : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (hX : ∃ (X₁ : LiZhongQC.ClosedRS.{u}) (ι : X → X₁.carrier), Topology.IsOpenEmbedding ι ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι ∧ (range ι)ᶜ.Infinite)
    (hY : EmbedsInClosedRS Y) {L : (X → ℂ → ℂ) → (Y → ℂ → ℂ)}
    (hL : IsLinearIsometryOnto (integrableHolQDSet X) (integrableHolQDSet Y) quadDiffNorm quadDiffNorm L) :
    ∃ (c : Y ≃ₜ X) (α : ℂ), IsBiholomorphic (c : Y → X) ∧ ‖α‖ = 1 ∧
      ∀ φ ∈ integrableHolQDSet X, ∀ y : Y,
        EqOn (L φ y) (fun z => α * pullbackQDRS (c : Y → X) φ y z) (chartAt ℂ y).target := by
  sorry

/-- **The Noether gap theorem** (quoted, §8.9, l. 7083). On a compact Riemann surface `M` of genus `g`, for points
`b₁, …, b_{n+1}` (not necessarily distinct) with `n + 1 ≥ 2g` there is a meromorphic function `f` with
`(f) ≥ −(b₁ + ⋯ + b_{n+1})` and not `(f) ≥ −(b₁ + ⋯ + b_n)`. -/
theorem noether_gap {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [CompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {g : ℕ} (hg : HasGenus M g) {n : ℕ} (b : Fin (n + 1) → M)
    (hn : 2 * g ≤ n + 1) :
    ∃ f ∈ meroFunctionSpace (∑ i, Finsupp.single (b i) (1 : ℤ)),
      f ∉ meroFunctionSpace (∑ i : Fin n, Finsupp.single (b (Fin.castSucc i)) (1 : ℤ)) := by
  sorry

/-- Helper for **Lemma 5** (§8.9). `p` is a nonsimple zero of the quadratic differential `q` (in the chart at `p`): the
local coefficient is holomorphic at `p` and vanishes there to order `≥ 2`.
[CORRECTION] The printed reading `q p c = 0 ∧ deriv (q p) c = 0` (`c` the chart point) is junk at a pole: there `q p c` is
unconstrained and `deriv` takes the junk value `0`, so every pole with chart value `0` would count as a nonsimple zero
and `lemma8_5` would be false (take `R₂` holomorphic with a simple zero at a boundary point `p` and `R₁` with a simple
pole at `p` and chart values `0`; every `C₁R₁ + C₂R₂` with `C₁ ≠ 0`, forced by (b), then has a junk "nonsimple zero" at
`p`). The `AnalyticAt` guard excludes poles. -/
def IsNonsimpleZeroQD {W : Type*} [TopologicalSpace W] [ChartedSpace ℂ W] (q : W → ℂ → ℂ) (p : W) : Prop :=
  AnalyticAt ℂ (q p) (chartAt ℂ p p) ∧ q p (chartAt ℂ p p) = 0 ∧ deriv (q p) (chartAt ℂ p p) = 0

/-- **Lemma 5** (§8.9, l. 7089). If `R₁, R₂ ∈ R(X)` are nonzero with no nonsimple zeros in common on `X̄`, there are
constants `C₁`, `C₂` such that (a) `C₁R₁ + C₂R₂` has no nonsimple zeros in `X̄`, and (b) every pole in `X̄` of `R₁` or
`R₂` is a pole of `C₁R₁ + C₂R₂`. -/
theorem lemma8_5 {X₁ : Type u} [TopologicalSpace X₁] [T2Space X₁] [ConnectedSpace X₁] [CompactSpace X₁]
    [ChartedSpace ℂ X₁] [IsManifold 𝓘(ℂ) ω X₁] (X : TopologicalSpace.Opens X₁) {R₁ R₂ : X₁ → ℂ → ℂ}
    (h₁ : R₁ ∈ ratSpaceRS X₁ (X : Set X₁)ᶜ) (h₂ : R₂ ∈ ratSpaceRS X₁ (X : Set X₁)ᶜ) (h₁0 : R₁ ≠ 0) (h₂0 : R₂ ≠ 0)
    (hcommon : ∀ p ∈ closure (X : Set X₁), ¬ (IsNonsimpleZeroQD R₁ p ∧ IsNonsimpleZeroQD R₂ p)) :
    ∃ C₁ C₂ : ℂ, (∀ p ∈ closure (X : Set X₁), ¬ IsNonsimpleZeroQD (C₁ • R₁ + C₂ • R₂) p) ∧
      ∀ p ∈ closure (X : Set X₁), IsPoleQD R₁ p ∨ IsPoleQD R₂ p → IsPoleQD (C₁ • R₁ + C₂ • R₂) p := by
  sorry

/-- **Lemma 6** (§8.9, l. 7098). Let `S` be an infinite subset of the compact Riemann surface `N`, `s₁, …, sₙ ∈ S` and
`m ∈ N − S`. There is a meromorphic `g` on `N` with (a) `g(m) = 0`, (b) all poles simple and in `S − {s₁, …, sₙ}`,
(c) no zeros in `{s₁, …, sₙ}`, (d) all zeros simple. -/
theorem lemma8_6 {N : Type u} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [CompactSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {S : Set N} (hS : S.Infinite) {n : ℕ} (s : Fin n → N)
    (hs : ∀ i, s i ∈ S) {m : N} (hm : m ∉ S) :
    ∃ g : N → ℂ, IsMeromorphicRS g ∧ 0 < ordRS g m ∧
      (∀ q, ordRS g q < 0 → ordRS g q = -1 ∧ q ∈ S ∧ q ∉ range s) ∧ (∀ i, ordRS g (s i) ≤ 0) ∧
      ∀ q, 0 < ordRS g q → ordRS g q = 1 := by
  sorry

/-- **Definition 5** (§8.9, l. 7108), the set `F`. The differentials of `A(X)` with a nonsimple zero at `b ∈ X`. -/
def nonsimpleZeroSetRS {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (b : X) : Set (X → ℂ → ℂ) :=
  {φ | φ ∈ integrableHolQDSet X ∧ IsNonsimpleZeroQD φ b}

/-- **Definition 5** (§8.9, l. 7108–7118), the set `V`. The `ψ ∈ A(X)` with `ψ²/φ ∈ L¹(X)` for some `φ ∈ F`.
Remark (AUDIT5_GL N1): as written `F` contains `φ = 0` (`IsNonsimpleZeroQD 0 b` holds), and Lean's `ψ²/0 = 0` then puts
every `ψ ∈ A(X)` in `V`. The book means `φ ≢ 0`. No statement uses `F` or `V`; a user must add `φ ≠ 0`. -/
def vSetRS {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (b : X) : Set (X → ℂ → ℂ) :=
  {ψ | ψ ∈ integrableHolQDSet X ∧ ∃ φ ∈ nonsimpleZeroSetRS b, quadDiffNorm (fun x z => ψ x z ^ 2 / φ x z) < ⊤}

end GardinerLakic2000
