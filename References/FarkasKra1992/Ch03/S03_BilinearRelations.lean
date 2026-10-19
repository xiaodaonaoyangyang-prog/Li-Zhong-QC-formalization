import References.FarkasKra1992.Ch03.S02_HarmonicAndAnalyticDifferentials

/-!
# Farkas–Kra, Chapter III §3: Bilinear relations (III.3.1–III.3.4)

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §3 (`full.md` FK1:2797–2892).

Conventions: as in `Ch03/S02_HarmonicAndAnalyticDifferentials`; `M` is compact of genus `g`, `{a_j, b_j}` is a canonical homology
basis and `{ζ_k}` the normalized basis of the holomorphic differentials (`IsNormalizedBasis`) with period matrix `Π`,
`π_{jk} = ∫_{b_j} ζ_k`. Differentials of the first, second and third kind are `Forster1981.IsAbelianDiff1`, `IsAbelianDiff2`,
`IsAbelianDiff3`.

* Proposition III.3.1 (Riemann's relation I) — `prop3_3_1`
* III.3.1 ((3.1.2): `∫_{b_j} ζ_k = ∫_{b_k} ζ_j`) — `para3_3_1`
* III.3.2 (Riemann's relation II: `(ζ_j, ζ_k) = 2 Im π_{jk}`) — `para3_3_2`
* Proposition III.3.3, part (a) — `prop3_3_3_a`
* Proposition III.3.3, part (b) — `prop3_3_3_b`
* III.3.4 (differentials of the first, second, third kind) — exists: `Forster1981.IsAbelianDiff1`, `Forster1981.IsAbelianDiff2`, `Forster1981.IsAbelianDiff3`
* Corollary III.3.4, part (a) — `cor3_3_4_a`
* Corollary III.3.4, part (b) — `cor3_3_4_b`
* III.3.5–III.3.8 (normalized differentials of the third kind, reciprocity laws) — omitted: scope (used only by III.6–III.8)
-/

open scoped Manifold ContDiff Topology Matrix
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {x₀ : X} {g : ℕ}

/-- **Riemann's bilinear relation I** (Ch. III §3.1, (3.1.1)). Let `θ` and `θ̃` be holomorphic differentials on the compact
surface `M`. Then `0 = Σ_l [∫_{a_l} θ ∫_{b_l} θ̃ − ∫_{b_l} θ ∫_{a_l} θ̃]`. -/
theorem prop3_3_1 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {θ θ₁ : Form1 X} (h₁ : IsAbelianDiff1 θ) (h₂ : IsAbelianDiff1 θ₁)
    {A B A₁ B₁ : Fin g → ℂ} (hA : ∀ j, IsPeriodOf θ (a j) (A j)) (hB : ∀ j, IsPeriodOf θ (b j) (B j))
    (hA₁ : ∀ j, IsPeriodOf θ₁ (a j) (A₁ j)) (hB₁ : ∀ j, IsPeriodOf θ₁ (b j) (B₁ j)) :
    ∑ j, (A j * B₁ j - B j * A₁ j) = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §3.1, (3.1.2)). For the normalized basis, `∫_{b_j} ζ_k = ∫_{b_k} ζ_j` (the matrix `Π` is
symmetric). -/
theorem para3_3_1 [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {ζ : Fin g → Form1 X} (hζ : IsNormalizedBasis a ζ) {j k : Fin g} {v w : ℂ}
    (hv : IsPeriodOf (ζ k) (b j) v) (hw : IsPeriodOf (ζ j) (b k) w) : v = w := by
  sorry

/-- **Riemann's bilinear relation II** (Ch. III §3.2). For the normalized basis `{ζ_j}` with period matrix `Π`,
`−i (ζ_j, ζ_k) = conj(∫_{b_j} ζ_k) − ∫_{b_k} ζ_j = −2i Im π_{jk}`: the inner product is `(ζ_j, ζ_k) = 2 Im π_{jk}`
(in particular `Im π_{jj} > 0`). -/
theorem para3_3_2 [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {ζ : Fin g → Form1 X} (hζ : IsNormalizedBasis a ζ)
    {P : Matrix (Fin g) (Fin g) ℂ} (hP : ∀ j k, IsPeriodOf (ζ k) (b j) (P j k)) (j k : Fin g) :
    HasL2Inner univ (ζ j) (ζ k) (2 * ((P j k).im : ℂ)) := by
  sorry

/-- **Proposition III.3.3(a)** (Ch. III §3.3). Let `θ` be a holomorphic differential. If all the "a" periods of `θ` are zero
(`∫_{a_j} θ = 0`, `j = 1, …, g`), then `θ = 0`. -/
theorem prop3_3_3_a [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {θ : Form1 X} (hθ : IsAbelianDiff1 θ) (h0 : ∀ j, IsPeriodOf θ (a j) 0) :
    Form1.EqOn θ 0 univ := by
  sorry

/-- **Proposition III.3.3(b)** (Ch. III §3.3). Let `θ` be a holomorphic differential. If all the periods of `θ` are real, then
`θ = 0`. -/
theorem prop3_3_3_b [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {θ : Form1 X} (hθ : IsAbelianDiff1 θ)
    (hreal : ∀ k, ∃ r : ℝ, IsPeriodOf θ (Sum.elim a b k) (r : ℂ)) : Form1.EqOn θ 0 univ := by
  sorry

/-- **Corollary III.3.4(a)** (Ch. III §3.4). We can prescribe uniquely the "a" periods of an abelian differential of the first
kind: for every `c : Fin g → ℂ` there is exactly one holomorphic differential with `∫_{a_j} θ = c_j`. -/
theorem cor3_3_4_a [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) (c : Fin g → ℂ) :
    ∃ θ : Form1 X, IsAbelianDiff1 θ ∧ (∀ j, IsPeriodOf θ (a j) (c j)) ∧
      ∀ θ₁ : Form1 X, IsAbelianDiff1 θ₁ → (∀ j, IsPeriodOf θ₁ (a j) (c j)) → Form1.EqOn θ θ₁ univ := by
  sorry

/-- **Corollary III.3.4(b)** (Ch. III §3.4). We can prescribe uniquely the real parts of all the periods of an abelian
differential of the first kind: for every `r : Fin g ⊕ Fin g → ℝ` there is exactly one holomorphic differential `θ` whose
`ℵ_k` period has real part `r_k`. -/
theorem cor3_3_4_b [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) (r : Fin g ⊕ Fin g → ℝ) :
    ∃ θ : Form1 X, IsAbelianDiff1 θ ∧ (∀ k, ∃ v : ℂ, IsPeriodOf θ (Sum.elim a b k) v ∧ v.re = r k) ∧
      ∀ θ₁ : Form1 X, IsAbelianDiff1 θ₁ → (∀ k, ∃ v : ℂ, IsPeriodOf θ₁ (Sum.elim a b k) v ∧ v.re = r k) →
        Form1.EqOn θ θ₁ univ := by
  sorry

end FarkasKra1992
