import References.FarkasKra1992.Ch03.S01_IntersectionTheory

/-!
# Farkas–Kra, Chapter III §2: Harmonic and analytic differentials on compact surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §2 (`full.md` FK1:2397–2796).

Conventions: as in `Ch03/S01_IntersectionTheory`. The canonical homology basis `{a_1, …, a_g, b_1, …, b_g}` is
`IsCanonicalHomologyBasis a b`; the index `ℵ_j` of (1.2.1) is `Sum.elim a b : Fin g ⊕ Fin g → H₁`. A *harmonic differential* is
a form `w` with `w.IsForm` and `IsHarmonicForm w univ`; the space `H` of harmonic differentials (complex valued) has
dimension `2g` (`thm3_2_1`: a basis indexed by `Fin g ⊕ Fin g`). The holomorphic differentials are
`Forster1981.IsAbelianDiff1`. The matrix `J` is `symplecticJ`. The inner product is `HasL2Inner univ` and the norm
square `HasL2Inner univ ω ω ‖ω‖²`.

* Theorem III.2.1 (`dim H = 2g`) — `thm3_2_1`
* Corollary III.2.1 (the dual basis of a canonical homology basis; prescribed periods) — `symplecticJ`, `IsDualBasis`, `cor3_2_1_a`, `cor3_2_1_b`
* III.2.2 (the intersection matrix of the dual basis is `J`) — `para3_2_2`
* Proposition III.2.3 — `prop3_2_3`
* Corollary III.2.3 — `cor3_2_3`
* III.2.4 (the Gram matrix `Γ` is real, symmetric, positive definite) — `para3_2_4`
* III.2.5 (the matrix of `*` on `H`: `𝒢² = −I`, `Γ = 𝒢 ᵗJ`) — `para3_2_5`
* Proposition III.2.7 (`dim ℋ¹(M) = g`, the basis `ω_j = α_j + i*α_j`) — `prop3_2_7`
* Proposition III.2.8, part (a) (the normalized basis `ζ_k`) — `IsNormalizedBasis`, `prop3_2_8_a`
* Proposition III.2.8, part (b) (the period matrix `Π`) — `prop3_2_8_b`

Omitted (U−): III.2.6 (the holomorphic differentials `ω_j` and the matrix `Γ + iJ`: a computation folded into III.2.7), the
Remark after III.2.3, the Remark after III.2.8.
-/

open scoped Manifold ContDiff Topology Matrix
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {x₀ : X} {g : ℕ}

/-- **The intersection matrix `J`** (Ch. III §1.2, (1.2.1)). The `2g × 2g` matrix `[[0, I], [−I, 0]]` indexed by
`Fin g ⊕ Fin g`. -/
def symplecticJ (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := Matrix.fromBlocks 0 1 (-1) 0

/-- **Dual basis** (Ch. III §2.1, (2.1.1)). `{α_j}` is dual to the canonical homology basis `{ℵ_k}` when every `α_j` is a real
harmonic differential with `∫_{ℵ_k} α_j = δ_{jk}`. -/
def IsDualBasis (a b : Fin g → Abelianization (FundamentalGroup X x₀)) (α : Fin g ⊕ Fin g → Form1 X) : Prop :=
  ∀ j, (α j).IsForm ∧ (α j).IsSmoothOn univ ∧ IsHarmonicForm (α j) univ ∧ conjForm (α j) = α j ∧
    ∀ k, IsPeriodOf (α j) (Sum.elim a b k) (if k = j then 1 else 0)

/-- **Theorem III.2.1** (Ch. III §2.1). On a compact Riemann surface `M` of genus `g`, the vector space `H` of harmonic
differentials has dimension `2g`: there is a basis of `H` indexed by `Fin g ⊕ Fin g`. -/
theorem thm3_2_1 [CompactSpace X] (hX : LiZhongQC.HasGenus X g) :
    ∃ α : Fin g ⊕ Fin g → Form1 X, (∀ j, (α j).IsForm ∧ IsHarmonicForm (α j) univ) ∧ LinearIndependent ℂ α ∧
      ∀ w : Form1 X, w.IsForm → IsHarmonicForm w univ → ∃ c : Fin g ⊕ Fin g → ℂ,
        Form1.EqOn w (∑ j, c j • α j) univ := by
  sorry

/-- **Corollary III.2.1, part (a)** (Ch. III §2.1). Given a canonical homology basis `{ℵ_1, …, ℵ_{2g}}` for `H₁(M)` there is a
unique dual basis `{α_1, …, α_{2g}}` of `H`; furthermore each `α_j` is real. -/
theorem cor3_2_1_a [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) :
    (∃ α : Fin g ⊕ Fin g → Form1 X, IsDualBasis a b α) ∧
      ∀ α α₁ : Fin g ⊕ Fin g → Form1 X, IsDualBasis a b α → IsDualBasis a b α₁ →
        ∀ j, Form1.EqOn (α j) (α₁ j) univ := by
  sorry

/-- **Corollary III.2.1, part (b)** (Ch. III §2.1). Given any set of `2g` complex numbers `c_1, …, c_{2g}`, there is a unique
harmonic differential whose `ℵ_k` period is `c_k`, `k = 1, …, 2g`. -/
theorem cor3_2_1_b [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) (c : Fin g ⊕ Fin g → ℂ) :
    ∃ w : Form1 X, w.IsForm ∧ IsHarmonicForm w univ ∧ (∀ k, IsPeriodOf w (Sum.elim a b k) (c k)) ∧
      ∀ w₁ : Form1 X, w₁.IsForm → IsHarmonicForm w₁ univ → (∀ k, IsPeriodOf w₁ (Sum.elim a b k) (c k)) →
        Form1.EqOn w w₁ univ := by
  sorry

/-- **Unlabelled** (Ch. III §2.2, FK1:2467–2473). The matrix with `(k, j)`-entry `∬_M α_k ∧ α_j` of the dual basis is
`J = [[0, I], [−I, 0]]`; equivalently `(α_k, −*α_j) = ℵ_k · ℵ_j`. -/
theorem para3_2_2 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {α : Fin g ⊕ Fin g → Form1 X} (hα : IsDualBasis a b α) (k j : Fin g ⊕ Fin g) :
    HasIntegral2 ((α k).wedge (α j)) ((symplecticJ g k j : ℤ) : ℂ) := by
  sorry

/-- **Proposition III.2.3** (Ch. III §2.3). If `θ` and `θ̃` are two closed differentials on `M` (compact of genus `g`), then
`∬_M θ ∧ θ̃ = Σ_j [∫_{a_j} θ ∫_{b_j} θ̃ − ∫_{b_j} θ ∫_{a_j} θ̃]`, for the periods over a canonical homology basis. -/
theorem prop3_2_3 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {θ θ₁ : Form1 X} (h₁ : θ.IsForm) (h₂ : θ.IsSmoothOn univ)
    (h₃ : θ.IsClosed univ) (h₄ : θ₁.IsForm) (h₅ : θ₁.IsSmoothOn univ) (h₆ : θ₁.IsClosed univ)
    {A B A₁ B₁ : Fin g → ℂ}
    (hA : ∀ j, IsPeriodOf θ (a j) (A j)) (hB : ∀ j, IsPeriodOf θ (b j) (B j))
    (hA₁ : ∀ j, IsPeriodOf θ₁ (a j) (A₁ j)) (hB₁ : ∀ j, IsPeriodOf θ₁ (b j) (B₁ j)) :
    HasIntegral2 (θ.wedge θ₁) (∑ j, (A j * B₁ j - B j * A₁ j)) := by
  sorry

/-- **Corollary III.2.3** (Ch. III §2.3). If `θ` is a harmonic 1-form on `M`, then
`‖θ‖² = Σ_j [∫_{a_j} θ ∫_{b_j} *θ̄ − ∫_{b_j} θ ∫_{a_j} *θ̄]`. -/
theorem cor3_2_3 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {θ : Form1 X} (h₁ : θ.IsForm) (h₂ : IsHarmonicForm θ univ)
    {A B A₁ B₁ : Fin g → ℂ} (hA : ∀ j, IsPeriodOf θ (a j) (A j)) (hB : ∀ j, IsPeriodOf θ (b j) (B j))
    (hA₁ : ∀ j, IsPeriodOf (starForm (conjForm θ)) (a j) (A₁ j))
    (hB₁ : ∀ j, IsPeriodOf (starForm (conjForm θ)) (b j) (B₁ j)) :
    HasL2Inner univ θ θ (∑ j, (A j * B₁ j - B j * A₁ j)) := by
  sorry

/-- **Unlabelled** (Ch. III §2.4, FK1:2557–2591). The matrix `Γ = (γ_{kj})`, `γ_{kj} = (α_k, α_j) = ∬_M α_k ∧ *α_j`, is a real
symmetric positive definite matrix. -/
theorem para3_2_4 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {α : Fin g ⊕ Fin g → Form1 X} (hα : IsDualBasis a b α) :
    ∃ Γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ, (∀ k j, HasL2Inner univ (α k) (α j) (Γ k j)) ∧ Γ.IsSymm ∧
      Γ.PosDef := by
  sorry

/-- **Unlabelled** (Ch. III §2.5, FK1:2593–2621). The operator `*` on the space `H` of harmonic differentials is represented
by a real matrix `𝒢` with `*α_k = Σ_j λ_{kj} α_j`; then `𝒢² = −I` and `Γ = 𝒢 ᵗJ`. -/
theorem para3_2_5 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {α : Fin g ⊕ Fin g → Form1 X} (hα : IsDualBasis a b α)
    {Γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ} (hΓ : ∀ k j, HasL2Inner univ (α k) (α j) (Γ k j)) :
    ∃ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      (∀ k, Form1.EqOn (starForm (α k)) (∑ j, ((G k j : ℝ) : ℂ) • α j) univ) ∧ G * G = -1 ∧
        Γ = G * ((symplecticJ g).map (Int.cast : ℤ → ℝ))ᵀ := by
  sorry

/-- **Proposition III.2.7** (Ch. III §2.7). On a compact Riemann surface of genus `g`, the vector space `ℋ¹(M)` of holomorphic
differentials has dimension `g`. Furthermore, `{ω_1, …, ω_g}`, `ω_j = α_j + i*α_j`, forms a basis for `ℋ¹(M)`. -/
theorem prop3_2_7 [CompactSpace X] {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {α : Fin g ⊕ Fin g → Form1 X} (hα : IsDualBasis a b α) :
    (∀ j : Fin g, IsAbelianDiff1 (α (Sum.inl j) + Complex.I • starForm (α (Sum.inl j)))) ∧
      LinearIndependent ℂ (fun j : Fin g => α (Sum.inl j) + Complex.I • starForm (α (Sum.inl j))) ∧
      ∀ w : Form1 X, IsAbelianDiff1 w → ∃ c : Fin g → ℂ,
        Form1.EqOn w (∑ j, c j • (α (Sum.inl j) + Complex.I • starForm (α (Sum.inl j)))) univ := by
  sorry

/-- **Normalized basis of the holomorphic differentials** (Ch. III §2.8, helper). A basis `{ζ_1, …, ζ_g}` of the space of
holomorphic abelian differentials with `∫_{a_j} ζ_k = δ_{jk}`. -/
def IsNormalizedBasis (a : Fin g → Abelianization (FundamentalGroup X x₀)) (ζ : Fin g → Form1 X) : Prop :=
  (∀ k, IsAbelianDiff1 (ζ k)) ∧ LinearIndependent ℂ ζ ∧
    (∀ w : Form1 X, IsAbelianDiff1 w → ∃ c : Fin g → ℂ, Form1.EqOn w (∑ k, c k • ζ k) univ) ∧
    ∀ j k, IsPeriodOf (ζ k) (a j) (if j = k then 1 else 0)

/-- **Proposition III.2.8, part (a)** (Ch. III §2.8). There exists a unique basis `{ζ_1, …, ζ_g}` for the space of holomorphic
abelian differentials with the property `∫_{a_j} ζ_k = δ_{jk}`. -/
theorem prop3_2_8_a [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) :
    (∃ ζ : Fin g → Form1 X, IsNormalizedBasis a ζ) ∧
      ∀ ζ ζ₁ : Fin g → Form1 X, IsNormalizedBasis a ζ → IsNormalizedBasis a ζ₁ →
        ∀ k, Form1.EqOn (ζ k) (ζ₁ k) univ := by
  sorry

/-- **Proposition III.2.8, part (b)** (Ch. III §2.8). For this basis, the matrix `Π = (π_{jk})`, `π_{jk} = ∫_{b_j} ζ_k`, is
symmetric with positive definite imaginary part. -/
theorem prop3_2_8_b [CompactSpace X] (hX : LiZhongQC.HasGenus X g) {a b : Fin g → Abelianization (FundamentalGroup X x₀)}
    (hab : IsCanonicalHomologyBasis a b) {ζ : Fin g → Form1 X} (hζ : IsNormalizedBasis a ζ)
    {P : Matrix (Fin g) (Fin g) ℂ} (hP : ∀ j k, IsPeriodOf (ζ k) (b j) (P j k)) :
    P.IsSymm ∧ (P.map Complex.im).PosDef := by
  sorry

end FarkasKra1992
