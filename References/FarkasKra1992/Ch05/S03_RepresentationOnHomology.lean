import References.FarkasKra1992.Ch05.S01_HurwitzTheorem
import References.FarkasKra1992.Ch03.S02_HarmonicAndAnalyticDifferentials

/-!
# Farkas–Kra, Chapter V §3: Representation of Aut M on H₁(M)

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. V §3 (`full.md` FK2:4596–4901).

Conventions: as in `Ch05/S01_HurwitzTheorem` (`M` compact of genus `g`, `Aut M` = biholomorphic `T : M ≃ₜ M`) and
`Ch03/S01–S02` (`H₁(M) = Abelianization(π₁(M, x₀))`, canonical homology basis `IsCanonicalHomologyBasis a b`, `κ = (a, b)`,
`IsPeriodOf`, `IsDualBasis`, `symplecticJ g = J₀`). The action of `T` on `H₁(M)` is the push-forward of loops composed with the
change of base point along a path `γ` from `x₀` to `T x₀` (`homologyAction`); on the abelianization it does not depend on `γ`
(`para5_3_1`). `Tκ = Xκ` is `HasHomologyMatrix`. The symplectic group is `IsSymplecticFK g X` (`det X = 1`, `X J₀ Xᵗ = J₀`;
unimodularity is part of FK's definition).

* Definition V.3.1 (the action of `T` on `H₁(M)`, `Tκ = Xκ`) — `homologyAction`, `HasHomologyMatrix`
* Definition V.3.1 (the symplectic group `Sp(g, ℤ)`) — `IsSymplecticFK`
* V.3.1 (the action does not depend on the path) — `para5_3_1`
* Theorem V.3.1 (existence and uniqueness of `X ∈ Sp(g, ℤ)`) — `thm5_3_1_a`
* Theorem V.3.1 (the map `T ↦ X` is an anti-homomorphism, `T ↦ Xᵗ` is a homomorphism) — `thm5_3_1_b`
* Theorem V.3.1 (injectivity for `g ≥ 2`) — `thm5_3_1_c`
* Corollary V.3.1 — `cor5_3_1`
* V.3.2 (the action on forms, `Tω = ω ∘ T⁻¹`) — `IsForm1Pushforward`
* Theorem V.3.2 — `thm5_3_2`
* Theorem V.3.3 — `thm5_3_3`
* Lemma V.3.3, part 1 (first rows of `SL(n, ℤ)`) — `lem5_3_3_a`
* Lemma V.3.3, part 2 (first rows of `Sp(n, ℤ)`) — `lem5_3_3_b`
* Lemma V.3.4 (Serre) — `lem5_3_4`
* Theorem V.3.4 (the action on `H₁(M, ℤ_n)`) — `thm5_3_4_a`
* Theorem V.3.4 (the kernel for `n = 2`) — `thm5_3_4_b`

Omitted (U−): the Remark after the Definition of `Sp(g, ℤ)` (closure under inverses) and the Remark after Theorem V.3.2 (block form
of `ᵗ(X⁻¹)`).
**Readings:** (i) FK's "natural homomorphism `h : Aut M → Sp(g, ℤ)`" is, for the row convention `Tκ = Xκ` (3.1.1), an
anti-homomorphism `X_{T₁T₂} = X_{T₂} X_{T₁}`; `T ↦ Xᵗ` is a homomorphism (`thm5_3_1_b`); (ii) in Lemma V.3.4 the modulus is
`n ≥ 2` (for `n = 1` every matrix is `≡ I`); (iii) the natural homomorphism `Aut M → Sp(g, ℤ_n)` is `T ↦ X mod n`.
-/

open scoped Manifold ContDiff Topology References ComplexConjugate Matrix
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsBiholomorphic HasGenus)

section Defs

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **The action of an automorphism on `H₁(M)`** (Ch. V §3.1). The push-forward of loops at `x₀` by `T`, followed by the change of
base point from `T x₀` back to `x₀` along the path `γ`, on abelianizations. -/
def homologyAction (T : M ≃ₜ M) (x₀ : M) (γ : Path x₀ (T x₀)) :
    Abelianization (FundamentalGroup M x₀) →* Abelianization (FundamentalGroup M x₀) :=
  Abelianization.map ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm.toMonoidHom.comp
    (FundamentalGroup.map (T : C(M, M)) x₀))

/-- **`Tκ = Xκ`** (Ch. V §3.1, (3.1.1)). The matrix `X` (integer entries) of the action of `T` on the homology basis
`κ = (a_1, …, a_g, b_1, …, b_g)`: `T κ_j = Σ_l x_{jl} κ_l` in `H₁(M)` (written additively). -/
def HasHomologyMatrix {x₀ : M} {g : ℕ} (T : M ≃ₜ M) (γ : Path x₀ (T x₀)) (a b : Fin g → Abelianization (FundamentalGroup M x₀))
    (X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ j, Additive.ofMul (homologyAction T x₀ γ (Sum.elim a b j)) = ∑ l, X j l • Additive.ofMul (Sum.elim a b l)

/-- **The symplectic group `Sp(g, ℤ)`** (Ch. V §3.1, Definition, (3.1.3)). The unimodular `2g × 2g` integer matrices with
`X J₀ Xᵗ = J₀`, `J₀ = [0 I; −I 0]`. -/
def IsSymplecticFK (g : ℕ) (X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  X.det = 1 ∧ X * symplecticJ g * Xᵀ = symplecticJ g

/-- **The action of an automorphism on 1-forms** (Ch. V §3.2). `w'` represents `Tw = w ∘ T⁻¹` for `w = u dz + v dz̄`: both
coefficients of `w'` vanish off the chart targets, and in the preferred chart at `x`, for `z` in its target, with the moving
point `p = T⁻¹(φ_x⁻¹ z)` and `ψ = (chart at p) ∘ T⁻¹ ∘ (chart at x)⁻¹` (defined near `z`), `u'(z) = u_p(φ_p p) ψ'(z)`,
`v'(z) = v_p(φ_p p) conj ψ'(z)`. [CORRECTION, FK-fix2] The chart is taken at the moving point `p`, as in
`Forster1981.Form1.pullback`, and the off-target clause is added (AUDIT5_FK F4). -/
def IsForm1Pushforward (T : M ≃ₜ M) (w w' : Form1 M) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → w'.1 x z = 0 ∧ w'.2 x z = 0) ∧
    ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      w'.1 x z = w.1 (T.symm ((chartAt ℂ x).symm z))
          (chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm z))) *
          deriv (fun u => chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm u))) z ∧
        w'.2 x z = w.2 (T.symm ((chartAt ℂ x).symm z))
          (chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm z))) *
          conj (deriv (fun u => chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm u))) z)

end Defs

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  {x₀ : M}

/-- **Unlabelled** (Ch. V §3.1). The action of `T` on `H₁(M)` does not depend on the path used to change the base point. -/
theorem para5_3_1 (T : M ≃ₜ M) (γ γ' : Path x₀ (T x₀)) : homologyAction T x₀ γ = homologyAction T x₀ γ' := by
  sorry

/-- **Theorem V.3.1, part 1** (Ch. V §3.1). Let `T ∈ Aut M` and `κ = (a, b)` a canonical homology basis. Then there is exactly one
integer matrix `X` with `Tκ = Xκ`, and `X ∈ Sp(g, ℤ)` (`det X = 1` since `T` preserves the orientation). -/
theorem thm5_3_1_a {g : ℕ} (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀)) :
    ∃! X, HasHomologyMatrix T γ a b X ∧ IsSymplecticFK g X := by
  sorry

/-- **Theorem V.3.1, part 2** (Ch. V §3.1; homomorphism property, see the reading (i)). If `X₁`, `X₂` are the matrices of `T₁`, `T₂`
(row convention `Tκ = Xκ`), then `X₂ X₁` is the matrix of `T₁ ∘ T₂`; hence `T ↦ Xᵗ` is a homomorphism `Aut M → Sp(g, ℤ)`. -/
theorem thm5_3_1_b {g : ℕ} (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T₁ T₂ : M ≃ₜ M) (h₁ : IsBiholomorphic (T₁ : M → M))
    (h₂ : IsBiholomorphic (T₂ : M → M)) (γ₁ : Path x₀ (T₁ x₀)) (γ₂ : Path x₀ (T₂ x₀)) (γ₁₂ : Path x₀ ((T₁ * T₂) x₀))
    {X₁ X₂ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hX₁ : HasHomologyMatrix T₁ γ₁ a b X₁)
    (hX₂ : HasHomologyMatrix T₂ γ₂ a b X₂) : HasHomologyMatrix (T₁ * T₂) γ₁₂ a b (X₂ * X₁) := by
  sorry

/-- **Theorem V.3.1, part 3** (Ch. V §3.1). For `g ≥ 2` the map `T ↦ X` is injective: two automorphisms with the same matrix
coincide. -/
theorem thm5_3_1_c {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T₁ T₂ : M ≃ₜ M) (h₁ : IsBiholomorphic (T₁ : M → M))
    (h₂ : IsBiholomorphic (T₂ : M → M)) (γ₁ : Path x₀ (T₁ x₀)) (γ₂ : Path x₀ (T₂ x₀))
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hX₁ : HasHomologyMatrix T₁ γ₁ a b X)
    (hX₂ : HasHomologyMatrix T₂ γ₂ a b X) : T₁ = T₂ := by
  sorry

/-- **Corollary V.3.1** (Ch. V §3.1). Let `g ≥ 2`. If `T(a_j) = a_j` in `H₁(M)` for `j = 1, …, g`, then `T = 1`. -/
theorem cor5_3_1 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀))
    (hfix : ∀ j, homologyAction T x₀ γ (a j) = a j) : T = 1 := by
  sorry

/-- **Theorem V.3.2** (Ch. V §3.2). Let `X ∈ Sp(g, ℤ)` represent `T` on `H₁(M, ℤ)` with respect to the canonical homology basis
`κ`, and let `α = (α_1, …, α_{2g})` be the basis of the harmonic differentials dual to `κ` (`∫_{κ_j} α_k = δ_{kj}`). Then the
matrix of `T` on the harmonic differentials with respect to `α` is `ᵗ(X⁻¹)`: `Tα_l = Σ_k (ᵗ(X⁻¹))_{lk} α_k`. -/
theorem thm5_3_2 {g : ℕ} (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀))
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hX : HasHomologyMatrix T γ a b X) (hXs : IsSymplecticFK g X)
    {α β : Fin g ⊕ Fin g → Form1 M} (hα : ∀ k, (α k).IsForm ∧ IsHarmonicForm (α k) univ)
    (hdual : ∀ j k, IsPeriodOf (α k) (Sum.elim a b j) (if k = j then 1 else 0))
    (hβ : ∀ l, IsForm1Pushforward T (α l) (β l)) (l : Fin g ⊕ Fin g) :
    Form1.EqOn (β l) (∑ k, (((X.map (Int.cast : ℤ → ℂ))ᵀ)⁻¹ l k) • α k) univ := by
  sorry

/-- **Theorem V.3.3** (Ch. V §3.3). Let `M` have genus `g ≥ 2` and let `T ∈ Aut M` satisfy `T(a_1) = a_1`, `T(a_2) = a_2`,
`T(b_1) = b_1`, `T(b_2) = b_2` in `H₁(M)`. Then `T = 1`. -/
theorem thm5_3_3 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀))
    (hfix : ∀ j : Fin g, j.val < 2 → homologyAction T x₀ γ (a j) = a j ∧ homologyAction T x₀ γ (b j) = b j) : T = 1 := by
  sorry

/-- **Lemma V.3.3, part 1** (Ch. V §3.3). Let `a ∈ ℤⁿ`. A necessary and sufficient condition for `ᵗa` to be the first row of an
element of `SL(n, ℤ)` is that the components of `a` be relatively prime.
[CORRECTION, FK-fix3] Indexed by `Fin (n + 2)` (`n + 2 ≥ 2` rows): for one row the equivalence fails (`a = (−1)` has `gcd = 1`, but
`SL(1, ℤ) = {1}`; AUDITR2_FK R2FK-3). -/
theorem lem5_3_3_a {n : ℕ} (a : Fin (n + 2) → ℤ) :
    (∃ X : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ, X.det = 1 ∧ X 0 = a) ↔ Finset.univ.gcd a = 1 := by
  sorry

/-- **Lemma V.3.3, part 2** (Ch. V §3.3). Let `a, b ∈ ℤⁿ`. A necessary and sufficient condition for `(ᵗa, ᵗb)` to be the first row
of an element of `Sp(n, ℤ)` is that its components be relatively prime. -/
theorem lem5_3_3_b {n : ℕ} (a b : Fin (n + 1) → ℤ) :
    (∃ X : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℤ, IsSymplecticFK (n + 1) X ∧
      ∀ i, X (Sum.inl 0) i = Sum.elim a b i) ↔ Finset.univ.gcd (Sum.elim a b) = 1 := by
  sorry

/-- **Lemma V.3.4** (Serre; Ch. V §3.4). Let `A ∈ SL(k, ℤ)` have finite order `m > 1`. If `A ≡ I mod n` (`n ≥ 2`), then
`m = n = 2`. -/
theorem lem5_3_4 {k n : ℕ} (A : Matrix.SpecialLinearGroup (Fin k) ℤ) (hfin : IsOfFinOrder A) (hm : 1 < orderOf A)
    (hn : 1 < n) (hA : ((A : Matrix (Fin k) (Fin k) ℤ).map (Int.cast : ℤ → ZMod n)) = 1) :
    orderOf A = 2 ∧ n = 2 := by
  sorry

/-- **Theorem V.3.4, part 1** (Ch. V §3.4). The action of `Aut M` on `H₁(M, ℤ_n)` (the matrix `X mod n`): for `g ≥ 2` and
`n ≥ 3`, the homomorphism `h : Aut M → Sp(g, ℤ_n)` is injective: if `X ≡ I mod n` then `T = 1`. -/
theorem thm5_3_4_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀))
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hX : HasHomologyMatrix T γ a b X) {n : ℕ} (hn : 3 ≤ n)
    (hXn : X.map (Int.cast : ℤ → ZMod n) = 1) : T = 1 := by
  sorry

/-- **Theorem V.3.4, part 2** (Ch. V §3.4). For `g ≥ 2` and `n = 2`, only automorphisms of order `2` are in the kernel of `h`:
if `X ≡ I mod 2`, then `T = 1` or `T` has order `2`. -/
theorem thm5_3_4_b {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {a b : Fin g → Abelianization (FundamentalGroup M x₀)}
    (hab : IsCanonicalHomologyBasis a b) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (γ : Path x₀ (T x₀))
    {X : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hX : HasHomologyMatrix T γ a b X)
    (hXn : X.map (Int.cast : ℤ → ZMod 2) = 1) : T = 1 ∨ orderOf T = 2 := by
  sorry

end FarkasKra1992
