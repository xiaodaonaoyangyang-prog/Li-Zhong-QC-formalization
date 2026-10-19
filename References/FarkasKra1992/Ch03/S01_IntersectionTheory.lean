import References.FarkasKra1992.Ch01.S03_DifferentialForms
import References.FarkasKra1992.Ch01.S04_IntegrationFormulae
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Farkas–Kra, Chapter III §1: Intersection theory on compact surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §1 (`full.md` FK1:2298–2396).

Conventions: forms are Forster's coefficient forms (`Ch01/S03_DifferentialForms`). The first homology group is
`H₁(M) = Abelianization(π₁(M, x₀))` (leader ruling, 2026-10-09), written multiplicatively; a *cycle* is a class `a ∈ H₁`.
The period `∫_a α` of a closed smooth form `α` over a class `a` is `Forster1981.period` of any loop representing `a`
(`IsPeriodOf`; for a closed form the period is a homomorphism, so it depends only on the class). The form `η_a`
associated with a cycle (III.1.1, built from strips around simple closed curves, II.3.3) is characterized by (1.1.1):
a real smooth closed form with compact support such that `∫_a α = −∬_M α ∧ η_a` for all closed smooth `α`
(`IsAssociatedForm`). The intersection number `a · b = ∬_M η_a ∧ η_b` (1.1.2) is the relation `IsIntersectionNumber`.
The genus is the topological genus `LiZhongQC.HasGenus` (as in Part 1); near miss `Forster1981.genus` (`= dim H¹(M, 𝒪)`, Forster's
definition of the genus, equal to it by Hubbard Prop. A10.1.1). Surface integrals are `Forster1981.HasIntegral2` (compactly supported 2-forms; `ω = f dx ∧ dy`, `∬ ω = ∬ f dx dy`).

* III.1.1 (the form `η_a` associated with a cycle) — `IsPeriodOf`, `IsAssociatedForm`
* Proposition III.1.1 (existence of associated forms) — `prop3_1_1_a`
* Proposition III.1.1 (the intersection number is well defined; it depends only on the homology classes) — `IsIntersectionNumber`, `prop3_1_1_b`
* Proposition III.1.1, (1.1.3) — `prop3_1_1_c`
* Proposition III.1.1, (1.1.4)–(1.1.5) — `prop3_1_1_d`
* Proposition III.1.1, (1.1.6) — `prop3_1_1_e`
* III.1.2 (canonical homology basis) — `IsCanonicalHomologyBasis`
* III.1.2 (existence of a canonical homology basis) — `para3_1_2`

Omitted (U−): the clause "`a · b` counts the number of times `a` intersects `b`" of Proposition III.1.1 (a topological
remark with no precise statement), the matrix `J` (it is the definition of `IsCanonicalHomologyBasis`).
-/

open scoped Manifold ContDiff Topology
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {x₀ : X}

/-- **The period over a homology class** (Ch. III §1.1, helper). `∫_a α = v` for a class `a ∈ H₁(M) = Abelianization(π₁)`:
every loop `σ` representing `a` has `Forster1981.period α σ = v`. -/
def IsPeriodOf (w : Form1 X) (a : Abelianization (FundamentalGroup X x₀)) (v : ℂ) : Prop :=
  ∀ σ : FundamentalGroup X x₀, Abelianization.of σ = a → period w σ = v

/-- **The form associated with a cycle** (Ch. III §1.1). A real, smooth, closed 1-form `η` with compact support such that
`∫_a α = −∬_M α ∧ η` (1.1.1) for all closed smooth forms `α`. -/
def IsAssociatedForm (a : Abelianization (FundamentalGroup X x₀)) (η : Form1 X) : Prop :=
  η.IsForm ∧ η.IsSmoothOn univ ∧ η.IsClosed univ ∧ conjForm η = η ∧
    (∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, η.pointValue x = (0, 0)) ∧
    ∀ α : Form1 X, α.IsForm → α.IsSmoothOn univ → α.IsClosed univ →
      ∃ v : ℂ, IsPeriodOf α a v ∧ HasIntegral2 (α.wedge η) (-v)

/-- **Intersection number** (Ch. III §1.1, (1.1.2)). `a · b = ∬_M η_a ∧ η_b` for associated forms `η_a`, `η_b`: the relation
"`n` is the intersection number of `a` and `b`".
Near miss: `GardinerLakic2000.intersectionNumber` (the geometric minimal number of intersection points of simple loops in the free
homotopy classes, in `ℕ∞`; here the algebraic, signed number on homology classes, which may be negative). -/
def IsIntersectionNumber (a b : Abelianization (FundamentalGroup X x₀)) (n : ℂ) : Prop :=
  ∃ ηa ηb : Form1 X, IsAssociatedForm a ηa ∧ IsAssociatedForm b ηb ∧ HasIntegral2 (ηa.wedge ηb) n

/-- **Proposition III.1.1(a)** (Ch. III §1.1). To every cycle `c` on `M` we can associate a real closed differential `η_c` with
compact support such that (1.1.1) holds. -/
theorem prop3_1_1_a (a : Abelianization (FundamentalGroup X x₀)) : ∃ η : Form1 X, IsAssociatedForm a η := by
  sorry

/-- **Proposition III.1.1(b)** (Ch. III §1.1). The intersection number is well defined: for associated forms `η_a`, `η_b` and
`η_a′`, `η_b′` of the same classes, `∬ η_a ∧ η_b = ∬ η_a′ ∧ η_b′` (the integrals exist). -/
theorem prop3_1_1_b (a b : Abelianization (FundamentalGroup X x₀)) :
    ∃ n : ℂ, ∀ ηa ηb : Form1 X, IsAssociatedForm a ηa → IsAssociatedForm b ηb → HasIntegral2 (ηa.wedge ηb) n := by
  sorry

/-- **Proposition III.1.1, (1.1.3)** (Ch. III §1.1). `a · b = −b · a`. -/
theorem prop3_1_1_c {a b : Abelianization (FundamentalGroup X x₀)} {n : ℂ} (h : IsIntersectionNumber a b n) :
    IsIntersectionNumber b a (-n) := by
  sorry

/-- **Proposition III.1.1, (1.1.4)–(1.1.5)** (Ch. III §1.1). The intersection number is bilinear: `(a + b) · c = a · c + b · c`
(the sum of cycles is the product in `Abelianization`). -/
theorem prop3_1_1_d {a b c : Abelianization (FundamentalGroup X x₀)} {n m : ℂ} (h₁ : IsIntersectionNumber a c n)
    (h₂ : IsIntersectionNumber b c m) : IsIntersectionNumber (a * b) c (n + m) := by
  sorry

/-- **Proposition III.1.1, (1.1.6)** (Ch. III §1.1). `a · b ∈ ℤ`. -/
theorem prop3_1_1_e {a b : Abelianization (FundamentalGroup X x₀)} {n : ℂ} (h : IsIntersectionNumber a b n) :
    ∃ k : ℤ, n = k := by
  sorry

/-- **Canonical homology basis** (Ch. III §1.2). On a compact surface of genus `g`, a basis `{a_1, …, a_g, b_1, …, b_g}` of
`H₁` (a `ℤ`-basis of the abelian group `H₁`) with intersection numbers `a_j · b_k = δ_{jk}`, `a_j · a_k = 0 = b_j · b_k`
(the matrix `J = [[0, I], [−I, 0]]`). -/
def IsCanonicalHomologyBasis {g : ℕ} (a b : Fin g → Abelianization (FundamentalGroup X x₀)) : Prop :=
  (∀ h : Abelianization (FundamentalGroup X x₀), ∃! m : Fin g ⊕ Fin g → ℤ,
    h = (∏ j, a j ^ m (Sum.inl j)) * ∏ j, b j ^ m (Sum.inr j)) ∧
    ∀ j k, IsIntersectionNumber (a j) (b k) (if j = k then 1 else 0) ∧ IsIntersectionNumber (a j) (a k) 0 ∧
      IsIntersectionNumber (b j) (b k) 0

/-- **Unlabelled** (Ch. III §1.2, FK1:2375). A compact Riemann surface of genus `g` has a canonical homology basis (the sides of
the polygon of the symbol `∏ b_j a_j b_j⁻¹ a_j⁻¹`, whose intersection properties are "easy to check"). -/
theorem para3_1_2 {g : ℕ} [CompactSpace X] (hX : LiZhongQC.HasGenus X g) :
    ∃ a b : Fin g → Abelianization (FundamentalGroup X x₀), IsCanonicalHomologyBasis a b := by
  sorry

end FarkasKra1992
