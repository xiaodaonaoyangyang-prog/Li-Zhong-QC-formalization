import References.Forster1981.Ch02.S17_TheSerreDualityTheorem

/-!
# Forster, Chapter 2 §18: Functions and differential forms with prescribed principal parts

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §18 (`full.md` F1:6580–6851).

Conventions (rulings B0.8): Mittag–Leffler distributions are cochains of `𝓜` (resp. `𝓜^(1)`) whose coboundary comes from a
cocycle of `𝒪` (resp. `Ω`), at representative level through the inclusion `ι`; `[δμ]` appears inside the relations
`IsMLClass`, `IsMLClass1`; `Res(μ)` is the relation `HasMLResidue1` summed over the surface; a solution is the relation
`IsMLSolution`, `IsMLSolution1`. The Wronskian is the determinant of the iterated derivatives (near miss
`Polynomial.wronskian`); `W_z(ω₁, …, ω_g)` is read in the preferred chart at a point (`formWronskian`); a basis of `Ω(X)` is
given by representatives (`IsBasisOfHol`). The weight of a Weierstrass point is the order of zero of the Wronskian.

* Paragraph 18.1 (Mittag–Leffler distributions of functions, F1:6584) — `IsMLDistribution`, `IsMLClass`, `IsMLSolution`,
  `thm18_1`
* Theorem 18.2 (F1:6608) — `IsFormTimesCochain`, `thm18_2`
* Paragraph 18.3 (doubly periodic functions with prescribed principal parts, F1:6636) — `para18_3`
* Paragraph 18.4 (the Wronskian determinant, F1:6666) — `wronskian`, `formWronskian`, `para18_4`
* Theorem 18.5 (F1:6694) — `thm18_5`
* Definition 18.6 (Weierstrass points, F1:6728) — `IsBasisOfHol`, `IsWeierstrassPoint`, `weierstrassWeight`
* Theorem 18.7 (F1:6730) — `thm18_7`
* Theorem 18.8 (F1:6762) — `thm18_8`
* Corollary 18.9 (F1:6802) — `cor18_9_a`, `cor18_9_b`
* Paragraph 18.10 (forms with prescribed principal parts, F1:6806) — `IsMLSolution1`, `para18_10`
* Theorem 18.11 (F1:6808) — `thm18_11`
* Corollary 18.12 (F1:6812) — `cor18_12_a`, `cor18_12_b`

Omitted (U−): the remarks of 18.1, 18.2 (a), (b), the consequence of 18.3, the basis change claim of 18.5, the remark of 18.9.
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Mittag–Leffler distributions of functions** (18.1, Ch. 2 §18, F1:6584): a 0-cochain `μ = (f_i)` of `𝓜` whose
coboundary comes from a cocycle of `𝒪` (the differences `f_j − f_i` are holomorphic); `ι` is the inclusion `𝒪 → 𝓜`. -/
def IsMLDistribution (ι : modO X ⟶ modM X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM X) 𝔘.U) : Prop :=
  ∃ ξ : ↥(cechZ1 (modO X) 𝔘.U), cechMap ι 𝔘.U ξ = cechD0 (modM X) 𝔘.U μ

/-- **The class `[δμ] ∈ H¹(X, 𝒪)`** of a Mittag–Leffler distribution (18.1, Ch. 2 §18, F1:6584). -/
def IsMLClass (ι : modO X ⟶ modM X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM X) 𝔘.U) (c : H1 (modO X) ⊤) : Prop :=
  ∃ ξ : ↥(cechZ1 (modO X) 𝔘.U), cechMap ι 𝔘.U ξ = cechD0 (modM X) 𝔘.U μ ∧ c = cechClass (modO X) 𝔘 ξ

/-- **A solution of a Mittag–Leffler distribution** (18.1, Ch. 2 §18, F1:6584): a global meromorphic function `f` with
`f|U_i − f_i` holomorphic on `U_i` for every `i`. -/
def IsMLSolution (ι : modO X ⟶ modM X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM X) 𝔘.U) (f : H0 (modM X)) : Prop :=
  ∃ g : CechC0 (modO X) 𝔘.U, ∀ i, ι.app (op (𝔘.U i)) (g i) = cechRes (modM X) (le_top : 𝔘.U i ≤ ⊤) f - μ i

/-- **A solution of a Mittag–Leffler distribution of forms** (18.10, Ch. 2 §18, F1:6806): a global meromorphic 1-form `ω`
with `ω|U_i − ω_i` holomorphic on `U_i` for every `i`; `ι` is the inclusion `Ω → 𝓜^(1)`. -/
def IsMLSolution1 (ι : modOmega X ⟶ modM1 X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM1 X) 𝔘.U) (w : H0 (modM1 X)) :
    Prop :=
  ∃ g : CechC0 (modOmega X) 𝔘.U, ∀ i, ι.app (op (𝔘.U i)) (g i) = cechRes (modM1 X) (le_top : 𝔘.U i ≤ ⊤) w - μ i

/-- **The product of a holomorphic 1-form by a cochain of `𝓜`** (18.2, Ch. 2 §18, F1:6608): `ν_i = ω|U_i · μ_i` on
representatives. -/
def IsFormTimesCochain (s : H0 (modOmega X)) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM X) 𝔘.U)
    (ν : CechC0 (modM1 X) 𝔘.U) : Prop :=
  ∀ (i : 𝔘.ι) (a : X → ℂ) (w : Form1 X)
    (ha : a ∈ repSpan (R := ℂ) (fun (a : X → ℂ) x => MeromorphicAt (LiZhongQC.localExpr a x) (chartAt ℂ x x))
      (𝔘.U i : Set X))
    (hw : w ∈ repSpan (R := ℂ) (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧ w.IsHolAt x)
      (𝔘.U i : Set X)),
    (Submodule.Quotient.mk ⟨a, ha⟩ : ↥((modM X).obj (op (𝔘.U i)))) = μ i →
    (Submodule.Quotient.mk ⟨w, hw⟩ : ↥((modOmega X).obj (op (𝔘.U i)))) =
      cechRes (modOmega X) (le_top : 𝔘.U i ≤ ⊤) s →
    ∃ hb : w.smulFun a ∈ repSpan (R := ℂ) (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧
      ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → MeromorphicAt (w.1 y) z) (𝔘.U i : Set X),
      ν i = Submodule.Quotient.mk ⟨w.smulFun a, hb⟩

/-- **The Wronskian determinant** (18.4, Ch. 2 §18, F1:6666): `W(f₁, …, f_g) = det (f_k^{(m)})_{0 ≤ m < g, 1 ≤ k ≤ g}`. -/
noncomputable def wronskian {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (fun (m k : Fin n) => iteratedDeriv m (f k) z)

/-- **The Wronskian of 1-forms in a chart** (18.4, Ch. 2 §18, F1:6666): for `ω_k = f_k dz` in the preferred chart at `x`,
`W_z(ω₁, …, ω_g) = W(f₁, …, f_g)` as a function of the coordinate `z`. -/
noncomputable def formWronskian {n : ℕ} (w : Fin n → Form1 X) (x : X) (z : ℂ) : ℂ :=
  wronskian (fun k => (w k).1 x) z

/-- **A basis of `Ω(X)` by representatives** (18.6, Ch. 2 §18, F1:6728): the classes of the forms `w_k` form a basis of
`Ω(X) = H⁰(X, Ω)`. -/
def IsBasisOfHol {n : ℕ} (w : Fin n → Form1 X) : Prop :=
  ∃ b : Module.Basis (Fin n) ℂ (H0 (modOmega X)), ∀ k, ∃ hk : w k ∈ holFormsOn X ⊤,
    (Submodule.Quotient.mk ⟨w k, hk⟩ : H0 (modOmega X)) = b k

/-- **Weierstrass points** (18.6, Ch. 2 §18, F1:6728): for a basis `ω₁, …, ω_g` of `Ω(X)`, the Wronskian
`W_z(ω₁, …, ω_g)` in a chart at `p` vanishes at `p`. -/
def IsWeierstrassPoint {n : ℕ} (w : Fin n → Form1 X) (p : X) : Prop := formWronskian w p (chartAt ℂ p p) = 0

/-- **The weight** of a Weierstrass point (18.6, Ch. 2 §18, F1:6728): the order of the zero of the Wronskian at `p`
(`0` at points which are not Weierstrass points). -/
noncomputable def weierstrassWeight {n : ℕ} (w : Fin n → Form1 X) (p : X) : ℕ :=
  (analyticOrderAt (formWronskian w p) (chartAt ℂ p p)).toNat

end Defs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 18.1** (Ch. 2 §18, F1:6584). A Mittag–Leffler distribution `μ` has a solution if and only if `[δμ] = 0`. -/
theorem thm18_1 {ι : modO X ⟶ modM X} (hι : IsInducedBy ι (id : (X → ℂ) → (X → ℂ))) {𝔘 : CechCover X ⊤}
    {μ : CechC0 (modM X) 𝔘.U} (hμ : IsMLDistribution ι 𝔘 μ) :
    (∃ f, IsMLSolution ι 𝔘 μ f) ↔ ∀ c, IsMLClass ι 𝔘 μ c → c = 0 := by
  sorry

/-- **Theorem 18.2** (Ch. 2 §18, F1:6608). On a compact Riemann surface, a Mittag–Leffler distribution `μ` of meromorphic
functions has a solution if and only if `Res(ωμ) = 0` for every `ω ∈ Ω(X)`.
Modelling: `Res(ωμ)` is the sum over `X` of the residues `Res_a(ωμ)` of 17.2 (the product `ωμ` is the relation
`IsFormTimesCochain`). -/
theorem thm18_2 [CompactSpace X] {ι : modO X ⟶ modM X} (hι : IsInducedBy ι (id : (X → ℂ) → (X → ℂ)))
    {𝔘 : CechCover X ⊤} {μ : CechC0 (modM X) 𝔘.U} (hμ : IsMLDistribution ι 𝔘 μ) :
    (∃ f, IsMLSolution ι 𝔘 μ f) ↔
      ∀ (s : H0 (modOmega X)) (ν : CechC0 (modM1 X) 𝔘.U), IsFormTimesCochain s 𝔘 μ ν →
        ∀ r : X → ℂ, (∀ a, HasMLResidue1 𝔘 ν a (r a)) → (∑ᶠ a, r a) = 0 := by
  sorry

/-- **Paragraph 18.3** (Ch. 2 §18, F1:6636). Let `Γ = ℤγ₁ + ℤγ₂` be a lattice, `a_1, …, a_n` distinct points of the period
parallelogram `P` and principal parts `Σ_{ν=1}^{r_j} c^{(j)}_ν (z − a_j)^{−ν}` prescribed at `a_j`. There is a doubly periodic
meromorphic function with exactly these principal parts at the points `a_j` (and their translates by `Γ`) and no other poles if
and only if `Σ_j c^{(j)}_1 = 0`.
[CORRECTION, Forster-fix1] `1 ≤ r_j` (every `a_j` carries a principal part): with `r_j = 0` the sum still counted the
unconstrained `c^{(j)}_1` (`n = 1`, `r = 0`, `c = 1`: `f ≡ 0` against `1 = 0`; AUDIT5_Forster G4). -/
theorem para18_3 (L : PeriodPair) {n : ℕ} (a : Fin n → ℂ) (ha : Function.Injective a)
    (hP : ∀ j, ∃ t₁ ∈ Ico (0 : ℝ) 1, ∃ t₂ ∈ Ico (0 : ℝ) 1, a j = t₁ * L.ω₁ + t₂ * L.ω₂) (r : Fin n → ℕ)
    (hr : ∀ j, 1 ≤ r j) (c : Fin n → ℕ → ℂ) :
    (∃ f : ℂ → ℂ, (∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) ∧
      (∀ j, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (a j) ∧ ∀ᶠ z in 𝓝[≠] (a j),
        f z = g z + ∑ ν ∈ Finset.Icc 1 (r j), c j ν / (z - a j) ^ ν) ∧
      ∀ z, (∀ j, ∀ l ∈ L.lattice, z ≠ a j + l) → AnalyticAt ℂ f z) ↔ ∑ j, c j 1 = 0 := by
  sorry

/-- **Paragraph 18.4** (Ch. 2 §18, F1:6666). If `f₁, …, f_g` are holomorphic and linearly independent over `ℂ` on a domain
`U ⊆ ℂ`, then the Wronskian determinant `W(f₁, …, f_g)` does not vanish identically. -/
theorem para18_4 {n : ℕ} {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {f : Fin n → ℂ → ℂ}
    (hf : ∀ k, DifferentiableOn ℂ (f k) U) (hli : LinearIndependent ℂ (fun k (z : U) => f k z)) :
    ¬ ∀ z ∈ U, wronskian f z = 0 := by
  sorry

/-- **Theorem 18.5** (Ch. 2 §18, F1:6694). Let `ω₁, …, ω_g` be holomorphic 1-forms and `(U, z)`, `(Ũ, z̃)` two coordinate
neighbourhoods (the preferred charts at `x` and `x′`). Then on `U ∩ Ũ`:
`W_z(ω₁, …, ω_g) = (dz̃/dz)^N W_z̃(ω₁, …, ω_g)`, `N = g(g + 1)/2`. -/
theorem thm18_5 {n : ℕ} {w : Fin n → Form1 X} (hw : ∀ k, (w k).IsForm ∧ (w k).IsHolomorphicOn univ) {x x' p : X}
    (hx : p ∈ (chartAt ℂ x).source) (hx' : p ∈ (chartAt ℂ x').source) :
    formWronskian w x (chartAt ℂ x p) =
      deriv (LiZhongQC.chartTransition x' x) (chartAt ℂ x p) ^ (n * (n + 1) / 2) * formWronskian w x' (chartAt ℂ x' p) := by
  sorry

/-- **Theorem 18.7** (Ch. 2 §18, F1:6730). Let `X` be a compact Riemann surface of genus `g`, `ω₁, …, ω_g` a basis of
`Ω(X)` and `p ∈ X`. There is a non-constant meromorphic function with a pole of order `≤ g` at `p` and holomorphic on
`X ∖ {p}` if and only if `p` is a Weierstrass point. -/
theorem thm18_7 [CompactSpace X] {w : Fin (genus X) → Form1 X} (hw : IsBasisOfHol w) (p : X) :
    (∃ f : X → ℂ, LiZhongQC.IsMeromorphicRS f ∧ (¬ ∃ c : ℂ, ∀ᶠ x in Filter.codiscrete X, f x = c) ∧
      (∀ x, x ≠ p → 0 ≤ LiZhongQC.ordRS f x) ∧ (-(genus X : ℤ) : ℤ) ≤ LiZhongQC.ordRS f p) ↔
      IsWeierstrassPoint w p := by
  sorry

/-- **Theorem 18.8** (Ch. 2 §18, F1:6762). On a compact Riemann surface of genus `g` the Weierstrass points, counted
with their weights, are finite in number and their number is `(g − 1) g (g + 1)`. -/
theorem thm18_8 [CompactSpace X] {w : Fin (genus X) → Form1 X} (hw : IsBasisOfHol w) :
    (Function.support (weierstrassWeight w)).Finite ∧
      (∑ᶠ p, (weierstrassWeight w p : ℤ)) = ((genus X : ℤ) - 1) * genus X * ((genus X : ℤ) + 1) := by
  sorry

/-- **Corollary 18.9(a)** (Ch. 2 §18, F1:6802). A compact Riemann surface of genus `g ≥ 2` admits a holomorphic covering
`X → ℙ¹` with at most `g` sheets. -/
theorem cor18_9_a [CompactSpace X] (hg : 2 ≤ genus X) :
    ∃ n : ℕ, n ≤ genus X ∧ ∃ f : X → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      IsHolomorphicCovering f n := by
  sorry

/-- **Corollary 18.9(b)** (Ch. 2 §18, F1:6802). Every compact Riemann surface of genus `2` is hyperelliptic. -/
theorem cor18_9_b [CompactSpace X] (hg : genus X = 2) : IsHyperelliptic X := by
  sorry

/-- **Paragraph 18.10** (Ch. 2 §18, F1:6806). A Mittag–Leffler distribution `μ` of meromorphic 1-forms has a solution if and
only if its class `[δμ] ∈ H¹(X, Ω)` vanishes. -/
theorem para18_10 {ι : modOmega X ⟶ modM1 X} (hι : IsInducedBy ι (id : Form1 X → Form1 X)) {𝔘 : CechCover X ⊤}
    {μ : CechC0 (modM1 X) 𝔘.U} (hμ : IsMLDistribution1 ι 𝔘 μ) :
    (∃ w, IsMLSolution1 ι 𝔘 μ w) ↔ ∀ c, IsMLClass1 ι 𝔘 μ c → c = 0 := by
  sorry

/-- **Theorem 18.11** (Ch. 2 §18, F1:6808). On a compact Riemann surface a Mittag–Leffler distribution `μ` of meromorphic
1-forms has a solution if and only if `Res(μ) = 0`. -/
theorem thm18_11 [CompactSpace X] {ι : modOmega X ⟶ modM1 X} (hι : IsInducedBy ι (id : Form1 X → Form1 X))
    {𝔘 : CechCover X ⊤} {μ : CechC0 (modM1 X) 𝔘.U} (hμ : IsMLDistribution1 ι 𝔘 μ) :
    (∃ w, IsMLSolution1 ι 𝔘 μ w) ↔ ∀ r : X → ℂ, (∀ a, HasMLResidue1 𝔘 μ a (r a)) → (∑ᶠ a, r a) = 0 := by
  sorry

/-- **Corollary 18.12(a)** (Ch. 2 §18, F1:6812). On a compact Riemann surface, for every point `p` and every `n ≥ 2` there
is a meromorphic 1-form with a pole of order `n` at `p` and otherwise holomorphic (an elementary differential of the second
kind). -/
theorem cor18_12_a [CompactSpace X] (p : X) {n : ℕ} (hn : 2 ≤ n) :
    ∃ w : Form1 X, w.IsForm ∧ w.IsMeromorphicOn univ ∧ w.orderAt p = ((-(n : ℤ) : ℤ) : WithTop ℤ) ∧
      ∀ x, x ≠ p → (0 : WithTop ℤ) ≤ w.orderAt x := by
  sorry

/-- **Corollary 18.12(b)** (Ch. 2 §18, F1:6812). On a compact Riemann surface, for distinct points `p₁`, `p₂` there is a
meromorphic 1-form with poles of first order at `p₁` and `p₂` with residues `+1` and `−1` and otherwise holomorphic (an
elementary differential of the third kind). -/
theorem cor18_12_b [CompactSpace X] {p₁ p₂ : X} (h : p₁ ≠ p₂) :
    ∃ w : Form1 X, w.IsForm ∧ w.IsMeromorphicOn univ ∧ w.orderAt p₁ = ((-1 : ℤ) : WithTop ℤ) ∧
      w.orderAt p₂ = ((-1 : ℤ) : WithTop ℤ) ∧ HasResidue w p₁ 1 ∧ HasResidue w p₂ (-1) ∧
      ∀ x, x ≠ p₁ → x ≠ p₂ → (0 : WithTop ℤ) ≤ w.orderAt x := by
  sorry

end Statements

end Forster1981
