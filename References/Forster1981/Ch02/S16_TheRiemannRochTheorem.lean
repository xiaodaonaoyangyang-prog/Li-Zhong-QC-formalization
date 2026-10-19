import References.Forster1981.Ch02.S15_TheExactCohomologySequence

/-!
# Forster, Chapter 2 §16: The Riemann–Roch theorem

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16 (`full.md` F1:5588–5849).

Conventions (ruling B0.6): `Div X` is `Function.locallyFinsupp X ℤ` (locally finite support, as the book needs; near miss
`LiZhongQC.Divisor`, a finitely supported function), with its order and the point divisor `divSingle`. The order of a meromorphic function is
`LiZhongQC.ordRS`, that of a 1-form is `Form1.orderAt`. "`(f) = D`" is the relation `IsDivisorOf f D` (a function `divisorOf`
would need the identity theorem), likewise `IsDivisorOfForm`. `deg D := ∑ᶠ x, D x` (junk `0` only for infinite support, never
on a compact surface). The sheaf `𝒪_D` of meromorphic functions `f` with `(f) ≥ −D` is built by `localRepPresheaf` with
representatives modulo functions vanishing off a discrete set; `ℂ_P` is the skyscraper sheaf. The genus is `genus X`
(`dim H¹(X, 𝒪)`); near miss `LiZhongQC.thm22_4_riemann_roch` (Riemann–Roch for the project's divisors).

* Paragraph 16.1 (the group `Div(X)`, F1:5592) — exists: `Function.locallyFinsupp`
* Paragraph 16.2 (the divisor of a function or form, F1:5600) — exists: `LiZhongQC.ordRS`, `Forster1981.Form1.orderAt`
* Paragraph 16.2 (divisors, principal and canonical, F1:5600) — `IsDivisorOf`, `IsDivisorOfForm`, `IsPrincipalDivisor`,
  `AreEquivalentDivisors`, `IsCanonicalDivisor`, `para16_2`
* Paragraph 16.1 (the divisor `n·P`, F1:5592) — `divSingle` (a wrapper of Mathlib's point divisor (locallyFinsuppWithin.single) with classical
  decidability)
* Paragraph 16.3 (the degree, F1:5622) — `divDeg`, `para16_3`
* Paragraph 16.4 (the sheaf `𝒪_D`, F1:5636) — `modOD`, `para16_4`
* Theorem 16.5 (F1:5650) — `thm16_5`
* Paragraph 16.6 (the skyscraper sheaf `ℂ_P`, F1:5660) — `modSkyscraper`, `para16_6`
* Paragraph 16.7 (F1:5672) — `para16_7`
* Corollary 16.8 (F1:5702) — `cor16_8`
* Theorem 16.9 (Riemann–Roch, F1:5710) — `thm16_9`
* Definition 16.10 (index of speciality, F1:5764) — `specialityIndex`
* Theorem 16.11 (F1:5782) — `thm16_11`
* Corollary 16.12 (F1:5792) — `cor16_12`
* Corollary 16.13 (F1:5796) — `cor16_13`

Omitted (U−): "holomorphic ⇔ `(f) ≥ 0`", chart independence and "canonical divisors are equivalent" (16.2), "`deg` is a
homomorphism" (16.3), "`𝒪_D` is a sheaf" and `𝒪₀ = 𝒪` (16.4), item (i) of 16.6, the long exact sequence `(*)` of 16.7, the
claims of 16.10.

Reading (16.12): "Riemann surface of genus `g`" is a *compact* Riemann surface.
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

open scoped Classical in
/-- **The divisor `n·P`** (16.1, Ch. 2 §16, F1:5592): the value `n` at `P` and `0` elsewhere. -/
noncomputable def divSingle (P : X) (n : ℤ) : Function.locallyFinsupp X ℤ :=
  Function.locallyFinsuppWithin.single P n

/-- **The degree** of a divisor (16.3, Ch. 2 §16, F1:5622): `deg D = Σ D(x)`. -/
noncomputable def divDeg (D : Function.locallyFinsupp X ℤ) : ℤ := ∑ᶠ x, D x

/-- **The divisor of a meromorphic function** (16.2, Ch. 2 §16, F1:5600): `(f) = D` when `f` is meromorphic and
`ord_x f = D(x)` for every `x`. -/
def IsDivisorOf (f : X → ℂ) (D : Function.locallyFinsupp X ℤ) : Prop :=
  LiZhongQC.IsMeromorphicRS f ∧ ∀ x, LiZhongQC.ordRS f x = (D x : WithTop ℤ)

/-- **The divisor of a meromorphic 1-form** (16.2, Ch. 2 §16, F1:5600): `(ω) = D`. -/
def IsDivisorOfForm (w : Form1 X) (D : Function.locallyFinsupp X ℤ) : Prop :=
  w.IsForm ∧ w.IsMeromorphicOn univ ∧ ∀ x, w.orderAt x = (D x : WithTop ℤ)

/-- **Principal divisors** (16.2, Ch. 2 §16, F1:5600). -/
def IsPrincipalDivisor (D : Function.locallyFinsupp X ℤ) : Prop := ∃ f : X → ℂ, IsDivisorOf f D

/-- **Equivalent divisors** (16.2, Ch. 2 §16, F1:5600): `D − D′` is principal. -/
def AreEquivalentDivisors (D D' : Function.locallyFinsupp X ℤ) : Prop := IsPrincipalDivisor (D - D')

/-- **Canonical divisors** (16.2, Ch. 2 §16, F1:5600): the divisor of a meromorphic 1-form. Near miss
`LiZhongQC.IsCanonicalDivisor` (the project's finitely supported divisors). -/
def IsCanonicalDivisor (D : Function.locallyFinsupp X ℤ) : Prop := ∃ w : Form1 X, IsDivisorOfForm w D

/-- **The sheaf `𝒪_D`** (16.4, Ch. 2 §16, F1:5636): meromorphic functions `f` with `(f) ≥ −D`; representatives are
meromorphic in every chart with `ord_x f ≥ −D(x)` at the points of the open set, modulo functions vanishing off a
discrete set. -/
abbrev modOD (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (D : Function.locallyFinsupp X ℤ) :
    TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := X → ℂ)
    (fun a x => MeromorphicAt (LiZhongQC.localExpr a x) (chartAt ℂ x x) ∧
      ((-(D x) : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS a x)
    (fun a x => ∀ᶠ y in 𝓝[≠] x, a y = 0)

/-- **The skyscraper sheaf `ℂ_P`** (16.6, Ch. 2 §16, F1:5660): `ℂ_P(U) = ℂ` if `P ∈ U` and `0` otherwise. -/
abbrev modSkyscraper (X : Type) [TopologicalSpace X] (P : X) : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := ℂ) (fun _ _ => True) (fun a x => x = P → a = 0)

end Defs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The index of speciality** (Definition 16.10, Ch. 2 §16, F1:5764): `i(D) = dim H¹(X, 𝒪_D)`. -/
noncomputable def specialityIndex (D : Function.locallyFinsupp X ℤ) : ℕ := Module.finrank ℂ (H1 (modOD X D) ⊤)

/-- **Paragraph 16.2** (Ch. 2 §16, F1:5600). `(fg) = (f) + (g)`, `(1/f) = −(f)` and `(fω) = (f) + (ω)`. -/
theorem para16_2 {f g : X → ℂ} {D D' : Function.locallyFinsupp X ℤ} (hf : IsDivisorOf f D) (hg : IsDivisorOf g D') :
    IsDivisorOf (f * g) (D + D') ∧ IsDivisorOf (fun x => (f x)⁻¹) (-D) ∧
      ∀ {w : Form1 X} {E : Function.locallyFinsupp X ℤ}, IsDivisorOfForm w E → IsDivisorOfForm (w.smulFun f) (D + E) := by
  sorry

/-- **Paragraph 16.3** (Ch. 2 §16, F1:5622). On a compact Riemann surface, the divisor of a meromorphic function has
degree `0`: `deg (f) = 0`.
Near miss: `Lehto1987.para4_5_4_a` (the same fact for the project's finitely supported `Divisor` and a `(0,0)`-differential; it assumes `SecondCountableTopology`, so it does not literally cover this statement). -/
theorem para16_3 [CompactSpace X] {f : X → ℂ} {D : Function.locallyFinsupp X ℤ} (hf : IsDivisorOf f D) :
    divDeg D = 0 := by
  sorry

/-- **Paragraph 16.4** (Ch. 2 §16, F1:5636). If `D − D′ = (ψ)` is principal, multiplication by `ψ` is an isomorphism of
sheaves `𝒪_D ≅ 𝒪_{D′}`. -/
theorem para16_4 {D D' : Function.locallyFinsupp X ℤ} {ψ : X → ℂ} (hψ : IsDivisorOf ψ (D - D')) :
    ∃ e : modOD X D ≅ modOD X D', IsInducedBy e.hom (fun (a : X → ℂ) x => ψ x * a x) := by
  sorry

/-- **Theorem 16.5** (Ch. 2 §16, F1:5650). On a compact Riemann surface, `deg D < 0` implies `H⁰(X, 𝒪_D) = 0`.
Near miss: `Lehto1987.eq4_5_3` (`dim D = 0` if `deg D > 0`, for the project's `Divisor`; stated through `divDim`, not through the sheaf `𝒪_D`). -/
theorem thm16_5 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : divDeg D < 0) :
    Subsingleton (H0 (modOD X D)) := by
  sorry

/-- **Paragraph 16.6** (Ch. 2 §16, F1:5660). `H¹(X, ℂ_P) = 0`. -/
theorem para16_6 (P : X) : Subsingleton (H1 (modSkyscraper X P) ⊤) := by
  sorry

/-- **Paragraph 16.7** (Ch. 2 §16, F1:5672). For a point `P` and a divisor `D`, the sequence
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` is short exact, with `α` the inclusion and `β` the map taking `f` to the coefficient of
`z^{−D(P)−1}` in its Laurent expansion at `P` (in the preferred chart at `P`).
Modelling: the coefficient `c` is the residue `(2πi)⁻¹ ∮ f(z) z^{D(P)} dz` over small circles about the centre of the chart. -/
theorem para16_7 (P : X) (D : Function.locallyFinsupp X ℤ) :
    ∃ (α : modOD X D ⟶ modOD X (D + divSingle P 1))
      (β : modOD X (D + divSingle P 1) ⟶ modSkyscraper X P),
      IsInducedBy α (id : (X → ℂ) → (X → ℂ)) ∧ IsShortExactSeq _ _ _ α β ∧
      ∀ (Y : Opens X) (a : X → ℂ)
        (ha : a ∈ repSpan (R := ℂ) (fun (a : X → ℂ) x => MeromorphicAt (LiZhongQC.localExpr a x) (chartAt ℂ x x) ∧
          ((-((D + divSingle P 1) x) : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS a x) (Y : Set X))
        (_ : P ∈ Y) (c : ℂ),
        (∃ ε > 0, ∀ ρ ∈ Ioo 0 ε, (2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(chartAt ℂ P P, ρ), a ((chartAt ℂ P).symm z) * (z - chartAt ℂ P P) ^ (D P)) = c) →
        ∃ hc : c ∈ repSpan (R := ℂ) (fun (_ : ℂ) (_ : X) => True) (Y : Set X),
          (β.app (op Y) (Submodule.Quotient.mk ⟨a, ha⟩) : ↥((modSkyscraper X P).obj (op Y))) =
            Submodule.Quotient.mk ⟨c, hc⟩ := by
  sorry

/-- **Corollary 16.8** (Ch. 2 §16, F1:5702). If `D ≤ D′`, the homomorphism `H¹(X, 𝒪_D) → H¹(X, 𝒪_{D′})` induced by the
inclusion is surjective. -/
theorem cor16_8 [CompactSpace X] {D D' : Function.locallyFinsupp X ℤ} (h : D ≤ D')
    {α : modOD X D ⟶ modOD X D'} (hα : IsInducedBy α (id : (X → ℂ) → (X → ℂ)))
    {α₁ : H1 (modOD X D) ⊤ →ₗ[ℂ] H1 (modOD X D') ⊤} (h₁ : IsH1Induced _ _ α α₁) : Function.Surjective α₁ := by
  sorry

/-- **Theorem 16.9** (Riemann–Roch, Ch. 2 §16, F1:5710). Let `D` be a divisor on a compact Riemann surface `X` of genus
`g`. Then `H⁰(X, 𝒪_D)` and `H¹(X, 𝒪_D)` are finite dimensional and `dim H⁰(X, 𝒪_D) − dim H¹(X, 𝒪_D) = 1 − g + deg D`.
Near miss: `LiZhongQC.thm22_4_riemann_roch` (`ℓ(α) − ℓ(K − α) = deg α − g + 1` for the project's `Divisor`, with the topological genus `HasGenus` and a canonical divisor `K`; here the genus is `dim H¹(X, 𝒪)` and the speciality index replaces `ℓ(K − α)`). -/
theorem thm16_9 [CompactSpace X] (D : Function.locallyFinsupp X ℤ) :
    FiniteDimensional ℂ (H0 (modOD X D)) ∧ FiniteDimensional ℂ (H1 (modOD X D) ⊤) ∧
      (Module.finrank ℂ (H0 (modOD X D)) : ℤ) - (specialityIndex D : ℤ) = 1 - (genus X : ℤ) + divDeg D := by
  sorry

/-- **Theorem 16.11** (Ch. 2 §16, F1:5782). Let `X` be a compact Riemann surface of genus `g` and `a ∈ X`. Then there is a
non-constant meromorphic function with a pole of order at most `g + 1` at `a` and no other poles. -/
theorem thm16_11 [CompactSpace X] (a : X) :
    ∃ f : X → ℂ, LiZhongQC.IsMeromorphicRS f ∧ (¬ ∃ c : ℂ, ∀ᶠ x in Filter.codiscrete X, f x = c) ∧
      (∀ x, x ≠ a → 0 ≤ LiZhongQC.ordRS f x) ∧ (-((genus X : ℤ) + 1) : ℤ) ≤ LiZhongQC.ordRS f a := by
  sorry

/-- **Corollary 16.12** (Ch. 2 §16, F1:5792). A compact Riemann surface of genus `g` admits a holomorphic covering
`X → ℙ¹` with at most `g + 1` sheets. -/
theorem cor16_12 [CompactSpace X] :
    ∃ n : ℕ, n ≤ genus X + 1 ∧ ∃ f : X → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      IsHolomorphicCovering f n := by
  sorry

/-- **Corollary 16.13** (Ch. 2 §16, F1:5796). A compact Riemann surface of genus `0` is isomorphic to `ℙ¹`.
Near miss: `LiZhongQC.thm22_3_classification` (uniformization of simply connected surfaces, by the topological genus; not stated for `genus X = 0`). -/
theorem cor16_13 [CompactSpace X] (hg : genus X = 0) :
    ∃ f : X ≃ₜ References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.symm := by
  sorry

end Statements

end Forster1981
