import References.Common.HyperbolicSurface
import References.Forster1981.Ch01.S02_ElementaryPropertiesOfHolomorphicMappings
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Hubbard 2006, Appendix A3: The Riemann–Hurwitz formula

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 5281–5398.

**Conventions.** Riemann surfaces as in `Ch01/S01_TwoStatements` (all in `Type`). The local degree `deg_y f` of a
non-constant holomorphic map at `y` is `Forster1981.multiplicity f y` (so `deg_y f − 1` is the branching order of
Forster B0.7); a map `f : Y → X` is *proper of degree `d`* if it is a proper map and the multiplicities over every point
add up to `d`. The Euler characteristic of a topological space is `eulerCharTop`, from Mathlib's singular homology with
real coefficients. **Misprint in the book:** the sum (A3.5) defining the Euler characteristic of a space starts at `i =
1`; formula (A3.4) and the rest of the text need `i = 0`; the correct sum `∑_{i ≥ 0} (−1)^i dim H_i(X; ℝ)` is used.

* Definition A3.1 (Euler characteristic of a finite simplicial complex) — `simplicialEulerChar`
* Exercise A3.2 — omitted: exercise
* Definition A3.3 (Euler characteristic of a topological space) — `eulerCharTop`
* Theorem A3.4 (Riemann–Hurwitz formula) — `thmA3_4`
* Lemma A3.5 (a connected surface has a finite maximal multicurve iff `H₁(X; ℝ)` is finite dimensional) — `lemmaA3_5`
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

/-- **Euler characteristic of a finite abstract simplicial complex** (Def. A3.1): `χ(Σ) = ∑ (−1)^i #Σ_i`, `Σ_i` the set
of simplices with `i + 1` vertices (the dimension-`i` simplices). A simplicial complex is a finite set `Σ` of non-empty
finite subsets of the vertex set, closed under non-empty subsets (the closure property is a hypothesis of the uses, not
of the definition). -/
def simplicialEulerChar {V : Type*} (K : Finset (Finset V)) : ℤ :=
  ∑ i ∈ Finset.range (K.sup Finset.card), (-1) ^ i * ((K.filter (fun σ => σ.card = i + 1)).card : ℤ)

/-- The singular homology `H_i(X; ℝ)` of a topological space (a real vector space). -/
abbrev singularHomologyR (i : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℝ) i).obj (ModuleCat.of ℝ ℝ)).obj (TopCat.of X)

/-- **Euler characteristic of a topological space** (Def. A3.3): `χ(X) = ∑_{i ≥ 0} (−1)^i dim_ℝ H_i(X; ℝ)`. *Junk:* the
sum is a `finsum` (`0` when infinitely many terms are non-zero) and `Module.finrank` is `0` for infinite dimensional
spaces; every use assumes that all `H_i` are finite dimensional and that `H_i = 0` for large `i`. -/
noncomputable def eulerCharTop (X : Type) [TopologicalSpace X] : ℤ :=
  ∑ᶠ i : ℕ, (-1) ^ i * (Module.finrank ℝ (singularHomologyR i X) : ℤ)

/-- **Theorem A3.4** (Riemann–Hurwitz, Appendix A3, H2:5298). Let `X`, `Y` be connected Riemann surfaces, `X` with
finite dimensional homology (`H_i(X; ℝ)` finite dimensional, zero for large `i`) and `f : Y → X` a proper non-constant
analytic map of degree `d` (the multiplicities over every point of `X` add up to `d`) with finitely many critical
values. Then `f` has finitely many critical points, `Y` has finite dimensional homology, and `χ(Y) = d χ(X) − ∑_{y ∈ Y}
(deg_y f − 1)`. Near miss: `Forster1981.thm17_14` (compact case, in `ℚ`); this is the non-compact generalization used
with finite type. -/
theorem thmA3_4 {X Y : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (hXfin : ∀ i, Module.Finite ℝ (singularHomologyR i X)) (hXvan : ∃ N, ∀ i > N, Subsingleton (singularHomologyR i X))
    (f : Y → X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c, ∀ y, f y = c) (hproper : IsProperMap f) (d : ℕ)
    (hd : ∀ x : X, ∑ᶠ y ∈ f ⁻¹' {x}, (Forster1981.multiplicity f y).toNat = d)
    (hcv : {x : X | ∃ y ∈ f ⁻¹' {x}, 2 ≤ Forster1981.multiplicity f y}.Finite) :
    {y : Y | 2 ≤ Forster1981.multiplicity f y}.Finite ∧ (∀ i, Module.Finite ℝ (singularHomologyR i Y)) ∧
      (∃ N, ∀ i > N, Subsingleton (singularHomologyR i Y)) ∧
      eulerCharTop Y = d * eulerCharTop X - ∑ᶠ y : Y, (((Forster1981.multiplicity f y).toNat : ℤ) - 1) := by
  sorry

/-- **Lemma A3.5** (Appendix A3, H2:5287). A connected Riemann surface `X` has a finite maximal multicurve iff `H₁(X;
ℝ)` is finite dimensional. (`References.IsMaximalMulticurve`, the shared notion: a multicurve maximal for inclusion;
loops around punctures are admitted.) -/
theorem lemmaA3_5 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (∃ Y : Set (Set X), Y.Finite ∧ References.IsMaximalMulticurve Y) ↔ Module.Finite ℝ (singularHomologyR 1 X) := by
  sorry

end Hubbard2006
