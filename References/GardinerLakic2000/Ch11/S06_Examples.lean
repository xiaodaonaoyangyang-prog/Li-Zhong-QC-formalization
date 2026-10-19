import References.GardinerLakic2000.Ch11.S05_Uniqueness

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.6 Examples

Source `teichmuller.txt`, lines 8650–8718 (Chapter 11, §11.6).

* Definition 3 (geometric decay, l. 8696) — `DecaysGeometrically`
* The example surface `R`, `φ` with properties (a)–(d) (l. 8653–8693) — deferred: leader calibration C0.5
* Proposition 1 (l. 8698) — deferred: leader calibration C0.5

Not items: the construction of `R̂` (the unit square with its side identifications, l. 8666–8693) and the proof of
Proposition 1 (extremal length of the `A_k`-annuli, l. 8700–8717). Deferred (C0.5): stating Proposition 1 and the
example's properties (a)–(d) faithfully needs the surface `R̂` built as a quotient space with charts `(z − a_k)²`,
i.e. definitions with proof obligations, which the no-proof rule excludes; the example is used nowhere else in the
book. Modelling of Definition 3: sequences are indexed by `ℕ` (the book's `k ≥ 1`), the tail sums are `tsum`s of a
summable sequence.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

/-- **Definition 3** (§11.6, l. 8696). A sequence of positive numbers `ε_k` decays geometrically if there is a constant
`M` with `Σ_{j ≥ k} ε_j ≤ M ε_k` for all `k`. -/
def DecaysGeometrically (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ Summable ε ∧ ∃ M : ℝ, ∀ k, ∑' j, ε (j + k) ≤ M * ε k

end GardinerLakic2000
