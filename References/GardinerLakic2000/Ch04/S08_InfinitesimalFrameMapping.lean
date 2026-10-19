import References.GardinerLakic2000.Ch04.S07_FrameMappingTheorem
import References.GardinerLakic2000.Ch03.S03_PredualSpace

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.8 Infinitesimal frame mapping

Source `teichmuller.txt`, lines 4192–4296.

* Definition (`b*(μ)` and `b(V)`, recalled from §3.3, l. 4193–4199) — exists:
  `GardinerLakic2000.boundaryDilatationStar` `GardinerLakic2000.infBoundaryDilatation`
* Definition 2 (Reich–Strebel functional, l. 4201) — `IsReichStrebelFunctional`
* Theorem 7 (the infinitesimal frame mapping theorem, l. 4203) — `thm4_7`
* Definition (degenerating Hamilton sequence of a functional `V`, l. 4263) — `HasDegHamiltonSeqV`
* Theorem 8 (l. 4263) — `thm4_8`

Not items (DESIGN §3): extremal sequences and extremal differentials of `V` (l. 4211, used in the proof only).

**Conventions.** `Z = Z(R)` is Part A's `zSpace R`, `‖V‖` its dual norm on `A(R)`; "`μ` represents `V`" is
`V(φ) = (φ, μ)` (`pairingRS`) for `φ ∈ A(R)`. The Hamilton sequences of a functional (Theorem 8) are read from the
proof (l. 4265, 4291): `‖φₙ‖ = 1`, `φₙ` degenerating, `|V(φₙ)| → ‖V‖` [reading].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- The dual norm `‖V‖` of `V ∈ Z(R)` (Part A's `dualNormOn` on `A(R)`). -/
def zNorm (V : (R → ℂ → ℂ) → ℂ) : ℝ := dualNormOn (integrableHolQDSet R) quadDiffNorm V

/-- **Definition 2** (Reich–Strebel functional, §4.8, l. 4201). `V ∈ Z` with `b(V) < ‖V‖`. -/
def IsReichStrebelFunctional (V : (R → ℂ → ℂ) → ℂ) : Prop :=
  V ∈ zSpace R ∧ infBoundaryDilatation V < ENNReal.ofReal (zNorm V)

/-- **Theorem 7** (the infinitesimal frame mapping theorem, §4.8, l. 4203). If `V` is a Reich–Strebel functional,
there is a unique `φ ∈ A(R)` of norm one such that `‖V‖ |φ|/φ` represents `V`. -/
theorem thm4_7 {V : (R → ℂ → ℂ) → ℂ} (hV : IsReichStrebelFunctional V) :
    ∃! φ : R → ℂ → ℂ, φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1 ∧
      ∀ ψ ∈ integrableHolQDSet R, V ψ = pairingRS ψ fun x z => zNorm V * (conj (φ x z) / ‖φ x z‖) := by
  sorry

/-- **Definition** (§4.8, l. 4263, 4265–4295). `V` has a degenerating Hamilton sequence: a degenerating sequence
`φₙ` in `A(R)` with `|V(φₙ)| → ‖V‖`. -/
def HasDegHamiltonSeqV (V : (R → ℂ → ℂ) → ℂ) : Prop :=
  ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ ∧ Tendsto (fun n => ‖V (φ n)‖) atTop (𝓝 (zNorm V))

/-- **[CORRECTION]** (AUDIT4 G6) `0 < ‖V‖` is added: for `V = 0` on a surface with `dim A(R) < ∞` the functional is not Reich–Strebel
(`0 < 0` fails) and no degenerating sequence exists, so the two sides differ.
**Theorem 8** (§4.8, l. 4263). `V ∈ Z` is not a Reich–Strebel functional if and only if `V` has a degenerating
Hamilton sequence. -/
theorem thm4_8 {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) (hV0 : 0 < zNorm V) :
    ¬ IsReichStrebelFunctional V ↔ HasDegHamiltonSeqV V := by
  sorry

end GardinerLakic2000
