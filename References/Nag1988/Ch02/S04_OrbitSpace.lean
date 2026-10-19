import References.Nag1988.Ch02.S01_TeichmullerSpaceAndReducedSpace
import References.GardinerLakic2000.Ch10.S01_MCGForCoveringGroup

/-!
# Nag, Chapter 2 §2.4: Teichmüller space as the orbit space `M(X)/Q₀(X)`

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.4 (`full.md` N1:3861–3914; folder
`The Complex Analytic Theory … 10dae1e9`, cited `N1:<line>`). New: Proposition 2.4.1; Proposition 2.4.2 is passed.

**Model** (group version, see `Ch02/S01`). The action of a quasiconformal self-map `φ` of `X` on `M(X)` by pull-back
(`ν = φ^*μ`, (4.1), the dilatation of `w_μ ∘ φ̃`) is, for the lift `h` of `φ` to `ℍ`, the relation `IsPullback μ h ν` below: `ν` is
(almost everywhere on `ℍ`) the complex dilatation of `w^μ ∘ h`. The groups: `Q(X)` is `GardinerLakic2000.qcNormalizer Γ` (lifts of
quasiconformal self-maps of `X`), `Q₀(X)` is `GardinerLakic2000.qcNormalizer0 Γ` (the lifts fixing every real point, N1:3330:
homotopic to the identity relative to the boundary), and `Q₀^#(X)` is `qcNormalizerSharp Γ` (lifts commuting with every element of
`Γ` on `ℝ̂`, through the boundary maps `GardinerLakic2000.qcBdry`: homotopic to the identity, by Nielsen's theorem for
torsion-free `Γ`). The orbit spaces `L^∞_{(-1,1)}(X)_1/Q_0(X)`,
`/Q_0^#(X)`, `/Q(X)` are described by the equivalence relations of `Ch02/S01`.

* Proposition 2.4.1 (`T(X)`, `T^#(X)`, `R(X)` are the orbit spaces `M(X)/Q₀(X)`, `M(X)/Q₀^#(X)`, `M(X)/Q(X)`; the quotient metric of
  `τ̂` is `τ`; N1:3875) — `prop2_4_1_teich`, `prop2_4_1_reduced`, `prop2_4_1_riemann`, `prop2_4_1_dist`
* Proposition 2.4.2 (fibres of `Φ`: the boundary values coincide; N1:3891) — exists: `LiZhongQC.lemma33_1`, `Lehto1987.thm5_3_1`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (TeichGamma teichSetoidGamma teichDistanceGamma fMuSym h36p_m IsFuchsian BeltramiGamma upperHalf
  complexDilatation)
open GardinerLakic2000 (qcNormalizer qcNormalizer0)

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **`Q₀^#(X)`** (§2.4.1; N1:3881): the lifts to `ℍ` of the quasiconformal self-maps of `X` that are homotopic to the identity (not
necessarily rel boundary): the elements of `QC(Γ)` whose boundary map (`GardinerLakic2000.qcBdry`, in `ℂ̂`) commutes
with every element of `Γ` on the real line. -/
def qcNormalizerSharp (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {h | h ∈ qcNormalizer Γ ∧ ∀ γ ∈ Γ, ∀ x : ℝ,
    GardinerLakic2000.qcBdry h (LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) ((x : ℂ) : LiZhongQC.ExtPlane)) =
      LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) (GardinerLakic2000.qcBdry h ((x : ℂ) : LiZhongQC.ExtPlane))}

/-- **Pull-back** `ν = h^*μ` (§2.4.1, (4.1); N1:3848): `ν` is, almost everywhere on `ℍ`, the complex dilatation of `w^μ ∘ h`. -/
def IsPullback (μ : BeltramiGamma Γ) (h : ℂ → ℂ) (ν : BeltramiGamma Γ) : Prop :=
  ∀ᵐ z ∂(volume.restrict upperHalf), ν.1.1 z = complexDilatation (fMuSym μ.1.1 ∘ h) z

/-- **Proposition 2.4.1** (§2.4.1; N1:3875), `T(X)`: `[μ] = [ν]` iff `ν` is the pull-back of `μ` by some element of `Q₀`. -/
theorem prop2_4_1_teich (hΓ : IsFuchsian Γ) (μ ν : BeltramiGamma Γ) :
    (teichSetoidGamma Γ).r μ ν ↔ ∃ h ∈ qcNormalizer0 Γ, IsPullback μ h ν := by
  sorry

/-- **Proposition 2.4.1**, `T^#(X)`: `μ ∼_# ν` iff `ν` is the pull-back of `μ` by some element of `Q₀^#`. -/
theorem prop2_4_1_reduced (hΓ : IsFuchsian Γ) (μ ν : BeltramiGamma Γ) :
    (reducedSetoidGamma Γ).r μ ν ↔ ∃ h ∈ qcNormalizerSharp Γ, IsPullback μ h ν := by
  sorry

/-- **Proposition 2.4.1**, `R(X)`: `μ ∼_R ν` iff `ν` is the pull-back of `μ` by some element of `Q`. -/
theorem prop2_4_1_riemann (hΓ : IsFuchsian Γ) (μ ν : BeltramiGamma Γ) :
    riemannRel μ ν ↔ ∃ h ∈ qcNormalizer Γ, IsPullback μ h ν := by
  sorry

/-- **Proposition 2.4.1**, the metric: the quotient metric of `τ̂` through `M(X) → T(X)` is the Teichmüller metric `τ`. -/
theorem prop2_4_1_dist (hΓ : IsFuchsian Γ) (s t : TeichGamma Γ) :
    teichDistanceGamma s t = quotientDist betaDist (Quotient.mk (teichSetoidGamma Γ)) s t := by
  sorry

end Nag1988
