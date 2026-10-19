import References.GarnettMarshall2005.Ch06.S01_FMRieszTheorem
import References.Pommerenke1992.Ch06.S04_PlessnersTheoremAndTwisting

/-!
# Garnett–Marshall, Chapter VI §2: Privalov's theorem and Plessner's theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §2 (pp. 203–205;
`full.md` of the second part, P2:809–882).

Conventions of the section, as modelled here. `ζ ∈ ∂𝔻`, `α > 1`, `0 < h < 1`; the cone `Γ_α(ζ)` is
`LiZhongQC.stolzAngle ζ α` (Ch. I §2) and the truncated cone `Γ^h_α(ζ)` is `truncStolzCone ζ α h`. "Nontangential
limit" is `HasNontangentialLimit` of Ch. I §2 (a finite limit through every cone `Γ_α(ζ)`, `α > 1`). A harmonic
function on `𝔻` is `InnerProductSpace.HarmonicOnNhd u unitDisc` with complex values allowed (Part A; real-valued
harmonic functions are the case of real values). A meromorphic function on `𝔻` is Mathlib's `MeromorphicNFOn f
unitDisc` (leader ruling C5): at every point `f` is analytic or has a pole, where its value is `0`. With Mathlib's raw
`MeromorphicOn`, whose values at poles and removable points are arbitrary, Theorem 2.3 ("`f ≡ 0`") would be false (a
removable point with a wrong value). The value `0` at the poles is not seen by the statements: near a pole `|f|` is
large, so it affects neither bounds on cones nor finite nontangential limits, and adding the one value `0` to a set
that is not dense in `ℂ` cannot make it dense. `|E|` for `E ⊆ ∂𝔻` is `arcMeasure E`, the outer measure for sets that
need not be measurable, and "almost every `ζ ∈ E`" is "`∀ᵐ ζ ∂arcMeasure, ζ ∈ E → …`" (an outer-measure statement).

* Definition (truncated cone `Γ^h_α(ζ)`, §2, P2:811–818) — `truncStolzCone`
* Definition 2.1 (nontangentially bounded, §2) — `IsNontangentiallyBounded`
* Theorem 2.2 (Privalov, §2) — `thm6_2_2`
* Definition (cone domain, §2, P2:843–849) — `coneDomain`, `truncConeDomain`
* Theorem 2.3 (§2) — `thm6_2_3` (B-cand. Pommerenke1992.cor6_14, the Privalov uniqueness theorem for angular limits
  in every Stolz angle, a weaker statement)
* Definition 2.4 (Plessner point, §2; used in Theorem 2.5 and App. I, P3:4941, 5196) — exists:
  `Pommerenke1992.IsPlessnerPoint` (dense image of every Stolz angle at ζ, values through `LiZhongQC.meroToExt`,
  finite part dense; for a meromorphic f in normal form this is the book's notion: each truncated cone Γ^h_α(ζ)
  contains a Stolz angle at ζ and each Stolz angle contains some Γ^h_α(ζ), the two families being cofinal near ζ, and
  meroToExt f agrees with f off the poles, where the book's set gains only the value 0, which cannot make a non-dense
  set dense)
* Theorem 2.5 (Plessner, §2) — `thm6_2_5` (B-cand. Pommerenke1992.thm6_13, the almost-everywhere dichotomy without
  the Borel partition and without the non-zero limit)

Not stated (inventory U−): "the definition of nontangential boundedness only requires a single truncated cone,
whereas nontangential convergence requires every cone" (P2:828, a remark); "because `α` and `h` are fixed, `∂U_i` is a
rectifiable Jordan curve" (P2:838, Figure VI.2, a step of the proof of Theorem 2.2; later proofs reuse the
construction "as in the proof of Privalov's theorem" as a template, P2:859); the necessity of nontangential approach,
Bagemihl–Seidel's function with radial limit `0` almost everywhere (P2:861, Exercise 5).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (unitDisc stolzAngle)
open InnerProductSpace (HarmonicOnNhd)
open Pommerenke1992 (IsPlessnerPoint)

/-- **Definition** (truncated cone, Ch. VI §2, P2:811–818; used in Definitions 2.1, 2.4, in Chapter VII and in
Chapter X). Let `ζ ∈ ∂𝔻`, `α > 1` and `0 < h < 1`. The truncated cone is
`Γ^h_α(ζ) = {z : |z − ζ| < α(1 − |z|) < αh}`.
Modelling: the set is written literally and defined for all `ζ`, `α`, `h`; it is used for `ζ ∈ ∂𝔻`, `α > 1`,
`0 < h < 1`, where it lies in `𝔻` (`|z − ζ| ≥ 0` forces `|z| < 1`). The formula was checked against the equation
image. -/
def truncStolzCone (ζ : ℂ) (α h : ℝ) : Set ℂ :=
  {z | ‖z - ζ‖ < α * (1 - ‖z‖) ∧ α * (1 - ‖z‖) < α * h}

/-- **Definition 2.1** (nontangentially bounded, Ch. VI §2; used in Theorem 2.2, in the proof of Theorem 2.5 and in
Exercise VI.6). Let `u` be a harmonic or meromorphic function on `𝔻` and `ζ ∈ ∂𝔻`. The function `u` is
nontangentially bounded at `ζ` if there exist `M < ∞`, `α > 1` and `0 < h < 1` such that `|u(z)| ≤ M` on `Γ^h_α(ζ)`.
Modelling: `u : ℂ → ℂ` (the harmonic or meromorphic hypothesis is carried by the statements); `ζ ∈ ∂𝔻` is part of
the definition, as for `HasNontangentialLimit`; `M` is a real number. -/
def IsNontangentiallyBounded (u : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧
    ∃ M α h : ℝ, 1 < α ∧ 0 < h ∧ h < 1 ∧ ∀ z ∈ truncStolzCone ζ α h, ‖u z‖ ≤ M

/-- **Theorem 2.2** (Privalov, Ch. VI §2; cited "by Privalov's theorem" at P2:881, in Exercise VI.5, P2:1670, and in
Chapter X, P2:7552). Suppose `E ⊆ ∂𝔻` and suppose `u(z)` is nontangentially bounded at each `ζ ∈ E`. Then `u(z)` has
a nontangential limit at almost every `ζ ∈ E`.
Modelling: `u` is harmonic or meromorphic on `𝔻` (module docstring); `E` is any subset of `∂𝔻` (the conclusion is
an outer-measure statement); the limit is finite (`A ∈ ℂ`), as the proof gives ("a finite nontangential limit"). -/
theorem thm6_2_2 {u : ℂ → ℂ} (hu : HarmonicOnNhd u unitDisc ∨ MeromorphicNFOn u unitDisc) {E : Set ℂ}
    (hE : E ⊆ sphere (0 : ℂ) 1) (hb : ∀ ζ ∈ E, IsNontangentiallyBounded u ζ) :
    ∀ᵐ ζ ∂arcMeasure, ζ ∈ E → ∃ A : ℂ, HasNontangentialLimit u ζ A := by
  sorry

/-- **Definition** (cone domain, Ch. VI §2, P2:843–849; used in the proofs of §2–§6, in Chapter VII, P2:3016, 3024, in
Chapter X, P2:7201–7288, P3:680, 694, 1268, 1502, and in App. M). A cone domain is a domain of the form
`U = ⋃_{ζ∈K} Γ_α(ζ)` or `U = ⋃_{ζ∈K} Γ^h_α(ζ)`, where `K ⊆ ∂𝔻` is compact, `α > 1` and `0 < h < 1`.
Modelling: the first form is `coneDomain K α`, the second `truncConeDomain K α h`; both are defined for all `K`, `α`,
`h`, and the conditions (`K ⊆ ∂𝔻` compact, `α > 1`, `0 < h < 1`, and that the union is a domain) are hypotheses of
the statements that use them. -/
def coneDomain (K : Set ℂ) (α : ℝ) : Set ℂ :=
  ⋃ ζ ∈ K, stolzAngle ζ α

/-- **Definition** (truncated cone domain, the second form of a cone domain, Ch. VI §2, P2:843–849; see
`coneDomain`). `U = ⋃_{ζ∈K} Γ^h_α(ζ)`. -/
def truncConeDomain (K : Set ℂ) (α h : ℝ) : Set ℂ :=
  ⋃ ζ ∈ K, truncStolzCone ζ α h

/-- **Theorem 2.3** (Ch. VI §2; cited at P2:881, 903, 965, 1220 and in Chapter X, P3:1290, "Theorem VI.2.3"). Let
`f(z)` be a meromorphic function on `𝔻` and let `E ⊆ ∂𝔻` have `|E| > 0`. If for each `ζ ∈ E` there is
`α = α(ζ) > 1` such that `lim_{Γ_α(ζ) ∋ z → ζ} f(z) = 0`, then `f(z) ≡ 0` in `𝔻`.
Modelling: `MeromorphicNFOn f unitDisc` (module docstring; with the raw `MeromorphicOn` the conclusion would be false);
`|E| > 0` is the outer measure `arcMeasure E > 0` (the set of `ζ ∈ ∂𝔻` at which `f` tends to `0` in some cone is a
Borel set, so a measurable `E` could be taken); the limit is along `𝓝[Γ_α(ζ)] ζ` for the one cone `α(ζ)`. -/
theorem thm6_2_3 {f : ℂ → ℂ} (hf : MeromorphicNFOn f unitDisc) {E : Set ℂ} (hE : E ⊆ sphere (0 : ℂ) 1)
    (hEpos : 0 < arcMeasure E) (hlim : ∀ ζ ∈ E, ∃ α : ℝ, 1 < α ∧ Tendsto f (𝓝[stolzAngle ζ α] ζ) (𝓝 0)) :
    ∀ z ∈ unitDisc, f z = 0 := by
  sorry

/-- **Theorem 2.5** (Plessner, Ch. VI §2; cited at P2:965, in Chapter X, P2:7566, P3:1474, and in App. I, P3:4941).
Let `f(z)` be a nonconstant meromorphic function on `𝔻`. Then there are pairwise disjoint Borel subsets `N`, `G` and
`P` of `∂𝔻` such that `∂𝔻 = N ∪ G ∪ P` and (a) `|N| = 0`, (b) at each `ζ ∈ G`, `f` has a finite nontangential limit
`f(ζ)` and `f(ζ) ≠ 0`, and (c) each `ζ ∈ P` is a Plessner point for `f`.
Modelling: `MeromorphicNFOn f unitDisc`; "nonconstant" is `f(z) ≠ f(w)` for some `z, w ∈ 𝔻` (for a meromorphic
function in normal form that is constant near one point of the connected `𝔻` is constant on `𝔻`); Borel is
`MeasurableSet` in `ℂ`; "`f(ζ) ≠ 0`" is part of (b) as printed (the proof applies Theorem 2.3 to `f` and to `1/f`). -/
theorem thm6_2_5 {f : ℂ → ℂ} (hf : MeromorphicNFOn f unitDisc) (hnc : ∃ z ∈ unitDisc, ∃ w ∈ unitDisc, f z ≠ f w) :
    ∃ N G P : Set ℂ, MeasurableSet N ∧ MeasurableSet G ∧ MeasurableSet P ∧ Disjoint N G ∧ Disjoint N P ∧
      Disjoint G P ∧ N ∪ G ∪ P = sphere (0 : ℂ) 1 ∧ arcMeasure N = 0 ∧
      (∀ ζ ∈ G, ∃ A : ℂ, A ≠ 0 ∧ HasNontangentialLimit f ζ A) ∧ ∀ ζ ∈ P, IsPlessnerPoint f ζ := by
  sorry

end GarnettMarshall2005
