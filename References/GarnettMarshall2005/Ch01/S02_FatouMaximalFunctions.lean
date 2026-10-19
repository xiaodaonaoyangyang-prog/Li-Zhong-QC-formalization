import References.GarnettMarshall2005.Ch01.S01_HalfPlaneAndDisc
import LiZhongQC.ClusterSets

/-!
# Garnett–Marshall, Chapter I §2: Fatou's theorem and maximal functions

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. I §2 (pp. 6–13;
`full.md` P1:474–726).

Conventions as in §1: `∂𝔻` is `Metric.sphere 0 1`, `|E|` is `arcMeasure E` (Lebesgue measure `dθ` on `∂𝔻`, total
mass `2π`), "almost every `ζ ∈ ∂𝔻`" is `arcMeasure`-almost every, `L¹(∂𝔻)` is `Integrable · arcMeasure`,
`‖f‖₁ = eLpNorm f 1 arcMeasure` and `‖f‖_∞ = eLpNorm f ⊤ arcMeasure`, all with respect to `dθ`. Maximal functions
take values in `[0, ∞]`, and the book's level sets `{ζ : Mf(ζ) > λ}` are compared in `[0, ∞]`. The level `λ` is
written `lam` (`λ` is a Lean keyword).

* Definition (the cone `Γ_α(ζ)`, `ζ ∈ ∂𝔻`, `α > 1`, §2) — exists: `LiZhongQC.stolzAngle` (the points z of the unit
  disc with |z − ζ| < α(1 − |z|); the disc condition is automatic for α ≥ 0, since |z| ≥ 1 makes the right side at
  most 0, so the set is the book's cone)
* Definition ((2.1), nontangential limit, §2) — `HasNontangentialLimit`
* Definition (nontangential maximal function `u*_α`, §2) — `ntMaximal`
* Definition (`|E|`, Lebesgue measure of `E ⊆ ∂𝔻`, §2, P1:501) — exists: `GarnettMarshall2005.arcMeasure` (defined
  in §1, where the measure dθ first occurs)
* Theorem 2.1 (Fatou's theorem, §2): (2.2) and (2.3) — `thm1_2_1_i`, `thm1_2_1_ii`
* Definition (solution of the Dirichlet problem for `f ∈ L¹(∂𝔻)`, §2, P1:515) — omitted: a second name for the
  Poisson integral of f; no statement depends on it
* Definition (Hardy–Littlewood maximal function `Mf`, §2) — `hlMaximal`
* Lemma 2.2 (§2) — `lemma1_2_2`
* Lemma 2.3 (§2) — `lemma1_2_3`
* Lemma 2.4 (§2) — `lemma1_2_4`
* Corollary 2.5 (§2) — `cor1_2_5`

Not stated (inventory U−): the cone `Γ_α(ζ)` is asymptotic to a sector of angle `2 sec⁻¹ α`, and the cones expand as `α`
increases (P1:482, used only in the proof of Theorem 2.1); a finite nontangential limit gives `u*_α(ζ) < ∞` (P1:499,
immediate); the remarks P1:515–525 (weak type 1-1, `u*_α < ∞` a.e., the approximate identity scheme); the function
`P*_z` and (2.4), (2.6), (2.7), which are steps of the proofs of Theorem 2.1 and Lemma 2.2; the display (2.8) at P1:642
announces Lemma 2.4 and is that lemma. P1:725 (for measurable `E ⊆ ∂𝔻`, `ω(z, E, 𝔻)` is the unique bounded harmonic
function on `𝔻` with nontangential limit `χ_E` almost everywhere): its existence half is Fatou's theorem for `f = χ_E`
(`thm1_2_1_i`; used so at P2:1201), its uniqueness half follows from Corollary 2.5 and is not cited later.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (unitDisc stolzAngle)
open InnerProductSpace (HarmonicOnNhd)

/-- **Definition** (nontangential limit, (2.1), Ch. I §2, P1:487–491). A function `u` on `𝔻` has nontangential
limit `A` at `ζ ∈ ∂𝔻` if `lim_{Γ_α(ζ)∋z→ζ} u(z) = A` for every `α > 1`.
Modelling: `ζ ∈ ∂𝔻` is part of the definition (the book defines the notion only at `ζ ∈ ∂𝔻`); the cone `Γ_α(ζ)` is
`LiZhongQC.stolzAngle ζ α`. Pommerenke's `HasAngularLimit` (Stolz angles `|arg(1 − ζ̄z)| < α`, values in `ℂ̂`)
describes the same notion only through a comparison of the two families of cones. -/
def HasNontangentialLimit {V : Type*} [TopologicalSpace V] (u : ℂ → V) (ζ : ℂ) (A : V) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧ ∀ α : ℝ, 1 < α → Tendsto u (𝓝[stolzAngle ζ α] ζ) (𝓝 A)

/-- **Definition** (nontangential maximal function, Ch. I §2, P1:493–497). With fixed `α > 1`, the nontangential
maximal function of `u` at `ζ` is `u*_α(ζ) = sup_{Γ_α(ζ)} |u(z)|`, with values in `[0, ∞]`. Junk: `0` for `α ≤ 1` at
`ζ ∈ ∂𝔻` (the cone is empty there); never used there. -/
def ntMaximal {V : Type*} [NormedAddCommGroup V] (α : ℝ) (u : ℂ → V) (ζ : ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ stolzAngle ζ α, ‖u z‖ₑ

/-- **Theorem 2.1** (Fatou's theorem, Ch. I §2), first part. Let `f(e^{iθ}) ∈ L¹(∂𝔻)` and let `u` be the Poisson
integral of `f`. Then at almost every `ζ = e^{iθ} ∈ ∂𝔻`, (2.2) `lim_{Γ_α(ζ)∋z→ζ} u(z) = f(ζ)` for all `α > 1`, that
is, `u` has nontangential limit `f(ζ)` at `ζ`.
Modelling: `f` is complex-valued (the proof reduces to real `f`). -/
theorem thm1_2_1_i {f : ℂ → ℂ} (hf : Integrable f arcMeasure) :
    ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit (poissonIntegral f) ζ (f ζ) := by
  sorry

/-- **Theorem 2.1** (Fatou's theorem, Ch. I §2), second part. Moreover, for each `α > 1`, (2.3)
`|{ζ ∈ ∂𝔻 : u*_α(ζ) > λ}| ≤ ((3 + 6α)/λ) ‖f‖₁`.
Modelling: `λ > 0` is added (meaning): `λ` is a positive level in the book; for a real `λ < 0` the left side is
`|∂𝔻| = 2π` while the right side is negative, and `λ = 0` divides by zero. The constant `3 + 6α` was checked against
the equation image. -/
theorem thm1_2_1_ii {f : ℂ → ℂ} (hf : Integrable f arcMeasure) {α : ℝ} (hα : 1 < α) {lam : ℝ} (hlam : 0 < lam) :
    arcMeasure {ζ ∈ sphere (0 : ℂ) 1 | ENNReal.ofReal lam < ntMaximal α (poissonIntegral f) ζ} ≤
      ENNReal.ofReal ((3 + 6 * α) / lam) * eLpNorm f 1 arcMeasure := by
  sorry

/-- **Definition** (Hardy–Littlewood maximal function, Ch. I §2, P1:559–565). For `f ∈ L¹(∂𝔻)`,
`Mf(ζ) = sup_{I∋ζ} (1/|I|) ∫_I |f| dθ`, the maximal average of `|f|` over subarcs `I ⊆ ∂𝔻` that contain `ζ`, with
values in `[0, ∞]`.
Modelling: the subarcs are the open arcs `openArc a b`, `a < b ≤ a + 2π` (as in the proofs of Lemmas 2.3 and 2.4);
`|I| = arcMeasure I = b − a > 0`; closed subarcs and the whole circle give the same supremum, since the average is
continuous in the endpoints and `∂𝔻` minus a point is `openArc a (a + 2π)`. -/
def hlMaximal {V : Type*} [NormedAddCommGroup V] (f : ℂ → V) (ζ : ℂ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : a < b ∧ b ≤ a + 2 * π) (_ : ζ ∈ openArc a b),
    (arcMeasure (openArc a b))⁻¹ * ∫⁻ w in openArc a b, ‖f w‖ₑ ∂arcMeasure

/-- **Lemma 2.2** (Ch. I §2). Let `u` be the Poisson integral of `f ∈ L¹(∂𝔻)` and let `α > 1`. Then (2.5)
`u*_α(ζ) ≤ (1 + 2α) Mf(ζ)`.
Modelling: at every `ζ ∈ ∂𝔻`, in `[0, ∞]`; the constant `1 + 2α` was checked against the equation image. -/
theorem lemma1_2_2 {f : ℂ → ℂ} (hf : Integrable f arcMeasure) {α : ℝ} (hα : 1 < α) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, ntMaximal α (poissonIntegral f) ζ ≤ ENNReal.ofReal (1 + 2 * α) * hlMaximal f ζ := by
  sorry

/-- **Lemma 2.3** (Ch. I §2). Let `μ` be a positive Borel measure on `∂𝔻` and let `{I_j}` be a finite sequence of
open intervals in `∂𝔻`. Then `{I_j}` contains a pairwise disjoint subfamily `{J_k}` such that (2.9)
`Σ μ(J_k) ≥ (1/3) μ(⋃ I_j)`.
Modelling: `μ` is a Borel measure on `ℂ`, of which only the values on subsets of `∂𝔻` enter; the open intervals are
the open arcs `openArc a b`, `a < b ≤ a + 2π`, indexed by `Fin n`; the subfamily is indexed by `S ⊆ Fin n`; the
measures are compared in `[0, ∞]`; `μ` need not be finite (if some `μ(I_j) = ∞`, the single interval `I_j` is a
subfamily). -/
theorem lemma1_2_3 (μ : Measure ℂ) {n : ℕ} (I : Fin n → Set ℂ)
    (hI : ∀ j, ∃ a b : ℝ, a < b ∧ b ≤ a + 2 * π ∧ I j = openArc a b) :
    ∃ S : Finset (Fin n), (S : Set (Fin n)).PairwiseDisjoint I ∧
      (1 / 3 : ℝ≥0∞) * μ (⋃ j, I j) ≤ ∑ k ∈ S, μ (I k) := by
  sorry

/-- **Lemma 2.4** (Ch. I §2). The operator `f ↦ Mf` is weak-type 1-1: if `f ∈ L¹`, then (2.8)
`|{ζ ∈ ∂𝔻 : Mf(ζ) > λ}| ≤ 3‖f‖₁/λ`.
Modelling: `λ > 0` is added (meaning), as in (2.3): for a real `λ < 0` the left side is `2π` while the right side is
negative, and `λ = 0` divides by zero. [OCR] The lead-in is garbled in the source ("weak-type I·I: I f f ∈ L¹",
P1:687); the inequality (2.8) (displayed at P1:642 and P1:689) was checked against the equation image. -/
theorem lemma1_2_4 {f : ℂ → ℂ} (hf : Integrable f arcMeasure) {lam : ℝ} (hlam : 0 < lam) :
    arcMeasure {ζ ∈ sphere (0 : ℂ) 1 | ENNReal.ofReal lam < hlMaximal f ζ} ≤
      ENNReal.ofReal (3 / lam) * eLpNorm f 1 arcMeasure := by
  sorry

/-- **Corollary 2.5** (Ch. I §2). If `u` is a bounded harmonic function on `𝔻`, then for every `α > 0` and for almost
every `ζ = e^{iθ} ∈ ∂𝔻`, `f(ζ) = lim_{Γ_α(ζ)∋z→ζ} u(z)` exists, `u(z)` is the Poisson integral of `f`, and
`‖f‖_∞ = sup_{z∈𝔻} |u(z)|`.
Modelling: `α > 0` is kept literally (leader ruling Q9): `Γ_α(ζ) = ∅` for `α ≤ 1`, where a limit along the trivial
filter holds trivially, so this is equivalent to `α > 1`. The quantifiers are in the book's order (`∀ α`, then almost
every `ζ`); since the cones increase with `α`, this is equivalent to the order of Theorem 2.1. `u` is complex-valued
(Ch. II applies the corollary to a bounded analytic function, P1:2284). `f ∈ L^∞(∂𝔻)` is made explicit (the proof
takes `f ∈ L^∞`, and "the Poisson integral of `f`" presupposes integrability). -/
theorem cor1_2_5 {u : ℂ → ℂ} (hu : HarmonicOnNhd u unitDisc) (hub : ∃ M : ℝ, ∀ z ∈ unitDisc, ‖u z‖ ≤ M) :
    ∃ f : ℂ → ℂ, MemLp f ⊤ arcMeasure ∧
      (∀ α : ℝ, 0 < α → ∀ᵐ ζ ∂arcMeasure, Tendsto u (𝓝[stolzAngle ζ α] ζ) (𝓝 (f ζ))) ∧
      (∀ z ∈ unitDisc, u z = poissonIntegral f z) ∧
      eLpNorm f ⊤ arcMeasure = ⨆ z ∈ unitDisc, ‖u z‖ₑ := by
  sorry

end GarnettMarshall2005
