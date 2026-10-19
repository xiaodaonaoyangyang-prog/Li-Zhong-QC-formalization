import References.GardinerLakic2000.Ch18.S04_LinearTheory

/-!
# Gardiner–Lakic 2000, Ch. 18 §18.5 Infinitesimal earthquakes

Source `teichmuller.txt`, lines 13551–13643 (Chapter 18, §18.5).

* Definition (the finite infinitesimal earthquake measure `σ_S` of `V` on a finite `S ∪ {∞}`: nonnegative, atomic,
  unlinked, no line joining adjacent points, `E(σ_S) = V` on `S` modulo quadratic polynomials, (18.11),
  l. 13554–13576) — `IsInfEarthquakeMeasure`
* Lemma 9 (l. 13576) — `lemma18_9`
* Lemma 10 (l. 13581) — `lemma18_10`
* Definition (support of a measure; unlinked lines of support; vague convergence of the atomic measures, l. 13589,
  13593) — `IsInSupport`, `HasUnlinkedSupport`, `atomicMeasure`, `ConvergesVaguelyLines`
* Lemma 11 (l. 13593) — `lemma18_11`
* Lemma 12 (l. 13599) — `lemma18_12`
* Theorem 5 (l. 13612) — `thm18_5`

Not items: the linear and quadratic procedures, lower lines and parabolas, `hull(V, S)` (l. 13554–13580, the
construction of `σ_S`, characterized by Lemma 9); the Remark (Zygmund–Jackson, l. 13616); the exercises. Modelling: as
§18.4. `S` is a finite subset of `ℝ` and `∞` is the extra special point of the book (after `V` is normalized to grow
at most like `|x| log|x|`); an atomic measure on the lines with ends in `S ∪ {∞}` is a pair of weight functions, `w`
on the pairs `(a, b)`, `a < b`, and `w∞` on the lines `{a, ∞}`; `a, b` (resp. `a, ∞`) are adjacent when no point of
`S` lies between them (resp. `a` is the least or largest point of `S`). Lemma 10's bound is on the atomic norm (the
sums of the weights of the lines joining `[a, b]` to `[c, d]` for the quadruples of E0.8). "Weak limit" in Lemmas
11–12 is vague convergence against continuous compactly supported functions on `{a < b}` (and on `ℝ` for the lines to
`∞`) along a subsequence. The uniqueness in Theorem 5 is quoted from [Gar95] in the book. [CORRECTION] (AUDIT5_GL1518
G15-6) As in §18.4, the measures of Theorem 5 are pairs `(σ⁺, σ⁻)` of measures (nonnegative: `σ⁻ = 0`), not finite
`SignedMeasure`s (the measure `σ_V` of the periodic bumps `Σ_{a ∈ ℤ} E_{a,a+1}` has infinite mass), and the integrals of
Lemma 12 use the kernels normalized at `0`, `1` (they diverge otherwise for nested lines at all scales).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (extRealLine)

/-- **Definition** (`σ_S`, §18.5, l. 13554–13576, (18.11)). The weights `w` on the lines `(a, b)` and `w∞` on the lines
`{a, ∞}` with ends in `S ∪ {∞}` are nonnegative, unlinked, never join adjacent points, and
`Σ w(a, b) E_ab(x) + Σ w∞(a) (x − a)⁺ = V(x)` on `S` modulo an affine polynomial.
[CORRECTION] (AUDITR2_GL1518 G2, confirmed in AUDIT5_GL1518) The equation is modulo affine polynomials, not quadratic
ones. The book's data include the point `∞`: `V` is normalized at `∞` (it grows at most like
`|x| log|x|`). Modulo quadratics, the line `(min S, max S)` carries a free weight, because `E_{min S, max S}` is quadratic on
`S` (`S = {0, 1, 2}`, `V = 0`: both `w = 0` and `w = δ_{(0,2)}` qualified). Lemmas 10–12 apply it to the normalized
field `zNormalize V`. -/
def IsInfEarthquakeMeasure (S : Finset ℝ) (V : ℝ → ℝ) (w : ℝ × ℝ → ℝ) (winf : ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ w p) ∧ (∀ a, 0 ≤ winf a) ∧ (∀ p, w p ≠ 0 → p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2) ∧
    (∀ a, winf a ≠ 0 → a ∈ S) ∧
    (∀ p q, w p ≠ 0 → w q ≠ 0 → ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)) ∧
    (∀ p a, w p ≠ 0 → winf a ≠ 0 → ¬ (p.1 < a ∧ a < p.2)) ∧
    (∀ p, w p ≠ 0 → ∃ s ∈ S, p.1 < s ∧ s < p.2) ∧
    (∀ a, winf a ≠ 0 → (∃ s ∈ S, s < a) ∧ ∃ s ∈ S, a < s) ∧
    ∃ β γ : ℝ, ∀ x ∈ S, (∑ p ∈ S ×ˢ S, w p * earthquakeVF p.1 p.2 x) + (∑ a ∈ S, winf a * max (x - a) 0) =
      V x + β * x + γ

/-- **Lemma 9** (§18.5, l. 13576). The measure `σ_S` constructed from `V` on `S` is nonnegative, has unlinked lines of
support, no line joining adjacent points, and `E(σ_S) = V` on `S` modulo an affine polynomial (the normalization at `∞`,
[CORRECTION] AUDITR2_GL1518 G2); it is the only such atomic measure. -/
theorem lemma18_9 {S : Finset ℝ} (hS : 3 ≤ S.card) (V : ℝ → ℝ) :
    (∃ (w : ℝ × ℝ → ℝ) (winf : ℝ → ℝ), IsInfEarthquakeMeasure S V w winf) ∧
    ∀ (w w' : ℝ × ℝ → ℝ) (winf winf' : ℝ → ℝ), IsInfEarthquakeMeasure S V w winf →
      IsInfEarthquakeMeasure S V w' winf' → w = w' ∧ winf = winf' := by
  sorry

/-- **Lemma 10** (§18.5, l. 13581). For `V` in `𝒵`, the measures `σ_S` have norm bounded independently of `S`. -/
theorem lemma18_10 {V : ℂ → ℂ} (hVr : ∀ x : ℝ, (V x).im = 0) (hV : V ∈ zCrSet extRealLine) :
    ∃ C : ℝ, ∀ (S : Finset ℝ) (w : ℝ × ℝ → ℝ) (winf : ℝ → ℝ),
      IsInfEarthquakeMeasure S (fun x => (zNormalize V x).re) w winf →
      (∀ a b c d : ℝ, a < b → b < c → c < d → (d - c) * (b - a) / ((c - b) * (d - a)) = 1 / 8 →
        ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ∈ Icc a b ∧ p.2 ∈ Icc c d), w p ≤ C) ∧
      ∀ a b c : ℝ, a < b → b < c → (b - a) / (c - b) = 1 / 8 →
        (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ∈ Icc a b ∧ c ≤ p.2), w p) +
          ∑ x ∈ S.filter (fun x => x ∈ Icc a b), winf x ≤ C := by
  sorry

/-- Helper (§18.5). `p` lies in the support of `μ`: every neighbourhood of `p` has positive measure. -/
def IsInSupport {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) (p : X) : Prop :=
  ∀ U ∈ 𝓝 p, 0 < μ U

/-- Helper (§18.5, l. 13593). The lines of support of `(σ, σ∞)` do not intersect. -/
def HasUnlinkedSupport (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ) : Prop :=
  (∀ p q : ℝ × ℝ, IsInSupport (σ.1 + σ.2) p → IsInSupport (σ.1 + σ.2) q →
    ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)) ∧
  ∀ (p : ℝ × ℝ) (a : ℝ), IsInSupport (σ.1 + σ.2) p → IsInSupport (σinf.1 + σinf.2) a → ¬ (p.1 < a ∧ a < p.2)

/-- Helper (§18.5). The atomic measure `Σ w(p) δ_p` of a finitely supported weight function. -/
def atomicMeasure {X : Type*} [MeasurableSpace X] (T : Finset X) (w : X → ℝ) : Measure X :=
  ∑ p ∈ T, ENNReal.ofReal (w p) • Measure.dirac p

/-- Helper (§18.5, l. 13589). Along the subsequence `φ`, the atomic measures of `σ_{S_n}` converge vaguely to `(σ, σ∞)`
(against continuous functions with compact support in `{a < b}`, resp. `ℝ`). -/
def ConvergesVaguelyLines (S : ℕ → Finset ℝ) (w : ℕ → ℝ × ℝ → ℝ) (winf : ℕ → ℝ → ℝ) (φ : ℕ → ℕ)
    (σ : Measure (ℝ × ℝ)) (σinf : Measure ℝ) : Prop :=
  StrictMono φ ∧
  (∀ f : ℝ × ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ {p | p.1 < p.2} →
    Tendsto (fun n => ∫ p, f p ∂atomicMeasure (S (φ n) ×ˢ S (φ n)) (w (φ n))) atTop (𝓝 (∫ p, f p ∂σ))) ∧
  ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun n => ∫ a, f a ∂atomicMeasure (S (φ n)) (winf (φ n))) atTop (𝓝 (∫ a, f a ∂σinf))

/-- **Lemma 11** (§18.5, l. 13593). Any weak limit `σ` of the measures `σₙ` is nonnegative, has bounded norm and
non-intersecting lines of support. -/
theorem lemma18_11 {V : ℂ → ℂ} (hVr : ∀ x : ℝ, (V x).im = 0) (hV : V ∈ zCrSet extRealLine) {S : ℕ → Finset ℝ}
    (hS : Monotone S) {w : ℕ → ℝ × ℝ → ℝ} {winf : ℕ → ℝ → ℝ}
    (hw : ∀ n, IsInfEarthquakeMeasure (S n) (fun x => (zNormalize V x).re) (w n) (winf n)) {φ : ℕ → ℕ}
    {σ : Measure (ℝ × ℝ)} {σinf : Measure ℝ} [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts σinf]
    (hconv : ConvergesVaguelyLines S w winf φ σ σinf) :
    (⨆ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (_ : a < b ∧ b < c ∧ c < d ∧ (d - c) * (b - a) / ((c - b) * (d - a)) = 1 / 8),
      σ (Icc a b ×ˢ Icc c d)) < ⊤ ∧
    (∀ p q : ℝ × ℝ, IsInSupport σ p → IsInSupport σ q → ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)) ∧
    ∀ (p : ℝ × ℝ) (a : ℝ), IsInSupport σ p → IsInSupport σinf a → ¬ (p.1 < a ∧ a < p.2) := by
  sorry

/-- **Lemma 12** (§18.5, l. 13599). Let `V ∈ 𝒵`, `S₁ ⊆ S₂ ⊆ ⋯` finite with dense union, `σₙ` the measures of Lemma 9
for `V` on `Sₙ`, and `σ` a weak limit. Then `W(x) = ∬ E_ab(x) dσ(a, b)` and `V(x)` differ by a quadratic polynomial. -/
theorem lemma18_12 {V : ℂ → ℂ} (hVr : ∀ x : ℝ, (V x).im = 0) (hV : V ∈ zCrSet extRealLine) {S : ℕ → Finset ℝ}
    (hS : Monotone S) (hdense : Dense (⋃ n, (↑(S n) : Set ℝ))) {w : ℕ → ℝ × ℝ → ℝ} {winf : ℕ → ℝ → ℝ}
    (hw : ∀ n, IsInfEarthquakeMeasure (S n) (fun x => (zNormalize V x).re) (w n) (winf n)) {φ : ℕ → ℕ}
    {σ : Measure (ℝ × ℝ)} {σinf : Measure ℝ} [IsFiniteMeasureOnCompacts σ] [IsFiniteMeasureOnCompacts σinf]
    (hconv : ConvergesVaguelyLines S w winf φ σ σinf) :
    ∃ a b c : ℝ, ∀ x : ℝ,
      (∫ p, (earthquakeVF p.1 p.2 x - earthquakeVF p.1 p.2 0 * (1 - x) - earthquakeVF p.1 p.2 1 * x) ∂σ) +
        (∫ y, (max (x - y) 0 - max (-y) 0 * (1 - x) - max (1 - y) 0 * x) ∂σinf) =
      (V x).re + a * x ^ 2 + b * x + c := by
  sorry

/-- **Theorem 5** (§18.5, l. 13612). `B` and `E` are bounded linear surjections of `𝓜` onto `𝒵` and `Θ` onto the
bounded cusp forms (Theorem 4). The measure `σ_V` of `V ∈ 𝒵` is nonnegative, has non-intersecting lines of support and
`E(σ_V) = V`; every nonnegative `σ` with non-intersecting lines of support and `E(σ) = V` equals `σ_V`. -/
theorem thm18_5 {V : ℂ → ℂ} (hVr : ∀ x : ℝ, (V x).im = 0) (hV : V ∈ zCrSet extRealLine) :
    (∃ (σ : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf : Measure ℝ × Measure ℝ),
      IsLineMeasure σ ∧ earthquakeMeasureNorm σ σinf < ⊤ ∧ σ.2 = 0 ∧ σinf.2 = 0 ∧ HasUnlinkedSupport σ σinf ∧
      ∃ a b c : ℝ, ∀ x : ℝ, earthquakeOp σ σinf x = (V x).re + a * x ^ 2 + b * x + c) ∧
    ∀ (σ σ' : Measure (ℝ × ℝ) × Measure (ℝ × ℝ)) (σinf σinf' : Measure ℝ × Measure ℝ),
      IsLineMeasure σ → earthquakeMeasureNorm σ σinf < ⊤ → σ.2 = 0 → σinf.2 = 0 →
      HasUnlinkedSupport σ σinf → (∃ a b c : ℝ, ∀ x : ℝ, earthquakeOp σ σinf x = (V x).re + a * x ^ 2 + b * x + c) →
      IsLineMeasure σ' → earthquakeMeasureNorm σ' σinf' < ⊤ → σ'.2 = 0 → σinf'.2 = 0 →
      HasUnlinkedSupport σ' σinf' →
      (∃ a b c : ℝ, ∀ x : ℝ, earthquakeOp σ' σinf' x = (V x).re + a * x ^ 2 + b * x + c) →
        σ = σ' ∧ σinf = σinf' := by
  sorry

end GardinerLakic2000
