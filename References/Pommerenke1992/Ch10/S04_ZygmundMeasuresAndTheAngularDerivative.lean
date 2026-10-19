import References.Pommerenke1992.Ch10.S03_LowerBoundsForCompression

/-!
# Pommerenke 1992, Ch. 10 §10.4 Zygmund Measures and the Angular Derivative

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 10 *Hausdorff Measure*, §10.4; source `full.md`
of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 2315–2503.

* Definition (Zygmund measure, recalled from Section 7.2, l. 2317; used in Theorem 10.12 and in the proof of
  Theorem 10.14; index "Zygmund measure 235") — exists: `Pommerenke1992.IsZygmundMeasure` ((7.2.6) of Part C, the
  same condition: a non-negative finite measure on 𝕋 with |μ(I) − μ(I′)| bounded by a constant times Λ(I) for
  adjacent arcs I, I′ of equal length)
* Definition (the gauge `ψ` of (10.4.1), in Theorem 10.12, l. 2319–2323; cited "given by (1)" in Theorems 10.13 and
  10.14 and in Exercise 10.4.1) — `makarovPsi`
* Theorem 10.12 (Mak89b; (10.4.2); cited at l. 2331 and 2435) — `thm10_12`
* Theorem 10.13 (Mak89b, compare AnPi89; cited at P1 l. 3447, "see Theorem 10.13"; index "angular derivative … 237") —
  `thm10_13`
* Theorem 10.14 (cited at l. 1721, "Makarov's Theorem 10.14", and in the proof of Theorem 10.13, l. 2403) —
  `thm10_14`
* Theorem 10.15 (Mak89a; (10.4.11), whose tag is lost in the OCR; cited "(11)" at l. 2445; index "twisting 238") —
  `thm10_15`
* Formula (10.4.12) (§10.4, P2 l. 2465–2469, U+: Mak89d, Mak89e; cited at P1 l. 3266, "see (10.4.12)", and P2
  l. 2883, §11.2; index "bounded on radius 239") — `eq10_4_12`
* Rohde's theorem (Roh89; (10.4.14), (10.4.15), l. 2477–2489; named "Rohde's theorem stated above" in
  Exercise 10.4.2, l. 2499) — `rohde_theorem`

Not items (DESIGN §3): "The function `ψ` in this result is related to that of Theorem 10.6 but is not the same" and
Makarov's example of a nonzero Zygmund measure `μ` with `Λ_ψ(supp μ) < ∞`, so that `ψ` in (2) cannot be replaced by
any `φ` with `φ(t)/ψ(t) → 0` (l. 2331; a quoted sharpness remark, not cited); the proof of Theorem 10.12
((10.4.3)–(10.4.7), l. 2333–2387; Proposition 7.3, (4.2.5), Theorem 8.9, "as in the proof of Theorem 8.10"; the
display at l. 2360 is truncated in the OCR, crop `db3af5cf…`); "The angular derivative was studied in Section 4.3 and
6.5" (l. 2389; a pointer); the history of Theorem 10.13 (Hal68, AnPi88, Ber92), its sharpness (Mak89b: some `f` has
`{ζ ∈ 𝕋 : f'(ζ) ≠ ∞ exists}` of σ-finite `Λ_ψ`-measure) and the Anderson conjecture (And71) (l. 2393–2399; quoted, a
conjecture); the proof of Theorem 10.13 (l. 2401–2403; Proposition 10.2, Proposition 4.12, Proposition 4.7,
`g = −log f'`); the proof of Theorem 10.14 ((10.4.8)–(10.4.10), l. 2413–2435; Fatou's theorem, the Riesz uniqueness
theorem, (4.2.1), Proposition 7.3, Dur70, Theorem 4.3, Löwner's lemma, HeSt69, (4.2.19), Theorems 10.12 and 10.11;
"`ψ` satisfies the assumptions of Theorem 10.11 with `α = 1/2`" needs a suitable extension of `ψ` away from `0`, U−);
the sharpness of Theorem 10.15 (Mak89a: for some `f` the set where (11) holds has `Λ_φ`-measure `0` for every
`φ = O(t^α)`, `α < 1`; l. 2445; quoted, not cited); the proof of Theorem 10.15 (l. 2447–2463; Proposition 1.2,
Becker's criterion, (4.2.4), Dur70, Exercise 10.2.2, Theorem 9.19, Theorem 11.1, Ost35; its
"`|arg[f_k(rζ) − f_k(ζ)] < 2π`" misses a bar); (10.4.13) `dim{ζ ∈ 𝕋 : sup_r |log f'(rζ)| < ∞} = 1` (l. 2471–2475;
U−: (10.4.12) with `g = log f' ∈ 𝓑`, not cited); "In other words practically all types of behaviour occur in sets of
dimension almost one" and "We will consider the subspace `B₀` in Section 11.2" (l. 2489–2491; remarks); Exercises
10.4.1–10.4.2 and Fig. 10.3 (l. 2493–2502).

**Conventions.** As in §10.2. "`M₁, M₂, …` suitable positive constants" (l. 2317); `K` of Rohde's theorem is
absolute. `𝓑` is `IsBloch` and `‖g‖_𝓑` is `(blochSeminorm g).toReal` (Chapter 4). `Λ_ψ` for the gauge (10.4.1) is
`hausdorffMeasureGauge ψ` for every gauge `ψ` with `ψ =ᶠ[𝓝[>] 0] makarovPsi` (Q10.8). Arguments (Theorem 10.15):
`arg f'(rζ)` is `Im L(rζ)` for a holomorphic branch `L` of `log f'` on `𝔻`, and `arg[f(rζ) − f(ζ)]` is `θ(rζ)` for a
continuous branch `θ` of `arg[f(z) − f(ζ)]` on `𝔻` (the Part C form of (6.4.9)); the boundedness does not depend on
the branch.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane unitDisc)

/-- **Definition (10.4.1)** (§10.4, in Theorem 10.12; P2 l. 2319–2323; cited "given by (1)" in Theorem 10.13,
l. 2391, Theorem 10.14, l. 2411, and Exercise 10.4.1). `ψ(t) = t √(log(1/t) · log log log(1/t))` for
`0 < t ≤ e^{−e^e}`.
Modelling: the book's formula as a real function, defined by the book for `0 < t ≤ e^{−e^e}`; its values elsewhere
are junk that no statement sees: statements use `makarovPsi` only through gauges equal to it on some interval
`(0, t₀)`, as for `makarovPhi` (Q10.8). Unlike (10.3.1) it is increasing on its whole printed interval; the crop of
(10.4.1) was checked. -/
def makarovPsi (t : ℝ) : ℝ :=
  t * Real.sqrt (Real.log (1 / t) * Real.log (Real.log (Real.log (1 / t))))

/-- **Theorem 10.12** (§10.4; Mak89b; (10.4.2); P2 l. 2319–2329; cited at P2 l. 2331 and in the proof of
Theorem 10.14, l. 2435). Let `μ` be a Zygmund measure and let `ψ` be given by (10.4.1). If `E` is a Borel set on
`𝕋`, then (2) `Λ_ψ(E) = 0 ⟹ μ(E) = 0`.
Modelling: `μ` is a measure on `ℂ` with `IsZygmundMeasure μ` ((7.2.6); finite and carried by `𝕋`); `Λ_ψ` is
`hausdorffMeasureGauge ψ` for any gauge `ψ` equal to `makarovPsi` on some `(0, t₀)` (Q10.8; such gauges exist, and
all of them give the same `Λ_ψ`). -/
theorem thm10_12 {ψ : ℝ → ℝ} (hψ : IsHausdorffGauge ψ) (hψM : ψ =ᶠ[𝓝[>] 0] makarovPsi) {μ : Measure ℂ}
    (hμ : IsZygmundMeasure μ) {E : Set ℂ} (hEm : MeasurableSet E) (hET : E ⊆ sphere 0 1)
    (hE : hausdorffMeasureGauge ψ E = 0) :
    μ E = 0 := by
  sorry

/-- **Theorem 10.13** (§10.4; Mak89b, compare AnPi89; P2 l. 2391; cited at P1 l. 3447, §4.3, "see Theorem 10.13").
Let `f` map `𝔻` conformally into `ℂ`. Then `f` has a finite angular derivative on a set `E ⊂ 𝕋` with `Λ_ψ(E) > 0`,
where `ψ` is given by (10.4.1).
Modelling: "a finite angular derivative at `ζ`" is `HasAngularDerivative f ζ a` with `a ∈ ℂ` (§4.3; the value `0` is
allowed); `Λ_ψ` as in `thm10_12`. -/
theorem thm10_13 {ψ : ℝ → ℝ} (hψ : IsHausdorffGauge ψ) (hψM : ψ =ᶠ[𝓝[>] 0] makarovPsi) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∃ E ⊆ sphere (0 : ℂ) 1, 0 < hausdorffMeasureGauge ψ E ∧ ∀ ζ ∈ E, ∃ a : ℂ, HasAngularDerivative f ζ a := by
  sorry

/-- **Theorem 10.14** (§10.4; P2 l. 2405–2411; cited at P2 l. 1721, "Makarov's Theorem 10.14 gives the best possible
bound", and in the proof of Theorem 10.13, l. 2403). If `g ∈ 𝓑` has a finite angular limit almost nowhere, then
`Re g(rζ) → +∞` as `r → 1−`, `ζ ∈ E`, for some Borel set `E ⊂ 𝕋` with `Λ_ψ(E) > 0`, where `ψ` is given by (10.4.1).
Modelling: `𝓑` is `IsBloch`; "a finite angular limit almost nowhere" is: for almost every `t`, `g` has no finite
angular limit at `e^{it}`; `Λ_ψ` as in `thm10_12`. -/
theorem thm10_14 {ψ : ℝ → ℝ} (hψ : IsHausdorffGauge ψ) (hψM : ψ =ᶠ[𝓝[>] 0] makarovPsi) {g : ℂ → ℂ}
    (hg : IsBloch g)
    (hnowhere : ∀ᵐ t : ℝ, ¬ ∃ w : ℂ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) w) :
    ∃ E : Set ℂ, MeasurableSet E ∧ E ⊆ sphere 0 1 ∧ 0 < hausdorffMeasureGauge ψ E ∧
      ∀ ζ ∈ E, Tendsto (fun r : ℝ => (g (r * ζ)).re) (𝓝[<] 1) atTop := by
  sorry

/-- **Theorem 10.15** (§10.4; Mak89a; (10.4.11), whose tag is lost in the OCR (the crop `ca862b75…` prints "(11)");
P2 l. 2437–2443; cited "(11)" at l. 2445). If `f` maps `𝔻` conformally into `ℂ`, then there is a set `E ⊂ 𝕋` with
`dim E = 1` such that (11) `sup_r |arg f'(rζ)| < ∞`, `sup_r |arg[f(rζ) − f(ζ)]| < ∞` for `ζ ∈ E`.
Modelling (Q10.13(a)): at every `ζ ∈ E` the finite angular limit `f(ζ) = w` exists (part of the conclusion: the proof
deletes the other points, l. 2461); `arg f'(rζ)` is `Im L(rζ)` for every holomorphic branch `L` of `log f'` on `𝔻`,
and `arg[f(rζ) − f(ζ)]` is `θ(rζ)` for every continuous branch `θ` of `arg[f(z) − w]` on `𝔻` (both kinds exist: `f'`
has no zeros, `w ∉ f(𝔻)`, and `𝔻` is simply connected; two branches differ by a constant, so the boundedness is
the same for all of them); `sup_r` is over `0 ≤ r < 1`. -/
theorem thm10_15 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∃ E ⊆ sphere (0 : ℂ) 1, dimH E = 1 ∧ ∀ ζ ∈ E, ∃ w : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w ∧
      (∀ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc → (∀ z ∈ unitDisc, exp (L z) = deriv f z) →
        ∃ M : ℝ, ∀ r ∈ Ico (0 : ℝ) 1, |(L (r * ζ)).im| ≤ M) ∧
      ∀ θ : ℂ → ℝ, ContinuousOn θ unitDisc → (∀ z ∈ unitDisc, f z - w = (‖f z - w‖ : ℂ) * exp (θ z * I)) →
        ∃ M : ℝ, ∀ r ∈ Ico (0 : ℝ) 1, |θ (r * ζ)| ≤ M := by
  sorry

/-- **Formula (10.4.12)** (§10.4; Mak89d, Mak89e; P2 l. 2465–2469; cited at P1 l. 3266, §4.2, "much more is true as
Makarov has proved; see (10.4.12)", and at P2 l. 2883, §11.2, where (11.2.7) "follows from it"). If `g ∈ 𝓑`, then
(12) `dim{ζ ∈ 𝕋 : sup_r |g(rζ)| < ∞} = 1`.
Modelling: `sup_r |g(rζ)| < ∞` is a bound `M` of `|g(rζ)|` for `0 ≤ r < 1`. -/
theorem eq10_4_12 {g : ℂ → ℂ} (hg : IsBloch g) :
    dimH {ζ ∈ sphere (0 : ℂ) 1 | ∃ M : ℝ, ∀ r ∈ Ico (0 : ℝ) 1, ‖g (r * ζ)‖ ≤ M} = 1 := by
  sorry

/-- **Rohde's theorem** (§10.4; Roh89; (10.4.14), (10.4.15); P2 l. 2477–2489; named "Rohde's theorem stated above"
in Exercise 10.4.2, l. 2499). Let `g ∈ 𝓑` have finite angular limits almost nowhere and consider a square grid of
mesh size `a > 0`. We prescribe a sequence `(Q_n)` of closed squares of this grid with the only stipulation that
`Q_n` and `Q_{n+1}` are adjacent. Then there exists a set `E ⊂ 𝕋` with (14) `dim E ≥ 1 − a^{−1} K ‖g‖_𝓑` (where `K`
is an absolute constant) such that, for each `ζ ∈ E`, we can find `r_n → 1` with (15) `g(rζ) ∈ Q_n ∪ Q_{n+1}` for
`r_n ≤ r ≤ r_{n+1}`.
Modelling (a named theorem, although the name occurs only in an exercise, Q10.9; Q10.13(b)): `K` is absolute
(`∃ K, ∀ g a (Q_n)`); the grid is the standard grid of the closed squares `[ja, (j+1)a] × [ka, (k+1)a]` (a translated
or rotated grid gives the same statement for `g + b` or `e^{iβ} g`, which changes neither `‖g‖_𝓑` nor the angular
limits), and `Q_n` is given by its index `s n = (j, k) ∈ ℤ²`; "adjacent" is "sharing a side" (Fig. 10.3 shows a
chain of edge-neighbours), `|j_{n+1} − j_n| + |k_{n+1} − k_n| = 1`; `(r_n)` is a non-decreasing sequence in `[0, 1)`
with `r_n → 1`, indexed from `n = 0` like `(Q_n)`; `‖g‖_𝓑` is `(blochSeminorm g).toReal` (finite for `g ∈ 𝓑`). The
crop prints `g(rζ) ⊂ Q_n ∪ Q_{n+1}` (crop `ce80aa2a…`), read `∈`. -/
theorem rohde_theorem :
    ∃ K : ℝ, ∀ g : ℂ → ℂ, IsBloch g →
      (∀ᵐ t : ℝ, ¬ ∃ w : ℂ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) w) →
      ∀ a : ℝ, 0 < a → ∀ s : ℕ → ℤ × ℤ, (∀ n, |(s (n + 1)).1 - (s n).1| + |(s (n + 1)).2 - (s n).2| = 1) →
        ∃ E ⊆ sphere (0 : ℂ) 1, ENNReal.ofReal (1 - K * (blochSeminorm g).toReal / a) ≤ dimH E ∧
          ∀ ζ ∈ E, ∃ r : ℕ → ℝ, Monotone r ∧ (∀ n, 0 ≤ r n ∧ r n < 1) ∧ Tendsto r atTop (𝓝 1) ∧
            ∀ n, ∀ ρ ∈ Icc (r n) (r (n + 1)), ∃ m ∈ ({n, n + 1} : Set ℕ),
              a * ((s m).1 : ℝ) ≤ (g (ρ * ζ)).re ∧ (g (ρ * ζ)).re ≤ a * ((s m).1 + 1 : ℝ) ∧
              a * ((s m).2 : ℝ) ≤ (g (ρ * ζ)).im ∧ (g (ρ * ζ)).im ≤ a * ((s m).2 + 1 : ℝ) := by
  sorry

end Pommerenke1992
