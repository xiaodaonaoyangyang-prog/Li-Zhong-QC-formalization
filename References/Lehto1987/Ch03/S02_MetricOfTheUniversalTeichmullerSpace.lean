import References.Lehto1987.Ch03.S01_ModelsOfTheUniversalTeichmullerSpace
import LiZhongQC.Ch11.S36_Hamilton

/-!
# Lehto, Chapter III §2: Metric of the universal Teichmüller space

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. III §2 (`full.md`
P1:3756–3959).

Conventions (see §1). The project's Teichmüller distance `LiZhongQC.UniversalTeichmuller.dist p q` is
`inf log K` over the representatives (with `f_μ ∈ F*`, the maximal dilatation of `f_ν ∘ f_μ⁻¹` taken on `f_μ(H)`, where
it is not conformal); Lehto's `τ` is half of it (decision B0.3), `teichDist`. Maximal dilatations of maps of plane
sets are the project's `LiZhongQC.maxDilatation` (the essential supremum of the dilatation quotient, in `[0, ∞]`). The
sup norm `‖μ‖∞` is `eLpNorm μ ⊤ volume`. "Metric space" and "continuous" statements about `T`, which carries no
topology instance, are written with `teichDist` in `ε–δ` form, as in Li Zhong §21.

* Definition (the Teichmüller distance `τ`, (2.1), §2.1) — `teichDist`
* Definition (`τ₁`, `τ₂`, (2.2), (2.3), §2.1) — `teichDist1`, `teichDist2`
* Lemma 2.1 (§2.1) — `lemma3_2_1`
* Formula (2.4) (§2.1) — `eq3_2_4`
* Unlabelled (§2.1, P1:3794): the infimum in (2.1) is attained — exists: `LiZhongQC.UniversalTeichmuller.eq21_1` (for
  twice the distance: some representatives realize it)
* Unlabelled (§2.1, P1:3794): `τ` is a metric — exists: `LiZhongQC.UniversalTeichmuller.dist_self_symm`,
  `LiZhongQC.UniversalTeichmuller.dist_triangle`, `LiZhongQC.UniversalTeichmuller.eq_of_dist_eq_zero` (jointly, for
  twice the distance, decision B0.13)
* Unlabelled (§2.1, P1:3796–3812): invariance under right translations; `τ([f], [g]) = τ(0, [g ∘ f⁻¹])` —
  `para3_2_1_c`
* Unlabelled (§2.2, P1:3818–3822): `τ` through complex dilatations,
  `τ = ½ min log((1 + ‖(μ − ν)/(1 − μ̄ν)‖∞)/(1 − ‖…‖∞))` — exists: `LiZhongQC.UniversalTeichmuller.eq21_4` (the infimum
  form for twice the distance; the minimum is attained by `LiZhongQC.UniversalTeichmuller.eq21_1`)
* Definition (the hyperbolic distance `‖h(μ, ν)‖∞` of complex dilatations, §2.2) — exists:
  `LiZhongQC.beltramiPoincareDist` (the essential supremum over the upper half-plane of the hyperbolic distance of the
  unit disc, with Lehto's normalization of I (1.1))
* Unlabelled (§2.2, P1:3835): `τ = min ‖h(μ, ν)‖∞` — omitted: not cited
* Definition (the distance `β`, §2.2) — `betaDist`
* Unlabelled (§2.2, P1:3846): `β = tanh τ`, and the infimum defining `β` is attained — `para3_2_2_b`
* Theorem 2.1 (§2.2) — exists: `LiZhongQC.UniversalTeichmuller.thm21_1_path_connected` (the path t ↦ [tμ] from the
  origin to [μ], continuous for twice the distance)
* Definition (length of an arc, geodesic, §2.3) — `arcLengthT`, `IsGeodesicT`
* Definition (extremal complex dilatation, §2.3) — `IsExtremalDil`
* Theorem 2.2 (§2.3) — `thm3_2_2`
* Lemma 2.2 (§2.4) — `lemma3_2_2`
* Theorem 2.3 (§2.4) — `thm3_2_3`
* Unlabelled (§2.4, P1:3956): convergent sequences have representatives with 1°, 3°, 4° of Lemma 2.2 — `para3_2_4`
* Unlabelled (§2.4, P1:3958): `(T, β)` is complete; `(Δ, q)` is not — omitted: not cited (U−)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf BeltramiH UniversalTeichmuller teichSetoid fMuSym
  normalizedSolution maxDilatation)
open LehtoVirtanen1973 (sphericalDist)

/-! ## §2.1 Definition of the Teichmüller distance -/

/-- **Definition** (the Teichmüller distance, (2.1), Ch. III §2.1):
`τ(p, q) = ½ inf {log K_{g ∘ f⁻¹} | f ∈ p, g ∈ q}`, half of the project's `UniversalTeichmuller.dist`.
Not a duplicate of `GardinerLakic2000.teichDist`, the distance of the Teichmüller space `T(R)` of a Riemann
surface. -/
def teichDist (p q : UniversalTeichmuller) : ℝ := (1 / 2) * UniversalTeichmuller.dist p q

/-- **Definition** (`τ₁`, (2.2), Ch. III §2.1). For a fixed representative `f₀ = f_{μ₀} ∈ p`:
`τ₁(p, q) = ½ inf {log K_{g ∘ f₀⁻¹} | g ∈ q}` (the maximal dilatation on `f₀(H)`). -/
def teichDist1 (μ₀ : BeltramiH) (q : UniversalTeichmuller) : ℝ :=
  (1 / 2) * sInf {d | ∃ ν : BeltramiH, Quotient.mk teichSetoid ν = q ∧
    d = Real.log (maxDilatation (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ)
      (normalizedSolution μ₀.1 '' upperHalf)).toReal}

/-- **Definition** (`τ₂`, (2.3), Ch. III §2.1). For fixed `f₀ = f_{μ₀} ∈ p`, `g₀ = f_{ν₀} ∈ q`, let `W` be the class
of the quasiconformal mappings of the plane which agree in `f₀(H′)` with `g₀ ∘ f₀⁻¹`;
`τ₂(p, q) = ½ inf {log K_w | w ∈ W}`. -/
def teichDist2 (μ₀ ν₀ : BeltramiH) : ℝ :=
  (1 / 2) * sInf {d | ∃ w : ℂ → ℂ, LiZhongQC.IsQuasiconformal w univ ∧ w '' univ = univ ∧
    EqOn w (normalizedSolution ν₀.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ)
      (normalizedSolution μ₀.1 '' lowerHalf) ∧ d = Real.log (maxDilatation w univ).toReal}

/-- **Lemma 2.1** (Ch. III §2.1). The functions `τ`, `τ₁` and `τ₂` are the same; the same holds when the points of
`T` are represented by the mappings `f^μ ∈ F` (with maximal dilatations in `H`).
Modelling: for representatives `μ₀ ∈ p`, `ν₀ ∈ q`; the last conjunct is the version with `F`. -/
theorem lemma3_2_1 {μ₀ ν₀ : BeltramiH} {p q : UniversalTeichmuller} (hp : Quotient.mk teichSetoid μ₀ = p)
    (hq : Quotient.mk teichSetoid ν₀ = q) :
    teichDist p q = teichDist1 μ₀ q ∧ teichDist p q = teichDist2 μ₀ ν₀ ∧
      teichDist p q = (1 / 2) * sInf {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧
        Quotient.mk teichSetoid ν = q ∧
        d = Real.log (maxDilatation (fMuSym ν.1 ∘ Function.invFunOn (fMuSym μ.1) univ) upperHalf).toReal} := by
  sorry

/-- **Formula (2.4)** (Ch. III §2.1). `τ(p, q) = ½ log K_h`, where `h = g₀ ∘ f₀⁻¹|ℝ` for `f₀ ∈ p`, `g₀ ∈ q` and `K_h` is
the smallest maximal dilatation of the quasiconformal self-maps of `H` with boundary values `h` (I.5.7).
Modelling: `f₀ = f^μ`, `g₀ = f^ν`; `h` is the real function with `h(f^μ(x)) = f^ν(x)` on `ℝ`; `K_h` is
`extremalDilatation h`, which is finite (part of the conclusion). -/
theorem eq3_2_4 (μ ν : BeltramiH) {h : ℝ → ℝ} (hh : ∀ x : ℝ, ((h (fMuSym μ.1 x).re : ℝ) : ℂ) = fMuSym ν.1 x) :
    extremalDilatation h < ⊤ ∧ teichDist (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν) =
      (1 / 2) * Real.log (extremalDilatation h).toReal := by
  sorry

/-- **Unlabelled** (Ch. III §2.1, P1:3796–3812). The Teichmüller distance is invariant under the right translations,
`τ([f], [g]) = τ([f ∘ f₀⁻¹], [g ∘ f₀⁻¹])`; in particular `τ([f], [g]) = τ(0, [g ∘ f⁻¹])`.
Modelling: `[g ∘ f⁻¹]` is the point `r` with `r ∘ [f] = [g]` (`IsTProduct`). -/
theorem para3_2_1_c :
    (∀ ω : UniversalTeichmuller → UniversalTeichmuller, IsRightTranslation ω →
      ∀ p q, teichDist (ω p) (ω q) = teichDist p q) ∧
    ∀ p q r : UniversalTeichmuller, IsTProduct r p q → teichDist p q = teichDist UniversalTeichmuller.origin r := by
  sorry

/-! ## §2.2 Teichmüller distance and complex dilatation -/

/-- **Definition** (the distance `β`, Ch. III §2.2):
`β(p, q) = inf {‖(μ − ν)/(1 − μ̄ν)‖∞ | μ ∈ p, ν ∈ q}` (the norm taken over `H`, where the coefficients live). -/
def betaDist (p q : UniversalTeichmuller) : ℝ :=
  sInf {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
    d = UniversalTeichmuller.dilatationDiffNorm μ.1 ν.1}

/-- **Unlabelled** (Ch. III §2.2, P1:3846). `β = tanh τ`; in the definition of `β` the infimum is attained. -/
theorem para3_2_2_b :
    (∀ p q : UniversalTeichmuller, betaDist p q = Real.tanh (teichDist p q)) ∧
    ∀ p q : UniversalTeichmuller, ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧
      Quotient.mk teichSetoid ν = q ∧ betaDist p q = UniversalTeichmuller.dilatationDiffNorm μ.1 ν.1 := by
  sorry

/-! ## §2.3 Geodesics for the Teichmüller metric -/

/-- **Definition** (length of an arc, Ch. III §2.3). The length of `γ` between the parameters `a` and `b` is the
supremum of `Σ τ(γ(t_{j−1}), γ(t_j))` over the subdivisions `a = t₀ < t₁ < ⋯ < t_n = b`, in `[0, ∞]`. -/
def arcLengthT (γ : ℝ → UniversalTeichmuller) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : Fin (n + 1) → ℝ) (_ : Monotone t ∧ t 0 = a ∧ t (Fin.last n) = b),
    ENNReal.ofReal (∑ j : Fin n, teichDist (γ (t j.castSucc)) (γ (t j.succ)))

/-- **Definition** (geodesic, Ch. III §2.3). An arc `γ : [0, 1] → (T, τ)` is a geodesic if the length of every subarc
is equal to the distance between its endpoints.
Modelling: `γ` is continuous on `[0, 1]` for `τ` (`ε–δ`). -/
def IsGeodesicT (γ : ℝ → UniversalTeichmuller) : Prop :=
  (∀ t₀ ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ → teichDist (γ t) (γ t₀) < ε) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → arcLengthT γ a b = ENNReal.ofReal (teichDist (γ a) (γ b))

/-- **Definition** (extremal complex dilatation, Ch. III §2.3): `μ ∈ p` is extremal if
`‖μ‖∞ = min {‖ν‖∞ | ν ∈ p}`. -/
def IsExtremalDil (μ : BeltramiH) : Prop :=
  ∀ ν : BeltramiH, Quotient.mk teichSetoid ν = Quotient.mk teichSetoid μ → eLpNorm μ.1 ⊤ volume ≤ eLpNorm ν.1 ⊤ volume

/-- **Theorem 2.2** (Ch. III §2.3). If `μ` is an extremal complex dilatation for the point `p ∈ T`, then
`μ_t = ((1 + |μ|)^t − (1 − |μ|)^t)/((1 + |μ|)^t + (1 − |μ|)^t) · μ/|μ|`, `0 ≤ t ≤ 1` (2.5), is extremal for the point
`p_t = [μ_t]`. The arc `t ↦ p_t` is a geodesic from `0` to `p`, and `τ(p_t, 0) = t τ(p, 0)` (2.6).
Modelling: `μ_t` is `0` where `μ = 0`; `μ_t ∈ B` is part of the conclusion. [OCR] (2.6) is printed
`τ(p₁, 0) := t τ(p, 0)`. -/
theorem thm3_2_2 {μ : BeltramiH} (hμ : IsExtremalDil μ) :
    ∃ M : ℝ → BeltramiH,
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, (M t).1 z =
        ((((1 + ‖μ.1 z‖) ^ t - (1 - ‖μ.1 z‖) ^ t) / ((1 + ‖μ.1 z‖) ^ t + (1 - ‖μ.1 z‖) ^ t) : ℝ) : ℂ) *
          (μ.1 z / (‖μ.1 z‖ : ℂ))) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsExtremalDil (M t)) ∧ IsGeodesicT (fun t => Quotient.mk teichSetoid (M t)) ∧
      Quotient.mk teichSetoid (M 0) = UniversalTeichmuller.origin ∧
      Quotient.mk teichSetoid (M 1) = Quotient.mk teichSetoid μ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, teichDist (Quotient.mk teichSetoid (M t)) UniversalTeichmuller.origin =
        t * teichDist (Quotient.mk teichSetoid μ) UniversalTeichmuller.origin := by
  sorry

/-! ## §2.4 Completeness of the universal Teichmüller space -/

/-- **Lemma 2.2** (Ch. III §2.4). Every Cauchy sequence in `(T, τ)` contains a subsequence whose points are
represented by complex dilatations `μₙ` with the following properties: 1° `lim μₙ(z) = μ(z)` exists almost
everywhere; 2° `[f_{μₙ}] → [f_μ]` in the Teichmüller metric; 3° `f_{μₙ}(z) → f_μ(z)` uniformly in the spherical
metric; 4° `f^{μₙ}(z) → f^μ(z)` locally uniformly in the upper half-plane.
Modelling: the limit `μ` is in `B`; the spherical metric is LV's `sphericalDist` on `ℂ̄`. [OCR] 4° prints `f_n^{μ_n}`
for `f^{μ_n}`. -/
theorem lemma3_2_2 {pn : ℕ → UniversalTeichmuller}
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, teichDist (pn m) (pn n) < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (μn : ℕ → BeltramiH) (μ : BeltramiH),
      (∀ n, Quotient.mk teichSetoid (μn n) = pn (φ n)) ∧
      (∀ᵐ z : ℂ, Tendsto (fun n => (μn n).1 z) atTop (𝓝 (μ.1 z))) ∧
      Tendsto (fun n => teichDist (Quotient.mk teichSetoid (μn n)) (Quotient.mk teichSetoid μ)) atTop (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ℂ,
        sphericalDist (normalizedSolution (μn n).1 z) (normalizedSolution μ.1 z) < ε) ∧
      TendstoLocallyUniformlyOn (fun n => fMuSym (μn n).1) (fMuSym μ.1) atTop upperHalf := by
  sorry

/-- **Theorem 2.3** (Ch. III §2.4). The universal Teichmüller space is complete: every Cauchy sequence of `(T, τ)`
converges. -/
theorem thm3_2_3 {pn : ℕ → UniversalTeichmuller}
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, teichDist (pn m) (pn n) < ε) :
    ∃ p : UniversalTeichmuller, Tendsto (fun n => teichDist (pn n) p) atTop (𝓝 0) := by
  sorry

/-- **Unlabelled** (Ch. III §2.4, P1:3956). If `pₙ → p` in `(T, τ)`, there are complex dilatations `μₙ ∈ pₙ`,
`μ ∈ p`, such that the conditions 1°, 3° and 4° of Lemma 2.2 hold (no subsequence is needed). -/
theorem para3_2_4 {pn : ℕ → UniversalTeichmuller} {p : UniversalTeichmuller}
    (hp : Tendsto (fun n => teichDist (pn n) p) atTop (𝓝 0)) :
    ∃ (μn : ℕ → BeltramiH) (μ : BeltramiH), (∀ n, Quotient.mk teichSetoid (μn n) = pn n) ∧
      Quotient.mk teichSetoid μ = p ∧ (∀ᵐ z : ℂ, Tendsto (fun n => (μn n).1 z) atTop (𝓝 (μ.1 z))) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ z : ℂ,
        sphericalDist (normalizedSolution (μn n).1 z) (normalizedSolution μ.1 z) < ε) ∧
      TendstoLocallyUniformlyOn (fun n => fMuSym (μn n).1) (fMuSym μ.1) atTop upperHalf := by
  sorry

end Lehto1987
