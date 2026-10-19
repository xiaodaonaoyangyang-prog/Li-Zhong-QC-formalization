import References.Lehto1987.Ch03.S03_SpaceOfQuasisymmetricFunctions

/-!
# Lehto, Chapter III §4: Space of Schwarzian derivatives

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. III §4 (`full.md`
P1:4100–4338).

Conventions (see §1–§3). In §4–§5 Lehto exchanges the roles of the half-planes (`f_μ` conformal in `H`), "which
does not affect any of the results". The model here is the project's throughout (decision B0.2): `μ` lives in the
upper half-plane and `f_μ` is conformal in the lower half-plane `H′`, so every half-plane of §4 is mirrored:
- `Q` is the space `LiZhongQC.bersSpaceL` of holomorphic functions in `H′` with finite hyperbolic sup norm;
- `s_μ = S_{f_μ|H′}` is `LiZhongQC.bersFunction`, and the Bers map `[μ] ↦ s_μ` is `LiZhongQC.bersMapU` (`T(1)` is its
  range);
- `U` is `LiZhongQC.schwarzianUnivalentSet`, the Schwarzians of the univalent meromorphic functions in `H′`;
- the explicit formula `μ(z̄) = −2y²φ(z)` becomes `μ(z) = −2y²φ(z̄)` for `z ∈ H`.

The norm is Lehto's `‖φ‖ = sup 4y²|φ|`, i.e. `Gehring1978.hypNorm` on `H′` (decision B0.3; it is 4 times the project's
`LiZhongQC.bersNormL`); the distance of `Q` is `q(φ₁, φ₂) = ‖φ₁ − φ₂‖`.

* Definition (the Banach space `Q` and its norm, §4.1) — exists: `LiZhongQC.bersSpaceL`, `Gehring1978.hypNorm`
  (Lehto's norm is the hyperbolic sup norm with the density of curvature −4, decision B0.3)
* Unlabelled (§4.1, P1:4122): `Q` is a Banach space — `para3_4_1_a`
* Definition (`s_μ = S_{f_μ|H}`, §4.1) — exists: `LiZhongQC.bersFunction`
* Unlabelled (§4.1, P1:4124): `s_μ` is well defined on `T` and `‖s_μ‖ ≤ 6` — exists:
  `LiZhongQC.bersFunction_eq_of_equiv`, `LiZhongQC.bersMapU_mem` (jointly; the bound reads 3/2 in the project's norm,
  which is a quarter of Lehto's)
* Formula (4.1) (§4.2) — `eq3_4_1`
* Formula (4.2) (§4.2) — `eq3_4_2`
* Formula (4.3) (§4.2) — omitted: formula (1.10) of II.1.3 (`eq2_1_10`)
* Formula (4.4) (§4.2) — `eq3_4_4`
* Formula (4.5) (§4.2) — omitted: a step of the proof of (4.6)
* Formula (4.6) (§4.2) — `eq3_4_6`
* Theorem 4.1 (§4.3) — exists: `LiZhongQC.thm21_2_lipschitz`, `LiZhongQC.thm21_2_injective`,
  `LiZhongQC.thm21_2_inverse_continuous` (jointly: the Bers map is Lipschitz, injective, and has a continuous
  inverse on its image)
* Definition (`T(1)`, the image of the Bers imbedding, §4.3) — exists: `LiZhongQC.bersMapU` (its range)
* Unlabelled (§4.3, P1:4214): `T(1)` is the set of the Schwarzians of the conformal maps with a quasiconformal
  extension to the plane — `para3_4_3_a`
* Unlabelled (§4.3, P1:4216–4219): `B(0, 2) ⊂ T(1)`, with the explicit inverse `φ ↦ [μ]` — `para3_4_3_b`
* Unlabelled (§4.3, P1:4222): `(T(1), q)` is not complete — omitted: not cited (U−)
* Definition (the set `U`, §4.4) — exists: `LiZhongQC.schwarzianUnivalentSet`
* Unlabelled (§4.4, P1:4244–4246): `cl B(0, 2) ⊂ U ⊂ cl B(0, 6)` and the diameter of `U` is 12 — `para3_4_4_a`
* Unlabelled (§4.4, P1:4248): `U` is closed in `Q` — `para3_4_4_b`
* Formula (4.8) (§4.4) — omitted: an approximation step, not cited
* Theorem 4.2 (§4.5, Gehring) — exists: `LiZhongQC.thm21_4_gehring` (the interior points of U in the Banach space
  are exactly the range of the Bers map)
* Unlabelled (§4.6, P1:4304–4310, Gehring, quoted): the domain `G` bounded by two spirals — `para3_4_6`
* Theorem 4.3 (§4.6) — omitted: the project's statement `gehring_closure_ne` was deleted by user decision, 2026-10-17
* Unlabelled (§4.6, P1:4323–4337): Flinn's Jordan example, `diam T(1) = 12`, connectedness, Thurston's isolated
  points — omitted: quoted or not cited
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf BeltramiH UniversalTeichmuller teichSetoid
  normalizedSolution bersSpaceL bersMapU schwarzianUnivalentSet schwarzian maxDilatation)
open References (IsJordanDomainExt)
open Gehring1978 (hypNorm IsConformalExt imageExt)

/-! ## §4.1 Mapping into the space of Schwarzian derivatives -/

/-- **Unlabelled** (Ch. III §4.1, P1:4122). `Q` is complete: every Cauchy sequence of `(Q, ‖·‖)` converges in `Q`. -/
theorem para3_4_1_a {φn : ℕ → ℂ → ℂ} (hφn : ∀ n, φn n ∈ bersSpaceL)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, hypNorm (φn m - φn n) (toExt lowerHalf) < ENNReal.ofReal ε) :
    ∃ φ ∈ bersSpaceL, Tendsto (fun n => hypNorm (φn n - φ) (toExt lowerHalf)) atTop (𝓝 0) := by
  sorry

/-! ## §4.2 Comparison of distances -/

/-- **Formula (4.1)** (Ch. III §4.2). `q(s_μ, 0) ≤ 6 β([μ], 0)`. -/
theorem eq3_4_1 (p : UniversalTeichmuller) :
    hypNorm (bersMapU p) (toExt lowerHalf) ≤ ENNReal.ofReal (6 * betaDist p UniversalTeichmuller.origin) := by
  sorry

/-- **Formula (4.2)** (Ch. III §4.2). `q(s_μ, 0) ≥ 2 β([μ], 0)`. -/
theorem eq3_4_2 (p : UniversalTeichmuller) :
    ENNReal.ofReal (2 * betaDist p UniversalTeichmuller.origin) ≤ hypNorm (bersMapU p) (toExt lowerHalf) := by
  sorry

/-- **Formula (4.4)** (Ch. III §4.2). `q(s_μ, s_ν) ≤ σ₀(A_ν) β([μ], [ν])`, where `A_ν` is the quasidisc on which
`f_ν` is conformal and `σ₀` its outer radius of univalence (II.2.6); since `σ₀ ≤ 12`, also `q(s_μ, s_ν) ≤ 12 β`.
Modelling: `A_ν = f_ν(H′)` in the project's model (decision B0.2). -/
theorem eq3_4_4 (μ ν : BeltramiH) :
    hypNorm (bersMapU (Quotient.mk teichSetoid μ) - bersMapU (Quotient.mk teichSetoid ν)) (toExt lowerHalf) ≤
        outerRadiusUniv (toExt (normalizedSolution ν.1 '' lowerHalf)) *
          ENNReal.ofReal (betaDist (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν)) ∧
      hypNorm (bersMapU (Quotient.mk teichSetoid μ) - bersMapU (Quotient.mk teichSetoid ν)) (toExt lowerHalf) ≤
        ENNReal.ofReal (12 * betaDist (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν)) := by
  sorry

/-- **Formula (4.6)** (Ch. III §4.2). If `ν` is chosen in its class so that `f_ν` has the smallest maximal dilatation
`K_ν`, then `q(s_μ, s_ν) ≥ ε(K_ν) β([μ], [ν])`, where `ε` is the constant of Theorem II.4.1.
Modelling: the constant `ε(K)` of Theorem II.4.1 cannot be named; `∀ K, ∃ ε > 0`, for every extremal `ν` with
`K_ν ≤ K` (the property passes to smaller `ε`). -/
theorem eq3_4_6 (K : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ ν : BeltramiH, IsExtremalDil ν →
      maxDilatation (normalizedSolution ν.1) univ ≤ ENNReal.ofReal K →
      ENNReal.ofReal (ε * betaDist (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν)) ≤
        hypNorm (bersMapU (Quotient.mk teichSetoid μ) - bersMapU (Quotient.mk teichSetoid ν)) (toExt lowerHalf) := by
  sorry

/-! ## §4.3 Imbedding of the universal Teichmüller space -/

/-- **Unlabelled** (Ch. III §4.3, P1:4214). `T(1) = {S_f | f is conformal in H and has a quasiconformal extension to
the plane}`.
Modelling: the half-plane `H′` of the project's model; the Schwarzians are restricted to `H′` (as the values of the
Bers map). -/
theorem para3_4_3_a :
    range bersMapU = {φ | ∃ f : ℂ → ℂ, LiZhongQC.IsConformalOnto f lowerHalf (f '' lowerHalf) ∧
      (∃ F : ℂ → ℂ, LiZhongQC.IsQuasiconformal F univ ∧ F '' univ = univ ∧ EqOn F f lowerHalf) ∧
      φ = lowerHalf.indicator (schwarzian f)} := by
  sorry

/-- **Unlabelled** (Ch. III §4.3, P1:4216–4219). `T(1)` contains the open ball `B(0, 2) = {φ ∈ Q | ‖φ‖ < 2}`, and in
this ball the inverse of the Bers imbedding is `φ ↦ [μ]` with `μ(z̄) = −2y²φ(z)`.
Modelling: mirrored (decision B0.2): `μ(z) = −2y²φ(z̄)` for `z = x + iy` in `H`, `φ` on `H′`. -/
theorem para3_4_3_b {φ : ℂ → ℂ} (hφ : φ ∈ bersSpaceL) (h2 : hypNorm φ (toExt lowerHalf) < 2) :
    ∃ μ : BeltramiH, (∀ z ∈ upperHalf, μ.1 z = -2 * ((z.im : ℂ) ^ 2) * φ (conj z)) ∧
      bersMapU (Quotient.mk teichSetoid μ) = lowerHalf.indicator φ := by
  sorry

/-! ## §4.4 Schwarzian derivatives of univalent functions -/

/-- **Unlabelled** (Ch. III §4.4, P1:4244–4246). `U` contains the closure of `B(0, 2)` and is contained in the closure
of `B(0, 6)`; the diameter of `U` is `12`. -/
theorem para3_4_4_a :
    (∀ φ ∈ bersSpaceL, hypNorm φ (toExt lowerHalf) ≤ 2 → lowerHalf.indicator φ ∈ schwarzianUnivalentSet) ∧
      (∀ φ ∈ schwarzianUnivalentSet, hypNorm φ (toExt lowerHalf) ≤ 6) ∧
      ⨆ (φ ∈ schwarzianUnivalentSet) (ψ ∈ schwarzianUnivalentSet), hypNorm (φ - ψ) (toExt lowerHalf) = 12 := by
  sorry

/-- **Unlabelled** (Ch. III §4.4, P1:4248). `U` is closed in `Q`. -/
theorem para3_4_4_b {φn : ℕ → ℂ → ℂ} (hφn : ∀ n, φn n ∈ schwarzianUnivalentSet) {φ : ℂ → ℂ} (hφ : φ ∈ bersSpaceL)
    (hlim : Tendsto (fun n => hypNorm (φn n - φ) (toExt lowerHalf)) atTop (𝓝 0)) :
    lowerHalf.indicator φ ∈ schwarzianUnivalentSet := by
  sorry

/-! ## §4.6 Closure of the universal Teichmüller space -/

/-- **Unlabelled** (Ch. III §4.6, P1:4304–4310, Gehring, quoted). Let `G` be the complement of the curve
`γ = {z = ±e^{(−a+i)t} | 0 ≤ t < ∞} ∪ {0}`, where `a > 0` is small. There is a positive constant `ε` such that if `f`
is a conformal mapping of `G` and `‖S_f‖_G ≤ ε`, then `f(G)` is not a Jordan domain.
Modelling: "`a` small": for all `a` in some interval `(0, a₀)`; `G` is a domain of `ℂ̄` (it contains `∞`). -/
theorem para3_4_6 :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℂ → ℂ,
        IsConformalExt f (toExt ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ (z = Complex.exp ((-a + I) * t) ∨
          z = -Complex.exp ((-a + I) * t))} ∪ {0}))ᶜ →
        hypNorm (schwarzian f) (toExt ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ (z = Complex.exp ((-a + I) * t) ∨
          z = -Complex.exp ((-a + I) * t))} ∪ {0}))ᶜ ≤ ENNReal.ofReal ε →
        ¬ IsJordanDomainExt (imageExt f (toExt ({z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ (z = Complex.exp ((-a + I) * t) ∨
          z = -Complex.exp ((-a + I) * t))} ∪ {0}))ᶜ) := by
  sorry

end Lehto1987
