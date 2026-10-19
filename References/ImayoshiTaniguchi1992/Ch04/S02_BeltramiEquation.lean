import References.ImayoshiTaniguchi1992.Ch04.S01_QuasiconformalMappings
import LiZhongQC.Ch02.S12_Existence

/-!
# Imayoshi–Taniguchi, Chapter 4 §4.2: The Beltrami differential equation (W2 batch I2)

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 4 §4.2 (`full.md` IT1:2975–3540,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: as in `Ch04/S01_QuasiconformalMappings`. The generalized (distributional) partial derivatives of a continuous function `f`
are `LiZhongQC.HasGenPartials f g h univ p` (`g = f_x`, `h = f_y`, in `L^p_loc`), with `f_z = LiZhongQC.genDz g h`, `f_z̄ = LiZhongQC.genDzbar g h`.
`C_p = LiZhongQC.hilbertNorm p` is the `L^p` norm of the Hilbert transform (IT Proposition 4.22), `B(ℂ)₁` with bounded support is
`LiZhongQC.IsCompactBeltramiCoeff μ k` (measurable, `|μ| ≤ k < 1`, vanishing outside a disc).

* Proposition 4.19 (Cauchy–Pompeiu formula for `L^p` derivatives) — exists: `LiZhongQC.eq11_11_pompeiu_gen`
* Lemma 4.20 (Hölder continuity of `Ph`) — exists: `LiZhongQC.lemma11_2`
* Lemma 4.21 (`‖Th‖₂ = ‖h‖₂`) — exists: `LiZhongQC.thm11_3_isometry`
* Proposition 4.22 (the Calderón–Zygmund constant `C_p`) — exists: `LiZhongQC.eq11_16`
* Proposition 4.23 (`(Ph)_z = Th`) — exists: `LiZhongQC.thm11_1`
* Theorem 4.24 (the normal solution exists) — exists: `LiZhongQC.thm12_1`
* Definition (the normal solution of `f_z̄ = μ f_z`, Theorem 4.24) — `IsNormalSolution`
* Corollary 1 to Theorem 4.24 (`L^p` estimates (4.20), (4.21) of the normal solution) — `cor4_24_1_a`, `cor4_24_1_b`
* Corollary 2 to Theorem 4.24 (`μ_n → μ` a.e. implies `f_n → f`) — exists: `LiZhongQC.eq12_1_solution_tendsto_cauchyT`
* Theorem 4.25 (the normal solution is quasiconformal with `μ_f = μ`) — exists: `LiZhongQC.thm12_1`
* Lemma 4.27 (the approximants for smooth `μ` are `C¹` homeomorphisms) — exists: `LiZhongQC.thm12_1_smooth_case`
* Theorem 4.30 (the measurable Riemann mapping theorem on `Ĉ`, normalized at `0, 1, ∞`) — exists: `LiZhongQC.thm13_7_normalized_existence`
* Proposition 4.31 (a quasiconformal map of `Δ` onto a Jordan domain extends to the closure) — exists:
  `LiZhongQC.thm13_3_boundary_correspondence`
* Proposition 4.33 (normalized quasiconformal self-map of `H` with a given `μ`) — exists: `GardinerLakic2000.cor1_1_1_a`

Omitted (U−): Lemma 4.26 (`u_z̄ = v_z` gives a `C¹` function), Lemma 4.28 (a local homeomorphism of `Ĉ` is a homeomorphism; cited only
inside the proof of Theorem 4.30, whose plane form is `LiZhongQC.lemma12_1`), Lemma 4.29 (distortion estimate for the approximants),
Proposition 4.32 (no quasiconformal map of `Δ` onto `ℂ`): technical steps of the existence proof, not cited by a later Teichmüller result.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (HasGenPartials genDz genDzbar hilbertNorm IsCompactBeltramiCoeff)

/-- **The normal solution** (Theorem 4.24, Ch. 4 §4.2.2, IT1:3194). For `p > 2` and a Beltrami coefficient `μ` with bounded support,
`f` is a normal solution of `f_z̄ = μ f_z` with the generalized partial derivatives `g = f_x`, `h = f_y`: `f` is continuous, `f(0) = 0`,
`f_z̄ = μ f_z` a.e., and `f_z − 1` belongs to `L^p(ℂ)` (with `f_z̄ ∈ L^p(ℂ)`). -/
def IsNormalSolution (p : ℝ) (μ f g h : ℂ → ℂ) : Prop :=
  Continuous f ∧ f 0 = 0 ∧ HasGenPartials f g h univ (ENNReal.ofReal p) ∧
    (∀ᵐ z, genDzbar g h z = μ z * genDz g h z) ∧ MemLp (fun z => genDz g h z - 1) (ENNReal.ofReal p) volume ∧
    MemLp (genDzbar g h) (ENNReal.ofReal p) volume

/-- **Corollary 1 to Theorem 4.24, first part** (Ch. 4 §4.2.3, IT1:3270, (4.20)). Under the circumstances of Theorem 4.24 (`p > 2`,
`μ ∈ B(ℂ)₁` with bounded support, `‖μ‖∞ = k` and `k C_p < 1`), the normal solution `f` satisfies
`‖f_z̄‖_p ≤ ‖μ‖_p/(1 − k C_p)`. -/
theorem cor4_24_1_a {p k : ℝ} (hp : 2 < p) (hk : 0 ≤ k) {μ f g h : ℂ → ℂ} (hμ : IsCompactBeltramiCoeff μ k)
    (hkp : k * hilbertNorm p < 1) (hf : IsNormalSolution p μ f g h) :
    eLpNorm (genDzbar g h) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (1 / (1 - k * hilbertNorm p)) * eLpNorm μ (ENNReal.ofReal p) volume := by
  sorry

/-- **Corollary 1 to Theorem 4.24, second part** (Ch. 4 §4.2.3, IT1:3270, (4.21)). With `K_p` the constant of Lemma 4.20 (depending
only on `p`): `|f(ζ₁) − f(ζ₂)| ≤ K_p/(1 − k C_p) ‖μ‖_p |ζ₁ − ζ₂|^{1 − 2/p} + |ζ₁ − ζ₂|` for every `ζ₁, ζ₂ ∈ ℂ`. -/
theorem cor4_24_1_b {p : ℝ} (hp : 2 < p) :
    ∃ K : ℝ, ∀ {k : ℝ}, 0 ≤ k → ∀ {μ f g h : ℂ → ℂ}, IsCompactBeltramiCoeff μ k → k * hilbertNorm p < 1 →
      IsNormalSolution p μ f g h → ∀ ζ₁ ζ₂ : ℂ,
        ‖f ζ₁ - f ζ₂‖ ≤ K / (1 - k * hilbertNorm p) * (eLpNorm μ (ENNReal.ofReal p) volume).toReal * ‖ζ₁ - ζ₂‖ ^ (1 - 2 / p) +
          ‖ζ₁ - ζ₂‖ := by
  sorry

end ImayoshiTaniguchi1992
