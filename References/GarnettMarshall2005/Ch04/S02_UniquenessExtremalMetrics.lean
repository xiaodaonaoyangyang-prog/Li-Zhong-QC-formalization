import References.GarnettMarshall2005.Ch04.S01_DefinitionsExamples

/-!
# Garnett–Marshall, Chapter IV §2: Uniqueness of extremal metrics

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. IV §2 (pp. 133–134;
`full.md` P1:5984–6015).

Conventions of Chapter IV as in §1: planar domains and path families of point sets, metrics
`LiZhongQC.densitiesP0 Ω`, area `LiZhongQC.rhoArea ρ Ω`, `ρ`-length `pathRhoLength`, all in `[0, ∞]`. The ratio
`L²(Γ, ρ)/A(Ω, ρ)` is `pathRhoLength Γ ρ ^ 2 / rhoArea ρ Ω`; for a metric `A(Ω, ρ) ∈ (0, ∞)`, so the quotient has no
junk value (it is `∞` exactly when `L(Γ, ρ) = ∞`). "a.e. dxdy" is almost everywhere on `Ω` for area measure.

* Theorem 2.1 (§2; (2.1)) — `thm4_2_1_a`, `thm4_2_1_b`, `thm4_2_1_c`

Correction (Theorem 2.1, the equality clause and the "in particular"): as printed they are false when the common
ratio `L²/A` is `0` or `∞`, and they are stated with `0 < L²/A < ∞` (resp. `0 < λ_Ω(Γ) < ∞`); the counterexamples
are in the docstring of `thm4_2_1_b` (leader ruling B12(1)).

Not stated (inventory U−): the opening remark that deciding when a path family has an extremal metric is an open
problem, and that an extremal metric is unique up to a multiplicative constant (P1:5986; it announces Theorem 2.1).
(2.2) is a step of the proof.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (densitiesP0 rhoArea)

/-! ### GM4-A helpers (-d9): `ρ`-lengths, areas and the convexity estimates of Theorem 2.1 -/

/-- **Theorem 2.1** (Ch. IV §2), inequality (2.1) (cited at P1:6108, 6229 and in App. H, P3:4620). Let `Γ` be a path
family on `Ω` and let `ρ₁` and `ρ₂` be metrics on `Ω` satisfying
`L²(Γ, ρ₁)/A(Ω, ρ₁) = L²(Γ, ρ₂)/A(Ω, ρ₂)`. Let `ρ₃ = c₁ρ₁ + c₂ρ₂`, where `c_j = ½ A(Ω, ρ_j)^{−1/2}`. Then
(2.1) `L²(Γ, ρ₃)/A(Ω, ρ₃) ≥ L²(Γ, ρ₁)/A(Ω, ρ₁)`.
Modelling: `Ω` is a plane domain; the constants `c_j` and the ratios are in `[0, ∞]` (`A(Ω, ρ_j) ∈ (0, ∞)`, so
`c_j` is a finite positive number); (2.1) holds as printed, the ratios `0` and `∞` included. -/
theorem thm4_2_1_a {Ω : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ)
    {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : ρ₁ ∈ densitiesP0 Ω) (hρ₂ : ρ₂ ∈ densitiesP0 Ω)
    (h₁₂ : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = pathRhoLength Γ ρ₂ ^ 2 / rhoArea ρ₂ Ω) {c₁ c₂ : ℝ≥0∞}
    (hc₁ : c₁ = 2⁻¹ * rhoArea ρ₁ Ω ^ (-(1 / 2 : ℝ))) (hc₂ : c₂ = 2⁻¹ * rhoArea ρ₂ Ω ^ (-(1 / 2 : ℝ)))
    {ρ₃ : ℂ → ℝ≥0∞} (hρ₃ : ρ₃ = fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) :
    pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω ≤ pathRhoLength Γ ρ₃ ^ 2 / rhoArea ρ₃ Ω := by
  have _ := hΩ
  have _ := hΓ
  subst hρ₃
  obtain ⟨hL, hA, -⟩ := gm4a_rho3_bounds hρ₁ hρ₂ h₁₂ hc₁ hc₂
  exact gm4a_le_div_of_le_one hL hA

/-- **Theorem 2.1** (Ch. IV §2), the equality clause. In the situation of `thm4_2_1_a`, if equality holds in (2.1),
then `c₁ρ₁ = c₂ρ₂` a.e. dxdy.
Modelling: **[CORRECTION]** (leader ruling B12(1)). As printed the clause is false when the common ratio `L²/A` is
`0` or `∞`, and it is stated under `0 < L²(Γ, ρ₁)/A(Ω, ρ₁) < ∞`. Counterexamples: let `Γ = {γ₀}` for a segment
`γ₀ ⊆ Ω` and let `D₁`, `D₂` be disjoint discs in `Ω \ γ₀`. (Ratio `0`.) `ρ_j = χ_{D_j}`: then
`L(Γ, ρ₁) = L(Γ, ρ₂) = L(Γ, ρ₃) = 0`, so equality holds in (2.1), but `c₁ρ₁ ≠ c₂ρ₂` on `D₁`, a set of positive area.
(Ratio `∞`.) `ρ_j = ∞ · χ_{γ₀} + χ_{D_j}` (metrics, since `γ₀` is a null set): then all three `ρ`-lengths are `∞`,
equality holds in (2.1), and again `c₁ρ₁ ≠ c₂ρ₂` on `D₁`. The book's proof divides by `L`: with `A = 1` it uses
`L(Γ, ρ₃)² ≥ L(Γ, ρ₁)²` and `A(Ω, ρ₃) ≤ 1` to force `A(Ω, ρ₃) = 1`, which needs `0 < L < ∞`. -/
theorem thm4_2_1_b {Ω : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ)
    {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₁ : ρ₁ ∈ densitiesP0 Ω) (hρ₂ : ρ₂ ∈ densitiesP0 Ω)
    (h₁₂ : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = pathRhoLength Γ ρ₂ ^ 2 / rhoArea ρ₂ Ω)
    (hpos : 0 < pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω) (hfin : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω < ⊤)
    {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ = 2⁻¹ * rhoArea ρ₁ Ω ^ (-(1 / 2 : ℝ)))
    (hc₂ : c₂ = 2⁻¹ * rhoArea ρ₂ Ω ^ (-(1 / 2 : ℝ))) {ρ₃ : ℂ → ℝ≥0∞} (hρ₃ : ρ₃ = fun z => c₁ * ρ₁ z + c₂ * ρ₂ z)
    (heq : pathRhoLength Γ ρ₃ ^ 2 / rhoArea ρ₃ Ω = pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω) :
    (fun z => c₁ * ρ₁ z) =ᵐ[volume.restrict Ω] fun z => c₂ * ρ₂ z := by
  have _ := hΩ
  have _ := hΓ
  subst hρ₃
  obtain ⟨hL, hA, hA₀⟩ := gm4a_rho3_bounds hρ₁ hρ₂ h₁₂ hc₁ hc₂
  have h1 : rhoArea (fun z => c₁ * ρ₁ z + c₂ * ρ₂ z) Ω = 1 := gm4a_eq_one_of_div_eq hpos hfin hL hA hA₀ heq
  obtain ⟨-, -, hf, -⟩ := gm4a_coeff Γ hρ₁ hc₁
  obtain ⟨-, -, hg, -⟩ := gm4a_coeff Γ hρ₂ hc₂
  refine gm4a_ae_eq_of_rhoArea_add ((gm4a_mem_densitiesP0.1 hρ₁).1.const_mul c₁)
    ((gm4a_mem_densitiesP0.1 hρ₂).1.const_mul c₂) ?_ ?_
  · rw [hf, hg]
    exact gm4a_quarter_add_lt_top
  · rw [h1, hf, hg]
    exact gm4a_one_eq_quarters

/-- **Theorem 2.1** (Ch. IV §2), "in particular". If `ρ₁` and `ρ₂` are extremal metrics for `Γ`, normalized by
`A(Ω, ρ₁) = A(Ω, ρ₂)`, then `ρ₁ = ρ₂` a.e. dxdy.
Modelling: **[CORRECTION]** (leader ruling B12(1)): stated under `0 < λ_Ω(Γ) < ∞`, the common ratio of two extremal
metrics being `λ_Ω(Γ)`. For `Γ = {γ₀}` (a segment) `λ_Ω(Γ) = ∞`, and the metrics of ratio `∞` of `thm4_2_1_b`, with
discs `D₁`, `D₂` of equal area, are extremal, of equal area and not equal a.e.; when `λ_Ω(Γ) = 0` (for example for
the family of all rectifiable arcs in `Ω`) every metric is extremal. -/
theorem thm4_2_1_c {Ω : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {Γ : Set (Set ℂ)} (hΓ : IsPathFamily Ω Γ)
    (hpos : 0 < extremalLengthGM Ω Γ) (hfin : extremalLengthGM Ω Γ < ⊤) {ρ₁ ρ₂ : ℂ → ℝ≥0∞}
    (hρ₁ : IsExtremalMetricGM Ω Γ ρ₁) (hρ₂ : IsExtremalMetricGM Ω Γ ρ₂) (hA : rhoArea ρ₁ Ω = rhoArea ρ₂ Ω) :
    ρ₁ =ᵐ[volume.restrict Ω] ρ₂ := by
  obtain ⟨hρ₁m, hr₁⟩ := hρ₁
  obtain ⟨hρ₂m, hr₂⟩ := hρ₂
  have h₁₂ : pathRhoLength Γ ρ₁ ^ 2 / rhoArea ρ₁ Ω = pathRhoLength Γ ρ₂ ^ 2 / rhoArea ρ₂ Ω := hr₁.trans hr₂.symm
  have hc₂ : 2⁻¹ * rhoArea ρ₁ Ω ^ (-(1 / 2 : ℝ)) = 2⁻¹ * rhoArea ρ₂ Ω ^ (-(1 / 2 : ℝ)) := by rw [hA]
  obtain ⟨hL, hA1, hA4⟩ := gm4a_rho3_bounds hρ₁m hρ₂m h₁₂ rfl hc₂
  have hmem := gm4a_rho3_mem (gm4a_mem_densitiesP0.1 hρ₁m).1 (gm4a_mem_densitiesP0.1 hρ₂m).1 _ _ hA1 hA4
  have hge := thm4_2_1_a hΩ hΓ hρ₁m hρ₂m h₁₂ rfl hc₂ rfl
  have heq := le_antisymm ((gm4a_ratio_le (Γ := Γ) hmem).trans hr₁.symm.le) hge
  have hae := thm4_2_1_b hΩ hΓ hρ₁m hρ₂m h₁₂ (by rw [hr₁]; exact hpos) (by rw [hr₁]; exact hfin) rfl hc₂ rfl heq
  obtain ⟨hc0, hctop, -, -⟩ := gm4a_coeff Γ hρ₁m rfl
  exact gm4a_ae_eq_of_const_mul hc0 hctop hae

end GarnettMarshall2005
