import References.FarkasKra1992.Ch02.S03_SquareIntegrableForms

/-!
# Farkas–Kra, Chapter II §4: Harmonic differentials

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. II §4 (`full.md` FK1:1892–2157).

Conventions: as in `Ch02/S03_SquareIntegrableForms`. A *local coordinate vanishing at `P₀`* is a chart `e` of the maximal
analytic atlas with `P₀ ∈ e.source` and `e P₀ = 0`; `z⁻ⁿ` is the function `x ↦ (e x)⁻ⁿ` (defined off `P₀`). Harmonic functions
are `Forster1981.IsHarmonicOn` (complex valued, smooth with `d′d″f = 0`; the real valued ones are the real parts). "`u − z⁻ⁿ`
is harmonic on a neighbourhood `N` of `P₀`" means that `u − z⁻ⁿ` (defined on `N ∖ {P₀}`) is the restriction of a function
harmonic on `N`. The energy conditions (4.1.6) and (4.1.7) are `IsL2Form1` of `du` off a neighbourhood of `P₀` and the
orthogonality `(du, df) = 0 = (du, *df)` for the smooth compactly supported `f` vanishing near `P₀`.

* Theorem II.4.1 — `thm2_4_1`
* II.4.2 (the variant with `Re z⁻ⁿ`, real valued `u`) — `para2_4_2_a`
* II.4.2 (uniqueness up to an additive constant on a compact surface) — `para2_4_2_b`
* Theorem II.4.3 — `thm2_4_3`
* II.4.3 Remark (uniqueness up to an additive constant on a compact surface) — `para2_4_3`

Omitted (U−): II.4.4 (the `arg` variant, no precise statement), II.4.5 (the Dirichlet principle, a digression with no
numbered result).
-/

open scoped Manifold ContDiff Topology
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Finite energy and orthogonality conditions** (Ch. II §4.1, (4.1.6)–(4.1.7), helper). `u` has finite energy off every
neighbourhood `N` of the singular set `S` (`du ∈ L²(M ∖ N)`), and `(du, df) = 0 = (du, *df)` for all smooth `f` with compact
support vanishing on a neighbourhood of `S`. -/
def HasFiniteEnergyAndOrth (u : X → ℂ) (S : Set X) : Prop :=
  (∀ N : Set X, IsOpen N → S ⊆ N → IsL2Form1 Nᶜ (dForm u)) ∧
    ∀ f : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f → HasCompactSupport f → (∃ N ∈ 𝓝ˢ S, ∀ x ∈ N, f x = 0) →
      HasL2Inner univ (dForm u) (dForm f) 0 ∧ HasL2Inner univ (dForm u) (starForm (dForm f)) 0

/-- **Theorem II.4.1** (Ch. II §4.1). Let `M` be a Riemann surface with `z` a local coordinate vanishing at `P₀ ∈ M`, and
`n ≥ 1`. There exists on `M` a function `u` with: (4.1.4) `u` is harmonic on `M ∖ {P₀}`; (4.1.5) `u − z⁻ⁿ` is harmonic on
every sufficiently small neighbourhood `N` of `P₀`; (4.1.6) `∬_{M∖N} du ∧ *dū < ∞`; (4.1.7) `(du, df) = 0 = (du, *df)` for all
smooth functions `f` on `M` that have compact support and vanish on a neighbourhood of `P₀`. -/
theorem thm2_4_1 {P₀ : X} {e : OpenPartialHomeomorph X ℂ} (he : e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X)
    (hP : P₀ ∈ e.source) (h0 : e P₀ = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : X → ℂ, IsHarmonicOn u {P₀}ᶜ ∧
      (∃ N ∈ 𝓝 P₀, ∃ h : X → ℂ, IsHarmonicOn h N ∧ ∀ x ∈ N, x ≠ P₀ → h x = u x - (e x) ^ (-(n : ℤ))) ∧
      HasFiniteEnergyAndOrth u {P₀} := by
  sorry

/-- **Unlabelled** (Ch. II §4.2, FK1:2062–2066). The condition (4.1.5) can be replaced by `u − Re z⁻ⁿ` harmonic in a
neighbourhood of `P₀`, and then `u` may be required to be real valued: for every `n ≥ 1` there is a real valued `u`
with (4.1.4), (4.1.6), (4.1.7) and `u − Re z⁻ⁿ` harmonic near `P₀`. -/
theorem para2_4_2_a {P₀ : X} {e : OpenPartialHomeomorph X ℂ} (he : e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X)
    (hP : P₀ ∈ e.source) (h0 : e P₀ = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : X → ℝ, IsHarmonicOn (fun x => (u x : ℂ)) {P₀}ᶜ ∧
      (∃ N ∈ 𝓝 P₀, ∃ h : X → ℂ, IsHarmonicOn h N ∧
        ∀ x ∈ N, x ≠ P₀ → h x = (u x : ℂ) - (((e x) ^ (-(n : ℤ))).re : ℂ)) ∧
      HasFiniteEnergyAndOrth (fun x => (u x : ℂ)) {P₀} := by
  sorry

/-- **Unlabelled** (Ch. II §4.2, FK1:2068). If `M` is compact, the function `u` of Theorem II.4.1 is unique up to an additive
constant: two functions with (4.1.4)–(4.1.7) differ by a constant. -/
theorem para2_4_2_b [CompactSpace X] {P₀ : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X) (hP : P₀ ∈ e.source) (h0 : e P₀ = 0) {n : ℕ} {u u' : X → ℂ}
    (hu : IsHarmonicOn u {P₀}ᶜ) (hu1 : ∃ N ∈ 𝓝 P₀, ∃ h : X → ℂ, IsHarmonicOn h N ∧
      ∀ x ∈ N, x ≠ P₀ → h x = u x - (e x) ^ (-(n : ℤ))) (hu2 : HasFiniteEnergyAndOrth u {P₀})
    (hv : IsHarmonicOn u' {P₀}ᶜ) (hv1 : ∃ N ∈ 𝓝 P₀, ∃ h : X → ℂ, IsHarmonicOn h N ∧
      ∀ x ∈ N, x ≠ P₀ → h x = u' x - (e x) ^ (-(n : ℤ))) (hv2 : HasFiniteEnergyAndOrth u' {P₀}) :
    ∃ c : ℂ, ∀ x, x ≠ P₀ → u' x = u x + c := by
  sorry

/-- **Theorem II.4.3** (Ch. II §4.3). Let `M` be a Riemann surface and `P₁`, `P₂` two points on `M`; let `z_j` be a local
coordinate vanishing at `P_j`. There exists on `M` a real valued function `u` with: (4.3.1) `u` is harmonic on `M ∖ {P₁, P₂}`;
(4.3.2) `u − log |z₁|` is harmonic in a neighbourhood of `P₁` and `u + log |z₂|` is harmonic in a neighbourhood of `P₂`;
(4.3.3) `∬_{M∖N} du ∧ *dū < ∞` for every open `N` containing `P₁` and `P₂`; (4.3.4) `(du, df) = 0 = (du, *df)` for all smooth `f`
with compact support vanishing on a neighbourhood of `P₁` and `P₂`.
Modelling: `P₁ ≠ P₂` (as in the proof). -/
theorem thm2_4_3 {P₁ P₂ : X} (hP : P₁ ≠ P₂) {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X) (he₂ : e₂ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X)
    (h₁ : P₁ ∈ e₁.source) (h₂ : P₂ ∈ e₂.source) (h₁₀ : e₁ P₁ = 0) (h₂₀ : e₂ P₂ = 0) :
    ∃ u : X → ℝ, IsHarmonicOn (fun x => (u x : ℂ)) ({P₁, P₂} : Set X)ᶜ ∧
      (∃ N ∈ 𝓝 P₁, ∃ h : X → ℂ, IsHarmonicOn h N ∧
        ∀ x ∈ N, x ≠ P₁ → h x = (u x : ℂ) - (Real.log ‖e₁ x‖ : ℂ)) ∧
      (∃ N ∈ 𝓝 P₂, ∃ h : X → ℂ, IsHarmonicOn h N ∧
        ∀ x ∈ N, x ≠ P₂ → h x = (u x : ℂ) + (Real.log ‖e₂ x‖ : ℂ)) ∧
      HasFiniteEnergyAndOrth (fun x => (u x : ℂ)) {P₁, P₂} := by
  sorry

/-- **Unlabelled** (Ch. II §4.3, Remark). For compact `M`, the function `u` of Theorem II.4.3 is unique up to an additive
constant. -/
theorem para2_4_3 [CompactSpace X] {P₁ P₂ : X} {e₁ e₂ : OpenPartialHomeomorph X ℂ} {u u' : X → ℝ}
    (hu : IsHarmonicOn (fun x => (u x : ℂ)) ({P₁, P₂} : Set X)ᶜ)
    (hu1 : ∃ N ∈ 𝓝 P₁, ∃ h : X → ℂ, IsHarmonicOn h N ∧ ∀ x ∈ N, x ≠ P₁ → h x = (u x : ℂ) - (Real.log ‖e₁ x‖ : ℂ))
    (hu2 : ∃ N ∈ 𝓝 P₂, ∃ h : X → ℂ, IsHarmonicOn h N ∧ ∀ x ∈ N, x ≠ P₂ → h x = (u x : ℂ) + (Real.log ‖e₂ x‖ : ℂ))
    (hu3 : HasFiniteEnergyAndOrth (fun x => (u x : ℂ)) {P₁, P₂})
    (hv : IsHarmonicOn (fun x => (u' x : ℂ)) ({P₁, P₂} : Set X)ᶜ)
    (hv1 : ∃ N ∈ 𝓝 P₁, ∃ h : X → ℂ, IsHarmonicOn h N ∧ ∀ x ∈ N, x ≠ P₁ → h x = (u' x : ℂ) - (Real.log ‖e₁ x‖ : ℂ))
    (hv2 : ∃ N ∈ 𝓝 P₂, ∃ h : X → ℂ, IsHarmonicOn h N ∧ ∀ x ∈ N, x ≠ P₂ → h x = (u' x : ℂ) + (Real.log ‖e₂ x‖ : ℂ))
    (hv3 : HasFiniteEnergyAndOrth (fun x => (u' x : ℂ)) {P₁, P₂}) :
    ∃ c : ℝ, ∀ x, x ≠ P₁ → x ≠ P₂ → u' x = u x + c := by
  sorry

end FarkasKra1992
