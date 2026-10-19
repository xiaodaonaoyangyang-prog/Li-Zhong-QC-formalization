import References.Lehto1987.Ch03.S02_MetricOfTheUniversalTeichmullerSpace

/-!
# Lehto, Chapter III §3: Space of quasisymmetric functions

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. III §3 (`full.md`
P1:3960–4099).

Conventions (see §1, §2). `X` is `qsX`. The maximal dilatation `K*_h` of a quasisymmetric `h` is that of I.5.1
(`boundaryMaxDil (realExt h)`). The map (3.1) is any `Φ : T → X` with `Φ([μ]) = f^μ|ℝ` (it exists and is bijective,
`eq3_1_1`). The ball `B` is `LiZhongQC.BeltramiH`, with the sup norm `eLpNorm · ⊤ volume`. "Continuous" and
"homeomorphism" statements are written in `ε–δ` form with the metrics `τ` (`teichDist`) and `ρ` (`rhoDist`).

* Definition (the distance `ρ` on `X`, §3.1) — `rhoDist`
* Unlabelled (§3.1, P1:3970): `ρ` is a metric — omitted: "easy to verify" (U−)
* Theorem 3.1 (§3.1) — `thm3_3_1`
* Formula (3.2) (§3.1) — `eq3_3_2`
* Unlabelled (§3.1, P1:3988): `(X, ρ)` is complete — omitted: not cited (U−)
* Unlabelled (§3.1, P1:3990–3992): `ρ`-convergence implies locally uniform convergence, and the converse fails —
  `para3_3_1`
* Definition (the map `ψ : B → X`, §3.2) — `psiBX`
* Definition (the section `s` through the Beurling–Ahlfors extension, §3.2) — `baSection`
* Unlabelled (§3.2, P1:4010, 4028–4030): `ψ` is continuous and `s` is a continuous section of `ψ` — `para3_3_2`
* Theorem 3.2 (§3.3, Earle–Eells) — `thm3_3_2`
* Theorem 3.3 (§3.4) — `thm3_3_3`
* Unlabelled (§3.4, P1:4098): left translations need not be continuous — omitted: a remark restating Theorem 3.3
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf BeltramiH UniversalTeichmuller teichSetoid fMuSym
  beurlingAhlfors)

/-! ## §3.1 Distance between quasisymmetric functions -/

/-- **Definition** (the distance `ρ`, Ch. III §3.1): `ρ(h₁, h₂) = ½ log K*_{h₂ ∘ h₁⁻¹}` for `h₁, h₂ ∈ X`, with the
maximal dilatation `K*` of I.5.1.
Modelling: `h₁⁻¹` is `Function.invFun h₁` (`h₁` is a bijection of `ℝ`); the value is real (`K*` is finite for the
quasisymmetric functions of `X`, the only arguments used). -/
def rhoDist (h₁ h₂ : ℝ → ℝ) : ℝ :=
  (1 / 2) * Real.log (boundaryMaxDil (realExt (h₂ ∘ Function.invFun h₁))).toReal

/-- **Theorem 3.1** (Ch. III §3.1). The group isomorphism `[f] ↦ f|ℝ` (3.1) is a homeomorphism of `(T, τ)` onto
`(X, ρ)`.
Modelling: for the map `Φ` of (1.1): `Φ` and its inverse are continuous (`Φ` is bijective onto `X` by `eq3_1_1`). -/
theorem thm3_3_1 (Φ : UniversalTeichmuller → ℝ → ℝ)
    (hΦ : ∀ (μ : BeltramiH) (x : ℝ), ((Φ (Quotient.mk teichSetoid μ) x : ℝ) : ℂ) = fMuSym μ.1 x) :
    (∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, teichDist p q < δ → rhoDist (Φ p) (Φ q) < ε) ∧
      ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, rhoDist (Φ p) (Φ q) < δ → teichDist p q < ε := by
  sorry

/-- **Formula (3.2)** (Ch. III §3.1). `ρ(f₁|ℝ, f₂|ℝ) ≤ τ([f₁], [f₂])`.
Modelling: through the map `Φ` of (1.1). -/
theorem eq3_3_2 (Φ : UniversalTeichmuller → ℝ → ℝ)
    (hΦ : ∀ (μ : BeltramiH) (x : ℝ), ((Φ (Quotient.mk teichSetoid μ) x : ℝ) : ℂ) = fMuSym μ.1 x)
    (p q : UniversalTeichmuller) : rhoDist (Φ p) (Φ q) ≤ teichDist p q := by
  sorry

/-- **Unlabelled** (Ch. III §3.1, P1:3990–3992). (a) If `h, hₙ ∈ X` and `ρ(hₙ, h) → 0`, then `hₙ → h` locally
uniformly. (b) The converse is not true: `hₙ(x) = x` for `x ≤ n`, `hₙ(x) = 2x − n` for `x > n`, `n = 1, 2, …` (written with `n + 1`, `n : ℕ`; `n = 0` is not normalized) are in `X` and tend to
the identity locally uniformly, but `ρ(hₙ, id) ↛ 0`. -/
theorem para3_3_1 :
    (∀ (hn : ℕ → ℝ → ℝ) (h : ℝ → ℝ), (∀ n, hn n ∈ qsX) → h ∈ qsX →
      Tendsto (fun n => rhoDist (hn n) h) atTop (𝓝 0) → TendstoLocallyUniformly hn h atTop) ∧
    ((∀ n : ℕ, (fun x : ℝ => if x ≤ (n + 1 : ℕ) then x else 2 * x - (n + 1 : ℕ)) ∈ qsX) ∧
      TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => if x ≤ (n + 1 : ℕ) then x else 2 * x - (n + 1 : ℕ)) id atTop ∧
      ¬ Tendsto (fun n : ℕ => rhoDist (fun x : ℝ => if x ≤ (n + 1 : ℕ) then x else 2 * x - (n + 1 : ℕ)) id) atTop (𝓝 0)) := by
  sorry

/-! ## §3.2 Existence of a section -/

/-- **Definition** (the map `ψ : B → X`, Ch. III §3.2): `ψ(μ) = f^μ|ℝ`.
Modelling: the real values of `f^μ` (`LiZhongQC.fMuSym`, real on `ℝ`) at the real points. -/
def psiBX (μ : BeltramiH) : ℝ → ℝ := fun x => (fMuSym μ.1 x).re

/-- **Definition** (the section `s : X → B`, Ch. III §3.2): `s(h)` is the complex dilatation of the Beurling–Ahlfors
extension `f(x + iy) = ½ ∫₀¹ (h(x + ty) + h(x − ty)) dt + i ∫₀¹ (h(x + ty) − h(x − ty)) dt` of `h` (I.5.3) in the
upper half-plane.
Modelling: `LiZhongQC.beurlingAhlfors h 2` (parameter `2`: Lehto's imaginary part has no factor `½`); the complex
dilatation `∂̄f/∂f` in `H`, extended by `0`. -/
def baSection (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then LiZhongQC.complexDilatation (beurlingAhlfors h 2) z else 0

/-- **Unlabelled** (Ch. III §3.2, P1:4010, 4028–4030). `ψ` maps `B` into `X` and is continuous; `s` maps `X` into
`B`, is continuous, and `ψ ∘ s` is the identity of `X`: `s` is a section.
Modelling: `B` carries the sup norm; `s(h) ∈ B` is part of the conclusion. -/
theorem para3_3_2 :
    (∀ μ : BeltramiH, psiBX μ ∈ qsX) ∧
    (∀ μ : BeltramiH, ∀ ε > 0, ∃ δ > 0, ∀ ν : BeltramiH, eLpNorm (μ.1 - ν.1) ⊤ volume < ENNReal.ofReal δ →
      rhoDist (psiBX μ) (psiBX ν) < ε) ∧
    (∀ h ∈ qsX, ∃ hs : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ LiZhongQC.IsBeltramiCoeff (baSection h) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → baSection h z = 0, psiBX ⟨baSection h, hs⟩ = h) ∧
    ∀ h ∈ qsX, ∀ ε > 0, ∃ δ > 0, ∀ h' ∈ qsX, rhoDist h h' < δ →
      eLpNorm (baSection h - baSection h') ⊤ volume < ENNReal.ofReal ε := by
  sorry

/-! ## §3.3 Contractibility of the universal Teichmüller space -/

/-- **Theorem 3.2** (Ch. III §3.3, Earle–Eells). The universal Teichmüller space is contractible: there is a
continuous mapping `H : T × [0, 1] → T` which is the identity for `t = 0` and constant for `t = 1` (the proof's
`([s(h)], t) ↦ [(1 − t) s(h)]`).
Modelling: continuity in `(p, t)` in `ε–δ` form for `τ`. -/
theorem thm3_3_2 :
    ∃ H : UniversalTeichmuller → ℝ → UniversalTeichmuller, (∀ p, H p 0 = p) ∧
      (∀ p, H p 1 = UniversalTeichmuller.origin) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, teichDist p q < δ → |s - t| < δ →
        teichDist (H p t) (H q s) < ε := by
  sorry

/-! ## §3.4 Incompatibility of the group structure with the metric -/

/-- **Theorem 3.3** (Ch. III §3.4). The universal Teichmüller space is not a topological group: there are `[f]` and
`[gₙ] → [g]` such that `[f ∘ gₙ]` does not tend to `[f ∘ g]`.
Modelling: the products are the group law (1.2) (`IsTProduct`). -/
theorem thm3_3_3 :
    ∃ (p q r : UniversalTeichmuller) (qn rn : ℕ → UniversalTeichmuller), IsTProduct p q r ∧
      (∀ n, IsTProduct p (qn n) (rn n)) ∧ Tendsto (fun n => teichDist (qn n) q) atTop (𝓝 0) ∧
      ¬ Tendsto (fun n => teichDist (rn n) r) atTop (𝓝 0) := by
  sorry

end Lehto1987
