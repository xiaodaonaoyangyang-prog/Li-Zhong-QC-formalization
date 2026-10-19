import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Hubbard 2006, Appendix A6: Compact perturbations

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 5979–6260 and `H3` lines 1–114.

**Conventions.** `E`, `F` are Banach spaces over `ℝ` or `ℂ` (`𝕜` with `[RCLike 𝕜]`), maps are continuous linear maps `E
→L[𝕜] F`, `u` is a compact operator (`IsCompactOperator`). *Strict* means closed range. A *quasi-monomorphism* is a
strict map with finite dimensional kernel, a *quasi-epimorphism* has a finite dimensional cokernel, a
*quasi-isomorphism* (Fredholm operator) has both, and the index is `dim ker − dim coker`. For quasi-isomorphisms these
are Mathlib's `ContinuousLinearMap.IsFredholm` (for Banach spaces the kernel is automatically complemented and the range
closed) and `LinearMap.index`. The **Hölder seminorm** of §A6.3 is `holderSemi α f = sup_{z₁ ≠ z₂} ‖f z₁ − f z₂‖ / ‖z₁ −
z₂‖^α`, valued in `[0, ∞]` (no junk value when the supremum is infinite). **Book imprecision (A6.3.5):** the printed
`‖f‖_α` is a *seminorm* (it vanishes on constants) and "the `0`-Hölder norm is the sup-norm" is false for the printed
formula (it gives the oscillation); here `‖f‖_0` is the sup norm `supNorm f` and `‖f‖_α` is the seminorm; with these
readings the stated inequalities are true. The Cauchy transform is the convolution `(1/πz) ∗ f`, `cauchyTransform f z =
∫ f(w)/(π (z − w)) dA(w)` (junk `0` only if the integrand is not integrable, which does not happen for the bounded
compactly supported `f` of the statements).

* Definition A6.1.1 (1) (strict map) — `IsStrictMap`
* Definition A6.1.1 (2), (3) (quasi-monomorphism, quasi-epimorphism) — `IsQuasiMonomorphism`, `IsQuasiEpimorphism`
* Definition (the transpose `f^⊤`) — `transposeCLM`
* Definition A6.1.1 (4), (5) (quasi-isomorphism = Fredholm operator, its index) — exists:
  `ContinuousLinearMap.IsFredholm`, `LinearMap.index`
* Theorem A6.1.2 (1) (quasi-monomorphisms are stable under compact perturbation) — `thmA6_1_2_a`
* Theorem A6.1.2 (2) (quasi-epimorphisms are stable under compact perturbation) — `thmA6_1_2_b`
* Theorem A6.1.2 (3) (Riesz perturbation theorem: Fredholm operators and their index) — `thmA6_1_2_c`
* Lemma A6.1.3 (quasi-monomorphism iff proper on a closed ball) — `lemmaA6_1_3`
* Lemma A6.1.4 (strict, quasi-monomorphism, quasi-epimorphism, compactness and duality) — `lemmaA6_1_4_a`,
  `lemmaA6_1_4_b`, `lemmaA6_1_4_c`, `lemmaA6_1_4_d`
* Section A6.2 (Schwartz perturbation, alternating sums, families of complexes) — omitted: scope (support for Appendix
  A8 only)
* Exercises A6.2.3, A6.3.3, A6.3.5, A6.3.6 — omitted: exercises
* Definition (the Hölder seminorm, A6.3.5; the Cauchy transform) — `holderSemi`, `supNorm`, `cauchyTransform`
* Proposition A6.3.1 (`∂̄ ((1/πz) ∗ f) = f`) — `propA6_3_1`
* Theorem A6.3.2 (Hölder estimate of the Cauchy transform) — `thmA6_3_2`
* Theorem A6.3.4 (Hölder estimate of the derivative of the Cauchy transform) — `thmA6_3_4`
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace Hubbard2006

section Operators

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Strict linear map** (Def. A6.1.1 (1)): the image is closed. -/
def IsStrictMap (f : E →L[𝕜] F) : Prop := IsClosed (range f)

/-- The **transpose** `f^⊤ : F^⊤ → E^⊤`, `φ ↦ φ ∘ f`, of a continuous linear map between the (topological) duals. -/
noncomputable def transposeCLM (f : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip f

/-- **Quasi-monomorphism** (Def. A6.1.1 (2)): strict, with finite dimensional kernel. -/
def IsQuasiMonomorphism (f : E →L[𝕜] F) : Prop := IsStrictMap f ∧ FiniteDimensional 𝕜 (LinearMap.ker (f : E →ₗ[𝕜] F))

/-- **Quasi-epimorphism** (Def. A6.1.1 (3)): the cokernel `F/f(E)` is finite dimensional. -/
def IsQuasiEpimorphism (f : E →L[𝕜] F) : Prop := FiniteDimensional 𝕜 (F ⧸ LinearMap.range (f : E →ₗ[𝕜] F))

/-- **Theorem A6.1.2 (1)** (Riesz perturbation theorem, Appendix A6, H2:6003). If `f` is a quasi-monomorphism and `u` is
compact, then `f + u` is a quasi-monomorphism. -/
theorem thmA6_1_2_a (f u : E →L[𝕜] F) (hu : IsCompactOperator u) (hf : IsQuasiMonomorphism f) :
    IsQuasiMonomorphism (f + u) := by
  sorry

/-- **Theorem A6.1.2 (2)** (Appendix A6, H2:6003). If `f` is a quasi-epimorphism and `u` is compact, then `f + u` is a
quasi-epimorphism. -/
theorem thmA6_1_2_b (f u : E →L[𝕜] F) (hu : IsCompactOperator u) (hf : IsQuasiEpimorphism f) :
    IsQuasiEpimorphism (f + u) := by
  sorry

/-- **Theorem A6.1.2 (3)** (Appendix A6, H2:6003). If `f` is a quasi-isomorphism (Fredholm operator) and `u` is compact,
then `f + u` is a quasi-isomorphism and `index f = index (f + u)`. -/
theorem thmA6_1_2_c (f u : E →L[𝕜] F) (hu : IsCompactOperator u) (hf : f.IsFredholm) :
    (f + u).IsFredholm ∧ LinearMap.index (f : E →ₗ[𝕜] F) = LinearMap.index ((f + u : E →L[𝕜] F) : E →ₗ[𝕜] F) := by
  sorry

/-- **Lemma A6.1.3** (Appendix A6, H2:6017). A continuous linear map `f : E → F` is a quasi-monomorphism iff there is a
closed ball `B` of positive radius in `E` such that the restriction of `f` to `B` is proper. -/
theorem lemmaA6_1_3 (f : E →L[𝕜] F) :
    IsQuasiMonomorphism f ↔ ∃ (x : E) (r : ℝ), 0 < r ∧ IsProperMap ((Metric.closedBall x r).domRestrict f) := by
  sorry

/-- **Lemma A6.1.4 (a)** (Appendix A6, H2:6035). `f` is strict iff its transpose `f^⊤ : F^⊤ → E^⊤` is strict. -/
theorem lemmaA6_1_4_a (f : E →L[𝕜] F) : IsStrictMap f ↔ IsStrictMap (transposeCLM f) := by
  sorry

/-- **Lemma A6.1.4 (b)** (Appendix A6). `f` is a quasi-epimorphism iff `f^⊤` is a quasi-monomorphism. -/
theorem lemmaA6_1_4_b (f : E →L[𝕜] F) :
    IsQuasiEpimorphism f ↔ IsQuasiMonomorphism (transposeCLM f) := by
  sorry

/-- **Lemma A6.1.4 (c)** (Appendix A6). `f` is a quasi-monomorphism iff `f^⊤` is a quasi-epimorphism. -/
theorem lemmaA6_1_4_c (f : E →L[𝕜] F) :
    IsQuasiMonomorphism f ↔ IsQuasiEpimorphism (transposeCLM f) := by
  sorry

/-- **Lemma A6.1.4 (d)** (Appendix A6; Schauder's theorem). `f` is compact iff `f^⊤` is compact. -/
theorem lemmaA6_1_4_d (f : E →L[𝕜] F) :
    IsCompactOperator f ↔ IsCompactOperator (transposeCLM f) := by
  sorry

end Operators

/-! ## A6.3 The Cauchy transform and Hölder estimates -/

/-- **Hölder seminorm** `[f]_α = sup_{z₁ ≠ z₂} ‖f z₁ − f z₂‖ / ‖z₁ − z₂‖^α` of a function `ℂ → E` (A6.3.5), valued in
`[0, ∞]`. -/
noncomputable def holderSemi {E : Type*} [NormedAddCommGroup E] (α : ℝ) (f : ℂ → E) : ℝ≥0∞ :=
  ⨆ (z₁ : ℂ) (z₂ : ℂ) (_ : z₁ ≠ z₂), ‖f z₁ - f z₂‖ₑ / ‖z₁ - z₂‖ₑ ^ α

/-- The **sup norm** `‖f‖_0 = sup_z ‖f z‖` (valued in `[0, ∞]`), the book's `α = 0` Hölder "norm" read as the sup norm.
-/
noncomputable def supNorm (f : ℂ → ℂ) : ℝ≥0∞ := ⨆ z, ‖f z‖ₑ

/-- The **Cauchy transform** `(1/πz) ∗ f`, `z ↦ ∫ f(w)/(π (z − w)) dA(w)` (Lebesgue measure on `ℂ`). -/
noncomputable def cauchyTransform (f : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w, f w / (π * (z - w))

/-- **Proposition A6.3.1** (Appendix A6, H2:6195). If `f` has compact support, then `∂̄ ((1/πz) ∗ f) = f`. Regularity is
not stated in the book; for merely continuous `f` the identity holds only in the sense of distributions, so the formal
statement takes `f` of class `C¹` with compact support (classical sense): the Cauchy transform is differentiable and `∂̄
T = ½ (∂_x T + i ∂_y T) = f` pointwise.
Near misses: `LiZhongQC.eq11_17` (`∂_{z̄} T_ω = ω` for `ω ∈ C₀^∞`, with `T = -(1/π)∬ ω(ζ)/(ζ - z)`, the same transform), `LiZhongQC.dzbar_cauchyT`; the hypothesis here is the weaker `C¹` with compact support. -/
theorem propA6_3_1 (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (z : ℂ) :
    DifferentiableAt ℝ (cauchyTransform f) z ∧
      (1 / 2 : ℂ) * (fderiv ℝ (cauchyTransform f) z 1 + Complex.I * fderiv ℝ (cauchyTransform f) z Complex.I) = f z := by
  sorry

/-- **Theorem A6.3.2** (Appendix A6, H2:6243). For `R > 0` and `0 < α < 1` there is a constant `C` such that for every
continuous `f` supported in `{|z| ≤ R}`, `‖(1/πz) ∗ f‖_α ≤ C ‖f‖_0`.
Near miss: `LiZhongQC.lemma11_2` (Hölder continuity of `T_ω` for `ω ∈ L_p`, `p > 2`, with exponent `(p-2)/p`; different hypotheses and constants). -/
theorem thmA6_3_2 {R α : ℝ} (hR : 0 < R) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, Continuous f → (∀ z, R < ‖z‖ → f z = 0) →
      holderSemi α (cauchyTransform f) ≤ C * supNorm f := by
  sorry

/-- **Theorem A6.3.4** (Appendix A6, H3:21). For `0 < α < 1` there is a constant `C` such that for every compactly
supported `α`-Hölder function `f`, the convolution `(1/πz) ∗ f` is `C^{1,α}` and `‖D((1/πz) ∗ f)‖_α ≤ C ‖f‖_α` (the
derivative is the real Fréchet derivative, with the operator norm). -/
theorem thmA6_3_4 {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, HasCompactSupport f → holderSemi α f < ⊤ →
      (∀ z, DifferentiableAt ℝ (cauchyTransform f) z) ∧
        holderSemi α (fun z => fderiv ℝ (cauchyTransform f) z) ≤ C * holderSemi α f := by
  sorry

end Hubbard2006
