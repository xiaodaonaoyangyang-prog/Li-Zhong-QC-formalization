import References.Pommerenke1992.Ch01.S02_ConformalMaps
import LiZhongQC.Lemmas.Koebe
import LiZhongQC.Lemmas.KrausNehari

/-!
# Pommerenke 1992, Ch. 1 §1.3 The Koebe Distortion Theorem

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 495–756.

* Definition (the class `S`, (1.3.1)) — exists: `LiZhongQC.knHyp` (analytic and injective in the unit disc with
  `f(0) = 0`, `f'(0) = 1`)
* Definition (the class `Σ`, (1.3.2); the coefficients `a_n`, `b_n`) — `IsClassSigma`, `sigmaCoeff`, `sCoeff`
* Area theorem ((1.3.6)) — `area_theorem`
* Formula (1.3.9) (Bieberbach, `|a₂| ≤ 2` for `f ∈ S`) — exists: `LiZhongQC.koebe_bieberbach` (the bound
  `|f''(0)| ≤ 4`; a trivial rewriting, as `a₂ = f''(0)/2`)
* Definition (the Koebe function (1.3.10)) — exists: `LiZhongQC.koebeFn`
* Formula (1.3.11) (de Branges' theorem, `|a_n| ≤ n` for `f ∈ S`) — `eq1_3_11`
* Definition (the Koebe transform (1.3.12)) — `koebeTransform`
* Formula (1.3.12) (the Koebe transform belongs to `S`, with its second coefficient) — `eq1_3_12`
* Proposition 1.2 — exists: `LiZhongQC.kb_koebe_transform_ineq` (the same inequality for an analytic injective map of
  the unit disc)
* Theorem 1.3 (Koebe distortion theorem) — `thm1_3`
* Definition (the distance `d_f(z)` to the boundary, (1.3.16)) — `distToBoundary`
* Corollary 1.4 — `cor1_4`
* Corollary 1.5 — `cor1_5`
* Corollary 1.6 — `cor1_6`
* Theorem 1.7 — `thm1_7`

Not items (DESIGN §3):
- the correspondences (1.3.3), (1.3.4) between `S` and `Σ` (not cited);
- the area formula (1.3.5), quoted from Duren (not cited by number);
- the odd function (1.3.7) and the bound (1.3.8) (not cited);
- the sentences "equality holds for the Koebe function" after (1.3.9) and Proposition 1.2 (outside the labelled
  statements);
- the Hardy-space remark after Theorem 1.7 (a forward reference to Theorem 8.2).

**Conventions.**
- "`f` maps `𝔻` conformally into `ℂ`" means `f` is analytic and injective in the unit disc.
- The coefficients are `a_n = f⁽ⁿ⁾(0)/n!` and, for `g ∈ Σ`, `b_n = (2πi)⁻¹ ∮_{|ζ| = 2} g(ζ) ζ^{n-1} dζ`: the
  coefficient of `ζ⁻ⁿ` in the Laurent expansion at `∞`, and `b₀` for `n = 0`.
- `λ` is the non-euclidean metric `hypDistD` of §1.2.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc knHyp)

/-- The Taylor coefficients `a_n = f⁽ⁿ⁾(0)/n!` of a function analytic at `0`, as in (1.3.1). -/
def sCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- **Definition (1.3.2)** (§1.3). The class `Σ`: the functions `g(ζ) = ζ + b₀ + b₁ ζ⁻¹ + …` univalent in
`𝔻* = {|ζ| > 1} ∪ {∞}`.
Modelling: `g` is analytic and injective in `{|ζ| > 1}`, and `g(ζ) - ζ` tends to a finite limit `b₀` as `ζ → ∞`.
This is equivalent to the expansion, as `g(ζ) - ζ` then has a removable singularity at `∞`. -/
def IsClassSigma (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g {ζ | 1 < ‖ζ‖} ∧ InjOn g {ζ | 1 < ‖ζ‖} ∧
    ∃ b₀ : ℂ, Tendsto (fun ζ => g ζ - ζ - b₀) (cocompact ℂ) (𝓝 0)

/-- The coefficients `b_n` of `g ∈ Σ`, (1.3.2): the coefficient of `ζ⁻ⁿ` in the Laurent expansion of `g` at `∞`
(and `b₀` for `n = 0`), computed as `b_n = (2πi)⁻¹ ∮_{|ζ| = 2} g(ζ) ζ^{n-1} dζ` (any radius `> 1` gives the same
value). -/
def sigmaCoeff (g : ℂ → ℂ) (n : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * circleIntegral (fun ζ => g ζ * ζ ^ ((n : ℤ) - 1)) 0 2

/-- **Area theorem (1.3.6)** (§1.3). For `g ∈ Σ`, `|b₁|² ≤ Σ n |b_n|² ≤ 1`; equality holds if and only if
`g(ζ) ≡ ζ + b₀ + b₁ ζ⁻¹` with `|b₁| = 1`.
Modelling: the series is summed in `ℝ≥0∞` (it always has a value there). The equality case is equality throughout
(6), that is `|b₁| = 1`. -/
theorem area_theorem {g : ℂ → ℂ} (hg : IsClassSigma g) :
    (‖sigmaCoeff g 1‖₊ : ℝ≥0∞) ^ 2 ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * (‖sigmaCoeff g (n + 1)‖₊ : ℝ≥0∞) ^ 2 ∧
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * (‖sigmaCoeff g (n + 1)‖₊ : ℝ≥0∞) ^ 2 ≤ 1 ∧
      (‖sigmaCoeff g 1‖ = 1 ↔ ∃ c₀ c₁ : ℂ, ‖c₁‖ = 1 ∧ ∀ ζ : ℂ, 1 < ‖ζ‖ → g ζ = ζ + c₀ + c₁ / ζ) := by
  sorry

/-- **Formula (1.3.11)** (§1.3; cited as (1.3.11); de Branges' theorem, the former Bieberbach conjecture).
`|a_n| ≤ n` for `f ∈ S`, `n = 2, 3, …`. -/
theorem eq1_3_11 {f : ℂ → ℂ} (hf : knHyp f) {n : ℕ} (hn : 2 ≤ n) : ‖sCoeff f n‖ ≤ n := by
  sorry

/-- **Definition (1.3.12)** (§1.3). The Koebe transform of `f` (analytic and univalent in `𝔻`) at `z₀ ∈ 𝔻`:
`h(z) = (f((z + z₀)/(1 + z̄₀ z)) - f(z₀))/((1 - |z₀|²) f'(z₀))`. -/
def koebeTransform (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  (f ((z + z₀) / (1 + conj z₀ * z)) - f z₀) / (((1 - ‖z₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀)

/-- The Koebe transform (1.3.12) of a univalent `f` at `z₀ ∈ 𝔻` is in `S`, with
`h''(0) = (1 - |z₀|²) f''(z₀)/f'(z₀) - 2 z̄₀`, and `h'(ζ) = f'(T ζ) T'(ζ)/((1 - |z₀|²) f'(z₀))` for
`T ζ = (ζ + z₀)/(1 + z̄₀ ζ)` (the computation inside `LiZhongQC.kb_koebe_transform_ineq`). -/
theorem p92_1_koebeT {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {z : ℂ}
    (hz : z ∈ unitDisc) :
    knHyp (koebeTransform f z) ∧
      deriv (deriv (koebeTransform f z)) 0 =
        ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z ∧
      ∀ ζ ∈ unitDisc, HasDerivAt (koebeTransform f z)
        (deriv f ((ζ + z) / (1 + conj z * ζ)) * ((1 - conj z * z) / (1 + conj z * ζ) ^ 2) /
          (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) ζ := by
  have hK : koebeTransform f z = fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z) := rfl
  rw [hK]
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hs_eq : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - conj z * z := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hs0 : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast this
  have hf'z : deriv f z ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj hz
  have hc0 : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z ≠ 0 := mul_ne_zero hs0 hf'z
  have hTmaps := LiZhongQC.kb_d1_mapsTo hz1
  have hTinj := LiZhongQC.kb_d1_injOn hz1
  have hTd : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt (fun ζ => (ζ + z) / (1 + conj z * ζ))
      ((1 - conj z * z) / (1 + conj z * ζ) ^ 2) ζ := fun ζ hζ =>
    LiZhongQC.kb_d1_hasDerivAt_T z ζ (LiZhongQC.kb_d1_denom_ne_zero hz1 (mem_ball_zero_iff.1 hζ))
  have hT0 : ((0 : ℂ) + z) / (1 + conj z * 0) = z := by simp
  have hT'0 : (1 - conj z * z) / (1 + conj z * 0) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs_eq]
    simp
  have hTdiff : DifferentiableOn ℂ (fun ζ => (ζ + z) / (1 + conj z * ζ)) (ball 0 1) :=
    fun ζ hζ => (hTd ζ hζ).differentiableAt.differentiableWithinAt
  have hFd : DifferentiableOn ℂ (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) (ball 0 1) :=
    ((hf.comp hTdiff hTmaps).sub_const (f z)).div_const _
  have hFinj : InjOn (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) (ball 0 1) := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ h
    have h' : f ((ζ₁ + z) / (1 + conj z * ζ₁)) = f ((ζ₂ + z) / (1 + conj z * ζ₂)) := by
      simp only at h
      rw [div_left_inj' hc0] at h
      linear_combination h
    exact hTinj hζ₁ hζ₂ (hinj (hTmaps hζ₁) (hTmaps hζ₂) h')
  have hF0 : (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) 0 = 0 := by simp
  have hFder : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt (fun ζ => (f ((ζ + z) /
      (1 + conj z * ζ)) - f z) / (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z))
      (deriv f ((ζ + z) / (1 + conj z * ζ)) * ((1 - conj z * z) / (1 + conj z * ζ) ^ 2) /
        (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) ζ := by
    intro ζ hζ
    have hfT : HasDerivAt f (deriv f ((ζ + z) / (1 + conj z * ζ))) ((ζ + z) / (1 + conj z * ζ)) :=
      (hf.differentiableAt (isOpen_ball.mem_nhds (hTmaps hζ))).hasDerivAt
    exact ((hfT.comp ζ (hTd ζ hζ)).sub_const (f z)).div_const _
  have hF1 : deriv (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) 0 = 1 := by
    rw [(hFder 0 h0mem).deriv, hT0, hT'0, mul_comm]
    exact div_self hc0
  have hev : deriv (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) =ᶠ[𝓝 0]
      fun ζ => deriv f ((ζ + z) / (1 + conj z * ζ)) * ((1 - conj z * z) / (1 + conj z * ζ) ^ 2) /
        (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z) := by
    filter_upwards [isOpen_ball.mem_nhds h0mem] with ζ hζ
    exact (hFder ζ hζ).deriv
  have hf'd : HasDerivAt (deriv f) (deriv (deriv f) z) (((0 : ℂ) + z) / (1 + conj z * 0)) := by
    rw [hT0]
    exact ((hf.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hG : HasDerivAt (fun ζ => deriv f ((ζ + z) / (1 + conj z * ζ)) *
        ((1 - conj z * z) / (1 + conj z * ζ) ^ 2) / (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z)) _ 0 :=
    ((hf'd.comp (0 : ℂ) (hTd 0 h0mem)).mul (LiZhongQC.kb_d1_hasDerivAt_T' z)).div_const _
  have hF2 : deriv (deriv (fun ζ => (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
      (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z))) 0 =
      ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z := by
    rw [hev.deriv_eq, hG.deriv]
    simp only [Function.comp_apply]
    rw [hT0, hT'0, ← hs_eq]
    field_simp
    ring
  exact ⟨⟨hFd, hFinj, hF0, hF1⟩, hF2, hFder⟩

/-- **Formula (1.3.12)** (§1.3; cited as (1.3.12)). If `f` is analytic and univalent in `𝔻` and `z₀ ∈ 𝔻`, then the
Koebe transform `h = z + (½(1 - |z₀|²) f''(z₀)/f'(z₀) - z̄₀) z² + …` belongs to `S`. -/
theorem eq1_3_12 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {z₀ : ℂ}
    (hz₀ : z₀ ∈ unitDisc) :
    knHyp (koebeTransform f z₀) ∧
      sCoeff (koebeTransform f z₀) 2 =
        1 / 2 * ((1 - ‖z₀‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z₀ / deriv f z₀) - conj z₀ := by
  obtain ⟨hK, h2, -⟩ := p92_1_koebeT hf hinj hz₀
  refine ⟨hK, ?_⟩
  show iteratedDeriv 2 (koebeTransform f z₀) 0 / ((Nat.factorial 2 : ℕ) : ℂ) = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, h2]
  norm_num
  ring

/-- Pointwise radial estimate, lower half (the mirror of `LiZhongQC.kb_d2_re_bound`): if `w = s z` with `0 ≤ s`,
`s‖z‖ < 1` and `‖(1 - ‖w‖²) a/b - 2 w̄‖ ≤ 4`, then `Re(a/b · z) ≥ -(‖z‖/(1 - s‖z‖) + 3‖z‖/(1 + s‖z‖))`. -/
theorem p92_1_re_lower {a b z : ℂ} {s : ℝ} (hs : 0 ≤ s) (hsr : s * ‖z‖ < 1)
    (h : ‖((1 - ‖(s : ℂ) * z‖ ^ 2 : ℝ) : ℂ) * a / b - 2 * conj ((s : ℂ) * z)‖ ≤ 4) :
    -(‖z‖ / (1 - s * ‖z‖) + 3 * ‖z‖ / (1 + s * ‖z‖)) ≤ (a / b * z).re := by
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hw : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hs]
  rw [hw, mul_div_assoc] at h
  have hr2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * conj ((s : ℂ) * z))).re
      = (1 - (s * ‖z‖) ^ 2) * (a / b * z).re - 2 * s * ‖z‖ ^ 2 := by
    rw [hr2]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hle : -(‖z‖ * 4) ≤
      (z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * conj ((s : ℂ) * z))).re := by
    have h1 := (abs_le.1 (Complex.abs_re_le_norm
      (z * (((1 - (s * ‖z‖) ^ 2 : ℝ) : ℂ) * (a / b) - 2 * conj ((s : ℂ) * z))))).1
    rw [norm_mul] at h1
    nlinarith [mul_le_mul_of_nonneg_left h hr0]
  have h1 : 0 < 1 + s * ‖z‖ := by have := mul_nonneg hs hr0; linarith
  have h2 : 0 < 1 - s * ‖z‖ := by linarith
  have key : (1 - (s * ‖z‖) ^ 2) * (a / b * z).re ≥ 2 * s * ‖z‖ ^ 2 - 4 * ‖z‖ := by linarith
  have e : ‖z‖ / (1 - s * ‖z‖) + 3 * ‖z‖ / (1 + s * ‖z‖) =
      (4 * ‖z‖ - 2 * s * ‖z‖ ^ 2) / ((1 - s * ‖z‖) * (1 + s * ‖z‖)) := by
    rw [div_add_div _ _ h2.ne' h1.ne']
    congr 1
    ring
  have hDe : (1 - s * ‖z‖) * (1 + s * ‖z‖) = 1 - (s * ‖z‖) ^ 2 := by ring
  rw [e, neg_le, le_div_iff₀ (mul_pos h2 h1), hDe]
  linarith

/-- Radial integration, lower half (the mirror of `LiZhongQC.kb_d2_deriv_bound`):
`(1 - s‖z‖)/(1 + s‖z‖)³ ≤ ‖f'(s z)‖` for `s ∈ [0,1]`. -/
theorem p92_1_deriv_lower {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h1 : deriv f 0 = 1) (hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hineq : ∀ z ∈ ball (0 : ℂ) 1,
      ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z‖ ≤ 4)
    {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - s * ‖z‖) / (1 + s * ‖z‖) ^ 3 ≤ ‖deriv f ((s : ℂ) * z)‖ := by
  obtain ⟨G, hGd, hGe⟩ := LiZhongQC.kb_d2_log_deriv hf hne
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hsr : ∀ t ∈ Icc (0 : ℝ) 1, t * ‖z‖ < 1 := fun t ht => by
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 hr0
      _ < 1 := by rw [one_mul]; exact hz
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ ball (0 : ℂ) 1 := fun t ht => by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_of_nonneg ht.1]
    exact hsr t ht
  have hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (G ((t : ℂ) * z)).re)
      ((deriv (deriv f) ((t : ℂ) * z) / deriv f ((t : ℂ) * z) * z).re) t := fun t ht =>
    ((hGd _ (hmem t ht)).comp (t : ℂ) (hasDerivAt_mul_const z)).real_of_complex
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => Real.log (1 - t * ‖z‖) - 3 * Real.log (1 + t * ‖z‖))
      (-(‖z‖ / (1 - t * ‖z‖) + 3 * ‖z‖ / (1 + t * ‖z‖))) t := by
    intro t ht
    have ha : 0 < 1 + t * ‖z‖ := by have := mul_nonneg ht.1 hr0; linarith
    have hb : 0 < 1 - t * ‖z‖ := by linarith [hsr t ht]
    have d1 : HasDerivAt (fun t : ℝ => 1 - t * ‖z‖) (-‖z‖) t :=
      (hasDerivAt_mul_const ‖z‖).const_sub 1
    have d2 : HasDerivAt (fun t : ℝ => 1 + t * ‖z‖) ‖z‖ t :=
      (hasDerivAt_mul_const ‖z‖).const_add 1
    have := (d1.log hb.ne').fun_sub ((d2.log ha.ne').const_mul 3)
    convert this using 1
    ring
  have hG0 : (G 0).re = 0 := by
    have e := hGe 0 (mem_ball_self one_pos)
    rw [h1] at e
    have hn := congrArg (fun w : ℂ => ‖w‖) e
    simp only [Complex.norm_exp, norm_one] at hn
    exact Real.exp_eq_one_iff _ |>.1 hn
  have hstart : (fun t : ℝ => Real.log (1 - t * ‖z‖) - 3 * Real.log (1 + t * ‖z‖)) 0 ≤
      (fun t : ℝ => (G ((t : ℂ) * z)).re) 0 := by
    simp [hG0]
  have hfence := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun t : ℝ => Real.log (1 - t * ‖z‖) - 3 * Real.log (1 + t * ‖z‖))
    (f' := fun t => -(‖z‖ / (1 - t * ‖z‖) + 3 * ‖z‖ / (1 + t * ‖z‖)))
    (B := fun t : ℝ => (G ((t : ℂ) * z)).re)
    (B' := fun t => (deriv (deriv f) ((t : ℂ) * z) / deriv f ((t : ℂ) * z) * z).re)
    (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hstart
    (fun t ht => (hu t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => p92_1_re_lower (Ico_subset_Icc_self ht).1 (hsr t (Ico_subset_Icc_self ht))
      (hineq _ (hmem t (Ico_subset_Icc_self ht))))
  have hus := hfence hs
  have ha : 0 < 1 + s * ‖z‖ := by have := mul_nonneg hs.1 hr0; linarith
  have hb : 0 < 1 - s * ‖z‖ := by linarith [hsr s hs]
  have hexp : Real.exp (Real.log (1 - s * ‖z‖) - 3 * Real.log (1 + s * ‖z‖))
      = (1 - s * ‖z‖) / (1 + s * ‖z‖) ^ 3 := by
    have e3 : 3 * Real.log (1 + s * ‖z‖) = Real.log ((1 + s * ‖z‖) ^ 3) := by
      rw [Real.log_pow]; norm_num
    rw [Real.exp_sub, e3, Real.exp_log hb, Real.exp_log (pow_pos ha 3)]
  calc (1 - s * ‖z‖) / (1 + s * ‖z‖) ^ 3
      = Real.exp (Real.log (1 - s * ‖z‖) - 3 * Real.log (1 + s * ‖z‖)) := hexp.symm
    _ ≤ Real.exp (G ((s : ℂ) * z)).re := Real.exp_le_exp.2 hus
    _ = ‖deriv f ((s : ℂ) * z)‖ := by rw [← hGe _ (hmem s hs), Complex.norm_exp]

/-- The norm of a curve has a derivative bounded by the speed where the curve does not vanish. -/
theorem p92_1_hasDerivAt_norm {γ : ℝ → ℂ} {γ' : ℂ} {t : ℝ} (h : HasDerivAt γ γ' t) (h0 : γ t ≠ 0) :
    ∃ d : ℝ, HasDerivAt (fun s => ‖γ s‖) d t ∧ d ≤ ‖γ'‖ := by
  have hs := h.norm_sq
  have hpos : 0 < ‖γ t‖ := norm_pos_iff.2 h0
  have hsq := hs.sqrt (by positivity)
  have e : (fun y => √(‖γ y‖ ^ 2)) = fun s => ‖γ s‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg _)
  rw [e] at hsq
  refine ⟨_, hsq, ?_⟩
  rw [Real.sqrt_sq (norm_nonneg _), div_le_iff₀ (by positivity)]
  have := real_inner_le_norm (γ t) γ'
  nlinarith [norm_nonneg γ']

/-- The lower growth bound of (1.3.14) for normalized `g` (`g(0) = 0`, `g'(0) = 1`): `|z|/(1 + |z|)² ≤ |g(z)|`.
If `|g(z)| < 1/4`, the segment `[0, g(z)]` lies in `g(𝔻)` (`LiZhongQC.koebe_quarter`); along its preimage `γ`,
`Φ(|γ|)`, `Φ(ρ) = ρ/(1 + ρ)²`, grows at most at the speed `|g(z)|` (`p92_1_deriv_lower`). -/
theorem p92_1_growth_lower {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hinj : InjOn g unitDisc)
    (h0 : g 0 = 0) (h1 : deriv g 0 = 1) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖g z‖ := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hq : ‖z‖ / (1 + ‖z‖) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (1 - ‖z‖)]
  by_cases hw : 1 / 4 ≤ ‖g z‖
  · linarith
  have hw' : ‖g z‖ < 1 / 4 := not_le.1 hw
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  by_cases hw0 : g z = 0
  · have : z = 0 := hinj hz h0D (by rw [hw0, h0])
    rw [this, norm_zero, zero_div]
    exact norm_nonneg _
  set w := g z with hwdef
  have hne : ∀ ζ ∈ ball (0 : ℂ) 1, deriv g ζ ≠ 0 := fun ζ hζ =>
    LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hg hinj hζ
  have hineq := fun ζ (hζ : ζ ∈ ball (0 : ℂ) 1) => LiZhongQC.kb_koebe_transform_ineq hg hinj hζ
  have hconf : LiZhongQC.IsConformalOnto g unitDisc (g '' unitDisc) := ⟨hg, hinj, rfl⟩
  obtain ⟨-, -, hright, hleft, hder⟩ := p92_1_inverse hconf
  set h := Function.invFunOn g unitDisc with hhdef
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * w ∈ g '' unitDisc := by
    intro t ht
    apply LiZhongQC.koebe_quarter hg hinj h0 h1
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_of_nonneg ht.1]
    nlinarith [ht.2, norm_nonneg w]
  have hhmem : ∀ t ∈ Icc (0 : ℝ) 1, h ((t : ℂ) * w) ∈ unitDisc := fun t ht => by
    obtain ⟨ζ, hζ, hζe⟩ := hseg t ht
    rw [← hζe, hleft ζ hζ]
    exact hζ
  have hgh : ∀ t ∈ Icc (0 : ℝ) 1, g (h ((t : ℂ) * w)) = (t : ℂ) * w := fun t ht =>
    hright _ (hseg t ht)
  -- the preimage curve `γ(t) = h(t w)` and its derivative `w / g'(γ t)`
  have hγd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => h ((t : ℂ) * w))
      ((deriv g (h ((t : ℂ) * w)))⁻¹ * w) t := by
    intro t ht
    have hd := hder _ (hhmem t ht)
    rw [hgh t ht] at hd
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const w
    exact hd.comp t hlin
  have hγ0 : ∀ t ∈ Ioo (0 : ℝ) 1, h ((t : ℂ) * w) ≠ 0 := by
    intro t ht hc
    have := hgh t (Ioo_subset_Icc_self ht)
    rw [hc, h0] at this
    rcases mul_eq_zero.1 this.symm with h' | h'
    · exact ht.1.ne' (by exact_mod_cast h')
    · exact hw0 h'
  -- `Φ(ρ) = ρ/(1 + ρ)²` with `Φ'(ρ) = (1 - ρ)/(1 + ρ)³`
  have hΦ : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun x : ℝ => x / (1 + x) ^ 2) ((1 - x) / (1 + x) ^ 3) x := by
    intro x hx
    have hd : (1 + x) ^ 2 ≠ 0 := by positivity
    have h₁ : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
    have h₂ : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + x)) x := by
      convert ((hasDerivAt_id' x).const_add 1).pow 2 using 1
      norm_num
    have h₃ := h₁.div h₂ hd
    convert h₃ using 1
    field_simp
    ring
  set F : ℝ → ℝ := fun t => ‖h ((t : ℂ) * w)‖ / (1 + ‖h ((t : ℂ) * w)‖) ^ 2 with hF
  have hFd : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt F d t ∧ d ≤ ‖w‖ := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    obtain ⟨d, hd, hdle⟩ := p92_1_hasDerivAt_norm (hγd t htI) (hγ0 t ht)
    set ρ := ‖h ((t : ℂ) * w)‖ with hρ
    have hρ1 : ρ < 1 := mem_ball_zero_iff.1 (hhmem t htI)
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hcomp := (hΦ ρ hρ0).comp t hd
    refine ⟨(1 - ρ) / (1 + ρ) ^ 3 * d, hcomp, ?_⟩
    have hg' : (1 - ρ) / (1 + ρ) ^ 3 ≤ ‖deriv g (h ((t : ℂ) * w))‖ := by
      have := p92_1_deriv_lower hg h1 hne hineq hρ1 (s := 1) ⟨zero_le_one, le_rfl⟩
      simpa using this
    have hsp : ‖(deriv g (h ((t : ℂ) * w)))⁻¹ * w‖ = ‖w‖ / ‖deriv g (h ((t : ℂ) * w))‖ := by
      rw [norm_mul, norm_inv]
      ring
    rw [hsp] at hdle
    have hgpos : 0 < ‖deriv g (h ((t : ℂ) * w))‖ := norm_pos_iff.2 (hne _ (hhmem t htI))
    have hΦ0 : 0 ≤ (1 - ρ) / (1 + ρ) ^ 3 := div_nonneg (by linarith) (by positivity)
    calc (1 - ρ) / (1 + ρ) ^ 3 * d ≤ (1 - ρ) / (1 + ρ) ^ 3 * (‖w‖ / ‖deriv g (h ((t : ℂ) * w))‖) :=
          mul_le_mul_of_nonneg_left hdle hΦ0
      _ ≤ ‖deriv g (h ((t : ℂ) * w))‖ * (‖w‖ / ‖deriv g (h ((t : ℂ) * w))‖) :=
          mul_le_mul_of_nonneg_right hg' (by positivity)
      _ = ‖w‖ := by field_simp
  have hFc : ContinuousOn F (Icc 0 1) := fun t ht => by
    have hc := (hγd t ht).continuousAt.norm
    have hpos : (1 + ‖h ((t : ℂ) * w)‖) ^ 2 ≠ 0 := by positivity
    exact (hc.div ((continuousAt_const.add hc).pow 2) hpos).continuousWithinAt
  have hmvt := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hFc
    (fun t ht => by
      rw [interior_Icc] at ht
      obtain ⟨d, hd, -⟩ := hFd t ht
      exact hd.differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      obtain ⟨d, hd, hdle⟩ := hFd t ht
      rw [hd.deriv]
      exact hdle)
    0 (left_mem_Icc.2 zero_le_one) 1 (right_mem_Icc.2 zero_le_one) zero_le_one
  have hF1 : F 1 = ‖z‖ / (1 + ‖z‖) ^ 2 := by
    simp only [hF, Complex.ofReal_one, one_mul, hwdef]
    rw [hleft z hz]
  have hF0 : F 0 = 0 := by
    simp only [hF, Complex.ofReal_zero, zero_mul]
    rw [← h0, hleft 0 h0D, norm_zero, zero_div]
  rw [hF1, hF0] at hmvt
  linarith

/-- **Theorem 1.3** (§1.3; the Koebe distortion theorem). If `f` maps `𝔻` conformally into `ℂ` and `z ∈ 𝔻`, then
(1.3.14) `|f'(0)| |z|/(1 + |z|)² ≤ |f(z) - f(0)| ≤ |f'(0)| |z|/(1 - |z|)²` and (1.3.15)
`|f'(0)| (1 - |z|)/(1 + |z|)³ ≤ |f'(z)| ≤ |f'(0)| (1 + |z|)/(1 - |z|)³`. -/
theorem thm1_3 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖deriv f 0‖ * ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖f z - f 0‖ ∧ ‖f z - f 0‖ ≤ ‖deriv f 0‖ * ‖z‖ / (1 - ‖z‖) ^ 2 ∧
      ‖deriv f 0‖ * (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ ‖deriv f 0‖ * (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  -- normalization `g = (f - f(0))/f'(0) ∈ S`
  have hψd : DifferentiableOn ℂ (fun w => f w - f 0) unitDisc := hf.sub_const _
  have hψi : InjOn (fun w => f w - f 0) unitDisc := fun a ha b hb h =>
    hinj ha hb (sub_left_inj.1 h)
  have hψ0 : (fun w => f w - f 0) 0 = 0 := sub_self _
  have hdψ : ∀ w, deriv (fun w => f w - f 0) w = deriv f w := fun w => deriv_sub_const _
  obtain ⟨ha, hgd, hgi, hg0, hg1⟩ := LiZhongQC.kb_ka_normalize hψd hψi hψ0
  rw [hdψ] at ha hgd hgi hg0 hg1
  have hf0 : 0 < ‖deriv f 0‖ := norm_pos_iff.2 ha
  have hne : ∀ ζ ∈ ball (0 : ℂ) 1, deriv (fun w => (f w - f 0) / deriv f 0) ζ ≠ 0 := fun ζ hζ =>
    LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hgd hgi hζ
  have hineq := fun ζ (hζ : ζ ∈ ball (0 : ℂ) 1) => LiZhongQC.kb_koebe_transform_ineq hgd hgi hζ
  have hdg : deriv (fun w => (f w - f 0) / deriv f 0) z = deriv f z / deriv f 0 := by
    rw [deriv_div_const, hdψ]
  have hlow := p92_1_growth_lower hgd hgi hg0 hg1 hz
  have hup := LiZhongQC.koebe_growth_scaled hψd hψi hψ0 hz1
  rw [hdψ] at hup
  have hdlow := p92_1_deriv_lower hgd hg1 hne hineq hz1 (s := 1) ⟨zero_le_one, le_rfl⟩
  have hdup := LiZhongQC.kb_d2_deriv_bound hgd hg1 hne hineq hz1 (s := 1) ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, one_mul] at hdlow hdup
  rw [hdg, norm_div] at hdlow hdup
  simp only [norm_div] at hlow
  refine ⟨?_, hup, ?_, ?_⟩
  · rw [le_div_iff₀ hf0] at hlow
    calc ‖deriv f 0‖ * ‖z‖ / (1 + ‖z‖) ^ 2 = ‖z‖ / (1 + ‖z‖) ^ 2 * ‖deriv f 0‖ := by ring
      _ ≤ ‖f z - f 0‖ := hlow
  · rw [le_div_iff₀ hf0] at hdlow
    calc ‖deriv f 0‖ * (1 - ‖z‖) / (1 + ‖z‖) ^ 3 = (1 - ‖z‖) / (1 + ‖z‖) ^ 3 * ‖deriv f 0‖ := by ring
      _ ≤ ‖deriv f z‖ := hdlow
  · rw [div_le_iff₀ hf0] at hdup
    calc ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 * ‖deriv f 0‖ := hdup
      _ = ‖deriv f 0‖ * (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by ring

/-- **Definition (1.3.16)** (§1.3). The distance to the boundary `d_f(z) = dist(f(z), ∂f(𝔻))`, `z ∈ 𝔻`, for a
conformal map `f` of `𝔻` into `ℂ` (the boundary is nonempty, as `f(𝔻) ≠ ℂ`). -/
def distToBoundary (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  infDist (f z) (frontier (f '' unitDisc))

/-- **Corollary 1.4** (§1.3; (1.3.17), cited). If `f` maps `𝔻` conformally into `ℂ`, then
`¼ (1 - |z|²)|f'(z)| ≤ d_f(z) ≤ (1 - |z|²)|f'(z)|` for `z ∈ 𝔻`. -/
theorem cor1_4 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {z : ℂ}
    (hz : z ∈ unitDisc) :
    1 / 4 * (1 - ‖z‖ ^ 2) * ‖deriv f z‖ ≤ distToBoundary f z ∧
      distToBoundary f z ≤ (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hdef : distToBoundary f z = infDist (f z) (frontier (f '' unitDisc)) := rfl
  rw [hdef]
  have hconf : LiZhongQC.IsConformalOnto f unitDisc (f '' unitDisc) := ⟨hf, hinj, rfl⟩
  obtain ⟨hhd, hhb, -, hleft, hder⟩ := p92_1_inverse hconf
  have hVo : IsOpen (f '' unitDisc) := hconf.isOpen isOpen_ball
  have hfz : f z ∈ f '' unitDisc := mem_image_of_mem f hz
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hhalf : (1 / 2 : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.2 ?_
    norm_num
  -- `f(𝔻) ≠ ℂ`: otherwise the inverse is a bounded entire function (Liouville)
  have hVne : f '' unitDisc ≠ univ := by
    intro hV
    have hmem : ∀ w : ℂ, w ∈ f '' unitDisc := fun w => hV ▸ mem_univ w
    have hdiff : Differentiable ℂ (Function.invFunOn f unitDisc) := fun w =>
      (hhd w (hmem w)).differentiableAt (hVo.mem_nhds (hmem w))
    have hbdd : Bornology.IsBounded (range (Function.invFunOn f unitDisc)) :=
      isBounded_ball.subset (range_subset_iff.2 fun w => hhb.mapsTo (hmem w))
    have := hdiff.apply_eq_apply_of_bounded hbdd (f 0) (f (1 / 2))
    rw [hleft 0 h0D, hleft (1 / 2) hhalf] at this
    norm_num at this
  have hfr : (frontier (f '' unitDisc)).Nonempty := nonempty_frontier_iff.2 ⟨⟨f z, hfz⟩, hVne⟩
  have hfrV : ∀ w ∈ frontier (f '' unitDisc), w ∉ f '' unitDisc := fun w hw hwV =>
    hw.2 (by rwa [hVo.interior_eq])
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hf'z : deriv f z ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj hz
  have hc : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpos.ne') hf'z
  have hcn : ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z‖ = (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  constructor
  · -- Koebe 1/4 for the Koebe transform, which omits `(w - f(z))/c` for `w ∈ ∂f(𝔻)`
    rw [le_infDist hfr]
    intro w hw
    obtain ⟨hK, -, -⟩ := p92_1_koebeT hf hinj hz
    have homit : (w - f z) / (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z) ∉ koebeTransform f z '' ball (0 : ℂ) 1 := by
      rintro ⟨ζ, hζ, heq⟩
      apply hfrV w hw
      refine ⟨_, LiZhongQC.kb_d1_mapsTo hz1 hζ, ?_⟩
      have h' : koebeTransform f z ζ = (f ((ζ + z) / (1 + conj z * ζ)) - f z) /
          (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv f z) := rfl
      rw [h', div_left_inj' hc] at heq
      linear_combination heq
    have hq := LiZhongQC.koebe_quarter_of_not_mem hK.diff hK.inj hK.zero homit
    rw [hK.one, norm_one, norm_div, hcn] at hq
    have hpos' : 0 < (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := mul_pos hpos (norm_pos_iff.2 hf'z)
    rw [mul_div_assoc', le_div_iff₀ hpos'] at hq
    rw [dist_comm, dist_eq_norm]
    linarith
  · -- Schwarz's lemma for `M_z ∘ f⁻¹` on the disc `B(f(z), d) ⊆ f(𝔻)`
    rcases eq_or_lt_of_le (infDist_nonneg : 0 ≤ infDist (f z) (frontier (f '' unitDisc))) with hd0 | hdpos
    · rw [← hd0]
      positivity
    have hball : ball (f z) (infDist (f z) (frontier (f '' unitDisc))) ⊆ f '' unitDisc := by
      refine (isPreconnected_ball).subset_of_closure_inter_subset hVo ⟨f z, mem_ball_self hdpos, hfz⟩ ?_
      rintro y ⟨hyc, hyb⟩
      by_contra hyV
      have hyfr : y ∈ frontier (f '' unitDisc) := ⟨hyc, by rwa [hVo.interior_eq]⟩
      have h1 := infDist_le_dist_of_mem (x := f z) hyfr
      rw [mem_ball, dist_comm] at hyb
      linarith
    have hφd : DifferentiableOn ℂ (fun y => LiZhongQC.blaschke z (Function.invFunOn f unitDisc y))
        (ball (f z) (infDist (f z) (frontier (f '' unitDisc)))) :=
      (LiZhongQC.differentiableOn_blaschke hz1).comp (hhd.mono hball) fun y hy => hhb.mapsTo (hball hy)
    have hφz : LiZhongQC.blaschke z (Function.invFunOn f unitDisc (f z)) = 0 := by
      rw [hleft z hz, LiZhongQC.blaschke_self]
    have hφmaps : MapsTo (fun y => LiZhongQC.blaschke z (Function.invFunOn f unitDisc y))
        (ball (f z) (infDist (f z) (frontier (f '' unitDisc))))
        (closedBall ((fun y => LiZhongQC.blaschke z (Function.invFunOn f unitDisc y)) (f z)) 1) := by
      intro y hy
      simp only [hφz]
      exact mem_closedBall_zero_iff.2
        (LiZhongQC.blaschke_mem_unitDisc hz1 (mem_ball_zero_iff.1 (hhb.mapsTo (hball hy)))).le
    have hS := Complex.norm_deriv_le_div_of_mapsTo_ball hφd hφmaps hdpos
    have hB : HasDerivAt (LiZhongQC.blaschke z) ((1 - z * conj z) / (1 - conj z * z) ^ 2)
        (Function.invFunOn f unitDisc (f z)) := by
      rw [hleft z hz]
      exact LiZhongQC.hasDerivAt_blaschke hz1 hz1
    have hφder := hB.comp (f z) (hder z hz)
    rw [show (LiZhongQC.blaschke z ∘ Function.invFunOn f unitDisc) =
      fun y => LiZhongQC.blaschke z (Function.invFunOn f unitDisc y) from rfl] at hφder
    rw [hφder.deriv] at hS
    have e : (1 : ℂ) - z * conj z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hval : ‖(1 - z * conj z) / (1 - conj z * z) ^ 2 * (deriv f z)⁻¹‖ =
        1 / ((1 - ‖z‖ ^ 2) * ‖deriv f z‖) := by
      rw [show conj z * z = z * conj z from mul_comm _ _, e, norm_mul, norm_div, norm_pow, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp
    rw [hval] at hS
    have hpos' : 0 < (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := mul_pos hpos (norm_pos_iff.2 hf'z)
    rw [div_le_div_iff₀ hpos' hdpos, one_mul, one_mul] at hS
    exact hS

/-- With `ρ = |M_{z₀}(z₁)| = |z₁ - z₀|/|1 - z̄₀ z₁|` and `λ = λ(z₀, z₁)` (1.2.8): `e^{2λ} = (1 + ρ)/(1 - ρ)` and
`tanh λ = ρ`. -/
theorem p92_1_hyp_exp {z₀ z₁ : ℂ} (h₀ : z₀ ∈ unitDisc) (h₁ : z₁ ∈ unitDisc) :
    Real.exp (2 * hypDistD z₀ z₁) = (1 + ‖LiZhongQC.blaschke z₀ z₁‖) / (1 - ‖LiZhongQC.blaschke z₀ z₁‖) ∧
      Real.tanh (hypDistD z₀ z₁) = ‖LiZhongQC.blaschke z₀ z₁‖ := by
  have hρ1 : ‖LiZhongQC.blaschke z₀ z₁‖ < 1 :=
    LiZhongQC.blaschke_mem_unitDisc (mem_ball_zero_iff.1 h₀) (mem_ball_zero_iff.1 h₁)
  have hρ0 := norm_nonneg (LiZhongQC.blaschke z₀ z₁)
  have hratio : ‖z₀ - z₁‖ / ‖1 - conj z₀ * z₁‖ = ‖LiZhongQC.blaschke z₀ z₁‖ := by
    rw [LiZhongQC.blaschke, norm_div, norm_sub_rev]
  have hlam := eq1_2_8 h₀ h₁
  rw [hratio] at hlam
  set ρ := ‖LiZhongQC.blaschke z₀ z₁‖ with hρ
  have hX : 0 < (1 + ρ) / (1 - ρ) := div_pos (by linarith) (by linarith)
  have h2 : Real.exp (2 * hypDistD z₀ z₁) = (1 + ρ) / (1 - ρ) := by
    rw [hlam, show 2 * (1 / 2 * Real.log ((1 + ρ) / (1 - ρ))) = Real.log ((1 + ρ) / (1 - ρ)) by ring,
      Real.exp_log hX]
  refine ⟨h2, ?_⟩
  set E := Real.exp (hypDistD z₀ z₁) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : E ^ 2 = (1 + ρ) / (1 - ρ) := by
    rw [hE, ← Real.exp_nat_mul, ← h2]
    norm_num
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← hE]
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := by linarith
  have key : (E - E⁻¹) / 2 / ((E + E⁻¹) / 2) = (E ^ 2 - 1) / (E ^ 2 + 1) := by
    field_simp
  rw [key, hE2]
  field_simp
  ring

/-- **Corollary 1.5** (§1.3; (1.3.18), cited). If `f` is a conformal map of `𝔻` into `ℂ` and `z₀, z₁ ∈ 𝔻`, then
(1.3.18) `tanh λ(z₀, z₁)/4 ≤ |f(z₁) - f(z₀)|/((1 - |z₀|²)|f'(z₀)|) ≤ exp[4 λ(z₀, z₁)]` and (1.3.19)
`|f'(z₀)| exp[-6 λ(z₀, z₁)] ≤ |f'(z₁)| ≤ |f'(z₀)| exp[6 λ(z₀, z₁)]`. -/
theorem cor1_5 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {z₀ z₁ : ℂ}
    (h₀ : z₀ ∈ unitDisc) (h₁ : z₁ ∈ unitDisc) :
    Real.tanh (hypDistD z₀ z₁) / 4 ≤ ‖f z₁ - f z₀‖ / ((1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖) ∧
      ‖f z₁ - f z₀‖ / ((1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖) ≤ Real.exp (4 * hypDistD z₀ z₁) ∧
      ‖deriv f z₀‖ * Real.exp (-(6 * hypDistD z₀ z₁)) ≤ ‖deriv f z₁‖ ∧
      ‖deriv f z₁‖ ≤ ‖deriv f z₀‖ * Real.exp (6 * hypDistD z₀ z₁) := by
  obtain ⟨hexp2, htanh⟩ := p92_1_hyp_exp h₀ h₁
  have hz₀1 : ‖z₀‖ < 1 := mem_ball_zero_iff.1 h₀
  have hz₁1 : ‖z₁‖ < 1 := mem_ball_zero_iff.1 h₁
  set ζ := LiZhongQC.blaschke z₀ z₁ with hζ
  have hζD : ζ ∈ unitDisc := mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc hz₀1 hz₁1)
  have hρ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζD
  have hρ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  set ρ := ‖ζ‖ with hρ
  -- `T ζ = z₁` for the disc automorphism `T u = (u + z₀)/(1 + z̄₀ u)` of the Koebe transform
  have hT : (ζ + z₀) / (1 + conj z₀ * ζ) = z₁ := by
    rw [hζ]
    have := LiZhongQC.blaschke_neg_blaschke hz₀1 hz₁1
    simpa [LiZhongQC.blaschke, sub_neg_eq_add, map_neg] using this
  obtain ⟨hK, -, hKd⟩ := p92_1_koebeT hf hinj h₀
  have hpos : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith [norm_nonneg z₀]
  have hf'0 : deriv f z₀ ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj h₀
  have hfpos : 0 < ‖deriv f z₀‖ := norm_pos_iff.2 hf'0
  have hcn : ‖((1 - ‖z₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀‖ = (1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  -- the value and the derivative of the Koebe transform at `ζ`
  have hKval : ‖koebeTransform f z₀ ζ‖ = ‖f z₁ - f z₀‖ / ((1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖) := by
    have h' : koebeTransform f z₀ ζ = (f ((ζ + z₀) / (1 + conj z₀ * ζ)) - f z₀) /
        (((1 - ‖z₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀) := rfl
    rw [h', hT, norm_div, hcn]
  have hs_eq : (1 : ℂ) - conj z₀ * z₀ = ((1 - ‖z₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hN0 : (1 : ℂ) + conj z₀ * ζ ≠ 0 := LiZhongQC.kb_d1_denom_ne_zero hz₀1 hρ1
  have hNpos : 0 < ‖(1 : ℂ) + conj z₀ * ζ‖ := norm_pos_iff.2 hN0
  have hKder : ‖deriv (koebeTransform f z₀) ζ‖ =
      ‖deriv f z₁‖ / (‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 * ‖deriv f z₀‖) := by
    rw [(hKd ζ hζD).deriv, hT, hs_eq, norm_div, norm_mul, norm_div, hcn, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
    field_simp
  -- `1 - ρ ≤ |1 + z̄₀ ζ| ≤ 1 + ρ`
  have hNle : ‖(1 : ℂ) + conj z₀ * ζ‖ ≤ 1 + ρ := by
    calc ‖(1 : ℂ) + conj z₀ * ζ‖ ≤ ‖(1 : ℂ)‖ + ‖conj z₀ * ζ‖ := norm_add_le _ _
      _ = 1 + ‖z₀‖ * ρ := by rw [norm_one, norm_mul, Complex.norm_conj]
      _ ≤ 1 + ρ := by nlinarith [norm_nonneg z₀]
  have hNge : 1 - ρ ≤ ‖(1 : ℂ) + conj z₀ * ζ‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖conj z₀ * ζ‖ ≤ ‖(1 : ℂ) + conj z₀ * ζ‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(conj z₀ * ζ))
      simpa [sub_neg_eq_add, norm_neg] using this
    rw [norm_one, norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg z₀]
  -- Theorem 1.3 for the Koebe transform at `ζ`
  obtain ⟨t1, t2, t3, t4⟩ := thm1_3 hK.diff hK.inj hζD
  simp only [hK.one, hK.zero, norm_one, sub_zero, one_mul] at t1 t2 t3 t4
  rw [hKval] at t1 t2
  rw [hKder] at t3 t4
  set Q := ‖f z₁ - f z₀‖ / ((1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖) with hQ
  have h1ρ : 0 < 1 - ρ := by linarith
  have h1ρ' : 0 < 1 + ρ := by linarith
  have hX : Real.exp (2 * hypDistD z₀ z₁) = (1 + ρ) / (1 - ρ) := hexp2
  have e4 : Real.exp (4 * hypDistD z₀ z₁) = ((1 + ρ) / (1 - ρ)) ^ 2 := by
    rw [← hX, ← Real.exp_nat_mul]
    ring_nf
  have e6 : Real.exp (6 * hypDistD z₀ z₁) = ((1 + ρ) / (1 - ρ)) ^ 3 := by
    rw [← hX, ← Real.exp_nat_mul]
    ring_nf
  have e6' : Real.exp (-(6 * hypDistD z₀ z₁)) = ((1 - ρ) / (1 + ρ)) ^ 3 := by
    rw [Real.exp_neg, e6, ← inv_pow, inv_div]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htanh]
    refine le_trans ?_ t1
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_nonneg hρ0 (mul_nonneg h1ρ.le (by linarith : (0 : ℝ) ≤ 3 + ρ))]
  · refine le_trans t2 ?_
    rw [e4, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (1 - ρ)) (by nlinarith : (0 : ℝ) ≤ (1 + ρ) ^ 2 - ρ)]
  · rw [e6']
    have hden : 0 < ‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 * ‖deriv f z₀‖ := by positivity
    rw [le_div_iff₀ hden] at t3
    have hN2 : (1 - ρ) ^ 2 ≤ ‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 := pow_le_pow_left₀ h1ρ.le hNge 2
    have hA : 0 ≤ (1 - ρ) / (1 + ρ) ^ 3 := by positivity
    calc ‖deriv f z₀‖ * ((1 - ρ) / (1 + ρ)) ^ 3 = (1 - ρ) / (1 + ρ) ^ 3 * ((1 - ρ) ^ 2 * ‖deriv f z₀‖) := by
          field_simp
      _ ≤ (1 - ρ) / (1 + ρ) ^ 3 * (‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 * ‖deriv f z₀‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN2 hfpos.le) hA
      _ ≤ ‖deriv f z₁‖ := by linarith
  · rw [e6]
    have hden : 0 < ‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 * ‖deriv f z₀‖ := by positivity
    rw [div_le_iff₀ hden] at t4
    have hN2 : ‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 ≤ (1 + ρ) ^ 2 := pow_le_pow_left₀ hNpos.le hNle 2
    have hA : 0 ≤ (1 + ρ) / (1 - ρ) ^ 3 := by positivity
    calc ‖deriv f z₁‖ ≤ (1 + ρ) / (1 - ρ) ^ 3 * (‖(1 : ℂ) + conj z₀ * ζ‖ ^ 2 * ‖deriv f z₀‖) := t4
      _ ≤ (1 + ρ) / (1 - ρ) ^ 3 * ((1 + ρ) ^ 2 * ‖deriv f z₀‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN2 hfpos.le) hA
      _ = ‖deriv f z₀‖ * ((1 + ρ) / (1 - ρ)) ^ 3 := by
          field_simp

/-- The hyperbolic distance in the box (1.3.20) is bounded: `e^{2λ(z₀, z)} ≤ 4(1 + b + c)²/a`, because
`|1 - z̄₀ z| ≤ (1 + b + c) δ`, `1 - |z₀|² ≥ δ`, `1 - |z|² ≥ a δ` and `1 - ρ² = (1 - |z|²)(1 - |z₀|²)/|1 - z̄₀ z|²`. -/
theorem p92_1_box {a b c δ θ : ℝ} {z₀ z : ℂ} (ha : 0 < a) (hb : 0 < b) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hz₀ : ‖z₀‖ = 1 - δ) (hzb : 1 - b * δ ≤ ‖z‖) (hza : ‖z‖ ≤ 1 - a * δ) (hθc : |θ| ≤ c * δ)
    (hθz : z * (‖z₀‖ : ℂ) = z₀ * (‖z‖ : ℂ) * Complex.exp (θ * I)) :
    Real.exp (2 * hypDistD z₀ z) ≤ 4 * (1 + b + c) ^ 2 / a := by
  have hz₀pos : 0 < ‖z₀‖ := by rw [hz₀]; linarith
  have hz₀1 : ‖z₀‖ < 1 := by rw [hz₀]; linarith
  have haδ : 0 < a * δ := mul_pos ha hδ0
  have hz1 : ‖z‖ < 1 := by linarith
  have hz₀D : z₀ ∈ unitDisc := mem_ball_zero_iff.2 hz₀1
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz1
  obtain ⟨hexp2, -⟩ := p92_1_hyp_exp hz₀D hzD
  have hc0 : 0 ≤ c := by
    have := abs_nonneg θ
    by_contra h
    push Not at h
    nlinarith
  -- `z̄₀ z = |z₀| |z| e^{iθ}`
  have hzz : conj z₀ * z = ((‖z₀‖ * ‖z‖ : ℝ) : ℂ) * Complex.exp (θ * I) := by
    have hz₀ne : ((‖z₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz₀pos.ne'
    apply mul_left_cancel₀ hz₀ne
    have e : conj z₀ * z₀ = ((‖z₀‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      push_cast
      ring
    calc ((‖z₀‖ : ℝ) : ℂ) * (conj z₀ * z) = conj z₀ * (z * (‖z₀‖ : ℂ)) := by ring
      _ = conj z₀ * (z₀ * (‖z‖ : ℂ) * Complex.exp (θ * I)) := by rw [hθz]
      _ = (conj z₀ * z₀) * (‖z‖ : ℂ) * Complex.exp (θ * I) := by ring
      _ = _ := by rw [e]; push_cast; ring
  have hR1 : ‖z₀‖ * ‖z‖ ≤ 1 := by nlinarith [norm_nonneg z, norm_nonneg z₀]
  have hRδ : 1 - ‖z₀‖ * ‖z‖ ≤ (1 + b) * δ := by
    rw [hz₀]
    nlinarith [mul_pos hb hδ0, mul_nonneg (mul_nonneg hb.le hδ0.le) hδ0.le]
  have hnorm1 : ‖(1 : ℂ) - conj z₀ * z‖ ≤ (1 + b + c) * δ := by
    rw [hzz]
    have hR0 : 0 ≤ ‖z₀‖ * ‖z‖ := by positivity
    have e : (1 : ℂ) - ((‖z₀‖ * ‖z‖ : ℝ) : ℂ) * Complex.exp (θ * I) =
        ((1 - ‖z₀‖ * ‖z‖ : ℝ) : ℂ) + ((‖z₀‖ * ‖z‖ : ℝ) : ℂ) * (1 - Complex.exp (θ * I)) := by
      push_cast
      ring
    have hexpθ : ‖(1 : ℂ) - Complex.exp (θ * I)‖ ≤ |θ| := by
      rw [norm_sub_rev, mul_comm]
      simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    calc ‖(1 : ℂ) - ((‖z₀‖ * ‖z‖ : ℝ) : ℂ) * Complex.exp (θ * I)‖
        ≤ ‖((1 - ‖z₀‖ * ‖z‖ : ℝ) : ℂ)‖ + ‖((‖z₀‖ * ‖z‖ : ℝ) : ℂ) * (1 - Complex.exp (θ * I))‖ := by
          rw [e]
          exact norm_add_le _ _
      _ = (1 - ‖z₀‖ * ‖z‖) + ‖z₀‖ * ‖z‖ * ‖(1 : ℂ) - Complex.exp (θ * I)‖ := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg hR0]
      _ ≤ (1 + b) * δ + 1 * (c * δ) :=
          add_le_add hRδ (mul_le_mul hR1 (hexpθ.trans hθc) (norm_nonneg _) zero_le_one)
      _ = (1 + b + c) * δ := by ring
  have hkey := LiZhongQC.normSq_blaschke_key z₀ z
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hkey
  have hρ1 : ‖LiZhongQC.blaschke z₀ z‖ < 1 := LiZhongQC.blaschke_mem_unitDisc hz₀1 hz1
  have hρ0 := norm_nonneg (LiZhongQC.blaschke z₀ z)
  have hden : (1 : ℂ) - conj z₀ * z ≠ 0 := LiZhongQC.blaschke_den_ne_zero hz₀1 hz1
  have hNpos : 0 < ‖(1 : ℂ) - conj z₀ * z‖ := norm_pos_iff.2 hden
  have hρdef : ‖LiZhongQC.blaschke z₀ z‖ = ‖z - z₀‖ / ‖(1 : ℂ) - conj z₀ * z‖ := by
    rw [LiZhongQC.blaschke, norm_div]
  rw [hexp2, hρdef]
  set N := ‖(1 : ℂ) - conj z₀ * z‖ with hN
  set M := ‖z - z₀‖ with hM
  have h1z : a * δ ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1z₀ : δ ≤ 1 - ‖z₀‖ ^ 2 := by rw [hz₀]; nlinarith
  have hMN : M < N := by
    rw [hρdef, div_lt_one hNpos] at hρ1
    exact hρ1
  have hM0 : 0 ≤ M := norm_nonneg _
  -- `(1 + M/N)/(1 - M/N) = (N + M)²/(N² - M²) ≤ 4 N²/((1 - |z|²)(1 - |z₀|²))`
  have hq : (1 + M / N) / (1 - M / N) = (N + M) ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖z₀‖ ^ 2)) := by
    have hd : N ^ 2 - M ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖z₀‖ ^ 2) := by linarith
    have h1 : 1 - M / N ≠ 0 := sub_ne_zero.2 ((div_lt_one hNpos).2 hMN).ne'
    have h2 : N ^ 2 - M ^ 2 ≠ 0 := by nlinarith
    rw [← hd, div_eq_div_iff h1 h2]
    field_simp
    ring
  rw [hq]
  have hnum : a * δ * δ ≤ (1 - ‖z‖ ^ 2) * (1 - ‖z₀‖ ^ 2) :=
    mul_le_mul h1z h1z₀ hδ0.le (by linarith)
  have hNM : (N + M) ^ 2 ≤ (2 * ((1 + b + c) * δ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc (N + M) ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖z₀‖ ^ 2))
      ≤ (2 * ((1 + b + c) * δ)) ^ 2 / (a * δ * δ) :=
        div_le_div₀ (by positivity) hNM (by positivity) hnum
    _ = 4 * (1 + b + c) ^ 2 / a := by
        field_simp
        ring

/-- **Corollary 1.6** (§1.3). Let `a, b, c` be positive constants and let `0 < |z₀| = 1 - δ < 1`. If (1.3.20)
`0 ≤ 1 - bδ ≤ |z| ≤ 1 - aδ`, `|arg z - arg z₀| ≤ cδ`, and if `f` maps `𝔻` conformally into `ℂ`, then (1.3.21)
`|f(z) - f(z₀)| ≤ M₁ δ |f'(z₀)|` and (1.3.22) `M₂⁻¹ |f'(z₀)| ≤ |f'(z)| ≤ M₂ |f'(z₀)|`, where the constants `M₁` and `M₂`
depend only on `a, b, c`.
Modelling: `∀ a b c, ∃ M₁ M₂, ∀ z₀ δ z f`. The angular condition is that the directions of `z` and `z₀` differ by an
angle `θ` with `|θ| ≤ cδ`, which avoids the branch cut of `arg`. -/
theorem cor1_6 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ M₁ M₂ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧ ∀ (z₀ : ℂ) (δ : ℝ), 0 < δ → δ < 1 → ‖z₀‖ = 1 - δ →
      ∀ z : ℂ, 0 ≤ 1 - b * δ → 1 - b * δ ≤ ‖z‖ → ‖z‖ ≤ 1 - a * δ →
        (∃ θ : ℝ, |θ| ≤ c * δ ∧ z * (‖z₀‖ : ℂ) = z₀ * (‖z‖ : ℂ) * exp (θ * I)) →
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
          ‖f z - f z₀‖ ≤ M₁ * δ * ‖deriv f z₀‖ ∧ M₂⁻¹ * ‖deriv f z₀‖ ≤ ‖deriv f z‖ ∧
            ‖deriv f z‖ ≤ M₂ * ‖deriv f z₀‖ := by
  have hK0 : 0 < 4 * (1 + b + c) ^ 2 / a := by positivity
  refine ⟨2 * (4 * (1 + b + c) ^ 2 / a) ^ 2, (4 * (1 + b + c) ^ 2 / a) ^ 3, by positivity, by positivity,
    fun z₀ δ hδ0 hδ1 hz₀ z _ hzb hza hθ f hf hinj => ?_⟩
  obtain ⟨θ, hθc, hθz⟩ := hθ
  have hE := p92_1_box ha hb hδ0 hδ1 hz₀ hzb hza hθc hθz
  set K := 4 * (1 + b + c) ^ 2 / a with hK
  have hz₀D : z₀ ∈ unitDisc := mem_ball_zero_iff.2 (by rw [hz₀]; linarith)
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 (by nlinarith [mul_pos ha hδ0])
  obtain ⟨-, c2, c3, c4⟩ := cor1_5 hf hinj hz₀D hzD
  set E := Real.exp (2 * hypDistD z₀ z) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have e4 : Real.exp (4 * hypDistD z₀ z) = E ^ 2 := by
    rw [hEdef, ← Real.exp_nat_mul]
    ring_nf
  have e6 : Real.exp (6 * hypDistD z₀ z) = E ^ 3 := by
    rw [hEdef, ← Real.exp_nat_mul]
    ring_nf
  have e6' : Real.exp (-(6 * hypDistD z₀ z)) = (E ^ 3)⁻¹ := by rw [Real.exp_neg, e6]
  have hE2 : E ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hE0.le hE 2
  have hE3 : E ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ hE0.le hE 3
  have hf'0 : deriv f z₀ ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hf hinj hz₀D
  have hfpos : 0 < ‖deriv f z₀‖ := norm_pos_iff.2 hf'0
  have hpos : 0 < 1 - ‖z₀‖ ^ 2 := by nlinarith [norm_nonneg z₀, mem_ball_zero_iff.1 hz₀D]
  have h2δ : 1 - ‖z₀‖ ^ 2 ≤ 2 * δ := by rw [hz₀]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [e4, div_le_iff₀ (mul_pos hpos hfpos)] at c2
    calc ‖f z - f z₀‖ ≤ E ^ 2 * ((1 - ‖z₀‖ ^ 2) * ‖deriv f z₀‖) := c2
      _ ≤ K ^ 2 * (2 * δ * ‖deriv f z₀‖) :=
          mul_le_mul hE2 (mul_le_mul_of_nonneg_right h2δ hfpos.le) (by positivity) (by positivity)
      _ = 2 * K ^ 2 * δ * ‖deriv f z₀‖ := by ring
  · rw [e6'] at c3
    calc (K ^ 3)⁻¹ * ‖deriv f z₀‖ ≤ (E ^ 3)⁻¹ * ‖deriv f z₀‖ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hE3) hfpos.le
      _ = ‖deriv f z₀‖ * (E ^ 3)⁻¹ := mul_comm _ _
      _ ≤ ‖deriv f z‖ := c3
  · rw [e6] at c4
    calc ‖deriv f z‖ ≤ ‖deriv f z₀‖ * E ^ 3 := c4
      _ ≤ ‖deriv f z₀‖ * K ^ 3 := mul_le_mul_of_nonneg_left hE3 hfpos.le
      _ = K ^ 3 * ‖deriv f z₀‖ := mul_comm _ _

/-- **Theorem 1.7** (§1.3). Let `f` map `𝔻` conformally into `ℂ`. Then (1.3.23) the radial limit
`f(ζ) = lim_{r → 1} f(rζ) ≠ ∞` exists for almost all `ζ ∈ 𝕋`, and (1.3.24)
`(1/2π) ∫₀^{2π} |f(r e^{it}) - f(0)|^{2/5} dt ≤ 5 |f'(0)|^{2/5}` for `0 ≤ r < 1`.
Modelling: "almost all `ζ ∈ 𝕋`" is almost every `t ∈ ℝ` for `ζ = e^{it}`; the limit is finite. -/
theorem thm1_7 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    (∀ᵐ t : ℝ, ∃ w : ℂ, Tendsto (fun r : ℝ => f (r * exp (t * I))) (𝓝[<] 1) (𝓝 w)) ∧
      ∀ r ∈ Ico (0 : ℝ) 1,
        1 / (2 * π) * ∫ t in (0 : ℝ)..2 * π, ‖f (r * exp (t * I)) - f 0‖ ^ (2 / 5 : ℝ) ≤
          5 * ‖deriv f 0‖ ^ (2 / 5 : ℝ) := by
  sorry

end Pommerenke1992
