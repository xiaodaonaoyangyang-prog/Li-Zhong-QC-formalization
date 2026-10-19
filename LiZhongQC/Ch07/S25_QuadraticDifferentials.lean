import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Lemmas.LocalRoots
import LiZhongQC.Lemmas.Umlaufsatz

/-!
# §25 全纯二次微分 — Holomorphic quadratic differentials

A quadratic differential on a Riemann surface is a `(2, 0)` differential (`IsDiffFamily 2 0`,
§22.5).  Most statements of §25.1–25.2 are local, and are formalized for a local coefficient
`φ(z) dz²` holomorphic in a plane domain.

* §25.1 horizontal and vertical trajectory arcs                  — `IsHorizontalArc`, `IsVerticalArc`
* natural parameters at regular points (25.1)–(25.3)             — `eq25_2_natural_parameter`,
                                                                    `eq25_3_natural_parameter_unique`
* natural parameters at zeros (25.4)–(25.6) and the `m + 2` critical trajectories
* natural parameters at simple poles (25.7)–(25.8) and double poles (25.9)
* §25.2 the `φ`-metric, `φ`-length and `φ`-area; `φ`-straight arcs
* local shortest connections; Theorem 25.1 (geodesics), Theorem 25.2 (polygons),
  Theorem 25.3 (uniqueness of geodesics)

* Theorem 25.4 (existence of shortest curves in a homotopy class on a compact surface) and its
  corollary (existence and uniqueness of geodesics for genus `g > 1`)
                                                                    — `thm25_4_shortest_exists`,
                                                                      `thm25_4_cor_unique_geodesic`
* §25.3 the linear space `Q(S)`: dimension `1` (complex) for tori, `3g - 3` (complex) and `6g - 6`
  (real) for genus `g > 1`, via Riemann–Roch                        — `sec25_3_dim_*`

The `φ`-length of a path on a Riemann surface is computed in charts: `phiLengthPath`.

## What is proved here

Only `dz_sq_trajectories`, that the horizontal and vertical segments are the trajectories of `dz²`.
The natural parameters (25.1)–(25.9) need holomorphic square and `(m+2)`-th roots, the geodesic
theorems 25.1–25.4 need the `φ`-metric machinery, and §25.3 rests on Riemann–Roch.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

/-! ## §25.1 Basic notions -/

/-- A holomorphic quadratic differential on a Riemann surface. -/
def IsHolQuadDiff {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) : Prop :=
  q ∈ holQuadDiffSubmodule S

/-- A meromorphic quadratic differential on a Riemann surface. -/
def IsMeroQuadDiff {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) : Prop :=
  IsDiffFamily 2 0 q ∧ ∀ x : S, MeromorphicOn (q x) (chartAt ℂ x).target

/-- `c` is a horizontal trajectory arc (水平轨线弧) of `φ(z) dz²` on `(a, b)`: it passes only
through regular points and `φ(c(t)) c'(t)² > 0`. -/
def IsHorizontalArc (φ : ℂ → ℂ) (c : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧ φ (c t) ≠ 0 ∧
    (φ (c t) * deriv c t ^ 2).im = 0 ∧ 0 < (φ (c t) * deriv c t ^ 2).re

/-- `c` is a vertical trajectory arc (垂直轨线弧): `φ(c(t)) c'(t)² < 0`. -/
def IsVerticalArc (φ : ℂ → ℂ) (c : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧ φ (c t) ≠ 0 ∧
    (φ (c t) * deriv c t ^ 2).im = 0 ∧ (φ (c t) * deriv c t ^ 2).re < 0

/-- In the plane with `φ = 1`, horizontal segments are horizontal trajectory arcs and vertical
segments are vertical trajectory arcs of `dz²`. -/
theorem dz_sq_trajectories (z₀ : ℂ) :
    IsHorizontalArc (fun _ => 1) (fun t => z₀ + t) 0 1 ∧
      IsVerticalArc (fun _ => 1) (fun t => z₀ + t * I) 0 1 := by
  have hhor : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z₀ + (t : ℂ)) 1 t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add z₀
  have hver : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z₀ + (t : ℂ) * I) I t := fun t => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add z₀
  constructor
  · intro t _
    refine ⟨(hhor t).differentiableAt, ?_, one_ne_zero, ?_, ?_⟩
    · rw [(hhor t).deriv]
      exact one_ne_zero
    · rw [(hhor t).deriv]
      norm_num
    · rw [(hhor t).deriv]
      norm_num
  · intro t _
    refine ⟨(hver t).differentiableAt, ?_, one_ne_zero, ?_, ?_⟩
    · rw [(hver t).deriv]
      exact I_ne_zero
    · rw [(hver t).deriv]
      simp [Complex.I_sq]
    · rw [(hver t).deriv]
      simp [Complex.I_sq]

/-- (25.1)–(25.2): near a regular point `z₀` (`φ(z₀) ≠ 0`) the natural parameter
`ζ(z) = ∫_{z₀}^{z} √φ(t) dt` is a local conformal coordinate with `ζ(z₀) = 0` in which
`φ dz² = dζ²`. -/
theorem eq25_2_natural_parameter {φ : ℂ → ℂ} {z₀ : ℂ} (hφ : AnalyticAt ℂ φ z₀) (h0 : φ z₀ ≠ 0) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, deriv ζ z ^ 2 = φ z := by
  obtain ⟨r, hr, hr0, hrφ, -⟩ := exists_analyticAt_sq_eq hφ h0
  obtain ⟨ζ, hζ, hζ0, hζd⟩ := exists_primitive_analyticAt hr
  refine ⟨ζ, hζ, hζ0, ?_, ?_⟩
  · rw [hζd.self_of_nhds.deriv]
    exact hr0
  · filter_upwards [hζd] with z hz
    rw [hz.deriv, hrφ]

/-- (25.3): two natural parameters at a regular point differ by sign: `ζ = ±ζ₁`. -/
theorem eq25_3_natural_parameter_unique {φ ζ ζ₁ : ℂ → ℂ} {z₀ : ℂ} (hζ : AnalyticAt ℂ ζ z₀)
    (hζ₁ : AnalyticAt ℂ ζ₁ z₀) (h0 : ζ z₀ = 0) (h0₁ : ζ₁ z₀ = 0)
    (h : ∀ᶠ z in 𝓝 z₀, deriv ζ z ^ 2 = φ z) (h₁ : ∀ᶠ z in 𝓝 z₀, deriv ζ₁ z ^ 2 = φ z)
    (hne : φ z₀ ≠ 0) : (∀ᶠ z in 𝓝 z₀, ζ z = ζ₁ z) ∨ ∀ᶠ z in 𝓝 z₀, ζ z = -ζ₁ z := by
  have _hne := hne
  have hD : AnalyticAt ℂ (fun z => deriv ζ z - deriv ζ₁ z) z₀ := hζ.deriv.sub hζ₁.deriv
  have hE : AnalyticAt ℂ (fun z => deriv ζ z + deriv ζ₁ z) z₀ := hζ.deriv.add hζ₁.deriv
  have hprod : ∀ᶠ z in 𝓝 z₀, (deriv ζ z - deriv ζ₁ z) * (deriv ζ z + deriv ζ₁ z) = 0 := by
    filter_upwards [h, h₁] with z hz hz₁
    have : (deriv ζ z - deriv ζ₁ z) * (deriv ζ z + deriv ζ₁ z) =
        deriv ζ z ^ 2 - deriv ζ₁ z ^ 2 := by ring
    rw [this, hz, hz₁, sub_self]
  -- an analytic `F` vanishing at `z₀` whose derivative vanishes near `z₀` vanishes near `z₀`
  have key : ∀ (s : ℂ) (F : ℂ → ℂ), AnalyticAt ℂ F z₀ → F z₀ = 0 →
      (∀ᶠ z in 𝓝 z₀, deriv F z = deriv ζ z + s * deriv ζ₁ z) →
      (∀ᶠ z in 𝓝 z₀, deriv ζ z + s * deriv ζ₁ z = 0) → ∀ᶠ z in 𝓝 z₀, F z = 0 := by
    intro s F hF hF0 hFd hs
    have := eventually_eq_const_of_deriv_eq_zero hF
      ((hFd.and hs).mono fun z hz => hz.1.trans hz.2)
    filter_upwards [this] with z hz
    rw [hz, hF0]
  rcases hD.eventually_eq_zero_or_eventually_ne_zero with hD0 | hDne
  · left
    have hFd : ∀ᶠ z in 𝓝 z₀, deriv (fun z => ζ z - ζ₁ z) z = deriv ζ z + (-1) * deriv ζ₁ z := by
      filter_upwards [hζ.eventually_analyticAt, hζ₁.eventually_analyticAt] with z ha hb
      have hD' : HasDerivAt (fun z => ζ z - ζ₁ z) (deriv ζ z - deriv ζ₁ z) z :=
        ha.differentiableAt.hasDerivAt.sub hb.differentiableAt.hasDerivAt
      rw [hD'.deriv]
      ring
    have := key (-1) (fun z => ζ z - ζ₁ z) (hζ.sub hζ₁) (by simp [h0, h0₁]) hFd
      (hD0.mono fun z hz => by
        have hz' : deriv ζ z - deriv ζ₁ z = 0 := hz
        linear_combination hz')
    filter_upwards [this] with z hz
    exact sub_eq_zero.1 hz
  · right
    have hE0 : ∀ᶠ z in 𝓝 z₀, deriv ζ z + deriv ζ₁ z = 0 := by
      rcases hE.eventually_eq_zero_or_eventually_ne_zero with hE0 | hEne
      · exact hE0
      · exfalso
        obtain ⟨z, hz1, hz2, hz3⟩ :=
          (hDne.and (hEne.and (hprod.filter_mono nhdsWithin_le_nhds))).exists
        exact (mul_ne_zero hz1 hz2) hz3
    have hFd : ∀ᶠ z in 𝓝 z₀, deriv (fun z => ζ z + ζ₁ z) z = deriv ζ z + 1 * deriv ζ₁ z := by
      filter_upwards [hζ.eventually_analyticAt, hζ₁.eventually_analyticAt] with z ha hb
      have hD' : HasDerivAt (fun z => ζ z + ζ₁ z) (deriv ζ z + deriv ζ₁ z) z :=
        ha.differentiableAt.hasDerivAt.add hb.differentiableAt.hasDerivAt
      rw [hD'.deriv]
      ring
    have := key 1 (fun z => ζ z + ζ₁ z) (hζ.add hζ₁) (by simp [h0, h0₁]) hFd
      (hE0.mono fun z hz => by linear_combination hz)
    filter_upwards [this] with z hz
    exact eq_neg_of_add_eq_zero_left hz

/-- The derivative at `z₀` of `z ↦ (z - z₀) H z` is `H z₀`. -/
theorem hasDerivAt_sub_mul {H : ℂ → ℂ} {z₀ : ℂ} (hH : DifferentiableAt ℂ H z₀) :
    HasDerivAt (fun z => (z - z₀) * H z) (H z₀) z₀ := by
  have h := ((hasDerivAt_id z₀).sub_const z₀).mul hH.hasDerivAt
  have e : (1 : ℂ) * H z₀ + (id z₀ - z₀) * deriv H z₀ = H z₀ := by simp
  rw [e] at h
  exact h

/-- **Pull-back of a coefficient under `w ↦ z₀ + w²`.**  For `ψ` analytic at `z₀` with
`ψ z₀ ≠ 0` and `j : ℕ`, there are an even analytic square root `r` of `w ↦ ψ (z₀ + w²)`, the
primitive `ξ` of `2 wʲ r` with `ξ 0 = 0`, and an analytic `G` with `G 0 ≠ 0` and
`ξ w = w^(j+1) G (w²)` near `0`.

Route: `r` from `exists_analyticAt_sq_eq` (even since the pulled-back coefficient is), `ξ` from
`exists_primitive_analyticAt`; the parity `ξ (-w) = (-1)^(j+1) ξ w` follows from the vanishing
derivative of the difference; `exists_factor_of_deriv_eq_pow_mul` gives `ξ = w^(j+1) g` with `g`
even, and `exists_analyticAt_comp_sq_of_even` writes `g = G ∘ (·²)`. -/
theorem exists_natural_parameter_pullback {ψ : ℂ → ℂ} {z₀ : ℂ} (hψ : AnalyticAt ℂ ψ z₀)
    (hψ0 : ψ z₀ ≠ 0) (j : ℕ) :
    ∃ r ξ G : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0 ≠ 0 ∧ (∀ w, r w ^ 2 = ψ (z₀ + w ^ 2)) ∧
      AnalyticAt ℂ ξ 0 ∧ ξ 0 = 0 ∧ (∀ᶠ w in 𝓝 (0 : ℂ), HasDerivAt ξ (2 * w ^ j * r w) w) ∧
      AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧ ∀ᶠ w in 𝓝 (0 : ℂ), ξ w = w ^ (j + 1) * G (w ^ 2) := by
  -- the pulled-back coefficient and its even square root
  have hq : AnalyticAt ℂ (fun w : ℂ => ψ (z₀ + w ^ 2)) 0 :=
    hψ.comp_of_eq (f := fun w : ℂ => z₀ + w ^ 2) (by fun_prop) (by simp)
  have hq0 : (fun w : ℂ => ψ (z₀ + w ^ 2)) 0 ≠ 0 := by simpa using hψ0
  obtain ⟨r, hr, hr0, hrq, hrfun⟩ := exists_analyticAt_sq_eq hq hq0
  have hreven : ∀ w, r (-w) = r w := fun w => hrfun (-w) w (by simp)
  -- the primitive `ξ` of `2 wʲ r`
  have hf : AnalyticAt ℂ (fun w : ℂ => 2 * w ^ j * r w) 0 :=
    (analyticAt_const.mul (analyticAt_id.pow j)).mul hr
  obtain ⟨ξ, hξ, hξ0, hξd⟩ := exists_primitive_analyticAt hf
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hξd
  have hballev : ∀ᶠ w in 𝓝 (0 : ℂ), dist w 0 < ε := Metric.ball_mem_nhds 0 hε
  -- parity: `ξ (-w) = (-1)^(j+1) ξ w`
  have hpar : ∀ᶠ w in 𝓝 (0 : ℂ), ξ (-w) = (-1) ^ (j + 1) * ξ w := by
    have hD : AnalyticAt ℂ (fun w => ξ (-w) - (-1) ^ (j + 1) * ξ w) 0 := by
      have h1 : AnalyticAt ℂ (ξ ∘ fun w : ℂ => -w) 0 :=
        hξ.comp_of_eq analyticAt_id.neg (by simp)
      exact h1.sub (analyticAt_const.mul hξ)
    have hDd : ∀ᶠ w in 𝓝 (0 : ℂ), deriv (fun w => ξ (-w) - (-1) ^ (j + 1) * ξ w) w = 0 := by
      filter_upwards [hballev] with w hw
      have hw' : dist (-w) 0 < ε := by rwa [dist_zero_right, norm_neg, ← dist_zero_right]
      have h1 : HasDerivAt (fun w => ξ (-w)) (2 * (-w) ^ j * r (-w) * (-1)) w :=
        (hball hw').comp w (hasDerivAt_neg w)
      have h2 : HasDerivAt (fun w => (-1 : ℂ) ^ (j + 1) * ξ w) ((-1) ^ (j + 1) * (2 * w ^ j * r w)) w :=
        (hball hw).const_mul _
      have h3 : HasDerivAt (fun w => ξ (-w) - (-1 : ℂ) ^ (j + 1) * ξ w)
          (2 * (-w) ^ j * r (-w) * (-1) - (-1) ^ (j + 1) * (2 * w ^ j * r w)) w := h1.sub h2
      rw [h3.deriv, hreven, neg_pow]
      ring
    have := eventually_eq_const_of_deriv_eq_zero hD hDd
    filter_upwards [this] with w hw
    simp only [neg_zero, hξ0, mul_zero, sub_zero] at hw
    exact sub_eq_zero.1 hw
  -- the factorization `ξ = w^(j+1) g`
  have hd' : ∀ᶠ w in 𝓝 (0 : ℂ), deriv ξ w = w ^ j * (2 * r w) := by
    filter_upwards [hξd] with w hw
    rw [hw.deriv]
    ring
  obtain ⟨g, hg, hg0, hξg⟩ := exists_factor_of_deriv_eq_pow_mul hξ hξ0 (analyticAt_const.mul hr)
    (by simpa using hr0) hd'
  -- `g` is even
  have hgeven : ∀ᶠ w in 𝓝 (0 : ℂ), g (-w) = g w := by
    obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.1 (hξg.and hpar)
    have hballev' : ∀ᶠ w in 𝓝 (0 : ℂ), dist w 0 < ε' := Metric.ball_mem_nhds 0 hε'
    filter_upwards [hballev'] with w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hw' : dist (-w) 0 < ε' := by rwa [dist_zero_right, norm_neg, ← dist_zero_right]
      obtain ⟨h1, h2⟩ := hball' hw
      obtain ⟨h3, -⟩ := hball' hw'
      rw [h3, h1, neg_pow] at h2
      have hne : (-1 : ℂ) ^ (j + 1) * w ^ (j + 1) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hw0)
      have h4 : (-1 : ℂ) ^ (j + 1) * w ^ (j + 1) * g (-w) =
          (-1 : ℂ) ^ (j + 1) * w ^ (j + 1) * g w := by linear_combination h2
      exact mul_left_cancel₀ hne h4
  obtain ⟨G, hG, hG0, hGg⟩ := exists_analyticAt_comp_sq_of_even hg hgeven
  refine ⟨r, ξ, G, hr, hr0, hrq, hξ, hξ0, hξd, hG, by rw [hG0]; exact hg0, ?_⟩
  filter_upwards [hξg, hGg] with w h1 h2
  rw [h1, h2]

/-- If `(z - z₀) ^ a * A z = 0` on a punctured neighbourhood of `z₀` and `A` is continuous at
`z₀`, then `A z₀ = 0`. -/
theorem eq_zero_of_pow_sub_mul_eq_zero {A : ℂ → ℂ} {z₀ : ℂ} {a : ℕ} (hA : ContinuousAt A z₀)
    (h : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ a * A z = 0) : A z₀ = 0 := by
  have h1 : ∀ᶠ z in 𝓝[≠] z₀, A z = (fun _ => (0 : ℂ)) z := by
    filter_upwards [h, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ z₀ := hz0
    exact (mul_eq_zero.1 hz).resolve_left (pow_ne_zero a (sub_ne_zero.2 hz0'))
  exact eq_of_continuousAt_of_eventuallyEq_nhdsNE hA continuousAt_const h1

/-- (25.4)–(25.5): at a zero of order `m` there is a natural parameter `ζ` (a local conformal
coordinate with `ζ(z₀) = 0`) with `φ dz² = ((m+2)/2)² ζ^m dζ²`. -/
theorem eq25_5_natural_parameter_zero {φ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 0 < m)
    {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ z₀) (hψ0 : ψ z₀ ≠ 0) (hφ : ∀ᶠ z in 𝓝 z₀, φ z = (z - z₀) ^ m * ψ z) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 := by
  obtain ⟨r, ξ, G, hr, hr0, hrq, hξ, hξ0, hξd, hG, hG0, hξG⟩ :=
    exists_natural_parameter_pullback hψ hψ0 (m + 1)
  -- an `(m+2)`-th root `k` of `G ^ 2`, and `ζ z = (z - z₀) k (z - z₀)`
  obtain ⟨k, hk, hk0, hkG⟩ := exists_analyticAt_pow_eq (hG.pow 2) (pow_ne_zero 2 hG0)
    (by omega : 0 < m + 2)
  set ζ : ℂ → ℂ := fun z => (z - z₀) * k (z - z₀) with hζdef
  have hkz : AnalyticAt ℂ (fun z => k (z - z₀)) z₀ :=
    hk.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  have hζ : AnalyticAt ℂ ζ z₀ := (analyticAt_id.sub analyticAt_const).mul hkz
  have hζ0 : ζ z₀ = 0 := by simp [hζdef]
  have hζd0 : deriv ζ z₀ = k 0 := by
    have h : HasDerivAt ζ ((fun z => k (z - z₀)) z₀) z₀ := hasDerivAt_sub_mul hkz.differentiableAt
    rw [h.deriv]
    simp
  -- the facts about `k` near `0`, transported along `v ↦ v²`
  have hsq0 : Tendsto (fun v : ℂ => v ^ 2) (𝓝 0) (𝓝 0) := by
    have := (continuous_pow 2).tendsto (0 : ℂ)
    rwa [zero_pow two_ne_zero] at this
  have hkv : ∀ᶠ v in 𝓝 (0 : ℂ), k (v ^ 2) ^ (m + 2) = G (v ^ 2) ^ 2 ∧ k (v ^ 2) ≠ 0 := by
    have h1 : ∀ᶠ u in 𝓝 (0 : ℂ), k u ^ (m + 2) = G u ^ 2 ∧ k u ≠ 0 := by
      have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), k u ≠ 0 := hk.continuousAt.eventually_ne hk0
      filter_upwards [hkG, h2] with u hu1 hu2
      exact ⟨by simpa using hu1, hu2⟩
    exact hsq0.eventually h1
  -- a radius `ε` for the `w`-facts and a radius `ε'` for the analyticity of `ζ`
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hξd.and (hξG.and hkv))
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.1 (hζ.eventually_analyticAt.and hφ)
  -- `ζ (z₀ + v²) ^ (m+2) = ξ v ^ 2` for `‖v‖ < ε`
  have hζξ : ∀ v : ℂ, dist v 0 < ε → ζ (z₀ + v ^ 2) ^ (m + 2) = ξ v ^ 2 := by
    intro v hv
    obtain ⟨-, hv2, hv3, -⟩ := hball hv
    simp only [hζdef, add_sub_cancel_left]
    rw [hv2, mul_pow, hv3]
    ring
  refine ⟨ζ, hζ, hζ0, ?_, ?_⟩
  · rw [hζd0]
    exact hk0
  · set δ : ℝ := min (ε ^ 2) ε' with hδ
    have hδ0 : 0 < δ := lt_min (pow_pos hε 2) hε'
    filter_upwards [Metric.ball_mem_nhds z₀ hδ0] with z hzδ
    have hzδ' : ‖z - z₀‖ < δ := by rwa [mem_ball, dist_eq_norm] at hzδ
    obtain ⟨hζan, hφz⟩ := hball' (by
      rw [dist_eq_norm]
      exact lt_of_lt_of_le hzδ' (min_le_right _ _))
    rcases eq_or_ne z z₀ with rfl | hz0'
    · -- at `z₀` both sides vanish
      rw [hφz, hζ0, sub_self, zero_pow hm.ne']
      ring
    · -- the square root `w` of `z - z₀`
      set w : ℂ := (z - z₀) ^ ((1 / 2 : ℝ) : ℂ) with hw
      have hw2 : w ^ 2 = z - z₀ := cpow_half_sq _
      have hwn : ‖w‖ = Real.sqrt ‖z - z₀‖ := norm_cpow_half _
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, zero_pow two_ne_zero] at hw2
        exact hz0' (sub_eq_zero.1 hw2.symm)
      have hwε : dist w 0 < ε := by
        rw [dist_zero_right, hwn, Real.sqrt_lt' hε]
        exact lt_of_lt_of_le hzδ' (min_le_left _ _)
      obtain ⟨hξdw, -, -, hkw⟩ := hball hwε
      have hz_eq : z = z₀ + w ^ 2 := by rw [hw2]; ring
      have hζz : ζ z ≠ 0 := by
        show (z - z₀) * k (z - z₀) ≠ 0
        rw [← hw2]
        exact mul_ne_zero (pow_ne_zero 2 hw0) hkw
      -- the chain rule along `v ↦ z₀ + v²`, applied to `ζ ^ (m+2)`
      have hchain : HasDerivAt (fun v => ζ (z₀ + v ^ 2) ^ (m + 2))
          (↑(m + 2 : ℕ) * ζ z ^ (m + 2 - 1) * (deriv ζ z * (2 * w))) w := by
        have h1 : HasDerivAt (fun v : ℂ => z₀ + v ^ 2) (2 * w) w := by
          have := (hasDerivAt_pow 2 w).const_add z₀
          simpa using this
        have h2 : HasDerivAt (fun v => ζ (z₀ + v ^ 2)) (deriv ζ z * (2 * w)) w :=
          HasDerivAt.comp_of_eq w hζan.differentiableAt.hasDerivAt h1 hz_eq
        have h3 : HasDerivAt (fun v => ζ (z₀ + v ^ 2) ^ (m + 2))
            (↑(m + 2 : ℕ) * ζ (z₀ + w ^ 2) ^ (m + 2 - 1) * (deriv ζ z * (2 * w))) w :=
          h2.pow (m + 2)
        rw [← hz_eq] at h3
        exact h3
      have hev : (fun v => ζ (z₀ + v ^ 2) ^ (m + 2)) =ᶠ[𝓝 w] fun v => ξ v ^ 2 := by
        have : ∀ᶠ v in 𝓝 w, dist v 0 < ε :=
          Metric.isOpen_ball.mem_nhds (by rw [mem_ball]; exact hwε)
        filter_upwards [this] with v hv
        exact hζξ v hv
      have hderiv : (m + 2 : ℂ) * ζ z ^ (m + 1) * deriv ζ z * (2 * w) =
          2 * ξ w * (2 * w ^ (m + 1) * r w) := by
        have h1 : HasDerivAt (fun v => ξ v ^ 2) (↑(2 : ℕ) * ξ w ^ (2 - 1) * (2 * w ^ (m + 1) * r w)) w :=
          hξdw.pow 2
        have h2 := hchain.congr_of_eventuallyEq hev.symm
        have h3 := h2.unique h1
        have e1 : m + 2 - 1 = m + 1 := by omega
        have e2 : (2 : ℕ) - 1 = 1 := by norm_num
        rw [e1, e2, pow_one] at h3
        push_cast at h3
        linear_combination h3
      have hK2 : (m + 2 : ℂ) * ζ z ^ (m + 1) * deriv ζ z = 2 * ξ w * w ^ m * r w := by
        refine mul_right_cancel₀ (mul_ne_zero two_ne_zero hw0) ?_
        rw [hderiv]
        ring
      have hK1 : ζ z ^ (m + 2) = ξ w ^ 2 := by
        rw [hz_eq]
        exact hζξ w hwε
      have hK3 : φ z = w ^ (2 * m) * r w ^ 2 := by
        rw [hφz, hrq w, ← hz_eq, ← hw2]
        ring
      rw [hK3]
      refine mul_left_cancel₀ (pow_ne_zero (m + 2) hζz) ?_
      linear_combination (w ^ (2 * m) * r w ^ 2) * hK1 -
        (1 / 4) * ((m + 2 : ℂ) * ζ z ^ (m + 1) * deriv ζ z + 2 * ξ w * w ^ m * r w) * hK2

/-- (25.6): two natural parameters at a zero of order `m` differ by an `(m+2)`-th root of unity. -/
theorem eq25_6_natural_parameter_zero_unique {φ ζ ζ₁ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 0 < m)
    (hζ : AnalyticAt ℂ ζ z₀) (hζ₁ : AnalyticAt ℂ ζ₁ z₀) (h0 : ζ z₀ = 0) (h0₁ : ζ₁ z₀ = 0)
    (hd : deriv ζ z₀ ≠ 0) (hd₁ : deriv ζ₁ z₀ ≠ 0)
    (h : ∀ᶠ z in 𝓝 z₀, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (h₁ : ∀ᶠ z in 𝓝 z₀, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ₁ z ^ m * deriv ζ₁ z ^ 2) :
    ∃ ε : ℂ, ε ^ (m + 2) = 1 ∧ ∀ᶠ z in 𝓝 z₀, ζ z = ε * ζ₁ z := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  push_cast at h h₁
  -- the difference quotients `v`, `v₁` and the ratio `U = v / v₁`
  set v : ℂ → ℂ := dslope ζ z₀ with hvdef
  set v₁ : ℂ → ℂ := dslope ζ₁ z₀ with hv₁def
  have hv : AnalyticAt ℂ v z₀ := analyticAt_dslope hζ
  have hv₁ : AnalyticAt ℂ v₁ z₀ := analyticAt_dslope hζ₁
  have hv0 : v z₀ = deriv ζ z₀ := dslope_same ζ z₀
  have hv₁0 : v₁ z₀ = deriv ζ₁ z₀ := dslope_same ζ₁ z₀
  have hζv : ∀ z, ζ z = (z - z₀) * v z := fun z => by
    have := sub_smul_dslope ζ z₀ z
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this.symm
  have hζ₁v : ∀ z, ζ₁ z = (z - z₀) * v₁ z := fun z => by
    have := sub_smul_dslope ζ₁ z₀ z
    rw [smul_eq_mul, h0₁, sub_zero] at this
    exact this.symm
  have hv₁0' : v₁ z₀ ≠ 0 := by rw [hv₁0]; exact hd₁
  have hv₁ne : ∀ᶠ z in 𝓝 z₀, v₁ z ≠ 0 := hv₁.continuousAt.eventually_ne hv₁0'
  set U : ℂ → ℂ := fun z => v z / v₁ z with hUdef
  have hU : AnalyticAt ℂ U z₀ := hv.div hv₁ hv₁0'
  set U₀ : ℂ := U z₀ with hU₀def
  have hU₀ : U₀ ≠ 0 := by
    simp only [hU₀def, hUdef, hv0, hv₁0]
    exact div_ne_zero hd hd₁
  -- `ζ = U ζ₁` near `z₀`
  have hζU : ∀ᶠ z in 𝓝 z₀, ζ z = U z * ζ₁ z := by
    filter_upwards [hv₁ne] with z hz
    rw [hζv z, hζ₁v z]
    simp only [hUdef]
    field_simp
  -- `A = ζ₁'` and the derivative of `ζ = U ζ₁`
  set A : ℂ → ℂ := deriv ζ₁ with hAdef
  have hA : AnalyticAt ℂ A z₀ := hζ₁.deriv
  have hA0 : A z₀ ≠ 0 := hd₁
  have hζ'U : ∀ᶠ z in 𝓝 z₀, deriv ζ z = deriv U z * ζ₁ z + U z * A z := by
    have h1 : deriv ζ =ᶠ[𝓝 z₀] deriv (fun z => U z * ζ₁ z) := Filter.EventuallyEq.deriv hζU
    filter_upwards [h1, hU.eventually_analyticAt, hζ₁.eventually_analyticAt] with z hz hUz hζ₁z
    rw [hz]
    exact (hUz.differentiableAt.hasDerivAt.mul hζ₁z.differentiableAt.hasDerivAt).deriv
  -- the key identity `U^m (U' ζ₁ + U ζ₁')² = ζ₁'²` on the punctured neighbourhood
  have hc : (((m' : ℂ) + 1 + 2) / 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    apply div_ne_zero _ two_ne_zero
    exact_mod_cast (by omega : m' + 1 + 2 ≠ 0)
  have hkeyNE : ∀ᶠ z in 𝓝[≠] z₀,
      U z ^ (m' + 1) * (deriv U z * ζ₁ z + U z * A z) ^ 2 = A z ^ 2 := by
    filter_upwards [(h.and (h₁.and (hζU.and (hζ'U.and hv₁ne)))).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hz0
    obtain ⟨hz, hz₁, hzU, hz', hzv⟩ := hz
    have hz0' : z ≠ z₀ := hz0
    have hζ₁ne : ζ₁ z ≠ 0 := by
      rw [hζ₁v z]
      exact mul_ne_zero (sub_ne_zero.2 hz0') hzv
    rw [hzU, hz'] at hz
    have h2 : (((m' : ℂ) + 1 + 2) / 2) ^ 2 * ζ₁ z ^ (m' + 1) *
        (U z ^ (m' + 1) * (deriv U z * ζ₁ z + U z * A z) ^ 2 - A z ^ 2) = 0 := by
      have := hz.symm.trans hz₁
      linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero hc (pow_ne_zero _ hζ₁ne))
    · exact sub_eq_zero.1 h3
  -- the identity at `z₀` by continuity, hence `U₀ ^ (m+2) = 1`
  have hkey0 : U₀ ^ (m' + 1) * (deriv U z₀ * ζ₁ z₀ + U₀ * A z₀) ^ 2 = A z₀ ^ 2 := by
    have hUc := hU.continuousAt
    have hU'c := hU.deriv.continuousAt
    have hζ₁c := hζ₁.continuousAt
    have hAc := hA.continuousAt
    have hc1 : ContinuousAt (fun z => U z ^ (m' + 1) * (deriv U z * ζ₁ z + U z * A z) ^ 2) z₀ := by
      fun_prop
    have hc2 : ContinuousAt (fun z => A z ^ 2) z₀ := by fun_prop
    exact eq_of_continuousAt_of_eventuallyEq_nhdsNE hc1 hc2 hkeyNE
  rw [h0₁, mul_zero, zero_add] at hkey0
  have hε : U₀ ^ (m' + 1 + 2) = 1 := by
    have h2 : U₀ ^ (m' + 1 + 2) * A z₀ ^ 2 = 1 * A z₀ ^ 2 := by
      linear_combination hkey0
    exact mul_right_cancel₀ (pow_ne_zero 2 hA0) h2
  refine ⟨U₀, hε, ?_⟩
  -- it remains to show that `U` is constant near `z₀`
  suffices hUc : ∀ᶠ z in 𝓝 z₀, U z = U₀ by
    filter_upwards [hζU, hUc] with z hz hz'
    rw [hz, hz']
  by_contra hcon
  -- otherwise `U - U₀ = (z - z₀)^(j+1) R` with `R z₀ ≠ 0`
  have hUm : AnalyticAt ℂ (fun z => U z - U₀) z₀ := hU.sub analyticAt_const
  have hne : ¬ ∀ᶠ z in 𝓝 z₀, U z - U₀ = 0 := fun h' =>
    hcon (h'.mono fun z hz => sub_eq_zero.1 hz)
  obtain ⟨k, R, hR, hR0, hUR⟩ := hUm.exists_eventuallyEq_pow_smul_nonzero_iff.2 hne
  simp only [smul_eq_mul] at hUR
  have hk : k ≠ 0 := by
    rintro rfl
    have := hUR.self_of_nhds
    rw [pow_zero, one_mul, sub_self] at this
    exact hR0 this.symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [Nat.succ_eq_add_one] at hUR
  -- `U = U₀ + (z - z₀)^(j+1) R` and its derivative
  have hF1 : ∀ᶠ z in 𝓝 z₀, U z = U₀ + (z - z₀) ^ (j + 1) * R z := by
    filter_upwards [hUR] with z hz
    linear_combination hz
  have hF2 : ∀ᶠ z in 𝓝 z₀,
      deriv U z = (z - z₀) ^ j * (((j : ℂ) + 1) * R z + (z - z₀) * deriv R z) := by
    have h1 : deriv U =ᶠ[𝓝 z₀] deriv (fun z => U₀ + (z - z₀) ^ (j + 1) * R z) :=
      Filter.EventuallyEq.deriv hF1
    filter_upwards [h1, hR.eventually_analyticAt] with z hz hRz
    have hp : HasDerivAt (fun z => (z - z₀) ^ (j + 1))
        (((j + 1 : ℕ) : ℂ) * (z - z₀) ^ (j + 1 - 1) * 1) z :=
      ((hasDerivAt_id z).sub_const z₀).pow (j + 1)
    have hD : HasDerivAt (fun z => U₀ + (z - z₀) ^ (j + 1) * R z)
        (((j + 1 : ℕ) : ℂ) * (z - z₀) ^ (j + 1 - 1) * 1 * R z + (z - z₀) ^ (j + 1) * deriv R z) z :=
      (hp.mul hRz.differentiableAt.hasDerivAt).const_add U₀
    rw [hz, hD.deriv, Nat.add_sub_cancel]
    push_cast
    ring
  -- the geometric sum `S` with `U^(m+1) - U₀^(m+1) = (U - U₀) S`
  set S : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (m' + 1), U z ^ i * U₀ ^ (m' + 1 - 1 - i) with hSdef
  have hF6 : ∀ z, U z ^ (m' + 1) = U₀ ^ (m' + 1) + (U z - U₀) * S z := fun z => by
    have := geom_sum₂_mul (U z) U₀ (m' + 1)
    simp only [hSdef]
    linear_combination -this
  have hS0 : S z₀ = ((m' : ℂ) + 1) * U₀ ^ m' := by
    have hterm : ∀ i ∈ Finset.range (m' + 1), U₀ ^ i * U₀ ^ (m' + 1 - 1 - i) = U₀ ^ m' := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [← pow_add]
      congr 1
      omega
    simp only [hSdef]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  -- the expression `E` with `(z - z₀)^(j+1) E = 0` near `z₀`
  set T₁ : ℂ → ℂ := fun z =>
    R z * A z + (((j : ℂ) + 1) * R z + (z - z₀) * deriv R z) * v₁ z with hT₁def
  set T₂ : ℂ → ℂ := fun z => 2 * U₀ * A z + (z - z₀) ^ (j + 1) * T₁ z with hT₂def
  set E : ℂ → ℂ := fun z => U₀ ^ (m' + 1) * T₁ z * T₂ z + R z * S z * U₀ ^ 2 * A z ^ 2 +
    (z - z₀) ^ (j + 1) * R z * S z * T₁ z * T₂ z with hEdef
  have hE : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ (j + 1) * E z = 0 := by
    filter_upwards [hkeyNE, (hF1.and hF2).filter_mono nhdsWithin_le_nhds] with z hz hz12
    obtain ⟨hz1, hz2⟩ := hz12
    rw [hF6 z, hz2, hζ₁v z, hz1] at hz
    simp only [hEdef, hT₁def, hT₂def]
    linear_combination hz - A z ^ 2 * hε
  have hEc : ContinuousAt E z₀ := by
    have hUc := hU.continuousAt
    have hSc : ContinuousAt S z₀ := by
      have hSa : AnalyticAt ℂ S z₀ := by
        have h1 := Finset.analyticAt_sum (𝕜 := ℂ)
          (f := fun i : ℕ => fun z : ℂ => U z ^ i * U₀ ^ (m' + 1 - 1 - i)) (Finset.range (m' + 1))
          (fun i _ => (hU.pow i).mul analyticAt_const)
        refine h1.congr (Eventually.of_forall fun z => ?_)
        simp only [hSdef, Finset.sum_apply]
      exact hSa.continuousAt
    have hRc := hR.continuousAt
    have hR'c := hR.deriv.continuousAt
    have hAc := hA.continuousAt
    have hv₁c := hv₁.continuousAt
    simp only [hEdef, hT₁def, hT₂def]
    fun_prop
  have hE0 := eq_zero_of_pow_sub_mul_eq_zero hEc hE
  -- but `E z₀ ≠ 0`
  have hE0' : E z₀ = R z₀ * A z₀ ^ 2 * U₀ ^ (m' + 2) * (2 * (j : ℂ) + m' + 5) := by
    simp only [hEdef, hT₁def, hT₂def, sub_self, zero_mul, add_zero, zero_pow (Nat.succ_ne_zero j)]
    rw [hS0, hv₁0]
    ring
  rw [hE0'] at hE0
  have h5 : (2 * (j : ℂ) + m' + 5) ≠ 0 := by
    have : ((2 * j + m' + 5 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast at this
    exact this
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hR0 (pow_ne_zero 2 hA0)) (pow_ne_zero _ hU₀)) h5) hE0

/-! ## Model trajectories

The three `IsHorizontalArc` statements below are pure arithmetic: in each case the product
`φ(c t) c'(t)²` collapses to a positive real multiple of a single unit-modulus factor, and the
two conditions `im = 0` and `0 < re` then say exactly that that factor is `1`.  The next two
lemmas isolate those steps. -/

/-- A complex number of modulus one whose imaginary part vanishes and whose real part is
positive equals `1`. -/
theorem eq_one_of_norm_one_of_im_zero_of_re_pos {w : ℂ} (hn : ‖w‖ = 1) (him : w.im = 0)
    (hre : 0 < w.re) : w = 1 := by
  have hw : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hw] at hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre] at hn
  rw [hw, hn, Complex.ofReal_one]

/-- Multiplying by a positive real changes neither the vanishing of the imaginary part nor the
positivity of the real part, so it does not affect being a horizontal direction. -/
theorem ofReal_mul_horizontal_iff {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (((x : ℂ) * w).im = 0 ∧ 0 < ((x : ℂ) * w).re) ↔ (w.im = 0 ∧ 0 < w.re) := by
  have him : ((x : ℂ) * w).im = x * w.im := by simp [Complex.mul_im]
  have hre : ((x : ℂ) * w).re = x * w.re := by simp [Complex.mul_re]
  rw [him, hre]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mul_eq_zero.1 h1).resolve_left hx.ne', ?_⟩
    nlinarith
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, mul_zero], mul_pos hx h2⟩

/-- The ray `t ↦ t A` has derivative `A`. -/
theorem hasDerivAt_ofReal_mul (A : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * A) A t := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const A

/-- The shifted ray `t ↦ (t + 1) A` has derivative `A`. -/
theorem hasDerivAt_ofReal_add_one_mul (A : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((s : ℂ) + 1) * A) A t := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).add_const (1 : ℂ)).mul_const A

/-- §25.1: local structure at a zero of order `m`: in the natural parameter, the ray
`{t e^{iθ} : t > 0}` is a horizontal trajectory arc of `((m+2)/2)² ζ^m dζ²` iff
`θ ≡ 2kπ/(m+2)`; so exactly `m + 2` horizontal trajectory arcs end at the zero, dividing a
neighbourhood into `m + 2` sectors of equal angle. -/
theorem zero_critical_trajectories {m : ℕ} (θ : ℝ) :
    IsHorizontalArc (fun ζ => ((m + 2 : ℂ) / 2) ^ 2 * ζ ^ m) (fun t => (t : ℂ) * exp (θ * I)) 0 1 ↔
      ∃ k : ℤ, θ = 2 * k * π / (m + 2) := by
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hm2C : ((m : ℂ) + 2) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.2 hm2
    push_cast at h
    exact h
  have hE0 : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hEn : ‖exp ((θ : ℂ) * I) ^ (m + 2)‖ = 1 := by
    rw [norm_pow, Complex.norm_exp_ofReal_mul_I θ, one_pow]
  have hd : ∀ t : ℝ, deriv (fun s : ℝ => (s : ℂ) * exp ((θ : ℂ) * I)) t = exp ((θ : ℂ) * I) :=
    fun t => (hasDerivAt_ofReal_mul _ t).deriv
  have hpow : exp ((θ : ℂ) * I) ^ (m + 2) = exp (((m : ℂ) + 2) * ((θ : ℂ) * I)) := by
    rw [show ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) by push_cast; ring, Complex.exp_nat_mul]
  -- for `t > 0` the product is a positive real multiple of `(e^{iθ})^{m+2}`
  have hprod : ∀ t : ℝ, 0 < t →
      ((m + 2 : ℂ) / 2) ^ 2 * ((t : ℂ) * exp ((θ : ℂ) * I)) ^ m * exp ((θ : ℂ) * I) ^ 2
        = (((((m : ℝ) + 2) / 2) ^ 2 * t ^ m : ℝ) : ℂ) * exp ((θ : ℂ) * I) ^ (m + 2) := by
    intro t _
    push_cast
    ring
  constructor
  · intro harc
    obtain ⟨-, -, -, him, hre⟩ := harc (1 / 2) (by norm_num)
    simp only [hd] at him hre
    rw [hprod (1 / 2) (by norm_num)] at him hre
    have hx : (0 : ℝ) < ((((m : ℝ) + 2) / 2) ^ 2 * (1 / 2 : ℝ) ^ m) := by positivity
    obtain ⟨him', hre'⟩ := (ofReal_mul_horizontal_iff hx _).1 ⟨him, hre⟩
    have h1 : exp (((m : ℂ) + 2) * ((θ : ℂ) * I)) = 1 := by
      rw [← hpow]
      exact eq_one_of_norm_one_of_im_zero_of_re_pos hEn him' hre'
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    refine ⟨n, ?_⟩
    have hn' : (((m : ℂ) + 2) * (θ : ℂ)) * I = ((n : ℂ) * (2 * (π : ℂ))) * I := by
      rw [show (((m : ℂ) + 2) * (θ : ℂ)) * I = ((m : ℂ) + 2) * ((θ : ℂ) * I) by ring, hn]
      ring
    have hn'' : ((m : ℂ) + 2) * (θ : ℂ) = (n : ℂ) * (2 * (π : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero hn'
    have hreal : ((m : ℝ) + 2) * θ = 2 * n * π := by
      have hcast : ((((m : ℝ) + 2) * θ : ℝ) : ℂ) = (((2 * n * π : ℝ)) : ℂ) := by
        push_cast
        linear_combination hn''
      exact_mod_cast hcast
    field_simp
    linarith [hreal]
  · rintro ⟨k, hk⟩
    have hE1 : exp ((θ : ℂ) * I) ^ (m + 2) = 1 := by
      rw [hpow]
      refine Complex.exp_eq_one_iff.2 ⟨k, ?_⟩
      rw [hk]
      push_cast
      field_simp
    intro t ht
    have ht0 : 0 < t := ht.1
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    refine ⟨(hasDerivAt_ofReal_mul _ t).differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [hd]; exact hE0
    · refine mul_ne_zero (pow_ne_zero 2 ?_) (pow_ne_zero m (mul_ne_zero htne hE0))
      exact div_ne_zero hm2C two_ne_zero
    · rw [hd, hprod t ht0, hE1, mul_one, Complex.ofReal_im]
    · rw [hd, hprod t ht0, hE1, mul_one, Complex.ofReal_re]
      positivity

/-- (25.7)–(25.8): at a simple pole there is a natural parameter with `φ dz² = ¼ ζ⁻¹ dζ²`. -/
theorem eq25_8_natural_parameter_simple_pole {φ : ℂ → ℂ} {z₀ : ℂ} {ψ : ℂ → ℂ}
    (hψ : AnalyticAt ℂ ψ z₀) (hψ0 : ψ z₀ ≠ 0) (hφ : ∀ᶠ z in 𝓝[≠] z₀, φ z = ψ z / (z - z₀)) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, φ z = (1 / 4) * (ζ z)⁻¹ * deriv ζ z ^ 2 := by
  obtain ⟨r, ξ, G, hr, hr0, hrq, hξ, hξ0, hξd, hG, hG0, hξG⟩ :=
    exists_natural_parameter_pullback hψ hψ0 0
  simp only [pow_zero, mul_one, zero_add, pow_one] at hξd hξG
  -- `ζ z = (z - z₀) G (z - z₀) ^ 2`
  set ζ : ℂ → ℂ := fun z => (z - z₀) * G (z - z₀) ^ 2 with hζdef
  have hGz : AnalyticAt ℂ (fun z => G (z - z₀)) z₀ :=
    hG.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  have hζ : AnalyticAt ℂ ζ z₀ := (analyticAt_id.sub analyticAt_const).mul (hGz.pow 2)
  have hζ0 : ζ z₀ = 0 := by simp [hζdef]
  have hζd0 : deriv ζ z₀ = G 0 ^ 2 := by
    have h : HasDerivAt ζ (((fun z => G (z - z₀)) ^ 2) z₀) z₀ :=
      hasDerivAt_sub_mul ((hGz.pow 2).differentiableAt)
    rw [h.deriv]
    simp
  -- `ξ` does not vanish near `0` (its derivative at `0` is `2 r 0 ≠ 0`)
  have hξne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ξ w ≠ 0 := by
    rcases hξ.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have h1 : deriv ξ 0 = 0 := by
        rw [Filter.EventuallyEq.deriv_eq (h : ξ =ᶠ[𝓝 (0 : ℂ)] fun _ => 0), deriv_const]
      rw [hξd.self_of_nhds.deriv] at h1
      simp [hr0] at h1
    · exact h
  -- a radius `ε` for the facts about `ξ` and `G`, and a radius `ε'` for the analyticity of `ζ`
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.1 (hξd.and (hξG.and (eventually_nhdsWithin_iff.1 hξne)))
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.1 hζ.eventually_analyticAt
  -- `ζ (z₀ + v²) = ξ v ^ 2` for `‖v‖ < ε`
  have hζξ : ∀ v : ℂ, dist v 0 < ε → ζ (z₀ + v ^ 2) = ξ v ^ 2 := by
    intro v hv
    obtain ⟨-, hv2, -⟩ := hball hv
    simp only [hζdef, add_sub_cancel_left]
    rw [hv2]
    ring
  refine ⟨ζ, hζ, hζ0, ?_, ?_⟩
  · rw [hζd0]
    exact pow_ne_zero 2 hG0
  · set δ : ℝ := min (ε ^ 2) ε' with hδ
    have hδ0 : 0 < δ := lt_min (pow_pos hε 2) hε'
    filter_upwards [hφ, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hδ0),
      self_mem_nhdsWithin] with z hφz hzδ hz0
    have hz0' : z ≠ z₀ := hz0
    have hzδ' : ‖z - z₀‖ < δ := by rwa [mem_ball, dist_eq_norm] at hzδ
    -- the square root `w` of `z - z₀`
    set w : ℂ := (z - z₀) ^ ((1 / 2 : ℝ) : ℂ) with hw
    have hw2 : w ^ 2 = z - z₀ := cpow_half_sq _
    have hwn : ‖w‖ = Real.sqrt ‖z - z₀‖ := norm_cpow_half _
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, zero_pow two_ne_zero] at hw2
      exact hz0' (sub_eq_zero.1 hw2.symm)
    have hwε : dist w 0 < ε := by
      rw [dist_zero_right, hwn, Real.sqrt_lt' hε]
      exact lt_of_lt_of_le hzδ' (min_le_left _ _)
    obtain ⟨hξdw, -, hξnew⟩ := hball hwε
    have hξw : ξ w ≠ 0 := hξnew hw0
    have hz_eq : z = z₀ + w ^ 2 := by rw [hw2]; ring
    have hζan : AnalyticAt ℂ ζ z := hball' (by
      rw [dist_eq_norm]
      exact lt_of_lt_of_le hzδ' (min_le_right _ _))
    -- the chain rule along `v ↦ z₀ + v²`
    have hchain : HasDerivAt (fun v => ζ (z₀ + v ^ 2)) (deriv ζ z * (2 * w)) w := by
      have h1 : HasDerivAt (fun v : ℂ => z₀ + v ^ 2) (2 * w) w := by
        have := (hasDerivAt_pow 2 w).const_add z₀
        simpa using this
      exact HasDerivAt.comp_of_eq w hζan.differentiableAt.hasDerivAt h1 hz_eq
    have hev : (fun v => ζ (z₀ + v ^ 2)) =ᶠ[𝓝 w] fun v => ξ v ^ 2 := by
      have : ∀ᶠ v in 𝓝 w, dist v 0 < ε :=
        Metric.isOpen_ball.mem_nhds (by rw [mem_ball]; exact hwε)
      filter_upwards [this] with v hv
      exact hζξ v hv
    have hderiv : deriv ζ z * (2 * w) = 2 * ξ w * (2 * r w) := by
      have h1 : HasDerivAt (fun v => ξ v ^ 2) (↑(2 : ℕ) * ξ w ^ (2 - 1) * (2 * r w)) w := hξdw.pow 2
      have h2 := hchain.congr_of_eventuallyEq hev.symm
      rw [h2.unique h1]
      push_cast
      ring
    have hζz : ζ z = ξ w ^ 2 := by
      rw [hz_eq]
      exact hζξ w hwε
    have hdz : deriv ζ z = 2 * ξ w * r w / w := by
      field_simp
      linear_combination hderiv / 2
    have hψz : ψ z = r w ^ 2 := by rw [hrq w, ← hz_eq]
    rw [hφz, hζz, hdz, hψz, ← hw2]
    field_simp
    ring

/-- §25.1: at a simple pole exactly one horizontal trajectory arc ends at the pole: for
`¼ ζ⁻¹ dζ²` the ray `{t e^{iθ}}` is horizontal iff `θ ∈ 2πℤ`. -/
theorem simple_pole_trajectory (θ : ℝ) :
    IsHorizontalArc (fun ζ => (1 / 4) * ζ⁻¹) (fun t => (t : ℂ) * exp (θ * I)) 0 1 ↔
      ∃ k : ℤ, θ = 2 * k * π := by
  have hE0 : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hEn : ‖exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hd : ∀ t : ℝ, deriv (fun s : ℝ => (s : ℂ) * exp ((θ : ℂ) * I)) t = exp ((θ : ℂ) * I) :=
    fun t => (hasDerivAt_ofReal_mul _ t).deriv
  -- for `t > 0` the product is a positive real multiple of `e^{iθ}`
  have hprod : ∀ t : ℝ, 0 < t →
      (1 / 4 : ℂ) * ((t : ℂ) * exp ((θ : ℂ) * I))⁻¹ * exp ((θ : ℂ) * I) ^ 2
        = ((1 / (4 * t) : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
    intro t ht
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp
  constructor
  · intro harc
    obtain ⟨-, -, -, him, hre⟩ := harc (1 / 2) (by norm_num)
    simp only [hd] at him hre
    rw [hprod (1 / 2) (by norm_num)] at him hre
    obtain ⟨him', hre'⟩ :=
      (ofReal_mul_horizontal_iff (by norm_num : (0:ℝ) < 1 / (4 * (1/2 : ℝ))) _).1 ⟨him, hre⟩
    obtain ⟨n, hn⟩ :=
      Complex.exp_eq_one_iff.1 (eq_one_of_norm_one_of_im_zero_of_re_pos hEn him' hre')
    refine ⟨n, ?_⟩
    have hn' : ((θ : ℝ) : ℂ) * I = ((n : ℂ) * (2 * (π : ℂ))) * I := by
      rw [hn]; ring
    have hn'' : ((θ : ℝ) : ℂ) = (n : ℂ) * (2 * (π : ℂ)) :=
      mul_right_cancel₀ Complex.I_ne_zero hn'
    have hcast : ((θ : ℝ) : ℂ) = ((2 * n * π : ℝ) : ℂ) := by
      rw [hn'']; push_cast; ring
    exact_mod_cast hcast
  · rintro ⟨k, rfl⟩
    have hE1 : exp (((2 * (k : ℝ) * π : ℝ) : ℂ) * I) = 1 := by
      refine Complex.exp_eq_one_iff.2 ⟨k, ?_⟩
      push_cast
      ring
    intro t ht
    have ht0 : 0 < t := ht.1
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    refine ⟨(hasDerivAt_ofReal_mul _ t).differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [hd]; exact hE0
    · exact mul_ne_zero (by norm_num) (inv_ne_zero (mul_ne_zero htne hE0))
    · rw [hd, hprod t ht0, hE1, mul_one, Complex.ofReal_im]
    · rw [hd, hprod t ht0, hE1, mul_one, Complex.ofReal_re]
      positivity

/-- (25.9): at a double pole with leading coefficient `a₋₂` (independent of the parameter) there
is a natural parameter with `φ dz² = a₋₂ ζ⁻² dζ²`. -/
theorem eq25_9_natural_parameter_double_pole {φ : ℂ → ℂ} {z₀ : ℂ} {ψ : ℂ → ℂ}
    (hψ : AnalyticAt ℂ ψ z₀) (hψ0 : ψ z₀ ≠ 0) (hφ : ∀ᶠ z in 𝓝[≠] z₀, φ z = ψ z / (z - z₀) ^ 2) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ z₀ ∧ ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, φ z = ψ z₀ * (ζ z)⁻¹ ^ 2 * deriv ζ z ^ 2 := by
  -- an analytic square root `r` of `ψ / ψ z₀` with `r z₀ = 1`
  have hq : AnalyticAt ℂ (fun z => ψ z / ψ z₀) z₀ := hψ.div analyticAt_const hψ0
  have hq0 : (fun z => ψ z / ψ z₀) z₀ ≠ 0 := by simp [div_self hψ0]
  obtain ⟨r, hr, hr1, hrq⟩ :
      ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = 1 ∧ ∀ z, r z ^ 2 = ψ z / ψ z₀ := by
    obtain ⟨r, hr, -, hrq, -⟩ := exists_analyticAt_sq_eq hq hq0
    have h1 : r z₀ ^ 2 = 1 ^ 2 := by
      rw [hrq]
      simp [div_self hψ0]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact ⟨r, hr, h, hrq⟩
    · refine ⟨fun z => -r z, hr.neg, by simp [h], fun z => ?_⟩
      rw [neg_sq]
      exact hrq z
  -- the difference quotient of `r` and its primitive `G`; `ζ z = (z - z₀) exp (G z)`
  have hd : AnalyticAt ℂ (dslope r z₀) z₀ := analyticAt_dslope hr
  obtain ⟨G, hG, hG0, hGd⟩ := exists_primitive_analyticAt hd
  set ζ : ℂ → ℂ := fun z => (z - z₀) * exp (G z) with hζdef
  have hζ : AnalyticAt ℂ ζ z₀ := (analyticAt_id.sub analyticAt_const).mul hG.cexp
  have hζ0 : ζ z₀ = 0 := by simp [hζdef]
  have hζd : ∀ᶠ z in 𝓝 z₀,
      HasDerivAt ζ (1 * exp (G z) + (z - z₀) * (exp (G z) * dslope r z₀ z)) z := by
    filter_upwards [hGd] with z hz
    exact ((hasDerivAt_id z).sub_const z₀).mul hz.cexp
  refine ⟨ζ, hζ, hζ0, ?_, ?_⟩
  · rw [hζd.self_of_nhds.deriv, hG0]
    simp
  · filter_upwards [hφ, hζd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hφz hz hz0
    have hz0' : z ≠ z₀ := hz0
    have hzz : z - z₀ ≠ 0 := sub_ne_zero.2 hz0'
    have hds : dslope r z₀ z = (r z - 1) / (z - z₀) := by
      rw [dslope_of_ne r hz0', slope_def_field, hr1]
    have hdz : deriv ζ z = exp (G z) * r z := by
      rw [hz.deriv, hds]
      field_simp
      ring
    have hζz : ζ z = (z - z₀) * exp (G z) := rfl
    have hex : exp (G z) ≠ 0 := Complex.exp_ne_zero _
    rw [hφz, hdz, hζz, mul_pow, hrq]
    field_simp

/-- §25.1, Figure 7.25.3: for `a₋₂ ζ⁻² dζ²` with `a₋₂ < 0` the circles `|ζ| = r` are closed
horizontal trajectories; with `a₋₂ > 0` the rays from `0` are horizontal trajectories. -/
theorem double_pole_trajectories {a : ℝ} (ha : a ≠ 0) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (a < 0 → IsHorizontalArc (fun ζ => (a : ℂ) * ζ⁻¹ ^ 2) (fun t => (r : ℂ) * exp (2 * π * t * I)) 0 1) ∧
      (0 < a → IsHorizontalArc (fun ζ => (a : ℂ) * ζ⁻¹ ^ 2) (fun t => (t + 1 : ℂ) * exp (θ * I)) 0 1) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · -- circles `|ζ| = r`: the `t`-dependence cancels and the product is the constant `-4π²a`
    have hdc : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (r : ℂ) * exp (2 * (π : ℂ) * (s : ℂ) * I))
        ((r : ℂ) * (exp (2 * (π : ℂ) * (t : ℂ) * I) * (2 * (π : ℂ) * I))) t := by
      intro t
      have hlin : HasDerivAt (fun s : ℝ => 2 * (π : ℂ) * (s : ℂ) * I) (2 * (π : ℂ) * I) t := by
        have hfun : (fun s : ℝ => 2 * (π : ℂ) * (s : ℂ) * I)
            = fun s : ℝ => (s : ℂ) * (2 * (π : ℂ) * I) := by
          funext s; ring
        rw [hfun]
        exact hasDerivAt_ofReal_mul (2 * (π : ℂ) * I) t
      exact hlin.cexp.const_mul (r : ℂ)
    intro t _
    have hEne : exp (2 * (π : ℂ) * (t : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have hx : ((r : ℂ) * exp (2 * (π : ℂ) * (t : ℂ) * I)) ≠ 0 := mul_ne_zero hrne hEne
    have hderiv := (hdc t).deriv
    have key : (((r : ℂ) * exp (2 * (π : ℂ) * (t : ℂ) * I))⁻¹) ^ 2
        * ((r : ℂ) * (exp (2 * (π : ℂ) * (t : ℂ) * I) * (2 * (π : ℂ) * I))) ^ 2
        = (2 * (π : ℂ) * I) ^ 2 := by
      rw [show (r : ℂ) * (exp (2 * (π : ℂ) * (t : ℂ) * I) * (2 * (π : ℂ) * I))
            = ((r : ℂ) * exp (2 * (π : ℂ) * (t : ℂ) * I)) * (2 * (π : ℂ) * I) from by ring,
        mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, one_mul]
    have hval : (a : ℂ) * (((r : ℂ) * exp (2 * (π : ℂ) * (t : ℂ) * I))⁻¹) ^ 2
        * ((r : ℂ) * (exp (2 * (π : ℂ) * (t : ℂ) * I) * (2 * (π : ℂ) * I))) ^ 2
        = ((-4 * π ^ 2 * a : ℝ) : ℂ) := by
      rw [mul_assoc, key]
      push_cast
      linear_combination (4 * (π : ℂ) ^ 2 * (a : ℂ)) * Complex.I_sq
    refine ⟨(hdc t).differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [hderiv]
      refine mul_ne_zero hrne (mul_ne_zero hEne ?_)
      exact mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero
    · exact mul_ne_zero hane (pow_ne_zero 2 (inv_ne_zero hx))
    · rw [hderiv, hval, Complex.ofReal_im]
    · rw [hderiv, hval, Complex.ofReal_re]
      have hp : (0 : ℝ) < π ^ 2 := by positivity
      nlinarith
  · -- rays from `0`, for every direction `θ`
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : (0 : ℝ) < t + 1 := by linarith
    have hE0 : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have htne : ((t : ℂ) + 1) ≠ 0 := by
      have h := Complex.ofReal_ne_zero.2 ht1.ne'
      push_cast at h
      exact h
    have hderiv := (hasDerivAt_ofReal_add_one_mul (exp ((θ : ℂ) * I)) t).deriv
    have hval : (a : ℂ) * ((((t : ℂ) + 1) * exp ((θ : ℂ) * I))⁻¹) ^ 2 * exp ((θ : ℂ) * I) ^ 2
        = ((a / (t + 1) ^ 2 : ℝ) : ℂ) := by
      push_cast
      field_simp
    refine ⟨(hasDerivAt_ofReal_add_one_mul _ t).differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [hderiv]; exact hE0
    · exact mul_ne_zero hane (pow_ne_zero 2 (inv_ne_zero (mul_ne_zero htne hE0)))
    · rw [hderiv, hval, Complex.ofReal_im]
    · rw [hderiv, hval, Complex.ofReal_re]
      positivity

/-! ## §25.2 The metric induced by a quadratic differential -/

/-- The `φ`-metric density `|φ|^{1/2}` (25.11). -/
def phiDensity (φ : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ‖φ z‖)

/-- The `φ`-length `l_φ(γ) = ∫_γ |φ|^{1/2} |dz|`. -/
def phiLength (φ : ℂ → ℂ) (γ : LRCurve) : ℝ≥0∞ := γ.rhoLength (phiDensity φ)

/-- The `φ`-area `A_φ(D) = ∬_D |φ| dx dy`. -/
def phiArea (φ : ℂ → ℂ) (D : Set ℂ) : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal ‖φ z‖

/-- `|φ| dx dy` is invariant under conformal changes of parameter:
`A_φ(D) = A_ψ(h(D))` when `φ = (ψ ∘ h) h'²`. -/
theorem phiArea_conformal_invariant {φ ψ h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hh : IsConformalOnto h D (h '' D)) (hφ : ∀ z ∈ D, φ z = ψ (h z) * deriv h z ^ 2) :
    phiArea φ D = phiArea ψ (h '' D) := by
  simp only [phiArea]
  rw [lintegral_image_conformal hD hh (fun w => ENNReal.ofReal ‖ψ w‖)]
  refine setLIntegral_congr_fun hD.measurableSet fun z hz => ?_
  rw [hφ z hz, norm_mul, norm_pow, ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm, mul_comm]

/-- `c : [a, b] → ℂ` is a `φ`-straight arc (`φ` 直线弧): `arg(φ dz²)` is constant along `c`. -/
def IsPhiStraightArc (φ : ℂ → ℂ) (c : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ θ : ℝ, ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
    φ (c t) * deriv c t ^ 2 ≠ 0 ∧ arg (φ (c t) * deriv c t ^ 2 * exp (-θ * I)) = 0

/-- Horizontal and vertical trajectory arcs are `φ`-straight arcs. -/
theorem horizontal_vertical_isPhiStraight {φ : ℂ → ℂ} {c : ℝ → ℂ} {a b : ℝ} :
    (IsHorizontalArc φ c a b → IsPhiStraightArc φ c a b) ∧
      (IsVerticalArc φ c a b → IsPhiStraightArc φ c a b) := by
  constructor
  · intro h
    refine ⟨0, fun t ht => ?_⟩
    obtain ⟨hd, hd0, hφ0, him, hre⟩ := h t ht
    refine ⟨hd, hd0, mul_ne_zero hφ0 (pow_ne_zero 2 hd0), ?_⟩
    rw [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one,
      Complex.arg_eq_zero_iff]
    exact ⟨hre.le, him⟩
  · intro h
    refine ⟨π, fun t ht => ?_⟩
    obtain ⟨hd, hd0, hφ0, him, hre⟩ := h t ht
    refine ⟨hd, hd0, mul_ne_zero hφ0 (pow_ne_zero 2 hd0), ?_⟩
    have hexp : Complex.exp (-(π : ℂ) * I) = -1 := by
      rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    rw [hexp, mul_neg_one, Complex.arg_eq_zero_iff, Complex.neg_re, Complex.neg_im, him, neg_zero]
    exact ⟨by linarith, rfl⟩

/-- The `φ`-length of the part `γ|[s, t]` of a curve. -/
def phiSegmentLength (φ : ℂ → ℂ) (γ : LRCurve) (s t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioo s t, phiDensity φ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ

/-! ### Helpers for `local_shortest_regular` (`psa_`): the natural parameter as a chart

Near a regular point the natural parameter `ζ` (`eq25_2_natural_parameter`) is injective on a
closed disc `B̄ = closedBall z₀ r ⊆ D` with `ζ'² = φ` and `ζ' ≠ 0`; its inverse `ψ` on the open
image `ζ(B)` is holomorphic with `ψ' = 1/(ζ' ∘ ψ)`.  In the coordinate `ζ` the `φ`-length of a
curve is its Euclidean length: the pulled-back straight segment is `φ`-straight with `φ`-length
`|ζ z₂ - ζ z₁|`; a curve staying in `B̄` is at least as long (fundamental theorem of calculus for
the Lipschitz function `Re(ū · ζ ∘ σ)`); and a curve leaving `B̄` has `φ`-length at least
`ρ - ρ/3 > |ζ z₂ - ζ z₁|` when `ball 0 ρ ⊆ ζ(B)` and `ζ z₁, ζ z₂ ∈ ball 0 (ρ/3)`. -/

/-- The chart: a closed disc around a regular point on which the natural parameter is
injective and analytic, with `ζ'² = φ` and `ζ' ≠ 0`. -/
theorem psa_chart {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hφ : DifferentiableOn ℂ φ D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (h0 : φ z₀ ≠ 0) :
    ∃ (ζ : ℂ → ℂ) (r : ℝ), 0 < r ∧ closedBall z₀ r ⊆ D ∧ ζ z₀ = 0 ∧
      InjOn ζ (closedBall z₀ r) ∧
      ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0 := by
  obtain ⟨ζ, hζ, hζ0, hζ'0, hζφ⟩ :=
    eq25_2_natural_parameter (hφ.analyticAt (hD.mem_nhds hz₀)) h0
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ᶠ x in 𝓝 z₀, g (ζ x) = x :=
    ⟨_, hζ.hasStrictDerivAt.eventually_left_inverse hζ'0⟩
  have hφne : ∀ᶠ z in 𝓝 z₀, φ z ≠ 0 :=
    (hφ.continuousOn.continuousAt (hD.mem_nhds hz₀)).eventually_ne h0
  have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ φ z ≠ 0 ∧ z ∈ D ∧
      g (ζ z) = z := by
    filter_upwards [hζ.eventually_analyticAt, hζφ, hφne, hD.mem_nhds hz₀, hg]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  have hmem : ∀ z ∈ closedBall z₀ (ε / 2), dist z z₀ < ε := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)
  refine ⟨ζ, ε / 2, by positivity, fun z hz => (hball (hmem z hz)).2.2.2.1, hζ0, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' := (hball (hmem x hx)).2.2.2.2
    have hy' := (hball (hmem y hy)).2.2.2.2
    rw [← hx', ← hy', hxy]
  · intro z hz
    obtain ⟨h1, h2, h3, -, -⟩ := hball (hmem z hz)
    refine ⟨h1, h2, fun h => h3 ?_⟩
    rw [← h2, h, zero_pow two_ne_zero]

/-- The inverse chart `ψ = ζ⁻¹` on the open image `ζ(B)`: it maps into `B`, is a right inverse
of `ζ`, and is holomorphic with `ψ' = 1/(ζ' ∘ ψ)`. -/
theorem psa_inverse {ζ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0) :
    IsOpen (ζ '' ball z₀ r) ∧
      ∀ w ∈ ζ '' ball z₀ r, Function.invFunOn ζ (ball z₀ r) w ∈ ball z₀ r ∧
        ζ (Function.invFunOn ζ (ball z₀ r) w) = w ∧
        HasDerivAt (Function.invFunOn ζ (ball z₀ r))
          (deriv ζ (Function.invFunOn ζ (ball z₀ r) w))⁻¹ w := by
  have hsub : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  have hanb : AnalyticOnNhd ℂ ζ (ball z₀ r) := fun z hz => (han z (hsub hz)).1
  have hopen : IsOpen (ζ '' ball z₀ r) := by
    rcases hanb.is_constant_or_isOpen isPreconnected_ball with ⟨c, hc⟩ | hop
    · exfalso
      have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
      have hev : ζ =ᶠ[𝓝 z₀] fun _ => c := by
        filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz using hc z hz
      exact (han z₀ (hsub hz₀)).2 (by rw [hev.deriv_eq, deriv_const])
    · exact hop _ subset_rfl isOpen_ball
  refine ⟨hopen, fun w hw => ?_⟩
  have hconf : IsConformalOnto ζ (ball z₀ r) (ζ '' ball z₀ r) :=
    ⟨fun z hz => (hanb z hz).differentiableAt.differentiableWithinAt, hinj.mono hsub, rfl⟩
  have hsymm := hconf.symm isOpen_ball
  have hmem : Function.invFunOn ζ (ball z₀ r) w ∈ ball z₀ r := hsymm.mapsTo hw
  have hζψ : ζ (Function.invFunOn ζ (ball z₀ r) w) = w := Function.invFunOn_eq hw
  have hψd : DifferentiableAt ℂ (Function.invFunOn ζ (ball z₀ r)) w :=
    hsymm.1.differentiableAt (hopen.mem_nhds hw)
  have hζd : HasDerivAt ζ (deriv ζ (Function.invFunOn ζ (ball z₀ r) w))
      (Function.invFunOn ζ (ball z₀ r) w) :=
    (han _ (hsub hmem)).1.differentiableAt.hasDerivAt
  have hcomp := hζd.comp w hψd.hasDerivAt
  have hid : id =ᶠ[𝓝 w] ζ ∘ Function.invFunOn ζ (ball z₀ r) := by
    filter_upwards [hopen.mem_nhds hw] with y hy
    exact (Function.invFunOn_eq hy).symm
  have hone : deriv ζ (Function.invFunOn ζ (ball z₀ r) w) *
      deriv (Function.invFunOn ζ (ball z₀ r)) w = 1 := by
    have h := (hcomp.congr_of_eventuallyEq hid).deriv
    rw [deriv_id] at h
    exact h.symm
  refine ⟨hmem, hζψ, ?_⟩
  have hval : deriv (Function.invFunOn ζ (ball z₀ r)) w =
      (deriv ζ (Function.invFunOn ζ (ball z₀ r) w))⁻¹ := eq_inv_of_mul_eq_one_right hone
  rw [← hval]
  exact hψd.hasDerivAt

/-- The pulled-back straight segment: a `φ`-straight path in `D` from `ψ w₁` to `ψ w₂` of
`φ`-length `|w₂ - w₁|`. -/
theorem psa_segment {φ ζ ψ : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} {r ρ : ℝ} (hr : 0 < r)
    (hBD : closedBall z₀ r ⊆ D)
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0)
    (hψ : ∀ w ∈ ζ '' ball z₀ r, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hρB : ball 0 ρ ⊆ ζ '' ball z₀ r) {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ ball 0 ρ) (hw₂ : w₂ ∈ ball 0 ρ)
    (hne : w₁ ≠ w₂) :
    ∃ γ : LRCurve, IsPathIn D (ψ w₁) (ψ w₂) γ ∧ IsPhiStraightArc φ γ.toFun 0 1 ∧
      phiLength φ γ = ENNReal.ofReal ‖w₂ - w₁‖ := by
  have hsub : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  have hne' : w₂ - w₁ ≠ 0 := sub_ne_zero.2 hne.symm
  -- the segment in the chart
  have hℓmem : ∀ t ∈ Icc (0 : ℝ) 1, w₁ + (t : ℂ) * (w₂ - w₁) ∈ ball 0 ρ := fun t ht => by
    rw [← Complex.real_smul]
    exact (convex_ball (0 : ℂ) ρ).add_smul_sub_mem hw₁ hw₂ ht
  have hℓd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w₁ + (s : ℂ) * (w₂ - w₁)) (w₂ - w₁) t :=
    fun t => by simpa using ((hasDerivAt_id' t).ofReal_comp.mul_const (w₂ - w₁)).const_add w₁
  set f : ℝ → ℂ := fun t => ψ (w₁ + (t : ℂ) * (w₂ - w₁)) with hfdef
  have hfmem : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ ball z₀ r := fun t ht =>
    (hψ _ (hρB (hℓmem t ht))).1
  have hfd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f ((w₂ - w₁) * (deriv ζ (f t))⁻¹) t :=
    fun t ht => by
      have h := (hψ _ (hρB (hℓmem t ht))).2.2.scomp t (hℓd t)
      simp only [smul_eq_mul] at h
      exact h
  have hfne : ∀ t ∈ Icc (0 : ℝ) 1, deriv ζ (f t) ≠ 0 := fun t ht =>
    (han _ (hsub (hfmem t ht))).2.2
  -- a uniform Lipschitz bound from a positive lower bound of `|ζ'|` on the closed disc
  have hζc : ContinuousOn (fun z => ‖deriv ζ z‖) (closedBall z₀ r) := fun z hz =>
    ((han z hz).1.deriv.continuousAt.norm).continuousWithinAt
  obtain ⟨zm, hzm, hzmin⟩ := (isCompact_closedBall z₀ r).exists_isMinOn
    ⟨z₀, mem_closedBall_self hr.le⟩ hζc
  have hcpos : 0 < ‖deriv ζ zm‖ := norm_pos_iff.2 (han zm hzm).2.2
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(w₂ - w₁) * (deriv ζ (f t))⁻¹‖ ≤ ‖w₂ - w₁‖ / ‖deriv ζ zm‖ := fun t ht => by
    rw [norm_mul, norm_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hcpos (hzmin (hsub (hfmem t ht))))
      (norm_nonneg _)
  have hM0 : 0 ≤ ‖w₂ - w₁‖ / ‖deriv ζ zm‖ := by positivity
  have hLip : LipschitzOnWith (Real.toNNReal (‖w₂ - w₁‖ / ‖deriv ζ zm‖)) f (Icc 0 1) := by
    refine (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun t => (w₂ - w₁) * (deriv ζ (f t))⁻¹)
      (fun t ht => (hfd t ht).hasDerivWithinAt) ?_
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0]
    exact hbound t ht
  have hlocLip : LocallyLipschitzOn (Ioo 0 1) f := fun t ht =>
    ⟨_, Icc 0 1, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hLip⟩
  refine ⟨⟨f, hlocLip⟩, ⟨⟨_, hLip⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show ψ (w₁ + ((0 : ℝ) : ℂ) * (w₂ - w₁)) = ψ w₁
    simp
  · show ψ (w₁ + ((1 : ℝ) : ℂ) * (w₂ - w₁)) = ψ w₂
    simp
  · rintro _ ⟨t, ht, rfl⟩
    exact hBD (hsub (hfmem t ht))
  · -- `φ`-straight: `φ(f t) f'(t)² = (w₂ - w₁)²` is constant
    refine ⟨arg ((w₂ - w₁) ^ 2), fun t ht => ?_⟩
    show DifferentiableAt ℝ f t ∧ deriv f t ≠ 0 ∧ φ (f t) * deriv f t ^ 2 ≠ 0 ∧
      arg (φ (f t) * deriv f t ^ 2 * exp (-(arg ((w₂ - w₁) ^ 2) : ℂ) * I)) = 0
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hd := hfd t ht'
    have hζne := hfne t ht'
    have hsq : φ (f t) * deriv f t ^ 2 = (w₂ - w₁) ^ 2 := by
      rw [hd.deriv, ← (han _ (hsub (hfmem t ht'))).2.1]
      field_simp
    have hx : (w₂ - w₁) ^ 2 ≠ 0 := pow_ne_zero 2 hne'
    refine ⟨hd.differentiableAt, ?_, ?_, ?_⟩
    · rw [hd.deriv]
      exact mul_ne_zero hne' (inv_ne_zero hζne)
    · rw [hsq]; exact hx
    · rw [hsq]
      have key : (w₂ - w₁) ^ 2 * exp (-(arg ((w₂ - w₁) ^ 2) : ℂ) * I) =
          (‖(w₂ - w₁) ^ 2‖ : ℂ) := by
        calc (w₂ - w₁) ^ 2 * exp (-(arg ((w₂ - w₁) ^ 2) : ℂ) * I)
            = (‖(w₂ - w₁) ^ 2‖ : ℂ) * exp ((arg ((w₂ - w₁) ^ 2) : ℂ) * I) *
                exp (-(arg ((w₂ - w₁) ^ 2) : ℂ) * I) := by
              rw [Complex.norm_mul_exp_arg_mul_I]
          _ = (‖(w₂ - w₁) ^ 2‖ : ℂ) := by
              rw [mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero,
                mul_one]
      rw [key]
      exact Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  · -- the `φ`-length is the Euclidean length of the segment
    show ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity φ (f t) * ‖deriv f t‖ₑ = ENNReal.ofReal ‖w₂ - w₁‖
    have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
        phiDensity φ (f t) * ‖deriv f t‖ₑ = ENNReal.ofReal ‖w₂ - w₁‖ := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      have hζne : ‖deriv ζ (f t)‖ ≠ 0 := norm_ne_zero_iff.2 (hfne t ht')
      have hφ : ‖φ (f t)‖ = ‖deriv ζ (f t)‖ ^ 2 := by
        rw [← (han _ (hsub (hfmem t ht'))).2.1, norm_pow]
      rw [phiDensity, hφ, Real.sqrt_sq (norm_nonneg _), (hfd t ht').deriv, ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg _), norm_mul, norm_inv]
      congr 1
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt, setLIntegral_const, Real.volume_Ioo,
      sub_zero, ENNReal.ofReal_one, mul_one]

/-- Fundamental theorem of calculus in the chart: a Lipschitz curve staying in the closed disc up
to time `τ` has `φ`-length up to `τ` at least `|ζ(σ τ) - ζ(σ 0)|`. -/
theorem psa_chord_le {φ ζ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0)
    {σ : ℝ → ℂ} {K : ℝ≥0} (hσ : LipschitzOnWith K σ (Icc 0 1)) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (hmaps : ∀ t ∈ Icc 0 τ, σ t ∈ closedBall z₀ r) :
    ENNReal.ofReal ‖ζ (σ τ) - ζ (σ 0)‖ ≤
      ∫⁻ t in Ioo 0 τ, phiDensity φ (σ t) * ‖deriv σ t‖ₑ := by
  have hIcc : Icc (0 : ℝ) τ ⊆ Icc 0 1 := Icc_subset_Icc_right hτ1
  -- `ζ` is Lipschitz on the closed disc
  have hζc : ContinuousOn (fun z => ‖deriv ζ z‖) (closedBall z₀ r) := fun z hz =>
    ((han z hz).1.deriv.continuousAt.norm).continuousWithinAt
  obtain ⟨L, hL⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn hζc
  have hζL : LipschitzOnWith (Real.toNNReal L) ζ (closedBall z₀ r) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun z hz => (han z hz).1.differentiableAt)
      ?_ (convex_closedBall z₀ r)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_max_of_le_left (by simpa using hL z hz)
  -- the direction `u` of the chord and the real function `G = Re(ū ζ ∘ σ)`
  by_cases hΔ0 : ζ (σ τ) - ζ (σ 0) = 0
  · rw [hΔ0, norm_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hΔn : 0 < ‖ζ (σ τ) - ζ (σ 0)‖ := norm_pos_iff.2 hΔ0
  set u : ℂ := (ζ (σ τ) - ζ (σ 0)) / (‖ζ (σ τ) - ζ (σ 0)‖ : ℂ) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔn.le, div_self hΔn.ne']
  have hcu : conj u * (ζ (σ τ) - ζ (σ 0)) = (‖ζ (σ τ) - ζ (σ 0)‖ : ℂ) := by
    have hΔc : (‖ζ (σ τ) - ζ (σ 0)‖ : ℂ) ≠ 0 := by exact_mod_cast hΔn.ne'
    rw [hu, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq,
      mul_div_assoc, div_self hΔc, mul_one]
  set G : ℝ → ℝ := fun t => (conj u * ζ (σ t)).re with hG
  have hGL : LipschitzOnWith (Real.toNNReal L * K) G (Icc 0 τ) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    rw [Real.dist_eq]
    calc |(conj u * ζ (σ s)).re - (conj u * ζ (σ t)).re|
        = |(conj u * (ζ (σ s) - ζ (σ t))).re| := by rw [mul_sub, Complex.sub_re]
      _ ≤ ‖conj u * (ζ (σ s) - ζ (σ t))‖ := Complex.abs_re_le_norm _
      _ = ‖ζ (σ s) - ζ (σ t)‖ := by rw [norm_mul, Complex.norm_conj, hu1, one_mul]
      _ = dist (ζ (σ s)) (ζ (σ t)) := (Complex.dist_eq _ _).symm
      _ ≤ (Real.toNNReal L : ℝ) * dist (σ s) (σ t) :=
          hζL.dist_le_mul _ (hmaps s hs) _ (hmaps t ht)
      _ ≤ (Real.toNNReal L : ℝ) * ((K : ℝ) * dist s t) := by
          gcongr
          exact hσ.dist_le_mul _ (hIcc hs) _ (hIcc ht)
      _ = ((Real.toNNReal L * K : ℝ≥0) : ℝ) * dist s t := by push_cast; ring
  have hGac : AbsolutelyContinuousOnInterval G 0 τ := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal L * K)
    rw [uIcc_of_le hτ0.le]
    exact hGL
  have hFTC : ∫ t in (0 : ℝ)..τ, deriv G t = ‖ζ (σ τ) - ζ (σ 0)‖ := by
    rw [hGac.integral_deriv_eq_sub]
    show (conj u * ζ (σ τ)).re - (conj u * ζ (σ 0)).re = ‖ζ (σ τ) - ζ (σ 0)‖
    rw [← Complex.sub_re, ← mul_sub, hcu, Complex.ofReal_re]
  -- the pointwise comparison `|G'| ≤ |ζ'(σ)| |σ'|` almost everywhere
  have hσae : ∀ᵐ t, t ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ σ t :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le zero_le_one]; exact hσ)
  have hae : ∀ᵐ t, t ∈ Ioc (0 : ℝ) τ →
      ‖deriv G t‖ₑ ≤ phiDensity φ (σ t) * ‖deriv σ t‖ₑ := by
    filter_upwards [hσae, hGac.ae_differentiableAt] with t hσt hGt ht
    have ht1 : t ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le, ht.2.trans hτ1⟩
    have hσm : σ t ∈ closedBall z₀ r := hmaps t (Ioc_subset_Icc_self ht)
    obtain ⟨hζa, hζφ, hζne⟩ := han _ hσm
    have hd1 : HasDerivAt σ (deriv σ t) t := (hσt ht1).hasDerivAt
    have hd2 : HasDerivAt (ζ ∘ σ) (deriv σ t • deriv ζ (σ t)) t :=
      hζa.differentiableAt.hasDerivAt.scomp t hd1
    have hd3 : HasDerivAt G ((conj u * (deriv σ t • deriv ζ (σ t))).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd2.const_mul (conj u))
    rw [hd3.deriv, smul_eq_mul]
    have hφ : Real.sqrt ‖φ (σ t)‖ = ‖deriv ζ (σ t)‖ := by
      rw [← hζφ, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    rw [phiDensity, hφ, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs]
    calc |(conj u * (deriv σ t * deriv ζ (σ t))).re|
        ≤ ‖conj u * (deriv σ t * deriv ζ (σ t))‖ := Complex.abs_re_le_norm _
      _ = ‖deriv ζ (σ t)‖ * ‖deriv σ t‖ := by
          rw [norm_mul, Complex.norm_conj, hu1, one_mul, norm_mul, mul_comm]
  calc ENNReal.ofReal ‖ζ (σ τ) - ζ (σ 0)‖
      = ‖(‖ζ (σ τ) - ζ (σ 0)‖ : ℝ)‖ₑ := (Real.enorm_eq_ofReal (norm_nonneg _)).symm
    _ = ‖∫ t in (0 : ℝ)..τ, deriv G t‖ₑ := by rw [hFTC]
    _ = ‖∫ t in Ioc (0 : ℝ) τ, deriv G t‖ₑ := by rw [intervalIntegral.integral_of_le hτ0.le]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) τ, ‖deriv G t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) τ, phiDensity φ (σ t) * ‖deriv σ t‖ₑ :=
        setLIntegral_mono_ae' measurableSet_Ioc hae
    _ = ∫⁻ t in Ioo (0 : ℝ) τ, phiDensity φ (σ t) * ‖deriv σ t‖ₑ :=
        (setLIntegral_congr Ioo_ae_eq_Ioc).symm

/-- Every rectifiable path in `D` between two points of the small chart disc has `φ`-length at
least the chart distance of its end points: inside `B̄` by `psa_chord_le`, and a path leaving
`B̄` has already `φ`-length `≥ ρ - ρ/3` up to its first exit time. -/
theorem psa_lower {φ ζ : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} {r ρ : ℝ} (hr : 0 < r)
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0)
    (hinj : InjOn ζ (closedBall z₀ r)) (hρB : ball 0 ρ ⊆ ζ '' ball z₀ r) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ ball z₀ r) (hζ₁ : ζ z₁ ∈ ball 0 (ρ / 3)) (hζ₂ : ζ z₂ ∈ ball 0 (ρ / 3))
    {σ : LRCurve} (hσ : IsPathIn D z₁ z₂ σ) :
    ENNReal.ofReal ‖ζ z₂ - ζ z₁‖ ≤ phiLength φ σ := by
  obtain ⟨⟨K, hK⟩, h0, h1, -⟩ := hσ
  have hsub : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  by_cases hout : ∃ t ∈ Icc (0 : ℝ) 1, σ.toFun t ∉ ball z₀ r
  · -- the first exit time `τ`
    obtain ⟨t₁, ht₁, hout₁⟩ := hout
    set S : Set ℝ := Icc 0 1 ∩ σ.toFun ⁻¹' (ball z₀ r)ᶜ with hS
    have hSc : IsClosed S :=
      hK.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isOpen_ball.isClosed_compl
    have hSne : S.Nonempty := ⟨t₁, ht₁, hout₁⟩
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    have hτS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
    have hτ1 : sInf S ≤ 1 := hτS.1.2
    have hτ0 : 0 < sInf S := by
      rcases hτS.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hτS.2
        show σ.toFun (sInf S) ∈ ball z₀ r
        rw [← h, h0]
        exact hz₁
    have hin : ∀ t ∈ Ico (0 : ℝ) (sInf S), σ.toFun t ∈ ball z₀ r := by
      intro t ht
      by_contra hcon
      exact notMem_of_lt_csInf ht.2 hSbdd ⟨⟨ht.1, ht.2.le.trans hτ1⟩, hcon⟩
    have hτmem : σ.toFun (sInf S) ∈ closedBall z₀ r := by
      rw [← closure_ball z₀ hr.ne']
      haveI hne : (𝓝[Ico (0 : ℝ) (sInf S)] (sInf S)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hτ0.ne]
        exact ⟨hτ0.le, le_rfl⟩
      refine mem_closure_of_tendsto (f := σ.toFun) ?_
        (eventually_nhdsWithin_of_forall (a := sInf S) hin)
      exact (hK.continuousOn.continuousWithinAt hτS.1).mono_left
        (nhdsWithin_mono _ (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hτ1)))
    have hmaps : ∀ t ∈ Icc 0 (sInf S), σ.toFun t ∈ closedBall z₀ r := by
      intro t ht
      rcases ht.2.lt_or_eq with h | h
      · exact hsub (hin t ⟨ht.1, h⟩)
      · rw [h]; exact hτmem
    have hchord := psa_chord_le han hK hτ0 hτ1 hmaps
    rw [h0] at hchord
    -- the exit point is mapped outside `ball 0 ρ`
    have hfar : ρ ≤ ‖ζ (σ.toFun (sInf S))‖ := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨x, hx, hxe⟩ := hρB (mem_ball_zero_iff.2 hlt)
      have hxeq : x = σ.toFun (sInf S) := hinj (hsub hx) hτmem hxe
      exact hτS.2 (hxeq ▸ hx)
    have hζ₁' : ‖ζ z₁‖ < ρ / 3 := mem_ball_zero_iff.1 hζ₁
    have hζ₂' : ‖ζ z₂‖ < ρ / 3 := mem_ball_zero_iff.1 hζ₂
    calc ENNReal.ofReal ‖ζ z₂ - ζ z₁‖
        ≤ ENNReal.ofReal ‖ζ (σ.toFun (sInf S)) - ζ z₁‖ := by
          apply ENNReal.ofReal_le_ofReal
          have h3 := norm_sub_le (ζ z₂) (ζ z₁)
          have h4 := norm_sub_norm_le (ζ (σ.toFun (sInf S))) (ζ z₁)
          linarith
      _ ≤ ∫⁻ t in Ioo 0 (sInf S), phiDensity φ (σ.toFun t) * ‖deriv σ.toFun t‖ₑ := hchord
      _ ≤ ∫⁻ t in Ioo 0 1, phiDensity φ (σ.toFun t) * ‖deriv σ.toFun t‖ₑ :=
          lintegral_mono_set (Ioo_subset_Ioo_right hτ1)
      _ = phiLength φ σ := rfl
  · -- the whole path stays in the disc
    have hall : ∀ t ∈ Icc (0 : ℝ) 1, σ.toFun t ∈ ball z₀ r := fun t ht => by
      by_contra h
      exact hout ⟨t, ht, h⟩
    have h := psa_chord_le han hK zero_lt_one le_rfl (fun t ht => hsub (hall t ht))
    rw [h1, h0] at h
    exact h

/-- §25.2: near a regular point, the `φ`-straight segment between two points is the unique
shortest connection: its `φ`-length is the `φ`-distance. -/
theorem local_shortest_regular {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hφ : DifferentiableOn ℂ φ D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (h0 : φ z₀ ≠ 0) :
    ∃ V ∈ 𝓝 z₀, ∀ z₁ ∈ V, ∀ z₂ ∈ V, z₁ ≠ z₂ →
      ∃ γ : LRCurve, IsPathIn D z₁ z₂ γ ∧ IsPhiStraightArc φ γ.toFun 0 1 ∧
        phiLength φ γ = metricDist D (phiDensity φ) z₁ z₂ := by
  obtain ⟨ζ, r, hr, hBD, hζ0, hinj, han⟩ := psa_chart hD hφ hz₀ h0
  obtain ⟨hopen, hψ⟩ := psa_inverse hr hinj fun z hz => ⟨(han z hz).1, (han z hz).2.2⟩
  have h0mem : (0 : ℂ) ∈ ζ '' ball z₀ r := ⟨z₀, mem_ball_self hr, hζ0⟩
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 hopen 0 h0mem
  have hsub : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  have hcont : ContinuousOn ζ (ball z₀ r) := fun z hz =>
    (han z (hsub hz)).1.continuousAt.continuousWithinAt
  refine ⟨ball z₀ r ∩ ζ ⁻¹' ball 0 (ρ / 3), ?_, ?_⟩
  · refine (hcont.isOpen_inter_preimage isOpen_ball isOpen_ball).mem_nhds
      ⟨mem_ball_self hr, ?_⟩
    rw [mem_preimage, hζ0]
    exact mem_ball_self (by positivity)
  · rintro z₁ ⟨hz₁, hζ₁⟩ z₂ ⟨hz₂, hζ₂⟩ hne
    have hne' : ζ z₁ ≠ ζ z₂ := fun h => hne (hinj (hsub hz₁) (hsub hz₂) h)
    have hw₁ : ζ z₁ ∈ ball 0 ρ := ball_subset_ball (by linarith) hζ₁
    have hw₂ : ζ z₂ ∈ ball 0 ρ := ball_subset_ball (by linarith) hζ₂
    obtain ⟨γ, hγpath, hγstraight, hγlen⟩ := psa_segment hr hBD han hψ hρB hw₁ hw₂ hne'
    have hψ₁ : Function.invFunOn ζ (ball z₀ r) (ζ z₁) = z₁ :=
      (hinj.mono hsub).leftInvOn_invFunOn hz₁
    have hψ₂ : Function.invFunOn ζ (ball z₀ r) (ζ z₂) = z₂ :=
      (hinj.mono hsub).leftInvOn_invFunOn hz₂
    rw [hψ₁, hψ₂] at hγpath
    refine ⟨γ, hγpath, hγstraight, ?_⟩
    apply le_antisymm
    · exact le_iInf₂ fun σ hσ => hγlen ▸ psa_lower hr han hinj hρB hz₁ hζ₁ hζ₂ hσ
    · exact iInf₂_le (f := fun σ (_ : σ ∈ {γ : LRCurve | IsPathIn D z₁ z₂ γ}) =>
        σ.rhoLength (phiDensity φ)) γ hγpath

/-- `γ` is a `φ`-geodesic in `D` (locally shortest curve): every sufficiently short sub-arc
realizes the `φ`-distance of its end points. -/
def IsPhiGeodesic (φ : ℂ → ℂ) (D : Set ℂ) (γ : LRCurve) : Prop :=
  (∃ K : ℝ≥0, LipschitzOnWith K γ.toFun (Icc 0 1)) ∧ γ.closedTrace ⊆ D ∧
    ∀ t₀ ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      t₀ - δ < s → s < t → t < t₀ + δ →
        phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)

/-- Helper for `thm25_1_geodesics` (`s25g_`): a natural-parameter chart around a regular point `z₀` of `φ`: an open
disc `W ⊆ D` on which the natural parameter `ζ` (`ζ′² = φ`, `ζ′ ≠ 0`) is analytic and injective with open image and
holomorphic inverse `ψ`, and a neighbourhood `V ⊆ W` of `z₀` in which the `φ`-distance of two distinct points is the
Euclidean distance `|ζ z₂ − ζ z₁|` of their images (the proof of `local_shortest_regular`, with the value exposed). -/
theorem s25g_chart {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hφ : DifferentiableOn ℂ φ D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h0 : φ z₀ ≠ 0) :
    ∃ (ζ ψ : ℂ → ℂ) (W V : Set ℂ), V ∈ 𝓝 z₀ ∧ V ⊆ W ∧ IsOpen W ∧ W ⊆ D ∧
      (∀ z ∈ W, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0) ∧ InjOn ζ W ∧ IsOpen (ζ '' W) ∧
      (∀ w ∈ ζ '' W, ψ w ∈ W ∧ ζ (ψ w) = w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w) ∧
      ∀ z₁ ∈ V, ∀ z₂ ∈ V, z₁ ≠ z₂ →
        metricDist D (phiDensity φ) z₁ z₂ = ENNReal.ofReal ‖ζ z₂ - ζ z₁‖ := by
  obtain ⟨ζ, r, hr, hBD, hζ0, hinj, han⟩ := psa_chart hD hφ hz₀ h0
  obtain ⟨hopen, hψ⟩ := psa_inverse hr hinj fun z hz => ⟨(han z hz).1, (han z hz).2.2⟩
  have h0mem : (0 : ℂ) ∈ ζ '' ball z₀ r := ⟨z₀, mem_ball_self hr, hζ0⟩
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 hopen 0 h0mem
  have hsub : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  have hcont : ContinuousOn ζ (ball z₀ r) := fun z hz =>
    (han z (hsub hz)).1.continuousAt.continuousWithinAt
  refine ⟨ζ, Function.invFunOn ζ (ball z₀ r), ball z₀ r, ball z₀ r ∩ ζ ⁻¹' ball 0 (ρ / 3), ?_, inter_subset_left,
    isOpen_ball, fun z hz => hBD (hsub hz), fun z hz => han z (hsub hz), hinj.mono hsub, hopen, hψ, ?_⟩
  · refine (hcont.isOpen_inter_preimage isOpen_ball isOpen_ball).mem_nhds
      ⟨mem_ball_self hr, ?_⟩
    rw [mem_preimage, hζ0]
    exact mem_ball_self (by positivity)
  · rintro z₁ ⟨hz₁, hζ₁⟩ z₂ ⟨hz₂, hζ₂⟩ hne
    have hne' : ζ z₁ ≠ ζ z₂ := fun h => hne (hinj (hsub hz₁) (hsub hz₂) h)
    have hw₁ : ζ z₁ ∈ ball 0 ρ := ball_subset_ball (by linarith) hζ₁
    have hw₂ : ζ z₂ ∈ ball 0 ρ := ball_subset_ball (by linarith) hζ₂
    obtain ⟨γ, hγpath, hγstraight, hγlen⟩ := psa_segment hr hBD han hψ hρB hw₁ hw₂ hne'
    have hψ₁ : Function.invFunOn ζ (ball z₀ r) (ζ z₁) = z₁ :=
      (hinj.mono hsub).leftInvOn_invFunOn hz₁
    have hψ₂ : Function.invFunOn ζ (ball z₀ r) (ζ z₂) = z₂ :=
      (hinj.mono hsub).leftInvOn_invFunOn hz₂
    rw [hψ₁, hψ₂] at hγpath
    apply le_antisymm
    · exact iInf₂_le_of_le γ hγpath (le_of_eq hγlen)
    · exact le_iInf₂ fun σ hσ => hγlen ▸ psa_lower hr han hinj hρB hz₁ hζ₁ hζ₂ hσ

/-- Helper for `thm25_1_geodesics`: the equality case of `|∫ f′| ≤ ∫ |f′|`.  If a Lipschitz `f : [s, t] → ℂ` has
total variation `∫ |f′|` equal to the chord `|f t − f s| ≠ 0`, then `f′` points in the chord direction almost
everywhere. -/
theorem s25g_equality {f : ℝ → ℂ} {s t : ℝ} (hst : s < t) (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (Icc s t))
    (hlen : ∫⁻ x in Ioo s t, ‖deriv f x‖ₑ = ENNReal.ofReal ‖f t - f s‖) (hne : f t ≠ f s) :
    ∀ᵐ x ∂(volume.restrict (Ioo s t)),
      deriv f x = ((‖deriv f x‖ : ℝ) : ℂ) * ((f t - f s) / ((‖f t - f s‖ : ℝ) : ℂ)) := by
  obtain ⟨K, hK⟩ := hf
  have hΔn : 0 < ‖f t - f s‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set u : ℂ := (f t - f s) / (‖f t - f s‖ : ℂ) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔn.le, div_self hΔn.ne']
  have hcu : conj u * (f t - f s) = (‖f t - f s‖ : ℂ) := by
    have hΔc : (‖f t - f s‖ : ℂ) ≠ 0 := by exact_mod_cast hΔn.ne'
    rw [hu, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq,
      mul_div_assoc, div_self hΔc, mul_one]
  set G : ℝ → ℝ := fun x => (conj u * f x).re with hG
  have hGL : LipschitzOnWith K G (Icc s t) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq (G a) (G b)]
    calc |G a - G b| = |(conj u * (f a - f b)).re| := by
          simp only [hG]
          rw [mul_sub, Complex.sub_re]
      _ ≤ ‖conj u * (f a - f b)‖ := Complex.abs_re_le_norm _
      _ = ‖f a - f b‖ := by rw [norm_mul, Complex.norm_conj, hu1, one_mul]
      _ = dist (f a) (f b) := (Complex.dist_eq _ _).symm
      _ ≤ K * dist a b := hK.dist_le_mul _ ha _ hb
  have hGac : AbsolutelyContinuousOnInterval G s t := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K)
    rw [uIcc_of_le hst.le]
    exact hGL
  have hFTC : ∫ x in s..t, deriv G x = ‖f t - f s‖ := by
    rw [hGac.integral_deriv_eq_sub]
    show (conj u * f t).re - (conj u * f s).re = ‖f t - f s‖
    rw [← Complex.sub_re, ← mul_sub, hcu, Complex.ofReal_re]
  have hfae : ∀ᵐ x, x ∈ uIcc s t → DifferentiableAt ℝ f x :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le hst.le]; exact hK)
  have hGI : IntervalIntegrable (deriv G) volume s t := hGac.intervalIntegrable_deriv
  have hGI' : IntegrableOn (deriv G) (Ioo s t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hst.le).1 hGI
  have hGint : ∫ x in Ioo s t, deriv G x = ‖f t - f s‖ := by
    rw [← hFTC, intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
  have hmeas : Measurable fun x => ‖deriv f x‖ := (measurable_deriv f).norm
  have hlt : ∫⁻ x in Ioo s t, ENNReal.ofReal ‖deriv f x‖ < ⊤ := by
    have : ∫⁻ x in Ioo s t, ENNReal.ofReal ‖deriv f x‖ = ENNReal.ofReal ‖f t - f s‖ := by
      rw [← hlen]
      exact lintegral_congr fun x => ofReal_norm_eq_enorm _
    rw [this]
    exact ENNReal.ofReal_lt_top
  have hfi : IntegrableOn (fun x => ‖deriv f x‖) (Ioo s t) volume :=
    ⟨hmeas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => norm_nonneg _)]
      exact hlt⟩
  have hfint : ∫ x in Ioo s t, ‖deriv f x‖ = ‖f t - f s‖ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
      hmeas.aestronglyMeasurable]
    have : ∫⁻ x in Ioo s t, ENNReal.ofReal ‖deriv f x‖ = ENNReal.ofReal ‖f t - f s‖ := by
      rw [← hlen]
      exact lintegral_congr fun x => ofReal_norm_eq_enorm _
    rw [this, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- pointwise: `G' = Re(ū f')` a.e.
  have hGd : ∀ᵐ x ∂(volume.restrict (Ioo s t)), deriv G x = (conj u * deriv f x).re := by
    filter_upwards [ae_restrict_of_ae hfae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    have hx' : DifferentiableAt ℝ f x := hx (by rw [uIcc_of_le hst.le]; exact Ioo_subset_Icc_self hxm)
    have hd1 : HasDerivAt f (deriv f x) x := hx'.hasDerivAt
    have hd3 : HasDerivAt G ((conj u * deriv f x).re) x :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd1.const_mul (conj u))
    exact hd3.deriv
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo s t)), deriv G x ≤ ‖deriv f x‖ := by
    filter_upwards [hGd] with x hx
    rw [hx]
    calc (conj u * deriv f x).re ≤ ‖conj u * deriv f x‖ := Complex.re_le_norm _
      _ = ‖deriv f x‖ := by rw [norm_mul, Complex.norm_conj, hu1, one_mul]
  have hgi : Integrable (fun x => ‖deriv f x‖ - deriv G x) (volume.restrict (Ioo s t)) :=
    hfi.sub hGI'
  have hg0 : ∫ x in Ioo s t, (‖deriv f x‖ - deriv G x) = 0 := by
    rw [integral_sub hfi hGI', hfint, hGint, sub_self]
  have hgz := (integral_eq_zero_iff_of_nonneg_ae
    (by filter_upwards [hle] with x hx using sub_nonneg.2 hx) hgi).1 hg0
  filter_upwards [hgz, hGd] with x hx hxd
  have h1 : deriv G x = ‖deriv f x‖ := by
    have : ‖deriv f x‖ - deriv G x = 0 := hx
    linarith
  have h2 : (conj u * deriv f x).re = ‖conj u * deriv f x‖ := by
    rw [norm_mul, Complex.norm_conj, hu1, one_mul, ← hxd, h1]
  have h3 : (conj u * deriv f x).im = 0 := by
    have hn := Complex.normSq_eq_norm_sq (conj u * deriv f x)
    have ha := Complex.normSq_apply (conj u * deriv f x)
    rw [← h2] at hn
    have : (conj u * deriv f x).im * (conj u * deriv f x).im = 0 := by nlinarith
    exact mul_self_eq_zero.1 this
  have h4 : conj u * deriv f x = (‖deriv f x‖ : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, h2, norm_mul, Complex.norm_conj, hu1, one_mul]
    · rw [Complex.ofReal_im]
      exact h3
  calc deriv f x = u * (conj u * deriv f x) := by
        rw [← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, hu1]
        simp
    _ = ((‖deriv f x‖ : ℝ) : ℂ) * ((f t - f s) / ((‖f t - f s‖ : ℝ) : ℂ)) := by
        rw [h4, mul_comm, hu]

/-- Helper for `s25g_local`: the distance of a point of `D` to itself is `0` (the constant path). -/
theorem s25g_metricDist_self (D : Set ℂ) (ρ : ℂ → ℝ≥0∞) {z : ℂ} (hz : z ∈ D) : metricDist D ρ z z = 0 := by
  refine le_antisymm ?_ zero_le
  let c : LRCurve := ⟨fun _ => z, (LipschitzWith.const z).locallyLipschitz.locallyLipschitzOn⟩
  have hc : IsPathIn D z z c := by
    refine ⟨⟨0, (LipschitzWith.const z).lipschitzOnWith⟩, rfl, rfl, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact hz
  refine (iInf₂_le c hc).trans (le_of_eq ?_)
  show ∫⁻ t in Ioo (0 : ℝ) 1, ρ z * ‖deriv (fun _ : ℝ => z) t‖ₑ = 0
  simp

/-- Helper for `s25g_local`: the fundamental theorem of calculus for the real part of `w · f`, `f` Lipschitz. -/
theorem s25g_ftc_re {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (Icc a b))
    (w : ℂ) : ∫ x in a..b, (w * deriv f x).re = (w * f b).re - (w * f a).re := by
  obtain ⟨K, hK⟩ := hf
  set G : ℝ → ℝ := fun x => (w * f x).re with hG
  have hGL : LipschitzOnWith (‖w‖₊ * K) G (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq (G x) (G y)]
    calc |G x - G y| = |(w * (f x - f y)).re| := by
          simp only [hG]
          rw [mul_sub, Complex.sub_re]
      _ ≤ ‖w * (f x - f y)‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * dist (f x) (f y) := by rw [norm_mul, Complex.dist_eq]
      _ ≤ ‖w‖ * (K * dist x y) := by gcongr; exact hK.dist_le_mul _ hx _ hy
      _ = ((‖w‖₊ * K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  have hGac : AbsolutelyContinuousOnInterval G a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ‖w‖₊ * K)
    rw [uIcc_of_le hab]
    exact hGL
  show _ = G b - G a
  rw [← hGac.integral_deriv_eq_sub]
  have hfae : ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le hab]; exact hK)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hfae] with x hx hxm
  have hx' : DifferentiableAt ℝ f x := hx (by rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self (by
    rwa [uIoc_of_le hab] at hxm))
  have hd3 : HasDerivAt G ((w * deriv f x).re) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hx'.hasDerivAt.const_mul w)
  exact hd3.deriv.symm

/-- Helper for `thm25_1_geodesics`: the local structure of a non-pausing `φ`-geodesic at a regular parameter `t₀`.
Near `t₀` the curve stays in a natural-parameter chart `(ζ, ψ, W)`, and its image `ζ ∘ γ` is a monotone, unit-speed
(in `φ`-arclength) straight segment in a fixed direction `u`: `ζ(γ t) − ζ(γ s) = u · l_φ(γ|[s, t])`. -/
theorem s25g_local {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hφ : DifferentiableOn ℂ φ D) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ D γ)
    (hγp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (h0 : φ (γ.toFun t₀) ≠ 0) :
    ∃ δ > 0, ∃ (ζ ψ : ℂ → ℂ) (W : Set ℂ) (u : ℂ), ‖u‖ = 1 ∧ IsOpen W ∧ W ⊆ D ∧
      (∀ z ∈ W, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0) ∧ InjOn ζ W ∧ IsOpen (ζ '' W) ∧
      (∀ w ∈ ζ '' W, ψ w ∈ W ∧ ζ (ψ w) = w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t₀ - δ < t → t < t₀ + δ → γ.toFun t ∈ W) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, t₀ - δ < s → s ≤ t → t < t₀ + δ →
        ζ (γ.toFun t) - ζ (γ.toFun s) = u * ((phiSegmentLength φ γ s t).toReal : ℂ) := by
  classical
  obtain ⟨⟨K, hK⟩, hsub, hwin⟩ := hγ
  set z₀ := γ.toFun t₀ with hz₀
  have hz₀D : z₀ ∈ D := hsub ⟨t₀, ht₀, rfl⟩
  obtain ⟨ζ, ψ, W, V, hV, hVW, hWo, hWD, han, hinj, hopen, hψ, hmd⟩ := s25g_chart hD hφ hz₀D h0
  obtain ⟨ε0, hε0, hball0⟩ := Metric.mem_nhds_iff.1 hV
  set ε : ℝ := ε0 / 2 with hε
  have hε' : 0 < ε := by positivity
  have hcb : closedBall z₀ ε ⊆ V := (closedBall_subset_ball (by linarith)).trans hball0
  -- `ζ` is Lipschitz on the closed disc
  have hζc : ContinuousOn (fun z => ‖deriv ζ z‖) (closedBall z₀ ε) := fun z hz =>
    (((han z (hVW (hcb hz))).1.deriv.continuousAt).norm).continuousWithinAt
  obtain ⟨Lb, hLb⟩ := (isCompact_closedBall z₀ ε).exists_bound_of_continuousOn hζc
  have hζL : LipschitzOnWith (Real.toNNReal Lb) ζ (closedBall z₀ ε) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (han z (hVW (hcb hz))).1.differentiableAt) ?_ (convex_closedBall z₀ ε)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_max_of_le_left (by simpa using hLb z hz)
  -- the windows
  obtain ⟨δ₁, hδ₁, h₁⟩ : ∃ δ₁ > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ → γ.toFun t ∈ closedBall z₀ ε := by
    have hc : ContinuousWithinAt γ.toFun (Icc 0 1) t₀ := hK.continuousOn t₀ ht₀
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 hc ε hε'
    refine ⟨δ, hδ, fun t ht htd => ?_⟩
    exact (h ht (by rwa [Real.dist_eq])).le
  obtain ⟨δ₂, hδ₂, h₂⟩ := hwin t₀ ht₀
  set r : ℝ := min δ₁ δ₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrδ₁ : r < δ₁ := by
    have := min_le_left δ₁ δ₂
    rw [hr]; linarith
  have hrδ₂ : r < δ₂ := by
    have := min_le_right δ₁ δ₂
    rw [hr]; linarith
  set sa : ℝ := max 0 (t₀ - r) with hsa
  set sb : ℝ := min 1 (t₀ + r) with hsb
  have hsasb : sa < sb :=
    lt_min_iff.2 ⟨max_lt zero_lt_one (by linarith [ht₀.2]), max_lt (by linarith [ht₀.1]) (by linarith)⟩
  have hmem : ∀ x ∈ Icc sa sb, x ∈ Icc (0 : ℝ) 1 ∧ t₀ - r ≤ x ∧ x ≤ t₀ + r := fun x hx =>
    ⟨⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, (le_max_right _ _).trans hx.1,
      hx.2.trans (min_le_right _ _)⟩
  have hmem' : ∀ x ∈ Icc (0 : ℝ) 1, t₀ - r < x → x < t₀ + r → x ∈ Icc sa sb := fun x hx h1 h2 =>
    ⟨max_le hx.1 h1.le, le_min hx.2 h2.le⟩
  have hγmem : ∀ x ∈ Icc sa sb, γ.toFun x ∈ closedBall z₀ ε := fun x hx =>
    h₁ x (hmem x hx).1 (lt_of_le_of_lt (abs_le.2 ⟨by linarith [(hmem x hx).2.1], by linarith [(hmem x hx).2.2]⟩)
      hrδ₁)
  have hγW : ∀ x ∈ Icc sa sb, γ.toFun x ∈ W := fun x hx => hVW (hcb (hγmem x hx))
  have hF2 : ∀ s ∈ Icc sa sb, ∀ t ∈ Icc sa sb, s < t →
      phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t) := by
    intro s hs t ht hst
    exact h₂ s (hmem s hs).1 t (hmem t ht).1 (by linarith [(hmem s hs).2.1]) hst
      (by linarith [(hmem t ht).2.2])
  have hF3 : ∀ s ∈ Icc sa sb, ∀ t ∈ Icc sa sb, s < t → γ.toFun s ≠ γ.toFun t ∧
      phiSegmentLength φ γ s t = ENNReal.ofReal ‖ζ (γ.toFun t) - ζ (γ.toFun s)‖ := by
    have key : ∀ s ∈ Icc sa sb, ∀ t ∈ Icc sa sb, s < t → γ.toFun s ≠ γ.toFun t →
        phiSegmentLength φ γ s t = ENNReal.ofReal ‖ζ (γ.toFun t) - ζ (γ.toFun s)‖ := by
      intro s hs t ht hst hne
      rw [hF2 s hs t ht hst]
      exact hmd _ (hcb (hγmem s hs)) _ (hcb (hγmem t ht)) hne
    intro s hs t ht hst
    have hne : γ.toFun s ≠ γ.toFun t := by
      intro heq
      obtain ⟨v, hv, hvne⟩ := hγp s t (hmem s hs).1.1 hst (hmem t ht).1.2
      have hvm : v ∈ Icc sa sb := ⟨hs.1.trans hv.1, hv.2.trans ht.2⟩
      have hsv : s < v := lt_of_le_of_ne hv.1 (fun h => hvne (by rw [← h]))
      have h1 := key s hs v hvm hsv hvne.symm
      have h2 : phiSegmentLength φ γ s t = 0 := by
        rw [hF2 s hs t ht hst, ← heq]
        exact s25g_metricDist_self D _ (hsub ⟨s, (hmem s hs).1, rfl⟩)
      have h3 : phiSegmentLength φ γ s v ≤ phiSegmentLength φ γ s t :=
        lintegral_mono_set (Ioo_subset_Ioo_right hv.2)
      have hpos : 0 < ‖ζ (γ.toFun v) - ζ (γ.toFun s)‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 fun h => hvne (hinj (hγW v hvm) (hγW s hs) h))
      rw [h2, h1] at h3
      have := ENNReal.ofReal_eq_zero.1 (le_zero_iff.1 h3)
      linarith
    exact ⟨hne, key s hs t ht hst hne⟩
  -- the curve `f = ζ ∘ γ`
  set f : ℝ → ℂ := fun x => ζ (γ.toFun x) with hf
  have hfL : LipschitzOnWith (Real.toNNReal Lb * K) f (Icc sa sb) :=
    hζL.comp (hK.mono (fun x hx => (hmem x hx).1)) (fun x hx => hγmem x hx)
  have hγae : ∀ᵐ x, x ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ.toFun x :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le zero_le_one]; exact hK)
  have hF5 : ∀ s ∈ Icc sa sb, ∀ t ∈ Icc sa sb, ∀ᵐ x ∂(volume.restrict (Ioo s t)),
      phiDensity φ (γ.toFun x) * ‖deriv γ.toFun x‖ₑ = ‖deriv f x‖ₑ := by
    intro s hs t ht
    filter_upwards [ae_restrict_of_ae hγae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    have hxI : x ∈ Icc sa sb := ⟨hs.1.trans hxm.1.le, hxm.2.le.trans ht.2⟩
    have hd1 : HasDerivAt γ.toFun (deriv γ.toFun x) x :=
      (hx (by rw [uIcc_of_le zero_le_one]; exact (hmem x hxI).1)).hasDerivAt
    obtain ⟨hζa, hζφ, hζne⟩ := han _ (hγW x hxI)
    have hd2 : HasDerivAt f (deriv γ.toFun x • deriv ζ (γ.toFun x)) x :=
      hζa.differentiableAt.hasDerivAt.scomp x hd1
    have hφ' : Real.sqrt ‖φ (γ.toFun x)‖ = ‖deriv ζ (γ.toFun x)‖ := by
      rw [← hζφ, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    rw [hd2.deriv, smul_eq_mul, enorm_mul, phiDensity, hφ', ofReal_norm_eq_enorm, mul_comm]
  -- the chord direction
  have hne0 : f sb ≠ f sa := fun h =>
    (hF3 sa ⟨le_rfl, hsasb.le⟩ sb ⟨hsasb.le, le_rfl⟩ hsasb).1 (hinj (hγW sa ⟨le_rfl, hsasb.le⟩)
      (hγW sb ⟨hsasb.le, le_rfl⟩) h.symm)
  have hlen : ∫⁻ x in Ioo sa sb, ‖deriv f x‖ₑ = ENNReal.ofReal ‖f sb - f sa‖ := by
    rw [← (hF3 sa ⟨le_rfl, hsasb.le⟩ sb ⟨hsasb.le, le_rfl⟩ hsasb).2]
    exact (lintegral_congr_ae (hF5 sa ⟨le_rfl, hsasb.le⟩ sb ⟨hsasb.le, le_rfl⟩)).symm
  have hae := s25g_equality hsasb ⟨_, hfL⟩ hlen hne0
  set u : ℂ := (f sb - f sa) / ((‖f sb - f sa‖ : ℝ) : ℂ) with hu
  have hΔn : 0 < ‖f sb - f sa‖ := norm_pos_iff.2 (sub_ne_zero.2 hne0)
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔn.le, div_self hΔn.ne']
  -- the direction is shared by every sub-segment
  have hF7 : ∀ s ∈ Icc sa sb, ∀ t ∈ Icc sa sb, s < t → f t - f s = u * ((‖f t - f s‖ : ℝ) : ℂ) := by
    intro s hs t ht hst
    have hae' : ∀ᵐ x ∂(volume.restrict (Ioo s t)), deriv f x = ((‖deriv f x‖ : ℝ) : ℂ) * u :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.1 ht.2) hae
    have hLs : ∃ K : ℝ≥0, LipschitzOnWith K f (Icc s t) :=
      ⟨_, hfL.mono (Icc_subset_Icc hs.1 ht.2)⟩
    have hre : ∀ w : ℂ, (w * f t).re - (w * f s).re =
        (∫ x in Ioo s t, ‖deriv f x‖) * (w * u).re := by
      intro w
      rw [← s25g_ftc_re hst.le hLs w, intervalIntegral.integral_of_le hst.le,
        integral_Ioc_eq_integral_Ioo, ← integral_mul_const]
      refine integral_congr_ae ?_
      filter_upwards [hae'] with x hx
      conv_lhs => rw [hx]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    set I' : ℝ := ∫ x in Ioo s t, ‖deriv f x‖ with hI'
    have h1 := hre 1
    have h2 := hre (-Complex.I)
    have hI0 : 0 ≤ I' := integral_nonneg fun x => norm_nonneg _
    have hfe : f t - f s = (I' : ℂ) * u := by
      apply Complex.ext
      · simpa [Complex.sub_re] using h1
      · simpa [Complex.mul_re, Complex.mul_im, Complex.sub_im] using h2
    have hnorm : ‖f t - f s‖ = I' := by
      rw [hfe, norm_mul, hu1, mul_one, Complex.norm_real, Real.norm_of_nonneg hI0]
    rw [hnorm, hfe, mul_comm]
  refine ⟨r, hr0, ζ, ψ, W, u, hu1, hWo, hWD, fun z hz => han z hz, hinj, hopen, hψ, ?_, ?_⟩
  · intro t ht h1 h2
    exact hγW t (hmem' t ht h1 h2)
  · intro s hs t ht h1 h2 h3
    have hsI := hmem' s hs h1 (lt_of_le_of_lt h2 h3)
    have htI := hmem' t ht (lt_of_lt_of_le h1 h2) h3
    rcases h2.lt_or_eq with hlt | heq
    · rw [(hF3 s hsI t htI hlt).2, ENNReal.toReal_ofReal (norm_nonneg _)]
      exact hF7 s hsI t htI hlt
    · subst heq
      simp [phiSegmentLength]

/-- Helper for `s25g_part1`: the `φ`-length of a Lipschitz curve in `D` grows at most linearly. -/
theorem s25g_segLen_bound {φ : ℂ → ℂ} {D : Set ℂ} (hφ : DifferentiableOn ℂ φ D) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ D γ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      phiSegmentLength φ γ s t ≤ ENNReal.ofReal (M * (t - s)) := by
  obtain ⟨⟨K, hK⟩, hsub, -⟩ := hγ
  have hcpt : IsCompact (γ.toFun '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hK.continuousOn
  have hφc : ContinuousOn (fun z => ‖φ z‖) (γ.toFun '' Icc (0 : ℝ) 1) :=
    (hφ.continuousOn.mono hsub).norm
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hφc
  refine ⟨Real.sqrt (max C 0) * K, by positivity, fun s hs t ht hst => ?_⟩
  have hpt : ∀ x ∈ Ioo s t, phiDensity φ (γ.toFun x) * ‖deriv γ.toFun x‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (max C 0) * K) := by
    intro x hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
    have hd : ‖deriv γ.toFun x‖ ≤ K :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx01.1 hx01.2) hK
    have hφx : Real.sqrt ‖φ (γ.toFun x)‖ ≤ Real.sqrt (max C 0) := by
      apply Real.sqrt_le_sqrt
      have := hC (γ.toFun x) ⟨x, ⟨hx01.1.le, hx01.2.le⟩, rfl⟩
      rw [Real.norm_of_nonneg (norm_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    rw [phiDensity, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hφx hd (norm_nonneg _) (Real.sqrt_nonneg _))
  calc phiSegmentLength φ γ s t
      ≤ ∫⁻ x in Ioo s t, ENNReal.ofReal (Real.sqrt (max C 0) * K) :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal (Real.sqrt (max C 0) * K * (t - s)) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]

/-- Helper for `s25g_part1`: additivity of the `φ`-length of a curve over adjacent intervals. -/
theorem s25g_segLen_add (φ : ℂ → ℂ) (γ : LRCurve) {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t) :
    phiSegmentLength φ γ a t = phiSegmentLength φ γ a s + phiSegmentLength φ γ s t := by
  unfold phiSegmentLength
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc,
    setLIntegral_congr Ioo_ae_eq_Ioc, ← Ioc_union_Ioc_eq_Ioc has hst,
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- Helper for `s25g_part1`: inverting a continuous strictly increasing arclength `S` on `[a, b]` with `S a = 0`
and rescaling `[0, S b]` to `[a, b]` gives a strictly increasing bijection `h` of `[a, b]` with
`S (h τ) = k (τ - a)`, `k = S b / (b - a)`, continuous at interior points. -/
theorem s25g_arclength_inv {S : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hS : ContinuousOn S (Icc a b))
    (hmono : StrictMonoOn S (Icc a b)) (hS0 : S a = 0) :
    ∃ h : ℝ → ℝ, StrictMonoOn h (Icc a b) ∧ h '' Icc a b = Icc a b ∧
      (∀ τ ∈ Icc a b, h τ ∈ Icc a b ∧ S (h τ) = S b / (b - a) * (τ - a)) ∧
      ∀ τ' ∈ Ioo a b, ∀ δ > 0, ∃ η > 0, ∀ τ ∈ Icc a b, |τ - τ'| < η → |h τ - h τ'| < δ := by
  set k : ℝ := S b / (b - a) with hk
  have hSb : 0 < S b := by
    have := hmono (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
    rwa [hS0] at this
  have hk0 : 0 < k := div_pos hSb (by linarith)
  have hkb : k * (b - a) = S b := by rw [hk]; exact div_mul_cancel₀ _ (sub_pos.2 hab).ne'
  have hex : ∀ τ ∈ Icc a b, ∃ x ∈ Icc a b, S x = k * (τ - a) := by
    intro τ hτ
    have hmem : k * (τ - a) ∈ Icc (S a) (S b) := by
      rw [hS0]
      refine ⟨by nlinarith [hτ.1], ?_⟩
      have : k * (b - a) = S b := hkb
      nlinarith [hτ.2]
    exact intermediate_value_Icc hab.le hS hmem
  choose! h hhI hhS using hex
  have hlt : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, S x < S y ↔ x < y := fun x hx y hy => hmono.lt_iff_lt hx hy
  refine ⟨h, ?_, ?_, fun τ hτ => ⟨hhI τ hτ, hhS τ hτ⟩, ?_⟩
  · intro τ₁ h1 τ₂ h2 h12
    rw [← hlt _ (hhI τ₁ h1) _ (hhI τ₂ h2), hhS τ₁ h1, hhS τ₂ h2]
    nlinarith
  · ext x
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hhI τ hτ
    · intro hx
      have hSx : S x ∈ Icc (S a) (S b) := ⟨hmono.monotoneOn (left_mem_Icc.2 hab.le) hx hx.1,
        hmono.monotoneOn hx (right_mem_Icc.2 hab.le) hx.2⟩
      refine ⟨a + S x / k, ⟨by rw [hS0] at hSx; have := div_nonneg hSx.1 hk0.le; linarith, ?_⟩, ?_⟩
      · have : S x ≤ S b := hSx.2
        have h1 : S x / k ≤ b - a := by
          rw [div_le_iff₀ hk0]
          have : k * (b - a) = S b := hkb
          nlinarith
        linarith
      · have hτ : a + S x / k ∈ Icc a b := by
          refine ⟨by rw [hS0] at hSx; have := div_nonneg hSx.1 hk0.le; linarith, ?_⟩
          have h1 : S x / k ≤ b - a := by
            rw [div_le_iff₀ hk0]
            have : k * (b - a) = S b := hkb
            nlinarith [hSx.2]
          linarith
        have h2 : S (h (a + S x / k)) = S x := by
          rw [hhS _ hτ]; field_simp; ring
        exact (hmono.injOn (hhI _ hτ) hx h2)
  · intro τ' hτ' δ hδ
    have hτ'I : τ' ∈ Icc a b := Ioo_subset_Icc_self hτ'
    set t' := h τ' with ht'
    have ht'I : t' ∈ Icc a b := hhI τ' hτ'I
    have hSt' : S t' = k * (τ' - a) := hhS τ' hτ'I
    have hlow : S a < S t' := by rw [hS0, hSt']; nlinarith [hτ'.1]
    have hhigh : S t' < S b := by
      have : k * (b - a) = S b := hkb
      rw [hSt']; nlinarith [hτ'.2]
    have ht'a : a < t' := (hlt _ (left_mem_Icc.2 hab.le) _ ht'I).1 hlow
    have ht'b : t' < b := (hlt _ ht'I _ (right_mem_Icc.2 hab.le)).1 hhigh
    set x1 := max a (t' - δ / 2) with hx1
    set x2 := min b (t' + δ / 2) with hx2
    have hx1I : x1 ∈ Icc a b := ⟨le_max_left _ _, max_le hab.le (by linarith [ht'I.2])⟩
    have hx2I : x2 ∈ Icc a b := ⟨le_min hab.le (by linarith [ht'I.1]), min_le_left _ _⟩
    have hx1t : x1 < t' := max_lt ht'a (by linarith)
    have hx2t : t' < x2 := lt_min ht'b (by linarith)
    have h1 : S x1 < S t' := (hlt _ hx1I _ ht'I).2 hx1t
    have h2 : S t' < S x2 := (hlt _ ht'I _ hx2I).2 hx2t
    refine ⟨min (S t' - S x1) (S x2 - S t') / k, div_pos (lt_min (by linarith) (by linarith)) hk0, ?_⟩
    intro τ hτ hττ
    have hd : |k * (τ - τ')| < min (S t' - S x1) (S x2 - S t') := by
      rw [abs_mul, abs_of_pos hk0, mul_comm]
      exact (lt_div_iff₀ hk0).1 hττ
    have hSτ : S (h τ) - S t' = k * (τ - τ') := by rw [hhS τ hτ, hSt']; ring
    have hlo : S x1 < S (h τ) := by
      have := (abs_lt.1 hd).1
      have := min_le_left (S t' - S x1) (S x2 - S t')
      linarith [(abs_lt.1 hd).1]
    have hhi : S (h τ) < S x2 := by
      have := min_le_right (S t' - S x1) (S x2 - S t')
      linarith [(abs_lt.1 hd).2]
    have hl1 : x1 < h τ := (hlt _ hx1I _ (hhI τ hτ)).1 hlo
    have hl2 : h τ < x2 := (hlt _ (hhI τ hτ) _ hx2I).1 hhi
    rw [abs_lt]
    constructor
    · linarith [le_max_right a (t' - δ / 2)]
    · linarith [min_le_right b (t' + δ / 2)]

/-- Helper for `thm25_1_geodesics`: the first assertion (a non-pausing `φ`-geodesic is, on every interval avoiding
the zeros of `φ`, a reparametrized `φ`-straight arc).  Route: the `φ`-arclength `S` from `a` is strictly increasing
(`hγp`); `h = S⁻¹ ∘ (affine)`; `φ (γ ∘ h) (γ ∘ h)′²` is locally constant by `s25g_local`, hence constant. -/
theorem s25g_part1 {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hφ : DifferentiableOn ℂ φ D) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ D γ)
    (hγp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ t ∈ Icc a b, φ (γ.toFun t) ≠ 0) →
      ∃ γ' : ℝ → ℂ, (∀ t ∈ Icc a b, γ' t = γ.toFun t) ∧ IsPhiStraightArc φ γ' a b ∨
        ∃ h : ℝ → ℝ, StrictMonoOn h (Icc a b) ∧ h '' Icc a b = Icc a b ∧
          IsPhiStraightArc φ (γ.toFun ∘ h) a b := by
  classical
  intro a b ha hab hb hnz
  have hI : ∀ x ∈ Icc a b, x ∈ Icc (0 : ℝ) 1 := fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  obtain ⟨M, hM0, hM⟩ := s25g_segLen_bound hφ hγ
  have hfin : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → phiSegmentLength φ γ s t ≠ ⊤ :=
    fun s hs t ht hst => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM s (hI s hs) t (hI t ht) hst)
  set S : ℝ → ℝ := fun x => (phiSegmentLength φ γ a x).toReal with hS
  have hSa : S a = 0 := by simp [hS, phiSegmentLength]
  have hSadd : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      S t - S s = (phiSegmentLength φ γ s t).toReal := by
    intro s hs t ht hst
    simp only [hS]
    rw [s25g_segLen_add φ γ hs.1 hst,
      ENNReal.toReal_add (hfin a ⟨le_rfl, hab.le⟩ s hs hs.1) (hfin s hs t ht hst)]
    ring
  have hSmo : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → S s ≤ S t := fun s hs t ht hst => by
    have := hSadd s hs t ht hst
    have h0 := ENNReal.toReal_nonneg (a := phiSegmentLength φ γ s t)
    linarith
  have hSlip : LipschitzOnWith M.toNNReal S (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    wlog hxy : x ≤ y generalizing x y
    · rw [dist_comm, dist_comm x y]
      exact this y hy x hx (not_le.1 hxy).le
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hSmo x hx y hy hxy)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy), hSadd x hx y hy hxy]
    have := hM x (hI x hx) y (hI y hy) hxy
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rw [ENNReal.toReal_ofReal (mul_nonneg hM0 (sub_nonneg.2 hxy))] at h2
    rwa [Real.coe_toNNReal _ hM0]
  -- strict monotonicity of the `φ`-arclength: `hγp` rules out pauses
  have hSstrict : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → S s < S t := by
    intro s hs t ht hst
    obtain ⟨δ, hδ, ζ, ψ, W, u, hu1, hWo, hWD, han, hinj, hopen, hψ, hwin, hrel⟩ :=
      s25g_local hD hφ hγ hγp (hI s hs) (hnz s hs)
    have hmin := min_le_right t (s + δ / 2)
    set t'' := min t (s + δ / 2) with ht''
    have hst'' : s < t'' := lt_min hst (by linarith)
    have ht''t : t'' ≤ t := min_le_left _ _
    have ht''I : t'' ∈ Icc a b := ⟨hs.1.trans hst''.le, ht''t.trans ht.2⟩
    obtain ⟨v, hv, hvne⟩ := hγp s t'' (hI s hs).1 hst'' (hI t'' ht''I).2
    have hvI : v ∈ Icc a b := ⟨hs.1.trans hv.1, hv.2.trans ht''I.2⟩
    have hsW := hwin s (hI s hs) (by linarith) (by linarith)
    have hvW := hwin v (hI v hvI) (by linarith [hv.1]) (by linarith [hv.2])
    have hrel' := hrel s (hI s hs) v (hI v hvI) (by linarith) hv.1 (by linarith [hv.2])
    rw [← hSadd s hs v hvI hv.1] at hrel'
    have hne : S v - S s ≠ 0 := by
      intro h0
      rw [h0] at hrel'
      simp only [Complex.ofReal_zero, mul_zero] at hrel'
      exact hvne (hinj hvW hsW (sub_eq_zero.1 hrel'))
    have h1 : S s < S v := by
      have := hSmo s hs v hvI hv.1
      exact lt_of_le_of_ne this (fun h => hne (by rw [h]; ring))
    exact h1.trans_le ((hSmo v hvI t'' ht''I hv.2).trans (hSmo t'' ht''I t ht ht''t))
  have hSmono : StrictMonoOn S (Icc a b) := fun s hs t ht hst => hSstrict s hs t ht hst
  obtain ⟨h, hmono, himg, hhS, hcont⟩ :=
    s25g_arclength_inv hab hSlip.continuousOn hSmono hSa
  set k : ℝ := S b / (b - a) with hk
  have hk0 : 0 < k := by
    have : 0 < S b := by
      have := hSmono (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
      rwa [hSa] at this
    exact div_pos this (sub_pos.2 hab)
  -- local structure of `γ ∘ h`
  have hloc2 : ∀ τ' ∈ Ioo a b, ∃ c : ℂ, ∀ᶠ τ in 𝓝 τ', DifferentiableAt ℝ (γ.toFun ∘ h) τ ∧
      deriv (γ.toFun ∘ h) τ ≠ 0 ∧ φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = c := by
    intro τ' hτ'
    have hτ'I : τ' ∈ Icc a b := Ioo_subset_Icc_self hτ'
    obtain ⟨ht'I, hSt'⟩ := hhS τ' hτ'I
    set t' := h τ' with ht'
    obtain ⟨δ, hδ, ζ, ψ, W, u, hu1, hWo, hWD, han, hinj, hopen, hψ, hwin, hrel⟩ :=
      s25g_local hD hφ hγ hγp (hI t' ht'I) (hnz t' ht'I)
    obtain ⟨η, hη, hηh⟩ := hcont τ' hτ' δ hδ
    set N : Set ℝ := Ioo (max a (τ' - η)) (min b (τ' + η)) with hN
    have hNo : IsOpen N := isOpen_Ioo
    have hNn : N ∈ 𝓝 τ' :=
      hNo.mem_nhds ⟨max_lt hτ'.1 (by linarith), lt_min hτ'.2 (by linarith)⟩
    have hNI : ∀ τ ∈ N, τ ∈ Icc a b ∧ |τ - τ'| < η := by
      intro τ hτ
      refine ⟨⟨(le_max_left _ _).trans hτ.1.le, hτ.2.le.trans (min_le_left _ _)⟩, ?_⟩
      rw [abs_lt]
      constructor
      · linarith [le_max_right a (τ' - η), hτ.1]
      · linarith [min_le_right b (τ' + η), hτ.2]
    have hxd : ∀ τ ∈ N, h τ ∈ Icc a b ∧ |h τ - t'| < δ := fun τ hτ =>
      ⟨(hhS τ (hNI τ hτ).1).1, hηh τ (hNI τ hτ).1 (hNI τ hτ).2⟩
    have hψζ : ∀ x ∈ W, ψ (ζ x) = x := fun x hx =>
      hinj (hψ (ζ x) ⟨x, hx, rfl⟩).1 hx (hψ (ζ x) ⟨x, hx, rfl⟩).2.1
    have hGW : ∀ τ ∈ N, γ.toFun (h τ) ∈ W := by
      intro τ hτ
      obtain ⟨hxI, hxd'⟩ := hxd τ hτ
      rw [abs_lt] at hxd'
      exact hwin (h τ) (hI _ hxI) (by linarith [hxd'.1]) (by linarith [hxd'.2])
    have hlin : ∀ τ ∈ N, ζ (γ.toFun (h τ)) = ζ (γ.toFun t') + u * ((k * (τ - τ') : ℝ) : ℂ) := by
      intro τ hτ
      obtain ⟨hxI, hxd'⟩ := hxd τ hτ
      rw [abs_lt] at hxd'
      have hdiff : S (h τ) - S t' = k * (τ - τ') := by
        rw [(hhS τ (hNI τ hτ).1).2, hSt']; ring
      rcases le_total t' (h τ) with hle | hle
      · have := hrel t' (hI t' ht'I) (h τ) (hI _ hxI) (by linarith) hle (by linarith [hxd'.2])
        rw [← hSadd t' ht'I (h τ) hxI hle, hdiff] at this
        linear_combination this
      · have := hrel (h τ) (hI _ hxI) t' (hI t' ht'I) (by linarith [hxd'.1]) hle (by linarith)
        rw [← hSadd (h τ) hxI t' ht'I hle, show S t' - S (h τ) = -(k * (τ - τ')) by linarith] at this
        push_cast at this ⊢
        linear_combination -this
    have hGd : ∀ τ ∈ N, HasDerivAt (γ.toFun ∘ h)
        (u * (k : ℂ) * (deriv ζ (γ.toFun (h τ)))⁻¹) τ := by
      intro τ hτ
      set A : ℝ → ℂ := fun σ => ζ (γ.toFun t') + u * ((k * (σ - τ') : ℝ) : ℂ) with hA
      have hA' : HasDerivAt A (u * (k : ℂ)) τ := by
        have h1 : HasDerivAt (fun σ : ℝ => k * (σ - τ')) (k * 1) τ :=
          ((hasDerivAt_id τ).sub_const τ').const_mul k
        have h2 := (h1.ofReal_comp).const_mul u
        have h3 := h2.const_add (ζ (γ.toFun t'))
        exact h3.congr_deriv (by push_cast; ring)
      have hAτ : A τ = ζ (γ.toFun (h τ)) := (hlin τ hτ).symm
      have hAmem : A τ ∈ ζ '' W := ⟨_, hGW τ hτ, hAτ.symm⟩
      have hψd := (hψ (A τ) hAmem).2.2
      have hcomp := hψd.scomp τ hA'
      have hψA : ψ (A τ) = γ.toFun (h τ) := by rw [hAτ]; exact hψζ _ (hGW τ hτ)
      have hev : (γ.toFun ∘ h) =ᶠ[𝓝 τ] ψ ∘ A := by
        filter_upwards [hNo.mem_nhds hτ] with σ hσ
        show γ.toFun (h σ) = ψ (A σ)
        rw [show A σ = ζ (γ.toFun (h σ)) from (hlin σ hσ).symm, hψζ _ (hGW σ hσ)]
      rw [hψA] at hcomp
      simpa [smul_eq_mul] using hcomp.congr_of_eventuallyEq hev
    refine ⟨(u * (k : ℂ)) ^ 2, ?_⟩
    filter_upwards [hNn] with τ hτ
    obtain ⟨hζa, hζφ, hζne⟩ := han _ (hGW τ hτ)
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu1; exact zero_ne_one hu1
    have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hd := hGd τ hτ
    refine ⟨hd.differentiableAt, ?_, ?_⟩
    · rw [hd.deriv]
      exact mul_ne_zero (mul_ne_zero hu0 hk0') (inv_ne_zero hζne)
    · rw [hd.deriv]
      show φ (γ.toFun (h τ)) * _ = _
      rw [← hζφ]
      field_simp
  -- `φ (γ ∘ h) (γ ∘ h)'²` is locally constant, hence constant
  set Wf : ℝ → ℂ := fun τ => φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 with hWf
  have hlcl : IsLocallyConstant (fun x : Ioo a b => Wf x.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨c, hc⟩ := hloc2 x.1 x.2
    have hx := hc.self_of_nhds
    have h1 : ∀ᶠ τ in 𝓝 x.1, Wf τ = Wf x.1 := by
      filter_upwards [hc] with τ hτ
      rw [show Wf τ = c from hτ.2.2, show Wf x.1 = c from hx.2.2]
    exact (continuous_subtype_val.tendsto x).eventually h1
  haveI : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hτ₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ τ ∈ Ioo a b, Wf τ = Wf ((a + b) / 2) := fun τ hτ =>
    hlcl.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨τ, hτ⟩) (y := ⟨(a + b) / 2, hτ₀⟩)
      (mem_univ _) (mem_univ _)
  have hdiff : ∀ τ ∈ Ioo a b, DifferentiableAt ℝ (γ.toFun ∘ h) τ ∧ deriv (γ.toFun ∘ h) τ ≠ 0 := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hloc2 τ hτ
    have := hc.self_of_nhds
    exact ⟨this.1, this.2.1⟩
  have hc0 : Wf ((a + b) / 2) ≠ 0 := by
    have hτ := hτ₀
    have hmem := (hhS _ (Ioo_subset_Icc_self hτ)).1
    exact mul_ne_zero (hnz _ hmem) (pow_ne_zero 2 (hdiff _ hτ).2)
  refine ⟨γ.toFun, Or.inr ⟨h, hmono, himg, ⟨arg (Wf ((a + b) / 2)), fun τ hτ => ⟨(hdiff τ hτ).1,
    (hdiff τ hτ).2, ?_, ?_⟩⟩⟩⟩
  · have := hconst τ hτ
    rw [show φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = Wf τ from rfl, this]
    exact hc0
  · have := hconst τ hτ
    rw [show φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = Wf τ from rfl, this]
    have hexp : Wf ((a + b) / 2) = ((‖Wf ((a + b) / 2)‖ : ℝ) : ℂ) * exp (arg (Wf ((a + b) / 2)) * I) :=
      (Complex.norm_mul_exp_arg_mul_I _).symm
    have e : Wf ((a + b) / 2) * exp (-(arg (Wf ((a + b) / 2)) : ℂ) * I) =
        ((‖Wf ((a + b) / 2)‖ : ℝ) : ℂ) := by
      conv_lhs => arg 1; rw [hexp]
      rw [mul_assoc, ← Complex.exp_add, show (arg (Wf ((a + b) / 2)) : ℂ) * I +
        -(arg (Wf ((a + b) / 2)) : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one]
    rw [e]
    exact Complex.arg_ofReal_of_nonneg (norm_nonneg _)

/-- Helper for `s25g_part2`: a complex number whose square is a non-zero number of argument `0` is real and
non-zero. -/
theorem s25g_sq_real {q z : ℂ} (hq : q ^ 2 = z) (hz0 : z ≠ 0) (harg : Complex.arg z = 0) :
    q.im = 0 ∧ q.re ≠ 0 := by
  obtain ⟨hre, him⟩ := Complex.arg_eq_zero_iff.1 harg
  have hzre : 0 < z.re := by
    rcases hre.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hz0 (Complex.ext (by simpa using h.symm) (by simpa using him))
  have h1 : (q ^ 2).re = z.re := by rw [hq]
  have h2 : (q ^ 2).im = z.im := by rw [hq]
  simp only [sq, Complex.mul_re, Complex.mul_im] at h1 h2
  have hq0 : q.re ≠ 0 := by
    intro h0
    rw [h0] at h1
    nlinarith [sq_nonneg q.im]
  refine ⟨?_, hq0⟩
  have : q.re * q.im = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hq0
  · exact h

/-- Helper for `s25g_part2`: integrability of the derivative of the real part of `w · f`, `f` Lipschitz. -/
theorem s25g_ftc_int {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (Icc a b))
    (w : ℂ) : IntervalIntegrable (fun x => (w * deriv f x).re) volume a b := by
  obtain ⟨K, hK⟩ := hf
  set G : ℝ → ℝ := fun x => (w * f x).re with hG
  have hGL : LipschitzOnWith (‖w‖₊ * K) G (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq (G x) (G y)]
    calc |G x - G y| = |(w * (f x - f y)).re| := by
          simp only [hG]
          rw [mul_sub, Complex.sub_re]
      _ ≤ ‖w * (f x - f y)‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * dist (f x) (f y) := by rw [norm_mul, Complex.dist_eq]
      _ ≤ ‖w‖ * (K * dist x y) := by gcongr; exact hK.dist_le_mul _ hx _ hy
      _ = ((‖w‖₊ * K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring
  have hGac : AbsolutelyContinuousOnInterval G a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ‖w‖₊ * K)
    rw [uIcc_of_le hab]
    exact hGL
  have hfae : ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le hab]; exact hK)
  refine hGac.intervalIntegrable_deriv.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
  filter_upwards [hfae] with x hx hxm
  have hx' : DifferentiableAt ℝ f x := hx (by rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self (by
    rwa [uIoc_of_le hab] at hxm))
  have hd3 : HasDerivAt G ((w * deriv f x).re) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hx'.hasDerivAt.const_mul w)
  exact hd3.deriv

/-- Helper for `s25g_part2`: if `w · f′` is real and positive on `(s, t)` (`|w| = 1`, `f` Lipschitz and everywhere
differentiable on `(s, t)`), then `f` runs along a straight segment: its variation equals the chord, which is
non-zero. -/
theorem s25g_straight_seg {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (Icc s t)) (hdiff : ∀ x ∈ Ioo s t, DifferentiableAt ℝ f x) {w : ℂ}
    (hw : ‖w‖ = 1) (hreal : ∀ x ∈ Ioo s t, (w * deriv f x).im = 0)
    (hpos : ∀ x ∈ Ioo s t, 0 < (w * deriv f x).re) :
    ∫⁻ x in Ioo s t, ‖deriv f x‖ₑ = ENNReal.ofReal ‖f t - f s‖ ∧ f t ≠ f s := by
  obtain ⟨K, hK⟩ := hf
  have hint := s25g_ftc_int hst.le ⟨K, hK⟩ w
  have hftc := s25g_ftc_re hst.le ⟨K, hK⟩ w
  have hfc : ContinuousOn f (Icc s t) := hK.continuousOn
  have hgc : ContinuousOn (fun x => (w * f x).re) (Icc s t) :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hfc))
  have hgm : StrictMonoOn (fun x => (w * f x).re) (Icc s t) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc s t) hgc fun x hx => ?_
    rw [interior_Icc] at hx
    have hd3 : HasDerivAt (fun x => (w * f x).re) ((w * deriv f x).re) x :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x ((hdiff x hx).hasDerivAt.const_mul w)
    rw [hd3.deriv]
    exact hpos x hx
  have hlt : (w * f s).re < (w * f t).re := hgm (left_mem_Icc.2 hst.le) (right_mem_Icc.2 hst.le) hst
  -- the imaginary part of `w f` is constant
  have hg2c : ContinuousOn (fun x => (w * f x).im) (Icc s t) :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_const.mul hfc))
  have hg2d : DifferentiableOn ℝ (fun x => (w * f x).im) (Ioo s t) := fun x hx => by
    have hd3 : HasDerivAt (fun x => (w * f x).im) ((w * deriv f x).im) x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x ((hdiff x hx).hasDerivAt.const_mul w)
    exact hd3.differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope (fun x => (w * f x).im) hst hg2c hg2d
  have him : (w * f t).im = (w * f s).im := by
    have hd3 : HasDerivAt (fun x => (w * f x).im) ((w * deriv f ξ).im) ξ :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt ξ ((hdiff ξ hξ).hasDerivAt.const_mul w)
    rw [hd3.deriv, hreal ξ hξ] at hξd
    have := (div_eq_zero_iff.1 hξd.symm)
    rcases this with h | h
    · linarith
    · exfalso; linarith
  have hnorm : ‖f t - f s‖ = (w * f t).re - (w * f s).re := by
    have hF : w * (f t - f s) = (((w * f t).re - (w * f s).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.sub_re]
        ring
      · simp [Complex.mul_im, Complex.sub_im]
        have := him
        simp [Complex.mul_im] at this
        linarith
    have : ‖w * (f t - f s)‖ = ‖f t - f s‖ := by rw [norm_mul, hw, one_mul]
    rw [← this, hF, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · have hpt : ∀ x ∈ Ioo s t, ‖deriv f x‖ₑ = ENNReal.ofReal ((w * deriv f x).re) := by
      intro x hx
      have h1 : ‖deriv f x‖ = (w * deriv f x).re := by
        have hr : w * deriv f x = (((w * deriv f x).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simpa using hreal x hx)
        have : ‖w * deriv f x‖ = ‖deriv f x‖ := by rw [norm_mul, hw, one_mul]
        rw [← this, hr, Complex.norm_real, Real.norm_of_nonneg (hpos x hx).le]
        simp
      rw [← ofReal_norm, h1]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioo_of_le hst.le).1 hint)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using (hpos x hx).le)]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hst.le, hftc, hnorm]
  · intro h
    have : ‖f t - f s‖ = 0 := by rw [h, sub_self, norm_zero]
    linarith

/-- Helper for `thm25_1_geodesics`: the second assertion (a `φ`-straight arc through regular points is a
geodesic).  Route: in a chart, `(ζ ∘ c)′ = ± e^{iθ/2} √|φ c′²|` with a constant sign (Darboux), so the `φ`-length of
`c|[s, t]` is `|ζ c t − ζ c s|`, the `φ`-distance by `s25g_chart`. -/
theorem s25g_part2 {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hφ : DifferentiableOn ℂ φ D) :
    ∀ c : LRCurve, (∃ K : ℝ≥0, LipschitzOnWith K c.toFun (Icc 0 1)) → c.closedTrace ⊆ D →
      (∀ t ∈ Icc (0 : ℝ) 1, φ (c.toFun t) ≠ 0) → IsPhiStraightArc φ c.toFun 0 1 →
      IsPhiGeodesic φ D c := by
  classical
  intro c hcL htr hnz hstr
  obtain ⟨K, hK⟩ := hcL
  obtain ⟨θ, hθ⟩ := hstr
  refine ⟨⟨K, hK⟩, htr, fun t₀ ht₀ => ?_⟩
  set z₀ := c.toFun t₀ with hz₀
  have hz₀D : z₀ ∈ D := htr ⟨t₀, ht₀, rfl⟩
  obtain ⟨ζ, ψ, W, V, hV, hVW, hWo, hWD, han, hinj, hopen, hψ, hmd⟩ :=
    s25g_chart hD hφ hz₀D (hnz t₀ ht₀)
  obtain ⟨ε0, hε0, hball0⟩ := Metric.mem_nhds_iff.1 hV
  set ε : ℝ := ε0 / 2 with hε
  have hε' : 0 < ε := by positivity
  have hcb : closedBall z₀ ε ⊆ V := (closedBall_subset_ball (by linarith)).trans hball0
  have hζc : ContinuousOn (fun z => ‖deriv ζ z‖) (closedBall z₀ ε) := fun z hz =>
    (((han z (hVW (hcb hz))).1.deriv.continuousAt).norm).continuousWithinAt
  obtain ⟨Lb, hLb⟩ := (isCompact_closedBall z₀ ε).exists_bound_of_continuousOn hζc
  have hζL : LipschitzOnWith (Real.toNNReal Lb) ζ (closedBall z₀ ε) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (han z (hVW (hcb hz))).1.differentiableAt) ?_ (convex_closedBall z₀ ε)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_max_of_le_left (by simpa using hLb z hz)
  obtain ⟨δ₁, hδ₁, h₁⟩ : ∃ δ₁ > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ →
      c.toFun t ∈ closedBall z₀ ε := by
    have hc : ContinuousWithinAt c.toFun (Icc 0 1) t₀ := hK.continuousOn t₀ ht₀
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 hc ε hε'
    refine ⟨δ, hδ, fun t ht htd => ?_⟩
    exact (h ht (by rwa [Real.dist_eq])).le
  refine ⟨δ₁, hδ₁, ?_⟩
  intro s hs t ht h1 hst h2
  have hmem : ∀ x ∈ Icc s t, x ∈ Icc (0 : ℝ) 1 ∧ |x - t₀| < δ₁ := fun x hx =>
    ⟨⟨hs.1.trans hx.1, hx.2.trans ht.2⟩, abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
  have hcmem : ∀ x ∈ Icc s t, c.toFun x ∈ closedBall z₀ ε := fun x hx =>
    h₁ x (hmem x hx).1 (hmem x hx).2
  have hcW : ∀ x ∈ Icc s t, c.toFun x ∈ W := fun x hx => hVW (hcb (hcmem x hx))
  set f : ℝ → ℂ := fun x => ζ (c.toFun x) with hf
  have hfL : LipschitzOnWith (Real.toNNReal Lb * K) f (Icc s t) :=
    hζL.comp (hK.mono (fun x hx => (hmem x hx).1)) (fun x hx => hcmem x hx)
  -- derivative of `f` and the straightness relation on `(s, t)`
  have hIoo : ∀ x ∈ Ioo s t, x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
  have hfd : ∀ x ∈ Ioo s t, HasDerivAt f (deriv c.toFun x * deriv ζ (c.toFun x)) x := by
    intro x hx
    have hcd : DifferentiableAt ℝ c.toFun x := (hθ x (hIoo x hx)).1
    have hxI : x ∈ Icc s t := Ioo_subset_Icc_self hx
    exact ((han _ (hcW x hxI)).1.differentiableAt.hasDerivAt).scomp x hcd.hasDerivAt
  set e' : ℂ := Complex.exp (-(θ : ℂ) / 2 * I) with he'
  have he'1 : ‖e'‖ = 1 := by
    rw [he', Complex.norm_exp]
    simp
  have he'sq : e' ^ 2 = Complex.exp (-(θ : ℂ) * I) := by
    rw [he', sq, ← Complex.exp_add]
    congr 1
    ring
  have hqsq : ∀ x ∈ Ioo s t, (e' * deriv f x) ^ 2 =
      φ (c.toFun x) * deriv c.toFun x ^ 2 * Complex.exp (-(θ : ℂ) * I) := by
    intro x hx
    obtain ⟨hζa, hζφ, hζne⟩ := han _ (hcW x (Ioo_subset_Icc_self hx))
    rw [(hfd x hx).deriv, mul_pow, he'sq, ← hζφ]
    ring
  have hqre : ∀ x ∈ Ioo s t, (e' * deriv f x).im = 0 ∧ (e' * deriv f x).re ≠ 0 := by
    intro x hx
    obtain ⟨-, -, hne0, harg⟩ := hθ x (hIoo x hx)
    refine s25g_sq_real (hqsq x hx) ?_ harg
    exact mul_ne_zero hne0 (Complex.exp_ne_zero _)
  -- the sign of `Re (e' f′)` is constant (Darboux)
  have hgd : ∀ x ∈ Ioo s t, HasDerivAt (fun x => (e' * f x).re) ((e' * deriv f x).re) x := by
    intro x hx
    have := (hfd x hx).deriv
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((hfd x hx).differentiableAt.hasDerivAt.const_mul e')
  have hdarb := (ordConnected_Ioo (a := s) (b := t)).image_deriv
    (f := fun x => (e' * f x).re) (fun x hx => (hgd x hx).differentiableAt)
  have hsign : (∀ x ∈ Ioo s t, 0 < (e' * deriv f x).re) ∨ (∀ x ∈ Ioo s t, (e' * deriv f x).re < 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x1, hx1, hx1'⟩, ⟨x2, hx2, hx2'⟩⟩ := hcon
    have h0 : (0 : ℝ) ∈ deriv (fun x => (e' * f x).re) '' Ioo s t := by
      have m1 : deriv (fun x => (e' * f x).re) x1 = (e' * deriv f x1).re := (hgd x1 hx1).deriv
      have m2 : deriv (fun x => (e' * f x).re) x2 = (e' * deriv f x2).re := (hgd x2 hx2).deriv
      have n1 : (e' * deriv f x1).re < 0 := lt_of_le_of_ne hx1' (hqre x1 hx1).2
      have n2 : 0 < (e' * deriv f x2).re := lt_of_le_of_ne hx2' (hqre x2 hx2).2.symm
      rcases le_total x1 x2 with h12 | h12
      · exact hdarb.out ⟨x1, hx1, rfl⟩ ⟨x2, hx2, rfl⟩ ⟨by rw [m1]; exact n1.le, by rw [m2]; exact n2.le⟩
      · exact hdarb.out ⟨x1, hx1, rfl⟩ ⟨x2, hx2, rfl⟩ ⟨by rw [m1]; exact n1.le, by rw [m2]; exact n2.le⟩
    obtain ⟨x, hx, hx0⟩ := h0
    rw [(hgd x hx).deriv] at hx0
    exact (hqre x hx).2 hx0
  have hseg : ∫⁻ x in Ioo s t, ‖deriv f x‖ₑ = ENNReal.ofReal ‖f t - f s‖ ∧ f t ≠ f s := by
    rcases hsign with hp | hn
    · exact s25g_straight_seg hst ⟨_, hfL⟩ (fun x hx => (hfd x hx).differentiableAt) he'1
        (fun x hx => (hqre x hx).1) hp
    · refine s25g_straight_seg hst ⟨_, hfL⟩ (fun x hx => (hfd x hx).differentiableAt) (w := -e')
        (by rw [norm_neg, he'1]) (fun x hx => ?_) (fun x hx => ?_)
      · simp [(hqre x hx).1]
      · have := hn x hx
        simp only [neg_mul, Complex.neg_re]
        linarith
  have hsegLen : phiSegmentLength φ c s t = ∫⁻ x in Ioo s t, ‖deriv f x‖ₑ := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    obtain ⟨hζa, hζφ, hζne⟩ := han _ (hcW x (Ioo_subset_Icc_self hx))
    have hφ' : Real.sqrt ‖φ (c.toFun x)‖ = ‖deriv ζ (c.toFun x)‖ := by
      rw [← hζφ, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    rw [(hfd x hx).deriv, enorm_mul, phiDensity, hφ', ofReal_norm, mul_comm]
  have hne : c.toFun s ≠ c.toFun t := fun h => hseg.2 (by simp only [hf]; rw [h])
  rw [hsegLen, hseg.1]
  exact (hmd (c.toFun s) (hcb (hcmem s ⟨le_rfl, hst.le⟩)) (c.toFun t)
    (hcb (hcmem t ⟨hst.le, le_rfl⟩)) hne).symm

/-- **Theorem 25.1**: a geodesic of the `φ`-metric (`φ ≢ 0` holomorphic) consists of `φ`-straight
arcs; the arcs can only meet at zeros of `φ` (at a zero of order `m` making an angle
`≥ 2π/(m+2)`).  Here: along every sub-interval on which `γ` avoids the zeros of `φ`, `γ` is a
`φ`-straight arc; and conversely every `φ`-straight arc through regular points is a geodesic.

**Correction.**  `γ` is assumed not to pause (`hγp`: on no sub-interval is it constant), and the
reparametrization `h` maps `[a, b]` onto itself.  Without `hγp` the statement was **false** (a constant
curve is an `IsPhiGeodesic` but no straight arc, which needs a non-zero derivative); without the onto
condition the second alternative was nearly vacuous. -/
theorem thm25_1_geodesics {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    (hφ : DifferentiableOn ℂ φ D) (hne : ∃ z ∈ D, φ z ≠ 0) {γ : LRCurve} (hγ : IsPhiGeodesic φ D γ)
    (hγp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ t ∈ Icc a b, φ (γ.toFun t) ≠ 0) →
      ∃ γ' : ℝ → ℂ, (∀ t ∈ Icc a b, γ' t = γ.toFun t) ∧ IsPhiStraightArc φ γ' a b ∨
        ∃ h : ℝ → ℝ, StrictMonoOn h (Icc a b) ∧ h '' Icc a b = Icc a b ∧
          IsPhiStraightArc φ (γ.toFun ∘ h) a b) ∧
    ∀ c : LRCurve, (∃ K : ℝ≥0, LipschitzOnWith K c.toFun (Icc 0 1)) → c.closedTrace ⊆ D →
      (∀ t ∈ Icc (0 : ℝ) 1, φ (c.toFun t) ≠ 0) → IsPhiStraightArc φ c.toFun 0 1 →
      IsPhiGeodesic φ D c := by
  exact ⟨s25g_part1 hD hφ hγ hγp, s25g_part2 hD hφ⟩

/-- A `φ`-polygon in the unit disc (§25.2): a Jordan domain `P` with `P̄ ⊆ Δ` whose boundary is
made of `n` `φ`-straight `C¹` arcs `sideⱼ` from `Vⱼ` to `Vⱼ₊₁`, with interior angles `θⱼ ∈ (0, 2π)`
at the vertices (the angle from the direction of `sideⱼ` at `Vⱼ` counter-clockwise to the reversed
direction of `sideⱼ₋₁`).  The boundary is traversed once and positively: `P` lies to the left of every
side (`positive`), and two sides meet only at consecutive vertices (`simple`).

**Correction.**  Without `positive` the recorded angles are the exterior ones for a clockwise
traversal, and Theorem 25.2 was **false** (a clockwise square with `φ ≡ 1` has all angles `3π/2`);
`simple` excludes a boundary traversed more than once. -/
structure PhiPolygon (φ : ℂ → ℂ) (n : ℕ) [NeZero n] where
  dom : Set ℂ
  vert : Fin n → ℂ
  side : Fin n → ℝ → ℂ
  angle : Fin n → ℝ
  isJordan : IsJordanDomain dom
  closure_sub : closure dom ⊆ unitDisc
  side_straight : ∀ j, IsPhiStraightArc φ (side j) 0 1 ∧ ContDiffOn ℝ 1 (side j) (Icc 0 1)
  side_start : ∀ j, side j 0 = vert j
  side_end : ∀ j, side j 1 = vert (j + 1)
  frontier_eq : frontier dom = ⋃ j, side j '' Icc 0 1
  angle_mem : ∀ j, 0 < angle j ∧ angle j < 2 * π
  angle_def : ∀ j, ∃ k : ℤ,
    angle j = arg (-(derivWithin (side (j - 1)) (Icc 0 1) 1) / derivWithin (side j) (Icc 0 1) 0) + 2 * k * π
  positive : ∀ j, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ ε : ℝ in 𝓝[>] 0,
    side j t + (ε : ℂ) * I * deriv (side j) t ∈ dom
  simple : ∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, side i s = side j t → i = j ∧ s = t

/-! ### Helpers for `thm25_2_polygon` (`b2_`): Teichmüller's lemma

The sides of a `φ`-polygon form a positively oriented corner loop (`LiZhongQC.Lemmas.Umlaufsatz`); a
finite factorization `φ = ∏ (z - a)^{m_a} · e^{G}` and the constancy of `arg (φ(c) c'²)` along each
side (in lifted form) turn the winding and Umlaufsatz identities into Teichmüller's identity
`Σ (2π - (mⱼ + 2) θⱼ) = 2π (M + 2)` (`b2_identity`), and counting (`b2_count`) gives three small
angles. -/

/-- A real number strictly between `0` and `2π` is not an integer multiple of `2π`. -/
theorem b2_p4_ne_two_int_pi {x : ℝ} (hx : 0 < x ∧ x < 2 * π) (z : ℤ) : x ≠ 2 * z * π := by
  intro h
  rw [h] at hx
  have h1 : (0 : ℝ) < z := by nlinarith [Real.pi_pos]
  have h2 : (z : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have h1' : (0 : ℤ) < z := by exact_mod_cast h1
  have h2' : z < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- At every vertex of a `φ`-polygon the outgoing direction `u_k` and the incoming direction
`v_{k-1}` do not vanish (otherwise `angle_def` would give an angle in `2πℤ`). -/
theorem b2_p4_uv_ne_zero {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) (k : Fin n) :
    derivWithin (P.side k) (Icc 0 1) 0 ≠ 0 ∧ derivWithin (P.side (k - 1)) (Icc 0 1) 1 ≠ 0 := by
  obtain ⟨z, hz⟩ := P.angle_def k
  have hne := b2_p4_ne_two_int_pi (P.angle_mem k) z
  constructor
  · intro h
    rw [h, div_zero, arg_zero, zero_add] at hz
    exact hne hz
  · intro h
    rw [h, neg_zero, zero_div, arg_zero, zero_add] at hz
    exact hne hz

/-- The interior angle of a `φ`-polygon is `π` minus the exterior angle: `arg (-v/u)` is congruent
to `π - arg (u/v)` modulo `2π`, and both `P.angle k` and `π - arg (u/v)` lie in `[0, 2π)`. -/
theorem b2_p4_angle_eq {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) (k : Fin n) :
    P.angle k = π - b2_extAngle P.side k := by
  obtain ⟨hu, hv⟩ := b2_p4_uv_ne_zero P k
  obtain ⟨z, hz⟩ := P.angle_def k
  have hmem := P.angle_mem k
  unfold b2_extAngle
  set u := derivWithin (P.side k) (Icc 0 1) 0 with hu_def
  set v := derivWithin (P.side (k - 1)) (Icc 0 1) 1 with hv_def
  have hw : u / v ≠ 0 := div_ne_zero hu hv
  have hcoe : ((arg (-v / u) : ℝ) : Real.Angle) = ((π - arg (u / v) : ℝ) : Real.Angle) := by
    have h1 : -v / u = -(u / v)⁻¹ := by rw [inv_div, neg_div]
    rw [h1, arg_neg_coe_angle (inv_ne_zero hw), arg_inv_coe_angle, Real.Angle.coe_sub]
    abel
  obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hcoe
  have hA : P.angle k - (π - arg (u / v)) = 2 * π * ((j + z : ℤ) : ℝ) := by
    rw [hz]
    push_cast
    linarith [hj]
  have harg1 := neg_pi_lt_arg (u / v)
  have harg2 := arg_le_pi (u / v)
  have hpi := Real.pi_pos
  have hlo : (-1 : ℝ) < ((j + z : ℤ) : ℝ) := by nlinarith
  have hhi : ((j + z : ℤ) : ℝ) < 1 := by nlinarith
  have hlo' : (-1 : ℤ) < j + z := by exact_mod_cast hlo
  have hhi' : j + z < (1 : ℤ) := by exact_mod_cast hhi
  have h0 : j + z = 0 := by omega
  rw [h0, Int.cast_zero, mul_zero] at hA
  linarith

/-- An angle function only depends on the function on the open interval. -/
theorem b2_p4_angleFn_congr {f g : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ)
    (hfg : ∀ t ∈ Ioo a b, f t = g t) : b2_IsAngleFn g a b θ :=
  ⟨h.1, fun t ht => by rw [← hfg t ht]; exact h.2 t ht⟩

/-- A constant `θ` is an angle function of `w` when `arg (w e^{-iθ}) = 0` on the open interval. -/
theorem b2_p4_angleFn_const {w : ℝ → ℂ} {a b θ : ℝ}
    (h : ∀ t ∈ Ioo a b, arg (w t * exp (-(θ : ℂ) * I)) = 0) :
    b2_IsAngleFn w a b (fun _ => θ) := by
  refine ⟨continuousOn_const, fun t ht => ?_⟩
  have h1 := Complex.norm_mul_exp_arg_mul_I (w t * exp (-(θ : ℂ) * I))
  have hn : ‖exp (-(θ : ℂ) * I)‖ = 1 := by
    rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h t ht, ofReal_zero, zero_mul, exp_zero, mul_one, norm_mul, hn, mul_one] at h1
  calc w t = w t * exp (-(θ : ℂ) * I) * exp ((θ : ℂ) * I) := by
        rw [mul_assoc, ← Complex.exp_add]
        simp
    _ = (‖w t‖ : ℂ) * exp ((θ : ℂ) * I) := by rw [← h1]

/-- The vertices of a `φ`-polygon are pairwise distinct (`simple` at the parameter `0`). -/
theorem b2_p4_vert_inj {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) {i j : Fin n}
    (h : P.vert i = P.vert j) : i = j := by
  rw [← P.side_start, ← P.side_start] at h
  exact (P.simple i j 0 ⟨le_rfl, zero_lt_one⟩ 0 ⟨le_rfl, zero_lt_one⟩ h).1

/-- The sides of a `φ`-polygon form a corner loop.  The derivatives are non-zero on the open
sides by `side_straight`, and at the end points and against cusps by `angle_def`/`angle_mem`
(`arg 0 = 0` and `arg` of a positive real is `0`, while the angles lie in `(0, 2π)`). -/
theorem b2_phiPolygon_cornerLoop {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) :
    b2_IsCornerLoop P.side := by
  refine ⟨fun j => (P.side_straight j).2, ?_, ?_, P.simple, ?_⟩
  · intro j t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      exact (b2_p4_uv_ne_zero P j).1
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]
      have := (b2_p4_uv_ne_zero P (j + 1)).2
      rwa [add_sub_cancel_right] at this
    · obtain ⟨θ, hθ⟩ := (P.side_straight j).1
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds h0 h1)]
      exact (hθ t ⟨h0, h1⟩).2.1
  · intro j
    rw [P.side_end, P.side_start]
  · intro j
    obtain ⟨hu, hv⟩ := b2_p4_uv_ne_zero P j
    rw [mem_slitPlane_iff_arg]
    refine ⟨fun h => ?_, div_ne_zero hu hv⟩
    have h2 := b2_p4_angle_eq P j
    unfold b2_extAngle at h2
    rw [h, sub_self] at h2
    exact (P.angle_mem j).1.ne' h2

/-- The domain of a `φ`-polygon is positively bounded by its sides (the connected exterior comes from
the Jordan curve theorem through `JordanBridge`). -/
theorem b2_phiPolygon_posBoundary {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) :
    b2_IsPosBoundary P.side P.dom := by
  obtain ⟨hdo, hdc, hJ⟩ := P.isJordan
  have hbdd : Bornology.IsBounded P.dom :=
    ((Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset P.closure_sub).subset subset_closure
  rw [frontier_toExt_of_isBounded hbdd hdo] at hJ
  obtain ⟨hext, -⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hdo hdc hbdd hJ
  have hmem : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact ⟨hdo, hdc, hbdd, hext, P.frontier_eq, 0, 1 / 2, hmem, P.positive 0 (1 / 2) hmem⟩

/-- The interior angle of a `φ`-polygon is `π` minus the exterior (turning) angle. -/
theorem b2_phiPolygon_angle_eq {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) (k : Fin n) :
    P.angle k = π - b2_extAngle P.side k := by
  exact b2_p4_angle_eq P k

/-- A zero of `φ` on the boundary of a `φ`-polygon is a vertex (`φ ≠ 0` on the open sides). -/
theorem b2_phiPolygon_frontier_zero {φ : ℂ → ℂ} {n : ℕ} [NeZero n] (P : PhiPolygon φ n) {a : ℂ}
    (ha : a ∈ frontier P.dom) (h0 : φ a = 0) : ∃ k, a = P.vert k := by
  rw [P.frontier_eq] at ha
  obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.1 ha
  rcases eq_or_lt_of_le ht.1 with h | h
  · exact ⟨j, by rw [← h, P.side_start]⟩
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · exact ⟨j + 1, by rw [h', P.side_end]⟩
  obtain ⟨θ, hθ⟩ := (P.side_straight j).1
  exact absurd (by rw [h0, zero_mul]) (hθ t ⟨h, h'⟩).2.2.1

/-- At every point of the disc a holomorphic `φ ≢ 0` has a finite, non-negative order. -/
theorem b2_order_exists {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ m : ℕ, meromorphicOrderAt φ z = (m : ℤ) := by
  have han : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd isOpen_ball
  obtain ⟨w, hw, hw0⟩ := hne
  have hwt : analyticOrderAt φ w ≠ ⊤ := by
    rw [(han w hw).analyticOrderAt_eq_zero.2 hw0]
    exact ENat.zero_ne_top
  have hzt : analyticOrderAt φ z ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected hw hz hwt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hzt
  refine ⟨m, ?_⟩
  rw [(han z hz).meromorphicOrderAt_eq, ← hm]
  rfl

/-- (Argument principle I) **Finite factorization.**  On a disc `ball 0 r` (`r < 1`) containing a
given compact `K ⊆ Δ`, `φ = ∏_{a ∈ Z} (z - a)^{m a} · e^{G}` with `Z` the (finitely many) zeros of `φ`
in the disc, `m a` their orders and `G` continuous. -/
theorem b2_factor {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ unitDisc) :
    ∃ r : ℝ, r < 1 ∧ K ⊆ ball (0 : ℂ) r ∧ ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (G : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball (0 : ℂ) r ∧ φ a = 0 ∧ meromorphicOrderAt φ a = (m a : ℤ)) ∧
      ContinuousOn G (ball (0 : ℂ) r) ∧
      ∀ z ∈ ball (0 : ℂ) r, φ z = (∏ a ∈ Z, (z - a) ^ m a) * exp (G z) := by
  classical
  have hK1 : K ⊆ ball (0 : ℂ) 1 := hKsub
  obtain ⟨r₀, hr₀, hKr₀⟩ := exists_lt_subset_ball hK.isClosed hK1
  set r : ℝ := max r₀ (1 / 2) with hr_def
  have hr1 : r < 1 := max_lt hr₀ (by norm_num)
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right r₀ (1 / 2))
  have hKr : K ⊆ ball (0 : ℂ) r := hKr₀.trans (ball_subset_ball (le_max_left _ _))
  have hball : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hcb : closedBall (0 : ℂ) r ⊆ unitDisc := closedBall_subset_ball hr1
  have han : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd isOpen_ball
  have hord : ∀ z ∈ unitDisc, meromorphicOrderAt φ z ≠ ⊤ := by
    intro z hz
    obtain ⟨m, hm⟩ := b2_order_exists hφ hne hz
    rw [hm]
    exact WithTop.coe_ne_top
  set U : Set ℂ := ball (0 : ℂ) r with hU_def
  have hmerU : MeromorphicOn φ U := fun z hz => (han z (hball hz)).meromorphicAt
  have hmerC : MeromorphicOn φ (closedBall 0 r) := fun z hz => (han z (hcb hz)).meromorphicAt
  set D := MeromorphicOn.divisor φ U with hD_def
  have hfinC := (MeromorphicOn.divisor φ (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  have hfin : D.support.Finite := by
    refine hfinC.subset ?_
    intro a ha
    have haU : a ∈ U := D.supportWithinDomain ha
    rw [Function.mem_support] at ha ⊢
    rwa [MeromorphicOn.divisor_apply hmerC (ball_subset_closedBall haU),
      ← MeromorphicOn.divisor_apply hmerU haU]
  obtain ⟨g, hg, hg0, hfg⟩ := hmerU.extract_zeros_poles (fun u => hord u (hball u.2)) hfin
  have hUsc : IsSimplyConnected U := by
    unfold IsSimplyConnected
    have : ContractibleSpace U :=
      (convex_ball (0 : ℂ) r).contractibleSpace (nonempty_ball.2 hrpos)
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨G, hGc, hGe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUsc isOpen_ball
    hg.continuousOn (by rintro ⟨z, hz, hz0⟩; exact hg0 ⟨z, hz⟩ hz0)
  set Z : Finset ℂ := hfin.toFinset with hZ_def
  have hDnn : ∀ a, 0 ≤ D a := fun a =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han.mono hball) a
  have hprod : (∏ᶠ u, (· - u) ^ D u) = ∏ u ∈ Z, (· - u) ^ D u := by
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    rw [Function.FactorizedRational.mulSupport]
    intro a ha
    rw [hZ_def, Set.Finite.coe_toFinset]
    exact ha
  set Q : ℂ → ℂ := fun z => (∏ a ∈ Z, (z - a) ^ (D a).toNat) * g z with hQ_def
  have hQeq : ((∏ᶠ u, (· - u) ^ D u) • g) = Q := by
    funext z
    rw [hprod, Pi.smul_apply', smul_eq_mul, Finset.prod_apply, hQ_def]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Pi.pow_apply, ← Int.toNat_of_nonneg (hDnn a), zpow_natCast, Int.toNat_natCast]
  rw [hQeq] at hfg
  refine ⟨r, hr1, hKr, Z, fun a => (D a).toNat, G, ?_, hGc, ?_⟩
  · intro a ha
    rw [hZ_def, Set.Finite.mem_toFinset, Function.mem_support] at ha
    have haU : a ∈ U := D.supportWithinDomain ha
    have hDa : D a = (meromorphicOrderAt φ a).untop₀ := MeromorphicOn.divisor_apply hmerU haU
    obtain ⟨m, hm⟩ := b2_order_exists hφ hne (hball haU)
    rw [hm, WithTop.untop₀_coe] at hDa
    refine ⟨haU, ?_, ?_⟩
    · by_contra h0
      have h1 : analyticOrderAt φ a = 0 := (han a (hball haU)).analyticOrderAt_eq_zero.2 h0
      have h2 : meromorphicOrderAt φ a = 0 := by
        rw [(han a (hball haU)).meromorphicOrderAt_eq, h1]
        rfl
      rw [h2] at hm
      have hm0 : ((m : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := hm.symm
      have hm0' : (m : ℤ) = 0 := WithTop.coe_injective hm0
      exact ha (by rw [hDa, hm0'])
    · rw [hm]
      simp only [hDa, Int.toNat_natCast]
  · intro z hz
    have hev := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.1 hfg) z hz
    have hU' : ∀ᶠ y in 𝓝[≠] z, y ∈ U := eventually_nhdsWithin_of_eventually_nhds
      (isOpen_ball.mem_nhds hz)
    have hev' : ∀ᶠ y in 𝓝[≠] z, φ y = Q y := by
      filter_upwards [hev, hU'] with y h1 h2 using h1 h2
    have hφc : ContinuousAt φ z := (han z (hball hz)).continuousAt
    have hQc : ContinuousAt Q z := by
      refine ContinuousAt.mul ?_ (hg z hz).continuousAt
      exact continuous_finsetProd _ (fun a _ => (continuous_id.sub continuous_const).pow _)
        |>.continuousAt
    have h1 : Tendsto φ (𝓝[≠] z) (𝓝 (φ z)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto φ (𝓝[≠] z) (𝓝 (Q z)) :=
      (hQc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev'.mono fun y hy => hy.symm)
    rw [tendsto_nhds_unique h1 h2, hQ_def]
    simp only
    congr 1
    exact (hGe hz).symm

/-- (Argument principle II) **Lift form along a side.**  Along a `φ`-straight arc `c`, the lifted
argument `Im G(c) + Σ m_a · arg(c - a) + 2 · arg c'` of `φ(c) c'²` takes the same value at both ends
(it is continuous, and `≡ θ (mod 2π)` on the open arc). -/
theorem b2_side_const {φ : ℂ → ℂ} {c : ℝ → ℂ} (hstr : IsPhiStraightArc φ c 0 1)
    (hcc : ContinuousOn c (Icc 0 1)) {r : ℝ} (hcr : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ ball (0 : ℂ) r)
    {Z : Finset ℂ} {m : ℂ → ℕ} {G : ℂ → ℂ} (hG : ContinuousOn G (ball (0 : ℂ) r))
    (hfac : ∀ z ∈ ball (0 : ℂ) r, φ z = (∏ a ∈ Z, (z - a) ^ m a) * exp (G z))
    {ℓ : ℂ → ℝ → ℝ} (hℓ : ∀ a ∈ Z, b2_IsAngleFn (fun t => c t - a) 0 1 (ℓ a))
    {ψ : ℝ → ℝ} (hψ : b2_IsAngleFn (deriv c) 0 1 ψ) :
    (G (c 1)).im + ∑ a ∈ Z, (m a : ℝ) * ℓ a 1 + 2 * ψ 1 =
      (G (c 0)).im + ∑ a ∈ Z, (m a : ℝ) * ℓ a 0 + 2 * ψ 0 := by
  obtain ⟨θ, hθ⟩ := hstr
  have hGc : ContinuousOn (fun t => G (c t)) (Icc 0 1) := hG.comp hcc (fun t ht => hcr t ht)
  have hA1 : b2_IsAngleFn (fun t => exp (G (c t))) 0 1 (fun t => (G (c t)).im) :=
    b2_angleFn_exp (Complex.continuous_im.comp_continuousOn hGc)
  have hA2 : b2_IsAngleFn (fun t => ∏ a ∈ Z, (c t - a) ^ m a) 0 1
      (fun t => ∑ a ∈ Z, (m a : ℝ) * ℓ a t) :=
    b2_angleFn_prod Z (fun a ha => b2_angleFn_pow (hℓ a ha) (m a))
  have hA3 : b2_IsAngleFn (fun t => deriv c t ^ 2) 0 1 (fun t => ((2 : ℕ) : ℝ) * ψ t) :=
    b2_angleFn_pow hψ 2
  have hA := b2_angleFn_mul (b2_angleFn_mul hA1 hA2) hA3
  have hB : b2_IsAngleFn (fun t => φ (c t) * deriv c t ^ 2) 0 1
      (fun t => (G (c t)).im + ∑ a ∈ Z, (m a : ℝ) * ℓ a t + ((2 : ℕ) : ℝ) * ψ t) :=
    b2_p4_angleFn_congr hA (fun t ht => by
      rw [hfac (c t) (hcr t (Ioo_subset_Icc_self ht))]
      ring)
  have hC : b2_IsAngleFn (fun t => φ (c t) * deriv c t ^ 2) 0 1 (fun _ => θ) :=
    b2_p4_angleFn_const (fun t ht => (hθ t ht).2.2.2)
  have hE := b2_angleFn_change_eq zero_le_one (fun t ht => (hθ t ht).2.2.1) hB hC
  simp only [sub_self, Nat.cast_ofNat] at hE
  linarith

/-- **Teichmüller's identity** `Σⱼ (2π - (mⱼ + 2) θⱼ) = 2π (M + 2)`, `mⱼ` the order of `φ` at the
vertex `Vⱼ` and `M` the number of zeros of `φ` in the polygon (with multiplicity).  Proof: sum
`b2_side_const` over the sides; the `G`-terms telescope, a zero inside contributes `2π m_a`
(`b2_wind_in`), outside `0` (`b2_wind_out`), at the vertex `Vₖ` `mₖ θₖ` (`b2_bwa`,
`b2_phiPolygon_frontier_zero`), and the tangent terms give `2 (2π - Σ (π - θₖ))` (`b2_umlaufsatz`). -/
theorem b2_identity {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {n : ℕ} [NeZero n] (P : PhiPolygon φ n) {m : Fin n → ℕ}
    (hm : ∀ k, meromorphicOrderAt φ (P.vert k) = (m k : ℤ)) :
    ∃ M : ℕ, ∑ k, (2 * π - ((m k : ℝ) + 2) * P.angle k) = 2 * π * ((M : ℝ) + 2) := by
  classical
  have hc := b2_phiPolygon_cornerLoop P
  have hD := b2_phiPolygon_posBoundary P
  obtain ⟨hdo, -, hdb, -, -, -⟩ := id hD
  have hKc : IsCompact (closure P.dom) := hdb.isCompact_closure
  obtain ⟨r, -, hKr, Z, μ, G, hZ, hG, hfac⟩ := b2_factor hφ hne hKc P.closure_sub
  have hside_cl : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, P.side j t ∈ closure P.dom := fun j t ht =>
    frontier_subset_closure (by rw [P.frontier_eq]; exact mem_iUnion.2 ⟨j, t, ht, rfl⟩)
  have hvert_fr : ∀ k, P.vert k ∈ frontier P.dom := fun k => by
    rw [P.frontier_eq]
    exact mem_iUnion.2 ⟨k, 0, ⟨le_rfl, zero_le_one⟩, P.side_start k⟩
  -- angle functions of the tangents and of `side j - a` for the zeros `a`
  choose ψ hψ using fun j => b2_exists_angleFn_tangent hc j
  have hex : ∀ a ∈ Z, ∀ j, ∃ θ, b2_IsAngleFn (fun t => P.side j t - a) 0 1 θ := by
    intro a ha j
    by_cases hat : a ∈ ⋃ i, P.side i '' Icc 0 1
    · rw [← P.frontier_eq] at hat
      obtain ⟨k, rfl⟩ := b2_phiPolygon_frontier_zero P hat (hZ a ha).2.1
      rw [← P.side_start k]
      exact b2_exists_angleFn_vertex hc k j
    · exact b2_exists_angleFn_off hc hat j
  choose! ℓ hℓ using hex
  -- the side identities, summed over the sides
  have hsc : ∀ j, (G (P.side j 1)).im + ∑ a ∈ Z, (μ a : ℝ) * ℓ a j 1 + 2 * ψ j 1 =
      (G (P.side j 0)).im + ∑ a ∈ Z, (μ a : ℝ) * ℓ a j 0 + 2 * ψ j 0 := fun j =>
    b2_side_const (P.side_straight j).1 (P.side_straight j).2.continuousOn
      (fun t ht => hKr (hside_cl j t ht)) hG hfac (fun a ha => hℓ a ha j) (hψ j)
  have hsum : ∑ j, ((G (P.side j 1)).im - (G (P.side j 0)).im) +
      ∑ a ∈ Z, (μ a : ℝ) * ∑ j, (ℓ a j 1 - ℓ a j 0) + 2 * ∑ j, (ψ j 1 - ψ j 0) = 0 := by
    have h1 : ∀ j, ((G (P.side j 1)).im - (G (P.side j 0)).im) +
        ∑ a ∈ Z, (μ a : ℝ) * (ℓ a j 1 - ℓ a j 0) + 2 * (ψ j 1 - ψ j 0) = 0 := by
      intro j
      have h2 := hsc j
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have h0 := Finset.sum_eq_zero (s := Finset.univ) (fun j _ => h1 j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at h0
    simp only [← Finset.mul_sum] at h0
    exact h0
  -- the `G`-terms telescope
  have htel : ∑ j, ((G (P.side j 1)).im - (G (P.side j 0)).im) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    simp only [P.side_end, P.side_start]
    exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => rfl)
  -- a vertex that is not in `Z` is not a zero, so its order is `0`
  have hmZ : ∀ k, P.vert k ∉ Z → m k = 0 := by
    intro k hk
    have hvcl : P.vert k ∈ closure P.dom := frontier_subset_closure (hvert_fr k)
    have hφv : φ (P.vert k) ≠ 0 := by
      rw [hfac _ (hKr hvcl)]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a ha => pow_ne_zero _ (sub_ne_zero.2 ?_))
        (exp_ne_zero _)
      rintro rfl
      exact hk ha
    have han : AnalyticAt ℂ φ (P.vert k) :=
      hφ.analyticOnNhd isOpen_ball _ (P.closure_sub hvcl)
    have h1 : meromorphicOrderAt φ (P.vert k) = 0 := by
      rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.2 hφv]
      rfl
    rw [hm k] at h1
    have h2 : ((m k : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := h1
    exact_mod_cast WithTop.coe_injective h2
  -- the winding contribution of each zero
  have hW : ∀ a ∈ Z, (μ a : ℝ) * ∑ j, (ℓ a j 1 - ℓ a j 0) =
      (if a ∈ P.dom then 2 * π * (μ a : ℝ) else 0) +
        ∑ k, (if P.vert k = a then (m k : ℝ) * P.angle k else 0) := by
    intro a ha
    by_cases had : a ∈ P.dom
    · have hvne : ∀ k, P.vert k ≠ a := fun k h => by
        have h1 := hvert_fr k
        rw [hdo.frontier_eq, h] at h1
        exact h1.2 had
      rw [b2_wind_in hc hD had (hℓ a ha), ite_eq_left had,
        Finset.sum_eq_zero (fun k _ => ite_eq_right (hvne k))]
      ring
    by_cases hac : a ∈ closure P.dom
    · have hafr : a ∈ frontier P.dom := by
        rw [hdo.frontier_eq]
        exact ⟨hac, had⟩
      obtain ⟨k₀, hk₀⟩ := b2_phiPolygon_frontier_zero P hafr (hZ a ha).2.1
      have hL : ∀ j, b2_IsAngleFn (fun t => P.side j t - P.side k₀ 0) 0 1 (ℓ a j) := by
        intro j
        rw [P.side_start, ← hk₀]
        exact hℓ a ha j
      have hbwa := b2_bwa hc hD k₀ hL
      rw [← b2_phiPolygon_angle_eq] at hbwa
      have hμ : μ a = m k₀ := by
        have h1 := (hZ a ha).2.2
        rw [hk₀, hm k₀] at h1
        have h2 : ((m k₀ : ℤ) : WithTop ℤ) = ((μ (P.vert k₀) : ℤ) : WithTop ℤ) := h1
        have h3 : (m k₀ : ℤ) = (μ (P.vert k₀) : ℤ) := WithTop.coe_injective h2
        rw [hk₀]
        exact_mod_cast h3.symm
      rw [hbwa, ite_eq_right had, zero_add, Finset.sum_eq_single k₀, ite_eq_left hk₀.symm, hμ]
      · intro k _ hk
        rw [ite_eq_right]
        intro h
        exact hk (b2_p4_vert_inj P (h.trans hk₀))
      · intro h
        exact absurd (Finset.mem_univ k₀) h
    · have hvne : ∀ k, P.vert k ≠ a := fun k h =>
        hac (h ▸ frontier_subset_closure (hvert_fr k))
      rw [b2_wind_out hc hD hac (hℓ a ha), ite_eq_right had,
        Finset.sum_eq_zero (fun k _ => ite_eq_right (hvne k))]
      ring
  set M : ℕ := ∑ a ∈ Z, (if a ∈ P.dom then μ a else 0) with hM_def
  have hZsum : ∑ a ∈ Z, (μ a : ℝ) * ∑ j, (ℓ a j 1 - ℓ a j 0) =
      2 * π * (M : ℝ) + ∑ k, (m k : ℝ) * P.angle k := by
    rw [Finset.sum_congr rfl hW, Finset.sum_add_distrib, Finset.sum_comm (s := Z)]
    congr 1
    · rw [hM_def, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [hmZ k h]
        simp
  -- the tangent terms
  have hU := b2_umlaufsatz hc hD hψ
  have hB : ∑ k, b2_extAngle P.side k = n * π - ∑ k, P.angle k := by
    have h1 : ∀ k, b2_extAngle P.side k = π - P.angle k := fun k => by
      have h2 := b2_phiPolygon_angle_eq P k
      linarith
    simp only [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hA : ∑ k, (2 * π - ((m k : ℝ) + 2) * P.angle k) =
      n * (2 * π) - ∑ k, (m k : ℝ) * P.angle k - 2 * ∑ k, P.angle k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  refine ⟨M, ?_⟩
  rw [hA]
  rw [htel, hZsum, hU, hB] at hsum
  linarith

/-- **Counting.**  If `Σ (2π - (mⱼ + 2) θⱼ) = 2π (M + 2)` with all `θⱼ > 0`, then at least three
`θⱼ < 2π / (mⱼ + 2)`: the other terms are `≤ 0` and every term is `< 2π`, while the sum is `≥ 4π`. -/
theorem b2_count {n : ℕ} (θ : Fin n → ℝ) (m : Fin n → ℕ) (hθ : ∀ j, 0 < θ j) (M : ℕ)
    (hsum : ∑ j, (2 * π - ((m j : ℝ) + 2) * θ j) = 2 * π * ((M : ℝ) + 2)) :
    3 ≤ {j : Fin n | θ j < 2 * π / ((m j : ℝ) + 2)}.ncard := by
  classical
  by_contra hlt'
  have hlt := not_le.mp hlt'
  set S : Finset (Fin n) := Finset.univ.filter (fun j => θ j < 2 * π / ((m j : ℝ) + 2)) with hS
  have hSc : {j : Fin n | θ j < 2 * π / ((m j : ℝ) + 2)}.ncard = S.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [hS]
  rw [hSc] at hlt
  have hS2 : (S.card : ℝ) ≤ 2 := by exact_mod_cast (show S.card ≤ 2 by omega)
  set T : Fin n → ℝ := fun j => 2 * π - ((m j : ℝ) + 2) * θ j with hT
  have hT_lt : ∀ j, T j < 2 * π := fun j => by
    have : 0 < ((m j : ℝ) + 2) * θ j := mul_pos (by positivity) (hθ j)
    simp only [hT]
    linarith
  have hT_nonpos : ∀ j ∉ S, T j ≤ 0 := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    have hpos : (0 : ℝ) < (m j : ℝ) + 2 := by positivity
    rw [div_le_iff₀ hpos] at hj
    simp only [hT]
    linarith
  have hsplit : ∑ j, T j = ∑ j ∈ S, T j + ∑ j ∈ Finset.univ \ S, T j := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
  have hrest : ∑ j ∈ Finset.univ \ S, T j ≤ 0 :=
    Finset.sum_nonpos (fun j hj => hT_nonpos j (Finset.mem_sdiff.1 hj).2)
  have hSsum : ∑ j ∈ S, T j < 4 * π := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]
      positivity
    · calc ∑ j ∈ S, T j < ∑ _j ∈ S, 2 * π := Finset.sum_lt_sum_of_nonempty h (fun j _ => hT_lt j)
        _ = S.card * (2 * π) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (2 * π) := by gcongr
        _ = 4 * π := by ring
  have hM : (4 : ℝ) * π ≤ 2 * π * ((M : ℝ) + 2) := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith [Real.pi_pos]
  have hlt4 : ∑ j, T j < 4 * π := by
    rw [hsplit]
    linarith
  simp only [hT] at hlt4
  linarith

/-- **Theorem 25.2**: for a `φ`-polygon (`φ ≢ 0` holomorphic in `Δ`) with vertices `Vⱼ`, where `φ` has
a zero of order `mⱼ ≥ 0`, at least three interior angles satisfy `θⱼ < 2π/(mⱼ + 2)`.  (This follows
from `Σ (2π - (mⱼ+2) θⱼ) = 2π(m + 2)`, `m` the number of zeros inside.) -/
theorem thm25_2_polygon {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {n : ℕ} [NeZero n] (P : PhiPolygon φ n) :
    3 ≤ {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (P.vert j) = (m : ℤ) ∧
      P.angle j < 2 * π / ((m : ℝ) + 2)}.ncard := by
  have hv : ∀ k, P.vert k ∈ unitDisc := by
    intro k
    apply P.closure_sub
    apply frontier_subset_closure
    rw [P.frontier_eq]
    exact mem_iUnion.2 ⟨k, 0, ⟨le_rfl, zero_le_one⟩, P.side_start k⟩
  choose m hm using fun k => b2_order_exists hφ hne (hv k)
  obtain ⟨M, hM⟩ := b2_identity hφ hne P hm
  have hcount := b2_count P.angle m (fun j => (P.angle_mem j).1) M hM
  have hset : {j : Fin n | ∃ m' : ℕ, meromorphicOrderAt φ (P.vert j) = (m' : ℤ) ∧
      P.angle j < 2 * π / ((m' : ℝ) + 2)} = {j : Fin n | P.angle j < 2 * π / ((m j : ℝ) + 2)} := by
    ext j
    constructor
    · rintro ⟨m', hm', hlt⟩
      have h1 : ((m' : ℤ) : WithTop ℤ) = ((m j : ℤ) : WithTop ℤ) := hm'.symm.trans (hm j)
      have h2 : m' = m j := by exact_mod_cast WithTop.coe_injective h1
      change P.angle j < 2 * π / ((m j : ℝ) + 2)
      rw [← h2]
      exact hlt
    · intro hlt
      exact ⟨m j, hm j, hlt⟩
  rw [hset]
  exact hcount

/-! ## Curves on Riemann surfaces and Theorem 25.4 -/

universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- The `φ`-length of the part `γ|[s, t]` of a path `γ` on a Riemann surface, for a quadratic
differential `q`: the part is cut into pieces `γ|[tᵢ, tᵢ₊₁]` each contained in the chart at `xᵢ`, and
the `φ`-lengths of the chart images are added.  (The value does not depend on the subdivision, as the
density `|φ|^{1/2}|dz|` is invariant; the supremum makes the definition unambiguous.)

The partitions are required to have **Lipschitz** chart expressions on every piece, and the value is
their **infimum**.  Both are needed: `Path a b` is merely continuous, so a singular reparametrisation
(a Cantor-function change of variable) has `deriv = 0` almost everywhere and every piece integrates to
`0`.  Over all partitions that made the "length" of every path `0`, and `phiDistRS ≡ 0`.  With the
Lipschitz condition a non-rectifiable path has no admissible partition, and the infimum over the empty
family is `⊤` — the correct length; for a rectifiable path all admissible partitions agree, so the
infimum is the length.  See the README Corrections. -/
def phiLengthOn (q : S → ℂ → ℂ) {a b : S} (γ : Path a b) (s t : ℝ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → S)
    (_ : τ 0 = s ∧ τ (Fin.last n) = t ∧ Monotone τ ∧
      ∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
          (Icc (τ i.castSucc) (τ i.succ))),
    ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
      phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend u)) *
        ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ

/-- The `φ`-length `l_φ(γ)` of a path on a Riemann surface. -/
def phiLengthPath (q : S → ℂ → ℂ) {a b : S} (γ : Path a b) : ℝ≥0∞ := phiLengthOn q γ 0 1

/-- The `φ`-distance of two points of a Riemann surface. -/
def phiDistRS (q : S → ℂ → ℂ) (a b : S) : ℝ≥0∞ := ⨅ γ : Path a b, phiLengthPath q γ

/-- A `φ`-geodesic on a Riemann surface: a path which is locally shortest, i.e. every sufficiently
short sub-arc realizes the `φ`-distance of its end points. -/
def IsPhiGeodesicRS (q : S → ℂ → ℂ) {a b : S} (γ : Path a b) : Prop :=
  ∀ t₀ ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
    t₀ - δ < s → s < t → t < t₀ + δ →
      phiLengthOn q γ s t = phiDistRS q (γ.extend s) (γ.extend t)

section S26Helpers

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- `p ∈ S₀` is a regular point of the quadratic differential `q`. -/
def IsRegularPoint (q : S₀ → ℂ → ℂ) (p : S₀) : Prop := q p (chartAt ℂ p p) ≠ 0

/-- The transformation law of a holomorphic quadratic differential `q`, specialised: for `z` in the
chart target at `x` with `p = φ_x⁻¹ z` in the chart source at `y`, `q_x(z) = q_y(τ z) τ'(z)²`,
`τ = φ_y ∘ φ_x⁻¹`. -/
theorem s26u_law {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source) :
    q x z = q y (chartTransition y x z) * deriv (chartTransition y x) z ^ 2 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  rw [hq'.1.2 y x z hz hzy]
  norm_num

/-- Regularity in an arbitrary chart: for `z` in the chart target at `x`, the point `φ_x⁻¹ z` is a
regular point of `q` (a condition in the preferred chart at that point) iff `q_x(z) ≠ 0` (the
transformation law in both directions). -/
theorem s26u_isRegularPoint_iff {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    IsRegularPoint q ((chartAt ℂ x).symm z) ↔ q x z ≠ 0 := by
  set p := (chartAt ℂ x).symm z with hp
  have hpx : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  constructor
  · intro hr h0
    have hw : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hwp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hlaw := s26u_law hq p x hw (by rw [hwp]; exact hpx)
    have hT : chartTransition x p (chartAt ℂ p p) = z := by
      show chartAt ℂ x ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [hwp]
      exact (chartAt ℂ x).right_inv hz
    rw [hT, h0, zero_mul] at hlaw
    exact hr hlaw
  · intro hne h0
    apply hne
    have hlaw := s26u_law hq x p hz (mem_chart_source ℂ p)
    have hT : chartTransition p x z = chartAt ℂ p p := rfl
    rw [hlaw, hT, h0, zero_mul]

/-- If regular points of `q` accumulate at `φ_x⁻¹ z`, then `q_x` has no zeros in a punctured
neighbourhood of `z` (isolated zeros of the holomorphic `q_x`). -/
theorem s26u_eventually_ne_zero {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hfr : ∃ᶠ p in 𝓝 ((chartAt ℂ x).symm z), IsRegularPoint q p) :
    ∀ᶠ w in 𝓝[≠] z, q x w ≠ 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have han : AnalyticAt ℂ (q x) z := (hq'.2 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds hz)
  refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
  have hpx : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcont : Tendsto (chartAt ℂ x) (𝓝 ((chartAt ℂ x).symm z)) (𝓝 z) := by
    have h := ((chartAt ℂ x).continuousAt hpx).tendsto
    rwa [(chartAt ℂ x).right_inv hz] at h
  refine hfr ?_
  filter_upwards [hcont.eventually h0, (chartAt ℂ x).open_source.mem_nhds hpx] with p' hp' hsrc hreg
  have h1 := (s26u_isRegularPoint_iff hq x ((chartAt ℂ x).map_source hsrc)).1
    (by rw [(chartAt ℂ x).left_inv hsrc]; exact hreg)
  exact h1 hp'

/-- On a connected (T1) surface, regular points of a holomorphic quadratic differential `q ≠ 0`
accumulate at every point: the set of points near which no point is regular is clopen
(`s26u_eventually_ne_zero`), and if it were everything then `q = 0` (`s26u_isRegularPoint_iff`). -/
theorem s26u_frequently_regular [ConnectedSpace S₀] [T1Space S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S₀) : ∃ᶠ p' in 𝓝 p, IsRegularPoint q p' := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set B : Set S₀ := {p | ∀ᶠ p' in 𝓝 p, ¬ IsRegularPoint q p'} with hBdef
  have hBo : IsOpen B := isOpen_setOfPred_eventually_nhds
  have hBc : IsClosed B := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p₀ hp₀
    have hfr : ∃ᶠ p' in 𝓝 p₀, IsRegularPoint q p' := hp₀
    have hsrc : (chartAt ℂ p₀).source ∈ 𝓝 p₀ :=
      (chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀)
    have hl : (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀) = p₀ :=
      (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)
    have hw := s26u_eventually_ne_zero hq p₀ ((chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀))
      (by rw [hl]; exact hfr)
    have ht : Tendsto (chartAt ℂ p₀) (𝓝[≠] p₀) (𝓝[≠] (chartAt ℂ p₀ p₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hsrc] with p' hp' hne'
      exact fun heq => hne' ((chartAt ℂ p₀).injOn hp' (mem_chart_source ℂ p₀) heq)
    have hpunct : ∀ᶠ p' in 𝓝 p₀, p' ≠ p₀ → IsRegularPoint q p' := by
      have h2 := ht.eventually hw
      rw [eventually_nhdsWithin_iff] at h2
      filter_upwards [h2, hsrc] with p' h1 h3 hne'
      have h4 := (s26u_isRegularPoint_iff hq p₀ ((chartAt ℂ p₀).map_source h3)).2 (h1 hne')
      rwa [(chartAt ℂ p₀).left_inv h3] at h4
    filter_upwards [eventually_eventually_nhds.2 hpunct] with p₁ hp₁
    by_cases hp₁₀ : p₁ = p₀
    · rw [hp₁₀]
      exact hp₀
    · show ∃ᶠ p' in 𝓝 p₁, IsRegularPoint q p'
      refine Eventually.frequently ?_
      filter_upwards [hp₁, eventually_ne_nhds hp₁₀] with p'' h1 h2 using h1 h2
  rcases isClopen_iff.1 ⟨hBc, hBo⟩ with hB | hB
  · intro hp
    have hpB : p ∈ B := hp
    rw [hB] at hpB
    exact hpB
  · exfalso
    apply hne
    funext x z
    show q x z = 0
    by_cases hz : z ∈ (chartAt ℂ x).target
    · have hB' : (chartAt ℂ x).symm z ∈ B := by
        rw [hB]
        exact mem_univ _
      by_contra h0
      exact hB'.self_of_nhds ((s26u_isRegularPoint_iff hq x hz).2 h0)
    · exact hq'.1.1 x z hz

/-- Chart invariance of the `q`-density times the speed of a curve `c` at a time `u`, for two charts at
`y` and `y'` whose sources contain `c u`: the transition is holomorphic with a holomorphic local inverse,
and the transformation law of `q` absorbs its derivative (both sides vanish where neither chart
expression of `c` is differentiable). -/
theorem s26n_density_speed_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (y y' : S₀) {c : ℝ → S₀} {u : ℝ} (hc : ContinuousAt c u) (hy : c u ∈ (chartAt ℂ y).source)
    (hy' : c u ∈ (chartAt ℂ y').source) :
    phiDensity (q y) (chartAt ℂ y (c u)) * ‖deriv (fun v => chartAt ℂ y (c v)) u‖ₑ =
      phiDensity (q y') (chartAt ℂ y' (c u)) * ‖deriv (fun v => chartAt ℂ y' (c v)) u‖ₑ := by
  have hw : chartAt ℂ y (c u) ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hws : (chartAt ℂ y).symm (chartAt ℂ y (c u)) = c u := (chartAt ℂ y).left_inv hy
  have hw' : chartAt ℂ y' (c u) ∈ (chartAt ℂ y').target := (chartAt ℂ y').map_source hy'
  have hws' : (chartAt ℂ y').symm (chartAt ℂ y' (c u)) = c u := (chartAt ℂ y').left_inv hy'
  obtain ⟨hT, -⟩ := s23_transition y' y hw (by rw [hws]; exact hy')
  obtain ⟨hS, -⟩ := s23_transition y y' hw' (by rw [hws']; exact hy)
  have hlaw := s26u_law hq y y' hw (by rw [hws]; exact hy')
  have hTw : chartTransition y' y (chartAt ℂ y (c u)) = chartAt ℂ y' (c u) := by
    show chartAt ℂ y' ((chartAt ℂ y).symm (chartAt ℂ y (c u))) = chartAt ℂ y' (c u)
    rw [hws]
  have hev : (fun v => chartAt ℂ y' (c v)) =ᶠ[𝓝 u]
      chartTransition y' y ∘ fun v => chartAt ℂ y (c v) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hy)] with v hv
    show chartAt ℂ y' (c v) = chartAt ℂ y' ((chartAt ℂ y).symm (chartAt ℂ y (c v)))
    rw [(chartAt ℂ y).left_inv hv]
  have hev' : (fun v => chartAt ℂ y (c v)) =ᶠ[𝓝 u]
      chartTransition y y' ∘ fun v => chartAt ℂ y' (c v) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ y').open_source.mem_nhds hy')] with v hv
    show chartAt ℂ y (c v) = chartAt ℂ y ((chartAt ℂ y').symm (chartAt ℂ y' (c v)))
    rw [(chartAt ℂ y').left_inv hv]
  by_cases hd : DifferentiableAt ℝ (fun v => chartAt ℂ y (c v)) u
  · have hder : deriv (fun v => chartAt ℂ y' (c v)) u =
        deriv (chartTransition y' y) (chartAt ℂ y (c u)) * deriv (fun v => chartAt ℂ y (c v)) u := by
      rw [hev.deriv_eq]
      exact (hT.hasDerivAt.comp u hd.hasDerivAt).deriv
    simp only [phiDensity]
    rw [hder, hlaw, hTw, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), enorm_mul, ofReal_norm, mul_assoc]
  · have hd' : ¬ DifferentiableAt ℝ (fun v => chartAt ℂ y' (c v)) u := by
      intro hg
      exact hd ((hS.hasDerivAt.comp u hg.hasDerivAt).differentiableAt.congr_of_eventuallyEq hev')
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
    simp

/-- For a monotone subdivision `τ`, the integral over `(τ 0, τ n)` is at most the sum of the integrals over
the pieces `(τ i, τ (i + 1))`. -/
theorem s26n_lintegral_le_sum (G : ℝ → ℝ≥0∞) :
    ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ), Monotone τ →
      ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)), G u ≤
        ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ), G u := by
  intro n
  induction n with
  | zero => intro τ _; simp
  | succ n ih =>
    intro τ hτ
    have hτ' : Monotone fun i : Fin (n + 1) => τ i.castSucc := fun i j hij =>
      hτ (Fin.castSucc_le_castSucc_iff.2 hij)
    have h1 := ih (fun i => τ i.castSucc) hτ'
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at h1
    rw [Fin.sum_univ_castSucc, Fin.succ_last]
    have hsub : Ioo (τ 0) (τ (Fin.last (n + 1))) ⊆
        Ioo (τ 0) (τ (Fin.last n).castSucc) ∪ Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))) := by
      intro u hu
      rcases lt_or_ge u (τ (Fin.last n).castSucc) with h | h
      · exact Or.inl ⟨hu.1, h⟩
      · exact Or.inr ⟨h, hu.2.le⟩
    calc ∫⁻ u in Ioo (τ 0) (τ (Fin.last (n + 1))), G u
        ≤ ∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc) ∪
            Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := lintegral_mono_set hsub
      _ ≤ (∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc), G u) +
            ∫⁻ u in Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := lintegral_union_le _ _ _
      _ = (∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc), G u) +
            ∫⁻ u in Ioo (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := by
          congr 1
          exact (setLIntegral_congr Ioo_ae_eq_Icc).symm
      _ ≤ _ := add_le_add_left h1 _

end S26Helpers

/-- Helper for `s25e_potential`: at a point of differentiability, the derivative of `G ∘ c` is bounded by `ρ ‖c'‖`. -/
theorem s25e_deriv_bound {ρ G : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ → |G y - G x| ≤ (ρ x + ε) * ‖y - x‖)
    {c : ℝ → ℂ} {c' : ℂ} {f' : ℝ} {t : ℝ} (hcd : HasDerivAt c c' t)
    (hfd : HasDerivAt (fun s => G (c s)) f' t) : |f'| ≤ ρ (c t) * ‖c'‖ := by
  have hmain : ∀ ε : ℝ, 0 < ε → |f'| ≤ (ρ (c t) + ε) * ‖c'‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hGδ⟩ := hG (c t) ε hε
    have hslope_c := hcd.tendsto_slope_zero
    have hslope_f := hfd.tendsto_slope_zero
    refine le_of_tendsto_of_tendsto hslope_f.norm (hslope_c.norm.const_mul (ρ (c t) + ε)) ?_
    have hcont : Tendsto (fun h : ℝ => c (t + h)) (𝓝[≠] 0) (𝓝 (c t)) := by
      have h2 : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
        have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact hcd.continuousAt.tendsto.comp h2
    have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖c (t + h) - c t‖ < δ :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hcont).eventually (gt_mem_nhds hδ)
    filter_upwards [h1] with h hh
    have hb := hGδ (c (t + h)) hh
    have hinv : 0 ≤ |h|⁻¹ := inv_nonneg.2 (abs_nonneg h)
    simp only [norm_smul, norm_inv, Real.norm_eq_abs]
    calc |h|⁻¹ * |G (c (t + h)) - G (c t)| ≤ |h|⁻¹ * ((ρ (c t) + ε) * ‖c (t + h) - c t‖) :=
          mul_le_mul_of_nonneg_left hb hinv
      _ = (ρ (c t) + ε) * (|h|⁻¹ * ‖c (t + h) - c t‖) := by ring
  refine le_of_forall_pos_le_add fun e he => ?_
  have h1 : (0 : ℝ) < e / (‖c'‖ + 1) := div_pos he (by positivity)
  have := hmain _ h1
  have h2 : e / (‖c'‖ + 1) * ‖c'‖ ≤ e := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg c']
  nlinarith [h2]


/-- Helper for `s25e_cone_shortest`: a **potential** `G` with pointwise Lipschitz constant at most `ρ` bounds the
`ρ`-length of every Lipschitz curve from below by the increase of `G` along it. -/
theorem s25e_potential {ρ G : ℂ → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hGc : Continuous G)
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ → |G y - G x| ≤ (ρ x + ε) * ‖y - x‖)
    {c : ℝ → ℂ} {K : ℝ≥0} {α β : ℝ} (hαβ : α ≤ β) (hK : LipschitzOnWith K c (Icc α β)) :
    ENNReal.ofReal (G (c β) - G (c α)) ≤
      ∫⁻ t in Ioo α β, ENNReal.ofReal (ρ (c t)) * ‖deriv c t‖ₑ := by
  classical
  set f : ℝ → ℝ := fun t => G (c t) with hf
  have hcc : ContinuousOn c (Icc α β) := hK.continuousOn
  have hfc : ContinuousOn f (Icc α β) := hGc.comp_continuousOn hcc
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ t ∈ Icc α β, ρ (c t) ≤ M0 := by
    obtain ⟨M0, hM0⟩ := (isCompact_Icc.image_of_continuousOn (hρc.comp_continuousOn hcc)).bddAbove
    exact ⟨M0, fun t ht => hM0 ⟨t, ht, rfl⟩⟩
  have hM00 : 0 ≤ M0 := (hρ0 (c α)).trans (hM0 α ⟨le_rfl, hαβ⟩)
  -- the Dini bound `|f z - f x| ≤ (ρ(c x) + ε) K (z - x)` for `z ↓ x`
  have hdini : ∀ x ∈ Ico α β, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[>] x,
      |f z - f x| ≤ (ρ (c x) + ε) * (K * (z - x)) := by
    intro x hx ε hε
    obtain ⟨δ, hδ, hGδ⟩ := hG (c x) ε hε
    have hmem : Ioo x β ∈ 𝓝[>] x := Ioo_mem_nhdsGT hx.2
    have hle : 𝓝[>] x ≤ 𝓝[Icc α β] x :=
      le_inf nhdsWithin_le_nhds (le_principal_iff.2 (mem_of_superset hmem fun z hz =>
        ⟨hx.1.trans hz.1.le, hz.2.le⟩))
    have hcx : Tendsto c (𝓝[>] x) (𝓝 (c x)) :=
      (hcc x ⟨hx.1, hx.2.le⟩).tendsto.mono_left hle
    have h1 : ∀ᶠ z in 𝓝[>] x, ‖c z - c x‖ < δ :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hcx).eventually (gt_mem_nhds hδ)
    filter_upwards [hmem, h1] with z hz hzδ
    have hzI : z ∈ Icc α β := ⟨hx.1.trans hz.1.le, hz.2.le⟩
    have hxI : x ∈ Icc α β := ⟨hx.1, hx.2.le⟩
    have hb := hGδ (c z) hzδ
    have hcl : ‖c z - c x‖ ≤ K * (z - x) := by
      have := hK.dist_le_mul z hzI x hxI
      rw [dist_eq_norm, Real.dist_eq, abs_of_pos (sub_pos.2 hz.1)] at this
      exact this
    calc |f z - f x| ≤ (ρ (c x) + ε) * ‖c z - c x‖ := hb
      _ ≤ (ρ (c x) + ε) * (K * (z - x)) := mul_le_mul_of_nonneg_left hcl (by linarith [hρ0 (c x)])
  -- `f` is Lipschitz with constant `L = M0 K + 1`
  set L : ℝ := M0 * K + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  have hfL : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, s ≤ t → |f t - f s| ≤ L * (t - s) := by
    intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc α β := Icc_subset_Icc hs.1 ht.2
    have key := image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary
      (f := fun x => f x - f s) (f' := fun _ => M0 * K + 1 / 2) (a := s) (b := t)
      ((hfc.mono hsub).sub continuousOn_const)
      (fun x hx r hr => by
        have hxI : x ∈ Ico α β := ⟨hs.1.trans hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        set ε : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hεdef
        have hε : 0 < ε := by positivity
        have hr' : (M0 + ε) * K < r := by
          have : ε * K ≤ 1 / 2 := by
            rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [NNReal.coe_nonneg K]
          nlinarith
        refine ((hdini x hxI ε hε).and (Ioo_mem_nhdsGT hxI.2)).frequently.mono ?_
        rintro z ⟨hz1, hz2⟩
        have hzx : 0 < z - x := sub_pos.2 hz2.1
        show slope (norm ∘ fun x => f x - f s) x z < r
        rw [slope_def_field]
        have h3 : ‖f z - f s‖ - ‖f x - f s‖ ≤ |f z - f x| := by
          simp only [Real.norm_eq_abs]
          calc |f z - f s| - |f x - f s| ≤ |(f z - f s) - (f x - f s)| := abs_sub_abs_le_abs_sub _ _
            _ = |f z - f x| := by congr 1; ring
        simp only [Function.comp_apply]
        rw [div_lt_iff₀ hzx]
        calc ‖f z - f s‖ - ‖f x - f s‖ ≤ |f z - f x| := h3
          _ ≤ (ρ (c x) + ε) * (K * (z - x)) := hz1
          _ ≤ (M0 + ε) * (K * (z - x)) := by
              refine mul_le_mul_of_nonneg_right (by linarith [hM0 x ⟨hxI.1, hxI.2.le⟩]) ?_
              positivity
          _ = (M0 + ε) * K * (z - x) := by ring
          _ < r * (z - x) := mul_lt_mul_of_pos_right hr' hzx)
      (B := fun x => L * (x - s)) (B' := fun _ => L)
      (by simp)
      (by fun_prop)
      (fun x _ => (((hasDerivAt_id x).sub_const s).const_mul L).hasDerivWithinAt.congr_deriv (by simp))
      (fun x _ _ => by rw [hL]; linarith)
      (x := t) ⟨hst, le_rfl⟩
    simpa [Real.norm_eq_abs] using key
  have hLip : LipschitzOnWith ⟨L, hL0⟩ f (Icc α β) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq]
    wlog hxy : y ≤ x generalizing x y
    · rw [abs_sub_comm, abs_sub_comm x y]
      exact this y hy x hx (not_le.1 hxy).le
    have := hfL y hy x hx hxy
    rw [abs_of_nonneg (sub_nonneg.2 hxy)]
    exact this
  -- almost everywhere differentiability and the pointwise derivative bound
  have hcae : ∀ᵐ t, t ∈ uIcc α β → DifferentiableAt ℝ c t :=
    ae_differentiableAt_of_lipschitzOn (K := K) (by rw [uIcc_of_le hαβ]; exact hK)
  have hfac : AbsolutelyContinuousOnInterval f α β := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨L, hL0⟩)
    rw [uIcc_of_le hαβ]
    exact hLip
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioo α β)),
      ‖deriv f t‖ₑ ≤ ENNReal.ofReal (ρ (c t)) * ‖deriv c t‖ₑ := by
    filter_upwards [ae_restrict_of_ae hcae, ae_restrict_of_ae hfac.ae_differentiableAt,
      ae_restrict_mem measurableSet_Ioo] with t hct hft ht
    have htI : t ∈ uIcc α β := by rw [uIcc_of_le hαβ]; exact Ioo_subset_Icc_self ht
    have hb := s25e_deriv_bound hρ0 hG (hct htI).hasDerivAt (hft htI).hasDerivAt
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (hρ0 _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hb)
  have hInt : IntervalIntegrable (deriv f) volume α β := hfac.intervalIntegrable_deriv
  have hFTC : ∫ t in α..β, deriv f t = f β - f α := hfac.integral_deriv_eq_sub
  have hInt' : IntegrableOn (deriv f) (Ioo α β) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hαβ).1 hInt
  calc ENNReal.ofReal (G (c β) - G (c α)) = ENNReal.ofReal (∫ t in Ioo α β, deriv f t) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hαβ, hFTC]
    _ ≤ ENNReal.ofReal (∫ t in Ioo α β, ‖deriv f t‖) :=
        ENNReal.ofReal_le_ofReal (by simpa using norm_integral_le_integral_norm (μ := volume.restrict (Ioo α β)) (deriv f) |>.trans' (le_abs_self _))
    _ = ∫⁻ t in Ioo α β, ‖deriv f t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hInt'
    _ ≤ _ := lintegral_mono_ae hpt

/-- Helper for `s25e_cone_shortest`: the model density `√‖Q_m(w)‖` is `c ‖w‖^(c-1)`, `c = (m+2)/2`. -/
theorem s25e_rho_eq (m : ℕ) (w : ℂ) :
    Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * w ^ m‖ =
      (((m : ℝ) + 2) / 2) * ‖w‖ ^ ((((m : ℝ) + 2) / 2) - 1) := by
  have hc : 0 ≤ ((m : ℝ) + 2) / 2 := by positivity
  have h1 : ‖(((m : ℂ) + 2) / 2)‖ = ((m : ℝ) + 2) / 2 := by
    have : (((m : ℂ) + 2) / 2) = ((((m : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg hc]
  rw [norm_mul, norm_pow, norm_pow, h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg w)]
  congr 2
  ring

/-- Helper for `s25e_cone_shortest`: mean value inequality for `t ↦ t^c`, `c ≥ 1`. -/
theorem s25e_rpow_diff {c : ℝ} (hc : 1 ≤ c) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    q ^ c - p ^ c ≤ c * q ^ (c - 1) * (q - p) := by
  rcases hpq.lt_or_eq with hlt | heq
  · have hcont : ContinuousOn (fun t : ℝ => t ^ c) (Icc p q) :=
      (Real.continuous_rpow_const (by linarith)).continuousOn
    have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ c) (Ioo p q) := fun t ht =>
      (Real.differentiableAt_rpow_const_of_ne c (by linarith [ht.1])).differentiableWithinAt
    obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope (fun t : ℝ => t ^ c) hlt hcont hdiff
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    rw [Real.deriv_rpow_const ξ c] at hξd
    have hq0 : 0 < q := by linarith
    have h1 : ξ ^ (c - 1) ≤ q ^ (c - 1) :=
      Real.rpow_le_rpow hξ0.le hξ.2.le (by linarith)
    have h2 : q ^ c - p ^ c = c * ξ ^ (c - 1) * (q - p) := by
      field_simp at hξd
      linarith
    rw [h2]
    have : 0 ≤ q - p := by linarith
    have hc0 : 0 ≤ c := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc0) this
  · subst heq; simp

/-- Helper for `s25e_cone_shortest`: the radial potential `‖w‖^c` has pointwise Lipschitz constant `c ‖x‖^(c-1)`. -/
theorem s25e_radial_pt {c : ℝ} (hc : 1 < c) (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |‖y‖ ^ c - ‖x‖ ^ c| ≤ (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
  have hcont : ContinuousAt (fun t : ℝ => t ^ (c - 1)) ‖x‖ :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (ε / c) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  set u := ‖x‖
  set v := ‖y‖
  have hvu : |v - u| ≤ ‖y - x‖ := abs_norm_sub_norm_le y x
  have hmax : dist (max u v) u < δ := by
    rw [Real.dist_eq]
    rcases le_total u v with h | h
    · rw [max_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      exact lt_of_le_of_lt ((le_abs_self _).trans hvu) hy
    · rw [max_eq_left h]; simpa using hδ
  have hb := hδ' hmax
  rw [Real.dist_eq] at hb
  have hb' : (max u v) ^ (c - 1) ≤ u ^ (c - 1) + ε / c := by
    have := (abs_lt.1 hb).2
    linarith
  have hu0 : 0 ≤ u := norm_nonneg _
  have hv0 : 0 ≤ v := norm_nonneg _
  have hc0 : 0 < c := by linarith
  have hdiff : |v ^ c - u ^ c| ≤ c * (max u v) ^ (c - 1) * |v - u| := by
    rcases le_total u v with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow hu0 h hc0.le)), abs_of_nonneg (sub_nonneg.2 h),
        max_eq_right h]
      exact s25e_rpow_diff hc.le hu0 h
    · rw [abs_of_nonpos (sub_nonpos.2 (Real.rpow_le_rpow hv0 h hc0.le)), abs_of_nonpos (sub_nonpos.2 h),
        max_eq_left h]
      have := s25e_rpow_diff hc.le hv0 h
      linarith
  calc |v ^ c - u ^ c| ≤ c * (max u v) ^ (c - 1) * |v - u| := hdiff
    _ ≤ c * (max u v) ^ (c - 1) * ‖y - x‖ := mul_le_mul_of_nonneg_left hvu (by positivity)
    _ ≤ (c * u ^ (c - 1) + ε) * ‖y - x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc c * (max u v) ^ (c - 1) ≤ c * (u ^ (c - 1) + ε / c) := mul_le_mul_of_nonneg_left hb' hc0.le
          _ = c * u ^ (c - 1) + ε := by field_simp

/-- Helper for `s25e_cone_shortest`: the angular sector `cos(π/c) ‖z‖ ≤ Re z` lies in the slit plane. -/
theorem s25e_sector_slit {c : ℝ} (hc : 1 < c) {z : ℂ} (hz0 : z ≠ 0)
    (hsec : Real.cos (π / c) * ‖z‖ ≤ z.re) : z ∈ Complex.slitPlane ∧ |Complex.arg z| ≤ π / c := by
  have hπc : π / c < π := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hπc0 : 0 < π / c := by positivity
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcos : Real.cos (π / c) ≤ Real.cos (Complex.arg z) := by
    rw [Complex.cos_arg hz0, le_div_iff₀ hnz]
    linarith
  have habs : |Complex.arg z| ≤ π / c := by
    by_contra h
    rw [not_le] at h
    have h1 : Real.cos |Complex.arg z| < Real.cos (π / c) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hπc0.le (Complex.abs_arg_le_pi z) h
    rw [Real.cos_abs] at h1
    linarith
  refine ⟨Complex.mem_slitPlane_iff_arg.2 ⟨?_, hz0⟩, habs⟩
  intro h
  rw [h] at habs
  have : |π| = π := abs_of_pos Real.pi_pos
  linarith

/-- Helper for `s25e_cone_shortest`: on the boundary rays of the sector, `z^c = -‖z‖^c`. -/
theorem s25e_sector_boundary {c : ℝ} (hc : 1 < c) {z : ℂ} (hz0 : z ≠ 0)
    (heq : Real.cos (π / c) * ‖z‖ = z.re) : z ^ (c : ℂ) = -((‖z‖ ^ c : ℝ) : ℂ) := by
  have hπc : π / c < π := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hπc0 : 0 < π / c := by positivity
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcos : Real.cos (Complex.arg z) = Real.cos (π / c) := by
    rw [Complex.cos_arg hz0, div_eq_iff hnz.ne']
    linarith
  obtain ⟨-, habs⟩ := s25e_sector_slit hc hz0 heq.le
  have habs' : |Complex.arg z| = π / c := by
    refine Real.injOn_cos ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩ ⟨hπc0.le, hπc.le⟩ ?_
    rw [Real.cos_abs]
    exact hcos
  have hθ : Complex.arg z * c = π ∨ Complex.arg z * c = -π := by
    rcases abs_eq hπc0.le |>.1 habs' with h | h
    · left; rw [h]; field_simp
    · right; rw [h]; field_simp
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.log]
  have h1 : (↑(Real.log ‖z‖) + ↑(Complex.arg z) * Complex.I) * (c : ℂ) =
      ((Real.log ‖z‖ * c : ℝ) : ℂ) + ((Complex.arg z * c : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hnz]
  have h2 : Complex.exp (((Complex.arg z * c : ℝ) : ℂ) * Complex.I) = -1 := by
    rcases hθ with h | h
    · rw [h, Complex.exp_pi_mul_I]
    · rw [h]
      push_cast
      rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  rw [h2, mul_neg_one]

/-- Helper for `s25e_cone_shortest`: pointwise Lipschitz constant of the developed distance `‖a‖^c ‖(w/a)^c - 1‖`
at a point `x` with `x/a` in the slit plane. -/
theorem s25e_sector_pt {c : ℝ} (hc : 1 < c) {a : ℂ} (ha : a ≠ 0) {x : ℂ} (hx : x / a ∈ Complex.slitPlane)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      ‖a‖ ^ c * |‖(y / a) ^ (c : ℂ) - 1‖ - ‖(x / a) ^ (c : ℂ) - 1‖| ≤
        (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnac : 0 < ‖a‖ ^ c := Real.rpow_pos_of_pos hna c
  have hd : HasDerivAt (fun w : ℂ => (w / a) ^ (c : ℂ)) ((c : ℂ) * (x / a) ^ ((c : ℂ) - 1) * (1 / a)) x :=
    ((hasDerivAt_id x).div_const a).cpow_const hx
  have hlo := (hasDerivAt_iff_isLittleO.1 hd).def (c := ε / ‖a‖ ^ c) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hlo
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h1 := hδ' (by simpa [dist_eq_norm] using hy)
  set D : ℂ := (c : ℂ) * (x / a) ^ ((c : ℂ) - 1) * (1 / a) with hD
  have hDn : ‖a‖ ^ c * ‖D‖ = c * ‖x‖ ^ (c - 1) := by
    have e1 : ((c : ℂ) - 1) = ((c - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hD, norm_mul, norm_mul, e1, Complex.norm_cpow_real, norm_div, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ c), norm_one, Real.div_rpow (norm_nonneg _) hna.le,
      Real.rpow_sub_one hna.ne' c]
    have : ‖a‖ ^ (c - 1) ≠ 0 := (Real.rpow_pos_of_pos hna _).ne'
    field_simp
  have h2 : ‖(y / a) ^ (c : ℂ) - (x / a) ^ (c : ℂ)‖ ≤ (‖D‖ + ε / ‖a‖ ^ c) * ‖y - x‖ := by
    calc ‖(y / a) ^ (c : ℂ) - (x / a) ^ (c : ℂ)‖
        ≤ ‖(y / a) ^ (c : ℂ) - (x / a) ^ (c : ℂ) - (y - x) • D‖ + ‖(y - x) • D‖ := by
          have := norm_add_le ((y / a) ^ (c : ℂ) - (x / a) ^ (c : ℂ) - (y - x) • D) ((y - x) • D)
          simpa using this
      _ ≤ ε / ‖a‖ ^ c * ‖y - x‖ + ‖y - x‖ * ‖D‖ := by
          gcongr
          exact le_of_eq (norm_smul _ _)
      _ = (‖D‖ + ε / ‖a‖ ^ c) * ‖y - x‖ := by ring
  calc ‖a‖ ^ c * |‖(y / a) ^ (c : ℂ) - 1‖ - ‖(x / a) ^ (c : ℂ) - 1‖|
      ≤ ‖a‖ ^ c * ‖(y / a) ^ (c : ℂ) - (x / a) ^ (c : ℂ)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hnac.le
        have := abs_norm_sub_norm_le ((y / a) ^ (c : ℂ) - 1) ((x / a) ^ (c : ℂ) - 1)
        simpa using this
    _ ≤ ‖a‖ ^ c * ((‖D‖ + ε / ‖a‖ ^ c) * ‖y - x‖) := mul_le_mul_of_nonneg_left h2 hnac.le
    _ = (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
        rw [← hDn]
        field_simp

/-- Helper for `s25e_cone_shortest`: the cone-distance potential `G` from `a ≠ 0` (the developed distance
`‖a‖^c ‖(w/a)^c - 1‖` in the sector `cos(π/c) ‖w/a‖ ≤ Re (w/a)`, and `‖a‖^c + ‖w‖^c` outside) has pointwise
Lipschitz constant at most the density `c ‖x‖^(c-1)` at every point. -/
theorem s25e_cone_pt {c : ℝ} (hc : 1 < c) {a : ℂ} (ha : a ≠ 0) {G : ℂ → ℝ}
    (hG : ∀ w, G w = if Real.cos (π / c) * ‖w / a‖ ≤ (w / a).re then ‖a‖ ^ c * ‖(w / a) ^ (c : ℂ) - 1‖
      else ‖a‖ ^ c + ‖w‖ ^ c)
    (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ → |G y - G x| ≤ (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
  classical
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnac : 0 < ‖a‖ ^ c := Real.rpow_pos_of_pos hna c
  have hc0 : 0 < c := by linarith
  set κ := Real.cos (π / c) with hκ
  set f : ℂ → ℝ := fun w => (w / a).re - κ * ‖w / a‖ with hfdef
  have hfc : Continuous f := by
    refine Continuous.sub ?_ (continuous_const.mul ?_)
    · exact Complex.continuous_re.comp (continuous_id.div_const a)
    · exact continuous_norm.comp (continuous_id.div_const a)
  have hsec_iff : ∀ w, κ * ‖w / a‖ ≤ (w / a).re ↔ 0 ≤ f w := fun w => by
    simp only [hfdef]; constructor <;> intro h <;> linarith
  have hGx : ∀ w, κ * ‖w / a‖ ≤ (w / a).re → G w = ‖a‖ ^ c * ‖(w / a) ^ (c : ℂ) - 1‖ := fun w h => by
    rw [hG w, if_pos h]
  have hGx' : ∀ w, ¬ κ * ‖w / a‖ ≤ (w / a).re → G w = ‖a‖ ^ c + ‖w‖ ^ c := fun w h => by
    rw [hG w, if_neg h]
  have hrad := s25e_radial_pt hc x hε
  obtain ⟨δr, hδr, hbr⟩ := hrad
  by_cases hx0 : x = 0
  · -- the apex
    subst hx0
    have hG0 : G 0 = ‖a‖ ^ c := by
      rw [hGx 0 (by simp), zero_div, Complex.zero_cpow (by exact_mod_cast hc0.ne')]
      simp
    have hbound : ∀ y : ℂ, |G y - G 0| ≤ ‖y‖ ^ c := by
      intro y
      rw [hG0]
      by_cases hy : κ * ‖y / a‖ ≤ (y / a).re
      · rw [hGx y hy]
        have h1 : ‖(y / a) ^ (c : ℂ)‖ = ‖y‖ ^ c / ‖a‖ ^ c := by
          rw [Complex.norm_cpow_real, norm_div, Real.div_rpow (norm_nonneg _) hna.le]
        have h2 : |‖(y / a) ^ (c : ℂ) - 1‖ - 1| ≤ ‖(y / a) ^ (c : ℂ)‖ := by
          simpa using abs_norm_sub_norm_le ((y / a) ^ (c : ℂ) - 1) (-1)
        calc |‖a‖ ^ c * ‖(y / a) ^ (c : ℂ) - 1‖ - ‖a‖ ^ c| = ‖a‖ ^ c * |‖(y / a) ^ (c : ℂ) - 1‖ - 1| := by
              rw [← mul_sub_one, abs_mul, abs_of_pos hnac]
          _ ≤ ‖a‖ ^ c * ‖(y / a) ^ (c : ℂ)‖ := mul_le_mul_of_nonneg_left h2 hnac.le
          _ = ‖y‖ ^ c := by rw [h1]; field_simp
      · rw [hGx' y hy]
        simp [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) c)]
    -- `‖y‖^c ≤ ε ‖y‖` for small `y`
    set δ := ε ^ (1 / (c - 1)) with hδdef
    have hδ : 0 < δ := Real.rpow_pos_of_pos hε _
    refine ⟨δ, hδ, fun y hy => ?_⟩
    rw [sub_zero] at hy ⊢
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
    have hδε : δ ^ (c - 1) = ε := by
      rw [hδdef, ← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have h1 : ‖y‖ ^ (c - 1) ≤ ε := by
      rw [← hδε]
      exact Real.rpow_le_rpow hy0 hy.le (by linarith)
    have h2 : ‖y‖ ^ c = ‖y‖ ^ (c - 1) * ‖y‖ := by
      rcases hy0.eq_or_lt with h | h
      · rw [← h]; simp [Real.zero_rpow hc0.ne']
      · rw [Real.rpow_sub_one h.ne']; field_simp
    calc |G y - G 0| ≤ ‖y‖ ^ c := hbound y
      _ = ‖y‖ ^ (c - 1) * ‖y‖ := h2
      _ ≤ ε * ‖y‖ := mul_le_mul_of_nonneg_right h1 hy0
      _ ≤ (c * ‖(0 : ℂ)‖ ^ (c - 1) + ε) * ‖y‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hy0
          have : 0 ≤ c * ‖(0 : ℂ)‖ ^ (c - 1) := by positivity
          linarith
  · have hx0n : 0 < ‖x‖ := norm_pos_iff.2 hx0
    by_cases hsx : κ * ‖x / a‖ ≤ (x / a).re
    · obtain ⟨hslit, -⟩ := s25e_sector_slit hc (div_ne_zero hx0 ha) hsx
      obtain ⟨δ1, hδ1, hb1⟩ := s25e_sector_pt hc ha hslit hε
      have hGxy : ∀ y : ℂ, κ * ‖y / a‖ ≤ (y / a).re → ‖y - x‖ < δ1 →
          |G y - G x| ≤ (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
        intro y hy hyd
        rw [hGx y hy, hGx x hsx, ← mul_sub, abs_mul, abs_of_pos hnac]
        exact hb1 y hyd
      by_cases hstrict : κ * ‖x / a‖ < (x / a).re
      · have hev : ∀ᶠ y in 𝓝 x, κ * ‖y / a‖ ≤ (y / a).re := by
          have : 0 < f x := by simp only [hfdef]; linarith
          filter_upwards [hfc.continuousAt.eventually (lt_mem_nhds this)] with y hy
          exact (hsec_iff y).2 hy.le
        obtain ⟨δ2, hδ2, hb2⟩ := Metric.eventually_nhds_iff.1 hev
        refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy => ?_⟩
        have hy2 : dist y x < δ2 := by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _)
        exact hGxy y (hb2 hy2) (lt_of_lt_of_le hy (min_le_left _ _))
      · -- on the boundary ray
        have heq : κ * ‖x / a‖ = (x / a).re := le_antisymm hsx (not_lt.1 hstrict)
        have hbd := s25e_sector_boundary hc (div_ne_zero hx0 ha) heq
        have hGxb : G x = ‖a‖ ^ c + ‖x‖ ^ c := by
          rw [hGx x hsx, hbd]
          have h1 : ‖-((‖x / a‖ ^ c : ℝ) : ℂ) - 1‖ = ‖x / a‖ ^ c + 1 := by
            have : -((‖x / a‖ ^ c : ℝ) : ℂ) - 1 = -(((‖x / a‖ ^ c + 1 : ℝ)) : ℂ) := by push_cast; ring
            rw [this, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          rw [h1, norm_div, Real.div_rpow (norm_nonneg _) hna.le]
          field_simp
          ring
        refine ⟨min δ1 δr, lt_min hδ1 hδr, fun y hy => ?_⟩
        have hy1 : ‖y - x‖ < δ1 := lt_of_lt_of_le hy (min_le_left _ _)
        have hyr : ‖y - x‖ < δr := lt_of_lt_of_le hy (min_le_right _ _)
        by_cases hys : κ * ‖y / a‖ ≤ (y / a).re
        · exact hGxy y hys hy1
        · rw [hGx' y hys, hGxb, add_sub_add_left_eq_sub]
          exact hbr y hyr
    · -- outside the sector
      have hev : ∀ᶠ y in 𝓝 x, ¬ κ * ‖y / a‖ ≤ (y / a).re := by
        have : f x < 0 := by
          simp only [hfdef]
          push Not at hsx
          linarith
        filter_upwards [hfc.continuousAt.eventually (gt_mem_nhds this)] with y hy
        intro h
        have := (hsec_iff y).1 h
        linarith
      obtain ⟨δ2, hδ2, hb2⟩ := Metric.eventually_nhds_iff.1 hev
      refine ⟨min δ2 δr, lt_min hδ2 hδr, fun y hy => ?_⟩
      have hy2 : dist y x < δ2 := by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _)
      have hyr : ‖y - x‖ < δr := lt_of_lt_of_le hy (min_le_right _ _)
      rw [hGx' y (hb2 hy2), hGx' x hsx, add_sub_add_left_eq_sub]
      exact hbr y hyr

/-- Helper for `s25e_cone_shortest`: a potential with pointwise Lipschitz constant `≤ c ‖x‖^(c-1)` (`c = (m+2)/2`),
vanishing at `a`, bounds from below the `Q_m`-length of every curve from `a` to `b` in the plane by its value at `b`. -/
theorem s25e_cone_lower (m : ℕ) {G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖)
    {a b : ℂ} (hGa : G a = 0) {γ : LRCurve} (hγ : IsPathIn univ a b γ) :
    ENNReal.ofReal (G b) ≤ phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ := by
  obtain ⟨⟨K, hK⟩, h0, h1, -⟩ := hγ
  have hρ : ∀ x, Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖ =
      (((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) := fun x => s25e_rho_eq m x
  have hρc : Continuous fun x : ℂ => Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖ := by fun_prop
  have := s25e_potential (ρ := fun x : ℂ => Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖) (G := G) hρc
    (fun x => Real.sqrt_nonneg _) ?_ (fun x ε hε => by simpa only [hρ] using hG x ε hε) zero_le_one hK
  · rw [h0, h1, hGa, sub_zero] at this
    exact this
  · refine continuous_iff_continuousAt.2 fun x => ?_
    rw [Metric.continuousAt_iff]
    intro e he
    set R : ℝ := (((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) with hR
    have hR0 : 0 ≤ R := by positivity
    obtain ⟨δ, hδ, hb⟩ := hG x 1 one_pos
    refine ⟨min δ (e / (R + 1 + 1)), lt_min hδ (by positivity), fun y hy => ?_⟩
    rw [dist_eq_norm] at hy
    have h1 : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
    have h2 : ‖y - x‖ < e / (R + 1 + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    rw [Real.dist_eq]
    calc |G y - G x| ≤ (R + 1) * ‖y - x‖ := hb y h1
      _ ≤ (R + 1 + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
      _ < e := by
          rw [lt_div_iff₀ (by positivity)] at h2
          nlinarith

/-- Helper for `s25e_cone_shortest`, the flat case `m = 0`. -/
theorem s25e_cone_flat (m : ℕ) (hm : m = 0) {r : ℝ} (hr : 0 < r) {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) :
    ∃ G : ℂ → ℝ, (∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
        |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖) ∧
      G a = 0 ∧ 0 ≤ G b ∧ G b ≤ ‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2) ∧
      ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
        phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ ≤ ENNReal.ofReal (G b) := by
  subst hm
  refine ⟨fun w => ‖w - a‖, fun x ε hε => ⟨ε, hε, fun y hy => ?_⟩, by simp, norm_nonneg _, ?_, ?_⟩
  · have h1 : |‖y - a‖ - ‖x - a‖| ≤ ‖y - x‖ := by
      simpa using abs_norm_sub_norm_le (y - a) (x - a)
    have h2 : ‖y - x‖ ≤ ((((0 : ℕ) : ℝ) + 2) / 2 * ‖x‖ ^ ((((0 : ℕ) : ℝ) + 2) / 2 - 1) + ε) * ‖y - x‖ := by
      have : (((0 : ℕ) : ℝ) + 2) / 2 * ‖x‖ ^ ((((0 : ℕ) : ℝ) + 2) / 2 - 1) = 1 := by simp
      rw [this]
      nlinarith [norm_nonneg (y - x)]
    exact h1.trans h2
  · have : (((0 : ℕ) : ℝ) + 2) / 2 = 1 := by norm_num
    rw [this, Real.rpow_one, Real.rpow_one]
    exact (norm_sub_le b a).trans (le_of_eq (add_comm _ _))
  · set γ : LRCurve := ⟨fun t : ℝ => a + (t : ℂ) * (b - a),
      (LipschitzWith.of_dist_le_mul (K := ‖b - a‖₊) (fun s t => by
        simp only [dist_eq_norm]
        rw [show a + (s : ℂ) * (b - a) - (a + (t : ℂ) * (b - a)) = ((s : ℂ) - t) * (b - a) by ring,
          norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_comm])).locallyLipschitz.locallyLipschitzOn⟩ with hγ
    have hγd : ∀ t : ℝ, HasDerivAt γ.toFun (b - a) t := fun t => by
      exact (hasDerivAt_ofReal_mul (b - a) t).const_add a
    refine ⟨γ, ⟨⟨‖b - a‖₊, (LipschitzWith.of_dist_le_mul (K := ‖b - a‖₊) (fun s t => by
        show dist (a + (s : ℂ) * (b - a)) (a + (t : ℂ) * (b - a)) ≤ _
        simp only [dist_eq_norm]
        rw [show a + (s : ℂ) * (b - a) - (a + (t : ℂ) * (b - a)) = ((s : ℂ) - t) * (b - a) by ring,
          norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_comm])).lipschitzOnWith⟩, by simp [hγ], by simp [hγ], ?_⟩, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      show a + (t : ℂ) * (b - a) ∈ ball (0 : ℂ) r
      have : a + (t : ℂ) * (b - a) = (1 - t : ℝ) • a + (t : ℝ) • b := by
        simp only [Complex.real_smul]; push_cast; ring
      rw [this]
      exact (convex_ball (0 : ℂ) r) ha hb (by linarith [ht.2]) ht.1 (by ring)
    · unfold phiLength LRCurve.rhoLength phiDensity
      have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt ‖((((0 : ℕ) : ℂ) + 2) / 2) ^ 2 *
          γ.toFun t ^ 0‖) * ‖deriv γ.toFun t‖ₑ = ‖b - a‖ₑ := by
        intro t _
        rw [(hγd t).deriv]
        simp
      rw [setLIntegral_congr_fun measurableSet_Ioo hpt, setLIntegral_const, Real.volume_Ioo]
      simp [ofReal_norm]

/-- Helper for `s25e_cone_shortest`: the `Q_m`-length of a radial piece `t ↦ (α + β t) v` (`α + β t ≥ 0` on
`[t₀, t₁]`) is `‖v‖^c |s(t₁)^c - s(t₀)^c|`. -/
theorem s25e_radial_len {c : ℝ} (hc : 1 < c) {v : ℂ} {α β : ℝ} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hs0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ α + β * t) :
    ∫⁻ t in Ioo t₀ t₁, ENNReal.ofReal (c * ‖((α + β * t : ℝ) : ℂ) * v‖ ^ (c - 1)) *
        ‖deriv (fun t : ℝ => ((α + β * t : ℝ) : ℂ) * v) t‖ₑ =
      ENNReal.ofReal (‖v‖ ^ c * |(α + β * t₁) ^ c - (α + β * t₀) ^ c|) := by
  have hc0 : 0 < c := by linarith
  set s : ℝ → ℝ := fun t => α + β * t with hsdef
  have hs : ∀ t, HasDerivAt s β t := fun t =>
    (((hasDerivAt_id' t).const_mul β).const_add α).congr_deriv (mul_one β)
  set F : ℝ → ℝ := fun t => ‖v‖ ^ c * s t ^ c with hF
  set F' : ℝ → ℝ := fun t => ‖v‖ ^ c * (c * s t ^ (c - 1) * β) with hF'
  have hFd : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (F' t) t := by
    intro t ht
    have := ((hs t).rpow_const (Or.inr hc.le)).const_mul (‖v‖ ^ c)
    convert this using 1
    simp only [hF']; ring
  have hF'c : ContinuousOn F' (Icc t₀ t₁) := by
    have h1 : ContinuousOn (fun t => s t ^ (c - 1)) (Icc t₀ t₁) := fun t ht =>
      ((Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).comp (hs t).continuousAt).continuousWithinAt
    exact continuousOn_const.mul ((continuousOn_const.mul h1).mul continuousOn_const)
  have hint : IntervalIntegrable F' volume t₀ t₁ :=
    (hF'c.mono (by rw [uIcc_of_le h01])).intervalIntegrable
  have hIntF' : IntegrableOn F' (Ioo t₀ t₁) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le h01).1 hint
  have hpt : ∀ t ∈ Ioo t₀ t₁, ENNReal.ofReal (c * ‖(s t : ℂ) * v‖ ^ (c - 1)) *
        ‖deriv (fun t : ℝ => (s t : ℂ) * v) t‖ₑ = ENNReal.ofReal |F' t| := by
    intro t ht
    have hd : HasDerivAt (fun t : ℝ => (s t : ℂ) * v) ((β : ℂ) * v) t := by
      simpa using ((hs t).ofReal_comp).mul_const v
    rw [hd.deriv, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hst : 0 ≤ s t := hs0 t (Ioo_subset_Icc_self ht)
    have e1 : ‖(s t : ℂ) * v‖ = s t * ‖v‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hst]
    have e2 : ‖(β : ℂ) * v‖ = |β| * ‖v‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e3 : ‖v‖ ^ c = ‖v‖ ^ (c - 1) * ‖v‖ := by
      rcases (norm_nonneg v).eq_or_lt with h | h
      · rw [← h]; simp [Real.zero_rpow hc0.ne', Real.zero_rpow (by linarith : c - 1 ≠ 0)]
      · rw [Real.rpow_sub_one h.ne']; field_simp
    rw [e1, e2, Real.mul_rpow hst (norm_nonneg v), hF', abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖v‖ ^ c), abs_of_nonneg hc0.le,
      abs_of_nonneg (Real.rpow_nonneg hst _), e3]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
  by_cases hβ : 0 ≤ β
  · have hnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ F' t := fun t ht => by
      have := hs0 t ht
      simp only [hF']; positivity
    rw [setLIntegral_congr_fun measurableSet_Ioo
        (fun t ht => by rw [abs_of_nonneg (hnn t (Ioo_subset_Icc_self ht))]),
      ← ofReal_integral_eq_lintegral_ofReal hIntF' (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using hnn t (Ioo_subset_Icc_self ht)),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h01,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hFd t (by rwa [uIcc_of_le h01] at ht)) hint]
    congr 1
    have hmo : s t₀ ^ c ≤ s t₁ ^ c :=
      Real.rpow_le_rpow (hs0 t₀ ⟨le_rfl, h01⟩) (by simp only [hsdef]; nlinarith) hc0.le
    rw [show (α + β * t₁) ^ c - (α + β * t₀) ^ c = s t₁ ^ c - s t₀ ^ c from rfl,
      abs_of_nonneg (sub_nonneg.2 hmo)]
    simp only [hF]; ring
  · push Not at hβ
    have hnn : ∀ t ∈ Icc t₀ t₁, F' t ≤ 0 := fun t ht => by
      have := hs0 t ht
      simp only [hF']
      have : 0 ≤ ‖v‖ ^ c * (c * s t ^ (c - 1)) := by positivity
      nlinarith
    rw [setLIntegral_congr_fun measurableSet_Ioo
        (fun t ht => by rw [abs_of_nonpos (hnn t (Ioo_subset_Icc_self ht))]),
      ← ofReal_integral_eq_lintegral_ofReal (f := fun x => -F' x) hIntF'.neg (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have := hnn t (Ioo_subset_Icc_self ht)
        simpa using this),
      integral_neg, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h01,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hFd t (by rwa [uIcc_of_le h01] at ht)) hint]
    congr 1
    have hmo : s t₁ ^ c ≤ s t₀ ^ c :=
      Real.rpow_le_rpow (hs0 t₁ ⟨h01, le_rfl⟩) (by simp only [hsdef]; nlinarith) hc0.le
    rw [show (α + β * t₁) ^ c - (α + β * t₀) ^ c = s t₁ ^ c - s t₀ ^ c from rfl,
      abs_of_nonpos (sub_nonpos.2 hmo)]
    simp only [hF]; ring

/-- Helper for `s25e_cone_shortest`: the broken radial segment `a → 0 → b` in the disc has `Q_m`-length
`‖a‖^c + ‖b‖^c`. -/
theorem s25e_apex_curve (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) :
    ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ =
        ENNReal.ofReal (‖a‖ ^ ((((m : ℝ) + 2) / 2)) + ‖b‖ ^ ((((m : ℝ) + 2) / 2))) := by
  set c : ℝ := ((m : ℝ) + 2) / 2 with hcdef
  have hc : 1 < c := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hcdef]; linarith
  have hc0 : 0 < c := by linarith
  set g : ℝ → ℂ := fun t => ((max 0 (1 - 2 * t) : ℝ) : ℂ) * a + ((max 0 (2 * t - 1) : ℝ) : ℂ) * b with hg
  have hlip : LipschitzWith (2 * ‖a‖₊ + 2 * ‖b‖₊) g := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    simp only [dist_eq_norm, hg, Real.norm_eq_abs]
    have h1 : |max 0 (1 - 2 * s) - max 0 (1 - 2 * t)| ≤ 2 * |s - t| := by
      rw [max_comm 0 (1 - 2 * s), max_comm 0 (1 - 2 * t)]
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [show 1 - 2 * s - (1 - 2 * t) = -2 * (s - t) by ring, abs_mul]; simp
    have h2 : |max 0 (2 * s - 1) - max 0 (2 * t - 1)| ≤ 2 * |s - t| := by
      rw [max_comm 0 (2 * s - 1), max_comm 0 (2 * t - 1)]
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [show 2 * s - 1 - (2 * t - 1) = 2 * (s - t) by ring, abs_mul]; simp
    calc ‖((max 0 (1 - 2 * s) : ℝ) : ℂ) * a + ((max 0 (2 * s - 1) : ℝ) : ℂ) * b -
          (((max 0 (1 - 2 * t) : ℝ) : ℂ) * a + ((max 0 (2 * t - 1) : ℝ) : ℂ) * b)‖
        = ‖(((max 0 (1 - 2 * s) - max 0 (1 - 2 * t) : ℝ) : ℂ)) * a +
            (((max 0 (2 * s - 1) - max 0 (2 * t - 1) : ℝ) : ℂ)) * b‖ := by
          congr 1; push_cast; ring
      _ ≤ |max 0 (1 - 2 * s) - max 0 (1 - 2 * t)| * ‖a‖ +
            |max 0 (2 * s - 1) - max 0 (2 * t - 1)| * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * |s - t| * ‖a‖ + 2 * |s - t| * ‖b‖ := by gcongr
      _ = ((2 * ‖a‖₊ + 2 * ‖b‖₊ : ℝ≥0) : ℝ) * |s - t| := by
          push_cast; ring
  set γ : LRCurve := ⟨g, hlip.locallyLipschitz.locallyLipschitzOn⟩ with hγ
  have hg0 : g 0 = a := by simp [hg]
  have hg1 : g 1 = b := by simp [hg]; norm_num
  refine ⟨γ, ⟨⟨_, hlip.lipschitzOnWith⟩, hg0, hg1, ?_⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    show g t ∈ ball (0 : ℂ) r
    rw [mem_ball_zero_iff] at ha hb ⊢
    have hM : max ‖a‖ ‖b‖ < r := max_lt ha hb
    simp only [hg]
    rcases le_total t (1 / 2) with h | h
    · have e1 : max 0 (2 * t - 1) = 0 := max_eq_left (by linarith)
      have e2 : max 0 (1 - 2 * t) = 1 - 2 * t := max_eq_right (by linarith [ht.1])
      rw [e1, e2]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.1] : 0 ≤ 1 - 2 * t)]
      calc (1 - 2 * t) * ‖a‖ ≤ 1 * ‖a‖ :=
            mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
        _ ≤ max ‖a‖ ‖b‖ := by rw [one_mul]; exact le_max_left _ _
        _ < r := hM
    · have e1 : max 0 (1 - 2 * t) = 0 := max_eq_left (by linarith)
      have e2 : max 0 (2 * t - 1) = 2 * t - 1 := max_eq_right (by linarith)
      rw [e1, e2]
      simp only [Complex.ofReal_zero, zero_mul, zero_add]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * t - 1)]
      calc (2 * t - 1) * ‖b‖ ≤ 1 * ‖b‖ :=
            mul_le_mul_of_nonneg_right (by linarith [ht.2]) (norm_nonneg _)
        _ ≤ max ‖a‖ ‖b‖ := by rw [one_mul]; exact le_max_right _ _
        _ < r := hM
  · have hdens : ∀ z : ℂ, phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) z =
        ENNReal.ofReal (c * ‖z‖ ^ (c - 1)) := fun z => by
      unfold phiDensity
      rw [s25e_rho_eq]
    unfold phiLength LRCurve.rhoLength
    simp only [hdens]
    have hI : ∀ (u v : ℝ) (huv : u ≤ v), 0 ≤ u →
        ∫⁻ t in Ioo u v, ENNReal.ofReal (c * ‖γ.toFun t‖ ^ (c - 1)) * ‖deriv γ.toFun t‖ₑ =
          ∫⁻ t in Ioc u v, ENNReal.ofReal (c * ‖γ.toFun t‖ ^ (c - 1)) * ‖deriv γ.toFun t‖ₑ :=
      fun u v _ _ => setLIntegral_congr Ioo_ae_eq_Ioc
    rw [hI 0 1 zero_le_one le_rfl, ← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1),
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      ← hI 0 (1 / 2) (by norm_num) le_rfl, ← hI (1 / 2) 1 (by norm_num) (by norm_num)]
    have hA : ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (c * ‖γ.toFun t‖ ^ (c - 1)) * ‖deriv γ.toFun t‖ₑ =
        ENNReal.ofReal (‖a‖ ^ c) := by
      have h := s25e_radial_len hc (v := a) (α := 1) (β := -2) (t₀ := 0) (t₁ := 1 / 2) (by norm_num)
        (fun t ht => by linarith [ht.2])
      rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun t =>
        ENNReal.ofReal (c * ‖((1 + -2 * t : ℝ) : ℂ) * a‖ ^ (c - 1)) *
          ‖deriv (fun t : ℝ => ((1 + -2 * t : ℝ) : ℂ) * a) t‖ₑ)]
      · rw [h]
        congr 1
        norm_num [Real.zero_rpow hc0.ne']
      · intro t ht
        have hev : γ.toFun =ᶠ[𝓝 t] fun t : ℝ => ((1 + -2 * t : ℝ) : ℂ) * a := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
          show g u = _
          simp only [hg]
          rw [max_eq_right (by linarith [hu.2] : 0 ≤ 1 - 2 * u), max_eq_left (by linarith [hu.2] : 2 * u - 1 ≤ 0)]
          simp only [Complex.ofReal_zero, zero_mul, add_zero]
          congr 2; ring
        beta_reduce
        rw [hev.deriv_eq, hev.eq_of_nhds]
    have hB : ∫⁻ t in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal (c * ‖γ.toFun t‖ ^ (c - 1)) * ‖deriv γ.toFun t‖ₑ =
        ENNReal.ofReal (‖b‖ ^ c) := by
      have h := s25e_radial_len hc (v := b) (α := -1) (β := 2) (t₀ := 1 / 2) (t₁ := 1) (by norm_num)
        (fun t ht => by linarith [ht.1])
      rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun t =>
        ENNReal.ofReal (c * ‖((-1 + 2 * t : ℝ) : ℂ) * b‖ ^ (c - 1)) *
          ‖deriv (fun t : ℝ => ((-1 + 2 * t : ℝ) : ℂ) * b) t‖ₑ)]
      · rw [h]
        congr 1
        norm_num [Real.zero_rpow hc0.ne']
      · intro t ht
        have hev : γ.toFun =ᶠ[𝓝 t] fun t : ℝ => ((-1 + 2 * t : ℝ) : ℂ) * b := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
          show g u = _
          simp only [hg]
          rw [max_eq_left (by linarith [hu.1] : 1 - 2 * u ≤ 0), max_eq_right (by linarith [hu.1] : 0 ≤ 2 * u - 1)]
          simp only [Complex.ofReal_zero, zero_mul, zero_add]
          congr 2; ring
        beta_reduce
        rw [hev.deriv_eq, hev.eq_of_nhds]
    rw [hA, hB, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Helper for `s25e_cone_shortest`: strictly inside the sector, `|arg z| < π/c`. -/
theorem s25e_sector_strict {c : ℝ} (hc : 1 < c) {z : ℂ} (hz0 : z ≠ 0)
    (hsec : Real.cos (π / c) * ‖z‖ < z.re) : |Complex.arg z| < π / c := by
  have hπc : π / c < π := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hπc0 : 0 < π / c := by positivity
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcos : Real.cos (π / c) < Real.cos (Complex.arg z) := by
    rw [Complex.cos_arg hz0, lt_div_iff₀ hnz]
    linarith
  by_contra h
  rw [not_lt] at h
  have h1 : Real.cos |Complex.arg z| ≤ Real.cos (π / c) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hπc0.le (Complex.abs_arg_le_pi z) h
  rw [Real.cos_abs] at h1
  linarith

/-- Helper for `s25e_cone_shortest`: for `|arg z| < π/c`, the power `z^c` lies in the slit plane and `(z^c)^(1/c) = z`. -/
theorem s25e_cpow_cpow_inv {c : ℝ} (hc : 1 < c) {z : ℂ} (hz0 : z ≠ 0) (habs : |Complex.arg z| < π / c) :
    z ^ (c : ℂ) ∈ Complex.slitPlane ∧ (z ^ (c : ℂ)) ^ ((1 / c : ℝ) : ℂ) = z := by
  have hc0 : 0 < c := by linarith
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hθc : |Complex.arg z * c| < π := by
    rw [abs_mul, abs_of_pos hc0]
    have := (lt_div_iff₀ hc0).1 habs
    linarith
  have hθ1 : -π < Complex.arg z * c := (abs_lt.1 hθc).1
  have hθ2 : Complex.arg z * c < π := (abs_lt.1 hθc).2
  have hpow : z ^ (c : ℂ) = ((‖z‖ ^ c : ℝ) : ℂ) * (Complex.cos ((Complex.arg z * c : ℝ) : ℂ) +
      Complex.sin ((Complex.arg z * c : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hz0, Complex.log]
    have h1 : (↑(Real.log ‖z‖) + ↑(Complex.arg z) * Complex.I) * (c : ℂ) =
        ((Real.log ‖z‖ * c : ℝ) : ℂ) + ((Complex.arg z * c : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hnz, Complex.exp_mul_I]
  have hnorm : 0 < ‖z‖ ^ c := Real.rpow_pos_of_pos hnz c
  have harg : Complex.arg (z ^ (c : ℂ)) = Complex.arg z * c := by
    rw [hpow]
    exact Complex.arg_mul_cos_add_sin_mul_I hnorm ⟨hθ1, hθ2.le⟩
  have hz1 : z ^ (c : ℂ) ≠ 0 := by
    rw [hpow]
    intro h
    have := congrArg (fun w : ℂ => ‖w‖) h
    simp only [norm_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnorm.le] at this
    have h2 : ‖Complex.cos ((Complex.arg z * c : ℝ) : ℂ) + Complex.sin ((Complex.arg z * c : ℝ) : ℂ) * Complex.I‖ = 1 := by
      rw [← Complex.exp_mul_I]; exact Complex.norm_exp_ofReal_mul_I _
    rw [h2] at this
    linarith
  refine ⟨Complex.mem_slitPlane_iff_arg.2 ⟨by rw [harg]; linarith, hz1⟩, ?_⟩
  have hcm := Complex.cpow_mul (x := z) (y := (c : ℂ)) ((1 / c : ℝ) : ℂ)
    (by simpa [Complex.log_im, mul_comm] using hθ1) (by simpa [Complex.log_im, mul_comm] using hθ2.le)
  rw [← hcm]
  have : (c : ℂ) * ((1 / c : ℝ) : ℂ) = 1 := by
    have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast; field_simp
  rw [this, Complex.cpow_one]

/-- Helper for `s25e_cone_shortest`: the integrand `ρ(w) ‖w'‖` along `w = a z^(1/c)` is `‖a‖^c ‖z'‖`. -/
theorem s25e_sector_integrand {c : ℝ} (hc : 1 < c) {a z d : ℂ} (ha : a ≠ 0) (hz : z ≠ 0) :
    ENNReal.ofReal (c * ‖a * z ^ ((1 / c : ℝ) : ℂ)‖ ^ (c - 1)) *
        ‖a * (((1 / c : ℝ) : ℂ) * z ^ (((1 / c : ℝ) : ℂ) - 1) * d)‖ₑ = ENNReal.ofReal (‖a‖ ^ c * ‖d‖) := by
  have hc0 : 0 < c := by linarith
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : ((1 / c : ℝ) : ℂ) - 1 = ((1 / c - 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [norm_mul, e1, Complex.norm_cpow_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 / c)]
  rw [Real.mul_rpow hna.le (Real.rpow_nonneg hnz.le _), ← Real.rpow_mul hnz.le]
  have e2 : ‖a‖ ^ c = ‖a‖ ^ (c - 1) * ‖a‖ := by rw [Real.rpow_sub_one hna.ne']; field_simp
  have e3 : ‖z‖ ^ (1 / c * (c - 1)) * ‖z‖ ^ (1 / c - 1) = 1 := by
    rw [← Real.rpow_add hnz]
    have : 1 / c * (c - 1) + (1 / c - 1) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  calc c * (‖a‖ ^ (c - 1) * ‖z‖ ^ (1 / c * (c - 1))) * (‖a‖ * (1 / c * ‖z‖ ^ (1 / c - 1) * ‖d‖))
      = (c * (1 / c)) * ‖a‖ ^ (c - 1) * ‖a‖ * (‖z‖ ^ (1 / c * (c - 1)) * ‖z‖ ^ (1 / c - 1)) * ‖d‖ := by ring
    _ = ‖a‖ ^ c * ‖d‖ := by
        rw [e3, e2]
        field_simp

/-- Helper for `s25e_cone_shortest`: for `b` strictly inside the sector of `a`, the developed straight segment
`t ↦ a (1 + t ((b/a)^c - 1))^(1/c)` is a Lipschitz curve in the disc from `a` to `b` of `Q_m`-length
`‖a‖^c ‖(b/a)^c - 1‖`. -/
theorem s25e_sector_curve (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) (ha0 : a ≠ 0)
    (hstrict : Real.cos (π / ((((m : ℝ) + 2) / 2))) * ‖b / a‖ < (b / a).re) :
    ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ =
        ENNReal.ofReal (‖a‖ ^ ((((m : ℝ) + 2) / 2)) * ‖(b / a) ^ ((((m : ℝ) + 2) / 2 : ℝ) : ℂ) - 1‖) := by
  set c : ℝ := ((m : ℝ) + 2) / 2 with hcdef
  have hc : 1 < c := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hcdef]; linarith
  have hc0 : 0 < c := by linarith
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hstrict
  have hba0 : b / a ≠ 0 := div_ne_zero hb0 ha0
  have habs := s25e_sector_strict hc hba0 hstrict
  obtain ⟨hzs, hinv⟩ := s25e_cpow_cpow_inv hc hba0 habs
  set zb : ℂ := (b / a) ^ (c : ℂ) with hzb
  set d : ℂ := zb - 1 with hd
  set zt : ℝ → ℂ := fun t => 1 + (t : ℂ) * d with hzt
  have hztd : ∀ t : ℝ, HasDerivAt zt d t := fun t => (hasDerivAt_ofReal_mul d t).const_add 1
  have hztslit : ∀ t ∈ Icc (0 : ℝ) 1, zt t ∈ Complex.slitPlane := by
    intro t ht
    have hre : (zt t).re = 1 + t * (zb.re - 1) := by simp [hzt, hd]
    have him : (zt t).im = t * zb.im := by simp [hzt, hd]
    rw [Complex.mem_slitPlane_iff] at hzs ⊢
    rw [hre, him]
    rcases hzs with h | h
    · left
      rcases ht.2.eq_or_lt with h1 | h1
      · rw [h1]; linarith
      · nlinarith [mul_nonneg ht.1 h.le]
    · by_cases ht0 : t = 0
      · left; rw [ht0]; norm_num
      · right
        exact mul_ne_zero ht0 h
  have hzt0 : ∀ t ∈ Icc (0 : ℝ) 1, zt t ≠ 0 := fun t ht h => by
    have := hztslit t ht
    rw [h] at this
    exact Complex.zero_notMem_slitPlane this
  -- the minimum of `‖zt‖` on `[0, 1]`
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (f := fun t : ℝ => ‖zt t‖) (by
      refine continuous_norm.comp_continuousOn ?_
      exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
  set μ : ℝ := ‖zt t₀‖ with hμ
  have hμ0 : 0 < μ := norm_pos_iff.2 (hzt0 t₀ ht₀)
  have hμle : ∀ t ∈ Icc (0 : ℝ) 1, μ ≤ ‖zt t‖ := fun t ht => hmin ht
  set p : ℝ := 1 / c with hp
  set w : ℝ → ℂ := fun t => a * zt t ^ (p : ℂ) with hw
  have hwd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (a * ((p : ℂ) * zt t ^ ((p : ℂ) - 1) * d)) t := by
    intro t ht
    have h1 := (Complex.hasStrictDerivAt_cpow_const (c := (p : ℂ)) (hztslit t ht)).hasDerivAt
    have h2 := (h1.scomp t (hztd t)).const_mul a
    exact h2.congr_deriv (by rw [smul_eq_mul]; ring)
  have hpexp : p - 1 ≤ 0 := by
    rw [hp, div_sub_one hc0.ne', div_nonpos_iff]
    right; exact ⟨by linarith, hc0.le⟩
  have hnorm_der : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖a * ((p : ℂ) * zt t ^ ((p : ℂ) - 1) * d)‖ ≤ ‖a‖ * (p * μ ^ (p - 1) * ‖d‖) := by
    intro t ht
    have e1 : (p : ℂ) - 1 = ((p - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, norm_mul, norm_mul, e1, Complex.norm_cpow_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ p)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)) hna.le
    exact Real.rpow_le_rpow_of_nonpos hμ0 (hμle t ht) hpexp
  set K : ℝ≥0 := ⟨‖a‖ * (p * μ ^ (p - 1) * ‖d‖), by positivity⟩ with hK
  have hLip : LipschitzOnWith K w (Icc 0 1) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun t ht => (hwd t ht).differentiableAt) ?_
      (convex_Icc 0 1)
    intro t ht
    rw [(hwd t ht).deriv]
    exact_mod_cast hnorm_der t ht
  set γ : LRCurve := ⟨w, fun x _ => ⟨K, Ioo 0 1, self_mem_nhdsWithin, hLip.mono Ioo_subset_Icc_self⟩⟩ with hγ
  have hw0 : w 0 = a := by simp [hw, hzt]
  have hw1 : w 1 = b := by
    have : zt 1 = zb := by simp [hzt, hd]
    simp only [hw, this]
    have h2 : zb ^ ((p : ℝ) : ℂ) = b / a := hinv
    rw [h2]; field_simp
  refine ⟨γ, ⟨⟨K, hLip⟩, hw0, hw1, ?_⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    show w t ∈ ball (0 : ℂ) r
    rw [mem_ball_zero_iff] at ha hb ⊢
    set q := max 1 ‖b / a‖ with hq
    have hq1 : 1 ≤ q := le_max_left _ _
    have hq0 : 0 ≤ q := by linarith
    have hzbn : ‖zb‖ = ‖b / a‖ ^ c := by rw [hzb, Complex.norm_cpow_real]
    have hqc : ‖zt t‖ ≤ q ^ c := by
      have h1 : ‖zt t‖ ≤ (1 - t) * 1 + t * ‖zb‖ := by
        have : zt t = ((1 - t : ℝ) : ℂ) * 1 + (t : ℂ) * zb := by simp [hzt, hd]; ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.2]),
          Real.norm_of_nonneg ht.1, norm_one]
      have h2 : (1 : ℝ) ≤ q ^ c := Real.one_le_rpow hq1 hc0.le
      have h3 : ‖zb‖ ≤ q ^ c := by
        rw [hzbn]; exact Real.rpow_le_rpow (norm_nonneg _) (le_max_right _ _) hc0.le
      nlinarith [ht.1, ht.2]
    have hwn : ‖w t‖ = ‖a‖ * ‖zt t‖ ^ p := by
      simp only [hw, norm_mul, Complex.norm_cpow_real]
    have hpq : ‖zt t‖ ^ p ≤ q := by
      calc ‖zt t‖ ^ p ≤ (q ^ c) ^ p := Real.rpow_le_rpow (norm_nonneg _) hqc (by positivity)
        _ = q := by rw [hp, one_div, Real.rpow_rpow_inv hq0 hc0.ne']
    calc ‖w t‖ = ‖a‖ * ‖zt t‖ ^ p := hwn
      _ ≤ ‖a‖ * q := mul_le_mul_of_nonneg_left hpq hna.le
      _ = max ‖a‖ ‖b‖ := by
          rw [hq, mul_max_of_nonneg _ _ hna.le, mul_one, norm_div, mul_div_cancel₀ _ hna.ne']
      _ < r := max_lt ha hb
  · have hdens : ∀ z : ℂ, phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) z =
        ENNReal.ofReal (c * ‖z‖ ^ (c - 1)) := fun z => by
      unfold phiDensity
      rw [s25e_rho_eq]
    unfold phiLength LRCurve.rhoLength
    simp only [hdens]
    have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (c * ‖γ.toFun t‖ ^ (c - 1)) * ‖deriv γ.toFun t‖ₑ =
        ENNReal.ofReal (‖a‖ ^ c * ‖d‖) := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      show ENNReal.ofReal (c * ‖w t‖ ^ (c - 1)) * ‖deriv w t‖ₑ = _
      rw [(hwd t htI).deriv]
      exact s25e_sector_integrand hc ha0 (hzt0 t htI)
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt, setLIntegral_const, Real.volume_Ioo]
    simp

/-- Helper for `s25e_cone_shortest`: on the boundary rays of the sector the developed distance is `‖a‖^c + ‖x‖^c`. -/
theorem s25e_cone_boundary_val {c : ℝ} (hc : 1 < c) {a x : ℂ} (ha : a ≠ 0) (hx : x ≠ 0)
    (heq : Real.cos (π / c) * ‖x / a‖ = (x / a).re) :
    ‖a‖ ^ c * ‖(x / a) ^ (c : ℂ) - 1‖ = ‖a‖ ^ c + ‖x‖ ^ c := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hbd := s25e_sector_boundary hc (div_ne_zero hx ha) heq
  have h1 : ‖-((‖x / a‖ ^ c : ℝ) : ℂ) - 1‖ = ‖x / a‖ ^ c + 1 := by
    have : -((‖x / a‖ ^ c : ℝ) : ℂ) - 1 = -(((‖x / a‖ ^ c + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [this, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hbd, h1, norm_div, Real.div_rpow (norm_nonneg _) hna.le]
  have : ‖a‖ ^ c ≠ 0 := (Real.rpow_pos_of_pos hna c).ne'
  field_simp
  ring

/-- Helper for `s25e_cone_shortest`, `m ≥ 1`, `a = 0`. -/
theorem s25e_cone_case_zero (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) (ha0 : a = 0) :
    ∃ G : ℂ → ℝ, (∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
        |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖) ∧
      G a = 0 ∧ 0 ≤ G b ∧ G b ≤ ‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2) ∧
      ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
        phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ ≤ ENNReal.ofReal (G b) := by
  subst ha0
  have hc : 1 < ((m : ℝ) + 2) / 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hc0 : ((m : ℝ) + 2) / 2 ≠ 0 := by linarith
  refine ⟨fun w => ‖w‖ ^ (((m : ℝ) + 2) / 2), fun x ε hε => ?_, by simp [Real.zero_rpow hc0],
    Real.rpow_nonneg (norm_nonneg _) _, by simp [Real.zero_rpow hc0], ?_⟩
  · obtain ⟨δ, hδ, hb⟩ := s25e_radial_pt hc x hε
    exact ⟨δ, hδ, hb⟩
  · obtain ⟨γ, hγ, hlen⟩ := s25e_apex_curve m hm ha hb
    refine ⟨γ, hγ, le_of_eq ?_⟩
    rw [hlen]
    simp [Real.zero_rpow hc0]

/-- Helper for `s25e_cone_shortest`, `m ≥ 1`, `a ≠ 0`, `b` not strictly inside the sector of `a`. -/
theorem s25e_cone_case_apex (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) (ha0 : a ≠ 0)
    (hns : ¬ Real.cos (π / ((((m : ℝ) + 2) / 2))) * ‖b / a‖ < (b / a).re) :
    ∃ G : ℂ → ℝ, (∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
        |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖) ∧
      G a = 0 ∧ 0 ≤ G b ∧ G b ≤ ‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2) ∧
      ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
        phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ ≤ ENNReal.ofReal (G b) := by
  set c : ℝ := ((m : ℝ) + 2) / 2 with hcdef
  have hc : 1 < c := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hcdef]; linarith
  have hc0 : 0 < c := by linarith
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  set G : ℂ → ℝ := fun w => if Real.cos (π / c) * ‖w / a‖ ≤ (w / a).re then
    ‖a‖ ^ c * ‖(w / a) ^ (c : ℂ) - 1‖ else ‖a‖ ^ c + ‖w‖ ^ c with hG
  have hGa : G a = 0 := by
    have h1 : Real.cos (π / c) * ‖a / a‖ ≤ (a / a).re := by
      rw [div_self ha0]; simp [Real.cos_le_one]
    simp only [hG, if_pos h1, div_self ha0, Complex.one_cpow, sub_self, norm_zero, mul_zero]
  have hGb : G b = ‖a‖ ^ c + ‖b‖ ^ c := by
    by_cases hb0 : b = 0
    · subst hb0
      have h1 : Real.cos (π / c) * ‖(0 : ℂ) / a‖ ≤ ((0 : ℂ) / a).re := by simp
      have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast (by linarith : c ≠ 0)
      simp only [hG, if_pos h1, zero_div, Complex.zero_cpow hcc, norm_zero,
        Real.zero_rpow (by linarith : c ≠ 0)]
      simp
    · by_cases hsb : Real.cos (π / c) * ‖b / a‖ ≤ (b / a).re
      · have heq : Real.cos (π / c) * ‖b / a‖ = (b / a).re := le_antisymm hsb (not_lt.1 hns)
        simp only [hG, if_pos hsb]
        exact s25e_cone_boundary_val hc ha0 hb0 heq
      · simp only [hG, if_neg hsb]
  refine ⟨G, fun x ε hε => s25e_cone_pt hc ha0 (fun w => rfl) x hε, hGa, by rw [hGb]; positivity,
    le_of_eq hGb, ?_⟩
  obtain ⟨γ, hγ, hlen⟩ := s25e_apex_curve m hm ha hb
  exact ⟨γ, hγ, by rw [hGb]; exact le_of_eq hlen⟩

/-- Helper for `s25e_cone_shortest`, `m ≥ 1`, `a ≠ 0`, `b` strictly inside the sector of `a`. -/
theorem s25e_cone_case_sector (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) (ha0 : a ≠ 0)
    (hs : Real.cos (π / ((((m : ℝ) + 2) / 2))) * ‖b / a‖ < (b / a).re) :
    ∃ G : ℂ → ℝ, (∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
        |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖) ∧
      G a = 0 ∧ 0 ≤ G b ∧ G b ≤ ‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2) ∧
      ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
        phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ ≤ ENNReal.ofReal (G b) := by
  set c : ℝ := ((m : ℝ) + 2) / 2 with hcdef
  have hc : 1 < c := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hcdef]; linarith
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hnac : 0 < ‖a‖ ^ c := Real.rpow_pos_of_pos hna c
  set G : ℂ → ℝ := fun w => if Real.cos (π / c) * ‖w / a‖ ≤ (w / a).re then
    ‖a‖ ^ c * ‖(w / a) ^ (c : ℂ) - 1‖ else ‖a‖ ^ c + ‖w‖ ^ c with hG
  have hGa : G a = 0 := by
    have h1 : Real.cos (π / c) * ‖a / a‖ ≤ (a / a).re := by
      rw [div_self ha0]; simp [Real.cos_le_one]
    simp only [hG, if_pos h1, div_self ha0, Complex.one_cpow, sub_self, norm_zero, mul_zero]
  have hGb : G b = ‖a‖ ^ c * ‖(b / a) ^ (c : ℂ) - 1‖ := by
    simp only [hG, if_pos hs.le]
  refine ⟨G, fun x ε hε => s25e_cone_pt hc ha0 (fun w => rfl) x hε, hGa, by rw [hGb]; positivity, ?_, ?_⟩
  · rw [hGb]
    have h1 : ‖(b / a) ^ (c : ℂ) - 1‖ ≤ ‖b / a‖ ^ c + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_cpow_real, norm_one]
    calc ‖a‖ ^ c * ‖(b / a) ^ (c : ℂ) - 1‖ ≤ ‖a‖ ^ c * (‖b / a‖ ^ c + 1) :=
          mul_le_mul_of_nonneg_left h1 hnac.le
      _ = ‖b‖ ^ c + ‖a‖ ^ c := by
          rw [norm_div, Real.div_rpow (norm_nonneg _) hna.le]
          field_simp
      _ = ‖a‖ ^ c + ‖b‖ ^ c := add_comm _ _
  · obtain ⟨γ, hγ, hlen⟩ := s25e_sector_curve m hm ha hb ha0 hs
    exact ⟨γ, hγ, by rw [hGb]; exact le_of_eq hlen⟩

/-- Helper for `s25e_cone_shortest`, `s25e_surface_lower`: the explicit **cone potential** from `a`: a function `G`
with pointwise Lipschitz constant `≤ c ‖x‖^(c-1)`, `G a = 0`, `0 ≤ G b ≤ ‖a‖^c + ‖b‖^c`, whose value at `b` is the
`Q_m`-distance of `a` and `b` in the plane, attained by a curve in the disc. -/
theorem s25e_cone_potential (m : ℕ) {r : ℝ} (hr : 0 < r) {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) :
    ∃ G : ℂ → ℝ, (∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
        |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖) ∧
      G a = 0 ∧ 0 ≤ G b ∧ G b ≤ ‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2) ∧
      (∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
        phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ ≤ ENNReal.ofReal (G b)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · exact s25e_cone_flat m hm0 hr ha hb
  · by_cases ha0 : a = 0
    · exact s25e_cone_case_zero m hm1 ha hb ha0
    · by_cases hs : Real.cos (π / ((((m : ℝ) + 2) / 2))) * ‖b / a‖ < (b / a).re
      · exact s25e_cone_case_sector m hm1 ha hb ha0 hs
      · exact s25e_cone_case_apex m hm1 ha hb ha0 hs

/-- Helper for `exists_local_shortest_nbhd` (`s25e_`), the plane model: in the cone metric of the quadratic
differential `Q_m(w) dw²`, `Q_m(w) = ((m+2)/2)² wᵐ` (`m = 0`: the flat metric `|dw|` at a regular point; `m ≥ 1`: a zero
of order `m`, a cone of total angle `(m+2)π`), any two points of a disc are joined inside the disc by a Lipschitz curve
whose `Q_m`-length is their `Q_m`-distance in the whole plane: the straight segment when the angular gap is `< 2π/(m+2)`,
else the broken segment through the apex (the discs centred at the apex are convex). -/
theorem s25e_cone_shortest (m : ℕ) {r : ℝ} (hr : 0 < r) {a b : ℂ} (ha : a ∈ ball (0 : ℂ) r)
    (hb : b ∈ ball (0 : ℂ) r) :
    ∃ γ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b γ ∧
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ =
        metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) a b := by
  classical
  obtain ⟨G, hG, hGa, hGb0, hGb, γ, hγ, hup⟩ := s25e_cone_potential m hr ha hb
  refine ⟨γ, hγ, le_antisymm ?_ ?_⟩
  · unfold metricDist
    refine le_iInf₂ fun γ' hγ' => ?_
    exact hup.trans (s25e_cone_lower m hG hGa hγ')
  · unfold metricDist phiLength
    exact iInf₂_le γ ⟨hγ.1, hγ.2.1, hγ.2.2.1, subset_univ _⟩

/-- Helper for `exists_local_shortest_nbhd`: the natural coordinate at any point `p` of a Riemann surface carrying a
holomorphic quadratic differential `q ≢ 0`: `q_p(z) = Q_m(ζ z) ζ'(z)²` near `z₀ = φ_p(p)` for an analytic `ζ` with
`ζ(z₀) = 0`, `ζ'(z₀) ≠ 0` (`m = 0` if `q p z₀ ≠ 0`, `eq25_2_natural_parameter`; else `m` the order of the zero,
`eq25_5_natural_parameter_zero`).  The zero is isolated because `q ≢ 0` on the connected surface (identity theorem). -/
theorem s25e_natural_chart [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ (m : ℕ) (ζ : ℂ → ℂ), AnalyticAt ℂ ζ (chartAt ℂ p p) ∧ ζ (chartAt ℂ p p) = 0 ∧
      deriv ζ (chartAt ℂ p p) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 := by
  classical
  set z₀ := chartAt ℂ p p with hz₀def
  have hz₀ : z₀ ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have han : AnalyticAt ℂ (q p) z₀ := (hq'.2 p).analyticAt ((chartAt ℂ p).open_target.mem_nhds hz₀)
  have hfr : ∃ᶠ p' in 𝓝 p, IsRegularPoint q p' := s26u_frequently_regular hq hne p
  have hnz : ∀ᶠ w in 𝓝[≠] z₀, q p w ≠ 0 :=
    s26u_eventually_ne_zero hq p hz₀ (by rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]; exact hfr)
  have hnev : ¬ ∀ᶠ z in 𝓝 z₀, q p z = 0 := by
    intro h
    have h1 : ∀ᶠ z in 𝓝[≠] z₀, q p z = 0 := nhdsWithin_le_nhds h
    obtain ⟨z, hz1, hz2⟩ := (h1.and hnz).exists
    exact hz2 hz1
  by_cases h0 : q p z₀ = 0
  · -- a zero of order `m ≥ 1`
    obtain ⟨m, ψ, hψ, hψ0, hqψ⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnev
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · exfalso
        have := hqψ.self_of_nhds
        rw [hm0] at this
        simp only [pow_zero, one_smul] at this
        exact hψ0 (this.symm.trans h0)
      · exact hm
    obtain ⟨ζ, hζ, hζ0, hζd, hζq⟩ := eq25_5_natural_parameter_zero hm hψ hψ0
      (hqψ.mono fun z hz => by simpa [smul_eq_mul] using hz)
    exact ⟨m, ζ, hζ, hζ0, hζd, hζq⟩
  · -- a regular point: `m = 0`
    obtain ⟨ζ, hζ, hζ0, hζd, hζq⟩ := eq25_2_natural_parameter han h0
    refine ⟨0, ζ, hζ, hζ0, hζd, ?_⟩
    filter_upwards [hζq] with z hz
    simp [← hz]

/-- Helper for `s25e_surface_lower`, `s25e_surface_upper`: a closed disc around `z₀ = φ_p p` on which the natural
coordinate `ζ` is analytic, injective, with `ζ' ≠ 0` and `q_p = Q_m(ζ) ζ'²`. -/
theorem s25e_local_chart [T2Space S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) (m : ℕ)
    (ζ : ℂ → ℂ) (hζ : AnalyticAt ℂ ζ (chartAt ℂ p p)) (hζ0 : ζ (chartAt ℂ p p) = 0)
    (hζd : deriv ζ (chartAt ℂ p p) ≠ 0)
    (hζq : ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) :
    ∃ r₀ > 0, closedBall (chartAt ℂ p p) r₀ ⊆ (chartAt ℂ p).target ∧
      (∀ z ∈ closedBall (chartAt ℂ p p) r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
        q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) ∧
      InjOn ζ (closedBall (chartAt ℂ p p) r₀) := by
  set z₀ := chartAt ℂ p p with hz₀
  have hz₀t : z₀ ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ᶠ x in 𝓝 z₀, g (ζ x) = x :=
    ⟨_, hζ.hasStrictDerivAt.eventually_left_inverse hζd⟩
  have hdne : ∀ᶠ z in 𝓝 z₀, deriv ζ z ≠ 0 :=
    (hζ.deriv.continuousAt).eventually_ne hζd
  have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 ∧ z ∈ (chartAt ℂ p).target ∧ g (ζ z) = z := by
    filter_upwards [hζ.eventually_analyticAt, hdne, hζq, (chartAt ℂ p).open_target.mem_nhds hz₀t, hg]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  have hmem : ∀ z ∈ closedBall z₀ (ε / 2), dist z z₀ < ε := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)
  refine ⟨ε / 2, by positivity, fun z hz => (hball (hmem z hz)).2.2.2.1, fun z hz => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := hball (hmem z hz)
    exact ⟨h1, h2, h3⟩
  · intro x hx y hy hxy
    have hx' := (hball (hmem x hx)).2.2.2.2
    have hy' := (hball (hmem y hy)).2.2.2.2
    rw [← hx', ← hy', hxy]

/-- Helper for `s25e_surface_lower`, `s25e_surface_upper`: the `φ`-density times the speed of a curve through the
natural chart is the `Q_m`-density times the speed of its natural image `ζ ∘ φ_p ∘ γ`: pointwise identity of the
integrands (both sides vanish where the chart expression of `γ` is not differentiable). -/
theorem s25e_pw [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) (m : ℕ) (ζ : ℂ → ℂ)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (han : ∀ z ∈ closedBall (chartAt ℂ p p) r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
        q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hinj : InjOn ζ (closedBall (chartAt ℂ p p) r₀))
    {γ : ℝ → S} {u : ℝ} (hγ : ContinuousAt γ u) (hx : γ u ∈ (chartAt ℂ p).source)
    (hu : chartAt ℂ p (γ u) ∈ ball (chartAt ℂ p p) r₀) :
    phiDensity (q p) (chartAt ℂ p (γ u)) * ‖deriv (fun v => chartAt ℂ p (γ v)) u‖ₑ =
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (ζ (chartAt ℂ p (γ u))) *
        ‖deriv (fun v => ζ (chartAt ℂ p (γ v))) u‖ₑ := by
  classical
  set z₀ := chartAt ℂ p p with hz₀
  set v₀ := chartAt ℂ p (γ u) with hv₀
  obtain ⟨hζa, hζd, hζq⟩ := han v₀ (ball_subset_closedBall hu)
  have hdens : phiDensity (q p) v₀ = phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (ζ v₀) *
      ENNReal.ofReal ‖deriv ζ v₀‖ := by
    have e : ‖q p v₀‖ = ‖(((m : ℂ) + 2) / 2) ^ 2 * ζ v₀ ^ m‖ * ‖deriv ζ v₀‖ ^ 2 := by
      rw [hζq]
      exact (norm_mul _ _).trans (by rw [norm_pow])
    unfold phiDensity
    rw [e, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have hcont : ContinuousAt (fun v => chartAt ℂ p (γ v)) u :=
    ((chartAt ℂ p).continuousAt hx).comp hγ
  by_cases hd : DifferentiableAt ℝ (fun v => chartAt ℂ p (γ v)) u
  · have h1 := hζa.differentiableAt.hasDerivAt.scomp u hd.hasDerivAt
    have h2 : deriv (fun v => ζ (chartAt ℂ p (γ v))) u = deriv (fun v => chartAt ℂ p (γ v)) u * deriv ζ v₀ := by
      rw [show (fun v => ζ (chartAt ℂ p (γ v))) = ζ ∘ fun v => chartAt ℂ p (γ v) from rfl, h1.deriv, smul_eq_mul]
    rw [h2, hdens, enorm_mul, ofReal_norm]
    ring
  · have hd' : ¬ DifferentiableAt ℝ (fun v => ζ (chartAt ℂ p (γ v))) u := by
      intro hc
      apply hd
      have hs := hζa.hasStrictDerivAt
      have hloc := hs.to_localInverse hζd
      have hgd : DifferentiableAt ℂ (hs.localInverse ζ (deriv ζ v₀) v₀ hζd) (ζ v₀) :=
        hloc.hasDerivAt.differentiableAt
      have hev : (fun v => chartAt ℂ p (γ v)) =ᶠ[𝓝 u]
          (hs.localInverse ζ (deriv ζ v₀) v₀ hζd) ∘ fun v => ζ (chartAt ℂ p (γ v)) := by
        have h1 := hs.eventually_left_inverse hζd
        filter_upwards [hcont.eventually h1] with v hv
        exact hv.symm
      have := (hgd.restrictScalars ℝ).comp u hc
      exact this.congr_of_eventuallyEq hev
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
    simp

/-- Helper for `s25e_surface_lower`: a holomorphic function composed with a Lipschitz curve is Lipschitz on a compact
interval as soon as its image stays in the open set of holomorphy. -/
theorem s25e_comp_lipschitz {F : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hF : DifferentiableOn ℂ F E)
    {u : ℝ → ℂ} {K : ℝ≥0} {α β : ℝ} (hu : LipschitzOnWith K u (Icc α β)) (hmap : MapsTo u (Icc α β) E) :
    ∃ K' : ℝ≥0, LipschitzOnWith K' (fun t => F (u t)) (Icc α β) := by
  have hloc : LocallyLipschitzOn E F := by
    intro w hw
    have hana : AnalyticAt ℂ F w := (hF.analyticOnNhd hE) w hw
    have hcd : ContDiffAt ℝ 1 F w := (hana.restrictScalars (𝕜 := ℝ)).contDiffAt
    obtain ⟨K₀, t, ht, hlip⟩ := hcd.exists_lipschitzOnWith
    exact ⟨K₀, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  have hloc2 : LocallyLipschitzOn (Icc α β) (fun t => F (u t)) := by
    intro t ht
    obtain ⟨K₀, N, hN, hlip⟩ := hloc (hmap ht)
    have hcont : ContinuousWithinAt u (Icc α β) t := hu.continuousOn t ht
    have hpre : u ⁻¹' N ∈ 𝓝[Icc α β] t := (hcont.tendsto_nhdsWithin hmap) hN
    refine ⟨K₀ * K, u ⁻¹' N ∩ Icc α β, ?_, ?_⟩
    · exact inter_mem hpre self_mem_nhdsWithin
    · exact hlip.comp (hu.mono inter_subset_right) (fun y hy => hy.1)
  exact hloc2.exists_lipschitzOnWith_of_compact isCompact_Icc

/-- Helper for `s25e_surface_lower`: telescoping lower bound in `ℝ≥0∞` (negative increments count as `0`). -/
theorem s25e_telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
    ENNReal.ofReal (f (Fin.last n) - f 0) ≤ ∑ i : Fin n, ENNReal.ofReal (f i.succ - f i.castSucc)
  | 0, f => by simp
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have ih := s25e_telescope n (fun i => f i.castSucc)
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at ih
    calc ENNReal.ofReal (f (Fin.last (n + 1)) - f 0)
        = ENNReal.ofReal ((f (Fin.last (n + 1)) - f (Fin.last n).castSucc) +
            (f (Fin.last n).castSucc - f 0)) := by congr 1; ring
      _ ≤ ENNReal.ofReal (f (Fin.last (n + 1)) - f (Fin.last n).castSucc) +
            ENNReal.ofReal (f (Fin.last n).castSucc - f 0) := ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [add_comm]
          refine add_le_add ih ?_
          rw [Fin.succ_last]

/-- Helper for `s25e_surface_lower`: `s25e_potential` for the model density `√‖Q_m‖` on a general interval. -/
theorem s25e_potential_model (m : ℕ) {G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖)
    {c : ℝ → ℂ} {K : ℝ≥0} {α β : ℝ} (hαβ : α ≤ β) (hK : LipschitzOnWith K c (Icc α β)) :
    ENNReal.ofReal (G (c β) - G (c α)) ≤
      ∫⁻ t in Ioo α β, ENNReal.ofReal (Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * c t ^ m‖) * ‖deriv c t‖ₑ := by
  have hρ : ∀ x, Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖ =
      (((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) := fun x => s25e_rho_eq m x
  have hρc : Continuous fun x : ℂ => Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖ := by fun_prop
  refine s25e_potential (ρ := fun x : ℂ => Real.sqrt ‖(((m : ℂ) + 2) / 2) ^ 2 * x ^ m‖) (G := G) hρc
    (fun x => Real.sqrt_nonneg _) ?_ (fun x ε hε => by simpa only [hρ] using hG x ε hε) hαβ hK
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [Metric.continuousAt_iff]
  intro e he
  set R : ℝ := (((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨δ, hδ, hb⟩ := hG x 1 one_pos
  refine ⟨min δ (e / (R + 1 + 1)), lt_min hδ (by positivity), fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  have h1 : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have h2 : ‖y - x‖ < e / (R + 1 + 1) := lt_of_lt_of_le hy (min_le_right _ _)
  rw [Real.dist_eq]
  calc |G y - G x| ≤ (R + 1) * ‖y - x‖ := hb y h1
    _ ≤ (R + 1 + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
    _ < e := by
        rw [lt_div_iff₀ (by positivity)] at h2
        nlinarith

/-- Helper for `s25e_surface_lower`: one chart piece of a partition, cut at the time `τs`: the increase of the
potential `G ∘ ζ ∘ φ_p ∘ γ` between `min s τs` and `min t τs` is bounded by the piece integral in the chart `x` (the
path stays in the natural chart disc up to the time `τs`). -/
theorem s25e_piece_lower [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) (m : ℕ)
    (ζ : ℂ → ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (han : ∀ z ∈ closedBall (chartAt ℂ p p) r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
        q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hinj : InjOn ζ (closedBall (chartAt ℂ p p) r₀)) {G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖)
    {a b : S} (γ : Path a b) {τs : ℝ}
    (hsrc : ∀ t ∈ Icc (0 : ℝ) τs, γ.extend t ∈ (chartAt ℂ p).source ∧
      chartAt ℂ p (γ.extend t) ∈ ball (chartAt ℂ p p) r₀)
    (x : S) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hsx : γ.extend '' Icc s t ⊆ (chartAt ℂ x).source)
    (hK : ∃ K : ℝ≥0, LipschitzOnWith K (fun v => chartAt ℂ x (γ.extend v)) (Icc s t)) :
    ENNReal.ofReal (G (ζ (chartAt ℂ p (γ.extend (min t τs)))) - G (ζ (chartAt ℂ p (γ.extend (min s τs))))) ≤
      ∫⁻ u in Ioo s t, phiDensity (q x) (chartAt ℂ x (γ.extend u)) *
        ‖deriv (fun v => chartAt ℂ x (γ.extend v)) u‖ₑ := by
  classical
  by_cases hseq : min s τs = min t τs
  · rw [hseq, sub_self, ENNReal.ofReal_zero]
    exact bot_le
  have hsτ : s < τs := by
    by_contra h
    push Not at h
    exact hseq (by rw [min_eq_right h, min_eq_right (h.trans hst)])
  rw [min_eq_left hsτ.le]
  set t₂ := min t τs with ht₂
  have hst₂ : s ≤ t₂ := le_min hst hsτ.le
  have ht₂t : t₂ ≤ t := min_le_left _ _
  have ht₂τ : t₂ ≤ τs := min_le_right _ _
  have hI : ∀ v ∈ Icc s t₂, v ∈ Icc (0 : ℝ) τs := fun v hv => ⟨hs.trans hv.1, hv.2.trans ht₂τ⟩
  have hIt : ∀ v ∈ Icc s t₂, v ∈ Icc s t := fun v hv => ⟨hv.1, hv.2.trans ht₂t⟩
  obtain ⟨K, hKx⟩ := hK
  have hE : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source
  have hFd : DifferentiableOn ℂ (chartTransition p x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source) := fun w hw =>
    (s23_transition_differentiableAt p x hw.1 hw.2).differentiableWithinAt
  have hsxv : ∀ v ∈ Icc s t₂, γ.extend v ∈ (chartAt ℂ x).source := fun v hv => hsx ⟨v, hIt v hv, rfl⟩
  have hmapx : MapsTo (fun v => chartAt ℂ x (γ.extend v)) (Icc s t₂)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source) := fun v hv =>
    ⟨(chartAt ℂ x).map_source (hsxv v hv), by
      rw [mem_preimage, (chartAt ℂ x).left_inv (hsxv v hv)]
      exact (hsrc v (hI v hv)).1⟩
  obtain ⟨K₁, hK₁⟩ := s25e_comp_lipschitz hE hFd (hKx.mono (Icc_subset_Icc le_rfl ht₂t)) hmapx
  have hteq : ∀ v ∈ Icc s t₂, chartTransition p x (chartAt ℂ x (γ.extend v)) = chartAt ℂ p (γ.extend v) :=
    fun v hv => by
      show chartAt ℂ p ((chartAt ℂ x).symm (chartAt ℂ x (γ.extend v))) = _
      rw [(chartAt ℂ x).left_inv (hsxv v hv)]
  have hKp : LipschitzOnWith K₁ (fun v => chartAt ℂ p (γ.extend v)) (Icc s t₂) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [← hteq y hy, ← hteq z hz]
    exact hK₁.dist_le_mul y hy z hz
  have hζd : DifferentiableOn ℂ ζ (ball (chartAt ℂ p p) r₀) := fun w hw =>
    (han w (ball_subset_closedBall hw)).1.differentiableAt.differentiableWithinAt
  obtain ⟨K₂, hK₂⟩ := s25e_comp_lipschitz isOpen_ball hζd hKp (fun v hv => (hsrc v (hI v hv)).2)
  have hpot := s25e_potential_model m hG hst₂ hK₂
  refine hpot.trans ?_
  calc _ = ∫⁻ u in Ioo s t₂, phiDensity (q p) (chartAt ℂ p (γ.extend u)) *
          ‖deriv (fun v => chartAt ℂ p (γ.extend v)) u‖ₑ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        have huI := hI u (Ioo_subset_Icc_self hu)
        exact (s25e_pw hq p m ζ hr₀ han hinj (γ := γ.extend) γ.continuous_extend.continuousAt
          (hsrc u huI).1 (hsrc u huI).2).symm
    _ = ∫⁻ u in Ioo s t₂, phiDensity (q x) (chartAt ℂ x (γ.extend u)) *
          ‖deriv (fun v => chartAt ℂ x (γ.extend v)) u‖ₑ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        have huI := hI u (Ioo_subset_Icc_self hu)
        exact s26n_density_speed_chart hq p x γ.continuous_extend.continuousAt (hsrc u huI).1
          (hsxv u (Ioo_subset_Icc_self hu))
    _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo le_rfl ht₂t)

/-- Helper for `s25e_surface_lower`: if a path stays in the natural chart disc up to time `τs`, its `φ`-length is at
least the increase of a potential `G` of the model density along `ζ ∘ φ_p ∘ γ` up to `τs`: sum the pieces of any
partition with `s25e_telescope`. -/
theorem s25e_partition_lower [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) (m : ℕ)
    (ζ : ℂ → ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (han : ∀ z ∈ closedBall (chartAt ℂ p p) r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
        q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (hinj : InjOn ζ (closedBall (chartAt ℂ p p) r₀)) {G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖)
    {a b : S} (γ : Path a b) {τs : ℝ} (hτs : τs ∈ Icc (0 : ℝ) 1)
    (hsrc : ∀ t ∈ Icc (0 : ℝ) τs, γ.extend t ∈ (chartAt ℂ p).source ∧
      chartAt ℂ p (γ.extend t) ∈ ball (chartAt ℂ p p) r₀) :
    ENNReal.ofReal (G (ζ (chartAt ℂ p (γ.extend τs))) - G (ζ (chartAt ℂ p (γ.extend 0)))) ≤
      phiLengthPath q γ := by
  classical
  unfold phiLengthPath phiLengthOn
  refine le_iInf fun n => le_iInf fun τ => le_iInf fun x => le_iInf fun h => ?_
  obtain ⟨h0, hn, hmono, hpc⟩ := h
  have htel := s25e_telescope n (fun i => G (ζ (chartAt ℂ p (γ.extend (min (τ i) τs)))))
  have hlast : G (ζ (chartAt ℂ p (γ.extend (min (τ (Fin.last n)) τs)))) =
      G (ζ (chartAt ℂ p (γ.extend τs))) := by
    rw [hn, min_eq_right hτs.2]
  have hfirst : G (ζ (chartAt ℂ p (γ.extend (min (τ 0) τs)))) =
      G (ζ (chartAt ℂ p (γ.extend 0))) := by
    rw [h0, min_eq_left hτs.1]
  rw [hlast, hfirst] at htel
  refine htel.trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨hsx, hK⟩ := hpc i
  have hs0 : 0 ≤ τ i.castSucc := h0 ▸ hmono (Fin.zero_le _)
  exact s25e_piece_lower hq p m ζ hr₀ han hinj hG γ hsrc (x i) hs0 (hmono (Fin.castSucc_lt_succ (i := i)).le)
    hsx hK

/-- Helper for `s25e_surface_lower`: the radial potential `‖w‖^c`, `c = (m+2)/2`, has pointwise Lipschitz constant
`c ‖x‖^(c-1)` (also in the flat case `m = 0`, `c = 1`). -/
theorem s25e_radial_hG (m : ℕ) : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
    |‖y‖ ^ (((m : ℝ) + 2) / 2) - ‖x‖ ^ (((m : ℝ) + 2) / 2)| ≤
      ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖ := by
  intro x ε hε
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, one_pos, fun y _ => ?_⟩
    have hc : (((0 : ℕ) : ℝ) + 2) / 2 = 1 := by norm_num
    rw [hc]
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul]
    have := abs_norm_sub_norm_le y x
    nlinarith [norm_nonneg (y - x)]
  · have hc : 1 < (((m : ℝ) + 2) / 2) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    exact s25e_radial_pt hc x hε

/-- Helper for `s25e_surface_lower`: three points of norm `< ρ/3` have `‖·‖^c`-sums below `ρ^c`, `c = (m+2)/2 ≥ 1`. -/
theorem s25e_pow_third (m : ℕ) {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hu3 : u < ρ / 3)
    (hv3 : v < ρ / 3) :
    2 * u ^ (((m : ℝ) + 2) / 2) + v ^ (((m : ℝ) + 2) / 2) ≤ ρ ^ (((m : ℝ) + 2) / 2) := by
  have hc1 : (1 : ℝ) ≤ ((m : ℝ) + 2) / 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : (3 : ℝ) ≤ 3 ^ (((m : ℝ) + 2) / 2) := by
    calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ 3 ^ (((m : ℝ) + 2) / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
  have hbd : ∀ t : ℝ, 0 ≤ t → t < ρ / 3 → t ^ (((m : ℝ) + 2) / 2) ≤ ρ ^ (((m : ℝ) + 2) / 2) / 3 := by
    intro t ht ht3
    calc t ^ (((m : ℝ) + 2) / 2) ≤ (ρ / 3) ^ (((m : ℝ) + 2) / 2) :=
          Real.rpow_le_rpow ht ht3.le (by positivity)
      _ = ρ ^ (((m : ℝ) + 2) / 2) / 3 ^ (((m : ℝ) + 2) / 2) := Real.div_rpow hρ.le (by norm_num) _
      _ ≤ ρ ^ (((m : ℝ) + 2) / 2) / 3 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) h3
  have := hbd u hu hu3
  have := hbd v hv hv3
  linarith

/-- Helper for `s25e_surface_upper`: a single chart piece bounds the `φ`-length from above. -/
theorem s25e_len_le_piece {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) (x : S) {s t : ℝ} (hst : s ≤ t)
    (hsrc : γ.extend '' Icc s t ⊆ (chartAt ℂ x).source)
    (hK : ∃ K : ℝ≥0, LipschitzOnWith K (fun v => chartAt ℂ x (γ.extend v)) (Icc s t)) :
    phiLengthOn q γ s t ≤ ∫⁻ u in Ioo s t, phiDensity (q x) (chartAt ℂ x (γ.extend u)) *
      ‖deriv (fun v => chartAt ℂ x (γ.extend v)) u‖ₑ := by
  unfold phiLengthOn
  refine iInf_le_of_le 1 (iInf_le_of_le ![s, t] (iInf_le_of_le (fun _ => x) (iInf_le_of_le ?_ ?_)))
  · refine ⟨rfl, rfl, ?_, fun i => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact ⟨by simpa using hsrc, by simpa using hK⟩
  · simp

/-- Helper for `exists_local_shortest_nbhd` (lower bound): in a small neighbourhood `W` of `p`, every path of `S`
between two points has `φ`-length at least the `Q_m`-distance of their natural coordinates
`ζ (φ_p a)`, `ζ (φ_p b)`.  (Pieces of the path in the natural chart have the chart-independent integrand
`s26n_density_speed_chart`, summed with `s26n_lintegral_le_sum`; a path leaving the chart disc pays at least the radial
gap, which exceeds the distance of two points of `W`; inside the disc the model lower bound is `psa_lower`-style, with
the cone lower bound of `s25e_cone_shortest`'s distance.) -/
theorem s25e_surface_lower [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) (m : ℕ) (ζ : ℂ → ℂ)
    (hζ : AnalyticAt ℂ ζ (chartAt ℂ p p)) (hζ0 : ζ (chartAt ℂ p p) = 0)
    (hζd : deriv ζ (chartAt ℂ p p) ≠ 0)
    (hζq : ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) :
    ∃ W ∈ 𝓝 p, ∀ a ∈ W, ∀ b ∈ W, ∀ γ' : Path a b,
      metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
          (ζ (chartAt ℂ p a)) (ζ (chartAt ℂ p b)) ≤ phiLengthPath q γ' := by
  classical
  obtain ⟨r₀, hr₀, hsub, han, hinj⟩ := s25e_local_chart hq p m ζ hζ hζ0 hζd hζq
  set z₀ := chartAt ℂ p p with hz₀
  have han' : ∀ z ∈ closedBall z₀ r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 := fun z hz =>
    ⟨(han z hz).1, (han z hz).2.1⟩
  obtain ⟨hopen, hψ⟩ := psa_inverse hr₀ hinj han'
  set ψ' : ℂ → ℂ := Function.invFunOn ζ (ball z₀ r₀) with hψ'def
  set Ω : Set ℂ := ζ '' ball z₀ r₀ with hΩ
  have hball_sub : ball z₀ r₀ ⊆ closedBall z₀ r₀ := ball_subset_closedBall
  have h0Ω : (0 : ℂ) ∈ Ω := ⟨z₀, mem_ball_self hr₀, hζ0⟩
  have hψl : ∀ z ∈ ball z₀ r₀, ψ' (ζ z) = z := fun z hz =>
    hinj (hball_sub (hψ (ζ z) ⟨z, hz, rfl⟩).1) (hball_sub hz) (hψ (ζ z) ⟨z, hz, rfl⟩).2.1
  obtain ⟨ρ₁, hρ₁, hρ₁Ω⟩ := Metric.isOpen_iff.1 hopen 0 h0Ω
  set ρc : ℝ := ρ₁ / 2 with hρc
  have hρc0 : 0 < ρc := by positivity
  have hKsub : closedBall (0 : ℂ) ρc ⊆ Ω := fun w hw =>
    hρ₁Ω (by rw [mem_ball_zero_iff]; have := mem_closedBall_zero_iff.1 hw; linarith)
  have hψcont : ContinuousOn ψ' Ω := fun w hw => (hψ w hw).2.2.continuousAt.continuousWithinAt
  set χ : ℂ → S := fun w => (chartAt ℂ p).symm (ψ' w) with hχ
  have hχcont : ContinuousOn χ Ω :=
    (chartAt ℂ p).continuousOn_symm.comp hψcont (fun w hw => hsub (hball_sub (hψ w hw).1))
  have hφχ : ∀ w ∈ Ω, chartAt ℂ p (χ w) = ψ' w := fun w hw =>
    (chartAt ℂ p).right_inv (hsub (hball_sub (hψ w hw).1))
  have hχsrc : ∀ w ∈ Ω, χ w ∈ (chartAt ℂ p).source := fun w hw =>
    (chartAt ℂ p).map_target (hsub (hball_sub (hψ w hw).1))
  have hUo : ∀ ρ : ℝ,
      IsOpen ((chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) ρ)) := by
    intro ρ
    refine (chartAt ℂ p).continuousOn.isOpen_inter_preimage (chartAt ℂ p).open_source ?_
    have hζc : ContinuousOn ζ (ball z₀ r₀) := fun z hz =>
      (han z (hball_sub hz)).1.continuousAt.continuousWithinAt
    exact hζc.isOpen_inter_preimage isOpen_ball isOpen_ball
  set Uc : Set S := (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) ρc) with hUc
  have hUco : IsOpen Uc := hUo ρc
  set W : Set S :=
    (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) (ρc / 3)) with hW
  have hpW : p ∈ W := ⟨mem_chart_source ℂ p, mem_ball_self hr₀, by
    rw [mem_preimage, hζ0]; exact mem_ball_self (by positivity)⟩
  refine ⟨W, (hUo _).mem_nhds hpW, fun a ha b hb γ' => ?_⟩
  set A : ℂ := ζ (chartAt ℂ p a) with hA
  set B : ℂ := ζ (chartAt ℂ p b) with hB
  have hAn : ‖A‖ < ρc / 3 := mem_ball_zero_iff.1 ha.2.2
  have hBn : ‖B‖ < ρc / 3 := mem_ball_zero_iff.1 hb.2.2
  have hρ3 : ρc / 3 < ρc := by linarith
  have hAb : A ∈ ball (0 : ℂ) ρc := mem_ball_zero_iff.2 (hAn.trans hρ3)
  have hBb : B ∈ ball (0 : ℂ) ρc := mem_ball_zero_iff.2 (hBn.trans hρ3)
  obtain ⟨G, hG, hGA, hGB0, hGB, c, hcpath, hclen⟩ := s25e_cone_potential m hρc0 hAb hBb
  have hmd : metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) A B ≤
      ENNReal.ofReal (G B) := by
    have hc' : IsPathIn univ A B c := ⟨hcpath.1, hcpath.2.1, hcpath.2.2.1, subset_univ _⟩
    exact (iInf₂_le (f := fun σ (_ : σ ∈ {γ : LRCurve | IsPathIn univ A B γ}) =>
        σ.rhoLength (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))) c hc').trans hclen
  have ha0 : γ'.extend 0 = a := Path.extend_zero γ'
  have hb1 : γ'.extend 1 = b := Path.extend_one γ'
  have hKc : IsCompact (χ '' closedBall (0 : ℂ) ρc) :=
    (isCompact_closedBall _ _).image_of_continuousOn (hχcont.mono hKsub)
  have hUcK : ∀ x ∈ Uc, x ∈ χ '' closedBall (0 : ℂ) ρc := fun x hx =>
    ⟨ζ (chartAt ℂ p x), mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 hx.2.2).le, by
      simp only [hχ]
      rw [hψl _ hx.2.1]
      exact (chartAt ℂ p).left_inv hx.1⟩
  by_cases hE : ∃ t ∈ Icc (0 : ℝ) 1, γ'.extend t ∉ Uc
  · obtain ⟨t₀, ht₀, ht₀U⟩ := hE
    set Es : Set ℝ := Icc 0 1 ∩ γ'.extend ⁻¹' Ucᶜ with hEs
    have hEsc : IsClosed Es :=
      isClosed_Icc.inter (hUco.isClosed_compl.preimage γ'.continuous_extend)
    have hEsne : Es.Nonempty := ⟨t₀, ht₀, ht₀U⟩
    have hEsb : BddBelow Es := ⟨0, fun t ht => ht.1.1⟩
    set τs : ℝ := sInf Es with hτs
    have hτE : τs ∈ Es := hEsc.csInf_mem hEsne hEsb
    have hτI : τs ∈ Icc (0 : ℝ) 1 := hτE.1
    have hbefore : ∀ t ∈ Ico (0 : ℝ) τs, γ'.extend t ∈ Uc := fun t ht => by
      by_contra hcon
      have hmem : t ∈ Es := ⟨⟨ht.1, ht.2.le.trans hτI.2⟩, hcon⟩
      exact absurd (csInf_le hEsb hmem) (not_le.2 ht.2)
    have haU : a ∈ Uc := ⟨ha.1, ha.2.1, mem_ball_zero_iff.2 (hAn.trans hρ3)⟩
    have hτpos : 0 < τs := by
      rcases hτI.1.eq_or_lt with h | h
      · exfalso
        apply hτE.2
        rw [← h, ha0]
        exact haU
      · exact h
    have hlim : γ'.extend τs ∈ χ '' closedBall (0 : ℂ) ρc := by
      refine hKc.isClosed.mem_of_tendsto (f := γ'.extend) (b := 𝓝[<] τs) ?_ ?_
      · exact (γ'.continuous_extend.continuousAt (x := τs)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT hτpos] with t ht using hUcK _ (hbefore t ⟨ht.1.le, ht.2⟩)
    obtain ⟨w, hwK, hw⟩ := hlim
    have hwΩ : w ∈ Ω := hKsub hwK
    have hγτ_src : γ'.extend τs ∈ (chartAt ℂ p).source := by
      rw [← hw]; exact hχsrc w hwΩ
    have hγτ_φ : chartAt ℂ p (γ'.extend τs) = ψ' w := by
      rw [← hw]; exact hφχ w hwΩ
    have hγτ_ball : chartAt ℂ p (γ'.extend τs) ∈ ball z₀ r₀ := by
      rw [hγτ_φ]; exact (hψ w hwΩ).1
    have hζγτ : ζ (chartAt ℂ p (γ'.extend τs)) = w := by
      rw [hγτ_φ]; exact (hψ w hwΩ).2.1
    have hwnorm : ‖w‖ = ρc := by
      refine le_antisymm (mem_closedBall_zero_iff.1 hwK) ?_
      by_contra hlt
      push Not at hlt
      apply hτE.2
      exact ⟨hγτ_src, hγτ_ball, by rw [mem_preimage, hζγτ]; exact mem_ball_zero_iff.2 hlt⟩
    have hsrc : ∀ t ∈ Icc (0 : ℝ) τs, γ'.extend t ∈ (chartAt ℂ p).source ∧
        chartAt ℂ p (γ'.extend t) ∈ ball z₀ r₀ := by
      intro t ht
      rcases ht.2.eq_or_lt with h | h
      · rw [h]; exact ⟨hγτ_src, hγτ_ball⟩
      · have := hbefore t ⟨ht.1, h⟩
        exact ⟨this.1, this.2.1⟩
    have hPL : ENNReal.ofReal (‖w‖ ^ (((m : ℝ) + 2) / 2) - ‖A‖ ^ (((m : ℝ) + 2) / 2)) ≤
        phiLengthPath q γ' := by
      have := s25e_partition_lower hq p m ζ hr₀ han hinj
        (G := fun w : ℂ => ‖w‖ ^ (((m : ℝ) + 2) / 2)) (s25e_radial_hG m) γ' hτI hsrc
      rw [hζγτ, ha0] at this
      exact this
    calc _ ≤ ENNReal.ofReal (G B) := hmd
      _ ≤ ENNReal.ofReal (‖w‖ ^ (((m : ℝ) + 2) / 2) - ‖A‖ ^ (((m : ℝ) + 2) / 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hwnorm]
          have := s25e_pow_third m hρc0 (norm_nonneg A) (norm_nonneg B) hAn hBn
          linarith
      _ ≤ _ := hPL
  · push Not at hE
    have hsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ'.extend t ∈ (chartAt ℂ p).source ∧
        chartAt ℂ p (γ'.extend t) ∈ ball z₀ r₀ := fun t ht => ⟨(hE t ht).1, (hE t ht).2.1⟩
    have hPL := s25e_partition_lower hq p m ζ hr₀ han hinj hG γ' (τs := 1) ⟨zero_le_one, le_rfl⟩ hsrc
    rw [hb1, ha0] at hPL
    calc _ ≤ ENNReal.ofReal (G B) := hmd
      _ = ENNReal.ofReal (G B - G A) := by rw [hGA, sub_zero]
      _ ≤ _ := hPL

/-- Helper for `exists_local_shortest_nbhd` (upper bound): inside every neighbourhood `W` of `p` there is a
neighbourhood `V` such that two points of `V` are joined by a path of `S` inside `V` of `φ`-length at most the
`Q_m`-distance of their natural coordinates: the model minimizer of `s25e_cone_shortest` in a disc of the natural
coordinate, pulled back by the inverse of `ζ ∘ φ_p` (Lipschitz chart expression, partition `n = 1`). -/
theorem s25e_surface_upper [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) (m : ℕ) (ζ : ℂ → ℂ)
    (hζ : AnalyticAt ℂ ζ (chartAt ℂ p p)) (hζ0 : ζ (chartAt ℂ p p) = 0)
    (hζd : deriv ζ (chartAt ℂ p p) ≠ 0)
    (hζq : ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (W : Set S) (hW : W ∈ 𝓝 p) :
    ∃ V ∈ 𝓝 p, V ⊆ W ∧ ∀ a ∈ V, ∀ b ∈ V, ∃ γ : Path a b, (∀ t, γ t ∈ V) ∧
      phiLengthPath q γ ≤ metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m))
          (ζ (chartAt ℂ p a)) (ζ (chartAt ℂ p b)) := by
  classical
  obtain ⟨r₀, hr₀, hsub, han, hinj⟩ := s25e_local_chart hq p m ζ hζ hζ0 hζd hζq
  set z₀ := chartAt ℂ p p with hz₀
  have han' : ∀ z ∈ closedBall z₀ r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 := fun z hz =>
    ⟨(han z hz).1, (han z hz).2.1⟩
  obtain ⟨hopen, hψ⟩ := psa_inverse hr₀ hinj han'
  set ψ' : ℂ → ℂ := Function.invFunOn ζ (ball z₀ r₀) with hψ'def
  set Ω : Set ℂ := ζ '' ball z₀ r₀ with hΩ
  have hball_sub : ball z₀ r₀ ⊆ closedBall z₀ r₀ := ball_subset_closedBall
  have h0Ω : (0 : ℂ) ∈ Ω := ⟨z₀, mem_ball_self hr₀, hζ0⟩
  have hψl : ∀ z ∈ ball z₀ r₀, ψ' (ζ z) = z := fun z hz =>
    hinj (hball_sub (hψ (ζ z) ⟨z, hz, rfl⟩).1) (hball_sub hz) (hψ (ζ z) ⟨z, hz, rfl⟩).2.1
  have hψ0 : ψ' 0 = z₀ := by
    have := hψl z₀ (mem_ball_self hr₀)
    rwa [hζ0] at this
  obtain ⟨ρ₁, hρ₁, hρ₁Ω⟩ := Metric.isOpen_iff.1 hopen 0 h0Ω
  -- `ψ'` is Lipschitz on `closedBall 0 (ρ₁/2)`
  have hKsub : closedBall (0 : ℂ) (ρ₁ / 2) ⊆ Ω := fun w hw =>
    hρ₁Ω (by rw [mem_ball_zero_iff]; have := mem_closedBall_zero_iff.1 hw; linarith)
  have hψcont : ContinuousOn ψ' Ω := fun w hw => (hψ w hw).2.2.continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun w => ‖(deriv ζ (ψ' w))⁻¹‖) (closedBall (0 : ℂ) (ρ₁ / 2)) := by
    intro w hw
    have hwΩ := hKsub hw
    have hwb := (hψ w hwΩ).1
    have h1 : ContinuousAt (fun w => deriv ζ (ψ' w)) w :=
      ((han _ (hball_sub hwb)).1.deriv.continuousAt).comp (hψcont.continuousAt (hopen.mem_nhds hwΩ))
    exact ((h1.inv₀ (han _ (hball_sub hwb)).2.1).norm).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (ρ₁ / 2)).exists_bound_of_continuousOn hdc
  have hψLip : LipschitzOnWith (Real.toNNReal M) ψ' (closedBall (0 : ℂ) (ρ₁ / 2)) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun w hw => (hψ w (hKsub hw)).2.2.differentiableAt) ?_
      (convex_closedBall _ _)
    intro w hw
    rw [(hψ w (hKsub hw)).2.2.deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_max_of_le_left (by simpa using hM w hw)
  -- `χ w = φ_p⁻¹ (ψ' w)` and the radius `ρ'`
  set χ : ℂ → S := fun w => (chartAt ℂ p).symm (ψ' w) with hχ
  have hχ0 : χ 0 = p := by
    simp only [hχ, hψ0]
    exact (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hχc : ContinuousAt χ 0 := by
    have h1 : ContinuousAt ψ' 0 := hψcont.continuousAt (hopen.mem_nhds h0Ω)
    have h2 : ContinuousAt (chartAt ℂ p).symm z₀ :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    exact (hψ0 ▸ h2).comp h1
  obtain ⟨ρ₂, hρ₂, hρ₂W⟩ := Metric.mem_nhds_iff.1 (hχc.preimage_mem_nhds (by rw [hχ0]; exact hW))
  set ρ' : ℝ := min (ρ₁ / 2) ρ₂ with hρ'
  have hρ'0 : 0 < ρ' := lt_min (by positivity) hρ₂
  set V : Set S := (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) ρ') with hV
  have hVo : IsOpen V := by
    refine (chartAt ℂ p).continuousOn.isOpen_inter_preimage (chartAt ℂ p).open_source ?_
    have hζc : ContinuousOn ζ (ball z₀ r₀) := fun z hz => (han z (hball_sub hz)).1.continuousAt.continuousWithinAt
    exact hζc.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hpV : p ∈ V := ⟨mem_chart_source ℂ p, mem_ball_self hr₀, by rw [mem_preimage, hζ0]; exact mem_ball_self hρ'0⟩
  have hVχ : ∀ x ∈ V, χ (ζ (chartAt ℂ p x)) = x := fun x hx => by
    simp only [hχ]
    rw [hψl _ hx.2.1]
    exact (chartAt ℂ p).left_inv hx.1
  refine ⟨V, hVo.mem_nhds hpV, fun x hx => ?_, fun a ha b hb => ?_⟩
  · rw [← hVχ x hx]
    exact hρ₂W (by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hx.2.2) (min_le_right _ _))
  · obtain ⟨c, hcpath, hclen⟩ := s25e_cone_shortest m hρ'0 (a := ζ (chartAt ℂ p a))
      (b := ζ (chartAt ℂ p b)) ha.2.2 hb.2.2
    obtain ⟨⟨K, hK⟩, hc0, hc1, hctr⟩ := hcpath
    have hcI : ∀ t ∈ Icc (0 : ℝ) 1, c.toFun t ∈ ball (0 : ℂ) ρ' := fun t ht => hctr ⟨t, ht, rfl⟩
    have hρ'le : ρ' ≤ ρ₁ / 2 := min_le_left _ _
    have hcK : ∀ t ∈ Icc (0 : ℝ) 1, c.toFun t ∈ closedBall (0 : ℂ) (ρ₁ / 2) := fun t ht => by
      rw [mem_closedBall_zero_iff]
      have := mem_ball_zero_iff.1 (hcI t ht)
      linarith
    have hcΩ : ∀ t ∈ Icc (0 : ℝ) 1, c.toFun t ∈ Ω := fun t ht => hKsub (hcK t ht)
    have hχcont : ContinuousOn χ Ω :=
      (chartAt ℂ p).continuousOn_symm.comp hψcont (fun w hw => hsub (hball_sub (hψ w hw).1))
    have hcont : Continuous (fun t : unitInterval => χ (c.toFun t)) := by
      have : ContinuousOn (fun t : ℝ => χ (c.toFun t)) (Icc 0 1) :=
        hχcont.comp hK.continuousOn hcΩ
      exact this.comp_continuous continuous_subtype_val (fun t => t.2)
    have hs : (fun t : unitInterval => χ (c.toFun t)) 0 = a := by
      show χ (c.toFun ((0 : unitInterval) : ℝ)) = a
      simp only [Set.Icc.coe_zero]
      rw [hc0]
      exact hVχ a ha
    have ht : (fun t : unitInterval => χ (c.toFun t)) 1 = b := by
      show χ (c.toFun ((1 : unitInterval) : ℝ)) = b
      simp only [Set.Icc.coe_one]
      rw [hc1]
      exact hVχ b hb
    let γ : Path a b := ⟨⟨fun t : unitInterval => χ (c.toFun t), hcont⟩, hs, ht⟩
    have hγext : ∀ v ∈ Icc (0 : ℝ) 1, γ.extend v = χ (c.toFun v) := fun v hv => by
      rw [Path.extend_apply γ hv]
      rfl
    have hφχ : ∀ w ∈ Ω, chartAt ℂ p (χ w) = ψ' w := fun w hw =>
      (chartAt ℂ p).right_inv (hsub (hball_sub (hψ w hw).1))
    have hχsrc : ∀ w ∈ Ω, χ w ∈ (chartAt ℂ p).source := fun w hw =>
      (chartAt ℂ p).map_target (hsub (hball_sub (hψ w hw).1))
    refine ⟨γ, fun t => ?_, ?_⟩
    · show χ (c.toFun t) ∈ V
      have hw := hcΩ t t.2
      refine ⟨hχsrc _ hw, ?_, ?_⟩
      · rw [hφχ _ hw]; exact (hψ _ hw).1
      · show ζ (chartAt ℂ p (χ (c.toFun t))) ∈ ball (0 : ℂ) ρ'
        rw [hφχ _ hw, (hψ _ hw).2.1]; exact hcI t t.2
    · have hlen1 := s25e_len_le_piece (q := q) γ p (zero_le_one) (by
          rintro _ ⟨v, hv, rfl⟩
          rw [hγext v hv]
          exact hχsrc _ (hcΩ v hv)) (by
          have hmaps : MapsTo c.toFun (Icc (0 : ℝ) 1) (closedBall (0 : ℂ) (ρ₁ / 2)) := hcK
          refine ⟨_, LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal M * K) fun x hx y hy => ?_⟩
          rw [hγext x hx, hγext y hy, hφχ _ (hcΩ x hx), hφχ _ (hcΩ y hy)]
          exact (hψLip.comp hK hmaps).dist_le_mul x hx y hy)
      refine le_trans hlen1 (le_trans (le_of_eq ?_) (le_of_eq hclen))
      unfold phiLength LRCurve.rhoLength
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have huI : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
      have hw := hcΩ u huI
      have hext : ∀ v ∈ Icc (0 : ℝ) 1, ζ (chartAt ℂ p (γ.extend v)) = c.toFun v := fun v hv => by
        rw [hγext v hv, hφχ _ (hcΩ v hv), (hψ _ (hcΩ v hv)).2.1]
      have hpw := s25e_pw hq p m ζ hr₀ han hinj (γ := γ.extend) γ.continuous_extend.continuousAt
        (by rw [hγext u huI]; exact hχsrc _ hw) (by
          rw [hγext u huI, hφχ _ hw]; exact (hψ _ hw).1)
      refine hpw.trans ?_
      have hev : (fun v => ζ (chartAt ℂ p (γ.extend v))) =ᶠ[𝓝 u] c.toFun := by
        filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv using hext v ⟨hv.1, hv.2⟩
      rw [hev.deriv_eq, hext u huI]

/-- §25.2: every point `p` of a Riemann surface has a neighbourhood `V_p` in which any two points are
joined by a shortest curve of the `φ`-metric (a `φ`-straight segment in a natural parameter, or a
broken `φ`-straight arc through a zero). -/
theorem exists_local_shortest_nbhd [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ V ∈ 𝓝 p, ∀ a ∈ V, ∀ b ∈ V, ∃ γ : Path a b, (∀ t, γ t ∈ V) ∧
      phiLengthPath q γ = phiDistRS q a b := by
  obtain ⟨m, ζ, hζ, hζ0, hζd, hζq⟩ := s25e_natural_chart hq hne p
  obtain ⟨W, hW, hlow⟩ := s25e_surface_lower hq hne p m ζ hζ hζ0 hζd hζq
  obtain ⟨V, hV, hVW, hup⟩ := s25e_surface_upper hq hne p m ζ hζ hζ0 hζd hζq W hW
  refine ⟨V, hV, fun a ha b hb => ?_⟩
  obtain ⟨γ, hγV, hγl⟩ := hup a ha b hb
  refine ⟨γ, hγV, le_antisymm ?_ (iInf_le _ γ)⟩
  exact le_iInf fun γ' => hγl.trans (hlow a (hVW ha) b (hVW hb) γ')

/-- Helper for `s25i_transport`: affine change of variable in the `ρ`-length integrand of a curve `c₁` that equals
`c₂ ∘ (l · + m)` near every point of `(a, b)`. -/
theorem s25i_cov_lintegral (D : ℂ → ℝ≥0∞) {c₁ c₂ : ℝ → ℂ} {l m a b : ℝ} (hl : 0 < l)
    (hc : ∀ u ∈ Ioo a b, c₁ =ᶠ[𝓝 u] fun w => c₂ (l * w + m)) :
    ∫⁻ u in Ioo a b, D (c₁ u) * ‖deriv c₁ u‖ₑ =
      ∫⁻ v in Ioo (l * a + m) (l * b + m), D (c₂ v) * ‖deriv c₂ v‖ₑ := by
  have himg : (fun u : ℝ => l * u + m) '' Ioo a b = Ioo (l * a + m) (l * b + m) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    · intro hv
      refine ⟨(v - m) / l, ⟨?_, ?_⟩, by field_simp; ring⟩
      · rw [lt_div_iff₀ hl]; linarith [hv.1]
      · rw [div_lt_iff₀ hl]; linarith [hv.2]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f := fun u : ℝ => l * u + m) (f' := fun _ => l) (fun u _ => by
      simpa using ((hasDerivAt_id u).const_mul l |>.add_const m).hasDerivWithinAt)
    (fun u _ v _ h => by simpa [hl.ne'] using h)]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have h1 : c₁ u = c₂ (l * u + m) := (hc u hu).self_of_nhds
  have h2 : deriv c₁ u = l • deriv c₂ (l * u + m) := by
    rw [(hc u hu).deriv_eq]
    have := deriv_comp_mul_left (c := l) (x := u) (fun w => c₂ (w + m))
    simp only [deriv_comp_add_const] at this
    exact this
  rw [h1, h2, enorm_smul, Real.enorm_eq_ofReal hl.le, abs_of_pos hl]
  ring

/-- Helper for `shortest_isPhiGeodesicRS` (`s25i_`): an affine reparametrization does not increase the `φ`-length of a
sub-arc.  If `β = α ∘ (u ↦ l u + m)` on `[x, y]` with `l > 0`, then `l_φ(β|[x, y]) ≤ l_φ(α|[l x + m, l y + m])`: a
partition of the image interval pulls back (Lipschitz chart pieces stay Lipschitz) and the integrand
`φ-density · |chart derivative|` is invariant under the affine change of variable.  With `l = 1`, `m = 0` this is
the locality of `phiLengthOn` (it only depends on the path on `[x, y]`). -/
theorem s25i_transport {q : S → ℂ → ℂ} {a b c d : S} (α : Path a b) (β : Path c d) {l m x y : ℝ} (hl : 0 < l)
    (hxy : x ≤ y) (hβ : ∀ u ∈ Icc x y, β.extend u = α.extend (l * u + m)) :
    phiLengthOn q β x y ≤ phiLengthOn q α (l * x + m) (l * y + m) := by
  classical
  unfold phiLengthOn
  refine le_iInf fun n => le_iInf fun τ => le_iInf fun xs => le_iInf fun h => ?_
  obtain ⟨h0, hn, hmono, hpc⟩ := h
  have hl0 : l ≠ 0 := hl.ne'
  set τ' : Fin (n + 1) → ℝ := fun j => (τ j - m) / l with hτ'
  have hτ'mono : Monotone τ' := fun i j hij =>
    div_le_div_of_nonneg_right (sub_le_sub_right (hmono hij) m) hl.le
  have hτ'0 : τ' 0 = x := by
    simp only [hτ', h0]
    field_simp
    ring
  have hτ'n : τ' (Fin.last n) = y := by
    simp only [hτ', hn]
    field_simp
    ring
  have hbd : ∀ j, x ≤ τ' j ∧ τ' j ≤ y := fun j =>
    ⟨hτ'0 ▸ hτ'mono (Fin.zero_le _), hτ'n ▸ hτ'mono (Fin.le_last _)⟩
  have hAτ : ∀ j, l * τ' j + m = τ j := fun j => by
    simp only [hτ']
    field_simp
    ring
  refine iInf_le_of_le n (iInf_le_of_le τ' (iInf_le_of_le xs (iInf_le_of_le
    ⟨hτ'0, hτ'n, hτ'mono, fun i => ?_⟩ (le_of_eq ?_))))
  · obtain ⟨hsrc, K, hK⟩ := hpc i
    have hmemI : ∀ u ∈ Icc (τ' i.castSucc) (τ' i.succ), u ∈ Icc x y ∧
        l * u + m ∈ Icc (τ i.castSucc) (τ i.succ) := fun u hu =>
      ⟨⟨(hbd _).1.trans hu.1, hu.2.trans (hbd _).2⟩, by
        rw [← hAτ i.castSucc, ← hAτ i.succ]
        exact ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩⟩
    refine ⟨?_, K * Real.toNNReal l, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [hβ u (hmemI u hu).1]
      exact hsrc ⟨l * u + m, (hmemI u hu).2, rfl⟩
    · rw [hβ u (hmemI u hu).1, hβ v (hmemI v hv).1]
      refine (hK.dist_le_mul _ (hmemI u hu).2 _ (hmemI v hv).2).trans (le_of_eq ?_)
      rw [Real.dist_eq, Real.dist_eq, show l * u + m - (l * v + m) = l * (u - v) by ring,
        abs_mul, abs_of_pos hl, NNReal.coe_mul, Real.coe_toNNReal _ hl.le]
      ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hI : Ioo (τ' i.castSucc) (τ' i.succ) ⊆ Ioo x y := Ioo_subset_Ioo (hbd _).1 (hbd _).2
    have := s25i_cov_lintegral (phiDensity (q (xs i))) (c₁ := fun v => chartAt ℂ (xs i) (β.extend v))
      (c₂ := fun v => chartAt ℂ (xs i) (α.extend v)) (l := l) (m := m) (a := τ' i.castSucc)
      (b := τ' i.succ) hl (fun u hu => by
        filter_upwards [Icc_mem_nhds (hI hu).1 (hI hu).2] with w hw using by rw [hβ w hw])
    rw [this, hAτ, hAτ]

/-- Helper for `s25i_split_ge`: clipping a partition by a monotone map `c` that sends each interval `[u, v]` either
into itself or to a point gives a partition of `[c s, c t]` whose `φ`-length bound is the clipped sum. -/
theorem s25i_clip {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) {c : ℝ → ℝ} (hc : Monotone c)
    (hd : ∀ u v : ℝ, u ≤ v → Icc (c u) (c v) ⊆ Icc u v ∨ c u = c v) {s t : ℝ} {n : ℕ}
    {τ : Fin (n + 1) → ℝ} {xs : Fin n → S} (h0 : τ 0 = s) (hn : τ (Fin.last n) = t) (hmono : Monotone τ)
    (hpc : ∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (xs i)).source ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (xs i) (γ.extend v))
        (Icc (τ i.castSucc) (τ i.succ))) :
    phiLengthOn q γ (c s) (c t) ≤ ∑ i : Fin n, ∫⁻ u in Ioo (c (τ i.castSucc)) (c (τ i.succ)),
      phiDensity (q (xs i)) (chartAt ℂ (xs i) (γ.extend u)) *
        ‖deriv (fun v : ℝ => chartAt ℂ (xs i) (γ.extend v)) u‖ₑ := by
  classical
  unfold phiLengthOn
  set xs' : Fin n → S := fun i =>
    if c (τ i.castSucc) = c (τ i.succ) then γ.extend (c (τ i.castSucc)) else xs i with hxs'
  refine iInf_le_of_le n (iInf_le_of_le (fun j => c (τ j)) (iInf_le_of_le xs' (iInf_le_of_le
    ⟨by simp only [h0], by simp only [hn], fun i j hij => hc (hmono hij), fun i => ?_⟩ (le_of_eq ?_))))
  · by_cases hdeg : c (τ i.castSucc) = c (τ i.succ)
    · have hx : xs' i = γ.extend (c (τ i.castSucc)) := if_pos hdeg
      rw [hx]
      have hpt : ∀ u ∈ Icc (c (τ i.castSucc)) (c (τ i.succ)), u = c (τ i.castSucc) := fun u hu =>
        le_antisymm (hdeg ▸ hu.2) hu.1
      refine ⟨?_, 0, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        rw [hpt u hu]
        exact mem_chart_source ℂ _
      · rw [hpt u hu, hpt v hv]
        simp
    · have hx : xs' i = xs i := if_neg hdeg
      rw [hx]
      rcases hd (τ i.castSucc) (τ i.succ) (hmono (Fin.castSucc_le_succ i)) with hsub | heq
      · obtain ⟨hsrc, K, hK⟩ := hpc i
        exact ⟨(image_mono hsub).trans hsrc, K, hK.mono hsub⟩
      · exact absurd heq hdeg
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hdeg : c (τ i.castSucc) = c (τ i.succ)
    · simp only [hdeg, Ioo_self, Measure.restrict_empty, lintegral_zero_measure]
    · have hx : xs' i = xs i := if_neg hdeg
      simp only [hx]

/-- Helper for `s25i_split_ge`: the integral over `(a, b)` dominates the integrals over the two parts clipped at `y`. -/
theorem s25i_lint_split (F : ℝ → ℝ≥0∞) {a b y : ℝ} (hab : a ≤ b) :
    (∫⁻ u in Ioo (min a y) (min b y), F u) + (∫⁻ u in Ioo (max a y) (max b y), F u) ≤
      ∫⁻ u in Ioo a b, F u := by
  have hA : Ioo (min a y) (min b y) ⊆ Ioo a b ∩ Iio y := fun u hu => by
    refine ⟨⟨?_, hu.2.trans_le (min_le_left _ _)⟩, hu.2.trans_le (min_le_right _ _)⟩
    rcases le_total a y with h | h
    · rw [min_eq_left h] at hu; exact hu.1
    · exfalso
      rw [min_eq_right h] at hu
      exact absurd (hu.1.trans hu.2) (not_lt.2 (min_le_right _ _))
  have hB : Ioo (max a y) (max b y) ⊆ Ioo a b ∩ Ioi y := fun u hu => by
    refine ⟨⟨hu.1.trans_le' (le_max_left _ _), ?_⟩, hu.1.trans_le' (le_max_right _ _) |>.trans_le' le_rfl⟩
    rcases le_total b y with h | h
    · exfalso
      rw [max_eq_right h] at hu
      exact absurd (hu.1.trans hu.2) (not_lt.2 (le_max_right _ _))
    · rw [max_eq_left h] at hu; exact hu.2
  have hdisj : Disjoint (Ioo (min a y) (min b y)) (Ioo (max a y) (max b y)) := by
    refine Set.disjoint_left.2 fun u hu1 hu2 => ?_
    have h1 : u < y := (hA hu1).2
    have h2 : y < u := (hB hu2).2
    exact absurd (h1.trans h2) (lt_irrefl _)
  rw [← lintegral_union measurableSet_Ioo hdisj]
  exact lintegral_mono_set (union_subset (hA.trans inter_subset_left) (hB.trans inter_subset_left))

/-- Helper for `shortest_isPhiGeodesicRS`: the `φ`-length of sub-arcs is superadditive.  (Clip a partition of `[x, z]`
at `y`: `τⱼ ↦ min τⱼ y` and `τⱼ ↦ max τⱼ y` give partitions of `[x, y]` and `[y, z]`, the pieces that collapse to the
point `y` being given the chart at `γ y`.) -/
theorem s25i_split_ge {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    phiLengthOn q γ x y + phiLengthOn q γ y z ≤ phiLengthOn q γ x z := by
  classical
  refine le_iInf fun n => le_iInf fun τ => le_iInf fun xs => le_iInf fun h => ?_
  obtain ⟨h0, hn, hmono, hpc⟩ := h
  have c1 := s25i_clip (q := q) γ (c := fun u => min u y) (fun u v h => min_le_min_right y h)
    (fun u v huv => by
      by_cases hu : u ≤ y
      · left
        intro w hw
        exact ⟨(min_eq_left hu) ▸ hw.1, hw.2.trans (min_le_left _ _)⟩
      · right
        push Not at hu
        simp only [min_eq_right hu.le, min_eq_right (hu.le.trans huv)]) h0 hn hmono hpc
  have c2 := s25i_clip (q := q) γ (c := fun u => max u y) (fun u v h => max_le_max_right y h)
    (fun u v huv => by
      by_cases hv : y ≤ v
      · left
        intro w hw
        exact ⟨(le_max_left u y).trans hw.1, hw.2.trans (max_eq_left hv).le⟩
      · right
        push Not at hv
        simp only [max_eq_right hv.le, max_eq_right (huv.trans hv.le)]) h0 hn hmono hpc
  simp only [min_eq_left hxy, min_eq_right hyz, max_eq_right hxy, max_eq_left hyz] at c1 c2
  calc phiLengthOn q γ x y + phiLengthOn q γ y z ≤ _ := add_le_add c1 c2
    _ = _ := (Finset.sum_add_distrib).symm
    _ ≤ _ := Finset.sum_le_sum fun i _ => s25i_lint_split _ (hmono (Fin.castSucc_le_succ i))

/-- Helper for `s25i_split_le`: concatenating an admissible partition of `[x, y]` with one of `[y, z]` gives an
admissible partition of `[x, z]` whose sum is the sum of the two sums. -/
theorem s25i_concat {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) {x y z : ℝ} {n₁ n₂ : ℕ}
    {τ₁ : Fin (n₁ + 1) → ℝ} {τ₂ : Fin (n₂ + 1) → ℝ} {x₁ : Fin n₁ → S} {x₂ : Fin n₂ → S}
    (h01 : τ₁ 0 = x) (hn1 : τ₁ (Fin.last n₁) = y) (hm1 : Monotone τ₁)
    (hp1 : ∀ i : Fin n₁, γ.extend '' Icc (τ₁ i.castSucc) (τ₁ i.succ) ⊆ (chartAt ℂ (x₁ i)).source ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x₁ i) (γ.extend v)) (Icc (τ₁ i.castSucc) (τ₁ i.succ)))
    (h02 : τ₂ 0 = y) (hn2 : τ₂ (Fin.last n₂) = z) (hm2 : Monotone τ₂)
    (hp2 : ∀ i : Fin n₂, γ.extend '' Icc (τ₂ i.castSucc) (τ₂ i.succ) ⊆ (chartAt ℂ (x₂ i)).source ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x₂ i) (γ.extend v)) (Icc (τ₂ i.castSucc) (τ₂ i.succ))) :
    phiLengthOn q γ x z ≤
      (∑ i : Fin n₁, ∫⁻ u in Ioo (τ₁ i.castSucc) (τ₁ i.succ),
        phiDensity (q (x₁ i)) (chartAt ℂ (x₁ i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x₁ i) (γ.extend v)) u‖ₑ) +
      ∑ i : Fin n₂, ∫⁻ u in Ioo (τ₂ i.castSucc) (τ₂ i.succ),
        phiDensity (q (x₂ i)) (chartAt ℂ (x₂ i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x₂ i) (γ.extend v)) u‖ₑ := by
  classical
  unfold phiLengthOn
  set τ : Fin (n₁ + n₂ + 1) → ℝ := fun j =>
    if h : j.val ≤ n₁ then τ₁ ⟨j.val, by omega⟩ else τ₂ ⟨j.val - n₁, by omega⟩ with hτ
  set xs : Fin (n₁ + n₂) → S := fun i =>
    if h : i.val < n₁ then x₁ ⟨i.val, h⟩ else x₂ ⟨i.val - n₁, by omega⟩ with hxs
  have hτ1 : ∀ k : Fin (n₁ + 1), τ ⟨k.val, by omega⟩ = τ₁ k := fun k => by
    simp only [hτ, dif_pos (Nat.lt_succ_iff.1 k.2)]
  have hτ2 : ∀ k : Fin (n₂ + 1), τ ⟨n₁ + k.val, by omega⟩ = τ₂ k := fun k => by
    rcases Nat.eq_zero_or_pos k.val with hk | hk
    · have hk0 : k = 0 := Fin.ext hk
      subst hk0
      simp only [hτ]
      rw [dif_pos (by simp)]
      exact (congrArg τ₁ (Fin.ext (by simp))).trans (hn1.trans h02.symm)
    · simp only [hτ]
      rw [dif_neg (by omega)]
      exact congrArg τ₂ (Fin.ext (by simp))
  have hA : ∀ i : Fin n₁, τ (Fin.castAdd n₂ i).castSucc = τ₁ i.castSucc ∧
      τ (Fin.castAdd n₂ i).succ = τ₁ i.succ ∧ xs (Fin.castAdd n₂ i) = x₁ i := fun i => by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hτ1 i.castSucc]; rfl
    · rw [← hτ1 i.succ]; rfl
    · simp only [hxs, Fin.coe_castAdd, dif_pos i.2]
  have hB : ∀ k : Fin n₂, τ (Fin.natAdd n₁ k).castSucc = τ₂ k.castSucc ∧
      τ (Fin.natAdd n₁ k).succ = τ₂ k.succ ∧ xs (Fin.natAdd n₁ k) = x₂ k := fun k => by
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg τ (Fin.ext (by simp))).trans (hτ2 k.castSucc)
    · exact (congrArg τ (Fin.ext (by simp <;> omega))).trans (hτ2 k.succ)
    · simp only [hxs, Fin.coe_natAdd]
      rw [dif_neg (by omega)]
      congr 1
      ext
      simp
  have hmono : Monotone τ := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    simp only [hτ]
    by_cases hi : i.val ≤ n₁
    · by_cases hj : j.val ≤ n₁
      · rw [dif_pos hi, dif_pos hj]
        exact hm1 (by simpa using hij')
      · rw [dif_pos hi, dif_neg hj]
        calc τ₁ ⟨i.val, _⟩ ≤ τ₁ (Fin.last n₁) := hm1 (Fin.le_last _)
          _ = y := hn1
          _ = τ₂ 0 := h02.symm
          _ ≤ _ := hm2 (Fin.zero_le _)
    · have hj : ¬ j.val ≤ n₁ := by omega
      rw [dif_neg hi, dif_neg hj]
      exact hm2 (by simpa using Nat.sub_le_sub_right hij' n₁)
  have h0 : τ 0 = x := by
    have := hτ1 0
    simp only [Fin.val_zero] at this
    rw [show (0 : Fin (n₁ + n₂ + 1)) = ⟨0, by omega⟩ from rfl, this, h01]
  have hn : τ (Fin.last (n₁ + n₂)) = z := by
    have := hτ2 (Fin.last n₂)
    simp only [Fin.val_last] at this
    rw [show Fin.last (n₁ + n₂) = ⟨n₁ + n₂, by omega⟩ from rfl, ← hn2, ← this]
  refine iInf_le_of_le (n₁ + n₂) (iInf_le_of_le τ (iInf_le_of_le xs (iInf_le_of_le
    ⟨h0, hn, hmono, fun i => ?_⟩ (le_of_eq ?_))))
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) i
    · obtain ⟨e1, e2, e3⟩ := hA i
      rw [e1, e2, e3]
      exact hp1 i
    · obtain ⟨e1, e2, e3⟩ := hB k
      rw [e1, e2, e3]
      exact hp2 k
  · rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨e1, e2, e3⟩ := hA i
      rw [e1, e2, e3]
    · refine Finset.sum_congr rfl fun k _ => ?_
      obtain ⟨e1, e2, e3⟩ := hB k
      rw [e1, e2, e3]

/-- Helper for `shortest_isPhiGeodesicRS`: the `φ`-length of sub-arcs is subadditive (concatenate a partition of
`[x, y]` with one of `[y, z]`). -/
theorem s25i_split_le {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    phiLengthOn q γ x z ≤ phiLengthOn q γ x y + phiLengthOn q γ y z := by
  classical
  by_cases hA : phiLengthOn q γ x y = ⊤
  · rw [hA, top_add]
    exact le_top
  by_cases hB : phiLengthOn q γ y z = ⊤
  · rw [hB, add_top]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ≥0 := ε / 2 with hδ
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]
    exact (half_pos hε).ne'
  have hδε : (δ : ℝ≥0∞) + δ = ε := by
    rw [← ENNReal.coe_add, hδ, add_halves]
  have h1 : phiLengthOn q γ x y < phiLengthOn q γ x y + δ := ENNReal.lt_add_right hA hδ0
  have h2 : phiLengthOn q γ y z < phiLengthOn q γ y z + δ := ENNReal.lt_add_right hB hδ0
  obtain ⟨n₁, h1⟩ := iInf_lt_iff.1 h1
  obtain ⟨τ₁, h1⟩ := iInf_lt_iff.1 h1
  obtain ⟨x₁, h1⟩ := iInf_lt_iff.1 h1
  obtain ⟨⟨h01, hn1, hm1, hp1⟩, hS1⟩ := iInf_lt_iff.1 h1
  obtain ⟨n₂, h2⟩ := iInf_lt_iff.1 h2
  obtain ⟨τ₂, h2⟩ := iInf_lt_iff.1 h2
  obtain ⟨x₂, h2⟩ := iInf_lt_iff.1 h2
  obtain ⟨⟨h02, hn2, hm2, hp2⟩, hS2⟩ := iInf_lt_iff.1 h2
  calc phiLengthOn q γ x z ≤ _ := s25i_concat γ h01 hn1 hm1 hp1 h02 hn2 hm2 hp2
    _ ≤ (phiLengthOn q γ x y + δ) + (phiLengthOn q γ y z + δ) := add_le_add hS1.le hS2.le
    _ = phiLengthOn q γ x y + phiLengthOn q γ y z + ε := by rw [← hδε]; ring

/-- Helper for `shortest_isPhiGeodesicRS`: the sub-arc `γ|[s, t]`, reparametrized affinely to `[0, 1]`, is a path
whose `φ`-length is at most `l_φ(γ|[s, t])` (`s25i_transport`). -/
theorem s25i_subpath_length {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1) :
    ∃ β : Path (γ.extend s) (γ.extend t), (∀ u, β u ∈ γ.extend '' Icc s t) ∧
      phiLengthPath q β ≤ phiLengthOn q γ s t := by
  classical
  have hts : 0 < t - s := sub_pos.2 hst
  have hcont : Continuous (fun u : unitInterval => γ.extend (s + (t - s) * (u : ℝ))) :=
    γ.continuous_extend.comp (by fun_prop)
  let β : Path (γ.extend s) (γ.extend t) :=
    ⟨⟨fun u : unitInterval => γ.extend (s + (t - s) * (u : ℝ)), hcont⟩, by simp, by simp⟩
  have hβ : ∀ u ∈ Icc (0 : ℝ) 1, β.extend u = γ.extend ((t - s) * u + s) := fun u hu => by
    rw [Path.extend_apply β hu]
    show γ.extend (s + (t - s) * u) = _
    rw [add_comm]
  refine ⟨β, fun u => ⟨s + (t - s) * (u : ℝ), ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · nlinarith [u.2.1]
  · nlinarith [u.2.2]
  · have := s25i_transport (q := q) γ β (l := t - s) (m := s) (x := 0) (y := 1) hts zero_le_one hβ
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at this
    exact this

/-- Helper for `s25i_splice`: the spliced path, `γ` off `(s, t)` and the affine reparametrization of `σ` on `[s, t]`. -/
theorem s25i_splice_path {a b : S} (γ : Path a b) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (σ : Path (γ.extend s) (γ.extend t)) :
    ∃ γ' : Path a b, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → γ'.extend u =
      if u ≤ s then γ.extend u else if u ≤ t then σ.extend ((u - s) / (t - s)) else γ.extend u := by
  classical
  have hts : 0 < t - s := sub_pos.2 hst
  set F : ℝ → S := fun u => if u ≤ s then γ.extend u else
    if u ≤ t then σ.extend ((u - s) / (t - s)) else γ.extend u with hF
  have hinner : Continuous fun u : ℝ => if u ≤ t then σ.extend ((u - s) / (t - s)) else γ.extend u := by
    refine Continuous.if_le (σ.continuous_extend.comp (by fun_prop)) γ.continuous_extend continuous_id
      continuous_const (fun u hu => ?_)
    show σ.extend ((u - s) / (t - s)) = γ.extend u
    have hu : u = t := hu
    rw [hu, div_self hts.ne']
    exact Path.extend_one σ
  have hcont : Continuous F := by
    refine Continuous.if_le γ.continuous_extend hinner continuous_id continuous_const (fun u hu => ?_)
    show γ.extend u = if u ≤ t then σ.extend ((u - s) / (t - s)) else γ.extend u
    have hu : u = s := hu
    rw [hu, if_pos hst.le, sub_self, zero_div]
    exact (Path.extend_zero σ).symm
  have hF0 : F 0 = a := by
    simp only [hF, if_pos hs]
    exact Path.extend_zero γ
  have hF1 : F 1 = b := by
    have hs1 : ¬ (1 ≤ s) := by linarith
    simp only [hF, if_neg hs1]
    by_cases h : 1 ≤ t
    · have ht1 : t = 1 := le_antisymm ht h
      rw [if_pos h, ← ht1, div_self hts.ne']
      rw [Path.extend_one σ, ht1]
      exact Path.extend_one γ
    · rw [if_neg h]
      exact Path.extend_one γ
  refine ⟨⟨⟨fun u : unitInterval => F u, hcont.comp continuous_subtype_val⟩, hF0, hF1⟩, fun u hu0 hu1 => ?_⟩
  rw [Path.extend_apply _ ⟨hu0, hu1⟩]
  rfl

/-- Helper for `s25i_splice`: the spliced path is homotopic to `γ` (straight-line homotopy in the chart disc on
`[s, t]`, fixed outside). -/
theorem s25i_splice_homotopic {a b : S} (γ : Path a b) (p : S) {r : ℝ}
    (hr : ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (hγ : γ.extend '' Icc s t ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r)
    (σ : Path (γ.extend s) (γ.extend t))
    (hσ : ∀ u, σ u ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r)
    (γ' : Path a b) (hγ' : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → γ'.extend u =
      if u ≤ s then γ.extend u else if u ≤ t then σ.extend ((u - s) / (t - s)) else γ.extend u) :
    γ'.Homotopic γ := by
  classical
  set φ := chartAt ℂ p with hφ
  set z₀ := chartAt ℂ p p with hz₀
  have hts : 0 < t - s := sub_pos.2 hst
  set cl : ℝ → ℝ := fun u => max s (min u t) with hcl
  have hclc : Continuous cl := by fun_prop
  have hcl1 : ∀ u, s ≤ cl u ∧ cl u ≤ t := fun u =>
    ⟨le_max_left _ _, max_le hst.le (min_le_right _ _)⟩
  have hcl2 : ∀ u, s ≤ u → u ≤ t → cl u = u := fun u h1 h2 => by
    simp only [hcl, min_eq_left h2, max_eq_right h1]
  have hσe : ∀ v ∈ Icc (0 : ℝ) 1, σ.extend v ∈ φ.source ∩ φ ⁻¹' ball z₀ r := fun v hv => by
    rw [Path.extend_apply σ hv]
    exact hσ _
  have hv : ∀ u, (cl u - s) / (t - s) ∈ Icc (0 : ℝ) 1 := fun u =>
    ⟨div_nonneg (sub_nonneg.2 (hcl1 u).1) hts.le, (div_le_one hts).2 (by linarith [(hcl1 u).2])⟩
  have hγe : ∀ u, γ.extend (cl u) ∈ φ.source ∩ φ ⁻¹' ball z₀ r := fun u => hγ ⟨cl u, hcl1 u, rfl⟩
  set Ψσ : ℝ → ℂ := fun u => φ (σ.extend ((cl u - s) / (t - s))) with hΨσ
  set Ψγ : ℝ → ℂ := fun u => φ (γ.extend (cl u)) with hΨγ
  have hΨσc : Continuous Ψσ :=
    φ.continuousOn.comp_continuous (σ.continuous_extend.comp (by fun_prop)) (fun u => (hσe _ (hv u)).1)
  have hΨγc : Continuous Ψγ :=
    φ.continuousOn.comp_continuous (γ.continuous_extend.comp hclc) (fun u => (hγe u).1)
  have hΨσb : ∀ u, Ψσ u ∈ ball z₀ r := fun u => (hσe _ (hv u)).2
  have hΨγb : ∀ u, Ψγ u ∈ ball z₀ r := fun u => (hγe u).2
  set comb : ℝ → ℝ → ℂ := fun ρ u => (1 - ρ) • Ψσ u + ρ • Ψγ u with hcomb
  have hcombb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ u, comb ρ u ∈ ball z₀ r := fun ρ h0 h1 u =>
    (convex_ball z₀ r) (hΨσb u) (hΨγb u) (sub_nonneg.2 h1) h0 (by ring)
  set M : ℝ → ℝ → S := fun ρ u => φ.symm (comb ρ u) with hM
  have hcombc : Continuous fun x : unitInterval × unitInterval => comb (x.1 : ℝ) (x.2 : ℝ) := by
    have h1 : Continuous fun x : unitInterval × unitInterval => (x.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun x : unitInterval × unitInterval => (x.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub h1).smul (hΨσc.comp h2)).add (h1.smul (hΨγc.comp h2))
  have hMc : Continuous fun x : unitInterval × unitInterval => M (x.1 : ℝ) (x.2 : ℝ) :=
    φ.continuousOn_symm.comp_continuous hcombc (fun x => hr (hcombb x.1 x.1.2.1 x.1.2.2 x.2))
  -- values of `M`
  have hMs : ∀ ρ : ℝ, M ρ s = γ.extend s := fun ρ => by
    have e1 : Ψσ s = φ (γ.extend s) := by
      simp only [hΨσ, hcl2 s le_rfl hst.le, sub_self, zero_div]
      rw [Path.extend_zero σ]
    have e2 : Ψγ s = φ (γ.extend s) := by
      simp only [hΨγ, hcl2 s le_rfl hst.le]
    have e3 : comb ρ s = φ (γ.extend s) := by
      simp only [hcomb, e1, e2]
      rw [← add_smul]
      simp
    simp only [hM, e3]
    exact φ.left_inv (hγ ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩).1
  have hMt : ∀ ρ : ℝ, M ρ t = γ.extend t := fun ρ => by
    have e1 : Ψσ t = φ (γ.extend t) := by
      simp only [hΨσ, hcl2 t hst.le le_rfl, div_self hts.ne']
      rw [Path.extend_one σ]
    have e2 : Ψγ t = φ (γ.extend t) := by
      simp only [hΨγ, hcl2 t hst.le le_rfl]
    have e3 : comb ρ t = φ (γ.extend t) := by
      simp only [hcomb, e1, e2]
      rw [← add_smul]
      simp
    simp only [hM, e3]
    exact φ.left_inv (hγ ⟨t, ⟨hst.le, le_rfl⟩, rfl⟩).1
  have hM0 : ∀ u ∈ Icc s t, M 0 u = σ.extend ((u - s) / (t - s)) := fun u hu => by
    have e3 : comb 0 u = φ (σ.extend ((u - s) / (t - s))) := by
      simp only [hcomb, hΨσ, hcl2 u hu.1 hu.2]
      simp
    simp only [hM, e3]
    exact φ.left_inv (hσe _ (by simpa [hcl2 u hu.1 hu.2] using hv u)).1
  have hM1 : ∀ u ∈ Icc s t, M 1 u = γ.extend u := fun u hu => by
    have e3 : comb 1 u = φ (γ.extend u) := by
      simp only [hcomb, hΨγ, hcl2 u hu.1 hu.2]
      simp
    simp only [hM, e3]
    exact φ.left_inv (hγ ⟨u, hu, rfl⟩).1
  have hext : ∀ {x y : S} (τ : Path x y) (u : unitInterval), τ.extend (u : ℝ) = τ u := fun τ u => by
    rw [Path.extend_apply τ u.2]
  set H : unitInterval × unitInterval → S := fun x =>
    if (x.2 : ℝ) ≤ s then γ.extend (x.2 : ℝ) else
      if (x.2 : ℝ) ≤ t then M (x.1 : ℝ) (x.2 : ℝ) else γ.extend (x.2 : ℝ) with hH
  have h2c : Continuous fun x : unitInterval × unitInterval => (x.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hHin : Continuous fun x : unitInterval × unitInterval =>
      if (x.2 : ℝ) ≤ t then M (x.1 : ℝ) (x.2 : ℝ) else γ.extend (x.2 : ℝ) := by
    refine Continuous.if_le hMc (γ.continuous_extend.comp h2c) h2c continuous_const (fun x hx => ?_)
    have hx : (x.2 : ℝ) = t := hx
    show M (x.1 : ℝ) (x.2 : ℝ) = γ.extend (x.2 : ℝ)
    rw [hx]
    exact hMt _
  have hHc : Continuous H := by
    refine Continuous.if_le (γ.continuous_extend.comp h2c) hHin h2c continuous_const (fun x hx => ?_)
    have hx : (x.2 : ℝ) = s := hx
    show γ.extend (x.2 : ℝ) = if (x.2 : ℝ) ≤ t then M (x.1 : ℝ) (x.2 : ℝ) else γ.extend (x.2 : ℝ)
    rw [hx, if_pos hst.le]
    exact (hMs _).symm
  refine ⟨{ toFun := H, continuous_toFun := hHc, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · intro u
    show H (0, u) = γ' u
    rw [← hext γ' u, hγ' u u.2.1 u.2.2]
    by_cases h1 : (u : ℝ) ≤ s
    · simp only [hH, if_pos h1]
    · by_cases h2 : (u : ℝ) ≤ t
      · simp only [hH, if_neg h1, if_pos h2]
        exact hM0 u ⟨(not_le.1 h1).le, h2⟩
      · simp only [hH, if_neg h1, if_neg h2]
  · intro u
    show H (1, u) = γ u
    rw [← hext γ u]
    by_cases h1 : (u : ℝ) ≤ s
    · simp only [hH, if_pos h1]
    · by_cases h2 : (u : ℝ) ≤ t
      · simp only [hH, if_neg h1, if_pos h2]
        exact hM1 u ⟨(not_le.1 h1).le, h2⟩
      · simp only [hH, if_neg h1, if_neg h2]
  · intro ρ u hu
    show H (ρ, u) = γ' u
    rcases hu with hu | hu
    · subst hu
      have h0 : ((0 : unitInterval) : ℝ) ≤ s := by simpa using hs
      simp only [hH, if_pos h0]
      rw [show γ' 0 = a from γ'.source]
      simpa using Path.extend_zero γ
    · subst hu
      rw [show γ' 1 = b from γ'.target]
      have h1 : ¬ (((1 : unitInterval) : ℝ) ≤ s) := by simp; linarith
      by_cases h2 : ((1 : unitInterval) : ℝ) ≤ t
      · have ht1 : t = 1 := le_antisymm ht (by simpa using h2)
        simp only [hH, if_neg h1, if_pos h2]
        have := hMt ρ
        rw [ht1] at this
        simpa [ht1] using this.trans (Path.extend_one γ)
      · simp only [hH, if_neg h1, if_neg h2]
        simpa using Path.extend_one γ

/-- Helper for `shortest_isPhiGeodesicRS`: replacing a sub-arc `γ|[s, t]` that lies in a chart disc `D` by any path
`σ` in `D` with the same end points gives a homotopic path (the straight-line homotopy in the chart), whose
`φ`-length is at most `l_φ(γ|[0, s]) + l_φ(σ) + l_φ(γ|[t, 1])` (the new path is `γ` off `(s, t)` and the affine
reparametrization of `σ` on `[s, t]`; `s25i_split_le`, `s25i_transport`). -/
theorem s25i_splice {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) (p : S) {r : ℝ}
    (hr : ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (hγ : γ.extend '' Icc s t ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r)
    (σ : Path (γ.extend s) (γ.extend t))
    (hσ : ∀ u, σ u ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) :
    ∃ γ' : Path a b, γ'.Homotopic γ ∧
      phiLengthPath q γ' ≤ phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 := by
  classical
  obtain ⟨γ', hγ'⟩ := s25i_splice_path γ hs hst ht σ
  refine ⟨γ', s25i_splice_homotopic γ p hr hs hst ht hγ σ hσ γ' hγ', ?_⟩
  have hts : 0 < t - s := sub_pos.2 hst
  have hs1 : s ≤ 1 := hst.le.trans ht
  have e1 : phiLengthOn q γ' 0 s ≤ phiLengthOn q γ 0 s := by
    have := s25i_transport (q := q) γ γ' (l := 1) (m := 0) (x := 0) (y := s) one_pos hs (fun u hu => by
      rw [hγ' u hu.1 (hu.2.trans hs1), if_pos hu.2]
      simp)
    simpa using this
  have e2 : phiLengthOn q γ' s t ≤ phiLengthPath q σ := by
    have := s25i_transport (q := q) σ γ' (l := 1 / (t - s)) (m := -s / (t - s)) (x := s) (y := t)
      (one_div_pos.2 hts) hst.le (fun u hu => by
        rw [hγ' u (hs.trans hu.1) (hu.2.trans ht)]
        by_cases hus : u ≤ s
        · have hu' : u = s := le_antisymm hus hu.1
          subst hu'
          rw [if_pos hus]
          have : 1 / (t - u) * u + -u / (t - u) = 0 := by field_simp; ring
          rw [this]
          exact (Path.extend_zero σ).symm
        · rw [if_neg hus, if_pos hu.2]
          congr 1
          field_simp
          ring)
    have h0 : 1 / (t - s) * s + -s / (t - s) = 0 := by field_simp; ring
    have h1 : 1 / (t - s) * t + -s / (t - s) = 1 := by field_simp; ring
    rw [h0, h1] at this
    exact this
  have e3 : phiLengthOn q γ' t 1 ≤ phiLengthOn q γ t 1 := by
    have := s25i_transport (q := q) γ γ' (l := 1) (m := 0) (x := t) (y := 1) one_pos ht (fun u hu => by
      rw [hγ' u ((hs.trans hst.le).trans hu.1) hu.2, if_neg (not_le.2 (hst.trans_le hu.1))]
      by_cases hut : u ≤ t
      · have hu' : u = t := le_antisymm hut hu.1
        subst hu'
        rw [if_pos hut, div_self hts.ne']
        simpa using Path.extend_one σ
      · rw [if_neg hut]
        simp)
    simpa using this
  have hsplit1 := s25i_split_le (q := q) γ' (x := 0) (y := s) (z := 1) hs hs1
  have hsplit2 := s25i_split_le (q := q) γ' (x := s) (y := t) (z := 1) hst.le ht
  unfold phiLengthPath
  calc phiLengthOn q γ' 0 1 ≤ phiLengthOn q γ' 0 s + phiLengthOn q γ' s 1 := hsplit1
    _ ≤ phiLengthOn q γ' 0 s + (phiLengthOn q γ' s t + phiLengthOn q γ' t 1) := by gcongr
    _ ≤ phiLengthOn q γ 0 s + (phiLengthPath q σ + phiLengthOn q γ t 1) := by gcongr
    _ = phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 := by ring

/-- Helper for `shortest_isPhiGeodesicRS`: near every point `p` there is a chart disc `D` and a neighbourhood `V ⊆ D`
such that two points of `V` are joined by a path in `D` whose `φ`-length is their `φ`-distance
(`exists_local_shortest_nbhd`, with the neighbourhood of `s25e_surface_upper` shrunk into the disc). -/
theorem s25i_local [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ r > 0, ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧ ∃ V ∈ 𝓝 p,
      V ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r ∧
      ∀ a ∈ V, ∀ b ∈ V, ∃ σ : Path a b,
        (∀ u, σ u ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) ∧
          phiLengthPath q σ = phiDistRS q a b := by
  classical
  set z₀ := chartAt ℂ p p with hz₀
  have hz₀t : z₀ ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  obtain ⟨r, hr0, hrt⟩ := Metric.isOpen_iff.1 (chartAt ℂ p).open_target z₀ hz₀t
  have hDo : IsOpen ((chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball z₀ r) :=
    (chartAt ℂ p).continuousOn.isOpen_inter_preimage (chartAt ℂ p).open_source isOpen_ball
  have hpD : p ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball z₀ r :=
    ⟨mem_chart_source ℂ p, mem_ball_self hr0⟩
  refine ⟨r, hr0, hrt, ?_⟩
  obtain ⟨m, ζ, hζ, hζ0, hζd, hζq⟩ := s25e_natural_chart hq hne p
  obtain ⟨W, hW, hlow⟩ := s25e_surface_lower hq hne p m ζ hζ hζ0 hζd hζq
  obtain ⟨V, hV, hVW, hup⟩ := s25e_surface_upper hq hne p m ζ hζ hζ0 hζd hζq
    (W ∩ ((chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball z₀ r)) (inter_mem hW (hDo.mem_nhds hpD))
  refine ⟨V, hV, fun x hx => (hVW hx).2, fun a ha b hb => ?_⟩
  obtain ⟨σ, hσV, hσl⟩ := hup a ha b hb
  refine ⟨σ, fun u => (hVW (hσV u)).2, le_antisymm ?_ (iInf_le _ σ)⟩
  exact le_iInf fun γ' => hσl.trans (hlow a (hVW ha).1 b (hVW hb).1 γ')

/-- A nonzero actual holomorphic one-form has an effective canonical divisor.
The witness is built from its genuine meromorphic section and finite zero divisor;
all chart coefficients are obtained from the installed canonical-data bridge. -/
theorem k25g1_effective_canonical
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    (ω₀ : Jacobians.HolomorphicOneForms S) (hω₀ : ω₀ ≠ 0) :
    ∃ K : Divisor S, IsCanonicalDivisor K ∧ ∀ x, 0 ≤ K x := by
  classical
  let K : Divisor S := Jacobians.LaurentTail.canonicalDivisorOf ω₀ hω₀
  let data : Jacobians.Dolbeault.CanonicalForm17Data S :=
    { ω₀ := Jacobians.Dolbeault.holToMero ω₀
      nontrivial := by
        obtain ⟨x⟩ := (inferInstance : Nonempty S)
        refine ⟨x, ?_⟩
        change meromorphicOrderAt
          (Jacobians.Dolbeault.formCoeff
            (Jacobians.Dolbeault.holToSection ω₀) x) (chartAt ℂ x x) ≠ ⊤
        rw [Jacobians.Dolbeault.formCoeff_holToSection]
        exact Jacobians.LaurentTail.omegaOrderAt_ne_top ω₀ hω₀ x
      K := K
      order_eq := by
        intro x
        change meromorphicOrderAt
          (Jacobians.Dolbeault.formCoeff
            (Jacobians.Dolbeault.holToSection ω₀) x) (chartAt ℂ x x) =
          (K x : WithTop ℤ)
        rw [Jacobians.Dolbeault.formCoeff_holToSection]
        exact (Jacobians.LaurentTail.coe_canonicalDivisorOf ω₀ hω₀ x).symm }
  refine ⟨K, ?_, ?_⟩
  · exact k22q_canonical_chart_coefficients data
  · intro x
    have horder : (0 : WithTop ℤ) ≤ (K x : WithTop ℤ) := by
      rw [show (K x : WithTop ℤ) =
          Jacobians.LaurentTail.omegaOrderAt ω₀ x from
        Jacobians.LaurentTail.coe_canonicalDivisorOf ω₀ hω₀ x]
      exact (Jacobians.LaurentTail.analyticAt_coeffAt_self ω₀ x).meromorphicOrderAt_nonneg
    exact WithTop.coe_le_coe.mp horder

/-- For actual genus one the effective canonical divisor has degree zero,
so the frozen canonical predicate has a genuine zero-divisor witness. -/
theorem k25g1_zero_canonical
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (hS : HasGenus S 1) : IsCanonicalDivisor (0 : Divisor S) := by
  classical
  letI : CompactSpace S := hS.1
  have hgenus : genus S = 1 := k22rr_genus_eq hS
  have hpos : 0 < genus S := by omega
  obtain ⟨ω₀, hω₀⟩ := Jacobians.Dolbeault.exists_holomorphicOneForm_ne_zero hpos
  obtain ⟨K, hK, hnonneg⟩ := k25g1_effective_canonical ω₀ hω₀
  have hdegree : K.deg = 0 := by
    simpa using (deg_canonical hS hK)
  have heffective : (0 : Divisor S) ≤ K := by
    intro x
    change 0 ≤ K x
    exact hnonneg x
  have hdegreeJ : Jacobians.Divisor.deg S K = 0 := by
    rw [k22rr_degree_eq]
    exact hdegree
  have hzero : K = 0 :=
    Jacobians.Dolbeault.FiniteCover.eq_zero_of_effective_deg_zero heffective hdegreeJ
  simpa only [hzero] using hK

/-!
READ-ONLY PROPOSAL, UNELABORATED, UNFROZEN. No S25 proof work is authorized.
Insert above the original Theorem 25.4 docstring. All bodies are deliberate stubs.
The route minimizes a continuous finite-edge cost on compact vertex sets.
Greedy first-exit subdivision replaces exact equal-arclength subdivision.
-/

/-- Proposed length bridge: concatenating two paths costs at most the sum.
Use the installed positive affine transport and split inequalities. -/
theorem s25s_length_trans_le {q : S → ℂ → ℂ} {a b c : S}
    (α : Path a b) (β : Path b c) :
    phiLengthPath q (α.trans β) ≤ phiLengthPath q α + phiLengthPath q β := by
  classical
  have hleft : phiLengthOn q (α.trans β) 0 (1 / 2) ≤ phiLengthPath q α := by
    have h := s25i_transport (q := q) α (α.trans β)
      (l := 2) (m := 0) (x := 0) (y := 1 / 2) (by norm_num) (by norm_num)
      (fun u hu => by
        simpa only [add_zero] using Path.extend_trans_of_le_half α β hu.2)
    norm_num at h
    exact h
  have hright : phiLengthOn q (α.trans β) (1 / 2) 1 ≤ phiLengthPath q β := by
    have h := s25i_transport (q := q) β (α.trans β)
      (l := 2) (m := -1) (x := 1 / 2) (y := 1) (by norm_num) (by norm_num)
      (fun u hu => by
        simpa only [sub_eq_add_neg] using Path.extend_trans_of_half_le α β hu.1)
    norm_num at h
    exact h
  change phiLengthOn q (α.trans β) 0 1 ≤ _
  exact (s25i_split_le (α.trans β) (by norm_num) (by norm_num)).trans
    (add_le_add hleft hright)


/-- An arbitrary split time for the equal-grid gluing proof. The two affine pieces
meet at the common endpoint, and installed affine transport bounds their lengths. -/
theorem s25s_join_at {q : S → ℂ → ℂ} {a b c : S}
    (α : Path a b) (β : Path b c) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ γ : Path a c,
      (∀ t ∈ Icc 0 r, γ.extend t = α.extend (t / r)) ∧
      (∀ t ∈ Icc r 1, γ.extend t = β.extend ((t - r) / (1 - r))) ∧
      phiLengthPath q γ ≤ phiLengthPath q α + phiLengthPath q β := by
  classical
  have hrne : r ≠ 0 := hr0.ne'
  have hd : 0 < 1 - r := sub_pos.mpr hr1
  have hdne : 1 - r ≠ 0 := hd.ne'
  let F : ℝ → S := fun t =>
    if t ≤ r then α.extend (t / r) else β.extend ((t - r) / (1 - r))
  have hF : Continuous F := by
    apply continuous_if_le continuous_id continuous_const
      (α.continuous_extend.comp (by fun_prop)).continuousOn
      (β.continuous_extend.comp (by fun_prop)).continuousOn
    intro t ht
    change t = r at ht
    subst t
    simp only [Function.comp_apply, div_self hrne, sub_self, zero_div,
      Path.extend_one, Path.extend_zero]
  have hF0 : F 0 = a := by simp [F, hr0.le, Path.extend_zero]
  have hF1 : F 1 = c := by simp [F, not_le.mpr hr1, hdne, Path.extend_one]
  let γ : Path a c := Path.ofLine hF.continuousOn hF0 hF1
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = F t := by
    intro t ht
    rw [Path.extend_apply γ ht]
    rfl
  have hl : ∀ t ∈ Icc 0 r, γ.extend t = α.extend (t / r) := by
    intro t ht
    rw [hγ t ⟨ht.1, ht.2.trans hr1.le⟩]
    exact if_pos ht.2
  have hr : ∀ t ∈ Icc r 1, γ.extend t = β.extend ((t - r) / (1 - r)) := by
    intro t ht
    by_cases htr : t ≤ r
    · have he : t = r := le_antisymm htr ht.1
      subst t
      rw [hl r ⟨hr0.le, le_rfl⟩]
      simp [hrne, Path.extend_one, Path.extend_zero]
    · rw [hγ t ⟨hr0.le.trans ht.1, ht.2⟩]
      exact if_neg htr
  refine ⟨γ, hl, hr, ?_⟩
  have hll : phiLengthOn q γ 0 r ≤ phiLengthPath q α := by
    have h := s25i_transport (q := q) α γ (l := 1 / r) (m := 0)
      (x := 0) (y := r) (one_div_pos.mpr hr0) hr0.le
      (fun t ht => by simpa only [one_div, div_eq_mul_inv, mul_comm, add_zero, mul_one] using hl t ht)
    change phiLengthOn q γ 0 r ≤ phiLengthOn q α 0 1
    simpa [hrne] using h
  have hrr : phiLengthOn q γ r 1 ≤ phiLengthPath q β := by
    have h := s25i_transport (q := q) β γ (l := 1 / (1 - r)) (m := -r / (1 - r))
      (x := r) (y := 1) (one_div_pos.mpr hd) hr1.le
      (fun t ht => by
        rw [hr t ht]
        congr 1
        ring)
    have he0 : 1 / (1 - r) * r + -r / (1 - r) = 0 := by ring
    have he1 : 1 / (1 - r) * 1 + -r / (1 - r) = 1 := by
      field_simp [hdne]
      ring
    change phiLengthOn q γ r 1 ≤ phiLengthOn q β 0 1
    simpa only [he0, he1] using h
  exact (s25i_split_le γ hr0.le hr1.le).trans (add_le_add hll hrr)

/-- Proposed finite gluing bridge: glue endpoint-compatible paths on an equal time grid,
retain each segment's trace, and bound total length by the finite sum of segment lengths. -/
theorem s25s_glue_path {q : S → ℂ → ℂ} {N : ℕ} (hN : 0 < N)
    (x : Fin (N + 1) → S)
    (σ : ∀ i : Fin N, Path (x i.castSucc) (x i.succ)) :
    ∃ γ : Path (x 0) (x (Fin.last N)),
      (∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = x j) ∧
      (∀ i : Fin N, γ.extend ''
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆ range (σ i)) ∧
      phiLengthPath q γ ≤ ∑ i : Fin N, phiLengthPath q (σ i) := by
  classical
  revert x
  revert hN
  induction N with
  | zero =>
    intro hN
    omega
  | succ n ih =>
    intro hN x σ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      refine ⟨σ 0, ?_, ?_, ?_⟩
      · intro j
        fin_cases j <;> simp [Path.extend_zero, Path.extend_one]
      · intro i
        fin_cases i
        rintro _ ⟨t, ht, rfl⟩
        have ht01 : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
        exact ⟨⟨t, ht01⟩, (Path.extend_apply (σ 0) ht01).symm⟩
      · simp
    · let x' : Fin (n + 1) → S := fun j => x j.castSucc
      let σ' : ∀ i : Fin n, Path (x' i.castSucc) (x' i.succ) :=
        fun i => σ i.castSucc
      obtain ⟨δ, hδv, hδtrace, hδlen⟩ := ih hn x' σ'
      dsimp only [σ'] at hδlen
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hd : 0 < (n + 1 : ℝ) := by positivity
      let r : ℝ := (n : ℝ) / (n + 1 : ℝ)
      have hr0 : 0 < r := div_pos hnR hd
      have hr1 : r < 1 := (div_lt_one hd).2 (by linarith)
      obtain ⟨γ₀, hl₀, hr₀, hγ₀len⟩ := s25s_join_at (q := q) δ (σ (Fin.last n)) hr0 hr1
      have hx0 : x 0 = x' 0 := congrArg x (Fin.ext rfl)
      have hx1 : x (Fin.last (n + 1)) = x (Fin.last n).succ := congrArg x (Fin.ext rfl)
      let γ : Path (x 0) (x (Fin.last (n + 1))) := γ₀.cast hx0 hx1
      have hγext : γ.extend = γ₀.extend := Path.extend_cast γ₀ hx0 hx1
      have hl : ∀ t ∈ Icc 0 r, γ.extend t = δ.extend (t / r) := by
        intro t ht
        rw [hγext]
        exact hl₀ t ht
      have hr : ∀ t ∈ Icc r 1, γ.extend t = (σ (Fin.last n)).extend ((t - r) / (1 - r)) := by
        intro t ht
        rw [hγext]
        exact hr₀ t ht
      have hγlen : phiLengthPath q γ ≤ phiLengthPath q δ + phiLengthPath q (σ (Fin.last n)) := hγ₀len
      refine ⟨γ, ?_, ?_, ?_⟩
      · intro j
        simp only [Nat.cast_add, Nat.cast_one]
        by_cases hj : j.val = n + 1
        · have he : j = Fin.last (n + 1) := Fin.ext hj
          subst j
          simp [Path.extend_one, hd.ne']
        · have hjn : j.val < n + 1 := by omega
          let j' : Fin (n + 1) := ⟨j.val, hjn⟩
          have hjle : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ hjn)
          have ht : (j.val : ℝ) / (n + 1 : ℝ) ∈ Icc 0 r :=
            ⟨div_nonneg (Nat.cast_nonneg _) hd.le,
             div_le_div_of_nonneg_right hjle hd.le⟩
          rw [hl _ ht]
          have htime : ((j.val : ℝ) / (n + 1 : ℝ)) / r = (j'.val : ℝ) / (n : ℝ) := by
            dsimp [r, j']
            exact div_div_div_cancel_right₀ hd.ne' _ _
          rw [htime, hδv j']
          exact congrArg x (Fin.ext rfl)
      · intro i
        rintro _ ⟨t, ht, rfl⟩
        simp only [Nat.cast_add, Nat.cast_one] at ht
        by_cases hi : i.val < n
        · let i' : Fin n := ⟨i.val, hi⟩
          have hie : i = i'.castSucc := Fin.ext rfl
          have hib : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hi)
          have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hd.le).trans ht.1
          have htr : t ≤ r := ht.2.trans (div_le_div_of_nonneg_right hib hd.le)
          rw [hl t ⟨ht0, htr⟩]
          have he0 : ((i.val : ℝ) / (n + 1 : ℝ)) / r = (i'.val : ℝ) / (n : ℝ) := by
            dsimp [r, i']
            exact div_div_div_cancel_right₀ hd.ne' _ _
          have he1 : (((i.val : ℝ) + 1) / (n + 1 : ℝ)) / r =
              ((i'.val : ℝ) + 1) / (n : ℝ) := by
            dsimp [r, i']
            exact div_div_div_cancel_right₀ hd.ne' _ _
          have hscaled : t / r ∈ Icc ((i'.val : ℝ) / (n : ℝ))
              (((i'.val : ℝ) + 1) / (n : ℝ)) := by
            rw [← he0, ← he1]
            exact ⟨div_le_div_of_nonneg_right ht.1 hr0.le,
              div_le_div_of_nonneg_right ht.2 hr0.le⟩
          have hx : δ.extend (t / r) ∈ range (σ i'.castSucc) :=
            hδtrace i' ⟨t / r, hscaled, rfl⟩
          rw [← hie] at hx
          exact hx
        · have hie : i = Fin.last n := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst i
          have htr : r ≤ t := by simpa only [Fin.val_last, r] using ht.1
          have ht1 : t ≤ 1 := by
            simpa only [Fin.val_last, div_self hd.ne'] using ht.2
          rw [hr t ⟨htr, ht1⟩]
          have hden : 0 < 1 - r := sub_pos.mpr hr1
          have hu : (t - r) / (1 - r) ∈ Icc (0 : ℝ) 1 :=
            ⟨div_nonneg (sub_nonneg.mpr htr) hden.le,
              (div_le_one hden).2 (by linarith)⟩
          exact ⟨⟨(t - r) / (1 - r), hu⟩, (Path.extend_apply (σ (Fin.last n)) hu).symm⟩
      · calc
          phiLengthPath q γ ≤ phiLengthPath q δ + phiLengthPath q (σ (Fin.last n)) := hγlen
          _ ≤ (∑ i : Fin n, phiLengthPath q (σ i.castSucc)) +
              phiLengthPath q (σ (Fin.last n)) :=
                add_le_add hδlen (le_refl (phiLengthPath q (σ (Fin.last n))))
          _ = ∑ i : Fin (n + 1), phiLengthPath q (σ i) := by
            rw [Fin.sum_univ_castSucc]


/-- Two paths in one preferred-chart disc are homotopic relative to their endpoints. -/
theorem s25s_disc_homotopic {a b : S} (p : S) {r : ℝ}
    (hr : ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target)
    (α β : Path a b)
    (hα : ∀ u, α u ∈ (chartAt ℂ p).source ∩
      chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r)
    (hβ : ∀ u, β u ∈ (chartAt ℂ p).source ∩
      chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) : α.Homotopic β := by
  let φ := chartAt ℂ p
  let A : unitInterval → ℂ := fun u => φ (α u)
  let B : unitInterval → ℂ := fun u => φ (β u)
  have hAc : Continuous A := φ.continuousOn.comp_continuous α.continuous
    (fun u => (hα u).1)
  have hBc : Continuous B := φ.continuousOn.comp_continuous β.continuous
    (fun u => (hβ u).1)
  let F : unitInterval × unitInterval → ℂ := fun z =>
    (1 - (z.1 : ℝ)) • A z.2 + (z.1 : ℝ) • B z.2
  have hFc : Continuous F := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hAc.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hBc.comp continuous_snd))
  have hF : ∀ z, F z ∈ ball (φ p) r := by
    intro z
    exact (convex_ball (φ p) r) (hα z.2).2 (hβ z.2).2
      (sub_nonneg.2 z.1.2.2) z.1.2.1 (by ring)
  refine ⟨{ toFun := fun z => φ.symm (F z)
            continuous_toFun := φ.continuousOn_symm.comp_continuous hFc
              (fun z => hr (hF z))
            map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · intro u
    change φ.symm ((1 - (0 : ℝ)) • A u + (0 : ℝ) • B u) = α u
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using φ.left_inv (hα u).1
  · intro u
    change φ.symm ((1 - (1 : ℝ)) • A u + (1 : ℝ) • B u) = β u
    simpa only [sub_self, zero_smul, one_smul, zero_add] using φ.left_inv (hβ u).1
  · intro t u hu
    have hab : A u = B u := by
      rcases hu with hu | hu
      · subst u
        change φ (α 0) = φ (β 0)
        rw [α.source, β.source]
      · subst u
        change φ (α 1) = φ (β 1)
        rw [α.target, β.target]
    change φ.symm ((1 - (t : ℝ)) • A u + (t : ℝ) • B u) = α u
    rw [← hab, ← add_smul, sub_add_cancel, one_smul]
    exact φ.left_inv (hα u).1

/-- Casting the vertices of a finite concatenation casts its two outer endpoints. -/
theorem s25s_concat_cast {N : ℕ} (x y : Fin (N + 1) → S)
    (h : ∀ j, y j = x j)
    (σ : ∀ i : Fin N, Path (x i.castSucc) (x i.succ)) :
    Path.concat y (fun i => (σ i).cast (h i.castSucc) (h i.succ)) =
      (Path.concat x σ).cast (h 0) (h (Fin.last N)) := by
  have he : y = x := funext h
  subst y
  simp only [Path.cast_rfl_rfl]

/-- Concatenating the subpaths at a finite list of times recovers the outer subpath,
with explicitly identified vertices. No monotonicity is needed for this class identity. -/
theorem s25s_concat_subpath_class {N : ℕ} {a b : S} (γ : Path a b)
    (t : Fin (N + 1) → unitInterval) (x : Fin (N + 1) → S)
    (hv : ∀ j, x j = γ (t j)) :
    (Path.concat x (fun i => (γ.subpath (t i.castSucc) (t i.succ)).cast
      (hv i.castSucc) (hv i.succ))).Homotopic
      ((γ.subpath (t 0) (t (Fin.last N))).cast (hv 0) (hv (Fin.last N))) := by
  rw [s25s_concat_cast (γ ∘ t) x hv]
  exact (Path.Homotopic.concat_subpath γ t).pathCast (hv 0) (hv (Fin.last N))

/-- A subpath on an ordered interval inherits a range containment for the extended path. -/
theorem s25s_subpath_mem {a b : S} (γ : Path a b) {s t : unitInterval}
    (hst : s ≤ t) {D : Set S} (hD : γ.extend '' Icc (s : ℝ) (t : ℝ) ⊆ D) :
    ∀ u, γ.subpath s t u ∈ D := by
  intro u
  have hu : γ.subpath s t u ∈ range (γ.subpath s t) := ⟨u, rfl⟩
  rw [Path.range_subpath_of_le γ s t hst] at hu
  rcases hu with ⟨v, hv, he⟩
  apply hD
  refine ⟨v, ⟨hv.1, hv.2⟩, ?_⟩
  rw [Path.extend_apply γ v.2]
  exact he

/-- Proposed chartwise homotopy bridge: paths through the same vertices, with each paired
segment contained in the same convex chart disc, are homotopic with endpoints fixed.
The parameter grids may differ; existing path reparametrization homotopy is sufficient. -/
theorem s25s_polygon_homotopy {N : ℕ} (hN : 0 < N)
    (c : Fin N → S) (r : Fin N → ℝ)
    (hr : ∀ i, ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target)
    {a b : S} (α β : Path a b) (τ η : Fin (N + 1) → ℝ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last N) = 1) (hτ : StrictMono τ)
    (hη0 : η 0 = 0) (hη1 : η (Fin.last N) = 1) (hη : StrictMono η)
    (hv : ∀ j, α.extend (τ j) = β.extend (η j))
    (hα : ∀ i : Fin N, α.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆
      (chartAt ℂ (c i)).source ∩ chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))
    (hβ : ∀ i : Fin N, β.extend '' Icc (η i.castSucc) (η i.succ) ⊆
      (chartAt ℂ (c i)).source ∩ chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) :
    β.Homotopic α := by
  classical
  -- Positivity is retained from the frozen contract; the concat argument also allows N = 0.
  have _hN := hN
  have htmem : ∀ j, τ j ∈ Icc (0 : ℝ) 1 := by
    intro j
    constructor
    · rw [← hτ0]
      exact hτ.monotone (Fin.zero_le j)
    · rw [← hτ1]
      exact hτ.monotone (Fin.le_last j)
  have humem : ∀ j, η j ∈ Icc (0 : ℝ) 1 := by
    intro j
    constructor
    · rw [← hη0]
      exact hη.monotone (Fin.zero_le j)
    · rw [← hη1]
      exact hη.monotone (Fin.le_last j)
  let t : Fin (N + 1) → unitInterval := fun j => ⟨τ j, htmem j⟩
  let u : Fin (N + 1) → unitInterval := fun j => ⟨η j, humem j⟩
  have ht0 : t 0 = 0 := Subtype.ext hτ0
  have ht1 : t (Fin.last N) = 1 := Subtype.ext hτ1
  have hu0 : u 0 = 0 := Subtype.ext hη0
  have hu1 : u (Fin.last N) = 1 := Subtype.ext hη1
  have hv' : ∀ j, α (t j) = β (u j) := by
    intro j
    simpa only [t, u, Path.extend_apply α (htmem j),
      Path.extend_apply β (humem j)] using hv j
  let x : Fin (N + 1) → S := fun j => α (t j)
  let A : ∀ i : Fin N, Path (x i.castSucc) (x i.succ) :=
    fun i => α.subpath (t i.castSucc) (t i.succ)
  let B : ∀ i : Fin N, Path (x i.castSucc) (x i.succ) := fun i =>
    (β.subpath (u i.castSucc) (u i.succ)).cast (hv' i.castSucc) (hv' i.succ)
  have hedge : ∀ i, (B i).Homotopic (A i) := by
    intro i
    apply s25s_disc_homotopic (c i) (hr i)
    · exact s25s_subpath_mem β (hη.monotone i.castSucc_le_succ) (hβ i)
    · exact s25s_subpath_mem α (hτ.monotone i.castSucc_le_succ) (hα i)
  have hB := s25s_concat_subpath_class β u x hv'
  have hA := Path.Homotopic.concat_subpath α t
  have H := hB.symm.trans ((Path.Homotopic.concat_hcomp x B A hedge).trans hA)
  change Nonempty (ContinuousMap.HomotopyRel
    (β.subpath (u 0) (u (Fin.last N))).toContinuousMap
    (α.subpath (t 0) (t (Fin.last N))).toContinuousMap {0, 1}) at H
  rw [ht0, ht1, hu0, hu1, Path.subpath_zero_one, Path.subpath_zero_one] at H
  exact H


/-- The earlier plane cone-potential estimate gives finite model distance, independently
of the later compact local-block contract. -/
theorem s25s_model_distance_lt_top (m : ℕ) (a b : ℂ) :
    metricDist univ (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) a b < ⊤ := by
  classical
  let R : ℝ := ‖a‖ + ‖b‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have ha : a ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    linarith [norm_nonneg b]
  have hb : b ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    linarith [norm_nonneg a]
  obtain ⟨G, hG, hGa, hGb0, hGb, γ, hγ, hlen⟩ := s25e_cone_potential m hR ha hb
  have hpath : IsPathIn univ a b γ :=
    ⟨hγ.1, hγ.2.1, hγ.2.2.1, subset_univ _⟩
  have hdist : metricDist univ
      (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) a b ≤
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) γ := by
    exact iInf₂_le γ hpath
  exact lt_of_le_of_lt (hdist.trans hlen) ENNReal.ofReal_lt_top

/-- An open preferred-chart neighborhood admits finite-length paths in its chart disc.
Finiteness comes from the earlier model upper bound; local minimizers supply containment. -/
theorem s25s_local_finite_chart [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ (r : ℝ) (U : Set S), 0 < r ∧
      ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r ∧
      ∀ a ∈ U, ∀ b ∈ U, ∃ σ : Path a b,
        (∀ t, σ t ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) ∧
        phiLengthPath q σ < ⊤ := by
  classical
  obtain ⟨r, hr, hrt, V, hV, hVD, hmin⟩ := s25i_local hq hne p
  obtain ⟨m, ζ, hζ, hζ0, hζd, hζq⟩ := s25e_natural_chart hq hne p
  obtain ⟨W, hW, hWV, hup⟩ :=
    s25e_surface_upper hq hne p m ζ hζ hζ0 hζd hζq V hV
  obtain ⟨U, hUW, hU, hpU⟩ := mem_nhds_iff.1 hW
  refine ⟨r, U, hr, hrt, hU, hpU, hUW.trans hWV |>.trans hVD, ?_⟩
  intro a ha b hb
  obtain ⟨η, hηW, hηlen⟩ := hup a (hUW ha) b (hUW hb)
  have hfin : phiLengthPath q η < ⊤ :=
    lt_of_le_of_lt hηlen (s25s_model_distance_lt_top m _ _)
  obtain ⟨σ, hσD, hσlen⟩ := hmin a (hWV (hUW ha)) b (hWV (hUW hb))
  refine ⟨σ, hσD, ?_⟩
  rw [hσlen]
  exact lt_of_le_of_lt (iInf_le _ η) hfin

/- UNCOMPILED ARCHIVE DRAFT. Assembly splits early distance helpers from radial shrink.
No verification is claimed. Unresolved validation obligations are catalogued in REPORT.md. -/

/-- The distance infimum is bounded by any specified path. -/
theorem s25s_dist_le_length {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) :
    phiDistRS q a b ≤ phiLengthPath q γ := by
  exact iInf_le (fun δ : Path a b => phiLengthPath q δ) γ

/-- Concatenation gives the triangle inequality without requiring symmetry. -/
theorem s25s_dist_triangle {q : S → ℂ → ℂ} (a b c : S) :
    phiDistRS q a c ≤ phiDistRS q a b + phiDistRS q b c := by
  classical
  unfold phiDistRS
  rw [ENNReal.iInf_add]
  refine le_iInf fun α => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun β => ?_
  exact (iInf_le _ (α.trans β)).trans (s25s_length_trans_le α β)

/-- A bounded density in a convex preferred-chart ball gives ordered short connectors. -/
theorem s25s_chart_connector {q : S → ℂ → ℂ} (p : S) {r C : ℝ}
    (hball : ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target)
    (hρ : ∀ z ∈ ball (chartAt ℂ p p) r, Real.sqrt ‖q p z‖ ≤ C)
    {a b : S}
    (ha : a ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r)
    (hb : b ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) :
    ∃ γ : Path a b,
      phiLengthPath q γ ≤ ENNReal.ofReal (C * dist (chartAt ℂ p a) (chartAt ℂ p b)) := by
  classical
  let A := chartAt ℂ p a
  let B := chartAt ℂ p b
  let f : ℝ → ℂ := AffineMap.lineMap A B
  have hfball : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ ball (chartAt ℂ p p) r :=
    fun t ht => (convex_ball _ _).lineMap_mem ha.2 hb.2 ht
  have hfLip : LipschitzWith (nndist A B) f := lipschitzWith_lineMap A B
  have hfcont : ContinuousOn (fun t : ℝ => (chartAt ℂ p).symm (f t)) (Icc 0 1) :=
    (chartAt ℂ p).continuousOn_symm.comp hfLip.continuous.continuousOn
      (fun t ht => hball (hfball t ht))
  let γ : Path a b :=
    ⟨⟨fun t : unitInterval => (chartAt ℂ p).symm (f t),
      hfcont.comp_continuous continuous_subtype_val (fun t => t.2)⟩,
      by simpa [f, A] using (chartAt ℂ p).left_inv ha.1,
      by simpa [f, B] using (chartAt ℂ p).left_inv hb.1⟩
  have hγext : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.extend t = (chartAt ℂ p).symm (f t) := by
    intro t ht
    rw [Path.extend_apply γ ht]
    rfl
  have hφγ : ∀ t ∈ Icc (0 : ℝ) 1, chartAt ℂ p (γ.extend t) = f t := by
    intro t ht
    rw [hγext t ht]
    exact (chartAt ℂ p).right_inv (hball (hfball t ht))
  have hsrc : γ.extend '' Icc (0 : ℝ) 1 ⊆ (chartAt ℂ p).source := by
    rintro x ⟨t, ht, rfl⟩
    rw [hγext t ht]
    exact (chartAt ℂ p).map_target (hball (hfball t ht))
  have hlip : ∃ K : ℝ≥0,
      LipschitzOnWith K (fun t => chartAt ℂ p (γ.extend t)) (Icc (0 : ℝ) 1) := by
    refine ⟨nndist A B, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [hφγ x hx, hφγ y hy]
    exact hfLip.dist_le_mul x y
  refine ⟨γ, (s25e_len_le_piece γ p zero_le_one hsrc hlip).trans ?_⟩
  calc
    (∫⁻ u in Ioo (0 : ℝ) 1,
      phiDensity (q p) (chartAt ℂ p (γ.extend u)) *
        ‖deriv (fun v => chartAt ℂ p (γ.extend v)) u‖ₑ) ≤
        ∫⁻ _u in Ioo (0 : ℝ) 1, ENNReal.ofReal (C * dist A B) := by
      refine setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
      have huI := Ioo_subset_Icc_self hu
      have hev : (fun v => chartAt ℂ p (γ.extend v)) =ᶠ[𝓝 u] f := by
        filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv using hφγ v hv
      have hd : deriv f u = B - A := AffineMap.hasDerivAt_lineMap.deriv
      rw [hev.deriv_eq, hd, hφγ u huI]
      change ENNReal.ofReal (Real.sqrt ‖q p (f u)‖) * ‖B - A‖ₑ ≤ _
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      simpa [dist_eq_norm, norm_sub_rev] using
        mul_le_mul_of_nonneg_right (hρ (f u) (hfball u huI)) (norm_nonneg (B - A))
    _ = ENNReal.ofReal (C * dist A B) := by
      rw [setLIntegral_const, Real.volume_Ioo]
      simp

/-- Choose one chart neighborhood and one density bound for all ordered endpoint pairs. -/
theorem s25s_chart_upper [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) :
    ∃ W ∈ 𝓝 p, W ⊆ (chartAt ℂ p).source ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ W, ∀ b ∈ W,
        phiDistRS q a b ≤ ENNReal.ofReal
          (C * dist (chartAt ℂ p a) (chartAt ℂ p b)) := by
  have hq' : IsDiffFamily 2 0 q ∧
      ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  let z₀ := chartAt ℂ p p
  have hz₀ : z₀ ∈ (chartAt ℂ p).target :=
    (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 (chartAt ℂ p).open_target z₀ hz₀
  have hclosed : closedBall z₀ (r / 2) ⊆ (chartAt ℂ p).target := by
    intro z hz
    apply hrt
    apply mem_ball.mpr
    exact (mem_closedBall.1 hz).trans_lt (by linarith)
  have hρcont : ContinuousOn (fun z : ℂ => Real.sqrt ‖q p z‖)
      (closedBall z₀ (r / 2)) :=
    ((hq'.2 p).continuousOn.norm.sqrt).mono hclosed
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn hρcont
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hρ : ∀ z ∈ ball z₀ (r / 2), Real.sqrt ‖q p z‖ ≤ C := by
    intro z hz
    have h := hM z (ball_subset_closedBall hz)
    have h' : Real.sqrt ‖q p z‖ ≤ M := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h
    exact h'.trans (le_max_left _ _)
  let W := (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball z₀ (r / 2)
  have hWo : IsOpen W :=
    (chartAt ℂ p).continuousOn.isOpen_inter_preimage (chartAt ℂ p).open_source isOpen_ball
  have hpW : p ∈ W := ⟨mem_chart_source ℂ p, mem_ball_self (by positivity)⟩
  refine ⟨W, hWo.mem_nhds hpW, fun x hx => hx.1, C, hC, ?_⟩
  intro a ha b hb
  obtain ⟨γ, hγ⟩ := s25s_chart_connector p
    (ball_subset_closedBall.trans hclosed) hρ ha hb
  exact (s25s_dist_le_length γ).trans hγ

/-- Convert triangle to real values only after checking the two summands are finite. -/
theorem s25s_dist_toReal_triangle {q : S → ℂ → ℂ} (a b c : S)
    (hab : phiDistRS q a b < ⊤) (hbc : phiDistRS q b c < ⊤) :
    (phiDistRS q a c).toReal ≤ (phiDistRS q a b).toReal +
      (phiDistRS q b c).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hab.ne, hbc.ne⟩) (s25s_dist_triangle (q := q) a b c)
  rwa [ENNReal.toReal_add hab.ne hbc.ne] at h

/-- Ordered connectors in both directions control the oscillation of distance. -/
theorem s25s_dist_oscillation {q : S → ℂ → ℂ} (p : S) {W : Set S} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ a ∈ W, ∀ b ∈ W,
      phiDistRS q a b ≤ ENNReal.ofReal (C * dist (chartAt ℂ p a) (chartAt ℂ p b)))
    {a b a' b' : S} (ha : a ∈ W) (hb : b ∈ W) (ha' : a' ∈ W) (hb' : b' ∈ W) :
    |(phiDistRS q a b).toReal - (phiDistRS q a' b').toReal| ≤
      C * (dist (chartAt ℂ p a) (chartAt ℂ p a') +
        dist (chartAt ℂ p b) (chartAt ℂ p b')) := by
  have hfin : ∀ x ∈ W, ∀ y ∈ W, phiDistRS q x y < ⊤ :=
    fun x hx y hy => (hbound x hx y hy).trans_lt ENNReal.ofReal_lt_top
  have hreal : ∀ x ∈ W, ∀ y ∈ W,
      (phiDistRS q x y).toReal ≤ C * dist (chartAt ℂ p x) (chartAt ℂ p y) := by
    intro x hx y hy
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound x hx y hy)
    rwa [ENNReal.toReal_ofReal (mul_nonneg hC dist_nonneg)] at h
  have hchain : ∀ x ∈ W, ∀ y ∈ W, ∀ u ∈ W, ∀ v ∈ W,
      (phiDistRS q x y).toReal ≤ (phiDistRS q u v).toReal +
        C * (dist (chartAt ℂ p x) (chartAt ℂ p u) +
          dist (chartAt ℂ p y) (chartAt ℂ p v)) := by
    intro x hx y hy u hu v hv
    have h₁ := s25s_dist_toReal_triangle (q := q) x u y (hfin x hx u hu) (hfin u hu y hy)
    have h₂ := s25s_dist_toReal_triangle (q := q) u v y (hfin u hu v hv) (hfin v hv y hy)
    have h₃ := hreal x hx u hu
    have h₄ := hreal v hv y hy
    rw [dist_comm (chartAt ℂ p v) (chartAt ℂ p y)] at h₄
    nlinarith
  have h₁ := hchain a ha b hb a' ha' b' hb'
  have h₂ := hchain a' ha' b' hb' a ha b hb
  rw [dist_comm (chartAt ℂ p a') (chartAt ℂ p a),
    dist_comm (chartAt ℂ p b') (chartAt ℂ p b)] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Local finite continuous distance, obtained using ordered short connectors. -/
theorem s25s_distance_local_control [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (p : S) :
    ∃ W ∈ 𝓝 p,
      ContinuousOn (fun z : S × S => phiDistRS q z.1 z.2) (W ×ˢ W) ∧
      ∀ a ∈ W, ∀ b ∈ W, phiDistRS q a b < ⊤ := by
  obtain ⟨W, hW, hsrc, C, hC, hbound⟩ := s25s_chart_upper hq p
  have hfin : ∀ a ∈ W, ∀ b ∈ W, phiDistRS q a b < ⊤ :=
    fun a ha b hb => (hbound a ha b hb).trans_lt ENNReal.ofReal_lt_top
  have hφ₁ : ContinuousOn (fun z : S × S => chartAt ℂ p z.1) (W ×ˢ W) :=
    (chartAt ℂ p).continuousOn.comp continuous_fst.continuousOn (fun z hz => hsrc hz.1)
  have hφ₂ : ContinuousOn (fun z : S × S => chartAt ℂ p z.2) (W ×ˢ W) :=
    (chartAt ℂ p).continuousOn.comp continuous_snd.continuousOn (fun z hz => hsrc hz.2)
  have hreal : ContinuousOn (fun z : S × S => (phiDistRS q z.1 z.2).toReal) (W ×ˢ W) := by
    intro x hx
    apply Metric.continuousWithinAt_iff'.mpr
    intro ε hε
    have hcost : ContinuousWithinAt (fun z : S × S =>
        C * (dist (chartAt ℂ p z.1) (chartAt ℂ p x.1) +
          dist (chartAt ℂ p z.2) (chartAt ℂ p x.2))) (W ×ˢ W) x :=
      continuousWithinAt_const.mul (((hφ₁ x hx).dist continuousWithinAt_const).add
        ((hφ₂ x hx).dist continuousWithinAt_const))
    have hsmall : ∀ᶠ z in 𝓝[W ×ˢ W] x,
        C * (dist (chartAt ℂ p z.1) (chartAt ℂ p x.1) +
          dist (chartAt ℂ p z.2) (chartAt ℂ p x.2)) < ε :=
      hcost.tendsto.eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hsmallz
    rw [Real.dist_eq]
    exact (s25s_dist_oscillation p hC hbound hz.1 hz.2 hx.1 hx.2).trans_lt hsmallz
  refine ⟨W, hW, ?_, hfin⟩
  have hcont := ENNReal.continuous_ofReal.comp_continuousOn hreal
  refine hcont.congr ?_
  intro z hz
  exact (ENNReal.ofReal_toReal (hfin z.1 hz.1 z.2 hz.2).ne).symm

/-- Proposed topological bridge: every fixed-endpoint class has a finite-length representative.
Subdivide a continuous path into chart discs, replace the pieces by installed local minimizers,
then concatenate. The original path need not have an admissible Lipschitz partition. -/
theorem s25s_finite_rep [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (α : Path a b) :
    ∃ β : Path a b, β.Homotopic α ∧ phiLengthPath q β < ⊤ := by
  classical
  have hlocal : ∀ p : S, ∃ (r : ℝ) (U : Set S), 0 < r ∧
      ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r ∧
      ∀ a ∈ U, ∀ b ∈ U, ∃ σ : Path a b,
        (∀ t, σ t ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) ∧
        phiLengthPath q σ < ⊤ := fun p => s25s_local_finite_chart hq hne p
  choose r U hr hrt hU hpU hUD hfinite using hlocal
  let C : S → Set unitInterval := fun p => α ⁻¹' U p
  have hC : ∀ p, IsOpen (C p) := fun p => (hU p).preimage α.continuous
  have hcover : (univ : Set unitInterval) ⊆ ⋃ p, C p := by
    intro t _
    exact mem_iUnion.mpr ⟨α t, hpU (α t)⟩
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hC hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsmall : 1 / (N : ℝ) < δ := by simpa [N] using hn
  let τ : Fin (N + 1) → ℝ := fun j => (j.val : ℝ) / (N : ℝ)
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτ1 : τ (Fin.last N) = 1 := by simp [τ, hNR.ne']
  have hτ : StrictMono τ := by
    intro i j hij
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) hNR
  have hτI : ∀ j, τ j ∈ Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨div_nonneg (Nat.cast_nonneg _) hNR.le, (div_le_one hNR).2 ?_⟩
    exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hsegment : ∀ i : Fin N, ∃ p : S,
      α.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ U p := by
    intro i
    let t₀ : unitInterval := ⟨τ i.castSucc, hτI i.castSucc⟩
    obtain ⟨p, hp⟩ := hLeb t₀ (mem_univ _)
    refine ⟨p, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 :=
      ⟨(hτI i.castSucc).1.trans ht.1, ht.2.trans (hτI i.succ).2⟩
    have hwidth : τ i.succ - τ i.castSucc = 1 / (N : ℝ) := by
      dsimp [τ]
      push_cast
      ring
    have hball : (⟨t, htI⟩ : unitInterval) ∈ ball t₀ δ := by
      rw [mem_ball]
      change |t - τ i.castSucc| < δ
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact ((sub_le_sub_right ht.2 _).trans_eq hwidth).trans_lt hsmall
    rw [Path.extend_apply α htI]
    exact hp hball
  choose c hsegment using hsegment
  let x : Fin (N + 1) → S := fun j => α.extend (τ j)
  have hx0 : x 0 = a := by simp [x, hτ0, Path.extend_zero]
  have hx1 : x (Fin.last N) = b := by simp [x, hτ1, Path.extend_one]
  have hedge : ∀ i : Fin N, ∃ σ : Path (x i.castSucc) (x i.succ),
      (∀ u, σ u ∈ (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r (c i))) ∧
      phiLengthPath q σ < ⊤ := by
    intro i
    have htimes : τ i.castSucc ≤ τ i.succ := hτ.monotone (Fin.castSucc_le_succ i)
    have hleft : x i.castSucc ∈ U (c i) :=
      hsegment i ⟨τ i.castSucc, ⟨le_rfl, htimes⟩, rfl⟩
    have hright : x i.succ ∈ U (c i) :=
      hsegment i ⟨τ i.succ, ⟨htimes, le_rfl⟩, rfl⟩
    exact hfinite (c i) _ hleft _ hright
  choose σ hσD hσfin using hedge
  obtain ⟨γ, hγv, hγtrace, hγlen⟩ := s25s_glue_path (q := q) hN x σ
  let β : Path a b := γ.cast hx0.symm hx1.symm
  have hβextend : β.extend = γ.extend := Path.extend_cast γ hx0.symm hx1.symm
  have hβlen : phiLengthPath q β = phiLengthPath q γ := rfl
  have hαD : ∀ i : Fin N, α.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆
      (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r (c i)) :=
    fun i => (hsegment i).trans (hUD (c i))
  have hβD : ∀ i : Fin N, β.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆
      (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r (c i)) := by
    intro i
    rw [hβextend]
    have hgrid : Icc (τ i.castSucc) (τ i.succ) =
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) := by
      simp [τ]
    rw [hgrid]
    refine (hγtrace i).trans ?_
    rintro _ ⟨u, rfl⟩
    exact hσD i u
  have hv : ∀ j, α.extend (τ j) = β.extend (τ j) := by
    intro j
    rw [hβextend]
    exact (hγv j).symm
  have hclass : β.Homotopic α := s25s_polygon_homotopy hN c (fun i => r (c i))
    (fun i => hrt (c i)) α β τ τ hτ0 hτ1 hτ hτ0 hτ1 hτ hv hαD hβD
  refine ⟨β, hclass, ?_⟩
  rw [hβlen]
  refine lt_of_le_of_lt hγlen ?_
  exact ENNReal.sum_lt_top.2 (fun i _ => hσfin i)


/-- Shrink a natural-coordinate disc inside any prescribed neighborhood.
The exit inequality applies the installed radial potential to an extracted subpath. -/
theorem s25s_radial_compact_shrink [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S)
    {V : Set S} (hV : V ∈ 𝓝 p) :
    ∃ (U K : Set S) (ε : ℝ≥0∞),
      IsOpen U ∧ p ∈ U ∧ U ⊆ interior K ∧ IsCompact K ∧ K ⊆ V ∧
      0 < ε ∧ ε < ⊤ ∧
      (∀ {a b : S} (γ : Path a b) {s t : ℝ},
        0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U →
        γ.extend '' Icc s t ⊆ K → γ.extend t ∈ frontier K →
        ε ≤ phiLengthOn q γ s t) := by
  classical
  obtain ⟨m, ζ, hζ, hζ0, hζd, hζq⟩ := s25e_natural_chart hq hne p
  obtain ⟨r₀, hr₀, hsub, han, hinj⟩ :=
    s25e_local_chart hq p m ζ hζ hζ0 hζd hζq
  let z₀ := chartAt ℂ p p
  have han' : ∀ z ∈ closedBall z₀ r₀, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 :=
    fun z hz => ⟨(han z hz).1, (han z hz).2.1⟩
  obtain ⟨hopen, hψ⟩ := psa_inverse hr₀ hinj han'
  let ψ : ℂ → ℂ := Function.invFunOn ζ (ball z₀ r₀)
  let Ω : Set ℂ := ζ '' ball z₀ r₀
  have h0Ω : (0 : ℂ) ∈ Ω := ⟨z₀, mem_ball_self hr₀, hζ0⟩
  have hψl : ∀ z ∈ ball z₀ r₀, ψ (ζ z) = z := fun z hz =>
    hinj (ball_subset_closedBall (hψ (ζ z) ⟨z, hz, rfl⟩).1)
      (ball_subset_closedBall hz) (hψ (ζ z) ⟨z, hz, rfl⟩).2.1
  have hψ0 : ψ 0 = z₀ := by
    have h := hψl z₀ (mem_ball_self hr₀)
    rwa [hζ0] at h
  have hψcont : ContinuousOn ψ Ω :=
    fun w hw => (hψ w hw).2.2.continuousAt.continuousWithinAt
  let χ : ℂ → S := fun w => (chartAt ℂ p).symm (ψ w)
  have hχ0 : χ 0 = p := by
    change (chartAt ℂ p).symm (ψ 0) = p
    rw [hψ0]
    exact (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hχcont : ContinuousOn χ Ω :=
    (chartAt ℂ p).continuousOn_symm.comp hψcont
      (fun w hw => hsub (ball_subset_closedBall (hψ w hw).1))
  have hχc : ContinuousAt χ 0 := hχcont.continuousAt (hopen.mem_nhds h0Ω)
  have hφχ : ∀ w ∈ Ω, chartAt ℂ p (χ w) = ψ w := fun w hw =>
    (chartAt ℂ p).right_inv (hsub (ball_subset_closedBall (hψ w hw).1))
  have hχsrc : ∀ w ∈ Ω, χ w ∈ (chartAt ℂ p).source := fun w hw =>
    (chartAt ℂ p).map_target (hsub (ball_subset_closedBall (hψ w hw).1))
  obtain ⟨ρ₁, hρ₁, hρ₁Ω⟩ := Metric.isOpen_iff.1 hopen 0 h0Ω
  obtain ⟨ρ₂, hρ₂, hρ₂V⟩ := Metric.mem_nhds_iff.1
    (hχc.preimage_mem_nhds (by rw [hχ0]; exact hV))
  let R : ℝ := min ρ₁ ρ₂ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < ρ₁ := by
    have := min_le_left ρ₁ ρ₂
    dsimp [R]
    linarith [lt_min hρ₁ hρ₂]
  have hR2 : R < ρ₂ := by
    have := min_le_right ρ₁ ρ₂
    dsimp [R]
    linarith [lt_min hρ₁ hρ₂]
  have hKΩ : closedBall (0 : ℂ) R ⊆ Ω := fun w hw =>
    hρ₁Ω (mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hw).trans_lt hR1))
  let K : Set S := χ '' closedBall (0 : ℂ) R
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (hχcont.mono hKΩ)
  have hKV : K ⊆ V := by
    rintro x ⟨w, hw, rfl⟩
    exact hρ₂V (mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hw).trans_lt hR2))
  have hKo : ∀ ρ : ℝ, IsOpen
      ((chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹'
        (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) ρ)) := by
    intro ρ
    refine (chartAt ℂ p).continuousOn.isOpen_inter_preimage
      (chartAt ℂ p).open_source ?_
    have hζc : ContinuousOn ζ (ball z₀ r₀) := fun z hz =>
      (han z (ball_subset_closedBall hz)).1.continuousAt.continuousWithinAt
    exact hζc.isOpen_inter_preimage isOpen_ball isOpen_ball
  let O : Set S := (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹'
    (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) R)
  let U : Set S := (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹'
    (ball z₀ r₀ ∩ ζ ⁻¹' ball (0 : ℂ) (R / 2))
  have hO : IsOpen O := hKo R
  have hU : IsOpen U := hKo (R / 2)
  have hpU : p ∈ U := ⟨mem_chart_source ℂ p, mem_ball_self hr₀, by
    rw [mem_preimage, hζ0]
    exact mem_ball_self (by positivity)⟩
  have hOK : O ⊆ K := by
    intro x hx
    refine ⟨ζ (chartAt ℂ p x),
      mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 hx.2.2).le, ?_⟩
    change (chartAt ℂ p).symm (ψ (ζ (chartAt ℂ p x))) = x
    rw [hψl _ hx.2.1]
    exact (chartAt ℂ p).left_inv hx.1
  have hUO : U ⊆ O := by
    intro x hx
    refine ⟨hx.1, hx.2.1, mem_ball_zero_iff.2 ?_⟩
    have := mem_ball_zero_iff.1 hx.2.2
    linarith
  have hUK : U ⊆ interior K := hUO.trans (hO.subset_interior_iff.mpr hOK)
  have hKchart : ∀ x ∈ K, x ∈ (chartAt ℂ p).source ∧
      chartAt ℂ p x ∈ ball z₀ r₀ ∧ ‖ζ (chartAt ℂ p x)‖ ≤ R := by
    rintro x ⟨w, hw, rfl⟩
    have hwΩ := hKΩ hw
    refine ⟨hχsrc w hwΩ, ?_, ?_⟩
    · rw [hφχ w hwΩ]
      exact (hψ w hwΩ).1
    · rw [hφχ w hwΩ, (hψ w hwΩ).2.1]
      exact mem_closedBall_zero_iff.1 hw
  have hfront : ∀ x ∈ frontier K, ‖ζ (chartAt ℂ p x)‖ = R := by
    intro x hx
    have hxK : x ∈ K := hK.isClosed.closure_eq ▸ frontier_subset_closure hx
    have hxchart := hKchart x hxK
    refine le_antisymm hxchart.2.2 ?_
    by_contra hn
    have hn' : ‖ζ (chartAt ℂ p x)‖ < R := lt_of_not_ge hn
    have hxO : x ∈ O := ⟨hxchart.1, hxchart.2.1, mem_ball_zero_iff.2 hn'⟩
    have hxi : x ∈ interior K := (hO.subset_interior_iff.mpr hOK) hxO
    exact (mem_frontier_iff_notMem_interior hxK).mp hx hxi
  let c : ℝ := ((m : ℝ) + 2) / 2
  let ε : ℝ≥0∞ := ENNReal.ofReal (R ^ c - (R / 2) ^ c)
  have hc : 0 < c := by dsimp [c]; positivity
  have hgap : 0 < R ^ c - (R / 2) ^ c := by
    exact sub_pos.mpr (Real.rpow_lt_rpow (by positivity) (by linarith) hc)
  refine ⟨U, K, ε, hU, hpU, hUK, hK, hKV,
    ENNReal.ofReal_pos.mpr hgap, ENNReal.ofReal_lt_top, ?_⟩
  intro a b γ s t hs hst ht ha htrace hb
  obtain ⟨β, hβtrace, hβlen⟩ := s25i_subpath_length γ hs hst ht
  have hβsrc : ∀ v ∈ Icc (0 : ℝ) 1,
      β.extend v ∈ (chartAt ℂ p).source ∧
      chartAt ℂ p (β.extend v) ∈ ball z₀ r₀ := by
    intro v hv
    rw [Path.extend_apply β hv]
    have h := hKchart _ (htrace (hβtrace ⟨v, hv⟩))
    exact ⟨h.1, h.2.1⟩
  have hrad := s25e_partition_lower hq p m ζ hr₀ han hinj
    (G := fun w : ℂ => ‖w‖ ^ c) (s25e_radial_hG m)
    β (τs := 1) ⟨zero_le_one, le_rfl⟩ hβsrc
  rw [Path.extend_one, Path.extend_zero, hfront _ hb] at hrad
  have hstart : ‖ζ (chartAt ℂ p (γ.extend s))‖ ^ c ≤ (R / 2) ^ c :=
    Real.rpow_le_rpow (norm_nonneg _) (mem_ball_zero_iff.1 ha.2.2).le hc.le
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left hstart (R ^ c))).trans
    (hrad.trans hβlen)

/-- Proposed local block: an open inner set around p lies in a compact set K, itself
inside a convex chart disc. Local distance on K is finite, continuous, and realized inside
the disc. A path starting in the inner set and reaching the frontier of K while staying
in K pays a strictly positive exit cost. Use the installed natural-coordinate radial potential. -/
theorem s25s_local_compact_block [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ (r : ℝ) (U K : Set S) (ε : ℝ≥0∞),
      0 < r ∧ ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ interior K ∧ IsCompact K ∧
      K ⊆ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r ∧
      0 < ε ∧ ε < ⊤ ∧
      ContinuousOn (fun z : S × S => phiDistRS q z.1 z.2) (K ×ˢ K) ∧
      (∀ a ∈ K, ∀ b ∈ K, phiDistRS q a b < ⊤ ∧
        ∃ σ : Path a b,
          (∀ u, σ u ∈ (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) r) ∧
          phiLengthPath q σ = phiDistRS q a b) ∧
      (∀ {a b : S} (γ : Path a b) {s t : ℝ},
        0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U →
        γ.extend '' Icc s t ⊆ K → γ.extend t ∈ frontier K →
        ε ≤ phiLengthOn q γ s t) := by
  classical
  obtain ⟨r, hr, hrt, V, hV, hVD, hmin⟩ := s25i_local hq hne p
  obtain ⟨W, hW, hcont, hfin⟩ := s25s_distance_local_control hq p
  obtain ⟨U, K, ε, hU, hpU, hUK, hK, hKV, hε, hεfin, hexit⟩ :=
    s25s_radial_compact_shrink hq hne p (inter_mem hV hW)
  refine ⟨r, U, K, ε, hr, hrt, hU, hpU, hUK, hK, ?_, hε, hεfin, ?_, ?_, hexit⟩
  · exact fun x hx => hVD (hKV hx).1
  · exact hcont.mono (fun z hz => ⟨(hKV hz.1).2, (hKV hz.2).2⟩)
  · intro a ha b hb
    exact ⟨hfin a (hKV ha).2 b (hKV hb).2,
      hmin a (hKV ha).1 b (hKV hb).1⟩


/-- Proposed finite cover: compactness selects finitely many local blocks, and the minimum
of their positive exit costs is a uniform positive exit cost. The inner open sets cover S. -/
theorem s25s_uniform_cover [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    ∃ (n : ℕ) (c : Fin n → S) (r : Fin n → ℝ) (U K : Fin n → Set S)
      (ε : ℝ≥0∞), 0 < ε ∧ ε < ⊤ ∧
      (∀ p : S, ∃ i : Fin n, p ∈ U i) ∧
      (∀ i : Fin n, 0 < r i ∧
        ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target ∧
        IsOpen (U i) ∧ U i ⊆ interior (K i) ∧ IsCompact (K i) ∧
        K i ⊆ (chartAt ℂ (c i)).source ∩
          chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) ∧
        ContinuousOn (fun z : S × S => phiDistRS q z.1 z.2) ((K i) ×ˢ (K i)) ∧
        (∀ a ∈ K i, ∀ b ∈ K i, phiDistRS q a b < ⊤ ∧
          ∃ σ : Path a b,
            (∀ u, σ u ∈ (chartAt ℂ (c i)).source ∩
              chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) ∧
            phiLengthPath q σ = phiDistRS q a b) ∧
        (∀ {a b : S} (γ : Path a b) {s t : ℝ},
          0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U i →
          γ.extend '' Icc s t ⊆ K i → γ.extend t ∈ frontier (K i) →
          ε ≤ phiLengthOn q γ s t)) := by
  classical
  choose r₀ U₀ K₀ ε₀ h₀ using fun p : S => s25s_local_compact_block hq hne p
  have hopen : ∀ p : S, IsOpen (U₀ p) := by
    intro p
    rcases h₀ p with ⟨_, _, ho, _, _, _, _, _, _, _, _, _⟩
    exact ho
  have hcover₀ : (Set.univ : Set S) ⊆ ⋃ p : S, U₀ p := by
    intro p _
    rcases h₀ p with ⟨_, _, _, hp, _, _, _, _, _, _, _, _⟩
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U₀ hopen hcover₀
  have hTcover : ∀ x : S, ∃ p ∈ T, x ∈ U₀ p := by
    intro x
    rcases Set.mem_iUnion.mp (hT (Set.mem_univ x)) with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpT, hpx⟩
    exact ⟨p, hpT, hpx⟩
  have hTne : T.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    obtain ⟨p, hp, _⟩ := hTcover x
    exact ⟨p, hp⟩
  let C : Finset ℝ≥0∞ := T.image ε₀
  have hCne : C.Nonempty := Finset.image_nonempty.mpr hTne
  have hCpos : ∀ z ∈ C, 0 < z ∧ z < ⊤ := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, _, rfl⟩
    rcases h₀ p with ⟨_, _, _, _, _, _, _, he, hef, _, _, _⟩
    exact ⟨he, hef⟩
  let ε : ℝ≥0∞ := C.min' hCne
  have hε : 0 < ε ∧ ε < ⊤ := hCpos ε (Finset.min'_mem C hCne)
  let c : Fin T.card → S := fun i => (T.equivFin.symm i).val
  have hc : ∀ i : Fin T.card, c i ∈ T := fun i => (T.equivFin.symm i).property
  have hεle : ∀ i : Fin T.card, ε ≤ ε₀ (c i) := by
    intro i
    exact Finset.min'_le C (ε₀ (c i)) (Finset.mem_image.mpr ⟨c i, hc i, rfl⟩)
  refine ⟨T.card, c, (fun i => r₀ (c i)), (fun i => U₀ (c i)),
    (fun i => K₀ (c i)), ε, hε.1, hε.2, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, hx⟩ := hTcover x
    refine ⟨T.equivFin ⟨p, hp⟩, ?_⟩
    have hcp : c (T.equivFin ⟨p, hp⟩) = p := by
      change (T.equivFin.symm (T.equivFin ⟨p, hp⟩)).val = p
      rw [Equiv.symm_apply_apply]
    simpa only [hcp] using hx
  · intro i
    rcases h₀ (c i) with ⟨hr, hb, ho, _, hi, hk, hd, _, _, hcont, hshort, hex⟩
    refine ⟨hr, hb, ho, hi, hk, hd, hcont, hshort, ?_⟩
    intro a b γ s t hs hst ht hstart htrace hfront
    exact (hεle i).trans (hex γ hs hst ht hstart htrace hfront)


/-- First exit from an interior, including the closed endpoint trace. No regularity
of the path beyond continuity, or compactness of the closed set, is required. -/
theorem s25s_first_exit {a b : S} (γ : Path a b) (K : Set S) (hK : IsClosed K)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (hstart : γ.extend s ∈ interior K) :
    ∃ t : ℝ, s < t ∧ t ≤ 1 ∧ γ.extend '' Icc s t ⊆ K ∧
      (t = 1 ∨ γ.extend t ∈ frontier K) := by
  classical
  let E : Set ℝ := Icc s 1 ∩ γ.extend ⁻¹' (interior K)ᶜ
  have hEc : IsClosed E :=
    isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage γ.continuous_extend)
  by_cases hE : E.Nonempty
  · have hEb : BddBelow E := ⟨s, fun u hu => hu.1.1⟩
    let t : ℝ := sInf E
    have htE : t ∈ E := hEc.csInf_mem hE hEb
    have htI : t ∈ Icc s 1 := htE.1
    have hst : s < t := by
      rcases htI.1.eq_or_lt with h | h
      · exfalso
        apply htE.2
        simpa only [← h] using hstart
      · exact h
    have hbefore : ∀ u ∈ Ico s t, γ.extend u ∈ interior K := by
      intro u hu
      by_contra hnot
      have huE : u ∈ E := ⟨⟨hu.1, hu.2.le.trans htI.2⟩, hnot⟩
      exact (not_le_of_gt hu.2) (csInf_le hEb huE)
    have htK : γ.extend t ∈ K := by
      refine hK.mem_of_tendsto (f := γ.extend) (b := 𝓝[<] t) ?_ ?_
      · exact γ.continuous_extend.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT hst] with u hu
        exact interior_subset (hbefore u ⟨hu.1.le, hu.2⟩)
    have htrace : γ.extend '' Icc s t ⊆ K := by
      rintro y ⟨u, hu, rfl⟩
      rcases hu.2.eq_or_lt with h | h
      · simpa only [h] using htK
      · exact interior_subset (hbefore u ⟨hu.1, h⟩)
    have hfront : γ.extend t ∈ frontier K := by
      rw [hK.frontier_eq]
      exact ⟨htK, htE.2⟩
    exact ⟨t, hst, htI.2, htrace, Or.inr hfront⟩
  · refine ⟨1, hs1, le_rfl, ?_, Or.inl rfl⟩
    rintro y ⟨u, hu, rfl⟩
    apply interior_subset
    by_contra hnot
    exact hE ⟨u, hu, hnot⟩

/-- Refine the first positive time interval at its midpoint, duplicating only
its owner. Existing Fin insertion supplies strictness; both subtraces stay put. -/
theorem s25s_refine_once {a b : S} (γ : Path a b) {m n : ℕ} (hm : 0 < m)
    (K : Fin n → Set S) (τ : Fin (m + 1) → ℝ) (w : Fin m → Fin n)
    (hτ : StrictMono τ)
    (htrace : ∀ i : Fin m, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ K (w i)) :
    ∃ (τ' : Fin (m + 2) → ℝ) (w' : Fin (m + 1) → Fin n),
      τ' 0 = τ 0 ∧ τ' (Fin.last (m + 1)) = τ (Fin.last m) ∧ StrictMono τ' ∧
      ∀ i : Fin (m + 1),
        γ.extend '' Icc (τ' i.castSucc) (τ' i.succ) ⊆ K (w' i) := by
  classical
  cases m with
  | zero => omega
  | succ k =>
    let x : ℝ := (τ 0 + τ (0 : Fin (k + 1)).succ) / 2
    have hab : τ 0 < τ (0 : Fin (k + 1)).succ :=
      hτ (by simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ]; omega :
        (0 : Fin (k + 2)) < (0 : Fin (k + 1)).succ)
    have hax : τ 0 < x := by dsimp only [x]; linarith
    have hxb : x < τ (0 : Fin (k + 1)).succ := by dsimp only [x]; linarith
    let τ' : Fin (k + 3) → ℝ :=
      Fin.insertNth (α := fun _ : Fin (k + 3) => ℝ) (0 : Fin (k + 2)).succ x τ
    let w' : Fin (k + 2) → Fin n := Fin.cons (w 0) w
    have hform : τ' = Fin.cons (τ 0) (Fin.cons x (Fin.tail τ)) := by
      change Fin.insertNth (α := fun _ : Fin (k + 3) => ℝ) (0 : Fin (k + 2)).succ x τ = _
      calc
        Fin.insertNth (α := fun _ : Fin (k + 3) => ℝ) (0 : Fin (k + 2)).succ x τ =
            Fin.insertNth (α := fun _ : Fin (k + 3) => ℝ) (0 : Fin (k + 2)).succ x
              (Fin.cons (τ 0) (Fin.tail τ)) :=
          congrArg (fun f : Fin (k + 2) → ℝ =>
            Fin.insertNth (α := fun _ : Fin (k + 3) => ℝ) (0 : Fin (k + 2)).succ x f)
            (Fin.cons_self_tail τ).symm
        _ = Fin.cons (τ 0) (Fin.cons x (Fin.tail τ)) := by
          rw [Fin.insertNth_succ_cons, Fin.insertNth_zero']
    have htail (j : Fin (k + 1)) : Fin.tail τ j = τ j.succ := rfl
    have hstrict : StrictMono τ' := by
      exact Fin.strictMono_insertNth hτ (0 : Fin (k + 1)) x hax hxb
    have hzero : τ' 0 = τ 0 := by rw [hform, Fin.cons_zero]
    have hlast : τ' (Fin.last (k + 2)) = τ (Fin.last (k + 1)) := by
      rw [hform, Fin.cons_last, Fin.cons_last, htail, Fin.succ_last]
    have hleft : γ.extend '' Icc (τ 0) x ⊆ K (w 0) := by
      rintro y ⟨u, hu, rfl⟩
      apply htrace (0 : Fin (k + 1))
      exact ⟨u, ⟨hu.1, hu.2.trans hxb.le⟩, rfl⟩
    have hright : γ.extend '' Icc x (τ (0 : Fin (k + 1)).succ) ⊆ K (w 0) := by
      rintro y ⟨u, hu, rfl⟩
      apply htrace (0 : Fin (k + 1))
      exact ⟨u, ⟨hax.le.trans hu.1, hu.2⟩, rfl⟩
    refine ⟨τ', w', hzero, hlast, hstrict, ?_⟩
    intro j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simpa only [hform, w', Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hleft
    · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
      · simpa only [hform, w', ← Fin.succ_castSucc, Fin.castSucc_zero,
          Fin.cons_zero, Fin.cons_succ, htail] using hright
      · simpa only [hform, w', ← Fin.succ_castSucc, Fin.cons_succ, htail]
          using htrace j.succ

/-- Any strict positive coarse subdivision can be refined to a prescribed
larger number of pieces without changing endpoints or leaving its owners. -/
theorem s25s_refine_grid {a b : S} (γ : Path a b) {m N n : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) (K : Fin n → Set S)
    (τ : Fin (m + 1) → ℝ) (w : Fin m → Fin n) (hτ : StrictMono τ)
    (htrace : ∀ i : Fin m, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ K (w i)) :
    ∃ (σ : Fin (N + 1) → ℝ) (v : Fin N → Fin n),
      σ 0 = τ 0 ∧ σ (Fin.last N) = τ (Fin.last m) ∧ StrictMono σ ∧
      ∀ i : Fin N, γ.extend '' Icc (σ i.castSucc) (σ i.succ) ⊆ K (v i) := by
  have hpad : ∀ d : ℕ, ∃ (σ : Fin (m + d + 1) → ℝ) (v : Fin (m + d) → Fin n),
      σ 0 = τ 0 ∧ σ (Fin.last (m + d)) = τ (Fin.last m) ∧ StrictMono σ ∧
      ∀ i : Fin (m + d), γ.extend '' Icc (σ i.castSucc) (σ i.succ) ⊆ K (v i) := by
    intro d
    induction d with
    | zero => exact ⟨τ, w, rfl, rfl, hτ, htrace⟩
    | succ d ih =>
      obtain ⟨σ, v, h0, h1, hmono, hsub⟩ := ih
      have hmd : 0 < m + d := by omega
      obtain ⟨σ', v', h0', h1', hmono', hsub'⟩ :=
        s25s_refine_once γ hmd K σ v hmono hsub
      have hout : ∃ (σ' : Fin (m + d + 2) → ℝ) (v' : Fin (m + d + 1) → Fin n),
          σ' 0 = τ 0 ∧ σ' (Fin.last (m + d + 1)) = τ (Fin.last m) ∧
          StrictMono σ' ∧ ∀ i : Fin (m + d + 1),
            γ.extend '' Icc (σ' i.castSucc) (σ' i.succ) ⊆ K (v' i) :=
        ⟨σ', v', h0'.trans h0, h1'.trans h1, hmono', hsub'⟩
      simpa only [Nat.add_succ] using hout
  obtain ⟨d, hd⟩ : ∃ d : ℕ, N = m + d := ⟨N - m, by omega⟩
  subst N
  exact hpad d

/-- Finite fuel bounds greedy exits. The paid-prefix invariant prevents a
nonterminal step at exhausted fuel, without ENNReal subtraction or cancellation. -/
theorem s25s_greedy_fuel {q : S → ℂ → ℂ} {n : ℕ} (U K : Fin n → Set S)
    (hU : ∀ i, U i ⊆ interior (K i)) (hK : ∀ i, IsClosed (K i))
    (hcover : ∀ p : S, ∃ i : Fin n, p ∈ U i)
    {ε L : ℝ≥0∞}
    (hexit : ∀ i : Fin n, ∀ {a b : S} (γ : Path a b) {s t : ℝ},
      0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U i →
      γ.extend '' Icc s t ⊆ K i → γ.extend t ∈ frontier (K i) →
      ε ≤ phiLengthOn q γ s t)
    {M : ℕ} (hM : L < (M : ℝ≥0∞) * ε)
    {a b : S} (γ : Path a b) (hγ : phiLengthPath q γ ≤ L) :
    ∀ r j : ℕ, j + r = M → ∀ s : ℝ, 0 ≤ s → s < 1 →
      (j : ℝ≥0∞) * ε ≤ phiLengthOn q γ 0 s →
      ∃ (m : ℕ), 0 < m ∧ m ≤ r ∧
        ∃ (τ : Fin (m + 1) → ℝ) (w : Fin m → Fin n),
          τ 0 = s ∧ τ (Fin.last m) = 1 ∧ StrictMono τ ∧
          ∀ i : Fin m, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ K (w i) := by
  classical
  have hprefix : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → phiLengthOn q γ 0 s ≤ L := by
    intro s hs hs1
    calc
      phiLengthOn q γ 0 s ≤ phiLengthOn q γ 0 s + phiLengthOn q γ s 1 :=
        le_add_right le_rfl
      _ ≤ phiLengthOn q γ 0 1 := s25i_split_ge γ hs hs1
      _ ≤ L := hγ
  intro r
  induction r with
  | zero =>
    intro j hj s hs hs1 hpaid
    have hjM : j = M := by omega
    have hbad : (M : ℝ≥0∞) * ε ≤ L := by
      simpa only [hjM] using hpaid.trans (hprefix s hs hs1.le)
    exact False.elim ((not_le_of_gt hM) hbad)
  | succ r ih =>
    intro j hj s hs hs1 hpaid
    obtain ⟨i, hi⟩ := hcover (γ.extend s)
    obtain ⟨t, hst, ht1, htrace, hterminal⟩ :=
      s25s_first_exit γ (K i) (hK i) hs hs1 (hU i hi)
    by_cases ht : t = 1
    · let τ : Fin 2 → ℝ := Fin.cons s (fun _ : Fin 1 => (1 : ℝ))
      let w : Fin 1 → Fin n := fun _ => i
      have hmono : StrictMono τ := by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro k
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        simpa only [τ, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hs1
      refine ⟨1, by decide, by omega, τ, w, rfl, rfl, hmono, ?_⟩
      intro k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simpa only [τ, w, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ht] using htrace
    · have htlt : t < 1 := by
        rcases ht1.eq_or_lt with h | h
        · exact False.elim (ht h)
        · exact h
      have hfront : γ.extend t ∈ frontier (K i) := by
        rcases hterminal with h | h
        · exact False.elim (ht h)
        · exact h
      have hepay : ε ≤ phiLengthOn q γ s t := hexit i γ hs hst ht1 hi htrace hfront
      have hpaid' : ((j + 1 : ℕ) : ℝ≥0∞) * ε ≤ phiLengthOn q γ 0 t := by
        calc
          ((j + 1 : ℕ) : ℝ≥0∞) * ε = (j : ℝ≥0∞) * ε + ε := by
            rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          _ ≤ phiLengthOn q γ 0 s + phiLengthOn q γ s t := add_le_add hpaid hepay
          _ ≤ phiLengthOn q γ 0 t := s25i_split_ge γ hs hst.le
      have hj' : j + 1 + r = M := by omega
      obtain ⟨m, hm, hmr, τ, w, h0, h1, hmono, hsub⟩ :=
        ih (j + 1) hj' t (hs.trans hst.le) htlt hpaid'
      let τ' : Fin (m + 2) → ℝ := Fin.cons s τ
      let w' : Fin (m + 1) → Fin n := Fin.cons i w
      have hmono' : StrictMono τ' := by
        apply Fin.strictMono_cons.mpr
        refine ⟨?_, hmono⟩
        intro k
        have htk : t ≤ τ k := by
          rw [← h0]
          exact hmono.monotone (Fin.zero_le k)
        exact hst.trans_le htk
      have h0' : τ' 0 = s := by rfl
      have h1' : τ' (Fin.last (m + 1)) = 1 := by
        dsimp only [τ']
        rw [Fin.cons_last]
        exact h1
      refine ⟨m + 1, by omega, by omega, τ', w', h0', h1', hmono', ?_⟩
      intro k
      obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
      · simpa only [τ', w', Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, h0]
          using htrace
      · simpa only [τ', w', ← Fin.succ_castSucc, Fin.cons_succ] using hsub k

/-- Proposed uniform greedy subdivision. At each vertex choose an inner set containing it,
and stop at the first exit from the corresponding compact set's interior. Every completed
exit pays epsilon, so superadditivity bounds the number of pieces. Refine existing nondegenerate
pieces in time to pad every subdivision to one fixed N without changing containment. -/
theorem s25s_bounded_subdivide [T2Space S]
    {q : S → ℂ → ℂ} {n : ℕ} (U K : Fin n → Set S)
    (hU : ∀ i, U i ⊆ interior (K i)) (hK : ∀ i, IsClosed (K i))
    (hcover : ∀ p : S, ∃ i : Fin n, p ∈ U i)
    {ε L : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε < ⊤) (hL : L < ⊤)
    (hexit : ∀ i : Fin n, ∀ {a b : S} (γ : Path a b) {s t : ℝ},
      0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U i →
      γ.extend '' Icc s t ⊆ K i → γ.extend t ∈ frontier (K i) →
      ε ≤ phiLengthOn q γ s t) :
    ∃ N : ℕ, 0 < N ∧ ∀ {a b : S} (γ : Path a b), phiLengthPath q γ ≤ L →
      ∃ (τ : Fin (N + 1) → ℝ) (w : Fin N → Fin n),
        τ 0 = 0 ∧ τ (Fin.last N) = 1 ∧ StrictMono τ ∧
        ∀ i : Fin N, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ K (w i) := by
  classical
  -- The stronger frozen finiteness hypothesis is preserved. Counting itself
  -- needs positive epsilon and finite L; no toReal or cancellation is used.
  have _hεfin := hεfin
  obtain ⟨M, hMpos, hM⟩ := ENNReal.exists_nat_pos_mul_gt (a := ε) (b := L) hε.ne' hL.ne
  refine ⟨M, hMpos, ?_⟩
  intro a b γ hγ
  obtain ⟨m, hm, hmM, τ, w, h0, h1, hmono, htrace⟩ :=
    s25s_greedy_fuel U K hU hK hcover hexit hM γ hγ M 0 (by omega)
      0 (by norm_num) (by norm_num) (by simp only [Nat.cast_zero, zero_mul]; exact bot_le)
  obtain ⟨σ, v, h0', h1', hmono', htrace'⟩ :=
    s25s_refine_grid γ hm hmM K τ w hmono htrace
  exact ⟨σ, v, h0'.trans h0, h1'.trans h1, hmono', htrace'⟩


/-- Cancel the interior connector between two successive transported edges. -/
theorem s25s_connector_cancel {x₀ x₁ x₂ y₀ y₁ y₂ : S}
    (k₀ : Path x₀ y₀) (k₁ : Path x₁ y₁) (k₂ : Path x₂ y₂)
    (σ : Path y₀ y₁) (ρ : Path y₁ y₂) :
    (((k₀.trans σ).trans k₁.symm).trans ((k₁.trans ρ).trans k₂.symm)).Homotopic
      ((k₀.trans (σ.trans ρ)).trans k₂.symm) := by
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_refl]
  let A := Path.Homotopic.Quotient.mk k₀
  let B := Path.Homotopic.Quotient.mk k₁
  let C := Path.Homotopic.Quotient.mk k₂
  let P := Path.Homotopic.Quotient.mk σ
  let Q := Path.Homotopic.Quotient.mk ρ
  change ((A.trans P).trans B.symm).trans ((B.trans Q).trans C.symm) =
    (A.trans (P.trans Q)).trans C.symm
  calc
    _ = A.trans (P.trans ((B.symm.trans B).trans (Q.trans C.symm))) := by
      simp only [Path.Homotopic.Quotient.trans_assoc]
    _ = _ := by
      rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
      simp only [Path.Homotopic.Quotient.trans_assoc]

/-- Transporting every edge by vertex connectors cancels all interior connectors. -/
theorem s25s_concat_connectors {N : ℕ} (x y : Fin (N + 1) → S)
    (k : ∀ j, Path (x j) (y j))
    (σ : ∀ i : Fin N, Path (y i.castSucc) (y i.succ)) :
    (Path.concat x (fun i => ((k i.castSucc).trans (σ i)).trans (k i.succ).symm)).Homotopic
      (((k 0).trans (Path.concat y σ)).trans (k (Fin.last N)).symm) := by
  induction N with
  | zero =>
    simp only [Path.concat_zero, Fin.last_zero]
    exact (((Path.Homotopic.trans_refl (k 0)).hcomp
      (Path.Homotopic.refl ((k 0).symm))).trans
      (Path.Homotopic.trans_symm (k 0))).symm
  | succ N ih =>
    rw [Path.concat_succ, Path.concat_succ]
    exact ((ih (x ∘ Fin.castSucc) (y ∘ Fin.castSucc)
      (fun j => k j.castSucc) (fun i => σ i.castSucc)).hcomp
      (Path.Homotopic.refl _)).trans
      (s25s_connector_cancel (k 0) (k (Fin.last N).castSucc)
        (k (Fin.last (N + 1)))
        (Path.concat (y ∘ Fin.castSucc) (fun i => σ i.castSucc)) (σ (Fin.last N)))

/-- A path concatenation stays inside a set if its two factors do. -/
theorem s25s_trans_mem {a b c : S} {D : Set S} (σ : Path a b) (ρ : Path b c)
    (hσ : ∀ u, σ u ∈ D) (hρ : ∀ u, ρ u ∈ D) : ∀ u, σ.trans ρ u ∈ D := by
  intro u
  rw [Path.trans_apply]
  split_ifs
  · exact hσ _
  · exact hρ _

/-- A finite chart-disc polygon has the class of its chosen disc-contained edges. -/
theorem s25s_grid_concat_class {N : ℕ} (hN : 0 < N)
    (c : Fin N → S) (r : Fin N → ℝ)
    (hr : ∀ i, ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target)
    (x : Fin (N + 1) → S)
    (σ : ∀ i : Fin N, Path (x i.castSucc) (x i.succ))
    (hσ : ∀ i u, σ i u ∈ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))
    {a b : S} (γ : Path a b) (hx0 : x 0 = a) (hx1 : x (Fin.last N) = b)
    (hv : ∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = x j)
    (hγ : ∀ i : Fin N, γ.extend ''
      Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
      (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) :
    ((Path.concat x σ).cast hx0.symm hx1.symm).Homotopic γ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : ∀ j : Fin (N + 1), (j.val : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    intro j
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNr.le,
      (div_le_one hNr).2 (by exact_mod_cast Nat.le_of_lt_succ j.isLt)⟩
  let t : Fin (N + 1) → unitInterval := fun j => ⟨(j.val : ℝ) / (N : ℝ), hm j⟩
  have ht0 : t 0 = 0 := by apply Subtype.ext; simp [t]
  have ht1 : t (Fin.last N) = 1 := by
    apply Subtype.ext
    simp [t, ne_of_gt hNr]
  have hv' : ∀ j, x j = γ (t j) := by
    intro j
    simpa only [t, Path.extend_apply γ (hm j)] using (hv j).symm
  let ρ : ∀ i : Fin N, Path (x i.castSucc) (x i.succ) := fun i =>
    (γ.subpath (t i.castSucc) (t i.succ)).cast (hv' i.castSucc) (hv' i.succ)
  have hedge : ∀ i, (σ i).Homotopic (ρ i) := by
    intro i
    apply s25s_disc_homotopic (c i) (hr i) _ _ (hσ i)
    apply s25s_subpath_mem γ
    · change (i.val : ℝ) / (N : ℝ) ≤ ((i.succ.val : ℕ) : ℝ) / (N : ℝ)
      apply div_le_div_of_nonneg_right _ hNr.le
      exact_mod_cast Nat.le_succ i.val
    · simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hγ i
  have H := (Path.Homotopic.concat_hcomp x σ ρ hedge).trans
    (s25s_concat_subpath_class γ t x hv')
  change Nonempty (ContinuousMap.HomotopyRel (Path.concat x σ).toContinuousMap
    (γ.subpath (t 0) (t (Fin.last N))).toContinuousMap {0, 1}) at H
  rw [ht0, ht1, Path.subpath_zero_one] at H
  exact H

/-- Local endpoint transport of a polygon preserves its class when its outer connectors
are constant. The equal-grid representative is supplied by the frozen gluing contract. -/
theorem s25s_transport_polygon {N : ℕ} (hN : 0 < N)
    (c : Fin N → S) (r : Fin N → ℝ)
    (hr : ∀ i, ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target)
    {a b : S} (x y : Fin (N + 1) → S)
    (hx0 : x 0 = a) (hx1 : x (Fin.last N) = b)
    (hy0 : y 0 = a) (hy1 : y (Fin.last N) = b)
    (k : ∀ j, Path (x j) (y j))
    (hk0 : ∀ u, k 0 u = a) (hk1 : ∀ u, k (Fin.last N) u = b)
    (hk : ∀ i : Fin N, ∀ u,
      k i.castSucc u ∈ (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) ∧
      k i.succ u ∈ (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))
    (γ : Path a b)
    (hv : ∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = y j)
    (hγ : ∀ i : Fin N, γ.extend ''
      Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
      (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) :
    ∃ δ : Path a b, δ.Homotopic γ ∧
      (∀ j : Fin (N + 1), δ.extend ((j.val : ℝ) / (N : ℝ)) = x j) ∧
      (∀ i : Fin N, δ.extend ''
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
        (chartAt ℂ (c i)).source ∩
          chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : ∀ j : Fin (N + 1), (j.val : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    intro j
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNr.le,
      (div_le_one hNr).2 (by exact_mod_cast Nat.le_of_lt_succ j.isLt)⟩
  let t : Fin (N + 1) → unitInterval := fun j => ⟨(j.val : ℝ) / (N : ℝ), hm j⟩
  have hv' : ∀ j, y j = γ (t j) := by
    intro j
    simpa only [t, Path.extend_apply γ (hm j)] using (hv j).symm
  let σ : ∀ i : Fin N, Path (y i.castSucc) (y i.succ) := fun i =>
    (γ.subpath (t i.castSucc) (t i.succ)).cast (hv' i.castSucc) (hv' i.succ)
  have hσ : ∀ i u, σ i u ∈ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) := by
    intro i
    apply s25s_subpath_mem γ
    · change (i.val : ℝ) / (N : ℝ) ≤ ((i.succ.val : ℕ) : ℝ) / (N : ℝ)
      apply div_le_div_of_nonneg_right _ hNr.le
      exact_mod_cast Nat.le_succ i.val
    · simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hγ i
  let ρ : ∀ i : Fin N, Path (x i.castSucc) (x i.succ) := fun i =>
    ((k i.castSucc).trans (σ i)).trans (k i.succ).symm
  have hρ : ∀ i u, ρ i u ∈ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) := by
    intro i
    exact s25s_trans_mem _ _
      (s25s_trans_mem _ _ (fun u => (hk i u).1) (hσ i))
      (fun u => (hk i (unitInterval.symm u)).2)
  obtain ⟨δ₀, hδv, hδtrace, hδlength⟩ :=
    s25s_glue_path (q := fun _ _ => 0) hN x ρ
  -- The gluing length bound is deliberately not needed for this topological statement.
  have _hδlength := hδlength
  let δ : Path a b := δ₀.cast hx0.symm hx1.symm
  have hδD : ∀ i : Fin N, δ.extend ''
      Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
      (chartAt ℂ (c i)).source ∩
        chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) := by
    intro i z hz
    obtain ⟨u, hu⟩ := hδtrace i hz
    rw [← hu]
    exact hρ i u
  have hδclass := s25s_grid_concat_class hN c r hr x ρ hρ δ hx0 hx1 hδv hδD
  have hγclass := s25s_grid_concat_class hN c r hr y σ hσ γ hy0 hy1 hv hγ
  have H := (s25s_concat_connectors x y k σ).pathCast hx0.symm hx1.symm
  have hk0' : (k 0).cast hx0.symm hy0.symm = Path.refl a := by
    ext u
    exact hk0 u
  have hk1' : (k (Fin.last N)).cast hx1.symm hy1.symm = Path.refl b := by
    ext u
    exact hk1 u
  have H' : ((Path.concat x ρ).cast hx0.symm hx1.symm).Homotopic
      (((Path.refl a).trans ((Path.concat y σ).cast hy0.symm hy1.symm)).trans
        (Path.refl b)) := by
    simpa only [Path.cast_trans _ _ hx0.symm hy1.symm hx1.symm,
      Path.cast_trans _ _ hx0.symm hy0.symm hy1.symm,
      Path.cast_symm, hk0', hk1', Path.refl_symm] using H
  have H'' := H'.trans ((Path.Homotopic.trans_refl _).trans
    ((Path.Homotopic.refl_trans _).trans hγclass))
  exact ⟨δ, hδclass.symm.trans H'', hδv, hδD⟩

/-- Proposed closedness bridge: for a fixed finite disc word, compact admissible vertex
tuples admitting a polygon in a fixed homotopy class form a closed set.
Nearby vertices can be connected inside intersections of adjacent chart discs; cancellation
of the inserted connectors preserves the class. Compact sets prevent escape at the limit. -/
theorem s25s_polygon_class_closed [T2Space S] {N : ℕ} (hN : 0 < N)
    (c : Fin N → S) (r : Fin N → ℝ) (K : Fin N → Set S)
    (hr : ∀ i, ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target)
    (hK : ∀ i, IsCompact (K i))
    (hKD : ∀ i, K i ⊆ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))
    {a b : S} (α : Path a b) :
    IsClosed {x : Fin (N + 1) → S |
      x 0 = a ∧ x (Fin.last N) = b ∧
      (∀ i : Fin N, x i.castSucc ∈ K i ∧ x i.succ ∈ K i) ∧
      ∃ γ : Path a b, γ.Homotopic α ∧
        (∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = x j) ∧
        (∀ i : Fin N, γ.extend ''
          Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
          (chartAt ℂ (c i)).source ∩
            chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))} := by
  classical
  letI : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := S)
  let D : Fin N → Set S := fun i => (chartAt ℂ (c i)).source ∩
    chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)
  let A : Set (Fin (N + 1) → S) := {x |
    x 0 = a ∧ x (Fin.last N) = b ∧
    (∀ i : Fin N, x i.castSucc ∈ K i ∧ x i.succ ∈ K i) ∧
    ∃ γ : Path a b, γ.Homotopic α ∧
      (∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = x j) ∧
      (∀ i : Fin N, γ.extend ''
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆ D i)}
  change IsClosed A
  apply isClosed_of_closure_subset
  intro x hx
  have hx0 : x 0 = a := closure_minimal (fun y hy => hy.1)
    (isClosed_eq (continuous_apply 0) continuous_const) hx
  have hx1 : x (Fin.last N) = b := closure_minimal (fun y hy => hy.2.1)
    (isClosed_eq (continuous_apply (Fin.last N)) continuous_const) hx
  have hxK : ∀ i : Fin N, x i.castSucc ∈ K i ∧ x i.succ ∈ K i := by
    intro i
    exact ⟨closure_minimal (fun y hy => (hy.2.2.1 i).1)
      ((hK i).isClosed.preimage (continuous_apply i.castSucc)) hx,
      closure_minimal (fun y hy => (hy.2.2.1 i).2)
      ((hK i).isClosed.preimage (continuous_apply i.succ)) hx⟩
  have hD : ∀ i, IsOpen (D i) := fun i =>
    (chartAt ℂ (c i)).isOpen_inter_preimage isOpen_ball
  -- At a vertex use the intersection of precisely its incident discs.
  let V : Fin (N + 1) → Set S := fun j =>
    ⋂ i : Fin N, if j = i.castSucc ∨ j = i.succ then D i else univ
  have hV : ∀ j, IsOpen (V j) := by
    intro j
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact hD i
    · exact isOpen_univ
  have hxV : ∀ j, x j ∈ V j := by
    intro j
    apply mem_iInter.mpr
    intro i
    by_cases hj : j = i.castSucc ∨ j = i.succ
    · rw [if_pos hj]
      rcases hj with hj | hj
      · subst j
        exact hKD i (hxK i).1
      · subst j
        exact hKD i (hxK i).2
    · rw [if_neg hj]
      trivial
  let W : Set (Fin (N + 1) → S) :=
    ⋂ j : Fin (N + 1), (fun y => y j) ⁻¹' pathComponentIn (V j) (x j)
  have hW : IsOpen W := isOpen_iInter_of_finite fun j =>
    ((hV j).pathComponentIn (x j)).preimage (continuous_apply j)
  have hxW : x ∈ W := mem_iInter.mpr fun j => mem_pathComponentIn_self (hxV j)
  obtain ⟨y, hyW, hyA⟩ := mem_closure_iff.mp hx W hW hxW
  rcases hyA with ⟨hy0, hy1, hyK, γ, hγα, hγv, hγD⟩
  have hj : ∀ j, JoinedIn (V j) (x j) (y j) := fun j => mem_iInter.mp hyW j
  -- Endpoints use constant connectors, even if the local component has nontrivial loops.
  let k : ∀ j, Path (x j) (y j) := fun j =>
    if h0 : j = 0 then
      (Path.refl a).cast (by simpa only [h0] using hx0) (by simpa only [h0] using hy0)
    else if h1 : j = Fin.last N then
      (Path.refl b).cast (by simpa only [h1] using hx1) (by simpa only [h1] using hy1)
    else (hj j).somePath
  have hlast : Fin.last N ≠ (0 : Fin (N + 1)) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  have hk0 : ∀ u, k 0 u = a := by
    intro u
    simp only [k, dif_pos rfl, Path.cast_coe, Path.refl_apply]
  have hk1 : ∀ u, k (Fin.last N) u = b := by
    intro u
    simp [k, hlast]
  have hkV : ∀ j u, k j u ∈ V j := by
    intro j u
    by_cases h0 : j = 0
    · subst j
      rw [hk0]
      rw [← hx0]
      exact hxV 0
    · by_cases h1 : j = Fin.last N
      · subst j
        rw [hk1]
        rw [← hx1]
        exact hxV (Fin.last N)
      · simpa [k, h0, h1] using (hj j).somePath_mem u
  have hk : ∀ i : Fin N, ∀ u, k i.castSucc u ∈ D i ∧ k i.succ u ∈ D i := by
    intro i u
    constructor
    · have hm := mem_iInter.mp (hkV i.castSucc u) i
      simpa using hm
    · have hm := mem_iInter.mp (hkV i.succ u) i
      simpa using hm
  obtain ⟨δ, hδγ, hδv, hδD⟩ := s25s_transport_polygon hN c r hr x y
    hx0 hx1 hy0 hy1 k hk0 hk1 hk γ hγv hγD
  exact ⟨hx0, hx1, hxK, δ, hδγ.trans hγα, hδv, hδD⟩


/-- Superadditivity iterated over a monotone finite grid, including infinite lengths. -/
theorem s25s_grid_split_ge {q : S → ℂ → ℂ} {a b : S} (γ : Path a b)
    {N : ℕ} (τ : Fin (N + 1) → ℝ) (hτ : Monotone τ) :
    (∑ i : Fin N, phiLengthOn q γ (τ i.castSucc) (τ i.succ)) ≤
      phiLengthOn q γ (τ 0) (τ (Fin.last N)) := by
  classical
  revert τ
  induction N with
  | zero =>
    intro τ hτ
    simp
  | succ n ih =>
    intro τ hτ
    let τ' : Fin (n + 1) → ℝ := fun j => τ j.castSucc
    have hτ' : Monotone τ' := by
      intro i j hij
      exact hτ hij
    have hp := ih τ' hτ'
    have h0 : τ 0 ≤ τ (Fin.last n).castSucc := hτ (Fin.zero_le _)
    have h1 : τ (Fin.last n).castSucc ≤ τ (Fin.last (n + 1)) := hτ (Fin.le_last _)
    rw [Fin.sum_univ_castSucc]
    calc
      (∑ i : Fin n, phiLengthOn q γ (τ i.castSucc.castSucc) (τ i.castSucc.succ)) +
          phiLengthOn q γ (τ (Fin.last n).castSucc) (τ (Fin.last n).succ) ≤
          phiLengthOn q γ (τ 0) (τ (Fin.last n).castSucc) +
            phiLengthOn q γ (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))) := by
          simpa [τ'] using add_le_add hp (le_refl
            (phiLengthOn q γ (τ (Fin.last n).castSucc) (τ (Fin.last n).succ)))
      _ ≤ phiLengthOn q γ (τ 0) (τ (Fin.last (n + 1))) := s25i_split_ge γ h0 h1

/-- The finite sum of endpoint distances is bounded by the original path's length.
Each strict subinterval uses the earlier affine subpath bound, then the grid split bound. -/
theorem s25s_grid_distance_le {q : S → ℂ → ℂ} {a b : S} (β : Path a b)
    {N : ℕ} (τ : Fin (N + 1) → ℝ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last N) = 1) (hτ : StrictMono τ) :
    (∑ i : Fin N, phiDistRS q (β.extend (τ i.castSucc)) (β.extend (τ i.succ))) ≤
      phiLengthPath q β := by
  classical
  have hτI : ∀ j, 0 ≤ τ j ∧ τ j ≤ 1 := by
    intro j
    constructor
    · simpa only [hτ0] using hτ.monotone (Fin.zero_le j)
    · simpa only [hτ1] using hτ.monotone (Fin.le_last j)
  have hedge : ∀ i : Fin N,
      phiDistRS q (β.extend (τ i.castSucc)) (β.extend (τ i.succ)) ≤
        phiLengthOn q β (τ i.castSucc) (τ i.succ) := by
    intro i
    obtain ⟨ρ, hρ, hρlen⟩ := s25i_subpath_length (q := q) β (hτI i.castSucc).1
      (hτ i.castSucc_lt_succ) (hτI i.succ).2
    exact (iInf_le _ ρ).trans hρlen
  calc
    (∑ i : Fin N, phiDistRS q (β.extend (τ i.castSucc)) (β.extend (τ i.succ))) ≤
        ∑ i : Fin N, phiLengthOn q β (τ i.castSucc) (τ i.succ) :=
      Finset.sum_le_sum (fun i _ => hedge i)
    _ ≤ phiLengthOn q β 0 1 := by
      simpa only [hτ0, hτ1] using s25s_grid_split_ge (q := q) β τ hτ.monotone
    _ = phiLengthPath q β := rfl

/-- Proposed compact minimization bridge: minimize the finite edge cost over the compact
vertex sets and the finite set of disc words, then realize that tuple by local minimizers.
Every bounded competitor has an admissible subdivision. Only an upper gluing bound is
needed; exact additivity for Path.trans and a global metric structure are unnecessary. -/
theorem s25s_minimum_of_cover [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {n N : ℕ} (hN : 0 < N) (c : Fin n → S) (r : Fin n → ℝ) (K : Fin n → Set S)
    (hr : ∀ i, ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target)
    (hK : ∀ i, IsCompact (K i))
    (hKD : ∀ i, K i ⊆ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i))
    (hd : ∀ i, ContinuousOn (fun z : S × S => phiDistRS q z.1 z.2) ((K i) ×ˢ (K i)))
    (hs : ∀ i, ∀ a ∈ K i, ∀ b ∈ K i, phiDistRS q a b < ⊤ ∧
      ∃ σ : Path a b,
        (∀ u, σ u ∈ (chartAt ℂ (c i)).source ∩
          chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) ∧
        phiLengthPath q σ = phiDistRS q a b)
    {L : ℝ≥0∞} (hL : L < ⊤)
    (hsub : ∀ {a b : S} (β : Path a b), phiLengthPath q β ≤ L →
      ∃ (τ : Fin (N + 1) → ℝ) (w : Fin N → Fin n),
        τ 0 = 0 ∧ τ (Fin.last N) = 1 ∧ StrictMono τ ∧
        ∀ i : Fin N, β.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ K (w i))
    {a b : S} (α : Path a b) (hα : phiLengthPath q α ≤ L) :
    ∃ γ : Path a b, γ.Homotopic α ∧ phiLengthPath q γ ≤ L ∧
      ∀ β : Path a b, β.Homotopic α → phiLengthPath q β ≤ L →
        phiLengthPath q γ ≤ phiLengthPath q β := by
  classical
  -- The analytic hypotheses have already supplied hd and hs; the compact argument uses those data.
  have _hq := hq
  have _hne := hne
  have _hL := hL
  let Word := Fin N → Fin n
  let Vertex := Fin (N + 1) → S
  let η : Fin (N + 1) → ℝ := fun j => (j.val : ℝ) / (N : ℝ)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hη0 : η 0 = 0 := by simp [η]
  have hη1 : η (Fin.last N) = 1 := by simp [η, hNR.ne']
  have hη : StrictMono η := by
    intro i j hij
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) hNR
  have hηedge : ∀ i : Fin N,
      Icc (η i.castSucc) (η i.succ) =
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) := by
    intro i
    simp [η]
  let A : Word → Set Vertex := fun w => {x |
    x 0 = a ∧ x (Fin.last N) = b ∧
    (∀ i : Fin N, x i.castSucc ∈ K (w i) ∧ x i.succ ∈ K (w i)) ∧
    ∃ γ : Path a b, γ.Homotopic α ∧
      (∀ j : Fin (N + 1), γ.extend ((j.val : ℝ) / (N : ℝ)) = x j) ∧
      (∀ i : Fin N, γ.extend ''
        Icc ((i.val : ℝ) / (N : ℝ)) (((i.val : ℝ) + 1) / (N : ℝ)) ⊆
        (chartAt ℂ (c (w i))).source ∩
          chartAt ℂ (c (w i)) ⁻¹' ball (chartAt ℂ (c (w i)) (c (w i))) (r (w i)))}
  let V : Set Vertex := ⋃ w : Word, A w
  let F : Vertex → ℝ≥0∞ := fun x =>
    ∑ i : Fin N, phiDistRS q (x i.castSucc) (x i.succ)
  have hclosed : ∀ w : Word, IsClosed (A w) := by
    intro w
    exact s25s_polygon_class_closed hN (fun i => c (w i)) (fun i => r (w i))
      (fun i => K (w i)) (fun i => hr (w i)) (fun i => hK (w i))
      (fun i => hKD (w i)) α
  have hVcompact : IsCompact V := (isClosed_iUnion_of_finite hclosed).isCompact
  have hFword : ∀ w : Word, ContinuousOn F (A w) := by
    intro w
    apply continuousOn_finsetSum Finset.univ
    intro i _
    have hpair : Continuous (fun x : Vertex => (x i.castSucc, x i.succ)) :=
      (continuous_apply i.castSucc).prodMk (continuous_apply i.succ)
    exact (hd (w i)).comp hpair.continuousOn
      (fun x hx => ⟨(hx.2.2.1 i).1, (hx.2.2.1 i).2⟩)
  have hFunion : ∀ s : Finset Word,
      ContinuousOn F (⋃ w ∈ (s : Set Word), A w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert w s hws ih =>
      have hclosed_s : IsClosed (⋃ v ∈ (s : Set Word), A v) :=
        s.finite_toSet.isClosed_biUnion (fun v _ => hclosed v)
      simpa only [Finset.coe_insert, Set.biUnion_insert] using
        (hFword w).union_of_isClosed ih (hclosed w) hclosed_s
  have hFV : ContinuousOn F V := by
    simpa only [Finset.coe_univ, Set.biUnion_univ] using hFunion Finset.univ
  have hrealize : ∀ (w : Word) (x : Vertex), x 0 = a → x (Fin.last N) = b →
      (∀ i : Fin N, x i.castSucc ∈ K (w i) ∧ x i.succ ∈ K (w i)) →
      ∃ γ : Path a b,
        (∀ j, γ.extend (η j) = x j) ∧
        (∀ i : Fin N, γ.extend '' Icc (η i.castSucc) (η i.succ) ⊆
          (chartAt ℂ (c (w i))).source ∩ chartAt ℂ (c (w i)) ⁻¹'
            ball (chartAt ℂ (c (w i)) (c (w i))) (r (w i))) ∧
        phiLengthPath q γ ≤ F x := by
    intro w x hx0 hx1 hxK
    have hedge : ∀ i : Fin N, ∃ σ : Path (x i.castSucc) (x i.succ),
        (∀ u, σ u ∈ (chartAt ℂ (c (w i))).source ∩ chartAt ℂ (c (w i)) ⁻¹'
          ball (chartAt ℂ (c (w i)) (c (w i))) (r (w i))) ∧
        phiLengthPath q σ = phiDistRS q (x i.castSucc) (x i.succ) := by
      intro i
      exact (hs (w i) _ (hxK i).1 _ (hxK i).2).2
    choose σ hσD hσlen using hedge
    obtain ⟨δ, hδv, hδtrace, hδlen⟩ := s25s_glue_path (q := q) hN x σ
    let γ : Path a b := δ.cast hx0.symm hx1.symm
    have hext : γ.extend = δ.extend := Path.extend_cast δ hx0.symm hx1.symm
    refine ⟨γ, ?_, ?_, ?_⟩
    · intro j
      rw [hext]
      exact hδv j
    · intro i
      rw [hext, hηedge i]
      refine (hδtrace i).trans ?_
      rintro _ ⟨u, rfl⟩
      exact hσD i u
    · have hlen : phiLengthPath q γ = phiLengthPath q δ := rfl
      rw [hlen]
      calc
        phiLengthPath q δ ≤ ∑ i : Fin N, phiLengthPath q (σ i) := hδlen
        _ = F x := Finset.sum_congr rfl (fun i _ => hσlen i)
  have hcompetitor : ∀ (β : Path a b), β.Homotopic α → phiLengthPath q β ≤ L →
      ∃ x ∈ V, F x ≤ phiLengthPath q β := by
    intro β hβα hβL
    obtain ⟨τ, w, hτ0, hτ1, hτ, hβK⟩ := hsub β hβL
    let x : Vertex := fun j => β.extend (τ j)
    have hx0 : x 0 = a := by simp [x, hτ0, Path.extend_zero]
    have hx1 : x (Fin.last N) = b := by simp [x, hτ1, Path.extend_one]
    have hxK : ∀ i : Fin N, x i.castSucc ∈ K (w i) ∧ x i.succ ∈ K (w i) := by
      intro i
      have htime := hτ.monotone (Fin.castSucc_le_succ i)
      exact ⟨hβK i ⟨τ i.castSucc, ⟨le_rfl, htime⟩, rfl⟩,
        hβK i ⟨τ i.succ, ⟨htime, le_rfl⟩, rfl⟩⟩
    obtain ⟨γ, hγv, hγD, hγlen⟩ := hrealize w x hx0 hx1 hxK
    have hβD : ∀ i : Fin N, β.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆
        (chartAt ℂ (c (w i))).source ∩ chartAt ℂ (c (w i)) ⁻¹'
          ball (chartAt ℂ (c (w i)) (c (w i))) (r (w i)) :=
      fun i => (hβK i).trans (hKD (w i))
    have hγβ : γ.Homotopic β := s25s_polygon_homotopy hN
      (fun i => c (w i)) (fun i => r (w i)) (fun i => hr (w i)) β γ τ η
      hτ0 hτ1 hτ hη0 hη1 hη (fun j => (hγv j).symm) hβD hγD
    have hxA : x ∈ A w := by
      refine ⟨hx0, hx1, hxK, γ, hγβ.trans hβα, hγv, ?_⟩
      intro i
      simpa only [hηedge i] using hγD i
    refine ⟨x, mem_iUnion.mpr ⟨w, hxA⟩, ?_⟩
    exact s25s_grid_distance_le (q := q) β τ hτ0 hτ1 hτ
  obtain ⟨xα, hxα, hcostα⟩ := hcompetitor α (Path.Homotopic.refl α) hα
  obtain ⟨x, hxV, hxmin⟩ := hVcompact.exists_isMinOn ⟨xα, hxα⟩ hFV
  rcases mem_iUnion.mp hxV with ⟨w, hxA⟩
  rcases hxA with ⟨hx0, hx1, hxK, γ₀, hγ₀α, hγ₀v, hγ₀D⟩
  obtain ⟨γ, hγv, hγD, hγlen⟩ := hrealize w x hx0 hx1 hxK
  have hγγ₀ : γ.Homotopic γ₀ := s25s_polygon_homotopy hN
    (fun i => c (w i)) (fun i => r (w i)) (fun i => hr (w i)) γ₀ γ η η
    hη0 hη1 hη hη0 hη1 hη
    (fun j => (hγ₀v j).trans (hγv j).symm)
    (fun i => by simpa only [hηedge i] using hγ₀D i) hγD
  have hmin : ∀ y ∈ V, F x ≤ F y := isMinOn_iff.mp hxmin
  refine ⟨γ, hγγ₀.trans hγ₀α, hγlen.trans ((hmin xα hxα).trans (hcostα.trans hα)), ?_⟩
  intro β hβα hβL
  obtain ⟨y, hyV, hycost⟩ := hcompetitor β hβα hβL
  exact hγlen.trans ((hmin y hyV).trans hycost)


/-- **Theorem 25.4**: let `φ dz² ≢ 0` be a holomorphic quadratic differential on a compact Riemann
surface `S`.  For any two points `p₁, p₂` and any curve `α` joining them, the homotopy class `[α]`
contains a curve of minimal `φ`-length. -/
theorem thm25_4_shortest_exists [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p₁ p₂ : S} (α : Path p₁ p₂) :
    ∃ γ : Path p₁ p₂, γ.Homotopic α ∧ ∀ γ' : Path p₁ p₂, γ'.Homotopic α →
      phiLengthPath q γ ≤ phiLengthPath q γ' := by
  classical
  obtain ⟨β, hβα, hβfin⟩ := s25s_finite_rep hq hne α
  obtain ⟨n, c, r, U, K, ε, hε, hεfin, hcover, hblocks⟩ := s25s_uniform_cover hq hne
  have hr : ∀ i : Fin n,
      ball (chartAt ℂ (c i) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target :=
    fun i => (hblocks i).2.1
  have hU : ∀ i : Fin n, U i ⊆ interior (K i) :=
    fun i => (hblocks i).2.2.2.1
  have hK : ∀ i : Fin n, IsCompact (K i) :=
    fun i => (hblocks i).2.2.2.2.1
  have hKD : ∀ i : Fin n, K i ⊆ (chartAt ℂ (c i)).source ∩
      chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i) :=
    fun i => (hblocks i).2.2.2.2.2.1
  have hd : ∀ i : Fin n,
      ContinuousOn (fun z : S × S => phiDistRS q z.1 z.2) ((K i) ×ˢ (K i)) :=
    fun i => (hblocks i).2.2.2.2.2.2.1
  have hs : ∀ i : Fin n, ∀ a ∈ K i, ∀ b ∈ K i, phiDistRS q a b < ⊤ ∧
      ∃ σ : Path a b,
        (∀ u, σ u ∈ (chartAt ℂ (c i)).source ∩
          chartAt ℂ (c i) ⁻¹' ball (chartAt ℂ (c i) (c i)) (r i)) ∧
        phiLengthPath q σ = phiDistRS q a b :=
    fun i => (hblocks i).2.2.2.2.2.2.2.1
  have hexit : ∀ i : Fin n, ∀ {a b : S} (γ : Path a b) {s t : ℝ},
      0 ≤ s → s < t → t ≤ 1 → γ.extend s ∈ U i →
      γ.extend '' Icc s t ⊆ K i → γ.extend t ∈ frontier (K i) →
      ε ≤ phiLengthOn q γ s t :=
    fun i => (hblocks i).2.2.2.2.2.2.2.2
  obtain ⟨N, hN, hsub⟩ := s25s_bounded_subdivide U K hU
    (fun i => (hK i).isClosed) hcover hε hεfin hβfin hexit
  obtain ⟨γ, hγβ, hγL, hγmin⟩ := s25s_minimum_of_cover hq hne hN c r K
    hr hK hKD hd hs hβfin hsub β le_rfl
  refine ⟨γ, hγβ.trans hβα, ?_⟩
  intro γ' hγ'
  by_cases hcomp : phiLengthPath q γ' ≤ phiLengthPath q β
  · exact hγmin γ' (hγ'.trans hβα.symm) hcomp
  · exact hγL.trans (le_of_lt (lt_of_not_ge hcomp))

/-- §25.2 (remark after Theorem 25.4): a shortest curve in a homotopy class is a `φ`-geodesic. -/
theorem shortest_isPhiGeodesicRS [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p₁ p₂ : S} {γ : Path p₁ p₂}
    (hγ : ∀ γ' : Path p₁ p₂, γ'.Homotopic γ → phiLengthPath q γ ≤ phiLengthPath q γ')
    (hfin : phiLengthPath q γ < ⊤) : IsPhiGeodesicRS q γ := by
  classical
  intro t₀ ht₀
  obtain ⟨r, hr0, hrt, V, hV, hVW, hloc⟩ := s25i_local hq hne (γ.extend t₀)
  have hpre : γ.extend ⁻¹' V ∈ 𝓝 t₀ := γ.continuous_extend.continuousAt.preimage_mem_nhds hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨δ, hδ, fun s hs t ht h1 hst h2 => ?_⟩
  have hmem : ∀ u ∈ Icc s t, γ.extend u ∈ V := fun u hu => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2])
  have hsV := hmem s ⟨le_rfl, hst.le⟩
  have htV := hmem t ⟨hst.le, le_rfl⟩
  obtain ⟨σ, hσW, hσl⟩ := hloc _ hsV _ htV
  apply le_antisymm
  · obtain ⟨γ', hγ'h, hγ'l⟩ := s25i_splice γ (γ.extend t₀) hrt hs.1 hst ht.2
      (by rintro _ ⟨x, hx, rfl⟩; exact hVW (hmem x hx)) σ hσW
    have h1 := hγ γ' hγ'h
    have hfin' : phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 ≤ phiLengthPath q γ := by
      unfold phiLengthPath
      have e1 := s25i_split_ge (q := q) γ (x := 0) (y := s) (z := t) hs.1 hst.le
      have e2 := s25i_split_ge (q := q) γ (x := 0) (y := t) (z := 1) (hs.1.trans hst.le) ht.2
      exact (add_le_add_left e1 _).trans e2
    have hA : phiLengthOn q γ 0 s + phiLengthOn q γ t 1 ≠ ⊤ := by
      refine ne_top_of_le_ne_top hfin.ne ?_
      calc phiLengthOn q γ 0 s + phiLengthOn q γ t 1 ≤
            phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 := by
            rw [add_right_comm]; exact le_self_add
        _ ≤ _ := hfin'
    rw [← hσl]
    have h3 : phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 ≤
        phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 :=
      hfin'.trans (h1.trans hγ'l)
    refine (ENNReal.add_le_add_iff_right hA).1 ?_
    calc phiLengthOn q γ s t + (phiLengthOn q γ 0 s + phiLengthOn q γ t 1) =
          phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 := by ring
      _ ≤ phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 := h3
      _ = phiLengthPath q σ + (phiLengthOn q γ 0 s + phiLengthOn q γ t 1) := by ring
  · obtain ⟨β, hβW, hβl⟩ := s25i_subpath_length (q := q) γ hs.1 hst ht.2
    exact (iInf_le _ β).trans hβl

/-! ## §25.3 The linear space of holomorphic quadratic differentials -/

/-- On `unitDiscOpens` (the unit disc with the charts of an open subset of `ℂ`) every preferred
chart has target `Δ`. -/
theorem s25d_chart_target (x : unitDiscOpens) : (chartAt ℂ x).target = unitDisc := by
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def]
  ext z
  simp [mfld_simps, chartAt_self_eq]
  rfl

/-- On `unitDiscOpens` every chart transition is the identity on `Δ` (the charts are restrictions
of the identity of `ℂ`). -/
theorem s25d_chartTransition_eq (x y : unitDiscOpens) {z : ℂ} (hz : z ∈ unitDisc) :
    chartTransition x y z = z := by
  have hy : z ∈ (chartAt ℂ y).target := by rw [s25d_chart_target]; exact hz
  have h := (chartAt ℂ (y : ℂ)).subtypeRestr_symm_apply (U := unitDiscOpens) ⟨y⟩ hy
  simpa [chartTransition, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq] using h

/-- On `unitDiscOpens` the chart transitions have derivative `1` at every point of `Δ`. -/
theorem s25d_deriv_chartTransition (x y : unitDiscOpens) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv (chartTransition x y) z = 1 := by
  have h : chartTransition x y =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw => s25d_chartTransition_eq x y hw
  rw [h.deriv_eq, deriv_id]

/-- The quadratic differential `zⁿ dz²` on `Δ`: the coefficient `zⁿ` on `Δ` in every chart (zero
off `Δ`). -/
def s25d_q (n : ℕ) : unitDiscOpens → ℂ → ℂ :=
  fun _ z => unitDisc.indicator (fun w : ℂ => w ^ n) z

/-- `zⁿ dz²` is a holomorphic quadratic differential on `Δ`: the transformation law reads
`q_y(z) = q_x(z)` since every chart transition is the identity near `z`. -/
theorem s25d_q_mem (n : ℕ) : s25d_q n ∈ holQuadDiffSubmodule unitDiscOpens := by
  refine ⟨⟨fun x z hz => ?_, fun x y z hz _ => ?_⟩, fun x => ?_⟩
  · rw [s25d_chart_target] at hz
    exact Set.indicator_of_notMem hz _
  · rw [s25d_chart_target] at hz
    rw [s25d_deriv_chartTransition x y hz, s25d_chartTransition_eq x y hz]
    simp [s25d_q]
  · rw [s25d_chart_target]
    exact (differentiableOn_pow n).congr fun z hz => Set.indicator_of_mem hz _

/-- The functions `zⁿ` restricted to `Δ` (zero off `Δ`) are linearly independent: a vanishing
finite combination is a polynomial with infinitely many roots. -/
theorem s25d_linearIndependent :
    LinearIndependent ℂ (fun n : ℕ => unitDisc.indicator (fun w : ℂ => w ^ n)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  set p : Polynomial ℂ := ∑ j ∈ s, Polynomial.C (g j) * Polynomial.X ^ j with hp
  have hroot : ∀ z ∈ unitDisc, p.IsRoot z := by
    intro z hz
    have h := congr_fun hg z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Set.indicator_of_mem hz] at h
    simp [hp, Polynomial.eval_finsetSum, h]
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((infinite_of_mem_nhds (0 : ℂ) (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mono hroot)
  have h := congr_arg (fun q => Polynomial.coeff q i) hp0
  simpa [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hi] using h

/-- §25.3: for an open Riemann surface (here: the unit disc) `Q(S)` is infinite dimensional. -/
theorem sec25_3_dim_open_infinite : ¬ Module.Finite ℂ (holQuadDiffSubmodule unitDiscOpens) := by
  intro hfin
  let v : ℕ → holQuadDiffSubmodule unitDiscOpens := fun n => ⟨s25d_q n, s25d_q_mem n⟩
  let x₀ : unitDiscOpens := ⟨0, mem_ball_self one_pos⟩
  let L : holQuadDiffSubmodule unitDiscOpens →ₗ[ℂ] ℂ → ℂ :=
    (LinearMap.proj x₀).comp (holQuadDiffSubmodule unitDiscOpens).subtype
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp L s25d_linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite v hv

/-- §25.3: for a compact Riemann surface of genus `1`, `Q(S)` is one dimensional over `ℂ` (two
dimensional over `ℝ`); this follows from the uniformization theorem. -/
theorem sec25_3_dim_genus_one [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (hS : HasGenus S 1) :
    Module.finrank ℂ (holQuadDiffSubmodule S) = 1 ∧ Module.finrank ℝ (holQuadDiffSubmodule S) = 2 := by
  classical
  letI : CompactSpace S := hS.1
  have hK : IsCanonicalDivisor (0 : Divisor S) := k25g1_zero_canonical hS
  obtain ⟨e⟩ := k22q_canonical_equiv hK
  have hcomplex : Module.finrank ℂ (holQuadDiffSubmodule S) = 1 := by
    calc
      Module.finrank ℂ (holQuadDiffSubmodule S) =
          Module.finrank ℂ (meroFunctionSpace (2 • (0 : Divisor S))) := e.finrank_eq.symm
      _ = 1 := by
        rw [smul_zero]
        change ellDim (0 : Divisor S) = 1
        rw [k22rr_ellDim_eq_lDim]
        exact Jacobians.lDim_zero_eq_one
  refine ⟨hcomplex, ?_⟩
  rw [finrank_real_of_complex, hcomplex]

/-- §25.3: for a compact Riemann surface of genus `g > 1`, `Q(S)` has real dimension `6g - 6` and
complex dimension `3g - 3` (Theorem 22.5). -/
theorem sec25_3_dim_genus_gt_one [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) :
    Module.finrank ℝ (holQuadDiffSubmodule S) = 6 * g - 6 ∧
      Module.finrank ℂ (holQuadDiffSubmodule S) = 3 * g - 3 := by
  letI : CompactSpace S := hS.1
  letI : FiniteDimensional ℂ (holQuadDiffSubmodule S) := k22q_finite_quadratic (S := S)
  have hcomplex := thm22_5_dim_quadratic_differentials hg hS
  refine ⟨?_, hcomplex⟩
  rw [finrank_real_of_complex, hcomplex]
  omega

/-- §25.3 (the Riemann–Roch computation).  Let `ψ₀ dz` be a holomorphic differential with divisor
`α = (ψ₀ dz)`, `deg α = 2(g - 1)`.  Riemann–Roch gives `dim D[-α] = dim D₀[α] + 3g - 3` and
`dim D₀[α] = 0` (a non-zero meromorphic function `f` with `(f) ≥ α` would have `deg (f) > 0`), so
`dim D[-α] = 3g - 3`; and `ψ dz ↦ ψ ψ₀ dz²` is an isomorphism `D[-α] → Q(S)`.  In the notation of
§22.5 (`meroFunctionSpace β = {f : (f) ≥ -β}`), `D[-α] ≅ D₀[-2α]`, so `ℓ(2α) = 3g - 3` and
`ℓ(-α) = 0`. -/
theorem sec25_3_riemann_roch_computation [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {α : Divisor S} (hα : IsCanonicalDivisor α)
    (hhol : ∀ x, 0 ≤ α x) :
    α.deg = 2 * ((g : ℤ) - 1) ∧ ellDim (-α) = 0 ∧ ellDim (2 • α) = 3 * g - 3 ∧
      Module.finrank ℂ (holQuadDiffSubmodule S) = ellDim (2 • α) := by
  -- Effectivity is redundant for this numerical computation; retain the frozen hypothesis.
  have _hhol := hhol
  letI : CompactSpace S := hS.1
  have hdeg := deg_canonical hS hα
  have hnegdeg : Jacobians.Divisor.deg S (-α) < 0 := by
    rw [map_neg, k22rr_degree_eq, hdeg]
    omega
  have hneg : ellDim (-α) = 0 := by
    rw [k22rr_ellDim_eq_lDim]
    exact Jacobians.lDim_eq_zero_of_deg_neg (-α) hnegdeg
  have hsub : α - 2 • α = -α := by
    simp only [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hdegdouble : (2 • α).deg = 2 * α.deg := by
    change Jacobians.Divisor.deg S (2 • α) = 2 * Jacobians.Divisor.deg S α
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      (map_nsmul (Jacobians.Divisor.deg S) 2 α)
  have hrr2 := thm22_4_riemann_roch hS hα (2 • α)
  rw [hsub, hneg, hdegdouble, hdeg] at hrr2
  have hdim : ellDim (2 • α) = 3 * g - 3 := by omega
  refine ⟨by omega, hneg, hdim, ?_⟩
  exact (thm22_5_dim_quadratic_differentials hg hS).trans hdim.symm

end LiZhongQC
