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
  sorry

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

/-- **Theorem 25.3** (uniqueness of geodesics).  Let `φ ≢ 0` be holomorphic in the unit disc (the
universal covering of a Riemann surface with hyperbolic universal covering, to which a
quadratic differential and homotopic curves with common end points are lifted).  Two
`φ`-geodesics with the same end points have the same trace.

**Correction.**  The geodesics are assumed not to pause (`hp₁`, `hp₂`).  Without this the statement was
**false**: `IsPhiGeodesic` only constrains short windows around each time, so a curve may go out, pause,
and come back — such a spike from `0` to `0` and the constant curve at `0` are both geodesics, with
different traces. -/
theorem thm25_3_unique_geodesic {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {γ₁ γ₂ : LRCurve} (h₁ : IsPhiGeodesic φ unitDisc γ₁)
    (h₂ : IsPhiGeodesic φ unitDisc γ₂) (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1) :
    γ₁.closedTrace = γ₂.closedTrace := by
  sorry

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

/-- §25.2: every point `p` of a Riemann surface has a neighbourhood `V_p` in which any two points are
joined by a shortest curve of the `φ`-metric (a `φ`-straight segment in a natural parameter, or a
broken `φ`-straight arc through a zero). -/
theorem exists_local_shortest_nbhd [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ V ∈ 𝓝 p, ∀ a ∈ V, ∀ b ∈ V, ∃ γ : Path a b, (∀ t, γ t ∈ V) ∧
      phiLengthPath q γ = phiDistRS q a b := by
  sorry

/-- **Theorem 25.4**: let `φ dz² ≢ 0` be a holomorphic quadratic differential on a compact Riemann
surface `S`.  For any two points `p₁, p₂` and any curve `α` joining them, the homotopy class `[α]`
contains a curve of minimal `φ`-length. -/
theorem thm25_4_shortest_exists [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p₁ p₂ : S} (α : Path p₁ p₂) :
    ∃ γ : Path p₁ p₂, γ.Homotopic α ∧ ∀ γ' : Path p₁ p₂, γ'.Homotopic α →
      phiLengthPath q γ ≤ phiLengthPath q γ' := by
  sorry

/-- §25.2 (remark after Theorem 25.4): a shortest curve in a homotopy class is a `φ`-geodesic. -/
theorem shortest_isPhiGeodesicRS [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p₁ p₂ : S} {γ : Path p₁ p₂}
    (hγ : ∀ γ' : Path p₁ p₂, γ'.Homotopic γ → phiLengthPath q γ ≤ phiLengthPath q γ')
    (hfin : phiLengthPath q γ < ⊤) : IsPhiGeodesicRS q γ := by
  sorry

/-- **Corollary of Theorems 25.3 and 25.4**: on a closed Riemann surface of genus `g > 1`, every
homotopy class of curves with given end points contains exactly one `φ`-geodesic (up to
reparametrization: two geodesics in the class have the same trace).

**Correction.**  In the uniqueness half the geodesics are assumed not to pause; without this it was
**false**, for the same reason as Theorem 25.3 (`IsPhiGeodesicRS` allows a curve to go out, pause and
come back).  The existence half is unchanged. -/
theorem thm25_4_cor_unique_geodesic [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {p₁ p₂ : S} (α : Path p₁ p₂) :
    (∃ γ : Path p₁ p₂, γ.Homotopic α ∧ IsPhiGeodesicRS q γ) ∧
      ∀ γ₁ γ₂ : Path p₁ p₂, γ₁.Homotopic α → γ₂.Homotopic α → IsPhiGeodesicRS q γ₁ →
        IsPhiGeodesicRS q γ₂ → (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s) →
        (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) → range γ₁ = range γ₂ := by
  sorry

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
  sorry

/-- §25.3: for a compact Riemann surface of genus `g > 1`, `Q(S)` has real dimension `6g - 6` and
complex dimension `3g - 3` (Theorem 22.5). -/
theorem sec25_3_dim_genus_gt_one [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) :
    Module.finrank ℝ (holQuadDiffSubmodule S) = 6 * g - 6 ∧
      Module.finrank ℂ (holQuadDiffSubmodule S) = 3 * g - 3 := by
  sorry

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
  sorry

end LiZhongQC
