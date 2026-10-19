import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.S34mOsgood

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

/-! R83 S34 (精英下属5): banked `s34m_` pieces for `bersQuotient_manifold` (statements as frozen in IFACE_S34). -/

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The coordinate image `{e(φ_μ)}` of `T_{G₀}` under a linear coordinate system `e` of `Q(G₀, 𝕃)` is open
(Theorem 33.1 and the comparison of `‖·‖_𝕃` with `‖e(·)‖`). -/
theorem s34m_range_open (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) :
    IsOpen (range fun μ : BeltramiGamma Γ => e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) := by
  have hrange : (range fun μ : BeltramiGamma Γ => e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) =
      range fun t : TeichGamma Γ => e (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ) := by
    ext v
    constructor
    · rintro ⟨μ, rfl⟩
      refine ⟨Quotient.mk _ μ, ?_⟩
      have h := (bersMapGamma_mem hΓ (Quotient.mk _ μ)).2.2 μ rfl
      have h' : (⟨bersMapGamma Γ (Quotient.mk _ μ), (bersMapGamma_mem hΓ _).1⟩ : automorphicQD Γ) =
          ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ := Subtype.ext h.symm
      simp only [h']
    · rintro ⟨t, rfl⟩
      exact ⟨Quotient.out t, rfl⟩
  rw [hrange]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    convert isOpen_univ
    refine eq_univ_of_forall fun v => ?_
    obtain ⟨t⟩ : Nonempty (TeichGamma Γ) := ⟨TeichGamma.origin Γ⟩
    exact ⟨t, Subsingleton.elim _ _⟩
  · obtain ⟨a, b, -, hb, hcompare⟩ := s33dim_coordinate_comparison hm e hfin
    exact s33dim_coords_open hΓ e hb fun φ => (hcompare φ).2

/-- The upper comparison of `‖·‖_𝕃` with linear coordinates, on Bers points. -/
theorem s34m_upper (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) :
    ∃ b > 0, ∀ μ ν : BeltramiGamma Γ, bersNormL (bersFunctionGamma μ - bersFunctionGamma ν) ≤
      ENNReal.ofReal (b * ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
        e ⟨bersFunctionGamma ν, (bersFunctionGamma_mem hΓ ν).1⟩‖) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, one_pos, fun μ ν => ?_⟩
    have h : (⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ : automorphicQD Γ) =
        ⟨bersFunctionGamma ν, (bersFunctionGamma_mem hΓ ν).1⟩ := e.injective (Subsingleton.elim _ _)
    have h' : bersFunctionGamma μ = bersFunctionGamma ν := congrArg Subtype.val h
    have hz : bersFunctionGamma μ - bersFunctionGamma ν = 0 := by rw [h', sub_self]
    rw [hz]
    have h0 : bersNormL (0 : ℂ → ℂ) = 0 := by simp [bersNormL]
    rw [h0]
    exact bot_le
  · obtain ⟨a, b, -, hb, hcompare⟩ := s33dim_coordinate_comparison hm e hfin
    refine ⟨b, hb, fun μ ν => ?_⟩
    have h := (hcompare (⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
      ⟨bersFunctionGamma ν, (bersFunctionGamma_mem hΓ ν).1⟩)).2
    rw [map_sub] at h
    exact h

/-- Möbius invariance of the cross ratio `CR(w, a, b, c) = ((w - a)(b - c))/((w - c)(b - a))` (all points finite with
finite images). -/
theorem s34m_cr_mob {α β γ δ w a b c : ℂ} (hdet : α * δ - β * γ ≠ 0) (hw : γ * w + δ ≠ 0) (ha : γ * a + δ ≠ 0)
    (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hwc : w ≠ c) (hba : b ≠ a) :
    ((((α * w + β) / (γ * w + δ)) - (α * a + β) / (γ * a + δ)) *
        ((α * b + β) / (γ * b + δ) - (α * c + β) / (γ * c + δ))) /
      ((((α * w + β) / (γ * w + δ)) - (α * c + β) / (γ * c + δ)) *
        ((α * b + β) / (γ * b + δ) - (α * a + β) / (γ * a + δ))) =
      ((w - a) * (b - c)) / ((w - c) * (b - a)) := by
  have key : ∀ x y : ℂ, γ * x + δ ≠ 0 → γ * y + δ ≠ 0 →
      (α * x + β) / (γ * x + δ) - (α * y + β) / (γ * y + δ) =
        (α * δ - β * γ) * (x - y) / ((γ * x + δ) * (γ * y + δ)) := by
    intro x y hx hy
    rw [div_sub_div _ _ hx hy]
    congr 1
    ring
  rw [key w a hw ha, key b c hb hc, key w c hw hc, key b a hb ha]
  have h1 : w - c ≠ 0 := sub_ne_zero.2 hwc
  have h2 : b - a ≠ 0 := sub_ne_zero.2 hba
  field_simp

/-- The inverse of `w ↦ CR(w, a, b, c)`: `Ψ(u) = (a(b - c) - u c(b - a))/((b - c) - u(b - a))`. -/
theorem s34m_cr_inv {w a b c : ℂ} (hwc : w ≠ c) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    (a * (b - c) - ((w - a) * (b - c)) / ((w - c) * (b - a)) * c * (b - a)) /
        ((b - c) - ((w - a) * (b - c)) / ((w - c) * (b - a)) * (b - a)) = w := by
  have h1 : w - c ≠ 0 := sub_ne_zero.2 hwc
  have h2 : b - a ≠ 0 := sub_ne_zero.2 hba
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  have hden : (b - c) - ((w - a) * (b - c)) / ((w - c) * (b - a)) * (b - a) = (b - c) * (a - c) / (w - c) := by
    field_simp
    ring
  have h4 : a - c ≠ 0 := sub_ne_zero.2 hac
  rw [hden]
  field_simp
  ring

/-- The value at `∞`: `CR(N(∞), N a, N b, N c) = (b - c)/(b - a)` for `N(∞) = α/γ`. -/
theorem s34m_cr_mob_inf {α β γ δ a b c : ℂ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0) (ha : γ * a + δ ≠ 0)
    (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hba : b ≠ a) :
    ((α / γ - (α * a + β) / (γ * a + δ)) * ((α * b + β) / (γ * b + δ) - (α * c + β) / (γ * c + δ))) /
      ((α / γ - (α * c + β) / (γ * c + δ)) * ((α * b + β) / (γ * b + δ) - (α * a + β) / (γ * a + δ))) =
      (b - c) / (b - a) := by
  have key : ∀ x y : ℂ, γ * x + δ ≠ 0 → γ * y + δ ≠ 0 →
      (α * x + β) / (γ * x + δ) - (α * y + β) / (γ * y + δ) =
        (α * δ - β * γ) * (x - y) / ((γ * x + δ) * (γ * y + δ)) := by
    intro x y hx hy
    rw [div_sub_div _ _ hx hy]
    congr 1
    ring
  have keyinf : ∀ x : ℂ, γ * x + δ ≠ 0 → α / γ - (α * x + β) / (γ * x + δ) = (α * δ - β * γ) / (γ * (γ * x + δ)) := by
    intro x hx
    rw [div_sub_div _ _ hγ hx]
    congr 1
    ring
  rw [keyinf a ha, key b c hb hc, keyinf c hc, key b a hb ha]
  have h2 : b - a ≠ 0 := sub_ne_zero.2 hba
  field_simp

/-- The `∞`-normalization: `CR(N w, N 0, N 1, N ∞) = w` for a Möbius map `N` with finite `N 0, N 1, N ∞`. -/
theorem s34m_cr_norm {α β γ δ w : ℂ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0) (h1 : γ + δ ≠ 0)
    (hw : γ * w + δ ≠ 0) :
    ((((α * w + β) / (γ * w + δ)) - β / δ) * ((α + β) / (γ + δ) - α / γ)) /
      ((((α * w + β) / (γ * w + δ)) - α / γ) * ((α + β) / (γ + δ) - β / δ)) = w := by
  have e1 : (α * w + β) / (γ * w + δ) - β / δ = (α * δ - β * γ) * w / ((γ * w + δ) * δ) := by
    rw [div_sub_div _ _ hw hδ]
    congr 1
    ring
  have e2 : (α + β) / (γ + δ) - α / γ = -(α * δ - β * γ) / ((γ + δ) * γ) := by
    rw [div_sub_div _ _ h1 hγ]
    congr 1
    ring
  have e3 : (α * w + β) / (γ * w + δ) - α / γ = -(α * δ - β * γ) / ((γ * w + δ) * γ) := by
    rw [div_sub_div _ _ hw hγ]
    congr 1
    ring
  have e4 : (α + β) / (γ + δ) - β / δ = (α * δ - β * γ) / ((γ + δ) * δ) := by
    rw [div_sub_div _ _ h1 hδ]
    congr 1
    ring
  rw [e1, e2, e3, e4]
  field_simp

/-- For solutions `y₁, y₂` of `y'' + (φ/2) y = 0` on a connected open `D` with Wronskian `1` at one point, the
Wronskian is `1` on `D`, `y₁/y₂` is locally univalent meromorphic on `D` and `S_{y₁/y₂} = φ` (the argument of
`eq19_2_ode`, for given solutions). -/
theorem s34m_ratio_props {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {y₁ y₂ φ : ℂ → ℂ}
    (hw₁ : DifferentiableOn ℂ y₁ D) (hw₂ : DifferentiableOn ℂ y₂ D)
    (hode₁ : ∀ z ∈ D, deriv (deriv y₁) z = -(φ z / 2) * y₁ z)
    (hode₂ : ∀ z ∈ D, deriv (deriv y₂) z = -(φ z / 2) * y₂ z) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (hW₀ : y₁ z₀ * deriv y₂ z₀ - y₂ z₀ * deriv y₁ z₀ = 1) :
    (∀ z ∈ D, y₁ z * deriv y₂ z - y₂ z * deriv y₁ z = 1) ∧
      IsLocUnivMero (fun z => y₁ z / y₂ z) D ∧ ∀ z ∈ D, schwarzian (fun z => y₁ z / y₂ z) z = φ z := by
  have hW : ∀ z ∈ D, y₁ z * deriv y₂ z - y₂ z * deriv y₁ z = 1 := by
    have hd₁ : DifferentiableOn ℂ (deriv y₁) D := hw₁.deriv hD
    have hd₂ : DifferentiableOn ℂ (deriv y₂) D := hw₂.deriv hD
    have hWd : DifferentiableOn ℂ (fun z => y₁ z * deriv y₂ z - y₂ z * deriv y₁ z) D :=
      (hw₁.mul hd₂).sub (hw₂.mul hd₁)
    have hW' : EqOn (deriv fun z => y₁ z * deriv y₂ z - y₂ z * deriv y₁ z) 0 D := by
      intro z hz
      have hn := hD.mem_nhds hz
      have h : HasDerivAt (fun z => y₁ z * deriv y₂ z - y₂ z * deriv y₁ z) _ z :=
        ((hw₁.differentiableAt hn).hasDerivAt.mul (hd₂.differentiableAt hn).hasDerivAt).sub
          ((hw₂.differentiableAt hn).hasDerivAt.mul (hd₁.differentiableAt hn).hasDerivAt)
      rw [h.deriv, hode₁ z hz, hode₂ z hz]
      simp only [Pi.zero_apply]
      ring
    intro z hz
    have h := hD.is_const_of_deriv_eq_zero hDc.isPreconnected hWd hW' hz hz₀
    rw [h, hW₀]
  have han₁ : ∀ z ∈ D, AnalyticAt ℂ y₁ z := fun z hz => hw₁.analyticAt (hD.mem_nhds hz)
  have han₂ : ∀ z ∈ D, AnalyticAt ℂ y₂ z := fun z hz => hw₂.analyticAt (hD.mem_nhds hz)
  have hne2 : ∀ z ∈ D, y₂ z ≠ 0 → AnalyticAt ℂ (fun z => y₁ z / y₂ z) z ∧
      deriv (fun z => y₁ z / y₂ z) z ≠ 0 ∧ schwarzian (fun z => y₁ z / y₂ z) z = φ z := by
    intro z hz h2
    have hU : IsOpen (D ∩ y₂ ⁻¹' {0}ᶜ) :=
      hw₂.continuousOn.isOpen_inter_preimage hD isOpen_compl_singleton
    have hderiv : ∀ y ∈ D ∩ y₂ ⁻¹' {0}ᶜ, deriv (fun z => y₁ z / y₂ z) y = -1 / y₂ y ^ 2 := by
      intro y hy
      have hy2 : y₂ y ≠ 0 := hy.2
      have hn := hD.mem_nhds hy.1
      have h : HasDerivAt (fun z => y₁ z / y₂ z) _ y :=
        (hw₁.differentiableAt hn).hasDerivAt.div (hw₂.differentiableAt hn).hasDerivAt hy2
      rw [h.deriv, div_left_inj' (pow_ne_zero 2 hy2)]
      linear_combination -hW y hy.1
    have hfa : AnalyticAt ℂ (fun z => y₁ z / y₂ z) z := (han₁ z hz).div (han₂ z hz) h2
    refine ⟨hfa, ?_, ?_⟩
    · rw [hderiv z ⟨hz, h2⟩]
      exact div_ne_zero (by norm_num) (pow_ne_zero 2 h2)
    · rw [schwarzian_of_analyticAt hfa]
      exact schwarzianHol_eq_of_deriv_eq_const_div_sq hU ⟨hz, h2⟩ (by norm_num)
        (hw₂.mono inter_subset_left) (fun y hy => hy.2) hderiv (fun y hy => hode₂ y hy.1)
  have heq2 : ∀ z ∈ D, y₂ z = 0 →
      (meromorphicOrderAt (fun z => y₁ z / y₂ z) z < 0 ∧
        AnalyticAt ℂ (fun w => (toMeromorphicNFAt (fun z => y₁ z / y₂ z) z w)⁻¹) z ∧
        deriv (fun w => (toMeromorphicNFAt (fun z => y₁ z / y₂ z) z w)⁻¹) z ≠ 0) ∧
      schwarzian (fun z => y₁ z / y₂ z) z = φ z := by
    intro z hz h2
    have hWz := hW z hz
    have h1 : y₁ z ≠ 0 := by
      intro h
      rw [h, h2] at hWz
      simp at hWz
    have hGa : AnalyticAt ℂ (fun y => y₂ y / y₁ y) z := (han₂ z hz).div (han₁ z hz) h1
    have hfG : (fun z => y₁ z / y₂ z) = fun y => (y₂ y / y₁ y)⁻¹ := by
      funext y
      rw [inv_div]
    have hU : IsOpen (D ∩ y₁ ⁻¹' {0}ᶜ) :=
      hw₁.continuousOn.isOpen_inter_preimage hD isOpen_compl_singleton
    have hGderiv : ∀ y ∈ D ∩ y₁ ⁻¹' {0}ᶜ, deriv (fun y => y₂ y / y₁ y) y = 1 / y₁ y ^ 2 := by
      intro y hy
      have hy1 : y₁ y ≠ 0 := hy.2
      have hn := hD.mem_nhds hy.1
      have h : HasDerivAt (fun y => y₂ y / y₁ y) _ y :=
        (hw₂.differentiableAt hn).hasDerivAt.div (hw₁.differentiableAt hn).hasDerivAt hy1
      rw [h.deriv, div_left_inj' (pow_ne_zero 2 hy1)]
      linear_combination hW y hy.1
    have hG0 : (fun y => y₂ y / y₁ y) z = 0 := by simp [h2]
    have hG' : deriv (fun y => y₂ y / y₁ y) z ≠ 0 := by
      rw [hGderiv z ⟨hz, h1⟩]
      exact div_ne_zero one_ne_zero (pow_ne_zero 2 h1)
    have hord1 : meromorphicOrderAt (fun y => y₂ y / y₁ y) z = 1 := by
      rw [hGa.meromorphicOrderAt_eq, hGa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hG0 hG']
      rfl
    have hord : meromorphicOrderAt (fun y => (y₂ y / y₁ y)⁻¹) z = -1 := by
      show meromorphicOrderAt (fun y => y₂ y / y₁ y)⁻¹ z = -1
      rw [meromorphicOrderAt_inv, hord1]
    have hNF : toMeromorphicNFAt (fun y => (y₂ y / y₁ y)⁻¹) z = fun y => (y₂ y / y₁ y)⁻¹ :=
      (toMeromorphicNFAt_eq_self (f := fun y => (y₂ y / y₁ y)⁻¹) (x := z)).mpr
        hGa.meromorphicNFAt.inv
    rw [hfG, hNF]
    simp only [inv_inv]
    refine ⟨⟨by rw [hord]; decide, hGa, hG'⟩, ?_⟩
    rw [schwarzian_inv_of_simple_zero hGa hG0 hG', schwarzian_of_analyticAt hGa]
    exact schwarzianHol_eq_of_deriv_eq_const_div_sq hU ⟨hz, h1⟩ one_ne_zero
      (hw₁.mono inter_subset_left) (fun y hy => hy.2) hGderiv (fun y hy => hode₁ y hy.1)
  refine ⟨hW, ⟨fun z hz => (han₁ z hz).meromorphicAt.div (han₂ z hz).meromorphicAt, fun z hz => ?_⟩,
    fun z hz => ?_⟩
  · by_cases h2 : y₂ z = 0
    · exact Or.inr (heq2 z hz h2).1
    · exact Or.inl ⟨(hne2 z hz h2).1, (hne2 z hz h2).2.1⟩
  · by_cases h2 : y₂ z = 0
    · exact (heq2 z hz h2).2
    · exact (hne2 z hz h2).2.2

/-- `f_μ` on `Im z ≤ 0` depends only on `φ_μ` (`ut_welding`). -/
theorem s34m_eq_lower {μ ν : BeltramiGamma Γ} (h : bersFunctionGamma μ = bersFunctionGamma ν) {z : ℂ}
    (hz : z.im ≤ 0) : normalizedSolution μ.1.1 z = normalizedSolution ν.1.1 z := by
  have hS : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution μ.1.1) z =
      schwarzian (normalizedSolution ν.1.1) z := by
    intro z hz
    have h1 := congrFun h z
    simp only [bersFunctionGamma, bersFunction, indicator_of_mem hz] at h1
    exact h1
  exact (ut_welding (bA_equiv_of_schwarzian_eq hS)).1 z hz

/-- `e(φ_{μₙ}) → e(φ_μ)` gives Bers convergence `‖φ_{μₙ} - φ_μ‖_𝕃 → 0`, hence (`normalizedSolution_tendsto_of_bers`)
representatives `νₙ ∼ μₙ` with `f_{νₙ} → f_μ` locally uniformly; `f_{νₙ} = f_{μₙ}` on `Im z ≤ 0`. -/
theorem s34m_conv_reps (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) {μs : ℕ → BeltramiGamma Γ} {μ : BeltramiGamma Γ}
    (ht : Tendsto (fun n => e ⟨bersFunctionGamma (μs n), (bersFunctionGamma_mem hΓ (μs n)).1⟩) atTop
      (𝓝 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩))) :
    ∃ νs : ℕ → BeltramiGamma Γ, (∀ n, ∀ z : ℂ, z.im ≤ 0 → normalizedSolution (νs n).1.1 z =
      normalizedSolution (μs n).1.1 z) ∧
      ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun n => normalizedSolution (νs n).1.1)
        (normalizedSolution μ.1.1) atTop K := by
  obtain ⟨b, hb, hup⟩ := s34m_upper hΓ e hfin
  have hconv : Tendsto (fun n => bersNormL (bersFunctionGamma (μs n) - bersFunctionGamma μ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖e ⟨bersFunctionGamma (μs n), (bersFunctionGamma_mem hΓ (μs n)).1⟩ -
        e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero).1 ht
      exact this
    have hb0 : Tendsto (fun n => ENNReal.ofReal (b * ‖e ⟨bersFunctionGamma (μs n), (bersFunctionGamma_mem hΓ (μs n)).1⟩ -
        e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩‖)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      simpa using h1.const_mul b
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0 (fun n => bot_le) (fun n => hup _ _)
  obtain ⟨νs, hνμ, -, hunif⟩ := normalizedSolution_tendsto_of_bers hΓ hconv
  exact ⟨νs, fun n z hz => s34m_eq_lower (bersFunctionGamma_eq_of_equiv (hνμ n)) hz, hunif⟩

/-- **Joint continuity of `(φ, z) ↦ f_φ(z)` on `Im z ≤ 0`** (sequential form). -/
theorem s34m_jc (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) {μs : ℕ → BeltramiGamma Γ} {μ : BeltramiGamma Γ}
    (ht : Tendsto (fun n => e ⟨bersFunctionGamma (μs n), (bersFunctionGamma_mem hΓ (μs n)).1⟩) atTop
      (𝓝 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩)))
    {zs : ℕ → ℂ} {z : ℂ} (hzs : ∀ n, (zs n).im ≤ 0) (hz : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => normalizedSolution (μs n).1.1 (zs n)) atTop (𝓝 (normalizedSolution μ.1.1 z)) := by
  obtain ⟨νs, heq, hunif⟩ := s34m_conv_reps hΓ e hfin ht
  have hc : Continuous (normalizedSolution μ.1.1) := by
    obtain ⟨e', he'⟩ := b34_b_homeo μ.1
    rw [← he']
    exact e'.continuous
  have h := (hunif (closedBall z 1) (isCompact_closedBall z 1)).tendsto_comp hc.continuousWithinAt
    (tendsto_nhdsWithin_iff.2 ⟨hz, (hz.eventually (closedBall_mem_nhds z one_pos)).mono fun n hn => hn⟩)
  exact h.congr fun n => heq n (zs n) (hzs n)

/-- **Uniform properness on `Im z ≤ 0`** (sequential form): `zₙ → ∞` gives `f_{φₙ}(zₙ) → ∞` (inverse convergence,
`b34_b_inv_tendsto`). -/
theorem s34m_jc_inf (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) {μs : ℕ → BeltramiGamma Γ} {μ : BeltramiGamma Γ}
    (ht : Tendsto (fun n => e ⟨bersFunctionGamma (μs n), (bersFunctionGamma_mem hΓ (μs n)).1⟩) atTop
      (𝓝 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩)))
    {zs : ℕ → ℂ} (hzs : ∀ n, (zs n).im ≤ 0) (hz : Tendsto (fun n => ‖zs n‖) atTop atTop) :
    Tendsto (fun n => ‖normalizedSolution (μs n).1.1 (zs n)‖) atTop atTop := by
  obtain ⟨νs, heq, hunif⟩ := s34m_conv_reps hΓ e hfin ht
  have hhom : ∀ μ : BeltramiH, IsOpenMap (normalizedSolution μ.1) ∧ Continuous (normalizedSolution μ.1) ∧
      Function.Bijective (normalizedSolution μ.1) := fun μ => by
    obtain ⟨e', he'⟩ := b34_b_homeo μ
    rw [← he']
    exact ⟨e'.isOpenMap, e'.continuous, e'.bijective⟩
  rw [Filter.tendsto_atTop]
  intro C
  by_contra hcon
  rw [not_eventually] at hcon
  -- a subsequence with `‖f(zₙ)‖ < C`, then a convergent one
  obtain ⟨φ₁, hφ₁, hlt⟩ := extraction_of_frequently_atTop hcon
  have hbd : ∀ n, normalizedSolution (νs (φ₁ n)).1.1 (zs (φ₁ n)) ∈ closedBall (0 : ℂ) C := by
    intro n
    rw [mem_closedBall, dist_zero_right, heq _ _ (hzs _)]
    exact (not_le.1 (hlt n)).le
  obtain ⟨w₀, -, φ₂, hφ₂, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbd
  obtain ⟨v₀, hv₀⟩ := (hhom μ.1).2.2.2 w₀
  have hmono : StrictMono (φ₁ ∘ φ₂) := hφ₁.comp hφ₂
  have hconv' : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun n => normalizedSolution (νs ((φ₁ ∘ φ₂) n)).1.1)
      (normalizedSolution μ.1.1) atTop K := fun K hK u hu => hmono.tendsto_atTop.eventually (hunif K hK u hu)
  have hw := b34_b_inv_tendsto (F := fun n => normalizedSolution (νs ((φ₁ ∘ φ₂) n)).1.1)
    (f := normalizedSolution μ.1.1) (fun n => (hhom _).1) (fun n => (hhom _).2.1) (fun n => (hhom _).2.2.1)
    (hhom μ.1).2.1 (hhom μ.1).2.2.1 hconv'
    (z := fun n => normalizedSolution (νs ((φ₁ ∘ φ₂) n)).1.1 (zs ((φ₁ ∘ φ₂) n)))
    (w := fun n => zs ((φ₁ ∘ φ₂) n)) (by rw [hv₀]; exact hlim) (fun n => rfl)
  have h1 := (hz.comp hmono.tendsto_atTop).eventually (eventually_gt_atTop (‖v₀‖ + 1))
  have h2 := hw.norm.eventually (gt_mem_nhds (lt_add_one ‖v₀‖))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  simp only [Function.comp_apply] at hn1 hn2
  linarith

/-- A uniform limit of analytic functions on an open subset of `ℂᵐ` is analytic. -/
theorem s34m_analytic_of_tendstoUniformlyOn {m : ℕ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    {F : ℕ → (Fin m → ℂ) → ℂ} {f : (Fin m → ℂ) → ℂ} (hF : ∀ N, AnalyticOnNhd ℂ (F N) U)
    (h : TendstoUniformlyOn F f atTop U) : AnalyticOnNhd ℂ f U := by
  refine s34m_osgood hU (h.continuousOn (Eventually.of_forall fun N => (hF N).continuousOn).frequently) ?_
  intro x hx i
  have hcont : Continuous fun s : ℂ => Function.update x i s := continuous_const.update i continuous_id
  have hVo : IsOpen ((fun s : ℂ => Function.update x i s) ⁻¹' U) := hU.preimage hcont
  have hxV : x i ∈ (fun s : ℂ => Function.update x i s) ⁻¹' U := by
    simp only [mem_preimage, Function.update_eq_self]
    exact hx
  have hT := (h.comp fun s : ℂ => Function.update x i s).tendstoLocallyUniformlyOn
  have hd := hT.differentiableOn (Eventually.of_forall fun N => fun s hs =>
    (((hF N) _ hs).differentiableAt.comp s (hasFDerivAt_update x s).differentiableAt).differentiableWithinAt) hVo
  exact (hd (x i) hxV).differentiableAt (hVo.mem_nhds hxV)

/-- **Limits of analytic functions, sequential form.**  If `H k → G` along every sequence `tₙ → t` in a compact `K`
(`H (kₙ) (tₙ) - G (tₙ) → 0` for `kₙ ↑ ∞`), then the convergence is uniform on `K`, and `G` is analytic on the open
`B ⊆ K` where the `H k` are. -/
theorem s34m_limit_analytic {m : ℕ} {B K : Set (Fin m → ℂ)} (hB : IsOpen B) (hK : IsCompact K) (hBK : B ⊆ K)
    {H : ℕ → (Fin m → ℂ) → ℂ} {G : (Fin m → ℂ) → ℂ} (hH : ∀ k, AnalyticOnNhd ℂ (H k) B)
    (hseq : ∀ (ts : ℕ → Fin m → ℂ) (ks : ℕ → ℕ) (t : Fin m → ℂ), (∀ n, ts n ∈ K) → t ∈ K →
      Tendsto ts atTop (𝓝 t) → StrictMono ks → Tendsto (fun n => H (ks n) (ts n) - G (ts n)) atTop (𝓝 0)) :
    AnalyticOnNhd ℂ G B := by
  have hU : TendstoUniformlyOn H G atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨ks, hks, hk⟩ := extraction_of_frequently_atTop hcon
    simp only [not_forall, not_lt] at hk
    choose ts hts hge using hk
    obtain ⟨t, htK, φ, hφ, hlim⟩ := hK.tendsto_subseq hts
    have h := hseq (ts ∘ φ) (ks ∘ φ) t (fun n => hts _) htK hlim (hks.comp hφ)
    obtain ⟨n, hn⟩ := (h.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε by simpa using hε))).exists
    have := hge (φ n)
    rw [dist_eq_norm, norm_sub_rev] at this
    simp only [Function.comp_apply] at hn
    linarith
  exact s34m_analytic_of_tendstoUniformlyOn hB hH (hU.mono hBK)

/-- A nontrivial combination `c y₁ + d y₂` of two solutions with Wronskian `1` has isolated zeros: it is nonzero on a
punctured neighbourhood of every point. -/
theorem s34m_sol_ne {D : Set ℂ} (hD : IsOpen D) {y₁ y₂ : ℂ → ℂ} (hy₁ : DifferentiableOn ℂ y₁ D)
    (hy₂ : DifferentiableOn ℂ y₂ D) (hW : ∀ z ∈ D, y₁ z * deriv y₂ z - y₂ z * deriv y₁ z = 1) {c d : ℂ}
    (hcd : c ≠ 0 ∨ d ≠ 0) {z : ℂ} (hz : z ∈ D) : ∀ᶠ w in 𝓝[≠] z, c * y₁ w + d * y₂ w ≠ 0 := by
  have hn := hD.mem_nhds hz
  have hd₁ := (hy₁.differentiableAt hn).hasDerivAt
  have hd₂ := (hy₂.differentiableAt hn).hasDerivAt
  have hu : HasDerivAt (fun w => c * y₁ w + d * y₂ w) (c * deriv y₁ z + d * deriv y₂ z) z :=
    (hd₁.const_mul c).add (hd₂.const_mul d)
  by_cases h0 : c * y₁ z + d * y₂ z = 0
  · have h' : c * deriv y₁ z + d * deriv y₂ z ≠ 0 := by
      intro h1
      have hWz := hW z hz
      have hc : c = 0 := by linear_combination (deriv y₂ z) * h0 - y₂ z * h1 - c * hWz
      have hd : d = 0 := by linear_combination -(deriv y₁ z) * h0 + y₁ z * h1 - d * hWz
      rcases hcd with h | h
      · exact h hc
      · exact h hd
    exact hu.eventually_ne h'
  · exact nhdsWithin_le_nhds (hu.continuousAt.eventually_ne h0)

/-- **The cross-multiplied Möbius relation.**  If `f` is locally univalent on a connected open `D` with `S_f = φ`
and `y₁, y₂` solve `y'' + (φ/2) y = 0` with Wronskian `1`, then `f (γ y₁ + δ y₂) = α y₁ + β y₂` on `D` for some
`αδ - βγ ≠ 0` (Theorem 19.1 for `f` and `y₁/y₂`, extended over the zeros by continuity). -/
theorem s34m_xm {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {f y₁ y₂ φ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hfl : IsLocUnivMero f D) (hfS : ∀ z ∈ D, schwarzian f z = φ z)
    (hy₁ : DifferentiableOn ℂ y₁ D) (hy₂ : DifferentiableOn ℂ y₂ D)
    (hode₁ : ∀ z ∈ D, deriv (deriv y₁) z = -(φ z / 2) * y₁ z)
    (hode₂ : ∀ z ∈ D, deriv (deriv y₂) z = -(φ z / 2) * y₂ z)
    (hW : ∀ z ∈ D, y₁ z * deriv y₂ z - y₂ z * deriv y₁ z = 1) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧ ∀ z ∈ D, f z * (γ * y₁ z + δ * y₂ z) = α * y₁ z + β * y₂ z := by
  obtain ⟨z₀, hz₀⟩ := hDc.nonempty
  obtain ⟨-, hVl, hVS⟩ := s34m_ratio_props hD hDc hy₁ hy₂ hode₁ hode₂ hz₀ (hW z₀ hz₀)
  obtain ⟨a, b, c, d, hdet, hrel⟩ := thm19_1_unique hD hDc hfl hVl fun z hz => (hfS z hz).trans (hVS z hz).symm
  refine ⟨a, b, c, d, hdet, fun z hz => ?_⟩
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [h.1, h.2]
    ring
  have hev : ∀ᶠ w in 𝓝[≠] z, f w * (c * y₁ w + d * y₂ w) = a * y₁ w + b * y₂ w := by
    filter_upwards [s34m_sol_ne hD hy₁ hy₂ hW hcd hz, s34m_sol_ne hD hy₁ hy₂ hW (c := 0) (d := 1) (Or.inr one_ne_zero) hz,
      nhdsWithin_le_nhds (hD.mem_nhds hz)] with w hu h2 hw
    have h2' : y₂ w ≠ 0 := by simpa using h2
    have hn := hD.mem_nhds hw
    have hVa : AnalyticAt ℂ (fun z => y₁ z / y₂ z) w :=
      (hy₁.analyticAt hn).div (hy₂.analyticAt hn) h2'
    have hden : c * (y₁ w / y₂ w) + d ≠ 0 := by
      rw [show c * (y₁ w / y₂ w) + d = (c * y₁ w + d * y₂ w) / y₂ w by field_simp]
      exact div_ne_zero hu h2'
    have h := hrel w hw (hf.analyticAt hn) hVa hden
    have hu' : y₁ w * c + y₂ w * d ≠ 0 := by rw [mul_comm (y₁ w), mul_comm (y₂ w)]; exact hu
    rw [h]
    field_simp
  have hcont : ContinuousAt (fun w => f w * (c * y₁ w + d * y₂ w) - (a * y₁ w + b * y₂ w)) z := by
    have hn := hD.mem_nhds hz
    exact ((hf.continuousOn.continuousAt hn).mul ((continuous_const.continuousAt.mul
      (hy₁.continuousOn.continuousAt hn)).add (continuous_const.continuousAt.mul
        (hy₂.continuousOn.continuousAt hn)))).sub ((continuous_const.continuousAt.mul
          (hy₁.continuousOn.continuousAt hn)).add (continuous_const.continuousAt.mul
            (hy₂.continuousOn.continuousAt hn)))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
  have hzero : Tendsto (fun w => f w * (c * y₁ w + d * y₂ w) - (a * y₁ w + b * y₂ w)) (𝓝[≠] z) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun w hw => by
      show (0 : ℂ) = f w * (c * y₁ w + d * y₂ w) - (a * y₁ w + b * y₂ w)
      rw [hw, sub_self])
  have := tendsto_nhds_unique hlim hzero
  exact sub_eq_zero.1 this

/-- From the relation at a point with `y₂ ≠ 0`: `-γ f + α ≠ 0` and `y₁/y₂ = (δ f - β)/(-γ f + α)`. -/
theorem s34m_xm_inv {α β γ δ fz u v : ℂ} (hdet : α * δ - β * γ ≠ 0) (h : fz * (γ * u + δ * v) = α * u + β * v)
    (hv : v ≠ 0) : -γ * fz + α ≠ 0 ∧ u / v = (δ * fz - β) / (-γ * fz + α) := by
  have h1 : -γ * fz + α ≠ 0 := by
    intro h0
    have h2 : (β - fz * δ) * v = 0 := by linear_combination -h - u * h0
    have h3 : β = fz * δ := by
      have := (mul_eq_zero.1 h2).resolve_right hv
      linear_combination this
    apply hdet
    have h4 : α = γ * fz := by linear_combination h0
    rw [h3, h4]
    ring
  refine ⟨h1, ?_⟩
  rw [div_eq_div_iff hv h1]
  linear_combination -h

/-- At a zero of `y₂` (where `y₁ ≠ 0`): `γ ≠ 0` and `f = α/γ`. -/
theorem s34m_xm_pole {α β γ δ fz u : ℂ} (hdet : α * δ - β * γ ≠ 0) (h : fz * (γ * u + δ * 0) = α * u + β * 0)
    (hu : u ≠ 0) : γ ≠ 0 ∧ fz = α / γ := by
  have h1 : (fz * γ - α) * u = 0 := by linear_combination h
  have h2 : fz * γ = α := by
    have := (mul_eq_zero.1 h1).resolve_right hu
    linear_combination this
  have hγ : γ ≠ 0 := by
    intro hγ
    apply hdet
    rw [hγ] at h2 ⊢
    rw [← h2]
    ring
  exact ⟨hγ, by rw [eq_div_iff hγ, h2]⟩

/-- Difference of Möbius values. -/
theorem s34m_mob_sub {A B C D x y : ℂ} (hx : C * x + D ≠ 0) (hy : C * y + D ≠ 0) :
    (A * x + B) / (C * x + D) - (A * y + B) / (C * y + D) = (A * D - B * C) * (x - y) / ((C * x + D) * (C * y + D)) := by
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- A Möbius map is injective on its finite points. -/
theorem s34m_mob_ne {A B C D x y : ℂ} (hdet : A * D - B * C ≠ 0) (hx : C * x + D ≠ 0) (hy : C * y + D ≠ 0)
    (hxy : x ≠ y) : (A * x + B) / (C * x + D) ≠ (A * y + B) / (C * y + D) := by
  intro h
  have := s34m_mob_sub (A := A) (B := B) hx hy
  rw [h, sub_self, eq_comm] at this
  exact div_ne_zero (mul_ne_zero hdet (sub_ne_zero.2 hxy)) (mul_ne_zero hx hy) this

/-- **The three-point formula**: a Möbius map `N` is recovered from its values `bⱼ = N(aⱼ)` at three distinct finite
points: `N w = Ψ(CR(w, a), b)`. -/
theorem s34m_three_point {A B C D w a₀ a₁ a₂ : ℂ} (hdet : A * D - B * C ≠ 0) (hw : C * w + D ≠ 0)
    (h₀ : C * a₀ + D ≠ 0) (h₁ : C * a₁ + D ≠ 0) (h₂ : C * a₂ + D ≠ 0) (h10 : a₁ ≠ a₀) (h12 : a₁ ≠ a₂)
    (h02 : a₀ ≠ a₂) (hw2 : w ≠ a₂) :
    ((A * a₀ + B) / (C * a₀ + D) * ((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        ((w - a₀) * (a₁ - a₂)) / ((w - a₂) * (a₁ - a₀)) * ((A * a₂ + B) / (C * a₂ + D)) *
          ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) /
      (((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        ((w - a₀) * (a₁ - a₂)) / ((w - a₂) * (a₁ - a₀)) *
          ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) = (A * w + B) / (C * w + D) := by
  rw [← s34m_cr_mob hdet hw h₀ h₁ h₂ hw2 h10]
  exact s34m_cr_inv (s34m_mob_ne hdet hw h₂ hw2) (s34m_mob_ne hdet h₁ h₀ h10) (s34m_mob_ne hdet h₁ h₂ h12)
    (s34m_mob_ne hdet h₀ h₂ h02)

/-- The three-point formula at `∞`: `N(∞) = A/C = Ψ((a₁ - a₂)/(a₁ - a₀), b)` when `C ≠ 0`. -/
theorem s34m_three_point_inf {A B C D a₀ a₁ a₂ : ℂ} (hdet : A * D - B * C ≠ 0) (hC : C ≠ 0)
    (h₀ : C * a₀ + D ≠ 0) (h₁ : C * a₁ + D ≠ 0) (h₂ : C * a₂ + D ≠ 0) (h10 : a₁ ≠ a₀) (h12 : a₁ ≠ a₂)
    (h02 : a₀ ≠ a₂) :
    ((A * a₀ + B) / (C * a₀ + D) * ((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        (a₁ - a₂) / (a₁ - a₀) * ((A * a₂ + B) / (C * a₂ + D)) *
          ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) /
      (((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        (a₁ - a₂) / (a₁ - a₀) * ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) = A / C := by
  rw [← s34m_cr_mob_inf hdet hC h₀ h₁ h₂ h10]
  have hne : A / C ≠ (A * a₂ + B) / (C * a₂ + D) := by
    intro h
    rw [div_eq_div_iff hC h₂] at h
    apply hdet
    linear_combination h
  exact s34m_cr_inv hne (s34m_mob_ne hdet h₁ h₀ h10) (s34m_mob_ne hdet h₁ h₂ h12) (s34m_mob_ne hdet h₀ h₂ h02)

/-- The `Ψ`-denominator at `CR(w, a)`, `b = N(a)`: nonzero iff `N(w)` is finite. -/
theorem s34m_tp_den {A B C D w a₀ a₁ a₂ : ℂ} (hdet : A * D - B * C ≠ 0) (h₀ : C * a₀ + D ≠ 0)
    (h₁ : C * a₁ + D ≠ 0) (h₂ : C * a₂ + D ≠ 0) (h10 : a₁ ≠ a₀) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) (hw2 : w ≠ a₂) :
    (((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        ((w - a₀) * (a₁ - a₂)) / ((w - a₂) * (a₁ - a₀)) *
          ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) = 0 ↔ C * w + D = 0 := by
  rw [s34m_mob_sub h₁ h₂, s34m_mob_sub h₁ h₀]
  have e1 : a₁ - a₂ ≠ 0 := sub_ne_zero.2 h12
  have e2 : a₁ - a₀ ≠ 0 := sub_ne_zero.2 h10
  have e3 : w - a₂ ≠ 0 := sub_ne_zero.2 hw2
  have e4 : a₀ - a₂ ≠ 0 := sub_ne_zero.2 h02
  have key : (A * D - B * C) * (a₁ - a₂) / ((C * a₁ + D) * (C * a₂ + D)) -
      (w - a₀) * (a₁ - a₂) / ((w - a₂) * (a₁ - a₀)) *
        ((A * D - B * C) * (a₁ - a₀) / ((C * a₁ + D) * (C * a₀ + D))) =
      (A * D - B * C) * (a₁ - a₂) * (a₀ - a₂) * (C * w + D) /
        ((C * a₁ + D) * (C * a₂ + D) * (C * a₀ + D) * (w - a₂)) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.1 h with h | h
      · exfalso
        rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact hdet h
          · exact e1 h
        · exact e4 h
      · exact h
    · exfalso
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact h₁ h
          · exact h₂ h
        · exact h₀ h
      · exact e3 h
  · intro h
    left
    rw [h, mul_zero]

/-- The `Ψ`-denominator at `(a₁ - a₂)/(a₁ - a₀)`, `b = N(a)`: nonzero iff `N(∞)` is finite (`C ≠ 0`). -/
theorem s34m_tp_den_inf {A B C D a₀ a₁ a₂ : ℂ} (hdet : A * D - B * C ≠ 0) (h₀ : C * a₀ + D ≠ 0)
    (h₁ : C * a₁ + D ≠ 0) (h₂ : C * a₂ + D ≠ 0) (h10 : a₁ ≠ a₀) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (((A * a₁ + B) / (C * a₁ + D) - (A * a₂ + B) / (C * a₂ + D)) -
        (a₁ - a₂) / (a₁ - a₀) * ((A * a₁ + B) / (C * a₁ + D) - (A * a₀ + B) / (C * a₀ + D))) = 0 ↔ C = 0 := by
  rw [s34m_mob_sub h₁ h₂, s34m_mob_sub h₁ h₀]
  have e1 : a₁ - a₂ ≠ 0 := sub_ne_zero.2 h12
  have e2 : a₁ - a₀ ≠ 0 := sub_ne_zero.2 h10
  have e4 : a₀ - a₂ ≠ 0 := sub_ne_zero.2 h02
  have key : (A * D - B * C) * (a₁ - a₂) / ((C * a₁ + D) * (C * a₂ + D)) -
      (a₁ - a₂) / (a₁ - a₀) * ((A * D - B * C) * (a₁ - a₀) / ((C * a₁ + D) * (C * a₀ + D))) =
      (A * D - B * C) * (a₁ - a₂) * (a₀ - a₂) * C / ((C * a₁ + D) * (C * a₂ + D) * (C * a₀ + D)) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.1 h with h | h
      · exfalso
        rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact hdet h
          · exact e1 h
        · exact e4 h
      · exact h
    · exfalso
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact h₁ h
        · exact h₂ h
      · exact h₀ h
  · intro h
    left
    rw [h, mul_zero]

/-- `CR(wₙ, aₙ) → (a₁ - a₂)/(a₁ - a₀)` as `wₙ → ∞` and `aₙ → a`. -/
theorem s34m_cr_tendsto_inf {w a₀ a₁ a₂ : ℕ → ℂ} {a₀' a₁' a₂' : ℂ} (hw : Tendsto (fun n => ‖w n‖) atTop atTop)
    (h0 : Tendsto a₀ atTop (𝓝 a₀')) (h1 : Tendsto a₁ atTop (𝓝 a₁')) (h2 : Tendsto a₂ atTop (𝓝 a₂'))
    (h10 : a₁' ≠ a₀') :
    Tendsto (fun n => ((w n - a₀ n) * (a₁ n - a₂ n)) / ((w n - a₂ n) * (a₁ n - a₀ n))) atTop
      (𝓝 ((a₁' - a₂') / (a₁' - a₀'))) := by
  have hs : Tendsto (fun n => (w n)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact tendsto_inv_atTop_zero.comp hw
  have hlim : Tendsto (fun n => ((1 - a₀ n * (w n)⁻¹) * (a₁ n - a₂ n)) / ((1 - a₂ n * (w n)⁻¹) * (a₁ n - a₀ n)))
      atTop (𝓝 (((1 - a₀' * 0) * (a₁' - a₂')) / ((1 - a₂' * 0) * (a₁' - a₀')))) := by
    refine ((tendsto_const_nhds.sub (h0.mul hs)).mul (h1.sub h2)).div
      ((tendsto_const_nhds.sub (h2.mul hs)).mul (h1.sub h0)) ?_
    simp only [mul_zero, sub_zero, one_mul]
    exact sub_ne_zero.2 h10
  simp only [mul_zero, sub_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [hw.eventually (eventually_gt_atTop 0)] with n hn
  have hwn : w n ≠ 0 := norm_pos_iff.1 hn
  rw [show (1 - a₀ n * (w n)⁻¹) = (w n - a₀ n) / w n by field_simp,
    show (1 - a₂ n * (w n)⁻¹) = (w n - a₂ n) / w n by field_simp]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_div_div_cancel_right₀ hwn]

/-- **Parametric Picard iteration.**  On an open preconnected `D` with normalized primitives and a radial cover `g`
(as in `exists_ode_solution_of_radialCover`), the equation `w'' + (φ_t/2) w = 0`, `φ_t = ∑ⱼ tⱼ ψⱼ`, has solutions
`w t` with fixed initial data at `g 0`, depending analytically on `t ∈ ℂᵐ`: the Picard iterates are polynomials in
`t` (expansion over words `Fin n → Fin m`) and converge uniformly for bounded `t`. -/
theorem s34m_param_ode {m : ℕ} {D : Set ℂ} (hD : IsOpen D) (hDp : IsPreconnected D) {g : ℂ → ℂ}
    (hg0 : g 0 ∈ D)
    (hprim : ∀ h : ℂ → ℂ, DifferentiableOn ℂ h D →
      ∃ H : ℂ → ℂ, (∀ z ∈ D, HasDerivAt H (h z) z) ∧ H (g 0) = 0)
    (hcover : ∀ z ∈ D, ∃ ρ ρ' : ℝ, 0 < ρ ∧ ρ < ρ' ∧ DifferentiableOn ℂ g (ball 0 ρ') ∧
      MapsTo g (closedBall 0 ρ) D ∧ g '' closedBall 0 ρ ∈ 𝓝 z)
    {ψ : Fin m → ℂ → ℂ} (hψ : ∀ j, DifferentiableOn ℂ (ψ j) D) (α β : ℂ) :
    ∃ w : (Fin m → ℂ) → ℂ → ℂ,
      (∀ t, DifferentiableOn ℂ (w t) D ∧
        (∀ z ∈ D, deriv (deriv (w t)) z = -((∑ j, t j * ψ j z) / 2) * w t z) ∧
        w t (g 0) = α ∧ deriv (w t) (g 0) = β) ∧
      ∀ z ∈ D, AnalyticOnNhd ℂ (fun t => w t z) univ := by
  classical
  -- a normalized primitive operator, linear on `D`
  obtain ⟨P, hP⟩ : ∃ P : (ℂ → ℂ) → ℂ → ℂ, ∀ h, DifferentiableOn ℂ h D →
      (∀ z ∈ D, HasDerivAt (P h) (h z) z) ∧ P h (g 0) = 0 := by
    refine ⟨fun h => if hh : DifferentiableOn ℂ h D then Classical.choose (hprim h hh) else 0,
      fun h hh => ?_⟩
    simp only [hh, dite_true]
    exact Classical.choose_spec (hprim h hh)
  have hPd : ∀ h, DifferentiableOn ℂ h D → DifferentiableOn ℂ (P h) D := fun h hh z hz =>
    ((hP h hh).1 z hz).differentiableAt.differentiableWithinAt
  have hPuniq : ∀ h H, DifferentiableOn ℂ h D → (∀ z ∈ D, HasDerivAt H (h z) z) → H (g 0) = 0 →
      ∀ z ∈ D, P h z = H z := by
    intro h H hh hH hH0 z hz
    exact hD.eqOn_of_deriv_eq hDp (hPd h hh) (fun y hy => (hH y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [((hP h hh).1 y hy).deriv, (hH y hy).deriv]) hg0 (by rw [(hP h hh).2, hH0]) hz
  have hPcongr : ∀ h₁ h₂, DifferentiableOn ℂ h₁ D → DifferentiableOn ℂ h₂ D → (∀ y ∈ D, h₁ y = h₂ y) →
      ∀ z ∈ D, P h₁ z = P h₂ z := by
    intro h₁ h₂ hh₁ hh₂ heq z hz
    exact hPuniq h₁ (P h₂) hh₁ (fun y hy => by rw [heq y hy]; exact (hP h₂ hh₂).1 y hy) (hP h₂ hh₂).2 z hz
  have hPsum : ∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (h : ι → ℂ → ℂ), (∀ i ∈ s, DifferentiableOn ℂ (h i) D) →
      ∀ z ∈ D, P (fun y => ∑ i ∈ s, c i * h i y) z = ∑ i ∈ s, c i * P (h i) z := by
    intro ι s c h hh z hz
    refine hPuniq _ (fun y => ∑ i ∈ s, c i * P (h i) y)
      (DifferentiableOn.fun_sum fun i hi => (hh i hi).const_mul _) (fun y hy => ?_) ?_ z hz
    · exact HasDerivAt.fun_sum fun i hi => ((hP (h i) (hh i hi)).1 y hy).const_mul (c i)
    · exact Finset.sum_eq_zero fun i hi => by rw [(hP (h i) (hh i hi)).2, mul_zero]
  -- the word coefficients
  obtain ⟨V, hV0, hVs⟩ : ∃ V : (n : ℕ) → (Fin n → Fin m) → ℂ → ℂ,
      (∀ w, V 0 w = fun z => α + β * (z - g 0)) ∧
      ∀ n w, V (n + 1) w = P (P (fun z => -(ψ (w 0) z / 2) * V n (Fin.tail w) z)) :=
    ⟨fun n => Nat.rec (motive := fun n => (Fin n → Fin m) → ℂ → ℂ) (fun _ z => α + β * (z - g 0))
      (fun n v w => P (P (fun z => -(ψ (w 0) z / 2) * v (Fin.tail w) z))) n, fun _ => rfl, fun _ _ => rfl⟩
  have hVd : ∀ n w, DifferentiableOn ℂ (V n w) D := by
    intro n
    induction n with
    | zero =>
      intro w
      rw [hV0]
      fun_prop
    | succ n ih =>
      intro w
      rw [hVs]
      exact hPd _ (hPd _ (((hψ _).div_const 2).neg.mul (ih _)))
  -- the Picard iterates for each `t`
  obtain ⟨u, hu0, husucc⟩ : ∃ u : (Fin m → ℂ) → ℕ → ℂ → ℂ, (∀ t, u t 0 = fun z => α + β * (z - g 0)) ∧
      ∀ t n, u t (n + 1) = P (P (fun z => -((∑ j, t j * ψ j z) / 2) * u t n z)) :=
    ⟨fun t n => Nat.rec (fun z => α + β * (z - g 0))
      (fun _ v => P (P (fun z => -((∑ j, t j * ψ j z) / 2) * v z))) n, fun _ => rfl, fun _ _ => rfl⟩
  have hφd : ∀ t : Fin m → ℂ, DifferentiableOn ℂ (fun z => ∑ j, t j * ψ j z) D := fun t =>
    DifferentiableOn.fun_sum fun j _ => (hψ j).const_mul (t j)
  have hud : ∀ t n, DifferentiableOn ℂ (u t n) D := by
    intro t n
    induction n with
    | zero =>
      rw [hu0]
      fun_prop
    | succ n ih =>
      rw [husucc]
      exact hPd _ (hPd _ (((hφd t).div_const 2).neg.mul ih))
  have hkd : ∀ t n, DifferentiableOn ℂ (fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) D :=
    fun t n => ((hφd t).div_const 2).neg.mul (hud t n)
  -- the word expansion: `u t n` is a polynomial in `t`
  have hword : ∀ n, ∀ t, ∀ z ∈ D, u t n z = ∑ w : Fin n → Fin m, (∏ i, t (w i)) * V n w z := by
    intro n
    induction n with
    | zero =>
      intro t z _
      simp [hu0, hV0]
    | succ n ih =>
      intro t z hz
      have hdp : ∀ p : Fin m × (Fin n → Fin m), DifferentiableOn ℂ (fun y => -(ψ p.1 y / 2) * V n p.2 y) D :=
        fun p => ((hψ _).div_const 2).neg.mul (hVd n p.2)
      have hk : ∀ y ∈ D, -((∑ j, t j * ψ j y) / 2) * u t n y =
          ∑ p : Fin m × (Fin n → Fin m), (t p.1 * ∏ i, t (p.2 i)) * (-(ψ p.1 y / 2) * V n p.2 y) := by
        intro y hy
        rw [ih t y hy, Fintype.sum_prod_type]
        have e1 : -((∑ j, t j * ψ j y) / 2) = ∑ j, -(t j * ψ j y / 2) := by
          rw [Finset.sum_div, ← Finset.sum_neg_distrib]
        rw [e1, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      have h1 : ∀ y ∈ D, P (fun y => -((∑ j, t j * ψ j y) / 2) * u t n y) y =
          ∑ p : Fin m × (Fin n → Fin m), (t p.1 * ∏ i, t (p.2 i)) * P (fun y => -(ψ p.1 y / 2) * V n p.2 y) y := by
        intro y hy
        rw [hPcongr _ _ (hkd t n) (DifferentiableOn.fun_sum fun p _ => (hdp p).const_mul _) hk y hy]
        exact hPsum _ Finset.univ _ _ (fun p _ => hdp p) y hy
      have h2 : P (P (fun y => -((∑ j, t j * ψ j y) / 2) * u t n y)) z =
          ∑ p : Fin m × (Fin n → Fin m),
            (t p.1 * ∏ i, t (p.2 i)) * P (P (fun y => -(ψ p.1 y / 2) * V n p.2 y)) z := by
        rw [hPcongr _ _ (hPd _ (hkd t n)) (DifferentiableOn.fun_sum fun p _ => (hPd _ (hdp p)).const_mul _) h1 z hz]
        exact hPsum _ Finset.univ _ _ (fun p _ => hPd _ (hdp p)) z hz
      rw [husucc, h2]
      refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin m) _ _ fun p => ?_
      show _ = (∏ i, t (Fin.cons (α := fun _ => Fin m) p.1 p.2 i)) * V (n + 1) (Fin.cons (α := fun _ => Fin m) p.1 p.2) z
      rw [Fin.prod_univ_succ, hVs]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
  -- uniform bounds for bounded `t`
  have hsumT : ∀ z ∈ D, ∀ T : ℝ, 0 ≤ T → ∃ s ∈ 𝓝 z, ∃ v : ℕ → ℝ, Summable v ∧
      ∀ n, ∀ t : Fin m → ℂ, ‖t‖ ≤ T → ∀ x ∈ s, ‖u t n x‖ ≤ v n := by
    intro z hz T hT
    obtain ⟨ρ, ρ', hρ, hρρ', hgd, hgD, hN⟩ := hcover z hz
    have hcb : closedBall (0 : ℂ) ρ ⊆ ball 0 ρ' := closedBall_subset_ball hρρ'
    have hK : IsCompact (closedBall (0 : ℂ) ρ) := isCompact_closedBall 0 ρ
    have hgc : ContinuousOn g (closedBall 0 ρ) := hgd.continuousOn.mono hcb
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
      ((hgd.deriv isOpen_ball).continuousOn.mono hcb)
    have hB : ∀ j, ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖ψ j (g ζ)‖ ≤ B := fun j =>
      hK.exists_bound_of_continuousOn ((hψ j).continuousOn.comp hgc hgD)
    choose B hB using hB
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun ζ => α + β * (g ζ - g 0))
      ((continuousOn_const.add (continuousOn_const.mul (hgc.sub continuousOn_const))))
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self hρ.le
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 h0mem)
    have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0 h0mem)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 h0mem)
    set M : ℝ := T * (∑ j, B j) / 2 with hMdef
    have hM0 : 0 ≤ M := by
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hB0 j
      positivity
    have hM : ∀ t : Fin m → ℂ, ‖t‖ ≤ T → ∀ ζ ∈ closedBall (0 : ℂ) ρ,
        ‖(∑ j, t j * ψ j (g ζ)) / 2‖ ≤ M := by
      intro t ht ζ hζ
      rw [norm_div, Complex.norm_two, hMdef]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      calc ‖∑ j, t j * ψ j (g ζ)‖ ≤ ∑ j, ‖t j * ψ j (g ζ)‖ := norm_sum_le _ _
        _ ≤ ∑ j, T * B j := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul ((norm_le_pi_norm t j).trans ht) (hB j ζ hζ) (norm_nonneg _) hT
        _ = T * ∑ j, B j := by rw [Finset.mul_sum]
    have hbound : ∀ t : Fin m → ℂ, ‖t‖ ≤ T → ∀ n, ∀ ζ ∈ closedBall (0 : ℂ) ρ,
        ‖u t n (g ζ)‖ ≤ C * (M * A ^ 2) ^ n / (2 * n).factorial * ‖ζ‖ ^ (2 * n) := by
      intro t ht n
      induction n with
      | zero =>
        intro ζ hζ
        rw [hu0]
        simpa using hC ζ hζ
      | succ n ih =>
        intro ζ hζ
        have hk : ∀ ξ ∈ closedBall (0 : ℂ) ρ, ‖(fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) (g ξ)‖ ≤
            (M * (C * (M * A ^ 2) ^ n / (2 * n).factorial)) * ‖ξ‖ ^ (2 * n) := by
          intro ξ hξ
          show ‖-((∑ j, t j * ψ j (g ξ)) / 2) * u t n (g ξ)‖ ≤ _
          rw [norm_mul, norm_neg, mul_assoc]
          exact mul_le_mul (hM t ht ξ hξ) (ih ξ hξ) (norm_nonneg _) hM0
        have h1 := norm_comp_le_of_hasDerivAt_radial hρρ' hgd hgD (hP _ (hkd t n)).1
          (hP _ (hkd t n)).2 hA hk
        have h1' : ∀ ξ ∈ closedBall (0 : ℂ) ρ, ‖P (fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) (g ξ)‖ ≤
            (M * (C * (M * A ^ 2) ^ n / (2 * n).factorial) * A / (2 * n + 1)) *
              ‖ξ‖ ^ (2 * n + 1) := by
          intro ξ hξ
          calc _ ≤ _ := h1 ξ hξ
            _ = _ := by push_cast; ring
        have h2 := norm_comp_le_of_hasDerivAt_radial hρρ' hgd hgD
          (hP _ (hPd _ (hkd t n))).1 (hP _ (hPd _ (hkd t n))).2 hA h1'
        have hf : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
        rw [husucc]
        calc ‖P (P fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) (g ζ)‖ ≤ _ := h2 ζ hζ
          _ = C * (M * A ^ 2) ^ (n + 1) / (2 * (n + 1)).factorial * ‖ζ‖ ^ (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
            push_cast
            field_simp
            ring
    have hcoef : ∀ n : ℕ, 0 ≤ C * (M * A ^ 2) ^ n / ((2 * n).factorial : ℝ) := fun n =>
      div_nonneg (mul_nonneg hC0 (pow_nonneg (mul_nonneg hM0 (sq_nonneg A)) n)) (Nat.cast_nonneg _)
    refine ⟨g '' closedBall 0 ρ, hN,
      fun n => C * (M * A ^ 2) ^ n / (2 * n).factorial * ρ ^ (2 * n), ?_, ?_⟩
    · have hs := (Real.summable_pow_div_factorial (M * A ^ 2 * ρ ^ 2)).mul_left C
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hcoef n) (pow_nonneg hρ.le _))
        (fun n => ?_) hs
      have hfac : (n.factorial : ℝ) ≤ (2 * n).factorial := by
        exact_mod_cast Nat.factorial_le (by omega)
      have hn0 : (0 : ℝ) < n.factorial := by positivity
      have e : C * (M * A ^ 2) ^ n / ((2 * n).factorial : ℝ) * ρ ^ (2 * n)
          = C * ((M * A ^ 2 * ρ ^ 2) ^ n / (2 * n).factorial) := by
        rw [mul_pow, ← pow_mul]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
        (pow_nonneg (mul_nonneg (mul_nonneg hM0 (sq_nonneg A)) (sq_nonneg ρ)) n) hn0 hfac) hC0
    · rintro n t ht x ⟨ζ, hζ, rfl⟩
      calc ‖u t n (g ζ)‖ ≤ _ := hbound t ht n ζ hζ
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hζ) _) (hcoef n)
  refine ⟨fun t z => ∑' n, u t n z, fun t => ?_, fun z hz => ?_⟩
  · -- for fixed `t`: the S19 argument
    have hderiv_succ : ∀ n, ∀ z ∈ D, deriv (u t (n + 1)) z =
        P (fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) z := by
      intro n z hz
      rw [husucc]
      exact ((hP _ (hPd _ (hkd t n))).1 z hz).deriv
    have hderiv2_succ : ∀ n, ∀ z ∈ D, deriv (deriv (u t (n + 1))) z = -((∑ j, t j * ψ j z) / 2) * u t n z := by
      intro n z hz
      have hev : deriv (u t (n + 1)) =ᶠ[𝓝 z] P (fun z => -((∑ j, t j * ψ j z) / 2) * u t n z) := by
        filter_upwards [hD.mem_nhds hz] with y hy
        exact hderiv_succ n y hy
      rw [hev.deriv_eq]
      exact ((hP _ (hkd t n)).1 z hz).deriv
    have hderiv_zero : ∀ z, deriv (u t 0) z = β := by
      intro z
      rw [hu0]
      have h : HasDerivAt (fun z => α + β * (z - g 0)) β z := by
        simpa using (((hasDerivAt_id z).sub_const (g 0)).const_mul β).const_add α
      exact h.deriv
    have hderiv2_zero : ∀ z, deriv (deriv (u t 0)) z = 0 := by
      intro z
      have h : deriv (u t 0) = fun _ => β := funext hderiv_zero
      rw [h, deriv_const]
    have hval_succ : ∀ n, u t (n + 1) (g 0) = 0 := fun n => by
      rw [husucc]
      exact (hP _ (hPd _ (hkd t n))).2
    have hderiv_succ_0 : ∀ n, deriv (u t (n + 1)) (g 0) = 0 := fun n => by
      rw [hderiv_succ n (g 0) hg0]
      exact (hP _ (hkd t n)).2
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℂ → ℂ, S = fun N z => ∑ n ∈ Finset.range N, u t n z := ⟨_, rfl⟩
    have hconv : TendstoLocallyUniformlyOn S (fun z => ∑' n, u t n z) atTop D := by
      rw [hS]
      refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz => ?_
      obtain ⟨s, hs, v, hv, hvb⟩ := hsumT z hz ‖t‖ (norm_nonneg _)
      exact ⟨s, mem_nhdsWithin_of_mem_nhds hs, tendstoUniformlyOn_tsum_nat hv fun n x hx => hvb n t le_rfl x hx⟩
    have hSd : ∀ N, DifferentiableOn ℂ (S N) D := fun N => by
      rw [hS]
      exact DifferentiableOn.fun_sum fun n _ => hud t n
    have hdS : ∀ N, ∀ z ∈ D, deriv (S N) z = ∑ n ∈ Finset.range N, deriv (u t n) z := by
      intro N z hz
      rw [hS]
      exact deriv_fun_sum fun n _ => (hud t n).differentiableAt (hD.mem_nhds hz)
    have hddS : ∀ N, ∀ z ∈ D,
        deriv (deriv (S N)) z = ∑ n ∈ Finset.range N, deriv (deriv (u t n)) z := by
      intro N z hz
      have hev : deriv (S N) =ᶠ[𝓝 z] fun y => ∑ n ∈ Finset.range N, deriv (u t n) y := by
        filter_upwards [hD.mem_nhds hz] with y hy
        exact hdS N y hy
      rw [hev.deriv_eq]
      exact deriv_fun_sum fun n _ => ((hud t n).deriv hD).differentiableAt (hD.mem_nhds hz)
    have hODE_S : ∀ N, ∀ z ∈ D, deriv (deriv (S (N + 1))) z = -((∑ j, t j * ψ j z) / 2) * S N z := by
      intro N z hz
      rw [hddS (N + 1) z hz, Finset.sum_range_succ', hderiv2_zero, add_zero, hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => hderiv2_succ n z hz
    have hconv1 := hconv.deriv (Eventually.of_forall hSd) hD
    have hconv2 := hconv1.deriv (Eventually.of_forall fun N => (hSd N).deriv hD) hD
    have hwd : DifferentiableOn ℂ (fun z => ∑' n, u t n z) D :=
      hconv.differentiableOn (Eventually.of_forall hSd) hD
    refine ⟨hwd, fun z hz => ?_, ?_, ?_⟩
    · have h1 : Tendsto (fun N => deriv (deriv (S (N + 1))) z) atTop
          (𝓝 (deriv (deriv (fun z => ∑' n, u t n z)) z)) :=
        (hconv2.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
      have h2 : Tendsto (fun N => deriv (deriv (S (N + 1))) z) atTop
          (𝓝 (-((∑ j, t j * ψ j z) / 2) * ∑' n, u t n z)) :=
        ((hconv.tendsto_at hz).const_mul (-((∑ j, t j * ψ j z) / 2))).congr fun N => (hODE_S N z hz).symm
      exact tendsto_nhds_unique h1 h2
    · show ∑' n, u t n (g 0) = α
      rw [tsum_eq_single 0 fun n hn => ?_]
      · rw [hu0]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact hval_succ k
    · have h1 : Tendsto (fun N => deriv (S N) (g 0)) atTop (𝓝 (deriv (fun z => ∑' n, u t n z) (g 0))) :=
        hconv1.tendsto_at hg0
      have h2 : Tendsto (fun N => deriv (S N) (g 0)) atTop (𝓝 β) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
        rw [hdS (k + 1) (g 0) hg0, Finset.sum_range_succ', hderiv_zero]
        simp [hderiv_succ_0]
      exact tendsto_nhds_unique h1 h2
  · -- analyticity in `t`: uniform limit of polynomials on every ball
    intro t₀ _
    set T : ℝ := ‖t₀‖ + 1 with hT
    obtain ⟨s, hs, v, hv, hvb⟩ := hsumT z hz T (by positivity)
    have hU : TendstoUniformlyOn (fun N t => ∑ n ∈ Finset.range N, u t n z) (fun t => ∑' n, u t n z) atTop
        (ball (0 : Fin m → ℂ) T) :=
      tendstoUniformlyOn_tsum_nat hv fun n t ht =>
        hvb n t (by rw [mem_ball, dist_zero_right] at ht; exact ht.le) z (mem_of_mem_nhds hs)
    have hpoly : ∀ N, AnalyticOnNhd ℂ (fun t => ∑ n ∈ Finset.range N, u t n z) (ball (0 : Fin m → ℂ) T) := by
      intro N t _
      have e : (fun t => ∑ n ∈ Finset.range N, u t n z) =
          fun t => ∑ n ∈ Finset.range N, ∑ w : Fin n → Fin m, (∏ i, t (w i)) * V n w z := by
        funext t
        exact Finset.sum_congr rfl fun n _ => hword n t z hz
      rw [e]
      refine Finset.analyticAt_fun_sum _ fun n _ => Finset.analyticAt_fun_sum _ fun w _ => ?_
      exact (Finset.analyticAt_fun_prod _ fun i _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) (w i)).analyticAt t).mul analyticAt_const
    exact s34m_analytic_of_tendstoUniformlyOn isOpen_ball hpoly hU t₀
      (by rw [mem_ball, dist_zero_right]; linarith)

/-- A constant-coefficient combination of two solutions of `y'' + (φ/2) y = 0` is a solution. -/
theorem s34m_comb {D : Set ℂ} (hD : IsOpen D) {w₁ w₂ φ : ℂ → ℂ} (hw₁ : DifferentiableOn ℂ w₁ D)
    (hw₂ : DifferentiableOn ℂ w₂ D) (hode₁ : ∀ z ∈ D, deriv (deriv w₁) z = -(φ z / 2) * w₁ z)
    (hode₂ : ∀ z ∈ D, deriv (deriv w₂) z = -(φ z / 2) * w₂ z) (p₁ p₂ : ℂ) :
    DifferentiableOn ℂ (fun z => p₁ * w₁ z + p₂ * w₂ z) D ∧
      (∀ z ∈ D, deriv (fun z => p₁ * w₁ z + p₂ * w₂ z) z = p₁ * deriv w₁ z + p₂ * deriv w₂ z) ∧
      ∀ z ∈ D, deriv (deriv (fun z => p₁ * w₁ z + p₂ * w₂ z)) z = -(φ z / 2) * (p₁ * w₁ z + p₂ * w₂ z) := by
  have hd : ∀ z ∈ D, deriv (fun z => p₁ * w₁ z + p₂ * w₂ z) z = p₁ * deriv w₁ z + p₂ * deriv w₂ z := by
    intro z hz
    have hn := hD.mem_nhds hz
    exact (((hw₁.differentiableAt hn).hasDerivAt.const_mul p₁).add
      ((hw₂.differentiableAt hn).hasDerivAt.const_mul p₂)).deriv
  refine ⟨(hw₁.const_mul p₁).add (hw₂.const_mul p₂), hd, fun z hz => ?_⟩
  have hn := hD.mem_nhds hz
  have hev : deriv (fun z => p₁ * w₁ z + p₂ * w₂ z) =ᶠ[𝓝 z] fun z => p₁ * deriv w₁ z + p₂ * deriv w₂ z := by
    filter_upwards [hn] with y hy
    exact hd y hy
  rw [hev.deriv_eq]
  have h : HasDerivAt (fun y => p₁ * deriv w₁ y + p₂ * deriv w₂ y)
      (p₁ * deriv (deriv w₁) z + p₂ * deriv (deriv w₂) z) z :=
    (((hw₁.deriv hD).differentiableAt hn).hasDerivAt.const_mul p₁).add
      (((hw₂.deriv hD).differentiableAt hn).hasDerivAt.const_mul p₂)
  rw [h.deriv, hode₁ z hz, hode₂ z hz]
  ring

/-- Inverting a Möbius value: if `C w + D ≠ 0` then `N w = (A w + B)/(C w + D)` is a finite point of the inverse
`M = (D v - B)/(-C v + A)` with `M(N w) = w`. -/
theorem s34m_mob_inv {A B C D w : ℂ} (hdet : A * D - B * C ≠ 0) (hw : C * w + D ≠ 0) :
    -C * ((A * w + B) / (C * w + D)) + A ≠ 0 ∧
      (D * ((A * w + B) / (C * w + D)) + -B) / (-C * ((A * w + B) / (C * w + D)) + A) = w := by
  have hc : (A * w + B) / (C * w + D) * (C * w + D) = A * w + B := div_mul_cancel₀ _ hw
  have h1 : -C * ((A * w + B) / (C * w + D)) + A = (A * D - B * C) / (C * w + D) := by
    rw [eq_div_iff hw]
    linear_combination (-C) * hc
  have h2 : D * ((A * w + B) / (C * w + D)) + -B = (A * D - B * C) * w / (C * w + D) := by
    rw [eq_div_iff hw]
    linear_combination D * hc
  refine ⟨by rw [h1]; exact div_ne_zero hdet hw, ?_⟩
  rw [h1, h2]
  field_simp

/-- A finite Möbius value is never `N(∞) = A/C`. -/
theorem s34m_mob_ne_inf {A B C D w : ℂ} (hdet : A * D - B * C ≠ 0) (hC : C ≠ 0) (hw : C * w + D ≠ 0) :
    (A * w + B) / (C * w + D) ≠ A / C := by
  intro h
  rw [div_eq_div_iff hw hC] at h
  apply hdet
  linear_combination -h

/-- The pole value `M(∞) = α/γ` of `M = N⁻¹` from the three values `bⱼ = N(aⱼ)`, `N(w) = (δw - β)/(-γw + α)`:
`α/γ = Ψ((b₁ - b₂)/(b₁ - b₀), a)`, with nonzero denominators. -/
theorem s34m_Q_props {α β γ δ a₀ a₁ a₂ : ℂ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (h₀ : -γ * a₀ + α ≠ 0) (h₁ : -γ * a₁ + α ≠ 0) (h₂ : -γ * a₂ + α ≠ 0) (h10 : a₁ ≠ a₀) (h12 : a₁ ≠ a₂)
    (h02 : a₀ ≠ a₂) :
    (δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₀ + -β) / (-γ * a₀ + α) ≠ 0 ∧
      (a₁ - a₂) - ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₂ + -β) / (-γ * a₂ + α)) /
          ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₀ + -β) / (-γ * a₀ + α)) * (a₁ - a₀) ≠ 0 ∧
      (a₀ * (a₁ - a₂) - ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₂ + -β) / (-γ * a₂ + α)) /
          ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₀ + -β) / (-γ * a₀ + α)) * a₂ * (a₁ - a₀)) /
        ((a₁ - a₂) - ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₂ + -β) / (-γ * a₂ + α)) /
          ((δ * a₁ + -β) / (-γ * a₁ + α) - (δ * a₀ + -β) / (-γ * a₀ + α)) * (a₁ - a₀)) = α / γ := by
  have hdetN : δ * α - -β * -γ ≠ 0 := by intro h; apply hdet; linear_combination h
  obtain ⟨k₀, e₀⟩ := s34m_mob_inv hdetN h₀
  obtain ⟨k₁, e₁⟩ := s34m_mob_inv hdetN h₁
  obtain ⟨k₂, e₂⟩ := s34m_mob_inv hdetN h₂
  simp only [neg_neg] at k₀ k₁ k₂ e₀ e₁ e₂
  set b₀ := (δ * a₀ + -β) / (-γ * a₀ + α)
  set b₁ := (δ * a₁ + -β) / (-γ * a₁ + α)
  set b₂ := (δ * a₂ + -β) / (-γ * a₂ + α)
  have hb10 : b₁ ≠ b₀ := s34m_mob_ne hdetN h₁ h₀ h10
  have hb12 : b₁ ≠ b₂ := s34m_mob_ne hdetN h₁ h₂ h12
  have hb02 : b₀ ≠ b₂ := s34m_mob_ne hdetN h₀ h₂ h02
  have k₀' : γ * b₀ + δ ≠ 0 := k₀
  have k₁' : γ * b₁ + δ ≠ 0 := k₁
  have k₂' : γ * b₂ + δ ≠ 0 := k₂
  have e₀' : (α * b₀ + β) / (γ * b₀ + δ) = a₀ := e₀
  have e₁' : (α * b₁ + β) / (γ * b₁ + δ) = a₁ := e₁
  have e₂' : (α * b₂ + β) / (γ * b₂ + δ) = a₂ := e₂
  refine ⟨sub_ne_zero.2 hb10, ?_, ?_⟩
  · rw [← e₀', ← e₁', ← e₂']
    intro h
    exact hγ ((s34m_tp_den_inf hdet k₀' k₁' k₂' hb10 hb12 hb02).1 h)
  · rw [← e₀', ← e₁', ← e₂']
    exact s34m_three_point_inf hdet hγ k₀' k₁' k₂' hb10 hb12 hb02

/-- **Holomorphic dependence on the Bers point (boundary values).**  In linear coordinates `e` of `Q(G₀, 𝕃)`, the
boundary value `f_μ(x)` at a real point `x` (it depends only on `φ_μ`) is an analytic function of `e(φ_μ)` on the
coordinate image of `T_{G₀}`. -/
theorem s34m_real_analytic (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) (x : ℝ) :
    ∃ F : (Fin m → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (range fun μ : BeltramiGamma Γ => e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) ∧
      ∀ μ : BeltramiGamma Γ, F (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) = normalizedSolution μ.1.1 x := by
  classical
  set R := range fun μ : BeltramiGamma Γ => e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ with hRdef
  have hRo : IsOpen R := s34m_range_open hΓ e hfin
  obtain ⟨μd⟩ : Nonempty (BeltramiGamma Γ) := ⟨Quotient.out (TeichGamma.origin Γ)⟩
  let rep : (Fin m → ℂ) → BeltramiGamma Γ := fun t => if h : t ∈ R then h.choose else μd
  have hrep : ∀ t ∈ R, e ⟨bersFunctionGamma (rep t), (bersFunctionGamma_mem hΓ (rep t)).1⟩ = t := by
    intro t ht
    simp only [rep, ht, dite_true]
    exact ht.choose_spec
  let fT : (Fin m → ℂ) → ℂ → ℂ := fun t z => normalizedSolution (rep t).1.1 z
  have hfT_eq : ∀ μ : BeltramiGamma Γ, ∀ z : ℂ, z.im ≤ 0 →
      fT (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) z = normalizedSolution μ.1.1 z := by
    intro μ z hz
    have h := hrep _ ⟨μ, rfl⟩
    exact s34m_eq_lower (congrArg Subtype.val (e.injective h)) hz
  refine ⟨fun t => fT t x, ?_, fun μ => hfT_eq μ x (by simp)⟩
  -- sequential continuity of `fT` on `Im z ≤ 0`
  have hseq : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ R) → t ∈ R → Tendsto ts atTop (𝓝 t) →
      ∀ (zs : ℕ → ℂ) (z : ℂ), (∀ n, (zs n).im ≤ 0) → Tendsto zs atTop (𝓝 z) →
        Tendsto (fun n => fT (ts n) (zs n)) atTop (𝓝 (fT t z)) := by
    intro ts t hts ht hlim zs z hzs hz
    refine s34m_jc hΓ e hfin (μs := fun n => rep (ts n)) (μ := rep t) ?_ hzs hz
    rw [hrep t ht]
    exact hlim.congr fun n => (hrep _ (hts n)).symm
  have hseq_inf : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ R) → t ∈ R → Tendsto ts atTop (𝓝 t) →
      ∀ zs : ℕ → ℂ, (∀ n, (zs n).im ≤ 0) → Tendsto (fun n => ‖zs n‖) atTop atTop →
        Tendsto (fun n => ‖fT (ts n) (zs n)‖) atTop atTop := by
    intro ts t hts ht hlim zs hzs hz
    refine s34m_jc_inf hΓ e hfin (μs := fun n => rep (ts n)) (μ := rep t) ?_ hzs hz
    rw [hrep t ht]
    exact hlim.congr fun n => (hrep _ (hts n)).symm
  have hcontT : ∀ z : ℂ, z.im ≤ 0 → ∀ t ∈ R, ContinuousAt (fun t => fT t z) t := by
    intro z hz t ht
    rw [ContinuousAt, tendsto_iff_seq_tendsto]
    intro ts hts
    have hev : ∀ᶠ n in atTop, ts n ∈ R := hts.eventually (hRo.mem_nhds ht)
    let ts' : ℕ → Fin m → ℂ := fun n => if ts n ∈ R then ts n else t
    have hts' : Tendsto ts' atTop (𝓝 t) := hts.congr' (hev.mono fun n hn => by simp [ts', hn])
    have h := hseq ts' t (fun n => by by_cases h : ts n ∈ R <;> simp [ts', h, ht]) ht hts'
      (fun _ => z) z (fun _ => hz) tendsto_const_nhds
    exact h.congr' (hev.mono fun n hn => by simp [ts', hn])
  -- the quadratic differentials `ψⱼ` of the coordinate basis
  let ψ : Fin m → ℂ → ℂ := fun j => ((e.symm (Pi.single j 1) : automorphicQD Γ) : ℂ → ℂ)
  have hψd : ∀ j, DifferentiableOn ℂ (ψ j) lowerHalf := fun j => (e.symm (Pi.single j 1)).2.1
  have hexp : ∀ t ∈ R, ∀ z ∈ lowerHalf, schwarzian (fT t) z = ∑ j, t j * ψ j z := by
    intro t ht z hz
    have h1 : bersFunctionGamma (rep t) z = schwarzian (fT t) z := by
      simp only [bersFunctionGamma, bersFunction, indicator_of_mem hz, fT]
    have h2 : (⟨bersFunctionGamma (rep t), (bersFunctionGamma_mem hΓ (rep t)).1⟩ : automorphicQD Γ) =
        ∑ j, t j • e.symm (Pi.single j 1) := by
      apply e.injective
      rw [map_sum, hrep t ht]
      simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply]
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← h1]
    have h3 := congrArg (fun φ : automorphicQD Γ => (φ : ℂ → ℂ) z) h2
    simp only at h3
    rw [h3, Submodule.coe_sum, Finset.sum_apply]
    rfl
  -- solutions of `y'' + (φ_t/2) y = 0` on `𝕃`, analytic in `t`
  have : SimplyConnectedSpace ↥lowerHalf := l333_fam_isSimplyConnected_lowerHalf
  obtain ⟨g, hg0, hcover⟩ := exists_radialCover_of_simplyConnected isOpen_lowerHalf bA_isConnected_lowerHalf
  have hprim : ∀ h : ℂ → ℂ, DifferentiableOn ℂ h lowerHalf →
      ∃ H : ℂ → ℂ, (∀ z ∈ lowerHalf, HasDerivAt H (h z) z) ∧ H (g 0) = 0 := by
    intro h hh
    obtain ⟨G, hG, hG'⟩ := RMT.exists_primitive_of_simplyConnected isOpen_lowerHalf bA_isConnected_lowerHalf hh
    refine ⟨fun z => G z - G (g 0), fun z hz => ?_, sub_self _⟩
    have h1 := (hG.differentiableAt (isOpen_lowerHalf.mem_nhds hz)).hasDerivAt
    rw [hG' z hz] at h1
    exact h1.sub_const _
  obtain ⟨w₁, hw₁, hw₁a⟩ := s34m_param_ode isOpen_lowerHalf bA_isConnected_lowerHalf.isPreconnected hg0 hprim hcover
    hψd 1 0
  obtain ⟨w₂, hw₂, hw₂a⟩ := s34m_param_ode isOpen_lowerHalf bA_isConnected_lowerHalf.isPreconnected hg0 hprim hcover
    hψd 0 1
  intro t₀ ht₀
  have hWw : ∀ t, w₁ t (g 0) * deriv (w₂ t) (g 0) - w₂ t (g 0) * deriv (w₁ t) (g 0) = 1 := by
    intro t
    rw [(hw₁ t).2.2.1, (hw₁ t).2.2.2, (hw₂ t).2.2.1, (hw₂ t).2.2.2]
    ring
  have hfconf : ∀ t, IsConformalOnto (fT t) lowerHalf (fT t '' lowerHalf) := fun t =>
    ut_conformal_lowerHalf (rep t).1
  have hfinj : ∀ t, Function.Injective (fT t) := fun t => s34_h_injective (rep t).1
  have hf0 : ∀ t, fT t 0 = 0 := fun t => (ut_spec (rep t).1).2.2.1
  have hf1 : ∀ t, fT t 1 = 1 := fun t => (ut_spec (rep t).1).2.2.2.1
  -- the relation at `t₀` for `w₁, w₂`
  obtain ⟨a, b, c, d, hdet, hXM₀⟩ := s34m_xm isOpen_lowerHalf bA_isConnected_lowerHalf (f := fT t₀)
    (φ := fun z => ∑ j, t₀ j * ψ j z) (hfconf t₀).1 (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf (hfconf t₀))
    (hexp t₀ ht₀) (hw₁ t₀).1 (hw₂ t₀).1 (hw₁ t₀).2.1 (hw₂ t₀).2.1
    (s34m_ratio_props isOpen_lowerHalf bA_isConnected_lowerHalf (hw₁ t₀).1 (hw₂ t₀).1 (hw₁ t₀).2.1 (hw₂ t₀).2.1
      hg0 (hWw t₀)).1
  -- move the pole of the ratio to `q = f_{t₀}(i) ∈ D_{φ₀}`
  set q := fT t₀ I with hq
  have hqne : ∀ z : ℂ, z.im ≤ 0 → fT t₀ z ≠ q := by
    intro z hz h
    have h' : z = I := hfinj t₀ (by rw [h, hq])
    rw [h', Complex.I_im] at hz
    norm_num at hz
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq (-(a * d - b * c))⁻¹ two_pos
  set p₁ := κ * c with hp₁
  set p₂ := κ * d with hp₂
  set r₁ := κ * (a - q * c) with hr₁
  set r₂ := κ * (b - q * d) with hr₂
  let y₁ : (Fin m → ℂ) → ℂ → ℂ := fun t z => p₁ * w₁ t z + p₂ * w₂ t z
  let y₂ : (Fin m → ℂ) → ℂ → ℂ := fun t z => r₁ * w₁ t z + r₂ * w₂ t z
  have hy₁ := fun t => s34m_comb isOpen_lowerHalf (hw₁ t).1 (hw₂ t).1 (hw₁ t).2.1 (hw₂ t).2.1 p₁ p₂
  have hy₂ := fun t => s34m_comb isOpen_lowerHalf (hw₁ t).1 (hw₂ t).1 (hw₁ t).2.1 (hw₂ t).2.1 r₁ r₂
  have hWy0 : ∀ t, y₁ t (g 0) * deriv (y₂ t) (g 0) - y₂ t (g 0) * deriv (y₁ t) (g 0) = 1 := by
    intro t
    show (p₁ * w₁ t (g 0) + p₂ * w₂ t (g 0)) * deriv (fun z => r₁ * w₁ t z + r₂ * w₂ t z) (g 0) -
      (r₁ * w₁ t (g 0) + r₂ * w₂ t (g 0)) * deriv (fun z => p₁ * w₁ t z + p₂ * w₂ t z) (g 0) = 1
    rw [(hy₂ t).2.1 _ hg0, (hy₁ t).2.1 _ hg0, (hw₁ t).2.2.1, (hw₁ t).2.2.2, (hw₂ t).2.2.1, (hw₂ t).2.2.2]
    have hdet' : -(a * d - b * c) ≠ 0 := neg_ne_zero.2 hdet
    have : κ ^ 2 * (-(a * d - b * c)) = 1 := by rw [hκ, inv_mul_cancel₀ hdet']
    rw [hp₁, hp₂, hr₁, hr₂]
    linear_combination this
  have hRy : ∀ t, (∀ z ∈ lowerHalf, y₁ t z * deriv (y₂ t) z - y₂ t z * deriv (y₁ t) z = 1) ∧
      IsLocUnivMero (fun z => y₁ t z / y₂ t z) lowerHalf ∧
      ∀ z ∈ lowerHalf, schwarzian (fun z => y₁ t z / y₂ t z) z = ∑ j, t j * ψ j z := fun t =>
    s34m_ratio_props isOpen_lowerHalf bA_isConnected_lowerHalf (hy₁ t).1 (hy₂ t).1 (hy₁ t).2.2 (hy₂ t).2.2 hg0
      (hWy0 t)
  -- the relations for all `t ∈ R`
  have hXMt : ∀ t ∈ R, ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      ∀ z ∈ lowerHalf, fT t z * (γ * y₁ t z + δ * y₂ t z) = α * y₁ t z + β * y₂ t z := fun t ht =>
    s34m_xm isOpen_lowerHalf bA_isConnected_lowerHalf (hfconf t).1
      (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf (hfconf t)) (hexp t ht) (hy₁ t).1 (hy₂ t).1
      (hy₁ t).2.2 (hy₂ t).2.2 (hRy t).1
  choose! α β γ δ hdetT hXMT using hXMt
  -- at `t₀`: `y₂ = (f - q) y₁`, so `y₂(t₀, ·)` has no zeros
  have hy20 : ∀ z ∈ lowerHalf, y₂ t₀ z = (fT t₀ z - q) * y₁ t₀ z := by
    intro z hz
    show r₁ * w₁ t₀ z + r₂ * w₂ t₀ z = (fT t₀ z - q) * (p₁ * w₁ t₀ z + p₂ * w₂ t₀ z)
    rw [hp₁, hp₂, hr₁, hr₂]
    linear_combination -κ * hXM₀ z hz
  have hy10 : ∀ z ∈ lowerHalf, y₁ t₀ z ≠ 0 := by
    intro z hz h
    have hW := (hRy t₀).1 z hz
    have h2 : y₂ t₀ z = 0 := by rw [hy20 z hz, h, mul_zero]
    rw [h, h2] at hW
    simp at hW
  have hy2ne0 : ∀ z ∈ lowerHalf, y₂ t₀ z ≠ 0 := fun z hz => by
    rw [hy20 z hz]
    exact mul_ne_zero (sub_ne_zero.2 (hqne z (le_of_lt hz))) (hy10 z hz)
  -- three interior reference points and the explicit three-point formula
  have hL : ∀ s : ℝ, 0 < s → (-(s : ℂ) * I) ∈ lowerHalf := fun s hs => by
    show (-(s : ℂ) * I).im < 0
    simp [hs]
  set ζ₀ : ℂ := -((1 : ℝ) : ℂ) * I with hζ₀
  set ζ₁ : ℂ := -((2 : ℝ) : ℂ) * I with hζ₁
  set ζ₂ : ℂ := -((3 : ℝ) : ℂ) * I with hζ₂
  have hζ₀L : ζ₀ ∈ lowerHalf := hL 1 one_pos
  have hζ₁L : ζ₁ ∈ lowerHalf := hL 2 two_pos
  have hζ₂L : ζ₂ ∈ lowerHalf := hL 3 (by norm_num)
  have hζ10 : ζ₁ ≠ ζ₀ := by rw [hζ₀, hζ₁]; intro h; simpa using congrArg Complex.im h
  have hζ12 : ζ₁ ≠ ζ₂ := by rw [hζ₁, hζ₂]; intro h; simpa using congrArg Complex.im h
  have hζ02 : ζ₀ ≠ ζ₂ := by rw [hζ₀, hζ₂]; intro h; simpa using congrArg Complex.im h
  let V : (Fin m → ℂ) → ℂ → ℂ := fun t z => y₁ t z / y₂ t z
  let CR : ℂ → ℂ → ℂ → ℂ → ℂ := fun w a₀ a₁ a₂ => ((w - a₀) * (a₁ - a₂)) / ((w - a₂) * (a₁ - a₀))
  let Ψ : ℂ → ℂ → ℂ → ℂ → ℂ := fun u b₀ b₁ b₂ =>
    (b₀ * (b₁ - b₂) - u * b₂ * (b₁ - b₀)) / ((b₁ - b₂) - u * (b₁ - b₀))
  let Ψd : ℂ → ℂ → ℂ → ℂ → ℂ := fun u b₁ b₂ b₀ => (b₁ - b₂) - u * (b₁ - b₀)
  let Φ : (Fin m → ℂ) → ℂ → ℂ := fun t w =>
    Ψ (CR w (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)) (V t ζ₀) (V t ζ₁) (V t ζ₂)
  let uinf : (Fin m → ℂ) → ℂ := fun t => (fT t ζ₁ - fT t ζ₂) / (fT t ζ₁ - fT t ζ₀)
  let Ginf : (Fin m → ℂ) → ℂ := fun t => Ψ (uinf t) (V t ζ₀) (V t ζ₁) (V t ζ₂)
  let Q : (Fin m → ℂ) → ℂ := fun t =>
    Ψ ((V t ζ₁ - V t ζ₂) / (V t ζ₁ - V t ζ₀)) (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)
  -- the Möbius map `N_t` with `V_t = N_t ∘ f_t`
  have hN : ∀ t ∈ R, ∀ z ∈ lowerHalf, y₂ t z ≠ 0 →
      -γ t * fT t z + α t ≠ 0 ∧ V t z = (δ t * fT t z + -β t) / (-γ t * fT t z + α t) := by
    intro t ht z hz hy
    obtain ⟨h1, h2⟩ := s34m_xm_inv (hdetT t ht) (hXMT t ht z hz) hy
    exact ⟨h1, by show y₁ t z / y₂ t z = _; rw [h2, sub_eq_add_neg]⟩
  have hdetN : ∀ t ∈ R, δ t * α t - -β t * -γ t ≠ 0 := fun t ht => by
    have := hdetT t ht
    intro h
    apply this
    linear_combination h
  -- at `t₀`: `V = 1/(f - q)`
  have hV0 : ∀ z ∈ lowerHalf, V t₀ z = (0 * fT t₀ z + 1) / (1 * fT t₀ z + -q) := by
    intro z hz
    show y₁ t₀ z / y₂ t₀ z = _
    rw [hy20 z hz, zero_mul, zero_add, one_mul, ← sub_eq_add_neg]
    have := hy10 z hz
    have h2 := sub_ne_zero.2 (hqne z (le_of_lt hz))
    field_simp
  -- continuity in `t`
  have hcy₂ : ∀ z ∈ lowerHalf, Continuous fun t => y₂ t z := fun z hz =>
    (continuous_const.mul (continuousOn_univ.1 (hw₁a z hz).continuousOn)).add
      (continuous_const.mul (continuousOn_univ.1 (hw₂a z hz).continuousOn))
  have hcy₁ : ∀ z ∈ lowerHalf, Continuous fun t => y₁ t z := fun z hz =>
    (continuous_const.mul (continuousOn_univ.1 (hw₁a z hz).continuousOn)).add
      (continuous_const.mul (continuousOn_univ.1 (hw₂a z hz).continuousOn))
  have hcV : ∀ z ∈ lowerHalf, ∀ t, y₂ t z ≠ 0 → ContinuousAt (fun t => V t z) t := fun z hz t ht =>
    ((hcy₁ z hz).continuousAt).div (hcy₂ z hz).continuousAt ht
  have hcf : ∀ w : ℂ, w.im ≤ 0 → ContinuousAt (fun t => fT t w) t₀ := fun w hw => hcontT w hw t₀ ht₀
  -- the values at `t₀`
  have hfζ : ∀ t, fT t ζ₁ ≠ fT t ζ₀ ∧ fT t ζ₁ ≠ fT t ζ₂ ∧ fT t ζ₀ ≠ fT t ζ₂ := fun t =>
    ⟨fun h => hζ10 (hfinj t h), fun h => hζ12 (hfinj t h), fun h => hζ02 (hfinj t h)⟩
  have hreal : ∀ t, ∀ w : ℂ, w.im ≤ 0 → w ≠ ζ₂ → fT t w ≠ fT t ζ₂ := fun t w _ hw h => hw (hfinj t h)
  have hζ₂0 : (0 : ℂ) ≠ ζ₂ := by rw [hζ₂]; intro h; simpa using congrArg Complex.im h
  have hζ₂1 : (1 : ℂ) ≠ ζ₂ := by rw [hζ₂]; intro h; simpa using congrArg Complex.im h
  have hζ₂x : (x : ℂ) ≠ ζ₂ := by rw [hζ₂]; intro h; simpa using congrArg Complex.im h
  have hq0 : ∀ z ∈ lowerHalf, (1 : ℂ) * fT t₀ z + -q ≠ 0 := fun z hz => by
    rw [one_mul, ← sub_eq_add_neg]
    exact sub_ne_zero.2 (hqne z (le_of_lt hz))
  have hden0 : ∀ w : ℂ, w.im ≤ 0 → w ≠ ζ₂ →
      Ψd (CR (fT t₀ w) (fT t₀ ζ₀) (fT t₀ ζ₁) (fT t₀ ζ₂)) (V t₀ ζ₁) (V t₀ ζ₂) (V t₀ ζ₀) ≠ 0 := by
    intro w hw hw2
    show (V t₀ ζ₁ - V t₀ ζ₂) - CR (fT t₀ w) (fT t₀ ζ₀) (fT t₀ ζ₁) (fT t₀ ζ₂) * (V t₀ ζ₁ - V t₀ ζ₀) ≠ 0
    rw [hV0 ζ₀ hζ₀L, hV0 ζ₁ hζ₁L, hV0 ζ₂ hζ₂L]
    rw [Ne, s34m_tp_den (by norm_num) (hq0 ζ₀ hζ₀L) (hq0 ζ₁ hζ₁L) (hq0 ζ₂ hζ₂L) (hfζ t₀).1 (hfζ t₀).2.1
      (hfζ t₀).2.2 (hreal t₀ w hw hw2), one_mul, ← sub_eq_add_neg, sub_eq_zero]
    exact hqne w hw
  have hden0inf : Ψd (uinf t₀) (V t₀ ζ₁) (V t₀ ζ₂) (V t₀ ζ₀) ≠ 0 := by
    show (V t₀ ζ₁ - V t₀ ζ₂) - (fT t₀ ζ₁ - fT t₀ ζ₂) / (fT t₀ ζ₁ - fT t₀ ζ₀) * (V t₀ ζ₁ - V t₀ ζ₀) ≠ 0
    rw [hV0 ζ₀ hζ₀L, hV0 ζ₁ hζ₁L, hV0 ζ₂ hζ₂L]
    rw [Ne, s34m_tp_den_inf (by norm_num) (hq0 ζ₀ hζ₀L) (hq0 ζ₁ hζ₁L) (hq0 ζ₂ hζ₂L) (hfζ t₀).1 (hfζ t₀).2.1
      (hfζ t₀).2.2]
    exact one_ne_zero
  -- the open conditions near `t₀`
  let Dw : (Fin m → ℂ) → ℂ → ℂ := fun t w =>
    Ψd (CR (fT t w) (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)) (V t ζ₁) (V t ζ₂) (V t ζ₀)
  let Dinf : (Fin m → ℂ) → ℂ := fun t => Ψd (uinf t) (V t ζ₁) (V t ζ₂) (V t ζ₀)
  have hζ₀le : ζ₀.im ≤ 0 := le_of_lt hζ₀L
  have hζ₁le : ζ₁.im ≤ 0 := le_of_lt hζ₁L
  have hζ₂le : ζ₂.im ≤ 0 := le_of_lt hζ₂L
  have hV₀ : ∀ z ∈ lowerHalf, ContinuousAt (fun t => V t z) t₀ := fun z hz => hcV z hz t₀ (hy2ne0 z hz)
  have hcDw : ∀ w : ℂ, w.im ≤ 0 → w ≠ ζ₂ → ContinuousAt (fun t => Dw t w) t₀ := by
    intro w hw hw2
    have hCR : ContinuousAt (fun t => CR (fT t w) (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)) t₀ :=
      (((hcf w hw).sub (hcf ζ₀ hζ₀le)).mul ((hcf ζ₁ hζ₁le).sub (hcf ζ₂ hζ₂le))).div
        (((hcf w hw).sub (hcf ζ₂ hζ₂le)).mul ((hcf ζ₁ hζ₁le).sub (hcf ζ₀ hζ₀le)))
        (mul_ne_zero (sub_ne_zero.2 (hreal t₀ w hw hw2)) (sub_ne_zero.2 (hfζ t₀).1))
    exact ((hV₀ ζ₁ hζ₁L).sub (hV₀ ζ₂ hζ₂L)).sub (hCR.mul ((hV₀ ζ₁ hζ₁L).sub (hV₀ ζ₀ hζ₀L)))
  have hcDinf : ContinuousAt Dinf t₀ :=
    ((hV₀ ζ₁ hζ₁L).sub (hV₀ ζ₂ hζ₂L)).sub ((((hcf ζ₁ hζ₁le).sub (hcf ζ₂ hζ₂le)).div
      ((hcf ζ₁ hζ₁le).sub (hcf ζ₀ hζ₀le)) (sub_ne_zero.2 (hfζ t₀).1)).mul ((hV₀ ζ₁ hζ₁L).sub (hV₀ ζ₀ hζ₀L)))
  have him0 : (0 : ℂ).im ≤ 0 := by simp
  have him1 : (1 : ℂ).im ≤ 0 := by simp
  have himx : (x : ℂ).im ≤ 0 := by simp
  have hP : ∀ᶠ t in 𝓝 t₀, t ∈ R ∧ y₂ t ζ₀ ≠ 0 ∧ y₂ t ζ₁ ≠ 0 ∧ y₂ t ζ₂ ≠ 0 ∧ Dw t 0 ≠ 0 ∧ Dw t 1 ≠ 0 ∧
      Dw t x ≠ 0 ∧ Dinf t ≠ 0 :=
    (hRo.eventually_mem ht₀).and <| ((hcy₂ ζ₀ hζ₀L).continuousAt.eventually_ne (hy2ne0 ζ₀ hζ₀L)).and <|
      ((hcy₂ ζ₁ hζ₁L).continuousAt.eventually_ne (hy2ne0 ζ₁ hζ₁L)).and <|
      ((hcy₂ ζ₂ hζ₂L).continuousAt.eventually_ne (hy2ne0 ζ₂ hζ₂L)).and <|
      ((hcDw 0 him0 hζ₂0).eventually_ne (hden0 0 him0 hζ₂0)).and <|
      ((hcDw 1 him1 hζ₂1).eventually_ne (hden0 1 him1 hζ₂1)).and <|
      ((hcDw x himx hζ₂x).eventually_ne (hden0 x himx hζ₂x)).and (hcDinf.eventually_ne hden0inf)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hP
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  set K := closedBall t₀ r with hK
  have hKP : ∀ t ∈ K, t ∈ R ∧ y₂ t ζ₀ ≠ 0 ∧ y₂ t ζ₁ ≠ 0 ∧ y₂ t ζ₂ ≠ 0 ∧ Dw t 0 ≠ 0 ∧ Dw t 1 ≠ 0 ∧
      Dw t x ≠ 0 ∧ Dinf t ≠ 0 := fun t ht => hεP (lt_of_le_of_lt (mem_closedBall.1 ht) (by linarith))
  have hKR : ∀ t ∈ K, t ∈ R := fun t ht => (hKP t ht).1
  -- Möbius facts on `K`
  have hNa : ∀ t ∈ K, (-γ t * fT t ζ₀ + α t ≠ 0 ∧ V t ζ₀ = (δ t * fT t ζ₀ + -β t) / (-γ t * fT t ζ₀ + α t)) ∧
      (-γ t * fT t ζ₁ + α t ≠ 0 ∧ V t ζ₁ = (δ t * fT t ζ₁ + -β t) / (-γ t * fT t ζ₁ + α t)) ∧
      (-γ t * fT t ζ₂ + α t ≠ 0 ∧ V t ζ₂ = (δ t * fT t ζ₂ + -β t) / (-γ t * fT t ζ₂ + α t)) := fun t ht =>
    ⟨hN t (hKR t ht) ζ₀ hζ₀L (hKP t ht).2.1, hN t (hKR t ht) ζ₁ hζ₁L (hKP t ht).2.2.1,
      hN t (hKR t ht) ζ₂ hζ₂L (hKP t ht).2.2.2.1⟩
  have hfinw : ∀ t ∈ K, ∀ w : ℂ, w.im ≤ 0 → w ≠ ζ₂ → Dw t w ≠ 0 → -γ t * fT t w + α t ≠ 0 := by
    intro t ht w hw hw2 hD hC
    apply hD
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNa t ht
    show (V t ζ₁ - V t ζ₂) - CR (fT t w) (fT t ζ₀) (fT t ζ₁) (fT t ζ₂) * (V t ζ₁ - V t ζ₀) = 0
    rw [e0, e1, e2]
    exact (s34m_tp_den (hdetN t (hKR t ht)) h0 h1 h2 (hfζ t).1 (hfζ t).2.1 (hfζ t).2.2
      (hreal t w hw hw2)).2 hC
  have hfininf : ∀ t ∈ K, -γ t ≠ 0 := by
    intro t ht hC
    apply (hKP t ht).2.2.2.2.2.2.2
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNa t ht
    show (V t ζ₁ - V t ζ₂) - (fT t ζ₁ - fT t ζ₂) / (fT t ζ₁ - fT t ζ₀) * (V t ζ₁ - V t ζ₀) = 0
    rw [e0, e1, e2]
    exact (s34m_tp_den_inf (hdetN t (hKR t ht)) h0 h1 h2 (hfζ t).1 (hfζ t).2.1 (hfζ t).2.2).2 hC
  have hγK : ∀ t ∈ K, γ t ≠ 0 := fun t ht h => hfininf t ht (by rw [h, neg_zero])
  have hΦ : ∀ t ∈ K, ∀ w : ℂ, w ≠ fT t ζ₂ → -γ t * w + α t ≠ 0 →
      Φ t w = (δ t * w + -β t) / (-γ t * w + α t) := by
    intro t ht w hw2 hw
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNa t ht
    show Ψ (CR w (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)) (V t ζ₀) (V t ζ₁) (V t ζ₂) = _
    rw [e0, e1, e2]
    exact s34m_three_point (hdetN t (hKR t ht)) hw h0 h1 h2 (hfζ t).1 (hfζ t).2.1 (hfζ t).2.2 hw2
  have hGinf : ∀ t ∈ K, Ginf t = δ t / -γ t := by
    intro t ht
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNa t ht
    show Ψ (uinf t) (V t ζ₀) (V t ζ₁) (V t ζ₂) = _
    rw [e0, e1, e2]
    exact s34m_three_point_inf (hdetN t (hKR t ht)) (hfininf t ht) h0 h1 h2 (hfζ t).1 (hfζ t).2.1 (hfζ t).2.2
  have hQK : ∀ t ∈ K, V t ζ₁ - V t ζ₀ ≠ 0 ∧
      (fT t ζ₁ - fT t ζ₂) - (V t ζ₁ - V t ζ₂) / (V t ζ₁ - V t ζ₀) * (fT t ζ₁ - fT t ζ₀) ≠ 0 ∧
      Q t = α t / γ t := by
    intro t ht
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNa t ht
    show V t ζ₁ - V t ζ₀ ≠ 0 ∧
      (fT t ζ₁ - fT t ζ₂) - (V t ζ₁ - V t ζ₂) / (V t ζ₁ - V t ζ₀) * (fT t ζ₁ - fT t ζ₀) ≠ 0 ∧
      Ψ ((V t ζ₁ - V t ζ₂) / (V t ζ₁ - V t ζ₀)) (fT t ζ₀) (fT t ζ₁) (fT t ζ₂) = α t / γ t
    rw [e0, e1, e2]
    exact s34m_Q_props (hdetT t (hKR t ht)) (hγK t ht) h0 h1 h2 (hfζ t).1 (hfζ t).2.1 (hfζ t).2.2
  -- continuity of `Q` on `K`
  have hca : ∀ t ∈ K, ∀ z : ℂ, z.im ≤ 0 → ContinuousAt (fun t => fT t z) t := fun t ht z hz =>
    hcontT z hz t (hKR t ht)
  have hcb : ∀ t ∈ K, ContinuousAt (fun t => V t ζ₀) t ∧ ContinuousAt (fun t => V t ζ₁) t ∧
      ContinuousAt (fun t => V t ζ₂) t := fun t ht =>
    ⟨hcV ζ₀ hζ₀L t (hKP t ht).2.1, hcV ζ₁ hζ₁L t (hKP t ht).2.2.1, hcV ζ₂ hζ₂L t (hKP t ht).2.2.2.1⟩
  have hcQ : ∀ t ∈ K, ContinuousAt Q t := by
    intro t ht
    obtain ⟨hb₀, hb₁, hb₂⟩ := hcb t ht
    have ha₀ := hca t ht ζ₀ hζ₀le
    have ha₁ := hca t ht ζ₁ hζ₁le
    have ha₂ := hca t ht ζ₂ hζ₂le
    obtain ⟨hd1, hd2, -⟩ := hQK t ht
    have hu : ContinuousAt (fun t => (V t ζ₁ - V t ζ₂) / (V t ζ₁ - V t ζ₀)) t := (hb₁.sub hb₂).div (hb₁.sub hb₀) hd1
    exact ((ha₀.mul (ha₁.sub ha₂)).sub ((hu.mul ha₂).mul (ha₁.sub ha₀))).div
      ((ha₁.sub ha₂).sub (hu.mul (ha₁.sub ha₀))) hd2
  -- the zeros of `y₂` stay away from the boundary points
  have hpole : ∀ (ζs : ℕ → ℂ) (p : ℂ), (∀ k, ζs k ∈ lowerHalf) → Tendsto ζs atTop (𝓝 p) → p.im ≤ 0 →
      (∀ t ∈ K, -γ t * fT t p + α t ≠ 0) → ∃ k₀, ∀ k ≥ k₀, ∀ t ∈ K, y₂ t (ζs k) ≠ 0 := by
    intro ζs p hζs hlim hp hfinp
    by_contra hcon
    push Not at hcon
    choose ks hks ts hts hy0 using hcon
    obtain ⟨t', ht', φ, hφ, hlimt⟩ := (isCompact_closedBall t₀ r).tendsto_subseq hts
    have hval : ∀ n, fT (ts n) (ζs (ks n)) = Q (ts n) := by
      intro n
      have hX := hXMT (ts n) (hKR _ (hts n)) (ζs (ks n)) (hζs _)
      have hW := (hRy (ts n)).1 (ζs (ks n)) (hζs _)
      have h0 : y₂ (ts n) (ζs (ks n)) = 0 := hy0 n
      have hy1 : y₁ (ts n) (ζs (ks n)) ≠ 0 := by
        intro h1
        rw [h1, h0] at hW
        simp at hW
      rw [h0] at hX
      rw [(s34m_xm_pole (hdetT _ (hKR _ (hts n))) hX hy1).2, (hQK _ (hts n)).2.2]
    have hks' : Tendsto (fun n => ks (φ n)) atTop atTop :=
      tendsto_atTop_mono (fun n => le_trans (hφ.id_le n) (hks (φ n))) tendsto_id
    have h1 := hseq (ts ∘ φ) t' (fun n => hKR _ (hts _)) (hKR t' ht') hlimt (fun n => ζs (ks (φ n))) p
      (fun n => le_of_lt (hζs _)) (hlim.comp hks')
    have h2 : Tendsto (fun n => fT ((ts ∘ φ) n) (ζs (ks (φ n)))) atTop (𝓝 (Q t')) :=
      ((hcQ t' ht').tendsto.comp hlimt).congr fun n => (hval (φ n)).symm
    have heq := tendsto_nhds_unique h1 h2
    apply hfinp t' ht'
    rw [heq, (hQK t' ht').2.2]
    field_simp [hγK t' ht']
    ring
  have hpoleI : ∀ ζs : ℕ → ℂ, (∀ k, ζs k ∈ lowerHalf) → Tendsto (fun k => ‖ζs k‖) atTop atTop →
      ∃ k₀, ∀ k ≥ k₀, ∀ t ∈ K, y₂ t (ζs k) ≠ 0 := by
    intro ζs hζs hlim
    by_contra hcon
    push Not at hcon
    choose ks hks ts hts hy0 using hcon
    obtain ⟨t', ht', φ, hφ, hlimt⟩ := (isCompact_closedBall t₀ r).tendsto_subseq hts
    have hval : ∀ n, fT (ts n) (ζs (ks n)) = Q (ts n) := by
      intro n
      have hX := hXMT (ts n) (hKR _ (hts n)) (ζs (ks n)) (hζs _)
      have hW := (hRy (ts n)).1 (ζs (ks n)) (hζs _)
      have h0 : y₂ (ts n) (ζs (ks n)) = 0 := hy0 n
      have hy1 : y₁ (ts n) (ζs (ks n)) ≠ 0 := by
        intro h1
        rw [h1, h0] at hW
        simp at hW
      rw [h0] at hX
      rw [(s34m_xm_pole (hdetT _ (hKR _ (hts n))) hX hy1).2, (hQK _ (hts n)).2.2]
    have hks' : Tendsto (fun n => ks (φ n)) atTop atTop :=
      tendsto_atTop_mono (fun n => le_trans (hφ.id_le n) (hks (φ n))) tendsto_id
    have h1 := hseq_inf (ts ∘ φ) t' (fun n => hKR _ (hts _)) (hKR t' ht') hlimt (fun n => ζs (ks (φ n)))
      (fun n => le_of_lt (hζs _)) (hlim.comp hks')
    have h2 : Tendsto (fun n => fT ((ts ∘ φ) n) (ζs (ks (φ n)))) atTop (𝓝 (Q t')) :=
      ((hcQ t' ht').tendsto.comp hlimt).congr fun n => (hval (φ n)).symm
    exact not_tendsto_atTop_of_tendsto_nhds h2.norm h1
  -- sequential continuity of the explicit formula
  have hab : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ K) → t ∈ K → Tendsto ts atTop (𝓝 t) →
      (∀ z : ℂ, z.im ≤ 0 → Tendsto (fun n => fT (ts n) z) atTop (𝓝 (fT t z))) ∧
      Tendsto (fun n => V (ts n) ζ₀) atTop (𝓝 (V t ζ₀)) ∧ Tendsto (fun n => V (ts n) ζ₁) atTop (𝓝 (V t ζ₁)) ∧
      Tendsto (fun n => V (ts n) ζ₂) atTop (𝓝 (V t ζ₂)) := by
    intro ts t hts ht hlim
    obtain ⟨hb₀, hb₁, hb₂⟩ := hcb t ht
    exact ⟨fun z hz => hseq ts t (fun n => hKR _ (hts n)) (hKR t ht) hlim (fun _ => z) z (fun _ => hz)
      tendsto_const_nhds, hb₀.tendsto.comp hlim, hb₁.tendsto.comp hlim, hb₂.tendsto.comp hlim⟩
  have hΦlim : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ K) → t ∈ K → Tendsto ts atTop (𝓝 t) →
      ∀ (ws : ℕ → ℂ) (w : ℂ), Tendsto ws atTop (𝓝 w) → w ≠ fT t ζ₂ →
        Ψd (CR w (fT t ζ₀) (fT t ζ₁) (fT t ζ₂)) (V t ζ₁) (V t ζ₂) (V t ζ₀) ≠ 0 →
        Tendsto (fun n => Φ (ts n) (ws n)) atTop (𝓝 (Φ t w)) := by
    intro ts t hts ht hlim ws w hws hw2 hden
    obtain ⟨ha, hb₀, hb₁, hb₂⟩ := hab ts t hts ht hlim
    have ha₀ := ha ζ₀ hζ₀le
    have ha₁ := ha ζ₁ hζ₁le
    have ha₂ := ha ζ₂ hζ₂le
    have hu : Tendsto (fun n => CR (ws n) (fT (ts n) ζ₀) (fT (ts n) ζ₁) (fT (ts n) ζ₂)) atTop
        (𝓝 (CR w (fT t ζ₀) (fT t ζ₁) (fT t ζ₂))) :=
      ((hws.sub ha₀).mul (ha₁.sub ha₂)).div ((hws.sub ha₂).mul (ha₁.sub ha₀))
        (mul_ne_zero (sub_ne_zero.2 hw2) (sub_ne_zero.2 (hfζ t).1))
    exact ((hb₀.mul (hb₁.sub hb₂)).sub ((hu.mul hb₂).mul (hb₁.sub hb₀))).div
      ((hb₁.sub hb₂).sub (hu.mul (hb₁.sub hb₀))) hden
  have hΦlimI : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ K) → t ∈ K → Tendsto ts atTop (𝓝 t) →
      ∀ ws : ℕ → ℂ, Tendsto (fun n => ‖ws n‖) atTop atTop →
        Tendsto (fun n => Φ (ts n) (ws n)) atTop (𝓝 (Ginf t)) := by
    intro ts t hts ht hlim ws hws
    obtain ⟨ha, hb₀, hb₁, hb₂⟩ := hab ts t hts ht hlim
    have hu := s34m_cr_tendsto_inf hws (ha ζ₀ hζ₀le) (ha ζ₁ hζ₁le) (ha ζ₂ hζ₂le) (hfζ t).1
    exact ((hb₀.mul (hb₁.sub hb₂)).sub ((hu.mul hb₂).mul (hb₁.sub hb₀))).div
      ((hb₁.sub hb₂).sub (hu.mul (hb₁.sub hb₀))) (hKP t ht).2.2.2.2.2.2.2
  have hGinflim : ∀ (ts : ℕ → Fin m → ℂ) (t : Fin m → ℂ), (∀ n, ts n ∈ K) → t ∈ K → Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n => Ginf (ts n)) atTop (𝓝 (Ginf t)) := by
    intro ts t hts ht hlim
    obtain ⟨ha, hb₀, hb₁, hb₂⟩ := hab ts t hts ht hlim
    have hu : Tendsto (fun n => uinf (ts n)) atTop (𝓝 (uinf t)) :=
      ((ha ζ₁ hζ₁le).sub (ha ζ₂ hζ₂le)).div ((ha ζ₁ hζ₁le).sub (ha ζ₀ hζ₀le)) (sub_ne_zero.2 (hfζ t).1)
    exact ((hb₀.mul (hb₁.sub hb₂)).sub ((hu.mul hb₂).mul (hb₁.sub hb₀))).div
      ((hb₁.sub hb₂).sub (hu.mul (hb₁.sub hb₀))) (hKP t ht).2.2.2.2.2.2.2
  -- `V` is the explicit Möbius image of `f` at points where `y₂ ≠ 0`
  have hVΦ : ∀ t ∈ K, ∀ z ∈ lowerHalf, y₂ t z ≠ 0 → z ≠ ζ₂ → V t z = Φ t (fT t z) := by
    intro t ht z hz hy hz2
    obtain ⟨h1, h2⟩ := hN t (hKR t ht) z hz hy
    rw [h2, hΦ t ht _ (fun h => hz2 (hfinj t h)) h1]
  have hVan : ∀ z ∈ lowerHalf, ∀ t, y₂ t z ≠ 0 → AnalyticAt ℂ (fun t => V t z) t := by
    intro z hz t hy
    have h1 : AnalyticAt ℂ (fun t => y₁ t z) t :=
      (analyticAt_const.mul (hw₁a z hz t (mem_univ _))).add (analyticAt_const.mul (hw₂a z hz t (mem_univ _)))
    have h2 : AnalyticAt ℂ (fun t => y₂ t z) t :=
      (analyticAt_const.mul (hw₁a z hz t (mem_univ _))).add (analyticAt_const.mul (hw₂a z hz t (mem_univ _)))
    exact h1.div h2 hy
  -- sequences in `𝕃` tending to the boundary
  have hseqL : ∀ p : ℂ, p.im = 0 → (∀ k : ℕ, p - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I ∈ lowerHalf) ∧
      Tendsto (fun k : ℕ => p - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 p) := by
    intro p hp
    refine ⟨fun k => ?_, ?_⟩
    · show (p - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I).im < 0
      have h1 : (p - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I).im = -(1 / ((k : ℝ) + 1)) := by
        rw [Complex.sub_im, hp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [h1]
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · have h : Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.sub (h.mul_const I)
  have hseqI : (∀ k : ℕ, -(((k : ℝ) + 1 : ℝ) : ℂ) * I ∈ lowerHalf) ∧
      Tendsto (fun k : ℕ => ‖-(((k : ℝ) + 1 : ℝ) : ℂ) * I‖) atTop atTop := by
    refine ⟨fun k => ?_, ?_⟩
    · show (-(((k : ℝ) + 1 : ℝ) : ℂ) * I).im < 0
      have h1 : (-(((k : ℝ) + 1 : ℝ) : ℂ) * I).im = -((k : ℝ) + 1) := by simp
      rw [h1]
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    · have : ∀ k : ℕ, ‖-(((k : ℝ) + 1 : ℝ) : ℂ) * I‖ = (k : ℝ) + 1 := fun k => by
        rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp only [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- analyticity of the boundary values `G_p = N_t(f_t(p))`, `p = 0, 1`
  have hGan : ∀ p : ℂ, p.im = 0 → p ≠ ζ₂ → (∀ t ∈ K, Dw t p ≠ 0) →
      AnalyticOnNhd ℂ (fun t => Φ t (fT t p)) (ball t₀ r) := by
    intro p hp hp2 hDp
    obtain ⟨hζs, hζlim⟩ := hseqL p hp
    obtain ⟨k₀, hk₀⟩ := hpole _ p hζs hζlim hp.le fun t ht => hfinw t ht p hp.le hp2 (hDp t ht)
    have hev2 : ∀ᶠ k : ℕ in atTop, p - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I ≠ ζ₂ :=
      hζlim.eventually_ne hp2
    refine s34m_limit_analytic isOpen_ball (isCompact_closedBall t₀ r) ball_subset_closedBall
      (H := fun k t => V t (p - ((1 / (((k + k₀ : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)) ?_ ?_
    · intro k t ht
      exact hVan _ (hζs _) t (hk₀ _ (by omega) t (ball_subset_closedBall ht))
    · intro ts ks t hts ht hlim hks
      have hks' : Tendsto (fun n => ks n + k₀) atTop atTop :=
        tendsto_atTop_mono (fun n => Nat.le_add_right (ks n) k₀) hks.tendsto_atTop
      have hw := hab ts t hts ht hlim
      have hfw : Tendsto (fun n => fT (ts n) (p - ((1 / (((ks n + k₀ : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)) atTop
          (𝓝 (fT t p)) :=
        hseq ts t (fun n => hKR _ (hts n)) (hKR t ht) hlim _ p (fun n => le_of_lt (hζs _)) (hζlim.comp hks')
      have h1 := hΦlim ts t hts ht hlim _ _ hfw (hreal t p hp.le hp2) (hDp t ht)
      have h2 := hΦlim ts t hts ht hlim _ _ (hw.1 p hp.le) (hreal t p hp.le hp2) (hDp t ht)
      have h3 := h1.sub h2
      rw [sub_self] at h3
      refine h3.congr' ?_
      filter_upwards [hks'.eventually hev2] with n hn
      rw [hVΦ (ts n) (hts n) _ (hζs _) (hk₀ _ (by omega) _ (hts n)) hn]
  have hG₀ := hGan 0 (by simp) hζ₂0 fun t ht => (hKP t ht).2.2.2.2.1
  have hG₁ := hGan 1 (by simp) hζ₂1 fun t ht => (hKP t ht).2.2.2.2.2.1
  have hGIan : AnalyticOnNhd ℂ Ginf (ball t₀ r) := by
    obtain ⟨hζs, hζlim⟩ := hseqI
    obtain ⟨k₀, hk₀⟩ := hpoleI _ hζs hζlim
    have hev2 : ∀ᶠ k : ℕ in atTop, -(((k : ℝ) + 1 : ℝ) : ℂ) * I ≠ ζ₂ := by
      filter_upwards [eventually_ge_atTop 3] with k hk h
      have := congrArg Complex.im h
      rw [hζ₂] at this
      simp at this
      have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    refine s34m_limit_analytic isOpen_ball (isCompact_closedBall t₀ r) ball_subset_closedBall
      (H := fun k t => V t (-((((k + k₀ : ℕ) : ℝ) + 1 : ℝ) : ℂ) * I)) ?_ ?_
    · intro k t ht
      exact hVan _ (hζs _) t (hk₀ _ (by omega) t (ball_subset_closedBall ht))
    · intro ts ks t hts ht hlim hks
      have hks' : Tendsto (fun n => ks n + k₀) atTop atTop :=
        tendsto_atTop_mono (fun n => Nat.le_add_right (ks n) k₀) hks.tendsto_atTop
      have hfw := hseq_inf ts t (fun n => hKR _ (hts n)) (hKR t ht) hlim _ (fun n => le_of_lt (hζs _))
        (hζlim.comp hks')
      have h1 := hΦlimI ts t hts ht hlim _ hfw
      have h3 := h1.sub (hGinflim ts t hts ht hlim)
      rw [sub_self] at h3
      refine h3.congr' ?_
      filter_upwards [hks'.eventually hev2] with n hn
      rw [hVΦ (ts n) (hts n) _ (hζs _) (hk₀ _ (by omega) _ (hts n)) hn]
  -- interior points: `f_t(z) = CR(V_t(z), G₀, G₁, G∞)`, analytic in `t`
  obtain ⟨hzs, hzlim⟩ := hseqL (x : ℂ) (by simp)
  obtain ⟨k₁, hk₁⟩ := hpole _ (x : ℂ) hzs hzlim (by simp) fun t ht =>
    hfinw t ht x himx hζ₂x (hKP t ht).2.2.2.2.2.2.1
  have hint : ∀ k, AnalyticOnNhd ℂ (fun t => fT t ((x : ℂ) - ((1 / (((k + k₁ : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I))
      (ball t₀ r) := by
    intro k
    set z : ℂ := (x : ℂ) - ((1 / (((k + k₁ : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I with hzdef
    have hzL : z ∈ lowerHalf := hzs _
    have hyz : ∀ t ∈ K, y₂ t z ≠ 0 := fun t ht => hk₁ _ (by omega) t ht
    have hform : ∀ t ∈ ball t₀ r, fT t z = ((V t z - Φ t (fT t 0)) * (Φ t (fT t 1) - Ginf t)) /
        ((V t z - Ginf t) * (Φ t (fT t 1) - Φ t (fT t 0))) := by
      intro t ht
      have htK := ball_subset_closedBall ht
      have hdN := hdetN t (hKR t htK)
      obtain ⟨hNz, hVz⟩ := hN t (hKR t htK) z hzL (hyz t htK)
      have hfin0 := hfinw t htK 0 him0 hζ₂0 (hKP t htK).2.2.2.2.1
      have hfin1 := hfinw t htK 1 him1 hζ₂1 (hKP t htK).2.2.2.2.2.1
      have hα : α t ≠ 0 := by have h := hfin0; rw [hf0 t] at h; simpa using h
      have h1' : -γ t + α t ≠ 0 := by have h := hfin1; rw [hf1 t] at h; simpa using h
      rw [hVz, hΦ t htK _ (hreal t 0 him0 hζ₂0) hfin0, hΦ t htK _ (hreal t 1 him1 hζ₂1) hfin1, hGinf t htK,
        hf0 t, hf1 t]
      have := s34m_cr_norm hdN (hfininf t htK) hα h1' hNz
      simp only [mul_zero, zero_add, mul_one] at this ⊢
      rw [this]
    refine AnalyticOnNhd.congr isOpen_ball ?_ fun t ht => (hform t ht).symm
    intro t ht
    have htK := ball_subset_closedBall ht
    have hdN := hdetN t (hKR t htK)
    obtain ⟨hNz, hVz⟩ := hN t (hKR t htK) z hzL (hyz t htK)
    have hfin0 := hfinw t htK 0 him0 hζ₂0 (hKP t htK).2.2.2.2.1
    have hfin1 := hfinw t htK 1 him1 hζ₂1 (hKP t htK).2.2.2.2.2.1
    have hV := hVan z hzL t (hyz t htK)
    have hd1 : V t z - Ginf t ≠ 0 := by
      rw [hVz, hGinf t htK]
      exact sub_ne_zero.2 (s34m_mob_ne_inf hdN (hfininf t htK) hNz)
    have hd2 : Φ t (fT t 1) - Φ t (fT t 0) ≠ 0 := by
      rw [hΦ t htK _ (hreal t 0 him0 hζ₂0) hfin0, hΦ t htK _ (hreal t 1 him1 hζ₂1) hfin1, hf0 t, hf1 t]
      rw [hf0 t] at hfin0
      rw [hf1 t] at hfin1
      exact sub_ne_zero.2 (s34m_mob_ne hdN hfin1 hfin0 one_ne_zero)
    exact (((hV.sub (hG₀ t ht)).mul ((hG₁ t ht).sub (hGIan t ht))).div
      ((hV.sub (hGIan t ht)).mul ((hG₁ t ht).sub (hG₀ t ht))) (mul_ne_zero hd1 hd2))
  -- the boundary value at `x`
  have hFan : AnalyticOnNhd ℂ (fun t => fT t x) (ball t₀ r) := by
    refine s34m_limit_analytic isOpen_ball (isCompact_closedBall t₀ r) ball_subset_closedBall hint ?_
    intro ts ks t hts ht hlim hks
    have hks' : Tendsto (fun n => ks n + k₁) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right (ks n) k₁) hks.tendsto_atTop
    have h1 := hseq ts t (fun n => hKR _ (hts n)) (hKR t ht) hlim _ (x : ℂ) (fun n => le_of_lt (hzs _))
      (hzlim.comp hks')
    have h2 := hseq ts t (fun n => hKR _ (hts n)) (hKR t ht) hlim (fun _ => (x : ℂ)) (x : ℂ) (fun _ => himx)
      tendsto_const_nhds
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  exact hFan t₀ (mem_ball_self hr0)

/-- **Uniform discs**: for `z₀ ∈ D_{φ₀}`, the quasidiscs `D_φ` with `e(φ)` near `e(φ₀)` all contain a fixed disc
about `z₀` (`f_μ → f_{μ₀}` locally uniformly with the inverses, `normalizedSolution_tendsto_of_bers`,
`b34_b_inv_tendsto`). -/
theorem s34m_disc_uniform (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) (μ₀ : BeltramiGamma Γ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ bersDisc Γ (bersFunctionGamma μ₀)) :
    ∃ r > 0, ∃ ρ > 0, ∀ μ : BeltramiGamma Γ,
      ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
          e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < r →
        ball z₀ ρ ⊆ bersDisc Γ (bersFunctionGamma μ) := by
  obtain ⟨b, hb, hup⟩ := s34m_upper hΓ e hfin
  obtain ⟨w₀, hw₀, hz₀w⟩ : ∃ w₀ ∈ upperHalf, normalizedSolution μ₀.1.1 w₀ = z₀ := by
    rw [(bersDisc_wellDefined (μ := μ₀) (ν := μ₀) rfl).2] at hz₀
    exact hz₀
  by_contra hcon
  push Not at hcon
  have hseq : ∀ k : ℕ, ∃ μ : BeltramiGamma Γ, ∃ z : ℂ,
      ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
          e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < 1 / ((k : ℝ) + 1) ∧
        ‖z - z₀‖ < 1 / ((k : ℝ) + 1) ∧ z ∉ bersDisc Γ (bersFunctionGamma μ) := by
    intro k
    obtain ⟨μ, h1, h2⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity) (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨z, hz, hzn⟩ := not_subset.1 h2
    rw [mem_ball, dist_eq_norm] at hz
    exact ⟨μ, z, h1, hz, hzn⟩
  choose μs zs hμs hzs hzn using hseq
  have hconv : Tendsto (fun k => bersNormL (bersFunctionGamma (μs k) - bersFunctionGamma μ₀)) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun k : ℕ => ENNReal.ofReal (b * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul b
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0 (fun k => bot_le) (fun k => ?_)
    exact (hup _ _).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hμs k).le hb.le))
  obtain ⟨νs, hνμ, -, hunif⟩ := normalizedSolution_tendsto_of_bers hΓ hconv
  have hdisc : ∀ k, bersDisc Γ (bersFunctionGamma (μs k)) = normalizedSolution (νs k).1.1 '' upperHalf := by
    intro k
    rw [← bersFunctionGamma_eq_of_equiv (hνμ k)]
    exact (bersDisc_wellDefined (μ := νs k) (ν := νs k) rfl).2
  have hhom : ∀ μ : BeltramiH, IsOpenMap (normalizedSolution μ.1) ∧ Continuous (normalizedSolution μ.1) ∧
      Function.Bijective (normalizedSolution μ.1) := fun μ => by
    obtain ⟨e', he'⟩ := b34_b_homeo μ
    rw [← he']
    exact ⟨e'.isOpenMap, e'.continuous, e'.bijective⟩
  choose ws hws using fun k => (hhom (νs k).1).2.2.2 (zs k)
  have hzlim : Tendsto zs atTop (𝓝 (normalizedSolution μ₀.1.1 w₀)) := by
    rw [hz₀w]
    exact b34_b_tendsto_of_lt hzs
  have hwlim : Tendsto ws atTop (𝓝 w₀) :=
    b34_b_inv_tendsto (F := fun k => normalizedSolution (νs k).1.1) (f := normalizedSolution μ₀.1.1)
      (fun k => (hhom (νs k).1).1) (fun k => (hhom (νs k).1).2.1) (fun k => (hhom (νs k).1).2.2.1)
      (hhom μ₀.1).2.1 (hhom μ₀.1).2.2.1 hunif hzlim hws
  obtain ⟨k, hk⟩ := (hwlim.eventually (isOpen_upperHalf.mem_nhds hw₀)).exists
  exact hzn k (by rw [hdisc k]; exact ⟨ws k, hk, hws k⟩)

/-- A point of `F(G₀)` is `(φ_μ, f_μ(τ))` for some `μ ∈ M(G₀)` and `τ ∈ ℍ`. -/
theorem s34m_fiber_rep (x : BersFiberSpace Γ) :
    ∃ (μ : BeltramiGamma Γ) (τ : UpperHalfPlane), x.1 = (bersFunctionGamma μ, normalizedSolution μ.1.1 τ) := by
  obtain ⟨μ, hμ, w, hw, hz⟩ := x.2.2
  exact ⟨μ, ⟨w, hw⟩, Prod.ext hμ.symm hz.symm⟩

/-- `γ_φ (f_μ(τ)) = f_μ(γ τ)`. -/
theorem s34m_act_spec (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) (τ : UpperHalfPlane) :
    bersFiberAction Γ γ (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ) =
      normalizedSolution μ.1.1 ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [(bersFiberAction_wellDefined hΓ μ hγ).1, ← b33_d_mobiusFn_smul]
  congr 2
  exact (s34_h_injective μ.1).injOn.leftInvOn_invFunOn (mem_univ _)

/-- **The orbit relation**: `[x] = [y]` in `V(G₀)` iff `y = γ x` for some `γ ∈ G₀` (`γ ↦ γ_φ` is a group action
on `D_φ`, so the relation is already an equivalence). -/
theorem s34m_mk_eq_iff (hΓ : IsFuchsian Γ) (x y : BersFiberSpace Γ) :
    Quot.mk (bersFiberRel Γ) x = Quot.mk (bersFiberRel Γ) y ↔ bersFiberRel Γ x y := by
  have heq : Equivalence (bersFiberRel Γ) := by
    refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
    · obtain ⟨μ, τ, hx⟩ := s34m_fiber_rep x
      refine ⟨1, Γ.one_mem, ?_⟩
      rw [hx]
      show (bersFunctionGamma μ, bersFiberAction Γ 1 (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ)) = _
      rw [s34m_act_spec hΓ μ Γ.one_mem, one_smul]
    · obtain ⟨μ, τ, hx⟩ := s34m_fiber_rep x
      obtain ⟨γ, hγ, hxy⟩ := h
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [← hxy, hx]
      show (bersFunctionGamma μ, bersFiberAction Γ γ⁻¹ (bersFunctionGamma μ)
        (bersFiberAction Γ γ (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ))) = _
      rw [s34m_act_spec hΓ μ hγ, s34m_act_spec hΓ μ (Γ.inv_mem hγ), inv_smul_smul]
    · obtain ⟨μ, τ, hx⟩ := s34m_fiber_rep x
      obtain ⟨γ, hγ, hxy⟩ := h₁
      obtain ⟨δ, hδ, hyz⟩ := h₂
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, ?_⟩
      rw [← hyz, ← hxy, hx]
      show (bersFunctionGamma μ, bersFiberAction Γ (δ * γ) (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ)) =
        (bersFunctionGamma μ, bersFiberAction Γ δ (bersFunctionGamma μ)
          (bersFiberAction Γ γ (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ)))
      rw [s34m_act_spec hΓ μ (Γ.mul_mem hδ hγ), s34m_act_spec hΓ μ hγ, s34m_act_spec hΓ μ hδ, mul_smul]
  constructor
  · intro h
    exact heq.eqvGen_iff.1 (Quot.eqvGen_exact h)
  · intro h
    exact Quot.sound h

/-- **Local injectivity boxes**: about `(φ₀, z₀) ∈ F(G₀)` there is a box `‖e(φ) - e(φ₀)‖ < r`, `|z - z₀| < ρ`
whose coordinate ball lies in the coordinate image of `T_{G₀}`, whose discs lie in the `D_φ`, and on which `[·]` is
injective (`bersFiber_action_discontinuous`; `±I` act trivially). -/
theorem s34m_local_box (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) (μ₀ : BeltramiGamma Γ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ bersDisc Γ (bersFunctionGamma μ₀)) :
    ∃ r > 0, ∃ ρ > 0,
      ball (e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩) r ⊆
          range (fun μ : BeltramiGamma Γ => e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) ∧
      (∀ μ : BeltramiGamma Γ,
        ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
            e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < r →
          ball z₀ ρ ⊆ bersDisc Γ (bersFunctionGamma μ)) ∧
      ∀ x y : BersFiberSpace Γ,
        (∃ μ : BeltramiGamma Γ, x.1.1 = bersFunctionGamma μ ∧
          ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
              e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < r) → ‖x.1.2 - z₀‖ < ρ →
        (∃ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ ∧
          ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
              e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < r) → ‖y.1.2 - z₀‖ < ρ →
        Quot.mk (bersFiberRel Γ) x = Quot.mk (bersFiberRel Γ) y → x = y := by
  obtain ⟨b, hb, hup⟩ := s34m_upper hΓ e hfin
  obtain ⟨r₁, hr₁, ρ₁, hρ₁, hdisc⟩ := s34m_disc_uniform hΓ e hfin μ₀ hz₀
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.1 (s34m_range_open hΓ e hfin) _ ⟨μ₀, rfl⟩
  have hφ₀ : bersFunctionGamma μ₀ ∈ bersImage Γ :=
    ⟨Quotient.mk _ μ₀, ((bersMapGamma_mem hΓ (Quotient.mk _ μ₀)).2.2 μ₀ rfl).symm⟩
  obtain ⟨ε, hε, hdis⟩ := bersFiber_action_discontinuous hΓ hfree ⟨(bersFunctionGamma μ₀, z₀), hφ₀, hz₀⟩
  refine ⟨min (min r₁ r₂) (ε / b), by positivity, min ρ₁ ε, by positivity, fun t ht => hball (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 ht)
    ((min_le_left _ _).trans (min_le_right _ _)))), fun μ hμ => (ball_subset_ball (min_le_left _ _)).trans
      (hdisc μ (lt_of_lt_of_le hμ ((min_le_left _ _).trans (min_le_left _ _)))), ?_⟩
  have hnorm : ∀ μ : BeltramiGamma Γ, ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ -
      e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩‖ < min (min r₁ r₂) (ε / b) →
      bersNormL (bersFunctionGamma μ - bersFunctionGamma μ₀) < ENNReal.ofReal ε := by
    intro μ hμ
    refine (hup μ μ₀).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    have := lt_of_lt_of_le hμ (min_le_right _ _)
    rw [lt_div_iff₀ hb] at this
    linarith
  rintro x y ⟨μx, hμx, hx⟩ hxz ⟨μy, hμy, hy⟩ hyz hxy
  obtain ⟨γ, hγ, hγxy⟩ := (s34m_mk_eq_iff hΓ x y).1 hxy
  by_cases h1 : γ = 1 ∨ γ = -1
  · obtain ⟨μ, τ, hxr⟩ := s34m_fiber_rep x
    apply Subtype.ext
    rw [← hγxy, hxr]
    show _ = (bersFunctionGamma μ, bersFiberAction Γ γ (bersFunctionGamma μ) (normalizedSolution μ.1.1 τ))
    rw [s34m_act_spec hΓ μ hγ]
    rcases h1 with rfl | rfl
    · rw [one_smul]
    · have hneg : (((-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ : UpperHalfPlane) : ℂ) = τ := by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply]
        simp
      rw [hneg]
  · push Not at h1
    exfalso
    refine hdis γ hγ h1.1 h1.2 x y ?_ (lt_of_lt_of_le hxz (min_le_right _ _)) ?_
      (lt_of_lt_of_le hyz (min_le_right _ _)) hγxy
    · rw [hμx]
      exact hnorm μx hx
    · rw [hμy]
      exact hnorm μy hy


/-- **The action in coordinates is analytic**: for `γ ∈ G₀`, `(e(φ), z) ↦ γ_φ(z)` is analytic on
`{(e(φ), z) : φ ∈ T_{G₀}, z ∈ D_φ}` (the coefficients of the Möbius map `γ_φ` are rational in boundary values of
`f_μ`, `s34_F_affine`/`s34_F_pole`). -/
theorem s34m_action_analytic (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) :
    ∃ A : (Fin m → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ A {p | ∃ μ : BeltramiGamma Γ,
        e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1 ∧ p.2 ∈ bersDisc Γ (bersFunctionGamma μ)} ∧
      ∀ μ : BeltramiGamma Γ, ∀ z ∈ bersDisc Γ (bersFunctionGamma μ),
        A (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩, z) = bersFiberAction Γ γ (bersFunctionGamma μ) z := by
  classical
  choose F hFa hFv using fun x : ℝ => s34m_real_analytic hΓ e hfin x
  have hFt : ∀ (x : ℝ) (p : (Fin m → ℂ) × ℂ), (∃ μ : BeltramiGamma Γ,
      e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1) → AnalyticAt ℂ (fun p => F x p.1) p := by
    rintro x p ⟨μ, hμ⟩
    exact (hFa x p.1 ⟨μ, hμ⟩).comp analyticAt_fst
  have hdisc : ∀ μ : BeltramiGamma Γ, ∀ z ∈ bersDisc Γ (bersFunctionGamma μ),
      z ∈ normalizedSolution μ.1.1 '' upperHalf := by
    intro μ z hz
    rwa [(bersDisc_wellDefined (μ := μ) (ν := μ) rfl).2] at hz
  by_cases hc : γ 1 0 = 0
  · -- the affine case
    set x₁ : ℝ := (γ 0 0 * 1 + γ 0 1) / (γ 1 0 * 1 + γ 1 1) with hx₁
    set x₀ : ℝ := (γ 0 0 * 0 + γ 0 1) / (γ 1 0 * 0 + γ 1 1) with hx₀
    have e₁ : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 1 = (x₁ : ℂ) := by
      have h := s34_w_mobius_ofReal γ 1
      rw [Complex.ofReal_one] at h
      exact h
    have e₀ : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0 = (x₀ : ℂ) := by
      have h := s34_w_mobius_ofReal γ 0
      rw [Complex.ofReal_zero] at h
      exact h
    refine ⟨fun p => (F x₁ p.1 - F x₀ p.1) * p.2 + F x₀ p.1, ?_, fun μ z hz => ?_⟩
    · rintro p ⟨μ, hμ, -⟩
      exact (((hFt x₁ p ⟨μ, hμ⟩).sub (hFt x₀ p ⟨μ, hμ⟩)).mul analyticAt_snd).add (hFt x₀ p ⟨μ, hμ⟩)
    · have key : bersFiberAction Γ γ (bersFunctionGamma μ) z =
          (F x₁ (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) -
            F x₀ (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩)) * z +
            F x₀ (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) := by
        rw [(bersFiberAction_wellDefined hΓ μ hγ).1, s34_F_affine μ hγ hc, e₁, e₀, hFv, hFv]
      exact key.symm
  · -- the pole case
    set pr : ℝ := γ 0 0 / γ 1 0 with hpr
    let s : ℝ → ℝ := fun x => γ 0 0 / γ 1 0 + -(γ 1 0 ^ 2)⁻¹ * (x + γ 1 1 / γ 1 0)⁻¹
    have es : ∀ x : ℝ, (γ 0 0 : ℂ) / γ 1 0 + -((γ 1 0 : ℂ) ^ 2)⁻¹ * ((x : ℂ) + (γ 1 1 : ℂ) / γ 1 0)⁻¹ =
        ((s x : ℝ) : ℂ) := fun x => by
      simp only [s]
      push_cast
      ring
    have ep : (γ 0 0 : ℂ) / γ 1 0 = ((pr : ℝ) : ℂ) := by
      rw [hpr, Complex.ofReal_div]
    have hG : ∀ (μ : BeltramiGamma Γ) (x : ℝ), s34_G (normalizedSolution μ.1.1) γ x =
        (F (s x) (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) -
          F pr (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩))⁻¹ := by
      intro μ x
      rw [s34_G, es, ep, hFv, hFv]
    let Gt : ℝ → (Fin m → ℂ) × ℂ → ℂ := fun x p => (F (s x) p.1 - F pr p.1)⁻¹
    have hGt : ∀ (x : ℝ) (p : (Fin m → ℂ) × ℂ), (∃ μ : BeltramiGamma Γ,
        e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1) → AnalyticAt ℂ (Gt x) p := by
      rintro x p ⟨μ, hμ⟩
      by_cases hsx : s x = pr
      · have : Gt x = fun _ => 0 := by
          funext q
          simp only [Gt, hsx, sub_self, inv_zero]
        rw [this]
        exact analyticAt_const
      · refine ((hFt (s x) p ⟨μ, hμ⟩).sub (hFt pr p ⟨μ, hμ⟩)).inv ?_
        show F (s x) p.1 - F pr p.1 ≠ 0
        rw [← hμ, hFv, hFv]
        intro h
        exact hsx (Complex.ofReal_injective (s34_h_injective μ.1 (sub_eq_zero.1 h)))
    refine ⟨fun p => F pr p.1 + ((Gt 1 p - Gt 0 p) * p.2 + Gt 0 p)⁻¹, ?_, fun μ z hz => ?_⟩
    · rintro p ⟨μ, hμ, hz⟩
      refine (hFt pr p ⟨μ, hμ⟩).add (((((hGt 1 p ⟨μ, hμ⟩).sub (hGt 0 p ⟨μ, hμ⟩)).mul analyticAt_snd).add
        (hGt 0 p ⟨μ, hμ⟩)).inv ?_)
      have hz' : p.2 ≠ normalizedSolution μ.1.1 (-((γ 1 1 : ℂ) / γ 1 0)) := by
        refine s34_h_ne_pole μ.1 ?_ (hdisc μ _ hz)
        rw [← Complex.ofReal_div, ← Complex.ofReal_neg, Complex.ofReal_im]
      have h1 := (s34_F_pole μ hγ hc hz').1
      have hG1 := hG μ 1
      have hG0 := hG μ 0
      rw [Complex.ofReal_one] at hG1
      rw [Complex.ofReal_zero] at hG0
      rw [hG1, hG0, hμ] at h1
      exact h1
    · have hz' : z ≠ normalizedSolution μ.1.1 (-((γ 1 1 : ℂ) / γ 1 0)) := by
        refine s34_h_ne_pole μ.1 ?_ (hdisc μ _ hz)
        rw [← Complex.ofReal_div, ← Complex.ofReal_neg, Complex.ofReal_im]
      have hG1 := hG μ 1
      have hG0 := hG μ 0
      rw [Complex.ofReal_one] at hG1
      rw [Complex.ofReal_zero] at hG0
      have key : bersFiberAction Γ γ (bersFunctionGamma μ) z =
          F pr (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) +
            ((Gt 1 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩, z) -
              Gt 0 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩, z)) * z +
              Gt 0 (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩, z))⁻¹ := by
        rw [(bersFiberAction_wellDefined hΓ μ hγ).1, (s34_F_pole μ hγ hc hz').2, hG1, hG0, ep, ← hFv pr μ]
      exact key.symm

/-- **`[·]` is open** for the quotient topology: the saturation of an open set is the union of its images under
the action maps, which are homeomorphisms of `F(G₀)` (`s34m_action_analytic`). -/
theorem s34m_mk_isOpenMap (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) :
    @IsOpenMap (BersFiberSpace Γ) (BersQuotient Γ) _
      (TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance) (Quot.mk (bersFiberRel Γ)) := by
  classical
  have hrep : ∀ y : BersFiberSpace Γ, ∃ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ := by
    intro y
    obtain ⟨μ, τ, h⟩ := s34m_fiber_rep y
    exact ⟨μ, congrArg Prod.fst h⟩
  have hmem : ∀ y : BersFiberSpace Γ, y.1.1 ∈ automorphicQD Γ := by
    intro y
    obtain ⟨μ, hμ⟩ := hrep y
    rw [hμ]
    exact (bersFunctionGamma_mem hΓ μ).1
  have hact : ∀ γ ∈ Γ, ∀ y : BersFiberSpace Γ, bersFiberSpaceAction Γ γ y.1 ∈ BersFiberSpace Γ := by
    intro γ hγ y
    obtain ⟨μ, hμ⟩ := hrep y
    show y.1.1 ∈ bersImage Γ ∧ bersFiberAction Γ γ y.1.1 y.1.2 ∈ bersDisc Γ y.1.1
    refine ⟨y.2.1, ?_⟩
    have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
    rw [hμ] at h2 ⊢
    rw [← (bersFiberAction_wellDefined hΓ μ hγ).2.2]
    exact mem_image_of_mem _ h2
  have hcont : ∀ γ (hγ : γ ∈ Γ), Continuous fun y : BersFiberSpace Γ =>
      (⟨bersFiberSpaceAction Γ γ y.1, hact γ hγ y⟩ : BersFiberSpace Γ) := by
    intro γ hγ
    obtain ⟨A, hA, hAv⟩ := s34m_action_analytic hΓ e hfin hγ
    have hE : Continuous fun y : BersFiberSpace Γ => e ⟨y.1.1, hmem y⟩ :=
      e.continuous.comp (continuous_subtype_val.fst.subtype_mk hmem)
    have hS : ∀ y : BersFiberSpace Γ, (e ⟨y.1.1, hmem y⟩, y.1.2) ∈ {p : (Fin m → ℂ) × ℂ | ∃ μ : BeltramiGamma Γ,
        e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1 ∧ p.2 ∈ bersDisc Γ (bersFunctionGamma μ)} := by
      intro y
      obtain ⟨μ, hμ⟩ := hrep y
      have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
      rw [hμ] at h2
      exact ⟨μ, congrArg e (Subtype.ext hμ.symm), h2⟩
    have hval : ∀ y : BersFiberSpace Γ, A (e ⟨y.1.1, hmem y⟩, y.1.2) = bersFiberAction Γ γ y.1.1 y.1.2 := by
      intro y
      obtain ⟨μ, hμ⟩ := hrep y
      have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
      have he : (⟨y.1.1, hmem y⟩ : automorphicQD Γ) = ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ :=
        Subtype.ext hμ
      rw [hμ] at h2
      rw [he, hAv μ _ h2, hμ]
    have h2c : Continuous fun y : BersFiberSpace Γ => bersFiberAction Γ γ y.1.1 y.1.2 :=
      (hA.continuousOn.comp_continuous (hE.prodMk continuous_subtype_val.snd) hS).congr hval
    exact (continuous_subtype_val.fst.prodMk h2c).subtype_mk _
  intro U hU
  show IsOpen (Quot.mk (bersFiberRel Γ) ⁻¹' (Quot.mk (bersFiberRel Γ) '' U))
  have hsat : Quot.mk (bersFiberRel Γ) ⁻¹' (Quot.mk (bersFiberRel Γ) '' U) =
      ⋃ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ),
        (fun y : BersFiberSpace Γ => (⟨bersFiberSpaceAction Γ γ y.1, hact γ hγ y⟩ : BersFiberSpace Γ)) ⁻¹' U := by
    ext y
    rw [mem_preimage, mem_iUnion₂]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨γ, hγ, h⟩ := (s34m_mk_eq_iff hΓ y x).1 hxy.symm
      refine ⟨γ, hγ, ?_⟩
      rw [mem_preimage]
      convert hx using 1
      exact Subtype.ext h
    · rintro ⟨γ, hγ, hy⟩
      exact ⟨_, hy, ((s34m_mk_eq_iff hΓ y _).2 ⟨γ, hγ, rfl⟩).symm⟩
  rw [hsat]
  exact isOpen_iUnion fun γ => isOpen_iUnion fun hγ => hU.preimage (hcont γ hγ)


end LiZhongQC
