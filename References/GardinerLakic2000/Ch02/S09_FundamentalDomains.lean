import References.GardinerLakic2000.Ch02.S08_TypesOfElements

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.9 Fundamental domains

Source `teichmuller.txt`, lines 1835–1926 (Chapter 2, §2.9).

* Definition (fundamental domain, l. 1836–1845) — exists: `LiZhongQC.IsFundamentalDomainH` (the measurable
  fundamental set the book says suffices, l. 1845; conditions 3–4, the paired analytic boundary arcs, are not used)
* Formula (2.27) (the Dirichlet fundamental domain, l. 1852–1866; used in Ch. 3, 14) — `dirichletDomain`
* Formula (2.28) (the Ford fundamental domain, via isometric circles, l. 1869–1879) — `fordDomain`
* Unlabelled (the Dirichlet domain centred at 0 coincides with the Ford domain in the disc model, l. 1880–1899) —
  `para2_9_ford_eq_dirichlet`
* Definition (the area of `ℍ/Γ`, `4 ∬_ω ρ²`, l. 1901–1906; used in Ch. 10) — `hypArea`
* Unlabelled (the area does not depend on the fundamental domain, l. 1907–1913) — `para2_9_area_indep`
* Definition (the limit set, l. 1916) — exists: `LiZhongQC.fuchsianLimitSet` (accumulation points of orbits in ℂ̄)
* Definition (first and second kind, l. 1916; used in Ch. 5, 10) — `IsFirstKind`
* Theorem 3 (l. 1920) — `IsHypLine`, `HasFiniteSidesNoFreeSides`, `thm2_3`
* Definition (the border of `ℍ/Γ`, l. 1925; used in Ch. 13) — exists: `LiZhongQC.ordinarySet` (the border is the
  quotient of the ordinary set by Γ)

Not items: the construction remarks and convexity of `ω_D` (l. 1866, U−); the Gauss–Bonnet remark (l. 1914).
Modelling: the Dirichlet inequality uses Mathlib's hyperbolic `dist` on ℍ (a constant multiple of the book's
distance, which does not change the half-planes); `z₀` is not an elliptic fixed point, so `A ≠ id` is `A z₀ ≠ z₀`.
For (2.28), `E(A)`, the exterior of the isometric circle `|cz + d| = 1`, is `{|A′(z)| < 1}`; `fordDomain` is stated for
any set of Möbius maps and any domain, so that the same definition serves `ℍ` (2.28) and the disc (l. 1899).
Theorem 3 (b): "finitely many sides" reads "the boundary of `ω` in `ℍ` is covered by finitely many hyperbolic lines",
"no free sides" reads "`ω̄` meets `ℝ̂` in finitely many points" (with finitely many sides, a free side is exactly an
interval of `ℝ̂` in `ω̄`) [modelling]; `ω` is the Dirichlet domain (2.27) as in the book.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (upperHalf unitDisc IsFuchsian IsFundamentalDomainH fuchsianLimitSet extRealLine toExt h36p_m
  ExtPlane)

/-- **Formula (2.27)** (§2.9, l. 1852–1862). The Dirichlet domain `ω_D(z₀) = ⋂_{A ≠ id} h(A)`,
`h(A) = {z ∈ ℍ : d(z, z₀) < d(z, A(z₀))}`, as a subset of `ℂ`. -/
def dirichletDomain (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (z₀ : UpperHalfPlane) : Set ℂ :=
  {w : ℂ | ∃ z : UpperHalfPlane, (z : ℂ) = w ∧ ∀ γ ∈ Γ, γ • z₀ ≠ z₀ → dist z z₀ < dist z (γ • z₀)}

/-- **Formula (2.28)** (§2.9, l. 1869–1879). The Ford domain `ω_F = (⋂_A E(A)) ∩ U`: the points of `U` exterior to
the isometric circles `{|A′(z)| = 1}` of all the maps `A ∈ G` (for a Fuchsian group, `G` the Möbius maps of
`Γ ∖ {id}`, none fixing `∞`, and `U = ℍ`). -/
def fordDomain (G : Set (ℂ → ℂ)) (U : Set ℂ) : Set ℂ := {z ∈ U | ∀ A ∈ G, ‖deriv A z‖ < 1}

/-- Helper for `para2_9_ford_eq_dirichlet`: `|a − c̄|² = |a − c|² + 4 Im a Im c`. -/
theorem gl2_fd_norm_sub_conj_sq (a c : ℂ) : ‖a - conj c‖ ^ 2 = ‖a - c‖ ^ 2 + 4 * a.im * c.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Helper for `para2_9_ford_eq_dirichlet`: comparison of hyperbolic distances to `z₀`,
`d(a, z₀) < d(b, z₀) ⇔ |a − z̄₀|²/Im a < |b − z̄₀|²/Im b` (`cosh d(a, z₀) = 1 + |a − z₀|²/(2 Im a Im z₀)`). -/
theorem gl2_fd_dist_lt_iff (z₀ a b : UpperHalfPlane) :
    dist a z₀ < dist b z₀ ↔
      ‖(a : ℂ) - conj (z₀ : ℂ)‖ ^ 2 / a.im < ‖(b : ℂ) - conj (z₀ : ℂ)‖ ^ 2 / b.im := by
  have h0 := z₀.im_pos
  have e : ∀ c : UpperHalfPlane, ‖(c : ℂ) - conj (z₀ : ℂ)‖ ^ 2 / c.im =
      2 * z₀.im * (dist (c : ℂ) z₀ ^ 2 / (2 * c.im * z₀.im)) + 4 * z₀.im := by
    intro c
    have hc := c.im_pos
    rw [gl2_fd_norm_sub_conj_sq, Complex.dist_eq, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
    field_simp
  have key : dist a z₀ < dist b z₀ ↔
      dist (a : ℂ) z₀ ^ 2 / (2 * a.im * z₀.im) < dist (b : ℂ) z₀ ^ 2 / (2 * b.im * z₀.im) := by
    rw [← abs_of_nonneg (dist_nonneg (x := a) (y := z₀)), ← abs_of_nonneg (dist_nonneg (x := b) (y := z₀)),
      ← Real.cosh_lt_cosh, UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist, add_lt_add_iff_left]
  rw [e a, e b, add_lt_add_iff_right, key]
  exact (mul_lt_mul_iff_of_pos_left (by positivity)).symm

/-- Helper for `para2_9_ford_eq_dirichlet`: `Im γz = Im z / |cz + d|²`. -/
theorem gl2_fd_im_m (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (h36p_m γ z).im = z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
  have hdet := LiZhongQC.b33_d_det γ
  have _hz := hz
  rw [← Complex.normSq_eq_norm_sq]
  unfold h36p_m
  rw [Complex.div_im]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
  rw [div_sub_div_same]
  congr 1
  linear_combination z.im * hdet

/-- Helper for `para2_9_ford_eq_dirichlet`: the Cayley-type map `B(z) = (z − z₀)/(z − z̄₀)` sends `ℍ` into `Δ`
(`|z − z̄₀|² − |z − z₀|² = 4 Im z Im z₀ > 0`). -/
theorem gl2_fd_B_mem (z₀ z : UpperHalfPlane) :
    ((z : ℂ) - z₀) / ((z : ℂ) - conj (z₀ : ℂ)) ∈ unitDisc := by
  have hy := z.coe_im_pos
  have hb := z₀.coe_im_pos
  have hden : (z : ℂ) - conj (z₀ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hlt : ‖(z : ℂ) - z₀‖ ^ 2 < ‖(z : ℂ) - conj (z₀ : ℂ)‖ ^ 2 := by
    rw [gl2_fd_norm_sub_conj_sq]
    nlinarith
  have hlt' : ‖(z : ℂ) - z₀‖ < ‖(z : ℂ) - conj (z₀ : ℂ)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
  rw [unitDisc, mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hden)]
  exact hlt'

/-- Helper for `para2_9_ford_eq_dirichlet`: the inverse `B⁻¹(w) = (z₀ − z̄₀ w)/(1 − w)` sends `Δ` into `ℍ`, and
`B(B⁻¹ w) = w` (`B⁻¹w − z₀ = (z₀ − z̄₀) w/(1 − w)`, `B⁻¹w − z̄₀ = (z₀ − z̄₀)/(1 − w)`). -/
theorem gl2_fd_Binv (z₀ : UpperHalfPlane) {w : ℂ} (hw : w ∈ unitDisc) :
    0 < (((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)).im ∧
      ((((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)) - z₀) /
        ((((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)) - conj (z₀ : ℂ)) = w := by
  have hb := z₀.coe_im_pos
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have h1w : (1 : ℂ) - w ≠ 0 := fun h => by
    have : w = 1 := (sub_eq_zero.1 h).symm
    rw [this, norm_one] at hw1
    exact lt_irrefl _ hw1
  have hcc : (z₀ : ℂ) - conj (z₀ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  set u : ℂ := ((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w) with hu
  have e1 : u - z₀ = ((z₀ : ℂ) - conj (z₀ : ℂ)) * w / (1 - w) := by
    rw [hu]
    field_simp
    ring
  have e2 : u - conj (z₀ : ℂ) = ((z₀ : ℂ) - conj (z₀ : ℂ)) / (1 - w) := by
    rw [hu]
    field_simp
    ring
  have hden : u - conj (z₀ : ℂ) ≠ 0 := by
    rw [e2]
    exact div_ne_zero hcc h1w
  have hB : (u - z₀) / (u - conj (z₀ : ℂ)) = w := by
    rw [e1, e2]
    field_simp
  refine ⟨?_, hB⟩
  -- `|u − z₀| = |w| |u − z̄₀| < |u − z̄₀|`, so `Im u > 0`
  have hn : ‖u - z₀‖ < ‖u - conj (z₀ : ℂ)‖ := by
    have h := congrArg norm hB
    rw [norm_div, div_eq_iff (norm_ne_zero_iff.2 hden)] at h
    rw [h]
    exact mul_lt_of_lt_one_left (norm_pos_iff.2 hden) hw1
  have hsq : ‖u - z₀‖ ^ 2 < ‖u - conj (z₀ : ℂ)‖ ^ 2 := by
    gcongr
  rw [gl2_fd_norm_sub_conj_sq] at hsq
  nlinarith

/-- Helper for `para2_9_ford_eq_dirichlet`: the isometric-circle condition for `A = B ∘ γ ∘ B⁻¹` at `w = B(z)`
is the Dirichlet inequality, `|A′(w)| < 1 ⇔ d(z, z₀) < d(γz, z₀)`: by the chain rule
`|A′(w)| = |z − z̄₀|²/(|γz − z̄₀|² |cz + d|²)`, and `Im γz = Im z/|cz + d|²`. -/
theorem gl2_fd_deriv_lt_iff (z₀ : UpperHalfPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : UpperHalfPlane) :
    ‖deriv (fun w => (h36p_m γ (((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)) - z₀) /
        (h36p_m γ (((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)) - conj (z₀ : ℂ)))
        (((z : ℂ) - z₀) / ((z : ℂ) - conj (z₀ : ℂ)))‖ < 1 ↔ dist z z₀ < dist (γ • z) z₀ := by
  have hy := z.coe_im_pos
  have hb := z₀.coe_im_pos
  set c : ℂ := (z₀ : ℂ) with hc
  set u : ℂ := (z : ℂ) with hu
  set w : ℂ := (u - c) / (u - conj c) with hw
  have hden : u - conj c ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hcc : c - conj c ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have h1w : 1 - w = (c - conj c) / (u - conj c) := by
    rw [hw]
    field_simp
    ring
  have h1w0 : 1 - w ≠ 0 := by
    rw [h1w]
    exact div_ne_zero hcc hden
  have hinv : (c - conj c * w) / (1 - w) = u := by
    rw [div_eq_iff h1w0, hw]
    field_simp
    ring
  -- the image point `v = γ u` and the denominator `q = cu + d`
  set q : ℂ := (γ 1 0 : ℂ) * u + γ 1 1 with hq
  have hq0 : q ≠ 0 := LiZhongQC.k24_d_den_ne_zero (LiZhongQC.b33_d_det γ) hy.ne'
  set v : ℂ := h36p_m γ u with hv
  have hvim : v.im = u.im / ‖q‖ ^ 2 := gl2_fd_im_m γ hy
  have hvpos : 0 < v.im := by
    rw [hvim]
    have := norm_pos_iff.2 hq0
    positivity
  have hvden : v - conj c ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  -- the chain rule for `B ∘ γ ∘ B⁻¹` at `w`
  have hD1 : HasDerivAt (fun w : ℂ => (c - conj c * w) / (1 - w)) ((c - conj c) / (1 - w) ^ 2) w := by
    have h := (((hasDerivAt_id' w).const_mul (conj c)).const_sub c).div
      ((hasDerivAt_id' w).const_sub (1 : ℂ)) h1w0
    refine h.congr_deriv ?_
    ring
  have hD2 : HasDerivAt (h36p_m γ) (1 / q ^ 2) ((c - conj c * w) / (1 - w)) := by
    rw [hinv]
    exact LiZhongQC.h36p_m_hasDerivAt γ hy
  have hD3 : HasDerivAt (fun v : ℂ => (v - c) / (v - conj c)) ((c - conj c) / (v - conj c) ^ 2)
      (h36p_m γ ((c - conj c * w) / (1 - w))) := by
    rw [hinv]
    have h := ((hasDerivAt_id' v).sub_const c).div ((hasDerivAt_id' v).sub_const (conj c)) hvden
    refine h.congr_deriv ?_
    ring
  have hderiv : deriv (fun w => (h36p_m γ ((c - conj c * w) / (1 - w)) - c) /
      (h36p_m γ ((c - conj c * w) / (1 - w)) - conj c)) w =
      (c - conj c) / (v - conj c) ^ 2 * (1 / q ^ 2 * ((c - conj c) / (1 - w) ^ 2)) := by
    have hcomp := hD3.comp w (hD2.comp w hD1)
    exact hcomp.deriv
  have hnorm : ‖deriv (fun w => (h36p_m γ ((c - conj c * w) / (1 - w)) - c) /
      (h36p_m γ ((c - conj c * w) / (1 - w)) - conj c)) w‖ =
      ‖u - conj c‖ ^ 2 / (‖v - conj c‖ ^ 2 * ‖q‖ ^ 2) := by
    have hnc := norm_pos_iff.2 hcc
    have hnu := norm_pos_iff.2 hden
    have hnv := norm_pos_iff.2 hvden
    have hnq := norm_pos_iff.2 hq0
    rw [hderiv, h1w]
    simp only [norm_mul, norm_div, norm_pow, norm_one]
    field_simp
  -- the distance side
  have hγz : ((γ • z : UpperHalfPlane) : ℂ) = v := (LiZhongQC.h36p_m_coe γ z).symm
  have hγim : (γ • z).im = u.im / ‖q‖ ^ 2 := by
    rw [← UpperHalfPlane.coe_im, hγz, hvim]
  rw [hnorm, gl2_fd_dist_lt_iff z₀ z (γ • z), hγz, hγim, ← UpperHalfPlane.coe_im, ← hu]
  have hnv := norm_pos_iff.2 hvden
  have hnq := norm_pos_iff.2 hq0
  rw [div_lt_one (by positivity), div_div_eq_mul_div, div_lt_div_iff_of_pos_right hy]

/-- **Unlabelled** (§2.9, l. 1880–1899). Let `z₀ ∈ ℍ` be nonelliptic and `B(z) = (z − z₀)/(z − z̄₀)`. The Dirichlet
domain of `Γ` centred at `z₀`, transported to the disc by `B`, is the Ford domain of `B Γ B⁻¹` in the disc. -/
theorem para2_9_ford_eq_dirichlet {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (z₀ : UpperHalfPlane) (hz₀ : ∀ γ ∈ Γ, γ • z₀ = z₀ → γ = 1 ∨ γ = -1) :
    (fun z => (z - z₀) / (z - conj (z₀ : ℂ))) '' dirichletDomain Γ z₀ =
      fordDomain {A | ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧
          A = fun w => (h36p_m γ ((z₀ - conj (z₀ : ℂ) * w) / (1 - w)) - z₀) /
            (h36p_m γ ((z₀ - conj (z₀ : ℂ) * w) / (1 - w)) - conj (z₀ : ℂ))}
        unitDisc := by
  -- `Γ` need not be Fuchsian: the identity is pointwise in `z` and `γ`
  have _hΓ := hΓ
  -- `±1` fix every point
  have hpm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ = 1 ∨ γ = -1 → γ • z₀ = z₀ := by
    rintro γ (rfl | rfl)
    · exact one_smul _ _
    · ext1
      rw [← LiZhongQC.h36p_m_coe, LiZhongQC.h36p_a_m_neg, LiZhongQC.h36p_m_coe, one_smul]
  ext w
  constructor
  · rintro ⟨_, ⟨z, rfl, hz⟩, rfl⟩
    refine ⟨gl2_fd_B_mem z₀ z, ?_⟩
    intro A hA
    obtain ⟨γ, hγ, h1, hm1, rfl⟩ := hA
    refine (gl2_fd_deriv_lt_iff z₀ γ z).2 ?_
    -- `z₀` is not elliptic, so `γ⁻¹ z₀ ≠ z₀`; and `d(z, γ⁻¹ z₀) = d(γ z, z₀)`
    have hne : γ⁻¹ • z₀ ≠ z₀ := fun h => by
      rcases hz₀ γ⁻¹ (Γ.inv_mem hγ) h with h' | h'
      · exact h1 (inv_eq_one.1 h')
      · exact hm1 (by rw [← inv_inv γ, h', inv_neg, inv_one])
    have h := hz γ⁻¹ (Γ.inv_mem hγ) hne
    rwa [← dist_smul γ z (γ⁻¹ • z₀), smul_inv_smul] at h
  · rintro ⟨hw, hA⟩
    obtain ⟨hu, hBu⟩ := gl2_fd_Binv z₀ hw
    set z : UpperHalfPlane := UpperHalfPlane.mk (((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w)) hu with hzdef
    have hzc : (z : ℂ) = ((z₀ : ℂ) - conj (z₀ : ℂ) * w) / (1 - w) := UpperHalfPlane.coe_mk _ _
    refine ⟨(z : ℂ), ⟨z, rfl, fun γ hγ hne => ?_⟩, ?_⟩
    · have h1 : γ⁻¹ ≠ 1 := fun h => hne (hpm γ (Or.inl (inv_eq_one.1 h)))
      have hm1 : γ⁻¹ ≠ -1 := fun h => hne (hpm γ (Or.inr (by rw [← inv_inv γ, h, inv_neg, inv_one])))
      have hlt := hA _ ⟨γ⁻¹, Γ.inv_mem hγ, h1, hm1, rfl⟩
      have key := gl2_fd_deriv_lt_iff z₀ γ⁻¹ z
      rw [hzc, hBu] at key
      have e : dist (γ⁻¹ • z) z₀ = dist z (γ • z₀) := by
        rw [← dist_smul γ⁻¹ z (γ • z₀), inv_smul_smul]
      rw [← e]
      exact key.1 hlt
    · show ((z : ℂ) - z₀) / ((z : ℂ) - conj (z₀ : ℂ)) = w
      rw [hzc]
      exact hBu

/-- **Definition** (§2.9, l. 1901–1906). The (noneuclidean) area `4 ∬_S ρ²(z) dx dy`, `ρ(z) = |z − z̄|⁻¹`, of a set
`S ⊆ ℍ`; the area of `ℍ/Γ` is `hypArea ω` for a fundamental domain `ω`. -/
def hypArea (S : Set ℂ) : ℝ≥0∞ := 4 * ∫⁻ z in S, ENNReal.ofReal (‖z - conj z‖⁻¹ ^ 2)

/-- Helper for `para2_9_area_indep`: the density `ρ² = |z − z̄|⁻²` of the noneuclidean area is invariant,
`ρ²(γz) |γ′(z)|² = ρ²(z)` on `ℍ` (`Im γz = Im z / |cz + d|²`, `|γ′(z)|² = |cz + d|⁻⁴`). -/
theorem gl2_fd_density_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    ENNReal.ofReal (‖h36p_m γ z - conj (h36p_m γ z)‖⁻¹ ^ 2) *
      ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = ENNReal.ofReal (‖z - conj z‖⁻¹ ^ 2) := by
  have hdet := LiZhongQC.b33_d_det γ
  have hy : 0 < z.im := hz
  have hq : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.k24_d_den_ne_zero hdet hy.ne'
  have hn : 0 < ‖(γ 1 0 : ℂ) * z + γ 1 1‖ := norm_pos_iff.2 hq
  have him : (h36p_m γ z).im = z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    unfold h36p_m
    rw [Complex.div_im]
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    rw [div_sub_div_same]
    congr 1
    linear_combination z.im * hdet
  have hY : 0 < (h36p_m γ z).im := by
    rw [him]
    positivity
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_two, abs_of_pos hY, abs_of_pos hy, him]
  have hn' := hn.ne'
  have hy' := hy.ne'
  field_simp

/-- Helper for `para2_9_area_indep`: for a fundamental domain `F`, almost every `z ∈ ℍ` has exactly
`m = |Γ ∩ {±1}|` elements `γ ∈ Γ` with `γz ∈ F` (covering, and `h36p_ae_unique`: they form one class `±γ₀`). -/
theorem gl2_fd_count {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      ∑' γ : Γ, (h36p_m γ.1 ⁻¹' F).indicator (fun _ => (1 : ℝ≥0∞)) z =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
  have hF' := hF
  obtain ⟨-, -, hcov, -, -⟩ := hF
  filter_upwards [LiZhongQC.h36p_ae_unique hΓ hF', ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet]
    with w hu hw
  have hrw : ∀ γ : Γ, (h36p_m γ.1 ⁻¹' F).indicator (fun _ => (1 : ℝ≥0∞)) w =
      {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => (1 : ℝ≥0∞)) γ := fun γ => by
    by_cases h : h36p_m γ.1 w ∈ F
    · rw [indicator_of_mem (show w ∈ h36p_m γ.1 ⁻¹' F from h),
        indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
    · rw [indicator_of_notMem (show w ∉ h36p_m γ.1 ⁻¹' F from h),
        indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
  rw [tsum_congr hrw]
  obtain ⟨γ₀, hγ₀, hγ₀F⟩ := hcov ⟨w, hw⟩
  have hγ₀F' : h36p_m γ₀ w ∈ F := by
    have e := LiZhongQC.h36p_m_coe γ₀ ⟨w, hw⟩
    simp only at e
    rw [e]
    exact hγ₀F
  have h := LiZhongQC.h36p_a_count (P := fun γ => h36p_m γ w ∈ F) hγ₀
    (fun γ hγ => ⟨fun h => hu γ hγ γ₀ hγ₀ h hγ₀F', by
      rintro (rfl | rfl)
      · exact hγ₀F'
      · show h36p_m (-γ₀) w ∈ F
        rw [LiZhongQC.h36p_a_m_neg]
        exact hγ₀F'⟩) 1
  rw [h, mul_one]

/-- Helper for `para2_9_area_indep`: unfolding `F'` over the translates of `F` gives
`m ∬_{F'} ρ² = Σ_γ ∬_F 𝟙_{F'}(γz) ρ²(z) = ∬_F #{γ : γz ∈ F'} ρ² = m ∬_F ρ²` (`h36p_unfold`, `gl2_fd_density_inv`,
`gl2_fd_count`). -/
theorem gl2_fd_unfold {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F F' : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) (hF' : IsFundamentalDomainH Γ F') :
    (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in F', ENNReal.ofReal (‖z - conj z‖⁻¹ ^ 2) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in F, ENNReal.ofReal (‖z - conj z‖⁻¹ ^ 2) := by
  have : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  set ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z - conj z‖⁻¹ ^ 2) with hρdef
  have hρ : Measurable ρ := by
    rw [hρdef]
    fun_prop
  have hFH := hF.1
  have hFm := hF.2.1
  have hF'H := hF'.1
  have hF'm := hF'.2.1
  have hind : Measurable (F'.indicator ρ) := hρ.indicator hF'm
  have h1 : ∫⁻ z in F', ρ z = ∫⁻ z in upperHalf, F'.indicator ρ z := by
    rw [lintegral_indicator hF'm, Measure.restrict_restrict hF'm, inter_eq_left.2 hF'H]
  have h2 : ∀ γ : Γ, ∫⁻ z in F, F'.indicator ρ (h36p_m γ.1 z) *
      ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) =
      ∫⁻ z in F, (h36p_m γ.1 ⁻¹' F').indicator (fun _ => (1 : ℝ≥0∞)) z * ρ z := fun γ => by
    refine setLIntegral_congr_fun hFm fun z hz => ?_
    by_cases h : h36p_m γ.1 z ∈ F'
    · rw [indicator_of_mem h, indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' F' from h), one_mul]
      exact gl2_fd_density_inv γ.1 (hFH hz)
    · rw [indicator_of_notMem h, indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' F' from h), zero_mul, zero_mul]
  have hmeas : ∀ γ : Γ, AEMeasurable (fun z => (h36p_m γ.1 ⁻¹' F').indicator (fun _ => (1 : ℝ≥0∞)) z * ρ z)
      (volume.restrict F) := fun γ =>
    ((measurable_const.indicator (LiZhongQC.h36p_m_measurable _ hF'm)).mul hρ).aemeasurable
  have hcnt : ∀ᵐ z ∂(volume.restrict F), ∑' γ : Γ, (h36p_m γ.1 ⁻¹' F').indicator (fun _ => (1 : ℝ≥0∞)) z =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) :=
    ae_restrict_of_ae_restrict_of_subset hFH (gl2_fd_count hΓ hF')
  rw [h1, ← LiZhongQC.h36p_unfold hΓ hF hind, tsum_congr h2, ← lintegral_tsum hmeas, ← lintegral_const_mul _ hρ]
  refine lintegral_congr_ae ?_
  filter_upwards [hcnt] with z hz
  rw [ENNReal.tsum_mul_right, hz]

/-- **Unlabelled** (§2.9, l. 1907–1913). The area of `ℍ/Γ` does not depend on the fundamental domain. -/
theorem para2_9_area_indep {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {F₁ F₂ : Set ℂ} (h₁ : IsFundamentalDomainH Γ F₁) (h₂ : IsFundamentalDomainH Γ F₂) :
    hypArea F₁ = hypArea F₂ := by
  -- `m A(F₂) = m A(F₁)` with the multiplicity `m = |Γ ∩ {±1}| ∈ (0, ∞)`
  have hm0 : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne'
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h := gl2_fd_unfold hΓ h₁ h₂
  rw [hypArea, hypArea, (ENNReal.mul_right_inj hm0 hm).1 h.symm]

/-- **Definition** (§2.9, l. 1916). `Γ` is of the first kind if its limit set is all of `ℝ̂` (of the second kind
otherwise). -/
def IsFirstKind (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop := fuchsianLimitSet Γ = extRealLine

/-- Helper for **Theorem 3** (§2.9). A hyperbolic line of `ℍ`: a half circle centred on `ℝ` or a vertical half line
(as a subset of `ℂ`). -/
def IsHypLine (L : Set ℂ) : Prop :=
  (∃ (c : ℝ) (r : ℝ), 0 < r ∧ L = {z ∈ upperHalf | ‖z - c‖ = r}) ∨ ∃ a : ℝ, L = {z ∈ upperHalf | z.re = a}

/-- Helper for **Theorem 3** (§2.9, l. 1922). `ω` has finitely many sides and no free sides: its boundary in `ℍ` is
covered by finitely many hyperbolic lines, and its closure in `ℂ̄` meets `ℝ̂` in finitely many points. -/
def HasFiniteSidesNoFreeSides (ω : Set ℂ) : Prop :=
  (∃ L : Finset (Set ℂ), (∀ l ∈ L, IsHypLine l) ∧ frontier ω ∩ upperHalf ⊆ ⋃ l ∈ L, l) ∧
    (closure (toExt ω) ∩ extRealLine).Finite

/-- **Theorem 3** (§2.9, l. 1920). For a Fuchsian group `Γ` and its Dirichlet domain `ω` (2.27), the following are
equivalent: (a) `ℍ/Γ` has finite area; (b) `ω` has finitely many sides and no free sides; (c) `Γ` is finitely
generated and of the first kind. -/
theorem thm2_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (z₀ : UpperHalfPlane)
    (hz₀ : ∀ γ ∈ Γ, γ • z₀ = z₀ → γ = 1 ∨ γ = -1) :
    List.TFAE [hypArea (dirichletDomain Γ z₀) < ⊤, HasFiniteSidesNoFreeSides (dirichletDomain Γ z₀),
      Group.FG Γ ∧ IsFirstKind Γ] := by
  sorry

end GardinerLakic2000
