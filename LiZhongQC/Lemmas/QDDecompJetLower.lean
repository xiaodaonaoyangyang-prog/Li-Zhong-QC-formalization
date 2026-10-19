import LiZhongQC.Lemmas.QDReflectAcrossArc

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Points of a periodic simple closed curve close to `c s` are of the form `c (s + d)` with `|d|` small. -/
theorem s31qj_lb_near_param {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ s u : ℝ, ‖c u - c s‖ < ε → ∃ d : ℝ, |d| < η ∧ c u = c (s + d) := by
  have hp : Function.Periodic c 1 := hper
  obtain ⟨ε, hε, hgap⟩ := s31qk_curve_gap hc.continuous hper hinj (lt_min hη (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨ε, hε, fun s u hu => ?_⟩
  set k : ℤ := round (u - s) with hk
  set d : ℝ := u - s - k with hd
  have hd2 : |d| ≤ 1 / 2 := by simpa [hd] using abs_sub_round (u - s)
  have hcu : c u = c (s + d) := by
    have := (hp.int_mul k) (s + d)
    rw [mul_one, show s + d + k = u by rw [hd]; ring] at this
    exact this
  refine ⟨d, ?_, hcu⟩
  by_contra hnot
  push Not at hnot
  have hmin : min η (1 / 2) ≤ |d| := (min_le_left _ _).trans hnot
  have := hgap s d hmin hd2
  rw [← hcu] at this
  linarith

/-- The derivative of a smooth regular curve is Lipschitz with the Taylor constant: `‖c'(s+d) - c'(s)‖ ≤ 2 M |d|`. -/
theorem s31qj_lb_deriv_lip {c : ℝ → ℂ} {M : ℝ}
    (htay : ∀ s d : ℝ, ‖c (s + d) - c s - (d : ℂ) * deriv c s‖ ≤ M * d ^ 2) (s d : ℝ) :
    ‖deriv c (s + d) - deriv c s‖ ≤ 2 * M * |d| := by
  by_cases hd : d = 0
  · subst hd; simp
  have h1 := htay s d
  have h2 := htay (s + d) (-d)
  rw [show s + d + -d = s by ring] at h2
  have hsum : (d : ℂ) * (deriv c (s + d) - deriv c s) =
      (c (s + d) - c s - (d : ℂ) * deriv c s) + (c s - c (s + d) - ((-d : ℝ) : ℂ) * deriv c (s + d)) := by
    push_cast; ring
  have h3 : ‖(d : ℂ) * (deriv c (s + d) - deriv c s)‖ ≤ 2 * (M * d ^ 2) := by
    rw [hsum]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ M * d ^ 2 + M * (-d) ^ 2 := add_le_add h1 h2
      _ = 2 * (M * d ^ 2) := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h3
  have hd0 : 0 < |d| := abs_pos.2 hd
  have : |d| * ‖deriv c (s + d) - deriv c s‖ ≤ |d| * (2 * M * |d|) := by
    calc _ ≤ 2 * (M * d ^ 2) := h3
      _ = |d| * (2 * M * |d|) := by rw [← sq_abs d]; ring
  exact le_of_mul_le_mul_left this hd0

/-- **Vertical uniqueness.**  Two points of the curve in a small ball around `c s` whose difference is
orthogonal to the tangent direction `c'(s)` coincide. -/
theorem s31qj_lb_vert_unique {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) :
    ∃ r₁ > 0, ∀ s u₁ u₂ : ℝ, ‖c u₁ - c s‖ < r₁ → ‖c u₂ - c s‖ < r₁ →
      ((c u₁ - c u₂) * conj (deriv c s)).re = 0 → c u₁ = c u₂ := by
  obtain ⟨δ, M, hδ, hM, hlow, hup, htay⟩ := s31qk_curve_bounds hc hc' hper
  set η : ℝ := δ ^ 2 / (8 * M ^ 2) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ε, hε, hnear⟩ := s31qj_lb_near_param hc hper hinj hη0
  refine ⟨ε, hε, fun s u₁ u₂ h₁ h₂ hre => ?_⟩
  obtain ⟨d₁, hd₁, e₁⟩ := hnear s u₁ h₁
  obtain ⟨d₂, hd₂, e₂⟩ := hnear s u₂ h₂
  rw [e₁, e₂] at hre ⊢
  set c₀ := deriv c s with hc₀
  set c₁ := deriv c (s + d₁) with hc₁
  set D : ℝ := d₂ - d₁ with hD
  by_contra hne
  have hD0 : D ≠ 0 := by
    intro h0
    apply hne
    rw [show d₂ = d₁ by linarith]
  have hΔ := s31qj_lb_deriv_lip htay s d₁
  have hE := htay (s + d₁) D
  rw [show s + d₁ + D = s + d₂ by rw [hD]; ring] at hE
  set E : ℂ := c (s + d₂) - c (s + d₁) - (D : ℂ) * c₁ with hEdef
  have hA : c (s + d₁) - c (s + d₂) = -((D : ℂ) * c₁ + E) := by rw [hEdef]; ring
  rw [hA] at hre
  have hre' : ((D : ℂ) * c₁ * conj c₀).re + (E * conj c₀).re = 0 := by
    have : (-((D : ℂ) * c₁ + E) * conj c₀).re = -(((D : ℂ) * c₁ * conj c₀).re + (E * conj c₀).re) := by
      rw [neg_mul, Complex.neg_re, add_mul, Complex.add_re]
    rw [this] at hre
    linarith
  have hc1c0 : (c₁ * conj c₀).re = ‖c₀‖ ^ 2 + ((c₁ - c₀) * conj c₀).re := by
    have : c₁ * conj c₀ = (c₀ * conj c₀) + (c₁ - c₀) * conj c₀ := by ring
    rw [this, Complex.add_re, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_re]
  have hDre : ((D : ℂ) * c₁ * conj c₀).re = D * (c₁ * conj c₀).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  have hc0M : ‖c₀‖ ≤ M := hup s
  have hc0δ : δ ≤ ‖c₀‖ := hlow s
  have hr1 : |((c₁ - c₀) * conj c₀).re| ≤ 2 * M * |d₁| * M := by
    calc _ ≤ ‖(c₁ - c₀) * conj c₀‖ := Complex.abs_re_le_norm _
      _ = ‖c₁ - c₀‖ * ‖c₀‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ 2 * M * |d₁| * M := by gcongr
  have hr2 : |(E * conj c₀).re| ≤ M * D ^ 2 * M := by
    calc _ ≤ ‖E * conj c₀‖ := Complex.abs_re_le_norm _
      _ = ‖E‖ * ‖c₀‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ M * D ^ 2 * M := by gcongr
  -- combine
  have hk : (c₁ * conj c₀).re ≥ δ ^ 2 - 2 * M * |d₁| * M := by
    have h1 : δ ^ 2 ≤ ‖c₀‖ ^ 2 := by nlinarith
    have := neg_abs_le ((c₁ - c₀) * conj c₀).re
    linarith
  have hD2 : |D| < 2 * η := by
    rw [hD]
    calc |d₂ - d₁| ≤ |d₂| + |d₁| := abs_sub _ _
      _ < 2 * η := by linarith
  have hd1η : |d₁| < η := hd₁
  have hM2 : 0 < M ^ 2 := by positivity
  have hηM : 8 * M ^ 2 * η = δ ^ 2 := by rw [hη]; field_simp
  -- `|D| (δ² - 2M²η) ≤ M² D²`
  have hmain : D * (c₁ * conj c₀).re = -(E * conj c₀).re := by linarith
  have hab : |D| * (δ ^ 2 - 2 * M * |d₁| * M) ≤ M * D ^ 2 * M := by
    have h1 : |D * (c₁ * conj c₀).re| ≤ M * D ^ 2 * M := by
      rw [hmain, abs_neg]; exact hr2
    rw [abs_mul] at h1
    have h2 : 0 ≤ (c₁ * conj c₀).re := by
      have : 0 ≤ δ ^ 2 - 2 * M * |d₁| * M := by nlinarith
      linarith
    rw [abs_of_nonneg h2] at h1
    calc |D| * (δ ^ 2 - 2 * M * |d₁| * M) ≤ |D| * (c₁ * conj c₀).re :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg D)
      _ ≤ _ := h1
  have hDpos : 0 < |D| := abs_pos.2 hD0
  have hfin : δ ^ 2 - 2 * M * |d₁| * M ≤ M * |D| * M := by
    have : |D| * (δ ^ 2 - 2 * M * |d₁| * M) ≤ |D| * (M * |D| * M) := by
      calc _ ≤ M * D ^ 2 * M := hab
        _ = |D| * (M * |D| * M) := by rw [← sq_abs D]; ring
    exact le_of_mul_le_mul_left this hDpos
  nlinarith

/-- Uniqueness of curve points on a line orthogonal to the tangent at `c s`. -/
theorem s31qj_lb_line_unique {c : ℝ → ℂ} {r₁ : ℝ}
    (hvu : ∀ s u₁ u₂ : ℝ, ‖c u₁ - c s‖ < r₁ → ‖c u₂ - c s‖ < r₁ →
      ((c u₁ - c u₂) * conj (deriv c s)).re = 0 → c u₁ = c u₂)
    {s : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hperp : (e * conj (deriv c s)).re = 0) {x l₁ l₂ : ℝ}
    (h₁ : c s + ((l₁ : ℂ) + x * I) * e ∈ range c) (h₂ : c s + ((l₂ : ℂ) + x * I) * e ∈ range c)
    (n₁ : ‖((l₁ : ℂ) + x * I) * e‖ < r₁) (n₂ : ‖((l₂ : ℂ) + x * I) * e‖ < r₁) : l₁ = l₂ := by
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  have d₁ : ‖c u₁ - c s‖ < r₁ := by
    rw [hu₁, add_sub_cancel_left]; exact n₁
  have d₂ : ‖c u₂ - c s‖ < r₁ := by
    rw [hu₂, add_sub_cancel_left]; exact n₂
  have hdiff : c u₁ - c u₂ = ((l₁ - l₂ : ℝ) : ℂ) * e := by
    rw [hu₁, hu₂]; push_cast; ring
  have h := hvu s u₁ u₂ d₁ d₂ (by
    rw [hdiff, mul_assoc, Complex.re_ofReal_mul, hperp, mul_zero])
  have h0 : e ≠ 0 := norm_pos_iff.1 (by rw [he]; exact one_pos)
  rw [hu₁, hu₂] at h
  have h4 : ((l₁ : ℂ) + x * I) * e = ((l₂ : ℂ) + x * I) * e := add_left_cancel h
  have h5 := mul_right_cancel₀ h0 h4
  have := congrArg Complex.re h5
  simpa using this

theorem s31qj_lb_two {A B Z q : ℝ} (hZ : Z ∈ uIcc A B) (h1 : q ∈ uIcc Z A) (h2 : q ∈ uIcc Z B) :
    q = Z := by
  rw [Set.mem_uIcc] at hZ h1 h2
  rcases hZ with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h1 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
    rcases h2 with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> linarith

theorem s31qj_lb_three {A B Z q : ℝ} (h1 : q ∈ uIcc A Z) (h2 : q ∈ uIcc Z B) (h3 : q ∈ uIcc A B) :
    q = A ∨ q = Z ∨ q = B := by
  rw [Set.mem_uIcc] at h1 h2 h3
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rcases h3 with ⟨c1, c2⟩ | ⟨c1, c2⟩
  all_goals first
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; linarith)
    | (exfalso; linarith)

section Lines
variable {Jd : Set ℂ} {G : ℝ → ℂ}

/-- A path from a point of `Jd` to a point outside its closure meets the frontier. -/
theorem s31qj_lb_cross (hG : Continuous G) {A B : ℝ} (hA : G A ∈ Jd) (hJ : IsOpen Jd)
    (hB : G B ∉ closure Jd) : ∃ l ∈ uIcc A B, G l ∈ frontier Jd := by
  by_contra hne
  push Not at hne
  have hpc : IsPreconnected (G '' uIcc A B) := isPreconnected_uIcc.image G hG.continuousOn
  have hdis : Disjoint (G '' uIcc A B) (frontier Jd) := by
    rw [Set.disjoint_left]
    rintro _ ⟨l, hl, rfl⟩ hf
    exact hne l hl hf
  have := s31qk_subset_exterior hJ hpc hdis (y := G B) ⟨B, right_mem_uIcc, rfl⟩ hB
  exact this ⟨A, left_mem_uIcc, rfl⟩ (subset_closure hA)

theorem s31qj_lb_not_mem_frontier (hJ : IsOpen Jd) {z : ℂ} (hz : z ∈ Jd) : z ∉ frontier Jd := by
  rw [frontier, hJ.interior_eq]; exact fun h => h.2 hz

/-- Within the uniqueness window, `G l` outside the closure and `G A ∈ Jd`: the whole segment from `Z` to `B`
stays outside the closure when `G Z` and `G B` do. -/
theorem s31qj_lb_ext_seg (hG : Continuous G) (hJ : IsOpen Jd) {I : Set ℝ} (hI : I.OrdConnected)
    (huq : ∀ l₁ l₂, l₁ ∈ I → l₂ ∈ I → G l₁ ∈ frontier Jd → G l₂ ∈ frontier Jd → l₁ = l₂)
    {A Z B : ℝ} (hAI : A ∈ I) (hZI : Z ∈ I) (hBI : B ∈ I) (hA : G A ∈ Jd)
    (hZ : G Z ∉ closure Jd) (hB : G B ∉ closure Jd) : ∀ l ∈ uIcc Z B, G l ∉ closure Jd := by
  obtain ⟨q₁, hq₁, hq₁f⟩ := s31qj_lb_cross hG hA hJ hB
  obtain ⟨q₂, hq₂, hq₂f⟩ := s31qj_lb_cross hG hA hJ hZ
  have hq₁I : q₁ ∈ I := hI.uIcc_subset hAI hBI hq₁
  have hq₂I : q₂ ∈ I := hI.uIcc_subset hAI hZI hq₂
  have hq : q₁ = q₂ := huq _ _ hq₁I hq₂I hq₁f hq₂f
  rw [← hq] at hq₂
  have hmiss : ∀ l ∈ uIcc Z B, G l ∉ frontier Jd := by
    intro l hl hlf
    have hlI : l ∈ I := hI.uIcc_subset hZI hBI hl
    have hlq : l = q₁ := huq _ _ hlI hq₁I hlf hq₁f
    rw [hlq] at hl
    rcases s31qj_lb_three hq₂ hl hq₁ with h | h | h
    · rw [h] at hq₁f; exact s31qj_lb_not_mem_frontier hJ hA hq₁f
    · rw [h] at hq₁f; exact hZ (frontier_subset_closure hq₁f)
    · rw [h] at hq₁f; exact hB (frontier_subset_closure hq₁f)
  have hpc : IsPreconnected (G '' uIcc Z B) := isPreconnected_uIcc.image G hG.continuousOn
  have hdis : Disjoint (G '' uIcc Z B) (frontier Jd) := by
    rw [Set.disjoint_left]
    rintro _ ⟨l, hl, rfl⟩ hf
    exact hmiss l hl hf
  intro l hl
  exact s31qk_subset_exterior hJ hpc hdis (y := G Z) ⟨Z, left_mem_uIcc, rfl⟩ hZ ⟨l, hl, rfl⟩

/-- **Side lemma.**  A point of `Jd` cannot lie between two points outside its closure on a line meeting the
frontier at most once. -/
theorem s31qj_lb_between (hG : Continuous G) (hJ : IsOpen Jd) {I : Set ℝ} (hI : I.OrdConnected)
    (huq : ∀ l₁ l₂, l₁ ∈ I → l₂ ∈ I → G l₁ ∈ frontier Jd → G l₂ ∈ frontier Jd → l₁ = l₂)
    {A B Z : ℝ} (hAI : A ∈ I) (hBI : B ∈ I) (hZ : Z ∈ uIcc A B)
    (hA : G A ∉ closure Jd) (hB : G B ∉ closure Jd) : G Z ∉ Jd := by
  intro hZJ
  have hZI : Z ∈ I := hI.uIcc_subset hAI hBI hZ
  obtain ⟨q₁, hq₁, hq₁f⟩ := s31qj_lb_cross hG hZJ hJ hA
  obtain ⟨q₂, hq₂, hq₂f⟩ := s31qj_lb_cross hG hZJ hJ hB
  have hq₁I : q₁ ∈ I := hI.uIcc_subset hZI hAI hq₁
  have hq₂I : q₂ ∈ I := hI.uIcc_subset hZI hBI hq₂
  have hq : q₁ = q₂ := huq _ _ hq₁I hq₂I hq₁f hq₂f
  rw [← hq] at hq₂
  have := s31qj_lb_two hZ hq₁ hq₂
  rw [this] at hq₁f
  exact s31qj_lb_not_mem_frontier hJ hZJ hq₁f

end Lines

theorem s31qj_lb_dichotomy {Jd : Set ℂ} (hJ : IsOpen Jd) {S : Set ℂ} (hS : IsPreconnected S)
    (hdis : Disjoint S (frontier Jd)) : S ⊆ Jd ∨ S ⊆ (closure Jd)ᶜ := by
  by_cases h : ∃ y ∈ S, y ∉ closure Jd
  · obtain ⟨y, hyS, hy⟩ := h
    exact Or.inr (s31qk_subset_exterior hJ hS hdis hyS hy)
  · push Not at h
    left
    intro z hz
    have hzc : z ∈ closure Jd := h z hz
    by_contra hzJ
    exact Set.disjoint_left.1 hdis hz ⟨hzc, by rwa [hJ.interior_eq]⟩

/-- Coordinates in the frame `(p, e)`: `z = p + (u.re + u.im I) e` with `u = (z - p) ē`. -/
theorem s31qj_lb_coord {e : ℂ} (he : ‖e‖ = 1) (p z : ℂ) :
    p + ((((z - p) * conj e).re : ℝ) + (((z - p) * conj e).im : ℝ) * I) * e = z := by
  have h1 : conj e * e = 1 := by
    rw [Complex.conj_mul', he]; simp
  rw [Complex.re_add_im]
  calc p + (z - p) * conj e * e = p + (z - p) * (conj e * e) := by ring
    _ = z := by rw [h1]; ring

theorem s31qj_lb_Gnorm {e : ℂ} (he : ‖e‖ = 1) (l x : ℝ) :
    ‖((l : ℂ) + (x : ℂ) * I) * e‖ ≤ |l| + |x| := by
  rw [norm_mul, he, mul_one]
  calc ‖(l : ℂ) + (x : ℂ) * I‖ ≤ ‖(l : ℂ)‖ + ‖(x : ℂ) * I‖ := norm_add_le _ _
    _ = |l| + |x| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]

theorem s31qj_lb_Gdiff {e : ℂ} (he : ‖e‖ = 1) (p : ℂ) (l x a : ℝ) :
    ‖(p + ((l : ℂ) + (x : ℂ) * I) * e) - (p + (a : ℂ) * e)‖ = ‖((l - a : ℝ) : ℂ) + (x : ℂ) * I‖ := by
  have : (p + ((l : ℂ) + (x : ℂ) * I) * e) - (p + (a : ℂ) * e) =
      (((l - a : ℝ) : ℂ) + (x : ℂ) * I) * e := by push_cast; ring
  rw [this, norm_mul, he, mul_one]

theorem s31qj_lb_cnorm_lt {a x ρ : ℝ} (hρ : 0 < ρ) (h : a ^ 2 + x ^ 2 < ρ ^ 2) :
    ‖(a : ℂ) + (x : ℂ) * I‖ < ρ := by
  by_contra hge
  push Not at hge
  have h2 : ‖(a : ℂ) + (x : ℂ) * I‖ ^ 2 = a ^ 2 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  nlinarith [mul_self_le_mul_self hρ.le hge]

/-- **Side lemma (S6a).**  If the tangent disc on one side of a `C^∞` arc is outside `closure Jd`, the tangent
disc on the other side lies in `Jd`. -/
theorem s31qj_lb_side {c : ℝ → ℂ} {Jd : Set ℂ} (hJ : IsOpen Jd) (hfr : frontier Jd = range c) {r₁ : ℝ}
    (hvu : ∀ s u₁ u₂ : ℝ, ‖c u₁ - c s‖ < r₁ → ‖c u₂ - c s‖ < r₁ →
      ((c u₁ - c u₂) * conj (deriv c s)).re = 0 → c u₁ = c u₂)
    {s : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hperp : (e * conj (deriv c s)).re = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : 2 * ρ < r₁) (hmiss : ∀ t, ρ ≤ ‖c t - (c s + ((-ρ : ℝ) : ℂ) * e)‖)
    (hT : ball (c s + (ρ : ℂ) * e) ρ ⊆ (closure Jd)ᶜ) : ball (c s + ((-ρ : ℝ) : ℂ) * e) ρ ⊆ Jd := by
  have hdis : Disjoint (ball (c s + ((-ρ : ℝ) : ℂ) * e) ρ) (frontier Jd) := by
    rw [hfr, Set.disjoint_right]
    rintro _ ⟨t, rfl⟩ hb
    rw [mem_ball, dist_eq_norm] at hb
    exact absurd (hmiss t) (not_le.2 hb)
  rcases s31qj_lb_dichotomy hJ (convex_ball _ ρ).isPreconnected hdis with h | h
  · exact h
  exfalso
  have hcs : c s ∈ closure Jd := frontier_subset_closure (hfr ▸ mem_range_self s)
  obtain ⟨j, hjJ, hj⟩ := Metric.mem_closure_iff.1 hcs (ρ / 2) (by positivity)
  set u : ℂ := (j - c s) * conj e with hu
  have hjn : ‖u‖ < ρ / 2 := by
    rw [hu, norm_mul, Complex.norm_conj, he, mul_one, ← dist_eq_norm, dist_comm]; exact hj
  have hre : |u.re| < ρ / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm u) hjn
  have him : |u.im| < ρ / 2 := lt_of_le_of_lt (Complex.abs_im_le_norm u) hjn
  set G : ℝ → ℂ := fun l => c s + ((l : ℂ) + (u.im : ℂ) * I) * e with hG
  have hGc : Continuous G := by simp only [hG]; fun_prop
  have hjG : G u.re = j := s31qj_lb_coord he (c s) j
  have huq : ∀ l₁ l₂, l₁ ∈ Icc (-ρ) ρ → l₂ ∈ Icc (-ρ) ρ → G l₁ ∈ frontier Jd → G l₂ ∈ frontier Jd →
      l₁ = l₂ := by
    intro l₁ l₂ h₁ h₂ f₁ f₂
    rw [hfr] at f₁ f₂
    refine s31qj_lb_line_unique hvu he hperp f₁ f₂ ?_ ?_
    · refine lt_of_le_of_lt (s31qj_lb_Gnorm he l₁ u.im) ?_
      have := abs_le.2 h₁; linarith
    · refine lt_of_le_of_lt (s31qj_lb_Gnorm he l₂ u.im) ?_
      have := abs_le.2 h₂; linarith
  have hA : G (-ρ) ∉ closure Jd := by
    refine h ?_
    rw [mem_ball, dist_eq_norm, hG]
    simp only
    rw [s31qj_lb_Gdiff he (c s) (-ρ) u.im (-ρ), sub_self, Complex.ofReal_zero, zero_add, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hB : G ρ ∉ closure Jd := by
    refine hT ?_
    rw [mem_ball, dist_eq_norm, hG]
    simp only
    rw [s31qj_lb_Gdiff he (c s) ρ u.im ρ, sub_self, Complex.ofReal_zero, zero_add, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hZ : u.re ∈ uIcc (-ρ) ρ := by
    rw [uIcc_of_le (by linarith)]
    have := abs_lt.1 hre
    exact ⟨by linarith, by linarith⟩
  have := s31qj_lb_between hGc hJ ordConnected_Icc huq (A := -ρ) (B := ρ) (Z := u.re)
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ hZ hA hB
  exact this (hjG ▸ hjJ)

theorem s31qj_lb_u_of_G {e : ℂ} (he : ‖e‖ = 1) (p : ℂ) (l x : ℝ) :
    ((p + ((l : ℂ) + (x : ℂ) * I) * e) - p) * conj e = (l : ℂ) + (x : ℂ) * I := by
  have h1 : conj e * e = 1 := by
    rw [Complex.conj_mul', he]; simp
  calc ((p + ((l : ℂ) + (x : ℂ) * I) * e) - p) * conj e
      = ((l : ℂ) + (x : ℂ) * I) * (conj e * e) := by ring
    _ = _ := by rw [h1]; ring

theorem s31qj_lb_uc {l x : ℝ} : (((l : ℂ) + (x : ℂ) * I).re = l) ∧ (((l : ℂ) + (x : ℂ) * I).im = x) := by
  constructor <;> simp

/-- Uniqueness of frontier points on a vertical line inside the window. -/
theorem s31qj_lb_huq {c : ℝ → ℂ} {Jd : Set ℂ} (hfr : frontier Jd = range c) {r₁ : ℝ}
    (hvu : ∀ s u₁ u₂ : ℝ, ‖c u₁ - c s‖ < r₁ → ‖c u₂ - c s‖ < r₁ →
      ((c u₁ - c u₂) * conj (deriv c s)).re = 0 → c u₁ = c u₂)
    {s : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hperp : (e * conj (deriv c s)).re = 0) {ρ x : ℝ}
    (hρr : 2 * ρ < r₁) (hx : |x| < ρ) :
    ∀ l₁ l₂, l₁ ∈ Icc (-ρ) ρ → l₂ ∈ Icc (-ρ) ρ →
      (fun l : ℝ => c s + ((l : ℂ) + (x : ℂ) * I) * e) l₁ ∈ frontier Jd →
      (fun l : ℝ => c s + ((l : ℂ) + (x : ℂ) * I) * e) l₂ ∈ frontier Jd → l₁ = l₂ := by
  intro l₁ l₂ h₁ h₂ f₁ f₂
  rw [hfr] at f₁ f₂
  refine s31qj_lb_line_unique hvu he hperp f₁ f₂ ?_ ?_
  · refine lt_of_le_of_lt (s31qj_lb_Gnorm he l₁ x) ?_
    have := abs_le.2 h₁; linarith
  · refine lt_of_le_of_lt (s31qj_lb_Gnorm he l₂ x) ?_
    have := abs_le.2 h₂; linarith

/-- **Box connectedness (S6a).**  Near a point `c s` of a `C^∞` arc whose exterior tangent disc is
`ball (c s + ρ e) ρ`, the exterior of `Jd` inside the box `|Re u|, |Im u| < ρ/2`, `u = (z - c s) ē`, is connected. -/
theorem s31qj_lb_box_conn {c : ℝ → ℂ} {Jd : Set ℂ} (hJ : IsOpen Jd) (hfr : frontier Jd = range c) {r₁ : ℝ}
    (hvu : ∀ s u₁ u₂ : ℝ, ‖c u₁ - c s‖ < r₁ → ‖c u₂ - c s‖ < r₁ →
      ((c u₁ - c u₂) * conj (deriv c s)).re = 0 → c u₁ = c u₂)
    {s : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hperp : (e * conj (deriv c s)).re = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : 2 * ρ < r₁) (hmiss : ∀ t, ρ ≤ ‖c t - (c s + ((-ρ : ℝ) : ℂ) * e)‖)
    (hT : ball (c s + (ρ : ℂ) * e) ρ ⊆ (closure Jd)ᶜ) :
    IsPreconnected ({z : ℂ | |((z - c s) * conj e).re| < ρ / 2 ∧ |((z - c s) * conj e).im| < ρ / 2} ∩
      (closure Jd)ᶜ) := by
  have hB := s31qj_lb_side hJ hfr hvu he hperp hρ hρr hmiss hT
  set N : Set ℂ := {z : ℂ | |((z - c s) * conj e).re| < ρ / 2 ∧ |((z - c s) * conj e).im| < ρ / 2} with hN
  set G : ℝ → ℝ → ℂ := fun x l => c s + ((l : ℂ) + (x : ℂ) * I) * e with hG
  have hGc : ∀ x, Continuous (G x) := fun x => by simp only [hG]; fun_prop
  have hGN : ∀ x l : ℝ, |l| < ρ / 2 → |x| < ρ / 2 → G x l ∈ N := by
    intro x l hl hx
    refine ⟨?_, ?_⟩
    · show |(((c s + ((l : ℂ) + (x : ℂ) * I) * e) - c s) * conj e).re| < ρ / 2
      rw [s31qj_lb_u_of_G he, (s31qj_lb_uc).1]; exact hl
    · show |(((c s + ((l : ℂ) + (x : ℂ) * I) * e) - c s) * conj e).im| < ρ / 2
      rw [s31qj_lb_u_of_G he, (s31qj_lb_uc).2]; exact hx
  have hGT : ∀ x : ℝ, |x| < ρ / 2 → G x (ρ / 4) ∈ ball (c s + (ρ : ℂ) * e) ρ := by
    intro x hx
    rw [mem_ball, dist_eq_norm]
    show ‖(c s + (((ρ / 4 : ℝ) : ℂ) + (x : ℂ) * I) * e) - (c s + (ρ : ℂ) * e)‖ < ρ
    rw [s31qj_lb_Gdiff he (c s) (ρ / 4) x ρ]
    refine s31qj_lb_cnorm_lt hρ ?_
    have := abs_lt.1 hx
    nlinarith
  have hGB : ∀ x : ℝ, |x| < ρ / 2 → G x (-ρ) ∈ ball (c s + ((-ρ : ℝ) : ℂ) * e) ρ := by
    intro x hx
    rw [mem_ball, dist_eq_norm]
    show ‖(c s + (((-ρ : ℝ) : ℂ) + (x : ℂ) * I) * e) - (c s + ((-ρ : ℝ) : ℂ) * e)‖ < ρ
    rw [s31qj_lb_Gdiff he (c s) (-ρ) x (-ρ), sub_self, Complex.ofReal_zero, zero_add, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_lt.1 hx]
  set Sg : Set ℂ := (fun x : ℝ => G x (ρ / 4)) '' Ioo (-(ρ / 2)) (ρ / 2) with hSg
  have hSgpc : IsPreconnected Sg :=
    isPreconnected_Ioo.image _ (by simp only [hG]; fun_prop : Continuous fun x : ℝ => G x (ρ / 4)).continuousOn
  have hSgE : Sg ⊆ N ∩ (closure Jd)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : |x| < ρ / 2 := abs_lt.2 ⟨by linarith [hx.1], hx.2⟩
    exact ⟨hGN x (ρ / 4) (by rw [abs_of_pos (by positivity)]; linarith) hx', hT (hGT x hx')⟩
  have h0 : G 0 (ρ / 4) ∈ Sg := ⟨0, ⟨by linarith, by linarith⟩, rfl⟩
  refine isPreconnected_of_forall (G 0 (ρ / 4)) fun y hy => ?_
  obtain ⟨hyN, hyE⟩ := hy
  set u : ℂ := (y - c s) * conj e with hu
  have hyG : G u.im u.re = y := s31qj_lb_coord he (c s) y
  have hl : |u.re| < ρ / 2 := hyN.1
  have hx : |u.im| < ρ / 2 := hyN.2
  set Pth : Set ℂ := G u.im '' uIcc u.re (ρ / 4) with hPth
  have hPpc : IsPreconnected Pth := isPreconnected_uIcc.image _ (hGc _).continuousOn
  have hPext : ∀ l ∈ uIcc u.re (ρ / 4), G u.im l ∉ closure Jd := by
    have hx2 : |u.im| < ρ := by linarith
    refine s31qj_lb_ext_seg (hGc u.im) hJ (I := Icc (-ρ) ρ) ordConnected_Icc
      (s31qj_lb_huq hfr hvu he hperp hρr hx2) (A := -ρ) (Z := u.re) (B := ρ / 4)
      ⟨le_rfl, by linarith⟩ ⟨by linarith [abs_lt.1 hl], by linarith [abs_lt.1 hl]⟩
      ⟨by linarith, by linarith⟩ (hB (hGB u.im hx)) ?_ (hT (hGT u.im hx))
    rw [hyG]; exact hyE
  have hPN : ∀ l ∈ uIcc u.re (ρ / 4), |l| < ρ / 2 := by
    intro l hl'
    rw [Set.mem_uIcc] at hl'
    have := abs_lt.1 hl
    rw [abs_lt]
    rcases hl' with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
  refine ⟨Pth ∪ Sg, ?_, Or.inr h0, Or.inl ⟨u.re, left_mem_uIcc, hyG⟩, ?_⟩
  · intro z hz
    rcases hz with ⟨l, hl', rfl⟩ | hz
    · exact ⟨hGN u.im l (hPN l hl') hx, hPext l hl'⟩
    · exact hSgE hz
  · exact hPpc.union (G u.im (ρ / 4)) ⟨ρ / 4, right_mem_uIcc, rfl⟩
      ⟨u.im, ⟨by linarith [abs_lt.1 hx], (abs_lt.1 hx).2⟩, rfl⟩ hSgpc |> fun h => h

theorem s31qj_lb_perp {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) {ζ : ℂ} {s : ℝ}
    (hmin : ∀ t, ‖ζ - c s‖ ≤ ‖ζ - c t‖) : ((ζ - c s) * conj (deriv c s)).re = 0 := by
  have hd : HasDerivAt (fun t => ζ - c t) (-deriv c s) s := by
    simpa using ((hc.differentiable (by simp)).differentiableAt (x := s)).hasDerivAt.const_sub ζ
  have hmin' : IsLocalMin (fun t => ‖ζ - c t‖ ^ 2) s :=
    Filter.Eventually.of_forall fun t => pow_le_pow_left₀ (norm_nonneg _) (hmin t) 2
  have h0 := hmin'.hasDerivAt_eq_zero hd.norm_sq
  rw [Complex.inner] at h0
  have : ((-deriv c s) * conj (ζ - c s)).re = -((ζ - c s) * conj (deriv c s)).re := by
    rw [← Complex.conj_re ((ζ - c s) * conj (deriv c s))]
    simp only [map_mul, Complex.conj_conj, neg_mul, Complex.neg_re]
    ring_nf
  linarith

/-- **Frame at the nearest point.**  For `ζ` outside `closure Jd` there is a nearest curve point `c s`, a unit
normal `e` pointing to `ζ` and, uniformly in `ζ`, tangent discs of radius `ρ ≤ ρ₀` on both sides of the curve
(the one on the `ζ` side lies outside `closure Jd`). -/
theorem s31qj_lb_frame {c : ℝ → ℂ} {Jd : Set ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) (hJ : IsOpen Jd)
    (hfr : frontier Jd = range c) :
    ∃ ρ₀ > 0, ∀ ζ : ℂ, ζ ∉ closure Jd → ∃ s : ℝ, ∃ e : ℂ, ‖e‖ = 1 ∧ (e * conj (deriv c s)).re = 0 ∧
      ζ = c s + (‖ζ - c s‖ : ℂ) * e ∧ 0 < ‖ζ - c s‖ ∧ (∀ t, ‖ζ - c s‖ ≤ ‖ζ - c t‖) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ball (c s + (ρ : ℂ) * e) ρ ⊆ (closure Jd)ᶜ ∧
        ∀ t, ρ ≤ ‖c t - (c s + ((-ρ : ℝ) : ℂ) * e)‖ := by
  obtain ⟨ρ₁, hρ₁, hext⟩ := s31qk_exterior_disc hc hc' hper hinj hJ hfr
  obtain ⟨ρ₂, hρ₂, htd⟩ := s31qk_tangent_disc hc hc' hper hinj
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun ζ hζ => ?_⟩
  obtain ⟨s, hd0, hmin, hdisc⟩ := hext ζ hζ
  set d : ℝ := ‖ζ - c s‖ with hd
  set e : ℂ := (ζ - c s) / (d : ℂ) with he
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, ← hd, div_self hd0.ne']
  have hperp0 := s31qj_lb_perp hc hmin
  have hperp : (e * conj (deriv c s)).re = 0 := by
    rw [he, div_mul_eq_mul_div, Complex.div_ofReal_re, hperp0, zero_div]
  refine ⟨s, e, hen, hperp, by rw [he, mul_div_cancel₀ _ hdC]; ring, hd0, hmin, fun ρ hρ hρm => ?_⟩
  refine ⟨(hdisc ρ hρ (hρm.trans (min_le_left _ _))).1, fun t => ?_⟩
  have := htd s (-e) (by rw [norm_neg, hen]) (by rw [neg_mul, Complex.neg_re, hperp, neg_zero]) ρ hρ
    (hρm.trans (min_le_right _ _)) t
  rw [show c s + ((-ρ : ℝ) : ℂ) * e = c s + (ρ : ℂ) * (-e) by push_cast; ring]
  exact this

section Main
variable {Jd : Set ℂ} {c : ℝ → ℂ} {r : ℝ} {κ : ℂ → ℂ}

/-- The image of the open half disc under `κ` is `V ∩ (closure Jd)ᶜ`. -/
theorem s31qj_lb_image (hJo : IsOpen Jd)
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd)) {V : Set ℂ}
    (hVeq : κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ) :
    κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im} = V ∩ (closure Jd)ᶜ := by
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  set Bc : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hBc
  have hBBc : B ⊆ Bc := fun z hz => ⟨hz.1, hz.2.le⟩
  have hclos : closure Jd = Jd ∪ frontier Jd := by
    rw [frontier, hJo.interior_eq, union_sdiff_cancel subset_closure]
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have h1 : κ z ∈ V ∩ Jdᶜ := hVeq ▸ mem_image_of_mem κ (hBBc hz)
    exact ⟨h1.1, hup hz⟩
  · rintro ζ ⟨hζV, hζc⟩
    have hζJ : ζ ∉ Jd := fun h => hζc (subset_closure h)
    obtain ⟨z, hz, rfl⟩ : ζ ∈ κ '' Bc := by rw [hVeq]; exact ⟨hζV, hζJ⟩
    rcases hz.2.lt_or_eq with h | h
    · exact ⟨z, ⟨hz.1, h⟩, rfl⟩
    · exact absurd (frontier_subset_closure (hreal ⟨hz.1, h.symm⟩)) hζc

/-- `κ` maps open subsets of the open half disc to open sets. -/
theorem s31qj_lb_open_map (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) (hr : 0 < r) {S : Set ℂ}
    (hS : S ⊆ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) (hSo : IsOpen S) : IsOpen (κ '' S) := by
  have hBo := s31qk_isOpen_upper r
  have hA : AnalyticOnNhd ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := hhol.analyticOnNhd hBo
  have hpc : IsPreconnected {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := by
    have : {z : ℂ | ‖z‖ < r ∧ 0 < z.im} = ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} := by
      ext z; simp
    rw [this]
    exact (convex_ball _ _).inter (convex_halfSpace_im_gt 0) |>.isPreconnected
  rcases hA.is_constant_or_isOpen hpc with ⟨w, hw⟩ | hopen
  · exfalso
    set a : ℂ := ((r / 2 : ℝ) : ℂ) * I with ha
    set b : ℂ := ((r / 4 : ℝ) : ℂ) * I with hb
    have hmem : ∀ t : ℝ, 0 < t → t < r → ((t : ℝ) : ℂ) * I ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} := by
      intro t ht htr
      refine ⟨?_, ?_⟩
      · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]; exact htr
      · simpa using ht
    have h1 := hw _ (hmem (r / 2) (by positivity) (by linarith))
    have h2 := hw _ (hmem (r / 4) (by positivity) (by linarith))
    have := hinj (hmem (r / 2) (by positivity) (by linarith)) (hmem (r / 4) (by positivity) (by linarith))
      (h1.trans h2.symm)
    have := congrArg Complex.im this
    simp at this
    linarith
  · exact hopen S hS hSo

/-- **Continuity of `κ⁻¹` at the segment (S6a).**  Points of the open half disc whose `κ`-image is close to `κ x₀`
are close to `x₀`. -/
theorem s31qj_lb_cl (hJo : IsOpen Jd) (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) (hfr : frontier Jd = range c)
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    {V : Set ℂ} (hVo : IsOpen V) (hVeq : κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {x₀ : ℝ} (hx₀ : |x₀| < r) :
    ∀ ε > 0, ∃ η > 0, ∀ w ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}, ‖κ w - κ x₀‖ < η → ‖w - x₀‖ < ε := by
  intro ε hε
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  set Bc : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hBc
  have hBBc : B ⊆ Bc := fun z hz => ⟨hz.1, hz.2.le⟩
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hx₀
  obtain ⟨r₁, hr₁, hvu⟩ := s31qj_lb_vert_unique hc hc' hper hinj
  obtain ⟨ρ₀, hρ₀, hframe⟩ := s31qj_lb_frame hc hc' hper hinj hJo hfr
  have hx₀B : (x₀ : ℂ) ∈ Bc := ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hp : κ x₀ ∈ frontier Jd := hreal ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hpV : κ x₀ ∈ V := (hVeq ▸ mem_image_of_mem κ hx₀B : κ x₀ ∈ V ∩ Jdᶜ).1
  obtain ⟨ρV, hρV, hρVV⟩ := Metric.isOpen_iff.1 hVo _ hpV
  have himg := s31qj_lb_image hJo hup hreal hVeq
  set ε' : ℝ := min ε ((r - |x₀|) / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by linarith)
  have hε'r : ε' ≤ (r - |x₀|) / 2 := min_le_right _ _
  -- the arc `|w - x₀| = ε'`
  set Carc : Set ℂ := sphere (x₀ : ℂ) ε' ∩ {w : ℂ | 0 ≤ w.im} with hCarc
  have hCc : IsCompact Carc :=
    (isCompact_sphere _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hnorm : ∀ w : ℂ, ‖w - x₀‖ ≤ ε' → ‖w‖ < r := by
    intro w hw
    have : ‖w‖ ≤ ‖w - x₀‖ + |x₀| := by
      calc ‖w‖ = ‖(w - x₀) + (x₀ : ℂ)‖ := by ring_nf
        _ ≤ ‖w - x₀‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
        _ = ‖w - x₀‖ + |x₀| := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hCsub : Carc ⊆ Bc := fun w hw => ⟨hnorm w (by
    have := hw.1; rw [mem_sphere, dist_eq_norm] at this; exact this.le), hw.2⟩
  have hCimg : IsCompact (κ '' Carc) := hCc.image_of_continuousOn (hcont.mono hCsub)
  have hxC : κ x₀ ∉ κ '' Carc := by
    rintro ⟨w, hw, hwe⟩
    have h1 := hκinj (hCsub hw) hx₀B hwe
    have h2 := hw.1
    rw [mem_sphere, dist_eq_norm, h1, sub_self, norm_zero] at h2
    linarith
  obtain ⟨η₀, hη₀, hη₀sub⟩ := Metric.isOpen_iff.1 hCimg.isClosed.isOpen_compl _ hxC
  -- the scale `ρ`
  set ρ : ℝ := min (min ρ₀ (r₁ / 4)) (min η₀ ρV / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₀ (by positivity)) (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρr₁ : 2 * ρ < r₁ := by
    have : ρ ≤ r₁ / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρη : 2 * ρ ≤ η₀ := by
    have : ρ ≤ min η₀ ρV / 2 := min_le_right _ _
    linarith [min_le_left η₀ ρV]
  have hρV' : 2 * ρ ≤ ρV := by
    have : ρ ≤ min η₀ ρV / 2 := min_le_right _ _
    linarith [min_le_right η₀ ρV]
  -- a point `ζ₁ = κ w₁` very close to `κ x₀`
  obtain ⟨δ, hδ, hδκ⟩ := Metric.continuousWithinAt_iff.1 (hcont (x₀ : ℂ) hx₀B) (ρ / 8) (by positivity)
  set y : ℝ := min δ ε' / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyδ : y < δ := by have := min_le_left δ ε'; linarith
  have hyε : y < ε' := by have := min_le_right δ ε'; linarith
  set w₁ : ℂ := (x₀ : ℂ) + (y : ℂ) * I with hw₁
  have hw₁x : ‖w₁ - x₀‖ = y := by
    rw [hw₁, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy0]
  have hw₁B : w₁ ∈ B := by
    refine ⟨hnorm w₁ (by rw [hw₁x]; exact hyε.le), ?_⟩
    simp [hw₁, hy0]
  have hζ₁p : ‖κ w₁ - κ x₀‖ < ρ / 8 := by
    have := hδκ (hBBc hw₁B) (by rw [dist_eq_norm, hw₁x]; exact hyδ)
    rwa [dist_eq_norm] at this
  have hζ₁ : κ w₁ ∉ closure Jd := hup hw₁B
  obtain ⟨s, e, he, hperp, hζe, hd0, hmin, hdisc⟩ := hframe (κ w₁) hζ₁
  obtain ⟨hT, hmiss⟩ := hdisc ρ hρ0 hρρ₀
  set d : ℝ := ‖κ w₁ - c s‖ with hd
  have hdp : d < ρ / 8 := by
    obtain ⟨t', ht'⟩ : κ x₀ ∈ range c := hfr ▸ hp
    have := hmin t'
    rw [← ht'] at hζ₁p
    linarith
  have hpcs : ‖κ x₀ - c s‖ < ρ / 4 := by
    calc ‖κ x₀ - c s‖ ≤ ‖κ x₀ - κ w₁‖ + ‖κ w₁ - c s‖ := by
          rw [show κ x₀ - c s = (κ x₀ - κ w₁) + (κ w₁ - c s) by ring]; exact norm_add_le _ _
      _ < ρ / 4 := by rw [norm_sub_rev]; linarith
  have hconn := s31qj_lb_box_conn hJo hfr hvu he hperp hρ0 hρr₁ hmiss hT
  set N : Set ℂ := {z : ℂ | |((z - c s) * conj e).re| < ρ / 2 ∧ |((z - c s) * conj e).im| < ρ / 2} with hN
  have hun : ∀ z : ℂ, ‖(z - c s) * conj e‖ = ‖z - c s‖ := fun z => by
    rw [norm_mul, Complex.norm_conj, he, mul_one]
  have hNball : ball (c s) (ρ / 2) ⊆ N := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    exact ⟨lt_of_le_of_lt (Complex.abs_re_le_norm _) (by rw [hun]; exact hz),
      lt_of_le_of_lt (Complex.abs_im_le_norm _) (by rw [hun]; exact hz)⟩
  have hNsub : N ⊆ ball (c s) ρ := by
    intro z hz
    rw [mem_ball, dist_eq_norm, ← hun]
    have := Complex.norm_le_abs_re_add_abs_im ((z - c s) * conj e)
    linarith [hz.1, hz.2]
  have hNp : ∀ z ∈ N, ‖z - κ x₀‖ < min η₀ ρV := by
    intro z hz
    have h1 := hNsub hz
    rw [mem_ball, dist_eq_norm] at h1
    calc ‖z - κ x₀‖ ≤ ‖z - c s‖ + ‖c s - κ x₀‖ := by
          rw [show z - κ x₀ = (z - c s) + (c s - κ x₀) by ring]; exact norm_add_le _ _
      _ < ρ + ρ / 4 := by rw [norm_sub_rev (c s)]; linarith
      _ < min η₀ ρV := by
        have := min_le_left η₀ ρV
        have := min_le_right η₀ ρV
        rcases le_total η₀ ρV with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
  -- the two pieces
  set S₁ : Set ℂ := B ∩ ball (x₀ : ℂ) ε' with hS₁
  set S₂ : Set ℂ := B ∩ (closedBall (x₀ : ℂ) ε')ᶜ with hS₂
  have hS₁o : IsOpen S₁ := (s31qk_isOpen_upper r).inter isOpen_ball
  have hS₂o : IsOpen S₂ := (s31qk_isOpen_upper r).inter isClosed_closedBall.isOpen_compl
  have hU₁ : IsOpen (κ '' S₁) := s31qj_lb_open_map hhol (hκinj.mono hBBc) hr inter_subset_left hS₁o
  have hU₂ : IsOpen (κ '' S₂) := s31qj_lb_open_map hhol (hκinj.mono hBBc) hr inter_subset_left hS₂o
  set E : Set ℂ := N ∩ (closure Jd)ᶜ with hE
  have hcover : E ⊆ κ '' S₁ ∪ κ '' S₂ := by
    intro z hz
    have hzV : z ∈ V := hρVV (by
      rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le (hNp z hz.1) (min_le_right _ _))
    have hzB : z ∈ κ '' B := by rw [himg]; exact ⟨hzV, hz.2⟩
    obtain ⟨w, hwB, rfl⟩ := hzB
    rcases lt_trichotomy ‖w - x₀‖ ε' with h | h | h
    · left; exact ⟨w, ⟨hwB, by rw [mem_ball, dist_eq_norm]; exact h⟩, rfl⟩
    · exfalso
      have hwC : w ∈ Carc := ⟨by rw [mem_sphere, dist_eq_norm]; exact h, hwB.2.le⟩
      have hzη : κ w ∈ ball (κ x₀) η₀ := by
        rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le (hNp _ hz.1) (min_le_left _ _)
      exact hη₀sub hzη ⟨w, hwC, rfl⟩
    · right; exact ⟨w, ⟨hwB, by rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]; exact h⟩, rfl⟩
  have hζ₁E : κ w₁ ∈ E := by
    refine ⟨hNball ?_, hζ₁⟩
    rw [mem_ball, dist_eq_norm]; linarith
  have hE₁ : (E ∩ κ '' S₁).Nonempty :=
    ⟨κ w₁, hζ₁E, w₁, ⟨hw₁B, by rw [mem_ball, dist_eq_norm, hw₁x]; exact hyε⟩, rfl⟩
  have hE₂ : E ∩ κ '' S₂ = ∅ := by
    by_contra hne
    obtain ⟨z, hzE, hz₁, hz₂⟩ := hconn (κ '' S₁) (κ '' S₂) hU₁ hU₂ hcover hE₁
      (Set.nonempty_iff_ne_empty.2 hne)
    obtain ⟨a, ha, rfl⟩ := hz₁
    obtain ⟨b, hb, hab⟩ := hz₂
    have := hκinj (hBBc hb.1) (hBBc ha.1) hab
    rw [this] at hb
    have h1 := ha.2
    have h2 := hb.2
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at h2
    linarith
  refine ⟨ρ / 4, by positivity, fun w hwB hwp => ?_⟩
  have hwN : κ w ∈ N := by
    refine hNball ?_
    rw [mem_ball, dist_eq_norm]
    calc ‖κ w - c s‖ ≤ ‖κ w - κ x₀‖ + ‖κ x₀ - c s‖ := by
          rw [show κ w - c s = (κ w - κ x₀) + (κ x₀ - c s) by ring]; exact norm_add_le _ _
      _ < ρ / 2 := by linarith
  have hwE : κ w ∈ E := ⟨hwN, hup hwB⟩
  rcases hcover hwE with ⟨a, ha, hae⟩ | ⟨a, ha, hae⟩
  · have := hκinj (hBBc ha.1) (hBBc hwB) hae
    rw [this] at ha
    have h1 := ha.2
    rw [mem_ball, dist_eq_norm] at h1
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  · exfalso
    have : κ w ∈ E ∩ κ '' S₂ := ⟨hwE, a, ha, hae⟩
    rw [hE₂] at this
    exact this

/-- **Barrier estimate (S6a).**  Let `φ` be holomorphic on `V ∩ (closure Jd)ᶜ` with `Im φ < r`, let `ball a ρ ⊆ Jd` and
suppose `Im φ` tends to `0` uniformly at the frontier of `Jd` in `closedBall a (2ρ) ⊆ V`.  Then
`Im φ ≤ (2r/ρ) · (ρ - ρ² Re (e/(z - a)))` on `ball a (2ρ)` outside `closure Jd` (maximum modulus principle for
`exp (-i G)` on the shrunken domain `{ε < dist(·, frontier Jd)}`). -/
theorem s31qj_lb_mp {Jd V : Set ℂ} (hJo : IsOpen Jd) {φ : ℂ → ℂ} {r ρ : ℝ} {a e : ℂ}
    (hρ : 0 < ρ) (hr : 0 < r) (he : ‖e‖ = 1)
    (hφ : DifferentiableOn ℂ φ (V ∩ (closure Jd)ᶜ))
    (hφr : ∀ z ∈ V ∩ (closure Jd)ᶜ, (φ z).im < r)
    (haJ : a ∈ Jd) (hball : ball a ρ ⊆ Jd) (hKV : closedBall a (2 * ρ) ⊆ V)
    (huc : ∀ ε' > 0, ∃ ε₀ > 0, ∀ z ∈ closedBall a (2 * ρ), z ∈ (closure Jd)ᶜ →
      Metric.infDist z (frontier Jd) < ε₀ → (φ z).im < ε') :
    ∀ ζ ∈ ball a (2 * ρ), ζ ∈ (closure Jd)ᶜ → 0 < Metric.infDist ζ (frontier Jd) →
      (φ ζ).im ≤ (2 * r / ρ) * (ρ - ρ ^ 2 * (e / (ζ - a)).re) := by
  intro ζ hζb hζe hζd
  set K : ℝ := 2 * r / ρ with hK
  have hK0 : 0 ≤ K := by positivity
  have hdist : ∀ z ∈ (closure Jd)ᶜ, ρ ≤ ‖z - a‖ := fun z hz => by
    by_contra h
    push Not at h
    exact hz (subset_closure (hball (by rw [mem_ball, dist_eq_norm]; exact h)))
  have hre : ∀ z : ℂ, (e / (z - a)).re ≤ 1 / ‖z - a‖ := fun z => by
    calc _ ≤ ‖e / (z - a)‖ := Complex.re_le_norm _
      _ = 1 / ‖z - a‖ := by rw [norm_div, he]
  have hh0 : ∀ z ∈ (closure Jd)ᶜ, 0 ≤ ρ - ρ ^ 2 * (e / (z - a)).re := by
    intro z hz
    have h1 := hdist z hz
    have h2 : ρ ^ 2 * (e / (z - a)).re ≤ ρ := by
      calc ρ ^ 2 * (e / (z - a)).re ≤ ρ ^ 2 * (1 / ‖z - a‖) :=
            mul_le_mul_of_nonneg_left (hre z) (by positivity)
        _ ≤ ρ := by
          rw [mul_one_div, div_le_iff₀ (lt_of_lt_of_le hρ h1)]
          nlinarith
    linarith
  have hh2 : ∀ z : ℂ, ‖z - a‖ = 2 * ρ → ρ / 2 ≤ ρ - ρ ^ 2 * (e / (z - a)).re := by
    intro z hz
    have h2 : ρ ^ 2 * (e / (z - a)).re ≤ ρ / 2 := by
      calc ρ ^ 2 * (e / (z - a)).re ≤ ρ ^ 2 * (1 / ‖z - a‖) :=
            mul_le_mul_of_nonneg_left (hre z) (by positivity)
        _ = ρ / 2 := by rw [hz]; field_simp
    linarith
  -- the function `G` and its imaginary part
  set G : ℂ → ℂ := fun z => φ z + (I * ((K * ρ ^ 2 : ℝ) : ℂ)) * (e / (z - a)) - I * ((K * ρ : ℝ) : ℂ)
    with hG
  have hGim : ∀ z, (G z).im = (φ z).im - K * (ρ - ρ ^ 2 * (e / (z - a)).re) := by
    intro z
    simp only [hG, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hza : ∀ z ∈ (closure Jd)ᶜ, z - a ≠ 0 := fun z hz h0 =>
    hz (subset_closure (by rw [sub_eq_zero.1 h0]; exact haJ))
  have hGd : DifferentiableOn ℂ G (V ∩ (closure Jd)ᶜ) := by
    intro z hz
    have h1 : DifferentiableWithinAt ℂ (fun z => e / (z - a)) (V ∩ (closure Jd)ᶜ) z :=
      (differentiableWithinAt_const e).div (differentiableWithinAt_id.sub_const a) (hza z hz.2)
    exact ((hφ z hz).add (h1.const_mul _)).sub_const _
  set f : ℂ → ℂ := fun z => Complex.exp (-(I * G z)) with hf
  have hfnorm : ∀ z, ‖f z‖ = Real.exp (G z).im := by
    intro z
    simp only [hf, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring_nf
  have hfd : DifferentiableOn ℂ f (V ∩ (closure Jd)ᶜ) := (hGd.const_mul I).neg.cexp
  by_contra hnot
  push Not at hnot
  set δ : ℝ := (φ ζ).im - K * (ρ - ρ ^ 2 * (e / (ζ - a)).re) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨ε₀, hε₀, hUC⟩ := huc (δ / 2) (by positivity)
  set ε : ℝ := min (ε₀ / 2) (Metric.infDist ζ (frontier Jd) / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεζ : ε < Metric.infDist ζ (frontier Jd) := by
    have := min_le_right (ε₀ / 2) (Metric.infDist ζ (frontier Jd) / 2); linarith
  have hεε₀ : ε < ε₀ := by have := min_le_left (ε₀ / 2) (Metric.infDist ζ (frontier Jd) / 2); linarith
  set W : Set ℂ := ball a (2 * ρ) ∩ ((closure Jd)ᶜ ∩ {z | ε < Metric.infDist z (frontier Jd)}) with hW
  have hWo : IsOpen W :=
    isOpen_ball.inter (isClosed_closure.isOpen_compl.inter
      (isOpen_lt continuous_const (Metric.continuous_infDist_pt _)))
  have hWb : Bornology.IsBounded W := Metric.isBounded_ball.subset inter_subset_left
  have hζW : ζ ∈ W := ⟨hζb, hζe, hεζ⟩
  have hWJ : W ⊆ Jdᶜ := fun z hz hzJ => hz.2.1 (subset_closure hzJ)
  have hcl : closure W ⊆ V ∩ (closure Jd)ᶜ := by
    intro z hz
    have h1 : z ∈ closedBall a (2 * ρ) :=
      closure_ball_subset_closedBall (closure_mono inter_subset_left hz)
    have h2 : ε ≤ Metric.infDist z (frontier Jd) := by
      have hsub : W ⊆ {z | ε ≤ Metric.infDist z (frontier Jd)} := by
        intro z hz
        show ε ≤ Metric.infDist z (frontier Jd)
        exact le_of_lt hz.2.2
      exact closure_minimal hsub (isClosed_le continuous_const (Metric.continuous_infDist_pt _)) hz
    have h3 : z ∉ Jd := closure_minimal hWJ hJo.isClosed_compl hz
    have h4 : z ∉ frontier Jd := by
      intro hzf
      rw [Metric.infDist_zero_of_mem hzf] at h2
      linarith
    refine ⟨hKV h1, ?_⟩
    rw [closure_eq_self_union_frontier]
    rintro (h | h)
    · exact h3 h
    · exact h4 h
  have hdc : DiffContOnCl ℂ f W :=
    ⟨hfd.mono (fun z hz => ⟨(hcl (subset_closure hz)).1, hz.2.1⟩),
      hfd.continuousOn.mono hcl⟩
  have hbd : ∀ z ∈ frontier W, ‖f z‖ ≤ Real.exp (δ / 2) := by
    intro z hz
    rw [hWo.frontier_eq] at hz
    obtain ⟨hzc, hzW⟩ := hz
    obtain ⟨hzV, hze⟩ := hcl hzc
    have hzball : z ∈ closedBall a (2 * ρ) :=
      closure_ball_subset_closedBall (closure_mono inter_subset_left hzc)
    rw [hfnorm]
    apply Real.exp_le_exp.2
    rw [hGim]
    have hUr := hφr z ⟨hzV, hze⟩
    have hhz := hh0 z hze
    by_cases hin : z ∈ ball a (2 * ρ)
    · -- near the frontier of `Jd`
      have hdz : Metric.infDist z (frontier Jd) ≤ ε := by
        by_contra hlt
        push Not at hlt
        exact hzW ⟨hin, hze, hlt⟩
      have := hUC z hzball hze (lt_of_le_of_lt hdz hεε₀)
      nlinarith [mul_nonneg hK0 hhz]
    · -- on the outer circle
      have hnorm : ‖z - a‖ = 2 * ρ := by
        have h1 : ‖z - a‖ ≤ 2 * ρ := by
          have := hzball; rw [mem_closedBall, dist_eq_norm] at this; exact this
        have h2 : 2 * ρ ≤ ‖z - a‖ := by
          have := hin; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
        linarith
      have := hh2 z hnorm
      have hKρ : K * (ρ / 2) = r := by rw [hK]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left this hK0]
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hWb hdc hbd (subset_closure hζW)
  rw [hfnorm, hGim] at hmax
  have := Real.exp_le_exp.1 hmax
  rw [← hδ] at this
  linarith

/-- **Uniform version of the continuity of `κ⁻¹` on compact sets inside `V`.** -/
theorem s31qj_lb_ucl (hJo : IsOpen Jd) (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0)
    (hper : ∀ t, c (t + 1) = c t) (hinj : InjOn c (Ico 0 1)) (hfr : frontier Jd = range c)
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    {V : Set ℂ} (hVo : IsOpen V) (hVeq : κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    (hne : (frontier Jd).Nonempty) {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∀ ε' > 0, ∃ ε₀ > 0, ∀ w ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}, κ w ∈ K →
      Metric.infDist (κ w) (frontier Jd) < ε₀ → w.im < ε' := by
  intro ε' hε'
  by_contra hcon
  push Not at hcon
  choose w hwB hwK hwd hwim using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨z₀, hz₀K, φ', hφ'm, hlim⟩ := hK.tendsto_subseq (x := fun n => κ (w n)) hwK
  have hlim' : Tendsto (fun n => Metric.infDist (κ (w (φ' n))) (frontier Jd)) atTop
      (𝓝 (Metric.infDist z₀ (frontier Jd))) :=
    ((Metric.continuous_infDist_pt _).tendsto z₀).comp hlim
  have hD : Metric.infDist z₀ (frontier Jd) ≤ 0 := by
    refine le_of_tendsto_of_tendsto hlim' tendsto_one_div_add_atTop_nhds_zero_nat ?_
    refine Filter.Eventually.of_forall fun n => ?_
    have h1 := hwd (φ' n)
    have h2 : (n : ℝ) ≤ (φ' n : ℝ) := by exact_mod_cast hφ'm.id_le n
    have h3 : 1 / ((φ' n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact (h1.trans_le h3).le
  have hz₀F : z₀ ∈ frontier Jd :=
    (isClosed_frontier.mem_iff_infDist_zero hne).2 (le_antisymm hD Metric.infDist_nonneg)
  have hz₀V : z₀ ∈ V := hKV hz₀K
  have hz₀J : z₀ ∉ Jd := fun h => s31qj_lb_not_mem_frontier hJo h hz₀F
  obtain ⟨x, hxBc, hx⟩ : z₀ ∈ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := by
    rw [hVeq]; exact ⟨hz₀V, hz₀J⟩
  have hx0 : x.im = 0 := by
    by_contra hx0
    have hpos : 0 < x.im := lt_of_le_of_ne hxBc.2 (Ne.symm hx0)
    exact hup ⟨hxBc.1, hpos⟩ (hx ▸ frontier_subset_closure hz₀F)
  have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hx0])
  have hx₀ : |x.re| < r := lt_of_le_of_lt (Complex.abs_re_le_norm x) hxBc.1
  obtain ⟨η, hη, hcl⟩ := s31qj_lb_cl hJo hc hc' hper hinj hfr hhol hcont hκinj hup hreal hVo hVeq hx₀ ε' hε'
  have hev : ∀ᶠ n in atTop, ‖κ (w (φ' n)) - κ (x.re : ℂ)‖ < η := by
    have := (Metric.tendsto_nhds.1 hlim) η hη
    filter_upwards [this] with n hn
    rw [dist_eq_norm] at hn
    rw [← hxr, hx]
    exact hn
  obtain ⟨n, hn⟩ := hev.exists
  have h1 := hcl (w (φ' n)) (hwB (φ' n)) hn
  have h2 : (w (φ' n)).im ≤ ‖w (φ' n) - (x.re : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w (φ' n) - (x.re : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have := hwim (φ' n)
  linarith

/-- **Koebe step (lower bound).**  If `ball (κ w) R ⊆ κ '' B⁺` then `R / (4 Im w) ≤ |κ'(w)|`
(one-quarter theorem for the inverse `κ⁻¹`, whose image avoids the real axis). -/
theorem s31qj_lb_koebe (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) {w : ℂ} (hw : w ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    {R : ℝ} (hR : 0 < R) (hball : ball (κ w) R ⊆ κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) :
    R / (4 * w.im) ≤ ‖deriv κ w‖ := by
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  have hBo : IsOpen B := s31qk_isOpen_upper r
  have hconf : IsConformalOnto κ B (κ '' B) := ⟨hhol, hinj, rfl⟩
  have hsymm := hconf.symm hBo
  set φ : ℂ → ℂ := Function.invFunOn κ B with hφ
  have hleft : ∀ z ∈ B, φ (κ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hφd : DifferentiableOn ℂ φ (κ '' B) := hsymm.1
  have hφinj : InjOn φ (κ '' B) := hsymm.2.1
  have hφB : ∀ y ∈ κ '' B, φ y ∈ B := by
    intro y hy
    have h := mem_image_of_mem φ hy
    rwa [hsymm.2.2] at h
  have hwim : 0 < w.im := hw.2
  -- the rescaled inverse
  set ψ : ℂ → ℂ := fun u => φ (κ w + (R : ℂ) * u) - w with hψ
  have hmem : ∀ u ∈ ball (0 : ℂ) 1, κ w + (R : ℂ) * u ∈ ball (κ w) R := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    exact mul_lt_of_lt_one_right hR hu
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := by
    intro u hu
    have h1 : DifferentiableAt ℂ φ (κ w + (R : ℂ) * u) :=
      (hφd.mono hball).differentiableAt (isOpen_ball.mem_nhds (hmem u hu))
    exact ((h1.comp u ((differentiableAt_const _).add ((differentiableAt_const _).mul
      differentiableAt_id))).sub (differentiableAt_const _)).differentiableWithinAt
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hψinj : InjOn ψ (ball 0 1) := by
    intro u hu v hv huv
    have h1 := hφinj (hball (hmem u hu)) (hball (hmem v hv)) (sub_left_inj.1 huv)
    exact mul_left_cancel₀ hRC (add_left_cancel h1)
  have hψ0 : ψ 0 = 0 := by simp [hψ, hleft w hw]
  have hq : ((w.re : ℝ) : ℂ) - w ∉ ψ '' ball 0 1 := by
    rintro ⟨u, hu, hψu⟩
    have h1 : φ (κ w + (R : ℂ) * u) = ((w.re : ℝ) : ℂ) := by
      have := congrArg (· + w) hψu
      simpa [hψ] using this
    have h2 := hφB _ (hball (hmem u hu))
    rw [h1] at h2
    simpa using h2.2
  have hk := koebe_quarter_of_not_mem hψd hψinj hψ0 hq
  have hqn : ‖((w.re : ℝ) : ℂ) - w‖ = w.im := by
    have : ((w.re : ℝ) : ℂ) - w = -((w.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [this, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hwim]
  -- derivatives
  have hκd : DifferentiableAt ℂ κ w := hhol.differentiableAt (hBo.mem_nhds hw)
  have hφdz : DifferentiableAt ℂ φ (κ w) :=
    (hφd.mono hball).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hev : (φ ∘ κ) =ᶠ[𝓝 w] id := by
    filter_upwards [hBo.mem_nhds hw] with z hz
    exact hleft z hz
  have hchain : deriv φ (κ w) * deriv κ w = 1 := by
    have h1 : HasDerivAt (φ ∘ κ) (deriv φ (κ w) * deriv κ w) w := hφdz.hasDerivAt.comp w hκd.hasDerivAt
    have h2 : HasDerivAt (φ ∘ κ) 1 w := (hasDerivAt_id w).congr_of_eventuallyEq hev
    exact h1.unique h2
  have hder : deriv ψ 0 = deriv φ (κ w) * (R : ℂ) := by
    have h1 : HasDerivAt (fun u : ℂ => κ w + (R : ℂ) * u) (R : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)).const_add (κ w)
    have h2 : HasDerivAt φ (deriv φ (κ w)) (κ w + (R : ℂ) * 0) := by
      rw [mul_zero, add_zero]; exact hφdz.hasDerivAt
    exact ((h2.comp 0 h1).sub_const w).deriv
  rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hqn] at hk
  have hn1 : ‖deriv φ (κ w)‖ * ‖deriv κ w‖ = 1 := by rw [← norm_mul, hchain, norm_one]
  rw [div_le_iff₀ (by positivity)]
  have : R = R * (‖deriv φ (κ w)‖ * ‖deriv κ w‖) := by rw [hn1, mul_one]
  have hκn : 0 ≤ ‖deriv κ w‖ := norm_nonneg _
  calc R = R * (‖deriv φ (κ w)‖ * ‖deriv κ w‖) := this
    _ = (‖deriv φ (κ w)‖ * R) * ‖deriv κ w‖ := by ring
    _ ≤ (4 * w.im) * ‖deriv κ w‖ := mul_le_mul_of_nonneg_right hk hκn
    _ = ‖deriv κ w‖ * (4 * w.im) := by ring

end Main

/-- **Lower bound for `|κ'|` near the segment** (the converse of `s31qk_deriv_bounded`; S6a, `s31qd_boundary_jet`).
Under the hypotheses of `s31qi_reflect_across_arc` (without `Qc`), at each point `t` of the segment `|κ'|` is bounded
below by a positive constant on the upper half disc near `t`.  Intended route: a barrier at the interior tangent disc
(it lies in `Jd`, by a local side argument for the `C²` curve) bounds `Im ∘ κ⁻¹ ≤ C · dist(·, curve)` near `κ t`, then
Koebe's one-quarter theorem for `κ⁻¹` on `B(κ w, dist(κ w, curve))` gives `|κ'(w)| ≥ dist(κ w, curve) / (4 Im w)`. -/
theorem s31qj_deriv_lower
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {t : ℝ} (ht : |t| < r) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ w : ℂ, ‖w - t‖ < δ → ‖w‖ < r → 0 < w.im → m ≤ ‖deriv κ w‖ := by
  have hJo : IsOpen Jd := hJd.1
  have hfr : frontier Jd = range c := by rw [s31qk_range_eq hper, hcf]
  obtain ⟨V, hVo, hVeq⟩ := hlocal
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  set Bc : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hBc
  have hBBc : B ⊆ Bc := fun z hz => ⟨hz.1, hz.2.le⟩
  have himg := s31qj_lb_image hJo hup hreal hVeq
  have htBc : (t : ℂ) ∈ Bc := ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hp₀F : κ t ∈ frontier Jd := hreal ⟨by rwa [Complex.norm_real, Real.norm_eq_abs], by simp⟩
  have hp₀V : κ t ∈ V := (hVeq ▸ mem_image_of_mem κ htBc : κ t ∈ V ∩ Jdᶜ).1
  obtain ⟨ρV, hρV, hρVV⟩ := Metric.isOpen_iff.1 hVo _ hp₀V
  obtain ⟨r₁, hr₁, hvu⟩ := s31qj_lb_vert_unique hc hc' hper hinj
  obtain ⟨ρ₀, hρ₀, hframe⟩ := s31qj_lb_frame hc hc' hper hinj hJo hfr
  have hne : (frontier Jd).Nonempty := ⟨κ t, hp₀F⟩
  set ρ : ℝ := min (min ρ₀ (r₁ / 4)) (ρV / 8) with hρdef
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₀ (by positivity)) (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρr₁ : 2 * ρ < r₁ := by
    have : ρ ≤ r₁ / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρV8 : 8 * ρ ≤ ρV := by
    have : ρ ≤ ρV / 8 := min_le_right _ _
    linarith
  obtain ⟨δ, hδ, hδκ⟩ := Metric.continuousWithinAt_iff.1 (hcont (t : ℂ) htBc) (ρ / 4) (by positivity)
  refine ⟨ρ / (8 * r), δ, by positivity, hδ, fun w hwt hwr hwi => ?_⟩
  have hwB : w ∈ B := ⟨hwr, hwi⟩
  have hζp : ‖κ w - κ t‖ < ρ / 4 := by
    have := hδκ (hBBc hwB) (by rwa [dist_eq_norm])
    rwa [dist_eq_norm] at this
  have hζ : κ w ∉ closure Jd := hup hwB
  obtain ⟨s, e, he, hperp, hζe, hd0, hmin, hdisc⟩ := hframe (κ w) hζ
  set d : ℝ := ‖κ w - c s‖ with hd
  have hdp : d < ρ / 4 := by
    obtain ⟨t', ht'⟩ : κ t ∈ range c := hfr ▸ hp₀F
    have := hmin t'
    rw [← ht'] at hζp
    linarith
  have hdρ : d < ρ := by linarith
  obtain ⟨hT, hmiss⟩ := hdisc ρ hρ0 hρρ₀
  obtain ⟨hTd, -⟩ := hdisc d hd0 (by linarith)
  set a : ℂ := c s + ((-ρ : ℝ) : ℂ) * e with ha
  have hball : ball a ρ ⊆ Jd := s31qj_lb_side hJo hfr hvu he hperp hρ0 hρr₁ hmiss hT
  have haJ : a ∈ Jd := hball (mem_ball_self hρ0)
  have hcsp : ‖c s - κ t‖ < ρ / 2 := by
    calc ‖c s - κ t‖ ≤ ‖c s - κ w‖ + ‖κ w - κ t‖ := by
          rw [show c s - κ t = (c s - κ w) + (κ w - κ t) by ring]; exact norm_add_le _ _
      _ < ρ / 2 := by rw [norm_sub_rev]; linarith
  have hacs : ‖a - c s‖ = ρ := by
    rw [ha, add_sub_cancel_left, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hρ0]
  have hKV : closedBall a (2 * ρ) ⊆ V := by
    intro z hz
    apply hρVV
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - κ t‖ ≤ ‖z - a‖ + ‖a - c s‖ + ‖c s - κ t‖ := by
          rw [show z - κ t = (z - a) + (a - c s) + (c s - κ t) by ring]
          have h1 := norm_add_le (z - a) (a - c s)
          have h2 := norm_add_le (z - a + (a - c s)) (c s - κ t)
          linarith
      _ < ρV := by linarith
  have hucl := s31qj_lb_ucl hJo hc hc' hper hinj hfr hhol hcont hκinj hup hreal hVo hVeq hne
    (isCompact_closedBall a (2 * ρ)) hKV
  -- the inverse `φ = κ⁻¹`
  set φ : ℂ → ℂ := Function.invFunOn κ B with hφ
  have hconf : IsConformalOnto κ B (κ '' B) := ⟨hhol, hκinj.mono hBBc, rfl⟩
  have hsymm := hconf.symm (s31qk_isOpen_upper r)
  have hφd : DifferentiableOn ℂ φ (V ∩ (closure Jd)ᶜ) := by rw [← himg]; exact hsymm.1
  have hφB : ∀ y ∈ V ∩ (closure Jd)ᶜ, φ y ∈ B := by
    intro y hy
    rw [← himg] at hy
    have h := mem_image_of_mem φ hy
    rwa [hsymm.2.2] at h
  have hφr : ∀ z ∈ V ∩ (closure Jd)ᶜ, (φ z).im < r := fun z hz =>
    lt_of_le_of_lt ((le_abs_self _).trans (Complex.abs_im_le_norm _)) (hφB z hz).1
  have hκφ : ∀ y ∈ V ∩ (closure Jd)ᶜ, κ (φ y) = y := by
    intro y hy
    rw [← himg] at hy
    exact Function.invFunOn_eq (by obtain ⟨z, hz, rfl⟩ := hy; exact ⟨z, hz, rfl⟩)
  have huc : ∀ ε' > 0, ∃ ε₀ > 0, ∀ z ∈ closedBall a (2 * ρ), z ∈ (closure Jd)ᶜ →
      Metric.infDist z (frontier Jd) < ε₀ → (φ z).im < ε' := by
    intro ε' hε'
    obtain ⟨ε₀, hε₀, h⟩ := hucl ε' hε'
    refine ⟨ε₀, hε₀, fun z hz hze hzd => ?_⟩
    have hzO : z ∈ V ∩ (closure Jd)ᶜ := ⟨hKV hz, hze⟩
    exact h (φ z) (hφB z hzO) (by rw [hκφ z hzO]; exact hz) (by rw [hκφ z hzO]; exact hzd)
  -- the barrier at `ζ = κ w`
  have hζa : κ w - a = ((d + ρ : ℝ) : ℂ) * e := by
    rw [ha]
    conv_lhs => rw [hζe]
    push_cast
    ring
  have hζball : κ w ∈ ball a (2 * ρ) := by
    rw [mem_ball, dist_eq_norm, hζa, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hζnf : κ w ∉ frontier Jd := fun h => hζ (frontier_subset_closure h)
  have hζpos : 0 < Metric.infDist (κ w) (frontier Jd) :=
    (isClosed_frontier.notMem_iff_infDist_pos hne).1 hζnf
  have hmp := s31qj_lb_mp hJo (φ := φ) hρ0 hr he hφd hφr haJ hball hKV huc (κ w) hζball hζ hζpos
  have hφw : φ (κ w) = w := (hκinj.mono hBBc).leftInvOn_invFunOn hwB
  rw [hφw] at hmp
  have hre : (e / (κ w - a)).re = 1 / (d + ρ) := by
    have he0 : e ≠ 0 := norm_pos_iff.1 (by rw [he]; exact one_pos)
    have hdρ0 : (((d + ρ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have : e / (κ w - a) = ((1 / (d + ρ) : ℝ) : ℂ) := by
      rw [hζa]
      push_cast
      field_simp
    rw [this, Complex.ofReal_re]
  rw [hre] at hmp
  have hbar : ρ - ρ ^ 2 * (1 / (d + ρ)) ≤ d := by
    have hdr : 0 < d + ρ := by linarith
    have : ρ - d ≤ ρ ^ 2 * (1 / (d + ρ)) := by
      rw [mul_one_div, le_div_iff₀ hdr]
      nlinarith [sq_nonneg d]
    linarith
  have hwim : w.im ≤ (2 * r / ρ) * d := by
    refine hmp.trans ?_
    exact mul_le_mul_of_nonneg_left hbar (by positivity)
  -- Koebe
  have hballκ : ball (κ w) d ⊆ κ '' B := by
    intro z hz
    rw [himg]
    have hz' : z ∈ ball (c s + (d : ℂ) * e) d := by rw [← hζe]; exact hz
    refine ⟨hρVV ?_, hTd hz'⟩
    rw [mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - κ t‖ ≤ ‖z - κ w‖ + ‖κ w - κ t‖ := by
          rw [show z - κ t = (z - κ w) + (κ w - κ t) by ring]; exact norm_add_le _ _
      _ < ρV := by linarith
  have hk := s31qj_lb_koebe hhol (hκinj.mono hBBc) hwB hd0 hballκ
  have hwim' : w.im * ρ ≤ 2 * r * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ0] at hwim
    exact hwim
  refine le_trans ?_ hk
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end LiZhongQC
