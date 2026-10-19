import LiZhongQC.Ch11.S35_DiscTeichmullerMaps

/-!
# §36 Hamilton 定理 — Hamilton's theorem

* §36.1 a Riemann surface `S = ℍ/G` as the interior of the bordered surface
  `S* = (ℍ ∪ b(G))/G`, `b(G) = ℝ̂ ∖ Λ(G)`; quasiconformal maps homotopic modulo the boundary
  (模边界同伦); Theorem 36.1 (⟺ lifts with equal boundary values); the Teichmüller extremal problem
  in a class modulo the boundary and the existence of extremal maps
                                      — `ordinarySet`, `HomotopicModBoundary`, `thm36_1`,
                                        `IsExtremalModBoundary`, `exists_extremal_mod_boundary`
* §36.2 the integrable holomorphic quadratic differentials `A(S)`; Theorem 36.2 (Hamilton:
  `sup_{‖ω‖=1} |∫_S κω| = ‖κ‖_∞` for an extremal `κ`); the finite type case recovers
  Teichmüller's theorem; Corollary 36.1 (`‖κ|_{S∖K}‖_∞ = ‖κ‖_∞`)
                                      — `integrableAutomorphicQD`, `thm36_2_hamilton`,
                                        `thm36_2_finite_type`, `cor36_1`
* §36.3 the proof: Lemma 36.1 (norm-extremal points of a submanifold of a dual space); Lemma 36.2
  (the trivial Beltrami differentials `N` form an analytic submanifold of `M(S)` with
  `T₀N ⊥ A(S)`: the Bers map `Φ`, its derivative `DΦ(0) = P`, `F ∘ P = id`, `N = Φ⁻¹(0)`);
  trivial and locally trivial differentials; `τ(ν, π)`; Lemma 36.3; Strebel's converse
                                      — `lemma36_1`, `bersDerivative`, `lemma36_2_*`,
                                        `IsTrivialBeltrami`, `IsLocallyTrivialBeltrami`,
                                        `beltramiPoincareDist`, `lemma36_3`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## §36.1 Quasiconformal maps homotopic modulo the boundary -/

/-- §36.1: the limit set of a Fuchsian group `G` (as a subgroup of `SL(2, ℂ)`), a closed subset of
`ℝ̂`. -/
def fuchsianLimitSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ExtPlane :=
  limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))

/-- §36.1: the set of ordinary boundary points `b(G) = ℝ̂ ∖ Λ(G)`; `S* = (ℍ ∪ b(G))/G` is a bordered
Riemann surface with interior `S = ℍ/G`. -/
def ordinarySet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ExtPlane :=
  extRealLine \ fuchsianLimitSet Γ

/-- §36.1: `H̃` is a lift of the homotopy `H : S × [0, 1] → S₁`. -/
def IsLiftHomotopy {S S₁ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] (p : UpperHalfPlane → S)
    (p₁ : UpperHalfPlane → S₁) (H : C(S × unitInterval, S₁)) (Ht : UpperHalfPlane → unitInterval → UpperHalfPlane) :
    Prop :=
  Continuous (fun x : UpperHalfPlane × unitInterval => Ht x.1 x.2) ∧ ∀ τ t, p₁ (Ht τ t) = H (p τ, t)

/-- **§36.1 (模边界同伦).**  Two quasiconformal maps `f₀, f₁ : S → S₁` are homotopic modulo the
boundary if `f₀ = f₁` on `S* ∖ S` and there is a homotopy `F : S* × [0, 1] → S₁*` from `f₀` to `f₁`
with `F(p, t) = f₀(p)` for all `p ∈ S* ∖ S`.  (Expressed through lifts: a homotopy `H` between
`f₀` and `f₁` whose lift `H̃` extends continuously to the closed half-plane, constantly in `t` on
`ℝ̂`.) -/
def HomotopicModBoundary {S S₁ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] (p : UpperHalfPlane → S)
    (p₁ : UpperHalfPlane → S₁) (f₀ f₁ : S → S₁) : Prop :=
  ∃ (H : C(S × unitInterval, S₁)) (Ht : UpperHalfPlane → unitInterval → UpperHalfPlane)
    (G : ExtPlane → unitInterval → ExtPlane),
    (∀ x, H (x, 0) = f₀ x) ∧ (∀ x, H (x, 1) = f₁ x) ∧ IsLiftHomotopy p p₁ H Ht ∧
    Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2) ∧
    (∀ (τ : UpperHalfPlane) (t : unitInterval), G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane)) ∧
    ∀ x ∈ extRealLine, ∀ t, G x t = G x 0

/-! ### s36h Stage 0 (coordinator 553e2d): the `⇐` direction of Theorem 36.1 (`h36t_`) -/

/-- `tanh` is monotone. -/
theorem h36t_tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  have hx := Real.cosh_pos x
  have hy := Real.cosh_pos y
  have key : Real.tanh y - Real.tanh x = Real.sinh (y - x) / (Real.cosh x * Real.cosh y) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
    field_simp
  have h1 : 0 ≤ Real.sinh (y - x) := Real.sinh_nonneg_iff.2 (by linarith)
  have h2 : 0 ≤ Real.tanh y - Real.tanh x := by rw [key]; positivity
  linarith

/-- The geodesic disc point is `s · u` with `s ∈ [0, 1]`, where `u` is the disc coordinate of the
endpoint. -/
theorem h36t_B_eq_smul (p q : UpperHalfPlane) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ c36_d_B p q t = (s : ℂ) * c36_d_disc p q := by
  have hD0 : 0 ≤ dist p q / 2 := by positivity
  rcases hD0.eq_or_lt with h0 | hpos
  · refine ⟨0, le_refl _, zero_le_one, ?_⟩
    have hu : c36_d_disc p q = 0 := by
      rw [← norm_eq_zero, c36_d_norm_disc, ← h0, Real.tanh_zero]
    rw [c36_d_B, hu, mul_zero, mul_zero]
  · have hT : 0 < Real.tanh (dist p q / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2 hpos) (Real.cosh_pos _)
    have hlam := c36_d_lam_mul_tanh (dist p q / 2) t
    refine ⟨c36_d_lam (dist p q / 2) t, ?_, ?_, rfl⟩
    · have h1 := c36_d_tanh_nonneg (mul_nonneg ht0 hD0)
      rw [← hlam] at h1
      nlinarith
    · have h1 := h36t_tanh_le_tanh (show t * (dist p q / 2) ≤ dist p q / 2 by nlinarith)
      rw [← hlam] at h1
      nlinarith

/-- The quadratic identity behind the Euclidean convexity of half-discs: with
`Q(v) = R |1 - v|² - |α - ᾱ v|²`, one has `Q(s u) = s Q(u) + Q(0) (1 - s)(1 - s |u|²)`. -/
theorem h36t_Q_identity (α u : ℂ) (s R : ℝ) :
    R * Complex.normSq (1 - (s : ℂ) * u) - Complex.normSq (α - conj α * ((s : ℂ) * u)) =
      s * (R * Complex.normSq (1 - u) - Complex.normSq (α - conj α * u)) +
        (R - Complex.normSq α) * (1 - s) * (1 - s * Complex.normSq u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `inv_p(v) - c = ((p - c) - conj (p - c) v) / (1 - v)` for a real centre `c`. -/
theorem h36t_inv_sub_real (p : UpperHalfPlane) (c : ℝ) {v : ℂ} (hv : 1 - v ≠ 0) :
    c36_d_inv p v - c = (((p : ℂ) - c) - conj ((p : ℂ) - c) * v) / (1 - v) := by
  unfold c36_d_inv
  rw [map_sub, Complex.conj_ofReal]
  field_simp
  ring

/-- The key identity for the geodesic segment against a real centre `c` and a level `R`:
`(R - |γ(t) - c|²) |1 - s u|² = s (R - |b - c|²) |1 - u|² + (R - |a - c|²)(1 - s)(1 - s |u|²)`. -/
theorem h36t_geod_key (a b : UpperHalfPlane) (c R : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ ∃ u : ℂ, Complex.normSq u < 1 ∧ 0 < Complex.normSq (1 - (s : ℂ) * u) ∧
      (R - Complex.normSq ((c36_d_geod a b t : ℂ) - c)) * Complex.normSq (1 - (s : ℂ) * u) =
        s * ((R - Complex.normSq ((b : ℂ) - c)) * Complex.normSq (1 - u)) +
          (R - Complex.normSq ((a : ℂ) - c)) * (1 - s) * (1 - s * Complex.normSq u) := by
  obtain ⟨s, hs0, hs1, hB⟩ := h36t_B_eq_smul a b ht0 ht1
  set u := c36_d_disc a b with hu
  have hu1 : ‖u‖ < 1 := c36_d_norm_disc_lt_one a b
  have hv1 : ‖(s : ℂ) * u‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    nlinarith [norm_nonneg u]
  have h1u := c36_d_one_sub_ne hu1
  have h1v := c36_d_one_sub_ne hv1
  have hNu : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.2 h1u
  have hNv : 0 < Complex.normSq (1 - (s : ℂ) * u) := Complex.normSq_pos.2 h1v
  have hnu : Complex.normSq u < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
  refine ⟨s, hs0, hs1, u, hnu, hNv, ?_⟩
  have hg : ((c36_d_geod a b t : UpperHalfPlane) : ℂ) = c36_d_inv a ((s : ℂ) * u) := by
    show c36_d_inv a (c36_d_B a b t) = _
    rw [hB]
  have hb : ((b : UpperHalfPlane) : ℂ) = c36_d_inv a u := (c36_d_inv_disc a b).symm
  have eg : Complex.normSq ((c36_d_geod a b t : ℂ) - c) * Complex.normSq (1 - (s : ℂ) * u) =
      Complex.normSq (((a : ℂ) - c) - conj ((a : ℂ) - c) * ((s : ℂ) * u)) := by
    rw [hg, h36t_inv_sub_real a c h1v, Complex.normSq_div]
    field_simp
  have eb : Complex.normSq ((b : ℂ) - c) * Complex.normSq (1 - u) =
      Complex.normSq (((a : ℂ) - c) - conj ((a : ℂ) - c) * u) := by
    rw [hb, h36t_inv_sub_real a c h1u, Complex.normSq_div]
    field_simp
  have hid := h36t_Q_identity ((a : ℂ) - c) u s R
  rw [sub_mul, eg, hid, ← eb]
  ring

/-- Euclidean shrinking towards a finite real point: if `a, b ∈ ℍ` lie within `ε` of the real
point `c`, so does every point of the geodesic segment between them. -/
theorem h36t_geod_dist_lt (a b : UpperHalfPlane) (c : ℝ) {ε : ℝ} (ha : dist (a : ℂ) c < ε)
    (hb : dist (b : ℂ) c < ε) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (c36_d_geod a b t : ℂ) c < ε := by
  set M := max (dist (a : ℂ) c) (dist (b : ℂ) c) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left dist_nonneg
  have hMε : M < ε := max_lt ha hb
  obtain ⟨s, hs0, hs1, u, hnu, hNv, hkey⟩ := h36t_geod_key a b c (M ^ 2) ht0 ht1
  have hsq : ∀ z : ℂ, dist z c ≤ M → Complex.normSq (z - c) ≤ M ^ 2 := by
    intro z hz
    rw [Complex.normSq_eq_norm_sq, ← Complex.dist_eq]
    exact pow_le_pow_left₀ dist_nonneg hz 2
  have hA := hsq _ (le_max_left _ _)
  have hB := hsq _ (le_max_right _ _)
  have hNu : 0 ≤ Complex.normSq (1 - u) := Complex.normSq_nonneg _
  have hR : 0 ≤ s * ((M ^ 2 - Complex.normSq ((b : ℂ) - c)) * Complex.normSq (1 - u)) +
      (M ^ 2 - Complex.normSq ((a : ℂ) - c)) * (1 - s) * (1 - s * Complex.normSq u) := by
    have h1 : 0 ≤ 1 - s * Complex.normSq u := by nlinarith [Complex.normSq_nonneg u]
    have h2 : 0 ≤ (M ^ 2 - Complex.normSq ((b : ℂ) - c)) * Complex.normSq (1 - u) :=
      mul_nonneg (by linarith) hNu
    have h3 : 0 ≤ (M ^ 2 - Complex.normSq ((a : ℂ) - c)) * (1 - s) := mul_nonneg (by linarith) (by linarith)
    exact add_nonneg (mul_nonneg hs0 h2) (mul_nonneg h3 h1)
  rw [← hkey] at hR
  have hle : Complex.normSq ((c36_d_geod a b t : ℂ) - c) ≤ M ^ 2 := by
    have := nonneg_of_mul_nonneg_left hR hNv
    linarith
  rw [Complex.normSq_eq_norm_sq, ← Complex.dist_eq] at hle
  have := abs_le_of_sq_le_sq' hle hM0
  linarith [this.2]

/-- Euclidean shrinking towards `∞`: if `a, b ∈ ℍ` lie outside the closed disc of radius `R` about
`0`, so does every point of the geodesic segment between them. -/
theorem h36t_geod_norm_gt (a b : UpperHalfPlane) {R : ℝ} (ha : R < ‖(a : ℂ)‖) (hb : R < ‖(b : ℂ)‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : R < ‖(c36_d_geod a b t : ℂ)‖ := by
  rcases lt_or_ge R 0 with hR0 | hR0
  · exact lt_of_lt_of_le hR0 (norm_nonneg _)
  set m := min ‖(a : ℂ)‖ ‖(b : ℂ)‖ with hm
  have hRm : R < m := lt_min ha hb
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨s, hs0, hs1, u, hnu, hNv, hkey⟩ := h36t_geod_key a b 0 (m ^ 2) ht0 ht1
  simp only [Complex.ofReal_zero, sub_zero] at hkey
  have hsq : ∀ z : ℂ, m ≤ ‖z‖ → m ^ 2 ≤ Complex.normSq z := by
    intro z hz
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ hm0 hz 2
  have hA := hsq _ (min_le_left _ _)
  have hB := hsq _ (min_le_right _ _)
  have hNu : 0 ≤ Complex.normSq (1 - u) := Complex.normSq_nonneg _
  have hR : s * ((m ^ 2 - Complex.normSq (b : ℂ)) * Complex.normSq (1 - u)) +
      (m ^ 2 - Complex.normSq (a : ℂ)) * (1 - s) * (1 - s * Complex.normSq u) ≤ 0 := by
    have h1 : 0 ≤ 1 - s * Complex.normSq u := by nlinarith [Complex.normSq_nonneg u]
    have h2 : (m ^ 2 - Complex.normSq (b : ℂ)) * Complex.normSq (1 - u) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hNu
    have h3 : (m ^ 2 - Complex.normSq (a : ℂ)) * (1 - s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h4 : s * ((m ^ 2 - Complex.normSq (b : ℂ)) * Complex.normSq (1 - u)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 h2
    have h5 : (m ^ 2 - Complex.normSq (a : ℂ)) * (1 - s) * (1 - s * Complex.normSq u) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h3 h1
    linarith
  rw [← hkey] at hR
  have hge : m ^ 2 ≤ Complex.normSq (c36_d_geod a b t : ℂ) := by
    by_contra hcon
    push Not at hcon
    have : 0 < (m ^ 2 - Complex.normSq (c36_d_geod a b t : ℂ)) * Complex.normSq (1 - (s : ℂ) * u) :=
      mul_pos (by linarith) hNv
    linarith
  rw [Complex.normSq_eq_norm_sq] at hge
  have := abs_le_of_sq_le_sq' hge (norm_nonneg _)
  nlinarith [norm_nonneg (c36_d_geod a b t : ℂ), sq_nonneg (‖(c36_d_geod a b t : ℂ)‖ - m)]

/-- Deck correspondence: a lift `F` of `f` conjugates each `γ ∈ Γ` to some `δ ∈ Γ₁`,
`F ∘ γ = δ ∘ F` (uniqueness of lifts through the covering `p₁`). -/
theorem h36t_deck {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    {p₁ : UpperHalfPlane → S₁} (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) {f : S → S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p p₁ f F) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) : ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ := by
  have hpγ : ∀ τ, p (γ • τ) = p τ := fun τ => ((hp.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm
  have h0 : p₁ (F UpperHalfPlane.I) = p₁ (F (γ • UpperHalfPlane.I)) := by rw [hF, hF, hpγ]
  obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 h0
  refine ⟨δ, hδ, fun τ => ?_⟩
  have hcomp : p₁ ∘ (fun τ => F (γ • τ)) = p₁ ∘ (fun τ => δ • F τ) := by
    funext τ
    simp only [Function.comp_apply]
    rw [hF, hpγ, ← hF]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  have h := hp₁.1.eq_of_comp_eq (F.continuous.comp (continuous_const_smul γ))
    ((continuous_const_smul δ).comp F.continuous) hcomp UpperHalfPlane.I hδe.symm
  exact congrFun h τ

/-- The geodesic homotopy between the lifts descends: its projection by `p₁` only depends on
`p τ`. -/
theorem h36t_wd {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    {p₁ : UpperHalfPlane → S₁} (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) {f₀ f₁ : S → S₁}
    {F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₀ G₁ : ExtPlane → ExtPlane} (hF₀ : IsLift p p₁ f₀ F₀)
    (hF₁ : IsLift p p₁ f₁ F₁) (hG₀ : IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀)
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁) (hbd : ∀ x ∈ extRealLine, G₀ x = G₁ x)
    {τ τ' : UpperHalfPlane} (h : p τ = p τ') (t : ℝ) :
    p₁ (c36_d_geod (F₀ τ) (F₁ τ) t) = p₁ (c36_d_geod (F₀ τ') (F₁ τ') t) := by
  obtain ⟨γ, hγ, rfl⟩ := (hp.2.2.2 τ τ').1 h
  obtain ⟨δ₀, hδ₀, h₀⟩ := h36t_deck hp hp₁ hF₀ hγ
  obtain ⟨δ₁, -, h₁⟩ := h36t_deck hp hp₁ hF₁ hγ
  rw [h₀, h₁, ← h36t_deck_agree hG₀ hG₁ hbd h₀ h₁, h36t_geod_smul]
  exact (hp₁.2.2.2 _ _).2 ⟨δ₀, hδ₀, rfl⟩

/-- The fold `x + i y ↦ x + i |y|` of `ℂ` onto the closed upper half-plane. -/
def h36t_foldC (w : ℂ) : ℂ := (w.re : ℂ) + ((|w.im| : ℝ) : ℂ) * Complex.I

/-- The fold of `ℂ` is continuous. -/
theorem h36t_foldC_continuous : Continuous h36t_foldC := by
  unfold h36t_foldC
  fun_prop

/-- The fold of `ℂ` preserves norms. -/
theorem h36t_norm_foldC (w : ℂ) : ‖h36t_foldC w‖ = ‖w‖ := by
  have h : ‖h36t_foldC w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [h36t_foldC, Complex.normSq_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The fold `x + i y ↦ x + i |y|` of `ℂ̄` onto the closed upper half-plane (fixing `∞`). -/
def h36t_fold : ExtPlane → ExtPlane := OnePoint.map h36t_foldC

/-- The fold of `ℂ̄` is continuous. -/
theorem h36t_fold_continuous : Continuous h36t_fold := by
  refine OnePoint.continuous_map_iff.2 ⟨h36t_foldC_continuous, ?_⟩
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact,
    ← tendsto_norm_atTop_iff_cobounded]
  simp_rw [h36t_norm_foldC]
  exact tendsto_norm_cobounded_atTop

/-- The fold fixes the closed upper half-plane. -/
theorem h36t_fold_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) : h36t_fold (w : ExtPlane) = w := by
  show ((h36t_foldC w : ℂ) : ExtPlane) = w
  congr 1
  apply Complex.ext <;> simp [h36t_foldC, abs_of_nonneg hw]

/-- The fold lands in the closure of `ℍ` in `ℂ̄`. -/
theorem h36t_fold_mem (z : ExtPlane) : h36t_fold z ∈ closure (toExt upperHalf) := by
  rw [scExt_closure_toExt_upperHalf]
  induction z using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe w =>
    refine Or.inl ⟨h36t_foldC w, ?_, rfl⟩
    show 0 ≤ (h36t_foldC w).im
    simp [h36t_foldC]

/-- The fold fixes `ℝ̂`. -/
theorem h36t_fold_extRealLine {x : ExtPlane} (hx : x ∈ extRealLine) : h36t_fold x = x := by
  rcases hx with ⟨w, hw, rfl⟩ | hx
  · exact h36t_fold_of_im_nonneg (le_of_eq (show w.im = 0 from hw).symm)
  · rw [mem_singleton_iff.1 hx]
    rfl

/-- A point of the closure of `ℍ` in `ℂ̄` lies on `ℝ̂` or in `ℍ`. -/
theorem h36t_closure_cases {z : ExtPlane} (hz : z ∈ closure (toExt upperHalf)) :
    z ∈ extRealLine ∨ ∃ τ : UpperHalfPlane, z = ((τ : ℂ) : ExtPlane) := by
  rcases wd_b_closure_upper_cases hz with h | ⟨x, rfl⟩ | ⟨w, hw, rfl⟩
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl ⟨(x : ℂ), Complex.ofReal_im x, rfl⟩)
  · exact Or.inr ⟨UpperHalfPlane.mk w hw, rfl⟩

/-- The boundary-fixing extension on the closed upper half-plane of `ℂ̄`: the geodesic homotopy
between `F₀` and `F₁` on `ℍ`, and `G₀` elsewhere. -/
def h36t_Gup (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ : ExtPlane → ExtPlane) (z : ExtPlane)
    (t : unitInterval) : ExtPlane :=
  OnePoint.elim z (G₀ extInf) fun w =>
    if hw : 0 < w.im then (((c36_d_geod (F₀ (UpperHalfPlane.mk w hw)) (F₁ (UpperHalfPlane.mk w hw)) t :
      UpperHalfPlane) : ℂ) : ExtPlane) else G₀ w

/-- On `ℍ` the extension is the geodesic homotopy. -/
theorem h36t_Gup_coe (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ : ExtPlane → ExtPlane)
    (τ : UpperHalfPlane) (t : unitInterval) :
    h36t_Gup F₀ F₁ G₀ ((τ : ℂ) : ExtPlane) t =
      (((c36_d_geod (F₀ τ) (F₁ τ) t : UpperHalfPlane) : ℂ) : ExtPlane) := by
  show (if hw : 0 < (τ : ℂ).im then _ else _) = _
  simp only [τ.coe_im_pos, ↓reduceDIte]

/-- On `ℝ̂` the extension is `G₀`, for every `t`. -/
theorem h36t_Gup_extRealLine (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ : ExtPlane → ExtPlane)
    {x : ExtPlane} (hx : x ∈ extRealLine) (t : unitInterval) : h36t_Gup F₀ F₁ G₀ x t = G₀ x := by
  rcases hx with ⟨w, hw, rfl⟩ | hx
  · show (if hw' : 0 < w.im then _ else _) = _
    have h : ¬ 0 < w.im := by rw [show w.im = 0 from hw]; exact lt_irrefl 0
    simp only [h, ↓reduceDIte]
  · rw [mem_singleton_iff.1 hx]
    rfl

/-- Euclidean shrinking in `ℂ̄`: every neighbourhood `N` of a point of `ℝ̂` contains a neighbourhood
`N'` such that geodesic segments with endpoints in `N'` stay in `N`. -/
theorem h36t_shrink {w₀ : ExtPlane} (hw₀ : w₀ ∈ extRealLine) {N : Set ExtPlane} (hN : N ∈ 𝓝 w₀) :
    ∃ N' ∈ 𝓝 w₀, N' ⊆ N ∧ ∀ a b : UpperHalfPlane, ((a : ℂ) : ExtPlane) ∈ N' →
      ((b : ℂ) : ExtPlane) ∈ N' → ∀ t : unitInterval,
        (((c36_d_geod a b t : UpperHalfPlane) : ℂ) : ExtPlane) ∈ N := by
  rcases hw₀ with ⟨x, hx, rfl⟩ | hw₀
  · rw [OnePoint.nhds_coe_eq, mem_map] at hN
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
    refine ⟨((↑) : ℂ → ExtPlane) '' ball x ε, ?_, ?_, ?_⟩
    · exact (OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball).mem_nhds ⟨x, mem_ball_self hε, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hball hz
    · rintro a b ⟨za, hza, hza'⟩ ⟨zb, hzb, hzb'⟩ t
      have ha : (a : ℂ) = za := (OnePoint.coe_injective hza').symm
      have hb : (b : ℂ) = zb := (OnePoint.coe_injective hzb').symm
      have hxr : x = ((x.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [show x.im = 0 from hx]
      apply hball
      rw [mem_ball, hxr]
      rw [mem_ball, hxr, ← ha] at hza
      rw [mem_ball, hxr, ← hb] at hzb
      exact h36t_geod_dist_lt a b x.re hza hzb t.2.1 t.2.2
  · rw [mem_singleton_iff.1 hw₀] at hN ⊢
    obtain ⟨K, ⟨-, hKk⟩, hKN⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 hN
    obtain ⟨R, hR⟩ := hKk.isBounded.subset_closedBall 0
    refine ⟨((↑) : ℂ → ExtPlane) '' (closedBall 0 R)ᶜ ∪ {OnePoint.infty}, ?_, ?_, ?_⟩
    · exact OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨isClosed_closedBall, isCompact_closedBall 0 R⟩
    · exact (union_subset_union_left _ (image_mono (compl_subset_compl.2 hR))).trans hKN
    · have hout : ∀ c : UpperHalfPlane, ((c : ℂ) : ExtPlane) ∈
          ((↑) : ℂ → ExtPlane) '' (closedBall 0 R)ᶜ ∪ {OnePoint.infty} → R < ‖(c : ℂ)‖ := by
        rintro c (⟨z, hz, hz'⟩ | hc)
        · rw [OnePoint.coe_injective hz'] at hz
          simpa [mem_closedBall, dist_zero_right] using hz
        · exact absurd (mem_singleton_iff.1 hc) (OnePoint.coe_ne_infty _)
      intro a b ha hb t
      apply hKN
      refine Or.inl ⟨_, fun hK => ?_, rfl⟩
      have h1 := hR hK
      rw [mem_closedBall, dist_zero_right] at h1
      have h2 := h36t_geod_norm_gt a b (hout a ha) (hout b hb) t.2.1 t.2.2
      linarith

/-- The extension is continuous on the closed upper half-plane of `ℂ̄` (times `[0, 1]`). -/
theorem h36t_Gup_continuousOn {F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₀ G₁ : ExtPlane → ExtPlane}
    (hG₀ : IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀)
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁) (hbd : ∀ x ∈ extRealLine, G₀ x = G₁ x) :
    ContinuousOn (fun x : ExtPlane × unitInterval => h36t_Gup F₀ F₁ G₀ x.1 x.2)
      (closure (toExt upperHalf) ×ˢ univ) := by
  rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
  change z₀ ∈ closure (toExt upperHalf) at hz₀
  rcases h36t_closure_cases hz₀ with hR | ⟨τ₀, rfl⟩
  · show Tendsto (fun x : ExtPlane × unitInterval => h36t_Gup F₀ F₁ G₀ x.1 x.2) _
      (𝓝 (h36t_Gup F₀ F₁ G₀ z₀ t₀))
    rw [h36t_Gup_extRealLine F₀ F₁ G₀ hR]
    intro N hN
    have hw₀ : G₀ z₀ ∈ extRealLine := by
      rw [← h36t_image_extRealLine hG₀]
      exact ⟨z₀, hR, rfl⟩
    obtain ⟨N', hN', hN'N, hgeo⟩ := h36t_shrink hw₀ hN
    have h0 : ∀ᶠ z in 𝓝[closure (toExt upperHalf)] z₀, G₀ z ∈ N' := hG₀.2.1 z₀ hz₀ hN'
    have h1 : ∀ᶠ z in 𝓝[closure (toExt upperHalf)] z₀, G₁ z ∈ N' := by
      have h := hG₁.2.1 z₀ hz₀
      rw [ContinuousWithinAt, ← hbd z₀ hR] at h
      exact h hN'
    have hfst : Tendsto Prod.fst (𝓝[closure (toExt upperHalf) ×ˢ univ] (z₀, t₀))
        (𝓝[closure (toExt upperHalf)] z₀) :=
      continuous_fst.continuousWithinAt.tendsto_nhdsWithin fun x hx => hx.1
    rw [Filter.mem_map]
    filter_upwards [hfst.eventually h0, hfst.eventually h1, eventually_mem_nhdsWithin] with x hx0 hx1 hxs
    rcases h36t_closure_cases hxs.1 with hxR | ⟨τ, hτ⟩
    · rw [mem_preimage, h36t_Gup_extRealLine F₀ F₁ G₀ hxR]
      exact hN'N hx0
    · rw [mem_preimage, hτ, h36t_Gup_coe]
      rw [hτ, h36t_ext_coe hG₀] at hx0
      rw [hτ, h36t_ext_coe hG₁] at hx1
      exact hgeo _ _ hx0 hx1 x.2
  · have he : Topology.IsOpenEmbedding (fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) :=
      OnePoint.isOpenEmbedding_coe.comp UpperHalfPlane.isOpenEmbedding_coe
    have hE := he.prodMap (Topology.IsOpenEmbedding.id (X := unitInterval))
    have hc : ContinuousAt ((fun x : ExtPlane × unitInterval => h36t_Gup F₀ F₁ G₀ x.1 x.2) ∘
        Prod.map (fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) id) (τ₀, t₀) := by
      have e : ((fun x : ExtPlane × unitInterval => h36t_Gup F₀ F₁ G₀ x.1 x.2) ∘
          Prod.map (fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) id) =
          fun x : UpperHalfPlane × unitInterval =>
            (((c36_d_geod (F₀ x.1) (F₁ x.1) x.2 : UpperHalfPlane) : ℂ) : ExtPlane) := by
        funext x
        exact h36t_Gup_coe F₀ F₁ G₀ x.1 x.2
      rw [e]
      exact (OnePoint.continuous_coe.comp (UpperHalfPlane.continuous_coe.comp
        (c36_d_geod_continuous.comp ((F₀.continuous.comp continuous_fst).prodMk
        ((F₁.continuous.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))))).continuousAt
    rw [hE.continuousAt_iff] at hc
    exact hc.continuousWithinAt

/-- **Theorem 36.1, `⇐`**: two quasiconformal maps `f₀, f₁ : S → S₁` whose lifts `f̃₀, f̃₁` to the
universal covering have homeomorphic extensions agreeing on `ℝ̂` are homotopic modulo the boundary
(via the geodesic homotopy between the lifts). -/
theorem h36_thm36_1_mpr {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [T2Space S₁] [ConnectedSpace S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) (hΓ : IsFuchsian Γ) (f₀ f₁ : S ≃ₜ S₁)
    (hf₀ : IsQCRS f₀) (hf₁ : IsQCRS f₁) :
    (∃ (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ G₁ : ExtPlane → ExtPlane),
        IsLift p p₁ f₀ F₀ ∧ IsLift p p₁ f₁ F₁ ∧ IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀ ∧
        IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁ ∧ ∀ x ∈ extRealLine, G₀ x = G₁ x) →
      HomotopicModBoundary p p₁ f₀ f₁ := by
  have _ := hΓ
  have _ := hf₀
  have _ := hf₁
  rintro ⟨F₀, F₁, G₀, G₁, hF₀, hF₁, hG₀, hG₁, hbd⟩
  have hsurj : Function.Surjective p := hp.2.2.1
  have hsec : ∀ x, p (Function.surjInv hsurj x) = x := Function.surjInv_eq hsurj
  have hHtc : Continuous (fun x : UpperHalfPlane × unitInterval => c36_d_geod (F₀ x.1) (F₁ x.1) x.2) :=
    c36_d_geod_continuous.comp ((F₀.continuous.comp continuous_fst).prodMk
      ((F₁.continuous.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))
  have hHf : ∀ (τ : UpperHalfPlane) (t : unitInterval),
      p₁ (c36_d_geod (F₀ (Function.surjInv hsurj (p τ))) (F₁ (Function.surjInv hsurj (p τ))) t) =
        p₁ (c36_d_geod (F₀ τ) (F₁ τ) t) :=
    fun τ t => h36t_wd hp hp₁ hF₀ hF₁ hG₀ hG₁ hbd (hsec (p τ)) t
  have hq : Topology.IsQuotientMap (Prod.map p (id : unitInterval → unitInterval)) :=
    (hp.1.isOpenMap.prodMap IsOpenMap.id).isQuotientMap (hp.1.continuous.prodMap continuous_id)
      (hsurj.prodMap Function.surjective_id)
  have hHfc : Continuous (fun x : S × unitInterval =>
      p₁ (c36_d_geod (F₀ (Function.surjInv hsurj x.1)) (F₁ (Function.surjInv hsurj x.1)) x.2)) := by
    refine hq.continuous_iff.2 ?_
    have e : (fun x : S × unitInterval =>
        p₁ (c36_d_geod (F₀ (Function.surjInv hsurj x.1)) (F₁ (Function.surjInv hsurj x.1)) x.2)) ∘
          Prod.map p id = fun x : UpperHalfPlane × unitInterval => p₁ (c36_d_geod (F₀ x.1) (F₁ x.1) x.2) := by
      funext x
      exact hHf x.1 x.2
    rw [e]
    exact hp₁.1.continuous.comp hHtc
  refine ⟨⟨_, hHfc⟩, fun τ t => c36_d_geod (F₀ τ) (F₁ τ) t,
    fun z t => h36t_Gup F₀ F₁ G₀ (h36t_fold z) t, ?_, ?_, ⟨hHtc, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    show p₁ (c36_d_geod (F₀ (Function.surjInv hsurj x)) (F₁ (Function.surjInv hsurj x)) 0) = f₀ x
    rw [h36t_geod_zero, hF₀, hsec]
  · intro x
    show p₁ (c36_d_geod (F₀ (Function.surjInv hsurj x)) (F₁ (Function.surjInv hsurj x)) 1) = f₁ x
    rw [h36t_geod_one, hF₁, hsec]
  · intro τ t
    exact (hHf τ t).symm
  · exact (h36t_Gup_continuousOn hG₀ hG₁ hbd).comp_continuous
      ((h36t_fold_continuous.comp continuous_fst).prodMk continuous_snd)
      (fun x => ⟨h36t_fold_mem x.1, mem_univ _⟩)
  · intro τ t
    show h36t_Gup F₀ F₁ G₀ (h36t_fold ((τ : ℂ) : ExtPlane)) t = _
    rw [h36t_fold_of_im_nonneg τ.coe_im_pos.le, h36t_Gup_coe]
  · intro x hx t
    show h36t_Gup F₀ F₁ G₀ (h36t_fold x) t = h36t_Gup F₀ F₁ G₀ (h36t_fold x) 0
    rw [h36t_fold_extRealLine hx, h36t_Gup_extRealLine F₀ F₁ G₀ hx, h36t_Gup_extRealLine F₀ F₁ G₀ hx]

/-! ### s36h Stage 2 (coordinator 553e2d), part Q1: the boundary extension of a lift, the `⇒` of Theorem 36.1
and the limit-set lemma (`h36q_`) -/

/-- **Q2**: a `K`-q.c. lift extends to a homeomorphism of the closed half-plane (Theorem 13.3 on the Jordan domain
`ℍ`). -/
theorem h36q_ext_of_isKQC {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {K : ℝ} (hF : IsKQC (liftToC F) upperHalf K) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F) upperHalf upperHalf G :=
  thm13_3_boundary_correspondence isJordanDomain_upperHalf isJordanDomain_upperHalf ⟨K, hF⟩
    (h36q_liftToC_image F)

/-- **Q1 + Q2**: in holomorphic atlases, the lift of a q.c. map extends to a homeomorphism of the closed
half-plane. -/
theorem h36q_ext_of_lift {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) {f : S ≃ₜ S₁} (hf : IsQCRS f)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p p₁ f F) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F) upperHalf upperHalf G := by
  obtain ⟨K, hK⟩ := hf
  exact h36q_ext_of_isKQC (h23l_lift_isKQC hp hp₁ hK hF)

/-- The inverse `F⁻¹` of a lift of `f` is a lift of `f⁻¹`. -/
theorem h36q_isLift_symm {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁} {f : S ≃ₜ S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p p₁ f F) : IsLift p₁ p f.symm F.symm := by
  intro τ
  have h := hF (F.symm τ)
  rw [F.apply_symm_apply] at h
  rw [h, f.symm_apply_apply]

/-- **E** [P1, stub] The inverse extension: if `G` extends `liftToC F` to a homeomorphism of the closed half-plane,
then its inverse on `closure ℍ` extends `liftToC F⁻¹` (`G` is a continuous bijection of the compact set
`closure (toExt ℍ)` onto itself, hence a homeomorphism of it, and `G⁻¹ = F⁻¹` on `ℍ`). -/
theorem h36q_ext_symm {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) :
    ∃ G' : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F.symm) upperHalf upperHalf G' ∧
      ∀ x ∈ closure (toExt upperHalf), G' (G x) = x ∧ G (G' x) = x := by
  have hGi : InjOn G (closure (toExt upperHalf)) := hG.2.2.1
  have hsurj : SurjOn G (closure (toExt upperHalf)) (closure (toExt upperHalf)) := by
    intro x hx
    rw [hG.2.2.2]
    exact hx
  have hL := hGi.leftInvOn_invFunOn
  have hR := hsurj.rightInvOn_invFunOn
  have hM := hsurj.mapsTo_invFunOn
  refine ⟨Function.invFunOn G (closure (toExt upperHalf)), ⟨?_, ?_, ?_, ?_⟩, fun x hx => ⟨hL hx, hR hx⟩⟩
  · intro z hz
    have hz' : 0 < z.im := hz
    have h1 : liftToC F.symm z = ((F.symm ⟨z, hz'⟩ : UpperHalfPlane) : ℂ) := by
      unfold liftToC
      simp only [hz', ↓reduceDIte]
    have h2 : G (((F.symm ⟨z, hz'⟩ : UpperHalfPlane) : ℂ) : ExtPlane) = (z : ExtPlane) := by
      rw [h36t_ext_coe hG, F.apply_symm_apply]
    have hK : (((F.symm ⟨z, hz'⟩ : UpperHalfPlane) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
      subset_closure ⟨_, (F.symm _).coe_im_pos, rfl⟩
    rw [h1, ← h2, hL hK]
  · rw [continuousOn_iff_isClosed]
    intro t ht
    refine ⟨G '' (t ∩ closure (toExt upperHalf)),
      ((ht.inter isClosed_closure).isCompact.image_of_continuousOn (hG.2.1.mono inter_subset_right)).isClosed,
      ?_⟩
    ext x
    constructor
    · rintro ⟨hxt, hxK⟩
      exact ⟨⟨_, ⟨hxt, hM hxK⟩, hR hxK⟩, hxK⟩
    · rintro ⟨⟨y, ⟨hyt, hyK⟩, rfl⟩, hxK⟩
      refine ⟨?_, hxK⟩
      show Function.invFunOn G (closure (toExt upperHalf)) (G y) ∈ t
      rw [hL hyK]
      exact hyt
  · intro a ha b hb hab
    calc a = G (Function.invFunOn G (closure (toExt upperHalf)) a) := (hR ha).symm
      _ = G (Function.invFunOn G (closure (toExt upperHalf)) b) := by rw [hab]
      _ = b := hR hb
  · refine Subset.antisymm (fun _ ⟨x, hx, hxe⟩ => hxe ▸ hM hx) fun x hx => ⟨G x, ?_, hL hx⟩
    rw [← hG.2.2.2]
    exact mem_image_of_mem G hx

/-- The fold `h36t_fold` commutes with a real Möbius map at a point `z` of the lower half-plane: both sides are
`γ(z̄) = conj(γ z)` (`γ` preserves the lower half-plane and has real coefficients). -/
theorem h36q_c_fold_comm (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z.im < 0) :
    mobiusSL (slRealToComplex γ) (h36t_fold (z : ExtPlane)) =
      h36t_fold (mobiusSL (slRealToComplex γ) (z : ExtPlane)) := by
  have hfold : ∀ w : ℂ, w.im < 0 → h36t_fold (w : ExtPlane) = ((conj w : ℂ) : ExtPlane) := by
    intro w hw
    show ((h36t_foldC w : ℂ) : ExtPlane) = _
    congr 1
    apply Complex.ext <;> simp [h36t_foldC, abs_of_neg hw]
  have hden := k24_d_den_ne_zero (k24_det_realR γ) hz.ne
  have hzc : (conj z).im ≠ 0 := by
    rw [Complex.conj_im]
    exact neg_ne_zero.2 hz.ne
  have hdenc := k24_d_den_ne_zero (k24_det_realR γ) hzc
  have him : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im < 0 := by
    rw [mobiusFn_im_real, k24_det_realR, one_mul]
    exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.2 hden)
  rw [hfold z hz, k24_mobiusSL_real, mobiusExt_coe hdenc, mobiusExt_coe hden, hfold _ him]
  congr 1
  simp [mobiusFn, map_div₀]

/-- **Q4** [P3, stub] Limit points go to limit points: let `G` extend `liftToC F` homeomorphically to the closed
half-plane, and let `F` conjugate every `γ ∈ Γ` into `Γ₁` (`F ∘ γ = δ ∘ F`).  Then `G` maps `Λ(Γ) ∩ ℝ̂` into
`Λ(Γ₁)`.  (For `γₙ q → x`: replace `q` by `q̄` if `Im q < 0`; then `G(γₙ q) = δₙ (G q) → G x` by the equivariance of
`G` on `closure ℍ` and its continuity; `δₙ = δₘ` forces `γₙ = ±γₘ` because `G` is injective on `closure ℍ`, so
`(δₙ)` has infinite range, and `k22_t_injective_reindex` gives an injective subsequence.  `IsFuchsian` is not
needed.) -/
theorem h36q_limitSet_mapsTo {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G)
    (hdeck : ∀ γ ∈ Γ, ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ) {x : ExtPlane} (hx : x ∈ extRealLine)
    (hxΛ : x ∈ fuchsianLimitSet Γ) : G x ∈ fuchsianLimitSet Γ₁ := by
  obtain ⟨q, γs, hinj, hlim⟩ := hxΛ
  have hmem : ∀ n, ∃ g ∈ Γ, slRealToComplex g = (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) :=
    fun n => Subgroup.mem_map.1 (γs n).2
  choose g hgΓ hg using hmem
  choose δ hδΓ hδ using fun n => hdeck (g n) (hgΓ n)
  have hlim' : Tendsto (fun n => mobiusSL (slRealToComplex (g n)) q) atTop (𝓝 x) := by
    simpa only [hg] using hlim
  obtain ⟨q', hq'c, hq'lim⟩ : ∃ q' ∈ closure (toExt upperHalf),
      Tendsto (fun n => mobiusSL (slRealToComplex (g n)) q') atTop (𝓝 x) := by
    by_cases hq : q ∈ closure (toExt upperHalf)
    · exact ⟨q, hq, hlim'⟩
    · have hqR : q ∉ extRealLine := fun h => hq (h36t_extRealLine_subset_closure h)
      rcases k24_mem_halves hqR with hq' | ⟨z, hz, rfl⟩
      · exact absurd (subset_closure hq') hq
      · refine ⟨h36t_fold (z : ExtPlane), h36t_fold_mem _, ?_⟩
        have h := (h36t_fold_continuous.tendsto x).comp hlim'
        rw [h36t_fold_extRealLine hx] at h
        refine h.congr fun n => ?_
        exact (h36q_c_fold_comm (g n) hz).symm
  have hcl : ∀ n, mobiusSL (slRealToComplex (g n)) q' ∈ closure (toExt upperHalf) := fun n =>
    MapsTo.closure (fun p hp => k24_real_mapsTo_upper (g n) hp) (k22_t_continuous _) hq'c
  have hGlim : Tendsto (fun n => mobiusSL (slRealToComplex (δ n)) (G q')) atTop (𝓝 (G x)) := by
    have h1 : Tendsto (fun n => mobiusSL (slRealToComplex (g n)) q') atTop
        (𝓝[closure (toExt upperHalf)] x) :=
      tendsto_nhdsWithin_iff.2 ⟨hq'lim, Eventually.of_forall hcl⟩
    refine ((hG.2.1 x (h36t_extRealLine_subset_closure hx)).tendsto.comp h1).congr fun n => ?_
    exact h36t_ext_equivariant hG (hδ n) hq'c
  have hginj : Function.Injective g := by
    intro n m h
    apply hinj
    apply Subtype.ext
    rw [← hg, ← hg, h]
  let s : ℕ → Γ₁.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) := fun n =>
    ⟨slRealToComplex (δ n), Subgroup.mem_map_of_mem _ (hδΓ n)⟩
  have hinf : (range s).Infinite := by
    intro hfin
    have hfib : ∀ v ∈ range s, (s ⁻¹' {v}).Finite := by
      rintro _ ⟨n₀, rfl⟩
      refine (((finite_singleton (-g n₀)).insert (g n₀)).preimage hginj.injOn).subset ?_
      intro n hn
      have hn' : s n = s n₀ := hn
      have hδeq : slRealToComplex (δ n) = slRealToComplex (δ n₀) := congrArg Subtype.val hn'
      have hact : ∀ τ, δ n • τ = δ n₀ • τ := fun τ => by
        apply UpperHalfPlane.ext
        apply OnePoint.coe_injective
        rw [← h36t_mobiusSL_coe, ← h36t_mobiusSL_coe, hδeq]
      have hgact : ∀ τ, g n • τ = g n₀ • τ := fun τ => F.injective (by rw [hδ, hδ, hact])
      exact b33_d_eq_or_eq_neg hgact
    exact Set.infinite_univ ((hfin.preimage' hfib).subset fun n _ => ⟨n, rfl⟩)
  obtain ⟨ψ, hψinj, hψ⟩ := k22_t_injective_reindex s hinf
  exact ⟨G q', s ∘ ψ, hψinj, hGlim.comp hψ⟩

/-- **Q5**: the extension of a lift of a homeomorphism maps `b(Γ) = ℝ̂ ∖ Λ(Γ)` onto `b(Γ₁)` (Q4 for `F` and, through
the inverse extension `h36q_ext_symm`, for `F⁻¹`; the deck correspondences from `h23l_deck`). -/
theorem h36q_ordinarySet_image {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    {p₁ : UpperHalfPlane → S₁} (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) {f : S ≃ₜ S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p p₁ f F) {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) : G '' ordinarySet Γ = ordinarySet Γ₁ := by
  obtain ⟨G', hG', hinv⟩ := h36q_ext_symm hG
  have hGR := h36t_image_extRealLine hG
  have hG'R := h36t_image_extRealLine hG'
  have hd : ∀ γ ∈ Γ, ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ := fun γ hγ => h23l_deck hp hp₁ hF hγ
  have hd' : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ, ∀ τ, F.symm (δ • τ) = γ • F.symm τ := fun δ hδ =>
    h23l_deck hp₁ hp (h36q_isLift_symm hF) hδ
  ext y
  constructor
  · rintro ⟨x, ⟨hxR, hxΛ⟩, rfl⟩
    have hGx : G x ∈ extRealLine := hGR ▸ mem_image_of_mem G hxR
    refine ⟨hGx, fun hΛ => hxΛ ?_⟩
    have h := h36q_limitSet_mapsTo hG' hd' hGx hΛ
    rwa [(hinv x (h36t_extRealLine_subset_closure hxR)).1] at h
  · rintro ⟨hyR, hyΛ⟩
    have hy' : G' y ∈ extRealLine := hG'R ▸ mem_image_of_mem G' hyR
    refine ⟨G' y, ⟨hy', fun hΛ => hyΛ ?_⟩, (hinv y (h36t_extRealLine_subset_closure hyR)).2⟩
    have h := h36q_limitSet_mapsTo hG hd hy' hΛ
    rwa [(hinv y (h36t_extRealLine_subset_closure hyR)).2] at h

/-! ### The `⇒` of Theorem 36.1 -/

/-- Uniqueness of the extension: a homeomorphic extension of `liftToC F` agrees on `closure ℍ` with every map that is
continuous there and equals `F` on `ℍ` (`ℍ` is dense in its closure). -/
theorem h36q_eqOn_closure {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F) upperHalf upperHalf G₁) (hG₂ : ContinuousOn G₂ (closure (toExt upperHalf)))
    (h : ∀ τ : UpperHalfPlane, G₂ ((τ : ℂ) : ExtPlane) = ((F τ : ℂ) : ExtPlane)) :
    EqOn G₁ G₂ (closure (toExt upperHalf)) := by
  refine Set.EqOn.of_subset_closure (s := toExt upperHalf) ?_ hG₁.2.1 hG₂ subset_closure subset_rfl
  rintro _ ⟨z, hz, rfl⟩
  have e : ((z : ℂ) : ExtPlane) = (((UpperHalfPlane.mk z hz : UpperHalfPlane) : ℂ) : ExtPlane) := rfl
  rw [e, h36t_ext_coe hG₁, h]

/-- **Theorem 36.1, `⇒`**: the end maps `H̃(·, 0)`, `H̃(·, 1)` of the lifted homotopy are homeomorphisms
(`h23l_lift_homeomorph`) lifting `f₀`, `f₁`; they are q.c. and extend to `closure ℍ` (Q1 + Q2); the extensions agree
there with `G(·, 0)`, `G(·, 1)` (`h36q_eqOn_closure`), which agree on `ℝ̂`. -/
theorem h36q_mp {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) (f₀ f₁ : S ≃ₜ S₁)
    (hf₀ : IsQCRS f₀) (hf₁ : IsQCRS f₁) :
    HomotopicModBoundary p p₁ f₀ f₁ →
      ∃ (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ G₁ : ExtPlane → ExtPlane),
        IsLift p p₁ f₀ F₀ ∧ IsLift p p₁ f₁ F₁ ∧ IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀ ∧
        IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁ ∧ ∀ x ∈ extRealLine, G₀ x = G₁ x := by
  rintro ⟨H, Ht, G, h0, h1, ⟨hHtc, hHt⟩, hGc, hGHt, hbd⟩
  have hc : ∀ t : unitInterval, Continuous fun τ => Ht τ t := fun t =>
    hHtc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨F₀, hF₀⟩ := h23l_lift_homeomorph hp.1 hp₁.1 f₀ (hc 0) fun τ => (hHt τ 0).trans (h0 (p τ))
  obtain ⟨F₁, hF₁⟩ := h23l_lift_homeomorph hp.1 hp₁.1 f₁ (hc 1) fun τ => (hHt τ 1).trans (h1 (p τ))
  have hL₀ : IsLift p p₁ f₀ F₀ := fun τ => by rw [hF₀]; exact (hHt τ 0).trans (h0 (p τ))
  have hL₁ : IsLift p p₁ f₁ F₁ := fun τ => by rw [hF₁]; exact (hHt τ 1).trans (h1 (p τ))
  obtain ⟨G₀, hG₀⟩ := h36q_ext_of_lift hp hp₁ hf₀ hL₀
  obtain ⟨G₁, hG₁⟩ := h36q_ext_of_lift hp hp₁ hf₁ hL₁
  have hGt : ∀ t : unitInterval, ContinuousOn (fun x => G x t) (closure (toExt upperHalf)) := fun t =>
    (hGc.comp (continuous_id.prodMk continuous_const)).continuousOn
  have e₀ := h36q_eqOn_closure hG₀ (hGt 0) fun τ => by rw [hGHt, hF₀]
  have e₁ := h36q_eqOn_closure hG₁ (hGt 1) fun τ => by rw [hGHt, hF₁]
  refine ⟨F₀, F₁, G₀, G₁, hL₀, hL₁, hG₀, hG₁, fun x hx => ?_⟩
  rw [e₀ (h36t_extRealLine_subset_closure hx), e₁ (h36t_extRealLine_subset_closure hx)]
  exact (hbd x hx 1).symm

/-! ### Batch C (low priority): the limit-set lemma `lift_homotopy_agrees_on_limitSet` -/

/-- **C1** [P1, stub] The deck element of a lifted homotopy does not depend on `t`: for `γ ∈ Γ` there is `δ ∈ Γ₁` with
`H̃(γ τ, t) = δ H̃(τ, t)` for all `τ, t` (both sides lift `(τ, t) ↦ H(p τ, t)` through `p₁` on the connected
`ℍ × [0, 1]` and agree at one point: `IsCoveringMap.eq_of_comp_eq`). -/
theorem h36q_lh_deck {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    {p₁ : UpperHalfPlane → S₁} (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁)
    {H : C(S × unitInterval, S₁)} {Ht : UpperHalfPlane → unitInterval → UpperHalfPlane}
    (hH : IsLiftHomotopy p p₁ H Ht) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ δ ∈ Γ₁, ∀ τ t, Ht (γ • τ) t = δ • Ht τ t := by
  have hpγ : ∀ τ, p (γ • τ) = p τ := fun τ => ((hp.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm
  have h0 : p₁ (Ht UpperHalfPlane.I 0) = p₁ (Ht (γ • UpperHalfPlane.I) 0) := by rw [hH.2, hH.2, hpγ]
  obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 h0
  refine ⟨δ, hδ, fun τ t => ?_⟩
  have hcomp : p₁ ∘ (fun x : UpperHalfPlane × unitInterval => Ht (γ • x.1) x.2) =
      p₁ ∘ (fun x : UpperHalfPlane × unitInterval => δ • Ht x.1 x.2) := by
    funext x
    simp only [Function.comp_apply]
    rw [hH.2, hpγ, ← hH.2]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  have h := hp₁.1.eq_of_comp_eq
    (hH.1.comp (((continuous_const_smul γ).comp continuous_fst).prodMk continuous_snd))
    ((continuous_const_smul δ).comp hH.1) hcomp (UpperHalfPlane.I, 0) hδe.symm
  exact congrFun h (τ, t)

/-- The fixed points in `ℂ̄` of a Möbius map `z ↦ (a z + b)/(c z + d)` (`a d - b c = 1`) other than the identity form a
finite set: besides `∞` they are roots of the nonzero quadratic `c z² + (d - a) z - b`. -/
theorem h36q_a_fix_finite {a b c d : ℂ} (h : a * d - b * c = 1) (hne : ¬ (b = 0 ∧ c = 0 ∧ a = d)) :
    (mobiusFixedPoints a b c d).Finite := by
  have hP : Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C (d - a) * Polynomial.X - Polynomial.C b ≠ 0 := by
    intro h0
    have h2 := congrArg (fun q => Polynomial.coeff q 2) h0
    have h1 := congrArg (fun q => Polynomial.coeff q 1) h0
    have h00 := congrArg (fun q => Polynomial.coeff q 0) h0
    simp at h2 h1 h00
    exact hne ⟨h00, h2, by linear_combination -h1⟩
  refine ((Set.finite_singleton extInf).union
    ((Polynomial.finite_setOfPred_isRoot hP).image ((↑) : ℂ → ExtPlane))).subset ?_
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe z =>
    refine Or.inr ⟨z, ?_, rfl⟩
    have hz := (mem_mobiusFixedPoints_coe_iff h z).1 hx
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hz

/-- An element of `SL(2, ℝ)` acting trivially on `ℍ` is `±1` (its fixed points `i`, `2i` force `b = c = 0`, `a = d`). -/
theorem h36q_a_eq_one_or_neg_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : ∀ τ : UpperHalfPlane, γ • τ = τ) :
    γ = 1 ∨ γ = -1 := by
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast k24_det_realR γ
  have hfix : ∀ τ : UpperHalfPlane, (γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - γ 0 1 = 0 := by
    intro τ
    refine (mem_mobiusFixedPoints_coe_iff hdetC _).1 ?_
    show mobiusExt _ _ _ _ _ = _
    rw [← k24_mobiusSL_real, h36t_mobiusSL_coe, h τ]
  have h1 := hfix UpperHalfPlane.I
  have h2 := hfix (UpperHalfPlane.mk (2 * Complex.I) (by simp))
  have e1 := congrArg Complex.re h1
  have e2 := congrArg Complex.im h1
  have e3 := congrArg Complex.re h2
  norm_num [mul_pow] at e1 e2 e3
  have hc : γ 1 0 = 0 := by linarith
  have hb : γ 0 1 = 0 := by linarith
  have hd : γ 1 1 = γ 0 0 := by linarith
  have hdet := k24_det_realR γ
  rw [hb, hd] at hdet
  have ha : (γ 0 0 - 1) * (γ 0 0 + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 ha with ha | ha
  · left
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd] <;> linarith
  · right
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd] <;> linarith

/-- **C2** [P1, stub] The extended lifted homotopy is constant in `t` at every fixed point `y ∈ closure ℍ` of an element
`γ ≠ ±1` of `Γ`: with `δ` from `h36q_lh_deck`, `G(γ y', t) = δ G(y', t)` on `closure ℍ` (continuity), so `G(y, t)` is a
fixed point of `δ`; `δ ≠ ±1` because `H̃(·, 0)` is injective (a lift of the homeomorphism `f₀`,
`h23l_lift_homeomorph`); `δ` has at most two fixed points (`mobius_fixed_points`) and `[0, 1]` is connected. -/
theorem h36q_lh_fix {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    {p₁ : UpperHalfPlane → S₁} (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) {f₀ : S ≃ₜ S₁}
    {H : C(S × unitInterval, S₁)} (hH₀ : ∀ x, H (x, 0) = f₀ x)
    {Ht : UpperHalfPlane → unitInterval → UpperHalfPlane} (hH : IsLiftHomotopy p p₁ H Ht)
    {G : ExtPlane → unitInterval → ExtPlane} (hG : Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2))
    (hGH : ∀ (τ : UpperHalfPlane) (t : unitInterval), G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hγ₁ : γ ≠ 1) (hγ₂ : γ ≠ -1) {y : ExtPlane}
    (hy : y ∈ closure (toExt upperHalf)) (hfix : mobiusSL (slRealToComplex γ) y = y) (t : unitInterval) :
    G y t = G y 0 := by
  obtain ⟨δ, -, hγδ⟩ := h36q_lh_deck hp hp₁ hH hγ
  have hGs : ∀ s : unitInterval, Continuous fun x => G x s := fun s =>
    hG.comp (continuous_id.prodMk continuous_const)
  -- `G(·, s)` intertwines `γ` and `δ` on `closure ℍ`, so `G(y, s)` is a fixed point of `δ`
  have heq : ∀ s : unitInterval, mobiusSL (slRealToComplex δ) (G y s) = G y s := by
    intro s
    have hE : EqOn (fun x => G (mobiusSL (slRealToComplex γ) x) s)
        (fun x => mobiusSL (slRealToComplex δ) (G x s)) (closure (toExt upperHalf)) := by
      refine Set.EqOn.of_subset_closure (s := toExt upperHalf) ?_
        ((hGs s).comp (k22_t_continuous _)).continuousOn ((k22_t_continuous _).comp (hGs s)).continuousOn
        subset_closure subset_rfl
      rintro _ ⟨z, hz, rfl⟩
      have e : ((z : ℂ) : ExtPlane) = (((UpperHalfPlane.mk z hz : UpperHalfPlane) : ℂ) : ExtPlane) := rfl
      simp only
      rw [e, h36t_mobiusSL_coe, hGH, hGH, hγδ, h36t_mobiusSL_coe]
    have h := hE hy
    simp only at h
    rw [hfix] at h
    exact h.symm
  -- `δ` is not the identity: otherwise `γ` would act trivially, since `H̃(·, 0)` is injective
  have hdetC : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by exact_mod_cast k24_det_realR δ
  have hne : ¬ ((δ 0 1 : ℂ) = 0 ∧ (δ 1 0 : ℂ) = 0 ∧ (δ 0 0 : ℂ) = δ 1 1) := by
    rintro ⟨hb, hc, had⟩
    have ha : (δ 0 0 : ℂ) ≠ 0 := by
      intro ha0
      rw [ha0, hb, zero_mul, zero_mul, sub_zero] at hdetC
      exact zero_ne_one hdetC
    have hδ : ∀ w : UpperHalfPlane, δ • w = w := by
      intro w
      apply UpperHalfPlane.ext
      rw [h36t_coe_smul, hb, hc, ← had, zero_mul, zero_add, add_zero]
      exact mul_div_cancel_left₀ _ ha
    have hc0 : Continuous fun τ => Ht τ 0 := hH.1.comp (continuous_id.prodMk continuous_const)
    obtain ⟨F₀, hF₀⟩ := h23l_lift_homeomorph hp.1 hp₁.1 f₀ hc0 fun τ => (hH.2 τ 0).trans (hH₀ (p τ))
    have hγid : ∀ τ : UpperHalfPlane, γ • τ = τ := by
      intro τ
      apply F₀.injective
      rw [hF₀]
      show Ht (γ • τ) 0 = Ht τ 0
      rw [hγδ, hδ]
    rcases h36q_a_eq_one_or_neg_one hγid with h | h
    · exact hγ₁ h
    · exact hγ₂ h
  -- `t ↦ G(y, t)` is a continuous map of the connected `[0, 1]` into the finite set `Fix δ`
  have hmaps : MapsTo (fun s => G y s) univ (mobiusFixedPoints (δ 0 0 : ℂ) (δ 0 1) (δ 1 0) (δ 1 1)) := by
    intro s _
    show mobiusExt _ _ _ _ (G y s) = G y s
    rw [← k24_mobiusSL_real]
    exact heq s
  exact isPreconnected_univ.constant_of_mapsTo (h36q_a_fix_finite hdetC hne).isDiscrete
    (hG.comp (continuous_const.prodMk continuous_id)).continuousOn hmaps (mem_univ t) (mem_univ 0)

/-- The value of a real Möbius map at a real point off its pole is the real number
`(a t + b) / (c t + d)`. -/
theorem h36q_d_val (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) {t : ℝ} (ht : m 1 0 * t + m 1 1 ≠ 0) :
    mobiusSL (slRealToComplex m) ((t : ℂ) : ExtPlane) =
      ((((m 0 0 * t + m 0 1) / (m 1 0 * t + m 1 1) : ℝ) : ℂ) : ExtPlane) := by
  have ht' : ((m 1 0 : ℝ) : ℂ) * (t : ℂ) + ((m 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [k24_mobiusSL_real, mobiusExt_coe ht']
  congr 1
  simp only [mobiusFn]
  push_cast
  ring

/-- A real Möbius map sending the real point `t` into `ℂ` has no pole at `t`. -/
theorem h36q_d_den_ne (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) {t : ℝ} {s : Set ℂ}
    (h : mobiusSL (slRealToComplex m) ((t : ℂ) : ExtPlane) ∈ ((↑) : ℂ → ExtPlane) '' s) :
    m 1 0 * t + m 1 1 ≠ 0 := by
  intro h0
  have h0' : ((m 1 0 : ℝ) : ℂ) * (t : ℂ) + ((m 1 1 : ℝ) : ℂ) = 0 := by exact_mod_cast h0
  rw [k24_mobiusSL_real, mobiusExt_coe_of_eq_zero h0'] at h
  obtain ⟨z, -, hz⟩ := h
  exact OnePoint.coe_ne_infty z hz

/-- **Intermediate value theorem.** A real Möbius map sending `[-ε, ε]` into the disc `|w| < ε` has a fixed
point in `[-ε, ε]`. -/
theorem h36q_d_ivt (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t ∈ Icc (-ε) ε, mobiusSL (slRealToComplex m) ((t : ℂ) : ExtPlane) ∈
      ((↑) : ℂ → ExtPlane) '' ball (0 : ℂ) ε) :
    ∃ t ∈ Icc (-ε) ε, mobiusSL (slRealToComplex m) ((t : ℂ) : ExtPlane) = ((t : ℂ) : ExtPlane) := by
  have hden : ∀ t ∈ Icc (-ε) ε, m 1 0 * t + m 1 1 ≠ 0 := fun t ht => h36q_d_den_ne m (h t ht)
  have habs : ∀ t ∈ Icc (-ε) ε, |(m 0 0 * t + m 0 1) / (m 1 0 * t + m 1 1)| < ε := by
    intro t ht
    have h1 := h t ht
    rw [h36q_d_val m (hden t ht)] at h1
    obtain ⟨z, hz, hzq⟩ := h1
    rw [OnePoint.coe_injective hzq, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hz
    exact hz
  have hfc : ContinuousOn (fun t : ℝ => (m 0 0 * t + m 0 1) / (m 1 0 * t + m 1 1) - t) (Icc (-ε) ε) :=
    ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) hden) continuousOn_id
  have hle : -ε ≤ ε := by linarith
  have h1 := habs ε ⟨hle, le_rfl⟩
  have h2 := habs (-ε) ⟨le_rfl, hle⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hle hfc (show (0 : ℝ) ∈ Icc _ _ from
    ⟨by linarith [(abs_lt.1 h1).2], by linarith [(abs_lt.1 h2).1]⟩)
  refine ⟨t, ht, ?_⟩
  rw [h36q_d_val m (hden t ht)]
  congr 2
  linarith

/-- Every point of `ℝ̂` is the image of `0` under some element of `SL(2, ℝ)`. -/
theorem h36q_d_exists_base {a : ExtPlane} (ha : a ∈ extRealLine) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) ℝ, mobiusSL (slRealToComplex h) ((0 : ℂ) : ExtPlane) = a := by
  rcases ha with ⟨z, hz, rfl⟩ | ha
  · obtain ⟨h, hh⟩ : ∃ h : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (h : Matrix (Fin 2) (Fin 2) ℝ) = !![1, z.re; 0, 1] :=
      ⟨⟨!![1, z.re; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
    refine ⟨h, ?_⟩
    rw [k24_mobiusSL_real, hh, mobiusExt_coe (by simp)]
    congr 1
    apply Complex.ext <;> simp [mobiusFn, show z.im = 0 from hz]
  · obtain ⟨h, hh⟩ : ∃ h : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (h : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] :=
      ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
    refine ⟨h, ?_⟩
    rw [mem_singleton_iff.1 ha, k24_mobiusSL_real, hh, mobiusExt_coe_of_eq_zero (by simp)]

/-- Fixed points near the attracting point: if real `γₙ` converge to `a ∈ ℝ̂` uniformly on the compact sets
avoiding `b ≠ a`, then every neighbourhood of `a` contains, for all large `n`, a fixed point of `γₙ` on `ℝ̂`
(conjugate `a` to `0`, then `h36q_d_ivt` on a small interval `[-ε, ε]`). -/
theorem h36q_d_fix_near (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ) {a b : ExtPlane} (ha : a ∈ extRealLine)
    (hab : a ≠ b)
    (hA : ∀ K : Set ExtPlane, IsCompact K → b ∉ K → ∀ U ∈ 𝓝 a,
      ∀ᶠ n in atTop, mobiusSL (slRealToComplex (γs n)) '' K ⊆ U)
    {U : Set ExtPlane} (hU : U ∈ 𝓝 a) :
    ∀ᶠ n in atTop, ∃ y ∈ U, y ∈ extRealLine ∧ mobiusSL (slRealToComplex (γs n)) y = y := by
  obtain ⟨h, h0⟩ := h36q_d_exists_base ha
  have hHc : Continuous (mobiusSL (slRealToComplex h)) := k22_t_continuous _
  have hHic : Continuous (mobiusSL (slRealToComplex h⁻¹)) := k22_t_continuous _
  have hHiH : ∀ p, mobiusSL (slRealToComplex h⁻¹) (mobiusSL (slRealToComplex h) p) = p := fun p => by
    rw [k24_slReal_inv, k24_mobiusSL_inv_apply]
  have hHHi : ∀ p, mobiusSL (slRealToComplex h) (mobiusSL (slRealToComplex h⁻¹) p) = p := fun p => by
    rw [k24_slReal_inv, k24_mobiusSL_apply_inv]
  have hV : mobiusSL (slRealToComplex h) ⁻¹' U ∩ {mobiusSL (slRealToComplex h⁻¹) b}ᶜ ∈
      𝓝 ((0 : ℂ) : ExtPlane) := by
    refine inter_mem (hHc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)) ?_
    refine isOpen_compl_singleton.mem_nhds fun h' => hab ?_
    rw [← h0, mem_singleton_iff.1 h', hHHi]
  rw [OnePoint.nhds_coe_eq, mem_map] at hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨ε, hε0, hεδ⟩ : ∃ ε, 0 < ε ∧ ε < δ := ⟨δ / 2, by positivity, by linarith⟩
  have hKV : ∀ t ∈ Icc (-ε) ε, mobiusSL (slRealToComplex h) ((t : ℂ) : ExtPlane) ∈ U ∧
      ((t : ℂ) : ExtPlane) ≠ mobiusSL (slRealToComplex h⁻¹) b := by
    intro t ht
    refine hball ?_
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.2 ⟨ht.1, ht.2⟩
    linarith
  have hKc : IsCompact (((↑) : ℂ → ExtPlane) '' (((↑) : ℝ → ℂ) '' Icc (-ε) ε)) :=
    (isCompact_Icc.image Complex.continuous_ofReal).image OnePoint.continuous_coe
  have hbK : b ∉ mobiusSL (slRealToComplex h) '' (((↑) : ℂ → ExtPlane) '' (((↑) : ℝ → ℂ) '' Icc (-ε) ε)) := by
    rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, htb⟩
    apply (hKV t ht).2
    rw [← htb, hHiH]
  have hU' : mobiusSL (slRealToComplex h⁻¹) ⁻¹' (((↑) : ℂ → ExtPlane) '' ball (0 : ℂ) ε) ∈ 𝓝 a := by
    refine hHic.continuousAt.preimage_mem_nhds ?_
    rw [← h0, hHiH]
    exact (OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball).mem_nhds ⟨0, mem_ball_self hε0, rfl⟩
  filter_upwards [hA _ (hKc.image hHc) hbK _ hU'] with n hn
  have hmv : ∀ p, mobiusSL (slRealToComplex (h⁻¹ * γs n * h)) p =
      mobiusSL (slRealToComplex h⁻¹) (mobiusSL (slRealToComplex (γs n)) (mobiusSL (slRealToComplex h) p)) := by
    intro p
    rw [k24_slReal_mul, k24_slReal_mul, k24_mobiusSL_mul, k24_mobiusSL_mul]
  obtain ⟨t, ht, hft⟩ := h36q_d_ivt (h⁻¹ * γs n * h) hε0 fun t ht => by
    rw [hmv]
    exact hn ⟨_, ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  refine ⟨mobiusSL (slRealToComplex h) ((t : ℂ) : ExtPlane), (hKV t ht).1,
    k24_real_mapsTo_extRealLine h (Or.inl ⟨(t : ℂ), Complex.ofReal_im t, rfl⟩), ?_⟩
  rw [hmv] at hft
  have := congrArg (mobiusSL (slRealToComplex h)) hft
  rwa [hHHi] at this

/-- **C3** [P4, stub] The limit set of a Fuchsian group lies in the closure of the fixed points in `closure ℍ` of its
elements `γ ≠ ±1`.  (A limit point is a limit of `γₙ i`, `γₙ` injective, `i` ordinary by `IsFuchsian`
(`k22_t_limitSet_subset_orbitLim`); a subsequence has attracting/repelling points `a, b ∈ ℝ̂`
(`k22_convergence_real`) and the limit is `a`.  If some `γ ≠ ±1` of `Γ` fixes `a`, done.  Otherwise, for `a ≠ b`,
`γₙ` maps a small arc `J ∋ a` of `ℝ̂` into itself for large `n`, so has a fixed point in `J` (by the intermediate
value theorem); for `a = b` use `γₙ g` with `g a ≠ a`.) -/
theorem h36q_limitSet_subset_closure_fix (hΓ : IsFuchsian Γ) :
    fuchsianLimitSet Γ ⊆ closure {y : ExtPlane | y ∈ closure (toExt upperHalf) ∧
      ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ mobiusSL (slRealToComplex γ) y = y} := by
  intro x hx
  obtain ⟨γs, hinj, hlim⟩ := k22_t_limitSet_subset_orbitLim (k24_c_I_not_mem_limitSet hΓ) hx
  choose γr hγrΓ hγr using fun n => Subgroup.mem_map.1 (γs n).2
  have hγrinj : Function.Injective γr := fun n m h =>
    hinj (Subtype.ext (by rw [← hγr n, ← hγr m, h]))
  have hγs : ∀ n, ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ)) = slRealToComplex (γr n) :=
    fun n => (hγr n).symm
  have hnorm := k24_c_norm_tendsto hΓ (fun n => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ))
    (Subtype.val_injective.comp hinj) (fun n => (γs n).2)
  have hreal : ∀ n (i j : Fin 2), ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) i j).im = 0 := by
    intro n i j
    rw [← hγr n, k24_c_map_apply, Complex.ofReal_im]
  obtain ⟨φ, a, b, hφ, hA, -, haR, hbR⟩ :=
    k22_convergence_real (fun n => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ)) hnorm hreal
  have haR' : a ∈ extRealLine := haR
  have hIb : ((Complex.I : ℂ) : ExtPlane) ≠ b := by
    rintro rfl
    rcases hbR with ⟨z, hz, hzI⟩ | h
    · rw [OnePoint.coe_injective hzI] at hz
      simp at hz
    · exact OnePoint.coe_ne_infty _ h
  have hta : Tendsto (fun n => mobiusSL (γs (φ n)) ((Complex.I : ℂ) : ExtPlane)) atTop (𝓝 a) := by
    rw [tendsto_def]
    intro U hU
    filter_upwards [hA {((Complex.I : ℂ) : ExtPlane)} isCompact_singleton
      (fun h => hIb (mem_singleton_iff.1 h).symm) U hU] with n hn
    exact hn (mem_image_of_mem _ (mem_singleton _))
  rw [tendsto_nhds_unique (hlim.comp hφ.tendsto_atTop) hta, mem_closure_iff_nhds]
  intro U hU
  by_cases hg : ∃ g ∈ Γ, mobiusSL (slRealToComplex g) b ≠ a
  · obtain ⟨g, hgΓ, hgb⟩ := hg
    have hδinj : Function.Injective fun n => γr (φ n) * g⁻¹ := fun m n h =>
      hφ.injective (hγrinj (mul_right_cancel h))
    have hAδ : ∀ K : Set ExtPlane, IsCompact K → mobiusSL (slRealToComplex g) b ∉ K → ∀ V ∈ 𝓝 a,
        ∀ᶠ n in atTop, mobiusSL (slRealToComplex (γr (φ n) * g⁻¹)) '' K ⊆ V := by
      intro K hK hbK V hV
      have hK' : IsCompact (mobiusSL (slRealToComplex g⁻¹) '' K) := hK.image (k22_t_continuous _)
      have hbK' : b ∉ mobiusSL (slRealToComplex g⁻¹) '' K := by
        rintro ⟨k, hk, hkb⟩
        apply hbK
        rw [← hkb, k24_slReal_inv, k24_mobiusSL_apply_inv]
        exact hk
      filter_upwards [hA _ hK' hbK' V hV] with n hn
      have e : mobiusSL (slRealToComplex (γr (φ n) * g⁻¹)) '' K =
          mobiusSL (γs (φ n)) '' (mobiusSL (slRealToComplex g⁻¹) '' K) := by
        rw [← image_comp]
        refine image_congr fun p _ => ?_
        simp only [Function.comp_apply, k24_slReal_mul, k24_mobiusSL_mul, hγs]
      rw [e]
      exact hn
    have hne : ∀ᶠ n in atTop, γr (φ n) * g⁻¹ ≠ 1 ∧ γr (φ n) * g⁻¹ ≠ -1 := by
      have hc := hδinj.tendsto_cofinite
      rw [Nat.cofinite_eq_atTop] at hc
      filter_upwards [hc ((finite_singleton (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)).insert
        1).compl_mem_cofinite] with n hn
      exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
    obtain ⟨n, ⟨y, hyU, hyR, hyfix⟩, hn1, hn2⟩ :=
      ((h36q_d_fix_near _ haR' hgb.symm hAδ hU).and hne).exists
    exact ⟨y, hyU, h36t_extRealLine_subset_closure hyR, _, Γ.mul_mem (hγrΓ _) (Γ.inv_mem hgΓ), hn1, hn2, hyfix⟩
  · simp only [not_exists, not_and, ne_eq, not_not] at hg
    have hb : b = a := by
      have := hg 1 Γ.one_mem
      rwa [k24_slReal_one, k24_mobiusSL_one] at this
    have hc := hγrinj.tendsto_cofinite
    rw [Nat.cofinite_eq_atTop] at hc
    obtain ⟨n, hn⟩ := (show ∀ᶠ n in atTop, γr n ∈ ({1, -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))ᶜ from
      hc ((finite_singleton (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)).insert 1).compl_mem_cofinite).exists
    have hfix := hg _ (hγrΓ n)
    rw [hb] at hfix
    exact ⟨a, mem_of_mem_nhds hU, h36t_extRealLine_subset_closure haR', γr n, hγrΓ n,
      fun h => hn (Or.inl h), fun h => hn (Or.inr h), hfix⟩

/-- §36.1: a quasiconformal map `f : S → S₁` extends to a homeomorphism `S* → S₁*`: its lifts extend
to the closed half-plane and map `b(G)` onto `b(G₁)`.

**Correction.**  The hypotheses `[IsManifold 𝓘(ℂ) ω S]`, `[IsManifold 𝓘(ℂ) ω S₁]` were missing:
without holomorphically compatible charts (`[IsManifold 𝓘(ℂ) ω _]`) `IsQCRS`/`IsKQCRS` and
`IsUniformization` do not control the lift, and the statement was **false** (a copy of `ℍ` charted by the
radial stretches `w ↦ (w - x)|w - x|`, with a Lipschitz self-map having no homeomorphic extension, was a
counterexample). -/
theorem qc_extends_to_border {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [T2Space S] [ConnectedSpace S] [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [T2Space S₁] [ConnectedSpace S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) (f : S ≃ₜ S₁) (hf : IsQCRS f)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p p₁ f F) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F) upperHalf upperHalf G ∧
      G '' ordinarySet Γ = ordinarySet Γ₁ := by
  obtain ⟨G, hG⟩ := h36q_ext_of_lift hp hp₁ hf hF
  exact ⟨G, hG, h36q_ordinarySet_image hp hp₁ hF hG⟩

/-- **Theorem 36.1**: two quasiconformal maps `f₀, f₁ : S → S₁` are homotopic modulo the boundary iff
they have lifts `f̃₀, f̃₁` to the universal covering (self-maps of `ℍ`, resp. `Δ`) with the same
boundary values on `ℝ̂` (resp. `∂Δ`).

**Correction.**  The hypotheses `[IsManifold 𝓘(ℂ) ω S]`, `[IsManifold 𝓘(ℂ) ω S₁]` were missing:
without holomorphically compatible charts (`[IsManifold 𝓘(ℂ) ω _]`) `IsQCRS`/`IsKQCRS` and
`IsUniformization` do not control the lift, and the statement was **false** (a copy of `ℍ` charted by the
radial stretches `w ↦ (w - x)|w - x|`, with a Lipschitz self-map having no homeomorphic extension, was a
counterexample). -/
theorem thm36_1 {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [T2Space S] [ConnectedSpace S]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁] [T2Space S₁] [ConnectedSpace S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) (hΓ : IsFuchsian Γ) (f₀ f₁ : S ≃ₜ S₁)
    (hf₀ : IsQCRS f₀) (hf₁ : IsQCRS f₁) :
    HomotopicModBoundary p p₁ f₀ f₁ ↔
      ∃ (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane) (G₀ G₁ : ExtPlane → ExtPlane),
        IsLift p p₁ f₀ F₀ ∧ IsLift p p₁ f₁ F₁ ∧ IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀ ∧
        IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁ ∧ ∀ x ∈ extRealLine, G₀ x = G₁ x := by
  exact ⟨h36q_mp hp hp₁ f₀ f₁ hf₀ hf₁, h36_thm36_1_mpr hp hp₁ hΓ f₀ f₁ hf₀ hf₁⟩

/-- §36.1 (in the proof of Theorem 36.1): lifts of homotopic maps agree at the fixed points of the
elements of `G` (`F̃(γⁿ(z), t) = γ₁ⁿ ∘ F̃(z, t)`, `n → ∞`), hence on the limit set `Λ(G)`, the closure
of the fixed points.

**Correction.**  The homotopy `H` was arbitrary, and the statement was **false** (a homotopy constant in
space, `H(x, t) = σ(t)`, on `Δ* = ℍ/⟨z ↦ z + 1⟩`); now `H` starts at a homeomorphism `f₀` (`hH₀`) and
`Γ` is Fuchsian. -/
theorem lift_homotopy_agrees_on_limitSet {S S₁ : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {p₁ : UpperHalfPlane → S₁}
    (hp : IsUniformization Γ p) (hp₁ : IsUniformization Γ₁ p₁) (hΓ : IsFuchsian Γ) {f₀ : S ≃ₜ S₁}
    {H : C(S × unitInterval, S₁)} (hH₀ : ∀ x, H (x, 0) = f₀ x)
    {Ht : UpperHalfPlane → unitInterval → UpperHalfPlane} (hH : IsLiftHomotopy p p₁ H Ht)
    {G : ExtPlane → unitInterval → ExtPlane} (hG : Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2))
    (hGH : ∀ (τ : UpperHalfPlane) (t : unitInterval), G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane)) :
    ∀ x ∈ fuchsianLimitSet Γ, ∀ t, G x t = G x 0 := by
  intro x hx
  have hC : IsClosed {y : ExtPlane | ∀ t, G y t = G y 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_eq (hG.comp (continuous_id.prodMk continuous_const))
      (hG.comp (continuous_id.prodMk continuous_const))
  refine closure_minimal (fun y hy => ?_) hC (h36q_limitSet_subset_closure_fix hΓ hx)
  obtain ⟨hyc, γ, hγ, hγ₁, hγ₂, hfix⟩ := hy
  exact fun t => h36q_lh_fix hp hp₁ hH₀ hH hG hGH hγ hγ₁ hγ₂ hyc hfix t

/-- §36.1: the extension of the lifted homotopy to `ℝ̂` by the Poincaré geodesic segments
`t ↦` the point dividing the segment from `f̃₀(z)` to `f̃₁(z)` in the ratio `t : (1 - t)`. -/
theorem geodesic_homotopy_lift {F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₀ G₁ : ExtPlane → ExtPlane}
    (h₀ : IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀)
    (h₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁) (hbd : ∀ x ∈ extRealLine, G₀ x = G₁ x) :
    ∃ Ht : UpperHalfPlane → unitInterval → UpperHalfPlane,
      Continuous (fun x : UpperHalfPlane × unitInterval => Ht x.1 x.2) ∧ (∀ τ, Ht τ 0 = F₀ τ) ∧
      (∀ τ, Ht τ 1 = F₁ τ) ∧ (∀ τ t, dist (F₀ τ) (Ht τ t) = t * dist (F₀ τ) (F₁ τ)) ∧
      ∀ τ t, dist (Ht τ t) (F₁ τ) = (1 - t) * dist (F₀ τ) (F₁ τ) := by
  have _ := h₀
  have _ := h₁
  have _ := hbd
  refine ⟨fun τ t => c36_d_geod (F₀ τ) (F₁ τ) t, ?_, ?_, ?_, ?_, ?_⟩
  · exact c36_d_geod_continuous.comp ((F₀.continuous.comp continuous_fst).prodMk
      ((F₁.continuous.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))
  · intro τ
    refine (dist_eq_zero.1 ?_).symm
    show dist (F₀ τ) (c36_d_geod (F₀ τ) (F₁ τ) ((0 : unitInterval) : ℝ)) = 0
    rw [c36_d_dist_left _ _ (0 : unitInterval).2.1]
    simp
  · intro τ
    refine dist_eq_zero.1 ?_
    show dist (c36_d_geod (F₀ τ) (F₁ τ) ((1 : unitInterval) : ℝ)) (F₁ τ) = 0
    rw [c36_d_dist_right _ _ (1 : unitInterval).2.2]
    simp
  · intro τ t
    exact c36_d_dist_left _ _ t.2.1
  · intro τ t
    exact c36_d_dist_right _ _ t.2.2

/-- The essential supremum of `|μ|` over `ℍ`. -/
def beltramiNormH (μ : ℂ → ℂ) : ℝ :=
  (essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)).toReal

/-- **§36.1 (the Teichmüller extremal problem modulo the boundary).**  In the Fuchsian model: the
maps `S → S₁` homotopic to `f` modulo the boundary correspond to the `G`-compatible Beltrami
coefficients `ν` with `f^ν|ℝ = f^μ|ℝ` (Theorem 36.1); `μ` is extremal in its class if
`‖μ‖_∞ ≤ ‖ν‖_∞` for all such `ν`. -/
def IsExtremalModBoundary (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ : BeltramiGamma Γ) : Prop :=
  ∀ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν μ → beltramiNormH μ.1.1 ≤ beltramiNormH ν.1.1

/-! ### s36c track (coordinator 553e2d), part C: extremal maps modulo the boundary -/

/-! ### S36-C (scout 3): extremal maps exist in every class modulo the boundary -/

/-- An a.e. bound `‖μ‖ ≤ c` on `ℍ` (`c ≥ 0`) bounds `beltramiNormH μ` by `c`. -/
theorem c36_c_normH_le {μ : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ c) : beltramiNormH μ ≤ c := by
  have hle : essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≤ ENNReal.ofReal c := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [h] with z hz
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hz
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal hc] at h2
  exact h2

/-- For `ν ∈ M`, `‖ν‖ ≤ beltramiNormH ν` a.e. on `ℍ` (the essential supremum is finite, bounded by the
`k < 1` of `ν`). -/
theorem c36_c_ae_le_normH (ν : BeltramiH) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν.1 z‖ ≤ beltramiNormH ν.1 := by
  obtain ⟨k, -, -, -, hb⟩ := bg_beltramiH_upper ν
  have hfin : essSup (fun z => (‖ν.1 z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (essSup_le_of_ae_le (ENNReal.ofReal k) ?_)
    filter_upwards [hb] with z hz
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hz
  filter_upwards [ENNReal.ae_le_essSup (fun z => (‖ν.1 z‖₊ : ℝ≥0∞))] with z hz
  rw [beltramiNormH, show ‖ν.1 z‖ = ((‖ν.1 z‖₊ : ℝ≥0∞)).toReal by simp]
  exact (ENNReal.toReal_le_toReal (by simp) hfin).2 hz

/-- `beltramiNormH ν < 1` for `ν ∈ M`. -/
theorem c36_c_normH_lt_one (ν : BeltramiH) : beltramiNormH ν.1 < 1 := by
  obtain ⟨k, hk0, hk1, -, hb⟩ := bg_beltramiH_upper ν
  exact (c36_c_normH_le hk0 hb).trans_lt hk1

/-- For `ν ∈ M` with `beltramiNormH ν ≤ k < 1`, `f^ν` is a normalized `(1 + k)/(1 - k)`-q.c. map of the plane commuting
with `conj`, and `(1 + k)/(1 - k)`-q.c. on `ℍ`. -/
theorem c36_c_fMuSym_spec (ν : BeltramiH) {k : ℝ} (hk1 : k < 1) (hle : beltramiNormH ν.1 ≤ k) :
    IsKQCNormalizedPlane (fMuSym ν.1) ((1 + k) / (1 - k)) ∧
      (∀ z, fMuSym ν.1 (conj z) = conj (fMuSym ν.1 z)) ∧
      IsKQC (fMuSym ν.1) upperHalf ((1 + k) / (1 - k)) := by
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg.trans hle
  obtain ⟨k', -, -, hm, -⟩ := bg_beltramiH_upper ν
  have hμ : IsBeltramiCoeff ν.1 upperHalf k :=
    ⟨hm, (c36_c_ae_le_normH ν).mono fun z hz => hz.trans hle⟩
  obtain ⟨-, hN, hK, -⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨-, -, hsym, hKU, -⟩ := fMuSym_upperHalf hk0 hk1 hμ
  exact ⟨⟨hK, hN.2.1, hN.2.2.1, hN.2.2.2.1⟩, hsym, hKU⟩

/-- **Same Möbius for the whole class.**  If `ν ∼ μ` in `M(G₀)` (`f^ν = f^μ` on `ℝ`) and `f^μ ∘ γ = A ∘ f^μ` on `ℍ`,
then
also `f^ν ∘ γ = A ∘ f^ν` on `ℍ`: DEF gives some `A'` for `ν`; on `ℝ` (off the poles) `A'(f^ν x) = f^ν(γ x) = f^μ(γ x) =
A(f^μ x) = A(f^ν x)`, so `A' = A` at three real points, hence on `ℍ` (the (⇐) half of `chi_eq_iff`, which needs no
density). -/
theorem c36_c_rel_of_equiv {μ ν : BeltramiGamma Γ} (h : teichSetoidGamma Γ ν μ)
    {γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hA : ∀ z ∈ upperHalf, fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym μ.1.1 z)) :
    ∀ z ∈ upperHalf, fMuSym ν.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym ν.1.1 z) := by
  obtain ⟨A₁, h₁⟩ := b33_d_def ν hγ
  obtain ⟨e₁, he₁, hU₁, hsym₁, -, -⟩ := b33_d_sym_facts ν
  obtain ⟨e₂, he₂, -, -, -, -⟩ := b33_d_sym_facts μ
  rw [← he₁] at h₁ ⊢
  rw [← he₂] at hA
  have hR : ∀ x : ℝ, e₁ x = e₂ x := fun x => by rw [he₁, he₂]; exact h x
  have hreal₁ : ∀ t : ℝ, (e₁ t).im = 0 := fun t => by
    have h := hsym₁ t
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have key : ∀ k : ℝ, k ≠ 0 → ∃ u : ℝ, e₁ ((-(γ 1 1 / γ 1 0) + k : ℝ) : ℂ) = u ∧ A₁ 1 0 * u + A₁ 1 1 ≠ 0 ∧
      A 1 0 * u + A 1 1 ≠ 0 ∧
      mobiusFn (A₁ 0 0) (A₁ 0 1) (A₁ 1 0) (A₁ 1 1) (u : ℂ) = mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) u := by
    intro k hk
    have hx := b33_d_nonpole γ hk
    set x : ℝ := -(γ 1 1 / γ 1 0) + k
    obtain ⟨u, hu⟩ : ∃ u : ℝ, e₁ x = u := ⟨_, (b33_d_ofReal_re (hreal₁ x)).symm⟩
    obtain ⟨hA₁, hE₁⟩ := b33_d_ext_real e₁.continuous e₁.injective h₁ hx
    obtain ⟨hA₂, hE₂⟩ := b33_d_ext_real e₂.continuous e₂.injective hA hx
    rw [← hR x, hu] at hA₂ hE₂
    rw [hu] at hA₁ hE₁
    rw [b33_d_mobiusFn_ofReal, hR] at hE₁
    rw [b33_d_mobiusFn_ofReal] at hE₂
    refine ⟨u, hu, by exact_mod_cast hA₁, by exact_mod_cast hA₂, hE₁.symm.trans hE₂⟩
  obtain ⟨u₁, hu₁, a₁, b₁, c₁⟩ := key 1 one_ne_zero
  obtain ⟨u₂, hu₂, a₂, b₂, c₂⟩ := key 2 two_ne_zero
  obtain ⟨u₃, hu₃, a₃, b₃, c₃⟩ := key 3 three_ne_zero
  have hne : ∀ {k l : ℝ} {u v : ℝ}, k ≠ l → e₁ ((-(γ 1 1 / γ 1 0) + k : ℝ) : ℂ) = u →
      e₁ ((-(γ 1 1 / γ 1 0) + l : ℝ) : ℂ) = v → u ≠ v := by
    intro k l u v hkl hu hv huv
    apply hkl
    have h1 := e₁.injective (hu.trans ((congrArg _ huv).trans hv.symm))
    have h2 := ofReal_injective h1
    linarith
  have hEq := b33_d_eqOn_of_three (hne (by norm_num) hu₁ hu₂) (hne (by norm_num) hu₁ hu₃)
    (hne (by norm_num) hu₂ hu₃) (A := A₁) (B := A)
    (by intro t ht; rcases ht with rfl | rfl | rfl <;> assumption)
    (by intro t ht; rcases ht with rfl | rfl | rfl <;> assumption)
    (by intro t ht; rcases ht with rfl | rfl | rfl <;> assumption)
  intro z hz
  have hz₁ : e₁ z ∈ upperHalf := hU₁ ▸ mem_image_of_mem _ hz
  rw [h₁ z hz, hEq _ hz₁]

/-- **Normal-family limit with the subsequence exposed**: normalized `K₀`-q.c. maps `Pₙ` of the plane which are
eventually
`(1 + k')/(1 - k')`-q.c. on `ℍ` for every `k' ∈ (k*, 1)` have a subsequence converging pointwise to a normalized
`K₀`-q.c.
map `P₀` which is `(1 + k')/(1 - k')`-q.c. on `ℍ` for every `k' ∈ (k*, 1)` (as `s35a_limit`, keeping the subsequence).
-/
theorem c36_c_limit {P : ℕ → ℂ → ℂ} {K₀ kstar : ℝ} (hP : ∀ n, IsKQCNormalizedPlane (P n) K₀)
    (hK : ∀ k' : ℝ, kstar < k' → k' < 1 → ∀ᶠ n in atTop, IsKQC (P n) upperHalf ((1 + k') / (1 - k'))) :
    ∃ P₀ : ℂ → ℂ, IsKQCNormalizedPlane P₀ K₀ ∧
      (∃ φ : ℕ → ℕ, ∀ z, Tendsto (fun n => P (φ n) z) atTop (𝓝 (P₀ z))) ∧
      ∀ k' : ℝ, kstar < k' → k' < 1 → IsKQC P₀ upperHalf ((1 + k') / (1 - k')) := by
  obtain ⟨φ, hφ, P₀, hlim⟩ := UniversalTeichmuller.ut2_nf_extract hP
  have hP₀ := UniversalTeichmuller.ut2_nf_limit (fun n => hP (φ n)) hlim
  have hpt : ∀ z, Tendsto (fun n => P (φ n) z) atTop (𝓝 (P₀ z)) := fun z =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)
  refine ⟨P₀, hP₀, ⟨φ, hpt⟩, fun k' hk' hk'1 => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hK k' hk' hk'1)
  have hqc : ∀ n, IsKQC (P (φ (n + N))) upperHalf ((1 + k') / (1 - k')) := fun n =>
    hN _ ((Nat.le_add_left N n).trans (hφ.id_le (n + N)))
  have hlim' : TendstoLocallyUniformly (fun n => P (φ (n + N))) P₀ atTop := fun u hu x => by
    obtain ⟨t, ht, H⟩ := hlim u hu x
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually H⟩
  exact UniversalTeichmuller.ut2_limit_isKQC isOpen_upperHalf hqc hlim'.tendstoLocallyUniformlyOn
    (hP₀.1.2.2.1.2.1.mono (subset_univ _))

/-- §36.1: as in Theorem 35.1, an extremal map exists in every class modulo the boundary. -/
theorem exists_extremal_mod_boundary (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    ∃ μ₀ : BeltramiGamma Γ, teichSetoidGamma Γ μ₀ μ ∧ IsExtremalModBoundary Γ μ₀ := by
  have _hΓ := hΓ
  -- `k* = inf {‖ν‖_∞ : ν ∼ μ}`
  set S : Set ℝ := {t | ∃ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν μ ∧ beltramiNormH ν.1.1 = t}
  have hSne : S.Nonempty := ⟨_, μ, fun _ => rfl, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro t ⟨ν, -, rfl⟩; exact ENNReal.toReal_nonneg⟩
  set kstar : ℝ := sInf S
  have hk0 : 0 ≤ kstar := le_csInf hSne (by rintro t ⟨ν, -, rfl⟩; exact ENNReal.toReal_nonneg)
  have hk1 : kstar < 1 := (csInf_le hSbdd ⟨μ, fun _ => rfl, rfl⟩).trans_lt (c36_c_normH_lt_one μ.1)
  set k₁ : ℝ := (1 + kstar) / 2 with hk₁def
  have hk₁a : kstar < k₁ := by rw [hk₁def]; linarith
  have hk₁b : k₁ < 1 := by rw [hk₁def]; linarith
  -- a minimizing sequence `νₙ ∼ μ` with `‖νₙ‖_∞ < k* + min (1/(n+1)) (k₁ - k*)`
  have hseq : ∀ n : ℕ, ∃ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν μ ∧
      beltramiNormH ν.1.1 < kstar + min (1 / ((n : ℝ) + 1)) (k₁ - kstar) := by
    intro n
    have hε : 0 < min (1 / ((n : ℝ) + 1)) (k₁ - kstar) := lt_min (by positivity) (sub_pos.2 hk₁a)
    obtain ⟨t, ⟨ν, hν, rfl⟩, ht⟩ := Real.lt_sInf_add_pos hSne hε
    exact ⟨ν, hν, ht⟩
  choose νs hνs hlt using hseq
  have hle₁ : ∀ n, beltramiNormH (νs n).1.1 ≤ k₁ := fun n => by
    have := hlt n
    have := min_le_right (1 / ((n : ℝ) + 1)) (k₁ - kstar)
    linarith
  -- the maps `f^{νₙ}`: normalized, uniformly q.c., symmetric, eventually `(1 + k')/(1 - k')`-q.c. on `ℍ`
  have hP : ∀ n, IsKQCNormalizedPlane (fMuSym (νs n).1.1) ((1 + k₁) / (1 - k₁)) := fun n =>
    (c36_c_fMuSym_spec (νs n).1 hk₁b (hle₁ n)).1
  have hPsym : ∀ n z, fMuSym (νs n).1.1 (conj z) = conj (fMuSym (νs n).1.1 z) := fun n =>
    (c36_c_fMuSym_spec (νs n).1 hk₁b (hle₁ n)).2.1
  have hK : ∀ k' : ℝ, kstar < k' → k' < 1 →
      ∀ᶠ n in atTop, IsKQC (fMuSym (νs n).1.1) upperHalf ((1 + k') / (1 - k')) := by
    intro k' hk' hk'1
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hk')
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 := min_le_left (1 / ((n : ℝ) + 1)) (k₁ - kstar)
    have h3 := hlt n
    exact (c36_c_fMuSym_spec (νs n).1 hk'1 (by linarith)).2.2
  -- the limit `P₀`
  obtain ⟨P₀, hP₀, ⟨φ, hpt⟩, hP₀K⟩ := c36_c_limit hP hK
  have hsym : ∀ z, P₀ (conj z) = conj (P₀ z) := fun z =>
    tendsto_nhds_unique (hpt (conj z))
      (((Complex.continuous_conj.tendsto _).comp (hpt z)).congr fun n => (hPsym (φ n) z).symm)
  have hbd : ∀ x : ℝ, P₀ x = fMuSym μ.1.1 x := fun x =>
    tendsto_nhds_unique (hpt x) (tendsto_const_nhds.congr fun n => (hνs (φ n) x).symm)
  -- `ν₀ = 𝟙_ℍ μ_{P₀} ∈ M` with `f^{ν₀} = P₀`
  set ν₀ : BeltramiH := ⟨upperHalf.indicator (complexDilatation P₀), ut_rg_indicator_mem hP₀.1⟩
  have hfix : fMuSym ν₀.1 = P₀ := b33_t_fMuSym_eq_of_conj hP₀.1 hP₀.2.1 hP₀.2.2.1 hP₀.2.2.2 hsym
  have hU : ∀ z ∈ upperHalf, P₀ z ∈ upperHalf := by
    obtain ⟨-, -, -, -, -, -, hU₀, -⟩ := b33_t_fs_spec ν₀
    rw [hfix] at hU₀
    exact fun z hz => hU₀ ▸ mem_image_of_mem _ hz
  -- Γ-compatibility: `P₀ ∘ γ = A ∘ P₀` on `ℍ` with the Möbius `A` of `f^μ`, common to the whole class
  have hrel : ∀ γ ∈ Γ, ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z ∈ upperHalf, fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym μ.1.1 z)) →
      ∀ z ∈ upperHalf, P₀ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (P₀ z) := by
    intro γ hγ A hA z hz
    have hden : (A 1 0 : ℂ) * P₀ z + A 1 1 ≠ 0 := bg2_d_den_ne_zero (b33_d_det A) (hU z hz).ne'
    have hAc : ContinuousAt (mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1)) (P₀ z) := by
      unfold mobiusFn
      exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
    refine tendsto_nhds_unique (hpt _) ?_
    exact (hAc.tendsto.comp (hpt z)).congr fun n => (c36_c_rel_of_equiv (hνs (φ n)) hγ hA z hz).symm
  have hcompat : IsGammaCompatible Γ ν₀.1 := fun γ hγ => by
    obtain ⟨A, hA⟩ := b33_d_def μ hγ
    exact b33_t_compat_of_conj hP₀.1 hU (hrel γ hγ A hA)
  set μ₀ : BeltramiGamma Γ := ⟨ν₀, hcompat⟩
  have hcls : teichSetoidGamma Γ μ₀ μ := fun x => by
    show fMuSym ν₀.1 x = fMuSym μ.1.1 x
    rw [hfix]
    exact hbd x
  refine ⟨μ₀, hcls, fun ν hν => ?_⟩
  -- `‖μ₀‖_∞ ≤ k* ≤ ‖ν‖_∞`
  have hνμ : teichSetoidGamma Γ ν μ := fun x => (hν x).trans (hcls x)
  refine le_trans ?_ (csInf_le hSbdd ⟨ν, hνμ, rfl⟩)
  refine le_of_forall_gt_imp_ge_of_dense fun k' hk' => ?_
  rcases lt_or_ge k' 1 with hk'1 | hk'1
  · -- `P₀` is `(1 + k')/(1 - k')`-q.c. on `ℍ`, so `‖μ_{P₀}‖ ≤ k'` a.e. there
    have hb := (isKQC_maxDilatation_le (hP₀K k' hk' hk'1)).2
    have hk'0 : 0 < 1 - k' := by linarith
    have heq : ((1 + k') / (1 - k') - 1) / ((1 + k') / (1 - k') + 1) = k' := by
      field_simp
      ring
    refine c36_c_normH_le (hk0.trans hk'.le) ?_
    filter_upwards [hb, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzU
    show ‖upperHalf.indicator (complexDilatation P₀) z‖ ≤ k'
    rw [indicator_of_mem hzU, ← heq]
    exact hz
  · exact (c36_c_normH_lt_one ν₀).le.trans hk'1

/-! ## §36.2 Hamilton's theorem and its corollaries -/

/-- `F ⊆ ℍ` is a measurable fundamental domain of `Γ`.

**Correction.**  The condition `volume (F \ interior F) = 0` was missing: `F` could have empty interior
(`F = {z ∈ ℍ | Re z ∉ ℚ}` for `⟨z ↦ z + √2⟩`, on which every `φ` has `∬_F |φ| = 0`) or a boundary of
positive measure counted twice, and Theorem 36.2, Lemma 36.2 and their consequences were **false**. -/
def IsFundamentalDomainH (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) : Prop :=
  F ⊆ upperHalf ∧ MeasurableSet F ∧ (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
    (∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F → (τ₂ : ℂ) ∈ interior F →
      (∃ γ ∈ Γ, γ • τ₁ = τ₂) → τ₁ = τ₂) ∧
    volume (F \ interior F) = 0

/-- §36.2: `A(S) = {ω ∈ Q(S) : ‖ω‖ < ∞}`, the integrable holomorphic quadratic differentials, lifted
to `ℍ`: `G`-automorphic holomorphic `φ` on `ℍ` with `∬_F |φ| < ∞` over a fundamental domain `F`. -/
def integrableAutomorphicQD (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ upperHalf ∧ phiArea φ F < ⊤ ∧
    ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z}

/-- The pairing `∫_S κω = ∬_F κφ dx dy`. -/
def beltramiPairing (F : Set ℂ) (κ φ : ℂ → ℂ) : ℂ := ∫ z in F, κ z * φ z

/-- §36.2: `‖P_κ‖ = sup_{‖ω‖ = 1} |∫_S κω|`, the norm of the linear functional `ω ↦ ∫_S κω` on `A(S)`. -/
def hamiltonNorm (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) (κ : ℂ → ℂ) : ℝ :=
  ⨆ (φ : ℂ → ℂ) (_ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1), ‖beltramiPairing F κ φ‖

/-- The zero set of a holomorphic function on `ℍ` which is not identically zero is discrete, hence
countable, hence null: `φ ≠ 0` almost everywhere on every measurable `F ⊆ ℍ`. -/
theorem ae_ne_zero_of_differentiableOn_upperHalf {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hne : ¬ EqOn φ 0 upperHalf) {F : Set ℂ} (hF : F ⊆ upperHalf) (hFm : MeasurableSet F) :
    ∀ᵐ z ∂(volume.restrict F), φ z ≠ 0 := by
  have ha : AnalyticOnNhd ℂ φ upperHalf := hφ.analyticOnNhd isOpen_upperHalf
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isConnected_upperHalf.isPreconnected with
    h | h
  · exact absurd h hne
  · have hmem : {x | φ x ≠ 0} ∈ codiscreteWithin upperHalf := h
    rw [mem_codiscreteWithin] at hmem
    -- the zero set `ℍ ∖ {φ ≠ 0}` is discrete, hence countable (`ℂ` is second countable), hence null
    have hdisc : IsDiscrete (upperHalf \ {x | φ x ≠ 0}) := by
      rw [isDiscrete_iff_nhdsNE]
      intro x hx
      exact disjoint_iff.1 (hmem x hx.1)
    have hcount : (upperHalf \ {x | φ x ≠ 0}).Countable :=
      (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
    have hnull : volume (upperHalf \ {x | φ x ≠ 0}) = 0 := hcount.measure_zero volume
    rw [ae_restrict_iff' hFm]
    filter_upwards [compl_mem_ae_iff.2 hnull] with z hz hzF hφz
    exact hz ⟨hF hzF, fun h' => h' hφz⟩

/-- §36.2: `∫_S κω = ‖κ‖_∞` with `‖ω‖ = 1` forces `κ = ‖κ‖_∞ ω̄/|ω|` a.e. -/
theorem pairing_eq_norm_imp_teichmuller {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1)
    (heq : beltramiPairing F μ.1.1 φ = beltramiNormH μ.1.1) :
    ∀ᵐ z ∂(volume.restrict F), μ.1.1 z = beltramiNormH μ.1.1 * conj (φ z) / ‖φ z‖ := by
  obtain ⟨hFH, hFm, -, -⟩ := hF
  obtain ⟨hφd, -, -⟩ := hφ
  obtain ⟨⟨k, -, -, hκmeas, hκbd⟩, -⟩ := μ.1.2
  set κ : ℂ → ℂ := μ.1.1 with hκ
  set N : ℝ := beltramiNormH κ with hN
  rw [Measure.restrict_univ] at hκmeas hκbd
  -- the essential supremum is finite and bounds `κ` a.e. on `ℍ`, hence a.e. on `F ⊆ ℍ`
  have hEfin : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := k)) (essSup_le_of_ae_le _ ?_)
    filter_upwards [ae_restrict_of_ae hκbd] with z hz
    calc (‖κ z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖κ z‖ := by rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal k := ENNReal.ofReal_le_ofReal hz
  have hbdH : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ N := by
    filter_upwards [ENNReal.ae_le_essSup (fun z => (‖κ z‖₊ : ℝ≥0∞))
      (μ := volume.restrict upperHalf)] with z hz
    have := ENNReal.toReal_mono hEfin hz
    rw [ENNReal.coe_toReal, coe_nnnorm] at this
    exact this
  have hbdF : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ N := ae_restrict_of_ae_restrict_of_subset hFH hbdH
  -- integrability of `φ` and of `κ φ` on `F`
  have hφmeas : AEStronglyMeasurable φ (volume.restrict F) :=
    (hφd.continuousOn.mono hFH).aestronglyMeasurable hFm
  have hφint : IntegrableOn φ F := by
    refine ⟨hφmeas, ?_⟩
    have h1 : (∫⁻ z in F, ‖φ z‖ₑ) = phiArea φ F := by
      unfold phiArea
      simp_rw [ofReal_norm]
    show (∫⁻ z in F, ‖φ z‖ₑ) < ⊤
    rw [h1, hn]
    exact ENNReal.one_lt_top
  have hκmeasF : AEStronglyMeasurable κ (volume.restrict F) :=
    hκmeas.mono_measure Measure.restrict_le_self
  have hκφint : Integrable (fun z => κ z * φ z) (volume.restrict F) := hφint.bdd_mul hκmeasF hbdF
  have hreint : Integrable (fun z => (κ z * φ z).re) (volume.restrict F) := by
    simpa only [RCLike.re_to_complex] using hκφint.re
  -- `∫_F Re(κφ) = N` and `∫_F |φ| = 1`
  have hre : ∫ z in F, (κ z * φ z).re = N := by
    have h1 := integral_re hκφint
    simp only [RCLike.re_to_complex] at h1
    rw [h1]
    change (beltramiPairing F κ φ).re = N
    rw [heq, Complex.ofReal_re]
  have hnorm1 : ∫ z in F, ‖φ z‖ = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => norm_nonneg _) hφmeas.norm]
    have h1 : (∫⁻ z in F, ENNReal.ofReal ‖φ z‖) = 1 := hn
    rw [h1, ENNReal.toReal_one]
  -- the nonnegative integrand `N|φ| − Re(κφ)` has integral `0`, hence vanishes a.e. on `F`
  have hint : Integrable (fun z => N * ‖φ z‖ - (κ z * φ z).re) (volume.restrict F) :=
    (hφint.norm.const_mul N).sub hreint
  have hnonneg : 0 ≤ᵐ[volume.restrict F] fun z => N * ‖φ z‖ - (κ z * φ z).re := by
    filter_upwards [hbdF] with z hz
    have h1 : (κ z * φ z).re ≤ ‖κ z * φ z‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [norm_mul] at h1
    have h2 : ‖κ z‖ * ‖φ z‖ ≤ N * ‖φ z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    simp only [Pi.zero_apply]
    linarith
  have hzero : ∫ z in F, (N * ‖φ z‖ - (κ z * φ z).re) = 0 := by
    rw [integral_sub (hφint.norm.const_mul N) hreint, integral_const_mul, hnorm1, hre]
    ring
  have hae : (fun z => N * ‖φ z‖ - (κ z * φ z).re) =ᵐ[volume.restrict F] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hzero
  -- the zero set of `φ` is null: `φ` is holomorphic on `ℍ` and not identically zero (`∫_F |φ| = 1`)
  have hne : ∀ᵐ z ∂(volume.restrict F), φ z ≠ 0 := by
    refine ae_ne_zero_of_differentiableOn_upperHalf hφd ?_ hFH hFm
    intro h0
    have h1 : phiArea φ F = 0 := by
      unfold phiArea
      have h2 : (∫⁻ z in F, ENNReal.ofReal ‖φ z‖) = ∫⁻ z in F, (0 : ℝ≥0∞) :=
        setLIntegral_congr_fun hFm fun z hz => by rw [h0 (hFH hz)]; simp
      rw [h2, lintegral_zero]
    rw [h1] at hn
    exact zero_ne_one hn
  filter_upwards [hbdF, hae, hne] with z hz1 hz2 hz3
  simp only [Pi.zero_apply] at hz2
  -- `Re(κφ) = N|φ| ≥ |κφ| ≥ Re(κφ)`, so `κφ = N|φ|` as a complex number
  have h1 : (κ z * φ z).re ≤ ‖κ z * φ z‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : ‖κ z * φ z‖ ≤ N * ‖φ z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz1 (norm_nonneg _)
  have h3 : (κ z * φ z).re = ‖κ z * φ z‖ := le_antisymm h1 (by linarith)
  have h4 : κ z * φ z = ((N * ‖φ z‖ : ℝ) : ℂ) := by
    obtain ⟨-, him⟩ := Complex.nonneg_iff.1 (Complex.re_eq_norm.1 h3)
    apply Complex.ext
    · rw [Complex.ofReal_re]
      linarith
    · rw [Complex.ofReal_im]
      exact him.symm
  -- divide by `φ z ≠ 0`
  have hφz : (‖φ z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz3
  rw [eq_div_iff hφz]
  apply mul_right_cancel₀ hz3
  have hc : φ z * conj (φ z) = (‖φ z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  push_cast at h4
  linear_combination (‖φ z‖ : ℂ) * h4 - (N : ℂ) * hc

/-! ## §36.3 The proof of Hamilton's theorem -/

/-- §36.3: `M ⊆ B*` is a `C¹` submanifold at `x` with tangent space `T`: every tangent vector
`y ∈ T` is the velocity at `0` of a `C¹` path in `M` through `x`. -/
def IsC1SubmanifoldAt {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (M : Set (B →L[𝕜] 𝕜)) (x : B →L[𝕜] 𝕜) (T : Submodule 𝕜 (B →L[𝕜] 𝕜)) : Prop :=
  ∀ y ∈ T, ∃ (α : ℝ → B →L[𝕜] 𝕜) (δ : ℝ), 0 < δ ∧ (∀ t ∈ Ioo (-δ) δ, α t ∈ M) ∧ α 0 = x ∧
    HasDerivAt α y 0

/-! ### s36c track (coordinator 553e2d), part A: Lemma 36.1 (Hahn–Banach and convexity of the norm) -/

/-- Lemma 36.1 helper: a path `α : ℝ → F` with `α'(0) = v` admits arbitrarily small positive times
`0 < t < min δ 1` at which the first-order Taylor estimate `‖α t - (α 0 + t • v)‖ ≤ ε t` holds. -/
theorem c36_a_exists_pos_small {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ → F} {v : F} (hα : HasDerivAt α v 0) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ t < 1 ∧ ‖α t - (α 0 + t • v)‖ ≤ ε * t := by
  have h1 := hα.isLittleO.def hε
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖α t - α 0 - (t - 0) • v‖ ≤ ε * ‖t - 0‖ :=
    nhdsWithin_le_nhds h1
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have h5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht2, ht3, ht4, ht5⟩ := (h2.and (h3.and (h4.and h5))).exists
  refine ⟨t, ht5, ht3, ht4, ?_⟩
  have e : α t - (α 0 + t • v) = α t - α 0 - (t - 0) • v := by rw [sub_zero, sub_sub]
  rw [e]
  simpa [Real.norm_eq_abs, abs_of_pos ht5] using ht2

/-- Lemma 36.1 helper (convexity of the norm, downward): for `0 ≤ t ≤ 1`,
`‖x - t • y‖ ≤ (1 - t) ‖x‖ + t ‖x - y‖`, since `x - t • y = (1 - t) • x + t • (x - y)`. -/
theorem c36_a_norm_sub_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x y : F) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖x - t • y‖ ≤ (1 - t) * ‖x‖ + t * ‖x - y‖ := by
  have e : x - t • y = (1 - t) • x + t • (x - y) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  rw [e]
  calc ‖(1 - t) • x + t • (x - y)‖ ≤ ‖(1 - t) • x‖ + ‖t • (x - y)‖ := norm_add_le _ _
    _ = (1 - t) * ‖x‖ + t * ‖x - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0,
        abs_of_nonneg (by linarith)]

/-- Lemma 36.1 helper (convexity of the norm, upward): for `0 ≤ t`,
`(1 + t) ‖x‖ ≤ ‖x + t • y‖ + t ‖x - y‖`, since `(1 + t) • x = (x + t • y) + t • (x - y)`. -/
theorem c36_a_norm_add_smul_ge {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x y : F) {t : ℝ} (ht0 : 0 ≤ t) :
    (1 + t) * ‖x‖ ≤ ‖x + t • y‖ + t * ‖x - y‖ := by
  have e : (1 + t) • x = (x + t • y) + t • (x - y) := by
    rw [add_smul, one_smul, smul_sub]; abel
  calc (1 + t) * ‖x‖ = ‖(1 + t) • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ = ‖(x + t • y) + t • (x - y)‖ := by rw [e]
    _ ≤ ‖x + t • y‖ + ‖t • (x - y)‖ := norm_add_le _ _
    _ = ‖x + t • y‖ + t * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]

/-- **Lemma 36.1**: let `B` be a Banach space, `M ⊆ B*` a `C¹` submanifold of its dual, and suppose
the dual norm attains its minimum or maximum on `M` at `x ∈ M`.  If `A ⊆ B` is a closed subspace
such that the tangent space `T_x M` is the annihilator of `A` (it annihilates `A`, and every functional
vanishing on `A` is tangent), then `‖x|_A‖ = ‖x‖`.

**Correction.**  The hypothesis `hann` (`A^⊥ ⊆ T`) was missing, and with only `T ⊆ A^⊥` the statement
was **false**: `M = {x}`, `x ≠ 0`, `T = ⊥` (the tangent space of a point), `A = ⊥` satisfy every other
hypothesis, but `‖x|_⊥‖ = 0`.  In Hamilton's theorem the lemma is applied with `T₀N = A(S)^⊥`
(Lemma 36.2, part 4), i.e. with equality. -/
theorem lemma36_1 {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]
    {M : Set (B →L[𝕜] 𝕜)} {x : B →L[𝕜] 𝕜} (hx : x ∈ M) {T : Submodule 𝕜 (B →L[𝕜] 𝕜)}
    (hM : IsC1SubmanifoldAt M x T) (hext : (∀ y ∈ M, ‖x‖ ≤ ‖y‖) ∨ ∀ y ∈ M, ‖y‖ ≤ ‖x‖)
    {A : Submodule 𝕜 B} (hA : IsClosed (A : Set B)) (hperp : ∀ y ∈ T, ∀ a ∈ A, y a = 0)
    (hann : ∀ y : B →L[𝕜] 𝕜, (∀ a ∈ A, y a = 0) → y ∈ T) :
    ‖x.comp A.subtypeL‖ = ‖x‖ := by
  have _ := hx
  have _ := hA
  have _ := hperp
  -- Hahn–Banach: extend `x|_A` to `g` with `‖g‖ = ‖x|_A‖`
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq A (x.comp A.subtypeL)
  -- `y := x - g` annihilates `A`, hence is tangent
  have hyA : ∀ a ∈ A, (x - g) a = 0 := by
    intro a ha
    have h := hg ⟨a, ha⟩
    rw [sub_apply, h]
    simp
  have hyT : x - g ∈ T := hann (x - g) hyA
  have hxy : ‖x - (x - g)‖ = ‖x.comp A.subtypeL‖ := by rw [sub_sub_cancel, hgn]
  have hle : ‖x.comp A.subtypeL‖ ≤ ‖x‖ := by
    calc ‖x.comp A.subtypeL‖ ≤ ‖x‖ * ‖A.subtypeL‖ := x.opNorm_comp_le _
      _ ≤ ‖x‖ * 1 := by gcongr; exact Submodule.norm_subtypeL_le A
      _ = ‖x‖ := mul_one _
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hc : 0 < ‖x‖ - ‖x.comp A.subtypeL‖ := sub_pos.2 hlt
  rcases hext with hmin | hmax
  · -- minimum: move along `-y`
    obtain ⟨α, δ, hδ, hαM, hα0, hα⟩ := hM (-(x - g)) (T.neg_mem hyT)
    obtain ⟨t, ht0, htδ, ht1, hest⟩ := c36_a_exists_pos_small hα (half_pos hc) hδ
    have h1 := hmin _ (hαM t ⟨by linarith, htδ⟩)
    rw [hα0, smul_neg, ← sub_eq_add_neg] at hest
    have h2 := c36_a_norm_sub_smul_le x (x - g) ht0.le ht1.le
    rw [hxy] at h2
    have h3 : ‖α t‖ ≤ ‖α t - (x - t • (x - g))‖ + ‖x - t • (x - g)‖ := by
      calc ‖α t‖ = ‖(α t - (x - t • (x - g))) + (x - t • (x - g))‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    nlinarith
  · -- maximum: move along `+y`
    obtain ⟨α, δ, hδ, hαM, hα0, hα⟩ := hM (x - g) hyT
    obtain ⟨t, ht0, htδ, ht1, hest⟩ := c36_a_exists_pos_small hα (half_pos hc) hδ
    have h1 := hmax _ (hαM t ⟨by linarith, htδ⟩)
    rw [hα0] at hest
    have h2 := c36_a_norm_add_smul_ge x (x - g) ht0.le
    rw [hxy] at h2
    have h3 : ‖x + t • (x - g)‖ ≤ ‖α t‖ + ‖α t - (x + t • (x - g))‖ := by
      calc ‖x + t • (x - g)‖ = ‖α t - (α t - (x + t • (x - g)))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    nlinarith

/-- §36.3: in a Hilbert space, if the restriction of the functional `⟪x, ·⟫` to a closed subspace
`A` has the same norm as `x`, then `x ∈ A`.

This is the book's own step, "由 `‖x|_A‖ = ‖x‖` 推出 `x ∈ A`".  Proof: represent the restricted
functional by some `v ∈ A` (Riesz on `A`, which is complete because it is closed); then
`⟪v, a⟫ = ⟪x, a⟫` for every `a ∈ A` and `‖v‖ = ‖x‖`, so taking `a = v` gives
`⟪x, v⟫ = ‖v‖²` and hence `‖x - v‖² = ‖x‖² - 2‖v‖² + ‖v‖² = 0`. -/
theorem mem_of_norm_comp_subtypeL_eq {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] {x : B} {A : Submodule ℝ B} (hA : IsClosed (A : Set B))
    (h : ‖(InnerProductSpace.toDual ℝ B x).comp A.subtypeL‖ = ‖x‖) : x ∈ A := by
  haveI : CompleteSpace A := completeSpace_coe_iff_isComplete.2 hA.isComplete
  set φ : StrongDual ℝ A := (InnerProductSpace.toDual ℝ B x).comp A.subtypeL with hφ
  set v : A := (InnerProductSpace.toDual ℝ A).symm φ with hv
  have hvnorm : ‖(v : B)‖ = ‖x‖ := by
    have h1 : ‖v‖ = ‖φ‖ := by
      rw [hv]
      exact (InnerProductSpace.toDual ℝ A).symm.norm_map φ
    rw [show ‖(v : B)‖ = ‖v‖ from rfl, h1, hφ, h]
  have hvip : ∀ a : A, inner ℝ (v : B) (a : B) = inner ℝ x (a : B) := by
    intro a
    have h2 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := A) (x := a) (y := φ)
    rw [← hv] at h2
    rw [← Submodule.coe_inner]
    exact h2
  have hxv : inner ℝ x (v : B) = ‖(v : B)‖ ^ 2 := by
    rw [← hvip v, real_inner_self_eq_norm_sq]
  have hzero : ‖x - (v : B)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hxv, hvnorm]
    ring
  have hxeq : x = (v : B) := by
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hzero
    rwa [norm_eq_zero, sub_eq_zero] at h3
  rw [hxeq]
  exact v.2

/-- §36.3: in a Hilbert space the conclusion of Lemma 36.1 means that `x ⊥ T_x M`.

The book: "如果在引理36.1中进一步假定B是Hilbert空间，那么立即推出大家熟知的结果：即这时的x垂直于M
在x的切空间.事实上，由 `‖x|_A‖ = ‖x‖` 推出 `x ∈ A`".  So `A` is the *same* closed subspace that
Lemma 36.1 is applied to, and the tangent space annihilating `A` then gives `x ⊥ T` at once.

**Correction.**  This previously took the norm equality as a hypothesis quantified over **all**
closed `A` annihilated by `T`, and in that form it was **vacuous**: `A = ⊥` is closed, the side
condition `∀ y ∈ T, ∀ a ∈ ⊥, ⟪y, a⟫ = 0` holds trivially for every `T`, and the restricted
functional lives on the zero space, so the hypothesis instantiated at `⊥` reads `0 = ‖x‖` and
forces `x = 0` outright.  The statement was therefore true but said only "if `x = 0` then
`x ⊥ T`", capturing none of the intended content; proving it would have retired a `sorry` and
encoded nothing.  The book quantifies `A` nowhere — it is the subspace fixed by Lemma 36.1, whose
own statement (`lemma36_1`) takes `A` as a parameter and concludes about that same `A` — so `A` is
now a parameter here too, with the annihilation hypothesis it carries in the book. -/
theorem lemma36_1_hilbert {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    {x : B} {T A : Submodule ℝ B} (hA : IsClosed (A : Set B))
    (hperp : ∀ y ∈ T, ∀ a ∈ A, inner ℝ y a = 0)
    (h : ‖(InnerProductSpace.toDual ℝ B x).comp A.subtypeL‖ = ‖x‖) :
    ∀ y ∈ T, inner ℝ x y = 0 := by
  have hxA : x ∈ A := mem_of_norm_comp_subtypeL_eq hA h
  intro y hy
  rw [← real_inner_comm]
  exact hperp y hy x hxA

/-- §36.3: the normalized quasiconformal map `f_μ` for `μ ∈ M(ℍ, G)`: dilatation `μ` in `ℍ`,
conformal in `𝕃`, and `f_μ(z) = z + O(|z|⁻¹)` at `∞` is the normalization of the book (for the disc);
here we use the normalization `f_μ(0) = 0`, `f_μ(1) = 1`, `f_μ(∞) = ∞` of §21, which changes `φ_μ` by
nothing (the Schwarzian derivative is Möbius invariant). -/
theorem bersFunction_normalization_independent (μ : BeltramiH) {f : ℂ → ℂ} (hf : IsQuasiconformal f univ)
    (hfs : f '' univ = univ) (hμ : ∀ᵐ z, complexDilatation f z = μ.1 z) :
    EqOn (schwarzian f) (bersFunction μ.1) lowerHalf := by
  obtain ⟨K, hK⟩ := hf
  have hN := bg2_normalize μ hK hfs hμ
  have ha : f 1 - f 0 ≠ 0 := fun h =>
    one_ne_zero (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  have hfeq : f = fun w => ((f 1 - f 0) * normalizedSolution μ.1 w + f 0) /
      (0 * normalizedSolution μ.1 w + 1) := by
    funext w
    rw [hN w, zero_mul, zero_add, div_one, mul_div_assoc', mul_div_cancel_left₀ _ ha]
    ring
  intro z hz
  have hloc := isLocUnivMero_of_isConformalOnto isOpen_lowerHalf (ut_conformal_lowerHalf μ)
  rw [bersFunction, indicator_of_mem hz, hfeq]
  exact schwarzian_mobius_comp hloc (by simpa using ha) hz

/-- §36.3: the derivative `P(μ)(z) = -(6/π) ∬_ℍ μ(ζ)/(ζ - z)⁴ dξ dη` (`z ∈ 𝕃`) of the Bers map
`Φ : μ ↦ φ_μ = S_{f_μ}|𝕃` at `μ = 0` (from the representation `f_{tμ}(z) = z + t σ₁(z) + …`,
`σ₁ = V(μ)` the normalized transform `normalizedCauchyTOn`, `S_{f_{tμ}} = t σ₁''' + o(t)`). -/
def bersDerivative (μ : ℂ → ℂ) (z : ℂ) : ℂ := -(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - z) ^ 4

/-- §36.3: the normalized Cauchy transform
`V(μ)(z) = -(z(z - 1)/π) ∬_D μ(ζ)/(ζ(ζ - 1)(ζ - z)) dξ dη`, the first variation `f_{tμ}(z) = z + t V(μ)(z) + o(t)`
of the maps fixing `0, 1, ∞` (Ahlfors).  For bounded `μ` the integral converges absolutely for every `z` (the
kernel is `O(|ζ|⁻³)` at `∞`), whereas the plain `T(μ) = cauchyTOn D μ` diverges for bounded `μ` on `D = ℍ`.
Since `z(z - 1)/(ζ(ζ - 1)(ζ - z)) = 1/(ζ - z) - (z + ζ - 1)/(ζ(ζ - 1))`, `V(μ)` differs from `T(μ)` by a term
linear in `z` whenever both converge. -/
def normalizedCauchyTOn (D : Set ℂ) (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(z * (z - 1) / π : ℂ) * ∫ ζ in D, μ ζ / (ζ * (ζ - 1) * (ζ - z))

/-! ### s36b track (coordinator 553e2d), part P: `bersDerivative` is `V(μ)'''` (differentiation under the integral) -/

/-- Points of `ball w₀ (-Im w₀ / 2)` (`Im w₀ < 0`) satisfy `Im w ≤ -(-Im w₀ / 2)` and `‖w‖ ≤ 2 ‖w₀‖`. -/
theorem b36_p_ball {w₀ w : ℂ} (hw₀ : w₀.im < 0) (hw : w ∈ ball w₀ (-w₀.im / 2)) :
    w.im ≤ -(-w₀.im / 2) ∧ ‖w‖ ≤ 2 * ‖w₀‖ := by
  rw [mem_ball, dist_eq_norm] at hw
  have h1 : |(w - w₀).im| ≤ ‖w - w₀‖ := abs_im_le_norm _
  rw [sub_im] at h1
  have h1' := (abs_le.1 h1).2
  have h2 : |w₀.im| ≤ ‖w₀‖ := abs_im_le_norm _
  rw [abs_of_neg hw₀] at h2
  have h3 : ‖w‖ ≤ ‖w₀‖ + ‖w - w₀‖ := by
    have := norm_add_le w₀ (w - w₀)
    rwa [add_sub_cancel] at this
  constructor
  · linarith
  · linarith

/-- Separation of `ℍ` from the points `w` with `Im w ≤ -δ`, `‖w‖ ≤ R`:
`δ (1 + ‖ζ‖) ≤ (1 + R + δ) ‖ζ - w‖` for `ζ ∈ ℍ`. -/
theorem b36_p_sep {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ.im) (hw : w.im ≤ -δ) (hwR : ‖w‖ ≤ R) :
    δ * (1 + ‖ζ‖) ≤ (1 + R + δ) * ‖ζ - w‖ := by
  have h1 : δ ≤ ‖ζ - w‖ := by
    have e1 := abs_im_le_norm (ζ - w)
    rw [sub_im] at e1
    have e2 := le_abs_self (ζ.im - w.im)
    linarith
  have h2 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
  have e1 : δ * ‖ζ‖ ≤ δ * (‖ζ - w‖ + R) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have e2 : δ * (1 + R) ≤ ‖ζ - w‖ * (1 + R) :=
    mul_le_mul_of_nonneg_right h1 (by linarith [(norm_nonneg w).trans hwR])
  nlinarith

/-- `‖(ζ - w)⁻¹‖ ≤ A (1 + ‖ζ‖)⁻¹` with `A = (1 + R + δ)/δ`, for `ζ ∈ ℍ`, `Im w ≤ -δ`, `‖w‖ ≤ R`. -/
theorem b36_p_inv_le {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ.im) (hw : w.im ≤ -δ) (hwR : ‖w‖ ≤ R) :
    ‖(ζ - w)⁻¹‖ ≤ (1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹ := by
  have hs := b36_p_sep hδ hζ hw hwR
  have hpos : 0 < ‖ζ - w‖ := by
    have e1 := abs_im_le_norm (ζ - w)
    rw [sub_im] at e1
    have e2 := le_abs_self (ζ.im - w.im)
    linarith
  have hs1 : 0 < 1 + ‖ζ‖ := by positivity
  have key : (1 + ‖ζ‖) * ‖ζ - w‖⁻¹ ≤ (1 + R + δ) / δ := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos hδ]
    linarith
  rw [norm_inv]
  calc ‖ζ - w‖⁻¹ = (1 + ‖ζ‖)⁻¹ * ((1 + ‖ζ‖) * ‖ζ - w‖⁻¹) := by field_simp
    _ ≤ (1 + ‖ζ‖)⁻¹ * ((1 + R + δ) / δ) := by gcongr
    _ = _ := by ring

/-- The cube bound `‖((ζ - w)³)⁻¹‖ ≤ A³ ((1 + ‖ζ‖)³)⁻¹`. -/
theorem b36_p_inv_pow3_le {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ.im) (hw : w.im ≤ -δ)
    (hwR : ‖w‖ ≤ R) :
    ‖((ζ - w) ^ 3)⁻¹‖ ≤ ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have h := b36_p_inv_le hδ hζ hw hwR
  rw [← inv_pow, norm_pow, ← inv_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 3

/-- The fourth-power bound `‖((ζ - w)⁴)⁻¹‖ ≤ A⁴ ((1 + ‖ζ‖)³)⁻¹` (using `(1 + ‖ζ‖)⁻¹ ≤ 1`). -/
theorem b36_p_inv_pow4_le {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ.im) (hw : w.im ≤ -δ)
    (hwR : ‖w‖ ≤ R) :
    ‖((ζ - w) ^ 4)⁻¹‖ ≤ ((1 + R + δ) / δ) ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have h := b36_p_inv_le hδ hζ hw hwR
  have hs1 : 0 < 1 + ‖ζ‖ := by positivity
  have hi0 : 0 ≤ (1 + ‖ζ‖)⁻¹ := by positivity
  have hi1 : (1 + ‖ζ‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg ζ])
  have hA : 0 ≤ (1 + R + δ) / δ := by
    have : 0 ≤ R := (norm_nonneg w).trans hwR
    positivity
  rw [← inv_pow, norm_pow]
  calc ‖(ζ - w)⁻¹‖ ^ 4 ≤ ((1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) h 4
    _ = ((1 + R + δ) / δ) ^ 4 * (1 + ‖ζ‖)⁻¹ ^ 4 := by rw [mul_pow]
    _ ≤ ((1 + R + δ) / δ) ^ 4 * (1 + ‖ζ‖)⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi0 hi1 (by norm_num)) (by positivity)
    _ = ((1 + R + δ) / δ) ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by rw [inv_pow]

/-- The integrable profile `((1 + ‖ζ‖)³)⁻¹` on `ℂ` (`integrable_one_add_norm`, `dim_ℝ ℂ = 2 < 3`). -/
theorem b36_p_profile_integrable : Integrable (fun ζ : ℂ => ((1 + ‖ζ‖) ^ 3)⁻¹) := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine h.congr (Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(3 : ℝ)) = ((1 + ‖ζ‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/-- The `w`-independent part of the first derivative of the kernel: the difference of the
`1/(ζ - w)²`-part at `w` and at a fixed pair `a, b`, written as three triple products,
`1/(ζ-w)² - 1/((ζ-a)(ζ-b)) = O(|ζ|⁻³)` uniformly: `≤ 6 R A³ ((1 + ‖ζ‖)³)⁻¹`. -/
theorem b36_p_E_le {ζ w a b : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ.im) (hw : w.im ≤ -δ)
    (hwR : ‖w‖ ≤ R) (ha : a.im ≤ -δ) (haR : ‖a‖ ≤ R) (hb : b.im ≤ -δ) (hbR : ‖b‖ ≤ R) :
    ‖1 / (ζ - w) ^ 2 - 1 / ((ζ - a) * (ζ - b))‖ ≤
      6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have hne : ∀ u : ℂ, u.im ≤ -δ → ζ - u ≠ 0 := fun u hu h => by
    have := congrArg Complex.im h
    rw [sub_im, zero_im] at this
    linarith
  have hX := hne w hw
  have hY := hne a ha
  have hZ := hne b hb
  have heq : 1 / (ζ - w) ^ 2 - 1 / ((ζ - a) * (ζ - b)) =
      (w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹) +
        (w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹) +
          (a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹) := by
    field_simp
    ring
  set m : ℝ := (1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹ with hm
  have hR : 0 ≤ R := (norm_nonneg w).trans hwR
  have hm0 : 0 ≤ m := by positivity
  have iw := b36_p_inv_le hδ hζ hw hwR
  have ia := b36_p_inv_le hδ hζ ha haR
  have ib := b36_p_inv_le hδ hζ hb hbR
  have hwa : ‖w - a‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have hab : ‖a - b‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have hm3 : m ^ 3 = ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
    rw [hm, mul_pow, inv_pow]
  rw [heq]
  calc ‖(w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹) +
        (w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹) +
          (a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹)‖
      ≤ ‖(w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹)‖ +
        ‖(w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹)‖ +
          ‖(a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹)‖ := norm_add₃_le
    _ ≤ 2 * R * (m * m * m) + 2 * R * (m * m * m) + 2 * R * (m * m * m) := by
        simp only [norm_mul]
        gcongr
    _ = 6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
        rw [show 6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ = 6 * R * m ^ 3 by
          rw [hm3]; ring]
        ring

/-- The `w`-derivative of the kernel `ahKer w ζ = w(w-1)/(ζ(ζ-1)(ζ-w))`:
`∂_w ahKer w ζ = 1/(ζ - w)² - 1/(ζ(ζ - 1))`. -/
theorem b36_p_hasDerivAt_ker {ζ w : ℂ} (h0 : ζ ≠ 0) (h1 : ζ ≠ 1) (hw : ζ ≠ w) :
    HasDerivAt (fun v => ahKer v ζ) (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))) w := by
  have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
  have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
  have hd : ζ * (ζ - 1) * (ζ - w) ≠ 0 := mul_ne_zero (mul_ne_zero h0 h1') hw'
  have h := ((hasDerivAt_id' w).fun_mul ((hasDerivAt_id' w).sub_const 1)).fun_div
    (((hasDerivAt_id' w).const_sub ζ).const_mul (ζ * (ζ - 1))) hd
  unfold ahKer
  convert h using 1
  field_simp
  ring

/-- The `w`-derivative of `1/(ζ - w)² - 1/(ζ(ζ-1))` (times `c`) is `2 c/(ζ - w)³`. -/
theorem b36_p_hasDerivAt_K1 (c : ℂ) {ζ w : ℂ} (hw : ζ ≠ w) :
    HasDerivAt (fun v => c * (1 / (ζ - v) ^ 2 - 1 / (ζ * (ζ - 1)))) (2 * (c / (ζ - w) ^ 3)) w := by
  have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
  have h := (((hasDerivAt_const w (1 : ℂ)).fun_div (((hasDerivAt_id' w).const_sub ζ).fun_pow 2)
    (pow_ne_zero 2 hw')).sub_const (1 / (ζ * (ζ - 1)))).const_mul c
  convert h using 1
  field_simp
  ring

/-- The `w`-derivative of `c/(ζ - w)³` is `3 c/(ζ - w)⁴`. -/
theorem b36_p_hasDerivAt_K2 (c : ℂ) {ζ w : ℂ} (hw : ζ ≠ w) :
    HasDerivAt (fun v => c / (ζ - v) ^ 3) (3 * (c / (ζ - w) ^ 4)) w := by
  have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
  have h := (hasDerivAt_const w c).fun_div (((hasDerivAt_id' w).const_sub ζ).fun_pow 3)
    (pow_ne_zero 3 hw')
  convert h using 1
  field_simp
  ring

/-- The first `w`-derivative of the kernel is dominated on `ℍ`, uniformly for `w` near `w₀ ∈ 𝕃`, by an integrable
function.  Neither piece of `1/(ζ - w)² - 1/(ζ(ζ - 1))` is integrable alone; instead split it as `E + D` with
`D = 1/((ζ - a)(ζ - b)) - 1/(ζ(ζ - 1)) = (ahKer a - ahKer b)/(a - b)` for the fixed pair `a = w₀`, `b = 2 w₀`
(integrable by `ah_ker_integrable`) and `E = O((1 + ‖ζ‖)⁻³)` uniformly (`b36_p_E_le`). -/
theorem b36_p_K1_dom {w₀ : ℂ} (hw₀ : w₀.im < 0) :
    ∃ g : ℂ → ℝ, Integrable g (volume.restrict upperHalf) ∧
      ∀ ζ ∈ upperHalf, ∀ w ∈ ball w₀ (-w₀.im / 2),
        ‖1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))‖ ≤ g ζ := by
  have hδ : 0 < -w₀.im / 2 := by linarith
  have hw₀0 : w₀ ≠ 0 := fun h => by rw [h, zero_im] at hw₀; exact lt_irrefl _ hw₀
  have hab : w₀ - 2 * w₀ ≠ 0 := by
    rw [show w₀ - 2 * w₀ = -w₀ by ring]
    exact neg_ne_zero.2 hw₀0
  have ha : w₀.im ≤ -(-w₀.im / 2) ∧ ‖w₀‖ ≤ 2 * ‖w₀‖ := b36_p_ball hw₀ (mem_ball_self hδ)
  have hb : (2 * w₀).im ≤ -(-w₀.im / 2) ∧ ‖2 * w₀‖ ≤ 2 * ‖w₀‖ := by
    constructor
    · have : (2 * w₀).im = 2 * w₀.im := by simp
      rw [this]
      linarith
    · rw [norm_mul]
      simp
  set D : ℂ → ℂ := fun ζ => 1 / ((ζ - w₀) * (ζ - 2 * w₀)) - 1 / (ζ * (ζ - 1)) with hDdef
  have hD : IntegrableOn D upperHalf := by
    refine (((ah_ker_integrable w₀).sub (ah_ker_integrable (2 * w₀))).div_const
      (w₀ - 2 * w₀)).integrableOn.congr_fun (fun ζ hζ => ?_) isOpen_upperHalf.measurableSet
    have hζ' : 0 < ζ.im := hζ
    have h0 : ζ ≠ 0 := fun h => by rw [h, zero_im] at hζ'; exact lt_irrefl _ hζ'
    have h1 : ζ ≠ 1 := fun h => by rw [h, one_im] at hζ'; linarith
    have ha' : ζ ≠ w₀ := fun h => by rw [h] at hζ'; linarith
    have hb' : ζ ≠ 2 * w₀ := fun h => by rw [h] at hζ'; linarith [hb.1]
    simp only [hDdef, Pi.sub_apply]
    rw [ahK_sub_eq h0 h1 ha' hb', sub_zero, mul_div_cancel_left₀ _ hab]
  refine ⟨fun ζ => ‖D ζ‖ + 6 * (2 * ‖w₀‖) * ((1 + 2 * ‖w₀‖ + -w₀.im / 2) / (-w₀.im / 2)) ^ 3 *
      ((1 + ‖ζ‖) ^ 3)⁻¹,
    hD.norm.add (b36_p_profile_integrable.const_mul _).integrableOn, ?_⟩
  intro ζ hζ w hw
  have hwb := b36_p_ball hw₀ hw
  have hE := b36_p_E_le hδ hζ hwb.1 hwb.2 ha.1 ha.2 hb.1 hb.2
  have hsplit : 1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1)) =
      (1 / (ζ - w) ^ 2 - 1 / ((ζ - w₀) * (ζ - 2 * w₀))) + D ζ := by
    simp only [hDdef]
    ring
  rw [hsplit]
  calc _ ≤ ‖1 / (ζ - w) ^ 2 - 1 / ((ζ - w₀) * (ζ - 2 * w₀))‖ + ‖D ζ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Level 1** (`V'`): for `w₀ ∈ 𝕃`, `w ↦ ∫_ℍ μ ahKer w` has derivative `∫_ℍ μ (1/(ζ - w₀)² - 1/(ζ(ζ - 1)))`,
and the new integrand is integrable (differentiation under the integral, dominated by `b36_p_K1_dom`). -/
theorem b36_p_hasDerivAt_N {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable μ (volume.restrict upperHalf))
    (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ ζ‖ ≤ k) {w₀ : ℂ} (hw₀ : w₀ ∈ lowerHalf) :
    Integrable (fun ζ => μ ζ * (1 / (ζ - w₀) ^ 2 - 1 / (ζ * (ζ - 1)))) (volume.restrict upperHalf) ∧
      HasDerivAt (fun w => ∫ ζ in upperHalf, μ ζ * ahKer w ζ)
        (∫ ζ in upperHalf, μ ζ * (1 / (ζ - w₀) ^ 2 - 1 / (ζ * (ζ - 1)))) w₀ := by
  have hw₀' : w₀.im < 0 := hw₀
  have hδ : 0 < -w₀.im / 2 := by linarith
  obtain ⟨g, hg, hgb⟩ := b36_p_K1_dom hw₀'
  have hUm : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict upperHalf)
    (F := fun w ζ => μ ζ * ahKer w ζ)
    (F' := fun w ζ => μ ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
    (bound := fun ζ => k * g ζ) (ball_mem_nhds w₀ hδ)
    (Eventually.of_forall fun w => hm.fun_mul (ahK_measurable w).aestronglyMeasurable)
    ((ah_ker_integrable w₀).integrableOn.bdd_mul hm hb) ?_ ?_ (hg.const_mul k) ?_
  · exact hm.fun_mul
      ((by fun_prop : Measurable fun ζ : ℂ => 1 / (ζ - w₀) ^ 2 - 1 / (ζ * (ζ - 1))).aestronglyMeasurable)
  · filter_upwards [hb, ae_restrict_mem hUm] with ζ hζb hζ w hw
    rw [norm_mul]
    exact mul_le_mul hζb (hgb ζ hζ w hw) (norm_nonneg _) hk
  · filter_upwards [ae_restrict_mem hUm] with ζ hζ w hw
    have hζ' : 0 < ζ.im := hζ
    have hwb := b36_p_ball hw₀' hw
    have h0 : ζ ≠ 0 := fun h => by rw [h, zero_im] at hζ'; exact lt_irrefl _ hζ'
    have h1 : ζ ≠ 1 := fun h => by rw [h, one_im] at hζ'; linarith
    have hw' : ζ ≠ w := fun h => by rw [h] at hζ'; linarith [hwb.1]
    exact (b36_p_hasDerivAt_ker h0 h1 hw').const_mul (μ ζ)

/-- **Level 2**: for `w₀ ∈ 𝕃`, `w ↦ ∫_ℍ μ (1/(ζ - w)² - 1/(ζ(ζ - 1)))` has derivative `2 ∫_ℍ μ/(ζ - w₀)³`
(dominated by `2 k A³ (1 + ‖ζ‖)⁻³`). -/
theorem b36_p_hasDerivAt_G1 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable μ (volume.restrict upperHalf))
    (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ ζ‖ ≤ k) {w₀ : ℂ} (hw₀ : w₀ ∈ lowerHalf) :
    HasDerivAt (fun w => ∫ ζ in upperHalf, μ ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
      (2 * ∫ ζ in upperHalf, μ ζ / (ζ - w₀) ^ 3) w₀ := by
  have hw₀' : w₀.im < 0 := hw₀
  have hδ : 0 < -w₀.im / 2 := by linarith
  have hUm : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  set A : ℝ := (1 + 2 * ‖w₀‖ + -w₀.im / 2) / (-w₀.im / 2) with hAdef
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict upperHalf)
    (F := fun w ζ => μ ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
    (F' := fun w ζ => 2 * (μ ζ / (ζ - w) ^ 3))
    (bound := fun ζ => 2 * (k * (A ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹))) (ball_mem_nhds w₀ hδ)
    (Eventually.of_forall fun w => hm.fun_mul
      (by fun_prop : Measurable fun ζ : ℂ => 1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))).aestronglyMeasurable)
    (b36_p_hasDerivAt_N hk hm hb hw₀).1 ?_ ?_ ?_ ?_
  · rw [← integral_const_mul]
    exact h.2
  · exact (hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - w₀) ^ 3).aestronglyMeasurable).const_mul 2
  · filter_upwards [hb, ae_restrict_mem hUm] with ζ hζb hζ w hw
    have hwb := b36_p_ball hw₀' hw
    have hi := b36_p_inv_pow3_le hδ hζ hwb.1 hwb.2
    rw [norm_mul, div_eq_mul_inv, norm_mul, Complex.norm_ofNat]
    gcongr
  · exact (((b36_p_profile_integrable.const_mul (A ^ 3)).const_mul k).const_mul 2).integrableOn
  · filter_upwards [ae_restrict_mem hUm] with ζ hζ w hw
    have hζ' : 0 < ζ.im := hζ
    have hwb := b36_p_ball hw₀' hw
    have hw' : ζ ≠ w := fun h => by rw [h] at hζ'; linarith [hwb.1]
    exact b36_p_hasDerivAt_K1 (μ ζ) hw'

/-- **Level 3**: for `w₀ ∈ 𝕃`, `w ↦ ∫_ℍ μ/(ζ - w)³` has derivative `3 ∫_ℍ μ/(ζ - w₀)⁴`
(dominated by `3 k A⁴ (1 + ‖ζ‖)⁻³`). -/
theorem b36_p_hasDerivAt_H3 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable μ (volume.restrict upperHalf))
    (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ ζ‖ ≤ k) {w₀ : ℂ} (hw₀ : w₀ ∈ lowerHalf) :
    HasDerivAt (fun w => ∫ ζ in upperHalf, μ ζ / (ζ - w) ^ 3)
      (3 * ∫ ζ in upperHalf, μ ζ / (ζ - w₀) ^ 4) w₀ := by
  have hw₀' : w₀.im < 0 := hw₀
  have hδ : 0 < -w₀.im / 2 := by linarith
  have hUm : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  set A : ℝ := (1 + 2 * ‖w₀‖ + -w₀.im / 2) / (-w₀.im / 2) with hAdef
  have hw₀b := b36_p_ball hw₀' (mem_ball_self hδ)
  have hint : Integrable (fun ζ => μ ζ / (ζ - w₀) ^ 3) (volume.restrict upperHalf) := by
    refine Integrable.mono' ((b36_p_profile_integrable.const_mul (A ^ 3)).const_mul k).integrableOn
      (hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - w₀) ^ 3).aestronglyMeasurable) ?_
    filter_upwards [hb, ae_restrict_mem hUm] with ζ hζb hζ
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul hζb (b36_p_inv_pow3_le hδ hζ hw₀b.1 hw₀b.2) (norm_nonneg _) hk
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict upperHalf)
    (F := fun w ζ => μ ζ / (ζ - w) ^ 3)
    (F' := fun w ζ => 3 * (μ ζ / (ζ - w) ^ 4))
    (bound := fun ζ => 3 * (k * (A ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹))) (ball_mem_nhds w₀ hδ)
    (Eventually.of_forall fun w =>
      hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - w) ^ 3).aestronglyMeasurable)
    hint ?_ ?_ ?_ ?_
  · rw [← integral_const_mul]
    exact h.2
  · exact (hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - w₀) ^ 4).aestronglyMeasurable).const_mul 3
  · filter_upwards [hb, ae_restrict_mem hUm] with ζ hζb hζ w hw
    have hwb := b36_p_ball hw₀' hw
    have hi := b36_p_inv_pow4_le hδ hζ hwb.1 hwb.2
    rw [norm_mul, div_eq_mul_inv, norm_mul, Complex.norm_ofNat]
    gcongr
  · exact (((b36_p_profile_integrable.const_mul (A ^ 4)).const_mul k).const_mul 3).integrableOn
  · filter_upwards [ae_restrict_mem hUm] with ζ hζ w hw
    have hζ' : 0 < ζ.im := hζ
    have hwb := b36_p_ball hw₀' hw
    have hw' : ζ ≠ w := fun h => by rw [h] at hζ'; linarith [hwb.1]
    exact b36_p_hasDerivAt_K2 (μ ζ) hw'

/-- `V(μ)(w) = -(1/π) ∫_ℍ μ(ζ) ahKer w ζ`: pull the factor `w(w - 1)` inside the integral. -/
theorem b36_p_normalizedCauchyT_eq (μ : ℂ → ℂ) :
    normalizedCauchyTOn upperHalf μ = fun w => -(1 / π : ℂ) * ∫ ζ in upperHalf, μ ζ * ahKer w ζ := by
  funext w
  have h : ∫ ζ in upperHalf, μ ζ * ahKer w ζ =
      w * (w - 1) * ∫ ζ in upperHalf, μ ζ / (ζ * (ζ - 1) * (ζ - w)) := by
    rw [← integral_const_mul]
    congr 1
    funext ζ
    unfold ahKer
    ring
  rw [normalizedCauchyTOn, h]
  ring

/-- Bridge to S13's first variation (for part 2 of Lemma 36.2): for `ν` vanishing on the closed lower half-plane
(e.g. `ν ∈ M`), the normalized Cauchy transform over `ℍ` is Ahlfors' `ahVar ν`. -/
theorem b36_p_normalizedCauchyT_eq_ahVar {ν : ℂ → ℂ} (hν : ∀ z : ℂ, z.im ≤ 0 → ν z = 0) :
    normalizedCauchyTOn upperHalf ν = ahVar ν := by
  rw [b36_p_normalizedCauchyT_eq]
  funext w
  rw [ahVar, ← integral_indicator isOpen_upperHalf.measurableSet]
  congr 2
  funext ζ
  by_cases hζ : ζ ∈ upperHalf
  · rw [indicator_of_mem hζ]
  · rw [indicator_of_notMem hζ, hν ζ (not_lt.1 hζ), zero_mul]

/-- §36.3: the first term of the representation of `f_{tμ}`: `σ₁ = V(μ)` (`normalizedCauchyTOn`; the book's
`T(μ)(z) = -(1/π)∬ μ(ζ)/(ζ-z)` up to a term linear in `z`, which the third derivative kills), and
`S_{f_{tμ}}(z) = t σ₁'''(z) + o(|t|)` for `z ∈ 𝕃`, with `σ₁''' = P(μ)`.

**Correction.**  This was stated with `cauchyTOn upperHalf μ`, which is a divergent integral for bounded `μ`
(Lean's junk value `0`), so the right side was `0`: false for `μ = k·1_ℍ + k·1_{B(i,1/2)}`. -/
theorem bersDerivative_eq_cauchyT_third (μ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    bersDerivative μ.1 z = deriv (deriv (deriv (normalizedCauchyTOn upperHalf μ.1))) z := by
  obtain ⟨⟨k, hk0, -, hm', hb'⟩, -⟩ := μ.2
  rw [Measure.restrict_univ] at hm' hb'
  have hm : AEStronglyMeasurable μ.1 (volume.restrict upperHalf) := hm'.restrict
  have hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ.1 ζ‖ ≤ k := ae_restrict_of_ae hb'
  set G₁ : ℂ → ℂ := fun w => ∫ ζ in upperHalf, μ.1 ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1)))
    with hG₁
  set H₃ : ℂ → ℂ := fun w => ∫ ζ in upperHalf, μ.1 ζ / (ζ - w) ^ 3 with hH₃
  have h1 : ∀ w ∈ lowerHalf,
      HasDerivAt (normalizedCauchyTOn upperHalf μ.1) (-(1 / π : ℂ) * G₁ w) w := by
    intro w hw
    rw [b36_p_normalizedCauchyT_eq]
    exact ((b36_p_hasDerivAt_N hk0 hm hb hw).2).const_mul _
  have h2 : ∀ w ∈ lowerHalf, HasDerivAt G₁ (2 * H₃ w) w := fun w hw =>
    b36_p_hasDerivAt_G1 hk0 hm hb hw
  have h3 : HasDerivAt H₃ (3 * ∫ ζ in upperHalf, μ.1 ζ / (ζ - z) ^ 4) z :=
    b36_p_hasDerivAt_H3 hk0 hm hb hz
  have e1 : ∀ w ∈ lowerHalf, deriv (normalizedCauchyTOn upperHalf μ.1) =ᶠ[𝓝 w]
      fun v => -(1 / π : ℂ) * G₁ v := by
    intro w hw
    filter_upwards [isOpen_lowerHalf.mem_nhds hw] with v hv
    exact (h1 v hv).deriv
  have e2 : deriv (deriv (normalizedCauchyTOn upperHalf μ.1)) =ᶠ[𝓝 z]
      fun v => -(1 / π : ℂ) * (2 * H₃ v) := by
    filter_upwards [isOpen_lowerHalf.mem_nhds hz] with v hv
    rw [(e1 v hv).deriv_eq]
    exact ((h2 v hv).const_mul _).deriv
  rw [e2.deriv_eq, ((h3.const_mul 2).const_mul (-(1 / π : ℂ))).deriv, bersDerivative]
  ring

/-! ### s36b track (coordinator 553e2d), part Q: Lemma 36.2 (part 1), analyticity and `DΦ(0) = P` -/

open scoped Classical in
/-- The affine family `t ↦ μ + t ν` in `M`, defaulting to `μ` where `μ + t ν` is not admissible. -/
def b36_q_fam (μ ν : BeltramiH) (t : ℂ) : BeltramiH :=
  if h : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → μ.1 z + t * ν.1 z = 0 then ⟨fun w => μ.1 w + t * ν.1 w, h⟩ else μ

/-- A radius `r > 0` and a bound `k < 1` with `‖μ + t ν‖_∞ ≤ k` for `|t| < r`
(`|μ + t ν| ≤ k_μ + |t| k_ν`, `r = (1 - k_μ)/(2(k_ν + 1))`). -/
theorem b36_q_small (μ ν : BeltramiH) :
    ∃ r > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k := by
  obtain ⟨⟨k₁, hk₁0, hk₁1, hm₁, hb₁⟩, -⟩ := μ.2
  obtain ⟨⟨k₂, hk₂0, hk₂1, hm₂, hb₂⟩, -⟩ := ν.2
  have hr : 0 < (1 - k₁) / (2 * (k₂ + 1)) := div_pos (by linarith) (by positivity)
  have hrk : (1 - k₁) / (2 * (k₂ + 1)) * k₂ ≤ (1 - k₁) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨(1 - k₁) / (2 * (k₂ + 1)), hr, k₁ + (1 - k₁) / (2 * (k₂ + 1)) * k₂,
    add_nonneg hk₁0 (mul_nonneg hr.le hk₂0), by linarith, fun t ht => ⟨hm₁.add (hm₂.const_mul t), ?_⟩⟩
  filter_upwards [hb₁, hb₂] with w h1 h2
  have htn : ‖t‖ ≤ (1 - k₁) / (2 * (k₂ + 1)) := (mem_ball_zero_iff.mp ht).le
  calc ‖μ.1 w + t * ν.1 w‖ ≤ ‖μ.1 w‖ + ‖t‖ * ‖ν.1 w‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ k₁ + (1 - k₁) / (2 * (k₂ + 1)) * k₂ :=
        add_le_add h1 (mul_le_mul htn h2 (norm_nonneg _) hr.le)

/-- On the ball of `b36_q_small`, `b36_q_fam μ ν t` is `μ + t ν`. -/
theorem b36_q_fam_val (μ ν : BeltramiH) {r k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) r) : (b36_q_fam μ ν t).1 = fun w => μ.1 w + t * ν.1 w := by
  have hc : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → μ.1 z + t * ν.1 z = 0 :=
    ⟨⟨k, hk0, hk1, hb t ht⟩, fun z hz => by rw [μ.2.2 z hz, ν.2.2 z hz, mul_zero, add_zero]⟩
  unfold b36_q_fam
  exact congrArg Subtype.val (dite_eq_left hc)

/-- `bB_schwarzian_holo` over an arbitrary open parameter set `P` with a uniform bound `k < 1`:
`t ↦ S_{f_{ν t}}(z)` is holomorphic on `P` for each `z ∈ 𝕃`. -/
theorem b36_q_schwarzian_holo {ν : ℂ → BeltramiH} {P : Set ℂ} (hP : IsOpen P) {k : ℝ} (hk₀ : 0 ≤ k)
    (hk1 : k < 1) (hkP : ∀ t ∈ P, IsBeltramiCoeff (ν t).1 univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => (ν t).1 z) P) {z : ℂ} (hz : z ∈ lowerHalf) :
    DifferentiableOn ℂ (fun t => schwarzian (normalizedSolution (ν t).1) z) P := by
  have hconf := fun t => ut_conformal_lowerHalf (ν t)
  have ha : ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun t => normalizedSolution (ν t).1 w) P :=
    fun w _ => thm13_8_ahlfors_bers_holomorphic (μ := fun t => (ν t).1)
      (f := fun t => normalizedSolution (ν t).1) hP hk₀ hk1 hkP hhol (fun t _ => ut_spec (ν t)) w
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := fun t => normalizedSolution (ν t).1)
    isOpen_lowerHalf ha (fun t _ => (hconf t).1) (bB_hs_bound hP hk₀ hk1 hkP) z hz
  have hne : ∀ t, deriv (normalizedSolution (ν t).1) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  refine ((((hd3.mul hd1).sub (hd2.mul hd2)).div (hd1.pow 2) fun t _ => pow_ne_zero 2 (hne t)).sub
    (((hd2.div hd1 fun t _ => hne t).pow 2).const_mul (1 / 2))).congr fun t _ => ?_
  exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)

/-- The hypotheses of `thm13_8`/`bB_hs_bound` for the family `b36_q_fam μ ν` on the ball of `b36_q_small`. -/
theorem b36_q_fam_hyps (μ ν : BeltramiH) {r k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => μ.1 w + t * ν.1 w) univ k) :
    (∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (b36_q_fam μ ν t).1 univ k) ∧
      ∀ w, DifferentiableOn ℂ (fun t => (b36_q_fam μ ν t).1 w) (ball 0 r) := by
  refine ⟨fun t ht => by rw [b36_q_fam_val μ ν hk0 hk1 hb ht]; exact hb t ht, fun w => ?_⟩
  exact (by fun_prop : DifferentiableOn ℂ (fun t : ℂ => μ.1 w + t * ν.1 w) (ball 0 r)).congr
    fun t ht => by rw [b36_q_fam_val μ ν hk0 hk1 hb ht]

/-- **Part 1**: `t ↦ φ_{μ + t ν}(z)` is holomorphic near `0` for `z ∈ 𝕃`. -/
theorem b36_q_part1 (μ ν : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    ∃ r > 0, DifferentiableOn ℂ (fun t : ℂ => bersFunction (fun w => μ.1 w + t * ν.1 w) z) (ball 0 r) := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := b36_q_small μ ν
  obtain ⟨hkP, hhol⟩ := b36_q_fam_hyps μ ν hk0 hk1 hb
  refine ⟨r, hr, (b36_q_schwarzian_holo isOpen_ball hk0 hk1 hkP hhol hz).congr fun t ht => ?_⟩
  simp only [bersFunction, indicator_of_mem hz, b36_q_fam_val μ ν hk0 hk1 hb ht]

/-- `V[ν] = normalizedCauchyTOn upperHalf ν` for `ν` vanishing on `Im ≤ 0`. -/
theorem b36_q_ahVar_eq (ν : BeltramiH) : ahVar ν.1 = normalizedCauchyTOn upperHalf ν.1 := by
  funext w
  simp only [ahVar, normalizedCauchyTOn, ahKer]
  have hU : MeasurableSet upperHalf := (isOpen_lt continuous_const continuous_im).measurableSet
  rw [← integral_indicator hU]
  have h1 : upperHalf.indicator (fun ζ => ν.1 ζ / (ζ * (ζ - 1) * (ζ - w))) =
      fun ζ => ν.1 ζ / (ζ * (ζ - 1) * (ζ - w)) := by
    funext ζ
    by_cases hζ : ζ ∈ upperHalf
    · rw [indicator_of_mem hζ]
    · rw [indicator_of_notMem hζ, ν.2.2 ζ (not_lt.mp hζ), zero_div]
  have h2 : (fun ζ => ν.1 ζ * (w * (w - 1) / (ζ * (ζ - 1) * (ζ - w)))) =
      fun ζ => (w * (w - 1)) * (ν.1 ζ / (ζ * (ζ - 1) * (ζ - w))) := by
    funext ζ
    ring
  rw [h1, h2, integral_const_mul]
  ring

/-- The zero Beltrami coefficient as an element of `M`. -/
def b36_q_zero : BeltramiH := ⟨0, bB_l_zero_mem⟩

/-- `f_{0 + 0·ν} = id`. -/
theorem b36_q_F0 (ν : BeltramiH) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => b36_q_zero.1 w + t * ν.1 w) univ k) :
    normalizedSolution (b36_q_fam b36_q_zero ν 0).1 = id := by
  rw [b36_q_fam_val b36_q_zero ν hk0 hk1 hb (mem_ball_self hr)]
  have h : (fun w => b36_q_zero.1 w + 0 * ν.1 w) = (0 : ℂ → ℂ) := by
    funext w
    simp [b36_q_zero]
  rw [h]
  exact bB_l_normalizedSolution_zero

/-- First variation along `t ↦ t ν` at `t = 0`: `∂_t f_{tν}(w)|₀ = V[ν](w)` (`ahT_hasDerivAt` at `t₀ = 0`,
where `f₀ = id` and the coefficient derivative is `ν`). -/
theorem b36_q_first_var (ν : BeltramiH) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => b36_q_zero.1 w + t * ν.1 w) univ k) (w : ℂ) :
    HasDerivAt (fun t => normalizedSolution (b36_q_fam b36_q_zero ν t).1 w) (ahVar ν.1 w) 0 := by
  obtain ⟨hkP, hhol⟩ := b36_q_fam_hyps b36_q_zero ν hk0 hk1 hb
  have h := ahT_hasDerivAt (μ := fun t => (b36_q_fam b36_q_zero ν t).1)
    (f := fun t => normalizedSolution (b36_q_fam b36_q_zero ν t).1) isOpen_ball hk0 hk1 hkP hhol
    (fun t _ => ut_spec _) (mem_ball_self hr) w
  have hF0 := b36_q_F0 ν hr hk0 hk1 hb
  have hval0 := b36_q_fam_val b36_q_zero ν hk0 hk1 hb (mem_ball_self hr)
  have hdot : ahT_dot (fun ζ => deriv (fun s => (b36_q_fam b36_q_zero ν s).1 ζ) 0)
      (b36_q_fam b36_q_zero ν 0).1 (normalizedSolution (b36_q_fam b36_q_zero ν 0).1) = ν.1 := by
    funext ζ
    have hinv : Function.invFunOn (id : ℂ → ℂ) univ ζ = ζ :=
      (injOn_id univ).leftInvOn_invFunOn (mem_univ ζ)
    have hdz : dz id ζ = 1 := by
      simp only [dz, fderiv_id, ContinuousLinearMap.id_apply]
      rw [I_mul_I]
      ring
    have hder : deriv (fun s => (b36_q_fam b36_q_zero ν s).1 ζ) 0 = ν.1 ζ := by
      have hev : (fun s => (b36_q_fam b36_q_zero ν s).1 ζ) =ᶠ[𝓝 0]
          fun s => b36_q_zero.1 ζ + s * ν.1 ζ :=
        eventually_of_mem (ball_mem_nhds 0 hr) fun s hs => by
          beta_reduce
          rw [b36_q_fam_val b36_q_zero ν hk0 hk1 hb hs]
      rw [hev.deriv_eq]
      simp
    rw [hF0, hval0]
    simp only [ahT_dot, hinv, hdz, hder]
    simp [b36_q_zero]
  rw [hdot, hF0] at h
  exact h

/-- `iteratedDeriv 3 id = 0`. -/
theorem b36_q_iteratedDeriv3_id (z : ℂ) : iteratedDeriv 3 (fun w : ℂ => w) z = 0 := by
  simp [iteratedDeriv_succ, deriv_id'']

/-- The third derivative is linear on functions holomorphic near `z`:
`(f - id - h V)‴(z) = f‴(z) - h V‴(z)`. -/
theorem b36_q_iteratedDeriv3_lin {f V : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) (hV : DifferentiableOn ℂ V U) (h : ℂ) :
    iteratedDeriv 3 (fun w => f w - w - h * V w) z = iteratedDeriv 3 f z - h * iteratedDeriv 3 V z := by
  have hn : U ∈ 𝓝 z := hU.mem_nhds hz
  have c1 : ContDiffAt ℂ 3 f z := (hf.contDiffOn hU).contDiffAt hn
  have c2 : ContDiffAt ℂ 3 (fun w : ℂ => w) z := contDiffAt_id
  have c3 : ContDiffAt ℂ 3 V z := (hV.contDiffOn hU).contDiffAt hn
  rw [iteratedDeriv_fun_sub (c1.sub c2) ((contDiffAt_const (c := h)).mul c3), iteratedDeriv_fun_sub c1 c2,
    iteratedDeriv_const_mul_field, b36_q_iteratedDeriv3_id, sub_zero]

/-- The commutation `∂_t ∂_w³ f_{tν}(z)|₀ = V[ν]‴(z)`: the uniform second-order Taylor bound in `t`
(`bB_h0_taylor_le`, uniform on a ball in `w`) and Cauchy's estimate for the third `w`-derivative. -/
theorem b36_q_d3 (ν : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) {r k : ℝ} (hr : 0 < r) (hk0 : 0 ≤ k)
    (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (fun w => b36_q_zero.1 w + t * ν.1 w) univ k) :
    HasDerivAt (fun t => iteratedDeriv 3 (normalizedSolution (b36_q_fam b36_q_zero ν t).1) z)
      (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
  obtain ⟨hkP, hhol⟩ := b36_q_fam_hyps b36_q_zero ν hk0 hk1 hb
  set F : ℂ → ℂ → ℂ := fun t => normalizedSolution (b36_q_fam b36_q_zero ν t).1 with hFdef
  have ha : ∀ w, DifferentiableOn ℂ (fun t => F t w) (ball 0 r) :=
    thm13_8_ahlfors_bers_holomorphic (μ := fun t => (b36_q_fam b36_q_zero ν t).1) (f := F) isOpen_ball
      hk0 hk1 hkP hhol (fun t _ => ut_spec _)
  have hbU : ∀ t, DifferentiableOn ℂ (F t) lowerHalf := fun t => (ut_conformal_lowerHalf _).1
  have hc := bB_hs_bound (ν := b36_q_fam b36_q_zero ν) isOpen_ball hk0 hk1 hkP
  have hF0 : F 0 = id := b36_q_F0 ν hr hk0 hk1 hb
  have hV : ∀ w, HasDerivAt (fun t => F t w) (ahVar ν.1 w) 0 := b36_q_first_var ν hr hk0 hk1 hb
  -- `V[ν]` is holomorphic on `𝕃` (`bB_h0_deriv_holo` with the roles of `t` and `w` swapped)
  have hVd : DifferentiableOn ℂ (ahVar ν.1) lowerHalf := by
    have h := bB_h0_deriv_holo (P := lowerHalf) (U := ball (0 : ℂ) r) (F := fun w t => F t w)
      (fun t _ => hbU t) (fun w _ => ha w)
      (fun w₀ hw₀ t₀ ht₀ => by
        obtain ⟨ε, hε, h1, h2, M, hM⟩ := hc t₀ ht₀ w₀ hw₀
        exact ⟨ε, hε, h2, h1, M, fun w hw t ht => hM t ht w hw⟩) 0 (mem_ball_self hr)
    exact h.congr fun w _ => (hV w).deriv.symm
  obtain ⟨ε, hε, hPε, hUε, M, hM⟩ := hc 0 (mem_ball_self hr) z hz
  -- uniform Taylor bound
  have htay : ∀ h : ℂ, ‖h‖ < ε / 2 → ∀ w ∈ ball z ε,
      ‖F h w - w - h * ahVar ν.1 w‖ ≤ 8 * M / ε ^ 2 * ‖h‖ ^ 2 := by
    intro h hh w hw
    have hg : DifferentiableOn ℂ (fun t => F t w) (ball 0 ε) := (ha w).mono hPε
    have := bB_h0_taylor_le hε hg (fun t ht => hM t ht w hw) hh
    rw [zero_add, (hV w).deriv, hF0] at this
    exact this
  -- Cauchy estimate for the third derivative
  set C : ℝ := (Nat.factorial 3 : ℝ) * (8 * M / ε ^ 2) / (ε / 2) ^ 3 with hCdef
  have hd3 : ∀ h : ℂ, ‖h‖ < ε / 2 →
      ‖iteratedDeriv 3 (F h) z - h * iteratedDeriv 3 (ahVar ν.1) z‖ ≤ C * ‖h‖ ^ 2 := by
    intro h hh
    have hE : DifferentiableOn ℂ (fun w => F h w - w - h * ahVar ν.1 w) lowerHalf :=
      ((hbU h).sub differentiableOn_id).sub (hVd.const_mul h)
    have hsub : closedBall z (ε / 2) ⊆ lowerHalf :=
      (closedBall_subset_ball (by linarith)).trans hUε
    have hbd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 (by linarith : 0 < ε / 2)
      (hE.diffContOnCl_ball hsub) (fun w hw => htay h hh w
        (closedBall_subset_ball (by linarith) (sphere_subset_closedBall hw)))
    rw [b36_q_iteratedDeriv3_lin isOpen_lowerHalf hz (hbU h) hVd h] at hbd
    calc _ ≤ _ := hbd
      _ = C * ‖h‖ ^ 2 := by rw [hCdef]; ring
  have h0 : iteratedDeriv 3 (F 0) z = 0 := by
    rw [hF0]
    exact b36_q_iteratedDeriv3_id z
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self hε) z (mem_ball_self hε))
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min (ε / 2) (c / (C + 1)) := lt_min (by linarith) (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
  rw [mem_ball_zero_iff, lt_min_iff] at ht
  rw [h0, sub_zero, sub_zero, smul_eq_mul]
  calc ‖iteratedDeriv 3 (F t) z - t * iteratedDeriv 3 (ahVar ν.1) z‖ ≤ C * ‖t‖ ^ 2 := hd3 t ht.1
    _ ≤ c * ‖t‖ := by
      have h1 : C * ‖t‖ ≤ c := by
        have := ht.2
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith [norm_nonneg t]
      nlinarith [norm_nonneg t]

/-- **Part 2** (up to target 3): `∂_t φ_{tν}(z)|₀ = V[ν]‴(z)` for `z ∈ 𝕃` (linearization of
`S = (f‴ f′ - f″²)/f′² - ½(f″/f′)²` at `f₀ = id`, plus `b36_q_d3`). -/
theorem b36_q_part2 (ν : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    HasDerivAt (fun t : ℂ => bersFunction (fun w => t * ν.1 w) z) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := b36_q_small b36_q_zero ν
  obtain ⟨hkP, hhol⟩ := b36_q_fam_hyps b36_q_zero ν hk0 hk1 hb
  set F : ℂ → ℂ → ℂ := fun t => normalizedSolution (b36_q_fam b36_q_zero ν t).1 with hFdef
  have ha : ∀ w, DifferentiableOn ℂ (fun t => F t w) (ball 0 r) :=
    thm13_8_ahlfors_bers_holomorphic (μ := fun t => (b36_q_fam b36_q_zero ν t).1) (f := F) isOpen_ball
      hk0 hk1 hkP hhol (fun t _ => ut_spec _)
  have hconf := fun t => ut_conformal_lowerHalf (b36_q_fam b36_q_zero ν t)
  have hc := bB_hs_bound (ν := b36_q_fam b36_q_zero ν) isOpen_ball hk0 hk1 hkP
  have hF0 : F 0 = id := b36_q_F0 ν hr hk0 hk1 hb
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := F) isOpen_lowerHalf (fun w _ => ha w)
    (fun t _ => (hconf t).1) hc z hz
  have hb0 : ball (0 : ℂ) r ∈ 𝓝 0 := ball_mem_nhds 0 hr
  have e1 := (hd1.differentiableAt hb0).hasDerivAt
  have e2 := (hd2.differentiableAt hb0).hasDerivAt
  have e3 : HasDerivAt (fun t => deriv (deriv (deriv (F t))) z) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
    have h := b36_q_d3 ν hz hr hk0 hk1 hb
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h ⊢
    exact h
  have v1 : deriv (F 0) z = 1 := by rw [hF0, deriv_id]
  have v2 : deriv (deriv (F 0)) z = 0 := by rw [hF0, deriv_id', deriv_const]
  have v3 : deriv (deriv (deriv (F 0))) z = 0 := by rw [hF0, deriv_id', deriv_const', deriv_const]
  have hne : ∀ t, deriv (F t) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  have hS := (((e3.mul e1).sub (e2.mul e2)).div (e1.pow 2) (pow_ne_zero 2 (hne 0))).sub
    (((e2.div e1 (hne 0)).pow 2).const_mul (1 / 2))
  have hS' : HasDerivAt (fun t => (deriv (deriv (deriv (F t))) z * deriv (F t) z -
      deriv (deriv (F t)) z * deriv (deriv (F t)) z) / deriv (F t) z ^ 2 -
      1 / 2 * (deriv (deriv (F t)) z / deriv (F t) z) ^ 2) (iteratedDeriv 3 (ahVar ν.1) z) 0 := by
    convert hS using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, v1, v2, v3]
    ring
  refine hS'.congr_of_eventuallyEq ?_
  filter_upwards [hb0] with t ht
  have hfun : (fun w => t * ν.1 w) = (b36_q_fam b36_q_zero ν t).1 := by
    rw [b36_q_fam_val b36_q_zero ν hk0 hk1 hb ht]
    funext w
    simp [b36_q_zero]
  simp only [bersFunction, hfun, indicator_of_mem hz]
  exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)

/-- **Lemma 36.2 (part 1)**, assuming target 3 (`bersDerivative_eq_cauchyT_third`) as the hypothesis `h3`. -/
theorem b36_q_main
    (h3 : ∀ (μ : BeltramiH) {z : ℂ}, z ∈ lowerHalf →
      bersDerivative μ.1 z = deriv (deriv (deriv (normalizedCauchyTOn upperHalf μ.1))) z)
    (μ : BeltramiGamma Γ) :
    (∀ ν : BeltramiGamma Γ, ∀ z ∈ lowerHalf, ∃ r > 0,
      DifferentiableOn ℂ (fun t : ℂ => bersFunction (fun w => μ.1.1 w + t * ν.1.1 w) z) (ball 0 r)) ∧
      ∀ ν : BeltramiGamma Γ, ∀ z ∈ lowerHalf,
        HasDerivAt (fun t : ℂ => bersFunction (fun w => t * ν.1.1 w) z) (bersDerivative ν.1.1 z) 0 := by
  refine ⟨fun ν z hz => b36_q_part1 μ.1 ν.1 hz, fun ν z hz => ?_⟩
  have h := b36_q_part2 ν.1 hz
  rwa [b36_q_ahVar_eq, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    ← h3 ν.1 hz] at h

/-- **Lemma 36.2 (part 1)**: the Bers map `Φ : M(ℍ, G) → Q(G, 𝕃)`, `μ ↦ φ_μ`, is complex analytic
(`φ_μ(z)` is holomorphic in `μ` for fixed `z`, with `‖Φ(μ)‖ ≤ 3/2`, so `DΦ(μ)` is a bounded linear
map and `‖Φ(μ + cν) - Φ(μ) - DΦ(μ)(cν)‖ ≤ 3|c|²/4`), and `DΦ(0) = P`. -/
theorem lemma36_2_bers_analytic (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    (∀ ν : BeltramiGamma Γ, ∀ z ∈ lowerHalf, ∃ r > 0,
      DifferentiableOn ℂ (fun t : ℂ => bersFunction (fun w => μ.1.1 w + t * ν.1.1 w) z) (ball 0 r)) ∧
      ∀ ν : BeltramiGamma Γ, ∀ z ∈ lowerHalf,
        HasDerivAt (fun t : ℂ => bersFunction (fun w => t * ν.1.1 w) z) (bersDerivative ν.1.1 z) 0 := by
  have _hΓ := hΓ
  exact b36_q_main (fun μ _ hz => bersDerivative_eq_cauchyT_third μ hz) μ

/-! ### s36b track (coordinator 553e2d), part R:
`lemma36_2_right_inverse` via a Cayley change of variables and the mean value
property (the Bers reproducing formula `∬_ℍ y² φ(ζ̄)/(ζ - z)⁴ = (π/12) φ(z)`). -/

/-- The Cayley-type map `q ↦ a + (ā - a)/(1 - q)`: for `Im a < 0` it maps the unit disc onto `ℍ`,
with `0 ↦ ā`; the same map with `a` replaced by `ā` maps the disc onto `𝕃`, with `0 ↦ a`. -/
def b36_r_cay (a q : ℂ) : ℂ := a + (conj a - a) / (1 - q)

/-- On the unit disc `1 - q ≠ 0`. -/
theorem b36_r_one_sub_ne {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : 1 - q ≠ 0 := by
  intro h
  have h1 : q = 1 := by linear_combination -h
  rw [h1, mem_ball, dist_zero_right, norm_one] at hq
  exact lt_irrefl _ hq

/-- On the unit disc `1 - q̄ ≠ 0`. -/
theorem b36_r_one_sub_conj_ne {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : 1 - conj q ≠ 0 := by
  intro h
  apply b36_r_one_sub_ne hq
  have h2 := congrArg conj h
  simpa using h2

/-- `ā - a ≠ 0` when `Im a ≠ 0`. -/
theorem b36_r_conj_sub_ne {a : ℂ} (ha : a.im ≠ 0) : conj a - a ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp only [sub_im, conj_im, zero_im] at h2
  exact ha (by linarith)

/-- The imaginary part of the Cayley map:
`Im (a + (ā - a)/(1 - q)) = -Im a · (1 - |q|²)/|1 - q|²`. -/
theorem b36_r_cay_im (a : ℂ) {q : ℂ} (hq : 1 - q ≠ 0) :
    (b36_r_cay a q).im = -a.im * (1 - ‖q‖ ^ 2) / ‖1 - q‖ ^ 2 := by
  have hq' : 1 - conj q ≠ 0 := by
    intro h
    apply hq
    have h2 := congrArg conj h
    simpa using h2
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.im_eq_sub_conj (b36_r_cay a q), Complex.im_eq_sub_conj a, ← Complex.mul_conj' q,
    ← Complex.mul_conj' (1 - q)]
  simp only [b36_r_cay, map_add, map_div₀, map_sub, Complex.conj_conj, map_one]
  field_simp
  ring

/-- Conjugating the Cayley map: `conj (cay a q) = cay ā q̄`. -/
theorem b36_r_conj_cay (a q : ℂ) : conj (b36_r_cay a q) = b36_r_cay (conj a) (conj q) := by
  simp [b36_r_cay, map_add, map_div₀, map_sub]

/-- `cay ā 0 = a`. -/
theorem b36_r_cay_conj_zero (a : ℂ) : b36_r_cay (conj a) 0 = a := by
  simp [b36_r_cay]

/-- `cay a q - a = (ā - a)/(1 - q)`. -/
theorem b36_r_cay_sub (a q : ℂ) : b36_r_cay a q - a = (conj a - a) / (1 - q) := by
  simp [b36_r_cay]

/-- For `Im a < 0`, the Cayley map sends the unit disc into `ℍ`. -/
theorem b36_r_cay_mem_upper {a : ℂ} (ha : a ∈ lowerHalf) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    b36_r_cay a q ∈ upperHalf := by
  have hu := b36_r_one_sub_ne hq
  show 0 < (b36_r_cay a q).im
  rw [b36_r_cay_im a hu]
  have ha' : a.im < 0 := ha
  have h1 : ‖q‖ < 1 := by simpa [mem_ball, dist_zero_right] using hq
  have h2 : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have h3 : 0 < ‖1 - q‖ ^ 2 := by positivity
  exact div_pos (mul_pos (by linarith) h2) h3

/-- For `Im a < 0`, the Cayley map with `ā` sends the unit disc into `𝕃`. -/
theorem b36_r_cay_mem_lower {a : ℂ} (ha : a ∈ lowerHalf) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    b36_r_cay (conj a) q ∈ lowerHalf := by
  have hu := b36_r_one_sub_ne hq
  show (b36_r_cay (conj a) q).im < 0
  rw [b36_r_cay_im (conj a) hu, conj_im, neg_neg]
  have ha' : a.im < 0 := ha
  have h1 : ‖q‖ < 1 := by simpa [mem_ball, dist_zero_right] using hq
  have h2 : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have h3 : 0 < ‖1 - q‖ ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos ha' h2) h3

/-- The Cayley map is injective on the disc (`Im a ≠ 0`). -/
theorem b36_r_injOn {a : ℂ} (ha : a ∈ lowerHalf) : InjOn (b36_r_cay a) (ball (0 : ℂ) 1) := by
  intro q₁ h₁ q₂ h₂ heq
  have hd := b36_r_conj_sub_ne (a := a) (ne_of_lt (show a.im < 0 from ha))
  have hu₁ := b36_r_one_sub_ne h₁
  have hu₂ := b36_r_one_sub_ne h₂
  have h := add_left_cancel (show a + (conj a - a) / (1 - q₁) = a + (conj a - a) / (1 - q₂) from heq)
  rw [div_eq_div_iff hu₁ hu₂] at h
  have h' := mul_left_cancel₀ hd h
  linear_combination h'

/-- The Cayley map sends the unit disc onto `ℍ` (`Im a < 0`). -/
theorem b36_r_image {a : ℂ} (ha : a ∈ lowerHalf) : b36_r_cay a '' ball (0 : ℂ) 1 = upperHalf := by
  ext ζ
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact b36_r_cay_mem_upper ha hq
  · intro hζ
    have hζ' : 0 < ζ.im := hζ
    have ha' : a.im < 0 := ha
    have hd := b36_r_conj_sub_ne (a := a) (ne_of_lt ha')
    have hζa : ζ - a ≠ 0 := by
      intro h
      have h2 := congrArg Complex.im h
      simp only [sub_im, zero_im] at h2
      linarith
    refine ⟨(ζ - conj a) / (ζ - a), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.2 hζa)]
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [sub_re, sub_im, conj_re, conj_im]
      nlinarith
    · have h1 : 1 - (ζ - conj a) / (ζ - a) = (conj a - a) / (ζ - a) := by
        field_simp
        ring
      simp only [b36_r_cay]
      rw [h1]
      field_simp
      ring

/-- The derivative of the Cayley map: `(ā - a)/(1 - q)²`. -/
theorem b36_r_hasDerivAt (a : ℂ) {q : ℂ} (hq : 1 - q ≠ 0) :
    HasDerivAt (b36_r_cay a) ((conj a - a) / (1 - q) ^ 2) q := by
  have h1 : HasDerivAt (fun x : ℂ => (1 - x)⁻¹) (-(-1) / (1 - q) ^ 2) q :=
    ((hasDerivAt_id q).const_sub 1).inv hq
  have h2 := (h1.const_mul (conj a - a)).const_add a
  have he : b36_r_cay a = fun x => a + (conj a - a) * (1 - x)⁻¹ := by
    funext x
    simp [b36_r_cay, div_eq_mul_inv]
  rw [he]
  convert h2 using 1
  ring

/-- The Cayley map is holomorphic on the disc. -/
theorem b36_r_differentiableOn (a : ℂ) : DifferentiableOn ℂ (b36_r_cay a) (ball (0 : ℂ) 1) :=
  fun _ hq => (b36_r_hasDerivAt a (b36_r_one_sub_ne hq)).differentiableAt.differentiableWithinAt

/-- The holomorphic function `h(q) = φ(cay ā q)/(1 - q)⁴` on the disc (`h(0) = φ(a)`). -/
def b36_r_hfun (φ : ℂ → ℂ) (a q : ℂ) : ℂ := φ (b36_r_cay (conj a) q) / (1 - q) ^ 4

/-- The transformed integrand on the disc: `G(q) = ¼ (1 - |q|²)² h(q̄)`. -/
def b36_r_G (φ : ℂ → ℂ) (a q : ℂ) : ℂ := (1 / 4 : ℂ) * (1 - q * conj q) ^ 2 * b36_r_hfun φ a (conj q)

/-- **Kernel identity.**  Under `ζ = cay a q`, `|dζ/dq|² · (Im ζ)² φ(ζ̄)/(ζ - a)⁴ = G(q)`. -/
theorem b36_r_kernel {a : ℂ} (ha : a ∈ lowerHalf) (φ : ℂ → ℂ) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    ‖deriv (b36_r_cay a) q‖ ^ 2 • (((b36_r_cay a q).im : ℂ) ^ 2 * φ (conj (b36_r_cay a q)) /
      (b36_r_cay a q - a) ^ 4) = b36_r_G φ a q := by
  have hu := b36_r_one_sub_ne hq
  have hu' := b36_r_one_sub_conj_ne hq
  have hd := b36_r_conj_sub_ne (ne_of_lt (show a.im < 0 from ha))
  have hd' : a - conj a ≠ 0 := by
    intro h
    apply hd
    linear_combination -h
  rw [(b36_r_hasDerivAt a hu).deriv, b36_r_cay_im a hu, b36_r_conj_cay, b36_r_cay_sub,
    Complex.real_smul]
  unfold b36_r_G b36_r_hfun
  set Φ := φ (b36_r_cay (conj a) (conj q))
  push_cast
  rw [← Complex.mul_conj' q, ← Complex.mul_conj' (1 - q),
    ← Complex.mul_conj' ((conj a - a) / (1 - q) ^ 2), Complex.im_eq_sub_conj a]
  simp only [map_div₀, map_sub, map_pow, Complex.conj_conj, map_one]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

/-- `h` is holomorphic on the disc. -/
theorem b36_r_hfun_diff {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {a : ℂ}
    (ha : a ∈ lowerHalf) : DifferentiableOn ℂ (b36_r_hfun φ a) (ball (0 : ℂ) 1) := by
  have h1 : DifferentiableOn ℂ (fun q => φ (b36_r_cay (conj a) q)) (ball (0 : ℂ) 1) :=
    hφ.comp (b36_r_differentiableOn (conj a)) (fun q hq => b36_r_cay_mem_lower ha hq)
  have h2 : DifferentiableOn ℂ (fun q : ℂ => (1 - q) ^ 4) (ball (0 : ℂ) 1) :=
    ((differentiableOn_const 1).sub differentiableOn_id).pow 4
  exact h1.div h2 (fun q hq => pow_ne_zero 4 (b36_r_one_sub_ne hq))

/-- `h(0) = φ(a)`. -/
theorem b36_r_hfun_zero (φ : ℂ → ℂ) (a : ℂ) : b36_r_hfun φ a 0 = φ a := by
  simp [b36_r_hfun, b36_r_cay_conj_zero]

/-- The Bers-norm bound `|φ(w)| (Im w)² ≤ M` gives `|h(q)| (1 - |q|²)² ≤ M/(Im a)²`. -/
theorem b36_r_hfun_bound {φ : ℂ → ℂ} {M : ℝ} (hM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ M)
    {a : ℂ} (ha : a ∈ lowerHalf) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    ‖b36_r_hfun φ a q‖ * (1 - ‖q‖ ^ 2) ^ 2 ≤ M / a.im ^ 2 := by
  have hu := b36_r_one_sub_ne hq
  have hw := b36_r_cay_mem_lower ha hq
  have him := b36_r_cay_im (conj a) hu
  rw [conj_im, neg_neg] at him
  have ha' : a.im ≠ 0 := ne_of_lt ha
  have hnu : 0 < ‖1 - q‖ := norm_pos_iff.2 hu
  have key : ‖b36_r_hfun φ a q‖ * (1 - ‖q‖ ^ 2) ^ 2
      = ‖φ (b36_r_cay (conj a) q)‖ * (b36_r_cay (conj a) q).im ^ 2 / a.im ^ 2 := by
    rw [him, b36_r_hfun, norm_div, norm_pow]
    field_simp
  rw [key]
  exact div_le_div_of_nonneg_right (hM _ hw) (sq_nonneg _)

/-- `|G(q)| ≤ M/(4 (Im a)²)` on the disc. -/
theorem b36_r_G_bound {φ : ℂ → ℂ} {M : ℝ} (hM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ M)
    {a : ℂ} (ha : a ∈ lowerHalf) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) :
    ‖b36_r_G φ a q‖ ≤ M / a.im ^ 2 / 4 := by
  have hq' : conj q ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right, Complex.norm_conj] using hq
  have hb := b36_r_hfun_bound hM ha hq'
  rw [Complex.norm_conj] at hb
  have hq1 : ‖q‖ < 1 := by simpa [mem_ball, dist_zero_right] using hq
  have h1 : ‖(1 : ℂ) - q * conj q‖ = 1 - ‖q‖ ^ 2 := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    nlinarith [norm_nonneg q]
  unfold b36_r_G
  rw [norm_mul, norm_mul, norm_pow, h1]
  have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [h4]
  nlinarith [norm_nonneg (b36_r_hfun φ a (conj q))]

/-- The polar integrand of `G` is integrable on `(0, 1) × (-π, π)`. -/
theorem b36_r_polar_integrable {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {M : ℝ}
    (hM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ M) {a : ℂ} (ha : a ∈ lowerHalf) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * b36_r_G φ a (Complex.polarCoord.symm p + 0))
      (Ioo 0 1 ×ˢ Ioo (-π) π) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have hc : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  have hmaps : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π,
      Complex.polarCoord.symm p + 0 ∈ ball (0 : ℂ) 1 := by
    intro p hp
    rw [add_zero, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2
  have hGc : ContinuousOn (b36_r_G φ a) (ball (0 : ℂ) 1) := by
    have hh := (b36_r_hfun_diff hφ ha).continuousOn
    have hc2 : ContinuousOn (fun q : ℂ => b36_r_hfun φ a (conj q)) (ball (0 : ℂ) 1) :=
      hh.comp Complex.continuous_conj.continuousOn (fun q hq => by
        simpa [mem_ball, dist_zero_right, Complex.norm_conj] using hq)
    exact ContinuousOn.mul (by fun_prop) hc2
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (p.1 : ℂ) * b36_r_G φ a (Complex.polarCoord.symm p + 0))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
      (hGc.comp (hc.add continuous_const).continuousOn hmaps)
  have hfin : volume (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) < ⊤ :=
    ((Metric.isBounded_Ioo 0 1).prod (Metric.isBounded_Ioo _ _)).measure_lt_top
  refine Integrable.mono' (g := fun _ => M / a.im ^ 2 / 4) (integrableOn_const hfin.ne)
    (hcont.aestronglyMeasurable hS) ?_
  refine ae_restrict_of_forall_mem hS fun p hp => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1.1]
  have hb := b36_r_G_bound hM ha (hmaps p hp)
  calc p.1 * ‖b36_r_G φ a (Complex.polarCoord.symm p + 0)‖ ≤ 1 * (M / a.im ^ 2 / 4) :=
        mul_le_mul hp.1.2.le hb (norm_nonneg _) zero_le_one
    _ = M / a.im ^ 2 / 4 := one_mul _

/-- Mean value property along the reversed circle:
`∫₀^{2π} h(r e^{-iθ}) dθ = 2π h(0)` for `h` holomorphic on the disc and `0 ≤ r < 1`. -/
theorem b36_r_circle_neg {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 r (-θ)) = 2 * π * h 0 := by
  have hper : Function.Periodic (fun θ => h (circleMap 0 r θ)) (2 * π) := fun θ => by
    simp only
    rw [periodic_circleMap]
  have e1 : ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 r (-θ))
      = ∫ θ in -(2 * π)..-0, h (circleMap 0 r θ) :=
    intervalIntegral.integral_comp_neg (fun θ => h (circleMap 0 r θ))
  have e2 : ∫ θ in -(2 * π)..0, h (circleMap 0 r θ)
      = ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 r θ) := by
    have := hper.intervalIntegral_add_eq (-(2 * π)) 0
    simpa using this
  have hsub : closure (ball (0 : ℂ) |r|) ⊆ ball (0 : ℂ) 1 :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by rwa [abs_of_nonneg hr0]))
  have hmv : Real.circleAverage h 0 r = h 0 :=
    DiffContOnCl.circleAverage (hh.mono hsub).diffContOnCl
  rw [Real.circleAverage_def] at hmv
  rw [e1, neg_zero, e2]
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  calc ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 r θ)
      = (2 * π : ℝ) • ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 r θ)) :=
        (smul_inv_smul₀ h2π _).symm
    _ = (2 * π : ℝ) • h 0 := by rw [hmv]
    _ = 2 * π * h 0 := by rw [Complex.real_smul]; push_cast; ring

/-- The angular integral of the polar integrand of `G`, for `0 ≤ r ≤ 1`. -/
theorem b36_r_inner {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {a : ℂ}
    (ha : a ∈ lowerHalf) {r : ℝ} (hr : r ∈ Set.uIcc (0 : ℝ) 1) :
    ∫ θ in (0 : ℝ)..2 * π, (r : ℂ) * b36_r_G φ a (circleMap 0 r θ)
      = ((r * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((1 / 4 : ℂ) * (2 * π * φ a)) := by
  rw [Set.uIcc_of_le zero_le_one] at hr
  have hpt : ∀ θ : ℝ, (r : ℂ) * b36_r_G φ a (circleMap 0 r θ)
      = ((r * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * (1 / 4 : ℂ) * b36_r_hfun φ a (circleMap 0 r (-θ)) := by
    intro θ
    unfold b36_r_G
    rw [Complex.mul_conj', norm_circleMap_zero, ← Complex.ofReal_pow, sq_abs, conj_circleMap_zero]
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  rcases eq_or_lt_of_le hr.2 with h1 | h1
  · subst h1
    simp
  · rw [b36_r_circle_neg (b36_r_hfun_diff hφ ha) hr.1 h1, b36_r_hfun_zero]
    ring

/-- `∫₀¹ r (1 - r²)² dr = 1/6`. -/
theorem b36_r_radial : ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ 2 = 1 / 6 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ 3 / 6) (x * (1 - x ^ 2) ^ 2) x := by
    intro x _
    have h := (((hasDerivAt_pow 2 x).const_sub 1).pow 3).neg.div_const 6
    convert h using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-- **Bers reproducing formula** (weight `y²`, lower half-plane): for `φ` holomorphic on `𝕃` with
`sup_𝕃 |φ| y² ≤ M` and `z ∈ 𝕃`, `∬_ℍ (Im ζ)² φ(ζ̄)/(ζ - z)⁴ dξ dη = (π/12) φ(z)`. -/
theorem b36_r_reproducing {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {M : ℝ}
    (hM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ M) {z : ℂ} (hz : z ∈ lowerHalf) :
    ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4 = (π / 12 : ℂ) * φ z := by
  have e1 : ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4
      = ∫ q in ball (0 : ℂ) 1, b36_r_G φ z q := by
    rw [← b36_r_image hz, ahP_integral_image isOpen_ball (b36_r_differentiableOn z)
      (b36_r_injOn hz)]
    exact setIntegral_congr_fun measurableSet_ball (fun q hq => b36_r_kernel hz φ hq)
  rw [e1, setIntegral_ball_eq_polar' 0 zero_le_one (b36_r_polar_integrable hφ hM hz),
    intervalIntegral.integral_congr (fun r hr => b36_r_inner hφ hz hr),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, b36_r_radial]
  push_cast
  ring

/-- **Lemma 36.2 (part 2)**: the operator `F(φ)(z) = c y² φ(z̄)` (`z ∈ ℍ`, the reflected differential,
cf. Lemma 33.3) satisfies `P ∘ F = id` on `Q(G, 𝕃)` for a suitable constant `c`; hence `DΦ(0) = P`
is surjective onto `Q(G, 𝕃)` with closed kernel, and `Φ⁻¹(0)` is an analytic submanifold (inverse
function theorem).  `Q(G, 𝕃)` is the Banach space of the book: `φ` has finite norm `sup y²|φ|` (for a compact
surface this is automatic; `automorphicQD` alone does not require it). -/
theorem lemma36_2_right_inverse (hΓ : IsFuchsian Γ) :
    ∃ c : ℂ, ∀ φ ∈ automorphicQD Γ, bersNormL φ < ⊤ → ∀ z ∈ lowerHalf,
      bersDerivative (fun ζ => c * (ζ.im : ℂ) ^ 2 * φ (conj ζ)) z = φ z := by
  have _hΓ := hΓ
  refine ⟨-2, fun φ hφ hnorm z hz => ?_⟩
  have hd : DifferentiableOn ℂ φ lowerHalf := hφ.1
  have hM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ (bersNormL φ).toReal := by
    intro w hw
    have h1 : ENNReal.ofReal (‖φ w‖ * w.im ^ 2) ≤ bersNormL φ :=
      le_iSup₂ (f := fun w (_ : w ∈ lowerHalf) => ENNReal.ofReal (‖φ w‖ * w.im ^ 2)) w hw
    exact (ENNReal.ofReal_le_iff_le_toReal hnorm.ne).1 h1
  have hint : ∀ ζ : ℂ, (-2 : ℂ) * (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4
      = -2 * ((ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4) := fun ζ => by ring
  unfold bersDerivative
  simp_rw [hint]
  rw [integral_const_mul, b36_r_reproducing hd hM hz]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

/-- §36.3 (平凡的): `μ ∈ M(ℍ, G)` is trivial if it is the complex dilatation of a quasiconformal
self-map of `S` homotopic to the identity modulo the boundary, i.e. `f_μ|ℝ = id`. -/
def IsTrivialBeltrami (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ : BeltramiGamma Γ) : Prop :=
  ∀ x : ℝ, normalizedSolution μ.1.1 x = x

/-- **Lemma 36.2 (part 3)**: `N = Φ⁻¹(0)`: `μ` is trivial iff `φ_μ = 0` (`f_μ|𝕃` is then a Möbius
transformation `A`, and `A⁻¹ ∘ f_μ` is the identity on `𝕃`, hence on `ℝ`; conversely a trivial `μ`
has `f_μ = A ∘ w` with `w = id` on `𝕃`). -/
theorem lemma36_2_trivial_iff (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) :
    IsTrivialBeltrami Γ μ ↔ bersFunction μ.1.1 = 0 := by
  have _hΓ := hΓ
  have h0 : bersFunction (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [bersFunction, bB_l_normalizedSolution_zero]
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz, bB_l_schwarzian_id]
      rfl
    · rw [indicator_of_notMem hz]
      rfl
  constructor
  · intro h
    have hrel : teichSetoid μ.1 ⟨0, bB_l_zero_mem⟩ := by
      intro x
      show normalizedSolution μ.1.1 x = normalizedSolution (0 : ℂ → ℂ) x
      rw [bB_l_normalizedSolution_zero, h x]
      rfl
    rw [bersFunction_eq_of_equiv hrel]
    exact h0
  · intro h x
    have hrel : teichSetoid μ.1 ⟨0, bB_l_zero_mem⟩ := by
      refine bA_equiv_of_schwarzian_eq fun z hz => ?_
      have h1 := congrFun h z
      rw [bersFunction, indicator_of_mem hz] at h1
      show schwarzian (normalizedSolution μ.1.1) z = schwarzian (normalizedSolution (0 : ℂ → ℂ)) z
      rw [h1, bB_l_normalizedSolution_zero, bB_l_schwarzian_id]
      rfl
    have := hrel x
    change normalizedSolution μ.1.1 x = normalizedSolution (0 : ℂ → ℂ) x at this
    rw [this, bB_l_normalizedSolution_zero]
    rfl

/-- §36.3 (局部平凡的): `μ` is locally trivial if it lies in the tangent space `T₀N = ker DΦ(0)`. -/
def IsLocallyTrivialBeltrami (μ : ℂ → ℂ) : Prop := ∀ z ∈ lowerHalf, bersDerivative μ z = 0

/-! ## BLOCK A — install just before the docstring of `lemma36_2_kernel_orthogonal` (batch A)

Uses from S36 only declarations above that point (`IsFundamentalDomainH`, `integrableAutomorphicQD`,
`beltramiPairing`, `hamiltonNorm`, `bersDerivative`, `b36_*`, `c36_*`, …). -/

/-! ### A.1 Proved helpers from scout B (`h36_reductions.lean`, renamed `h36_` → `h36p_`): the area mean
value and the group action -/

/-- Polar coordinates about `z₀` over a measurable set `U` (the proof of `lintegral_unitDisc_eq_polar`
with `unitDisc` replaced by `U`). -/
theorem h36p_lintegral_eq_polar (z₀ : ℂ) {U : Set ℂ} (hU : MeasurableSet U) {G : ℂ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ z in U, G z = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal ρ * U.indicator G (circleMap z₀ ρ θ) := by
  rw [← lintegral_indicator hU, ← lintegral_add_right_eq_self (U.indicator G) z₀]
  have hpolar := Complex.lintegral_comp_polarCoord_symm (fun w => U.indicator G (w + z₀))
  rw [← hpolar]
  simp_rw [smul_eq_mul]
  have hcont : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * U.indicator G (Complex.polarCoord.symm p + z₀))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    (measurable_fst.ennreal_ofReal.mul
      ((hG.indicator hU).comp (hcont.measurable.add_const z₀))).aemeasurable
  rw [show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  refine lintegral_congr fun ρ => lintegral_congr fun θ => ?_
  congr 2
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  push_cast
  ring

/-- The circle mean inequality `2π |φ(c)| ≤ ∫_{-π}^{π} |φ(c + r e^{iθ})| dθ` for `φ` holomorphic on a
set containing the closed disc (as `h35_circle_mean_le`, for an arbitrary domain). -/
theorem h36p_circle_mean_le {φ : ℂ → ℂ} {U : Set ℂ} (hφ : DifferentiableOn ℂ φ U) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ U) :
    ENNReal.ofReal (2 * π * ‖φ c‖) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ‖φ (circleMap c r θ)‖ := by
  have hdc : DiffContOnCl ℂ φ (ball c |r|) := by
    rw [abs_of_pos hr]
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hr.ne']
    exact hφ.mono hsub
  have hmv : Real.circleAverage φ c r = φ c := hdc.circleAverage
  have hle : ‖φ c‖ ≤ Real.circleAverage (fun z => ‖φ z‖) c r := by
    rw [← hmv]
    exact Real.norm_circleAverage_le_circleAverage_norm
  have hcont : Continuous fun θ : ℝ => ‖φ (circleMap c r θ)‖ := by
    refine (continuous_norm.comp_continuousOn (hφ.continuousOn.mono hsub)).comp_continuous
      (continuous_circleMap c r) fun θ => ?_
    exact sphere_subset_closedBall (circleMap_mem_sphere c hr.le θ)
  have hint : ∫ θ in (0 : ℝ)..2 * π, ‖φ (circleMap c r θ)‖ =
      2 * π * Real.circleAverage (fun z => ‖φ z‖) c r := by
    rw [Real.circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]
  have h2pi : 0 ≤ 2 * π := Real.two_pi_pos.le
  have hlin : ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, ‖φ (circleMap c r θ)‖) =
      ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal ‖φ (circleMap c r θ)‖ := by
    rw [intervalIntegral.integral_of_le h2pi,
      ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun θ => norm_nonneg _)]
    exact setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hper : Function.Periodic (fun θ : ℝ => ENNReal.ofReal ‖φ (circleMap c r θ)‖) (2 * π) :=
    fun θ => by simp only [periodic_circleMap c r θ]
  rw [← lintegral_Ioo_zero_two_pi_eq_of_periodic hper, ← hlin, hint]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

/-- **Local mean value bound**: `π s² |φ(c)| ≤ ∬_{B(c, s)} |φ|` for `φ` holomorphic on a set
containing the closed disc `B̄(c, s)`. -/
theorem h36p_meanvalue {φ : ℂ → ℂ} {U : Set ℂ} (hφ : DifferentiableOn ℂ φ U) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hsub : closedBall c s ⊆ U) :
    ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖φ c‖ ≤ ∫⁻ z in ball c s, ENNReal.ofReal ‖φ z‖ := by
  classical
  set G : ℂ → ℝ≥0∞ := (ball c s).indicator (fun z => ENNReal.ofReal ‖φ z‖) with hGdef
  have hGm : Measurable G := by
    rw [hGdef, ← Set.piecewise_eq_indicator]
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      (hφ.continuousOn.mono (ball_subset_closedBall.trans hsub)).norm).measurable_piecewise
      continuousOn_const measurableSet_ball
  have hGeq : ∫⁻ z in ball c s, ENNReal.ofReal ‖φ z‖ = ∫⁻ z in ball c s, G z :=
    setLIntegral_congr_fun measurableSet_ball fun z hz => by rw [hGdef, indicator_of_mem hz]
  rw [hGeq, h36p_lintegral_eq_polar c measurableSet_ball hGm]
  have hpt : ∀ r ∈ Ioo (0 : ℝ) s, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖φ c‖) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * (ball c s).indicator G (circleMap c r θ) := by
    intro r hr
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (h36p_circle_mean_le hφ hr.1 ((closedBall_subset_closedBall hr.2.le).trans hsub)).trans
      (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    have hmem : circleMap c r θ ∈ ball c s := by
      rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr.1]
      exact hr.2
    rw [indicator_of_mem hmem, hGdef, indicator_of_mem hmem]
  calc ENNReal.ofReal (π * s ^ 2) * ENNReal.ofReal ‖φ c‖
      = (∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r) * ENNReal.ofReal (2 * π * ‖φ c‖) := by
        have hr : ∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r = ENNReal.ofReal (s ^ 2 / 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((Continuous.integrableOn_Icc (f := fun r : ℝ => r) (a := 0) (b := s) continuous_id).mono_set
              Ioo_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r hr => hr.1.le))]
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le, integral_id]
          ring_nf
        rw [hr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ∫⁻ r in Ioo (0 : ℝ) s, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖φ c‖) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) s, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ball c s).indicator G (circleMap c r θ) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ball c s).indicator G (circleMap c r θ) :=
        lintegral_mono_set Ioo_subset_Ioi_self

/-! ### The group action: Möbius invariance of `|φ| dx dy`, countability, local `L¹` bounds -/

/-- The Möbius map `z ↦ (a z + b)/(c z + d)` of `γ ∈ SL(2, ℝ)`, as a function `ℂ → ℂ`. -/
def h36p_m (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

/-- On `ℍ`, `h36p_m γ` is the action of `γ`. -/
theorem h36p_m_coe (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    h36p_m γ τ = ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [h36p_m]

/-- `h36p_m γ` maps `ℍ` into `ℍ`. -/
theorem h36p_m_mem (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_m γ z ∈ upperHalf := by
  have h := h36p_m_coe γ ⟨z, hz⟩
  simp only at h
  rw [h]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).coe_im_pos

/-- The derivative of `h36p_m γ` at a point of `ℍ`. -/
theorem h36p_m_hasDerivAt (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    HasDerivAt (h36p_m γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z := by
  have hdet := b33_d_det γ
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hz))
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
  exact k24_d_deriv hdetC hden

/-- `h36p_m γ` is measurable. -/
theorem h36p_m_measurable (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Measurable (h36p_m γ) := by
  unfold h36p_m
  fun_prop

/-- `h36p_m γ` is injective on `ℍ`. -/
theorem h36p_m_injOn (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : InjOn (h36p_m γ) upperHalf := by
  intro z₁ h₁ z₂ h₂ h
  have e1 := h36p_m_coe γ ⟨z₁, h₁⟩
  have e2 := h36p_m_coe γ ⟨z₂, h₂⟩
  simp only at e1 e2
  have h' : (γ • (⟨z₁, h₁⟩ : UpperHalfPlane)) = γ • (⟨z₂, h₂⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext (by rw [← e1, ← e2]; exact h)
  have := smul_left_cancel γ h'
  exact congrArg UpperHalfPlane.coe this

/-- **Invariance of `|φ| dx dy`**: for `γ ∈ Γ`, `φ ∈ integrableAutomorphicQD Γ F` and measurable
`E ⊆ ℍ`, `∬_{γ(E)} |φ| = ∬_E |φ|`. -/
theorem h36p_lintegral_image_m {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {E : Set ℂ} (hE : MeasurableSet E)
    (hEH : E ⊆ upperHalf) :
    ∫⁻ w in h36p_m γ '' E, ENNReal.ofReal ‖φ w‖ = ∫⁻ z in E, ENNReal.ofReal ‖φ z‖ := by
  have hdet := b33_d_det γ
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE
    (fun z hz => ((h36p_m_hasDerivAt γ (hEH hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((h36p_m_injOn γ).mono hEH)]
  refine setLIntegral_congr_fun hE fun z hz => ?_
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hEH hz))
  have hA := hφ.2.2 γ hγ z (hEH hz)
  have hφm : φ (h36p_m γ z) = φ z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
    rw [← hA, div_mul_cancel₀ _ (pow_ne_zero _ hden)]
    rfl
  simp only [det_restrictScalars_toSpanSingleton]
  rw [hφm, abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  rw [norm_mul, norm_pow, norm_div, norm_one, norm_pow]
  field_simp

/-- A Fuchsian group is countable (it is covered by the finite sets `{γ | γ(C_n) ∩ C_n ≠ ∅}` for the
compact boxes `C_n`). -/
theorem h36p_countable (hΓ : IsFuchsian Γ) : (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Countable := by
  set C : ℕ → Set UpperHalfPlane :=
    fun n => {τ : UpperHalfPlane | 1 / ((n : ℝ) + 1) ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ (n : ℝ) + 1} with hCdef
  have hC : ∀ n, IsCompact (C n) := fun n => k24_c_isCompact_box (by positivity)
  have hI : ∀ n : ℕ, UpperHalfPlane.I ∈ C n := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [UpperHalfPlane.I_im]
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rw [UpperHalfPlane.coe_I, Complex.norm_I]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsub : (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) ⊆
      ⋃ n : ℕ, {γ ∈ Γ | ((γ • ·) '' C n ∩ C n).Nonempty} := by
    intro γ hγ
    set τ := γ • UpperHalfPlane.I
    have hτ := τ.im_pos
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖(τ : ℂ)‖ (1 / τ.im))
    refine mem_iUnion.2 ⟨n, hγ, τ, ⟨UpperHalfPlane.I, hI n, rfl⟩, ?_, ?_⟩
    · have h1 : 1 / τ.im ≤ (n : ℝ) + 1 := by linarith [le_max_right ‖(τ : ℂ)‖ (1 / τ.im)]
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hτ] at h1
      linarith
    · linarith [le_max_left ‖(τ : ℂ)‖ (1 / τ.im)]
  exact (countable_iUnion fun n => (hΓ (C n) (hC n)).countable).mono hsub

/-- The closed disc `B̄(z, Im z / 2)` lies in `ℍ`. -/
theorem h36p_closedBall_sub {z : ℂ} (hz : z ∈ upperHalf) : closedBall z (z.im / 2) ⊆ upperHalf := by
  intro w hw
  have hz' : 0 < z.im := hz
  have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [mem_closedBall, dist_eq_norm] at hw
  show 0 < w.im
  have := (abs_le.1 (h1.trans hw)).1
  linarith

/-- **Local `L¹` bound** for automorphic `φ`: `∬_{B̄(z, Im z/2)} |φ| ≤ N ∬_F |φ|`, with `N` the number of
`γ ∈ Γ` moving the disc to meet itself (finite since `Γ` is Fuchsian).  Only the covering property of
`F` is used. -/
theorem h36p_local_L1 (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {z : ℂ}
    (hz : z ∈ upperHalf) :
    ∃ N : ℕ, ∀ φ ∈ integrableAutomorphicQD Γ F,
      ∫⁻ w in closedBall z (z.im / 2), ENNReal.ofReal ‖φ w‖ ≤ N * phiArea φ F := by
  obtain ⟨hFH, hFm, hcov, -⟩ := hF
  set B := closedBall z (z.im / 2) with hBdef
  have hBH : B ⊆ upperHalf := h36p_closedBall_sub hz
  set C : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' B with hCdef
  have hC : IsCompact C := by
    have hsub : B ⊆ range UpperHalfPlane.coe := fun w hw => ⟨⟨w, hBH hw⟩, rfl⟩
    exact (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff hsub).2
      (isCompact_closedBall z _)
  set S := {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty} with hSdef
  have hS : S.Finite := hΓ C hC
  refine ⟨S.ncard, fun φ hφ => ?_⟩
  have hcount := h36p_countable hΓ
  have : Countable Γ := hcount.to_subtype
  set g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ‖φ w‖ with hg
  -- the translates `γ⁻¹(F)` cover `B`
  have hcover : B ⊆ ⋃ γ : Γ, (B ∩ h36p_m γ ⁻¹' F) := by
    intro w hw
    obtain ⟨γ, hγ, hγF⟩ := hcov ⟨w, hBH hw⟩
    refine mem_iUnion.2 ⟨⟨γ, hγ⟩, hw, ?_⟩
    show h36p_m γ w ∈ F
    have := h36p_m_coe γ ⟨w, hBH hw⟩
    simp only at this
    rw [this]
    exact hγF
  -- the images `γ(B)` are compact, hence measurable
  have hBimg : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, MeasurableSet (h36p_m γ '' B) := by
    intro γ
    have hcont : ContinuousOn (h36p_m γ) B := fun w hw =>
      (h36p_m_hasDerivAt γ (hBH hw)).continuousAt.continuousWithinAt
    exact ((isCompact_closedBall z _).image_of_continuousOn hcont).isClosed.measurableSet
  have hgF : AEMeasurable g (volume.restrict F) :=
    ((hφ.1.continuousOn.mono hFH).aestronglyMeasurable hFm).aemeasurable.norm.ennreal_ofReal
  -- step 1: split over the cover and move each piece by `γ`
  have hstep : ∀ γ : Γ, ∫⁻ w in B ∩ h36p_m γ ⁻¹' F, g w ≤
      ∫⁻ w in F, (h36p_m γ '' B).indicator g w := by
    intro γ
    have hE : MeasurableSet (B ∩ h36p_m γ ⁻¹' F) :=
      measurableSet_closedBall.inter (h36p_m_measurable γ hFm)
    rw [← h36p_lintegral_image_m hφ γ.2 hE (inter_subset_left.trans hBH),
      setLIntegral_indicator (hBimg γ)]
    refine lintegral_mono_set ?_
    rintro _ ⟨w, ⟨hwB, hwF⟩, rfl⟩
    exact ⟨mem_image_of_mem _ hwB, hwF⟩
  -- step 2: the multiplicity of the cover `{γ(B)}` is at most `#S`
  have hmult : ∀ w ∈ F, ∑' γ : Γ, (h36p_m γ '' B).indicator g w ≤ S.ncard * g w := by
    intro w hwF
    by_cases hex : ∃ γ₀ : Γ, w ∈ h36p_m γ₀ '' B
    · obtain ⟨γ₀, b₀, hb₀, hb₀w⟩ := hex
      set T : Set Γ := {γ | ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) ∈ S} with hTdef
      have hinj : InjOn (fun γ : Γ => ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ)) T := by
        intro a _ b _ hab
        exact Subtype.ext (mul_left_cancel hab)
      have hTfin : T.Finite := hS.preimage hinj
      have hTcard : T.ncard ≤ S.ncard :=
        Set.ncard_le_ncard_of_injOn _ (fun a ha => ha) hinj hS
      have hsupp : ∀ γ ∉ hTfin.toFinset, (h36p_m γ '' B).indicator g w = 0 := by
        intro γ hγT
        rw [Set.Finite.mem_toFinset] at hγT
        refine indicator_of_notMem ?_ _
        rintro ⟨b, hb, hbw⟩
        apply hγT
        -- `γ • b = γ₀ • b₀` in `ℍ`
        have e1 := h36p_m_coe γ ⟨b, hBH hb⟩
        have e0 := h36p_m_coe γ₀ ⟨b₀, hBH hb₀⟩
        simp only at e1 e0
        have heq : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
            (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b₀, hBH hb₀⟩ : UpperHalfPlane) :=
          UpperHalfPlane.ext (by rw [← e1, ← e0, hbw, hb₀w])
        have hδ : ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
            ⟨b₀, hBH hb₀⟩ := by
          rw [mul_smul, heq, inv_smul_smul]
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ γ₀.2) γ.2, _, ⟨⟨b, hBH hb⟩,
          (show (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C from hb), rfl⟩, ?_⟩
        show ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C
        rw [hδ]
        exact hb₀
      rw [tsum_eq_sum hsupp]
      calc ∑ γ ∈ hTfin.toFinset, (h36p_m γ '' B).indicator g w
          ≤ ∑ _γ ∈ hTfin.toFinset, g w :=
            Finset.sum_le_sum fun γ _ => indicator_le_self _ _ _
        _ = hTfin.toFinset.card * g w := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.ncard * g w := by
            gcongr
            rw [← Set.ncard_eq_toFinset_card T hTfin]
            exact_mod_cast hTcard
    · push Not at hex
      have h0 : ∀ γ : Γ, (h36p_m γ '' B).indicator g w = 0 := fun γ =>
        indicator_of_notMem (hex γ) _
      simp only [h0, tsum_zero]
      exact bot_le
  calc ∫⁻ w in B, g w
      ≤ ∫⁻ w in ⋃ γ : Γ, (B ∩ h36p_m γ ⁻¹' F), g w := lintegral_mono_set hcover
    _ ≤ ∑' γ : Γ, ∫⁻ w in B ∩ h36p_m γ ⁻¹' F, g w := lintegral_iUnion_le _ _
    _ ≤ ∑' γ : Γ, ∫⁻ w in F, (h36p_m γ '' B).indicator g w := ENNReal.tsum_le_tsum hstep
    _ = ∫⁻ w in F, ∑' γ : Γ, (h36p_m γ '' B).indicator g w :=
        (lintegral_tsum fun γ : Γ => hgF.indicator (hBimg γ)).symm
    _ ≤ ∫⁻ w in F, (S.ncard : ℝ≥0∞) * g w := setLIntegral_mono' hFm hmult
    _ = S.ncard * phiArea φ F := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
        rfl

/-! ### A.2 The multiplicity `|Γ ∩ {±1}|` and the Poincaré series `Θ` -/

/-- The multiplicity `m = |Γ ∩ {±1}| ∈ {1, 2}` with which `Γ ⊆ SL(2, ℝ)` counts a Möbius map is positive:
`⟨-1⟩ = {±1}` is finite and contains `1`. -/
theorem h36p_mult_pos : 0 < Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) := by
  have h1 : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
  have h2 : Finite ↥(Γ ⊓ Subgroup.zpowers (-1)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : Γ ⊓ Subgroup.zpowers (-1) ≤ Subgroup.zpowers (-1)))
  exact Nat.card_pos

/-- The Poincaré series `Θf(z) = Σ_{γ ∈ Γ} f(γz) γ'(z)²`, `γ'(z)² = (cz + d)⁻⁴`, summed over the elements
of `Γ ⊆ SL(2, ℝ)` (a Möbius map is counted `m = |Γ ∩ {±1}|` times): the series of
`poincare_series_surjective`. -/
def h36p_theta (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' γ : Γ, f ((γ.1 0 0 * z + γ.1 0 1) / (γ.1 1 0 * z + γ.1 1 1)) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4

/-! ### A.3 Stubs of prover P1 (the a.e. tiling) -/

/-- `h36p_m γ⁻¹` inverts `h36p_m γ` on `ℍ`. -/
theorem h36p_a_inv_m (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_m γ⁻¹ (h36p_m γ z) = z := by
  have e1 := h36p_m_coe γ ⟨z, hz⟩
  simp only at e1
  rw [e1, h36p_m_coe γ⁻¹ (γ • ⟨z, hz⟩), inv_smul_smul]

/-- Möbius preimages of null sets are null in `ℍ`: `volume (ℍ ∩ γ⁻¹(E)) = 0` when `volume E = 0`
(the set lies in the image of `E ∩ ℍ` under the smooth map `h36p_m γ⁻¹`). -/
theorem h36p_a_preimage_null (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {E : Set ℂ} (hE : volume E = 0) :
    volume (upperHalf ∩ h36p_m γ ⁻¹' E) = 0 := by
  have hsub : upperHalf ∩ h36p_m γ ⁻¹' E ⊆ h36p_m γ⁻¹ '' (E ∩ upperHalf) := by
    rintro z ⟨hz, hzE⟩
    exact ⟨h36p_m γ z, ⟨hzE, h36p_m_mem γ hz⟩, h36p_a_inv_m γ hz⟩
  refine measure_mono_null hsub ?_
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left hE)
  intro w hw
  exact ((h36p_m_hasDerivAt γ⁻¹ hw.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt

/-- An element `δ ≠ ±1` of `SL(2, ℝ)` has finitely many fixed points in `ℍ`: they are roots of the
nonzero polynomial `c z² + (d - a) z - b`. -/
theorem h36p_a_fix_finite {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h1 : δ ≠ 1) (h2 : δ ≠ -1) :
    {z : ℂ | z ∈ upperHalf ∧ h36p_m δ z = z}.Finite := by
  set p : Polynomial ℂ := Polynomial.C (δ 1 0 : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C ((δ 1 1 : ℂ) - δ 0 0) * Polynomial.X - Polynomial.C (δ 0 1 : ℂ) with hp
  have hdet := b33_d_det δ
  have hp0 : p ≠ 0 := by
    intro h0
    have e0 := congrArg (Polynomial.eval 0) h0
    have e1 := congrArg (Polynomial.eval 1) h0
    have e2 := congrArg (Polynomial.eval (-1)) h0
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero] at e0 e1 e2
    have r0 : δ 0 1 = 0 := by
      have : ((δ 0 1 : ℝ) : ℂ) = 0 := by linear_combination -e0
      exact_mod_cast this
    have r1 : δ 1 0 = 0 := by
      have : ((δ 1 0 : ℝ) : ℂ) = 0 := by linear_combination (e1 + e2) / 2 - e0
      exact_mod_cast this
    have r2 : δ 1 1 = δ 0 0 := by
      have : ((δ 1 1 : ℝ) : ℂ) = δ 0 0 := by linear_combination (e1 - e2) / 2
      exact_mod_cast this
    rw [r0, r1, r2] at hdet
    have hsq : (δ 0 0 - 1) * (δ 0 0 + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 hsq with ha | ha
    · apply h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [r0, r1, r2] <;> linarith
    · apply h2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [r0, r1, r2] <;> linarith
  refine (Polynomial.finite_setOfPred_isRoot hp0).subset ?_
  rintro z ⟨hz, hfix⟩
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hz))
  unfold h36p_m at hfix
  rw [div_eq_iff hden] at hfix
  show Polynomial.IsRoot p z
  simp only [hp, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  linear_combination -hfix

/-- The fixed points in `ℍ` of an element `δ ≠ ±1` of `SL(2, ℝ)` form a null set. -/
theorem h36p_a_fix_null {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h1 : δ ≠ 1) (h2 : δ ≠ -1) :
    volume {z : ℂ | z ∈ upperHalf ∧ h36p_m δ z = z} = 0 :=
  (h36p_a_fix_finite h1 h2).measure_zero volume

/-- **[P1, stub] A.e. uniqueness of the representative in `F`.**  For a.e. `z ∈ ℍ`, two elements
`γ₁, γ₂ ∈ Γ` moving `z` into `F` agree up to sign.  (Off the null set
`⋃_{γ ∈ Γ} γ⁻¹(F ∖ int F) ∪ ⋃_{δ ∈ Γ, δ ≠ ±1} Fix δ` — countable `Γ` (`h36p_countable`), Möbius maps preserve
null sets, `volume (F \ interior F) = 0`, a `δ ≠ ±1` has at most one fixed point in `ℍ` — both `γⱼ z` lie in
`int F`, the injectivity clause of `IsFundamentalDomainH` makes them equal, and `γ₂⁻¹ γ₁` fixes `z`.) -/
theorem h36p_ae_unique (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, h36p_m γ₁ z ∈ F → h36p_m γ₂ z ∈ F →
      γ₁ = γ₂ ∨ γ₁ = -γ₂ := by
  obtain ⟨-, -, -, hinj, hnull⟩ := hF
  have hcount := h36p_countable hΓ
  have hN1 : volume (⋃ γ ∈ (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      upperHalf ∩ h36p_m γ ⁻¹' (F \ interior F)) = 0 :=
    (measure_biUnion_null_iff hcount).2 fun γ _ => h36p_a_preimage_null γ hnull
  have hN2 : volume (⋃ δ ∈ {δ ∈ (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) | δ ≠ 1 ∧ δ ≠ -1},
      {z : ℂ | z ∈ upperHalf ∧ h36p_m δ z = z}) = 0 :=
    (measure_biUnion_null_iff (hcount.mono (sep_subset _ _))).2 fun δ hδ =>
      h36p_a_fix_null hδ.2.1 hδ.2.2
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN1, measure_eq_zero_iff_ae_notMem.1 hN2]
    with z h1 h2 hz γ₁ hγ₁ γ₂ hγ₂ hF1 hF2
  have hint : ∀ γ ∈ Γ, h36p_m γ z ∈ F → h36p_m γ z ∈ interior F := by
    intro γ hγ hγF
    by_contra hc
    exact h1 (mem_biUnion hγ ⟨hz, hγF, hc⟩)
  set τ : UpperHalfPlane := ⟨z, hz⟩ with hτ
  have e1 := h36p_m_coe γ₁ τ
  have e2 := h36p_m_coe γ₂ τ
  have e3 := h36p_m_coe (γ₂⁻¹ * γ₁) τ
  have heq : γ₁ • τ = γ₂ • τ := by
    refine hinj (γ₁ • τ) (γ₂ • τ) ?_ ?_ ⟨γ₂ * γ₁⁻¹, Γ.mul_mem hγ₂ (Γ.inv_mem hγ₁), ?_⟩
    · rw [← e1]; exact hint γ₁ hγ₁ hF1
    · rw [← e2]; exact hint γ₂ hγ₂ hF2
    · rw [mul_smul, inv_smul_smul]
  have hfix : (γ₂⁻¹ * γ₁) • τ = τ := by rw [mul_smul, heq, inv_smul_smul]
  have hfixz : h36p_m (γ₂⁻¹ * γ₁) z = z := by
    rw [hfix] at e3
    exact e3
  by_cases hd1 : γ₂⁻¹ * γ₁ = 1
  · exact Or.inl (inv_mul_eq_one.1 hd1).symm
  by_cases hd2 : γ₂⁻¹ * γ₁ = -1
  · right
    rw [inv_mul_eq_iff_eq_mul] at hd2
    rw [hd2, mul_neg_one]
  · exfalso
    apply h2
    exact mem_biUnion ⟨Γ.mul_mem (Γ.inv_mem hγ₂) hγ₁, hd1, hd2⟩ ⟨hz, hfixz⟩

/-- `-γ` and `γ` induce the same Möbius map. -/
theorem h36p_a_m_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : h36p_m (-γ) z = h36p_m γ z := by
  simp only [h36p_m, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
  rw [show -(γ 0 0 : ℂ) * z + -(γ 0 1 : ℂ) = -((γ 0 0 : ℂ) * z + γ 0 1) by ring,
    show -(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * z + γ 1 1) by ring, neg_div_neg_eq]

/-- For `F ⊆ ℍ`: `γ(F) = (γ⁻¹)⁻¹(F) ∩ ℍ`. -/
theorem h36p_a_image_eq (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {F : Set ℂ} (hFH : F ⊆ upperHalf) :
    h36p_m γ '' F = h36p_m γ⁻¹ ⁻¹' F ∩ upperHalf := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, h36p_m_mem γ (hFH hz)⟩
    show h36p_m γ⁻¹ (h36p_m γ z) ∈ F
    rw [h36p_a_inv_m γ (hFH hz)]
    exact hz
  · rintro ⟨hwF, hw⟩
    refine ⟨h36p_m γ⁻¹ w, hwF, ?_⟩
    have := h36p_a_inv_m γ⁻¹ hw
    rwa [inv_inv] at this

/-- Change of variables through `γ`: `∬_F g(γz) |cz + d|⁻⁴ = ∬_ℍ 𝟙_{γ⁻¹ w ∈ F} g(w)` (`F ⊆ ℍ`
measurable). -/
theorem h36p_a_cov (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {F : Set ℂ} (hFH : F ⊆ upperHalf)
    (hFm : MeasurableSet F) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in F, g (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      ∫⁻ w in upperHalf, (h36p_m γ⁻¹ ⁻¹' F).indicator g w := by
  have hdet := b33_d_det γ
  rw [setLIntegral_indicator (h36p_m_measurable _ hFm), ← h36p_a_image_eq γ hFH,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hFm
      (fun z hz => ((h36p_m_hasDerivAt γ (hFH hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      ((h36p_m_injOn γ).mono hFH)]
  refine setLIntegral_congr_fun hFm fun z hz => ?_
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hFH hz))
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), mul_comm]
  congr 2
  have hq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  rw [norm_div, norm_one, norm_pow]
  field_simp

/-- The elements of `⟨-1⟩ ⊆ SL(2, ℝ)` are `±1`. -/
theorem h36p_a_mem_zpowers {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : δ ∈ Subgroup.zpowers (-1)) :
    δ = 1 ∨ δ = -1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.even_or_odd k with he | ho
  · exact Or.inl he.neg_one_zpow
  · exact Or.inr ho.neg_one_zpow

/-- The count: if the `γ ∈ Γ` with `P γ` are exactly `±γ₀` (`γ₀ ∈ Γ`), then `Σ_{γ ∈ Γ} 𝟙_P(γ) x = m x`
with `m = |Γ ∩ {±1}|` (the set is the injective image `γ₀ (Γ ∩ ⟨-1⟩)`). -/
theorem h36p_a_count {P : Matrix.SpecialLinearGroup (Fin 2) ℝ → Prop}
    {γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ₀ : γ₀ ∈ Γ) (hP : ∀ γ ∈ Γ, P γ ↔ γ = γ₀ ∨ γ = -γ₀)
    (x : ℝ≥0∞) :
    ∑' γ : Γ, {γ : Γ | P γ.1}.indicator (fun _ => x) γ =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * x := by
  set K := Γ ⊓ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) with hK
  let φ : K → Γ := fun δ => ⟨γ₀ * δ.1, Γ.mul_mem hγ₀ (Subgroup.mem_inf.1 δ.2).1⟩
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))
  have hrange : {γ : Γ | P γ.1} = Set.range φ := by
    ext γ
    constructor
    · intro hγ
      rcases (hP γ.1 γ.2).1 hγ with h | h
      · exact ⟨⟨1, K.one_mem⟩, Subtype.ext (by simp [φ, h])⟩
      · have hm1 : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Γ := by
          have := Γ.mul_mem (Γ.inv_mem hγ₀) γ.2
          rwa [h, mul_neg, inv_mul_cancel] at this
        exact ⟨⟨-1, Subgroup.mem_inf.2 ⟨hm1, Subgroup.mem_zpowers _⟩⟩, Subtype.ext (by simp [φ, h])⟩
    · rintro ⟨δ, rfl⟩
      refine (hP _ (φ δ).2).2 ?_
      rcases h36p_a_mem_zpowers (Subgroup.mem_inf.1 δ.2).2 with h | h
      · left
        simp [φ, h]
      · right
        simp [φ, h]
  have h1 : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
  have h2 : Finite K :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : Γ ⊓ Subgroup.zpowers (-1) ≤ Subgroup.zpowers (-1)))
  rw [hrange, ← tsum_subtype, tsum_range (fun _ => x) hφ, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  simp

/-- **[P1, stub] Unfolding.**  For measurable `g ≥ 0`,
`Σ_{γ ∈ Γ} ∬_F g(γz) |γ'(z)|² = m ∬_ℍ g` with `m = |Γ ∩ {±1}|` and `|γ'(z)|² = |cz + d|⁻⁴`: change of variables
`∬_F g(γz)|γ'(z)|² = ∬_{γ(F)} g` (`γ` is injective on `ℍ ⊇ F`), and for a.e. `w ∈ ℍ` the set
`{γ ∈ Γ | γ⁻¹ w ∈ F}` is one class `{±γ₀} ∩ Γ` (covering clause of `IsFundamentalDomainH`, `h36p_ae_unique`),
of cardinality `m`. -/
theorem h36p_unfold (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∑' γ : Γ, ∫⁻ z in F, g (h36p_m γ.1 z) * ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in upperHalf, g z := by
  have hF' := hF
  obtain ⟨hFH, hFm, hcov, -, -⟩ := hF
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  calc ∑' γ : Γ, ∫⁻ z in F, g (h36p_m γ.1 z) * ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)
      = ∑' γ : Γ, ∫⁻ w in upperHalf, (h36p_m γ.1⁻¹ ⁻¹' F).indicator g w :=
        tsum_congr fun γ => h36p_a_cov γ.1 hFH hFm g
    _ = ∫⁻ w in upperHalf, ∑' γ : Γ, (h36p_m γ.1⁻¹ ⁻¹' F).indicator g w :=
        (lintegral_tsum fun γ => (hg.indicator (h36p_m_measurable _ hFm)).aemeasurable).symm
    _ = ∫⁻ w in upperHalf, (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * g w := by
        refine lintegral_congr_ae ?_
        filter_upwards [h36p_ae_unique hΓ hF', ae_restrict_mem isOpen_upperHalf.measurableSet]
          with w hu hw
        have hinv : ∑' γ : Γ, (h36p_m γ.1⁻¹ ⁻¹' F).indicator g w =
            ∑' γ : Γ, (h36p_m γ.1 ⁻¹' F).indicator g w :=
          (Equiv.inv Γ).tsum_eq (fun γ : Γ => (h36p_m γ.1 ⁻¹' F).indicator g w)
        have hrw : ∀ γ : Γ, (h36p_m γ.1 ⁻¹' F).indicator g w =
            {γ : Γ | h36p_m γ.1 w ∈ F}.indicator (fun _ => g w) γ := fun γ => by
          by_cases h : h36p_m γ.1 w ∈ F
          · rw [indicator_of_mem (show w ∈ h36p_m γ.1 ⁻¹' F from h),
              indicator_of_mem (show γ ∈ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
          · rw [indicator_of_notMem (show w ∉ h36p_m γ.1 ⁻¹' F from h),
              indicator_of_notMem (show γ ∉ {γ : Γ | h36p_m γ.1 w ∈ F} from h)]
        rw [hinv, tsum_congr hrw]
        obtain ⟨γ₀, hγ₀, hγ₀F⟩ := hcov ⟨w, hw⟩
        have hγ₀F' : h36p_m γ₀ w ∈ F := by
          have e := h36p_m_coe γ₀ ⟨w, hw⟩
          simp only at e
          rw [e]
          exact hγ₀F
        refine h36p_a_count (P := fun γ => h36p_m γ w ∈ F) hγ₀
          (fun γ hγ => ⟨fun h => hu γ hγ γ₀ hγ₀ h hγ₀F', ?_⟩) (g w)
        rintro (rfl | rfl)
        · exact hγ₀F'
        · show h36p_m (-γ₀) w ∈ F
          rw [h36p_a_m_neg]
          exact hγ₀F'
    _ = _ := lintegral_const_mul _ hg

/-! ### A.4 Stubs of prover P2 (the Poincaré series) -/

/-- On `ℍ` the Möbius maps compose: `h36p_m (γ δ) z = h36p_m γ (h36p_m δ z)`. -/
theorem h36p_b_m_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_m (γ * δ) z = h36p_m γ (h36p_m δ z) := by
  have e1 := h36p_m_coe (γ * δ) ⟨z, hz⟩
  have e2 := h36p_m_coe δ ⟨z, hz⟩
  have e3 := h36p_m_coe γ (δ • (⟨z, hz⟩ : UpperHalfPlane))
  simp only at e1 e2
  rw [e1, e2, e3, mul_smul]

/-- The cocycle of `j(γ, z) = cz + d`: `j(γ δ, z) = j(γ, δ z) j(δ, z)` on `ℍ`. -/
theorem h36p_b_j_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    (((γ * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
        (((γ * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ) =
      ((γ 1 0 : ℂ) * h36p_m δ z + γ 1 1) * ((δ 1 0 : ℂ) * z + δ 1 1) := by
  have hden := k24_d_den_ne_zero (b33_d_det δ) (ne_of_gt (show 0 < z.im from hz))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  unfold h36p_m
  push_cast
  field_simp
  ring

/-- `‖a / q⁴‖ = ‖a‖ ‖q‖⁻⁴`. -/
theorem h36p_b_norm_term (a q : ℂ) : ‖a / q ^ 4‖ = ‖a‖ * ‖q‖⁻¹ ^ 4 := by
  rw [norm_div, norm_pow, div_eq_mul_inv, inv_pow]

/-- **Möbius change of variables** on a measurable `E ⊆ ℍ`:
`∬_{γ(E)} G = ∬_E G(γz) |γ'(z)|²`, `|γ'(z)|² = |cz + d|⁻⁴`. -/
theorem h36p_b_lintegral_image (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {E : Set ℂ} (hE : MeasurableSet E)
    (hEH : E ⊆ upperHalf) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in h36p_m γ '' E, G w =
      ∫⁻ z in E, G (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE
    (fun z hz => ((h36p_m_hasDerivAt γ (hEH hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((h36p_m_injOn γ).mono hEH)]
  refine setLIntegral_congr_fun hE fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [mul_comm, abs_of_nonneg (sq_nonneg _)]
  congr 2
  rw [norm_div, norm_one, norm_pow]
  ring

/-- **Multiplicity of the translates** of `B̄ = B̄(z, Im z / 2)`: `Σ_{γ ∈ Γ} ∬_{γ(B̄)} G ≤ N ∬_ℍ G` for every
`G ≥ 0`, with `N` the number of `γ ∈ Γ` moving `B̄` to meet itself (finite since `Γ` is Fuchsian). -/
theorem h36p_b_mult (hΓ : IsFuchsian Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ N : ℕ, ∀ G : ℂ → ℝ≥0∞, AEMeasurable G (volume.restrict upperHalf) →
      ∑' γ : Γ, ∫⁻ w in h36p_m γ '' closedBall z (z.im / 2), G w ≤ N * ∫⁻ w in upperHalf, G w := by
  set B := closedBall z (z.im / 2) with hBdef
  have hBH : B ⊆ upperHalf := h36p_closedBall_sub hz
  set C : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' B with hCdef
  have hC : IsCompact C := by
    have hsub : B ⊆ range UpperHalfPlane.coe := fun w hw => ⟨⟨w, hBH hw⟩, rfl⟩
    exact (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff hsub).2
      (isCompact_closedBall z _)
  set S := {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty} with hSdef
  have hS : S.Finite := hΓ C hC
  refine ⟨S.ncard, fun G hG => ?_⟩
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  have hBimg : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, MeasurableSet (h36p_m γ '' B) := by
    intro γ
    have hcont : ContinuousOn (h36p_m γ) B := fun w hw =>
      (h36p_m_hasDerivAt γ (hBH hw)).continuousAt.continuousWithinAt
    exact ((isCompact_closedBall z _).image_of_continuousOn hcont).isClosed.measurableSet
  have hBimgH : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, h36p_m γ '' B ⊆ upperHalf := by
    rintro γ _ ⟨w, hw, rfl⟩
    exact h36p_m_mem γ (hBH hw)
  have hmult : ∀ w, ∑' γ : Γ, (h36p_m γ '' B).indicator G w ≤ S.ncard * G w := by
    intro w
    by_cases hex : ∃ γ₀ : Γ, w ∈ h36p_m γ₀ '' B
    · obtain ⟨γ₀, b₀, hb₀, hb₀w⟩ := hex
      set T : Set Γ := {γ | ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) ∈ S} with hTdef
      have hinj : InjOn (fun γ : Γ => ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ)) T := by
        intro a _ b _ hab
        exact Subtype.ext (mul_left_cancel hab)
      have hTfin : T.Finite := hS.preimage hinj
      have hTcard : T.ncard ≤ S.ncard :=
        Set.ncard_le_ncard_of_injOn _ (fun a ha => ha) hinj hS
      have hsupp : ∀ γ ∉ hTfin.toFinset, (h36p_m γ '' B).indicator G w = 0 := by
        intro γ hγT
        rw [Set.Finite.mem_toFinset] at hγT
        refine indicator_of_notMem ?_ _
        rintro ⟨b, hb, hbw⟩
        apply hγT
        have e1 := h36p_m_coe γ ⟨b, hBH hb⟩
        have e0 := h36p_m_coe γ₀ ⟨b₀, hBH hb₀⟩
        simp only at e1 e0
        have heq : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
            (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b₀, hBH hb₀⟩ : UpperHalfPlane) :=
          UpperHalfPlane.ext (by rw [← e1, ← e0, hbw, hb₀w])
        have hδ : ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
            ⟨b₀, hBH hb₀⟩ := by
          rw [mul_smul, heq, inv_smul_smul]
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ γ₀.2) γ.2, _, ⟨⟨b, hBH hb⟩,
          (show (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C from hb), rfl⟩, ?_⟩
        show ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C
        rw [hδ]
        exact hb₀
      rw [tsum_eq_sum hsupp]
      calc ∑ γ ∈ hTfin.toFinset, (h36p_m γ '' B).indicator G w
          ≤ ∑ _γ ∈ hTfin.toFinset, G w :=
            Finset.sum_le_sum fun γ _ => indicator_le_self _ _ _
        _ = hTfin.toFinset.card * G w := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.ncard * G w := by
            gcongr
            rw [← Set.ncard_eq_toFinset_card T hTfin]
            exact_mod_cast hTcard
    · push Not at hex
      have h0 : ∀ γ : Γ, (h36p_m γ '' B).indicator G w = 0 := fun γ =>
        indicator_of_notMem (hex γ) _
      simp only [h0, tsum_zero]
      exact bot_le
  calc ∑' γ : Γ, ∫⁻ w in h36p_m γ '' B, G w
      = ∑' γ : Γ, ∫⁻ w in upperHalf, (h36p_m γ '' B).indicator G w := by
        refine tsum_congr fun γ => ?_
        rw [setLIntegral_indicator (hBimg γ), inter_eq_left.2 (hBimgH γ)]
    _ = ∫⁻ w in upperHalf, ∑' γ : Γ, (h36p_m γ '' B).indicator G w :=
        (lintegral_tsum fun γ : Γ => hG.indicator (hBimg γ)).symm
    _ ≤ ∫⁻ w in upperHalf, (S.ncard : ℝ≥0∞) * G w := lintegral_mono fun w => hmult w
    _ = S.ncard * ∫⁻ w in upperHalf, G w := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)

/-- The terms `f(γz)/j(γ, z)⁴` of the Poincaré series are holomorphic on `ℍ`. -/
theorem h36p_b_term_diff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    DifferentiableOn ℂ (fun z => f (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4) upperHalf := by
  have hm : DifferentiableOn ℂ (h36p_m γ) upperHalf := fun z hz =>
    (h36p_m_hasDerivAt γ hz).differentiableAt.differentiableWithinAt
  refine (hf.comp hm fun z hz => h36p_m_mem γ hz).div (by fun_prop) fun z hz => pow_ne_zero _ ?_
  exact k24_d_den_ne_zero (b33_d_det γ) (ne_of_gt (show 0 < z.im from hz))

/-- **Local uniform bound** for the Poincaré series: on `B(z₀, Im z₀/4)` the terms are bounded by a summable
family (area mean value on `B(w, Im z₀/4)` and the multiplicity of the translates of `B̄(z₀, Im z₀/2)`). -/
theorem h36p_b_local (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤) {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf) :
    ∃ u : Γ → ℝ, Summable u ∧ ∀ γ : Γ, ∀ w ∈ ball z₀ (z₀.im / 4),
      ‖f (h36p_m γ.1 w) / ((γ.1 1 0 : ℂ) * w + γ.1 1 1) ^ 4‖ ≤ u γ := by
  have hz₀' : 0 < z₀.im := hz₀
  set r := z₀.im / 4 with hr
  have hr0 : 0 < r := by positivity
  set B := closedBall z₀ (z₀.im / 2) with hBdef
  have hBH : B ⊆ upperHalf := h36p_closedBall_sub hz₀
  obtain ⟨N, hN⟩ := h36p_b_mult hΓ hz₀
  set I : Γ → ℝ≥0∞ := fun γ =>
    ∫⁻ w in B, ENNReal.ofReal ‖f (h36p_m γ.1 w) / ((γ.1 1 0 : ℂ) * w + γ.1 1 1) ^ 4‖ with hI
  have hG : AEMeasurable (fun w => ENNReal.ofReal ‖f w‖) (volume.restrict upperHalf) :=
    (hf.continuousOn.aestronglyMeasurable isOpen_upperHalf.measurableSet).aemeasurable.norm.ennreal_ofReal
  have hIeq : ∀ γ : Γ, I γ = ∫⁻ w in h36p_m γ.1 '' B, ENNReal.ofReal ‖f w‖ := by
    intro γ
    rw [h36p_b_lintegral_image γ.1 measurableSet_closedBall hBH]
    refine lintegral_congr fun w => ?_
    rw [h36p_b_norm_term, ENNReal.ofReal_mul (norm_nonneg _)]
  have hsum : ∑' γ, I γ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hfA.ne) ?_
    simp_rw [hIeq]
    exact hN _ hG
  refine ⟨fun γ => (π * r ^ 2)⁻¹ * (I γ).toReal, (ENNReal.summable_toReal hsum).mul_left _, ?_⟩
  intro γ w hw
  have hIγ : I γ ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.le_tsum γ)
  have hsub : closedBall w r ⊆ B := by
    intro p hp
    rw [mem_closedBall] at hp ⊢
    rw [mem_ball] at hw
    have := dist_triangle p w z₀
    linarith
  have hmv := h36p_meanvalue (h36p_b_term_diff hf γ.1) hr0 (hsub.trans hBH)
  have hle : ENNReal.ofReal (π * r ^ 2 * ‖f (h36p_m γ.1 w) / ((γ.1 1 0 : ℂ) * w + γ.1 1 1) ^ 4‖) ≤ I γ := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact hmv.trans (lintegral_mono_set (ball_subset_closedBall.trans hsub))
  have hle' := (ENNReal.ofReal_le_iff_le_toReal hIγ).1 hle
  have hpos : 0 < π * r ^ 2 := by positivity
  rw [le_inv_mul_iff₀ hpos]
  exact hle'

/-- **Holomorphy of the Poincaré series** `Θf` on `ℍ` (`differentiableOn_tsum_of_summable_norm` on the discs of
`h36p_b_local`). -/
theorem h36p_b_theta_diff (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤) : DifferentiableOn ℂ (h36p_theta Γ f) upperHalf := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  obtain ⟨u, hu, hle⟩ := h36p_b_local hΓ hf hfA hz₀
  have hsub : ball z₀ (z₀.im / 4) ⊆ upperHalf :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans
      (h36p_closedBall_sub hz₀)
  have hd : DifferentiableOn ℂ (h36p_theta Γ f) (ball z₀ (z₀.im / 4)) :=
    differentiableOn_tsum_of_summable_norm hu (fun γ => (h36p_b_term_diff hf γ.1).mono hsub) isOpen_ball hle
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).differentiableWithinAt

/-- **Automorphy of the Poincaré series**: `Θf(δz) j(δ, z)⁻⁴ = Θf(z)` for `δ ∈ Γ`, `z ∈ ℍ` (reindex `γ ↦ γδ`,
cocycle of `j`). -/
theorem h36p_b_automorphic (f : ℂ → ℂ) : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
    h36p_theta Γ f ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
      h36p_theta Γ f z := by
  intro δ hδ z hz
  unfold h36p_theta
  rw [← tsum_div_const]
  conv_rhs => rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  change f (h36p_m γ.1 (h36p_m δ z)) / ((γ.1 1 0 : ℂ) * h36p_m δ z + γ.1 1 1) ^ 4 /
      ((δ 1 0 : ℂ) * z + δ 1 1) ^ 4 =
    f (h36p_m (γ.1 * δ) z) / ((((γ.1 * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
      (((γ.1 * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ^ 4
  rw [h36p_b_m_mul γ.1 δ hz, h36p_b_j_mul γ.1 δ hz, mul_pow, div_div]

/-- **Unfolding the terms**: `Σ_{γ ∈ Γ} ∬_F |f(γz)| |j(γ, z)|⁻⁴ = m ∬_ℍ |f|` (`h36p_unfold`). -/
theorem h36p_b_sum_lintegral (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) :
    ∑' γ : Γ, ∫⁻ z in F, ‖f (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖ₑ =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf := by
  classical
  set G : ℂ → ℝ≥0∞ := upperHalf.indicator (fun w => ENNReal.ofReal ‖f w‖) with hGdef
  have hGm : Measurable G := by
    rw [hGdef, ← Set.piecewise_eq_indicator]
    exact (ENNReal.continuous_ofReal.comp_continuousOn hf.continuousOn.norm).measurable_piecewise
      continuousOn_const isOpen_upperHalf.measurableSet
  have e1 : phiArea f upperHalf = ∫⁻ z in upperHalf, G z :=
    setLIntegral_congr_fun isOpen_upperHalf.measurableSet fun z hz => by rw [hGdef, indicator_of_mem hz]
  rw [e1, ← h36p_unfold hΓ hF hGm]
  refine tsum_congr fun γ => setLIntegral_congr_fun hF.2.1 fun z hz => ?_
  rw [hGdef, indicator_of_mem (h36p_m_mem γ.1 (hF.1 hz)), ← ofReal_norm, h36p_b_norm_term,
    ENNReal.ofReal_mul (norm_nonneg _)]

/-- **Unfolding for integrable functions**: for `h` integrable on `ℍ`,
`Σ_{γ ∈ Γ} ∬_F |j(γ, z)|⁻⁴ h(γz) = m ∬_ℍ h`.  (The measures `γ_*(|j(γ, ·)|⁻⁴ dA|_F)` sum to `m dA|_ℍ` by
`h36p_unfold` on indicators; then `integral_sum_measure`.) -/
theorem h36p_b_integral_unfold (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {h : ℂ → ℂ}
    (hh : Integrable h (volume.restrict upperHalf)) :
    ∑' γ : Γ, ∫ z in F, (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) • h (h36p_m γ.1 z) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ∫ z in upperHalf, h z := by
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  set D : Γ → ℂ → ℝ≥0∞ := fun γ z => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) with hD
  have hDm : ∀ γ, Measurable (D γ) := fun γ => by
    simp only [hD]
    fun_prop
  set ν : Γ → Measure ℂ := fun γ => Measure.map (h36p_m γ.1) ((volume.restrict F).withDensity (D γ))
    with hν
  have hsum : Measure.sum ν =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) • volume.restrict upperHalf := by
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul,
      ← lintegral_indicator_one (μ := volume.restrict upperHalf) hs,
      ← h36p_unfold hΓ hF (measurable_one.indicator hs)]
    refine tsum_congr fun γ => ?_
    have hpre : MeasurableSet (h36p_m γ.1 ⁻¹' s) := h36p_m_measurable _ hs
    rw [hν, Measure.map_apply (h36p_m_measurable _) hs, withDensity_apply _ hpre,
      Measure.restrict_restrict hpre, ← setLIntegral_indicator hpre]
    refine lintegral_congr fun z => ?_
    by_cases hzs : h36p_m γ.1 z ∈ s
    · rw [indicator_of_mem (show z ∈ h36p_m γ.1 ⁻¹' s from hzs), indicator_of_mem hzs, Pi.one_apply,
        one_mul]
    · rw [indicator_of_notMem (show z ∉ h36p_m γ.1 ⁻¹' s from hzs), indicator_of_notMem hzs, zero_mul]
  have hint : Integrable h (Measure.sum ν) := by
    rw [hsum]
    exact hh.smul_measure (ENNReal.natCast_ne_top _)
  calc ∑' γ : Γ, ∫ z in F, (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) • h (h36p_m γ.1 z)
      = ∑' γ : Γ, ∫ w, h w ∂(ν γ) := by
        refine tsum_congr fun γ => ?_
        rw [hν, integral_map (h36p_m_measurable _).aemeasurable (hint.1.mono_measure (Measure.le_sum ν γ)),
          integral_withDensity_eq_integral_toReal_smul (hDm γ) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [hD, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)]
    _ = ∫ w, h w ∂(Measure.sum ν) := (integral_sum_measure hint).symm
    _ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ∫ z in upperHalf, h z := by
        rw [hsum, integral_smul_measure, ENNReal.toReal_natCast, Complex.real_smul]
        push_cast
        ring

/-- The pointwise algebra of `Γ`-compatibility: if `k = k' j²/\overline{j²}` then
`k (a / j⁴) = |j|⁻⁴ (k' a)`. -/
theorem h36p_b_compat_alg {k k' a q : ℂ} (hq : q ≠ 0) (hk : k = k' * (q ^ 2 / conj (q ^ 2))) :
    k * (a / q ^ 4) = (‖q‖⁻¹ ^ 4 : ℝ) • (k' * a) := by
  have hqc : conj q ≠ 0 := (map_ne_zero _).2 hq
  have hqn : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hq
  have hqq : conj q * q = (‖q‖ : ℂ) ^ 2 := Complex.conj_mul' q
  rw [hk, Complex.real_smul, map_pow]
  push_cast
  field_simp
  linear_combination (-(k' * a) * (conj q * q + (‖q‖ : ℂ) ^ 2)) * hqq

/-- **[P2, stub] The Poincaré series of an integrable holomorphic function.**  For `f` holomorphic on `ℍ`
with `∬_ℍ |f| < ∞`, `Θf ∈ A(Γ, F)`: the series converges locally uniformly on `ℍ` (area mean value
`h36p_meanvalue` on a disc `B`, plus the finite multiplicity of the translates `γ(B)` from `IsFuchsian`, as in
`h36p_local_L1`), so `Θf` is holomorphic (`differentiableOn_tsum_of_summable_norm`); it is automorphic
(reindex `γ ↦ γδ`, cocycle `j(γδ, z) = j(γ, δz) j(δ, z)` of `j(γ, z) = cz + d`); and `∬_F |Θf| ≤ m ∬_ℍ |f|`
(`h36p_unfold`).  Moreover for every bounded measurable `Γ`-compatible `κ`,
`m ∬_ℍ κ f = ∬_F κ Θf`: `Γ`-compatibility turns `κ(z) f(γz) γ'(z)²` into `(κ f)(γz) |γ'(z)|²` a.e.; then
exchange sum and integral (dominated by `m ∬_ℍ |κ f|`) and unfold. -/
theorem h36p_poincare (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤) :
    h36p_theta Γ f ∈ integrableAutomorphicQD Γ F ∧
      ∀ κ : ℂ → ℂ, AEStronglyMeasurable κ (volume.restrict upperHalf) →
        (∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) → IsGammaCompatible Γ κ →
          (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ∫ z in upperHalf, κ z * f z =
            beltramiPairing F κ (h36p_theta Γ f) := by
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  set T : Γ → ℂ → ℂ := fun γ z => f (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4 with hT
  have hθ : h36p_theta Γ f = fun z => ∑' γ, T γ z := rfl
  have hTsum : ∑' γ : Γ, ∫⁻ z in F, ‖T γ z‖ₑ =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf :=
    h36p_b_sum_lintegral hΓ hF hf
  have hTm : ∀ γ, AEStronglyMeasurable (T γ) (volume.restrict F) := fun γ =>
    ((h36p_b_term_diff hf γ.1).continuousOn.mono hFH).aestronglyMeasurable hFm
  refine ⟨⟨h36p_b_theta_diff hΓ hf hfA, ?_, h36p_b_automorphic f⟩, ?_⟩
  · calc phiArea (h36p_theta Γ f) F = ∫⁻ z in F, ‖∑' γ, T γ z‖ₑ := by
          unfold phiArea
          simp_rw [ofReal_norm]
          rfl
      _ ≤ ∫⁻ z in F, ∑' γ, ‖T γ z‖ₑ := lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ, ∫⁻ z in F, ‖T γ z‖ₑ := lintegral_tsum fun γ => (hTm γ).enorm
      _ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf := hTsum
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfA
  · rintro κ hκm ⟨M, hκM⟩ hκΓ
    have hfi : IntegrableOn f upperHalf := by
      refine ⟨hf.continuousOn.aestronglyMeasurable isOpen_upperHalf.measurableSet, ?_⟩
      have h1 : (∫⁻ z in upperHalf, ‖f z‖ₑ) = phiArea f upperHalf := by
        unfold phiArea
        simp_rw [ofReal_norm]
      show (∫⁻ z in upperHalf, ‖f z‖ₑ) < ⊤
      rw [h1]
      exact hfA
    have hκf : Integrable (fun z => κ z * f z) (volume.restrict upperHalf) := hfi.bdd_mul hκm hκM
    have hκmF : AEStronglyMeasurable κ (volume.restrict F) := hκm.mono_measure (Measure.restrict_mono hFH le_rfl)
    have hκMF : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ M := ae_restrict_of_ae_restrict_of_subset hFH hκM
    unfold beltramiPairing
    rw [← h36p_b_integral_unfold hΓ hF hκf]
    have hfin : ∑' γ : Γ, ∫⁻ z in F, ‖κ z * T γ z‖ₑ ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal M *
        ((Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfA.ne)) ?_
      rw [← hTsum, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun γ => ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hκMF] with z hz
      rw [enorm_mul]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hz
    have hsw := integral_tsum (μ := volume.restrict F) (f := fun γ z => κ z * T γ z)
      (fun γ => hκmF.mul (hTm γ)) hfin
    have e1 : ∫ z in F, κ z * h36p_theta Γ f z = ∑' γ, ∫ z in F, κ z * T γ z := by
      rw [← hsw]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hθ]
      exact tsum_mul_left.symm
    rw [e1]
    refine tsum_congr fun γ => integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH (hκΓ γ.1 γ.2), ae_restrict_mem hFm] with z hz hzF
    have hden := k24_d_den_ne_zero (b33_d_det γ.1) (ne_of_gt (show 0 < z.im from hFH hzF))
    exact (h36p_b_compat_alg hden hz).symm

/-- The pointwise bound of the kernel `1/((ζ - z)³(ζ - w))` on `ℍ` (`z, w ∈ 𝕃`) by the integrable profile
`((1 + ‖ζ‖)³)⁻¹`, with `δ = min (-Im z) (-Im w)` and `R = max ‖z‖ ‖w‖`. -/
theorem h36p_b_kernel_le {z w ζ : ℂ} (hz : z ∈ lowerHalf) (hw : w ∈ lowerHalf) (hζ : ζ ∈ upperHalf) :
    ‖1 / ((ζ - z) ^ 3 * (ζ - w))‖ ≤
      ((1 + max ‖z‖ ‖w‖ + min (-z.im) (-w.im)) / min (-z.im) (-w.im)) ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have hz' : z.im < 0 := hz
  have hw' : w.im < 0 := hw
  set δ := min (-z.im) (-w.im) with hδdef
  set R := max ‖z‖ ‖w‖ with hRdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hzδ : z.im ≤ -δ := by linarith [min_le_left (-z.im) (-w.im)]
  have hwδ : w.im ≤ -δ := by linarith [min_le_right (-z.im) (-w.im)]
  have hzR : ‖z‖ ≤ R := le_max_left _ _
  have hwR : ‖w‖ ≤ R := le_max_right _ _
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  have h3 := b36_p_inv_pow3_le hδ hζ hzδ hzR
  have h1 := b36_p_inv_le hδ hζ hwδ hwR
  have hi1 : (1 + ‖ζ‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg ζ])
  have hA : 0 ≤ (1 + R + δ) / δ := by positivity
  have hP : 0 ≤ ((1 + ‖ζ‖) ^ 3)⁻¹ := by positivity
  rw [one_div, mul_inv, norm_mul]
  calc ‖((ζ - z) ^ 3)⁻¹‖ * ‖(ζ - w)⁻¹‖
      ≤ (((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹) * ((1 + R + δ) / δ * 1) :=
        mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_left hi1 hA)) (norm_nonneg _) (by positivity)
    _ = ((1 + R + δ) / δ) ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by ring

/-- **[P2, stub] The kernels.**  For `z, w ∈ 𝕃`, `ζ ↦ 1/((ζ - z)³(ζ - w))` is holomorphic on `ℍ` and
integrable there (on `ℍ`, `|ζ - z| ≥ c_z (1 + |ζ|)`; `b36_p_profile_integrable`).  `w = z` is the kernel
`(ζ - z)⁻⁴` of `bersDerivative`. -/
theorem h36p_kernel_L1 {z w : ℂ} (hz : z ∈ lowerHalf) (hw : w ∈ lowerHalf) :
    DifferentiableOn ℂ (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf ∧
      phiArea (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf < ⊤ := by
  have hz' : z.im < 0 := hz
  have hw' : w.im < 0 := hw
  have hne : ∀ ζ ∈ upperHalf, (ζ - z) ^ 3 * (ζ - w) ≠ 0 := by
    intro ζ hζ
    have hζ' : 0 < ζ.im := hζ
    refine mul_ne_zero (pow_ne_zero _ fun h => ?_) fun h => ?_
    · have := congrArg Complex.im h
      simp only [sub_im, zero_im] at this
      linarith
    · have := congrArg Complex.im h
      simp only [sub_im, zero_im] at this
      linarith
  have hd : DifferentiableOn ℂ (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf :=
    (differentiableOn_const 1).div (by fun_prop) hne
  refine ⟨hd, ?_⟩
  have hint : IntegrableOn (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf :=
    Integrable.mono' (b36_p_profile_integrable.const_mul _).integrableOn
      (hd.continuousOn.aestronglyMeasurable isOpen_upperHalf.measurableSet)
      (ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun ζ hζ => h36p_b_kernel_le hz hw hζ)
  have h1 : phiArea (fun ζ => 1 / ((ζ - z) ^ 3 * (ζ - w))) upperHalf =
      ∫⁻ ζ in upperHalf, ‖1 / ((ζ - z) ^ 3 * (ζ - w))‖ₑ := by
    unfold phiArea
    simp_rw [ofReal_norm]
  rw [h1]
  exact hint.2

/-! ### A.5 Stubs of prover P3 (the reproducing formula) -/

/-- The transformed integrand `G` of the reproducing formula is continuous on the disc (scout C's
`h36_rp_G_continuousOn`). -/
theorem h36p_c_rp_G_continuousOn {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {a : ℂ}
    (ha : a ∈ lowerHalf) : ContinuousOn (b36_r_G φ a) (ball (0 : ℂ) 1) := by
  have hh := (b36_r_hfun_diff hφ ha).continuousOn
  have hc2 : ContinuousOn (fun q : ℂ => b36_r_hfun φ a (conj q)) (ball (0 : ℂ) 1) :=
    hh.comp Complex.continuous_conj.continuousOn (fun q hq => by
      simpa [mem_ball, dist_zero_right, Complex.norm_conj] using hq)
  exact ContinuousOn.mul (by fun_prop) hc2

/-- Integrability of the kernel integrand on `ℍ` gives integrability of the polar integrand of `G`
(scout C's `h36_rp_polar_integrable`: Cayley change of variables `ahP_integrableOn_image`, then
`integrableOn_polar_of_integrableOn_ball` applied to the measurable indicator of `G` on the disc). -/
theorem h36p_c_rp_polar_integrable {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {z : ℂ}
    (hz : z ∈ lowerHalf)
    (hint : IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4) upperHalf) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * b36_r_G φ z (Complex.polarCoord.symm p + 0))
      (Ioo 0 1 ×ˢ Ioo (-π) π) := by
  have hGball : IntegrableOn (b36_r_G φ z) (ball (0 : ℂ) 1) := by
    rw [← b36_r_image hz, ahP_integrableOn_image isOpen_ball (b36_r_differentiableOn z)
      (b36_r_injOn hz)] at hint
    exact hint.congr_fun (fun q hq => b36_r_kernel hz φ hq) measurableSet_ball
  classical
  set G' : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (b36_r_G φ z) with hG'
  have hmeas : Measurable G' := by
    have : G' = (ball (0 : ℂ) 1).piecewise (b36_r_G φ z) 0 := by
      rw [hG', Set.piecewise_eq_indicator]
    rw [this]
    exact ContinuousOn.measurable_piecewise (h36p_c_rp_G_continuousOn hφ hz) continuousOn_const
      measurableSet_ball
  have hG'int : IntegrableOn G' (ball (0 : ℂ) 1) :=
    hGball.congr_fun (fun q hq => by rw [hG', indicator_of_mem hq]) measurableSet_ball
  have h := integrableOn_polar_of_integrableOn_ball hmeas hG'int
  refine h.congr_fun (fun p hp => ?_) (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmem : Complex.polarCoord.symm p ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2
  simp only [add_zero, hG', indicator_of_mem hmem]

/-- **Bers reproducing formula, integrable form** (scout C's `h36_rp_of_integrable`): for `φ` holomorphic
on `𝕃`, `z ∈ 𝕃`, and the integrand `(Im ζ)² φ(ζ̄)/(ζ - z)⁴` integrable on `ℍ`,
`∬_ℍ (Im ζ)² φ(ζ̄)/(ζ - z)⁴ dξ dη = (π/12) φ(z)`. -/
theorem h36p_c_rp_of_integrable {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ lowerHalf) {z : ℂ}
    (hz : z ∈ lowerHalf)
    (hint : IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4) upperHalf) :
    ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4 = (π / 12 : ℂ) * φ z := by
  have e1 : ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - z) ^ 4
      = ∫ q in ball (0 : ℂ) 1, b36_r_G φ z q := by
    rw [← b36_r_image hz, ahP_integral_image isOpen_ball (b36_r_differentiableOn z)
      (b36_r_injOn hz)]
    exact setIntegral_congr_fun measurableSet_ball (fun q hq => b36_r_kernel hz φ hq)
  rw [e1, setIntegral_ball_eq_polar' 0 zero_le_one (h36p_c_rp_polar_integrable hφ hz hint),
    intervalIntegral.integral_congr (fun r hr => b36_r_inner hφ hz hr),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, b36_r_radial]
  push_cast
  ring

/-- The Bergman kernel integrand `K_h(ζ, w) = (Im ζ)² h(ζ)/(ζ̄ - w)⁴` of the reproducing formula on `ℍ`
(`ζ, w ∈ ℍ`). -/
def h36p_c_K (h : ℂ → ℂ) (ζ w : ℂ) : ℂ := (ζ.im : ℂ) ^ 2 * h ζ / (conj ζ - w) ^ 4

/-- `ζ̄ ∈ 𝕃` for `ζ ∈ ℍ`. -/
theorem h36p_c_conj_mem {ζ : ℂ} (hζ : ζ ∈ upperHalf) : conj ζ ∈ lowerHalf := by
  show (conj ζ).im < 0
  rw [conj_im]
  have : 0 < ζ.im := hζ
  linarith

/-- `Im ζ + Im w ≤ |ζ̄ - w|`. -/
theorem h36p_c_im_add_le (ζ w : ℂ) : ζ.im + w.im ≤ ‖conj ζ - w‖ := by
  have h := Complex.abs_im_le_norm (conj ζ - w)
  rw [sub_im, conj_im, show -ζ.im - w.im = -(ζ.im + w.im) by ring, abs_neg] at h
  exact (le_abs_self _).trans h

/-- `ζ̄ - w ≠ 0` for `ζ, w ∈ ℍ`. -/
theorem h36p_c_conj_sub_ne {ζ w : ℂ} (hζ : ζ ∈ upperHalf) (hw : w ∈ upperHalf) : conj ζ - w ≠ 0 := by
  intro h0
  have h := h36p_c_im_add_le ζ w
  rw [h0, norm_zero] at h
  have h1 : 0 < ζ.im := hζ
  have h2 : 0 < w.im := hw
  linarith

/-- The norm of the kernel: `|K_h(ζ, w)| = (Im ζ)² |h(ζ)| |w - ζ̄|⁻⁴`. -/
theorem h36p_c_K_norm (h : ℂ → ℂ) (ζ w : ℂ) :
    ‖h36p_c_K h ζ w‖ = ζ.im ^ 2 * ‖h ζ‖ * ‖w - conj ζ‖⁻¹ ^ 4 := by
  rw [h36p_c_K, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← norm_neg (conj ζ - w), neg_sub, div_eq_mul_inv, inv_pow]

/-- For `ζ, w ∈ ℍ`: `|K_h(ζ, w)| ≤ |h(ζ)|/(16 (Im w)²)` (as `|ζ̄ - w| ≥ Im ζ + Im w ≥ 2 √(Im ζ Im w)`). -/
theorem h36p_c_K_le (h : ℂ → ℂ) {ζ w : ℂ} (hζ : ζ ∈ upperHalf) (hw : w ∈ upperHalf) :
    ‖h36p_c_K h ζ w‖ ≤ ‖h ζ‖ / (16 * w.im ^ 2) := by
  have hy : 0 < ζ.im := hζ
  have hv : 0 < w.im := hw
  have hle := h36p_c_im_add_le ζ w
  have hpos : 0 < ‖conj ζ - w‖ := by linarith
  rw [h36p_c_K, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 4 * ζ.im * w.im ≤ (ζ.im + w.im) ^ 2 := by nlinarith [sq_nonneg (ζ.im - w.im)]
  have h3 : (ζ.im + w.im) ^ 2 ≤ ‖conj ζ - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
  have h4 : (4 * ζ.im * w.im) ^ 2 ≤ (‖conj ζ - w‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (h2.trans h3) 2
  have h1 : 16 * ζ.im ^ 2 * w.im ^ 2 ≤ ‖conj ζ - w‖ ^ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (h ζ))]

/-- **Kernel area**: for `a ∈ 𝕃`, `∬_ℍ |w - a|⁻⁴ dA(w) = |𝔻|/(4 (Im a)²)` (the Cayley map
`q ↦ a + (ā - a)/(1 - q)` of the disc onto `ℍ` has Jacobian `|ā - a|²/|1 - q|⁴`, which cancels the kernel up
to the constant `|ā - a|⁻²`). -/
theorem h36p_c_kernel_area {a : ℂ} (ha : a ∈ lowerHalf) :
    ∫⁻ w in upperHalf, ENNReal.ofReal (‖w - a‖⁻¹ ^ 4) =
      volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * a.im ^ 2)⁻¹) := by
  rw [← b36_r_image ha, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (fun q hq => ((b36_r_hasDerivAt a (b36_r_one_sub_ne hq)).hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) (b36_r_injOn ha), mul_comm, ← setLIntegral_const]
  refine setLIntegral_congr_fun measurableSet_ball fun q hq => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hu : ‖1 - q‖ ≠ 0 := norm_ne_zero_iff.2 (b36_r_one_sub_ne hq)
  have ha' : a.im ≠ 0 := ne_of_lt (show a.im < 0 from ha)
  have hn : ‖conj a - a‖ = 2 * |a.im| := by
    have e : conj a - a = ((-(2 * a.im) : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
      ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_mul, abs_two]
  rw [b36_r_cay_sub, norm_div, norm_div, norm_pow, hn]
  have hab : |a.im| ≠ 0 := abs_ne_zero.2 ha'
  field_simp
  rw [sq_abs]
  ring

/-- **Tonelli for the kernel**: for measurable `S ⊆ ℍ`, `∫_S ∫_ℍ |K_h(ζ, w)| dw dζ = |𝔻| ∫_S |h|/4`. -/
theorem h36p_c_tonelli {S : Set ℂ} (hS : MeasurableSet S) (hSH : S ⊆ upperHalf) (h : ℂ → ℂ) :
    ∫⁻ ζ in S, ∫⁻ w in upperHalf, ENNReal.ofReal ‖h36p_c_K h ζ w‖ =
      volume (ball (0 : ℂ) 1) * ∫⁻ ζ in S, ENNReal.ofReal (‖h ζ‖ / 4) := by
  rw [← lintegral_const_mul' _ _ measure_ball_lt_top.ne]
  refine setLIntegral_congr_fun hS fun ζ hζ => ?_
  have hy : 0 < ζ.im := hSH hζ
  have e : ∀ w, ENNReal.ofReal ‖h36p_c_K h ζ w‖ =
      ENNReal.ofReal (ζ.im ^ 2 * ‖h ζ‖) * ENNReal.ofReal (‖w - conj ζ‖⁻¹ ^ 4) := fun w => by
    rw [h36p_c_K_norm, ENNReal.ofReal_mul (by positivity)]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h36p_c_kernel_area (h36p_c_conj_mem (hSH hζ)),
    conj_im, mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- The kernel `(w, ζ) ↦ K_h(ζ, w)` is continuous on `ℍ × ℍ` for `h` continuous on `ℍ`. -/
theorem h36p_c_K_continuousOn {h : ℂ → ℂ} (hh : ContinuousOn h upperHalf) :
    ContinuousOn (fun p : ℂ × ℂ => h36p_c_K h p.2 p.1) (upperHalf ×ˢ upperHalf) := by
  unfold h36p_c_K
  refine ContinuousOn.div ?_ ?_ ?_
  · refine ContinuousOn.mul (by fun_prop) ?_
    exact hh.comp continuous_snd.continuousOn (fun p hp => hp.2)
  · have : Continuous fun p : ℂ × ℂ => (conj p.2 - p.1) ^ 4 :=
      ((Complex.continuous_conj.comp continuous_snd).sub continuous_fst).pow 4
    exact this.continuousOn
  · intro p hp
    exact pow_ne_zero _ (h36p_c_conj_sub_ne hp.2 hp.1)

/-- The kernel `(w, ζ) ↦ K_h(ζ, w)` is a.e.-strongly measurable on `ℍ × S` (`S ⊆ ℍ` measurable). -/
theorem h36p_c_K_aesm {h : ℂ → ℂ} (hh : ContinuousOn h upperHalf) {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) :
    AEStronglyMeasurable (fun p : ℂ × ℂ => h36p_c_K h p.2 p.1)
      ((volume.restrict upperHalf).prod (volume.restrict S)) := by
  rw [Measure.prod_restrict]
  exact ((h36p_c_K_continuousOn hh).mono (prod_mono subset_rfl hSH)).aestronglyMeasurable
    (isOpen_upperHalf.measurableSet.prod hS)

/-- A function continuous on `ℍ` with `∫_S |h| < ∞` is integrable on `S ⊆ ℍ`. -/
theorem h36p_c_integrableOn {h : ℂ → ℂ} (hh : ContinuousOn h upperHalf) {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) (hhi : ∫⁻ ζ in S, ENNReal.ofReal ‖h ζ‖ < ⊤) : IntegrableOn h S := by
  refine ⟨(hh.mono hSH).aestronglyMeasurable hS, ?_⟩
  unfold HasFiniteIntegral
  simpa only [ofReal_norm] using hhi

/-- For `w ∈ ℍ` the kernel `ζ ↦ K_h(ζ, w)` is integrable on `S ⊆ ℍ` when `h` is (bound `h36p_c_K_le`). -/
theorem h36p_c_K_integrableOn {h : ℂ → ℂ} (hh : ContinuousOn h upperHalf) {S : Set ℂ} (hS : MeasurableSet S)
    (hSH : S ⊆ upperHalf) (hhi : ∫⁻ ζ in S, ENNReal.ofReal ‖h ζ‖ < ⊤) {w : ℂ} (hw : w ∈ upperHalf) :
    IntegrableOn (fun ζ => h36p_c_K h ζ w) S := by
  have hc : ContinuousOn (fun ζ => h36p_c_K h ζ w) S := by
    have := (h36p_c_K_continuousOn hh).comp (Continuous.continuousOn (f := fun ζ : ℂ => (w, ζ))
      (by fun_prop)) (fun ζ hζ => ⟨hw, hSH hζ⟩)
    exact this
  exact ((h36p_c_integrableOn hh hS hSH hhi).norm.div_const (16 * w.im ^ 2)).mono'
    (hc.aestronglyMeasurable hS) (ae_restrict_of_forall_mem hS fun ζ hζ => h36p_c_K_le h (hSH hζ) hw)

/-- **The reproducing formula on `ℍ`** (`b36_r_reproducing` conjugated, integrable form): for `f`
holomorphic on `ℍ`, `w ∈ ℍ` and `ζ ↦ K_f(ζ, w)` integrable on `ℍ`,
`∬_ℍ (Im ζ)² f(ζ)/(ζ̄ - w)⁴ = (π/12) f(w)`.  Apply `h36p_c_rp_of_integrable` to `u ↦ conj f(ū)` on `𝕃` at
`w̄`, and conjugate. -/
theorem h36p_c_rp_upper {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) {w : ℂ} (hw : w ∈ upperHalf)
    (hint : IntegrableOn (fun ζ => h36p_c_K f ζ w) upperHalf) :
    ∫ ζ in upperHalf, h36p_c_K f ζ w = (π / 12 : ℂ) * f w := by
  set φ : ℂ → ℂ := fun u => conj (f (conj u)) with hφdef
  have hφ : DifferentiableOn ℂ φ lowerHalf := by
    intro u hu
    have hu' : conj u ∈ upperHalf := by
      show 0 < (conj u).im
      rw [conj_im]
      have : u.im < 0 := hu
      linarith
    have h2 := (hf.differentiableAt (isOpen_upperHalf.mem_nhds hu')).conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hz : conj w ∈ lowerHalf := h36p_c_conj_mem hw
  have hpt : ∀ ζ : ℂ, (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - conj w) ^ 4 = conj (h36p_c_K f ζ w) := by
    intro ζ
    simp only [hφdef, h36p_c_K, Complex.conj_conj, map_div₀, map_mul, map_pow, Complex.conj_ofReal,
      map_sub]
  have hint' : IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ (conj ζ) / (ζ - conj w) ^ 4) upperHalf := by
    simp_rw [hpt]
    exact Integrable.mono hint (Complex.continuous_conj.comp_aestronglyMeasurable hint.1)
      (Eventually.of_forall fun ζ => by rw [Complex.norm_conj])
  have h1 := h36p_c_rp_of_integrable hφ hz hint'
  simp_rw [hpt] at h1
  rw [integral_conj] at h1
  have h2 := congrArg conj h1
  rw [Complex.conj_conj] at h2
  rw [h2]
  simp only [hφdef, map_mul, Complex.conj_conj, map_div₀, Complex.conj_ofReal, map_ofNat]

/-- **[P3, stub] Local triviality annihilates every integrable holomorphic `f`.**  If a bounded measurable
`κ` on `ℍ` has `∬_ℍ κ(ζ)/(ζ - z)⁴ = 0` for all `z ∈ 𝕃` (i.e. `bersDerivative κ = 0` on `𝕃`), then
`∬_ℍ κ f = 0` for every holomorphic `f` on `ℍ` with `∬_ℍ |f| < ∞`.  Route: the reproducing formula
`f(w) = (12/π) ∬_ℍ (Im ζ)² f(ζ)/(ζ̄ - w)⁴` (`b36_r_reproducing` conjugated, in the integrable form of scout C's
`h36_rp_of_integrable`), then Fubini, justified by `∬_ℍ |w - a|⁻⁴ dA(w) = π/(4 (Im a)²)` (`a ∈ 𝕃`), and the
inner integral is `-(π/6)·bersDerivative κ (ζ̄) = 0`. -/
theorem h36p_orth_integrable {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf))
    {M : ℝ} (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M)
    (hκ : ∀ z ∈ lowerHalf, ∫ ζ in upperHalf, κ ζ / (ζ - z) ^ 4 = 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalf) (hfA : phiArea f upperHalf < ⊤) :
    ∫ ζ in upperHalf, κ ζ * f ζ = 0 := by
  have hH : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hfc : ContinuousOn f upperHalf := hf.continuousOn
  have hrep : ∀ w ∈ upperHalf, f w = (12 / π : ℂ) * ∫ ζ in upperHalf, h36p_c_K f ζ w := by
    intro w hw
    rw [h36p_c_rp_upper hf hw (h36p_c_K_integrableOn hfc hH subset_rfl hfA hw)]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  set H : ℂ → ℂ → ℂ := fun w ζ => κ w * h36p_c_K f ζ w with hHdef
  have hHi : Integrable (Function.uncurry H)
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    have hKm := h36p_c_K_aesm hfc hH subset_rfl
    refine ⟨(hκm.comp_fst (ν := volume.restrict upperHalf)).mul hKm, ?_⟩
    unfold HasFiniteIntegral
    have hb : ∀ᵐ p ∂((volume.restrict upperHalf).prod (volume.restrict upperHalf)),
        ‖Function.uncurry H p‖ₑ ≤ ENNReal.ofReal M * ENNReal.ofReal ‖h36p_c_K f p.2 p.1‖ := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hκM] with p hp
      show ‖κ p.1 * h36p_c_K f p.2 p.1‖ₑ ≤ _
      rw [enorm_mul, ← ofReal_norm, ← ofReal_norm]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hp) _
    have hA : ∫⁻ ζ in upperHalf, ENNReal.ofReal (‖f ζ‖ / 4) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg (f ζ)]))
        hfA
    calc ∫⁻ p, ‖Function.uncurry H p‖ₑ ∂((volume.restrict upperHalf).prod (volume.restrict upperHalf))
        ≤ ∫⁻ p, ENNReal.ofReal M * ENNReal.ofReal ‖h36p_c_K f p.2 p.1‖
            ∂((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := lintegral_mono_ae hb
      _ = ENNReal.ofReal M * ∫⁻ ζ in upperHalf, ∫⁻ w in upperHalf, ENNReal.ofReal ‖h36p_c_K f ζ w‖ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_prod_symm _ hKm.aemeasurable.norm.ennreal_ofReal]
      _ = ENNReal.ofReal M * (volume (ball (0 : ℂ) 1) * ∫⁻ ζ in upperHalf, ENNReal.ofReal (‖f ζ‖ / 4)) := by
          rw [h36p_c_tonelli hH subset_rfl f]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top measure_ball_lt_top hA)
  have h1 : ∫ w in upperHalf, κ w * f w = (12 / π : ℂ) * ∫ w in upperHalf, ∫ ζ in upperHalf, H w ζ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hH fun w hw => ?_
    rw [hrep w hw, hHdef]
    simp only
    rw [integral_const_mul]
    ring
  have h2 : ∀ ζ ∈ upperHalf, ∫ w in upperHalf, H w ζ = 0 := by
    intro ζ hζ
    have e : ∀ w, H w ζ = ((ζ.im : ℂ) ^ 2 * f ζ) * (κ w / (w - conj ζ) ^ 4) := by
      intro w
      simp only [hHdef, h36p_c_K]
      rw [show (conj ζ - w) ^ 4 = (w - conj ζ) ^ 4 by ring]
      ring
    simp_rw [e]
    rw [integral_const_mul, hκ _ (h36p_c_conj_mem hζ), mul_zero]
  rw [h1, integral_integral_swap hHi, setIntegral_congr_fun hH h2, integral_zero, mul_zero]

/-- For `w ∈ ℍ` the kernel `ζ ↦ K_h(ζ, w)` is continuous on `ℍ` (for `h` continuous on `ℍ`). -/
theorem h36p_c_K_continuousOn_left {h : ℂ → ℂ} (hh : ContinuousOn h upperHalf) {w : ℂ}
    (hw : w ∈ upperHalf) : ContinuousOn (fun ζ => h36p_c_K h ζ w) upperHalf := by
  unfold h36p_c_K
  exact ContinuousOn.div (ContinuousOn.mul (by fun_prop) hh)
    ((Complex.continuous_conj.sub continuous_const).pow 4).continuousOn
    fun ζ hζ => pow_ne_zero _ (h36p_c_conj_sub_ne hζ hw)

/-- **Change of variables through `h36p_m γ`** on a measurable `E ⊆ ℍ`:
`∫_{γ(E)} g = ∫_E |cz + d|⁻⁴ g(γz)`. -/
theorem h36p_c_image_m (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {E : Set ℂ} (hE : MeasurableSet E)
    (hEH : E ⊆ upperHalf) (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in h36p_m γ '' E, g w =
      ∫⁻ z in E, ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) * g (h36p_m γ z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE
    (fun z hz => ((h36p_m_hasDerivAt γ (hEH hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((h36p_m_injOn γ).mono hEH)]
  refine setLIntegral_congr_fun hE fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), norm_div, norm_one, norm_pow]
  congr 2
  ring

/-- **Multiplicity of the translates of a disc**: for `z ∈ ℍ` and `B = B̄(z, Im z/2)` there is `N` with
`Σ_{γ ∈ Γ} 𝟙_{γ(B)}(w) g(w) ≤ N g(w)` for all `w` and `g ≥ 0` (`N = #{γ ∈ Γ | γ(B) ∩ B ≠ ∅}`, finite since `Γ`
is Fuchsian; the argument of `h36p_local_L1`). -/
theorem h36p_c_mult (hΓ : IsFuchsian Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ N : ℕ, ∀ (g : ℂ → ℝ≥0∞) (w : ℂ),
      ∑' γ : Γ, (h36p_m γ '' closedBall z (z.im / 2)).indicator g w ≤ N * g w := by
  set B := closedBall z (z.im / 2) with hBdef
  have hBH : B ⊆ upperHalf := h36p_closedBall_sub hz
  set C : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' B with hCdef
  have hC : IsCompact C := by
    have hsub : B ⊆ range UpperHalfPlane.coe := fun w hw => ⟨⟨w, hBH hw⟩, rfl⟩
    exact (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff hsub).2
      (isCompact_closedBall z _)
  set S := {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty} with hSdef
  have hS : S.Finite := hΓ C hC
  refine ⟨S.ncard, fun g w => ?_⟩
  by_cases hex : ∃ γ₀ : Γ, w ∈ h36p_m γ₀ '' B
  · obtain ⟨γ₀, b₀, hb₀, hb₀w⟩ := hex
    set T : Set Γ := {γ | ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) ∈ S} with hTdef
    have hinj : InjOn (fun γ : Γ => ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ)) T := by
      intro a _ b _ hab
      exact Subtype.ext (mul_left_cancel hab)
    have hTfin : T.Finite := hS.preimage hinj
    have hTcard : T.ncard ≤ S.ncard :=
      Set.ncard_le_ncard_of_injOn _ (fun a ha => ha) hinj hS
    have hsupp : ∀ γ ∉ hTfin.toFinset, (h36p_m γ '' B).indicator g w = 0 := by
      intro γ hγT
      rw [Set.Finite.mem_toFinset] at hγT
      refine indicator_of_notMem ?_ _
      rintro ⟨b, hb, hbw⟩
      apply hγT
      have e1 := h36p_m_coe γ ⟨b, hBH hb⟩
      have e0 := h36p_m_coe γ₀ ⟨b₀, hBH hb₀⟩
      simp only at e1 e0
      have heq : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
          (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (⟨b₀, hBH hb₀⟩ : UpperHalfPlane) :=
        UpperHalfPlane.ext (by rw [← e1, ← e0, hbw, hb₀w])
      have hδ : ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) =
          ⟨b₀, hBH hb₀⟩ := by
        rw [mul_smul, heq, inv_smul_smul]
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ γ₀.2) γ.2, _, ⟨⟨b, hBH hb⟩,
        (show (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C from hb), rfl⟩, ?_⟩
      show ((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ) • (⟨b, hBH hb⟩ : UpperHalfPlane) ∈ C
      rw [hδ]
      exact hb₀
    rw [tsum_eq_sum hsupp]
    calc ∑ γ ∈ hTfin.toFinset, (h36p_m γ '' B).indicator g w
        ≤ ∑ _γ ∈ hTfin.toFinset, g w :=
          Finset.sum_le_sum fun γ _ => indicator_le_self _ _ _
      _ = hTfin.toFinset.card * g w := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ S.ncard * g w := by
          gcongr
          rw [← Set.ncard_eq_toFinset_card T hTfin]
          exact_mod_cast hTcard
  · push Not at hex
    have h0 : ∀ γ : Γ, (h36p_m γ '' B).indicator g w = 0 := fun γ =>
      indicator_of_notMem (hex γ) _
    simp only [h0, tsum_zero]
    exact bot_le

/-- **The Poincaré series of the kernel `|w - ζ̄|⁻⁴`**: for `z ∈ ℍ` there is `C < ∞` with
`Σ_{γ ∈ Γ} |γz - ζ̄|⁻⁴ |cz + d|⁻⁴ ≤ C/(Im ζ)²` for all `ζ ∈ ℍ`: area mean value (`h36p_meanvalue`) of the
holomorphic `w ↦ (ζ̄ - γw)⁻⁴ (cw + d)⁻⁴` on `B = B̄(z, Im z/2)`, change of variables onto `γ(B)`
(`h36p_c_image_m`), the multiplicity `h36p_c_mult`, and the kernel area `h36p_c_kernel_area`. -/
theorem h36p_c_pser (hΓ : IsFuchsian Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ζ ∈ upperHalf,
      ∑' γ : Γ, ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 * ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) ≤
        C * ENNReal.ofReal ((ζ.im ^ 2)⁻¹) := by
  obtain ⟨N, hN⟩ := h36p_c_mult hΓ hz
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  have hz' : 0 < z.im := hz
  have hr0 : 0 < z.im / 2 := by positivity
  set B := closedBall z (z.im / 2) with hBdef
  have hBH : B ⊆ upperHalf := h36p_closedBall_sub hz
  set a : ℝ≥0∞ := ENNReal.ofReal (π * (z.im / 2) ^ 2) with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨a⁻¹ * (N * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal (1 / 4))), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 ha0))
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top))
  intro ζ hζ
  have hy : 0 < ζ.im := hζ
  set k : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (‖u - conj ζ‖⁻¹ ^ 4) with hkdef
  have hkm : Measurable k := by
    rw [hkdef]
    fun_prop
  have hBimg : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, MeasurableSet (h36p_m γ '' B) := by
    intro γ
    have hcont : ContinuousOn (h36p_m γ) B := fun w hw =>
      (h36p_m_hasDerivAt γ (hBH hw)).continuousAt.continuousWithinAt
    exact ((isCompact_closedBall z _).image_of_continuousOn hcont).isClosed.measurableSet
  have hterm : ∀ γ : Γ, a * ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 *
      ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) ≤ ∫⁻ u in upperHalf, (h36p_m γ.1 '' B).indicator k u := by
    intro γ
    have hdet := b33_d_det γ.1
    set q : ℂ → ℂ := fun w => ((conj ζ - h36p_m γ.1 w) ^ 4 * ((γ.1 1 0 : ℂ) * w + γ.1 1 1) ^ 4)⁻¹
      with hqdef
    have hden : ∀ w ∈ upperHalf, (γ.1 1 0 : ℂ) * w + γ.1 1 1 ≠ 0 := fun w hw =>
      k24_d_den_ne_zero hdet (ne_of_gt (show 0 < w.im from hw))
    have hq : DifferentiableOn ℂ q upperHalf := by
      intro w hw
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.inv ?_ ?_
      · exact (((differentiableAt_const _).sub (h36p_m_hasDerivAt γ.1 hw).differentiableAt).pow 4).mul
          ((((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).pow 4)
      · exact mul_ne_zero (pow_ne_zero _ (h36p_c_conj_sub_ne hζ (h36p_m_mem γ.1 hw)))
          (pow_ne_zero _ (hden w hw))
    have hqn : ∀ w ∈ upperHalf, ENNReal.ofReal ‖q w‖ =
        ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * w + γ.1 1 1‖⁻¹ ^ 4) * k (h36p_m γ.1 w) := by
      intro w _
      rw [hqdef, hkdef]
      simp only
      rw [← ENNReal.ofReal_mul (by positivity), norm_inv, norm_mul, norm_pow, norm_pow, norm_sub_rev]
      congr 1
      rw [mul_inv, inv_pow, inv_pow]
      ring
    have hmv := h36p_meanvalue hq hr0 hBH
    calc a * ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 * ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)
        = a * ENNReal.ofReal ‖q z‖ := by
          rw [hqn z hz]
          congr 1
          show _ = ENNReal.ofReal _ * ENNReal.ofReal _
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ∫⁻ w in ball z (z.im / 2), ENNReal.ofReal ‖q w‖ := hmv
      _ ≤ ∫⁻ w in B, ENNReal.ofReal ‖q w‖ := lintegral_mono_set ball_subset_closedBall
      _ = ∫⁻ w in B, ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * w + γ.1 1 1‖⁻¹ ^ 4) * k (h36p_m γ.1 w) :=
          setLIntegral_congr_fun measurableSet_closedBall fun w hw => hqn w (hBH hw)
      _ = ∫⁻ u in h36p_m γ.1 '' B, k u := (h36p_c_image_m γ.1 measurableSet_closedBall hBH k).symm
      _ = ∫⁻ u in upperHalf, (h36p_m γ.1 '' B).indicator k u := by
          rw [setLIntegral_indicator (hBimg γ.1), inter_eq_left.2]
          rintro _ ⟨w, hw, rfl⟩
          exact h36p_m_mem γ.1 (hBH hw)
  have hsum : a * ∑' γ : Γ, ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 *
      ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) ≤
      N * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * ζ.im ^ 2)⁻¹)) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : Γ, a * ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 *
          ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)
        ≤ ∑' γ : Γ, ∫⁻ u in upperHalf, (h36p_m γ.1 '' B).indicator k u := ENNReal.tsum_le_tsum hterm
      _ = ∫⁻ u in upperHalf, ∑' γ : Γ, (h36p_m γ.1 '' B).indicator k u :=
          (lintegral_tsum (μ := volume.restrict upperHalf)
            (f := fun (γ : Γ) (u : ℂ) => (h36p_m γ.1 '' B).indicator k u)
            fun γ => (hkm.indicator (hBimg γ.1)).aemeasurable).symm
      _ ≤ ∫⁻ u in upperHalf, N * k u := lintegral_mono fun u => hN k u
      _ = N * ∫⁻ u in upperHalf, k u := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)
      _ = N * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * ζ.im ^ 2)⁻¹)) := by
          rw [hkdef, h36p_c_kernel_area (h36p_c_conj_mem hζ), conj_im, neg_sq]
  have e4 : ENNReal.ofReal ((4 * ζ.im ^ 2)⁻¹) =
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal ((ζ.im ^ 2)⁻¹) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  calc ∑' γ : Γ, ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 * ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)
      = a⁻¹ * (a * ∑' γ : Γ, ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 *
          ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
    _ ≤ a⁻¹ * (N * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((4 * ζ.im ^ 2)⁻¹))) :=
        mul_le_mul_right hsum _
    _ = a⁻¹ * (N * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal (1 / 4))) * ENNReal.ofReal ((ζ.im ^ 2)⁻¹) := by
        rw [e4]
        simp only [mul_assoc]

/-- **Kernel invariance (pointwise)**: for `δ ∈ Γ`, `φ ∈ A(Γ, F)` and `ζ, z ∈ ℍ`,
`K_φ(ζ, δ⁻¹z) j(δ⁻¹, z)⁻⁴ = |j(δ, ζ)|⁻⁴ K_φ(δζ, z)`, `j(γ, z) = cz + d` (`Im δζ = Im ζ/|j(δ, ζ)|²`,
`φ(δζ) = φ(ζ) j(δ, ζ)⁴`, and `j(δ, ζ̄)(δζ̄ - z) = j(δ⁻¹, z)(ζ̄ - δ⁻¹z)`). -/
theorem h36p_c_kinv {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ) {ζ z : ℂ} (hζ : ζ ∈ upperHalf)
    (hz : z ∈ upperHalf) :
    h36p_c_K φ ζ (h36p_m δ⁻¹ z) / (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
      ((‖(δ 1 0 : ℂ) * ζ + δ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * h36p_c_K φ (h36p_m δ ζ) z := by
  have hdet := b33_d_det δ
  have hy : 0 < ζ.im := hζ
  have hv : 0 < z.im := hz
  have e00 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 = δ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e01 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 = -δ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e10 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = -δ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e11 : (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 = δ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hW : h36p_m δ⁻¹ z ∈ upperHalf := h36p_m_mem δ⁻¹ hz
  have hJ : ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 ≠ 0 :=
    k24_d_den_ne_zero (b33_d_det δ⁻¹) hv.ne'
  have hWJ : h36p_m δ⁻¹ z * (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) =
      ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℂ) * z +
        (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 := by
    unfold h36p_m
    exact div_mul_cancel₀ _ hJ
  have hA : (δ 1 0 : ℂ) * ζ + δ 1 1 ≠ 0 := k24_d_den_ne_zero hdet hy.ne'
  have hAc : (δ 1 0 : ℂ) * conj ζ + δ 1 1 ≠ 0 :=
    k24_d_den_ne_zero hdet (by rw [conj_im]; linarith)
  have hconj : conj (h36p_m δ ζ) = ((δ 0 0 : ℂ) * conj ζ + δ 0 1) / ((δ 1 0 : ℂ) * conj ζ + δ 1 1) := by
    simp [h36p_m, map_div₀]
  have hφu : φ (h36p_m δ ζ) = φ ζ * ((δ 1 0 : ℂ) * ζ + δ 1 1) ^ 4 := by
    have hA' := hφ.2.2 δ hδ ζ hζ
    rw [← hA', div_mul_cancel₀ _ (pow_ne_zero _ hA)]
    rfl
  have him : ((h36p_m δ ζ).im : ℂ) =
      (ζ.im : ℂ) / (((δ 1 0 : ℂ) * ζ + δ 1 1) * conj ((δ 1 0 : ℂ) * ζ + δ 1 1)) := by
    rw [Complex.mul_conj]
    have e : (h36p_m δ ζ).im = ζ.im / Complex.normSq ((δ 1 0 : ℂ) * ζ + δ 1 1) := by
      unfold h36p_m
      rw [Complex.div_im]
      simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
      rw [div_sub_div_same]
      congr 1
      linear_combination ζ.im * hdet
    rw [e]
    push_cast
    ring
  have hnrm : ((‖(δ 1 0 : ℂ) * ζ + δ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) =
      ((((δ 1 0 : ℂ) * ζ + δ 1 1) * conj ((δ 1 0 : ℂ) * ζ + δ 1 1)) ^ 2)⁻¹ := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hcA : conj ((δ 1 0 : ℂ) * ζ + δ 1 1) = (δ 1 0 : ℂ) * conj ζ + δ 1 1 := by simp
  have hkey : ((δ 0 0 : ℂ) * conj ζ + δ 0 1) / ((δ 1 0 : ℂ) * conj ζ + δ 1 1) - z =
      (((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
        (δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) * (conj ζ - h36p_m δ⁻¹ z) /
        ((δ 1 0 : ℂ) * conj ζ + δ 1 1) := by
    rw [eq_div_iff hAc, sub_mul, div_mul_cancel₀ _ hAc]
    rw [e00, e01, e10, e11] at hWJ
    rw [e10, e11]
    push_cast at hWJ ⊢
    linear_combination hWJ
  have hZW : conj ζ - h36p_m δ⁻¹ z ≠ 0 := h36p_c_conj_sub_ne hζ hW
  have hAc' : conj ζ * (δ 1 0 : ℂ) + δ 1 1 ≠ 0 := by rwa [mul_comm]
  have hA' : ζ * (δ 1 0 : ℂ) + δ 1 1 ≠ 0 := by rwa [mul_comm]
  unfold h36p_c_K
  rw [hφu, him, hnrm, hconj, hcA, hkey]
  field_simp

/-- **Unfolding as a measure identity**: `Σ_{γ ∈ Γ} γ_*(|cz + d|⁻⁴ dA|_F) = m · dA|_ℍ`, i.e. `h36p_unfold` for
every measurable `g ≥ 0` (`Measure.ext_of_lintegral`). -/
theorem h36p_c_sum_measure (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    Measure.sum (fun γ : Γ => ((volume.restrict F).withDensity
      (fun z => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4))).map (h36p_m γ.1)) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) • volume.restrict upperHalf := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul, ← h36p_unfold hΓ hF hg]
  refine tsum_congr fun γ => ?_
  have hρ : Measurable fun z : ℂ => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) := by fun_prop
  rw [lintegral_map hg (h36p_m_measurable γ.1),
    lintegral_withDensity_eq_lintegral_mul _ hρ
      (show Measurable fun a => g (h36p_m γ.1 a) from hg.comp (h36p_m_measurable γ.1))]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]

/-- **Unfolding for integrable `G`**: for `G` integrable on `ℍ`,
`Σ_{γ ∈ Γ} ∫_F |cz + d|⁻⁴ G(γz) dz = m ∫_ℍ G` (`h36p_c_sum_measure` and `integral_sum_measure`). -/
theorem h36p_c_unfold_int (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {G : ℂ → ℂ}
    (hG : IntegrableOn G upperHalf) :
    ∑' γ : Γ, ∫ z in F, ((‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * G (h36p_m γ.1 z) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * ∫ z in upperHalf, G z := by
  set ρ : Γ → ℂ → ℝ≥0∞ := fun γ z => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) with hρdef
  have hρm : ∀ γ : Γ, Measurable (ρ γ) := fun γ => by
    rw [hρdef]
    fun_prop
  set μs : Γ → Measure ℂ := fun γ => ((volume.restrict F).withDensity (ρ γ)).map (h36p_m γ.1) with hμs
  have hS : Measure.sum μs = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) • volume.restrict upperHalf :=
    h36p_c_sum_measure hΓ hF
  have hGi : Integrable G (Measure.sum μs) := by
    rw [hS]
    exact hG.smul_measure (ENNReal.natCast_ne_top _)
  have h1 := integral_sum_measure hGi
  rw [hS, integral_smul_measure, ENNReal.toReal_natCast] at h1
  have h2 : ∀ γ : Γ, ∫ x, G x ∂μs γ =
      ∫ z in F, ((‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * G (h36p_m γ.1 z) := by
    intro γ
    have hm : AEStronglyMeasurable G (μs γ) := (hGi.mono_measure (Measure.le_sum μs γ)).aestronglyMeasurable
    rw [hμs] at hm ⊢
    simp only at hm ⊢
    rw [integral_map (h36p_m_measurable γ.1).aemeasurable hm,
      integral_withDensity_eq_integral_toReal_smul (hρm γ) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hρdef]
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  rw [← tsum_congr h2, ← h1, Complex.real_smul, Complex.ofReal_natCast]

/-- **Integrability of the reproducing integrand of an automorphic form**: for `φ ∈ A(Γ, F)` and `z ∈ ℍ`,
`η ↦ K_φ(η, z) = (Im η)² φ(η)/(η̄ - z)⁴` is integrable on `ℍ`.  Unfold `m ∬_ℍ |K_φ(·, z)|` to `F`
(`h36p_unfold`), turn each term into `|K_φ(ζ, γz)| |cz + d|⁻⁴` by kernel invariance (`h36p_c_kinv`,
`γ ↦ γ⁻¹`), and bound the sum over `γ` by the Poincaré series `h36p_c_pser`: `≤ C ∬_F |φ| < ∞`. -/
theorem h36p_c_Gz_int (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun η => h36p_c_K φ η z) upperHalf := by
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hH : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hφc : ContinuousOn φ upperHalf := hφ.1.continuousOn
  have hc := h36p_c_K_continuousOn_left hφc hz
  refine ⟨hc.aestronglyMeasurable hH, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [← ofReal_norm]
  classical
  set g : ℂ → ℝ≥0∞ := upperHalf.piecewise (fun η => ENNReal.ofReal ‖h36p_c_K φ η z‖) 0 with hgdef
  have hg : Measurable g :=
    (ENNReal.continuous_ofReal.comp_continuousOn hc.norm).measurable_piecewise continuousOn_const hH
  have hU := h36p_unfold hΓ hF hg
  have hgH : ∫⁻ η in upperHalf, g η = ∫⁻ η in upperHalf, ENNReal.ofReal ‖h36p_c_K φ η z‖ :=
    setLIntegral_congr_fun hH fun η hη => by rw [hgdef, piecewise_eq_of_mem _ _ _ hη]
  set T : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℂ → ℝ≥0∞ := fun γ ζ =>
    ENNReal.ofReal ‖h36p_c_K φ ζ (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4‖ with hTdef
  have hterm : ∀ γ : Γ, ∫⁻ ζ in F, g (h36p_m γ.1 ζ) *
      ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * ζ + γ.1 1 1‖⁻¹ ^ 4) = ∫⁻ ζ in F, T γ.1⁻¹ ζ := by
    intro γ
    refine setLIntegral_congr_fun hFm fun ζ hζ => ?_
    rw [hgdef, piecewise_eq_of_mem _ _ _ (h36p_m_mem γ.1 (hFH hζ)), hTdef]
    show _ = ENNReal.ofReal ‖h36p_c_K φ ζ (h36p_m γ.1⁻¹ z) /
      (((γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
        (γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4‖
    rw [h36p_c_kinv hφ γ.2 (hFH hζ) hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), ENNReal.ofReal_mul (by positivity), mul_comm]
  rw [tsum_congr hterm] at hU
  have hre : ∑' γ : Γ, ∫⁻ ζ in F, T γ.1⁻¹ ζ = ∑' γ : Γ, ∫⁻ ζ in F, T γ.1 ζ :=
    (Equiv.inv Γ).tsum_eq (fun γ : Γ => ∫⁻ ζ in F, T γ.1 ζ)
  have hTm : ∀ γ : Γ, AEMeasurable (T γ.1) (volume.restrict F) := by
    intro γ
    have hc' : ContinuousOn (fun ζ => h36p_c_K φ ζ (h36p_m γ.1 z) /
        ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4) upperHalf :=
      (h36p_c_K_continuousOn_left hφc (h36p_m_mem γ.1 hz)).div_const _
    exact ((hc'.mono hFH).aestronglyMeasurable hFm).aemeasurable.norm.ennreal_ofReal
  rw [hre, ← lintegral_tsum hTm] at hU
  obtain ⟨C, hC, hCb⟩ := h36p_c_pser hΓ hz
  have hbd : ∫⁻ ζ in F, ∑' γ : Γ, T γ.1 ζ ≤ ∫⁻ ζ in F, C * ENNReal.ofReal ‖φ ζ‖ := by
    refine setLIntegral_mono' hFm fun ζ hζ => ?_
    have hy : 0 < ζ.im := hFH hζ
    have e : ∀ γ : Γ, T γ.1 ζ = ENNReal.ofReal (ζ.im ^ 2 * ‖φ ζ‖) *
        ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 * ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) := by
      intro γ
      rw [hTdef]
      show ENNReal.ofReal ‖h36p_c_K φ ζ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4‖ = _
      rw [norm_div, h36p_c_K_norm, norm_pow, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_eq_mul_inv, ← inv_pow]
      ring
    rw [tsum_congr e, ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (ζ.im ^ 2 * ‖φ ζ‖) * ∑' γ : Γ, ENNReal.ofReal (‖h36p_m γ.1 z - conj ζ‖⁻¹ ^ 4 *
          ‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4)
        ≤ ENNReal.ofReal (ζ.im ^ 2 * ‖φ ζ‖) * (C * ENNReal.ofReal ((ζ.im ^ 2)⁻¹)) :=
          mul_le_mul_right (hCb ζ (hFH hζ)) _
      _ = C * ENNReal.ofReal ‖φ ζ‖ := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
  have hfin : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ η in upperHalf, g η < ⊤ := by
    rw [← hU]
    refine lt_of_le_of_lt hbd ?_
    rw [lintegral_const_mul' _ _ hC.ne]
    exact ENNReal.mul_lt_top hC hφ.2.1
  rw [← hgH]
  have h1 : (1 : ℝ≥0∞) ≤ (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) := by
    exact_mod_cast h36p_mult_pos
  calc ∫⁻ η in upperHalf, g η = 1 * ∫⁻ η in upperHalf, g η := (one_mul _).symm
    _ ≤ (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ η in upperHalf, g η := mul_le_mul_left h1 _
    _ < ⊤ := hfin

/-- **Holomorphy of the Bergman projection**: for measurable `S ⊆ ℍ` and `h` continuous on `ℍ` with
`∫_S |h| < ∞`, `w ↦ ∫_S (Im ζ)² h(ζ)/(ζ̄ - w)⁴` is holomorphic on `ℍ` (differentiation under the integral,
dominated near `w₀` by `4 |h|/δ³`, `δ = Im w₀/2`). -/
theorem h36p_c_beta_diff {S : Set ℂ} (hS : MeasurableSet S) (hSH : S ⊆ upperHalf) {h : ℂ → ℂ}
    (hh : ContinuousOn h upperHalf) (hhi : ∫⁻ ζ in S, ENNReal.ofReal ‖h ζ‖ < ⊤) :
    DifferentiableOn ℂ (fun w => ∫ ζ in S, h36p_c_K h ζ w) upperHalf := by
  intro w₀ hw₀
  have hv : 0 < w₀.im := hw₀
  set δ : ℝ := w₀.im / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ w ∈ ball w₀ δ, δ ≤ w.im := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_im_le_norm (w - w₀)
    rw [sub_im] at h1
    have := (abs_le.1 (h1.trans hw.le)).1
    linarith
  have hballH : ∀ w ∈ ball w₀ δ, w ∈ upperHalf := fun w hw =>
    show 0 < w.im from lt_of_lt_of_le hδ (hball w hw)
  have hint := h36p_c_integrableOn hh hS hSH hhi
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun w ζ => h36p_c_K h ζ w)
    (F' := fun w ζ => 4 * ((ζ.im : ℂ) ^ 2 * h ζ) / (conj ζ - w) ^ 5) (x₀ := w₀)
    (bound := fun ζ => 4 * ‖h ζ‖ / δ ^ 3) (ball_mem_nhds w₀ hδ)
    ((isOpen_upperHalf.eventually_mem hw₀).mono fun w hw =>
      (h36p_c_K_integrableOn hh hS hSH hhi hw).aestronglyMeasurable)
    (h36p_c_K_integrableOn hh hS hSH hhi hw₀) ?_ ?_ ((hint.norm.const_mul 4).div_const _) ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine ContinuousOn.aestronglyMeasurable ?_ hS
    refine ContinuousOn.div (continuousOn_const.mul (ContinuousOn.mul (by fun_prop) (hh.mono hSH)))
      (((Complex.continuous_conj.sub continuous_const).pow 5).continuousOn) ?_
    intro ζ hζ
    exact pow_ne_zero _ (h36p_c_conj_sub_ne (hSH hζ) hw₀)
  · refine ae_restrict_of_forall_mem hS fun ζ hζ w hw => ?_
    have hy : 0 < ζ.im := hSH hζ
    have hN := h36p_c_im_add_le ζ w
    have hδw := hball w hw
    have hNpos : 0 < ‖conj ζ - w‖ := by linarith
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : ζ.im ^ 2 * δ ^ 3 ≤ ‖conj ζ - w‖ ^ 5 := by
      calc ζ.im ^ 2 * δ ^ 3 ≤ (ζ.im + δ) ^ 2 * (ζ.im + δ) ^ 3 := by
            gcongr <;> linarith
        _ = (ζ.im + δ) ^ 5 := by ring
        _ ≤ ‖conj ζ - w‖ ^ 5 := by
            gcongr
            linarith
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left h5 (norm_nonneg (h ζ))]
  · refine ae_restrict_of_forall_mem hS fun ζ hζ w hw => ?_
    have hne : conj ζ - w ≠ 0 := h36p_c_conj_sub_ne (hSH hζ) (hballH w hw)
    have h1 := ((hasDerivAt_id' w).const_sub (conj ζ)).pow 4
    have h2 := (hasDerivAt_const w ((ζ.im : ℂ) ^ 2 * h ζ)).div h1 (pow_ne_zero 4 hne)
    unfold h36p_c_K
    convert h2 using 1
    norm_num
    field_simp

/-- **`L¹` bound of the Bergman projection**: for measurable `S ⊆ ℍ` and `h` continuous on `ℍ` with
`∫_S |h| < ∞`, `∬_ℍ |∫_S (Im ζ)² h(ζ)/(ζ̄ - w)⁴ dζ| dw < ∞` (Tonelli and the kernel area). -/
theorem h36p_c_beta_L1 {S : Set ℂ} (hS : MeasurableSet S) (hSH : S ⊆ upperHalf) {h : ℂ → ℂ}
    (hh : ContinuousOn h upperHalf) (hhi : ∫⁻ ζ in S, ENNReal.ofReal ‖h ζ‖ < ⊤) :
    ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in S, h36p_c_K h ζ w‖ < ⊤ := by
  have hA : ∫⁻ ζ in S, ENNReal.ofReal (‖h ζ‖ / 4) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg (h ζ)])) hhi
  calc ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in S, h36p_c_K h ζ w‖
      ≤ ∫⁻ w in upperHalf, ∫⁻ ζ in S, ENNReal.ofReal ‖h36p_c_K h ζ w‖ := by
        refine lintegral_mono fun w => ?_
        simp_rw [ofReal_norm]
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ζ in S, ∫⁻ w in upperHalf, ENNReal.ofReal ‖h36p_c_K h ζ w‖ :=
        lintegral_lintegral_swap (h36p_c_K_aesm hh hS hSH).aemeasurable.norm.ennreal_ofReal
    _ = volume (ball (0 : ℂ) 1) * ∫⁻ ζ in S, ENNReal.ofReal (‖h ζ‖ / 4) := h36p_c_tonelli hS hSH h
    _ < ⊤ := ENNReal.mul_lt_top measure_ball_lt_top hA

/-- **[P3, stub] Surjectivity of `Θ`.**  Every `φ ∈ A(Γ, F)` is the Poincaré series `Θf` of an integrable
holomorphic `f` on `ℍ`.  Route: `f = m⁻¹ β(𝟙_F φ)` with `β(h)(w) = (12/π) ∬_ℍ (Im ζ)² h(ζ)/(ζ̄ - w)⁴`;
holomorphic by differentiation under the integral; `∬_ℍ |f| ≤ 3 m⁻¹ ∬_F |φ|` (Tonelli, kernel area
`π/(4 (Im ζ)²)`); `Θf = φ` on `ℍ` by kernel invariance (scout C's `h36_kernel_invariance`), unfolding
(`h36p_unfold`) and the reproducing formula for `φ` (integrable kernel integrand: unfolding again). -/
theorem h36p_theta_surj (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ φ ∈ integrableAutomorphicQD Γ F, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf ∧
      phiArea f upperHalf < ⊤ ∧ ∀ z ∈ upperHalf, φ z = h36p_theta Γ f z := by
  intro φ hφ
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hφc : ContinuousOn φ upperHalf := hφ.1.continuousOn
  have hm0 : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast h36p_mult_pos.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  set c : ℂ := (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ)⁻¹ * (12 / π : ℂ) with hcdef
  refine ⟨fun w => c * ∫ ζ in F, h36p_c_K φ ζ w, ?_, ?_, ?_⟩
  · exact (h36p_c_beta_diff hFm hFH hφc hφ.2.1).const_mul c
  · unfold phiArea
    calc ∫⁻ w in upperHalf, ENNReal.ofReal ‖c * ∫ ζ in F, h36p_c_K φ ζ w‖
        = ∫⁻ w in upperHalf, ENNReal.ofReal ‖c‖ * ENNReal.ofReal ‖∫ ζ in F, h36p_c_K φ ζ w‖ := by
          simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      _ = ENNReal.ofReal ‖c‖ * ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, h36p_c_K φ ζ w‖ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h36p_c_beta_L1 hFm hFH hφc hφ.2.1)
  · intro z hz
    have hGi := h36p_c_Gz_int hΓ hF hφ hz
    have hU := h36p_c_unfold_int hΓ hF hGi
    have hR := h36p_c_rp_upper hφ.1 hz hGi
    have hterm : ∀ γ : Γ, c * (∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1 z)) /
        ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4 =
        c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1 z) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4 := by
      intro γ
      rw [mul_div_assoc, integral_div]
    have hterm2 : ∀ γ : Γ, c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1⁻¹ z) /
        (((γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
        c * ∫ ζ in F, ((‖(γ.1 1 0 : ℂ) * ζ + γ.1 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * h36p_c_K φ (h36p_m γ.1 ζ) z := by
      intro γ
      congr 1
      exact setIntegral_congr_fun hFm fun ζ hζ => h36p_c_kinv hφ γ.2 (hFH hζ) hz
    have hre := (Equiv.inv Γ).tsum_eq (fun γ : Γ => c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1 z) /
      ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4)
    show φ z = ∑' γ : Γ, c * (∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1 z)) / ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4
    rw [tsum_congr hterm, ← hre]
    show φ z = ∑' γ : Γ, c * ∫ ζ in F, h36p_c_K φ ζ (h36p_m γ.1⁻¹ z) /
        (((γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (γ.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4
    rw [tsum_congr hterm2, tsum_mul_left, hU, hR, hcdef]
    field_simp

/-! ### A.6 Proved glue: T3 (the kernel condition) and `poincare_series_surjective` -/

/-- **T3.**  A bounded measurable `Γ`-compatible `κ`, vanishing on the closed lower half-plane and orthogonal
to `A(Γ, F)`, annihilates the kernels `(ζ - z)⁻³(ζ - w)⁻¹` (`z, w ∈ 𝕃`) — the hypothesis of
`h35b_bers_small` — by `h36p_poincare` applied to the kernel (`h36p_kernel_L1`), since `m ≠ 0`. -/
theorem h36p_kernel_cond (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict upperHalf)) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) (hκΓ : IsGammaCompatible Γ κ)
    (hκ0 : ∀ z : ℂ, z.im ≤ 0 → κ z = 0)
    (horth : ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F κ φ = 0) :
    ∀ z ∈ lowerHalf, ∀ w ∈ lowerHalf, ∫ ζ, κ ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0 := by
  intro z hz w hw
  obtain ⟨hd, hA⟩ := h36p_kernel_L1 hz hw
  obtain ⟨hmem, hpair⟩ := h36p_poincare hΓ hF hd hA
  have h1 := hpair κ hκm ⟨M, hκM⟩ hκΓ
  rw [horth _ hmem] at h1
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast h36p_mult_pos.ne'
  have h2 : ∫ ζ in upperHalf, κ ζ * (1 / ((ζ - z) ^ 3 * (ζ - w))) = 0 :=
    (mul_eq_zero.1 h1).resolve_left hm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := upperHalf)]
  · rw [← h2]
    congr 1
    funext ζ
    rw [mul_one_div]
  · intro ζ hζ
    have hζ' : ¬ (0 < ζ.im) := hζ
    rw [hκ0 ζ (not_lt.1 hζ'), zero_div]

/-- The statement of `poincare_series_surjective` (placed before `lemma36_2_kernel_orthogonal`, which uses it):
`h36p_theta_surj` gives `f` with `Θf = φ` on `ℍ`, and `h36p_poincare` the pairing identity. -/
theorem h36p_pss (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ φ ∈ integrableAutomorphicQD Γ F, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf ∧ phiArea f upperHalf < ⊤ ∧
      (∀ z ∈ upperHalf, φ z = ∑' γ : Γ, f ((γ.1 0 0 * z + γ.1 0 1) / (γ.1 1 0 * z + γ.1 1 1)) /
        ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4) ∧
      ∀ μ : BeltramiGamma Γ, (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) *
        ∫ z in upperHalf, μ.1.1 z * f z = beltramiPairing F μ.1.1 φ := by
  intro φ hφ
  obtain ⟨f, hf, hfA, hθ⟩ := h36p_theta_surj hΓ hF φ hφ
  refine ⟨f, hf, hfA, hθ, fun μ => ?_⟩
  obtain ⟨-, hpair⟩ := h36p_poincare hΓ hF hf hfA
  obtain ⟨⟨k, -, -, hμm, hμb⟩, -⟩ := μ.1.2
  rw [Measure.restrict_univ] at hμm hμb
  rw [hpair μ.1.1 hμm.restrict ⟨k, ae_restrict_of_ae hμb⟩ μ.2]
  obtain ⟨hFH, hFm, -⟩ := hF
  unfold beltramiPairing
  exact setIntegral_congr_fun hFm fun z hz => by rw [hθ z (hFH hz)]

/-- **Lemma 36.2 (part 4)**: `DΦ(0)(μ) = 0` iff `∬_ℍ μ f = 0` for all polynomials `f`
(the Taylor coefficients of `P(μ)` at `∞` are `-(6/π) n(n-1)(n-2) ∬ ζ^{n-3} μ`), iff
`∬_ℍ μ f = 0` for all integrable holomorphic `f`, iff `∬_{ℍ/G} μ φ = 0` for all `φ ∈ A(ℍ, G)`
(every `φ ∈ A(ℍ, G)` is a Poincaré series `Θf = Σ (f ∘ γ) γ'²`): `T₀N ⊥ A(S)`. -/
theorem lemma36_2_kernel_orthogonal (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) :
    IsLocallyTrivialBeltrami μ.1.1 ↔ ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F μ.1.1 φ = 0 := by
  obtain ⟨⟨k, -, -, hμm, hμb⟩, hμ0⟩ := μ.1.2
  rw [Measure.restrict_univ] at hμm hμb
  have hμm' : AEStronglyMeasurable μ.1.1 (volume.restrict upperHalf) := hμm.restrict
  have hμM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ.1.1 z‖ ≤ k := ae_restrict_of_ae hμb
  have hc : (-(6 / π : ℂ)) ≠ 0 := by
    simp
  constructor
  · intro hloc φ hφ
    obtain ⟨f, hf, hfA, -, hpair⟩ := h36p_pss hΓ hF φ hφ
    have hκ : ∀ z ∈ lowerHalf, ∫ ζ in upperHalf, μ.1.1 ζ / (ζ - z) ^ 4 = 0 := by
      intro z hz
      have h := hloc z hz
      unfold bersDerivative at h
      exact (mul_eq_zero.1 h).resolve_left hc
    rw [← hpair μ, h36p_orth_integrable hμm' hμM hκ hf hfA, mul_zero]
  · intro horth z hz
    have h := h36p_kernel_cond hΓ hF hμm' hμM μ.2 hμ0 horth z hz z hz
    have e : ∫ ζ in upperHalf, μ.1.1 ζ / (ζ - z) ^ 4 = ∫ ζ, μ.1.1 ζ / ((ζ - z) ^ 3 * (ζ - z)) := by
      have e1 : (fun ζ => μ.1.1 ζ / ((ζ - z) ^ 3 * (ζ - z))) = fun ζ => μ.1.1 ζ / (ζ - z) ^ 4 := by
        funext ζ
        ring
      rw [e1]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
      have hζ' : ¬ (0 < ζ.im) := hζ
      rw [hμ0 ζ (not_lt.1 hζ'), zero_div]
    unfold bersDerivative
    rw [e, h, mul_zero]

/-- §36.3: the Poincaré series `Θf = Σ_{γ ∈ G} (f ∘ γ) γ'²` of an integrable holomorphic `f` on `ℍ`
is an integrable automorphic quadratic differential, and every element of `A(ℍ, G)` is of this
form; `∬_ℍ μ f = ∬_F μ Θf` for `G`-compatible `μ`.

**Correction.**  The sum `∑' γ : Γ` runs over `Γ ⊆ SL(2, ℝ)`, so when `-1 ∈ Γ` every Möbius map is
counted twice (`Γ = {±1}`, `F = ℍ` was a counterexample); the pairing identity now carries the
multiplicity `|Γ ∩ {±1}|`. -/
theorem poincare_series_surjective (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ φ ∈ integrableAutomorphicQD Γ F, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf ∧ phiArea f upperHalf < ⊤ ∧
      (∀ z ∈ upperHalf, φ z = ∑' γ : Γ, f ((γ.1 0 0 * z + γ.1 0 1) / (γ.1 1 0 * z + γ.1 1 1)) /
        ((γ.1 1 0 : ℂ) * z + γ.1 1 1) ^ 4) ∧
      ∀ μ : BeltramiGamma Γ, (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) *
        ∫ z in upperHalf, μ.1.1 z * f z = beltramiPairing F μ.1.1 φ := by
  exact h36p_pss hΓ hF

/-- §36.3: the Poincaré distance `d(z, w) = ½ ln((1 + r)/(1 - r))`, `r = |(z - w)/(1 - z̄w)|`, of two
points of the unit disc (the values of Beltrami coefficients). -/
def discPoincareDist (z w : ℂ) : ℝ :=
  (1 / 2) * Real.log ((1 + ‖(z - w) / (1 - conj z * w)‖) / (1 - ‖(z - w) / (1 - conj z * w)‖))

/-- §36.3: `τ(ν, π) = ess sup_{z ∈ ℍ} d(ν(z), π(z))`. -/
def beltramiPoincareDist (ν π' : ℂ → ℂ) : ℝ :=
  (essSup (fun z => ENNReal.ofReal (discPoincareDist (ν z) (π' z))) (volume.restrict upperHalf)).toReal

/-! ### s36c track (coordinator 553e2d), part B: the Poincaré distance of coefficients and `½ ln K` -/

/-- `|(a - b)/(1 - ā b)| = |(a - b)/(1 - b̄ a)|`: the two denominators are complex conjugate. -/
theorem c36_b_norm_conj_denom (a b : ℂ) :
    ‖(a - b) / (1 - conj a * b)‖ = ‖(a - b) / (1 - conj b * a)‖ := by
  rw [norm_div, norm_div, ← Complex.norm_conj (1 - conj a * b)]
  congr 2
  rw [map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]

/-- `t ↦ ½ ln((1 + t)/(1 - t))` commutes with the essential supremum: if `0 ≤ ρ ≤ c < 1` a.e. for a
nonzero measure, then `ess sup ½ ln((1 + ρ)/(1 - ρ)) = ½ ln((1 + ess sup ρ)/(1 - ess sup ρ))` (a
continuous monotone map passes through the `limsup`, after clamping at `c`; the pattern of
`ut_e_essSup_quot`). -/
theorem c36_b_essSup_halfLog {m : Measure ℂ} (hm : m ≠ 0) {ρ : ℂ → ℝ} {c : ℝ} (hc : c < 1)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρc : ∀ᵐ z ∂m, ρ z ≤ c) :
    essSup (fun z => ENNReal.ofReal ((1 / 2) * Real.log ((1 + ρ z) / (1 - ρ z)))) m =
      ENNReal.ofReal ((1 / 2) * Real.log ((1 + (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal) /
        (1 - (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal))) := by
  have hne : (ae m).NeBot := ae_neBot.2 hm
  obtain ⟨z₀, hz₀⟩ := hρc.exists
  have hc0 : 0 ≤ c := (hρ0 z₀).trans hz₀
  set c' : ℝ≥0∞ := ENNReal.ofReal c
  have hc't : c' ≠ ⊤ := ENNReal.ofReal_ne_top
  set T : ℝ≥0∞ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 / 2) * Real.log ((1 + (min x c').toReal) / (1 - (min x c').toReal))) with hT
  have hmin : ∀ x : ℝ≥0∞, 0 ≤ (min x c').toReal ∧ (min x c').toReal ≤ c := fun x =>
    ⟨ENNReal.toReal_nonneg, by
      rw [← ENNReal.toReal_ofReal hc0]
      exact ENNReal.toReal_mono hc't (min_le_right _ _)⟩
  have hqpos : ∀ x : ℝ≥0∞, 0 < (1 + (min x c').toReal) / (1 - (min x c').toReal) := fun x => by
    have := hmin x
    exact div_pos (by linarith) (by linarith)
  have hTmono : Monotone T := by
    intro x y hxy
    have hs := hmin x
    have ht := hmin y
    have hst : (min x c').toReal ≤ (min y c').toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hc't (min_le_right _ _)) (min_le_min_right _ hxy)
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (hqpos x) ?_) (by norm_num)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hTcont : Continuous T := by
    have h1 : Continuous fun x : ℝ≥0∞ => (min x c').toReal :=
      ENNReal.continuousOn_toReal.comp_continuous (continuous_id.min continuous_const)
        fun x => ne_top_of_le_ne_top hc't (min_le_right _ _)
    have h2 : Continuous fun x : ℝ≥0∞ => (1 + (min x c').toReal) / (1 - (min x c').toReal) := by
      refine (continuous_const.add h1).div (continuous_const.sub h1) ?_
      intro x
      have := hmin x
      linarith
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul (h2.log fun x => (hqpos x).ne'))
  have hE : essSup (fun z => ENNReal.ofReal (ρ z)) m ≤ c' :=
    essSup_le_of_ae_le _ (by filter_upwards [hρc] with z hz using ENNReal.ofReal_le_ofReal hz)
  have key := hTmono.map_limsup_of_continuousAt (F := ae m) (fun z => ENNReal.ofReal (ρ z))
    hTcont.continuousAt
  have h1 : T (essSup (fun z => ENNReal.ofReal (ρ z)) m) =
      ENNReal.ofReal ((1 / 2) * Real.log ((1 + (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal) /
        (1 - (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal))) := by
    simp only [hT, min_eq_left hE]
  have h2 : (T ∘ fun z => ENNReal.ofReal (ρ z)) =ᵐ[m]
      fun z => ENNReal.ofReal ((1 / 2) * Real.log ((1 + ρ z) / (1 - ρ z))) := by
    filter_upwards [hρc] with z hz
    have hle : ENNReal.ofReal (ρ z) ≤ c' := ENNReal.ofReal_le_ofReal hz
    simp only [Function.comp_apply, hT, min_eq_left hle, ENNReal.toReal_ofReal (hρ0 z)]
  rw [← h1, ← essSup_congr_ae h2]
  exact key.symm

/-- The a.e. bound `|μ_f| ≤ k < 1` for a `K`-q.c. map `f` of `D`, with `k = (K - 1)/(K + 1)`. -/
theorem c36_b_dilatation_bound {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    0 ≤ (K - 1) / (K + 1) ∧ (K - 1) / (K + 1) < 1 ∧
      ∀ᵐ z ∂(volume.restrict D), ‖complexDilatation f z‖ ≤ (K - 1) / (K + 1) := by
  have hK1 : (1 : ℝ) ≤ K := hf.2.1
  refine ⟨div_nonneg (by linarith) (by linarith), ?_, (isKQC_maxDilatation_le hf).2⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- The pointwise identity behind §36.3: for q.c. `f, g` of `ℍ` with dilatations `ν, π`,
a.e. on `ℍ` `|μ_{f ∘ g⁻¹}(g z)| = |(ν - π)/(1 - ν̄ π)|(z)` (the chain rule `ahQ_comp_inv_dilatation`;
`|∂g/conj ∂g| = 1` since `∂g ≠ 0` where `J_g > 0`). -/
theorem c36_b_norm_dilatation_comp_inv {f g : ℂ → ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f upperHalf K₁)
    (hg : IsKQC g upperHalf K₂) {ν π' : ℂ → ℂ}
    (hν : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f z = ν z)
    (hπ : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation g z = π' z) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖complexDilatation (f ∘ Function.invFunOn g upperHalf) (g z)‖ =
        ‖(ν z - π' z) / (1 - conj (ν z) * π' z)‖ := by
  filter_upwards [ahQ_comp_inv_dilatation hf hg, thm9_6_cor2_jacobian_pos hg, hν, hπ]
    with z hCz hJz h1 h2
  have hdz : dz g z ≠ 0 := by
    intro h0
    unfold jacobian at hJz
    rw [h0, norm_zero] at hJz
    nlinarith [norm_nonneg (dzbar g z)]
  rw [hCz, h1, h2, norm_mul, norm_div (dz g z), Complex.norm_conj,
    div_self (norm_ne_zero_iff.2 hdz), mul_one, c36_b_norm_conj_denom]

/-- §36.3: for `g` with dilatation `π` and `f` with dilatation `ν`, `½ ln D_{f ∘ g⁻¹}(g(z)) = d(ν(z), π(z))`,
so `τ(ν, π) = ½ ln K[f ∘ g⁻¹]`. -/
theorem beltramiPoincareDist_eq_dilatation {f g : ℂ → ℂ} (hf : IsQuasiconformal f upperHalf)
    (hg : IsQuasiconformal g upperHalf) (hgs : g '' upperHalf = upperHalf) {ν π' : ℂ → ℂ}
    (hν : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f z = ν z)
    (hπ : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation g z = π' z) :
    (∀ᵐ z ∂(volume.restrict upperHalf),
      (1 / 2) * Real.log (dilatationQuotient (f ∘ Function.invFunOn g upperHalf) (g z)) = discPoincareDist (ν z) (π' z)) ∧
      ENNReal.ofReal (2 * beltramiPoincareDist ν π') = ENNReal.log (maxDilatation (f ∘ Function.invFunOn g upperHalf) upperHalf) := by
  obtain ⟨K₁, hf⟩ := hf
  obtain ⟨K₂, hg⟩ := hg
  set h : ℂ → ℂ := f ∘ Function.invFunOn g upperHalf with hhdef
  set ρ : ℂ → ℝ := fun z => ‖(ν z - π' z) / (1 - conj (ν z) * π' z)‖ with hρdef
  have hpt := c36_b_norm_dilatation_comp_inv hf hg hν hπ
  -- the a.e. bound `ρ ≤ 2k/(1 + k²) < 1`
  obtain ⟨hk₁0, hk₁1, hb₁⟩ := c36_b_dilatation_bound hf
  obtain ⟨hk₂0, hk₂1, hb₂⟩ := c36_b_dilatation_bound hg
  set k : ℝ := max ((K₁ - 1) / (K₁ + 1)) ((K₂ - 1) / (K₂ + 1)) with hkdef
  have hk0 : 0 ≤ k := le_max_of_le_left hk₁0
  have hk1 : k < 1 := max_lt hk₁1 hk₂1
  have hc1 : 2 * k / (1 + k ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - k)]
  have hρc : ∀ᵐ z ∂(volume.restrict upperHalf), ρ z ≤ 2 * k / (1 + k ^ 2) := by
    filter_upwards [hb₁, hb₂, hν, hπ] with z h1 h2 h3 h4
    show ‖(ν z - π' z) / (1 - conj (ν z) * π' z)‖ ≤ _
    rw [c36_b_norm_conj_denom, ← h3, ← h4]
    exact ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
  -- clause 1
  have hcl1 : ∀ᵐ z ∂(volume.restrict upperHalf),
      (1 / 2) * Real.log (dilatationQuotient h (g z)) = discPoincareDist (ν z) (π' z) := by
    filter_upwards [hpt] with z hz
    rw [dilatationQuotient, hz]
    rfl
  refine ⟨hcl1, ?_⟩
  -- `h = f ∘ g⁻¹` is q.c. on `ℍ`
  have hleft : LeftInvOn (Function.invFunOn g upperHalf) g upperHalf :=
    hg.2.2.1.2.1.leftInvOn_invFunOn
  have hinv : IsKQC (Function.invFunOn g upperHalf) upperHalf K₂ := by
    have h' := thm7_2_inv hg
    rwa [hgs] at h'
  have hinvimg : Function.invFunOn g upperHalf '' upperHalf ⊆ upperHalf := by
    have h' := hleft.image_image
    rw [hgs] at h'
    exact h'.le
  have hhK : IsKQC h upperHalf (K₂ * K₁) := thm7_1_comp hinv hf hinvimg
  -- `K[h] = ess sup_ℍ D_h = ess sup_ℍ D_h ∘ g = ess sup_ℍ (1 + ρ)/(1 - ρ)`
  have hm : volume.restrict upperHalf ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩
  have hK1 : maxDilatation h upperHalf =
      essSup (fun w => ENNReal.ofReal (dilatationQuotient h w)) (volume.restrict upperHalf) := by
    rw [maxDilatation]
    refine essSup_congr_ae ?_
    filter_upwards [thm9_6_cor2_jacobian_pos hhK] with w hJw
    have hdz : dz h w ≠ 0 := by
      intro h0
      unfold jacobian at hJw
      rw [h0, norm_zero] at hJw
      nlinarith [norm_nonneg (dzbar h w)]
    rw [UniversalTeichmuller.ut_e_quot_eq hdz]
    rfl
  have hK2 : essSup (fun w => ENNReal.ofReal (dilatationQuotient h w)) (volume.restrict upperHalf) =
      essSup (fun z => ENNReal.ofReal (dilatationQuotient h (g z))) (volume.restrict upperHalf) := by
    have h' := UniversalTeichmuller.ut_e_essSup_image hg (fun w => ENNReal.ofReal (dilatationQuotient h w))
    rwa [hgs] at h'
  have hK3 : essSup (fun z => ENNReal.ofReal (dilatationQuotient h (g z))) (volume.restrict upperHalf) =
      essSup (fun z => ENNReal.ofReal ((1 + ρ z) / (1 - ρ z))) (volume.restrict upperHalf) := by
    refine essSup_congr_ae ?_
    filter_upwards [hpt] with z hz
    rw [dilatationQuotient, hz]
  set E : ℝ := (essSup (fun z => ENNReal.ofReal (ρ z)) (volume.restrict upperHalf)).toReal with hEdef
  have hKeq : maxDilatation h upperHalf = ENNReal.ofReal ((1 + E) / (1 - E)) := by
    rw [hK1, hK2, hK3, UniversalTeichmuller.ut_e_essSup_quot hm hc1 (fun z => norm_nonneg _) hρc]
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hE1 : E < 1 := by
    refine lt_of_le_of_lt ?_ hc1
    refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith) (by positivity))
      (essSup_le_of_ae_le _ ?_)
    filter_upwards [hρc] with z hz
    exact ENNReal.ofReal_le_ofReal hz
  have hQ1 : 1 ≤ (1 + E) / (1 - E) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hlog0 : 0 ≤ Real.log ((1 + E) / (1 - E)) := Real.log_nonneg hQ1
  have hτ : beltramiPoincareDist ν π' = (1 / 2) * Real.log ((1 + E) / (1 - E)) := by
    have h' := c36_b_essSup_halfLog hm hc1 (fun z => norm_nonneg _) hρc
    rw [beltramiPoincareDist]
    change (essSup (fun z => ENNReal.ofReal ((1 / 2) * Real.log ((1 + ρ z) / (1 - ρ z))))
      (volume.restrict upperHalf)).toReal = _
    rw [h', ← hEdef]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [hKeq, hτ, ENNReal.log_ofReal_of_pos (by linarith), EReal.coe_ennreal_ofReal,
    show 2 * ((1 / 2) * Real.log ((1 + E) / (1 - E))) = Real.log ((1 + E) / (1 - E)) by ring,
    max_eq_left hlog0]

/-- §36.3: `d(z, 0) = artanh |z|`, since `(z - 0)/(1 - z̄·0) = z`. -/
theorem discPoincareDist_zero {z : ℂ} (hz : ‖z‖ < 1) :
    discPoincareDist z 0 = Real.artanh ‖z‖ := by
  have hsimp : ((z - 0) / (1 - conj z * 0) : ℂ) = z := by simp
  rw [discPoincareDist, hsimp,
    Real.artanh_eq_half_log ⟨by linarith [norm_nonneg z], hz.le⟩]

/-- `(‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖`. -/
theorem coe_nnnorm_eq_ofReal_norm (x : ℂ) : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- Every element of `BeltramiH` carries an a.e. bound by some `k < 1` on `ℍ`: the bound lives in
the subtype, stated for `volume.restrict univ`, and transfers to `volume.restrict upperHalf`. -/
theorem beltramiH_ae_bound (ν : BeltramiH) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν.1 z‖ ≤ k := by
  obtain ⟨⟨k, hk0, hk1, -, hbd⟩, -⟩ := ν.2
  refine ⟨k, hk0, hk1, ?_⟩
  exact hbd.filter_mono
    (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono (Set.subset_univ _) le_rfl))

/-- Hence `‖ν‖_∞` on `ℍ` is finite, so `beltramiNormH ν` is a faithful `.toReal` and not the junk
value `0`.  (This is what makes the `⊤` hazard of `eq35_8` inapplicable here.) -/
theorem beltramiH_essSup_ne_top (ν : BeltramiH) :
    essSup (fun z => (‖ν.1 z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤ := by
  obtain ⟨k, hk0, hk1, hbd⟩ := beltramiH_ae_bound ν
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (essSup_le_of_ae_le (ENNReal.ofReal k) ?_)
  filter_upwards [hbd] with z hz
  rw [coe_nnnorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hz

/-- The a.e. bound by `beltramiNormH`, from the definition of the essential supremum. -/
theorem ae_norm_le_beltramiNormH {μ : ℂ → ℂ}
    (hfin : essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ beltramiNormH μ := by
  filter_upwards [ENNReal.ae_le_essSup (fun z => (‖μ z‖₊ : ℝ≥0∞))] with z hz
  rw [beltramiNormH, show ‖μ z‖ = ((‖μ z‖₊ : ℝ≥0∞)).toReal by simp]
  exact (ENNReal.toReal_le_toReal (by simp) hfin).2 hz

/-- `beltramiNormH ν < 1` for `ν : BeltramiH`. -/
theorem beltramiNormH_lt_one (ν : BeltramiH) : beltramiNormH ν.1 < 1 := by
  obtain ⟨k, hk0, hk1, hbd⟩ := beltramiH_ae_bound ν
  have hle : essSup (fun z => (‖ν.1 z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)
      ≤ ENNReal.ofReal k := by
    refine essSup_le_of_ae_le (ENNReal.ofReal k) ?_
    filter_upwards [hbd] with z hz
    rw [coe_nnnorm_eq_ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hz
  have h := ENNReal.toReal_le_toReal (beltramiH_essSup_ne_top ν) ENNReal.ofReal_ne_top |>.2 hle
  rw [ENNReal.toReal_ofReal hk0] at h
  exact lt_of_le_of_lt h hk1

/-- `0 ≤ beltramiNormH μ`, since it is a `.toReal`. -/
theorem beltramiNormH_nonneg (μ : ℂ → ℂ) : 0 ≤ beltramiNormH μ := ENNReal.toReal_nonneg

/-- The algebraic step behind `discPoincareDist_sub_le`: writing `A = |1 - z̄w|`, `B = |z - w|`
and `r = |z|`, one has `A - 1 ≤ r (B - r)`.

Both sides of `A ≤ 1 - r² + rB` are non-negative, and squaring reduces the claim to
`2(1 - r²)(Re(z̄w) - r² + rB) ≥ 0`, i.e. to `Re(z̄(z - w)) ≤ |z̄(z - w)|` — which is just
`Complex.re_le_norm`. -/
theorem norm_one_sub_conj_mul_sub_one_le {z w : ℂ} (hz : ‖z‖ < 1) :
    ‖1 - conj z * w‖ - 1 ≤ ‖z‖ * (‖z - w‖ - ‖z‖) := by
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hr2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
  -- `Re(z̄(z-w)) ≤ |z̄(z-w)| = ‖z‖ ‖z-w‖`, i.e. `r² - Re(z̄w) ≤ r B`
  have hzz : (conj z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hkey : ‖z‖ ^ 2 - (conj z * w).re ≤ ‖z‖ * ‖z - w‖ := by
    have h1 : (conj z * (z - w)).re ≤ ‖conj z * (z - w)‖ := Complex.re_le_norm _
    rw [norm_mul, RCLike.norm_conj, mul_sub, Complex.sub_re, hzz] at h1
    exact h1
  -- expand the two squared norms
  have hA2 : ‖1 - conj z * w‖ ^ 2 = 1 - 2 * (conj z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, one_mul,
      Complex.conj_re]
    ring
  have hB2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (conj z * w).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.conj_re (conj z * w), map_mul, Complex.conj_conj]
  -- square and compare
  have hCnn : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖ := by positivity
  have hsq : ‖1 - conj z * w‖ ^ 2 ≤ (1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖) ^ 2 := by
    nlinarith [hA2, hB2, hkey, hr2, norm_nonneg (z - w), mul_nonneg hr0 (norm_nonneg (z - w))]
  have hle : ‖1 - conj z * w‖ ≤ 1 - ‖z‖ ^ 2 + ‖z‖ * ‖z - w‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hCnn] at h
  nlinarith [hle]

/-- `|1 - z̄w|² - |z - w|² = (1 - |z|²)(1 - |w|²)`: the identity behind the invariance of the
pseudo-hyperbolic distance. -/
theorem normSq_one_sub_conj_mul_sub_normSq_sub (z w : ℂ) :
    ‖1 - conj z * w‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  have hA2 : ‖1 - conj z * w‖ ^ 2 = 1 - 2 * (conj z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, one_mul,
      Complex.conj_re]
    ring
  have hB2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (conj z * w).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.conj_re (conj z * w), map_mul, Complex.conj_conj]
  rw [hA2, hB2]
  ring

/-- §36.3: the pointwise inequality with the explicit constant.  The sharp bound is
`-½log(1 - |w|²)`; `|w|²/(1 - |w|²)` is a convenient majorant, since `-log(1-u) ≤ u/(1-u)`.

Stated separately from `discPoincareDist_sub_le` because the `∃ α` there yields an *opaque* `α`,
and the `L∞` version (`lemma36_3`) needs `t ↦ α(t) t` to be **monotone** in order to bound it by its
value at `‖π‖_∞`; the explicit `t²/(1 - t²)` is. -/
theorem discPoincareDist_sub_le_explicit {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    discPoincareDist z w - discPoincareDist z 0
      ≤ ‖z - w‖ - ‖z‖ + ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hq0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hB0 : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
  have hr2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
  have hq2 : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith
  have hr1 : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hAB := normSq_one_sub_conj_mul_sub_normSq_sub z w
  have hA2pos : (0 : ℝ) < ‖1 - conj z * w‖ ^ 2 := by
    nlinarith [mul_pos hr2 hq2, sq_nonneg ‖z - w‖]
  have hA0 : (0 : ℝ) < ‖1 - conj z * w‖ := by
    rcases (norm_nonneg (1 - conj z * w)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hA2pos; norm_num at hA2pos
  have hBA : ‖z - w‖ < ‖1 - conj z * w‖ := by
    have h1 : ‖z - w‖ ^ 2 < ‖1 - conj z * w‖ ^ 2 := by nlinarith [mul_pos hr2 hq2]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  -- `d(z, 0) = log(1 + |z|) - ½ log(1 - |z|²)`
  have hd0 : discPoincareDist z 0 = Real.log (1 + ‖z‖) - (1 / 2) * Real.log (1 - ‖z‖ ^ 2) := by
    have hsimp : ((z - 0) / (1 - conj z * 0) : ℂ) = z := by simp
    rw [discPoincareDist, hsimp]
    have e : (1 + ‖z‖) / (1 - ‖z‖) = (1 + ‖z‖) ^ 2 / (1 - ‖z‖ ^ 2) := by
      rw [div_eq_div_iff hr1.ne' hr2.ne']
      ring
    rw [e, Real.log_div (by positivity) hr2.ne', Real.log_pow]
    push_cast
    ring
  -- `d(z, w) = log(A + B) - ½ log(1 - |z|²) - ½ log(1 - |w|²)`
  have hdw : discPoincareDist z w
      = Real.log (‖1 - conj z * w‖ + ‖z - w‖) - (1 / 2) * Real.log (1 - ‖z‖ ^ 2)
        - (1 / 2) * Real.log (1 - ‖w‖ ^ 2) := by
    rw [discPoincareDist, norm_div]
    have hden1 : (0 : ℝ) < 1 - ‖z - w‖ / ‖1 - conj z * w‖ := by
      rw [sub_pos, div_lt_one hA0]
      exact hBA
    have hsub : ‖1 - conj z * w‖ - ‖z - w‖ ≠ 0 := (sub_pos.2 hBA).ne'
    have e1 : (1 + ‖z - w‖ / ‖1 - conj z * w‖) / (1 - ‖z - w‖ / ‖1 - conj z * w‖)
        = (‖1 - conj z * w‖ + ‖z - w‖) / (‖1 - conj z * w‖ - ‖z - w‖) := by
      have hnum : 1 + ‖z - w‖ / ‖1 - conj z * w‖
          = (‖1 - conj z * w‖ + ‖z - w‖) / ‖1 - conj z * w‖ := by
        rw [add_div, div_self hA0.ne']
      have hden : 1 - ‖z - w‖ / ‖1 - conj z * w‖
          = (‖1 - conj z * w‖ - ‖z - w‖) / ‖1 - conj z * w‖ := by
        rw [sub_div, div_self hA0.ne']
      rw [hnum, hden, div_div_div_cancel_right₀ hA0.ne']
    have e2 : (‖1 - conj z * w‖ + ‖z - w‖) / (‖1 - conj z * w‖ - ‖z - w‖)
        = (‖1 - conj z * w‖ + ‖z - w‖) ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
      rw [div_eq_div_iff hsub (mul_pos hr2 hq2).ne', ← hAB]
      ring
    rw [e1, e2, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul hr2.ne' hq2.ne']
    push_cast
    ring
  -- `log((A + B)/(1 + |z|)) ≤ B - |z|`
  have hlog : Real.log (‖1 - conj z * w‖ + ‖z - w‖) - Real.log (1 + ‖z‖)
      ≤ ‖z - w‖ - ‖z‖ := by
    have h1 : Real.log ((‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖))
        ≤ (‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : (‖1 - conj z * w‖ + ‖z - w‖) / (1 + ‖z‖) - 1 ≤ ‖z - w‖ - ‖z‖ := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [norm_one_sub_conj_mul_sub_one_le (w := w) hz]
    linarith
  -- `-½ log(1 - |w|²) ≤ |w|²/(1 - |w|²)`
  have hlogq : -((1 / 2) * Real.log (1 - ‖w‖ ^ 2)) ≤ ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
    have h1 : Real.log (1 / (1 - ‖w‖ ^ 2)) ≤ 1 / (1 - ‖w‖ ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero hq2.ne', Real.log_one, zero_sub] at h1
    have h2 : 1 / (1 - ‖w‖ ^ 2) - 1 = ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (0 : ℝ) ≤ ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by positivity
    linarith
  rw [hdw, hd0]
  linarith

/-- §36.3 (the pointwise inequality behind Lemma 36.3): `d(z, w) - d(z, 0) ≤ |z - w| - |z| + α(|w|)|w|`
with `α(r) → 0` as `r → 0`.

The sharp constant is `α(t) t = -½ log(1 - t²)` (attained in the limit `|z| → 1` with
`|z - w| = 1`), so any `α` with `α(t) t ≥ -½ log(1 - t²)` works; `α(t) = t/(1 - t²)` is taken here,
since `-log(1 - u) ≤ u/(1 - u)`.  Note `α(t) = t` does **not** work: at `|w| = 0.9` the sharp
constant is `0.8304 > 0.81 = |w|²`.

Proof: `d(z, w) = log(A + B) - ½log(1 - |z|²) - ½log(1 - |w|²)` and
`d(z, 0) = log(1 + |z|) - ½log(1 - |z|²)`, where `A = |1 - z̄w|` and `B = |z - w|`, using
`A² - B² = (1 - |z|²)(1 - |w|²)`.  So the difference is `log((A + B)/(1 + |z|)) - ½log(1 - |w|²)`;
then `log u ≤ u - 1` and `norm_one_sub_conj_mul_sub_one_le` give
`log((A + B)/(1 + |z|)) ≤ B - |z|`. -/
theorem discPoincareDist_sub_le :
    ∃ α : ℝ → ℝ, Tendsto α (𝓝[>] 0) (𝓝 0) ∧ ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
      discPoincareDist z w - discPoincareDist z 0 ≤ ‖z - w‖ - ‖z‖ + α ‖w‖ * ‖w‖ := by
  refine ⟨fun t => t / (1 - t ^ 2), ?_, fun z w hz hw => ?_⟩
  · have hc : ContinuousAt (fun t : ℝ => t / (1 - t ^ 2)) 0 := by
      refine ContinuousAt.div continuousAt_id (by fun_prop) ?_
      norm_num
    have h1 : Tendsto (fun t : ℝ => t / (1 - t ^ 2)) (𝓝 0) (𝓝 0) := by
      have h := hc.tendsto
      norm_num at h
      exact h
    exact h1.mono_left nhdsWithin_le_nhds
  · have h := discPoincareDist_sub_le_explicit hz hw
    have hfin : ‖w‖ / (1 - ‖w‖ ^ 2) * ‖w‖ = ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2) := by
      field_simp
    rw [hfin]
    exact h

/-- The analytic input behind `artanh_sub_self_monotoneOn`: `x ↦ log(1 + x) - log(1 - x) - 2x` is
monotone on `(-1, 1)`, its derivative being `1/(1 + x) + 1/(1 - x) - 2 = 2x²/(1 - x²) ≥ 0`.

Mathlib develops `Real.artanh` purely order-theoretically and gives it no derivative, so the
logarithmic form is the one differentiated here; `Real.artanh_eq_half_log` transports the result. -/
theorem monotoneOn_log_sub_log_sub_two_mul :
    MonotoneOn (fun x : ℝ => Real.log (1 + x) - Real.log (1 - x) - 2 * x)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hderiv : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
        (1 / (1 + x) - -1 / (1 - x) - 2) x := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    have d1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).log h1.ne'
    have d2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).log h2.ne'
    have d3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    exact (d1.sub d2).sub d3
  refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
    (fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt) ?_ ?_
  · rw [isOpen_Ioo.interior_eq]
    exact fun x hx => ((hderiv x hx).differentiableAt).differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    rw [(hderiv x hx).deriv]
    have key : 1 / (1 + x) - -1 / (1 - x) - 2 = 2 * x ^ 2 / ((1 + x) * (1 - x)) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by positivity) (mul_pos h1 h2).le

/-- `x ↦ artanh x - x` is monotone on `(-1, 1)`: in the language of §36.3, `|z| ↦ d(z, 0) - |z|`
is increasing.  This is the second ingredient of Lemma 36.3, the first being
`discPoincareDist_sub_le_explicit`. -/
theorem artanh_sub_self_monotoneOn :
    MonotoneOn (fun x : ℝ => Real.artanh x - x) (Set.Ioo (-1 : ℝ) 1) := by
  have key : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Real.artanh x - x = 1 / 2 * (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, Real.log_div h1.ne' h2.ne']
    ring
  intro s hs t ht hst
  have h : Real.log (1 + s) - Real.log (1 - s) - 2 * s
      ≤ Real.log (1 + t) - Real.log (1 - t) - 2 * t :=
    monotoneOn_log_sub_log_sub_two_mul hs ht hst
  show Real.artanh s - s ≤ Real.artanh t - t
  rw [key s hs, key t ht]
  linarith

/-- `t ↦ t²/(1 - t²)` is monotone on `[0, 1)` — the `α(t) t` of `discPoincareDist_sub_le`. -/
theorem sq_div_one_sub_sq_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    s ^ 2 / (1 - s ^ 2) ≤ t ^ 2 / (1 - t ^ 2) := by
  have ht0 : (0 : ℝ) ≤ t := le_trans hs hst
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hds : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hdt : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hds hdt]
  nlinarith [mul_nonneg (sub_nonneg.2 hst) (by linarith : (0 : ℝ) ≤ t + s)]

/-- If `‖μ‖ ≤ c` a.e. on `ℍ` then `‖μ‖_∞ ≤ ofReal c` in `ℝ≥0∞`. -/
theorem essSup_nnnorm_le_ofReal {μ : ℂ → ℂ} {c : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ c) :
    essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≤ ENNReal.ofReal c := by
  refine essSup_le_of_ae_le (ENNReal.ofReal c) ?_
  filter_upwards [h] with z hz
  rw [coe_nnnorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hz

/-- An a.e. bound makes `‖μ‖_∞` finite, so `beltramiNormH μ` is a faithful `.toReal` and not the
junk value `0` (the `⊤` hazard recorded for `eq35_8`). -/
theorem essSup_nnnorm_ne_top_of_ae_bound {μ : ℂ → ℂ} {c : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ c) :
    essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (essSup_nnnorm_le_ofReal h)

/-- The real form: an a.e. bound by `c ≥ 0` bounds `beltramiNormH`. -/
theorem beltramiNormH_le_of_ae_bound {μ : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ c) : beltramiNormH μ ≤ c := by
  have h2 := (ENNReal.toReal_le_toReal (essSup_nnnorm_ne_top_of_ae_bound h)
    ENNReal.ofReal_ne_top).2 (essSup_nnnorm_le_ofReal h)
  rwa [ENNReal.toReal_ofReal hc] at h2

/-- `τ(ν, 0) = ‖artanh |ν|‖_∞`, by `discPoincareDist_zero` a.e. on `ℍ`. -/
theorem beltramiPoincareDist_zero_eq (ν : BeltramiH) :
    beltramiPoincareDist ν.1 0
      = (essSup (fun z => ENNReal.ofReal (Real.artanh ‖ν.1 z‖))
          (volume.restrict upperHalf)).toReal := by
  obtain ⟨k, hk0, hk1, hbd⟩ := beltramiH_ae_bound ν
  rw [beltramiPoincareDist]
  congr 1
  refine essSup_congr_ae ?_
  filter_upwards [hbd] with z hz
  simp only [Pi.zero_apply, discPoincareDist_zero (lt_of_le_of_lt hz hk1)]

/-- `‖ν z‖ ≤ tanh τ(ν, 0)` a.e.: the essential supremum of `artanh |ν|` is finite, hence dominates
`artanh ‖ν z‖` a.e., and `artanh` is strictly monotone with `artanh (tanh τ) = τ`. -/
theorem ae_norm_le_tanh_essSup_artanh (ν : BeltramiH) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν.1 z‖ ≤ Real.tanh
      (essSup (fun z => ENNReal.ofReal (Real.artanh ‖ν.1 z‖))
        (volume.restrict upperHalf)).toReal := by
  obtain ⟨k, hk0, hk1, hbd⟩ := beltramiH_ae_bound ν
  have hTne : essSup (fun z => ENNReal.ofReal (Real.artanh ‖ν.1 z‖))
      (volume.restrict upperHalf) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (essSup_le_of_ae_le (ENNReal.ofReal (Real.artanh k)) ?_)
    filter_upwards [hbd] with z hz
    exact ENNReal.ofReal_le_ofReal
      (Real.artanh_le_artanh (by linarith [norm_nonneg (ν.1 z)]) hk1 hz)
  filter_upwards [hbd,
    ENNReal.ae_le_essSup (fun z => ENNReal.ofReal (Real.artanh ‖ν.1 z‖))] with z hz hle
  have hlt : ‖ν.1 z‖ < 1 := lt_of_le_of_lt hz hk1
  have h1 : Real.artanh ‖ν.1 z‖
      ≤ (essSup (fun z => ENNReal.ofReal (Real.artanh ‖ν.1 z‖))
          (volume.restrict upperHalf)).toReal := by
    rw [← ENNReal.toReal_ofReal (Real.artanh_nonneg (norm_nonneg (ν.1 z)))]
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hTne).2 hle
  refine (Real.artanh_le_artanh_iff ⟨by linarith [norm_nonneg (ν.1 z)], hlt⟩
    ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).1 ?_
  rw [Real.artanh_tanh]
  exact h1

/-- If `‖μ‖ ≤ tanh c` a.e. on `ℍ` with `0 ≤ c`, then `artanh ‖μ‖_∞ ≤ c`. -/
theorem artanh_beltramiNormH_le_of_ae_tanh {μ : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ z‖ ≤ Real.tanh c) :
    Real.artanh (beltramiNormH μ) ≤ c := by
  have htn : 0 ≤ Real.tanh c := by
    by_contra hneg
    rw [not_le] at hneg
    have h0 := Real.artanh_neg ⟨Real.neg_one_lt_tanh c, hneg⟩
    rw [Real.artanh_tanh] at h0
    linarith
  calc Real.artanh (beltramiNormH μ)
      ≤ Real.artanh (Real.tanh c) :=
        Real.artanh_le_artanh (by linarith [beltramiNormH_nonneg μ]) (Real.tanh_lt_one c)
          (beltramiNormH_le_of_ae_bound htn h)
    _ = c := Real.artanh_tanh c

/-- **`artanh ‖ν‖_∞ ≤ τ(ν, 0)`** — the step that makes Lemma 36.3 come out with `- ‖ν‖_∞` on the
right.  Note that the reverse inequality also holds (`artanh` is monotone and continuous, so it
commutes with the essential supremum), but only this direction is needed. -/
theorem artanh_beltramiNormH_le (ν : BeltramiH) :
    Real.artanh (beltramiNormH ν.1) ≤ beltramiPoincareDist ν.1 0 := by
  rw [beltramiPoincareDist_zero_eq ν]
  exact artanh_beltramiNormH_le_of_ae_tanh ENNReal.toReal_nonneg
    (ae_norm_le_tanh_essSup_artanh ν)

/-- **Lemma 36.3**: for `ν, π ∈ M(ℍ, G)`, `τ(ν, π) - τ(ν, 0) ≤ ‖ν - π‖_∞ - ‖ν‖_∞ + o(‖π‖_∞)`.

Proof (as in the book): pointwise `d(ν z, π z) - d(ν z, 0) ≤ |ν z - π z| - |ν z| + α(|π z|)|π z|`
(`discPoincareDist_sub_le_explicit`, with `α(t) = t/(1 - t²)`), and `d(ν z, 0) = artanh |ν z|`, so

  `d(ν z, π z) ≤ (artanh |ν z| - |ν z|) + |ν z - π z| + α(|π z|)|π z|`.

Each of the three summands is now bounded a.e. by its value at the relevant essential supremum,
because `t ↦ artanh t - t` (`artanh_sub_self_monotoneOn`) and `t ↦ t²/(1 - t²)`
(`sq_div_one_sub_sq_le`) are increasing on `[0, 1)` — this rearrangement *before* taking the
supremum is what makes the argument work: `essSup` is not additive, and `- ‖ν‖_∞` could not have
been produced from a bound on `d(ν z, π z) - d(ν z, 0)` alone.  Taking `essSup` gives

  `τ(ν, π) ≤ (artanh ‖ν‖_∞ - ‖ν‖_∞) + ‖ν - π‖_∞ + α(‖π‖_∞)‖π‖_∞`,

and `artanh ‖ν‖_∞ ≤ τ(ν, 0)` (`artanh_beltramiNormH_le`) absorbs the leading term. -/
theorem lemma36_3 :
    ∃ β : ℝ → ℝ, Tendsto β (𝓝[>] 0) (𝓝 0) ∧ ∀ ν π' : BeltramiH,
      beltramiPoincareDist ν.1 π'.1 - beltramiPoincareDist ν.1 0 ≤
        beltramiNormH (ν.1 - π'.1) - beltramiNormH ν.1 + β (beltramiNormH π'.1) * beltramiNormH π'.1 := by
  refine ⟨fun t => t / (1 - t ^ 2), ?_, fun ν π' => ?_⟩
  · have hc : ContinuousAt (fun t : ℝ => t / (1 - t ^ 2)) 0 := by
      refine ContinuousAt.div continuousAt_id (by fun_prop) ?_
      norm_num
    have h1 : Tendsto (fun t : ℝ => t / (1 - t ^ 2)) (𝓝 0) (𝓝 0) := by
      have h := hc.tendsto
      norm_num at h
      exact h
    exact h1.mono_left nhdsWithin_le_nhds
  · show beltramiPoincareDist ν.1 π'.1 - beltramiPoincareDist ν.1 0 ≤
      beltramiNormH (ν.1 - π'.1) - beltramiNormH ν.1
        + beltramiNormH π'.1 / (1 - beltramiNormH π'.1 ^ 2) * beltramiNormH π'.1
    obtain ⟨kν, hkν0, hkν1, hbdν⟩ := beltramiH_ae_bound ν
    obtain ⟨kπ, hkπ0, hkπ1, hbdπ⟩ := beltramiH_ae_bound π'
    have hKν1 : beltramiNormH ν.1 < 1 := beltramiNormH_lt_one ν
    have hKπ1 : beltramiNormH π'.1 < 1 := beltramiNormH_lt_one π'
    have hKν0 : 0 ≤ beltramiNormH ν.1 := beltramiNormH_nonneg _
    have hKπ0 : 0 ≤ beltramiNormH π'.1 := beltramiNormH_nonneg _
    have hKd0 : 0 ≤ beltramiNormH (ν.1 - π'.1) := beltramiNormH_nonneg _
    -- the three a.e. bounds by the essential suprema
    have haeν : ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν.1 z‖ ≤ beltramiNormH ν.1 :=
      ae_norm_le_beltramiNormH (beltramiH_essSup_ne_top ν)
    have haeπ : ∀ᵐ z ∂(volume.restrict upperHalf), ‖π'.1 z‖ ≤ beltramiNormH π'.1 :=
      ae_norm_le_beltramiNormH (beltramiH_essSup_ne_top π')
    have haed : ∀ᵐ z ∂(volume.restrict upperHalf),
        ‖(ν.1 - π'.1) z‖ ≤ beltramiNormH (ν.1 - π'.1) := by
      refine ae_norm_le_beltramiNormH (essSup_nnnorm_ne_top_of_ae_bound (c := kν + kπ) ?_)
      filter_upwards [hbdν, hbdπ] with z hzν hzπ
      rw [Pi.sub_apply]
      exact le_trans (norm_sub_le _ _) (add_le_add hzν hzπ)
    -- the bound is non-negative, so it survives the passage to `ENNReal`
    have hq0 : 0 ≤ beltramiNormH π'.1 ^ 2 / (1 - beltramiNormH π'.1 ^ 2) := by
      have hd : (0 : ℝ) < 1 - beltramiNormH π'.1 ^ 2 := by nlinarith
      positivity
    have hmono0 : Real.artanh 0 - 0 ≤ Real.artanh (beltramiNormH ν.1) - beltramiNormH ν.1 :=
      artanh_sub_self_monotoneOn ⟨by norm_num, by norm_num⟩ ⟨by linarith, hKν1⟩ hKν0
    rw [Real.artanh_zero] at hmono0
    have hC0 : 0 ≤ Real.artanh (beltramiNormH ν.1) - beltramiNormH ν.1
        + beltramiNormH (ν.1 - π'.1)
        + beltramiNormH π'.1 ^ 2 / (1 - beltramiNormH π'.1 ^ 2) := by linarith
    -- the pointwise bound, a.e.
    have hbound : ∀ᵐ z ∂(volume.restrict upperHalf),
        discPoincareDist (ν.1 z) (π'.1 z) ≤ Real.artanh (beltramiNormH ν.1) - beltramiNormH ν.1
          + beltramiNormH (ν.1 - π'.1)
          + beltramiNormH π'.1 ^ 2 / (1 - beltramiNormH π'.1 ^ 2) := by
      filter_upwards [hbdν, hbdπ, haeν, haeπ, haed] with z hzν hzπ hKzν hKzπ hKzd
      have hzν1 : ‖ν.1 z‖ < 1 := lt_of_le_of_lt hzν hkν1
      have hzπ1 : ‖π'.1 z‖ < 1 := lt_of_le_of_lt hzπ hkπ1
      have h1 := discPoincareDist_sub_le_explicit hzν1 hzπ1
      rw [discPoincareDist_zero hzν1] at h1
      have h2 : Real.artanh ‖ν.1 z‖ - ‖ν.1 z‖
          ≤ Real.artanh (beltramiNormH ν.1) - beltramiNormH ν.1 :=
        artanh_sub_self_monotoneOn ⟨by linarith [norm_nonneg (ν.1 z)], hzν1⟩
          ⟨by linarith, hKν1⟩ hKzν
      have h3 := sq_div_one_sub_sq_le (norm_nonneg (π'.1 z)) hKzπ hKπ1
      have h4 : ‖ν.1 z - π'.1 z‖ ≤ beltramiNormH (ν.1 - π'.1) := by
        rw [← Pi.sub_apply]
        exact hKzd
      linarith
    -- take the essential supremum
    have hτ : beltramiPoincareDist ν.1 π'.1 ≤ Real.artanh (beltramiNormH ν.1) - beltramiNormH ν.1
        + beltramiNormH (ν.1 - π'.1)
        + beltramiNormH π'.1 ^ 2 / (1 - beltramiNormH π'.1 ^ 2) := by
      rw [beltramiPoincareDist]
      refine ENNReal.toReal_le_of_le_ofReal hC0 (essSup_le_of_ae_le _ ?_)
      filter_upwards [hbound] with z hz
      exact ENNReal.ofReal_le_ofReal hz
    have hτ0 := artanh_beltramiNormH_le ν
    have hbq : beltramiNormH π'.1 / (1 - beltramiNormH π'.1 ^ 2) * beltramiNormH π'.1
        = beltramiNormH π'.1 ^ 2 / (1 - beltramiNormH π'.1 ^ 2) := by
      rw [div_mul_eq_mul_div, ← pow_two]
    rw [hbq]
    linarith

/-! ## BLOCK B — install just before the docstring of `hamilton_contradiction` (batch B)

Uses from S36 §36.3: `IsTrivialBeltrami`, `discPoincareDist`, `beltramiPoincareDist`,
`artanh_beltramiNormH_le`, `ae_norm_le_beltramiNormH`, `beltramiH_essSup_ne_top`, `beltramiNormH_lt_one`;
from S35: `h35_pt_hyp`; from BLOCK A: `h36p_kernel_cond`. -/

/-! ### B.1 Stubs of provers P2, P1, P4 -/

/-- An element of `integrableAutomorphicQD Γ F` is integrable on `F` (`F ⊆ ℍ` measurable). -/
theorem h36p_b_integrableOn_A {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) : IntegrableOn φ F := by
  refine ⟨(hφ.1.continuousOn.mono hFH).aestronglyMeasurable hFm, ?_⟩
  have h1 : (∫⁻ z in F, ‖φ z‖ₑ) = phiArea φ F := by
    unfold phiArea
    simp_rw [ofReal_norm]
  show (∫⁻ z in F, ‖φ z‖ₑ) < ⊤
  rw [h1]
  exact hφ.2.1

/-- `integrableAutomorphicQD Γ F` is closed under addition (`F ⊆ ℍ` measurable). -/
theorem h36p_b_A_add {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf) {φ ψ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hψ : ψ ∈ integrableAutomorphicQD Γ F) :
    φ + ψ ∈ integrableAutomorphicQD Γ F := by
  refine ⟨hφ.1.add hψ.1, ?_, fun γ hγ z hz => ?_⟩
  · have hle : phiArea (φ + ψ) F ≤ phiArea φ F + phiArea ψ F := by
      unfold phiArea
      rw [← lintegral_add_left' (((hφ.1.continuousOn.mono hFH).aestronglyMeasurable
        hFm).aemeasurable.norm.ennreal_ofReal)]
      refine lintegral_mono fun z => ?_
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hφ.2.1, hψ.2.1⟩)
  · simp only [Pi.add_apply]
    rw [add_div, hφ.2.2 γ hγ z hz, hψ.2.2 γ hγ z hz]

/-- `integrableAutomorphicQD Γ F` is closed under scalar multiplication. -/
theorem h36p_b_A_smul {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (a : ℂ) :
    a • φ ∈ integrableAutomorphicQD Γ F := by
  refine ⟨hφ.1.const_smul a, ?_, fun γ hγ z hz => ?_⟩
  · have : phiArea (a • φ) F = ENNReal.ofReal ‖a‖ * phiArea φ F := by
      unfold phiArea
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun z => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    rw [this]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.2.1
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, hφ.2.2 γ hγ z hz]

/-- `0 ∈ integrableAutomorphicQD Γ F`. -/
theorem h36p_b_A_zero {F : Set ℂ} : (0 : ℂ → ℂ) ∈ integrableAutomorphicQD Γ F :=
  ⟨differentiableOn_const 0, by simp [phiArea], fun _ _ _ _ => by simp⟩

/-- **The pairing is bounded by `hamiltonNorm`**: `|∬_F μ φ| ≤ ‖P_μ‖ ∬_F |φ|` for `φ ∈ A(Γ, F)` (normalize
`φ` to area `1`; if `∬_F |φ| = 0` both sides vanish, since `|μ| ≤ k` a.e.). -/
theorem h36p_b_pairing_le {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) (μ : BeltramiGamma Γ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    ‖beltramiPairing F μ.1.1 φ‖ ≤ hamiltonNorm Γ F μ.1.1 * ∫ z in F, ‖φ z‖ := by
  obtain ⟨⟨k, hk0, -, -, hμb⟩, -⟩ := μ.1.2
  rw [Measure.restrict_univ] at hμb
  have hμF : ∀ᵐ z ∂(volume.restrict F), ‖μ.1.1 z‖ ≤ k := ae_restrict_of_ae hμb
  have hk : ∀ ψ ∈ integrableAutomorphicQD Γ F,
      ‖beltramiPairing F μ.1.1 ψ‖ ≤ k * ∫ z in F, ‖ψ z‖ := by
    intro ψ hψ
    unfold beltramiPairing
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((h36p_b_integrableOn_A hFH hFm hψ).norm.const_mul k) ?_
    filter_upwards [hμF] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have harea : ∀ ψ ∈ integrableAutomorphicQD Γ F,
      ENNReal.ofReal (∫ z in F, ‖ψ z‖) = phiArea ψ F := fun ψ hψ =>
    ofReal_integral_eq_lintegral_ofReal (h36p_b_integrableOn_A hFH hFm hψ).norm
      (ae_of_all _ fun _ => norm_nonneg _)
  have hk1 : ∀ ψ : ℂ → ℂ, ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1 →
      ‖beltramiPairing F μ.1.1 ψ‖ ≤ k := by
    intro ψ hψ
    have h1 : ∫ z in F, ‖ψ z‖ = 1 := by
      have := harea ψ hψ.1
      rw [hψ.2, ← ENNReal.ofReal_one] at this
      exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => norm_nonneg _) zero_le_one).1 this
    have := hk ψ hψ.1
    rwa [h1, mul_one] at this
  have hbdd : BddAbove (range fun ψ : ℂ → ℂ =>
      ⨆ (_ : ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1), ‖beltramiPairing F μ.1.1 ψ‖) := by
    refine ⟨k, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact Real.iSup_le (fun hψ => hk1 ψ hψ) hk0
  have hle : ∀ ψ : ℂ → ℂ, ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1 →
      ‖beltramiPairing F μ.1.1 ψ‖ ≤ hamiltonNorm Γ F μ.1.1 := by
    intro ψ hψ
    calc ‖beltramiPairing F μ.1.1 ψ‖
        = ⨆ (_ : ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1), ‖beltramiPairing F μ.1.1 ψ‖ :=
          (ciSup_pos (f := fun _ => ‖beltramiPairing F μ.1.1 ψ‖) hψ).symm
      _ ≤ _ := le_ciSup hbdd ψ
  have ha0 : 0 ≤ ∫ z in F, ‖φ z‖ := integral_nonneg fun _ => norm_nonneg _
  rcases ha0.lt_or_eq with hapos | ha0'
  · set a := ∫ z in F, ‖φ z‖ with ha
    set ψ : ℂ → ℂ := fun z => (a : ℂ)⁻¹ * φ z with hψdef
    have hψA : ψ ∈ integrableAutomorphicQD Γ F := h36p_b_A_smul hφ (a : ℂ)⁻¹
    have hψ1 : phiArea ψ F = 1 := by
      rw [← harea ψ hψA]
      have e : ∫ z in F, ‖ψ z‖ = a⁻¹ * a := by
        simp only [hψdef, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha0]
        rw [integral_const_mul]
      rw [e, inv_mul_cancel₀ hapos.ne', ENNReal.ofReal_one]
    have h1 := hle ψ ⟨hψA, hψ1⟩
    have e : beltramiPairing F μ.1.1 ψ = (a : ℂ)⁻¹ * beltramiPairing F μ.1.1 φ := by
      unfold beltramiPairing
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hψdef]
      ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha0, inv_mul_le_iff₀ hapos] at h1
    linarith
  · have h := hk φ hφ
    rw [← ha0', mul_zero] at h ⊢
    exact h

/-- **[P2, stub] (A_Γ) Duality on `F`.**  There is a bounded measurable `ν₀` on `F` with
`|ν₀| ≤ ‖P_μ‖ = hamiltonNorm Γ F μ` a.e. on `F` and `∬_F ν₀ φ = ∬_F μ φ` for all `φ ∈ A(Γ, F)`.  Route: the
functional `𝟙_F φ ↦ ∬_F μ φ` on the subspace `{𝟙_F φ}` of `L¹(F)` has norm `≤ hamiltonNorm` (normalize
`∬_F |φ| = 1`; `φ = 0` a.e. on `F` gives `0`); Hahn–Banach; `L¹(F)* = L∞(F)` (`h35a_L1_dual_repr` is for a finite
measure: pass to the finite measure `ρ · volume|_F`, `ρ = (1 + |z|²)⁻²`, and back). -/
theorem h36p_duality_F {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ) :
    ∃ ν₀ : ℂ → ℂ, AEStronglyMeasurable ν₀ (volume.restrict F) ∧
      (∀ᵐ z ∂(volume.restrict F), ‖ν₀ z‖ ≤ hamiltonNorm Γ F μ.1.1) ∧
      ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F ν₀ φ = beltramiPairing F μ.1.1 φ := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  obtain ⟨⟨k, -, -, hμm, hμb⟩, -⟩ := μ.1.2
  rw [Measure.restrict_univ] at hμm hμb
  have hH0 : 0 ≤ hamiltonNorm Γ F μ.1.1 :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- the finite measure `P = ρ · volume|_F`, `ρ = (1 + |z|)⁻³`
  set ρ : ℂ → ℝ := fun z => ((1 + ‖z‖) ^ 3)⁻¹ with hρdef
  have hρpos : ∀ z, 0 < ρ z := fun z => by simp only [hρdef]; positivity
  have hρm : Measurable ρ := by simp only [hρdef]; fun_prop
  set P : Measure ℂ := (volume.restrict F).withDensity (fun z => ENNReal.ofReal (ρ z)) with hPdef
  have hfin : IsFiniteMeasure P :=
    isFiniteMeasure_withDensity_ofReal (b36_p_profile_integrable.integrableOn (s := F)).2
  have hPF : P ≪ volume.restrict F := withDensity_absolutelyContinuous _ _
  have hFP : volume.restrict F ≪ P := withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (hρpos z)).ne')
  have hPv : P ≪ volume := hPF.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hPint : ∀ g : ℂ → ℂ, ∫ z, g z ∂P = ∫ z in F, (ρ z : ℂ) * g z := by
    intro g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hPintR : ∀ g : ℂ → ℝ, ∫ z, g z ∂P = ∫ z in F, ρ z * g z := by
    intro g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, smul_eq_mul]
  have hPi : ∀ g : ℂ → ℂ, Integrable g P ↔ Integrable (fun z => (ρ z : ℂ) * g z) (volume.restrict F) := by
    intro g
    rw [hPdef, integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integrable_congr (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hdiv : ∀ φ : ℂ → ℂ, ∀ z, (ρ z : ℂ) * (φ z / ρ z) = φ z := fun φ z => by
    have : (ρ z : ℂ) ≠ 0 := by exact_mod_cast (hρpos z).ne'
    field_simp
  have hnorm : ∀ φ : ℂ → ℂ, ∀ z, ρ z * ‖φ z / ρ z‖ = ‖φ z‖ := fun φ z => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hρpos z).le]
    field_simp [(hρpos z).ne']
  have hAi : ∀ φ ∈ integrableAutomorphicQD Γ F, Integrable (fun z => φ z / ρ z) P := by
    intro φ hφ
    rw [hPi]
    exact (h36p_b_integrableOn_A hFH hFm hφ).congr (ae_of_all _ fun z => (hdiv φ z).symm)
  -- the functional `G ↦ ∫ μ G dP` on `L¹(P)`, restricted to the image `W` of `A(Γ, F)`
  obtain ⟨ℓ, hℓ⟩ := h35a_exists_mul_functional (hμm.mono_ac hPv) (hPv.ae_le hμb)
  set S : Set (Lp ℂ 1 P) :=
    {G | ∃ φ ∈ integrableAutomorphicQD Γ F, (G : ℂ → ℂ) =ᵐ[P] fun z => φ z / ρ z} with hSdef
  set W : Submodule ℂ (Lp ℂ 1 P) := Submodule.span ℂ S with hWdef
  have hW : ∀ G ∈ W, ∃ φ ∈ integrableAutomorphicQD Γ F, (G : ℂ → ℂ) =ᵐ[P] fun z => φ z / ρ z := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, h36p_b_A_zero, ?_⟩
      filter_upwards [Lp.coeFn_zero ℂ 1 P] with z hz
      rw [hz]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨φ, hφ, h1⟩ := hx
      obtain ⟨ψ, hψ, h2⟩ := hy
      refine ⟨φ + ψ, h36p_b_A_add hFm hFH hφ hψ, ?_⟩
      filter_upwards [Lp.coeFn_add x y, h1, h2] with z e0 e1 e2
      rw [e0, Pi.add_apply, e1, e2, Pi.add_apply, add_div]
    | smul a x _ hx =>
      obtain ⟨φ, hφ, h1⟩ := hx
      refine ⟨a • φ, h36p_b_A_smul hφ a, ?_⟩
      filter_upwards [Lp.coeFn_smul a x, h1] with z e0 e1
      rw [e0, Pi.smul_apply, e1, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  have hbd : ‖ℓ.comp W.subtypeL‖ ≤ hamiltonNorm Γ F μ.1.1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ hH0 (fun G => ?_)
    obtain ⟨φ, hφ, hGφ⟩ := hW G G.2
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hℓ, ← Submodule.norm_coe,
      L1.norm_eq_integral_norm]
    have e1 : ∫ z, μ.1.1 z * ((G : Lp ℂ 1 P) : ℂ → ℂ) z ∂P = beltramiPairing F μ.1.1 φ := by
      have e : ∫ z, μ.1.1 z * ((G : Lp ℂ 1 P) : ℂ → ℂ) z ∂P = ∫ z, μ.1.1 z * (φ z / ρ z) ∂P :=
        integral_congr_ae (by filter_upwards [hGφ] with z hz; rw [hz])
      rw [e, hPint]
      unfold beltramiPairing
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only
      rw [mul_left_comm, hdiv]
    have e2 : ∫ z, ‖((G : Lp ℂ 1 P) : ℂ → ℂ) z‖ ∂P = ∫ z in F, ‖φ z‖ := by
      have e : ∫ z, ‖((G : Lp ℂ 1 P) : ℂ → ℂ) z‖ ∂P = ∫ z, ‖φ z / ρ z‖ ∂P :=
        integral_congr_ae (by filter_upwards [hGφ] with z hz; rw [hz])
      rw [e, hPintR]
      exact integral_congr_ae (ae_of_all _ fun z => hnorm φ z)
    rw [e1, e2]
    exact h36p_b_pairing_le hFH hFm μ hφ
  -- Hahn–Banach, then `L¹(P)* = L∞(P)`
  obtain ⟨L, hLext, hLnorm⟩ := exists_extension_norm_eq W (ℓ.comp W.subtypeL)
  obtain ⟨ν, hνm, hνb, hνrep⟩ := h35a_L1_dual_repr L
  refine ⟨ν, hνm.mono_ac hFP, hFP.ae_le ?_, fun φ hφ => ?_⟩
  · filter_upwards [hνb] with z hz
    exact hz.trans (hLnorm ▸ hbd)
  · have hφi := hAi φ hφ
    have hmem : hφi.toL1 (fun z => φ z / ρ z) ∈ W := Submodule.subset_span ⟨φ, hφ, hφi.coeFn_toL1⟩
    have h1 := hLext ⟨hφi.toL1 (fun z => φ z / ρ z), hmem⟩
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hℓ, hνrep _ hφi] at h1
    have e1 : ∫ z, μ.1.1 z * (hφi.toL1 (fun z => φ z / ρ z) : ℂ → ℂ) z ∂P =
        ∫ z, μ.1.1 z * (φ z / ρ z) ∂P :=
      integral_congr_ae (by filter_upwards [hφi.coeFn_toL1] with z hz; rw [hz])
    rw [e1, hPint, hPint] at h1
    unfold beltramiPairing
    have e2 : ∀ κ : ℂ → ℂ, ∫ z in F, (ρ z : ℂ) * (κ z * (φ z / ρ z)) = ∫ z in F, κ z * φ z := fun κ =>
      integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [mul_left_comm, hdiv])
    rw [e2, e2] at h1
    exact h1

/-- Composition on `ℍ`: `h36p_m (A B) z = h36p_m A (h36p_m B z)`. -/
theorem h36p_a_m_mul (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_m (A * B) z = h36p_m A (h36p_m B z) := by
  have e1 := h36p_m_coe B ⟨z, hz⟩
  have e2 := h36p_m_coe (A * B) ⟨z, hz⟩
  simp only at e1 e2
  rw [e2, e1, h36p_m_coe A, mul_smul]

/-- `h36p_m 1` is the identity. -/
theorem h36p_a_m_one (z : ℂ) : h36p_m 1 z = z := by
  simp [h36p_m]

/-- The factor `J(γ, z) = j²/conj(j²)`, `j = cz + d`, of `IsGammaCompatible`. -/
def h36p_a_J (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)

/-- `|J(γ, z)| ≤ 1` (it is `1` off the pole of `j`, and `0/0 = 0` there). -/
theorem h36p_a_J_norm_le (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ‖h36p_a_J γ z‖ ≤ 1 := by
  unfold h36p_a_J
  rw [norm_div, Complex.norm_conj]
  exact div_self_le_one _

/-- `J(-γ, z) = J(γ, z)`. -/
theorem h36p_a_J_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : h36p_a_J (-γ) z = h36p_a_J γ z := by
  unfold h36p_a_J
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
  rw [show (-(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ)) ^ 2 = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 by ring]

/-- `J(1, z) = 1`. -/
theorem h36p_a_J_one (z : ℂ) : h36p_a_J 1 z = 1 := by
  simp [h36p_a_J]

/-- The cocycle `J(AB, z) = J(A, Bz) J(B, z)` on `ℍ` (from `j(AB, z) = j(A, Bz) j(B, z)`). -/
theorem h36p_a_J_mul (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_a_J (A * B) z = h36p_a_J A (h36p_m B z) * h36p_a_J B z := by
  have hden := k24_d_den_ne_zero (b33_d_det B) (ne_of_gt (show 0 < z.im from hz))
  have hj : (((A * B : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
      (((A * B : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ) =
      ((A 1 0 : ℂ) * h36p_m B z + A 1 1) * ((B 1 0 : ℂ) * z + B 1 1) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h36p_m]
    push_cast
    field_simp
    ring
  unfold h36p_a_J
  rw [hj, mul_pow, map_mul, div_mul_div_comm]

/-- `J(γ, ·)` is measurable. -/
theorem h36p_a_J_measurable (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Measurable (h36p_a_J γ) := by
  have h1 : Measurable fun z : ℂ => ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 := by fun_prop
  exact h1.div (Complex.continuous_conj.measurable.comp h1)

/-- **[P1, stub] Γ-equivariant extension from `F`.**  A bounded measurable `ν₀` on `F` (`|ν₀| ≤ c` a.e.) is
a.e. on `F` the restriction of a measurable `Γ`-compatible `ν` on `ℍ`, zero on the closed lower half-plane,
with `|ν| ≤ c` a.e. on `ℍ`.  Route: enumerate `Γ` (countable), let `γ_z` be the first `γ` with `γz ∈ F`
(covering clause) and `ν(z) = ν₀(γ_z z) j(γ_z, z)²/conj(j(γ_z, z)²)` (measurable version of `ν₀`); `h36p_ae_unique`
makes `γ_z` unique up to sign a.e., which gives the compatibility (cocycle of `j`) and `ν = ν₀` a.e. on `F`. -/
theorem h36p_extend (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {ν₀ : ℂ → ℂ} {c : ℝ}
    (hc : 0 ≤ c) (hν₀m : AEStronglyMeasurable ν₀ (volume.restrict F))
    (hν₀ : ∀ᵐ z ∂(volume.restrict F), ‖ν₀ z‖ ≤ c) :
    ∃ ν : ℂ → ℂ, AEStronglyMeasurable ν volume ∧ (∀ z : ℂ, z.im ≤ 0 → ν z = 0) ∧
      IsGammaCompatible Γ ν ∧ (∀ᵐ z ∂(volume.restrict upperHalf), ‖ν z‖ ≤ c) ∧
      ν =ᵐ[volume.restrict F] ν₀ := by
  classical
  have hF' := hF
  obtain ⟨hFH, hFm, hcov, -, -⟩ := hF
  -- a measurable version of `ν₀`, clipped to be bounded by `c` everywhere
  set ν₁ : ℂ → ℂ := hν₀m.mk ν₀ with hν₁
  have hν₁m : Measurable ν₁ := hν₀m.stronglyMeasurable_mk.measurable
  set ν₂ : ℂ → ℂ := fun w => if ‖ν₁ w‖ ≤ c then ν₁ w else 0 with hν₂
  have hν₂m : Measurable ν₂ :=
    Measurable.ite (measurableSet_le hν₁m.norm measurable_const) hν₁m measurable_const
  have hν₂c : ∀ w, ‖ν₂ w‖ ≤ c := by
    intro w
    simp only [hν₂]
    split_ifs with h
    · exact h
    · rw [norm_zero]
      exact hc
  have hν₂F : ν₂ =ᵐ[volume.restrict F] ν₀ := by
    filter_upwards [hν₀m.ae_eq_mk, hν₀] with w h1 h2
    have h3 : ‖ν₁ w‖ ≤ c := by
      rw [hν₁, ← h1]
      exact h2
    simp only [hν₂, h3, ↓reduceIte]
    exact h1.symm
  -- enumerate `Γ`; `γ_x` is the first `e n` moving `x ∈ ℍ` into `F`
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  have hex : ∀ x : ℂ, ∃ n : ℕ, x ∈ upperHalf → h36p_m (e n).1 x ∈ F := by
    intro x
    by_cases hx : x ∈ upperHalf
    · obtain ⟨γ, hγ, hγF⟩ := hcov ⟨x, hx⟩
      obtain ⟨n, hn⟩ := he ⟨γ, hγ⟩
      refine ⟨n, fun _ => ?_⟩
      have e1 := h36p_m_coe γ ⟨x, hx⟩
      simp only at e1
      rw [hn, e1]
      exact hγF
    · exact ⟨0, fun h => absurd h hx⟩
  set f : ℕ → ℂ → ℂ := fun n x => ν₂ (h36p_m (e n).1 x) * h36p_a_J (e n).1 x with hf
  set ν : ℂ → ℂ := fun x => if x ∈ upperHalf then f (Nat.find (hex x)) x else 0 with hν
  have hνm : Measurable ν := by
    refine Measurable.ite isOpen_upperHalf.measurableSet ?_ measurable_const
    refine Measurable.find (fun n => ?_) (fun n => ?_) hex
    · exact (hν₂m.comp (h36p_m_measurable _)).mul (h36p_a_J_measurable _)
    · have hset : {x : ℂ | x ∈ upperHalf → h36p_m (e n).1 x ∈ F} =
          upperHalfᶜ ∪ h36p_m (e n).1 ⁻¹' F := by
        ext x
        constructor
        · intro h
          have h' : x ∈ upperHalf → h36p_m (e n).1 x ∈ F := h
          by_cases hx : x ∈ upperHalf
          · exact Or.inr (h' hx)
          · exact Or.inl hx
        · rintro (h | h) hx
          · exact absurd hx h
          · exact h
      rw [hset]
      exact isOpen_upperHalf.measurableSet.compl.union (h36p_m_measurable _ hFm)
  -- the value of `ν` on `ℍ` through its chosen representative
  have hval : ∀ x ∈ upperHalf, ∃ γ ∈ Γ, h36p_m γ x ∈ F ∧ ν x = ν₂ (h36p_m γ x) * h36p_a_J γ x := by
    intro x hx
    refine ⟨(e (Nat.find (hex x))).1, (e _).2, Nat.find_spec (hex x) hx, ?_⟩
    simp only [hν, hx, ↓reduceIte, hf]
  -- a.e., any representative gives the value (`h36p_ae_unique`: representatives agree up to sign)
  have hindep : ∀ᵐ x ∂(volume.restrict upperHalf), x ∈ upperHalf → ∀ γ ∈ Γ, h36p_m γ x ∈ F →
      ν x = ν₂ (h36p_m γ x) * h36p_a_J γ x := by
    filter_upwards [h36p_ae_unique hΓ hF'] with x hu hx γ hγ hγF
    obtain ⟨γ', hγ', hγ'F, hνx⟩ := hval x hx
    rw [hνx]
    rcases hu γ' hγ' γ hγ hγ'F hγF with h | h
    · rw [h]
    · rw [h, h36p_a_m_neg, h36p_a_J_neg]
  refine ⟨ν, hνm.aestronglyMeasurable, fun z hz => ?_, fun γ hγ => ?_, ?_, ?_⟩
  · have hz' : z ∉ upperHalf := fun h => absurd hz (not_le.2 h)
    simp only [hν, hz', ↓reduceIte]
  · filter_upwards [hindep, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz1 hz
    show ν z = ν (h36p_m γ z) * h36p_a_J γ z
    obtain ⟨γ', hγ', hγ'F, hνw⟩ := hval _ (h36p_m_mem γ hz)
    have hmul : h36p_m (γ' * γ) z = h36p_m γ' (h36p_m γ z) := h36p_a_m_mul γ' γ hz
    rw [hz1 hz (γ' * γ) (Γ.mul_mem hγ' hγ) (by rw [hmul]; exact hγ'F), hνw, hmul,
      h36p_a_J_mul γ' γ hz, mul_assoc]
  · refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ upperHalf
    · obtain ⟨γ, -, -, hνz⟩ := hval z hz
      rw [hνz, norm_mul]
      calc ‖ν₂ (h36p_m γ z)‖ * ‖h36p_a_J γ z‖ ≤ c * 1 :=
            mul_le_mul (hν₂c _) (h36p_a_J_norm_le γ z) (norm_nonneg _) hc
        _ = c := mul_one c
    · simp only [hν, hz, ↓reduceIte, norm_zero]
      exact hc
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH hindep, hν₂F, ae_restrict_mem hFm]
      with z hz1 hz2 hzF
    rw [hz1 (hFH hzF) 1 Γ.one_mem (by rw [h36p_a_m_one]; exact hzF), h36p_a_m_one, h36p_a_J_one,
      mul_one, hz2]

/-- Two Möbius maps with nonzero determinants which agree at three distinct points off both poles agree
everywhere as functions `ℂ → ℂ` (the junk value `0` at the common pole included): the quadratic
`(A w + B)(C' w + D') - (A' w + B')(C w + D)` has three roots, so it vanishes identically. -/
theorem h36p_d_mob_ext {A B C D A' B' C' D' : ℂ} (h : A * D - B * C ≠ 0) (h' : A' * D' - B' * C' ≠ 0)
    {w₁ w₂ w₃ : ℂ} (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (hp : ∀ w ∈ ({w₁, w₂, w₃} : Set ℂ), C * w + D ≠ 0 ∧ C' * w + D' ≠ 0 ∧
      mobiusFn A B C D w = mobiusFn A' B' C' D' w) :
    ∀ w, mobiusFn A B C D w = mobiusFn A' B' C' D' w := by
  have hroot : ∀ w ∈ ({w₁, w₂, w₃} : Set ℂ),
      (A * C' - A' * C) * w ^ 2 + (A * D' + B * C' - A' * D - B' * C) * w + (B * D' - B' * D) = 0 := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hp w hw
    rw [mobiusFn, mobiusFn, div_eq_div_iff h1 h2] at h3
    linear_combination h3
  have r1 := hroot w₁ (by simp)
  have r2 := hroot w₂ (by simp)
  have r3 := hroot w₃ (by simp)
  set α := A * C' - A' * C with hα
  set β := A * D' + B * C' - A' * D - B' * C with hβ
  set δ := B * D' - B' * D with hδ
  have e12 : α * (w₁ + w₂) + β = 0 := by
    have hne : w₁ - w₂ ≠ 0 := sub_ne_zero.2 h12
    have : (w₁ - w₂) * (α * (w₁ + w₂) + β) = 0 := by linear_combination r1 - r2
    exact (mul_eq_zero.1 this).resolve_left hne
  have e13 : α * (w₁ + w₃) + β = 0 := by
    have hne : w₁ - w₃ ≠ 0 := sub_ne_zero.2 h13
    have : (w₁ - w₃) * (α * (w₁ + w₃) + β) = 0 := by linear_combination r1 - r3
    exact (mul_eq_zero.1 this).resolve_left hne
  have hα0 : α = 0 := by
    have hne : w₂ - w₃ ≠ 0 := sub_ne_zero.2 h23
    have : (w₂ - w₃) * α = 0 := by linear_combination e12 - e13
    exact (mul_eq_zero.1 this).resolve_left hne
  have hβ0 : β = 0 := by linear_combination e12 - (w₁ + w₂) * hα0
  have hδ0 : δ = 0 := by linear_combination r1 - w₁ ^ 2 * hα0 - w₁ * hβ0
  have hpoly : ∀ w, (A * w + B) * (C' * w + D') = (A' * w + B') * (C * w + D) := by
    intro w
    linear_combination w ^ 2 * hα0 + w * hβ0 + hδ0
  intro w
  by_cases hw : C * w + D = 0
  · have hAB : A * w + B ≠ 0 := by
      intro h0
      apply h
      linear_combination A * hw - C * h0
    have hw' : C' * w + D' = 0 := by
      have e := hpoly w
      rw [hw, mul_zero] at e
      exact (mul_eq_zero.1 e).resolve_left hAB
    rw [mobiusFn, mobiusFn, hw, hw', div_zero, div_zero]
  · by_cases hw' : C' * w + D' = 0
    · exfalso
      have hAB : A' * w + B' ≠ 0 := by
        intro h0
        apply h'
        linear_combination A' * hw' - C' * h0
      have e := hpoly w
      rw [hw', mul_zero] at e
      exact (mul_eq_zero.1 e.symm).elim hAB hw
    · rw [mobiusFn, mobiusFn, div_eq_div_iff hw hw']
      exact hpoly w

/-- The determinant of `γ ∈ SL(2, ℝ)`, cast to `ℂ`: `a d - b c = 1`. -/
theorem h36p_d_det (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- `γ ∈ SL(2, ℝ)` maps `𝕃` into `𝕃`. -/
theorem h36p_d_im_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z.im < 0) :
    (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im < 0 := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hden := k24_d_den_ne_zero hdetR hz.ne
  rw [mobiusFn_im_real, hdetR, one_mul]
  exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.2 hden)

/-- `γ ∈ SL(2, ℝ)` maps `ℍ` into `ℍ`. -/
theorem h36p_d_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hden := k24_d_den_ne_zero hdetR hz.ne'
  rw [mobiusFn_im_real, hdetR, one_mul]
  exact div_pos hz (Complex.normSq_pos.2 hden)

/-- **The Möbius relation of `f_μ`** (`k24_mob_core`): for a `Γ`-compatible `μ ∈ M` and `γ ∈ Γ`,
`f_μ ∘ γ = M ∘ f_μ` on all of `ℂ` for a Möbius `M = (A, B, C, D)`. -/
theorem h36p_d_rel (μ : BeltramiH) (hμ : IsGammaCompatible Γ μ.1) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) : ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z, normalizedSolution μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn A B C D (normalizedSolution μ.1 z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, -, -⟩ := ut_spec μ
  exact k24_mob_core hK hs h0 γ (k24_dil_comp μ hμ hγ) (ut_spec μ)

/-- **Möbius rigidity from `𝕃`.**  If injective `f₁, f₂` fixing `0` agree on `𝕃` and `fⱼ ∘ γ = Mⱼ ∘ fⱼ` on `ℂ`
(`γ ∈ SL(2, ℝ)`, `Mⱼ` Möbius), then `M₁ = M₂` on `ℂ`: they agree at the three points `f₁(-i), f₁(-2i), f₁(-3i)`,
which are off both poles because `fⱼ(γ z) ≠ 0 = fⱼ(0)` for `z ∈ 𝕃` (`γ z ∈ 𝕃`). -/
theorem h36p_d_mob_eq {f₁ f₂ : ℂ → ℂ} (hi₁ : Function.Injective f₁) (hi₂ : Function.Injective f₂)
    (h0₁ : f₁ 0 = 0) (h0₂ : f₂ 0 = 0) (heq : EqOn f₁ f₂ lowerHalf) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {A B C D A' B' C' D' : ℂ} (h : A * D - B * C ≠ 0) (h' : A' * D' - B' * C' ≠ 0)
    (hr₁ : ∀ z, f₁ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (f₁ z))
    (hr₂ : ∀ z, f₂ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A' B' C' D' (f₂ z)) :
    ∀ w, mobiusFn A B C D w = mobiusFn A' B' C' D' w := by
  -- the three points and their properties
  have key : ∀ z ∈ lowerHalf, C * f₁ z + D ≠ 0 ∧ C' * f₁ z + D' ≠ 0 ∧
      mobiusFn A B C D (f₁ z) = mobiusFn A' B' C' D' (f₁ z) := by
    intro z hz
    have hγz : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ∈ lowerHalf := h36p_d_im_neg γ hz
    have hne : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ≠ 0 := by
      intro h0
      have := hγz
      rw [h0] at this
      exact lt_irrefl (0 : ℝ) (by simp [lowerHalf] at this)
    refine ⟨fun hp => ?_, fun hp => ?_, ?_⟩
    · apply hne
      apply hi₁
      rw [hr₁, h0₁, mobiusFn, hp, div_zero]
    · apply hne
      apply hi₂
      rw [hr₂, h0₂, ← heq hz, mobiusFn, hp, div_zero]
    · rw [← hr₁, heq hγz, hr₂, heq hz]
  have hL : ∀ n : ℕ, (-(((n : ℂ) + 1) * I)) ∈ lowerHalf := fun n => by
    show (-(((n : ℂ) + 1) * I)).im < 0
    simp only [neg_im, mul_im, I_re, I_im, mul_zero, mul_one]
    have : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
    rw [this]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hdist : ∀ m n : ℕ, m ≠ n → f₁ (-(((m : ℂ) + 1) * I)) ≠ f₁ (-(((n : ℂ) + 1) * I)) := by
    intro m n hmn he
    apply hmn
    have h1 := hi₁ he
    have h2 : ((m : ℂ) + 1) * I = ((n : ℂ) + 1) * I := neg_injective h1
    have h3 : (m : ℂ) + 1 = (n : ℂ) + 1 := mul_right_cancel₀ I_ne_zero h2
    exact_mod_cast add_right_cancel h3
  refine h36p_d_mob_ext h h' (hdist 0 1 (by norm_num)) (hdist 0 2 (by norm_num)) (hdist 1 2 (by norm_num)) ?_
  intro w hw
  rcases hw with rfl | rfl | rfl
  · exact key _ (hL 0)
  · exact key _ (hL 1)
  · exact key _ (hL 2)

/-- Commutation through a conjugacy: if `H ∘ P = B`, `H ∘ T = M ∘ H`, `B ∘ T = M ∘ B` and `H` is injective, then
`P ∘ T = T ∘ P`. -/
theorem h36p_d_comm {H B P T M : ℂ → ℂ} (hinj : Function.Injective H) (hHP : ∀ z, H (P z) = B z)
    (hH : ∀ z, H (T z) = M (H z)) (hB : ∀ z, B (T z) = M (B z)) : ∀ z, P (T z) = T (P z) := by
  intro z
  apply hinj
  rw [hHP, hB, hH, hHP]

/-- **Equivariance ⟹ compatibility.**  For a continuous `P` which does not vanish on `ℍ` and satisfies
`P ∘ γ = M_γ ∘ P` on `ℂ` (a Möbius `M_γ` for every `γ ∈ Γ`), `𝟙_ℍ μ_P` is `Γ`-compatible, at every point of
`ℍ`: `μ_P(z) = μ_{M_γ ∘ P}(z) = μ_{P ∘ γ}(z) = μ_P(γ z) (cz + d)²/conj (cz + d)²` (the pole of `M_γ` is
avoided since `P(γ z) ≠ 0`). -/
theorem h36p_d_compat {P : ℂ → ℂ} (hPc : Continuous P) (hP0 : ∀ z ∈ upperHalf, P z ≠ 0)
    (hrel : ∀ γ ∈ Γ, ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z, P (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (P z)) :
    IsGammaCompatible Γ (upperHalf.indicator (complexDilatation P)) := by
  intro γ hγ
  obtain ⟨A, B, C, D, hdet, hr⟩ := hrel γ hγ
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
  have hz' : 0 < z.im := hz
  have hγz : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ∈ upperHalf := h36p_d_im_pos γ hz'
  have hpole : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := k24_d_den_ne_zero hdetR hz'.ne'
  have hPpole : C * P z + D ≠ 0 := by
    intro hp
    apply hP0 _ hγz
    rw [hr, mobiusFn, hp, div_zero]
  have e1 := k24_d_dil_mobius P (h36p_d_det γ) hpole
  have hh : DifferentiableAt ℂ (mobiusFn A B C D) (P z) := by
    show DifferentiableAt ℂ (fun w => (A * w + B) / (C * w + D)) (P z)
    exact DifferentiableAt.fun_div (by fun_prop) (by fun_prop) hPpole
  have hden := mobiusFn_inv_den_ne_zero hdet hPpole
  have hk : DifferentiableAt ℂ (mobiusFn D (-B) (-C) A) (mobiusFn A B C D (P z)) := by
    show DifferentiableAt ℂ (fun w => (D * w + -B) / (-C * w + A)) (mobiusFn A B C D (P z))
    exact DifferentiableAt.fun_div (by fun_prop) (by fun_prop) hden
  have hkh : ∀ᶠ w in 𝓝 (P z), mobiusFn D (-B) (-C) A (mobiusFn A B C D w) = w := by
    have hc : Continuous fun w : ℂ => C * w + D := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hPpole] with w hw
    exact mobiusFn_inv_apply hdet hw
  have e2 := s23_dilatation_comp_left hPc.continuousAt hh hk hkh
  have e3 : P ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) = mobiusFn A B C D ∘ P := funext hr
  rw [e3, e2] at e1
  show upperHalf.indicator (complexDilatation P) z =
    upperHalf.indicator (complexDilatation P) (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))
  rw [indicator_of_mem hz, indicator_of_mem hγz]
  exact e1

/-- **Normalized uniqueness** (`thm13_5_uniqueness_plane`, the argument of `h35b_eq_on_real`): a normalized q.c.
self-map `H` of the plane, holomorphic on `𝕃`, is the normalized solution of `𝟙_ℍ μ_H`. -/
theorem h36p_d_norm_eq {H : ℂ → ℂ} {K : ℝ} (hH : IsKQC H univ K) (hHs : H '' univ = univ) (hH0 : H 0 = 0)
    (hH1 : H 1 = 1) (hHd : DifferentiableOn ℂ H lowerHalf) :
    normalizedSolution (upperHalf.indicator (complexDilatation H)) = H := by
  set ν' : BeltramiH := ⟨upperHalf.indicator (complexDilatation H), ut_rg_indicator_mem hH⟩ with hν'
  obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ν'
  refine thm13_5_uniqueness_plane hq ⟨K, hH⟩ hs hHs ?_ hq0 hq1 hH0 hH1
  filter_upwards [hd, aw_nu_indicator_ae_eq hHd] with z h1 h2
  exact h1.trans h2

/-- For `μ ∈ M` with `|μ| ≤ k < 1` everywhere, `f_μ` is `(1 + k)/(1 - k)`-q.c. on the plane (Theorem 13.7 and
uniqueness). -/
theorem h36p_d_isKQC_of_bound (μ : BeltramiH) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ.1 z‖ ≤ k) :
    IsKQC (normalizedSolution μ.1) univ ((1 + k) / (1 - k)) := by
  obtain ⟨⟨k', -, -, hm, -⟩, -⟩ := μ.2
  have hμ : IsBeltramiCoeff μ.1 univ k := ⟨hm, Eventually.of_forall hb⟩
  obtain ⟨f, -, hK, huniq⟩ := thm13_7_normalized_existence hk0 hk1 hμ
  rw [huniq _ (ut_spec μ)]
  exact hK

/-- **[P4, stub] (B_Γ) The Γ-equivariant Teichmüller lemma** ("infinitesimally trivial ⟹ trivial to second
order").  A bounded measurable `Γ`-compatible `κ`, zero on the closed lower half-plane, annihilating the
kernels `(ζ - z)⁻³(ζ - w)⁻¹` (`z, w ∈ 𝕃`), is to second order the dilatation of trivial `π' ∈ M(Γ)`:
`|π' - tκ| ≤ C t²` a.e. on `ℍ` for `0 < t < t₀`.  Route (the disc `h35_trivial`, made equivariant): scale
`κ` into `M`; `h35b_bers_small` gives `‖φ_{tκ}‖ = O(t²)` with `φ_{tκ} ∈ Q(Γ, 𝕃)` (`bersFunctionGamma_mem`);
`lemma33_3` gives `σ ∈ M(Γ)`, `σ = -2y² φ_{tκ}(z̄)`, `‖σ‖ = O(t²)`, `bersFunction σ = φ_{tκ}`; `h35b_eq_on_real`
and `h35b_P` make `P = f_σ⁻¹ ∘ f_{tκ}` q.c., `P|ℝ = id`, `|μ_P - tκ| = O(t²)`; `P` commutes with `Γ`
(`k24_rel_exists` for `f_{tκ}` and `f_σ`: the two Möbius maps agree on `f(ℝ)`), so `π' = 𝟙_ℍ μ_P ∈ M(Γ)`, and
`f_{π'} = P` (normalized uniqueness) gives `IsTrivialBeltrami`. -/
theorem h36p_teich_lemma (hΓ : IsFuchsian Γ) {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ volume) {M : ℝ}
    (hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ M) (hκ0 : ∀ z : ℂ, z.im ≤ 0 → κ z = 0)
    (hκΓ : IsGammaCompatible Γ κ)
    (horth : ∀ z ∈ lowerHalf, ∀ w ∈ lowerHalf, ∫ ζ, κ ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ∃ π' : BeltramiGamma Γ,
      IsTrivialBeltrami Γ π' ∧ ∀ᵐ z ∂(volume.restrict upperHalf), ‖π'.1.1 z - t * κ z‖ ≤ C * t ^ 2 := by
  -- scale `κ` into `M`: `κ' = λ κ`, `|κ'| ≤ 1/2`
  set lam : ℝ := 1 / (2 * (|M| + 1)) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamM : lam * |M| ≤ 1 / 2 := by
    rw [hlam, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [abs_nonneg M]
  have hκb : ∀ᵐ z, ‖κ z‖ ≤ |M| := by
    have h1 : ∀ᵐ z, z ∈ upperHalf → ‖κ z‖ ≤ M :=
      (ae_restrict_iff' isOpen_upperHalf.measurableSet).1 hκM
    filter_upwards [h1] with z hz
    by_cases hzU : z ∈ upperHalf
    · exact (hz hzU).trans (le_abs_self M)
    · rw [hκ0 z (not_lt.1 hzU), norm_zero]
      exact abs_nonneg M
  have hκ'mem : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun z => (lam : ℂ) * κ z) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → (lam : ℂ) * κ z = 0 := by
    refine ⟨⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩, fun z hz => by rw [hκ0 z hz, mul_zero]⟩
    · rw [Measure.restrict_univ]
      exact hκm.const_mul _
    · rw [Measure.restrict_univ]
      filter_upwards [hκb] with z hz
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
      calc lam * ‖κ z‖ ≤ lam * |M| := by gcongr
        _ ≤ 1 / 2 := hlamM
  set κ' : BeltramiH := ⟨fun z => (lam : ℂ) * κ z, hκ'mem⟩ with hκ'def
  have hκ'Γ : IsGammaCompatible Γ κ'.1 := by
    intro γ hγ
    filter_upwards [hκΓ γ hγ] with z hz
    show (lam : ℂ) * κ z = (lam : ℂ) * κ _ * _
    rw [hz]
    ring
  have horth' : ∀ z ∈ lowerHalf, ∀ w ∈ lowerHalf, ∫ ζ, κ'.1 ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0 := by
    intro z hz w hw
    have e : (fun ζ => κ'.1 ζ / ((ζ - z) ^ 3 * (ζ - w))) =
        fun ζ => (lam : ℂ) * (κ ζ / ((ζ - z) ^ 3 * (ζ - w))) := by
      funext ζ
      show (lam : ℂ) * κ ζ / _ = _
      ring
    rw [e, integral_const_mul, horth z hz w hw, mul_zero]
  -- the Bers function of `s κ'` is `O(s²)`
  obtain ⟨r, hr, k, hk0, hk1, hb, hS⟩ := h35b_bers_small κ' horth'
  refine ⟨6 / (r ^ 2 * lam ^ 2), lam * (r / 2), by positivity, by positivity, fun t ht0 ht1 => ?_⟩
  set s : ℝ := t / lam with hsdef
  have hs0 : 0 < s := div_pos ht0 hlam0
  have hsr2 : s < r / 2 := by
    rw [hsdef, div_lt_iff₀ hlam0]
    linarith
  have hsb : (s : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    linarith
  set ν : BeltramiH := h35_pd_q_fam h35_pd_q_zero κ' (s : ℂ) with hνdef
  have hνval : ν.1 = fun w => (s : ℂ) * κ'.1 w := h35b_fam_eq κ' hk0 hk1 hb hsb
  have hνΓ : IsGammaCompatible Γ ν.1 := by
    intro γ hγ
    filter_upwards [hκ'Γ γ hγ] with z hz
    rw [hνval]
    show (s : ℂ) * κ'.1 z = (s : ℂ) * κ'.1 _ * _
    rw [hz]
    ring
  set s' : ℝ := 3 / 2 * s ^ 2 / r ^ 2 with hs'def
  have hs'0 : 0 ≤ s' := by positivity
  have hs'8 : s' < 3 / 8 := by
    have h1 : s ^ 2 < (r / 2) ^ 2 := by gcongr
    rw [hs'def, div_lt_iff₀ (by positivity)]
    nlinarith
  have hφpt : ∀ z ∈ lowerHalf, ‖bersFunction ν.1 z‖ * z.im ^ 2 ≤ s' := by
    intro z hz
    rw [bersFunction, indicator_of_mem hz]
    have h := hS (s : ℂ) hsb z hz
    rwa [Complex.norm_real, Real.norm_of_nonneg hs0.le] at h
  have hφN : bersNormL (bersFunction ν.1) ≤ ENNReal.ofReal s' :=
    iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (hφpt z hz)
  have hφlt : bersNormL (bersFunction ν.1) < ENNReal.ofReal (1 / 2) :=
    lt_of_le_of_lt hφN ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by linarith))
  obtain ⟨hφA, -, -⟩ := bersFunctionGamma_mem hΓ (⟨ν, hνΓ⟩ : BeltramiGamma Γ)
  -- `lemma33_3`: the equivariant Ahlfors–Weill section `σ ∈ M(Γ)`, `‖σ‖ ≤ 2 s'`
  obtain ⟨σ, hσval, hσB⟩ := (lemma33_3 hΓ).2 (bersFunction ν.1) hφA hφlt
  have hσφ : bersFunction σ.1.1 = bersFunction ν.1 := (bg_bersMapGamma_eq rfl).symm.trans hσB
  have hσb : ∀ z, ‖σ.1.1 z‖ ≤ 2 * s' := by
    intro z
    by_cases hz : 0 < z.im
    · rw [hσval z hz]
      have hcz : conj z ∈ lowerHalf := by
        show (conj z).im < 0
        rw [Complex.conj_im]
        linarith
      have h := hφpt (conj z) hcz
      rw [Complex.conj_im, neg_sq] at h
      rw [norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [show ‖(2 : ℂ)‖ = 2 by simp]
      nlinarith
    · rw [σ.1.2.2 z (not_lt.1 hz), norm_zero]
      positivity
  have hσK : IsKQC (normalizedSolution σ.1.1) univ ((1 + 2 * s') / (1 - 2 * s')) :=
    h36p_d_isKQC_of_bound σ.1 (by positivity) (by linarith) hσb
  have hσKU : IsKQC (normalizedSolution σ.1.1) upperHalf ((1 + 2 * s') / (1 - 2 * s')) :=
    ac_t_isKQC_restrict hσK isOpen_upperHalf (subset_univ _)
  obtain ⟨-, hσs, hσ0, -, -⟩ := ut_spec σ.1
  obtain ⟨⟨Kν, hνK⟩, -, hν0, -, -⟩ := ut_spec ν
  have hx : ∀ x : ℝ, normalizedSolution σ.1.1 x = normalizedSolution ν.1 x := by
    have hrel := bA_equiv_of_schwarzian_eq (μ := σ.1) (ν := ν) fun z hz => by
      have h := congrFun hσφ z
      rwa [bersFunction, bersFunction, indicator_of_mem hz, indicator_of_mem hz] at h
    intro x
    exact hrel x
  -- `P = f_σ⁻¹ ∘ f_ν`
  obtain ⟨⟨KP, hP⟩, hPs, hfix, hdil⟩ := h35b_P ν hσK hσs hσKU hx
  set fσ : ℂ → ℂ := normalizedSolution σ.1.1 with hfσ
  set fν : ℂ → ℂ := normalizedSolution ν.1 with hfν
  set P : ℂ → ℂ := Function.invFunOn fσ univ ∘ fν with hPdef
  have hiσ : Function.Injective fσ := injOn_univ.1 hσK.2.2.1.2.1
  have hiν : Function.Injective fν := injOn_univ.1 hνK.2.2.1.2.1
  have hleft : ∀ z, Function.invFunOn fσ univ (fσ z) = z := fun z =>
    hσK.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, fσ (Function.invFunOn fσ univ w) = w := fun w =>
    Function.invFunOn_eq (show w ∈ fσ '' univ by rw [hσs]; exact mem_univ w)
  have hL : EqOn fσ fν lowerHalf := (fMu_lower_model σ.1 ν).2 hx
  have hPL : ∀ z ∈ lowerHalf, P z = z := fun z hz => by
    show Function.invFunOn fσ univ (fν z) = z
    rw [← hL hz, hleft]
  have hPd : DifferentiableOn ℂ P lowerHalf := differentiableOn_id.congr fun z hz => hPL z hz
  have hHP : ∀ z, fσ (P z) = fν z := fun z => hright _
  -- `P` commutes with `Γ`
  have hrelP : ∀ γ ∈ Γ, ∀ z, P (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (P z) := by
    intro γ hγ
    obtain ⟨A, B, C, D, hd, hr⟩ := h36p_d_rel σ.1 σ.2 hγ
    obtain ⟨A', B', C', D', hd', hr'⟩ := h36p_d_rel ν hνΓ hγ
    have hM := h36p_d_mob_eq hiσ hiν hσ0 hν0 hL γ hd hd' hr hr'
    exact h36p_d_comm hiσ hHP hr fun z => (hr' z).trans (hM _).symm
  have hPc : Continuous P := continuousOn_univ.1 hP.2.2.1.1
  have hPH : P '' upperHalf = upperHalf := (ut_preserves_halves hP hPs hfix).1
  have hP0 : ∀ z ∈ upperHalf, P z ≠ 0 := fun z hz h0 => by
    have h1 : P z ∈ upperHalf := hPH ▸ mem_image_of_mem P hz
    rw [h0] at h1
    exact lt_irrefl (0 : ℝ) (by simp [upperHalf] at h1)
  have hπΓ : IsGammaCompatible Γ (upperHalf.indicator (complexDilatation P)) :=
    h36p_d_compat hPc hP0 fun γ hγ =>
      ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, by rw [h36p_d_det γ]; exact one_ne_zero, hrelP γ hγ⟩
  have hPfix0 : P 0 = 0 := by simpa using hfix 0
  have hPfix1 : P 1 = 1 := by simpa using hfix 1
  refine ⟨⟨⟨upperHalf.indicator (complexDilatation P), ut_rg_indicator_mem hP⟩, hπΓ⟩, fun x => ?_, ?_⟩
  · show normalizedSolution (upperHalf.indicator (complexDilatation P)) x = x
    rw [h36p_d_norm_eq hP hPs hPfix0 hPfix1 hPd]
    exact hfix x
  · filter_upwards [hdil, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzU
    show ‖upperHalf.indicator (complexDilatation P) z - t * κ z‖ ≤ _
    rw [indicator_of_mem hzU]
    have hνz : ν.1 z = (t : ℂ) * κ z := by
      rw [hνval]
      show (s : ℂ) * ((lam : ℂ) * κ z) = _
      rw [← mul_assoc, ← Complex.ofReal_mul, hsdef, div_mul_cancel₀ _ hlam0.ne']
    rw [hνz] at hz
    refine hz.trans (le_of_eq ?_)
    have hne : 1 - 2 * s' ≠ 0 := by linarith
    have hK : ((1 + 2 * s') / (1 - 2 * s') - 1) / ((1 + 2 * s') / (1 - 2 * s') + 1) = 2 * s' := by
      rw [div_sub_one hne, div_add_one hne, div_div_div_cancel_right₀ hne]
      ring
    rw [hK, hs'def, hsdef]
    field_simp
    ring

/-- **[P4, stub] The trivial translate.**  For `μ ∈ M(Γ)` and a trivial `π' ∈ M(Γ)` there is `μ' ∈ M(Γ)` in
the class of `μ` with `‖μ'‖_∞ ≤ tanh τ(μ, π')`.  Route: `g = f_{π'}` fixes `ℝ` pointwise, so `g(ℍ) = ℍ`,
`g` is conformal on `𝕃`, and `g ∘ γ = γ ∘ g` (`k24_rel_exists`; the Möbius map agrees with `γ` on `ℝ`);
`F = f_μ ∘ g⁻¹` has `|μ_F(g z)| = |(μ - π')/(1 - π̄' μ)|(z) = tanh d(μ(z), π'(z))` a.e.
(`ahQ_comp_inv_dilatation`, Lusin (N) for `g`), `F|ℝ = f_μ|ℝ`, `F` conjugates `Γ` to Möbius maps; so
`μ' = 𝟙_ℍ μ_F ∈ M(Γ)`, `f_{μ'} = F` (normalized uniqueness), and `lemma33_1` gives the class. -/
theorem h36p_translate (μ π' : BeltramiGamma Γ) (hπ' : IsTrivialBeltrami Γ π') :
    ∃ μ' : BeltramiGamma Γ, teichSetoidGamma Γ μ' μ ∧
      beltramiNormH μ'.1.1 ≤ Real.tanh (beltramiPoincareDist μ.1.1 π'.1.1) := by
  obtain ⟨⟨Kg, hg⟩, hgs, hg0, -, hgd⟩ := ut_spec π'.1
  obtain ⟨⟨Kf, hf⟩, hfs, hf0, hf1, hfd⟩ := ut_spec μ.1
  set g : ℂ → ℂ := normalizedSolution π'.1.1 with hgdef
  set f : ℂ → ℂ := normalizedSolution μ.1.1 with hfdef
  -- `g = f_{π'}` is the identity on `𝕃` and on `ℝ`
  have hgL : ∀ z ∈ lowerHalf, g z = z := by
    have h := (fMu_lower_model π'.1 ⟨0, bB_l_zero_mem⟩).2 fun x => by
      show normalizedSolution π'.1.1 x = normalizedSolution (0 : ℂ → ℂ) x
      rw [bB_l_normalizedSolution_zero]
      exact hπ' x
    intro z hz
    have h1 := h hz
    change g z = normalizedSolution (0 : ℂ → ℂ) z at h1
    rw [h1, bB_l_normalizedSolution_zero]
    rfl
  have hgi : Function.Injective g := injOn_univ.1 hg.2.2.1.2.1
  set gi : ℂ → ℂ := Function.invFunOn g univ with hgidef
  have hleft : ∀ z, gi (g z) = z := fun z => hg.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, g (gi w) = w := fun w =>
    Function.invFunOn_eq (show w ∈ g '' univ by rw [hgs]; exact mem_univ w)
  have hgiR : ∀ x : ℝ, gi x = x := fun x => by
    conv_lhs => rw [← hπ' x]
    exact hleft _
  have hgiL : ∀ z ∈ lowerHalf, gi z = z := fun z hz => by
    conv_lhs => rw [← hgL z hz]
    exact hleft z
  have hgiK : IsKQC gi univ Kg := by
    have h := thm7_2_inv hg
    rwa [hgs] at h
  -- `F = f_μ ∘ g⁻¹`
  set F : ℂ → ℂ := f ∘ gi with hFdef
  have hF : IsKQC F univ (Kg * Kf) := thm7_1_comp hgiK hf (subset_univ _)
  have hgis : gi '' univ = univ := eq_univ_of_forall fun z => ⟨g z, mem_univ _, hleft z⟩
  have hFs : F '' univ = univ := by rw [hFdef, image_comp, hgis, hfs]
  have hF0 : F 0 = 0 := by
    show f (gi 0) = 0
    rw [show gi 0 = 0 by simpa using hgiR 0, hf0]
  have hF1 : F 1 = 1 := by
    show f (gi 1) = 1
    rw [show gi 1 = 1 by simpa using hgiR 1, hf1]
  have hFd : DifferentiableOn ℂ F lowerHalf :=
    (ut_conformal_lowerHalf μ.1).1.congr fun z hz => by
      show f (gi z) = f z
      rw [hgiL z hz]
  -- `F` is `Γ`-equivariant: `g` commutes with `Γ` (its Möbius map is `γ`, as `g = id` on `𝕃`)
  have hrelF : ∀ γ ∈ Γ, ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z, F (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (F z) := by
    intro γ hγ
    obtain ⟨A, B, C, D, hd, hr⟩ := h36p_d_rel π'.1 π'.2 hγ
    have hdγ : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [h36p_d_det γ]; exact one_ne_zero
    have hM := h36p_d_mob_eq hgi Function.injective_id hg0 rfl (fun z hz => hgL z hz) γ hd hdγ hr
      fun z => rfl
    have hgγ : ∀ z, g (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (g z) := fun z => (hr z).trans (hM _)
    have hgiγ := h36p_d_comm (B := id) hgi hright hgγ fun z => rfl
    obtain ⟨A', B', C', D', hd', hr'⟩ := h36p_d_rel μ.1 μ.2 hγ
    refine ⟨A', B', C', D', hd', fun z => ?_⟩
    show f (gi (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)) = mobiusFn A' B' C' D' (f (gi z))
    rw [hgiγ]
    exact hr' (gi z)
  have hiF : Function.Injective F := injOn_univ.1 hF.2.2.1.2.1
  have hF0' : ∀ z ∈ upperHalf, F z ≠ 0 := fun z hz h0 => by
    have hz0 : z = 0 := hiF (h0.trans hF0.symm)
    rw [hz0] at hz
    exact lt_irrefl (0 : ℝ) (by simp [upperHalf] at hz)
  have hμΓ : IsGammaCompatible Γ (upperHalf.indicator (complexDilatation F)) :=
    h36p_d_compat (continuousOn_univ.1 hF.2.2.1.1) hF0' hrelF
  have hnorm : normalizedSolution (upperHalf.indicator (complexDilatation F)) = F :=
    h36p_d_norm_eq hF hFs hF0 hF1 hFd
  refine ⟨⟨⟨upperHalf.indicator (complexDilatation F), ut_rg_indicator_mem hF⟩, hμΓ⟩, ?_, ?_⟩
  · -- the class: `F = f_μ` on `ℝ` (`lemma33_1`)
    refine (lemma33_1 ⟨upperHalf.indicator (complexDilatation F), ut_rg_indicator_mem hF⟩ μ.1).2 fun x => ?_
    show normalizedSolution (upperHalf.indicator (complexDilatation F)) x = f x
    rw [hnorm]
    show f (gi x) = f x
    rw [hgiR]
  · -- the norm: `|μ_F(g z)| ≤ |(μ - π')/(1 - π̄' μ)|(z) = tanh d(μ z, π' z) ≤ tanh τ`
    set τ : ℝ := beltramiPoincareDist μ.1.1 π'.1.1 with hτ
    obtain ⟨k₁, hk₁0, hk₁1, hb₁⟩ := beltramiH_ae_bound μ.1
    obtain ⟨k₂, hk₂0, hk₂1, hb₂⟩ := beltramiH_ae_bound π'.1
    set k : ℝ := max k₁ k₂ with hkdef
    have hk0 : 0 ≤ k := le_max_of_le_left hk₁0
    have hk1 : k < 1 := max_lt hk₁1 hk₂1
    have hc1 : 2 * k / (1 + k ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [sq_nonneg (1 - k)]
    set ρ : ℂ → ℝ := fun z => ‖(μ.1.1 z - π'.1.1 z) / (1 - conj (μ.1.1 z) * π'.1.1 z)‖ with hρdef
    have hρc : ∀ᵐ z ∂(volume.restrict upperHalf), ρ z ≤ 2 * k / (1 + k ^ 2) := by
      filter_upwards [hb₁, hb₂] with z h1 h2
      show ‖(μ.1.1 z - π'.1.1 z) / (1 - conj (μ.1.1 z) * π'.1.1 z)‖ ≤ _
      rw [c36_b_norm_conj_denom]
      exact ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
    have hdρ : ∀ z, ρ z < 1 → discPoincareDist (μ.1.1 z) (π'.1.1 z) = Real.artanh (ρ z) := by
      intro z hz
      rw [discPoincareDist, Real.artanh_eq_half_log ⟨le_trans (by norm_num) (norm_nonneg _), hz.le⟩]
    have hne : essSup (fun z => ENNReal.ofReal (discPoincareDist (μ.1.1 z) (π'.1.1 z)))
        (volume.restrict upperHalf) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (essSup_le_of_ae_le (ENNReal.ofReal (Real.artanh (2 * k / (1 + k ^ 2)))) ?_)
      filter_upwards [hρc] with z hz
      rw [hdρ z (hz.trans_lt hc1)]
      exact ENNReal.ofReal_le_ofReal (Real.artanh_le_artanh (lt_of_lt_of_le (by norm_num) (norm_nonneg _)) hc1 hz)
    have hdτ : ∀ᵐ z ∂(volume.restrict upperHalf), discPoincareDist (μ.1.1 z) (π'.1.1 z) ≤ τ := by
      filter_upwards [ENNReal.ae_le_essSup
        (fun z => ENNReal.ofReal (discPoincareDist (μ.1.1 z) (π'.1.1 z)))] with z hz
      rcases le_or_gt (discPoincareDist (μ.1.1 z) (π'.1.1 z)) 0 with h | h
      · exact h.trans ENNReal.toReal_nonneg
      · rw [← ENNReal.toReal_ofReal h.le]
        exact ENNReal.toReal_mono hne hz
    have hρτ : ∀ᵐ z ∂(volume.restrict upperHalf), ρ z ≤ Real.tanh τ := by
      filter_upwards [hρc, hdτ] with z h1 h2
      have hρ1 : ρ z < 1 := h1.trans_lt hc1
      have hρ0 : 0 ≤ ρ z := norm_nonneg _
      rw [hdρ z hρ1] at h2
      calc ρ z = Real.tanh (Real.artanh (ρ z)) := (Real.tanh_artanh ⟨by linarith, hρ1⟩).symm
        _ ≤ Real.tanh τ := h36t_tanh_le_tanh h2
    -- the chain rule for `F = f_μ ∘ g⁻¹` at `g z`
    have hid : ∀ᵐ z ∂(volume.restrict upperHalf), ‖complexDilatation F (g z)‖ ≤ ρ z := by
      have h := ahQ_comp_inv_dilatation hf hg
      rw [Measure.restrict_univ] at h
      filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae hfd, ae_restrict_of_ae hgd] with z h1 h2 h3
      show ‖complexDilatation (f ∘ Function.invFunOn g univ) (g z)‖ ≤ _
      rw [h1, h2, h3, norm_mul]
      have hu : ‖dz g z / conj (dz g z)‖ ≤ 1 := by
        rw [norm_div, Complex.norm_conj]
        exact div_self_le_one _
      calc ‖(μ.1.1 z - π'.1.1 z) / (1 - conj (π'.1.1 z) * μ.1.1 z)‖ * ‖dz g z / conj (dz g z)‖
          ≤ ‖(μ.1.1 z - π'.1.1 z) / (1 - conj (π'.1.1 z) * μ.1.1 z)‖ * 1 :=
            mul_le_mul_of_nonneg_left hu (norm_nonneg _)
        _ = ρ z := by rw [mul_one]; exact (c36_b_norm_conj_denom _ _).symm
    -- transfer to a.e. `w = g z ∈ ℍ` (Lusin (N) for `g⁻¹`)
    have hgU : IsKQC g upperHalf Kg := ac_t_isKQC_restrict hg isOpen_upperHalf (subset_univ _)
    have hgH : g '' upperHalf = upperHalf := (ut_preserves_halves hg hgs hπ').1
    have hW : ∀ᵐ w ∂(volume.restrict upperHalf), ‖complexDilatation F w‖ ≤ Real.tanh τ := by
      have h := abT_ae_image hgU (p := fun w => ‖complexDilatation F w‖ ≤ Real.tanh τ)
        (by filter_upwards [hid, hρτ] with z h1 h2 using h1.trans h2)
      rwa [hgH] at h
    refine beltramiNormH_le_of_ae_bound (c36_d_tanh_nonneg ENNReal.toReal_nonneg) ?_
    filter_upwards [hW, ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw hwU
    show ‖upperHalf.indicator (complexDilatation F) w‖ ≤ _
    rw [indicator_of_mem hwU]
    exact hw

/-! ### B.2 Proved glue: the assembly of `hamilton_contradiction` (T5) -/

/-- `hamiltonNorm Γ F κ ≥ 0` (a supremum of norms; the empty supremum is `0`). -/
theorem h36p_hamiltonNorm_nonneg (F : Set ℂ) (κ : ℂ → ℂ) : 0 ≤ hamiltonNorm Γ F κ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- `Γ`-compatibility is preserved by differences. -/
theorem h36p_isGammaCompatible_sub {μ ν : ℂ → ℂ} (hμ : IsGammaCompatible Γ μ) (hν : IsGammaCompatible Γ ν) :
    IsGammaCompatible Γ (fun z => μ z - ν z) := by
  intro γ hγ
  filter_upwards [hμ γ hγ, hν γ hγ] with z h1 h2
  linear_combination h1 - h2

/-- An element of `integrableAutomorphicQD Γ F` is integrable on `F` (`F ⊆ ℍ` measurable). -/
theorem h36p_integrableOn_A {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) : IntegrableOn φ F := by
  refine ⟨(hφ.1.continuousOn.mono hFH).aestronglyMeasurable hFm, ?_⟩
  have h1 : (∫⁻ z in F, ‖φ z‖ₑ) = phiArea φ F := by
    unfold phiArea
    simp_rw [ofReal_norm]
  show (∫⁻ z in F, ‖φ z‖ₑ) < ⊤
  rw [h1]
  exact hφ.2.1

/-- A time `t` for the second-order estimate: `0 < t < t₀`, `t ≤ 1`, `t (k + H + C) ≤ 1/2` and
`t (k - H) - (C + 2 (k + H + C)²) t² > 0` (the choice of `h35_thm35_5_of_AB`). -/
theorem h36p_choose_t {k H C t₀ : ℝ} (hH0 : 0 ≤ H) (hkH : H < k) (hC : 0 ≤ C) (ht₀ : 0 < t₀) :
    ∃ t : ℝ, 0 < t ∧ t < t₀ ∧ t ≤ 1 ∧ t * (k + H + C) ≤ 1 / 2 ∧
      0 < t * (k - H) - (C + 2 * (k + H + C) ^ 2) * t ^ 2 := by
  have hk0 : 0 ≤ k := by linarith
  have hA0 : 0 ≤ k + H + C := by linarith
  have hE0 : 0 ≤ C + 2 * (k + H + C) ^ 2 := by positivity
  set A := k + H + C with hA
  set E := C + 2 * A ^ 2 with hE
  have hkH' : 0 < k - H := by linarith
  set t : ℝ := min (min (t₀ / 2) (1 / 2)) (min (1 / (2 * A + 2)) ((k - H) / (2 * (E + 1)))) with ht
  have htpos : 0 < t :=
    lt_min (lt_min (by linarith) (by norm_num)) (lt_min (by positivity) (by positivity))
  have htt₀ : t < t₀ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  have htA : t * A ≤ 1 / 2 := by
    have h1 : t ≤ 1 / (2 * A + 2) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : t * (2 * A + 2) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      exact h1
    nlinarith
  have htE : t * E < k - H := by
    have h1 : t ≤ (k - H) / (2 * (E + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨t, htpos, htt₀, ht1, htA, ?_⟩
  have : E * t ^ 2 = (t * E) * t := by ring
  rw [this]
  nlinarith

/-- **The assembly of `hamilton_contradiction`** (T5; the S35 disc assembly `h35_thm35_5_of_AB`, made
`Γ`-equivariant).  If `H = hamiltonNorm Γ F μ < k = ‖μ‖_∞`: (A_Γ) `h36p_duality_F` + `h36p_extend` give a
`Γ`-compatible `ν`, `|ν| ≤ H`, with `κ = μ - ν ⊥ A(Γ, F)`; T3 `h36p_kernel_cond` gives the kernel condition;
(B_Γ) `h36p_teich_lemma` gives trivial `π'` with `|π' - tκ| ≤ C t²`; the pointwise estimate `h35_pt_hyp` gives
`d(μ(z), π'(z)) ≤ artanh k - δ` a.e. (`δ > 0`), so `τ(μ, π') < artanh k ≤ τ(μ, 0)`. -/
theorem h36p_core (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    (hlt : hamiltonNorm Γ F μ.1.1 < beltramiNormH μ.1.1) :
    ∃ π' : BeltramiGamma Γ, IsTrivialBeltrami Γ π' ∧
      beltramiPoincareDist μ.1.1 π'.1.1 < beltramiPoincareDist μ.1.1 0 := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hH0 := h36p_hamiltonNorm_nonneg (Γ := Γ) F μ.1.1
  have hk1 : beltramiNormH μ.1.1 < 1 := beltramiNormH_lt_one μ.1
  have hkpos : 0 < beltramiNormH μ.1.1 := lt_of_le_of_lt hH0 hlt
  have hμk : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ.1.1 z‖ ≤ beltramiNormH μ.1.1 :=
    ae_norm_le_beltramiNormH (beltramiH_essSup_ne_top μ.1)
  obtain ⟨⟨k₀, -, -, hμm, hμb⟩, hμ0⟩ := μ.1.2
  rw [Measure.restrict_univ] at hμm hμb
  -- (A_Γ): duality on `F`, extended equivariantly
  obtain ⟨ν₀, hν₀m, hν₀H, hν₀pair⟩ := h36p_duality_F hF μ
  obtain ⟨ν, hνm, hν0, hνΓ, hνH, hνν₀⟩ := h36p_extend hΓ hF hH0 hν₀m hν₀H
  have hκm : AEStronglyMeasurable (fun z => μ.1.1 z - ν z) volume := hμm.sub hνm
  have hκM : ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖(fun z => μ.1.1 z - ν z) z‖ ≤ beltramiNormH μ.1.1 + hamiltonNorm Γ F μ.1.1 := by
    filter_upwards [hμk, hνH] with z h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hκ0 : ∀ z : ℂ, z.im ≤ 0 → (fun z => μ.1.1 z - ν z) z = 0 := fun z hz => by
    simp only [hμ0 z hz, hν0 z hz, sub_self]
  have hκΓ : IsGammaCompatible Γ (fun z => μ.1.1 z - ν z) := h36p_isGammaCompatible_sub μ.2 hνΓ
  have hκorth : ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F (fun z => μ.1.1 z - ν z) φ = 0 := by
    intro φ hφ
    have hφi := h36p_integrableOn_A hFH hFm hφ
    have hμφ : Integrable (fun z => μ.1.1 z * φ z) (volume.restrict F) :=
      hφi.bdd_mul hμm.restrict (ae_restrict_of_ae hμb)
    have hνφ : Integrable (fun z => ν z * φ z) (volume.restrict F) :=
      hφi.bdd_mul hνm.restrict (ae_restrict_of_ae_restrict_of_subset hFH hνH)
    have e1 : beltramiPairing F (fun z => μ.1.1 z - ν z) φ =
        beltramiPairing F μ.1.1 φ - beltramiPairing F ν φ := by
      unfold beltramiPairing
      rw [← integral_sub hμφ hνφ]
      congr 1
      funext z
      ring
    have e2 : beltramiPairing F ν φ = beltramiPairing F ν₀ φ :=
      integral_congr_ae (by filter_upwards [hνν₀] with z hz; rw [hz])
    rw [e1, e2, hν₀pair φ hφ, sub_self]
  -- T3 and (B_Γ)
  have hker := h36p_kernel_cond hΓ hF hκm.restrict hκM hκΓ hκ0 hκorth
  obtain ⟨C, t₀, hC, ht₀, htriv⟩ := h36p_teich_lemma hΓ hκm hκM hκ0 hκΓ hker
  obtain ⟨t, htpos, htt₀, ht1, htA, hδ⟩ := h36p_choose_t hH0 hlt hC ht₀
  obtain ⟨π', hπ'tr, hπ't⟩ := htriv t htpos htt₀
  refine ⟨π', hπ'tr, ?_⟩
  set k := beltramiNormH μ.1.1 with hkdef
  set H := hamiltonNorm Γ F μ.1.1 with hHdef
  set δ := t * (k - H) - (C + 2 * (k + H + C) ^ 2) * t ^ 2 with hδdef
  -- the pointwise hyperbolic estimate
  have hpt : ∀ᵐ z ∂(volume.restrict upperHalf),
      discPoincareDist (μ.1.1 z) (π'.1.1 z) ≤ Real.artanh k - δ := by
    filter_upwards [hμk, hνH, hπ't] with z h1 h2 h3
    have h4 : h35_pd_discPoincareDist (μ.1.1 z) (π'.1.1 z) ≤
        Real.artanh k - t * (k - H) + (C + 2 * (k + H + C) ^ 2) * t ^ 2 :=
      h35_pt_hyp hk1 h1 h2 hC htpos.le ht1 h3 htA
    have e : Real.artanh k - t * (k - H) + (C + 2 * (k + H + C) ^ 2) * t ^ 2 = Real.artanh k - δ := by
      rw [hδdef]
      ring
    rw [e] at h4
    exact h4
  -- `τ(μ, π') ≤ max (artanh k - δ) 0 < artanh k ≤ τ(μ, 0)`
  have hb : beltramiPoincareDist μ.1.1 π'.1.1 ≤ max (Real.artanh k - δ) 0 := by
    unfold beltramiPoincareDist
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (essSup_le_of_ae_le _ ?_)
    filter_upwards [hpt] with z hz
    exact ENNReal.ofReal_le_ofReal (hz.trans (le_max_left _ _))
  have hkI : k ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hk1⟩
  have hart : 0 < Real.artanh k := by
    have h := (Real.artanh_lt_artanh_iff (x := 0) (y := k) ⟨by norm_num, by norm_num⟩ hkI).2 hkpos
    rwa [Real.artanh_zero] at h
  have hmax : max (Real.artanh k - δ) 0 < Real.artanh k := max_lt (by linarith) hart
  exact lt_of_le_of_lt hb (lt_of_lt_of_le hmax (artanh_beltramiNormH_le μ.1))

/-- §36.3 (the final step of the proof of Hamilton's theorem): if `‖P_μ‖ < ‖μ‖_∞` for the extremal
`μ`, Hahn–Banach gives `ν` with `⟨ν, ω⟩ = ⟨μ, ω⟩` on `A(S)` and `‖ν‖ = ‖P_μ‖ < ‖μ‖`; then
`μ - ν ∈ T₀N`, so there is a path `α(t) ∈ N` with `α(0) = 0`, `α'(0) = μ - ν`, and Lemma 36.3 gives
`τ(μ, α(t₁)) < τ(μ, 0)` for small `t₁ > 0`: the map with dilatation `α(t₁)` is trivial and
`K[f ∘ g⁻¹] < K[f]` in the class of `f` — contradicting extremality. -/
theorem hamilton_contradiction (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    (hlt : hamiltonNorm Γ F μ.1.1 < beltramiNormH μ.1.1) :
    ∃ π' : BeltramiGamma Γ, IsTrivialBeltrami Γ π' ∧ beltramiPoincareDist μ.1.1 π'.1.1 < beltramiPoincareDist μ.1.1 0 := by
  exact h36p_core hΓ hF μ hlt

/-! ## BLOCK C — install just after `hamilton_contradiction`, above the moved §36.2 block

Scout B's reductions R0–R3 (renamed `h36_` → `h36p_`), re-checked against the installed F5/F6/F7 statements.
`thm36_2_finite_type` precedes `pairing_eq_norm_imp_teichmuller` inside the moved block, and the block moves
verbatim; so R2/R3 use verbatim copies of `ae_ne_zero_of_differentiableOn_upperHalf` and
`pairing_eq_norm_imp_teichmuller` (C.1). -/

/-! ### C.2 Scout B's reductions R0–R3 -/

/-- An element of `integrableAutomorphicQD Γ F` of area `1` is integrable on `F` with `∫_F |φ| = 1`. -/
theorem h36p_integrableOn_of_unit {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) :
    IntegrableOn φ F ∧ ∫ z in F, ‖φ z‖ = 1 := by
  have hφmeas : AEStronglyMeasurable φ (volume.restrict F) :=
    (hφ.1.continuousOn.mono hFH).aestronglyMeasurable hFm
  refine ⟨⟨hφmeas, ?_⟩, ?_⟩
  · have h1 : (∫⁻ z in F, ‖φ z‖ₑ) = phiArea φ F := by
      unfold phiArea
      simp_rw [ofReal_norm]
    show (∫⁻ z in F, ‖φ z‖ₑ) < ⊤
    rw [h1, hn]
    exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => norm_nonneg _) hφmeas.norm]
    have h1 : (∫⁻ z in F, ENNReal.ofReal ‖φ z‖) = 1 := hn
    rw [h1, ENNReal.toReal_one]

/-- `|∫_F κφ| ≤ c` for `|κ| ≤ c` a.e. on `F` and `φ` of area `1`. -/
theorem h36p_norm_pairing_le {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hn : phiArea φ F = 1) {κ : ℂ → ℂ} {c : ℝ}
    (hκ : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ c) :
    ‖beltramiPairing F κ φ‖ ≤ c := by
  obtain ⟨hφi, h1⟩ := h36p_integrableOn_of_unit hFH hFm hφ hn
  unfold beltramiPairing
  have h := norm_integral_le_of_norm_le (hφi.norm.const_mul c)
    (by
      filter_upwards [hκ] with z hz
      rw [norm_mul (κ z) (φ z)]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _))
  rw [integral_const_mul, h1, mul_one] at h
  exact h

/-- For `μ ∈ M(Γ)`, `|μ| ≤ ‖μ‖_∞` a.e. on every `F ⊆ ℍ`. -/
theorem h36p_ae_le_normH_F (μ : BeltramiGamma Γ) {F : Set ℂ} (hFH : F ⊆ upperHalf) :
    ∀ᵐ z ∂(volume.restrict F), ‖μ.1.1 z‖ ≤ beltramiNormH μ.1.1 :=
  ae_restrict_of_ae_restrict_of_subset hFH (c36_c_ae_le_normH μ.1)

/-- **The easy half of Hamilton's theorem**: `hamiltonNorm Γ F μ ≤ ‖μ‖_∞` (any measurable `F ⊆ ℍ`). -/
theorem h36p_hamiltonNorm_le {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) (μ : BeltramiGamma Γ) :
    hamiltonNorm Γ F μ.1.1 ≤ beltramiNormH μ.1.1 :=
  Real.iSup_le (fun _ => Real.iSup_le (fun hφ =>
    h36p_norm_pairing_le hFH hFm hφ.1 hφ.2 (h36p_ae_le_normH_F μ hFH)) (beltramiNormH_nonneg _))
    (beltramiNormH_nonneg _)

/-- Each admissible value lies below `hamiltonNorm`. -/
theorem h36p_le_hamiltonNorm {F : Set ℂ} (hFH : F ⊆ upperHalf) (hFm : MeasurableSet F) (μ : BeltramiGamma Γ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1) :
    ‖beltramiPairing F μ.1.1 φ‖ ≤ hamiltonNorm Γ F μ.1.1 := by
  have hbdd : BddAbove (range fun ψ : ℂ → ℂ =>
      ⨆ (_ : ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1), ‖beltramiPairing F μ.1.1 ψ‖) := by
    refine ⟨beltramiNormH μ.1.1, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact Real.iSup_le (fun hψ => h36p_norm_pairing_le hFH hFm hψ.1 hψ.2 (h36p_ae_le_normH_F μ hFH))
      (beltramiNormH_nonneg _)
  calc ‖beltramiPairing F μ.1.1 φ‖
      = ⨆ (_ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1), ‖beltramiPairing F μ.1.1 φ‖ :=
        (ciSup_pos (f := fun _ => ‖beltramiPairing F μ.1.1 φ‖) hφ).symm
    _ ≤ _ := le_ciSup hbdd φ

/-- A unimodular multiple of an admissible function is admissible. -/
theorem h36p_rotate_mem {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1)
    {u : ℂ} (hu : ‖u‖ = 1) :
    (fun z => u * φ z) ∈ integrableAutomorphicQD Γ F ∧ phiArea (fun z => u * φ z) F = 1 := by
  have harea : phiArea (fun z => u * φ z) F = phiArea φ F := by
    simp only [phiArea, norm_mul, hu, one_mul]
  refine ⟨⟨hφ.1.1.const_mul u, harea.trans_lt hφ.1.2.1, fun γ hγ z hz => ?_⟩, harea.trans hφ.2⟩
  have h := hφ.1.2.2 γ hγ z hz
  simp only
  rw [mul_div_assoc, h]

/-- The pairing is linear in `φ`: `∫_F κ (u φ) = u ∫_F κ φ`. -/
theorem h36p_pairing_smul (F : Set ℂ) (κ φ : ℂ → ℂ) (u : ℂ) :
    beltramiPairing F κ (fun z => u * φ z) = u * beltramiPairing F κ φ := by
  unfold beltramiPairing
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-- **Hamilton sequences from the Hamilton equality.**  If `hamiltonNorm Γ F μ = ‖μ‖_∞` and the unit
sphere of `integrableAutomorphicQD Γ F` is non-empty, there are `φₙ` of area `1` with
`∫_F μ φₙ → ‖μ‖_∞`. -/
theorem h36p_seq_of_hamilton {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    (hH : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1)
    (hA : ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1) ∧
      Tendsto (fun n => beltramiPairing F μ.1.1 (φ n)) atTop (𝓝 (beltramiNormH μ.1.1 : ℂ)) := by
  obtain ⟨hFH, hFm, -, -⟩ := hF
  set s := beltramiNormH μ.1.1 with hs
  rcases (beltramiNormH_nonneg μ.1.1).lt_or_eq with hpos | hzero
  · -- `s > 0`: approximate the supremum from below, then rotate
    have hex : ∀ n : ℕ, ∃ ψ : ℂ → ℂ, (ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1) ∧
        s - s / ((n : ℝ) + 2) < ‖beltramiPairing F μ.1.1 ψ‖ := by
      intro n
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hε : 0 < s / ((n : ℝ) + 2) := div_pos hpos hn2
      have hlt : s - s / ((n : ℝ) + 2) < hamiltonNorm Γ F μ.1.1 := by rw [hH]; linarith
      obtain ⟨ψ, hψ⟩ := exists_lt_of_lt_ciSup hlt
      by_cases hmem : ψ ∈ integrableAutomorphicQD Γ F ∧ phiArea ψ F = 1
      · rw [ciSup_pos hmem] at hψ
        exact ⟨ψ, hmem, hψ⟩
      · rw [ciSup_neg hmem, Real.sSup_empty] at hψ
        have hle : s / ((n : ℝ) + 2) ≤ s := div_le_self hpos.le (by linarith)
        exact absurd hψ (by linarith)
    choose ψ hψS hψ using hex
    have hε : Tendsto (fun n : ℕ => s / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hlow : Tendsto (fun n : ℕ => s - s / ((n : ℝ) + 2)) atTop (𝓝 s) := by
      simpa using (tendsto_const_nhds (x := s)).sub hε
    have hlim : Tendsto (fun n => ‖beltramiPairing F μ.1.1 (ψ n)‖) atTop (𝓝 s) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => (hψ n).le)
        (fun n => (h36p_le_hamiltonNorm hFH hFm μ (hψS n)).trans hH.le)
    choose u hu1 hu using fun n => exists_unit_mul_eq_norm (beltramiPairing F μ.1.1 (ψ n))
    refine ⟨fun n z => u n * ψ n z, fun n => h36p_rotate_mem (hψS n) (hu1 n), ?_⟩
    have e : ∀ n, beltramiPairing F μ.1.1 (fun z => u n * ψ n z) =
        ((‖beltramiPairing F μ.1.1 (ψ n)‖ : ℝ) : ℂ) := fun n => by
      rw [h36p_pairing_smul, hu n]
    simp only [e]
    exact (Complex.continuous_ofReal.tendsto _).comp hlim
  · -- `s = 0`: `μ = 0` a.e. on `F`, every admissible `φ` gives the pairing `0`
    obtain ⟨φ₀, hφ₀, h1⟩ := hA
    refine ⟨fun _ => φ₀, fun _ => ⟨hφ₀, h1⟩, ?_⟩
    have h0 : beltramiPairing F μ.1.1 φ₀ = 0 := by
      have hb := h36p_norm_pairing_le hFH hFm hφ₀ h1 (h36p_ae_le_normH_F μ hFH)
      rw [← hzero] at hb
      exact norm_le_zero_iff.1 hb
    have hs0 : ((s : ℝ) : ℂ) = 0 := by rw [hs, ← hzero, Complex.ofReal_zero]
    simp only [h0, hs0]
    exact tendsto_const_nhds

/-! ### R2: Corollary 36.1 from the Hamilton equality -/

/-! ### Local uniform bounds and the assembly of Corollary 36.1 -/

/-- **Local uniform bounds** for area-one automorphic `φ`: every `z ∈ ℍ` has a disc on which all such
`φ` are bounded by one constant (mean value + `h36p_local_L1`). -/
theorem h36p_local_bound (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1) :
    ∀ z ∈ upperHalf, ∃ δ > 0, ball z δ ⊆ upperHalf ∧ ∃ M : ℝ, ∀ n, ∀ w ∈ ball z δ, ‖φ n w‖ ≤ M := by
  intro z hz
  have hz' : 0 < z.im := hz
  obtain ⟨N, hN⟩ := h36p_local_L1 hΓ hF hz
  set δ : ℝ := z.im / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hsub : ∀ w ∈ ball z δ, closedBall w δ ⊆ closedBall z (z.im / 2) := by
    intro w hw
    refine closedBall_subset_closedBall' ?_
    rw [mem_ball] at hw
    linarith
  refine ⟨δ, hδ0, fun w hw => h36p_closedBall_sub hz (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hw), N / (π * δ ^ 2), fun n w hw => ?_⟩
  have hmv := h36p_meanvalue (hφ n).1.1 hδ0 ((hsub w hw).trans (h36p_closedBall_sub hz))
  have h2 : ∫⁻ v in ball w δ, ENNReal.ofReal ‖φ n v‖ ≤ N := by
    calc ∫⁻ v in ball w δ, ENNReal.ofReal ‖φ n v‖
        ≤ ∫⁻ v in closedBall z (z.im / 2), ENNReal.ofReal ‖φ n v‖ :=
          lintegral_mono_set (ball_subset_closedBall.trans (hsub w hw))
      _ ≤ N * phiArea (φ n) F := hN (φ n) (hφ n).1
      _ = N := by rw [(hφ n).2, mul_one]
  have h3 := hmv.trans h2
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)] at h3
  have hp : 0 < π * δ ^ 2 := by positivity
  rw [le_div_iff₀ hp]
  linarith

/-- If `hamiltonNorm Γ F κ > 0`, the unit sphere of `integrableAutomorphicQD Γ F` is non-empty. -/
theorem h36p_exists_unit_of_pos {F : Set ℂ} {κ : ℂ → ℂ} (h : 0 < hamiltonNorm Γ F κ) :
    ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1 := by
  by_contra hno
  push Not at hno
  have h0 : hamiltonNorm Γ F κ = 0 := by
    unfold hamiltonNorm
    have hz : ∀ φ : ℂ → ℂ, (⨆ (_ : φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1),
        ‖beltramiPairing F κ φ‖) = 0 := by
      intro φ
      have : IsEmpty (φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1) :=
        ⟨fun h => hno φ h.1 h.2⟩
      exact Real.iSup_of_isEmpty _
    simp_rw [hz]
    exact ciSup_const
  linarith

/-- **Corollary 36.1 from the Hamilton equality** (with the hypothesis `hvol : volume (F \ K) ≠ 0` of the
corrected `cor36_1`): if `hamiltonNorm Γ F μ = ‖μ‖_∞`, then `‖μ|_{F ∖ K}‖_∞ = ‖μ‖_∞` for every compact `K ⊆ F`
with `F ∖ K` of positive measure.  (Book proof: a Hamilton sequence would concentrate on `K`; a
normal-family limit `ψ` has `∬_K |ψ| = 1` and `ψ = 0` a.e. on `F ∖ K`, impossible for a holomorphic
`ψ ≢ 0`.)  Only the covering property of `F` is used. -/
theorem h36p_cor36_1_of_hamilton (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (hH : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1) {K : Set ℂ}
    (hK : IsCompact K) (hKF : K ⊆ F) (hvol : volume (F \ K) ≠ 0) :
    (essSup (fun z => (‖μ.1.1 z‖₊ : ℝ≥0∞)) (volume.restrict (F \ K))).toReal = beltramiNormH μ.1.1 := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -⟩ := hF'
  set κ : ℂ → ℂ := μ.1.1 with hκdef
  set k := beltramiNormH κ with hkdef
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hFKm : MeasurableSet (F \ K) := hFm.diff hKm
  have hFKH : F \ K ⊆ upperHalf := sdiff_subset.trans hFH
  have hKH : K ⊆ upperHalf := hKF.trans hFH
  set Ef := essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict (F \ K)) with hEf
  have hEH : essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) ≠ ⊤ :=
    beltramiH_essSup_ne_top μ.1
  have hle : Ef ≤ essSup (fun z => (‖κ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf) :=
    essSup_mono_measure' (Measure.restrict_mono hFKH le_rfl)
  have hEfne : Ef ≠ ⊤ := ne_top_of_le_ne_top hEH hle
  set e := Ef.toReal with he
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hek : e ≤ k := ENNReal.toReal_mono hEH hle
  refine le_antisymm hek (not_lt.1 fun hlt => ?_)
  -- the a.e. bounds `|κ| ≤ k` on `K` and `|κ| ≤ e` on `F ∖ K`
  have hbK : ∀ᵐ z ∂(volume.restrict K), ‖κ z‖ ≤ k := h36p_ae_le_normH_F μ hKH
  have hbFK : ∀ᵐ z ∂(volume.restrict (F \ K)), ‖κ z‖ ≤ e := by
    filter_upwards [ENNReal.ae_le_essSup (fun z => (‖κ z‖₊ : ℝ≥0∞))
      (μ := volume.restrict (F \ K))] with z hz
    rw [he, show ‖κ z‖ = ((‖κ z‖₊ : ℝ≥0∞)).toReal by simp]
    exact (ENNReal.toReal_le_toReal (by simp) hEfne).2 hz
  have hkpos : 0 < k := lt_of_le_of_lt he0 hlt
  have hA := h36p_exists_unit_of_pos (hH.symm ▸ hkpos : 0 < hamiltonNorm Γ F κ)
  obtain ⟨φ, hφS, hlim⟩ := h36p_seq_of_hamilton hF μ hH hA
  -- measurability and integrability
  obtain ⟨⟨k₀, -, -, hκmeas, hκbd⟩, -⟩ := μ.1.2
  rw [Measure.restrict_univ] at hκmeas hκbd
  have hκmF : AEStronglyMeasurable κ (volume.restrict F) := hκmeas.restrict
  have hκbF : ∀ᵐ z ∂(volume.restrict F), ‖κ z‖ ≤ k₀ := ae_restrict_of_ae hκbd
  have hint : ∀ n, IntegrableOn (φ n) F ∧ ∫ z in F, ‖φ n z‖ = 1 := fun n =>
    h36p_integrableOn_of_unit hFH hFm (hφS n).1 (hφS n).2
  set a : ℕ → ℝ := fun n => ∫ z in K, ‖φ n z‖ with ha
  set b : ℕ → ℝ := fun n => ∫ z in F \ K, ‖φ n z‖ with hb
  have hab : ∀ n, a n + b n = 1 := by
    intro n
    have h := integral_inter_add_sdiff hKm (hint n).1.norm
    rw [inter_eq_right.2 hKF, (hint n).2] at h
    exact h
  have hb0 : ∀ n, 0 ≤ b n := fun n => setIntegral_nonneg hFKm fun z _ => norm_nonneg _
  have ha1 : ∀ n, a n ≤ 1 := fun n => by linarith [hab n, hb0 n]
  -- `|∫_F κ φₙ| ≤ k aₙ + e bₙ`
  have hpair : ∀ n, ‖beltramiPairing F κ (φ n)‖ ≤ k * a n + e * b n := by
    intro n
    have hκφ : IntegrableOn (fun z => κ z * φ n z) F := (hint n).1.bdd_mul hκmF hκbF
    have h1 : ‖beltramiPairing F κ (φ n)‖ ≤ ∫ z in F, ‖κ z * φ n z‖ :=
      norm_integral_le_integral_norm _
    have h2 := integral_inter_add_sdiff hKm hκφ.norm
    rw [inter_eq_right.2 hKF] at h2
    have h3 : ∫ z in K, ‖κ z * φ n z‖ ≤ k * a n := by
      rw [ha, ← integral_const_mul]
      refine integral_mono_ae (IntegrableOn.mono_set hκφ.norm hKF)
        (((hint n).1.mono_set hKF).norm.const_mul k) ?_
      filter_upwards [hbK] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    have h4 : ∫ z in F \ K, ‖κ z * φ n z‖ ≤ e * b n := by
      rw [hb, ← integral_const_mul]
      refine integral_mono_ae (IntegrableOn.mono_set hκφ.norm sdiff_subset)
        (((hint n).1.mono_set sdiff_subset).norm.const_mul e) ?_
      filter_upwards [hbFK] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    linarith
  -- `aₙ → 1`, `bₙ → 0`
  have hlimN : Tendsto (fun n => ‖beltramiPairing F κ (φ n)‖) atTop (𝓝 k) := by
    have := hlim.norm
    rwa [Complex.norm_real, Real.norm_of_nonneg hkpos.le] at this
  have hke : 0 < k - e := by linarith
  have halim : Tendsto a atTop (𝓝 1) := by
    have hlow : Tendsto (fun n => (‖beltramiPairing F κ (φ n)‖ - e) / (k - e)) atTop (𝓝 1) := by
      have := (hlimN.sub_const e).div_const (k - e)
      rwa [div_self hke.ne'] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_) ha1
    rw [div_le_iff₀ hke]
    have := hpair n
    have hbn : b n = 1 - a n := by linarith [hab n]
    rw [hbn] at this
    nlinarith
  have hblim : Tendsto b atTop (𝓝 0) := by
    have hbe : b = fun n => 1 - a n := funext fun n => by linarith [hab n]
    rw [hbe]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub halim
  -- Montel
  obtain ⟨σ, hσ, g, hg, hconv⟩ := h35_montel_loc isOpen_upperHalf φ (fun n => (hφS n).1.1)
    (h36p_local_bound hΓ hF hφS)
  have hpt : ∀ z ∈ upperHalf, Tendsto (fun n => φ (σ n) z) atTop (𝓝 (g z)) := fun z hz =>
    hconv.tendsto_at hz
  -- `∫_K |g| = 1`
  have hunifK := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalf).1 hconv K hKH hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKH)
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  have hIntK : Tendsto (fun n => ∫ z in K, ‖φ (σ n) z‖) atTop (𝓝 (∫ z in K, ‖g z‖)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M + 1) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun n =>
        ((((hφS (σ n)).1.1.continuousOn.mono hKH).aestronglyMeasurable hKm)).norm
    · have hev := Metric.tendstoUniformlyOn_iff.1 hunifK 1 one_pos
      filter_upwards [hev] with n hn
      rw [ae_restrict_iff' hKm]
      refine Eventually.of_forall fun z hz => ?_
      have h1 := hn z hz
      rw [dist_eq_norm] at h1
      have h2 := hM z hz
      rw [norm_norm]
      have : ‖φ (σ n) z‖ ≤ ‖g z‖ + ‖g z - φ (σ n) z‖ := by
        calc ‖φ (σ n) z‖ = ‖g z - (g z - φ (σ n) z)‖ := by ring_nf
          _ ≤ ‖g z‖ + ‖g z - φ (σ n) z‖ := norm_sub_le _ _
      linarith
    · exact integrableOn_const hKfin.ne
    · rw [ae_restrict_iff' hKm]
      exact Eventually.of_forall fun z hz => ((hpt z (hKH hz)).norm)
  have hgK : ∫ z in K, ‖g z‖ = 1 :=
    tendsto_nhds_unique hIntK (halim.comp hσ.tendsto_atTop)
  -- Fatou on `F ∖ K`: `∫_{F∖K} |g| = 0`
  have hmeasn : ∀ n, AEMeasurable (fun z => ENNReal.ofReal ‖φ (σ n) z‖) (volume.restrict (F \ K)) :=
    fun n => (((hφS (σ n)).1.1.continuousOn.mono hFKH).aestronglyMeasurable hFKm).aemeasurable.norm
      |>.ennreal_ofReal
  have hlinb : ∀ n, ∫⁻ z in F \ K, ENNReal.ofReal ‖φ n z‖ = ENNReal.ofReal (b n) := by
    intro n
    rw [hb]
    exact (ofReal_integral_eq_lintegral_ofReal ((hint n).1.mono_set sdiff_subset).norm
      (Eventually.of_forall fun z => norm_nonneg _)).symm
  have hFatou : ∫⁻ z in F \ K, ENNReal.ofReal ‖g z‖ = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ z in F \ K, ENNReal.ofReal ‖g z‖
        = ∫⁻ z in F \ K, liminf (fun n => ENNReal.ofReal ‖φ (σ n) z‖) atTop := by
          refine setLIntegral_congr_fun hFKm fun z hz => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp ((hpt z (hFKH hz)).norm)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ z in F \ K, ENNReal.ofReal ‖φ (σ n) z‖) atTop :=
          lintegral_liminf_le' hmeasn
      _ = 0 := by
          simp_rw [hlinb]
          have : Tendsto (fun n => ENNReal.ofReal (b (σ n))) atTop (𝓝 0) := by
            have := (ENNReal.continuous_ofReal.tendsto _).comp (hblim.comp hσ.tendsto_atTop)
            simpa [Function.comp_def] using this
          exact this.liminf_eq
  have hgFK : ∀ᵐ z ∂(volume.restrict (F \ K)), g z = 0 := by
    have hgm : AEMeasurable (fun z => ENNReal.ofReal ‖g z‖) (volume.restrict (F \ K)) :=
      ((hg.continuousOn.mono hFKH).aestronglyMeasurable hFKm).aemeasurable.norm.ennreal_ofReal
    filter_upwards [(lintegral_eq_zero_iff' hgm).1 hFatou] with z hz
    have : ‖g z‖ ≤ 0 := ENNReal.ofReal_eq_zero.1 hz
    exact norm_le_zero_iff.1 this
  -- `g ≢ 0` on `ℍ`, so `g ≠ 0` a.e. on `F ∖ K`: contradiction with `volume (F ∖ K) ≠ 0`
  have hne : ¬ EqOn g 0 upperHalf := by
    intro h0
    have : ∫ z in K, ‖g z‖ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [h0 (hKH hz)]; simp
    rw [hgK] at this
    exact one_ne_zero this
  have hnz := ae_ne_zero_of_differentiableOn_upperHalf hg hne hFKH hFKm
  have hfalse : ∀ᵐ z ∂(volume.restrict (F \ K)), False := by
    filter_upwards [hgFK, hnz] with z h1 h2
    exact h2 h1
  have hzero : volume.restrict (F \ K) = 0 := by
    rw [← ae_eq_bot]
    exact Filter.eventually_false_iff_eq_bot.1 hfalse
  exact hvol (Measure.restrict_eq_zero.1 hzero)

/-! ### R3: the finite type case from the Hamilton equality (with the corrected `hfin`) -/

/-- `h36p_m γ⁻¹` inverts `h36p_m γ` on `ℍ`. -/
theorem h36p_m_inv_m (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_m γ⁻¹ (h36p_m γ z) = z := by
  have e1 := h36p_m_coe γ ⟨z, hz⟩
  simp only at e1
  have e2 := h36p_m_coe γ⁻¹ (γ • (⟨z, hz⟩ : UpperHalfPlane))
  rw [e1, e2, inv_smul_smul]

/-- The pointwise algebra behind the invariance of `k φ̄/|φ|`: with `φ(γz) = φ(z) q⁴`,
`k \overline{φ(γz)}/|φ(γz)| · q²/\overline{q²} = k φ̄(z)/|φ(z)|`. -/
theorem h36p_teich_transform (c : ℝ) (p q : ℂ) (hq : q ≠ 0) :
    (c : ℂ) * conj (p * q ^ 4) / (‖p * q ^ 4‖ : ℂ) * (q ^ 2 / conj (q ^ 2)) =
      (c : ℂ) * conj p / (‖p‖ : ℂ) := by
  by_cases hp : p = 0
  · simp [hp]
  have hqc : conj q ≠ 0 := (map_ne_zero _).2 hq
  have hpn : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hp
  have hqn : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hq
  have hqq : conj q * q = (‖q‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have key : conj q ^ 2 * q ^ 2 = (‖q‖ : ℂ) ^ 4 := by
    rw [← mul_pow, hqq]; ring
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow]
  push_cast
  rw [div_mul_div_comm, div_eq_div_iff (by simp [hpn, hqn, hqc]) hpn]
  linear_combination (c : ℂ) * conj p * (‖p‖ : ℂ) * conj q ^ 2 * key

/-- **Extension from `F` to `ℍ`**: if `μ = c φ̄/|φ|` a.e. on `F` (with `μ ∈ M(Γ)`, `φ` automorphic), the
same holds a.e. on `ℍ` (the translates of `F` cover `ℍ`; only the covering property of `F` is used). -/
theorem h36p_ae_extend (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (c : ℝ)
    (h : ∀ᵐ z ∂(volume.restrict F), μ.1.1 z = c * conj (φ z) / ‖φ z‖) :
    ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = c * conj (φ z) / ‖φ z‖ := by
  obtain ⟨hFH, hFm, hcov, -⟩ := hF
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  set P : ℂ → Prop := fun z => μ.1.1 z = c * conj (φ z) / ‖φ z‖ with hPdef
  have hcover : upperHalf ⊆ ⋃ γ : Γ, (upperHalf ∩ h36p_m γ ⁻¹' F) := by
    intro w hw
    obtain ⟨γ, hγ, hγF⟩ := hcov ⟨w, hw⟩
    refine mem_iUnion.2 ⟨⟨γ, hγ⟩, hw, ?_⟩
    show h36p_m γ w ∈ F
    have := h36p_m_coe γ ⟨w, hw⟩
    simp only at this
    rw [this]
    exact hγF
  refine ae_restrict_of_ae_restrict_of_subset hcover ?_
  rw [ae_restrict_iUnion_iff]
  intro γ
  set g : Matrix.SpecialLinearGroup (Fin 2) ℝ := (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) with hg
  have hE : MeasurableSet (upperHalf ∩ h36p_m g ⁻¹' F) :=
    isOpen_upperHalf.measurableSet.inter (h36p_m_measurable g hFm)
  -- the Γ-compatibility of `μ` at `g`
  have hcomp := μ.2 g γ.2
  -- `P ∘ h36p_m g` holds a.e. on `ℍ ∩ g⁻¹(F)`
  have hpull : ∀ᵐ z ∂(volume.restrict (upperHalf ∩ h36p_m g ⁻¹' F)), P (h36p_m g z) := by
    rw [ae_restrict_iff' hFm] at h
    rw [ae_iff] at h
    set N := {w : ℂ | ¬ (w ∈ F → P w)} with hN
    have hN0 : volume (N ∩ upperHalf) = 0 := measure_mono_null inter_subset_left h
    have hdiff : DifferentiableOn ℝ (h36p_m g⁻¹) (N ∩ upperHalf) := fun w hw =>
      ((h36p_m_hasDerivAt g⁻¹ hw.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt
    have himg : volume (h36p_m g⁻¹ '' (N ∩ upperHalf)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hN0
    rw [ae_restrict_iff' hE]
    refine measure_mono_null ?_ himg
    intro z hz
    have hz' : ¬ (z ∈ upperHalf ∩ h36p_m g ⁻¹' F → P (h36p_m g z)) := hz
    obtain ⟨⟨hzH, hzF⟩, hnot⟩ := not_imp.1 hz'
    refine ⟨h36p_m g z, ⟨fun hF' => hnot ?_, h36p_m_mem g hzH⟩, h36p_m_inv_m g hzH⟩
    exact hF' hzF
  filter_upwards [hpull, ae_restrict_of_ae_restrict_of_subset inter_subset_left hcomp,
    ae_restrict_mem hE] with z hz hcz hzE
  have hzH : z ∈ upperHalf := hzE.1
  have hdet := b33_d_det g
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hzH))
  have hA := hφ.2.2 g γ.2 z hzH
  have hφm : φ (h36p_m g z) = φ z * ((g 1 0 : ℂ) * z + g 1 1) ^ 4 := by
    rw [← hA, div_mul_cancel₀ _ (pow_ne_zero _ hden)]
    rfl
  show μ.1.1 z = c * conj (φ z) / ‖φ z‖
  rw [hcz]
  change μ.1.1 (h36p_m g z) * _ = _
  rw [hz, hφm]
  exact h36p_teich_transform c (φ z) _ hden

/-- `integrableAutomorphicQD Γ F` is closed under addition. -/
theorem h36p_A_add {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf) {φ ψ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hψ : ψ ∈ integrableAutomorphicQD Γ F) :
    φ + ψ ∈ integrableAutomorphicQD Γ F := by
  refine ⟨hφ.1.add hψ.1, ?_, fun γ hγ z hz => ?_⟩
  · have hle : phiArea (φ + ψ) F ≤ phiArea φ F + phiArea ψ F := by
      unfold phiArea
      rw [← lintegral_add_left' (((hφ.1.continuousOn.mono hFH).aestronglyMeasurable
        hFm).aemeasurable.norm.ennreal_ofReal)]
      refine lintegral_mono fun z => ?_
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hφ.2.1, hψ.2.1⟩)
  · simp only [Pi.add_apply]
    rw [add_div, hφ.2.2 γ hγ z hz, hψ.2.2 γ hγ z hz]

/-- `integrableAutomorphicQD Γ F` is closed under scalar multiplication. -/
theorem h36p_A_smul {F : Set ℂ} {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (a : ℂ) :
    a • φ ∈ integrableAutomorphicQD Γ F := by
  refine ⟨hφ.1.const_smul a, ?_, fun γ hγ z hz => ?_⟩
  · have : phiArea (a • φ) F = ENNReal.ofReal ‖a‖ * phiArea φ F := by
      unfold phiArea
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun z => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    rw [this]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.2.1
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, hφ.2.2 γ hγ z hz]

/-- `0 ∈ integrableAutomorphicQD Γ F`. -/
theorem h36p_A_zero {F : Set ℂ} : (0 : ℂ → ℂ) ∈ integrableAutomorphicQD Γ F :=
  ⟨differentiableOn_const 0, by simp [phiArea], fun _ _ _ _ => by simp⟩

/-- Every element of the span of `{𝟙_ℍ φ | φ ∈ integrableAutomorphicQD Γ F}` is of this form. -/
theorem h36p_span_indicator {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf) {v : ℂ → ℂ}
    (hv : v ∈ Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ F)) :
    ∃ φ ∈ integrableAutomorphicQD Γ F, v = upperHalf.indicator φ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    exact ⟨φ, hφ, rfl⟩
  | zero => exact ⟨0, h36p_A_zero, (indicator_zero _ _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    obtain ⟨ψ, hψ, rfl⟩ := hy
    exact ⟨φ + ψ, h36p_A_add hFm hFH hφ hψ, (indicator_add' _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    refine ⟨a • φ, h36p_A_smul hφ a, ?_⟩
    funext x
    by_cases hx : x ∈ upperHalf <;> simp [hx]

/-- An element of the span is integrable on `F`. -/
theorem h36p_span_integrable {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    (v : Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ F)) :
    Integrable (v : ℂ → ℂ) (volume.restrict F) := by
  obtain ⟨φ, hφ, hv⟩ := h36p_span_indicator hFm hFH v.2
  have hφi : IntegrableOn φ F := by
    refine ⟨(hφ.1.continuousOn.mono hFH).aestronglyMeasurable hFm, ?_⟩
    have h1 : (∫⁻ z in F, ‖φ z‖ₑ) = phiArea φ F := by
      unfold phiArea
      simp_rw [ofReal_norm]
    show (∫⁻ z in F, ‖φ z‖ₑ) < ⊤
    rw [h1]
    exact hφ.2.1
  refine hφi.congr_fun (fun z hz => ?_) hFm
  rw [hv, indicator_of_mem (hFH hz)]

/-- **The finite type case from the Hamilton equality**, with the corrected `hfin`:
finite-dimensionality of `A(S)` is asked of the restrictions `𝟙_ℍ φ` (the values of `φ` off `ℍ` are
irrelevant).  A Hamilton sequence has an `L¹(F)`-convergent subsequence (compact unit sphere of the
finite-dimensional image in `L¹(F)`); its limit `φ` attains `∫_F μ φ = ‖μ‖_∞`, whence `μ = k φ̄/|φ|`
a.e. on `F` (`pairing_eq_norm_imp_teichmuller`) and on `ℍ` (`h36p_ae_extend`). -/
theorem h36p_finite_type_of_hamilton (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (hfin : Module.Finite ℂ
      (Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ F)))
    (μ : BeltramiGamma Γ) (hH : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1) :
    (μ.1.1 =ᵐ[volume.restrict upperHalf] 0) ∨
      ∃ φ : ℂ → ℂ, φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1 ∧
        beltramiPairing F μ.1.1 φ = beltramiNormH μ.1.1 ∧
        ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = beltramiNormH μ.1.1 * conj (φ z) / ‖φ z‖ := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -⟩ := hF'
  set κ : ℂ → ℂ := μ.1.1 with hκdef
  set k := beltramiNormH κ with hkdef
  rcases (beltramiNormH_nonneg κ).lt_or_eq with hkpos | hk0
  swap
  · -- `k = 0`: `μ = 0` a.e. on `ℍ`
    left
    filter_upwards [c36_c_ae_le_normH μ.1] with z hz
    have hz' : ‖κ z‖ ≤ 0 := by rw [hk0]; exact hz
    simpa using norm_le_zero_iff.1 hz'
  right
  have hA := h36p_exists_unit_of_pos (hH.symm ▸ hkpos : 0 < hamiltonNorm Γ F κ)
  obtain ⟨φ, hφS, hlim⟩ := h36p_seq_of_hamilton hF μ hH hA
  -- the finite-dimensional image of the span in `L¹(F)`
  set V := Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ F) with hV
  let L : V →ₗ[ℂ] Lp ℂ 1 (volume.restrict F) :=
    { toFun := fun v => (h36p_span_integrable hFm hFH v).toL1 _
      map_add' := fun v w => by
        rw [← Integrable.toL1_add]
        rfl
      map_smul' := fun a v => by
        rw [RingHom.id_apply, ← Integrable.toL1_smul]
        rfl }
  set W := LinearMap.range L with hW
  have : FiniteDimensional ℂ V := hfin
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range L
  -- the Hamilton sequence in `W`
  have hmemV : ∀ n, upperHalf.indicator (φ n) ∈ V := fun n =>
    Submodule.subset_span ⟨φ n, (hφS n).1, rfl⟩
  set u : ℕ → W := fun n => ⟨L ⟨_, hmemV n⟩, LinearMap.mem_range_self L _⟩ with hu
  have hint : ∀ n, IntegrableOn (φ n) F ∧ ∫ z in F, ‖φ n z‖ = 1 := fun n =>
    h36p_integrableOn_of_unit hFH hFm (hφS n).1 (hφS n).2
  have hu_ae : ∀ n, ((u n : Lp ℂ 1 (volume.restrict F)) : ℂ → ℂ) =ᵐ[volume.restrict F] φ n := by
    intro n
    have h1 := (h36p_span_integrable hFm hFH ⟨_, hmemV n⟩).coeFn_toL1
    filter_upwards [h1, ae_restrict_mem hFm] with z hz hzF
    change (((h36p_span_integrable hFm hFH ⟨_, hmemV n⟩).toL1 _ : Lp ℂ 1 (volume.restrict F)) :
      ℂ → ℂ) z = φ n z
    rw [hz]
    exact indicator_of_mem (hFH hzF) _
  have hu_norm : ∀ n, ‖u n‖ = 1 := by
    intro n
    rw [← Submodule.norm_coe, L1.norm_eq_integral_norm, ← (hint n).2]
    exact integral_congr_ae (by filter_upwards [hu_ae n] with z hz; rw [hz])
  -- a convergent subsequence
  obtain ⟨u₀, -, σ, hσ, hconv⟩ := (isCompact_closedBall (0 : W) 1).tendsto_subseq
    (x := u) fun n => by rw [mem_closedBall, dist_zero_right, hu_norm n]
  have hu₀ : ‖u₀‖ = 1 := by
    have := (continuous_norm.tendsto u₀).comp hconv
    simp only [Function.comp_def, hu_norm] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- the pairing functional on `L¹(F)`
  obtain ⟨⟨k₀, -, -, hκmeas, hκbd⟩, -⟩ := μ.1.2
  rw [Measure.restrict_univ] at hκmeas hκbd
  obtain ⟨ℓ, hℓ⟩ := h35a_exists_mul_functional (μ := volume.restrict F) (κ := κ) (C := k₀)
    hκmeas.restrict (ae_restrict_of_ae hκbd)
  have hℓu : ∀ n, ℓ (u n) = beltramiPairing F κ (φ n) := by
    intro n
    rw [hℓ]
    exact integral_congr_ae (by filter_upwards [hu_ae n] with z hz; rw [hz])
  have hℓlim : Tendsto (fun n => ℓ (u (σ n))) atTop (𝓝 (ℓ u₀)) :=
    (ℓ.continuous.comp continuous_subtype_val).continuousAt.tendsto.comp hconv
  have hℓk : ℓ u₀ = (k : ℂ) := by
    refine tendsto_nhds_unique hℓlim ?_
    simp only [hℓu]
    exact hlim.comp hσ.tendsto_atTop
  -- the limit is a quadratic differential of norm one attaining `k`
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 u₀.2
  obtain ⟨ψ, hψ, hvψ⟩ := h36p_span_indicator hFm hFH v.2
  have hu₀ae : ((u₀ : Lp ℂ 1 (volume.restrict F)) : ℂ → ℂ) =ᵐ[volume.restrict F] ψ := by
    rw [← hv]
    have h1 := (h36p_span_integrable hFm hFH v).coeFn_toL1
    filter_upwards [h1, ae_restrict_mem hFm] with z hz hzF
    change ((h36p_span_integrable hFm hFH v).toL1 _ : ℂ → ℂ) z = ψ z
    rw [hz, hvψ]
    exact indicator_of_mem (hFH hzF) _
  have hψint : ∫ z in F, ‖ψ z‖ = 1 := by
    rw [← hu₀, ← Submodule.norm_coe, L1.norm_eq_integral_norm]
    exact (integral_congr_ae (by filter_upwards [hu₀ae] with z hz; rw [hz])).symm
  have hψi : IntegrableOn ψ F := by
    have := L1.integrable_coeFn (u₀ : Lp ℂ 1 (volume.restrict F))
    exact this.congr hu₀ae
  have hψn : phiArea ψ F = 1 := by
    unfold phiArea
    rw [← ofReal_integral_eq_lintegral_ofReal hψi.norm (Eventually.of_forall fun z => norm_nonneg _),
      hψint, ENNReal.ofReal_one]
  have hψpair : beltramiPairing F κ ψ = k := by
    rw [← hℓk, hℓ]
    exact (integral_congr_ae (by filter_upwards [hu₀ae] with z hz; rw [hz])).symm
  refine ⟨ψ, hψ, hψn, hψpair, ?_⟩
  exact h36p_ae_extend hΓ hF μ hψ k (pairing_eq_norm_imp_teichmuller hF μ hψ hψn hψpair)

/-! ### C.3 Proved glue for `thm36_2_hamilton` -/

/-- `τ(ν, 0) ≤ artanh ‖ν‖_∞` (the reverse of `artanh_beltramiNormH_le`): `τ(ν, 0) = ‖artanh |ν|‖_∞`
(`beltramiPoincareDist_zero_eq`) and `artanh |ν(z)| ≤ artanh ‖ν‖_∞` a.e. -/
theorem h36p_tau_zero_le (ν : BeltramiH) : beltramiPoincareDist ν.1 0 ≤ Real.artanh (beltramiNormH ν.1) := by
  rw [beltramiPoincareDist_zero_eq ν]
  have hk0 := beltramiNormH_nonneg ν.1
  have hk1 := beltramiNormH_lt_one ν
  have hkI : beltramiNormH ν.1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hk1⟩
  have hart : 0 ≤ Real.artanh (beltramiNormH ν.1) := by
    have h := (Real.artanh_le_artanh_iff (x := 0) ⟨by norm_num, by norm_num⟩ hkI).2 hk0
    rwa [Real.artanh_zero] at h
  refine ENNReal.toReal_le_of_le_ofReal hart (essSup_le_of_ae_le _ ?_)
  filter_upwards [ae_norm_le_beltramiNormH (beltramiH_essSup_ne_top ν)] with z hz
  exact ENNReal.ofReal_le_ofReal
    ((Real.artanh_le_artanh_iff ⟨by linarith [norm_nonneg (ν.1 z)], hz.trans_lt hk1⟩ hkI).2 hz)

/-- **Theorem 36.2 (Hamilton)**: if `f₀ : S → S₁` is extremal in its class modulo the boundary and `κ`
is its complex dilatation, then `sup_{‖ω‖=1} |∫_S κω| = ‖κ‖_∞`, `ω` ranging over the holomorphic
quadratic differentials of `L¹`-norm `1`. -/
theorem thm36_2_hamilton (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) : hamiltonNorm Γ F μ.1.1 = beltramiNormH μ.1.1 := by
  refine le_antisymm (h36p_hamiltonNorm_le hF.1 hF.2.1 μ) (not_lt.1 fun hlt => ?_)
  obtain ⟨π', hπ', hτ⟩ := hamilton_contradiction hΓ hF μ hlt
  obtain ⟨μ', hrel, hμ'⟩ := h36p_translate μ π' hπ'
  have h1 : beltramiNormH μ.1.1 ≤ beltramiNormH μ'.1.1 := hμ μ' hrel
  have h2 := h36p_tau_zero_le μ.1
  have ha0 : 0 ≤ beltramiNormH μ'.1.1 := beltramiNormH_nonneg _
  have hk0 : 0 ≤ beltramiNormH μ.1.1 := beltramiNormH_nonneg _
  have haI : beltramiNormH μ'.1.1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, beltramiNormH_lt_one μ'.1⟩
  have hkI : beltramiNormH μ.1.1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, beltramiNormH_lt_one μ.1⟩
  have htI : Real.tanh (beltramiPoincareDist μ.1.1 π'.1.1) ∈ Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have h3 : Real.artanh (beltramiNormH μ'.1.1) ≤ beltramiPoincareDist μ.1.1 π'.1.1 := by
    have h := (Real.artanh_le_artanh_iff haI htI).2 hμ'
    rwa [Real.artanh_tanh] at h
  have h4 : Real.artanh (beltramiNormH μ'.1.1) < Real.artanh (beltramiNormH μ.1.1) := by linarith
  have h5 := (Real.artanh_lt_artanh_iff haI hkI).1 h4
  linarith

-- strebel_hamilton_sufficient is stated and proved in LiZhongQC/Lemmas/S36StrebelFinal.lean
-- (it uses the complete group Strebel proof downstream of this file).

/-- §36.2: Hamilton's theorem gives a sequence `ωₙ ∈ A(S)`, `‖ωₙ‖ = 1`, with `∫_S κωₙ → ‖κ‖_∞`
(a Hamilton sequence).

**Correction.**  The hypothesis `hA` (`A(Γ) ≠ 0`) was missing: for `μ = 0` and a group without
integrable automorphic forms (e.g. `SL(2, ℤ)`) no unit `φ` exists. -/
theorem hamilton_sequence_exists (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (μ : BeltramiGamma Γ) (hμ : IsExtremalModBoundary Γ μ)
    (hA : ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, φ n ∈ integrableAutomorphicQD Γ F ∧ phiArea (φ n) F = 1) ∧
      Tendsto (fun n => beltramiPairing F μ.1.1 (φ n)) atTop (𝓝 (beltramiNormH μ.1.1 : ℂ)) := by
  exact h36p_seq_of_hamilton hF μ (thm36_2_hamilton hΓ hF μ hμ) hA

/-- §36.2 (the finite type case): when `S` is a compact surface minus finitely many points, `A(S)`
(differentials with at most simple poles at the punctures) is finite dimensional, a Hamilton
sequence has a norm-convergent subsequence with limit `ω`, `∫_S κω = ‖κ‖_∞`, and then
`κ = k ω̄/|ω|`, `k = ‖κ‖_∞`: Teichmüller's theorem.

**Correction.**  `hfin` asked for finiteness of the span of `integrableAutomorphicQD Γ F`, whose elements
are unconstrained off `ℍ`, so it never held and the theorem was **vacuous**; it now concerns the
restrictions `𝟙_ℍ φ`. -/
theorem thm36_2_finite_type (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (hfin : Module.Finite ℂ (Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ F)))
    (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) :
    (μ.1.1 =ᵐ[volume.restrict upperHalf] 0) ∨
      ∃ φ : ℂ → ℂ, φ ∈ integrableAutomorphicQD Γ F ∧ phiArea φ F = 1 ∧
        beltramiPairing F μ.1.1 φ = beltramiNormH μ.1.1 ∧
        ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = beltramiNormH μ.1.1 * conj (φ z) / ‖φ z‖ := by
  have _hfree := hfree
  exact h36p_finite_type_of_hamilton hΓ hF hfin μ (thm36_2_hamilton hΓ hF μ hμ)

/-- **Corollary 36.1**: if `κ` is the complex dilatation of an extremal map `f₀ : S → S₁`, then for
every compact `K ⊆ S`, `‖κ|_{S ∖ K}‖_∞ = ‖κ‖_∞`: the local dilatation of an extremal map cannot be
everywhere smaller than `K[f₀] - ε` near the boundary.

**Correction.**  The hypothesis `hvol : volume (F \ K) ≠ 0` was missing: for a compact surface one may
take `K = F`, where the left side is `0`. -/
theorem cor36_1 (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) {K : Set ℂ} (hK : IsCompact K) (hKF : K ⊆ F) (hvol : volume (F \ K) ≠ 0) :
    (essSup (fun z => (‖μ.1.1 z‖₊ : ℝ≥0∞)) (volume.restrict (F \ K))).toReal = beltramiNormH μ.1.1 := by
  exact h36p_cor36_1_of_hamilton hΓ hF μ (thm36_2_hamilton hΓ hF μ hμ) hK hKF hvol

end LiZhongQC
