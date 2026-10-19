import References.GardinerLakic2000.Ch06.S05_InfinitesimalTheory

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.6 Infinitesimally trivial Beltrami differentials

Source `teichmuller.txt`, lines 5957–5995.

* Definition (`M₀(G)`, the trivial Beltrami coefficients, l. 5958) — exists: `LiZhongQC.IsTrivialBeltrami` (the
  bridge of Definition 5.6: w_μ|ℝ = id in the book, w^μ|ℝ = id in the project, the same set by
  `LiZhongQC.lemma33_1` with μ₂ = 0)
* Definition (`N(G)`, the infinitesimally trivial Beltrami differentials, l. 5958) — exists:
  `GardinerLakic2000.nSpaceGamma`
* Theorem 6 (`N(G)` is the tangent space of `M₀(G)` at `0`, l. 5962) — `thm6_6`

[misprint] the proof (l. 5964) says "(4.26) in the case `K₀ = 0`": `K₀ = 1`; the statement is not affected.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (BeltramiGamma upperHalf IsFundamentalDomainH IsFuchsian IsTrivialBeltrami)

/-- Helper for Theorem 6. A Lipschitz bound for the Bers map at a point `w ∈ 𝕃` near `0`: if `|α|, |η| ≤ 1/4`
a.e. and `0 ≤ s < 1`, then `|Φ(α + sη)(w) − Φ(α)(w)| ≤ (9/2) y⁻² s` (`t ↦ Φ(α + tη)(w)` is holomorphic on the unit
disc, `b36_q_schwarzian_holo`, and bounded by `(3/2) y⁻²`, `bB_sd_kraus_pt`; the Schwarz lemma
`Complex.dist_le_div_mul_dist_of_mapsTo_ball`). -/
theorem gl6_bers_lipschitz (α η : LiZhongQC.BeltramiH) (hα : ∀ᵐ z, ‖α.1 z‖ ≤ 1 / 4) (hη : ∀ᵐ z, ‖η.1 z‖ ≤ 1 / 4)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {w : ℂ} (hw : w ∈ LiZhongQC.lowerHalf) :
    ‖LiZhongQC.bersFunction (fun z => α.1 z + (s : ℂ) * η.1 z) w - LiZhongQC.bersFunction α.1 w‖ ≤
      9 / 2 * (w.im ^ 2)⁻¹ * s := by
  have hb : ∀ t ∈ ball (0 : ℂ) 1, LiZhongQC.IsBeltramiCoeff (fun z => α.1 z + t * η.1 z) univ (1 / 2) := by
    intro t ht
    obtain ⟨⟨_, -, -, hmα, -⟩, -⟩ := α.2
    obtain ⟨⟨_, -, -, hmη, -⟩, -⟩ := η.2
    refine ⟨hmα.add (hmη.const_mul t), ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [hα, hη] with z h1 h2
    have ht1 : ‖t‖ ≤ 1 := (mem_ball_zero_iff.1 ht).le
    calc ‖α.1 z + t * η.1 z‖ ≤ ‖α.1 z‖ + ‖t‖ * ‖η.1 z‖ := by
          rw [← norm_mul]
          exact norm_add_le _ _
      _ ≤ 1 / 4 + 1 * (1 / 4) := add_le_add h1 (mul_le_mul ht1 h2 (norm_nonneg _) zero_le_one)
      _ = 1 / 2 := by norm_num
  have hk0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hk1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨hkP, hhol⟩ := LiZhongQC.b36_q_fam_hyps α η hk0 hk1 hb
  have hbers : ∀ t ∈ ball (0 : ℂ) 1, LiZhongQC.bersFunction (fun z => α.1 z + t * η.1 z) w =
      LiZhongQC.schwarzian (LiZhongQC.normalizedSolution (LiZhongQC.b36_q_fam α η t).1) w := by
    intro t ht
    rw [← LiZhongQC.b36_q_fam_val α η hk0 hk1 hb ht]
    exact indicator_of_mem hw _
  have hy : 0 < w.im ^ 2 := by
    have h : w.im < 0 := hw
    nlinarith
  have hM0 : 0 < 3 / 2 * (w.im ^ 2)⁻¹ := mul_pos (by norm_num) (inv_pos.2 hy)
  have hgd : DifferentiableOn ℂ (fun t => LiZhongQC.bersFunction (fun z => α.1 z + t * η.1 z) w) (ball 0 1) :=
    (LiZhongQC.b36_q_schwarzian_holo isOpen_ball hk0 hk1 hkP hhol hw).congr fun t ht => hbers t ht
  have hgM : ∀ t ∈ ball (0 : ℂ) 1,
      ‖LiZhongQC.bersFunction (fun z => α.1 z + t * η.1 z) w‖ ≤ 3 / 2 * (w.im ^ 2)⁻¹ := by
    intro t ht
    have h := LiZhongQC.bB_sd_kraus_pt (LiZhongQC.b36_q_fam α η t) hw
    rw [hbers t ht, le_mul_inv_iff₀ hy]
    exact h
  have hg0 : LiZhongQC.bersFunction (fun z => α.1 z + (0 : ℂ) * η.1 z) w = LiZhongQC.bersFunction α.1 w := by
    have e : (fun z => α.1 z + (0 : ℂ) * η.1 z) = α.1 := by
      funext z
      rw [zero_mul, add_zero]
    rw [e]
  have hmaps : MapsTo (fun t => LiZhongQC.bersFunction (fun z => α.1 z + t * η.1 z) w) (ball 0 1)
      (closedBall (LiZhongQC.bersFunction (fun z => α.1 z + (0 : ℂ) * η.1 z) w) (3 * (3 / 2 * (w.im ^ 2)⁻¹))) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    calc _ ≤ ‖LiZhongQC.bersFunction (fun z => α.1 z + t * η.1 z) w‖ +
          ‖LiZhongQC.bersFunction (fun z => α.1 z + (0 : ℂ) * η.1 z) w‖ := norm_sub_le _ _
      _ ≤ 3 / 2 * (w.im ^ 2)⁻¹ + 3 / 2 * (w.im ^ 2)⁻¹ :=
          add_le_add (hgM t ht) (hgM 0 (mem_ball_self one_pos))
      _ ≤ 3 * (3 / 2 * (w.im ^ 2)⁻¹) := by linarith
  have hsb : (s : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact hs1
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps hsb
  rw [dist_eq_norm, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_of_nonneg hs0, div_one, hg0] at h
  calc _ ≤ _ := h
    _ = 9 / 2 * (w.im ^ 2)⁻¹ * s := by ring

/-- Helper for Theorem 6 (⇐). If a curve `σ_t` of trivial coefficients satisfies `σ_t = (t/λ) ν₀ + O(t²)` a.e. on
`ℍ`, then `Φ̇[ν₀] = 0` on `𝕃`: `|Φ(u ν₀)(w)| = |Φ(u ν₀)(w) − Φ(σ_{λu})(w)| = O(u²)` (`gl6_bers_lipschitz`,
`Φ(σ_t) = 0` by `lemma36_2_trivial_iff`), while `u ↦ Φ(u ν₀)(w)` has derivative `Φ̇[ν₀](w)` at `0`. -/
theorem gl6_bersDerivative_eq_zero {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (ν₀ : BeltramiGamma Γ) (hν₀ : ∀ᵐ z, ‖ν₀.1.1 z‖ ≤ 1 / 2) {lam δ C : ℝ} (hlam : 0 < lam) (hδ : 0 < δ)
    (σ : ℝ → BeltramiGamma Γ) (hσT : ∀ t, |t| < δ → IsTrivialBeltrami Γ (σ t))
    (hσB : ∀ t, |t| < δ → ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖(σ t).1.1 z - ((t / lam : ℝ) : ℂ) * ν₀.1.1 z‖ ≤ C * t ^ 2)
    {w : ℂ} (hw : w ∈ LiZhongQC.lowerHalf) : LiZhongQC.bersDerivative ν₀.1.1 w = 0 := by
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  obtain ⟨⟨_, -, -, hν₀m, -⟩, hν₀0⟩ := ν₀.1.2
  rw [Measure.restrict_univ] at hν₀m
  have hy : 0 < w.im ^ 2 := by
    have h : w.im < 0 := hw
    nlinarith
  set K : ℝ := 18 * (w.im ^ 2)⁻¹ * ((|C| + 1) * lam ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set ρ : ℝ := min (δ / lam) (min (1 / 2) (1 / (4 * ((|C| + 1) * lam ^ 2)))) with hρ
  have hρ0 : 0 < ρ := lt_min (div_pos hδ hlam) (lt_min (by norm_num) (by positivity))
  -- the quadratic bound
  have hquad : ∀ u : ℝ, |u| < ρ →
      ‖LiZhongQC.bersFunction (fun z => ((u : ℝ) : ℂ) * ν₀.1.1 z) w‖ ≤ K * u ^ 2 := by
    intro u hu
    rw [hρ, lt_min_iff, lt_min_iff] at hu
    obtain ⟨hu1, hu2, hu3⟩ := hu
    by_cases hu0 : u = 0
    · have e : (fun z => ((u : ℝ) : ℂ) * ν₀.1.1 z) = (0 : ℂ → ℂ) := by
        funext z
        rw [hu0, ofReal_zero, zero_mul]
        rfl
      have e1 : LiZhongQC.bersFunction (0 : ℂ → ℂ) w = LiZhongQC.schwarzian (LiZhongQC.normalizedSolution 0) w :=
        indicator_of_mem hw _
      rw [e, e1, LiZhongQC.bB_l_normalizedSolution_zero, LiZhongQC.bB_l_schwarzian_id, norm_zero]
      positivity
    set t : ℝ := lam * u with htdef
    have ht : |t| < δ := by
      rw [htdef, abs_mul, abs_of_pos hlam]
      rwa [lt_div_iff₀ hlam, mul_comm] at hu1
    have htl : t / lam = u := by rw [htdef]; field_simp
    have hupos : 0 < |u| := abs_pos.2 hu0
    -- `α = u ν₀`
    have hαb : ∀ᵐ z, ‖((u : ℝ) : ℂ) * ν₀.1.1 z‖ ≤ 1 / 4 := by
      filter_upwards [hν₀] with z hz
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [abs_nonneg u, norm_nonneg (ν₀.1.1 z)]
    set α : LiZhongQC.BeltramiH := ⟨fun z => ((u : ℝ) : ℂ) * ν₀.1.1 z,
      ⟨⟨1 / 4, by norm_num, by norm_num, by rw [Measure.restrict_univ]; exact hν₀m.const_mul _,
        by rw [Measure.restrict_univ]; exact hαb⟩, fun z hz => by
          show ((u : ℝ) : ℂ) * ν₀.1.1 z = 0
          rw [hν₀0 z hz, mul_zero]⟩⟩ with hαdef
    set ε : ℝ := (|C| + 1) * t ^ 2 with hεdef
    have htne : t ≠ 0 := mul_ne_zero hlam.ne' hu0
    have hε : 0 < ε := by positivity
    have hβα : ∀ᵐ z, ‖(σ t).1.1 z - α.1 z‖ ≤ |C| * t ^ 2 := by
      have h1 : ∀ᵐ z, z ∈ upperHalf →
          ‖(σ t).1.1 z - ((t / lam : ℝ) : ℂ) * ν₀.1.1 z‖ ≤ C * t ^ 2 :=
        (ae_restrict_iff' hU).1 (hσB t ht)
      filter_upwards [h1] with z hz
      by_cases hzU : z ∈ upperHalf
      · have h2 := hz hzU
        rw [htl] at h2
        exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg t))
      · have hz0 : z.im ≤ 0 := not_lt.1 hzU
        show ‖(σ t).1.1 z - ((u : ℝ) : ℂ) * ν₀.1.1 z‖ ≤ _
        rw [(σ t).1.2.2 z hz0, hν₀0 z hz0, mul_zero, sub_zero, norm_zero]
        positivity
    have h4ε : ((4 * ε : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
    have hηb : ∀ᵐ z, ‖((4 * ε : ℝ) : ℂ)⁻¹ * ((σ t).1.1 z - α.1 z)‖ ≤ 1 / 4 := by
      filter_upwards [hβα] with z hz
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,
        div_le_iff₀ (by positivity)]
      have : |C| * t ^ 2 ≤ ε := by
        rw [hεdef]
        nlinarith [sq_nonneg t]
      linarith
    obtain ⟨⟨_, -, -, hβm, -⟩, hβ0⟩ := (σ t).1.2
    rw [Measure.restrict_univ] at hβm
    set η : LiZhongQC.BeltramiH := ⟨fun z => ((4 * ε : ℝ) : ℂ)⁻¹ * ((σ t).1.1 z - α.1 z),
      ⟨⟨1 / 4, by norm_num, by norm_num,
        by rw [Measure.restrict_univ]; exact (hβm.sub (hν₀m.const_mul _)).const_mul _,
        by rw [Measure.restrict_univ]; exact hηb⟩,
        fun z hz => by
          show _ * ((σ t).1.1 z - ((u : ℝ) : ℂ) * ν₀.1.1 z) = 0
          rw [hβ0 z hz, hν₀0 z hz, mul_zero, sub_zero, mul_zero]⟩⟩ with hηdef
    have hs1 : 4 * ε < 1 := by
      have hA : 0 < 4 * ((|C| + 1) * lam ^ 2) := by positivity
      have h' : |u| * (4 * ((|C| + 1) * lam ^ 2)) < 1 := (lt_div_iff₀ hA).1 hu3
      have hu' : u ^ 2 ≤ |u| := by
        rw [← sq_abs]
        nlinarith [abs_nonneg u]
      have e : 4 * ε = 4 * ((|C| + 1) * lam ^ 2) * u ^ 2 := by
        rw [hεdef, htdef]
        ring
      rw [e]
      nlinarith
    have hL := gl6_bers_lipschitz α η hαb hηb (s := 4 * ε) (by positivity) hs1 hw
    have hfe : (fun z => α.1 z + ((4 * ε : ℝ) : ℂ) * η.1 z) = (σ t).1.1 := by
      funext z
      show α.1 z + ((4 * ε : ℝ) : ℂ) * (((4 * ε : ℝ) : ℂ)⁻¹ * ((σ t).1.1 z - α.1 z)) = (σ t).1.1 z
      field_simp
      ring
    have hβ0' : LiZhongQC.bersFunction (σ t).1.1 w = 0 :=
      congrFun ((LiZhongQC.lemma36_2_trivial_iff hΓ (σ t)).1 (hσT t ht)) w
    rw [hfe, hβ0', zero_sub, norm_neg] at hL
    calc _ = ‖LiZhongQC.bersFunction α.1 w‖ := rfl
      _ ≤ _ := hL
      _ = K * u ^ 2 := by
        rw [hK, hεdef, htdef]
        ring
  -- the derivative at `0` vanishes
  have hd := gl6_bers_hasDerivAt ν₀.1 hw
  have hr := (show HasDerivAt (fun s : ℂ => LiZhongQC.bersFunction (fun z => s * ν₀.1.1 z) w)
    (LiZhongQC.bersDerivative ν₀.1.1 w) ((0 : ℝ) : ℂ) by rw [ofReal_zero]; exact hd).comp_ofReal
  have hf0 : LiZhongQC.bersFunction (fun z => ((0 : ℝ) : ℂ) * ν₀.1.1 z) w = 0 := by
    have h := hquad 0 (by rw [abs_zero]; exact hρ0)
    have h00 : K * (0 : ℝ) ^ 2 = 0 := by ring
    rw [h00] at h
    exact norm_le_zero_iff.1 h
  have h0 : HasDerivAt (fun y : ℝ => LiZhongQC.bersFunction (fun z => (y : ℂ) * ν₀.1.1 z) w) 0 0 := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hm : 0 < min ρ (c / (K + 1)) := lt_min hρ0 (div_pos hc (by positivity))
    filter_upwards [ball_mem_nhds (0 : ℝ) hm] with u hu
    rw [mem_ball_zero_iff, lt_min_iff] at hu
    have hq := hquad u (by rw [← Real.norm_eq_abs]; exact hu.1)
    simp only [hf0, sub_zero, smul_zero]
    have h2 : ‖u‖ * (K + 1) < c := (lt_div_iff₀ (by positivity)).1 hu.2
    calc _ ≤ K * u ^ 2 := hq
      _ = K * ‖u‖ * ‖u‖ := by
        have hsq : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
        rw [Real.norm_eq_abs, mul_assoc K, hsq, hK]
      _ ≤ c * ‖u‖ := by
        gcongr
        nlinarith [norm_nonneg u]
  exact hr.unique h0

/-- **Theorem 6** (§6.6, l. 5962). `μ` is an infinitesimally trivial Beltrami differential if and only if there is a
curve `σ_t` of trivial Beltrami coefficients with `σ_t(z) = tμ(z) + O(t²)` uniformly in `z`. Modelling: `t` real,
`σ_t ∈ M(G)` defined for `|t| < δ`; "uniformly" is an a.e. bound `C t²` on `ℍ`. -/
theorem thm6_6 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiSpaceGamma Γ) :
    μ ∈ nSpaceGamma Γ F ↔ ∃ (δ C : ℝ) (σ : ℝ → BeltramiGamma Γ), 0 < δ ∧
      (∀ t, |t| < δ → IsTrivialBeltrami Γ (σ t)) ∧
      ∀ t, |t| < δ → ∀ᵐ z ∂(volume.restrict upperHalf), ‖(σ t).1.1 z - t * μ z‖ ≤ C * t ^ 2 := by
  -- `hfree` is not needed: the Teichmüller lemma and the kernel identification hold for every Fuchsian group
  have _hfree := hfree
  obtain ⟨lam, ν, hlam, hν, hνb⟩ := gl6_scale hμ
  obtain ⟨hD, hP⟩ := gl6_scale_linear hF hν
  have hK := LiZhongQC.lemma36_2_kernel_orthogonal hΓ hF ν
  have hlamne : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam.ne'
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  have hνμ : ∀ z ∈ upperHalf, ν.1.1 z = lam * μ z := fun z hz => by
    rw [hν, indicator_of_mem hz]
  have hscale : ∀ (t : ℝ) (z : ℂ), z ∈ upperHalf → ((t / lam : ℝ) : ℂ) * ν.1.1 z = (t : ℂ) * μ z := by
    intro t z hz
    rw [hνμ z hz]
    push_cast
    field_simp
  constructor
  · rintro ⟨-, horthF⟩
    obtain ⟨⟨kν, -, -, hνm, hνk⟩, hν0⟩ := ν.1.2
    rw [Measure.restrict_univ] at hνm hνk
    have hpair : ∀ φ ∈ LiZhongQC.integrableAutomorphicQD Γ F, LiZhongQC.beltramiPairing F ν.1.1 φ = 0 := fun φ hφ => by
      rw [hP, horthF φ hφ, mul_zero]
    have hκM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖ν.1.1 z‖ ≤ kν := ae_restrict_of_ae hνk
    have horth := LiZhongQC.h36p_kernel_cond hΓ hF hνm.restrict hκM ν.2 hν0 hpair
    obtain ⟨C₁, t₁, hC₁, ht₁, h₁⟩ := LiZhongQC.h36p_teich_lemma hΓ hνm hκM hν0 ν.2 horth
    have hnM : ∀ᵐ z ∂(volume.restrict upperHalf), ‖-ν.1.1 z‖ ≤ kν := by
      filter_upwards [hκM] with z hz
      rwa [norm_neg]
    have hn0 : ∀ z : ℂ, z.im ≤ 0 → -ν.1.1 z = 0 := fun z hz => by rw [hν0 z hz, neg_zero]
    have hnΓ : LiZhongQC.IsGammaCompatible Γ (fun z => -ν.1.1 z) := by
      intro γ hγ
      filter_upwards [ν.2 γ hγ] with z hz
      show -ν.1.1 z = -ν.1.1 _ * _
      rw [hz]
      ring
    have hnorth : ∀ z ∈ LiZhongQC.lowerHalf, ∀ w ∈ LiZhongQC.lowerHalf, ∫ ζ, -ν.1.1 ζ / ((ζ - z) ^ 3 * (ζ - w)) = 0 :=
      fun z hz w hw => by simp only [neg_div, integral_neg, horth z hz w hw, neg_zero]
    obtain ⟨C₂, t₂, hC₂, ht₂, h₂⟩ := LiZhongQC.h36p_teich_lemma hΓ hνm.neg hnM hn0 hnΓ hnorth
    -- the trivial zero coefficient
    have hz0Γ : LiZhongQC.IsGammaCompatible Γ LiZhongQC.b36_q_zero.1 := fun γ _ =>
      Filter.Eventually.of_forall fun z => by
        show (0 : ℂ) = 0 * _
        rw [zero_mul]
    set z0 : BeltramiGamma Γ := ⟨LiZhongQC.b36_q_zero, hz0Γ⟩ with hz0
    have hz0T : IsTrivialBeltrami Γ z0 := fun x => by
      show LiZhongQC.normalizedSolution (0 : ℂ → ℂ) x = x
      rw [LiZhongQC.bB_l_normalizedSolution_zero]
      rfl
    have : Nonempty (BeltramiGamma Γ) := ⟨z0⟩
    choose! f₁ hf₁ using h₁
    choose! f₂ hf₂ using h₂
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → BeltramiGamma Γ, ∀ t, σ t =
        if 0 < t then f₁ (t / lam) else if t < 0 then f₂ (-t / lam) else z0 := ⟨_, fun t => rfl⟩
    refine ⟨lam * min t₁ t₂, max C₁ C₂ / lam ^ 2, σ, mul_pos hlam (lt_min ht₁ ht₂), ?_⟩
    have key : ∀ t : ℝ, |t| < lam * min t₁ t₂ → IsTrivialBeltrami Γ (σ t) ∧
        ∀ᵐ z ∂(volume.restrict upperHalf), ‖(σ t).1.1 z - t * μ z‖ ≤ max C₁ C₂ / lam ^ 2 * t ^ 2 := by
      intro t ht
      have hlt : |t| / lam < min t₁ t₂ := by rwa [div_lt_iff₀ hlam, mul_comm]
      rcases lt_trichotomy t 0 with htn | rfl | htp
      · have hs0 : 0 < -t / lam := div_pos (neg_pos.2 htn) hlam
        have hs1 : -t / lam < t₂ := by
          rw [abs_of_neg htn] at hlt
          exact hlt.trans_le (min_le_right _ _)
        have hσt : σ t = f₂ (-t / lam) := by
          rw [hσ t]
          simp only [not_lt.2 htn.le, htn, ↓reduceIte]
        obtain ⟨hT, hB⟩ := hf₂ _ hs0 hs1
        refine ⟨hσt ▸ hT, ?_⟩
        filter_upwards [hB, ae_restrict_mem hU] with z hz hzU
        have e : (t : ℂ) * μ z = ((-t / lam : ℝ) : ℂ) * -ν.1.1 z := by
          rw [mul_neg, ← neg_mul, ← ofReal_neg, ← neg_div, neg_neg, hscale t z hzU]
        rw [hσt, e]
        calc _ ≤ C₂ * (-t / lam) ^ 2 := hz
          _ = C₂ / lam ^ 2 * t ^ 2 := by
            rw [div_pow, neg_sq]
            ring
          _ ≤ max C₁ C₂ / lam ^ 2 * t ^ 2 := by
            gcongr
            exact le_max_right _ _
      · have hσt : σ 0 = z0 := by
          rw [hσ 0]
          simp only [lt_irrefl, ↓reduceIte]
        refine ⟨hσt ▸ hz0T, Filter.Eventually.of_forall fun z => ?_⟩
        rw [hσt]
        show ‖(0 : ℂ) - ((0 : ℝ) : ℂ) * μ z‖ ≤ max C₁ C₂ / lam ^ 2 * 0 ^ 2
        simp
      · have hs0 : 0 < t / lam := div_pos htp hlam
        have hs1 : t / lam < t₁ := by
          rw [abs_of_pos htp] at hlt
          exact hlt.trans_le (min_le_left _ _)
        have hσt : σ t = f₁ (t / lam) := by
          rw [hσ t]
          simp only [htp, ↓reduceIte]
        obtain ⟨hT, hB⟩ := hf₁ _ hs0 hs1
        refine ⟨hσt ▸ hT, ?_⟩
        filter_upwards [hB, ae_restrict_mem hU] with z hz hzU
        rw [hσt, ← hscale t z hzU]
        calc _ ≤ C₁ * (t / lam) ^ 2 := hz
          _ = C₁ / lam ^ 2 * t ^ 2 := by
            rw [div_pow]
            ring
          _ ≤ max C₁ C₂ / lam ^ 2 * t ^ 2 := by
            gcongr
            exact le_max_left _ _
    exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩
  · rintro ⟨δ, C, σ, hδ, hσT, hσB⟩
    refine ⟨hμ, fun φ hφ => ?_⟩
    have hσB' : ∀ t, |t| < δ → ∀ᵐ z ∂(volume.restrict upperHalf),
        ‖(σ t).1.1 z - ((t / lam : ℝ) : ℂ) * ν.1.1 z‖ ≤ C * t ^ 2 := by
      intro t ht
      filter_upwards [hσB t ht, ae_restrict_mem hU] with z hz hzU
      rwa [hscale t z hzU]
    have h1 : LiZhongQC.IsLocallyTrivialBeltrami ν.1.1 := fun w hw =>
      gl6_bersDerivative_eq_zero hΓ ν hνb hlam hδ σ hσT hσB' hw
    have h4 := hK.1 h1 φ hφ
    rw [hP] at h4
    exact (mul_eq_zero.1 h4).resolve_left hlamne

end GardinerLakic2000
