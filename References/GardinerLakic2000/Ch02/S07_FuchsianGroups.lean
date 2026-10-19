import References.GardinerLakic2000.Ch02.S06_ThricePuncturedSphere

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.7 Fuchsian groups

Source `teichmuller.txt`, lines 1614–1794 (Chapter 2, §2.7).

* Definition (torsion free, l. 1616) — exists: `IsMulTorsionFree` (Mathlib; for groups, no nontrivial element of finite
  order)
* Definition 9 (acts properly discontinuously, l. 1618) — exists: `ProperlyDiscontinuousSMul` (Mathlib, for two
  compacts K and L; the same notion for group actions, take K ∪ L; leader ruling A0.2)
* Definition 10 (Fuchsian group, l. 1622) — exists: `LiZhongQC.IsFuchsian` (a subgroup of SL(2,ℝ) acting properly
  discontinuously on ℍ, in the compact-set form of Definition 9; leader ruling A0.2)
* Lemma 2 (l. 1624) — `lemma2_2`
* Definition (isotropy group, orbit, l. 1648) — exists: `MulAction.stabilizer` `MulAction.orbit`
* Lemma 3 (l. 1650; cited in Ch. 10, l. 7924, 8171) — `lemma2_3_a`, `lemma2_3_b`
* Proposition 4 (l. 1696) — `prop2_4`
* Definition (`p̄`, `X/G`, l. 1725) — exists: `MulAction.orbitRel`
* Lemma 4 ((2.24), l. 1733) — `orbitDist`, `lemma2_4_a`, `lemma2_4_b`, `lemma2_4_c`
* Definition 11 (identity property, l. 1771) — `HasIdentityProperty`
* Definition 12 (elliptic point, l. 1774) — `IsEllipticPoint`
* Lemma 5 (l. 1778) — `lemma2_5`
* Theorem 2 (l. 1784; cited in Ch. 10, l. 8231) — `thm2_2_a`, `thm2_2_b`, `IsQuotientComplexStructure`,
  `IsHolomorphicOnFor`, `thm2_2_c`, `thm2_2_d`

Not items: the Remarks after Proposition 4 (l. 1721, the Δ-model convention; l. 1723, PSL(2,ℂ) on ℍ³); "PSL(2,ℝ) has
the identity property" (l. 1773, U−); the Remark on isotropy groups (l. 1776). Modelling: Fuchsian groups are
subgroups of SL(2,ℝ) (leader ruling A0.2), acting on Mathlib's `UpperHalfPlane`; `±1` act trivially, so "nontrivial
isotropy" (Definition 12) and the identity property (Definition 11) speak about the transformations, not the group
elements. In Lemma 3 "orbits are discrete" is `DiscreteTopology` of each orbit. In Theorem 2 the metric is Mathlib's
`dist` on ℍ (curvature −1, twice the book's; completeness does not depend on the factor), and the quotient carries the
quotient topology; "unique complex structure" is stated as: any two such structures have the same holomorphic
functions on open sets. Near misses: Lemma 3 `Katok1992.actsPD_iff_orbit_stabilizer`, Proposition 4
`Katok1992.thm2_2_6` (Katok's "properly discontinuous" is "orbits locally finite").
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (upperHalf IsFuchsian)

/-- An element of `SL(2,ℝ)` acting trivially on `ℍ` is `±1`. -/
theorem l22_smul_self_iff {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : ∀ τ : UpperHalfPlane, δ • τ = τ) : δ = 1 ∨ δ = -1 := by
  -- the action on ℂ via h36p_m
  have key : ∀ τ : UpperHalfPlane, LiZhongQC.h36p_m δ (τ : ℂ) = (τ : ℂ) := fun τ => by
    rw [LiZhongQC.h36p_m_coe, h τ]
  -- the denominator never vanishes on ℍ
  have hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) ℝ) = 1 := δ.2
  have hden : ∀ z : ℂ, 0 < z.im → ((δ 1 0 : ℂ) * z + δ 1 1) ≠ 0 := by
    intro z hz h0
    have him : ((δ 1 0 : ℂ) * z + (δ 1 1 : ℂ)).im = δ 1 0 * z.im := by
      rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_im]
      ring
    have e : δ 1 0 * z.im = 0 := by
      have e := congrArg Complex.im h0
      rw [him, Complex.zero_im] at e
      exact e
    have hc0 : δ 1 0 = 0 := by
      rcases mul_eq_zero.1 e with h | h
      · exact h
      · exact absurd h hz.ne'
    have hre : ((δ 1 0 : ℂ) * z + (δ 1 1 : ℂ)).re = δ 1 0 * z.re + δ 1 1 := by
      rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]
      ring
    have hd0 : δ 1 1 = 0 := by
      have e := congrArg Complex.re h0
      rw [hre, hc0, Complex.zero_re] at e
      simpa using e
    rw [Matrix.det_fin_two, hd0, hc0, mul_zero, mul_zero, sub_zero] at hdet
    exact one_ne_zero hdet.symm
  -- evaluate at I and 2I
  have eq1 := key ⟨Complex.I, by simp⟩
  have eq2 := key ⟨2 * Complex.I, by simp⟩
  rw [LiZhongQC.h36p_m, div_eq_iff (hden _ (by simp))] at eq1
  rw [LiZhongQC.h36p_m, div_eq_iff (hden _ (by simp))] at eq2
  -- read off real and imaginary parts
  have e1 := Complex.ext_iff.1 eq1
  have e2 := Complex.ext_iff.1 eq2
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im] at e1 e2
  -- e1 : b = −c ∧ a = d ; e2 : b = −4c ∧ 2a = 2d (up to ordering)
  obtain ⟨e1r, e1i⟩ := e1
  obtain ⟨e2r, e2i⟩ := e2
  have hc0 : δ 1 0 = 0 := by linarith
  have hb0 : δ 0 1 = 0 := by linarith
  have had : δ 0 0 = δ 1 1 := by linarith
  -- det: a² = 1
  have ha2 : δ 0 0 ^ 2 = 1 := by
    have hdet' := hdet
    rw [Matrix.det_fin_two, hb0, hc0, zero_mul, sub_zero] at hdet'
    rw [← had] at hdet'
    rwa [← pow_two] at hdet'
  have ha1 : δ 0 0 = 1 ∨ δ 0 0 = -1 := sq_eq_one_iff.1 ha2
  -- assemble the matrix equality
  have hval : (δ : Matrix (Fin 2) (Fin 2) ℝ) = δ 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0, hc0, had]
  rcases ha1 with h1 | h1
  · left
    apply Subtype.ext
    rw [hval, h1]
    simp
  · right
    apply Subtype.ext
    rw [hval, h1]
    simp

/-- **Lemma 2** (§2.7, l. 1624). A bijective holomorphic self-map `A` of `ℍ` is `z ↦ (az + b)/(cz + d)` with real
`a, b, c, d`, `ad − bc = 1`, and the matrix is unique up to sign (so Fuchsian groups lie in PSL(2,ℝ)). -/
theorem lemma2_2 {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A upperHalf) (hbij : BijOn A upperHalf upperHalf) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ z ∈ upperHalf, A z = LiZhongQC.h36p_m γ z) ∧
      ∀ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ z ∈ upperHalf, A z = LiZhongQC.h36p_m γ' z) →
        γ' = γ ∨ γ' = -γ := by
  have hΩ : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hconf : LiZhongQC.IsConformalOnto A upperHalf upperHalf := ⟨hA, hbij.injOn, hbij.image_eq⟩
  -- the homeomorphism of ℍ induced by A
  set ginv := Function.invFunOn A upperHalf with hginv
  have hginvL : ∀ z ∈ upperHalf, ginv (A z) = z := fun z hz => hbij.injOn.leftInvOn_invFunOn hz
  have hginvR : ∀ w ∈ upperHalf, A (ginv w) = w := fun w hw =>
    Function.invFunOn_eq (by rwa [← hbij.image_eq] at hw)
  have hginv_mem : ∀ w ∈ upperHalf, ginv w ∈ upperHalf := fun w hw =>
    Function.invFunOn_mem (by rwa [← hbij.image_eq] at hw)
  have hconfinv : ContinuousOn ginv upperHalf := (hconf.symm hΩ).1.continuousOn
  set F : UpperHalfPlane ≃ₜ UpperHalfPlane := {
    toFun := fun τ => ⟨A τ.1, hbij.mapsTo τ.2⟩
    invFun := fun τ => ⟨ginv τ.1, hginv_mem τ.1 τ.2⟩
    left_inv := fun τ => UpperHalfPlane.ext (hginvL τ.1 τ.2)
    right_inv := fun τ => UpperHalfPlane.ext (hginvR τ.1 τ.2)
    continuous_toFun := Continuous.upperHalfPlaneMk
      (hA.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.2) (fun τ => hbij.mapsTo τ.2)
    continuous_invFun := Continuous.upperHalfPlaneMk
      (hconfinv.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.2) _ } with hFdef
  -- the lift is conformal on ℍ, hence 1-qc
  have hEq : EqOn (LiZhongQC.liftToC F) A upperHalf := fun z hz => by
    have e := LiZhongQC.h23l_liftToC_coe F ⟨z, hz⟩
    rw [e, hFdef]
    rfl
  have hconfL : LiZhongQC.IsConformalOnto (LiZhongQC.liftToC F) upperHalf upperHalf := by
    refine ⟨?_, ?_, ?_⟩
    · exact hconf.1.congr fun z hz => hEq hz
    · exact hconf.2.1.congr hEq.symm
    · rw [Set.EqOn.image_eq hEq, hconf.2.2]
  obtain ⟨m, hm⟩ := LiZhongQC.utm_eq_smul_of_isKQC_one F (LiZhongQC.isKQC_one_of_conformal hΩ hconfL)
  refine ⟨m, ?_, ?_⟩
  · intro z hz
    have e1 : A z = ↑(F ⟨z, hz⟩) := rfl
    rw [e1, hm ⟨z, hz⟩, ← LiZhongQC.h36p_m_coe]
  · intro γ' hγ'
    -- δ := m⁻¹ * γ' acts trivially on ℍ
    have hδ : ∀ τ : UpperHalfPlane, (m⁻¹ * γ') • τ = τ := by
      intro τ
      have e : γ' • τ = m • τ := by
        have h1 := hγ' ↑τ τ.2
        have h2 : A ↑τ = LiZhongQC.h36p_m m ↑τ := by
          have e1 : A ↑τ = ↑(F τ) := rfl
          rw [e1, hm τ]
          rw [LiZhongQC.h36p_m_coe]
        rw [LiZhongQC.h36p_m_coe] at h1
        rw [h1] at h2
        rw [LiZhongQC.h36p_m_coe] at h2
        exact UpperHalfPlane.coe_injective h2
      rw [mul_smul, e, inv_smul_smul]
    -- classify
    rcases l22_smul_self_iff hδ with h1 | h1
    · left
      have e := eq_mul_of_inv_mul_eq h1
      rwa [mul_one] at e
    · right
      have e := eq_mul_of_inv_mul_eq h1
      rwa [mul_neg_one] at e

/-- The (2.22)-type estimate, fixed second index. -/
theorem l23a_estimate {X : Type*} [MetricSpace X] {G : Subgroup (X ≃ₜ X)}
    (hG : ∀ g ∈ G, Isometry (g : X → X)) {pp rr : ℕ → X} {g : ℕ → G} (hrr : ∀ n, rr n = g n • pp n)
    (b : X) (m n₀ : ℕ) :
    dist ((g m * (g n₀)⁻¹ : G) • b) b ≤ dist b (rr n₀) + dist (pp n₀) (pp m) + dist (rr m) b := by
  have e1 : ∀ (h : G) (u : X), h • u = (h : X ≃ₜ X) u := fun h u => rfl
  have hppinv : ∀ n, ((g n)⁻¹ : G) • rr n = pp n := fun n => by
    rw [hrr n]
    exact inv_smul_smul _ _
  have hI : ∀ h : G, Isometry ((h : X ≃ₜ X) : X → X) := fun h => hG _ (SetLike.coe_mem h)
  have hIs : ∀ h : G, Isometry (((h⁻¹ : G) : X ≃ₜ X) : X → X) := fun h =>
    hG _ (SetLike.coe_mem (h⁻¹))
  have tA : dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) ((g m : G) • pp n₀) =
      dist (((g n₀)⁻¹ : G) • b) (pp n₀) := by
    rw [e1, e1]
    exact (hI (g m)).dist_eq _ _
  have tA' : dist (((g n₀)⁻¹ : G) • b) (pp n₀) = dist b (rr n₀) := by
    rw [← hppinv n₀, e1, e1]
    exact (hIs (g n₀)).dist_eq _ _
  have tB : dist ((g m : G) • pp n₀) (rr m) = dist (pp n₀) (pp m) := by
    rw [hrr m, e1, e1]
    exact (hI (g m)).dist_eq _ _
  calc dist ((g m * (g n₀)⁻¹ : G) • b) b
      = dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) b := by rw [mul_smul]
    _ ≤ dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) ((g m : G) • pp n₀) +
          (dist ((g m : G) • pp n₀) (rr m) + dist (rr m) b) := by
        have t1 : dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) b ≤
            dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) ((g m : G) • pp n₀) +
              dist ((g m : G) • pp n₀) b := dist_triangle _ _ _
        have t2 : dist ((g m : G) • pp n₀) b ≤
            dist ((g m : G) • pp n₀) (rr m) + dist (rr m) b := dist_triangle _ _ _
        calc dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) b ≤
              dist ((g m : G) • (((g n₀)⁻¹ : G) • b)) ((g m : G) • pp n₀) + dist ((g m : G) • pp n₀) b := t1
          _ ≤ _ := by linarith [t2]
    _ = dist b (rr n₀) + (dist (pp n₀) (pp m) + dist (rr m) b) := by rw [tA, tA', tB]
    _ = _ := by rw [← add_assoc]

/-- Isolated orbit points: if the orbit of `b` is discrete, some ball around `b` meets the orbit only
at `b`. -/
theorem l23a_orbit_ball {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) {b : X}
    (hdisc : DiscreteTopology (MulAction.orbit G b)) :
    ∃ ρ > 0, ∀ y ∈ MulAction.orbit G b, dist y b < ρ → y = b := by
  have hmemb : b ∈ MulAction.orbit G b := MulAction.mem_orbit_iff.2 ⟨1, one_smul _ _⟩
  have hopen1 : IsOpen ({⟨b, hmemb⟩} : Set (MulAction.orbit G b)) :=
    discreteTopology_iff_isOpen_singleton.1 hdisc ⟨b, hmemb⟩
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hopen1
  have hbV : b ∈ V := by
    have : ⟨b, hmemb⟩ ∈ Subtype.val ⁻¹' V := by rw [hV]; exact Set.mem_singleton _
    exact this
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hVo b hbV
  refine ⟨ρ, hρ, fun y hyo hyb => ?_⟩
  have hyV : y ∈ V := hρV hyb
  have hmem : (⟨y, hyo⟩ : MulAction.orbit G b) ∈ Subtype.val ⁻¹' V := hyV
  rw [hV] at hmem
  have := Set.mem_singleton_iff.1 hmem
  exact congrArg Subtype.val this

/-- **Lemma 3** (§2.7, l. 1650), first part. A group of isometries of a metric space with finite isotropy groups and
discrete orbits acts properly discontinuously. -/
theorem lemma2_3_a {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) (hG : ∀ g ∈ G, Isometry (g : X → X))
    (hfin : ∀ x : X, (MulAction.stabilizer G x : Set G).Finite)
    (hdisc : ∀ x : X, DiscreteTopology (MulAction.orbit G x)) : ProperlyDiscontinuousSMul G X := by
  refine ⟨fun {K L} hK hL => ?_⟩
  by_contra hnot
  rw [Set.not_finite] at hnot
  -- an injective sequence of bad elements
  obtain ⟨gs, hgsinj, hgsmem⟩ : ∃ gs : ℕ → G, Function.Injective gs ∧
      ∀ n, gs n ∈ {g : G | ((g • ·) '' K ∩ L).Nonempty} := by
    obtain ⟨f, hf⟩ := hnot.natEmbedding
    exact ⟨fun n => (f n).1, fun i j h => hf (Subtype.ext h), fun n => (f n).2⟩
  -- points witnessing the non-emptiness
  have hp : ∀ n, ∃ p ∈ K, (gs n) • p ∈ L := fun n => by
    obtain ⟨y, ⟨p, hpK, hpy⟩, hyL⟩ := hgsmem n
    exact ⟨p, hpK, by rwa [← hpy] at hyL⟩
  choose pp hppK hppL using hp
  set rr : ℕ → X := fun n => gs n • pp n with hrrdef
  -- convergent subsequences in K and L
  obtain ⟨a, haK, φ₁, hφ₁, hlim₁⟩ :=
    (hK.isCountablyCompact.isSeqCompact).subseq_of_frequently_in (Frequently.of_forall hppK)
  obtain ⟨b, hbL, φ₂, hφ₂, hlim₂⟩ :=
    (hL.isCountablyCompact.isSeqCompact).subseq_of_frequently_in
      (Frequently.of_forall (fun n => hppL (φ₁ n)))
  set ψ := φ₁ ∘ φ₂ with hψdef
  have hψmono : StrictMono ψ := hφ₁.comp hφ₂
  have hlim₁ψ : Tendsto (pp ∘ ψ) atTop (𝓝 a) := by
    rw [hψdef, ← Function.comp_assoc]
    exact hlim₁.comp hφ₂.tendsto_atTop
  have hlim₂ψ : Tendsto (rr ∘ ψ) atTop (𝓝 b) := by
    rw [hψdef, ← Function.comp_assoc]
    exact hlim₂
  -- the isolation radius of b in its orbit
  obtain ⟨ρ, hρ, hρprop⟩ := l23a_orbit_ball G (hdisc b)
  -- choose n₀ (along ψ) making the two fixed terms small
  have hconv1 : ∀ᶠ n : ℕ in atTop, dist b ((rr ∘ ψ) n) < ρ / 4 := by
    have := hlim₂ψ.eventually (ball_mem_nhds b (by positivity : (0 : ℝ) < ρ / 4))
    filter_upwards [this] with n hn
    rw [dist_comm]
    exact hn
  have hconv2 : ∀ᶠ n : ℕ in atTop, dist ((pp ∘ ψ) n) a < ρ / 4 :=
    hlim₁ψ.eventually (ball_mem_nhds a (by positivity))
  obtain ⟨n₀, hn₀⟩ := (hconv1.and hconv2).exists  -- some n₀ with both
  -- M₀ making the m-dependent terms small
  have hconv3 : ∀ᶠ m : ℕ in atTop, dist ((rr ∘ ψ) m) b < ρ / 4 :=
    hlim₂ψ.eventually (ball_mem_nhds b (by positivity))
  have hconv4 : ∀ᶠ m : ℕ in atTop, dist ((pp ∘ ψ) m) a < ρ / 4 := hconv2
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (hconv3.and hconv4)
  -- the stabilizer-finiteness contradiction
  have hfin' := hfin b
  have hrr : ∀ n, rr n = gs n • pp n := fun n => rfl
  have hstab : ∀ m ≥ M₀, (gs (ψ m) * (gs (ψ n₀))⁻¹ : G) ∈ MulAction.stabilizer G b := by
    intro m hm
    rw [MulAction.mem_stabilizer_iff]
    have hest := l23a_estimate hG hrr b (ψ m) (ψ n₀)
    have t1 : dist b (rr (ψ n₀)) < ρ / 4 := hn₀.1
    have t2 : dist (pp (ψ n₀)) (pp (ψ m)) < ρ / 2 := by
      have t2a := hn₀.2
      have t2b := (hM₀ m hm).2
      rw [dist_comm] at t2b
      calc dist (pp (ψ n₀)) (pp (ψ m)) ≤ dist (pp (ψ n₀)) a + dist a (pp (ψ m)) := dist_triangle _ _ _
        _ < ρ / 4 + ρ / 4 := add_lt_add t2a t2b
        _ = ρ / 2 := by ring
    have t3 : dist (rr (ψ m)) b < ρ / 4 := (hM₀ m hm).1
    have hball : dist ((gs (ψ m) * (gs (ψ n₀))⁻¹ : G) • b) b < ρ := by linarith [hest, t1, t2, t3]
    have hmem : (gs (ψ m) * (gs (ψ n₀))⁻¹ : G) • b ∈ MulAction.orbit G b :=
      MulAction.mem_orbit_iff.2 ⟨_, rfl⟩
    exact hρprop _ hmem (mem_ball.2 hball)
  -- the pigeonhole on `m ↦ g_{ψ m} g_{ψ n₀}⁻¹` into the finite stabilizer
  haveI := hfin'.fintype
  obtain ⟨m₁, m₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun m : ℕ => (⟨(gs (ψ (m + M₀)) * (gs (ψ n₀))⁻¹ : G), hstab (m + M₀) (by omega)⟩ :
      (MulAction.stabilizer G b : Set G)))
  have heqG : (gs (ψ (m₁ + M₀)) * (gs (ψ n₀))⁻¹ : G) = (gs (ψ (m₂ + M₀)) * (gs (ψ n₀))⁻¹ : G) :=
    congrArg Subtype.val heq
  have hcancel : gs (ψ (m₁ + M₀)) = gs (ψ (m₂ + M₀)) := mul_right_cancel heqG
  have hidx : ψ (m₁ + M₀) = ψ (m₂ + M₀) := hgsinj hcancel
  have hm : m₁ + M₀ = m₂ + M₀ := hψmono.injective hidx
  exact hne (Nat.add_right_cancel hm)

/-- The self-intersection set at a singleton is the stabilizer. -/
theorem l23b_inter_self_eq_stabilizer {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) (x : X) :
    {g : G | ((g • ·) '' {x} ∩ {x}).Nonempty} = (MulAction.stabilizer G x : Set G) := by
  ext g
  show ((g • ·) '' {x} ∩ {x}).Nonempty ↔ (g ∈ (MulAction.stabilizer G x : Set G))
  simp only [Set.image_singleton, Set.singleton_inter_nonempty, SetLike.mem_coe]
  exact MulAction.mem_stabilizer_iff.symm

/-- The orbit points of a properly discontinuous action are uniformly separated from the point. -/
theorem l23b_isolated {X : Type*} [MetricSpace X] [LocallyCompactSpace X] (G : Subgroup (X ≃ₜ X))
    (hpd : ProperlyDiscontinuousSMul G X) (x : X) :
    ∃ ε > 0, ∀ y ∈ MulAction.orbit G x, y ≠ x → ε ≤ dist y x := by
  classical
  obtain ⟨K, ⟨hKn, hKc⟩, -⟩ := ((compact_basis_nhds x).mem_iff).1 (isOpen_univ.mem_nhds trivial)
  obtain ⟨ε₀, hε₀, hε₀K⟩ := Metric.mem_nhds_iff.1 hKn
  set C := closedBall x (ε₀ / 2) with hCdef
  have hCK : C ⊆ K := (closedBall_subset_ball (by linarith)).trans hε₀K
  have hCc : IsCompact C := hKc.of_isClosed_subset isClosed_closedBall hCK
  have hF : ({g : G | ((g • ·) '' C ∩ C).Nonempty}).Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) (T := X) (K := C) (L := C) hCc hCc
  set P : Finset ℝ := (hF.toFinset.filter fun g : G => ¬ g • x = x).image fun g : G =>
    dist (g • x) x with hPdef
  by_cases hP : P.Nonempty
  · have hε₁ : (0 : ℝ) < P.min' hP := by
      have hmem := P.min'_mem hP
      simp only [hPdef, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset] at hmem
      obtain ⟨g, ⟨-, hgx⟩, hgd⟩ := hmem
      rw [← hgd]
      exact dist_pos.2 hgx
    refine ⟨min (ε₀ / 2) (P.min' hP), lt_min (by positivity) hε₁, fun y hy hne => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    by_cases hgF : g ∈ {g : G | ((g • ·) '' C ∩ C).Nonempty}
    · have hmem : dist (g • x) x ∈ P := by
        simp only [hPdef, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨g, ⟨hgF, hne⟩, rfl⟩
      exact (min_le_right _ _).trans (P.min'_le _ hmem)
    · have hgnC : g • x ∉ C := by
        intro hgxC
        exact hgF ⟨g • x, ⟨x, mem_closedBall_self (by linarith), rfl⟩, hgxC⟩
      rw [hCdef, mem_closedBall, not_le] at hgnC
      exact (min_le_left _ _).trans hgnC.le
  · refine ⟨ε₀ / 2, by positivity, fun y hy hne => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    have hgF : g ∉ {g : G | ((g • ·) '' C ∩ C).Nonempty} := by
      intro hgF
      have hfil : g ∈ hF.toFinset.filter (fun g : G => ¬ g • x = x) := by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hgF, hne⟩
      exact hP (Finset.image_nonempty.2 ⟨_, hfil⟩)
    have hgnC : g • x ∉ C := by
      intro hgxC
      exact hgF ⟨g • x, ⟨x, mem_closedBall_self (by linarith), rfl⟩, hgxC⟩
    rw [hCdef, mem_closedBall, not_le] at hgnC
    exact hgnC.le

/-- **Lemma 3** (§2.7, l. 1650), converse. If the group of isometries acts properly discontinuously on the locally
compact metric space `X`, its isotropy groups are finite and its orbits discrete. -/
theorem lemma2_3_b {X : Type*} [MetricSpace X] [LocallyCompactSpace X] (G : Subgroup (X ≃ₜ X))
    (hG : ∀ g ∈ G, Isometry (g : X → X)) (hpd : ProperlyDiscontinuousSMul G X) :
    ∀ x : X, (MulAction.stabilizer G x : Set G).Finite ∧ DiscreteTopology (MulAction.orbit G x) := by
  intro x
  constructor
  · rw [← l23b_inter_self_eq_stabilizer G x]
    exact ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) (T := X)
      (K := {x}) (L := {x}) isCompact_singleton isCompact_singleton
  · obtain ⟨ε, hε, hεprop⟩ := l23b_isolated G hpd x
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    obtain ⟨g₀, hg₀⟩ := MulAction.mem_orbit_iff.1 q.2
    rw [isOpen_induced_iff]
    refine ⟨ball (q : X) ε, isOpen_ball, ?_⟩
    ext ⟨y, hy⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball]
    constructor
    · intro hd
      apply Subtype.ext
      -- hd : dist y ↑q < ε; transport back to x by g₀⁻¹
      have hxq : (g₀⁻¹ : G) • (q : X) = x := by
        rw [← hg₀]
        exact inv_smul_smul _ _
      have h1 : (g₀⁻¹ : G) • y ∈ MulAction.orbit G x := by
        obtain ⟨h', hh'⟩ := MulAction.mem_orbit_iff.1 hy
        rw [MulAction.mem_orbit_iff]
        exact ⟨(g₀⁻¹ : G) * h', by rw [mul_smul, hh']⟩
      by_cases hcon : (g₀⁻¹ : G) • y = x
      · have hyy : y = g₀ • x := by
          have hcc := congrArg ((g₀ : G) • ·) hcon
          rwa [smul_inv_smul] at hcc
        exact hyy.trans hg₀
      · have h2 := hεprop ((g₀⁻¹ : G) • y) h1 hcon
        have hdist : dist ((g₀⁻¹ : G) • y) x = dist y (q : X) := by
          have hIso := hG _ (Subgroup.inv_mem G (SetLike.coe_mem g₀))
          have e1 : ∀ (g : G) (u : X), g • u = (g : X ≃ₜ X) u := fun g u => rfl
          calc dist ((g₀⁻¹ : G) • y) x
              = dist ((g₀⁻¹ : G) • y) ((g₀⁻¹ : G) • (q : X)) := by
                exact (congrArg (fun u => dist ((g₀⁻¹ : G) • y) u) hxq).symm
            _ = dist (((g₀⁻¹ : G) : X ≃ₜ X) y) (((g₀⁻¹ : G) : X ≃ₜ X) (q : X)) := by rw [e1, e1]
            _ = dist y (q : X) := hIso.dist_eq y (q : X)
        rw [hdist] at h2
        exact absurd (h2.trans_lt hd) (lt_irrefl _)
    · intro hd
      have hyq : y = (q : X) := congrArg Subtype.val hd
      rw [hyq, dist_self]
      exact hε

/-- The `SL(2,ℝ)`-set of the Fuchsian hypothesis equals the image of the subtype set. -/
theorem p24_fuchsian_set_eq (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (C : Set UpperHalfPlane) :
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧ ((γ • ·) '' C ∩ C).Nonempty} =
      Subtype.val '' {g : Γ | ((g • ·) '' C ∩ C).Nonempty} := by
  ext γ
  constructor
  · rintro ⟨hγΓ, hP⟩
    exact ⟨⟨γ, hγΓ⟩, hP, rfl⟩
  · rintro ⟨g, hP, rfl⟩
    exact ⟨g.2, hP⟩

/-- A properly discontinuous subgroup of `SL(2,ℝ)` has an isolated identity
(the converse argument of GL Lemma 3, l. 1650). -/
theorem p24_isolated_one {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hF : IsFuchsian Γ) :
    IsOpen ({1} : Set Γ) := by
  by_contra hnot
  set τ : UpperHalfPlane := ⟨Complex.I, by simp⟩ with hτdef
  -- the action map g ↦ g • τ on Γ is continuous
  have hφcont : Continuous (fun g : Γ => (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ) :=
    continuous_subtype_val.smul continuous_const
  have hφ1 : (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := one_smul _ _
  -- the compact unit disc around τ in ℍ (ProperSpace)
  set C := closedBall τ 1 with hCdef
  have hCcompact : IsCompact C := isCompact_closedBall τ 1
  -- the finiteness from the Fuchsian hypothesis, transferred to the subtype
  have hS : ({γ : Matrix.SpecialLinearGroup (Fin 2) ℝ |
      γ ∈ Γ ∧ ((γ • ·) '' C ∩ C).Nonempty}).Finite := hF C hCcompact
  have hS' : ({g : Γ | ((g • ·) '' C ∩ C).Nonempty}).Finite := by
    apply Set.Finite.of_finite_image (f := (Subtype.val : Γ → Matrix.SpecialLinearGroup (Fin 2) ℝ))
    · rw [← p24_fuchsian_set_eq Γ C]
      exact hS
    · exact Subtype.val_injective.injOn
  -- V := preimage of the open unit ball around τ, a neighbourhood of 1 in Γ
  set V := (fun g : Γ => (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ) ⁻¹' (ball τ 1) with hVdef
  have h1V : (1 : Γ) ∈ V := by
    rw [hVdef]
    apply mem_preimage.2
    show (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ ∈ ball τ 1
    rw [one_smul]
    exact mem_ball_self one_pos
  have hVn : V ∈ 𝓝 (1 : Γ) := by
    have hball : ball τ 1 ∈ 𝓝 ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ) := by
      rw [one_smul]
      exact ball_mem_nhds τ one_pos
    exact hφcont.continuousAt.preimage_mem_nhds hball
  -- V ⊆ the Fuchsian set
  have hVF' : V ⊆ {g : Γ | ((g • ·) '' C ∩ C).Nonempty} := by
    intro g hg
    have hg1 : ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ)) • τ ∈ C :=
      ball_subset_closedBall (mem_preimage.1 hg)
    refine ⟨(g • τ), ?_, ?_⟩
    · exact ⟨τ, mem_closedBall_self one_pos.le, by rfl⟩
    · exact hg1
  -- V is infinite: otherwise {1} would be open
  have hVinf : V.Infinite := by
    intro hVfin
    obtain ⟨U, hUV, hUo, h1U⟩ := mem_nhds_iff.1 hVn
    have hcl : IsClosed (V \ {1}) := (hVfin.subset Set.sdiff_subset).isClosed
    have hU'o : IsOpen (U \ (V \ {1})) := hUo.sdiff hcl
    have h1U' : (1 : Γ) ∈ U \ (V \ {1}) := ⟨h1U, fun h => h.2 rfl⟩
    have hsub : U \ (V \ {1}) ⊆ {1} := fun x hx => by
      by_contra hx1
      exact hx.2 ⟨hUV hx.1, hx1⟩
    have : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := mem_of_superset (hU'o.mem_nhds h1U') hsub
    exact hnot ((isOpen_iff_mem_nhds).2 fun x hx => by rw [mem_singleton_iff.1 hx]; exact this)
  exact hVinf (hS'.subset hVF')

/-- **Proposition 4** (§2.7, l. 1696). A subgroup of SL(2,ℝ) is discrete if and only if it acts properly
discontinuously on `ℍ`. -/
theorem prop2_4 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : DiscreteTopology Γ ↔ IsFuchsian Γ := by
  constructor
  · intro h C hC
    haveI := h
    have key : Set.Finite {g : Γ | ((g • ·) '' C ∩ C).Nonempty} :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (K := C) (L := C) hC hC
    rw [p24_fuchsian_set_eq Γ C]
    exact key.image Subtype.val
  · intro hF
    exact discreteTopology_iff_isOpen_singleton_one.2 (p24_isolated_one hF)

/-- **Formula (2.24)** (§2.7, l. 1737). The distance of two orbits `d̄(p̄, r̄) = inf_{p ∈ p̄, r ∈ r̄} d(p, r)`. -/
def orbitDist {G X : Type*} [Group G] [MulAction G X] [PseudoMetricSpace X]
    (p r : Quotient (MulAction.orbitRel G X)) : ℝ :=
  ⨅ (x : {a : X // Quotient.mk (MulAction.orbitRel G X) a = p})
    (y : {b : X // Quotient.mk (MulAction.orbitRel G X) b = r}), dist x.1 y.1

/-- Small archimedean step: some `1 / (N + 1)` is below `ε`. -/
theorem l24_one_div_lt {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, 1 / ((N : ℝ) + 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  rw [show ε = 1 / (1 / ε) from (one_div_one_div ε).symm,
    one_div_lt_one_div (by positivity) (one_div_pos.2 hε)]
  have hN' : (1 : ℝ) / ε < (N : ℝ) := by exact_mod_cast hN
  linarith

/-- Monotonicity of `1 / (n + 1)` in `n`. -/
theorem l24_one_div_le {N n : ℕ} (hn : N ≤ n) : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
  refine (one_div_le_one_div (by positivity) (by positivity)).2 ?_
  have h : N + 1 ≤ n + 1 := by omega
  exact_mod_cast h

/-- Pull `g₁` out of a distance of two orbit points (general group action by isometries). -/
theorem l24g_dist_smul {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z)) (g₁ g₂ : G) (u v : X) :
    dist (g₁ • u) (g₂ • v) = dist u ((g₁⁻¹ * g₂ : G) • v) := by
  have key := (hG g₁⁻¹).dist_eq (g₁ • u) (g₂ • v)
  rw [inv_smul_smul] at key
  rw [← mul_smul] at key
  exact key.symm

/-- Approximate attainment for `orbitDist` (general group action by isometries). -/
theorem l24g_attain {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z)) (x y : X) {ε : ℝ}
    (hε : orbitDist (Quotient.mk (MulAction.orbitRel G X) x)
      (Quotient.mk (MulAction.orbitRel G X) y) < ε) :
    ∃ g : G, dist x (g • y) < ε := by
  have hne1 : Nonempty {a : X // Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x} := ⟨⟨x, rfl⟩⟩
  have hne2 : Nonempty {b : X // Quotient.mk (MulAction.orbitRel G X) b =
      Quotient.mk (MulAction.orbitRel G X) y} := ⟨⟨y, rfl⟩⟩
  unfold orbitDist at hε
  obtain ⟨x', hx'⟩ := exists_lt_of_ciInf_lt hε
  obtain ⟨y', hy'⟩ := exists_lt_of_ciInf_lt hx'
  have hmemx : (x'.1 : X) ∈ MulAction.orbit G x := by
    have h := (Quotient.eq).1 x'.2
    rwa [MulAction.orbitRel_apply] at h
  obtain ⟨g₁, hg₁⟩ := MulAction.mem_orbit_iff.1 hmemx
  have hmemy : (y'.1 : X) ∈ MulAction.orbit G y := by
    have h := (Quotient.eq).1 y'.2
    rwa [MulAction.orbitRel_apply] at h
  obtain ⟨g₂, hg₂⟩ := MulAction.mem_orbit_iff.1 hmemy
  refine ⟨g₁⁻¹ * g₂, ?_⟩
  rw [← l24g_dist_smul hG g₁ g₂ x y, hg₁, hg₂]
  exact hy'

/-- From `orbitDist (mk x) (mk y) = 0`: a sequence of group elements with `A n • y → x`. -/
theorem l24_seq {X : Type*} [MetricSpace X] {G : Subgroup (X ≃ₜ X)}
    (hG : ∀ g ∈ G, Isometry (g : X → X)) (x y : X)
    (h0 : orbitDist (Quotient.mk (MulAction.orbitRel G X) x)
      (Quotient.mk (MulAction.orbitRel G X) y) = 0) :
    ∃ A : ℕ → G, ∀ n : ℕ, dist x (A n • y) < 1 / ((n : ℝ) + 1) := by
  have h : ∀ n : ℕ, ∃ g : G, dist x (g • y) < 1 / ((n : ℝ) + 1) := fun n =>
    l24g_attain (fun g => hG _ (SetLike.coe_mem g)) x y (by rw [h0]; positivity)
  classical
  exact ⟨fun n => (h n).choose, fun n => (h n).choose_spec⟩

/-- Lemma 4 (a), finite case: finitely many group elements force an attained zero distance. -/
theorem l24_finite_zero {X : Type*} [MetricSpace X] {G : Subgroup (X ≃ₜ X)} (x y : X)
    {A : ℕ → G} (hA : ∀ n : ℕ, dist x (A n • y) < 1 / ((n : ℝ) + 1)) (hfin : (Set.range A).Finite) :
    ∃ n : ℕ, x = A n • y := by
  classical
  have hS : ((fun g : G => dist x (g • y)) '' Set.range A).Finite := hfin.image _
  have hSne : ((fun g : G => dist x (g • y)) '' Set.range A).Nonempty :=
    (Set.range_nonempty A).image _
  have : Finite ↥((fun g : G => dist x (g • y)) '' Set.range A) := Set.finite_coe_iff.2 hS
  have : Nonempty ↥((fun g : G => dist x (g • y)) '' Set.range A) := by
    obtain ⟨v, hv⟩ := hSne
    exact ⟨⟨v, hv⟩⟩
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min
    (fun s : ↥((fun g : G => dist x (g • y)) '' Set.range A) => (s : ℝ))
  obtain ⟨g₀, hg₀, hdist0⟩ := a₀.2
  obtain ⟨n₀, rfl⟩ := hg₀
  have hdist : dist x (A n₀ • y) = (a₀ : ℝ) := hdist0
  have hle0 : (a₀ : ℝ) ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨N, hN⟩ := l24_one_div_lt hpos
    have hle := ha₀ ⟨dist x (A N • y), ⟨A N, ⟨N, rfl⟩, rfl⟩⟩
    have hlt : dist x (A N • y) < (a₀ : ℝ) := (hA N).trans hN
    linarith
  have hge0 : 0 ≤ (a₀ : ℝ) := by
    rw [← hdist]
    exact dist_nonneg
  have h0 : dist x (A n₀ • y) = 0 := by
    rw [hdist]
    exact le_antisymm hle0 hge0
  exact ⟨n₀, dist_eq_zero.1 h0⟩

/-- **Lemma 4** (§2.7, l. 1733), the metric. For a properly discontinuous group of isometries of a locally compact
metric space, `d̄` vanishes only on equal orbits (it is symmetric and satisfies the triangle inequality). -/
theorem lemma2_4_a {X : Type*} [MetricSpace X] [LocallyCompactSpace X] (G : Subgroup (X ≃ₜ X))
    (hG : ∀ g ∈ G, Isometry (g : X → X)) (hpd : ProperlyDiscontinuousSMul G X)
    (p r : Quotient (MulAction.orbitRel G X)) : orbitDist p r = 0 → p = r := by
  intro h0
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  obtain ⟨A, hA⟩ := l24_seq hG x y h0
  by_contra hne
  have hne' : ∀ g : G, g • y ≠ x := by
    intro g hg
    exact hne ((Quotient.eq).2 ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨g, hg⟩)))
  have hrrT : Tendsto (fun k : ℕ => A k • y) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := l24_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_comm]
    exact (hA n).trans (lt_of_le_of_lt (l24_one_div_le hn) hN)
  obtain ⟨ε₁, hε₁, hiso⟩ := l23b_isolated G hpd x
  by_cases hfin : (Set.range A).Finite
  · obtain ⟨n₀, hn₀⟩ := l24_finite_zero x y hA hfin
    exact hne' (A n₀) hn₀.symm
  · obtain ⟨N₀, hN₀⟩ := l24_one_div_lt (show (0 : ℝ) < ε₁ / 6 by positivity)
    have hbound : ∀ m ≥ N₀, dist x (A m • y) < ε₁ / 6 :=
      fun m hm => (hA m).trans (lt_of_le_of_lt (l24_one_div_le hm) hN₀)
    have hstab : ∀ m ≥ N₀, (A m * (A N₀)⁻¹ : G) ∈ (MulAction.stabilizer G x : Set G) := by
      intro m hm
      have hc : Tendsto (fun k : ℕ => dist ((A m * (A N₀)⁻¹ : G) • (A k • y)) (A k • y)) atTop
          (𝓝 (dist ((A m * (A N₀)⁻¹ : G) • x) x)) := by
        have hcont : Continuous (fun z : X => (A m * (A N₀)⁻¹ : G) • z) :=
          ((A m * (A N₀)⁻¹ : G) : X ≃ₜ X).continuous
        exact Tendsto.dist ((hcont.tendsto x).comp hrrT) hrrT
      have hbound2 : ∀ᶠ k in atTop,
          dist ((A m * (A N₀)⁻¹ : G) • (A k • y)) (A k • y) ≤ 2 * ε₁ / 3 := by
        refine eventually_atTop.2 ⟨N₀, fun k hk => ?_⟩
        have he := l23a_estimate hG (g := A) (pp := fun _ : ℕ => y) (rr := fun n : ℕ => A n • y)
          (fun n => rfl) (A k • y) m N₀
        rw [dist_self, add_zero] at he
        have t1 : dist (A k • y) (A N₀ • y) < ε₁ / 3 := by
          have ht := dist_triangle (A k • y) x (A N₀ • y)
          rw [dist_comm (A k • y) x] at ht
          linarith [hbound k hk, hbound N₀ le_rfl]
        have t2 : dist (A m • y) (A k • y) < ε₁ / 3 := by
          have ht := dist_triangle (A m • y) x (A k • y)
          rw [dist_comm (A m • y) x] at ht
          linarith [hbound m hm, hbound k hk]
        linarith [he, t1, t2]
      have hlim : dist ((A m * (A N₀)⁻¹ : G) • x) x ≤ 2 * ε₁ / 3 :=
        le_of_tendsto_of_tendsto hc tendsto_const_nhds hbound2
      have hmem : ((A m * (A N₀)⁻¹ : G) • x) ∈ MulAction.orbit G x :=
        MulAction.mem_orbit_iff.2 ⟨_, rfl⟩
      by_cases hfix : (A m * (A N₀)⁻¹ : G) • x = x
      · exact MulAction.mem_stabilizer_iff.2 hfix
      · have hsep := hiso _ hmem hfix
        exfalso
        linarith
    have hInf : (Set.range A).Infinite := hfin
    have hIci : (A '' Set.Ici N₀).Infinite := by
      have hsub : Set.range A \ (A '' Set.Iio N₀) ⊆ A '' Set.Ici N₀ := by
        rintro v ⟨⟨n, rfl⟩, hnv⟩
        refine ⟨n, Set.mem_Ici.2 ?_, rfl⟩
        by_contra hlt
        rw [not_le] at hlt
        exact hnv ⟨n, Set.mem_Iio.2 hlt, rfl⟩
      exact (hInf.sdiff ((Set.finite_Iio N₀).image A)).mono hsub
    set emb := Set.Infinite.natEmbedding (A '' Set.Ici N₀) hIci with hemb
    have hfmem : ∀ n : ℕ, (emb n).1 * (A N₀)⁻¹ ∈ (MulAction.stabilizer G x : Set G) := by
      intro n
      obtain ⟨m, hmN, hmA⟩ := (emb n).2
      rw [← hmA]
      exact hstab m (Set.mem_Ici.1 hmN)
    have hfinj : Function.Injective fun n : ℕ => (emb n).1 * (A N₀)⁻¹ := by
      intro n n' hnn
      have h1 : (emb n).1 = (emb n').1 := mul_right_cancel hnn
      have h2 : emb n = emb n' := Subtype.ext h1
      exact emb.injective h2
    have hstabInf : (MulAction.stabilizer G x : Set G).Infinite :=
      Set.infinite_of_injective_forall_mem hfinj hfmem
    exact hstabInf (lemma2_3_b G hG hpd x).1

/-- `orbitDist` of two marked points is at most the distance of the representatives. -/
theorem l24g_orbitDist_le {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (x y : X) :
    orbitDist (Quotient.mk (MulAction.orbitRel G X) x) (Quotient.mk (MulAction.orbitRel G X) y) ≤
      dist x y := by
  have hne1 : Nonempty {a : X // Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x} := ⟨⟨x, rfl⟩⟩
  have hne2 : Nonempty {b : X // Quotient.mk (MulAction.orbitRel G X) b =
      Quotient.mk (MulAction.orbitRel G X) y} := ⟨⟨y, rfl⟩⟩
  unfold orbitDist
  have hbddy : ∀ x' : {a : X // Quotient.mk (MulAction.orbitRel G X) a =
        Quotient.mk (MulAction.orbitRel G X) x},
      BddBelow (Set.range (fun y' : {b : X // Quotient.mk (MulAction.orbitRel G X) b =
        Quotient.mk (MulAction.orbitRel G X) y} => dist x'.1 y'.1)) :=
    fun x' => ⟨0, fun z hz => by
      obtain ⟨y', rfl⟩ := hz
      exact dist_nonneg⟩
  have hbddx : BddBelow (Set.range (fun x' : {a : X // Quotient.mk (MulAction.orbitRel G X) a =
        Quotient.mk (MulAction.orbitRel G X) x} =>
      ⨅ (y' : {b : X // Quotient.mk (MulAction.orbitRel G X) b =
        Quotient.mk (MulAction.orbitRel G X) y}), dist x'.1 y'.1)) :=
    ⟨0, fun z hz => by
      obtain ⟨x', rfl⟩ := hz
      exact le_ciInf fun y' => dist_nonneg⟩
  exact (ciInf_le hbddx ⟨x, rfl⟩).trans (ciInf_le (hbddy ⟨x, rfl⟩) ⟨y, rfl⟩)

/-- `orbitDist` is nonnegative. -/
theorem l24g_orbitDist_nonneg {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (p r : Quotient (MulAction.orbitRel G X)) : 0 ≤ orbitDist p r := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  have hne1 : Nonempty {a : X // Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x} := ⟨⟨x, rfl⟩⟩
  have hne2 : Nonempty {b : X // Quotient.mk (MulAction.orbitRel G X) b =
      Quotient.mk (MulAction.orbitRel G X) y} := ⟨⟨y, rfl⟩⟩
  unfold orbitDist
  exact le_ciInf fun x' => le_ciInf fun y' => dist_nonneg

/-- Collapse of the double infimum to one orbit (isometry invariance). -/
theorem l24g_collapse {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z)) (x y : X) :
    orbitDist (Quotient.mk (MulAction.orbitRel G X) x) (Quotient.mk (MulAction.orbitRel G X) y) =
      ⨅ g : G, dist x (g • y) := by
  have hne1 : Nonempty {a : X // Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x} := ⟨⟨x, rfl⟩⟩
  have hne2 : Nonempty {b : X // Quotient.mk (MulAction.orbitRel G X) b =
      Quotient.mk (MulAction.orbitRel G X) y} := ⟨⟨y, rfl⟩⟩
  have hmk : ∀ g : G, Quotient.mk (MulAction.orbitRel G X) (g • y) =
      Quotient.mk (MulAction.orbitRel G X) y :=
    fun g => (Quotient.eq).2 ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩))
  have hbddG : BddBelow (Set.range fun g : G => dist x (g • y)) :=
    ⟨0, fun z hz => by
      obtain ⟨g, rfl⟩ := hz
      exact dist_nonneg⟩
  apply le_antisymm
  · unfold orbitDist
    have hbddx : BddBelow (Set.range (fun x' : {a : X // Quotient.mk (MulAction.orbitRel G X) a =
          Quotient.mk (MulAction.orbitRel G X) x} =>
        ⨅ (y' : {b : X // Quotient.mk (MulAction.orbitRel G X) b =
          Quotient.mk (MulAction.orbitRel G X) y}), dist x'.1 y'.1)) :=
      ⟨0, fun z hz => by
        obtain ⟨x', rfl⟩ := hz
        exact le_ciInf fun y' => dist_nonneg⟩
    have hbddy : BddBelow (Set.range (fun y' : {b : X // Quotient.mk (MulAction.orbitRel G X) b =
        Quotient.mk (MulAction.orbitRel G X) y} => dist x y'.1)) :=
      ⟨0, fun z hz => by
        obtain ⟨y', rfl⟩ := hz
        exact dist_nonneg⟩
    refine le_ciInf fun g => ?_
    exact (ciInf_le hbddx ⟨x, rfl⟩).trans (ciInf_le hbddy ⟨g • y, hmk g⟩)
  · unfold orbitDist
    refine le_ciInf fun x' => le_ciInf fun y' => ?_
    obtain ⟨g₁, hg₁⟩ := MulAction.mem_orbit_iff.1 ((MulAction.orbitRel_apply).1 ((Quotient.eq).1 x'.2))
    obtain ⟨g₂, hg₂⟩ := MulAction.mem_orbit_iff.1 ((MulAction.orbitRel_apply).1 ((Quotient.eq).1 y'.2))
    rw [← hg₁, ← hg₂, l24g_dist_smul hG g₁ g₂ x y]
    exact ciInf_le hbddG (g₁⁻¹ * g₂)

/-- Triangle inequality for `orbitDist` (via the collapse). -/
theorem l24g_triangle {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z))
    (p q r : Quotient (MulAction.orbitRel G X)) :
    orbitDist p r ≤ orbitDist p q + orbitDist q r := by
  have hneG : Nonempty G := ⟨1⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  obtain ⟨z, rfl⟩ := Quotient.exists_rep r
  rw [l24g_collapse hG x y, l24g_collapse hG y z, l24g_collapse hG x z]
  have hbdd1 : BddBelow (Set.range fun g : G => dist x (g • y)) :=
    ⟨0, fun t ht => by
      obtain ⟨g, rfl⟩ := ht
      exact dist_nonneg⟩
  have hbdd2 : BddBelow (Set.range fun g : G => dist y (g • z)) :=
    ⟨0, fun t ht => by
      obtain ⟨g, rfl⟩ := ht
      exact dist_nonneg⟩
  have hbdd3 : BddBelow (Set.range fun g : G => dist x (g • z)) :=
    ⟨0, fun t ht => by
      obtain ⟨g, rfl⟩ := ht
      exact dist_nonneg⟩
  have hb : BddBelow (Set.range fun p : G × G => dist x (p.1 • y) + dist y (p.2 • z)) :=
    ⟨0, fun t ht => by
      obtain ⟨⟨a, b⟩, rfl⟩ := ht
      exact add_nonneg dist_nonneg dist_nonneg⟩
  have hprod : (⨅ p : G × G, (dist x (p.1 • y) + dist y (p.2 • z))) =
      (⨅ g₁ : G, dist x (g₁ • y)) + (⨅ g₂ : G, dist y (g₂ • z)) := by
    apply le_antisymm
    · have hs1 : ∀ g₁ : G, (⨅ p : G × G, (dist x (p.1 • y) + dist y (p.2 • z))) - dist x (g₁ • y) ≤
          ⨅ g₂ : G, dist y (g₂ • z) := by
        intro g₁
        refine le_ciInf fun g₂ => ?_
        have h := ciInf_le hb (g₁, g₂)
        linarith
      have hs2 : (⨅ p : G × G, (dist x (p.1 • y) + dist y (p.2 • z))) - (⨅ g₂ : G, dist y (g₂ • z)) ≤
          ⨅ g₁ : G, dist x (g₁ • y) := by
        refine le_ciInf fun g₁ => ?_
        have h := hs1 g₁
        linarith
      linarith [hs2]
    · exact le_ciInf fun p => add_le_add (ciInf_le hbdd1 p.1) (ciInf_le hbdd2 p.2)
  rw [← hprod]
  refine le_ciInf fun p => ?_
  calc (⨅ g : G, dist x (g • z)) ≤ dist x ((p.1 * p.2) • z) := ciInf_le hbdd3 _
    _ ≤ dist x (p.1 • y) + dist (p.1 • y) ((p.1 * p.2) • z) := dist_triangle _ _ _
    _ = dist x (p.1 • y) + dist y (p.2 • z) := by
        rw [l24g_dist_smul hG p.1 (p.1 * p.2) y z, inv_mul_cancel_left]


/-- The projection to the orbit space is open: the saturation of an open set is a union of
homeomorphic images. -/
theorem l24b_isOpenMap {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) :
    IsOpenMap (Quotient.mk (MulAction.orbitRel G X)) := by
  intro U hU
  have hq : IsQuotientMap (Quotient.mk (MulAction.orbitRel G X)) := isQuotientMap_quotient_mk'
  rw [← hq.isCoinducing.isOpen_preimage]
  have hsat : Quotient.mk (MulAction.orbitRel G X) ⁻¹'
      (Quotient.mk (MulAction.orbitRel G X) '' U) =
      ⋃ g : G, ((g : X ≃ₜ X)) '' U := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, hum⟩ := hz
      have h := (Quotient.eq).1 hum
      rw [MulAction.orbitRel_apply] at h
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
      refine Set.mem_iUnion.2 ⟨g⁻¹, ⟨u, hu, ?_⟩⟩
      show (g⁻¹ : G) • u = z
      rw [← hg]
      exact inv_smul_smul g z
    · intro hz
      obtain ⟨g, ⟨u, hu, hz'⟩⟩ := Set.mem_iUnion.1 hz
      refine ⟨u, hu, ?_⟩
      have hz'' : (g : G) • u = z := hz'
      exact (Quotient.eq).2 ((MulAction.orbitRel_apply).2
        (MulAction.mem_orbit_iff.2 ⟨g⁻¹, by rw [← hz'']; exact inv_smul_smul g u⟩))
  rw [hsat]
  exact isOpen_iUnion fun g => (g : X ≃ₜ X).isOpen_image.2 hU

/-- The `orbitDist`-balls are exactly the neighbourhoods in the quotient topology. -/
theorem l24b_nhds_iff {X : Type*} [MetricSpace X] {G : Subgroup (X ≃ₜ X)}
    (hG : ∀ g ∈ G, Isometry (g : X → X))
    (p : Quotient (MulAction.orbitRel G X)) (s : Set (Quotient (MulAction.orbitRel G X))) :
    s ∈ 𝓝 p ↔ ∃ ε > (0 : ℝ), {r | orbitDist p r < ε} ⊆ s := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  constructor
  · intro hs
    have hpre : Quotient.mk (MulAction.orbitRel G X) ⁻¹' s ∈ 𝓝 x :=
      Quotient.preimage_mem_nhds (s := MulAction.orbitRel G X) hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hpre
    refine ⟨ε, hε, fun r hr => ?_⟩
    obtain ⟨y, rfl⟩ := Quotient.exists_rep r
    obtain ⟨g, hg⟩ := l24g_attain (fun g => hG _ (SetLike.coe_mem g)) x y hr
    have hmem : Quotient.mk (MulAction.orbitRel G X) (g • y) ∈ s := by
      apply hεs
      rw [Metric.mem_ball, dist_comm]
      exact hg
    have heq : Quotient.mk (MulAction.orbitRel G X) (g • y) =
        Quotient.mk (MulAction.orbitRel G X) y :=
      (Quotient.eq).2 ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩))
    rw [heq] at hmem
    exact hmem
  · rintro ⟨ε, hε, hεs⟩
    have hsub1 : Quotient.mk (MulAction.orbitRel G X) '' Metric.ball x ε ⊆
        {r | orbitDist (Quotient.mk (MulAction.orbitRel G X) x) r < ε} := by
      rintro r ⟨y, hy, rfl⟩
      exact (l24g_orbitDist_le x y).trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hy)
    exact mem_of_superset
      ((l24b_isOpenMap G (Metric.ball x ε) isOpen_ball).mem_nhds ⟨x, Metric.mem_ball_self hε, rfl⟩)
      (hsub1.trans hεs)

/-- **Lemma 4** (§2.7, l. 1733), the topology. `d̄` metrizes `X/G` (its balls are the neighbourhoods of the quotient
topology), and the projection `π : X → X/G` is open and continuous. -/
theorem lemma2_4_b {X : Type*} [MetricSpace X] [LocallyCompactSpace X] (G : Subgroup (X ≃ₜ X))
    (hG : ∀ g ∈ G, Isometry (g : X → X)) (hpd : ProperlyDiscontinuousSMul G X) :
    IsOpenMap (Quotient.mk (MulAction.orbitRel G X)) ∧ Continuous (Quotient.mk (MulAction.orbitRel G X)) ∧
      ∀ (p : Quotient (MulAction.orbitRel G X)) (s : Set (Quotient (MulAction.orbitRel G X))),
        s ∈ 𝓝 p ↔ ∃ ε > (0 : ℝ), {r | orbitDist p r < ε} ⊆ s := by
  exact ⟨l24b_isOpenMap G, continuous_quotient_mk', fun p s => l24b_nhds_iff hG p s⟩

/-- **Lemma 4** (§2.7, l. 1733), local homeomorphism. At a point with trivial isotropy group the projection is
injective on a neighbourhood (hence, being open and continuous, a local homeomorphism). -/
theorem lemma2_4_c {X : Type*} [MetricSpace X] [LocallyCompactSpace X] (G : Subgroup (X ≃ₜ X))
    (hG : ∀ g ∈ G, Isometry (g : X → X)) (hpd : ProperlyDiscontinuousSMul G X) {x : X}
    (hx : MulAction.stabilizer G x = ⊥) : ∃ U ∈ 𝓝 x, InjOn (Quotient.mk (MulAction.orbitRel G X)) U := by
  obtain ⟨ε₁, hε₁, hiso⟩ := l23b_isolated G hpd x
  refine ⟨Metric.ball x (ε₁ / 2), Metric.ball_mem_nhds x (by positivity), ?_⟩
  intro r₁ hr₁ r₂ hr₂ hmk
  have h := (Quotient.eq).1 hmk
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.1 h
  have hB : (A⁻¹ : G) • r₁ = r₂ := by
    rw [← hA]
    exact inv_smul_smul _ _
  have hI : ∀ h : G, Isometry ((h : X ≃ₜ X) : X → X) := fun h => hG _ (SetLike.coe_mem h)
  have key : dist x ((A⁻¹ : G) • x) < ε₁ := by
    have step1 : dist x ((A⁻¹ : G) • x) ≤ dist x r₂ + dist ((A⁻¹ : G) • r₁) ((A⁻¹ : G) • x) := by
      rw [← hB]
      exact dist_triangle _ _ _
    have step2 : dist ((A⁻¹ : G) • r₁) ((A⁻¹ : G) • x) = dist r₁ x := (hI A⁻¹).dist_eq r₁ x
    rw [step2] at step1
    have h1 : dist x r₂ < ε₁ / 2 := by
      rw [dist_comm]
      exact Metric.mem_ball.1 hr₂
    have h2 : dist r₁ x < ε₁ / 2 := Metric.mem_ball.1 hr₁
    linarith
  have hfix : (A⁻¹ : G) • x = x := by
    by_contra hne2
    have hsep := hiso _ (MulAction.mem_orbit_iff.2 ⟨A⁻¹, rfl⟩) hne2
    rw [dist_comm] at key
    linarith
  have hA1 : (A⁻¹ : G) = 1 := by
    have hm : (A⁻¹ : G) ∈ MulAction.stabilizer G x := MulAction.mem_stabilizer_iff.2 hfix
    rw [hx] at hm
    exact Subgroup.mem_bot.1 hm
  have hr : r₂ = r₁ := by
    rw [← hB, hA1, one_smul]
  exact hr.symm

/-- **Definition 11** (§2.7, l. 1771). `G` acting on `X` has the identity property: an element fixing a set of points
with an accumulation point in `X` is the identity (acts as the identity). -/
def HasIdentityProperty (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] : Prop :=
  ∀ g : G, ∀ S : Set X, (∃ x : X, AccPt x (𝓟 S)) → (∀ s ∈ S, g • s = s) → ∀ x : X, g • x = x

/-- **Definition 12** (§2.7, l. 1774). An elliptic point of `G` acting on `X`: a point whose isotropy group is
nontrivial (some element fixing it acts nontrivially). -/
def IsEllipticPoint {G X : Type*} [Group G] [MulAction G X] (p : X) : Prop :=
  ∃ g : G, g • p = p ∧ ∃ x : X, g • x ≠ x

/-- Propagation of fixedness to `p` inside the half-isolation ball (Lemma 4's penultimate
paragraph, group form): if `A` fixes a nearby `q` then `A` fixes `p`. -/
theorem l25_fixed_propagates {X : Type*} [MetricSpace X] {G : Subgroup (X ≃ₜ X)}
    (hG : ∀ g ∈ G, Isometry (g : X → X)) {p : X} {ρ : ℝ}
    (hρiso : ∀ y ∈ MulAction.orbit G p, dist y p < ρ → y = p)
    {A : G} {q : X} (hq : dist q p < ρ / 2) (hAq : A • q = q) : A • p = p := by
  have hI : ∀ h : G, Isometry ((h : X ≃ₜ X) : X → X) := fun h => hG _ (SetLike.coe_mem h)
  have hstep : dist p (A • p) < ρ := by
    have e : dist (A • q) (A • p) = dist q p := (hI A).dist_eq q p
    calc dist p (A • p) ≤ dist p q + dist q (A • p) := dist_triangle _ _ _
      _ = dist p q + dist (A • q) (A • p) := by rw [hAq]
      _ = dist p q + dist q p := by rw [e]
      _ < ρ / 2 + ρ / 2 := by
          have h1 : dist p q < ρ / 2 := by
            rw [dist_comm]
            exact hq
          have h2 : dist q p < ρ / 2 := hq
          linarith
      _ = ρ := by ring
  exact hρiso _ (MulAction.mem_orbit_iff.2 ⟨A, rfl⟩) (by
    rw [dist_comm]
    exact hstep)

/-- **Lemma 5** (§2.7, l. 1778). For a group of isometries with discrete orbits, finite isotropy groups and the
identity property, every point has an open neighbourhood `N` with `N ∖ {p}` free of elliptic points. -/
theorem lemma2_5 {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) (hG : ∀ g ∈ G, Isometry (g : X → X))
    (hdisc : ∀ x : X, DiscreteTopology (MulAction.orbit G x))
    (hfin : ∀ x : X, (MulAction.stabilizer G x : Set G).Finite) (hid : HasIdentityProperty G X) (p : X) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ ∀ q ∈ N, q ≠ p → ¬ IsEllipticPoint (G := G) q := by
  classical
  obtain ⟨ρ, hρ, hρiso⟩ := l23a_orbit_ball G (hdisc p)
  by_contra hN
  push_neg at hN
  have hball : ∀ n : ℕ, ∃ q : X, q ∈ Metric.ball p (min (ρ / 2) (1 / ((n : ℝ) + 1))) ∧ q ≠ p ∧
      IsEllipticPoint (G := G) q := fun n =>
    hN _ isOpen_ball (Metric.mem_ball_self (lt_min (by positivity) (by positivity)))
  choose q hq hqp hell using hball
  choose A hA using hell
  have hfix : ∀ n, (A n) • p = p := fun n =>
    l25_fixed_propagates hG hρiso (lt_of_lt_of_le (Metric.mem_ball.1 (hq n)) (min_le_left _ _))
      (hA n).1
  have hstabmem : ∀ n, A n ∈ (MulAction.stabilizer G p : Set G) := fun n =>
    MulAction.mem_stabilizer_iff.2 (hfix n)
  haveI : Finite ↥(MulAction.stabilizer G p : Set G) := Set.finite_coe_iff.2 (hfin p)
  set B := fun n => (⟨A n, hstabmem n⟩ : ↥(MulAction.stabilizer G p : Set G)) with hBdef
  obtain ⟨a₀, hT0⟩ := Finite.exists_infinite_fiber B
  -- a₀ : ↥(stabilizer G p); hT0 : Infinite ↥(B ⁻¹' {a₀})
  have hTA : ∀ n, B n = a₀ → A n = a₀.1 := fun n h => Subtype.ext_iff.1 h
  -- the accumulating fixed set
  set S := q '' (B ⁻¹' {a₀}) with hSdef
  have hacc : AccPt p (𝓟 S) := by
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨N, hNlt⟩ := l24_one_div_lt hε
    have hlarge : ∃ n ∈ B ⁻¹' {a₀}, N ≤ n := by
      by_contra h
      push_neg at h
      exact (Set.infinite_coe_iff.1 hT0)
        (Set.Finite.subset (Set.finite_Iio N) (fun n hn => Set.mem_Iio.2 (h n hn)))
    obtain ⟨n, hnT, hnN⟩ := hlarge
    have hdist : dist (q n) p < ε := by
      have h1 : dist (q n) p < 1 / ((n : ℝ) + 1) :=
        lt_of_lt_of_le (Metric.mem_ball.1 (hq n)) (min_le_right _ _)
      have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        refine (one_div_le_one_div (by positivity) (by positivity)).2 ?_
        have h : N + 1 ≤ n + 1 := by omega
        exact_mod_cast h
      exact h1.trans_le (h2.trans (le_of_lt hNlt))
    exact ⟨q n, ⟨(hεU (Metric.mem_ball.1 hdist)), ⟨n, hnT, rfl⟩⟩, hqp n⟩
  -- identity property kills the fiber value
  have htriv : ∀ x : X, (a₀.1 : G) • x = x := hid a₀.1 S ⟨p, hacc⟩ (by
    rintro s ⟨n, hnT, rfl⟩
    have hAn : A n = a₀.1 := hTA n (Set.mem_singleton_iff.1 hnT)
    rw [← hAn]
    exact (hA n).1)
  obtain ⟨n₀, hn₀⟩ := (Set.infinite_coe_iff.1 hT0).nonempty
  have hAn₀ : A n₀ = a₀.1 := hTA n₀ (Set.mem_singleton_iff.1 hn₀)
  obtain ⟨x₀, hx₀⟩ := (hA n₀).2
  rw [hAn₀] at hx₀
  exact hx₀ (htriv x₀)

/-- General-group form of `l23a_orbit_ball`: isolated orbit points. -/
theorem l25g_orbit_ball {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X] {b : X}
    (hdisc : DiscreteTopology (MulAction.orbit G b)) :
    ∃ ρ > 0, ∀ y ∈ MulAction.orbit G b, dist y b < ρ → y = b := by
  have hmemb : b ∈ MulAction.orbit G b := MulAction.mem_orbit_iff.2 ⟨1, one_smul _ _⟩
  have hopen1 : IsOpen ({⟨b, hmemb⟩} : Set (MulAction.orbit G b)) :=
    discreteTopology_iff_isOpen_singleton.1 hdisc ⟨b, hmemb⟩
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hopen1
  have hbV : b ∈ V := by
    have : ⟨b, hmemb⟩ ∈ Subtype.val ⁻¹' V := by rw [hV]; exact Set.mem_singleton _
    exact this
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hVo b hbV
  refine ⟨ρ, hρ, fun y hyo hyb => ?_⟩
  have hyV : y ∈ V := hρV hyb
  have hmem : (⟨y, hyo⟩ : MulAction.orbit G b) ∈ Subtype.val ⁻¹' V := hyV
  rw [hV] at hmem
  have := Set.mem_singleton_iff.1 hmem
  exact congrArg Subtype.val this

/-- General-group propagation of fixedness inside the half-isolation ball. -/
theorem l25g_fixed_propagates {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z)) {p : X} {ρ : ℝ}
    (hρiso : ∀ y ∈ MulAction.orbit G p, dist y p < ρ → y = p)
    {A : G} {q : X} (hq : dist q p < ρ / 2) (hAq : A • q = q) : A • p = p := by
  have hstep : dist p (A • p) < ρ := by
    have e : dist (A • q) (A • p) = dist q p := (hG A).dist_eq q p
    calc dist p (A • p) ≤ dist p q + dist q (A • p) := dist_triangle _ _ _
      _ = dist p q + dist (A • q) (A • p) := by rw [hAq]
      _ = dist p q + dist q p := by rw [e]
      _ < ρ / 2 + ρ / 2 := by
          have h1 : dist p q < ρ / 2 := by
            rw [dist_comm]
            exact hq
          have h2 : dist q p < ρ / 2 := hq
          linarith
      _ = ρ := by ring
  exact hρiso _ (MulAction.mem_orbit_iff.2 ⟨A, rfl⟩) (by
    rw [dist_comm]
    exact hstep)

/-- General-group form of `l23b_isolated`: uniform isolation of orbit points from pd. -/
theorem l25g_isolated {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {G : Type*} [Group G]
    [MulAction G X] (hpd : ProperlyDiscontinuousSMul G X) (x : X) :
    ∃ ε > 0, ∀ y ∈ MulAction.orbit G x, y ≠ x → ε ≤ dist y x := by
  classical
  obtain ⟨K, ⟨hKn, hKc⟩, -⟩ := ((compact_basis_nhds x).mem_iff).1 (isOpen_univ.mem_nhds trivial)
  obtain ⟨ε₀, hε₀, hε₀K⟩ := Metric.mem_nhds_iff.1 hKn
  set C := closedBall x (ε₀ / 2) with hCdef
  have hCK : C ⊆ K := (closedBall_subset_ball (by linarith)).trans hε₀K
  have hCc : IsCompact C := hKc.of_isClosed_subset isClosed_closedBall hCK
  have hF : ({g : G | ((g • ·) '' C ∩ C).Nonempty}).Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) (T := X) (K := C) (L := C) hCc hCc
  set P : Finset ℝ := (hF.toFinset.filter fun g : G => ¬ g • x = x).image fun g : G =>
    dist (g • x) x with hPdef
  by_cases hP : P.Nonempty
  · have hε₁ : (0 : ℝ) < P.min' hP := by
      have hmem := P.min'_mem hP
      simp only [hPdef, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset] at hmem
      obtain ⟨g, ⟨-, hgx⟩, hgd⟩ := hmem
      rw [← hgd]
      exact dist_pos.2 hgx
    refine ⟨min (ε₀ / 2) (P.min' hP), lt_min (by positivity) hε₁, fun y hy hne => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    by_cases hgF : g ∈ {g : G | ((g • ·) '' C ∩ C).Nonempty}
    · have hmem : dist (g • x) x ∈ P := by
        simp only [hPdef, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨g, ⟨hgF, hne⟩, rfl⟩
      exact (min_le_right _ _).trans (P.min'_le _ hmem)
    · have hgnC : g • x ∉ C := by
        intro hgxC
        exact hgF ⟨g • x, ⟨x, mem_closedBall_self (by linarith), rfl⟩, hgxC⟩
      rw [hCdef, mem_closedBall, not_le] at hgnC
      exact (min_le_left _ _).trans hgnC.le
  · refine ⟨ε₀ / 2, by positivity, fun y hy hne => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    have hgF : g ∉ {g : G | ((g • ·) '' C ∩ C).Nonempty} := by
      intro hgF
      have hfil : g ∈ hF.toFinset.filter (fun g : G => ¬ g • x = x) := by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hgF, hne⟩
      exact hP (Finset.image_nonempty.2 ⟨_, hfil⟩)
    have hgnC : g • x ∉ C := by
      intro hgxC
      exact hgF ⟨g • x, ⟨x, mem_closedBall_self (by linarith), rfl⟩, hgxC⟩
    rw [hCdef, mem_closedBall, not_le] at hgnC
    exact hgnC.le

/-- General-group form of Lemma 3's discreteness clause: pd + isometries ⟹ discrete orbits. -/
theorem l25g_orbit_discrete {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {G : Type*} [Group G]
    [MulAction G X] (hG : ∀ g : G, Isometry (fun z : X => g • z))
    (hpd : ProperlyDiscontinuousSMul G X) (x : X) :
    DiscreteTopology (MulAction.orbit G x) := by
  obtain ⟨ε, hε, hεprop⟩ := l25g_isolated hpd x
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨g₀, hg₀⟩ := MulAction.mem_orbit_iff.1 q.2
  rw [isOpen_induced_iff]
  refine ⟨Metric.ball (q : X) ε, isOpen_ball, ?_⟩
  ext ⟨y, hy⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball]
  constructor
  · intro hd
    apply Subtype.ext
    have hxq : (g₀⁻¹ : G) • (q : X) = x := by
      rw [← hg₀]
      exact inv_smul_smul _ _
    have h1 : (g₀⁻¹ : G) • y ∈ MulAction.orbit G x := by
      obtain ⟨h', hh'⟩ := MulAction.mem_orbit_iff.1 hy
      rw [MulAction.mem_orbit_iff]
      exact ⟨(g₀⁻¹ : G) * h', by rw [mul_smul, hh']⟩
    by_cases hcon : (g₀⁻¹ : G) • y = x
    · have hyy : y = g₀ • x := by
        have hcc := congrArg ((g₀ : G) • ·) hcon
        rwa [smul_inv_smul] at hcc
      exact hyy.trans hg₀
    · have h2 := hεprop ((g₀⁻¹ : G) • y) h1 hcon
      have hdist : dist ((g₀⁻¹ : G) • y) x = dist y (q : X) := by
        calc dist ((g₀⁻¹ : G) • y) x
            = dist ((g₀⁻¹ : G) • y) ((g₀⁻¹ : G) • (q : X)) := by
              exact (congrArg (fun u => dist ((g₀⁻¹ : G) • y) u) hxq).symm
          _ = dist y (q : X) := (hG g₀⁻¹).dist_eq _ _
      rw [hdist] at h2
      exact absurd (h2.trans_lt hd) (lt_irrefl _)
  · intro hd
    have hyq : y = (q : X) := congrArg Subtype.val hd
    rw [hyq, dist_self]
    exact hε

/-- General-group Lemma 5: near `p`, all other points are nonelliptic. -/
theorem l25g_nonelliptic_nhd {X : Type*} [MetricSpace X] {G : Type*} [Group G] [MulAction G X]
    (hG : ∀ g : G, Isometry (fun z : X => g • z))
    (hdisc : ∀ x : X, DiscreteTopology (MulAction.orbit G x))
    (hfin : ∀ x : X, (MulAction.stabilizer G x : Set G).Finite) (hid : HasIdentityProperty G X)
    (p : X) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ ∀ q ∈ N, q ≠ p → ¬ IsEllipticPoint (G := G) q := by
  classical
  obtain ⟨ρ, hρ, hρiso⟩ := l25g_orbit_ball (hdisc p)
  by_contra hN
  push Not at hN
  have hball : ∀ n : ℕ, ∃ q : X, q ∈ Metric.ball p (min (ρ / 2) (1 / ((n : ℝ) + 1))) ∧ q ≠ p ∧
      IsEllipticPoint (G := G) q := fun n =>
    hN _ isOpen_ball (Metric.mem_ball_self (lt_min (by positivity) (by positivity)))
  choose q hq hqp hell using hball
  choose A hA using hell
  have hfix : ∀ n, (A n) • p = p := fun n =>
    l25g_fixed_propagates hG hρiso (lt_of_lt_of_le (Metric.mem_ball.1 (hq n)) (min_le_left _ _))
      (hA n).1
  have hstabmem : ∀ n, A n ∈ (MulAction.stabilizer G p : Set G) := fun n =>
    MulAction.mem_stabilizer_iff.2 (hfix n)
  have : Finite ↥(MulAction.stabilizer G p : Set G) := Set.finite_coe_iff.2 (hfin p)
  set B := fun n => (⟨A n, hstabmem n⟩ : ↥(MulAction.stabilizer G p : Set G)) with hBdef
  obtain ⟨a₀, hT0⟩ := Finite.exists_infinite_fiber B
  have hTA : ∀ n, B n = a₀ → A n = a₀.1 := fun n h => Subtype.ext_iff.1 h
  set S := q '' (B ⁻¹' {a₀}) with hSdef
  have hacc : AccPt p (𝓟 S) := by
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨N, hNlt⟩ := l24_one_div_lt hε
    have hlarge : ∃ n ∈ B ⁻¹' {a₀}, N ≤ n := by
      by_contra h
      push Not at h
      exact (Set.infinite_coe_iff.1 hT0)
        (Set.Finite.subset (Set.finite_Iio N) (fun n hn => Set.mem_Iio.2 (h n hn)))
    obtain ⟨n, hnT, hnN⟩ := hlarge
    have hdist : dist (q n) p < ε := by
      have h1 : dist (q n) p < 1 / ((n : ℝ) + 1) :=
        lt_of_lt_of_le (Metric.mem_ball.1 (hq n)) (min_le_right _ _)
      have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := l24_one_div_le hnN
      exact h1.trans_le (h2.trans (le_of_lt hNlt))
    exact ⟨q n, ⟨(hεU (Metric.mem_ball.1 hdist)), ⟨n, hnT, rfl⟩⟩, hqp n⟩
  have htriv : ∀ x : X, (a₀.1 : G) • x = x := hid a₀.1 S ⟨p, hacc⟩ (by
    rintro s ⟨n, hnT, rfl⟩
    have hAn : A n = a₀.1 := hTA n (Set.mem_singleton_iff.1 hnT)
    rw [← hAn]
    exact (hA n).1)
  obtain ⟨n₀, hn₀⟩ := (Set.infinite_coe_iff.1 hT0).nonempty
  have hAn₀ : A n₀ = a₀.1 := hTA n₀ (Set.mem_singleton_iff.1 hn₀)
  obtain ⟨x₀, hx₀⟩ := (hA n₀).2
  rw [hAn₀] at hx₀
  exact hx₀ (htriv x₀)

/-- A set with an accumulation point is infinite (metric form). -/
theorem l25g_infinite_of_accPt {X : Type*} [MetricSpace X] {S : Set X} {x : X}
    (hacc : AccPt x (𝓟 S)) : S.Infinite := by
  rw [accPt_iff_nhds] at hacc
  by_contra hnf
  have hfin : S.Finite := by
    by_contra h
    exact hnf h
  by_cases hem : (S \ {x}).Nonempty
  · classical
    set F := ((hfin.sdiff (t := {x})).toFinset).image (fun s => dist s x) with hFdef
    have hFne : F.Nonempty := by
      obtain ⟨y, hy⟩ := hem
      exact ⟨dist y x, Finset.mem_image.2 ⟨y, (Set.Finite.mem_toFinset _).2 hy, rfl⟩⟩
    have hpos : 0 < F.min' hFne := by
      have hmem := F.min'_mem hFne
      simp only [hFdef, Finset.mem_image, Set.Finite.mem_toFinset] at hmem
      obtain ⟨y, hy, hye⟩ := hmem
      rw [← hye]
      exact dist_pos.2 (fun h => hy.2 (Set.mem_singleton_iff.2 h))
    obtain ⟨y, hyU, hyx⟩ := hacc (Metric.ball x (F.min' hFne)) (Metric.ball_mem_nhds x hpos)
    have hyS : y ∈ S \ {x} := ⟨hyU.2, fun h => hyx (Set.mem_singleton_iff.1 h)⟩
    have hle : F.min' hFne ≤ dist y x := by
      refine F.min'_le _ ?_
      simp only [hFdef, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨y, hyS, rfl⟩
    exact (lt_irrefl _) (lt_of_lt_of_le (Metric.mem_ball.1 hyU.1) hle)
  · rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hem
    obtain ⟨y, hyU, hyx⟩ := hacc (Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    exact hyx (Set.mem_singleton_iff.1 (hem hyU.2))

/-- The Möbius denominator never vanishes on `ℍ` (the `l22_smul_self_iff` idiom). -/
theorem t22b_denom_ne_zero {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (z : UpperHalfPlane) :
    ((δ 1 0 : ℂ) * (z : ℂ) + δ 1 1) ≠ 0 := by
  intro h0
  have hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) ℝ) = 1 := δ.2
  have hz : 0 < (z : ℂ).im := z.coe_im_pos
  have him : ((δ 1 0 : ℂ) * (z : ℂ) + (δ 1 1 : ℂ)).im = δ 1 0 * (z : ℂ).im := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_im]
    ring
  have e : δ 1 0 * (z : ℂ).im = 0 := by
    have e := congrArg Complex.im h0
    rw [him, Complex.zero_im] at e
    exact e
  have hc0 : δ 1 0 = 0 := by
    rcases mul_eq_zero.1 e with h | h
    · exact h
    · exact absurd h hz.ne'
  have hre : ((δ 1 0 : ℂ) * (z : ℂ) + (δ 1 1 : ℂ)).re = δ 1 0 * (z : ℂ).re + δ 1 1 := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  have hd0 : δ 1 1 = 0 := by
    have e := congrArg Complex.re h0
    rw [hre, hc0, Complex.zero_re] at e
    simpa using e
  rw [Matrix.det_fin_two, hd0, hc0, mul_zero, mul_zero, sub_zero] at hdet
  exact one_ne_zero hdet.symm

/-- A Möbius element of `SL(2,ℝ)` fixing three distinct points of `ℍ` acts trivially on `ℍ`. -/
theorem t22b_trivial_of_three_fixed {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {z₁ z₂ z₃ : UpperHalfPlane} (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h13 : z₁ ≠ z₃)
    (h1 : δ • z₁ = z₁) (h2 : δ • z₂ = z₂) (h3 : δ • z₃ = z₃) :
    ∀ x : UpperHalfPlane, δ • x = x := by
  have key : ∀ w : UpperHalfPlane, δ • w = w → LiZhongQC.h36p_m δ (w : ℂ) = (w : ℂ) :=
    fun w hw => by
      rw [LiZhongQC.h36p_m_coe, hw]
  have eq1 := key z₁ h1
  have eq2 := key z₂ h2
  have eq3 := key z₃ h3
  rw [LiZhongQC.h36p_m, div_eq_iff (t22b_denom_ne_zero z₁)] at eq1
  rw [LiZhongQC.h36p_m, div_eq_iff (t22b_denom_ne_zero z₂)] at eq2
  rw [LiZhongQC.h36p_m, div_eq_iff (t22b_denom_ne_zero z₃)] at eq3
  have h12' : (z₁ : ℂ) ≠ z₂ := fun h => h12 (UpperHalfPlane.coe_injective h)
  have h23' : (z₂ : ℂ) ≠ z₃ := fun h => h23 (UpperHalfPlane.coe_injective h)
  have h13' : (z₁ : ℂ) ≠ z₃ := fun h => h13 (UpperHalfPlane.coe_injective h)
  have f12 : (δ 1 0 : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((δ 1 1 : ℂ) - (δ 0 0 : ℂ)) = 0 := by
    have hprod : ((δ 1 0 : ℂ) * ((z₁ : ℂ) + (z₂ : ℂ)) + ((δ 1 1 : ℂ) - (δ 0 0 : ℂ))) *
        ((z₁ : ℂ) - (z₂ : ℂ)) = 0 := by
      linear_combination -(eq1 - eq2)
    rcases mul_eq_zero.1 hprod with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) h12'
  have f13 : (δ 1 0 : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((δ 1 1 : ℂ) - (δ 0 0 : ℂ)) = 0 := by
    have hprod : ((δ 1 0 : ℂ) * ((z₁ : ℂ) + (z₃ : ℂ)) + ((δ 1 1 : ℂ) - (δ 0 0 : ℂ))) *
        ((z₁ : ℂ) - (z₃ : ℂ)) = 0 := by
      linear_combination -(eq1 - eq3)
    rcases mul_eq_zero.1 hprod with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) h13'
  have hcC : (δ 1 0 : ℂ) * ((z₂ : ℂ) - (z₃ : ℂ)) = 0 := by linear_combination f12 - f13
  have hc0 : δ 1 0 = 0 := by
    rcases mul_eq_zero.1 hcC with h | h
    · exact_mod_cast h
    · exact absurd (sub_eq_zero.1 h) h23'
  have hc0' : (δ 1 0 : ℂ) = 0 := by exact_mod_cast hc0
  have hd_eq : δ 1 1 = δ 0 0 := by
    have h := f12
    rw [hc0', zero_mul, zero_add] at h
    exact_mod_cast sub_eq_zero.1 h
  have hd' : (δ 1 1 : ℂ) = (δ 0 0 : ℂ) := by exact_mod_cast hd_eq
  have hb0 : δ 0 1 = 0 := by
    rw [hc0', hd'] at eq1
    have hbC : (δ 0 1 : ℂ) = 0 := by linear_combination eq1
    exact_mod_cast hbC
  have hb0' : (δ 0 1 : ℂ) = 0 := by exact_mod_cast hb0
  have hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) ℝ) = 1 := δ.2
  have ha2 : δ 0 0 * δ 0 0 = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, hb0, hc0, hd_eq, zero_mul, sub_zero] at h
    exact h
  have ha0 : δ 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha2
    exact zero_ne_one ha2
  have ha0' : ((δ 0 0 : ℂ)) ≠ 0 := by exact_mod_cast ha0
  intro x
  apply UpperHalfPlane.coe_injective
  rw [← LiZhongQC.h36p_m_coe, LiZhongQC.h36p_m, hb0', hc0', hd', add_zero, zero_mul, zero_add,
    div_eq_iff ha0']
  ring

/-- The identity property for a Fuchsian group acting on `ℍ`. -/
theorem t22b_identity_property {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} :
    HasIdentityProperty Γ UpperHalfPlane := by
  classical
  intro γ S hacc hfix
  obtain ⟨xp, hacc⟩ := hacc
  have hSinf : S.Infinite := l25g_infinite_of_accPt hacc
  obtain ⟨z₁, hz₁⟩ := hSinf.nonempty
  obtain ⟨z₂, hz₂⟩ := ((hSinf.sdiff (Set.finite_singleton z₁)).nonempty)
  obtain ⟨z₃, hz₃⟩ := (((hSinf.sdiff (Set.finite_singleton z₁)).sdiff (Set.finite_singleton z₂)).nonempty)
  have h1 : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z₁ = z₁ :=
    (Subgroup.smul_def γ z₁).symm.trans (hfix z₁ hz₁)
  have h2 : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z₂ = z₂ :=
    (Subgroup.smul_def γ z₂).symm.trans (hfix z₂ hz₂.1)
  have h3 : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z₃ = z₃ :=
    (Subgroup.smul_def γ z₃).symm.trans (hfix z₃ hz₃.1.1)
  have h12 : z₁ ≠ z₂ := fun h => hz₂.2 (Set.mem_singleton_iff.2 h.symm)
  have h23 : z₂ ≠ z₃ := fun h => hz₃.2 (Set.mem_singleton_iff.2 h.symm)
  have h13 : z₁ ≠ z₃ := fun h => hz₃.1.2 (Set.mem_singleton_iff.2 h.symm)
  have htriv : ∀ x : UpperHalfPlane, (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x = x :=
    t22b_trivial_of_three_fixed h12 h23 h13 h1 h2 h3
  intro x
  rw [Subgroup.smul_def]
  exact htriv x

/-- Isotropy groups of a Fuchsian group are finite (from the compact singleton). -/
theorem t22b_stab_finite {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (τ : UpperHalfPlane) : (MulAction.stabilizer Γ τ : Set Γ).Finite := by
  have hF := hΓ {τ} isCompact_singleton
  refine Set.Finite.of_finite_image ?_ Subtype.coe_injective.injOn
  have himg : Subtype.val '' (MulAction.stabilizer Γ τ : Set Γ) =
      {γ ∈ Γ | ((γ • ·) '' {τ} ∩ {τ}).Nonempty} := by
    ext γ
    constructor
    · rintro ⟨⟨γ', hγ'⟩, hstab, rfl⟩
      have hstab' := MulAction.mem_stabilizer_iff.1 (SetLike.mem_coe.1 hstab)
      refine ⟨hγ', ?_⟩
      exact ⟨τ, ⟨τ, Set.mem_singleton τ, hstab'⟩, Set.mem_singleton τ⟩
    · rintro ⟨hγΓ, hne⟩
      refine ⟨⟨γ, hγΓ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      rw [Set.inter_singleton_nonempty] at hne
      obtain ⟨x, hxτ, hx⟩ := (Set.mem_image _ _ _).1 hne
      rw [Set.mem_singleton_iff.1 hxτ] at hx
      exact hx
  rw [himg]
  exact hF

/-- **Theorem 2** (§2.7, l. 1784), completeness. For a Fuchsian group `Γ`, `ℍ/Γ` with the quotient metric (2.24) is
complete. -/
theorem thm2_2_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (u : ℕ → Quotient (MulAction.orbitRel Γ UpperHalfPlane))
    (hu : ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, orbitDist (u m) (u n) < ε) :
    ∃ q, Tendsto (fun n => orbitDist (u n) q) atTop (𝓝 0) := by
  classical
  have hIso : ∀ γ : Γ, Isometry (fun τ : UpperHalfPlane => γ • τ) := by
    intro γ
    have h := isometry_smul UpperHalfPlane (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    exact h
  obtain ⟨N₀, hN₀⟩ := hu 1 one_pos
  obtain ⟨p₀, hp₀⟩ := Quotient.exists_rep (u N₀)
  have hkey : ∀ k : ℕ, ∃ z : UpperHalfPlane,
      Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) z = u (k + N₀) ∧ dist p₀ z < 1 := by
    intro k
    obtain ⟨y, hy⟩ := Quotient.exists_rep (u (k + N₀))
    have hlt : orbitDist (u N₀) (u (k + N₀)) < 1 := hN₀ N₀ le_rfl (k + N₀) (Nat.le_add_left N₀ k)
    rw [← hp₀, ← hy] at hlt
    obtain ⟨g, hg⟩ := l24g_attain hIso p₀ y hlt
    refine ⟨g • y, ?_, hg⟩
    rw [← hy]
    exact (Quotient.eq).2 ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩))
  choose z hzk hz1 using hkey
  have hmem : ∀ k, z k ∈ Metric.closedBall p₀ 1 := fun k => by
    rw [Metric.mem_closedBall, dist_comm]
    exact (hz1 k).le
  obtain ⟨a, -, φ, hφmono, hφT⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) a, ?_⟩
  rw [← tendsto_add_atTop_iff_nat N₀, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hu (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hφT (ε / 2) (by positivity)
  refine ⟨N₁, fun n hn => ?_⟩
  have hk₀ : N₁ ≤ φ (max K N₁) := (le_max_right K N₁).trans (hφmono.id_le _)
  have h1 : orbitDist (u (n + N₀)) (u (φ (max K N₁) + N₀)) < ε / 2 :=
    hN₁ (n + N₀) (hn.trans (Nat.le_add_right n N₀)) (φ (max K N₁) + N₀)
      (hk₀.trans (Nat.le_add_right _ _))
  have h2 : orbitDist (u (φ (max K N₁) + N₀)) (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) a) <
      ε / 2 := by
    rw [← hzk (φ (max K N₁))]
    exact lt_of_le_of_lt (l24g_orbitDist_le _ _) (hK (max K N₁) (le_max_left K N₁))
  have htri := l24g_triangle hIso (u (n + N₀)) (u (φ (max K N₁) + N₀))
    (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) a)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (l24g_orbitDist_nonneg _ _)]
  linarith [htri, h1, h2]

/-- **Theorem 2** (§2.7, l. 1784), the elliptic points of a Fuchsian group form a discrete set (they do not
accumulate in `ℍ`). -/
theorem thm2_2_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (τ : UpperHalfPlane) :
    ¬ AccPt τ (𝓟 {σ : UpperHalfPlane | IsEllipticPoint (G := Γ) σ}) := by
  have : DiscreteTopology Γ := (prop2_4 Γ).mpr hΓ
  have : ProperlyDiscontinuousSMul Γ UpperHalfPlane :=
    UpperHalfPlane.instProperlyDiscontinuousSL2RSubgroup Γ
  have hIso : ∀ γ : Γ, Isometry (fun σ : UpperHalfPlane => γ • σ) := by
    intro γ
    have h := isometry_smul UpperHalfPlane (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    exact h
  have hdisc : ∀ σ : UpperHalfPlane, DiscreteTopology (MulAction.orbit Γ σ) := fun σ =>
    l25g_orbit_discrete hIso inferInstance σ
  have hfin : ∀ σ : UpperHalfPlane, (MulAction.stabilizer Γ σ : Set Γ).Finite := fun σ =>
    t22b_stab_finite hΓ σ
  obtain ⟨N, hNo, hNmem, hNprop⟩ :=
    l25g_nonelliptic_nhd (G := Γ) hIso hdisc hfin t22b_identity_property τ
  rw [accPt_iff_nhds]
  push Not
  refine ⟨N, hNo.mem_nhds hNmem, fun y hy => ?_⟩
  by_contra hyτ
  exact hNprop y hy.1 hyτ hy.2

/-- Helper for **Theorem 2** (§2.7, l. 1784). The charted structure `c` on `ℍ/Γ` is a complex structure (analytic
atlas) for which the projection `π : ℍ → ℍ/Γ` is holomorphic. -/
def IsQuotientComplexStructure (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (c : ChartedSpace ℂ (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) : Prop :=
  letI := c
  IsManifold 𝓘(ℂ) ω (Quotient (MulAction.orbitRel Γ UpperHalfPlane)) ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane))

/-- Helper for **Theorem 2** (§2.7, l. 1784). The function `u` is holomorphic on `U` for the charted structure `c`. -/
def IsHolomorphicOnFor {Q : Type*} [TopologicalSpace Q] (c : ChartedSpace ℂ Q) (u : Q → ℂ) (U : Set Q) : Prop :=
  letI := c
  MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) u U

/-- **Theorem 2** (§2.7, l. 1784), the complex structure. There is a complex structure on `ℍ/Γ` making it a Riemann
surface and `π : ℍ → ℍ/Γ` holomorphic, and it is unique: two such structures have the same holomorphic functions on
every open set. -/
theorem thm2_2_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    (∃ c, IsQuotientComplexStructure Γ c) ∧
      ∀ c₁ c₂, IsQuotientComplexStructure Γ c₁ → IsQuotientComplexStructure Γ c₂ →
        ∀ (U : Set (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
          (u : Quotient (MulAction.orbitRel Γ UpperHalfPlane) → ℂ), IsOpen U →
          (IsHolomorphicOnFor c₁ u U ↔ IsHolomorphicOnFor c₂ u U) := by
  sorry

/-- Sign change does not change the induced map of an `SL(2,ℝ)` element on `ℍ`. -/
theorem t22d_neg_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : UpperHalfPlane) :
    (-γ) • x = γ • x := by
  apply UpperHalfPlane.coe_injective
  rw [← LiZhongQC.h36p_m_coe, ← LiZhongQC.h36p_m_coe, LiZhongQC.h36p_m, LiZhongQC.h36p_m]
  have e : ∀ i j : Fin 2, ((-γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) i j : ℂ) = -(γ i j : ℂ) := by
    intro i j
    show (((-γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ) = _
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
  rw [e, e, e, e]
  simp only [neg_mul]
  rw [← neg_add, ← neg_add, neg_div_neg_eq]

/-- **Theorem 2** (§2.7, l. 1784), local behaviour of `π`. Near `τ`, `π` is `n`-to-`1` off `τ`, `n` the number of
transformations of `Γ` fixing `τ` (the order of the isotropy group); at a nonelliptic point (`n = 1`) it is injective
near `τ`, hence a local homeomorphism. -/
theorem thm2_2_d {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (τ : UpperHalfPlane) :
    ∃ U ∈ 𝓝 τ,
      (∀ σ ∈ U, σ ≠ τ → {σ' ∈ U | Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ' =
          Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ}.ncard =
        {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)}.ncard) ∧
      ({h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)}.ncard = 1 →
        InjOn (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane)) U) := by
  classical
  have hIso : ∀ γ : Γ, Isometry (fun σ : UpperHalfPlane => γ • σ) := by
    intro γ
    have h := isometry_smul UpperHalfPlane (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    exact h
  have : DiscreteTopology Γ := (prop2_4 Γ).mpr hΓ
  have : ProperlyDiscontinuousSMul Γ UpperHalfPlane :=
    UpperHalfPlane.instProperlyDiscontinuousSL2RSubgroup Γ
  have hdisc : ∀ σ : UpperHalfPlane, DiscreteTopology (MulAction.orbit Γ σ) := fun σ =>
    l25g_orbit_discrete hIso inferInstance σ
  have hfin : ∀ σ : UpperHalfPlane, (MulAction.stabilizer Γ σ : Set Γ).Finite := fun σ =>
    t22b_stab_finite hΓ σ
  obtain ⟨ρ, hρ, hρiso⟩ := l25g_orbit_ball (G := Γ) (hdisc τ)
  obtain ⟨N, hNo, hNmem, hNprop⟩ :=
    l25g_nonelliptic_nhd (G := Γ) hIso hdisc hfin t22b_identity_property τ
  set Sτ := (MulAction.stabilizer Γ τ : Set Γ) with hSτdef
  have hSfin : Sτ.Finite := hfin τ
  set N' := ⋂ γ ∈ Sτ, ((γ : Γ) • ·) ⁻¹' N with hN'def
  have hN'open : IsOpen N' := by
    rw [hN'def]
    exact hSfin.isOpen_biInter fun γ _ => IsOpen.preimage (hIso γ).lipschitzWith.continuous hNo
  have hτN' : τ ∈ N' := by
    rw [hN'def, Set.mem_iInter₂]
    intro γ hγ
    have hγτ : (γ : Γ) • τ = τ := MulAction.mem_stabilizer_iff.1 (SetLike.mem_coe.1 hγ)
    rw [Set.mem_preimage, hγτ]
    exact hNmem
  have hN'N : N' ⊆ N := by
    intro z hz
    rw [hN'def] at hz
    have h1 : (1 : Γ) ∈ Sτ := SetLike.mem_coe.2 (MulAction.mem_stabilizer_iff.2 (one_smul _ _))
    have := Set.mem_iInter₂.1 hz 1 h1
    rwa [Set.mem_preimage, one_smul] at this
  have hN'inv : ∀ γ ∈ Sτ, ∀ z ∈ N', (γ : Γ) • z ∈ N' := by
    intro δ hδ z hz
    rw [hN'def] at hz
    rw [hN'def, Set.mem_iInter₂]
    intro γ hγ
    rw [Set.mem_preimage]
    show (γ : Γ) • ((δ : Γ) • z) ∈ N
    rw [← mul_smul]
    exact Set.mem_iInter₂.1 hz (γ * δ)
      (SetLike.mem_coe.2 (MulMemClass.mul_mem (SetLike.mem_coe.1 hγ) (SetLike.mem_coe.1 hδ)))
  set U := Metric.ball τ (ρ / 6) ∩ N' with hUdef
  have hUU : U ∈ 𝓝 τ := inter_mem (Metric.ball_mem_nhds τ (by positivity)) (hN'open.mem_nhds hτN')
  -- the key upgrade: movers inside U fix τ
  have hkey : ∀ σ σ' : UpperHalfPlane, σ ∈ U → σ' ∈ U →
      Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ' =
        Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ →
      ∃ δ : Γ, δ • σ = σ' ∧ (δ : Γ) • τ = τ := by
    intro σ σ' hσU hσ'U hmk
    have h := (Quotient.eq).1 hmk
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.1 h
    refine ⟨δ, hδ, ?_⟩
    have hσball : dist σ τ < ρ / 6 := Metric.mem_ball.1 hσU.1
    have hσ'ball : dist σ' τ < ρ / 6 := Metric.mem_ball.1 hσ'U.1
    have h1 : dist ((δ⁻¹ : Γ) • τ) τ < ρ := by
      have e : dist ((δ⁻¹ : Γ) • τ) σ = dist τ (δ • σ) := by
        have hdd := (hIso δ⁻¹).dist_eq τ (δ • σ)
        rw [inv_smul_smul] at hdd
        exact hdd
      calc dist ((δ⁻¹ : Γ) • τ) τ ≤ dist ((δ⁻¹ : Γ) • τ) σ + dist σ τ := dist_triangle _ _ _
        _ = dist τ (δ • σ) + dist σ τ := by rw [e]
        _ = dist τ σ' + dist σ τ := by rw [hδ]
        _ < ρ / 6 + ρ / 6 := by
          have a1 : dist τ σ' < ρ / 6 := by
            rw [dist_comm]
            exact hσ'ball
          linarith [hσball, a1]
        _ = ρ / 3 := by ring
        _ < ρ := by linarith
    have hmem : (δ⁻¹ : Γ) • τ ∈ MulAction.orbit Γ τ := MulAction.mem_orbit_iff.2 ⟨δ⁻¹, rfl⟩
    have h2 := hρiso _ hmem h1
    have h3 := congrArg (fun z => (δ : Γ) • z) h2
    rw [smul_inv_smul] at h3
    exact h3.symm
  refine ⟨U, hUU, ?_, ?_⟩
  · intro σ hσU hστ
    have hσball : dist σ τ < ρ / 6 := Metric.mem_ball.1 hσU.1
    have hσN : σ ∈ N := hN'N hσU.2
    have hFeq : {σ' ∈ U | Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ' =
        Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) σ} =
        (fun δ : Γ => δ • σ) '' Sτ := by
      ext σ'
      constructor
      · rintro ⟨hσ'U, hmk⟩
        obtain ⟨δ, hδσ, hδτ⟩ := hkey σ σ' hσU hσ'U hmk
        exact ⟨δ, SetLike.mem_coe.2 (MulAction.mem_stabilizer_iff.2 hδτ), hδσ⟩
      · rintro ⟨δ, hδS, hδσ⟩
        have hδσ' : δ • σ = σ' := hδσ
        subst hδσ'
        have hδτ : (δ : Γ) • τ = τ := MulAction.mem_stabilizer_iff.1 (SetLike.mem_coe.1 hδS)
        constructor
        · constructor
          · rw [Metric.mem_ball]
            have e : dist ((δ : Γ) • σ) τ = dist σ τ := by
              conv_lhs => rw [← hδτ]
              exact (hIso δ).dist_eq σ τ
            rw [e]
            exact hσball
          · exact hN'inv δ hδS σ hσU.2
        · exact (Quotient.eq).2 ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨δ, rfl⟩))
    rw [hFeq]
    have hσne : ∀ g : Γ, g • σ = σ → ∀ x : UpperHalfPlane, g • x = x := by
      intro g hgσ
      by_contra h
      push Not at h
      exact hNprop σ hσN hστ ⟨g, hgσ, h⟩
    have hMsub : ∀ h : UpperHalfPlane → UpperHalfPlane, h ∈
        {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)} →
        ∃ δ : Γ, (δ : Γ) • τ = τ ∧ h = ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) := by
      intro h hh
      obtain ⟨γ, hγΓ, hγτ, hhγ⟩ := hh
      refine ⟨⟨γ, hγΓ⟩, ?_, hhγ⟩
      rw [Subgroup.smul_def]
      exact hγτ
    have h1 : ∀ h (hh : h ∈ {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧
        h = (γ • ·)}), h σ ∈ (fun δ : Γ => δ • σ) '' Sτ := by
      intro h hh
      obtain ⟨δ, hδτ, hhδ⟩ := hMsub h hh
      refine ⟨δ, SetLike.mem_coe.2 (MulAction.mem_stabilizer_iff.2 hδτ), ?_⟩
      rw [hhδ]
      rfl
    have h2 : ∀ h₁ h₂ (hh₁ : h₁ ∈ {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧
        h = (γ • ·)}) (hh₂ : h₂ ∈ {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧
        h = (γ • ·)}), h₁ σ = h₂ σ → h₁ = h₂ := by
      intro h₁ h₂ hh₁ hh₂ heq
      obtain ⟨δ₁, hδ₁τ, hhδ₁⟩ := hMsub h₁ hh₁
      obtain ⟨δ₂, hδ₂τ, hhδ₂⟩ := hMsub h₂ hh₂
      have heq' : (δ₂⁻¹ * δ₁ : Γ) • σ = σ := by
        have e1 : (δ₁ : Γ) • σ = (δ₂ : Γ) • σ := by
          have c1 : h₁ σ = ((δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ := by rw [hhδ₁]
          have c2 : h₂ σ = ((δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ := by rw [hhδ₂]
          rw [c1, c2] at heq
          rw [show ((δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ = (δ₁ : Γ) • σ from rfl,
            show ((δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ = (δ₂ : Γ) • σ from rfl] at heq
          exact heq
        calc (δ₂⁻¹ * δ₁ : Γ) • σ = (δ₂⁻¹ : Γ) • ((δ₁ : Γ) • σ) := mul_smul _ _ _
          _ = (δ₂⁻¹ : Γ) • ((δ₂ : Γ) • σ) := by rw [e1]
          _ = σ := inv_smul_smul _ _
      have htriv : ∀ x : UpperHalfPlane, (δ₂⁻¹ * δ₁ : Γ) • x = x := hσne _ heq'
      have htriv' : ∀ x : UpperHalfPlane,
          ((δ₂⁻¹ * δ₁ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x = x := by
        intro x
        rw [← Subgroup.smul_def]
        exact htriv x
      rcases l22_smul_self_iff htriv' with hE | hE
      · have h5 : ((δ₂⁻¹ * δ₁ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 := hE
        have hδ₁₂ : δ₁ = δ₂ := by
          have h1' : (δ₂⁻¹ * δ₁ : Γ) = 1 := by
            apply Subtype.ext
            show ((δ₂⁻¹ * δ₁ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) =
              ((1 : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            rw [Subgroup.coe_one]
            exact h5
          exact (inv_mul_eq_one.1 h1').symm
        rw [hhδ₁, hhδ₂, hδ₁₂]
      · have h5 : ((δ₂⁻¹ * δ₁ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1 := hE
        have hδ₁₂ : (δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ) =
            -(δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
          have h6 := eq_mul_of_inv_mul_eq h5
          rwa [mul_neg_one] at h6
        rw [hhδ₁, hhδ₂, hδ₁₂]
        funext x
        exact t22d_neg_smul _ _
    have h3 : ∀ σ' ∈ (fun δ : Γ => δ • σ) '' Sτ, ∃ h, ∃ hh : h ∈
        {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)}, h σ = σ' := by
      rintro σ' ⟨δ, hδS, hδσ⟩
      have hδσ' : δ • σ = σ' := hδσ
      refine ⟨(fun x => ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) • x), ?_, ?_⟩
      · exact ⟨(δ : Matrix.SpecialLinearGroup (Fin 2) ℝ), SetLike.coe_mem δ,
          by rw [← Subgroup.smul_def]; exact MulAction.mem_stabilizer_iff.1 (SetLike.mem_coe.1 hδS),
          rfl⟩
      · rw [← hδσ']
        rfl
    exact (Set.ncard_congr (fun h (_ : h ∈ {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ,
        γ • τ = τ ∧ h = (γ • ·)}) => h σ) h1 h2 h3).symm
  · intro hM1
    intro σ₁ hσ₁ σ₂ hσ₂ hmk
    obtain ⟨δ, hδσ, hδτ⟩ := hkey σ₁ σ₂ hσ₁ hσ₂ hmk.symm
    obtain ⟨h₀, hM0⟩ := Set.ncard_eq_one.1 hM1
    have hidM : (fun x => (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x) ∈
        {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)} :=
      ⟨1, Subgroup.one_mem Γ, one_smul _ τ, rfl⟩
    have hδM : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) ∈
        {h : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, γ • τ = τ ∧ h = (γ • ·)} := by
      refine ⟨(δ : Matrix.SpecialLinearGroup (Fin 2) ℝ), SetLike.coe_mem δ, ?_, rfl⟩
      rw [← Subgroup.smul_def]
      exact hδτ
    have e1 : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) = h₀ := by
      rw [hM0] at hδM
      exact Set.mem_singleton_iff.1 hδM
    have e2 : (fun x => (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x) = h₀ := by
      rw [hM0] at hidM
      exact Set.mem_singleton_iff.1 hidM
    have hfin2 : (δ : Γ) • σ₁ = σ₁ := by
      have hmap : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ₁ =
          ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ₁ := by rw [e1, e2]
      have l : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ₁ = (δ : Γ) • σ₁ := rfl
      have r : ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) σ₁ = (1 : Γ) • σ₁ := by
        show (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • σ₁ = (1 : Γ) • σ₁
        rw [Subgroup.smul_def, Subgroup.coe_one]
      rw [l, r] at hmap
      rw [one_smul] at hmap
      exact hmap
    exact hfin2.symm.trans hδσ

end GardinerLakic2000
