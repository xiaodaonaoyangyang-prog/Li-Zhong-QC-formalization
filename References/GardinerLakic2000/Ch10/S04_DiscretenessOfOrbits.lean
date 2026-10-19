import References.GardinerLakic2000.Ch10.S03_LengthSpectrum

/-!
# Gardiner–Lakic 2000, Ch. 10 §10.4 Discreteness of orbits

Source `teichmuller.txt`, lines 8170–8218 (Chapter 10, §10.4).

* Definition (`MCG(Γ)` acts discontinuously on `T(Γ)`, l. 8171) — `IsSeqCompactT`, `McgActsDiscontinuously`
* Lemma 2 (Teichmüller, (10.9), l. 8184; the Ch. 2 introduction, l. 1109) — `lemma10_2`
* Theorem 4 (l. 8217) — `thm10_4`

Not items: (10.10) and the orbit estimate (l. 8194–8215, proof). The book writes "the set of elements `h` for which
`h(K) ∩ K` is empty is a finite set" (l. 8171) for nonempty [misprint]. Modelling (C0.3): compactness in `T(Γ)` is
sequential compactness for `teichDistanceGamma`; a mapping class moves `K` to meet itself if some representative
`h ∈ QC(Γ)` has a geometric isomorphism `ρ_h` with `ρ_h(K) ∩ K ≠ ∅`. In Lemma 2 the Möbius maps act on `ℂ`
(`LiZhongQC.h36p_m`), `w` is a `K`-quasiconformal homeomorphism of the plane, and the multipliers are
`LiZhongQC.multiplier`; near miss `LiZhongQC.lemma30_3_wolpert` (lengths of closed curves on surfaces). Near miss for
Theorem 4: `LiZhongQC.thm30_3` (closed surfaces of genus `> 1`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsFuchsian IsHyperbolic IsKQC multiplier h36p_m TeichGamma teichDistanceGamma)

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): the image of a round annulus under a homeomorphism of the plane separates the
images of its complementary pieces. If `w` is a `K`-quasiconformal homeomorphism of `ℂ` onto `ℂ`, `|x − q| ≤ r` and
`ρ ≤ |y − q|`, then `w(r < |z − q| < ρ)` separates `{w(q), w(x)}` from `{w(y), ∞}`: its complement in `ℂ̄` is the
disjoint union of the compact connected set `w(|z − q| ≤ r)` and the closed connected set `ℂ̄ ∖ w(|z − q| < ρ)`. -/
theorem gl10_tl_sep {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K) (honto : w '' univ = univ) {q x y : ℂ} {r ρ : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hx : ‖x - q‖ ≤ r) (hy : ρ ≤ ‖y - q‖) :
    SeparatesSets (w '' annulusAt q r ρ) {((w q : ℂ) : ExtPlane), ((w x : ℂ) : ExtPlane)}
      {((w y : ℂ) : ExtPlane), extInf} := by
  have hc : Continuous w := continuousOn_univ.mp hw.2.2.1.1
  have hinj : Function.Injective w := injOn_univ.mp hw.2.2.1.2.1
  have hsurj : Function.Surjective w := fun ζ => by
    have hmem : ζ ∈ w '' univ := by rw [honto]; exact mem_univ ζ
    obtain ⟨a, -, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hgc : Continuous (Function.invFunOn w univ) := by
    have h := hw.2.2.1.2.2.2
    rw [honto] at h
    exact continuousOn_univ.mp h
  have hgw : ∀ z, Function.invFunOn w univ (w z) = z := fun z =>
    hw.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  -- images of open sets are open
  have hopen : ∀ S : Set ℂ, IsOpen S → IsOpen (w '' S) := by
    intro S hS
    have e : w '' S = Function.invFunOn w univ ⁻¹' S := by
      ext ζ
      constructor
      · rintro ⟨z, hz, rfl⟩
        show Function.invFunOn w univ (w z) ∈ S
        rw [hgw]
        exact hz
      · intro hζ
        obtain ⟨z, rfl⟩ := hsurj ζ
        refine ⟨z, ?_, rfl⟩
        have h' : Function.invFunOn w univ (w z) ∈ S := hζ
        rwa [hgw] at h'
    rw [e]
    exact hS.preimage hgc
  -- the pieces
  have hCU : closedBall q r ⊆ ball q ρ := closedBall_subset_ball hrρ
  have hann : annulusAt q r ρ = ball q ρ \ closedBall q r := by
    ext z
    rw [Set.mem_sdiff, mem_ball_iff_norm, mem_closedBall_iff_norm, not_le]
    constructor
    · intro hz
      have hz' : r < ‖z - q‖ ∧ ‖z - q‖ < ρ := hz
      exact ⟨hz'.2, hz'.1⟩
    · rintro ⟨h1, h2⟩
      show r < ‖z - q‖ ∧ ‖z - q‖ < ρ
      exact ⟨h2, h1⟩
  have hVb : Bornology.IsBounded (w '' ball q ρ) :=
    ((isCompact_closedBall q ρ).image hc).isBounded.subset (image_mono ball_subset_closedBall)
  have hS : (toExt (w '' annulusAt q r ρ))ᶜ =
      toExt (w '' closedBall q r) ∪ (toExt (w '' ball q ρ))ᶜ := by
    rw [hann, image_sdiff hinj]
    show (((↑) : ℂ → ExtPlane) '' (w '' ball q ρ \ w '' closedBall q r))ᶜ =
      ((↑) : ℂ → ExtPlane) '' (w '' closedBall q r) ∪ (((↑) : ℂ → ExtPlane) '' (w '' ball q ρ))ᶜ
    rw [image_sdiff OnePoint.coe_injective, compl_sdiff]
  have hsub : toExt (w '' closedBall q r) ⊆ toExt (w '' ball q ρ) := image_mono (image_mono hCU)
  have hP₁c : IsClosed (toExt (w '' closedBall q r)) :=
    (((isCompact_closedBall q r).image hc).image OnePoint.continuous_coe).isClosed
  have hP₂c : IsClosed (toExt (w '' ball q ρ))ᶜ :=
    (OnePoint.isOpenMap_coe _ (hopen _ isOpen_ball)).isClosed_compl
  have hP₁p : IsPreconnected (toExt (w '' closedBall q r)) :=
    ((convex_closedBall q r).isPreconnected.image _ hc.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  -- the outer piece is connected: `{ρ ≤ |z − q|}` is a continuous image of `[ρ, ∞) × ℝ`
  have hO : IsPreconnected (ball q ρ)ᶜ := by
    have e : (ball q ρ)ᶜ = (fun p : ℝ × ℝ => q + (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ici ρ ×ˢ univ) := by
      ext z
      constructor
      · intro hz
        rw [mem_compl_iff, mem_ball_iff_norm, not_lt] at hz
        refine ⟨(‖z - q‖, arg (z - q)), ⟨hz, mem_univ _⟩, ?_⟩
        show q + ((‖z - q‖ : ℝ) : ℂ) * exp ((arg (z - q) : ℂ) * I) = z
        rw [norm_mul_exp_arg_mul_I]
        ring
      · rintro ⟨⟨s, θ⟩, ⟨hs, -⟩, rfl⟩
        have hs' : ρ ≤ s := hs
        rw [mem_compl_iff, mem_ball_iff_norm, not_lt]
        show ρ ≤ ‖q + (s : ℂ) * exp ((θ : ℂ) * I) - q‖
        rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
        exact hs'
    rw [e]
    exact (isPreconnected_Ici.prod isPreconnected_univ).image _ (by fun_prop : Continuous fun p : ℝ × ℝ =>
      q + (p.1 : ℂ) * exp ((p.2 : ℂ) * I)).continuousOn
  have hA : IsPreconnected (toExt (w '' ball q ρ)ᶜ) := by
    rw [← image_compl_eq ⟨hinj, hsurj⟩]
    exact (hO.image _ hc.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  have hP₂p : IsPreconnected (toExt (w '' ball q ρ))ᶜ := by
    refine hA.subset_closure ?_ ?_
    · rintro _ ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hξζ⟩
      exact hζ (OnePoint.coe_injective hξζ ▸ hξ)
    · intro p hp
      induction p using OnePoint.rec with
      | infty => exact LiZhongQC.extInf_mem_closure_toExt_compl_of_isBounded hVb
      | coe ζ =>
        refine subset_closure ⟨ζ, fun hζ => hp ⟨ζ, hζ, rfl⟩, rfl⟩
  -- membership of the four points
  have hq1 : ((w q : ℂ) : ExtPlane) ∈ toExt (w '' closedBall q r) :=
    ⟨w q, ⟨q, mem_closedBall_self hr.le, rfl⟩, rfl⟩
  have hx1 : ((w x : ℂ) : ExtPlane) ∈ toExt (w '' closedBall q r) := by
    refine ⟨w x, ⟨x, ?_, rfl⟩, rfl⟩
    rw [mem_closedBall_iff_norm]
    exact hx
  have hy2 : ((w y : ℂ) : ExtPlane) ∈ (toExt (w '' ball q ρ))ᶜ := by
    rintro ⟨ζ, ⟨z, hz, hzζ⟩, hζ⟩
    have hzy : z = y := hinj (hzζ.trans (OnePoint.coe_injective hζ))
    rw [hzy, mem_ball_iff_norm] at hz
    linarith
  have hi2 : extInf ∈ (toExt (w '' ball q ρ))ᶜ := by
    rintro ⟨ζ, -, hζ⟩
    exact OnePoint.coe_ne_infty ζ hζ
  -- the separation
  show ∃ x₁ ∈ (toExt (w '' annulusAt q r ρ))ᶜ, ∃ x₂ ∈ (toExt (w '' annulusAt q r ρ))ᶜ,
    {((w q : ℂ) : ExtPlane), ((w x : ℂ) : ExtPlane)} ⊆ connectedComponentIn (toExt (w '' annulusAt q r ρ))ᶜ x₁ ∧
      {((w y : ℂ) : ExtPlane), extInf} ⊆ connectedComponentIn (toExt (w '' annulusAt q r ρ))ᶜ x₂ ∧
      connectedComponentIn (toExt (w '' annulusAt q r ρ))ᶜ x₁ ≠
        connectedComponentIn (toExt (w '' annulusAt q r ρ))ᶜ x₂
  rw [hS]
  refine ⟨_, subset_union_left hq1, _, subset_union_right hy2, ?_, ?_, ?_⟩
  · have h := hP₁p.subset_connectedComponentIn hq1
      (subset_union_left : toExt (w '' closedBall q r) ⊆ toExt (w '' closedBall q r) ∪ (toExt (w '' ball q ρ))ᶜ)
    intro p hp
    rcases hp with rfl | hp
    · exact h hq1
    · rw [mem_singleton_iff] at hp
      rw [hp]
      exact h hx1
  · have h := hP₂p.subset_connectedComponentIn hy2
      (subset_union_right : (toExt (w '' ball q ρ))ᶜ ⊆ toExt (w '' closedBall q r) ∪ (toExt (w '' ball q ρ))ᶜ)
    intro p hp
    rcases hp with rfl | hp
    · exact h hy2
    · rw [mem_singleton_iff] at hp
      rw [hp]
      exact h hi2
  · intro heq
    have hmy : ((w y : ℂ) : ExtPlane) ∈ connectedComponentIn
        (toExt (w '' closedBall q r) ∪ (toExt (w '' ball q ρ))ᶜ) ((w q : ℂ) : ExtPlane) := by
      rw [heq]
      exact mem_connectedComponentIn (subset_union_right hy2)
    have hmq : ((w q : ℂ) : ExtPlane) ∈ connectedComponentIn
        (toExt (w '' closedBall q r) ∪ (toExt (w '' ball q ρ))ᶜ) ((w q : ℂ) : ExtPlane) :=
      mem_connectedComponentIn (subset_union_left hq1)
    have hdisj : ∀ p, p ∈ toExt (w '' closedBall q r) → p ∉ (toExt (w '' ball q ρ))ᶜ :=
      fun p hp hp' => hp' (hsub hp)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn) _ _ hP₁c hP₂c
        (connectedComponentIn_subset _ _) (by
          ext p
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro _ hp1 hp2
          exact hdisj p hp1 hp2) with h1 | h2
    · exact hdisj _ (h1 hmy) hy2
    · exact hdisj _ hq1 (h2 hmq)

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): one ring. For a `K`-quasiconformal homeomorphism `w` of the plane and
`0 < |x − q| < ρ = |y − q|`, the ring `|x − q| < |z − q| < ρ` has modulus `log(ρ/|x − q|)` (`nf_e_dcModulus_annulusAt`).
Its image separates `{w(q), w(x)}` from `{w(y), ∞}` (`gl10_tl_sep`), so its modulus is at most
`2μ(√(s)) ≤ log(16/s)`, `s = |w(x) − w(q)|/(|w(x) − w(q)| + |w(y) − w(q)|)` (Teichmüller's modulus theorem `thm5_3`
after translating `w(q)` to `0`, and `μ(r) ≤ log(4/r)`, `eq14_27`). Theorem 7.4 compares the two moduli. -/
theorem gl10_tl_ring {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K) (honto : w '' univ = univ) {q x y : ℂ} {ρ : ℝ}
    (hxq : x ≠ q) (hxρ : ‖x - q‖ < ρ) (hy : ‖y - q‖ = ρ) :
    Real.log (ρ / ‖x - q‖) ≤ K * Real.log (16 * (1 + ‖w y - w q‖ / ‖w x - w q‖)) := by
  have hr : 0 < ‖x - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hxq)
  have hρ : 0 < ρ := hr.trans hxρ
  have hK : 0 ≤ K := by linarith [hw.2.1]
  -- the translated map `w₀ = w − w(q)`
  obtain ⟨hw₀, hon₀⟩ := LiZhongQC.td_affine_comp hw honto (α := 1) (γ := 1) 0 (-w q) one_ne_zero one_ne_zero
  have e : (fun z => (1 : ℂ) * w (1 * z + 0) + -w q) = fun z => w z - w q := by
    funext z
    rw [one_mul, one_mul, add_zero, sub_eq_add_neg]
  rw [e] at hw₀ hon₀
  -- the ring and its image
  have hB := LiZhongQC.nf_g_isDoublyConnected_annulusAt q hr hxρ
  have hM := LiZhongQC.nf_e_dcModulus_annulusAt q hr hxρ
  have hbdd : Bornology.IsBounded (annulusAt q ‖x - q‖ ρ) :=
    Metric.isBounded_ball.subset fun z hz => mem_ball_iff_norm.2 hz.2
  have hcl : closure (toExt (annulusAt q ‖x - q‖ ρ)) ⊆ toExt univ := by
    rw [LiZhongQC.closure_toExt_of_isBounded' hbdd]
    exact image_mono (subset_univ _)
  obtain ⟨hdc, hle, -⟩ := LiZhongQC.thm7_4_dcModulus_quasi_invariance hw₀ hB hcl
  have hsep := gl10_tl_sep hw₀ hon₀ hr hxρ le_rfl hy.ge
  have h0 : w q - w q = 0 := sub_self _
  simp only [h0] at hsep
  -- Teichmüller's modulus theorem for the image ring
  have hz₁ : w x - w q ≠ 0 := sub_ne_zero.2 fun h => hxq (injOn_univ.mp hw.2.2.1.2.1 h)
  have hyq : y ≠ q := by
    intro h
    rw [h, sub_self, norm_zero] at hy
    linarith
  have hz₂ : w y - w q ≠ 0 := sub_ne_zero.2 fun h => hyq (injOn_univ.mp hw.2.2.1.2.1 h)
  have hT := LiZhongQC.thm5_3_teichmuller_modulus_theorem hz₁ hz₂ hdc hsep
  -- `2μ(√s) ≤ log(16/s)`
  set s : ℝ := ‖w x - w q‖ / (‖w x - w q‖ + ‖w y - w q‖) with hs
  have hn₁ : 0 < ‖w x - w q‖ := norm_pos_iff.2 hz₁
  have hn₂ : 0 < ‖w y - w q‖ := norm_pos_iff.2 hz₂
  have hs0 : 0 < s := div_pos hn₁ (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsq1 : Real.sqrt s < 1 := (Real.sqrt_lt_sqrt hs0.le hs1).trans_eq Real.sqrt_one
  have hμ := (LiZhongQC.eq14_27 hsq0 hsq1).2
  have h16 : 2 * Real.log (4 / Real.sqrt s) = Real.log (16 * (1 + ‖w y - w q‖ / ‖w x - w q‖)) := by
    have e2 : (2 : ℝ) * Real.log (4 / Real.sqrt s) = Real.log ((4 / Real.sqrt s) ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e2, div_pow, Real.sq_sqrt hs0.le, hs]
    congr 1
    field_simp
    ring
  have hbound : 2 * LiZhongQC.grotzschMu (Real.sqrt s) ≤ Real.log (16 * (1 + ‖w y - w q‖ / ‖w x - w q‖)) := by
    rw [← h16]
    linarith
  -- combine
  have hchain : ENNReal.ofReal (Real.log (ρ / ‖x - q‖)) ≤
      ENNReal.ofReal (K * (2 * LiZhongQC.grotzschMu (Real.sqrt s))) := by
    rw [← hM, ENNReal.ofReal_mul hK]
    exact hle.trans (by gcongr)
  have hpos : 0 < Real.log (ρ / ‖x - q‖) := Real.log_pos ((one_lt_div hr).2 hxρ)
  rcases (ENNReal.ofReal_le_ofReal_iff').1 hchain with h | h
  · exact h.trans (mul_le_mul_of_nonneg_left hbound hK)
  · linarith

/-- Helper for `lemma10_2` (§10.4): the determinant of `A ∈ SL(2, ℝ)`, `ad − bc = 1`, over `ℂ`. -/
theorem gl10_tl_det (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): the algebra at a finite fixed point `q` of `z ↦ A z`, `e = c q + d`. The
eigenvalue equation `e² − (a + d) e + 1 = 0`, and in the coordinate `v = 1/(z − q)` the map is affine:
`1/(A z − q) = e² / (z − q) + e c` (from `A z − q = (z − q)/(e (c z + d))`). -/
theorem gl10_tl_fix {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {q : ℂ} (hqd : (A 1 0 : ℂ) * q + A 1 1 ≠ 0)
    (hq : h36p_m A q = q) :
    ((A 1 0 : ℂ) * q + A 1 1) ^ 2 - ((A 0 0 : ℂ) + A 1 1) * ((A 1 0 : ℂ) * q + A 1 1) + 1 = 0 ∧
      ∀ z : ℂ, (A 1 0 : ℂ) * z + A 1 1 ≠ 0 → z ≠ q → h36p_m A z - q ≠ 0 ∧
        1 / (h36p_m A z - q) =
          ((A 1 0 : ℂ) * q + A 1 1) ^ 2 * (1 / (z - q)) + ((A 1 0 : ℂ) * q + A 1 1) * A 1 0 := by
  have hdet := gl10_tl_det A
  have hqe : q * ((A 1 0 : ℂ) * q + A 1 1) = (A 0 0 : ℂ) * q + A 0 1 := by
    have h : ((A 0 0 : ℂ) * q + A 0 1) / ((A 1 0 : ℂ) * q + A 1 1) = q := hq
    rw [div_eq_iff hqd] at h
    exact h.symm
  refine ⟨by linear_combination (A 1 0 : ℂ) * hqe - hdet, fun z hz hzq => ?_⟩
  have hkey : h36p_m A z - q = (z - q) / (((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1)) := by
    rw [eq_div_iff (mul_ne_zero hqd hz)]
    show (((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) - q) *
      (((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1)) = z - q
    have h1 : (((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) - q) *
        (((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1)) =
        ((A 0 0 : ℂ) * z + A 0 1) * ((A 1 0 : ℂ) * q + A 1 1) -
          q * ((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1) := by
      calc (((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) - q) *
            (((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1)) =
            ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1) *
              ((A 1 0 : ℂ) * q + A 1 1) - q * ((A 1 0 : ℂ) * q + A 1 1) * ((A 1 0 : ℂ) * z + A 1 1) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hz]
    rw [h1, hqe]
    linear_combination (z - q) * hdet
  have hzq' : z - q ≠ 0 := sub_ne_zero.2 hzq
  refine ⟨by rw [hkey]; exact div_ne_zero hzq' (mul_ne_zero hqd hz), ?_⟩
  rw [hkey, one_div_div]
  field_simp
  ring

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): a root `e` of `e² − (a + d) e + 1 = 0` for hyperbolic `A` (`|a + d| > 2`) is real,
`|e| ≠ 1`, and if `|e| > 1` then `multiplier A = |e|²` (the larger root in modulus is `(|a + d| + √((a+d)² − 4))/2`). -/
theorem gl10_tl_real {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) {e : ℂ}
    (he : e ^ 2 - ((A 0 0 : ℂ) + A 1 1) * e + 1 = 0) :
    e.im = 0 ∧ ‖e‖ ≠ 1 ∧ (1 < ‖e‖ → multiplier A = ‖e‖ ^ 2) := by
  have ht : 2 < |A 0 0 + A 1 1| := hA
  have ht2 : 4 < (A 0 0 + A 1 1) ^ 2 := by nlinarith [sq_abs (A 0 0 + A 1 1), abs_nonneg (A 0 0 + A 1 1)]
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [sq, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.zero_re, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im,
    Complex.zero_im] at hre him
  have hv : e.im = 0 := by
    by_contra hv
    have h2 : e.im * (2 * e.re - (A 0 0 + A 1 1)) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact hv h
    · nlinarith [sq_nonneg e.im, sq_nonneg e.re]
  have hu : e.re ^ 2 - (A 0 0 + A 1 1) * e.re + 1 = 0 := by rw [hv] at hre; nlinarith
  have hnorm : ‖e‖ = |e.re| := by
    have heu : e = (e.re : ℂ) := Complex.ext (by simp) (by simp [hv])
    conv_lhs => rw [heu]
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- `|u|² − |t| |u| + 1 = 0` for `u = e.re`, `t = a + d`
  have hut : 0 < (A 0 0 + A 1 1) * e.re := by nlinarith [sq_nonneg e.re]
  have habs : |e.re| ^ 2 - |A 0 0 + A 1 1| * |e.re| + 1 = 0 := by
    rw [← abs_mul, abs_of_pos hut, sq_abs]
    linarith
  refine ⟨hv, ?_, fun h1 => ?_⟩
  · intro h1
    rw [hnorm] at h1
    rw [h1] at habs
    linarith
  · rw [hnorm] at h1 ⊢
    set X := |e.re| with hX
    set T := |A 0 0 + A 1 1| with hT
    have hT2 : T ^ 2 = (A 0 0 + A 1 1) ^ 2 := sq_abs _
    set s := Real.sqrt ((A 0 0 + A 1 1) ^ 2 - 4) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = T ^ 2 - 4 := by rw [hs, Real.sq_sqrt (by linarith), hT2]
    have hsq : (2 * X - T) ^ 2 = s ^ 2 := by nlinarith
    have hpos : 0 ≤ 2 * X - T := by
      by_contra hneg
      have hneg' : 2 * X - T < 0 := lt_of_not_ge hneg
      have hst : s = T - 2 * X := (sq_eq_sq₀ hs0 (by linarith)).1 (by nlinarith)
      nlinarith
    have hval : 2 * X - T = s := (sq_eq_sq₀ hpos hs0).1 hsq
    show ((|A 0 0 + A 1 1| + Real.sqrt ((A 0 0 + A 1 1) ^ 2 - 4)) / 2) ^ 2 = X ^ 2
    rw [← hT, ← hs]
    congr 1
    linarith

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): the exact geometric rate of an orbit converging to a fixed point.
- **Hypotheses.** `A` is hyperbolic, `q ∈ ℂ` is a fixed point of `z ↦ A z`, and the orbit `zₙ₊₁ = A zₙ` avoids the
  pole and `q` and tends to `q`. So `q` is the attracting fixed point and `z₀` is not the repelling one: an orbit
  started there is constant and does not tend to `q`.
- **Conclusion.** `λ = multiplier A > 1` and `c λ⁻ⁿ ≤ |zₙ − q| ≤ C λ⁻ⁿ`, with the statement's convention
  `multiplier A = ((|tr| + √(tr² − 4))/2)²`: the derivative of `A` at its attracting fixed point is `λ⁻¹`.
- **Proof idea.** `A z − q = (z − q)/(e (c z + d))` with the eigenvalue `e = c q + d`. Convergence forces `|e| > 1`,
  so `λ = e²`, and the corrections `log(|c zₖ + d|/|e|) = O(|zₖ − q|)` are summable. -/
theorem gl10_tl_rate {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) {q : ℂ}
    (hqd : (A 1 0 : ℂ) * q + A 1 1 ≠ 0) (hq : h36p_m A q = q) {z : ℕ → ℂ}
    (hz : ∀ n, z (n + 1) = h36p_m A (z n)) (hzd : ∀ n, (A 1 0 : ℂ) * z n + A 1 1 ≠ 0) (hzq : ∀ n, z n ≠ q)
    (hlim : Tendsto z atTop (𝓝 q)) :
    1 < multiplier A ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      c * (multiplier A)⁻¹ ^ n ≤ ‖z n - q‖ ∧ ‖z n - q‖ ≤ C * (multiplier A)⁻¹ ^ n := by
  obtain ⟨hquad, hrec⟩ := gl10_tl_fix hqd hq
  obtain ⟨-, hne1, hmult⟩ := gl10_tl_real hA hquad
  set e : ℂ := (A 1 0 : ℂ) * q + A 1 1 with he
  have he2 : e ^ 2 ≠ 1 := by
    intro h
    apply hne1
    have h' := congrArg norm h
    rw [norm_pow, norm_one] at h'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h'
  have he21 : (1 : ℂ) - e ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm he2)
  -- the affine recurrence for `vₙ = 1/(zₙ − q)` and its closed form
  set vs : ℂ := e * (A 1 0 : ℂ) / (1 - e ^ 2) with hvs
  have hvs_fix : e ^ 2 * vs + e * (A 1 0 : ℂ) = vs := by
    rw [hvs]
    field_simp
    ring
  have hvrec : ∀ n, 1 / (z (n + 1) - q) = e ^ 2 * (1 / (z n - q)) + e * (A 1 0 : ℂ) := by
    intro n
    rw [hz n]
    exact (hrec (z n) (hzd n) (hzq n)).2
  have hclosed : ∀ n, 1 / (z n - q) = (e ^ 2) ^ n * (1 / (z 0 - q) - vs) + vs := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hvrec, ih, pow_succ]
      linear_combination hvs_fix
  have hvn : ∀ n, ‖1 / (z n - q)‖ = ‖z n - q‖⁻¹ := fun n => by rw [norm_div, norm_one, one_div]
  -- `‖vₙ‖ → ∞`
  have hzn : Tendsto (fun n => ‖z n - q‖) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_iff_norm_sub_tendsto_zero.1 hlim,
      Eventually.of_forall fun n => norm_pos_iff.2 (sub_ne_zero.2 (hzq n))⟩
  have hvinf : Tendsto (fun n => ‖1 / (z n - q)‖) atTop atTop := by
    simp_rw [hvn]
    exact hzn.inv_tendsto_nhdsGT_zero
  -- convergence forces `|e| > 1`
  have he1 : 1 < ‖e‖ := by
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · exfalso
      have hpow : Tendsto (fun n : ℕ => (e ^ 2) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [norm_pow]; nlinarith [norm_nonneg e])
      have hconv : Tendsto (fun n => ‖1 / (z n - q)‖) atTop (𝓝 ‖0 * (1 / (z 0 - q) - vs) + vs‖) := by
        refine (((hpow.mul_const (1 / (z 0 - q) - vs)).add_const vs).norm).congr fun n => ?_
        rw [hclosed n]
      exact not_tendsto_atTop_of_tendsto_nhds hconv hvinf
    · exact hgt
  have hLm : multiplier A = ‖e‖ ^ 2 := hmult he1
  have hL1 : 1 < ‖e‖ ^ 2 := by nlinarith
  rw [hLm]
  refine ⟨hL1, ?_⟩
  set L : ℝ := ‖e‖ ^ 2 with hL
  set D : ℂ := 1 / (z 0 - q) - vs with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have hconst : ∀ n, ‖1 / (z n - q)‖ = ‖vs‖ := fun n => by rw [hclosed n, h0, mul_zero, zero_add]
    have : Tendsto (fun n => ‖1 / (z n - q)‖) atTop (𝓝 ‖vs‖) := by
      simp_rw [hconst]
      exact tendsto_const_nhds
    exact not_tendsto_atTop_of_tendsto_nhds this hvinf
  have hnormpow : ∀ n : ℕ, ‖(e ^ 2) ^ n‖ = L ^ n := fun n => by rw [norm_pow, norm_pow]
  have hLn : ∀ n : ℕ, 0 < L ^ n := fun n => pow_pos (by linarith) n
  -- the upper bound of `‖vₙ‖`, hence the lower bound of `‖zₙ − q‖`
  have hupper_v : ∀ n, ‖1 / (z n - q)‖ ≤ L ^ n * (‖D‖ + ‖vs‖) := by
    intro n
    rw [hclosed n]
    have h1 := one_le_pow₀ hL1.le (n := n)
    calc ‖(e ^ 2) ^ n * D + vs‖ ≤ ‖(e ^ 2) ^ n‖ * ‖D‖ + ‖vs‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ = L ^ n * ‖D‖ + ‖vs‖ := by rw [hnormpow]
      _ ≤ L ^ n * (‖D‖ + ‖vs‖) := by nlinarith [norm_nonneg vs]
  -- `Lⁿ ‖zₙ − q‖ → 1/‖D‖`, hence bounded
  have he2' : e ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by rw [h, norm_zero] at he1; linarith)
  have hratio : Tendsto (fun n => L ^ n * ‖z n - q‖) atTop (𝓝 ‖D‖⁻¹) := by
    have hinv : ‖(e ^ 2)⁻¹‖ < 1 := by
      rw [norm_inv, norm_pow]
      exact inv_lt_one_of_one_lt₀ hL1
    have h1 : Tendsto (fun n : ℕ => D + vs * (e ^ 2)⁻¹ ^ n) atTop (𝓝 (D + vs * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv))
    rw [mul_zero, add_zero] at h1
    refine ((h1.norm).inv₀ (norm_ne_zero_iff.2 hD0)).congr fun n => ?_
    have hv : 1 / (z n - q) = (e ^ 2) ^ n * (D + vs * (e ^ 2)⁻¹ ^ n) := by
      rw [hclosed n, mul_add, ← mul_assoc, mul_comm ((e ^ 2) ^ n) vs, mul_assoc, ← mul_pow,
        mul_inv_cancel₀ he2', one_pow, mul_one]
    have hn := hvn n
    rw [hv, norm_mul, hnormpow] at hn
    have hN : ‖D + vs * (e ^ 2)⁻¹ ^ n‖ = (L ^ n * ‖z n - q‖)⁻¹ := by
      rw [mul_inv, ← hn, ← mul_assoc, inv_mul_cancel₀ (hLn n).ne', one_mul]
    rw [hN, inv_inv]
  obtain ⟨C₀, hC₀⟩ := hratio.bddAbove_range
  refine ⟨(‖D‖ + ‖vs‖)⁻¹, max C₀ 1, by positivity, by positivity, fun n => ⟨?_, ?_⟩⟩
  · have hpos : 0 < ‖z n - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (hzq n))
    have h1 := hupper_v n
    rw [hvn] at h1
    rw [inv_pow, ← mul_inv]
    have h2 : 0 < (‖D‖ + ‖vs‖) * L ^ n := by
      have := norm_pos_iff.2 hD0
      have := hLn n
      positivity
    calc ((‖D‖ + ‖vs‖) * L ^ n)⁻¹ ≤ (‖z n - q‖⁻¹)⁻¹ :=
          inv_anti₀ (inv_pos.2 hpos) (by rw [mul_comm]; exact h1)
      _ = ‖z n - q‖ := inv_inv _
  · have h1 : L ^ n * ‖z n - q‖ ≤ max C₀ 1 := (hC₀ (mem_range_self n)).trans (le_max_left _ _)
    rw [inv_pow]
    rw [le_mul_inv_iff₀ (hLn n), mul_comm]
    exact h1

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): `w` maps points that are not poles of `A₁` to points that are not poles of `A₂`.
Otherwise, near such a point `z₀` with `w(z₀)` the pole of `A₂`, the conjugacy gives `w(A₁ z) = A₂(w z)` for
`z → z₀`, `z ≠ z₀`; the left side tends to the finite `w(A₁ z₀)`, while `|A₂(w z)| → ∞` (the numerator of `A₂` does not
vanish at its pole, `det = 1`). -/
theorem gl10_tl_pole {A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K)
    (hconj : ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 → (A₂ 1 0 : ℂ) * w z + A₂ 1 1 ≠ 0 →
      w (h36p_m A₁ z) = h36p_m A₂ (w z)) :
    ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 → (A₂ 1 0 : ℂ) * w z + A₂ 1 1 ≠ 0 := by
  intro z₀ h₁
  by_contra hp
  have hp' : (A₂ 1 0 : ℂ) * w z₀ + A₂ 1 1 = 0 := hp
  have hc : Continuous w := continuousOn_univ.mp hw.2.2.1.1
  have hinj : Function.Injective w := injOn_univ.mp hw.2.2.1.2.1
  have hdet := gl10_tl_det A₂
  have hc₂ : (A₂ 1 0 : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hp'
    rw [hp', h0] at hdet
    simp at hdet
  have hden : ∀ ζ : ℂ, (A₂ 1 0 : ℂ) * ζ + A₂ 1 1 = (A₂ 1 0 : ℂ) * (ζ - w z₀) := fun ζ => by
    linear_combination hp'
  have hnum : (A₂ 0 0 : ℂ) * w z₀ + A₂ 0 1 ≠ 0 := by
    intro h0
    have h1 : ((A₂ 0 0 : ℂ) * w z₀ + A₂ 0 1) * (A₂ 1 0 : ℂ) = -1 := by
      linear_combination (A₂ 0 0 : ℂ) * hp' - hdet
    rw [h0, zero_mul] at h1
    norm_num at h1
  -- the sequence `z₀ + 1/(k+1)`
  set zk : ℕ → ℂ := fun k => z₀ + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hzk
  have hzt : Tendsto zk atTop (𝓝 z₀) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds (x := z₀)).add h
    rw [Complex.ofReal_zero, add_zero] at h2
    exact h2
  have hzne : ∀ k, zk k ≠ z₀ := fun k h => by
    have h' : ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by
      have := congrArg (fun u => u - z₀) h
      simpa [hzk] using this
    have : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
    exact this (by exact_mod_cast h')
  have hcont₁ : ContinuousAt (fun z : ℂ => (A₁ 1 0 : ℂ) * z + A₁ 1 1) z₀ := by fun_prop
  have hev : ∀ᶠ k in atTop, (A₁ 1 0 : ℂ) * zk k + A₁ 1 1 ≠ 0 :=
    hzt.eventually (hcont₁.eventually_ne h₁)
  -- the left side converges
  have hm : ContinuousAt (h36p_m A₁) z₀ := by
    show ContinuousAt (fun z : ℂ => ((A₁ 0 0 : ℂ) * z + A₁ 0 1) / ((A₁ 1 0 : ℂ) * z + A₁ 1 1)) z₀
    exact ContinuousAt.div (by fun_prop) (by fun_prop) h₁
  have hL : Tendsto (fun k => ‖w (h36p_m A₁ (zk k))‖) atTop (𝓝 ‖w (h36p_m A₁ z₀)‖) :=
    ((hc.continuousAt.tendsto.comp (hm.tendsto.comp hzt))).norm
  -- the right side tends to infinity
  have hg : Tendsto (fun k => ‖(A₂ 1 0 : ℂ) * w (zk k) + A₂ 1 1‖) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (((hc.continuousAt.tendsto.comp hzt).const_mul (A₂ 1 0 : ℂ)).add_const (A₂ 1 1 : ℂ)).norm
      rwa [hp', norm_zero] at h
    · rw [hden]
      exact norm_pos_iff.2 (mul_ne_zero hc₂ (sub_ne_zero.2 fun h => hzne k (hinj h)))
  have hN : Tendsto (fun k => ‖(A₂ 0 0 : ℂ) * w (zk k) + A₂ 0 1‖) atTop
      (𝓝 ‖(A₂ 0 0 : ℂ) * w z₀ + A₂ 0 1‖) :=
    (((hc.continuousAt.tendsto.comp hzt).const_mul (A₂ 0 0 : ℂ)).add_const (A₂ 0 1 : ℂ)).norm
  have hR : Tendsto (fun k => ‖h36p_m A₂ (w (zk k))‖) atTop atTop := by
    have h := hN.pos_mul_atTop (norm_pos_iff.2 hnum) hg.inv_tendsto_nhdsGT_zero
    refine h.congr fun k => ?_
    show ‖(A₂ 0 0 : ℂ) * w (zk k) + A₂ 0 1‖ * ‖(A₂ 1 0 : ℂ) * w (zk k) + A₂ 1 1‖⁻¹ =
      ‖((A₂ 0 0 : ℂ) * w (zk k) + A₂ 0 1) / ((A₂ 1 0 : ℂ) * w (zk k) + A₂ 1 1)‖
    rw [norm_div, div_eq_mul_inv]
  -- the two sides agree eventually
  have heq : (fun k => ‖w (h36p_m A₁ (zk k))‖) =ᶠ[atTop] fun k => ‖h36p_m A₂ (w (zk k))‖ := by
    filter_upwards [hev] with k hk
    rw [hconj (zk k) hk (by rw [hden]; exact mul_ne_zero hc₂ (sub_ne_zero.2 fun h => hzne k (hinj h)))]
  exact not_tendsto_atTop_of_tendsto_nhds hL (hR.congr' heq.symm)

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): an orbit converging to an attracting finite fixed point. If `q` is a fixed point
of `z ↦ B z` with `|e| > 1`, `e = c q + d`, the orbit of `x₀ = q + 1/R` (`R` large) has `1/(xₙ − q) =
(e²)ⁿ (R − v*) + v*` with `v* = e c/(1 − e²)` (`gl10_tl_fix`), so it avoids the pole and `q` and tends to `q`. -/
theorem gl10_tl_attract {B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {q : ℂ} (hqd : (B 1 0 : ℂ) * q + B 1 1 ≠ 0)
    (hq : h36p_m B q = q) (he1 : 1 < ‖(B 1 0 : ℂ) * q + B 1 1‖) :
    ∃ x : ℕ → ℂ, (∀ n, x (n + 1) = h36p_m B (x n)) ∧ (∀ n, (B 1 0 : ℂ) * x n + B 1 1 ≠ 0) ∧
      (∀ n, x n ≠ q) ∧ Tendsto x atTop (𝓝 q) := by
  obtain ⟨-, hrec⟩ := gl10_tl_fix hqd hq
  set e : ℂ := (B 1 0 : ℂ) * q + B 1 1 with he
  have he0 : e ≠ 0 := hqd
  have hL1 : 1 < ‖e ^ 2‖ := by rw [norm_pow]; nlinarith
  have he2 : (1 : ℂ) - e ^ 2 ≠ 0 := by
    intro h
    have : e ^ 2 = 1 := by linear_combination -h
    rw [this, norm_one] at hL1
    exact lt_irrefl _ hL1
  set vs : ℂ := e * (B 1 0 : ℂ) / (1 - e ^ 2) with hvs
  have hvs_fix : e ^ 2 * vs + e * (B 1 0 : ℂ) = vs := by
    rw [hvs]
    field_simp
    ring
  set R : ℝ := 2 * ‖vs‖ + ‖(B 1 0 : ℂ) / e‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  set x : ℕ → ℂ := fun n => (h36p_m B)^[n] (q + 1 / (R : ℂ)) with hx
  have hxs : ∀ n, x (n + 1) = h36p_m B (x n) := fun n => Function.iterate_succ_apply' _ _ _
  -- the closed form, the lower bound `‖vₙ‖ > ‖c/e‖`, and the pole avoidance, by induction
  have hpow1 : ∀ n : ℕ, 1 ≤ ‖(e ^ 2) ^ n‖ := fun n => by rw [norm_pow]; exact one_le_pow₀ hL1.le
  have hlow : ∀ n : ℕ, ‖(B 1 0 : ℂ) / e‖ + 1 ≤ ‖(e ^ 2) ^ n * ((R : ℂ) - vs) + vs‖ := by
    intro n
    have h1 : R - ‖vs‖ ≤ ‖(R : ℂ) - vs‖ := by
      have := norm_sub_norm_le (R : ℂ) vs
      rwa [Complex.norm_real, Real.norm_of_nonneg hR0.le] at this
    have h2 : ‖(e ^ 2) ^ n * ((R : ℂ) - vs)‖ - ‖vs‖ ≤ ‖(e ^ 2) ^ n * ((R : ℂ) - vs) + vs‖ := by
      have := norm_sub_norm_le ((e ^ 2) ^ n * ((R : ℂ) - vs)) (-vs)
      rwa [norm_neg, sub_neg_eq_add] at this
    rw [norm_mul] at h2
    have h3 := hpow1 n
    have h4 : 0 ≤ ‖(R : ℂ) - vs‖ := norm_nonneg _
    nlinarith
  have hdenV : ∀ V : ℂ, ‖(B 1 0 : ℂ) / e‖ + 1 ≤ ‖V‖ → e + (B 1 0 : ℂ) * (1 / V) ≠ 0 := by
    intro V hV h0
    have hV0 : V ≠ 0 := fun h => by rw [h, norm_zero] at hV; linarith [norm_nonneg ((B 1 0 : ℂ) / e)]
    have h1 : e * V + (B 1 0 : ℂ) = 0 := by
      have h2 := congrArg (· * V) h0
      simp only [zero_mul, add_mul, mul_assoc, one_div, inv_mul_cancel₀ hV0, mul_one] at h2
      exact h2
    have hc : (B 1 0 : ℂ) = -(e * V) := by linear_combination h1
    have h3 : ‖(B 1 0 : ℂ) / e‖ = ‖V‖ := by
      rw [hc, norm_div, norm_neg, norm_mul]
      exact mul_div_cancel_left₀ _ (norm_ne_zero_iff.2 he0)
    linarith
  have hmain : ∀ n, x n ≠ q ∧ 1 / (x n - q) = (e ^ 2) ^ n * ((R : ℂ) - vs) + vs := by
    intro n
    induction n with
    | zero =>
      have hx0 : x 0 = q + 1 / (R : ℂ) := rfl
      have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
      refine ⟨fun h => ?_, ?_⟩
      · rw [hx0] at h
        exact one_div_ne_zero hRc (by linear_combination h)
      · rw [hx0, add_sub_cancel_left, one_div_one_div, pow_zero, one_mul, sub_add_cancel]
    | succ n ih =>
      obtain ⟨hne, hv⟩ := ih
      have hd : (B 1 0 : ℂ) * x n + B 1 1 ≠ 0 := by
        have h := hdenV _ (hlow n)
        rw [← hv, one_div_one_div] at h
        intro h0
        apply h
        linear_combination h0 + he
      obtain ⟨hne', hv'⟩ := hrec (x n) hd hne
      refine ⟨by rw [hxs]; exact sub_ne_zero.1 hne', ?_⟩
      rw [hxs, hv', hv, pow_succ]
      linear_combination hvs_fix
  refine ⟨x, hxs, fun n => ?_, fun n => (hmain n).1, ?_⟩
  · have h := hdenV _ (hlow n)
    rw [← (hmain n).2, one_div_one_div] at h
    intro h0
    apply h
    linear_combination h0 + he
  · -- `‖xₙ − q‖ = 1/‖vₙ‖ → 0`
    have hvinf : Tendsto (fun n => ‖(e ^ 2) ^ n * ((R : ℂ) - vs) + vs‖) atTop atTop := by
      have hRv : 0 < ‖(R : ℂ) - vs‖ := by
        have := norm_sub_norm_le (R : ℂ) vs
        rw [Complex.norm_real, Real.norm_of_nonneg hR0.le] at this
        linarith [norm_nonneg ((B 1 0 : ℂ) / e), norm_nonneg vs]
      have hgrow : Tendsto (fun n : ℕ => ‖e ^ 2‖ ^ n * ‖(R : ℂ) - vs‖ - ‖vs‖) atTop atTop :=
        tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop_atTop_of_one_lt hL1).atTop_mul_const hRv)
      refine tendsto_atTop_mono (fun n => ?_) hgrow
      have := norm_sub_norm_le ((e ^ 2) ^ n * ((R : ℂ) - vs)) (-vs)
      rw [norm_neg, sub_neg_eq_add, norm_mul, norm_pow] at this
      linarith
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (hvinf.inv_tendsto_atTop).congr fun n => ?_
    show ‖(e ^ 2) ^ n * ((R : ℂ) - vs) + vs‖⁻¹ = ‖x n - q‖
    rw [← (hmain n).2, norm_div, norm_one, one_div, inv_inv]

/-- Helper for `lemma10_2` (§10.4): the entries of `A⁻¹ = (d, −b; −c, a)` for `A ∈ SL(2, ℝ)`. -/
theorem gl10_tl_inv_entry (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): `A⁻¹` has the trace of `A`, so it is hyperbolic with the same multiplier. -/
theorem gl10_tl_inv_hyp {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) :
    IsHyperbolic A⁻¹ ∧ multiplier A⁻¹ = multiplier A := by
  obtain ⟨e00, -, -, e11⟩ := gl10_tl_inv_entry A
  have ht : A⁻¹ 0 0 + A⁻¹ 1 1 = A 0 0 + A 1 1 := by rw [e00, e11, add_comm]
  have hA' : 2 < |A 0 0 + A 1 1| := hA
  refine ⟨show 2 < |A⁻¹ 0 0 + A⁻¹ 1 1| by rw [ht]; exact hA', ?_⟩
  show ((|A⁻¹ 0 0 + A⁻¹ 1 1| + Real.sqrt ((A⁻¹ 0 0 + A⁻¹ 1 1) ^ 2 - 4)) / 2) ^ 2 =
    ((|A 0 0 + A 1 1| + Real.sqrt ((A 0 0 + A 1 1) ^ 2 - 4)) / 2) ^ 2
  rw [ht]

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): for an affine `A` (`c = 0`), `z ↦ A z` and `z ↦ A⁻¹ z` are inverse bijections of
`ℂ` (`A z = (a z + b)/d`, `A⁻¹ z = (d z − b)/a`, `a d = 1`). -/
theorem gl10_tl_affine_inv {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : A 1 0 = 0) (ζ : ℂ) :
    h36p_m A⁻¹ (h36p_m A ζ) = ζ ∧ h36p_m A (h36p_m A⁻¹ ζ) = ζ := by
  obtain ⟨e00, e01, e10, e11⟩ := gl10_tl_inv_entry A
  have hdet := gl10_tl_det A
  rw [hc, Complex.ofReal_zero, mul_zero, sub_zero] at hdet
  have ha : (A 0 0 : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd : (A 1 1 : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  constructor
  · show ((A⁻¹ 0 0 : ℂ) * (((A 0 0 : ℂ) * ζ + A 0 1) / ((A 1 0 : ℂ) * ζ + A 1 1)) + A⁻¹ 0 1) /
      ((A⁻¹ 1 0 : ℂ) * (((A 0 0 : ℂ) * ζ + A 0 1) / ((A 1 0 : ℂ) * ζ + A 1 1)) + A⁻¹ 1 1) = ζ
    rw [e00, e01, e10, e11, hc]
    push_cast
    simp only [zero_mul, zero_add, neg_zero]
    field_simp
    ring
  · show ((A 0 0 : ℂ) * (((A⁻¹ 0 0 : ℂ) * ζ + A⁻¹ 0 1) / ((A⁻¹ 1 0 : ℂ) * ζ + A⁻¹ 1 1)) + A 0 1) /
      ((A 1 0 : ℂ) * (((A⁻¹ 0 0 : ℂ) * ζ + A⁻¹ 0 1) / ((A⁻¹ 1 0 : ℂ) * ζ + A⁻¹ 1 1)) + A 1 1) = ζ
    rw [e00, e01, e10, e11, hc]
    push_cast
    simp only [zero_mul, zero_add, neg_zero]
    field_simp
    ring

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): a hyperbolic `A` has a finite attracting fixed point (`|c q + d| > 1`), or it is
affine (`c = 0`) and `A⁻¹` has one. For `c ≠ 0`, `q = (e − d)/c` with `e = (t ± √(t² − 4))/2` of modulus `> 1`
(`t = a + d`); for `c = 0`, `q = b/(d − a)` with `e = d` for `A` and `e = a = 1/d` for `A⁻¹`. -/
theorem gl10_tl_fixpt {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) :
    (∃ q : ℂ, (A 1 0 : ℂ) * q + A 1 1 ≠ 0 ∧ h36p_m A q = q ∧ 1 < ‖(A 1 0 : ℂ) * q + A 1 1‖) ∨
      (A 1 0 = 0 ∧ ∃ q : ℂ, (A⁻¹ 1 0 : ℂ) * q + A⁻¹ 1 1 ≠ 0 ∧ h36p_m A⁻¹ q = q ∧
        1 < ‖(A⁻¹ 1 0 : ℂ) * q + A⁻¹ 1 1‖) := by
  have ht : 2 < |A 0 0 + A 1 1| := hA
  have hdetR : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by exact_mod_cast gl10_tl_det A
  have ht2 : 4 < (A 0 0 + A 1 1) ^ 2 := by nlinarith [sq_abs (A 0 0 + A 1 1), abs_nonneg (A 0 0 + A 1 1)]
  by_cases hc : A 1 0 = 0
  · -- the affine case
    rw [hc, mul_zero, sub_zero] at hdetR
    have hda : A 1 1 - A 0 0 ≠ 0 := by
      intro h
      have h1 : A 1 1 = A 0 0 := by linarith
      rw [h1] at hdetR ht2
      nlinarith
    set q₀ : ℝ := A 0 1 / (A 1 1 - A 0 0) with hq₀
    have hfix : A 0 0 * q₀ + A 0 1 = A 1 1 * q₀ := by
      rw [hq₀]
      field_simp
      ring
    have hd1 : |A 1 1| ≠ 1 := by
      intro h
      rcases abs_eq (zero_le_one' ℝ) |>.1 h with h1 | h1
      · rw [h1] at hdetR hda
        apply hda
        linarith
      · rw [h1] at hdetR hda
        apply hda
        linarith
    rcases lt_or_gt_of_ne hd1 with hlt | hgt
    · right
      obtain ⟨e00, e01, e10, e11⟩ := gl10_tl_inv_entry A
      have ha1 : 1 < |A 0 0| := by
        have h1 : |A 0 0| * |A 1 1| = 1 := by rw [← abs_mul, hdetR, abs_one]
        have h2 : 0 < |A 1 1| := by
          rcases eq_or_ne (A 1 1) 0 with h0 | h0
          · rw [h0, mul_zero] at hdetR; norm_num at hdetR
          · exact abs_pos.2 h0
        nlinarith
      have hden : (A⁻¹ 1 0 : ℂ) * (q₀ : ℂ) + A⁻¹ 1 1 = (A 0 0 : ℂ) := by
        rw [e10, e11, hc]
        simp
      refine ⟨hc, (q₀ : ℂ), ?_, ?_, ?_⟩
      · rw [hden]
        exact_mod_cast (abs_pos.1 (by linarith : (0 : ℝ) < |A 0 0|))
      · show ((A⁻¹ 0 0 : ℂ) * q₀ + A⁻¹ 0 1) / ((A⁻¹ 1 0 : ℂ) * q₀ + A⁻¹ 1 1) = q₀
        rw [hden, e00, e01, div_eq_iff (by exact_mod_cast (abs_pos.1 (by linarith : (0 : ℝ) < |A 0 0|)))]
        exact_mod_cast (by linarith [hfix] : A 1 1 * q₀ + -A 0 1 = q₀ * A 0 0)
      · rw [hden, Complex.norm_real, Real.norm_eq_abs]
        exact ha1
    · left
      have hden : (A 1 0 : ℂ) * (q₀ : ℂ) + A 1 1 = (A 1 1 : ℂ) := by
        rw [hc]
        simp
      refine ⟨(q₀ : ℂ), ?_, ?_, ?_⟩
      · rw [hden]
        exact_mod_cast (abs_pos.1 (by linarith : (0 : ℝ) < |A 1 1|))
      · show ((A 0 0 : ℂ) * q₀ + A 0 1) / ((A 1 0 : ℂ) * q₀ + A 1 1) = q₀
        rw [hden, div_eq_iff (by exact_mod_cast (abs_pos.1 (by linarith : (0 : ℝ) < |A 1 1|)))]
        have h := hfix
        exact_mod_cast (by linarith [h] : A 0 0 * q₀ + A 0 1 = q₀ * A 1 1)
      · rw [hden, Complex.norm_real, Real.norm_eq_abs]
        exact hgt
  · -- `c ≠ 0`: both fixed points are finite; take the attracting one
    left
    set t := A 0 0 + A 1 1 with htdef
    set s := Real.sqrt (t ^ 2 - 4) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hs2 : s ^ 2 = t ^ 2 - 4 := Real.sq_sqrt (by linarith)
    obtain ⟨e, he, he1⟩ : ∃ e : ℝ, e ^ 2 - t * e + 1 = 0 ∧ 1 < |e| := by
      rcases lt_or_gt_of_ne (show t ≠ 0 by intro h; rw [h] at ht2; norm_num at ht2) with hneg | hpos
      · refine ⟨(t - s) / 2, by linear_combination hs2 / 4, ?_⟩
        have : 2 < -t := by rw [abs_of_neg hneg] at ht; exact ht
        rw [abs_of_neg (by linarith)]
        linarith
      · refine ⟨(t + s) / 2, by linear_combination hs2 / 4, ?_⟩
        have : 2 < t := by rw [abs_of_pos hpos] at ht; exact ht
        rw [abs_of_pos (by linarith)]
        linarith
    set q : ℝ := (e - A 1 1) / A 1 0 with hq
    have hden : A 1 0 * q + A 1 1 = e := by
      rw [hq]
      field_simp
      ring
    have hfix : A 0 0 * q + A 0 1 = q * (A 1 0 * q + A 1 1) := by
      rw [hden, hq]
      field_simp
      linear_combination -he - hdetR - e * htdef
    have he0 : e ≠ 0 := fun h => by rw [h, abs_zero] at he1; linarith
    have hdenC : (A 1 0 : ℂ) * (q : ℂ) + A 1 1 = (e : ℂ) := by exact_mod_cast hden
    refine ⟨(q : ℂ), ?_, ?_, ?_⟩
    · rw [hdenC]
      exact_mod_cast he0
    · show ((A 0 0 : ℂ) * q + A 0 1) / ((A 1 0 : ℂ) * q + A 1 1) = q
      rw [div_eq_iff (by rw [hdenC]; exact_mod_cast he0)]
      exact_mod_cast hfix
    · rw [hdenC, Complex.norm_real, Real.norm_eq_abs]
      exact he1

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): a converging orbit and its image. Replace `A₁, A₂` by `A₁⁻¹, A₂⁻¹` if needed (same
multipliers). Then `B₁` has a finite attracting fixed point `q` and an orbit `xₙ → q`; `x₀` is taken in a small
ball around `q`, which avoids the repelling fixed point of `B₁`. The map `w` sends them to a
finite fixed point `w(q)` of `B₂` and to the `B₂`-orbit of `w(x₀)`. This uses the conjugacy `hconj` near `q`, away
from the two poles, and the continuity of `w`: `w(q)` is not the pole of `B₂`, because `w(B₁ xₙ) → w(q)` is finite. -/
theorem gl10_tl_orbit {A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h₁ : IsHyperbolic A₁) (h₂ : IsHyperbolic A₂)
    {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K) (honto : w '' univ = univ)
    (hconj : ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 → (A₂ 1 0 : ℂ) * w z + A₂ 1 1 ≠ 0 →
      w (h36p_m A₁ z) = h36p_m A₂ (w z)) :
    ∃ B₁ B₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsHyperbolic B₁ ∧ IsHyperbolic B₂ ∧
      multiplier B₁ = multiplier A₁ ∧ multiplier B₂ = multiplier A₂ ∧ ∃ (q : ℂ) (x : ℕ → ℂ),
        ((B₁ 1 0 : ℂ) * q + B₁ 1 1 ≠ 0 ∧ h36p_m B₁ q = q ∧ (∀ n, x (n + 1) = h36p_m B₁ (x n)) ∧
          (∀ n, (B₁ 1 0 : ℂ) * x n + B₁ 1 1 ≠ 0) ∧ (∀ n, x n ≠ q) ∧ Tendsto x atTop (𝓝 q)) ∧
        ((B₂ 1 0 : ℂ) * w q + B₂ 1 1 ≠ 0 ∧ h36p_m B₂ (w q) = w q ∧
          (∀ n, w (x (n + 1)) = h36p_m B₂ (w (x n))) ∧ (∀ n, (B₂ 1 0 : ℂ) * w (x n) + B₂ 1 1 ≠ 0) ∧
          (∀ n, w (x n) ≠ w q) ∧ Tendsto (fun n => w (x n)) atTop (𝓝 (w q))) := by
  have hc : Continuous w := continuousOn_univ.mp hw.2.2.1.1
  have hinj : Function.Injective w := injOn_univ.mp hw.2.2.1.2.1
  have hsurj : Function.Surjective w := fun ζ => by
    have hmem : ζ ∈ w '' univ := by rw [honto]; exact mem_univ ζ
    obtain ⟨a, -, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hpole := gl10_tl_pole hw hconj
  rcases gl10_tl_fixpt h₁ with ⟨q, hqd, hq, he1⟩ | ⟨hc₁, q, hqd, hq, he1⟩
  · -- `A₁` has a finite attracting fixed point
    obtain ⟨x, hx, hxd, hxq, hxl⟩ := gl10_tl_attract hqd hq he1
    refine ⟨A₁, A₂, h₁, h₂, rfl, rfl, q, x, ⟨hqd, hq, hx, hxd, hxq, hxl⟩,
      ⟨hpole q hqd, ?_, ?_, fun n => hpole _ (hxd n), ?_, (hc.tendsto q).comp hxl⟩⟩
    · have h := hconj q hqd (hpole q hqd)
      rw [hq] at h
      exact h.symm
    · intro n
      rw [hx n]
      exact hconj _ (hxd n) (hpole _ (hxd n))
    · intro n h
      exact hxq n (hinj h)
  · -- `A₁` is affine with a repelling finite fixed point: use `A₁⁻¹`, `A₂⁻¹`
    have hdet₁ := gl10_tl_det A₁
    rw [hc₁, Complex.ofReal_zero, mul_zero, sub_zero] at hdet₁
    have hden₁ : ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 := fun z => by
      rw [hc₁, Complex.ofReal_zero, zero_mul, zero_add]
      exact right_ne_zero_of_mul_eq_one hdet₁
    -- `A₂` is affine too: `w` is onto and never meets the pole of `A₂`
    have hc₂ : A₂ 1 0 = 0 := by
      by_contra hc2
      have hc2' : (A₂ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc2
      obtain ⟨z, hz⟩ := hsurj (-(A₂ 1 1 : ℂ) / A₂ 1 0)
      apply hpole z (hden₁ z)
      rw [hz]
      field_simp
      ring
    have hdet₂ := gl10_tl_det A₂
    rw [hc₂, Complex.ofReal_zero, mul_zero, sub_zero] at hdet₂
    obtain ⟨-, -, f10, f11⟩ := gl10_tl_inv_entry A₂
    have hden₂ : ∀ ζ : ℂ, (A₂⁻¹ 1 0 : ℂ) * ζ + A₂⁻¹ 1 1 ≠ 0 := fun ζ => by
      rw [f10, f11, hc₂, neg_zero, Complex.ofReal_zero, zero_mul, zero_add]
      exact left_ne_zero_of_mul_eq_one hdet₂
    -- the conjugacy for the inverses
    have hconjinv : ∀ z : ℂ, w (h36p_m A₁⁻¹ z) = h36p_m A₂⁻¹ (w z) := by
      intro z
      have h := hconj (h36p_m A₁⁻¹ z) (hden₁ _) (hpole _ (hden₁ _))
      rw [(gl10_tl_affine_inv hc₁ z).2] at h
      rw [h, (gl10_tl_affine_inv hc₂ _).1]
    obtain ⟨hh₁, hm₁⟩ := gl10_tl_inv_hyp h₁
    obtain ⟨hh₂, hm₂⟩ := gl10_tl_inv_hyp h₂
    obtain ⟨x, hx, hxd, hxq, hxl⟩ := gl10_tl_attract hqd hq he1
    refine ⟨A₁⁻¹, A₂⁻¹, hh₁, hh₂, hm₁, hm₂, q, x, ⟨hqd, hq, hx, hxd, hxq, hxl⟩,
      ⟨hden₂ _, ?_, ?_, fun n => hden₂ _, ?_, (hc.tendsto q).comp hxl⟩⟩
    · rw [← hconjinv, hq]
    · intro n
      rw [hx n, hconjinv]
    · intro n h
      exact hxq n (hinj h)

open LiZhongQC in
/-- Helper for `lemma10_2` (§10.4): the inverse map. The inverse `v` of `w` is a `K`-quasiconformal homeomorphism of
the plane onto itself (`thm7_2_inv`) and conjugates `A₂` to `A₁`. -/
theorem gl10_tl_inv {A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K)
    (honto : w '' univ = univ)
    (hconj : ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 → (A₂ 1 0 : ℂ) * w z + A₂ 1 1 ≠ 0 →
      w (h36p_m A₁ z) = h36p_m A₂ (w z)) :
    ∃ v : ℂ → ℂ, IsKQC v univ K ∧ v '' univ = univ ∧
      ∀ ζ : ℂ, (A₂ 1 0 : ℂ) * ζ + A₂ 1 1 ≠ 0 → (A₁ 1 0 : ℂ) * v ζ + A₁ 1 1 ≠ 0 →
        v (h36p_m A₂ ζ) = h36p_m A₁ (v ζ) := by
  set v := Function.invFunOn w univ with hvdef
  have hv1 : IsKQC v univ K := by
    have h := LiZhongQC.thm7_2_inv hw
    rwa [honto] at h
  have hinj : InjOn w univ := hw.2.2.1.2.1
  have hleft : ∀ z, v (w z) = z := fun z => hinj.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ ζ, w (v ζ) = ζ := fun ζ => by
    have hmem : ζ ∈ w '' univ := by rw [honto]; exact mem_univ ζ
    obtain ⟨a, ha, hwa⟩ := hmem
    exact Function.invFunOn_eq ⟨a, ha, hwa⟩
  refine ⟨v, hv1, eq_univ_of_forall fun z => ⟨w z, mem_univ _, hleft z⟩, ?_⟩
  intro ζ h2 h1
  have h2' : (A₂ 1 0 : ℂ) * w (v ζ) + A₂ 1 1 ≠ 0 := by rwa [hright ζ]
  have h := hconj (v ζ) h1 h2'
  rw [hright ζ] at h
  rw [← h, hleft]

/-- Helper for `lemma10_2` (§10.4): the limit `n → ∞`. If `log(ρ/(C λ₁⁻ⁿ)) ≤ K log 16(1 + D/(c λ₂⁻ⁿ))` for all large
`n`, then `log λ₁ ≤ K log λ₂`. The left side is `log(ρ/C) + n log λ₁`, the right side is at most
`K(log 16 + log(1 + D/c) + n log λ₂)`; divide by `n`. -/
theorem gl10_tl_limit {l₁ l₂ K C c D ρ : ℝ} (hl₁ : 1 < l₁) (hl₂ : 1 < l₂) (hK : 0 < K) (hC : 0 < C) (hc : 0 < c)
    (hD : 0 ≤ D) (hρ : 0 < ρ)
    (h : ∀ᶠ n : ℕ in atTop, Real.log (ρ / (C * l₁⁻¹ ^ n)) ≤ K * Real.log (16 * (1 + D / (c * l₂⁻¹ ^ n)))) :
    Real.log l₁ ≤ K * Real.log l₂ := by
  have hX : 0 ≤ D / c := div_nonneg hD hc.le
  set M : ℝ := K * (Real.log 16 + Real.log (1 + D / c)) - Real.log (ρ / C) with hM
  have hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (Real.log l₁ - K * Real.log l₂) ≤ M := by
    filter_upwards [h] with n hn
    have hl₁n : 0 < l₁ ^ n := pow_pos (by linarith) n
    have hl₂n : 1 ≤ l₂ ^ n := one_le_pow₀ hl₂.le
    have hl₂n' : 0 < l₂ ^ n := by linarith
    have e1 : ρ / (C * l₁⁻¹ ^ n) = ρ / C * l₁ ^ n := by
      rw [inv_pow]
      field_simp
    have e2 : D / (c * l₂⁻¹ ^ n) = D / c * l₂ ^ n := by
      rw [inv_pow]
      field_simp
    rw [e1, e2, Real.log_mul (by positivity) hl₁n.ne', Real.log_pow] at hn
    have h3 : Real.log (16 * (1 + D / c * l₂ ^ n)) ≤
        Real.log 16 + Real.log (1 + D / c) + n * Real.log l₂ := by
      have hle : 16 * (1 + D / c * l₂ ^ n) ≤ 16 * ((1 + D / c) * l₂ ^ n) := by nlinarith
      calc Real.log (16 * (1 + D / c * l₂ ^ n)) ≤ Real.log (16 * ((1 + D / c) * l₂ ^ n)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log 16 + Real.log (1 + D / c) + n * Real.log l₂ := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hl₂n'.ne',
              Real.log_pow]
            ring
    have h4 := mul_le_mul_of_nonneg_left h3 hK.le
    rw [hM]
    nlinarith
  by_contra hlt
  have hδ : 0 < Real.log l₁ - K * Real.log l₂ := by linarith [not_le.1 hlt]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  obtain ⟨m, hm⟩ := exists_nat_gt (M / (Real.log l₁ - K * Real.log l₂))
  have h5 := hN (max N m) (le_max_left _ _)
  have hmax : (m : ℝ) ≤ ((max N m : ℕ) : ℝ) := by exact_mod_cast le_max_right N m
  have h6 : M / (Real.log l₁ - K * Real.log l₂) < ((max N m : ℕ) : ℝ) := lt_of_lt_of_le hm hmax
  rw [div_lt_iff₀ hδ] at h6
  linarith

/-- **Lemma 2** (Teichmüller, (10.9), §10.4, l. 8184). If `A₁`, `A₂` are hyperbolic with multipliers `λ₁, λ₂ > 1` and
`w` is a `K`-quasiconformal homeomorphism of the plane with `w ∘ A₁ = A₂ ∘ w`, then
`K⁻¹ log λ₂ ≤ log λ₁ ≤ K log λ₂`. -/
theorem lemma10_2 {A₁ A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h₁ : IsHyperbolic A₁) (h₂ : IsHyperbolic A₂)
    {w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K) (honto : w '' univ = univ)
    (hconj : ∀ z : ℂ, (A₁ 1 0 : ℂ) * z + A₁ 1 1 ≠ 0 → (A₂ 1 0 : ℂ) * w z + A₂ 1 1 ≠ 0 →
      w (h36p_m A₁ z) = h36p_m A₂ (w z)) :
    K⁻¹ * Real.log (multiplier A₂) ≤ Real.log (multiplier A₁) ∧
      Real.log (multiplier A₁) ≤ K * Real.log (multiplier A₂) := by
  have hK : 0 < K := by linarith [hw.2.1]
  -- the one-sided inequality `log λ₁ ≤ K log λ₂`, for any conjugating `K`-q.c. homeomorphism
  have key : ∀ (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (u : ℂ → ℂ), IsHyperbolic A → IsHyperbolic B →
      IsKQC u univ K → u '' univ = univ →
      (∀ z : ℂ, (A 1 0 : ℂ) * z + A 1 1 ≠ 0 → (B 1 0 : ℂ) * u z + B 1 1 ≠ 0 →
        u (h36p_m A z) = h36p_m B (u z)) →
      Real.log (multiplier A) ≤ K * Real.log (multiplier B) := by
    intro A B u hA hB hu hon hc
    obtain ⟨E₁, E₂, hE₁, hE₂, hm₁, hm₂, q, x, ⟨hqd, hq, hx, hxd, hxq, hxl⟩,
      ⟨hwqd, hwq, hwx, hwxd, hwxq, hwxl⟩⟩ := gl10_tl_orbit hA hB hu hon hc
    obtain ⟨hl₁, c₁, k₁, hc₁, hk₁, hr₁⟩ := gl10_tl_rate hE₁ hqd hq hx hxd hxq hxl
    obtain ⟨hl₂, c₂, k₂, hc₂, hk₂, hr₂⟩ := gl10_tl_rate hE₂ hwqd hwq hwx hwxd hwxq hwxl
    rw [← hm₁, ← hm₂]
    refine gl10_tl_limit hl₁ hl₂ hK hk₁ hc₂ (norm_nonneg (u (q + 1) - u q)) one_pos ?_
    have hev : ∀ᶠ n in atTop, x n ∈ ball q 1 := hxl.eventually (ball_mem_nhds q one_pos)
    filter_upwards [hev] with n hn
    have hn' : ‖x n - q‖ < 1 := by rw [← dist_eq_norm]; exact hn
    have hy : ‖q + 1 - q‖ = 1 := by rw [add_sub_cancel_left, norm_one]
    have hring := gl10_tl_ring hu hon (hxq n) hn' hy
    have hpos : 0 < ‖x n - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (hxq n))
    have hupos : 0 < ‖u (x n) - u q‖ := norm_pos_iff.2 (sub_ne_zero.2 (hwxq n))
    have hθ₁ : 0 < k₁ * (multiplier E₁)⁻¹ ^ n := by
      have : 0 < multiplier E₁ := by linarith
      positivity
    have hθ₂ : 0 < c₂ * (multiplier E₂)⁻¹ ^ n := by
      have : 0 < multiplier E₂ := by linarith
      positivity
    calc Real.log (1 / (k₁ * (multiplier E₁)⁻¹ ^ n)) ≤ Real.log (1 / ‖x n - q‖) :=
          Real.log_le_log (by positivity) (one_div_le_one_div_of_le hpos (hr₁ n).2)
      _ ≤ K * Real.log (16 * (1 + ‖u (q + 1) - u q‖ / ‖u (x n) - u q‖)) := hring
      _ ≤ K * Real.log (16 * (1 + ‖u (q + 1) - u q‖ / (c₂ * (multiplier E₂)⁻¹ ^ n))) := by
          refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hK.le
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
          exact div_le_div_of_nonneg_left (norm_nonneg _) hθ₂ (hr₂ n).1
  -- both directions: `w` and its inverse
  obtain ⟨v, hv, hvon, hvc⟩ := gl10_tl_inv hw honto hconj
  have h1 := key A₁ A₂ w h₁ h₂ hw honto hconj
  have h2 := key A₂ A₁ v h₂ h₁ hv hvon hvc
  exact ⟨(inv_mul_le_iff₀ hK).2 h2, h1⟩

/-- Helper (§10.4, l. 8171). `K ⊆ T(Γ)` is (sequentially) compact for Teichmüller's metric. -/
def IsSeqCompactT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (K : Set (TeichGamma Γ)) : Prop :=
  ∀ u : ℕ → TeichGamma Γ, (∀ n, u n ∈ K) → ∃ P ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => teichDistanceGamma (u (φ n)) P) atTop (𝓝 0)

/-- **Definition** (§10.4, l. 8171). `MCG(Γ)` acts discontinuously on `T(Γ)`: for every compact `K ⊆ T(Γ)` only
finitely many mapping classes `h` have `h(K) ∩ K ≠ ∅`. -/
def McgActsDiscontinuously (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ∀ K : Set (TeichGamma Γ), IsSeqCompactT Γ K →
    {m : mcgGamma Γ | ∃ h : qcNormalizer Γ, Quot.mk _ h = m ∧ ∃ Φ : TeichGamma Γ → TeichGamma Γ,
      IsRhoGamma Γ Γ h.1 Φ ∧ (Φ '' K ∩ K).Nonempty}.Finite

/-- **Theorem 4** (§10.4, l. 8217). For a finitely generated Fuchsian group `Γ` of the first kind (`R = ℍ/Γ` of finite
analytic type, as in the §10.4 introduction), `MCG(Γ)` acts discontinuously on `T(Γ)`.
[CORRECTION] (AUDIT5_GL P2) The hypothesis `hfirst` (limit set `ℝ̂`) is added. For `Γ` of the second kind the statement
is false: for `Γ = ⟨z ↦ 4z⟩`, boundary twists `h_n` with `K(h_n) → 1` give infinitely many classes moving `0` into the
compact set `{0} ∪ {ρ_{h_n}(0)}`. The book's step "`h` fixes the origin" uses the first kind. -/
theorem thm10_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ)
    (hfirst : LiZhongQC.fuchsianLimitSet Γ = LiZhongQC.extRealLine) :
    McgActsDiscontinuously Γ := by
  sorry

end GardinerLakic2000
