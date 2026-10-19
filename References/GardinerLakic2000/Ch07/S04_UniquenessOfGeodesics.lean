import References.GardinerLakic2000.Ch07.S03_LiftingTheorem

/-!
# Gardiner–Lakic 2000, Ch. 7 §7.4 Uniqueness of geodesics

Source `teichmuller.txt`, lines 6387–6515.

* Definition (geometric segment, l. 6388–6393) — `IsGeodesicSegment`
* Unlabelled (§7.4, l. 6394–6402; used in Theorem 3 and l. 4408: `t ↦ [tμ/‖μ‖∞]` is a geodesic segment from the
  basepoint to `[μ]`, `μ` extremal) — `para7_4_geodesic_exists`
* Definition (uniquely extremal Beltrami coefficient, l. 6402) — `IsUniquelyExtremal`
* Definition (holomorphic isometry `Δ → T(R)`, l. 6403) — `IsHolIsometry`
* Definition (Teichmüller disc, l. 6403; cited Ch. 8, l. 6588) — `teichmullerDisc`
* Theorem 3 (the four conditions (a)–(d), l. 6405; cited l. 7859) — `thm7_3`

Not items (DESIGN §3): the claims for surfaces of finite analytic type (l. 6402–6403; Teichmüller's theorems of
Ch. 4), (7.17), (7.18), steps of the proof.

[misprint] The geodesic segment is defined by `d(f(x), f(y)) = d(f(x), f(z)) + d(f(z), f(y))` "whenever
`a ≤ x ≤ y ≤ z ≤ b`" (l. 6392, GL8:6224); the point `z` between `x` and `y` is meant: `a ≤ x ≤ z ≤ y ≤ b`.

Near miss (dupcheck): `Katok1992.IsGeodesicSegment` (unit-speed hyperbolic geodesics in `ℍ`); the book's notion is
for the Teichmüller metric, with any parametrization.

**Conventions.** The Fuchsian model of §7.2 (`M(G)`, `T(G)`, `teichDistanceGamma`, `holDiscsT`, `holDiscsM`); an
extremal coefficient is `LiZhongQC.IsExtremalModBoundary`; `‖μ‖∞ = LiZhongQC.beltramiNormH μ`. Continuity of a
segment is for the Teichmüller metric. "Only one geodesic segment joining the base point and `[μ]`" is read as: all
such segments have the same image [reading]. A Teichmüller disc is the image `{[t |φ|/φ] : |t| < 1}` of the
holomorphic isometry (7.16) with `μ = k|φ|/φ`, `φ ∈ A(G)`, `‖φ‖ = 1` (`|φ|/φ = φ̄/|φ|`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc upperHalf discPoincareDist BeltramiGamma TeichGamma teichDistanceGamma IsFuchsian
  IsExtremalModBoundary beltramiNormH teichSetoidGamma integrableAutomorphicQD phiArea IsFundamentalDomainH)

/-- **Definition** (geodesic segment, §7.4, l. 6388). The image of an injective continuous map `f` of `[a, b]` such
that `d(f(x), f(y)) = d(f(x), f(z)) + d(f(z), f(y))` whenever `a ≤ x ≤ z ≤ y ≤ b` [misprint corrected, see the
module docstring]; it joins `f(a)` to `f(b)`. -/
def IsGeodesicSegment {X : Type*} (d : X → X → ℝ) (f : ℝ → X) (a b : ℝ) : Prop :=
  a < b ∧ InjOn f (Icc a b) ∧
    (∀ s ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc a b, |t - s| < δ → d (f s) (f t) < ε) ∧
    ∀ x z y, a ≤ x → x ≤ z → z ≤ y → y ≤ b → d (f x) (f y) = d (f x) (f z) + d (f z) (f y)

/-- Helper (S1, transport) for §7.4. For `ν' ∼ ν` in `M(G)` and `ρ ∈ M(G)` there is `ρ'' ∼ ρ` in `M(G)` with
`‖(ν − ρ'')/(1 − ρ̄''ν)‖∞ = ‖(ν' − ρ)/(1 − ρ̄ν')‖∞`: `f_{ρ''} = f_ρ ∘ f_{ν'}⁻¹ ∘ f_ν` (`ut_transport`, `ut_welding`),
and it is `G`-equivariant since `f_ν` and `f_{ν'}` agree on `ℝ̂` and so conjugate each `γ ∈ G` to the same Möbius
map (`h36p_d_rel`, `h36p_d_mob_eq`, `h36p_d_comm`, `h36p_d_compat`). -/
theorem gl7_transport {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ν ν' : BeltramiGamma Γ}
    (h : teichSetoidGamma Γ ν' ν) (ρ : BeltramiGamma Γ) :
    ∃ ρ'' : BeltramiGamma Γ, teichSetoidGamma Γ ρ'' ρ ∧
      LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν.1.1 ρ''.1.1 =
        LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν'.1.1 ρ.1.1 := by
  have hU : LiZhongQC.teichSetoid ν'.1 ν.1 := (LiZhongQC.lemma33_1 ν'.1 ν.1).1 h
  set fν := LiZhongQC.normalizedSolution ν.1.1 with hfν
  set fν' := LiZhongQC.normalizedSolution ν'.1.1 with hfν'
  set fρ := LiZhongQC.normalizedSolution ρ.1.1 with hfρ
  set g := Function.invFunOn fν' univ with hgdef
  set F : ℂ → ℂ := fρ ∘ g ∘ fν with hFdef
  obtain ⟨K, hFK, hFs, hF0, hF1, hFL⟩ := LiZhongQC.ut_rg_comp_spec hU ρ.1 hFdef
  obtain ⟨⟨Kν', hKν'⟩, hsν', h0ν', -, -⟩ := LiZhongQC.ut_spec ν'.1
  obtain ⟨⟨Kν, hKν⟩, -, h0ν, -, -⟩ := LiZhongQC.ut_spec ν.1
  have hiν' : Function.Injective fν' := injOn_univ.1 hKν'.2.2.1.2.1
  have hiν : Function.Injective fν := injOn_univ.1 hKν.2.2.1.2.1
  have hleft : ∀ z, g (fν' z) = z := fun z => hKν'.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, fν' (g w) = w := fun w =>
    Function.invFunOn_eq (show w ∈ fν' '' univ by rw [hsν']; exact mem_univ w)
  have hFd : DifferentiableOn ℂ F LiZhongQC.lowerHalf :=
    (LiZhongQC.ut_conformal_lowerHalf ρ.1).1.congr fun z hz => hFL z (le_of_lt hz)
  have hnorm : LiZhongQC.normalizedSolution (upperHalf.indicator (LiZhongQC.complexDilatation F)) = F :=
    LiZhongQC.h36p_d_norm_eq hFK hFs hF0 hF1 hFd
  -- `F` is `Γ`-equivariant: `g ∘ f_ν = f_{ν'}⁻¹ ∘ f_ν` commutes with every `γ ∈ Γ`
  have hrelF : ∀ γ ∈ Γ, ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z, F (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = LiZhongQC.mobiusFn A B C D (F z) := by
    intro γ hγ
    obtain ⟨A, B, C, D, hd, hr⟩ := LiZhongQC.h36p_d_rel ν.1 ν.2 hγ
    obtain ⟨A', B', C', D', hd', hr'⟩ := LiZhongQC.h36p_d_rel ν'.1 ν'.2 hγ
    have heq : EqOn fν' fν LiZhongQC.lowerHalf := fun z hz => (LiZhongQC.ut_welding hU).1 z (le_of_lt hz)
    have hM := LiZhongQC.h36p_d_mob_eq hiν' hiν h0ν' h0ν heq γ hd' hd hr' hr
    have hcomm := LiZhongQC.h36p_d_comm (H := fν') (B := fν) (P := g ∘ fν)
      (T := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) (M := LiZhongQC.mobiusFn A B C D) hiν'
      (fun z => hright (fν z)) (fun z => (hr' z).trans (hM _)) hr
    obtain ⟨Aρ, Bρ, Cρ, Dρ, hdρ, hrρ⟩ := LiZhongQC.h36p_d_rel ρ.1 ρ.2 hγ
    refine ⟨Aρ, Bρ, Cρ, Dρ, hdρ, fun z => ?_⟩
    have h1 := hcomm z
    simp only [Function.comp_apply] at h1
    show fρ (g (fν (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z))) =
      LiZhongQC.mobiusFn Aρ Bρ Cρ Dρ (fρ (g (fν z)))
    rw [h1]
    exact hrρ _
  have hiF : Function.Injective F := injOn_univ.1 hFK.2.2.1.2.1
  have hF0' : ∀ z ∈ upperHalf, F z ≠ 0 := fun z hz h0 => by
    have hz0 : z = 0 := hiF (h0.trans hF0.symm)
    rw [hz0] at hz
    simp [upperHalf] at hz
  have hμΓ : LiZhongQC.IsGammaCompatible Γ (upperHalf.indicator (LiZhongQC.complexDilatation F)) :=
    LiZhongQC.h36p_d_compat (continuousOn_univ.1 hFK.2.2.1.1) hF0' hrelF
  refine ⟨⟨⟨upperHalf.indicator (LiZhongQC.complexDilatation F), LiZhongQC.ut_rg_indicator_mem hFK⟩, hμΓ⟩, ?_, ?_⟩
  · -- the class: `F = f_ρ` on `ℝ`, since `g ∘ f_ν = id` on `ℝ`
    refine (LiZhongQC.lemma33_1 ⟨upperHalf.indicator (LiZhongQC.complexDilatation F),
      LiZhongQC.ut_rg_indicator_mem hFK⟩ ρ.1).2 fun x => ?_
    show LiZhongQC.normalizedSolution (upperHalf.indicator (LiZhongQC.complexDilatation F)) x = fρ x
    rw [hnorm]
    show fρ (g (fν x)) = fρ x
    have hx : fν x = fν' x := (hU x).symm
    rw [hx, hleft]
  · -- the dilatation: `f_{ρ''} ∘ f_ν⁻¹ = f_ρ ∘ f_{ν'}⁻¹` and `f_ν(ℍ) = f_{ν'}(ℍ)`
    set ρ'' : LiZhongQC.BeltramiH := ⟨upperHalf.indicator (LiZhongQC.complexDilatation F),
      LiZhongQC.ut_rg_indicator_mem hFK⟩ with hρ''
    have hsurj : ∀ w, fν (Function.invFunOn fν univ w) = w := by
      obtain ⟨-, hsν, -, -, -⟩ := LiZhongQC.ut_spec ν.1
      exact fun w => Function.invFunOn_eq (show w ∈ fν '' univ by rw [hsν]; exact mem_univ w)
    have hcomp : LiZhongQC.normalizedSolution ρ''.1 ∘ Function.invFunOn fν univ = fρ ∘ g := by
      funext w
      show LiZhongQC.normalizedSolution (upperHalf.indicator (LiZhongQC.complexDilatation F))
        (Function.invFunOn fν univ w) = fρ (g w)
      rw [hnorm]
      show fρ (g (fν (Function.invFunOn fν univ w))) = fρ (g w)
      rw [hsurj]
    have hv : LiZhongQC.ut_v ν.1 ρ'' = LiZhongQC.ut_v ν'.1 ρ.1 := by
      show Real.log (LiZhongQC.maxDilatation (LiZhongQC.normalizedSolution ρ''.1 ∘ Function.invFunOn fν univ)
        (fν '' upperHalf)).toReal = Real.log (LiZhongQC.maxDilatation (fρ ∘ g) (fν' '' upperHalf)).toReal
      rw [hcomp, (LiZhongQC.ut_welding hU).2]
    obtain ⟨ha1, hae⟩ := LiZhongQC.UniversalTeichmuller.ut_v_eq ν.1 ρ''
    obtain ⟨hb1, hbe⟩ := LiZhongQC.UniversalTeichmuller.ut_v_eq ν'.1 ρ.1
    rw [hae, hbe] at hv
    have ha0 : 0 ≤ LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν.1.1 ρ''.1 := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν'.1.1 ρ.1.1 := ENNReal.toReal_nonneg
    have hv' : (1 / 2) * Real.log ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν.1.1 ρ''.1) /
        (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν.1.1 ρ''.1)) =
        (1 / 2) * Real.log ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν'.1.1 ρ.1.1) /
        (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm ν'.1.1 ρ.1.1)) := by rw [hv]
    exact le_antisymm ((l21b_halfLog_mono hb0 hb1 ha0 ha1).1 hv'.le) ((l21b_halfLog_mono ha0 ha1 hb0 hb1).1 hv'.ge)

/-- Helper (S2) for §7.4. The Teichmüller distance is at most the value on representatives:
`d([μ], [ν]) ≤ ½ log((1 + δ)/(1 − δ))`, `δ = ‖(μ − ν)/(1 − ν̄μ)‖∞`. -/
theorem gl7_teichDist_le {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ ν : BeltramiGamma Γ) :
    teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ≤
      (1 / 2) * Real.log ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1) /
        (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1)) := by
  obtain ⟨h0, h1, -⟩ := LiZhongQC.bg_d_teichDelta_spec (Quotient.mk (teichSetoidGamma Γ) μ)
    (Quotient.mk (teichSetoidGamma Γ) ν)
  have hd1 := (LiZhongQC.UniversalTeichmuller.ut_v_eq μ.1 ν.1).1
  have hle : LiZhongQC.teichDeltaGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ≤
      LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1 := by
    refine csInf_le ⟨0, ?_⟩ ⟨μ, ν, rfl, rfl, rfl⟩
    rintro d ⟨μ', ν', -, -, rfl⟩
    exact ENNReal.toReal_nonneg
  exact (l21b_halfLog_mono (ENNReal.toReal_nonneg) hd1 h0 h1).2 hle

/-- Helper (S3) for §7.4. The distance is approximated by representatives. -/
theorem gl7_teichDist_approx {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p q : TeichGamma Γ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ μ ν : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) μ = p ∧ Quotient.mk (teichSetoidGamma Γ) ν = q ∧
      (1 / 2) * Real.log ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1) /
        (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1)) < teichDistanceGamma p q + ε := by
  obtain ⟨h0, h1, happ⟩ := LiZhongQC.bg_d_teichDelta_spec p q
  set δ₀ := LiZhongQC.teichDeltaGamma p q with hδ₀
  set L : ℝ → ℝ := fun x => (1 / 2) * Real.log ((1 + x) / (1 - x)) with hLdef
  have hq : ContinuousAt (fun x : ℝ => (1 + x) / (1 - x)) δ₀ :=
    (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) (by linarith)
  have hpos : (1 + δ₀) / (1 - δ₀) ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  have hc : ContinuousAt L δ₀ :=
    continuousAt_const.mul (ContinuousAt.comp (g := Real.log) (Real.continuousAt_log hpos) hq)
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1 hc ε hε
  set b := min (δ₀ + η / 2) ((1 + δ₀) / 2) with hb
  have hδb : δ₀ < b := lt_min (by linarith) (by linarith)
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨μ, ν, hμ, hν, hlt⟩ := happ b hδb
  refine ⟨μ, ν, hμ, hν, ?_⟩
  have hLb : L b < L δ₀ + ε := by
    have h := hη' (show dist b δ₀ < η by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_left (δ₀ + η / 2) ((1 + δ₀) / 2)])
    rw [Real.dist_eq] at h
    linarith [le_abs_self (L b - L δ₀)]
  have hmono := (l21b_halfLog_mono (r := b) (r' := LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1)
    (by linarith) hb1 ENNReal.toReal_nonneg (hlt.trans hb1)).2 hlt.le
  calc _ ≤ L b := hmono
    _ < L δ₀ + ε := hLb
    _ = teichDistanceGamma p q + ε := rfl

/-- Helper (S4) for §7.4. `d(p, p) = 0` and `d(p, q) = d(q, p)` on `T(G)`. -/
theorem gl7_teichDist_self_symm {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p q : TeichGamma Γ) :
    teichDistanceGamma p p = 0 ∧ teichDistanceGamma p q = teichDistanceGamma q p := by
  have hδ : ∀ p q : TeichGamma Γ, LiZhongQC.teichDeltaGamma p q = LiZhongQC.teichDeltaGamma q p := by
    intro p q
    show sInf _ = sInf _
    congr 1
    ext d
    constructor
    · rintro ⟨μ, ν, hμ, hν, rfl⟩
      exact ⟨ν, μ, hν, hμ, LiZhongQC.UniversalTeichmuller.ut_d_symm _ _⟩
    · rintro ⟨μ, ν, hμ, hν, rfl⟩
      exact ⟨ν, μ, hν, hμ, LiZhongQC.UniversalTeichmuller.ut_d_symm _ _⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, rfl⟩ := Quotient.exists_rep p
    have h1 := gl7_teichDist_le μ μ
    rw [LiZhongQC.UniversalTeichmuller.ut_d_self] at h1
    have h2 : 0 ≤ teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) μ) := by
      obtain ⟨h0, h1', -⟩ := LiZhongQC.bg_d_teichDelta_spec (Quotient.mk (teichSetoidGamma Γ) μ)
        (Quotient.mk (teichSetoidGamma Γ) μ)
      have := (l21b_halfLog_mono (r := LiZhongQC.teichDeltaGamma (Quotient.mk (teichSetoidGamma Γ) μ)
        (Quotient.mk (teichSetoidGamma Γ) μ)) (r' := 0) h0 h1' le_rfl (by norm_num)).2 h0
      have hz : (1 / 2 : ℝ) * Real.log ((1 + 0) / (1 - 0)) = 0 := by norm_num
      rw [hz] at this
      exact this
    norm_num at h1
    linarith
  · show (1 / 2) * Real.log ((1 + LiZhongQC.teichDeltaGamma p q) / (1 - LiZhongQC.teichDeltaGamma p q)) =
      (1 / 2) * Real.log ((1 + LiZhongQC.teichDeltaGamma q p) / (1 - LiZhongQC.teichDeltaGamma q p))
    rw [hδ p q]

/-- Helper (S5) for §7.4. The triangle inequality for the Teichmüller distance on `T(G)` (S1 with the universal
composition estimate `ut_v_triangle`, as in `UniversalTeichmuller.dist_triangle`). -/
theorem gl7_teichDist_triangle {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p q r : TeichGamma Γ) :
    teichDistanceGamma p r ≤ teichDistanceGamma p q + teichDistanceGamma q r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨μ, ν, hμ, hν, h1⟩ := gl7_teichDist_approx p q (half_pos hε)
  obtain ⟨ν', ρ, hν', hρ, h2⟩ := gl7_teichDist_approx q r (half_pos hε)
  have hνν' : teichSetoidGamma Γ ν' ν := Quotient.exact (hν'.trans hν.symm)
  obtain ⟨ρ'', hρρ, hδρ⟩ := gl7_transport hνν' ρ
  have hρ'' : Quotient.mk (teichSetoidGamma Γ) ρ'' = r := (Quotient.sound hρρ).trans hρ
  have hv : ∀ a b : BeltramiGamma Γ, (1 / 2) * Real.log
      ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm a.1.1 b.1.1) /
        (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm a.1.1 b.1.1)) = (1 / 2) * LiZhongQC.ut_v a.1 b.1 :=
    fun a b => by rw [(LiZhongQC.UniversalTeichmuller.ut_v_eq a.1 b.1).2]
  have htri := LiZhongQC.UniversalTeichmuller.ut_v_triangle μ.1 ν.1 ρ''.1
  have e1 := gl7_teichDist_le μ ρ''
  rw [hμ, hρ'', hv] at e1
  rw [hv] at h1 h2
  have hδρ' : LiZhongQC.ut_v ν.1 ρ''.1 = LiZhongQC.ut_v ν'.1 ρ.1 := by
    rw [(LiZhongQC.UniversalTeichmuller.ut_v_eq ν.1 ρ''.1).2, (LiZhongQC.UniversalTeichmuller.ut_v_eq ν'.1 ρ.1).2,
      hδρ]
  linarith

/-- Helper (S6) for §7.4. For an extremal `μ`, `d([0], [μ]) = ½ log((1 + ‖μ‖∞)/(1 − ‖μ‖∞)) = tanh⁻¹ ‖μ‖∞`:
`≤` from the representatives `0`, `μ`; `≥` since any pair `π' ∼ 0`, `μ' ∼ μ` gives `μ'' ∼ μ` with
`‖μ''‖∞ ≤ tanh τ(μ', π') ≤ ‖(μ' − π')/(1 − π̄'μ')‖∞` (`h36p_translate`) and `‖μ‖∞ ≤ ‖μ''‖∞` (extremality). -/
theorem gl7_teichDist_origin {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) :
    teichDistanceGamma (LiZhongQC.TeichGamma.origin Γ) (Quotient.mk (teichSetoidGamma Γ) μ) =
      (1 / 2) * Real.log ((1 + beltramiNormH μ.1.1) / (1 - beltramiNormH μ.1.1)) := by
  obtain ⟨z0, hz0, hz0v⟩ : ∃ z0 : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) z0 =
      LiZhongQC.TeichGamma.origin Γ ∧ z0.1.1 = 0 := ⟨_, rfl, rfl⟩
  have hk0 := LiZhongQC.beltramiNormH_nonneg μ.1.1
  have hk1 := LiZhongQC.beltramiNormH_lt_one μ.1
  have hδ0 : LiZhongQC.UniversalTeichmuller.dilatationDiffNorm z0.1.1 μ.1.1 = beltramiNormH μ.1.1 := by
    show (essSup (fun z => (‖(z0.1.1 z - μ.1.1 z) / (1 - conj (μ.1.1 z) * z0.1.1 z)‖₊ : ℝ≥0∞))
      (volume.restrict upperHalf)).toReal = (essSup (fun z => (‖μ.1.1 z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)).toReal
    rw [hz0v]
    simp only [Pi.zero_apply, zero_sub, mul_zero, sub_zero, div_one, nnnorm_neg]
  -- the key estimate: every pair of representatives of `[0]`, `[μ]` has `‖μ‖∞ ≤ ‖(μ' − π')/(1 − π̄'μ')‖∞`
  have key : ∀ π' μ' : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) π' = LiZhongQC.TeichGamma.origin Γ →
      Quotient.mk (teichSetoidGamma Γ) μ' = Quotient.mk (teichSetoidGamma Γ) μ →
      beltramiNormH μ.1.1 ≤ LiZhongQC.UniversalTeichmuller.dilatationDiffNorm π'.1.1 μ'.1.1 := by
    intro π' μ' hπ' hμ'
    have htriv : LiZhongQC.IsTrivialBeltrami Γ π' := fun x => by
      have h := (LiZhongQC.lemma33_1 π'.1 z0.1).1 (Quotient.exact (hπ'.trans hz0.symm)) x
      rw [h]
      show LiZhongQC.normalizedSolution z0.1.1 x = x
      rw [hz0v, LiZhongQC.bB_l_normalizedSolution_zero]
      rfl
    obtain ⟨μ'', hμ''c, hμ''n⟩ := LiZhongQC.h36p_translate μ' π' htriv
    have hext := hμ μ'' ((teichSetoidGamma Γ).iseqv.trans hμ''c (Quotient.exact hμ'))
    -- `tanh τ(μ', π') ≤ ‖(π' − μ')/(1 − μ̄'π')‖∞`
    set ρ : ℂ → ℝ := fun z => ‖(μ'.1.1 z - π'.1.1 z) / (1 - conj (μ'.1.1 z) * π'.1.1 z)‖ with hρdef
    obtain ⟨k₁, hk₁0, hk₁1, hb₁⟩ := LiZhongQC.beltramiH_ae_bound μ'.1
    obtain ⟨k₂, hk₂0, hk₂1, hb₂⟩ := LiZhongQC.beltramiH_ae_bound π'.1
    have hkm0 : 0 ≤ max k₁ k₂ := le_max_of_le_left hk₁0
    have hkm1 : max k₁ k₂ < 1 := max_lt hk₁1 hk₂1
    have hc1 : 2 * max k₁ k₂ / (1 + max k₁ k₂ ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [sq_nonneg (1 - max k₁ k₂)]
    have hρc : ∀ᵐ z ∂(volume.restrict upperHalf), ρ z ≤ 2 * max k₁ k₂ / (1 + max k₁ k₂ ^ 2) := by
      filter_upwards [hb₁, hb₂] with z h1 h2
      show ‖(μ'.1.1 z - π'.1.1 z) / (1 - conj (μ'.1.1 z) * π'.1.1 z)‖ ≤ _
      rw [LiZhongQC.c36_b_norm_conj_denom]
      exact LiZhongQC.ahQ_pseudo_bound hkm0 hkm1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
    set E : ℝ≥0∞ := essSup (fun z => ENNReal.ofReal (ρ z)) (volume.restrict upperHalf) with hE
    have hEc : E ≤ ENNReal.ofReal (2 * max k₁ k₂ / (1 + max k₁ k₂ ^ 2)) :=
      essSup_le_of_ae_le _ (by filter_upwards [hρc] with z hz using ENNReal.ofReal_le_ofReal hz)
    have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEc
    have hx1 : E.toReal < 1 :=
      lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) hEc) hc1
    have hx0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
    have hδE : LiZhongQC.UniversalTeichmuller.dilatationDiffNorm π'.1.1 μ'.1.1 = E.toReal := by
      show (essSup (fun z => (‖(π'.1.1 z - μ'.1.1 z) / (1 - conj (μ'.1.1 z) * π'.1.1 z)‖₊ : ℝ≥0∞))
        (volume.restrict upperHalf)).toReal = _
      congr 1
      congr 1
      funext z
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
      show ENNReal.ofReal ‖(π'.1.1 z - μ'.1.1 z) / (1 - conj (μ'.1.1 z) * π'.1.1 z)‖ =
        ENNReal.ofReal ‖(μ'.1.1 z - π'.1.1 z) / (1 - conj (μ'.1.1 z) * π'.1.1 z)‖
      rw [norm_div, norm_div, norm_sub_rev]
    have hρE : ∀ᵐ z ∂(volume.restrict upperHalf), ρ z ≤ E.toReal := by
      filter_upwards [ENNReal.ae_le_essSup (fun z => ENNReal.ofReal (ρ z))] with z hz
      have h := ENNReal.toReal_mono hEtop hz
      rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h
    have hart0 : 0 ≤ Real.artanh E.toReal := by
      have h := Real.artanh_le_artanh (x := 0) (y := E.toReal) (by norm_num) hx1 hx0
      rwa [Real.artanh_zero] at h
    have hτ : LiZhongQC.beltramiPoincareDist μ'.1.1 π'.1.1 ≤ Real.artanh E.toReal := by
      refine ENNReal.toReal_le_of_le_ofReal hart0 (essSup_le_of_ae_le _ ?_)
      filter_upwards [hρE, hρc] with z h1 h2
      refine ENNReal.ofReal_le_ofReal ?_
      have hρ1 : ρ z < 1 := h2.trans_lt hc1
      show (1 / 2) * Real.log ((1 + ρ z) / (1 - ρ z)) ≤ _
      rw [← Real.artanh_eq_half_log ⟨le_trans (by norm_num) (norm_nonneg _), hρ1.le⟩]
      exact Real.artanh_le_artanh (lt_of_lt_of_le (by norm_num) (norm_nonneg _)) hx1 h1
    have htanh : Real.tanh (LiZhongQC.beltramiPoincareDist μ'.1.1 π'.1.1) ≤ E.toReal := by
      have h := LiZhongQC.h36t_tanh_le_tanh hτ
      rwa [Real.tanh_artanh ⟨by linarith, hx1⟩] at h
    rw [hδE]
    linarith
  apply le_antisymm
  · rw [← hz0]
    exact (gl7_teichDist_le z0 μ).trans_eq (by rw [hδ0])
  · obtain ⟨h0, h1, -⟩ := LiZhongQC.bg_d_teichDelta_spec (LiZhongQC.TeichGamma.origin Γ)
      (Quotient.mk (teichSetoidGamma Γ) μ)
    have hkey : beltramiNormH μ.1.1 ≤ LiZhongQC.teichDeltaGamma (LiZhongQC.TeichGamma.origin Γ)
        (Quotient.mk (teichSetoidGamma Γ) μ) := by
      refine le_csInf ⟨_, z0, μ, hz0, rfl, rfl⟩ ?_
      rintro d ⟨π', μ', hπ', hμ', rfl⟩
      exact key π' μ' hπ' hμ'
    exact (l21b_halfLog_mono h0 h1 hk0 hk1).2 hkey

/-- Helper (S7) for §7.4. Along the ray `s ↦ [sμ]` of an extremal `μ`, `k = ‖μ‖∞`, for `0 ≤ s ≤ t ≤ 1`:
`d([sμ], [tμ]) = L(tk) − L(sk)`, `L(x) = ½ log((1 + x)/(1 − x))`: `≤` pointwise
(`|(tμ − sμ)/(1 − st|μ|²)| ≤ ((t − s)k)/(1 − stk²)` and `L(tk) − L(sk) = L((tk − sk)/(1 − stk²))`), `≥` from S5, S6
and `≤` for the pairs `(0, s)` and `(t, 1)`. -/
theorem gl7_teichDist_scale {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) ⟨LiZhongQC.ut_scale μ.1 s, LiZhongQC.bg_p_scale_compat μ s⟩)
        (Quotient.mk (teichSetoidGamma Γ) ⟨LiZhongQC.ut_scale μ.1 t, LiZhongQC.bg_p_scale_compat μ t⟩) =
      (1 / 2) * Real.log ((1 + t * beltramiNormH μ.1.1) / (1 - t * beltramiNormH μ.1.1)) -
        (1 / 2) * Real.log ((1 + s * beltramiNormH μ.1.1) / (1 - s * beltramiNormH μ.1.1)) := by
  set k : ℝ := beltramiNormH μ.1.1 with hkdef
  have hk0 : 0 ≤ k := LiZhongQC.beltramiNormH_nonneg _
  have hk1 : k < 1 := LiZhongQC.beltramiNormH_lt_one μ.1
  set A : ℝ → BeltramiGamma Γ := fun s => ⟨LiZhongQC.ut_scale μ.1 s, LiZhongQC.bg_p_scale_compat μ s⟩ with hAdef
  set L : ℝ → ℝ := fun x => (1 / 2) * Real.log ((1 + x) / (1 - x)) with hLdef
  have hAval : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ z, (A s).1.1 z = (s : ℂ) * μ.1.1 z := by
    intro s hs0 hs1 z
    simp only [hAdef, LiZhongQC.ut_scale]
    rw [min_eq_right hs1, max_eq_right hs0]
  have hμk : ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ.1.1 z‖ ≤ k :=
    LiZhongQC.ae_norm_le_beltramiNormH (LiZhongQC.beltramiH_essSup_ne_top μ.1)
  -- the upper bound along the ray
  have hup : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) (A s)) (Quotient.mk (teichSetoidGamma Γ) (A t)) ≤
        L (t * k) - L (s * k) := by
    intro s t hs hst ht
    have hs1 : s ≤ 1 := hst.trans ht
    have ht0 : 0 ≤ t := hs.trans hst
    have hsk0 : 0 ≤ s * k := mul_nonneg hs hk0
    have htk0 : 0 ≤ t * k := mul_nonneg ht0 hk0
    have htk1 : t * k < 1 := by nlinarith [mul_le_mul_of_nonneg_right ht hk0]
    have hsk1 : s * k < 1 := by nlinarith [mul_le_mul_of_nonneg_right hs1 hk0]
    have hst1 : s * t ≤ 1 := by nlinarith [mul_le_mul hs1 ht ht0 zero_le_one]
    have hstk : s * t * k ^ 2 ≤ k ^ 2 := by nlinarith [sq_nonneg k, mul_nonneg hs ht0]
    have hden0 : 0 < 1 - s * t * k ^ 2 := by nlinarith
    set u : ℝ := (t - s) * k / (1 - s * t * k ^ 2) with hu
    have hu0 : 0 ≤ u := div_nonneg (mul_nonneg (by linarith) hk0) hden0.le
    have hq : 0 < (1 - t * k) * (1 + s * k) := mul_pos (by linarith) (by linarith)
    have hu1 : u < 1 := by
      rw [hu, div_lt_one hden0]
      nlinarith
    -- `δ(A s, A t) ≤ u`
    have hδu : LiZhongQC.UniversalTeichmuller.dilatationDiffNorm (A s).1.1 (A t).1.1 ≤ u := by
      refine ENNReal.toReal_le_of_le_ofReal hu0 (essSup_le_of_ae_le _ ?_)
      filter_upwards [hμk] with z hz
      rw [hAval s hs hs1 z, hAval t ht0 ht z, ← enorm_eq_nnnorm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      set m := μ.1.1 z with hm
      have hdenz : 1 - conj ((t : ℂ) * m) * ((s : ℂ) * m) = ((1 - t * s * ‖m‖ ^ 2 : ℝ) : ℂ) := by
        have hc := Complex.conj_mul' m
        rw [map_mul, Complex.conj_ofReal]
        push_cast
        rw [← hc]
        ring
      have hnum : (s : ℂ) * m - (t : ℂ) * m = ((s - t : ℝ) : ℂ) * m := by push_cast; ring
      have hmk2 : t * s * ‖m‖ ^ 2 ≤ t * s * k ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (mul_nonneg ht0 hs)
      have hpos : 0 < 1 - t * s * ‖m‖ ^ 2 := by nlinarith
      rw [hdenz, hnum, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg hpos.le, abs_of_nonpos (show s - t ≤ 0 by linarith), hu, div_le_div_iff₀ hpos hden0]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hst) (sub_nonneg.2 hz))
        (add_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg hs ht0) (norm_nonneg m)) hk0))]
    have hd := gl7_teichDist_le (A s) (A t)
    obtain ⟨hδ1, -⟩ := LiZhongQC.UniversalTeichmuller.ut_v_eq (A s).1 (A t).1
    have hmono := (l21b_halfLog_mono hu0 hu1 ENNReal.toReal_nonneg hδ1).2 hδu
    -- `L(u) = L(tk) − L(sk)`
    have hLu : L u = L (t * k) - L (s * k) := by
      have ha : 0 < (1 + t * k) / (1 - t * k) := div_pos (by linarith) (by linarith)
      have hb : 0 < (1 + s * k) / (1 - s * k) := div_pos (by linarith) (by linarith)
      have e : (1 + u) / (1 - u) = (1 + t * k) / (1 - t * k) / ((1 + s * k) / (1 - s * k)) := by
        have h5 : 1 - s * t * k ^ 2 ≠ 0 := hden0.ne'
        have eL : (1 + u) / (1 - u) = ((1 + t * k) * (1 - s * k)) / ((1 - t * k) * (1 + s * k)) := by
          rw [hu, one_add_div h5, one_sub_div h5, div_div_div_cancel_right₀ h5]
          congr 1 <;> ring
        rw [eL, div_div_div_eq]
      show (1 / 2) * Real.log ((1 + u) / (1 - u)) =
        (1 / 2) * Real.log ((1 + t * k) / (1 - t * k)) - (1 / 2) * Real.log ((1 + s * k) / (1 - s * k))
      rw [e, Real.log_div ha.ne' hb.ne']
      ring
    calc _ ≤ L (LiZhongQC.UniversalTeichmuller.dilatationDiffNorm (A s).1.1 (A t).1.1) := hd
      _ ≤ L u := hmono
      _ = L (t * k) - L (s * k) := hLu
  -- the end points of the ray
  have hA0 : Quotient.mk (teichSetoidGamma Γ) (A 0) = LiZhongQC.TeichGamma.origin Γ := by
    refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
    funext z
    simp [hAdef, LiZhongQC.ut_scale]
  have hA1 : Quotient.mk (teichSetoidGamma Γ) (A 1) = Quotient.mk (teichSetoidGamma Γ) μ := by
    refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
    funext z
    simp [hAdef, LiZhongQC.ut_scale]
  have hL0 : L (0 * k) = 0 := by simp [hLdef]
  -- the lower bound from S5 and S6
  have h6 : teichDistanceGamma (LiZhongQC.TeichGamma.origin Γ) (Quotient.mk (teichSetoidGamma Γ) μ) = L k :=
    gl7_teichDist_origin μ hμ
  have h5a := gl7_teichDist_triangle (LiZhongQC.TeichGamma.origin Γ) (Quotient.mk (teichSetoidGamma Γ) (A s))
    (Quotient.mk (teichSetoidGamma Γ) μ)
  have h5b := gl7_teichDist_triangle (Quotient.mk (teichSetoidGamma Γ) (A s))
    (Quotient.mk (teichSetoidGamma Γ) (A t)) (Quotient.mk (teichSetoidGamma Γ) μ)
  have hu1 := hup 0 s le_rfl hs (hst.trans ht)
  have hu2 := hup t 1 (hs.trans hst) ht le_rfl
  rw [hA0, hL0] at hu1
  rw [hA1, one_mul] at hu2
  have hmain := hup s t hs hst ht
  refine le_antisymm hmain ?_
  show L (t * k) - L (s * k) ≤
    teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) (A s)) (Quotient.mk (teichSetoidGamma Γ) (A t))
  linarith

/-- **Unlabelled** (§7.4, l. 6394–6402). If `μ ≠ 0` is extremal in its class, `f(t) = [t μ/‖μ‖∞]`,
`t ∈ [0, ‖μ‖∞]`, is a geodesic segment joining the basepoint to `[μ]`. Modelling: `f(t)` is the class of any `ν ∈
M(G)` with `ν = (t/‖μ‖∞) μ`. -/
theorem para7_4_geodesic_exists {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (μ : BeltramiGamma Γ) (hμ : IsExtremalModBoundary Γ μ) (hμ0 : beltramiNormH μ.1.1 ≠ 0) :
    ∃ f : ℝ → TeichGamma Γ, IsGeodesicSegment teichDistanceGamma f 0 (beltramiNormH μ.1.1) ∧
      f 0 = LiZhongQC.TeichGamma.origin Γ ∧ f (beltramiNormH μ.1.1) = Quotient.mk (teichSetoidGamma Γ) μ ∧
      ∀ t ∈ Icc 0 (beltramiNormH μ.1.1), ∀ ν : BeltramiGamma Γ,
        (ν.1.1 = fun z => ((t / beltramiNormH μ.1.1 : ℝ) : ℂ) * μ.1.1 z) →
          f t = Quotient.mk (teichSetoidGamma Γ) ν := by
  -- `hΓ` is not needed: the distance identities hold for every subgroup
  have _hΓ := hΓ
  set k : ℝ := beltramiNormH μ.1.1 with hkdef
  have hk0 : 0 < k := lt_of_le_of_ne (LiZhongQC.beltramiNormH_nonneg _) (Ne.symm hμ0)
  have hk1 : k < 1 := LiZhongQC.beltramiNormH_lt_one μ.1
  set g : ℝ → BeltramiGamma Γ := fun t =>
    ⟨LiZhongQC.ut_scale μ.1 (t / k), LiZhongQC.bg_p_scale_compat μ (t / k)⟩ with hgdef
  set L : ℝ → ℝ := fun x => (1 / 2) * Real.log ((1 + x) / (1 - x)) with hLdef
  -- the distance along the ray
  have hd : ∀ s t, 0 ≤ s → s ≤ t → t ≤ k →
      teichDistanceGamma (Quotient.mk _ (g s)) (Quotient.mk _ (g t)) = L t - L s := by
    intro s t hs hst ht
    have h := gl7_teichDist_scale μ hμ (div_nonneg hs hk0.le) (div_le_div_of_nonneg_right hst hk0.le)
      ((div_le_one hk0).2 ht)
    rwa [div_mul_cancel₀ _ hk0.ne', div_mul_cancel₀ _ hk0.ne'] at h
  have hLlt : ∀ x y : ℝ, 0 ≤ x → x < y → y < 1 → L x < L y := by
    intro x y hx hxy hy
    have h1 : (1 + x) / (1 - x) < (1 + y) / (1 - y) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have h2 : 0 < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
    show (1 / 2) * Real.log ((1 + x) / (1 - x)) < (1 / 2) * Real.log ((1 + y) / (1 - y))
    linarith [Real.log_lt_log h2 h1]
  have hdabs : ∀ s ∈ Icc 0 k, ∀ t ∈ Icc 0 k,
      teichDistanceGamma (Quotient.mk _ (g s)) (Quotient.mk _ (g t)) = |L t - L s| := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [hd s t hs.1 hst ht.2, abs_of_nonneg]
      rcases hst.lt_or_eq with h | h
      · exact (sub_pos.2 (hLlt s t hs.1 h (lt_of_le_of_lt ht.2 hk1))).le
      · rw [h, sub_self]
    · have hsym := (gl7_teichDist_self_symm (Quotient.mk (teichSetoidGamma Γ) (g s))
        (Quotient.mk (teichSetoidGamma Γ) (g t))).2
      rw [hsym, hd t s ht.1 hts hs.2, abs_of_nonpos]
      · ring
      · rcases hts.lt_or_eq with h | h
        · exact (sub_neg.2 (hLlt t s ht.1 h (lt_of_le_of_lt hs.2 hk1))).le
        · rw [h, sub_self]
  refine ⟨fun t => Quotient.mk _ (g t), ⟨hk0, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- injective: distinct parameters have positive distance
    intro s hs t ht hst
    by_contra hne
    have h0 := hdabs s hs t ht
    simp only at hst
    have hself := (gl7_teichDist_self_symm (Quotient.mk (teichSetoidGamma Γ) (g t))
      (Quotient.mk (teichSetoidGamma Γ) (g t))).1
    rw [hst, hself] at h0
    rcases lt_or_gt_of_ne hne with h | h
    · have := hLlt s t hs.1 h (lt_of_le_of_lt ht.2 hk1)
      rw [abs_of_pos (sub_pos.2 this)] at h0
      linarith
    · have := hLlt t s ht.1 h (lt_of_le_of_lt hs.2 hk1)
      rw [abs_of_neg (sub_neg.2 this)] at h0
      linarith
  · -- continuous: `L` is continuous on `[0, k]`
    intro s hs ε hε
    have hs1 : 0 < 1 - s := by linarith [hs.2]
    have hq : ContinuousAt (fun x : ℝ => (1 + x) / (1 - x)) s :=
      (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) hs1.ne'
    have hpos : (1 + s) / (1 - s) ≠ 0 := (div_pos (by linarith [hs.1]) hs1).ne'
    have hlog : ContinuousAt (fun x : ℝ => Real.log ((1 + x) / (1 - x))) s :=
      ContinuousAt.comp (g := Real.log) (Real.continuousAt_log hpos) hq
    have hc : ContinuousAt L s := continuousAt_const.mul hlog
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hc ε hε
    refine ⟨δ, hδ, fun t ht hts => ?_⟩
    show teichDistanceGamma (Quotient.mk _ (g s)) (Quotient.mk _ (g t)) < ε
    rw [hdabs s hs t ht, ← Real.dist_eq]
    exact hδ' (by rwa [Real.dist_eq])
  · -- additive along the segment
    intro x z y hx hxz hzy hy
    show teichDistanceGamma (Quotient.mk _ (g x)) (Quotient.mk _ (g y)) =
      teichDistanceGamma (Quotient.mk _ (g x)) (Quotient.mk _ (g z)) +
        teichDistanceGamma (Quotient.mk _ (g z)) (Quotient.mk _ (g y))
    rw [hd x y hx (hxz.trans hzy) hy, hd x z hx hxz (hzy.trans hy), hd z y (hx.trans hxz) hzy hy]
    ring
  · -- `f(0) = [0]`
    refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
    funext z
    simp [hgdef, LiZhongQC.ut_scale]
  · -- `f(‖μ‖∞) = [μ]`
    refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
    funext z
    simp [hgdef, LiZhongQC.ut_scale, div_self hk0.ne']
  · -- `f(t) = [(t/‖μ‖∞) μ]`
    intro t ht ν hν
    refine congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ?_))
    rw [hν]
    funext z
    simp only [hgdef, LiZhongQC.ut_scale]
    rw [min_eq_right ((div_le_one hk0).2 ht.2), max_eq_right (div_nonneg ht.1 hk0.le)]

/-- **Definition** (§7.4, l. 6402). `μ` is uniquely extremal: it is extremal and it is the only extremal
representative of its class (up to null sets). -/
def IsUniquelyExtremal (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ : BeltramiGamma Γ) : Prop :=
  IsExtremalModBoundary Γ μ ∧ ∀ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν μ → IsExtremalModBoundary Γ ν →
    ν.1.1 =ᵐ[volume.restrict upperHalf] μ.1.1

/-- **Definition** (§7.4, l. 6403). A holomorphic isometry `f : Δ → T(G)`: holomorphic, with
`d(f(s), f(t)) = σ_Δ(s, t)` for `s, t ∈ Δ`. -/
def IsHolIsometry (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (f : ℂ → TeichGamma Γ) : Prop :=
  f ∈ holDiscsT Γ ∧ ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, teichDistanceGamma (f s) (f t) = discPoincareDist s t

/-- **Definition** (Teichmüller disc, §7.4, l. 6403). The image `{[t |φ|/φ] : t ∈ Δ}` of the holomorphic isometry
(7.16) with `μ = k|φ|/φ`, `φ ∈ A(G)` of norm 1 (over a fundamental domain `F`). -/
def teichmullerDisc (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) : Set (TeichGamma Γ) :=
  {p | ∃ t ∈ unitDisc, ∃ ν : BeltramiGamma Γ,
    (∀ z ∈ upperHalf, ν.1.1 z = t * (conj (φ z) / ‖φ z‖)) ∧ p = Quotient.mk (teichSetoidGamma Γ) ν}

/-- **Theorem 3** (§7.4, l. 6405). Suppose `μ` is extremal and nonzero. The following are equivalent:
(a) `μ` is uniquely extremal and `|μ| = ‖μ‖∞` a.e.;
(b) there is only one geodesic segment joining the basepoint and `[μ]`;
(c) there is only one holomorphic isometry `f : Δ → T(R)` with `f(0) = [0]` and `f(‖μ‖∞) = [μ]`;
(d) there is only one holomorphic map `g : Δ → M(R)` with `g(0) = 0` and `[g(‖μ‖∞)] = [μ]`.
Modelling: "only one" is existence and uniqueness (segments: same image; maps: equal on `Δ`, coefficients a.e.). -/
theorem thm7_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ)
    (hμ : IsExtremalModBoundary Γ μ) (hμ0 : beltramiNormH μ.1.1 ≠ 0) :
    List.TFAE [IsUniquelyExtremal Γ μ ∧ ∀ᵐ z ∂(volume.restrict upperHalf), ‖μ.1.1 z‖ = beltramiNormH μ.1.1,
      ∀ (f g : ℝ → TeichGamma Γ) (a b a' b' : ℝ), IsGeodesicSegment teichDistanceGamma f a b →
        IsGeodesicSegment teichDistanceGamma g a' b' → f a = LiZhongQC.TeichGamma.origin Γ →
        f b = Quotient.mk (teichSetoidGamma Γ) μ → g a' = LiZhongQC.TeichGamma.origin Γ →
        g b' = Quotient.mk (teichSetoidGamma Γ) μ →
        f '' Icc a b = g '' Icc a' b',
      (∃ f, IsHolIsometry Γ f ∧ f 0 = LiZhongQC.TeichGamma.origin Γ ∧
          f (beltramiNormH μ.1.1) = Quotient.mk (teichSetoidGamma Γ) μ) ∧
        ∀ f₁ f₂, IsHolIsometry Γ f₁ → IsHolIsometry Γ f₂ → f₁ 0 = f₂ 0 →
          f₁ 0 = LiZhongQC.TeichGamma.origin Γ → f₁ (beltramiNormH μ.1.1) = Quotient.mk (teichSetoidGamma Γ) μ →
          f₂ (beltramiNormH μ.1.1) = Quotient.mk (teichSetoidGamma Γ) μ → ∀ t ∈ unitDisc, f₁ t = f₂ t,
      (∃ g ∈ holDiscsM Γ, (∀ z, (g 0).1.1 z = 0) ∧
          Quotient.mk (teichSetoidGamma Γ) (g (beltramiNormH μ.1.1)) = Quotient.mk (teichSetoidGamma Γ) μ) ∧
        ∀ g₁ ∈ holDiscsM Γ, ∀ g₂ ∈ holDiscsM Γ, (∀ z, (g₁ 0).1.1 z = 0) → (∀ z, (g₂ 0).1.1 z = 0) →
          Quotient.mk (teichSetoidGamma Γ) (g₁ (beltramiNormH μ.1.1)) = Quotient.mk (teichSetoidGamma Γ) μ →
          Quotient.mk (teichSetoidGamma Γ) (g₂ (beltramiNormH μ.1.1)) = Quotient.mk (teichSetoidGamma Γ) μ →
          ∀ t ∈ unitDisc, (g₁ t).1.1 =ᵐ[volume.restrict upperHalf] (g₂ t).1.1] := by
  sorry

end GardinerLakic2000
