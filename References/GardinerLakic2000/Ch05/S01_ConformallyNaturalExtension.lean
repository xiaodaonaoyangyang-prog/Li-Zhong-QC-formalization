import References.GardinerLakic2000.Ch04.S12_InfinitesimalMetric
import References.Pommerenke1992.Ch05.S05_QuasiconformalExtension

/-!
# Gardiner–Lakic 2000, Ch. 5 §5.1 Conformally natural extension

Chapter 5 *Teichmüller equivalence*, §5.1 (and the chapter introduction, l. 4666–4678, no items); source
`teichmuller.txt`, lines 4679–5010.

* Theorem 1 (Douady–Earle, l. 4698), the extension and its quasiconformality — exists:
  `Pommerenke1992.thm5_15` `Pommerenke1992.thm5_15_ii` (a homeomorphism of the closed disc, real-analytic, with
  |∂̄| ≤ κ|∂|, κ < 1, for quasisymmetric boundary values)
* Theorem 1 (i) (conformal naturality) — exists: `Pommerenke1992.thm5_15` (last conjunct, σ ∘ φ ∘ τ with
  σ, τ ∈ Möb(𝔻) written out)
* Theorem 1 (ii) (`DE(id) = id`) — `thm5_1_ii`
* Theorem 1 (iii) (mean value zero implies `DE(h)(0) = 0`) — exists: `Pommerenke1992.eq5_5_2` [misprint: the book
  prints ∫_{|z|=1} h(z) dz, also GL8:4572; the mean value ∫ h |dz| is meant (Exercise 9, l. 5250, GL8:5130)]
* Definition (the vector field `V_m` of a probability measure, (5.3)–(5.4), l. 4708–4732) — `vectorFieldVm`
* Definition (conformal barycenter, l. 4736) — `conformalBarycenter`
* Lemma 1 (a measure without atoms has a unique zero of `V_m`, l. 4738) — `lemma5_1`
* Definition 1 (the Douady–Earle extension, (5.6), l. 4781) — exists: `Pommerenke1992.douadyEarleExt` (the book's
  F_{h,z} is −(1 − |w|²) times `Pommerenke1992.douadyEarleF`, which has the same zeros in Δ)
* Theorem 2 (the dilatation of `DE(h)` depends only on `K`, l. 5009; cited l. 10302) — `thm5_2`

Not items (DESIGN §3): the automorphy conditions (5.1), (5.2) (l. 4684–4692, not cited), `|V_m(0)| ≤ 1` (l. 4722),
`α(h)`, `β(h)` and the other steps of the proof, the remark after it (l. 5007, restated as Theorem 2).

**Conventions.** Quasisymmetric circle maps are `Pommerenke1992.IsQuasisymmetric` together with
`Pommerenke1992.IsSensePreservingCircleHomeo` (B0.6); the Douady–Earle extension is `Pommerenke1992.douadyEarleExt`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

/-- **Definition** ((5.3)–(5.4), §5.1, l. 4708–4732). For a probability measure `m` on `∂Δ` (a measure on `ℂ`
carried by the unit circle), the conformally natural vector field
`V_m(w) = (1 − |w|²) ∫_{∂Δ} (t − w)/(1 − w̄ t) dm(t)` on `Δ`. -/
def vectorFieldVm (m : Measure ℂ) (w : ℂ) : ℂ :=
  ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * ∫ t, (t - w) / (1 - conj w * t) ∂m

/-- **Definition** (conformal barycenter, §5.1, l. 4736). The zero of `V_m` in `Δ` (unique when `m` has no atoms,
Lemma 1). Junk value (some point of `Δ`, by choice) when there is no zero. -/
def conformalBarycenter (m : Measure ℂ) : ℂ :=
  Classical.epsilon fun w : ℂ => w ∈ LiZhongQC.unitDisc ∧ vectorFieldVm m w = 0

/-- **Lemma 1** (§5.1, l. 4738). If the probability measure `m` on `∂Δ` has no atoms, then `V_m` has a unique zero
in `Δ`. -/
theorem lemma5_1 (m : Measure ℂ) [IsProbabilityMeasure m] (hna : ∀ t : ℂ, m {t} = 0) (hm : m (sphere 0 1)ᶜ = 0) :
    ∃! w : ℂ, w ∈ LiZhongQC.unitDisc ∧ vectorFieldVm m w = 0 := by
  sorry

/-- **Theorem 1 (ii)** (Douady–Earle, §5.1, l. 4705). The extension of the identity of `∂Δ` is the identity of
`Δ` (of the closed disc). -/
theorem thm5_1_ii : EqOn (Pommerenke1992.douadyEarleExt fun z => z) (fun z => z) (closedBall 0 1) := by
  classical
  intro z _
  by_cases hzΔ : z ∈ LiZhongQC.unitDisc
  · -- for `w ∈ Δ`, `F(z, w)` is the Poisson integral of the Möbius map `ζ ↦ (w − ζ)/(1 − w̄ζ)`, i.e. its value at `z`
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hzΔ
    have hF : ∀ w ∈ LiZhongQC.unitDisc,
        Pommerenke1992.douadyEarleF (fun z => z) z w = (w - z) / (1 - conj w * z) := by
      intro w hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      have hden : ∀ ζ ∈ closedBall (0 : ℂ) 1, 1 - conj w * ζ ≠ 0 := fun ζ hζ h0 => by
        have h1 : ‖conj w * ζ‖ < 1 := by
          rw [norm_mul, Complex.norm_conj]
          exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg w) (mem_closedBall_zero_iff.1 hζ)) hw1
        rw [← sub_eq_zero.1 h0, norm_one] at h1
        exact lt_irrefl _ h1
      have hd : DiffContOnCl ℂ (fun ζ => (w - ζ) / (1 - conj w * ζ)) (ball (0 : ℂ) 1) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball (0 : ℂ) one_ne_zero]
        exact (differentiableOn_const _).sub differentiableOn_id |>.div
          ((differentiableOn_const _).sub (differentiableOn_id.const_mul _)) hden
      have hP := hd.circleAverage_poissonKernel_smul hzΔ
      rw [Real.circleAverage_def] at hP
      rw [← hP]
      -- unfold `douadyEarleF` by `show` (a `rw` with the definition would add an equation lemma `eq_1`)
      show ∫ t in (0 : ℝ)..2 * π, (w - exp (t * I)) / (1 - conj w * exp (t * I)) *
        ((poissonKernel 0 z (exp (t * I)) / (2 * π) : ℝ) : ℂ) = _
      simp only [circleMap_zero, Complex.ofReal_one, one_mul, Pi.smul_apply', Complex.real_smul]
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      push_cast
      ring
    have hex : ∃ w : ℂ, w ∈ LiZhongQC.unitDisc ∧ Pommerenke1992.douadyEarleF (fun z => z) z w = 0 :=
      ⟨z, hzΔ, by rw [hF z hzΔ, sub_self, zero_div]⟩
    obtain ⟨hw, h0⟩ := Classical.epsilon_spec hex
    rw [hF _ hw, div_eq_zero_iff] at h0
    show Pommerenke1992.douadyEarleExt (fun z => z) z = z
    show (if z ∈ LiZhongQC.unitDisc then Classical.epsilon (fun w : ℂ => w ∈ LiZhongQC.unitDisc ∧
      Pommerenke1992.douadyEarleF (fun z => z) z w = 0) else z) = z
    rw [ite_eq_left hzΔ]
    rcases h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exfalso
      have h1 : ‖conj (Classical.epsilon fun w : ℂ => w ∈ LiZhongQC.unitDisc ∧
          Pommerenke1992.douadyEarleF (fun z => z) z w = 0) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz1.le) (mem_ball_zero_iff.1 hw)
      rw [← sub_eq_zero.1 h0, norm_one] at h1
      exact lt_irrefl _ h1
  · -- on the circle the extension is the boundary map itself
    show Pommerenke1992.douadyEarleExt (fun z => z) z = z
    show (if z ∈ LiZhongQC.unitDisc then Classical.epsilon (fun w : ℂ => w ∈ LiZhongQC.unitDisc ∧
      Pommerenke1992.douadyEarleF (fun z => z) z w = 0) else z) = z
    rw [ite_eq_right hzΔ]

/-- **Theorem 2** (§5.1, l. 5009). If a quasisymmetric homeomorphism `h` of `∂Δ` extends to a `K`-quasiconformal
homeomorphism `H` of `Δ`, then the Douady–Earle extension `DE(h)` is `K′`-quasiconformal with `K′` depending only on
`K`. Modelling: `∀ K ∃ K′ ∀ h`; "`H` extends `h`" through the homeomorphic extension `G` of `H` to the closed disc. -/
theorem thm5_2 (K : ℝ) : ∃ K' : ℝ, ∀ h : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo h →
    Pommerenke1992.IsQuasisymmetric h → ∀ (H : ℂ → ℂ) (G : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane),
    LiZhongQC.IsKQC H LiZhongQC.unitDisc K → H '' LiZhongQC.unitDisc = LiZhongQC.unitDisc →
    LiZhongQC.IsHomeoExtension H LiZhongQC.unitDisc LiZhongQC.unitDisc G →
    (∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ = ((h ζ : ℂ) : LiZhongQC.ExtPlane)) →
    LiZhongQC.IsKQC (Pommerenke1992.douadyEarleExt h) LiZhongQC.unitDisc K' := by
  sorry

end GardinerLakic2000
