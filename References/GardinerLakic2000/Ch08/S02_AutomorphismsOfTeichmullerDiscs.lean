import References.GardinerLakic2000.Ch08.S01_GlobalToLocal

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.2 Automorphisms of Teichmüller discs

Source `teichmuller.txt`, lines 6590–6663 (Chapter 8, §8.2).

* Definition (the stabilizer `Γ(D_φ)` of a Teichmüller disc in the mapping class group, l. 6591) — `discStabilizer`
* Theorem 3 (l. 6593; cited at l. 8735) — `thm8_3`
* Definition (the action of `ρ_g` on `D_φ` by `t ↦ (at + b)/(b̄t + ā)`, l. 6621–6625) — `ActsOnDiscBy`
* Theorem 4 (l. 6621) — `thm8_4_a`, `thm8_4_b`

Not items: (8.1) and the computation l. 6635–6662 (proof); "`Γ` rarely contains more than one element … Veech"
(l. 6591, a remark). Modelling: as §8.1 (Fuchsian model, C0.1–C0.3); the mapping class `[g]` is represented by
`g ∈ QC(Γ)` and "`ρ_g(D_φ) = D_φ`" by a `Φ` with `IsRhoGamma Γ Γ g Φ` preserving `D_φ`. In Theorem 3 the natural
parameter identity (b) `φ(f(z)) f_z(z)² = a² φ(z)` is read almost everywhere on `ℍ` for the lifted differential.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (upperHalf unitDisc BeltramiGamma TeichGamma teichSetoidGamma IsFuchsian integrableAutomorphicQD
  phiArea IsFundamentalDomainH complexDilatation dz)

/-- **Definition** (§8.2, l. 6591). `Γ(D_φ)`: the elements `g` of `QC(Γ)` whose geometric isomorphism preserves the
Teichmüller disc `D_φ`. -/
def discStabilizer (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) : Set (ℂ → ℂ) :=
  {g | g ∈ qcNormalizer Γ ∧ ∃ Φ : TeichGamma Γ → TeichGamma Γ, IsRhoGamma Γ Γ g Φ ∧
    Φ '' teichmullerDisc Γ φ = teichmullerDisc Γ φ}

/-- **Definition** (§8.2, l. 6621–6625). `Φ` acts on `D_φ` by the Möbius map `t ↦ (at + b)/(b̄t + ā)`:
`Φ([t|φ|/φ]) = [((at + b)/(b̄t + ā)) |φ|/φ]` for `|t| < 1`. -/
def ActsOnDiscBy (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ)
    (Φ : TeichGamma Γ → TeichGamma Γ) (a b : ℂ) : Prop :=
  ∀ t ∈ unitDisc, ∀ μ ν : BeltramiGamma Γ, (∀ z ∈ upperHalf, μ.1.1 z = t * (conj (φ z) / ‖φ z‖)) →
    (∀ z ∈ upperHalf, ν.1.1 z = (a * t + b) / (conj b * t + conj a) * (conj (φ z) / ‖φ z‖)) →
      Φ (Quotient.mk (teichSetoidGamma Γ) μ) = Quotient.mk (teichSetoidGamma Γ) ν

/-- Helper for `thm8_4_b`: for `|a|² − |b|² = 1` and `|t| < 1`, `b̄t + ā ≠ 0` and `(at + b)/(b̄t + ā)` lies in the disc
(`|b̄t + ā|² − |at + b|² = (|a|² − |b|²)(1 − |t|²)`). -/
theorem gl8_mob_disc {a b t : ℂ} (hn : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1) (ht : ‖t‖ < 1) :
    conj b * t + conj a ≠ 0 ∧ ‖(a * t + b) / (conj b * t + conj a)‖ < 1 := by
  have hid : normSq (conj b * t + conj a) - normSq (a * t + b) = (normSq a - normSq b) * (1 - normSq t) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [Complex.normSq_eq_norm_sq a, Complex.normSq_eq_norm_sq b, hn, one_mul] at hid
  have ht2 : normSq t < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg t]
  have hden : 0 < normSq (conj b * t + conj a) := by
    have := Complex.normSq_nonneg (a * t + b)
    linarith
  refine ⟨fun h => by rw [h, map_zero] at hden; exact lt_irrefl 0 hden, ?_⟩
  have h1 : normSq ((a * t + b) / (conj b * t + conj a)) < 1 := by
    rw [map_div₀, div_lt_one hden]
    linarith
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg ((a * t + b) / (conj b * t + conj a))]

/-- Helper for `thm8_4_b`: the Möbius maps `t ↦ (at + b)/(b̄t + ā)` compose by the matrix product:
`M₁(M₂(t)) = ((a₁a₂ + b₁b̄₂)t + (a₁b₂ + b₁ā₂))/(conj(a₁b₂ + b₁ā₂) t + conj(a₁a₂ + b₁b̄₂))`. -/
theorem gl8_mob_comp {a₁ b₁ a₂ b₂ t : ℂ} (hd₂ : conj b₂ * t + conj a₂ ≠ 0) :
    (a₁ * ((a₂ * t + b₂) / (conj b₂ * t + conj a₂)) + b₁) /
        (conj b₁ * ((a₂ * t + b₂) / (conj b₂ * t + conj a₂)) + conj a₁) =
      ((a₁ * a₂ + b₁ * conj b₂) * t + (a₁ * b₂ + b₁ * conj a₂)) /
        (conj (a₁ * b₂ + b₁ * conj a₂) * t + conj (a₁ * a₂ + b₁ * conj b₂)) := by
  set s := (a₂ * t + b₂) / (conj b₂ * t + conj a₂) with hs
  have hsD : s * (conj b₂ * t + conj a₂) = a₂ * t + b₂ := div_mul_cancel₀ _ hd₂
  have hN : (a₁ * a₂ + b₁ * conj b₂) * t + (a₁ * b₂ + b₁ * conj a₂) =
      (a₁ * s + b₁) * (conj b₂ * t + conj a₂) := by
    linear_combination (-a₁) * hsD
  have hD : conj (a₁ * b₂ + b₁ * conj a₂) * t + conj (a₁ * a₂ + b₁ * conj b₂) =
      (conj b₁ * s + conj a₁) * (conj b₂ * t + conj a₂) := by
    simp only [map_add, map_mul, Complex.conj_conj]
    linear_combination (-conj b₁) * hsD
  rw [hN, hD, mul_div_mul_right _ _ hd₂]

/-- Helper for `thm8_4_b`: for an integrable automorphic `φ` and `|s| < 1`, the Teichmüller–Beltrami differential
`s φ̄/|φ|` on `ℍ` (extended by `0`) is an element of `M(Γ)` (`|s φ̄/|φ|| ≤ |s|`, and `Γ`-compatibility from
`φ(γz)(γ′z)² = φ(z)`). -/
theorem gl8_disc_beltrami {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : Set ℂ} {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) {s : ℂ} (hs : ‖s‖ < 1) :
    ∃ μ : BeltramiGamma Γ, ∀ z ∈ upperHalf, μ.1.1 z = s * (conj (φ z) / ‖φ z‖) := by
  classical
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  set f : ℂ → ℂ := upperHalf.indicator fun z => s * (conj (φ z) / ‖φ z‖) with hf
  have hfm : AEStronglyMeasurable f volume := by
    rw [hf, aestronglyMeasurable_indicator_iff hU]
    have hφm : AEMeasurable φ (volume.restrict upperHalf) :=
      (hφ.1.continuousOn.aestronglyMeasurable hU).aemeasurable
    exact (aemeasurable_const.mul ((Complex.continuous_conj.measurable.comp_aemeasurable hφm).div
      (Complex.measurable_ofReal.comp_aemeasurable hφm.norm))).aestronglyMeasurable
  have hbound : ∀ z, ‖f z‖ ≤ ‖s‖ := by
    intro z
    by_cases hz : z ∈ upperHalf
    · rw [hf, indicator_of_mem hz, norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      by_cases h0 : ‖φ z‖ = 0
      · rw [h0, div_zero, mul_zero]
        exact norm_nonneg _
      · rw [div_self h0, mul_one]
    · rw [hf, indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  have hzero : ∀ z : ℂ, z.im ≤ 0 → f z = 0 := by
    intro z hz
    rw [hf, indicator_of_notMem]
    show ¬ (0 < z.im)
    linarith
  have hcompat : LiZhongQC.IsGammaCompatible Γ f := by
    intro γ hγ
    filter_upwards [ae_restrict_mem hU] with z hz
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.det_coe
      rwa [Matrix.det_fin_two] at h
    set e : ℂ := (γ 1 0 : ℂ) * z + γ 1 1 with he
    have hz' : 0 < z.im := hz
    have he0 : e ≠ 0 := by
      intro h0
      have him := congrArg Complex.im h0
      simp only [he, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.zero_im] at him
      rcases mul_eq_zero.1 him with h | h
      · have hre := congrArg Complex.re h0
        simp only [he, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.zero_re, h, zero_mul, zero_add] at hre
        rw [h, hre, mul_zero, mul_zero, sub_zero] at hdet
        exact zero_ne_one hdet
      · linarith
    have hγz : ((γ 0 0 : ℂ) * z + γ 0 1) / e ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
    have hauto := hφ.2.2 γ hγ z hz
    have hφγ : φ (((γ 0 0 : ℂ) * z + γ 0 1) / e) = φ z * e ^ 4 := by
      rw [← hauto, div_mul_cancel₀ _ (pow_ne_zero 4 he0)]
    show f z = f (((γ 0 0 : ℂ) * z + γ 0 1) / e) * (e ^ 2 / conj (e ^ 2))
    rw [hf, indicator_of_mem hz, indicator_of_mem hγz, hφγ]
    set w := φ z with hw
    have hce : conj e ≠ 0 := (map_ne_zero _).2 he0
    have hen : (‖e‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 he0).ne'
    have hee : conj e * e = (‖e‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    by_cases hw0 : w = 0
    · rw [hw0]
      simp
    have hwn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw0).ne'
    have key : conj e ^ 4 * (e ^ 2 / conj (e ^ 2)) = (‖e‖ : ℂ) ^ 4 := by
      rw [map_pow, mul_div_assoc', show conj e ^ 4 * e ^ 2 = (conj e * e) ^ 2 * conj e ^ 2 by ring, hee,
        mul_div_assoc, div_self (pow_ne_zero 2 hce), mul_one]
      ring
    calc s * (conj w / ‖w‖)
        = s * conj w * (‖e‖ : ℂ) ^ 4 / ((‖w‖ : ℂ) * (‖e‖ : ℂ) ^ 4) := by
          field_simp
      _ = s * conj w * (conj e ^ 4 * (e ^ 2 / conj (e ^ 2))) / ((‖w‖ : ℂ) * (‖e‖ : ℂ) ^ 4) := by rw [key]
      _ = s * (conj (w * e ^ 4) / ‖w * e ^ 4‖) * (e ^ 2 / conj (e ^ 2)) := by
          simp only [map_mul, map_pow, norm_mul, norm_pow]
          push_cast
          ring
  refine ⟨⟨⟨f, ⟨‖s‖, norm_nonneg _, hs, hfm.restrict, Eventually.of_forall fun z => hbound z⟩, hzero⟩, hcompat⟩,
    fun z hz => ?_⟩
  show f z = _
  rw [hf, indicator_of_mem hz]

/-- **Theorem 3** (§8.2, l. 6593). If `ρ_g(D_φ) = D_φ`, there is `f` in the class of `g` with (a) Beltrami coefficient
`−s|φ|/φ`, `|s| < 1`, (b) `φ(f(z)) f_z(z)² = a² φ(z)` for a constant `a ≠ 0`, and (c) `ρ_f = ρ_g`. -/
theorem thm8_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (hφ1 : phiArea φ F = 1)
    {g : ℂ → ℂ} (hg : g ∈ discStabilizer Γ φ) :
    ∃ f ∈ qcNormalizer Γ, ∃ s : ℂ, ‖s‖ < 1 ∧ ∃ a : ℂ, a ≠ 0 ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f z = -s * (conj (φ z) / ‖φ z‖)) ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), φ (f z) * dz f z ^ 2 = a ^ 2 * φ z) ∧
      ∀ Φ Ψ : TeichGamma Γ → TeichGamma Γ, IsRhoGamma Γ Γ g Φ → IsRhoGamma Γ Γ f Ψ → ∀ P, Ψ P = Φ P := by
  sorry

/-- **Theorem 4** (§8.2, l. 6621), the action. Every element of `Γ(D_φ)` acts on `D_φ` as an isometry of the Poincaré
metric: by `t ↦ (at + b)/(b̄t + ā)` for a matrix `(a b; b̄ ā)` with `|a|² − |b|² = 1`, determined up to sign. -/
theorem thm8_4_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (hφ1 : phiArea φ F = 1)
    {g : ℂ → ℂ} (hg : g ∈ discStabilizer Γ φ) {Φ : TeichGamma Γ → TeichGamma Γ} (hΦ : IsRhoGamma Γ Γ g Φ) :
    ∃ a b : ℂ, ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1 ∧ ActsOnDiscBy Γ φ Φ a b ∧
      ∀ a' b' : ℂ, ‖a'‖ ^ 2 - ‖b'‖ ^ 2 = 1 → ActsOnDiscBy Γ φ Φ a' b' → (a' = a ∧ b' = b) ∨ (a' = -a ∧ b' = -b) := by
  sorry

/-- **Theorem 4** (§8.2, l. 6627–6633), the homomorphism. The map `ρ_g ↦ (t ↦ (at + b)/(b̄t + ā))` is a homomorphism
from `Γ(D_φ)` to the Möbius transformations of the disc: the composite `ρ_{g₁} ∘ ρ_{g₂}` acts by the product
matrix. -/
theorem thm8_4_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) (hφ1 : phiArea φ F = 1)
    {Φ₁ Φ₂ : TeichGamma Γ → TeichGamma Γ} {a₁ b₁ a₂ b₂ : ℂ} (h₁ : ActsOnDiscBy Γ φ Φ₁ a₁ b₁)
    (h₂ : ActsOnDiscBy Γ φ Φ₂ a₂ b₂) (hn₁ : ‖a₁‖ ^ 2 - ‖b₁‖ ^ 2 = 1) (hn₂ : ‖a₂‖ ^ 2 - ‖b₂‖ ^ 2 = 1) :
    ActsOnDiscBy Γ φ (Φ₁ ∘ Φ₂) (a₁ * a₂ + b₁ * conj b₂) (a₁ * b₂ + b₁ * conj a₂) := by
  -- `hΓ`, `hF`, `hφ1` and `hn₁` are not needed: the composition rule is Möbius algebra (an identity of fractions,
  -- also when a denominator vanishes) plus the intermediate point `M₂(t)` of the disc, which only needs `hn₂`
  have _ := hΓ
  have _ := hF
  have _ := hφ1
  have _ := hn₁
  intro t ht μ ν hμ hν
  obtain ⟨hd₂, hs⟩ := gl8_mob_disc hn₂ (mem_ball_zero_iff.1 ht)
  set s := (a₂ * t + b₂) / (conj b₂ * t + conj a₂) with hsdef
  obtain ⟨μ', hμ'⟩ := gl8_disc_beltrami hφ hs
  have hs' : s ∈ unitDisc := mem_ball_zero_iff.2 hs
  have e₂ := h₂ t ht μ μ' hμ hμ'
  have e₁ := h₁ s hs' μ' ν hμ' (fun z hz => by rw [hν z hz, hsdef, gl8_mob_comp hd₂])
  show Φ₁ (Φ₂ _) = _
  rw [e₂, e₁]

end GardinerLakic2000
