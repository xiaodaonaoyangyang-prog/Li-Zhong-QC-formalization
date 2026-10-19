import References.GardinerLakic2000.Ch01.S04_GeometricQuasiconformality

/-!
# Gardiner–Lakic 2000, Ch. 1 §1.5 Solving the Beltrami equation

Source `teichmuller.txt`, lines 791–870 (Chapter 1, §1.5).

* Theorem 1 (the mapping theorem, l. 808; cited in Ch. 2, 3, 9, 14), the one-to-one correspondence — exists:
  `LiZhongQC.thm13_7_normalized_existence` (for every μ with ess sup at most k < 1 a unique normalized solution
  fixing 0 and 1; the other direction is the definition of the complex dilatation)
* Theorem 1 (l. 808), holomorphic dependence of `f^μ` on `μ` — exists: `LiZhongQC.thm13_8_ahlfors_bers_holomorphic`
  (reading: holomorphic along holomorphic families of coefficients, leader ruling A0.6)
* Theorem 1 (l. 808), the estimate (1.15) — `thm1_1_c`
* Definition (the space `M(ℍ)` of coefficients supported in ℍ, l. 842) — exists: `LiZhongQC.BeltramiH`
* Definition (the reflected coefficient `μ̃`, l. 842) — exists: `LiZhongQC.symmetricExtension`
* Corollary 1 (l. 847) — `IsNormalizedHSelfMap`, `cor1_1_1_a`, `cor1_1_1_b`
* Lemma 1 (l. 867; cited in Ch. 15 twice) — `lemma1_1`
* Lemma 2 (l. 869; cited in Ch. 14) — `lemma1_2`

Not items: (1.14) is notation; "a solution on `ℂ` restricts to `Ω`" (l. 802, U−); (1.16), (1.17) (l. 828–836) and
"the inverse has the same `‖·‖∞`" (l. 840) are not cited (U−; their content is `LiZhongQC.ahQ_comp_inv_dilatation`
and `LiZhongQC.thm7_2_inv`). Modelling: quasiconformal self-maps of `ℂ̄` fixing `0, 1, ∞` are the project's normalized
plane solutions (`LiZhongQC.IsNormalizedSolution`: onto `ℂ`, fixing `0` and `1`); the solution with coefficient `μ`
is `LiZhongQC.normalizedSolution μ`. Near misses: for (1.15) `LiZhongQC.ah_first_variation` (an `o(t)` bound at each
point, not `C(R) t²` uniformly on `|z| < R`); for Lemma 1 `LiZhongQC.thm13_8_ahlfors_bers_continuous` (continuous
parameter families on the disc); for Lemma 2 `LiZhongQC.thm8_1_normal_family`, `LiZhongQC.thm8_2_limit` (bounded
domains).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC IsBeltramiCoeff normalizedSolution normalizedCauchyTOn complexDilatation upperHalf
  symmetricExtension BeltramiH)

/-- **Theorem 1** (the mapping theorem, §1.5, l. 808), the estimate (1.15). For every `R > 0` there are `δ > 0` and
`C(R) > 0` with `|f^{tμ}(z) − z − t V(z)| ≤ C(R) t²` for `|z| < R`, `|t| < δ`, where
`V(z) = −(z(z − 1)/π) ∬ μ(ζ)/(ζ(ζ − 1)(ζ − z)) dξ dη` (`LiZhongQC.normalizedCauchyTOn` over `ℂ`). -/
theorem thm1_1_c {μ : ℂ → ℂ} (hμ : ∃ k : ℝ, k < 1 ∧ IsBeltramiCoeff μ univ k) {R : ℝ} (hR : 0 < R) :
    ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, ‖z‖ < R →
      ‖normalizedSolution (fun w => t * μ w) z - z - t * normalizedCauchyTOn univ μ z‖ ≤ C * ‖t‖ ^ 2 := by
  sorry

/-- Helper for **Corollary 1** (§1.5, l. 847). `f` is a quasiconformal self-map of `ℍ` with complex dilatation `μ`
on `ℍ`, which extends continuously to the closure of `ℍ` (with `f(z) → ∞` as `z → ∞`) and fixes `0` and `1`. -/
def IsNormalizedHSelfMap (f μ : ℂ → ℂ) : Prop :=
  (∃ K : ℝ, IsKQC f upperHalf K) ∧ f '' upperHalf = upperHalf ∧
    (∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation f z = μ z) ∧
    ContinuousOn f (closure upperHalf) ∧ f '' closure upperHalf = closure upperHalf ∧ f 0 = 0 ∧ f 1 = 1 ∧
    Tendsto f (cocompact ℂ ⊓ 𝓟 (closure upperHalf)) (cocompact ℂ)

/-- **Corollary 1** (§1.5, l. 847), first part. To every `μ ∈ M(ℍ)` there is a unique quasiconformal self-map of `ℍ`
with complex dilatation `μ`, extending continuously to `ℍ̄` and fixing `0, 1, ∞` (unique on `ℍ̄`). -/
theorem cor1_1_1_a (μ : BeltramiH) :
    ∃ f : ℂ → ℂ, IsNormalizedHSelfMap f μ.1 ∧
      ∀ g : ℂ → ℂ, IsNormalizedHSelfMap g μ.1 → EqOn g f (closure upperHalf) := by
  obtain ⟨⟨k, hk₀, hk, hμ⟩, -⟩ := μ.2
  have hμH : IsBeltramiCoeff μ.1 upperHalf k :=
    ⟨hμ.1.mono_measure (Measure.restrict_mono (subset_univ _) le_rfl),
      ae_restrict_of_ae_restrict_of_subset (subset_univ _) hμ.2⟩
  -- existence: `f^μ`, the normalized solution for the symmetric extension of `μ` (S33)
  obtain ⟨-, hN, hK, huniq⟩ := LiZhongQC.bg_sym_spec hk₀ hk hμH
  obtain ⟨himg, -, -, hKH, hd⟩ := LiZhongQC.fMuSym_upperHalf hk₀ hk hμH
  obtain ⟨-, hs, h0, h1, -⟩ := hN
  obtain ⟨e, he⟩ := LiZhongQC.t1_homeomorph hK hs
  have h01 : (0 : ℂ) ∈ closure upperHalf ∧ (1 : ℂ) ∈ closure upperHalf := by
    rw [LiZhongQC.scExt_closure_upperHalf]
    exact ⟨le_refl (0 : ℝ), by simp⟩
  refine ⟨LiZhongQC.fMuSym μ.1, ⟨⟨_, hKH⟩, himg, hd, ?_, ?_, h0, h1, ?_⟩, ?_⟩
  · rw [← he]
    exact e.continuous.continuousOn
  · rw [← he, e.image_closure, he, himg]
  · rw [← he]
    exact (show Tendsto (⇑e) (cocompact ℂ) (cocompact ℂ) from e.map_cocompact.le).mono_left inf_le_left
  -- uniqueness: reflect `g` to a normalized solution `G` for the symmetric extension (S13), so `G = f^μ`
  intro g hg
  obtain ⟨⟨Kg, hgK⟩, hgimg, hgd, hgc, -, hg0, hg1, hginf⟩ := hg
  obtain ⟨G, hGK, hGs, hGg, hGsym⟩ := LiZhongQC.qc_reflection_extension hgK hgimg
    (hginf.mono_left (inf_le_inf_left _ (principal_mono.2 subset_closure)))
  obtain ⟨e', he'⟩ := LiZhongQC.t1_homeomorph hGK hGs
  have hGg' : EqOn G g (closure upperHalf) :=
    hGg.of_subset_closure (he' ▸ e'.continuous.continuousOn) hgc subset_closure subset_rfl
  have hU : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation G z = μ.1 z := by
    filter_upwards [hgd, ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz₁ hz₂
    rw [LiZhongQC.bg_dilatation_congr LiZhongQC.isOpen_upperHalf hGg hz₂, hz₁]
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict LiZhongQC.lowerHalf)
      (volume.restrict upperHalf) := by
    have h := LiZhongQC.gzE_conj_measurePreserving.restrict_preimage LiZhongQC.isOpen_upperHalf.measurableSet
    rwa [LiZhongQC.bg_s_conj_preimage_upperHalf] at h
  have hGr : G = fun w => conj (G (conj w)) := funext fun w => by rw [hGsym, Complex.conj_conj]
  have hGd : ∀ᵐ z, complexDilatation G z = symmetricExtension μ.1 z := by
    refine LiZhongQC.bg_ae_of_halves ?_ ?_
    · filter_upwards [hU, ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz₁ hz₂
      rw [hz₁, symmetricExtension, ite_eq_right (not_lt.2 (le_of_lt hz₂))]
    · filter_upwards [hmp.quasiMeasurePreserving.ae hU, ae_restrict_mem LiZhongQC.isOpen_lowerHalf.measurableSet]
        with z hz₁ hz₂
      have hc := LiZhongQC.bg_dilatation_conj G z
      rw [← hGr] at hc
      rw [hc, hz₁, symmetricExtension, ite_eq_left (show z.im < 0 from hz₂)]
  have hGN : LiZhongQC.IsNormalizedSolution G (symmetricExtension μ.1) :=
    ⟨⟨_, hGK⟩, hGs, (hGg' h01.1).trans hg0, (hGg' h01.2).trans hg1, hGd⟩
  intro z hz
  rw [← hGg' hz, huniq G hGN]

/-- **Corollary 1** (§1.5, l. 847–862), second part. For every `R > 0` there are `C(R) > 0` and `δ > 0` with
`|f^{tμ}(z) − z − t F(z)| ≤ C(R) t²` for `|z| < R` and real `|t| < δ`, where
`F(z) = −(1/π) ∬_ℍ [μ(ζ) R(ζ, z) + μ̄(ζ) R(ζ̄, z)] dξ dη`, `R(ζ, z) = z(z − 1)/(ζ(ζ − 1)(ζ − z))`; `f^{tμ}` is the
normalized solution with the reflected coefficient `(tμ)~` (l. 842–844). -/
theorem cor1_1_1_b (μ : BeltramiH) {R : ℝ} (hR : 0 < R) :
    ∃ C > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| < δ → ∀ z : ℂ, ‖z‖ < R →
      ‖normalizedSolution (symmetricExtension (fun w => (t : ℂ) * μ.1 w)) z - z -
          t * (-(1 / π : ℂ) * ∫ ζ in upperHalf,
            (μ.1 ζ * (z * (z - 1) / (ζ * (ζ - 1) * (ζ - z))) +
              conj (μ.1 ζ) * (z * (z - 1) / (conj ζ * (conj ζ - 1) * (conj ζ - z)))))‖ ≤ C * t ^ 2 := by
  sorry

/-- Helper for `lemma1_1` (§1.5). A Beltrami coefficient on `ℂ` bounded by `k` forces `0 ≤ k` (`ℂ` is not null). -/
theorem gl1_bel_k_nonneg {μ : ℂ → ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ univ k) : 0 ≤ k := by
  by_contra hk
  push Not at hk
  have h := hμ.2
  rw [Measure.restrict_univ] at h
  have hF : ∀ᵐ z : ℂ, False := h.mono fun z hz =>
    absurd (lt_of_le_of_lt (norm_nonneg _) (hz.trans_lt hk)) (lt_irrefl _)
  have h0 : volume {z : ℂ | ¬ False} = 0 := ae_iff.1 hF
  have h1 : volume (ball (0 : ℂ) 1) = 0 := measure_mono_null (fun z _ => not_false) h0
  exact (measure_ball_pos volume (0 : ℂ) one_pos).ne' h1

/-- Helper for `lemma1_1` (§1.5). An a.e. limit of Beltrami coefficients bounded by `k` is a Beltrami coefficient
bounded by `k` (a.e. strongly measurable as an a.e. limit, and the bound passes to the limit). -/
theorem gl1_bel_limit_coeff {μ : ℕ → ℂ → ℂ} {ν : ℂ → ℂ} {k : ℝ} (hμ : ∀ n, IsBeltramiCoeff (μ n) univ k)
    (hconv : ∀ᵐ z, Tendsto (fun n => μ n z) atTop (𝓝 (ν z))) : IsBeltramiCoeff ν univ k := by
  rw [IsBeltramiCoeff, Measure.restrict_univ]
  have hm : ∀ n, AEStronglyMeasurable (μ n) volume := fun n => by
    have := (hμ n).1
    rwa [Measure.restrict_univ] at this
  have hb : ∀ n, ∀ᵐ z, ‖μ n z‖ ≤ k := fun n => by
    have := (hμ n).2
    rwa [Measure.restrict_univ] at this
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hm hconv, ?_⟩
  filter_upwards [ae_all_iff.2 hb, hconv] with z hz hc
  exact le_of_tendsto' hc.norm hz

/-- Helper for `lemma1_1` (§1.5). For `‖μ‖ ≤ k < 1` the value `f^μ = normalizedSolution μ` is a genuine normalized
solution (the `choose` branch, by `LiZhongQC.thm13_7_normalized_existence`) and is `(1 + k)/(1 − k)`-quasiconformal. -/
theorem gl1_bel_spec {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ univ k) :
    LiZhongQC.IsNormalizedSolution (normalizedSolution μ) μ ∧
      IsKQC (normalizedSolution μ) univ ((1 + k) / (1 - k)) := by
  obtain ⟨f₀, hf₀, hK, huniq⟩ := LiZhongQC.thm13_7_normalized_existence (gl1_bel_k_nonneg hμ) hk hμ
  have hex : ∃ f : ℂ → ℂ, LiZhongQC.IsNormalizedSolution f μ := ⟨f₀, hf₀⟩
  have hspec : LiZhongQC.IsNormalizedSolution (normalizedSolution μ) μ := by
    rw [normalizedSolution, dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hspec, ?_⟩
  rw [huniq _ hspec]
  exact hK

/-- Helper for `lemma1_1` (§1.5). The quotient `H = f₁ ∘ f₀⁻¹` of two normalized solutions for coefficients bounded
by `k` is a normalized `K²`-quasiconformal self-map of the plane (`K = (1 + k)/(1 − k)`), and
`|μ_H(f₀ z)| (1 − k) ≤ |μ₁(z) − μ₀(z)|` a.e. (`LiZhongQC.ahQ_comp_inv_dilatation`, `|1 − μ̄₀ μ₁| ≥ 1 − k²`). -/
theorem gl1_bel_quotient {μ₁ μ₀ f₁ f₀ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμ₁ : IsBeltramiCoeff μ₁ univ k)
    (hμ₀ : IsBeltramiCoeff μ₀ univ k) (hf₁ : LiZhongQC.IsNormalizedSolution f₁ μ₁)
    (hf₀ : LiZhongQC.IsNormalizedSolution f₀ μ₀) (hK₁ : IsKQC f₁ univ ((1 + k) / (1 - k)))
    (hK₀ : IsKQC f₀ univ ((1 + k) / (1 - k))) :
    LiZhongQC.IsKQCNormalizedPlane (f₁ ∘ Function.invFunOn f₀ univ) (((1 + k) / (1 - k)) ^ 2) ∧
      ∀ᵐ z, ‖complexDilatation (f₁ ∘ Function.invFunOn f₀ univ) (f₀ z)‖ * (1 - k) ≤ ‖μ₁ z - μ₀ z‖ := by
  have hk0 : 0 ≤ k := gl1_bel_k_nonneg hμ₁
  have hs₀ : f₀ '' univ = univ := hf₀.2.1
  have hinj₀ : InjOn f₀ univ := hK₀.2.2.1.2.1
  have hleft : ∀ x, Function.invFunOn f₀ univ (f₀ x) = x := fun x => hinj₀.leftInvOn_invFunOn (mem_univ x)
  -- normalization and the constant `K²`
  have hinvK : IsKQC (Function.invFunOn f₀ univ) univ ((1 + k) / (1 - k)) := by
    have h := LiZhongQC.thm7_2_inv hK₀
    rwa [hs₀] at h
  have hHK : IsKQC (f₁ ∘ Function.invFunOn f₀ univ) univ (((1 + k) / (1 - k)) ^ 2) := by
    rw [sq]
    exact LiZhongQC.thm7_1_comp hinvK hK₁ (subset_univ _)
  have hinvs : Function.invFunOn f₀ univ '' univ = univ :=
    eq_univ_of_forall fun x => ⟨f₀ x, mem_univ _, hleft x⟩
  have himg : (f₁ ∘ Function.invFunOn f₀ univ) '' univ = univ := by
    rw [image_comp, hinvs]
    exact hf₁.2.1
  have hH0 : (f₁ ∘ Function.invFunOn f₀ univ) 0 = 0 := by
    have e := hleft 0
    rw [hf₀.2.2.1] at e
    rw [Function.comp_apply, e, hf₁.2.2.1]
  have hH1 : (f₁ ∘ Function.invFunOn f₀ univ) 1 = 1 := by
    have e := hleft 1
    rw [hf₀.2.2.2.1] at e
    rw [Function.comp_apply, e, hf₁.2.2.2.1]
  refine ⟨⟨hHK, himg, hH0, hH1⟩, ?_⟩
  -- the dilatation of the quotient
  have hdil := LiZhongQC.ahQ_comp_inv_dilatation hK₁ hK₀
  have hb₁ := hμ₁.2
  have hb₀ := hμ₀.2
  rw [Measure.restrict_univ] at hdil hb₁ hb₀
  filter_upwards [hdil, hf₁.2.2.2.2, hf₀.2.2.2.2, hb₁, hb₀] with z hz e₁ e₀ hz₁ hz₀
  rw [hz, e₁, e₀]
  set a := μ₁ z with ha
  set b := μ₀ z with hb
  set d := LiZhongQC.dz f₀ z with hd
  have hden : 1 - k ≤ ‖1 - conj b * a‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (conj b * a)
    rw [norm_one, norm_mul, Complex.norm_conj] at h1
    have h2 : ‖b‖ * ‖a‖ ≤ k * k := mul_le_mul hz₀ hz₁ (norm_nonneg _) hk0
    nlinarith
  have hpos : 0 < ‖1 - conj b * a‖ := by linarith
  have hdd : ‖d / conj d‖ ≤ 1 := by
    rw [norm_div, Complex.norm_conj]
    exact div_self_le_one _
  rw [norm_mul, norm_div]
  have h3 : ‖a - b‖ / ‖1 - conj b * a‖ * ‖d / conj d‖ ≤ ‖a - b‖ / ‖1 - conj b * a‖ :=
    mul_le_of_le_one_right (by positivity) hdd
  calc ‖a - b‖ / ‖1 - conj b * a‖ * ‖d / conj d‖ * (1 - k)
      ≤ ‖a - b‖ / ‖1 - conj b * a‖ * ‖1 - conj b * a‖ :=
        mul_le_mul h3 hden (by linarith) (by positivity)
    _ = ‖a - b‖ := div_mul_cancel₀ _ hpos.ne'

/-- Helper for `lemma1_1` (§1.5). The subsequence principle for locally uniform convergence on `ℂ`: if every
subsequence has a further subsequence converging locally uniformly to `g`, so does the whole sequence. -/
theorem gl1_bel_tlu_of_subseq {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformly (fun n => F (φ (ψ n))) g atTop) :
    TendstoLocallyUniformly F g atTop := by
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro C _ hC
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hne
  obtain ⟨ψ, -, hlim⟩ := h φ hφ
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ] at hlim
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 (hlim C (subset_univ _) hC) ε hε).exists
  exact hφP (ψ n) hn

/-- Helper for `lemma1_1` (§1.5). Normalized `K`-quasiconformal self-maps of the plane whose complex dilatations tend
to `0` a.e. tend to the identity locally uniformly: by `gl1_bel_tlu_of_subseq`, `ut2_nf_extract` and `ut2_nf_limit`,
any subsequential limit is a normalized quasiconformal map, holomorphic on every disc (`ab_limit_holomorphic`), hence
affine (`nx_entire_affine`) and fixing `0, 1`, i.e. the identity. -/
theorem gl1_bel_tendsto_id {G : ℕ → ℂ → ℂ} {K : ℝ} (hG : ∀ n, LiZhongQC.IsKQCNormalizedPlane (G n) K)
    (hμ : ∀ᵐ z, Tendsto (fun n => complexDilatation (G n) z) atTop (𝓝 0)) :
    TendstoLocallyUniformly G id atTop := by
  refine gl1_bel_tlu_of_subseq fun φ hφ => ?_
  obtain ⟨ψ, hψ, g, hg⟩ := LiZhongQC.UniversalTeichmuller.ut2_nf_extract (fun n => hG (φ n))
  refine ⟨ψ, hψ, ?_⟩
  have hgN := LiZhongQC.UniversalTeichmuller.ut2_nf_limit (fun n => hG (φ (ψ n))) hg
  -- the dilatations of the subsequence still tend to `0` a.e.
  have hμs : ∀ᵐ z, Tendsto (fun n => complexDilatation (G (φ (ψ n))) z) atTop (𝓝 0) :=
    hμ.mono fun w hw => hw.comp (hφ.comp hψ).tendsto_atTop
  -- the limit is holomorphic on every disc `B(0, R)`
  have hdiff : DifferentiableOn ℂ g univ := by
    intro z _
    set R : ℝ := ‖z‖ + 1 with hR
    have hR0 : 0 < R := by positivity
    have hball : DifferentiableOn ℂ g (ball 0 R) := by
      refine LiZhongQC.ab_limit_holomorphic isOpen_ball isBounded_ball (K := K)
        (fun n => LiZhongQC.ac_t_isKQC_restrict (hG (φ (ψ n))).1 isOpen_ball (subset_univ _))
        ⟨_, fun n w hw => LiZhongQC.UniversalTeichmuller.ut2_nb_upper (hG (φ (ψ n))) hR0
          (mem_ball_zero_iff.1 hw).le⟩ hg.tendstoLocallyUniformlyOn (ae_restrict_of_ae hμs)
    have hz : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 (by linarith)
    exact (hball.differentiableAt (isOpen_ball.mem_nhds hz)).differentiableWithinAt
  -- a conformal bijection of `ℂ` fixing `0` and `1` is the identity
  obtain ⟨a, b, -, hab⟩ := LiZhongQC.nx_entire_affine ⟨hdiff, hgN.1.2.2.1.2.1, hgN.2.1⟩
  have hb : b = 0 := by
    have := hab 0
    rw [hgN.2.2.1, mul_zero, zero_add] at this
    exact this.symm
  have ha : a = 1 := by
    have := hab 1
    rw [hgN.2.2.2, mul_one, hb, add_zero] at this
    exact this.symm
  have hgid : g = id := funext fun z => by
    rw [hab z, ha, hb, one_mul, add_zero, id]
  rw [hgid] at hg
  exact hg

/-- **Lemma 1** (§1.5, l. 867). If `‖μₙ‖∞ ≤ k < 1` and `μₙ → μ` almost everywhere, then the normalized solutions
`f^{μₙ}` converge to `f^μ` uniformly on compact subsets of `ℂ`. -/
theorem lemma1_1 {μ : ℕ → ℂ → ℂ} {ν : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμ : ∀ n, IsBeltramiCoeff (μ n) univ k)
    (hconv : ∀ᵐ z, Tendsto (fun n => μ n z) atTop (𝓝 (ν z))) :
    TendstoLocallyUniformly (fun n => normalizedSolution (μ n)) (normalizedSolution ν) atTop := by
  -- the coefficients and their normalized solutions are genuine
  have hν := gl1_bel_limit_coeff hμ hconv
  obtain ⟨hf, hfK⟩ := gl1_bel_spec hk hν
  -- the quotients `Hₙ = f^{μₙ} ∘ (f^ν)⁻¹` (normalized, `K²`-q.c.)
  have hQ := fun n => gl1_bel_quotient hk (hμ n) hν (gl1_bel_spec hk (hμ n)).1 hf (gl1_bel_spec hk (hμ n)).2 hfK
  -- their dilatations tend to `0` a.e. at `f^ν(z)`, hence a.e. (`f^ν` preserves null sets and is onto)
  have hk1 : 0 < 1 - k := by linarith
  have hgood : ∀ᵐ z, Tendsto (fun n => complexDilatation
      (normalizedSolution (μ n) ∘ Function.invFunOn (normalizedSolution ν) univ) (normalizedSolution ν z))
      atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.2 fun n => (hQ n).2, hconv] with z hzb hc
    have hc' : Tendsto (fun n => ‖μ n z - ν z‖ / (1 - k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => μ n z - ν z) atTop (𝓝 0) := by
        simpa using hc.sub_const (ν z)
      simpa using h1.norm.div_const (1 - k)
    refine squeeze_zero_norm (fun n => ?_) hc'
    rw [le_div_iff₀ hk1]
    exact hzb n
  have hin : ∀ᵐ w, Tendsto (fun n => complexDilatation
      (normalizedSolution (μ n) ∘ Function.invFunOn (normalizedSolution ν) univ) w) atTop (𝓝 0) := by
    have h1 := LiZhongQC.abT_ae_image (p := fun w => Tendsto (fun n => complexDilatation
      (normalizedSolution (μ n) ∘ Function.invFunOn (normalizedSolution ν) univ) w) atTop (𝓝 0)) hfK
      (by rw [Measure.restrict_univ]; exact hgood)
    rwa [hf.2.1, Measure.restrict_univ] at h1
  -- `Hₙ → id` locally uniformly, so `f^{μₙ} = Hₙ ∘ f^ν → f^ν`
  have hid := gl1_bel_tendsto_id (fun n => (hQ n).1) hin
  have hcont : Continuous (normalizedSolution ν) := continuousOn_univ.1 hfK.2.2.1.1
  have hcomp := hid.comp (normalizedSolution ν) hcont
  have hinj : InjOn (normalizedSolution ν) univ := hfK.2.2.1.2.1
  have e : (fun n => (normalizedSolution (μ n) ∘ Function.invFunOn (normalizedSolution ν) univ) ∘
      normalizedSolution ν) = fun n => normalizedSolution (μ n) := by
    funext n z
    simp only [Function.comp_apply]
    rw [hinj.leftInvOn_invFunOn (mem_univ z)]
  rw [e, Function.id_comp] at hcomp
  exact hcomp

/-- **Lemma 2** (§1.5, l. 869). A sequence of `K₀`-quasiconformal homeomorphisms of `ℂ̄` fixing `0, 1, ∞` has a
subsequence converging uniformly on compact subsets of `ℂ` to a normalized quasiconformal map `f` with
`K(f) ≤ K₀`. -/
theorem lemma1_2 {f : ℕ → ℂ → ℂ} {K₀ : ℝ} (hf : ∀ n, IsKQC (f n) univ K₀) (honto : ∀ n, f n '' univ = univ)
    (h0 : ∀ n, f n 0 = 0) (h1 : ∀ n, f n 1 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, TendstoLocallyUniformly (fun n => f (φ n)) g atTop ∧
      IsKQC g univ K₀ ∧ g '' univ = univ ∧ g 0 = 0 ∧ g 1 = 1 := by
  have hF : ∀ n, LiZhongQC.IsKQCNormalizedPlane (f n) K₀ := fun n => ⟨hf n, honto n, h0 n, h1 n⟩
  obtain ⟨φ, hφ, g, hg⟩ := LiZhongQC.UniversalTeichmuller.ut2_nf_extract hF
  obtain ⟨hgK, hgs, hg0, hg1⟩ := LiZhongQC.UniversalTeichmuller.ut2_nf_limit (fun n => hF (φ n)) hg
  exact ⟨φ, hφ, g, hg, hgK, hgs, hg0, hg1⟩

end GardinerLakic2000
