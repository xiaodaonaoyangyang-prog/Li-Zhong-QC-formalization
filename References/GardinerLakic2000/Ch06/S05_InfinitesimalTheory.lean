import References.GardinerLakic2000.Ch06.S04_ManifoldStructure
import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.5 The infinitesimal theory

Source `teichmuller.txt`, lines 5827–5956.

* Formula (6.17) (`V = lim (w^{tμ} − z)/t`, l. 5828–5833; cited l. 5947) — `eq6_17`
* Formula (6.18) (`V‴(z) = −(6/π) ∬_ℍ μ(ζ)/(ζ − z)⁴`, l. 5840) — `eq6_18`
* Unlabelled (§6.5, l. 5846: `Φ̇[μ] = lim Φ(tμ)/t = V‴`) — exists: `LiZhongQC.lemma36_2_bers_analytic` (second
  conjunct: the derivative at 0 of t ↦ S(w^{tμ})(z) is LiZhongQC.bersDerivative μ z, which is (6.18))
* Theorem 5 (l. 5848) — `thm6_5`
* Corollary 1 (the reproducing formula (6.19), l. 5858) — `cor6_5_1`
* Definition (`N(G)`, the Beltrami differentials annihilating `A(G)`, l. 5886–5891) — `nSpaceGamma`
* Definition (the projection `P`, l. 5897–5901) — `projectionP`
* Corollary 2 (l. 5893; cited l. 9975), in three parts — `cor6_5_2_a` (`‖P‖ ≤ 3`, a projection onto `B(G)`),
  `cor6_5_2_b` (`ker P = N`), `cor6_5_2_c` (`Z(R) ≅ B(G)`)

Not items (DESIGN §3): the automorphy of `V‴` (l. 5844), the list of the spaces `L∞(G)`, `B(G)`, `A(G)` (Part A §0 and
§6.3). Near miss for Corollary 1: `LiZhongQC.lemma36_2_right_inverse` (the reproducing formula with an unspecified
constant). Near miss for (6.17): `LiZhongQC.ah_first_variation` (`o(‖μ‖)` for normalized plane solutions).

The name `projectionP` avoids `LiZhongQC.bersProjection` (the projection of the Bers fiber space, another notion).

**Conventions.** `w^{tμ}` is `LiZhongQC.normalizedSolution (t • μ)` for `μ ∈ M(ℍ)` (supported in `ℍ`), `t` complex;
`V = LiZhongQC.normalizedCauchyTOn upperHalf μ` (Part A §0); `Φ(μ) = LiZhongQC.bersFunction μ`. In Corollary 2 the
space `B(G)` is on `ℍ` (§6.4), identified with the harmonic Beltrami differentials `ρ⁻² ψ̄ = 4y² ψ̄`, and `Z(R)` is
the space of bounded functionals on `A(G)` (Part A's `IsBoundedFunctionalOn` with the norm `∬_F |φ|`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (BeltramiH BeltramiGamma lowerHalf upperHalf normalizedSolution bersFunction bersDerivative
  normalizedCauchyTOn integrableAutomorphicQD beltramiPairing phiArea IsFundamentalDomainH IsFuchsian)

/-- Helper for (6.17). The second-order expansion `w^{tμ}(w) = w + t V(w) + O(|t|²)`, uniform for `|w| ≤ R`
(`t ↦ w^{tμ}(w)` is holomorphic by Theorem 13.8, bounded by the growth bound `ut2_nb_upper`; `bB_h0_taylor_le`; the
derivative at `0` is `V = normalizedCauchyTOn ℍ μ`, `b36_q_first_var` and `b36_q_ahVar_eq`). -/
theorem gl6_normalizedSolution_taylor (μ : BeltramiH) {R : ℝ} (hR : 0 < R) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℂ, ‖t‖ < δ → ∀ w : ℂ, ‖w‖ ≤ R →
      ‖normalizedSolution (fun ζ => t * μ.1 ζ) w - w - t * normalizedCauchyTOn upperHalf μ.1 w‖ ≤
        C * ‖t‖ ^ 2 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := LiZhongQC.b36_q_small LiZhongQC.b36_q_zero μ
  obtain ⟨hkP, hhol⟩ := LiZhongQC.b36_q_fam_hyps LiZhongQC.b36_q_zero μ hk0 hk1 hb
  have ha : ∀ w, DifferentiableOn ℂ
      (fun t => normalizedSolution (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ t).1 w) (ball 0 r) :=
    LiZhongQC.thm13_8_ahlfors_bers_holomorphic (μ := fun t => (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ t).1)
      (f := fun t => normalizedSolution (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ t).1) isOpen_ball hk0 hk1
      hkP hhol (fun t _ => LiZhongQC.ut_spec _)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ ball (0 : ℂ) r, ∀ w : ℂ, ‖w‖ ≤ R →
      ‖normalizedSolution (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ s).1 w‖ ≤ M :=
    ⟨_, fun s hs w hw => LiZhongQC.UniversalTeichmuller.ut2_nb_upper
      (LiZhongQC.bB_hs_normalizedPlane _ hk0 hk1 (hkP s hs)) hR hw⟩
  refine ⟨8 * M / r ^ 2, r / 2, half_pos hr, fun t ht w hw => ?_⟩
  have h := LiZhongQC.bB_h0_taylor_le hr (ha w) (fun s hs => hM s hs w hw) ht
  have hF0 := LiZhongQC.b36_q_F0 μ hr hk0 hk1 hb
  have hV := LiZhongQC.b36_q_first_var μ hr hk0 hk1 hb w
  have hfam : (fun ζ => t * μ.1 ζ) = (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ t).1 := by
    rw [LiZhongQC.b36_q_fam_val LiZhongQC.b36_q_zero μ hk0 hk1 hb
      (mem_ball_zero_iff.2 (by linarith [norm_nonneg t]))]
    funext ζ
    simp [LiZhongQC.b36_q_zero]
  simp only [zero_add] at h
  rw [hV.deriv, hF0, LiZhongQC.b36_q_ahVar_eq] at h
  rw [hfam]
  exact h

/-- **Formula (6.17)** (§6.5, l. 5828–5833). For `μ ∈ M(ℍ)`, `V(z) = lim_{t → 0} (w^{tμ}(z) − z)/t` exists
uniformly on compact subsets of `ℂ` and `V(z) = −(z(z − 1)/π) ∬_ℍ μ(ζ)/(ζ(ζ − 1)(ζ − z)) dξ dη`. -/
theorem eq6_17 (μ : BeltramiH) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (t : ℂ) (z : ℂ) => (normalizedSolution (fun w => t * μ.1 w) z - z) / t)
      (normalizedCauchyTOn upperHalf μ.1) (𝓝[≠] 0) K := by
  obtain ⟨R, hR0, hKR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun z hz => (mem_closedBall_zero_iff.1 (hR hz)).trans (le_max_left _ _)⟩
  obtain ⟨C, δ, hδ, hT⟩ := gl6_normalizedSolution_taylor μ hR0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hη : 0 < min δ (ε / (|C| + 1)) := lt_min hδ (div_pos hε (by positivity))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hη)] with t ht0 ht z hz
  have htne : t ≠ 0 := ht0
  rw [mem_ball_zero_iff, lt_min_iff] at ht
  have h := hT t ht.1 z (hKR z hz)
  have htp : 0 < ‖t‖ := norm_pos_iff.2 htne
  have heq : normalizedCauchyTOn upperHalf μ.1 z - (normalizedSolution (fun w => t * μ.1 w) z - z) / t =
      -((normalizedSolution (fun w => t * μ.1 w) z - z - t * normalizedCauchyTOn upperHalf μ.1 z) / t) := by
    field_simp
    ring
  rw [dist_eq_norm, heq, norm_neg, norm_div, div_lt_iff₀ htp]
  have h2 : ‖t‖ * (|C| + 1) < ε := (lt_div_iff₀ (by positivity)).1 ht.2
  calc _ ≤ C * ‖t‖ ^ 2 := h
    _ ≤ |C| * ‖t‖ ^ 2 := by gcongr; exact le_abs_self C
    _ < ε * ‖t‖ := by nlinarith [mul_lt_mul_of_pos_right h2 htp, sq_nonneg ‖t‖]

/-- **Formula (6.18)** (§6.5, l. 5840). For `z` in the lower half-plane,
`V‴(z) = −(6/π) ∬_ℍ μ(ζ)/(ζ − z)⁴ dξ dη` (`= LiZhongQC.bersDerivative μ z`). -/
theorem eq6_18 (μ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    iteratedDeriv 3 (normalizedCauchyTOn upperHalf μ.1) z = bersDerivative μ.1 z := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  exact (LiZhongQC.bersDerivative_eq_cauchyT_third μ hz).symm

/-- Helper for Theorem 5 and Theorem 6. `Φ̇[μ] = d/dt Φ(tμ)|₀` pointwise on `𝕃` (`b36_q_part2` with
`V‴ = bersDerivative`, `bersDerivative_eq_cauchyT_third`). -/
theorem gl6_bers_hasDerivAt (μ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    HasDerivAt (fun s : ℂ => bersFunction (fun w => s * μ.1 w) z) (bersDerivative μ.1 z) 0 := by
  have h := LiZhongQC.b36_q_part2 μ hz
  rwa [LiZhongQC.b36_q_ahVar_eq, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    ← LiZhongQC.bersDerivative_eq_cauchyT_third μ hz] at h

/-- **Theorem 5** (§6.5, l. 5848). There is a constant `C` such that `|Φ(tμ)(z) − t Φ̇[μ](z)| ≤ C y⁻² t²` for `|t|`
less than some `δ > 0` (`z = x + iy` in `𝕃`): `Φ̇` is the derivative of `Φ` at `0` for the norm of `B(G)`. -/
theorem thm6_5 (μ : BeltramiH) : ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ lowerHalf,
    ‖bersFunction (fun w => t * μ.1 w) z - t * bersDerivative μ.1 z‖ ≤ C * (z.im ^ 2)⁻¹ * ‖t‖ ^ 2 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := LiZhongQC.b36_q_small LiZhongQC.b36_q_zero μ
  obtain ⟨hkP, hhol⟩ := LiZhongQC.b36_q_fam_hyps LiZhongQC.b36_q_zero μ hk0 hk1 hb
  refine ⟨12 / r ^ 2, r / 2, half_pos hr, fun t ht z hz => ?_⟩
  have hfam : ∀ s ∈ ball (0 : ℂ) r,
      (fun w => s * μ.1 w) = (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ s).1 := by
    intro s hs
    rw [LiZhongQC.b36_q_fam_val LiZhongQC.b36_q_zero μ hk0 hk1 hb hs]
    funext w
    simp [LiZhongQC.b36_q_zero]
  have hbers : ∀ s ∈ ball (0 : ℂ) r, bersFunction (fun w => s * μ.1 w) z =
      LiZhongQC.schwarzian (normalizedSolution (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ s).1) z := by
    intro s hs
    rw [hfam s hs]
    exact indicator_of_mem hz _
  have hgd : DifferentiableOn ℂ (fun s => bersFunction (fun w => s * μ.1 w) z) (ball 0 r) :=
    (LiZhongQC.b36_q_schwarzian_holo isOpen_ball hk0 hk1 hkP hhol hz).congr fun s hs => hbers s hs
  have hy : 0 < z.im ^ 2 := by
    have h : z.im < 0 := hz
    nlinarith
  have hgM : ∀ s ∈ ball (0 : ℂ) r, ‖bersFunction (fun w => s * μ.1 w) z‖ ≤ 3 / 2 * (z.im ^ 2)⁻¹ := by
    intro s hs
    have h := LiZhongQC.bB_sd_kraus_pt (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero μ s) hz
    rw [hbers s hs, le_mul_inv_iff₀ hy]
    exact h
  have hg0 : bersFunction (fun w => (0 : ℂ) * μ.1 w) z = 0 := by
    have e : (fun w => (0 : ℂ) * μ.1 w) = (0 : ℂ → ℂ) := by
      funext w
      simp
    have e1 : bersFunction (0 : ℂ → ℂ) z = LiZhongQC.schwarzian (normalizedSolution 0) z :=
      indicator_of_mem hz _
    rw [e, e1, LiZhongQC.bB_l_normalizedSolution_zero, LiZhongQC.bB_l_schwarzian_id]
  have hgd0 := (gl6_bers_hasDerivAt μ hz).deriv
  have htay := LiZhongQC.bB_h0_taylor_le hr hgd hgM ht
  simp only [zero_add] at htay
  rw [hg0, sub_zero, hgd0] at htay
  calc _ ≤ _ := htay
    _ = 12 / r ^ 2 * (z.im ^ 2)⁻¹ * ‖t‖ ^ 2 := by ring

/-- **Corollary 1** (the reproducing formula (6.19), §6.5, l. 5858). For every `ψ ∈ B(G)` (on `ℍ`) and `z` in the
lower half-plane, `conj ψ(z̄) = (12/π) ∬_ℍ η² conj ψ(ζ)/(ζ − z)⁴ dξ dη`, `ζ = ξ + iη`. -/
theorem cor6_5_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) {z : ℂ} (hz : z ∈ lowerHalf) :
    conj (ψ (conj z)) = (12 / π : ℂ) * ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * conj (ψ ζ) / (ζ - z) ^ 4 := by
  -- `Γ` and the automorphy of `ψ` play no role: the reproducing formula holds for every bounded holomorphic `ψ`
  have _hΓ := hΓ
  obtain ⟨hd, -, hfin⟩ := hψ
  rw [gl6_cuspNorm_half ψ fun _ hw => gl6_density_upperHalf hw] at hfin
  set S : ℝ≥0∞ := ⨆ w ∈ upperHalf, ENNReal.ofReal (‖ψ w‖ * w.im ^ 2) with hS
  have hSfin : S ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by norm_num)] at hfin
    exact lt_irrefl _ hfin
  have hM : ∀ w ∈ upperHalf, ‖ψ w‖ * w.im ^ 2 ≤ S.toReal := fun w hw =>
    (ENNReal.ofReal_le_iff_le_toReal hSfin).1
      (le_iSup₂ (f := fun w (_ : w ∈ upperHalf) => ENNReal.ofReal (‖ψ w‖ * w.im ^ 2)) w hw)
  set φ : ℂ → ℂ := fun u => conj (ψ (conj u)) with hφdef
  have hconjL : ∀ u ∈ lowerHalf, conj u ∈ upperHalf := fun u hu => by
    show 0 < (conj u).im
    rw [conj_im]
    have : u.im < 0 := hu
    linarith
  have hφd : DifferentiableOn ℂ φ lowerHalf := by
    intro u hu
    have h2 := (hd.differentiableAt (LiZhongQC.isOpen_upperHalf.mem_nhds (hconjL u hu))).conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hφM : ∀ w ∈ lowerHalf, ‖φ w‖ * w.im ^ 2 ≤ S.toReal := fun w hw => by
    have h := hM (conj w) (hconjL w hw)
    rw [conj_im, neg_sq] at h
    simpa only [hφdef, Complex.norm_conj] using h
  have h := LiZhongQC.b36_r_reproducing hφd hφM hz
  simp only [hφdef, Complex.conj_conj] at h
  rw [h]
  field_simp

/-- **Definition** (`N(G)`, §6.5, l. 5886–5891). The Beltrami differentials `μ ∈ L∞(G)` with `∬_{ℍ/G} μφ = 0` for
all `φ ∈ A(G)` (the infinitesimally trivial Beltrami differentials of §6.6); the integral is over a fundamental
domain `F`. -/
def nSpaceGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) : Set (ℂ → ℂ) :=
  {μ | μ ∈ beltramiSpaceGamma Γ ∧ ∀ φ ∈ integrableAutomorphicQD Γ F, beltramiPairing F μ φ = 0}

/-- **Definition** (§6.5, l. 5897–5901). The projection `P(μ)(z) = ρ⁻²(z) (3/π) ∬_ℍ μ(ζ)/(ζ − z̄)⁴ dξ dη`, `z ∈ ℍ`,
with `ρ(z) = (2y)⁻¹` (so `ρ⁻² = 4y²`). -/
def projectionP (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)

/-- Helper for Corollary 2 and Theorem 6. `P(μ)(z) = −2 y² Φ̇[μ](z̄)` (`LiZhongQC.bersDerivative`): both are
`∬_ℍ μ(ζ)/(ζ − z̄)⁴` up to the constants `12 y²/π` and `−6/π`. -/
theorem gl6_projectionP_eq (μ : ℂ → ℂ) (z : ℂ) :
    projectionP μ z = -2 * (z.im : ℂ) ^ 2 * bersDerivative μ (conj z) := by
  show 4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4) =
    -2 * (z.im : ℂ) ^ 2 * (-(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)
  ring

/-- Helper for Corollary 2 and Theorem 6. A Beltrami differential `μ ∈ L∞(G)` scaled into `M(G)`: for some
`λ > 0`, `λ 𝟙_ℍ μ` (with `|λμ| ≤ 1/2`) is an element of `M(G)`. -/
theorem gl6_scale {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiSpaceGamma Γ) :
    ∃ (lam : ℝ) (ν : BeltramiGamma Γ), 0 < lam ∧ ν.1.1 = upperHalf.indicator (fun z => (lam : ℂ) * μ z) ∧
      ∀ᵐ z, ‖ν.1.1 z‖ ≤ 1 / 2 := by
  obtain ⟨hΓμ, k, hm, hb⟩ := hμ
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  set lam : ℝ := 1 / (2 * (|k| + 1)) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamk : lam * |k| ≤ 1 / 2 := by
    rw [hlam, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [abs_nonneg k]
  set κ : ℂ → ℂ := upperHalf.indicator fun z => (lam : ℂ) * μ z with hκ
  have hκ0 : ∀ z : ℂ, z.im ≤ 0 → κ z = 0 := fun z hz => by
    rw [hκ]
    exact indicator_of_notMem (show z ∉ upperHalf from not_lt.2 hz) _
  have hκb : ∀ᵐ z, ‖κ z‖ ≤ 1 / 2 := by
    have h1 : ∀ᵐ z, z ∈ upperHalf → ‖μ z‖ ≤ k := (ae_restrict_iff' hU).1 hb
    filter_upwards [h1] with z hz
    by_cases hzU : z ∈ upperHalf
    · simp only [hκ, indicator_of_mem hzU]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
      calc lam * ‖μ z‖ ≤ lam * |k| := by gcongr; exact (hz hzU).trans (le_abs_self k)
        _ ≤ 1 / 2 := hlamk
    · simp only [hκ, indicator_of_notMem hzU, norm_zero]
      norm_num
  have hmem : (∃ k' : ℝ, 0 ≤ k' ∧ k' < 1 ∧ LiZhongQC.IsBeltramiCoeff κ univ k') ∧
      ∀ z : ℂ, z.im ≤ 0 → κ z = 0 := by
    refine ⟨⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩, hκ0⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hU).2 (hm.const_mul _)
    · rw [Measure.restrict_univ]
      exact hκb
  have hcompat : LiZhongQC.IsGammaCompatible Γ κ := by
    intro γ hγ
    filter_upwards [hΓμ γ hγ, ae_restrict_mem hU] with z hz hzU
    have hγz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf :=
      LiZhongQC.h36p_m_mem γ hzU
    simp only [hκ, indicator_of_mem hzU, indicator_of_mem hγz]
    rw [hz]
    ring
  exact ⟨lam, ⟨⟨κ, hmem⟩, hcompat⟩, hlam0, rfl, hκb⟩

/-- Helper for Corollary 2 and Theorem 6. The scaled differential of `gl6_scale` has `Φ̇[ν] = λ Φ̇[μ]` and pairings
`∬_F ν φ = λ ∬_F μ φ` (`F ⊆ ℍ`). -/
theorem gl6_scale_linear {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {μ : ℂ → ℂ} {lam : ℝ} {ν : BeltramiGamma Γ}
    (hν : ν.1.1 = upperHalf.indicator fun z => (lam : ℂ) * μ z) :
    (∀ w, bersDerivative ν.1.1 w = lam * bersDerivative μ w) ∧
      ∀ φ, beltramiPairing F ν.1.1 φ = lam * beltramiPairing F μ φ := by
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  refine ⟨fun w => ?_, fun φ => ?_⟩
  · show -(6 / π : ℂ) * ∫ ζ in upperHalf, ν.1.1 ζ / (ζ - w) ^ 4 =
      (lam : ℂ) * (-(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - w) ^ 4)
    have e : ∫ ζ in upperHalf, ν.1.1 ζ / (ζ - w) ^ 4 = ∫ ζ in upperHalf, (lam : ℂ) * (μ ζ / (ζ - w) ^ 4) :=
      setIntegral_congr_fun hU fun ζ hζ => by
        simp only [hν, indicator_of_mem hζ]
        ring
    rw [e, integral_const_mul]
    ring
  · show ∫ z in F, ν.1.1 z * φ z = (lam : ℂ) * ∫ z in F, μ z * φ z
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hF.2.1 fun z hz => by
      simp only [hν, indicator_of_mem (hF.1 hz)]
      ring

/-- Helper for Corollary 2. `Φ̇[ν]` is holomorphic on `𝕃`: it is `V‴` (`bersDerivative_eq_cauchyT_third`) for the
holomorphic `V = normalizedCauchyTOn ℍ ν` (`b36_p_hasDerivAt_N`). -/
theorem gl6_bersDerivative_differentiableOn (ν : BeltramiH) :
    DifferentiableOn ℂ (bersDerivative ν.1) lowerHalf := by
  obtain ⟨⟨k, hk0, -, hm', hb'⟩, -⟩ := ν.2
  rw [Measure.restrict_univ] at hm' hb'
  have hV : DifferentiableOn ℂ (normalizedCauchyTOn upperHalf ν.1) lowerHalf := by
    intro w hw
    rw [LiZhongQC.b36_p_normalizedCauchyT_eq]
    exact (((LiZhongQC.b36_p_hasDerivAt_N hk0 hm'.restrict (ae_restrict_of_ae hb') hw).2.const_mul
      _).differentiableAt).differentiableWithinAt
  have h3 := ((hV.deriv LiZhongQC.isOpen_lowerHalf).deriv LiZhongQC.isOpen_lowerHalf).deriv
    LiZhongQC.isOpen_lowerHalf
  exact h3.congr fun w hw => LiZhongQC.bersDerivative_eq_cauchyT_third ν hw

/-- Helper for Corollary 2. `Φ̇[ν]` is a quadratic differential for `G` on `𝕃`: `Φ(tν) ∈ Q(G, 𝕃)` for small `t`
(`bersFunctionGamma_mem`), and the automorphy identity passes to the derivative at `t = 0` (`gl6_bers_hasDerivAt`). -/
theorem gl6_bersDerivative_automorphic {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (ν : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {w : ℂ} (hw : w ∈ lowerHalf) :
    bersDerivative ν.1.1 (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w) / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 4 =
      bersDerivative ν.1.1 w := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := LiZhongQC.b36_q_small LiZhongQC.b36_q_zero ν.1
  have hval : ∀ t ∈ ball (0 : ℂ) r,
      (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero ν.1 t).1 = fun z => t * ν.1.1 z := by
    intro t ht
    rw [LiZhongQC.b36_q_fam_val LiZhongQC.b36_q_zero ν.1 hk0 hk1 hb ht]
    funext z
    simp [LiZhongQC.b36_q_zero]
  have hγw : LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w ∈ lowerHalf := LiZhongQC.h36p_d_im_neg γ hw
  have heq : (fun s : ℂ => bersFunction (fun z => s * ν.1.1 z)
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w) / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 4) =ᶠ[𝓝 0]
        fun s => bersFunction (fun z => s * ν.1.1 z) w := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    have hΓt : LiZhongQC.IsGammaCompatible Γ (LiZhongQC.b36_q_fam LiZhongQC.b36_q_zero ν.1 t).1 := by
      rw [hval t ht]
      intro δ hδ
      filter_upwards [ν.2 δ hδ] with z hz
      show t * ν.1.1 z = t * ν.1.1 _ * _
      rw [hz]
      ring
    have hA' := (LiZhongQC.bersFunctionGamma_mem hΓ ⟨_, hΓt⟩).1
    have h := hA'.2.2 γ hγ w hw
    show bersFunction (fun z => t * ν.1.1 z) (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w) /
      ((γ 1 0 : ℂ) * w + γ 1 1) ^ 4 = bersFunction (fun z => t * ν.1.1 z) w
    rw [← hval t ht]
    exact h
  have h1 := (gl6_bers_hasDerivAt ν.1 hγw).div_const (((γ 1 0 : ℂ) * w + γ 1 1) ^ 4)
  have h2 := (gl6_bers_hasDerivAt ν.1 hw).congr_of_eventuallyEq heq
  exact h1.unique h2

/-- Helper for Corollary 2. `|P(μ)(z)| ≤ 3 ‖μ‖∞` at every `z ∈ ℍ`: `|P μ(z)| ≤ (12 y²/π) ‖μ‖∞ ∬_ℍ |ζ − z̄|⁻⁴ dA` and
the kernel area `∬_ℍ |ζ − a|⁻⁴ = π/(4 (Im a)²)` (`h36p_c_kernel_area`). -/
theorem gl6_projectionP_enorm_le {μ : ℂ → ℂ} {M : ℝ≥0∞}
    (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ ζ‖ₑ ≤ M) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖projectionP μ z‖ₑ ≤ 3 * M := by
  have hz' : 0 < z.im := hz
  have hy0 : z.im ≠ 0 := hz'.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have ha : conj z ∈ lowerHalf := by
    show (conj z).im < 0
    rw [conj_im]
    linarith
  have hker := LiZhongQC.h36p_c_kernel_area ha
  rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, conj_im, neg_sq] at hker
  have hmeas : Measurable fun ζ : ℂ => ENNReal.ofReal (‖ζ - conj z‖⁻¹ ^ 4) := by fun_prop
  have hI : ‖∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4‖ₑ ≤
      M * ((NNReal.pi : ℝ≥0∞) * ENNReal.ofReal ((4 * z.im ^ 2)⁻¹)) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← hker, ← lintegral_const_mul _ hmeas]
    refine lintegral_mono_ae ?_
    filter_upwards [hb] with ζ hζ
    rw [← ofReal_norm, norm_div, norm_pow, div_eq_mul_inv, ← inv_pow, ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm]
    exact mul_le_mul_of_nonneg_right hζ zero_le
  have e : projectionP μ z = (4 * (z.im : ℂ) ^ 2 * (3 / π : ℂ)) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4 := by
    show 4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4) = _
    ring
  have hc : ‖(4 * (z.im : ℂ) ^ 2 * (3 / π : ℂ))‖ₑ = ENNReal.ofReal (12 * z.im ^ 2 / π) := by
    rw [← ofReal_norm]
    congr 1
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  rw [e, enorm_mul, hc]
  calc _ ≤ ENNReal.ofReal (12 * z.im ^ 2 / π) * (M * ((NNReal.pi : ℝ≥0∞) * ENNReal.ofReal ((4 * z.im ^ 2)⁻¹))) :=
        mul_le_mul_of_nonneg_left hI zero_le
    _ = 3 * M := by
      rw [show (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π by rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]]
      rw [mul_comm M, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [show 12 * z.im ^ 2 / π * π * (4 * z.im ^ 2)⁻¹ = 3 by field_simp; ring, ENNReal.ofReal_ofNat]

/-- **Corollary 2** (§6.5, l. 5893), first part. `P` maps `L∞(G)` into the harmonic Beltrami differentials
`4y² ψ̄`, `ψ ∈ B(G)`, with `‖P μ‖∞ ≤ 3 ‖μ‖∞`, and it is the identity on them: a projection onto `B(G)` with
`‖P‖ ≤ 3`. -/
theorem cor6_5_2_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    (∀ μ ∈ beltramiSpaceGamma Γ,
      eLpNorm (projectionP μ) ⊤ (volume.restrict upperHalf) ≤ 3 * eLpNorm μ ⊤ (volume.restrict upperHalf) ∧
      ∃ ψ ∈ boundedCuspForms Γ upperHalf, ∀ z ∈ upperHalf, projectionP μ z = 4 * (z.im : ℂ) ^ 2 * conj (ψ z)) ∧
    ∀ ψ ∈ boundedCuspForms Γ upperHalf, ∀ z ∈ upperHalf,
      projectionP (upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) z =
        4 * (z.im : ℂ) ^ 2 * conj (ψ z) := by
  have hU : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  have hconj : ∀ z ∈ upperHalf, conj z ∈ lowerHalf := fun z hz => by
    show (conj z).im < 0
    rw [conj_im]
    have : 0 < z.im := hz
    linarith
  refine ⟨fun μ hμ => ?_, fun ψ hψ z hz => ?_⟩
  · obtain ⟨lam, ν, hlam, hν, -⟩ := gl6_scale hμ
    have hlamne : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam.ne'
    have hD : ∀ w, bersDerivative μ w = (lam : ℂ)⁻¹ * bersDerivative ν.1.1 w := by
      intro w
      have e : ∫ ζ in upperHalf, ν.1.1 ζ / (ζ - w) ^ 4 =
          ∫ ζ in upperHalf, (lam : ℂ) * (μ ζ / (ζ - w) ^ 4) :=
        setIntegral_congr_fun hU fun ζ hζ => by
          simp only [hν, indicator_of_mem hζ]
          ring
      show -(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - w) ^ 4 =
        (lam : ℂ)⁻¹ * (-(6 / π : ℂ) * ∫ ζ in upperHalf, ν.1.1 ζ / (ζ - w) ^ 4)
      rw [e, integral_const_mul]
      have hl : (lam : ℂ)⁻¹ * (lam : ℂ) = 1 := inv_mul_cancel₀ hlamne
      linear_combination (-(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - w) ^ 4) * hl.symm
    obtain ⟨-, k, hm, hb⟩ := hμ
    have hbk : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖μ ζ‖ₑ ≤ ENNReal.ofReal (max k 0) := by
      filter_upwards [hb] with ζ h
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (h.trans (le_max_left _ _))
    -- the cusp form `ψ(z) = conj((3/π) ∬_ℍ μ(ζ)/(ζ − z̄)⁴) = conj(G(z̄))`, `G = −(1/2) λ⁻¹ Φ̇[ν]`
    set G : ℂ → ℂ := fun w => -(1 / 2 : ℂ) * ((lam : ℂ)⁻¹ * bersDerivative ν.1.1 w) with hG
    have hψG : (fun z => conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)) =
        fun z => conj (G (conj z)) := by
      funext z
      congr 1
      show (3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4 =
        -(1 / 2 : ℂ) * ((lam : ℂ)⁻¹ * bersDerivative ν.1.1 (conj z))
      rw [← hD]
      show _ = -(1 / 2 : ℂ) * (-(6 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)
      ring
    have hGd : DifferentiableOn ℂ G lowerHalf :=
      ((gl6_bersDerivative_differentiableOn ν.1).const_mul _).const_mul _
    refine ⟨?_, fun z => conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4), ⟨?_, ?_, ?_⟩,
      fun z hz => ?_⟩
    · -- `‖P μ‖∞ ≤ 3 ‖μ‖∞`
      have hPc : ContinuousOn (projectionP μ) upperHalf := by
        have he : EqOn (projectionP μ)
            (fun z => -2 * (z.im : ℂ) ^ 2 * ((lam : ℂ)⁻¹ * bersDerivative ν.1.1 (conj z))) upperHalf :=
          fun z _ => by rw [gl6_projectionP_eq, hD]
        refine ContinuousOn.congr ?_ he
        have hc : ContinuousOn (fun z => bersDerivative ν.1.1 (conj z)) upperHalf :=
          (gl6_bersDerivative_differentiableOn ν.1).continuousOn.comp Complex.continuous_conj.continuousOn
            fun z hz => hconj z hz
        exact ((continuous_const.mul ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2)).continuousOn).mul
          (continuousOn_const.mul hc)
      rw [eLpNorm_exponent_top (hPc.aestronglyMeasurable hU), eLpNorm_exponent_top hm]
      exact essSup_le_of_ae_le _ (by
        filter_upwards [ae_restrict_mem hU] with z hz
        exact gl6_projectionP_enorm_le ae_le_eLpNormEssSup hz)
    · -- holomorphy
      rw [hψG]
      intro z hz
      have h2 := (hGd.differentiableAt (LiZhongQC.isOpen_lowerHalf.mem_nhds (hconj z hz))).conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    · -- automorphy
      rw [hψG]
      intro γ hγ z hz
      have hdet : 0 < γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by
        have h := γ.2
        rw [Matrix.det_fin_two] at h
        rw [h]
        exact one_pos
      have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.realMobius_den_ne_zero hdet hz
      have hcγ : conj ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) =
          LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (conj z) := by
        simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal]
        rfl
      have hA := gl6_bersDerivative_automorphic hΓ ν hγ (hconj z hz)
      have hden' : (γ 1 0 : ℂ) * conj z + γ 1 1 ≠ 0 := by
        intro h0
        apply hden
        have h1 := congrArg conj h0
        simpa only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj, map_zero] using h1
      rw [div_eq_iff (pow_ne_zero 4 hden')] at hA
      show conj (G (conj ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)))) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        conj (G (conj z))
      rw [hcγ, div_eq_iff (pow_ne_zero 4 hden)]
      simp only [hG, hA, map_mul, map_neg, map_div₀, map_one, map_ofNat, map_inv₀, Complex.conj_ofReal, map_pow,
        map_add, Complex.conj_conj]
      ring
    · -- finite cusp norm
      rw [gl6_cuspNorm_half _ fun _ hw => gl6_density_upperHalf hw]
      refine ENNReal.mul_lt_top (by norm_num) (lt_of_le_of_lt (iSup₂_le fun z hz => ?_)
        (ENNReal.ofReal_lt_top (r := 3 * max k 0)))
      have hP := gl6_projectionP_enorm_le hbk hz
      rw [← ofReal_norm, show (3 : ℝ≥0∞) * ENNReal.ofReal (max k 0) = ENNReal.ofReal (3 * max k 0) by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat],
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hP
      have hPn : ‖projectionP μ z‖ = 4 * z.im ^ 2 *
          ‖conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)‖ := by
        show ‖4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)‖ = _
        rw [Complex.norm_conj, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
          Complex.norm_ofNat]
      apply ENNReal.ofReal_le_ofReal
      show ‖conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)‖ * z.im ^ 2 ≤ 3 * max k 0
      nlinarith [le_max_right k 0,
        norm_nonneg (conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4)), sq_nonneg z.im]
    · -- `P μ = 4 y² ψ̄`
      show 4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4) =
        4 * (z.im : ℂ) ^ 2 * conj (conj ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4))
      rw [Complex.conj_conj]
  · -- `P` is the identity on `4 y² ψ̄`: the reproducing formula (Corollary 1) at `z̄`
    have h := cor6_5_1 hΓ hψ (hconj z hz)
    rw [Complex.conj_conj] at h
    have e : ∫ ζ in upperHalf, upperHalf.indicator (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) ζ /
        (ζ - conj z) ^ 4 = 4 * ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * conj (ψ ζ) / (ζ - conj z) ^ 4 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun hU fun ζ hζ => by
        simp only [indicator_of_mem hζ]
        ring
    show 4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf,
      upperHalf.indicator (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) ζ / (ζ - conj z) ^ 4) =
        4 * (z.im : ℂ) ^ 2 * conj (ψ z)
    rw [e, h]
    ring

/-- **Corollary 2** (§6.5, l. 5893), second part. `ker P = N`. -/
theorem cor6_5_2_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiSpaceGamma Γ) :
    (∀ z ∈ upperHalf, projectionP μ z = 0) ↔ μ ∈ nSpaceGamma Γ F := by
  -- `hfree` is not needed: the kernel identification `lemma36_2_kernel_orthogonal` holds for every Fuchsian group
  have _hfree := hfree
  obtain ⟨lam, ν, hlam, hν, -⟩ := gl6_scale hμ
  obtain ⟨hD, hP⟩ := gl6_scale_linear hF hν
  have hK := LiZhongQC.lemma36_2_kernel_orthogonal hΓ hF ν
  have hlamne : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hlam.ne'
  have hc2 : ∀ w : ℂ, w.im ≠ 0 → -2 * (w.im : ℂ) ^ 2 ≠ 0 := fun w hw =>
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (ofReal_ne_zero.2 hw))
  constructor
  · intro h
    refine ⟨hμ, fun φ hφ => ?_⟩
    have h1 : LiZhongQC.IsLocallyTrivialBeltrami ν.1.1 := by
      intro w hw
      have hw' : w.im < 0 := hw
      have hcw : conj w ∈ upperHalf := by
        show 0 < (conj w).im
        rw [conj_im]
        linarith
      have h2 := h (conj w) hcw
      rw [gl6_projectionP_eq, conj_conj] at h2
      have h3 : bersDerivative μ w = 0 :=
        (mul_eq_zero.1 h2).resolve_left (hc2 (conj w) (by rw [conj_im]; exact neg_ne_zero.2 hw'.ne))
      rw [hD, h3, mul_zero]
    have h4 := hK.1 h1 φ hφ
    rw [hP] at h4
    exact (mul_eq_zero.1 h4).resolve_left hlamne
  · rintro ⟨-, h⟩ z hz
    have hz' : 0 < z.im := hz
    have h1 := hK.2 fun φ hφ => by rw [hP, h φ hφ, mul_zero]
    have hcz : conj z ∈ lowerHalf := by
      show (conj z).im < 0
      rw [conj_im]
      linarith
    have h2 := h1 (conj z) hcz
    rw [hD] at h2
    rw [gl6_projectionP_eq, (mul_eq_zero.1 h2).resolve_left hlamne, mul_zero]

/-- Helper for `cor6_5_2_c` (§6.5): for a bounded measurable `μ` on `ℍ` and `z ∈ ℍ`, the integrand `μ(ζ)/(ζ − z̄)⁴` of
`P μ (z)` is integrable on `ℍ` (kernel area `LiZhongQC.h36p_c_kernel_area`). -/
theorem gl6_bd_kernel_int {μ : ℂ → ℂ} {k : ℝ} (hμ : LiZhongQC.IsBeltramiCoeff μ upperHalf k) {z : ℂ}
    (hz : z ∈ upperHalf) : IntegrableOn (fun ζ => μ ζ / (ζ - conj z) ^ 4) upperHalf := by
  obtain ⟨hm, hb⟩ := hμ
  have hz' : 0 < z.im := hz
  have ha : conj z ∈ lowerHalf := by
    show (conj z).im < 0
    rw [conj_im]
    linarith
  have hker := LiZhongQC.h36p_c_kernel_area ha
  have hmeas : Measurable fun ζ : ℂ => ENNReal.ofReal (‖ζ - conj z‖⁻¹ ^ 4) := by fun_prop
  have hm' : AEStronglyMeasurable (fun ζ => μ ζ / (ζ - conj z) ^ 4) (volume.restrict upperHalf) := by
    have h1 : Measurable fun ζ : ℂ => ((ζ - conj z) ^ 4)⁻¹ := by fun_prop
    have h2 : AEStronglyMeasurable (fun ζ => μ ζ * ((ζ - conj z) ^ 4)⁻¹) (volume.restrict upperHalf) :=
      hm.mul h1.aestronglyMeasurable
    simpa only [div_eq_mul_inv] using h2
  refine ⟨hm', ?_⟩
  show ∫⁻ ζ in upperHalf, ‖μ ζ / (ζ - conj z) ^ 4‖ₑ < ⊤
  calc ∫⁻ ζ in upperHalf, ‖μ ζ / (ζ - conj z) ^ 4‖ₑ
      ≤ ∫⁻ ζ in upperHalf, ENNReal.ofReal (max k 0) * ENNReal.ofReal (‖ζ - conj z‖⁻¹ ^ 4) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hb] with ζ hζ
        rw [← ofReal_norm, norm_div, norm_pow, div_eq_mul_inv, ← inv_pow, ENNReal.ofReal_mul (norm_nonneg _)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hζ.trans (le_max_left _ _))) le_rfl
    _ = ENNReal.ofReal (max k 0) * ∫⁻ ζ in upperHalf, ENNReal.ofReal (‖ζ - conj z‖⁻¹ ^ 4) :=
        lintegral_const_mul _ hmeas
    _ < ⊤ := by
        rw [hker]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top)

/-- Helper for `cor6_5_2_c` (§6.5): `P` is additive on bounded measurable Beltrami differentials on `ℍ`. -/
theorem gl6_bd_P_sub {μ ν : ℂ → ℂ} {k k' : ℝ} (hμ : LiZhongQC.IsBeltramiCoeff μ upperHalf k)
    (hν : LiZhongQC.IsBeltramiCoeff ν upperHalf k') {z : ℂ} (hz : z ∈ upperHalf) :
    projectionP (μ - ν) z = projectionP μ z - projectionP ν z := by
  have e : ∫ ζ in upperHalf, (μ - ν) ζ / (ζ - conj z) ^ 4 =
      (∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4) - ∫ ζ in upperHalf, ν ζ / (ζ - conj z) ^ 4 := by
    rw [← integral_sub (gl6_bd_kernel_int hμ hz) (gl6_bd_kernel_int hν hz)]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [Pi.sub_apply, sub_div]
  show 4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, (μ - ν) ζ / (ζ - conj z) ^ 4) =
    4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, μ ζ / (ζ - conj z) ^ 4) -
      4 * (z.im : ℂ) ^ 2 * ((3 / π : ℂ) * ∫ ζ in upperHalf, ν ζ / (ζ - conj z) ^ 4)
  rw [e]
  ring

/-- Helper for `cor6_5_2_c` (§6.5): `L∞(G)` is closed under subtraction. -/
theorem gl6_bd_bsub {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {μ ν : ℂ → ℂ}
    (hμ : μ ∈ beltramiSpaceGamma Γ) (hν : ν ∈ beltramiSpaceGamma Γ) : μ - ν ∈ beltramiSpaceGamma Γ := by
  obtain ⟨hcμ, k, hmμ, hbμ⟩ := hμ
  obtain ⟨hcν, k', hmν, hbν⟩ := hν
  refine ⟨fun γ hγ => ?_, k + k', hmμ.sub hmν, ?_⟩
  · filter_upwards [hcμ γ hγ, hcν γ hγ] with z h1 h2
    simp only [Pi.sub_apply]
    rw [h1, h2]
    ring
  · filter_upwards [hbμ, hbν] with z h1 h2
    simp only [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- Helper for `cor6_5_2_c` (§6.5): `B(G)` is closed under subtraction (`‖ψ − ψ'‖_B ≤ ‖ψ‖_B + ‖ψ'‖_B`). -/
theorem gl6_bd_sub {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ψ ψ' : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) (hψ' : ψ' ∈ boundedCuspForms Γ upperHalf) :
    ψ - ψ' ∈ boundedCuspForms Γ upperHalf := by
  obtain ⟨hd, ha, hn⟩ := hψ
  obtain ⟨hd', ha', hn'⟩ := hψ'
  have hc : ∀ φ : ℂ → ℂ, cuspNorm upperHalf φ = 4 * ⨆ z ∈ upperHalf, ENNReal.ofReal (‖φ z‖ * z.im ^ 2) :=
    fun φ => gl6_cuspNorm_half φ fun _ hw => gl6_density_upperHalf hw
  refine ⟨hd.sub hd', fun γ hγ z hz => ?_, ?_⟩
  · simp only [Pi.sub_apply]
    rw [sub_div, ha γ hγ z hz, ha' γ hγ z hz]
  · refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.2 ⟨hn, hn'⟩)
    rw [hc, hc ψ, hc ψ', ← mul_add]
    refine mul_le_mul' le_rfl (iSup₂_le fun z hz => ?_)
    have h1 : ENNReal.ofReal (‖(ψ - ψ') z‖ * z.im ^ 2) ≤
        ENNReal.ofReal (‖ψ z‖ * z.im ^ 2) + ENNReal.ofReal (‖ψ' z‖ * z.im ^ 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := norm_sub_le (ψ z) (ψ' z)
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg z.im]
    refine h1.trans (add_le_add ?_ ?_)
    · exact le_iSup₂ (f := fun z (_ : z ∈ upperHalf) => ENNReal.ofReal (‖ψ z‖ * z.im ^ 2)) z hz
    · exact le_iSup₂ (f := fun z (_ : z ∈ upperHalf) => ENNReal.ofReal (‖ψ' z‖ * z.im ^ 2)) z hz

/-- Helper for `cor6_5_2_c` (§6.5): `μ φ` is integrable on `F` for `μ ∈ L∞(G)` and `φ ∈ A(G)`. -/
theorem gl6_bd_pair_int {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {μ φ : ℂ → ℂ} (hμ : μ ∈ beltramiSpaceGamma Γ)
    (hφ : φ ∈ integrableAutomorphicQD Γ F) : IntegrableOn (fun z => μ z * φ z) F := by
  have hFH : F ⊆ upperHalf := hF.1
  obtain ⟨-, k, hm, hb⟩ := hμ
  exact (LiZhongQC.h36p_b_integrableOn_A hFH hF.2.1 hφ).bdd_mul (hm.mono_measure (Measure.restrict_mono hFH le_rfl))
    (ae_restrict_of_ae_restrict_of_subset hFH hb)

/-- Helper for `cor6_5_2_c` (§6.5): for `ψ ∈ B(G)` the harmonic Beltrami differential `4y²ψ̄` (extended by `0` off
`ℍ`) lies in `L∞(G)`, with `‖4y²ψ̄‖∞ ≤ ‖ψ‖_B` (`ρ⁻² = 4y²` on `ℍ`, `gl6_density_upperHalf`). -/
theorem gl6_bd_mem {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) :
    upperHalf.indicator (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) ∈ beltramiSpaceGamma Γ ∧
      eLpNorm (upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) ⊤ (volume.restrict upperHalf) ≤
        cuspNorm upperHalf ψ := by
  obtain ⟨hd, ha, hn⟩ := hψ
  have hH : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  set κ : ℂ → ℂ := upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w) with hκ
  have hc := gl6_cuspNorm_half ψ fun _ hw => gl6_density_upperHalf hw
  -- `|κ| = 4y²|ψ| = |ψ| ρ⁻² ≤ ‖ψ‖_B` on `ℍ`
  have hpt : ∀ z ∈ upperHalf, ‖κ z‖ₑ ≤ cuspNorm upperHalf ψ := by
    intro z hz
    have e : ‖4 * (z.im : ℂ) ^ 2 * conj (ψ z)‖ = 4 * (‖ψ z‖ * z.im ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_conj,
        Complex.norm_ofNat]
      ring
    rw [hc, hκ, indicator_of_mem hz, ← ofReal_norm, e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact mul_le_mul' le_rfl (le_iSup₂ (f := fun z (_ : z ∈ upperHalf) => ENNReal.ofReal (‖ψ z‖ * z.im ^ 2)) z hz)
  have hcont : ContinuousOn (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) upperHalf :=
    (continuousOn_const.mul ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn).mul
      (Complex.continuous_conj.comp_continuousOn hd.continuousOn)
  have hm : AEStronglyMeasurable κ (volume.restrict upperHalf) :=
    (hcont.aestronglyMeasurable hH).congr ((ae_restrict_iff' hH).2 (ae_of_all _ fun z hz => by
      rw [hκ, indicator_of_mem hz]))
  have hb : ∀ᵐ z ∂(volume.restrict upperHalf), ‖κ z‖ ≤ (cuspNorm upperHalf ψ).toReal := by
    filter_upwards [ae_restrict_mem hH] with z hz
    have h := hpt z hz
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hn.ne).1 h
  refine ⟨⟨fun γ hγ => ?_, _, hm, hb⟩, ?_⟩
  · -- Γ-compatibility: `Im γz = Im z/|j|²` and `ψ(γz) = ψ(z) j⁴`
    filter_upwards [ae_restrict_mem hH] with z hz
    have hz' : 0 < z.im := hz
    have hγz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
    have hj : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.k24_d_den_ne_zero (LiZhongQC.b33_d_det γ) hz'.ne'
    have hjc : conj ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := (map_ne_zero _).2 hj
    have him : (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)).im =
        z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := gl2_fd_im_m γ hz
    have hY : ((((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)).im : ℂ) =
        (z.im : ℂ) / (((γ 1 0 : ℂ) * z + γ 1 1) * conj ((γ 1 0 : ℂ) * z + γ 1 1)) := by
      rw [him, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hA := ha γ hγ z hz
    rw [div_eq_iff (pow_ne_zero 4 hj)] at hA
    show κ z = κ (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))
    rw [hκ, indicator_of_mem hz, indicator_of_mem hγz, hY, hA, map_mul, map_pow, map_pow]
    field_simp
  · rw [eLpNorm_exponent_top hm, eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_mem hH] with z hz
    exact hpt z hz

/-- Helper for `cor6_5_2_c` (§6.5): conversely `‖ψ‖_B ≤ ‖4y²ψ̄‖∞`, since a continuous function on the open set `ℍ` is
bounded at every point by its essential supremum. -/
theorem gl6_bd_cusp_le {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) :
    cuspNorm upperHalf ψ ≤
      eLpNorm (upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) ⊤ (volume.restrict upperHalf) := by
  obtain ⟨hd, -, -⟩ := hψ
  have hH : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  set κ : ℂ → ℂ := upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w) with hκ
  have hcont : ContinuousOn (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) upperHalf :=
    (continuousOn_const.mul ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn).mul
      (Complex.continuous_conj.comp_continuousOn hd.continuousOn)
  have hm : AEStronglyMeasurable κ (volume.restrict upperHalf) :=
    (hcont.aestronglyMeasurable hH).congr ((ae_restrict_iff' hH).2 (ae_of_all _ fun z hz => by
      rw [hκ, indicator_of_mem hz]))
  set E := eLpNormEssSup κ (volume.restrict upperHalf) with hE
  rw [gl6_cuspNorm_half ψ fun _ hw => gl6_density_upperHalf hw, eLpNorm_exponent_top hm, ← hE, ENNReal.mul_iSup]
  refine iSup_le fun z => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hz => ?_
  -- `4y²|ψ(z)| = |κ(z)|`, and a continuous function on the open `ℍ` is bounded by its essential supremum
  have e : 4 * ENNReal.ofReal (‖ψ z‖ * z.im ^ 2) = ‖4 * (z.im : ℂ) ^ 2 * conj (ψ z)‖ₑ := by
    rw [← ofReal_norm, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.norm_conj, Complex.norm_ofNat, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [e]
  by_contra hlt
  push Not at hlt
  set U := upperHalf ∩ (fun w => ‖4 * (w.im : ℂ) ^ 2 * conj (ψ w)‖ₑ) ⁻¹' Ioi E with hU
  have hUo : IsOpen U := (continuous_enorm.comp_continuousOn hcont).isOpen_inter_preimage
    LiZhongQC.isOpen_upperHalf isOpen_Ioi
  have hpos : 0 < volume U := hUo.measure_pos volume ⟨z, hz, hlt⟩
  have hae : ∀ᵐ w ∂(volume.restrict upperHalf), ‖κ w‖ₑ ≤ E := ae_le_eLpNormEssSup
  rw [ae_restrict_iff' hH] at hae
  have hnull : volume U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with w hw hwU
    have h := hw hwU.1
    rw [hκ, indicator_of_mem hwU.1] at h
    exact absurd hwU.2 (not_lt.2 h)
  exact hpos.ne' hnull

/-- Helper for `cor6_5_2_c` (§6.5): extending `ψ ∈ B(G)` by `0` off `ℍ` stays in `B(G)` with the same norm. -/
theorem gl6_bd_indicator {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) :
    upperHalf.indicator ψ ∈ boundedCuspForms Γ upperHalf ∧
      cuspNorm upperHalf (upperHalf.indicator ψ) = cuspNorm upperHalf ψ := by
  obtain ⟨hd, ha, hn⟩ := hψ
  have hc : ∀ φ : ℂ → ℂ, cuspNorm upperHalf φ = 4 * ⨆ z ∈ upperHalf, ENNReal.ofReal (‖φ z‖ * z.im ^ 2) :=
    fun φ => gl6_cuspNorm_half φ fun _ hw => gl6_density_upperHalf hw
  have heq : cuspNorm upperHalf (upperHalf.indicator ψ) = cuspNorm upperHalf ψ := by
    rw [hc, hc ψ]
    congr 1
    refine iSup_congr fun z => iSup_congr fun hz => ?_
    rw [indicator_of_mem hz]
  refine ⟨⟨hd.congr fun z hz => indicator_of_mem hz ψ, fun γ hγ z hz => ?_, heq ▸ hn⟩, heq⟩
  have hγz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
  rw [indicator_of_mem hγz, indicator_of_mem hz]
  exact ha γ hγ z hz

/-- Helper for `cor6_5_2_c` (§6.5): for `ψ ∈ B(G)` and `φ ∈ A(G)`, `4y²ψ̄ φ` is integrable on `F`. -/
theorem gl6_bd_harm_int {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {ψ φ : ℂ → ℂ} (hψ : ψ ∈ boundedCuspForms Γ upperHalf)
    (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    IntegrableOn (fun z => 4 * (z.im : ℂ) ^ 2 * conj (ψ z) * φ z) F := by
  have hFH : F ⊆ upperHalf := hF.1
  have h := gl6_bd_pair_int hF (gl6_bd_mem hψ).1 hφ
  refine h.congr_fun (fun z hz => ?_) hF.2.1
  simp only [indicator_of_mem (hFH hz)]

/-- Helper for `cor6_5_2_c` (§6.5): if `P μ = 4y²ψ̄` on `ℍ` (`μ ∈ L∞(G)`, `ψ ∈ B(G)`), then `μ` and `4y²ψ̄` induce the
same functional on `A(G)`: `μ − 4y²ψ̄` is killed by `P` (linearity of `P` and `cor6_5_2_a`), hence lies in
`N = ker P` (`cor6_5_2_b`). -/
theorem gl6_bd_repr {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {μ ψ : ℂ → ℂ}
    (hμ : μ ∈ beltramiSpaceGamma Γ) (hψ : ψ ∈ boundedCuspForms Γ upperHalf)
    (hP : ∀ z ∈ upperHalf, projectionP μ z = 4 * (z.im : ℂ) ^ 2 * conj (ψ z)) :
    ∀ φ ∈ integrableAutomorphicQD Γ F,
      beltramiPairing F μ φ = beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) φ := by
  intro φ hφ
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hκ := (gl6_bd_mem hψ).1
  set κ : ℂ → ℂ := upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w) with hκdef
  -- `P(μ − κ) = Pμ − Pκ = 4y²ψ̄ − 4y²ψ̄ = 0`, so `μ − κ ∈ N` (Corollary 2 (b))
  obtain ⟨k, hμk⟩ := hμ.2
  obtain ⟨k', hκk⟩ := hκ.2
  have hP0 : ∀ z ∈ upperHalf, projectionP (μ - κ) z = 0 := by
    intro z hz
    rw [gl6_bd_P_sub hμk hκk hz, hP z hz, (cor6_5_2_a hΓ).2 ψ hψ z hz, sub_self]
  have hN := (cor6_5_2_b hΓ hfree hF (gl6_bd_bsub hμ hκ)).1 hP0
  have h0 := hN.2 φ hφ
  have e : beltramiPairing F (μ - κ) φ = beltramiPairing F μ φ - beltramiPairing F κ φ := by
    show ∫ z in F, (μ - κ) z * φ z = (∫ z in F, μ z * φ z) - ∫ z in F, κ z * φ z
    rw [← integral_sub (gl6_bd_pair_int hF hμ hφ) (gl6_bd_pair_int hF hκ hφ)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have e2 : beltramiPairing F κ φ = beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) φ := by
    show ∫ z in F, κ z * φ z = ∫ z in F, 4 * (z.im : ℂ) ^ 2 * conj (ψ z) * φ z
    exact setIntegral_congr_fun hFm fun z hz => by simp only [hκdef, indicator_of_mem (hFH hz)]
  rw [e] at h0
  rw [← e2]
  exact sub_eq_zero.1 h0

/-- Helper for `cor6_5_2_c` (§6.5): two `ψ, ψ' ∈ B(G)` whose harmonic differentials `4y²ψ̄`, `4y²ψ̄'` induce the same
functional on `A(G)` coincide on `ℍ`: the difference `4y²(ψ − ψ')‾` is in `N = ker P` (`cor6_5_2_b`) and fixed by
`P` (`cor6_5_2_a`), hence `0`. -/
theorem gl6_bd_unique {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {ψ ψ' : ℂ → ℂ}
    (hψ : ψ ∈ boundedCuspForms Γ upperHalf) (hψ' : ψ' ∈ boundedCuspForms Γ upperHalf)
    (heq : ∀ φ ∈ integrableAutomorphicQD Γ F,
      beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) φ =
        beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ' w)) φ) :
    EqOn ψ ψ' upperHalf := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  have hd := gl6_bd_sub hψ hψ'
  have hκ := (gl6_bd_mem hd).1
  set κ : ℂ → ℂ := upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj ((ψ - ψ') w) with hκdef
  -- `κ = 4y²(ψ − ψ')‾` annihilates `A(G)`, so `P κ = 0`; but `P κ = κ`
  have hN : κ ∈ nSpaceGamma Γ F := by
    refine ⟨hκ, fun φ hφ => ?_⟩
    have h1 := heq φ hφ
    show ∫ z in F, κ z * φ z = 0
    have e : ∫ z in F, κ z * φ z = (∫ z in F, 4 * (z.im : ℂ) ^ 2 * conj (ψ z) * φ z) -
        ∫ z in F, 4 * (z.im : ℂ) ^ 2 * conj (ψ' z) * φ z := by
      rw [← integral_sub (gl6_bd_harm_int hF hψ hφ) (gl6_bd_harm_int hF hψ' hφ)]
      refine setIntegral_congr_fun hFm fun z hz => ?_
      simp only [hκdef, indicator_of_mem (hFH hz), Pi.sub_apply, map_sub]
      ring
    rw [e]
    exact sub_eq_zero.2 h1
  have hP0 := (cor6_5_2_b hΓ hfree hF hκ).2 hN
  intro z hz
  have h2 := (cor6_5_2_a hΓ).2 (ψ - ψ') hd z hz
  rw [hP0 z hz] at h2
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hz)
  have h3 : conj ((ψ - ψ') z) = 0 := by
    rcases mul_eq_zero.1 h2.symm with h | h
    · exact absurd h (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    · exact h
  rw [map_eq_zero, Pi.sub_apply, sub_eq_zero] at h3
  exact h3

/-- **Corollary 2** (§6.5, l. 5893), third part. `P` induces an isomorphism of `Z(R) ≅ A(R)*` onto `B(G)`
(`R = ℍ/G`): every bounded functional `V` on `A(G)` is `φ ↦ ∬_F 4y² ψ̄ φ` for exactly one `ψ ∈ B(G)`, with
`‖ψ‖_B` and `‖V‖` comparable. -/
theorem cor6_5_2_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∃ C : ℝ, ∀ V : (ℂ → ℂ) → ℂ,
      IsBoundedFunctionalOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V →
      ∃! ψ, ψ ∈ boundedCuspForms Γ upperHalf ∧ (∀ z ∉ upperHalf, ψ z = 0) ∧
        (∀ φ ∈ integrableAutomorphicQD Γ F,
          V φ = beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) φ) ∧
        (cuspNorm upperHalf ψ).toReal ≤ C * dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V ∧
        dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V ≤ C * (cuspNorm upperHalf ψ).toReal := by
  -- the representative `μ ∈ L∞(G)` of `V` (`para3_1_dual_gamma`), projected by `P` onto `B(G)` (`cor6_5_2_a`)
  refine ⟨3, fun V hV => ?_⟩
  have hFH : F ⊆ upperHalf := hF.1
  obtain ⟨μ, hμ, hrep, hnorm, -⟩ := para3_1_dual_gamma hΓ hF hV
  obtain ⟨hPμ, ψ₀, hψ₀, hPψ⟩ := (cor6_5_2_a hΓ).1 μ hμ
  obtain ⟨hψB, hcusp⟩ := gl6_bd_indicator hψ₀
  set ψ : ℂ → ℂ := upperHalf.indicator ψ₀ with hψdef
  have hpsi : ∀ φ ∈ integrableAutomorphicQD Γ F,
      V φ = beltramiPairing F (fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) φ := by
    intro φ hφ
    rw [hrep φ hφ, gl6_bd_repr hΓ hfree hF hμ hψ₀ hPψ φ hφ]
    refine setIntegral_congr_fun hF.2.1 fun z hz => ?_
    simp only [hψdef, indicator_of_mem (hFH hz)]
  set D := dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V with hDdef
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hfin : cuspNorm upperHalf ψ ≠ ⊤ := hψB.2.2.ne
  -- `‖ψ‖_B ≤ ‖P μ‖∞ ≤ 3 ‖μ‖∞ = 3 ‖V‖`
  have h1 : cuspNorm upperHalf ψ ≤ ENNReal.ofReal (3 * D) := by
    have hae : projectionP μ =ᵐ[volume.restrict upperHalf]
        upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ₀ w) := by
      filter_upwards [ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz
      rw [hPψ z hz, indicator_of_mem hz]
    calc cuspNorm upperHalf ψ = cuspNorm upperHalf ψ₀ := hcusp
      _ ≤ eLpNorm (upperHalf.indicator fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ₀ w)) ⊤
          (volume.restrict upperHalf) := gl6_bd_cusp_le hψ₀
      _ = eLpNorm (projectionP μ) ⊤ (volume.restrict upperHalf) := (eLpNorm_congr_ae hae).symm
      _ ≤ 3 * eLpNorm μ ⊤ (volume.restrict upperHalf) := hPμ
      _ = ENNReal.ofReal (3 * D) := by
          rw [hnorm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- `‖V‖ ≤ ‖4y²ψ̄‖∞ ≤ ‖ψ‖_B`
  have h2 : ENNReal.ofReal D ≤ cuspNorm upperHalf ψ :=
    (gl3_dual_le hFH (ν := fun w => 4 * (w.im : ℂ) ^ 2 * conj (ψ w)) hpsi).trans
      ((eLpNorm_congr_ae (by
        filter_upwards [ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz
        rw [indicator_of_mem hz])).trans_le (gl6_bd_mem hψB).2)
  refine ⟨ψ, ⟨hψB, fun z hz => indicator_of_notMem hz _, hpsi, ?_, ?_⟩, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  · have h3 : D ≤ (cuspNorm upperHalf ψ).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h2
    have h4 : 0 ≤ (cuspNorm upperHalf ψ).toReal := ENNReal.toReal_nonneg
    linarith
  · rintro ψ' ⟨hψ'B, hψ'0, hψ'rep, -, -⟩
    funext z
    by_cases hz : z ∈ upperHalf
    · exact gl6_bd_unique hΓ hfree hF hψ'B hψB (fun φ hφ => (hψ'rep φ hφ).symm.trans (hpsi φ hφ)) hz
    · rw [hψ'0 z hz, hψdef, indicator_of_notMem hz]

end GardinerLakic2000
