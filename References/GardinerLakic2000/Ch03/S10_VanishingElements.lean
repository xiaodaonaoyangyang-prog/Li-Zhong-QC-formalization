import References.GardinerLakic2000.Ch03.S09_EquivalenceTheorem

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.10 Vanishing elements of `Z(Λ)`

Source `teichmuller.txt`, lines 3171–3261 (Chapter 3, §3.10).

* Unlabelled (the isometric inclusion `Z(Ω) ⊆ Z(Λ)`, l. 3172; recalled at l. 3241) — `para3_10_inclusion`
* Definition 9 (`Z₀(Λ)`, l. 3174; used in Ch. 16, 17) — `zZeroClosed`
* Definition 10 (vanishing cross-ratio distortion, l. 3180; used in Ch. 16, 17) — `HasVanishingCrDistortion`,
  `HasVanishingCrDistortionInf`, `HasVanishingCrDistortionExt`
* Lemma 4 (l. 3184) — `lemma3_4`
* Theorem 12 (l. 3193) — `thm3_12`
* Theorem 13 (l. 3227) — `thm3_13`
* Unlabelled (a vector field is the derivative of a holomorphic motion of `Λ` iff it has bounded cross-ratio norm,
  l. 3241) — `para3_10_motion_iff`
* Definition (`Z₀(Ω)`, the predual-type subspace of `Z(Ω)` defined as in §3.3 by degenerating sequences of `A(Ω)`,
  l. 3172) — `IsDegeneratingSeqOpen`, `betaSeminormOpen`, `zZeroOpen`
* Definition (`φ_z` as an element of `A(Ω)`, `V(φ_z)` of Lemma 5, l. 3243) — `phiZOn`
* Lemma 5 (l. 3243) — `lemma3_5_a`, `lemma3_5_b`, `lemma3_5_c`
* Lemma 6 (l. 3256) — `lemma3_6`
* Theorem 14 (l. 3260) — `thm3_14`

Not items: "vanishing `∂̄`-derivative" (l. 3176, contained in Definition 9); the case `Λ = ℂ̄` (l. 3231–3239, U−); "no
predual of `Z(Λ)` when `Λ` has positive measure [EGL97]" (l. 3172, not cited). Modelling: vector fields on `Λ` are
functions `ℂ → ℂ` read on the finite points of `Λ`; an element of `Z(Λ)` as a vector field is `V_μ + p` on `Λ` (§3.9).
Definition 9's "neighbourhood `U` of `Λ`" is an open set of `ℂ̄` containing `Λ`. `HasVanishingCrDistortion` is Definition 10 for finite `d` and finite limit
point [reading, as in the proof of Theorem 12]; `HasVanishingCrDistortionExt` adds the two cases with `∞` (`d = ∞`, limit point `∞`) and is the
property of Theorems 13 and 14 [CORRECTION, AUDIT4 G4: with the finite cases only, Theorem 13 (⇐) is false]. Theorem 12 is stated for the finite
cases only (true, weaker than the book). In Lemmas 5, 6 and Theorem 14, `Ω = ℂ̄ ∖ Λ` with `0, 1, ∞ ∈ Λ`,
and the map `V ↦ W`, `W(z) = V(φ_z|_Ω)` (`φ_z` of (3.17), restricted to `Ω` by `phiZOn`), is the isomorphism of Lemma 5; the norm on
the vector fields is `teichNormVF`. [CORRECTION, AUDIT4 G3: the functionals of `Z(Ω)` are only constrained on `A(Ω)`, and `φ_z` itself is not in `A(Ω)`
(it is not `0` on `Λ`), so `V (φ_z)` was a free value and Lemmas 5, 6 and Theorem 14 were false; `V (phiZOn Ω z)` is the book's `V(φ_z)`.]
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane phiArea normalizedCauchyTOn IsBeltramiCoeff)

/-- Helper for `para3_10_inclusion`: the restriction `1_Ω φ` of `φ ∈ A(Ω^c)` to an open `Ω ⊆ ℂ̄` lies in `A(Ω)`
(it agrees with `φ` on the open set `Ω ∩ ℂ`, which contains a neighbourhood of `∞` when `∞ ∈ Ω`). -/
theorem gl3_restrict_mem {Ω : Set ExtPlane} (hΩ : IsOpen Ω) {φ : ℂ → ℂ} (hφ : φ ∈ aSpaceClosed Ωᶜ) :
    {z : ℂ | (z : ExtPlane) ∈ Ω}.indicator φ ∈ aSpaceOpen Ω := by
  classical
  set S : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ Ω} with hS
  have hSo : IsOpen S := hΩ.preimage OnePoint.continuous_coe
  obtain ⟨hint, hd, hinf⟩ := hφ
  refine ⟨⟨hint.indicator hSo.measurableSet, fun z hz => ?_, fun hinfΩ => ?_⟩, fun z hz => ?_⟩
  · have hzS : z ∈ S := by
      have : ¬ ((z : ExtPlane) ∈ Ωᶜ) := hz
      rwa [mem_compl_iff, not_not] at this
    have hev : S.indicator φ =ᶠ[𝓝 z] φ :=
      Filter.eventuallyEq_of_mem (hSo.mem_nhds hzS) fun w hw => indicator_of_mem hw φ
    exact ((hd z hz).differentiableAt (by
      have hopen : IsOpen {w : ℂ | (w : ExtPlane) ∉ Ωᶜ} := by
        simpa [mem_compl_iff, not_not] using hSo
      exact hopen.mem_nhds hz)).congr_of_eventuallyEq hev |>.differentiableWithinAt
  · obtain ⟨g, hg, hgeq⟩ := hinf hinfΩ
    refine ⟨g, hg, ?_⟩
    -- a neighbourhood `|z| > R` of `∞` lies in `Ω`
    have hinfΩ' : (OnePoint.infty : ExtPlane) ∈ Ω := by
      simpa [mem_compl_iff] using hinfΩ
    obtain ⟨K, ⟨-, hKk⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 (hΩ.mem_nhds hinfΩ')
    obtain ⟨R₀, hR₀⟩ := hKk.isBounded.subset_closedBall 0
    set R := max R₀ 1 with hR
    have hR0 : 0 < R := by positivity
    have hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ S := by
      intro z hz
      have hzK : z ∉ K := fun h => by
        have := mem_closedBall_zero_iff.1 (hR₀ h)
        have := le_max_left R₀ 1
        linarith
      exact hKsub (Or.inl ⟨z, hzK, rfl⟩)
    have hnear : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w⁻¹ ∈ S := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [ball_mem_nhds (0 : ℂ) (inv_pos.2 hR0)] with w hw hw0
      refine hfar _ ?_
      rw [norm_inv]
      exact (lt_inv_comm₀ hR0 (norm_pos_iff.2 hw0)).2 (mem_ball_zero_iff.1 hw)
    filter_upwards [hgeq, hnear] with w h1 h2
    rw [h1, indicator_of_mem h2]
  · exact indicator_of_notMem (show z ∉ S from hz) φ

/-- Helper for `para3_10_inclusion`: `A(Ω)` is closed under scalar multiplication. -/
theorem gl3_aSpaceOpen_smul {Ω : Set ExtPlane} {ψ : ℂ → ℂ} (hψ : ψ ∈ aSpaceOpen Ω) (c : ℂ) :
    c • ψ ∈ aSpaceOpen Ω := by
  obtain ⟨⟨hint, hd, hinf⟩, h0⟩ := hψ
  refine ⟨⟨hint.smul c, hd.const_smul c, fun hinfΩ => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨g, hg, hgeq⟩ := hinf hinfΩ
    refine ⟨c • g, hg.const_smul, ?_⟩
    filter_upwards [hgeq] with w hw
    simp only [Pi.smul_apply, smul_eq_mul, hw]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, h0 z hz, mul_zero]

/-- Helper for `para3_10_inclusion`: `phiArea` of a function in `L¹` is finite. -/
theorem gl3_phiArea_ne_top {φ : ℂ → ℂ} (hφ : Integrable φ) : phiArea φ univ ≠ ⊤ := by
  unfold phiArea
  rw [Measure.restrict_univ]
  simp only [ofReal_norm]
  exact hφ.hasFiniteIntegral.ne

/-- **Unlabelled** (§3.10, l. 3172). The isometric inclusion `Z(Ω) ⊆ Z(Λ)`, `Λ = ℂ̄ ∖ Ω`: `V ∈ Z(Ω)` extends to
`A(Λ)` by `φ ↦ V(φ|_Ω)`, with the same norm. -/
theorem para3_10_inclusion {Ω : Set ExtPlane} (hΩ : IsOpen Ω) {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceOpen Ω) :
    (fun φ => V ({z : ℂ | (z : ExtPlane) ∈ Ω}.indicator φ)) ∈ zSpaceClosed Ωᶜ ∧
      dualNormOn (aSpaceClosed Ωᶜ) (fun φ => phiArea φ univ) (fun φ => V ({z : ℂ | (z : ExtPlane) ∈ Ω}.indicator φ)) =
        dualNormOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V := by
  classical
  set S : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ Ω} with hS
  obtain ⟨hadd, hsmul, C, hC'⟩ := hV
  have hC : ∀ a ∈ aSpaceOpen Ω, ‖V a‖ ≤ C * (phiArea a univ).toReal := hC'
  -- the restriction does not increase the norm
  have hle : ∀ φ : ℂ → ℂ, phiArea (S.indicator φ) univ ≤ phiArea φ univ := by
    intro φ
    unfold phiArea
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    exact norm_indicator_le_norm_self φ z
  have hbound : ∀ φ ∈ aSpaceClosed Ωᶜ, ‖V (S.indicator φ)‖ ≤ max C 0 * (phiArea φ univ).toReal := by
    intro φ hφ
    have h1 := hC _ (gl3_restrict_mem hΩ hφ)
    have h2 : (phiArea (S.indicator φ) univ).toReal ≤ (phiArea φ univ).toReal :=
      ENNReal.toReal_mono (gl3_phiArea_ne_top hφ.1) (hle φ)
    calc ‖V (S.indicator φ)‖ ≤ C * (phiArea (S.indicator φ) univ).toReal := h1
      _ ≤ max C 0 * (phiArea (S.indicator φ) univ).toReal :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
      _ ≤ max C 0 * (phiArea φ univ).toReal := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  refine ⟨⟨fun a ha b hb => ?_, fun c a ha => ?_, max C 0, hbound⟩, ?_⟩
  · show V (S.indicator (a + b)) = V (S.indicator a) + V (S.indicator b)
    rw [indicator_add']
    exact hadd _ (gl3_restrict_mem hΩ ha) _ (gl3_restrict_mem hΩ hb)
  · show V (S.indicator (c • a)) = c * V (S.indicator a)
    have e : S.indicator (c • a) = c • S.indicator a := by
      ext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [e]
    exact hsmul c _ (gl3_restrict_mem hΩ ha)
  -- the two dual norms
  have hVbdd : BddAbove (range fun b : ℂ → ℂ => ⨆ (_ : b ∈ aSpaceOpen Ω ∧ phiArea b univ = 1), ‖V b‖) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨b, rfl⟩
    refine Real.iSup_le (fun hb => ?_) (le_max_right _ _)
    have := hC b hb.1
    rw [hb.2, ENNReal.toReal_one, mul_one] at this
    exact this.trans (le_max_left _ _)
  have hWbdd : BddAbove (range fun φ : ℂ → ℂ =>
      ⨆ (_ : φ ∈ aSpaceClosed Ωᶜ ∧ phiArea φ univ = 1), ‖V (S.indicator φ)‖) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    refine Real.iSup_le (fun hφ => ?_) (le_max_right _ _)
    have := hbound φ hφ.1
    rwa [hφ.2, ENNReal.toReal_one, mul_one] at this
  have hVnn : 0 ≤ dualNormOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V :=
    Real.iSup_nonneg fun b => Real.iSup_nonneg fun _ => norm_nonneg _
  have hVle : ∀ b, b ∈ aSpaceOpen Ω → phiArea b univ = 1 →
      ‖V b‖ ≤ dualNormOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V := by
    intro b hb hb1
    refine le_trans ?_ (le_ciSup hVbdd b)
    rw [ciSup_pos (⟨hb, hb1⟩ : b ∈ aSpaceOpen Ω ∧ phiArea b univ = 1)]
  apply le_antisymm
  · refine Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) hVnn) hVnn
    obtain ⟨hφA, hφ1'⟩ := hφ
    have hφ1 : phiArea φ univ = 1 := hφ1'
    set c := (phiArea (S.indicator φ) univ).toReal with hc
    have hc1 : c ≤ 1 := by
      have := ENNReal.toReal_mono (gl3_phiArea_ne_top hφA.1) (hle φ)
      rwa [hφ1, ENNReal.toReal_one] at this
    by_cases hc0 : c = 0
    · have h0 := hC _ (gl3_restrict_mem hΩ hφA)
      rw [← hc, hc0, mul_zero] at h0
      exact (h0.trans hVnn)
    · have hcpos : 0 < c := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hc0)
      set ψ := ((c : ℂ)⁻¹) • S.indicator φ with hψ
      have hψA : ψ ∈ aSpaceOpen Ω := gl3_aSpaceOpen_smul (gl3_restrict_mem hΩ hφA) _
      have hfin : phiArea (S.indicator φ) univ ≠ ⊤ := ne_top_of_le_ne_top (gl3_phiArea_ne_top hφA.1) (hle φ)
      have hψ1 : phiArea ψ univ = 1 := by
        unfold phiArea
        have h1 : ∀ z, ENNReal.ofReal ‖ψ z‖ = ENNReal.ofReal c⁻¹ * ENNReal.ofReal ‖S.indicator φ z‖ := by
          intro z
          rw [hψ, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hcpos, ENNReal.ofReal_mul (inv_nonneg.2 hcpos.le)]
        simp only [h1]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have h2 : ∫⁻ z in univ, ENNReal.ofReal ‖S.indicator φ z‖ = ENNReal.ofReal c := by
          rw [hc, ENNReal.ofReal_toReal hfin]
          rfl
        rw [h2, ← ENNReal.ofReal_mul (inv_nonneg.2 hcpos.le), inv_mul_cancel₀ hc0, ENNReal.ofReal_one]
      have hdecomp : S.indicator φ = (c : ℂ) • ψ := by
        rw [hψ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hc0), one_smul]
      have hVψ := hsmul (c : ℂ) ψ hψA
      rw [← hdecomp] at hVψ
      show ‖V (S.indicator φ)‖ ≤ _
      rw [hVψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      calc c * ‖V ψ‖ ≤ 1 * dualNormOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V :=
            mul_le_mul hc1 (hVle ψ hψA hψ1) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  · have hWnn : 0 ≤ dualNormOn (aSpaceClosed Ωᶜ) (fun φ => phiArea φ univ)
        (fun φ => V (S.indicator φ)) :=
      Real.iSup_nonneg fun b => Real.iSup_nonneg fun _ => norm_nonneg _
    refine Real.iSup_le (fun b => Real.iSup_le (fun hb => ?_) hWnn) hWnn
    obtain ⟨hbA, hb1⟩ := hb
    have hSb : S.indicator b = b := by
      refine indicator_eq_self.2 fun z hz => ?_
      by_contra hzS
      exact hz (hbA.2 z hzS)
    have hbC : b ∈ aSpaceClosed Ωᶜ := hbA.1
    refine le_trans ?_ (le_ciSup hWbdd b)
    rw [ciSup_pos (⟨hbC, hb1⟩ : b ∈ aSpaceClosed Ωᶜ ∧ phiArea b univ = 1), hSb]

/-- **Definition 9** (§3.10, l. 3174). `Z₀(Λ)`: the vector fields `V ∈ Z(Λ)` such that for every `ε > 0` there are an
extension `Ṽ = V_μ + p ∈ Z(ℂ)` of `V` and a neighbourhood `U` of `Λ` with `|∂̄Ṽ| = |μ| < ε` on `U`. -/
def zZeroClosed (Λ : Set ExtPlane) : Set (ℂ → ℂ) :=
  {V | ∀ ε > (0 : ℝ), ∃ μ : ℂ → ℂ, (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧
    (∃ a b c : ℂ, ∀ z : ℂ, (z : ExtPlane) ∈ Λ → V z = normalizedCauchyTOn univ μ z + (a * z ^ 2 + b * z + c)) ∧
    ∃ U : Set ExtPlane, IsOpen U ∧ Λ ⊆ U ∧ ∀ᵐ (z : ℂ) ∂volume, (z : ExtPlane) ∈ U → ‖μ z‖ < ε}

/-- **Definition 10** (§3.10, l. 3180). `V` has vanishing cross-ratio distortion on `Λ`: `‖V‖_cr < ∞` and
`V(aₙ, bₙ, cₙ, d) → 0` for every `d ∈ Λ` and all sequences `aₙ, bₙ, cₙ` of distinct points of `Λ` converging to the same
point of `Λ ∖ {d}`. -/
def HasVanishingCrDistortion (Λ : Set ExtPlane) (V : ℂ → ℂ) : Prop :=
  crNorm Λ V < ⊤ ∧ ∀ (d p : ℂ) (a b c : ℕ → ℂ), (d : ExtPlane) ∈ Λ → (p : ExtPlane) ∈ Λ → p ≠ d →
    (∀ n, (a n : ExtPlane) ∈ Λ ∧ (b n : ExtPlane) ∈ Λ ∧ (c n : ExtPlane) ∈ Λ) →
    (∀ n, a n ≠ b n ∧ b n ≠ c n ∧ a n ≠ c n) →
    Tendsto a atTop (𝓝 p) → Tendsto b atTop (𝓝 p) → Tendsto c atTop (𝓝 p) →
      Tendsto (fun n => crDistortion V (a n) (b n) (c n) d) atTop (𝓝 0)

/-- **Definition 10, the cases with `∞`** (§3.10, l. 3180). `V` has vanishing cross-ratio distortion at `∞`: (i) for `d = ∞ ∈ Λ`
and distinct points `aₙ, bₙ, cₙ ∈ Λ` converging to the same finite `p ∈ Λ`, `V(aₙ, bₙ, cₙ, ∞) → 0`
(`crDistortionInf`); (ii) for finite `d ∈ Λ` and distinct points `aₙ, bₙ, cₙ ∈ Λ` tending to `∞`, `V(aₙ, bₙ, cₙ, d) → 0`. -/
def HasVanishingCrDistortionInf (Λ : Set ExtPlane) (V : ℂ → ℂ) : Prop :=
  (∀ (p : ℂ) (a b c : ℕ → ℂ), (p : ExtPlane) ∈ Λ →
    (∀ n, (a n : ExtPlane) ∈ Λ ∧ (b n : ExtPlane) ∈ Λ ∧ (c n : ExtPlane) ∈ Λ) →
    (∀ n, a n ≠ b n ∧ b n ≠ c n ∧ a n ≠ c n) →
    Tendsto a atTop (𝓝 p) → Tendsto b atTop (𝓝 p) → Tendsto c atTop (𝓝 p) →
      Tendsto (fun n => crDistortionInf V (a n) (b n) (c n)) atTop (𝓝 0)) ∧
  ∀ (d : ℂ) (a b c : ℕ → ℂ), (d : ExtPlane) ∈ Λ →
    (∀ n, (a n : ExtPlane) ∈ Λ ∧ (b n : ExtPlane) ∈ Λ ∧ (c n : ExtPlane) ∈ Λ) →
    (∀ n, a n ≠ b n ∧ b n ≠ c n ∧ a n ≠ c n) →
    Tendsto a atTop (cocompact ℂ) → Tendsto b atTop (cocompact ℂ) → Tendsto c atTop (cocompact ℂ) →
      Tendsto (fun n => crDistortion V (a n) (b n) (c n) d) atTop (𝓝 0)

/-- **Definition 10** (§3.10, l. 3180), complete: vanishing cross-ratio distortion for all `d ∈ Λ` and all limit points of `Λ ∖ {d}`,
finite or `∞`. -/
def HasVanishingCrDistortionExt (Λ : Set ExtPlane) (V : ℂ → ℂ) : Prop :=
  HasVanishingCrDistortion Λ V ∧ HasVanishingCrDistortionInf Λ V

/-- Helper for `lemma3_4`: if `a, b, c` lie within `ε` of `p` and `a ≠ b`, then
`(∫ (|z − a||z − b||z − c|)⁻¹)⁻¹ ≤ 8ε/π` (on `B(p, ε)` the integrand is `≥ (8ε³)⁻¹`; a non-integrable integrand
has Bochner integral `0`). -/
theorem gl3_lemma3_4_bound {p a b c : ℂ} {ε : ℝ} (hε : 0 < ε) (ha : ‖a - p‖ ≤ ε) (hb : ‖b - p‖ ≤ ε)
    (hc : ‖c - p‖ ≤ ε) :
    (∫ z, (‖z - a‖ * ‖z - b‖ * ‖z - c‖)⁻¹)⁻¹ ≤ 8 * ε / π := by
  set f : ℂ → ℝ := fun z => (‖z - a‖ * ‖z - b‖ * ‖z - c‖)⁻¹ with hf_def
  have hbd : 0 ≤ 8 * ε / π := by positivity
  by_cases hi : Integrable f
  swap
  · rw [integral_undef hi, inv_zero]
    exact hbd
  set s : Set ℂ := ball p ε \ {a, b, c} with hs_def
  have hfin : ({a, b, c} : Set ℂ).Finite := by simp
  have hs : MeasurableSet s := measurableSet_ball.diff hfin.measurableSet
  have hvol : volume s = volume (ball p ε) := measure_sdiff_null (hfin.measure_zero volume)
  have hvs : volume.real s = π * ε ^ 2 := by
    rw [Measure.real, hvol, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hε.le]
    simp [mul_comm]
  have hfs : volume s ≠ ⊤ := by
    rw [hvol, Complex.volume_ball]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
  have hlow : ∀ z ∈ s, (8 * ε ^ 3)⁻¹ ≤ f z := by
    intro z hz
    obtain ⟨hzb, hzn⟩ := hz
    rw [mem_ball, dist_eq_norm] at hzb
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzn
    obtain ⟨hza, hzb', hzc⟩ := hzn
    have e1 : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
    have e2 : 0 < ‖z - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hzb')
    have e3 : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
    have t1 : ‖z - a‖ ≤ 2 * ε := by
      have := norm_sub_le (z - p) (a - p)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    have t2 : ‖z - b‖ ≤ 2 * ε := by
      have := norm_sub_le (z - p) (b - p)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    have t3 : ‖z - c‖ ≤ 2 * ε := by
      have := norm_sub_le (z - p) (c - p)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    have hprod : ‖z - a‖ * ‖z - b‖ * ‖z - c‖ ≤ 8 * ε ^ 3 := by
      calc ‖z - a‖ * ‖z - b‖ * ‖z - c‖ ≤ (2 * ε) * (2 * ε) * (2 * ε) := by gcongr
        _ = 8 * ε ^ 3 := by ring
    exact inv_anti₀ (by positivity) hprod
  have h1 := setIntegral_ge_of_const_le_real hs hfs hlow hi.integrableOn
  have h2 : ∫ z in s, f z ≤ ∫ z, f z :=
    setIntegral_le_integral hi (Eventually.of_forall fun z => by positivity)
  rw [hvs] at h1
  have h3 : (8 * ε ^ 3)⁻¹ * (π * ε ^ 2) = π / (8 * ε) := by
    field_simp
  rw [h3] at h1
  have hpos : 0 < π / (8 * ε) := by positivity
  calc (∫ z, f z)⁻¹ ≤ (π / (8 * ε))⁻¹ := inv_anti₀ hpos (h1.trans h2)
    _ = 8 * ε / π := by rw [inv_div]

/-- **Lemma 4** (§3.10, l. 3184). If `aₙ, bₙ, cₙ → p` are distinct for each `n` and `Fₙ > 0` normalizes
`∬ Fₙ/(|z − aₙ||z − bₙ||z − cₙ|) = 1`, then `Fₙ → 0`. -/
theorem lemma3_4 {p : ℂ} {a b c : ℕ → ℂ} (habc : ∀ n, a n ≠ b n ∧ b n ≠ c n ∧ a n ≠ c n)
    (ha : Tendsto a atTop (𝓝 p)) (hb : Tendsto b atTop (𝓝 p)) (hc : Tendsto c atTop (𝓝 p)) :
    Tendsto (fun n => (∫ z, (‖z - a n‖ * ‖z - b n‖ * ‖z - c n‖)⁻¹)⁻¹) atTop (𝓝 0) := by
  set ε : ℕ → ℝ := fun n => max ‖a n - p‖ (max ‖b n - p‖ ‖c n - p‖) with hε_def
  have hε0 : ∀ n, 0 < ε n := by
    intro n
    by_contra h
    push Not at h
    have h1 : ‖a n - p‖ ≤ 0 := (le_max_left _ _).trans h
    have h2 : ‖b n - p‖ ≤ 0 := ((le_max_left _ _).trans (le_max_right _ _)).trans h
    have e1 : a n = p := sub_eq_zero.1 (norm_le_zero_iff.1 h1)
    have e2 : b n = p := sub_eq_zero.1 (norm_le_zero_iff.1 h2)
    exact (habc n).1 (e1.trans e2.symm)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have ta := (tendsto_iff_norm_sub_tendsto_zero.1 ha)
    have tb := (tendsto_iff_norm_sub_tendsto_zero.1 hb)
    have tc := (tendsto_iff_norm_sub_tendsto_zero.1 hc)
    simpa using ta.max (tb.max tc)
  have hup : Tendsto (fun n => 8 * ε n / π) atTop (𝓝 0) := by
    simpa using (hεt.const_mul 8).div_const π
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · exact inv_nonneg.2 (integral_nonneg fun z => by positivity)
  · exact gl3_lemma3_4_bound (hε0 n) (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))

/-- **Theorem 12** (§3.10, l. 3193). If `V ∈ Z₀(Λ)`, then `V` has the vanishing cross-ratio property on `Λ`. -/
theorem thm3_12 {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {V : ℂ → ℂ} (hV : V ∈ zZeroClosed Λ) :
    HasVanishingCrDistortion Λ V := by
  sorry

/-- **Theorem 13** (§3.10, l. 3227). `V ∈ Z(Λ)` has the vanishing cross-ratio property if and only if `V ∈ Z₀(Λ)`. -/
theorem thm3_13 {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {V : ℂ → ℂ} (hV : V ∈ zCrSet Λ) :
    HasVanishingCrDistortionExt Λ V ↔ V ∈ zZeroClosed Λ := by
  sorry

/-- **Unlabelled** (§3.10, l. 3241). A vector field `V` on `Λ` is the derivative at `t = 0` of a holomorphic motion of
`Λ` (parametrized by a disc `|t| < δ`, rescaled here to the unit disc) if and only if it has bounded cross-ratio
norm. -/
theorem para3_10_motion_iff {Λ : Set ExtPlane} (hΛ : IsClosed Λ) (V : ℂ → ℂ) :
    (∃ (h : ℂ → ℂ → ℂ) (δ : ℝ), 0 < δ ∧ IsHolMotion {z : ℂ | (z : ExtPlane) ∈ Λ} h ∧
      ∀ z : ℂ, (z : ExtPlane) ∈ Λ → HasDerivAt (fun t => h t z) (δ * V z) 0) ↔ crNorm Λ V < ⊤ := by
  sorry

/-- Helper for `Z₀(Ω)` (§3.10, l. 3172, as Definition 1 of §3.1). A degenerating sequence in `A(Ω)`: norm `1`,
converging to `0` uniformly on compact subsets of `Ω ∩ ℂ` (and near `∞` in the chart `1/z` when `∞ ∈ Ω`, which the
integrable functions of `A(Ω)` satisfy automatically in norm; only finite compacts are required). -/
def IsDegeneratingSeqOpen (Ω : Set ExtPlane) (φ : ℕ → ℂ → ℂ) : Prop :=
  (∀ n, φ n ∈ aSpaceOpen Ω ∧ phiArea (φ n) univ = 1) ∧
    TendstoLocallyUniformlyOn φ 0 atTop {z : ℂ | (z : ExtPlane) ∈ Ω}

/-- Helper for `Z₀(Ω)` (§3.10, l. 3172, as Definition 2 of §3.3). `β(V)` for `V ∈ Z(Ω)`. -/
def betaSeminormOpen (Ω : Set ExtPlane) (V : (ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℕ → ℂ → ℂ) (_ : IsDegeneratingSeqOpen Ω φ), limsup (fun n => (‖V (φ n)‖₊ : ℝ≥0∞)) atTop

/-- **Definition** (§3.10, l. 3172). `Z₀(Ω) = {V ∈ Z(Ω) : β(V) = 0}`. -/
def zZeroOpen (Ω : Set ExtPlane) : Set ((ℂ → ℂ) → ℂ) := {V | V ∈ zSpaceOpen Ω ∧ betaSeminormOpen Ω V = 0}

/-- **`φ_z` as an element of `A(Ω)`** (§3.10, l. 3243): `φ_z` restricted to `Ω` and extended by `0` (the functionals of `Z(Ω)` are only
determined on `aSpaceOpen Ω`; `V(φ_z)` of Lemma 5 means `V` applied to this function). -/
def phiZOn (Ω : Set ExtPlane) (z : ℂ) : ℂ → ℂ := {w : ℂ | (w : ExtPlane) ∈ Ω}.indicator (phiZ z)

/-- **Lemma 5** (§3.10, l. 3243), injectivity. `V ↦ W`, `W(z) = V(φ_z)` for `z ∈ Λ`, is injective on `Z(Ω)`. -/
theorem lemma3_5_a {Ω : Set ExtPlane} (hΩ : IsOpen Ω) (h0 : ((0 : ℂ) : ExtPlane) ∉ Ω) (h1 : ((1 : ℂ) : ExtPlane) ∉ Ω)
    (hinf : (OnePoint.infty : ExtPlane) ∉ Ω) {V₁ V₂ : (ℂ → ℂ) → ℂ} (hV₁ : V₁ ∈ zSpaceOpen Ω)
    (hV₂ : V₂ ∈ zSpaceOpen Ω) (h : ∀ z : ℂ, (z : ExtPlane) ∉ Ω → z ≠ 0 → z ≠ 1 → V₁ (phiZOn Ω z) = V₂ (phiZOn Ω z)) :
    ∀ φ ∈ aSpaceOpen Ω, V₁ φ = V₂ φ := by
  sorry

/-- **Lemma 5** (§3.10, l. 3243), the image. The fields `W(z) = V(φ_z)`, `V ∈ Z(Ω)`, are exactly the fields on `Λ`
vanishing at `0` and `1` that extend to fields `W̃ = V_μ` in the plane with `∂̄W̃ = μ = 0` almost everywhere on `Λ`. -/
theorem lemma3_5_b {Ω : Set ExtPlane} (hΩ : IsOpen Ω) (h0 : ((0 : ℂ) : ExtPlane) ∉ Ω) (h1 : ((1 : ℂ) : ExtPlane) ∉ Ω)
    (hinf : (OnePoint.infty : ExtPlane) ∉ Ω) (W : ℂ → ℂ) :
    (∃ V ∈ zSpaceOpen Ω, ∀ z : ℂ, (z : ExtPlane) ∉ Ω → W z = V (phiZOn Ω z)) ↔
      ∃ μ : ℂ → ℂ, (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧ (∀ᵐ (z : ℂ) ∂volume, (z : ExtPlane) ∉ Ω → μ z = 0) ∧
        ∀ z : ℂ, (z : ExtPlane) ∉ Ω → W z = normalizedCauchyTOn univ μ z := by
  sorry

/-- **Lemma 5** (§3.10, l. 3243), isometry. The norm of `V ∈ Z(Ω)` equals the Teichmüller norm of its field
`W(z) = V(φ_z)` on `Λ`. -/
theorem lemma3_5_c {Ω : Set ExtPlane} (hΩ : IsOpen Ω) (h0 : ((0 : ℂ) : ExtPlane) ∉ Ω) (h1 : ((1 : ℂ) : ExtPlane) ∉ Ω)
    (hinf : (OnePoint.infty : ExtPlane) ∉ Ω) {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceOpen Ω) :
    ENNReal.ofReal (dualNormOn (aSpaceOpen Ω) (fun φ => phiArea φ univ) V) =
      teichNormVF Ωᶜ (fun z => V (phiZOn Ω z)) := by
  sorry

/-- **Lemma 6** (§3.10, l. 3256). Under the isomorphism of Lemma 5, `Z₀(Ω)` corresponds to `Z₀(Λ)`. -/
theorem lemma3_6 {Ω : Set ExtPlane} (hΩ : IsOpen Ω) (h0 : ((0 : ℂ) : ExtPlane) ∉ Ω) (h1 : ((1 : ℂ) : ExtPlane) ∉ Ω)
    (hinf : (OnePoint.infty : ExtPlane) ∉ Ω) {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceOpen Ω) :
    V ∈ zZeroOpen Ω ↔ (fun z => V (phiZOn Ω z)) ∈ zZeroClosed Ωᶜ := by
  sorry

/-- **Theorem 14** (§3.10, l. 3260). Under the isomorphism of Lemma 6, `Z₀(Ω)` corresponds to the vector fields
satisfying the vanishing cross-ratio condition. -/
theorem thm3_14 {Ω : Set ExtPlane} (hΩ : IsOpen Ω) (h0 : ((0 : ℂ) : ExtPlane) ∉ Ω) (h1 : ((1 : ℂ) : ExtPlane) ∉ Ω)
    (hinf : (OnePoint.infty : ExtPlane) ∉ Ω) {V : (ℂ → ℂ) → ℂ} (hV : V ∈ zSpaceOpen Ω) :
    V ∈ zZeroOpen Ω ↔ HasVanishingCrDistortionExt Ωᶜ (fun z => V (phiZOn Ω z)) := by
  sorry

end GardinerLakic2000
