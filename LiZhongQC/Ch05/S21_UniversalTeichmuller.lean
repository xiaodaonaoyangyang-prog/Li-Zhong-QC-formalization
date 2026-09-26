import LiZhongQC.Ch05.S20_SchwarzDomains
import LiZhongQC.Ch02.S13_Representation

/-!
# §21 万有 Teichmüller 空间 — The universal Teichmüller space

* the space `M` of Beltrami coefficients supported in `ℍ`, the normalized solutions `f_μ`
                                                     — `BeltramiH`, `normalizedSolution`
* the universal Teichmüller space `T = M/∼`          — `UniversalTeichmuller`
* the Teichmüller distance, (21.1), (21.4), the metric axioms
* Theorem 21.1 (`T` is path connected)               — `thm21_1_path_connected`
* the Banach space `A(𝕃)` and the Bers map `Ψ([μ]) = S_{f_μ}|𝕃`
* Lemma 21.1 (`‖S_f‖ ≤ 3 ‖μ_f‖_∞`), (21.10)
* Theorem 21.2 (`Ψ` is a homeomorphism onto its image), Theorem 21.3 (`Ψ(T)` is open)
* Theorem 21.4 (Gehring: `T* = int 𝓕*`) and the remarks of Gehring and Thurston
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The space `M` of Beltrami coefficients `μ` on the plane with `‖μ‖_∞ < 1` which vanish in the
closed lower half-plane. -/
def BeltramiH : Type :=
  {μ : ℂ → ℂ // (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff μ univ k) ∧ ∀ z : ℂ, z.im ≤ 0 → μ z = 0}

open scoped Classical in
/-- The normalized solution `f_μ` (Theorem 13.7): the quasiconformal map of the plane with complex
characteristic `μ` fixing `0, 1, ∞`. -/
def normalizedSolution (μ : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ f : ℂ → ℂ, IsNormalizedSolution f μ then h.choose else id

/-- `μ ∼ ν` iff `f_μ|ℝ = f_ν|ℝ`. -/
def teichSetoid : Setoid BeltramiH where
  r μ ν := ∀ x : ℝ, normalizedSolution μ.1 x = normalizedSolution ν.1 x
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- The universal Teichmüller space `T = M/∼` (万有 Teichmüller 空间). -/
def UniversalTeichmuller : Type := Quotient teichSetoid

/-! ### §21.1 metric track interface (coordinator 553e2d) -/

/-- `v(μ, ν) = ln K[f_ν ∘ f_μ⁻¹]` on `f_μ(ℍ)`: the quantity whose infimum over the two classes is the Teichmüller
distance `UniversalTeichmuller.dist`. -/
def ut_v (μ ν : BeltramiH) : ℝ :=
  Real.log (maxDilatation (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ)
    (normalizedSolution μ.1 '' upperHalf)).toReal

/-- **P.** `f_μ` is the normalized solution of the Beltrami equation for `μ` (Theorem 13.7). -/
theorem ut_spec (μ : BeltramiH) : IsNormalizedSolution (normalizedSolution μ.1) μ.1 := by
  obtain ⟨⟨k, hk0, hk1, hμ⟩, -⟩ := μ.2
  have h : ∃ f : ℂ → ℂ, IsNormalizedSolution f μ.1 :=
    (thm13_7_normalized_existence hk0 hk1 hμ).imp fun _ hf => hf.1
  rw [normalizedSolution, dite_eq_left h]
  exact h.choose_spec

/-- **P.** `f_μ` is conformal on the lower half-plane (`μ = 0` there). -/
theorem ut_conformal_lowerHalf (μ : BeltramiH) :
    IsConformalOnto (normalizedSolution μ.1) lowerHalf (normalizedSolution μ.1 '' lowerHalf) := by
  obtain ⟨⟨K, hK⟩, -, -, -, hd⟩ := ut_spec μ
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  obtain ⟨⟨hm, -⟩, hs⟩ := thm10_2_genHomeoSolution_of_isKQC (nx_isKQC_restrict hK hLo (subset_univ _))
  have hb : IsBeltramiCoeff (complexDilatation (normalizedSolution μ.1)) lowerHalf 0 := by
    refine ⟨hm, ?_⟩
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem hLo.measurableSet] with z h1 h2
    rw [h1, μ.2.2 z (le_of_lt h2), norm_zero]
  exact thm7_3_one_qc_conformal
    (by simpa using thm10_2_isKQC_of_genHomeoSolution hLo le_rfl zero_lt_one hb hs)

/-- An injective map of the plane fixing every real point sends non-real points to non-real points: if `Ψ z` were
real, then `Ψ z = Ψ (Re Ψ z)` and injectivity would make `z` real. -/
theorem ut_w0_im_ne_zero {Ψ : ℂ → ℂ} (hinj : Function.Injective Ψ) (hfix : ∀ x : ℝ, Ψ x = x) {z : ℂ}
    (hz : z.im ≠ 0) : (Ψ z).im ≠ 0 := by
  intro h
  have hre : Ψ z = Ψ (((Ψ z).re : ℝ) : ℂ) := by
    rw [hfix]
    exact Complex.ext rfl (by rw [h, Complex.ofReal_im])
  rw [hinj hre, Complex.ofReal_im] at hz
  exact hz rfl

/-- A map of the plane fixing every real point: every non-real point `w` in its range is the image of a point of `ℍ`
or of a point of `𝕃` (a real preimage would be fixed, so `w` would be real). -/
theorem ut_w0_cover {Ψ : ℂ → ℂ} (hsurj : Function.Surjective Ψ) (hfix : ∀ x : ℝ, Ψ x = x) {w : ℂ}
    (hw : w.im ≠ 0) : w ∈ Ψ '' upperHalf ∨ w ∈ Ψ '' lowerHalf := by
  obtain ⟨z, rfl⟩ := hsurj w
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact Or.inr ⟨z, h, rfl⟩
  · refine absurd ?_ hw
    have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by rw [h, Complex.ofReal_im])
    rw [hz, hfix, Complex.ofReal_im]
  · exact Or.inl ⟨z, h, rfl⟩

/-- A continuous injective map of the plane fixing every real point maps a preconnected set of non-real points into
one of the two half-planes: the image is preconnected and misses `ℝ` (`ut_w0_im_ne_zero`), and `ℍ`, `𝕃` are
disjoint open sets. -/
theorem ut_w0_subset_or {Ψ : ℂ → ℂ} (hc : Continuous Ψ) (hinj : Function.Injective Ψ)
    (hfix : ∀ x : ℝ, Ψ x = x) {S : Set ℂ} (hS : IsPreconnected S) (hS0 : ∀ z ∈ S, z.im ≠ 0) :
    Ψ '' S ⊆ upperHalf ∨ Ψ '' S ⊆ lowerHalf := by
  refine (hS.image Ψ hc.continuousOn).subset_or_subset (isOpen_lt continuous_const continuous_im)
    (isOpen_lt continuous_im continuous_const) ?_ ?_
  · refine Set.disjoint_left.2 fun z h₁ h₂ => ?_
    exact lt_asymm (show 0 < z.im from h₁) (show z.im < 0 from h₂)
  · rintro _ ⟨z, hz, rfl⟩
    rcases lt_or_gt_of_ne (ut_w0_im_ne_zero hinj hfix (hS0 z hz)) with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- **W0 (orientation).**  A `K`-q.c. map `Ψ` of the plane onto itself fixing every real point cannot map `ℍ` onto `𝕃`:
otherwise `-Ψ` would be a `K`-q.c. self-map of `ℍ` fixing `∞` whose boundary values `x ↦ -x` decrease, against
`b4_qs_monotone`. -/
theorem ut_w0_not_swap {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (hfix : ∀ x : ℝ, Ψ x = x) : Ψ '' upperHalf ≠ lowerHalf := by
  intro hswap
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  set E : ExtPlane ≃ₜ ExtPlane := (e.trans (Homeomorph.neg ℂ)).onePointCongr with hEdef
  have hEc : ∀ z : ℂ, E (z : ExtPlane) = ((-Ψ z : ℂ) : ExtPlane) := fun z => by
    rw [hEdef, Homeomorph.onePointCongr_apply, OnePoint.map_some, Homeomorph.trans_apply,
      Homeomorph.coe_neg, he]
  obtain ⟨hK, -⟩ := b4_rat_affine_comp hΨ hs (0 : ℂ) (0 : ℂ) one_ne_zero (neg_ne_zero.2 one_ne_zero)
  have hfun : (fun z => (-1 : ℂ) * Ψ (1 * z + 0) + 0) = fun z => -Ψ z := by
    funext z
    simp
  rw [hfun] at hK
  have hgK : IsKQC (fun z => -Ψ z) upperHalf K :=
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hgs : (fun z => -Ψ z) '' upperHalf = upperHalf := by
    rw [← Set.image_image (fun w : ℂ => -w) Ψ, hswap]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (-z).im
      rw [Complex.neg_im]
      exact neg_pos.2 hz
    · intro hw
      refine ⟨-w, ?_, neg_neg w⟩
      show (-w).im < 0
      rw [Complex.neg_im]
      exact neg_neg_iff_pos.2 hw
  have htoExt : E '' toExt upperHalf = toExt upperHalf := by
    unfold toExt
    rw [Set.image_image]
    simp_rw [hEc]
    rw [← Set.image_image (fun w : ℂ => (w : ExtPlane)) (fun z => -Ψ z), hgs]
  have hext : IsHomeoExtension (fun z => -Ψ z) upperHalf upperHalf E := by
    refine ⟨fun z _ => hEc z, E.continuous.continuousOn, E.injective.injOn, ?_⟩
    rw [Homeomorph.image_closure, htoExt]
  have hmono := (b4_qs_monotone (h := fun x : ℝ => -x)
    ⟨hgK, hgs, E, hext, rfl, fun x => by rw [hEc, hfix, Complex.ofReal_neg]⟩).1
  have h01 := hmono (show (0 : ℝ) < 1 from one_pos)
  norm_num at h01

/-- **W0.** A `K`-q.c. map of the plane onto itself which fixes every point of `ℝ` maps `ℍ` onto `ℍ` and `𝕃` onto
`𝕃` (it cannot swap the half-planes: `-Ψ` would be a q.c. self-map of `ℍ` with decreasing boundary values,
contradicting `b4_qs_monotone`). -/
theorem ut_preserves_halves {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (hfix : ∀ x : ℝ, Ψ x = x) : Ψ '' upperHalf = upperHalf ∧ Ψ '' lowerHalf = lowerHalf := by
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  have hc : Continuous Ψ := he ▸ e.continuous
  have hinj : Function.Injective Ψ := he ▸ e.injective
  have hsurj : Function.Surjective Ψ := he ▸ e.surjective
  have hLconn : IsPreconnected lowerHalf :=
    ((convex_Iio (0 : ℝ)).linear_preimage imLm).isPreconnected
  have hIU : (I : ℂ).im ≠ 0 := by simp
  have hIL : (-I : ℂ).im ≠ 0 := by simp
  rcases ut_w0_subset_or hc hinj hfix isConnected_upperHalf.isPreconnected
      (fun z hz => (show 0 < z.im from hz).ne') with hU | hU <;>
    rcases ut_w0_subset_or hc hinj hfix hLconn (fun z hz => (show z.im < 0 from hz).ne) with hL | hL
  · -- both half-planes into `ℍ`: `-i` is not hit
    exfalso
    rcases ut_w0_cover hsurj hfix hIL with h | h
    · have := hU h
      norm_num [upperHalf] at this
    · have := hL h
      norm_num [upperHalf] at this
  · -- `ℍ → ℍ`, `𝕃 → 𝕃`
    refine ⟨subset_antisymm hU fun w hw => ?_, subset_antisymm hL fun w hw => ?_⟩
    · rcases ut_w0_cover hsurj hfix (show 0 < w.im from hw).ne' with h | h
      · exact h
      · exact absurd (show w.im < 0 from hL h) (not_lt.2 (show 0 < w.im from hw).le)
    · rcases ut_w0_cover hsurj hfix (show w.im < 0 from hw).ne with h | h
      · exact absurd (show 0 < w.im from hU h) (not_lt.2 (show w.im < 0 from hw).le)
      · exact h
  · -- swap: `ℍ → 𝕃`, `𝕃 → ℍ`
    refine absurd (subset_antisymm hU fun w hw => ?_) (ut_w0_not_swap hΨ hs hfix)
    rcases ut_w0_cover hsurj hfix (show w.im < 0 from hw).ne with h | h
    · exact h
    · exact absurd (show 0 < w.im from hL h) (not_lt.2 (show w.im < 0 from hw).le)
  · -- both half-planes into `𝕃`: `i` is not hit
    exfalso
    rcases ut_w0_cover hsurj hfix hIU with h | h
    · have := hU h
      norm_num [lowerHalf] at this
    · have := hL h
      norm_num [lowerHalf] at this

/-- The reflection of a map `Ψ` across `ℝ`: `Ψ` on the closed lower half-plane `{Im z ≤ 0}` and
`z ↦ conj (Ψ (conj z))` on `ℍ`. -/
def ut_w_refl (Ψ : ℂ → ℂ) (z : ℂ) : ℂ := if z.im ≤ 0 then Ψ z else conj (Ψ (conj z))

/-- **W1** (reflection).  A continuous injective `Ψ : ℂ → ℂ` which fixes every point of `ℝ`, maps `𝕃` onto `𝕃` and
is `1`-q.c. on `𝕃` is the identity on the closed lower half-plane.  Its reflection `ut_w_refl Ψ` across `ℝ` is a
homeomorphism of `ℂ` onto `ℂ` which is `1`-q.c. on `𝕃` and on `ℍ`, hence on `ℂ` (`s13x_removable` with the null
set `ℝ`), hence a conformal bijection of `ℂ` (`thm7_3_one_qc_conformal`), hence affine (`nx_entire_affine`); it
fixes `0` and `1`, so it is the identity. -/
theorem ut_w_eq_self_of_refl {Ψ : ℂ → ℂ} (hc : Continuous Ψ) (hi : Function.Injective Ψ)
    (hL : Ψ '' lowerHalf = lowerHalf) (hfix : ∀ x : ℝ, Ψ x = x) (hK : IsKQC Ψ lowerHalf 1) {z : ℂ}
    (hz : z.im ≤ 0) : Ψ z = z := by
  -- `Ψ` fixes every point of the real axis
  have hreal : ∀ w : ℂ, w.im = 0 → Ψ w = w := fun w hw => by
    have hw' : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw])
    rw [← hw', hfix]
  -- `Ψ` maps `𝕃` into `𝕃` and `{Im z ≤ 0}` into `{Im z ≤ 0}`
  have hmapL : ∀ w : ℂ, w.im < 0 → (Ψ w).im < 0 := fun w hw => by
    have hmem : Ψ w ∈ Ψ '' lowerHalf := mem_image_of_mem Ψ hw
    rw [hL] at hmem
    exact hmem
  have hmapLe : ∀ w : ℂ, w.im ≤ 0 → (Ψ w).im ≤ 0 := fun w hw => by
    rcases hw.lt_or_eq with hlt | heq
    · exact (hmapL w hlt).le
    · rw [hreal w heq, heq]
  -- the two formulas for the reflection
  have hR1 : ∀ w : ℂ, w.im ≤ 0 → ut_w_refl Ψ w = Ψ w := fun w hw => ite_eq_left hw
  have hR2 : ∀ w : ℂ, 0 < w.im → ut_w_refl Ψ w = conj (Ψ (conj w)) := fun w hw =>
    ite_eq_right (not_le.2 hw)
  have hR2im : ∀ w : ℂ, 0 < w.im → 0 < (ut_w_refl Ψ w).im := fun w hw => by
    rw [hR2 w hw, Complex.conj_im, neg_pos]
    exact hmapL _ (by rw [Complex.conj_im]; linarith)
  -- continuity: the two formulas agree on `ℝ`
  have hRc : Continuous (ut_w_refl Ψ) := by
    show Continuous fun w : ℂ => if w.im ≤ 0 then Ψ w else conj (Ψ (conj w))
    refine Continuous.if_le hc (Complex.continuous_conj.comp (hc.comp Complex.continuous_conj))
      Complex.continuous_im continuous_const fun w hw => ?_
    have hcw : conj w = w := Complex.conj_eq_iff_im.2 hw
    simp only [hcw, hreal w hw]
  -- injectivity: `{Im z ≤ 0}` and `ℍ` are both invariant
  have hRi : Function.Injective (ut_w_refl Ψ) := by
    intro a b hab
    rcases le_or_gt a.im 0 with ha | ha <;> rcases le_or_gt b.im 0 with hb | hb
    · rw [hR1 a ha, hR1 b hb] at hab
      exact hi hab
    · have h1 := hmapLe a ha
      have h2 := hR2im b hb
      rw [hR1 a ha] at hab
      rw [hab] at h1
      linarith
    · have h1 := hR2im a ha
      have h2 := hmapLe b hb
      rw [hR1 b hb] at hab
      rw [hab] at h1
      linarith
    · rw [hR2 a ha, hR2 b hb] at hab
      have h1 : Ψ (conj a) = Ψ (conj b) := by simpa using congrArg conj hab
      simpa using congrArg conj (hi h1)
  -- surjectivity
  have hRs : ut_w_refl Ψ '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    rcases lt_trichotomy w.im 0 with hw | hw | hw
    · have hmem : w ∈ Ψ '' lowerHalf := by rw [hL]; exact hw
      obtain ⟨v, hv, hvw⟩ := hmem
      exact ⟨v, mem_univ v, by rw [hR1 v (le_of_lt (show v.im < 0 from hv)), hvw]⟩
    · exact ⟨w, mem_univ w, by rw [hR1 w hw.le, hreal w hw]⟩
    · have hmem : conj w ∈ Ψ '' lowerHalf := by
        rw [hL]
        show (conj w).im < 0
        rw [Complex.conj_im]
        linarith
      obtain ⟨v, hv, hvw⟩ := hmem
      have hv' : 0 < (conj v).im := by
        rw [Complex.conj_im]
        linarith [show v.im < 0 from hv]
      exact ⟨conj v, mem_univ _, by rw [hR2 _ hv', Complex.conj_conj, hvw, Complex.conj_conj]⟩
  -- the reflection is `1`-q.c. on `ℂ ∖ ℝ`, hence on `ℂ`
  have hhom : IsHomeomorphOnto (ut_w_refl Ψ) univ (ut_w_refl Ψ '' univ) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hRc.continuousOn (injOn_of_injective hRi)
  have hRK : IsKQC (ut_w_refl Ψ) univ 1 := by
    refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_univ le_rfl hhom gzE_volume_im_eq_zero
      ?_ ?_ ?_
    · -- a vertical line meets the real axis in one point
      refine Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => ?_
      simpa using hy
    · -- a horizontal line off the real axis misses it
      have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) :=
        measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
      filter_upwards [h0] with y hy
      refine countable_empty.mono fun x hx => ?_
      exact absurd (by simpa using hx) hy
    · rintro w ⟨-, hw⟩
      have hw' : w.im ≠ 0 := hw
      rcases lt_or_gt_of_ne hw' with hlt | hgt
      · exact ⟨lowerHalf, hK.1, hlt, subset_univ _,
          ad_isKQC_congr hK fun v hv => hR1 v (le_of_lt (show v.im < 0 from hv))⟩
      · refine ⟨conj ⁻¹' lowerHalf, hK.1.preimage Complex.continuous_conj, ?_, subset_univ _,
          ad_isKQC_congr (abR_x_isKQC_conj hK) fun v hv => hR2 v ?_⟩
        · show (conj w).im < 0
          rw [Complex.conj_im]
          linarith
        · have hv' : (conj v).im < 0 := hv
          rw [Complex.conj_im] at hv'
          linarith
  -- a conformal bijection of `ℂ` fixing `0` and `1` is the identity
  have hconf : IsConformalOnto (ut_w_refl Ψ) univ univ := by
    have h := thm7_3_one_qc_conformal hRK
    rwa [hRs] at h
  obtain ⟨a, b, -, hab⟩ := nx_entire_affine hconf
  have h0 : ut_w_refl Ψ 0 = 0 := by
    rw [hR1 0 (le_of_eq Complex.zero_im), hreal 0 Complex.zero_im]
  have h1 : ut_w_refl Ψ 1 = 1 := by
    rw [hR1 1 (le_of_eq Complex.one_im), hreal 1 Complex.one_im]
  have hb : b = 0 := by
    rw [hab, mul_zero, zero_add] at h0
    exact h0
  have ha : a = 1 := by
    rw [hab, hb, mul_one, add_zero] at h1
    exact h1
  rw [← hR1 z hz, hab, ha, hb, one_mul, add_zero]

/-- **W2** (welding core).  Let `f, f'` be q.c. maps of `ℂ` onto `ℂ` which are conformal on `𝕃` and agree on `ℝ`.
Then `Ψ = f⁻¹ ∘ f'` is a q.c. self-map of `ℂ` fixing `ℝ`, so it preserves `ℍ` and `𝕃` (`ut_preserves_halves`); it is
conformal on `𝕃` (`f'(𝕃) = f(Ψ(𝕃)) = f(𝕃)`, where `f⁻¹` is conformal), so it is the identity on `{Im z ≤ 0}`
(`ut_w_eq_self_of_refl`).  Hence `f' = f ∘ Ψ = f` there, and `f'(ℍ) = f(Ψ(ℍ)) = f(ℍ)`. -/
theorem ut_w_core {f f' : ℂ → ℂ} {K K' : ℝ} (hK : IsKQC f univ K) (hfs : f '' univ = univ)
    (hK' : IsKQC f' univ K') (hf's : f' '' univ = univ)
    (hfc : IsConformalOnto f lowerHalf (f '' lowerHalf))
    (hf'c : IsConformalOnto f' lowerHalf (f' '' lowerHalf)) (hx : ∀ x : ℝ, f x = f' x) :
    (∀ z : ℂ, z.im ≤ 0 → f z = f' z) ∧ f '' upperHalf = f' '' upperHalf := by
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  set g := Function.invFunOn f univ
  have hfg : ∀ w, f (g w) = w := fun w => by
    have hw : w ∈ f '' univ := by rw [hfs]; exact mem_univ w
    exact Function.invFunOn_eq hw
  have hgf : ∀ z, g (f z) = z := fun z => hK.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  -- `Ψ = f⁻¹ ∘ f'` is a q.c. self-map of `ℂ` fixing `ℝ`
  have hgK : IsKQC g univ K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hΨK : IsKQC (g ∘ f') univ (K' * K) := thm7_1_comp hK' hgK (subset_univ _)
  have hΨs : (g ∘ f') '' univ = univ := by
    rw [image_comp, hf's]
    exact eq_univ_of_forall fun z => ⟨f z, mem_univ _, hgf z⟩
  have hΨfix : ∀ x : ℝ, (g ∘ f') x = x := fun x => by
    rw [Function.comp_apply, ← hx x, hgf]
  obtain ⟨hU, hL⟩ := ut_preserves_halves hΨK hΨs hΨfix
  -- `f' = f ∘ Ψ`, so `f'(𝕃) = f(𝕃)`
  have hf'eq : ∀ z, f' z = f ((g ∘ f') z) := fun z => (hfg (f' z)).symm
  have hf'L : f' '' lowerHalf = f '' lowerHalf := by
    calc f' '' lowerHalf = (f ∘ (g ∘ f')) '' lowerHalf := image_congr fun z _ => hf'eq z
      _ = f '' lowerHalf := by rw [image_comp, hL]
  -- `Ψ` is conformal on `𝕃`
  have hΨc : IsConformalOnto (Function.invFunOn f lowerHalf ∘ f') lowerHalf lowerHalf :=
    (hfc.symm hLo).comp (by rw [← hf'L]; exact hf'c)
  have hΨ1 : IsKQC (g ∘ f') lowerHalf 1 := by
    refine ad_isKQC_congr (isKQC_one_of_conformal hLo hΨc) fun z hz => ?_
    have hmem : f' z ∈ f '' lowerHalf := by
      rw [← hf'L]
      exact mem_image_of_mem f' hz
    obtain ⟨y, hy, hyz⟩ := hmem
    simp only [Function.comp_apply]
    rw [← hyz, hgf, hfc.2.1.leftInvOn_invFunOn hy]
  -- hence `Ψ = id` on `{Im z ≤ 0}`
  have hid : ∀ z : ℂ, z.im ≤ 0 → (g ∘ f') z = z := fun z hz =>
    ut_w_eq_self_of_refl (continuousOn_univ.1 hΨK.2.2.1.1) (injOn_univ.1 hΨK.2.2.1.2.1) hL hΨfix
      hΨ1 hz
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hf'eq z, hid z hz]
  · calc f '' upperHalf = f '' ((g ∘ f') '' upperHalf) := by rw [hU]
      _ = f' '' upperHalf := by
        rw [← image_comp]
        exact image_congr fun z _ => (hf'eq z).symm

/-- **W** (welding uniqueness).  If `μ ∼ μ'` (`f_μ = f_μ'` on `ℝ`), then `f_μ = f_μ'` on the closed lower half-plane,
and hence `f_μ(ℍ) = f_μ'(ℍ)`: `f_μ⁻¹ ∘ f_μ'` fixes `ℝ`, preserves `𝕃` (W0) and is conformal there, so it is the
identity on `𝕃`. -/
theorem ut_welding {μ μ' : BeltramiH} (h : teichSetoid μ μ') :
    (∀ z : ℂ, z.im ≤ 0 → normalizedSolution μ.1 z = normalizedSolution μ'.1 z) ∧
      normalizedSolution μ.1 '' upperHalf = normalizedSolution μ'.1 '' upperHalf := by
  obtain ⟨⟨K, hK⟩, hfs, -⟩ := ut_spec μ
  obtain ⟨⟨K', hK'⟩, hf's, -⟩ := ut_spec μ'
  exact ut_w_core hK hfs hK' hf's (ut_conformal_lowerHalf μ) (ut_conformal_lowerHalf μ') h

/-- **RG** helper: the complex dilatation of a `K`-q.c. self-map `F` of the plane, cut off to the upper
half-plane, lies in `M`: it is measurable, bounded by `(K - 1)/(K + 1) < 1` a.e., and vanishes on `{Im z ≤ 0}`. -/
theorem ut_rg_indicator_mem {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (upperHalf.indicator (complexDilatation F)) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → upperHalf.indicator (complexDilatation F) z = 0 := by
  have hK1 : (1 : ℝ) ≤ K := hF.2.1
  refine ⟨⟨(K - 1) / (K + 1), div_nonneg (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), ?_, ?_⟩, fun z hz => ?_⟩
  · exact (((measurable_dzbar F).div (measurable_dz F)).indicator
      isOpen_upperHalf.measurableSet).aestronglyMeasurable
  · filter_upwards [(isKQC_maxDilatation_le hF).2] with z hz
    exact le_trans (norm_indicator_le_norm_self _ _) hz
  · exact Set.indicator_of_notMem (show z ∉ upperHalf from fun hu => absurd hz (not_le.2 hu)) _

/-- **RG** helper: if `F = f` on the closed lower half-plane and the complex dilatation of `f` agrees a.e. with a
coefficient `ν` vanishing there, then the complex dilatation of `F` agrees a.e. with its cut-off to `ℍ` (on the
open set `𝕃` the two maps have the same derivative, and `ℝ` is null). -/
theorem ut_rg_indicator_ae_eq {F f ν : ℂ → ℂ} (hFf : ∀ z : ℂ, z.im ≤ 0 → F z = f z)
    (hfd : ∀ᵐ z, complexDilatation f z = ν z) (hν : ∀ z : ℂ, z.im ≤ 0 → ν z = 0) :
    ∀ᵐ z, upperHalf.indicator (complexDilatation F) z = complexDilatation F z := by
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  filter_upwards [hfd, hnull] with z h1 h2
  rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
  · have hev : F =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_lt continuous_im continuous_const :
        IsOpen {w : ℂ | w.im < 0}).mem_nhds hlt] with w hw using hFf w (le_of_lt hw)
    have hder : fderiv ℝ F z = fderiv ℝ f z := hev.fderiv_eq
    have hcd : complexDilatation F z = complexDilatation f z := by
      simp only [complexDilatation, dz, dzbar, hder]
    have hnu : z ∉ upperHalf := fun hu => absurd hlt (not_lt.2 (le_of_lt hu))
    rw [Set.indicator_of_notMem hnu, hcd, h1, hν z hlt.le]
  · exact Set.indicator_of_mem (show z ∈ upperHalf from hgt) _

/-- **RG** helper: for `μ ∼ μ'` and any `ν`, the map `F = f_ν ∘ f_μ⁻¹ ∘ f_μ'` is a q.c. map of the plane onto itself
fixing `0` and `1` (Theorems 7.1, 7.2), and it agrees with `f_ν` on the closed lower half-plane, where `f_μ' = f_μ` by
welding uniqueness. -/
theorem ut_rg_comp_spec {μ μ' : BeltramiH} (h : teichSetoid μ μ') (ν : BeltramiH) {F : ℂ → ℂ}
    (hF : F = normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ ∘ normalizedSolution μ'.1) :
    ∃ K : ℝ, IsKQC F univ K ∧ F '' univ = univ ∧ F 0 = 0 ∧ F 1 = 1 ∧
      ∀ z : ℂ, z.im ≤ 0 → F z = normalizedSolution ν.1 z := by
  subst hF
  obtain ⟨⟨Kμ, hKμ⟩, hsμ, hμ0, hμ1, -⟩ := ut_spec μ
  obtain ⟨⟨Kμ', hKμ'⟩, hsμ', hμ'0, hμ'1, -⟩ := ut_spec μ'
  obtain ⟨⟨Kν, hKν⟩, hsν, hν0, hν1, -⟩ := ut_spec ν
  set g := Function.invFunOn (normalizedSolution μ.1) univ
  have hleft : ∀ z, g (normalizedSolution μ.1 z) = z := fun z =>
    hKμ.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hg : IsKQC g univ Kμ := by
    have hinv := thm7_2_inv hKμ
    rwa [hsμ] at hinv
  have hgs : g '' univ = univ := eq_univ_of_forall fun z => ⟨_, mem_univ _, hleft z⟩
  have hg0 : g 0 = 0 := by
    have h0 := hleft 0
    rwa [hμ0] at h0
  have hg1 : g 1 = 1 := by
    have h1 := hleft 1
    rwa [hμ1] at h1
  refine ⟨Kμ' * Kμ * Kν, thm7_1_comp (thm7_1_comp hKμ' hg (subset_univ _)) hKν (subset_univ _), ?_, ?_, ?_,
    fun z hz => ?_⟩
  · rw [image_comp, image_comp, hsμ', hgs, hsν]
  · simp only [Function.comp_apply, hμ'0, hg0, hν0]
  · simp only [Function.comp_apply, hμ'1, hg1, hν1]
  · simp only [Function.comp_apply]
    rw [← (ut_welding h).1 z hz, hleft z]

/-- **RG** (transport).  If `μ ∼ μ'`, then for every `ν` there is `ν' ∼ ν` with `f_ν' = f_ν ∘ f_μ⁻¹ ∘ f_μ'`
(`ν'` is the Beltrami coefficient of `f_ν ∘ f_μ⁻¹ ∘ f_μ'` on `ℍ`, extended by `0`). -/
theorem ut_transport {μ μ' : BeltramiH} (h : teichSetoid μ μ') (ν : BeltramiH) :
    ∃ ν' : BeltramiH, teichSetoid ν' ν ∧
      normalizedSolution ν'.1 =
        normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ ∘ normalizedSolution μ'.1 := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F =
      normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ ∘ normalizedSolution μ'.1 :=
    ⟨_, rfl⟩
  rw [← hFdef]
  obtain ⟨K, hF, hFs, hF0, hF1, hFν⟩ := ut_rg_comp_spec h ν hFdef
  have hnorm : normalizedSolution (upperHalf.indicator (complexDilatation F)) = F := by
    obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ⟨upperHalf.indicator (complexDilatation F), ut_rg_indicator_mem hF⟩
    refine thm13_5_uniqueness_plane hq ⟨K, hF⟩ hs hFs ?_ hq0 hq1 hF0 hF1
    filter_upwards [hd, ut_rg_indicator_ae_eq hFν (ut_spec ν).2.2.2.2 ν.2.2] with z h1 h2
    exact h1.trans h2
  refine ⟨⟨upperHalf.indicator (complexDilatation F), ut_rg_indicator_mem hF⟩, fun x => ?_, hnorm⟩
  show normalizedSolution (upperHalf.indicator (complexDilatation F)) x = normalizedSolution ν.1 x
  rw [hnorm]
  exact hFν x (le_of_eq (ofReal_im x))

/-- The coefficient `t μ` (with `t` clamped to `[0, 1]`) lies in `M`. -/
theorem ut_scale_mem (μ : BeltramiH) (t : ℝ) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (fun z => ((max 0 (min 1 t) : ℝ) : ℂ) * μ.1 z) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → ((max 0 (min 1 t) : ℝ) : ℂ) * μ.1 z = 0 := by
  obtain ⟨⟨k, hk0, hk1, hμm, hμb⟩, hμ0⟩ := μ.2
  refine ⟨⟨k, hk0, hk1, hμm.const_mul _, ?_⟩, fun z hz => by rw [hμ0 z hz, mul_zero]⟩
  filter_upwards [hμb] with z hz
  have h0 : 0 ≤ max 0 (min 1 t) := le_max_left _ _
  have h1 : max 0 (min 1 t) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  calc max 0 (min 1 t) * ‖μ.1 z‖ ≤ 1 * k := mul_le_mul h1 hz (norm_nonneg _) zero_le_one
    _ = k := one_mul k

/-- The path `t ↦ t μ` in `M` (`t` clamped to `[0, 1]`). -/
def ut_scale (μ : BeltramiH) (t : ℝ) : BeltramiH :=
  ⟨fun z => ((max 0 (min 1 t) : ℝ) : ℂ) * μ.1 z, ut_scale_mem μ t⟩

namespace UniversalTeichmuller

/-- The origin of `T`: the class of `μ = 0`. -/
def origin : UniversalTeichmuller :=
  Quotient.mk teichSetoid ⟨0, ⟨0, le_refl 0, zero_lt_one, aestronglyMeasurable_const, by simp⟩,
    fun _ _ => rfl⟩

/-- The Teichmüller distance
`d(p, q) = inf {ln K[g ∘ f⁻¹] : f ∈ p, g ∈ q}`, with `f = f_μ`, `g = f_ν` and `K[·]` the
maximal dilatation on `f_μ(ℍ)`.

Written as the `sInf` of a set of reals.  The nested form `⨅ μ ν (_ : [μ] = p ∧ [ν] = q), …` is
identically `0` in `ℝ`: for every pair not in the classes the innermost infimum is over an empty
proposition, i.e. `sInf ∅ = 0`, and the values are `≥ 0` (corrected 2026-09-25). -/
def dist (p q : UniversalTeichmuller) : ℝ :=
  sInf {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
    d = Real.log (maxDilatation (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ)
      (normalizedSolution μ.1 '' upperHalf)).toReal}

/-- The essential supremum `‖(μ - ν)/(1 - ν̄μ)‖_∞` over `ℍ`. -/
def dilatationDiffNorm (μ ν : ℂ → ℂ) : ℝ :=
  (essSup (fun z => (‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)).toReal

/-! ### §21.1 metric track interface, part 2 (coordinator 553e2d): the pointwise (21.4) and `dilatationDiffNorm` -/

/-- Change of variables in an essential supremum through a `K`-q.c. map `f` of `U`: `f` and `f⁻¹` both send null
sets to null sets (Lusin's property (N), `abT_ae_image`), so `ess sup_{f(U)} φ = ess sup_U (φ ∘ f)`. -/
theorem ut_e_essSup_image {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) (φ : ℂ → ℝ≥0∞) :
    essSup φ (volume.restrict (f '' U)) = essSup (fun z => φ (f z)) (volume.restrict U) := by
  have hleft : LeftInvOn (Function.invFunOn f U) f U := hf.2.2.1.2.1.leftInvOn_invFunOn
  refine le_antisymm (essSup_le_of_ae_le _ ?_) (essSup_le_of_ae_le _ ?_)
  · exact abT_ae_image hf (p := fun w => φ w ≤ essSup (fun z => φ (f z)) (volume.restrict U))
      (ENNReal.ae_le_essSup (fun z => φ (f z)))
  · have h := abT_ae_image (thm7_2_inv hf)
      (p := fun z => φ (f z) ≤ essSup φ (volume.restrict (f '' U))) (by
        filter_upwards [ENNReal.ae_le_essSup φ,
          ae_restrict_mem (isOpen_image_of_isKQC hf).measurableSet] with w hw hwD
        obtain ⟨z, hz, rfl⟩ := hwD
        show φ (f (Function.invFunOn f U (f z))) ≤ _
        rw [hleft hz]
        exact hw)
    rwa [hleft.image_image] at h

/-- The dilatation quotient in terms of the complex dilatation: for `a ≠ 0`,
`(|a| + |b|)/(|a| - |b|) = (1 + |b/a|)/(1 - |b/a|)`. -/
theorem ut_e_quot_eq {a b : ℂ} (ha : a ≠ 0) :
    (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) = (1 + ‖b / a‖) / (1 - ‖b / a‖) := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  rw [norm_div, ← div_div_div_cancel_right₀ hna (‖a‖ + ‖b‖), add_div, sub_div, div_self hna]

/-- `|(b - a)/(1 - ā b)| = |(a - b)/(1 - b̄ a)|`: the numerators differ by a sign and the denominators are
complex conjugate. -/
theorem ut_e_norm_quot_symm (a b : ℂ) :
    ‖(b - a) / (1 - conj a * b)‖ = ‖(a - b) / (1 - conj b * a)‖ := by
  rw [norm_div, norm_div, norm_sub_rev b a, ← Complex.norm_conj (1 - conj a * b)]
  congr 2
  rw [map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]

/-- `t ↦ (1 + t)/(1 - t)` commutes with the essential supremum: if `0 ≤ ρ ≤ c < 1` a.e. for a nonzero measure,
then `ess sup (1 + ρ)/(1 - ρ) = (1 + ess sup ρ)/(1 - ess sup ρ)` (a continuous monotone map passes through the
`limsup`, `Monotone.map_limsup_of_continuousAt`, after clamping at `c`). -/
theorem ut_e_essSup_quot {m : Measure ℂ} (hm : m ≠ 0) {ρ : ℂ → ℝ} {c : ℝ} (hc : c < 1)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρc : ∀ᵐ z ∂m, ρ z ≤ c) :
    essSup (fun z => ENNReal.ofReal ((1 + ρ z) / (1 - ρ z))) m =
      ENNReal.ofReal ((1 + (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal) /
        (1 - (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal)) := by
  have hne : (ae m).NeBot := ae_neBot.2 hm
  obtain ⟨z₀, hz₀⟩ := hρc.exists
  have hc0 : 0 ≤ c := (hρ0 z₀).trans hz₀
  set c' : ℝ≥0∞ := ENNReal.ofReal c
  have hc't : c' ≠ ⊤ := ENNReal.ofReal_ne_top
  set T : ℝ≥0∞ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 + (min x c').toReal) / (1 - (min x c').toReal)) with hT
  have hmin : ∀ x : ℝ≥0∞, 0 ≤ (min x c').toReal ∧ (min x c').toReal ≤ c := fun x =>
    ⟨ENNReal.toReal_nonneg, by
      rw [← ENNReal.toReal_ofReal hc0]
      exact ENNReal.toReal_mono hc't (min_le_right _ _)⟩
  have hTmono : Monotone T := by
    intro x y hxy
    have hs := hmin x
    have ht := hmin y
    have hst : (min x c').toReal ≤ (min y c').toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hc't (min_le_right _ _)) (min_le_min_right _ hxy)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hTcont : Continuous T := by
    have h1 : Continuous fun x : ℝ≥0∞ => (min x c').toReal :=
      ENNReal.continuousOn_toReal.comp_continuous (continuous_id.min continuous_const)
        fun x => ne_top_of_le_ne_top hc't (min_le_right _ _)
    refine ENNReal.continuous_ofReal.comp ((continuous_const.add h1).div (continuous_const.sub h1) ?_)
    intro x
    have := hmin x
    linarith
  have hE : essSup (fun z => ENNReal.ofReal (ρ z)) m ≤ c' :=
    essSup_le_of_ae_le _ (by filter_upwards [hρc] with z hz using ENNReal.ofReal_le_ofReal hz)
  have key := hTmono.map_limsup_of_continuousAt (F := ae m) (fun z => ENNReal.ofReal (ρ z))
    hTcont.continuousAt
  have h1 : T (essSup (fun z => ENNReal.ofReal (ρ z)) m) =
      ENNReal.ofReal ((1 + (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal) /
        (1 - (essSup (fun z => ENNReal.ofReal (ρ z)) m).toReal)) := by
    simp only [hT, min_eq_left hE]
  have h2 : (T ∘ fun z => ENNReal.ofReal (ρ z)) =ᵐ[m] fun z => ENNReal.ofReal ((1 + ρ z) / (1 - ρ z)) := by
    filter_upwards [hρc] with z hz
    have hle : ENNReal.ofReal (ρ z) ≤ c' := ENNReal.ofReal_le_ofReal hz
    simp only [Function.comp_apply, hT, min_eq_left hle, ENNReal.toReal_ofReal (hρ0 z)]
  rw [← h1, ← essSup_congr_ae h2]
  exact key.symm

/-- **E** (pointwise (21.4)).  `‖(μ - ν)/(1 - ν̄μ)‖_∞ < 1` and
`ln K[f_ν ∘ f_μ⁻¹ | f_μ(ℍ)] = ln((1 + ‖(μ - ν)/(1 - ν̄μ)‖_∞)/(1 - ‖(μ - ν)/(1 - ν̄μ)‖_∞))`: the complex dilatation of
`f_ν ∘ f_μ⁻¹` at `f_μ(z)` has modulus `|(ν - μ)/(1 - μ̄ν)|(z)`, and the essential supremum is transported by `f_μ`,
which preserves null sets in both directions. -/
theorem ut_v_eq (μ ν : BeltramiH) :
    dilatationDiffNorm μ.1 ν.1 < 1 ∧
      ut_v μ ν = Real.log ((1 + dilatationDiffNorm μ.1 ν.1) / (1 - dilatationDiffNorm μ.1 ν.1)) := by
  obtain ⟨⟨Kμ, hKμ⟩, himgμ, -, -, hdμ⟩ := ut_spec μ
  obtain ⟨⟨Kν, hKν⟩, -, -, -, hdν⟩ := ut_spec ν
  obtain ⟨⟨kμ, hkμ0, hkμ1, -, hbμ⟩, -⟩ := μ.2
  obtain ⟨⟨kν, -, hkν1, -, hbν⟩, -⟩ := ν.2
  rw [Measure.restrict_univ] at hbμ hbν
  unfold ut_v
  set f := normalizedSolution μ.1
  set F := normalizedSolution ν.1 ∘ Function.invFunOn f univ
  set ρ : ℂ → ℝ := fun z => ‖(μ.1 z - ν.1 z) / (1 - conj (ν.1 z) * μ.1 z)‖ with hρdef
  -- `ρ ≤ 2k/(1 + k²) < 1` a.e.
  have hk0 : 0 ≤ max kμ kν := le_max_of_le_left hkμ0
  have hk1 : max kμ kν < 1 := max_lt hkμ1 hkν1
  have hc1 : 2 * max kμ kν / (1 + max kμ kν ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - max kμ kν)]
  have hρc : ∀ᵐ z, ρ z ≤ 2 * max kμ kν / (1 + max kμ kν ^ 2) := by
    filter_upwards [hbμ, hbν] with z h1 h2
    exact ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
  -- `f⁻¹` and `F = f_ν ∘ f⁻¹` are q.c. on the plane
  have hleft : LeftInvOn (Function.invFunOn f univ) f univ := hKμ.2.2.1.2.1.leftInvOn_invFunOn
  have hright : ∀ w, f (Function.invFunOn f univ w) = w := by
    intro w
    apply Function.invFunOn_eq
    have hw : w ∈ f '' univ := by rw [himgμ]; exact mem_univ w
    obtain ⟨z, hz, hzw⟩ := hw
    exact ⟨z, hz, hzw⟩
  have hinv : IsKQC (Function.invFunOn f univ) univ Kμ := by
    have h := thm7_2_inv hKμ
    rwa [himgμ] at h
  have hinvimg : Function.invFunOn f univ '' univ = univ := by
    have h := hleft.image_image
    rwa [himgμ] at h
  have hFK : IsKQC F univ (Kμ * Kν) := thm7_1_comp hinv hKν (subset_univ _)
  -- a.e. `z`: `J_F(f z) > 0` (Lusin's property (N) for `f⁻¹`)
  have hJF : ∀ᵐ z, 0 < jacobian F (f z) := by
    have h := abT_ae_image hinv (p := fun z => 0 < jacobian F (f z)) (by
      filter_upwards [thm9_6_cor2_jacobian_pos hFK] with w hw
      show 0 < jacobian F (f (Function.invFunOn f univ w))
      rw [hright w]
      exact hw)
    rwa [hinvimg, Measure.restrict_univ] at h
  -- the pointwise identity: a.e., the dilatation quotient of `F` at `f z` is `(1 + ρ z)/(1 - ρ z)`
  have hpt : ∀ᵐ z, ENNReal.ofReal ((‖dz F (f z)‖ + ‖dzbar F (f z)‖) / (‖dz F (f z)‖ - ‖dzbar F (f z)‖)) =
      ENNReal.ofReal ((1 + ρ z) / (1 - ρ z)) := by
    have hC := ahQ_comp_inv_dilatation hKν hKμ
    have hJf := thm9_6_cor2_jacobian_pos hKμ
    rw [Measure.restrict_univ] at hC hJf
    filter_upwards [hC, hJf, hJF, hdμ, hdν] with z hCz hJfz hJFz h1 h2
    have hdz : dz f z ≠ 0 := by
      intro h0
      unfold jacobian at hJfz
      rw [h0, norm_zero] at hJfz
      nlinarith [norm_nonneg (dzbar f z)]
    have hdzF : dz F (f z) ≠ 0 := by
      intro h0
      unfold jacobian at hJFz
      rw [h0, norm_zero] at hJFz
      nlinarith [norm_nonneg (dzbar F (f z))]
    have hμF : ‖dzbar F (f z) / dz F (f z)‖ = ρ z := by
      change ‖complexDilatation F (f z)‖ = _
      rw [hCz, h1, h2, norm_mul, ut_e_norm_quot_symm, norm_div (dz f z), Complex.norm_conj,
        div_self (norm_ne_zero_iff.2 hdz), mul_one]
    rw [ut_e_quot_eq hdzF, hμF]
  -- the essential suprema
  have hm : volume.restrict upperHalf ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩
  have hnn : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := fun x => (ofReal_norm x).symm
  have hd : dilatationDiffNorm μ.1 ν.1 =
      (essSup (fun z => ENNReal.ofReal (ρ z)) (volume.restrict upperHalf)).toReal := by
    simp only [dilatationDiffNorm, hnn, hρdef]
  have hkey : maxDilatation F (f '' upperHalf) =
      ENNReal.ofReal ((1 + dilatationDiffNorm μ.1 ν.1) / (1 - dilatationDiffNorm μ.1 ν.1)) := by
    rw [maxDilatation, ut_e_essSup_image (ac_t_isKQC_restrict hKμ isOpen_upperHalf (subset_univ _)),
      essSup_congr_ae (ae_restrict_of_ae hpt),
      ut_e_essSup_quot hm hc1 (fun z => norm_nonneg _) (ae_restrict_of_ae hρc), hd]
  have hd1 : dilatationDiffNorm μ.1 ν.1 < 1 := by
    refine lt_of_le_of_lt ?_ hc1
    rw [hd]
    refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith) (by positivity))
      (essSup_le_of_ae_le _ ?_)
    filter_upwards [ae_restrict_of_ae hρc] with z hz
    exact ENNReal.ofReal_le_ofReal hz
  have hd0 : 0 ≤ dilatationDiffNorm μ.1 ν.1 := ENNReal.toReal_nonneg
  refine ⟨hd1, ?_⟩
  rw [hkey, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

/-- **MD** (lower bound).  If `g` is `K`-q.c. on a nonempty open set `D`, then `1 ≤ K[g]` on `D`: the Jacobian
is positive a.e., so the dilatation quotient is `≥ 1` a.e., and `D` has positive measure. -/
theorem ut_md_one_le {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K) (hne : D.Nonempty) :
    1 ≤ maxDilatation g D := by
  have hμ : volume.restrict D ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact hg.1.measure_ne_zero volume hne
  calc (1 : ℝ≥0∞) = essSup (fun _ : ℂ => (1 : ℝ≥0∞)) (volume.restrict D) := (essSup_const _ hμ).symm
    _ ≤ maxDilatation g D := by
      refine essSup_mono_ae ?_
      filter_upwards [thm9_6_cor2_jacobian_pos hg] with z hz
      unfold jacobian at hz
      have hlt : ‖dzbar g z‖ < ‖dz g z‖ := by
        nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ (by linarith)]
      linarith [norm_nonneg (dzbar g z)]

/-- **MD** (converse of `isKQC_maxDilatation_le`).  A q.c. map `g` of an open set `D` with `K[g] ≤ K`, `1 ≤ K`,
is `K`-q.c.: by Theorem 10.1, since `g` is A.C.L. (Theorem 9.1) and the dilatation inequality holds a.e.
(`J_g > 0` a.e., Theorem 9.6). -/
theorem ut_md_isKQC_of_le {g : ℂ → ℂ} {D : Set ℂ} {K₀ K : ℝ} (hg : IsKQC g D K₀) (hK : 1 ≤ K)
    (hle : maxDilatation g D ≤ ENNReal.ofReal K) : IsKQC g D K := by
  refine (thm10_1_isKQC_iff hg.1 hK hg.2.2.1).2 ⟨thm9_1_isACL hg, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict D)
      (fun z => ENNReal.ofReal ((‖dz g z‖ + ‖dzbar g z‖) / (‖dz g z‖ - ‖dzbar g z‖))),
    thm9_6_cor2_jacobian_pos hg] with z hz hJ
  unfold jacobian at hJ
  have hlt : ‖dzbar g z‖ < ‖dz g z‖ := by
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have h1 : ENNReal.ofReal ((‖dz g z‖ + ‖dzbar g z‖) / (‖dz g z‖ - ‖dzbar g z‖)) ≤ ENNReal.ofReal K :=
    hz.trans hle
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith), div_le_iff₀ (by linarith)] at h1
  exact h1

/-- **MD.** For a q.c. map `g` of a nonempty open set `D`, `K[g]` is finite and `≥ 1`, and `g` is
`K[g]`-q.c. -/
theorem ut_md_isKQC_toReal {g : ℂ → ℂ} {D : Set ℂ} {K₀ : ℝ} (hg : IsKQC g D K₀) (hne : D.Nonempty) :
    1 ≤ (maxDilatation g D).toReal ∧ IsKQC g D (maxDilatation g D).toReal := by
  have hfin : maxDilatation g D ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hg).1
  have h1 : 1 ≤ (maxDilatation g D).toReal := by
    simpa using ENNReal.toReal_mono hfin (ut_md_one_le hg hne)
  exact ⟨h1, ut_md_isKQC_of_le hg h1 (ENNReal.ofReal_toReal hfin).ge⟩

/-- **MD.** `f_μ⁻¹ ∘ f_μ = id` (`f_μ` is injective). -/
theorem ut_md_leftInv (σ : BeltramiH) (z : ℂ) :
    Function.invFunOn (normalizedSolution σ.1) univ (normalizedSolution σ.1 z) = z := by
  obtain ⟨K, hK⟩ := (ut_spec σ).1
  exact hK.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)

/-- **MD.** `f_ν ∘ f_μ⁻¹` is quasiconformal on the open set `f_μ(ℍ)` (Theorems 7.1 and 7.2). -/
theorem ut_md_trans_isKQC (μ ν : BeltramiH) :
    ∃ K : ℝ, IsKQC (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ)
      (normalizedSolution μ.1 '' upperHalf) K := by
  obtain ⟨Kμ, hμ⟩ := (ut_spec μ).1
  obtain ⟨Kν, hν⟩ := (ut_spec ν).1
  have hinv := thm7_2_inv hμ
  rw [(ut_spec μ).2.1] at hinv
  exact ⟨Kμ * Kν, ac_t_isKQC_restrict (thm7_1_comp hinv hν (subset_univ _))
    (isOpen_image_of_isKQC (ac_t_isKQC_restrict hμ isOpen_upperHalf (subset_univ _))) (subset_univ _)⟩

/-- **MD** (subadditivity along compositions): `v(μ, ρ) ≤ v(μ, ν) + v(ν, ρ)`, since
`f_ρ ∘ f_μ⁻¹ = (f_ρ ∘ f_ν⁻¹) ∘ (f_ν ∘ f_μ⁻¹)` and maximal dilatations multiply at most (Theorem 7.1). -/
theorem ut_v_triangle (μ ν ρ : BeltramiH) : ut_v μ ρ ≤ ut_v μ ν + ut_v ν ρ := by
  have hne : ∀ σ : BeltramiH, (normalizedSolution σ.1 '' upperHalf).Nonempty := fun σ =>
    ⟨_, mem_image_of_mem _ (show I ∈ upperHalf by simp [upperHalf])⟩
  obtain ⟨K₁, hA⟩ := ut_md_trans_isKQC μ ν
  obtain ⟨K₂, hB⟩ := ut_md_trans_isKQC ν ρ
  obtain ⟨K₃, hC⟩ := ut_md_trans_isKQC μ ρ
  obtain ⟨h1, hA'⟩ := ut_md_isKQC_toReal hA (hne μ)
  obtain ⟨h2, hB'⟩ := ut_md_isKQC_toReal hB (hne ν)
  have h3 := (ut_md_isKQC_toReal hC (hne μ)).1
  have himg : (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ) ''
      (normalizedSolution μ.1 '' upperHalf) ⊆ normalizedSolution ν.1 '' upperHalf := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by rw [Function.comp_apply, ut_md_leftInv μ z]⟩
  have hcomp : (normalizedSolution ρ.1 ∘ Function.invFunOn (normalizedSolution ν.1) univ) ∘
      (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ) =
      normalizedSolution ρ.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ := by
    funext w
    simp only [Function.comp_apply, ut_md_leftInv ν]
  have hBA := thm7_1_comp hA' hB' himg
  rw [hcomp] at hBA
  have hle := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by linarith) (by linarith))
    (isKQC_maxDilatation_le hBA).1
  unfold ut_v
  rw [← Real.log_mul (by linarith) (by linarith)]
  exact Real.log_le_log (by linarith) hle

/-- Pointwise symmetry of the integrand of `dilatationDiffNorm`: `|a - b|/|1 - b̄a| = |b - a|/|1 - āb|`, since
`1 - āb` is the conjugate of `1 - b̄a` (both sides are `0` when the denominator vanishes). -/
theorem ut_s_pt_symm (a b : ℂ) : ‖(a - b) / (1 - conj b * a)‖₊ = ‖(b - a) / (1 - conj a * b)‖₊ := by
  have h : 1 - conj a * b = conj (1 - conj b * a) := by
    rw [map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]
  apply NNReal.eq
  rw [coe_nnnorm, coe_nnnorm, norm_div, norm_div, norm_sub_rev a b, h, Complex.norm_conj]

/-- `‖(μ - ν)/(1 - ν̄μ)‖_∞ = ‖(ν - μ)/(1 - μ̄ν)‖_∞` (`|1 - ν̄μ| = |1 - μ̄ν|`, so both quotients vanish at the same
points). -/
theorem ut_d_symm (μ ν : ℂ → ℂ) : dilatationDiffNorm μ ν = dilatationDiffNorm ν μ := by
  simp only [dilatationDiffNorm, ut_s_pt_symm (μ _)]

/-- `‖(μ - μ)/(1 - μ̄μ)‖_∞ = 0`. -/
theorem ut_d_self (μ : ℂ → ℂ) : dilatationDiffNorm μ μ = 0 := by
  have h0 : essSup (fun _ : ℂ => (0 : ℝ≥0∞)) (volume.restrict upperHalf) = 0 := essSup_const_bot
  simp only [dilatationDiffNorm, sub_self, zero_div, nnnorm_zero, ENNReal.coe_zero, h0, ENNReal.toReal_zero]

/-- The clamp `t ↦ max 0 (min 1 t)` is `1`-Lipschitz. -/
theorem ut_s_clamp_lip (t t₀ : ℝ) : |max 0 (min 1 t) - max 0 (min 1 t₀)| ≤ |t - t₀| := by
  calc |max 0 (min 1 t) - max 0 (min 1 t₀)| ≤ max |0 - 0| |min 1 t - min 1 t₀| :=
        abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |0 - 0| (max |1 - 1| |t - t₀|) := max_le_max le_rfl (abs_min_sub_min_le_max _ _ _ _)
    _ = |t - t₀| := by
        rw [sub_self, sub_self, abs_zero, max_eq_right (abs_nonneg (t - t₀)),
          max_eq_right (abs_nonneg (t - t₀))]

/-- Pointwise bound along the path: for `s ∈ [0, 1]`, `s₀ ≤ 1` and `‖a‖ ≤ k < 1`,
`|s a - s₀ a|/|1 - conj(s₀ a)(s a)| ≤ |s - s₀| k/(1 - k²)` (the denominator is `1 - s₀ s ‖a‖² ≥ 1 - k² > 0`). -/
theorem ut_s_pt_scale (a : ℂ) {k s s₀ : ℝ} (hk1 : k < 1) (ha : ‖a‖ ≤ k)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs₀1 : s₀ ≤ 1) :
    ‖((s : ℂ) * a - (s₀ : ℂ) * a) / (1 - conj ((s₀ : ℂ) * a) * ((s : ℂ) * a))‖ ≤
      |s - s₀| * k / (1 - k ^ 2) := by
  have hden : 1 - conj ((s₀ : ℂ) * a) * ((s : ℂ) * a) = ((1 - s₀ * s * ‖a‖ ^ 2 : ℝ) : ℂ) := by
    have hc := Complex.conj_mul' a
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    rw [← hc]
    ring
  have hna : 0 ≤ ‖a‖ := norm_nonneg a
  have hk0 : 0 ≤ k := hna.trans ha
  have hq : s₀ * s * ‖a‖ ^ 2 ≤ k ^ 2 := by
    have h1 : s₀ * s ≤ 1 * 1 := mul_le_mul hs₀1 hs1 hs0 zero_le_one
    have h2 : ‖a‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hna ha 2
    calc s₀ * s * ‖a‖ ^ 2 ≤ (1 * 1) * k ^ 2 := mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
      _ = k ^ 2 := by ring
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hpos : 0 < 1 - s₀ * s * ‖a‖ ^ 2 := by linarith
  rw [hden, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, ← sub_mul, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div₀ (mul_nonneg (abs_nonneg _) hk0) (mul_le_mul_of_nonneg_left ha (abs_nonneg _)) hk2
    (by linarith)

/-- Along the path: `‖(tμ - t₀μ)/(1 - t₀ t |μ|²)‖_∞ ≤ |t - t₀| k/(1 - k²)` when `‖μ‖_∞ ≤ k < 1`. -/
theorem ut_d_scale_le (μ : BeltramiH) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hμ : IsBeltramiCoeff μ.1 univ k)
    (t t₀ : ℝ) : dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1 ≤ |t - t₀| * k / (1 - k ^ 2) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hC : 0 ≤ |t - t₀| * k / (1 - k ^ 2) := div_nonneg (mul_nonneg (abs_nonneg _) hk0) hk2.le
  apply ENNReal.toReal_le_of_le_ofReal hC
  refine essSup_le_of_ae_le _ ?_
  have hae : ∀ᵐ z ∂volume, ‖μ.1 z‖ ≤ k := by
    have h := hμ.2
    rwa [Measure.restrict_univ] at h
  filter_upwards [ae_restrict_of_ae hae] with z hz
  simp only [ut_scale]
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc _ ≤ |max 0 (min 1 t) - max 0 (min 1 t₀)| * k / (1 - k ^ 2) :=
        ut_s_pt_scale _ hk1 hz (le_max_left _ _) (max_le zero_le_one (min_le_left _ _))
          (max_le zero_le_one (min_le_left _ _))
    _ ≤ |t - t₀| * k / (1 - k ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (ut_s_clamp_lip t t₀) hk0) hk2.le

/-- `dist` in terms of `ut_v`. -/
theorem ut_dist_def (p q : UniversalTeichmuller) :
    dist p q = sInf {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
      d = ut_v μ ν} := rfl

/-- `v(μ, ν) ≥ 0` (by (21.4) pointwise, `(1 + d)/(1 - d) ≥ 1` for `0 ≤ d < 1`). -/
theorem ut_v_nonneg (μ ν : BeltramiH) : 0 ≤ ut_v μ ν := by
  obtain ⟨h1, h2⟩ := ut_v_eq μ ν
  have h0 : 0 ≤ dilatationDiffNorm μ.1 ν.1 := ENNReal.toReal_nonneg
  rw [h2]
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `v(μ, ν) = v(ν, μ)`. -/
theorem ut_v_symm (μ ν : BeltramiH) : ut_v μ ν = ut_v ν μ := by
  rw [(ut_v_eq μ ν).2, (ut_v_eq ν μ).2, ut_d_symm]

/-- The value set of `dist p q` is bounded below by `0`. -/
theorem ut_bddBelow (p q : UniversalTeichmuller) :
    BddBelow {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
      d = ut_v μ ν} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨μ, ν, -, -, rfl⟩
  exact ut_v_nonneg μ ν

/-- `dist p q ≤ v(μ, ν)` for representatives `μ ∈ p`, `ν ∈ q`. -/
theorem ut_dist_le {p q : UniversalTeichmuller} {μ ν : BeltramiH} (hμ : Quotient.mk teichSetoid μ = p)
    (hν : Quotient.mk teichSetoid ν = q) : dist p q ≤ ut_v μ ν :=
  csInf_le (ut_bddBelow p q) ⟨μ, ν, hμ, hν, rfl⟩

/-- For `ε > 0` there are representatives with `v(μ, ν) < dist p q + ε`. -/
theorem ut_dist_lt (p q : UniversalTeichmuller) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
      ut_v μ ν < dist p q + ε := by
  have hne : {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
      d = ut_v μ ν}.Nonempty :=
    ⟨_, p.out, q.out, Quotient.out_eq p, Quotient.out_eq q, rfl⟩
  obtain ⟨_, ⟨μ, ν, hμ, hν, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (dist p q) hε)
  exact ⟨μ, ν, hμ, hν, hlt⟩

/-- §21.1: `d(p, p) = 0` and `d(p, q) = d(q, p)`. -/
theorem dist_self_symm (p q : UniversalTeichmuller) : dist p p = 0 ∧ dist p q = dist q p := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · obtain ⟨μ, rfl⟩ := Quotient.exists_rep p
    calc dist _ _ ≤ ut_v μ μ := ut_dist_le rfl rfl
      _ = 0 := by rw [(ut_v_eq μ μ).2, ut_d_self]; norm_num
  · have hne : {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = p ∧
        d = ut_v μ ν}.Nonempty :=
      ⟨_, p.out, p.out, Quotient.out_eq p, Quotient.out_eq p, rfl⟩
    rw [ut_dist_def]
    refine le_csInf hne ?_
    rintro _ ⟨μ, ν, -, -, rfl⟩
    exact ut_v_nonneg μ ν
  · rw [ut_dist_def, ut_dist_def]
    congr 1
    ext d
    constructor
    · rintro ⟨μ, ν, hμ, hν, rfl⟩
      exact ⟨ν, μ, hν, hμ, ut_v_symm μ ν⟩
    · rintro ⟨μ, ν, hμ, hν, rfl⟩
      exact ⟨ν, μ, hν, hμ, ut_v_symm μ ν⟩

/-- §21.1: the triangle inequality. -/
theorem dist_triangle (p q r : UniversalTeichmuller) : dist p r ≤ dist p q + dist q r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨μ, ν, hμ, hν, h1⟩ := ut_dist_lt p q (half_pos hε)
  obtain ⟨ν', ρ, hν', hρ, h2⟩ := ut_dist_lt q r (half_pos hε)
  have hνν' : teichSetoid ν' ν := Quotient.exact (hν'.trans hν.symm)
  obtain ⟨ρ'', hρρ, hfρ⟩ := ut_transport hνν' ρ
  have hρ'' : Quotient.mk teichSetoid ρ'' = r := (Quotient.sound hρρ).trans hρ
  have hsurj : normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution ν.1) univ = id := by
    funext w
    have hw : w ∈ normalizedSolution ν.1 '' univ := by rw [(ut_spec ν).2.1]; exact mem_univ w
    exact Function.invFunOn_eq hw
  have hcomp : normalizedSolution ρ''.1 ∘ Function.invFunOn (normalizedSolution ν.1) univ =
      normalizedSolution ρ.1 ∘ Function.invFunOn (normalizedSolution ν'.1) univ := by
    rw [hfρ]
    funext w
    have := congrFun hsurj w
    simp only [Function.comp_apply, id] at this ⊢
    rw [this]
  have hv : ut_v ν ρ'' = ut_v ν' ρ := by
    unfold ut_v
    rw [hcomp, (ut_welding hνν').2]
  calc dist p r ≤ ut_v μ ρ'' := ut_dist_le hμ hρ''
    _ ≤ ut_v μ ν + ut_v ν ρ'' := ut_v_triangle μ ν ρ''
    _ = ut_v μ ν + ut_v ν' ρ := by rw [hv]
    _ ≤ dist p q + dist q r + ε := by linarith

/-! ### §21.1-B track interface (coordinator 553e2d): attainment (21.1) and `d(p, q) = 0 ⇒ p = q` -/

/-- **NB** (growth bound): a normalized `K`-q.c. map of the plane satisfies `|f(z)| ≤ λ(K Λ(R))` for `|z| ≤ R`
(Theorem 15.3 and the radial lower bound `td_dist_lower` give `Λ(|f(z)|) ≤ K Λ(|z|)`). -/
theorem ut2_nb_upper {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖z‖ ≤ R) : ‖f z‖ ≤ lambdaInv (K * quadLambda R) := by
  obtain ⟨hqc, hs, h0, h1⟩ := hf
  have hK : 1 ≤ K := hqc.2.1
  have hΛR : 0 < quadLambda R := b4_num_quadLambda_pos hR
  have hinj := hqc.2.2.1.2.1
  by_cases hz0 : z = 0
  · rw [hz0, h0, norm_zero]
    exact (td_quadLambda_lambdaInv (mul_pos (by linarith) hΛR)).1.le
  by_cases hz1 : z = 1
  · rw [hz1, norm_one] at hz
    rw [hz1, h1, norm_one]
    refine b4_le_lambdaInv one_pos ?_
    rw [b4_quadLambda_one]
    have hΛR1 : 1 ≤ quadLambda R := by
      rw [← b4_quadLambda_one]
      exact quadLambda_strictMono.1.monotoneOn (mem_Ioi.2 one_pos) hR hz
    exact one_le_mul_of_one_le_of_one_le hK hΛR1
  have hfz0 : f z ≠ 0 := fun h => hz0 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
  have hfz1 : f z ≠ 1 := fun h => hz1 (hinj (mem_univ _) (mem_univ _) (h.trans h1.symm))
  have hteich := thm15_3_teichmuller ⟨hqc, hs, h0, h1⟩ hz0 hz1
  have hlow := td_dist_lower ⟨hz0, hz1⟩ ⟨hfz0, hfz1⟩
  have habs : |Real.log (quadLambda ‖f z‖) - Real.log (quadLambda ‖z‖)| ≤ Real.log K :=
    (ENNReal.ofReal_le_ofReal_iff (Real.log_nonneg hK)).1 (hlow.trans hteich)
  have hs0 : 0 < ‖f z‖ := norm_pos_iff.2 hfz0
  have hz0' : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hΛz : 0 < quadLambda ‖z‖ := b4_num_quadLambda_pos hz0'
  have hlog : Real.log (quadLambda ‖f z‖) ≤ Real.log (K * quadLambda ‖z‖) := by
    rw [Real.log_mul (by linarith) hΛz.ne']
    linarith [le_abs_self (Real.log (quadLambda ‖f z‖) - Real.log (quadLambda ‖z‖))]
  have hle : quadLambda ‖f z‖ ≤ K * quadLambda ‖z‖ :=
    (Real.log_le_log_iff (b4_num_quadLambda_pos hs0) (mul_pos (by linarith) hΛz)).1 hlog
  refine b4_le_lambdaInv hs0 (hle.trans (mul_le_mul_of_nonneg_left ?_ (by linarith)))
  exact quadLambda_strictMono.1.monotoneOn hz0' hR hz

/-- **NB'** (properness): `|z| ≤ λ(K Λ(R))` whenever `|f(z)| ≤ R` (NB for the normalized `K`-q.c. map `f⁻¹`). -/
theorem ut2_nb_lower {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖f z‖ ≤ R) : ‖z‖ ≤ lambdaInv (K * quadLambda R) := by
  obtain ⟨hqc, hs, h0, h1⟩ := hf
  have hinv := thm7_2_inv hqc
  rw [hs] at hinv
  have hleft : LeftInvOn (Function.invFunOn f univ) f univ := hqc.2.2.1.2.1.leftInvOn_invFunOn
  have hg0 : Function.invFunOn f univ 0 = 0 := by
    have h := hleft (mem_univ 0)
    rwa [h0] at h
  have hg1 : Function.invFunOn f univ 1 = 1 := by
    have h := hleft (mem_univ 1)
    rwa [h1] at h
  have hgs : Function.invFunOn f univ '' univ = univ :=
    eq_univ_of_forall fun w => ⟨f w, mem_univ _, hleft (mem_univ w)⟩
  have hz' := ut2_nb_upper ⟨hinv, hgs, hg0, hg1⟩ hR hz
  rwa [hleft (mem_univ z)] at hz'

/-- **LG** (local to global): an injective map of an open set which is `K`-q.c. near every point is `K`-q.c. there
(it is an open map, hence a homeomorphism onto its image; then `s13x_removable` with `L = ∅`). -/
theorem ut2_lg {g : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K) (hinj : InjOn g Ω)
    (hloc : ∀ z ∈ Ω, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K) : IsKQC g Ω K := by
  have hcont : ContinuousOn g Ω := fun z hz => by
    obtain ⟨U, hUo, hzU, -, hgU⟩ := hloc z hz
    exact ((hgU.2.2.1.1 z hzU).continuousAt (hUo.mem_nhds hzU)).continuousWithinAt
  refine s13x_removable (L := ∅) hΩ hK (qcl_f_isHomeomorphOnto_of_injOn hΩ hcont hinj) measure_empty
    (Eventually.of_forall fun x => by simp) (Eventually.of_forall fun y => by simp) fun z hz => hloc z hz.1

/-- **LIM** (Theorem 8.2 on an arbitrary open set): an injective locally uniform limit of `K`-q.c. maps of an open
set is `K`-q.c. there (Theorem 8.2 on small discs, then LG). -/
theorem ut2_limit_isKQC {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω)
    (hqc : ∀ n, IsKQC (Fn n) Ω K) (hlim : TendstoLocallyUniformlyOn Fn F atTop Ω) (hinj : InjOn F Ω) :
    IsKQC F Ω K := by
  refine ut2_lg hΩ (hqc 0).2.1 hinj fun z hz => ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ z hz
  refine ⟨ball z r, isOpen_ball, mem_ball_self hr, hball, ?_⟩
  rcases thm8_2_limit isBounded_ball (isConnected_ball hr)
      (fun n => ac_t_isKQC_restrict (hqc n) isOpen_ball hball) (hlim.mono hball) with ⟨c, hc⟩ | h
  · -- a constant limit on the ball contradicts injectivity at the two points `z` and `z + r/2`
    have h1 : z ∈ ball z r := mem_ball_self hr
    have h2 : z + ((r / 2 : ℝ) : ℂ) ∈ ball z r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have heq := hinj (hball h1) (hball h2) ((hc z h1).trans (hc _ h2).symm)
    have h0 : ((r / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w => w - z) heq
      simpa using this.symm
    exact absurd (Complex.ofReal_eq_zero.1 h0) (half_pos hr).ne'
  · exact h

/-- **NF-a helper** (Arzelà–Ascoli on the plane with a pointwise bound): continuous maps `gn n` of the plane with
`‖gn n z‖ ≤ B z` which are equicontinuous at every point have a locally uniformly convergent subsequence (the
pointwise bound replaces the uniform one in `nf_f_exists_subseq_tendstoLocallyUniformlyOn`; Tychonoff still applies to
`∏_z closedBall 0 (B z)`). -/
theorem ut2_nfa_subseq {B : ℂ → ℝ} {gn : ℕ → ℂ → ℂ} (hcont : ∀ n, Continuous (gn n))
    (hB : ∀ n z, ‖gn n z‖ ≤ B z)
    (heq : ∀ z₀ : ℂ, ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ ∀ n z, Dist.dist z z₀ < θ →
      Dist.dist (gn n z) (gn n z₀) < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, TendstoLocallyUniformly (fun n => gn (φ n)) f atTop := by
  choose θ hθpos hθ using heq
  set g : ℕ → C(ℂ, ℂ) := fun n => ⟨gn n, hcont n⟩
  set S : Set C(ℂ, ℂ) := {h : C(ℂ, ℂ) | (∀ z, ‖h z‖ ≤ B z) ∧
      ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ), Dist.dist z z₀ < θ z₀ η hη → Dist.dist (h z) (h z₀) ≤ η}
  have hgS : ∀ n, g n ∈ S := fun n => ⟨hB n, fun z₀ η hη z hz => (hθ z₀ η hη n z hz).le⟩
  set T : Set (ℂ → ℂ) := {u : ℂ → ℂ | (∀ z, ‖u z‖ ≤ B z) ∧
      ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ), Dist.dist z z₀ < θ z₀ η hη → Dist.dist (u z) (u z₀) ≤ η}
  have himage : ContinuousMap.toFun '' S = T := by
    apply Subset.antisymm
    · rintro u ⟨h, hhS, rfl⟩
      exact hhS
    · rintro u ⟨huA, huB⟩
      have hucont : Continuous u := by
        rw [Metric.continuous_iff]
        intro z₀ ε hε
        exact ⟨θ z₀ (ε / 2) (half_pos hε), hθpos z₀ (ε / 2) (half_pos hε),
          fun z hz => lt_of_le_of_lt (huB z₀ (ε / 2) (half_pos hε) z hz) (half_lt_self hε)⟩
      exact ⟨⟨u, hucont⟩, ⟨huA, huB⟩, rfl⟩
  have hTclosed : IsClosed T := by
    have hA : IsClosed {u : ℂ → ℂ | ∀ z, ‖u z‖ ≤ B z} := by
      rw [ofPred_forall]
      exact isClosed_iInter fun z => isClosed_le (continuous_apply z).norm continuous_const
    have hE : IsClosed {u : ℂ → ℂ | ∀ (z₀ : ℂ) (η : ℝ) (hη : 0 < η) (z : ℂ),
        Dist.dist z z₀ < θ z₀ η hη → Dist.dist (u z) (u z₀) ≤ η} := by
      simp only [ofPred_forall]
      refine isClosed_iInter fun z₀ => isClosed_iInter fun η => isClosed_iInter fun hη =>
        isClosed_iInter fun z => ?_
      by_cases hp : Dist.dist z z₀ < θ z₀ η hη
      · simpa [hp] using isClosed_le ((continuous_apply z).dist (continuous_apply z₀))
          continuous_const
      · simp [hp]
    exact hA.inter hE
  have hTsub : T ⊆ Set.pi univ fun z : ℂ => closedBall (0 : ℂ) (B z) := by
    intro u hu i _
    simpa using hu.1 i
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := by
    rw [himage]
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      hTclosed hTsub
  have hS2 : Equicontinuous ((↑) : S → ℂ → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds x₀ (hθpos x₀ (ε / 2) (half_pos hε))] with x hx s
    calc Dist.dist ((s : C(ℂ, ℂ)) x₀) ((s : C(ℂ, ℂ)) x) = Dist.dist ((s : C(ℂ, ℂ)) x) ((s : C(ℂ, ℂ)) x₀) :=
          dist_comm _ _
      _ ≤ ε / 2 := s.2.2 x₀ (ε / 2) (half_pos hε) x hx
      _ < ε := half_lt_self hε
  obtain ⟨h, -, φ, hφmono, hφtend⟩ :=
    (ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2).tendsto_subseq hgS
  exact ⟨φ, hφmono, h, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hφtend⟩

/-- **NF-a** (normal family, extraction): a sequence of normalized `K`-q.c. maps of the plane has a locally uniformly
convergent subsequence (Theorem 8.1 on the discs `|z| < m` with the bound NB and a diagonal subsequence, or
Arzelà–Ascoli for the bounded maps `w ↦ w/(1 + |w|)` composed with `fₙ`). -/
theorem ut2_nf_extract {F : ℕ → ℂ → ℂ} {K : ℝ} (hF : ∀ n, IsKQCNormalizedPlane (F n) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ, TendstoLocallyUniformly (fun n => F (φ n)) G atTop := by
  refine ut2_nfa_subseq (B := fun z => lambdaInv (K * quadLambda (‖z‖ + 1)))
    (fun n => continuousOn_univ.1 (hF n).1.2.2.1.1)
    (fun n z => ut2_nb_upper (hF n) (by positivity) (by linarith)) fun z₀ η hη => ?_
  have hM : ∀ n, ∀ z ∈ ball z₀ 1, ‖F n z‖ ≤ lambdaInv (K * quadLambda (‖z₀‖ + 1)) := by
    intro n z hz
    refine ut2_nb_upper (hF n) (by positivity) ?_
    have h1 := norm_sub_norm_le z z₀
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  obtain ⟨θ, hθ, h⟩ := nf_f_equicontinuous_of_isKQC
    (fun n => ac_t_isKQC_restrict (hF n).1 isOpen_ball (subset_univ _)) hM (mem_ball_self one_pos) hη
  exact ⟨min θ 1, lt_min hθ one_pos, fun n z hz =>
    h n z (mem_ball.2 (hz.trans_le (min_le_right _ _))) (hz.trans_le (min_le_left _ _))⟩

/-- **NF-b** (normal family, the limit): a locally uniform limit of normalized `K`-q.c. maps of the plane is a
normalized `K`-q.c. map of the plane (injective by Theorem 8.2 on large discs since `G 0 = 0 ≠ 1 = G 1`, `K`-q.c. by
LIM, onto since `G(ℂ)` is open and, by NB', closed). -/
theorem ut2_nf_limit {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K : ℝ} (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hlim : TendstoLocallyUniformly F G atTop) : IsKQCNormalizedPlane G K := by
  -- the normalization passes to the pointwise limit
  have hpt : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (G z)) := fun z =>
    (tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)
  have hG0 : G 0 = 0 :=
    tendsto_nhds_unique (hpt 0) (tendsto_const_nhds.congr fun n => ((hF n).2.2.1).symm)
  have hG1 : G 1 = 1 :=
    tendsto_nhds_unique (hpt 1) (tendsto_const_nhds.congr fun n => ((hF n).2.2.2).symm)
  -- `G` is injective: Theorem 8.2 on a disc containing `0, 1, z, w`, where `G` is not constant
  have hinj : InjOn G univ := by
    intro z _ w _ hzw
    have hr : (0 : ℝ) < ‖z‖ + ‖w‖ + 2 := by positivity
    have hmem : ∀ x : ℂ, ‖x‖ < ‖z‖ + ‖w‖ + 2 → x ∈ ball (0 : ℂ) (‖z‖ + ‖w‖ + 2) := fun x hx =>
      mem_ball_zero_iff.2 hx
    rcases thm8_2_limit isBounded_ball (isConnected_ball hr)
      (fun n => ac_t_isKQC_restrict (hF n).1 isOpen_ball (subset_univ _))
      hlim.tendstoLocallyUniformlyOn with ⟨c, hc⟩ | hGqc
    · have h0 := hc 0 (hmem 0 (by simpa using hr))
      have h1 := hc 1 (hmem 1 (by rw [norm_one]; linarith [norm_nonneg z, norm_nonneg w]))
      rw [hG0] at h0
      rw [hG1] at h1
      exact absurd (h0.trans h1.symm) zero_ne_one
    · exact hGqc.2.2.1.2.1 (hmem z (by linarith [norm_nonneg w])) (hmem w (by linarith [norm_nonneg z])) hzw
  have hGqc : IsKQC G univ K :=
    ut2_limit_isKQC isOpen_univ (fun n => (hF n).1) (tendstoLocallyUniformlyOn_univ.2 hlim) hinj
  -- properness of `G`, from the lower bound NB' for the `F n`
  have hprop : ∀ R : ℝ, 0 < R → ∀ z, ‖G z‖ < R → ‖z‖ ≤ lambdaInv (K * quadLambda R) := by
    intro R hR z hz
    obtain ⟨n, hn⟩ := ((hpt z).norm.eventually_lt_const hz).exists
    exact ut2_nb_lower (hF n) hR hn.le
  -- `G(ℂ)` is closed: near `w ∈ closure G(ℂ)` it is the compact image of a closed disc
  have hclosed : IsClosed (G '' univ) := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have hR : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hcpt : IsCompact (G '' closedBall 0 (lambdaInv (K * quadLambda (‖w‖ + 1)))) :=
      (isCompact_closedBall _ _).image (continuousOn_univ.1 hGqc.2.2.1.1)
    have hsub : ball (0 : ℂ) (‖w‖ + 1) ∩ G '' univ ⊆
        G '' closedBall 0 (lambdaInv (K * quadLambda (‖w‖ + 1))) := by
      rintro _ ⟨hb, z, -, rfl⟩
      exact ⟨z, mem_closedBall_zero_iff.2 (hprop _ hR z (mem_ball_zero_iff.1 hb)), rfl⟩
    have hw' := closure_mono hsub (isOpen_ball.inter_closure ⟨mem_ball_zero_iff.2 (by linarith), hw⟩)
    rw [hcpt.isClosed.closure_eq] at hw'
    exact image_mono (subset_univ _) hw'
  -- `G(ℂ)` is open, closed and nonempty, so it is `ℂ`
  exact ⟨hGqc, IsClopen.eq_univ ⟨hclosed, isOpen_image_of_isKQC hGqc⟩ (univ_nonempty.image G), hG0, hG1⟩

/-- **R** (reduction to a fixed first representative): for `μ ∼ μ₀` and any `ν` there is `ν' ∼ ν` with
`v(μ₀, ν') = v(μ, ν)` (`ν'` from `ut_transport`, and `f_μ(ℍ) = f_μ₀(ℍ)` by `ut_welding`). -/
theorem ut2_reduce {μ₀ μ : BeltramiH} (h : teichSetoid μ μ₀) (ν : BeltramiH) :
    ∃ ν' : BeltramiH, teichSetoid ν' ν ∧ ut_v μ₀ ν' = ut_v μ ν := by
  obtain ⟨ν', hν'ν, hfν'⟩ := ut_transport h ν
  refine ⟨ν', hν'ν, ?_⟩
  have hsurj : normalizedSolution μ₀.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ = id := by
    funext w
    have hw : w ∈ normalizedSolution μ₀.1 '' univ := by rw [(ut_spec μ₀).2.1]; exact mem_univ w
    exact Function.invFunOn_eq hw
  have hcomp : normalizedSolution ν'.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ =
      normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ := by
    rw [hfν']
    funext w
    have := congrFun hsurj w
    simp only [Function.comp_apply, id] at this ⊢
    rw [this]
  unfold ut_v
  rw [hcomp, (ut_welding h).2]

/-- **U** helper (gluing across `ℝ`): a map `f` of the plane which is a homeomorphism onto its image and is `K`-q.c.
on `ℍ` and on `𝕃` is `K`-q.c. on `ℂ` (`s13x_removable` with the null set `ℝ`, which meets every vertical line in one
point and almost every horizontal line in no point). -/
theorem ut2_ruh_glue {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K) (hf : IsHomeomorphOnto f univ (f '' univ))
    (hU : IsKQC f upperHalf K) (hL : IsKQC f lowerHalf K) : IsKQC f univ K := by
  refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_univ hK hf gzE_volume_im_eq_zero ?_ ?_ ?_
  · -- a vertical line meets the real axis in one point
    refine Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => ?_
    simpa using hy
  · -- a horizontal line off the real axis misses it
    have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with y hy
    refine countable_empty.mono fun x hx => ?_
    exact absurd (by simpa using hx) hy
  · -- off the real axis, a point lies in `ℍ` or in `𝕃`
    rintro w ⟨-, hw⟩
    have hw' : w.im ≠ 0 := hw
    rcases lt_or_gt_of_ne hw' with hlt | hgt
    · exact ⟨lowerHalf, hL.1, hlt, subset_univ _, hL⟩
    · exact ⟨upperHalf, hU.1, hgt, subset_univ _, hU⟩

/-- **U** (uniform dilatation): if `f_μ₀` is `K₀`-q.c. then `f_ν` is `K₀ e^{v(μ₀, ν)}`-q.c. (on `ℍ` it is
`(f_ν ∘ f_μ₀⁻¹) ∘ f_μ₀` with `K[f_ν ∘ f_μ₀⁻¹] = e^{v(μ₀, ν)}`, on `𝕃` it is conformal; glue across `ℝ` with
`s13x_removable`). -/
theorem ut2_uniform_K {μ₀ : BeltramiH} {K₀ : ℝ} (h₀ : IsKQC (normalizedSolution μ₀.1) univ K₀) (ν : BeltramiH) :
    IsKQC (normalizedSolution ν.1) univ (K₀ * Real.exp (ut_v μ₀ ν)) := by
  obtain ⟨K', hg⟩ := ut_md_trans_isKQC μ₀ ν
  have hne : (normalizedSolution μ₀.1 '' upperHalf).Nonempty :=
    ⟨_, mem_image_of_mem _ (show I ∈ upperHalf by simp [upperHalf])⟩
  obtain ⟨hKg1, hgK⟩ := ut_md_isKQC_toReal hg hne
  -- `e^{v(μ₀, ν)} = K[f_ν ∘ f_μ₀⁻¹]`
  have hexp : Real.exp (ut_v μ₀ ν) = (maxDilatation (normalizedSolution ν.1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) (normalizedSolution μ₀.1 '' upperHalf)).toReal := by
    unfold ut_v
    exact Real.exp_log (by linarith)
  rw [hexp]
  have hK1 : 1 ≤ K₀ * (maxDilatation (normalizedSolution ν.1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) (normalizedSolution μ₀.1 '' upperHalf)).toReal :=
    one_le_mul_of_one_le_of_one_le h₀.2.1 hKg1
  -- on `ℍ`: `f_ν = (f_ν ∘ f_μ₀⁻¹) ∘ f_μ₀` (Theorem 7.1)
  have hU : IsKQC (normalizedSolution ν.1) upperHalf (K₀ * (maxDilatation (normalizedSolution ν.1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) (normalizedSolution μ₀.1 '' upperHalf)).toReal) := by
    refine ad_isKQC_congr (thm7_1_comp (ac_t_isKQC_restrict h₀ isOpen_upperHalf (subset_univ _)) hgK
      subset_rfl) fun z _ => ?_
    simp only [Function.comp_apply, ut_md_leftInv μ₀ z]
  -- on `𝕃`: `f_ν` is conformal, hence `1`-q.c.
  have hL : IsKQC (normalizedSolution ν.1) lowerHalf (K₀ * (maxDilatation (normalizedSolution ν.1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) (normalizedSolution μ₀.1 '' upperHalf)).toReal) :=
    (isKQC_one_of_conformal (isOpen_lt continuous_im continuous_const) (ut_conformal_lowerHalf ν)).mono hK1
  obtain ⟨Kν, hKν⟩ := (ut_spec ν).1
  exact ut2_ruh_glue hK1 hKν.2.2.1 hU hL

/-- **M** (the limit stays in the class): if `νs n ∼ ν` for all `n` and `f_{νs n}` converges locally uniformly to a
normalized `K`-q.c. map `G` of the plane, then `G = f_{ν'}` for some `ν' ∼ ν` (`G` is `1`-q.c. on `𝕃` by LIM, so
`ν' = 𝟙_ℍ μ_G ∈ M` and `G` solves its Beltrami equation; `G = f_ν` on `ℝ` as a pointwise limit). -/
theorem ut2_limit_mem {νs : ℕ → BeltramiH} {ν : BeltramiH} (hν : ∀ n, teichSetoid (νs n) ν) {G : ℂ → ℂ} {K : ℝ}
    (hG : IsKQCNormalizedPlane G K)
    (hlim : TendstoLocallyUniformly (fun n => normalizedSolution (νs n).1) G atTop) :
    ∃ ν' : BeltramiH, teichSetoid ν' ν ∧ normalizedSolution ν'.1 = G := by
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  have hlimU : TendstoLocallyUniformlyOn (fun n => normalizedSolution (νs n).1) G atTop univ :=
    tendstoLocallyUniformlyOn_univ.2 hlim
  -- `G` is `1`-q.c. on `𝕃` as a locally uniform limit of the conformal maps `f_{νs n}|𝕃`
  have hG1 : IsKQC G lowerHalf 1 :=
    ut2_limit_isKQC hLo (fun n => isKQC_one_of_conformal hLo (ut_conformal_lowerHalf (νs n)))
      (hlimU.mono (subset_univ _)) (hG.1.2.2.1.2.1.mono (subset_univ _))
  -- so its complex dilatation vanishes a.e. on `𝕃`
  have hd0 : ∀ᵐ z, z ∈ lowerHalf → complexDilatation G z = 0 := by
    refine (ae_restrict_iff' hLo.measurableSet).1 ?_
    filter_upwards [(isKQC_maxDilatation_le hG1).2] with z hz
    norm_num at hz
    exact hz
  -- the coefficient `ν' = 𝟙_ℍ μ_G` of `M`
  set ν' : BeltramiH := ⟨upperHalf.indicator (complexDilatation G), ut_rg_indicator_mem hG.1⟩ with hν'def
  have hae : ∀ᵐ z, complexDilatation G z = ν'.1 z := by
    have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
      measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
    filter_upwards [hd0, hnull] with z h1 h2
    rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
    · have hnu : z ∉ upperHalf := fun hu => absurd hlt (not_lt.2 (le_of_lt hu))
      rw [hν'def]
      show complexDilatation G z = upperHalf.indicator (complexDilatation G) z
      rw [Set.indicator_of_notMem hnu, h1 hlt]
    · rw [hν'def]
      show complexDilatation G z = upperHalf.indicator (complexDilatation G) z
      rw [Set.indicator_of_mem (show z ∈ upperHalf from hgt)]
  -- `G` is the normalized solution for `ν'` (uniqueness, Theorem 13.5)
  have hnorm : normalizedSolution ν'.1 = G := by
    obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ν'
    refine thm13_5_uniqueness_plane hq ⟨K, hG.1⟩ hs hG.2.1 ?_ hq0 hq1 hG.2.2.1 hG.2.2.2
    filter_upwards [hd, hae] with z h1 h2
    exact h1.trans h2.symm
  -- on `ℝ`, `G` is the pointwise limit of the constant sequence `f_{νs n}(x) = f_ν(x)`
  refine ⟨ν', fun x => ?_, hnorm⟩
  show normalizedSolution ν'.1 x = normalizedSolution ν.1 x
  rw [hnorm]
  have h1 : Tendsto (fun n => normalizedSolution (νs n).1 (x : ℂ)) atTop (𝓝 (G x)) :=
    hlimU.tendsto_at (mem_univ _)
  have h2 : (fun n => normalizedSolution (νs n).1 (x : ℂ)) = fun _ => normalizedSolution ν.1 x :=
    funext fun n => hν n x
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- **LS** (lower semicontinuity of `v(μ₀, ·)`): if `f_{νs n} → f_{ν'}` locally uniformly and `v(μ₀, νs n) → d`, then
`v(μ₀, ν') ≤ d` (for `K' > e^d`, eventually `f_{νs n} ∘ f_μ₀⁻¹` is `K'`-q.c. on `f_μ₀(ℍ)` by `ut_md_isKQC_of_le`;
these converge locally uniformly there, so the limit is `K'`-q.c. there by LIM). -/
theorem ut2_v_le_of_tendsto {μ₀ ν' : BeltramiH} {νs : ℕ → BeltramiH} {d : ℝ}
    (hlim : TendstoLocallyUniformly (fun n => normalizedSolution (νs n).1) (normalizedSolution ν'.1) atTop)
    (hv : Tendsto (fun n => ut_v μ₀ (νs n)) atTop (𝓝 d)) : ut_v μ₀ ν' ≤ d := by
  have hne : (normalizedSolution μ₀.1 '' upperHalf).Nonempty :=
    ⟨_, mem_image_of_mem _ (show I ∈ upperHalf by simp [upperHalf])⟩
  obtain ⟨K₁, hg⟩ := ut_md_trans_isKQC μ₀ ν'
  -- `f_μ₀⁻¹` is continuous on the plane
  have hcont : Continuous (Function.invFunOn (normalizedSolution μ₀.1) univ) := by
    obtain ⟨K₀, hK₀⟩ := (ut_spec μ₀).1
    have h := hK₀.2.2.1.2.2.2
    rw [(ut_spec μ₀).2.1] at h
    exact continuousOn_univ.mp h
  have hconv := (hlim.comp _ hcont).tendstoLocallyUniformlyOn
    (s := normalizedSolution μ₀.1 '' upperHalf)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : d < Real.log (Real.exp (d + ε)) := by rw [Real.log_exp]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hv.eventually_lt_const hlt)
  -- eventually `f_{νs n} ∘ f_μ₀⁻¹` is `e^{d+ε}`-q.c. on `f_μ₀(ℍ)`
  have hqc : ∀ n, IsKQC (normalizedSolution (νs (n + N)).1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ)
      (normalizedSolution μ₀.1 '' upperHalf) (Real.exp (d + ε)) := by
    intro n
    obtain ⟨K, hgn⟩ := ut_md_trans_isKQC μ₀ (νs (n + N))
    obtain ⟨h1, hgn'⟩ := ut_md_isKQC_toReal hgn hne
    refine hgn'.mono ((Real.log_lt_log_iff (by linarith) (Real.exp_pos _)).mp ?_).le
    exact hN (n + N) (Nat.le_add_left N n)
  have hshift : TendstoLocallyUniformlyOn
      (fun n => normalizedSolution (νs (n + N)).1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ)
      (normalizedSolution ν'.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ) atTop
      (normalizedSolution μ₀.1 '' upperHalf) := by
    intro u hu x hx
    obtain ⟨t, ht, H⟩ := hconv u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually H⟩
  -- the limit `f_ν' ∘ f_μ₀⁻¹` is `e^{d+ε}`-q.c. there (LIM)
  have hK := ut2_limit_isKQC hg.1 hqc hshift hg.2.2.1.2.1
  have h1 := (ut_md_isKQC_toReal hK hne).1
  have hle := ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (isKQC_maxDilatation_le hK).1
  calc ut_v μ₀ ν' ≤ Real.log (Real.exp (d + ε)) := Real.log_le_log (by linarith) hle
    _ = d + ε := Real.log_exp _

/-- For `0 ≤ d < 1`, `ln((1 + d)/(1 - d)) = 0` forces `d = 0`: for `d > 0` the quotient exceeds `1`, so its
logarithm is positive. -/
theorem ut2_zh_eq_zero_of_log_quot_eq_zero {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (h : Real.log ((1 + d) / (1 - d)) = 0) : d = 0 := by
  by_contra hne
  have hpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hne)
  have h1 : 1 < (1 + d) / (1 - d) := by
    rw [one_lt_div (by linarith)]
    linarith
  have h2 := Real.log_pos h1
  linarith

/-- A `[0, ∞]`-valued function which is a.e. bounded by a finite constant, and whose essential supremum has `toReal`
equal to `0`, vanishes a.e.: the essential supremum is finite, hence `0`, and the function is a.e. below it. -/
theorem ut2_zh_ae_eq_zero_of_essSup_toReal_eq_zero {α : Type*} [MeasurableSpace α] {m : Measure α}
    {g : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) (hg : ∀ᵐ x ∂m, g x ≤ c) (h0 : (essSup g m).toReal = 0) :
    ∀ᵐ x ∂m, g x = 0 := by
  have hle : essSup g m ≤ c := essSup_le_of_ae_le _ hg
  have hE : essSup g m = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right (ne_top_of_le_ne_top hc hle)
  filter_upwards [ENNReal.ae_le_essSup g] with x hx
  exact nonpos_iff_eq_zero.1 (hx.trans_eq hE)

/-- For `‖a‖, ‖b‖ < 1`, `(a - b)/(1 - b̄a) = 0` forces `a = b`: the denominator does not vanish, since
`‖b̄a‖ = ‖b‖ ‖a‖ < 1`. -/
theorem ut2_zh_eq_of_quot_eq_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (h : (a - b) / (1 - conj b * a) = 0) : a = b := by
  rcases div_eq_zero_iff.1 h with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have h2 : ‖conj b * a‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_of_le_one_right (norm_nonneg _) ha.le).trans_lt hb
    rw [← sub_eq_zero.1 h1, norm_one] at h2
    exact lt_irrefl _ h2

/-- If `‖μ‖, ‖ν‖ ≤ k < 1` a.e. and `‖(μ - ν)/(1 - ν̄μ)‖_∞ = 0` on `ℍ`, then `μ = ν` a.e. on `ℍ`: the integrand is
bounded by `2k/(1 + k²)` (`ahQ_pseudo_bound`), so its essential supremum is finite, hence `0`, and the denominator
does not vanish. -/
theorem ut2_zh_ae_eq_of_dilatationDiffNorm_eq_zero {μ ν : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ᵐ z, ‖μ z‖ ≤ k) (hν : ∀ᵐ z, ‖ν z‖ ≤ k) (h : dilatationDiffNorm μ ν = 0) :
    ∀ᵐ z ∂(volume.restrict upperHalf), μ z = ν z := by
  have hc : ∀ᵐ z ∂(volume.restrict upperHalf),
      (‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (2 * k / (1 + k ^ 2)) := by
    filter_upwards [ae_restrict_of_ae hμ, ae_restrict_of_ae hν] with z h1 h2
    calc (‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖₊ : ℝ≥0∞) =
          ENNReal.ofReal ‖(μ z - ν z) / (1 - conj (ν z) * μ z)‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (2 * k / (1 + k ^ 2)) :=
          ENNReal.ofReal_le_ofReal (ahQ_pseudo_bound hk0 hk1 h1 h2)
  have h0 := ut2_zh_ae_eq_zero_of_essSup_toReal_eq_zero ENNReal.ofReal_ne_top hc h
  filter_upwards [h0, ae_restrict_of_ae hμ, ae_restrict_of_ae hν] with z hz h1 h2
  exact ut2_zh_eq_of_quot_eq_zero (h1.trans_lt hk1) (h2.trans_lt hk1)
    (nnnorm_eq_zero.1 (ENNReal.coe_eq_zero.1 hz))

/-- Two functions vanishing on the closed lower half-plane which agree a.e. on `ℍ` agree a.e. on `ℂ`. -/
theorem ut2_zh_ae_eq_of_ae_eq_upperHalf {μ ν : ℂ → ℂ} (hμ0 : ∀ z : ℂ, z.im ≤ 0 → μ z = 0)
    (hν0 : ∀ z : ℂ, z.im ≤ 0 → ν z = 0) (h : ∀ᵐ z ∂(volume.restrict upperHalf), μ z = ν z) :
    ∀ᵐ z, μ z = ν z := by
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at h
  filter_upwards [h] with z hz
  by_cases hi : 0 < z.im
  · exact hz hi
  · rw [not_lt] at hi
    rw [hμ0 z hi, hν0 z hi]

/-- **Z**: `v(μ, ν) = 0` implies `μ ∼ ν` (by (21.4) pointwise `‖(μ - ν)/(1 - ν̄μ)‖_∞ = 0`, so `μ = ν` a.e. on `ℍ`, hence
a.e. on `ℂ`, and `f_μ = f_ν` by uniqueness). -/
theorem ut2_equiv_of_v_eq_zero {μ ν : BeltramiH} (h : ut_v μ ν = 0) : teichSetoid μ ν := by
  obtain ⟨hd1, hv⟩ := ut_v_eq μ ν
  have hd : dilatationDiffNorm μ.1 ν.1 = 0 :=
    ut2_zh_eq_zero_of_log_quot_eq_zero ENNReal.toReal_nonneg hd1 (hv ▸ h)
  obtain ⟨⟨kμ, hkμ0, hkμ1, -, hbμ⟩, hμ0⟩ := μ.2
  obtain ⟨⟨kν, -, hkν1, -, hbν⟩, hν0⟩ := ν.2
  rw [Measure.restrict_univ] at hbμ hbν
  have hae : ∀ᵐ z, μ.1 z = ν.1 z := ut2_zh_ae_eq_of_ae_eq_upperHalf hμ0 hν0
    (ut2_zh_ae_eq_of_dilatationDiffNorm_eq_zero (le_max_of_le_left hkμ0) (max_lt hkμ1 hkν1)
      (by filter_upwards [hbμ] with z hz using hz.trans (le_max_left _ _))
      (by filter_upwards [hbν] with z hz using hz.trans (le_max_right _ _)) hd)
  obtain ⟨hqμ, hsμ, h0μ, h1μ, hcμ⟩ := ut_spec μ
  obtain ⟨hqν, hsν, h0ν, h1ν, hcν⟩ := ut_spec ν
  have hfg : normalizedSolution μ.1 = normalizedSolution ν.1 := by
    refine thm13_5_uniqueness_plane hqμ hqν hsμ hsν ?_ h0μ h1μ h0ν h1ν
    filter_upwards [hcμ, hcν, hae] with z h1 h2 h3
    rw [h1, h2, h3]
  intro x
  rw [hfg]

/-- (21.1): the infimum defining `d(p, q)` is attained. -/
theorem eq21_1 (p q : UniversalTeichmuller) :
    ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
      dist p q = Real.log (maxDilatation (normalizedSolution ν.1 ∘
        Function.invFunOn (normalizedSolution μ.1) univ) (normalizedSolution μ.1 '' upperHalf)).toReal := by
  set μ₀ : BeltramiH := p.out with hμ₀def
  have hμ₀ : Quotient.mk teichSetoid μ₀ = p := Quotient.out_eq p
  -- a minimizing sequence whose first representative is `μ₀` (R)
  have hseq : ∀ n : ℕ, ∃ ν : BeltramiH, Quotient.mk teichSetoid ν = q ∧
      ut_v μ₀ ν < dist p q + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨μ, ν, hμ, hν, hlt⟩ := ut_dist_lt p q (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨ν', hν'ν, hv⟩ := ut2_reduce (Quotient.exact (hμ.trans hμ₀.symm)) ν
    exact ⟨ν', (Quotient.sound hν'ν).trans hν, hv ▸ hlt⟩
  choose νs hνs hlt using hseq
  have hge : ∀ n, dist p q ≤ ut_v μ₀ (νs n) := fun n => ut_dist_le hμ₀ (hνs n)
  have hv : Tendsto (fun n => ut_v μ₀ (νs n)) atTop (𝓝 (dist p q)) := by
    have h0 : Tendsto (fun n : ℕ => dist p q + 1 / ((n : ℝ) + 1)) atTop (𝓝 (dist p q)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (dist p q)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hge fun n => (hlt n).le
  -- the maps `f_{νs n}` are normalized and uniformly quasiconformal (U)
  obtain ⟨K₀, hK₀⟩ := (ut_spec μ₀).1
  have hnorm : ∀ n, IsKQCNormalizedPlane (normalizedSolution (νs n).1) (K₀ * Real.exp (dist p q + 1)) := by
    intro n
    obtain ⟨-, hs, h0, h1, -⟩ := ut_spec (νs n)
    have hle : ut_v μ₀ (νs n) ≤ dist p q + 1 := by
      have h1n : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      linarith [hlt n]
    have hK₀0 : 0 ≤ K₀ := le_trans zero_le_one hK₀.2.1
    exact ⟨(ut2_uniform_K hK₀ (νs n)).mono (by gcongr), hs, h0, h1⟩
  -- a locally uniform limit (NF), which lies in `q` (M) and realizes the infimum (LS)
  obtain ⟨φ, hφ, G, hlim⟩ := ut2_nf_extract hnorm
  have hG := ut2_nf_limit (fun n => hnorm (φ n)) hlim
  have hcls : ∀ n, teichSetoid (νs (φ n)) q.out := fun n =>
    Quotient.exact ((hνs (φ n)).trans (Quotient.out_eq q).symm)
  obtain ⟨ν', hν', hfG⟩ := ut2_limit_mem hcls hG hlim
  have hν'q : Quotient.mk teichSetoid ν' = q := (Quotient.sound hν').trans (Quotient.out_eq q)
  refine ⟨μ₀, ν', hμ₀, hν'q, le_antisymm (ut_dist_le hμ₀ hν'q) ?_⟩
  rw [← hfG] at hlim
  exact ut2_v_le_of_tendsto hlim (hv.comp hφ.tendsto_atTop)

/-- §21.1: `d(p, q) = 0` implies `p = q`. -/
theorem eq_of_dist_eq_zero {p q : UniversalTeichmuller} (h : dist p q = 0) : p = q := by
  obtain ⟨μ, ν, hμ, hν, hd⟩ := eq21_1 p q
  rw [h] at hd
  rw [← hμ, ← hν]
  exact Quotient.sound (ut2_equiv_of_v_eq_zero hd.symm)

/-- (21.4): `d(p, q) = inf_{μ ∈ p, ν ∈ q} ln((1 + ‖(μ-ν)/(1-ν̄μ)‖_∞)/(1 - ‖(μ-ν)/(1-ν̄μ)‖_∞))`. -/
theorem eq21_4 (p q : UniversalTeichmuller) :
    dist p q = sInf {d | ∃ μ ν : BeltramiH, Quotient.mk teichSetoid μ = p ∧
        Quotient.mk teichSetoid ν = q ∧
        d = Real.log ((1 + dilatationDiffNorm μ.1 ν.1) / (1 - dilatationDiffNorm μ.1 ν.1))} := by
  rw [ut_dist_def]
  congr 1
  ext d
  constructor
  · rintro ⟨μ, ν, hμ, hν, rfl⟩
    exact ⟨μ, ν, hμ, hν, (ut_v_eq μ ν).2⟩
  · rintro ⟨μ, ν, hμ, hν, rfl⟩
    exact ⟨μ, ν, hμ, hν, ((ut_v_eq μ ν).2).symm⟩

/-- **Theorem 21.1**: `T` is path connected; indeed `t ↦ [tμ]` is a continuous path from the
origin to `[μ]`. -/
theorem thm21_1_path_connected (μ : BeltramiH) :
    ∃ γ : ℝ → UniversalTeichmuller, γ 0 = origin ∧ γ 1 = Quotient.mk teichSetoid μ ∧
      ∀ t₀ ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ →
        dist (γ t) (γ t₀) < ε := by
  obtain ⟨k, hk0, hk1, hμk⟩ := μ.2.1
  refine ⟨fun t => Quotient.mk teichSetoid (ut_scale μ t), ?_, ?_, ?_⟩
  · show Quotient.mk teichSetoid (ut_scale μ 0) = origin
    unfold origin
    congr 1
    apply Subtype.ext
    funext z
    simp [ut_scale]
  · show Quotient.mk teichSetoid (ut_scale μ 1) = Quotient.mk teichSetoid μ
    congr 1
    apply Subtype.ext
    funext z
    simp [ut_scale]
  · intro t₀ _ ε hε
    have hk2 : 0 < 1 - k ^ 2 := by nlinarith
    set η := (Real.exp ε - 1) / (Real.exp ε + 1) with hηdef
    have hexp : 1 < Real.exp ε := Real.one_lt_exp_iff.2 hε
    have hη0 : 0 < η := div_pos (by linarith) (by linarith)
    -- `ln((1 + d)/(1 - d)) < ε` for `0 ≤ d < η`
    have hsmall : ∀ d : ℝ, 0 ≤ d → d < η → Real.log ((1 + d) / (1 - d)) < ε := by
      intro d hd0 hdη
      have hη1 : η < 1 := by rw [hηdef, div_lt_one (by linarith)]; linarith
      have hd1 : d < 1 := hdη.trans hη1
      rw [Real.log_lt_iff_lt_exp (div_pos (by linarith) (by linarith)), div_lt_iff₀ (by linarith)]
      have : d * (Real.exp ε + 1) < Real.exp ε - 1 := by
        rw [hηdef, lt_div_iff₀ (by linarith)] at hdη
        exact hdη
      nlinarith
    refine ⟨η * (1 - k ^ 2) / (k + 1), div_pos (mul_pos hη0 hk2) (by linarith), fun t _ ht => ?_⟩
    obtain ⟨hd1, hdv⟩ := ut_v_eq (ut_scale μ t) (ut_scale μ t₀)
    have hd0 : 0 ≤ dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1 := ENNReal.toReal_nonneg
    have hle := ut_d_scale_le μ hk0 hk1 hμk t t₀
    have hdη : dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1 < η := by
      calc dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1 ≤ |t - t₀| * k / (1 - k ^ 2) := hle
        _ ≤ |t - t₀| * (k + 1) / (1 - k ^ 2) := by gcongr; linarith
        _ < η * (1 - k ^ 2) / (k + 1) * (k + 1) / (1 - k ^ 2) := by gcongr
        _ = η := by field_simp
    calc dist _ _ ≤ ut_v (ut_scale μ t) (ut_scale μ t₀) := ut_dist_le rfl rfl
      _ = Real.log ((1 + dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1) /
          (1 - dilatationDiffNorm (ut_scale μ t).1 (ut_scale μ t₀).1)) := hdv
      _ < ε := hsmall _ hd0 hdη

end UniversalTeichmuller

/-- The norm `‖φ‖ = sup_{z ∈ 𝕃} |φ(z)| |Im z|²` of the Banach space `A(𝕃)`. -/
def bersNormL (φ : ℂ → ℂ) : ℝ≥0∞ := ⨆ z ∈ lowerHalf, ENNReal.ofReal (‖φ z‖ * z.im ^ 2)

/-- The Banach space `A(𝕃)` of holomorphic functions in the lower half-plane with finite norm. -/
def bersSpaceL : Set (ℂ → ℂ) := {φ | DifferentiableOn ℂ φ lowerHalf ∧ bersNormL φ < ⊤}

/-- The lower half-plane is open.  (Companion to `isOpen_upperHalf` in §5; kept here rather than
beside it only to stay out of a concurrently edited file, and could be hoisted later.) -/
theorem isOpen_lowerHalf : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const

/-- `z ↦ -z` maps the lower half-plane conformally onto the upper half-plane.

It is `ℂ`-linear, hence holomorphic.  Note that `conj` also exchanges the two half-planes but is
*anti*holomorphic, so it cannot be used here: `IsConformalOnto` requires `DifferentiableOn ℂ`. -/
theorem isConformalOnto_neg_lowerHalf :
    IsConformalOnto (fun z : ℂ => -z) lowerHalf upperHalf := by
  refine ⟨differentiable_id.neg.differentiableOn, fun z₁ _ z₂ _ h => neg_injective h, ?_⟩
  ext w
  simp only [Set.mem_image, lowerHalf, upperHalf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hw
    exact ⟨-w, by simpa using hw, neg_neg w⟩

/-- The Poincaré density of `𝕃` is `1/|Im z|`, so `bersNormL` is the norm `‖·‖_𝕃` of §19.3.

Proof: `z ↦ C(-z)` is a conformal map of `𝕃` onto `Δ` (the negation is holomorphic, unlike
`conj`), and the chain rule gives `‖(C ∘ -)'(z)‖ = ‖C'(-z)‖` with `(C ∘ -)(z) = C(-z)`, so the
defining quotient at `z ∈ 𝕃` is literally the one at `-z ∈ ℍ`.  Hence the density equals
`poincareDensity upperHalf (-z) = 1/(-z).im = 1/(-Im z)`, which is `1/|Im z|` because
`Im z < 0`. -/
theorem poincareDensity_lowerHalf {z : ℂ} (hz : z ∈ lowerHalf) :
    poincareDensity lowerHalf z = 1 / |z.im| := by
  have hz' : z.im < 0 := hz
  have hneg : -z ∈ upperHalf := by
    simp only [upperHalf, Set.mem_setOf_eq, Complex.neg_im]
    linarith
  have hneg' : (0 : ℝ) < (-z).im := hneg
  -- `z ↦ C(-z)` is conformal from `𝕃` onto `Δ`
  have hconf : IsConformalOnto (cayley ∘ fun w : ℂ => -w) lowerHalf unitDisc :=
    isConformalOnto_cayley.comp isConformalOnto_neg_lowerHalf
  -- the chain rule: same modulus of derivative, same value
  have hdc : DifferentiableAt ℂ cayley (-z) := by
    have hfun : cayley = fun w : ℂ => (w - I) / (w + I) := rfl
    rw [hfun]
    exact (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v - I) (-z)).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v + I) (-z)) (cayley_den_ne_zero hneg')
  have hderiv : deriv (cayley ∘ fun w : ℂ => -w) z = -deriv cayley (-z) := by
    rw [deriv_comp z hdc (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -w) z), deriv_neg'']
    ring
  have hvalue : (cayley ∘ fun w : ℂ => -w) z = cayley (-z) := rfl
  -- evaluate the density on both sides through the same quotient
  rw [(poincareDensity_well_defined isOpen_lowerHalf hconf hconf hz).2, hderiv, hvalue,
    norm_neg, ← (poincareDensity_well_defined isOpen_upperHalf isConformalOnto_cayley
      isConformalOnto_cayley hneg).2, poincareDensity_upperHalf hneg, Complex.neg_im,
    abs_of_neg hz']

/-- The Schwarzian derivative of `f_μ` on `𝕃` (a function on `ℂ`, zero off `𝕃`). -/
def bersFunction (μ : ℂ → ℂ) : ℂ → ℂ := lowerHalf.indicator (schwarzian (normalizedSolution μ))

/-- The Bers map `Ψ : T → A(𝕃)`, `[μ] ↦ S_{f_μ}|𝕃` (computed on a representative). -/
def bersMapU (p : UniversalTeichmuller) : ℂ → ℂ := bersFunction (Quotient.out p).1

/-- The Bers map is well defined: equivalent coefficients give the same Schwarzian on `𝕃`. -/
theorem bersFunction_eq_of_equiv {μ ν : BeltramiH} (h : teichSetoid μ ν) :
    bersFunction μ.1 = bersFunction ν.1 := by
  have hw := (ut_welding h).1
  funext z
  simp only [bersFunction]
  by_cases hz : z ∈ lowerHalf
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    apply schwarzian_congr
    filter_upwards [nhdsWithin_le_nhds (isOpen_lowerHalf.mem_nhds hz)] with w hw'
    exact hw w (le_of_lt hw')
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

/-! ### Bers-A track interface (coordinator 553e2d): `Ψ(T) ⊆ A(𝕃)` and the injectivity of `Ψ` -/

/-- The lower half-plane `𝕃` is a hyperbolic simply connected domain: it is open, convex (hence
connected and contractible, so simply connected), and misses `0`. -/
theorem bA_k_isHyperbolicSimplyConnected_lowerHalf : IsHyperbolicSimplyConnected lowerHalf := by
  have hconv : Convex ℝ lowerHalf := (convex_Iio (0 : ℝ)).linear_preimage Complex.imLm
  have hne : (-I : ℂ) ∈ lowerHalf := by simp [lowerHalf]
  refine ⟨isOpen_lowerHalf, hconv.isConnected ⟨-I, hne⟩, ?_, ?_⟩
  · have : ContractibleSpace ↥lowerHalf := hconv.contractibleSpace ⟨-I, hne⟩
    exact SimplyConnectedSpace.ofContractible _
  · intro h
    have h0 : (0 : ℂ) ∈ lowerHalf := h ▸ mem_univ _
    simp [lowerHalf] at h0

/-- `σ₁(𝕃) = 0`: the conformal map `z ↦ C(-z) = (-z - i)/(-z + i)` of `𝕃` onto `Δ` is a fractional
linear transformation, so its Schwarzian vanishes identically (`sigmaOne_eq`, `schwarzian_mobius`). -/
theorem bA_k_sigmaOne_lowerHalf : sigmaOne lowerHalf = 0 := by
  have hconf : IsConformalOnto (cayley ∘ fun w : ℂ => -w) lowerHalf unitDisc :=
    isConformalOnto_cayley.comp isConformalOnto_neg_lowerHalf
  rw [sigmaOne_eq bA_k_isHyperbolicSimplyConnected_lowerHalf hconf]
  have hmob : (cayley ∘ fun w : ℂ => -w) = fun w => ((-1) * w + (-I)) / ((-1) * w + I) := by
    funext w
    simp only [Function.comp_apply, cayley]
    congr 1 <;> ring
  have hdet : (-1 : ℂ) * I - (-I) * (-1) ≠ 0 := by
    rw [show (-1 : ℂ) * I - (-I) * (-1) = -2 * I by ring]
    exact mul_ne_zero (by norm_num) I_ne_zero
  have hS : ∀ z, schwarzian (cayley ∘ fun w : ℂ => -w) z = 0 := fun z => by
    rw [hmob]
    exact schwarzian_mobius hdet z
  unfold schwarzianNorm
  simp [hS]

/-- A conformal map of `𝕃` is univalent meromorphic there (it is holomorphic, so it has no poles). -/
theorem bA_k_isUnivMero_of_isConformalOnto {f : ℂ → ℂ} {V : Set ℂ}
    (hf : IsConformalOnto f lowerHalf V) : IsUnivMero f lowerHalf :=
  ⟨isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hf, fun _ hw₁ _ hw₂ he => hf.2.1 hw₁.1 hw₂.1 he,
    fun _ hw₁ => absurd (hf.1.analyticAt (isOpen_lowerHalf.mem_nhds hw₁.1)) hw₁.2⟩

/-- **K** (Kraus on `𝕃`): a conformal map of `𝕃` has `‖S_f‖_𝕃 ≤ 3/2` (Theorem 19.3, `σ₂(𝕃) = 3/2 + σ₁(𝕃)`, with
`σ₁(𝕃) = 0` because the conformal map `z ↦ C(-z)` of `𝕃` onto `Δ` is Möbius). -/
theorem bA_kraus_lowerHalf {f : ℂ → ℂ} (hf : IsConformalOnto f lowerHalf (f '' lowerHalf)) :
    schwarzianNorm f lowerHalf ≤ ENNReal.ofReal (3 / 2) := by
  have hR := thm19_3 bA_k_isHyperbolicSimplyConnected_lowerHalf
  rw [bA_k_sigmaOne_lowerHalf, add_zero] at hR
  rw [← hR]
  exact le_iSup₂ (f := fun f (_ : IsUnivMero f lowerHalf) => schwarzianNorm f lowerHalf) f
    (bA_k_isUnivMero_of_isConformalOnto hf)

/-- **N** (the two norms agree): `‖𝟙_𝕃 S_f‖ = sup_{z ∈ 𝕃} |S_f(z)| (Im z)² = ‖S_f‖_𝕃`, since `η_𝕃(z) = 1/|Im z|`
(`poincareDensity_lowerHalf`). -/
theorem bA_bersNormL_eq (f : ℂ → ℂ) :
    bersNormL (lowerHalf.indicator (schwarzian f)) = schwarzianNorm f lowerHalf := by
  unfold bersNormL schwarzianNorm
  refine biSup_congr fun z hz => ?_
  rw [indicator_of_mem hz, poincareDensity_lowerHalf hz, one_div, inv_pow, div_inv_eq_mul, sq_abs]

/-- **W1** (boundary values of a Möbius relation): if `f = M ∘ g` on `𝕃` (off the pole of `M`), with `f, g` continuous
and `g` injective, then for real `x` the point `g(x)` is not the pole of `M` and `f(x) = M(g(x))`: let `z → x` from
`𝕃`; at the pole `M ∘ g` would be unbounded near `x` (the numerator does not vanish there, `ad - bc ≠ 0`). -/
theorem bA_boundary_mobius {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g) (hginj : Function.Injective g)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (h : ∀ z ∈ lowerHalf, c * g z + d ≠ 0 → f z = (a * g z + b) / (c * g z + d)) (x : ℝ) :
    c * g x + d ≠ 0 ∧ f x = (a * g x + b) / (c * g x + d) := by
  have hcl : (x : ℂ) ∈ closure lowerHalf := by simp [lowerHalf]
  have hne : (𝓝[lowerHalf] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hL : ∀ᶠ z in 𝓝[lowerHalf] (x : ℂ), z ∈ lowerHalf := self_mem_nhdsWithin
  have hden : Continuous fun z => c * g z + d := by fun_prop
  have hnum : Continuous fun z => a * g z + b := by fun_prop
  have htf := (hf.tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := lowerHalf))
  by_cases hc : c * g x + d = 0
  · exfalso
    have hN : a * g x + b ≠ 0 := fun hN => hdet (by linear_combination a * hc - c * hN)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hdet (by linear_combination a * hc)
    have hden_ne : ∀ z ∈ lowerHalf, c * g z + d ≠ 0 := by
      intro z hz
      have hzx : z ≠ (x : ℂ) := by
        rintro rfl
        simp [lowerHalf] at hz
      have hcz : c * g z + d = c * (g z - g x) := by linear_combination hc
      rw [hcz]
      exact mul_ne_zero hc0 (sub_ne_zero.2 (hginj.ne hzx))
    have hNpos : 0 < ‖a * g x + b‖ := norm_pos_iff.2 hN
    have h1 : ∀ᶠ z in 𝓝[lowerHalf] (x : ℂ), ‖a * g x + b‖ / 2 < ‖a * g z + b‖ :=
      ((hnum.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds).norm.eventually_const_lt
        (half_lt_self hNpos)
    have h2 : ∀ᶠ z in 𝓝[lowerHalf] (x : ℂ), ‖c * g z + d‖ * (‖f x‖ + 1) < ‖a * g x + b‖ / 2 := by
      have ht := (((hden.tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := lowerHalf))).norm.mul_const (‖f x‖ + 1))
      rw [hc, norm_zero, zero_mul] at ht
      exact ht.eventually_lt_const (half_pos hNpos)
    have h3 : ∀ᶠ z in 𝓝[lowerHalf] (x : ℂ), ‖f z‖ < ‖f x‖ + 1 :=
      htf.norm.eventually_lt_const (lt_add_one _)
    obtain ⟨z, hz, hz1, hz2, hz3⟩ := (hL.and (h1.and (h2.and h3))).exists
    have hdz := hden_ne z hz
    have hnz : a * g z + b = f z * (c * g z + d) := by
      rw [h z hz hdz, div_mul_cancel₀ _ hdz]
    have hle : ‖a * g z + b‖ ≤ ‖c * g z + d‖ * (‖f x‖ + 1) := by
      rw [hnz, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left hz3.le (norm_nonneg _)
    linarith
  · refine ⟨hc, ?_⟩
    have hev : ∀ᶠ z in 𝓝[lowerHalf] (x : ℂ), (a * g z + b) / (c * g z + d) = f z := by
      filter_upwards [hL, nhdsWithin_le_nhds (hden.continuousAt.eventually_ne hc)] with z hz hdz
      exact (h z hz hdz).symm
    exact tendsto_nhds_unique htf
      (((hnum.continuousAt.div hden.continuousAt hc).tendsto.mono_left nhdsWithin_le_nhds).congr' hev)

/-- **W2** helper: for `c ≠ 0`, the Möbius value `(a w + b)/(c w + d)` is bounded by `2(‖a‖ + ‖b‖)/‖c‖` once
`‖w‖ ≥ 1` and `‖c‖ ‖w‖ ≥ 2 ‖d‖` (then `‖c w + d‖ ≥ ‖c‖ ‖w‖ / 2` and `‖a w + b‖ ≤ (‖a‖ + ‖b‖) ‖w‖`). -/
theorem bA_w2_mobius_bound {a b c d w : ℂ} (hc : c ≠ 0) (hw1 : 1 ≤ ‖w‖) (hwd : 2 * ‖d‖ / ‖c‖ ≤ ‖w‖) :
    ‖(a * w + b) / (c * w + d)‖ ≤ 2 * (‖a‖ + ‖b‖) / ‖c‖ := by
  have hC : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hcw : 2 * ‖d‖ ≤ ‖c‖ * ‖w‖ := by
    rw [div_le_iff₀ hC] at hwd
    linarith
  have hden : ‖c‖ * ‖w‖ / 2 ≤ ‖c * w + d‖ := by
    have h1 := norm_sub_le (c * w + d) d
    rw [add_sub_cancel_right, norm_mul] at h1
    linarith
  have hnum : ‖a * w + b‖ ≤ (‖a‖ + ‖b‖) * ‖w‖ := by
    have h1 := norm_add_le (a * w) b
    rw [norm_mul] at h1
    nlinarith [norm_nonneg b]
  have hdpos : 0 < ‖c‖ * ‖w‖ / 2 := by positivity
  rw [norm_div, div_le_iff₀ (hdpos.trans_le hden)]
  calc ‖a * w + b‖ ≤ (‖a‖ + ‖b‖) * ‖w‖ := hnum
    _ = 2 * (‖a‖ + ‖b‖) / ‖c‖ * (‖c‖ * ‖w‖ / 2) := by field_simp
    _ ≤ 2 * (‖a‖ + ‖b‖) / ‖c‖ * ‖c * w + d‖ := mul_le_mul_of_nonneg_left hden (by positivity)

/-- **W2** helper: properness of a normalized `K`-q.c. map of the plane, in contrapositive form: `‖f z‖ > R` once
`‖z‖ > λ(K Λ(R))` (`ut2_nb_lower`). -/
theorem bA_w2_proper {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : lambdaInv (K * quadLambda R) < ‖z‖) : R < ‖f z‖ := by
  by_contra hle
  push Not at hle
  exact absurd (UniversalTeichmuller.ut2_nb_lower hf hR hle) (not_le.2 hz)

/-- **W2** (the Möbius map is the identity): if `f = M ∘ g` on `ℝ` for normalized q.c. maps `f, g` of the plane, then
`f = g` on `ℝ`: `f(x), g(x) → ∞` as `x → ∞` (`ut2_nb_lower`) forces `c = 0`, and then `M(0) = 0`, `M(1) = 1` give
`M = id`. -/
theorem bA_mobius_id {f g : ℂ → ℂ} {K K' : ℝ} (hf : IsKQCNormalizedPlane f K) (hg : IsKQCNormalizedPlane g K')
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (h : ∀ x : ℝ, c * g x + d ≠ 0 ∧ f x = (a * g x + b) / (c * g x + d)) (x : ℝ) : f x = g x := by
  have hc : c = 0 := by
    by_contra hc
    have hR : 0 < 2 * (‖a‖ + ‖b‖) / ‖c‖ + 1 := by positivity
    have hR' : 0 < max 1 (2 * ‖d‖ / ‖c‖) + 1 := by
      have := le_max_left 1 (2 * ‖d‖ / ‖c‖)
      linarith
    set L := lambdaInv (K * quadLambda (2 * (‖a‖ + ‖b‖) / ‖c‖ + 1))
    set L' := lambdaInv (K' * quadLambda (max 1 (2 * ‖d‖ / ‖c‖) + 1))
    have hnt : ‖((|L| + |L'| + 1 : ℝ) : ℂ)‖ = |L| + |L'| + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hft := bA_w2_proper hf hR (z := ((|L| + |L'| + 1 : ℝ) : ℂ))
      (by rw [hnt]; linarith [le_abs_self L, abs_nonneg L'])
    have hgt := bA_w2_proper hg hR' (z := ((|L| + |L'| + 1 : ℝ) : ℂ))
      (by rw [hnt]; linarith [le_abs_self L', abs_nonneg L])
    have hb := bA_w2_mobius_bound (a := a) (b := b) (d := d) hc
      (w := g ((|L| + |L'| + 1 : ℝ) : ℂ)) (by linarith [le_max_left 1 (2 * ‖d‖ / ‖c‖)])
      (by linarith [le_max_right 1 (2 * ‖d‖ / ‖c‖)])
    rw [← (h (|L| + |L'| + 1)).2] at hb
    linarith
  subst hc
  have hd : d ≠ 0 := fun hd => hdet (by rw [hd]; ring)
  have ha : a ≠ 0 := fun ha => hdet (by rw [ha]; ring)
  have hb : b = 0 := by
    have h0 := (h 0).2
    simp only [Complex.ofReal_zero, hf.2.2.1, hg.2.2.1, mul_zero, zero_add] at h0
    exact (div_eq_zero_iff.1 h0.symm).resolve_right hd
  subst hb
  have had : a = d := by
    have h1 := (h 1).2
    simp only [Complex.ofReal_one, hf.2.2.2, hg.2.2.2, mul_one, add_zero, zero_add] at h1
    rw [eq_div_iff hd, one_mul] at h1
    exact h1.symm
  subst had
  rw [(h x).2, zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ ha]

/-- The lower half-plane is connected. -/
theorem bA_isConnected_lowerHalf : IsConnected lowerHalf :=
  ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm).isConnected ⟨-I, by simp⟩

/-- Coefficients whose normalized solutions have the same Schwarzian on `𝕃` are equivalent: `f_μ = M ∘ f_ν` on `𝕃`
(Theorem 19.1), hence on `ℝ` (W1), and `M = id` (W2). -/
theorem bA_equiv_of_schwarzian_eq {μ ν : BeltramiH}
    (h : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution μ.1) z = schwarzian (normalizedSolution ν.1) z) :
    teichSetoid μ ν := by
  have hLo : IsOpen lowerHalf := isOpen_lowerHalf
  obtain ⟨a, b, c, d, hdet, hM⟩ := thm19_1_unique hLo bA_isConnected_lowerHalf
    (isLocUnivMero_of_isConformalOnto hLo (ut_conformal_lowerHalf μ))
    (isLocUnivMero_of_isConformalOnto hLo (ut_conformal_lowerHalf ν)) h
  obtain ⟨⟨Kμ, hKμ⟩, hsμ, hμ0, hμ1, -⟩ := ut_spec μ
  obtain ⟨⟨Kν, hKν⟩, hsν, hν0, hν1, -⟩ := ut_spec ν
  have hb := bA_boundary_mobius (continuousOn_univ.1 hKμ.2.2.1.1) (continuousOn_univ.1 hKν.2.2.1.1)
    (fun x y hxy => hKν.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy) hdet fun z hz hden =>
      hM z hz ((ut_conformal_lowerHalf μ).1.analyticAt (hLo.mem_nhds hz))
        ((ut_conformal_lowerHalf ν).1.analyticAt (hLo.mem_nhds hz)) hden
  exact bA_mobius_id ⟨hKμ, hsμ, hμ0, hμ1⟩ ⟨hKν, hsν, hν0, hν1⟩ hdet hb

/-- `Ψ(T) ⊆ A(𝕃)`, and `‖Ψ(p)‖ ≤ 3/2`. -/
theorem bersMapU_mem (p : UniversalTeichmuller) :
    bersMapU p ∈ bersSpaceL ∧ bersNormL (bersMapU p) ≤ ENNReal.ofReal (3 / 2) := by
  have hconf := ut_conformal_lowerHalf p.out
  have hle : bersNormL (bersMapU p) ≤ ENNReal.ofReal (3 / 2) := by
    rw [bersMapU, bersFunction, bA_bersNormL_eq]
    exact bA_kraus_lowerHalf hconf
  refine ⟨⟨?_, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, hle⟩
  refine (schwarzian_holomorphic isOpen_lowerHalf
    (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hconf)).congr fun z hz => ?_
  exact indicator_of_mem hz _

/-! ### Bers-B track interface (coordinator 553e2d): Lemma 21.1, (21.10) and the Lipschitz bound of Theorem 21.2,
by a holomorphic disc in `M` and the Schwarz lemma -/

/-! #### H0 (proved by the scout): holomorphic dependence of `z`-derivatives on a parameter, for separately holomorphic,
locally uniformly bounded families (difference quotients in `z` converge uniformly in `t`) -/

/-- Cauchy estimate for the second derivative: if `g` is holomorphic on `ball c ε` and bounded
there by `M`, then `‖g''‖ ≤ 8 M / ε²` on `ball c (ε / 2)`. -/
theorem bB_h0_norm_deriv2_le {g : ℂ → ℂ} {c : ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (ball c ε)) (hM : ∀ z ∈ ball c ε, ‖g z‖ ≤ M) :
    ∀ w ∈ ball c (ε / 2), ‖deriv (deriv g) w‖ ≤ 8 * M / ε ^ 2 := by
  intro w hw
  have hsub : closedBall w (ε / 2) ⊆ ball c ε := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball] at hw ⊢
    have := dist_triangle x w c
    linarith
  have hdc : DiffContOnCl ℂ g (ball w (ε / 2)) := hg.diffContOnCl_ball hsub
  have h2 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 (by positivity) hdc
    (fun z hz => hM z (hsub (sphere_subset_closedBall hz)))
  have hit : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hit] at h2
  calc ‖deriv (deriv g) w‖ ≤ (Nat.factorial 2 : ℝ) * M / (ε / 2) ^ 2 := h2
    _ = 8 * M / ε ^ 2 := by
      rw [Nat.factorial_two]
      field_simp
      ring

/-- Lipschitz bound for the derivative: under the hypotheses of `bB_h0_norm_deriv2_le`,
`‖g'(w) - g'(c)‖ ≤ (8 M / ε²) ‖w - c‖` on `ball c (ε / 2)`. -/
theorem bB_h0_deriv_sub_le {g : ℂ → ℂ} {c : ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (ball c ε)) (hM : ∀ z ∈ ball c ε, ‖g z‖ ≤ M) :
    ∀ w ∈ ball c (ε / 2), ‖deriv g w - deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖w - c‖ := by
  intro w hw
  have hd : DifferentiableOn ℂ (deriv g) (ball c ε) := hg.deriv isOpen_ball
  exact (convex_ball c (ε / 2)).norm_image_sub_le_of_norm_deriv_le (f := deriv g)
    (fun x hx => hd.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx)))
    (bB_h0_norm_deriv2_le hε hg hM) (mem_ball_self (by positivity)) hw

/-- First-order Taylor estimate: under the hypotheses of `bB_h0_norm_deriv2_le`,
`‖g(c + h) - g(c) - h g'(c)‖ ≤ (8 M / ε²) ‖h‖²` whenever `‖h‖ < ε / 2`. -/
theorem bB_h0_taylor_le {g : ℂ → ℂ} {c : ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (ball c ε)) (hM : ∀ z ∈ ball c ε, ‖g z‖ ≤ M)
    {h : ℂ} (hh : ‖h‖ < ε / 2) :
    ‖g (c + h) - g c - h * deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖h‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hε))
  have hC0 : 0 ≤ 8 * M / ε ^ 2 := by positivity
  have hsub : closedBall c ‖h‖ ⊆ ball c (ε / 2) := closedBall_subset_ball hh
  have hderiv : ∀ w ∈ closedBall c ‖h‖, HasDerivWithinAt (fun w => g w - w * deriv g c)
      (deriv g w - deriv g c) (closedBall c ‖h‖) w := by
    intro w hw
    have hw' : w ∈ ball c ε := ball_subset_ball (by linarith) (hsub hw)
    have hga : DifferentiableAt ℂ g w := hg.differentiableAt (isOpen_ball.mem_nhds hw')
    exact (hga.hasDerivAt.sub (hasDerivAt_mul_const (deriv g c))).hasDerivWithinAt
  have hbound : ∀ w ∈ closedBall c ‖h‖, ‖deriv g w - deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖h‖ := by
    intro w hw
    calc ‖deriv g w - deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖w - c‖ :=
          bB_h0_deriv_sub_le hε hg hM w (hsub hw)
      _ ≤ 8 * M / ε ^ 2 * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left _ hC0
        rw [mem_closedBall, dist_eq_norm] at hw
        exact hw
  have hmem : c + h ∈ closedBall c ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have key := (convex_closedBall c ‖h‖).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (mem_closedBall_self (norm_nonneg h)) hmem
  have heq : (g (c + h) - (c + h) * deriv g c) - (g c - c * deriv g c)
      = g (c + h) - g c - h * deriv g c := by ring
  rw [heq, add_sub_cancel_left] at key
  calc ‖g (c + h) - g c - h * deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖h‖ * ‖h‖ := key
    _ = 8 * M / ε ^ 2 * ‖h‖ ^ 2 := by ring

/-- Difference-quotient estimate: under the hypotheses of `bB_h0_norm_deriv2_le`,
`‖(g(c + h) - g(c)) / h - g'(c)‖ ≤ (8 M / ε²) ‖h‖` whenever `h ≠ 0` and `‖h‖ < ε / 2`. -/
theorem bB_h0_diffQuot_le {g : ℂ → ℂ} {c : ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (ball c ε)) (hM : ∀ z ∈ ball c ε, ‖g z‖ ≤ M)
    {h : ℂ} (h0 : h ≠ 0) (hh : ‖h‖ < ε / 2) :
    ‖(g (c + h) - g c) / h - deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖h‖ := by
  have hT := bB_h0_taylor_le hε hg hM hh
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
  have heq : (g (c + h) - g c - h * deriv g c) / h = (g (c + h) - g c) / h - deriv g c := by
    rw [sub_div, mul_div_cancel_left₀ _ h0]
  rw [← heq, norm_div, div_le_iff₀ hn]
  calc ‖g (c + h) - g c - h * deriv g c‖ ≤ 8 * M / ε ^ 2 * ‖h‖ ^ 2 := hT
    _ = 8 * M / ε ^ 2 * ‖h‖ * ‖h‖ := by ring

/-- Separately holomorphic, locally uniformly bounded families: the `z`-derivative is holomorphic
in the parameter. -/
theorem bB_h0_deriv_holo {P U : Set ℂ} {F : ℂ → ℂ → ℂ}
    (ha : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖F t z‖ ≤ M) :
    ∀ z ∈ U, DifferentiableOn ℂ (fun t => deriv (F t) z) P := by
  intro z₀ hz₀ t₀ ht₀
  obtain ⟨ε, hε, hPε, hUε, M, hM⟩ := hc t₀ ht₀ z₀ hz₀
  suffices hloc : DifferentiableOn ℂ (fun t => deriv (F t) z₀) (ball t₀ ε) from
    (hloc.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))).differentiableWithinAt
  -- the difference quotients in `z`, indexed by the increment `h ∈ 𝓝[≠] 0`
  let D : ℂ → ℂ → ℂ := fun h t => (F t (z₀ + h) - F t z₀) / h
  have hsmall : ∀ᶠ h in 𝓝[≠] (0 : ℂ), h ≠ 0 ∧ ‖h‖ < ε / 2 := by
    have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), h ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), ‖h‖ < ε / 2 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < ε / 2)] with h hh
      simpa using hh
    exact h1.and h2
  have hD : ∀ᶠ h in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (D h) (ball t₀ ε) := by
    filter_upwards [hsmall] with h hh
    have hz1 : z₀ + h ∈ U := by
      apply hUε
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith [hh.2]
    exact (((ha _ hz1).sub (ha _ hz₀)).div_const h).mono hPε
  have hconv : TendstoUniformlyOn D (fun t => deriv (F t) z₀) (𝓝[≠] (0 : ℂ)) (ball t₀ ε) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have h3 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), 8 * M / ε ^ 2 * ‖h‖ < δ := by
      apply eventually_nhdsWithin_of_eventually_nhds
      have ht : Tendsto (fun h : ℂ => 8 * M / ε ^ 2 * ‖h‖) (𝓝 0) (𝓝 0) := by
        have := (tendsto_norm_zero (E := ℂ)).const_mul (8 * M / ε ^ 2)
        rwa [mul_zero] at this
      exact ht.eventually (eventually_lt_nhds hδ)
    filter_upwards [hsmall, h3] with h hh hCh t ht
    rw [dist_comm, dist_eq_norm]
    have hFt : DifferentiableOn ℂ (F t) (ball z₀ ε) := (hb t (hPε ht)).mono hUε
    exact (bB_h0_diffQuot_le hε hFt (hM t ht) hh.1 hh.2).trans_lt hCh
  exact hconv.tendstoLocallyUniformlyOn.differentiableOn hD isOpen_ball

/-- The `z`-derivatives of such a family are again locally uniformly bounded (Cauchy estimates). -/
theorem bB_h0_deriv_bound {P U : Set ℂ} {F : ℂ → ℂ → ℂ}
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖F t z‖ ≤ M) :
    ∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖deriv (F t) z‖ ≤ M := by
  intro t₀ ht₀ z₀ hz₀
  obtain ⟨ε, hε, hPε, hUε, M, hM⟩ := hc t₀ ht₀ z₀ hz₀
  refine ⟨ε / 2, by positivity, (ball_subset_ball (by linarith)).trans hPε,
    (ball_subset_ball (by linarith)).trans hUε, M / (ε / 2), ?_⟩
  intro t ht z hz
  have ht' : t ∈ ball t₀ ε := ball_subset_ball (by linarith) ht
  have hsub : closedBall z (ε / 2) ⊆ ball z₀ ε := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball] at hz ⊢
    have := dist_triangle x z z₀
    linarith
  have hdc : DiffContOnCl ℂ (F t) (ball z (ε / 2)) :=
    ((hb t (hPε ht')).mono hUε).diffContOnCl_ball hsub
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc
    (fun w hw => hM t ht' w (hsub (sphere_subset_closedBall hw)))

/-- Iterated form: for every `n`, the `n`-th `z`-derivative `iteratedDeriv n (F t) z` is
holomorphic in `t`, holomorphic in `z`, and locally uniformly bounded. -/
theorem bB_h0_iteratedDeriv {P U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ → ℂ}
    (ha : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖F t z‖ ≤ M) (n : ℕ) :
    (∀ z ∈ U, DifferentiableOn ℂ (fun t => iteratedDeriv n (F t) z) P) ∧
    (∀ t ∈ P, DifferentiableOn ℂ (iteratedDeriv n (F t)) U) ∧
    (∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖iteratedDeriv n (F t) z‖ ≤ M) := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨ha, hb, hc⟩
  | succ n ih =>
    obtain ⟨ha', hb', hc'⟩ := ih
    simp only [iteratedDeriv_succ]
    exact ⟨bB_h0_deriv_holo (F := fun t => iteratedDeriv n (F t)) ha' hb' hc',
      fun t ht => (hb' t ht).deriv hU,
      bB_h0_deriv_bound (F := fun t => iteratedDeriv n (F t)) hb' hc'⟩

/-- The first three `z`-derivatives (in the nested-`deriv` form used by `schwarzianHol`) are
holomorphic in the parameter. -/
theorem bB_h0_deriv123_holo {P U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ → ℂ}
    (ha : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ z₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖F t z‖ ≤ M) :
    ∀ z ∈ U, DifferentiableOn ℂ (fun t => deriv (F t) z) P ∧
      DifferentiableOn ℂ (fun t => deriv (deriv (F t)) z) P ∧
      DifferentiableOn ℂ (fun t => deriv (deriv (deriv (F t))) z) P := by
  have h1 := (bB_h0_iteratedDeriv hU ha hb hc 1).1
  have h2 := (bB_h0_iteratedDeriv hU ha hb hc 2).1
  have h3 := (bB_h0_iteratedDeriv hU ha hb hc 3).1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h1 h2 h3
  intro z hz
  exact ⟨h1 z hz, h2 z hz, h3 z hz⟩

/-- The Schwarzian at a point where `f` is analytic with `f' ≠ 0`, expanded by the quotient rule:
`S_f = (f''' f' - f'' f'') / f'² - ½ (f''/f')²`. -/
theorem bB_hs_schwarzian_eq {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hf' : deriv f z ≠ 0) :
    schwarzian f z = (deriv (deriv (deriv f)) z * deriv f z - deriv (deriv f) z * deriv (deriv f) z) /
      deriv f z ^ 2 - 1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2 := by
  rw [schwarzian_of_analyticAt hf, schwarzianHol,
    deriv_fun_div hf.deriv.deriv.differentiableAt hf.deriv.differentiableAt hf']

/-- For `μ ∈ M` with `‖μ‖_∞ ≤ k < 1`, the normalized solution `f_μ` is a normalized `(1 + k)/(1 - k)`-q.c. map of the
plane (Theorem 13.7 and its uniqueness clause identify `f_μ` with the sharp solution). -/
theorem bB_hs_normalizedPlane (μ : BeltramiH) {k : ℝ} (hk₀ : 0 ≤ k) (hk1 : k < 1)
    (hμ : IsBeltramiCoeff μ.1 univ k) :
    IsKQCNormalizedPlane (normalizedSolution μ.1) ((1 + k) / (1 - k)) := by
  obtain ⟨f, -, hfK, huniq⟩ := thm13_7_normalized_existence hk₀ hk1 hμ
  have hs := ut_spec μ
  refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
  rw [huniq _ hs]
  exact hfK

/-- The normalized solutions of such a family are locally uniformly bounded in `(t, w) ∈ P × 𝕃`, for `P` any open
set on which `‖ν t‖_∞ ≤ k` (the growth bound `ut2_nb_upper` with `K = (1 + k)/(1 - k)`). -/
theorem bB_hs_bound {ν : ℂ → BeltramiH} {P : Set ℂ} (hP : IsOpen P) {k : ℝ} (hk₀ : 0 ≤ k) (hk1 : k < 1)
    (hkP : ∀ t ∈ P, IsBeltramiCoeff (ν t).1 univ k) :
    ∀ t₀ ∈ P, ∀ z₀ ∈ lowerHalf, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball z₀ ε ⊆ lowerHalf ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ z ∈ ball z₀ ε, ‖normalizedSolution (ν t).1 z‖ ≤ M := by
  intro t₀ ht₀ z₀ hz₀
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hP t₀ ht₀
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp isOpen_lowerHalf z₀ hz₀
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  refine ⟨min ε₁ ε₂, hε, (ball_subset_ball (min_le_left _ _)).trans hb₁,
    (ball_subset_ball (min_le_right _ _)).trans hb₂,
    lambdaInv ((1 + k) / (1 - k) * quadLambda (‖z₀‖ + min ε₁ ε₂)), fun t ht z hz => ?_⟩
  have htP : t ∈ P := hb₁ (ball_subset_ball (min_le_left _ _) ht)
  refine UniversalTeichmuller.ut2_nb_upper (bB_hs_normalizedPlane (ν t) hk₀ hk1 (hkP t htP))
    (add_pos_of_nonneg_of_pos (norm_nonneg _) hε) ?_
  rw [mem_ball, dist_eq_norm] at hz
  have := norm_sub_norm_le z z₀
  linarith

/-- **HS** (holomorphy of the Schwarzian in the parameter): for a holomorphic family `t ↦ ν t` in `M` over the unit
disc, uniformly `≤ k_r < 1` on each smaller disc, `t ↦ S_{f_{ν t}}(z)` is holomorphic for each `z ∈ 𝕃`
(Theorem 13.8 for `t ↦ f_t(w)`, the bound `ut2_nb_upper`, H0 three times, and
`S = (f'''f' - f''²)/f'² - ½(f''/f')²`). -/
theorem bB_schwarzian_holo {ν : ℂ → BeltramiH}
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => (ν t).1 z) (ball 0 1))
    (hk : ∀ r < 1, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (ν t).1 univ k)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    DifferentiableOn ℂ (fun t => schwarzian (normalizedSolution (ν t).1) z) (ball 0 1) := by
  intro t₀ ht₀
  obtain ⟨r, hr0, hr1⟩ := exists_between (mem_ball_zero_iff.mp ht₀)
  obtain ⟨k, hk₀, hk1, hkP⟩ := hk r hr1
  have hPsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
  have hconf := fun t => ut_conformal_lowerHalf (ν t)
  have ha : ∀ w ∈ lowerHalf, DifferentiableOn ℂ (fun t => normalizedSolution (ν t).1 w) (ball 0 r) :=
    fun w _ => thm13_8_ahlfors_bers_holomorphic (μ := fun t => (ν t).1)
      (f := fun t => normalizedSolution (ν t).1) isOpen_ball hk₀ hk1 hkP
      (fun w => (hhol w).mono hPsub) (fun t _ => ut_spec (ν t)) w
  obtain ⟨hd1, hd2, hd3⟩ := bB_h0_deriv123_holo (F := fun t => normalizedSolution (ν t).1) isOpen_lowerHalf ha
    (fun t _ => (hconf t).1) (bB_hs_bound isOpen_ball hk₀ hk1 hkP) z hz
  have hne : ∀ t, deriv (normalizedSolution (ν t).1) z ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf (hconf t).1 (hconf t).2.1 hz
  have hS : DifferentiableOn ℂ (fun t => schwarzian (normalizedSolution (ν t).1) z) (ball 0 r) := by
    refine ((((hd3.mul hd1).sub (hd2.mul hd2)).div (hd1.pow 2) fun t _ => pow_ne_zero 2 (hne t)).sub
      (((hd2.div hd1 fun t _ => hne t).pow 2).const_mul (1 / 2))).congr fun t _ => ?_
    exact bB_hs_schwarzian_eq ((hconf t).1.analyticAt (isOpen_lowerHalf.mem_nhds hz)) (hne t)
  exact (hS.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hr0))).differentiableWithinAt

/-- Kraus pointwise on `𝕃`: `|S_{f_σ}(z)| (Im z)² ≤ 3/2` for every `σ ∈ M` and `z ∈ 𝕃` (`bA_kraus_lowerHalf`
through `bA_bersNormL_eq`, evaluated at `z`). -/
theorem bB_sd_kraus_pt (σ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖schwarzian (normalizedSolution σ.1) z‖ * z.im ^ 2 ≤ 3 / 2 := by
  have h := bA_kraus_lowerHalf (ut_conformal_lowerHalf σ)
  rw [← bA_bersNormL_eq, bersNormL] at h
  have h2 := (le_iSup₂ (f := fun w (_ : w ∈ lowerHalf) =>
    ENNReal.ofReal (‖lowerHalf.indicator (schwarzian (normalizedSolution σ.1)) w‖ * w.im ^ 2)) z hz).trans h
  rw [indicator_of_mem hz] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 h2

/-- **SD** (the Schwarz lemma on the disc): for such a family, `|S_{f_{ν t}}(z) - S_{f_{ν 0}}(z)| (Im z)² ≤ 3|t|` on `𝕃`:
`Φ(t) = (S_{f_{ν t}}(z) - S_{f_{ν 0}}(z)) (Im z)²` is holomorphic on the unit disc (HS), bounded by `3` (Kraus,
`bA_kraus_lowerHalf`, for each term), and `Φ(0) = 0`. -/
theorem bB_schwarz_disc {ν : ℂ → BeltramiH}
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => (ν t).1 z) (ball 0 1))
    (hk : ∀ r < 1, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (ν t).1 univ k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖schwarzian (normalizedSolution (ν t).1) z - schwarzian (normalizedSolution (ν 0).1) z‖ * z.im ^ 2 ≤
      3 * ‖t‖ := by
  have hdist : ∀ s, dist (schwarzian (normalizedSolution (ν s).1) z * ((z.im ^ 2 : ℝ) : ℂ))
      (schwarzian (normalizedSolution (ν 0).1) z * ((z.im ^ 2 : ℝ) : ℂ)) =
      ‖schwarzian (normalizedSolution (ν s).1) z - schwarzian (normalizedSolution (ν 0).1) z‖ * z.im ^ 2 := by
    intro s
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hmaps : MapsTo (fun s => schwarzian (normalizedSolution (ν s).1) z * ((z.im ^ 2 : ℝ) : ℂ)) (ball 0 1)
      (closedBall (schwarzian (normalizedSolution (ν 0).1) z * ((z.im ^ 2 : ℝ) : ℂ)) 3) := by
    intro s _
    rw [mem_closedBall, hdist]
    have h1 := bB_sd_kraus_pt (ν s) hz
    have h2 := bB_sd_kraus_pt (ν 0) hz
    have h3 := norm_sub_le (schwarzian (normalizedSolution (ν s).1) z)
      (schwarzian (normalizedSolution (ν 0).1) z)
    nlinarith [sq_nonneg z.im]
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((bB_schwarzian_holo hhol hk hz).mul_const _) hmaps ht
  rw [hdist, dist_zero_right, div_one] at h
  exact h

/-! #### DISC helpers: the disc `ν_t = (μ₁ + t ψ̃)/(1 + μ̄₁ t ψ̃)` through `μ₁` (`t = 0`) and `μ₂` (`t = d̃`) -/

/-- DISC: the normalized pseudo-difference `ψ = (μ₂ - μ₁)/((1 - μ̄₁μ₂) d)`. -/
def bB_disc_psi (μ₁ μ₂ : ℂ → ℂ) (d : ℝ) : ℂ → ℂ :=
  fun z => (μ₂ z - μ₁ z) / (1 - conj (μ₁ z) * μ₂ z) / d

/-- DISC: the truncation `ψ̃ = ψ` where `|ψ| ≤ 1` and `|μ₁| ≤ k`, and `ψ̃ = 0` elsewhere. -/
def bB_disc_trunc (μ₁ ψ : ℂ → ℂ) (k : ℝ) : ℂ → ℂ :=
  fun z => if ‖ψ z‖ ≤ 1 ∧ ‖μ₁ z‖ ≤ k then ψ z else 0

/-- DISC: the disc `ν_t = (μ₁ + t ψ̃)/(1 + μ̄₁ t ψ̃)` (`ψ̃` the truncation of `ψ`). -/
def bB_disc_nu (μ₁ ψ : ℂ → ℂ) (k : ℝ) (t : ℂ) : ℂ → ℂ :=
  fun z => (μ₁ z + t * bB_disc_trunc μ₁ ψ k z) / (1 + conj (μ₁ z) * (t * bB_disc_trunc μ₁ ψ k z))

/-- For `k ≤ 1`, the truncation satisfies `|μ̄₁ ψ̃| ≤ 1` everywhere. -/
theorem bB_disc_trunc_norm_le (μ₁ ψ : ℂ → ℂ) {k : ℝ} (hk : k ≤ 1) (z : ℂ) :
    ‖conj (μ₁ z) * bB_disc_trunc μ₁ ψ k z‖ ≤ 1 := by
  unfold bB_disc_trunc
  split_ifs with h
  · rw [norm_mul, Complex.norm_conj]
    nlinarith [h.1, h.2, norm_nonneg (μ₁ z), norm_nonneg (ψ z)]
  · rw [mul_zero, norm_zero]
    exact zero_le_one

/-- The truncation changes nothing where `|ψ| ≤ 1` and `|μ₁| ≤ k`. -/
theorem bB_disc_trunc_eq {μ₁ ψ : ℂ → ℂ} {k : ℝ} {z : ℂ} (h₁ : ‖ψ z‖ ≤ 1) (h₂ : ‖μ₁ z‖ ≤ k) :
    bB_disc_trunc μ₁ ψ k z = ψ z :=
  ite_eq_left ⟨h₁, h₂⟩

/-- A Möbius map `t ↦ (a + t b)/(1 + c t b)` with `|c b| ≤ 1` is holomorphic on the unit disc. -/
theorem bB_disc_hol (a b c : ℂ) (hc : ‖c * b‖ ≤ 1) :
    DifferentiableOn ℂ (fun t => (a + t * b) / (1 + c * (t * b))) (ball 0 1) := by
  refine DifferentiableOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
  have ht' : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
  have hlt : ‖c * (t * b)‖ < 1 := by
    rw [show c * (t * b) = t * (c * b) by ring, norm_mul]
    calc ‖t‖ * ‖c * b‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact ht'
  intro h0
  have h1 : c * (t * b) = -1 := by linear_combination h0
  rw [h1, norm_neg, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- The disc-automorphism bound: `|(a + s)/(1 + ā s)| ≤ (k + r)/(1 + k r)` for `|a| ≤ k < 1`, `|s| ≤ r < 1`
(`|1 + ā s|² - |a + s|² = (1 - |a|²)(1 - |s|²)` and `|1 + ā s| ≤ 1 + |a| |s|`). -/
theorem bB_disc_mob_norm_le {a s : ℂ} {k r : ℝ} (ha : ‖a‖ ≤ k) (hk : k < 1) (hs : ‖s‖ ≤ r) (hr : r < 1) :
    ‖(a + s) / (1 + conj a * s)‖ ≤ (k + r) / (1 + k * r) := by
  have hA0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hS0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hk0 : 0 ≤ k := hA0.trans ha
  have hr0 : 0 ≤ r := hS0.trans hs
  have hid : ‖1 + conj a * s‖ ^ 2 - ‖a + s‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖s‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  have hAS : ‖a‖ * ‖s‖ < 1 := by nlinarith
  have hDle : ‖1 + conj a * s‖ ≤ 1 + ‖a‖ * ‖s‖ := by
    calc ‖1 + conj a * s‖ ≤ ‖(1 : ℂ)‖ + ‖conj a * s‖ := norm_add_le _ _
      _ = 1 + ‖a‖ * ‖s‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
  have hDge : 1 - ‖a‖ * ‖s‖ ≤ ‖1 + conj a * s‖ := by
    have h := norm_add_le (1 + conj a * s) (-(conj a * s))
    rw [add_neg_cancel_right, norm_one, norm_neg, norm_mul, Complex.norm_conj] at h
    linarith
  have hDpos : 0 < ‖1 + conj a * s‖ := by linarith
  rw [norm_div, div_le_div_iff₀ hDpos (by positivity)]
  have hXY : (‖a‖ + ‖s‖) * (1 + k * r) ≤ (k + r) * (1 + ‖a‖ * ‖s‖) := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (by nlinarith : (0 : ℝ) ≤ 1 - r * ‖s‖),
      mul_nonneg (sub_nonneg.2 hs) (by nlinarith : (0 : ℝ) ≤ 1 - k * ‖a‖)]
  have hsq : ((‖a‖ + ‖s‖) * (1 + k * r)) ^ 2 ≤ ((k + r) * (1 + ‖a‖ * ‖s‖)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hXY 2
  have hD2 : ‖1 + conj a * s‖ ^ 2 ≤ (1 + ‖a‖ * ‖s‖) ^ 2 := pow_le_pow_left₀ hDpos.le hDle 2
  have hkr : 0 ≤ (1 - k ^ 2) * (1 - r ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hD2 hkr
  have hkey : (‖a + s‖ * (1 + k * r)) ^ 2 ≤ ((k + r) * ‖1 + conj a * s‖) ^ 2 := by
    have hN2 : ‖a + s‖ ^ 2 = ‖1 + conj a * s‖ ^ 2 - (1 - ‖a‖ ^ 2) * (1 - ‖s‖ ^ 2) := by linarith
    calc (‖a + s‖ * (1 + k * r)) ^ 2 = ‖a + s‖ ^ 2 * (1 + k * r) ^ 2 := by ring
      _ = (‖1 + conj a * s‖ ^ 2 - (1 - ‖a‖ ^ 2) * (1 - ‖s‖ ^ 2)) * (1 + k * r) ^ 2 := by rw [hN2]
      _ ≤ ((k + r) * ‖1 + conj a * s‖) ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hkey

/-- `(k + r)/(1 + k r) < 1` for `0 ≤ k, r < 1`. -/
theorem bB_disc_bound_lt_one {k r : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (k + r) / (1 + k * r) < 1 := by
  rw [div_lt_one (by positivity)]
  nlinarith [mul_pos (sub_pos.2 hk1) (sub_pos.2 hr1)]

/-- The endpoint algebra: `(a + q)/(1 + ā q) = b` for `q = (b - a)/(1 - ā b)` and `|a|, |b| < 1`. -/
theorem bB_disc_mob_alg {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    (a + (b - a) / (1 - conj a * b)) / (1 + conj a * ((b - a) / (1 - conj a * b))) = b := by
  have hne : ∀ c : ℂ, ‖c‖ < 1 → 1 - conj a * c ≠ 0 := by
    intro c hc h
    have hlt : ‖conj a * c‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg a, norm_nonneg c]
    rw [← sub_eq_zero.1 h, norm_one] at hlt
    exact lt_irrefl _ hlt
  have h1 := hne b hb
  have h2 := hne a ha
  have hnum : a + (b - a) / (1 - conj a * b) = b * (1 - conj a * a) / (1 - conj a * b) := by
    rw [eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
    ring
  have hden : 1 + conj a * ((b - a) / (1 - conj a * b)) = (1 - conj a * a) / (1 - conj a * b) := by
    rw [eq_div_iff h1, add_mul, mul_div_assoc', div_mul_cancel₀ _ h1]
    ring
  rw [hnum, hden, div_div_div_cancel_right₀ h1, mul_div_cancel_right₀ _ h2]

/-- `ψ` vanishes on the closed lower half-plane, where `μ₁` and `μ₂` do. -/
theorem bB_disc_psi_zero {μ₁ μ₂ : ℂ → ℂ} (h₁ : ∀ z : ℂ, z.im ≤ 0 → μ₁ z = 0) (h₂ : ∀ z : ℂ, z.im ≤ 0 → μ₂ z = 0)
    (d : ℝ) {z : ℂ} (hz : z.im ≤ 0) : bB_disc_psi μ₁ μ₂ d z = 0 := by
  simp [bB_disc_psi, h₁ z hz, h₂ z hz]

/-- `ψ` is a.e. strongly measurable. -/
theorem bB_disc_psi_aesm {μ₁ μ₂ : ℂ → ℂ} (h₁ : AEStronglyMeasurable μ₁ volume)
    (h₂ : AEStronglyMeasurable μ₂ volume) (d : ℝ) : AEStronglyMeasurable (bB_disc_psi μ₁ μ₂ d) volume := by
  have hc : AEStronglyMeasurable (fun z => conj (μ₁ z)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable h₁
  exact ((h₂.sub h₁).div₀ (aestronglyMeasurable_const.sub (hc.mul h₂))).div₀ aestronglyMeasurable_const

/-- For `d̃ = ‖(μ₂ - μ₁)/(1 - μ̄₁μ₂)‖_∞ > 0` (over `ℍ`), `|ψ| ≤ 1` a.e. on `ℂ`: on `ℍ` by the definition of the
essential supremum (finite, since `d̃ > 0`), off `ℍ` since `ψ = 0` there. -/
theorem bB_disc_psi_le_one (μ₁ μ₂ : BeltramiH) (hd : 0 < UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1) :
    ∀ᵐ z, ‖bB_disc_psi μ₁.1 μ₂.1 (UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1) z‖ ≤ 1 := by
  have hne : essSup (fun z => (‖(μ₂.1 z - μ₁.1 z) / (1 - conj (μ₁.1 z) * μ₂.1 z)‖₊ : ℝ≥0∞))
      (volume.restrict upperHalf) ≠ ⊤ := by
    intro h
    have h0 : UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 = 0 := by
      rw [UniversalTeichmuller.dilatationDiffNorm, h, ENNReal.toReal_top]
    linarith
  have hae := ENNReal.ae_le_essSup (μ := volume.restrict upperHalf)
    (fun z => (‖(μ₂.1 z - μ₁.1 z) / (1 - conj (μ₁.1 z) * μ₂.1 z)‖₊ : ℝ≥0∞))
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hae
  filter_upwards [hae] with z hz
  by_cases hi : 0 < z.im
  · have h1 := ENNReal.toReal_mono hne (hz hi)
    rw [ENNReal.coe_toReal, coe_nnnorm] at h1
    rw [bB_disc_psi, norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le, div_le_one hd]
    exact h1
  · rw [bB_disc_psi_zero (fun z hz => μ₁.2.2 z hz) (fun z hz => μ₂.2.2 z hz) _ (not_lt.1 hi), norm_zero]
    exact zero_le_one

/-- `ν_t` vanishes on the closed lower half-plane. -/
theorem bB_disc_nu_zero {μ₁ ψ : ℂ → ℂ} (h₁ : ∀ z : ℂ, z.im ≤ 0 → μ₁ z = 0) (hψ : ∀ z : ℂ, z.im ≤ 0 → ψ z = 0)
    (k : ℝ) (t : ℂ) {z : ℂ} (hz : z.im ≤ 0) : bB_disc_nu μ₁ ψ k t z = 0 := by
  simp [bB_disc_nu, bB_disc_trunc, h₁ z hz, hψ z hz]

/-- `ν_t` is a Beltrami coefficient with bound `(k₁ + r)/(1 + k₁ r)` for `|t| ≤ r < 1` (measurable since `ψ̃ = ψ`
a.e.; the bound is `bB_disc_mob_norm_le` with `s = t ψ̃`). -/
theorem bB_disc_coeff {μ₁ ψ : ℂ → ℂ} {k₁ r : ℝ} (hk1 : k₁ < 1) (hμ₁ : IsBeltramiCoeff μ₁ univ k₁)
    (hψm : AEStronglyMeasurable ψ volume) (hψ1 : ∀ᵐ z, ‖ψ z‖ ≤ 1) {t : ℂ} (ht : ‖t‖ ≤ r) (hr : r < 1) :
    IsBeltramiCoeff (bB_disc_nu μ₁ ψ k₁ t) univ ((k₁ + r) / (1 + k₁ * r)) := by
  obtain ⟨hμm, hμb⟩ := hμ₁
  rw [Measure.restrict_univ] at hμm hμb
  have htr : bB_disc_trunc μ₁ ψ k₁ =ᵐ[volume] ψ := by
    filter_upwards [hμb, hψ1] with z h1 h2
    exact bB_disc_trunc_eq h2 h1
  have htm : AEStronglyMeasurable (bB_disc_trunc μ₁ ψ k₁) volume := hψm.congr htr.symm
  have hc : AEStronglyMeasurable (fun z => conj (μ₁ z)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hμm
  rw [IsBeltramiCoeff, Measure.restrict_univ]
  refine ⟨(hμm.add (htm.const_mul t)).div₀ (aestronglyMeasurable_const.add (hc.mul (htm.const_mul t))), ?_⟩
  filter_upwards [hμb, htr, hψ1] with z h1 h2 h3
  have hs : ‖t * bB_disc_trunc μ₁ ψ k₁ z‖ ≤ r := by
    rw [norm_mul, h2]
    calc ‖t‖ * ‖ψ z‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ ≤ r := by rw [mul_one]; exact ht
  exact bB_disc_mob_norm_le h1 hk1 hs hr

/-- `ν_t ∈ M` for `|t| < 1`. -/
theorem bB_disc_mem {μ₁ ψ : ℂ → ℂ} {k₁ : ℝ} (hk0 : 0 ≤ k₁) (hk1 : k₁ < 1) (hμ₁ : IsBeltramiCoeff μ₁ univ k₁)
    (h₁ : ∀ z : ℂ, z.im ≤ 0 → μ₁ z = 0) (hψm : AEStronglyMeasurable ψ volume) (hψ1 : ∀ᵐ z, ‖ψ z‖ ≤ 1)
    (hψ : ∀ z : ℂ, z.im ≤ 0 → ψ z = 0) {t : ℂ} (ht : ‖t‖ < 1) :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (bB_disc_nu μ₁ ψ k₁ t) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → bB_disc_nu μ₁ ψ k₁ t z = 0 :=
  ⟨⟨(k₁ + ‖t‖) / (1 + k₁ * ‖t‖), by positivity, bB_disc_bound_lt_one hk0 hk1 (norm_nonneg t) ht,
    bB_disc_coeff hk1 hμ₁ hψm hψ1 le_rfl ht⟩, fun _ hz => bB_disc_nu_zero h₁ hψ k₁ t hz⟩

/-- The endpoint: `ν_d = μ₂` a.e. (for `d ≠ 0` and `|ψ| ≤ 1` a.e.; `bB_disc_mob_alg`). -/
theorem bB_disc_nu_endpoint {μ₁ μ₂ : ℂ → ℂ} {k₁ k₂ d : ℝ} (hd : d ≠ 0) (hk₁ : k₁ < 1) (hk₂ : k₂ < 1)
    (hb₁ : ∀ᵐ z, ‖μ₁ z‖ ≤ k₁) (hb₂ : ∀ᵐ z, ‖μ₂ z‖ ≤ k₂) (hψ1 : ∀ᵐ z, ‖bB_disc_psi μ₁ μ₂ d z‖ ≤ 1) :
    ∀ᵐ z, bB_disc_nu μ₁ (bB_disc_psi μ₁ μ₂ d) k₁ d z = μ₂ z := by
  filter_upwards [hb₁, hb₂, hψ1] with z h1 h2 h3
  have hdq : (d : ℂ) * bB_disc_psi μ₁ μ₂ d z = (μ₂ z - μ₁ z) / (1 - conj (μ₁ z) * μ₂ z) :=
    mul_div_cancel₀ _ (ofReal_ne_zero.2 hd)
  rw [bB_disc_nu, bB_disc_trunc_eq h3 h1, hdq]
  exact bB_disc_mob_alg (h1.trans_lt hk₁) (h2.trans_lt hk₂)

/-- Normalized solutions of a.e.-equal coefficients in `M` coincide (`thm13_5_uniqueness_plane`). -/
theorem bB_disc_nsol_eq {ν μ : BeltramiH} (h : ∀ᵐ z, ν.1 z = μ.1 z) :
    normalizedSolution ν.1 = normalizedSolution μ.1 := by
  obtain ⟨hq, hs, h0, h1, hc⟩ := ut_spec ν
  obtain ⟨hq', hs', h0', h1', hc'⟩ := ut_spec μ
  refine thm13_5_uniqueness_plane hq hq' hs hs' ?_ h0 h1 h0' h1'
  filter_upwards [hc, hc', h] with z e1 e2 e3
  rw [e1, e2, e3]

/-- **DISC** (a holomorphic disc in `M` through `μ₁` and `μ₂`): for `d̃ = ‖(μ₂ - μ₁)/(1 - μ̄₁μ₂)‖_∞ > 0`,
`ν_t = (μ₁ + tψ)/(1 + t μ̄₁ψ)` with `ψ = (μ₂ - μ₁)/((1 - μ̄₁μ₂) d̃)`, truncated to `0` on the null set where `|ψ| > 1`
or `|μ₁| > k₁`: it is holomorphic in `t` at every point, uniformly `< 1` on smaller discs, `ν_0 = μ₁`, and
`ν_{d̃} = μ₂` a.e. (so `f_{ν_{d̃}} = f_{μ₂}` by uniqueness). -/
theorem bB_disc (μ₁ μ₂ : BeltramiH) (hd : 0 < UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1) :
    ∃ ν : ℂ → BeltramiH, (∀ z, DifferentiableOn ℂ (fun t => (ν t).1 z) (ball 0 1)) ∧
      (∀ r < 1, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ t ∈ ball (0 : ℂ) r, IsBeltramiCoeff (ν t).1 univ k) ∧
      (ν 0).1 = μ₁.1 ∧
      normalizedSolution (ν ((UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 : ℝ) : ℂ)).1 =
        normalizedSolution μ₂.1 := by
  obtain ⟨⟨k₁, hk₁0, hk₁1, hμ₁⟩, hμ₁0⟩ := μ₁.2
  obtain ⟨⟨k₂, -, hk₂1, hμ₂⟩, hμ₂0⟩ := μ₂.2
  have hd1 : UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 < 1 := (UniversalTeichmuller.ut_v_eq μ₂ μ₁).1
  have hψ1 := bB_disc_psi_le_one μ₁ μ₂ hd
  set d := UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1
  have hm₁ := hμ₁.1
  have hm₂ := hμ₂.1
  have hb₁ := hμ₁.2
  have hb₂ := hμ₂.2
  rw [Measure.restrict_univ] at hm₁ hm₂ hb₁ hb₂
  have hψ0 : ∀ z : ℂ, z.im ≤ 0 → bB_disc_psi μ₁.1 μ₂.1 d z = 0 := fun _ hz =>
    bB_disc_psi_zero hμ₁0 hμ₂0 d hz
  -- the parameter, clamped to the unit disc (`ν_t = μ₁` for `|t| ≥ 1`)
  have hc1 : ∀ t : ℂ, ‖if ‖t‖ < 1 then t else 0‖ < 1 := by
    intro t
    split_ifs with h
    · exact h
    · rw [norm_zero]
      exact zero_lt_one
  have hcb : ∀ t : ℂ, ‖t‖ < 1 → (if ‖t‖ < 1 then t else 0) = t := fun _ ht => ite_eq_left ht
  refine ⟨fun t => ⟨bB_disc_nu μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ (if ‖t‖ < 1 then t else 0),
    bB_disc_mem hk₁0 hk₁1 hμ₁ hμ₁0 (bB_disc_psi_aesm hm₁ hm₂ d) hψ1 hψ0 (hc1 t)⟩,
    fun z => ?_, fun r hr => ?_, ?_, ?_⟩
  · -- holomorphy in `t` at every `z`
    refine (bB_disc_hol (μ₁.1 z) (bB_disc_trunc μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ z) (conj (μ₁.1 z))
      (bB_disc_trunc_norm_le _ _ hk₁1.le z)).congr fun t ht => ?_
    show bB_disc_nu μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ (if ‖t‖ < 1 then t else 0) z = _
    rw [hcb t (mem_ball_zero_iff.1 ht)]
    rfl
  · -- the uniform bound on `ball 0 r`
    refine ⟨(k₁ + max r 0) / (1 + k₁ * max r 0), by positivity,
      bB_disc_bound_lt_one hk₁0 hk₁1 (le_max_right _ _) (max_lt hr zero_lt_one), fun t ht => ?_⟩
    have ht' : ‖t‖ < r := mem_ball_zero_iff.1 ht
    show IsBeltramiCoeff (bB_disc_nu μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ (if ‖t‖ < 1 then t else 0)) univ _
    rw [hcb t (ht'.trans hr)]
    exact bB_disc_coeff hk₁1 hμ₁ (bB_disc_psi_aesm hm₁ hm₂ d) hψ1 (ht'.le.trans (le_max_left _ _))
      (max_lt hr zero_lt_one)
  · -- `ν_0 = μ₁`
    show bB_disc_nu μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ (if ‖(0 : ℂ)‖ < 1 then 0 else 0) = μ₁.1
    funext z
    simp [bB_disc_nu]
  · -- `ν_d = μ₂` a.e., hence `f_{ν_d} = f_{μ₂}`
    refine bB_disc_nsol_eq ?_
    show ∀ᵐ z, bB_disc_nu μ₁.1 (bB_disc_psi μ₁.1 μ₂.1 d) k₁ (if ‖(d : ℂ)‖ < 1 then (d : ℂ) else 0) z = μ₂.1 z
    rw [hcb _ (by rw [Complex.norm_real, Real.norm_of_nonneg hd.le]; exact hd1)]
    exact bB_disc_nu_endpoint hd.ne' hk₁1 hk₂1 hb₁ hb₂ hψ1

/-- `x ≤ ln((1 + x)/(1 - x))` for `0 ≤ x < 1` (`(1 + x)/(1 - x) ≥ 1/(1 - x) ≥ e^x`). -/
theorem bB_le_log_quot {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : x ≤ Real.log ((1 + x) / (1 - x)) := by
  rw [Real.le_log_iff_exp_le (div_pos (by linarith) (by linarith)), le_div_iff₀ (by linarith)]
  have h := Real.add_one_le_exp (-x)
  have hpos := Real.exp_pos x
  have hmul : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith

/-- (21.10) pointwise: `|S_{f_{μ₂}}(z) - S_{f_{μ₁}}(z)| (Im z)² ≤ 3 ‖(μ₂ - μ₁)/(1 - μ̄₁μ₂)‖_∞` on `𝕃` (the disc DISC
and the Schwarz lemma SD at `t = d̃`; for `d̃ = 0`, `μ₂ ∼ μ₁` and the Schwarzians agree on `𝕃`). -/
theorem bB_eq21_10_pt (μ₁ μ₂ : BeltramiH) {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖schwarzian (normalizedSolution μ₂.1) z - schwarzian (normalizedSolution μ₁.1) z‖ * z.im ^ 2 ≤
      3 * UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 := by
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 := ENNReal.toReal_nonneg
  obtain ⟨hd1, hv⟩ := UniversalTeichmuller.ut_v_eq μ₂ μ₁
  rcases hd0.eq_or_lt with h0 | hpos
  · -- `d̃ = 0`: `μ₂ ∼ μ₁`, so the Schwarzians agree on `𝕃`
    have hv0 : ut_v μ₂ μ₁ = 0 := by
      rw [hv, ← h0]
      norm_num
    have hS := congrFun (bersFunction_eq_of_equiv (UniversalTeichmuller.ut2_equiv_of_v_eq_zero hv0)) z
    simp only [bersFunction, indicator_of_mem hz] at hS
    rw [hS, sub_self, norm_zero, zero_mul, ← h0, mul_zero]
  · obtain ⟨ν, hhol, hk, h0, h1⟩ := bB_disc μ₁ μ₂ hpos
    have ht : ((UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hd0]
      exact hd1
    have h := bB_schwarz_disc hhol hk ht hz
    rw [h1, h0, Complex.norm_real, Real.norm_of_nonneg hd0] at h
    exact h

/-- Post-composition with an affine map `u ↦ (u - b)/a` (`a ≠ 0`) keeps a `K`-q.c. map of the plane onto itself
`K`-q.c. and onto (Theorem 7.1 with the conformal affine map). -/
theorem bB_l_affine_isKQC {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    IsKQC (fun ζ => (f ζ - b) / a) univ K ∧ (fun ζ => (f ζ - b) / a) '' univ = univ := by
  have hA := nxE_affine_isConformalOnto (b := b) ha
  have h := thm7_1_comp hf (isKQC_one_of_conformal isOpen_univ hA) (subset_univ _)
  rw [mul_one] at h
  refine ⟨h, ?_⟩
  have himg : (fun ζ => (f ζ - b) / a) = (fun u => (u - b) / a) ∘ f := rfl
  rw [himg, image_comp, hs, hA.2.2]

/-- Post-composition with an affine map does not change the Schwarzian on `𝕃` of a map which is conformal there
(`schwarzian_mobius_comp`). -/
theorem bB_l_schwarzian_affine {f : ℂ → ℂ} (hhol : DifferentiableOn ℂ f lowerHalf)
    (hinj : InjOn f lowerHalf) {a : ℂ} (b : ℂ) (ha : a ≠ 0) {z : ℂ} (hz : z ∈ lowerHalf) :
    schwarzian (fun ζ => (f ζ - b) / a) z = schwarzian f z := by
  have hL : IsLocUnivMero f lowerHalf :=
    isLocUnivMero_of_isConformalOnto isOpen_lowerHalf ⟨hhol, hinj, rfl⟩
  have hfun : (fun ζ => (f ζ - b) / a) = fun ζ => (1 * f ζ + -b) / (0 * f ζ + a) := by
    funext ζ
    rw [one_mul, zero_mul, zero_add, ← sub_eq_add_neg]
  rw [hfun]
  exact schwarzian_mobius_comp hL (by rw [one_mul, mul_zero, sub_zero]; exact ha) hz

/-- **Normalization.** A q.c. map `f` of the plane onto itself which is holomorphic in `𝕃` has a normalized
affine post-composition `g = (f - f(0))/(f(1) - f(0))` with the same complex dilatation everywhere and the same
Schwarzian on `𝕃`. -/
theorem bB_l_normalize {f : ℂ → ℂ} {K : ℝ} (hK : IsKQC f univ K) (hs : f '' univ = univ)
    (hhol : DifferentiableOn ℂ f lowerHalf) :
    ∃ g : ℂ → ℂ, IsKQCNormalizedPlane g K ∧ DifferentiableOn ℂ g lowerHalf ∧
      (∀ z, complexDilatation g z = complexDilatation f z) ∧
      ∀ z ∈ lowerHalf, schwarzian g z = schwarzian f z := by
  have hinj : InjOn f univ := hK.2.2.1.2.1
  have ha : f 1 - f 0 ≠ 0 :=
    sub_ne_zero.2 fun h => one_ne_zero (hinj (mem_univ _) (mem_univ _) h)
  obtain ⟨hgK, hgs⟩ := bB_l_affine_isKQC hK hs (f 0) ha
  refine ⟨fun ζ => (f ζ - f 0) / (f 1 - f 0), ⟨hgK, hgs, by simp, div_self ha⟩,
    (hhol.sub_const (f 0)).div_const (f 1 - f 0), fun z => nxE_complexDilatation_affine ha z,
    fun z hz => bB_l_schwarzian_affine hhol (hinj.mono (subset_univ _)) (f 0) ha hz⟩

/-- The complex dilatation of a map holomorphic in `𝕃` vanishes there (`∂_{z̄} g = 0`, Cauchy–Riemann). -/
theorem bB_l_dilatation_lowerHalf {g : ℂ → ℂ} (hhol : DifferentiableOn ℂ g lowerHalf) {z : ℂ}
    (hz : z ∈ lowerHalf) : complexDilatation g z = 0 := by
  have hd : DifferentiableAt ℂ g z := hhol.differentiableAt (isOpen_lowerHalf.mem_nhds hz)
  rw [complexDilatation, (cauchyRiemann_iff.1 hd).2, zero_div]

/-- For a map holomorphic in `𝕃`, the complex dilatation agrees a.e. with its cut-off to `ℍ` (it vanishes on `𝕃`,
and `ℝ` is null). -/
theorem bB_l_indicator_ae_eq {g : ℂ → ℂ} (hhol : DifferentiableOn ℂ g lowerHalf) :
    ∀ᵐ z, upperHalf.indicator (complexDilatation g) z = complexDilatation g z := by
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  filter_upwards [hnull] with z hz
  rcases lt_or_gt_of_ne (hz : z.im ≠ 0) with hlt | hgt
  · have hnu : z ∉ upperHalf := fun hu => absurd hlt (not_lt.2 (le_of_lt hu))
    rw [Set.indicator_of_notMem hnu, bB_l_dilatation_lowerHalf hhol hlt]
  · exact Set.indicator_of_mem (show z ∈ upperHalf from hgt) _

/-- A normalized q.c. map of the plane which is holomorphic in `𝕃` is the normalized solution `f_μ` for its complex
dilatation cut off to `ℍ` (uniqueness, Theorem 13.5). -/
theorem bB_l_normalizedSolution_eq {g : ℂ → ℂ} {K : ℝ} (hg : IsKQCNormalizedPlane g K)
    (hhol : DifferentiableOn ℂ g lowerHalf) :
    normalizedSolution (upperHalf.indicator (complexDilatation g)) = g := by
  obtain ⟨hq, hs, hq0, hq1, hd⟩ :=
    ut_spec ⟨upperHalf.indicator (complexDilatation g), ut_rg_indicator_mem hg.1⟩
  refine thm13_5_uniqueness_plane hq ⟨K, hg.1⟩ hs hg.2.1 ?_ hq0 hq1 hg.2.2.1 hg.2.2.2
  filter_upwards [hd, bB_l_indicator_ae_eq hhol] with z h1 h2
  exact h1.trans h2

/-- The coefficient `μ = 0` lies in `M`. -/
theorem bB_l_zero_mem :
    (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (0 : ℂ → ℂ) univ k) ∧
      ∀ z : ℂ, z.im ≤ 0 → (0 : ℂ → ℂ) z = 0 :=
  ⟨⟨0, le_refl 0, zero_lt_one, aestronglyMeasurable_const, by simp⟩, fun _ _ => rfl⟩

/-- `f_0 = id` (uniqueness, Theorem 13.5, with `td_id_normalized`). -/
theorem bB_l_normalizedSolution_zero : normalizedSolution (0 : ℂ → ℂ) = id := by
  obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ⟨0, bB_l_zero_mem⟩
  obtain ⟨hi, his, hi0, hi1, hid⟩ :=
    td_id_normalized (μ := (0 : ℂ → ℂ)) (Eventually.of_forall fun _ => rfl)
  refine thm13_5_uniqueness_plane hq hi hs his ?_ hq0 hq1 hi0 hi1
  filter_upwards [hd, hid] with z h1 h2
  exact h1.trans h2.symm

/-- The Schwarzian of the identity vanishes (`schwarzian_mobius` with `(1, 0, 0, 1)`). -/
theorem bB_l_schwarzian_id (z : ℂ) : schwarzian id z = 0 := by
  have h : (id : ℂ → ℂ) = fun w => (1 * w + 0) / (0 * w + 1) := by
    funext w
    simp
  rw [h]
  exact schwarzian_mobius (by norm_num) z

/-- `‖(μ - 0)/(1 - 0̄ μ)‖_∞ = ‖μ‖_∞` (over `ℍ`). -/
theorem bB_l_dilatationDiffNorm_zero (μ : ℂ → ℂ) :
    UniversalTeichmuller.dilatationDiffNorm μ 0 =
      (essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)).toReal := by
  simp [UniversalTeichmuller.dilatationDiffNorm]

/-- The ENNReal step: `ofReal (3 ‖μ‖_{∞, ℍ}) ≤ 3 ‖ν‖_∞` when `|μ| ≤ |ν|` pointwise (`ofReal (toReal x) ≤ x`, and the
essential supremum is monotone in the function and in the measure). -/
theorem bB_l_ofReal_le {μ ν : ℂ → ℂ} (hle : ∀ z, ‖μ z‖ ≤ ‖ν z‖) :
    ENNReal.ofReal (3 * (essSup (fun z => (‖μ z‖₊ : ℝ≥0∞)) (volume.restrict upperHalf)).toReal) ≤
      3 * essSup (fun z => (‖ν z‖₊ : ℝ≥0∞)) volume := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  gcongr
  refine ENNReal.ofReal_toReal_le.trans ((essSup_mono_ae (Eventually.of_forall fun z => ?_)).trans
    (essSup_mono_measure' Measure.restrict_le_self))
  exact ENNReal.coe_le_coe.2 (by exact_mod_cast hle z)

/-- **Lemma 21.1**: if `f` is a quasiconformal map of the plane which is holomorphic (and
univalent) in `𝕃`, then `‖S_f|𝕃‖ ≤ 3 ‖μ_f‖_∞`. -/
theorem lemma21_1 {f : ℂ → ℂ} (hf : IsQuasiconformal f univ) (hs : f '' univ = univ)
    (hhol : DifferentiableOn ℂ f lowerHalf) :
    bersNormL (lowerHalf.indicator (schwarzian f)) ≤
      3 * essSup (fun z => (‖complexDilatation f z‖₊ : ℝ≥0∞)) volume := by
  -- normalize `f` to `g = (f - f(0))/(f(1) - f(0))`, compare `μ₂ = μ_g|ℍ` (so `f_{μ₂} = g`) with `μ₁ = 0`
  -- (so `f_{μ₁} = id`) by (21.10), and bound `‖μ₂‖_∞ ≤ ‖μ_f‖_∞`
  obtain ⟨K, hK⟩ := hf
  obtain ⟨g, hg, hghol, hgd, hgS⟩ := bB_l_normalize hK hs hhol
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂ : BeltramiH, μ₂.1 = upperHalf.indicator (complexDilatation g) :=
    ⟨⟨_, ut_rg_indicator_mem hg.1⟩, rfl⟩
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : BeltramiH, μ₁.1 = 0 := ⟨⟨0, bB_l_zero_mem⟩, rfl⟩
  unfold bersNormL
  refine iSup₂_le fun z hz => ?_
  have h := bB_eq21_10_pt μ₁ μ₂ hz
  rw [hμ₂, hμ₁, bB_l_normalizedSolution_eq hg hghol, bB_l_normalizedSolution_zero, bB_l_schwarzian_id,
    sub_zero, hgS z hz, bB_l_dilatationDiffNorm_zero] at h
  rw [indicator_of_mem hz]
  refine (ENNReal.ofReal_le_ofReal h).trans (bB_l_ofReal_le fun w => ?_)
  rw [← hgd w]
  exact norm_indicator_le_norm_self _ _

/-- (21.10): `‖S_{f_{μ₂}} - S_{f_{μ₁}}‖ ≤ 3 ‖(μ₂ - μ₁)/(1 - μ̄₁μ₂)‖_∞`. -/
theorem eq21_10 (μ₁ μ₂ : BeltramiH) :
    bersNormL (bersFunction μ₂.1 - bersFunction μ₁.1) ≤
      ENNReal.ofReal (3 * UniversalTeichmuller.dilatationDiffNorm μ₂.1 μ₁.1) := by
  unfold bersNormL
  refine iSup₂_le fun z hz => ?_
  rw [Pi.sub_apply, bersFunction, bersFunction, indicator_of_mem hz, indicator_of_mem hz]
  exact ENNReal.ofReal_le_ofReal (bB_eq21_10_pt μ₁ μ₂ hz)

/-- **Theorem 21.2** (continuity): `‖Ψ(q) - Ψ(p)‖ ≤ 3 d(p, q)`. -/
theorem thm21_2_lipschitz (p q : UniversalTeichmuller) :
    bersNormL (bersMapU q - bersMapU p) ≤ ENNReal.ofReal (3 * UniversalTeichmuller.dist p q) := by
  obtain ⟨μ, ν, hμ, hν, hd⟩ := UniversalTeichmuller.eq21_1 p q
  have hp : bersMapU p = bersFunction μ.1 :=
    bersFunction_eq_of_equiv (Quotient.exact ((Quotient.out_eq p).trans hμ.symm))
  have hq : bersMapU q = bersFunction ν.1 :=
    bersFunction_eq_of_equiv (Quotient.exact ((Quotient.out_eq q).trans hν.symm))
  rw [hp, hq]
  refine (eq21_10 μ ν).trans (ENNReal.ofReal_le_ofReal ?_)
  obtain ⟨hd1, hv⟩ := UniversalTeichmuller.ut_v_eq μ ν
  have hd0 : 0 ≤ UniversalTeichmuller.dilatationDiffNorm μ.1 ν.1 := ENNReal.toReal_nonneg
  have hdist : UniversalTeichmuller.dist p q = ut_v μ ν := hd
  rw [UniversalTeichmuller.ut_d_symm, hdist, hv]
  linarith [bB_le_log_quot hd0 hd1]

/-- **Theorem 21.2** (injectivity). -/
theorem thm21_2_injective : Function.Injective bersMapU := by
  intro p q hpq
  have hS : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution p.out.1) z =
      schwarzian (normalizedSolution q.out.1) z := by
    intro z hz
    have h := congrFun hpq z
    simp only [bersMapU, bersFunction, indicator_of_mem hz] at h
    exact h
  rw [← Quotient.out_eq p, ← Quotient.out_eq q]
  exact Quotient.sound (bA_equiv_of_schwarzian_eq hS)

/-! ### Ahlfors–Weill track interface (coordinator 553e2d): Theorems 21.2 (inverse continuity) and 21.3 (openness)

For `p = [μ]`, `f = f_μ` is conformal on `𝕃` and `D_p = f(𝕃)` is a quasidisc.  For `φ ∈ A(𝕃)` near `Ψp`, the quadratic
differential `φ - Ψp` transported to `D_p` is the Schwarzian of a `g` which Theorem 20.3 makes univalent with a
quasiconformal extension; the normalized `M ∘ ĝ ∘ f̂` is `f_{ν'}` with `Ψ[ν'] = φ` and `ut_v μ ν'` small. -/

/-- The boundary of `𝕃` in `ℂ̄` is the extended real line `ℝ ∪ {∞}`: it is the image of `∂ℍ = ℝ ∪ {∞}` under the
homeomorphism of `ℂ̄` induced by `z ↦ -z`. -/
theorem aw_qd_frontier_lowerHalf : frontier (toExt lowerHalf) = toExt realLine ∪ {extInf} := by
  have himg : (Homeomorph.neg ℂ) '' upperHalf = lowerHalf := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : 0 < w.im := hw
      show (-w).im < 0
      rw [neg_im]
      linarith
    · intro hz
      have hz' : z.im < 0 := hz
      refine ⟨-z, ?_, neg_neg z⟩
      show 0 < (-z).im
      rw [neg_im]
      linarith
  have hR : (Homeomorph.neg ℂ) '' realLine = realLine := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w.im = 0 := hw
      show (-w).im = 0
      rw [neg_im, hw', neg_zero]
    · intro hz
      have hz' : z.im = 0 := hz
      refine ⟨-z, ?_, neg_neg z⟩
      show (-z).im = 0
      rw [neg_im, hz', neg_zero]
  rw [← himg, ← s13x_de_image_toExt (Homeomorph.neg ℂ) upperHalf,
    ← (Homeomorph.neg ℂ).onePointCongr.image_frontier, tp_c1_frontier_upperHalf, image_union,
    s13x_de_image_toExt, hR, image_singleton]
  rfl

/-- The boundary in `ℂ̄` of the image `e(𝕃)` of `𝕃` under a homeomorphism `e` of `ℂ` is `e(ℝ) ∪ {∞}`. -/
theorem aw_qd_frontier_image_lowerHalf (e : ℂ ≃ₜ ℂ) :
    frontier (toExt (e '' lowerHalf)) = toExt (e '' realLine) ∪ {extInf} := by
  rw [← s13x_de_image_toExt e lowerHalf, ← e.onePointCongr.image_frontier, aw_qd_frontier_lowerHalf, image_union,
    s13x_de_image_toExt, image_singleton]
  rfl

/-- **QD**: `D_p = f_μ(𝕃)` is a `K`-quasidisc for any `K` with `f_μ` `K`-q.c. (its boundary in `ℂ̄` is
`f_μ(ℝ) ∪ {∞}`, a `K`-quasicircle by `isKQuasicircle_image_realLine`; it is a Jordan domain as the homeomorphic image
of `𝕃`). -/
theorem aw_quasidisc (μ : BeltramiH) :
    ∃ K : ℝ, 1 ≤ K ∧ IsKQC (normalizedSolution μ.1) univ K ∧
      IsKQuasidisc (normalizedSolution μ.1 '' lowerHalf) K := by
  obtain ⟨⟨K, hK⟩, hs, -, -, -⟩ := ut_spec μ
  refine ⟨K, hK.2.1, hK, ?_⟩
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hfr : frontier (toExt (normalizedSolution μ.1 '' lowerHalf)) =
      toExt (normalizedSolution μ.1 '' realLine) ∪ {extInf} := by
    rw [← he]
    exact aw_qd_frontier_image_lowerHalf e
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← he]
    exact e.isOpenMap _ (isOpen_lt continuous_im continuous_const)
  · rw [← he]
    exact bA_isConnected_lowerHalf.image _ e.continuous.continuousOn
  · rw [hfr]
    exact tp_isJordanCurve_image_realLine hK hs
  · rw [hfr]
    exact isKQuasicircle_image_realLine hK hs

/-- **TR-P** (conformal invariance of the Poincaré density): for `f` conformal from an open `U` onto `V` and any
conformal `h : U → Δ`, `η_V(f z) |f'(z)| = η_U(z)` (`h ∘ f⁻¹` is a conformal map of `V` onto `Δ`, and
`(f⁻¹)'(f z) f'(z) = 1`). -/
theorem aw_tr_density_conformal {U V : Set ℂ} (hU : IsOpen U) {f h : ℂ → ℂ} (hf : IsConformalOnto f U V)
    (hh : IsConformalOnto h U unitDisc) {z : ℂ} (hz : z ∈ U) :
    poincareDensity V (f z) * ‖deriv f z‖ = poincareDensity U z := by
  have hV : IsOpen V := hf.isOpen hU
  have hχ : IsConformalOnto (Function.invFunOn f U) V U := hf.symm hU
  have hk : IsConformalOnto (h ∘ Function.invFunOn f U) V unitDisc := hh.comp hχ
  have hfz : f z ∈ V := hf.mapsTo hz
  have hleft : Function.invFunOn f U (f z) = z := hf.2.1.leftInvOn_invFunOn hz
  have hχd : DifferentiableAt ℂ (Function.invFunOn f U) (f z) := hf.differentiableAt_invFunOn hU hz
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (hU.mem_nhds hz)
  have hhd : DifferentiableAt ℂ h (Function.invFunOn f U (f z)) := by
    rw [hleft]
    exact hh.1.differentiableAt (hU.mem_nhds hz)
  have hinv : deriv (Function.invFunOn f U) (f z) * deriv f z = 1 := by
    have heq : Function.invFunOn f U ∘ f =ᶠ[𝓝 z] id := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hf.2.1.leftInvOn_invFunOn hw
    rw [← deriv_comp z hχd hfd, heq.deriv_eq, deriv_id]
  have hkd : deriv (h ∘ Function.invFunOn f U) (f z) =
      deriv h z * deriv (Function.invFunOn f U) (f z) := by
    rw [deriv_comp (f z) hhd hχd, hleft]
  have hn : ‖deriv (Function.invFunOn f U) (f z)‖ * ‖deriv f z‖ = 1 := by
    rw [← norm_mul, hinv, norm_one]
  rw [(poincareDensity_well_defined hV hk hk hfz).2, (poincareDensity_well_defined hU hh hh hz).2, hkd,
    Function.comp_apply, hleft, norm_mul]
  calc 2 * (‖deriv h z‖ * ‖deriv (Function.invFunOn f U) (f z)‖) / (1 - ‖h z‖ ^ 2) * ‖deriv f z‖
      = 2 * ‖deriv h z‖ * (‖deriv (Function.invFunOn f U) (f z)‖ * ‖deriv f z‖) / (1 - ‖h z‖ ^ 2) := by ring
    _ = 2 * ‖deriv h z‖ / (1 - ‖h z‖ ^ 2) := by rw [hn, mul_one]

/-- **TR-G** (transport for a conformal map of `𝕃`): for `f` conformal on `𝕃` and `φ` holomorphic on `𝕃`, the function
`ψ = ((φ - S_f) / f'²) ∘ f⁻¹` is holomorphic on `f(𝕃)`, satisfies `ψ(f z) f'(z)² = φ(z) - S_f(z)` on `𝕃`, and
`‖ψ‖_{f(𝕃)} = sup_{z ∈ 𝕃} |φ(z) - S_f(z)| (Im z)²` (`aw_tr_density_conformal`, `poincareDensity_lowerHalf`). -/
theorem aw_tr_transport_gen {f φ : ℂ → ℂ} (hconf : IsConformalOnto f lowerHalf (f '' lowerHalf))
    (hφ : DifferentiableOn ℂ φ lowerHalf) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (f '' lowerHalf) ∧
      (∀ z ∈ lowerHalf, ψ (f z) * deriv f z ^ 2 = φ z - schwarzian f z) ∧
      hyperbolicSupNorm ψ (f '' lowerHalf) =
        ⨆ z ∈ lowerHalf, ENNReal.ofReal (‖φ z - schwarzian f z‖ * z.im ^ 2) := by
  have hχ : IsConformalOnto (Function.invFunOn f lowerHalf) (f '' lowerHalf) lowerHalf :=
    hconf.symm isOpen_lowerHalf
  have hf' : ∀ z ∈ lowerHalf, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn isOpen_lowerHalf hconf.1 hconf.2.1 hz
  have hS : DifferentiableOn ℂ (schwarzian f) lowerHalf :=
    schwarzian_holomorphic isOpen_lowerHalf (isLocUnivMero_of_isConformalOnto isOpen_lowerHalf hconf)
  have hd : DifferentiableOn ℂ (deriv f) lowerHalf := hconf.1.deriv isOpen_lowerHalf
  have hg : DifferentiableOn ℂ (fun z => (φ z - schwarzian f z) / deriv f z ^ 2) lowerHalf :=
    (hφ.sub hS).div (hd.pow 2) fun z hz => pow_ne_zero 2 (hf' z hz)
  refine ⟨(fun z => (φ z - schwarzian f z) / deriv f z ^ 2) ∘ Function.invFunOn f lowerHalf,
    hg.comp hχ.1 hχ.mapsTo, fun z hz => ?_, ?_⟩
  · rw [Function.comp_apply, hconf.2.1.leftInvOn_invFunOn hz]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (hf' z hz))
  · have hh : IsConformalOnto (cayley ∘ fun w : ℂ => -w) lowerHalf unitDisc :=
      isConformalOnto_cayley.comp isConformalOnto_neg_lowerHalf
    unfold hyperbolicSupNorm
    rw [iSup_image]
    refine biSup_congr fun z hz => ?_
    have hη := aw_tr_density_conformal isOpen_lowerHalf hconf hh hz
    rw [poincareDensity_lowerHalf hz] at hη
    have hfz : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.2 (hf' z hz)
    have him : |z.im| ≠ 0 := abs_ne_zero.2 (ne_of_lt hz)
    have hη' : poincareDensity (f '' lowerHalf) (f z) = 1 / |z.im| / ‖deriv f z‖ := by
      rw [← hη, mul_div_cancel_right₀ _ hfz]
    rw [Function.comp_apply, hconf.2.1.leftInvOn_invFunOn hz, hη', norm_div, norm_pow]
    congr 1
    field_simp
    rw [sq_abs]

/-- **TR** (transport): for `φ ∈ A(𝕃)` there is `ψ` holomorphic on `D_p = f_μ(𝕃)` with
`ψ(f z) f'(z)² = φ(z) - S_f(z)` on `𝕃`, and `‖ψ‖_{D_p} = ‖φ - Ψ[μ]‖_𝕃` (conformal invariance of the Poincaré density:
`η_{D_p}(f z) |f'(z)| = η_𝕃(z) = 1/|Im z|`). -/
theorem aw_transport (μ : BeltramiH) {φ : ℂ → ℂ} (hφ : φ ∈ bersSpaceL) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (normalizedSolution μ.1 '' lowerHalf) ∧
      (∀ z ∈ lowerHalf, ψ (normalizedSolution μ.1 z) * deriv (normalizedSolution μ.1) z ^ 2 =
        φ z - schwarzian (normalizedSolution μ.1) z) ∧
      hyperbolicSupNorm ψ (normalizedSolution μ.1 '' lowerHalf) = bersNormL (φ - bersFunction μ.1) := by
  obtain ⟨ψ, hψd, hψ, hψn⟩ := aw_tr_transport_gen (ut_conformal_lowerHalf μ) hφ.1
  refine ⟨ψ, hψd, hψ, ?_⟩
  rw [hψn]
  unfold bersNormL
  refine biSup_congr fun z hz => ?_
  rw [Pi.sub_apply, bersFunction, indicator_of_mem hz]

/-- **EXT-val**: at a point where `g` is analytic, a finite value `G v = M(ĝ v)` (`M = mobiusExt α β κ δ`) lies off
the pole of `M`, and `G v = (α g v + β)/(κ g v + δ)`. -/
theorem aw_ext_val {g G : ℂ → ℂ} {α β κ δ v : ℂ}
    (hG : mobiusExt α β κ δ (meroToExt g v) = ((G v : ℂ) : ExtPlane)) (hA : AnalyticAt ℂ g v) :
    κ * g v + δ ≠ 0 ∧ G v = (α * g v + β) / (κ * g v + δ) := by
  rw [t203_univ_meroToExt_of_analyticAt hA] at hG
  have hden : κ * g v + δ ≠ 0 := by
    intro h0
    rw [mobiusExt_coe_of_eq_zero h0] at hG
    exact OnePoint.coe_ne_infty _ hG.symm
  refine ⟨hden, ?_⟩
  rw [mobiusExt_coe hden] at hG
  exact (OnePoint.coe_injective hG).symm

/-- **EXT-germ**: if `M(meroToExt g v) = G v` (finite) on the open set `D` where `g` is meromorphic, then on a
punctured neighbourhood of each `w ∈ D` the map `G` is the Möbius map `M` of `g`, off its pole. -/
theorem aw_ext_germ {g G : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hg : IsLocUnivMero g D) {α β κ δ : ℂ}
    (hG : ∀ v ∈ D, mobiusExt α β κ δ (meroToExt g v) = ((G v : ℂ) : ExtPlane)) {w : ℂ} (hw : w ∈ D) :
    ∀ᶠ v in 𝓝[≠] w, κ * g v + δ ≠ 0 ∧ G v = (α * g v + β) / (κ * g v + δ) := by
  filter_upwards [(hg.1 w hw).eventually_analyticAt, nhdsWithin_le_nhds (hD.mem_nhds hw)] with v hA hv
  exact aw_ext_val (hG v hv) hA

/-- **EXT-analytic**: under the hypotheses of `aw_ext_germ`, `G` is analytic at every point of `D`: near a point of
analyticity of `g` it is `(α g + β)/(κ g + δ)`; near a pole it is `(β u + α)/(δ u + κ)` for `u = 1/g` in normal
form (`u = 0` at the pole, and `κ ≠ 0` because `G` is finite there). -/
theorem aw_ext_analyticAt {g G : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hg : IsLocUnivMero g D) {α β κ δ : ℂ}
    (hG : ∀ v ∈ D, mobiusExt α β κ δ (meroToExt g v) = ((G v : ℂ) : ExtPlane)) {w : ℂ} (hw : w ∈ D) :
    AnalyticAt ℂ G w := by
  rcases hg.2 w hw with ⟨hA, -⟩ | ⟨hord, hu, hu'⟩
  · have hden := (aw_ext_val (hG w hw) hA).1
    have hM : AnalyticAt ℂ (fun v => (α * g v + β) / (κ * g v + δ)) w :=
      (by fun_prop : AnalyticAt ℂ (fun v => α * g v + β) w).div
        (by fun_prop : AnalyticAt ℂ (fun v => κ * g v + δ) w) hden
    refine hM.congr ?_
    filter_upwards [hA.eventually_analyticAt, hD.mem_nhds hw] with v hAv hv
    exact (aw_ext_val (hG v hv) hAv).2.symm
  · set u : ℂ → ℂ := fun v => (toMeromorphicNFAt g w v)⁻¹ with hudef
    have hmero : MeromorphicAt g w := hg.1 w hw
    have hfu : g =ᶠ[𝓝[≠] w] fun v => (u v)⁻¹ := by
      filter_upwards [hmero.eq_nhdsNE_toMeromorphicNFAt] with v hv
      simp only [hudef, inv_inv]
      exact hv
    have hune : ∀ᶠ v in 𝓝[≠] w, u v ≠ 0 := by
      refine hu.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => hu' ?_
      have hz0 : u =ᶠ[𝓝 w] fun _ => (0 : ℂ) := hcon
      rw [hz0.deriv_eq, deriv_const]
    have hu0 : u w = 0 := by
      rcases meromorphicNFAt_iff_analyticAt_or.1 (meromorphicNFAt_toMeromorphicNFAt (f := g) (x := w)) with
        hA | ⟨-, -, h0⟩
      · have h1 := hA.meromorphicOrderAt_nonneg
        rw [hmero.meromorphicOrderAt_toMeromorphicNFAt] at h1
        exact absurd hord (not_lt.2 h1)
      · simp only [hudef, h0, inv_zero]
    have hGw := hG w hw
    rw [t203_univ_meroToExt_of_order_neg hord] at hGw
    have hκ : κ ≠ 0 := by
      intro h0
      rw [mobiusExt_infty_of_eq h0] at hGw
      exact OnePoint.coe_ne_infty _ hGw.symm
    rw [mobiusExt_infty_of_ne hκ] at hGw
    have hGw' : G w = α / κ := (OnePoint.coe_injective hGw).symm
    have hM : AnalyticAt ℂ (fun v => (β * u v + α) / (δ * u v + κ)) w :=
      (by fun_prop : AnalyticAt ℂ (fun v => β * u v + α) w).div
        (by fun_prop : AnalyticAt ℂ (fun v => δ * u v + κ) w) (by rw [hu0, mul_zero, zero_add]; exact hκ)
    refine hM.congr ?_
    have hP : ∀ᶠ v in 𝓝[≠] w, (β * u v + α) / (δ * u v + κ) = G v := by
      filter_upwards [aw_ext_germ hD hg hG hw, hfu, hune] with v hv hgv huv
      obtain ⟨hden, hGv⟩ := hv
      rw [hGv, hgv]
      rw [hgv] at hden
      have hden2 : δ * u v + κ ≠ 0 := by
        have e : δ * u v + κ = u v * (κ * (u v)⁻¹ + δ) := by field_simp; ring
        rw [e]
        exact mul_ne_zero huv hden
      rw [div_eq_div_iff hden2 hden]
      field_simp
      ring
    rw [eventually_nhdsWithin_iff] at hP
    filter_upwards [hP] with v hv
    by_cases hvw : v = w
    · rw [hvw, hu0, hGw', mul_zero, zero_add, mul_zero, zero_add]
    · exact hv hvw

/-- **EXT-Schwarzian**: under the hypotheses of `aw_ext_germ` (and `M` non-degenerate), `S_G = S_g` on `D`
(`schwarzian_congr` on the punctured germ, then Möbius invariance `schwarzian_mobius_comp`). -/
theorem aw_ext_schwarzian {g G : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hg : IsLocUnivMero g D) {α β κ δ : ℂ}
    (hdet : α * δ - β * κ ≠ 0)
    (hG : ∀ v ∈ D, mobiusExt α β κ δ (meroToExt g v) = ((G v : ℂ) : ExtPlane)) {w : ℂ} (hw : w ∈ D) :
    schwarzian G w = schwarzian g w := by
  rw [schwarzian_congr ((aw_ext_germ hD hg hG hw).mono fun v hv => hv.2)]
  exact schwarzian_mobius_comp hg hdet hw

/-- **EXT-affine**: the affine normalization `w ↦ (w - p)/q` (`q ≠ 0`) maps `ℂ` conformally onto `ℂ`. -/
theorem aw_ext_affine_conformal {p q : ℂ} (hq : q ≠ 0) :
    IsConformalOnto (fun w : ℂ => (1 * w + -p) / (0 * w + q)) univ univ := by
  have hden : ∀ w : ℂ, (0 : ℂ) * w + q ≠ 0 := fun w => by simpa using hq
  refine ⟨fun w _ => ?_, fun x _ y _ hxy => ?_, eq_univ_of_forall fun w => ⟨w * q + p, mem_univ _, ?_⟩⟩
  · exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 * w + -p) w).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 0 * w + q) w) (hden w)).differentiableWithinAt
  · have h := hxy
    simp only [zero_mul, zero_add] at h
    rw [div_left_inj' hq] at h
    linear_combination h
  · show (1 * (w * q + p) + -p) / (0 * (w * q + p) + q) = w
    rw [div_eq_iff (hden _)]
    ring

/-- **EXT** (the normalized extension): a univalent `g` on `D_p` with a `K'`-q.c. extension `G` (`HasQCExtensionExt`) and
`S_g(f z) f'(z)² = φ(z) - S_f(z)` on `𝕃` gives a normalized q.c. map `H = M ∘ G ∘ f̂` of the plane (a Möbius `M` sends
`G(f̂ ∞), G(f 0), G(f 1)` to `∞, 0, 1`): holomorphic on `𝕃` with `S_H = φ` there (chain rule, Möbius invariance; `M`
moves the pole of `g` to a finite point), and `H ∘ f⁻¹ = M ∘ G` is `K'`-q.c. on `f(ℍ)`. -/
theorem aw_extend (μ : BeltramiH) {K' : ℝ} {g φ : ℂ → ℂ} (hg : IsUnivMero g (normalizedSolution μ.1 '' lowerHalf))
    (hext : HasQCExtensionExt g (normalizedSolution μ.1 '' lowerHalf) K')
    (hS : ∀ z ∈ lowerHalf, schwarzian g (normalizedSolution μ.1 z) * deriv (normalizedSolution μ.1) z ^ 2 =
      φ z - schwarzian (normalizedSolution μ.1) z) :
    ∃ (H : ℂ → ℂ) (K₂ : ℝ), IsKQC H univ K₂ ∧ H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧
      DifferentiableOn ℂ H lowerHalf ∧ (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      IsKQC (H ∘ Function.invFunOn (normalizedSolution μ.1) univ) (normalizedSolution μ.1 '' upperHalf) K' := by
  obtain ⟨F, hFD, M₀, ⟨α, β, κ, δ, hdet, rfl⟩, g₀, hg₀, hg₀s, hM⟩ := hext
  obtain ⟨⟨Kf, hf⟩, hfs, hf0, hf1, -⟩ := ut_spec μ
  have hconf := ut_conformal_lowerHalf μ
  set f := normalizedSolution μ.1
  obtain ⟨ef, hef⟩ := t203_pack_homeo hf hfs
  have hDo : IsOpen (f '' lowerHalf) := by
    rw [← hef]
    exact ef.isOpenMap _ isOpen_lowerHalf
  have hUo : IsOpen (f '' upperHalf) := by
    rw [← hef]
    exact ef.isOpenMap _ isOpen_upperHalf
  have hG : ∀ v ∈ f '' lowerHalf, mobiusExt α β κ δ (meroToExt g v) = ((g₀ v : ℂ) : ExtPlane) := by
    intro v hv
    rw [← hFD v hv]
    exact hM v
  obtain ⟨e₀, he₀⟩ := t203_pack_homeo hg₀ hg₀s
  have hg₀i : Function.Injective g₀ := by
    rw [← he₀]
    exact e₀.injective
  have hq : g₀ 1 - g₀ 0 ≠ 0 := sub_ne_zero.2 fun h => one_ne_zero (hg₀i h)
  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun w => (1 * w + -g₀ 0) / (0 * w + (g₀ 1 - g₀ 0)) := ⟨_, rfl⟩
  have hAc : IsConformalOnto A univ univ := by
    rw [hA]
    exact aw_ext_affine_conformal hq
  have hAg : IsKQC (A ∘ g₀) univ K' := by
    simpa using thm7_1_comp hg₀ (isKQC_one_of_conformal isOpen_univ hAc) (subset_univ _)
  have hAgi : Function.Injective (A ∘ g₀) := (injOn_univ.1 hAc.2.1).comp hg₀i
  have hg₀a : ∀ w ∈ f '' lowerHalf, AnalyticAt ℂ g₀ w := fun w hw => aw_ext_analyticAt hDo hg.1 hG hw
  have hAa : ∀ w, AnalyticAt ℂ A w := fun w => by
    rw [hA]
    exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 * w + -g₀ 0) w).div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 0 * w + (g₀ 1 - g₀ 0)) w) (by simpa using hq)
  have hAga : ∀ w ∈ f '' lowerHalf, AnalyticAt ℂ (A ∘ g₀) w := fun w hw => (hAa (g₀ w)).comp (hg₀a w hw)
  refine ⟨(A ∘ g₀) ∘ f, Kf * K', thm7_1_comp hf hAg (subset_univ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_comp, hfs, image_comp, hg₀s, hAc.2.2]
  · show A (g₀ (f 0)) = 0
    rw [hf0, hA]
    simp
  · show A (g₀ (f 1)) = 1
    rw [hf1, hA]
    show (1 * g₀ 1 + -g₀ 0) / (0 * g₀ 1 + (g₀ 1 - g₀ 0)) = 1
    rw [div_eq_one_iff_eq (by simpa using hq)]
    ring
  · intro z hz
    exact ((hAga (f z) (mem_image_of_mem f hz)).differentiableAt.comp z
      (hconf.1.differentiableAt (isOpen_lowerHalf.mem_nhds hz))).differentiableWithinAt
  · intro z hz
    have hwD : f z ∈ f '' lowerHalf := mem_image_of_mem f hz
    have hfa : AnalyticAt ℂ f z := hconf.1.analyticAt (isOpen_lowerHalf.mem_nhds hz)
    have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_lowerHalf hconf.1 hconf.2.1 hz
    have hG' : deriv (A ∘ g₀) (f z) ≠ 0 :=
      deriv_ne_zero_of_injOn hDo (fun w hw => (hAga w hw).differentiableAt.differentiableWithinAt)
        hAgi.injOn hwD
    have hg₀' : deriv g₀ (f z) ≠ 0 :=
      deriv_ne_zero_of_injOn hDo (fun w hw => (hg₀a w hw).differentiableAt.differentiableWithinAt)
        hg₀i.injOn hwD
    have hS1 : schwarzian (A ∘ g₀) (f z) = schwarzian g₀ (f z) := by
      have e : A ∘ g₀ = fun w => (1 * g₀ w + -g₀ 0) / (0 * g₀ w + (g₀ 1 - g₀ 0)) := by
        rw [hA]
        rfl
      rw [e]
      exact schwarzian_mobius_comp_analytic (hg₀a _ hwD) hg₀' (by simpa using hq)
    rw [eq19_1_chain_rule hfa hf' (hAga _ hwD) hG', hS1, aw_ext_schwarzian hDo hg.1 hdet hG hwD, hS z hz]
    ring
  · have hcomp : ((A ∘ g₀) ∘ f) ∘ Function.invFunOn f univ = A ∘ g₀ := by
      funext w
      have hw : w ∈ f '' univ := by
        rw [hfs]
        exact mem_univ w
      show (A ∘ g₀) (f (Function.invFunOn f univ w)) = (A ∘ g₀) w
      rw [Function.invFunOn_eq hw]
    rw [hcomp]
    exact ac_t_isKQC_restrict hAg hUo (subset_univ _)

/-- **NU** helper: for a map `H` holomorphic on the lower half-plane, the cut-off of its complex dilatation to `ℍ`
agrees a.e. with its complex dilatation (on the open set `𝕃` both vanish, since `∂_{z̄} H = 0` there by the
Cauchy–Riemann equations, and `ℝ` is null). -/
theorem aw_nu_indicator_ae_eq {H : ℂ → ℂ} (hHd : DifferentiableOn ℂ H lowerHalf) :
    ∀ᵐ z, upperHalf.indicator (complexDilatation H) z = complexDilatation H z := by
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  filter_upwards [hnull] with z h2
  rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
  · have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
    have hdiff : DifferentiableAt ℂ H z := hHd.differentiableAt (hLo.mem_nhds hlt)
    have hbar : dzbar H z = 0 := (cauchyRiemann_iff.1 hdiff).2
    have hnu : z ∉ upperHalf := fun hu => absurd hlt (not_lt.2 (le_of_lt hu))
    rw [Set.indicator_of_notMem hnu, complexDilatation, hbar, zero_div]
  · exact Set.indicator_of_mem (show z ∈ upperHalf from hgt) _

/-- **NU** (the coefficient `ν'`): a normalized q.c. map `H` of the plane, holomorphic on `𝕃` with `S_H = φ` there, is
`f_{ν'}` for `ν' = 1_ℍ μ_H ∈ M` (`thm13_5_uniqueness_plane`, the `ut_transport` pattern), so `Ψ[ν'] = φ` on `𝕃`; and if
`H ∘ f_μ⁻¹` is `K'`-q.c. on `f_μ(ℍ)`, then `ut_v μ ν' ≤ log K'` (`isKQC_maxDilatation_le`). -/
theorem aw_nu (μ : BeltramiH) {φ H : ℂ → ℂ} {K₂ K' : ℝ} (hH : IsKQC H univ K₂) (hHs : H '' univ = univ)
    (hH0 : H 0 = 0) (hH1 : H 1 = 1) (hHd : DifferentiableOn ℂ H lowerHalf)
    (hHS : ∀ z ∈ lowerHalf, schwarzian H z = φ z)
    (hK' : IsKQC (H ∘ Function.invFunOn (normalizedSolution μ.1) univ) (normalizedSolution μ.1 '' upperHalf) K') :
    ∃ ν' : BeltramiH, (∀ z ∈ lowerHalf, schwarzian (normalizedSolution ν'.1) z = φ z) ∧ ut_v μ ν' ≤ Real.log K' := by
  have hnorm : normalizedSolution (upperHalf.indicator (complexDilatation H)) = H := by
    obtain ⟨hq, hs, hq0, hq1, hd⟩ := ut_spec ⟨upperHalf.indicator (complexDilatation H), ut_rg_indicator_mem hH⟩
    refine thm13_5_uniqueness_plane hq ⟨K₂, hH⟩ hs hHs ?_ hq0 hq1 hH0 hH1
    filter_upwards [hd, aw_nu_indicator_ae_eq hHd] with z h1 h2
    exact h1.trans h2
  refine ⟨⟨upperHalf.indicator (complexDilatation H), ut_rg_indicator_mem hH⟩, fun z hz => ?_, ?_⟩
  · show schwarzian (normalizedSolution (upperHalf.indicator (complexDilatation H))) z = φ z
    rw [hnorm]
    exact hHS z hz
  · show Real.log (maxDilatation (normalizedSolution (upperHalf.indicator (complexDilatation H)) ∘
      Function.invFunOn (normalizedSolution μ.1) univ) (normalizedSolution μ.1 '' upperHalf)).toReal ≤ Real.log K'
    rw [hnorm]
    have hK1 : (1 : ℝ) ≤ K' := hK'.2.1
    have hle := (isKQC_maxDilatation_le hK').1
    have hne : (normalizedSolution μ.1 '' upperHalf).Nonempty :=
      ⟨normalizedSolution μ.1 I, mem_image_of_mem _ (show (0 : ℝ) < I.im by simp)⟩
    have hge := UniversalTeichmuller.ut_md_one_le hK' hne
    have hup : (maxDilatation (H ∘ Function.invFunOn (normalizedSolution μ.1) univ)
        (normalizedSolution μ.1 '' upperHalf)).toReal ≤ K' :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hle
    have hlo : (1 : ℝ) ≤ (maxDilatation (H ∘ Function.invFunOn (normalizedSolution μ.1) univ)
        (normalizedSolution μ.1 '' upperHalf)).toReal := by
      have h := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle) hge
      rwa [ENNReal.toReal_one] at h
    exact Real.log_le_log (by linarith) hup

/-- **AW** (the Ahlfors–Weill core): for `p ∈ T` there is `c > 0` such that every `φ ∈ A(𝕃)` with
`‖φ - Ψp‖ ≤ s < 1/c` is `Ψ[ν']` on `𝕃` for some `ν'` with `ut_v μ ν' ≤ log((1 + cs)/(1 - cs))`, `μ = p.out`
(QD, `thm20_3_ahlfors` for `D_p`, TR, `thm19_1_exists`, EXT, NU). -/
theorem aw_core (p : UniversalTeichmuller) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ ∈ bersSpaceL, ∀ s : ℝ, 0 ≤ s → bersNormL (φ - bersMapU p) ≤ ENNReal.ofReal s → s < 1 / c →
      ∃ ν' : BeltramiH, (∀ z ∈ lowerHalf, schwarzian (normalizedSolution ν'.1) z = φ z) ∧
        ut_v p.out ν' ≤ Real.log ((1 + c * s) / (1 - c * s)) := by
  obtain ⟨K, hK1, -, hQD⟩ := aw_quasidisc p.out
  obtain ⟨c, hc, hcD⟩ := thm20_3_ahlfors hK1
  refine ⟨c, hc, fun φ hφ s hs0 hsN hs1 => ?_⟩
  obtain ⟨hSD, hext⟩ := hcD _ hQD
  obtain ⟨ψ, hψd, hψid, hψN⟩ := aw_transport p.out hφ
  obtain ⟨hDo, hDc, hDs, -⟩ := t203_hsc_of_isKQuasidisc hQD
  obtain ⟨g, hgl, hgS⟩ := thm19_1_exists hDo hDc hDs hψd
  have hgN : schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf) =
      hyperbolicSupNorm ψ (normalizedSolution p.out.1 '' lowerHalf) := by
    unfold schwarzianNorm hyperbolicSupNorm
    refine biSup_congr fun z hz => ?_
    rw [hgS z hz]
  have hgs : schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf) ≤ ENNReal.ofReal s := by
    rw [hgN, hψN]
    exact hsN
  have hc1 : c * s < 1 := by
    rw [lt_div_iff₀ hc] at hs1
    linarith
  have hgs' : schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf) < ENNReal.ofReal (1 / c) :=
    lt_of_le_of_lt hgs ((ENNReal.ofReal_lt_ofReal_iff (one_div_pos.2 hc)).2 hs1)
  have hgU := hSD.2.2 g hgl hgs'
  have hgE := hext g hgl hgs'
  have hS : ∀ z ∈ lowerHalf, schwarzian g (normalizedSolution p.out.1 z) *
      deriv (normalizedSolution p.out.1) z ^ 2 = φ z - schwarzian (normalizedSolution p.out.1) z := by
    intro z hz
    rw [hgS _ (mem_image_of_mem _ hz)]
    exact hψid z hz
  obtain ⟨H, K₂, hH, hHs, hH0, hH1, hHd, hHS, hK'⟩ := aw_extend p.out hgU hgE hS
  obtain ⟨ν', hν'S, hν'v⟩ := aw_nu p.out hH hHs hH0 hH1 hHd hHS hK'
  refine ⟨ν', hν'S, hν'v.trans ?_⟩
  have ht0 : 0 ≤ (schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf)).toReal := ENNReal.toReal_nonneg
  have hts : (schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf)).toReal ≤ s :=
    ENNReal.toReal_le_of_le_ofReal hs0 hgs
  have hct : c * (schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf)).toReal ≤ c * s :=
    mul_le_mul_of_nonneg_left hts hc.le
  have hct0 : 0 ≤ c * (schwarzianNorm g (normalizedSolution p.out.1 '' lowerHalf)).toReal :=
    mul_nonneg hc.le ht0
  apply Real.log_le_log
  · exact div_pos (by linarith) (by linarith)
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- For `ε > 0` there is `t ∈ (0, 1)` with `log((1 + t)/(1 - t)) < ε`. -/
theorem aw_t_log_small {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ Real.log ((1 + t) / (1 - t)) < ε := by
  have he : 1 < Real.exp ε := Real.one_lt_exp_iff.2 hε
  have hden : 0 < Real.exp ε + 1 := by linarith
  have ha0 : 0 < (Real.exp ε - 1) / (Real.exp ε + 1) := div_pos (by linarith) hden
  refine ⟨min (1 / 2) ((Real.exp ε - 1) / (Real.exp ε + 1) / 2), lt_min (by norm_num) (by linarith),
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
  have hta : min (1 / 2) ((Real.exp ε - 1) / (Real.exp ε + 1) / 2) < (Real.exp ε - 1) / (Real.exp ε + 1) :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ht1 : min (1 / 2) ((Real.exp ε - 1) / (Real.exp ε + 1) / 2) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht0 : 0 < min (1 / 2) ((Real.exp ε - 1) / (Real.exp ε + 1) / 2) := lt_min (by norm_num) (by linarith)
  generalize min (1 / 2) ((Real.exp ε - 1) / (Real.exp ε + 1) / 2) = t at hta ht1 ht0
  have h1t : 0 < 1 - t := by linarith
  have hta' : t * (Real.exp ε + 1) < Real.exp ε - 1 := (lt_div_iff₀ hden).1 hta
  have hlt : (1 + t) / (1 - t) < Real.exp ε := by
    rw [div_lt_iff₀ h1t]
    nlinarith
  calc Real.log ((1 + t) / (1 - t)) < Real.log (Real.exp ε) :=
        Real.log_lt_log (div_pos (by linarith) h1t) hlt
    _ = ε := Real.log_exp ε

/-- `s ↦ log((1 + s)/(1 - s))` is monotone on `[0, 1)`. -/
theorem aw_t_log_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    Real.log ((1 + s) / (1 - s)) ≤ Real.log ((1 + t) / (1 - t)) := by
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  apply Real.log_le_log (div_pos (by linarith) h1s)
  rw [div_le_div_iff₀ h1s h1t]
  nlinarith

/-- `Ψ[ν] = S_{f_ν}|𝕃`: the Bers map at the class of `ν` is computed on `ν` itself. -/
theorem aw_t_bersMapU_mk (ν : BeltramiH) :
    bersMapU (Quotient.mk teichSetoid ν) = bersFunction ν.1 := by
  exact bersFunction_eq_of_equiv (Quotient.exact (Quotient.out_eq (Quotient.mk teichSetoid ν)))

/-- **Theorem 21.2** (continuity of the inverse). -/
theorem thm21_2_inverse_continuous (p : UniversalTeichmuller) :
    ∀ ε > 0, ∃ δ > 0, ∀ q : UniversalTeichmuller,
      bersNormL (bersMapU q - bersMapU p) < ENNReal.ofReal δ → UniversalTeichmuller.dist p q < ε := by
  obtain ⟨c, hc, hcore⟩ := aw_core p
  intro ε hε
  obtain ⟨t, ht0, ht1, htε⟩ := aw_t_log_small hε
  refine ⟨t / c, div_pos ht0 hc, ?_⟩
  intro q hlt
  have hne : bersNormL (bersMapU q - bersMapU p) ≠ ⊤ := ne_top_of_lt hlt
  have hs0 : 0 ≤ (bersNormL (bersMapU q - bersMapU p)).toReal := ENNReal.toReal_nonneg
  have hsδ : (bersNormL (bersMapU q - bersMapU p)).toReal < t / c := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hcs : c * (bersNormL (bersMapU q - bersMapU p)).toReal < t := by
    rw [lt_div_iff₀ hc] at hsδ
    linarith
  have hsc : (bersNormL (bersMapU q - bersMapU p)).toReal < 1 / c := by
    rw [lt_div_iff₀ hc]
    linarith
  obtain ⟨ν', hν'S, hν'v⟩ := hcore (bersMapU q) (bersMapU_mem q).1 _ hs0 (ENNReal.ofReal_toReal hne).ge hsc
  have hq : Quotient.mk teichSetoid ν' = q := by
    apply thm21_2_injective
    rw [aw_t_bersMapU_mk]
    funext z
    by_cases hz : z ∈ lowerHalf
    · rw [bersFunction, indicator_of_mem hz, hν'S z hz]
    · rw [bersFunction, indicator_of_notMem hz, bersMapU, bersFunction, indicator_of_notMem hz]
  calc UniversalTeichmuller.dist p q ≤ ut_v p.out ν' := UniversalTeichmuller.ut_dist_le (Quotient.out_eq p) hq
    _ ≤ _ := hν'v
    _ ≤ Real.log ((1 + t) / (1 - t)) := aw_t_log_mono (mul_nonneg hc.le hs0) hcs.le ht1
    _ < ε := htε

/-- **Theorem 21.3**: `Ψ(T)` is open in `A(𝕃)`. -/
theorem thm21_3_open (p : UniversalTeichmuller) :
    ∃ ε > 0, ∀ φ ∈ bersSpaceL, bersNormL (φ - bersMapU p) < ENNReal.ofReal ε →
      ∃ q : UniversalTeichmuller, EqOn (bersMapU q) φ lowerHalf := by
  obtain ⟨c, hc, hcore⟩ := aw_core p
  refine ⟨1 / c, one_div_pos.2 hc, ?_⟩
  intro φ hφ hlt
  have hne : bersNormL (φ - bersMapU p) ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨ν', hν'S, -⟩ := hcore φ hφ _ ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hne).ge
    (ENNReal.toReal_lt_of_lt_ofReal hlt)
  refine ⟨Quotient.mk teichSetoid ν', ?_⟩
  intro z hz
  rw [aw_t_bersMapU_mk, bersFunction, indicator_of_mem hz]
  exact hν'S z hz

/-- The set `𝓕*` of Schwarzian derivatives (on `𝕃`) of univalent meromorphic functions in `𝕃`. -/
def schwarzianUnivalentSet : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, IsUnivMero f lowerHalf ∧ φ = lowerHalf.indicator (schwarzian f)}

/-- An interior point of a subset `S` of `A(𝕃)` (for the norm of `A(𝕃)`). -/
def IsBersInteriorPoint (S : Set (ℂ → ℂ)) (φ : ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ ψ ∈ bersSpaceL, bersNormL (ψ - φ) < ENNReal.ofReal ε → lowerHalf.indicator ψ ∈ S

/-- **Theorem 21.4** (Gehring): `T* = Ψ(T)` is the interior of `𝓕*` in `A(𝕃)`.

The condition `φ ∈ bersSpaceL` is part of "interior point of `𝓕*` in `A(𝕃)`": without it an
infinite-norm `φ` is vacuously interior (`‖ψ - φ‖ = ∞` for every `ψ ∈ A(𝕃)`), and so is a
non-holomorphic `φ` close to `0` (corrected 2026-09-25). -/
theorem thm21_4_gehring :
    {φ | φ ∈ bersSpaceL ∧ IsBersInteriorPoint schwarzianUnivalentSet φ ∧ φ = lowerHalf.indicator φ} =
      range bersMapU := by
  sorry

/-- Gehring's answer to Bers' question: the closure of `T*` is strictly smaller than `𝓕*`. -/
theorem gehring_closure_ne :
    ∃ φ ∈ schwarzianUnivalentSet, ∃ ε > 0, ∀ p : UniversalTeichmuller,
      ENNReal.ofReal ε ≤ bersNormL (φ - bersMapU p) := by
  sorry

/-- Thurston: `𝓕*` has isolated points (in particular it is not connected). -/
theorem thurston_isolated_points :
    ∃ φ ∈ schwarzianUnivalentSet, ∃ ε > 0, ∀ ψ ∈ schwarzianUnivalentSet,
      bersNormL (ψ - φ) < ENNReal.ofReal ε → ψ = φ := by
  sorry

end LiZhongQC
