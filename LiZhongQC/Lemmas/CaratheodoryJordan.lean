import LiZhongQC.ClusterSets
import LiZhongQC.Lemmas.JordanBridge

/-!
# Carathéodory's theorem: a conformal map onto a Jordan domain extends to a homeomorphism

The full chain of results (`C1`–`C10`) leading to Carathéodory's theorem
(`caratheodory_jordan_clean`): a conformal bijection `unitDisc → Ω` with `Ω` bounded and
`IsJordanCurve (frontier (toExt Ω))` extends to a homeomorphism of the closed disc onto
`closure Ω`, transported to `ExtPlane` via `IsHomeoExtension`.

Along the way:
* `isJordanCurve_of_loop`: a path on `[0,1]` continuous on the closed interval, injective on
  the half-open interval, and returning to its start traces a Jordan curve. Shared by
  `isSimpleClosedCurve_union_of_arcEndC` (gluing two arcs at both shared endpoints) and by
  `isJordanCurve_image_chord` (`C4`, gluing a chord's two endpoint images) instead of each
  independently re-deriving the `AddCircle.liftIco`/`homeomorphCircle` gluing machinery;
* the crosscut/loop splitting lemmas `S1`–`S4` and the arc-splitting lemma `C6`;
* the boundary cluster-set and continuous-extension results `C1`–`C3`, `C7`, `C8`;
* the chord-meets-frontier and injectivity-of-the-extension results `C5`, `C9`;
* `C10` (`caratheodory_jordan_clean`), assembling `C8` (existence of the continuous extension)
  with `C9` (its injectivity) via `OnePoint.map`.
-/

open Complex Set Metric Filter Topology MeasureTheory JordanCurveTheorem
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace LiZhongQC

def IsArcEndC (A : Set ℂ) (v w : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, A = γ '' Icc 0 1 ∧ ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = v ∧ γ 1 = w

/-- A path on `[0,1]` continuous on the closed interval, injective on the half-open interval,
and returning to its start (`F 0 = F 1`), traces a Jordan curve. Shared by
`isSimpleClosedCurve_union_of_arcEndC` (two arcs glued at both shared endpoints) and by
`isJordanCurve_image_chord` (C4). -/
theorem isJordanCurve_of_loop {F : ℝ → ℂ} (hcont : ContinuousOn F (Icc (0 : ℝ) 1))
    (hinj : InjOn F (Ico (0 : ℝ) 1)) (hF01 : F 0 = F 1) :
    IsJordanCurve (toExt (F '' Icc (0 : ℝ) 1)) := by
  have hT : (1 : ℝ) ≠ 0 := one_ne_zero
  have hcirc : Continuous (AddCircle.liftIco (1 : ℝ) 0 F) :=
    AddCircle.liftIco_zero_continuous hF01 hcont
  have hcircinj : Function.Injective (AddCircle.liftIco (1 : ℝ) 0 F) := by
    intro u v huv
    have hu' : ((AddCircle.equivIco (1 : ℝ) 0 u : AddCircle (1 : ℝ))) = u := AddCircle.coe_equivIco
    have hv' : ((AddCircle.equivIco (1 : ℝ) 0 v : AddCircle (1 : ℝ))) = v := AddCircle.coe_equivIco
    rw [← hu', ← hv'] at huv ⊢
    rw [AddCircle.liftIco_coe_apply (AddCircle.equivIco (1 : ℝ) 0 u).coe_prop,
      AddCircle.liftIco_coe_apply (AddCircle.equivIco (1 : ℝ) 0 v).coe_prop] at huv
    have hmu := (AddCircle.equivIco (1 : ℝ) 0 u).coe_prop
    have hmv := (AddCircle.equivIco (1 : ℝ) 0 v).coe_prop
    have hmu' : ((AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) ∈ Ico (0 : ℝ) 1 := ⟨hmu.1, by linarith [hmu.2]⟩
    have hmv' : ((AddCircle.equivIco (1 : ℝ) 0 v : ℝ)) ∈ Ico (0 : ℝ) 1 := ⟨hmv.1, by linarith [hmv.2]⟩
    have := hinj hmu' hmv' huv
    rw [Subtype.ext this]
  have hrange : range (AddCircle.liftIco (1 : ℝ) 0 F) = F '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      have hmemIco := (AddCircle.equivIco (1 : ℝ) 0 u).coe_prop
      have hu' : ((AddCircle.equivIco (1 : ℝ) 0 u : AddCircle (1 : ℝ))) = u := AddCircle.coe_equivIco
      rw [← hu', AddCircle.liftIco_coe_apply hmemIco]
      exact ⟨(AddCircle.equivIco (1 : ℝ) 0 u : ℝ), ⟨hmemIco.1, by linarith [hmemIco.2]⟩, rfl⟩
    · rintro w ⟨s, hs, rfl⟩
      rcases eq_or_lt_of_le hs.2 with hs1 | hs1
      · refine ⟨((0 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
        rw [AddCircle.liftIco_coe_apply (a := (0 : ℝ)) (by norm_num)]
        rw [hs1, hF01]
      · refine ⟨((s : ℝ) : AddCircle (1 : ℝ)), ?_⟩
        have hxmem : (s : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by rw [zero_add]; exact ⟨hs.1, hs1⟩
        rw [AddCircle.liftIco_coe_apply hxmem]
  refine ⟨fun w => ((AddCircle.liftIco (1 : ℝ) 0 F ((AddCircle.homeomorphCircle hT).symm w) : ℂ) :
    ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp
      (hcirc.comp (AddCircle.homeomorphCircle hT).symm.continuous)
  · intro w₁ w₂ h
    apply (AddCircle.homeomorphCircle hT).symm.injective
    apply hcircinj
    exact OnePoint.coe_injective h
  · show range (fun w => ((AddCircle.liftIco (1 : ℝ) 0 F
        ((AddCircle.homeomorphCircle hT).symm w) : ℂ) : ExtPlane)) = toExt (F '' Icc (0 : ℝ) 1)
    rw [toExt,
      show (fun w => ((AddCircle.liftIco (1 : ℝ) 0 F ((AddCircle.homeomorphCircle hT).symm w) :
          ℂ) : ExtPlane)) =
        ((↑) : ℂ → ExtPlane) ∘ (AddCircle.liftIco (1 : ℝ) 0 F) ∘
          (AddCircle.homeomorphCircle hT).symm from rfl,
      range_comp, range_comp, (AddCircle.homeomorphCircle hT).symm.surjective.range_eq,
      image_univ, hrange]

-- ===== Copied for self-containedness: S1-S4 + diam_closure_eq_diam_frontier (diam_scratch.lean, md5 01f9339d) =====

theorem isSimpleClosedCurve_union_of_arcEndC {A₁ A₂ : Set ℂ} {a b : ℂ}
    (h1 : IsArcEndC A₁ a b) (h2 : IsArcEndC A₂ a b) (hab : a ≠ b)
    (hint : A₁ ∩ A₂ = {a, b}) :
    IsJordanCurve (toExt (A₁ ∪ A₂)) := by
  obtain ⟨γ₁, hA₁, hγ₁c, hγ₁i, hγ₁0, hγ₁1⟩ := h1
  obtain ⟨γ₂, hA₂, hγ₂c, hγ₂i, hγ₂0, hγ₂1⟩ := h2
  set F : ℝ → ℂ := fun t => if t ≤ (1 / 2 : ℝ) then γ₁ (2 * t) else γ₂ (2 - 2 * t) with hF_def
  have hF0 : F 0 = a := by simp only [hF_def]; rw [if_pos (by norm_num)]; norm_num; exact hγ₁0
  have hF1 : F 1 = a := by
    simp only [hF_def]; rw [if_neg (by norm_num)]
    have : (2 : ℝ) - 2 * 1 = 0 := by norm_num
    rw [this, hγ₂0]
  have hFmem : ∀ t ∈ Icc (0 : ℝ) 1, F t ∈ A₁ ∪ A₂ := by
    intro t ht
    simp only [hF_def]
    split
    · next h => exact Or.inl (hA₁ ▸ ⟨2 * t, ⟨by linarith [ht.1], by linarith [h]⟩, rfl⟩)
    · next h =>
      push_neg at h
      exact Or.inr (hA₂ ▸ ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [h]⟩, rfl⟩)
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    have hp1 : {t : ℝ | t ≤ (1 / 2 : ℝ)} = Iic (1 / 2 : ℝ) := rfl
    have hp2 : {t : ℝ | ¬t ≤ (1 / 2 : ℝ)} = Ioi (1 / 2 : ℝ) := by ext t; simp
    apply ContinuousOn.if
    · intro t ht
      rw [hp1, frontier_Iic] at ht
      have ht2 : t = 1 / 2 := by simpa using ht.2
      subst ht2
      show γ₁ (2 * (1 / 2 : ℝ)) = γ₂ (2 - 2 * (1 / 2 : ℝ))
      norm_num
      rw [hγ₁1, hγ₂1]
    · rw [hp1, IsClosed.closure_eq isClosed_Iic]
      apply hγ₁c.comp (Continuous.continuousOn (by fun_prop))
      rintro t ⟨ht1, ht2⟩
      simp only [mem_Iic] at ht2
      show (2 * t : ℝ) ∈ Icc (0 : ℝ) 1
      exact ⟨by linarith [ht1.1], by linarith [ht2]⟩
    · rw [hp2, closure_Ioi]
      apply hγ₂c.comp (Continuous.continuousOn (by fun_prop))
      rintro t ⟨ht1, ht2⟩
      simp only [mem_Ici] at ht2
      show (2 - 2 * t : ℝ) ∈ Icc (0 : ℝ) 1
      exact ⟨by linarith [ht1.2], by linarith [ht2]⟩
  have hinj : InjOn F (Ico (0 : ℝ) 1) := by
    intro s hs t ht hst
    simp only [hF_def] at hst
    split at hst <;> split at hst <;> rename_i hs' ht'
    · have h1 : (2 * s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs']⟩
      have h2 : (2 * t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht']⟩
      have := hγ₁i h1 h2 hst
      linarith
    · push_neg at ht'
      exfalso
      have hsA : F s ∈ A₁ :=
        hA₁ ▸ ⟨2 * s, ⟨by linarith [hs.1], by linarith [hs']⟩, (if_pos hs').symm⟩
      have htA : F t ∈ A₂ :=
        hA₂ ▸ ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [ht']⟩, (if_neg (not_le.mpr ht')).symm⟩
      simp only [hF_def, if_pos hs', if_neg (not_le.mpr ht')] at hsA htA
      rw [hst] at hsA
      have hmem : γ₂ (2 - 2 * t) ∈ ({a, b} : Set ℂ) := hint ▸ ⟨hsA, htA⟩
      have hne0 : (2 - 2 * t : ℝ) ≠ 0 := by intro h; linarith [ht.2]
      have hne1 : (2 - 2 * t : ℝ) ≠ 1 := by intro h; linarith
      have h2t : (2 - 2 * t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht']⟩
      rcases hmem with hmem | hmem
      · exact hne0 (hγ₂i h2t (by norm_num) (by rw [hmem, hγ₂0]))
      · exact hne1 (hγ₂i h2t (by norm_num) (by rw [hmem, hγ₂1]))
    · push_neg at hs'
      exfalso
      have htA : F t ∈ A₁ :=
        hA₁ ▸ ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht']⟩, (if_pos ht').symm⟩
      have hsA : F s ∈ A₂ :=
        hA₂ ▸ ⟨2 - 2 * s, ⟨by linarith [hs.2], by linarith [hs']⟩, (if_neg (not_le.mpr hs')).symm⟩
      simp only [hF_def, if_pos ht', if_neg (not_le.mpr hs')] at hsA htA
      rw [← hst] at htA
      have hmem : γ₂ (2 - 2 * s) ∈ ({a, b} : Set ℂ) := hint ▸ ⟨htA, hsA⟩
      have hne0 : (2 - 2 * s : ℝ) ≠ 0 := by intro h; linarith [hs.2]
      have hne1 : (2 - 2 * s : ℝ) ≠ 1 := by intro h; linarith
      have h2s : (2 - 2 * s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs']⟩
      rcases hmem with hmem | hmem
      · exact hne0 (hγ₂i h2s (by norm_num) (by rw [hmem, hγ₂0]))
      · exact hne1 (hγ₂i h2s (by norm_num) (by rw [hmem, hγ₂1]))
    · push_neg at hs' ht'
      have h1 : (2 - 2 * s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs']⟩
      have h2 : (2 - 2 * t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht']⟩
      have := hγ₂i h1 h2 hst
      linarith
  have hrange : F '' Icc (0 : ℝ) 1 = A₁ ∪ A₂ := by
    apply Subset.antisymm
    · rintro w ⟨t, ht, rfl⟩; exact hFmem t ht
    · rintro w (hw | hw)
      · obtain ⟨s, hs, rfl⟩ := hA₁ ▸ hw
        refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        simp only [hF_def]
        rw [if_pos (by linarith [hs.2])]
        congr 1; ring
      · obtain ⟨s, hs, rfl⟩ := hA₂ ▸ hw
        rcases eq_or_lt_of_le hs.1 with hs0 | hs0
        · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
          rw [hF0, ← hs0, hγ₂0]
        · refine ⟨1 - s / 2, ⟨by linarith [hs.2], by linarith [hs0]⟩, ?_⟩
          rcases eq_or_lt_of_le hs.2 with hs1 | hs1
          · subst hs1
            have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
            rw [e1]
            simp only [hF_def]
            rw [if_pos (le_refl (1 / 2 : ℝ))]
            have e2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
            rw [e2, hγ₁1, hγ₂1]
          · simp only [hF_def]
            rw [if_neg (by linarith [hs1])]
            congr 1; ring
  rw [← hrange]
  exact isJordanCurve_of_loop hcont hinj (hF0.trans hF1.symm)

theorem exists_subarc_interior_of_mem_isSimpleClosedCurve {C : Set E2'}
    (hC : IsSimpleClosedCurve C) {x : E2'} (hx : x ∈ C) :
    ∃ (A : Set E2') (v w : E2'), IsSimpleArcEnd A v w ∧ A ⊆ C ∧ x ∈ A ∧ x ≠ v ∧ x ≠ w := by
  obtain ⟨f, hfC, hfcont, hfinj, hf0x, hfperiod⟩ := isSimpleClosedCurve_pt hC hx
  set y := f (1 / 2 : ℝ) with hy_def
  have hy_mem : y ∈ C := by rw [hfC]; exact ⟨1 / 2, by norm_num, rfl⟩
  have hyx : y ≠ x := by
    intro h
    have h01 := hfinj (show (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num)
      (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num) (by rw [hy_def] at h; rw [h, hf0x])
    norm_num at h01
  obtain ⟨g, hgC, hgcont, hginj, hg0y, hgperiod⟩ := isSimpleClosedCurve_pt hC hy_mem
  have hxC : x ∈ C := hx
  rw [hgC] at hxC
  obtain ⟨s₀, hs₀, hgs₀⟩ := hxC
  have hs₀_ne1 : s₀ ≠ 1 := by
    intro h; rw [h, ← hgperiod, hg0y] at hgs₀; exact hyx hgs₀
  have hs₀_ne0 : s₀ ≠ 0 := by
    intro h; rw [h, hg0y] at hgs₀; exact hyx hgs₀
  have hs₀' : s₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs₀.1 (Ne.symm hs₀_ne0), lt_of_le_of_ne hs₀.2 hs₀_ne1⟩
  set ε : ℝ := min (s₀ / 2) ((1 - s₀) / 2) with hε_def
  have hε_pos : 0 < ε := lt_min (by linarith [hs₀'.1]) (by linarith [hs₀'.2])
  have hε_le1 : ε ≤ s₀ / 2 := min_le_left _ _
  have hε_le2 : ε ≤ (1 - s₀) / 2 := min_le_right _ _
  have hlo : (0 : ℝ) < s₀ - ε := by linarith
  have hhi : s₀ + ε < 1 := by linarith
  set h : ℝ → E2' := fun t => g (s₀ - ε + 2 * ε * t) with hh_def
  have hmapmem : ∀ t ∈ Icc (0 : ℝ) 1, s₀ - ε + 2 * ε * t ∈ Ico (0 : ℝ) 1 := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, hε_pos]
  have hmapIcc : ∀ t ∈ Icc (0 : ℝ) 1, s₀ - ε + 2 * ε * t ∈ Icc (s₀ - ε) (s₀ + ε) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, hε_pos]
  have hinjA : InjOn h (Icc (0 : ℝ) 1) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have := hginj (hmapmem t₁ ht₁) (hmapmem t₂ ht₂) heq
    have hε_ne : (2 : ℝ) * ε ≠ 0 := by positivity
    have : s₀ - ε + 2 * ε * t₁ = s₀ - ε + 2 * ε * t₂ := this
    have : 2 * ε * t₁ = 2 * ε * t₂ := by linarith
    exact mul_left_cancel₀ hε_ne this
  have hcontA : Continuous h := hgcont.comp (by fun_prop)
  have h2ε : (2 : ℝ) * ε ≠ 0 := by positivity
  have himg : h '' Icc (0 : ℝ) 1 = g '' Icc (s₀ - ε) (s₀ + ε) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩; exact ⟨_, hmapIcc t ht, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(u - (s₀ - ε)) / (2 * ε), ⟨div_nonneg (by linarith [hu.1]) (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; linarith [hu.2]
      · simp only [hh_def]
        congr 1
        rw [mul_div_cancel₀ _ h2ε]
        ring
  refine ⟨h '' Icc (0 : ℝ) 1, h 0, h 1, ⟨h, rfl, hcontA, hinjA, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [himg]; rintro _ ⟨u, hu, rfl⟩; rw [hgC]
    exact ⟨u, ⟨hlo.le.trans hu.1, by linarith [hu.2]⟩, rfl⟩
  · rw [himg]; exact ⟨s₀, ⟨by linarith, by linarith⟩, hgs₀⟩
  · have hs₀'' : s₀ ∈ Ico (0 : ℝ) 1 := ⟨hs₀'.1.le, hs₀'.2⟩
    simp only [hh_def]
    rw [show s₀ - ε + 2 * ε * 0 = s₀ - ε by ring]
    intro heq
    have hmem : s₀ - ε ∈ Ico (0:ℝ) 1 := ⟨hlo.le, by linarith⟩
    have := hginj hs₀'' hmem (hgs₀.trans heq)
    linarith [this]
  · have hs₀'' : s₀ ∈ Ico (0 : ℝ) 1 := ⟨hs₀'.1.le, hs₀'.2⟩
    simp only [hh_def]
    rw [show s₀ - ε + 2 * ε * 1 = s₀ + ε by ring]
    intro heq
    have hmem : s₀ + ε ∈ Ico (0:ℝ) 1 := ⟨by linarith, hhi⟩
    have := hginj hs₀'' hmem (hgs₀.trans heq)
    linarith [this]

/-- E2'-native version of the frontier statement; the ℂ version follows by transport. -/
theorem frontier_pieces_eq_of_isSimpleClosedCurve_E2 {C A B : Set E2'}
    (hC : IsSimpleClosedCurve C)
    (hA : IsOpen A) (hB : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (huniv : A ∪ B ∪ C = univ) :
    frontier A = C ∧ frontier B = C := by
  have hCclosed : IsClosed C := by
    obtain ⟨f, hfC, hfcont, -⟩ := hC
    rw [hfC]; exact (isCompact_Icc.image hfcont).isClosed
  -- easy half
  have hfrA_sub : frontier A ⊆ C := by
    rw [hA.frontier_eq]
    intro z hz
    rcases (huniv ▸ mem_univ z : z ∈ A ∪ B ∪ C) with (h | h) | h
    · exact absurd h hz.2
    · exfalso
      obtain ⟨y, hyBA⟩ := mem_closure_iff_nhds.1 hz.1 B (hB.mem_nhds h)
      exact Set.disjoint_left.1 hAB hyBA.2 hyBA.1
    · exact h
  have hfrB_sub : frontier B ⊆ C := by
    rw [hB.frontier_eq]
    intro z hz
    rcases (huniv ▸ mem_univ z : z ∈ A ∪ B ∪ C) with (h | h) | h
    · exfalso
      obtain ⟨y, hyAB⟩ := mem_closure_iff_nhds.1 hz.1 A (hA.mem_nhds h)
      exact Set.disjoint_left.1 hAB hyAB.1 hyAB.2
    · exact absurd h hz.2
    · exact h
  have hsplit : ∀ (S U' V' : Set E2') (p : E2'), IsPreconnected S → IsOpen U' → IsOpen V' →
      Disjoint U' V' → S ⊆ U' ∪ V' → p ∈ S → p ∈ U' → S ⊆ U' := by
    intro S U' V' p hSpre hU' hV' hUV' hSsub hpS hpU'
    rcases isPreconnected_iff_subset_of_disjoint.1 hSpre U' V' hU' hV' hSsub
        (Set.eq_empty_iff_forall_notMem.2 fun z hz => Set.disjoint_left.1 hUV' hz.2.1 hz.2.2) with h | h
    · exact h
    · exact absurd (h hpS) (fun hpV => Set.disjoint_left.1 hUV' hpU' hpV)
  have hard : ∀ (U' V' : Set E2'), IsOpen U' → IsOpen V' → IsConnected U' → IsConnected V' →
      Disjoint U' V' → Disjoint U' C → Disjoint V' C → U' ∪ V' ∪ C = univ → C ⊆ frontier U' := by
    intro U' V' hU' hV' hU'c hV'c hUV' hU'C hV'C huniv'
    rw [hU'.frontier_eq]
    intro x hx
    obtain ⟨p, hp⟩ := hU'c.nonempty
    obtain ⟨q, hq⟩ := hV'c.nonempty
    have hpq : p ≠ q := fun h => Set.disjoint_left.1 hUV' hp (h ▸ hq)
    have hpC : p ∉ C := fun h => Set.disjoint_left.1 hU'C hp h
    have hqC : q ∉ C := fun h => Set.disjoint_left.1 hV'C hq h
    have hsep : ∀ F : Set E2', IsSimpleArcEnd F p q → (F ∩ C).Nonempty := by
      intro F hF
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      obtain ⟨k, hkF, hkcont, hkinj, hk0, hk1⟩ := hF
      have hFpre : IsPreconnected F := by
        rw [hkF]; exact (isPreconnected_Icc).image k hkcont.continuousOn
      have hFsub : F ⊆ U' ∪ V' := fun z hz => by
        rcases (huniv' ▸ mem_univ z : z ∈ U' ∪ V' ∪ C) with h | h
        · exact h
        · exact absurd (hcon ▸ (⟨hz, h⟩ : z ∈ F ∩ C) : z ∈ (∅ : Set E2')) (by simp)
      have hpF : p ∈ F := hkF ▸ ⟨0, left_mem_Icc.mpr zero_le_one, hk0⟩
      have hqF : q ∈ F := hkF ▸ ⟨1, right_mem_Icc.mpr zero_le_one, hk1⟩
      have hFU' := hsplit F U' V' p hFpre hU' hV' hUV' hFsub hpF hp
      exact Set.disjoint_left.1 hUV' (hFU' hqF) hq
    refine ⟨?_, fun hxU' => Set.disjoint_left.1 hU'C hxU' hx⟩
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨Asub, v, w, hAsubArc, hAsubSub, hxA, hxv, hxw⟩ :=
      exists_subarc_interior_of_mem_isSimpleClosedCurve hC hx
    obtain ⟨g, hgAsub, hgcont, hginj, hg0v, hg1w⟩ := hAsubArc
    have hxA' : x ∈ Asub := hxA
    rw [hgAsub] at hxA'
    obtain ⟨s, hs, hgsx⟩ := hxA'
    have hsne0 : s ≠ 0 := fun h => hxv (by rw [← hgsx, h, hg0v])
    have hsne1 : s ≠ 1 := fun h => hxw (by rw [← hgsx, h, hg1w])
    have hs' : s ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsne0), lt_of_le_of_ne hs.2 hsne1⟩
    obtain ⟨ε', hε'pos, hε'⟩ := Metric.continuousAt_iff.1 hgcont.continuousAt (δ / 6) (by linarith)
    set ε₀ : ℝ := min (min (s / 2) ((1 - s) / 2)) (ε' / 2) with hε₀_def
    have hε₀pos : 0 < ε₀ :=
      lt_min (lt_min (by linarith [hs'.1]) (by linarith [hs'.2])) (by linarith)
    have hε₀s : ε₀ ≤ s / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hε₀s' : ε₀ ≤ (1 - s) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hε₀ε' : ε₀ ≤ ε' / 2 := min_le_right _ _
    have hlo : (0 : ℝ) < s - ε₀ := by linarith
    have hhi : s + ε₀ < 1 := by linarith
    set Asub' : Set E2' := g '' Icc (s - ε₀) (s + ε₀) with hAsub'_def
    have hAsub'sub : Asub' ⊆ Asub := by
      rw [hgAsub]; rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
    have hAsub'_small : ∀ y ∈ Asub', dist y x < δ / 3 := by
      rintro y ⟨u, hu, rfl⟩
      have hdu : dist u s < ε' := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> [linarith [hu.1]; linarith [hu.2]]
      have := hε' hdu
      rw [hgsx] at this
      linarith [this]
    have hxv' : x ≠ g (s - ε₀) := fun heq => by
      have := hginj (show s - ε₀ ∈ Icc (0:ℝ) 1 from ⟨hlo.le, by linarith⟩)
        (show s ∈ Icc (0:ℝ) 1 from hs) (hgsx.trans heq).symm
      linarith [this]
    have hxw' : x ≠ g (s + ε₀) := fun heq => by
      have := hginj (show s + ε₀ ∈ Icc (0:ℝ) 1 from ⟨by linarith, hhi.le⟩)
        (show s ∈ Icc (0:ℝ) 1 from hs) (hgsx.trans heq).symm
      linarith [this]
    have hxA'2 : x ∈ Asub' := ⟨s, ⟨by linarith, by linarith⟩, hgsx⟩
    have h2ε₀ : (2 : ℝ) * ε₀ ≠ 0 := by positivity
    set h' : ℝ → E2' := fun t => g (s - ε₀ + 2 * ε₀ * t) with hh'_def
    have hmapmem' : ∀ t ∈ Icc (0 : ℝ) 1, s - ε₀ + 2 * ε₀ * t ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2, hε₀pos]
    have hmapIcc' : ∀ t ∈ Icc (0 : ℝ) 1, s - ε₀ + 2 * ε₀ * t ∈ Icc (s - ε₀) (s + ε₀) := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2, hε₀pos]
    have hinjA' : InjOn h' (Icc (0 : ℝ) 1) := by
      intro t₁ ht₁ t₂ ht₂ heq
      have heq2 := hginj (hmapmem' t₁ ht₁) (hmapmem' t₂ ht₂) heq
      have heq3 : 2 * ε₀ * t₁ = 2 * ε₀ * t₂ := by linarith [heq2]
      exact mul_left_cancel₀ h2ε₀ heq3
    have hcontA' : Continuous h' := hgcont.comp (by fun_prop)
    have himg' : h' '' Icc (0 : ℝ) 1 = Asub' := by
      rw [hAsub'_def]
      apply Subset.antisymm
      · rintro _ ⟨t, ht, rfl⟩; exact ⟨_, hmapIcc' t ht, rfl⟩
      · rintro _ ⟨u, hu, rfl⟩
        refine ⟨(u - (s - ε₀)) / (2 * ε₀), ⟨div_nonneg (by linarith [hu.1]) (by positivity), ?_⟩, ?_⟩
        · rw [div_le_one (by positivity)]; linarith [hu.2]
        · simp only [hh'_def]
          congr 1
          rw [mul_div_cancel₀ _ h2ε₀]
          ring
    have hAsubArc' : IsSimpleArcEnd Asub' (g (s - ε₀)) (g (s + ε₀)) :=
      ⟨h', himg'.symm, hcontA', hinjA', by simp [hh'_def], by
        simp only [hh'_def]; congr 1; ring⟩
    obtain ⟨E, hE_arc, hE_sub, hE_cut⟩ :=
      jordan_curve_access hC hAsubArc' (hAsub'sub.trans hAsubSub) hxA'2 hxv' hxw' hpC
        ⟨q, hpq, hqC, hsep⟩
    have hE_arc' := hE_arc
    obtain ⟨k, hkE, hkcont, hkinj, hk0, hk1⟩ := hE_arc'
    have hkCclosed : IsClosed (Icc (0:ℝ) 1 ∩ k ⁻¹' C) :=
      isClosed_Icc.inter (hCclosed.preimage hkcont)
    have hT_ne : (Icc (0:ℝ) 1 ∩ k ⁻¹' C).Nonempty :=
      ⟨1, right_mem_Icc.mpr zero_le_one, by rw [Set.mem_preimage, hk1]; exact hx⟩
    have hT_bdd : BddBelow (Icc (0:ℝ) 1 ∩ k ⁻¹' C) := ⟨0, fun t ht => ht.1.1⟩
    set t₁ := sInf (Icc (0:ℝ) 1 ∩ k ⁻¹' C) with ht₁_def
    have ht₁mem := hkCclosed.csInf_mem hT_ne hT_bdd
    have ht₁C : k t₁ ∈ C := ht₁mem.2
    have ht₁Icc : t₁ ∈ Icc (0:ℝ) 1 := ht₁mem.1
    have ht₁pos : 0 < t₁ := by
      rcases eq_or_lt_of_le ht₁Icc.1 with h | h
      · exfalso
        have : k 0 ∈ C := by rw [h]; exact ht₁C
        rw [hk0] at this; exact hpC this
      · exact h
    obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.1 hkcont.continuousAt (δ / 3) (by linarith)
    set t₂ := t₁ - min (δ' / 2) (t₁ / 2) with ht₂_def
    have ht₂lt : t₂ < t₁ := by
      have h1 : 0 < min (δ' / 2) (t₁ / 2) := lt_min (by linarith) (by linarith)
      linarith
    have ht₂pos : 0 < t₂ := by
      have h1 : min (δ' / 2) (t₁ / 2) ≤ t₁ / 2 := min_le_right _ _
      linarith
    have ht₂C : k t₂ ∉ C := fun h => by
      have hmem : t₂ ∈ Icc (0:ℝ) 1 ∩ k ⁻¹' C := ⟨⟨ht₂pos.le, by linarith [ht₁Icc.2]⟩, h⟩
      have := csInf_le hT_bdd hmem
      linarith [this]
    have ht₂dist : dist (k t₂) (k t₁) < δ / 3 := by
      apply hδ'
      rw [Real.dist_eq, abs_of_neg (by linarith : t₂ - t₁ < 0)]
      have h1 : min (δ' / 2) (t₁ / 2) ≤ δ' / 2 := min_le_left _ _
      linarith [h1]
    have ht₂p : k t₂ ≠ p := fun h => by
      have h01 : t₂ ∈ Icc (0:ℝ) 1 := ⟨ht₂pos.le, by linarith [ht₁Icc.2]⟩
      have := hkinj h01 (left_mem_Icc.mpr zero_le_one) (h.trans hk0.symm)
      linarith [this]
    have ht₂memE : k t₂ ∈ E := hkE ▸ ⟨t₂, ⟨ht₂pos.le, by linarith [ht₁Icc.2]⟩, rfl⟩
    have hcut := hE_cut (k t₂) ht₂memE ht₂C (Ne.symm ht₂p)
    have hcutpre : IsPreconnected (cutArc E p (k t₂)) := by
      have harc := cutArc_isSimpleArcEnd (isSimpleArcEnd_isSimpleArc hE_arc)
        (isSimpleArcEnd_mem_left hE_arc) ht₂memE ht₂p.symm
      obtain ⟨kc, hkcE, hkccont, -, -, -⟩ := harc
      rw [hkcE]; exact (isPreconnected_Icc).image kc hkccont.continuousOn
    have hcutsub : cutArc E p (k t₂) ⊆ U' ∪ V' := fun z hz => by
      rcases (huniv' ▸ mem_univ z : z ∈ U' ∪ V' ∪ C) with h | h
      · exact h
      · exact absurd h (Set.disjoint_left.1 hcut hz)
    have hcut_mem_left : p ∈ cutArc E p (k t₂) := isSimpleArcEnd_mem_left
      (cutArc_isSimpleArcEnd (isSimpleArcEnd_isSimpleArc hE_arc) (isSimpleArcEnd_mem_left hE_arc)
        ht₂memE ht₂p.symm)
    have hcut_mem_right : k t₂ ∈ cutArc E p (k t₂) := isSimpleArcEnd_mem_right
      (cutArc_isSimpleArcEnd (isSimpleArcEnd_isSimpleArc hE_arc) (isSimpleArcEnd_mem_left hE_arc)
        ht₂memE ht₂p.symm)
    have hcutU' := hsplit (cutArc E p (k t₂)) U' V' p hcutpre hU' hV' hUV' hcutsub hcut_mem_left hp
    have hkt₂U' : k t₂ ∈ U' := hcutU' hcut_mem_right
    have hkt₁Asub' : k t₁ ∈ Asub' := hE_sub ⟨hkE ▸ ⟨t₁, ht₁Icc, rfl⟩, ht₁C⟩
    refine ⟨k t₂, hkt₂U', ?_⟩
    calc dist x (k t₂) ≤ dist x (k t₁) + dist (k t₁) (k t₂) := dist_triangle _ _ _
      _ < δ / 3 + δ / 3 := by
          have h1 := hAsub'_small (k t₁) hkt₁Asub'
          rw [dist_comm] at h1
          have h2 := ht₂dist
          rw [dist_comm] at h2
          linarith [h1, h2]
      _ < δ := by linarith
  exact ⟨Subset.antisymm hfrA_sub (hard A B hA hB hAc hBc hAB hAC hBC huniv),
    Subset.antisymm hfrB_sub (hard B A hB hA hBc hAc hAB.symm hBC hAC
      (by rw [← huniv]; ac_rfl))⟩

theorem frontier_pieces_eq_of_jordan_curve_theorem_complex {C A B : Set ℂ}
    (hC : IsJordanCurve (toExt C))
    (hA : IsOpen A) (hB : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (huniv : A ∪ B ∪ C = univ) :
    frontier A = C ∧ frontier B = C := by
  have hC' : IsSimpleClosedCurve (complexToE2 '' C) :=
    isSimpleClosedCurve_image_of_isJordanCurve hC
  have hA' : IsOpen (complexToE2 '' A) := complexToE2.isOpen_image.2 hA
  have hB' : IsOpen (complexToE2 '' B) := complexToE2.isOpen_image.2 hB
  have hAc' : IsConnected (complexToE2 '' A) := hAc.image _ complexToE2.continuous.continuousOn
  have hBc' : IsConnected (complexToE2 '' B) := hBc.image _ complexToE2.continuous.continuousOn
  have hinj := complexToE2.injective
  have hAB' : Disjoint (complexToE2 '' A) (complexToE2 '' B) :=
    Set.disjoint_image_of_injective hinj hAB
  have hAC' : Disjoint (complexToE2 '' A) (complexToE2 '' C) :=
    Set.disjoint_image_of_injective hinj hAC
  have hBC' : Disjoint (complexToE2 '' B) (complexToE2 '' C) :=
    Set.disjoint_image_of_injective hinj hBC
  have huniv' : complexToE2 '' A ∪ complexToE2 '' B ∪ complexToE2 '' C = univ := by
    rw [← Set.image_union, ← Set.image_union, huniv, Set.image_univ,
      complexToE2.surjective.range_eq]
  obtain ⟨hfrA', hfrB'⟩ :=
    frontier_pieces_eq_of_isSimpleClosedCurve_E2 hC' hA' hB' hAc' hBc' hAB' hAC' hBC' huniv'
  rw [← complexToE2.image_frontier] at hfrA' hfrB'
  exact ⟨hinj.image_injective hfrA', hinj.image_injective hfrB'⟩

/-- `A \ {v, w}` is connected, for `A = IsArcEndC A v w`: it is the continuous image of the
connected set `Ioo 0 1` (using injectivity on `Icc 0 1` to identify the preimage of `{v,w}`
exactly with `{0,1}`). -/
theorem isConnected_arcEndC_diff_endpoints {A : Set ℂ} {v w : ℂ}
    (h : IsArcEndC A v w) : IsConnected (A \ {v, w}) := by
  obtain ⟨γ, hA, hγc, hγi, hγ0, hγ1⟩ := h
  have heq : A \ {v, w} = γ '' Ioo 0 1 := by
    rw [hA]
    ext z
    simp only [mem_diff, mem_image, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hne⟩
      refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, rfl⟩
      · rintro rfl; exact hne (Or.inl hγ0)
      · rintro rfl; exact hne (Or.inr hγ1)
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩, ?_⟩
      rintro (h | h)
      · exact absurd (hγi ⟨hs.1.le, hs.2.le⟩ (by norm_num) (h.trans hγ0.symm)) (by linarith [hs.1])
      · exact absurd (hγi ⟨hs.1.le, hs.2.le⟩ (by norm_num) (h.trans hγ1.symm)) (by linarith [hs.2])
  rw [heq]
  exact (isConnected_Ioo (by norm_num)).image _
    (hγc.mono Ioo_subset_Icc_self)

/-- Given a Jordan curve `C` with JCT pieces `A` (bounded), `B` (unbounded), any connected
unbounded set disjoint from `C` lies in `B`. (Immediate consequence of `A` being bounded.) -/
theorem subset_unbounded_piece_of_isConnected_not_isBounded {C A B E : Set ℂ}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (_hAC : Disjoint A C)
    (_hBC : Disjoint B C)
    (huniv : A ∪ B ∪ C = univ) (hAb : Bornology.IsBounded A)
    (hEc : IsConnected E) (hEb : ¬ Bornology.IsBounded E) (hEC : Disjoint E C) :
    E ⊆ B := by
  have hEsub : E ⊆ A ∪ B := by
    intro z hz
    rcases (huniv ▸ mem_univ z : z ∈ A ∪ B ∪ C) with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hEC hz)
  rcases (isPreconnected_iff_subset_of_disjoint.1 hEc.isPreconnected) A B hA hB hEsub
    (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hzA, hzB⟩
      exact Set.disjoint_left.1 hAB hzA hzB) with h | h
  · exact absurd (hAb.subset h) hEb
  · exact h

/-- **The S1 boundedness helper.**  For a bounded Jordan domain `Ω`, the interior of `closure Ω`
is `⊆ Ω`: a point of `interior (closure Ω)` cannot be on `frontier Ω`, because `frontier Ω`
equals the frontier of `(closure Ω)ᶜ` (both are `frontier Ω` by the JCT applied to `Ω` and
`(closure Ω)ᶜ`), which is disjoint from `interior (closure Ω)`. -/
theorem interior_closure_subset_of_isJordanCurve_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω) (hJ : IsJordanCurve (toExt (frontier Ω))) :
    interior (closure Ω) ⊆ Ω := by
  set B : Set ℂ := (closure Ω)ᶜ with hB_def
  obtain ⟨hBc, hBb⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hJ
  have hBopen : IsOpen B := isClosed_closure.isOpen_compl
  have hcl : closure Ω = Ω ∪ frontier Ω := by
    rw [closure_eq_interior_union_frontier, hΩo.interior_eq]
  have hAC : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  have hBC : Disjoint B (frontier Ω) := by
    rw [Set.disjoint_left]
    intro z hzB hzfr
    exact hzB (frontier_subset_closure hzfr)
  have hAB : Disjoint Ω B := by
    rw [Set.disjoint_left]
    intro z hzΩ hzB
    exact hzB (subset_closure hzΩ)
  have huniv : Ω ∪ B ∪ frontier Ω = univ := by
    rw [hB_def, union_right_comm, ← hcl, union_compl_self]
  obtain ⟨-, hfrB⟩ := frontier_pieces_eq_of_jordan_curve_theorem_complex hJ hΩo hBopen hΩc hBc
    hAB hAC hBC huniv
  have hfrB_sub : frontier B ⊆ (interior (closure Ω))ᶜ :=
    frontier_subset_closure.trans (by rw [hB_def, closure_compl])
  intro z hz
  have hzcl : z ∈ closure Ω := interior_subset hz
  have hzfr : z ∉ frontier Ω := by
    rw [← hfrB]
    intro hzfrB
    exact hfrB_sub hzfrB hz
  rw [hcl] at hzcl
  rcases hzcl with h | h
  · exact h
  · exact absurd h hzfr

theorem S1_pieces_identification {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hJ : IsJordanCurve (toExt (frontier Ω)))
    {τ τ' D : Set ℂ} {a b : ℂ} (hab : a ≠ b)
    (hτarc : IsArcEndC τ a b) (hτ'arc : IsArcEndC τ' a b)
    (hττ'union : τ ∪ τ' = frontier Ω) (hττ'int : τ ∩ τ' = {a, b})
    (hDarc : IsArcEndC D a b) (hDτ : D ∩ τ = {a, b}) (hDτ' : D ∩ τ' = {a, b})
    (hDΩ : D \ {a, b} ⊆ Ω) :
    ∃ I₁ I₂ W : Set ℂ,
      IsOpen I₁ ∧ IsOpen I₂ ∧ IsOpen W ∧ IsConnected I₁ ∧ IsConnected I₂ ∧
      I₁ ⊆ Ω ∧ I₂ ⊆ Ω ∧ Disjoint I₁ I₂ ∧ Disjoint I₁ W ∧ Disjoint I₂ W ∧
      frontier I₁ = τ ∪ D ∧ frontier I₂ = τ' ∪ D ∧
      Ω \ D = I₁ ∪ I₂ ∪ W := by
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  have hint_a : a ∈ τ ∩ τ' := by rw [hττ'int]; simp
  have hint_b : b ∈ τ ∩ τ' := by rw [hττ'int]; simp
  have haτ : a ∈ τ := hint_a.1
  have hbτ : b ∈ τ := hint_b.1
  have haτ' : a ∈ τ' := hint_a.2
  have hbτ' : b ∈ τ' := hint_b.2
  have hτsub : τ ⊆ frontier Ω := by rw [← hττ'union]; exact subset_union_left
  have hτ'sub : τ' ⊆ frontier Ω := by rw [← hττ'union]; exact subset_union_right
  have hDsub : D ⊆ closure Ω := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact frontier_subset_closure (hτsub haτ)
    rcases eq_or_ne z b with rfl | hzb
    · exact frontier_subset_closure (hτsub hbτ)
    · exact subset_closure (hDΩ ⟨hz, by simp [hza, hzb]⟩)
  -- The two auxiliary Jordan curves and their JCT decompositions.
  have hJ₁ : IsJordanCurve (toExt (τ ∪ D)) :=
    isSimpleClosedCurve_union_of_arcEndC hτarc hDarc hab ((Set.inter_comm τ D).trans hDτ)
  have hJ₂ : IsJordanCurve (toExt (τ' ∪ D)) :=
    isSimpleClosedCurve_union_of_arcEndC hτ'arc hDarc hab ((Set.inter_comm τ' D).trans hDτ')
  obtain ⟨P₁, Q₁, hP₁o, hQ₁o, hP₁c, hQ₁c, hP₁Q₁, hP₁Γ₁, hQ₁Γ₁, huniv₁, hP₁b, hQ₁b⟩ :=
    jordan_curve_theorem_complex_bounded hJ₁
  obtain ⟨P₂, Q₂, hP₂o, hQ₂o, hP₂c, hQ₂c, hP₂Q₂, hP₂Γ₂, hQ₂Γ₂, huniv₂, hP₂b, hQ₂b⟩ :=
    jordan_curve_theorem_complex_bounded hJ₂
  have hfrP₁ : frontier P₁ = τ ∪ D :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hJ₁ hP₁o hQ₁o hP₁c hQ₁c hP₁Q₁ hP₁Γ₁
      hQ₁Γ₁ huniv₁).1
  have hfrP₂ : frontier P₂ = τ' ∪ D :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hJ₂ hP₂o hQ₂o hP₂c hQ₂c hP₂Q₂ hP₂Γ₂
      hQ₂Γ₂ huniv₂).1
  have hΓ₁sub : τ ∪ D ⊆ closure Ω :=
    union_subset (hτsub.trans frontier_subset_closure) hDsub
  have hΓ₂sub : τ' ∪ D ⊆ closure Ω :=
    union_subset (hτ'sub.trans frontier_subset_closure) hDsub
  obtain ⟨hEc, hEb⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hJ
  have hEΓ₁ : Disjoint (closure Ω)ᶜ (τ ∪ D) :=
    Set.disjoint_left.2 fun z hz hz2 => hz (hΓ₁sub hz2)
  have hEΓ₂ : Disjoint (closure Ω)ᶜ (τ' ∪ D) :=
    Set.disjoint_left.2 fun z hz hz2 => hz (hΓ₂sub hz2)
  have hEQ₁ : (closure Ω)ᶜ ⊆ Q₁ :=
    subset_unbounded_piece_of_isConnected_not_isBounded hP₁o hQ₁o hP₁Q₁ hP₁Γ₁ hQ₁Γ₁ huniv₁ hP₁b
      hEc hEb hEΓ₁
  have hEQ₂ : (closure Ω)ᶜ ⊆ Q₂ :=
    subset_unbounded_piece_of_isConnected_not_isBounded hP₂o hQ₂o hP₂Q₂ hP₂Γ₂ hQ₂Γ₂ huniv₂ hP₂b
      hEc hEb hEΓ₂
  have hP₁cl : P₁ ⊆ closure Ω := fun z hz =>
    by_contra fun hzc => Set.disjoint_left.1 hP₁Q₁ hz (hEQ₁ hzc)
  have hP₂cl : P₂ ⊆ closure Ω := fun z hz =>
    by_contra fun hzc => Set.disjoint_left.1 hP₂Q₂ hz (hEQ₂ hzc)
  have hP₁Ω : P₁ ⊆ Ω :=
    (interior_maximal hP₁cl hP₁o).trans
      (interior_closure_subset_of_isJordanCurve_frontier hΩo hΩc hΩb hJ)
  have hP₂Ω : P₂ ⊆ Ω :=
    (interior_maximal hP₂cl hP₂o).trans
      (interior_closure_subset_of_isJordanCurve_frontier hΩo hΩc hΩb hJ)
  -- τ' minus its endpoints is disjoint from Γ₁ and, since P₁ ⊆ Ω is disjoint from ∂Ω, lands in Q₁.
  have hτ'mG1 : Disjoint (τ' \ {a, b}) (τ ∪ D) := by
    rw [Set.disjoint_union_right]
    refine ⟨Set.disjoint_left.2 ?_, Set.disjoint_left.2 ?_⟩
    · rintro z ⟨hz1, hz2⟩ hz3
      exact hz2 (hττ'int ▸ (⟨hz3, hz1⟩ : z ∈ τ ∩ τ'))
    · rintro z ⟨hz1, hz2⟩ hz3
      exact hz2 (hDτ' ▸ (⟨hz3, hz1⟩ : z ∈ D ∩ τ'))
  have hτ'msub : τ' \ {a, b} ⊆ P₁ ∪ Q₁ := fun z hz =>
    (huniv₁ ▸ mem_univ z : z ∈ P₁ ∪ Q₁ ∪ (τ ∪ D)).elim id
      (fun h => absurd h (Set.disjoint_left.1 hτ'mG1 hz))
  have hτ'mQ1 : τ' \ {a, b} ⊆ Q₁ := by
    have hpre1 : IsPreconnected (τ' \ {a, b}) :=
      (isConnected_arcEndC_diff_endpoints hτ'arc).isPreconnected
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre1 P₁ Q₁ hP₁o hQ₁o hτ'msub
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, h1, h2⟩; exact Set.disjoint_left.1 hP₁Q₁ h1 h2) with hcase | hcase
    · exfalso
      obtain ⟨z, hz⟩ := (isConnected_arcEndC_diff_endpoints hτ'arc).nonempty
      exact Set.disjoint_left.1 hΩfr (hP₁Ω (hcase hz)) (hτ'sub hz.1)
    · exact hcase
  have htmG2 : Disjoint (τ \ {a, b}) (τ' ∪ D) := by
    rw [Set.disjoint_union_right]
    refine ⟨Set.disjoint_left.2 ?_, Set.disjoint_left.2 ?_⟩
    · rintro z ⟨hz1, hz2⟩ hz3
      exact hz2 (hττ'int ▸ (⟨hz1, hz3⟩ : z ∈ τ ∩ τ'))
    · rintro z ⟨hz1, hz2⟩ hz3
      exact hz2 (hDτ ▸ (⟨hz3, hz1⟩ : z ∈ D ∩ τ))
  have htmsub : τ \ {a, b} ⊆ P₂ ∪ Q₂ := fun z hz =>
    (huniv₂ ▸ mem_univ z : z ∈ P₂ ∪ Q₂ ∪ (τ' ∪ D)).elim id
      (fun h => absurd h (Set.disjoint_left.1 htmG2 hz))
  have htmQ2 : τ \ {a, b} ⊆ Q₂ := by
    have hpre2 : IsPreconnected (τ \ {a, b}) :=
      (isConnected_arcEndC_diff_endpoints hτarc).isPreconnected
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre2 P₂ Q₂ hP₂o hQ₂o htmsub
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, h1, h2⟩; exact Set.disjoint_left.1 hP₂Q₂ h1 h2) with hcase | hcase
    · exfalso
      obtain ⟨z, hz⟩ := (isConnected_arcEndC_diff_endpoints hτarc).nonempty
      exact Set.disjoint_left.1 hΩfr (hP₂Ω (hcase hz)) (hτsub hz.1)
    · exact hcase
  -- P₂ misses Γ₁, so lies entirely in P₁ or Q₁ (and symmetrically for P₁ vs Γ₂).
  have habD : ({a, b} : Set ℂ) ⊆ D := by
    obtain ⟨γD, hDeq, -, -, hD0, hD1⟩ := hDarc
    rw [hDeq]
    rintro z (rfl | rfl)
    · exact ⟨0, left_mem_Icc.mpr zero_le_one, hD0⟩
    · exact ⟨1, right_mem_Icc.mpr zero_le_one, hD1⟩
  have hP₂Γ₁ : Disjoint P₂ (τ ∪ D) := by
    rw [Set.disjoint_union_right]
    refine ⟨Set.disjoint_left.2 ?_,
      Set.disjoint_left.2 (fun z hz => (Set.disjoint_left.1 hP₂Γ₂ hz) ∘ Or.inr)⟩
    intro z hz hzτ
    rcases eq_or_ne z a with rfl | hza
    · exact Set.disjoint_left.1 hP₂Γ₂ hz (Or.inr (habD (Or.inl rfl)))
    rcases eq_or_ne z b with rfl | hzb
    · exact Set.disjoint_left.1 hP₂Γ₂ hz (Or.inr (habD (Or.inr rfl)))
    · exact Set.disjoint_left.1 hP₂Q₂ hz (htmQ2 ⟨hzτ, by simp [hza, hzb]⟩)
  have hP₁Γ₂ : Disjoint P₁ (τ' ∪ D) := by
    rw [Set.disjoint_union_right]
    refine ⟨Set.disjoint_left.2 ?_,
      Set.disjoint_left.2 (fun z hz => (Set.disjoint_left.1 hP₁Γ₁ hz) ∘ Or.inr)⟩
    intro z hz hzτ'
    rcases eq_or_ne z a with rfl | hza
    · exact Set.disjoint_left.1 hP₁Γ₁ hz (Or.inr (habD (Or.inl rfl)))
    rcases eq_or_ne z b with rfl | hzb
    · exact Set.disjoint_left.1 hP₁Γ₁ hz (Or.inr (habD (Or.inr rfl)))
    · exact Set.disjoint_left.1 hP₁Q₁ hz (hτ'mQ1 ⟨hzτ', by simp [hza, hzb]⟩)
  have hP₂case : P₂ ⊆ P₁ ∨ P₂ ⊆ Q₁ :=
    isPreconnected_iff_subset_of_disjoint.1 hP₂c.isPreconnected P₁ Q₁ hP₁o hQ₁o
      (fun z hz => (huniv₁ ▸ mem_univ z : z ∈ P₁ ∪ Q₁ ∪ (τ ∪ D)).elim id
        (fun h => absurd h (Set.disjoint_left.1 hP₂Γ₁ hz)))
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, h1, h2⟩; exact Set.disjoint_left.1 hP₁Q₁ h1 h2)
  have hP₁case : P₁ ⊆ P₂ ∨ P₁ ⊆ Q₂ :=
    isPreconnected_iff_subset_of_disjoint.1 hP₁c.isPreconnected P₂ Q₂ hP₂o hQ₂o
      (fun z hz => (huniv₂ ▸ mem_univ z : z ∈ P₂ ∪ Q₂ ∪ (τ' ∪ D)).elim id
        (fun h => absurd h (Set.disjoint_left.1 hP₁Γ₂ hz)))
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, h1, h2⟩; exact Set.disjoint_left.1 hP₂Q₂ h1 h2)
  have hP₁P₂ : Disjoint P₁ P₂ := by
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hP₂P₁ : P₂ ⊆ P₁ := hP₂case.resolve_right
      (fun h => Set.disjoint_left.1 hP₁Q₁ hz.1 (h hz.2))
    have hP₁P₂' : P₁ ⊆ P₂ := hP₁case.resolve_right
      (fun h => Set.disjoint_left.1 hP₂Q₂ hz.2 (h hz.1))
    have heqP : P₁ = P₂ := Set.Subset.antisymm hP₁P₂' hP₂P₁
    have heqfr : τ ∪ D = τ' ∪ D := by rw [← hfrP₁, ← hfrP₂, heqP]
    obtain ⟨z', hz'⟩ := (isConnected_arcEndC_diff_endpoints hτarc).nonempty
    rcases (heqfr ▸ (Or.inl hz'.1) : z' ∈ τ' ∪ D) with h | h
    · exact hz'.2 (hττ'int ▸ (⟨hz'.1, h⟩ : z' ∈ τ ∩ τ'))
    · exact hz'.2 (hDτ ▸ (⟨h, hz'.1⟩ : z' ∈ D ∩ τ))
  refine ⟨P₁, P₂, Ω ∩ Q₁ ∩ Q₂, hP₁o, hP₂o, (hΩo.inter hQ₁o).inter hQ₂o, hP₁c, hP₂c, hP₁Ω, hP₂Ω,
    hP₁P₂, ?_, ?_, hfrP₁, hfrP₂, ?_⟩
  · exact Set.disjoint_left.2 fun z hz1 hz2 => Set.disjoint_left.1 hP₁Q₁ hz1 hz2.1.2
  · exact Set.disjoint_left.2 fun z hz1 hz2 => Set.disjoint_left.1 hP₂Q₂ hz1 hz2.2
  · ext z
    simp only [mem_diff, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨hzΩ, hzD⟩
      have hzτ : z ∉ τ := fun h => Set.disjoint_left.1 hΩfr hzΩ (hτsub h)
      have hzτ' : z ∉ τ' := fun h => Set.disjoint_left.1 hΩfr hzΩ (hτ'sub h)
      have hz1 : z ∈ P₁ ∪ Q₁ := (huniv₁ ▸ mem_univ z : z ∈ P₁ ∪ Q₁ ∪ (τ ∪ D)).elim id
        (fun h => absurd h (by simp [hzτ, hzD]))
      have hz2 : z ∈ P₂ ∪ Q₂ := (huniv₂ ▸ mem_univ z : z ∈ P₂ ∪ Q₂ ∪ (τ' ∪ D)).elim id
        (fun h => absurd h (by simp [hzτ', hzD]))
      rcases hz1 with h1 | h1
      · exact Or.inl (Or.inl h1)
      · rcases hz2 with h2 | h2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨⟨hzΩ, h1⟩, h2⟩
    · rintro ((h | h) | ⟨⟨hΩ', hQ1⟩, hQ2⟩)
      · exact ⟨hP₁Ω h, fun hD => Set.disjoint_left.1 hP₁Γ₁ h (Or.inr hD)⟩
      · exact ⟨hP₂Ω h, fun hD => Set.disjoint_left.1 hP₂Γ₂ h (Or.inr hD)⟩
      · exact ⟨hΩ', fun hD => Set.disjoint_left.1 hQ₁Γ₁ hQ1 (Or.inr hD)⟩


theorem cos_le_cos_of_abs_le_abs {θ φ : ℝ} (hθ : |θ| ≤ π) (h : |φ| ≤ |θ|) :
    Real.cos θ ≤ Real.cos φ := by
  rw [← Real.cos_abs θ, ← Real.cos_abs φ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) hθ h

theorem S2_disc_split {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsOpen (unitDisc ∩ ball z₀ ρ) ∧ IsConnected (unitDisc ∩ ball z₀ ρ) ∧
      IsOpen (unitDisc \ closedBall z₀ ρ) ∧ IsConnected (unitDisc \ closedBall z₀ ρ) ∧
      unitDisc \ (unitDisc ∩ sphere z₀ ρ) =
        (unitDisc ∩ ball z₀ ρ) ∪ (unitDisc \ closedBall z₀ ρ) ∧
      ∀ y ∈ unitDisc ∩ sphere z₀ ρ, ∃ N : Set ℂ, IsOpen N ∧ y ∈ N ∧ N ⊆ unitDisc ∧
        IsConnected (N ∩ (unitDisc ∩ ball z₀ ρ)) ∧
        IsConnected (N ∩ (unitDisc \ closedBall z₀ ρ)) := by
  have hDconv : Convex ℝ (unitDisc ∩ ball z₀ ρ) := (convex_ball 0 1).inter (convex_ball z₀ ρ)
  have hDopen : IsOpen (unitDisc ∩ ball z₀ ρ) := isOpen_ball.inter isOpen_ball
  have hDne : (unitDisc ∩ ball z₀ ρ).Nonempty := by
    refine ⟨(1 - ρ / 2) * z₀, ?_, ?_⟩
    · rw [unitDisc, mem_ball_zero_iff]
      have hc : (1 : ℂ) - (ρ : ℂ) / 2 = ((1 - ρ / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, norm_mul, hz₀, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · rw [mem_ball, dist_eq_norm]
      have : (1 - ρ / 2) * z₀ - z₀ = (-(ρ / 2) : ℝ) * z₀ := by push_cast; ring
      rw [this, norm_mul, hz₀, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      linarith
  have hDconn : IsConnected (unitDisc ∩ ball z₀ ρ) := hDconv.isConnected hDne
  have hEopen : IsOpen (unitDisc \ closedBall z₀ ρ) := isOpen_ball.sdiff isClosed_closedBall
  -- The "safe half" H, entirely inside Eρ.
  set H : Set ℂ := unitDisc ∩ {w : ℂ | (w * conj z₀).re ≤ 0} with hH_def
  have hlin : IsLinearMap ℝ (fun w : ℂ => (w * conj z₀).re) := by
    constructor
    · intro w1 w2; simp [add_mul, Complex.add_re]
    · intro c w
      show (((c : ℂ) * w) * conj z₀).re = c * (w * conj z₀).re
      rw [show (c : ℂ) * w * conj z₀ = (c : ℂ) * (w * conj z₀) by ring]
      exact Complex.re_ofReal_mul c (w * conj z₀)
  have hHconv : Convex ℝ H := (convex_ball 0 1).inter (convex_halfSpace_le hlin 0)
  have hHsubE : H ⊆ unitDisc \ closedBall z₀ ρ := by
    rintro w ⟨hw1, hw2⟩
    simp only [Set.mem_setOf_eq] at hw2
    refine ⟨hw1, ?_⟩
    simp only [mem_closedBall, dist_eq_norm, not_le]
    have hnorm : ‖w - z₀‖ ^ 2 = ‖w‖ ^ 2 - 2 * (w * conj z₀).re + ‖z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_sub]
      ring
    have hz₀sq : ‖z₀‖ ^ 2 = 1 := by rw [hz₀]; norm_num
    have hge1 : (1 : ℝ) ≤ ‖w - z₀‖ ^ 2 := by nlinarith [sq_nonneg (‖w‖ : ℝ), hw2, hz₀sq]
    have hge1' : (1 : ℝ) ≤ ‖w - z₀‖ := by
      have := Real.sqrt_le_sqrt hge1
      rwa [Real.sqrt_one, Real.sqrt_sq (norm_nonneg _)] at this
    linarith
  have hHne : H.Nonempty := ⟨0, by
    constructor
    · rw [unitDisc, mem_ball_zero_iff, norm_zero]; exact one_pos
    · show (0 * conj z₀).re ≤ 0; simp⟩
  -- For z ∈ Eρ, an arc at fixed radius connecting z to H.
  have harc : ∀ z ∈ unitDisc \ closedBall z₀ ρ, ∃ S : Set ℂ, IsConnected S ∧
      S ⊆ unitDisc \ closedBall z₀ ρ ∧ z ∈ S ∧ (S ∩ H).Nonempty := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨H, hHconv.isConnected hHne, hHsubE, hzH, ⟨z, hzH, hzH⟩⟩
    · have hzH' : 0 < (z * conj z₀).re :=
        not_le.mp (fun h => hzH ⟨hz.1, h⟩)
      have hzne : z ≠ 0 := by
        rintro rfl; simp at hzH'
      set φ : ℝ := Complex.arg (z * conj z₀) with hφ_def
      have hφabs : |φ| < π / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hzH')
      set ψ : ℝ := if 0 ≤ φ then (π / 2 : ℝ) else -(π / 2) with hψ_def
      have hψabs : |ψ| = π / 2 := by
        rw [hψ_def]; split <;> simp [abs_of_pos, abs_of_neg, Real.pi_pos]
      have hsign : (0 ≤ φ ∧ 0 ≤ ψ) ∨ (φ ≤ 0 ∧ ψ ≤ 0) := by
        rw [hψ_def]; split
        · exact Or.inl ⟨by assumption, by positivity⟩
        · exact Or.inr ⟨(not_le.mp (by assumption)).le, by linarith [Real.pi_pos]⟩
      have hz₀conj : conj z₀ * z₀ = 1 := by
        rw [mul_comm, Complex.mul_conj]
        norm_cast
        rw [Complex.normSq_eq_norm_sq, hz₀]; norm_num
      have hz₀conj' : z₀ * conj z₀ = 1 := by rw [mul_comm]; exact hz₀conj
      have hnormeq : ‖z * conj z₀‖ = ‖z‖ := by
        rw [norm_mul, Complex.norm_conj, hz₀, mul_one]
      have hkey : (‖z‖ : ℂ) * Complex.exp ((φ : ℂ) * I) = z * conj z₀ := by
        rw [← hnormeq, hφ_def]; exact Complex.norm_mul_exp_arg_mul_I (z * conj z₀)
      set θfun : ℝ → ℝ := fun t => (1 - t) * φ + t * ψ with hθfun_def
      set γ : ℝ → ℂ := fun t => (‖z‖ : ℂ) * z₀ * Complex.exp ((θfun t : ℂ) * I) with hγ_def
      have hθ0 : θfun 0 = φ := by simp [hθfun_def]
      have hθ1 : θfun 1 = ψ := by simp [hθfun_def]
      have hz0eq : γ 0 = z := by
        have e1 : γ 0 = z₀ * ((‖z‖ : ℂ) * Complex.exp ((φ : ℂ) * I)) := by
          rw [hγ_def]; simp only [hθ0]; ring
        rw [e1, hkey]; linear_combination z * hz₀conj
      have hRe : ∀ θ : ℝ, ((‖z‖ : ℂ) * z₀ * Complex.exp ((θ : ℂ) * I) * conj z₀).re
          = ‖z‖ * Real.cos θ := by
        intro θ
        rw [show (‖z‖ : ℂ) * z₀ * Complex.exp ((θ : ℂ) * I) * conj z₀
            = (‖z‖ : ℂ) * (Complex.exp ((θ : ℂ) * I) * (z₀ * conj z₀)) by ring, hz₀conj', mul_one]
        rw [Complex.mul_re]
        rw [Complex.exp_ofReal_mul_I_re]
        simp [Complex.exp_ofReal_mul_I]
      have hγ1H : γ 1 ∈ H := by
        constructor
        · rw [unitDisc, mem_ball_zero_iff]
          rw [hγ_def]
          simp only
          rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hzne), hz₀, mul_one]
          exact (mem_ball_zero_iff.mp hz.1 : ‖z‖ < 1)
        · show (γ 1 * conj z₀).re ≤ 0
          rw [hγ_def]
          simp only
          rw [hRe, hθ1]
          rcases (by rw [hψ_def]; split <;> simp : ψ = π / 2 ∨ ψ = -(π / 2)) with h | h <;>
            simp [h, Real.cos_pi_div_two]
      have hφrange := abs_lt.mp hφabs
      have hψrange := abs_le.mp hψabs.le
      have hEsafe : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ unitDisc \ closedBall z₀ ρ := by
        intro t ht
        have hnormγ : ‖γ t‖ = ‖z‖ := by
          rw [hγ_def]
          simp only
          rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hzne), hz₀, mul_one]
        have hθabs : |φ| ≤ |θfun t| := by
          rw [hθfun_def]
          simp only
          rcases hsign with ⟨hφ0, hψ0⟩ | ⟨hφ0, hψ0⟩
          · rw [abs_of_nonneg hφ0,
              abs_of_nonneg (by nlinarith [ht.1, ht.2] : (0:ℝ) ≤ (1 - t) * φ + t * ψ)]
            nlinarith [ht.1, ht.2, hψabs, abs_of_nonneg hψ0, hφrange.2]
          · rw [abs_of_nonpos hφ0,
              abs_of_nonpos (by nlinarith [ht.1, ht.2] : (1 - t) * φ + t * ψ ≤ 0)]
            nlinarith [ht.1, ht.2, hψabs, abs_of_nonpos hψ0, hφrange.1]
        have hπbound : -(π / 2) ≤ θfun t ∧ θfun t ≤ π / 2 := by
          rw [hθfun_def]
          simp only
          constructor <;>
            nlinarith [ht.1, ht.2, hφrange.1, hφrange.2, hψrange.1, hψrange.2]
        have hcos : Real.cos (θfun t) ≤ Real.cos φ :=
          cos_le_cos_of_abs_le_abs
            ((abs_le.mpr hπbound).trans (by linarith [Real.pi_pos]))
            hθabs
        refine ⟨by rw [unitDisc, mem_ball_zero_iff, hnormγ]; exact mem_ball_zero_iff.mp hz.1, ?_⟩
        simp only [mem_closedBall, dist_eq_norm, not_le]
        have hnorm2 : ‖γ t - z₀‖ ^ 2 = ‖z‖ ^ 2 - 2 * ‖z‖ * Real.cos (θfun t) + 1 := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
            Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
            hnormγ, hz₀]
          rw [show γ t = (‖z‖ : ℂ) * z₀ * Complex.exp ((θfun t : ℂ) * I) from rfl, hRe]
          ring
        have hzdist2 : ‖z - z₀‖ ^ 2 = ‖z‖ ^ 2 - 2 * ‖z‖ * Real.cos φ + 1 := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
            Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hz₀]
          have : (z * conj z₀).re = ‖z‖ * Real.cos φ := by
            rw [← hkey, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
            simp [Complex.exp_ofReal_mul_I]
          rw [this]; ring
        have hzE : ρ < ‖z - z₀‖ := by
          have h2 := hz.2; simp only [mem_closedBall, dist_eq_norm, not_le] at h2
          exact h2
        have hge : ‖z - z₀‖ ^ 2 ≤ ‖γ t - z₀‖ ^ 2 := by
          rw [hnorm2, hzdist2]; nlinarith [hcos, norm_nonneg z]
        have hzE2 : ρ ^ 2 < ‖z - z₀‖ ^ 2 := by
          nlinarith [hzE, norm_nonneg (z - z₀), hρ0]
        nlinarith [hge, hzE2, norm_nonneg (γ t - z₀), hρ0]
      refine ⟨γ '' Icc 0 1, ?_, ?_, ⟨0, left_mem_Icc.mpr zero_le_one, hz0eq⟩,
        ⟨γ 1, ⟨1, right_mem_Icc.mpr zero_le_one, rfl⟩, hγ1H⟩⟩
      · exact (isConnected_Icc zero_le_one).image _
          (by fun_prop : Continuous γ).continuousOn
      · rintro _ ⟨t, ht, rfl⟩; exact hEsafe t ht
  have hEconn : IsConnected (unitDisc \ closedBall z₀ ρ) := by
    set Sc : ↥(unitDisc \ closedBall z₀ ρ) → Set ℂ := fun z => (harc z.1 z.2).choose with hSc_def
    have hScSpec : ∀ z : ↥(unitDisc \ closedBall z₀ ρ),
        IsConnected (Sc z) ∧ Sc z ⊆ unitDisc \ closedBall z₀ ρ ∧ z.1 ∈ Sc z ∧
          (Sc z ∩ H).Nonempty :=
      fun z => (harc z.1 z.2).choose_spec
    set s : ↥(unitDisc \ closedBall z₀ ρ) → Set ℂ := fun z => H ∪ Sc z with hs_def
    obtain ⟨h0, hh0⟩ := hHne
    have hinter : (⋂ z, s z).Nonempty := ⟨h0, by
      rw [Set.mem_iInter]; intro z; exact Or.inl hh0⟩
    have hpre : ∀ z, IsPreconnected (s z) := fun z => by
      have hmeet : (H ∩ Sc z).Nonempty := by
        rw [Set.inter_comm]; exact (hScSpec z).2.2.2
      exact IsPreconnected.union' hmeet hHconv.isPreconnected (hScSpec z).1.isPreconnected
    have hunion_pre : IsPreconnected (⋃ z, s z) := isPreconnected_iUnion hinter hpre
    have hunion_eq : (⋃ z, s z) = unitDisc \ closedBall z₀ ρ := by
      ext w
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨z, hw | hw⟩
        · exact hHsubE hw
        · exact (hScSpec z).2.1 hw
      · intro hw
        exact ⟨⟨w, hw⟩, Or.inr (hScSpec ⟨w, hw⟩).2.2.1⟩
    rw [hunion_eq] at hunion_pre
    exact ⟨⟨h0, hHsubE hh0⟩, hunion_pre⟩
  have hUopen : IsOpen unitDisc := isOpen_ball
  have hsplit_eq : unitDisc \ (unitDisc ∩ sphere z₀ ρ) =
      (unitDisc ∩ ball z₀ ρ) ∪ (unitDisc \ closedBall z₀ ρ) := by
    ext w
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_union, Metric.mem_ball,
      Metric.mem_closedBall, Metric.mem_sphere]
    constructor
    · rintro ⟨hw1, h⟩
      push_neg at h
      rcases lt_trichotomy (dist w z₀) ρ with hlt | heq | hgt
      · exact Or.inl ⟨hw1, hlt⟩
      · exact absurd heq (h hw1)
      · exact Or.inr ⟨hw1, not_le.mpr hgt⟩
    · rintro (⟨hw1, hlt⟩ | ⟨hw1, hgt⟩)
      · exact ⟨hw1, fun h' => hlt.ne h'.2⟩
      · exact ⟨hw1, fun h' => (not_le.mp hgt).ne' h'.2⟩
  have hlocal : ∀ y ∈ unitDisc ∩ sphere z₀ ρ, ∃ N : Set ℂ, IsOpen N ∧ y ∈ N ∧ N ⊆ unitDisc ∧
      IsConnected (N ∩ (unitDisc ∩ ball z₀ ρ)) ∧
      IsConnected (N ∩ (unitDisc \ closedBall z₀ ρ)) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_sphere, dist_eq_norm] at hy2
    set θ₀ : ℝ := Complex.arg (y - z₀) with hθ₀_def
    set c : ℂ := Complex.exp ((θ₀ : ℂ) * I) with hc_def
    have hcne : c ≠ 0 := Complex.exp_ne_zero _
    set Φ : ℝ × ℝ → ℂ := fun p => z₀ + (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + Real.sin p.2 * I) * c
      with hΦ_def
    have hΦcont : Continuous Φ := by fun_prop
    have hΦeq : ∀ p : ℝ × ℝ, Φ p = z₀ + Complex.polarCoord.symm p * c := by
      intro p; simp only [hΦ_def, Complex.polarCoord_symm_apply]
    have hΦnorm : ∀ p : ℝ × ℝ, 0 < p.1 → ‖Φ p - z₀‖ = p.1 := by
      intro p hp1
      have he : Φ p - z₀ = (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + Real.sin p.2 * I) * c := by
        simp only [hΦ_def]; ring
      have h1 : ‖(Real.cos p.2 : ℂ) + Real.sin p.2 * I‖ = 1 := by
        rw [← Complex.exp_ofReal_mul_I]; exact Complex.norm_exp_ofReal_mul_I p.2
      have h2 : ‖c‖ = 1 := by rw [hc_def]; exact Complex.norm_exp_ofReal_mul_I θ₀
      rw [he, norm_mul, norm_mul, h1, h2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hp1, mul_one, mul_one]
    have hkey_y : (ρ : ℂ) * c = y - z₀ := by
      have h := Complex.norm_mul_exp_arg_mul_I (y - z₀)
      rw [hy2] at h
      exact h
    have hΦρ0 : Φ (ρ, 0) = y := by
      have e1 : Φ (ρ, 0) = z₀ + (ρ : ℂ) * c := by
        simp only [hΦ_def, Real.cos_zero, Real.sin_zero]; push_cast; ring
      rw [e1, hkey_y]; ring
    have hnhds : {p : ℝ × ℝ | Φ p ∈ unitDisc} ∈ nhds (ρ, (0 : ℝ)) := by
      apply hΦcont.continuousAt.preimage_mem_nhds
      rw [hΦρ0]
      exact hUopen.mem_nhds hy1
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
    set δ : ℝ := min (ε / 2) (ρ / 2) with hδ_def
    set η : ℝ := min (ε / 2) (π / 2) with hη_def
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hη0 : 0 < η := lt_min (by linarith) (by linarith [Real.pi_pos])
    have hδρ : δ < ρ := lt_of_le_of_lt (min_le_right (ε / 2) (ρ / 2)) (by linarith)
    have hηπ : η < π := lt_of_le_of_lt (min_le_right (ε / 2) (π / 2)) (by linarith [Real.pi_pos])
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    have hηε : η ≤ ε / 2 := min_le_left _ _
    set rect : Set (ℝ × ℝ) := Ioo (ρ - δ) (ρ + δ) ×ˢ Ioo (-η) η with hrect_def
    set rectD : Set (ℝ × ℝ) := Ioo (ρ - δ) ρ ×ˢ Ioo (-η) η with hrectD_def
    set rectE : Set (ℝ × ℝ) := Ioo ρ (ρ + δ) ×ˢ Ioo (-η) η with hrectE_def
    have hrectD_sub_rect : rectD ⊆ rect :=
      fun p hp => ⟨⟨hp.1.1, lt_trans hp.1.2 (by linarith : ρ < ρ + δ)⟩, hp.2⟩
    have hrectE_sub_rect : rectE ⊆ rect :=
      fun p hp => ⟨⟨lt_trans (by linarith : ρ - δ < ρ) hp.1.1, hp.1.2⟩, hp.2⟩
    have hrect_open : IsOpen rect := isOpen_Ioo.prod isOpen_Ioo
    have hrect_sub : rect ⊆ Complex.polarCoord.target := by
      rw [Complex.polarCoord_target]
      rintro ⟨s, φ⟩ ⟨hs, hφ⟩
      refine ⟨by simp only [Set.mem_Ioi]; linarith [hs.1], ?_⟩
      exact ⟨by linarith [hφ.1, hηπ], by linarith [hφ.2, hηπ]⟩
    have hMopen : IsOpen (Complex.polarCoord.symm '' rect) :=
      Complex.polarCoord.symm.isOpen_image_of_subset_source hrect_open hrect_sub
    have hN_eq : Φ '' rect = (fun w : ℂ => z₀ + w * c) '' (Complex.polarCoord.symm '' rect) := by
      rw [← Set.image_comp,
        show Φ = (fun w : ℂ => z₀ + w * c) ∘ Complex.polarCoord.symm from funext hΦeq]
    have hNopen : IsOpen (Φ '' rect) := by
      rw [hN_eq]
      exact ((Homeomorph.mulRight₀ c hcne).trans (Homeomorph.addLeft z₀)).isOpenMap _ hMopen
    have hρ0mem : (ρ, (0:ℝ)) ∈ rect := ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hyN : y ∈ Φ '' rect := ⟨(ρ, 0), hρ0mem, hΦρ0⟩
    have hrect_ball : rect ⊆ Metric.ball (ρ, (0 : ℝ)) ε := by
      rintro ⟨s, φ⟩ ⟨hs, hφ⟩
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      refine ⟨abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
        abs_lt.mpr ⟨by linarith [hφ.1], by linarith [hφ.2]⟩⟩
    have hNsub : Φ '' rect ⊆ unitDisc := by
      rintro w ⟨p, hp, rfl⟩
      exact hεsub (hrect_ball hp)
    have hpieceD_eq : Φ '' rect ∩ (unitDisc ∩ ball z₀ ρ) = Φ '' rectD := by
      ext w
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, _, hw2⟩
        rw [mem_ball, dist_eq_norm] at hw2
        have hp1pos : 0 < p.1 := by linarith [hp.1.1, hδρ]
        rw [hΦnorm p hp1pos] at hw2
        exact ⟨p, ⟨⟨hp.1.1, hw2⟩, hp.2⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        have hpr : p ∈ rect := hrectD_sub_rect hp
        have hp1pos : 0 < p.1 := by linarith [hp.1.1, hδρ]
        refine ⟨⟨p, hpr, rfl⟩, hNsub ⟨p, hpr, rfl⟩, ?_⟩
        rw [mem_ball, dist_eq_norm, hΦnorm p hp1pos]
        exact hp.1.2
    have hpieceE_eq : Φ '' rect ∩ (unitDisc \ closedBall z₀ ρ) = Φ '' rectE := by
      ext w
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, _, hw2⟩
        rw [mem_closedBall, dist_eq_norm, not_le] at hw2
        have hp1pos : 0 < p.1 := by linarith [hp.1.1, hδρ]
        rw [hΦnorm p hp1pos] at hw2
        exact ⟨p, ⟨⟨hw2, hp.1.2⟩, hp.2⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        have hpr : p ∈ rect := hrectE_sub_rect hp
        have hp1pos : 0 < p.1 := by linarith [hp.1.1, hρ0]
        refine ⟨⟨p, hpr, rfl⟩, hNsub ⟨p, hpr, rfl⟩, ?_⟩
        rw [mem_closedBall, dist_eq_norm, hΦnorm p hp1pos, not_le]
        exact hp.1.1
    have hrectD_conn : IsConnected rectD :=
      (isConnected_Ioo (by linarith : ρ - δ < ρ)).prod
        (isConnected_Ioo (by linarith : -η < η))
    have hrectE_conn : IsConnected rectE :=
      (isConnected_Ioo (by linarith : ρ < ρ + δ)).prod
        (isConnected_Ioo (by linarith : -η < η))
    have hDconn' : IsConnected (Φ '' rect ∩ (unitDisc ∩ ball z₀ ρ)) := by
      rw [hpieceD_eq]; exact hrectD_conn.image Φ hΦcont.continuousOn
    have hEconn' : IsConnected (Φ '' rect ∩ (unitDisc \ closedBall z₀ ρ)) := by
      rw [hpieceE_eq]; exact hrectE_conn.image Φ hΦcont.continuousOn
    exact ⟨Φ '' rect, hNopen, hyN, hNsub, hDconn', hEconn'⟩
  exact ⟨hDopen, hDconn, hEopen, hEconn, hsplit_eq, hlocal⟩


theorem S3_crosscut_splits {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hJ : IsJordanCurve (toExt (frontier Ω)))
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {σ τ τ' : Set ℂ} {a b : ℂ} (hab : a ≠ b)
    (hσ : σ = f '' (unitDisc ∩ sphere z₀ ρ))
    (hτarc : IsArcEndC τ a b) (hτ'arc : IsArcEndC τ' a b)
    (hττ'union : τ ∪ τ' = frontier Ω) (hττ'int : τ ∩ τ' = {a, b})
    (hDarc : IsArcEndC (σ ∪ {a, b}) a b)
    (hDτ : (σ ∪ {a, b}) ∩ τ = {a, b}) (hDτ' : (σ ∪ {a, b}) ∩ τ' = {a, b}) :
    ∃ I₁ I₂ : Set ℂ, IsOpen I₁ ∧ IsOpen I₂ ∧ IsConnected I₁ ∧ IsConnected I₂ ∧ Disjoint I₁ I₂ ∧
      frontier I₁ = τ ∪ σ ∪ {a, b} ∧ frontier I₂ = τ' ∪ σ ∪ {a, b} ∧ Ω \ σ = I₁ ∪ I₂ ∧
      ((f '' (unitDisc ∩ ball z₀ ρ) = I₁ ∧ f '' (unitDisc \ closedBall z₀ ρ) = I₂) ∨
        (f '' (unitDisc ∩ ball z₀ ρ) = I₂ ∧ f '' (unitDisc \ closedBall z₀ ρ) = I₁)) := by
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  have hint_a : a ∈ τ ∩ τ' := by rw [hττ'int]; simp
  have hint_b : b ∈ τ ∩ τ' := by rw [hττ'int]; simp
  have haτ : a ∈ τ := hint_a.1
  have hbτ : b ∈ τ := hint_b.1
  have hτsub : τ ⊆ frontier Ω := by rw [← hττ'union]; exact subset_union_left
  have haΩ : a ∉ Ω := fun h => Set.disjoint_left.1 hΩfr h (hτsub haτ)
  have hbΩ : b ∉ Ω := fun h => Set.disjoint_left.1 hΩfr h (hτsub hbτ)
  have hσΩ : σ ⊆ Ω := by
    rw [hσ, ← hf.2.2]; exact Set.image_mono Set.inter_subset_left
  have hDΩ : (σ ∪ {a, b}) \ {a, b} ⊆ Ω := by
    rintro z ⟨hz1, hz2⟩
    rcases hz1 with h | h
    · exact hσΩ h
    · exact absurd h hz2
  obtain ⟨I₁, I₂, W, hI₁o, hI₂o, hWo, hI₁c, hI₂c, hI₁Ω, hI₂Ω, hI₁I₂, hI₁W, hI₂W, hfrI₁0, hfrI₂0,
    hunion⟩ :=
    S1_pieces_identification hΩo hΩc hΩb hJ hab hτarc hτ'arc hττ'union hττ'int hDarc hDτ hDτ' hDΩ
  have hfrI₁ : frontier I₁ = τ ∪ σ ∪ {a, b} := by rw [hfrI₁0, union_assoc]
  have hfrI₂ : frontier I₂ = τ' ∪ σ ∪ {a, b} := by rw [hfrI₂0, union_assoc]
  have hzab : ∀ z ∈ Ω, z ∉ ({a, b} : Set ℂ) := by
    rintro z hzΩ (rfl | rfl)
    · exact haΩ hzΩ
    · exact hbΩ hzΩ
  have hΩDσ : Ω \ (σ ∪ {a, b}) = Ω \ σ := by
    ext z
    simp only [mem_diff, mem_union, not_or]
    constructor
    · rintro ⟨hzΩ, hzσ, -⟩; exact ⟨hzΩ, hzσ⟩
    · rintro ⟨hzΩ, hzσ⟩; exact ⟨hzΩ, hzσ, hzab z hzΩ⟩
  have hunion' : Ω \ σ = I₁ ∪ I₂ ∪ W := by rw [← hΩDσ]; exact hunion
  obtain ⟨hDρopen, hDρconn, hEρopen, hEρconn, hsplit_eq, -⟩ := S2_disc_split hz₀ hρ0 hρ1
  have hF₁c : IsConnected (f '' (unitDisc ∩ ball z₀ ρ)) :=
    hDρconn.image f (hf.1.continuousOn.mono Set.inter_subset_left)
  have hF₂c : IsConnected (f '' (unitDisc \ closedBall z₀ ρ)) :=
    hEρconn.image f (hf.1.continuousOn.mono Set.diff_subset)
  have hDρEρ_disj : (unitDisc ∩ ball z₀ ρ) ∩ (unitDisc \ closedBall z₀ ρ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_diff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hz1⟩, -, hz2⟩
    exact hz2 (ball_subset_closedBall hz1)
  have hF₁F₂disj : Disjoint (f '' (unitDisc ∩ ball z₀ ρ)) (f '' (unitDisc \ closedBall z₀ ρ)) := by
    rw [Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hf.2.1 Set.inter_subset_left Set.diff_subset, hDρEρ_disj,
      Set.image_empty]
  have hFunion : Ω \ σ = f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) := by
    rw [← hf.2.2, hσ, ← Set.InjOn.image_diff_subset hf.2.1 Set.inter_subset_left, hsplit_eq,
      Set.image_union]
  have h3way : ∀ S : Set ℂ, IsConnected S → S ⊆ I₁ ∪ I₂ ∪ W → S ⊆ I₁ ∨ S ⊆ I₂ ∨ S ⊆ W := by
    intro S hSc hSsub
    rcases isPreconnected_iff_subset_of_disjoint.1 hSc.isPreconnected I₁ (I₂ ∪ W) hI₁o
        (hI₂o.union hWo) (by rwa [← union_assoc])
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨-, h1, h2 | h2⟩
          · exact Set.disjoint_left.1 hI₁I₂ h1 h2
          · exact Set.disjoint_left.1 hI₁W h1 h2) with h | h
    · exact Or.inl h
    · rcases isPreconnected_iff_subset_of_disjoint.1 hSc.isPreconnected I₂ W hI₂o hWo h
          (by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨-, h1, h2⟩
            exact Set.disjoint_left.1 hI₂W h1 h2) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hF₁subIW : f '' (unitDisc ∩ ball z₀ ρ) ⊆ I₁ ∪ I₂ ∪ W := by
    rw [← hunion', hFunion]; exact Set.subset_union_left
  have hF₂subIW : f '' (unitDisc \ closedBall z₀ ρ) ⊆ I₁ ∪ I₂ ∪ W := by
    rw [← hunion', hFunion]; exact Set.subset_union_right
  have hcombine : I₁ ∪ I₂ ∪ W = f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) :=
    hunion'.symm.trans hFunion
  obtain ⟨p₁, hp₁⟩ := hI₁c.nonempty
  obtain ⟨p₂, hp₂⟩ := hI₂c.nonempty
  have hI₁sub : I₁ ⊆ I₁ ∪ I₂ ∪ W := fun z hz => Or.inl (Or.inl hz)
  have hI₂sub : I₂ ⊆ I₁ ∪ I₂ ∪ W := fun z hz => Or.inl (Or.inr hz)
  rcases h3way _ hF₁c hF₁subIW with hc1 | hc1 | hc1 <;>
    rcases h3way _ hF₂c hF₂subIW with hc2 | hc2 | hc2
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ I₁ := by rw [hcombine]; exact union_subset hc1 hc2
    exact Set.disjoint_left.1 hI₁I₂.symm hp₂ (hsub (hI₂sub hp₂))
  · -- F₁ ⊆ I₁, F₂ ⊆ I₂: the good case
    have hWempty : W = ∅ := by
      have hsub : I₁ ∪ I₂ ∪ W ⊆ I₁ ∪ I₂ := by rw [hcombine]; exact union_subset_union hc1 hc2
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rcases hsub (Or.inr hz : z ∈ I₁ ∪ I₂ ∪ W) with h | h
      · exact Set.disjoint_left.1 hI₁W h hz
      · exact Set.disjoint_left.1 hI₂W h hz
    have hI₁eq : f '' (unitDisc ∩ ball z₀ ρ) = I₁ := by
      refine Set.Subset.antisymm hc1 fun z hz => ?_
      rcases (hcombine ▸ hI₁sub hz :
          z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ)) with h | h
      · exact h
      · exact absurd (hc2 h) (Set.disjoint_left.1 hI₁I₂ hz)
    have hI₂eq : f '' (unitDisc \ closedBall z₀ ρ) = I₂ := by
      refine Set.Subset.antisymm hc2 fun z hz => ?_
      rcases (hcombine ▸ hI₂sub hz :
          z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ)) with h | h
      · exact absurd (hc1 h) (Set.disjoint_left.1 hI₁I₂.symm hz)
      · exact h
    exact ⟨I₁, I₂, hI₁o, hI₂o, hI₁c, hI₂c, hI₁I₂, hfrI₁, hfrI₂,
      by rw [hunion', hWempty, union_empty], Or.inl ⟨hI₁eq, hI₂eq⟩⟩
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ I₁ ∪ W := by rw [hcombine]; exact union_subset_union hc1 hc2
    rcases hsub (hI₂sub hp₂) with h | h
    · exact Set.disjoint_left.1 hI₁I₂.symm hp₂ h
    · exact Set.disjoint_left.1 hI₂W hp₂ h
  · -- F₁ ⊆ I₂, F₂ ⊆ I₁: the good case, swapped
    have hWempty : W = ∅ := by
      have hsub : I₁ ∪ I₂ ∪ W ⊆ I₁ ∪ I₂ := by
        rw [hcombine, union_comm (f '' (unitDisc ∩ ball z₀ ρ))]
        exact union_subset_union hc2 hc1
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rcases hsub (Or.inr hz : z ∈ I₁ ∪ I₂ ∪ W) with h | h
      · exact Set.disjoint_left.1 hI₁W h hz
      · exact Set.disjoint_left.1 hI₂W h hz
    have hI₁eq : f '' (unitDisc \ closedBall z₀ ρ) = I₁ := by
      refine Set.Subset.antisymm hc2 fun z hz => ?_
      rcases (hcombine ▸ hI₁sub hz :
          z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ)) with h | h
      · exact absurd (hc1 h) (Set.disjoint_left.1 hI₁I₂ hz)
      · exact h
    have hI₂eq : f '' (unitDisc ∩ ball z₀ ρ) = I₂ := by
      refine Set.Subset.antisymm hc1 fun z hz => ?_
      rcases (hcombine ▸ hI₂sub hz :
          z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ)) with h | h
      · exact h
      · exact absurd (hc2 h) (Set.disjoint_left.1 hI₁I₂.symm hz)
    exact ⟨I₁, I₂, hI₁o, hI₂o, hI₁c, hI₂c, hI₁I₂, hfrI₁, hfrI₂,
      by rw [hunion', hWempty, union_empty], Or.inr ⟨hI₂eq, hI₁eq⟩⟩
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ I₂ := by rw [hcombine]; exact union_subset hc1 hc2
    exact Set.disjoint_left.1 hI₁I₂ hp₁ (hsub (hI₁sub hp₁))
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ I₂ ∪ W := by rw [hcombine]; exact union_subset_union hc1 hc2
    rcases hsub (hI₁sub hp₁) with h | h
    · exact Set.disjoint_left.1 hI₁I₂ hp₁ h
    · exact Set.disjoint_left.1 hI₁W hp₁ h
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ W ∪ I₁ := by rw [hcombine]; exact union_subset_union hc1 hc2
    rcases hsub (hI₂sub hp₂) with h | h
    · exact Set.disjoint_left.1 hI₂W hp₂ h
    · exact Set.disjoint_left.1 hI₁I₂.symm hp₂ h
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ W ∪ I₂ := by rw [hcombine]; exact union_subset_union hc1 hc2
    rcases hsub (hI₁sub hp₁) with h | h
    · exact Set.disjoint_left.1 hI₁W hp₁ h
    · exact Set.disjoint_left.1 hI₁I₂ hp₁ h
  · exfalso
    have hsub : I₁ ∪ I₂ ∪ W ⊆ W := by rw [hcombine]; exact union_subset hc1 hc2
    exact Set.disjoint_left.1 hI₁W hp₁ (hsub (hI₁sub hp₁))

theorem S4_loop_splits {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hJ : IsJordanCurve (toExt (frontier Ω)))
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {σ : Set ℂ} {a : ℂ} (hσ : σ = f '' (unitDisc ∩ sphere z₀ ρ)) (ha : a ∈ frontier Ω)
    (hJloop : IsJordanCurve (toExt (σ ∪ {a}))) :
    ∃ I I' : Set ℂ, IsOpen I ∧ IsOpen I' ∧ IsConnected I ∧ IsConnected I' ∧
      Bornology.IsBounded I ∧ I ⊆ Ω ∧ Disjoint I I' ∧
      frontier I = σ ∪ {a} ∧ Ω \ σ = I ∪ I' ∧
      ((f '' (unitDisc ∩ ball z₀ ρ) = I ∧ f '' (unitDisc \ closedBall z₀ ρ) = I') ∨
        (f '' (unitDisc ∩ ball z₀ ρ) = I' ∧ f '' (unitDisc \ closedBall z₀ ρ) = I)) := by
  set J : Set ℂ := σ ∪ {a} with hJ_def
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  have haΩ : a ∉ Ω := fun h => Set.disjoint_left.1 hΩfr h ha
  have hσΩ : σ ⊆ Ω := by
    rw [hσ, ← hf.2.2]; exact Set.image_mono Set.inter_subset_left
  obtain ⟨I, O, hIo, hOo, hIc, hOc, hIO, hIJ, hOJ, huniv, hIb, hOb⟩ :=
    jordan_curve_theorem_complex_bounded hJloop
  have hfrI : frontier I = J :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hJloop hIo hOo hIc hOc hIO hIJ hOJ
      huniv).1
  have hJsub : J ⊆ closure Ω := by
    rw [hJ_def]
    apply union_subset (hσΩ.trans subset_closure)
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact frontier_subset_closure ha
  obtain ⟨hEc, hEb⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hJ
  have hEJ : Disjoint (closure Ω)ᶜ J :=
    Set.disjoint_left.2 fun z hz hz2 => hz (hJsub hz2)
  have hEO : (closure Ω)ᶜ ⊆ O :=
    subset_unbounded_piece_of_isConnected_not_isBounded hIo hOo hIO hIJ hOJ huniv hIb hEc hEb hEJ
  have hIcl : I ⊆ closure Ω := fun z hz =>
    by_contra fun hzc => Set.disjoint_left.1 hIO hz (hEO hzc)
  have hIΩ : I ⊆ Ω :=
    (interior_maximal hIcl hIo).trans
      (interior_closure_subset_of_isJordanCurve_frontier hΩo hΩc hΩb hJ)
  have hJclosed : IsClosed J := (isCompact_of_isJordanCurve_toExt hJloop).isClosed
  have hΩσΩJ : Ω \ σ = Ω \ J := by
    ext z
    simp only [mem_diff, hJ_def, mem_union, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hzΩ, hzσ⟩; exact ⟨hzΩ, hzσ, fun h => haΩ (h ▸ hzΩ)⟩
    · rintro ⟨hzΩ, hzσ, -⟩; exact ⟨hzΩ, hzσ⟩
  have hΩJopen : IsOpen (Ω \ J) := hΩo.sdiff hJclosed
  obtain ⟨hDρopen, hDρconn, hEρopen, hEρconn, hsplit_eq, -⟩ := S2_disc_split hz₀ hρ0 hρ1
  have hF₁c : IsConnected (f '' (unitDisc ∩ ball z₀ ρ)) :=
    hDρconn.image f (hf.1.continuousOn.mono Set.inter_subset_left)
  have hF₂c : IsConnected (f '' (unitDisc \ closedBall z₀ ρ)) :=
    hEρconn.image f (hf.1.continuousOn.mono Set.diff_subset)
  have hDρEρ_disj : (unitDisc ∩ ball z₀ ρ) ∩ (unitDisc \ closedBall z₀ ρ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_diff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hz1⟩, -, hz2⟩
    exact hz2 (ball_subset_closedBall hz1)
  have hF₁F₂disj : Disjoint (f '' (unitDisc ∩ ball z₀ ρ)) (f '' (unitDisc \ closedBall z₀ ρ)) := by
    rw [Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hf.2.1 Set.inter_subset_left Set.diff_subset, hDρEρ_disj,
      Set.image_empty]
  have hFunion : Ω \ σ = f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) := by
    rw [← hf.2.2, hσ, ← Set.InjOn.image_diff_subset hf.2.1 Set.inter_subset_left, hsplit_eq,
      Set.image_union]
  have hΩJ_F : Ω \ J = f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) := by
    rw [← hΩσΩJ]; exact hFunion
  have hIsubΩJ : I ⊆ Ω \ J := fun z hz => ⟨hIΩ hz, fun h => Set.disjoint_left.1 hIJ hz h⟩
  have hΩOopen : IsOpen (Ω ∩ O) := hΩo.inter hOo
  have hΩJsplit : Ω \ J = I ∪ (Ω ∩ O) := by
    ext z
    simp only [mem_diff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨hzΩ, hzJ⟩
      rcases (huniv ▸ mem_univ z : z ∈ I ∪ O ∪ J) with h | h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hzΩ, h⟩
      · exact absurd h hzJ
    · rintro (h | ⟨hzΩ, hzO⟩)
      · exact ⟨hIΩ h, fun hJ' => Set.disjoint_left.1 hIJ h hJ'⟩
      · exact ⟨hzΩ, fun hJ' => Set.disjoint_left.1 hOJ hzO hJ'⟩
  have h2way : ∀ S : Set ℂ, IsConnected S → S ⊆ I ∪ (Ω ∩ O) → S ⊆ I ∨ S ⊆ Ω ∩ O := by
    intro S hSc hSsub
    exact isPreconnected_iff_subset_of_disjoint.1 hSc.isPreconnected I (Ω ∩ O) hIo hΩOopen hSsub
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, h1, -, h2⟩
        exact Set.disjoint_left.1 hIO h1 h2)
  have hc1 := h2way _ hF₁c (hΩJsplit ▸ (hΩJ_F ▸ Set.subset_union_left : f '' (unitDisc ∩ ball z₀ ρ) ⊆ Ω \ J))
  have hc2 := h2way _ hF₂c (hΩJsplit ▸ (hΩJ_F ▸ Set.subset_union_right : f '' (unitDisc \ closedBall z₀ ρ) ⊆ Ω \ J))
  obtain ⟨p, hp⟩ := hIc.nonempty
  have hempty_of_subset_disjoint : ∀ {A B : Set ℂ}, Disjoint A B → A ⊆ B → A = ∅ := by
    intro A B hAB hsub
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact Set.disjoint_left.1 hAB hz (hsub hz)
  have hJordanCard : ¬ (frontier Ω ⊆ ({a} : Set ℂ)) := by
    intro hsub
    obtain ⟨γ, hγc, hγi, hγr⟩ := hJ
    have hne : Circle.exp 0 ≠ Circle.exp Real.pi := by
      intro heq
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 heq
      have heq2 : (1 : ℝ) + 2 * (m : ℝ) = 0 := by
        have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
        have h3 : Real.pi * (1 + 2 * (m : ℝ)) = 0 := by ring_nf; ring_nf at hm; linarith [hm]
        exact (mul_eq_zero.1 h3).resolve_left hπ
      have heq3 : (2 * m : ℤ) = -1 := by
        have : ((2 * m : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith [heq2]
        exact_mod_cast this
      omega
    apply hne
    have hmem1 : γ (Circle.exp 0) ∈ toExt (frontier Ω) := hγr ▸ mem_range_self _
    have hmem2 : γ (Circle.exp Real.pi) ∈ toExt (frontier Ω) := hγr ▸ mem_range_self _
    obtain ⟨x1, hx1, hx1eq⟩ := hmem1
    obtain ⟨x2, hx2, hx2eq⟩ := hmem2
    have hx1a : x1 = a := hsub hx1
    have hx2a : x2 = a := hsub hx2
    apply hγi
    rw [← hx1eq, ← hx2eq, hx1a, hx2a]
  rcases hc1 with hc1 | hc1 <;> rcases hc2 with hc2 | hc2
  · exfalso
    have hsub : Ω \ J ⊆ I := by rw [hΩJ_F]; exact union_subset hc1 hc2
    have hΩOsubI : Ω ∩ O ⊆ I := fun z hz => hsub (hΩJsplit ▸ (Or.inr hz : z ∈ I ∪ Ω ∩ O))
    have hΩOempty : Ω ∩ O = ∅ :=
      hempty_of_subset_disjoint
        (Set.disjoint_left.2 fun z hz1 hz2 => Set.disjoint_left.1 hIO hz2 hz1.2) hΩOsubI
    have hΩJeq : Ω \ J = I := by rw [hΩJsplit, hΩOempty, union_empty]
    have hΩeq : Ω = I ∪ σ := by
      rw [← hΩσΩJ] at hΩJeq
      ext z
      constructor
      · intro hz
        by_cases hzσ : z ∈ σ
        · exact Or.inr hzσ
        · exact Or.inl (hΩJeq ▸ (⟨hz, hzσ⟩ : z ∈ Ω \ σ))
      · rintro (h | h)
        · exact hIΩ h
        · exact hσΩ h
    apply hJordanCard
    have hcl1 : closure I = I ∪ J := by
      rw [closure_eq_interior_union_frontier, hIo.interior_eq, hfrI]
    have hcl2 : closure σ ⊆ J := (closure_mono (hJ_def ▸ subset_union_left)).trans
      (hJclosed.closure_eq.le)
    have hclΩ : closure Ω ⊆ I ∪ J := by
      rw [hΩeq, closure_union]
      exact union_subset (hcl1.le) (hcl2.trans subset_union_right) |>.trans (le_refl _)
    intro z hz
    rw [hΩo.frontier_eq] at hz
    have hzcl : z ∈ closure Ω := hz.1
    have hzIJ : z ∈ I ∪ J := hclΩ hzcl
    rcases hzIJ with h | h
    · exact absurd (hΩeq ▸ (Or.inl h) : z ∈ Ω) hz.2
    · rw [hJ_def] at h
      rcases h with h | h
      · exact absurd (hΩeq ▸ (Or.inr h) : z ∈ Ω) hz.2
      · exact h
  · -- F₁ ⊆ I, F₂ ⊆ Ω ∩ O: the good case
    have hIeqF₁ : f '' (unitDisc ∩ ball z₀ ρ) = I := by
      refine Set.Subset.antisymm hc1 fun z hz => ?_
      have hzF : z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) :=
        hΩJ_F ▸ (hIsubΩJ hz)
      rcases hzF with h | h
      · exact h
      · exact absurd hz (fun hz' => Set.disjoint_left.1 hIO hz' (hc2 h).2)
    have hIclosedRel : closure I ∩ (Ω \ J) = I := by
      have hcl1 : closure I = I ∪ J := by
        rw [closure_eq_interior_union_frontier, hIo.interior_eq, hfrI]
      rw [hcl1]
      ext z
      simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2.2
      · intro hz
        exact ⟨Or.inl hz, hIsubΩJ hz⟩
    have hF₂eq : (Ω \ J) \ I = f '' (unitDisc \ closedBall z₀ ρ) := by
      rw [hΩJ_F, hIeqF₁]
      ext z
      simp only [mem_diff, mem_union]
      constructor
      · rintro ⟨h | h, h2⟩
        · exact absurd h h2
        · exact h
      · intro h
        refine ⟨Or.inr h, fun h2 => ?_⟩
        rw [← hIeqF₁] at h2
        exact Set.disjoint_left.1 hF₁F₂disj h2 h
    have hF₂open : IsOpen (f '' (unitDisc \ closedBall z₀ ρ)) := by
      rw [← hF₂eq]
      have heq : (Ω \ J) \ I = (Ω \ J) ∩ (closure I)ᶜ := by
        ext z
        simp only [mem_diff, mem_inter_iff, mem_compl_iff]
        constructor
        · rintro ⟨hz1, hz2⟩
          exact ⟨hz1, fun hzc => hz2 (hIclosedRel ▸ (⟨hzc, hz1⟩ : z ∈ closure I ∩ (Ω \ J)))⟩
        · rintro ⟨hz1, hz2⟩
          exact ⟨hz1, fun hzI => hz2 (subset_closure hzI)⟩
      rw [heq]
      exact hΩJopen.inter isClosed_closure.isOpen_compl
    have hIdisjF₂ : Disjoint I (f '' (unitDisc \ closedBall z₀ ρ)) := by
      rw [← hIeqF₁]; exact hF₁F₂disj
    refine ⟨I, f '' (unitDisc \ closedBall z₀ ρ), hIo, hF₂open, hIc, hF₂c, hIb, hIΩ, hIdisjF₂,
      hfrI, ?_, Or.inl ⟨hIeqF₁, rfl⟩⟩
    rw [hΩσΩJ, ← hF₂eq]
    ext z
    simp only [mem_union, mem_diff]
    constructor
    · intro hz
      by_cases hzI : z ∈ I
      · exact Or.inl hzI
      · exact Or.inr ⟨hz, hzI⟩
    · rintro (h | ⟨h, -⟩)
      · exact hIsubΩJ h
      · exact h
  · -- F₁ ⊆ Ω ∩ O, F₂ ⊆ I: the good case, swapped
    have hIeqF₂ : f '' (unitDisc \ closedBall z₀ ρ) = I := by
      refine Set.Subset.antisymm hc2 fun z hz => ?_
      have hzF : z ∈ f '' (unitDisc ∩ ball z₀ ρ) ∪ f '' (unitDisc \ closedBall z₀ ρ) :=
        hΩJ_F ▸ (hIsubΩJ hz)
      rcases hzF with h | h
      · exact absurd hz (fun hz' => Set.disjoint_left.1 hIO hz' (hc1 h).2)
      · exact h
    have hIclosedRel : closure I ∩ (Ω \ J) = I := by
      have hcl1 : closure I = I ∪ J := by
        rw [closure_eq_interior_union_frontier, hIo.interior_eq, hfrI]
      rw [hcl1]
      ext z
      simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2.2
      · intro hz
        exact ⟨Or.inl hz, hIsubΩJ hz⟩
    have hF₁eq : (Ω \ J) \ I = f '' (unitDisc ∩ ball z₀ ρ) := by
      rw [hΩJ_F, hIeqF₂]
      ext z
      simp only [mem_diff, mem_union]
      constructor
      · rintro ⟨h | h, h2⟩
        · exact h
        · exact absurd h h2
      · intro h
        refine ⟨Or.inl h, fun h2 => ?_⟩
        rw [← hIeqF₂] at h2
        exact Set.disjoint_left.1 hF₁F₂disj h h2
    have hF₁open : IsOpen (f '' (unitDisc ∩ ball z₀ ρ)) := by
      rw [← hF₁eq]
      have heq : (Ω \ J) \ I = (Ω \ J) ∩ (closure I)ᶜ := by
        ext z
        simp only [mem_diff, mem_inter_iff, mem_compl_iff]
        constructor
        · rintro ⟨hz1, hz2⟩
          exact ⟨hz1, fun hzc => hz2 (hIclosedRel ▸ (⟨hzc, hz1⟩ : z ∈ closure I ∩ (Ω \ J)))⟩
        · rintro ⟨hz1, hz2⟩
          exact ⟨hz1, fun hzI => hz2 (subset_closure hzI)⟩
      rw [heq]
      exact hΩJopen.inter isClosed_closure.isOpen_compl
    have hIdisjF₁ : Disjoint I (f '' (unitDisc ∩ ball z₀ ρ)) := by
      rw [← hIeqF₂]; exact hF₁F₂disj.symm
    refine ⟨I, f '' (unitDisc ∩ ball z₀ ρ), hIo, hF₁open, hIc, hF₁c, hIb, hIΩ, hIdisjF₁,
      hfrI, ?_, Or.inr ⟨rfl, hIeqF₂⟩⟩
    rw [hΩσΩJ, ← hF₁eq]
    ext z
    simp only [mem_union, mem_diff]
    constructor
    · intro hz
      by_cases hzI : z ∈ I
      · exact Or.inl hzI
      · exact Or.inr ⟨hz, hzI⟩
    · rintro (h | ⟨h, -⟩)
      · exact hIsubΩJ h
      · exact h
  · exfalso
    have hsub : Ω \ J ⊆ Ω ∩ O := by rw [hΩJ_F]; exact union_subset hc1 hc2
    have hIsubΩO : I ⊆ Ω ∩ O := fun z hz => hsub (hIsubΩJ hz)
    exact Set.disjoint_left.1 hIO hp (hIsubΩO hp).2

theorem diam_closure_eq_diam_frontier {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) :
    Metric.diam (closure U) = Metric.diam (frontier U) := by
  have hfrontier_meet : ∀ (S : Set ℂ), IsPreconnected S → (S ∩ U).Nonempty → (S ∩ Uᶜ).Nonempty →
      (S ∩ frontier U).Nonempty := by
    intro S hSpre hSU hSUc
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hSsub : S ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · refine Or.inr fun hzcl => ?_
        have hzfr : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hzcl, hzU⟩
        have hmem : z ∈ S ∩ frontier U := ⟨hz, hzfr⟩
        rw [hcon] at hmem
        exact hmem
    rcases isPreconnected_iff_subset_of_disjoint.1 hSpre U (closure U)ᶜ hU
        isClosed_closure.isOpen_compl hSsub
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨-, hz1, hz2⟩
          exact hz2 (subset_closure hz1)) with h | h
    · obtain ⟨z, hz⟩ := hSUc
      exact hz.2 (h hz.1)
    · obtain ⟨z, hz⟩ := hSU
      exact (h hz.1) (subset_closure hz.2)
  have hUc_ne : Uᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hUb
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun hmem => ?_⟩
    have hle := mem_closedBall_zero_iff.mp (hR hmem)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |R| + 1)] at hle
    linarith [abs_nonneg R, le_abs_self R]
  have hfrne : (frontier U).Nonempty := by
    have h1 : (Set.univ ∩ U).Nonempty := by rwa [Set.univ_inter]
    have h2 : (Set.univ ∩ Uᶜ).Nonempty := by rwa [Set.univ_inter]
    obtain ⟨z, -, hz⟩ := hfrontier_meet Set.univ isPreconnected_univ h1 h2
    exact ⟨z, hz⟩
  have hpush : ∀ a ∈ U, ∀ b : ℂ, ∃ p ∈ frontier U, dist b a ≤ dist b p := by
    intro a haU b
    by_cases hab : a = b
    · subst hab
      obtain ⟨p, hp⟩ := hfrne
      exact ⟨p, hp, by simp⟩
    · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hUb
      set γ : ℝ → ℂ := fun t => a + (t : ℂ) * (a - b) with hγ_def
      have hγcont : Continuous γ := by fun_prop
      have hSpre : IsPreconnected (γ '' Ici (0 : ℝ)) :=
        isPreconnected_Ici.image γ hγcont.continuousOn
      have hSU : (γ '' Ici (0 : ℝ) ∩ U).Nonempty :=
        ⟨a, ⟨0, Set.self_mem_Ici, by simp [hγ_def]⟩, haU⟩
      have habpos : (0 : ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
      set t₀ : ℝ := (|R| + ‖a‖ + 1) / ‖a - b‖ with ht₀_def
      have ht₀nn : 0 ≤ t₀ := by positivity
      have hSUc : (γ '' Ici (0 : ℝ) ∩ Uᶜ).Nonempty := by
        refine ⟨γ t₀, ⟨t₀, ht₀nn, rfl⟩, fun hmem => ?_⟩
        have h1 := mem_closedBall_zero_iff.mp (hR hmem)
        have h2 : t₀ * ‖a - b‖ - ‖a‖ ≤ ‖γ t₀‖ := by
          have htri := norm_sub_norm_le ((t₀ : ℂ) * (a - b)) (-a)
          simp only [norm_neg] at htri
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀nn] at htri
          calc t₀ * ‖a - b‖ - ‖a‖ ≤ ‖(t₀ : ℂ) * (a - b) - -a‖ := by linarith [htri]
            _ = ‖γ t₀‖ := by rw [hγ_def]; congr 1; ring
        have h3 : t₀ * ‖a - b‖ = |R| + ‖a‖ + 1 := by rw [ht₀_def]; field_simp
        rw [h3] at h2
        linarith [h1, le_abs_self R]
      obtain ⟨p, ⟨t₁, ht₁, hp_eq⟩, hpfr⟩ := hfrontier_meet _ hSpre hSU hSUc
      simp only [Set.mem_Ici] at ht₁
      refine ⟨p, hpfr, ?_⟩
      rw [← hp_eq]
      rw [dist_eq_norm, dist_eq_norm,
        show b - γ t₁ = ((1 : ℂ) + (t₁ : ℂ)) * (b - a) by rw [hγ_def]; ring, norm_mul]
      have h1 : ‖(1 : ℂ) + (t₁ : ℂ)‖ = 1 + t₁ := by
        rw [show (1 : ℂ) + (t₁ : ℂ) = ((1 + t₁ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht₁])]
      rw [h1]
      nlinarith [norm_nonneg (b - a), ht₁]
  have hdiamU_le : Metric.diam U ≤ Metric.diam (frontier U) := by
    apply Metric.diam_le_of_forall_dist_le_of_nonempty hUne
    intro x hxU y hyU
    obtain ⟨p, hpfr, hpx⟩ := hpush x hxU y
    obtain ⟨q, hqfr, hqp⟩ := hpush y hyU p
    calc dist x y = dist y x := dist_comm x y
      _ ≤ dist y p := hpx
      _ ≤ dist p q := by rw [dist_comm y p]; exact hqp
      _ ≤ Metric.diam (frontier U) :=
          Metric.dist_le_diam_of_mem (hUb.closure.subset frontier_subset_closure) hpfr hqfr
  have hdiamfr_le : Metric.diam (frontier U) ≤ Metric.diam U := by
    rw [← Metric.diam_closure U]
    exact Metric.diam_mono frontier_subset_closure hUb.closure
  rw [Metric.diam_closure]
  exact le_antisymm hdiamU_le hdiamfr_le

-- ===== Copied for self-containedness: C6 isArcEndC_split_circleShortArc (c2e_scratch.lean, md5 cf53d860) =====

theorem isArcEndC_split_circleShortArc {φ : Circle → ℂ} (hφ : Continuous φ)
    (hinj : Function.Injective φ) {s t : Circle} (hst : s ≠ t) :
    IsArcEndC (φ '' circleShortArc s t) (φ s) (φ t) ∧
      ∃ τ' : Set ℂ, IsArcEndC τ' (φ s) (φ t) ∧ φ '' circleShortArc s t ∪ τ' = range φ ∧
        φ '' circleShortArc s t ∩ τ' = {φ s, φ t} := by
  set θ : ℝ := arg ((t : ℂ) / s) with hθdef
  have hts_ne_one : (t : ℂ) / s ≠ 1 := by
    intro h
    apply hst
    have hs0 : (s : ℂ) ≠ 0 := by
      intro h0; have := Circle.norm_coe s; rw [h0] at this; simp at this
    have : (t : ℂ) = s := by
      field_simp at h
      exact h
    exact Subtype.ext this.symm
  have hθne0 : θ ≠ 0 := by
    intro h
    apply hts_ne_one
    have hnorm : ‖(t : ℂ) / s‖ = 1 := by
      rw [norm_div, Circle.norm_coe, Circle.norm_coe, div_one]
    have heq := Complex.norm_mul_exp_arg_mul_I ((t : ℂ) / s)
    rw [← hθdef, h] at heq
    simpa [hnorm] using heq.symm
  have hθmem : θ ∈ Ioc (-Real.pi) Real.pi := ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hshortEq : circleShortArc s t = (fun u : ℝ => s * Circle.exp (u * θ)) '' Icc 0 1 := rfl
  set γ : ℝ → ℂ := fun u => φ (s * Circle.exp (u * θ)) with hγdef
  have hγcont : Continuous γ := hφ.comp (by fun_prop)
  have hγ0 : γ 0 = φ s := by
    rw [hγdef]; simp only [zero_mul, Circle.exp_zero, mul_one]
  have hγ1 : γ 1 = φ t := by
    rw [hγdef]
    simp only [one_mul]
    congr 1
    have hexp : Circle.exp θ = t / s := by
      apply Subtype.ext
      rw [Circle.coe_exp, Circle.coe_div, hθdef]
      have hnorm : ‖(t : ℂ) / s‖ = 1 := by rw [norm_div, Circle.norm_coe, Circle.norm_coe, div_one]
      have heq := Complex.norm_mul_exp_arg_mul_I ((t : ℂ) / s)
      rwa [hnorm, Complex.ofReal_one, one_mul] at heq
    rw [hexp, mul_comm]
    exact div_mul_cancel t s
  have hγimgEq : φ '' circleShortArc s t = γ '' Icc 0 1 := by
    rw [hshortEq]; exact (image_comp φ _ (Icc (0:ℝ) 1)).symm
  have hγinj : InjOn γ (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    rw [hγdef] at huv
    simp only at huv
    have hcircleEq : Circle.exp (u * θ) = Circle.exp (v * θ) := by
      have hs0 : (s : ℂ) ≠ 0 := by
        intro h0; have := Circle.norm_coe s; rw [h0] at this; simp at this
      apply Subtype.ext
      have h1 := hinj huv
      have h2 : (s : ℂ) * (Circle.exp (u * θ) : ℂ) = s * (Circle.exp (v * θ) : ℂ) := by
        have := congrArg (fun x : Circle => (x : ℂ)) h1
        simpa using this
      exact mul_left_cancel₀ hs0 h2
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircleEq
    have hmz : m = 0 := by
      by_contra hm0
      have hm1 : (1:ℝ) ≤ |(m:ℝ)| := by
        have h1 : (1:ℤ) ≤ |m| := Int.one_le_abs hm0
        calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
          _ ≤ ((|m|:ℤ):ℝ) := by exact_mod_cast h1
          _ = |(m:ℝ)| := by push_cast; ring
      have hlhs : |u * θ - v * θ| = |(m:ℝ)| * (2 * Real.pi) := by
        have : u * θ - v * θ = (m:ℝ) * (2 * Real.pi) := by linarith [hm]
        rw [this, abs_mul]
        congr 1
        rw [abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hbound : |u * θ - v * θ| ≤ |θ| := by
        rw [← sub_mul, abs_mul]
        have : |u - v| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
        calc |u - v| * |θ| ≤ 1 * |θ| := by
              apply mul_le_mul_of_nonneg_right this (abs_nonneg _)
          _ = |θ| := one_mul _
      have hθbound : |θ| ≤ Real.pi := by
        rw [abs_le]; exact ⟨hθmem.1.le, hθmem.2⟩
      have : |(m:ℝ)| * (2 * Real.pi) ≤ Real.pi := hlhs ▸ hbound.trans hθbound
      nlinarith [Real.pi_pos]
    rw [hmz] at hm
    simp only [Int.cast_zero, zero_mul, add_zero] at hm
    exact mul_right_cancel₀ hθne0 hm
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h0; have := Circle.norm_coe s; rw [h0] at this; simp at this
  have hexp : Circle.exp θ = t / s := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_div, hθdef]
    have hnorm : ‖(t : ℂ) / s‖ = 1 := by rw [norm_div, Circle.norm_coe, Circle.norm_coe, div_one]
    have heq := Complex.norm_mul_exp_arg_mul_I ((t : ℂ) / s)
    rwa [hnorm, Complex.ofReal_one, one_mul] at heq
  -- generic injectivity helper, reused for both `θ` and `ψ`
  have hInjHelper : ∀ c : ℝ, c ≠ 0 → |c| < 2 * Real.pi →
      InjOn (fun u : ℝ => s * Circle.exp (u * c)) (Icc (0 : ℝ) 1) := by
    intro c hc0 hc2π u hu v hv huv
    simp only at huv
    have hcircleEq : Circle.exp (u * c) = Circle.exp (v * c) := by
      apply Subtype.ext
      have h2 : (s : ℂ) * (Circle.exp (u * c) : ℂ) = s * (Circle.exp (v * c) : ℂ) := by
        have := congrArg (fun x : Circle => (x : ℂ)) huv
        simpa using this
      exact mul_left_cancel₀ hs0 h2
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircleEq
    have hmz : m = 0 := by
      by_contra hm0
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
          _ = |(m : ℝ)| := by push_cast; ring
      have hlhs : |u * c - v * c| = |(m : ℝ)| * (2 * Real.pi) := by
        have heq2 : u * c - v * c = (m : ℝ) * (2 * Real.pi) := by linarith [hm]
        rw [heq2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hbound : |u * c - v * c| ≤ |c| := by
        rw [← sub_mul, abs_mul]
        have hle : |u - v| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
        calc |u - v| * |c| ≤ 1 * |c| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          _ = |c| := one_mul _
      have hcontra : |(m : ℝ)| * (2 * Real.pi) ≤ |c| := hlhs ▸ hbound
      nlinarith [Real.pi_pos]
    rw [hmz] at hm
    simp only [Int.cast_zero, zero_mul, add_zero] at hm
    exact mul_right_cancel₀ hc0 hm
  -- Fact A: every `z : Circle` has a canonical angle `arg (z/s) ∈ (-π,π]`
  have harg : ∀ z : Circle, z = s * Circle.exp (arg ((z:ℂ) / s)) := by
    intro z
    apply Subtype.ext
    rw [Circle.coe_mul, Circle.coe_exp]
    have hnorm : ‖(z : ℂ) / s‖ = 1 := by rw [norm_div, Circle.norm_coe, Circle.norm_coe, div_one]
    have heq := Complex.norm_mul_exp_arg_mul_I ((z : ℂ) / s)
    rw [hnorm, Complex.ofReal_one, one_mul] at heq
    rw [heq]
    field_simp
  have hargmem : ∀ z : Circle, arg ((z:ℂ) / s) ∈ Ioc (-Real.pi) Real.pi :=
    fun z => ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have huniq : ∀ β₁ ∈ Ioc (-Real.pi) Real.pi, ∀ β₂ ∈ Ioc (-Real.pi) Real.pi,
      s * Circle.exp β₁ = s * Circle.exp β₂ → β₁ = β₂ := by
    intro β₁ hβ₁ β₂ hβ₂ heq
    have hcircleEq : Circle.exp β₁ = Circle.exp β₂ := mul_left_cancel heq
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircleEq
    have hmz : m = 0 := by
      by_contra hm0
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
          _ = |(m : ℝ)| := by push_cast; ring
      have hdiff : |β₁ - β₂| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨by linarith [hβ₁.1, hβ₂.2], by linarith [hβ₁.2, hβ₂.1]⟩
      have hlhs : |β₁ - β₂| = |(m : ℝ)| * (2 * Real.pi) := by
        have heq2 : β₁ - β₂ = (m : ℝ) * (2 * Real.pi) := by linarith [hm]
        rw [heq2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hcontra : |(m:ℝ)| * (2*Real.pi) < 2*Real.pi := hlhs ▸ hdiff
      nlinarith [Real.pi_pos]
    rw [hmz] at hm
    simpa using hm
  refine ⟨⟨γ, hγimgEq, hγcont.continuousOn, hγinj, hγ0, hγ1⟩, ?_⟩
  -- the long side
  rcases lt_or_gt_of_ne hθne0 with hθlt | hθgt
  · -- θ < 0 (case B): ψ := θ + 2π > 0
    set ψ : ℝ := θ + 2 * Real.pi with hψdef
    have hψpos : 0 < ψ := by rw [hψdef]; linarith [hθmem.1]
    have hψlt2π : ψ < 2 * Real.pi := by rw [hψdef]; linarith
    have hψne0 : ψ ≠ 0 := hψpos.ne'
    have hψabs : |ψ| < 2 * Real.pi := by rw [abs_of_pos hψpos]; exact hψlt2π
    have hψexp : Circle.exp ψ = t / s := by
      rw [hψdef, Circle.exp_add]
      have h2π : Circle.exp (2 * Real.pi) = 1 := by simp
      rw [h2π, mul_one]; exact hexp
    set τ : ℝ → ℂ := fun u => φ (s * Circle.exp (u * ψ)) with hτdef
    have hτcont : Continuous τ := hφ.comp (by fun_prop)
    have hτ0 : τ 0 = φ s := by rw [hτdef]; simp only [zero_mul, Circle.exp_zero, mul_one]
    have hτ1 : τ 1 = φ t := by
      rw [hτdef]; simp only [one_mul]; congr 1
      rw [hψexp, mul_comm]; exact div_mul_cancel t s
    have hτinj : InjOn τ (Icc (0 : ℝ) 1) := fun u hu v hv huv =>
      hInjHelper ψ hψne0 hψabs hu hv (hinj huv)
    have hτimgEq : φ '' ((fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1) = τ '' Icc 0 1 :=
      (image_comp φ _ (Icc (0:ℝ) 1)).symm
    refine ⟨φ '' ((fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1),
      ⟨τ, hτimgEq, hτcont.continuousOn, hτinj, hτ0, hτ1⟩, ?_, ?_⟩
    · -- union
      have hcircleUnion : circleShortArc s t ∪
          (fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1 = univ := by
        rw [hshortEq]
        ext z
        simp only [mem_union, mem_image, mem_univ, iff_true]
        set β := arg ((z:ℂ) / s) with hβdef
        have hzβ : z = s * Circle.exp β := harg z
        have hβmem : β ∈ Ioc (-Real.pi) Real.pi := hargmem z
        by_cases hcase : β ∈ Icc θ 0
        · left
          refine ⟨β / θ, ⟨by
            rw [le_div_iff_of_neg hθlt]; nlinarith [hcase.2], by
            rw [div_le_one_of_neg hθlt]; linarith [hcase.1]⟩, ?_⟩
          rw [div_mul_cancel₀ β hθne0, ← hzβ]
        · right
          simp only [mem_Icc, not_and_or, not_le] at hcase
          rcases hcase with hβltθ | hβpos
          · -- -π < β < θ
            refine ⟨(β + 2 * Real.pi) / ψ, ⟨by
              apply div_nonneg _ hψpos.le; linarith [hβmem.1], by
              rw [div_le_one hψpos]; linarith [hβltθ]⟩, ?_⟩
            have hstep : (β + 2 * Real.pi) / ψ * ψ = β + 2 * Real.pi :=
              div_mul_cancel₀ (β + 2 * Real.pi) hψne0
            rw [hstep]
            have hexpshift : Circle.exp (β + 2 * Real.pi) = Circle.exp β := by
              rw [Circle.exp_add]
              have h2π : Circle.exp (2 * Real.pi) = 1 := by simp
              rw [h2π, mul_one]
            rw [hexpshift, ← hzβ]
          · -- 0 < β ≤ π
            refine ⟨β / ψ, ⟨(div_pos hβpos hψpos).le, ?_⟩, ?_⟩
            · rw [div_le_one hψpos]; linarith [hβmem.2, hθmem.1]
            · rw [div_mul_cancel₀ β hψne0, ← hzβ]
      rw [← image_union, hcircleUnion, image_univ]
    · -- intersection
      have hcircleInter : circleShortArc s t ∩
          (fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1 = {s, t} := by
        rw [hshortEq]
        ext z
        simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨⟨u, hu, hueq⟩, ⟨u', hu', hu'eq⟩⟩
          have heqc : Circle.exp (u * θ) = Circle.exp (u' * ψ) := mul_left_cancel (a := s) (by
            rw [hueq, hu'eq])
          obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp heqc
          have hb1lo : θ ≤ u * θ := by nlinarith [hu.1, hu.2]
          have hb1hi : u * θ ≤ 0 := by nlinarith [hu.1, hu.2]
          have hb2lo : 0 ≤ u' * ψ := by nlinarith [hu'.1, hu'.2]
          have hb2hi : u' * ψ ≤ ψ := by nlinarith [hu'.1, hu'.2]
          have hkeq : (k:ℝ) * (2 * Real.pi) = u * θ - u' * ψ := by linarith [hk]
          have hkbound : (k:ℝ) * (2 * Real.pi) ∈ Icc (-(2*Real.pi)) 0 := by
            rw [hkeq]
            constructor <;> nlinarith [hb1lo, hb1hi, hb2lo, hb2hi]
          have hkz : k = 0 ∨ k = -1 := by
            have h1 : (-1:ℝ) ≤ (k:ℝ) := by nlinarith [hkbound.1, Real.pi_pos]
            have h2 : (k:ℝ) ≤ 0 := by nlinarith [hkbound.2, Real.pi_pos]
            have h1' : (-1:ℤ) ≤ k := by exact_mod_cast h1
            have h2' : k ≤ 0 := by exact_mod_cast h2
            omega
          rcases hkz with hk0 | hkm1
          · left
            rw [hk0] at hk
            simp only [Int.cast_zero, zero_mul, add_zero] at hk
            have hu0 : u * θ = 0 := by nlinarith [hb1hi, hb2lo, hk]
            have huz : u = 0 := by
              rcases mul_eq_zero.mp hu0 with h|h
              · exact h
              · exact absurd h hθne0
            rw [← hueq, huz, zero_mul, Circle.exp_zero, mul_one]
          · right
            rw [hkm1] at hk
            push_cast at hk
            have huθ : u * θ = θ := by nlinarith [hb1lo, hb2hi, hk, hψdef]
            have huz : u = 1 := mul_right_cancel₀ hθne0 (by rw [huθ, one_mul])
            rw [← hueq, huz, one_mul, hexp, mul_comm]
            exact div_mul_cancel t s
        · intro h
          rcases h with h | h
          · refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩, ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩⟩ <;>
              rw [h, zero_mul, Circle.exp_zero, mul_one]
          · refine ⟨⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩, ⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩⟩
            · rw [h, one_mul, hexp, mul_comm]; exact div_mul_cancel t s
            · rw [h, one_mul, hψexp, mul_comm]; exact div_mul_cancel t s
      rw [← image_inter hinj, hcircleInter]
      simp [image_insert_eq]
  · -- θ > 0 (case A): ψ := θ - 2π < 0
    set ψ : ℝ := θ - 2 * Real.pi with hψdef
    have hψneg : ψ < 0 := by rw [hψdef]; linarith [hθmem.2]
    have hψgtneg2π : -(2 * Real.pi) < ψ := by rw [hψdef]; linarith
    have hψne0 : ψ ≠ 0 := hψneg.ne
    have hψabs : |ψ| < 2 * Real.pi := by rw [abs_of_neg hψneg]; linarith
    have hψexp : Circle.exp ψ = t / s := by
      rw [hψdef, sub_eq_add_neg, Circle.exp_add]
      have h2π : Circle.exp (-(2 * Real.pi)) = 1 := by simp
      rw [h2π, mul_one]; exact hexp
    set τ : ℝ → ℂ := fun u => φ (s * Circle.exp (u * ψ)) with hτdef
    have hτcont : Continuous τ := hφ.comp (by fun_prop)
    have hτ0 : τ 0 = φ s := by rw [hτdef]; simp only [zero_mul, Circle.exp_zero, mul_one]
    have hτ1 : τ 1 = φ t := by
      rw [hτdef]; simp only [one_mul]; congr 1
      rw [hψexp, mul_comm]; exact div_mul_cancel t s
    have hτinj : InjOn τ (Icc (0 : ℝ) 1) := fun u hu v hv huv =>
      hInjHelper ψ hψne0 hψabs hu hv (hinj huv)
    have hτimgEq : φ '' ((fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1) = τ '' Icc 0 1 :=
      (image_comp φ _ (Icc (0:ℝ) 1)).symm
    refine ⟨φ '' ((fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1),
      ⟨τ, hτimgEq, hτcont.continuousOn, hτinj, hτ0, hτ1⟩, ?_, ?_⟩
    · -- union
      have hcircleUnion : circleShortArc s t ∪
          (fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1 = univ := by
        rw [hshortEq]
        ext z
        simp only [mem_union, mem_image, mem_univ, iff_true]
        set β := arg ((z:ℂ) / s) with hβdef
        have hzβ : z = s * Circle.exp β := harg z
        have hβmem : β ∈ Ioc (-Real.pi) Real.pi := hargmem z
        by_cases hcase : β ∈ Icc 0 θ
        · left
          refine ⟨β / θ, ⟨div_nonneg hcase.1 hθgt.le, ?_⟩, ?_⟩
          · rw [div_le_one hθgt]; exact hcase.2
          · rw [div_mul_cancel₀ β hθne0, ← hzβ]
        · right
          simp only [mem_Icc, not_and_or, not_le] at hcase
          rcases hcase with hβneg | hβgtθ
          · -- -π < β < 0
            refine ⟨β / ψ, ⟨?_, ?_⟩, ?_⟩
            · rw [le_div_iff_of_neg hψneg]; nlinarith [hβneg]
            · rw [div_le_one_of_neg hψneg]; nlinarith [hβmem.1, hθmem.2]
            rw [div_mul_cancel₀ β hψne0, ← hzβ]
          · -- θ < β ≤ π
            refine ⟨(β - 2 * Real.pi) / ψ, ⟨?_, ?_⟩, ?_⟩
            · rw [le_div_iff_of_neg hψneg]; nlinarith [hβmem.2]
            · rw [div_le_one_of_neg hψneg]; nlinarith [hβgtθ]
            have hstep : (β - 2 * Real.pi) / ψ * ψ = β - 2 * Real.pi :=
              div_mul_cancel₀ (β - 2 * Real.pi) hψne0
            rw [hstep]
            have hexpshift : Circle.exp (β - 2 * Real.pi) = Circle.exp β := by
              rw [sub_eq_add_neg, Circle.exp_add]
              have h2π : Circle.exp (-(2 * Real.pi)) = 1 := by
                simp
              rw [h2π, mul_one]
            rw [hexpshift, ← hzβ]
      rw [← image_union, hcircleUnion, image_univ]
    · -- intersection
      have hcircleInter : circleShortArc s t ∩
          (fun u : ℝ => s * Circle.exp (u * ψ)) '' Icc (0:ℝ) 1 = {s, t} := by
        rw [hshortEq]
        ext z
        simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨⟨u, hu, hueq⟩, ⟨u', hu', hu'eq⟩⟩
          have heqc : Circle.exp (u * θ) = Circle.exp (u' * ψ) := mul_left_cancel (a := s) (by
            rw [hueq, hu'eq])
          obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp heqc
          have hb1lo : 0 ≤ u * θ := by nlinarith [hu.1, hu.2]
          have hb1hi : u * θ ≤ θ := by nlinarith [hu.1, hu.2]
          have hb2lo : ψ ≤ u' * ψ := by nlinarith [hu'.1, hu'.2]
          have hb2hi : u' * ψ ≤ 0 := by nlinarith [hu'.1, hu'.2]
          have hkeq : (k:ℝ) * (2 * Real.pi) = u * θ - u' * ψ := by linarith [hk]
          have hkbound : (k:ℝ) * (2 * Real.pi) ∈ Icc (0:ℝ) (2*Real.pi) := by
            rw [hkeq]
            constructor <;> nlinarith [hb1lo, hb1hi, hb2lo, hb2hi]
          have hkz : k = 0 ∨ k = 1 := by
            have h1 : (0:ℝ) ≤ (k:ℝ) := by nlinarith [hkbound.1, Real.pi_pos]
            have h2 : (k:ℝ) ≤ 1 := by nlinarith [hkbound.2, Real.pi_pos]
            have h1' : (0:ℤ) ≤ k := by exact_mod_cast h1
            have h2' : k ≤ 1 := by exact_mod_cast h2
            omega
          rcases hkz with hk0 | hk1
          · left
            rw [hk0] at hk
            simp only [Int.cast_zero, zero_mul, add_zero] at hk
            have hu0 : u * θ = 0 := by nlinarith [hb1lo, hb2hi, hk]
            have huz : u = 0 := by
              rcases mul_eq_zero.mp hu0 with h|h
              · exact h
              · exact absurd h hθne0
            rw [← hueq, huz, zero_mul, Circle.exp_zero, mul_one]
          · right
            rw [hk1] at hk
            push_cast at hk
            have huθ : u * θ = θ := by nlinarith [hb1hi, hb2lo, hk]
            have huz : u = 1 := mul_right_cancel₀ hθne0 (by rw [huθ, one_mul])
            rw [← hueq, huz, one_mul, hexp, mul_comm]
            exact div_mul_cancel t s
        · intro h
          rcases h with h | h
          · refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩, ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩⟩ <;>
              rw [h, zero_mul, Circle.exp_zero, mul_one]
          · refine ⟨⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩, ⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩⟩
            · rw [h, one_mul, hexp, mul_comm]; exact div_mul_cancel t s
            · rw [h, one_mul, hψexp, mul_comm]; exact div_mul_cancel t s
      rw [← image_inter hinj, hcircleInter]
      simp [image_insert_eq]

-- ===== C1, C2, C3 and their internal helpers (c3_scratch.lean, md5 00dea849) =====

theorem tendsto_boundary_of_isConformalOnto {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {z : ℕ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hz : ∀ n, z n ∈ unitDisc) (hzζ : Tendsto z atTop (𝓝 ζ)) {w : ℂ}
    (hw : Tendsto (fun n => f (z n)) atTop (𝓝 w)) : w ∉ Ω := by
  intro hwΩ
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔo
  set g : ℂ → ℂ := Function.invFunOn f unitDisc with hg_def
  have hgconf : IsConformalOnto g Ω unitDisc := hf.symm hΔo
  have hgcont : ContinuousAt g w := hgconf.1.continuousOn.continuousAt (hΩo.mem_nhds hwΩ)
  have hcomp : Tendsto (fun n => g (f (z n))) atTop (𝓝 (g w)) := hgcont.tendsto.comp hw
  have heq : ∀ n, g (f (z n)) = z n := fun n => hf.2.1.leftInvOn_invFunOn (hz n)
  have hcomp' : Tendsto z atTop (𝓝 (g w)) := by simpa only [heq] using hcomp
  have hζeq : ζ = g w := tendsto_nhds_unique hzζ hcomp'
  have hgwmem : g w ∈ unitDisc := hgconf.2.2 ▸ mem_image_of_mem g hwΩ
  rw [← hζeq] at hgwmem
  rw [unitDisc, mem_ball_zero_iff, hζ] at hgwmem
  exact absurd hgwmem (lt_irrefl 1)

/-- The `lintegral` of a `2π`-periodic measurable function over a period-length window
`Ioc a (a + 2π)` does not depend on `a`, for `a ∈ Ioc (-π) π`. -/
theorem lintegral_Ioc_two_pi_shift {h : ℝ → ℝ≥0∞} (hmeas : Measurable h)
    (hper : Function.Periodic h (2 * π)) {a : ℝ} (ha : a ∈ Ioc (-π) π) :
    ∫⁻ θ in Ioc a (a + 2 * π), h θ = ∫⁻ θ in Ioc (-π) π, h θ := by
  set c : ℝ := 2 * π with hc_def
  have hshift : ∀ s t : ℝ, ∫⁻ θ in Ioc s t, h (θ + c) = ∫⁻ θ in Ioc (s + c) (t + c), h θ := by
    intro s t
    have hg : Measurable (fun θ : ℝ => θ + c) := measurable_add_const c
    have hmap : Measure.map (fun θ : ℝ => θ + c) volume = volume := map_add_right_eq_self volume c
    have hpre : (fun θ : ℝ => θ + c) ⁻¹' Ioc (s + c) (t + c) = Ioc s t := by
      ext θ
      simp only [mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [← hpre, ← setLIntegral_map measurableSet_Ioc hmeas hg, hmap]
  have hpershift : ∀ s t : ℝ, ∫⁻ θ in Ioc s t, h θ = ∫⁻ θ in Ioc (s + c) (t + c), h θ := by
    intro s t
    rw [← hshift]
    congr 1
    funext θ
    exact (hper θ).symm
  rcases eq_or_lt_of_le ha.2 with ha' | ha'
  · rw [ha']
    have hcc : (-π : ℝ) + c = π := by rw [hc_def]; ring
    calc ∫⁻ θ in Ioc π (π + c), h θ = ∫⁻ θ in Ioc (-π + c) (π + c), h θ := by rw [hcc]
      _ = ∫⁻ θ in Ioc (-π) π, h θ := (hpershift (-π) π).symm
  · have hπmem : π ∈ Ioc a (a + c) := ⟨ha', by rw [hc_def]; linarith [Real.pi_pos, ha.1]⟩
    rw [show Ioc a (a + c) = Ioc a π ∪ Ioc π (a + c) from
      (Ioc_union_Ioc_eq_Ioc hπmem.1.le hπmem.2).symm,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le (le_refl π))]
    have heq2 : ∫⁻ θ in Ioc π (a + c), h θ = ∫⁻ θ in Ioc (-π) a, h θ := by
      have hcc : (π : ℝ) = (-π) + c := by rw [hc_def]; ring
      calc ∫⁻ θ in Ioc π (a + c), h θ = ∫⁻ θ in Ioc ((-π) + c) (a + c), h θ := by rw [← hcc]
        _ = ∫⁻ θ in Ioc (-π) a, h θ := (hpershift (-π) a).symm
    rw [heq2, add_comm, ← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le (le_refl a)),
      Ioc_union_Ioc_eq_Ioc (by linarith [ha.1] : (-π : ℝ) ≤ a) ha'.le]

/-- If `g` has derivative `g'` throughout the open interval `(a, b)` and `‖g'‖` is integrable
there, then `g` has a limit as its argument approaches `b` from the left. -/
theorem exists_tendsto_nhdsLT_of_integrableOn_norm_deriv
    {g g' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt g (g' s) s)
    (hcont : ContinuousOn g' (Ioo a b))
    (hint : IntegrableOn (fun s => ‖g' s‖) (Ioo a b)) :
    ∃ L : ℂ, Tendsto g (𝓝[<] b) (𝓝 L) := by
  have hIoo : MeasurableSet (Ioo a b) := measurableSet_Ioo
  have hg'int : IntegrableOn g' (Ioo a b) :=
    ⟨hcont.aestronglyMeasurable hIoo, (hasFiniteIntegral_norm_iff g').mp hint.2⟩
  have hindic : Integrable ((Ioo a b).indicator (fun s => ‖g' s‖)) := hint.integrable_indicator hIoo
  have hshrink : Tendsto (fun i : ℝ => volume (Ioo i b)) (𝓝[<] b) (𝓝 0) := by
    have h0 : Tendsto (fun i : ℝ => b - i) (𝓝[<] b) (𝓝 0) := by
      have hc : ContinuousWithinAt (fun i : ℝ => b - i) (Iio b) b :=
        (continuous_const.sub continuous_id).continuousWithinAt
      simpa using hc.tendsto
    have h1 : Tendsto (fun i : ℝ => ENNReal.ofReal (b - i)) (𝓝[<] b) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h0
    simpa only [Real.volume_Ioo] using h1
  have htail0 : Tendsto (fun i => ∫ x in Ioo i b, (Ioo a b).indicator (fun s => ‖g' s‖) x)
      (𝓝[<] b) (𝓝 0) := hindic.tendsto_setIntegral_nhds_zero hshrink
  have hamem : Ioi a ∈ 𝓝[<] b := mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hab)
  have htail : Tendsto (fun i => ∫ x in Ioo i b, ‖g' x‖) (𝓝[<] b) (𝓝 0) := by
    refine htail0.congr' ?_
    filter_upwards [hamem] with i hi
    have hia : a < i := hi
    rw [MeasureTheory.integral_indicator hIoo, Measure.restrict_restrict hIoo,
      inter_eq_right.mpr (Ioo_subset_Ioo_left hia.le)]
  have hkey : ∀ ε : ℝ, ∀ s t : ℝ, a < s → s < b → t < b → s ≤ t →
      (∫ x in Ioo s b, ‖g' x‖) < ε → dist (g s) (g t) < ε := by
    intro ε s t hsa hsb htb hst hbound
    have hIcc : Icc s t ⊆ Ioo a b := fun x hx => ⟨hsa.trans_le hx.1, hx.2.trans_lt htb⟩
    have huIcc : uIcc s t = Icc s t := uIcc_of_le hst
    have hderiv' : ∀ x ∈ uIcc s t, HasDerivAt g (g' x) x := by
      rw [huIcc]; exact fun x hx => hderiv x (hIcc hx)
    have hintegrable' : IntervalIntegrable g' volume s t := by
      apply IntegrableOn.intervalIntegrable
      rw [huIcc]; exact hg'int.mono_set hIcc
    have hftc : ∫ x in s..t, g' x = g t - g s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hintegrable'
    have hnorm : ‖g t - g s‖ ≤ ∫ x in s..t, ‖g' x‖ := hftc ▸ intervalIntegral.norm_integral_le_integral_norm hst
    have hIoc_sub : Ioc s t ⊆ Ioo s b := fun x hx => ⟨hx.1, hx.2.trans_lt htb⟩
    have hTint : IntegrableOn (fun x => ‖g' x‖) (Ioo s b) :=
      hint.mono_set (Ioo_subset_Ioo_left hsa.le)
    have hmono : ∫ x in Ioc s t, ‖g' x‖ ≤ ∫ x in Ioo s b, ‖g' x‖ :=
      setIntegral_mono_set hTint (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (LE.le.eventuallySubset hIoc_sub)
    have heq : ∫ x in s..t, ‖g' x‖ = ∫ x in Ioc s t, ‖g' x‖ := intervalIntegral.integral_of_le hst
    calc dist (g s) (g t) = ‖g t - g s‖ := by rw [dist_comm]; exact Complex.dist_eq _ _
      _ ≤ ∫ x in s..t, ‖g' x‖ := hnorm
      _ = ∫ x in Ioc s t, ‖g' x‖ := heq
      _ ≤ ∫ x in Ioo s b, ‖g' x‖ := hmono
      _ < ε := hbound
  have hcauchy : Cauchy (Filter.map g (𝓝[<] b)) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    have hev : ∀ᶠ i in 𝓝[<] b, ∫ x in Ioo i b, ‖g' x‖ < ε :=
      htail.eventually (isOpen_Iio.mem_nhds hε)
    obtain ⟨l, hlb, hlsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 (hev.and hamem)
    set l' := max l a with hl'_def
    have hl'b : l' < b := max_lt hlb hab
    have hl'sub : Ioo l' b ⊆ {i | ∫ x in Ioo i b, ‖g' x‖ < ε} ∩ Ioi a :=
      (Ioo_subset_Ioo_left (le_max_left l a)).trans hlsub
    refine ⟨g '' Ioo l' b, Filter.image_mem_map ((nhdsLT_basis b).mem_of_mem hl'b), ?_⟩
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    have hsa : a < s := Set.mem_Ioi.mp (hl'sub hs).2
    have hta : a < t := Set.mem_Ioi.mp (hl'sub ht).2
    have hsb : s < b := hs.2
    have htb : t < b := ht.2
    have hsbound : ∫ x in Ioo s b, ‖g' x‖ < ε := (hl'sub hs).1
    have htbound : ∫ x in Ioo t b, ‖g' x‖ < ε := (hl'sub ht).1
    rcases le_total s t with hst | hst
    · exact hkey ε s t hsa hsb htb hst hsbound
    · rw [dist_comm]; exact hkey ε t s hta htb hsb hst htbound
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  exact ⟨L, hL⟩

/-- If `c` is continuous and injective on the compact interval `Icc l r`, its point-inverse
`Function.invFunOn c (Icc l r)` is continuous on the image `c '' Icc l r` (with the ambient
topology of `ℂ`, restricted to that image). -/
theorem continuousOn_invFunOn_of_continuousOn_injOn {c : ℝ → ℂ} {l r : ℝ}
    (hc : ContinuousOn c (Icc l r)) (hinj : InjOn c (Icc l r)) :
    ContinuousOn (Function.invFunOn c (Icc l r)) (c '' Icc l r) := by
  set ψ := Function.invFunOn c (Icc l r) with hψ_def
  have hleft : ∀ s ∈ Icc l r, ψ (c s) = s := hinj.leftInvOn_invFunOn
  have hemb : IsClosedEmbedding ((Icc l r).restrict c) :=
    hc.restrict.isClosedEmbedding hinj.injective
  set e := hemb.isEmbedding.toHomeomorph
  have to_rng : ∀ w, w ∈ c '' Icc l r → w ∈ range ((Icc l r).restrict c) := by
    intro w hw; obtain ⟨t, ht, rfl⟩ := hw; exact ⟨⟨t, ht⟩, rfl⟩
  have hψ_eq : ∀ w (hw : w ∈ c '' Icc l r),
      ψ w = (e.symm ⟨w, to_rng w hw⟩).val := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := (mem_image c _ _).mp hw
    rw [hleft t ht]
    exact (congrArg Subtype.val (hemb.isEmbedding.toHomeomorph_symm_apply ⟨t, ht⟩)).symm
  rw [Metric.continuousOn_iff]
  intro w hw ε hε
  have hcont_sub : Continuous (Subtype.val ∘ e.symm :
      ↑(range ((Icc l r).restrict c)) → ℝ) := continuous_subtype_val.comp e.symm.continuous
  have hw_rng : w ∈ range ((Icc l r).restrict c) := by
    obtain ⟨t, ht, rfl⟩ := (mem_image c _ _).mp hw; exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont_sub (⟨w, hw_rng⟩ : ↑(range _)) ε hε
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  have hz_rng : z ∈ range ((Icc l r).restrict c) := by
    obtain ⟨t, ht, rfl⟩ := (mem_image c _ _).mp hz; exact ⟨⟨t, ht⟩, rfl⟩
  rw [hψ_eq w hw, hψ_eq z hz]
  exact hball ⟨z, hz_rng⟩ (by simpa [Subtype.dist_eq] using hdist)

/-- The norm-squared of the standard `α + π + s` reparametrization of `circleMap z₀ ρ`, where
`α := arg z₀`: this is `1 - 2ρ cos s + ρ²`, independent of `arg z₀`. -/
theorem norm_sq_circleMap_arg_add_pi_add {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) (ρ s : ℝ) :
    ‖circleMap z₀ ρ (Complex.arg z₀ + π + s)‖ ^ 2 = 1 - 2 * ρ * Real.cos s + ρ ^ 2 := by
  set α := Complex.arg z₀ with hα_def
  have hz₀exp : Complex.exp ((α : ℂ) * I) = z₀ := by
    have h := Complex.norm_mul_exp_arg_mul_I z₀
    rwa [hz₀, Complex.ofReal_one, one_mul] at h
  have hfactor : circleMap z₀ ρ (α + π + s)
      = Complex.exp ((α : ℂ) * I) * (1 - (ρ : ℂ) * Complex.exp ((s : ℂ) * I)) := by
    show z₀ + (ρ : ℂ) * Complex.exp (((α + π + s : ℝ) : ℂ) * I) = _
    rw [← hz₀exp]
    have hsplit : ((α + π + s : ℝ) : ℂ) * I = (α : ℂ) * I + ((π : ℂ) * I + (s : ℂ) * I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hexpnorm : ‖Complex.exp ((α : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I α
  rw [hfactor, norm_mul, hexpnorm, one_mul, Complex.sq_norm, Complex.normSq_sub,
    Complex.normSq_one]
  have h1 : Complex.normSq ((ρ : ℂ) * Complex.exp ((s : ℂ) * I)) = ρ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, ← Complex.sq_norm,
      Complex.norm_exp_ofReal_mul_I, one_pow]
    ring
  have h2 : ((1 : ℂ) * (starRingEnd ℂ) ((ρ : ℂ) * Complex.exp ((s : ℂ) * I))).re
      = ρ * Real.cos s := by
    rw [one_mul, map_mul, Complex.conj_ofReal]
    have hce : (starRingEnd ℂ) (Complex.exp ((s : ℂ) * I)) = Complex.exp (((-s : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_conj]
      congr 1
      push_cast
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hce, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [h1, h2]
  ring

/-- Every point of the circle `sphere z₀ ρ` is `circleMap z₀ ρ (arg z₀ + π + s)` for some
`s ∈ Ioc (-π) π`. -/
theorem exists_mem_Ioc_circleMap_arg_add_pi_add {z₀ : ℂ} {ρ : ℝ} (hρ0 : 0 < ρ) {w : ℂ}
    (hw : w ∈ sphere z₀ ρ) :
    ∃ s ∈ Ioc (-π) π, circleMap z₀ ρ (Complex.arg z₀ + π + s) = w := by
  set α := Complex.arg z₀ with hα_def
  have hwz : ‖w - z₀‖ = ρ := by rw [← Complex.dist_eq]; exact hw
  set u : ℂ := -Complex.exp (((-α : ℝ) : ℂ) * I) * (w - z₀) / (ρ : ℂ) with hu_def
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
  have hunorm : ‖u‖ = 1 := by
    rw [hu_def, norm_div, norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, one_mul, hwz,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, div_self hρ0.ne']
  refine ⟨Complex.arg u, Complex.arg_mem_Ioc u, ?_⟩
  have hueq : Complex.exp ((Complex.arg u : ℂ) * I) = u := by
    have h := Complex.norm_mul_exp_arg_mul_I u
    rwa [hunorm, Complex.ofReal_one, one_mul] at h
  have hcancel : Complex.exp ((α : ℂ) * I) * Complex.exp (((-α : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    have hz : (α : ℂ) * I + ((-α : ℝ) : ℂ) * I = 0 := by push_cast; ring
    rw [hz, Complex.exp_zero]
  show z₀ + (ρ : ℂ) * Complex.exp (((α + π + Complex.arg u : ℝ) : ℂ) * I) = w
  have hsplit : ((α + π + Complex.arg u : ℝ) : ℂ) * I
      = (α : ℂ) * I + (π : ℂ) * I + (Complex.arg u : ℂ) * I := by push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, hueq, hu_def]
  rw [show (ρ : ℂ) * (Complex.exp ((α : ℂ) * I) * -1 *
        (-Complex.exp (((-α : ℝ) : ℂ) * I) * (w - z₀) / (ρ : ℂ)))
      = (w - z₀) * (Complex.exp ((α : ℂ) * I) * Complex.exp (((-α : ℝ) : ℂ) * I)) *
        ((ρ : ℂ) / (ρ : ℂ)) from by ring,
    div_self hρC, mul_one, hcancel, mul_one]
  ring

/-- Glue: from a derivative/integrability bound on `f ∘ c` near the right endpoint `r`, plus
`c` continuous and injective on `Icc l r`, get the limit of `f` along `𝓝[c '' Ioo l r] (c r)`. -/
theorem exists_tendsto_nhdsWithin_image_Ioo_of_hasDerivAt {f : ℂ → ℂ} {c c' : ℝ → ℂ} {l r : ℝ}
    (hlr : l < r) (hderiv : ∀ s ∈ Ioo l r, HasDerivAt (f ∘ c) (c' s) s)
    (hcont' : ContinuousOn c' (Ioo l r)) (hint : IntegrableOn (fun s => ‖c' s‖) (Ioo l r))
    (hcCont : ContinuousOn c (Icc l r)) (hcInj : InjOn c (Icc l r)) :
    ∃ a, Tendsto f (𝓝[c '' Ioo l r] (c r)) (𝓝 a) := by
  obtain ⟨a, ha⟩ := exists_tendsto_nhdsLT_of_integrableOn_norm_deriv hlr hderiv hcont' hint
  set ψ := Function.invFunOn c (Icc l r) with hψ_def
  have hψcont : ContinuousOn ψ (c '' Icc l r) :=
    continuousOn_invFunOn_of_continuousOn_injOn hcCont hcInj
  have hleft : ∀ s ∈ Icc l r, ψ (c s) = s := hcInj.leftInvOn_invFunOn
  refine ⟨a, ?_⟩
  have hsub1 : c '' Ioo l r ⊆ c '' Icc l r := Set.image_mono Ioo_subset_Icc_self
  have hrmem : r ∈ Icc l r := right_mem_Icc.mpr hlr.le
  have hψS : ContinuousWithinAt ψ (c '' Ioo l r) (c r) :=
    (hψcont (c r) (mem_image_of_mem c hrmem)).mono hsub1
  have hψval : ψ (c r) = r := hleft r hrmem
  have hψS' : Tendsto ψ (𝓝[c '' Ioo l r] (c r)) (𝓝 (ψ (c r))) := hψS
  rw [hψval] at hψS'
  have hψtendsto : Tendsto ψ (𝓝[c '' Ioo l r] (c r)) (𝓝[<] r) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hψS', ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨s, hs, rfl⟩ := hw
    rw [hleft s (Ioo_subset_Icc_self hs)]
    exact hs.2
  have hcomp : Tendsto (f ∘ c ∘ ψ) (𝓝[c '' Ioo l r] (c r)) (𝓝 a) := ha.comp hψtendsto
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨s, hs, rfl⟩ := hw
  simp only [Function.comp_apply]
  rw [hleft s (Ioo_subset_Icc_self hs)]

/-- **C1** one-sided limits at the two ends of a circular arc of finite image length. -/
theorem exists_tendsto_circleArc_end_of_arcLength_ne_top {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hlen : arcLength f z₀ ρ ≠ ⊤) {p : ℂ} (hp : ‖p‖ = 1) (hpρ : ‖p - z₀‖ = ρ) :
    ∃ a : ℂ, Tendsto f (𝓝[unitDisc ∩ sphere z₀ ρ] p) (𝓝 a) := by
  have hΔo : IsOpen unitDisc := isOpen_ball
  set α := Complex.arg z₀ with hα_def
  set β₀ := Real.arccos (ρ / 2) with hβ₀_def
  have hβ₀0 : 0 < β₀ := Real.arccos_pos.mpr (by linarith)
  have hβ₀π : β₀ < π := Real.arccos_lt_pi.mpr (by linarith)
  have hcosβ₀ : Real.cos β₀ = ρ / 2 := Real.cos_arccos (by linarith) (by linarith)
  set c : ℝ → ℂ := fun s => circleMap z₀ ρ (α + π + s) with hc_def
  have hc_sphere : ∀ s, c s ∈ sphere z₀ ρ := fun s => circleMap_mem_sphere z₀ hρ0.le _
  have hc_normsq : ∀ s, ‖c s‖ ^ 2 = 1 - 2 * ρ * Real.cos s + ρ ^ 2 :=
    fun s => norm_sq_circleMap_arg_add_pi_add hz₀ ρ s
  have hβmem : β₀ ∈ Icc (0 : ℝ) π := ⟨hβ₀0.le, hβ₀π.le⟩
  have hcos_iff_mem : ∀ s ∈ Ioc (-π) π, (c s ∈ unitDisc ↔ s ∈ Ioo (-β₀) β₀) := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg s, abs_le.mpr ⟨by linarith [hs.1], hs.2⟩⟩
    have hkey : Real.cos β₀ < Real.cos |s| ↔ |s| < β₀ :=
      Real.strictAntiOn_cos.lt_iff_gt hβmem habs
    rw [Real.cos_abs] at hkey
    rw [unitDisc, mem_ball_zero_iff, ← abs_of_nonneg (norm_nonneg (c s)),
      ← sq_lt_one_iff_abs_lt_one, hc_normsq]
    constructor
    · intro h1
      have h2 : Real.cos β₀ < Real.cos s := by rw [hcosβ₀]; nlinarith
      exact abs_lt.mp (hkey.mp h2)
    · intro hmem
      have h2 : Real.cos β₀ < Real.cos s := hkey.mpr (abs_lt.mpr hmem)
      rw [hcosβ₀] at h2; nlinarith
  have hIooβ_sub : Ioo (-β₀) β₀ ⊆ Ioc (-π) π := fun s hs =>
    ⟨lt_trans (by linarith) hs.1, le_of_lt (lt_trans hs.2 hβ₀π)⟩
  have hS_eq : unitDisc ∩ sphere z₀ ρ = c '' Ioo (-β₀) β₀ := by
    apply Subset.antisymm
    · rintro w ⟨hw1, hw2⟩
      obtain ⟨s, hs_mem, hcs_eq⟩ := exists_mem_Ioc_circleMap_arg_add_pi_add hρ0 hw2
      have hcs_eq' : c s = w := hcs_eq
      exact ⟨s, (hcos_iff_mem s hs_mem).mp (hcs_eq' ▸ hw1), hcs_eq⟩
    · rintro w ⟨s, hs, rfl⟩
      exact ⟨(hcos_iff_mem s (hIooβ_sub hs)).mpr hs, hc_sphere s⟩
  have hp_sphere : p ∈ sphere z₀ ρ := by rw [Metric.mem_sphere, Complex.dist_eq]; exact hpρ
  obtain ⟨s_p, hsp_mem, hcsp_eq⟩ := exists_mem_Ioc_circleMap_arg_add_pi_add hρ0 hp_sphere
  have hcsp_eq' : c s_p = p := hcsp_eq
  have hcsp_norm : ‖c s_p‖ = 1 := by rw [hcsp_eq']; exact hp
  have hcoss_p : Real.cos s_p = ρ / 2 := by
    have h1 := hc_normsq s_p; rw [hcsp_norm] at h1; nlinarith
  have habsp : |s_p| ∈ Icc (0 : ℝ) π :=
    ⟨abs_nonneg s_p, abs_le.mpr ⟨by linarith [hsp_mem.1], hsp_mem.2⟩⟩
  have hcosβ₀eqs : Real.cos β₀ = Real.cos |s_p| := by rw [Real.cos_abs, hcoss_p, hcosβ₀]
  have habseq : |s_p| = β₀ := (Real.strictAntiOn_cos.eq_iff_eq hβmem habsp).mp hcosβ₀eqs
  have hsp_cases : s_p = β₀ ∨ s_p = -β₀ := (abs_eq hβ₀0.le).mp habseq
  have hp_cases : p = c β₀ ∨ p = c (-β₀) := by
    rcases hsp_cases with h | h
    · left; rw [← hcsp_eq, h]
    · right; rw [← hcsp_eq, h]
  have hc_hasDerivAt : ∀ s : ℝ, HasDerivAt c (circleMap 0 ρ (α + π + s) * I) s :=
    fun s => (hasDerivAt_circleMap z₀ ρ (α + π + s)).comp_const_add (α + π) s
  have hc_cont : Continuous c :=
    (continuous_circleMap z₀ ρ).comp (continuous_const.add continuous_id)
  have hc_deriv_norm : ∀ s : ℝ, ‖circleMap 0 ρ (α + π + s) * I‖ = ρ := by
    intro s; rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ0]
  have hderivf_cont : ContinuousOn (deriv f) unitDisc :=
    ((hf.analyticOnNhd hΔo).deriv.differentiableOn).continuousOn
  have hfc_hasDerivAt : ∀ s ∈ Ioo (-β₀) β₀,
      HasDerivAt (f ∘ c) (deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)) s := by
    intro s hs
    have hcsmem : c s ∈ unitDisc := (hcos_iff_mem s (hIooβ_sub hs)).mpr hs
    have hf_deriv : HasDerivAt f (deriv f (c s)) (c s) :=
      (hf.differentiableAt (hΔo.mem_nhds hcsmem)).hasDerivAt
    exact hf_deriv.comp s (hc_hasDerivAt s)
  have hcircshift_cont : Continuous (fun s : ℝ => circleMap 0 ρ (α + π + s)) :=
    (continuous_circleMap 0 ρ).comp (continuous_const.add continuous_id)
  have hfc'_cont : ContinuousOn (fun s => deriv f (c s) * (circleMap 0 ρ (α + π + s) * I))
      (Ioo (-β₀) β₀) := by
    apply ContinuousOn.mul
    · exact hderivf_cont.comp hc_cont.continuousOn
        fun s hs => (hcos_iff_mem s (hIooβ_sub hs)).mpr hs
    · exact (hcircshift_cont.mul continuous_const).continuousOn
  have hTmeas : MeasurableSet {θ : ℝ | circleMap z₀ ρ θ ∈ unitDisc} :=
    (continuous_circleMap z₀ ρ).measurable measurableSet_ball
  set g : ℝ → ℝ≥0∞ := fun θ => ‖deriv f (circleMap z₀ ρ θ)‖ₑ * ENNReal.ofReal ρ with hg_def
  have hg_meas : Measurable g :=
    ((measurable_deriv f).comp (continuous_circleMap z₀ ρ).measurable).enorm.mul_const _
  set h : ℝ → ℝ≥0∞ := fun θ => {θ : ℝ | circleMap z₀ ρ θ ∈ unitDisc}.indicator g θ with hh_def
  have hh_meas : Measurable h := hg_meas.indicator hTmeas
  have hh_per : Function.Periodic h (2 * π) := by
    intro θ
    show {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g (θ + 2 * π)
      = {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g θ
    by_cases hθ : circleMap z₀ ρ θ ∈ unitDisc
    · have hθ' : θ ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := hθ
      have hθ2 : θ + 2 * π ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := by
        show circleMap z₀ ρ (θ + 2 * π) ∈ unitDisc; rw [periodic_circleMap z₀ ρ θ]; exact hθ
      rw [Set.indicator_of_mem hθ2, Set.indicator_of_mem hθ', hg_def]
      simp only [periodic_circleMap z₀ ρ θ]
    · have hθ' : θ ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := hθ
      have hθ2 : θ + 2 * π ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := by
        show circleMap z₀ ρ (θ + 2 * π) ∉ unitDisc; rw [periodic_circleMap z₀ ρ θ]; exact hθ
      rw [Set.indicator_of_notMem hθ2, Set.indicator_of_notMem hθ']
  have harcLength_eq : arcLength f z₀ ρ = ∫⁻ θ in Ioc (-π) π, h θ := by
    unfold arcLength
    rw [hh_def]
    rw [MeasureTheory.lintegral_indicator hTmeas, Measure.restrict_restrict hTmeas]
    congr 2
    ext θ
    simp only [mem_inter_iff, mem_setOf_eq]
    tauto
  have hshift_eq : ∫⁻ θ in Ioc (-π) π, h θ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by
    have hshift := lintegral_Ioc_two_pi_shift hh_meas hh_per
      (show α ∈ Ioc (-π) π from Complex.arg_mem_Ioc z₀)
    have hchg : ∫⁻ θ in Ioc α (α + 2 * π), h θ = ∫⁻ s in Ioc (-π) π, h (s + α + π) := by
      have hg' : Measurable (fun s : ℝ => s + α + π) := (measurable_id.add_const α).add_const π
      have hmap : Measure.map (fun s : ℝ => s + α + π) volume = volume := by
        rw [show (fun s : ℝ => s + α + π) = (fun s => s + (α + π)) from by funext s; ring]
        exact map_add_right_eq_self volume (α + π)
      have hpre : (fun s : ℝ => s + α + π) ⁻¹' Ioc α (α + 2 * π) = Ioc (-π) π := by
        ext s
        simp only [mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [← hpre, ← setLIntegral_map measurableSet_Ioc hh_meas hg', hmap]
    rw [← hshift, hchg]
    have hset_eq : {s : ℝ | s ∈ Ioc (-π) π ∧ c s ∈ unitDisc} = Ioo (-β₀) β₀ := by
      ext s
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact (hcos_iff_mem s h1).mp h2
      · intro h1; exact ⟨hIooβ_sub h1, (hcos_iff_mem s (hIooβ_sub h1)).mpr h1⟩
    have hcmeas : MeasurableSet {s : ℝ | c s ∈ unitDisc} := hc_cont.measurable measurableSet_ball
    have hpt : ∀ s : ℝ, h (s + α + π)
        = {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s := by
      intro s
      show {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g (s + α + π)
        = {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s
      have hcs_eq : s + α + π = α + π + s := by ring
      by_cases hmem : c s ∈ unitDisc
      · have hmem' : s ∈ {s : ℝ | c s ∈ unitDisc} := hmem
        rw [Set.indicator_of_mem hmem',
          Set.indicator_of_mem (show s + α + π ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} by
            show circleMap z₀ ρ (s + α + π) ∈ unitDisc; rw [hcs_eq]; exact hmem),
          hcs_eq]
      · have hmem' : s ∉ {s : ℝ | c s ∈ unitDisc} := hmem
        rw [Set.indicator_of_notMem hmem',
          Set.indicator_of_notMem (show s + α + π ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} by
            show circleMap z₀ ρ (s + α + π) ∉ unitDisc; rw [hcs_eq]; exact hmem)]
    calc ∫⁻ s in Ioc (-π) π, h (s + α + π)
        = ∫⁻ s in Ioc (-π) π, {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s := by
          congr 1; funext s; exact hpt s
      _ = ∫⁻ s in {s : ℝ | s ∈ Ioc (-π) π ∧ c s ∈ unitDisc}, g (α + π + s) := by
          rw [MeasureTheory.lintegral_indicator hcmeas, Measure.restrict_restrict hcmeas]
          congr 2
          ext s
          simp only [mem_inter_iff, mem_setOf_eq]
          tauto
      _ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by rw [hset_eq]
  have harcLength_final : arcLength f z₀ ρ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by
    rw [harcLength_eq, hshift_eq]
  have hlintegral_ne_top : ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) ≠ ⊤ := harcLength_final ▸ hlen
  have hint_transfer_c : IntegrableOn (fun s => deriv f (c s) * (circleMap 0 ρ (α + π + s) * I))
      (Ioo (-β₀) β₀) := by
    have hpt2 : (fun s => ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖ₑ)
        = fun s => g (α + π + s) := by
      funext s
      have hnorm_e : ‖circleMap 0 ρ (α + π + s) * I‖ₑ = ENNReal.ofReal ρ := by
        rw [← ofReal_norm, hc_deriv_norm]
      rw [enorm_mul, hg_def, hnorm_e]
    refine ⟨(hfc'_cont.aestronglyMeasurable measurableSet_Ioo), ?_⟩
    show ∫⁻ s in Ioo (-β₀) β₀, ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖ₑ < ⊤
    rw [hpt2]
    exact lt_top_iff_ne_top.mpr hlintegral_ne_top
  have hint_transfer : IntegrableOn (fun s => ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖)
      (Ioo (-β₀) β₀) := hint_transfer_c.integrable.norm
  have hβlt : (-β₀ : ℝ) < β₀ := by linarith
  have hc_inj : InjOn c (Icc (-β₀) β₀) := by
    intro s hs t ht hst
    have h1 : |(α + π + s) - (α + π + t)| < 2 * π := by
      have h2 : |s - t| ≤ 2 * β₀ := by
        rw [abs_le]
        constructor <;> [linarith [hs.1, ht.2]; linarith [hs.2, ht.1]]
      calc |(α + π + s) - (α + π + t)| = |s - t| := by congr 1; ring
        _ ≤ 2 * β₀ := h2
        _ < 2 * π := by linarith
    have h2 : α + π + s = α + π + t := eq_of_circleMap_eq hρ0.ne' h1 hst
    linarith
  obtain ⟨a₁, ha₁⟩ := exists_tendsto_nhdsWithin_image_Ioo_of_hasDerivAt hβlt hfc_hasDerivAt
    hfc'_cont hint_transfer hc_cont.continuousOn hc_inj
  have hneg_mapsto : MapsTo (Neg.neg : ℝ → ℝ) (Icc (-β₀) β₀) (Icc (-β₀) β₀) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hneg_mapsto_Ioo : MapsTo (Neg.neg : ℝ → ℝ) (Ioo (-β₀) β₀) (Ioo (-β₀) β₀) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hc₂_hasDerivAt : ∀ s ∈ Ioo (-β₀) β₀, HasDerivAt (f ∘ fun s => c (-s))
      (-(deriv f (c (-s)) * (circleMap 0 ρ (α + π + (-s)) * I))) s := by
    intro s hs
    have h1 := (hfc_hasDerivAt (-s) (hneg_mapsto_Ioo hs)).scomp s (hasDerivAt_neg s)
    rw [neg_one_smul] at h1
    exact h1
  have hfc₂'_cont : ContinuousOn
      (fun s => -(deriv f (c (-s)) * (circleMap 0 ρ (α + π + (-s)) * I))) (Ioo (-β₀) β₀) :=
    (hfc'_cont.comp continuous_neg.continuousOn hneg_mapsto_Ioo).neg
  have hint_transfer₂ : IntegrableOn
      (fun s => ‖-(deriv f (c (-s)) * (circleMap 0 ρ (α + π + (-s)) * I))‖) (Ioo (-β₀) β₀) := by
    simp only [norm_neg]
    have hemb : MeasurableEmbedding (Neg.neg : ℝ → ℝ) := (Homeomorph.neg ℝ).measurableEmbedding
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      Measure.measurePreserving_neg volume
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioo (-β₀) β₀ = Ioo (-β₀) β₀ := by
      ext s
      simp only [mem_preimage, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have hkey := hmp.integrableOn_comp_preimage hemb
      (f := fun s => ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖) (s := Ioo (-β₀) β₀)
    rw [hpre] at hkey
    exact hkey.mpr hint_transfer
  have hc₂_cont : ContinuousOn (fun s => c (-s)) (Icc (-β₀) β₀) :=
    hc_cont.continuousOn.comp continuous_neg.continuousOn hneg_mapsto
  have hc₂_inj : InjOn (fun s => c (-s)) (Icc (-β₀) β₀) := by
    intro s hs t ht hst
    have h1 : -s = -t := hc_inj (hneg_mapsto hs) (hneg_mapsto ht) hst
    linarith
  obtain ⟨a₂, ha₂⟩ := exists_tendsto_nhdsWithin_image_Ioo_of_hasDerivAt hβlt hc₂_hasDerivAt
    hfc₂'_cont hint_transfer₂ hc₂_cont hc₂_inj
  have himg_eq : (fun s => c (-s)) '' Ioo (-β₀) β₀ = c '' Ioo (-β₀) β₀ := by
    apply Subset.antisymm
    · rintro w ⟨s, hs, rfl⟩; exact ⟨-s, hneg_mapsto_Ioo hs, rfl⟩
    · rintro w ⟨s, hs, rfl⟩; exact ⟨-s, hneg_mapsto_Ioo hs, by simp⟩
  rw [himg_eq] at ha₂
  rw [hS_eq]
  rcases hp_cases with h | h
  · rw [h]; exact ⟨a₁, ha₁⟩
  · rw [h]; exact ⟨a₂, ha₂⟩


/-- Any two points on a curve with `HasDerivAt`+integrable-norm derivative are within the total
integral of the norm of the derivative. -/
theorem dist_le_integral_norm_deriv {g g' : ℝ → ℂ} {l r : ℝ}
    (hderiv : ∀ s ∈ Ioo l r, HasDerivAt g (g' s) s) (hcont' : ContinuousOn g' (Ioo l r))
    (hint : IntegrableOn (fun s => ‖g' s‖) (Ioo l r)) {s t : ℝ} (hs : s ∈ Ioo l r)
    (ht : t ∈ Ioo l r) :
    dist (g s) (g t) ≤ ∫ x in Ioo l r, ‖g' x‖ := by
  have hg'int : IntegrableOn g' (Ioo l r) :=
    ⟨hcont'.aestronglyMeasurable measurableSet_Ioo, (hasFiniteIntegral_norm_iff g').mp hint.2⟩
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm]; exact this ht hs (not_le.mp hst).le
  have hIcc_sub : Icc s t ⊆ Ioo l r := fun x hx => ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
  have huIcc : uIcc s t = Icc s t := uIcc_of_le hst
  have hderiv' : ∀ x ∈ uIcc s t, HasDerivAt g (g' x) x := by
    rw [huIcc]; exact fun x hx => hderiv x (hIcc_sub hx)
  have hintegrable' : IntervalIntegrable g' volume s t := by
    apply IntegrableOn.intervalIntegrable
    rw [huIcc]; exact hg'int.mono_set hIcc_sub
  have hftc : ∫ x in s..t, g' x = g t - g s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hintegrable'
  have hnorm : ‖g t - g s‖ ≤ ∫ x in s..t, ‖g' x‖ :=
    hftc ▸ intervalIntegral.norm_integral_le_integral_norm hst
  have hmono : ∫ x in Ioc s t, ‖g' x‖ ≤ ∫ x in Ioo l r, ‖g' x‖ :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (LE.le.eventuallySubset (fun x hx => hIcc_sub ⟨hx.1.le, hx.2⟩))
  have heq : ∫ x in s..t, ‖g' x‖ = ∫ x in Ioc s t, ‖g' x‖ := intervalIntegral.integral_of_le hst
  calc dist (g s) (g t) = ‖g t - g s‖ := by rw [dist_comm]; exact Complex.dist_eq _ _
    _ ≤ ∫ x in s..t, ‖g' x‖ := hnorm
    _ = ∫ x in Ioc s t, ‖g' x‖ := heq
    _ ≤ ∫ x in Ioo l r, ‖g' x‖ := hmono

/-- **C3** (corrected (c)) ends of the image of a finite-length circular arc: a genuine arc if the
ends differ, a Jordan loop if they coincide; plus the diameter bound. -/
theorem exists_ends_of_circleArc_image {f : ℂ → ℂ} {Ω : Set ℂ} (hΩbdd : Bornology.IsBounded Ω)
    (hf : IsConformalOnto f unitDisc Ω) {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hlen : arcLength f z₀ ρ ≠ ⊤) :
    ∃ a b : ℂ, a ∈ frontier Ω ∧ b ∈ frontier Ω ∧
      Metric.diam (f '' (unitDisc ∩ sphere z₀ ρ)) ≤ (arcLength f z₀ ρ).toReal ∧
      ((a ≠ b ∧ IsArcEndC (f '' (unitDisc ∩ sphere z₀ ρ) ∪ {a, b}) a b) ∨
        (a = b ∧ IsJordanCurve (toExt (f '' (unitDisc ∩ sphere z₀ ρ) ∪ {a})))) := by
  have hfdiff := hf.1
  have hfinj := hf.2.1
  have hfrange := hf.2.2
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔo
  set α := Complex.arg z₀ with hα_def
  set β₀ := Real.arccos (ρ / 2) with hβ₀_def
  have hβ₀0 : 0 < β₀ := Real.arccos_pos.mpr (by linarith)
  have hβ₀π : β₀ < π := Real.arccos_lt_pi.mpr (by linarith)
  have hcosβ₀ : Real.cos β₀ = ρ / 2 := Real.cos_arccos (by linarith) (by linarith)
  set c : ℝ → ℂ := fun s => circleMap z₀ ρ (α + π + s) with hc_def
  have hc_sphere : ∀ s, c s ∈ sphere z₀ ρ := fun s => circleMap_mem_sphere z₀ hρ0.le _
  have hc_normsq : ∀ s, ‖c s‖ ^ 2 = 1 - 2 * ρ * Real.cos s + ρ ^ 2 :=
    fun s => norm_sq_circleMap_arg_add_pi_add hz₀ ρ s
  have hβmem : β₀ ∈ Icc (0 : ℝ) π := ⟨hβ₀0.le, hβ₀π.le⟩
  have hcos_iff_mem : ∀ s ∈ Ioc (-π) π, (c s ∈ unitDisc ↔ s ∈ Ioo (-β₀) β₀) := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg s, abs_le.mpr ⟨by linarith [hs.1], hs.2⟩⟩
    have hkey : Real.cos β₀ < Real.cos |s| ↔ |s| < β₀ :=
      Real.strictAntiOn_cos.lt_iff_gt hβmem habs
    rw [Real.cos_abs] at hkey
    rw [unitDisc, mem_ball_zero_iff, ← abs_of_nonneg (norm_nonneg (c s)),
      ← sq_lt_one_iff_abs_lt_one, hc_normsq]
    constructor
    · intro h1
      have h2 : Real.cos β₀ < Real.cos s := by rw [hcosβ₀]; nlinarith
      exact abs_lt.mp (hkey.mp h2)
    · intro hmem
      have h2 : Real.cos β₀ < Real.cos s := hkey.mpr (abs_lt.mpr hmem)
      rw [hcosβ₀] at h2; nlinarith
  have hIooβ_sub : Ioo (-β₀) β₀ ⊆ Ioc (-π) π := fun s hs =>
    ⟨lt_trans (by linarith) hs.1, le_of_lt (lt_trans hs.2 hβ₀π)⟩
  have hS_eq : unitDisc ∩ sphere z₀ ρ = c '' Ioo (-β₀) β₀ := by
    apply Subset.antisymm
    · rintro w ⟨hw1, hw2⟩
      obtain ⟨s, hs_mem, hcs_eq⟩ := exists_mem_Ioc_circleMap_arg_add_pi_add hρ0 hw2
      have hcs_eq' : c s = w := hcs_eq
      exact ⟨s, (hcos_iff_mem s hs_mem).mp (hcs_eq' ▸ hw1), hcs_eq⟩
    · rintro w ⟨s, hs, rfl⟩
      exact ⟨(hcos_iff_mem s (hIooβ_sub hs)).mpr hs, hc_sphere s⟩
  have hc_hasDerivAt : ∀ s : ℝ, HasDerivAt c (circleMap 0 ρ (α + π + s) * I) s :=
    fun s => (hasDerivAt_circleMap z₀ ρ (α + π + s)).comp_const_add (α + π) s
  have hc_cont : Continuous c :=
    (continuous_circleMap z₀ ρ).comp (continuous_const.add continuous_id)
  have hc_deriv_norm : ∀ s : ℝ, ‖circleMap 0 ρ (α + π + s) * I‖ = ρ := by
    intro s; rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ0]
  have hderivf_cont : ContinuousOn (deriv f) unitDisc :=
    ((hfdiff.analyticOnNhd hΔo).deriv.differentiableOn).continuousOn
  have hfc_hasDerivAt : ∀ s ∈ Ioo (-β₀) β₀,
      HasDerivAt (f ∘ c) (deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)) s := by
    intro s hs
    have hcsmem : c s ∈ unitDisc := (hcos_iff_mem s (hIooβ_sub hs)).mpr hs
    have hf_deriv : HasDerivAt f (deriv f (c s)) (c s) :=
      (hfdiff.differentiableAt (hΔo.mem_nhds hcsmem)).hasDerivAt
    exact hf_deriv.comp s (hc_hasDerivAt s)
  have hcircshift_cont : Continuous (fun s : ℝ => circleMap 0 ρ (α + π + s)) :=
    (continuous_circleMap 0 ρ).comp (continuous_const.add continuous_id)
  have hfc'_cont : ContinuousOn (fun s => deriv f (c s) * (circleMap 0 ρ (α + π + s) * I))
      (Ioo (-β₀) β₀) := by
    apply ContinuousOn.mul
    · exact hderivf_cont.comp hc_cont.continuousOn
        fun s hs => (hcos_iff_mem s (hIooβ_sub hs)).mpr hs
    · exact (hcircshift_cont.mul continuous_const).continuousOn
  have hTmeas : MeasurableSet {θ : ℝ | circleMap z₀ ρ θ ∈ unitDisc} :=
    (continuous_circleMap z₀ ρ).measurable measurableSet_ball
  set g : ℝ → ℝ≥0∞ := fun θ => ‖deriv f (circleMap z₀ ρ θ)‖ₑ * ENNReal.ofReal ρ with hg_def
  have hg_meas : Measurable g :=
    ((measurable_deriv f).comp (continuous_circleMap z₀ ρ).measurable).enorm.mul_const _
  set h : ℝ → ℝ≥0∞ := fun θ => {θ : ℝ | circleMap z₀ ρ θ ∈ unitDisc}.indicator g θ with hh_def
  have hh_meas : Measurable h := hg_meas.indicator hTmeas
  have hh_per : Function.Periodic h (2 * π) := by
    intro θ
    show {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g (θ + 2 * π)
      = {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g θ
    by_cases hθ : circleMap z₀ ρ θ ∈ unitDisc
    · have hθ' : θ ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := hθ
      have hθ2 : θ + 2 * π ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := by
        show circleMap z₀ ρ (θ + 2 * π) ∈ unitDisc; rw [periodic_circleMap z₀ ρ θ]; exact hθ
      rw [Set.indicator_of_mem hθ2, Set.indicator_of_mem hθ', hg_def]
      simp only [periodic_circleMap z₀ ρ θ]
    · have hθ' : θ ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := hθ
      have hθ2 : θ + 2 * π ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} := by
        show circleMap z₀ ρ (θ + 2 * π) ∉ unitDisc; rw [periodic_circleMap z₀ ρ θ]; exact hθ
      rw [Set.indicator_of_notMem hθ2, Set.indicator_of_notMem hθ']
  have harcLength_eq : arcLength f z₀ ρ = ∫⁻ θ in Ioc (-π) π, h θ := by
    unfold arcLength
    rw [hh_def]
    rw [MeasureTheory.lintegral_indicator hTmeas, Measure.restrict_restrict hTmeas]
    congr 2
    ext θ
    simp only [mem_inter_iff, mem_setOf_eq]
    tauto
  have hshift_eq : ∫⁻ θ in Ioc (-π) π, h θ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by
    have hshift := lintegral_Ioc_two_pi_shift hh_meas hh_per
      (show α ∈ Ioc (-π) π from Complex.arg_mem_Ioc z₀)
    have hchg : ∫⁻ θ in Ioc α (α + 2 * π), h θ = ∫⁻ s in Ioc (-π) π, h (s + α + π) := by
      have hg' : Measurable (fun s : ℝ => s + α + π) := (measurable_id.add_const α).add_const π
      have hmap : Measure.map (fun s : ℝ => s + α + π) volume = volume := by
        rw [show (fun s : ℝ => s + α + π) = (fun s => s + (α + π)) from by funext s; ring]
        exact map_add_right_eq_self volume (α + π)
      have hpre : (fun s : ℝ => s + α + π) ⁻¹' Ioc α (α + 2 * π) = Ioc (-π) π := by
        ext s
        simp only [mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [← hpre, ← setLIntegral_map measurableSet_Ioc hh_meas hg', hmap]
    rw [← hshift, hchg]
    have hset_eq : {s : ℝ | s ∈ Ioc (-π) π ∧ c s ∈ unitDisc} = Ioo (-β₀) β₀ := by
      ext s
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact (hcos_iff_mem s h1).mp h2
      · intro h1; exact ⟨hIooβ_sub h1, (hcos_iff_mem s (hIooβ_sub h1)).mpr h1⟩
    have hcmeas : MeasurableSet {s : ℝ | c s ∈ unitDisc} := hc_cont.measurable measurableSet_ball
    have hpt : ∀ s : ℝ, h (s + α + π)
        = {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s := by
      intro s
      show {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc}.indicator g (s + α + π)
        = {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s
      have hcs_eq : s + α + π = α + π + s := by ring
      by_cases hmem : c s ∈ unitDisc
      · have hmem' : s ∈ {s : ℝ | c s ∈ unitDisc} := hmem
        rw [Set.indicator_of_mem hmem',
          Set.indicator_of_mem (show s + α + π ∈ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} by
            show circleMap z₀ ρ (s + α + π) ∈ unitDisc; rw [hcs_eq]; exact hmem),
          hcs_eq]
      · have hmem' : s ∉ {s : ℝ | c s ∈ unitDisc} := hmem
        rw [Set.indicator_of_notMem hmem',
          Set.indicator_of_notMem (show s + α + π ∉ {θ' : ℝ | circleMap z₀ ρ θ' ∈ unitDisc} by
            show circleMap z₀ ρ (s + α + π) ∉ unitDisc; rw [hcs_eq]; exact hmem)]
    calc ∫⁻ s in Ioc (-π) π, h (s + α + π)
        = ∫⁻ s in Ioc (-π) π, {s : ℝ | c s ∈ unitDisc}.indicator (fun s => g (α + π + s)) s := by
          congr 1; funext s; exact hpt s
      _ = ∫⁻ s in {s : ℝ | s ∈ Ioc (-π) π ∧ c s ∈ unitDisc}, g (α + π + s) := by
          rw [MeasureTheory.lintegral_indicator hcmeas, Measure.restrict_restrict hcmeas]
          congr 2
          ext s
          simp only [mem_inter_iff, mem_setOf_eq]
          tauto
      _ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by rw [hset_eq]
  have harcLength_final : arcLength f z₀ ρ = ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) := by
    rw [harcLength_eq, hshift_eq]
  have hlintegral_ne_top : ∫⁻ s in Ioo (-β₀) β₀, g (α + π + s) ≠ ⊤ := harcLength_final ▸ hlen
  have hpt2 : ∀ s, ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖ₑ = g (α + π + s) := by
    intro s
    have hnorm_e : ‖circleMap 0 ρ (α + π + s) * I‖ₑ = ENNReal.ofReal ρ := by
      rw [← ofReal_norm, hc_deriv_norm]
    rw [enorm_mul, hg_def, hnorm_e]
  have hint_transfer_c : IntegrableOn (fun s => deriv f (c s) * (circleMap 0 ρ (α + π + s) * I))
      (Ioo (-β₀) β₀) := by
    refine ⟨(hfc'_cont.aestronglyMeasurable measurableSet_Ioo), ?_⟩
    show ∫⁻ s in Ioo (-β₀) β₀, ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖ₑ < ⊤
    rw [show (fun s => ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖ₑ) = fun s => g (α + π + s)
      from funext hpt2]
    exact lt_top_iff_ne_top.mpr hlintegral_ne_top
  have hint_transfer : IntegrableOn (fun s => ‖deriv f (c s) * (circleMap 0 ρ (α + π + s) * I)‖)
      (Ioo (-β₀) β₀) := hint_transfer_c.integrable.norm
  have hβlt : (-β₀ : ℝ) < β₀ := by linarith
  have hc_inj : InjOn c (Icc (-β₀) β₀) := by
    intro s hs t ht hst
    have h1 : |(α + π + s) - (α + π + t)| < 2 * π := by
      have h2 : |s - t| ≤ 2 * β₀ := by
        rw [abs_le]
        constructor <;> [linarith [hs.1, ht.2]; linarith [hs.2, ht.1]]
      calc |(α + π + s) - (α + π + t)| = |s - t| := by congr 1; ring
        _ ≤ 2 * β₀ := h2
        _ < 2 * π := by linarith
    have h2 : α + π + s = α + π + t := eq_of_circleMap_eq hρ0.ne' h1 hst
    linarith
  -- the two endpoint limits, via the already-proven C1 theorem
  have hcβ₀_norm : ‖c β₀‖ = 1 := by
    have h1 : ‖c β₀‖ ^ 2 = 1 := by rw [hc_normsq, hcosβ₀]; ring
    have h2 : ‖c β₀‖ = Real.sqrt (‖c β₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, Real.sqrt_one] at h2; exact h2
  have hcβ₀_sphere : ‖c β₀ - z₀‖ = ρ := by
    have h := hc_sphere β₀; rwa [Metric.mem_sphere, Complex.dist_eq] at h
  obtain ⟨a, ha⟩ := exists_tendsto_circleArc_end_of_arcLength_ne_top hfdiff hz₀ hρ0 hρ1 hlen
    hcβ₀_norm hcβ₀_sphere
  have hcnβ₀_norm : ‖c (-β₀)‖ = 1 := by
    have h1 : ‖c (-β₀)‖ ^ 2 = 1 := by rw [hc_normsq, Real.cos_neg, hcosβ₀]; ring
    have h2 : ‖c (-β₀)‖ = Real.sqrt (‖c (-β₀)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, Real.sqrt_one] at h2; exact h2
  have hcnβ₀_sphere : ‖c (-β₀) - z₀‖ = ρ := by
    have h := hc_sphere (-β₀); rwa [Metric.mem_sphere, Complex.dist_eq] at h
  obtain ⟨b, hb⟩ := exists_tendsto_circleArc_end_of_arcLength_ne_top hfdiff hz₀ hρ0 hρ1 hlen
    hcnβ₀_norm hcnβ₀_sphere
  -- frontier membership, via mem_closure_of_tendsto and C2 (properness)
  have hSΔ : unitDisc ∩ sphere z₀ ρ ⊆ unitDisc := inter_subset_left
  have hinv_tendsto : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have hmono : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono hmono (tendsto_natCast_atTop_atTop (R := ℝ))
    exact tendsto_inv_atTop_zero.comp h1
  -- sequence approaching c β₀ from within the arc, and its NeBot-witnessing tendsto-within
  set zna : ℕ → ℂ := fun n => c (β₀ - β₀ * ((n : ℝ) + 1)⁻¹) with hzna_def
  have hzna_mem : ∀ n : ℕ, zna n ∈ unitDisc := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), h1, h2]
    have hmem : β₀ - β₀ * ((n : ℝ) + 1)⁻¹ ∈ Ioo (-β₀) β₀ := ⟨by nlinarith, by nlinarith⟩
    exact (hcos_iff_mem _ (hIooβ_sub hmem)).mpr hmem
  have hzna_tendsto : Tendsto zna atTop (𝓝 (c β₀)) := by
    have hstend : Tendsto (fun n : ℕ => β₀ - β₀ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 β₀) := by
      have := (tendsto_const_nhds (x := β₀)).mul hinv_tendsto
      simp only [mul_zero] at this
      simpa using tendsto_const_nhds.sub this
    exact (hc_cont.continuousAt.tendsto).comp hstend
  have hzna_tendsto' : Tendsto zna atTop (𝓝[unitDisc ∩ sphere z₀ ρ] (c β₀)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzna_tendsto, Filter.Eventually.of_forall fun n => ⟨hzna_mem n, hc_sphere _⟩⟩
  haveI hNeBotA : (𝓝[unitDisc ∩ sphere z₀ ρ] (c β₀)).NeBot :=
    Filter.neBot_of_le hzna_tendsto'
  set znb : ℕ → ℂ := fun n => c (-β₀ + β₀ * ((n : ℝ) + 1)⁻¹) with hznb_def
  have hznb_mem : ∀ n : ℕ, znb n ∈ unitDisc := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), h1, h2]
    have hmem : -β₀ + β₀ * ((n : ℝ) + 1)⁻¹ ∈ Ioo (-β₀) β₀ := ⟨by nlinarith, by nlinarith⟩
    exact (hcos_iff_mem _ (hIooβ_sub hmem)).mpr hmem
  have hznb_tendsto : Tendsto znb atTop (𝓝 (c (-β₀))) := by
    have hstend : Tendsto (fun n : ℕ => -β₀ + β₀ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 (-β₀)) := by
      have := (tendsto_const_nhds (x := β₀)).mul hinv_tendsto
      simp only [mul_zero] at this
      simpa using tendsto_const_nhds.add this
    exact (hc_cont.continuousAt.tendsto).comp hstend
  have hznb_tendsto' : Tendsto znb atTop (𝓝[unitDisc ∩ sphere z₀ ρ] (c (-β₀))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hznb_tendsto, Filter.Eventually.of_forall fun n => ⟨hznb_mem n, hc_sphere _⟩⟩
  haveI hNeBotB : (𝓝[unitDisc ∩ sphere z₀ ρ] (c (-β₀))).NeBot :=
    Filter.neBot_of_le hznb_tendsto'
  have haΩc : a ∈ closure Ω := by
    apply mem_closure_of_tendsto ha
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hfrange ▸ ⟨z, hSΔ hz, rfl⟩
  have hbΩc : b ∈ closure Ω := by
    apply mem_closure_of_tendsto hb
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hfrange ▸ ⟨z, hSΔ hz, rfl⟩
  have haΩ : a ∉ Ω := by
    have hfa_tendsto : Tendsto (fun n => f (zna n)) atTop (𝓝 a) := ha.comp hzna_tendsto'
    exact tendsto_boundary_of_isConformalOnto hf hcβ₀_norm hzna_mem hzna_tendsto hfa_tendsto
  have hbΩ : b ∉ Ω := by
    have hfb_tendsto : Tendsto (fun n => f (znb n)) atTop (𝓝 b) := hb.comp hznb_tendsto'
    exact tendsto_boundary_of_isConformalOnto hf hcnβ₀_norm hznb_mem hznb_tendsto hfb_tendsto
  have ha_frontier : a ∈ frontier Ω := by rw [frontier, hΩo.interior_eq]; exact ⟨haΩc, haΩ⟩
  have hb_frontier : b ∈ frontier Ω := by rw [frontier, hΩo.interior_eq]; exact ⟨hbΩc, hbΩ⟩
  -- diameter bound
  have hdiam : Metric.diam (f '' (unitDisc ∩ sphere z₀ ρ)) ≤ (arcLength f z₀ ρ).toReal := by
    have hIntEq : ∫ x in Ioo (-β₀) β₀, ‖deriv f (c x) * (circleMap 0 ρ (α + π + x) * I)‖
        = (arcLength f z₀ ρ).toReal := by
      have hkey : ENNReal.ofReal
          (∫ x in Ioo (-β₀) β₀, ‖deriv f (c x) * (circleMap 0 ρ (α + π + x) * I)‖)
          = ∫⁻ x in Ioo (-β₀) β₀, ‖deriv f (c x) * (circleMap 0 ρ (α + π + x) * I)‖ₑ :=
        ofReal_integral_norm_eq_lintegral_enorm hint_transfer_c.integrable
      rw [show (fun x => ‖deriv f (c x) * (circleMap 0 ρ (α + π + x) * I)‖ₑ)
          = fun s => g (α + π + s) from funext hpt2] at hkey
      rw [← harcLength_final] at hkey
      have hnn : 0 ≤ ∫ x in Ioo (-β₀) β₀, ‖deriv f (c x) * (circleMap 0 ρ (α + π + x) * I)‖ :=
        MeasureTheory.integral_nonneg fun x => norm_nonneg _
      rw [← ENNReal.toReal_ofReal hnn, hkey]
    rw [hS_eq, ← hIntEq]
    rw [show f '' (c '' Ioo (-β₀) β₀) = (f ∘ c) '' Ioo (-β₀) β₀ from (image_comp f c _).symm]
    apply Metric.diam_le_of_forall_dist_le (MeasureTheory.integral_nonneg fun x => norm_nonneg _)
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    exact dist_le_integral_norm_deriv hfc_hasDerivAt hfc'_cont hint_transfer hs ht
  -- the loop/arc parametrization `F`
  have hFa_lim : Tendsto (fun s => f (c s)) (𝓝[<] β₀) (𝓝 a) := by
    apply ha.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (-β₀ : ℝ) < β₀ by linarith))]
      with s hs hs'
    exact ⟨(hcos_iff_mem s (hIooβ_sub ⟨hs', hs⟩)).mpr ⟨hs', hs⟩, hc_sphere s⟩
  have hFb_lim : Tendsto (fun s => f (c s)) (𝓝[>] (-β₀)) (𝓝 b) := by
    apply hb.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (-β₀ : ℝ) < β₀ by linarith))]
      with s hs hs'
    exact ⟨(hcos_iff_mem s (hIooβ_sub ⟨hs, hs'⟩)).mpr ⟨hs, hs'⟩, hc_sphere s⟩
  set H : ℝ → ℂ := fun u => f (c (β₀ - 2 * β₀ * u)) with hH_def
  set F : ℝ → ℂ := Function.update (Function.update H 0 a) 1 b with hF_def
  have hF0 : F 0 = a := by
    rw [hF_def, Function.update_of_ne (by norm_num : (0 : ℝ) ≠ 1), Function.update_self]
  have hF1 : F 1 = b := by rw [hF_def, Function.update_self]
  have hFH : ∀ u : ℝ, u ≠ 0 → u ≠ 1 → F u = H u := by
    intro u hu0 hu1
    rw [hF_def, Function.update_of_ne hu1, Function.update_of_ne hu0]
  have haffine_cont : Continuous (fun u : ℝ => β₀ - 2 * β₀ * u) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hH_tendsto_0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hcomp : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝[>] (0 : ℝ)) (𝓝[<] β₀) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝 (0 : ℝ)) (𝓝 β₀) := by
          have h2 := haffine_cont.continuousAt (x := (0 : ℝ))
          simpa [ContinuousAt] using h2
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Iio]; nlinarith [mem_Ioi.mp hu, hβ₀0]
    exact hFa_lim.comp hcomp
  have hH_tendsto_1 : Tendsto H (𝓝[<] (1 : ℝ)) (𝓝 b) := by
    have hcomp : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝[<] (1 : ℝ)) (𝓝[>] (-β₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝 (1 : ℝ)) (𝓝 (β₀ - 2 * β₀ * 1)) :=
          haffine_cont.continuousAt.tendsto
        have heq : β₀ - 2 * β₀ * (1 : ℝ) = -β₀ := by ring
        rw [heq] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Ioi]; nlinarith [mem_Iio.mp hu, hβ₀0]
    exact hFb_lim.comp hcomp
  have hfc_cont : ContinuousOn (f ∘ c) (Ioo (-β₀) β₀) := fun s hs =>
    (hfc_hasDerivAt s hs).continuousAt.continuousWithinAt
  have haffine_mapsTo : MapsTo (fun u : ℝ => β₀ - 2 * β₀ * u) (Ioo (0 : ℝ) 1) (Ioo (-β₀) β₀) :=
    fun u hu => ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
  have hHcont : ContinuousOn H (Ioo (0 : ℝ) 1) :=
    hfc_cont.comp haffine_cont.continuousOn haffine_mapsTo
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · -- u = 0
      have hu0' : u = 0 := hu0.symm
      subst hu0'
      rw [ContinuousWithinAt, hF0, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hH_tendsto_0 ε hε
      refine ⟨min δ₀ (1 / 2), by positivity, fun v hv hvd => ?_⟩
      rw [Real.dist_eq, sub_zero] at hvd
      rcases eq_or_ne v 0 with hv0 | hv0
      · rw [hv0, hF0]; simp only [dist_self]; exact hε
      · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
        have hvd2 : |v| < 1 / 2 := lt_of_lt_of_le hvd (min_le_right _ _)
        have hv1 : v ≠ 1 := by
          intro h; rw [h] at hvd2; norm_num at hvd2
        rw [hFH v hv0 hv1]
        have hvd' : dist v 0 < δ₀ := by rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hvd (min_le_left _ _)
        exact hδ₀' hvpos hvd'
    · rcases eq_or_lt_of_le hu.2 with hu1 | hu1
      · -- u = 1
        subst hu1
        rw [ContinuousWithinAt, hF1, Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hH_tendsto_1 ε hε
        refine ⟨min δ₀ (1 / 2), by positivity, fun v hv hvd => ?_⟩
        rw [Real.dist_eq] at hvd
        rcases eq_or_ne v 1 with hv1 | hv1
        · rw [hv1, hF1]; simp only [dist_self]; exact hε
        · have hvlt1 : v < 1 := lt_of_le_of_ne hv.2 hv1
          have hvd2 : |v - 1| < 1 / 2 := lt_of_lt_of_le hvd (min_le_right _ _)
          have hv0 : v ≠ 0 := by
            intro h; rw [h] at hvd2; norm_num at hvd2
          rw [hFH v hv0 hv1]
          have hvd' : dist v 1 < δ₀ := by rw [Real.dist_eq]; exact lt_of_lt_of_le hvd (min_le_left _ _)
          exact hδ₀' hvlt1 hvd'
      · have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu0, hu1⟩
        have hHc : ContinuousWithinAt H (Icc (0 : ℝ) 1) u :=
          ((hHcont u hu').continuousAt (isOpen_Ioo.mem_nhds hu')).continuousWithinAt
        have hFHu : F u = H u := hFH u hu0.ne' hu1.ne
        have heq : H =ᶠ[𝓝[Icc (0 : ℝ) 1] u] F := by
          filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hu')] with v hv
          exact (hFH v hv.1.ne' hv.2.ne).symm
        rw [ContinuousWithinAt, hFHu]
        exact hHc.tendsto.congr' heq
  have hFmem_Ω : ∀ u ∈ Ioo (0 : ℝ) 1, F u ∈ Ω := by
    intro u hu
    rw [hFH u hu.1.ne' hu.2.ne, hH_def]
    exact hfrange ▸ ⟨c (β₀ - 2 * β₀ * u),
      (hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hu))).mpr (haffine_mapsTo hu), rfl⟩
  have hFinj_Ico : InjOn F (Ico (0 : ℝ) 1) := by
    intro u hu v hv huv
    rcases eq_or_ne u 0 with hu0 | hu0
    · rcases eq_or_ne v 0 with hv0 | hv0
      · rw [hu0, hv0]
      · exfalso
        have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv.2⟩
        rw [hu0, hF0] at huv
        exact haΩ (huv ▸ hFmem_Ω v hv')
    · rcases eq_or_ne v 0 with hv0 | hv0
      · exfalso
        have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
        rw [hv0, hF0] at huv
        exact haΩ (huv.symm ▸ hFmem_Ω u hu')
      · have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
        have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv.2⟩
        rw [hFH u hu0 hu'.2.ne, hFH v hv0 hv'.2.ne, hH_def] at huv
        have hcuv : c (β₀ - 2 * β₀ * u) = c (β₀ - 2 * β₀ * v) :=
          hfinj ((hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hu'))).mpr (haffine_mapsTo hu'))
            ((hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hv'))).mpr (haffine_mapsTo hv')) huv
        have hs_eq : β₀ - 2 * β₀ * u = β₀ - 2 * β₀ * v :=
          hc_inj (Ioo_subset_Icc_self (haffine_mapsTo hu')) (Ioo_subset_Icc_self (haffine_mapsTo hv'))
            hcuv
        have h2 : β₀ * u = β₀ * v := by linarith
        exact mul_left_cancel₀ hβ₀0.ne' h2
  have hHrange : H '' Ioo (0 : ℝ) 1 = f '' (unitDisc ∩ sphere z₀ ρ) := by
    rw [hS_eq]
    apply Subset.antisymm
    · rintro w ⟨u, hu, rfl⟩
      exact ⟨c (β₀ - 2 * β₀ * u), ⟨β₀ - 2 * β₀ * u, haffine_mapsTo hu, rfl⟩, rfl⟩
    · rintro w ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨(β₀ - t) / (2 * β₀),
        ⟨div_pos (by linarith [ht.2]) (by linarith),
          (div_lt_one (by linarith)).mpr (by linarith [ht.1])⟩, ?_⟩
      have heq : β₀ - 2 * β₀ * ((β₀ - t) / (2 * β₀)) = t := by
        field_simp
        ring
      show f (c (β₀ - 2 * β₀ * ((β₀ - t) / (2 * β₀)))) = f (c t)
      rw [heq]
  have hFrange : F '' Icc (0 : ℝ) 1 = f '' (unitDisc ∩ sphere z₀ ρ) ∪ {a, b} := by
    apply Subset.antisymm
    · rintro w ⟨u, hu, rfl⟩
      rcases eq_or_ne u 0 with rfl | hu0
      · right; rw [hF0]; simp
      rcases eq_or_ne u 1 with rfl | hu1
      · right; rw [hF1]; simp
      · left
        have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩
        rw [hFH u hu0 hu1, ← hHrange]
        exact ⟨u, hu', rfl⟩
    · rintro w (hw | hw)
      · rw [← hHrange] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        exact ⟨u, Ioo_subset_Icc_self hu, hFH u hu.1.ne' hu.2.ne⟩
      · rcases hw with rfl | rfl
        · exact ⟨0, ⟨le_refl 0, by norm_num⟩, hF0⟩
        · exact ⟨1, ⟨by norm_num, le_refl 1⟩, hF1⟩
  refine ⟨a, b, ha_frontier, hb_frontier, hdiam, ?_⟩
  by_cases hab : a = b
  · right
    refine ⟨hab, ?_⟩
    have hF01 : F 0 = F 1 := by rw [hF0, hF1, hab]
    have hloop := isJordanCurve_of_loop hFcont hFinj_Ico hF01
    have hset : f '' (unitDisc ∩ sphere z₀ ρ) ∪ ({a, b} : Set ℂ)
        = f '' (unitDisc ∩ sphere z₀ ρ) ∪ {a} := by rw [hab]; simp
    rwa [hFrange, hset] at hloop
  · left
    refine ⟨hab, ?_⟩
    have hFinj_Icc : InjOn F (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      rcases eq_or_ne u 1 with hu1 | hu1
      · rcases eq_or_ne v 1 with hv1 | hv1
        · rw [hu1, hv1]
        · exfalso
          have hv' : v ∈ Ico (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
          rcases eq_or_ne v 0 with hv0 | hv0
          · rw [hu1, hF1, hv0, hF0] at huv; exact hab huv.symm
          · have hv'' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv'.2⟩
            rw [hu1, hF1] at huv
            exact hbΩ (huv ▸ hFmem_Ω v hv'')
      · rcases eq_or_ne v 1 with hv1 | hv1
        · exfalso
          have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1, lt_of_le_of_ne hu.2 hu1⟩
          rcases eq_or_ne u 0 with hu0 | hu0
          · rw [hv1, hF1, hu0, hF0] at huv; exact hab huv
          · have hu'' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu'.2⟩
            rw [hv1, hF1] at huv
            exact hbΩ (huv.symm ▸ hFmem_Ω u hu'')
        · exact hFinj_Ico ⟨hu.1, lt_of_le_of_ne hu.2 hu1⟩ ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩ huv
    exact ⟨F, hFrange.symm, hFcont, hFinj_Icc, hF0, hF1⟩



/-- The endpoints of an arc are limit points of the arc interior. -/
theorem mem_closure_diff_of_isArcEndC {A : Set ℂ} {v w : ℂ} (hvw : v ≠ w)
    (h : IsArcEndC A v w) : v ∈ closure (A \ {v, w}) ∧ w ∈ closure (A \ {v, w}) := by
  obtain ⟨γ, hA, hγc, hγi, hγ0, hγ1⟩ := h
  have hmemIcc : ∀ k : ℕ, (1 / ((k : ℝ) + 2)) ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  have hmemIcc' : ∀ k : ℕ, (1 - 1 / ((k : ℝ) + 2)) ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) k],
      by
      have : (0:ℝ) ≤ 1 / ((k:ℝ)+2) := by positivity
      linarith⟩
  have hltone : ∀ k : ℕ, (1 / ((k:ℝ)+2)) < 1 := by
    intro k
    rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have htendsto0 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 2))) atTop (𝓝 (0:ℝ)) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    have heq : (fun k : ℕ => (1 / ((k:ℝ)+2))) =
        (fun k : ℕ => 1/((k:ℝ)+1)) ∘ (· + 1) := by
      funext k; simp only [Function.comp]; push_cast; ring_nf
    rw [heq]; exact h2
  have htendsto1 : Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2))) atTop (𝓝 (1:ℝ)) := by
    have h2 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
    have := h2.sub htendsto0
    simpa using this
  have hmemAv : ∀ k : ℕ, γ (1 / ((k:ℝ)+2)) ∈ A \ {v, w} := by
    intro k
    have hmemA : γ (1 / ((k:ℝ)+2)) ∈ A := by rw [hA]; exact ⟨_, hmemIcc k, rfl⟩
    refine ⟨hmemA, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro heq
      have := hγi (hmemIcc k) (left_mem_Icc.2 zero_le_one) (heq.trans hγ0.symm)
      have hpos : (0:ℝ) < 1 / ((k:ℝ)+2) := by positivity
      linarith [this]
    · intro heq
      have := hγi (hmemIcc k) (right_mem_Icc.2 zero_le_one) (heq.trans hγ1.symm)
      linarith [this, hltone k]
  have hmemAw : ∀ k : ℕ, γ (1 - 1 / ((k:ℝ)+2)) ∈ A \ {v, w} := by
    intro k
    have hmemA : γ (1 - 1 / ((k:ℝ)+2)) ∈ A := by rw [hA]; exact ⟨_, hmemIcc' k, rfl⟩
    refine ⟨hmemA, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro heq
      have := hγi (hmemIcc' k) (left_mem_Icc.2 zero_le_one) (heq.trans hγ0.symm)
      linarith [this, hltone k]
    · intro heq
      have := hγi (hmemIcc' k) (right_mem_Icc.2 zero_le_one) (heq.trans hγ1.symm)
      have hpos : (0:ℝ) < 1 / ((k:ℝ)+2) := by positivity
      linarith [this]
  have hcv : Tendsto (fun k : ℕ => γ (1 / ((k:ℝ)+2))) atTop (𝓝 v) := by
    rw [← hγ0]
    have hcont : ContinuousWithinAt γ (Icc 0 1) 0 :=
      hγc 0 (left_mem_Icc.2 zero_le_one)
    have hwithin : Tendsto (fun k : ℕ => (1 / ((k:ℝ)+2))) atTop (𝓝[Icc (0:ℝ) 1] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨htendsto0, Filter.Eventually.of_forall hmemIcc⟩
    exact hcont.tendsto.comp hwithin
  have hcw : Tendsto (fun k : ℕ => γ (1 - 1 / ((k:ℝ)+2))) atTop (𝓝 w) := by
    rw [← hγ1]
    have hcont : ContinuousWithinAt γ (Icc 0 1) 1 :=
      hγc 1 (right_mem_Icc.2 zero_le_one)
    have hwithin : Tendsto (fun k : ℕ => (1 - 1 / ((k:ℝ)+2))) atTop (𝓝[Icc (0:ℝ) 1] 1) :=
      tendsto_nhdsWithin_iff.2 ⟨htendsto1, Filter.Eventually.of_forall hmemIcc'⟩
    exact hcont.tendsto.comp hwithin
  exact ⟨mem_closure_of_tendsto hcv (Filter.Eventually.of_forall hmemAv),
    mem_closure_of_tendsto hcw (Filter.Eventually.of_forall hmemAw)⟩

/-- The single closing point of a Jordan-curve loop `σ ∪ {a}` is a limit point of `σ`. -/
theorem mem_closure_diff_of_isJordanCurve_singleton {σ : Set ℂ} {a : ℂ}
    (h : IsJordanCurve (toExt (σ ∪ {a}))) : a ∈ closure ((σ ∪ {a}) \ {a}) := by
  obtain ⟨γ, hγc, hγi, hγr⟩ := exists_circle_param_of_isJordanCurve_toExt h
  obtain ⟨c, hc⟩ : ∃ c : Circle, γ c = a := by
    have : a ∈ range γ := by rw [hγr]; exact Or.inr rfl
    exact this
  have hne0 : ∀ k : ℕ, c * Circle.exp (1 / ((k:ℝ) + 1)) ≠ c := by
    intro k heq
    have h1 : Circle.exp (1 / ((k:ℝ)+1)) = 1 :=
      mul_left_cancel (heq.trans (mul_one c).symm)
    have hpos : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
    have hlt : (1 / ((k:ℝ)+1)) < 2 * π := by
      have h2 : (1:ℝ) ≤ (k:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      calc (1 / ((k:ℝ)+1)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [h2]
        _ < 2 * π := by linarith [Real.pi_gt_three]
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.1 h1
    rcases eq_or_ne m 0 with rfl | hmne
    · simp at hm; linarith [hm, hpos]
    · exfalso
      rcases lt_or_gt_of_ne hmne with hm0 | hm0
      · have hmle : m ≤ -1 := by omega
        have hmle' : (m:ℝ) ≤ -1 := by exact_mod_cast hmle
        nlinarith [hm, hpos, Real.pi_pos]
      · have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm0
        nlinarith [hm, hlt, Real.pi_pos]
  have htendsto0 : Tendsto (fun k : ℕ => (1 / ((k:ℝ) + 1))) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htendsto : Tendsto (fun k : ℕ => c * Circle.exp (1 / ((k:ℝ)+1))) atTop (𝓝 c) := by
    have h1 : Tendsto (fun k : ℕ => Circle.exp (1 / ((k:ℝ)+1))) atTop (𝓝 (1:Circle)) := by
      have h1' := Circle.exp.continuous.tendsto (0:ℝ)
      rw [Circle.exp_zero] at h1'
      exact h1'.comp htendsto0
    have h2 : Tendsto (fun x : Circle => c * x) (𝓝 (1:Circle)) (𝓝 c) := by
      have := (continuous_const_mul c).tendsto (1:Circle)
      simpa using this
    exact h2.comp h1
  have hmemσ : ∀ k : ℕ, γ (c * Circle.exp (1 / ((k:ℝ)+1))) ∈ (σ ∪ {a}) \ {a} := by
    intro k
    have hmemA : γ (c * Circle.exp (1 / ((k:ℝ)+1))) ∈ σ ∪ {a} := by rw [← hγr]; exact mem_range_self _
    refine ⟨hmemA, ?_⟩
    simp only [mem_singleton_iff]
    intro heq
    exact hne0 k (hγi (heq.trans hc.symm))
  have hcv : Tendsto (fun k : ℕ => γ (c * Circle.exp (1 / ((k:ℝ)+1)))) atTop (𝓝 a) := by
    rw [← hc]
    exact hγc.continuousAt.tendsto.comp htendsto
  exact mem_closure_of_tendsto hcv (Filter.Eventually.of_forall hmemσ)

theorem exists_clusterSet_eq_singleton_of_isJordanCurve_frontier {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩbdd : Bornology.IsBounded Ω) (hf : IsConformalOnto f unitDisc Ω)
    (hJ : IsJordanCurve (toExt (frontier Ω))) {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) :
    ∃ w, clusterSet f unitDisc z₀ = {w} := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩc : IsConnected Ω := by
    have : IsConnected unitDisc :=
      (convex_ball (0:ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩
    rw [← hf.2.2]; exact this.image f hf.1.continuousOn
  obtain ⟨ρ, hρanti, hρpos, hρtendsto, hℓtendsto⟩ := wolff_length_area hΩbdd hf hz₀
  obtain ⟨φ, hφc, hφi, hφr⟩ := exists_circle_param_of_isJordanCurve_toExt hJ
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  -- Key step: the closure of the disc-piece has diameter tending to 0.
  have hdiam0 : Tendsto (fun n => Metric.diam (f '' (unitDisc ∩ ball z₀ (ρ n)))) atTop (𝓝 0) := by
    -- Eventually the radius is `< 1` and the arclength is finite.
    have hev1 : ∀ᶠ n in atTop, ρ n < 1 := hρtendsto.eventually_lt_const one_pos
    have hev2 : ∀ᶠ n in atTop, arcLength f z₀ (ρ n) ≠ ⊤ := by
      have h1 : ∀ᶠ n in atTop, arcLength f z₀ (ρ n) < 1 := hℓtendsto.eventually_lt_const one_pos
      filter_upwards [h1] with n hn
      exact hn.ne_top
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
    -- Package `C3` into a total function via the "hypothesis inside the ∃" `choose` trick.
    have hex : ∀ n : ℕ, ∃ a b : ℂ, n ≥ N₀ →
        (a ∈ frontier Ω ∧ b ∈ frontier Ω ∧
          Metric.diam (f '' (unitDisc ∩ sphere z₀ (ρ n))) ≤ (arcLength f z₀ (ρ n)).toReal ∧
          ((a ≠ b ∧ IsArcEndC (f '' (unitDisc ∩ sphere z₀ (ρ n)) ∪ {a, b}) a b) ∨
            (a = b ∧ IsJordanCurve (toExt (f '' (unitDisc ∩ sphere z₀ (ρ n)) ∪ {a}))))) := by
      intro n
      by_cases hn : n ≥ N₀
      · obtain ⟨a, b, ha, hb, hdiam, hcase⟩ :=
          exists_ends_of_circleArc_image hΩbdd hf hz₀ (hρpos n) (hN₀ n hn).1 (hN₀ n hn).2
        exact ⟨a, b, fun _ => ⟨ha, hb, hdiam, hcase⟩⟩
      · exact ⟨0, 0, fun h => absurd h hn⟩
    choose a b hab using hex
    set σ : ℕ → Set ℂ := fun n => f '' (unitDisc ∩ sphere z₀ (ρ n)) with hσdef
    have hσΩ : ∀ n, σ n ⊆ Ω := fun n => by
      rw [hσdef, ← hf.2.2]; exact Set.image_mono Set.inter_subset_left
    have hσfrdisj : ∀ n, Disjoint (σ n) (frontier Ω) := fun n =>
      Set.disjoint_of_subset_left (hσΩ n) hΩfr
    -- Preimages of `a n, b n` under `φ`, defined for `n ≥ N₀`.
    have hex2 : ∀ n : ℕ, ∃ s t : Circle, n ≥ N₀ → (φ s = a n ∧ φ t = b n) := by
      intro n
      by_cases hn : n ≥ N₀
      · obtain ⟨ha, hb, -, -⟩ := hab n hn
        rw [← hφr] at ha hb
        obtain ⟨s, hs⟩ := ha
        obtain ⟨t, ht⟩ := hb
        exact ⟨s, t, fun _ => ⟨hs, ht⟩⟩
      · exact ⟨1, 1, fun h => absurd h hn⟩
    choose s t hst using hex2
    set τ : ℕ → Set ℂ := fun n => φ '' circleShortArc (s n) (t n) with hτdef
    -- `diam σ n → 0`, from `C3`'s bound and Wolff's length-area lemma.
    have hℓtoReal0 : Tendsto (fun n => (arcLength f z₀ (ρ n)).toReal) atTop (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal (a := (0:ℝ≥0∞)) (by simp)).comp hℓtendsto
      have h2 : ((fun n => (arcLength f z₀ (ρ n)).toReal)) =
          ENNReal.toReal ∘ fun n => arcLength f z₀ (ρ n) := rfl
      rw [h2]; simpa using h1
    have hdiamσ0 : Tendsto (fun n => Metric.diam (σ n)) atTop (𝓝 0) := by
      have hle : ∀ᶠ n in atTop, Metric.diam (σ n) ≤ (arcLength f z₀ (ρ n)).toReal := by
        filter_upwards [Filter.eventually_atTop.2 ⟨N₀, fun n hn => (hab n hn).2.2.1⟩] with n hn
        exact hn
      exact squeeze_zero' (Filter.Eventually.of_forall fun n => Metric.diam_nonneg) hle hℓtoReal0
    -- Both endpoints lie in `closure (σ n)`, for `n ≥ N₀`.
    have hendptsclosure : ∀ n ≥ N₀, a n ∈ closure (σ n) ∧ b n ∈ closure (σ n) := by
      intro n hn
      obtain ⟨ha, hb, -, hcase⟩ := hab n hn
      have hanotmem : a n ∉ σ n := fun hmem => Set.disjoint_left.1 (hσfrdisj n) hmem ha
      have hbnotmem : b n ∉ σ n := fun hmem => Set.disjoint_left.1 (hσfrdisj n) hmem hb
      rcases hcase with ⟨hne, harc⟩ | ⟨heq, hloop⟩
      · have hcl := mem_closure_diff_of_isArcEndC hne harc
        have heqset : (σ n ∪ {a n, b n}) \ {a n, b n} = σ n := by
          ext z; simp only [mem_diff, mem_union, mem_insert_iff, mem_singleton_iff]
          constructor
          · rintro ⟨h | h, hne'⟩
            · exact h
            · exact absurd h hne'
          · intro h; exact ⟨Or.inl h, fun hc => hc.elim (fun h1 => hanotmem (h1 ▸ h))
              (fun h2 => hbnotmem (h2 ▸ h))⟩
        rwa [heqset] at hcl
      · have hcl := mem_closure_diff_of_isJordanCurve_singleton hloop
        have heqset : (σ n ∪ {a n}) \ {a n} = σ n := by
          ext z; simp only [mem_diff, mem_union, mem_singleton_iff]
          constructor
          · rintro ⟨h | h, hne'⟩
            · exact h
            · exact absurd h hne'
          · intro h; exact ⟨Or.inl h, fun hc => hanotmem (hc ▸ h)⟩
        rw [heqset] at hcl
        exact ⟨hcl, heq ▸ hcl⟩
    -- `dist (a n) (b n) → 0`, squeezed by `diam σ n`.
    have hdistab0 : Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
      have hle : ∀ᶠ n in atTop, dist (a n) (b n) ≤ Metric.diam (σ n) := by
        filter_upwards [Filter.eventually_atTop.2 ⟨N₀, fun n hn => hn⟩] with n hn
        have hbddσ : Bornology.IsBounded (closure (σ n)) := (hΩbdd.subset (hσΩ n)).closure
        have h1 := Metric.dist_le_diam_of_mem hbddσ (hendptsclosure n hn).1 (hendptsclosure n hn).2
        rwa [Metric.diam_closure] at h1
      exact squeeze_zero' (Filter.Eventually.of_forall fun n => dist_nonneg) hle hdiamσ0
    have hdistφ0 : Tendsto (fun n => dist (φ (s n)) (φ (t n))) atTop (𝓝 0) := by
      have heq : (fun n => dist (a n) (b n)) =ᶠ[atTop] (fun n => dist (φ (s n)) (φ (t n))) := by
        filter_upwards [Filter.eventually_atTop.2 ⟨N₀, fun n hn => hn⟩] with n hn
        rw [(hst n hn).1, (hst n hn).2]
      exact hdistab0.congr' heq
    have hdiamτ0 : Tendsto (fun n => Metric.diam (τ n)) atTop (𝓝 0) :=
      tendsto_diam_image_circleShortArc hφc hφi hdistφ0
    have hCtendsto : Tendsto (fun n => Metric.diam (σ n) + Metric.diam (τ n)) atTop (𝓝 0) := by
      simpa using hdiamσ0.add hdiamτ0
    -- The main per-`n` diameter bound (`P` is the right piece, ruling out the wrong one via `f 0`).
    have hδpos : 0 < Metric.infDist (f 0) (frontier Ω) := by
      have h0 : (0:ℂ) ∈ unitDisc := mem_ball_self one_pos
      have hf0Ω : f 0 ∈ Ω := hf.2.2 ▸ mem_image_of_mem f h0
      have hf0notfr : f 0 ∉ frontier Ω := fun h => Set.disjoint_left.1 hΩfr hf0Ω h
      have hfrne : (frontier Ω).Nonempty := by
        rw [← hφr]; exact ⟨φ 1, mem_range_self _⟩
      exact (isClosed_frontier.notMem_iff_infDist_pos hfrne).1 hf0notfr
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
      ((hCtendsto.eventually_lt_const hδpos).and (Filter.eventually_atTop.2 ⟨N₀, fun n hn => hn⟩))
    have hbound : ∀ᶠ n in atTop, Metric.diam (f '' (unitDisc ∩ ball z₀ (ρ n))) ≤
        Metric.diam (σ n) + Metric.diam (τ n) := by
      refine Filter.eventually_atTop.2 ⟨N₁, fun n hn => ?_⟩
      obtain ⟨hCδ, hnN₀⟩ := hN₁ n hn
      obtain ⟨ha, hb, -, hcase⟩ := hab n hnN₀
      have h0mem : (0:ℂ) ∈ unitDisc := mem_ball_self one_pos
      have h0notin : (0:ℂ) ∉ closedBall z₀ (ρ n) := by
        rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hz₀]
        exact not_le.2 (hN₀ n hnN₀).1
      have hf0ext : f 0 ∈ f '' (unitDisc \ closedBall z₀ (ρ n)) :=
        ⟨0, ⟨h0mem, h0notin⟩, rfl⟩
      rcases hcase with ⟨hne, harc⟩ | ⟨heq, hloop⟩
      · -- Arc case: use `C6` and `S3_crosscut_splits`.
        have hsnetn : s n ≠ t n := fun heqst =>
          hne ((hst n hnN₀).1.symm.trans (heqst ▸ (hst n hnN₀).2))
        have hτeq : τ n = φ '' circleShortArc (s n) (t n) := by rw [hτdef]
        obtain ⟨hτarc, τ', hτ'arc, hτunion, hτint⟩ :=
          isArcEndC_split_circleShortArc hφc hφi hsnetn
        rw [← hτeq] at hτarc hτunion hτint
        rw [(hst n hnN₀).1, (hst n hnN₀).2] at hτarc hτ'arc hτint
        have hτsubfr : τ n ⊆ frontier Ω := by
          rw [← hφr, ← hτunion]; exact subset_union_left
        have hτ'subfr : τ' ⊆ frontier Ω := by
          rw [← hφr, ← hτunion]; exact subset_union_right
        have hσdisjτ : Disjoint (σ n) (τ n) := Set.disjoint_of_subset_left (hσΩ n)
          (Set.disjoint_of_subset_right hτsubfr hΩfr)
        have hσdisjτ' : Disjoint (σ n) τ' := Set.disjoint_of_subset_left (hσΩ n)
          (Set.disjoint_of_subset_right hτ'subfr hΩfr)
        have habτ : ({a n, b n} : Set ℂ) ⊆ τ n := hτint ▸ Set.inter_subset_left
        have habτ' : ({a n, b n} : Set ℂ) ⊆ τ' := hτint ▸ Set.inter_subset_right
        have hDτ : (σ n ∪ {a n, b n}) ∩ τ n = {a n, b n} := by
          rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.1 hσdisjτ,
            Set.inter_eq_left.2 habτ, Set.empty_union]
        have hDτ' : (σ n ∪ {a n, b n}) ∩ τ' = {a n, b n} := by
          rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.1 hσdisjτ',
            Set.inter_eq_left.2 habτ', Set.empty_union]
        have hτunion' : τ n ∪ τ' = frontier Ω := hφr ▸ hτunion
        obtain ⟨I₁, I₂, hI₁o, hI₂o, hI₁c, hI₂c, hI₁I₂, hfrI₁, hfrI₂, hΩσ, hdisj⟩ :=
          S3_crosscut_splits hΩo hΩc hΩbdd hJ hf hz₀ (hρpos n) (hN₀ n hnN₀).1 hne rfl
            hτarc hτ'arc hτunion' hτint harc hDτ hDτ'
        have hI₁Ω : I₁ ⊆ Ω := fun z hz => (hΩσ ▸ (Or.inl hz : z ∈ I₁ ∪ I₂) : z ∈ Ω \ σ n).1
        have hI₂Ω : I₂ ⊆ Ω := fun z hz => (hΩσ ▸ (Or.inr hz : z ∈ I₁ ∪ I₂) : z ∈ Ω \ σ n).1
        have hbdd1 : Bornology.IsBounded I₁ := hΩbdd.subset hI₁Ω
        have hbdd2 : Bornology.IsBounded I₂ := hΩbdd.subset hI₂Ω
        have hne1 : I₁.Nonempty := hI₁c.nonempty
        have hne2 : I₂.Nonempty := hI₂c.nonempty
        have hendcl : a n ∈ closure (σ n) ∧ b n ∈ closure (σ n) := hendptsclosure n hnN₀
        have hsub1 : σ n ∪ {a n, b n} ⊆ closure (σ n) :=
          Set.union_subset subset_closure
            (Set.insert_subset hendcl.1 (Set.singleton_subset_iff.2 hendcl.2))
        have hboundgen : ∀ {τ₀ : Set ℂ} {I₀ : Set ℂ}, IsOpen I₀ → Bornology.IsBounded I₀ →
            I₀.Nonempty → frontier I₀ = τ₀ ∪ σ n ∪ {a n, b n} →
            ({a n, b n} : Set ℂ) ⊆ τ₀ →
            Metric.diam (closure I₀) ≤ Metric.diam τ₀ + Metric.diam (σ n) := by
          intro τ₀ I₀ hI₀o hI₀bdd hI₀ne hfrI₀ habτ₀
          rw [diam_closure_eq_diam_frontier hI₀o hI₀bdd hI₀ne, hfrI₀, union_assoc]
          have hbddστ₀union : Bornology.IsBounded (σ n ∪ {a n, b n}) :=
            Bornology.IsBounded.subset (hΩbdd.subset (hσΩ n)).closure hsub1
          have hinter : (τ₀ ∩ (σ n ∪ {a n, b n})).Nonempty :=
            ⟨a n, habτ₀ (by simp), by simp⟩
          calc Metric.diam (τ₀ ∪ (σ n ∪ {a n, b n}))
              ≤ Metric.diam τ₀ + Metric.diam (σ n ∪ {a n, b n}) := Metric.diam_union' hinter
            _ ≤ Metric.diam τ₀ + Metric.diam (closure (σ n)) := by
                gcongr
                exact Metric.diam_mono hsub1 (hΩbdd.subset (hσΩ n)).closure
            _ = Metric.diam τ₀ + Metric.diam (σ n) := by rw [Metric.diam_closure]
        have hb1 : Metric.diam (closure I₁) ≤ Metric.diam (τ n) + Metric.diam (σ n) :=
          hboundgen hI₁o hbdd1 hne1 hfrI₁ habτ
        have hb2 : Metric.diam (closure I₂) ≤ Metric.diam τ' + Metric.diam (σ n) :=
          hboundgen hI₂o hbdd2 hne2 hfrI₂ habτ'
        -- Side selection: `f 0` lands in the OTHER piece, ruling out `f''ball = I₂`.
        have haI₁fr : a n ∈ frontier I₁ := by
          rw [hfrI₁]; simp
        have key : f '' (unitDisc ∩ ball z₀ (ρ n)) = I₁ := by
          rcases hdisj with ⟨heq1, heq2⟩ | ⟨heq1, heq2⟩
          · exact heq1
          · exfalso
            have hf0I₁ : f 0 ∈ I₁ := heq2 ▸ hf0ext
            have hle : dist (f 0) (a n) ≤ Metric.diam (closure I₁) :=
              Metric.dist_le_diam_of_mem hbdd1.closure (subset_closure hf0I₁)
                (frontier_subset_closure haI₁fr)
            have hge : Metric.infDist (f 0) (frontier Ω) ≤ dist (f 0) (a n) :=
              Metric.infDist_le_dist_of_mem ha
            have h1 : Metric.infDist (f 0) (frontier Ω) ≤ Metric.diam (τ n) + Metric.diam (σ n) :=
              hge.trans (hle.trans hb1)
            have h2 : Metric.diam (τ n) + Metric.diam (σ n) ≤
                Metric.diam (σ n) + Metric.diam (τ n) := le_of_eq (add_comm _ _)
            exact absurd (hCδ.trans_le (h1.trans h2)) (lt_irrefl _)
        rw [key]
        calc Metric.diam I₁
            ≤ Metric.diam (closure I₁) :=
              Metric.diam_mono subset_closure hbdd1.closure
          _ ≤ Metric.diam (τ n) + Metric.diam (σ n) := hb1
          _ = Metric.diam (σ n) + Metric.diam (τ n) := add_comm _ _
      · -- Loop case: use `S4_loop_splits`.
        obtain ⟨I, I', hIo, hI'o, hIc, hI'c, hIbdd, hIΩ, hII', hfrI, hΩσ, hdisj⟩ :=
          S4_loop_splits hΩo hΩc hΩbdd hJ hf hz₀ (hρpos n) (hN₀ n hnN₀).1 rfl ha (heq ▸ hloop)
        have hne1 : I.Nonempty := hIc.nonempty
        have hendcl : a n ∈ closure (σ n) := (hendptsclosure n hnN₀).1
        have hsub1 : σ n ∪ {a n} ⊆ closure (σ n) :=
          Set.union_subset subset_closure (Set.singleton_subset_iff.2 hendcl)
        have hb1 : Metric.diam (closure I) ≤ Metric.diam (σ n) := by
          rw [diam_closure_eq_diam_frontier hIo hIbdd hne1, hfrI]
          exact Metric.diam_mono hsub1 (hΩbdd.subset (hσΩ n)).closure |>.trans_eq
            (Metric.diam_closure _)
        have haIfr : a n ∈ frontier I := by rw [hfrI]; exact Or.inr rfl
        have key : f '' (unitDisc ∩ ball z₀ (ρ n)) = I := by
          rcases hdisj with ⟨heq1, heq2⟩ | ⟨heq1, heq2⟩
          · exact heq1
          · exfalso
            have hf0I : f 0 ∈ I := heq2 ▸ hf0ext
            have hle : dist (f 0) (a n) ≤ Metric.diam (closure I) :=
              Metric.dist_le_diam_of_mem hIbdd.closure (subset_closure hf0I)
                (frontier_subset_closure haIfr)
            have hge : Metric.infDist (f 0) (frontier Ω) ≤ dist (f 0) (a n) :=
              Metric.infDist_le_dist_of_mem ha
            have h1 : Metric.infDist (f 0) (frontier Ω) ≤ Metric.diam (σ n) :=
              hge.trans (hle.trans hb1)
            have h2 : Metric.diam (σ n) ≤ Metric.diam (σ n) + Metric.diam (τ n) :=
              le_add_of_nonneg_right Metric.diam_nonneg
            exact absurd (hCδ.trans_le (h1.trans h2)) (lt_irrefl _)
        rw [key]
        calc Metric.diam I
            ≤ Metric.diam (closure I) := Metric.diam_mono subset_closure hIbdd.closure
          _ ≤ Metric.diam (σ n) := hb1
          _ ≤ Metric.diam (σ n) + Metric.diam (τ n) := le_add_of_nonneg_right Metric.diam_nonneg
    exact squeeze_zero' (Filter.Eventually.of_forall fun n => Metric.diam_nonneg) hbound hCtendsto
  -- Conclude via `clusterSet ⊆ closure (image of a small ball)` for every n.
  have hsub : ∀ n, clusterSet f unitDisc z₀ ⊆ closure (f '' (unitDisc ∩ ball z₀ (ρ n))) := by
    intro n
    exact Set.iInter₂_subset (ρ n) (hρpos n)
  have hdiamcl0 : Tendsto (fun n => Metric.diam (closure (f '' (unitDisc ∩ ball z₀ (ρ n)))))
      atTop (𝓝 0) := by
    simpa [Metric.diam_closure] using hdiam0
  have hclustersubsingleton : (clusterSet f unitDisc z₀).Subsingleton := by
    intro x hx y hy
    have hdistle : ∀ n, dist x y ≤ Metric.diam (closure (f '' (unitDisc ∩ ball z₀ (ρ n)))) := by
      intro n
      have hsubΩ : f '' (unitDisc ∩ ball z₀ (ρ n)) ⊆ Ω := by
        rw [← hf.2.2]; exact Set.image_mono Set.inter_subset_left
      have hbddn : Bornology.IsBounded (closure (f '' (unitDisc ∩ ball z₀ (ρ n)))) :=
        (hΩbdd.subset hsubΩ).closure
      exact Metric.dist_le_diam_of_mem hbddn (hsub n hx) (hsub n hy)
    have hle0 : dist x y ≤ 0 := ge_of_tendsto hdiamcl0 (Filter.Eventually.of_forall hdistle)
    exact dist_le_zero.mp hle0
  have hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).1 hΩbdd
    refine ⟨R, fun z hz => ?_⟩
    have : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    have := hR this
    simpa using this
  obtain ⟨hne, -, -⟩ := clusterSet_isCompact_isConnected (mem_sphere_zero_iff_norm.2 hz₀)
    hf.1.continuousOn hbdd
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hclustersubsingleton.eq_singleton_of_mem hw⟩


theorem mem_closure_image_of_tendsto_nhdsWithin {f : ℂ → ℂ} {s : Set ℂ} {x y : ℂ}
    (hx : x ∈ closure s) (htend : Tendsto f (𝓝[s] x) (𝓝 y)) : y ∈ closure (f '' s) := by
  haveI : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hmcp : MapClusterPt y (𝓝[s] x) f := htend.mapClusterPt
  have hle : f '' s ∈ Filter.map f (𝓝[s] x) :=
    Filter.mem_map.2 (Filter.mem_of_superset self_mem_nhdsWithin (Set.subset_preimage_image f s))
  exact mem_closure_iff_clusterPt.2 (hmcp.clusterPt.mono (Filter.le_principal_iff.2 hle))

/-- Every point of the unit circle is a limit point of `unitDisc` intersected with any ball
around it. -/
theorem mem_closure_unitDisc_inter_ball {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) :
    ζ ∈ closure (unitDisc ∩ ball ζ r) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min r (min ε 1) / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδr : δ < r := by
    have : min r (min ε 1) ≤ r := min_le_left _ _
    linarith [hδpos]
  have hδε : δ < ε := by
    have h1 : min r (min ε 1) ≤ min ε 1 := min_le_right _ _
    have h2 : min ε 1 ≤ ε := min_le_left _ _
    linarith [hδpos]
  have hδ1 : δ < 1 := by
    have h1 : min r (min ε 1) ≤ min ε 1 := min_le_right _ _
    have h2 : min ε 1 ≤ 1 := min_le_right _ _
    linarith [hδpos]
  have hcast1 : (1 - δ : ℂ) = ((1 - δ : ℝ) : ℂ) := by push_cast; ring
  refine ⟨(1 - δ) * ζ, ⟨?_, ?_⟩, ?_⟩
  · rw [unitDisc, mem_ball_zero_iff, hcast1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith), hζ, mul_one]
    linarith
  · rw [mem_ball, dist_eq_norm]
    have heq : (1 - δ : ℂ) * ζ - ζ = ((-δ:ℝ) : ℂ) * ζ := by push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos, hζ, mul_one]
    exact hδr
  · rw [dist_eq_norm]
    have heq : ζ - (1 - δ) * ζ = ((δ:ℝ):ℂ) * ζ := by rw [hcast1]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, hζ, mul_one]
    exact hδε

/-- **C8** (e1) the continuous extension to the closed disc. -/
theorem exists_continuousOn_extension_of_isJordanCurve_frontier {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩbdd : Bornology.IsBounded Ω) (hf : IsConformalOnto f unitDisc Ω)
    (hJ : IsJordanCurve (toExt (frontier Ω))) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧
      F '' sphere (0 : ℂ) 1 ⊆ frontier Ω ∧ F '' closedBall 0 1 = closure Ω := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hall : ∀ ζ ∈ sphere (0:ℂ) 1, ∃ w, clusterSet f unitDisc ζ = {w} := fun ζ hζ =>
    exists_clusterSet_eq_singleton_of_isJordanCurve_frontier hΩbdd hf hJ
      (mem_sphere_zero_iff_norm.1 hζ)
  obtain ⟨F, hFc, hFf⟩ :=
    (continuous_extension_iff_forall_clusterSet_subsingleton hf.1).2 hall
  have hcl : closure unitDisc = closedBall (0:ℂ) 1 := closure_ball (0:ℂ) one_ne_zero
  rw [hcl] at hFc
  -- `F ζ` agrees with the (unique) cluster value, for `ζ` on the sphere.
  have hFζeq : ∀ ζ ∈ sphere (0:ℂ) 1, ∀ w, clusterSet f unitDisc ζ = {w} → F ζ = w := by
    intro ζ hζ w hw
    have hζmemcl : ζ ∈ closure unitDisc := hcl ▸ (sphere_subset_closedBall hζ)
    have hFcont : ContinuousWithinAt F (closure unitDisc) ζ := by
      rw [hcl]; exact hFc ζ (hcl ▸ hζmemcl)
    have hFcont' : ContinuousWithinAt F unitDisc ζ :=
      hFcont.mono subset_closure
    have hftend : Tendsto f (𝓝[unitDisc] ζ) (𝓝 (F ζ)) := by
      have : Tendsto F (𝓝[unitDisc] ζ) (𝓝 (F ζ)) := hFcont'
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hFf hz
    have hζmemud : ζ ∈ closure unitDisc := hζmemcl
    have hFζmem : F ζ ∈ closure (f '' unitDisc) :=
      mem_closure_image_of_tendsto_nhdsWithin hζmemud hftend
    have hFζmemcs : F ζ ∈ clusterSet f unitDisc ζ := by
      rw [clusterSet]
      refine Set.mem_iInter₂.2 fun r hr => ?_
      have hsub : unitDisc ∩ ball ζ r ⊆ unitDisc := Set.inter_subset_left
      have hnhds : 𝓝[unitDisc ∩ ball ζ r] ζ ≤ 𝓝[unitDisc] ζ := nhdsWithin_mono ζ hsub
      have hftend' : Tendsto f (𝓝[unitDisc ∩ ball ζ r] ζ) (𝓝 (F ζ)) := hftend.mono_left hnhds
      exact mem_closure_image_of_tendsto_nhdsWithin
        (mem_closure_unitDisc_inter_ball (mem_sphere_zero_iff_norm.1 hζ) hr) hftend'
    rw [hw] at hFζmemcs
    exact hFζmemcs
  -- The value at every boundary point is genuinely on `frontier Ω`.
  have hFζfr : ∀ ζ ∈ sphere (0:ℂ) 1, F ζ ∈ frontier Ω := by
    intro ζ hζ
    obtain ⟨w', hw'⟩ := hall ζ hζ
    have hFζ : F ζ = w' := hFζeq ζ hζ w' hw'
    rw [hFζ, hΩo.frontier_eq]
    have hw'memcs : w' ∈ clusterSet f unitDisc ζ := hw' ▸ rfl
    have hw'mem_cl : w' ∈ closure Ω := by
      rw [clusterSet] at hw'memcs
      have := Set.mem_iInter₂.1 hw'memcs 1 one_pos
      refine closure_mono ?_ this
      rw [← hf.2.2]; exact Set.image_mono Set.inter_subset_left
    have hw'notmem : w' ∉ Ω := by
      -- Build a sequence witnessing the cluster value, to invoke `C2`.
      have hex : ∀ k : ℕ, ∃ z : ℂ, z ∈ unitDisc ∧ dist z ζ < 1/((k:ℝ)+1) ∧
          dist (f z) w' < 1/((k:ℝ)+1) := by
        intro k
        rw [clusterSet] at hw'memcs
        have hmem := Set.mem_iInter₂.1 hw'memcs (1/((k:ℝ)+1)) (by positivity)
        rw [Metric.mem_closure_iff] at hmem
        obtain ⟨y, hy, hdy⟩ := hmem (1/((k:ℝ)+1)) (by positivity)
        obtain ⟨z, hz, rfl⟩ := hy
        refine ⟨z, hz.1, hz.2, ?_⟩
        rwa [dist_comm] at hdy
      choose z hzmem hzdist hfzdist using hex
      have hz0 : Tendsto (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hzζ : Tendsto z atTop (𝓝 ζ) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => (hzdist k).le) hz0
      have hfzw' : Tendsto (fun k => f (z k)) atTop (𝓝 w') := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => (hfzdist k).le) hz0
      exact tendsto_boundary_of_isConformalOnto hf (mem_sphere_zero_iff_norm.1 hζ) hzmem hzζ hfzw'
    exact ⟨hw'mem_cl, hw'notmem⟩
  refine ⟨F, hFc, hFf, ?_, ?_⟩
  · rintro w ⟨ζ, hζ, rfl⟩; exact hFζfr ζ hζ
  · apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      rcases eq_or_lt_of_le (mem_closedBall.1 hz) with heq | hlt
      · have hzsph : z ∈ sphere (0:ℂ) 1 := heq
        exact frontier_subset_closure (hFζfr z hzsph)
      · have hzud : z ∈ unitDisc := hlt
        rw [hFf hzud]
        exact subset_closure (hf.2.2 ▸ mem_image_of_mem f hzud)
    · intro w hw
      have hwsub : Ω ⊆ F '' closedBall (0:ℂ) 1 := by
        rw [← hf.2.2]
        rintro y ⟨z, hz, rfl⟩
        refine ⟨z, ball_subset_closedBall hz, ?_⟩
        exact hFf hz
      have hFimg_closed : IsClosed (F '' closedBall (0:ℂ) 1) :=
        (isCompact_closedBall (0:ℂ) 1).image_of_continuousOn hFc |>.isClosed
      exact hFimg_closed.closure_subset_iff.2 hwsub hw

/-! ### C4 (-2c, c5c9_scratch.lean 2e3a854c6bb401cfbbb3b5dd04091a84; the closing gluing step
rewritten to use `isJordanCurve_of_loop` instead of its own copy of the `AddCircle` argument) -/

theorem isJordanCurve_image_chord {f : ℂ → ℂ} {ζ₁ ζ₂ : ℂ} (hζ₁ : ‖ζ₁‖ = 1) (hζ₂ : ‖ζ₂‖ = 1)
    (hne : ζ₁ ≠ ζ₂) (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfinj : InjOn f (openSegment ℝ ζ₁ ζ₂)) (hfw : f ζ₁ = f ζ₂)
    (hend : f ζ₁ ∉ f '' openSegment ℝ ζ₁ ζ₂) :
    IsJordanCurve (toExt (f '' segment ℝ ζ₁ ζ₂)) := by
  set seg : ℝ → ℂ := fun t => (1 - t) • ζ₁ + t • ζ₂ with hsegdef
  have hsegIcc : seg '' Icc (0 : ℝ) 1 = segment ℝ ζ₁ ζ₂ := (segment_eq_image ℝ ζ₁ ζ₂).symm
  have hsegIoo : seg '' Ioo (0 : ℝ) 1 = openSegment ℝ ζ₁ ζ₂ := (openSegment_eq_image ℝ ζ₁ ζ₂).symm
  have hsegcont : Continuous seg := by fun_prop
  have hsegmem : ∀ t ∈ Icc (0 : ℝ) 1, seg t ∈ closedBall (0 : ℂ) 1 := by
    intro t ht
    rw [hsegdef]
    simp only
    rw [mem_closedBall, dist_zero_right]
    calc ‖(1 - t) • ζ₁ + t • ζ₂‖ ≤ ‖(1 - t) • ζ₁‖ + ‖t • ζ₂‖ := norm_add_le _ _
      _ = (1 - t) * ‖ζ₁‖ + t * ‖ζ₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
            Real.norm_of_nonneg ht.1]
      _ = 1 := by rw [hζ₁, hζ₂]; ring
  have hseginj : InjOn seg univ := by
    intro s _ t _ hst
    rw [hsegdef] at hst
    simp only at hst
    by_contra hne'
    apply hne
    have hkey : (s - t) • (ζ₂ - ζ₁) = 0 := by
      have heq : (1 - s) • ζ₁ + s • ζ₂ - ((1 - t) • ζ₁ + t • ζ₂) = (s - t) • (ζ₂ - ζ₁) := by
        module
      rw [← heq, hst, sub_self]
    rcases smul_eq_zero.mp hkey with h | h
    · exact absurd (sub_eq_zero.mp h) hne'
    · exact (sub_eq_zero.mp h).symm
  set γ : ℝ → ℂ := fun t => f (seg t) with hγdef
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hf.comp hsegcont.continuousOn hsegmem
  have hγ0 : γ 0 = f ζ₁ := by rw [hγdef]; simp [hsegdef]
  have hγ1 : γ 1 = f ζ₂ := by rw [hγdef]; simp [hsegdef]
  have hγ01 : γ 0 = γ 1 := by rw [hγ0, hγ1, hfw]
  have hγimg : γ '' Icc (0 : ℝ) 1 = f '' segment ℝ ζ₁ ζ₂ := by
    show (f ∘ seg) '' Icc (0:ℝ) 1 = _
    rw [image_comp, hsegIcc]
  have hseg0 : seg 0 = ζ₁ := by rw [hsegdef]; simp
  have hseg1 : seg 1 = ζ₂ := by rw [hsegdef]; simp
  have hγinj : InjOn γ (Ico (0 : ℝ) 1) := by
    intro s hs t ht hst
    rw [hγdef] at hst
    simp only at hst
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← hs0, ← ht0]
      · exfalso
        apply hend
        rw [← hs0, hseg0] at hst
        have htmem : seg t ∈ openSegment ℝ ζ₁ ζ₂ := hsegIoo ▸ mem_image_of_mem seg
          (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, ht.2⟩)
        rw [hst]
        exact mem_image_of_mem f htmem
    · rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · exfalso
        apply hend
        rw [← ht0, hseg0] at hst
        have hsmem : seg s ∈ openSegment ℝ ζ₁ ζ₂ := hsegIoo ▸ mem_image_of_mem seg
          (show s ∈ Ioo (0 : ℝ) 1 from ⟨hs0, hs.2⟩)
        rw [← hst]
        exact mem_image_of_mem f hsmem
      · have hseq : seg s = seg t := hfinj (hsegIoo ▸ ⟨s, ⟨hs0, hs.2⟩, rfl⟩)
          (hsegIoo ▸ ⟨t, ⟨ht0, ht.2⟩, rfl⟩) hst
        exact hseginj (mem_univ s) (mem_univ t) hseq
  rw [← hγimg]
  exact isJordanCurve_of_loop hγcont hγinj hγ01

/-! ### C5 -/

/-- The chord `ζ₁ + t(ζ₂-ζ₁)` for `t:ℝ` meets the unit disc exactly in the open segment. -/
theorem normSq_chord_eq {ζ₁ ζ₂ : ℂ} (hζ₁ : ‖ζ₁‖ = 1) (hζ₂ : ‖ζ₂‖ = 1) (t : ℝ) :
    normSq (ζ₁ + (t:ℂ) * (ζ₂ - ζ₁)) = 1 + normSq (ζ₂ - ζ₁) * (t * (t - 1)) := by
  have h1 : normSq ζ₁ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ₁]; norm_num
  have h2 : normSq ζ₂ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ₂]; norm_num
  simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2 ⊢
  linear_combination (1 - t) * h1 + t * h2

theorem mem_unitDisc_chord_iff {ζ₁ ζ₂ : ℂ} (hζ₁ : ‖ζ₁‖ = 1) (hζ₂ : ‖ζ₂‖ = 1) (hne : ζ₁ ≠ ζ₂)
    (t : ℝ) : ζ₁ + (t:ℂ) * (ζ₂ - ζ₁) ∈ unitDisc ↔ t ∈ Ioo (0:ℝ) 1 := by
  have hD0 : (0:ℝ) < normSq (ζ₂ - ζ₁) := by
    rw [normSq_pos]
    intro h; exact hne (by linear_combination -h)
  rw [unitDisc, mem_ball_zero_iff, ← normSq_lt_one_iff, normSq_chord_eq hζ₁ hζ₂]
  constructor
  · intro h
    have : t * (t - 1) < 0 := by nlinarith [h, hD0]
    rcases lt_trichotomy t 0 with ht | ht | ht
    · nlinarith [this]
    · nlinarith [this, ht]
    · rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
      · exact ⟨ht, ht1⟩
      · nlinarith [this, ht1]
      · nlinarith [this]
  · intro ⟨h1, h2⟩
    nlinarith [mul_pos h1 (by linarith : (0:ℝ) < 1 - t), hD0]

set_option maxHeartbeats 4000000 in
/-- **C5** (corrected (d2); `hΩJ` ADDED — needed for "inside of the loop lies in Ω"). -/
theorem exists_arc_const_of_jordan_curve_meets_frontier_once {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩJ : IsJordanCurve (toExt (frontier Ω))) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hFf : ∀ z ∈ unitDisc, F z = f z)
    (hFc : ContinuousOn F (closedBall 0 1)) (hFsphere : F '' sphere (0 : ℂ) 1 ⊆ frontier Ω)
    {ζ₁ ζ₂ w : ℂ} (hζ₁ : ‖ζ₁‖ = 1) (hζ₂ : ‖ζ₂‖ = 1) (hne : ζ₁ ≠ ζ₂)
    (hFζ₁ : F ζ₁ = w) (hFζ₂ : F ζ₂ = w)
    (hJ : IsJordanCurve (toExt (F '' segment ℝ ζ₁ ζ₂)))
    (hJfr : F '' segment ℝ ζ₁ ζ₂ ∩ frontier Ω = {w}) :
    ∃ A : Set ℂ, A ⊆ sphere (0 : ℂ) 1 ∧ A.Nontrivial ∧ IsPreconnected A ∧ ∀ ζ ∈ A, F ζ = w := by
  have hΩfr_disj : Disjoint Ω (frontier Ω) := by rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  set Δ : ℂ := ζ₂ - ζ₁ with hΔ_def
  have hΔne : Δ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hnsqΔpos : 0 < normSq Δ := normSq_pos.mpr hΔne
  set L : ℂ → ℝ := fun z => ((z - ζ₁) * conj Δ).im with hL_def
  have hLapp : ∀ z, L z = ((z - ζ₁) * conj Δ).im := fun z => rfl
  have hLcont : Continuous L := by
    apply Complex.continuous_im.comp
    exact (continuous_id.sub continuous_const).mul continuous_const
  have hLzero : ∀ z, L z = 0 ↔ ∃ t : ℝ, z = ζ₁ + (t:ℂ) * Δ := by
    intro z
    rw [hLapp]
    constructor
    · intro h
      set τ0 : ℂ := (z - ζ₁) / Δ with hτ0_def
      have hz : z - ζ₁ = τ0 * Δ := by rw [hτ0_def]; field_simp
      have heq : (z - ζ₁) * conj Δ = (normSq Δ : ℂ) * τ0 := by
        rw [hz, normSq_eq_conj_mul_self]; ring
      have hτim : τ0.im = 0 := by
        have him := congrArg Complex.im heq
        rw [im_ofReal_mul, h] at him
        exact (mul_eq_zero.mp him.symm).resolve_left hnsqΔpos.ne'
      have hτreal : τ0 = (τ0.re : ℂ) := Complex.ext rfl (by simp [hτim])
      refine ⟨τ0.re, ?_⟩
      rw [hτreal] at hz
      linear_combination hz
    · rintro ⟨t, rfl⟩
      have heq2 : (ζ₁ + (t:ℂ)*Δ - ζ₁) = (t:ℂ)*Δ := by ring
      rw [heq2, Complex.mul_im]
      simp; ring
  have hLζ1 : L ζ₁ = 0 := by rw [hLapp]; simp
  have hLζ2 : L ζ₂ = 0 := by
    rw [hLapp]
    have hΔeq : ζ₂ - ζ₁ = Δ := rfl
    rw [hΔeq, Complex.mul_conj]
    simp
  set D1 : Set ℂ := ball (0:ℂ) 1 ∩ {z | 0 < L z} with hD1_def
  set D2 : Set ℂ := ball (0:ℂ) 1 ∩ {z | L z < 0} with hD2_def
  have hLaffine : ∀ (z w : ℂ) (a b : ℝ), a + b = 1 → L (a • z + b • w) = a * L z + b * L w := by
    intro z w a b hab
    rw [hLapp, hLapp, hLapp, Complex.real_smul, Complex.real_smul]
    have ha : a = 1 - b := by linarith
    subst ha
    push_cast
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.add_re,
      Complex.mul_re, Complex.one_re, Complex.one_im]
    ring
  have hD1convex : Convex ℝ D1 := by
    apply Convex.inter (convex_ball 0 1)
    intro z hz w hw a b ha hb hab
    simp only [mem_setOf_eq] at hz hw ⊢
    rw [hLaffine z w a b hab]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]; simpa using hw
    · nlinarith [mul_pos ha0 hz, mul_nonneg hb hw.le]
  have hD2convex : Convex ℝ D2 := by
    apply Convex.inter (convex_ball 0 1)
    intro z hz w hw a b ha hb hab
    simp only [mem_setOf_eq] at hz hw ⊢
    rw [hLaffine z w a b hab]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]; simpa using hw
    · nlinarith [mul_neg_of_pos_of_neg ha0 hz, mul_nonpos_of_nonneg_of_nonpos hb hw.le]
  have hD1open : IsOpen D1 := isOpen_ball.inter (isOpen_Ioi.preimage hLcont)
  have hD2open : IsOpen D2 := isOpen_ball.inter (isOpen_Iio.preimage hLcont)
  -- midpoint strictly interior
  set m : ℂ := (ζ₁+ζ₂)/2 with hm_def
  have h1 : normSq ζ₁ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ₁]; norm_num
  have h2 : normSq ζ₂ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ₂]; norm_num
  have hexpand1 : normSq (ζ₁-ζ₂) = normSq ζ₁ - 2*(ζ₁*conj ζ₂).re + normSq ζ₂ := by
    simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]; ring
  have hexpand2 : normSq (ζ₁+ζ₂) = normSq ζ₁ + 2*(ζ₁*conj ζ₂).re + normSq ζ₂ := by
    simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]; ring
  have hd0 : 0 < normSq (ζ₁ - ζ₂) := normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hmlt : normSq m < 1 := by
    have hm2 : (2:ℂ)*m = ζ₁+ζ₂ := by rw [hm_def]; ring
    have hkey : normSq (2*m) = normSq ζ₁ + 2*(ζ₁*conj ζ₂).re + normSq ζ₂ := by
      rw [hm2]; exact hexpand2
    rw [Complex.normSq_mul] at hkey
    have h4 : normSq (2:ℂ) = 4 := by simp [normSq_apply]; norm_num
    rw [h4] at hkey
    rw [hexpand1] at hd0
    linarith [h1, h2, hkey, hd0]
  set c : ℝ := (m * conj Δ).im with hc_def
  have hformula : ∀ s : ℝ, normSq (m + (s:ℂ)*Complex.I*Δ) = normSq m + 2*c*s + s^2 * normSq Δ := by
    intro s
    simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hc_def,
      Complex.conj_re, Complex.conj_im] at *
    ring
  have hLatz : ∀ s:ℝ, L (m + (s:ℂ)*Complex.I*Δ) = normSq Δ * s := by
    intro s
    rw [hLapp]
    have heqz : (m+(s:ℂ)*Complex.I*Δ - ζ₁) * conj Δ = (normSq Δ : ℝ) * (1/2+(s:ℂ)*Complex.I) := by
      rw [hm_def]
      have hmc : Δ * conj Δ = (normSq Δ : ℝ) := Complex.mul_conj Δ
      field_simp
      linear_combination (1+2*(s:ℂ)*Complex.I) * hmc
    rw [heqz, im_ofReal_mul]
    simp
  -- both D1, D2 nonempty
  have hgcont : Continuous (fun s:ℝ => normSq m+2*c*s+s^2*normSq Δ) := by fun_prop
  have hg0 : (normSq m+2*c*(0:ℝ)+(0:ℝ)^2*normSq Δ) < 1 := by simpa using hmlt
  have hnbhd : {s:ℝ | normSq m+2*c*s+s^2*normSq Δ < 1} ∈ 𝓝 (0:ℝ) :=
    hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hg0)
  obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  set s0 : ℝ := ε/2 with hs0_def
  have hs0pos : 0 < s0 := by rw [hs0_def]; linarith
  have hs0mem : normSq m + 2*c*s0+s0^2*normSq Δ < 1 :=
    hεsub (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_lt]; constructor <;> [linarith; linarith]))
  have hs0mem' : normSq m + 2*c*(-s0)+(-s0)^2*normSq Δ < 1 :=
    hεsub (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_lt]; constructor <;> [linarith; linarith]))
  have hz1mem : m + (s0:ℂ)*Complex.I*Δ ∈ D1 := by
    constructor
    · rw [mem_ball_zero_iff, ← normSq_lt_one_iff, hformula]; exact hs0mem
    · show 0 < L (m+(s0:ℂ)*Complex.I*Δ)
      rw [hLatz]; positivity
  have hz2mem : m + ((-s0:ℝ):ℂ)*Complex.I*Δ ∈ D2 := by
    constructor
    · rw [mem_ball_zero_iff, ← normSq_lt_one_iff, hformula]; exact hs0mem'
    · show L (m+((-s0:ℝ):ℂ)*Complex.I*Δ) < 0
      rw [hLatz]
      have hneg : normSq Δ * (-s0) < 0 := by nlinarith [hnsqΔpos, hs0pos]
      exact hneg
  -- exact sphere crossings with both signs of L (for the "opposite signs" argument later)
  set Dcr : ℝ := c^2 + normSq Δ * (1 - normSq m) with hDcr_def
  have hDcrpos : 0 < Dcr := by
    nlinarith [sq_nonneg c, mul_pos hnsqΔpos (by linarith : (0:ℝ) < 1 - normSq m)]
  set sqrtD : ℝ := Real.sqrt Dcr with hsqrtD_def
  have hsqrtDsq : sqrtD * sqrtD = Dcr := Real.mul_self_sqrt hDcrpos.le
  have hsqrtDpos : 0 < sqrtD := Real.sqrt_pos.mpr hDcrpos
  have hcbound : c^2 < Dcr := by
    have hpos : 0 < normSq Δ * (1 - normSq m) := mul_pos hnsqΔpos (by linarith)
    linarith [hDcr_def]
  have hcabs : |c| < sqrtD := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg c) hcbound
  set sa : ℝ := (-c+sqrtD)/normSq Δ with hsa_def
  set sb : ℝ := (-c-sqrtD)/normSq Δ with hsb_def
  have hsa_root : normSq Δ * sa^2 + 2*c*sa = 1 - normSq m := by
    rw [hsa_def]; field_simp; nlinarith [hsqrtDsq]
  have hsb_root : normSq Δ * sb^2 + 2*c*sb = 1 - normSq m := by
    rw [hsb_def]; field_simp; nlinarith [hsqrtDsq]
  have hsa_pos : 0 < sa := by
    rw [hsa_def]; apply div_pos _ hnsqΔpos
    nlinarith [abs_lt.mp hcabs]
  have hsb_neg : sb < 0 := by
    rw [hsb_def]; apply div_neg_of_neg_of_pos _ hnsqΔpos
    nlinarith [abs_lt.mp hcabs]
  have hza_sphere : normSq (m+(sa:ℂ)*Complex.I*Δ) = 1 := by rw [hformula]; linarith [hsa_root]
  have hzb_sphere : normSq (m+(sb:ℂ)*Complex.I*Δ) = 1 := by rw [hformula]; linarith [hsb_root]
  have hLza : L (m+(sa:ℂ)*Complex.I*Δ) > 0 := by rw [hLatz]; positivity
  have hLzb : L (m+(sb:ℂ)*Complex.I*Δ) < 0 := by
    rw [hLatz]; nlinarith [hnsqΔpos, hsb_neg]
  have hnorm_eq_one_of_normSq : ∀ z:ℂ, normSq z = 1 → ‖z‖ = 1 := by
    intro z hz
    rw [Complex.normSq_eq_norm_sq] at hz
    rw [← Real.sqrt_sq (norm_nonneg z), hz, Real.sqrt_one]
  have hza_mem_sphere : (m+(sa:ℂ)*Complex.I*Δ) ∈ sphere (0:ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (hnorm_eq_one_of_normSq _ hza_sphere)
  have hzb_mem_sphere : (m+(sb:ℂ)*Complex.I*Δ) ∈ sphere (0:ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (hnorm_eq_one_of_normSq _ hzb_sphere)
  -- convex combination reaches the boundary (D1 side)
  have hconvex_combo1 : ∀ (p ζ : ℂ), p ∈ D1 → ‖ζ‖ ≤ 1 → 0 ≤ L ζ → ζ ∈ closure D1 := by
    intro p ζ hp hζnorm hζL
    have hpnorm : ‖p‖ < 1 := mem_ball_zero_iff.mp hp.1
    have hpL : 0 < L p := hp.2
    rw [mem_closure_iff_seq_limit]
    refine ⟨fun n => (1 - (1 - 1/((n:ℝ)+1))) • p + (1 - 1/((n:ℝ)+1)) • ζ, ?_, ?_⟩
    · intro n
      have hden : (0:ℝ) < (n:ℝ)+1 := by positivity
      set t : ℝ := 1 - 1/((n:ℝ)+1) with ht_def
      have ht0 : 0 ≤ t := by
        have hle1 : 1/((n:ℝ)+1) ≤ 1 := by
          rw [div_le_one hden]
          have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        rw [ht_def]; linarith
      have ht1 : t < 1 := by
        have hgt0 : 0 < 1/((n:ℝ)+1) := by positivity
        rw [ht_def]; linarith
      constructor
      · rw [mem_ball_zero_iff]
        calc ‖(1-t) • p + t • ζ‖ ≤ ‖(1-t)•p‖ + ‖t•ζ‖ := norm_add_le _ _
          _ = (1-t)*‖p‖ + t*‖ζ‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
          _ ≤ (1-t)*‖p‖ + t*1 := by nlinarith [hζnorm, ht0]
          _ < 1 := by nlinarith [hpnorm, ht1]
      · show 0 < L ((1-t)•p+t•ζ)
        rw [hLaffine p ζ (1-t) t (by ring)]
        nlinarith [hpL, hζL, ht1]
    · have htend : Tendsto (fun n:ℕ => 1 - (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 (1-0)) :=
        Tendsto.const_sub 1 tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [sub_zero] at htend
      have hcombo : Tendsto (fun n:ℕ => (1 - (1 - (1:ℝ)/((n:ℝ)+1))) • p +
          (1 - (1:ℝ)/((n:ℝ)+1)) • ζ) atTop (𝓝 (((1:ℝ)-1)•p+(1:ℝ)•ζ)) := by
        apply Tendsto.add
        · exact (Tendsto.const_sub 1 htend).smul_const p
        · exact htend.smul_const ζ
      simpa using hcombo
  -- convex combination reaches the boundary (D2 side, mirror)
  have hconvex_combo2 : ∀ (p ζ : ℂ), p ∈ D2 → ‖ζ‖ ≤ 1 → L ζ ≤ 0 → ζ ∈ closure D2 := by
    intro p ζ hp hζnorm hζL
    have hpnorm : ‖p‖ < 1 := mem_ball_zero_iff.mp hp.1
    have hpL : L p < 0 := hp.2
    rw [mem_closure_iff_seq_limit]
    refine ⟨fun n => (1 - (1 - 1/((n:ℝ)+1))) • p + (1 - 1/((n:ℝ)+1)) • ζ, ?_, ?_⟩
    · intro n
      have hden : (0:ℝ) < (n:ℝ)+1 := by positivity
      set t : ℝ := 1 - 1/((n:ℝ)+1) with ht_def
      have ht0 : 0 ≤ t := by
        have hle1 : 1/((n:ℝ)+1) ≤ 1 := by
          rw [div_le_one hden]
          have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        rw [ht_def]; linarith
      have ht1 : t < 1 := by
        have hgt0 : 0 < 1/((n:ℝ)+1) := by positivity
        rw [ht_def]; linarith
      constructor
      · rw [mem_ball_zero_iff]
        calc ‖(1-t) • p + t • ζ‖ ≤ ‖(1-t)•p‖ + ‖t•ζ‖ := norm_add_le _ _
          _ = (1-t)*‖p‖ + t*‖ζ‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
          _ ≤ (1-t)*‖p‖ + t*1 := by nlinarith [hζnorm, ht0]
          _ < 1 := by nlinarith [hpnorm, ht1]
      · show L ((1-t)•p+t•ζ) < 0
        rw [hLaffine p ζ (1-t) t (by ring)]
        nlinarith [hpL, hζL, ht1]
    · have htend : Tendsto (fun n:ℕ => 1 - (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 (1-0)) :=
        Tendsto.const_sub 1 tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [sub_zero] at htend
      have hcombo : Tendsto (fun n:ℕ => (1 - (1 - (1:ℝ)/((n:ℝ)+1))) • p +
          (1 - (1:ℝ)/((n:ℝ)+1)) • ζ) atTop (𝓝 (((1:ℝ)-1)•p+(1:ℝ)•ζ)) := by
        apply Tendsto.add
        · exact (Tendsto.const_sub 1 htend).smul_const p
        · exact htend.smul_const ζ
      simpa using hcombo
  -- partition of the disc by the chord
  have hD1sub : D1 ⊆ unitDisc := inter_subset_left
  have hD2sub : D2 ⊆ unitDisc := inter_subset_left
  have hmemOpenSeg : ∀ z : ℂ, z ∈ openSegment ℝ ζ₁ ζ₂ ↔ ∃ t ∈ Ioo (0:ℝ) 1, z = ζ₁ + (t:ℂ)*Δ := by
    intro z
    rw [openSegment_eq_image' ℝ ζ₁ ζ₂]
    constructor
    · rintro ⟨t, ht, hzeq⟩
      simp only [] at hzeq
      exact ⟨t, ht, by rw [← hzeq, Complex.real_smul]⟩
    · rintro ⟨t, ht, hzeq⟩
      refine ⟨t, ht, ?_⟩
      simp only []
      rw [hzeq, Complex.real_smul]
  have hopenSegSub : openSegment ℝ ζ₁ ζ₂ ⊆ unitDisc := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := (hmemOpenSeg z).mp hz
    exact (mem_unitDisc_chord_iff hζ₁ hζ₂ hne t).mpr ht
  have hpartition : unitDisc = D1 ∪ D2 ∪ openSegment ℝ ζ₁ ζ₂ := by
    show ball (0:ℂ) 1 = D1 ∪ D2 ∪ openSegment ℝ ζ₁ ζ₂
    ext z
    constructor
    · intro hz
      rcases lt_trichotomy (L z) 0 with h|h|h
      · exact Or.inl (Or.inr ⟨hz, h⟩)
      · obtain ⟨t, rfl⟩ := (hLzero z).mp h
        have ht : t ∈ Ioo (0:ℝ) 1 := (mem_unitDisc_chord_iff hζ₁ hζ₂ hne t).mp hz
        exact Or.inr ((hmemOpenSeg _).mpr ⟨t, ht, rfl⟩)
      · exact Or.inl (Or.inl ⟨hz, h⟩)
    · intro hz
      rcases hz with (⟨hz1,-⟩|⟨hz1,-⟩)|hz1
      · exact hz1
      · exact hz1
      · exact hopenSegSub hz1
  have hD1D2disj : D1 ∩ D2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨-,hz1⟩,⟨-,hz2⟩⟩
    simp only [mem_setOf_eq] at hz1 hz2
    linarith [hz1,hz2]
  have hD1openSegDisj : D1 ∩ openSegment ℝ ζ₁ ζ₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨-,hzL⟩, hzseg⟩
    simp only [mem_setOf_eq] at hzL
    obtain ⟨t,ht,rfl⟩ := (hmemOpenSeg z).mp hzseg
    have hz0 : L (ζ₁+(t:ℂ)*Δ) = 0 := (hLzero _).mpr ⟨t, rfl⟩
    linarith [hzL, hz0]
  have hD2openSegDisj : D2 ∩ openSegment ℝ ζ₁ ζ₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨-,hzL⟩, hzseg⟩
    simp only [mem_setOf_eq] at hzL
    obtain ⟨t,ht,rfl⟩ := (hmemOpenSeg z).mp hzseg
    have hz0 : L (ζ₁+(t:ℂ)*Δ) = 0 := (hLzero _).mpr ⟨t, rfl⟩
    linarith [hzL, hz0]
  -- conformal images of D1, D2
  have hD1conn : IsConnected D1 := ⟨⟨_, hz1mem⟩, hD1convex.isPreconnected⟩
  have hD2conn : IsConnected D2 := ⟨⟨_, hz2mem⟩, hD2convex.isPreconnected⟩
  have hfD1 : IsConformalOnto f D1 (f '' D1) := ⟨hf.1.mono hD1sub, hf.2.1.mono hD1sub, rfl⟩
  have hfD2 : IsConformalOnto f D2 (f '' D2) := ⟨hf.1.mono hD2sub, hf.2.1.mono hD2sub, rfl⟩
  have hfD1open : IsOpen (f '' D1) := hfD1.isOpen hD1open
  have hfD2open : IsOpen (f '' D2) := hfD2.isOpen hD2open
  have hfD1conn : IsConnected (f '' D1) := hD1conn.image f (hf.1.continuousOn.mono hD1sub)
  have hfD2conn : IsConnected (f '' D2) := hD2conn.image f (hf.1.continuousOn.mono hD2sub)
  have hfD1sub : f '' D1 ⊆ Ω := hf.2.2 ▸ image_mono hD1sub
  have hfD2sub : f '' D2 ⊆ Ω := hf.2.2 ▸ image_mono hD2sub
  have hfD1D2disj : Disjoint (f '' D1) (f '' D2) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.InjOn.image_inter hf.2.1 hD1sub hD2sub, hD1D2disj,
      Set.image_empty]
  -- J, σ decomposition
  set Jset : Set ℂ := F '' segment ℝ ζ₁ ζ₂ with hJset_def
  set σ : Set ℂ := F '' openSegment ℝ ζ₁ ζ₂ with hσ_def
  have hseg : segment ℝ ζ₁ ζ₂ = openSegment ℝ ζ₁ ζ₂ ∪ {ζ₁,ζ₂} := by
    rw [segment_eq_image' ℝ ζ₁ ζ₂, openSegment_eq_image' ℝ ζ₁ ζ₂]
    ext z
    simp only [mem_image, mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨t, ⟨ht0,ht1⟩, rfl⟩
      rcases eq_or_lt_of_le ht0 with h0|h0
      · exact Or.inr (Or.inl (by rw [← h0]; simp))
      rcases eq_or_lt_of_le ht1 with h1|h1
      · exact Or.inr (Or.inr (by rw [h1]; simp))
      · exact Or.inl ⟨t,⟨h0,h1⟩,rfl⟩
    · rintro (⟨t,⟨ht0,ht1⟩,rfl⟩|rfl|rfl)
      · exact ⟨t,⟨ht0.le,ht1.le⟩,rfl⟩
      · exact ⟨0,⟨le_refl 0,zero_le_one⟩,by simp⟩
      · exact ⟨1,⟨zero_le_one,le_refl 1⟩,by simp⟩
  have hJeq : Jset = σ ∪ {w} := by
    rw [hJset_def, hσ_def, hseg, image_union]
    congr 1
    rw [Set.image_insert_eq, Set.image_singleton, hFζ₁, hFζ₂]
    simp
  have hσeq : σ = f '' openSegment ℝ ζ₁ ζ₂ := by
    rw [hσ_def]
    apply Set.image_congr
    intro z hz; exact hFf z (hopenSegSub hz)
  have hσΩ : σ ⊆ Ω := by
    rw [hσeq]; exact hf.2.2 ▸ image_mono hopenSegSub
  have hwmem : w ∈ Jset ∩ frontier Ω := by rw [hJfr]; exact Set.mem_singleton w
  have hwfr : w ∈ frontier Ω := hwmem.2
  have hwnotinΩ : w ∉ Ω := fun h => Set.disjoint_left.1 hΩfr_disj h hwfr
  have hfD1disjW : f '' D1 ∩ {w} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1,hz2⟩
    rw [mem_singleton_iff] at hz2
    exact hwnotinΩ (hz2 ▸ hfD1sub hz1)
  have hfD2disjW : f '' D2 ∩ {w} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1,hz2⟩
    rw [mem_singleton_iff] at hz2
    exact hwnotinΩ (hz2 ▸ hfD2sub hz1)
  have hfD1disjσ : Disjoint (f '' D1) σ := by
    rw [hσeq, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hf.2.1 hD1sub hopenSegSub, hD1openSegDisj, Set.image_empty]
  have hfD2disjσ : Disjoint (f '' D2) σ := by
    rw [hσeq, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hf.2.1 hD2sub hopenSegSub, hD2openSegDisj, Set.image_empty]
  have hfD1disjJ : Disjoint (f '' D1) Jset := by
    rw [hJeq, Set.disjoint_union_right]
    exact ⟨hfD1disjσ, Set.disjoint_iff_inter_eq_empty.mpr hfD1disjW⟩
  have hfD2disjJ : Disjoint (f '' D2) Jset := by
    rw [hJeq, Set.disjoint_union_right]
    exact ⟨hfD2disjσ, Set.disjoint_iff_inter_eq_empty.mpr hfD2disjW⟩
  -- JCT on Jset
  obtain ⟨Iset, Oset, hIo, hOo, hIc, hOc, hIO, hIJ, hOJ, huniv, hIb, hOb⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  have hfrI : frontier Iset = Jset :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hJ hIo hOo hIc hOc hIO hIJ hOJ huniv).1
  have hJsub : Jset ⊆ closure Ω := by
    rw [hJeq]
    apply union_subset (hσΩ.trans subset_closure)
    rw [singleton_subset_iff]
    exact frontier_subset_closure hwfr
  obtain ⟨hEc, hEb⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hΩo hΩc hΩbdd hΩJ
  have hEJ : Disjoint (closure Ω)ᶜ Jset := Set.disjoint_left.2 fun z hz hz2 => hz (hJsub hz2)
  have hEO : (closure Ω)ᶜ ⊆ Oset :=
    subset_unbounded_piece_of_isConnected_not_isBounded hIo hOo hIO hIJ hOJ huniv hIb hEc hEb hEJ
  have hIcl : Iset ⊆ closure Ω := fun z hz => by_contra fun hzc => Set.disjoint_left.1 hIO hz (hEO hzc)
  have hIΩ : Iset ⊆ Ω :=
    (interior_maximal hIcl hIo).trans (interior_closure_subset_of_isJordanCurve_frontier hΩo hΩc hΩbdd hΩJ)
  -- Ω \ σ = f(D1) ∪ f(D2)
  have hΩσeq : Ω \ σ = f '' D1 ∪ f '' D2 := by
    ext z
    constructor
    · rintro ⟨hzΩ, hzσ⟩
      rw [← hf.2.2, hpartition] at hzΩ
      obtain ⟨u, hu, rfl⟩ := hzΩ
      rcases hu with (hu|hu)|hu
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr ⟨u, hu, rfl⟩
      · exfalso; apply hzσ; rw [hσeq]; exact ⟨u, hu, rfl⟩
    · rintro (⟨u,hu,rfl⟩|⟨u,hu,rfl⟩)
      · exact ⟨hfD1sub ⟨u,hu,rfl⟩, fun hmem => Set.disjoint_left.1 hfD1disjσ ⟨u,hu,rfl⟩ hmem⟩
      · exact ⟨hfD2sub ⟨u,hu,rfl⟩, fun hmem => Set.disjoint_left.1 hfD2disjσ ⟨u,hu,rfl⟩ hmem⟩
  have hIsubΩσ : Iset ⊆ Ω \ σ := fun z hz =>
    ⟨hIΩ hz, fun hzσ => Set.disjoint_left.1 hIJ hz (by rw [hJeq]; exact Or.inl hzσ)⟩
  have hI_sub : Iset ⊆ f '' D1 ∪ f '' D2 := hΩσeq ▸ hIsubΩσ
  have hdichI : Iset ⊆ f '' D1 ∨ Iset ⊆ f '' D2 :=
    isPreconnected_iff_subset_of_disjoint.1 hIc.isPreconnected (f '' D1) (f '' D2) hfD1open hfD2open
      hI_sub
      (by rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨-,h1,h2⟩
          exact Set.disjoint_left.1 hfD1D2disj h1 h2)
  have hfD1subIO : f '' D1 ⊆ Iset ∪ Oset := fun z hz =>
    (huniv ▸ mem_univ z : z ∈ Iset ∪ Oset ∪ Jset).elim id
      (fun h => absurd h (Set.disjoint_left.1 hfD1disjJ hz))
  have hfD2subIO : f '' D2 ⊆ Iset ∪ Oset := fun z hz =>
    (huniv ▸ mem_univ z : z ∈ Iset ∪ Oset ∪ Jset).elim id
      (fun h => absurd h (Set.disjoint_left.1 hfD2disjJ hz))
  have hDkey : f '' D1 ⊆ Iset ∨ f '' D2 ⊆ Iset := by
    rcases hdichI with h|h
    · refine Or.inl ?_
      rcases isPreconnected_iff_subset_of_disjoint.1 hfD1conn.isPreconnected Iset Oset hIo hOo
        hfD1subIO
        (by rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨-,h1,h2⟩
            exact Set.disjoint_left.1 hIO h1 h2) with hc|hc
      · exact hc
      · exfalso
        obtain ⟨p,hp⟩ := hIc.nonempty
        exact Set.disjoint_left.1 hIO hp (hc (h hp))
    · refine Or.inr ?_
      rcases isPreconnected_iff_subset_of_disjoint.1 hfD2conn.isPreconnected Iset Oset hIo hOo
        hfD2subIO
        (by rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨-,h1,h2⟩
            exact Set.disjoint_left.1 hIO h1 h2) with hc|hc
      · exact hc
      · exfalso
        obtain ⟨p,hp⟩ := hIc.nonempty
        exact Set.disjoint_left.1 hIO hp (hc (h hp))
  -- the closure-to-w key lemma
  have hclosureToW : ∀ (Dk : Set ℂ), Dk ⊆ unitDisc → f '' Dk ⊆ Iset →
      ∀ ζ, ζ ∈ closure Dk → ζ ∈ sphere (0:ℂ) 1 → F ζ = w := by
    intro Dk hDksub hDkI ζ hζcl hζsph
    have hζcb : ζ ∈ closedBall (0:ℂ) 1 :=
      closure_ball_subset_closedBall (closure_mono hDksub hζcl)
    obtain ⟨u,hu_mem,hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hζcl
    have hun_cb : ∀ n, u n ∈ closedBall (0:ℂ) 1 := fun n => ball_subset_closedBall (hDksub (hu_mem n))
    have hwithin : Tendsto u atTop (𝓝[closedBall (0:ℂ) 1] ζ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_tendsto
        (Filter.Eventually.of_forall hun_cb)
    have hFu : Tendsto (F ∘ u) atTop (𝓝 (F ζ)) := (hFc ζ hζcb).tendsto.comp hwithin
    have hFζcl : F ζ ∈ closure (F '' Dk) :=
      mem_closure_of_tendsto hFu (Filter.Eventually.of_forall fun n => mem_image_of_mem F (hu_mem n))
    have hFDkeq : F '' Dk = f '' Dk := by
      apply Set.image_congr
      intro z hz; exact hFf z (hDksub hz)
    rw [hFDkeq] at hFζcl
    have hFζclI : F ζ ∈ closure Iset := closure_mono hDkI hFζcl
    rw [closure_eq_interior_union_frontier, hIo.interior_eq, hfrI] at hFζclI
    have hFζfr : F ζ ∈ frontier Ω := hFsphere ⟨ζ, hζsph, rfl⟩
    have hFζnotI : F ζ ∉ Iset := fun hmem => Set.disjoint_left.1 hΩfr_disj (hIΩ hmem) hFζfr
    rcases hFζclI with h|h
    · exact absurd h hFζnotI
    · have hmemw : F ζ ∈ Jset ∩ frontier Ω := ⟨h, hFζfr⟩
      rw [hJfr] at hmemw
      exact hmemw
  -- Circle parametrization and C6 arc split
  set s1 : Circle := ⟨ζ₁, by show ζ₁ ∈ sphere (0:ℂ) 1; rw [mem_sphere_zero_iff_norm]; exact hζ₁⟩
    with hs1_def
  set s2 : Circle := ⟨ζ₂, by show ζ₂ ∈ sphere (0:ℂ) 1; rw [mem_sphere_zero_iff_norm]; exact hζ₂⟩
    with hs2_def
  have hs1coe : (s1:ℂ) = ζ₁ := rfl
  have hs2coe : (s2:ℂ) = ζ₂ := rfl
  have hφcont : Continuous (fun z:Circle => (z:ℂ)) := by fun_prop
  have hφinj : Function.Injective (fun z:Circle => (z:ℂ)) := Subtype.coe_injective
  have hs1s2ne : s1 ≠ s2 := by
    intro h; exact hne (by rw [← hs1coe, ← hs2coe, h])
  have hrange : range (fun z:Circle => (z:ℂ)) = sphere (0:ℂ) 1 := by
    ext z; constructor
    · rintro ⟨s,rfl⟩; exact s.2
    · intro hz; exact ⟨⟨z,hz⟩, rfl⟩
  obtain ⟨hτarcC, τ', hτ'arc, hτunion, hτinter⟩ :=
    isArcEndC_split_circleShortArc hφcont hφinj hs1s2ne
  set τ : Set ℂ := (fun z:Circle => (z:ℂ)) '' circleShortArc s1 s2 with hτ_def
  rw [hs1coe, hs2coe] at hτarcC hτ'arc hτinter
  rw [hrange] at hτunion
  have hτsub : τ ⊆ sphere (0:ℂ) 1 := hrange ▸ (image_subset_range _ _)
  have hτ'sub : τ' ⊆ sphere (0:ℂ) 1 := by
    rw [← hτunion]; exact subset_union_right
  have hendpts : ∀ {A : Set ℂ} {v w' : ℂ}, IsArcEndC A v w' → v ∈ A ∧ w' ∈ A := by
    rintro A v w' ⟨γ, hAeq, -, -, hγ0, hγ1⟩
    rw [hAeq]
    exact ⟨⟨0, left_mem_Icc.2 zero_le_one, hγ0⟩, ⟨1, right_mem_Icc.2 zero_le_one, hγ1⟩⟩
  have hτendpts : ζ₁ ∈ τ ∧ ζ₂ ∈ τ := hendpts hτarcC
  have hτ'endpts : ζ₁ ∈ τ' ∧ ζ₂ ∈ τ' := hendpts hτ'arc
  -- sign characterization on the sphere
  have hLzero_sphere : ∀ z ∈ sphere (0:ℂ) 1, L z = 0 → z = ζ₁ ∨ z = ζ₂ := by
    intro z hz hLz
    obtain ⟨t,rfl⟩ := (hLzero z).mp hLz
    rw [mem_sphere_zero_iff_norm] at hz
    have hn1 : normSq (ζ₁+(t:ℂ)*Δ) = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [normSq_chord_eq hζ₁ hζ₂ t] at hn1
    have h2 : normSq Δ * (t*(t-1)) = 0 := by linarith [hn1]
    have ht0 : t*(t-1) = 0 := (mul_eq_zero.mp h2).resolve_left hnsqΔpos.ne'
    rcases mul_eq_zero.mp ht0 with h|h
    · left; rw [h]; simp
    · right
      have ht1 : t = 1 := by linarith
      rw [ht1]; simp [hΔ_def]
  have hsign_of_conn : ∀ (A : Set ℂ), A ⊆ sphere (0:ℂ) 1 → IsConnected (A \ {ζ₁,ζ₂}) →
      (∀ z ∈ A\{ζ₁,ζ₂}, 0 < L z) ∨ (∀ z ∈ A\{ζ₁,ζ₂}, L z < 0) := by
    intro A hAsub hAconn
    have hAdiff_Lne0 : ∀ z ∈ A\{ζ₁,ζ₂}, L z ≠ 0 := by
      intro z hz hLz
      rcases hLzero_sphere z (hAsub hz.1) hLz with h|h
      · exact hz.2 (Or.inl h)
      · exact hz.2 (Or.inr h)
    have himg_conn : IsPreconnected (L '' (A\{ζ₁,ζ₂})) :=
      hAconn.isPreconnected.image L hLcont.continuousOn
    have himg_sub : L '' (A\{ζ₁,ζ₂}) ⊆ Iio (0:ℝ) ∪ Ioi (0:ℝ) := by
      rintro r ⟨z,hz,rfl⟩
      rcases lt_trichotomy (L z) 0 with h|h|h
      · exact Or.inl h
      · exact absurd h (hAdiff_Lne0 z hz)
      · exact Or.inr h
    rcases isPreconnected_iff_subset_of_disjoint.1 himg_conn (Iio 0) (Ioi 0) isOpen_Iio isOpen_Ioi
      himg_sub
      (by rw [Set.eq_empty_iff_forall_notMem]; rintro r ⟨-,h1,h2⟩
          rw [mem_Iio] at h1; rw [mem_Ioi] at h2; linarith)
      with h|h
    · exact Or.inr (fun z hz => h ⟨z,hz,rfl⟩)
    · exact Or.inl (fun z hz => h ⟨z,hz,rfl⟩)
  have hτsign := hsign_of_conn τ hτsub (isConnected_arcEndC_diff_endpoints hτarcC)
  have hτ'sign := hsign_of_conn τ' hτ'sub (isConnected_arcEndC_diff_endpoints hτ'arc)
  have hnorm_eq_one_of_normSq : ∀ z:ℂ, normSq z = 1 → ‖z‖ = 1 := by
    intro z hz
    rw [Complex.normSq_eq_norm_sq] at hz
    rw [← Real.sqrt_sq (norm_nonneg z), hz, Real.sqrt_one]
  have hza_mem_sphere : (m+(sa:ℂ)*Complex.I*Δ) ∈ sphere (0:ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (hnorm_eq_one_of_normSq _ hza_sphere)
  have hzb_mem_sphere : (m+(sb:ℂ)*Complex.I*Δ) ∈ sphere (0:ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (hnorm_eq_one_of_normSq _ hzb_sphere)
  have hnotBothPos : ¬((∀ z∈τ\{ζ₁,ζ₂},0<L z) ∧ (∀ z∈τ'\{ζ₁,ζ₂},0<L z)) := by
    rintro ⟨h1,h2⟩
    have hall : ∀ z ∈ sphere (0:ℂ) 1, 0 ≤ L z := by
      intro z hz
      by_cases hzeq1 : z = ζ₁
      · rw [hzeq1]; linarith [hLζ1]
      by_cases hzeq2 : z = ζ₂
      · rw [hzeq2]; linarith [hLζ2]
      · have hzmem : z ∈ τ ∪ τ' := by rw [hτunion]; exact hz
        rcases hzmem with h|h
        · exact (h1 z ⟨h, by simp [hzeq1,hzeq2]⟩).le
        · exact (h2 z ⟨h, by simp [hzeq1,hzeq2]⟩).le
    exact absurd (hall _ hzb_mem_sphere) (not_le.2 hLzb)
  have hnotBothNeg : ¬((∀ z∈τ\{ζ₁,ζ₂},L z<0) ∧ (∀ z∈τ'\{ζ₁,ζ₂},L z<0)) := by
    rintro ⟨h1,h2⟩
    have hall : ∀ z ∈ sphere (0:ℂ) 1, L z ≤ 0 := by
      intro z hz
      by_cases hzeq1 : z = ζ₁
      · rw [hzeq1]; linarith [hLζ1]
      by_cases hzeq2 : z = ζ₂
      · rw [hzeq2]; linarith [hLζ2]
      · have hzmem : z ∈ τ ∪ τ' := by rw [hτunion]; exact hz
        rcases hzmem with h|h
        · exact (h1 z ⟨h, by simp [hzeq1,hzeq2]⟩).le
        · exact (h2 z ⟨h, by simp [hzeq1,hzeq2]⟩).le
    exact absurd (hall _ hza_mem_sphere) (not_le.2 hLza)
  have hopp : (∀ z∈τ\{ζ₁,ζ₂},0<L z) ∧ (∀ z∈τ'\{ζ₁,ζ₂},L z<0) ∨
      (∀ z∈τ\{ζ₁,ζ₂},L z<0) ∧ (∀ z∈τ'\{ζ₁,ζ₂},0<L z) := by
    rcases hτsign with h1|h1 <;> rcases hτ'sign with h2|h2
    · exact absurd ⟨h1,h2⟩ hnotBothPos
    · exact Or.inl ⟨h1,h2⟩
    · exact Or.inr ⟨h1,h2⟩
    · exact absurd ⟨h1,h2⟩ hnotBothNeg
  have hτarcPre : IsPreconnected τ := by
    obtain ⟨γ,hAeq,hγc,-,-,-⟩ := hτarcC
    rw [hAeq]; exact isPreconnected_Icc.image γ hγc
  have hτ'arcPre : IsPreconnected τ' := by
    obtain ⟨γ,hAeq,hγc,-,-,-⟩ := hτ'arc
    rw [hAeq]; exact isPreconnected_Icc.image γ hγc
  -- final assembly
  rcases hDkey with hcase | hcase
  · rcases hopp with ⟨hτpos,-⟩ | ⟨-,hτpos⟩
    · refine ⟨τ, hτsub, ⟨ζ₁,hτendpts.1,ζ₂,hτendpts.2,hne⟩, hτarcPre, ?_⟩
      intro ζ hζ
      by_cases hζeq : ζ = ζ₁ ∨ ζ = ζ₂
      · rcases hζeq with rfl|rfl
        · exact hFζ₁
        · exact hFζ₂
      · push_neg at hζeq
        have hζdiff : ζ ∈ τ\{ζ₁,ζ₂} := ⟨hζ, by simp [hζeq.1,hζeq.2]⟩
        have hζsph : ζ ∈ sphere (0:ℂ) 1 := hτsub hζ
        have hζnorm : ‖ζ‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.mp hζsph)
        have hζL : 0 ≤ L ζ := (hτpos ζ hζdiff).le
        have hζcl : ζ ∈ closure D1 := hconvex_combo1 _ ζ hz1mem hζnorm hζL
        exact hclosureToW D1 hD1sub hcase ζ hζcl hζsph
    · refine ⟨τ', hτ'sub, ⟨ζ₁,hτ'endpts.1,ζ₂,hτ'endpts.2,hne⟩, hτ'arcPre, ?_⟩
      intro ζ hζ
      by_cases hζeq : ζ = ζ₁ ∨ ζ = ζ₂
      · rcases hζeq with rfl|rfl
        · exact hFζ₁
        · exact hFζ₂
      · push_neg at hζeq
        have hζdiff : ζ ∈ τ'\{ζ₁,ζ₂} := ⟨hζ, by simp [hζeq.1,hζeq.2]⟩
        have hζsph : ζ ∈ sphere (0:ℂ) 1 := hτ'sub hζ
        have hζnorm : ‖ζ‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.mp hζsph)
        have hζL : 0 ≤ L ζ := (hτpos ζ hζdiff).le
        have hζcl : ζ ∈ closure D1 := hconvex_combo1 _ ζ hz1mem hζnorm hζL
        exact hclosureToW D1 hD1sub hcase ζ hζcl hζsph
  · rcases hopp with ⟨-,hτ'neg⟩ | ⟨hτneg,-⟩
    · refine ⟨τ', hτ'sub, ⟨ζ₁,hτ'endpts.1,ζ₂,hτ'endpts.2,hne⟩, hτ'arcPre, ?_⟩
      intro ζ hζ
      by_cases hζeq : ζ = ζ₁ ∨ ζ = ζ₂
      · rcases hζeq with rfl|rfl
        · exact hFζ₁
        · exact hFζ₂
      · push_neg at hζeq
        have hζdiff : ζ ∈ τ'\{ζ₁,ζ₂} := ⟨hζ, by simp [hζeq.1,hζeq.2]⟩
        have hζsph : ζ ∈ sphere (0:ℂ) 1 := hτ'sub hζ
        have hζnorm : ‖ζ‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.mp hζsph)
        have hζL : L ζ ≤ 0 := (hτ'neg ζ hζdiff).le
        have hζcl : ζ ∈ closure D2 := hconvex_combo2 _ ζ hz2mem hζnorm hζL
        exact hclosureToW D2 hD2sub hcase ζ hζcl hζsph
    · refine ⟨τ, hτsub, ⟨ζ₁,hτendpts.1,ζ₂,hτendpts.2,hne⟩, hτarcPre, ?_⟩
      intro ζ hζ
      by_cases hζeq : ζ = ζ₁ ∨ ζ = ζ₂
      · rcases hζeq with rfl|rfl
        · exact hFζ₁
        · exact hFζ₂
      · push_neg at hζeq
        have hζdiff : ζ ∈ τ\{ζ₁,ζ₂} := ⟨hζ, by simp [hζeq.1,hζeq.2]⟩
        have hζsph : ζ ∈ sphere (0:ℂ) 1 := hτsub hζ
        have hζnorm : ‖ζ‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.mp hζsph)
        have hζL : L ζ ≤ 0 := (hτneg ζ hζdiff).le
        have hζcl : ζ ∈ closure D2 := hconvex_combo2 _ ζ hz2mem hζnorm hζL
        exact hclosureToW D2 hD2sub hcase ζ hζcl hζsph

set_option maxHeartbeats 1000000 in
/-- **C9** (e2) injectivity of the extension on the closed disc (Step 4). -/
theorem injOn_extension_of_isJordanCurve_frontier {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩbdd : Bornology.IsBounded Ω) (hf : IsConformalOnto f unitDisc Ω)
    (hJ : IsJordanCurve (toExt (frontier Ω))) {F : ℂ → ℂ}
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc)
    (hFs : F '' sphere (0 : ℂ) 1 ⊆ frontier Ω) :
    InjOn F (closedBall 0 1) := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩne : (unitDisc : Set ℂ).Nonempty :=
    ⟨0, by rw [unitDisc, mem_ball_zero_iff, norm_zero]; exact one_pos⟩
  have hΩc : IsConnected Ω := by
    have hUDc : IsConnected unitDisc := (convex_ball (0:ℂ) 1).isConnected hΩne
    rw [← hf.2.2]
    exact hUDc.image f hf.1.continuousOn
  have hΩfr_disj : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  intro z1 hz1 z2 hz2 hFeq
  rcases eq_or_ne (‖z1‖) 1 with h1|h1
  · rcases eq_or_ne (‖z2‖) 1 with h2|h2
    · -- both on the sphere
      by_contra hne'
      set w : ℂ := F z1 with hw_def
      have hwfr : w ∈ frontier Ω := hFs ⟨z1, mem_sphere_zero_iff_norm.mpr h1, rfl⟩
      have hFz1w : F z1 = w := hw_def.symm
      have hFz2w : F z2 = w := by rw [hw_def, ← hFeq]
      have hopenSegSub : openSegment ℝ z1 z2 ⊆ unitDisc := by
        rw [openSegment_eq_image' ℝ z1 z2]
        rintro x ⟨t,ht,rfl⟩
        simp only []
        rw [Complex.real_smul]
        exact (mem_unitDisc_chord_iff h1 h2 hne' t).mpr ht
      have hfopenSegΩ : f '' openSegment ℝ z1 z2 ⊆ Ω := hf.2.2 ▸ image_mono hopenSegSub
      have hFeqf : EqOn F f (openSegment ℝ z1 z2) := fun x hx => hFf (hopenSegSub hx)
      have hFopenSegEq : F '' openSegment ℝ z1 z2 = f '' openSegment ℝ z1 z2 :=
        Set.image_congr (fun x hx => hFeqf hx)
      have hFinjSeg : InjOn F (openSegment ℝ z1 z2) := by
        intro x hx y hy hxy
        rw [hFeqf hx, hFeqf hy] at hxy
        exact hf.2.1 (hopenSegSub hx) (hopenSegSub hy) hxy
      have hend : F z1 ∉ F '' openSegment ℝ z1 z2 := by
        rw [hFopenSegEq]
        intro hmem
        exact Set.disjoint_left.1 hΩfr_disj (hfopenSegΩ hmem) hwfr
      have hJseg : IsJordanCurve (toExt (F '' segment ℝ z1 z2)) :=
        isJordanCurve_image_chord h1 h2 hne' hFc hFinjSeg hFeq hend
      have hseg : segment ℝ z1 z2 = openSegment ℝ z1 z2 ∪ {z1,z2} := by
        rw [segment_eq_image' ℝ z1 z2, openSegment_eq_image' ℝ z1 z2]
        ext x
        simp only [mem_image, mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨t, ⟨ht0,ht1⟩, rfl⟩
          rcases eq_or_lt_of_le ht0 with h0|h0
          · exact Or.inr (Or.inl (by rw [← h0]; simp))
          rcases eq_or_lt_of_le ht1 with h1'|h1'
          · exact Or.inr (Or.inr (by rw [h1']; simp))
          · exact Or.inl ⟨t,⟨h0,h1'⟩,rfl⟩
        · rintro (⟨t,⟨ht0,ht1⟩,rfl⟩|rfl|rfl)
          · exact ⟨t,⟨ht0.le,ht1.le⟩,rfl⟩
          · exact ⟨0,⟨le_refl 0,zero_le_one⟩,by simp⟩
          · exact ⟨1,⟨zero_le_one,le_refl 1⟩,by simp⟩
      have hJeq2 : F '' segment ℝ z1 z2 = F '' openSegment ℝ z1 z2 ∪ {w} := by
        rw [hseg, image_union]
        congr 1
        rw [Set.image_insert_eq, Set.image_singleton]
        ext y
        simp only [mem_insert_iff, mem_singleton_iff]
        rw [hw_def]
        constructor
        · rintro (rfl|rfl)
          · rfl
          · exact hFeq.symm
        · rintro rfl
          left; rfl
      have hJfrseg : F '' segment ℝ z1 z2 ∩ frontier Ω = {w} := by
        rw [hJeq2, Set.union_inter_distrib_right]
        have hemp : F '' openSegment ℝ z1 z2 ∩ frontier Ω = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨hy1,hy2⟩
          rw [hFopenSegEq] at hy1
          exact Set.disjoint_left.1 hΩfr_disj (hfopenSegΩ hy1) hy2
        have hsw : ({w}:Set ℂ) ∩ frontier Ω = {w} := by
          rw [Set.inter_eq_left, singleton_subset_iff]; exact hwfr
        rw [hemp, hsw]; simp
      obtain ⟨A, hAsub, hAnt, hAconn, hAconst⟩ :=
        exists_arc_const_of_jordan_curve_meets_frontier_once hΩo hΩc hΩbdd hJ hf hFf hFc hFs
          h1 h2 hne' hFz1w hFz2w hJseg hJfrseg
      have hFdiff : DifferentiableOn ℂ F unitDisc := hf.1.congr hFf
      have hAunion_sub : unitDisc ∪ A ⊆ closedBall (0:ℂ) 1 :=
        union_subset ball_subset_closedBall (hAsub.trans (fun x hx => hx.le))
      have hFconst : EqOn F (fun _ => w) unitDisc :=
        eqOn_const_of_eqOn_const_on_arc hAsub hAnt hAconn hFdiff (hFc.mono hAunion_sub) hAconst
      obtain ⟨p, hpq⟩ := hAnt
      obtain ⟨q, hq, hpqne⟩ := hpq.2
      have hp := hpq.1
      have hpUD : (0:ℂ) ∈ unitDisc := by rw [unitDisc, mem_ball_zero_iff, norm_zero]; exact one_pos
      have hqUD : ((1:ℂ)/2) ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]; norm_num
      have h01ne : (0:ℂ) ≠ (1:ℂ)/2 := by norm_num
      have hF0 : F 0 = w := hFconst hpUD
      have hFq : F ((1:ℂ)/2) = w := hFconst hqUD
      have hf0 : f 0 = w := by rw [← hF0]; exact (hFf hpUD).symm
      have hfq : f ((1:ℂ)/2) = w := by rw [← hFq]; exact (hFf hqUD).symm
      exact h01ne (hf.2.1 hpUD hqUD (hf0.trans hfq.symm))
    · -- z1 on sphere, z2 in the open disc
      exfalso
      have hz2disc : z2 ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]
        rcases mem_closedBall_zero_iff.mp hz2 |>.lt_or_eq with h|h
        · exact h
        · exact absurd h h2
      have hFz1fr : F z1 ∈ frontier Ω := hFs ⟨z1, mem_sphere_zero_iff_norm.mpr h1, rfl⟩
      have hFz2Ω : F z2 ∈ Ω := by
        rw [hFf hz2disc, ← hf.2.2]; exact mem_image_of_mem f hz2disc
      exact Set.disjoint_left.1 hΩfr_disj hFz2Ω (hFeq ▸ hFz1fr)
  · rcases eq_or_ne (‖z2‖) 1 with h2|h2
    · -- z1 in the open disc, z2 on the sphere
      exfalso
      have hz1disc : z1 ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]
        rcases mem_closedBall_zero_iff.mp hz1 |>.lt_or_eq with h|h
        · exact h
        · exact absurd h h1
      have hFz2fr : F z2 ∈ frontier Ω := hFs ⟨z2, mem_sphere_zero_iff_norm.mpr h2, rfl⟩
      have hFz1Ω : F z1 ∈ Ω := by
        rw [hFf hz1disc, ← hf.2.2]; exact mem_image_of_mem f hz1disc
      exact Set.disjoint_left.1 hΩfr_disj hFz1Ω (hFeq ▸ hFz2fr)
    · -- both in the open disc
      have hz1disc : z1 ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]
        rcases mem_closedBall_zero_iff.mp hz1 |>.lt_or_eq with h|h
        · exact h
        · exact absurd h h1
      have hz2disc : z2 ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]
        rcases mem_closedBall_zero_iff.mp hz2 |>.lt_or_eq with h|h
        · exact h
        · exact absurd h h2
      rw [hFf hz1disc, hFf hz2disc] at hFeq
      exact hf.2.1 hz1disc hz2disc hFeq

/-! ### C10 (-94, c10_scratch.lean a8d8d4e422e6d2370ecf46374bfd690e) -/

/-- The closure in `ℂ̄` of a bounded set of `ℂ` does not contain `∞` (local re-proof, to keep
this leaf's imports at `ClusterSets` + `JordanBridge` only; identical to
`Lemmas/Quadrilateral.lean`'s `closure_toExt_of_isBounded`). -/
theorem closure_toExt_of_isBounded' {A : Set ℂ} (hA : Bornology.IsBounded A) :
    closure (toExt A) = toExt (closure A) := by
  unfold toExt
  refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
    (image_closure_subset_closure_image OnePoint.continuous_coe)
  exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hA.isCompact_closure⟩

theorem frontier_toExt_of_isBounded' {A : Set ℂ} (hA : Bornology.IsBounded A) (hAo : IsOpen A) :
    frontier (toExt A) = toExt (frontier A) := by
  have hAo' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hAo
  rw [hAo'.frontier_eq, closure_toExt_of_isBounded' hA, hAo.frontier_eq]
  exact (image_diff OnePoint.coe_injective _ _).symm

/-- **C10** Theorem C2 — statement identical to `caratheodory_jordan` (end of this file). -/
theorem caratheodory_jordan_clean {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hJ : IsJordanCurve (frontier (toExt Ω))) :
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc Ω F := by
  have hfdiff := hf.1
  have hfinj := hf.2.1
  have hfrange := hf.2.2
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔo
  have hΔbdd : Bornology.IsBounded unitDisc := Metric.isBounded_ball
  have hJ' : IsJordanCurve (toExt (frontier Ω)) := by
    rwa [frontier_toExt_of_isBounded' hΩ hΩo] at hJ
  obtain ⟨G, hGcont, hGeq, hGsphere, hGrange⟩ :=
    exists_continuousOn_extension_of_isJordanCurve_frontier hΩ hf hJ'
  have hGinj : InjOn G (closedBall 0 1) :=
    injOn_extension_of_isJordanCurve_frontier hΩ hf hJ' hGcont hGeq hGsphere
  have hΔclosure : closure (toExt unitDisc) = toExt (closedBall (0 : ℂ) 1) := by
    rw [closure_toExt_of_isBounded' hΔbdd]
    congr 1
    rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero]
  have hΩclosure : closure (toExt Ω) = toExt (closure Ω) := closure_toExt_of_isBounded' hΩ
  have hcomp_eq : (OnePoint.map G) ∘ ((↑) : ℂ → ExtPlane) = ((↑) : ℂ → ExtPlane) ∘ G := by
    funext z; simp [OnePoint.map_some]
  refine ⟨OnePoint.map G, ?_, ?_, ?_, ?_⟩
  · intro z hz
    show OnePoint.map G (z : ExtPlane) = ((f z : ℂ) : ExtPlane)
    rw [OnePoint.map_some, hGeq hz]
  · rw [hΔclosure]
    have hcont_comp : ContinuousOn ((OnePoint.map G) ∘ ((↑) : ℂ → ExtPlane)) (closedBall 0 1) := by
      rw [hcomp_eq]; exact OnePoint.continuous_coe.comp_continuousOn hGcont
    exact (OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_image_iff).mpr
      hcont_comp
  · rw [hΔclosure]
    intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨z₁, hz₁, rfl⟩ := hw₁
    obtain ⟨z₂, hz₂, rfl⟩ := hw₂
    rw [OnePoint.map_some, OnePoint.map_some] at heq
    congr 1
    exact hGinj hz₁ hz₂ (OnePoint.coe_injective heq)
  · rw [hΔclosure, hΩclosure]
    unfold toExt
    rw [← image_comp, hcomp_eq, image_comp, hGrange]

/-- **Theorem C2** (Carathéodory, 1913).  If the boundary of a bounded domain `Ω` is a Jordan
curve, a conformal map of the disc onto `Ω` extends to a homeomorphism of the closures.

Moved here from `Lemmas/Caratheodory.lean` with its statement unchanged (user decision 2026-09-25):
the proof is `caratheodory_jordan_clean`, the end of this module's chain `C1`–`C10`, which
`Lemmas/Caratheodory.lean` cannot import. -/
theorem caratheodory_jordan {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hJ : IsJordanCurve (frontier (toExt Ω))) :
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc Ω F := by
  exact caratheodory_jordan_clean hΩ hf hJ

end LiZhongQC
