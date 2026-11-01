import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Normed.Module.Connected
import LiZhongQC.Lemmas.SchottkyHalfFundamentalEquivalence

open Set Metric Topology unitInterval

universe u

namespace LiZhongQC

/-- **Inward radial retraction of the thickened core.**  In disjoint disc charts `v j`, the complement
`Ω` of the small closed discs `v j '' closedBall 0 (ρ j)` deformation retracts, radially inside each chart,
onto the points outside the open unit discs. -/
theorem s78dg_inner_homotopy {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (ρ : Fin m → ℝ) (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j < 1)
    (Ω : Set X) (hΩ : Ω = (⋃ j, v j '' closedBall (0 : ℂ) (ρ j))ᶜ) :
    ∃ G : C(I × ↥Ω, ↥Ω),
      (∀ x, (G (0, x)).val = x.val) ∧
      (∀ x, (G (1, x)).val ∉ ⋃ j, v j '' ball (0 : ℂ) 1) ∧
      (∀ t x, x.val ∉ (⋃ j, v j '' ball (0 : ℂ) 1) → (G (t, x)).val = x.val) := by
  classical
  have hball : ∀ j, ball (0 : ℂ) (R j) ⊆ (v j).source :=
    fun j => ball_subset_closedBall.trans (hs j)
  let O : Fin m → Set X := fun j => v j '' ball (0 : ℂ) (R j)
  have hOopen : ∀ j, IsOpen (O j) :=
    fun j => (v j).isOpen_image_of_subset_source isOpen_ball (hball j)
  have hOdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j) := fun i j hij =>
    (hdisj hij).mono (image_mono ball_subset_closedBall) (image_mono ball_subset_closedBall)
  have hz : ∀ j (x : X), x ∈ O j →
      (v j).symm x ∈ ball (0 : ℂ) (R j) ∧ v j ((v j).symm x) = x := by
    intro j x hx
    obtain ⟨w, hw, hwx⟩ := hx
    have h1 : (v j).symm x = w := by rw [← hwx]; exact (v j).left_inv (hball j hw)
    exact ⟨h1 ▸ hw, by rw [h1]; exact hwx⟩
  let sc : ℝ → ℂ → ℝ := fun t z => 1 - t + t / min 1 ‖z‖
  let GG : ℝ → X → X := fun t x =>
    if h : ∃ j, x ∈ O j then
      v h.choose ((sc t ((v h.choose).symm x) : ℝ) • (v h.choose).symm x) else x
  have hGG : ∀ t j x, x ∈ O j →
      GG t x = v j ((sc t ((v j).symm x) : ℝ) • (v j).symm x) := by
    intro t j x hx
    have h : ∃ j, x ∈ O j := ⟨j, hx⟩
    have hc : h.choose = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hOdisj _ _ hne) h.choose_spec hx
    simp only [GG, dif_pos h, hc]
  have hGGn : ∀ t x, (∀ j, x ∉ O j) → GG t x = x := by
    intro t x hx
    have h : ¬ ∃ j, x ∈ O j := by
      rintro ⟨j, hj⟩
      exact hx j hj
    simp only [GG, dif_neg h]
  have hsc1 : ∀ t z, 1 ≤ ‖z‖ → sc t z = 1 := by
    intro t z hz1
    simp only [sc, min_eq_left hz1]
    ring
  have hsc0 : ∀ z, sc 0 z = 1 := by
    intro z
    simp [sc]
  have hscn : ∀ t z, 0 ≤ t → t ≤ 1 → 0 ≤ sc t z := by
    intro t z ht0 ht1
    have : 0 ≤ t / min 1 ‖z‖ := div_nonneg ht0 (le_min zero_le_one (norm_nonneg _))
    simp only [sc]
    linarith
  have hscl : ∀ t z, 0 ≤ t → t ≤ 1 → ‖z‖ < 1 → 0 < ‖z‖ →
      ‖(sc t z) • z‖ = (1 - t) * ‖z‖ + t := by
    intro t z ht0 ht1 hz1 hz0
    have hm : min 1 ‖z‖ = ‖z‖ := min_eq_right hz1.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hscn t z ht0 ht1)]
    simp only [sc, hm]
    field_simp
  -- norm control of the radial path
  have hwn : ∀ j t z, 0 ≤ t → t ≤ 1 → ρ j < ‖z‖ → ‖z‖ < R j →
      ρ j < ‖(sc t z) • z‖ ∧ ‖(sc t z) • z‖ < R j := by
    intro j t z ht0 ht1 hzρ hzR
    by_cases hz1 : 1 ≤ ‖z‖
    · rw [hsc1 t z hz1, one_smul]
      exact ⟨hzρ, hzR⟩
    · push Not at hz1
      rw [hscl t z ht0 ht1 hz1 ((hρ0 j).trans hzρ)]
      have := hR j
      constructor <;> nlinarith
  have hwn1 : ∀ z, ‖z‖ ≠ 0 → 1 ≤ ‖(sc 1 z) • z‖ := by
    intro z hz0
    by_cases hz1 : 1 ≤ ‖z‖
    · rw [hsc1 1 z hz1, one_smul]
      exact hz1
    · push Not at hz1
      rw [hscl 1 z zero_le_one le_rfl hz1 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0))]
      linarith
  have hΩm : ∀ x, x ∈ Ω ↔ ∀ i, x ∉ v i '' closedBall (0 : ℂ) (ρ i) := by
    intro x
    rw [hΩ]
    simp
  have hρz : ∀ j x, x ∈ Ω → x ∈ O j → ρ j < ‖(v j).symm x‖ := by
    intro j x hxΩ hxO
    by_contra hle
    push Not at hle
    exact (hΩm x).1 hxΩ j ⟨(v j).symm x, mem_closedBall_zero_iff.mpr hle, (hz j x hxO).2⟩
  have hinj : ∀ j w w', w ∈ ball (0 : ℂ) (R j) → w' ∈ ball (0 : ℂ) (R j) →
      v j w = v j w' → w = w' := fun j w w' hw hw' h => (v j).injOn (hball j hw) (hball j hw') h
  have hρR : ∀ j, closedBall (0 : ℂ) (ρ j) ⊆ ball (0 : ℂ) (R j) := by
    intro j w hw
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hw).trans_lt ((hρ1 j).trans (hR j))
  have h1R : ∀ j, ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) (R j) := fun j => ball_subset_ball (hR j).le
  have hDO : ∀ i, v i '' closedBall (0 : ℂ) (ρ i) ⊆ O i := fun i => image_mono (hρR i)
  have hBO : ∀ i, v i '' ball (0 : ℂ) 1 ⊆ O i := fun i => image_mono (h1R i)
  have hland : ∀ t, 0 ≤ t → t ≤ 1 → ∀ x ∈ Ω, GG t x ∈ Ω := by
    intro t ht0 ht1 x hxΩ
    by_cases h : ∃ j, x ∈ O j
    · obtain ⟨j, hj⟩ := h
      rw [hGG t j x hj]
      have hzb := (hz j x hj).1
      have hzρ := hρz j x hxΩ hj
      have hzR : ‖(v j).symm x‖ < R j := mem_ball_zero_iff.mp hzb
      obtain ⟨hw1, hw2⟩ := hwn j t _ ht0 ht1 hzρ hzR
      have hwb : (sc t ((v j).symm x)) • (v j).symm x ∈ ball (0 : ℂ) (R j) :=
        mem_ball_zero_iff.mpr hw2
      rw [hΩm]
      intro i hi
      by_cases hij : i = j
      · subst hij
        obtain ⟨w', hw', he⟩ := hi
        have := hinj i w' _ (hρR i hw') hwb he
        rw [this] at hw'
        exact absurd (mem_closedBall_zero_iff.mp hw') (not_le.mpr hw1)
      · exact Set.disjoint_left.mp (hOdisj i j hij) (hDO i hi) ⟨_, hwb, rfl⟩
    · rw [hGGn t x (fun j hj => h ⟨j, hj⟩)]
      exact hxΩ
  have hbd : ∀ x ∈ Ω, GG 1 x ∉ ⋃ j, v j '' ball (0 : ℂ) 1 := by
    intro x hxΩ
    by_cases h : ∃ j, x ∈ O j
    · obtain ⟨j, hj⟩ := h
      rw [hGG 1 j x hj]
      have hzb := (hz j x hj).1
      have hzρ := hρz j x hxΩ hj
      have hzR : ‖(v j).symm x‖ < R j := mem_ball_zero_iff.mp hzb
      obtain ⟨hw1, hw2⟩ := hwn j 1 _ zero_le_one le_rfl hzρ hzR
      have hwb : (sc 1 ((v j).symm x)) • (v j).symm x ∈ ball (0 : ℂ) (R j) :=
        mem_ball_zero_iff.mpr hw2
      have hge := hwn1 ((v j).symm x) ((hρ0 j).trans hzρ).ne'
      intro hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      by_cases hij : i = j
      · subst hij
        obtain ⟨w', hw', he⟩ := hi
        have := hinj i w' _ (h1R i hw') hwb he
        rw [this] at hw'
        exact absurd (mem_ball_zero_iff.mp hw') (not_lt.mpr hge)
      · exact Set.disjoint_left.mp (hOdisj i j hij) (hBO i hi) ⟨_, hwb, rfl⟩
    · rw [hGGn 1 x (fun j hj => h ⟨j, hj⟩)]
      intro hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      exact h ⟨i, hBO i hi⟩
  have hfix : ∀ t x, x ∉ (⋃ j, v j '' ball (0 : ℂ) 1) → GG t x = x := by
    intro t x hx
    by_cases h : ∃ j, x ∈ O j
    · obtain ⟨j, hj⟩ := h
      rw [hGG t j x hj]
      have hz1 : 1 ≤ ‖(v j).symm x‖ := by
        by_contra hlt
        push Not at hlt
        exact hx (mem_iUnion.mpr ⟨j, (v j).symm x, mem_ball_zero_iff.mpr hlt, (hz j x hj).2⟩)
      rw [hsc1 t _ hz1, one_smul]
      exact (hz j x hj).2
    · exact hGGn t x (fun j hj => h ⟨j, hj⟩)
  have hzero : ∀ x, GG 0 x = x := by
    intro x
    by_cases h : ∃ j, x ∈ O j
    · obtain ⟨j, hj⟩ := h
      rw [hGG 0 j x hj, hsc0, one_smul]
      exact (hz j x hj).2
    · exact hGGn 0 x (fun j hj => h ⟨j, hj⟩)
  -- closed small and unit discs
  have hD1closed : IsClosed (⋃ j, v j '' closedBall (0 : ℂ) 1) := by
    refine isClosed_iUnion_of_finite (fun j => ?_)
    exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
      ((v j).continuousOn.mono (closedBall_subset_closedBall (hR j).le |>.trans (hs j)))).isClosed
  have hD1O : ∀ j, v j '' closedBall (0 : ℂ) 1 ⊆ O j :=
    fun j => image_mono (closedBall_subset_ball (hR j))
  -- continuity
  have hcont : Continuous (fun p : I × ↥Ω => GG (p.1 : ℝ) p.2.val) := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases h : ∃ j, p.2.val ∈ O j
    · obtain ⟨j, hj⟩ := h
      have hmem : p.2.val ∈ (v j).target := by
        obtain ⟨w, hw, hwx⟩ := hj
        rw [← hwx]
        exact (v j).map_source (hball j hw)
      have hzρ := hρz j p.2.val p.2.property hj
      have hzR : ‖(v j).symm p.2.val‖ < R j := mem_ball_zero_iff.mp (hz j _ hj).1
      have hq : p.2.val ∈ O j := hj
      let zf : I × ↥Ω → ℂ := fun q => (v j).symm q.2.val
      have hzc : ContinuousAt zf p :=
        ContinuousAt.comp_of_eq ((v j).continuousAt_symm hmem)
          (continuous_subtype_val.comp continuous_snd).continuousAt rfl
      have hmin : ContinuousAt (fun q : I × ↥Ω => min 1 ‖zf q‖) p :=
        continuousAt_const.min hzc.norm
      have hmin0 : min 1 ‖zf p‖ ≠ 0 :=
        (lt_min zero_lt_one ((hρ0 j).trans hzρ)).ne'
      have hscc : ContinuousAt (fun q : I × ↥Ω => sc (q.1 : ℝ) (zf q)) p := by
        have h1 : ContinuousAt (fun q : I × ↥Ω => (q.1 : ℝ)) p :=
          (continuous_subtype_val.comp continuous_fst).continuousAt
        exact (continuousAt_const.sub h1).add (h1.div hmin hmin0)
      have hwc : ContinuousAt (fun q : I × ↥Ω => (sc (q.1 : ℝ) (zf q)) • zf q) p :=
        hscc.smul hzc
      have hws : (sc (p.1 : ℝ) (zf p)) • zf p ∈ (v j).source := by
        obtain ⟨-, hw2⟩ := hwn j _ _ p.1.property.1 p.1.property.2 hzρ hzR
        exact hball j (mem_ball_zero_iff.mpr hw2)
      have hFc : ContinuousAt (fun q : I × ↥Ω => v j ((sc (q.1 : ℝ) (zf q)) • zf q)) p :=
        ContinuousAt.comp_of_eq ((v j).continuousAt hws) hwc rfl
      have hopen : IsOpen {q : I × ↥Ω | q.2.val ∈ O j} :=
        (hOopen j).preimage (continuous_subtype_val.comp continuous_snd)
      refine hFc.congr ?_
      filter_upwards [hopen.mem_nhds hq] with q hqq
      exact (hGG q.1 j q.2.val hqq).symm
    · have hnot : ∀ j, p.2.val ∉ O j := fun j hj => h ⟨j, hj⟩
      have hopen : IsOpen {q : I × ↥Ω | q.2.val ∈ (⋃ j, v j '' closedBall (0 : ℂ) 1)ᶜ} :=
        hD1closed.isOpen_compl.preimage (continuous_subtype_val.comp continuous_snd)
      have hq : p.2.val ∈ (⋃ j, v j '' closedBall (0 : ℂ) 1)ᶜ := by
        intro hmem
        obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
        exact hnot j (hD1O j hj)
      have hc : ContinuousAt (fun q : I × ↥Ω => q.2.val) p :=
        (continuous_subtype_val.comp continuous_snd).continuousAt
      refine hc.congr ?_
      filter_upwards [hopen.mem_nhds hq] with q hqq
      apply (hfix q.1 q.2.val _).symm
      intro hmem
      obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
      exact hqq (mem_iUnion.mpr ⟨j, image_mono ball_subset_closedBall hj⟩)
  refine ⟨⟨fun p => ⟨GG (p.1 : ℝ) p.2.val, hland _ p.1.property.1 p.1.property.2 _ p.2.property⟩,
    hcont.subtype_mk _⟩, ?_, ?_, ?_⟩
  · intro x
    exact hzero x.val
  · intro x
    exact hbd x.val x.property
  · intro t x hx
    exact hfix t x.val hx

/-- The core is a deformation retract of its inward thickening: `π₁` isomorphism and
path-connectedness transfer. -/
theorem s78dg_inner_pi1 {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (ρ : Fin m → ℝ) (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j < 1)
    (Ω C : Set X) (hΩ : Ω = (⋃ j, v j '' closedBall (0 : ℂ) (ρ j))ᶜ)
    (hC : C = (⋃ j, v j '' ball (0 : ℂ) 1)ᶜ) :
    ∃ e : C(↥C, ↥Ω), (∀ x, (e x).val = x.val) ∧
      (∀ x, Function.Bijective (FundamentalGroup.map e x)) ∧
      (PathConnectedSpace ↥C → PathConnectedSpace ↥Ω) := by
  obtain ⟨G, hG0, hG1, hGf⟩ := s78dg_inner_homotopy v R hR hs hdisj ρ hρ0 hρ1 Ω hΩ
  have hCΩ : C ⊆ Ω := by
    intro x hx
    rw [hΩ]
    intro hmem
    obtain ⟨j, w, hw, hwx⟩ := mem_iUnion.mp hmem
    rw [hC] at hx
    apply hx
    exact mem_iUnion.mpr ⟨j, w, mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hw).trans_lt (hρ1 j)), hwx⟩
  have hr1 : ∀ x : ↥Ω, (G (1, x)).val ∈ C := fun x => by rw [hC]; exact hG1 x
  let e : C(↥C, ↥Ω) := ⟨fun x => ⟨x.val, hCΩ x.property⟩,
    Continuous.subtype_mk continuous_subtype_val (fun x => hCΩ x.property)⟩
  let r : C(↥Ω, ↥C) := ⟨fun x => ⟨(G (1, x)).val, hr1 x⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp
      (G.continuous.comp (continuous_const.prodMk continuous_id))) hr1⟩
  have hre : ∀ x, r (e x) = x := by
    intro x
    apply Subtype.ext
    change (G (1, e x)).val = x.val
    exact hGf 1 (e x) ((Set.ext_iff.1 hC x.1).1 x.2)
  let H : ContinuousMap.Homotopy (ContinuousMap.id ↥Ω) (e.comp r) :=
    { toFun := fun p => G (p.1, p.2)
      continuous_toFun := G.continuous
      map_zero_left := fun x => Subtype.ext (hG0 x)
      map_one_left := fun x => rfl }
  refine ⟨e, fun x => rfl, fun x => ?_, ?_⟩
  · obtain ⟨E, hE1, hE2⟩ := s78dg_retraction_fundamental_equiv e r hre H x
    have : FundamentalGroup.map e x = E.toMonoidHom :=
      MonoidHom.ext fun γ => (hE1 γ).symm
    rw [this]
    exact E.bijective
  · intro hCpc
    have hj : ∀ a : ↥Ω, Joined a (e (r a)) := by
      intro a
      refine ⟨⟨⟨fun t => G (t, a), G.continuous.comp (continuous_id.prodMk continuous_const)⟩,
        Subtype.ext (hG0 a), Subtype.ext rfl⟩⟩
    refine ⟨?_, fun a b => ?_⟩
    · obtain ⟨c⟩ := (inferInstance : Nonempty ↥C)
      exact ⟨e c⟩
    · exact (hj a).trans (((PathConnectedSpace.joined (r a) (r b)).map e.continuous).trans (hj b).symm)

end LiZhongQC
