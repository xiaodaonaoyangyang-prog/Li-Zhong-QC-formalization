import LiZhongQC.Lemmas.SchottkyCoreIntrinsicBoundary
import LiZhongQC.Lemmas.SchottkyIntrinsicBoundaryInvariant
import LiZhongQC.Lemmas.SchottkyCoreBoundaryComponents
import LiZhongQC.Lemmas.SchottkyGenusBridge2
import LiZhongQC.Lemmas.SchottkyBoundaryRankDisc
import LiZhongQC.Lemmas.SchottkyBoundaryRankEdge
import LiZhongQC.Lemmas.SchottkyOrientableDecomp
import LiZhongQC.Lemmas.SchottkyBoundaryRankNonOrientable

open Set Topology
noncomputable section
namespace LiZhongQC


/-- A continuous injection of the circle `ℝ / ℤ` (given by a continuous `ℝ → ℝ` loop, `G 1 = G 0`,
injective on `[0, 1)`) into `ℝ` does not exist. -/
theorem s78nm_no_periodic_injection (G : ℝ → ℝ) (hc : Continuous G)
    (hp : G 1 = G 0) (hi : InjOn G (Ico 0 1)) : False := by
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne : G (1 / 2) ≠ G 0 := fun h => by
    have := hi hh h0 h
    norm_num at this
  -- reduce to `G 0 < G (1/2)` (otherwise replace `G` by `-G`)
  suffices key : ∀ H : ℝ → ℝ, Continuous H → H 1 = H 0 → InjOn H (Ico 0 1) →
      H 0 < H (1 / 2) → False by
    rcases lt_or_gt_of_ne hne with h | h
    · refine key (fun t => - G t) hc.neg (by simp [hp]) ?_ (by simpa using h)
      intro x hx y hy hxy
      exact hi hx hy (neg_injective hxy)
    · exact key G hc hp hi h
  intro H hHc hH1 hHi hlt
  set v : ℝ := (H 0 + H (1 / 2)) / 2 with hv
  have hv0 : H 0 < v := by rw [hv]; linarith
  have hvh : v < H (1 / 2) := by rw [hv]; linarith
  obtain ⟨t1, ht1, hHt1⟩ : ∃ t1 ∈ Icc (0 : ℝ) (1 / 2), H t1 = v :=
    intermediate_value_Icc (by norm_num) hHc.continuousOn ⟨hv0.le, hvh.le⟩
  obtain ⟨t2, ht2, hHt2⟩ : ∃ t2 ∈ Icc (1 / 2 : ℝ) 1, H t2 = v :=
    intermediate_value_Icc' (by norm_num) hHc.continuousOn ⟨by rw [hH1]; exact hv0.le, hvh.le⟩
  have ht1' : t1 < 1 / 2 := by
    rcases ht1.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hHt1; exact absurd hHt1 (ne_of_gt hvh)
  have ht2' : 1 / 2 < t2 := by
    rcases ht2.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hHt2; exact absurd hHt2 (ne_of_gt hvh)
  have ht2'' : t2 < 1 := by
    rcases ht2.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, hH1] at hHt2; exact absurd hHt2 (ne_of_lt hv0)
  have := hHi ⟨ht1.1, by linarith⟩ ⟨by linarith, ht2''⟩ (hHt1.trans hHt2.symm)
  linarith

/-- Core of the loop lemma, with `β` a loop on all of `ℝ`: an embedded loop `β` whose image lies in the loop
`γ` covers all of it. -/
theorem s78nm_loop_range_eq_core {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ β : ℝ → X) (hγc : Continuous γ) (hγ1 : γ 1 = γ 0) (hγi : InjOn γ (Ico 0 1))
    (hβc : Continuous β) (hβ1 : β 1 = β 0) (hβi : InjOn β (Ico 0 1))
    (hsub : range β ⊆ γ '' Icc 0 1) : range β = γ '' Icc 0 1 := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let g : AddCircle (1 : ℝ) → X := AddCircle.liftIco (1 : ℝ) 0 γ
  have hg_apply : ∀ x : ℝ, x ∈ Ico (0 : ℝ) 1 → g (x : AddCircle (1 : ℝ)) = γ x := fun x hx =>
    AddCircle.liftIco_coe_apply (by simpa using hx)
  have hgc : Continuous g :=
    AddCircle.liftIco_continuous (by simpa using hγ1.symm) hγc.continuousOn
  let e : AddCircle (1 : ℝ) → ℝ := fun z =>
    ((AddCircle.equivIco (1 : ℝ) 0 z : Ico (0 : ℝ) (0 + 1)) : ℝ)
  have hmemI : ∀ z, e z ∈ Ico (0 : ℝ) 1 := fun z => by
    have := (AddCircle.equivIco (1 : ℝ) 0 z).2
    simpa [e] using this
  have hval : ∀ z, g z = γ (e z) := fun z => by
    have h := hg_apply (e z) (hmemI z)
    have hc : ((e z : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
    rw [hc] at h
    exact h
  have heinj : Function.Injective e := fun z w hzw =>
    (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext hzw)
  have hginj : Function.Injective g := by
    intro z w hzw
    rw [hval z, hval w] at hzw
    exact heinj (hγi (hmemI z) (hmemI w) hzw)
  have hgemb : Topology.IsClosedEmbedding g := hgc.isClosedEmbedding hginj
  have hrange : range g = γ '' Icc 0 1 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨e z, ⟨(hmemI z).1, (hmemI z).2.le⟩, (hval z).symm⟩
    · rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
      rcases ht1.lt_or_eq with h | h
      · exact ⟨t, hg_apply t ⟨ht0, h⟩⟩
      · refine ⟨((0 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
        rw [hg_apply 0 ⟨le_rfl, one_pos⟩, h, hγ1]
  refine Set.Subset.antisymm (hsub.trans fun _ h => h) ?_
  rw [← hrange]
  by_contra hnot
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Set.not_subset.mp hnot
  -- `z` is a point of the circle not hit by `β`
  have hback : ∀ t, ∃ w, g w = β t := fun t => by
    have := hsub (mem_range_self t)
    rw [← hrange] at this
    exact this
  choose k hk using hback
  have hkc : Continuous k := by
    rw [hgemb.isEmbedding.continuous_iff]
    have : g ∘ k = β := funext hk
    rw [this]; exact hβc
  have hkz : ∀ t, k t ≠ z := fun t h => hz ⟨t, by rw [← hk t, h]⟩
  have hk1 : k 1 = k 0 := hginj (by rw [hk, hk, hβ1])
  have hkinj : InjOn k (Ico 0 1) := fun x hx y hy hxy => hβi hx hy (by rw [← hk x, ← hk y, hxy])
  let ψ : AddCircle (1 : ℝ) → ℝ := fun w => e (w - z)
  have hψ : ∀ w, w ≠ z → ContinuousAt ψ w := by
    intro w hw
    have h1 : ContinuousAt (AddCircle.equivIco (1 : ℝ) 0) (w - z) :=
      AddCircle.continuousAt_equivIco (1 : ℝ) 0 (sub_ne_zero.mpr hw)
    have h2 : ContinuousAt (fun w : AddCircle (1 : ℝ) => w - z) w :=
      continuousAt_id.sub continuousAt_const
    exact continuous_subtype_val.continuousAt.comp
      (h1.comp (f := fun w : AddCircle (1 : ℝ) => w - z) h2)
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact sub_left_injective (heinj hab)
  let G : ℝ → ℝ := fun t => ψ (k t)
  have hGc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hψ (k t) (hkz t)).comp (hkc.continuousAt)
  exact s78nm_no_periodic_injection G hGc
    (by simp only [G, hk1])
    (fun x hx y hy hxy => hkinj hx hy (hψinj hxy))

/-- Loop version: `γ` and `β` are continuous `ℝ → X` loops on `[0,1]` (`γ 1 = γ 0`, `β 1 = β 0`, injective on
`[0,1)`); if `β '' [0,1] ⊆ γ '' [0,1]` then the two loops have the same image. -/
theorem s78nm_loop_range_eq {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ β : ℝ → X) (hγc : Continuous γ) (hγ1 : γ 1 = γ 0) (hγi : InjOn γ (Ico 0 1))
    (hβc : Continuous β) (hβ1 : β 1 = β 0) (hβi : InjOn β (Ico 0 1))
    (hsub : β '' Icc 0 1 ⊆ γ '' Icc 0 1) : β '' Icc 0 1 = γ '' Icc 0 1 := by
  let c : ℝ → ℝ := fun t => max 0 (min t 1)
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcI : ∀ t, c t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcid : ∀ t ∈ Icc (0 : ℝ) 1, c t = t := fun t ht => by
    simp only [c, min_eq_left ht.2, max_eq_right ht.1]
  have hrange : range (fun t => β (c t)) = β '' Icc 0 1 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩; exact ⟨c t, hcI t, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨t, ?_⟩
      show β (c t) = β t
      rw [hcid t ht]
  have h1 : β (c 1) = β (c 0) := by
    rw [hcid 1 ⟨zero_le_one, le_rfl⟩, hcid 0 ⟨le_rfl, zero_le_one⟩]; exact hβ1
  have hinj : InjOn (fun t => β (c t)) (Ico 0 1) := by
    intro x hx y hy hxy
    have hxy' : β (c x) = β (c y) := hxy
    rw [hcid x ⟨hx.1, hx.2.le⟩, hcid y ⟨hy.1, hy.2.le⟩] at hxy'
    exact hβi hx hy hxy'
  have h := s78nm_loop_range_eq_core γ (fun t => β (c t)) hγc hγ1 hγi (hβc.comp hcc) h1 hinj
    (by rw [hrange]; exact hsub)
  rw [← hrange]; exact h


universe u

/-- A parametrization of a circle-shaped space by a `1`-periodic loop on `ℝ`. -/
theorem s78nm_circle_param {Y : Type*} [TopologicalSpace Y] (e : ↥(Metric.sphere (0 : ℂ) 1) ≃ₜ Y) :
    ∃ β : ℝ → Y, Continuous β ∧ (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧ range β = univ := by
  let c : ℝ → ↥(Metric.sphere (0 : ℂ) 1) := fun t =>
    ⟨(Circle.exp (2 * Real.pi * t) : ℂ), (Circle.exp (2 * Real.pi * t)).2⟩
  have hc : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  refine ⟨fun t => e (c t), e.continuous.comp hc, ?_, ?_, ?_⟩
  · intro t
    have : Circle.exp (2 * Real.pi * (t + 1)) = Circle.exp (2 * Real.pi * t) :=
      Circle.exp_eq_exp.2 ⟨1, by push_cast; ring⟩
    simp only [c, this]
  · intro s hs t ht hst
    have h1 : c s = c t := e.injective hst
    have h2 : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
      Subtype.ext (congrArg Subtype.val h1)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
    have hm' : s = t + m := by
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpi
      linarith
    have hm1 : (m : ℝ) < 1 := by linarith [hs.2, ht.1]
    have hm2 : (-1 : ℝ) < m := by linarith [hs.1, ht.2]
    have : m = 0 := by
      have h1 : m < 1 := by exact_mod_cast hm1
      have h2 : -1 < m := by exact_mod_cast hm2
      omega
    rw [hm', this]; simp
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨r, hr⟩ := Circle.exp_surjective ⟨z.1, z.2⟩
    refine ⟨r / (2 * Real.pi), ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : 2 * Real.pi * (r / (2 * Real.pi)) = r := by field_simp
    simp only [c, this]
    congr 1

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
  (F : FiniteTypeStructure S g n m)

/-- The boundary of the core is exactly the set of points without an open Euclidean neighbourhood. -/
theorem s78nm_core_IB_iff (x : s31dt_Core F) :
    x ∈ s31dt_boundary F ↔ ¬ ∃ U : Set (s31dt_Core F), IsOpen U ∧ x ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  obtain ⟨c, -, hbd, -, -⟩ := s31dt_core_intrinsic_boundary F
  letI := c
  have h := s78nm_boundary_eq_intrinsic (S := s31dt_Core F)
  have hx : x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary (s31dt_Core F) ↔
      x ∈ s31dt_boundary F := by rw [hbd]
  rw [← hx, h]
  exact Iff.rfl

/-- Each hole boundary of the core is parametrized by a periodic embedded loop. -/
theorem s78nm_core_hole_loop (i : Fin m) :
    ∃ β : ℝ → s31dt_Core F, Continuous β ∧ (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧
      range β = {x : s31dt_Core F | x.val ∈ frontier (F.D i)} := by
  obtain ⟨e⟩ := s31dt_boundary_circle_homeomorph F i
  obtain ⟨β, hc, hp, hi, hr⟩ := s78nm_circle_param e
  refine ⟨fun t => (β t).val, continuous_subtype_val.comp hc, fun t => by simp only [hp], ?_, ?_⟩
  · intro s hs t ht hst
    exact hi hs ht (Subtype.ext hst)
  · apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact (β t).2
    · intro x hx
      have : (⟨x, hx⟩ : {x : s31dt_Core F | x.val ∈ frontier (F.D i)}) ∈ range β := by
        rw [hr]; trivial
      obtain ⟨t, ht⟩ := this
      exact ⟨t, congrArg Subtype.val ht⟩

/-- **Assembly.**  If a homeomorphic copy `Q` of the core has a finite family of embedded loops `γ j` that
lie in its intrinsic boundary `IBQ`, cover it up to the finite set `V`, and are pairwise distinct, then the
hole boundaries of the core are mapped onto the loops, bijectively. -/
theorem s78nm_assembly {Q : Type*} [TopologicalSpace Q] (φ : s31dt_Core F ≃ₜ Q)
    {q : ℕ} (γ : Fin q → ℝ → Q) (V : Set Q) (hV : V.Finite)
    (hγc : ∀ j, Continuous (γ j)) (hγ1 : ∀ j, γ j 1 = γ j 0) (hγi : ∀ j, InjOn (γ j) (Ico 0 1))
    (hdist : ∀ j j', j ≠ j' → γ j '' Icc 0 1 ≠ γ j' '' Icc 0 1)
    (IBQ : Set Q) (hIB : ∀ z, z ∈ IBQ ↔ ¬ ∃ U : Set Q, IsOpen U ∧ z ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (hH : ∀ j, γ j '' Icc 0 1 ⊆ IBQ) (hdec : IBQ ⊆ (⋃ j, γ j '' Icc 0 1) ∪ V) :
    ∃ σ : Fin m ≃ Fin q, ∀ j : Fin m,
      φ '' {x : s31dt_Core F | x.val ∈ frontier (F.D j)} = γ (σ j) '' Icc 0 1 := by
  haveI : T2Space Q := φ.symm.isEmbedding.t2Space
  let C : Fin m → Set (s31dt_Core F) := fun i => {x | x.val ∈ frontier (F.D i)}
  have hCB : ∀ i, C i ⊆ s31dt_boundary F := fun i x hx => ⟨i, hx⟩
  have hbd : ∀ x : s31dt_Core F, x ∈ s31dt_boundary F ↔ φ x ∈ IBQ := fun x => by
    rw [s78nm_core_IB_iff F x, hIB]
    exact not_congr (s78nm_euclid_nbhd_iff φ x)
  obtain ⟨hclopen, -, hdisj, hcover⟩ := s31dt_boundary_component_decomposition F
  -- every loop lies in one hole boundary
  have hτ : ∀ j : Fin q, ∃ i : Fin m, γ j '' Icc 0 1 ⊆ φ '' C i := by
    intro j
    let s : Set ↥(s31dt_boundary F) := Subtype.val ⁻¹' (φ.symm '' (γ j '' Icc 0 1))
    have hsub : φ.symm '' (γ j '' Icc 0 1) ⊆ s31dt_boundary F := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hbd, φ.apply_symm_apply]
      exact hH j hz
    have himg : Subtype.val '' s = φ.symm '' (γ j '' Icc 0 1) := by
      rw [Subtype.image_preimage_coe]
      exact Set.inter_eq_right.2 hsub |>.symm ▸ rfl
    have hpre : IsPreconnected (φ.symm '' (γ j '' Icc 0 1)) :=
      (isPreconnected_Icc.image _ (hγc j).continuousOn).image _ φ.symm.continuous.continuousOn
    have hpre' : IsPreconnected s := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
      exact hpre
    have hne : s.Nonempty := by
      have h0 : γ j 0 ∈ γ j '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      exact ⟨⟨φ.symm (γ j 0), hsub ⟨_, h0, rfl⟩⟩, ⟨_, h0, rfl⟩⟩
    obtain ⟨x0, hx0⟩ := hne
    have hx0c : x0 ∈ ⋃ i, {x : ↥(s31dt_boundary F) | x.val.val ∈ frontier (F.D i)} := by
      rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx0c
    refine ⟨i, ?_⟩
    have hcl := hclopen i
    have hss : s ⊆ {x : ↥(s31dt_boundary F) | x.val.val ∈ frontier (F.D i)} := by
      refine hpre'.subset_left_of_subset_union hcl.isOpen hcl.compl.isOpen disjoint_compl_right ?_
        ⟨x0, hx0, hi⟩
      intro x _
      by_cases hx : x ∈ {x : ↥(s31dt_boundary F) | x.val.val ∈ frontier (F.D i)}
      · exact Or.inl hx
      · exact Or.inr hx
    intro z hz
    have hzs : (⟨φ.symm z, hsub ⟨z, hz, rfl⟩⟩ : ↥(s31dt_boundary F)) ∈ s := ⟨z, hz, rfl⟩
    exact ⟨φ.symm z, hss hzs, φ.apply_symm_apply z⟩
  choose τ hτ using hτ
  -- parametrizations of the hole boundaries
  have hparam : ∀ i : Fin m, ∃ β : ℝ → Q, Continuous β ∧ β 1 = β 0 ∧ InjOn β (Ico 0 1) ∧
      β '' Icc 0 1 = φ '' C i := by
    intro i
    obtain ⟨β, hc, hp, hi, hr⟩ := s78nm_core_hole_loop F i
    refine ⟨fun t => φ (β t), φ.continuous.comp hc, ?_, ?_, ?_⟩
    · show φ (β 1) = φ (β 0)
      rw [show (1 : ℝ) = 0 + 1 by norm_num, hp]
    · intro s hs t ht hst
      exact hi hs ht (φ.injective hst)
    · apply Set.Subset.antisymm
      · rintro _ ⟨t, -, rfl⟩
        refine ⟨β t, ?_, rfl⟩
        have hmem : β t ∈ range β := ⟨t, rfl⟩
        rw [hr] at hmem
        exact hmem
      · rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ range β := by rw [hr]; exact hx
        obtain ⟨t, rfl⟩ := hx'
        -- reduce `t` modulo `1`
        refine ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
        show φ (β (Int.fract t)) = φ (β t)
        congr 1
        have hperiodic : Function.Periodic β 1 := hp
        have h3 := hperiodic.sub_int_mul_eq (x := t) ⌊t⌋
        rw [mul_one] at h3
        exact h3
  choose B hBc hB1 hBi hBr using hparam
  -- the loops are onto the hole boundaries
  have hrange : ∀ j : Fin q, φ '' C (τ j) = γ j '' Icc 0 1 := by
    intro j
    have h := s78nm_loop_range_eq (B (τ j)) (γ j) (hBc _) (hB1 _) (hBi _) (hγc j) (hγ1 j) (hγi j)
      (by rw [hBr]; exact hτ j)
    rw [← hBr, h]
  have hinj : Function.Injective τ := by
    intro j j' h
    by_contra hne
    apply hdist j j' hne
    rw [← hrange j, ← hrange j', h]
  have hsurj : Function.Surjective τ := by
    intro i
    by_contra hnot
    push_neg at hnot
    have hsubV : φ '' C i ⊆ V := by
      rintro _ ⟨x, hx, rfl⟩
      have hmem : φ x ∈ IBQ := (hbd x).1 (hCB i hx)
      rcases hdec hmem with h | h
      · exfalso
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
        rw [← hrange j] at hj
        obtain ⟨y, hy, hyx⟩ := hj
        have hxy : y = x := φ.injective hyx
        subst hxy
        -- `y ∈ C (τ j)` and `y ∈ C i`, with `τ j ≠ i`
        have hij : τ j ≠ i := hnot j
        have := hdisj hij
        have hyb : y ∈ s31dt_boundary F := hCB i hx
        exact (Set.disjoint_left.1 this) (show (⟨y, hyb⟩ : ↥(s31dt_boundary F)) ∈
          {x : ↥(s31dt_boundary F) | x.val.val ∈ frontier (F.D (τ j))} from hy)
          (show (⟨y, hyb⟩ : ↥(s31dt_boundary F)) ∈
            {x : ↥(s31dt_boundary F) | x.val.val ∈ frontier (F.D i)} from hx)
      · exact h
    obtain ⟨β, hc, hp, hi, hr⟩ := s78nm_core_hole_loop F i
    have hinf : (C i).Infinite := by
      rw [show C i = range β from hr.symm]
      have : (β '' Ico 0 1).Infinite := (Set.Ico_infinite zero_lt_one).image hi
      exact this.mono (Set.image_subset_range _ _)
    exact (hinf.image φ.injective.injOn) (hV.subset hsubV)
  have hbij : Function.Bijective τ := ⟨hinj, hsurj⟩
  refine ⟨(Equiv.ofBijective τ hbij).symm, fun j => ?_⟩
  have e : τ ((Equiv.ofBijective τ hbij).symm j) = j := (Equiv.ofBijective τ hbij).apply_symm_apply j
  have h2 := hrange ((Equiv.ofBijective τ hbij).symm j)
  rw [e] at h2
  exact h2


open Complex LeanEval.Topology.ClassificationOfSurfaces

/-- The set of points without an open Euclidean neighbourhood is closed. -/
theorem s78nm_IB_closed {Q : Type*} [TopologicalSpace Q] :
    IsClosed {z : Q | ¬ ∃ U : Set Q, IsOpen U ∧ z ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  simp only [mem_compl_iff, mem_setOf_eq, not_not] at hz
  obtain ⟨U, hU, hzU, hne⟩ := hz
  refine ⟨U, ?_, hU, hzU⟩
  intro y hy
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  exact ⟨U, hU, hy, hne⟩

/-- The glued-parameter set of the polygon models is compact. -/
theorem s78nm_T_compact (hl : ℝ) (q : ℕ) (N : ℝ) (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N))) : IsCompact T := by
  rw [hT]
  exact isCompact_Icc.union (isCompact_iUnion fun j => isCompact_Icc.union isCompact_Icc)

/-- A free-arc parameter is not congruent mod `1` to any glued parameter. -/
theorem s78nm_gap_ne (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ) (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N)
    (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (i : Fin q) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∀ t ∈ T, ∀ m : ℤ, (x - (3 * ((i : ℕ) : ℝ) + 2)) / N ≠ t + m := by
  intro t ht m hm
  rw [div_eq_iff hN.ne'] at hm
  have hmN : (m : ℝ) * N = (x - (3 * ((i : ℕ) : ℝ) + 2)) - t * N := by nlinarith [hm]
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hi1 : ((i : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast i.2
  have hq3 : 3 * (q : ℝ) ≤ N := by rw [hNdef]; linarith
  have hx0 := hx.1
  have hx1 := hx.2
  rw [hT] at ht
  rcases ht with h | h
  · have h1 : 0 ≤ t * N := mul_nonneg h.1 hN.le
    have h2 : t * N ≤ hl := (le_div_iff₀ hN).1 h.2
    exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hj1 : ((j : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast j.2
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with hji | hji | hji
    · have hji' : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hji
      rcases hj with hj | hj
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
    · have hjie : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) := by exact_mod_cast hji
      rcases hj with hj | hj
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
    · have hji' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hji
      rcases hj with hj | hj
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN hj
        exact s78dg_noint N _ hN (by nlinarith) (by nlinarith) (by nlinarith) m hmN

/-- The free-arc parameter does not lie on the circle image of the glued parameters. -/
theorem s78nm_arc_not_mem (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ) (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N)
    (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (i : Fin q) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ClosedUnitDisc.bdyPtOfReal ((x - (3 * ((i : ℕ) : ℝ) + 2)) / N) ∉
      ClosedUnitDisc.bdyPtOfReal '' T := by
  rintro ⟨t, ht, hts⟩
  obtain ⟨m, hm⟩ := (s78dg_bdy_eq_iff t _).1 hts
  exact s78nm_gap_ne hl hl0 q N hNdef hN T hT i x hx t ht (-m) (by rw [hm]; push_cast; ring)

/-- A point of the free arc has no Euclidean neighbourhood in a quotient of the disc by a relation whose
related points lie on the glued parameters. -/
theorem s78nm_free_arc (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ)
    (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N) (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (hR : ∀ x y, R x y → x ∈ ClosedUnitDisc.bdyPtOfReal '' T ∧ y ∈ ClosedUnitDisc.bdyPtOfReal '' T)
    (i : Fin q) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (U : Set (Quot R)) (hU : IsOpen U)
    (hq : Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((x - (3 * ((i : ℕ) : ℝ) + 2)) / N)) ∈ U)
    (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False :=
  s78dg_free_param R T (s78nm_T_compact hl q N T hT) hR _
    (fun t ht m => s78nm_gap_ne hl hl0 q N hNdef hN T hT i x hx t ht m) U hU hq h

/-- Points on the free arc form singleton classes. -/
theorem s78nm_singleton_class (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (F : Set ClosedUnitDisc)
    (hR : ∀ x y, R x y → x ∈ F ∧ y ∈ F) {a b : ClosedUnitDisc} (ha : a ∉ F)
    (h : Quot.mk R a = Quot.mk R b) : b = a := by
  have := Quot.eqvGen_exact h
  rcases s78dg_eqv_in_set R F hR this with h1 | h1
  · exact h1.symm
  · exact absurd h1.1 ha

/-- The `h`-arc of `Quot R` is an embedded loop. -/
theorem s78nm_hole_loop (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ)
    (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N) (hN1 : 1 ≤ N) (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (hR : ∀ x y, R x y → x ∈ ClosedUnitDisc.bdyPtOfReal '' T ∧ y ∈ ClosedUnitDisc.bdyPtOfReal '' T)
    (hc : ∀ i : Fin q, R (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 1) / N))
      (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 2) / N)))
    (i : Fin q) :
    (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R)) 0 =
      (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R)) 1 ∧
    InjOn (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R))
      (Ico 0 1) := by
  set c : ℝ := 3 * ((i : ℕ) : ℝ) + 2 with hcdef
  set F : Set ClosedUnitDisc := ClosedUnitDisc.bdyPtOfReal '' T with hF
  constructor
  · show Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((0 - c) / N)) = Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((1 - c) / N))
    have e0 : (0 - c) / N = -(3 * ((i : ℕ) : ℝ) + 2) / N := by rw [hcdef]; ring
    have e1 : (1 - c) / N = -(3 * ((i : ℕ) : ℝ) + 1) / N := by rw [hcdef]; ring
    rw [e0, e1]
    exact (Quot.sound (hc i)).symm
  · -- two points of `[0,1)` with the same class coincide
    have key : ∀ x y : ℝ, x ∈ Ioo (0 : ℝ) 1 → y ∈ Ico (0 : ℝ) 1 →
        Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((y - c) / N)) =
          Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((x - c) / N)) → y = x := by
      intro x y hx hy hxy
      have hnot : ClosedUnitDisc.bdyPtOfReal ((x - c) / N) ∉ F :=
        s78nm_arc_not_mem hl hl0 q N hNdef hN T hT i x hx
      have heq := s78nm_singleton_class R F hR hnot hxy.symm
      obtain ⟨m, hm⟩ := (s78dg_bdy_eq_iff _ _).1 heq
      rw [← sub_eq_iff_eq_add'] at hm
      have hm2 : y - x = m * N := by
        have : (y - c) / N - (x - c) / N = m := hm
        field_simp at this
        linarith
      have hlt : (m : ℝ) < 1 := by
        by_contra hge
        have hge' : (1 : ℝ) ≤ m := not_lt.1 hge
        nlinarith [hy.2, hx.1, mul_nonneg (sub_nonneg.2 hge') hN.le]
      have hgt : (-1 : ℝ) < m := by
        by_contra hge
        have hge' : (m : ℝ) ≤ -1 := not_lt.1 hge
        nlinarith [hy.1, hx.2, mul_nonneg (sub_nonneg.2 hge') hN.le]
      have h1 : m < 1 := by exact_mod_cast hlt
      have h2 : -1 < m := by exact_mod_cast hgt
      have hm0 : m = 0 := by omega
      rw [hm0, Int.cast_zero, zero_mul] at hm2
      linarith
    intro x hx y hy hxy
    rcases hx.1.eq_or_lt with h0 | hxpos
    · rcases hy.1.eq_or_lt with h0' | hypos
      · rw [← h0, ← h0']
      · -- `x = 0`, `y ∈ (0,1)`
        exact key y x ⟨hypos, hy.2⟩ hx hxy
    · exact (key x y ⟨hxpos, hx.2⟩ hy hxy.symm).symm

/-- The `h`-arc of `Quot R` lies in the set of points without a Euclidean neighbourhood. -/
theorem s78nm_loop_subset_IB (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ)
    (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N) (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (hR : ∀ x y, R x y → x ∈ ClosedUnitDisc.bdyPtOfReal '' T ∧ y ∈ ClosedUnitDisc.bdyPtOfReal '' T)
    (i : Fin q) :
    (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R)) ''
        Icc 0 1 ⊆
      {z : Quot R | ¬ ∃ U : Set (Quot R), IsOpen U ∧ z ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} := by
  set γ : ℝ → Quot R := fun t => Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) with hγ
  have hcont : Continuous γ :=
    continuous_quot_mk.comp (s78dg_bdy_continuous.comp ((continuous_id.sub continuous_const).div_const N))
  have hIo : γ '' Ioo 0 1 ⊆ {z : Quot R | ¬ ∃ U : Set (Quot R), IsOpen U ∧ z ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} := by
    rintro _ ⟨x, hx, rfl⟩ ⟨U, hU, hxU, ⟨h⟩⟩
    exact s78nm_free_arc R hl hl0 q N hNdef hN T hT hR i x hx U hU hxU h
  have h2 : closure (γ '' Ioo 0 1) ⊆ {z : Quot R | ¬ ∃ U : Set (Quot R), IsOpen U ∧ z ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))} := closure_minimal hIo s78nm_IB_closed
  calc γ '' Icc 0 1 = γ '' closure (Ioo 0 1) := by rw [closure_Ioo zero_ne_one]
    _ ⊆ closure (γ '' Ioo 0 1) := image_closure_subset_closure_image hcont
    _ ⊆ _ := h2

/-- Different holes have different arcs. -/
theorem s78nm_loop_distinct (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (hl : ℝ) (hl0 : 0 ≤ hl) (q : ℕ)
    (N : ℝ) (hNdef : N = hl + 3 * q) (hN : 0 < N) (T : Set ℝ)
    (hT : T = Icc 0 (hl / N) ∪ ⋃ j : Fin q,
      (Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
        Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N)))
    (hR : ∀ x y, R x y → x ∈ ClosedUnitDisc.bdyPtOfReal '' T ∧ y ∈ ClosedUnitDisc.bdyPtOfReal '' T)
    (i i' : Fin q) (hii : i ≠ i') :
    (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R)) ''
        Icc 0 1 ≠
      (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i' : ℕ) : ℝ) + 2)) / N)) : Quot R)) ''
        Icc 0 1 := by
  intro heq
  have hx : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hnot := s78nm_arc_not_mem hl hl0 q N hNdef hN T hT i (1 / 2) hx
  have hmem : (Quot.mk R (ClosedUnitDisc.bdyPtOfReal (((1 / 2 : ℝ) - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R) ∈
      (fun t : ℝ => (Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / N)) : Quot R)) ''
        Icc 0 1 := ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  rw [heq] at hmem
  obtain ⟨t', ht', hteq⟩ := hmem
  have h1 := s78nm_singleton_class R _ hR hnot hteq.symm
  obtain ⟨m, hm⟩ := (s78dg_bdy_eq_iff _ _).1 h1
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hi1 : ((i : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast i.2
  have hj0 : (0 : ℝ) ≤ ((i' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hj1 : ((i' : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast i'.2
  have hq3 : 3 * (q : ℝ) ≤ N := by rw [hNdef]; linarith
  have hm2 : t' - 1 / 2 + 3 * (((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)) = m * N := by
    have h' : (t' - (3 * ((i' : ℕ) : ℝ) + 2)) / N = ((1 / 2 : ℝ) - (3 * ((i : ℕ) : ℝ) + 2)) / N + m := hm
    rw [div_eq_iff hN.ne'] at h'
    field_simp at h'
    nlinarith [h']
  have hne : ((i : ℕ)) ≠ (i' : ℕ) := fun h => hii (Fin.ext h)
  rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    nlinarith [ht'.1, ht'.2, mul_nonneg (by linarith : (0 : ℝ) ≤ -1 - m) hN.le]
  · subst hm0
    simp only [Int.cast_zero, zero_mul] at hm2
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((i : ℕ) : ℝ) + 1 ≤ ((i' : ℕ) : ℝ) := by exact_mod_cast h
      nlinarith [ht'.1, ht'.2]
    · have : ((i' : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
      nlinarith [ht'.1, ht'.2]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith [ht'.1, ht'.2, mul_nonneg (by linarith : (0 : ℝ) ≤ m - 1) hN.le]

/-- Related points of the orientable model lie on the glued parameters. -/
theorem s78nm_orientable_hR (p q : ℕ) (hN : 0 < 4 * (p : ℝ) + 3 * q) :
    ∀ x y, OrientableRel p q x y →
      x ∈ ClosedUnitDisc.bdyPtOfReal '' (Icc 0 (4 * (p : ℝ) / (4 * p + 3 * q)) ∪ ⋃ j : Fin q,
        (Icc (-(3 * (j : ℝ) + 1) / (4 * p + 3 * q)) (-(3 * (j : ℝ)) / (4 * p + 3 * q)) ∪
          Icc (-(3 * (j : ℝ) + 3) / (4 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (4 * p + 3 * q)))) ∧
      y ∈ ClosedUnitDisc.bdyPtOfReal '' (Icc 0 (4 * (p : ℝ) / (4 * p + 3 * q)) ∪ ⋃ j : Fin q,
        (Icc (-(3 * (j : ℝ) + 1) / (4 * p + 3 * q)) (-(3 * (j : ℝ)) / (4 * p + 3 * q)) ∪
          Icc (-(3 * (j : ℝ) + 3) / (4 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (4 * p + 3 * q)))) := by
  set N : ℝ := 4 * p + 3 * q with hNdef
  intro x y hxy
  have hmem : ∀ {a b u : ℝ}, a ≤ u → u ≤ b → u / N ∈ Set.Icc (a / N) (b / N) :=
    fun h1 h2 => ⟨div_le_div_of_nonneg_right h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
  have hmem0 : ∀ {b u : ℝ}, 0 ≤ u → u ≤ b → u / N ∈ Set.Icc (0 : ℝ) (b / N) :=
    fun h1 h2 => ⟨div_nonneg h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
  cases hxy with
  | a x i =>
    have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    have hx0 := x.2.1
    have hx1 := x.2.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
      ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
  | b x i =>
    have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    have hx0 := x.2.1
    have hx1 := x.2.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
      ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
  | c x i =>
    have hx0 := x.2.1
    have hx1 := x.2.2
    exact ⟨⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl (hmem (by linarith) (by linarith))⟩), rfl⟩,
      ⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr (hmem (by linarith) (by linarith))⟩), rfl⟩⟩

/-- Related points of the non-orientable model lie on the glued parameters. -/
theorem s78nm_nonorientable_hR (p q : ℕ) (hN : 0 < 2 * (p : ℝ) + 3 * q) :
    ∀ x y, NonOrientableRel p q x y →
      x ∈ ClosedUnitDisc.bdyPtOfReal '' (Icc 0 (2 * (p : ℝ) / (2 * p + 3 * q)) ∪ ⋃ j : Fin q,
        (Icc (-(3 * (j : ℝ) + 1) / (2 * p + 3 * q)) (-(3 * (j : ℝ)) / (2 * p + 3 * q)) ∪
          Icc (-(3 * (j : ℝ) + 3) / (2 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (2 * p + 3 * q)))) ∧
      y ∈ ClosedUnitDisc.bdyPtOfReal '' (Icc 0 (2 * (p : ℝ) / (2 * p + 3 * q)) ∪ ⋃ j : Fin q,
        (Icc (-(3 * (j : ℝ) + 1) / (2 * p + 3 * q)) (-(3 * (j : ℝ)) / (2 * p + 3 * q)) ∪
          Icc (-(3 * (j : ℝ) + 3) / (2 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (2 * p + 3 * q)))) := by
  set N : ℝ := 2 * p + 3 * q with hNdef
  intro x y hxy
  have hmem : ∀ {a b u : ℝ}, a ≤ u → u ≤ b → u / N ∈ Set.Icc (a / N) (b / N) :=
    fun h1 h2 => ⟨div_le_div_of_nonneg_right h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
  have hmem0 : ∀ {b u : ℝ}, 0 ≤ u → u ≤ b → u / N ∈ Set.Icc (0 : ℝ) (b / N) :=
    fun h1 h2 => ⟨div_nonneg h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
  cases hxy with
  | a x i =>
    have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    have hx0 := x.2.1
    have hx1 := x.2.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
      ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
  | c x i =>
    have hx0 := x.2.1
    have hx1 := x.2.2
    exact ⟨⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl (hmem (by linarith) (by linarith))⟩), rfl⟩,
      ⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr (hmem (by linarith) (by linarith))⟩), rfl⟩⟩

/-- The `c`-relation at the endpoint `x = 1` glues the two ends of the free arc (orientable model). -/
theorem s78nm_orientable_hc (p q : ℕ) (i : Fin q) :
    OrientableRel p q (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 1) / (4 * p + 3 * q)))
      (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 2) / (4 * p + 3 * q))) := by
  have h := OrientableRel.c (p := p) (n := q) ⟨1, ⟨zero_le_one, le_rfl⟩⟩ i
  have e1 : (-(3 * ((i : ℕ) : ℝ) + ((⟨1, ⟨zero_le_one, le_rfl⟩⟩ : Icc (0 : ℝ) 1) : ℝ)) / (4 * (p : ℝ) + 3 * q)) =
      -(3 * ((i : ℕ) : ℝ) + 1) / (4 * p + 3 * q) := by simp
  have e2 : (-(3 * ((i : ℕ) : ℝ) + 3 - ((⟨1, ⟨zero_le_one, le_rfl⟩⟩ : Icc (0 : ℝ) 1) : ℝ)) / (4 * (p : ℝ) + 3 * q)) =
      -(3 * ((i : ℕ) : ℝ) + 2) / (4 * p + 3 * q) := by
    simp only []
    ring
  rw [e1, e2] at h
  exact h

/-- The `c`-relation at the endpoint `x = 1` (non-orientable model). -/
theorem s78nm_nonorientable_hc (p q : ℕ) (i : Fin q) :
    NonOrientableRel p q (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 1) / (2 * p + 3 * q)))
      (ClosedUnitDisc.bdyPtOfReal (-(3 * ((i : ℕ) : ℝ) + 2) / (2 * p + 3 * q))) := by
  have h := NonOrientableRel.c (p := p) (n := q) ⟨1, ⟨zero_le_one, le_rfl⟩⟩ i
  have e1 : (-(3 * ((i : ℕ) : ℝ) + ((⟨1, ⟨zero_le_one, le_rfl⟩⟩ : Icc (0 : ℝ) 1) : ℝ)) / (2 * (p : ℝ) + 3 * q)) =
      -(3 * ((i : ℕ) : ℝ) + 1) / (2 * p + 3 * q) := by simp
  have e2 : (-(3 * ((i : ℕ) : ℝ) + 3 - ((⟨1, ⟨zero_le_one, le_rfl⟩⟩ : Icc (0 : ℝ) 1) : ℝ)) / (2 * (p : ℝ) + 3 * q)) =
      -(3 * ((i : ℕ) : ℝ) + 2) / (2 * p + 3 * q) := by
    simp only []
    ring
  rw [e1, e2] at h
  exact h

/-- Hole loops of the orientable model (exported for the assembly of the classification bridge). -/
theorem s78rb_hole_loop_orientable (p q : ℕ) (hpq : 1 ≤ p ∨ 1 ≤ q) (i : Fin q) :
    let f : ℝ → Quot (OrientableRel p q) := fun t =>
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / (4 * p + 3 * q)))
    f 0 = f 1 ∧ InjOn f (Ico 0 1) := by
  have hN : 0 < 4 * (p : ℝ) + 3 * q := by
    rcases hpq with h | h
    · have : (1 : ℝ) ≤ p := by exact_mod_cast h
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      linarith
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
  have hN1 : 1 ≤ 4 * (p : ℝ) + 3 * q := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Fin.pos i
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  exact s78nm_hole_loop (OrientableRel p q) (4 * (p : ℝ)) (by positivity) q (4 * p + 3 * q) rfl hN hN1 _ rfl
    (s78nm_orientable_hR p q hN) (s78nm_orientable_hc p q) i


section FinalOrientable
variable [ConnectedSpace S]

theorem s78rb_core_model_boundary_orientable (hm : m ≠ 0) {p q : ℕ} (hpq : 1 ≤ p ∨ 1 ≤ q)
    (φ : s31dt_Core F ≃ₜ Quot (OrientableRel p q)) :
    ∃ σ : Fin m ≃ Fin q, ∀ j : Fin m,
      φ '' {x : s31dt_Core F | x.val ∈ frontier (F.D j)} =
        (fun t : ℝ => Quot.mk _ (ClosedUnitDisc.bdyPtOfReal
          ((t - (3 * ((σ j : ℕ) : ℝ) + 2)) / (4 * p + 3 * q)))) '' Icc 0 1 := by
  have hN : 0 < 4 * (p : ℝ) + 3 * q := by
    rcases hpq with h | h
    · have : (1 : ℝ) ≤ p := by exact_mod_cast h
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      linarith
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
  have hN1 : ∀ i : Fin q, 1 ≤ 4 * (p : ℝ) + 3 * q := fun i => by
    have : (1 : ℝ) ≤ q := by exact_mod_cast Fin.pos i
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  obtain ⟨V, hV, hdec⟩ := s78nm_orientable_decomp p q hpq
  let T : Set ℝ := Icc 0 (4 * (p : ℝ) / (4 * p + 3 * q)) ∪ ⋃ j : Fin q,
    (Icc (-(3 * (j : ℝ) + 1) / (4 * p + 3 * q)) (-(3 * (j : ℝ)) / (4 * p + 3 * q)) ∪
      Icc (-(3 * (j : ℝ) + 3) / (4 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (4 * p + 3 * q)))
  have hR := s78nm_orientable_hR p q hN
  have hc := s78nm_orientable_hc p q
  refine s78nm_assembly F φ
    (fun j t => (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal
      ((t - (3 * ((j : ℕ) : ℝ) + 2)) / (4 * p + 3 * q))) : Quot (OrientableRel p q)))
    V hV ?_ ?_ ?_ ?_ _ (fun z => Iff.rfl) ?_ ?_
  · intro j
    exact continuous_quot_mk.comp (s78dg_bdy_continuous.comp
      ((continuous_id.sub continuous_const).div_const _))
  · intro j
    exact (s78nm_hole_loop (OrientableRel p q) (4 * (p : ℝ)) (by positivity) q _ rfl hN (hN1 j) T rfl
      hR hc j).1.symm
  · intro j
    exact (s78nm_hole_loop (OrientableRel p q) (4 * (p : ℝ)) (by positivity) q _ rfl hN (hN1 j) T rfl
      hR hc j).2
  · intro j j' hjj
    exact s78nm_loop_distinct (OrientableRel p q) (4 * (p : ℝ)) (by positivity) q _ rfl hN T rfl hR j j' hjj
  · intro j
    exact s78nm_loop_subset_IB (OrientableRel p q) (4 * (p : ℝ)) (by positivity) q _ rfl hN T rfl hR j
  · intro z hz
    exact hdec z hz

end FinalOrientable


section FinalNonOrientable
variable [ConnectedSpace S]

theorem s78rb_hole_loop_nonorientable (p q : ℕ) (hp : 1 ≤ p) (i : Fin q) :
    let f : ℝ → Quot (NonOrientableRel p q) := fun t =>
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / (2 * p + 3 * q)))
    f 0 = f 1 ∧ InjOn f (Ico 0 1) := by
  have hN : 0 < 2 * (p : ℝ) + 3 * q := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  have hN1 : 1 ≤ 2 * (p : ℝ) + 3 * q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast Fin.pos i
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  exact s78nm_hole_loop (NonOrientableRel p q) (2 * (p : ℝ)) (by positivity) q _ rfl hN hN1 _ rfl
    (s78nm_nonorientable_hR p q hN) (s78nm_nonorientable_hc p q) i

theorem s78rb_core_model_boundary_nonorientable (hm : m ≠ 0) {p q : ℕ} (hp : 1 ≤ p)
    (φ : s31dt_Core F ≃ₜ Quot (NonOrientableRel p q)) :
    ∃ σ : Fin m ≃ Fin q, ∀ j : Fin m,
      φ '' {x : s31dt_Core F | x.val ∈ frontier (F.D j)} =
        (fun t : ℝ => Quot.mk _ (ClosedUnitDisc.bdyPtOfReal
          ((t - (3 * ((σ j : ℕ) : ℝ) + 2)) / (2 * p + 3 * q)))) '' Icc 0 1 := by
  have hN : 0 < 2 * (p : ℝ) + 3 * q := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  obtain ⟨V, hV, hdec⟩ := s78rb_nonorientable_decomp p q hp
  let T : Set ℝ := Icc 0 (2 * (p : ℝ) / (2 * p + 3 * q)) ∪ ⋃ j : Fin q,
    (Icc (-(3 * (j : ℝ) + 1) / (2 * p + 3 * q)) (-(3 * (j : ℝ)) / (2 * p + 3 * q)) ∪
      Icc (-(3 * (j : ℝ) + 3) / (2 * p + 3 * q)) (-(3 * (j : ℝ) + 2) / (2 * p + 3 * q)))
  have hR := s78nm_nonorientable_hR p q hN
  refine s78nm_assembly F φ
    (fun j t => (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal
      ((t - (3 * ((j : ℕ) : ℝ) + 2)) / (2 * p + 3 * q))) : Quot (NonOrientableRel p q)))
    V hV ?_ ?_ ?_ ?_ _ (fun z => Iff.rfl) ?_ ?_
  · intro j
    exact continuous_quot_mk.comp (s78dg_bdy_continuous.comp
      ((continuous_id.sub continuous_const).div_const _))
  · intro j
    exact (s78rb_hole_loop_nonorientable p q hp j).1.symm
  · intro j
    exact (s78rb_hole_loop_nonorientable p q hp j).2
  · intro j j' hjj
    exact s78nm_loop_distinct (NonOrientableRel p q) (2 * (p : ℝ)) (by positivity) q _ rfl hN T rfl hR j j' hjj
  · intro j
    exact s78nm_loop_subset_IB (NonOrientableRel p q) (2 * (p : ℝ)) (by positivity) q _ rfl hN T rfl hR j
  · intro z hz
    exact hdec z hz

end FinalNonOrientable


end LiZhongQC
