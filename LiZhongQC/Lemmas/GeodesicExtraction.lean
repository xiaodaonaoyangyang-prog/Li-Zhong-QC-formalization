import LiZhongQC.Lemmas.GeodesicContacts
import LiZhongQC.Lemmas.FluxRoute

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-! Topological extraction for the actual non-pausing geodesic API.
No simplicity, finite intersection set, or bigon premise is used in the
extraction theorems. The later smooth-chain realization is a separate step. -/

/-- Local injectivity on the compact parameter interval gives a uniform
positive separation between distinct visits to the same spatial point. -/
theorem s25gb_return_separation {f : ℝ → ℂ}
    (hloc : ∀ x ∈ Icc (0 : ℝ) 1, ∃ r > 0,
      InjOn f (Icc (0 : ℝ) 1 ∩ Ioo (x - r) (x + r))) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      s < t → t - s < δ → f s ≠ f t := by
  classical
  choose r hr hi using hloc
  let U : Icc (0 : ℝ) 1 → Set ℝ := fun x => Ioo (x - r x x.2) (x + r x x.2)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ x, U x := by
    intro x hx
    refine mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact ⟨by dsimp [U]; linarith [hr x hx], by dsimp [U]; linarith [hr x hx]⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun x => isOpen_Ioo : ∀ x, IsOpen (U x)) hcover
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst hsmall he
  obtain ⟨x, hx⟩ := hball s hs
  have hsU : s ∈ U x := hx (mem_ball_self hδ)
  have htU : t ∈ U x := hx (by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hst)]
    exact hsmall)
  exact (ne_of_lt hst) (hi x x.2 ⟨hs, hsU⟩ ⟨ht, htU⟩ he)

/-- Every noninjective locally injective continuous curve contains a simple
closed subarc. Minimize the length of a return interval in a compact set of
return pairs separated from the diagonal. -/
theorem s25gb_simple_loop {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hloc : ∀ x ∈ Icc (0 : ℝ) 1, ∃ r > 0,
      InjOn f (Icc (0 : ℝ) 1 ∩ Ioo (x - r) (x + r)))
    (hni : ¬ InjOn f (Icc (0 : ℝ) 1)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ f a = f b ∧ InjOn f (Ico a b) := by
  obtain ⟨δ, hδ, hsep⟩ := s25gb_return_separation hloc
  have hex : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, s < t ∧ f s = f t := by
    simp only [InjOn, not_forall] at hni
    obtain ⟨s, hs, t, ht, heq, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨s, hs, t, ht, h, heq⟩
    · exact ⟨t, ht, s, hs, h, heq.symm⟩
  let P : Set (ℝ × ℝ) :=
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      (fun p : ℝ × ℝ => f p.1 - f p.2) ⁻¹' {0}) ∩ {p | p.1 + δ ≤ p.2}
  have hPc : IsCompact P := by
    refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_
      (inter_subset_left.trans inter_subset_left)
    refine IsClosed.inter ?_ (isClosed_le (continuous_fst.add continuous_const) continuous_snd)
    exact ((hf.comp continuous_fst.continuousOn (fun p hp => hp.1)).sub
      (hf.comp continuous_snd.continuousOn (fun p hp => hp.2))).preimage_isClosed_of_isClosed
        (isClosed_Icc.prod isClosed_Icc) isClosed_singleton
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      s < t → f s = f t → (s, t) ∈ P := by
    intro s hs t ht hst heq
    refine ⟨⟨⟨hs, ht⟩, by simpa using sub_eq_zero.2 heq⟩, ?_⟩
    by_contra hn
    exact hsep s hs t ht hst (by dsimp at hn ⊢; linarith) heq
  obtain ⟨s, hs, t, ht, hst, he⟩ := hex
  obtain ⟨p, hp, hmin⟩ := hPc.exists_isMinOn ⟨(s, t), hmem s hs t ht hst he⟩
    (continuous_snd.sub continuous_fst).continuousOn
  rcases p with ⟨a, b⟩
  obtain ⟨⟨⟨ha, hb⟩, heq⟩, habδ⟩ := hp
  have hab : a < b := by dsimp at habδ; linarith
  have hmin' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      s < t → f s = f t → b - a ≤ t - s := by
    intro s hs t ht hst he
    exact hmin (hmem s hs t ht hst he)
  refine ⟨a, b, ha.1, hab, hb.2, sub_eq_zero.1 heq, ?_⟩
  intro s hs t ht he
  by_contra hne
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hs.1, hs.2.le.trans hb.2⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1, ht.2.le.trans hb.2⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmin' s hsI t htI h he
    linarith [hs.1, ht.2]
  · have := hmin' t htI s hsI h he.symm
    linarith [ht.1, hs.2]

/-- The simple-loop extractor applies to the actual geodesic and non-pausing
hypotheses of theorem 25.3, including repeats at zeros. -/
theorem s25gb_geodesic_simple_loop {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    (hni : ¬ InjOn γ.toFun (Icc (0 : ℝ) 1)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      γ.toFun a = γ.toFun b ∧ InjOn γ.toFun (Ico a b) := by
  obtain ⟨K, hK⟩ := hγ.1
  exact s25gb_simple_loop hK.continuousOn
    (fun x hx => s25fc_locally_injective hφ hne hγ hp hx) hni

/-- A compact target trace has a genuine excursion interval around any point
outside it. Only continuity is used; contacts may be infinite or accumulate. -/
theorem s25gb_excursion {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (h0 : f 0 ∈ g '' Icc (0 : ℝ) 1) (h1 : f 1 ∈ g '' Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxoff : f x ∉ g '' Icc (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧
      f a ∈ g '' Icc (0 : ℝ) 1 ∧ f b ∈ g '' Icc (0 : ℝ) 1 ∧
      ∀ t ∈ Ioo a b, f t ∉ g '' Icc (0 : ℝ) 1 := by
  let K : Set ℝ := Icc (0 : ℝ) 1 ∩ f ⁻¹' (g '' Icc (0 : ℝ) 1)
  have hK : IsClosed K := hf.preimage_isClosed_of_isClosed isClosed_Icc
    (isCompact_Icc.image_of_continuousOn hg).isClosed
  have hA : IsCompact (Icc (0 : ℝ) x ∩ K) := isCompact_Icc.inter_right hK
  have hB : IsCompact (Icc x (1 : ℝ) ∩ K) := isCompact_Icc.inter_right hK
  have hA0 : (0 : ℝ) ∈ Icc (0 : ℝ) x ∩ K :=
    ⟨⟨le_rfl, hx.1⟩, ⟨⟨le_rfl, zero_le_one⟩, h0⟩⟩
  have hB1 : (1 : ℝ) ∈ Icc x (1 : ℝ) ∩ K :=
    ⟨⟨hx.2, le_rfl⟩, ⟨⟨zero_le_one, le_rfl⟩, h1⟩⟩
  obtain ⟨a, ha, hmax⟩ := hA.exists_isMaxOn ⟨0, hA0⟩ continuous_id.continuousOn
  obtain ⟨b, hb, hmin⟩ := hB.exists_isMinOn ⟨1, hB1⟩ continuous_id.continuousOn
  have hax : a < x := by
    by_contra hn
    have he : a = x := le_antisymm ha.1.2 (le_of_not_gt hn)
    exact hxoff (he ▸ ha.2.2)
  have hxb : x < b := by
    by_contra hn
    have he : b = x := le_antisymm (le_of_not_gt hn) hb.1.1
    exact hxoff (he ▸ hb.2.2)
  refine ⟨a, b, ha.1.1, hax, hxb, hb.1.2, ha.2.2, hb.2.2, ?_⟩
  intro t ht hhit
  have htI : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.1.1.trans ht.1.le, ht.2.le.trans hb.1.2⟩
  rcases le_total t x with htx | hxt
  · have hta : t ≤ a := hmax ⟨⟨htI.1, htx⟩, ⟨htI, hhit⟩⟩
    exact (not_le_of_gt ht.1) hta
  · have hbt : b ≤ t := hmin ⟨⟨hxt, htI.2⟩, ⟨htI, hhit⟩⟩
    exact (not_le_of_gt ht.2) hbt

/-- Different embedded arcs with common endpoints contain an extracted bigon:
the interior of the first subarc avoids the entire second curve. The order of
the two second-curve parameters is deliberately unrestricted. -/
theorem s25gb_bigon_parameters {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hfi : InjOn f (Icc (0 : ℝ) 1))
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hoff : ∃ x ∈ Icc (0 : ℝ) 1, f x ∉ g '' Icc (0 : ℝ) 1) :
    ∃ a b u v : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      u ∈ Icc (0 : ℝ) 1 ∧ v ∈ Icc (0 : ℝ) 1 ∧ u ≠ v ∧
      f a = g u ∧ f b = g v ∧
      ∀ t ∈ Ioo a b, ∀ q ∈ Icc (0 : ℝ) 1, f t ≠ g q := by
  obtain ⟨x, hx, hxoff⟩ := hoff
  have hf0 : f 0 ∈ g '' Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, h0.symm⟩
  have hf1 : f 1 ∈ g '' Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, h1.symm⟩
  obtain ⟨a, b, ha, hax, hxb, hb, hga, hgb, hoff⟩ :=
    s25gb_excursion hf hg hf0 hf1 hx hxoff
  obtain ⟨u, hu, heu⟩ := hga
  obtain ⟨v, hv, hev⟩ := hgb
  have hab : a < b := hax.trans hxb
  have huv : u ≠ v := by
    intro he
    have heab : f a = f b := heu.symm.trans ((congrArg g he).trans hev)
    exact (ne_of_lt hab) (hfi ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ heab)
  refine ⟨a, b, u, v, ha, hab, hb, hu, hv, huv, heu.symm, hev.symm, ?_⟩
  intro t ht q hq he
  exact hoff t ht ⟨q, hq, he.symm⟩

/-- Normalize either orientation of an interval to `[0,1]`. -/
theorem s25gb_affine_mem {u v t : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    u + (v - u) * t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · nlinarith [mul_nonneg hu.1 (sub_nonneg.2 ht.2), mul_nonneg hv.1 ht.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 hu.2) (sub_nonneg.2 ht.2),
      mul_nonneg (sub_nonneg.2 hv.2) ht.1]

/-- Strictly interior affine parameters remain interior when endpoints are ordered. -/
theorem s25gb_affine_interior {a b t : ℝ} (hab : a < b) (ht : t ∈ Ioo (0 : ℝ) 1) :
    a + (b - a) * t ∈ Ioo a b := by
  constructor
  · nlinarith [mul_pos (sub_pos.2 hab) ht.1]
  · nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 ht.2)]

/-- Injectivity survives an affine restriction, including the reversed one. -/
theorem s25gb_affine_injective {f : ℝ → ℂ} (hf : InjOn f (Icc (0 : ℝ) 1))
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≠ v) :
    InjOn (fun t => f (u + (v - u) * t)) (Icc (0 : ℝ) 1) := by
  intro s hs t ht he
  have he' := hf (s25gb_affine_mem hu hv hs) (s25gb_affine_mem hu hv ht) he
  have hvu : v - u ≠ 0 := sub_ne_zero.2 huv.symm
  exact mul_left_cancel₀ hvu (add_left_cancel he')

/-- An extracted parameter bigon becomes two embedded normalized arcs. This
constructs the required simplicity data; it is not an input assumption. -/
theorem s25gb_normalized_bigon {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hoff : ∃ x ∈ Icc (0 : ℝ) 1, f x ∉ g '' Icc (0 : ℝ) 1) :
    ∃ (a b u v : ℝ) (F G : ℝ → ℂ),
      0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ u ∈ Icc (0 : ℝ) 1 ∧ v ∈ Icc (0 : ℝ) 1 ∧ u ≠ v ∧
      F = (fun t => f (a + (b - a) * t)) ∧
      G = (fun t => g (v + (u - v) * t)) ∧
      ContinuousOn F (Icc (0 : ℝ) 1) ∧ ContinuousOn G (Icc (0 : ℝ) 1) ∧
      InjOn F (Icc (0 : ℝ) 1) ∧ InjOn G (Icc (0 : ℝ) 1) ∧
      F 0 = G 1 ∧ F 1 = G 0 ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, F s ≠ G t := by
  obtain ⟨a, b, u, v, ha, hab, hb, hu, hv, huv, he0, he1, hdisj⟩ :=
    s25gb_bigon_parameters hf hg hfi h0 h1 hoff
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
  refine ⟨a, b, u, v, (fun t => f (a + (b - a) * t)),
    (fun t => g (v + (u - v) * t)), ha, hab, hb, hu, hv, huv, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun t ht => s25gb_affine_mem haI hbI ht)
  · exact hg.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun t ht => s25gb_affine_mem hv hu ht)
  · exact s25gb_affine_injective hfi haI hbI (ne_of_lt hab)
  · exact s25gb_affine_injective hgi hv hu huv.symm
  · simpa using he0
  · simpa using he1
  · intro s hs t ht
    exact hdisj _ (s25gb_affine_interior hab hs) _ (s25gb_affine_mem hv hu ht)

/-- Once simple loops have been excluded geometrically, local injectivity
already proved for geodesics yields global injectivity. This is an explicit
consumer interface, not a proof that such geometric exclusion is available. -/
theorem s25gb_injective_of_no_simple_loop {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    (hexclude : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      γ.toFun a = γ.toFun b → InjOn γ.toFun (Ico a b) → False) :
    InjOn γ.toFun (Icc (0 : ℝ) 1) := by
  by_contra hn
  obtain ⟨a, b, ha, hab, hb, he, hi⟩ := s25gb_geodesic_simple_loop hφ hne hγ hp hn
  exact hexclude a b ha hab hb he hi

/-- Every hypothetical pair contradicting theorem 25.3 gives one of the
actual topological obstructions: a simple loop in either original curve,
or an extracted bigon after orienting which curve has an excursion.
Global simplicity and existence of a bigon are conclusions, not premises. -/
theorem s25gb_actual_obstruction {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (h₁ : IsPhiGeodesic φ unitDisc γ₁)
    (h₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1)
    (htrace : γ₁.closedTrace ≠ γ₂.closedTrace) :
    (∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      γ₁.toFun a = γ₁.toFun b ∧ InjOn γ₁.toFun (Ico a b)) ∨
    (∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      γ₂.toFun a = γ₂.toFun b ∧ InjOn γ₂.toFun (Ico a b)) ∨
    ∃ f g : ℝ → ℂ,
      ((f = γ₁.toFun ∧ g = γ₂.toFun) ∨ (f = γ₂.toFun ∧ g = γ₁.toFun)) ∧
      InjOn f (Icc (0 : ℝ) 1) ∧ InjOn g (Icc (0 : ℝ) 1) ∧
      ∃ a b u v : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        u ∈ Icc (0 : ℝ) 1 ∧ v ∈ Icc (0 : ℝ) 1 ∧ u ≠ v ∧
        f a = g u ∧ f b = g v ∧
        ∀ t ∈ Ioo a b, ∀ q ∈ Icc (0 : ℝ) 1, f t ≠ g q := by
  classical
  by_cases hi₁ : InjOn γ₁.toFun (Icc (0 : ℝ) 1)
  · by_cases hi₂ : InjOn γ₂.toFun (Icc (0 : ℝ) 1)
    · right
      right
      obtain ⟨K₁, hK₁⟩ := h₁.1
      obtain ⟨K₂, hK₂⟩ := h₂.1
      change γ₁.toFun '' Icc (0 : ℝ) 1 ≠ γ₂.toFun '' Icc (0 : ℝ) 1 at htrace
      by_cases hsub : γ₁.toFun '' Icc (0 : ℝ) 1 ⊆ γ₂.toFun '' Icc (0 : ℝ) 1
      · have hnsub : ¬ γ₂.toFun '' Icc (0 : ℝ) 1 ⊆ γ₁.toFun '' Icc (0 : ℝ) 1 := by
          intro hsub'
          exact htrace (Subset.antisymm hsub hsub')
        have hoff : ∃ x ∈ Icc (0 : ℝ) 1, γ₂.toFun x ∉ γ₁.toFun '' Icc (0 : ℝ) 1 := by
          obtain ⟨z, hz, hno⟩ := Set.not_subset.1 hnsub
          obtain ⟨x, hx, he⟩ := hz
          exact ⟨x, hx, by rwa [he]⟩
        exact ⟨γ₂.toFun, γ₁.toFun, Or.inr ⟨rfl, rfl⟩, hi₂, hi₁,
          s25gb_bigon_parameters hK₂.continuousOn hK₁.continuousOn hi₂ h0.symm h1.symm hoff⟩
      · have hoff : ∃ x ∈ Icc (0 : ℝ) 1, γ₁.toFun x ∉ γ₂.toFun '' Icc (0 : ℝ) 1 := by
          obtain ⟨z, hz, hno⟩ := Set.not_subset.1 hsub
          obtain ⟨x, hx, he⟩ := hz
          exact ⟨x, hx, by rwa [he]⟩
        exact ⟨γ₁.toFun, γ₂.toFun, Or.inl ⟨rfl, rfl⟩, hi₁, hi₂,
          s25gb_bigon_parameters hK₁.continuousOn hK₂.continuousOn hi₁ h0 h1 hoff⟩
    · exact Or.inr (Or.inl (s25gb_geodesic_simple_loop hφ hne h₂ hp₂ hi₂))
  · exact Or.inl (s25gb_geodesic_simple_loop hφ hne h₁ hp₁ hi₁)

end LiZhongQC
