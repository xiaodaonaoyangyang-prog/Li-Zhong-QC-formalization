import LiZhongQC.Lemmas.GeodesicEndpointStraight
import LiZhongQC.Lemmas.GeodesicGapArclength
import LiZhongQC.Lemmas.FiniteGeodesicChain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- An oriented smooth straight representative of one actual time interval.
The original parameter map need not be differentiable. -/
structure s25cv_Side (φ : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) where
  side : ℝ → ℂ
  par : ℝ → ℝ
  straight : IsPhiStraightArc φ side 0 1
  smooth : ContDiffOn ℝ 1 side (Icc 0 1)
  regular : ∀ t ∈ Icc (0 : ℝ) 1, derivWithin side (Icc 0 1) t ≠ 0
  mono : StrictMonoOn par (Icc (0 : ℝ) 1)
  bij : BijOn par (Icc (0 : ℝ) 1) (Icc a b)
  first : par 0 = a
  last : par 1 = b
  trace : ∀ t ∈ Icc (0 : ℝ) 1, side t = γ (par t)

/-- Normalize a genuine smooth model and invert its increasing original-time
coordinate. Straightness is transported through the explicit affine map. -/
theorem s25cv_of_model {φ : ℂ → ℂ} {f σ : ℝ → ℂ} {θ : ℝ → ℝ} {a b B : ℝ}
    (hab : a < b) (hB : 0 < B) (hstr : IsPhiStraightArc φ σ 0 B)
    (hσ : ContDiffOn ℝ 1 σ (Icc 0 B))
    (hσd : ∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0)
    (hθm : StrictMonoOn θ (Icc a b)) (hθ : BijOn θ (Icc a b) (Icc 0 B))
    (hθ0 : θ a = 0) (hθ1 : θ b = B)
    (heq : ∀ u ∈ Icc a b, f u = σ (θ u)) :
    Nonempty (s25cv_Side φ f a b) := by
  classical
  let inv := Function.invFunOn θ (Icc a b)
  let side : ℝ → ℂ := fun t => σ (0 + B * t)
  let par : ℝ → ℝ := fun t => inv (B * t)
  have hmap : ∀ t ∈ Icc (0 : ℝ) 1, 0 + B * t ∈ Icc 0 B := by
    intro t ht
    constructor <;> nlinarith [mul_nonneg hB.le ht.1, mul_nonneg hB.le (sub_nonneg.2 ht.2)]
  have hpi : ∀ t ∈ Icc (0 : ℝ) 1, par t ∈ Icc a b := by
    intro t ht
    exact Function.invFunOn_mem (hθ.2.2 (by simpa using hmap t ht))
  have hθp : ∀ t ∈ Icc (0 : ℝ) 1, θ (par t) = B * t := by
    intro t ht
    exact Function.invFunOn_eq (hθ.2.2 (by simpa using hmap t ht))
  have hpm : StrictMonoOn par (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply (hθm.lt_iff_lt (hpi s hs) (hpi t ht)).1
    rw [hθp s hs, hθp t ht]
    exact mul_lt_mul_of_pos_left hst hB
  have hp0 : par 0 = a := by
    change inv (B * 0) = a
    rw [mul_zero, ← hθ0]
    exact hθ.2.1.leftInvOn_invFunOn ⟨le_rfl, hab.le⟩
  have hp1 : par 1 = b := by
    change inv (B * 1) = b
    rw [mul_one, ← hθ1]
    exact hθ.2.1.leftInvOn_invFunOn ⟨hab.le, le_rfl⟩
  have hpbij : BijOn par (Icc (0 : ℝ) 1) (Icc a b) := by
    refine ⟨hpi, hpm.injOn, ?_⟩
    intro u hu
    have hθu := hθ.1 hu
    have htu : θ u / B ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hθu.1 hB.le, (div_le_one hB).2 hθu.2⟩
    refine ⟨θ u / B, htu, ?_⟩
    change inv (B * (θ u / B)) = u
    rw [show B * (θ u / B) = θ u by field_simp]
    exact hθ.2.1.leftInvOn_invFunOn hu
  have hs : IsPhiStraightArc φ side 0 1 := by
    apply s25ep_straight_reparam hstr
    · intro t ht
      change 0 < 0 + B * t ∧ 0 + B * t < B
      constructor <;> nlinarith [mul_pos hB ht.1, mul_pos hB (sub_pos.2 ht.2)]
    · intro t ht
      have hd : HasDerivAt (fun t : ℝ => 0 + B * t) B t := by
        simpa using ((hasDerivAt_id t).const_mul B).const_add 0
      exact ⟨hd.differentiableAt, by rw [hd.deriv]; exact hB.ne'⟩
  refine ⟨{
    side := side
    par := par
    straight := hs
    smooth := fx_p2_contDiffOn_affine hσ hmap
    regular := ?_
    mono := hpm
    bij := hpbij
    first := hp0
    last := hp1
    trace := ?_
  }⟩
  · intro t ht
    have hd : ∀ q ∈ Icc (0 : ℝ) B, HasDerivWithinAt σ (deriv σ q) (Icc 0 B) q :=
      fun q hq => (hσd q hq).1.hasDerivAt.hasDerivWithinAt
    change derivWithin (fun t => σ (0 + B * t)) (Icc 0 1) t ≠ 0
    rw [fx_p2_derivWithin_affine hd zero_lt_one hmap ht]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hB.ne') (hσd _ (hmap t ht)).2
  · intro t ht
    rw [heq _ (hpi t ht), hθp t ht]
    simp only [side, zero_add]

/-- Restrict an already constructed side to any nondegenerate actual-time
subinterval. This preserves its orientation, exact trace, and endpoint tangents. -/
theorem s25cv_restrict {φ : ℂ → ℂ} {f : ℝ → ℂ} {a b c d : ℝ}
    (S : s25cv_Side φ f a b) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    Nonempty (s25cv_Side φ f c d) := by
  obtain ⟨u, hu, huc⟩ := S.bij.2.2 (show c ∈ Icc a b from ⟨hac, hcd.le.trans hdb⟩)
  obtain ⟨v, hv, hvd⟩ := S.bij.2.2 (show d ∈ Icc a b from ⟨hac.trans hcd.le, hdb⟩)
  have huv : u < v := (S.mono.lt_iff_lt hu hv).1 (by simpa [huc, hvd] using hcd)
  let A : ℝ → ℝ := fun t => u + (v - u) * t
  have hA : ∀ t ∈ Icc (0 : ℝ) 1, A t ∈ Icc u v := by
    intro t ht
    dsimp [A]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 huv.le) ht.1,
      mul_nonneg (sub_nonneg.2 huv.le) (sub_nonneg.2 ht.2)]
  have hA01 : ∀ t ∈ Icc (0 : ℝ) 1, A t ∈ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨hu.1.trans (hA t ht).1, (hA t ht).2.trans hv.2⟩
  have hA0 : A 0 = u := by simp [A]
  have hA1 : A 1 = v := by dsimp [A]; ring
  have hAm : StrictMono A := by
    intro s t hst
    simpa only [A, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hst (sub_pos.2 huv)) u
  have hAb : BijOn A (Icc (0 : ℝ) 1) (Icc u v) := by
    refine ⟨hA, (fun x hx y hy he => hAm.injective he), ?_⟩
    intro q hq
    refine ⟨(q - u) / (v - u), ?_, ?_⟩
    · exact ⟨div_nonneg (sub_nonneg.2 hq.1) (sub_nonneg.2 huv.le),
        (div_le_one (sub_pos.2 huv)).2 (by linarith [hq.2])⟩
    · dsimp [A]
      field_simp [(sub_pos.2 huv).ne']
      <;> ring
  have hparb : BijOn (S.par ∘ A) (Icc (0 : ℝ) 1) (Icc c d) := by
    refine ⟨?_, (S.mono.comp (hAm.strictMonoOn (Icc (0 : ℝ) 1)) hA01).injOn, ?_⟩
    · intro t ht
      have hl := S.mono.monotoneOn hu (hA01 t ht) (hA t ht).1
      have hr := S.mono.monotoneOn (hA01 t ht) hv (hA t ht).2
      simpa [huc, hvd] using And.intro hl hr
    · intro q hq
      obtain ⟨w, hw, hwq⟩ := S.bij.2.2
        (show q ∈ Icc a b from ⟨hac.trans hq.1, hq.2.trans hdb⟩)
      have hwuv : w ∈ Icc u v := by
        constructor
        · exact (S.mono.le_iff_le hu hw).1 (by simpa [huc, hwq] using hq.1)
        · exact (S.mono.le_iff_le hw hv).1 (by simpa [hvd, hwq] using hq.2)
      obtain ⟨t, ht, htw⟩ := hAb.2.2 hwuv
      exact ⟨t, ht, by simpa only [Function.comp_apply, htw] using hwq⟩
  have hstr : IsPhiStraightArc φ (S.side ∘ A) 0 1 := by
    apply s25ep_straight_reparam S.straight
    · intro t ht
      have hl := hAm ht.1
      have hr := hAm ht.2
      rw [hA0] at hl
      rw [hA1] at hr
      exact ⟨hu.1.trans_lt hl, hr.trans_le hv.2⟩
    · intro t ht
      have hd : HasDerivAt A (v - u) t := by
        simpa only [A, id_eq, mul_one] using ((hasDerivAt_id t).const_mul (v - u)).const_add u
      exact ⟨hd.differentiableAt, by rw [hd.deriv]; exact (sub_pos.2 huv).ne'⟩
  refine ⟨{
    side := S.side ∘ A
    par := S.par ∘ A
    straight := hstr
    smooth := fx_p2_contDiffOn_affine S.smooth hA01
    regular := ?_
    mono := S.mono.comp (hAm.strictMonoOn (Icc (0 : ℝ) 1)) hA01
    bij := hparb
    first := by simpa only [Function.comp_apply, hA0] using huc
    last := by simpa only [Function.comp_apply, hA1] using hvd
    trace := fun t ht => S.trace (A t) (hA01 t ht)
  }⟩
  intro t ht
  change derivWithin (fun t => S.side (u + (v - u) * t)) (Icc 0 1) t ≠ 0
  rw [fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn S.smooth)
    zero_lt_one hA01 ht]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (sub_pos.2 huv).ne') (S.regular _ (hA01 t ht))

/-- The compiled actual right-endpoint theorem supplies a straight smooth side. -/
theorem s25cv_zero_right {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx1 : x < 1) (hz : φ (γ.toFun x) = 0) :
    ∃ ε > 0, Nonempty (s25cv_Side φ γ.toFun x (x + ε)) := by
  obtain ⟨ε, B, σ, θ, hε, _, hB, _, _, hstr, hσ, _, hd, _, hm, hb, h0, h1, heq, _⟩ :=
    s25ep_actual_right_endpoint_straight hφ hne hγ hp hx hx1 hz
  exact ⟨ε, hε, s25cv_of_model (by linarith) hB hstr hσ hd hm hb h0 h1 heq⟩

/-- The compiled left endpoint is reversed explicitly before normalization. -/
theorem s25cv_zero_left {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx0 : 0 < x) (hz : φ (γ.toFun x) = 0) :
    ∃ ε > 0, Nonempty (s25cv_Side φ γ.toFun (x - ε) x) := by
  obtain ⟨ε, B, σ, θ, hε, _, hB, _, _, hstr, hσ, _, hd, _, hm, hb, h0, h1, heq, _⟩ :=
    s25ep_actual_left_endpoint_straight hφ hne hγ hp hx hx0 hz
  let η : ℝ → ℝ := fun t => B - θ t
  let τ : ℝ → ℂ := fun q => σ (B - q)
  have hηm : StrictMonoOn η (Icc (x - ε) x) := by
    intro s hs t ht hst
    exact sub_lt_sub_left (hm hs ht hst) B
  have hηb : BijOn η (Icc (x - ε) x) (Icc 0 B) := by
    refine ⟨?_, hηm.injOn, ?_⟩
    · intro t ht
      have h := hb.1 ht
      constructor <;> dsimp [η] <;> linarith [h.1, h.2]
    · intro q hq
      obtain ⟨t, ht, he⟩ := hb.2.2 (show B - q ∈ Icc (0 : ℝ) B by
        constructor <;> linarith [hq.1, hq.2])
      exact ⟨t, ht, by dsimp [η]; rw [he]; ring⟩
  have hτs : IsPhiStraightArc φ τ 0 B := by
    apply s25ep_straight_reparam hstr
    · intro t ht
      change 0 < B - t ∧ B - t < B
      constructor <;> linarith [ht.1, ht.2]
    · intro t ht
      have h : HasDerivAt (fun q : ℝ => B - q) (-1) t := by
        simpa only [id_eq] using (hasDerivAt_id t).const_sub B
      refine ⟨h.differentiableAt, ?_⟩
      change deriv (fun q : ℝ => B - q) t ≠ 0
      rw [h.deriv]
      norm_num
  have hτc : ContDiffOn ℝ 1 τ (Icc 0 B) :=
    hσ.comp (by fun_prop : ContDiff ℝ 1 (fun q : ℝ => B - q)).contDiffOn (by
      intro q hq; constructor <;> linarith [hq.1, hq.2])
  have hτd : ∀ q ∈ Icc 0 B, DifferentiableAt ℝ τ q ∧ deriv τ q ≠ 0 := by
    intro q hq
    have hq' : B - q ∈ Icc (0 : ℝ) B := by constructor <;> linarith [hq.1, hq.2]
    have h := (hd _ hq').1.hasDerivAt.scomp q ((hasDerivAt_id q).const_sub B)
    have h' : HasDerivAt τ (-deriv σ (B - q)) q := by
      simpa only [τ, Function.comp_def, one_smul, neg_smul] using h
    exact ⟨h'.differentiableAt, by rw [h'.deriv]; exact neg_ne_zero.2 (hd _ hq').2⟩
  refine ⟨ε, hε, s25cv_of_model (by linarith) hB hτs hτc hτd hηm hηb ?_ ?_ ?_⟩
  · dsimp [η]; rw [h1]; ring
  · dsimp [η]; rw [h0]; ring
  · intro t ht
    simpa only [τ, η, sub_sub_cancel] using heq t ht

end LiZhongQC

