import LiZhongQC.Lemmas.GeodesicLeftEndpoints
import LiZhongQC.Lemmas.FiniteGeodesicChain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Convert a one-sided smooth endpoint parametrization into an oriented
unit-interval side and an increasing map back to the original time interval.
No differentiability of the original time change is needed. -/
theorem s25gb_endpoint_normalize {f σ : ℝ → ℂ} {θ : ℝ → ℝ} {a b B : ℝ}
    (hab : a < b) (hB : 0 < B)
    (hσ : ContDiffOn ℝ 1 σ (Icc 0 B))
    (hσd : ∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0)
    (hθm : StrictMonoOn θ (Icc a b)) (hθ : BijOn θ (Icc a b) (Icc 0 B))
    (hθ0 : θ a = 0) (hθ1 : θ b = B)
    (heq : ∀ u ∈ Icc a b, f u = σ (θ u)) :
    ∃ side : ℝ → ℂ, ∃ par : ℝ → ℝ,
      ContDiffOn ℝ 1 side (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, derivWithin side (Icc 0 1) t ≠ 0) ∧
      StrictMonoOn par (Icc (0 : ℝ) 1) ∧ BijOn par (Icc (0 : ℝ) 1) (Icc a b) ∧
      par 0 = a ∧ par 1 = b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, side t = f (par t)) ∧
      side 0 = f a ∧ side 1 = f b := by
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
    have htu : θ u / B ∈ Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg hθu.1 hB.le, (div_le_one hB).2 hθu.2⟩
    refine ⟨θ u / B, htu, ?_⟩
    change inv (B * (θ u / B)) = u
    have hcancel : B * (θ u / B) = θ u := by field_simp
    rw [hcancel]
    exact hθ.2.1.leftInvOn_invFunOn hu
  have hside : ∀ t ∈ Icc (0 : ℝ) 1, side t = f (par t) := by
    intro t ht
    rw [heq _ (hpi t ht), hθp t ht]
    simp only [side, zero_add]
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin side (Icc 0 1) t = (B : ℂ) * deriv σ (B * t) := by
    intro t ht
    have hd : ∀ q ∈ Icc (0 : ℝ) B, HasDerivWithinAt σ (deriv σ q) (Icc 0 B) q :=
      fun q hq => (hσd q hq).1.hasDerivAt.hasDerivWithinAt
    simpa only [side, zero_add] using fx_p2_derivWithin_affine hd zero_lt_one hmap ht
  refine ⟨side, par, fx_p2_contDiffOn_affine hσ hmap, ?_, hpm, hpbij, hp0, hp1,
    hside, ?_, ?_⟩
  · intro t ht
    rw [hder t ht]
    exact mul_ne_zero (by exact_mod_cast hB.ne')
      (hσd _ (by simpa only [zero_add] using hmap t ht)).2
  · simpa only [hp0] using hside 0 ⟨le_rfl, zero_le_one⟩
  · simpa only [hp1] using hside 1 ⟨zero_le_one, le_rfl⟩

/-- The actual right endpoint API supplies a smooth regular unit side with
an increasing, onto original-time map. Straightness and corner matching are
not silently added to the endpoint API's conclusion. -/
theorem s25gb_actual_right_side {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (ha1 : a < 1) (hz : φ (γ.toFun a) = 0) :
    ∃ ε > 0, a + ε < 1 ∧ ∃ (side : ℝ → ℂ) (par : ℝ → ℝ),
      ContDiffOn ℝ 1 side (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, derivWithin side (Icc 0 1) t ≠ 0) ∧
      StrictMonoOn par (Icc (0 : ℝ) 1) ∧ BijOn par (Icc (0 : ℝ) 1) (Icc a (a + ε)) ∧
      par 0 = a ∧ par 1 = a + ε ∧
      (∀ t ∈ Icc (0 : ℝ) 1, side t = γ.toFun (par t)) ∧
      side 0 = γ.toFun a ∧ side 1 = γ.toFun (a + ε) := by
  obtain ⟨ε, B, σ, θ, hε, hε1, hB, hσ0, hσB, hσ, hσi, hσd,
    hθc, hθm, hθ, hθ0, hθ1, heq, himage⟩ :=
    s25ep_actual_right_endpoint hφ hne hγ hp ha ha1 hz
  exact ⟨ε, hε, hε1,
    s25gb_endpoint_normalize (by linarith) hB hσ hσd hθm hθ hθ0 hθ1 heq⟩

/-- Reverse the outgoing smooth coordinate on a left endpoint. The time map
is then increasing, exactly as the finite-chain assembler requires. -/
theorem s25gb_actual_left_side {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hb0 : 0 < b) (hz : φ (γ.toFun b) = 0) :
    ∃ ε > 0, 0 < b - ε ∧ ∃ (side : ℝ → ℂ) (par : ℝ → ℝ),
      ContDiffOn ℝ 1 side (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, derivWithin side (Icc 0 1) t ≠ 0) ∧
      StrictMonoOn par (Icc (0 : ℝ) 1) ∧ BijOn par (Icc (0 : ℝ) 1) (Icc (b - ε) b) ∧
      par 0 = b - ε ∧ par 1 = b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, side t = γ.toFun (par t)) ∧
      side 0 = γ.toFun (b - ε) ∧ side 1 = γ.toFun b := by
  obtain ⟨ε, B, σ, θ, hε, hε0, hB, hσ0, hσB, hσ, hσi, hσd,
    hθc, hθa, hθ, hθ0, hθ1, heq, himage⟩ :=
    s25ep_actual_left_endpoint hφ hne hγ hp hb hb0 hz
  let η : ℝ → ℝ := fun u => B - θ u
  let τ : ℝ → ℂ := fun q => σ (B - q)
  have hηm : StrictMonoOn η (Icc (b - ε) b) := by
    intro u hu v hv huv
    dsimp [η]
    exact sub_lt_sub_left (hθa hu hv huv) B
  have hη : BijOn η (Icc (b - ε) b) (Icc 0 B) := by
    refine ⟨?_, hηm.injOn, ?_⟩
    · intro u hu
      have h := hθ.1 hu
      constructor <;> dsimp [η] <;> linarith [h.1, h.2]
    · intro q hq
      obtain ⟨u, hu, heu⟩ := hθ.2.2 (show B - q ∈ Icc (0 : ℝ) B by
        constructor <;> linarith [hq.1, hq.2])
      refine ⟨u, hu, ?_⟩
      dsimp [η]
      rw [heu]
      ring
  have hτ : ContDiffOn ℝ 1 τ (Icc 0 B) :=
    hσ.comp (by fun_prop : ContDiff ℝ 1 (fun q : ℝ => B - q)).contDiffOn (by
      intro q hq
      constructor <;> linarith [hq.1, hq.2])
  have hτd : ∀ q ∈ Icc 0 B, DifferentiableAt ℝ τ q ∧ deriv τ q ≠ 0 := by
    intro q hq
    have hq' : B - q ∈ Icc (0 : ℝ) B := by constructor <;> linarith [hq.1, hq.2]
    have hd := (hσd _ hq').1.hasDerivAt.scomp q ((hasDerivAt_id q).const_sub B)
    have hd' : HasDerivAt τ (-deriv σ (B - q)) q := by
      simpa only [τ, Function.comp_def, one_smul, neg_smul] using hd
    exact ⟨hd'.differentiableAt, by rw [hd'.deriv]; exact neg_ne_zero.2 (hσd _ hq').2⟩
  have hη0 : η (b - ε) = 0 := by dsimp [η]; rw [hθ1]; ring
  have hη1 : η b = B := by dsimp [η]; rw [hθ0]; ring
  have heq' : ∀ u ∈ Icc (b - ε) b, γ.toFun u = τ (η u) := by
    intro u hu
    dsimp [τ, η]
    simpa only [sub_sub_cancel] using heq u hu
  exact ⟨ε, hε, hε0,
    s25gb_endpoint_normalize (by linarith) hB hτ hτd hηm hη hη0 hη1 heq'⟩

end LiZhongQC

