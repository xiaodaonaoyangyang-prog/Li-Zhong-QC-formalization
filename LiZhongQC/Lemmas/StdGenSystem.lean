import LiZhongQC.Lemmas.StdGenLift
import LiZhongQC.Lemmas.StdGenChordLoops
import LiZhongQC.Lemmas.StdGenGroup
import LiZhongQC.Lemmas.StdGenLink2

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

/-!
# Standard generators: assembly (R83, S27 `[e]`; 下属1)

* `s83sg_system` [S3]: a geometric standard system (generation, relation, `δ_g` hyperbolic, `tr[γ_g, δ_g] < 2`),
  assembled from the model `Q g` (T1), its chord loops and their classes ([a+b]), the deck representation (S2),
  the lifts ([c], [d1], [d2]), the separation and trace lemmas (L4, L5, D) and the group package (G1, G2).
* `s83sg_target`, `s83sg_exists_standardGenerators`: §27.1 `exists_standardGenerators` (statement of S27:2160).
-/

noncomputable section
namespace LiZhongQC

universe u

/-- A 1-periodic continuous map is a loop on `[0, 1]`. -/
theorem s83sy_loop_path {X : Type*} [TopologicalSpace X] (f : ℝ → X) (x : X) (hf : Continuous f)
    (hper : ∀ t, f (t + 1) = f t) (h0 : f 0 = x) : ∃ L : Path x x, ∀ t : unitInterval, L t = f t :=
  ⟨{ toFun := fun t => f t
     continuous_toFun := hf.comp continuous_subtype_val
     source' := by simpa using h0
     target' := by
       show f ((1 : unitInterval) : ℝ) = x
       rw [Set.Icc.coe_one, ← zero_add (1 : ℝ), hper, h0] }, fun t => rfl⟩

/-- Group words of the chord classes: `X = w b^{s₁} w⁻¹`, `Y = w (b^{s₂} a^{s₃} b^{-s₂}) w⁻¹` with `a, b` without
common powers: the powers of `X⁻¹`, `Y⁻¹` are nontrivial and different, and conjugation by `w b^{s₂}` sends
`X⁻¹ ↦ b^{-s₁}`, `Y⁻¹ ↦ a^{-s₃}`. -/
theorem s83sy_group {G : Type*} [Group G] (a b w : G) (hab : ∀ m n : ℤ, a ^ m = b ^ n → m = 0 ∧ n = 0)
    (s₁ s₂ s₃ : ℤ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₃ : s₃ = 1 ∨ s₃ = -1) :
    (∀ n : ℤ, n ≠ 0 → (w * b ^ s₁ * w⁻¹)⁻¹ ^ n ≠ 1) ∧
    (∀ n : ℤ, n ≠ 0 → (w * (b ^ s₂ * a ^ s₃ * b ^ (-s₂)) * w⁻¹)⁻¹ ^ n ≠ 1) ∧
    (∀ m n : ℤ, (w * b ^ s₁ * w⁻¹)⁻¹ ^ m = (w * (b ^ s₂ * a ^ s₃ * b ^ (-s₂)) * w⁻¹)⁻¹ ^ n →
      m = 0 ∧ n = 0) ∧
    (w * b ^ s₂)⁻¹ * (w * b ^ s₁ * w⁻¹)⁻¹ * (w * b ^ s₂) = b ^ (-s₁) ∧
    (w * b ^ s₂)⁻¹ * (w * (b ^ s₂ * a ^ s₃ * b ^ (-s₂)) * w⁻¹)⁻¹ * (w * b ^ s₂) = a ^ (-s₃) ∧
    b ≠ 1 := by
  have hX : ∀ n : ℤ, (w * b ^ s₁ * w⁻¹)⁻¹ ^ n = w * b ^ (-(s₁ * n)) * w⁻¹ := by
    intro n
    rw [inv_zpow', conj_zpow, ← zpow_mul, show s₁ * -n = -(s₁ * n) by ring]
  have hY : ∀ n : ℤ, (w * (b ^ s₂ * a ^ s₃ * b ^ (-s₂)) * w⁻¹)⁻¹ ^ n =
      w * (b ^ s₂ * a ^ (-(s₃ * n)) * (b ^ s₂)⁻¹) * w⁻¹ := by
    intro n
    rw [inv_zpow', conj_zpow, zpow_neg b s₂, conj_zpow, ← zpow_mul, show s₃ * -n = -(s₃ * n) by ring]
  refine ⟨fun n hn h => ?_, fun n hn h => ?_, fun m n h => ?_, by group, by group, fun h => ?_⟩
  · rw [hX, conj_eq_one_iff] at h
    have := (hab 0 (-(s₁ * n)) (by rw [zpow_zero, h])).2
    rcases hs₁ with rfl | rfl <;> omega
  · rw [hY, conj_eq_one_iff, conj_eq_one_iff] at h
    have := (hab (-(s₃ * n)) 0 (by rw [zpow_zero]; exact h)).1
    rcases hs₃ with rfl | rfl <;> omega
  · rw [hX, hY] at h
    have h2 := mul_left_cancel (mul_right_cancel h)
    have h3 : a ^ (-(s₃ * n)) = b ^ (-(s₁ * m)) := by
      calc a ^ (-(s₃ * n)) = (b ^ s₂)⁻¹ * (b ^ s₂ * a ^ (-(s₃ * n)) * (b ^ s₂)⁻¹) * b ^ s₂ := by group
        _ = (b ^ s₂)⁻¹ * b ^ (-(s₁ * m)) * b ^ s₂ := by rw [← h2]
        _ = b ^ (-(s₁ * m)) := by group
    obtain ⟨h4, h5⟩ := hab _ _ h3
    rcases hs₁ with rfl | rfl <;> rcases hs₃ with rfl | rfl <;> omega
  · have := (hab 0 1 (by rw [zpow_zero, zpow_one, h])).2
    omega

/-- The class map `Θ` is injective modulo `±1`. -/
theorem s83sy_lift {g : ℕ} {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (Θ : Γ₀ →* surfaceGroup g)
    (hΘk : ∀ γ : Γ₀, Θ γ = 1 ↔ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1) (x y : Γ₀) :
    Θ x = Θ y ↔ ((x : Matrix.SpecialLinearGroup (Fin 2) ℝ) = y ∨
      (x : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -y) := by
  have key : Θ x = Θ y ↔ Θ (x * y⁻¹) = 1 := by
    constructor
    · intro h
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel _
    · intro h
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact h)
  rw [key, hΘk, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, neg_one_mul]

theorem s83sy_comm_neg_left (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    commutatorSL (-X) Y = commutatorSL X Y := by
  have hn : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) ℝ, (-Z)⁻¹ = -Z⁻¹ := fun Z =>
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  unfold commutatorSL
  rw [hn]
  simp only [neg_mul, mul_neg, neg_neg]

theorem s83sy_comm_neg_right (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    commutatorSL X (-Y) = commutatorSL X Y := by
  have hn : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) ℝ, (-Z)⁻¹ = -Z⁻¹ := fun Z =>
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  unfold commutatorSL
  rw [hn]
  simp only [neg_mul, mul_neg, neg_neg]

theorem s83sy_tr_inv (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) : (M⁻¹) 0 0 + (M⁻¹) 1 1 = M 0 0 + M 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp
  ring

theorem s83sy_tr_swap (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (commutatorSL Y X) 0 0 + (commutatorSL Y X) 1 1 = (commutatorSL X Y) 0 0 + (commutatorSL X Y) 1 1 := by
  rw [show commutatorSL Y X = (commutatorSL X Y)⁻¹ by unfold commutatorSL; group]
  exact s83sy_tr_inv _

theorem s83sy_tr_inv_left (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (commutatorSL X⁻¹ Y) 0 0 + (commutatorSL X⁻¹ Y) 1 1 = (commutatorSL X Y) 0 0 + (commutatorSL X Y) 1 1 := by
  rw [show commutatorSL X⁻¹ Y = X⁻¹ * commutatorSL Y X * X⁻¹⁻¹ by unfold commutatorSL; group,
    s83sg_trace_conj, s83sy_tr_swap]

theorem s83sy_tr_inv_right (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (commutatorSL X Y⁻¹) 0 0 + (commutatorSL X Y⁻¹) 1 1 = (commutatorSL X Y) 0 0 + (commutatorSL X Y) 1 1 := by
  rw [show commutatorSL X Y⁻¹ = Y⁻¹ * commutatorSL Y X * Y⁻¹⁻¹ by unfold commutatorSL; group,
    s83sg_trace_conj, s83sy_tr_swap]

/-- Transfer from the chord lifts `A, B` to the group-package pair `Q, P` (`u⁻¹ A u = ±P^{∓1}`,
`u⁻¹ B u = ±Q^{∓1}`): commuting and the commutator trace. -/
theorem s83sy_transfer (A B u P Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s₁ s₃ : ℤ)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₃ : s₃ = 1 ∨ s₃ = -1)
    (hA : u⁻¹ * A * u = P ^ (-s₁) ∨ u⁻¹ * A * u = -P ^ (-s₁))
    (hB : u⁻¹ * B * u = Q ^ (-s₃) ∨ u⁻¹ * B * u = -Q ^ (-s₃)) :
    (A * B = B * A → Q * P = P * Q) ∧
      (commutatorSL A B) 0 0 + (commutatorSL A B) 1 1 = (commutatorSL Q P) 0 0 + (commutatorSL Q P) 1 1 := by
  have hA2 : u⁻¹ * A * u = P ∨ u⁻¹ * A * u = P⁻¹ ∨ u⁻¹ * A * u = -P ∨ u⁻¹ * A * u = -P⁻¹ := by
    rcases hs₁ with rfl | rfl <;> rcases hA with h | h <;> simp [h]
  have hB2 : u⁻¹ * B * u = Q ∨ u⁻¹ * B * u = Q⁻¹ ∨ u⁻¹ * B * u = -Q ∨ u⁻¹ * B * u = -Q⁻¹ := by
    rcases hs₃ with rfl | rfl <;> rcases hB with h | h <;> simp [h]
  constructor
  · intro hAB
    have hc : Commute (u⁻¹ * A * u) (u⁻¹ * B * u) := by
      show (u⁻¹ * A * u) * (u⁻¹ * B * u) = (u⁻¹ * B * u) * (u⁻¹ * A * u)
      calc (u⁻¹ * A * u) * (u⁻¹ * B * u) = u⁻¹ * (A * B) * u := by group
        _ = u⁻¹ * (B * A) * u := by rw [hAB]
        _ = (u⁻¹ * B * u) * (u⁻¹ * A * u) := by group
    have hPQ : Commute P Q := by
      rcases hA2 with h | h | h | h <;> rcases hB2 with k | k | k | k <;> rw [h, k] at hc <;>
        simpa [Commute.neg_left_iff, Commute.neg_right_iff, Commute.inv_left_iff, Commute.inv_right_iff]
          using hc
    exact hPQ.eq.symm
  · rw [show commutatorSL A B = u * commutatorSL (u⁻¹ * A * u) (u⁻¹ * B * u) * u⁻¹ by
      unfold commutatorSL; group, s83sg_trace_conj]
    rcases hA2 with h | h | h | h <;> rcases hB2 with k | k | k | k <;> rw [h, k] <;>
      (try simp only [s83sy_comm_neg_left, s83sy_comm_neg_right, s83sy_tr_inv_left, s83sy_tr_inv_right]) <;>
      exact (s83sy_tr_swap P Q).symm

/-- The conjugation `X ↦ A X A⁻¹` as a monoid hom. -/
theorem s83sg_conj_system {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ}
    (first : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (γg δg : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : ∀ j, (first j).1 ∈ Γ₀ ∧ (first j).2 ∈ Γ₀) (hγ : γg ∈ Γ₀) (hδ : δg ∈ Γ₀)
    (hgen : Subgroup.closure (range (fun j => (first j).1) ∪ range (fun j => (first j).2) ∪ {γg, δg}) ⊔
        Subgroup.zpowers (-1) = Γ₀ ⊔ Subgroup.zpowers (-1))
    (hrel : (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = 1 ∨
        (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = -1)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : (A * δg * A⁻¹) 0 1 = 0 ∧ (A * δg * A⁻¹) 1 0 = 0 ∧ 1 < (A * δg * A⁻¹) 0 0 ^ 2)
    (hfix : (A * γg * A⁻¹) 0 0 + (A * γg * A⁻¹) 0 1 = (A * γg * A⁻¹) 1 0 + (A * γg * A⁻¹) 1 1)
    (halt : 0 < (A * γg * A⁻¹) 0 1 * (A * γg * A⁻¹) 1 0) :
    Nonempty (StandardGenerators (conjGroup Γ₀ A) g) := by
  let c : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    (MulAut.conj A).toMonoidHom
  have hc : ∀ x, c x = A * x * A⁻¹ := fun x => rfl
  have hcn : c (-1) = -1 := by
    rw [hc, mul_neg, mul_one, neg_mul, mul_inv_cancel]
  have hcomm : ∀ x y, commutatorSL (c x) (c y) = c (commutatorSL x y) := by
    intro x y
    simp [commutatorSL]
  refine ⟨{
    first := fun j => (c (first j).1, c (first j).2)
    γg := c γg
    δg := c δg
    first_mem := fun j => ⟨⟨_, (hf j).1, rfl⟩, ⟨_, (hf j).2, rfl⟩⟩
    γg_mem := ⟨_, hγ, rfl⟩
    δg_mem := ⟨_, hδ, rfl⟩
    generate := ?_
    relation := ?_
    δg_diagonal := hd
    γg_fixes_one := hfix
    alternate := halt }⟩
  · have := congrArg (Subgroup.map c) hgen
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_closure, MonoidHom.map_zpowers, hcn] at this
    convert this using 2
    · simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
      rfl
    · rfl
  · have key : (List.ofFn fun j => commutatorSL (c (first j).1) (c (first j).2)).prod *
        commutatorSL (c γg) (c δg) =
        c ((List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg) := by
      rw [map_mul, map_list_prod, List.map_ofFn]
      simp only [hcomm]
      rfl
    show (List.ofFn fun j => commutatorSL (c (first j).1) (c (first j).2)).prod *
        commutatorSL (c γg) (c δg) = 1 ∨ _ = -1
    rcases hrel with h | h
    · left; rw [key, h, map_one]
    · right; rw [key, h, hcn]

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **[S3, W2 + W3: a geometric standard system]**  The generators, relation and generation of a standard
system, with the normalization (27.5) replaced by `δ_g` hyperbolic and `tr[γ_g, δ_g] < 2` (the invariant form
of "the fixed points alternate", `s83sg_normalize`).  All the topology lives here. -/
theorem s83sg_system [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ (first : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (γg δg : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ j, (first j).1 ∈ Γ₀ ∧ (first j).2 ∈ Γ₀) ∧ γg ∈ Γ₀ ∧ δg ∈ Γ₀ ∧
      Subgroup.closure (range (fun j => (first j).1) ∪ range (fun j => (first j).2) ∪ {γg, δg}) ⊔
        Subgroup.zpowers (-1) = Γ₀ ⊔ Subgroup.zpowers (-1) ∧
      ((List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = 1 ∨
        (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = -1) ∧
      4 < (δg 0 0 + δg 1 1) ^ 2 ∧
      (commutatorSL γg δg) 0 0 + (commutatorSL γg δg) 1 1 < 2 := by
  have hc0 : CompactSpace S₀ := hS.1
  have hfree := s27g_actsFreely hp₀
  have hΓ : IsFuchsian Γ₀ := utm_x2_isFuchsian hp₀
  obtain ⟨K, hK, hKc⟩ := bsu24_cocompact hp₀ (Homeomorph.refl UpperHalfPlane)
    (fun γ₀ hγ₀ => ⟨γ₀, hγ₀, fun τ => rfl⟩)
  have hcc : IsCocompact Γ₀ := ⟨K, hK, hKc⟩
  -- the model and its chord loops
  obtain ⟨h⟩ := s83sg_model_homeo hg hS
  obtain ⟨c₀, α, β, e, ε, θ₀, θ₁, θ₂, θ₃, e₀, w, ga, gb, s₁, s₂, s₃, hga, hgb, hαc, hβc, hαper, hβper,
    hα0, hβ0, hαs, hβs, hαβ, hc0e, he0, het, hε, hε2, h01, h12, h23, h30, hαe, hβe, hαp, hαm, hβp, hβm,
    hs₁, hs₂, hs₃, hcα, hcβ⟩ := s83sg_chord_model g hg
  obtain ⟨τ₀, hτ₀⟩ := hp₀.2.2.1 (h.symm c₀)
  obtain ⟨ρ, hρs, hρk, hρp⟩ := s83sg_deck_pi1 hp₀ τ₀
  -- the class map `Θ : Γ₀ → surfaceGroup g`
  let hcont : C(S₀, Quot (OrientableRel g 0)) := ⟨h, h.continuous⟩
  have hx : hcont (p₀ τ₀) = c₀ := by
    show h (p₀ τ₀) = c₀
    rw [hτ₀, Homeomorph.apply_symm_apply]
  let M : FundamentalGroup S₀ (p₀ τ₀) ≃* FundamentalGroup (Quot (OrientableRel g 0)) c₀ :=
    MulEquiv.ofBijective (FundamentalGroup.mapOfEq hcont hx)
      (s78dg_pi1_mapOfEq_bijective hcont _ _ hx (s78dg_pi1_homeo_bijective h _))
  let Θ : Γ₀ →* surfaceGroup g := (e₀.toMonoidHom.comp M.toMonoidHom).comp ρ
  have hΘs : Function.Surjective Θ := e₀.surjective.comp (M.surjective.comp hρs)
  have hΘk : ∀ γ : Γ₀, Θ γ = 1 ↔ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1 := by
    intro γ
    rw [← hρk γ]
    constructor
    · intro h1
      apply M.injective
      apply e₀.injective
      rw [map_one, map_one]
      exact h1
    · intro h1
      show e₀ (M (ρ γ)) = 1
      rw [h1, map_one, map_one]
  -- the loops on `S₀`
  let αS : ℝ → S₀ := fun t => h.symm (α t)
  let βS : ℝ → S₀ := fun t => h.symm (β t)
  have hαSc : Continuous αS := h.symm.continuous.comp hαc
  have hβSc : Continuous βS := h.symm.continuous.comp hβc
  have hαSper : ∀ t, αS (t + 1) = αS t := fun t => by
    show h.symm (α (t + 1)) = h.symm (α t)
    rw [hαper]
  have hβSper : ∀ t, βS (t + 1) = βS t := fun t => by
    show h.symm (β (t + 1)) = h.symm (β t)
    rw [hβper]
  have hαS0 : αS 0 = p₀ τ₀ := by
    show h.symm (α 0) = _
    rw [hα0, hτ₀]
  have hβS0 : βS 0 = p₀ τ₀ := by
    show h.symm (β 0) = _
    rw [hβ0, hτ₀]
  have hαSs : ∀ s t, αS s = αS t → ∃ n : ℤ, s = t + n := fun s t hst => hαs s t (h.symm.injective hst)
  have hβSs : ∀ s t, βS s = βS t → ∃ n : ℤ, s = t + n := fun s t hst => hβs s t (h.symm.injective hst)
  have hαβS : ∀ s t, αS s = βS t → (∃ m : ℤ, s = m) ∧ ∃ n : ℤ, t = n :=
    fun s t hst => hαβ s t (h.symm.injective hst)
  -- lifts [c] and their classes
  obtain ⟨γ, a, ha, ha0, haα, haγ, hργ⟩ := s83sg_lift_loop hp₀ τ₀ ρ hρp hαSc hαSper hαS0
  obtain ⟨δ, b, hb, hb0, hbβ, hbδ, hρδ⟩ := s83sg_lift_loop hp₀ τ₀ ρ hρp hβSc hβSper hβS0
  have hΘγ : Θ γ = w * gb ^ s₁ * w⁻¹ := by
    obtain ⟨LS, hLS⟩ := s83sy_loop_path αS (p₀ τ₀) hαSc hαSper hαS0
    obtain ⟨LQ, hLQ⟩ := s83sy_loop_path α c₀ hαc hαper hα0
    have h2 : M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk LS)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk LQ) :=
      s78dg_pi1_mapOfEq_mk hcont (p₀ τ₀) c₀ hx LS LQ (fun t => by
        rw [hLQ, hLS]
        exact (h.apply_symm_apply _).symm)
    show e₀ (M (ρ γ)) = _
    rw [hργ LS hLS, h2]
    exact hcα LQ hLQ
  have hΘδ : Θ δ = w * (gb ^ s₂ * ga ^ s₃ * gb ^ (-s₂)) * w⁻¹ := by
    obtain ⟨LS, hLS⟩ := s83sy_loop_path βS (p₀ τ₀) hβSc hβSper hβS0
    obtain ⟨LQ, hLQ⟩ := s83sy_loop_path β c₀ hβc hβper hβ0
    have h2 : M (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk LS)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk LQ) :=
      s78dg_pi1_mapOfEq_mk hcont (p₀ τ₀) c₀ hx LS LQ (fun t => by
        rw [hLQ, hLS]
        exact (h.apply_symm_apply _).symm)
    show e₀ (M (ρ δ)) = _
    rw [hρδ LS hLS, h2]
    exact hcβ LQ hLQ
  -- group facts
  obtain ⟨hX, hY, hXY, hcX, hcY, hb1⟩ := s83sy_group ga gb w
    (fun m n hmn => s83sg_sg_pow g ⟨g - 1, by omega⟩ m n (by subst hga hgb; exact hmn)) s₁ s₂ s₃ hs₁ hs₃
  have hA : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ∈ Γ₀ := Γ₀.inv_mem γ.2
  have hB : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ∈ Γ₀ := Γ₀.inv_mem δ.2
  have hcoe : ∀ (x : Γ₀) (n : ℤ), ((x⁻¹ ^ n : Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) =
      ((x : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n := fun x n => by
    rw [Subgroup.coe_zpow, Subgroup.coe_inv]
  have hpow : ∀ (x : Γ₀) (n : ℤ), Θ x⁻¹ ^ n ≠ 1 →
      ((x : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ 1 ∧
        ((x : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ -1 := by
    intro x n hn
    have hn' : Θ (x⁻¹ ^ n) ≠ 1 := by rw [map_zpow]; exact hn
    exact ⟨fun h1 => hn' ((hΘk _).2 (Or.inl ((hcoe x n).trans h1))),
      fun h1 => hn' ((hΘk _).2 (Or.inr ((hcoe x n).trans h1)))⟩
  have hpa : ∀ n : ℤ, n ≠ 0 → ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ 1 ∧
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ -1 := fun n hn =>
    hpow γ n (by rw [map_inv, hΘγ]; exact hX n hn)
  have hpb : ∀ n : ℤ, n ≠ 0 → ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ 1 ∧
      ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ≠ -1 := fun n hn =>
    hpow δ n (by rw [map_inv, hΘδ]; exact hY n hn)
  have hpab : ∀ m n : ℤ, ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ m =
      ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n ∨
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ m = -((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ^ n →
      m = 0 ∧ n = 0 := by
    intro m n hmn
    have h1 : Θ (γ⁻¹ ^ m) = Θ (δ⁻¹ ^ n) := by
      rw [s83sy_lift Θ hΘk, hcoe, hcoe]
      exact hmn
    rw [map_zpow, map_zpow, map_inv, map_inv, hΘγ, hΘδ] at h1
    exact hXY m n h1
  -- [d1]
  obtain ⟨hai, hbi, hmeet⟩ := s83sg_lift_inj_meet hp₀ hA hB haα hbβ haγ hbδ (ha0.trans hb0.symm) hαSs hβSs
    hαβS hpa hpb hpab
  -- the chart on `S₀` and [d2]
  let eS : OpenPartialHomeomorph S₀ ℂ := h.toOpenPartialHomeomorph.trans e
  have hsrc : ∀ x, x ∈ eS.source ↔ h x ∈ e.source := fun x => by
    simp [eS]
  have happ : ∀ x, eS x = e (h x) := fun x => rfl
  have hetS : eS.target = Metric.ball 0 1 := by
    simp [eS, het]
  have hhα : ∀ t, h (αS t) = α t := fun t => h.apply_symm_apply _
  have hhβ : ∀ t, h (βS t) = β t := fun t => h.apply_symm_apply _
  have hcross := s83sg_lift_cross hp₀ hA ha hb haα hbβ haγ (ha0.trans hb0.symm) hpa eS ε θ₀ θ₁ θ₂ θ₃
    ((hsrc _).2 (by rw [hhα, hα0]; exact hc0e)) (by rw [happ, hhα, hα0, he0]) hetS hε hε2 h01 h12 h23 h30
    (fun t => by rw [hsrc, hhα]; exact hαe t)
    (fun t h1 h2 => by rw [happ, hhα]; exact hαp t h1 h2)
    (fun t h1 h2 => by rw [happ, hhα]; exact hαm t h1 h2)
    (fun t h1 h2 => by rw [happ, hhβ]; exact hβp t h1 h2)
    (fun t h1 h2 => by rw [happ, hhβ]; exact hβm t h1 h2)
  -- hyperbolicity of the chord lifts
  have hAh : IsHyperbolic ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ := by
    have h1 := hpa 1 one_ne_zero
    rw [zpow_one] at h1
    exact cocompact_elements_hyperbolic hΓ hfree hcc _ hA h1.1 h1.2
  have hBh : IsHyperbolic ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ := by
    have h1 := hpb 1 one_ne_zero
    rw [zpow_one] at h1
    exact cocompact_elements_hyperbolic hΓ hfree hcc _ hB h1.1 h1.2
  -- the group package and the transfer to its last pair
  obtain ⟨first, γ', δ', hf, hgen, hrel, hnc', hΘγ', hΘδ'⟩ := s83sg_group_package hg Θ hΘs hΘk
  obtain ⟨u, hu⟩ := hΘs (w * gb ^ s₂)
  have hconjA := (s83sy_lift Θ hΘk (u⁻¹ * γ⁻¹ * u) (δ' ^ (-s₁))).1 (by
    rw [map_mul, map_mul, map_inv, map_inv, hu, hΘγ, map_zpow, hΘδ', ← hgb]
    exact hcX)
  have hconjB := (s83sy_lift Θ hΘk (u⁻¹ * δ⁻¹ * u) (γ' ^ (-s₃))).1 (by
    rw [map_mul, map_mul, map_inv, map_inv, hu, hΘδ, map_zpow, hΘγ', ← hga]
    exact hcY)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at hconjA hconjB
  obtain ⟨hcomm, htrEq⟩ := s83sy_transfer _ _ _ _ _ s₁ s₃ hs₁ hs₃ hconjA hconjB
  have hnc : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ * ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ ≠
      ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ :=
    fun h1 => hnc' (hcomm h1)
  -- [D], [L4], [L5]
  have hdisj := s83sg_disjoint_fixed hΓ hcc hA hB hAh hBh hnc
  have hsep := s83sg_link_sep hAh hBh hdisj ha hb hai hbi haγ hbδ (ha0.trans hb0.symm) hmeet hcross
  have htr := s83sg_sep_trace hAh hBh hdisj hsep
  rw [htrEq] at htr
  -- `δ'` is hyperbolic
  have hδ'1 : (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≠ 1 := fun h1 => by
    have h2 := (hΘk δ').2 (Or.inl h1)
    rw [hΘδ', ← hgb] at h2
    exact hb1 h2
  have hδ'2 : (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≠ -1 := fun h1 => by
    have h2 := (hΘk δ').2 (Or.inr h1)
    rw [hΘδ', ← hgb] at h2
    exact hb1 h2
  have hδh : IsHyperbolic (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    cocompact_elements_hyperbolic hΓ hfree hcc _ δ'.2 hδ'1 hδ'2
  have hδ4 : 4 < ((δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 + (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 2 := by
    have h2 : 2 < |(δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 + (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1| := hδh
    nlinarith [sq_abs ((δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 + (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1),
      abs_nonneg ((δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 + (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1)]
  exact ⟨first, γ', δ', hf, γ'.2, δ'.2, hgen, hrel, hδ4, htr⟩

theorem s83sg_target [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, Nonempty (StandardGenerators (conjGroup Γ₀ A) g) := by
  obtain ⟨first, γg, δg, hf, hγ, hδ, hgen, hrel, hhyp, htr⟩ := s83sg_system hg hS hp₀
  obtain ⟨A, h01, h10, hl, hfix, halt⟩ := s83sg_normalize γg δg hhyp htr
  exact ⟨A, s83sg_conj_system first γg δg hf hγ hδ hgen hrel A ⟨h01, h10, hl⟩ hfix halt⟩

/-- §27.1: the covering group of a closed surface of genus `g > 1` has a system of generators
satisfying (27.4) (lifted from a canonical system `α₁, β₁, …` of generators of `π₁`), and after a
suitable adjustment `p₀ ↦ p₀ ∘ ψ⁻¹` of the projection (conjugating `G₀` by `ψ`) a standard system
of generators exists.  (The fixed points of `γ_g` and `δ_g` alternate on `ℝ̂`, since `α_g`, `β_g` have
geometric intersection number `1`.) -/
theorem s83sg_exists_standardGenerators [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, Nonempty (StandardGenerators (conjGroup Γ₀ A) g) :=
  s83sg_target hg hS hp₀

section RelocatedS27


/-- §27.1: the covering group of a closed surface of genus `g > 1` has a system of generators
satisfying (27.4) (lifted from a canonical system `α₁, β₁, …` of generators of `π₁`), and after a
suitable adjustment `p₀ ↦ p₀ ∘ ψ⁻¹` of the projection (conjugating `G₀` by `ψ`) a standard system
of generators exists.  (The fixed points of `γ_g` and `δ_g` alternate on `ℝ̂`, since `α_g`, `β_g` have
geometric intersection number `1`.) -/
theorem exists_standardGenerators [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, Nonempty (StandardGenerators (conjGroup Γ₀ A) g) := by
  exact s83sg_exists_standardGenerators hg hS hp₀

end RelocatedS27

end LiZhongQC
