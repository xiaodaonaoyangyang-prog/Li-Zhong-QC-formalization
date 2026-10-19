import LiZhongQC.Lemmas.FoundationQuotient

/-!
Source-only A1 proof package. The public producer statement is frozen in
F1ABGeometryIface.lean (645946a37a0695736ae0c2a1e1bf430b).
No compiler run or axiom acceptance is claimed. No finite-sided polygon is assumed.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Compact test sets meet only finitely many translates of a compact set. -/
theorem ft1ga_compact_test_finite (hΓ : IsFuchsian Γ)
    (K L : Set UpperHalfPlane) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
      ((fun τ : UpperHalfPlane => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  refine (hΓ (K ∪ L) (hK.union hL)).subset ?_
  rintro γ ⟨hγ, x, ⟨y, hy, rfl⟩, hx⟩
  exact ⟨hγ, γ • y, ⟨y, Or.inl hy, rfl⟩, Or.inr hx⟩

/-- A compact set has closed orbit saturation under a Fuchsian group. -/
theorem ft1ga_compact_saturation_closed (hΓ : IsFuchsian Γ)
    (K : Set UpperHalfPlane) (hK : IsCompact K) :
    IsClosed (⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' K) := by
  let f : Γ → Set UpperHalfPlane := fun γ => (fun τ : UpperHalfPlane => γ.val • τ) '' K
  have hlocal : LocallyFinite f := by
    intro x
    refine ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩
    have hfinite := ft1ga_compact_test_finite hΓ K (closedBall x 1) hK (isCompact_closedBall x 1)
    have hp := hfinite.preimage (Subtype.val_injective.injOn :
      Set.InjOn (Subtype.val : Γ → Matrix.SpecialLinearGroup (Fin 2) ℝ) _)
    have heq : {i : Γ | (f i ∩ closedBall x 1).Nonempty} =
        (Subtype.val : Γ → Matrix.SpecialLinearGroup (Fin 2) ℝ) ⁻¹'
          {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
            ((fun τ : UpperHalfPlane => γ • τ) '' K ∩ closedBall x 1).Nonempty} := by
      ext i
      change ((fun τ : UpperHalfPlane => i.val • τ) '' K ∩ closedBall x 1).Nonempty ↔
        i.val ∈ Γ ∧ ((fun τ : UpperHalfPlane => i.val • τ) '' K ∩ closedBall x 1).Nonempty
      exact ⟨fun hi => ⟨i.property, hi⟩, fun hi => hi.2⟩
    rw [heq]
    exact hp
  have hclosed : IsClosed (⋃ γ : Γ, f γ) := hlocal.isClosed_iUnion fun γ =>
    (hK.image (continuous_const_smul γ.val)).isClosed
  have heq : (⋃ γ : Γ, f γ) = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' K := by
    ext x
    simp only [mem_iUnion, f]
    constructor
    · rintro ⟨γ, hx⟩
      exact ⟨γ.val, γ.property, hx⟩
    · rintro ⟨γ, hγ, hx⟩
      exact ⟨⟨γ, hγ⟩, hx⟩
  rwa [heq] at hclosed

/-- Hyperbolic closed balls are connected, via their Euclidean closed-disc image. -/
theorem ft1ga_closedBall_connected (o : UpperHalfPlane) (R : ℝ) (hR : 0 ≤ R) :
    IsConnected (closedBall o R) := by
  refine ⟨⟨o, mem_closedBall_self hR⟩, ?_⟩
  apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
  rw [UpperHalfPlane.image_coe_closedBall]
  exact Metric.isPreconnected_closedBall

/-- A finitely generated Fuchsian group admits an arbitrarily large compact ball whose
orbit saturation is closed and connected. Local finiteness is stated for arbitrary compact
test sets, including multiplicity from the two possible signs in SL(2,R). -/
theorem ft1ga_connected_ball_saturation (hΓ : IsFuchsian Γ) (hfg : Γ.FG)
    (R₀ : ℝ) :
    ∃ R₁ : ℝ, R₀ < R₁ ∧ 0 < R₁ ∧ ∀ R : ℝ, R₁ < R →
      let K : Set UpperHalfPlane := closedBall UpperHalfPlane.I R
      let U : Set UpperHalfPlane := ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' K
      IsCompact K ∧ IsConnected U ∧ IsClosed U ∧
      (∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U) ∧
      (∀ L : Set UpperHalfPlane, IsCompact L →
        {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
          ((fun τ : UpperHalfPlane => γ • τ) '' K ∩ L).Nonempty}.Finite) := by
  classical
  -- Finite group generation also gives finite monoid generation; inverses are included
  -- in that finite set, so the connected intersection-chain induction has no inverse case.
  obtain ⟨S, hS, hSfin⟩ := (Submonoid.fg_iff Γ.toSubmonoid).1
    ((Subgroup.fg_iff_submonoid_fg Γ).1 hfg)
  obtain ⟨M, hM⟩ := (hSfin.image (fun γ => dist (γ • UpperHalfPlane.I) UpperHalfPlane.I)).bddAbove
  let R₁ : ℝ := max R₀ (max M 0) + 1
  have hR₀ : R₀ < R₁ := by
    have := le_max_left R₀ (max M 0)
    dsimp only [R₁]
    linarith
  have hR₁ : 0 < R₁ := by
    have h0 := le_max_right M (0 : ℝ)
    have h1 := le_max_right R₀ (max M 0)
    dsimp only [R₁]
    linarith
  refine ⟨R₁, hR₀, hR₁, ?_⟩
  intro R hR
  let K : Set UpperHalfPlane := closedBall UpperHalfPlane.I R
  let f : Matrix.SpecialLinearGroup (Fin 2) ℝ → Set UpperHalfPlane :=
    fun γ => (fun τ : UpperHalfPlane => γ • τ) '' K
  let U : Set UpperHalfPlane := ⋃ γ ∈ Γ, f γ
  change IsCompact K ∧ IsConnected U ∧ IsClosed U ∧
    (∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U) ∧
    (∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧ (f γ ∩ L).Nonempty}.Finite)
  have hRp : 0 < R := hR₁.trans hR
  have hoK : UpperHalfPlane.I ∈ K := mem_closedBall_self hRp.le
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKC : IsConnected K := ft1ga_closedBall_connected _ _ hRp.le
  have hSK : ∀ s ∈ S, s • UpperHalfPlane.I ∈ K := by
    intro s hs
    have hb := hM ⟨s, hs, rfl⟩
    have h1 := le_max_left M (0 : ℝ)
    have h2 := le_max_right R₀ (max M 0)
    change dist (s • UpperHalfPlane.I) UpperHalfPlane.I ≤ R
    dsimp only [R₁] at hR
    linarith
  let rel : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ → Prop :=
    fun a b => (f a ∩ f b).Nonempty ∧ a ∈ Γ
  have hchains : ∀ γ, γ ∈ Submonoid.closure S → ∀ δ ∈ Γ,
      Relation.ReflTransGen rel δ (δ * γ) := by
    intro γ hγ
    induction hγ using Submonoid.closure_induction with
    | mem s hs =>
      intro δ hδ
      apply Relation.ReflTransGen.single
      refine ⟨⟨(δ * s) • UpperHalfPlane.I, ?_, ?_⟩, hδ⟩
      · exact ⟨s • UpperHalfPlane.I, hSK s hs, by rw [mul_smul]⟩
      · exact ⟨UpperHalfPlane.I, hoK, rfl⟩
    | one =>
      intro δ hδ
      simpa only [mul_one] using (Relation.ReflTransGen.refl : Relation.ReflTransGen rel δ δ)
    | mul a b ha hb iha ihb =>
      intro δ hδ
      have haΓ : a ∈ Γ := by
        change a ∈ Γ.toSubmonoid
        rwa [← hS]
      simpa only [mul_assoc] using (iha δ hδ).trans (ihb (δ * a) (Γ.mul_mem hδ haΓ))
  have hUC : IsConnected U := by
    refine IsConnected.biUnion_of_reflTransGen ⟨1, Γ.one_mem⟩
      (fun γ _ => hKC.image _ (continuous_const_smul γ).continuousOn) ?_
    intro γ hγ δ hδ
    have hmem : γ⁻¹ * δ ∈ Submonoid.closure S := by
      rw [hS]
      exact Γ.mul_mem (Γ.inv_mem hγ) hδ
    have hchain := hchains (γ⁻¹ * δ) hmem γ hγ
    have hchain' : Relation.ReflTransGen
        (fun i j : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
          (f i ∩ f j).Nonempty ∧ i ∈ (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)))
        γ (γ * (γ⁻¹ * δ)) :=
      Relation.ReflTransGen.mono (r := rel) (fun _ _ hh => ⟨hh.1, hh.2⟩) _ _ hchain
    simpa only [mul_inv_cancel_left] using hchain' 
  refine ⟨hK, hUC, ft1ga_compact_saturation_closed hΓ K hK, ?_, ?_⟩
  · intro γ hγ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨δ, hδ, z, hz, rfl⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion₂.2 ⟨γ * δ, Γ.mul_mem hγ hδ, z, hz, by
        change (γ * δ) • z = γ • (δ • z)
        rw [mul_smul]⟩
    · intro hx
      obtain ⟨δ, hδ, z, hz, rfl⟩ := mem_iUnion₂.1 hx
      refine ⟨(γ⁻¹ * δ) • z, mem_iUnion₂.2 ⟨γ⁻¹ * δ, Γ.mul_mem (Γ.inv_mem hγ) hδ,
        z, hz, rfl⟩, ?_⟩
      change γ • ((γ⁻¹ * δ) • z) = δ • z
      rw [mul_smul, smul_inv_smul]
  · intro L hL
    exact ft1ga_compact_test_finite hΓ K L hK hL

end LiZhongQC
