import LiZhongQC.Lemmas.F1OrdinarySupport

/-! F1 finite assembly (`ft1fas_assembly_of_exteriors`), conditional on the statements of the two
producers, which `F1Final` discharges by the accepted `ft1gb_periodic_exteriors` and
`ft1fas_end_normal_form`. No book theorem is used. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A pointwise alternative on `Fin N` gives one partition `Fin n ⊕ Fin m ≃ Fin N` with the
left alternative on the left indices and the right alternative on the right indices. -/
theorem ft1fin_split {N : ℕ} {P Q : Fin N → Prop} (hPQ : ∀ j, P j ∨ Q j) :
    ∃ (n m : ℕ) (e : (Fin n ⊕ Fin m) ≃ Fin N),
      (∀ i, P (e (Sum.inl i))) ∧ ∀ j, Q (e (Sum.inr j)) := by
  classical
  refine ⟨Fintype.card {j // P j}, Fintype.card {j // ¬ P j},
    (Equiv.sumCongr (Fintype.equivFin {j // P j}).symm
      (Fintype.equivFin {j // ¬ P j}).symm).trans (Equiv.sumCompl P), fun i => ?_, fun j => ?_⟩
  · first
      | exact ((Fintype.equivFin {j // P j}).symm i).2
      | (simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl];
          exact ((Fintype.equivFin {j // P j}).symm i).2)
  · first
      | exact (hPQ _).resolve_left ((Fintype.equivFin {j // ¬ P j}).symm j).2
      | (simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr];
          exact (hPQ _).resolve_left ((Fintype.equivFin {j // ¬ P j}).symm j).2)

/-- A set invariant under `h₀` is invariant under every signed power `±h₀ ^ k`, pointwise. -/
theorem ft1fin_signed_mem {W : Set UpperHalfPlane} {h₀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hinv : (fun τ : UpperHalfPlane => h₀ • τ) '' W = W)
    (hβ : ∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) (τ : UpperHalfPlane) :
    β • τ ∈ W ↔ τ ∈ W := by
  have hone : ∀ σ : UpperHalfPlane, h₀ • σ ∈ W ↔ σ ∈ W := by
    intro σ
    constructor
    · intro hσ
      rw [← hinv] at hσ
      obtain ⟨σ', hσ', heq⟩ := hσ
      have hσσ' : σ' = σ := (smul_left_cancel_iff h₀).1 heq
      rw [← hσσ']
      exact hσ'
    · intro hσ
      rw [← hinv]
      exact ⟨σ, hσ, rfl⟩
  have hpow : ∀ (k : ℤ) (σ : UpperHalfPlane), h₀ ^ k • σ ∈ W ↔ σ ∈ W := by
    intro k
    induction k using Int.induction_on with
    | zero => intro σ; rw [zpow_zero, one_smul]
    | succ k ih => intro σ; rw [zpow_add_one, mul_smul, ih, hone]
    | pred k ih => intro σ; rw [zpow_sub_one, mul_smul, ih, ← hone (h₀⁻¹ • σ), smul_inv_smul]
  obtain ⟨k, hk | hk⟩ := hβ
  · rw [hk]
    exact hpow k τ
  · rw [hk, s30l_neg_smul]
    exact hpow k τ

/-- Image form of `ft1fin_signed_mem`. -/
theorem ft1fin_signed_image {W : Set UpperHalfPlane} {h₀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hinv : (fun τ : UpperHalfPlane => h₀ • τ) '' W = W)
    (hβ : ∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) :
    (fun τ : UpperHalfPlane => β • τ) '' W = W := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (ft1fin_signed_mem hinv hβ σ).2 hσ
  · intro hτ
    refine ⟨β⁻¹ • τ, (ft1fin_signed_mem hinv hβ _).1 ?_, smul_inv_smul β τ⟩
    rwa [smul_inv_smul]

/-- **F1 finite assembly.** From the periodic-exterior producer `hB` (statement of
`ft1gb_periodic_exteriors`) and the end normal form `hNF` (statement of `ft1fas_end_normal_form`),
the coherent decomposition of `ft1fas_decomposition_with_ordinary`: one partition of the exteriors
into cusps and funnels, height-one horoballs, funnel sectors shrunk to the uniform gap against all
cusps, the compact core enlarged by the period residuals, and the full ordinary arcs. -/
theorem ft1fas_assembly_of_exteriors (hΓ : IsFuchsian Γ)
    (hB :
    (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    ∃ (N : ℕ) (C : Set UpperHalfPlane) (W : Fin N → Set UpperHalfPlane)
      (ρ : Fin N → ℝ → UpperHalfPlane)
      (h : Fin N → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      let U : Set UpperHalfPlane := ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C
      IsCompact C ∧ IsConnected U ∧ IsClosed U ∧
      (∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ Disjoint U (W j) ∧
        frontier (W j) = Set.range (ρ j)) ∧
      (∀ j, Topology.IsEmbedding (ρ j) ∧
        ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact ((ρ j) ⁻¹' L)) ∧
      (∀ j, h j ∈ Γ ∧ h j ≠ 1 ∧ h j ≠ -1 ∧
        (∀ t : ℝ, ρ j (t + 1) = h j • ρ j t) ∧
        (fun τ : UpperHalfPlane => h j • τ) '' W j = W j) ∧
      (∀ i j γ, γ ∈ Γ →
        (((fun τ : UpperHalfPlane => γ • τ) '' W i) ∩ W j).Nonempty →
        i = j ∧ ∃ k : ℤ, γ = h i ^ k ∨ γ = -h i ^ k) ∧
      Uᶜ = ⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' W j)
    (hNF : ∀
    (ρ : ℝ → UpperHalfPlane) (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L))
    (W : Set UpperHalfPlane) (hWo : IsOpen W) (hWc : IsConnected W)
    (hfront : frontier W = Set.range ρ)
    (h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hh₀ : h₀ ∈ Γ)
    (h1 : h₀ ≠ 1) (hm1 : h₀ ≠ -1)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = h₀ • ρ t)
    (hWinv : (fun τ : UpperHalfPlane => h₀ • τ) '' W = W)
    (hprec : ∀ γ ∈ Γ, ((fun τ : UpperHalfPlane => γ • τ) '' W ∩ W).Nonempty →
      ∃ k : ℤ, γ = h₀ ^ k ∨ γ = -h₀ ^ k),
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    (∃ (A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ Y : ℝ),
      π₀ ∈ Γ ∧ 0 < δ ∧ δ < Y ∧ 1 < Y ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) ↔
        (∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k)) ∧
      (∀ β ∈ Γ, (A⁻¹ * β * A) 1 0 = 0 → ∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k) ∧
      {τ : UpperHalfPlane | Y < τ.im} ⊆ (fun τ => A • τ) ⁻¹' W ∧
      (fun τ : UpperHalfPlane => A • τ) ⁻¹' W ⊆ {τ | δ < τ.im} ∧
      IsCompact ((fun τ : UpperHalfPlane => A • τ) ⁻¹' closure W ∩
        {τ | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ τ.im ≤ Y})) ∨
    (∃ (B h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ),
      h ∈ Γ ∧ 1 < lam ∧ 0 < θ ∧ θ < Real.pi / 2 ∧
      (∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * (τ : ℂ)) ∧
      (∀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) ↔
        (∃ k : ℤ, β = h ^ k ∨ β = -h ^ k)) ∧
      {τ : UpperHalfPlane | arg (τ : ℂ) < θ} ⊆ (fun τ => B • τ) ⁻¹' W ∧
      (fun τ : UpperHalfPlane => B • τ) ⁻¹' W ⊆ {τ | arg (τ : ℂ) < Real.pi - θ} ∧
      IsCompact ((fun τ : UpperHalfPlane => B • τ) ⁻¹' closure W ∩
        {τ | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ arg (τ : ℂ)}))) :
    (∀ γ ∈ Γ, γ = 1 ∨ γ = -1) ∨
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    ∃ (n m : ℕ) (C : Set UpperHalfPlane) (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (B h : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : Fin m → ℝ),
      IsCompact C ∧
      (∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ j, h j ∈ Γ ∧ 1 < lam j ∧ 0 < θ j ∧ θ j < π ∧
        ∀ τ : UpperHalfPlane, (((B j)⁻¹ • (h j • (B j • τ)) : UpperHalfPlane) : ℂ) = (lam j : ℂ) * (τ : ℂ)) ∧
      (∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
        i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k) ∧
      (∀ j j' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ j →
        arg (((B j')⁻¹ • (γ • (B j • τ)) : UpperHalfPlane) : ℂ) < θ j' →
        j = j' ∧ ∃ k : ℤ, γ = h j ^ k ∨ γ = -h j ^ k) ∧
      (∀ i j γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
        θ j ≤ arg (((B j)⁻¹ • (γ • (A i • τ)) : UpperHalfPlane) : ℂ)) ∧
      (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨ (∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) ∨
        ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j) ∧
      (∀ j (t : ℝ), 0 < t →
      mobiusSL (slRealToComplex (B j)) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ) ∧
      (∀ x : ExtPlane, x ∈ ordinarySet Γ →
      ∃ γ ∈ Γ, ∃ j : Fin m, ∃ t : ℝ, 0 < t ∧
        x = mobiusSL (slRealToComplex (γ * B j)) ((t : ℂ) : ExtPlane)) := by
  rcases hB with htriv | hpar | ⟨N, C, W, ρ, ψ, hBdata⟩
  · exact Or.inl htriv
  · exact Or.inr (Or.inl hpar)
  obtain ⟨hC, -, -, hW, hρ, hψ, hprec, hUc⟩ := hBdata
  refine Or.inr (or_iff_not_imp_left.2 fun hnE => ?_)
  -- Normal form of every exterior; the global elementary alternative is excluded by `hnE`.
  have hCF := fun j : Fin N => (hNF (ρ j) (hρ j).1 (hρ j).2 (W j) (hW j).1 (hW j).2.1
    (hW j).2.2.2 (ψ j) (hψ j).1 (hψ j).2.1 (hψ j).2.2.1 (hψ j).2.2.2.1 (hψ j).2.2.2.2
    (fun γ hγ hne => (hprec j j γ hγ hne).2)).resolve_left hnE
  -- One partition of the exteriors into cusps and funnels, kept throughout.
  obtain ⟨n, m, e, hcusp0, hfun0⟩ := ft1fin_split hCF
  beta_reduce at hcusp0 hfun0
  choose A π₀ δ Y hπ hδ _ hY1 htr hiffc hstab hhigh hlow hRc using hcusp0
  choose B g lam θ₀ hg hlam hθ0 hθ2 hsc hifff hsect hupper hRf using hfun0
  have hθπ : ∀ j, θ₀ j < Real.pi := fun j => (hθ2 j).trans (half_lt_self Real.pi_pos)
  -- Height-one cusps.
  have hpc := ft1fas_height_one_cusp_separation hΓ (fun i => W (e (Sum.inl i))) A π₀ Y
    (fun i => ⟨hπ i, htr i⟩) hhigh hstab
    (fun i i' γ hγ hne => by
      obtain ⟨heq, k, hk⟩ := hprec _ _ γ hγ hne
      exact ⟨Sum.inl_injective (e.injective heq), (hiffc i γ).1 ⟨k, hk⟩⟩)
  -- Funnel sectors inside the exteriors are precisely invariant.
  have hpf0 : ∀ j j' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ₀ j →
      arg (((B j')⁻¹ • (γ • (B j • τ)) : UpperHalfPlane) : ℂ) < θ₀ j' →
      j = j' ∧ ∃ k : ℤ, γ = g j ^ k ∨ γ = -g j ^ k := by
    intro j j' γ hγ τ h1 h2
    have hm1 : B j • τ ∈ W (e (Sum.inr j)) :=
      hsect j (show τ ∈ {τ : UpperHalfPlane | arg (τ : ℂ) < θ₀ j} from h1)
    have hm2 : B j' • ((B j')⁻¹ • (γ • (B j • τ))) ∈ W (e (Sum.inr j')) :=
      hsect j' (show (B j')⁻¹ • (γ • (B j • τ)) ∈ {τ : UpperHalfPlane | arg (τ : ℂ) < θ₀ j'} from h2)
    rw [smul_inv_smul] at hm2
    obtain ⟨heq, k, hk⟩ := hprec _ _ γ hγ ⟨γ • (B j • τ), ⟨B j • τ, hm1, rfl⟩, hm2⟩
    exact ⟨Sum.inr_injective (e.injective heq), (hifff j γ).1 ⟨k, hk⟩⟩
  -- Full ordinary arcs and the uniform angle gap against all cusps.
  have harc : ∀ j (t : ℝ), 0 < t →
      mobiusSL (slRealToComplex (B j)) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ := fun j =>
    ft1fas_funnel_arc_ordinary hΓ (B j) (g j) (lam j) (θ₀ j) (hg j) (hlam j) (hθ0 j) (hθπ j)
      (hsc j) (fun γ hγ τ h1 h2 => (hpf0 j j γ hγ τ h1 h2).2)
  have hgap := fun j => ft1fas_funnel_cusp_angle_gap hΓ A π₀ (fun i => ⟨hπ i, htr i⟩) hpc
    (B j) (g j) (lam j) (θ₀ j) (hg j) (hlam j) (hθ0 j) (hθπ j) (hsc j) (harc j)
  choose ε hε0 hεθ hεgap using hgap
  -- Compact core: the original core plus the period residuals of every end.
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : Set UpperHalfPlane, C₀ =
      (C ∪ ⋃ i, (fun τ : UpperHalfPlane => A i • τ) ''
        ((fun τ : UpperHalfPlane => A i • τ) ⁻¹' closure (W (e (Sum.inl i))) ∩
          {τ : UpperHalfPlane | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ τ.im ≤ Y i})) ∪
      ⋃ j, (fun τ : UpperHalfPlane => B j • τ) ''
        ((fun τ : UpperHalfPlane => B j • τ) ⁻¹' closure (W (e (Sum.inr j))) ∩
          {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam j ∧ θ₀ j ≤ arg (τ : ℂ)}) :=
    ⟨_, rfl⟩
  have hC₀ : IsCompact C₀ := by
    rw [hC₀def]
    exact (hC.union (isCompact_iUnion fun i => (hRc i).image (continuous_const_smul (A i)))).union
      (isCompact_iUnion fun j => (hRf j).image (continuous_const_smul (B j)))
  have hcover0 : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C₀ ∨
      (∃ i, Y i < ((A i)⁻¹ • (γ • τ)).im) ∨
      ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ₀ j := by
    intro τ
    by_cases hτ : τ ∈ ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C
    · obtain ⟨γ, hγ, c, hc, hcτ⟩ := mem_iUnion₂.1 hτ
      have hγτ : γ⁻¹ • τ = c := by rw [← hcτ]; exact inv_smul_smul γ c
      refine ⟨γ⁻¹, Γ.inv_mem hγ, Or.inl ?_⟩
      rw [hC₀def, hγτ]
      exact mem_union_left _ (mem_union_left _ hc)
    have hτ' := (Set.ext_iff.1 hUc τ).1 hτ
    obtain ⟨γ, hγ, hk⟩ := mem_iUnion₂.1 hτ'
    obtain ⟨k, σ, hσ, hστ⟩ := mem_iUnion.1 hk
    have hστ' : γ⁻¹ • τ = σ := by rw [← hστ]; exact inv_smul_smul γ σ
    obtain ⟨s, rfl⟩ := e.surjective k
    rcases s with i | j
    · -- A cusp end: translate into the strip `0 ≤ re ≤ 1` by a power of `π₀ i`.
      obtain ⟨w, hw⟩ : ∃ w : UpperHalfPlane, w = (A i)⁻¹ • σ := ⟨_, rfl⟩
      have hAw : A i • w = σ := by rw [hw, smul_inv_smul]
      obtain ⟨w', hw'⟩ : ∃ w' : UpperHalfPlane, w' = ((-⌊w.re⌋ : ℤ) : ℝ) +ᵥ w := ⟨_, rfl⟩
      have hmove := ft1e_zpow_smul (htr i) (-⌊w.re⌋) w
      rw [hAw, ← hw'] at hmove
      have hσ'W : π₀ i ^ (-⌊w.re⌋) • σ ∈ W (e (Sum.inl i)) :=
        (ft1fin_signed_mem (hψ (e (Sum.inl i))).2.2.2.2
          ((hiffc i _).2 ⟨-⌊w.re⌋, Or.inl rfl⟩) σ).2 hσ
      have hgτ : (π₀ i ^ (-⌊w.re⌋) * γ⁻¹) • τ = A i • w' := by rw [mul_smul, hστ', hmove]
      refine ⟨π₀ i ^ (-⌊w.re⌋) * γ⁻¹, Γ.mul_mem (Γ.zpow_mem (hπ i) (-⌊w.re⌋)) (Γ.inv_mem hγ), ?_⟩
      rw [hgτ]
      by_cases hYw : Y i < w'.im
      · exact Or.inr (Or.inl ⟨i, by rwa [inv_smul_smul]⟩)
      · refine Or.inl ?_
        rw [hC₀def]
        refine mem_union_left _ (mem_union_right _ (mem_iUnion.2 ⟨i, w', ⟨?_, ?_, ?_, le_of_not_gt hYw⟩, rfl⟩))
        · exact show A i • w' ∈ closure (W (e (Sum.inl i))) from
            subset_closure (by rw [← hmove]; exact hσ'W)
        · rw [hw', UpperHalfPlane.vadd_re]
          push_cast
          linarith [Int.floor_le w.re]
        · rw [hw', UpperHalfPlane.vadd_re]
          push_cast
          linarith [Int.lt_floor_add_one w.re]
    · -- A funnel end: scale into the annulus `1 ≤ |τ| ≤ lam` by a power of `g j`.
      obtain ⟨w, hw⟩ : ∃ w : UpperHalfPlane, w = (B j)⁻¹ • σ := ⟨_, rfl⟩
      have hBw : B j • w = σ := by rw [hw, smul_inv_smul]
      obtain ⟨k, hk0, hk1⟩ := ft1g_scale_to_annulus (lam j) (hlam j) w
      obtain ⟨w', hw'⟩ : ∃ w' : UpperHalfPlane, w' = (B j)⁻¹ • (g j ^ k • (B j • w)) :=
        ⟨_, rfl⟩
      have hw'c : (w' : ℂ) = (lam j : ℂ) ^ k * (w : ℂ) := by
        rw [hw']
        exact ft4a_scale_zpow (hsc j) k w
      have hBw' : B j • w' = g j ^ k • σ := by
        rw [hw', smul_inv_smul, hBw]
      have hσ'W : g j ^ k • σ ∈ W (e (Sum.inr j)) :=
        (ft1fin_signed_mem (hψ (e (Sum.inr j))).2.2.2.2 ((hifff j _).2 ⟨k, Or.inl rfl⟩) σ).2 hσ
      have hgτ : (g j ^ k * γ⁻¹) • τ = B j • w' := by rw [mul_smul, hστ', hBw']
      refine ⟨g j ^ k * γ⁻¹, Γ.mul_mem (Γ.zpow_mem (hg j) k) (Γ.inv_mem hγ), ?_⟩
      rw [hgτ]
      by_cases harg : arg (w' : ℂ) < θ₀ j
      · exact Or.inr (Or.inr ⟨j, by rwa [inv_smul_smul]⟩)
      · refine Or.inl ?_
        rw [hC₀def]
        refine mem_union_right _ (mem_iUnion.2 ⟨j, w', ⟨?_, ?_, ?_, le_of_not_gt harg⟩, rfl⟩)
        · exact show B j • w' ∈ closure (W (e (Sum.inr j))) from
            subset_closure (by rw [hBw']; exact hσ'W)
        · rw [hw'c]
          exact hk0
        · rw [hw'c]
          exact hk1
  -- Shrink the funnel sectors to the uniform gap; the horoballs are already at height one.
  obtain ⟨hCc, hcov⟩ := ft1fas_cover_after_shrinking C₀ hC₀ A Y B g lam θ₀ ε hY1
    (fun j => ⟨hg j, hlam j, hε0 j, hεθ j, hθπ j, hsc j⟩) hcover0
  refine ⟨n, m, _, A, π₀, B, g, lam, ε, hCc, fun i => ⟨hπ i, htr i⟩,
    fun j => ⟨hg j, hlam j, hε0 j, (hεθ j).trans_lt (hθπ j), hsc j⟩, hpc, ?_, ?_, hcov, harc, ?_⟩
  · intro j j' γ hγ τ h1 h2
    exact hpf0 j j' γ hγ τ (h1.trans_le (hεθ j)) (h2.trans_le (hεθ j'))
  · intro i j γ hγ τ hτ
    exact hεgap j i γ hγ τ hτ
  · exact ft1fas_ordinary_arc_coverage hΓ C hC W e (fun j => (hW j).1)
      (fun i j γ hγ hne => by
        obtain ⟨rfl, k, hk⟩ := hprec i j γ hγ hne
        exact ⟨rfl, ft1fin_signed_image (hψ _).2.2.2.2 ⟨k, hk⟩⟩)
      hUc A δ B θ₀ (fun i => ⟨hδ i, hlow i⟩) (fun j => ⟨hθ0 j, hθπ j, hupper j⟩)
      (fun i => ft1fas_parabolic_endpoint_limit hΓ (A i) (π₀ i) (hπ i) (htr i))
      (fun j => ft1fas_hyperbolic_endpoints_limit hΓ (B j) (g j) (lam j) (hg j) (hlam j) (hsc j))

end LiZhongQC
