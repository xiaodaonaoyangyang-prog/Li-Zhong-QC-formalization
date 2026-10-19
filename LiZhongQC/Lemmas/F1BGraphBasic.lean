import LiZhongQC.Lemmas.FoundationQuotient

/-! B2 basic constructions, source-only delivery 001.
Four complete source proofs; no proposed-interface dependency. Root owns compilation. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

-- Source: F1BSphereCircle.lean
/-- The central hyperbolic sphere has its actual positively oriented Euclidean
circle model. The image lies in the upper half plane by the metric centre lemma. -/
theorem ft1gb_sphere_circle_model (R : ℝ) (hR : 0 < R) :
    ∃ e : Circle → UpperHalfPlane,
      Topology.IsEmbedding e ∧ Set.range e = sphere UpperHalfPlane.I R ∧
      ∀ z : Circle, (e z : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
        (Real.sinh R : ℂ) * (z : ℂ) := by
  let c : ℂ := (UpperHalfPlane.I.center R : ℂ)
  let r : ℝ := Real.sinh R
  have hr : 0 < r := Real.sinh_pos_iff.2 hR
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let A : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) hrC).trans (Homeomorph.addLeft c)
  have hA (z : ℂ) : A z = c + (r : ℂ) * z := rfl
  have hdist (z : Circle) : dist (A (z : ℂ)) c = r := by
    rw [hA, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
  have hpos (z : Circle) : 0 < (A (z : ℂ)).im := by
    apply UpperHalfPlane.im_pos_of_dist_center_le (z := UpperHalfPlane.I) (r := R)
    change dist (A (z : ℂ)) c ≤ UpperHalfPlane.I.im * r
    rw [UpperHalfPlane.I_im, one_mul, hdist]
  let e : Circle → UpperHalfPlane := fun z => ⟨A (z : ℂ), hpos z⟩
  have hecoe (z : Circle) : (e z : ℂ) = A (z : ℂ) := rfl
  have hemb : Topology.IsEmbedding e := by
    apply UpperHalfPlane.isEmbedding_coe.of_comp_iff.1
    exact A.isEmbedding.comp (show Topology.IsEmbedding ((↑) : Circle → ℂ) from
      Topology.IsEmbedding.subtypeVal)
  refine ⟨e, hemb, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨z, rfl⟩
      apply UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.2
      change dist (e z : ℂ) c = UpperHalfPlane.I.im * r
      rw [hecoe, hdist, UpperHalfPlane.I_im, one_mul]
    · intro hp
      have hpdist : dist (p : ℂ) c = r := by
        simpa only [UpperHalfPlane.I_im, one_mul] using
          UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hp
      have hnorm : ‖((p : ℂ) - c) / (r : ℂ)‖ = 1 := by
        rw [norm_div, ← dist_eq_norm, hpdist, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
      let z : Circle := ⟨((p : ℂ) - c) / (r : ℂ), by
        change dist (((p : ℂ) - c) / (r : ℂ)) 0 = 1
        rwa [dist_zero_right]⟩
      refine ⟨z, ?_⟩
      apply UpperHalfPlane.ext
      rw [hecoe, hA]
      change c + (r : ℂ) * (((p : ℂ) - c) / (r : ℂ)) = (p : ℂ)
      field_simp [hrC]
      <;> ring
  · intro z
    exact hA z

-- Source: F1BGraphAlgebra.lean
/-- Away from the actual cut set, a translated central-circle arc can meet a
central-circle arc only through a central element. The geometric input is cut
avoidance, not a pre-assumed orbit-disjointness conclusion. -/
theorem ft1gb_arc_interior_rigidity (hfree : ActsFreely Γ) (R : ℝ)
    (V : Finset UpperHalfPlane)
    (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hsphere : ∀ i, Set.range (a i) ⊆ sphere UpperHalfPlane.I R)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s) :
    ∀ i j γ, γ ∈ Γ → ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∀ s : unitInterval, γ • a i t = a j s →
        i = j ∧ (γ = 1 ∨ γ = -1) ∧ t = s := by
  intro i j γ hγ t ht0 ht1 s heq
  have hfix : γ • UpperHalfPlane.I = UpperHalfPlane.I := by
    by_contra hne
    have hinvne : γ⁻¹ • UpperHalfPlane.I ≠ UpperHalfPlane.I := by
      intro h
      have hh := congrArg (fun x : UpperHalfPlane => γ • x) h
      simp only [smul_inv_smul] at hh
      exact hne hh.symm
    have hd : dist (a i t) (γ⁻¹ • UpperHalfPlane.I) = R := by
      have hiso := (isometry_smul UpperHalfPlane γ).dist_eq
        (a i t) (γ⁻¹ • UpperHalfPlane.I)
      rw [heq, smul_inv_smul] at hiso
      exact hiso.symm.trans (hsphere j ⟨s, rfl⟩)
    exact havoid i t ht0 ht1 ((hV (a i t)).2
      ⟨hsphere i ⟨t, rfl⟩, γ⁻¹, Γ.inv_mem hγ, hinvne, hd⟩)
  have hcentral := hfree γ hγ UpperHalfPlane.I hfix
  have heq' : a i t = a j s := by
    rcases hcentral with h | h
    · simpa only [h, one_smul] using heq
    · simpa only [h, ft0_neg_one_smul] using heq
  obtain ⟨hij, hts⟩ := hsep i j t s ht0 ht1 heq'
  exact ⟨hij, hcentral, hts⟩

/-- Extract a genuine successor permutation from unique outgoing incidence and
existence of incoming incidence. The finite bijection step contains no topology;
the two incidence premises must be supplied by the oriented endpoint producer. -/
theorem ft1gb_successor_of_incidence (n : ℕ)
    (a : Fin n → unitInterval → UpperHalfPlane)
    (hout : ∀ i, ∃ j γ, γ ∈ Γ ∧ a i 1 = γ • a j 0 ∧
      ∀ k δ, δ ∈ Γ → a i 1 = δ • a k 0 → k = j ∧ (δ = γ ∨ δ = -γ))
    (hin : ∀ j, ∃ i γ, γ ∈ Γ ∧ a i 1 = γ • a j 0) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ i, d i ∈ Γ ∧ a i 1 = d i • a (σ i) 0) ∧
      (∀ i j γ, γ ∈ Γ → a i 1 = γ • a j 0 →
        j = σ i ∧ (γ = d i ∨ γ = -d i)) := by
  classical
  choose next d hd he huniq using hout
  have hsurj : Function.Surjective next := by
    intro j
    obtain ⟨i, γ, hγ, hi⟩ := hin j
    exact ⟨i, (huniq i j γ hγ hi).1.symm⟩
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective next ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨σ, d, ?_, ?_⟩
  · intro i
    exact ⟨hd i, he i⟩
  · intro i j γ hγ hi
    exact huniq i j γ hγ hi

/-- Once the central exposed frontier is covered by selected arcs, its translates
cover the full frontier. An active orbit sphere supplies the translating element. -/
theorem ft1gb_translate_central_frontier (R : ℝ) {U : Set UpperHalfPlane}
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hactive : ∀ p ∈ frontier U, ∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (ha : ∀ i, Set.range (a i) ⊆ frontier U)
    (hcover : sphere UpperHalfPlane.I R ∩ frontier U = ⋃ i, Set.range (a i)) :
    frontier U = ⋃ γ ∈ Γ, ⋃ i,
      (fun τ : UpperHalfPlane => γ • τ) '' Set.range (a i) := by
  have hfr (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ) :
      (fun τ : UpperHalfPlane => γ • τ) '' frontier U = frontier U := by
    calc
      (fun τ : UpperHalfPlane => γ • τ) '' frontier U =
          frontier ((fun τ : UpperHalfPlane => γ • τ) '' U) :=
        (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_frontier U
      _ = frontier U := by rw [hUi γ hγ]
  ext p
  constructor
  · intro hp
    obtain ⟨γ, hγ, hdist⟩ := hactive p hp
    have hqF : γ⁻¹ • p ∈ frontier U := by
      rw [← hfr γ⁻¹ (Γ.inv_mem hγ)]
      exact ⟨p, hp, rfl⟩
    have hqS : γ⁻¹ • p ∈ sphere UpperHalfPlane.I R := by
      have hiso := (isometry_smul UpperHalfPlane γ).dist_eq
        (γ⁻¹ • p) UpperHalfPlane.I
      rw [smul_inv_smul] at hiso
      exact hiso.symm.trans hdist
    have hq : γ⁻¹ • p ∈ ⋃ i, Set.range (a i) := hcover ▸ ⟨hqS, hqF⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hq
    exact Set.mem_iUnion.2 ⟨γ, Set.mem_iUnion.2 ⟨hγ,
      Set.mem_iUnion.2 ⟨i, ⟨γ⁻¹ • p, hi, smul_inv_smul γ p⟩⟩⟩⟩
  · intro hp
    obtain ⟨γ, hp⟩ := Set.mem_iUnion.1 hp
    obtain ⟨hγ, hp⟩ := Set.mem_iUnion.1 hp
    obtain ⟨i, q, hq, hqp⟩ := Set.mem_iUnion.1 hp
    rw [← hfr γ hγ]
    exact ⟨q, ha i hq, hqp⟩

end LiZhongQC
