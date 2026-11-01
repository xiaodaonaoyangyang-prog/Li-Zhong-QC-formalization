import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Lemmas.RingCharacterization
import LiZhongQC.Lemmas.LocalWinding

/-!
# Quasiconformal maps in homotopy classes of genus `0` and `1` (`s24q_`, for §24.2)

Genus `1`: the torus model from `thm22_3_classification` (`s24q_torus_cover`), the orientation bridge
`s24q_torus_det_pos` and the affine representative (`s24q_torus_qc`).  Genus `0`: the sphere model from
`RiemannDynamics.uniformization_trichotomy` (`s24q_sphere_model`), the degree-one bridge
`s24q_sphere_homotopic_mobius` and the Möbius representative (`s24q_genus_zero_of_model`).  Orientation is the
unfolded `IsOrientationPreservingRS` of S24.  Used by `exists_qc_in_homotopy_class` (S24).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-- `surfaceGroup 1` is commutative and infinite. -/
theorem s24q_tc_surfaceGroup_one :
    (∀ x y : surfaceGroup 1, x * y = y * x) ∧ Infinite (surfaceGroup 1) := by
  classical
  let a : surfaceGroup 1 := PresentedGroup.of (Sum.inl 0)
  let b : surfaceGroup 1 := PresentedGroup.of (Sum.inr 0)
  have hrel : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h := PresentedGroup.one_of_mem (rels := ({(List.ofFn fun i : Fin 1 =>
      FreeGroup.of (Sum.inl i : Fin 1 ⊕ Fin 1) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
      Set (FreeGroup (Fin 1 ⊕ Fin 1)))) (x := (List.ofFn fun i : Fin 1 =>
      FreeGroup.of (Sum.inl i : Fin 1 ⊕ Fin 1) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod) rfl
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, map_mul, map_inv] at h
    exact h
  have hab : Commute a b := by
    have := congrArg (fun t => t * b * a) hrel
    have h2 : a * b = b * a := by
      simp only [one_mul] at this
      have : a * b * a⁻¹ * b⁻¹ * b * a = 1 * b * a := by rw [hrel]
      simpa [mul_assoc] using this
    exact h2
  have hgen : Subgroup.closure (Set.range (PresentedGroup.of : (Fin 1 ⊕ Fin 1) → surfaceGroup 1)) = ⊤ :=
    PresentedGroup.closure_range_of _
  have hcomm : ∀ x y : surfaceGroup 1, Commute x y := by
    intro x y
    have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : (Fin 1 ⊕ Fin 1) → surfaceGroup 1)) := by
      rw [hgen]; trivial
    have hy : y ∈ Subgroup.closure (Set.range (PresentedGroup.of : (Fin 1 ⊕ Fin 1) → surfaceGroup 1)) := by
      rw [hgen]; trivial
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      rcases i with i | i <;> rcases j with j | j
      · have : i = j := Subsingleton.elim _ _
        subst this; exact Commute.refl _
      · have : i = 0 := Subsingleton.elim _ _
        have : j = 0 := Subsingleton.elim _ _
        subst_vars; exact hab
      · have : i = 0 := Subsingleton.elim _ _
        have : j = 0 := Subsingleton.elim _ _
        subst_vars; exact hab.symm
      · have : i = j := Subsingleton.elim _ _
        subst this; exact Commute.refl _
    · intro x _; exact Commute.one_left x
    · intro x _; exact Commute.one_right x
    · intro x y z _ _ _ h1 h2; exact h1.mul_left h2
    · intro y z x _ _ _ h1 h2; exact h1.mul_right h2
    · intro x y _ _ h; exact h.inv_left
    · intro x y _ _ h; exact h.inv_right
  refine ⟨fun x y => (hcomm x y).eq, ?_⟩
  let f : (Fin 1 ⊕ Fin 1) → Multiplicative ℤ := Sum.elim (fun _ => Multiplicative.ofAdd 1) (fun _ => 1)
  have hf : ∀ r ∈ ({(List.ofFn fun i : Fin 1 =>
      FreeGroup.of (Sum.inl i : Fin 1 ⊕ Fin 1) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
      Set (FreeGroup (Fin 1 ⊕ Fin 1))), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    simp [List.ofFn_succ, f]
  let φ : surfaceGroup 1 →* Multiplicative ℤ := PresentedGroup.toGroup hf
  have hφ : Function.Surjective φ := by
    intro n
    refine ⟨a ^ (Multiplicative.toAdd n), ?_⟩
    have ha : φ a = Multiplicative.ofAdd 1 := PresentedGroup.toGroup.of hf
    rw [map_zpow, ha]
    apply Multiplicative.toAdd.injective
    simp
  exact Infinite.of_surjective φ hφ

/-- A compact set of `ℍ` surjecting onto a compact quotient of `ℍ` through an open map. -/
theorem s24q_tc_compact_cover {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {p : UpperHalfPlane → S} (ho : IsOpenMap p) (hs : Function.Surjective p) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ x : S, ∃ k ∈ K, p k = x := by
  classical
  choose z hz using hs
  have hN : ∀ x : S, ∃ N : Set UpperHalfPlane, IsCompact N ∧ N ∈ 𝓝 (z x) :=
    fun x => exists_compact_mem_nhds (z x)
  choose N hNc hNn using hN
  have hU : ∀ x : S, p '' N x ∈ 𝓝 x := fun x => by
    have := ho.image_mem_nhds (hNn x)
    rwa [hz x] at this
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => p '' N x) hU
  refine ⟨⋃ x ∈ t, N x, t.isCompact_biUnion fun x _ => hNc x, fun y => ?_⟩
  have hy : y ∈ ⋃ x ∈ t, p '' N x := by rw [ht]; trivial
  simp only [mem_iUnion] at hy
  obtain ⟨x, hxt, k, hk, rfl⟩ := hy
  exact ⟨k, mem_iUnion₂.mpr ⟨x, hxt, hk⟩, rfl⟩

/-- A family of pairwise commuting isometries of `ℍ` acting transitively on the fibres of a cocompact
quotient map consists of `±1` only. -/
theorem s24q_tc_geom {S : Type*} [TopologicalSpace S] [CompactSpace S] {p : UpperHalfPlane → S}
    (ho : IsOpenMap p) (hs : Function.Surjective p)
    (G : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hcomm : ∀ m ∈ G, ∀ n ∈ G, ∀ z : UpperHalfPlane, m • n • z = n • m • z)
    (htrans : ∀ z w, p z = p w → ∃ m ∈ G, m • z = w)
    {m₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hm₀ : m₀ ∈ G) : m₀ = 1 ∨ m₀ = -1 := by
  obtain ⟨K, hK, hKs⟩ := s24q_tc_compact_cover ho hs
  have hcont : Continuous fun k : UpperHalfPlane => dist (m₀ • k) k :=
    (continuous_const_smul m₀).dist continuous_id
  obtain ⟨C, hC⟩ := (hK.image hcont).isBounded.bddAbove
  refine utm_sl2_eq_of_bounded_displacement m₀ (C := C) fun z => ?_
  obtain ⟨k, hk, hpk⟩ := hKs (p z)
  obtain ⟨m, hm, hmz⟩ := htrans z k hpk.symm
  have h1 : dist (m₀ • z) z = dist (m₀ • k) k := by
    rw [← hmz, ← dist_smul m (m₀ • z) z, hcomm m hm m₀ hm₀ z]
  rw [h1]
  exact hC ⟨k, hk, rfl⟩

/-- Genus one, the model: a closed surface of genus `1` is `ℂ/Λ`.  From `thm22_3_classification` this uses the torus
disjunct `∃ L p, IsCoveringMap p ∧ MDifferentiable p ∧ Surjective p ∧ ∀ z w, p z = p w ↔ z - w ∈ L.lattice`, after
excluding the other four: compact (not `ℂ`, not `ℂ ∖ {0}`), `π₁ ≅ ℤ²` nontrivial (not simply connected) and abelian
(not `ℍ/Γ`: an abelian Fuchsian group is elementary, never cocompact). -/
theorem s24q_torus_cover {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hS : HasGenus S 1) :
    ∃ (L : PeriodPair) (p : ℂ → S), IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ Function.Surjective p ∧
      ∀ z w, p z = p w ↔ z - w ∈ L.lattice := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  have hcompS : CompactSpace S := hS.1
  obtain ⟨e⟩ := hS.2 x₀
  obtain ⟨hcommG, hinfG⟩ := s24q_tc_surfaceGroup_one
  have hcommπ : ∀ γ δ : FundamentalGroup S x₀, γ * δ = δ * γ := by
    intro γ δ
    apply e.injective
    rw [map_mul, map_mul, hcommG]
  have hinfπ : Infinite (FundamentalGroup S x₀) := Infinite.of_injective e.symm e.symm.injective
  have : T2Space (RiemannDynamics.PathCover x₀) := RiemannDynamics.t2space_pathCover x₀
  have : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  rcases (thm22_2_uniformization (S := RiemannDynamics.PathCover x₀)).1 with hcompact | hplane | hdisc
  · exfalso
    have := s22c3_compact_pathCover_fundamentalGroup_finite x₀ hcompact.1
    exact not_finite (FundamentalGroup S x₀)
  · obtain ⟨p, hcov, hhol, hsurj, hdeck⟩ := s22tc_plane_input x₀ hplane
    rcases s22tc_plane_classify p hcov hhol hsurj hdeck with h | h | h
    · exfalso
      obtain ⟨f, hf⟩ := h
      obtain ⟨h', -⟩ := k22u_biholomorphic_homeomorph hf
      have := hcompS
      have : CompactSpace ℂ := h'.compactSpace
      exact not_compactSpace_iff.mpr inferInstance this
    · exfalso
      obtain ⟨f, hf⟩ := h
      obtain ⟨h', -⟩ := k22u_biholomorphic_homeomorph hf
      have := hcompS
      have hc : CompactSpace ↥puncturedPlaneOpens := h'.compactSpace
      have hcl : IsClosed (Set.range (Subtype.val : ↥puncturedPlaneOpens → ℂ)) :=
        (isCompact_range continuous_subtype_val).isClosed
      have hr : Set.range (Subtype.val : ↥puncturedPlaneOpens → ℂ) = {0}ᶜ := by
        ext z; simp [puncturedPlaneOpens, puncturedPlane]
      rw [hr, isClosed_compl_iff] at hcl
      have := hcl.mem_nhds (Set.mem_singleton (0 : ℂ))
      rw [Metric.mem_nhds_iff] at this
      obtain ⟨ε, hε, hsub⟩ := this
      have h1 : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        linarith
      have := hsub h1
      rw [Set.mem_singleton_iff] at this
      have h2 : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hε).ne'
      exact h2 this
    · exact h
  · exfalso
    obtain ⟨f, hf⟩ := hdisc
    obtain ⟨d, -⟩ := k22u_biholomorphic_diffeomorph hf
    obtain ⟨c, -, -⟩ := s22c6_cayley_diffeomorph
    let eP : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ UpperHalfPlane := d.trans c.symm
    obtain ⟨hcov, hhol, hsurj, -⟩ := s22ct_pathCover_upperHalf_input x₀ eP
    let G : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {m | ∃ γ : FundamentalGroup S x₀,
      ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
        (∀ y, F y = eP (RiemannDynamics.pathCoverDeck x₀ γ.asHom (eP.symm y))) ∧ ∀ τ, F τ = m • τ}
    have hDeckG : ∀ γ : FundamentalGroup S x₀, ∃ m ∈ G, ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
        (∀ y, F y = eP (RiemannDynamics.pathCoverDeck x₀ γ.asHom (eP.symm y))) ∧ ∀ τ, F τ = m • τ := by
      intro γ
      obtain ⟨F, hF, hform, -, -⟩ := s22ct_pathCover_conjugate_deck x₀ eP γ
      obtain ⟨m, hm⟩ := k22c5_eq_smul_of_mdifferentiable F hF
      exact ⟨m, ⟨γ, F, hF, hform, hm⟩, F, hform, hm⟩
    have hopen : IsOpenMap (RiemannDynamics.pathCoverProj x₀ ∘ eP.symm) :=
      hcov.isLocalHomeomorph.isOpenMap
    have hcomm : ∀ m ∈ G, ∀ n ∈ G, ∀ z : UpperHalfPlane, m • n • z = n • m • z := by
      rintro m ⟨γ, F, hF, hFform, hFm⟩ n ⟨δ, F', hF', hF'form, hF'm⟩ z
      rw [← hF'm, ← hFm, ← hFm, ← hF'm, hFform, hF'form, hF'form, hFform, eP.symm_apply_apply,
        eP.symm_apply_apply]
      congr 1
      exact (s22c1_deck_commute_iff x₀ γ δ).2 (hcommπ γ δ) _
    have htrans : ∀ z w, (RiemannDynamics.pathCoverProj x₀ ∘ eP.symm) z =
        (RiemannDynamics.pathCoverProj x₀ ∘ eP.symm) w → ∃ m ∈ G, m • z = w := by
      intro z w h
      obtain ⟨γ, hγ⟩ := RiemannDynamics.pathCoverDeck_transitive x₀ (eP.symm z) (eP.symm w) h
      obtain ⟨m, hmG, F, hform, hFm⟩ := hDeckG (FundamentalGroup.fromPath γ)
      refine ⟨m, hmG, ?_⟩
      rw [← hFm, hform]
      change eP (RiemannDynamics.pathCoverDeck x₀ γ (eP.symm z)) = w
      rw [hγ, eP.apply_symm_apply]
    obtain ⟨γ₀, hγ₀⟩ := exists_ne (1 : FundamentalGroup S x₀)
    obtain ⟨m₀, hm₀G, F₀, hF₀form, hF₀m⟩ := hDeckG γ₀
    have hfix : ∀ τ : UpperHalfPlane, m₀ • τ = τ → False := by
      intro τ hτ
      apply hγ₀
      refine s22c1_deck_fixed_eq_one x₀ γ₀ (eP.symm τ) ?_
      have h1 : F₀ τ = τ := by rw [hF₀m, hτ]
      rw [hF₀form] at h1
      have := congrArg eP.symm h1
      rwa [eP.symm_apply_apply] at this
    rcases s24q_tc_geom hopen hsurj G hcomm htrans hm₀G with h | h
    · exact hfix UpperHalfPlane.I (by rw [h, one_smul])
    · refine hfix UpperHalfPlane.I ?_
      rw [h]
      apply UpperHalfPlane.ext
      rw [h36t_coe_smul]
      have h0 : (UpperHalfPlane.I : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
      simp

/-- A continuous lattice-periodic function on `ℂ` is bounded. -/
theorem s24q_lg_bounded {L : PeriodPair} {E : ℂ → ℂ} (hc : Continuous E)
    (hper : ∀ z, ∀ l ∈ L.lattice, E (z + l) = E z) : ∃ M : ℝ, ∀ z, ‖E z‖ ≤ M := by
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂
  have hg : Continuous g := by simp only [g]; fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (hc.comp hg).continuousOn
  refine ⟨M, fun z => ?_⟩
  set a : ℝ := L.basis.repr z 0
  set b : ℝ := L.basis.repr z 1
  have hz : z = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
    have := L.basis.sum_repr z
    rw [Fin.sum_univ_two, PeriodPair.basis_zero, PeriodPair.basis_one] at this
    rw [← this]
    simp [a, b, Algebra.smul_def]
  have hl : (⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨⌊a⌋, ⌊b⌋, rfl⟩
  have hw : z = g (Int.fract a, Int.fract b) + ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂) := by
    simp only [g]
    rw [hz]
    have h1 : ((Int.fract a : ℝ) : ℂ) = (a : ℂ) - (⌊a⌋ : ℂ) := by
      rw [Int.fract]; push_cast; ring
    have h2 : ((Int.fract b : ℝ) : ℂ) = (b : ℂ) - (⌊b⌋ : ℂ) := by
      rw [Int.fract]; push_cast; ring
    rw [h1, h2]; ring
  rw [hw, hper _ _ hl]
  exact hM _ ⟨⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩, ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩⟩

/-- The determinant of a real-linear map of `ℂ` in terms of `A 1` and `A I`. -/
theorem s24q_lg_det_eq (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.basisOneI]
  ring

/-- `A z = α z + β z̄` for a real-linear map of `ℂ`. -/
theorem s24q_lg_alpha_beta (A : ℂ →ₗ[ℝ] ℂ) (z : ℂ) :
    A z = ((A 1 - Complex.I * A Complex.I) / 2) * z +
      ((A 1 + Complex.I * A Complex.I) / 2) * (starRingEnd ℂ) z := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  have h : A z = z.re • A 1 + z.im • A Complex.I := by
    have := congrArg A hz
    rw [map_add, map_smul, map_smul] at this
    exact this
  rw [h]
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> ring

/-- `|α|² - |β|² = det A`. -/
theorem s24q_lg_det_norm (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = ‖(A 1 - Complex.I * A Complex.I) / 2‖ ^ 2 -
      ‖(A 1 + Complex.I * A Complex.I) / 2‖ ^ 2 := by
  rw [s24q_lg_det_eq]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- A real-linear map with bounded distance to a surjection has nonzero determinant. -/
theorem s24q_lg_det_ne {F : ℂ ≃ₜ ℂ} {A : ℂ →ₗ[ℝ] ℂ} {M : ℝ} (hb : ∀ z, ‖F z - A z‖ ≤ M) :
    LinearMap.det A ≠ 0 := by
  intro h0
  have hnb : ¬ Function.Surjective A := by
    intro hs
    have hinj : Function.Injective A := LinearMap.injective_iff_surjective.mpr hs
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h0
    rw [LinearMap.ker_eq_bot.mpr hinj] at hker
    exact lt_irrefl _ hker
  have hlt : LinearMap.range A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hnb (LinearMap.range_eq_top.mp h))
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hφc : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  let φc : ℂ →L[ℝ] ℝ := ⟨φ, hφc⟩
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (LinearMap.ext h)
  have hφF : ∀ z, |φ (F z)| ≤ ‖φc‖ * M := by
    intro z
    have h1 : φ (A z) = 0 := hφ ⟨z, rfl⟩
    have h2 : φ (F z) = φ (F z - A z) := by rw [map_sub, h1, sub_zero]
    rw [h2]
    calc |φ (F z - A z)| = ‖φc (F z - A z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φc‖ * ‖F z - A z‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * M := mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)
  let t : ℝ := (‖φc‖ * M + 1) / |φ w|
  obtain ⟨z, hz⟩ := F.surjective (t • w)
  have h1 := hφF z
  rw [hz, map_smul, smul_eq_mul] at h1
  have hpos : 0 < |φ w| := abs_pos.mpr hw
  rw [abs_mul] at h1
  have h2 : |t| = t := by
    apply abs_of_nonneg
    have : 0 ≤ ‖φc‖ * M := le_trans (abs_nonneg _) (hφF z)
    exact div_nonneg (by linarith) hpos.le
  rw [h2] at h1
  have h3 : t * |φ w| = ‖φc‖ * M + 1 := by
    simp only [t]; field_simp
  linarith

/-- Winding `+1` of the image of every circle about its centre, from the local winding at the centre. -/
theorem s24q_lg_winding_all {F : ℂ ≃ₜ ℂ}
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (0 + ρ * Complex.exp (2 * π * Complex.I * t)) - F 0) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {R : ℝ} (hR : 0 < R) {L : ℝ → ℂ} (hL : ContinuousOn L (Set.Icc 0 1))
    (hLe : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = F (R * Complex.exp (2 * π * Complex.I * t)) - F 0) :
    L 1 - L 0 = 2 * π * Complex.I := by
  obtain ⟨ρ₁, hρ₁, hρ⟩ := hw
  let r₀ : ℝ := ρ₁ / 2
  have hr₀ : 0 < r₀ := half_pos hρ₁
  let H : ℝ → ℝ → ℂ := fun s t =>
    F (((((1 - s) * r₀ + s * R : ℝ)) : ℂ) * Complex.exp (2 * π * Complex.I * t)) - F 0
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (1 - s) * r₀ + s * R := fun s hs => by
    rcases le_or_gt s (1 / 2) with h | h
    · nlinarith [mul_nonneg hs.1 hR.le, mul_pos (show (0:ℝ) < 1 - s by linarith) hr₀]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) hr₀.le, mul_pos (show (0:ℝ) < s by linarith) hR]
  have hHc : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry H) := by
      simp only [H]
      have := F.continuous
      fun_prop
    exact this.continuousOn
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H s 0 := by
    intro s _
    simp only [H]
    have : Complex.exp (2 * π * Complex.I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * Complex.I * ((0 : ℝ) : ℂ)) := by
      simp [Complex.exp_two_pi_mul_I]
    rw [this]
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H s t ≠ 0 := by
    intro s hs t _ h0
    have h1 : F (((((1 - s) * r₀ + s * R : ℝ)) : ℂ) * Complex.exp (2 * π * Complex.I * t)) = F 0 :=
      sub_eq_zero.mp h0
    have h2 := F.injective h1
    have h3 : ((((1 - s) * r₀ + s * R : ℝ)) : ℂ) = 0 ∨ Complex.exp (2 * π * Complex.I * t) = 0 :=
      mul_eq_zero.mp h2
    rcases h3 with h3 | h3
    · exact (hpos s hs).ne' (by exact_mod_cast h3)
    · exact Complex.exp_ne_zero _ h3
  obtain ⟨L₀, hL₀c, hL₀e⟩ := exists_continuousOn_log_lift (γ := fun t => H 0 t) (w := 0)
    (by
      have : Continuous (fun t => H 0 t) := by
        simp only [H]; have := F.continuous; fun_prop
      exact this.continuousOn)
    (fun t ht => hne 0 ⟨le_refl _, zero_le_one⟩ t ht)
  have hL₀ : L₀ 1 - L₀ 0 = 2 * π * Complex.I := by
    refine hρ r₀ hr₀ (by simp only [r₀]; linarith) L₀ hL₀c ?_
    intro t ht
    have := hL₀e t ht
    simp only [H, sub_zero] at this
    rw [this]
    simp
  have := lift_change_eq_of_homotopy (H := H) (w := 0) hHc hper (fun s hs t ht => hne s hs t ht) hL₀c hL
    (by intro t ht; rw [hL₀e t ht, sub_zero]) (by
      intro t ht
      rw [hLe t ht, sub_zero]
      simp [H])
  rw [← this, hL₀]

/-- Winding `-1` of the image of a circle under an orientation reversing real-linear map. -/
theorem s24q_lg_winding_neg {α β : ℂ} (hαβ : ‖α‖ < ‖β‖) {R : ℝ} (hR : 0 < R) {L : ℝ → ℂ}
    (hL : ContinuousOn L (Set.Icc 0 1))
    (hLe : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) =
      α * (R * Complex.exp (2 * π * Complex.I * t)) +
        β * (starRingEnd ℂ) (R * Complex.exp (2 * π * Complex.I * t))) :
    L 1 - L 0 = -(2 * π * Complex.I) := by
  have hβ : β ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hαβ; exact absurd hαβ (not_lt.mpr (norm_nonneg _))
  have hconj : ∀ t : ℝ, (starRingEnd ℂ) (R * Complex.exp (2 * π * Complex.I * t)) =
      R * Complex.exp (-(2 * π * Complex.I * t)) := by
    intro t
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have : (starRingEnd ℂ) (2 * π * Complex.I * t) = -(2 * π * Complex.I * t) := by
      simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    rw [this]
  let H : ℝ → ℝ → ℂ := fun s t => s * (α * (R * Complex.exp (2 * π * Complex.I * t))) +
    β * (R * Complex.exp (-(2 * π * Complex.I * t)))
  have hHc : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry H) := by simp only [H]; fun_prop
    exact this.continuousOn
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H s 0 := by
    intro s _
    simp only [H]
    have h1 : Complex.exp (2 * π * Complex.I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * Complex.I * ((0 : ℝ) : ℂ)) := by
      simp [Complex.exp_two_pi_mul_I]
    have h2 : Complex.exp (-(2 * π * Complex.I * ((1 : ℝ) : ℂ))) = Complex.exp (-(2 * π * Complex.I * ((0 : ℝ) : ℂ))) := by
      rw [Complex.exp_neg, Complex.exp_neg, h1]
    rw [h1, h2]
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H s t ≠ 0 := by
    intro s hs t _ h0
    have hE : ∀ x : ℝ, ‖Complex.exp (x * Complex.I)‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I x
    have e1 : ‖Complex.exp (2 * π * Complex.I * t)‖ = 1 := by
      have := hE (2 * π * t); convert this using 2; push_cast; ring_nf
    have e2 : ‖Complex.exp (-(2 * π * Complex.I * t))‖ = 1 := by
      have := hE (-(2 * π * t)); convert this using 2; push_cast; ring_nf
    have h1 : ‖(s : ℂ) * (α * (R * Complex.exp (2 * π * Complex.I * t)))‖ = s * (‖α‖ * R) := by
      rw [norm_mul, norm_mul, norm_mul, e1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hs.1, abs_of_pos hR]; ring
    have h2 : ‖β * (R * Complex.exp (-(2 * π * Complex.I * t)))‖ = ‖β‖ * R := by
      rw [norm_mul, norm_mul, e2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]; ring
    have h3 : β * (R * Complex.exp (-(2 * π * Complex.I * t))) =
        -((s : ℂ) * (α * (R * Complex.exp (2 * π * Complex.I * t)))) := by
      have := h0; simp only [H] at this; linear_combination this
    have h4 := congrArg (fun x => ‖x‖) h3
    simp only [norm_neg] at h4
    rw [h2, h1] at h4
    have h5 : s * (‖α‖ * R) ≤ ‖α‖ * R := by
      nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (mul_nonneg (norm_nonneg α) hR.le)]
    nlinarith [mul_pos hR (sub_pos.2 hαβ)]
  -- explicit lift at `s = 0`
  have hβR : (R : ℂ) * β ≠ 0 := mul_ne_zero (by exact_mod_cast hR.ne') hβ
  let L₀ : ℝ → ℂ := fun t => Complex.log (β * R) - 2 * π * Complex.I * t
  have hL₀c : ContinuousOn L₀ (Icc 0 1) := by
    have : Continuous L₀ := by simp only [L₀]; fun_prop
    exact this.continuousOn
  have hL₀e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₀ t) = H 0 t - 0 := by
    intro t _
    simp only [L₀, H, Complex.ofReal_zero, zero_mul, zero_add, sub_zero, Complex.exp_sub,
      Complex.exp_log (by rwa [mul_comm] : β * (R : ℂ) ≠ 0)]
    rw [Complex.exp_neg]
    field_simp
  have := lift_change_eq_of_homotopy (H := H) (w := 0) hHc hper (fun s hs t ht => hne s hs t ht) hL₀c hL
    hL₀e (by
      intro t ht
      rw [hLe t ht, sub_zero, hconj]
      simp only [H, Complex.ofReal_one, one_mul])
  rw [← this]
  simp only [L₀]
  push_cast
  ring

/-- **Orientation bridge (tori).** A homeomorphism `F` of `ℂ` with local winding `+1` at every point (the conclusion of
`rc_hloc_of_sensePreserving`) and `F(z + λ) = F(z) + A λ` on a lattice has `det A > 0` (`F - A` is bounded; `A`
singular would make `F` non-surjective, `det A < 0` reverses the winding of large circles). -/
theorem s24q_torus_det_pos {L₀ : PeriodPair} {F : ℂ ≃ₜ ℂ}
    (hw : ∀ p : ℂ, ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (p + ρ * Complex.exp (2 * π * Complex.I * t)) - F p) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {A : ℂ →ₗ[ℝ] ℂ} (hA : ∀ z, ∀ l ∈ L₀.lattice, F (z + l) = F z + A l) : 0 < LinearMap.det A := by
  classical
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  obtain ⟨M, hM⟩ := s24q_lg_bounded (L := L₀) (E := fun z => F z - A z) (F.continuous.sub hAc) (by
    intro z l hl
    simp only [hA z l hl, map_add]
    ring)
  have hdet0 : LinearMap.det A ≠ 0 := s24q_lg_det_ne hM
  by_contra hnot
  have hdet : LinearMap.det A < 0 := lt_of_le_of_ne (not_lt.mp hnot) hdet0
  have hnorm := s24q_lg_det_norm A
  set α : ℂ := (A 1 - Complex.I * A Complex.I) / 2 with hα
  set β : ℂ := (A 1 + Complex.I * A Complex.I) / 2 with hβ
  have hαβ : ‖α‖ < ‖β‖ := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg α, norm_nonneg β]
  have hMF : ‖F 0‖ ≤ M := by simpa using hM 0
  set M₂ : ℝ := M + ‖F 0‖ with hM₂
  have hM₂0 : 0 ≤ M₂ := by nlinarith [norm_nonneg (F 0)]
  have hd : 0 < ‖β‖ - ‖α‖ := sub_pos.2 hαβ
  set R : ℝ := (M₂ + 1) / (‖β‖ - ‖α‖) with hRdef
  have hR : 0 < R := div_pos (by linarith) hd
  have hRd : (‖β‖ - ‖α‖) * R = M₂ + 1 := by rw [hRdef]; field_simp
  let E : ℝ → ℂ := fun t => Complex.exp (2 * π * Complex.I * t)
  have hEn : ∀ t : ℝ, ‖E t‖ = 1 := by
    intro t
    show ‖Complex.exp (2 * π * Complex.I * t)‖ = 1
    have := Complex.norm_exp_ofReal_mul_I (2 * π * t)
    convert this using 2; push_cast; ring_nf
  let zt : ℝ → ℂ := fun t => (R : ℂ) * E t
  have hztn : ∀ t, ‖zt t‖ = R := by
    intro t; simp only [zt, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hAlow : ∀ t, M₂ + 1 ≤ ‖A (zt t)‖ := by
    intro t
    rw [s24q_lg_alpha_beta A (zt t)]
    have h1 : ‖(starRingEnd ℂ) (zt t)‖ = R := by rw [Complex.norm_conj, hztn]
    have h2 : ‖β * (starRingEnd ℂ) (zt t)‖ ≤ ‖α * zt t + β * (starRingEnd ℂ) (zt t)‖ + ‖α * zt t‖ := by
      have := norm_sub_le (α * zt t + β * (starRingEnd ℂ) (zt t)) (α * zt t)
      simpa using this
    rw [norm_mul, norm_mul, h1, hztn] at h2
    rw [← hRd]; nlinarith
  let e : ℂ → ℂ := fun z => F z - A z - F 0
  have hen : ∀ z, ‖e z‖ ≤ M₂ := by
    intro z
    have h1 := hM z
    calc ‖e z‖ = ‖(F z - A z) - F 0‖ := rfl
      _ ≤ ‖F z - A z‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ M₂ := by linarith
  let P : ℝ → ℝ → ℂ := fun s t => A (zt t) + (s : ℂ) * e (zt t)
  have hztc : Continuous zt := by simp only [zt, E]; fun_prop
  have hPc : ContinuousOn (Function.uncurry P) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry P) := by
      simp only [P, e]
      have := F.continuous; have := hAc
      fun_prop
    exact this.continuousOn
  have hz1 : zt 1 = zt 0 := by
    simp only [zt, E]
    have : Complex.exp (2 * π * Complex.I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * Complex.I * ((0 : ℝ) : ℂ)) := by
      simp [Complex.exp_two_pi_mul_I]
    rw [this]
  have hPper : ∀ s ∈ Icc (0 : ℝ) 1, P s 1 = P s 0 := by
    intro s _; simp only [P, hz1]
  have hPne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, P s t ≠ 0 := by
    intro s hs t _ h0
    have h1 : ‖A (zt t)‖ = ‖(s : ℂ) * e (zt t)‖ := by
      have : A (zt t) = -((s : ℂ) * e (zt t)) := by
        have := h0; simp only [P] at this; linear_combination this
      rw [this, norm_neg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
    have := hAlow t
    have := hen (zt t)
    nlinarith [hs.2, norm_nonneg (e (zt t))]
  -- lifts at the two ends
  have hP1 : ∀ t, P 1 t = F (zt t) - F 0 := by
    intro t; simp only [P, e]; push_cast; ring
  have hP0 : ∀ t, P 0 t = A (zt t) := by
    intro t; simp only [P]; simp
  obtain ⟨Lg, hLgc, hLge⟩ := exists_continuousOn_log_lift (γ := fun t => P 1 t) (w := 0)
    ((hPc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨zero_le_one, le_refl _⟩, ht⟩)).congr (fun t _ => rfl))
    (fun t ht => hPne 1 ⟨zero_le_one, le_refl _⟩ t ht)
  obtain ⟨LA, hLAc, hLAe⟩ := exists_continuousOn_log_lift (γ := fun t => P 0 t) (w := 0)
    ((hPc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨le_refl _, zero_le_one⟩, ht⟩)).congr (fun t _ => rfl))
    (fun t ht => hPne 0 ⟨le_refl _, zero_le_one⟩ t ht)
  have hW1 : Lg 1 - Lg 0 = 2 * π * Complex.I := by
    refine s24q_lg_winding_all (hw 0) hR hLgc ?_
    intro t ht
    rw [hLge t ht, sub_zero, hP1]
  have hW0 : LA 1 - LA 0 = -(2 * π * Complex.I) := by
    refine s24q_lg_winding_neg hαβ hR hLAc ?_
    intro t ht
    rw [hLAe t ht, sub_zero, hP0, s24q_lg_alpha_beta A (zt t)]
  have hEq := lift_change_eq_of_homotopy (H := P) (w := 0) hPc hPper
    (fun s hs t ht => hPne s hs t ht) hLAc hLgc
    (by intro t ht; rw [hLAe t ht])
    (by intro t ht; rw [hLge t ht])
  rw [hW0, hW1] at hEq
  have hπ : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply hπ
  linear_combination (-1 / 2 : ℂ) * hEq

/-- A continuous map `ℂ → ℂ` with values in a discrete `ℤ`-submodule is constant. -/
theorem s24q_tq_const (L : Submodule ℤ ℂ) [DiscreteTopology L] {c : ℂ → ℂ} (hc : Continuous c)
    (hL : ∀ z, c z ∈ L) : ∀ z, c z = c 0 := by
  intro z
  let c' : ℂ → L := fun z => ⟨c z, hL z⟩
  have hc' : Continuous c' := hc.subtype_mk _
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc' (x := z) (y := 0)
  exact congrArg Subtype.val this

/-- Continuous lift through a surjective plane covering. -/
theorem s24q_tq_lift {X : Type*} [TopologicalSpace X] {p : ℂ → X} (hpc : IsCoveringMap p)
    (hps : Function.Surjective p) {g : ℂ → X} (hg : Continuous g) :
    ∃ F : ℂ → ℂ, Continuous F ∧ ∀ z, p (F z) = g z := by
  obtain ⟨e₀, he₀⟩ := hps (g 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hpc.existsUnique_continuousMap_lifts ⟨g, hg⟩ 0 e₀ he₀
  exact ⟨F, F.continuous, fun z => congrFun hF z⟩

/-- Equivariance of a lift: `F (z + l) = F z + A l` for a real linear `A` carrying the lattice into the lattice. -/
theorem s24q_tq_equivariant {Y : Type*} {L₀ L₁ : PeriodPair}
    {p₁ : ℂ → Y} (hp₁ : ∀ x y, p₁ x = p₁ y ↔ x - y ∈ L₁.lattice) {F : ℂ → ℂ} (hF : Continuous F)
    (hper : ∀ z, ∀ l ∈ L₀.lattice, p₁ (F (z + l)) = p₁ (F z)) :
    ∃ A : ℂ →ₗ[ℝ] ℂ, (∀ l ∈ L₀.lattice, A l ∈ L₁.lattice) ∧
      ∀ z, ∀ l ∈ L₀.lattice, F (z + l) = F z + A l := by
  classical
  have hdisc : DiscreteTopology L₁.lattice := inferInstance
  have hconst : ∀ l ∈ L₀.lattice, ∃ a ∈ L₁.lattice, ∀ z, F (z + l) = F z + a := by
    intro l hl
    have hmem : ∀ z, F (z + l) - F z ∈ L₁.lattice := fun z => (hp₁ _ _).1 (hper z l hl)
    have hc : Continuous fun z => F (z + l) - F z := (hF.comp (continuous_id.add continuous_const)).sub hF
    have := s24q_tq_const L₁.lattice hc hmem
    refine ⟨F (0 + l) - F 0, hmem 0, fun z => ?_⟩
    have h := this z
    simp only [zero_add] at h ⊢
    linear_combination h
  obtain ⟨a₁, ha₁, h₁⟩ := hconst L₀.ω₁ L₀.ω₁_mem_lattice
  obtain ⟨a₂, ha₂, h₂⟩ := hconst L₀.ω₂ L₀.ω₂_mem_lattice
  let A : ℂ →ₗ[ℝ] ℂ := L₀.basis.constr ℝ ![a₁, a₂]
  have hA1 : A L₀.ω₁ = a₁ := by
    have h := L₀.basis.constr_basis ℝ ![a₁, a₂] 0
    rw [PeriodPair.basis_zero] at h
    exact h
  have hA2 : A L₀.ω₂ = a₂ := by
    have h := L₀.basis.constr_basis ℝ ![a₁, a₂] 1
    rw [PeriodPair.basis_one] at h
    exact h
  let S : AddSubgroup ℂ :=
    { carrier := {l | ∀ z, F (z + l) = F z + A l}
      zero_mem' := fun z => by simp
      add_mem' := by
        intro l l' hl hl' z
        have hl : ∀ z, F (z + l) = F z + A l := hl
        have hl' : ∀ z, F (z + l') = F z + A l' := hl'
        show F (z + (l + l')) = F z + A (l + l')
        have e : z + (l + l') = (z + l) + l' := (add_assoc _ _ _).symm
        rw [e, hl' (z + l), hl z, map_add]; ring
      neg_mem' := by
        intro l hl z
        have hl : ∀ z, F (z + l) = F z + A l := hl
        show F (z + -l) = F z + A (-l)
        have := hl (z + -l)
        rw [neg_add_cancel_right] at this
        rw [map_neg]
        linear_combination (-1 : ℂ) * this }
  have hω₁ : L₀.ω₁ ∈ S := fun z => by rw [h₁ z, hA1]
  have hω₂ : L₀.ω₂ ∈ S := fun z => by rw [h₂ z, hA2]
  have hle : L₀.lattice ≤ S.toIntSubmodule := by
    unfold PeriodPair.lattice
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hω₁
    · exact hω₂
  have hS : ∀ l ∈ L₀.lattice, ∀ z, F (z + l) = F z + A l := fun l hl => hle hl
  refine ⟨A, fun l hl => ?_, fun z l hl => hS l hl z⟩
  have h1 : F (0 + l) - F 0 ∈ L₁.lattice := (hp₁ _ _).1 (hper 0 l hl)
  have h2 := hS l hl 0
  rw [zero_add] at h1 h2
  have : A l = F l - F 0 := by linear_combination -h2
  rw [this]; exact h1

/-- The lift of a homeomorphism between two plane-covered surfaces is a homeomorphism of `ℂ`. -/
theorem s24q_tq_homeo {S₀ S₁ : Type*} [TopologicalSpace S₀] [TopologicalSpace S₁] {L₀ L₁ : PeriodPair}
    {p₀ : ℂ → S₀} {p₁ : ℂ → S₁} (hc₀ : IsCoveringMap p₀) (hs₀ : Function.Surjective p₀)
    (hf₀ : ∀ x y, p₀ x = p₀ y ↔ x - y ∈ L₀.lattice)
    (hc₁ : IsCoveringMap p₁) (hs₁ : Function.Surjective p₁)
    (hf₁ : ∀ x y, p₁ x = p₁ y ↔ x - y ∈ L₁.lattice) (f : S₀ ≃ₜ S₁) :
    ∃ F : ℂ ≃ₜ ℂ, ∀ z, p₁ (F z) = f (p₀ z) := by
  obtain ⟨F, hFc, hF⟩ := s24q_tq_lift hc₁ hs₁ (g := fun z => f (p₀ z)) (f.continuous.comp hc₀.continuous)
  obtain ⟨G, hGc, hG⟩ := s24q_tq_lift hc₀ hs₀ (g := fun w => f.symm (p₁ w)) (f.symm.continuous.comp hc₁.continuous)
  have hFG : ∀ w, F (G w) - w ∈ L₁.lattice := by
    intro w
    refine (hf₁ _ _).1 ?_
    rw [hF, hG, f.apply_symm_apply]
  have hGF : ∀ z, G (F z) - z ∈ L₀.lattice := by
    intro z
    refine (hf₀ _ _).1 ?_
    rw [hG, hF, f.symm_apply_apply]
  have hc1 : Continuous fun w => F (G w) - w := (hFc.comp hGc).sub continuous_id
  have hc0 : Continuous fun z => G (F z) - z := (hGc.comp hFc).sub continuous_id
  have k1 := s24q_tq_const L₁.lattice hc1 hFG
  have k0 := s24q_tq_const L₀.lattice hc0 hGF
  set l₁ := F (G 0) - 0
  set l₀ := G (F 0) - 0
  have hH : ∀ w, F (G (w - l₁)) = w := by
    intro w
    have := k1 (w - l₁)
    simp only [l₁] at this ⊢
    linear_combination this
  have hinj : Function.Injective F := by
    intro z z' h
    have h1 := k0 z
    have h2 := k0 z'
    have : G (F z) = G (F z') := by rw [h]
    simp only [l₀] at h1 h2
    linear_combination -h1 + h2 + this
  have hsurj : Function.Surjective F := fun w => ⟨G (w - l₁), hH w⟩
  refine ⟨{ Equiv.ofBijective F ⟨hinj, hsurj⟩ with continuous_toFun := hFc, continuous_invFun := ?_ }, hF⟩
  have : (Equiv.ofBijective F ⟨hinj, hsurj⟩).symm = fun w => G (w - l₁) := by
    funext w
    rw [Equiv.symm_apply_eq]
    exact (hH w).symm
  show Continuous (Equiv.ofBijective F ⟨hinj, hsurj⟩).symm
  rw [this]
  exact hGc.comp (continuous_id.sub continuous_const)

/-- Local winding `+1` of a lift `F` of a locally sense preserving homeomorphism through holomorphic plane coverings. -/
theorem s24q_tq_winding {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {p₀ : ℂ → S₀} {p₁ : ℂ → S₁} (hc₀ : IsCoveringMap p₀) (hd₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀)
    (hc₁ : IsCoveringMap p₁) (hd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₁) (f : S₀ ≃ₜ S₁)
    (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x))
    {F : ℂ ≃ₜ ℂ} (hF : ∀ z, p₁ (F z) = f (p₀ z)) (p : ℂ) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (p + ρ * Complex.exp (2 * π * Complex.I * t)) - F p) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
  classical
  set x : S₀ := p₀ p with hx
  set y : S₁ := f x with hy
  have hFp : p₁ (F p) = y := hF p
  obtain ⟨e₀, he₀, hpe₀⟩ := hc₀.isLocalHomeomorph p
  obtain ⟨e₁, he₁, hpe₁⟩ := hc₁.isLocalHomeomorph (F p)
  let U : Set ℂ := e₀.source ∩ p₀ ⁻¹' (chartAt ℂ x).source ∩ (fun z => f (p₀ z)) ⁻¹' (chartAt ℂ y).source
  let V : Set ℂ := e₁.source ∩ p₁ ⁻¹' (chartAt ℂ y).source
  have hU : IsOpen U :=
    (e₀.open_source.inter (hc₀.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)).inter
      ((f.continuous.comp hc₀.continuous).isOpen_preimage _ (chartAt ℂ y).open_source)
  have hV : IsOpen V := e₁.open_source.inter (hc₁.continuous.isOpen_preimage _ (chartAt ℂ y).open_source)
  have hpU : p ∈ U := ⟨⟨he₀, mem_chart_source ℂ x⟩, by
    show f (p₀ p) ∈ (chartAt ℂ y).source
    exact mem_chart_source ℂ y⟩
  have hFV : F p ∈ V := ⟨he₁, by rw [Set.mem_preimage, hFp]; exact mem_chart_source ℂ y⟩
  refine s24q_lw_winding_conj (F := F) (h := localMapExpr f x) (ψ₀ := fun z => chartAt ℂ x (p₀ z))
    (ψ₁ := fun z => chartAt ℂ y (p₁ z)) (U := U) (V := V) (D := localMapDomain f x) hU hpU hV
    (s23_localMapDomain_isOpen f.continuous x) ?_ ?_ ?_ ?_ F.continuous.continuousAt hFV ?_ ?_ ?_ ?_ (hf x)
  · intro z hz
    exact (s22tc_d_chart (hd₀ z) x hz.1.2).differentiableWithinAt
  · intro a ha b hb hab
    have h1 : p₀ a = p₀ b := (chartAt ℂ x).injOn ha.1.2 hb.1.2 hab
    rw [hpe₀] at h1
    exact e₀.injOn ha.1.1 hb.1.1 h1
  · intro z hz
    exact (s22tc_d_chart (hd₁ z) y hz.2).differentiableWithinAt
  · intro a ha b hb hab
    have h1 : p₁ a = p₁ b := (chartAt ℂ y).injOn ha.2 hb.2 hab
    rw [hpe₁] at h1
    exact e₁.injOn ha.1 hb.1 h1
  · intro z hz
    refine ⟨(chartAt ℂ x).map_source hz.1.2, ?_⟩
    show f ((chartAt ℂ x).symm (chartAt ℂ x (p₀ z))) ∈ (chartAt ℂ (f x)).source
    rw [(chartAt ℂ x).left_inv hz.1.2]
    exact hz.2
  · intro z hz hFz
    show chartAt ℂ y (p₁ (F z)) = chartAt ℂ (f x) (f ((chartAt ℂ x).symm (chartAt ℂ x (p₀ z))))
    rw [hF z, (chartAt ℂ x).left_inv hz.1.2]
  · intro z hz
    have h1 : ContinuousOn (fun z => (chartAt ℂ x).symm z) (localMapDomain f x) :=
      (chartAt ℂ x).continuousOn_symm.mono (fun z hz => hz.1)
    have h2 : ContinuousOn (fun z => f ((chartAt ℂ x).symm z)) (localMapDomain f x) :=
      f.continuous.comp_continuousOn h1
    refine ((chartAt ℂ (f x)).continuousOn.comp h2 (fun z hz => hz.2)) z hz
  · exact s23_c1_injOn_localMapExpr f.injective x

/-- The linear part of the lift: `F (z + l) = F z + A l`, `det A > 0`, and `A w ∈ Λ₁ ↔ w ∈ Λ₀`-compatibility. -/
theorem s24q_tq_affine {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {L₀ L₁ : PeriodPair}
    {p₀ : ℂ → S₀} {p₁ : ℂ → S₁} (hc₀ : IsCoveringMap p₀) (hd₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀)
    (hf₀ : ∀ x y, p₀ x = p₀ y ↔ x - y ∈ L₀.lattice)
    (hc₁ : IsCoveringMap p₁) (hd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₁)
    (hf₁ : ∀ x y, p₁ x = p₁ y ↔ x - y ∈ L₁.lattice) (f : S₀ ≃ₜ S₁)
    (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x))
    {F : ℂ ≃ₜ ℂ} (hF : ∀ z, p₁ (F z) = f (p₀ z)) :
    ∃ A : ℂ →ₗ[ℝ] ℂ, 0 < LinearMap.det A ∧ (∀ l ∈ L₀.lattice, A l ∈ L₁.lattice) ∧
      (∀ w, A w ∈ L₁.lattice → w ∈ L₀.lattice) ∧
      ∀ z, ∀ l ∈ L₀.lattice, F (z + l) = F z + A l := by
  classical
  obtain ⟨A, hA1, hA2⟩ := s24q_tq_equivariant (L₀ := L₀) (L₁ := L₁) (p₁ := p₁) hf₁ F.continuous (by
    intro z l hl
    rw [hF, hF, (hf₀ (z + l) z).2 (by simpa using hl)])
  have hpF : ∀ w, p₀ (F.symm w) = f.symm (p₁ w) := by
    intro w
    have := hF (F.symm w)
    rw [F.apply_symm_apply] at this
    rw [this, f.symm_apply_apply]
  obtain ⟨B, hB1, hB2⟩ := s24q_tq_equivariant (L₀ := L₁) (L₁ := L₀) (p₁ := p₀) hf₀ F.symm.continuous (by
    intro w l hl
    rw [hpF, hpF, (hf₁ (w + l) w).2 (by simpa using hl)])
  have hdet : 0 < LinearMap.det A :=
    s24q_torus_det_pos (L₀ := L₀) (F := F) (fun p => s24q_tq_winding hc₀ hd₀ hc₁ hd₁ f hf hF p) hA2
  have hAB : ∀ l ∈ L₁.lattice, A (B l) = l := by
    intro l hl
    have h1 := hB2 0 l hl
    have h2 := hA2 (F.symm 0) (B l) (hB1 l hl)
    have h3 : F (F.symm 0 + B l) = 0 + l := by
      rw [zero_add] at h1 ⊢
      rw [← h1, F.apply_symm_apply]
    rw [h3, F.apply_symm_apply] at h2
    linear_combination -h2
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    exact hdet.ne' (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  refine ⟨A, hdet, hA1, fun w hw => ?_, hA2⟩
  have := hAinj (show A (B (A w)) = A w from hAB _ hw)
  rw [← this]
  exact hB1 _ hw

/-- Descent of a continuous map of `ℂ` through two surjective open (covering) maps. -/
theorem s24q_tq_descend {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : ℂ → X} {p' : ℂ → Y}
    (hc : Continuous p) (hs : Function.Surjective p) (ho : IsOpenMap p) (hc' : Continuous p')
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hcomp : ∀ z w, p z = p w → p' (φ z) = p' (φ w)) :
    ∃ q : X → Y, Continuous q ∧ ∀ z, q (p z) = p' (φ z) := by
  classical
  let q : X → Y := fun x => p' (φ (Classical.choose (hs x)))
  have hq : ∀ z, q (p z) = p' (φ z) := fun z =>
    hcomp _ _ (Classical.choose_spec (hs (p z)))
  refine ⟨q, ?_, hq⟩
  have hqm : IsQuotientMap p := ho.isQuotientMap hc hs
  rw [hqm.continuous_iff]
  have : q ∘ p = fun z => p' (φ z) := funext hq
  rw [this]
  exact hc'.comp hφ

/-- The descended homeomorphism `q (p₀ z) = p₁ (A z)` of the two tori. -/
theorem s24q_tq_q {S₀ S₁ : Type*} [TopologicalSpace S₀] [TopologicalSpace S₁] {L₀ L₁ : PeriodPair}
    {p₀ : ℂ → S₀} {p₁ : ℂ → S₁} (hc₀ : IsCoveringMap p₀) (hs₀ : Function.Surjective p₀)
    (hf₀ : ∀ x y, p₀ x = p₀ y ↔ x - y ∈ L₀.lattice)
    (hc₁ : IsCoveringMap p₁) (hs₁ : Function.Surjective p₁)
    (hf₁ : ∀ x y, p₁ x = p₁ y ↔ x - y ∈ L₁.lattice) {A : ℂ →ₗ[ℝ] ℂ}
    (hdet : 0 < LinearMap.det A) (hA1 : ∀ l ∈ L₀.lattice, A l ∈ L₁.lattice)
    (hA3 : ∀ w, A w ∈ L₁.lattice → w ∈ L₀.lattice) :
    ∃ q : S₀ ≃ₜ S₁, ∀ z, q (p₀ z) = p₁ (A z) := by
  classical
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    exact hdet.ne' (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hAsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hAinj
  let e : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  have hec : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  obtain ⟨q₁, hq₁c, hq₁⟩ := s24q_tq_descend hc₀.continuous hs₀ hc₀.isLocalHomeomorph.isOpenMap
    hc₁.continuous hAc (φ := A) (by
      intro z w h
      have := (hf₀ z w).1 h
      exact (hf₁ _ _).2 (by rw [← map_sub]; exact hA1 _ this))
  obtain ⟨q₂, hq₂c, hq₂⟩ := s24q_tq_descend hc₁.continuous hs₁ hc₁.isLocalHomeomorph.isOpenMap
    hc₀.continuous hec (φ := e.symm) (by
      intro z w h
      have := (hf₁ z w).1 h
      refine (hf₀ _ _).2 ?_
      rw [← map_sub]
      apply hA3
      have : A (e.symm (z - w)) = z - w := e.apply_symm_apply _
      rw [this]; exact ‹z - w ∈ L₁.lattice›)
  have hl : ∀ x, q₂ (q₁ x) = x := by
    intro x
    obtain ⟨z, rfl⟩ := hs₀ x
    rw [hq₁, hq₂]
    have : e.symm (A z) = z := e.symm_apply_apply z
    rw [this]
  have hr : ∀ y, q₁ (q₂ y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := hs₁ y
    rw [hq₂, hq₁]
    have : A (e.symm w) = w := e.apply_symm_apply w
    rw [this]
  exact ⟨Homeomorph.mk (Equiv.mk q₁ q₂ hl hr) hq₁c hq₂c, hq₁⟩

/-- Descent of a parametrized continuous map of `ℂ` through a surjective open map. -/
theorem s24q_tq_descend2 {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    {p : ℂ → X} {p' : ℂ → Y} (hc : Continuous p) (hs : Function.Surjective p) (ho : IsOpenMap p)
    (hc' : Continuous p') {φ : T × ℂ → ℂ} (hφ : Continuous φ)
    (hcomp : ∀ t z w, p z = p w → p' (φ (t, z)) = p' (φ (t, w))) :
    ∃ q : T × X → Y, Continuous q ∧ ∀ t z, q (t, p z) = p' (φ (t, z)) := by
  classical
  let q : T × X → Y := fun u => p' (φ (u.1, Classical.choose (hs u.2)))
  have hq : ∀ t z, q (t, p z) = p' (φ (t, z)) := fun t z =>
    hcomp t _ _ (Classical.choose_spec (hs (p z)))
  refine ⟨q, ?_, hq⟩
  let g : T × ℂ → T × X := fun u => (u.1, p u.2)
  have hgc : Continuous g := by simp only [g]; fun_prop
  have hgs : Function.Surjective g := by
    rintro ⟨t, x⟩
    obtain ⟨z, rfl⟩ := hs x
    exact ⟨(t, z), rfl⟩
  have hgo : IsOpenMap g := IsOpenMap.id.prodMap ho
  have hqm : IsQuotientMap g := hgo.isQuotientMap hgc hgs
  rw [hqm.continuous_iff]
  have : q ∘ g = fun u => p' (φ u) := funext fun u => hq u.1 u.2
  rw [this]
  exact hc'.comp hφ

/-- The equivariant straight-line homotopy from `f` to the affine representative. -/
theorem s24q_tq_homotopy {S₀ S₁ : Type*} [TopologicalSpace S₀] [TopologicalSpace S₁] {L₀ L₁ : PeriodPair}
    {p₀ : ℂ → S₀} {p₁ : ℂ → S₁} (hc₀ : IsCoveringMap p₀) (hs₀ : Function.Surjective p₀)
    (hf₀ : ∀ x y, p₀ x = p₀ y ↔ x - y ∈ L₀.lattice) (hc₁ : IsCoveringMap p₁)
    (hf₁ : ∀ x y, p₁ x = p₁ y ↔ x - y ∈ L₁.lattice) (f : S₀ ≃ₜ S₁) {F : ℂ ≃ₜ ℂ}
    (hF : ∀ z, p₁ (F z) = f (p₀ z)) {A : ℂ →ₗ[ℝ] ℂ} (hA1 : ∀ l ∈ L₀.lattice, A l ∈ L₁.lattice)
    (hFA : ∀ z, ∀ l ∈ L₀.lattice, F (z + l) = F z + A l) {q : S₀ ≃ₜ S₁} (hq : ∀ z, q (p₀ z) = p₁ (A z)) :
    ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  classical
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  let φ : unitInterval × ℂ → ℂ := fun u => (1 - (u.1 : ℝ) : ℝ) * F u.2 + ((u.1 : ℝ) : ℂ) * A u.2
  have hφ : Continuous φ := by
    simp only [φ]
    have := F.continuous
    fun_prop
  obtain ⟨H, hHc, hH⟩ := s24q_tq_descend2 hc₀.continuous hs₀ hc₀.isLocalHomeomorph.isOpenMap hc₁.continuous hφ
    (by
      intro t z w h
      have hl := (hf₀ z w).1 h
      refine (hf₁ _ _).2 ?_
      have h1 : F z - F w = A z - A w := by
        have := hFA w (z - w) hl
        rw [add_sub_cancel, map_sub] at this
        linear_combination this
      simp only [φ]
      have h2 : (1 - (t : ℝ) : ℝ) * F z + ((t : ℝ) : ℂ) * A z - ((1 - (t : ℝ) : ℝ) * F w + ((t : ℝ) : ℂ) * A w) =
          A (z - w) := by
        rw [map_sub]
        push_cast
        linear_combination (1 - (t : ℂ)) * h1
      rw [h2]
      exact hA1 _ hl)
  refine ⟨⟨⟨H, hHc⟩, ?_, ?_⟩⟩
  · intro x
    obtain ⟨z, rfl⟩ := hs₀ x
    show H (0, p₀ z) = f (p₀ z)
    rw [hH]
    simp [φ, hF z]
  · intro x
    obtain ⟨z, rfl⟩ := hs₀ x
    show H (1, p₀ z) = q (p₀ z)
    rw [hH, hq]
    simp [φ]

/-- The affine map `A` (with `det A > 0`) is `K`-quasiconformal on `ℂ`. -/
theorem s24q_tq_affine_qc (A : ℂ →ₗ[ℝ] ℂ) (hdet : 0 < LinearMap.det A) :
    ∃ K : ℝ, IsKQC (fun z => A z) univ K := by
  have hn := s24q_lg_det_norm A
  set α : ℂ := (A 1 - Complex.I * A Complex.I) / 2
  set β : ℂ := (A 1 + Complex.I * A Complex.I) / 2
  have hβα : ‖β‖ < ‖α‖ := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg α, norm_nonneg β]
  have h1 := (affine_isC1Quasiconformal (A := α) (B := β) (C := 0) hβα).1
  refine ⟨_, ad_isKQC_congr (isKQC_of_isC1Quasiconformal h1) ?_⟩
  intro z _
  simp only [add_zero]
  exact s24q_lg_alpha_beta A z

/-- `q` is quasiconformal: its local expressions are `ψ₁ ∘ A ∘ ψ₀⁻¹` with conformal `ψ₀, ψ₁`. -/
theorem s24q_tq_qc {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {p₀ : ℂ → S₀} {p₁ : ℂ → S₁}
    (hc₀ : IsCoveringMap p₀) (hd₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀) (hs₀ : Function.Surjective p₀)
    (hc₁ : IsCoveringMap p₁) (hd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₁) {A : ℂ →ₗ[ℝ] ℂ}
    (hdet : 0 < LinearMap.det A) {q : S₀ ≃ₜ S₁} (hq : ∀ z, q (p₀ z) = p₁ (A z)) : IsQCRS q := by
  classical
  obtain ⟨K, hK⟩ := s24q_tq_affine_qc A hdet
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  refine ⟨K, hK.2.1, fun x => ?_⟩
  refine s23_lg (s23_localMapDomain_isOpen q.continuous x) hK.2.1 (s23_c1_injOn_localMapExpr q.injective x) ?_
  intro z hz
  have hz1 : z ∈ (chartAt ℂ x).target := hz.1
  have hz2 : q ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (q x)).source := hz.2
  obtain ⟨w, hw⟩ := hs₀ ((chartAt ℂ x).symm z)
  obtain ⟨e₀, he₀, hpe₀⟩ := hc₀.isLocalHomeomorph w
  obtain ⟨e₁, he₁, hpe₁⟩ := hc₁.isLocalHomeomorph (A w)
  set y : S₁ := q x with hy
  let W : Set ℂ := e₀.source ∩ p₀ ⁻¹' (chartAt ℂ x).source ∩
    (fun w' => p₁ (A w')) ⁻¹' (chartAt ℂ y).source ∩ A ⁻¹' e₁.source
  let V₁ : Set ℂ := e₁.source ∩ p₁ ⁻¹' (chartAt ℂ y).source
  have hWo : IsOpen W :=
    ((e₀.open_source.inter (hc₀.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)).inter
      ((hc₁.continuous.comp hAc).isOpen_preimage _ (chartAt ℂ y).open_source)).inter
      (hAc.isOpen_preimage _ e₁.open_source)
  have hV₁o : IsOpen V₁ := e₁.open_source.inter (hc₁.continuous.isOpen_preimage _ (chartAt ℂ y).open_source)
  have hpw : p₀ w = (chartAt ℂ x).symm z := hw
  have hqw : q (p₀ w) = p₁ (A w) := hq w
  have hwW : w ∈ W := ⟨⟨⟨he₀, by rw [Set.mem_preimage, hpw]; exact (chartAt ℂ x).map_target hz1⟩, by
      rw [Set.mem_preimage, ← hqw, hpw]; exact hz2⟩, he₁⟩
  let ψ₀ : ℂ → ℂ := fun w' => chartAt ℂ x (p₀ w')
  let ψ₁ : ℂ → ℂ := fun v => chartAt ℂ y (p₁ v)
  have hψ₀d : DifferentiableOn ℂ ψ₀ W := fun w' hw' =>
    (s22tc_d_chart (hd₀ w') x hw'.1.1.2).differentiableWithinAt
  have hψ₀i : InjOn ψ₀ W := by
    intro a ha b hb hab
    have h1 : p₀ a = p₀ b := (chartAt ℂ x).injOn ha.1.1.2 hb.1.1.2 hab
    rw [hpe₀] at h1
    exact e₀.injOn ha.1.1.1 hb.1.1.1 h1
  have hψ₁d : DifferentiableOn ℂ ψ₁ V₁ := fun v hv =>
    (s22tc_d_chart (hd₁ v) y hv.2).differentiableWithinAt
  have hψ₁i : InjOn ψ₁ V₁ := by
    intro a ha b hb hab
    have h1 : p₁ a = p₁ b := (chartAt ℂ y).injOn ha.2 hb.2 hab
    rw [hpe₁] at h1
    exact e₁.injOn ha.1 hb.1 h1
  have h0 : IsKQC ψ₀ W 1 := isKQC_one_of_conformal hWo ⟨hψ₀d, hψ₀i, rfl⟩
  have h1 : IsKQC ψ₁ V₁ 1 := isKQC_one_of_conformal hV₁o ⟨hψ₁d, hψ₁i, rfl⟩
  have hAW : IsKQC (fun v => A v) W K := ac_t_isKQC_restrict hK hWo (subset_univ _)
  have hsubA : (fun v => A v) '' W ⊆ V₁ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha.2, ha.1.2⟩
  have h2 : IsKQC (ψ₁ ∘ fun v => A v) W (K * 1) := thm7_1_comp hAW h1 hsubA
  have h3 : IsKQC (Function.invFunOn ψ₀ W) (ψ₀ '' W) 1 := thm7_2_inv h0
  have hsubI : Function.invFunOn ψ₀ W '' (ψ₀ '' W) ⊆ W := by
    rintro _ ⟨u, hu, rfl⟩
    exact Function.invFunOn_mem hu
  have h4 := thm7_1_comp h3 h2 hsubI
  rw [one_mul, mul_one] at h4
  have hUo : IsOpen (ψ₀ '' W) := isOpen_image_of_isKQC h0
  have hψ₀w : ψ₀ w = z := by
    simp only [ψ₀]; rw [hpw]; exact (chartAt ℂ x).right_inv hz1
  have hUD : ψ₀ '' W ⊆ localMapDomain q x := by
    rintro _ ⟨w', hw', rfl⟩
    refine ⟨(chartAt ℂ x).map_source hw'.1.1.2, ?_⟩
    show q ((chartAt ℂ x).symm (chartAt ℂ x (p₀ w'))) ∈ (chartAt ℂ (q x)).source
    rw [(chartAt ℂ x).left_inv hw'.1.1.2, hq]
    exact hw'.1.2
  refine ⟨ψ₀ '' W, hUo, ⟨w, hwW, hψ₀w⟩, hUD, ad_isKQC_congr h4 ?_⟩
  rintro _ ⟨w', hw', rfl⟩
  have e1 : Function.invFunOn ψ₀ W (ψ₀ w') = w' := hψ₀i.leftInvOn_invFunOn hw'
  simp only [Function.comp_apply, e1]
  show chartAt ℂ (q x) (q ((chartAt ℂ x).symm (chartAt ℂ x (p₀ w')))) = ψ₁ (A w')
  rw [(chartAt ℂ x).left_inv hw'.1.1.2, hq]

/-- Genus one, the tori: an orientation preserving homeomorphism `ℂ/Λ₀ → ℂ/Λ₁` lifts to `F` with
`F(z + λ) = F(z) + A λ` (`A` `ℝ`-linear, `det A > 0` by `s24q_torus_det_pos`); the affine map descends to a q.c. map
homotopic to `f` (equivariant straight-line homotopy; `affine_isC1Quasiconformal`). -/
theorem s24q_torus_qc [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {L₀ L₁ : PeriodPair} {p₀ : ℂ → S₀} {p₁ : ℂ → S₁}
    (hp₀ : IsCoveringMap p₀ ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀ ∧ Function.Surjective p₀ ∧
      ∀ z w, p₀ z = p₀ w ↔ z - w ∈ L₀.lattice)
    (hp₁ : IsCoveringMap p₁ ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₁ ∧ Function.Surjective p₁ ∧
      ∀ z w, p₁ z = p₁ w ↔ z - w ∈ L₁.lattice)
    (f : S₀ ≃ₜ S₁) (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x)) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  obtain ⟨hc₀, hd₀, hs₀, hf₀⟩ := hp₀
  obtain ⟨hc₁, hd₁, hs₁, hf₁⟩ := hp₁
  obtain ⟨F, hF⟩ := s24q_tq_homeo hc₀ hs₀ hf₀ hc₁ hs₁ hf₁ f
  obtain ⟨A, hdet, hA1, hA3, hFA⟩ := s24q_tq_affine hc₀ hd₀ hf₀ hc₁ hd₁ hf₁ f hf hF
  obtain ⟨q, hq⟩ := s24q_tq_q hc₀ hs₀ hf₀ hc₁ hs₁ hf₁ hdet hA1 hA3
  exact ⟨q, s24q_tq_qc hc₀ hd₀ hs₀ hc₁ hd₁ hdet hq,
    s24q_tq_homotopy hc₀ hs₀ hf₀ hc₁ hf₁ f hF hA1 hFA hq⟩

/-- Trivial fundamental group of a charted surface gives simple connectedness. -/
theorem s24q_sm_simply {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S] (x₀ : S)
    (htriv : ∀ γ : FundamentalGroup S x₀, γ = 1) : SimplyConnectedSpace S := by
  classical
  have : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  have : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  refine simply_connected_iff_paths_homotopic.mpr ⟨inferInstance, fun x y => ⟨fun u v => ?_⟩⟩
  have hx : ∀ γ : FundamentalGroup S x, γ = 1 := by
    intro γ
    obtain ⟨γ', rfl⟩ :=
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ x).surjective γ
    rw [htriv γ', map_one]
  have h1 : u.trans v.symm = Path.Homotopic.Quotient.refl x :=
    congrArg CategoryTheory.End.asHom (hx (FundamentalGroup.fromPath (u.trans v.symm)))
  have h2 := congrArg (fun η : Path.Homotopic.Quotient x x => η.trans v) h1
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] using h2

/-- Genus zero, the model: a closed surface of genus `0` (compact and simply connected, since `π₁` is trivial) is
biholomorphic to `ℂ̂` (`RiemannDynamics.uniformization_trichotomy`; the disc and the plane are not compact).  Nothing
beyond "compact and simply connected" is needed from `thm22_3_classification`. -/
theorem s24q_sphere_model {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hS : HasGenus S 0) : ∃ c : S ≃ₜ OnePoint ℂ, IsBiholomorphic (c : S → OnePoint ℂ) := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  have hcomp : CompactSpace S := hS.1
  obtain ⟨e⟩ := hS.2 x₀
  have hsub : Subsingleton (surfaceGroup 0) :=
    (PresentedGroup.mk_surjective _).subsingleton
  have htriv : ∀ γ : FundamentalGroup S x₀, γ = 1 := fun γ => e.injective (Subsingleton.elim _ _)
  have : SimplyConnectedSpace S := s24q_sm_simply x₀ htriv
  have : SecondCountableTopology S := k22u_compact_secondCountable
  rcases RiemannDynamics.uniformization_trichotomy S with h | h | h
  · exfalso
    obtain ⟨d⟩ := h
    exact (k22u_compact_separation hcomp).2 ⟨d, k22u_diffeomorph_isBiholomorphic d⟩
  · exfalso
    obtain ⟨d⟩ := h
    exact (k22u_compact_separation hcomp).1 ⟨d, k22u_diffeomorph_isBiholomorphic d⟩
  · obtain ⟨d⟩ := h
    exact ⟨d.toHomeomorph, k22u_diffeomorph_isBiholomorphic d⟩

/-- A homeomorphism of `ℂ̂` fixing `0` and `∞` is a homeomorphism-like map `φ` of `ℂ`. -/
theorem s24q_sp_phi (h : OnePoint ℂ ≃ₜ OnePoint ℂ) (h0 : h ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ))
    (hinf : h OnePoint.infty = OnePoint.infty) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Function.Injective φ ∧ φ 0 = 0 ∧
      (∀ z : ℂ, h (z : OnePoint ℂ) = ((φ z : ℂ) : OnePoint ℂ)) ∧
      Filter.Tendsto (fun z => ‖φ z‖) (cocompact ℂ) atTop := by
  classical
  have hfin : ∀ z : ℂ, ∃ w : ℂ, h (z : OnePoint ℂ) = (w : OnePoint ℂ) := by
    intro z
    have : h (z : OnePoint ℂ) ≠ OnePoint.infty := by
      intro hz
      rw [← hinf] at hz
      exact OnePoint.coe_ne_infty z (h.injective hz)
    exact OnePoint.ne_infty_iff_exists.mp this |>.imp fun w hw => hw.symm
  choose φ hφ using hfin
  have hcoe : (fun z : ℂ => ((φ z : ℂ) : OnePoint ℂ)) = (fun z : ℂ => h ((z : ℂ) : OnePoint ℂ)) := by
    funext z; exact (hφ z).symm
  have hcont : Continuous φ := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff]
    show Continuous fun z : ℂ => ((φ z : ℂ) : OnePoint ℂ)
    rw [hcoe]
    exact h.continuous.comp OnePoint.continuous_coe
  refine ⟨φ, hcont, ?_, ?_, hφ, ?_⟩
  · intro a b hab
    have : h (a : OnePoint ℂ) = h (b : OnePoint ℂ) := by rw [hφ, hφ, hab]
    exact OnePoint.coe_injective (h.injective this)
  · have := hφ 0
    rw [h0] at this
    exact (OnePoint.coe_injective this).symm
  · have h1 : Filter.Tendsto (fun z : ℂ => h (z : OnePoint ℂ)) (cocompact ℂ) (𝓝 OnePoint.infty) := by
      have h2 : Filter.Tendsto (fun z : ℂ => (z : OnePoint ℂ)) (cocompact ℂ) (𝓝 OnePoint.infty) := by
        rw [← coclosedCompact_eq_cocompact]
        exact OnePoint.tendsto_coe_infty
      have h3 := (h.continuous.tendsto OnePoint.infty).comp h2
      rwa [hinf] at h3
    have h5 : Filter.Tendsto (fun z : ℂ => ((φ z : ℂ) : OnePoint ℂ)) (cocompact ℂ) (𝓝 OnePoint.infty) := by
      rw [hcoe]; exact h1
    have h4 : Filter.Tendsto φ (cocompact ℂ) (coclosedCompact ℂ) := by
      rw [← OnePoint.comap_coe_nhds_infty, Filter.tendsto_comap_iff]
      exact h5
    rw [coclosedCompact_eq_cocompact] at h4
    exact tendsto_norm_cocompact_atTop.comp h4

/-- Winding `+1` of the image of every circle about its centre, from the local winding at the centre. -/
theorem s24q_sp_winding_all {F : ℂ → ℂ} (hFc : Continuous F) (hFi : Function.Injective F)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (0 + ρ * Complex.exp (2 * π * Complex.I * t)) - F 0) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {R : ℝ} (hR : 0 < R) {L : ℝ → ℂ} (hL : ContinuousOn L (Set.Icc 0 1))
    (hLe : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = F (R * Complex.exp (2 * π * Complex.I * t)) - F 0) :
    L 1 - L 0 = 2 * π * Complex.I := by
  obtain ⟨ρ₁, hρ₁, hρ⟩ := hw
  let r₀ : ℝ := ρ₁ / 2
  have hr₀ : 0 < r₀ := half_pos hρ₁
  let H : ℝ → ℝ → ℂ := fun s t =>
    F (((((1 - s) * r₀ + s * R : ℝ)) : ℂ) * Complex.exp (2 * π * Complex.I * t)) - F 0
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (1 - s) * r₀ + s * R := fun s hs => by
    rcases le_or_gt s (1 / 2) with h | h
    · nlinarith [mul_nonneg hs.1 hR.le, mul_pos (show (0:ℝ) < 1 - s by linarith) hr₀]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) hr₀.le, mul_pos (show (0:ℝ) < s by linarith) hR]
  have hHc : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry H) := by
      simp only [H]
      have := hFc
      fun_prop
    exact this.continuousOn
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H s 0 := by
    intro s _
    simp only [H]
    have : Complex.exp (2 * π * Complex.I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * Complex.I * ((0 : ℝ) : ℂ)) := by
      simp [Complex.exp_two_pi_mul_I]
    rw [this]
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H s t ≠ 0 := by
    intro s hs t _ h0
    have h1 : F (((((1 - s) * r₀ + s * R : ℝ)) : ℂ) * Complex.exp (2 * π * Complex.I * t)) = F 0 :=
      sub_eq_zero.mp h0
    have h2 := hFi h1
    have h3 : ((((1 - s) * r₀ + s * R : ℝ)) : ℂ) = 0 ∨ Complex.exp (2 * π * Complex.I * t) = 0 :=
      mul_eq_zero.mp h2
    rcases h3 with h3 | h3
    · exact (hpos s hs).ne' (by exact_mod_cast h3)
    · exact Complex.exp_ne_zero _ h3
  obtain ⟨L₀, hL₀c, hL₀e⟩ := exists_continuousOn_log_lift (γ := fun t => H 0 t) (w := 0)
    (by
      have : Continuous (fun t => H 0 t) := by
        simp only [H]; have := hFc; fun_prop
      exact this.continuousOn)
    (fun t ht => hne 0 ⟨le_refl _, zero_le_one⟩ t ht)
  have hL₀ : L₀ 1 - L₀ 0 = 2 * π * Complex.I := by
    refine hρ r₀ hr₀ (by simp only [r₀]; linarith) L₀ hL₀c ?_
    intro t ht
    have := hL₀e t ht
    simp only [H, sub_zero] at this
    rw [this]
    simp
  have := lift_change_eq_of_homotopy (H := H) (w := 0) hHc hper (fun s hs t ht => hne s hs t ht) hL₀c hL
    (by intro t ht; rw [hL₀e t ht, sub_zero]) (by
      intro t ht
      rw [hLe t ht, sub_zero]
      simp [H])
  rw [← this, hL₀]

/-- The lift of `z ↦ φ (exp z)` through `exp`, with degree one. -/
theorem s24q_sp_lift {φ : ℂ → ℂ} (hc : Continuous φ) (hi : Function.Injective φ) (h0 : φ 0 = 0)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = φ (0 + ρ * Complex.exp (2 * π * Complex.I * t)) - φ 0) →
        Lg 1 - Lg 0 = 2 * π * Complex.I) :
    ∃ H : ℂ → ℂ, Continuous H ∧ (∀ z, Complex.exp (H z) = φ (Complex.exp z)) ∧
      ∀ z, H (z + 2 * π * Complex.I) = H z + 2 * π * Complex.I := by
  classical
  have hne : ∀ z : ℂ, φ (Complex.exp z) ≠ 0 := by
    intro z h
    rw [← h0] at h
    exact Complex.exp_ne_zero z (hi h)
  let g₀ : ℂ → {w : ℂ // w ≠ 0} := fun z => ⟨φ (Complex.exp z), hne z⟩
  have hg₀ : Continuous g₀ := (hc.comp Complex.continuous_exp).subtype_mk _
  have hcov := Complex.isCoveringMap_exp
  have hsurj : Function.Surjective (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) := by
    rintro ⟨w, hw0⟩
    exact ⟨Complex.log w, Subtype.ext (Complex.exp_log hw0)⟩
  obtain ⟨H, hHc, hH⟩ := s24q_tq_lift hcov hsurj hg₀
  have hHe : ∀ z, Complex.exp (H z) = φ (Complex.exp z) := fun z => congrArg Subtype.val (hH z)
  refine ⟨H, hHc, hHe, ?_⟩
  have h2π : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- the degree
  obtain ⟨k, hk⟩ : ∃ k : ℤ, H (0 + 2 * π * Complex.I) = H 0 + k * (2 * π * Complex.I) := by
    have : Complex.exp (H (0 + 2 * π * Complex.I)) = Complex.exp (H 0) := by
      rw [hHe, hHe, zero_add, Complex.exp_two_pi_mul_I, Complex.exp_zero]
    exact Complex.exp_eq_exp_iff_exists_int.mp this
  have hdeg : ∀ z, H (z + 2 * π * Complex.I) = H z + k * (2 * π * Complex.I) := by
    intro z
    have hcomp : (fun z => (⟨Complex.exp (H (z + 2 * π * Complex.I)), Complex.exp_ne_zero _⟩ : {w : ℂ // w ≠ 0})) =
        fun z => (⟨Complex.exp (H z + k * (2 * π * Complex.I)), Complex.exp_ne_zero _⟩ : {w : ℂ // w ≠ 0}) := by
      funext z
      apply Subtype.ext
      simp only
      rw [hHe, Complex.exp_periodic z, Complex.exp_add, hHe, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have := hcov.eq_of_comp_eq (g₁ := fun z => H (z + 2 * π * Complex.I)) (g₂ := fun z => H z + k * (2 * π * Complex.I))
      (by fun_prop) (by fun_prop) hcomp 0 (by simpa using hk)
    exact congrFun this z
  -- `k = 1` from the winding
  have hk1 : (k : ℂ) = 1 := by
    let L : ℝ → ℂ := fun t => H (2 * π * Complex.I * t)
    have hLc : ContinuousOn L (Icc 0 1) := by
      have : Continuous L := by simp only [L]; fun_prop
      exact this.continuousOn
    have hw1 := s24q_sp_winding_all hc hi hw (R := 1) one_pos hLc (by
      intro t _
      simp only [L, hHe]
      simp [h0])
    have h1 : L 1 - L 0 = k * (2 * π * Complex.I) := by
      simp only [L]
      have := hk
      simp only [zero_add] at this
      simp [this]
    rw [h1] at hw1
    exact mul_right_cancel₀ h2π (by simpa using hw1)
  intro z
  rw [hdeg z, hk1, one_mul]

/-- The equivariant straight-line homotopy of `exp ∘ H ∘ log` to the identity: a continuous map
`Ψ : [0,1] × ℂ → ℂ` with `Ψ (t, exp z) = exp ((1-t) H z + t z)`, `Ψ (t, 0) = 0`, and the norm bounds. -/
theorem s24q_sp_psi {φ : ℂ → ℂ} (hc : Continuous φ) (h0 : φ 0 = 0) {H : ℂ → ℂ} (hHc : Continuous H)
    (hHe : ∀ z, Complex.exp (H z) = φ (Complex.exp z))
    (hHp : ∀ z, H (z + 2 * π * Complex.I) = H z + 2 * π * Complex.I) :
    ∃ Ψ : unitInterval × ℂ → ℂ, Continuous Ψ ∧ (∀ t, Ψ (t, 0) = 0) ∧
      (∀ t z, Ψ (t, Complex.exp z) = Complex.exp (((1 - (t : ℝ) : ℝ) : ℂ) * H z + ((t : ℝ) : ℂ) * z)) ∧
      (∀ t w, ‖Ψ (t, w)‖ ≤ max ‖φ w‖ ‖w‖) ∧ (∀ t w, w ≠ 0 → min ‖φ w‖ ‖w‖ ≤ ‖Ψ (t, w)‖) := by
  classical
  have h2π : (2 * (π : ℂ) * Complex.I) = 2 * π * Complex.I := rfl
  have hHnat : ∀ (n : ℕ) z, H (z + n * (2 * π * Complex.I)) = H z + n * (2 * π * Complex.I) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [show z + ((n + 1 : ℕ) : ℂ) * (2 * π * Complex.I) = z + n * (2 * π * Complex.I) + 2 * π * Complex.I by
        push_cast; ring, hHp, ih z]
      push_cast; ring
  have hHn : ∀ (n : ℤ) z, H (z + n * (2 * π * Complex.I)) = H z + n * (2 * π * Complex.I) := by
    intro n z
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
    · subst hm; exact_mod_cast hHnat m z
    · subst hm
      have h1 := hHnat m (z + ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I))
      rw [show z + ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) + (m : ℂ) * (2 * π * Complex.I) = z by push_cast; ring] at h1
      push_cast at h1 ⊢
      linear_combination -h1
  let Hh : unitInterval × ℂ → ℂ := fun u => ((1 - (u.1 : ℝ) : ℝ) : ℂ) * H u.2 + ((u.1 : ℝ) : ℂ) * u.2
  have hHhc : Continuous Hh := by
    simp only [Hh]
    fun_prop
  let p : ℂ → {w : ℂ // w ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hpc : Continuous p := Complex.continuous_exp.subtype_mk _
  have hps : Function.Surjective p := by
    rintro ⟨w, hw⟩
    exact ⟨Complex.log w, Subtype.ext (Complex.exp_log hw)⟩
  have hpo : IsOpenMap p := Complex.isCoveringMap_exp.isLocalHomeomorph.isOpenMap
  obtain ⟨Φ, hΦc, hΦ⟩ := s24q_tq_descend2 (p := p) (p' := Complex.exp) hpc hps hpo Complex.continuous_exp
    (φ := Hh) hHhc (by
      intro t z w hzw
      have h1 : Complex.exp z = Complex.exp w := congrArg Subtype.val hzw
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
      simp only [Hh]
      rw [hn, hHn n w]
      rw [show ((1 - (t : ℝ) : ℝ) : ℂ) * (H w + n * (2 * π * Complex.I)) + ((t : ℝ) : ℂ) * (w + n * (2 * π * Complex.I)) =
        (((1 - (t : ℝ) : ℝ) : ℂ) * H w + ((t : ℝ) : ℂ) * w) + n * (2 * π * Complex.I) by push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one])
  let Ψ : unitInterval × ℂ → ℂ := fun u => if hw : u.2 = 0 then 0 else Φ (u.1, ⟨u.2, hw⟩)
  have hΨe : ∀ t z, Ψ (t, Complex.exp z) = Complex.exp (((1 - (t : ℝ) : ℝ) : ℂ) * H z + ((t : ℝ) : ℂ) * z) := by
    intro t z
    simp only [Ψ, dite_eq_right (Complex.exp_ne_zero z)]
    exact hΦ t z
  have hbound : ∀ t w, ‖Ψ (t, w)‖ ≤ max ‖φ w‖ ‖w‖ ∧ (w ≠ 0 → min ‖φ w‖ ‖w‖ ≤ ‖Ψ (t, w)‖) := by
    intro t w
    by_cases hw : w = 0
    · subst hw
      simp [Ψ, h0]
    · have hz : Complex.exp (Complex.log w) = w := Complex.exp_log hw
      set z := Complex.log w
      rw [← hz, hΨe]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hre : (((1 - (t : ℝ) : ℝ) : ℂ) * H z + ((t : ℝ) : ℂ) * z).re =
          (1 - (t : ℝ)) * (H z).re + (t : ℝ) * z.re := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre]
      have e1 : Real.exp (H z).re = ‖φ (Complex.exp z)‖ := by rw [← hHe, Complex.norm_exp]
      have e2 : Real.exp z.re = ‖Complex.exp z‖ := by rw [Complex.norm_exp]
      rw [← e1, ← e2]
      constructor
      · calc Real.exp ((1 - (t : ℝ)) * (H z).re + (t : ℝ) * z.re)
            ≤ Real.exp (max (H z).re z.re) := by
              apply Real.exp_le_exp.mpr
              nlinarith [le_max_left (H z).re z.re, le_max_right (H z).re z.re]
          _ = max (Real.exp (H z).re) (Real.exp z.re) := Real.exp_monotone.map_max
      · intro _
        calc min (Real.exp (H z).re) (Real.exp z.re) = Real.exp (min (H z).re z.re) := by
              rw [Real.exp_monotone.map_min]
          _ ≤ Real.exp ((1 - (t : ℝ)) * (H z).re + (t : ℝ) * z.re) := by
              apply Real.exp_le_exp.mpr
              nlinarith [min_le_left (H z).re z.re, min_le_right (H z).re z.re]
  refine ⟨Ψ, ?_, fun t => by simp [Ψ], hΨe, fun t w => (hbound t w).1, fun t w hw => (hbound t w).2 hw⟩
  -- continuity
  have hΨc : ∀ u : unitInterval × ℂ, ContinuousAt Ψ u := by
    rintro ⟨t₀, w₀⟩
    by_cases hw₀ : w₀ = 0
    · subst hw₀
      have hm : Continuous fun u : unitInterval × ℂ => max ‖φ u.2‖ ‖u.2‖ := by fun_prop
      have hm0 : max ‖φ (0 : ℂ)‖ ‖(0 : ℂ)‖ = 0 := by simp [h0]
      have hΨ0 : Ψ (t₀, 0) = 0 := by simp [Ψ]
      have : Filter.Tendsto Ψ (𝓝 (t₀, (0 : ℂ))) (𝓝 0) := by
        refine squeeze_zero_norm (fun u => (hbound u.1 u.2).1) ?_
        have := hm.tendsto (t₀, (0 : ℂ))
        rwa [hm0] at this
      rw [ContinuousAt, hΨ0]
      exact this
    · let X : Set ℂ := {w | w ≠ 0}
      have hXo : IsOpen X := isOpen_ne
      let ι : unitInterval × {w : ℂ // w ≠ 0} → unitInterval × ℂ := fun u => (u.1, u.2.1)
      have hι : Topology.IsOpenEmbedding ι :=
        Topology.IsOpenEmbedding.id.prodMap hXo.isOpenEmbedding_subtypeVal
      have hΨι : Ψ ∘ ι = Φ := by
        funext u
        simp only [Function.comp_apply, ι, Ψ, dite_eq_right u.2.2]
      have h1 : ContinuousAt (Ψ ∘ ι) (t₀, (⟨w₀, hw₀⟩ : {w : ℂ // w ≠ 0})) := by
        rw [hΨι]; exact hΦc.continuousAt
      exact (hι.continuousAt_iff (g := Ψ) (x := (t₀, (⟨w₀, hw₀⟩ : {w : ℂ // w ≠ 0})))).mp h1
  exact continuous_iff_continuousAt.mpr hΨc

/-- Local winding `+1` transported through conformal charts, from a winding hypothesis on the chart map. -/
theorem s24q_lg_winding_conj' {F h ψ₀ ψ₁ : ℂ → ℂ} {z₀ : ℂ} {U V D : Set ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : IsOpen V) (hD : IsOpen D)
    (hψ₀ : DifferentiableOn ℂ ψ₀ U) (hψ₀i : Set.InjOn ψ₀ U)
    (hψ₁ : DifferentiableOn ℂ ψ₁ V) (hψ₁i : Set.InjOn ψ₁ V)
    (hFc : ContinuousAt F z₀) (hFz : F z₀ ∈ V) (hψD : Set.MapsTo ψ₀ U D)
    (hcomm : ∀ z ∈ U, F z ∈ V → ψ₁ (F z) = h (ψ₀ z))
    (hhc : ContinuousOn h D) (hhi : Set.InjOn h D)
    (hwh : ∃ ρ₂ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ∀ L : ℝ → ℂ, ContinuousOn L (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = h (ψ₀ z₀ + ρ * Complex.exp (2 * π * Complex.I * t)) - h (ψ₀ z₀)) →
        L 1 - L 0 = 2 * π * Complex.I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (z₀ + ρ * Complex.exp (2 * π * Complex.I * t)) - F z₀) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
  classical
  set a : ℂ := ψ₀ z₀ with ha
  have haD : a ∈ D := hψD hz₀
  have hκ₀ : deriv ψ₀ z₀ ≠ 0 := deriv_ne_zero_of_injOn hU hψ₀ hψ₀i hz₀
  have hκ₁ : deriv ψ₁ (F z₀) ≠ 0 := deriv_ne_zero_of_injOn hV hψ₁ hψ₁i hFz
  set κ₀ := deriv ψ₀ z₀ with hκ₀def
  set κ₁ := deriv ψ₁ (F z₀) with hκ₁def
  have hd₀ : HasDerivAt ψ₀ κ₀ z₀ := (hψ₀.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hd₁ : HasDerivAt ψ₁ κ₁ (F z₀) := (hψ₁.differentiableAt (hV.mem_nhds hFz)).hasDerivAt
  obtain ⟨ρ₂, hρ₂, hrc⟩ := hwh
  have hκ₀pos : 0 < ‖κ₀‖ := norm_pos_iff.mpr hκ₀
  have hκ₁pos : 0 < ‖κ₁‖ := norm_pos_iff.mpr hκ₁
  obtain ⟨rD, hrD, hrDsub⟩ := Metric.isOpen_iff.mp hD a haD
  -- eventual properties near `z₀`
  have hev₀ : ∀ᶠ z in 𝓝 z₀, ‖ψ₀ z - a - (z - z₀) * κ₀‖ ≤ (‖κ₀‖ / 2) * ‖z - z₀‖ := by
    have := hd₀.isLittleO.def (half_pos hκ₀pos)
    filter_upwards [this] with z hz
    simpa [smul_eq_mul] using hz
  have hev₁ : ∀ᶠ z in 𝓝 z₀, ‖ψ₁ (F z) - ψ₁ (F z₀) - (F z - F z₀) * κ₁‖ ≤ (‖κ₁‖ / 2) * ‖F z - F z₀‖ := by
    have := hd₁.isLittleO.def (half_pos hκ₁pos)
    have h2 := hFc.tendsto.eventually this
    filter_upwards [h2] with z hz
    simpa [smul_eq_mul] using hz
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU.mem_nhds hz₀
  have hevV : ∀ᶠ z in 𝓝 z₀, F z ∈ V := hFc.tendsto.eventually (hV.mem_nhds hFz)
  have hevball : ∀ᶠ z in 𝓝 z₀, dist (ψ₀ z) a < rD := by
    have hc : ContinuousAt ψ₀ z₀ := (hψ₀.differentiableAt (hU.mem_nhds hz₀)).continuousAt
    exact hc.tendsto.eventually (Metric.ball_mem_nhds a hrD)
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff.mp
    (hev₀.and (hev₁.and (hevU.and (hevV.and hevball))))
  refine ⟨min r (min (ρ₂ / ‖κ₀‖) (rD / ‖κ₀‖)), lt_min hr (lt_min (div_pos hρ₂ hκ₀pos) (div_pos hrD hκ₀pos)), ?_⟩
  intro ρ hρ0 hρ1 Lg hLg hLe
  have hρr : ρ < r := lt_of_lt_of_le hρ1 (min_le_left _ _)
  have hρρ₂ : ‖κ₀‖ * ρ < ρ₂ := by
    have := lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ hκ₀pos] at this; linarith
  have hρD : ‖κ₀‖ * ρ < rD := by
    have := lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ hκ₀pos] at this; linarith
  -- circles
  let E : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I)
  have hEn : ∀ x, ‖E x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I x
  have hE : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * t) = E (2 * π * t) := by
    intro t; simp only [E]; congr 1; push_cast; ring
  have hE1 : ∀ x : ℝ, E (2 * π * (1 + x)) = E (2 * π * x) := by
    intro x
    simp only [E]
    have : ((2 * π * (1 + x) : ℝ) : ℂ) * Complex.I = (2 * π * Complex.I) + ((2 * π * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  let c : ℝ → ℂ := fun t => z₀ + ρ * E (2 * π * t)
  have hcc : Continuous c := by
    have : Continuous E := by simp only [E]; fun_prop
    simp only [c]; fun_prop
  have hc1 : c 1 = c 0 := by
    have := hE1 0
    simp only [c, mul_one, add_zero, mul_zero] at this ⊢
    rw [this]
  have hcz : ∀ t, ‖c t - z₀‖ = ρ := by
    intro t; simp only [c, add_sub_cancel_left, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hcd : ∀ t, dist (c t) z₀ < r := fun t => by rw [dist_eq_norm, hcz]; exact hρr
  have hcne : ∀ t, c t ≠ z₀ := fun t h => by
    have := hcz t; rw [h, sub_self, norm_zero] at this; exact absurd this.symm hρ0.ne'
  have hLe' : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) = F (c t) - F z₀ := by
    intro t ht; rw [hLe t ht]; simp only [c, hE]
  have hψ₁z : ψ₁ (F z₀) = h a := hcomm z₀ hz₀ hFz
  let G' : ℝ → ℂ := fun t => ψ₁ (F (c t)) - ψ₁ (F z₀)
  have hG'eq : ∀ t, G' t = h (ψ₀ (c t)) - h a := by
    intro t
    simp only [G']
    rw [hcomm (c t) (hP (hcd t)).2.2.1 (hP (hcd t)).2.2.2.1, hψ₁z]
  have hcU : ∀ t, c t ∈ U := fun t => (hP (hcd t)).2.2.1
  have hψ₀c : ContinuousOn (fun t => ψ₀ (c t)) (Icc 0 1) :=
    hψ₀.continuousOn.comp hcc.continuousOn (fun t _ => hcU t)
  have hG'cont : ContinuousOn G' (Icc 0 1) := by
    have : ContinuousOn (fun t => h (ψ₀ (c t)) - h a) (Icc 0 1) :=
      (hhc.comp hψ₀c (fun t _ => hψD (hcU t))).sub continuousOn_const
    exact this.congr fun t _ => hG'eq t
  have hG'ne : ∀ t, G' t ≠ 0 := by
    intro t heq
    rw [hG'eq t, sub_eq_zero] at heq
    exact hcne t (hψ₀i (hcU t) hz₀ (hhi (hψD (hcU t)) haD heq))
  obtain ⟨M', hM'c, hM'e⟩ := exists_continuousOn_log_lift (γ := G') (w := 0) hG'cont
    (fun t _ => hG'ne t)
  -- Step A: transfer of the winding through `ψ₁`
  have hStepA : M' 1 - M' 0 = Lg 1 - Lg 0 := by
    have hβc : ContinuousOn (fun t => κ₁ * (F (c t) - F z₀)) (Icc 0 1) := by
      have : ContinuousOn (fun t => κ₁ * Complex.exp (Lg t)) (Icc 0 1) :=
        continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn hLg)
      exact this.congr fun t ht => by simp only [hLe' t ht]
    refine lift_change_eq_of_norm_sub_lt (γ := G') (β := fun t => κ₁ * (F (c t) - F z₀))
      (L := M') (M := fun t => Lg t + Complex.log κ₁) hG'cont hβc ?_ ?_ ?_ hM'c (hLg.add continuousOn_const) ?_ ?_
      |>.trans (by simp)
    · simp only [G', hc1]
    · simp only [hc1]
    · intro t ht
      have hne : F (c t) - F z₀ ≠ 0 := by rw [← hLe' t ht]; exact Complex.exp_ne_zero _
      have h1 := (hP (hcd t)).2.1
      have h2 : G' t - κ₁ * (F (c t) - F z₀) = ψ₁ (F (c t)) - ψ₁ (F z₀) - (F (c t) - F z₀) * κ₁ := by
        simp only [G']; ring
      rw [h2, norm_mul]
      have hpos : 0 < ‖F (c t) - F z₀‖ := norm_pos_iff.mpr hne
      calc _ ≤ ‖κ₁‖ / 2 * ‖F (c t) - F z₀‖ := h1
        _ < ‖κ₁‖ * ‖F (c t) - F z₀‖ := by nlinarith
    · intro t ht
      rw [hM'e t ht, sub_zero]
    · intro t ht
      rw [Complex.exp_add, hLe' t ht, Complex.exp_log hκ₁]; ring
  -- Step B: transfer of the winding through `ψ₀`
  have hEc : Continuous E := by simp only [E]; fun_prop
  let e : ℝ → ℂ := fun t => ψ₀ (c t) - a
  let k : ℝ → ℂ := fun t => (κ₀ * ρ) * E (2 * π * t)
  have hk : ∀ t, k t = (c t - z₀) * κ₀ := by intro t; simp only [k, c]; ring
  have hkn : ∀ t, ‖k t‖ = ‖κ₀‖ * ρ := by
    intro t; simp only [k, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hee : ∀ t, ‖e t - k t‖ ≤ ‖κ₀‖ / 2 * ρ := by
    intro t
    have h1 := (hP (hcd t)).1
    rw [hcz t] at h1
    have : e t - k t = ψ₀ (c t) - a - (c t - z₀) * κ₀ := by simp only [e, hk]
    rw [this]; exact h1
  have hen : ∀ t, ‖e t‖ < rD := fun t => by
    have := (hP (hcd t)).2.2.2.2
    rwa [dist_eq_norm] at this
  have hec : ContinuousOn e (Icc 0 1) := hψ₀c.sub continuousOn_const
  have hkc : Continuous k := by simp only [k]; fun_prop
  have hEp : E (2 * π * 1) = E (2 * π * 0) := by simpa using hE1 0
  let u : ℝ → ℝ → ℂ := fun s t => (1 - (s : ℂ)) * e t + (s : ℂ) * k t
  have hu : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc 0 1) := by
    have he2 : ContinuousOn (fun p : ℝ × ℝ => e p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      hec.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hk2 : ContinuousOn (fun p : ℝ × ℝ => k p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      (hkc.comp continuous_snd).continuousOn
    have hs1 : Continuous fun p : ℝ × ℝ => (1 - (p.1 : ℂ)) := by fun_prop
    have hs2 : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := by fun_prop
    exact (hs1.continuousOn.mul he2).add (hs2.continuousOn.mul hk2)
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, u s 1 = u s 0 := by
    intro s _
    have : e 1 = e 0 := by simp only [e, hc1]
    have h2 : k 1 = k 0 := by simp only [k, hEp]
    simp only [u, this, h2]
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, u s t ≠ 0 := by
    intro s hs t _ h0
    have h1 : u s t = k t + (1 - (s : ℂ)) * (e t - k t) := by simp only [u]; ring
    rw [h1] at h0
    have h2 : ‖k t‖ = ‖(1 - (s : ℂ)) * (e t - k t)‖ :=
      (congrArg (fun x => ‖x‖) (show k t = -((1 - (s : ℂ)) * (e t - k t)) by linear_combination h0)).trans
        (norm_neg _)
    rw [hkn t, norm_mul] at h2
    have h3 : ‖(1 - (s : ℂ))‖ = 1 - s := by
      have : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    rw [h3] at h2
    have := hee t
    nlinarith [hs.1, hs.2, norm_nonneg (e t - k t), mul_pos hκ₀pos hρ0]
  have hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a + u s t ∈ D := by
    intro s hs t _
    apply hrDsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h3 : ‖(1 - (s : ℂ))‖ = 1 - s := by
      have : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h4 : ‖(s : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc ‖u s t‖ ≤ ‖(1 - (s : ℂ)) * e t‖ + ‖(s : ℂ) * k t‖ := norm_add_le _ _
      _ = (1 - s) * ‖e t‖ + s * (‖κ₀‖ * ρ) := by rw [norm_mul, norm_mul, h3, h4, hkn]
      _ ≤ max ‖e t‖ (‖κ₀‖ * ρ) := by
          nlinarith [le_max_left ‖e t‖ (‖κ₀‖ * ρ), le_max_right ‖e t‖ (‖κ₀‖ * ρ), hs.1, hs.2,
            mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (le_max_left ‖e t‖ (‖κ₀‖ * ρ))),
            mul_nonneg hs.1 (sub_nonneg.2 (le_max_right ‖e t‖ (‖κ₀‖ * ρ)))]
      _ < rD := max_lt (hen t) hρD
  have hkD : ∀ t, a + k t ∈ D := fun t =>
    hrDsub (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hkn]; exact hρD)
  have hkne : ∀ t, k t ≠ 0 := fun t h0 => by
    have := hkn t
    rw [h0, norm_zero] at this
    exact (mul_pos hκ₀pos hρ0).ne this
  have hNcont : ContinuousOn (fun t => h (a + k t) - h a) (Icc 0 1) :=
    (hhc.comp (continuousOn_const.add hkc.continuousOn) (fun t _ => hkD t)).sub continuousOn_const
  have hNne : ∀ t ∈ Icc (0 : ℝ) 1, h (a + k t) - h a ≠ 0 := fun t _ h0 =>
    hkne t (by simpa using hhi (hkD t) haD (sub_eq_zero.mp h0))
  obtain ⟨N, hNc, hNe⟩ := exists_continuousOn_log_lift (γ := fun t => h (a + k t) - h a) (w := 0)
    hNcont hNne
  have hB1 : M' 1 - M' 0 = N 1 - N 0 := by
    refine s24q_lw_h_homotopy hhc hhi hu hper hne haD hDm hM'c hNc ?_ ?_
    · intro t ht
      have : a + u 0 t = ψ₀ (c t) := by simp only [u, e]; simp
      rw [this, hM'e t ht, sub_zero, hG'eq]
    · intro t ht
      have : u 1 t = k t := by simp [u]
      rw [this, hNe t ht, sub_zero]
  -- rotation of the circle
  have hEadd : ∀ x y : ℝ, E (x + y) = E x * E y := by
    intro x y; simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  let θ : ℝ := Complex.arg κ₀ / (2 * π)
  have hκE : κ₀ = (‖κ₀‖ : ℂ) * E (Complex.arg κ₀) := (Complex.norm_mul_exp_arg_mul_I κ₀).symm
  let v : ℝ → ℝ → ℂ := fun s t => ((‖κ₀‖ * ρ : ℝ) : ℂ) * E (2 * π * (t + (1 - s) * θ))
  have hv0 : ∀ t, v 0 t = k t := by
    intro t
    have h2 : 2 * π * (t + (1 - 0) * θ) = 2 * π * t + Complex.arg κ₀ := by
      simp only [θ]; field_simp; ring
    simp only [v, h2, hEadd, k]
    conv_rhs => rw [hκE]
    push_cast; ring
  have hv1 : ∀ t, v 1 t = ((‖κ₀‖ * ρ : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * t) := by
    intro t; simp only [v, sub_self, zero_mul, add_zero, hE]
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : Continuous (Function.uncurry v) := by
      simp only [v, E]; fun_prop
    exact this.continuousOn
  have hvper : ∀ s ∈ Icc (0 : ℝ) 1, v s 1 = v s 0 := by
    intro s _
    simp only [v, zero_add]
    rw [hE1]
  have hvn : ∀ s t, ‖v s t‖ = ‖κ₀‖ * ρ := by
    intro s t
    show ‖((‖κ₀‖ * ρ : ℝ) : ℂ) * E (2 * π * (t + (1 - s) * θ))‖ = _
    rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hκ₀pos hρ0)]
  have hvne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, v s t ≠ 0 := fun s _ t _ h0 => by
    have := hvn s t
    rw [h0, norm_zero] at this
    exact (mul_pos hκ₀pos hρ0).ne this
  have hvD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a + v s t ∈ D := fun s _ t _ =>
    hrDsub (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]; exact hρD)
  have hvt1 : Continuous (fun t => v 1 t) := by simp only [v, E]; fun_prop
  have hN'cont : ContinuousOn (fun t => h (a + v 1 t) - h a) (Icc 0 1) :=
    (hhc.comp (continuousOn_const.add hvt1.continuousOn)
      (fun t ht => hvD 1 ⟨zero_le_one, le_refl _⟩ t ht)).sub continuousOn_const
  obtain ⟨N', hN'c, hN'e⟩ := exists_continuousOn_log_lift (γ := fun t => h (a + v 1 t) - h a) (w := 0)
    hN'cont (fun t ht h0 => hvne 1 ⟨zero_le_one, le_refl _⟩ t ht
      (by simpa using hhi (hvD 1 ⟨zero_le_one, le_refl _⟩ t ht) haD (sub_eq_zero.mp h0)))
  have hB2 : N 1 - N 0 = N' 1 - N' 0 := by
    refine s24q_lw_h_homotopy hhc hhi hvc hvper hvne haD hvD hNc hN'c ?_ ?_
    · intro t ht
      rw [hv0, hNe t ht, sub_zero]
    · intro t ht
      rw [hN'e t ht, sub_zero]
  have hB3 : N' 1 - N' 0 = 2 * π * Complex.I := by
    refine hrc (‖κ₀‖ * ρ) (mul_pos hκ₀pos hρ0) hρρ₂ N' hN'c ?_
    intro t ht
    rw [hN'e t ht, sub_zero, hv1]
  rw [← hStepA, hB1, hB2, hB3]

/-- The local expression of a homeomorphism is continuous on its domain. -/
theorem s24q_lm_continuousOn {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] (f : S₀ → S₁) (hf : Continuous f) (x : S₀) :
    ContinuousOn (localMapExpr f x) (localMapDomain f x) := by
  have h1 : ContinuousOn (fun z => (chartAt ℂ x).symm z) (localMapDomain f x) :=
    (chartAt ℂ x).continuousOn_symm.mono (fun z hz => hz.1)
  have h2 : ContinuousOn (fun z => f ((chartAt ℂ x).symm z)) (localMapDomain f x) :=
    hf.comp_continuousOn h1
  exact (chartAt ℂ (f x)).continuousOn.comp h2 (fun z hz => hz.2)

/-- The local expression of a holomorphic map is holomorphic on its domain. -/
theorem s24q_lm_differentiableOn {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ → S₁}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : S₀) :
    DifferentiableOn ℂ (localMapExpr f x) (localMapDomain f x) := by
  intro z hz
  have hp : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz.1
  have hfp : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source := hz.2
  have h := (s23_mdifferentiableAt_iff (x := x) (y := f x) hp hfp).1 (hf _)
  have := h.2
  rw [(chartAt ℂ x).right_inv hz.1] at this
  exact this.differentiableWithinAt

/-- Local winding `+1` of a homeomorphism is preserved by post-composition with a biholomorphic map. -/
theorem s24q_lm_post {S₀ S₁ T : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ) ω S₀]
    [IsManifold 𝓘(ℂ) ω S₁] [IsManifold 𝓘(ℂ) ω T] (f : S₀ ≃ₜ S₁) (γ : S₁ ≃ₜ T)
    (hγ : IsBiholomorphic (γ : S₁ → T)) (x : S₀)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr f x (chartAt ℂ x x + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr f x (chartAt ℂ x x)) → Lg 1 - Lg 0 = 2 * π * Complex.I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr (f.trans γ) x (chartAt ℂ x x + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr (f.trans γ) x (chartAt ℂ x x)) → Lg 1 - Lg 0 = 2 * π * Complex.I := by
  classical
  have hγs : IsBiholomorphic (γ.symm : T → S₁) := IsBiholomorphic.homeomorph_symm hγ
  set z₀ := chartAt ℂ x x with hz₀
  let U : Set ℂ := localMapDomain f x ∩ localMapDomain (f.trans γ) x
  let V : Set ℂ := localMapDomain γ.symm (γ (f x))
  have hUo : IsOpen U :=
    (s23_localMapDomain_isOpen f.continuous x).inter (s23_localMapDomain_isOpen (f.trans γ).continuous x)
  have hz₀U : z₀ ∈ U := ⟨(s23_h_center f x).1, (s23_h_center (f.trans γ) x).1⟩
  have hVo : IsOpen V := s23_localMapDomain_isOpen γ.symm.continuous _
  have hFV : ∀ z ∈ U, localMapExpr (f.trans γ) x z ∈ V := by
    intro z hz
    have hzt : z ∈ (chartAt ℂ x).target := hz.1.1
    have hz2 : γ (f ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ (γ (f x))).source := hz.2.2
    have hz1 : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source := hz.1.2
    refine ⟨(chartAt ℂ (γ (f x))).map_source hz2, ?_⟩
    show γ.symm ((chartAt ℂ (γ (f x))).symm (chartAt ℂ (γ (f x)) (γ (f ((chartAt ℂ x).symm z))))) ∈
      (chartAt ℂ (γ.symm (γ (f x)))).source
    rw [(chartAt ℂ (γ (f x))).left_inv hz2, γ.symm_apply_apply, γ.symm_apply_apply]
    exact hz1
  have hFc : ContinuousAt (localMapExpr (f.trans γ) x) z₀ :=
    (s24q_lm_continuousOn (f.trans γ) (f.trans γ).continuous x).continuousAt
      ((s23_localMapDomain_isOpen (f.trans γ).continuous x).mem_nhds hz₀U.2)
  refine s24q_lg_winding_conj' (F := localMapExpr (f.trans γ) x) (h := localMapExpr f x) (ψ₀ := id)
    (ψ₁ := localMapExpr γ.symm (γ (f x))) (z₀ := z₀) (U := U) (V := V) (D := localMapDomain f x)
    hUo hz₀U hVo (s23_localMapDomain_isOpen f.continuous x) differentiableOn_id (Set.injOn_id U)
    (s24q_lm_differentiableOn hγs.1 _) (s23_c1_injOn_localMapExpr γ.symm.injective _)
    hFc (hFV z₀ hz₀U) (fun z hz => hz.1) ?_
    (s24q_lm_continuousOn f f.continuous x) (s23_c1_injOn_localMapExpr f.injective x) hw
  intro z hz hFz
  have hz2 : γ (f ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ (γ (f x))).source := hz.2.2
  show chartAt ℂ (γ.symm (γ (f x))) (γ.symm ((chartAt ℂ (γ (f x))).symm
      (chartAt ℂ (γ (f x)) (γ (f ((chartAt ℂ x).symm z)))))) = chartAt ℂ (f x) (f ((chartAt ℂ x).symm z))
  rw [(chartAt ℂ (γ (f x))).left_inv hz2, γ.symm_apply_apply, γ.symm_apply_apply]

/-- Local winding `+1` of a homeomorphism is preserved by pre-composition with the inverse of a biholomorphic map. -/
theorem s24q_lm_pre {S₀ S₁ T : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ) ω S₀]
    [IsManifold 𝓘(ℂ) ω S₁] [IsManifold 𝓘(ℂ) ω T] (c : S₀ ≃ₜ T) (hc : IsBiholomorphic (c : S₀ → T))
    (f : S₀ ≃ₜ S₁) (x : S₀)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr f x (chartAt ℂ x x + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr f x (chartAt ℂ x x)) → Lg 1 - Lg 0 = 2 * π * Complex.I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr (c.symm.trans f) (c x) (chartAt ℂ (c x) (c x) + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr (c.symm.trans f) (c x) (chartAt ℂ (c x) (c x))) → Lg 1 - Lg 0 = 2 * π * Complex.I := by
  classical
  have hcs : IsBiholomorphic (c.symm : T → S₀) := IsBiholomorphic.homeomorph_symm hc
  set z₀ := chartAt ℂ (c x) (c x) with hz₀
  let ψ₀ : ℂ → ℂ := localMapExpr c.symm (c x)
  have hψ₀eq : ψ₀ = fun z => chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm z)) := by
    funext z; simp only [ψ₀, localMapExpr, Homeomorph.symm_apply_apply]
  have hψ₀z : ψ₀ z₀ = chartAt ℂ x x := by
    have := (s23_h_center c.symm (c x)).2
    simpa only [Homeomorph.symm_apply_apply] using this
  let Dψ : Set ℂ := localMapDomain c.symm (c x)
  let U : Set ℂ := Dψ ∩ localMapDomain (c.symm.trans f) (c x)
  have hUo : IsOpen U :=
    (s23_localMapDomain_isOpen c.symm.continuous _).inter
      (s23_localMapDomain_isOpen (c.symm.trans f).continuous _)
  have hz₀U : z₀ ∈ U := ⟨(s23_h_center c.symm (c x)).1, (s23_h_center (c.symm.trans f) (c x)).1⟩
  have hψD : Set.MapsTo ψ₀ U (localMapDomain f x) := by
    intro z hz
    have hzt : z ∈ (chartAt ℂ (c x)).target := hz.1.1
    have h1 : c.symm ((chartAt ℂ (c x)).symm z) ∈ (chartAt ℂ x).source := by
      have : c.symm ((chartAt ℂ (c x)).symm z) ∈ (chartAt ℂ (c.symm (c x))).source := hz.1.2
      rwa [Homeomorph.symm_apply_apply] at this
    have h2 : f (c.symm ((chartAt ℂ (c x)).symm z)) ∈ (chartAt ℂ (f x)).source := by
      have := hz.2.2
      simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [hψ₀eq]; exact (chartAt ℂ x).map_source h1
    · have hz' : ψ₀ z = chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm z)) := by rw [hψ₀eq]
      change f ((chartAt ℂ x).symm (ψ₀ z)) ∈ (chartAt ℂ (f x)).source
      rw [hz', (chartAt ℂ x).left_inv h1]
      exact h2
  have hFc : ContinuousAt (localMapExpr (c.symm.trans f) (c x)) z₀ :=
    (s24q_lm_continuousOn (c.symm.trans f) (c.symm.trans f).continuous (c x)).continuousAt
      ((s23_localMapDomain_isOpen (c.symm.trans f).continuous (c x)).mem_nhds hz₀U.2)
  have hψ₀d : DifferentiableOn ℂ ψ₀ U :=
    (s24q_lm_differentiableOn hcs.1 (c x)).mono (fun z hz => hz.1)
  have hψ₀i : Set.InjOn ψ₀ U :=
    (s23_c1_injOn_localMapExpr c.symm.injective (c x)).mono (fun z hz => hz.1)
  refine s24q_lg_winding_conj' (F := localMapExpr (c.symm.trans f) (c x)) (h := localMapExpr f x)
    (ψ₀ := ψ₀) (ψ₁ := id) (z₀ := z₀) (U := U) (V := Set.univ) (D := localMapDomain f x)
    hUo hz₀U isOpen_univ (s23_localMapDomain_isOpen f.continuous x) hψ₀d hψ₀i
    differentiableOn_id (Set.injOn_id _) hFc (Set.mem_univ _) hψD ?_
    (s24q_lm_continuousOn f f.continuous x) (s23_c1_injOn_localMapExpr f.injective x) ?_
  · intro z hz _
    have hzt : z ∈ (chartAt ℂ (c x)).target := hz.1.1
    have h1 : c.symm ((chartAt ℂ (c x)).symm z) ∈ (chartAt ℂ x).source := by
      have : c.symm ((chartAt ℂ (c x)).symm z) ∈ (chartAt ℂ (c.symm (c x))).source := hz.1.2
      rwa [Homeomorph.symm_apply_apply] at this
    show localMapExpr (c.symm.trans f) (c x) z = localMapExpr f x (ψ₀ z)
    rw [hψ₀eq]
    simp only [localMapExpr, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [(chartAt ℂ x).left_inv h1]
  · obtain ⟨ρ₁, hρ₁, hρ⟩ := hw
    refine ⟨ρ₁, hρ₁, fun ρ hρ0 hρρ L hL hLe => hρ ρ hρ0 hρρ L hL ?_⟩
    intro t ht
    rw [hLe t ht]
    rw [hψ₀z]

/-- Core of the sphere bridge: a homeomorphism of `ℂ̂` fixing `0` and `∞` with local winding `+1` at `0` is
homotopic to the identity. -/
theorem s24q_sp_core (h : OnePoint ℂ ≃ₜ OnePoint ℂ) (h0 : h ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ))
    (hinf : h OnePoint.infty = OnePoint.infty)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ))) →
        Lg 1 - Lg 0 = 2 * π * Complex.I) :
    ∃ G : C(unitInterval × OnePoint ℂ, OnePoint ℂ), (∀ x, G (0, x) = h x) ∧ ∀ x, G (1, x) = x := by
  classical
  obtain ⟨φ, hφc, hφi, hφ0, hφe, hφt⟩ := s24q_sp_phi h h0 hinf
  have key : ∀ z : ℂ, localMapExpr h ((0 : ℂ) : OnePoint ℂ) z = φ z := by
    intro z
    have e1 : chartAt ℂ ((0 : ℂ) : OnePoint ℂ) = RiemannDynamics.sphereChartFinite := rfl
    simp only [localMapExpr, h0, e1]
    rw [RiemannDynamics.sphereChartFinite_symm_apply, hφe, RiemannDynamics.sphereChartFinite_coe]
  have hc0 : chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) = 0 := by
    have e1 : chartAt ℂ ((0 : ℂ) : OnePoint ℂ) = RiemannDynamics.sphereChartFinite := rfl
    rw [e1, RiemannDynamics.sphereChartFinite_coe]
  have hwφ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) = φ (0 + ρ * Complex.exp (2 * π * Complex.I * t)) - φ 0) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
    obtain ⟨ρ₁, hρ₁, hρ⟩ := hw
    refine ⟨ρ₁, hρ₁, fun ρ hρ0 hρρ L hL hLe => hρ ρ hρ0 hρρ L hL ?_⟩
    intro t ht
    rw [hLe t ht, hc0, key, key]
  obtain ⟨H, hHc, hHe, hHp⟩ := s24q_sp_lift hφc hφi hφ0 hwφ
  obtain ⟨Ψ, hΨc, hΨ0, hΨe, hΨle, hΨge⟩ := s24q_sp_psi hφc hφ0 hHc hHe hHp
  let G0 : unitInterval × OnePoint ℂ → OnePoint ℂ := fun u =>
    match u.2 with
    | (OnePoint.infty : OnePoint ℂ) => OnePoint.infty
    | ((w : ℂ) : OnePoint ℂ) => ((Ψ (u.1, w) : ℂ) : OnePoint ℂ)
  have hG0coe : ∀ t (w : ℂ), G0 (t, (w : OnePoint ℂ)) = ((Ψ (t, w) : ℂ) : OnePoint ℂ) := fun t w => rfl
  have hG0inf : ∀ t, G0 (t, OnePoint.infty) = OnePoint.infty := fun t => rfl
  have hcont : Continuous G0 := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t₀, x⟩
    induction x using OnePoint.rec with
    | infty =>
      show Filter.Tendsto G0 (nhds (t₀, (OnePoint.infty : OnePoint ℂ))) (nhds OnePoint.infty)
      rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
      rintro s ⟨-, hsc⟩
      obtain ⟨R, hR⟩ := hsc.isBounded.subset_closedBall 0
      have hR0 : ∀ z ∈ s, ‖z‖ ≤ max R 0 := fun z hz => by
        have := hR hz; rw [mem_closedBall_zero_iff] at this; exact this.trans (le_max_left _ _)
      have e1 : ∀ᶠ z in cocompact ℂ, max R 0 < ‖φ z‖ := hφt.eventually_gt_atTop _
      have e2 : ∀ᶠ z in cocompact ℂ, max R 0 < ‖z‖ := tendsto_norm_cocompact_atTop.eventually_gt_atTop _
      obtain ⟨K, hKc, hK⟩ := Filter.mem_cocompact.mp (e1.and e2)
      have hmem : (Set.univ : Set unitInterval) ×ˢ ((fun w : ℂ => (w : OnePoint ℂ)) '' Kᶜ ∪ {OnePoint.infty}) ∈
          nhds (t₀, (OnePoint.infty : OnePoint ℂ)) :=
        prod_mem_nhds Filter.univ_mem (OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨hKc.isClosed, hKc⟩)
      filter_upwards [hmem] with u hu
      obtain ⟨t, x⟩ := u
      obtain ⟨-, hx⟩ := hu
      rcases hx with ⟨w, hwK, rfl⟩ | hx
      · have hw := hK hwK
        rw [hG0coe]
        refine Or.inl ⟨Ψ (t, w), fun hmem' => ?_, rfl⟩
        have h1 := hΨge t w (by intro h; rw [h] at hw; simp at hw)
        have h2 := hR0 _ hmem'
        have : max R 0 < min ‖φ w‖ ‖w‖ := lt_min hw.1 hw.2
        linarith
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inr (hG0inf t)
    | coe w₀ =>
      have hι : Topology.IsOpenEmbedding (fun u : unitInterval × ℂ => (u.1, (u.2 : OnePoint ℂ))) :=
        Topology.IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
      have h1 : ContinuousAt (G0 ∘ fun u : unitInterval × ℂ => (u.1, (u.2 : OnePoint ℂ))) (t₀, w₀) := by
        have : (G0 ∘ fun u : unitInterval × ℂ => (u.1, (u.2 : OnePoint ℂ))) = fun u => ((Ψ u : ℂ) : OnePoint ℂ) := by
          funext u; exact hG0coe u.1 u.2
        rw [this]
        exact (OnePoint.continuous_coe.comp hΨc).continuousAt
      exact (hι.continuousAt_iff (g := G0) (x := (t₀, w₀))).mp h1
  refine ⟨⟨G0, hcont⟩, ?_, ?_⟩
  · intro x
    induction x using OnePoint.rec with
    | infty => exact (hG0inf 0).trans hinf.symm
    | coe w =>
      show G0 (0, (w : OnePoint ℂ)) = h (w : OnePoint ℂ)
      rw [hG0coe, hφe]
      by_cases hw0 : w = 0
      · subst hw0; rw [hΨ0, hφ0]
      · congr 1
        have hz : Complex.exp (Complex.log w) = w := Complex.exp_log hw0
        rw [← hz, hΨe, ← hHe]
        simp
  · intro x
    induction x using OnePoint.rec with
    | infty => exact hG0inf 1
    | coe w =>
      show G0 (1, (w : OnePoint ℂ)) = (w : OnePoint ℂ)
      rw [hG0coe]
      by_cases hw0 : w = 0
      · subst hw0; rw [hΨ0]
      · congr 1
        have hz : Complex.exp (Complex.log w) = w := Complex.exp_log hw0
        rw [← hz, hΨe]
        simp

/-- Every `GL(2,ℂ)` Möbius transformation of `ℂ̂` is the action of an `SL(2,ℂ)` element. -/
theorem s24q_mb_gl_sl (g : GL (Fin 2) ℂ) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x : OnePoint ℂ, mobiusSL γ x = g • x := by
  classical
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    have := g.det.ne_zero
    simpa [Matrix.GeneralLinearGroup.det] using this
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Matrix (Fin 2) (Fin 2) ℂ).det) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hdet; rw [← hs]; norm_num
  set M : Matrix (Fin 2) (Fin 2) ℂ := s⁻¹ • (g : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hMdet : M.det = 1 := by
    rw [hM, Matrix.det_smul, ← hs]
    simp [Fintype.card_fin]
    field_simp
  let γ : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨M, hMdet⟩
  refine ⟨γ, fun x => ?_⟩
  rw [k22_t_mobiusSL_eq_smul]
  have hT : ((Matrix.SpecialLinearGroup.toGL γ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = M := rfl
  have e00 : M 0 0 = s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := rfl
  have e01 : M 0 1 = s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := rfl
  have e10 : M 1 0 = s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := rfl
  have e11 : M 1 1 = s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := rfl
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite, OnePoint.smul_infty_eq_ite]
    simp only [hT, e00, e10, mul_eq_zero, inv_eq_zero, hs0, false_or]
    split_ifs
    · rfl
    · congr 1
      field_simp
  | coe w =>
    rw [OnePoint.smul_some_eq_ite, OnePoint.smul_some_eq_ite]
    simp only [hT, e00, e01, e10, e11]
    have h1 : s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w + s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
        s⁻¹ * ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w + (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by ring
    have h2 : s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * w + s⁻¹ * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
        s⁻¹ * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * w + (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by ring
    rw [h1, h2]
    by_cases hz : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w + (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0
    · simp [hz]
    · have : s⁻¹ * ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w + (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ≠ 0 :=
        mul_ne_zero (inv_ne_zero hs0) hz
      rw [ite_eq_right hz, ite_eq_right this, mul_div_mul_left _ _ (inv_ne_zero hs0)]

/-- The Möbius map `mobiusSL γ` as a biholomorphic homeomorphism of `ℂ̂`. -/
theorem s24q_mb_homeo (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ∃ T : OnePoint ℂ ≃ₜ OnePoint ℂ, (∀ x, T x = mobiusSL γ x) ∧ IsBiholomorphic (T : OnePoint ℂ → OnePoint ℂ) := by
  classical
  let T : OnePoint ℂ ≃ₜ OnePoint ℂ :=
    { toFun := mobiusSL γ
      invFun := mobiusSL γ⁻¹
      left_inv := fun x => k22_t_mobiusSL_inv_apply γ x
      right_inv := fun x => by
        have := k22_t_mobiusSL_inv_apply γ⁻¹ x
        rwa [inv_inv] at this
      continuous_toFun := k22_t_continuous γ
      continuous_invFun := k22_t_continuous γ⁻¹ }
  refine ⟨T, fun x => rfl, ?_, mobiusSL γ⁻¹, ?_, fun x => k22_t_mobiusSL_inv_apply γ x, fun x => ?_⟩
  · obtain ⟨e, he⟩ := RiemannDynamics.exists_gl_smul_diffeomorph (Matrix.SpecialLinearGroup.toGL γ)
    have : (T : OnePoint ℂ → OnePoint ℂ) = e := by
      rw [he]; funext x; exact k22_t_mobiusSL_eq_smul γ x
    rw [this]
    exact e.contMDiff.mdifferentiable (by simp)
  · obtain ⟨e, he⟩ := RiemannDynamics.exists_gl_smul_diffeomorph (Matrix.SpecialLinearGroup.toGL γ⁻¹)
    have : mobiusSL γ⁻¹ = e := by
      rw [he]; funext x; exact k22_t_mobiusSL_eq_smul γ⁻¹ x
    rw [this]
    exact e.contMDiff.mdifferentiable (by simp)
  · have := k22_t_mobiusSL_inv_apply γ⁻¹ x
    rwa [inv_inv] at this

/-- **Orientation bridge (sphere; degree one).** A homeomorphism of `ℂ̂` with local winding `+1` of its chart expression
at `0` (the conclusion of `rc_hloc_of_sensePreserving`; a homeomorphism of `ℂ̂` has constant local degree `±1`) is
homotopic to a Möbius map.  Route: Möbius-normalize `h(0) = 0`, `h(∞) = ∞`; lift `h|ℂ*` through `exp` to `H` with
`H(z + 2πi) = H(z) + 2πi` (degree `+1` by the winding of the circles about `0`, for all radii); the straight-line
homotopy `(1 - t)H + t·id` descends and extends continuously to `0` and `∞`. -/
theorem s24q_sphere_homotopic_mobius (h : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ))) →
        Lg 1 - Lg 0 = 2 * π * Complex.I) :
    ∃ (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ)),
      (∀ x, H (0, x) = h x) ∧ ∀ x, H (1, x) = mobiusSL γ x := by
  classical
  have hne : h ((0 : ℂ) : OnePoint ℂ) ≠ h OnePoint.infty := fun he => by
    have := h.injective he
    exact OnePoint.coe_ne_infty _ this
  obtain ⟨b, hb⟩ : ∃ b : OnePoint ℂ, b ≠ h ((0 : ℂ) : OnePoint ℂ) ∧ b ≠ h OnePoint.infty := by
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset ({h ((0 : ℂ) : OnePoint ℂ), h OnePoint.infty} : Finset (OnePoint ℂ))
    refine ⟨b, ?_, ?_⟩ <;> intro e <;> apply hb <;> simp [e]
  obtain ⟨g, hg0, -, hgI⟩ := RiemannDynamics.exists_gl_smul_eq_zero_one_infty hb.1.symm hne hb.2
  obtain ⟨γ₁, hγ₁⟩ := s24q_mb_gl_sl g
  obtain ⟨T₁, hT₁, hT₁b⟩ := s24q_mb_homeo γ₁
  have hw' := s24q_lm_post h T₁ hT₁b ((0 : ℂ) : OnePoint ℂ) hw
  obtain ⟨G, hG0, hG1⟩ := s24q_sp_core (h.trans T₁)
    (by show T₁ (h _) = _; rw [hT₁, hγ₁, hg0])
    (by show T₁ (h _) = _; rw [hT₁, hγ₁, hgI]) hw'
  refine ⟨γ₁⁻¹, ⟨fun u => mobiusSL γ₁⁻¹ (G u), (k22_t_continuous γ₁⁻¹).comp G.continuous⟩, ?_, ?_⟩
  · intro x
    show mobiusSL γ₁⁻¹ (G (0, x)) = h x
    rw [hG0]
    show mobiusSL γ₁⁻¹ (T₁ (h x)) = h x
    rw [hT₁]; exact k22_t_mobiusSL_inv_apply γ₁ _
  · intro x
    show mobiusSL γ₁⁻¹ (G (1, x)) = _
    rw [hG1]

/-- Genus zero: with biholomorphic models `c₀, c₁ : Sᵢ → ℂ̂`, `c₁ ∘ f ∘ c₀⁻¹` is an orientation preserving
homeomorphism of `ℂ̂`, homotopic to a Möbius map `M` (`s24q_sphere_homotopic_mobius`); so `f` is homotopic to the
biholomorphic, hence `1`-q.c., `c₁⁻¹ ∘ M ∘ c₀`. -/
theorem s24q_genus_zero_of_model [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {c₀ : S₀ ≃ₜ OnePoint ℂ} {c₁ : S₁ ≃ₜ OnePoint ℂ} (hc₀ : IsBiholomorphic (c₀ : S₀ → OnePoint ℂ))
    (hc₁ : IsBiholomorphic (c₁ : S₁ → OnePoint ℂ)) (f : S₀ ≃ₜ S₁)
    (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x)) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : S₀, c₀ x = ((0 : ℂ) : OnePoint ℂ) := ⟨c₀.symm _, c₀.apply_symm_apply _⟩
  have hLW0 := rc_hloc_of_sensePreserving (s23_localMapDomain_isOpen f.continuous x)
    (s24q_lm_continuousOn f f.continuous x) (s23_c1_injOn_localMapExpr f.injective x) (hf x)
    (s23_h_center f x).1
  have hLW1 := s24q_lm_pre c₀ hc₀ f x hLW0
  have hLW2 := s24q_lm_post (c₀.symm.trans f) c₁ hc₁ (c₀ x) hLW1
  rw [hx] at hLW2
  obtain ⟨γ, H, hH0, hH1⟩ := s24q_sphere_homotopic_mobius ((c₀.symm.trans f).trans c₁) hLW2
  obtain ⟨T, hT, hTb⟩ := s24q_mb_homeo γ
  have hc₁s : IsBiholomorphic (c₁.symm : OnePoint ℂ → S₁) := IsBiholomorphic.homeomorph_symm hc₁
  refine ⟨c₀.trans (T.trans c₁.symm), ⟨1, (isKQCRS_one_iff _).2 ?_⟩, ?_⟩
  · exact hc₁s.comp (hTb.comp hc₀)
  · refine ⟨⟨⟨fun p => c₁.symm (H (p.1, c₀ p.2)), ?_⟩, ?_, ?_⟩⟩
    · exact c₁.symm.continuous.comp (H.continuous.comp (continuous_fst.prodMk (c₀.continuous.comp continuous_snd)))
    · intro s
      show c₁.symm (H (0, c₀ s)) = f s
      rw [hH0]
      simp
    · intro s
      show c₁.symm (H (1, c₀ s)) = c₁.symm (T (c₀ s))
      rw [hH1, hT]

end LiZhongQC
