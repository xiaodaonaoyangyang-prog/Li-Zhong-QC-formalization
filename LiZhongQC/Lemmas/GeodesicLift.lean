import LiZhongQC.Lemmas.UniformizedUniqueness

/-! Finite length and covering-lift bridges for the actual surface geodesic predicate.
No global finite-length hypothesis is added to IsPhiGeodesicRS. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

namespace LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- A degenerate parameter interval has zero surface length: use the empty partition. -/
theorem s25v_lengthOn_self {q : S → ℂ → ℂ} {a b : S} (γ : Path a b) (t : ℝ) :
    phiLengthOn q γ t t = 0 := by
  apply le_antisymm ?_ zero_le
  unfold phiLengthOn
  refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => t)
    (iInf_le_of_le (fun i : Fin 0 => Fin.elim0 i) (iInf_le_of_le ?_ ?_)))
  · exact ⟨rfl, rfl, fun _ _ _ => le_rfl, fun i => Fin.elim0 i⟩
  · simp

/-- Finite representatives make the surface distance finite whenever a path is given. -/
theorem s25v_dist_lt_top_of_path [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (α : Path a b) : phiDistRS q a b < ⊤ := by
  obtain ⟨β, _hβ, hfin⟩ := s25s_finite_rep hq hne α
  exact lt_of_le_of_lt (s25s_dist_le_length β) hfin

/-- Endpoint distances along a path are finite, without any rectifiability assumption
on that path. The existing subpath constructor supplies the connecting path. -/
theorem s25v_dist_on_path_lt_top [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} (γ : Path a b) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    phiDistRS q (γ.extend s) (γ.extend t) < ⊤ := by
  obtain ⟨β, _htrace, _hlen⟩ := s25i_subpath_length (q := q) γ hs hst ht
  exact s25v_dist_lt_top_of_path hq hne β

/-- Compactness upgrades the actual local geodesic windows to finite global length.
A finite subdivision subordinate to the windows has finite-length edges; subadditivity
then gives a finite sum. No finite-length premise is used. -/
theorem s25v_geodesic_length_lt_top
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} {γ : Path a b} (hγ : IsPhiGeodesicRS q γ) :
    phiLengthPath q γ < ⊤ := by
  classical
  have hlocal : ∀ x : unitInterval, ∃ δ > 0,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        (x : ℝ) - δ < s → s < t → t < (x : ℝ) + δ →
          phiLengthOn q γ s t = phiDistRS q (γ.extend s) (γ.extend t) :=
    fun x => hγ x x.property
  choose δ hδ hwin using hlocal
  let C : unitInterval → Set unitInterval := fun x =>
    Subtype.val ⁻¹' Ioo ((x : ℝ) - δ x) ((x : ℝ) + δ x)
  have hC : ∀ x, IsOpen (C x) := fun x => isOpen_Ioo.preimage continuous_subtype_val
  have hcover : (univ : Set unitInterval) ⊆ ⋃ x, C x := by
    intro x _hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    change (x : ℝ) - δ x < x ∧ (x : ℝ) < x + δ x
    constructor <;> linarith [hδ x]
  obtain ⟨τ, hτ0, hτmono, ⟨N, hτN⟩, hsegments⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hC hcover
  have hedge : ∀ k : ℕ, phiLengthOn q γ (τ k) (τ (k + 1)) < ⊤ := by
    intro k
    have hle : (τ k : ℝ) ≤ τ (k + 1) := hτmono (Nat.le_succ k)
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨x, hx⟩ := hsegments k
      have hleft := hx (show τ k ∈ Icc (τ k) (τ (k + 1)) from
        ⟨le_rfl, hτmono (Nat.le_succ k)⟩)
      have hright := hx (show τ (k + 1) ∈ Icc (τ k) (τ (k + 1)) from
        ⟨hτmono (Nat.le_succ k), le_rfl⟩)
      change (x : ℝ) - δ x < τ k ∧ (τ k : ℝ) < x + δ x at hleft
      change (x : ℝ) - δ x < τ (k + 1) ∧ (τ (k + 1) : ℝ) < x + δ x at hright
      rw [hwin x (τ k) (τ k).property (τ (k + 1)) (τ (k + 1)).property
        hleft.1 hlt hright.2]
      exact s25v_dist_on_path_lt_top hq hne γ (τ k).property.1 hlt
        (τ (k + 1)).property.2
    · rw [heq, s25v_lengthOn_self]
      exact ENNReal.zero_lt_top
  have hprefix : ∀ k : ℕ, phiLengthOn q γ 0 (τ k) < ⊤ := by
    intro k
    induction k with
    | zero =>
        rw [hτ0]
        change phiLengthOn q γ 0 0 < ⊤
        rw [s25v_lengthOn_self]
        exact ENNReal.zero_lt_top
    | succ k ih =>
        exact lt_of_le_of_lt
          (s25i_split_le γ (τ k).property.1 (hτmono (Nat.le_succ k)))
          (ENNReal.add_lt_top.mpr ⟨ih, hedge k⟩)
  have h := hprefix N
  have hlast : (τ N : ℝ) = 1 := congrArg Subtype.val (hτN N le_rfl)
  rw [hlast] at h
  exact h

/-- The length of any ordered subinterval is bounded by total length. -/
theorem s25v_lengthOn_le_lengthPath {q : S → ℂ → ℂ} {a b : S}
    (γ : Path a b) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    phiLengthOn q γ s t ≤ phiLengthPath q γ := by
  calc
    phiLengthOn q γ s t ≤ phiLengthOn q γ 0 s + phiLengthOn q γ s t := le_add_self
    _ ≤ phiLengthOn q γ 0 t := s25i_split_ge γ hs hst
    _ ≤ phiLengthOn q γ 0 t + phiLengthOn q γ t 1 := le_self_add
    _ ≤ phiLengthOn q γ 0 1 := s25i_split_ge γ (hs.trans hst) ht

/-- The existing density-speed identity gives exact lift length on every finite-length
subinterval, with no new subdivision invariance assumption. -/
theorem s25v_lengthOn_lift [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ v, p (γ' v) = γ v)
    {s t : ℝ} (hfin : phiLengthOn q γ s t < ⊤) :
    phiLengthOn q γ s t =
      ∫⁻ v in Ioo s t, phiDensity (utm_liftQD q p)
        (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) *
          ‖deriv (fun u : ℝ => (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ)) v‖ₑ := by
  let F : ℝ → ℝ≥0∞ := fun v => phiDensity (utm_liftQD q p)
    (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) *
      ‖deriv (fun u : ℝ => (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ)) v‖ₑ
  have hsum : ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → S),
      τ 0 = s → τ (Fin.last n) = t → Monotone τ →
      (∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) →
      (∑ i : Fin n, ∫⁻ v in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend v)) *
          ‖deriv (fun u : ℝ => chartAt ℂ (x i) (γ.extend u)) v‖ₑ) =
        ∫⁻ v in Ioo s t, F v := by
    intro n τ x h0 h1 hm hsrc
    have heq := utm_a_lintegral_sum_eq F n τ hm
    rw [h0, h1] at heq
    refine Eq.trans ?_ heq
    apply Finset.sum_congr rfl
    intro i _hi
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro v hv
    exact utm_a_density_speed hq hp γ γ' hγ' (x i)
      (hsrc i ⟨v, Ioo_subset_Icc_self hv, rfl⟩)
  obtain ⟨n, τ, x, hP, _hbound⟩ :
      ∃ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → S),
        (τ 0 = s ∧ τ (Fin.last n) = t ∧ Monotone τ ∧
          ∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆
            (chartAt ℂ (x i)).source ∧
            ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
              (Icc (τ i.castSucc) (τ i.succ))) ∧
        (∑ i : Fin n, ∫⁻ v in Ioo (τ i.castSucc) (τ i.succ),
          phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend v)) *
            ‖deriv (fun u : ℝ => chartAt ℂ (x i) (γ.extend u)) v‖ₑ) < ⊤ := by
    simpa only [phiLengthOn, iInf_lt_iff, exists_prop] using hfin
  change phiLengthOn q γ s t = ∫⁻ v in Ioo s t, F v
  unfold phiLengthOn
  apply le_antisymm
  · exact iInf_le_of_le n (iInf_le_of_le τ (iInf_le_of_le x (iInf_le_of_le hP
      (hsum n τ x hP.1 hP.2.1 hP.2.2.1 (fun i => (hP.2.2.2 i).1)).le)))
  · refine le_iInf fun m => le_iInf fun σ => le_iInf fun y => le_iInf fun hQ => ?_
    exact (hsum m σ y hQ.1 hQ.2.1 hQ.2.2.1 (fun i => (hQ.2.2.2 i).1)).ge

/-- A surface geodesic has a Lipschitz lift and exact total lifted length.
The finite-length input to utm_length_lift is proved above from the original predicate. -/
theorem s25v_geodesic_lift_length
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} {γ : Path a b}
    (hγ : IsPhiGeodesicRS q γ) (γ' : C(unitInterval, UpperHalfPlane))
    (hγ' : ∀ v, p (γ' v) = γ v) :
    (∃ K : ℝ≥0, LipschitzOnWith K
      (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc 0 1)) ∧
      (∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p)
        (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
          ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) t‖ₑ) =
            phiLengthPath q γ :=
  utm_length_lift hq hp γ γ' hγ' (s25v_geodesic_length_lt_top hq hne hγ)

/-- Subadditivity glues local integral bounds over a finite subdivision of the
compact parameter interval. The integrand may take the value infinity. -/
theorem s25v_length_le_of_local_bounds {q : S → ℂ → ℂ} {a b : S}
    (γ : Path a b) (F : ℝ → ℝ≥0∞)
    (hlocal : ∀ v : unitInterval, ∃ T : Set unitInterval,
      IsOpen T ∧ v ∈ T ∧ ∀ s t : unitInterval, s ≤ t → Icc s t ⊆ T →
        phiLengthOn q γ s t ≤ ∫⁻ x in Ioo (s : ℝ) t, F x) :
    phiLengthPath q γ ≤ ∫⁻ x in Ioo (0 : ℝ) 1, F x := by
  classical
  choose T hTo hvT hT using hlocal
  have hcover : (univ : Set unitInterval) ⊆ ⋃ v, T v := by
    intro v _hv
    exact mem_iUnion.mpr ⟨v, hvT v⟩
  obtain ⟨τ, hτ0, hτmono, ⟨N, hτN⟩, hsegments⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hTo hcover
  have hprefix : ∀ k : ℕ,
      phiLengthOn q γ 0 (τ k) ≤ ∫⁻ x in Ioo (0 : ℝ) (τ k), F x := by
    intro k
    induction k with
    | zero =>
        rw [hτ0]
        change phiLengthOn q γ 0 0 ≤ ∫⁻ x in Ioo (0 : ℝ) 0, F x
        rw [s25v_lengthOn_self]
        exact zero_le
    | succ k ih =>
        obtain ⟨v, hv⟩ := hsegments k
        have hle : (τ k : ℝ) ≤ τ (k + 1) := hτmono (Nat.le_succ k)
        have hint := s25i_lint_split F
          (a := 0) (b := (τ (k + 1) : ℝ)) (y := (τ k : ℝ)) (τ (k + 1)).property.1
        have hsum :
            (∫⁻ x in Ioo (0 : ℝ) (τ k), F x) +
              (∫⁻ x in Ioo (τ k : ℝ) (τ (k + 1)), F x) ≤
                ∫⁻ x in Ioo (0 : ℝ) (τ (k + 1)), F x := by
          simpa only [min_eq_left (τ k).property.1, min_eq_right hle,
            max_eq_right (τ k).property.1, max_eq_left hle] using hint
        exact (s25i_split_le γ (τ k).property.1 hle).trans
          ((add_le_add ih (hT v (τ k) (τ (k + 1)) (hτmono (Nat.le_succ k)) hv)).trans hsum)
  have h := hprefix N
  have hlast : (τ N : ℝ) = 1 := congrArg Subtype.val (hτN N le_rfl)
  rw [hlast] at h
  exact h

/-- Projecting a Lipschitz lifted path cannot increase its metric length.
Local analytic chart expressions provide admissible chart pieces. This proof does
not first assume that the projected path has finite length. -/
theorem s25v_projection_length_le [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ v, p (γ' v) = γ v)
    {K : ℝ≥0} (hK : LipschitzOnWith K
      (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc 0 1)) :
    phiLengthPath q γ ≤
      ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p)
        (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
          ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) t‖ₑ := by
  let c : ℝ → ℂ := fun t => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)
  let F : ℝ → ℝ≥0∞ := fun t => phiDensity (utm_liftQD q p) (c t) * ‖deriv c t‖ₑ
  apply s25v_length_le_of_local_bounds γ F
  intro v
  let x := γ v
  have hx : p (γ' v) ∈ (chartAt ℂ x).source := by
    rw [hγ']
    exact mem_chart_source ℂ x
  obtain ⟨U, hUo, hvU, _hUH, _hinj, hU⟩ := utm_liftQD_local hq hp (γ' v) x hx
  let f : ℂ → ℂ := fun w => chartAt ℂ x (utm_pext p w)
  have hf : DifferentiableOn ℂ f U := fun w hw =>
    (hU w hw).2.1.differentiableAt.differentiableWithinAt
  obtain ⟨L, N, hN, hLN⟩ :=
    (hf.analyticAt (hUo.mem_nhds hvU)).hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨V, hVsub, hVo, hvV⟩ :=
    _root_.mem_nhds_iff.mp (Filter.inter_mem hN (hUo.mem_nhds hvU))
  let T : Set unitInterval := (fun u => (γ' u : ℂ)) ⁻¹' V
  have hTo : IsOpen T := hVo.preimage (UpperHalfPlane.continuous_coe.comp γ'.continuous)
  refine ⟨T, hTo, hvV, ?_⟩
  intro s t hst hT
  have hstR : (s : ℝ) ≤ t := hst
  have htime : ∀ u ∈ Icc (s : ℝ) t, u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨s.property.1.trans hu.1, hu.2.trans t.property.2⟩
  have hcV : ∀ u ∈ Icc (s : ℝ) t, c u ∈ V := by
    intro u hu
    have huI := htime u hu
    have hsub : (⟨u, huI⟩ : unitInterval) ∈ Icc s t := hu
    have h := hT hsub
    change (γ' ⟨u, huI⟩ : ℂ) ∈ V at h
    change (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) ∈ V
    rw [Set.projIcc_of_mem zero_le_one huI]
    exact h
  have hcoord : ∀ u : ℝ, chartAt ℂ x (γ.extend u) = f (c u) := by
    intro u
    change chartAt ℂ x (γ.extend u) =
      chartAt ℂ x (utm_pext p (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ))
    rw [utm_a_pext_lift γ γ' hγ']
  have hsrc : γ.extend '' Icc (s : ℝ) t ⊆ (chartAt ℂ x).source := by
    rintro _ ⟨u, hu, rfl⟩
    have h := (hU (c u) (hVsub (hcV u hu)).2).1
    change utm_pext p (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) ∈ _ at h
    rwa [utm_a_pext_lift γ γ' hγ'] at h
  have hcomp : LipschitzOnWith (L * K) (fun u => f (c u)) (Icc (s : ℝ) t) :=
    hLN.comp (hK.mono (fun u hu => htime u hu))
      (fun u hu => (hVsub (hcV u hu)).1)
  have hchart : LipschitzOnWith (L * K)
      (fun u => chartAt ℂ x (γ.extend u)) (Icc (s : ℝ) t) := by
    intro u hu w hw
    change edist (chartAt ℂ x (γ.extend u)) (chartAt ℂ x (γ.extend w)) ≤ _
    rw [hcoord u, hcoord w]
    exact hcomp hu hw
  refine (s25e_len_le_piece γ x hstR hsrc ⟨L * K, hchart⟩).trans_eq ?_
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact utm_a_density_speed hq hp γ γ' hγ' x
    (hsrc ⟨u, Ioo_subset_Icc_self hu, rfl⟩)

/-- The distance downstairs is at most the lifted planar distance. Each Lipschitz
planar competitor projects to an actual surface path with no greater length. -/
theorem s25v_dist_le_lifted_metricDist [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (z w : UpperHalfPlane) :
    phiDistRS q (p z) (p w) ≤
      metricDist upperHalf (phiDensity (utm_liftQD q p)) (z : ℂ) (w : ℂ) := by
  unfold metricDist
  refine le_iInf fun β => le_iInf fun hβ => ?_
  rcases hβ with ⟨⟨K, hK⟩, h0, h1, htrace⟩
  let β' : C(unitInterval, UpperHalfPlane) :=
    ⟨fun t => ⟨β.toFun t, htrace ⟨t, t.property, rfl⟩⟩,
      UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        (hK.continuousOn.comp_continuous continuous_subtype_val (fun t => t.property))⟩
  have hβ0 : β' 0 = z := by
    apply UpperHalfPlane.ext
    exact h0
  have hβ1 : β' 1 = w := by
    apply UpperHalfPlane.ext
    exact h1
  let α : Path (p z) (p w) :=
    ⟨⟨fun t => p (β' t), hp.1.continuous.comp β'.continuous⟩,
      by change p (β' 0) = p z; rw [hβ0],
      by change p (β' 1) = p w; rw [hβ1]⟩
  have hα : ∀ t, p (β' t) = α t := fun _ => rfl
  let c : ℝ → ℂ := fun t => (β' (Set.projIcc 0 1 zero_le_one t) : ℂ)
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, c t = β.toFun t := by
    intro t ht
    change β.toFun (Set.projIcc 0 1 zero_le_one t) = β.toFun t
    rw [Set.projIcc_of_mem zero_le_one ht]
  have hcK : LipschitzOnWith K c (Icc 0 1) := by
    intro s hs t ht
    change edist (c s) (c t) ≤ _
    rw [hc s hs, hc t ht]
    exact hK hs ht
  have hlength := s25v_projection_length_le hq hp α β' hα hcK
  refine (s25s_dist_le_length α).trans (hlength.trans_eq ?_)
  change (∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p) (c t) *
    ‖deriv c t‖ₑ) = ∫⁻ t in Ioo (0 : ℝ) 1,
      phiDensity (utm_liftQD q p) (β.toFun t) * ‖deriv β.toFun t‖ₑ
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hnear : c =ᶠ[𝓝 t] β.toFun :=
    Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hc
  dsimp only
  rw [hc t (Ioo_subset_Icc_self ht), hnear.deriv_eq]

/-- An affine restriction of a Lipschitz curve is an admissible competitor for
the planar distance. The affine change-of-variables identity gives its exact length. -/
theorem s25v_metricDist_le_segment (φ : ℂ → ℂ) (D : Set ℂ) (c : ℝ → ℂ)
    {K : ℝ≥0} (hK : LipschitzOnWith K c (Icc 0 1))
    (hD : c '' Icc (0 : ℝ) 1 ⊆ D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    metricDist D (phiDensity φ) (c s) (c t) ≤
      ∫⁻ u in Ioo s t, phiDensity φ (c u) * ‖deriv c u‖ₑ := by
  let d : ℝ → ℂ := fun u => c ((t - s) * u + s)
  have hpos : 0 < t - s := sub_pos.mpr hst
  have hmaps : ∀ u ∈ Icc (0 : ℝ) 1, (t - s) * u + s ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    constructor <;> nlinarith [hu.1, hu.2]
  have hLip : LipschitzOnWith (K * Real.toNNReal (t - s)) d (Icc 0 1) := by
    apply utm_b_lipschitz_affine hK (m := t - s) (k := s)
    · simp only [NNReal.coe_mul, Real.coe_toNNReal _ hpos.le, abs_of_pos hpos]
      exact le_rfl
    · exact hmaps
    · intro u _hu
      rfl
  let β : LRCurve := ⟨d, by
    intro u hu
    exact ⟨K * Real.toNNReal (t - s), Icc 0 1,
      Filter.mem_of_superset self_mem_nhdsWithin Ioo_subset_Icc_self, hLip⟩⟩
  have hβ : IsPathIn D (c s) (c t) β := by
    refine ⟨⟨_, hLip⟩, ?_, ?_, ?_⟩
    · change c ((t - s) * 0 + s) = c s
      rw [mul_zero, zero_add]
    · change c ((t - s) * 1 + s) = c t
      rw [mul_one, sub_add_cancel]
    · rintro _ ⟨u, hu, rfl⟩
      exact hD ⟨(t - s) * u + s, hmaps u hu, rfl⟩
  have hlen : β.rhoLength (phiDensity φ) =
      ∫⁻ u in Ioo s t, phiDensity φ (c u) * ‖deriv c u‖ₑ := by
    change (∫⁻ u in Ioo (0 : ℝ) 1, phiDensity φ (d u) * ‖deriv d u‖ₑ) =
      ∫⁻ u in Ioo s t, phiDensity φ (c u) * ‖deriv c u‖ₑ
    have h := s25i_cov_lintegral (phiDensity φ) (c₁ := d) (c₂ := c)
      (l := t - s) (m := s) (a := 0) (b := 1) hpos
      (fun _u _hu => Filter.Eventually.of_forall (fun _v => rfl))
    simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using h
  exact (iInf₂_le β hβ).trans_eq hlen

/-- Every covering lift of an actual surface geodesic is a planar geodesic in the
upper half-plane. Finite length is derived from the surface predicate, and the two
distance inequalities come respectively from projection of competitors and from
the lifted subarc itself. -/
theorem s25v_geodesic_lift_isPhiGeodesic
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} {γ : Path a b}
    (hγ : IsPhiGeodesicRS q γ) (γ' : C(unitInterval, UpperHalfPlane))
    (hγ' : ∀ v, p (γ' v) = γ v) :
    ∃ c : LRCurve,
      (∀ t : ℝ, c.toFun t = (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) ∧
      IsPhiGeodesic (utm_liftQD q p) upperHalf c ∧
      phiLength (utm_liftQD q p) c = phiLengthPath q γ := by
  have hfin := s25v_geodesic_length_lt_top hq hne hγ
  obtain ⟨⟨K, hK⟩, htotal⟩ := utm_length_lift hq hp γ γ' hγ' hfin
  let f : ℝ → ℂ := fun t => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)
  let c : LRCurve := ⟨f, by
    intro t ht
    exact ⟨K, Icc 0 1,
      Filter.mem_of_superset self_mem_nhdsWithin Ioo_subset_Icc_self, hK⟩⟩
  have htrace : f '' Icc (0 : ℝ) 1 ⊆ upperHalf := by
    rintro _ ⟨t, _ht, rfl⟩
    exact (γ' _).coe_im_pos
  refine ⟨c, fun _ => rfl, ⟨⟨K, hK⟩, htrace, ?_⟩, htotal⟩
  intro t₀ ht₀
  obtain ⟨δ, hδ, hwin⟩ := hγ t₀ ht₀
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hleft hst hright
  have hsubfin : phiLengthOn q γ s t < ⊤ :=
    lt_of_le_of_lt (s25v_lengthOn_le_lengthPath γ hs.1 hst.le ht.2) hfin
  have hlen := s25v_lengthOn_lift hq hp γ γ' hγ' hsubfin
  have hmin := hwin s hs t ht hleft hst hright
  change (∫⁻ u in Ioo s t, phiDensity (utm_liftQD q p) (f u) * ‖deriv f u‖ₑ) =
    metricDist upperHalf (phiDensity (utm_liftQD q p)) (f s) (f t)
  apply le_antisymm
  · rw [← hlen, hmin]
    have h := s25v_dist_le_lifted_metricDist hq hp
      (γ' (Set.projIcc 0 1 zero_le_one s)) (γ' (Set.projIcc 0 1 zero_le_one t))
    rw [hγ', hγ'] at h
    exact h
  · exact s25v_metricDist_le_segment (utm_liftQD q p) upperHalf f hK htrace hs.1 hst ht.2

/-- A specified lift preserves the no-pause condition: a constant lifted interval
would project to a constant original interval. -/
theorem s25v_lift_no_pause
    {p : UpperHalfPlane → S} {a b : S} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ v, p (γ' v) = γ v)
    (hno : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.extend u ≠ γ.extend s) :
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t,
        (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) ≠
          (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ) := by
  intro s t hs hst ht
  obtain ⟨u, hu, hne⟩ := hno s t hs hst ht
  refine ⟨u, hu, ?_⟩
  intro heq
  have hlift := UpperHalfPlane.coe_injective heq
  have hproj := congrArg p hlift
  rw [hγ', hγ'] at hproj
  exact hne hproj

/-- The covering path-lifting construction gives a geodesic lift through any
specified point above the initial endpoint. -/
theorem s25v_exists_geodesic_lift
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} {γ : Path a b}
    (hγ : IsPhiGeodesicRS q γ) (z : UpperHalfPlane) (hz : p z = a) :
    ∃ (γ' : C(unitInterval, UpperHalfPlane)) (c : LRCurve),
      γ' 0 = z ∧ (∀ v, p (γ' v) = γ v) ∧
      (∀ t : ℝ, c.toFun t = (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) ∧
      IsPhiGeodesic (utm_liftQD q p) upperHalf c ∧
      phiLength (utm_liftQD q p) c = phiLengthPath q γ := by
  have hstart : (γ : C(unitInterval, S)) 0 = p z := by
    rw [hz]
    exact γ.source
  let γ' := hp.1.liftPath (γ : C(unitInterval, S)) z hstart
  have hlift : ∀ v, p (γ' v) = γ v := fun v =>
    congrFun (hp.1.liftPath_lifts (γ : C(unitInterval, S)) z hstart) v
  obtain ⟨c, hc, hgeo, hlen⟩ := s25v_geodesic_lift_isPhiGeodesic hq hne hp hγ γ' hlift
  exact ⟨γ', c, hp.1.liftPath_zero (γ : C(unitInterval, S)) z hstart,
    hlift, hc, hgeo, hlen⟩

/-- Homotopic paths with the same initial lift have the same final lift.
This supplies the common-endpoint bridge needed before planar geodesic uniqueness. -/
theorem s25v_homotopic_lift_endpoints
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {a b : S} (γ₁ γ₂ : Path a b)
    (hhom : γ₁.Homotopic γ₂)
    (γ₁' γ₂' : C(unitInterval, UpperHalfPlane))
    (h₁ : ∀ t, p (γ₁' t) = γ₁ t) (h₂ : ∀ t, p (γ₂' t) = γ₂ t)
    (hstart : γ₁' 0 = γ₂' 0) : γ₁' 1 = γ₂' 1 := by
  have h01 : (γ₁ : C(unitInterval, S)) 0 = p (γ₁' 0) := (h₁ 0).symm
  have h02 : (γ₂ : C(unitInterval, S)) 0 = p (γ₁' 0) := by
    calc
      γ₂ 0 = a := γ₂.source
      _ = γ₁ 0 := γ₁.source.symm
      _ = p (γ₁' 0) := (h₁ 0).symm
  have he₁ : γ₁' = hp.1.liftPath (γ₁ : C(unitInterval, S)) (γ₁' 0) h01 :=
    (hp.1.eq_liftPath_iff' h01).mpr ⟨funext h₁, rfl⟩
  have he₂ : γ₂' = hp.1.liftPath (γ₂ : C(unitInterval, S)) (γ₁' 0) h02 :=
    (hp.1.eq_liftPath_iff' h02).mpr ⟨funext h₂, hstart.symm⟩
  exact (congrArg (fun f : C(unitInterval, UpperHalfPlane) => f 1) he₁).trans
    ((hp.1.liftPath_apply_one_eq_of_homotopicRel hhom (γ₁' 0) h01 h02).trans
      (congrArg (fun f : C(unitInterval, UpperHalfPlane) => f 1) he₂).symm)

end LiZhongQC

