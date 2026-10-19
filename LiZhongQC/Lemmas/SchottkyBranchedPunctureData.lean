import LiZhongQC.Lemmas.SchottkyCollarGeometry
import LiZhongQC.Lemmas.SchottkyBoundaryRank
import LiZhongQC.Lemmas.SchottkyGenusBridge11
import LiZhongQC.Ch07.S26_TeichmullerUniqueness
import LiZhongQC.Ch09.S31_FiniteType

/-!
# Puncture data for the branched double cover (R82, §32, lane (a))

For a closed Riemann surface `X` of genus `g` and an even finite set `P` of punctures (with
`g ≠ 0` or `P ≠ ∅`), the complement `U = X ∖ P` is connected and its fundamental group has an
index-two subgroup `K` not containing the loop around any puncture.  The construction uses the odd
winding characters of the core (`s78rb_boundary_characters`), extended over the discs by the radial
retraction, and the winding number mod 2.
-/

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

/-- **Removing small closed pieces keeps a connected space connected.**  If `C i ⊆ B i` with `C i`
closed, `B i` open and pairwise disjoint, and `B i ∖ C i` preconnected, then the complement of
`⋃ C i` is preconnected in a connected space. -/
theorem s82bc_conn_remove {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {ι : Type*}
    [Finite ι] (C B : ι → Set X) (hC : ∀ i, IsClosed (C i)) (hB : ∀ i, IsOpen (B i))
    (hCB : ∀ i, C i ⊆ B i) (hBd : Pairwise fun i j => Disjoint (B i) (B j))
    (hann : ∀ i, IsPreconnected (B i \ C i)) :
    IsPreconnected ((⋃ i, C i)ᶜ) := by
  classical
  have hAo : IsOpen ((⋃ i, C i)ᶜ) := (isClosed_iUnion_of_finite hC).isOpen_compl
  intro u v hu hv hAuv hAu hAv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- each annulus lies on one side
  have hside : ∀ i, ∃ b : Bool, B i \ C i ⊆ if b then u else v := by
    intro i
    have hsub : B i \ C i ⊆ (⋃ i, C i)ᶜ := by
      intro x hx hxc
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxc
      by_cases hji : j = i
      · subst hji; exact hx.2 hj
      · exact Set.disjoint_left.1 (hBd hji) (hCB j hj) hx.1
    have := hann i u v hu hv (hsub.trans hAuv)
    by_cases h1 : ((B i \ C i) ∩ u).Nonempty
    · by_cases h2 : ((B i \ C i) ∩ v).Nonempty
      · exfalso
        obtain ⟨x, hx⟩ := this h1 h2
        have : x ∈ (⋃ i, C i)ᶜ ∩ (u ∩ v) := ⟨hsub hx.1, hx.2⟩
        rw [hcon] at this; exact this
      · refine ⟨true, ?_⟩
        intro x hx
        rcases hAuv (hsub hx) with h | h
        · exact h
        · exact absurd ⟨x, hx, h⟩ h2
    · refine ⟨false, ?_⟩
      intro x hx
      rcases hAuv (hsub hx) with h | h
      · exact absurd ⟨x, hx, h⟩ h1
      · exact h
  choose sd hsd using hside
  let u' : Set X := ((⋃ i, C i)ᶜ ∩ u) ∪ ⋃ i ∈ {i | sd i = true}, B i
  let v' : Set X := ((⋃ i, C i)ᶜ ∩ v) ∪ ⋃ i ∈ {i | sd i = false}, B i
  have hu' : IsOpen u' :=
    (hAo.inter hu).union (isOpen_biUnion fun i _ => hB i)
  have hv' : IsOpen v' :=
    (hAo.inter hv).union (isOpen_biUnion fun i _ => hB i)
  have hcov : (univ : Set X) ⊆ u' ∪ v' := by
    intro x _
    by_cases hx : x ∈ (⋃ i, C i)ᶜ
    · rcases hAuv hx with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inl ⟨hx, h⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (not_not.mp hx)
      cases hs : sd i
      · exact Or.inr (Or.inr (mem_biUnion (show i ∈ {i | sd i = false} from hs) (hCB i hi)))
      · exact Or.inl (Or.inr (mem_biUnion (show i ∈ {i | sd i = true} from hs) (hCB i hi)))
  have hne1 : (univ ∩ u').Nonempty := by
    obtain ⟨x, hx, hxu⟩ := hAu
    exact ⟨x, trivial, Or.inl ⟨hx, hxu⟩⟩
  have hne2 : (univ ∩ v').Nonempty := by
    obtain ⟨x, hx, hxv⟩ := hAv
    exact ⟨x, trivial, Or.inl ⟨hx, hxv⟩⟩
  obtain ⟨x, -, hx1, hx2⟩ := isPreconnected_univ u' v' hu' hv' hcov hne1 hne2
  -- derive a contradiction from x ∈ u' ∩ v'
  have key : ∀ y, y ∈ u' → y ∈ v' → False := by
    intro y hy1 hy2
    rcases hy1 with ⟨hyA, hyu⟩ | hy1
    · rcases hy2 with ⟨-, hyv⟩ | hy2
      · have : y ∈ (⋃ i, C i)ᶜ ∩ (u ∩ v) := ⟨hyA, hyu, hyv⟩
        rw [hcon] at this; exact this
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy2
        obtain ⟨hsi, hyB⟩ := mem_iUnion.mp hi
        have hyBC : y ∈ B i \ C i := ⟨hyB, fun hc => hyA (mem_iUnion.mpr ⟨i, hc⟩)⟩
        have := hsd i hyBC
        have hsi' : sd i = false := hsi
        rw [hsi'] at this
        have h3 : y ∈ (⋃ i, C i)ᶜ ∩ (u ∩ v) := ⟨hyA, hyu, this⟩
        rw [hcon] at h3; exact h3
    · rcases hy2 with ⟨hyA, hyv⟩ | hy2
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy1
        obtain ⟨hsi, hyB⟩ := mem_iUnion.mp hi
        have hyBC : y ∈ B i \ C i := ⟨hyB, fun hc => hyA (mem_iUnion.mpr ⟨i, hc⟩)⟩
        have := hsd i hyBC
        have hsi' : sd i = true := hsi
        rw [hsi'] at this
        have h3 : y ∈ (⋃ i, C i)ᶜ ∩ (u ∩ v) := ⟨hyA, this, hyv⟩
        rw [hcon] at h3; exact h3
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy1
        obtain ⟨hsi, hyB⟩ := mem_iUnion.mp hi
        obtain ⟨j, hj⟩ := mem_iUnion.mp hy2
        obtain ⟨hsj, hyB'⟩ := mem_iUnion.mp hj
        have hij : i ≠ j := by
          rintro rfl
          have h1 : sd i = true := hsi
          have h2 : sd i = false := hsj
          rw [h1] at h2; exact Bool.noConfusion h2
        exact Set.disjoint_left.1 (hBd hij) hyB hyB'
  exact key x hx1 hx2

theorem s82bc_toExt_frontier_ball (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    frontier (toExt (Metric.ball c ρ)) = toExt (Metric.sphere c ρ) := by
  have hclosure : closure (toExt (Metric.ball c ρ)) = toExt (closure (Metric.ball c ρ)) := by
    unfold toExt
    refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
      (image_closure_subset_closure_image OnePoint.continuous_coe)
    exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, Metric.isBounded_ball.isCompact_closure⟩
  have hopen' : IsOpen (toExt (Metric.ball c ρ)) := OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
  rw [hopen'.frontier_eq, hclosure, ← frontier_ball c hρ.ne', Metric.isOpen_ball.frontier_eq]
  unfold toExt
  exact (image_diff OnePoint.coe_injective _ _).symm

theorem s82bc_isJordanDomain_ball (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsJordanDomain (Metric.ball c ρ) := by
  refine ⟨Metric.isOpen_ball, (convex_ball c ρ).isConnected ⟨c, Metric.mem_ball_self hρ⟩, ?_⟩
  rw [s82bc_toExt_frontier_ball c hρ]
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine ⟨fun θ => ((c + ρ * (θ : ℂ) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp (by fun_prop)
  · intro a b hab
    have h := OnePoint.coe_injective hab
    have h2 : (ρ : ℂ) * (a : ℂ) = (ρ : ℂ) * (b : ℂ) := add_left_cancel h
    exact Circle.coe_injective (mul_left_cancel₀ hρ' h2)
  · unfold toExt
    ext w
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨θ, rfl⟩
      refine ⟨c + ρ * (θ : ℂ), ?_, rfl⟩
      rw [mem_sphere_iff_norm]
      simp [Circle.norm_coe, abs_of_pos hρ]
    · rintro ⟨z, hz, rfl⟩
      have hn : ‖(z - c) / ρ‖ = 1 := by
        rw [norm_div, mem_sphere_iff_norm.mp hz, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          div_self hρ.ne']
      refine ⟨⟨(z - c) / ρ, mem_sphere_zero_iff_norm.2 hn⟩, ?_⟩
      show ((c + ρ * ((z - c) / ρ) : ℂ) : ExtPlane) = z
      rw [mul_div_cancel₀ _ hρ']; simp

theorem s82bc_circle_param (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ ∞ γ ∧ (∀ t, deriv γ t ≠ 0) ∧ (∀ t, γ (t + 1) = γ t) ∧
      InjOn γ (Ico 0 1) ∧ γ '' Ico 0 1 = Metric.sphere c ρ := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c + ρ * Complex.exp (2 * Real.pi * Complex.I * t))
      (ρ * (Complex.exp (2 * Real.pi * Complex.I * t) * (2 * Real.pi * Complex.I))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (ρ : ℂ) |>.const_add c
    convert h2 using 1
    ring
  refine ⟨fun t : ℝ => c + ρ * Complex.exp (2 * Real.pi * Complex.I * t), ?_, ?_, ?_, ?_, ?_⟩
  · have : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * t)) := by
      apply (ContDiff.restrict_scalars ℝ (𝕜' := ℂ) Complex.contDiff_exp).comp
      exact (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact contDiff_const.add (contDiff_const.mul this)
  · intro t
    rw [(hder t).deriv]
    simp [Complex.exp_ne_zero, hρ', Real.pi_ne_zero]
  · intro t
    simp only
    congr 2
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    simp [Complex.exp_two_pi_mul_I]
  · intro s hs t ht hst
    simp only at hst
    have h1 : Complex.exp (2 * Real.pi * Complex.I * s) = Complex.exp (2 * Real.pi * Complex.I * t) :=
      mul_left_cancel₀ hρ' (add_left_cancel hst)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
    have h2 : (s : ℂ) = t + n := by
      have : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      apply mul_left_cancel₀ this
      rw [mul_add]; linear_combination hn
    have h3 : s = t + n := by exact_mod_cast h2
    have h4 : (n : ℝ) < 1 := by linarith [hs.2, ht.1]
    have h5 : (-1 : ℝ) < n := by linarith [hs.1, ht.2]
    have h6 : n = 0 := by
      have a1 : n < 1 := by exact_mod_cast h4
      have a2 : -1 < n := by exact_mod_cast h5
      omega
    rw [h6] at h3; simpa using h3
  · ext z
    constructor
    · rintro ⟨t, -, rfl⟩
      rw [mem_sphere_iff_norm]
      simp [norm_mul, Complex.norm_exp, abs_of_pos hρ]
    · intro hz
      have hn : ‖(z - c) / ρ‖ = 1 := by
        rw [norm_div, mem_sphere_iff_norm.mp hz, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          div_self hρ.ne']
      set w := (z - c) / ρ with hw
      have hw' : w = Complex.exp (Complex.arg w * Complex.I) := by
        have := Complex.norm_mul_exp_arg_mul_I w
        rw [hn] at this; simpa using this.symm
      set t0 : ℝ := Complex.arg w / (2 * Real.pi) with ht0
      refine ⟨t0 - ⌊t0⌋, ⟨by linarith [Int.floor_le t0], by linarith [Int.lt_floor_add_one t0]⟩, ?_⟩
      show c + ρ * Complex.exp (2 * Real.pi * Complex.I * ((t0 - ⌊t0⌋ : ℝ) : ℂ)) = z
      have : Complex.exp (2 * Real.pi * Complex.I * ((t0 - ⌊t0⌋ : ℝ) : ℂ)) = w := by
        rw [hw']
        have e1 : (2 * Real.pi * Complex.I * ((t0 - ⌊t0⌋ : ℝ) : ℂ)) =
            Complex.arg w * Complex.I - ⌊t0⌋ * (2 * Real.pi * Complex.I) := by
          push_cast
          rw [ht0]; push_cast
          field_simp
        rw [e1, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I]
        simp
      rw [this, hw]; field_simp; ring

/-- A round disc in a chart is a closed disc in the sense of `IsClosedDiscIn`. -/
theorem s82bc_closedDisc_round {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (p : X)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ p p) ρ ⊆ (chartAt ℂ p).target) :
    IsClosedDiscIn ((chartAt ℂ p).symm '' Metric.closedBall (chartAt ℂ p p) ρ) := by
  obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5⟩ := s82bc_circle_param (chartAt ℂ p p) hρ
  refine ⟨p, ?_, Metric.ball (chartAt ℂ p p) ρ, s82bc_isJordanDomain_ball _ hρ,
    Metric.isBounded_ball, ?_, ?_, γ, hγ1, hγ2, hγ3, hγ4, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (chartAt ℂ p).map_target (hsub hw)
  · rw [closure_ball _ hρ.ne']; exact hsub
  · rw [closure_ball _ hρ.ne']
    ext w
    constructor
    · rintro ⟨_, ⟨w', hw', rfl⟩, rfl⟩
      rwa [(chartAt ℂ p).right_inv (hsub hw')]
    · intro hw
      exact ⟨_, ⟨w, hw, rfl⟩, (chartAt ℂ p).right_inv (hsub hw)⟩
  · rw [hγ5, frontier_ball _ hρ.ne']

/-- A chart of the maximal atlas followed by a translation stays in the maximal atlas. -/
theorem s82bc_shift_chart_mem {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (φ : OpenPartialHomeomorph X ℂ)
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (a : ℂ) :
    φ.transHomeomorph (Homeomorph.addRight a) ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  have hadd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => w + a) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => w + (-a)) :=
    (contDiff_id.add contDiff_const).contMDiff
  refine ⟨?_, ?_⟩
  · exact hadd.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hφ)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp hsub.contMDiffOn (fun w hw => hw)

/-- **Disjoint punctured charts.**  Around finitely many distinct points of a compact Hausdorff
Riemann surface there are charts of the maximal atlas, sending the point to `0`, with pairwise
disjoint chart balls that contain no other of the points. -/
theorem s82bc_local_charts {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [CompactSpace X] [IsManifold 𝓘(ℂ) ω X] {ι : Type*} [Finite ι] (p : ι → X)
    (hp : Function.Injective p) :
    ∃ (E : ι → OpenPartialHomeomorph X ℂ) (R : ι → ℝ), (∀ i, 0 < R i) ∧
      (∀ i, E i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ p i ∈ (E i).source ∧ E i (p i) = 0 ∧
        Metric.ball (0 : ℂ) (R i) ⊆ (E i).target ∧
        ∀ z : ℂ, ‖z‖ < R i → z ≠ 0 → (E i).symm z ∉ range p) ∧
      (Pairwise fun i j => Disjoint ((E i).symm '' Metric.ball (0 : ℂ) (R i))
        ((E j).symm '' Metric.ball (0 : ℂ) (R j))) ∧
      (∀ i w, (E i).symm w = (chartAt ℂ (p i)).symm (w + chartAt ℂ (p i) (p i))) ∧
      ∀ i w, w ∈ (E i).target ↔ w + chartAt ℂ (p i) (p i) ∈ (chartAt ℂ (p i)).target := by
  classical
  obtain ⟨W, hW, hWd⟩ := s31sd_disjoint_open_neighborhoods (fun i => ({p i} : Set X))
    (fun i => isClosed_singleton) (fun i j hij =>
      Set.disjoint_singleton.2 (fun h => hij (hp h)))
  let E : ι → OpenPartialHomeomorph X ℂ := fun i =>
    (chartAt ℂ (p i)).transHomeomorph (Homeomorph.addRight (-(chartAt ℂ (p i) (p i))))
  have hE0 : ∀ i, E i (p i) = 0 := fun i => by
    show chartAt ℂ (p i) (p i) + -(chartAt ℂ (p i) (p i)) = 0
    exact add_neg_cancel _
  have hEsrc : ∀ i, p i ∈ (E i).source := fun i => by
    simpa [E, OpenPartialHomeomorph.transHomeomorph] using mem_chart_source ℂ (p i)
  have hEsymm0 : ∀ i, (E i).symm 0 = p i := fun i => by
    have := (E i).left_inv (hEsrc i)
    rwa [hE0 i] at this
  have hR : ∀ i, ∃ R : ℝ, 0 < R ∧ Metric.ball (0 : ℂ) R ⊆ (E i).target ∩ (E i).symm ⁻¹' W i := by
    intro i
    have hopen : IsOpen ((E i).target ∩ (E i).symm ⁻¹' W i) :=
      (E i).symm.isOpen_inter_preimage (hW i).1
    have h0 : (0 : ℂ) ∈ (E i).target ∩ (E i).symm ⁻¹' W i := by
      refine ⟨?_, ?_⟩
      · have := (E i).map_source (hEsrc i); rwa [hE0 i] at this
      · show (E i).symm 0 ∈ W i
        rw [hEsymm0]; exact (hW i).2 rfl
    obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp hopen 0 h0
    exact ⟨R, hRpos, hRsub⟩
  choose R hRpos hRsub using hR
  refine ⟨E, R, hRpos, fun i => ⟨?_, hEsrc i, hE0 i, fun z hz => (hRsub i hz).1, ?_⟩, ?_, ?_, ?_⟩
  · exact s82bc_shift_chart_mem _ (IsManifold.chart_mem_maximalAtlas (p i)) _
  · rintro z hz hz0 ⟨j, hj⟩
    have hzW : (E i).symm z ∈ W i := (hRsub i (by simpa using hz)).2
    have hpj : p j ∈ W i := hj ▸ hzW
    by_cases hij : j = i
    · subst hij
      apply hz0
      have h1 : (E j).symm z = p j := hj.symm
      have := congrArg (E j) h1
      rwa [(E j).right_inv (hRsub j (by simpa using hz)).1, hE0] at this
    · exact Set.disjoint_left.1 (hWd (Ne.symm hij)) hpj ((hW j).2 rfl)
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have h1 : (E i).symm z ∈ W i := (hRsub i hz).2
    have h2 : (E j).symm w ∈ W j := (hRsub j hw).2
    rw [hwz] at h2
    exact Set.disjoint_left.1 (hWd hij) h1 h2
  · intro i w
    show (chartAt ℂ (p i)).symm (w + -(-(chartAt ℂ (p i) (p i)))) = _
    rw [neg_neg]
  · intro i w
    show w + -(-(chartAt ℂ (p i) (p i))) ∈ (chartAt ℂ (p i)).target ↔ _
    rw [neg_neg]

theorem s82bc_annulus_preconnected {ρ R : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} := by
  have himg : {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} =
      (fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) '' (Ioo ρ R ×ˢ univ) := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(‖z‖, Complex.arg z), ⟨⟨h1, h2⟩, trivial⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
    · rintro ⟨⟨r, θ⟩, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      have hr : 0 < r := hρ.trans_lt h1
      have hn : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
      show ρ < ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ ∧ ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ < R
      rw [hn]; exact ⟨h1, h2⟩
  rw [himg]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop)

/-- The image of an annulus-like region of a chart is preconnected. -/
theorem s82bc_chart_annulus_preconnected {X : Type u} [TopologicalSpace X]
    (E : OpenPartialHomeomorph X ℂ) {R ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hball : Metric.ball (0 : ℂ) R ⊆ E.target) :
    IsPreconnected ((E.symm '' Metric.ball (0 : ℂ) R) \ (E.symm '' Metric.closedBall (0 : ℂ) ρ)) := by
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) R :=
    Metric.closedBall_subset_ball hρR
  rw [← (E.symm.injOn.mono hball).image_diff_subset hsub]
  have hset : Metric.ball (0 : ℂ) R \ Metric.closedBall (0 : ℂ) ρ = {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} := by
    ext z
    simp only [mem_diff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, mem_setOf_eq]
    exact and_comm
  rw [hset]
  refine (s82bc_annulus_preconnected (R := R) hρ).image _ (E.symm.continuousOn.mono ?_)
  intro z hz
  exact hball (by simpa using hz.2)

/-- **A connected surface minus finitely many disjoint round chart discs is connected.** -/
theorem s82bc_complement_connected {X : Type u} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] {ι : Type*} [Finite ι] (E : ι → OpenPartialHomeomorph X ℂ)
    (R ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hρR : ∀ i, ρ i < R i)
    (hball : ∀ i, Metric.ball (0 : ℂ) (R i) ⊆ (E i).target)
    (hdisj : Pairwise fun i j => Disjoint ((E i).symm '' Metric.ball (0 : ℂ) (R i))
      ((E j).symm '' Metric.ball (0 : ℂ) (R j))) :
    IsConnected ((⋃ i, (E i).symm '' Metric.closedBall (0 : ℂ) (ρ i))ᶜ) := by
  refine ⟨?_, ?_⟩
  · by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι
      have hcn : ‖((((ρ i + R i) / 2 : ℝ)) : ℂ)‖ = (ρ i + R i) / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg]
        linarith [hρ i, hρR i]
      have hc : ((((ρ i + R i) / 2 : ℝ)) : ℂ) ∈ Metric.ball (0 : ℂ) (R i) := by
        rw [mem_ball_zero_iff, hcn]; linarith [hρR i]
      refine ⟨(E i).symm ((((ρ i + R i) / 2 : ℝ)) : ℂ), ?_⟩
      intro hmem
      obtain ⟨j, w, hw, hwc⟩ := mem_iUnion.mp hmem
      by_cases hji : j = i
      · subst hji
        have := (E j).symm.injOn (hball j (Metric.closedBall_subset_ball (hρR j) hw)) (hball j hc) hwc
        rw [this, mem_closedBall_zero_iff, hcn] at hw
        linarith [hρR j]
      · exact Set.disjoint_left.1 (hdisj hji)
          ⟨w, Metric.closedBall_subset_ball (hρR j) hw, hwc⟩ ⟨_, hc, rfl⟩
    · rw [not_nonempty_iff] at hι
      simp only [iUnion_of_empty, compl_empty]
      exact univ_nonempty
  · refine s82bc_conn_remove (fun i => (E i).symm '' Metric.closedBall (0 : ℂ) (ρ i))
      (fun i => (E i).symm '' Metric.ball (0 : ℂ) (R i)) ?_ ?_ ?_ hdisj ?_
    · intro i
      refine (IsCompact.image_of_continuousOn (isCompact_closedBall _ _) ?_).isClosed
      exact (E i).symm.continuousOn.mono (fun z hz => hball i
        (Metric.closedBall_subset_ball (hρR i) hz))
    · intro i
      exact (E i).symm.isOpen_image_of_subset_source Metric.isOpen_ball (hball i)
    · intro i
      exact image_mono (Metric.closedBall_subset_ball (hρR i))
    · intro i
      exact s82bc_chart_annulus_preconnected (E i) (hρ i) (hρR i) (hball i)

/-- **An odd circle character on the core.**  Let `X` be a closed Riemann surface and `v j` an even
number `m ≠ 0` of disjoint round disc charts (with `IsClosedDiscIn` images of the unit disc) whose
complement `S` is connected.  Then the core `X ∖ ⋃ interior (D j)` carries a circle-valued map
whose winding number along every boundary circle is odd. -/
theorem s82bc_core_odd_character {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [CompactSpace X] [IsManifold 𝓘(ℂ) ω X] {g m : ℕ} (hX : HasGenus X g)
    (hm : m ≠ 0) (hmeven : Even m)
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, Metric.closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint (v i '' Metric.closedBall (0 : ℂ) (R i))
      (v j '' Metric.closedBall (0 : ℂ) (R j)))
    (hdisc : ∀ j, IsClosedDiscIn (v j '' Metric.closedBall (0 : ℂ) 1))
    (S : TopologicalSpace.Opens X)
    (hS : (S : Set X) = (⋃ j, v j '' Metric.closedBall (0 : ℂ) 1)ᶜ) [ConnectedSpace S] :
    ∃ f : C(↥((⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ), AddCircle (1 : ℝ)),
      ∀ j : Fin m, ∃ (L : C(ℝ, ℝ)) (k : ℤ), Odd k ∧
        (∀ (t : ℝ) (h : v j (Circle.exp (2 * Real.pi * t) : ℂ) ∈
            (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ),
          f ⟨v j (Circle.exp (2 * Real.pi * t) : ℂ), h⟩ = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + k := by
  classical
  let F : FiniteTypeStructure S g 0 m :=
    { X := { carrier := X }
      P := ∅
      D := fun j => v j '' Metric.closedBall (0 : ℂ) 1
      ι := Subtype.val
      genus := hX
      card_P := Finset.card_empty
      disc := hdisc
      disjoint := fun i j hij => (hdisj hij).mono
        (image_mono (Metric.closedBall_subset_closedBall (hR i).le))
        (image_mono (Metric.closedBall_subset_closedBall (hR j).le))
      disjoint_P := fun j => by simp
      embedding := S.isOpen.isOpenEmbedding_subtypeVal
      holomorphic := (contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero
      range_ι := by
        rw [Subtype.range_coe, hS]
        simp }
  have hD : ∀ j, v j '' Metric.closedBall (0 : ℂ) 1 = F.D j := fun j => rfl
  obtain ⟨β, hβper, hβinj, hβrange, hβval⟩ : ∃ β : ∀ j : Fin m, C(ℝ, s31dt_Core F),
      (∀ j t, β j (t + 1) = β j t) ∧ (∀ j, InjOn (β j) (Ico 0 1)) ∧
      (∀ j, range (β j) = {x : s31dt_Core F | x.val ∈ frontier (F.D j)}) ∧
      ∀ j t, (β j t).val = v j (Circle.exp (2 * Real.pi * t) : ℂ) := by
    choose β h1 h2 h3 h4 using fun j => s78dg_core_circle F v R hR hs hD hdisj j
    exact ⟨β, h1, h2, h3, h4⟩
  obtain ⟨χ, ε, hε, hχ⟩ := s78rb_boundary_characters F hm β hβper hβinj hβrange
  let k0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  choose Lf hLf1 hLf2 using hχ
  have hcoreeq := s78dg_core_eq F v R hR hs hD
  let ι₀ : C(↥((⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ), s31dt_Core F) :=
    ⟨fun x => ⟨x.1, by rw [hcoreeq]; exact x.2⟩, by fun_prop⟩
  let f₀ : C(s31dt_Core F, AddCircle (1 : ℝ)) := ∑ k ∈ Finset.univ.erase k0, χ k
  let f : C(↥((⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ), AddCircle (1 : ℝ)) := f₀.comp ι₀
  refine ⟨f, fun j => ?_⟩
  let L : C(ℝ, ℝ) := ∑ k ∈ Finset.univ.erase k0, Lf k j
  let K : ℤ := ε j * ((if j ∈ Finset.univ.erase k0 then 1 else 0) -
    (Finset.univ.erase k0).card * (if j = k0 then 1 else 0))
  refine ⟨L, K, ?_, ?_, ?_⟩
  · -- oddness
    have hcard : (Finset.univ.erase k0).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hmodd : Odd (m - 1) := by
      obtain ⟨a, ha⟩ := hmeven
      refine ⟨a - 1, ?_⟩
      omega
    have hεodd : Odd (ε j) := by
      rcases hε j with h | h <;> rw [h] <;> decide
    by_cases hj : j = k0
    · have hnot : j ∉ Finset.univ.erase k0 := by simp [hj]
      have : K = ε j * (-(((m - 1 : ℕ) : ℤ))) := by
        simp only [K, hcard]
        rw [if_neg hnot, if_pos hj]
        push_cast; ring
      rw [this]
      exact hεodd.mul (((Int.odd_coe_nat _).mpr hmodd).neg)
    · have hin : j ∈ Finset.univ.erase k0 := by simp [hj]
      have : K = ε j := by
        simp [K, hin, hj]
      rw [this]; exact hεodd
  · intro t h
    have hmem : ι₀ ⟨v j (Circle.exp (2 * Real.pi * t) : ℂ), h⟩ = β j t :=
      Subtype.ext (hβval j t).symm
    show f₀ (ι₀ ⟨_, h⟩) = _
    rw [hmem]
    simp only [f₀, L, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sum_apply]
    have hsum : ∀ (s : Finset (Fin m)) (a : Fin m → ℝ),
        ((∑ i ∈ s, a i : ℝ) : AddCircle (1 : ℝ)) = ∑ i ∈ s, ((a i : ℝ) : AddCircle (1 : ℝ)) :=
      fun s a => map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a s
    rw [hsum]
    exact Finset.sum_congr rfl fun k _ => hLf1 k j t
  · intro t
    simp only [L, ContinuousMap.sum_apply]
    rw [Finset.sum_congr rfl fun k _ => hLf2 k j t, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const, nsmul_eq_mul]
    simp only [K, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
      Int.cast_natCast]
    rfl

/-- The radial clamp onto the complement of the open unit disc. -/
theorem s82bc_clamp_facts :
    (∀ z : ℂ, 1 ≤ ‖z‖ → (((max ‖z‖ 1 / ‖z‖ : ℝ) : ℂ)) * z = z) ∧
    (∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 → ‖(((max ‖z‖ 1 / ‖z‖ : ℝ) : ℂ)) * z‖ = 1) ∧
    ContinuousOn (fun z : ℂ => (((max ‖z‖ 1 / ‖z‖ : ℝ) : ℂ)) * z) {z : ℂ | z ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have h0 : ‖z‖ ≠ 0 := by positivity
    rw [max_eq_left hz, div_self h0]; simp
  · intro z hz hz1
    have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [norm_mul, Complex.norm_real, max_eq_right hz1, Real.norm_of_nonneg (by positivity)]
    field_simp
  · intro z hz
    have h0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply Complex.continuous_ofReal.continuousAt.comp
      exact ((continuous_norm.max continuous_const).continuousAt).div continuous_norm.continuousAt h0
    · exact continuousAt_id

/-- **Extension of a circle character from the core over the discs.**  A continuous circle-valued
map on the complement of the open unit discs of the charts `v j` extends to the complement of the
centres, by the radial retraction. -/
theorem s82bc_extend_character {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, Metric.closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint (v i '' Metric.closedBall (0 : ℂ) (R i))
      (v j '' Metric.closedBall (0 : ℂ) (R j)))
    (p : Fin m → X) (hp : ∀ j, p j = v j 0)
    (χ : C(↥((⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ), AddCircle (1 : ℝ))) :
    ∃ f : C(↥((range p)ᶜ), AddCircle (1 : ℝ)),
      ∀ (x : X) (hx : x ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ) (hxU : x ∈ (range p)ᶜ),
        f ⟨x, hxU⟩ = χ ⟨x, hx⟩ := by
  classical
  obtain ⟨cl1, cl2, cl3⟩ := s82bc_clamp_facts
  set clamp : ℂ → ℂ := fun z => (((max ‖z‖ 1 / ‖z‖ : ℝ) : ℂ)) * z with hclamp
  have hsrc : ∀ j, Metric.closedBall (0 : ℂ) 1 ⊆ (v j).source := fun j =>
    (Metric.closedBall_subset_closedBall (hR j).le).trans (hs j)
  have hDdisj : Pairwise fun i j => Disjoint (v i '' Metric.closedBall (0 : ℂ) 1)
      (v j '' Metric.closedBall (0 : ℂ) 1) := fun i j hij =>
    (hdisj hij).mono (image_mono (Metric.closedBall_subset_closedBall (hR i).le))
      (image_mono (Metric.closedBall_subset_closedBall (hR j).le))
  let ret : Fin m → X → X := fun j x => v j (clamp ((v j).symm x))
  let r : X → X := fun x =>
    if h : ∃ j, x ∈ v j '' Metric.closedBall (0 : ℂ) 1 then ret h.choose x else x
  have hrD : ∀ j x, x ∈ v j '' Metric.closedBall (0 : ℂ) 1 → r x = ret j x := by
    intro j x hx
    have h : ∃ j, x ∈ v j '' Metric.closedBall (0 : ℂ) 1 := ⟨j, hx⟩
    simp only [r, dif_pos h]
    have := h.choose_spec
    by_cases hj : h.choose = j
    · rw [hj]
    · exact (Set.disjoint_left.1 (hDdisj hj) this hx).elim
  have hrN : ∀ x, (∀ j, x ∉ v j '' Metric.closedBall (0 : ℂ) 1) → r x = x := by
    intro x hx
    have h : ¬ ∃ j, x ∈ v j '' Metric.closedBall (0 : ℂ) 1 := by
      rintro ⟨j, hj⟩; exact hx j hj
    simp only [r, dif_neg h]
  -- the retraction on a disc point
  have hretD : ∀ j z, ‖z‖ ≤ 1 → ret j (v j z) = v j (clamp z) := by
    intro j z hz
    simp only [ret]
    rw [(v j).left_inv (hsrc j (mem_closedBall_zero_iff.mpr hz))]
  have hcore : ∀ x, x ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ → r x = x := by
    intro x hx
    by_cases hD : ∃ j, x ∈ v j '' Metric.closedBall (0 : ℂ) 1
    · obtain ⟨j, z, hz, rfl⟩ := hD
      have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      have hz2 : 1 ≤ ‖z‖ := by
        by_contra hlt
        exact hx (mem_iUnion.mpr ⟨j, z, mem_ball_zero_iff.mpr (not_le.mp hlt), rfl⟩)
      rw [hrD j _ ⟨z, hz, rfl⟩, hretD j z hz1]
      have : clamp z = z := cl1 z hz2
      rw [this]
    · apply hrN
      intro j hj
      apply hD ⟨j, hj⟩
  have hretcore : ∀ x, x ∉ range p → r x ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ := by
    intro x hx
    by_cases hD : ∃ j, x ∈ v j '' Metric.closedBall (0 : ℂ) 1
    · obtain ⟨j, z, hz, rfl⟩ := hD
      have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact hx ⟨j, hp j⟩
      rw [hrD j _ ⟨z, hz, rfl⟩, hretD j z hz1]
      have hn : ‖clamp z‖ = 1 := cl2 z hz0 hz1
      rintro hmem
      obtain ⟨i, w, hw, hwe⟩ := mem_iUnion.mp hmem
      have hwR : w ∈ Metric.closedBall (0 : ℂ) (R i) :=
        Metric.closedBall_subset_closedBall (hR i).le (Metric.ball_subset_closedBall hw)
      have hcR : clamp z ∈ Metric.closedBall (0 : ℂ) (R j) := by
        rw [mem_closedBall_zero_iff, hn]; exact (hR j).le
      by_cases hij : i = j
      · subst hij
        have := (v i).injOn (hs i hwR) (hs i hcR) hwe
        rw [this, mem_ball_zero_iff, hn] at hw
        exact lt_irrefl _ hw
      · exact Set.disjoint_left.1 (hdisj hij) ⟨w, hwR, hwe⟩ ⟨_, hcR, rfl⟩
    · rw [hrN x (fun j hj => hD ⟨j, hj⟩)]
      intro hmem
      obtain ⟨i, w, hw, rfl⟩ := mem_iUnion.mp hmem
      exact hD ⟨i, w, Metric.ball_subset_closedBall hw, rfl⟩
  -- continuity of the retraction on the complement of the centres
  have hcoreClosed : IsClosed ((⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ) := by
    apply IsOpen.isClosed_compl
    exact isOpen_iUnion fun j => (v j).isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans (hsrc j))
  have hDclosed : ∀ j, IsClosed (v j '' Metric.closedBall (0 : ℂ) 1) := fun j =>
    (IsCompact.image_of_continuousOn (isCompact_closedBall _ _)
      ((v j).continuousOn.mono (hsrc j))).isClosed
  have hg : Continuous (fun x : ↥((range p)ᶜ) => r x.1) := by
    refine LocallyFinite.continuous (ι := Option (Fin m))
      (f := fun o => match o with
        | none => {x : ↥((range p)ᶜ) | x.1 ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ}
        | some j => {x : ↥((range p)ᶜ) | x.1 ∈ v j '' Metric.closedBall (0 : ℂ) 1})
      (locallyFinite_of_finite _) ?_ ?_ ?_
    · rw [eq_univ_iff_forall]
      intro x
      by_cases hx : x.1 ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ
      · exact mem_iUnion.mpr ⟨none, hx⟩
      · obtain ⟨j, z, hz, hzx⟩ := mem_iUnion.mp (not_not.mp hx)
        exact mem_iUnion.mpr ⟨some j, z, Metric.ball_subset_closedBall hz, hzx⟩
    · intro o
      cases o with
      | none => exact hcoreClosed.preimage continuous_subtype_val
      | some j => exact (hDclosed j).preimage continuous_subtype_val
    · intro o
      cases o with
      | none =>
        refine (continuous_subtype_val.continuousOn).congr ?_
        intro x hx
        exact hcore x.1 hx
      | some j =>
        have hcont : ∀ x : X, x ∈ v j '' Metric.closedBall (0 : ℂ) 1 → x ≠ p j →
            ContinuousAt (ret j) x := by
          rintro _ ⟨z, hz, rfl⟩ hxp
          have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
          have hz0 : z ≠ 0 := by
            rintro rfl; exact hxp (hp j).symm
          have hcz : clamp z ∈ (v j).source := hs j (by
            rw [mem_closedBall_zero_iff, cl2 z hz0 hz1]; exact (hR j).le)
          have hsymm : (v j).symm (v j z) = z := (v j).left_inv (hsrc j hz)
          have hxt : v j z ∈ (v j).target := (v j).map_source (hsrc j hz)
          have h1 : ContinuousAt (v j).symm (v j z) := (v j).continuousAt_symm hxt
          have h2 : ContinuousAt clamp ((v j).symm (v j z)) := by
            rw [hsymm]
            exact (cl3.continuousAt (isOpen_ne.mem_nhds hz0))
          have h3 : ContinuousAt (v j) (clamp ((v j).symm (v j z))) := by
            rw [hsymm]; exact (v j).continuousAt hcz
          exact ContinuousAt.comp (g := ⇑(v j)) (f := fun x => clamp ((v j).symm x)) (x := v j z) h3 (h2.comp h1)
        refine ContinuousOn.congr (f := fun x : ↥((range p)ᶜ) => ret j x.1) ?_ ?_
        · intro x hx
          have hne : x.1 ≠ p j := fun h => x.2 ⟨j, h.symm⟩
          exact ((hcont x.1 hx hne).comp continuous_subtype_val.continuousAt).continuousWithinAt
        · intro x hx
          exact hrD j x.1 hx
  have hmem : ∀ x : ↥((range p)ᶜ), r x.1 ∈ (⋃ j, v j '' Metric.ball (0 : ℂ) 1)ᶜ :=
    fun x => hretcore x.1 x.2
  refine ⟨⟨fun x => χ ⟨r x.1, hmem x⟩, χ.continuous.comp (hg.subtype_mk hmem)⟩, ?_⟩
  intro x hx hxU
  show χ ⟨r x, hmem ⟨x, hxU⟩⟩ = χ ⟨x, hx⟩
  congr 1
  exact Subtype.ext (hcore x hx)

/-- Points of the boundary circles of the discs lie in the core. -/
theorem s82bc_circle_mem_core {X : Type u} [TopologicalSpace X] {m : ℕ}
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, Metric.closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint (v i '' Metric.closedBall (0 : ℂ) (R i))
      (v j '' Metric.closedBall (0 : ℂ) (R j)))
    (j : Fin m) (u : ℂ) (hu : ‖u‖ = 1) :
    v j u ∈ (⋃ i, v i '' Metric.ball (0 : ℂ) 1)ᶜ := by
  intro hmem
  obtain ⟨i, w, hw, hwe⟩ := mem_iUnion.mp hmem
  have hwR : w ∈ Metric.closedBall (0 : ℂ) (R i) :=
    Metric.closedBall_subset_closedBall (hR i).le (Metric.ball_subset_closedBall hw)
  have huR : u ∈ Metric.closedBall (0 : ℂ) (R j) := by
    rw [mem_closedBall_zero_iff, hu]; exact (hR j).le
  by_cases hij : i = j
  · subst hij
    have := (v i).injOn (hs i hwR) (hs i huR) hwe
    rw [this, mem_ball_zero_iff, hu] at hw
    exact lt_irrefl _ hw
  · exact Set.disjoint_left.1 (hdisj hij) ⟨w, hwR, hwe⟩ ⟨u, huR, rfl⟩

/-- A character `π₁ → ℤ/2` of a circle-valued map: the winding number mod 2.  It is nontrivial on
every conjugated loop along which the map winds an odd number of times. -/
theorem s82bc_winding_parity {Y : Type*} [TopologicalSpace Y] (f : C(Y, AddCircle (1 : ℝ)))
    (x₀ : Y) :
    ∃ χ : FundamentalGroup Y x₀ →* Multiplicative (ZMod 2),
      ∀ (y : Y) (ℓ : Path y y) (a : Path x₀ y) (Λ : C(unitInterval, ℝ)) (k : ℤ),
        (∀ t, f (ℓ t) = (Λ t : AddCircle (1 : ℝ))) → Λ 1 = Λ 0 + k → Odd k →
        χ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm))) ≠ 1 := by
  classical
  obtain ⟨ψ, hψ⟩ := s78rb_winding_hom f x₀
  -- integrality
  have hint : ∀ γ : FundamentalGroup Y x₀, ∃ n : ℤ, ψ (Additive.ofMul γ) = n := by
    intro γ
    obtain ⟨ℓ₀, hℓ₀⟩ := Quotient.exists_rep γ
    -- a real lift of `f ∘ ℓ₀`
    obtain ⟨L, hL⟩ := s78rb_lift_real
      ⟨fun t => f (ℓ₀ (Set.projIcc (0 : ℝ) 1 zero_le_one t)), by fun_prop⟩
    let Λ : C(unitInterval, ℝ) := ⟨fun t => L t, by fun_prop⟩
    have hΛ : ∀ t, f (ℓ₀ t) = (Λ t : AddCircle (1 : ℝ)) := by
      intro t
      show f (ℓ₀ t) = ((L (t : ℝ) : ℝ) : AddCircle (1 : ℝ))
      rw [← hL (t : ℝ)]
      show f (ℓ₀ t) = f (ℓ₀ (Set.projIcc (0 : ℝ) 1 zero_le_one (t : ℝ)))
      rw [Set.projIcc_val]
    have h01 : ((Λ 1 : ℝ) : AddCircle (1 : ℝ)) = (Λ 0 : ℝ) := by
      rw [← hΛ 1, ← hΛ 0, ℓ₀.source, ℓ₀.target]
    obtain ⟨k, hk⟩ := s78rb_coe_eq_int _ _ h01
    refine ⟨k, ?_⟩
    have := hψ x₀ ℓ₀ (Path.refl x₀) Λ hΛ
    have hcl : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (((Path.refl x₀).trans ℓ₀).trans
        (Path.refl x₀).symm)) = γ := by
      rw [← hℓ₀]
      have hsr : (Path.Homotopic.Quotient.refl x₀).symm = Path.Homotopic.Quotient.refl x₀ := by
        have := Path.Homotopic.Quotient.symm_trans (Path.Homotopic.Quotient.refl x₀)
        rwa [Path.Homotopic.Quotient.trans_refl] at this
      show Path.Homotopic.Quotient.mk (((Path.refl x₀).trans ℓ₀).trans (Path.refl x₀).symm) =
        Path.Homotopic.Quotient.mk ℓ₀
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_refl, hsr,
        Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]
    rw [hcl] at this
    rw [this, hk]; ring
  choose n hn using hint
  let ψ' : Additive (FundamentalGroup Y x₀) →+ ℤ :=
    { toFun := fun c => n (Additive.toMul c)
      map_zero' := by
        have := hn 1
        have h0 : ψ (Additive.ofMul 1) = 0 := map_zero ψ
        rw [h0] at this
        exact_mod_cast this.symm
      map_add' := by
        intro c d
        have h1 := hn (Additive.toMul c * Additive.toMul d)
        have h2 := hn (Additive.toMul c)
        have h3 := hn (Additive.toMul d)
        have : ψ (Additive.ofMul (Additive.toMul c * Additive.toMul d)) =
            ψ (Additive.ofMul (Additive.toMul c)) + ψ (Additive.ofMul (Additive.toMul d)) :=
          map_add ψ _ _
        rw [h1, h2, h3] at this
        exact_mod_cast this }
  let χ : FundamentalGroup Y x₀ →* Multiplicative (ZMod 2) :=
    { toFun := fun c => Multiplicative.ofAdd ((n c : ℤ) : ZMod 2)
      map_one' := by
        have := ψ'.map_zero
        show Multiplicative.ofAdd ((n 1 : ℤ) : ZMod 2) = 1
        have h : n 1 = 0 := this
        rw [h]; simp
      map_mul' := by
        intro c d
        have := ψ'.map_add (Additive.ofMul c) (Additive.ofMul d)
        have h : n (c * d) = n c + n d := this
        show Multiplicative.ofAdd ((n (c * d) : ℤ) : ZMod 2) = _
        rw [h]; push_cast; rfl }
  refine ⟨χ, fun y ℓ a Λ k hΛ hk hodd => ?_⟩
  have hw := hψ y ℓ a Λ hΛ
  have hn' := hn (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)))
  rw [hw, hk] at hn'
  have hnk : n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm))) = k := by
    have : ((n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm))) : ℤ) : ℝ) = k := by
      rw [← hn']; ring
    exact_mod_cast this
  intro h1
  have h2 : ((n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm))) : ℤ) : ZMod 2) = 0 := by
    have h1' : Multiplicative.ofAdd
        ((n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm))) : ℤ) :
          ZMod 2) = 1 := h1
    simpa using congrArg Multiplicative.toAdd h1'
  rw [hnk] at h2
  have : (2 : ℤ) ∣ k := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp h2
    simpa using this
  exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)

/-- A surjective character onto `ℤ/2` has an index-two kernel. -/
theorem s82bc_index_two_of_char {G : Type*} [Group G] (χ : G →* Multiplicative (ZMod 2))
    (g : G) (hg : χ g ≠ 1) : χ.ker.index = 2 := by
  have hsurj : Function.Surjective χ := by
    intro z
    have h1 : ∀ w : Multiplicative (ZMod 2), w = 1 ∨ w = χ g := by
      intro w
      have : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b := by decide
      by_cases hw : w = 1
      · exact Or.inl hw
      · refine Or.inr ?_
        apply Multiplicative.toAdd.injective
        exact this _ _ (fun h => hw (by simpa using congrArg Multiplicative.ofAdd h))
          (fun h => hg (by simpa using congrArg Multiplicative.ofAdd h))
    rcases h1 z with h | h
    · exact ⟨1, by rw [map_one, h]⟩
    · exact ⟨g, h.symm⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ hsurj]
  rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]
  simp [Nat.card_eq_fintype_card]

open scoped Pointwise in
/-- The unit-disc chart attached to a chart `E` and a radius `ρ`: `z ↦ E⁻¹(ρ z)`. -/
theorem s82bc_scaled_chart {X : Type u} [TopologicalSpace X] (E : OpenPartialHomeomorph X ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hE : Metric.ball (0 : ℂ) (3 * ρ) ⊆ E.target) :
    ∃ v : OpenPartialHomeomorph ℂ X, (∀ z, v z = E.symm ((ρ : ℂ) * z)) ∧
      Metric.closedBall (0 : ℂ) 2 ⊆ v.source ∧
      ∀ s : ℝ, 0 ≤ s → v '' Metric.closedBall (0 : ℂ) s = E.symm '' Metric.closedBall (0 : ℂ) (ρ * s) := by
  have hne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  let h : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (ρ : ℂ) hne
  refine ⟨h.toOpenPartialHomeomorph.trans E.symm, fun z => rfl, ?_, ?_⟩
  · intro z hz
    refine ⟨trivial, ?_⟩
    show (ρ : ℂ) * z ∈ E.symm.source
    apply hE
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have := mem_closedBall_zero_iff.mp hz
    nlinarith
  · intro s hs
    have : (h.toOpenPartialHomeomorph.trans E.symm) '' Metric.closedBall (0 : ℂ) s =
        E.symm '' ((fun z : ℂ => (ρ : ℂ) * z) '' Metric.closedBall (0 : ℂ) s) := by
      rw [Set.image_image]; rfl
    rw [this]
    congr 1
    have := smul_closedBall (ρ : ℂ) (0 : ℂ) hs
    simp only [smul_eq_mul, mul_zero, Complex.norm_real, Real.norm_of_nonneg hρ.le] at this
    have e2 : (fun z : ℂ => (ρ : ℂ) * z) '' Metric.closedBall (0 : ℂ) s =
        (ρ : ℂ) • Metric.closedBall (0 : ℂ) s := Set.image_smul (a := (ρ : ℂ)) (t := _)
    rw [e2, this]

/-- **The puncture data for an even, nonempty set of punctures.**  The complement `U` of `P` is
connected, and carries an index-two subgroup `K` of its fundamental group which is not hit by the
loop around any puncture. -/
theorem s82bc_puncture_data_pos {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [CompactSpace X] [IsManifold 𝓘(ℂ) ω X] {g : ℕ} (hX : HasGenus X g)
    (P : Finset X) (hPe : Even P.card) (hP0 : P.card ≠ 0) :
    ∃ (U : TopologicalSpace.Opens X), (U : Set X)ᶜ = ↑P ∧ ∃ (_ : ConnectedSpace U) (x₀ : U)
      (K : Subgroup (FundamentalGroup U x₀)), K.index = 2 ∧
      ∀ q : ↥P, ∃ (E : OpenPartialHomeomorph X ℂ) (r ρ : ℝ),
        E ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ q.1 ∈ E.source ∧ E q.1 = 0 ∧ 0 < ρ ∧ ρ < r ∧
        Metric.ball (0 : ℂ) r ⊆ E.target ∧ (∀ z : ℂ, z ≠ 0 → ‖z‖ < r → E.symm z ∈ U) ∧
        ∃ (z₀ : U) (a : Path x₀ z₀) (β : Path z₀ z₀), (z₀ : X) = E.symm ρ ∧
          (∀ t : unitInterval, (β t : X) =
            E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) ∧
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K := by
  classical
  set m := P.card with hm
  have hm0 : m ≠ 0 := hP0
  let eqv : ↥P ≃ Fin m := P.equivFin
  let p : Fin m → X := fun j => (eqv.symm j).1
  have hp : Function.Injective p := fun a b h => eqv.symm.injective (Subtype.ext h)
  have hrange : range p = ↑P := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact (eqv.symm j).2
    · intro hx; exact ⟨eqv ⟨x, hx⟩, by simp [p]⟩
  obtain ⟨E, Rr, hRpos, hEprop, hEdisj, hErel, hErel2⟩ := s82bc_local_charts p hp
  let ρ : Fin m → ℝ := fun j => Rr j / 3
  have hρpos : ∀ j, 0 < ρ j := fun j => by have := hRpos j; simp only [ρ]; positivity
  have hρR : ∀ j, ρ j < Rr j := fun j => by have := hRpos j; simp only [ρ]; linarith
  have hball : ∀ j, Metric.ball (0 : ℂ) (Rr j) ⊆ (E j).target := fun j => (hEprop j).2.2.2.1
  have hball3 : ∀ j, Metric.ball (0 : ℂ) (3 * ρ j) ⊆ (E j).target := fun j => by
    have : 3 * ρ j = Rr j := by simp only [ρ]; ring
    rw [this]; exact hball j
  choose v hv1 hv2 hv3 using fun j => s82bc_scaled_chart (E j) (hρpos j) (hball3 j)
  have hEsymm0 : ∀ j, (E j).symm 0 = p j := fun j => by
    have := (E j).left_inv (hEprop j).2.1
    rwa [(hEprop j).2.2.1] at this
  have hp0 : ∀ j, p j = v j 0 := fun j => by rw [hv1, mul_zero]; exact (hEsymm0 j).symm
  have hvdisj : Pairwise fun i j => Disjoint (v i '' Metric.closedBall (0 : ℂ) 2)
      (v j '' Metric.closedBall (0 : ℂ) 2) := by
    intro i j hij
    have hsub : ∀ k, v k '' Metric.closedBall (0 : ℂ) 2 ⊆ (E k).symm '' Metric.ball (0 : ℂ) (Rr k) := by
      intro k
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨(ρ k : ℂ) * z, ?_, (hv1 k z).symm⟩
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρpos k).le]
      have := mem_closedBall_zero_iff.mp hz
      have h3 := hρpos k
      have h4 := hρR k
      simp only [ρ] at h3 h4 ⊢
      nlinarith
    exact (hEdisj hij).mono (hsub i) (hsub j)
  have hDeq : ∀ j, v j '' Metric.closedBall (0 : ℂ) 1 =
      (E j).symm '' Metric.closedBall (0 : ℂ) (ρ j) := fun j => by
    rw [hv3 j 1 zero_le_one, mul_one]
  have hdisc : ∀ j, IsClosedDiscIn (v j '' Metric.closedBall (0 : ℂ) 1) := by
    intro j
    rw [hDeq]
    have hsub : Metric.closedBall (chartAt ℂ (p j) (p j)) (ρ j) ⊆ (chartAt ℂ (p j)).target := by
      intro w hw
      have h1 : w - chartAt ℂ (p j) (p j) ∈ Metric.closedBall (0 : ℂ) (ρ j) := by
        rw [mem_closedBall_zero_iff]
        simpa [dist_eq_norm] using hw
      have h2 : w - chartAt ℂ (p j) (p j) ∈ (E j).target :=
        hball j (Metric.closedBall_subset_ball (hρR j) h1)
      have := (hErel2 j _).mp h2
      simpa using this
    have heq : (E j).symm '' Metric.closedBall (0 : ℂ) (ρ j) =
        (chartAt ℂ (p j)).symm '' Metric.closedBall (chartAt ℂ (p j) (p j)) (ρ j) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w + chartAt ℂ (p j) (p j), ?_, (hErel j w).symm⟩
        rw [mem_closedBall_iff_norm] <;> skip
        simpa [dist_eq_norm] using mem_closedBall_zero_iff.mp hw
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w - chartAt ℂ (p j) (p j), ?_, ?_⟩
        · rw [mem_closedBall_zero_iff]; simpa [dist_eq_norm] using hw
        · rw [hErel j]; simp
    rw [heq]
    exact s82bc_closedDisc_round (p j) (hρpos j) hsub
  have hDclosed : ∀ j, IsClosed (v j '' Metric.closedBall (0 : ℂ) 1) := fun j =>
    (IsCompact.image_of_continuousOn (isCompact_closedBall _ _)
      ((v j).continuousOn.mono ((Metric.closedBall_subset_closedBall (by norm_num)).trans (hv2 j)))).isClosed
  -- the surface `S` minus the discs, and its connectedness
  have hSopen : IsOpen (⋃ j, v j '' Metric.closedBall (0 : ℂ) 1)ᶜ :=
    (isClosed_iUnion_of_finite hDclosed).isOpen_compl
  let S : TopologicalSpace.Opens X := ⟨_, hSopen⟩
  have hSconn : IsConnected ((S : Set X)) := by
    have := s82bc_complement_connected E Rr ρ (fun j => (hρpos j).le) hρR hball hEdisj
    show IsConnected (⋃ j, v j '' Metric.closedBall (0 : ℂ) 1)ᶜ
    simp only [hDeq]
    exact this
  haveI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hSconn
  obtain ⟨fc, hfc⟩ := s82bc_core_odd_character hX hm0 hPe v (fun _ => 2) (fun _ => by norm_num)
    hv2 hvdisj hdisc S rfl
  obtain ⟨fU, hfU⟩ := s82bc_extend_character v (fun _ => 2) (fun _ => by norm_num) hv2 hvdisj p
    hp0 fc
  -- the punctured surface
  have hUopen : IsOpen (range p)ᶜ := (Set.finite_range p).isClosed.isOpen_compl
  let U : TopologicalSpace.Opens X := ⟨(range p)ᶜ, hUopen⟩
  have hUconn : IsConnected ((range p)ᶜ) := by
    have := s82bc_complement_connected E Rr (fun _ => 0) (fun _ => le_refl _) hRpos hball hEdisj
    have hset : (⋃ i, (E i).symm '' Metric.closedBall (0 : ℂ) 0) = range p := by
      ext x
      simp only [Metric.closedBall_zero, mem_iUnion, Set.image_singleton, mem_singleton_iff,
        mem_range]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hEsymm0]⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hEsymm0]⟩
    rwa [hset] at this
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUconn
  haveI : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
  haveI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  have hUne : Nonempty U := inferInstance
  let x₀ : U := Classical.arbitrary U
  obtain ⟨χ, hχ⟩ := s82bc_winding_parity fU x₀
  have hloop : ∀ j, ∃ (z₀ : U) (a : Path x₀ z₀) (β : Path z₀ z₀), (z₀ : X) = (E j).symm (ρ j) ∧
      (∀ t : unitInterval, (β t : X) =
        (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) ∧
      χ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm))) ≠ 1 := by
    intro j
    have hcirc : ∀ t : ℝ, ‖(ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t)‖ = ρ j := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρpos j).le]
      have : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
        have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
        rw [show (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
        exact this
      rw [this, mul_one]
    have hmemU : ∀ t : ℝ, (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t)) ∈
        (range p)ᶜ := by
      intro t
      refine (hEprop j).2.2.2.2 _ ?_ ?_
      · rw [hcirc]; exact hρR j
      · intro h0; have := hcirc t; rw [h0, norm_zero] at this; exact (hρpos j).ne this
    have htgt : ∀ t : ℝ, (ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) ∈ (E j).target :=
      fun t => hball j (by rw [mem_ball_zero_iff, hcirc]; exact hρR j)
    have hcont : Continuous (fun t : ℝ =>
        (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t))) :=
      (E j).symm.continuousOn.comp_continuous (by fun_prop) htgt
    have hone : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      simpa using Complex.exp_two_pi_mul_I
    have hzero : Complex.exp (2 * Real.pi * Complex.I * ((0 : ℝ) : ℂ)) = 1 := by simp
    let z₀ : U := ⟨(E j).symm (ρ j), by
      have := hmemU 0
      rwa [hzero, mul_one] at this⟩
    let β : Path z₀ z₀ :=
      { toFun := fun t => ⟨(E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))),
          hmemU t⟩
        continuous_toFun := (hcont.comp continuous_subtype_val).subtype_mk _
        source' := by
          apply Subtype.ext
          show (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I *
            (((0 : unitInterval) : ℝ) : ℂ))) = (E j).symm (ρ j : ℂ)
          simp
        target' := by
          apply Subtype.ext
          show (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I *
            (((1 : unitInterval) : ℝ) : ℂ))) = (E j).symm (ρ j : ℂ)
          simp [Complex.exp_two_pi_mul_I] }
    let a : Path x₀ z₀ := PathConnectedSpace.somePath x₀ z₀
    refine ⟨z₀, a, β, rfl, fun t => rfl, ?_⟩
    obtain ⟨L, k, hkodd, hLval, hLper⟩ := hfc j
    let Λ : C(unitInterval, ℝ) := ⟨fun t => L t, L.continuous.comp continuous_subtype_val⟩
    have hcircle : ∀ t : ℝ, v j (Circle.exp (2 * Real.pi * t) : ℂ) =
        (E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t)) := by
      intro t
      rw [hv1, Circle.coe_exp]
      congr 2
      push_cast; ring
    refine hχ z₀ β a Λ k ?_ ?_ hkodd
    · intro t
      have hmem := s82bc_circle_mem_core v (fun _ => 2) (fun _ => by norm_num) hv2 hvdisj j
        (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) (Circle.norm_coe _)
      have hxU : (v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) ∈ (range p)ᶜ := by
        rw [hcircle]; exact hmemU t
      have h1 := hfU _ hmem hxU
      have h2 := hLval (t : ℝ) hmem
      show fU ⟨(E j).symm _, hmemU t⟩ = _
      have h3 : fU ⟨(E j).symm ((ρ j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))),
          hmemU t⟩ = fU ⟨v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ), hxU⟩ := by
        congr 1; exact Subtype.ext (hcircle _).symm
      rw [h3, h1, h2]; rfl
    · have := hLper 0
      simpa [Λ] using this
  -- assemble
  have hrangeU : (U : Set X)ᶜ = ↑P := by
    show ((range p)ᶜ)ᶜ = _
    rw [compl_compl, hrange]
  refine ⟨U, hrangeU, inferInstance, x₀, χ.ker, ?_, ?_⟩
  · obtain ⟨z₀, a, β, -, -, hne⟩ := hloop ⟨0, Nat.pos_of_ne_zero hm0⟩
    exact s82bc_index_two_of_char χ _ hne
  · intro q
    set j := eqv q with hj
    have hqj : q.1 = p j := by simp [hj, p]
    obtain ⟨z₀, a, β, hz₀, hβ, hne⟩ := hloop j
    refine ⟨E j, Rr j, ρ j, (hEprop j).1, ?_, ?_, hρpos j, hρR j, hball j, ?_, z₀, a, β, hz₀, hβ, ?_⟩
    · rw [hqj]; exact (hEprop j).2.1
    · rw [hqj]; exact (hEprop j).2.2.1
    · intro z hz hzr
      exact (hEprop j).2.2.2.2 z hzr hz
    · intro hmem
      exact hne (MonoidHom.mem_ker.mp hmem)

/-- For `g ≠ 0` the surface group has a character onto `ℤ/2` sending the first `a`-generator to `1`. -/
theorem s82bc_surfaceGroup_char (g : ℕ) (hg : g ≠ 0) :
    ∃ (χ : surfaceGroup g →* Multiplicative (ZMod 2)) (x : surfaceGroup g), χ x ≠ 1 := by
  unfold surfaceGroup
  let f : Fin g ⊕ Fin g → Multiplicative (ZMod 2) :=
    Sum.elim (fun i => if i.val = 0 then Multiplicative.ofAdd 1 else 1) (fun _ => 1)
  have key : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ * b⁻¹ = 1 := by decide
  have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin g =>
      FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
        Set (FreeGroup (Fin g ⊕ Fin g))), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [mem_singleton_iff] at hr
    subst hr
    rw [map_list_prod, List.map_ofFn]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have h := key (f (Sum.inl i)) (f (Sum.inr i))
    have e1 : ∀ x : Fin g ⊕ Fin g, FreeGroup.lift f (FreeGroup.of x)⁻¹ = (f x)⁻¹ := by
      intro x; rw [map_inv, FreeGroup.lift_apply_of]
    simp only [Function.comp_apply, map_mul, FreeGroup.lift_apply_of, e1]
    exact h
  refine ⟨PresentedGroup.toGroup hrel, PresentedGroup.of (Sum.inl ⟨0, Nat.pos_of_ne_zero hg⟩), ?_⟩
  rw [PresentedGroup.toGroup.of]
  simp [f]

/-- **The puncture data**, all cases. -/
theorem s82bc_puncture_data {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [CompactSpace X] [IsManifold 𝓘(ℂ) ω X] {g : ℕ} (hX : HasGenus X g)
    (P : Finset X) (hPe : Even P.card) (hgn : g ≠ 0 ∨ P.card ≠ 0) :
    ∃ (U : TopologicalSpace.Opens X), (U : Set X)ᶜ = ↑P ∧ ∃ (_ : ConnectedSpace U) (x₀ : U)
      (K : Subgroup (FundamentalGroup U x₀)), K.index = 2 ∧
      ∀ q : ↥P, ∃ (E : OpenPartialHomeomorph X ℂ) (r ρ : ℝ),
        E ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ q.1 ∈ E.source ∧ E q.1 = 0 ∧ 0 < ρ ∧ ρ < r ∧
        Metric.ball (0 : ℂ) r ⊆ E.target ∧ (∀ z : ℂ, z ≠ 0 → ‖z‖ < r → E.symm z ∈ U) ∧
        ∃ (z₀ : U) (a : Path x₀ z₀) (β : Path z₀ z₀), (z₀ : X) = E.symm ρ ∧
          (∀ t : unitInterval, (β t : X) =
            E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) ∧
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K := by
  classical
  by_cases hP0 : P.card = 0
  · have hg : g ≠ 0 := by
      rcases hgn with h | h
      · exact h
      · exact absurd hP0 h
    have hPe' : P = ∅ := Finset.card_eq_zero.mp hP0
    subst hPe'
    let U : TopologicalSpace.Opens X := ⟨univ, isOpen_univ⟩
    let e : ↥U ≃ₜ X := Homeomorph.Set.univ X
    haveI : ConnectedSpace U := e.symm.surjective.connectedSpace e.symm.continuous
    let x₀ : U := e.symm (Classical.arbitrary X)
    obtain ⟨ψ⟩ := s78dg_pi1_transport e hX.2 x₀
    obtain ⟨χ0, x, hx⟩ := s82bc_surfaceGroup_char g hg
    let χ : FundamentalGroup U x₀ →* Multiplicative (ZMod 2) := χ0.comp ψ.toMonoidHom
    refine ⟨U, ?_, inferInstance, x₀, χ.ker, ?_, ?_⟩
    · ext x; simp [U]
    · apply s82bc_index_two_of_char χ (ψ.symm x)
      simp only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hx
    · intro q
      exact absurd q.2 (Finset.notMem_empty _)
  · exact s82bc_puncture_data_pos hX P hPe hP0

end LiZhongQC
