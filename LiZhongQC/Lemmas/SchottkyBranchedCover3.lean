import LiZhongQC.Lemmas.SchottkyBranchedCover1
import Mathlib.Analysis.Complex.Convex

/-!
# Local model of a double cover at a puncture

Over a chart punctured disc `D*_r` around a puncture, a two-sheeted covering `q : Y → S` with
non-closed lift of the circle is the squaring map: `s82bc_puncture_model`.
-/

open Set Topology Filter

noncomputable section
namespace LiZhongQC
universe u

/-- The punctured disc `D*_r`, as a subtype, is path connected (image of a half plane). -/
theorem s82bc_dstar_isPathConnected (r : ℝ) (hr : 0 < r) :
    IsPathConnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  have hconv : Convex ℝ {u : ℂ | u.re < Real.log r} := convex_halfSpace_re_lt _
  have hne : ({u : ℂ | u.re < Real.log r}).Nonempty := ⟨((Real.log r - 1 : ℝ) : ℂ), by
    show (((Real.log r - 1 : ℝ) : ℂ)).re < Real.log r
    rw [Complex.ofReal_re]; linarith⟩
  have h1 : IsPathConnected {u : ℂ | u.re < Real.log r} := hconv.isPathConnected hne
  have h2 := h1.image Complex.continuous_exp
  convert h2 using 1
  ext z
  simp only [mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨hz0, hz1⟩
    have hz : z ≠ 0 := norm_pos_iff.mp hz0
    refine ⟨Complex.log z, ?_, Complex.exp_log hz⟩
    rw [Complex.log_re]
    exact Real.log_lt_log hz0 hz1
  · rintro ⟨u, hu, rfl⟩
    refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
    rw [Complex.norm_exp]
    calc Real.exp u.re < Real.exp (Real.log r) := Real.exp_lt_exp.mpr hu
      _ = r := Real.exp_log hr


/-- The punctured disc around a puncture, as a subset of the base. -/
theorem s82bc_disc_image {S : Type u} [TopologicalSpace S] (E : OpenPartialHomeomorph S ℂ) (r : ℝ)
    (hE : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} ⊆ E.target) :
    {s : S | s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} =
      E.symm '' {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  ext s
  constructor
  · rintro ⟨hs, hz⟩
    exact ⟨E s, hz, E.left_inv hs⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨E.map_target (hE hz), by rw [E.right_inv (hE hz)]; exact hz⟩

theorem s82bc_disc_open {S : Type u} [TopologicalSpace S] (E : OpenPartialHomeomorph S ℂ) (r : ℝ) :
    IsOpen {s : S | s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} := by
  have : {s : S | s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} =
      E.source ∩ E ⁻¹' {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := rfl
  rw [this]
  refine E.isOpen_inter_preimage ?_
  exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- The homeomorphism between the punctured disc in the base and the model punctured disc. -/
theorem s82bc_disc_homeo {S : Type u} [TopologicalSpace S] (E : OpenPartialHomeomorph S ℂ) (r : ℝ)
    (hE : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} ⊆ E.target) :
    ∃ H : {s : S // s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} ≃ₜ
        {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r}, ∀ s, (H s : ℂ) = E s.1 := by
  refine ⟨
    { toFun := fun s => ⟨E s.1, s.2.2⟩
      invFun := fun z => ⟨E.symm z.1, E.map_target (hE z.2), by
        rw [E.right_inv (hE z.2)]; exact z.2⟩
      left_inv := fun s => Subtype.ext (E.left_inv s.2.1)
      right_inv := fun z => Subtype.ext (E.right_inv (hE z.2))
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun s => rfl⟩
  · refine Continuous.subtype_mk ?_ _
    exact E.continuousOn.comp_continuous continuous_subtype_val
      (fun s : {s : S // s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} => s.property.1)
  · refine Continuous.subtype_mk ?_ _
    exact E.continuousOn_symm.comp_continuous continuous_subtype_val (fun z => hE z.2)


/-- **Local model at a puncture.**  Let `q : Y → S` be a two-sheeted covering and `E` a chart of `S`
whose target contains the punctured disc `D*_r`.  If the lift of the circle of radius `ρ` is never
closed, then over `E⁻¹(D*_r)` the covering is the squaring map: there is an open embedding `w` of
`q⁻¹(E⁻¹ D*_r)` into `ℂ` onto `D*_{√r}` with `w² = E ∘ q`. -/
theorem s82bc_puncture_model {S Y : Type u} [TopologicalSpace S] [TopologicalSpace Y]
    (q : Y → S) (hcov : IsCoveringMap q) (hfib : ∀ s, (q ⁻¹' {s}).ncard = 2)
    (E : OpenPartialHomeomorph S ℂ) (r : ℝ) (hr : 0 < r)
    (hE : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} ⊆ E.target) (ρ : ℝ) (hρ0 : 0 < ρ) (hρr : ρ < r)
    (hmono : ∀ Γ : C(unitInterval, Y),
      (∀ t : unitInterval, q (Γ t) = E.symm (ρ * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) →
      Γ 1 ≠ Γ 0) :
    ∃ w : ↥(q ⁻¹' {s : S | s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}}) → ℂ,
      Topology.IsOpenEmbedding w ∧ range w = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < Real.sqrt r} ∧
      ∀ y, w y ^ 2 = E (q y.1) := by
  classical
  set Dset : Set S := {s : S | s ∈ E.source ∧ E s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}} with hDset
  have hDopen : IsOpen Dset := s82bc_disc_open E r
  have hDimg : Dset = E.symm '' {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := s82bc_disc_image E r hE
  have hDpc : IsPathConnected Dset := by
    rw [hDimg]
    exact (s82bc_dstar_isPathConnected r hr).image' (E.continuousOn_symm.mono hE)
  -- the base point and the circle
  have hρmem : (ρ : ℂ) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ0
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact hρr
  set z₀ : S := E.symm (ρ : ℂ) with hz₀
  have hz₀D : z₀ ∈ Dset := by
    rw [hDimg]; exact ⟨_, hρmem, rfl⟩
  have hcircmem : ∀ t : unitInterval,
      ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))) ∈
        {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
    intro t
    have hn : ‖(ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
      have : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [this, mul_one]
    exact ⟨by rw [hn]; exact hρ0, by rw [hn]; exact hρr⟩
  let c : C(unitInterval, S) := ⟨fun t => E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))),
    E.continuousOn_symm.comp_continuous (by fun_prop) (fun t => hE (hcircmem t))⟩
  have hc0 : c 0 = z₀ := by
    show E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((0 : unitInterval) : ℝ))) = _
    simp [hz₀]
  have hc1 : c 1 = z₀ := by
    show E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((1 : unitInterval) : ℝ))) = _
    simp [hz₀]
  have hcD : ∀ t, c t ∈ Dset := by
    intro t
    rw [hDimg]; exact ⟨_, hcircmem t, rfl⟩
  -- a point over the base point
  obtain ⟨y₀, hy₀⟩ : ∃ y, q y = z₀ := by
    have : (q ⁻¹' {z₀}).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hfib]; norm_num)
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  let Γ : C(unitInterval, Y) := hcov.liftPath c y₀ (by rw [hc0, hy₀])
  have hΓ0 : Γ 0 = y₀ := hcov.liftPath_zero _ _ _
  have hΓq : ∀ t, q (Γ t) = c t := fun t =>
    congrFun (hcov.liftPath_lifts c y₀ (by rw [hc0, hy₀])) t
  have hΓ1 : Γ 1 ≠ y₀ := by
    have := hmono Γ (fun t => hΓq t)
    rwa [hΓ0] at this
  have hΓ1q : q (Γ 1) = z₀ := by rw [hΓq, hc1]
  -- the fibre over the base point is `{y₀, Γ 1}`
  have hfibre : ∀ y, q y = z₀ → y = y₀ ∨ y = Γ 1 := by
    intro y hy
    obtain ⟨u, v, huv, hset⟩ := Set.ncard_eq_two.mp (hfib z₀)
    have h1 : y₀ ∈ q ⁻¹' {z₀} := hy₀
    have h2 : Γ 1 ∈ q ⁻¹' {z₀} := hΓ1q
    have h3 : y ∈ q ⁻¹' {z₀} := hy
    rw [hset] at h1 h2 h3
    simp only [mem_insert_iff, mem_singleton_iff] at h1 h2 h3
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first | exact absurd h2 (by simpa using hΓ1.symm) | simp_all
  -- path connectedness of the preimage
  have hΓA : ∀ t, Γ t ∈ q ⁻¹' Dset := fun t => by
    show q (Γ t) ∈ Dset
    rw [hΓq]; exact hcD t
  have hy₀A : y₀ ∈ q ⁻¹' Dset := by show q y₀ ∈ Dset; rw [hy₀]; exact hz₀D
  have hjoinΓ : JoinedIn (q ⁻¹' Dset) y₀ (Γ 1) :=
    ⟨{ toContinuousMap := Γ, source' := hΓ0, target' := rfl }, hΓA⟩
  have hjoin : ∀ y ∈ q ⁻¹' Dset, JoinedIn (q ⁻¹' Dset) y y₀ := by
    intro y hy
    obtain ⟨σ, hσ⟩ := hDpc.joinedIn (q y) hy z₀ hz₀D
    let Λ : C(unitInterval, Y) := hcov.liftPath (σ : C(unitInterval, S)) y σ.source
    have hΛ0 : Λ 0 = y := hcov.liftPath_zero _ _ _
    have hΛq : ∀ t, q (Λ t) = σ t := fun t =>
      congrFun (hcov.liftPath_lifts (σ : C(unitInterval, S)) y σ.source) t
    have hΛA : ∀ t, Λ t ∈ q ⁻¹' Dset := fun t => by
      show q (Λ t) ∈ Dset
      rw [hΛq]; exact hσ t
    have hj : JoinedIn (q ⁻¹' Dset) y (Λ 1) :=
      ⟨{ toContinuousMap := Λ, source' := hΛ0, target' := rfl }, hΛA⟩
    have hΛ1 : q (Λ 1) = z₀ := by rw [hΛq]; exact σ.target
    rcases hfibre (Λ 1) hΛ1 with h | h
    · rw [h] at hj; exact hj
    · rw [h] at hj
      exact hj.trans hjoinΓ.symm
  have hpc : IsPathConnected (q ⁻¹' Dset) := ⟨y₀, hy₀A, fun y hy => (hjoin y hy).symm⟩
  haveI : PathConnectedSpace ↥(q ⁻¹' Dset) := isPathConnected_iff_pathConnectedSpace.mp hpc
  -- the covering over the model punctured disc
  obtain ⟨H, hH⟩ := s82bc_disc_homeo E r hE
  have hcovA : IsCoveringMap (H ∘ (Dset.restrictPreimage q)) :=
    (hcov.restrictPreimage Dset).homeomorph_comp H
  have hfibA : ∀ z : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r},
      ((H ∘ (Dset.restrictPreimage q)) ⁻¹' {z}).ncard = 2 := by
    intro z
    have : (H ∘ (Dset.restrictPreimage q)) ⁻¹' {z} =
        (Subtype.val : ↥(q ⁻¹' Dset) → Y) ⁻¹' (q ⁻¹' {(H.symm z).1}) := by
      ext y
      simp only [Function.comp_apply, mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        have := congrArg H.symm h
        rw [H.symm_apply_apply] at this
        exact congrArg Subtype.val this
      · intro h
        apply H.symm.injective
        rw [H.symm_apply_apply]
        exact Subtype.ext h
    rw [this, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective, hfib]
    intro y hy
    refine ⟨⟨y, ?_⟩, rfl⟩
    show q y ∈ Dset
    have : q y = (H.symm z).1 := hy
    rw [this]; exact (H.symm z).2
  obtain ⟨w, hwc, hwo, hwi, hwr, hwsq⟩ := s82bc_dstar_double_cover r hr _ hcovA hfibA
  refine ⟨w, Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hwc hwi hwo, hwr, ?_⟩
  intro y
  rw [hwsq]
  show (H (Dset.restrictPreimage q y) : ℂ) = _
  rw [hH]; rfl

end LiZhongQC
