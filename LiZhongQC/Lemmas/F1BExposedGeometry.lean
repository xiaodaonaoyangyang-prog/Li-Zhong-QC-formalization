import LiZhongQC.Lemmas.FoundationQuotient

/-! B1 exposed-frontier geometry. Source-only delivery 001; compilation is owned by Root.
This bundle preserves the helper proof bodies and the frozen B1 target header.
Register this bundle alone if accepted; the component sources remain provenance copies. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

-- Source: F1BFiniteCuts.lean
/-- Distinct hyperbolic centres give equal-radius spheres with at most two common points.
The proof uses the installed two-dimensional Euclidean sphere intersection theorem. -/
theorem ft1gb_two_spheres_finite {a b : UpperHalfPlane} (hab : a ≠ b) (R : ℝ) :
    {p : UpperHalfPlane | dist p a = R ∧ dist p b = R}.Finite := by
  classical
  let S : Set UpperHalfPlane := {p : UpperHalfPlane | dist p a = R ∧ dist p b = R}
  have hcent : (a.center R : ℂ) ≠ (b.center R : ℂ) := by
    intro h
    apply hab
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa only [UpperHalfPlane.coe_re, UpperHalfPlane.center_re] using congrArg Complex.re h
    · have him : a.im * Real.cosh R = b.im * Real.cosh R := congrArg Complex.im h
      exact mul_right_cancel₀ (ne_of_gt (Real.cosh_pos R)) him
  have hdist : ∀ x p : UpperHalfPlane, dist p x = R →
      dist (p : ℂ) (x.center R : ℂ) = x.im * Real.sinh R := by
    intro x p hp
    exact UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp hp
  by_cases hs : S.Subsingleton
  · exact hs.finite
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.1 hs
  apply (Set.toFinite ({p, q} : Set UpperHalfPlane)).subset
  intro x hx
  have hpqC : (p : ℂ) ≠ (q : ℂ) := fun h => hpq (UpperHalfPlane.ext h)
  obtain h | h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := ℂ) Complex.finrank_real_complex hcent hpqC
    (hdist a p hp.1) (hdist a q hq.1) (hdist a x hx.1)
    (hdist b p hp.2) (hdist b q hq.2) (hdist b x hx.2)
  · exact Or.inl (UpperHalfPlane.ext h)
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 (UpperHalfPlane.ext h))

/-- The actual central orbit-circle cut set is finite. Coincident centres are
excluded explicitly; local finiteness is consumed at the original compact ball. -/
theorem ft1gb_cut_points_finite {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (R : ℝ)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite) :
    ∃ V : Finset UpperHalfPlane,
      ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
        ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R := by
  classical
  let K : Set UpperHalfPlane := closedBall UpperHalfPlane.I R
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {γ | γ ∈ Γ ∧ γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧
      ((fun τ : UpperHalfPlane => γ • τ) '' K ∩ K).Nonempty}
  have hT : T.Finite := (hLf K (isCompact_closedBall _ _)).subset fun γ hγ =>
    ⟨hγ.1, hγ.2.2⟩
  let S : Set UpperHalfPlane := {p | dist p UpperHalfPlane.I = R ∧
    ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R}
  have hfinite : (⋃ γ ∈ T,
      {p : UpperHalfPlane | dist p UpperHalfPlane.I = R ∧ dist p (γ • UpperHalfPlane.I) = R}).Finite :=
    hT.biUnion fun γ hγ => ft1gb_two_spheres_finite hγ.2.1.symm R
  have hS : S.Finite := hfinite.subset (by
    intro p hp
    obtain ⟨γ, hγ, hne, hpγ⟩ := hp.2
    have hpK : p ∈ K := hp.1.le
    have hinv : γ⁻¹ • p ∈ K := by
      change dist (γ⁻¹ • p) UpperHalfPlane.I ≤ R
      have hd := (isometry_smul UpperHalfPlane γ).dist_eq (γ⁻¹ • p) UpperHalfPlane.I
      simp only [smul_inv_smul] at hd
      exact (hd.symm.trans hpγ).le
    have hγT : γ ∈ T :=
      ⟨hγ, hne, ⟨p, ⟨γ⁻¹ • p, hinv, smul_inv_smul γ p⟩, hpK⟩⟩
    exact Set.mem_iUnion.2 ⟨γ, Set.mem_iUnion.2 ⟨hγT, hp.1, hpγ⟩⟩)
  refine ⟨hS.toFinset, ?_⟩
  intro p
  exact Set.Finite.mem_toFinset hS

-- Source: F1BCircleGraph.lean
/-- Above the horizontal line through its centre, a closed Euclidean disc is exactly
the hypograph of its upper circular branch. The radicand is allowed to be negative:
in that case both sides are false, rather than relying on a square-root junk value. -/
theorem ft1gb_disc_upper_graph {c z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hy : c.im < z.im) :
    ‖z - c‖ ≤ r ↔ z.im ≤ c.im + Real.sqrt (r ^ 2 - (z.re - c.re) ^ 2) := by
  have hn : ‖z - c‖ ^ 2 = (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, pow_two]
  have hy0 : 0 < z.im - c.im := sub_pos.2 hy
  constructor
  · intro h
    have hsq : ‖z - c‖ ^ 2 ≤ r ^ 2 := (sq_le_sq₀ (norm_nonneg _) hr).2 h
    have hrad : 0 ≤ r ^ 2 - (z.re - c.re) ^ 2 := by nlinarith [sq_nonneg (z.im - c.im)]
    have hs := Real.sq_sqrt hrad
    have hp := Real.sqrt_nonneg (r ^ 2 - (z.re - c.re) ^ 2)
    nlinarith
  · intro h
    have hrad : 0 < r ^ 2 - (z.re - c.re) ^ 2 := by
      apply Real.sqrt_pos.1
      linarith
    have hs := Real.sq_sqrt hrad.le
    have hp := Real.sqrt_nonneg (r ^ 2 - (z.re - c.re) ^ 2)
    apply (sq_le_sq₀ (norm_nonneg _) hr).1
    nlinarith

/-- A continuous graph is explicitly flattened by the involutive vertical shear
(x,y) ↦ (x,f(x)-y). This is an actual homeomorphism, not an assumed boundary chart. -/
theorem ft1gb_graph_halfplane (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z : ℂ, e z = ⟨z.re, f z.re - z.im⟩) ∧
      ∀ z : ℂ, z.im ≤ f z.re ↔ 0 ≤ (e z).im := by
  let g : ℂ → ℂ := fun z => ⟨z.re, f z.re - z.im⟩
  have hg : Continuous g := by
    have he : g = fun z : ℂ => (z.re : ℂ) + ((f z.re - z.im : ℝ) : ℂ) * Complex.I := by
      funext z
      apply Complex.ext <;> simp [g]
    rw [he]
    exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      ((Complex.continuous_ofReal.comp ((hf.comp Complex.continuous_re).sub Complex.continuous_im)).mul
        continuous_const)
  have hgg : Function.Involutive g := by
    intro z
    apply Complex.ext
    · rfl
    · change f z.re - (f z.re - z.im) = z.im
      ring
  let e : ℂ ≃ₜ ℂ :=
    { toFun := g
      invFun := g
      left_inv := hgg
      right_inv := hgg
      continuous_toFun := hg
      continuous_invFun := hg }
  refine ⟨e, fun z => rfl, ?_⟩
  intro z
  change z.im ≤ f z.re ↔ 0 ≤ f z.re - z.im
  exact sub_nonneg.symm

/-- The union of two discs is locally a hypograph whenever the chosen upward direction
has positive dot product with both outward normals. This lemma handles the coordinate
part once the normal-direction choice and local isolation have been constructed. -/
theorem ft1gb_two_disc_graph {c₁ c₂ z : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hy₁ : c₁.im < z.im) (hy₂ : c₂.im < z.im) :
    (‖z - c₁‖ ≤ r₁ ∨ ‖z - c₂‖ ≤ r₂) ↔
      z.im ≤ max (c₁.im + Real.sqrt (r₁ ^ 2 - (z.re - c₁.re) ^ 2))
        (c₂.im + Real.sqrt (r₂ ^ 2 - (z.re - c₂.re) ^ 2)) := by
  rw [le_max_iff, ft1gb_disc_upper_graph hr₁ hy₁, ft1gb_disc_upper_graph hr₂ hy₂]


/-- Two non-opposite unit outward normals admit one common upward direction.
The multiplier need not have unit norm: its scale is absorbed into the disc radii. -/
theorem ft1gb_common_upward_direction {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hopp : u ≠ -v) :
    ∃ w : ℂ, w ≠ 0 ∧ 0 < (u * w).im ∧ 0 < (v * w).im := by
  have hsum : u + v ≠ 0 := by
    intro h
    exact hopp (eq_neg_of_add_eq_zero_left h)
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hu
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    simpa only [pow_two] using h
  have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hv
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    simpa only [pow_two] using h
  have hsum2 : 0 < (u.re + v.re) ^ 2 + (u.im + v.im) ^ 2 := by
    have h : 0 < ‖u + v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hsum)
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.add_re, Complex.add_im, pow_two] using h
  let w : ℂ := Complex.I * conj (u + v)
  have he1 : (u * w).im = u.re ^ 2 + u.im ^ 2 + u.re * v.re + u.im * v.im := by
    simp [w, Complex.mul_im, Complex.mul_re, pow_two] <;> ring
  have he2 : (v * w).im = v.re ^ 2 + v.im ^ 2 + u.re * v.re + u.im * v.im := by
    simp [w, Complex.mul_im, Complex.mul_re, pow_two] <;> ring
  have hp : 0 < (u * w).im := by rw [he1]; nlinarith
  have hq : 0 < (v * w).im := by rw [he2]; nlinarith
  refine ⟨w, ?_, hp, hq⟩
  intro hw
  simpa only [hw, mul_zero, Complex.zero_im, lt_self_iff_false] using hp

-- Source: F1BActiveNormals.lean
/-- External tangency of the corresponding Euclidean circles is exactly distance 2R
between the hyperbolic centres. This derives the geometric meaning of A2's exclusion. -/
theorem ft1gb_external_tangent_radius {a b : UpperHalfPlane} {R : ℝ} (hR : 0 ≤ R)
    (ht : ‖(a.center R : ℂ) - (b.center R : ℂ)‖ =
      (a.im + b.im) * Real.sinh R) :
    dist a b = 2 * R := by
  have hn : ‖(a.center R : ℂ) - (b.center R : ℂ)‖ ^ 2 =
      (a.re - b.re) ^ 2 + (a.im * Real.cosh R - b.im * Real.cosh R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      UpperHalfPlane.center_re, UpperHalfPlane.center_im, pow_two]
  have hs := congrArg (fun x : ℝ => x ^ 2) ht
  rw [hn] at hs
  have he : (a.re - b.re) ^ 2 + a.im ^ 2 + b.im ^ 2 =
      2 * a.im * b.im * (Real.cosh R ^ 2 + Real.sinh R ^ 2) := by
    linear_combination hs - (a.im ^ 2 + b.im ^ 2) * (Real.cosh_sq_sub_sinh_sq R)
  apply Real.cosh_injOn (show dist a b ∈ Ici 0 from dist_nonneg)
    (show 2 * R ∈ Ici 0 by change 0 ≤ 2 * R; positivity)
  rw [UpperHalfPlane.cosh_dist', he, Real.cosh_two_mul]
  have hden : 2 * a.im * b.im ≠ 0 := by positivity
  field_simp
  <;> ring

/-- At a regular intersection of two orbit circles there is an actual complex
multiplier making both outward normals point upward. No local half-plane chart is assumed. -/
theorem ft1gb_active_normals_upward {a b p : UpperHalfPlane} {R : ℝ} (hR : 0 < R)
    (hpa : dist p a = R) (hpb : dist p b = R) (hnt : dist a b ≠ 2 * R) :
    ∃ w : ℂ, w ≠ 0 ∧
      0 < (((p : ℂ) - (a.center R : ℂ)) * w).im ∧
      0 < (((p : ℂ) - (b.center R : ℂ)) * w).im := by
  let ra : ℝ := a.im * Real.sinh R
  let rb : ℝ := b.im * Real.sinh R
  have hra : 0 < ra := mul_pos a.im_pos (Real.sinh_pos_iff.2 hR)
  have hrb : 0 < rb := mul_pos b.im_pos (Real.sinh_pos_iff.2 hR)
  have hraC : (ra : ℂ) ≠ 0 := by exact_mod_cast hra.ne'
  have hrbC : (rb : ℂ) ≠ 0 := by exact_mod_cast hrb.ne'
  have hna : ‖(p : ℂ) - (a.center R : ℂ)‖ = ra := by
    simpa only [dist_eq_norm] using UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp hpa
  have hnb : ‖(p : ℂ) - (b.center R : ℂ)‖ = rb := by
    simpa only [dist_eq_norm] using UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp hpb
  let u : ℂ := ((p : ℂ) - (a.center R : ℂ)) / (ra : ℂ)
  let v : ℂ := ((p : ℂ) - (b.center R : ℂ)) / (rb : ℂ)
  have hu : ‖u‖ = 1 := by
    rw [show u = ((p : ℂ) - (a.center R : ℂ)) / (ra : ℂ) from rfl,
      norm_div, hna, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hra, div_self hra.ne']
  have hv : ‖v‖ = 1 := by
    rw [show v = ((p : ℂ) - (b.center R : ℂ)) / (rb : ℂ) from rfl,
      norm_div, hnb, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrb, div_self hrb.ne']
  have hea : (p : ℂ) - (a.center R : ℂ) = (ra : ℂ) * u := by
    dsimp [u]
    field_simp [hraC] <;> ring
  have heb : (p : ℂ) - (b.center R : ℂ) = (rb : ℂ) * v := by
    dsimp [v]
    field_simp [hrbC] <;> ring
  have hnonopp : u ≠ -v := by
    intro huv
    rw [huv] at hea
    have he : (a.center R : ℂ) - (b.center R : ℂ) = ((ra + rb : ℝ) : ℂ) * v := by
      push_cast
      linear_combination heb - hea
    have hnorm : ‖(a.center R : ℂ) - (b.center R : ℂ)‖ = ra + rb := by
      rw [he, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (add_pos hra hrb)]
    apply hnt
    apply ft1gb_external_tangent_radius hR.le
    rw [hnorm]
    dsimp [ra, rb]
    ring
  obtain ⟨w, hw, huw, hvw⟩ := ft1gb_common_upward_direction hu hv hnonopp
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hea, mul_assoc]
    simpa using mul_pos hra huw
  · rw [heb, mul_assoc]
    simpa using mul_pos hrb hvw

-- Source: F1BLocalBalls.lean
/-- Membership in the literal saturation is membership in an orbit-centred ball.
This records the change of centres without changing the radius. -/
theorem ft1gb_orbit_ball_mem (R : ℝ) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R) (x : UpperHalfPlane) :
    x ∈ U ↔ ∃ γ ∈ Γ, dist x (γ • UpperHalfPlane.I) ≤ R := by
  have hb (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      (fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R =
        closedBall (γ • UpperHalfPlane.I) R :=
    (IsometryEquiv.constSMul γ).image_closedBall UpperHalfPlane.I R
  rw [hU]
  simp only [hb, Set.mem_iUnion, Metric.mem_closedBall, exists_prop]

/-- A frontier point of a closed orbit-ball saturation lies on an active sphere
and lies in no open orbit ball. This direction needs no regular-radius assumptions. -/
theorem ft1gb_frontier_distances (R : ℝ) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R) (hUc : IsClosed U)
    {p : UpperHalfPlane} (hp : p ∈ frontier U) :
    (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I) := by
  have hpU : p ∈ U := hUc.closure_eq ▸ frontier_subset_closure hp
  have hpnot : p ∉ interior U := (mem_frontier_iff_notMem_interior hpU).1 hp
  have hlower : ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I) := by
    intro γ hγ
    by_contra h
    have hpin : p ∈ ball (γ • UpperHalfPlane.I) R := lt_of_not_ge h
    have hsub : ball (γ • UpperHalfPlane.I) R ⊆ U := by
      intro x hx
      exact (ft1gb_orbit_ball_mem R hU x).2 ⟨γ, hγ, hx.le⟩
    exact hpnot (interior_maximal hsub isOpen_ball hpin)
  obtain ⟨γ, hγ, hpγ⟩ := (ft1gb_orbit_ball_mem R hU p).1 hpU
  exact ⟨⟨γ, hγ, le_antisymm hpγ (hlower γ hγ)⟩, hlower⟩

/-- Local finiteness deletes every inactive ball in a neighbourhood of an exposed
point. The finite test set is the actual closed unit ball about that point. -/
theorem ft1gb_orbit_ball_localization (R : ℝ) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    {p : UpperHalfPlane} (hp : ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)) :
    ∃ N : Set UpperHalfPlane, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ N, x ∈ U ↔ ∃ γ ∈ Γ,
        dist p (γ • UpperHalfPlane.I) = R ∧ dist x (γ • UpperHalfPlane.I) ≤ R := by
  classical
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {γ | γ ∈ Γ ∧
      ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩
        closedBall p 1).Nonempty}
  have hT : T.Finite := hLf (closedBall p 1) (isCompact_closedBall p 1)
  let S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {γ ∈ T | dist p (γ • UpperHalfPlane.I) ≠ R}
  have hS : S.Finite := hT.subset fun γ hγ => hγ.1
  let N : Set UpperHalfPlane := ball p 1 ∩
    ⋂ γ ∈ S, (closedBall (γ • UpperHalfPlane.I) R)ᶜ
  have hNo : IsOpen N := isOpen_ball.inter
    (hS.isOpen_biInter fun γ hγ => isClosed_closedBall.isOpen_compl)
  have hpN : p ∈ N := by
    refine ⟨by simp, Set.mem_iInter.2 fun γ => Set.mem_iInter.2 fun hγ => ?_⟩
    change ¬ dist p (γ • UpperHalfPlane.I) ≤ R
    intro hle
    exact hγ.2 (le_antisymm hle (hp γ hγ.1.1))
  refine ⟨N, hNo, hpN, ?_⟩
  intro x hx
  constructor
  · intro hxU
    obtain ⟨γ, hγ, hxγ⟩ := (ft1gb_orbit_ball_mem R hU x).1 hxU
    have hximage : x ∈ (fun τ : UpperHalfPlane => γ • τ) ''
        closedBall UpperHalfPlane.I R := by
      change x ∈ (IsometryEquiv.constSMul γ : UpperHalfPlane ≃ᵢ UpperHalfPlane) ''
        closedBall UpperHalfPlane.I R
      rw [(IsometryEquiv.constSMul γ).image_closedBall UpperHalfPlane.I R]
      exact hxγ
    have hγT : γ ∈ T :=
      ⟨hγ, ⟨x, hximage, Metric.mem_closedBall.2 (Metric.mem_ball.1 hx.1).le⟩⟩
    refine ⟨γ, hγ, ?_, hxγ⟩
    by_contra hne
    have hγS : γ ∈ S := ⟨hγT, hne⟩
    have hxnot := Set.mem_iInter.1 (Set.mem_iInter.1 hx.2 γ) hγS
    exact hxnot hxγ
  · rintro ⟨γ, hγ, _, hxγ⟩
    exact (ft1gb_orbit_ball_mem R hU x).2 ⟨γ, hγ, hxγ⟩

/-- A nonempty level set with at most two centres is represented by two actual
orbit centres, repeated when the level set is a singleton. -/
theorem ft1gb_two_active_centres (R : ℝ) {p : UpperHalfPlane}
    (hp : ∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R)
    (hfin : {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧
      dist p z = R}.Finite)
    (hcard : {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧
      dist p z = R}.ncard ≤ 2) :
    ∃ a b : UpperHalfPlane,
      ((∃ γ ∈ Γ, a = γ • UpperHalfPlane.I) ∧ dist p a = R) ∧
      ((∃ γ ∈ Γ, b = γ • UpperHalfPlane.I) ∧ dist p b = R) ∧
      ∀ z : UpperHalfPlane,
        ((∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist p z = R) ↔ z = a ∨ z = b := by
  classical
  let S : Set UpperHalfPlane := {z | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist p z = R}
  obtain ⟨γ, hγ, hpγ⟩ := hp
  let a : UpperHalfPlane := γ • UpperHalfPlane.I
  have ha : a ∈ S := ⟨⟨γ, hγ, rfl⟩, hpγ⟩
  by_cases hs : S.Subsingleton
  · refine ⟨a, a, ha, ha, ?_⟩
    intro z
    constructor
    · intro hz
      exact Or.inl (hs hz ha)
    · rintro (rfl | rfl) <;> exact ha
  have hb : ∃ b ∈ S, b ≠ a := by
    by_contra h
    push_neg at h
    apply hs
    intro x hx y hy
    exact (h x hx).trans (h y hy).symm
  obtain ⟨b, hb, hba⟩ := hb
  refine ⟨a, b, ha, hb, ?_⟩
  intro z
  constructor
  · intro hz
    by_contra h
    push_neg at h
    have hlarge : 2 < S.ncard := (Set.two_lt_ncard_iff hfin).2
      ⟨a, b, z, ha, hb, hz, hba.symm, h.1.symm, h.2.symm⟩
    exact (not_lt_of_ge hcard) hlarge
  · rintro (rfl | rfl)
    · exact ha
    · exact hb

-- Source: F1BChartTopology.lean
/-- Restrict a centred half-plane chart to a small target ball and rescale that
ball to the unit ball. The rescaling is positive and preserves the core side. -/
theorem ft1gb_chart_unit_ball {X : Type*} [TopologicalSpace X]
    {U : Set X} {p : X} (e : OpenPartialHomeomorph X ℂ)
    (hp : p ∈ e.source) (hp0 : e p = 0)
    (hside : ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im) :
    ∃ f : OpenPartialHomeomorph X ℂ,
      p ∈ f.source ∧ f p = 0 ∧ f.target = ball 0 1 ∧
        ∀ x ∈ f.source, x ∈ U ↔ 0 ≤ (f x).im := by
  have h0 : (0 : ℂ) ∈ e.target := hp0 ▸ e.map_source hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target 0 h0
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let g : OpenPartialHomeomorph X ℂ :=
    (e.symm.restrOpen (ball 0 r) isOpen_ball).symm
  have hgsource : g.source = e.source ∩ e ⁻¹' ball 0 r := rfl
  have hgtarget : g.target = ball 0 r := by
    change e.target ∩ ball 0 r = ball 0 r
    exact inter_eq_right.2 hball
  let s : ℂ ≃ₜ ℂ := Homeomorph.mulRight₀ (r : ℂ)⁻¹ (inv_ne_zero hrC)
  have hs (z : ℂ) : s z = z * (r : ℂ)⁻¹ := rfl
  have hsinv (z : ℂ) : s.symm z = z * (r : ℂ) := by
    change z * ((r : ℂ)⁻¹)⁻¹ = z * (r : ℂ)
    rw [inv_inv]
  let f : OpenPartialHomeomorph X ℂ := g.transHomeomorph s
  have hfsource : f.source = g.source := rfl
  have hfp : p ∈ f.source := by
    rw [hfsource, hgsource]
    exact ⟨hp, by simpa only [Set.mem_preimage, hp0, Metric.mem_ball, dist_self] using hr⟩
  refine ⟨f, hfp, ?_, ?_, ?_⟩
  · change s (e p) = 0
    rw [hp0, hs, zero_mul]
  · change s.symm ⁻¹' g.target = ball 0 1
    rw [hgtarget]
    ext z
    simp only [Set.mem_preimage, hsinv, Metric.mem_ball, dist_zero_right, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [one_mul] using (mul_lt_mul_iff_left₀ hr : ‖z‖ * r < 1 * r ↔ ‖z‖ < 1)
  · intro x hx
    have hxe : x ∈ e.source := (hgsource ▸ (hfsource ▸ hx)).1
    have hfi : (f x).im = (e x).im / r := by
      change (e x * (r : ℂ)⁻¹).im = (e x).im / r
      rw [← div_eq_mul_inv]
      simp
    rw [hfi, le_div_iff₀ hr, zero_mul]
    exact hside x hxe

/-- A point sent to zero by a genuine half-plane chart is on the frontier.
Negative imaginary points in every sufficiently small target ball rule out interior. -/
theorem ft1gb_frontier_of_halfplane_chart {X : Type*} [TopologicalSpace X]
    {U : Set X} {p : X} (e : OpenPartialHomeomorph X ℂ)
    (hp : p ∈ e.source) (hp0 : e p = 0)
    (hside : ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im) :
    p ∈ frontier U := by
  have hpU : p ∈ U := (hside p hp).2 (by simp only [hp0, Complex.zero_im, le_refl])
  apply (mem_frontier_iff_notMem_interior hpU).2
  intro hpin
  have hopen : IsOpen (e '' (e.source ∩ interior U)) :=
    e.isOpen_image_source_inter isOpen_interior
  have hzero : (0 : ℂ) ∈ e '' (e.source ∩ interior U) := ⟨p, ⟨hp, hpin⟩, hp0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen 0 hzero
  let z : ℂ := ((r / 2 : ℝ) : ℂ) * (-Complex.I)
  have hzNorm : ‖z‖ = r / 2 := by
    simp only [z, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have hzball : z ∈ ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, hzNorm]
    linarith
  obtain ⟨x, hx, hxe⟩ := hball hzball
  have hxU : x ∈ U := interior_subset hx.2
  have hnonneg := (hside x hx.1).1 hxU
  rw [hxe] at hnonneg
  have hzim : z.im = -(r / 2) := by simp [z]
  rw [hzim] at hnonneg
  linarith

-- Source: F1BTwoBallChart.lean
/-- Construct the actual half-plane chart for one or two active hyperbolic balls.
The centres may coincide. Non-tangency excludes only opposite outward normals;
all coordinate maps and the continuous maximum graph are constructed here. -/
theorem ft1gb_two_ball_chart {a b p : UpperHalfPlane} {R : ℝ}
    (hR : 0 < R) (hpa : dist p a = R) (hpb : dist p b = R)
    (hnt : dist a b ≠ 2 * R) {U N : Set UpperHalfPlane}
    (hNo : IsOpen N) (hpN : p ∈ N)
    (hlocal : ∀ x ∈ N, x ∈ U ↔ dist x a ≤ R ∨ dist x b ≤ R) :
    ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
        ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im := by
  obtain ⟨w, hw, hn₁, hn₂⟩ := ft1gb_active_normals_upward hR hpa hpb hnt
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  let A : ℂ ≃ₜ ℂ :=
    (Homeomorph.addRight (-(p : ℂ))).trans (Homeomorph.mulRight₀ w hw)
  have hA (z : ℂ) : A z = (z - (p : ℂ)) * w := by
    change (z + -(p : ℂ)) * w = (z - (p : ℂ)) * w
    rw [sub_eq_add_neg]
  have hAp : A (p : ℂ) = 0 := by rw [hA, sub_self, zero_mul]
  let c₁ : ℂ := A (a.center R : ℂ)
  let c₂ : ℂ := A (b.center R : ℂ)
  let r₁ : ℝ := (a.im * Real.sinh R) * ‖w‖
  let r₂ : ℝ := (b.im * Real.sinh R) * ‖w‖
  have hr₁ : 0 < r₁ := mul_pos (mul_pos a.im_pos (Real.sinh_pos_iff.2 hR)) hwn
  have hr₂ : 0 < r₂ := mul_pos (mul_pos b.im_pos (Real.sinh_pos_iff.2 hR)) hwn
  have hc₁ : c₁.im < 0 := by
    have he : c₁ = -(((p : ℂ) - (a.center R : ℂ)) * w) := by
      rw [show c₁ = A (a.center R : ℂ) from rfl, hA]
      ring
    rw [he, Complex.neg_im]
    linarith
  have hc₂ : c₂.im < 0 := by
    have he : c₂ = -(((p : ℂ) - (b.center R : ℂ)) * w) := by
      rw [show c₂ = A (b.center R : ℂ) from rfl, hA]
      ring
    rw [he, Complex.neg_im]
    linarith
  have hnorm₁ : ‖c₁‖ = r₁ := by
    change ‖A (a.center R : ℂ)‖ = (a.im * Real.sinh R) * ‖w‖
    rw [hA, norm_mul, norm_sub_rev]
    congr 1
    exact (show ‖(p : ℂ) - (a.center R : ℂ)‖ = a.im * Real.sinh R by
      simpa only [dist_eq_norm] using UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hpa)
  have hnorm₂ : ‖c₂‖ = r₂ := by
    change ‖A (b.center R : ℂ)‖ = (b.im * Real.sinh R) * ‖w‖
    rw [hA, norm_mul, norm_sub_rev]
    congr 1
    exact (show ‖(p : ℂ) - (b.center R : ℂ)‖ = b.im * Real.sinh R by
      simpa only [dist_eq_norm] using UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.1 hpb)
  let f : ℝ → ℝ := fun t =>
    max (c₁.im + Real.sqrt (r₁ ^ 2 - (t - c₁.re) ^ 2))
      (c₂.im + Real.sqrt (r₂ ^ 2 - (t - c₂.re) ^ 2))
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hbranch (c : ℂ) (r : ℝ) (hc : c.im < 0) (hn : ‖c‖ = r) :
      c.im + Real.sqrt (r ^ 2 - (0 - c.re) ^ 2) = 0 := by
    have hsq : c.re ^ 2 + c.im ^ 2 = r ^ 2 := by
      have h := congrArg (fun t : ℝ => t ^ 2) hn
      rw [Complex.sq_norm, Complex.normSq_apply] at h
      simpa only [pow_two] using h
    rw [show r ^ 2 - (0 - c.re) ^ 2 = c.im ^ 2 by nlinarith,
      Real.sqrt_sq_eq_abs, abs_of_neg hc]
    ring
  have hf0 : f 0 = 0 := by
    change max (c₁.im + Real.sqrt (r₁ ^ 2 - (0 - c₁.re) ^ 2))
      (c₂.im + Real.sqrt (r₂ ^ 2 - (0 - c₂.re) ^ 2)) = 0
    rw [hbranch c₁ r₁ hc₁ hnorm₁, hbranch c₂ r₂ hc₂ hnorm₂, max_self]
  obtain ⟨S, hS, hSside⟩ := ft1gb_graph_halfplane f hf
  let H : ℂ ≃ₜ ℂ := A.trans S
  let F : UpperHalfPlane → ℂ := fun x => H (x : ℂ)
  have hF : Topology.IsOpenEmbedding F :=
    H.isOpenEmbedding.comp UpperHalfPlane.isOpenEmbedding_coe
  have hFp : F p = 0 := by
    change S (A (p : ℂ)) = 0
    rw [hAp, hS]
    apply Complex.ext <;> simp [hf0]
  have him : Continuous (fun x : UpperHalfPlane => (A (x : ℂ)).im) :=
    Complex.continuous_im.comp (A.continuous.comp UpperHalfPlane.continuous_coe)
  let M : Set UpperHalfPlane := N ∩
    {x | c₁.im < (A (x : ℂ)).im} ∩ {x | c₂.im < (A (x : ℂ)).im}
  have hMo : IsOpen M :=
    (hNo.inter (isOpen_lt continuous_const him)).inter (isOpen_lt continuous_const him)
  have hpM : p ∈ M := by
    refine ⟨⟨hpN, ?_⟩, ?_⟩
    · change c₁.im < (A (p : ℂ)).im
      simpa only [hAp, Complex.zero_im] using hc₁
    · change c₂.im < (A (p : ℂ)).im
      simpa only [hAp, Complex.zero_im] using hc₂
  have hdist (x y : UpperHalfPlane) : dist x y ≤ R ↔
      ‖A (x : ℂ) - A (y.center R : ℂ)‖ ≤ (y.im * Real.sinh R) * ‖w‖ := by
    rw [UpperHalfPlane.dist_le_iff_dist_coe_center_le, dist_eq_norm]
    have he : A (x : ℂ) - A (y.center R : ℂ) =
        ((x : ℂ) - (y.center R : ℂ)) * w := by
      rw [hA, hA]
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_iff_left₀ hwn).symm
  have hside : ∀ x ∈ M, x ∈ U ↔ 0 ≤ (F x).im := by
    intro x hx
    rw [hlocal x hx.1.1, hdist x a, hdist x b]
    have hgraph := ft1gb_two_disc_graph hr₁.le hr₂.le hx.1.2 hx.2
    exact hgraph.trans (hSside (A (x : ℂ)))
  let E₀ : OpenPartialHomeomorph UpperHalfPlane ℂ := hF.toOpenPartialHomeomorph F
  let E : OpenPartialHomeomorph UpperHalfPlane ℂ := E₀.restrOpen M hMo
  have hpE : p ∈ E.source := by
    change p ∈ (Set.univ : Set UpperHalfPlane) ∩ M
    exact ⟨Set.mem_univ p, hpM⟩
  have hEp : E p = 0 := hFp
  apply ft1gb_chart_unit_ball E hpE hEp
  intro x hx
  change x ∈ (Set.univ : Set UpperHalfPlane) ∩ M at hx
  exact hside x hx.2

-- Source: F1BExposedFrontier.lean
/-- Build the local chart at every exposed candidate, before using the chart to
prove that the candidate really is on the frontier. This avoids circularity in
the reverse frontier inclusion. -/
theorem ft1gb_candidate_chart {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    {p : UpperHalfPlane}
    (hp : ∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R)
    (hlower : ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)) :
    ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
        ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im := by
  obtain ⟨N, hNo, hpN, hlocal⟩ := ft1gb_orbit_ball_localization R hU hLf hlower
  obtain ⟨a, b, ha, hb, hcent⟩ :=
    ft1gb_two_active_centres R hp (hlevel p).1 (hlevel p).2
  have hnt : dist a b ≠ 2 * R := by
    by_cases hab : a = b
    · rw [hab, dist_self]
      linarith
    obtain ⟨γ, hγ, haγ⟩ := ha.1
    obtain ⟨δ, hδ, hbδ⟩ := hb.1
    rw [haγ, hbδ] at hab ⊢
    exact hpair γ hγ δ hδ hab
  apply ft1gb_two_ball_chart hR ha.2 hb.2 hnt hNo hpN
  intro x hxN
  constructor
  · intro hxU
    obtain ⟨γ, hγ, hpγ, hxγ⟩ := (hlocal x hxN).1 hxU
    have hwhich := (hcent (γ • UpperHalfPlane.I)).1 ⟨⟨γ, hγ, rfl⟩, hpγ⟩
    rcases hwhich with he | he
    · exact Or.inl (he ▸ hxγ)
    · exact Or.inr (he ▸ hxγ)
  · intro hx
    apply (hlocal x hxN).2
    rcases hx with hxa | hxb
    · obtain ⟨γ, hγ, haγ⟩ := ha.1
      refine ⟨γ, hγ, ?_, ?_⟩
      · simpa only [← haγ] using ha.2
      · simpa only [← haγ] using hxa
    · obtain ⟨γ, hγ, hbγ⟩ := hb.1
      refine ⟨γ, hγ, ?_, ?_⟩
      · simpa only [← hbγ] using hb.2
      · simpa only [← hbγ] using hxb

/-- B1. The literal exposed boundary of the regular orbit-ball union has a local
half-plane chart at every frontier point. The central circle's cut set is genuinely finite. -/
theorem ft1gb_exposed_frontier (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (R : ℝ) (hR : 0 < R) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hUc : IsClosed U) (hUconn : IsConnected U)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
      dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2) :
    ∃ V : Finset UpperHalfPlane,
      (∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
        ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R) ∧
      frontier U = {p : UpperHalfPlane |
        (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
        ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)} ∧
      (∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im) := by
  -- These global hypotheses are retained verbatim from the approved interface.
  -- The local conclusion already follows from local finiteness and regularity.
  have _hΓ := hΓ
  have _hfree := hfree
  have _hUconn := hUconn
  have _hUi := hUi
  obtain ⟨V, hV⟩ := ft1gb_cut_points_finite R hLf
  have hcharts (p : UpperHalfPlane)
      (hp : (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
        ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)) :=
    ft1gb_candidate_chart hR hU hLf hpair hlevel hp.1 hp.2
  refine ⟨V, hV, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      exact ft1gb_frontier_distances R hU hUc hp
    · intro hp
      obtain ⟨e, hep, he0, _, heside⟩ := hcharts p hp
      exact ft1gb_frontier_of_halfplane_chart e hep he0 heside
  · intro p hp
    exact hcharts p (ft1gb_frontier_distances R hU hUc hp)

end LiZhongQC
