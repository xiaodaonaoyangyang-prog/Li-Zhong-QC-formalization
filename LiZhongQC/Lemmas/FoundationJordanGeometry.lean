import LiZhongQC.Lemmas.FoundationParabolicHelpers
import LiZhongQC.Lemmas.FiniteTypeUniquenessProof

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Exponentiating an injective lift with unit translation increment gives a Jordan
curve. The half-open period interval is essential: its two endpoints project together. -/
theorem ft1gc_periodic_exp_jordan (f : ℝ → ℂ) (hf : Continuous f)
    (hinj : Function.Injective f) (hshift : ∀ t : ℝ, f (t + 1) = f t + 1) :
    IsJordanCurve (toExt ((fun t : ℝ => Complex.exp (2 * Real.pi * I * f t)) '' Icc 0 1)) := by
  let F : AddConstMap ℝ ℂ 1 1 := { toFun := f, map_add_const' := hshift }
  have htranslate : ∀ t : ℝ, ∀ n : ℤ, f (t + n) = f t + n := by
    intro t n
    exact AddConstMapClass.map_add_int F t n
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply isJordanCurve_of_loop
  · exact (Complex.continuous_exp.comp (continuous_const.mul hf)).continuousOn
  · intro s hs t ht he
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
    have hft : f s = f t + n := by
      apply mul_left_cancel₀ hfactor
      linear_combination hn
    have hst : s = t + (n : ℝ) := hinj (hft.trans (htranslate t n).symm)
    have hnlow : (-1 : ℝ) < (n : ℝ) := by linarith [hs.1, hs.2, ht.1, ht.2]
    have hnhigh : (n : ℝ) < 1 := by linarith [hs.1, hs.2, ht.1, ht.2]
    have hnlow' : (-1 : ℤ) < n := by exact_mod_cast hnlow
    have hnhigh' : n < (1 : ℤ) := by exact_mod_cast hnhigh
    have hnzero : n = 0 := by omega
    simpa only [hnzero, Int.cast_zero, add_zero] using hst
  · have h01 : f 1 = f 0 + 1 := by simpa only [zero_add] using hshift 0
    rw [h01, mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The periodic upper-half-plane boundary gives a finite planar Jordan curve under
the standard exponential covering. This is the actual curve supplied to the installed
Jordan theorem, not an assumed conformal-circle crosscut. -/
theorem ft1gc_parabolic_exp_jordan (ρ : ℝ → UpperHalfPlane)
    (hρ : Topology.IsEmbedding ρ)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = (1 : ℝ) +ᵥ ρ t) :
    IsJordanCurve (toExt ((fun t : ℝ => Complex.exp (2 * Real.pi * I * (ρ t : ℂ))) '' Icc 0 1)) := by
  refine ft1gc_periodic_exp_jordan (fun t => (ρ t : ℂ))
    (UpperHalfPlane.continuous_coe.comp hρ.continuous) ?_ ?_
  · intro s t h
    exact hρ.injective (UpperHalfPlane.ext h)
  · intro t
    rw [hperiod, UpperHalfPlane.coe_vadd]
    push_cast
    ring

/-- A continuous map from a connected space into one fibre of exp is constant.
The proof uses the existing injectivity of exp in the principal horizontal strip. -/
theorem ft1gc_exp_fiber_const {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (g : X → ℂ) (hg : Continuous g) (hexp : ∀ x, Complex.exp (g x) = 1)
    (x y : X) : g x = g y := by
  have hlocal : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).2
    intro x
    have hlim : Tendsto (fun z => g z - g x) (𝓝 x) (𝓝 (0 : ℂ)) := by
      have hca : ContinuousAt (fun z => g z - g x) x := hg.continuousAt.sub continuousAt_const
      simpa only [sub_self] using hca.tendsto
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : ℂ) Real.pi_pos)] with z hz
    have hnorm : ‖g z - g x‖ < Real.pi := by
      simpa only [mem_ball, dist_zero_right] using hz
    have him : |(g z - g x).im| < Real.pi :=
      (Complex.abs_im_le_norm _).trans_lt hnorm
    have he : Complex.exp (g z - g x) = Complex.exp (0 : ℂ) := by
      rw [Complex.exp_sub, hexp, hexp, one_div_one, Complex.exp_zero]
    have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.1 him).1
      (abs_lt.1 him).2.le (by change -Real.pi < (0 : ℝ); linarith [Real.pi_pos])
      (by simpa using Real.pi_pos.le) he
    exact sub_eq_zero.1 heq
  exact hlocal.apply_eq_of_preconnectedSpace x y

/-- A unit-increment lift cannot exponentiate to a loop admitting a closed continuous
logarithm. This is the concrete essentiality fact used to put zero on the inner side of
the periodic Jordan curve; it does not assume a winding-number API. -/
theorem ft1gc_periodic_loop_no_closed_log (f L : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1)) (hL : ContinuousOn L (Icc 0 1))
    (hshift : f 1 = f 0 + 1)
    (hexp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp (L t) = Complex.exp (2 * Real.pi * I * f t))
    (hclose : L 0 = L 1) : False := by
  let c : ℂ := 2 * Real.pi * I
  let g : unitInterval → ℂ := fun t => L t - c * f t
  have hf' : Continuous (fun t : unitInterval => f t) :=
    hf.comp_continuous continuous_subtype_val (fun t => t.property)
  have hL' : Continuous (fun t : unitInterval => L t) :=
    hL.comp_continuous continuous_subtype_val (fun t => t.property)
  have hg : Continuous g := hL'.sub (continuous_const.mul hf')
  have hge : ∀ t : unitInterval, Complex.exp (g t) = 1 := by
    intro t
    change Complex.exp (L t - c * f t) = 1
    rw [Complex.exp_sub, hexp t t.property]
    exact div_self (Complex.exp_ne_zero _)
  have heq := ft1gc_exp_fiber_const g hg hge (0 : unitInterval) 1
  change L 0 - c * f 0 = L 1 - c * f 1 at heq
  rw [hclose, hshift] at heq
  have hc : c = 0 := by linear_combination heq
  have hcne : c ≠ 0 := by dsimp only [c]; simp [Real.pi_ne_zero]
  exact hcne hc

/-- A bounded closed Jordan filling avoiding zero admits a continuous logarithm.
The closed-disc homeomorphism is reused from the installed finite-type uniqueness
module, rather than rebuilding a Caratheodory extension. -/
theorem ft1gc_log_on_closed_jordan {A : Set ℂ}
    (hA : IsJordanDomain A) (hb : Bornology.IsBounded A) (hzero : (0 : ℂ) ∉ closure A) :
    ∃ L : closure A → ℂ, Continuous L ∧ ∀ z, Complex.exp (L z) = z.val := by
  obtain ⟨eD, -⟩ := s31sh_jordan_closed_disc hA
  let eA : closure A ≃ₜ closure (toExt A) :=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (closure A)).trans
      (Homeomorph.setCongr (closure_toExt_of_isBounded' hb).symm)
  let e : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure A := eD.trans eA.symm
  have hc : Continuous (fun z : Metric.closedBall (0 : ℂ) 1 => (e z).val) :=
    continuous_subtype_val.comp e.continuous
  have hne : ∀ z : Metric.closedBall (0 : ℂ) 1, (e z).val ≠ 0 := by
    intro z hz
    exact hzero (hz ▸ (e z).property)
  obtain ⟨L, hLc, hLe⟩ := ft1gc_continuous_log_on_closedDisc (fun z => (e z).val) hc hne
  refine ⟨fun z => L (e.symm z), hLc.comp e.symm.continuous, ?_⟩
  intro z
  rw [hLe, e.apply_symm_apply]

/-- A Jordan loop with a unit-increment exponential lift surrounds zero. The
bounded/unbounded labelling is essential; it fixes which complementary side is inner. -/
theorem ft1gc_periodic_jordan_zero_inside (f : ℝ → ℂ) (hf : Continuous f)
    (hinj : Function.Injective f) (hshift : ∀ t : ℝ, f (t + 1) = f t + 1)
    (A B : Set ℂ)
    (hAo : IsOpen A) (hBo : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAB : Disjoint A B)
    (hAC : Disjoint A ((fun t : ℝ => Complex.exp (2 * Real.pi * I * f t)) '' Icc 0 1))
    (hBC : Disjoint B ((fun t : ℝ => Complex.exp (2 * Real.pi * I * f t)) '' Icc 0 1))
    (hcover : A ∪ B ∪ ((fun t : ℝ => Complex.exp (2 * Real.pi * I * f t)) '' Icc 0 1) = univ)
    (hAb : Bornology.IsBounded A) (hBub : ¬ Bornology.IsBounded B) :
    (0 : ℂ) ∈ A := by
  classical
  -- The unbounded label is retained by the approved interface. Boundedness of A
  -- together with the stated Jordan partition already determines its inner label.
  have _hBub := hBub
  let q : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * I * f t)
  let C : Set ℂ := q '' Icc 0 1
  have hCJ : IsJordanCurve (toExt C) := ft1gc_periodic_exp_jordan f hf hinj hshift
  have hfront : frontier A = C :=
    (frontier_pieces_eq_of_jordan_curve_theorem_complex hCJ
      hAo hBo hAc hBc hAB hAC hBC hcover).1
  have hAJ : IsJordanDomain A := by
    refine ⟨hAo, hAc, ?_⟩
    rw [frontier_toExt_of_isBounded' hAb hAo, hfront]
    exact hCJ
  have hzeroC : (0 : ℂ) ∉ C := by
    rintro ⟨t, ht, he⟩
    exact Complex.exp_ne_zero _ he
  by_contra hzeroA
  have hzeroCl : (0 : ℂ) ∉ closure A := by
    rw [closure_eq_self_union_frontier, hfront]
    exact fun h => h.elim hzeroA hzeroC
  obtain ⟨L, hLc, hLe⟩ := ft1gc_log_on_closed_jordan hAJ hAb hzeroCl
  let L₀ : ℂ → ℂ := fun z => if hz : z ∈ closure A then L ⟨z, hz⟩ else 0
  have hL₀ : ContinuousOn L₀ (closure A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (fun z : closure A => L₀ z.val) = L := by
      funext z
      change (if hz : z.val ∈ closure A then L ⟨z.val, hz⟩ else 0) = L z
      rw [dif_pos z.property]
    change Continuous (fun z : closure A => L₀ z.val)
    rw [heq]
    exact hLc
  have hq : Continuous q := Complex.continuous_exp.comp (continuous_const.mul hf)
  have hqmem : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ closure A := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact ⟨t, ht, rfl⟩
  have hqclose : q 0 = q 1 := by
    have h01 : f 1 = f 0 + 1 := by simpa only [zero_add] using hshift 0
    change Complex.exp (2 * Real.pi * I * f 0) = Complex.exp (2 * Real.pi * I * f 1)
    rw [h01, mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  apply ft1gc_periodic_loop_no_closed_log f (L₀ ∘ q) hf.continuousOn
    (hL₀.comp hq.continuousOn hqmem)
    (by simpa only [zero_add] using hshift 0)
  · intro t ht
    change Complex.exp (L₀ (q t)) = q t
    change Complex.exp (if hz : q t ∈ closure A then L ⟨q t, hz⟩ else 0) = q t
    rw [dif_pos (hqmem t ht)]
    exact hLe ⟨q t, hqmem t ht⟩
  · exact congrArg L₀ hqclose

/-- A path-connected zero-free subset of the unit disc containing a full circle has
a connected lift in H. The norm bound is used to put every logarithmic lift in the
correct half-plane before transport; no intersection-connectivity inference is used. -/
theorem ft1gc_upper_exp_preimage_connected (U : Set ℂ) (hUpc : IsPathConnected U)
    (hzero : (0 : ℂ) ∉ U) (hdisc : U ⊆ {z : ℂ | ‖z‖ < 1})
    (a : ℝ) (ha : 0 < a)
    (hcircle : ∀ t : ℝ, (a : ℂ) * Complex.exp ((t * (2 * Real.pi) : ℝ) * I) ∈ U) :
    IsConnected {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ U} := by
  let c : ℂ := 2 * Real.pi * I
  have hc : c ≠ 0 := by dsimp only [c]; simp [Real.pi_ne_zero]
  have hconn : IsConnected (Complex.exp ⁻¹' U) :=
    isConnected_exp_preimage hUpc hzero ha hcircle
  have him : ∀ z : ℂ, (z / c).im = -z.re / (2 * Real.pi) := by
    intro z
    have hcR : c = (((2 * Real.pi : ℝ) : ℂ) * I) := by
      dsimp only [c]
      push_cast
      ring
    rw [hcR, div_mul_eq_div_div, Complex.div_I, Complex.neg_im, Complex.mul_I_im,
      Complex.div_ofReal_re, neg_div]
  have hpos : ∀ z ∈ Complex.exp ⁻¹' U, 0 < (z / c).im := by
    intro z hz
    have hn : ‖Complex.exp z‖ < 1 := hdisc hz
    rw [Complex.norm_exp, Real.exp_lt_one_iff] at hn
    rw [him]
    exact div_pos (neg_pos.2 hn) (mul_pos (by norm_num) Real.pi_pos)
  let V : Set ℂ := (fun z : ℂ => z / c) '' (Complex.exp ⁻¹' U)
  have hVc : IsConnected V := hconn.image _ (continuous_id.div_const c).continuousOn
  have hVr : V ⊆ range ((↑) : UpperHalfPlane → ℂ) := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨⟨w / c, hpos w hw⟩, rfl⟩
  have hH := hVc.preimage_of_isOpenMap UpperHalfPlane.coe_injective
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap hVr
  have heq : ((↑) : UpperHalfPlane → ℂ) ⁻¹' V =
      {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈ U} := by
    ext τ
    constructor
    · rintro ⟨z, hz, he⟩
      change Complex.exp (c * (τ : ℂ)) ∈ U
      rw [← he, mul_div_cancel₀ _ hc]
      exact hz
    · intro hτ
      refine ⟨c * (τ : ℂ), hτ, ?_⟩
      exact mul_div_cancel_left₀ (τ : ℂ) hc
  rw [heq] at hH
  exact hH

/-- Polar coordinates give path connectivity of the punctured unit disc without
choosing a globally continuous argument. -/
theorem ft1gc_punctured_disc_pathConnected :
    IsPathConnected (unitDisc \ ({0} : Set ℂ)) := by
  let P : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)
  have hPc : Continuous P := by fun_prop
  have hdomain : IsPathConnected (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
    ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩).prod isPathConnected_univ
  have heq : P '' (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) = unitDisc \ ({0} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hn : ‖P p‖ = p.1 := by
        change ‖(p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)‖ = p.1
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.1.1.le,
          norm_exp_ofReal_mul_I, mul_one]
      refine ⟨mem_ball_zero_iff.2 (hn.trans_lt hp.1.2), ?_⟩
      intro hz
      have he : P p = 0 := mem_singleton_iff.1 hz
      have hne : P p ≠ 0 := mul_ne_zero
        (Complex.ofReal_ne_zero.2 (ne_of_gt hp.1.1)) (Complex.exp_ne_zero _)
      exact hne he
    · intro hz
      have hz0 : z ≠ 0 := fun h => hz.2 (mem_singleton_iff.2 h)
      refine ⟨(‖z‖, Complex.arg z), ⟨⟨norm_pos_iff.2 hz0, mem_ball_zero_iff.1 hz.1⟩,
        mem_univ _⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← heq]
  exact hdomain.image hPc

/-- A Jordan domain remains path connected after removing an interior zero.
Normalize an installed disc uniformizer at zero and transport punctured-disc paths
by its conformal inverse. No general point-removal theorem is assumed. -/
theorem ft1gc_punctured_jordan_pathConnected {A : Set ℂ}
    (hA : IsJordanDomain A) (hzero : (0 : ℂ) ∈ A) :
    IsPathConnected (A \ ({0} : Set ℂ)) := by
  classical
  obtain ⟨f, hf, -⟩ := s13x_th_exists_disc_uniformizer hA
  have ha : ‖f 0‖ < 1 := mem_ball_zero_iff.1 (hf.mapsTo hzero)
  let g : ℂ → ℂ := blaschke (f 0) ∘ f
  have hg : IsConformalOnto g A unitDisc := (isConformalOnto_blaschke ha).comp hf
  have hg0 : g 0 = 0 := blaschke_self (f 0)
  let k : ℂ → ℂ := Function.invFunOn g A
  have hk : IsConformalOnto k unitDisc A := hg.symm hA.1
  have hk0 : k 0 = 0 := by
    have hinv := hg.2.1.leftInvOn_invFunOn hzero
    rw [hg0] at hinv
    exact hinv
  have hzeroD : (0 : ℂ) ∈ unitDisc := mem_ball_self zero_lt_one
  have heq : k '' (unitDisc \ ({0} : Set ℂ)) = A \ ({0} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hk.mapsTo hw.1, ?_⟩
      intro hzeroK
      have hkw : k w = k 0 := (mem_singleton_iff.1 hzeroK).trans hk0.symm
      exact hw.2 (mem_singleton_iff.2 (hk.2.1 hw.1 hzeroD hkw))
    · intro hz
      have hz0 : z ≠ 0 := fun h => hz.2 (mem_singleton_iff.2 h)
      refine ⟨g z, ⟨hg.mapsTo hz.1, ?_⟩, hg.2.1.leftInvOn_invFunOn hz.1⟩
      intro hgz
      have he : g z = g 0 := (mem_singleton_iff.1 hgz).trans hg0.symm
      exact hz0 (hg.2.1 hz.1 hzero he)
  rw [← heq]
  exact ft1gc_punctured_disc_pathConnected.image' (hk.1.continuousOn.mono sdiff_subset)

end LiZhongQC
