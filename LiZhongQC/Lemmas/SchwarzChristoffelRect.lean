import LiZhongQC.Lemmas.RectangleRigidity
import LiZhongQC.RiemannMapping
import LiZhongQC.Lemmas.LocalRoots

/-!
# The Schwarz–Christoffel map of the upper half-plane onto a rectangle

The existence half of **Theorem 1.1**: for `0 < k < 1` the half-plane quadrilateral
`ℍ(-1/k, -1, 1, 1/k)` is conformally equivalent to the rectangle `R(0, a, a+bi, bi)` with
`a = ∫₁^{1/k} dx/√((x²-1)(1-k²x²))` and `b = ∫₋₁¹ dx/√((1-x²)(1-k²x²))`, by the map
`F(z) = ∫ dζ/√((1-ζ²)(1-k²ζ²))` normalised by `F(-1/k) = 0`.  Together with
`thm1_1_halfPlane_normalForm` this gives `thm1_1_exists_rectangle` in `Ch01/S01_Quadrilateral.lean`,
which is to import this file (so this file must not import anything downstream of S01).

## Route (following the write-up `proof in LZ.txt`, §§4–6, except for one step)

* the integrand `scIntegrand k ζ = (-i/k) ∏ⱼ (ζ - pⱼ)^{-1/2}` (principal powers) is holomorphic and
  zero-free on `ℍ`, continues across each open real interval (rotated branch cuts), has the boundary
  values of LZ (4.4) and integrable singularities `|ζ - pⱼ|^{-1/2}` at the prevertices;
* `scMap` is its primitive (segment integrals from `i`), continuous up to the real axis and at `∞`
  (the latter via the inversion `ω ↦ -1/(kω)`, which permutes the prevertices);
* the boundary map is a bijection of `ℝ ∪ {∞}` onto `∂R`, running `0 → a → a+bi → bi → 0`;
* `F(ℍ) ⊆ R` by the Phragmén–Lindelöf / maximum principle and the open mapping theorem;
* **replacing LZ 6.2 (Darboux–Picard, i.e. the argument principle, absent from Mathlib):** `F : ℍ → R`
  is a proper local homeomorphism, hence a covering map
  (`IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph`), hence a homeomorphism because `R` is
  simply connected and `ℍ` connected (`IsCoveringMapOn.existsUnique_continuousMap_lifts`);
* the extension to `ℂ̄` is a homeomorphism of the closures sending the prevertices to the vertices.

Placement caveat: `Lemmas/Quadrilateral.lean` and `Ch01/S05_ExtremalProblems.lean` are downstream of
S01, so their `ℂ̄` facts (`closure_toExt_of_isBounded`, `frontier_toExt_of_isBounded`,
`frontier_rectangle`, the frontier of `toExt upperHalf`) must be re-proved here as helpers.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ### Stage 0: data -/

/-- The prevertices `-1/k, -1, 1, 1/k`. -/
def scPrevertex (k : ℝ) : Fin 4 → ℝ := ![-1 / k, -1, 1, 1 / k]

/-- `g_k(ζ) = (-i/k) ∏ⱼ (ζ - pⱼ)^{-1/2}` with principal powers; on `ℍ` this is a branch of
`1/√((1-ζ²)(1-k²ζ²))` (LZ (4.2)). -/
def scIntegrand (k : ℝ) (ζ : ℂ) : ℂ :=
  (-I / (k : ℂ)) * ∏ j : Fin 4, (ζ - (scPrevertex k j : ℂ)) ^ (-(1 / 2 : ℂ))

/-- `a = ∫₁^{1/k} dx/√((x²-1)(1-k²x²))`, the form used by `thm1_1_elliptic_modulus`. -/
def scSideA (k : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..(1 / k), 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))

/-- `b = ∫₋₁¹ dx/√((1-x²)(1-k²x²))`. -/
def scSideB (k : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, 1 / Real.sqrt ((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))

/-- The Schwarz–Christoffel map, as segment integrals from `i`, normalised by `F(-1/k) = 0`.
Defined on all of `ℂ`; meaningful on the closed upper half-plane. -/
def scMap (k : ℝ) (z : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, scIntegrand k (I + t * (z - I)) * (z - I)) -
    ∫ t in (0 : ℝ)..1, scIntegrand k (I + t * ((scPrevertex k 0 : ℂ) - I)) *
      ((scPrevertex k 0 : ℂ) - I)

/-- The value at `∞` (a point of the side `[bi, 0]`). -/
def scMapInfty (k : ℝ) : ℂ := limUnder atTop fun x : ℝ => scMap k x

/-- The extension to `ℂ̄`. -/
def scMapExt (k : ℝ) (p : ExtPlane) : ExtPlane :=
  OnePoint.elim p ((scMapInfty k : ℂ) : ExtPlane) fun z => ((scMap k z : ℂ) : ExtPlane)

/-- `ℂ` minus the four downward rays `pⱼ - i[0, ∞)`. -/
def scSlitDomain (k : ℝ) : Set ℂ :=
  {ζ | ∀ j : Fin 4, ∀ s : ℝ, 0 ≤ s → ζ ≠ (scPrevertex k j : ℂ) - s * I}

/-! ### `ℂ̄` facts

Re-proved here (with `scExt_` names) because the existing copies — `closure_toExt_of_isBounded`,
`frontier_toExt_of_isBounded`, `frontier_rectangle` in `Lemmas/Quadrilateral.lean`,
`closure_toExt_eq_toExt_closure_of_isBounded` in S01, the `ℍ` facts in S05 — are downstream of
S01, which is to import this file. -/

theorem scExt_coe_mem_toExt_iff {S : Set ℂ} {z : ℂ} : (z : ExtPlane) ∈ toExt S ↔ z ∈ S :=
  OnePoint.coe_injective.mem_set_image

theorem scExt_infty_notMem_toExt (S : Set ℂ) : extInf ∉ toExt S := OnePoint.infty_notMem_image_coe

theorem scExt_preimage_coe_toExt (S : Set ℂ) : ((↑) : ℂ → ExtPlane) ⁻¹' toExt S = S :=
  Set.preimage_image_eq S OnePoint.coe_injective

theorem scExt_isOpen_toExt {S : Set ℂ} (hS : IsOpen S) : IsOpen (toExt S) :=
  OnePoint.isOpen_image_coe.2 hS

/-- `ℂ̄ ∖ (S ∪ {∞}) = ℂ ∖ S`. -/
theorem scExt_compl_toExt_union_infty (S : Set ℂ) : (toExt S ∪ {extInf})ᶜ = toExt Sᶜ := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [scExt_infty_notMem_toExt]
  | coe z => simp [scExt_coe_mem_toExt_iff]

theorem scExt_isClosed_toExt_union_infty {S : Set ℂ} (hS : IsClosed S) :
    IsClosed (toExt S ∪ {extInf}) := by
  rw [← isOpen_compl_iff, scExt_compl_toExt_union_infty]
  exact scExt_isOpen_toExt hS.isOpen_compl

/-- The closure in `ℂ̄` of a bounded set of `ℂ` is the image of its closure in `ℂ` (it does not
contain `∞`). -/
theorem scExt_closure_toExt_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A) :
    closure (toExt A) = toExt (closure A) := by
  unfold toExt
  refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
    (image_closure_subset_closure_image OnePoint.continuous_coe)
  exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hA.isCompact_closure⟩

theorem scExt_frontier_toExt_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAo : IsOpen A) : frontier (toExt A) = toExt (frontier A) := by
  have hAo' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hAo
  rw [hAo'.frontier_eq, scExt_closure_toExt_of_isBounded hA, hAo.frontier_eq]
  exact (image_diff OnePoint.coe_injective _ _).symm

theorem scExt_isOpen_upperHalf : IsOpen upperHalf := isOpen_lt continuous_const continuous_im

theorem scExt_convex_upperHalf : Convex ℝ upperHalf := convex_halfSpace_im_gt 0

theorem scExt_closure_upperHalf : closure upperHalf = {z : ℂ | 0 ≤ z.im} := by
  have h : upperHalf = (univ : Set ℝ) ×ℂ Ioi 0 := by
    ext z
    simp [upperHalf, mem_reProdIm]
  rw [h, closure_reProdIm, closure_univ, closure_Ioi]
  ext z
  simp [mem_reProdIm]

/-- The closure of `ℍ` in `ℂ̄`: the closed half-plane together with `∞`. -/
theorem scExt_closure_toExt_upperHalf :
    closure (toExt upperHalf) = toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf} := by
  apply subset_antisymm
  · refine closure_minimal (subset_union_left.trans' (image_mono fun z hz => le_of_lt (show 0 < z.im from hz))) ?_
    exact scExt_isClosed_toExt_union_infty (isClosed_le continuous_const continuous_im)
  · refine union_subset ?_ ?_
    · rw [← scExt_closure_upperHalf]
      exact image_closure_subset_closure_image OnePoint.continuous_coe
    · rw [singleton_subset_iff, mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
      rintro s ⟨-, hs⟩
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
      set z : ℂ := ((|M| + 1 : ℝ) : ℂ) * I with hz
      have hnorm : ‖z‖ = |M| + 1 := by
        rw [hz, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg]
        positivity
      have hzH : z ∈ upperHalf := by
        show 0 < z.im
        rw [hz]
        simp
        positivity
      have hzs : z ∉ s := fun hmem => by
        have := hM z hmem
        rw [hnorm] at this
        linarith [le_abs_self M]
      exact ⟨(z : ExtPlane), ⟨z, hzH, rfl⟩, Or.inl ⟨z, hzs, rfl⟩⟩

/-- The boundary of `ℍ` in `ℂ̄`: the real axis together with `∞`. -/
theorem scExt_frontier_toExt_upperHalf :
    frontier (toExt upperHalf) = toExt {z : ℂ | z.im = 0} ∪ {extInf} := by
  rw [(scExt_isOpen_toExt scExt_isOpen_upperHalf).frontier_eq, scExt_closure_toExt_upperHalf]
  ext p
  induction p using OnePoint.rec with
  | infty => simp [scExt_infty_notMem_toExt]
  | coe z =>
    simp only [mem_diff, mem_union, scExt_coe_mem_toExt_iff, mem_setOf_eq, mem_singleton_iff,
      OnePoint.coe_ne_infty, or_false, upperHalf, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
    · intro h
      exact ⟨h.ge, h.le⟩

theorem scExt_coe_mem_frontier_toExt_upperHalf_iff {z : ℂ} :
    (z : ExtPlane) ∈ frontier (toExt upperHalf) ↔ z.im = 0 := by
  rw [scExt_frontier_toExt_upperHalf]
  simp [scExt_coe_mem_toExt_iff]

theorem scExt_ofReal_mem_frontier_toExt_upperHalf (t : ℝ) :
    ((t : ℂ) : ExtPlane) ∈ frontier (toExt upperHalf) :=
  scExt_coe_mem_frontier_toExt_upperHalf_iff.2 (Complex.ofReal_im t)

theorem scExt_infty_mem_frontier_toExt_upperHalf : extInf ∈ frontier (toExt upperHalf) := by
  rw [scExt_frontier_toExt_upperHalf]
  exact Or.inr rfl

theorem scExt_rectangle_eq (a b : ℝ) : rectangle a b = Ioo 0 a ×ℂ Ioo 0 b := by
  ext z
  simp only [rectangle, mem_setOf_eq, mem_reProdIm, mem_Ioo]
  tauto

theorem scExt_isOpen_rectangle (a b : ℝ) : IsOpen (rectangle a b) := by
  rw [scExt_rectangle_eq]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

theorem scExt_isBounded_rectangle (a b : ℝ) : Bornology.IsBounded (rectangle a b) := by
  rw [scExt_rectangle_eq]
  exact (Metric.isBounded_Ioo 0 a).reProdIm (Metric.isBounded_Ioo 0 b)

theorem scExt_convex_rectangle (a b : ℝ) : Convex ℝ (rectangle a b) := by
  have h : rectangle a b =
      {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < a} ∩ ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < b}) := by
    ext z
    simp only [rectangle, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt a)).inter
    ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt b))

theorem scExt_closure_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closure (rectangle a b) = Icc 0 a ×ℂ Icc 0 b := by
  rw [scExt_rectangle_eq, closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]

theorem scExt_frontier_rectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    frontier (rectangle a b) = Icc 0 a ×ℂ {0, b} ∪ {0, a} ×ℂ Icc 0 b := by
  rw [scExt_rectangle_eq, frontier_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne,
    frontier_Ioo ha, frontier_Ioo hb]

theorem scExt_closure_toExt_rectangle (a b : ℝ) :
    closure (toExt (rectangle a b)) = toExt (closure (rectangle a b)) :=
  scExt_closure_toExt_of_isBounded (scExt_isBounded_rectangle a b)

theorem scExt_frontier_toExt_rectangle (a b : ℝ) :
    frontier (toExt (rectangle a b)) = toExt (frontier (rectangle a b)) :=
  scExt_frontier_toExt_of_isBounded (scExt_isBounded_rectangle a b) (scExt_isOpen_rectangle a b)

theorem scExt_scMapExt_coe (k : ℝ) (z : ℂ) :
    scMapExt k (z : ExtPlane) = ((scMap k z : ℂ) : ExtPlane) := rfl

theorem scExt_scMapExt_infty (k : ℝ) : scMapExt k extInf = ((scMapInfty k : ℂ) : ExtPlane) := rfl

/-- **Properness from the boundary behaviour.**  If `F : ℂ̄ → ℂ̄` is continuous on the closure of
`toExt U`, extends `f`, maps `U` into the open set `V` and the boundary of `U` into the boundary
of `V`, then `f : U → V` is a proper map (`ℂ̄` is compact: a limit point of a fibre or of a
closed set lies in `closure (toExt U)`, and it cannot lie on the boundary because `F` would send it
to `∂V ∌ f`-values). -/
theorem scExt_isProperMap_restrict {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hU : IsOpen U) (hV : IsOpen V) (hfc : ContinuousOn f U)
    (hF : ContinuousOn F (closure (toExt U)))
    (hFf : ∀ z : ℂ, F (z : ExtPlane) = ((f z : ℂ) : ExtPlane))
    (hfr : MapsTo F (frontier (toExt U)) (frontier (toExt V))) (hUV : MapsTo f U V) :
    IsProperMap (fun z : U => (⟨f z, hUV z.2⟩ : V)) := by
  have hUo : IsOpen (toExt U) := scExt_isOpen_toExt hU
  have hVo : IsOpen (toExt V) := scExt_isOpen_toExt hV
  rw [isProperMap_iff_ultrafilter]
  refine ⟨(continuousOn_iff_continuous_restrict.1 hfc).subtype_mk _, ?_⟩
  intro 𝒰 y hy
  -- the ultrafilter pushed to `ℂ̄` converges (`ℂ̄` is compact)
  set ι : U → ExtPlane := fun z => ((z : ℂ) : ExtPlane) with hι
  obtain ⟨p, hlim⟩ : ∃ p : ExtPlane, Tendsto ι 𝒰 (𝓝 p) := by
    refine ⟨(𝒰.map ι).lim, ?_⟩
    have := Ultrafilter.le_nhds_lim (𝒰.map ι)
    rwa [Ultrafilter.coe_map] at this
  have hmem : ∀ z : U, ι z ∈ toExt U := fun z => ⟨z, z.2, rfl⟩
  have hpcl : p ∈ closure (toExt U) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall hmem)
  -- `F p = y`: `F ∘ ι = coe ∘ val ∘ (restricted f)` tends both to `F p` and to `y`
  have hFι : ∀ z : U, F (ι z) = ((((⟨f z, hUV z.2⟩ : V) : ℂ) : ℂ) : ExtPlane) := fun z => hFf z
  have h1 : Tendsto (F ∘ ι) 𝒰 (𝓝 (F p)) :=
    (hF p hpcl).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim,
      Eventually.of_forall fun z => subset_closure (hmem z)⟩)
  have h2 : Tendsto (F ∘ ι) 𝒰 (𝓝 (((y : ℂ) : ℂ) : ExtPlane)) := by
    have : F ∘ ι = (fun w : V => ((w : ℂ) : ExtPlane)) ∘ (fun z : U => (⟨f z, hUV z.2⟩ : V)) :=
      funext hFι
    rw [this]
    exact ((OnePoint.continuous_coe.comp continuous_subtype_val).tendsto y).comp hy
  have hFp : F p = ((y : ℂ) : ExtPlane) := tendsto_nhds_unique h1 h2
  -- `p` is not on the boundary: `F p = y ∈ toExt V` is not a boundary point of `toExt V`
  have hpU : p ∈ toExt U := by
    by_contra hpU
    have hfr' : p ∈ frontier (toExt U) := by
      rw [hUo.frontier_eq]
      exact ⟨hpcl, hpU⟩
    have h3 : F p ∈ frontier (toExt V) := hfr hfr'
    rw [hFp] at h3
    have h4 : ((y : ℂ) : ExtPlane) ∈ toExt V ∩ frontier (toExt V) := ⟨⟨y, y.2, rfl⟩, h3⟩
    rw [hVo.inter_frontier_eq] at h4
    exact h4
  obtain ⟨q, hq, rfl⟩ := hpU
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · apply Subtype.ext
    have := hFf q
    rw [hFp] at this
    exact (OnePoint.coe_injective this).symm
  · rw [nhds_subtype_eq_comap, ← OnePoint.comap_coe_nhds, comap_comap]
    exact Filter.map_le_iff_le_comap.1 hlim

/-! ### `ℍ` is a Jordan domain

Upstream copies (with `scExt_` names) of the S05 facts needed to package `ℍ` with the prevertices
as a topological quadrilateral for `thm1_1_elliptic_modulus`: the Cayley transform
`w ↦ i(1+w)/(1-w)` maps the unit disc onto `ℍ` and the unit circle onto `∂ℍ = ℝ ∪ {∞}`. -/

theorem scExt_cayley_det : I * 1 - I * (-1) ≠ 0 := by simp

theorem scExt_cayley_inv_det : (1 : ℂ) * I - (-I) * 1 ≠ 0 := by simp

/-- The Cayley transform `w ↦ i(1+w)/(1-w)` and its inverse `z ↦ (z-i)/(z+i)`. -/
theorem scExt_cayley_apply_inv (v : ExtPlane) :
    mobiusExt I I (-1) 1 (mobiusExt 1 (-I) 1 I v) = v := by
  simpa using mobiusExt_inv_apply scExt_cayley_inv_det v

theorem scExt_cayley_im {w : ℂ} (hw : ‖w‖ < 1) : 0 < ((I * w + I) / (-1 * w + 1)).im := by
  have hb : (-1 : ℂ) * w + 1 ≠ 0 := by
    intro h
    have h1 : w = 1 := by linear_combination -h
    rw [h1, norm_one] at hw
    exact lt_irrefl _ hw
  have h2 : w.re * w.re + w.im * w.im < 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ (Complex.normSq_pos.2 hb)
  simp only [add_im, mul_im, I_re, I_im, add_re, mul_re, neg_re, one_re, neg_im, one_im]
  nlinarith

/-- The Cayley transform maps the unit disc onto the upper half-plane. -/
theorem scExt_cayley_image_disc : mobiusExt I I (-1) 1 '' toExt unitDisc = toExt upperHalf := by
  ext p
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
      intro h
      have h1 : w = 1 := by linear_combination -h
      rw [h1, norm_one] at hw'
      exact lt_irrefl _ hw'
    rw [mobiusExt_coe hden]
    exact ⟨_, scExt_cayley_im hw', rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : 0 < z.im := hz
    have hden : (1 : ℂ) * z + I ≠ 0 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    refine ⟨mobiusExt 1 (-I) 1 I (z : ExtPlane), ?_, scExt_cayley_apply_inv _⟩
    rw [mobiusExt_coe hden]
    refine ⟨_, ?_, rfl⟩
    show ((1 : ℂ) * z + -I) / (1 * z + I) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hden),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, add_im, mul_re, mul_im, one_re, one_im, I_re, I_im, neg_re, neg_im]
    nlinarith

/-- The boundary of `ℍ` in `ℂ̄` is the Cayley image of the unit circle. -/
theorem scExt_frontier_toExt_upperHalf_eq_cayley :
    frontier (toExt upperHalf) = mobiusExt I I (-1) 1 '' toExt (sphere (0 : ℂ) 1) := by
  rw [← scExt_cayley_image_disc,
    show mobiusExt I I (-1) 1 = ⇑(mobiusHomeomorph I I (-1) 1 scExt_cayley_det) from rfl,
    ← (mobiusHomeomorph I I (-1) 1 scExt_cayley_det).image_frontier,
    unitDisc, scExt_frontier_toExt_of_isBounded Metric.isBounded_ball isOpen_ball,
    frontier_ball 0 one_ne_zero]

theorem scExt_isJordanCurve_frontier_upperHalf : IsJordanCurve (frontier (toExt upperHalf)) := by
  refine ⟨fun w => mobiusHomeomorph I I (-1) 1 scExt_cayley_det ((w : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact (mobiusHomeomorph I I (-1) 1 scExt_cayley_det).continuous.comp
      (OnePoint.continuous_coe.comp continuous_subtype_val)
  · intro w₁ w₂ h
    exact Subtype.ext
      (OnePoint.coe_injective ((mobiusHomeomorph I I (-1) 1 scExt_cayley_det).injective h))
  · rw [scExt_frontier_toExt_upperHalf_eq_cayley]
    ext p
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨(w : ℂ), w.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

theorem scExt_isConnected_upperHalf : IsConnected upperHalf :=
  scExt_convex_upperHalf.isConnected ⟨I, by simp [upperHalf]⟩

theorem scExt_isJordanDomain_upperHalf : IsJordanDomain upperHalf :=
  ⟨scExt_isOpen_upperHalf, scExt_isConnected_upperHalf, scExt_isJordanCurve_frontier_upperHalf⟩

/-- The identity is its own boundary extension. -/
theorem scExt_isHomeoExtension_id (U : Set ℂ) : IsHomeoExtension id U U id :=
  ⟨fun _ _ => rfl, continuousOn_id, injOn_id _, image_id _⟩

/-! ### Stage 1: the integrand -/

/-! ### Stage 1 helpers: prevertices, principal and rotated square roots -/

theorem scPrevertex_zero (k : ℝ) : scPrevertex k 0 = -1 / k := rfl

theorem scPrevertex_one (k : ℝ) : scPrevertex k 1 = -1 := rfl

theorem scPrevertex_two (k : ℝ) : scPrevertex k 2 = 1 := rfl

theorem scPrevertex_three (k : ℝ) : scPrevertex k 3 = 1 / k := rfl

/-- The prevertices increase: `-1/k < -1 < 1 < 1/k`. -/
theorem scPrevertex_lt {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scPrevertex k 0 < scPrevertex k 1 ∧ scPrevertex k 1 < scPrevertex k 2 ∧
      scPrevertex k 2 < scPrevertex k 3 := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  rw [scPrevertex_zero, scPrevertex_one, scPrevertex_two, scPrevertex_three, hkinv]
  exact ⟨by linarith, by norm_num, h1k⟩

/-- The upper half-plane is convex (a local copy; `S05` is downstream). -/
theorem convex_upperHalf : Convex ℝ upperHalf := convex_halfSpace_im_gt 0

theorem sub_ofReal_mem_slitPlane {ζ : ℂ} (hζ : 0 < ζ.im) (p : ℝ) : ζ - (p : ℂ) ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr (by simpa using hζ.ne'))

/-- On the closed upper half-plane the principal `w^{-1/2}` is the rotated branch
`e^{-iπ/4} (-i w)^{-1/2}`, whose cut is the negative imaginary axis. -/
theorem cpow_neg_half_eq_rotated {w : ℂ} (hw : w ≠ 0) (him : 0 ≤ w.im) :
    w ^ (-(1 / 2 : ℂ)) = exp (-(π / 4 : ℂ) * I) * (-I * w) ^ (-(1 / 2 : ℂ)) := by
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.2 I_ne_zero
  have hw' : -I * w ≠ 0 := mul_ne_zero hI hw
  have harg : arg (-I * w) = arg w - π / 2 := by
    rw [arg_mul hI hw ?_, arg_neg_I]
    · ring
    · rw [arg_neg_I, Set.mem_Ioc]
      exact ⟨by linarith [arg_nonneg_iff.2 him, Real.pi_pos], by linarith [arg_le_pi w, Real.pi_pos]⟩
  rw [cpow_def_of_ne_zero hw, cpow_def_of_ne_zero hw', ← exp_add]
  congr 1
  simp only [Complex.log, harg, norm_mul, norm_neg, norm_I, one_mul]
  push_cast
  ring

/-- The principal `t^{-1/2}` of a non-zero real number. -/
theorem ofReal_cpow_neg_half {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) ^ (-(1 / 2 : ℂ)) = (if 0 < t then 1 else -I) * ((1 / Real.sqrt |t| : ℝ) : ℂ) := by
  have hpos : ∀ s : ℝ, 0 < s → (s : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / Real.sqrt s : ℝ) : ℂ) := by
    intro s hs
    have h := ofReal_cpow hs.le (-(1 / 2))
    push_cast at h
    rw [← h, Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow, one_div]
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · rw [if_neg (not_lt.2 hlt.le), ofReal_cpow_of_nonpos hlt.le, abs_of_neg hlt, ← ofReal_neg,
      hpos _ (neg_pos.2 hlt)]
    have he : exp (π * I * -(1 / 2 : ℂ)) = -I := by
      rw [show (π : ℂ) * I * -(1 / 2 : ℂ) = ((-(π / 2) : ℝ) : ℂ) * I by push_cast; ring,
        exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
        Real.sin_pi_div_two]
      simp
    rw [he]
    ring
  · rw [if_pos hgt, abs_of_pos hgt, hpos t hgt, one_mul]

/-- `g_k² = -1 / (k² ∏ⱼ (ζ - pⱼ))` everywhere. -/
theorem scIntegrand_sq (k : ℝ) (ζ : ℂ) :
    scIntegrand k ζ ^ 2 = -1 / ((k : ℂ) ^ 2 * ∏ j : Fin 4, (ζ - (scPrevertex k j : ℂ))) := by
  have h : ∀ w : ℂ, (w ^ (-(1 / 2 : ℂ))) ^ 2 = w⁻¹ := fun w => by
    rw [← cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(1 / 2 : ℂ) = -1 by norm_num, cpow_neg_one]
  unfold scIntegrand
  rw [mul_pow, ← Finset.prod_pow]
  simp only [h]
  rw [Finset.prod_inv_distrib, div_pow, neg_sq, I_sq]
  ring

/-- `‖g_k(ζ)‖ = (1/k) ∏ⱼ ‖ζ - pⱼ‖^{-1/2}`. -/
theorem norm_scIntegrand {k : ℝ} (hk₀ : 0 < k) (ζ : ℂ) :
    ‖scIntegrand k ζ‖ = 1 / k * ∏ j : Fin 4, ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by
  unfold scIntegrand
  rw [norm_mul, norm_div, norm_neg, norm_I, norm_real, Real.norm_of_nonneg hk₀.le, norm_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have h := norm_cpow_real (ζ - (scPrevertex k j : ℂ)) (-(1 / 2))
  push_cast at h
  exact h

/-- `ω ↦ -1/(kω)` maps `ℍ` to itself. -/
theorem neg_one_div_mul_mem_upperHalf {k : ℝ} (hk₀ : 0 < k) {ω : ℂ} (hω : ω ∈ upperHalf) :
    -1 / ((k : ℂ) * ω) ∈ upperHalf := by
  have hω' : 0 < ω.im := hω
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω'
  have hne : (k : ℂ) * ω ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hk₀.ne') hω0
  show 0 < (-1 / ((k : ℂ) * ω)).im
  rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
  exact div_pos (by simpa using mul_pos hk₀ hω') (normSq_pos.2 hne)

theorem differentiableOn_scIntegrand {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    DifferentiableOn ℂ (scIntegrand k) upperHalf := by
  have _ := hk₀
  have _ := hk₁
  intro ζ hζ
  have hζ' : 0 < ζ.im := hζ
  refine DifferentiableAt.differentiableWithinAt ?_
  have hfac : ∀ j : Fin 4,
      DifferentiableAt ℂ (fun ζ : ℂ => (ζ - (scPrevertex k j : ℂ)) ^ (-(1 / 2 : ℂ))) ζ :=
    fun j => (differentiableAt_id.sub_const _).cpow_const (sub_ofReal_mem_slitPlane hζ' _)
  unfold scIntegrand
  simp only [Fin.prod_univ_four]
  exact ((((hfac 0).mul (hfac 1)).mul (hfac 2)).mul (hfac 3)).const_mul _

theorem scIntegrand_ne_zero {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {ζ : ℂ} (hζ : ζ ∈ upperHalf) :
    scIntegrand k ζ ≠ 0 := by
  have _ := hk₁
  have hζ' : 0 < ζ.im := hζ
  unfold scIntegrand
  refine mul_ne_zero (div_ne_zero (neg_ne_zero.2 I_ne_zero) (ofReal_ne_zero.2 hk₀.ne')) ?_
  refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
  have h0 := congrArg Complex.im ((cpow_eq_zero_iff _ _).1 h).1
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at h0
  exact hζ'.ne' h0

/-- Rotated branch cuts: `g_k` continues holomorphically across every open real interval. -/
theorem exists_scIntegrand_slitExt {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (scSlitDomain k) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.im → (∀ j, ζ ≠ (scPrevertex k j : ℂ)) → g ζ = scIntegrand k ζ := by
  have _ := hk₀
  have _ := hk₁
  refine ⟨fun ζ => (-I / (k : ℂ)) * ∏ j : Fin 4,
      (exp (-(π / 4 : ℂ) * I) * (-I * (ζ - (scPrevertex k j : ℂ))) ^ (-(1 / 2 : ℂ))), ?_, ?_⟩
  · intro ζ hζ
    refine DifferentiableAt.differentiableWithinAt ?_
    have hfac : ∀ j : Fin 4, DifferentiableAt ℂ (fun ζ : ℂ =>
        exp (-(π / 4 : ℂ) * I) * (-I * (ζ - (scPrevertex k j : ℂ))) ^ (-(1 / 2 : ℂ))) ζ := by
      intro j
      refine DifferentiableAt.const_mul ?_ _
      refine ((differentiableAt_id.sub_const _).const_mul _).cpow_const ?_
      show -I * (ζ - (scPrevertex k j : ℂ)) ∈ slitPlane
      have hre : (-I * (ζ - (scPrevertex k j : ℂ))).re = ζ.im := by
        simp only [mul_re, neg_re, neg_im, I_re, I_im, sub_re, sub_im, ofReal_re, ofReal_im]
        ring
      have him : (-I * (ζ - (scPrevertex k j : ℂ))).im = -(ζ.re - scPrevertex k j) := by
        simp only [mul_im, neg_re, neg_im, I_re, I_im, sub_re, sub_im, ofReal_re, ofReal_im]
        ring
      rw [mem_slitPlane_iff, hre, him]
      by_contra hcon
      rw [not_or, not_lt, not_not] at hcon
      refine hζ j (-ζ.im) (by linarith [hcon.1]) ?_
      apply Complex.ext
      · simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
        linarith [hcon.2]
      · simp only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re]
        ring
    simp only [Fin.prod_univ_four]
    exact ((((hfac 0).mul (hfac 1)).mul (hfac 2)).mul (hfac 3)).const_mul _
  · intro ζ him hne
    show (-I / (k : ℂ)) * ∏ j : Fin 4,
        (exp (-(π / 4 : ℂ) * I) * (-I * (ζ - (scPrevertex k j : ℂ))) ^ (-(1 / 2 : ℂ))) =
      scIntegrand k ζ
    unfold scIntegrand
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    refine (cpow_neg_half_eq_rotated (sub_ne_zero.2 (hne j)) ?_).symm
    simpa using him

/-- Boundary values on the five real intervals (LZ (4.4)). -/
theorem scIntegrand_ofReal {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ}
    (hx : ∀ j, x ≠ scPrevertex k j) :
    scIntegrand k x =
      (if x < -1 / k ∨ 1 / k < x then -I else if x < -1 then 1 else if x < 1 then I else -1) *
        ((1 / Real.sqrt |(1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)| : ℝ) : ℂ) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  have hp0 := scPrevertex_zero k
  have hp1 := scPrevertex_one k
  have hp2 := scPrevertex_two k
  have hp3 := scPrevertex_three k
  have hfac : ∀ j, ((x : ℂ) - (scPrevertex k j : ℂ)) ^ (-(1 / 2 : ℂ)) =
      (if 0 < x - scPrevertex k j then 1 else -I) *
        ((1 / Real.sqrt |x - scPrevertex k j| : ℝ) : ℂ) := by
    intro j
    rw [← ofReal_sub]
    exact ofReal_cpow_neg_half (sub_ne_zero.2 (hx j))
  -- the modulus
  have hR : (1 / (k : ℂ)) * ∏ j : Fin 4, ((1 / Real.sqrt |x - scPrevertex k j| : ℝ) : ℂ) =
      ((1 / Real.sqrt |(1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)| : ℝ) : ℂ) := by
    have hneC : ∀ j, ((Real.sqrt |x - scPrevertex k j| : ℝ) : ℂ) ≠ 0 := fun j =>
      ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.2 (hx j)))).ne'
    have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
    have hpoly : (1 - x ^ 2) * (1 - k ^ 2 * x ^ 2) = k ^ 2 * ((x - scPrevertex k 0) *
        (x - scPrevertex k 1) * (x - scPrevertex k 2) * (x - scPrevertex k 3)) := by
      rw [hp0, hp1, hp2, hp3]
      field_simp
      ring
    have hsq : Real.sqrt |(1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)| =
        k * (Real.sqrt |x - scPrevertex k 0| * Real.sqrt |x - scPrevertex k 1| *
          Real.sqrt |x - scPrevertex k 2| * Real.sqrt |x - scPrevertex k 3|) := by
      rw [hpoly, abs_mul, abs_of_pos (pow_pos hk₀ 2), abs_mul, abs_mul, abs_mul,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hk₀.le, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (abs_nonneg _)]
    rw [Fin.prod_univ_four, hsq]
    push_cast
    field_simp [hneC 0, hneC 1, hneC 2, hneC 3]
  -- the unit
  have hU : -I * ∏ j : Fin 4, (if 0 < x - scPrevertex k j then (1 : ℂ) else -I) =
      (if x < -1 / k ∨ 1 / k < x then -I else if x < -1 then 1 else if x < 1 then I else -1) := by
    have hx0 := hx 0
    have hx1 := hx 1
    have hx2 := hx 2
    have hx3 := hx 3
    rw [hp0] at hx0
    rw [hp1] at hx1
    rw [hp2] at hx2
    rw [hp3] at hx3
    rw [Fin.prod_univ_four, hp0, hp1, hp2, hp3]
    simp only [sub_pos]
    rcases lt_or_gt_of_ne hx0 with h0 | h0
    · have h1 : x < -1 := by linarith
      have h2 : x < 1 := by linarith
      have h3 : x < 1 / k := by linarith
      simp only [not_lt.2 h0.le, not_lt.2 h1.le, not_lt.2 h2.le, not_lt.2 h3.le, h0, true_or,
        ↓reduceIte]
      linear_combination (-I * (I ^ 2 - 1)) * I_sq
    rcases lt_or_gt_of_ne hx1 with h1 | h1
    · have h2 : x < 1 := by linarith
      have h3 : x < 1 / k := by linarith
      simp only [h0, not_lt.2 h1.le, not_lt.2 h2.le, not_lt.2 h3.le, not_lt.2 h0.le, h1,
        false_or, ↓reduceIte]
      linear_combination (I ^ 2 - 1) * I_sq
    rcases lt_or_gt_of_ne hx2 with h2 | h2
    · have h3 : x < 1 / k := by linarith
      have h0' : ¬ x < -1 / k := not_lt.2 h0.le
      simp only [h0, h1, not_lt.2 h2.le, not_lt.2 h3.le, h0', not_lt.2 h1.le, h2, false_or,
        ↓reduceIte]
      linear_combination (-I) * I_sq
    rcases lt_or_gt_of_ne hx3 with h3 | h3
    · have h0' : ¬ x < -1 / k := not_lt.2 h0.le
      simp only [h0, h1, h2, not_lt.2 h3.le, h0', not_lt.2 h1.le, not_lt.2 h2.le, false_or,
        ↓reduceIte]
      linear_combination I_sq
    · simp only [h0, h1, h2, h3, or_true, ↓reduceIte]
      ring
  have hsplit : scIntegrand k x =
      (-I * ∏ j : Fin 4, (if 0 < x - scPrevertex k j then (1 : ℂ) else -I)) *
        ((1 / (k : ℂ)) * ∏ j : Fin 4, ((1 / Real.sqrt |x - scPrevertex k j| : ℝ) : ℂ)) := by
    unfold scIntegrand
    simp only [hfac, Finset.prod_mul_distrib]
    ring
  rw [hsplit, hR, hU]

/-- Integrable singularities at the prevertices. -/
theorem norm_scIntegrand_le_near {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (j : Fin 4) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ ζ : ℂ, 0 ≤ ζ.im → ‖ζ - (scPrevertex k j : ℂ)‖ < δ →
      ζ ≠ (scPrevertex k j : ℂ) →
        ‖scIntegrand k ζ‖ ≤ C * ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (1 / k - 1) 2 / 2 := ⟨_, rfl⟩
  have hm1 := min_le_left (1 / k - 1) 2
  have hm2 := min_le_right (1 / k - 1) 2
  have hδ : 0 < δ := by
    rw [hδdef]
    exact half_pos (lt_min (by linarith) two_pos)
  have e1 : -1 / k = -k⁻¹ := by ring
  have e2 : 1 / k = k⁻¹ := one_div k
  have hsep : ∀ i : Fin 4, i ≠ j → 2 * δ ≤ |scPrevertex k i - scPrevertex k j| := by
    intro i hij
    fin_cases i <;> fin_cases j <;> simp [scPrevertex] at hij ⊢ <;>
      first
      | exact le_abs.2 (Or.inl (by linarith))
      | exact le_abs.2 (Or.inr (by linarith))
  refine ⟨1 / k * (δ ^ (-(1 / 2 : ℝ))) ^ 3, δ, hδ, fun ζ _ hζδ hζne => ?_⟩
  have hfar : ∀ i ∈ Finset.univ.erase j, δ ≤ ‖ζ - (scPrevertex k i : ℂ)‖ := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have h1 := hsep i hij
    have h2 : ‖((scPrevertex k i : ℝ) : ℂ) - (scPrevertex k j : ℂ)‖ ≤
        ‖ζ - (scPrevertex k i : ℂ)‖ + ‖ζ - (scPrevertex k j : ℂ)‖ := by
      calc ‖((scPrevertex k i : ℝ) : ℂ) - (scPrevertex k j : ℂ)‖
          = ‖(ζ - (scPrevertex k j : ℂ)) - (ζ - (scPrevertex k i : ℂ))‖ := by ring_nf
        _ ≤ ‖ζ - (scPrevertex k j : ℂ)‖ + ‖ζ - (scPrevertex k i : ℂ)‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs] at h2
    linarith
  rw [norm_scIntegrand hk₀, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have hprod : ∏ i ∈ Finset.univ.erase j, ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) ≤
      (δ ^ (-(1 / 2 : ℝ))) ^ 3 := by
    calc ∏ i ∈ Finset.univ.erase j, ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ))
        ≤ ∏ _i ∈ Finset.univ.erase j, δ ^ (-(1 / 2 : ℝ)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi =>
            Real.rpow_le_rpow_of_nonpos hδ (hfar i hi) (by norm_num)
      _ = (δ ^ (-(1 / 2 : ℝ))) ^ 3 := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Fintype.card_fin]
  have hpos : 0 ≤ ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by positivity
  have hk' : 0 ≤ 1 / k := by positivity
  calc 1 / k * (‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
        ∏ i ∈ Finset.univ.erase j, ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)))
      ≤ 1 / k * (‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (δ ^ (-(1 / 2 : ℝ))) ^ 3) := by
        gcongr
    _ = _ := by ring

/-- The inversion `ω ↦ -1/(kω)` permutes the prevertices and preserves `g_k dζ` up to a sign. -/
theorem scIntegrand_inversion {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ ω ∈ upperHalf,
      scIntegrand k (-1 / ((k : ℂ) * ω)) * (1 / ((k : ℂ) * ω ^ 2)) = ε * scIntegrand k ω := by
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
  have hne0 : ∀ ω ∈ upperHalf, ω ≠ 0 := fun ω hω h => by
    have hω' : 0 < ω.im := hω
    simp [h] at hω'
  obtain ⟨L, hL⟩ : ∃ L : ℂ → ℂ,
      L = fun ω => scIntegrand k (-1 / ((k : ℂ) * ω)) * (1 / ((k : ℂ) * ω ^ 2)) := ⟨_, rfl⟩
  have hg := differentiableOn_scIntegrand hk₀ hk₁
  have hgc : ContinuousOn (scIntegrand k) upperHalf := hg.continuousOn
  have hLc : ContinuousOn L upperHalf := by
    rw [hL]
    have h1 : ContinuousOn (fun ω : ℂ => -1 / ((k : ℂ) * ω)) upperHalf :=
      continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun ω hω =>
        mul_ne_zero hk0 (hne0 ω hω)
    have h2 : ContinuousOn (fun ω : ℂ => 1 / ((k : ℂ) * ω ^ 2)) upperHalf :=
      continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun ω hω =>
        mul_ne_zero hk0 (pow_ne_zero 2 (hne0 ω hω))
    exact (hgc.comp h1 fun ω hω => neg_one_div_mul_mem_upperHalf hk₀ hω).mul h2
  have hsq : ∀ ω ∈ upperHalf, L ω ^ 2 = scIntegrand k ω ^ 2 := by
    intro ω hω
    have hω0 := hne0 ω hω
    have hω' : 0 < ω.im := hω
    have hPne : ∏ j : Fin 4, (ω - (scPrevertex k j : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ h => by
        have h0 := congrArg Complex.im h
        simp only [sub_im, ofReal_im, sub_zero, zero_im] at h0
        exact hω'.ne' h0
    have hP : ∏ j : Fin 4, (-1 / ((k : ℂ) * ω) - (scPrevertex k j : ℂ)) =
        (∏ j : Fin 4, (ω - (scPrevertex k j : ℂ))) / ((k : ℂ) ^ 2 * ω ^ 4) := by
      simp only [Fin.prod_univ_four, scPrevertex_zero, scPrevertex_one, scPrevertex_two,
        scPrevertex_three]
      push_cast
      field_simp
      ring
    rw [hL]
    simp only [mul_pow, scIntegrand_sq, hP]
    field_simp
  have hratio : MapsTo (fun ω => L ω / scIntegrand k ω) upperHalf ({1, -1} : Set ℂ) := by
    intro ω hω
    have hgne := scIntegrand_ne_zero hk₀ hk₁ hω
    have h2 : (L ω / scIntegrand k ω) ^ 2 = 1 := by
      rw [div_pow, hsq ω hω, div_self (pow_ne_zero 2 hgne)]
    have h3 : (L ω / scIntegrand k ω - 1) * (L ω / scIntegrand k ω + 1) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hI : I ∈ upperHalf := by
    show 0 < I.im
    simp
  have hconst : ∀ ω ∈ upperHalf, L ω / scIntegrand k ω = L I / scIntegrand k I := fun ω hω =>
    convex_upperHalf.isPreconnected.constant_of_mapsTo (Set.toFinite _).isDiscrete
      (hLc.div hgc fun ω hω => scIntegrand_ne_zero hk₀ hk₁ hω) hratio hω hI
  refine ⟨L I / scIntegrand k I, ?_, fun ω hω => ?_⟩
  · have h' : L I / scIntegrand k I ∈ ({1, -1} : Set ℂ) := hratio hI
    rcases h' with h | h
    · rw [h]
      norm_num
    · rw [Set.mem_singleton_iff.1 h]
      norm_num
  · have h := hconst ω hω
    rw [← h, div_mul_cancel₀ _ (scIntegrand_ne_zero hk₀ hk₁ hω), hL]

/-! ### Stage 2: primitive -/

/-! ### Stage 2 helpers: segments from `i` and a primitive on `ℍ` -/

theorem isOpen_upperHalf' : IsOpen upperHalf := isOpen_lt continuous_const continuous_im

theorem I_mem_upperHalf : I ∈ upperHalf := by
  show 0 < I.im
  simp

/-- The segment from `i` to a point of `ℍ` stays in `ℍ`. -/
theorem segment_I_mem_upperHalf {z : ℂ} (hz : 0 ≤ z.im) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    I + (t : ℂ) * (z - I) ∈ upperHalf := by
  show 0 < (I + (t : ℂ) * (z - I)).im
  have him : (I + (t : ℂ) * (z - I)).im = (1 - t) + t * z.im := by
    simp only [add_im, I_im, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, I_re, zero_mul, add_zero]
    ring
  rw [him]
  nlinarith [mul_nonneg ht0 hz]

theorem segment_I_mem_upperHalf_of_mem {z : ℂ} (hz : z ∈ upperHalf) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : I + (t : ℂ) * (z - I) ∈ upperHalf := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · exact segment_I_mem_upperHalf (le_of_lt hz) ht0 ht1
  · simpa using hz

/-- `scMap` differs on `ℍ` by a constant from a primitive of the integrand. -/
theorem exists_primitive_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G upperHalf ∧
      (∀ z ∈ upperHalf, deriv G z = scIntegrand k z) ∧
        ∃ c : ℂ, ∀ z ∈ upperHalf, scMap k z = G z - c := by
  haveI : ContractibleSpace upperHalf := convex_upperHalf.contractibleSpace ⟨I, I_mem_upperHalf⟩
  obtain ⟨G, hG, hGd⟩ := RMT.exists_primitive_of_simplyConnected isOpen_upperHalf'
    (convex_upperHalf.isConnected ⟨I, I_mem_upperHalf⟩) (differentiableOn_scIntegrand hk₀ hk₁)
  refine ⟨G, hG, hGd, G I + ∫ t in (0 : ℝ)..1, scIntegrand k (I + t * ((scPrevertex k 0 : ℂ) - I)) *
      ((scPrevertex k 0 : ℂ) - I), fun z hz => ?_⟩
  have hseg : (∫ t in (0 : ℝ)..1, scIntegrand k (I + t * (z - I)) * (z - I)) = G z - G I := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (I + t * (z - I)))
        (scIntegrand k (I + t * (z - I)) * (z - I)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hmem := segment_I_mem_upperHalf_of_mem hz ht.1 ht.2
      have hGt : HasDerivAt G (scIntegrand k (I + t * (z - I))) (I + t * (z - I)) := by
        have h := (hG.differentiableAt (isOpen_upperHalf'.mem_nhds hmem)).hasDerivAt
        rwa [hGd _ hmem] at h
      have hp : HasDerivAt (fun t : ℝ => I + (t : ℂ) * (z - I)) (z - I) t := by
        have h := ((hasDerivAt_id (t : ℂ)).mul_const (z - I)).const_add I
        simpa using h.comp_ofReal
      exact hGt.comp t hp
    have hint : IntervalIntegrable (fun t : ℝ => scIntegrand k (I + t * (z - I)) * (z - I))
        volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      refine ContinuousOn.mul ?_ continuousOn_const
      refine (differentiableOn_scIntegrand hk₀ hk₁).continuousOn.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
      intro t ht
      exact segment_I_mem_upperHalf_of_mem hz ht.1 ht.2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  unfold scMap
  rw [hseg]
  ring

theorem hasDerivAt_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    HasDerivAt (scMap k) (scIntegrand k z) z := by
  obtain ⟨G, hG, hGd, c, hc⟩ := exists_primitive_scMap hk₀ hk₁
  have hGz : HasDerivAt G (scIntegrand k z) z := by
    have h := (hG.differentiableAt (isOpen_upperHalf'.mem_nhds hz)).hasDerivAt
    rwa [hGd z hz] at h
  refine (hGz.sub_const c).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalf'.mem_nhds hz] with w hw
  exact hc w hw

/-! ### Stage 3: continuity up to the real axis -/

/-! ### Stage 3 helpers: a uniform bound along the segments from `i` -/

theorem measurable_scIntegrand (k : ℝ) : Measurable (scIntegrand k) := by
  have h : ∀ j : Fin 4, Measurable fun ζ : ℂ => (ζ - (scPrevertex k j : ℂ)) ^ (-(1 / 2 : ℂ)) :=
    fun j => (measurable_id.sub_const _).pow_const _
  unfold scIntegrand
  simp only [Fin.prod_univ_four]
  exact measurable_const.mul ((((h 0).mul (h 1)).mul (h 2)).mul (h 3))

theorem scPrevertex_strictMono {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    StrictMono (scPrevertex k) := by
  obtain ⟨h01, h12, h23⟩ := scPrevertex_lt hk₀ hk₁
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  · exact h01
  · exact h12
  · exact h23

/-- If `ζ` is at distance `≥ c` from every prevertex except `pᵢ`, then
`‖g_k(ζ)‖ ≤ (1/k) c^{-3/2} ‖ζ - pᵢ‖^{-1/2}`. -/
theorem norm_scIntegrand_le_of_far {k : ℝ} (hk₀ : 0 < k) {ζ : ℂ} (i : Fin 4) {c : ℝ}
    (hc : 0 < c) (hfar : ∀ j, j ≠ i → c ≤ ‖ζ - (scPrevertex k j : ℂ)‖) :
    ‖scIntegrand k ζ‖ ≤
      1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 3 * ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by
  rw [norm_scIntegrand hk₀, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hprod : ∏ j ∈ Finset.univ.erase i, ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)) ≤
      (c ^ (-(1 / 2 : ℝ))) ^ 3 := by
    calc ∏ j ∈ Finset.univ.erase i, ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ))
        ≤ ∏ _j ∈ Finset.univ.erase i, c ^ (-(1 / 2 : ℝ)) :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) fun j hj =>
            Real.rpow_le_rpow_of_nonpos hc (hfar j (Finset.ne_of_mem_erase hj)) (by norm_num)
      _ = (c ^ (-(1 / 2 : ℝ))) ^ 3 := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  have hpos : 0 ≤ ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by positivity
  have hk' : 0 ≤ 1 / k := by positivity
  calc 1 / k * (‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
        ∏ j ∈ Finset.univ.erase i, ‖ζ - (scPrevertex k j : ℂ)‖ ^ (-(1 / 2 : ℝ)))
      ≤ 1 / k * (‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (c ^ (-(1 / 2 : ℝ))) ^ 3) := by
        gcongr
    _ = _ := by ring

/-- Every point is at positive distance from all prevertices but (at most) one. -/
theorem exists_far_from_prevertices {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (z₀ : ℂ) :
    ∃ i : Fin 4, ∃ ρ > 0, ∀ j, j ≠ i → ρ ≤ ‖z₀ - (scPrevertex k j : ℂ)‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, ∀ j, j ≠ i → z₀ ≠ (scPrevertex k j : ℂ) := by
    by_cases h : ∃ i : Fin 4, z₀ = (scPrevertex k i : ℂ)
    · obtain ⟨i, rfl⟩ := h
      exact ⟨i, fun j hj h => hj ((scPrevertex_strictMono hk₀ hk₁).injective
        (ofReal_injective h).symm)⟩
    · simp only [not_exists] at h
      exact ⟨0, fun j _ => h j⟩
  have hev : ∀ j : Fin 4, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), j ≠ i → ρ ≤ ‖z₀ - (scPrevertex k j : ℂ)‖ := by
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have hpos : 0 < ‖z₀ - (scPrevertex k j : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hi j hj))
      filter_upwards [nhdsWithin_le_nhds (eventually_le_nhds hpos)] with ρ hρ _
      exact hρ
  obtain ⟨ρ, hρ, hρpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  exact ⟨i, ρ, hρpos, hρ⟩

theorem continuousOn_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ContinuousOn (scMap k) {z : ℂ | 0 ≤ z.im} := by
  intro z₀ hz₀
  have hz₀' : 0 ≤ z₀.im := hz₀
  have hae1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
    rw [ae_iff]
    simp
  obtain ⟨i, ρ, hρ, hfar⟩ := exists_far_from_prevertices hk₀ hk₁ z₀
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖z₀ - I‖ + 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; linarith [norm_nonneg (z₀ - I)]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ρ / (2 * (M + 1)) := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hc₀M : c₀ * M + c₀ = ρ / 2 := by
    rw [hc₀]
    field_simp
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 / k * (c₀ ^ (-(1 / 2 : ℝ))) ^ 3 * M := ⟨_, rfl⟩
  have hη : 0 < min 1 (ρ / 2) := lt_min one_pos (half_pos hρ)
  have hS : ContinuousWithinAt
      (fun z => ∫ t in (0 : ℝ)..1, scIntegrand k (I + t * (z - I)) * (z - I))
      {z : ℂ | 0 ≤ z.im} z₀ := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun t => C * (1 - t) ^ (-(1 / 2 : ℝ))) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun z => ?_
      exact (((measurable_scIntegrand k).comp (measurable_const.add
        (Complex.measurable_ofReal.mul measurable_const))).mul measurable_const).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hη)] with z hzs hzb
      rw [mem_ball_iff_norm] at hzb
      have hzs' : 0 ≤ z.im := hzs
      filter_upwards [hae1] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
      show ‖scIntegrand k (I + t * (z - I)) * (z - I)‖ ≤ C * (1 - t) ^ (-(1 / 2 : ℝ))
      obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = I + (t : ℂ) * (z - I) := ⟨_, rfl⟩
      rw [← hζ]
      have him : ζ.im = (1 - t) + t * z.im := by
        rw [hζ]
        simp only [add_im, I_im, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, I_re, zero_mul,
          add_zero]
        ring
      have hlow : ∀ p : ℝ, 1 - t ≤ ‖ζ - (p : ℂ)‖ := fun p => by
        have h1 := abs_im_le_norm (ζ - (p : ℂ))
        have h2 : (ζ - (p : ℂ)).im = ζ.im := by simp
        rw [h2, him] at h1
        have h3 : 0 ≤ t * z.im := mul_nonneg ht.1.le hzs'
        calc 1 - t ≤ (1 - t) + t * z.im := by linarith
          _ ≤ |(1 - t) + t * z.im| := le_abs_self _
          _ ≤ _ := h1
      have hzI : ‖z - I‖ ≤ M := by
        calc ‖z - I‖ = ‖(z - z₀) + (z₀ - I)‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀ - I‖ := norm_add_le _ _
          _ ≤ M := by rw [hM]; linarith [min_le_left 1 (ρ / 2)]
      have hζz : ‖ζ - z‖ = (1 - t) * ‖z - I‖ := by
        rw [hζ, show I + (t : ℂ) * (z - I) - z = ((1 - t : ℝ) : ℂ) * (I - z) by push_cast; ring,
          norm_mul, norm_real, Real.norm_of_nonneg (by linarith), norm_sub_rev]
      have hfar' : ∀ j, j ≠ i → c₀ ≤ ‖ζ - (scPrevertex k j : ℂ)‖ := by
        intro j hj
        have h1 := hfar j hj
        have h2 : ‖z₀ - (scPrevertex k j : ℂ)‖ ≤ ‖z - (scPrevertex k j : ℂ)‖ + ‖z - z₀‖ := by
          calc ‖z₀ - (scPrevertex k j : ℂ)‖ = ‖(z - (scPrevertex k j : ℂ)) - (z - z₀)‖ := by
                ring_nf
            _ ≤ _ := norm_sub_le _ _
        have h3 : ‖z - (scPrevertex k j : ℂ)‖ ≤ ‖ζ - (scPrevertex k j : ℂ)‖ + ‖ζ - z‖ := by
          calc ‖z - (scPrevertex k j : ℂ)‖ = ‖(ζ - (scPrevertex k j : ℂ)) - (ζ - z)‖ := by
                ring_nf
            _ ≤ _ := norm_sub_le _ _
        have hmin := min_le_right 1 (ρ / 2)
        have h4 := hlow (scPrevertex k j)
        by_cases hct : c₀ ≤ 1 - t
        · linarith
        · have hct' : 1 - t ≤ c₀ := (not_le.1 hct).le
          have h5 : (1 - t) * ‖z - I‖ ≤ c₀ * M :=
            mul_le_mul hct' hzI (norm_nonneg _) hc₀pos.le
          linarith
      have hgb := norm_scIntegrand_le_of_far hk₀ i hc₀pos hfar'
      have hi : ‖ζ - (scPrevertex k i : ℂ)‖ ^ (-(1 / 2 : ℝ)) ≤ (1 - t) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (hlow _) (by norm_num)
      have hA : 0 ≤ 1 / k * (c₀ ^ (-(1 / 2 : ℝ))) ^ 3 := by positivity
      rw [norm_mul]
      calc ‖scIntegrand k ζ‖ * ‖z - I‖
          ≤ (1 / k * (c₀ ^ (-(1 / 2 : ℝ))) ^ 3 * (1 - t) ^ (-(1 / 2 : ℝ))) * M :=
            mul_le_mul (hgb.trans (mul_le_mul_of_nonneg_left hi hA)) hzI (norm_nonneg _)
              (by positivity)
        _ = C * (1 - t) ^ (-(1 / 2 : ℝ)) := by rw [hC]; ring
    · have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      have h2 := h1.comp_sub_left 1
      simp only [sub_zero, sub_self] at h2
      exact h2.symm.const_mul C
    · filter_upwards [hae1] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hmem := segment_I_mem_upperHalf hz₀' ht.1.le htl
      have hgc : ContinuousAt (scIntegrand k) (I + t * (z₀ - I)) :=
        ((differentiableOn_scIntegrand hk₀ hk₁).differentiableAt
          (isOpen_upperHalf'.mem_nhds hmem)).continuousAt
      have hp : ContinuousAt (fun z : ℂ => I + (t : ℂ) * (z - I)) z₀ := by fun_prop
      exact ((ContinuousAt.comp (g := scIntegrand k) (f := fun z : ℂ => I + (t : ℂ) * (z - I)) hgc hp).mul
        (continuousAt_id.sub continuousAt_const)).continuousWithinAt
  show ContinuousWithinAt (fun z => (∫ t in (0 : ℝ)..1, scIntegrand k (I + t * (z - I)) * (z - I)) -
    ∫ t in (0 : ℝ)..1, scIntegrand k (I + t * ((scPrevertex k 0 : ℂ) - I)) *
      ((scPrevertex k 0 : ℂ) - I)) {z : ℂ | 0 ≤ z.im} z₀
  exact hS.sub continuousWithinAt_const

/-! ### Stage 4: continuity at `∞` (via the inversion symmetry) -/

/-! ### Stage 4 helpers: the inversion identity `F(-1/(kz)) = ε F(z) + c` -/

/-- `ω ↦ -1/(kω)` has derivative `1/(kω²)`. -/
theorem hasDerivAt_neg_one_div_mul {k : ℝ} (hk₀ : 0 < k) {ω : ℂ} (hω : ω ≠ 0) :
    HasDerivAt (fun ω : ℂ => -1 / ((k : ℂ) * ω)) (1 / ((k : ℂ) * ω ^ 2)) ω := by
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
  have h := (((hasDerivAt_id ω).const_mul (k : ℂ)).inv (mul_ne_zero hk0 hω)).const_mul (-1 : ℂ)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [id, mul_one]
    field_simp
  · simp only [Pi.inv_apply, id]
    ring

/-- `ω ↦ -1/(kω)` maps the closed upper half-plane minus `0` to itself. -/
theorem neg_one_div_mul_im_nonneg {k : ℝ} (hk₀ : 0 < k) {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (-1 / ((k : ℂ) * w)).im := by
  rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
  exact div_nonneg (by simpa using mul_nonneg hk₀.le hw) (normSq_nonneg _)

/-- `ω ↦ -1/(kω)` is an involution of `ℂ ∖ {0}`. -/
theorem neg_one_div_mul_involutive {k : ℝ} (hk₀ : 0 < k) {w : ℂ} (hw : w ≠ 0) :
    -1 / ((k : ℂ) * (-1 / ((k : ℂ) * w))) = w := by
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
  field_simp

/-- **The inversion identity.**  On the closed upper half-plane minus `0`,
`F(-1/(kz)) = ε F(z) + c` for a sign `ε` and a constant `c`. -/
theorem scMap_inversion {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ ε c : ℂ, ε ^ 2 = 1 ∧ ∀ z : ℂ, 0 ≤ z.im → z ≠ 0 →
      scMap k (-1 / ((k : ℂ) * z)) = ε * scMap k z + c := by
  obtain ⟨ε, hε, hinv⟩ := scIntegrand_inversion hk₀ hk₁
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
  have hne0 : ∀ ω ∈ upperHalf, ω ≠ 0 := fun ω hω h => by
    have hω' : 0 < ω.im := hω
    simp [h] at hω'
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, h = fun ω => scMap k (-1 / ((k : ℂ) * ω)) - ε * scMap k ω :=
    ⟨_, rfl⟩
  have hderiv : ∀ ω ∈ upperHalf, HasDerivAt h 0 ω := by
    intro ω hω
    have h1 := (hasDerivAt_scMap hk₀ hk₁ (neg_one_div_mul_mem_upperHalf hk₀ hω)).comp ω
      (hasDerivAt_neg_one_div_mul hk₀ (hne0 ω hω))
    have h2 := (hasDerivAt_scMap hk₀ hk₁ hω).const_mul ε
    have h3 := h1.sub h2
    rw [hinv ω hω, sub_self] at h3
    rw [hh]
    exact h3
  have hconst : ∀ ω ∈ upperHalf, h ω = h I := fun ω hω =>
    isOpen_upperHalf'.is_const_of_deriv_eq_zero convex_upperHalf.isPreconnected
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hderiv w hw).deriv) hω I_mem_upperHalf
  refine ⟨ε, h I, hε, fun z hz hz0 => ?_⟩
  have hcont := continuousOn_scMap hk₀ hk₁
  have hMc : ContinuousAt (fun w : ℂ => -1 / ((k : ℂ) * w)) z :=
    continuousAt_const.div (continuousAt_const.mul continuousAt_id) (mul_ne_zero hk0 hz0)
  have hA : ContinuousWithinAt (fun w => scMap k (-1 / ((k : ℂ) * w))) upperHalf z :=
    ContinuousWithinAt.comp (g := scMap k) (f := fun w : ℂ => -1 / ((k : ℂ) * w))
      (hcont _ (neg_one_div_mul_im_nonneg hk₀ hz)) hMc.continuousWithinAt
      (fun w hw => show (0 : ℝ) ≤ (-1 / ((k : ℂ) * w)).im from
        le_of_lt (neg_one_div_mul_mem_upperHalf hk₀ hw))
  have hB : ContinuousWithinAt (scMap k) upperHalf z :=
    (hcont z hz).mono fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt hw
  have hlim1 : Tendsto h (𝓝[upperHalf] z)
      (𝓝 (scMap k (-1 / ((k : ℂ) * z)) - ε * scMap k z)) := by
    rw [hh]
    exact hA.tendsto.sub (hB.tendsto.const_mul ε)
  have hlim2 : Tendsto h (𝓝[upperHalf] z) (𝓝 (h I)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw => (hconst w hw).symm)
  haveI : (𝓝[upperHalf] z).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [show upperHalf = {w : ℂ | 0 < w.im} from rfl, closure_setOf_lt_im]
    exact hz
  have heq := tendsto_nhds_unique hlim1 hlim2
  linear_combination heq

theorem tendsto_scMap_cobounded {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    Tendsto (scMap k) (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 (scMapInfty k)) := by
  obtain ⟨ε, c, -, hinv⟩ := scMap_inversion hk₀ hk₁
  obtain ⟨s, hs⟩ : ∃ s : Set ℂ, s = {z : ℂ | 0 ≤ z.im} := ⟨_, rfl⟩
  rw [← hs]
  -- `-1/(kz) → 0` within the closed half-plane
  have hM : Tendsto (fun z : ℂ => -1 / ((k : ℂ) * z)) (Bornology.cobounded ℂ ⊓ 𝓟 s) (𝓝[s] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (tendsto_inv₀_cobounded (α := ℂ)).const_mul (-1 / (k : ℂ))
      rw [mul_zero] at h
      refine (h.congr fun z => ?_).mono_left inf_le_left
      ring
    · filter_upwards [(inf_le_right : Bornology.cobounded ℂ ⊓ 𝓟 s ≤ 𝓟 s) (mem_principal_self s)]
        with z hz
      rw [hs] at hz ⊢
      exact neg_one_div_mul_im_nonneg hk₀ hz
  have hne : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 s, z ≠ 0 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).mono fun z hz => norm_pos_iff.1 hz)
  have hc0 : Tendsto (scMap k) (𝓝[s] 0) (𝓝 (scMap k 0)) := by
    rw [hs]
    exact continuousOn_scMap hk₀ hk₁ 0 (by simp)
  have hL : Tendsto (scMap k) (Bornology.cobounded ℂ ⊓ 𝓟 s) (𝓝 (ε * scMap k 0 + c)) := by
    refine (((hc0.comp hM).const_mul ε).add_const c).congr' ?_
    filter_upwards [hne, (inf_le_right : Bornology.cobounded ℂ ⊓ 𝓟 s ≤ 𝓟 s)
      (mem_principal_self s)] with z hz0 hz
    rw [hs] at hz
    have hMz0 : -1 / ((k : ℂ) * z) ≠ 0 :=
      div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero (ofReal_ne_zero.2 hk₀.ne') hz0)
    have h := hinv (-1 / ((k : ℂ) * z)) (neg_one_div_mul_im_nonneg hk₀ hz) hMz0
    rw [neg_one_div_mul_involutive hk₀ hz0] at h
    simp only [Function.comp_apply]
    exact h.symm
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) atTop (Bornology.cobounded ℂ ⊓ 𝓟 s) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Filter.Eventually.of_forall fun x => ?_)⟩
    · refine (tendsto_norm_atTop_iff_cobounded (f := fun x : ℝ => (x : ℂ)) (l := atTop)).1 ?_
      simpa using tendsto_abs_atTop_atTop
    · rw [hs]
      simp
  have hinf : scMapInfty k = ε * scMap k 0 + c := (hL.comp hreal).limUnder_eq
  rw [hinf]
  exact hL

/-! ### Stage 5: boundary correspondence -/

/-! ### Stage 5 helpers (A): the real density, integrability, and `F` along the real axis -/

/-- The density `1/√|(1-x²)(1-k²x²)|` of `|g_k|` on the real axis (proof machinery for the
boundary correspondence). -/
def scDensity (k x : ℝ) : ℝ := 1 / Real.sqrt |(1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)|

theorem scDensity_neg (k x : ℝ) : scDensity k (-x) = scDensity k x := by
  simp only [scDensity, neg_sq]

/-- `g_k` vanishes at the prevertices (the principal power of `0`). -/
theorem scIntegrand_prevertex (k : ℝ) (j : Fin 4) : scIntegrand k (scPrevertex k j) = 0 := by
  unfold scIntegrand
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [sub_self, zero_cpow (by norm_num)]

theorem scDensity_prevertex {k : ℝ} (hk₀ : 0 < k) (j : Fin 4) :
    scDensity k (scPrevertex k j) = 0 := by
  have hk : k ≠ 0 := hk₀.ne'
  have h0 : (1 - scPrevertex k j ^ 2) * (1 - k ^ 2 * scPrevertex k j ^ 2) = 0 := by
    fin_cases j
    · show (1 - (-1 / k) ^ 2) * (1 - k ^ 2 * (-1 / k) ^ 2) = 0
      have h1 : k ^ 2 * (-1 / k) ^ 2 = 1 := by field_simp
      rw [h1, sub_self, mul_zero]
    · show (1 - (-1 : ℝ) ^ 2) * (1 - k ^ 2 * (-1) ^ 2) = 0
      norm_num
    · show (1 - (1 : ℝ) ^ 2) * (1 - k ^ 2 * 1 ^ 2) = 0
      norm_num
    · show (1 - (1 / k) ^ 2) * (1 - k ^ 2 * (1 / k) ^ 2) = 0
      have h1 : k ^ 2 * (1 / k) ^ 2 = 1 := by field_simp
      rw [h1, sub_self, mul_zero]
  simp [scDensity, h0]

/-- `‖g_k(x)‖ = scDensity k x` on the real axis. -/
theorem norm_scIntegrand_ofReal {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (x : ℝ) :
    ‖scIntegrand k x‖ = scDensity k x := by
  by_cases hx : ∀ j, x ≠ scPrevertex k j
  · rw [scIntegrand_ofReal hk₀ hk₁ hx, norm_mul, norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hu : ‖(if x < -1 / k ∨ 1 / k < x then -I else if x < -1 then (1 : ℂ) else
        if x < 1 then I else -1)‖ = 1 := by
      split_ifs <;> simp
    rw [hu, one_mul]
    rfl
  · simp only [not_forall, not_not] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [scIntegrand_prevertex, norm_zero, scDensity_prevertex hk₀]

/-- `|x - p|^{-1/2}` is integrable on bounded intervals. -/
theorem intervalIntegrable_abs_sub_rpow_neg_half (p a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x - p| ^ (-(1 / 2 : ℝ))) volume a b := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |a - p| + |b - p| + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 : IntervalIntegrable (fun x : ℝ => |x - p| ^ (-(1 / 2 : ℝ))) volume p (p + R) := by
    have h := hr.comp_sub_right p
    simp only [zero_add] at h
    rw [add_comm] at h
    refine (intervalIntegrable_congr fun x hx => ?_).1 h
    rw [uIoc_of_le (by linarith)] at hx
    rw [abs_of_nonneg (by linarith [hx.1])]
  have h2 : IntervalIntegrable (fun x : ℝ => |x - p| ^ (-(1 / 2 : ℝ))) volume (p - R) p := by
    have h := (hr.comp_sub_left p).symm
    simp only [sub_zero] at h
    refine (intervalIntegrable_congr fun x hx => ?_).1 h
    rw [uIoc_of_le (by linarith)] at hx
    rw [abs_of_nonpos (by linarith [hx.2]), neg_sub]
  refine (h2.trans h1).mono_set ?_
  apply uIcc_subset_uIcc
  · rw [mem_uIcc]
    left
    constructor <;> cases abs_cases (a - p) <;> linarith [abs_nonneg (b - p)]
  · rw [mem_uIcc]
    left
    constructor <;> cases abs_cases (b - p) <;> linarith [abs_nonneg (a - p)]

/-- `x ↦ g_k(x)` is locally integrable on the real axis. -/
theorem locallyIntegrable_scIntegrand_ofReal {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    LocallyIntegrable (fun x : ℝ => scIntegrand k x) volume := by
  intro x₀
  obtain ⟨i, ρ, hρ, hfar⟩ := exists_far_from_prevertices hk₀ hk₁ (x₀ : ℂ)
  refine ⟨Ioo (x₀ - ρ / 2) (x₀ + ρ / 2), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  have hmeas : AEStronglyMeasurable (fun x : ℝ => scIntegrand k x)
      (volume.restrict (Ioo (x₀ - ρ / 2) (x₀ + ρ / 2))) :=
    ((measurable_scIntegrand k).comp Complex.measurable_ofReal).aestronglyMeasurable
  have hbound : IntegrableOn (fun x : ℝ => 1 / k * ((ρ / 2) ^ (-(1 / 2 : ℝ))) ^ 3 *
      |x - scPrevertex k i| ^ (-(1 / 2 : ℝ))) (Ioo (x₀ - ρ / 2) (x₀ + ρ / 2)) := by
    have h := ((intervalIntegrable_abs_sub_rpow_neg_half (scPrevertex k i) (x₀ - ρ / 2)
      (x₀ + ρ / 2)).const_mul (1 / k * ((ρ / 2) ^ (-(1 / 2 : ℝ))) ^ 3))
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)] at h
    exact h
  refine hbound.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hfar' : ∀ j, j ≠ i → ρ / 2 ≤ ‖(x : ℂ) - (scPrevertex k j : ℂ)‖ := by
    intro j hj
    have h1 := hfar j hj
    have h2 : ‖(x₀ : ℂ) - (scPrevertex k j : ℂ)‖ ≤
        ‖(x : ℂ) - (scPrevertex k j : ℂ)‖ + ‖(x : ℂ) - (x₀ : ℂ)‖ := by
      calc ‖(x₀ : ℂ) - (scPrevertex k j : ℂ)‖
          = ‖((x : ℂ) - (scPrevertex k j : ℂ)) - ((x : ℂ) - (x₀ : ℂ))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖(x : ℂ) - (x₀ : ℂ)‖ < ρ / 2 := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    linarith
  have h := norm_scIntegrand_le_of_far hk₀ (ζ := (x : ℂ)) i (half_pos hρ) hfar'
  rwa [← ofReal_sub, norm_real, Real.norm_eq_abs] at h

theorem intervalIntegrable_scIntegrand_ofReal {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => scIntegrand k x) volume a b :=
  MeasureTheory.IntegrableOn.intervalIntegrable
    (MeasureTheory.LocallyIntegrable.integrableOn_isCompact
      (locallyIntegrable_scIntegrand_ofReal hk₀ hk₁) isCompact_uIcc)

theorem intervalIntegrable_scDensity {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (a b : ℝ) :
    IntervalIntegrable (scDensity k) volume a b := by
  refine ((intervalIntegrable_scIntegrand_ofReal hk₀ hk₁ a b).norm).congr_ae ?_
  exact Filter.Eventually.of_forall fun x => norm_scIntegrand_ofReal hk₀ hk₁ x

/-- A closed interval free of prevertices keeps a uniform distance from them. -/
theorem exists_dist_prevertices_Icc {k : ℝ} {y x : ℝ} (hno : ∀ j, scPrevertex k j ∉ Icc y x) :
    ∃ c > 0, ∀ j, ∀ s ∈ Icc y x, c ≤ |s - scPrevertex k j| := by
  have hev : ∀ j : Fin 4, ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ s ∈ Icc y x, c ≤ |s - scPrevertex k j| := by
    intro j
    have hj := hno j
    rw [mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with hj | hj
    · filter_upwards [nhdsWithin_le_nhds (eventually_le_nhds (sub_pos.2 hj))] with c hc s hs
      rw [abs_of_pos (by linarith [hs.1])]
      linarith [hs.1]
    · filter_upwards [nhdsWithin_le_nhds (eventually_le_nhds (sub_pos.2 hj))] with c hc s hs
      rw [abs_of_neg (by linarith [hs.2])]
      linarith [hs.2]
  obtain ⟨c, hc, hcpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  exact ⟨c, hcpos, hc⟩

/-- Along a real interval free of prevertices, `F(x) - F(y) = ∫_y^x g_k` (limit of the horizontal
integrals at height `ε → 0⁺`). -/
theorem scMap_ofReal_sub_of_noPrevertex {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {y x : ℝ}
    (hyx : y ≤ x) (hno : ∀ j, scPrevertex k j ∉ Icc y x) :
    scMap k x - scMap k y = ∫ s in y..x, scIntegrand k s := by
  obtain ⟨c, hc, hcle⟩ := exists_dist_prevertices_Icc hno
  obtain ⟨ĝ, hĝd, hĝeq⟩ := exists_scIntegrand_slitExt hk₀ hk₁
  have hFTC : ∀ ε : ℝ, 0 < ε → scMap k (x + ε * I) - scMap k (y + ε * I) =
      ∫ s in y..x, scIntegrand k (s + ε * I) := by
    intro ε hε
    have hmem : ∀ s : ℝ, (s : ℂ) + ε * I ∈ upperHalf := fun s => by
      show 0 < ((s : ℂ) + ε * I).im
      simpa using hε
    have hderiv : ∀ s ∈ uIcc y x, HasDerivAt (fun s : ℝ => scMap k (s + ε * I))
        (scIntegrand k (s + ε * I)) s := by
      intro s _
      have hp : HasDerivAt (fun s : ℝ => (s : ℂ) + ε * I) 1 s := by
        simpa using ((hasDerivAt_id (s : ℂ)).add_const ((ε : ℂ) * I)).comp_ofReal
      have h := (hasDerivAt_scMap hk₀ hk₁ (hmem s)).comp s hp
      rwa [mul_one] at h
    have hint : IntervalIntegrable (fun s : ℝ => scIntegrand k (s + ε * I)) volume y x :=
      ((differentiableOn_scIntegrand hk₀ hk₁).continuousOn.comp
        (Complex.continuous_ofReal.add continuous_const).continuousOn
        fun s _ => hmem s).intervalIntegrable
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  have hs0 : ∀ s : ℝ, Tendsto (fun ε : ℝ => (s : ℂ) + ε * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (s : ℂ)) := by
    intro s
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε => ?_⟩
    · have h : Tendsto (fun ε : ℝ => (s : ℂ) + ε * I) (𝓝 0)
          (𝓝 ((s : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · show 0 ≤ ((s : ℂ) + ε * I).im
      simpa using le_of_lt (show (0 : ℝ) < ε from hε)
  have hcont := continuousOn_scMap hk₀ hk₁
  have hL : Tendsto (fun ε : ℝ => scMap k (x + ε * I) - scMap k (y + ε * I)) (𝓝[>] 0)
      (𝓝 (scMap k x - scMap k y)) :=
    ((hcont x (by simp)).tendsto.comp (hs0 x)).sub ((hcont y (by simp)).tendsto.comp (hs0 y))
  have hR : Tendsto (fun ε : ℝ => ∫ s in y..x, scIntegrand k (s + ε * I)) (𝓝[>] 0)
      (𝓝 (∫ s in y..x, scIntegrand k s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 4) ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun ε => ((measurable_scIntegrand k).comp
        (Complex.measurable_ofReal.add_const _)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ε => ?_
      filter_upwards with s hs
      rw [uIoc_of_le hyx] at hs
      show ‖scIntegrand k ((s : ℂ) + ε * I)‖ ≤ 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 4
      have hfar : ∀ j, c ≤ ‖(s : ℂ) + ε * I - (scPrevertex k j : ℂ)‖ := fun j => by
        refine (hcle j s ⟨hs.1.le, hs.2⟩).trans ?_
        have h := abs_re_le_norm ((s : ℂ) + ε * I - (scPrevertex k j : ℂ))
        simpa using h
      have h1 := norm_scIntegrand_le_of_far hk₀ (ζ := (s : ℂ) + ε * I) 0 hc fun j _ => hfar j
      have h2 : ‖(s : ℂ) + ε * I - (scPrevertex k 0 : ℂ)‖ ^ (-(1 / 2 : ℝ)) ≤
          c ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hc (hfar 0) (by norm_num)
      have hA : 0 ≤ 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 3 := by positivity
      calc ‖scIntegrand k ((s : ℂ) + ε * I)‖
          ≤ 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 3 *
              ‖(s : ℂ) + ε * I - (scPrevertex k 0 : ℂ)‖ ^ (-(1 / 2 : ℝ)) := h1
        _ ≤ 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 3 * c ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hA
        _ = 1 / k * (c ^ (-(1 / 2 : ℝ))) ^ 4 := by ring
    · filter_upwards with s hs
      rw [uIoc_of_le hyx] at hs
      have hsI : s ∈ Icc y x := ⟨hs.1.le, hs.2⟩
      have hne : ∀ j, (s : ℂ) ≠ (scPrevertex k j : ℂ) := fun j h =>
        hno j (by rw [← ofReal_injective h]; exact hsI)
      have hslit : (s : ℂ) ∈ scSlitDomain k := by
        intro j t ht h
        have him := congrArg Complex.im h
        simp only [ofReal_im, sub_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
          mul_one, zero_sub] at him
        have ht0 : t = 0 := by linarith
        exact hne j (by rw [ht0] at h; simpa using h)
      have hcw : ContinuousWithinAt ĝ (scSlitDomain k) (s : ℂ) :=
        (hĝd _ hslit).continuousWithinAt
      have hpath : Tendsto (fun ε : ℝ => (s : ℂ) + ε * I) (𝓝[>] 0)
          (𝓝[scSlitDomain k] (s : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_nhdsWithin_iff.1 (hs0 s)).1,
          eventually_nhdsWithin_of_forall fun ε hε => ?_⟩
        intro j t ht h
        have him := congrArg Complex.im h
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, zero_add, mul_one,
          sub_im, zero_sub] at him
        linarith [show (0 : ℝ) < ε from hε]
      have hlim := hcw.tendsto.comp hpath
      rw [hĝeq s (by simp) hne] at hlim
      refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
      show ĝ ((s : ℂ) + ε * I) = scIntegrand k ((s : ℂ) + ε * I)
      refine hĝeq _ ?_ fun j h => ?_
      · simpa using le_of_lt (show (0 : ℝ) < ε from hε)
      · have him := congrArg Complex.im h
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, zero_add,
          mul_one] at him
        linarith [show (0 : ℝ) < ε from hε]
  exact tendsto_nhds_unique (hL.congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ))
    fun ε hε => hFTC ε hε)) hR

/-- Across `[u, v]` with no prevertex inside, `F(x) - F(y) = ∫_y^x g_k` for `u ≤ y ≤ x ≤ v`
(endpoints included, by continuity). -/
theorem scMap_ofReal_sub_eq_integral {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {u v : ℝ} (huv : u < v)
    (hno : ∀ j, scPrevertex k j ∉ Ioo u v) {y x : ℝ} (huy : u ≤ y) (hyx : y ≤ x) (hxv : x ≤ v) :
    scMap k x - scMap k y = ∫ s in y..x, scIntegrand k s := by
  have hint := intervalIntegrable_scIntegrand_ofReal hk₀ hk₁
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℂ, P = fun t : ℝ => scMap k (t : ℂ) - ∫ s in u..t, scIntegrand k s :=
    ⟨_, rfl⟩
  have hPc : ContinuousOn P (Icc u v) := by
    have h1 : ContinuousOn (fun t : ℝ => scMap k t) (Icc u v) :=
      (continuousOn_scMap hk₀ hk₁).comp Complex.continuous_ofReal.continuousOn fun t _ => by simp
    have h2 : ContinuousOn (fun t => ∫ s in u..t, scIntegrand k s) (Icc u v) := by
      have h := intervalIntegral.continuousOn_primitive_interval (μ := volume)
        (f := fun s : ℝ => scIntegrand k s) (a := u) (b := v)
        (by rw [uIcc_of_le huv.le]
            exact (intervalIntegrable_iff_integrableOn_Icc_of_le huv.le).1 (hint u v))
      rwa [uIcc_of_le huv.le] at h
    rw [hP]
    exact h1.sub h2
  have hstep : ∀ a b, a ∈ Ioo u v → b ∈ Ioo u v → a ≤ b → P a = P b := by
    intro a b ha hb hab
    have h := scMap_ofReal_sub_of_noPrevertex hk₀ hk₁ hab fun j hj =>
      hno j ⟨lt_of_lt_of_le ha.1 hj.1, lt_of_le_of_lt hj.2 hb.2⟩
    rw [← intervalIntegral.integral_interval_sub_left (hint u b) (hint u a)] at h
    rw [hP]
    linear_combination (-1 : ℂ) * h
  have hm : (u + v) / 2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
  have hconst : ∀ t ∈ Ioo u v, P t = P ((u + v) / 2) := fun t ht => by
    rcases le_total t ((u + v) / 2) with h | h
    · exact hstep _ _ ht hm h
    · exact (hstep _ _ hm ht h).symm
  have hall : ∀ t ∈ Icc u v, P t = P ((u + v) / 2) := by
    intro t ht
    have hcl : t ∈ closure (Ioo u v) := by rw [closure_Ioo huv.ne]; exact ht
    haveI := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto P (𝓝[Ioo u v] t) (𝓝 (P t)) :=
      ((hPc t ht).mono Ioo_subset_Icc_self).tendsto
    have h2 : Tendsto P (𝓝[Ioo u v] t) (𝓝 (P ((u + v) / 2))) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hconst s hs).symm)
    exact tendsto_nhds_unique h1 h2
  have hx := hall x ⟨huy.trans hyx, hxv⟩
  have hy := hall y ⟨huy, hyx.trans hxv⟩
  have hsub := intervalIntegral.integral_interval_sub_left (hint u x) (hint u y)
  rw [hP] at hx hy
  simp only at hx hy
  linear_combination hx - hy + hsub

/-- A prevertex outside `[u, v]`'s interior. -/
theorem scPrevertex_notMem_Ioo {k : ℝ} (j : Fin 4) {u v : ℝ}
    (h : ∀ i : Fin 4, scPrevertex k i ≤ u ∨ v ≤ scPrevertex k i) : scPrevertex k j ∉ Ioo u v :=
  fun hj => (h j).elim (fun h' => absurd hj.1 (not_lt.2 h')) fun h' => absurd hj.2 (not_lt.2 h')

/-- On `[-1/k, -1]`, `g_k = scDensity` (both vanish at the endpoints). -/
theorem scIntegrand_ofReal_bottom {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {s : ℝ}
    (hs : s ∈ Icc (-1 / k) (-1)) : scIntegrand k s = scDensity k s := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, show ((-1 / k : ℝ) : ℂ) = ((scPrevertex k 0 : ℝ) : ℂ) from rfl,
      scIntegrand_prevertex, show (-1 / k : ℝ) = scPrevertex k 0 from rfl,
      scDensity_prevertex hk₀, ofReal_zero]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, show ((-1 : ℝ) : ℂ) = ((scPrevertex k 1 : ℝ) : ℂ) from rfl, scIntegrand_prevertex,
      show (-1 : ℝ) = scPrevertex k 1 from rfl, scDensity_prevertex hk₀, ofReal_zero]
  have hx : ∀ j, s ≠ scPrevertex k j := by
    intro j
    fin_cases j
    · exact ne_of_gt h0
    · exact ne_of_lt h1
    · exact ne_of_lt (show s < 1 by linarith)
    · exact ne_of_lt (show s < 1 / k by linarith)
  rw [scIntegrand_ofReal hk₀ hk₁ hx,
    if_neg (show ¬ (s < -1 / k ∨ 1 / k < s) from
      not_or.2 ⟨not_lt.2 h0.le, not_lt.2 (by linarith)⟩), if_pos h1, one_mul]
  rfl

/-- On `[-1, 1]`, `g_k = i · scDensity`. -/
theorem scIntegrand_ofReal_right {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {s : ℝ}
    (hs : s ∈ Icc (-1) 1) : scIntegrand k s = I * scDensity k s := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, show ((-1 : ℝ) : ℂ) = ((scPrevertex k 1 : ℝ) : ℂ) from rfl, scIntegrand_prevertex,
      show (-1 : ℝ) = scPrevertex k 1 from rfl, scDensity_prevertex hk₀, ofReal_zero, mul_zero]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, show ((1 : ℝ) : ℂ) = ((scPrevertex k 2 : ℝ) : ℂ) from rfl, scIntegrand_prevertex,
      show (1 : ℝ) = scPrevertex k 2 from rfl, scDensity_prevertex hk₀, ofReal_zero, mul_zero]
  have hx : ∀ j, s ≠ scPrevertex k j := by
    intro j
    fin_cases j
    · exact ne_of_gt (show -1 / k < s by linarith)
    · exact ne_of_gt h0
    · exact ne_of_lt h1
    · exact ne_of_lt (show s < 1 / k by linarith)
  rw [scIntegrand_ofReal hk₀ hk₁ hx,
    if_neg (show ¬ (s < -1 / k ∨ 1 / k < s) from
      not_or.2 ⟨not_lt.2 (by linarith), not_lt.2 (by linarith)⟩),
    if_neg (show ¬ (s < -1) from not_lt.2 h0.le), if_pos h1]
  rfl

/-- On `[1, 1/k]`, `g_k = -scDensity`. -/
theorem scIntegrand_ofReal_top {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {s : ℝ}
    (hs : s ∈ Icc 1 (1 / k)) : scIntegrand k s = -scDensity k s := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, show ((1 : ℝ) : ℂ) = ((scPrevertex k 2 : ℝ) : ℂ) from rfl, scIntegrand_prevertex,
      show (1 : ℝ) = scPrevertex k 2 from rfl, scDensity_prevertex hk₀, ofReal_zero, neg_zero]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, show ((1 / k : ℝ) : ℂ) = ((scPrevertex k 3 : ℝ) : ℂ) from rfl, scIntegrand_prevertex,
      show (1 / k : ℝ) = scPrevertex k 3 from rfl, scDensity_prevertex hk₀, ofReal_zero, neg_zero]
  have hx : ∀ j, s ≠ scPrevertex k j := by
    intro j
    fin_cases j
    · exact ne_of_gt (show -1 / k < s by linarith)
    · exact ne_of_gt (show (-1 : ℝ) < s by linarith)
    · exact ne_of_gt h0
    · exact ne_of_lt h1
  rw [scIntegrand_ofReal hk₀ hk₁ hx,
    if_neg (show ¬ (s < -1 / k ∨ 1 / k < s) from
      not_or.2 ⟨not_lt.2 (by linarith), not_lt.2 h1.le⟩),
    if_neg (show ¬ (s < -1) from not_lt.2 (by linarith)),
    if_neg (show ¬ (s < 1) from not_lt.2 h0.le), neg_one_mul]
  rfl

theorem scSideA_eq_integral_scDensity {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k = ∫ s in (1 : ℝ)..(1 / k), scDensity k s := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  unfold scSideA
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le h1k.le] at hs
  have hs0 : 0 < s := by linarith [hs.1]
  have hks : k * s ≤ 1 := by
    have h := hs.2
    rw [le_div_iff₀ hk₀] at h
    linarith
  have hA : 1 - s ^ 2 ≤ 0 := by nlinarith [hs.1]
  have hB : 0 ≤ 1 - k ^ 2 * s ^ 2 := by
    nlinarith [mul_nonneg (mul_pos hk₀ hs0).le (sub_nonneg.2 hks)]
  show 1 / Real.sqrt ((s ^ 2 - 1) * (1 - k ^ 2 * s ^ 2)) = scDensity k s
  unfold scDensity
  rw [abs_of_nonpos (by nlinarith : (1 - s ^ 2) * (1 - k ^ 2 * s ^ 2) ≤ 0)]
  congr 2
  ring

theorem scSideB_eq_integral_scDensity {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideB k = ∫ s in (-1 : ℝ)..1, scDensity k s := by
  unfold scSideB
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by norm_num)] at hs
  have hA : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hk2 : k ^ 2 ≤ 1 := by nlinarith
  have hB : 0 ≤ 1 - k ^ 2 * s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg s)]
  show 1 / Real.sqrt ((1 - s ^ 2) * (1 - k ^ 2 * s ^ 2)) = scDensity k s
  unfold scDensity
  rw [abs_of_nonneg (mul_nonneg hA hB)]

theorem integral_scDensity_bottom (k : ℝ) :
    ∫ s in (-1 / k)..(-1), scDensity k s = ∫ s in (1 : ℝ)..(1 / k), scDensity k s := by
  have h := intervalIntegral.integral_comp_neg (a := (1 : ℝ)) (b := 1 / k) (f := scDensity k)
  simp only [scDensity_neg] at h
  rw [h, neg_div]

/-- `F` along the bottom side: `F(x) = ∫_{-1/k}^x scDensity` on `[-1/k, -1]`. -/
theorem scMap_ofReal_bottom {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ}
    (hx : x ∈ Icc (-1 / k) (-1)) :
    scMap k x = ((∫ s in (-1 / k)..x, scDensity k s : ℝ) : ℂ) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hlt : -1 / k < -1 := by rw [show -1 / k = -(1 / k) by ring]; linarith
  have h0 : scMap k ((-1 / k : ℝ) : ℂ) = 0 := by
    show scMap k (scPrevertex k 0 : ℂ) = 0
    unfold scMap
    exact sub_self _
  have hsep : ∀ i : Fin 4, scPrevertex k i ≤ -1 / k ∨ -1 ≤ scPrevertex k i := by
    intro i
    fin_cases i
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
    · exact Or.inr (show (-1 : ℝ) ≤ 1 by norm_num)
    · exact Or.inr (show (-1 : ℝ) ≤ 1 / k by linarith)
  have h := scMap_ofReal_sub_eq_integral hk₀ hk₁ hlt (fun j => scPrevertex_notMem_Ioo j hsep)
    le_rfl hx.1 hx.2
  rw [h0, sub_zero] at h
  rw [h, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hx.1] at hs
  exact scIntegrand_ofReal_bottom hk₀ hk₁ ⟨hs.1, hs.2.trans hx.2⟩

/-- `F` along the right side: `F(x) = a + i ∫_{-1}^x scDensity` on `[-1, 1]`. -/
theorem scMap_ofReal_right {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    scMap k x = scSideA k + I * ((∫ s in (-1 : ℝ)..x, scDensity k s : ℝ) : ℂ) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hm1 : scMap k ((-1 : ℝ) : ℂ) = scSideA k := by
    rw [scMap_ofReal_bottom hk₀ hk₁ ⟨by rw [show -1 / k = -(1 / k) by ring]; linarith, le_rfl⟩,
      integral_scDensity_bottom, ← scSideA_eq_integral_scDensity hk₀ hk₁]
  have hsep : ∀ i : Fin 4, scPrevertex k i ≤ -1 ∨ 1 ≤ scPrevertex k i := by
    intro i
    fin_cases i
    · exact Or.inl (show -1 / k ≤ -1 by rw [show -1 / k = -(1 / k) by ring]; linarith)
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
    · exact Or.inr (show (1 : ℝ) ≤ 1 / k by linarith)
  have h := scMap_ofReal_sub_eq_integral hk₀ hk₁ (u := -1) (v := 1) (by norm_num)
    (fun j => scPrevertex_notMem_Ioo j hsep) le_rfl hx.1 hx.2
  rw [hm1] at h
  have hI : (∫ s in (-1 : ℝ)..x, scIntegrand k s) =
      I * ((∫ s in (-1 : ℝ)..x, scDensity k s : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.1] at hs
    exact scIntegrand_ofReal_right hk₀ hk₁ ⟨hs.1, hs.2.trans hx.2⟩
  rw [hI] at h
  linear_combination h

/-- `F` along the top side: `F(x) = a + bi - ∫_1^x scDensity` on `[1, 1/k]`. -/
theorem scMap_ofReal_top {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ} (hx : x ∈ Icc 1 (1 / k)) :
    scMap k x = scSideA k + scSideB k * I - ((∫ s in (1 : ℝ)..x, scDensity k s : ℝ) : ℂ) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have h1 : scMap k ((1 : ℝ) : ℂ) = scSideA k + scSideB k * I := by
    rw [scMap_ofReal_right hk₀ hk₁ ⟨by norm_num, le_rfl⟩, ← scSideB_eq_integral_scDensity hk₀ hk₁]
    ring
  have hsep : ∀ i : Fin 4, scPrevertex k i ≤ 1 ∨ 1 / k ≤ scPrevertex k i := by
    intro i
    fin_cases i
    · exact Or.inl (show -1 / k ≤ 1 by rw [show -1 / k = -(1 / k) by ring]; linarith)
    · exact Or.inl (show (-1 : ℝ) ≤ 1 by norm_num)
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
  have h := scMap_ofReal_sub_eq_integral hk₀ hk₁ (u := 1) (v := 1 / k) h1k
    (fun j => scPrevertex_notMem_Ioo j hsep) le_rfl hx.1 hx.2
  rw [h1] at h
  have hI : (∫ s in (1 : ℝ)..x, scIntegrand k s) =
      -((∫ s in (1 : ℝ)..x, scDensity k s : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.1] at hs
    exact scIntegrand_ofReal_top hk₀ hk₁ ⟨hs.1, hs.2.trans hx.2⟩
  rw [hI] at h
  linear_combination h

theorem scSide_pos {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) : 0 < scSideA k ∧ 0 < scSideB k := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hpos : ∀ s : ℝ, (1 - s ^ 2) * (1 - k ^ 2 * s ^ 2) ≠ 0 → 0 < scDensity k s := fun s hs => by
    unfold scDensity
    exact one_div_pos.2 (Real.sqrt_pos.2 (abs_pos.2 hs))
  constructor
  · rw [scSideA_eq_integral_scDensity hk₀ hk₁]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_scDensity hk₀ hk₁ _ _) (fun s hs => hpos s ?_) h1k
    have hs0 : 0 < s := by linarith [hs.1]
    have hks : k * s < 1 := by
      have h := hs.2
      rw [lt_div_iff₀ hk₀] at h
      linarith
    have hA : 1 - s ^ 2 < 0 := by nlinarith [hs.1]
    have hB : 0 < 1 - k ^ 2 * s ^ 2 := by
      nlinarith [mul_pos (mul_pos hk₀ hs0) (sub_pos.2 hks)]
    exact (mul_neg_of_neg_of_pos hA hB).ne
  · rw [scSideB_eq_integral_scDensity hk₀ hk₁]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_scDensity hk₀ hk₁ _ _) (fun s hs => hpos s ?_) (by norm_num)
    have hA : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hk2 : k ^ 2 < 1 := by nlinarith
    have hB : 0 < 1 - k ^ 2 * s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hk2.le (sq_nonneg s)]
    exact (mul_pos hA hB).ne'

theorem scMap_prevertices {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scMap k (scPrevertex k 0) = 0 ∧ scMap k (scPrevertex k 1) = scSideA k ∧
      scMap k (scPrevertex k 2) = scSideA k + scSideB k * I ∧
      scMap k (scPrevertex k 3) = scSideB k * I := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold scMap
    exact sub_self _
  · show scMap k ((-1 : ℝ) : ℂ) = scSideA k
    rw [scMap_ofReal_right hk₀ hk₁ ⟨le_rfl, by norm_num⟩, intervalIntegral.integral_same]
    simp
  · show scMap k ((1 : ℝ) : ℂ) = scSideA k + scSideB k * I
    rw [scMap_ofReal_right hk₀ hk₁ ⟨by norm_num, le_rfl⟩, ← scSideB_eq_integral_scDensity hk₀ hk₁]
    ring
  · show scMap k ((1 / k : ℝ) : ℂ) = scSideB k * I
    rw [scMap_ofReal_top hk₀ hk₁ ⟨h1k.le, le_rfl⟩, ← scSideA_eq_integral_scDensity hk₀ hk₁]
    ring

/-! ### Stage 5 helpers (B): the boundary map along `ℝ ∪ {∞}` -/

theorem scDensity_nonneg (k x : ℝ) : 0 ≤ scDensity k x := by
  unfold scDensity
  positivity

/-- `∫_y^x scDensity > 0` across an interval free of prevertices. -/
theorem integral_scDensity_pos {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {y x : ℝ} (hyx : y < x)
    (hno : ∀ j, scPrevertex k j ∉ Ioo y x) : 0 < ∫ s in y..x, scDensity k s := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_scDensity hk₀ hk₁ _ _) (fun s hs => ?_) hyx
  have hne : ∀ j, s ≠ scPrevertex k j := fun j h => hno j (h ▸ hs)
  have hpoly : (1 - s ^ 2) * (1 - k ^ 2 * s ^ 2) = k ^ 2 * ((s - scPrevertex k 0) *
      (s - scPrevertex k 1) * (s - scPrevertex k 2) * (s - scPrevertex k 3)) := by
    rw [scPrevertex_zero, scPrevertex_one, scPrevertex_two, scPrevertex_three]
    field_simp
    ring
  unfold scDensity
  refine one_div_pos.2 (Real.sqrt_pos.2 (abs_pos.2 ?_))
  rw [hpoly]
  exact mul_ne_zero (pow_ne_zero 2 hk₀.ne') (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.2 (hne 0)) (sub_ne_zero.2 (hne 1))) (sub_ne_zero.2 (hne 2))) (sub_ne_zero.2 (hne 3)))

/-- The primitives of `scDensity` are strictly increasing across intervals free of prevertices. -/
theorem integral_scDensity_strictMonoOn {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {u v : ℝ}
    (hno : ∀ j, scPrevertex k j ∉ Ioo u v) (c : ℝ) :
    StrictMonoOn (fun x => ∫ s in c..x, scDensity k s) (Icc u v) := by
  intro y hy x hx hyx
  have h := intervalIntegral.integral_interval_sub_left (intervalIntegrable_scDensity hk₀ hk₁ c x)
    (intervalIntegrable_scDensity hk₀ hk₁ c y)
  have hpos := integral_scDensity_pos hk₀ hk₁ hyx fun j hj =>
    hno j ⟨lt_of_le_of_lt hy.1 hj.1, lt_of_lt_of_le hj.2 hx.2⟩
  simp only
  linarith

theorem integral_scDensity_neg_one_zero {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∫ s in (-1 : ℝ)..0, scDensity k s = scSideB k / 2 := by
  have hsym : ∫ s in (-1 : ℝ)..0, scDensity k s = ∫ s in (0 : ℝ)..1, scDensity k s := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (f := scDensity k)
    simp only [scDensity_neg, neg_zero] at h
    exact h.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_scDensity hk₀ hk₁ (-1) 0) (intervalIntegrable_scDensity hk₀ hk₁ 0 1)
  rw [scSideB_eq_integral_scDensity hk₀ hk₁, ← hadd, ← hsym]
  ring

/-- The inversion identity with its constants: `F(z) + F(-1/(kz)) = a + bi`. -/
theorem scMap_add_inversion {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {z : ℂ} (hz : 0 ≤ z.im)
    (hz0 : z ≠ 0) : scMap k z + scMap k (-1 / ((k : ℂ) * z)) = scSideA k + scSideB k * I := by
  obtain ⟨ε, c, -, hinv⟩ := scMap_inversion hk₀ hk₁
  obtain ⟨h0, hA, hAB, hB⟩ := scMap_prevertices hk₀ hk₁
  have hb := (scSide_pos hk₀ hk₁).2
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
  have e1 := hinv (-1) (by simp) (by norm_num)
  have e2 := hinv 1 (by simp) one_ne_zero
  have hM1 : -1 / ((k : ℂ) * -1) = ((scPrevertex k 3 : ℝ) : ℂ) := by
    rw [scPrevertex_three]
    push_cast
    field_simp
  have hM2 : -1 / ((k : ℂ) * 1) = ((scPrevertex k 0 : ℝ) : ℂ) := by
    rw [scPrevertex_zero]
    push_cast
    ring
  have hm1 : scMap k (-1) = scMap k ((scPrevertex k 1 : ℝ) : ℂ) := by
    rw [scPrevertex_one]
    push_cast
    rfl
  have hp1 : scMap k 1 = scMap k ((scPrevertex k 2 : ℝ) : ℂ) := by
    rw [scPrevertex_two]
    push_cast
    rfl
  rw [hM1, hm1, hB, hA] at e1
  rw [hM2, hp1, h0, hAB] at e2
  have hε : (1 + ε) * ((scSideB k : ℂ) * I) = 0 := by linear_combination e1 - e2
  have hbI : (scSideB k : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 hb.ne') I_ne_zero
  have hε' : ε = -1 := by
    have := (mul_eq_zero.1 hε).resolve_right hbI
    linear_combination this
  rw [hε'] at e1
  have hc : c = scSideA k + scSideB k * I := by linear_combination (-1 : ℂ) * e1
  rw [hinv z hz hz0, hε', hc]
  ring

/-- `F(∞) = bi/2`. -/
theorem scMapInfty_eq {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scMapInfty k = scSideB k / 2 * I := by
  have hF0 : scMap k ((0 : ℝ) : ℂ) = scSideA k + scSideB k / 2 * I := by
    rw [scMap_ofReal_right hk₀ hk₁ ⟨by norm_num, by norm_num⟩,
      integral_scDensity_neg_one_zero hk₀ hk₁]
    push_cast
    ring
  have hM : Tendsto (fun x : ℝ => (((-1 / (k * x) : ℝ)) : ℂ)) atTop
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((0 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun x =>
      show (0 : ℝ) ≤ (((-1 / (k * x) : ℝ)) : ℂ).im by rw [ofReal_im]⟩
    have h : Tendsto (fun x : ℝ => -1 / (k * x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hk₀)
    exact (Complex.continuous_ofReal.tendsto 0).comp h
  have hc0 := ((continuousOn_scMap hk₀ hk₁ _ (by simp)).tendsto.comp hM)
  have hlim : Tendsto (fun x : ℝ => scMap k x) atTop (𝓝 (scSideB k / 2 * I)) := by
    have h := (tendsto_const_nhds (x := (scSideA k : ℂ) + scSideB k * I)).sub hc0
    rw [hF0, show (scSideA k : ℂ) + scSideB k * I - (scSideA k + scSideB k / 2 * I) =
      scSideB k / 2 * I by ring] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hsum := scMap_add_inversion hk₀ hk₁ (z := (x : ℂ)) (by simp) (ofReal_ne_zero.2 hx.ne')
    have hcast : -1 / ((k : ℂ) * (x : ℂ)) = ((-1 / (k * x) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast] at hsum
    simp only [Function.comp_apply]
    linear_combination (-1 : ℂ) * hsum
  exact hlim.limUnder_eq

/-- `F` on the rays `|x| ≥ 1/k`: `F(x) = (b - ∫_{-1}^{-1/(kx)} scDensity) i`. -/
theorem scMap_ofReal_ray {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ} (hx : 1 / k ≤ |x|) :
    -1 / (k * x) ∈ Icc (-1 : ℝ) 1 ∧ -1 / (k * x) ≠ 0 ∧
      scMap k x = (scSideB k - ((∫ s in (-1 : ℝ)..(-1 / (k * x)), scDensity k s : ℝ) : ℂ)) * I := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    linarith
  have hkx : 1 ≤ k * |x| := by
    have h := (div_le_iff₀ hk₀).1 hx
    linarith [mul_comm |x| k]
  have hy : -1 / (k * x) ∈ Icc (-1 : ℝ) 1 := by
    have habs : |-1 / (k * x)| ≤ 1 := by
      rw [abs_div, abs_neg, abs_one, abs_mul, abs_of_pos hk₀,
        div_le_one (mul_pos hk₀ (abs_pos.2 hx0))]
      exact hkx
    exact abs_le.1 habs
  have hy0 : -1 / (k * x) ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero hk₀.ne' hx0)
  refine ⟨hy, hy0, ?_⟩
  have hsum := scMap_add_inversion hk₀ hk₁ (z := (x : ℂ)) (by simp) (ofReal_ne_zero.2 hx0)
  have hcast : -1 / ((k : ℂ) * (x : ℂ)) = ((-1 / (k * x) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, scMap_ofReal_right hk₀ hk₁ hy] at hsum
  linear_combination hsum

theorem scNoPrevertex_bottom {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∀ j, scPrevertex k j ∉ Ioo (-1 / k) (-1) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  refine fun j => scPrevertex_notMem_Ioo j fun i => ?_
  fin_cases i
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inr (show (-1 : ℝ) ≤ 1 by norm_num)
  · exact Or.inr (show (-1 : ℝ) ≤ 1 / k by linarith)

theorem scNoPrevertex_right {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∀ j, scPrevertex k j ∉ Ioo (-1) 1 := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  refine fun j => scPrevertex_notMem_Ioo j fun i => ?_
  fin_cases i
  · exact Or.inl (show -1 / k ≤ -1 by rw [show -1 / k = -(1 / k) by ring]; linarith)
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inr (show (1 : ℝ) ≤ 1 / k by linarith)

theorem scNoPrevertex_top {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∀ j, scPrevertex k j ∉ Ioo 1 (1 / k) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  refine fun j => scPrevertex_notMem_Ioo j fun i => ?_
  fin_cases i
  · exact Or.inl (show -1 / k ≤ 1 by rw [show -1 / k = -(1 / k) by ring]; linarith)
  · exact Or.inl (show (-1 : ℝ) ≤ 1 by norm_num)
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl

/-- `x ↦ -1/(kx)` increases on each half-line. -/
theorem neg_one_div_mul_lt {k : ℝ} (hk₀ : 0 < k) {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (hpos : 0 < x₁ * x₂) :
    -1 / (k * x₁) < -1 / (k * x₂) := by
  have hx₁ : x₁ ≠ 0 := fun h => by simp [h] at hpos
  have hx₂ : x₂ ≠ 0 := fun h => by simp [h] at hpos
  have h : -1 / (k * x₂) - -1 / (k * x₁) = (x₂ - x₁) / (k * (x₁ * x₂)) := by
    field_simp
    ring
  have : 0 < (x₂ - x₁) / (k * (x₁ * x₂)) := div_pos (sub_pos.2 h12) (mul_pos hk₀ hpos)
  linarith

/-- The five pieces of `ℝ` and the coordinates of `F` on them. -/
theorem scMap_ofReal_piece {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (x : ℝ) :
    (x < -1 / k ∧ (scMap k x).re = 0 ∧ 0 < (scMap k x).im ∧ (scMap k x).im < scSideB k / 2) ∨
    (-1 / k ≤ x ∧ x < -1 ∧ (scMap k x).im = 0 ∧ 0 ≤ (scMap k x).re ∧
      (scMap k x).re < scSideA k) ∨
    (-1 ≤ x ∧ x < 1 ∧ (scMap k x).re = scSideA k ∧ 0 ≤ (scMap k x).im ∧
      (scMap k x).im < scSideB k) ∨
    (1 ≤ x ∧ x < 1 / k ∧ (scMap k x).im = scSideB k ∧ 0 < (scMap k x).re ∧
      (scMap k x).re ≤ scSideA k) ∨
    (1 / k ≤ x ∧ (scMap k x).re = 0 ∧ scSideB k / 2 < (scMap k x).im ∧
      (scMap k x).im ≤ scSideB k) := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  have hmono2 := integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_right hk₀ hk₁) (-1)
  have hΦ2m1 : ∫ s in (-1 : ℝ)..(-1), scDensity k s = 0 := intervalIntegral.integral_same
  have hΦ20 := integral_scDensity_neg_one_zero hk₀ hk₁
  have hΦ21 : ∫ s in (-1 : ℝ)..1, scDensity k s = scSideB k :=
    (scSideB_eq_integral_scDensity hk₀ hk₁).symm
  have hm1I : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1I : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  rcases lt_or_ge x (-1 / k) with hx | hx
  · -- the left ray
    left
    have hax : 1 / k ≤ |x| := by rw [abs_of_neg (by linarith)]; linarith
    obtain ⟨hy, hy0, hF⟩ := scMap_ofReal_ray hk₀ hk₁ hax
    have hypos : 0 < -1 / (k * x) := div_pos_of_neg_of_neg (by norm_num)
      (mul_neg_of_pos_of_neg hk₀ (by linarith))
    have hylt : -1 / (k * x) < 1 := by
      have habs : |-1 / (k * x)| < 1 := by
        rw [abs_div, abs_neg, abs_one, abs_mul, abs_of_pos hk₀,
          div_lt_one (mul_pos hk₀ (abs_pos.2 (by linarith : x ≠ 0)))]
        rw [abs_of_neg (by linarith)]
        have h := (div_lt_iff₀ hk₀).1 (show 1 / k < -x by linarith)
        linarith [mul_comm (-x) k]
      exact (abs_lt.1 habs).2
    have h1 := (hmono2.lt_iff_lt h0I hy).2 hypos
    have h2 := (hmono2.lt_iff_lt hy h1I).2 hylt
    rw [hΦ20] at h1
    rw [hΦ21] at h2
    have hre : (scMap k x).re = 0 := by rw [hF]; simp
    have him : (scMap k x).im = scSideB k - ∫ s in (-1 : ℝ)..(-1 / (k * x)), scDensity k s := by
      rw [hF]; simp
    refine ⟨hx, hre, ?_, ?_⟩ <;> rw [him] <;> linarith
  rcases lt_or_ge x (-1) with hx' | hx'
  · -- the bottom side
    right; left
    have hxI : x ∈ Icc (-1 / k) (-1) := ⟨hx, hx'.le⟩
    have hmono0 := integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_bottom hk₀ hk₁) (-1 / k)
    have hlo : (-1 / k : ℝ) ∈ Icc (-1 / k) (-1) := ⟨le_rfl, by rw [hkinv]; linarith⟩
    have hhi : (-1 : ℝ) ∈ Icc (-1 / k) (-1) := ⟨by rw [hkinv]; linarith, le_rfl⟩
    have h1 := (hmono0.le_iff_le hlo hxI).2 hx
    have h2 := (hmono0.lt_iff_lt hxI hhi).2 hx'
    rw [intervalIntegral.integral_same] at h1
    rw [integral_scDensity_bottom, ← scSideA_eq_integral_scDensity hk₀ hk₁] at h2
    have hF := scMap_ofReal_bottom hk₀ hk₁ hxI
    have hre : (scMap k x).re = ∫ s in (-1 / k)..x, scDensity k s := by rw [hF, ofReal_re]
    have him : (scMap k x).im = 0 := by rw [hF, ofReal_im]
    refine ⟨hx, hx', him, ?_, ?_⟩ <;> rw [hre] <;> linarith
  rcases lt_or_ge x 1 with hx'' | hx''
  · -- the right side
    right; right; left
    have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx', hx''.le⟩
    have h1 := (hmono2.le_iff_le hm1I hxI).2 hx'
    have h2 := (hmono2.lt_iff_lt hxI h1I).2 hx''
    rw [hΦ2m1] at h1
    rw [hΦ21] at h2
    have hF := scMap_ofReal_right hk₀ hk₁ hxI
    have hre : (scMap k x).re = scSideA k := by rw [hF]; simp
    have him : (scMap k x).im = ∫ s in (-1 : ℝ)..x, scDensity k s := by rw [hF]; simp
    refine ⟨hx', hx'', hre, ?_, ?_⟩ <;> rw [him] <;> linarith
  rcases lt_or_ge x (1 / k) with hx''' | hx'''
  · -- the top side
    right; right; right; left
    have hxI : x ∈ Icc 1 (1 / k) := ⟨hx'', hx'''.le⟩
    have hmono3 := integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_top hk₀ hk₁) 1
    have hlo : (1 : ℝ) ∈ Icc 1 (1 / k) := ⟨le_rfl, h1k.le⟩
    have hhi : (1 / k : ℝ) ∈ Icc 1 (1 / k) := ⟨h1k.le, le_rfl⟩
    have h1 := (hmono3.le_iff_le hlo hxI).2 hx''
    have h2 := (hmono3.lt_iff_lt hxI hhi).2 hx'''
    rw [intervalIntegral.integral_same] at h1
    rw [← scSideA_eq_integral_scDensity hk₀ hk₁] at h2
    have hF := scMap_ofReal_top hk₀ hk₁ hxI
    have hre : (scMap k x).re = scSideA k - ∫ s in (1 : ℝ)..x, scDensity k s := by rw [hF]; simp
    have him : (scMap k x).im = scSideB k := by rw [hF]; simp
    refine ⟨hx'', hx''', him, ?_, ?_⟩ <;> rw [hre] <;> linarith
  · -- the right ray
    right; right; right; right
    have hax : 1 / k ≤ |x| := by rw [abs_of_pos (by linarith)]; exact hx'''
    obtain ⟨hy, hy0, hF⟩ := scMap_ofReal_ray hk₀ hk₁ hax
    have hyneg : -1 / (k * x) < 0 := div_neg_of_neg_of_pos (by norm_num)
      (mul_pos hk₀ (by linarith))
    have h1 := (hmono2.le_iff_le hm1I hy).2 hy.1
    have h2 := (hmono2.lt_iff_lt hy h0I).2 hyneg
    rw [hΦ2m1] at h1
    rw [hΦ20] at h2
    have hre : (scMap k x).re = 0 := by rw [hF]; simp
    have him : (scMap k x).im = scSideB k - ∫ s in (-1 : ℝ)..(-1 / (k * x)), scDensity k s := by
      rw [hF]; simp
    refine ⟨hx''', hre, ?_, ?_⟩ <;> rw [him] <;> linarith

/-- `x ↦ F(x)` is injective on `ℝ`. -/
theorem scMap_ofReal_injective {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    Function.Injective fun x : ℝ => scMap k x := by
  have ⟨ha, hb⟩ := scSide_pos hk₀ hk₁
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  have hmono2 := integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_right hk₀ hk₁) (-1)
  -- monotonicity of the relevant coordinate on each piece
  have hE : StrictAntiOn (fun x : ℝ => (scMap k x).im) (Iic (-1 / k)) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have hneg : (-1 / k : ℝ) < 0 := by rw [hkinv]; linarith
    have hx₁neg : x₁ < 0 := lt_of_le_of_lt (mem_Iic.1 hx₁) hneg
    have hx₂neg : x₂ < 0 := lt_of_le_of_lt (mem_Iic.1 hx₂) hneg
    have hax : ∀ x : ℝ, x < 0 → x ≤ -1 / k → 1 / k ≤ |x| := fun x hx0 hx => by
      rw [abs_of_neg hx0]
      linarith
    obtain ⟨hy₁, -, hF₁⟩ := scMap_ofReal_ray hk₀ hk₁ (hax x₁ hx₁neg (mem_Iic.1 hx₁))
    obtain ⟨hy₂, -, hF₂⟩ := scMap_ofReal_ray hk₀ hk₁ (hax x₂ hx₂neg (mem_Iic.1 hx₂))
    have hlt := (hmono2.lt_iff_lt hy₁ hy₂).2
      (neg_one_div_mul_lt hk₀ h12 (mul_pos_of_neg_of_neg hx₁neg hx₂neg))
    show (scMap k x₂).im < (scMap k x₁).im
    rw [hF₁, hF₂]
    simp only [mul_im, sub_re, ofReal_re, I_im, mul_one, sub_im, ofReal_im, I_re, mul_zero,
      sub_zero, add_zero]
    linarith
  have hD : StrictAntiOn (fun x : ℝ => (scMap k x).im) (Ici (1 / k)) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have hax : ∀ x : ℝ, 1 / k ≤ x → 1 / k ≤ |x| := fun x hx => by
      rw [abs_of_pos (by linarith)]
      exact hx
    obtain ⟨hy₁, -, hF₁⟩ := scMap_ofReal_ray hk₀ hk₁ (hax x₁ hx₁)
    obtain ⟨hy₂, -, hF₂⟩ := scMap_ofReal_ray hk₀ hk₁ (hax x₂ hx₂)
    have hlt := (hmono2.lt_iff_lt hy₁ hy₂).2 (neg_one_div_mul_lt hk₀ h12
      (mul_pos (by linarith [mem_Ici.1 hx₁]) (by linarith [mem_Ici.1 hx₂])))
    simp only at hlt ⊢
    rw [hF₁, hF₂]
    simp only [mul_im, sub_re, ofReal_re, I_im, mul_one, sub_im, ofReal_im, I_re, mul_zero,
      add_zero]
    linarith
  have hA : StrictMonoOn (fun x : ℝ => (scMap k x).re) (Icc (-1 / k) (-1)) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have h := (integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_bottom hk₀ hk₁) (-1 / k))
      hx₁ hx₂ h12
    simp only at h ⊢
    rw [scMap_ofReal_bottom hk₀ hk₁ hx₁, scMap_ofReal_bottom hk₀ hk₁ hx₂]
    simpa using h
  have hB : StrictMonoOn (fun x : ℝ => (scMap k x).im) (Icc (-1) 1) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have h := hmono2 hx₁ hx₂ h12
    simp only at h ⊢
    rw [scMap_ofReal_right hk₀ hk₁ hx₁, scMap_ofReal_right hk₀ hk₁ hx₂]
    simpa using h
  have hC : StrictAntiOn (fun x : ℝ => (scMap k x).re) (Icc 1 (1 / k)) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have h := (integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_top hk₀ hk₁) 1) hx₁ hx₂ h12
    simp only at h ⊢
    rw [scMap_ofReal_top hk₀ hk₁ hx₁, scMap_ofReal_top hk₀ hk₁ hx₂]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_zero]
    linarith
  intro x₁ x₂ heq
  simp only at heq
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  rcases scMap_ofReal_piece hk₀ hk₁ x₁ with
      ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ |
      ⟨a1, a2, a3, a4⟩ <;>
    rcases scMap_ofReal_piece hk₀ hk₁ x₂ with
      ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4, b5⟩ | ⟨b1, b2, b3, b4, b5⟩ | ⟨b1, b2, b3, b4, b5⟩ |
      ⟨b1, b2, b3, b4⟩ <;>
    first
    | (exfalso; linarith)
    | exact hE.injOn (mem_Iic.2 a1.le) (mem_Iic.2 b1.le) him
    | exact hA.injOn ⟨a1, a2.le⟩ ⟨b1, b2.le⟩ hre
    | exact hB.injOn ⟨a1, a2.le⟩ ⟨b1, b2.le⟩ him
    | exact hC.injOn ⟨a1, a2.le⟩ ⟨b1, b2.le⟩ hre
    | exact hD.injOn (mem_Ici.2 a1) (mem_Ici.2 b1) him

/-- `F(x) ≠ F(∞)` for real `x`. -/
theorem scMap_ofReal_ne_infty {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (x : ℝ) :
    scMap k x ≠ scMapInfty k := by
  have ⟨ha, hb⟩ := scSide_pos hk₀ hk₁
  rw [scMapInfty_eq hk₀ hk₁]
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [mul_re, div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofNat_im, ofReal_im,
    zero_div, I_im, mul_one, sub_zero, mul_im, add_zero] at hre him
  rcases scMap_ofReal_piece hk₀ hk₁ x with
      ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ |
      ⟨a1, a2, a3, a4⟩ <;> linarith

theorem scMapExt_bijOn_frontier {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    BijOn (scMapExt k) (frontier (toExt upperHalf))
      (frontier (toExt (rectangle (scSideA k) (scSideB k)))) := by
  have ⟨ha, hb⟩ := scSide_pos hk₀ hk₁
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hkinv : -1 / k = -(1 / k) := by ring
  rw [scExt_frontier_toExt_upperHalf, scExt_frontier_toExt_rectangle,
    scExt_frontier_rectangle ha hb]
  -- real points of the frontier of `ℍ`
  have hreal : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have hinfty : scMapExt k extInf = (((scSideB k / 2 : ℝ) * I : ℂ) : ExtPlane) := by
    rw [scExt_scMapExt_infty, scMapInfty_eq hk₀ hk₁]
    push_cast
    rfl
  have hmem : ∀ x : ℝ, scMap k x ∈
      Icc 0 (scSideA k) ×ℂ {0, scSideB k} ∪ {0, scSideA k} ×ℂ Icc 0 (scSideB k) := by
    intro x
    rcases scMap_ofReal_piece hk₀ hk₁ x with
        ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ | ⟨a1, a2, a3, a4, a5⟩ |
        ⟨a1, a2, a3, a4⟩
    · exact Or.inr ⟨Or.inl a2, a3.le, by linarith⟩
    · exact Or.inl ⟨⟨a4, a5.le⟩, Or.inl a3⟩
    · exact Or.inr ⟨Or.inr a3, a4, a5.le⟩
    · exact Or.inl ⟨⟨a4.le, a5⟩, Or.inr a3⟩
    · exact Or.inr ⟨Or.inl a2, by linarith, a4⟩
  refine ⟨?_, ?_, ?_⟩
  · -- maps to
    rintro p (⟨z, hz, rfl⟩ | hp)
    · rw [scExt_scMapExt_coe, scExt_coe_mem_toExt_iff, hreal z hz]
      exact hmem z.re
    · rw [mem_singleton_iff.1 hp, hinfty, scExt_coe_mem_toExt_iff]
      have hre : (((scSideB k / 2 : ℝ) : ℂ) * I).re = 0 := by simp
      have him : (((scSideB k / 2 : ℝ) : ℂ) * I).im = scSideB k / 2 := by simp
      have h0' : (0 : ℝ) ≤ (((scSideB k / 2 : ℝ) : ℂ) * I).im := by rw [him]; linarith
      have hb' : (((scSideB k / 2 : ℝ) : ℂ) * I).im ≤ scSideB k := by rw [him]; linarith
      exact Or.inr ⟨Or.inl hre, h0', hb'⟩
  · -- injective
    rintro p₁ (⟨z₁, hz₁, rfl⟩ | hp₁) p₂ (⟨z₂, hz₂, rfl⟩ | hp₂) heq
    · rw [scExt_scMapExt_coe, scExt_scMapExt_coe] at heq
      have h := OnePoint.coe_injective heq
      rw [hreal z₁ hz₁, hreal z₂ hz₂] at h ⊢
      rw [scMap_ofReal_injective hk₀ hk₁ h]
    · rw [mem_singleton_iff.1 hp₂, scExt_scMapExt_coe, scExt_scMapExt_infty] at heq
      rw [hreal z₁ hz₁] at heq
      exact absurd (OnePoint.coe_injective heq) (scMap_ofReal_ne_infty hk₀ hk₁ _)
    · rw [mem_singleton_iff.1 hp₁, scExt_scMapExt_coe, scExt_scMapExt_infty] at heq
      rw [hreal z₂ hz₂] at heq
      exact absurd (OnePoint.coe_injective heq).symm (scMap_ofReal_ne_infty hk₀ hk₁ _)
    · rw [mem_singleton_iff.1 hp₁, mem_singleton_iff.1 hp₂]
  · -- surjective
    rintro w ⟨u, hu, rfl⟩
    have hcont : ∀ c d : ℝ, c ≤ d →
        ContinuousOn (fun x => ∫ s in c..x, scDensity k s) (Icc c d) := fun c d hcd => by
      have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := scDensity k)
        (a := c) (b := d) (by rw [uIcc_of_le hcd]
                              exact (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).1
                                (intervalIntegrable_scDensity hk₀ hk₁ c d))
      rwa [uIcc_of_le hcd] at h
    -- a real preimage
    have hpre : ∀ x : ℝ, scMap k x = u → (u : ExtPlane) ∈
        scMapExt k '' (toExt {z : ℂ | z.im = 0} ∪ {extInf}) := fun x hx =>
      ⟨((x : ℂ) : ExtPlane), Or.inl ⟨(x : ℂ), by simp, rfl⟩, by rw [scExt_scMapExt_coe, hx]⟩
    -- a preimage on a ray, from a parameter `y ∈ [-1, 1] ∖ {0}`
    have hray : ∀ y : ℝ, y ∈ Icc (-1 : ℝ) 1 → y ≠ 0 →
        scMap k ((-1 / (k * y) : ℝ) : ℂ) =
          (scSideB k - ((∫ s in (-1 : ℝ)..y, scDensity k s : ℝ) : ℂ)) * I := by
      intro y hy hy0
      have hax : 1 / k ≤ |-1 / (k * y)| := by
        rw [abs_div, abs_neg, abs_one, abs_mul, abs_of_pos hk₀]
        rw [div_le_div_iff₀ hk₀ (mul_pos hk₀ (abs_pos.2 hy0))]
        have : |y| ≤ 1 := abs_le.2 hy
        nlinarith
      obtain ⟨-, -, hF⟩ := scMap_ofReal_ray hk₀ hk₁ hax
      have hinv : -1 / (k * (-1 / (k * y))) = y := by
        field_simp
      rwa [hinv] at hF
    rcases hu with ⟨⟨hre0, hrea⟩, him⟩ | ⟨hre, him0, himb⟩
    · rcases him with him | him
      · -- the bottom side
        have hIVT := intermediate_value_Icc (show (-1 / k : ℝ) ≤ -1 by rw [hkinv]; linarith)
          (hcont (-1 / k) (-1) (by rw [hkinv]; linarith))
        simp only [intervalIntegral.integral_same] at hIVT
        rw [integral_scDensity_bottom, ← scSideA_eq_integral_scDensity hk₀ hk₁] at hIVT
        obtain ⟨x, hx, hxv⟩ := hIVT ⟨hre0, hrea⟩
        refine hpre x ?_
        rw [scMap_ofReal_bottom hk₀ hk₁ hx]
        simp only at hxv
        apply Complex.ext <;> simp [hxv, him]
      · -- the top side
        have hIVT := intermediate_value_Icc h1k.le (hcont 1 (1 / k) h1k.le)
        simp only [intervalIntegral.integral_same] at hIVT
        rw [← scSideA_eq_integral_scDensity hk₀ hk₁] at hIVT
        obtain ⟨x, hx, hxv⟩ := hIVT
          (show scSideA k - u.re ∈ Icc 0 (scSideA k) from ⟨by linarith, by linarith⟩)
        refine hpre x ?_
        rw [scMap_ofReal_top hk₀ hk₁ hx]
        simp only at hxv
        apply Complex.ext <;> simp [hxv, mem_singleton_iff.1 him]
    · rcases hre with hre | hre
      · -- the left side
        rcases lt_trichotomy u.im (scSideB k / 2) with hlt | heq | hgt
        · have hIVT := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) (hcont (-1) 1
            (by norm_num) |>.mono (Icc_subset_Icc (by norm_num) le_rfl))
          rw [integral_scDensity_neg_one_zero hk₀ hk₁,
            ← scSideB_eq_integral_scDensity hk₀ hk₁] at hIVT
          obtain ⟨y, hy, hyv⟩ := hIVT
            (show scSideB k - u.im ∈ Icc (scSideB k / 2) (scSideB k) from
              ⟨by linarith, by linarith⟩)
          have hy0 : y ≠ 0 := by
            rintro rfl
            simp only [integral_scDensity_neg_one_zero hk₀ hk₁] at hyv
            linarith
          refine hpre (-1 / (k * y)) ?_
          rw [hray y ⟨by linarith [hy.1], hy.2⟩ hy0]
          simp only at hyv
          apply Complex.ext <;> simp [hyv, hre]
        · refine ⟨extInf, Or.inr rfl, ?_⟩
          rw [hinfty]
          congr 1
          apply Complex.ext <;> simp [heq, hre]
        · have hIVT := intermediate_value_Icc (show (-1 : ℝ) ≤ 0 by norm_num) (hcont (-1) 1
            (by norm_num) |>.mono (Icc_subset_Icc le_rfl (by norm_num)))
          simp only [intervalIntegral.integral_same] at hIVT
          rw [integral_scDensity_neg_one_zero hk₀ hk₁] at hIVT
          obtain ⟨y, hy, hyv⟩ := hIVT
            (show scSideB k - u.im ∈ Icc 0 (scSideB k / 2) from ⟨by linarith, by linarith⟩)
          have hy0 : y ≠ 0 := by
            rintro rfl
            simp only [integral_scDensity_neg_one_zero hk₀ hk₁] at hyv
            linarith
          refine hpre (-1 / (k * y)) ?_
          rw [hray y ⟨hy.1, by linarith [hy.2]⟩ hy0]
          simp only at hyv
          apply Complex.ext <;> simp [hyv, hre]
      · -- the right side
        have hIVT := intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
          (hcont (-1) 1 (by norm_num))
        simp only [intervalIntegral.integral_same] at hIVT
        rw [← scSideB_eq_integral_scDensity hk₀ hk₁] at hIVT
        obtain ⟨x, hx, hxv⟩ := hIVT ⟨him0, himb⟩
        refine hpre x ?_
        rw [scMap_ofReal_right hk₀ hk₁ hx]
        simp only at hxv
        apply Complex.ext <;> simp [hxv, mem_singleton_iff.1 hre]

/-! ### Stage 6: `F(ℍ) ⊆ R` -/

/-- `F` is bounded on the closed half-plane: it is continuous there (Stage 3) and has a limit at
`∞` (Stage 4). -/
theorem scMap_bounded_of_closure {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖scMap k z‖ ≤ C := by
  have hc : ContinuousOn (scMap k) {z : ℂ | 0 ≤ z.im} := continuousOn_scMap hk₀ hk₁
  -- near `∞`: within distance `1` of the limit
  have hinf := Metric.tendsto_nhds.1 (tendsto_scMap_cobounded hk₀ hk₁) 1 one_pos
  rw [eventually_inf_principal,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff] at hinf
  obtain ⟨R, -, hR⟩ := hinf
  -- on the compact part `closedBall 0 R ∩ {0 ≤ im}`: a continuous image of a compact set
  have hK : IsCompact (closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}) :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_im)
  obtain ⟨C₂, hC₂⟩ := isBounded_iff_forall_norm_le.1
    (hK.image_of_continuousOn (hc.mono inter_subset_right)).isBounded
  refine ⟨max C₂ (‖scMapInfty k‖ + 1), fun z hz => ?_⟩
  by_cases hzR : z ∈ closedBall (0 : ℂ) R
  · exact (hC₂ _ ⟨z, ⟨hzR, hz⟩, rfl⟩).trans (le_max_left _ _)
  · have h1 := hR hzR hz
    rw [dist_eq_norm] at h1
    refine le_trans ?_ (le_max_right _ _)
    calc ‖scMap k z‖ = ‖(scMap k z - scMapInfty k) + scMapInfty k‖ := by rw [sub_add_cancel]
      _ ≤ ‖scMap k z - scMapInfty k‖ + ‖scMapInfty k‖ := norm_add_le _ _
      _ ≤ ‖scMapInfty k‖ + 1 := by linarith

/-- On the real axis `F` takes values in the closed rectangle (Stage 5). -/
theorem scMap_ofReal_mem_Icc {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (x : ℝ) :
    scMap k x ∈ Icc 0 (scSideA k) ×ℂ Icc 0 (scSideB k) := by
  have h1 : scMapExt k ((x : ℂ) : ExtPlane) ∈
      frontier (toExt (rectangle (scSideA k) (scSideB k))) :=
    (scMapExt_bijOn_frontier hk₀ hk₁).mapsTo (scExt_ofReal_mem_frontier_toExt_upperHalf x)
  rw [scExt_frontier_toExt_rectangle, scExt_scMapExt_coe, scExt_coe_mem_toExt_iff] at h1
  have h2 := frontier_subset_closure h1
  rw [scExt_rectangle_eq, closure_reProdIm, mem_reProdIm] at h2
  rw [mem_reProdIm]
  exact ⟨closure_minimal Ioo_subset_Icc_self isClosed_Icc h2.1,
    closure_minimal Ioo_subset_Icc_self isClosed_Icc h2.2⟩

/-- **Phragmén–Lindelöf for the upper half-plane, bounded case.**  If `F` is holomorphic on `ℍ`,
continuous and bounded on the closed half-plane, and `Re F ≤ M` on `ℝ`, then `Re F ≤ M` on `ℍ`
(Mathlib's right-half-plane principle `PhragmenLindelof.right_half_plane_of_bounded_on_real`
applied to `w ↦ exp (F (i w))`). -/
theorem scExt_re_le_of_le_on_real {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F upperHalf)
    (hc : ContinuousOn F {z : ℂ | 0 ≤ z.im}) (hb : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ C)
    {M : ℝ} (hM : ∀ x : ℝ, (F x).re ≤ M) {z : ℂ} (hz : z ∈ upperHalf) : (F z).re ≤ M := by
  obtain ⟨C, hC⟩ := hb
  have hIw : ∀ w : ℂ, (I * w).im = w.re := fun w => by simp
  have hbound : ∀ w : ℂ, 0 ≤ w.re → ‖exp (F (I * w))‖ ≤ Real.exp C := fun w hw => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hC _ (by rw [hIw]; exact hw)))
  have hlin : Differentiable ℂ fun w : ℂ => I * w := differentiable_id.const_mul I
  have hmaps : MapsTo (fun w : ℂ => I * w) {w : ℂ | 0 < w.re} upperHalf := fun w hw => by
    show 0 < (I * w).im
    rw [hIw]
    exact hw
  have hmaps' : MapsTo (fun w : ℂ => I * w) {w : ℂ | 0 ≤ w.re} {z : ℂ | 0 ≤ z.im} :=
    fun w hw => by
      show 0 ≤ (I * w).im
      rw [hIw]
      exact hw
  have hGd : DiffContOnCl ℂ (fun w => exp (F (I * w))) {w : ℂ | 0 < w.re} := by
    refine ⟨(hd.comp hlin.differentiableOn hmaps).cexp, ?_⟩
    refine ((hc.comp hlin.continuous.continuousOn hmaps').cexp).mono ?_
    exact closure_minimal (fun w (hw : 0 < w.re) => le_of_lt hw)
      (isClosed_le continuous_const continuous_re)
  have hexp : ∃ c < (2 : ℝ), ∃ B, (fun w => exp (F (I * w))) =O[Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
      fun w => Real.exp (B * ‖w‖ ^ c) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp C) ?_⟩
    rw [eventually_inf_principal]
    refine Eventually.of_forall fun w (hw : 0 < w.re) => ?_
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact hbound w hw.le
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖exp (F (I * x))‖ := by
    show ∃ b, ∀ᶠ y in map (fun x : ℝ => ‖exp (F (I * x))‖) atTop, y ≤ b
    refine ⟨Real.exp C, ?_⟩
    rw [eventually_map]
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact hbound x (by simpa using hx)
  have him : ∀ x : ℝ, ‖exp (F (I * (x * I)))‖ ≤ Real.exp M := fun x => by
    have h1 : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := by
      push_cast
      linear_combination (x : ℂ) * I_sq
    rw [h1, Complex.norm_exp]
    exact Real.exp_le_exp.2 (hM (-x))
  have hzre : 0 ≤ (-I * z).re := by
    have e : (-I * z).re = z.im := by simp
    rw [e]
    exact le_of_lt hz
  have key := PhragmenLindelof.right_half_plane_of_bounded_on_real hGd hexp hre him hzre
  have h2 : I * (-I * z) = z := by linear_combination (-z) * I_sq
  rw [h2, Complex.norm_exp] at key
  exact Real.exp_le_exp.1 key

/-- `F(ℍ)` is open: `F` is a local homeomorphism at every point of `ℍ` (inverse function
theorem, `g_k ≠ 0`). -/
theorem scMap_image_upperHalf_isOpen {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsOpen (scMap k '' upperHalf) := by
  have hd : DifferentiableOn ℂ (scMap k) upperHalf := fun w hw =>
    (hasDerivAt_scMap hk₀ hk₁ hw).differentiableAt.differentiableWithinAt
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hstrict : HasStrictDerivAt (scMap k) (scIntegrand k z) z := by
    have h := ((hd.analyticOnNhd scExt_isOpen_upperHalf) z hz).hasStrictDerivAt
    rwa [(hasDerivAt_scMap hk₀ hk₁ hz).deriv] at h
  rw [← hstrict.map_nhds_eq (scIntegrand_ne_zero hk₀ hk₁ hz), mem_map]
  exact mem_of_superset (scExt_isOpen_upperHalf.mem_nhds hz) (subset_preimage_image _ _)

theorem mapsTo_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    MapsTo (scMap k) upperHalf (rectangle (scSideA k) (scSideB k)) := by
  have hd : DifferentiableOn ℂ (scMap k) upperHalf := fun w hw =>
    (hasDerivAt_scMap hk₀ hk₁ hw).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn (scMap k) {z : ℂ | 0 ≤ z.im} := continuousOn_scMap hk₀ hk₁
  obtain ⟨C, hC⟩ := scMap_bounded_of_closure hk₀ hk₁
  have hbd : ∀ x : ℝ, (scMap k x).re ∈ Icc 0 (scSideA k) ∧ (scMap k x).im ∈ Icc 0 (scSideB k) :=
    fun x => mem_reProdIm.1 (scMap_ofReal_mem_Icc hk₀ hk₁ x)
  -- the four Phragmén–Lindelöf bounds `0 ≤ Re F ≤ a`, `0 ≤ Im F ≤ b` on `ℍ`
  have hnI : ∀ w : ℂ, ‖-I * w‖ = ‖w‖ := fun w => by rw [norm_mul, norm_neg, norm_I, one_mul]
  have hI : ∀ w : ℂ, ‖I * w‖ = ‖w‖ := fun w => by rw [norm_mul, norm_I, one_mul]
  have e1 : ∀ w : ℂ, (-I * w).re = w.im := fun w => by simp
  have e2 : ∀ w : ℂ, (I * w).re = -w.im := fun w => by simp
  have h1 : ∀ z ∈ upperHalf, (scMap k z).re ≤ scSideA k := fun z hz =>
    scExt_re_le_of_le_on_real hd hc ⟨C, hC⟩ (fun x => (hbd x).1.2) hz
  have h2 : ∀ z ∈ upperHalf, 0 ≤ (scMap k z).re := fun z hz => by
    have := scExt_re_le_of_le_on_real (F := fun w => -scMap k w) hd.neg hc.neg
      ⟨C, fun w hw => by rw [norm_neg]; exact hC w hw⟩ (M := 0)
      (fun x => by
        rw [neg_re]
        linarith [(hbd x).1.1]) hz
    rw [neg_re] at this
    linarith
  have h3 : ∀ z ∈ upperHalf, (scMap k z).im ≤ scSideB k := fun z hz => by
    have := scExt_re_le_of_le_on_real (F := fun w => -I * scMap k w) (hd.const_mul _)
      (continuousOn_const.mul hc) ⟨C, fun w hw => by rw [hnI]; exact hC w hw⟩
      (fun x => by
        rw [e1]
        exact (hbd x).2.2) hz
    rw [e1] at this
    exact this
  have h4 : ∀ z ∈ upperHalf, 0 ≤ (scMap k z).im := fun z hz => by
    have := scExt_re_le_of_le_on_real (F := fun w => I * scMap k w) (hd.const_mul _)
      (continuousOn_const.mul hc) ⟨C, fun w hw => by rw [hI]; exact hC w hw⟩ (M := 0)
      (fun x => by
        rw [e2]
        linarith [(hbd x).2.1]) hz
    rw [e2] at this
    linarith
  -- `F(ℍ)` is open and lies in the closed rectangle, hence in its interior, the open rectangle
  have hsub : scMap k '' upperHalf ⊆ Icc 0 (scSideA k) ×ℂ Icc 0 (scSideB k) := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_reProdIm.2 ⟨⟨h2 z hz, h1 z hz⟩, ⟨h4 z hz, h3 z hz⟩⟩
  have hint := interior_maximal hsub (scMap_image_upperHalf_isOpen hk₀ hk₁)
  rw [interior_reProdIm, interior_Icc, interior_Icc, ← scExt_rectangle_eq] at hint
  exact fun z hz => hint ⟨z, hz, rfl⟩

/-! ### Stage 7: properness -/

/-- Continuity of the extension on `closure (toExt ℍ) = ℍ̄ ∪ {∞}`: Stage 3 at finite points,
Stage 4 at `∞` (where `𝓝 ∞` is the push-forward of the cobounded filter). -/
theorem scMapExt_continuousOn_closure_toExt {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ContinuousOn (scMapExt k) (closure (toExt upperHalf)) := by
  rw [scExt_closure_toExt_upperHalf]
  have hpre : ((↑) : ℂ → ExtPlane) ⁻¹' (toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf}) =
      {z : ℂ | 0 ≤ z.im} := by
    ext z
    simp [scExt_coe_mem_toExt_iff]
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    show Tendsto (scMapExt k) (𝓝[toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf}] extInf)
      (𝓝 (scMapExt k extInf))
    rw [nhdsWithin, OnePoint.nhds_infty_eq, inf_sup_right, tendsto_sup,
      ← Filter.map_inf_principal_preimage, hpre, tendsto_map'_iff]
    refine ⟨?_, (tendsto_pure_nhds _ _).mono_left inf_le_left⟩
    have h := tendsto_scMap_cobounded hk₀ hk₁
    rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact] at h
    exact (OnePoint.continuous_coe.tendsto _).comp h
  | coe z =>
    have hz : 0 ≤ z.im := by
      rcases hp with h | h
      · exact scExt_coe_mem_toExt_iff.1 h
      · exact absurd h (OnePoint.coe_ne_infty z)
    show Tendsto (scMapExt k) (𝓝[toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf}] (z : ExtPlane))
      (𝓝 (scMapExt k z))
    rw [OnePoint.nhdsWithin_coe, hpre, tendsto_map'_iff]
    exact (OnePoint.continuous_coe.tendsto _).comp (continuousOn_scMap hk₀ hk₁ z hz)

/-- `F : ℍ → R` is proper: `ℂ̄` is compact, `F` extends continuously to `closure (toExt ℍ)` and
sends `∂ℍ` (real axis and `∞`) into `∂R`, which is disjoint from `R`. -/
theorem isProperMap_scMap_restrict {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsProperMap (fun z : upperHalf =>
      (⟨scMap k z, mapsTo_scMap hk₀ hk₁ z.2⟩ : rectangle (scSideA k) (scSideB k))) :=
  scExt_isProperMap_restrict scExt_isOpen_upperHalf (scExt_isOpen_rectangle _ _)
    ((continuousOn_scMap hk₀ hk₁).mono fun z hz => le_of_lt (show 0 < z.im from hz))
    (scMapExt_continuousOn_closure_toExt hk₀ hk₁) (fun _ => rfl)
    (scMapExt_bijOn_frontier hk₀ hk₁).mapsTo (mapsTo_scMap hk₀ hk₁)

theorem isClosedMap_scMap_restrict {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsClosedMap (fun z : upperHalf =>
      (⟨scMap k z, mapsTo_scMap hk₀ hk₁ z.2⟩ : rectangle (scSideA k) (scSideB k))) := by
  exact (isProperMap_scMap_restrict hk₀ hk₁).isClosedMap

/-- `F` is holomorphic on `ℍ`, hence analytic, hence strictly differentiable, with derivative
`g_k` (Stage 2). -/
theorem scMap_hasStrictDerivAt {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    HasStrictDerivAt (scMap k) (scIntegrand k z) z := by
  have hd : DifferentiableOn ℂ (scMap k) upperHalf := fun w hw =>
    (hasDerivAt_scMap hk₀ hk₁ hw).differentiableAt.differentiableWithinAt
  have h := ((hd.analyticOnNhd scExt_isOpen_upperHalf) z hz).hasStrictDerivAt
  rwa [(hasDerivAt_scMap hk₀ hk₁ hz).deriv] at h

/-- The inverse function theorem: `F` is a local homeomorphism at every point of `ℍ`
(`g_k ≠ 0` there, Stage 1). -/
theorem scMap_isLocalHomeomorphOn {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsLocalHomeomorphOn (scMap k) upperHalf := fun _ hz =>
  ⟨((scMap_hasStrictDerivAt hk₀ hk₁ hz).hasStrictFDerivAt_equiv
      (scIntegrand_ne_zero hk₀ hk₁ hz)).toOpenPartialHomeomorph _,
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _, rfl⟩

theorem finite_scMap_fiber {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (w : ℂ) :
    {z | z ∈ upperHalf ∧ scMap k z = w}.Finite := by
  by_cases hw : w ∈ rectangle (scSideA k) (scSideB k)
  · -- the fibre is compact (properness) and discrete (local injectivity), hence finite
    set g := fun z : upperHalf =>
      (⟨scMap k z, mapsTo_scMap hk₀ hk₁ z.2⟩ : rectangle (scSideA k) (scSideB k)) with hg
    have hK : IsCompact (g ⁻¹' {⟨w, hw⟩}) :=
      (isProperMap_scMap_restrict hk₀ hk₁).isCompact_preimage isCompact_singleton
    have heq : {z | z ∈ upperHalf ∧ scMap k z = w} = Subtype.val '' (g ⁻¹' {⟨w, hw⟩}) := by
      ext z
      constructor
      · rintro ⟨hz, hzw⟩
        exact ⟨⟨z, hz⟩, Subtype.ext hzw, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, congrArg Subtype.val hx⟩
    rw [heq]
    refine (hK.image continuous_subtype_val).finite ?_
    refine ((scMap_isLocalHomeomorphOn hk₀ hk₁).mono ?_).isDiscrete_of_image ?_
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · refine Set.Subsingleton.isDiscrete ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨x', hx', rfl⟩, rfl⟩
      have h1 : scMap k (x : ℂ) = w := congrArg Subtype.val hx
      have h2 : scMap k (x' : ℂ) = w := congrArg Subtype.val hx'
      rw [h1, h2]
  · refine Set.finite_empty.subset ?_
    rintro z ⟨hz, rfl⟩
    exact hw (mapsTo_scMap hk₀ hk₁ hz)

/-! ### Stage 8: covering ⇒ conformal onto (replaces LZ 6.2) -/

theorem isConformalOnto_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsConformalOnto (scMap k) upperHalf (rectangle (scSideA k) (scSideB k)) := by
  -- the restricted map `g : ℍ → R` is a proper local homeomorphism, hence a covering map
  set g := fun z : upperHalf =>
    (⟨scMap k z, mapsTo_scMap hk₀ hk₁ z.2⟩ : rectangle (scSideA k) (scSideB k)) with hg
  have hproper := isProperMap_scMap_restrict hk₀ hk₁
  have hgc : Continuous g := hproper.continuous
  have hloc : IsLocalHomeomorph g := by
    have hcomp : IsLocalHomeomorph ((Subtype.val : rectangle (scSideA k) (scSideB k) → ℂ) ∘ g) := by
      have : (Subtype.val : rectangle (scSideA k) (scSideB k) → ℂ) ∘ g =
          scMap k ∘ (Subtype.val : upperHalf → ℂ) := rfl
      rw [this, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
      exact (scMap_isLocalHomeomorphOn hk₀ hk₁).comp
        scExt_isOpen_upperHalf.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun x _ => x.2)
    exact hcomp.of_comp (scExt_isOpen_rectangle _ _).isOpenEmbedding_subtypeVal.isLocalHomeomorph
      hgc
  have hcov : IsCoveringMap g := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph (fun y _ => ?_)
      (fun e _ => ?_)
    · refine ((finite_scMap_fiber hk₀ hk₁ (y : ℂ)).preimage
        (f := (Subtype.val : upperHalf → ℂ)) Subtype.val_injective.injOn).subset ?_
      intro x hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · obtain ⟨φ, hφ, hφe⟩ := hloc e
      exact ⟨φ, hφ, hφe⟩
  -- `R` is convex, hence simply connected and locally path connected; `ℍ` is connected
  haveI : PreconnectedSpace upperHalf :=
    isPreconnected_iff_preconnectedSpace.1 scExt_convex_upperHalf.isPreconnected
  let x₀ : upperHalf := ⟨I, by simp [upperHalf]⟩
  haveI : ContractibleSpace (rectangle (scSideA k) (scSideB k)) :=
    (scExt_convex_rectangle _ _).contractibleSpace ⟨_, (g x₀).2⟩
  haveI : LocallyPathConnectedSpace (rectangle (scSideA k) (scSideB k)) :=
    (scExt_isOpen_rectangle _ _).locallyPathConnectedSpace
  -- lift the identity of `R` through the covering `g`: a continuous section `G`
  obtain ⟨G, ⟨hG0, hGg⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id _) (g x₀) x₀ rfl
  have hGg' : ∀ y, g (G y) = y := fun y => by
    have := congrFun hGg y
    simpa using this
  -- `G ∘ g = id` on the connected `ℍ` (uniqueness of lifts)
  have hgG : ∀ x, G (g x) = x := by
    have h : (G ∘ g) = (id : upperHalf → upperHalf) :=
      hcov.eq_of_comp_eq (G.continuous.comp hgc) continuous_id
        (by
          funext x
          show g (G (g x)) = g x
          rw [hGg'])
        x₀ (by
          show G (g x₀) = x₀
          exact hG0)
    exact fun x => congrFun h x
  refine ⟨fun z hz => (hasDerivAt_scMap hk₀ hk₁ hz).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro z hz w hw hzw
    have h1 : g ⟨z, hz⟩ = g ⟨w, hw⟩ := Subtype.ext hzw
    have h2 := congrArg G h1
    rw [hgG, hgG] at h2
    exact congrArg Subtype.val h2
  · refine subset_antisymm (mapsTo_scMap hk₀ hk₁).image_subset fun w hw => ?_
    exact ⟨(G ⟨w, hw⟩ : ℂ), (G ⟨w, hw⟩).2, congrArg Subtype.val (hGg' ⟨w, hw⟩)⟩

/-! ### Stage 9: homeomorphic extension to the closures -/

theorem isHomeoExtension_scMap {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsHomeoExtension (scMap k) upperHalf (rectangle (scSideA k) (scSideB k)) (scMapExt k) := by
  obtain ⟨-, hinj, himg⟩ := isConformalOnto_scMap hk₀ hk₁
  have hbij := scMapExt_bijOn_frontier hk₀ hk₁
  have hUo : IsOpen (toExt upperHalf) := scExt_isOpen_toExt scExt_isOpen_upperHalf
  have hRo : IsOpen (toExt (rectangle (scSideA k) (scSideB k))) :=
    scExt_isOpen_toExt (scExt_isOpen_rectangle _ _)
  have hcl : closure (toExt upperHalf) = toExt upperHalf ∪ frontier (toExt upperHalf) := by
    rw [closure_eq_interior_union_frontier, hUo.interior_eq]
  have hclR : closure (toExt (rectangle (scSideA k) (scSideB k))) =
      toExt (rectangle (scSideA k) (scSideB k)) ∪
        frontier (toExt (rectangle (scSideA k) (scSideB k))) := by
    rw [closure_eq_interior_union_frontier, hRo.interior_eq]
  -- the image of the open half-plane is the open rectangle
  have himg' : scMapExt k '' toExt upperHalf = toExt (rectangle (scSideA k) (scSideB k)) := by
    rw [← himg]
    unfold toExt
    rw [image_image, image_image]
    rfl
  -- interior points go to interior points, boundary points to boundary points
  have hint : ∀ z ∈ upperHalf, scMapExt k (z : ExtPlane) ∈ toExt (rectangle (scSideA k) (scSideB k)) :=
    fun z hz => ⟨scMap k z, mapsTo_scMap hk₀ hk₁ hz, rfl⟩
  have hsep : ∀ z ∈ upperHalf, ∀ q ∈ frontier (toExt upperHalf),
      scMapExt k (z : ExtPlane) ≠ scMapExt k q := by
    intro z hz q hq h
    have h1 := hint z hz
    rw [h] at h1
    have h2 : scMapExt k q ∈ toExt (rectangle (scSideA k) (scSideB k)) ∩
        frontier (toExt (rectangle (scSideA k) (scSideB k))) := ⟨h1, hbij.mapsTo hq⟩
    rw [hRo.inter_frontier_eq] at h2
    exact h2
  refine ⟨fun z _ => rfl, scMapExt_continuousOn_closure_toExt hk₀ hk₁, ?_, ?_⟩
  · rw [hcl]
    rintro p (⟨z, hz, rfl⟩ | hp) q (⟨w, hw, rfl⟩ | hq) hpq
    · exact congrArg _ (hinj hz hw (OnePoint.coe_injective hpq))
    · exact absurd hpq (hsep z hz q hq)
    · exact absurd hpq.symm (hsep w hw p hp)
    · exact hbij.injOn hp hq hpq
  · apply subset_antisymm
    · calc scMapExt k '' closure (toExt upperHalf)
          ⊆ closure (scMapExt k '' toExt upperHalf) :=
            (scMapExt_continuousOn_closure_toExt hk₀ hk₁).image_closure
        _ = closure (toExt (rectangle (scSideA k) (scSideB k))) := by rw [himg']
    · rw [hclR]
      rintro p (hp | hp)
      · rw [← himg'] at hp
        exact image_mono subset_closure hp
      · rw [← hbij.image_eq] at hp
        exact image_mono frontier_subset_closure hp

theorem scMapExt_prevertices {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    ∀ j : Fin 4, scMapExt k (((scPrevertex k j : ℝ) : ℂ) : ExtPlane) =
      ![((0 : ℂ) : ExtPlane), ((scSideA k : ℂ) : ExtPlane),
        (((scSideA k : ℂ) + (scSideB k : ℂ) * I : ℂ) : ExtPlane),
        (((scSideB k : ℂ) * I : ℂ) : ExtPlane)] j := by
  obtain ⟨h0, h1, h2, h3⟩ := scMap_prevertices hk₀ hk₁
  intro j
  fin_cases j
  · exact congrArg (fun w : ℂ => (w : ExtPlane)) h0
  · exact congrArg (fun w : ℂ => (w : ExtPlane)) h1
  · exact congrArg (fun w : ℂ => (w : ExtPlane)) h2
  · exact congrArg (fun w : ℂ => (w : ExtPlane)) h3

end LiZhongQC
