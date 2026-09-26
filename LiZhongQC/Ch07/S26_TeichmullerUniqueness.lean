import LiZhongQC.Ch07.S25_QuadraticDifferentials
import LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# §26 Teichmüller 唯一性定理 — Teichmüller's uniqueness theorem

* §26.1 the Teichmüller extremal problem (26.1), (26.2); Theorem 26.1 (existence of extremal
  maps); the generalized Grötzsch problem (26.3)      — `IsExtremalInHomotopyClass`,
                                                         `thm26_1_extremal_exists`,
                                                         `grotzsch_generalized`
* §26.2 Teichmüller deformations `S_{q,k}`: the new parameters at regular points and at zeros,
  (26.4)–(26.6), the terminal differential `q'`, the deformation map `f₀`, the deformation
  space `T̃(S₀)`, the norm `‖q‖` and `Q₁(S₀)`      — `teichStretch`, `teichStretchZero`,
                                                         `IsTeichDeformation`, `quadDiffNorm`
* §26.3 Teichmüller maps, initial and terminal differentials, their Beltrami differential
  `k φ̄/|φ|`; every Teichmüller map is a deformation map followed by a conformal map
                                                       — `IsTeichmullerMap`
* §26.4 Theorem 26.2 (uniqueness theorem, (26.7)); Lemma 26.1 (26.8); the stretching function
  `λ_f` and (26.9); Lemma 26.2 (26.10); the inequalities (26.11)–(26.16) of the proof
                                                       — `thm26_2_uniqueness`, `lemma26_1`,
                                                         `lemma26_2`, `eq26_13`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-! ## §26.1 The Teichmüller extremal problem -/

/-- §26.1 (Teichmüller 极值问题).  `f₀` is an extremal map in its homotopy class `[f₀]`: a
quasiconformal map whose maximal dilatation satisfies (26.1), `K[f₀] = inf {K[f] : f ∈ [f₀]}`.
(By the convention `K[f] = ∞` for non-quasiconformal `f`, only quasiconformal competitors
matter.) -/
def IsExtremalInHomotopyClass (f : S₀ ≃ₜ S₁) : Prop :=
  IsQCRS f ∧ ∀ g : S₀ ≃ₜ S₁, IsQCRS g → ContinuousMap.Homotopic (f : C(S₀, S₁)) (g : C(S₀, S₁)) →
    maxDilatationRS f ≤ maxDilatationRS g

/-- (26.2): in the homotopy class of `f*` there is a sequence `fₙ` with `K[fₙ] → inf K[f]`; the
lifts of a sequence with bounded dilatation have a locally uniformly convergent subsequence
whose limit is a `K`-quasiconformal map homotopic to `f*` (§26.1, the proof of Theorem 26.1). -/
theorem eq26_2_limit_of_bounded_dilatation [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) (f₀ : S₀ ≃ₜ S₁) {K : ℝ} (fn : ℕ → S₀ ≃ₜ S₁)
    (hK : ∀ n, IsKQCRS (fn n) K)
    (hhom : ∀ n, ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) ((fn n : S₀ ≃ₜ S₁) : C(S₀, S₁))) :
    ∃ (φ : ℕ → ℕ) (f : S₀ ≃ₜ S₁), StrictMono φ ∧ IsKQCRS f K ∧
      ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)) ∧
      (∀ x, Tendsto (fun n => fn (φ n) x) atTop (𝓝 (f x))) ∧
      maxDilatationRS f ≤ liminf (fun n => maxDilatationRS (fn (φ n))) atTop := by
  sorry

/-- **Theorem 26.1**: in the Teichmüller extremal problem (closed surfaces of genus `g > 1`,
`f* : S₀ → S₁` an orientation preserving homeomorphism) an extremal map always exists. -/
theorem thm26_1_extremal_exists [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) (f₀ : S₀ ≃ₜ S₁) (hf₀ : IsOrientationPreservingRS f₀) :
    ∃ f : S₀ ≃ₜ S₁, ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)) ∧
      IsExtremalInHomotopyClass f := by
  sorry

/-- (26.3): the affine stretch `A : x + iy ↦ (a'/a) x + iy` of the rectangle `R(0, a, a+i, i)` onto
`R'(0, a', a'+i, i)`. -/
def affineStretch (a a' : ℝ) (z : ℂ) : ℂ := ((a' / a : ℝ) : ℂ) * z.re + z.im * I

/-! ### Helpers for `grotzsch_generalized` (`s26g_`): the generalized Grötzsch problem -/

/-- If `g` maps a bounded quadrilateral `Q` homeomorphically onto a bounded quadrilateral `Q'`, with a
homeomorphic extension `G` to the closures sending the vertices of `Q` to those of `Q'`, and `Qₘ → Q` from
inside with closures in `Q`, then the image quadrilaterals `g(Qₘ)` tend to `Q'` from inside. -/
theorem s26g_tendsFromInside_image {Q Q' : TopQuad} (hQb : Bornology.IsBounded Q.dom)
    (hQ'b : Bornology.IsBounded Q'.dom) {g : ℂ → ℂ} (hgc : ContinuousOn g Q.dom)
    (hgi : InjOn g Q.dom) (himg : g '' Q.dom = Q'.dom) {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g Q.dom Q'.dom G) (hGv : ∀ i, G (Q.vert i) = Q'.vert i)
    {Qm Qm' : ℕ → TopQuad} (hQm : TopQuad.TendsFromInside Qm Q)
    (hQmc : ∀ m, closure (toExt (Qm m).dom) ⊆ toExt Q.dom)
    (hQm' : ∀ m, (Qm m).IsImageUnder (Qm' m) g) : TopQuad.TendsFromInside Qm' Q' := by
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hQne : Q.dom.Nonempty := Q.isTopQuad.1.2.1.1
  obtain ⟨g0, hg0G, hg0c, hg0i, -, hg0eq⟩ := qcl_m_descend hQb hQ'b hG
  set C : Set ℂ := closure Q.dom with hCdef
  have hCc : IsCompact C := hQb.isCompact_closure
  have hg0u : UniformContinuousOn g0 C := hCc.uniformContinuousOn_of_continuous hg0c
  have hg0img : g0 '' Q.dom = Q'.dom := (hg0eq.image_eq).trans himg
  have hKm : ∀ m, closure (Qm m).dom ⊆ Q.dom := by
    intro m z hz
    have himg' := image_closure_subset_closure_image OnePoint.continuous_coe (s := (Qm m).dom)
    have h1 : (z : ExtPlane) ∈ closure (toExt (Qm m).dom) := himg' (mem_image_of_mem _ hz)
    exact coe_mem_toExt_iff.mp (hQmc m h1)
  have hQmb : ∀ m, Bornology.IsBounded (Qm m).dom := fun m => hQb.subset (hQm.1 m)
  have hQmo : ∀ m, IsOpen (Qm m).dom := fun m => (Qm m).isTopQuad.1.1
  have hQm'o : ∀ m, IsOpen (Qm' m).dom := fun m => (Qm' m).isTopQuad.1.1
  have hQm'sub : ∀ m, (Qm' m).dom ⊆ Q'.dom := by
    intro m
    rw [(hQm' m).1, ← himg]
    exact image_mono (hQm.1 m)
  have hQm'b : ∀ m, Bornology.IsBounded (Qm' m).dom := fun m => hQ'b.subset (hQm'sub m)
  have hfrQne : (frontier Q.dom).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · exact hQne.ne_empty h
    · rw [h] at hQb
      exact NormedSpace.unbounded_univ ℝ ℂ hQb
  have hfrQm'eq : ∀ m, frontier (Qm' m).dom = g '' frontier (Qm m).dom := fun m =>
    qcl_m_frontier_eq_image (hQmo m) (hQm'o m) (hQmb m) (hgc.mono ((hKm m).trans subset_rfl))
      (hgi.mono (hKm m)) (hQm' m).1.symm
  have hfrQ'eq : frontier Q'.dom = g0 '' frontier Q.dom :=
    qcl_m_frontier_eq_image hQo hQ'o hQb hg0c hg0i hg0img
  have hsideQm'eq : ∀ m i, (Qm' m).sideC i = g '' (Qm m).sideC i := fun m i =>
    qcl_m_sideC_eq_image hQo hgc hgi (hQmb m) (hQm'b m) (hQmc m) (hQm' m).1.symm (hQm' m).2 i
  have hsideQ'eq : ∀ i, Q'.sideC i = g0 '' Q.sideC i := by
    intro i
    have h1 := aqc_image_side_homeo hQ'o himg hG i
    rw [hGv i, hGv (i + 1), hGv (i + 2), ← Q'.side_eq_boundaryArc i,
      qcl_m_side_eq_toExt_sideC hQb i, qcl_m_side_eq_toExt_sideC hQ'b i,
      ← qcl_m_toExt_image_eq hg0G (qcl_m_sideC_subset_closure hQb i)] at h1
    exact ((Set.image_eq_image OnePoint.coe_injective).1 h1).symm
  have hsideQne : ∀ i, (Q.sideC i).Nonempty := by
    intro i
    have h1 : Q.vert i ∈ Q.side i := ⟨Q.isTopQuad.2.1 i, Or.inl rfl⟩
    rw [qcl_m_side_eq_toExt_sideC hQb i] at h1
    obtain ⟨c, hc, -⟩ := h1
    exact ⟨c, hc⟩
  refine ⟨hQm'sub, ?_, ?_, ?_⟩
  · -- vertices
    intro i
    have hvm : ∀ m, (Qm' m).vert i = G ((Qm m).vert i) := by
      intro m
      have h1 : (Qm m).vert i ∈ toExt Q.dom :=
        hQmc m (frontier_subset_closure ((Qm m).isTopQuad.2.1 i))
      obtain ⟨z, hz, hze⟩ := h1
      rw [(hQm' m).2 i, ← hze, hG.1 z hz]
      rfl
    have hmem : ∀ m, (Qm m).vert i ∈ closure (toExt Q.dom) := fun m =>
      subset_closure (hQmc m (frontier_subset_closure ((Qm m).isTopQuad.2.1 i)))
    have hQv : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    have ht : Tendsto (fun m => (Qm m).vert i) atTop (𝓝[closure (toExt Q.dom)] Q.vert i) :=
      tendsto_nhdsWithin_iff.2 ⟨hQm.2.1 i, Eventually.of_forall hmem⟩
    have h2 := ((hG.2.1 _ hQv).tendsto).comp ht
    rw [hGv i] at h2
    exact h2.congr fun m => (hvm m).symm
  · -- frontier
    intro ε hε
    obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuousOn_iff.1 hg0u ε hε
    filter_upwards [hQm.2.2.1 η hηpos] with m hm
    intro z hz
    rw [hfrQm'eq m] at hz
    obtain ⟨w, hwfr, rfl⟩ := hz
    have hwQ : w ∈ Q.dom := hKm m (frontier_subset_closure hwfr)
    obtain ⟨w', hw'fr, hw'dist⟩ := (Metric.infDist_lt_iff hfrQne).mp (hm w hwfr)
    have h2 : dist (g0 w) (g0 w') < ε :=
      hη w (subset_closure hwQ) w' (frontier_subset_closure hw'fr) hw'dist
    rw [← hg0eq hwQ]
    calc infDist (g0 w) (frontier Q'.dom)
        ≤ dist (g0 w) (g0 w') := by
          rw [hfrQ'eq]; exact Metric.infDist_le_dist_of_mem (mem_image_of_mem g0 hw'fr)
      _ < ε := h2
  · -- sides
    intro i ε hε
    obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuousOn_iff.1 hg0u ε hε
    filter_upwards [hQm.2.2.2 i η hηpos] with m hm
    intro z hz
    rw [hsideQm'eq m i] at hz
    obtain ⟨w, hwside, rfl⟩ := hz
    have hwQ : w ∈ Q.dom := hKm m (qcl_m_sideC_subset_closure (hQmb m) i hwside)
    obtain ⟨w', hw'side, hw'dist⟩ := (Metric.infDist_lt_iff (hsideQne i)).mp (hm w hwside)
    have h2 : dist (g0 w) (g0 w') < ε :=
      hη w (subset_closure hwQ) w' (qcl_m_sideC_subset_closure hQb i hw'side) hw'dist
    rw [← hg0eq hwQ]
    calc infDist (g0 w) (Q'.sideC i)
        ≤ dist (g0 w) (g0 w') := by
          rw [hsideQ'eq]; exact Metric.infDist_le_dist_of_mem (mem_image_of_mem g0 hw'side)
      _ < ε := h2
/-- The modulus inequality `M(Q') ≤ K M(Q)` for a `K`-q.c. map of a bounded quadrilateral `Q` onto a bounded
quadrilateral `Q'` (the whole domains, not compactly contained) with a vertex-preserving homeomorphic extension:
exhaust `Q` from inside (M1), push forward, and pass to the limit by Theorem 4.8. -/
theorem s26g_modulus_le {Q Q' : TopQuad} (hQb : Bornology.IsBounded Q.dom)
    (hQ'b : Bornology.IsBounded Q'.dom) {g : ℂ → ℂ} {K : ℝ} (hg : IsKQC g Q.dom K)
    (himg : g '' Q.dom = Q'.dom) {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g Q.dom Q'.dom G) (hGv : ∀ i, G (Q.vert i) = Q'.vert i) :
    Q'.modulus ≤ K * Q.modulus := by
  obtain ⟨Qm, hQm, hQmc⟩ := qcl_m_exists_tendsFromInside Q hQb
  choose Qm' hQm' hmod using fun m => hg.2.2.2 (Qm m) (hQmc m)
  have hT : TopQuad.TendsFromInside Qm' Q' :=
    s26g_tendsFromInside_image hQb hQ'b hg.2.2.1.1 hg.2.2.1.2.1 himg hG hGv hQm hQmc hQm'
  exact le_of_tendsto_of_tendsto' (thm4_8_modulus_continuous hQ'b hT)
    ((thm4_8_modulus_continuous hQb hQm).const_mul K) hmod

/-- A `K`-q.c. map of `R(0,a,a+i,i)` onto `R(0,a',a'+i,i)` with a vertex-preserving homeomorphic extension has
`max(a'/a, a/a') ≤ K` (apply `s26g_modulus_le` to the rectangles and to their rotations). -/
theorem s26g_rect_bound {a a' K : ℝ} (ha : 0 < a) (ha' : 0 < a') {g : ℂ → ℂ}
    (hg : IsKQC g (rectangle a 1) K) (himg : g '' rectangle a 1 = rectangle a' 1)
    {G : ExtPlane → ExtPlane} (hG : IsHomeoExtension g (rectangle a 1) (rectangle a' 1) G)
    (hGv : ∀ i, G (rectVert a 1 i) = rectVert a' 1 i) : max (a' / a) (a / a') ≤ K := by
  have h1 := s26g_modulus_le (Q := rectQuad ha one_pos) (Q' := rectQuad ha' one_pos)
    (isBounded_rectangle a 1) (isBounded_rectangle a' 1) hg himg hG hGv
  have h2 := s26g_modulus_le (Q := (rectQuad ha one_pos).rotate) (Q' := (rectQuad ha' one_pos).rotate)
    (isBounded_rectangle a 1) (isBounded_rectangle a' 1) hg himg hG (fun i => hGv (i + 1))
  have hr : ∀ Q : TopQuad, Q.rotate.modulus = 1 / Q.modulus := fun Q => by
    rw [thm1_2_modulus_rotate Q, one_div_one_div]
  rw [hr, hr, modulus_rectQuad, modulus_rectQuad] at h2
  rw [modulus_rectQuad, modulus_rectQuad] at h1
  simp only [div_one] at h1 h2
  refine max_le ?_ ?_
  · rw [div_le_iff₀ ha]
    linarith
  · rw [div_le_iff₀ ha']
    rw [mul_one_div, div_le_div_iff₀ ha' ha] at h2
    linarith

/-- **Part 1 of the generalized Grötzsch problem.**  A quasiconformal map of `Q` onto `Q'` with a
vertex-preserving homeomorphic extension has `K[f] ≥ max(a'/a, a/a')`: `f` is `K[f]`-q.c., and
`ψ ∘ f ∘ φ⁻¹` is a `K[f]`-q.c. map of the rectangles with matching vertices. -/
theorem s26g_part1 (Q Q' : TopQuad) {a a' : ℝ} {φ ψ : ℂ → ℂ}
    (hφ : Q.IsStdConformalMap a 1 φ) (hψ : Q'.IsStdConformalMap a' 1 ψ) (f : ℂ → ℂ)
    (hf : IsQuasiconformal f Q.dom) (himg : f '' Q.dom = Q'.dom) {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f Q.dom Q'.dom F) (hFv : ∀ i, F (Q.vert i) = Q'.vert i) :
    ENNReal.ofReal (max (a' / a) (a / a')) ≤ maxDilatation f Q.dom := by
  obtain ⟨ha, -, hφc, Φ, hΦ, hΦv⟩ := hφ
  obtain ⟨ha', -, hψc, Ψ, hΨ, hΨv⟩ := hψ
  obtain ⟨K₀, hK₀⟩ := hf
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  obtain ⟨-, hK⟩ := UniversalTeichmuller.ut_md_isKQC_toReal hK₀ Q.isTopQuad.1.2.1.1
  have hfin : maxDilatation f Q.dom ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK₀).1
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hφic : IsConformalOnto (Function.invFunOn φ Q.dom) (rectangle a 1) Q.dom := hφc.symm hQo
  have hΦi := isHomeoExtension_invFunOn hφc hΦ
  have hΦiv : ∀ i, Function.invFunOn Φ (closure (toExt Q.dom)) (rectVert a 1 i) = Q.vert i := by
    intro i
    rw [← hΦv i]
    exact hΦ.2.2.1.leftInvOn_invFunOn (frontier_subset_closure (Q.isTopQuad.2.1 i))
  have hg1 := thm7_1_comp (isKQC_one_of_conformal (isOpen_rectangle a 1) hφic) hK
    (by rw [hφic.2.2])
  have himg1 : (f ∘ Function.invFunOn φ Q.dom) '' rectangle a 1 = Q'.dom := by
    rw [image_comp, hφic.2.2, himg]
  have hg := thm7_1_comp hg1 (isKQC_one_of_conformal hQ'o hψc) himg1.subset
  have himg2 : (ψ ∘ (f ∘ Function.invFunOn φ Q.dom)) '' rectangle a 1 = rectangle a' 1 := by
    rw [image_comp, himg1, hψc.2.2]
  have hG := hΨ.comp (hF.comp hΦi hφic.mapsTo) (fun z hz => himg1 ▸ mem_image_of_mem _ hz)
  have hb := s26g_rect_bound ha ha' hg himg2 hG (fun i => by
    simp only [Function.comp_apply, hΦiv, hFv, hΨv])
  simpa using hb
/-- Real and imaginary parts of the affine stretch: `A(x + iy) = (a'/a) x + iy`. -/
theorem s26g_affine_re_im (a a' : ℝ) (z : ℂ) :
    (affineStretch a a' z).re = a' / a * z.re ∧ (affineStretch a a' z).im = z.im := by
  constructor <;> simp [affineStretch]

/-- The affine stretch is continuous. -/
theorem s26g_affine_continuous (a a' : ℝ) : Continuous (affineStretch a a') := by
  unfold affineStretch
  fun_prop

/-- For `a, a' > 0` the affine stretch is injective. -/
theorem s26g_affine_injective {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a') :
    Function.Injective (affineStretch a a') := by
  intro z w h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  rw [(s26g_affine_re_im a a' z).1, (s26g_affine_re_im a a' w).1] at h1
  rw [(s26g_affine_re_im a a' z).2, (s26g_affine_re_im a a' w).2] at h2
  have hr : a' / a ≠ 0 := (div_pos ha' ha).ne'
  exact Complex.ext (mul_left_cancel₀ hr h1) h2

/-- The affine stretch maps `R(0,a,a+i,i)` onto `R(0,a',a'+i,i)`. -/
theorem s26g_affine_image {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a') :
    affineStretch a a' '' rectangle a 1 = rectangle a' 1 := by
  have hr : 0 < a' / a := div_pos ha' ha
  ext w
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    obtain ⟨hre, him⟩ := s26g_affine_re_im a a' z
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; positivity
    · rw [hre]
      calc a' / a * z.re < a' / a * a := mul_lt_mul_of_pos_left h2 hr
        _ = a' := div_mul_cancel₀ a' ha.ne'
    · rw [him]; exact h3
    · rw [him]; exact h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨((a / a' * w.re : ℝ) : ℂ) + (w.im : ℂ) * I, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
        add_zero]
      positivity
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
        add_zero]
      calc a / a' * w.re < a / a' * a' := mul_lt_mul_of_pos_left h2 (div_pos ha ha')
        _ = a := div_mul_cancel₀ a ha'.ne'
    · simpa using h3
    · simpa using h4
    · apply Complex.ext
      · rw [(s26g_affine_re_im a a' _).1]
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
          add_zero]
        field_simp
      · rw [(s26g_affine_re_im a a' _).2]
        simp

/-- The affine stretch sends the vertices of `R(0,a,a+i,i)` to those of `R(0,a',a'+i,i)`. -/
theorem s26g_affine_vert {a a' : ℝ} (ha : 0 < a) (i : Fin 4) :
    OnePoint.map (affineStretch a a') (rectVert a 1 i) = rectVert a' 1 i := by
  have key : ∀ z w : ℂ, affineStretch a a' z = w →
      OnePoint.map (affineStretch a a') (z : ExtPlane) = (w : ExtPlane) := fun z w h => by
    rw [OnePoint.map_some, h]
  fin_cases i
  · exact key _ _ (by apply Complex.ext <;> simp [affineStretch])
  · exact key _ _ (by apply Complex.ext <;> simp [affineStretch, ha.ne'])
  · exact key _ _ (by apply Complex.ext <;> simp [affineStretch, ha.ne'])
  · exact key _ _ (by apply Complex.ext <;> simp [affineStretch])

/-- For `a, a' > 0` the affine stretch is `max(a'/a, a/a')`-q.c. on the plane: it is `z ↦ αz + βz̄` with
`α = (r+1)/2`, `β = (r-1)/2`, `r = a'/a`, and `(|α|+|β|)/(|α|-|β|) = max(r, 1/r)`. -/
theorem s26g_affine_isKQC {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a') :
    IsKQC (affineStretch a a') univ (max (a' / a) (a / a')) := by
  set r : ℝ := a' / a with hrdef
  have hr : 0 < r := div_pos ha' ha
  have hinv : a / a' = 1 / r := by rw [hrdef, one_div_div]
  have heq : affineStretch a a' =
      fun z => (((r + 1) / 2 : ℝ) : ℂ) * z + (((r - 1) / 2 : ℝ) : ℂ) * conj z + 0 := by
    funext z
    apply Complex.ext
    · rw [(s26g_affine_re_im a a' z).1]
      simp only [add_re, mul_re, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, sub_zero,
        zero_re]
      ring
    · rw [(s26g_affine_re_im a a' z).2]
      simp only [add_im, mul_im, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, add_zero]
      ring
  have hnα : ‖(((r + 1) / 2 : ℝ) : ℂ)‖ = (r + 1) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnβ : ‖(((r - 1) / 2 : ℝ) : ℂ)‖ = |(r - 1) / 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hlt : ‖(((r - 1) / 2 : ℝ) : ℂ)‖ < ‖(((r + 1) / 2 : ℝ) : ℂ)‖ := by
    rw [hnα, hnβ, abs_lt]
    constructor <;> linarith
  have hC1 := (affine_isC1Quasiconformal (C := 0) hlt).1
  rw [← heq] at hC1
  refine (isKQC_of_isC1Quasiconformal hC1).mono ?_
  rw [hnα, hnβ, hinv]
  rcases le_total 1 r with h1 | h1
  · rw [abs_of_nonneg (by linarith)]
    have e : ((r + 1) / 2 + (r - 1) / 2) / ((r + 1) / 2 - (r - 1) / 2) = r := by ring
    rw [e]
    exact le_max_left _ _
  · rw [abs_of_nonpos (by linarith)]
    have e : ((r + 1) / 2 + -((r - 1) / 2)) / ((r + 1) / 2 - -((r - 1) / 2)) = 1 / r := by
      congr 1 <;> ring
    rw [e]
    exact le_max_right _ _

/-- A continuous injective map of the plane extends (by `OnePoint.map`) homeomorphically from the closure of a
bounded set `U` onto the closure of `f(U)`. -/
theorem s26g_isHomeoExtension_map {f : ℂ → ℂ} (hfc : Continuous f) (hfi : Function.Injective f)
    {U : Set ℂ} (hU : Bornology.IsBounded U) : IsHomeoExtension f U (f '' U) (OnePoint.map f) := by
  have hC : closure (toExt U) = toExt (closure U) := closure_toExt_of_isBounded hU
  have htoExt : ∀ S : Set ℂ, OnePoint.map f '' toExt S = toExt (f '' S) := fun S => by
    simp only [toExt, image_image]
    rfl
  have hFC : ContinuousOn (OnePoint.map f) (closure (toExt U)) := by
    intro p hp
    rw [hC] at hp
    obtain ⟨z, -, rfl⟩ := hp
    exact ContinuousAt.continuousWithinAt (OnePoint.continuousAt_coe.2
      (OnePoint.continuous_coe.continuousAt.comp hfc.continuousAt))
  refine ⟨fun z _ => rfl, hFC, ?_, ?_⟩
  · intro p hp q hq hpq
    rw [hC] at hp hq
    obtain ⟨z, -, rfl⟩ := hp
    obtain ⟨w, -, rfl⟩ := hq
    rw [hfi (OnePoint.coe_injective hpq)]
  · refine subset_antisymm ?_ ?_
    · rw [← htoExt]
      exact hFC.image_closure
    · refine closure_minimal ?_ (isClosed_closure.isCompact.image_of_continuousOn hFC).isClosed
      rw [← htoExt]
      exact image_mono subset_closure

/-- §26.1 (the generalized Grötzsch problem).  Let `Q`, `Q'` be quadrilaterals with standard
conformal maps `φ : Q → R(0, a, a+i, i)`, `ψ : Q' → R'(0, a', a'+i, i)`.  Every quasiconformal map
of `Q` onto `Q'` preserving the vertices in order has `K[f] ≥ max(a'/a, a/a')`, and the map
`ψ⁻¹ ∘ A ∘ φ`, `A` the affine stretch (26.3), attains this value.  The vertex correspondence is that
of a homeomorphic extension `F` to the closures (`F (Q.vert i) = Q'.vert i`).

**Correction.**  The vertex correspondence was stated through `Q.IsImageUnder Q'`, i.e. through the raw
values of the maps at the boundary vertices, which nothing controls, and the statement was **false**:
a conformal map of `R(0,2,2+i,i)` onto `R(0,1/2,1/2+i,i)` with suitable vertex values has `K = 1 < 4`,
and `invFunOn ψ Q'.dom` takes the same junk value at all four (boundary) vertices. -/
theorem grotzsch_generalized (Q Q' : TopQuad) {a a' : ℝ} {φ ψ : ℂ → ℂ}
    (hφ : Q.IsStdConformalMap a 1 φ) (hψ : Q'.IsStdConformalMap a' 1 ψ) :
    (∀ f : ℂ → ℂ, IsQuasiconformal f Q.dom → f '' Q.dom = Q'.dom →
      (∃ F : ExtPlane → ExtPlane, IsHomeoExtension f Q.dom Q'.dom F ∧ ∀ i, F (Q.vert i) = Q'.vert i) →
      ENNReal.ofReal (max (a' / a) (a / a')) ≤ maxDilatation f Q.dom) ∧
    IsQuasiconformal (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ) Q.dom ∧
      (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ) '' Q.dom = Q'.dom ∧
      (∃ F : ExtPlane → ExtPlane, IsHomeoExtension (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ)
          Q.dom Q'.dom F ∧ ∀ i, F (Q.vert i) = Q'.vert i) ∧
      maxDilatation (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ) Q.dom =
        ENNReal.ofReal (max (a' / a) (a / a')) := by
  have hP1 := s26g_part1 Q Q' hφ hψ
  obtain ⟨ha, -, hφc, Φ, hΦ, hΦv⟩ := hφ
  obtain ⟨ha', -, hψc, Ψ, hΨ, hΨv⟩ := hψ
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hAimg := s26g_affine_image ha ha'
  have hA : IsKQC (affineStretch a a') (rectangle a 1) (max (a' / a) (a / a')) :=
    ac_t_isKQC_restrict (s26g_affine_isKQC ha ha') (isOpen_rectangle a 1) (subset_univ _)
  have hψic : IsConformalOnto (Function.invFunOn ψ Q'.dom) (rectangle a' 1) Q'.dom := hψc.symm hQ'o
  have h1 := thm7_1_comp (isKQC_one_of_conformal hQo hφc) hA (by rw [hφc.2.2])
  have himg1 : (affineStretch a a' ∘ φ) '' Q.dom = rectangle a' 1 := by
    rw [image_comp, hφc.2.2, hAimg]
  have h2 := thm7_1_comp h1 (isKQC_one_of_conformal (isOpen_rectangle a' 1) hψic) himg1.subset
  have himg2 : (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ) '' Q.dom = Q'.dom := by
    rw [image_comp, himg1, hψic.2.2]
  have hAext : IsHomeoExtension (affineStretch a a') (rectangle a 1) (rectangle a' 1)
      (OnePoint.map (affineStretch a a')) := by
    have h := s26g_isHomeoExtension_map (s26g_affine_continuous a a') (s26g_affine_injective ha ha')
      (isBounded_rectangle a 1)
    rwa [hAimg] at h
  have hext := (isHomeoExtension_invFunOn hψc hΨ).comp (hAext.comp hΦ hφc.mapsTo)
    (fun z hz => himg1 ▸ mem_image_of_mem _ hz)
  have hextv : ∀ i, (Function.invFunOn Ψ (closure (toExt Q'.dom)) ∘
      (OnePoint.map (affineStretch a a') ∘ Φ)) (Q.vert i) = Q'.vert i := by
    intro i
    simp only [Function.comp_apply]
    rw [hΦv i, s26g_affine_vert ha i, ← hΨv i]
    exact hΨ.2.2.1.leftInvOn_invFunOn (frontier_subset_closure (Q'.isTopQuad.2.1 i))
  have hqc : IsQuasiconformal (Function.invFunOn ψ Q'.dom ∘ affineStretch a a' ∘ φ) Q.dom := ⟨_, h2⟩
  refine ⟨fun f hf himg ⟨F, hF, hFv⟩ => hP1 f hf himg hF hFv, hqc, himg2, ⟨_, hext, hextv⟩, ?_⟩
  refine le_antisymm ?_ (hP1 _ hqc himg2 hext hextv)
  simpa using (isKQC_maxDilatation_le h2).1

/-! ## §26.2 Teichmüller deformations -/

/-- §26.2: the new parameter `ζ' = (ζ + k ζ̄)/(1 - k)` near a regular point of `q`, `ζ` a natural
parameter. -/
def teichStretch (k : ℝ) (ζ : ℂ) : ℂ := (ζ + k * conj ζ) / (1 - k)

/-- §26.2: the new parameter near a zero of order `m` of `q`, `ζ` a natural parameter with
`q = ((m+2)/2)² ζ^m dζ²`:
`ζ' = ζ [1 + k (ζ̄/ζ)^{m/2+1}]^{2/(m+2)} / (1 - k)^{2/(m+2)}` for `ζ ≠ 0`, `ζ' = 0` for `ζ = 0`.
Here `(ζ̄/ζ)^{1/2} = ζ̄/|ζ|`, so `(ζ̄/ζ)^{m/2+1} = (ζ̄/|ζ|)^{m+2}`, and `(1 + w)^a` (`|w| < 1`) is the
binomial series, i.e. the principal branch of the power. -/
def teichStretchZero (k : ℝ) (m : ℕ) (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0 else
    ζ * (1 + k * (conj ζ / ‖ζ‖) ^ (m + 2)) ^ ((2 : ℂ) / (m + 2)) / ((1 - k : ℂ) ^ ((2 : ℂ) / (m + 2)))

/-- (26.4): if two natural parameters at regular points satisfy `ζ = ±ζ₁ + c`, then the new
parameters satisfy `ζ' = ±ζ₁' + c₁`; hence the new parameters are conformally compatible. -/
theorem eq26_4 (k : ℝ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (c ζ₁ : ℂ) :
    teichStretch k (ε * ζ₁ + c) = ε * teichStretch k ζ₁ + teichStretch k c := by
  -- `ε = ±1` is real, so it is fixed by conjugation
  have hconj : conj ε = ε := by rcases hε with rfl | rfl <;> simp
  simp only [teichStretch, map_add, map_mul, hconj]
  -- no `k ≠ 1` hypothesis is needed: `(A + B)/D = A/D + B/D` holds even at `D = 0`
  rw [← mul_div_assoc, ← add_div]
  congr 1
  ring

/-- `(z ^ (2/(m+2))) ^ (m+2) = z ^ 2`.  No branch condition is needed, because the outer exponent is
a *natural* number: `Complex.cpow_mul_nat` is unconditional, unlike `Complex.cpow_mul`. -/
theorem cpow_two_div_pow (z : ℂ) (m : ℕ) :
    (z ^ ((2 : ℂ) / ((m : ℂ) + 2))) ^ (m + 2) = z ^ 2 := by
  have hm : ((m : ℂ) + 2) ≠ 0 := by
    have h : ((m + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h
    exact h
  rw [← Complex.cpow_mul_nat]
  push_cast
  rw [div_mul_cancel₀ _ hm]
  exact Complex.cpow_two z

/-- The `(m+2)`-th power of the new parameter at a zero:
`ζ'^{m+2} (1 - k)² = ζ^{m+2} (1 + k (ζ̄/|ζ|)^{m+2})²`. -/
theorem teichStretchZero_pow_mul {k : ℝ} (hk : k < 1) (m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    teichStretchZero k m ζ ^ (m + 2) * (1 - (k : ℂ)) ^ 2 =
      ζ ^ (m + 2) * (1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ^ 2 := by
  have h1k : (1 - (k : ℂ)) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  unfold teichStretchZero
  rw [if_neg hζ, div_pow, mul_pow, cpow_two_div_pow, cpow_two_div_pow,
    div_mul_cancel₀ _ (pow_ne_zero 2 h1k)]

/-- `ζ̄/|ζ|` has modulus one, and so do its powers. -/
theorem norm_conj_div_norm_pow {ζ : ℂ} (hζ : ζ ≠ 0) (n : ℕ) :
    ‖((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ n‖ = 1 := by
  rw [norm_pow, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 hζ), one_pow]

/-- `1 + k c ≠ 0` for `0 ≤ k < 1` and `|c| = 1`. -/
theorem one_add_ofReal_mul_ne_zero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {c : ℂ} (hc : ‖c‖ = 1) :
    1 + (k : ℂ) * c ≠ 0 := by
  intro h
  have h1 : ‖(k : ℂ) * c‖ = 1 := by
    rw [eq_neg_of_add_eq_zero_right h, norm_neg, norm_one]
  rw [norm_mul, hc, mul_one, Complex.norm_real, Real.norm_of_nonneg hk₀] at h1
  linarith

/-- The new parameter at a zero vanishes only at `ζ = 0`. -/
theorem teichStretchZero_ne_zero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    teichStretchZero k m ζ ≠ 0 := by
  have hA := one_add_ofReal_mul_ne_zero hk₀ hk (norm_conj_div_norm_pow hζ (m + 2))
  have h1k : (1 - (k : ℂ)) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  unfold teichStretchZero
  rw [if_neg hζ]
  refine div_ne_zero (mul_ne_zero hζ fun h => hA ((Complex.cpow_eq_zero_iff _ _).1 h).1)
    fun h => h1k ((Complex.cpow_eq_zero_iff _ _).1 h).1

/-- §26.2 (the argument (26.5)): the map `ζ ↦ ζ'` at a zero of order `m` is injective; `ζ₁, ζ₂`
with the same image satisfy `ζ₁^{m+2} = ζ₂^{m+2}`, so `ζ₁ = εζ₂` with `ε^{m+2} = 1`, and then
`ε = 1`.

Proof (no roots of unity are needed): put `n = m + 2`, `p = (ζ/|ζ|)ⁿ` and `A = 1 + k p̄`, so that
`ζ'ⁿ (1 - k)² = |ζ|ⁿ p A²` (`teichStretchZero_pow_mul`).  If `ζ₁' = ζ₂'`, comparing these identities
and their moduli `|ζ|ⁿ A Ā` gives `p₁ A₁ Ā₂ = p₂ A₂ Ā₁`.  Since `p p̄ = 1`, this reduces to
`(1 - k²)(p₁ - p₂) = 0`, so `p₁ = p₂`.  Then `ζ₁` and `ζ₂` have the same nonzero stretch factor
`A^{2/n}/(1 - k)^{2/n}`, hence `ζ₁ = ζ₂`. -/
theorem eq26_5_injective {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) :
    Function.Injective (teichStretchZero k m) := by
  intro ζ₁ ζ₂ h
  have hz : teichStretchZero k m 0 = 0 := by simp [teichStretchZero]
  by_cases h₁ : ζ₁ = 0
  · by_cases h₂ : ζ₂ = 0
    · rw [h₁, h₂]
    · exact absurd (by rw [← h, h₁, hz]) (teichStretchZero_ne_zero hk₀ hk m h₂)
  by_cases h₂ : ζ₂ = 0
  · exact absurd (by rw [h, h₂, hz]) (teichStretchZero_ne_zero hk₀ hk m h₁)
  -- notation
  obtain ⟨p₁, hp₁⟩ : ∃ p : ℂ, p = (ζ₁ / (‖ζ₁‖ : ℂ)) ^ (m + 2) := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p : ℂ, p = (ζ₂ / (‖ζ₂‖ : ℂ)) ^ (m + 2) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c = ((starRingEnd ℂ) ζ₁ / (‖ζ₁‖ : ℂ)) ^ (m + 2) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℂ, c = ((starRingEnd ℂ) ζ₂ / (‖ζ₂‖ : ℂ)) ^ (m + 2) := ⟨_, rfl⟩
  have hn₁ : (‖ζ₁‖ : ℂ) ≠ 0 := by simpa using h₁
  have hn₂ : (‖ζ₂‖ : ℂ) ≠ 0 := by simpa using h₂
  have hpow : ∀ {ζ : ℂ}, (‖ζ‖ : ℂ) ≠ 0 →
      ζ ^ (m + 2) = ((‖ζ‖ ^ (m + 2) : ℝ) : ℂ) * (ζ / (‖ζ‖ : ℂ)) ^ (m + 2) := by
    intro ζ hn
    rw [div_pow, Complex.ofReal_pow, mul_div_cancel₀ _ (pow_ne_zero _ hn)]
  have hconj : ∀ {ζ : ℂ}, ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2) =
      (starRingEnd ℂ) ((ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) := by
    intro ζ
    rw [map_pow, map_div₀, Complex.conj_ofReal]
  have hpc : ∀ {ζ : ℂ}, ζ ≠ 0 →
      (ζ / (‖ζ‖ : ℂ)) ^ (m + 2) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2) = 1 := by
    intro ζ hζ
    have hn : (‖ζ‖ : ℂ) ≠ 0 := by simpa using hζ
    rw [← mul_pow, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow, ← pow_two, div_self (pow_ne_zero 2 hn), one_pow]
  have hA₁ : 1 + (k : ℂ) * c₁ ≠ 0 :=
    one_add_ofReal_mul_ne_zero hk₀ hk (by rw [hc₁]; exact norm_conj_div_norm_pow h₁ _)
  have hA₂ : 1 + (k : ℂ) * c₂ ≠ 0 :=
    one_add_ofReal_mul_ne_zero hk₀ hk (by rw [hc₂]; exact norm_conj_div_norm_pow h₂ _)
  have hnp₁ : ‖p₁‖ = 1 := by
    rw [hp₁, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 h₁), one_pow]
  have hnp₂ : ‖p₂‖ = 1 := by
    rw [hp₂, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 h₂), one_pow]
  -- the equation of the `(m+2)`-th powers
  have E : ((‖ζ₁‖ ^ (m + 2) : ℝ) : ℂ) * p₁ * (1 + (k : ℂ) * c₁) ^ 2 =
      ((‖ζ₂‖ ^ (m + 2) : ℝ) : ℂ) * p₂ * (1 + (k : ℂ) * c₂) ^ 2 := by
    have h0 := congrArg (fun w => w ^ (m + 2) * (1 - (k : ℂ)) ^ 2) h
    simp only [teichStretchZero_pow_mul hk m h₁, teichStretchZero_pow_mul hk m h₂] at h0
    rw [hpow hn₁, hpow hn₂, ← hp₁, ← hp₂, ← hc₁, ← hc₂] at h0
    exact h0
  -- the equation of the moduli
  have N : ((‖ζ₁‖ ^ (m + 2) : ℝ) : ℂ) * ((1 + (k : ℂ) * c₁) * (starRingEnd ℂ) (1 + (k : ℂ) * c₁)) =
      ((‖ζ₂‖ ^ (m + 2) : ℝ) : ℂ) * ((1 + (k : ℂ) * c₂) * (starRingEnd ℂ) (1 + (k : ℂ) * c₂)) := by
    have h0 := congrArg (fun w => ‖w‖) E
    simp only [norm_mul, norm_pow, hnp₁, hnp₂, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] at h0
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, h0]
  have hK : ((‖ζ₁‖ ^ (m + 2) : ℝ) : ℂ) *
      ((1 + (k : ℂ) * c₁) * (starRingEnd ℂ) (1 + (k : ℂ) * c₁)) ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.2 h₁)) (mul_ne_zero hA₁ ?_)
    rw [Ne, map_eq_zero]
    exact hA₁
  have hcA : ∀ {c p : ℂ}, c = (starRingEnd ℂ) p →
      (starRingEnd ℂ) (1 + (k : ℂ) * c) = 1 + (k : ℂ) * p := by
    intro c p hcp
    rw [hcp, map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hcp₁ : c₁ = (starRingEnd ℂ) p₁ := by rw [hc₁, hp₁, hconj]
  have hcp₂ : c₂ = (starRingEnd ℂ) p₂ := by rw [hc₂, hp₂, hconj]
  have hpc₁ : p₁ * c₁ = 1 := by rw [hp₁, hc₁]; exact hpc h₁
  have hpc₂ : p₂ * c₂ = 1 := by rw [hp₂, hc₂]; exact hpc h₂
  have hX : p₁ * (1 + (k : ℂ) * c₁) * (1 + (k : ℂ) * p₂) =
      p₂ * (1 + (k : ℂ) * c₂) * (1 + (k : ℂ) * p₁) := by
    rw [← hcA hcp₁, ← hcA hcp₂]
    refine mul_left_cancel₀ hK ?_
    linear_combination ((starRingEnd ℂ) (1 + (k : ℂ) * c₁) * (starRingEnd ℂ) (1 + (k : ℂ) * c₂)) * E -
      (p₂ * (1 + (k : ℂ) * c₂) * (starRingEnd ℂ) (1 + (k : ℂ) * c₁)) * N
  have hk2 : (1 - (k : ℂ) ^ 2) ≠ 0 := by
    intro h0
    have h' := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at h'
    nlinarith
  have hp : p₁ = p₂ := by
    have h0 : (1 - (k : ℂ) ^ 2) * (p₁ - p₂) = 0 := by
      linear_combination hX - (k : ℂ) * (1 + (k : ℂ) * p₂) * hpc₁ + (k : ℂ) * (1 + (k : ℂ) * p₁) * hpc₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hk2)
  have hc : c₁ = c₂ := by rw [hcp₁, hcp₂, hp]
  -- equal stretch factors
  unfold teichStretchZero at h
  rw [if_neg h₁, if_neg h₂, mul_div_assoc, mul_div_assoc, ← hc₁, ← hc₂, hc] at h
  have h1k : (1 - (k : ℂ)) ≠ 0 := by
    intro h0
    have h' := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  refine mul_right_cancel₀ (div_ne_zero (fun h0 => hA₂ ((Complex.cpow_eq_zero_iff _ _).1 h0).1)
    fun h0 => h1k ((Complex.cpow_eq_zero_iff _ _).1 h0).1) h

/-- (26.6): near a regular point `p₁` close to a zero of order `m`, with `ζ₁` a natural parameter at
`p₁`, one has `±ζ₁ = ζ^{m/2+1} + c` for a single valued branch of `ζ^{m/2+1}`, and the new
parameters satisfy `±ζ₁' = ζ'^{m/2+1} + c₁`.  In terms of branches: if `w² = ζ^{m+2}` then
`(teichStretch k w)² = ζ'^{m+2}`. -/
theorem eq26_6 (k : ℝ) (m : ℕ) {ζ w : ℂ} (hζ : ζ ≠ 0) (hw : w ^ 2 = ζ ^ (m + 2)) :
    teichStretch k w ^ 2 = teichStretchZero k m ζ ^ (m + 2) := by
  have hw0 : w ≠ 0 := by
    intro h
    exact pow_ne_zero (m + 2) hζ (by rw [← hw, h]; ring)
  have hnζ : (‖ζ‖ : ℂ) ≠ 0 := by simpa using hζ
  have hn : ‖w‖ ^ 2 = ‖ζ‖ ^ (m + 2) := by rw [← norm_pow, hw, norm_pow]
  -- conjugating `hw` and `w * conj w = ‖w‖²` give the key identity with no branch cut
  have h1 : (starRingEnd ℂ) w ^ 2 = (starRingEnd ℂ) ζ ^ (m + 2) := by
    rw [← map_pow, hw, map_pow]
  have h2 : w * (starRingEnd ℂ) w = ((‖ζ‖ : ℂ)) ^ (m + 2) := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hn]
    push_cast
    ring
  have hconjw : (starRingEnd ℂ) w
      = w * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2) := by
    rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hnζ), ← h2, ← h1]
    ring
  -- both sides are `(·) * A² / (1-k)²` for the same `A`, so no case split on `A = 0` is needed
  have hL : teichStretch k w ^ 2
      = w ^ 2 * (1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ^ 2
        / (1 - (k : ℂ)) ^ 2 := by
    unfold teichStretch
    rw [div_pow]
    congr 1
    rw [hconjw]
    ring
  have hR : teichStretchZero k m ζ ^ (m + 2)
      = ζ ^ (m + 2) * (1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ^ 2
        / (1 - (k : ℂ)) ^ 2 := by
    unfold teichStretchZero
    rw [if_neg hζ, div_pow, mul_pow, cpow_two_div_pow, cpow_two_div_pow]
  rw [hL, hR, hw]

/-- The exponent `2/(m+2)` of `teichStretchZero` is real. -/
theorem teichStretchZero_exponent_eq_ofReal (m : ℕ) :
    (2 : ℂ) / ((m : ℂ) + 2) = (((2 : ℝ) / ((m : ℝ) + 2) : ℝ) : ℂ) := by
  norm_num

/-- `|ζ'| = |ζ| (|1 + k (ζ̄/|ζ|)^{m+2}| / (1 - k))^{2/(m+2)}`, written with the two powers separately. -/
theorem norm_teichStretchZero {k : ℝ} (hk : k < 1) (m : ℕ) (ζ : ℂ) :
    ‖teichStretchZero k m ζ‖ = ‖ζ‖ *
      (‖1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)‖ ^ ((2 : ℝ) / ((m : ℝ) + 2)) /
        (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2))) := by
  by_cases hζ : ζ = 0
  · subst hζ
    simp [teichStretchZero]
  have h1k : (1 - (k : ℂ)) = ((1 - k : ℝ) : ℂ) := by simp
  unfold teichStretchZero
  rw [if_neg hζ, teichStretchZero_exponent_eq_ofReal, norm_div, norm_mul, Complex.norm_cpow_real, h1k,
    Complex.norm_cpow_real, Complex.norm_real, Real.norm_of_nonneg (by linarith), mul_div_assoc]

/-- The new parameter at a zero does not shrink distances to `0`: `|ζ| ≤ |ζ'|`. -/
theorem norm_le_norm_teichStretchZero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) (ζ : ℂ) :
    ‖ζ‖ ≤ ‖teichStretchZero k m ζ‖ := by
  by_cases hζ : ζ = 0
  · simp [hζ]
  rw [norm_teichStretchZero hk]
  have h1 : 1 - k ≤ ‖1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)‖ := by
    have hc := norm_conj_div_norm_pow hζ (m + 2)
    have h2 := norm_sub_norm_le (1 : ℂ) (-((k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one, norm_mul, hc, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hk₀] at h2
    exact h2
  have hpos : 0 < (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2)) := Real.rpow_pos_of_pos (by linarith) _
  refine le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hpos).2 ?_)
  exact Real.rpow_le_rpow (by linarith) h1 (by positivity)

/-- `|ζ'| ≤ |ζ| ((1 + k)/(1 - k))^{2/(m+2)}`, written with the two powers separately. -/
theorem norm_teichStretchZero_le {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) (ζ : ℂ) :
    ‖teichStretchZero k m ζ‖ ≤
      ‖ζ‖ * ((1 + k) ^ ((2 : ℝ) / ((m : ℝ) + 2)) / (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2))) := by
  by_cases hζ : ζ = 0
  · simp [hζ, teichStretchZero]
  rw [norm_teichStretchZero hk]
  have h1 : ‖1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)‖ ≤ 1 + k := by
    have hc := norm_conj_div_norm_pow hζ (m + 2)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, hc, mul_one, Complex.norm_real, Real.norm_of_nonneg hk₀]
  have hpos : 0 < (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2)) := Real.rpow_pos_of_pos (by linarith) _
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hpos.le) (norm_nonneg _)
  exact Real.rpow_le_rpow (norm_nonneg _) h1 (by positivity)

/-- Rotation by an `(m+2)`-th root of unity commutes with the new parameter. -/
theorem teichStretchZero_mul_of_pow_eq_one {k : ℝ} {m : ℕ} {ε : ℂ} (hε : ε ^ (m + 2) = 1) (ζ : ℂ) :
    teichStretchZero k m (ε * ζ) = ε * teichStretchZero k m ζ := by
  have hεn : ‖ε‖ = 1 := by
    have h := congrArg norm hε
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hεn
  by_cases hζ : ζ = 0
  · simp [teichStretchZero, hζ]
  have hc : ((starRingEnd ℂ) (ε * ζ) / (‖ε * ζ‖ : ℂ)) ^ (m + 2) =
      ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2) := by
    rw [map_mul, norm_mul, hεn, one_mul, mul_div_assoc, mul_pow, ← map_pow (starRingEnd ℂ) ε (m + 2),
      hε, map_one, one_mul]
  unfold teichStretchZero
  rw [if_neg (mul_ne_zero hε0 hζ), if_neg hζ, hc]
  ring

/-- The new parameter at a zero is positively homogeneous of degree one. -/
theorem teichStretchZero_ofReal_mul {k : ℝ} {m : ℕ} {r : ℝ} (hr : 0 < r) (ζ : ℂ) :
    teichStretchZero k m ((r : ℂ) * ζ) = r * teichStretchZero k m ζ := by
  by_cases hζ : ζ = 0
  · simp [teichStretchZero, hζ]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : (starRingEnd ℂ) ((r : ℂ) * ζ) / (‖(r : ℂ) * ζ‖ : ℂ) = (starRingEnd ℂ) ζ / (‖ζ‖ : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Complex.ofReal_mul, mul_div_mul_left _ _ hr0]
  unfold teichStretchZero
  rw [if_neg (mul_ne_zero hr0 hζ), if_neg hζ, hc]
  ring

/-- Continuity away from `0`: `1 + k (ζ̄/|ζ|)^{m+2}` has real part `≥ 1 - k > 0`, so the principal
power is continuous there. -/
theorem continuousAt_teichStretchZero_of_ne {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) {ζ₀ : ℂ}
    (hζ₀ : ζ₀ ≠ 0) : ContinuousAt (teichStretchZero k m) ζ₀ := by
  have hn : (‖ζ₀‖ : ℂ) ≠ 0 := by simpa using hζ₀
  have hg : ContinuousAt (fun ζ : ℂ => 1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ζ₀ :=
    continuousAt_const.add (continuousAt_const.mul
      ((Complex.continuous_conj.continuousAt.div
        (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt) hn).pow _))
  have hslit : 1 + (k : ℂ) * ((starRingEnd ℂ) ζ₀ / (‖ζ₀‖ : ℂ)) ^ (m + 2) ∈ slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    have hc := norm_conj_div_norm_pow hζ₀ (m + 2)
    have hre := Complex.abs_re_le_norm (((starRingEnd ℂ) ζ₀ / (‖ζ₀‖ : ℂ)) ^ (m + 2))
    rw [hc] at hre
    have h1 := (abs_le.1 hre).1
    simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
    nlinarith [mul_nonneg hk₀ (by linarith : (0 : ℝ) ≤
      (((starRingEnd ℂ) ζ₀ / (‖ζ₀‖ : ℂ)) ^ (m + 2)).re + 1)]
  have hcp : ContinuousAt (fun ζ : ℂ => (1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ^
      ((2 : ℂ) / ((m : ℂ) + 2))) ζ₀ :=
    ContinuousAt.comp (g := fun w : ℂ => w ^ ((2 : ℂ) / ((m : ℂ) + 2))) (continuousAt_cpow_const hslit) hg
  have hG : ContinuousAt (fun ζ : ℂ => ζ * (1 + (k : ℂ) * ((starRingEnd ℂ) ζ / (‖ζ‖ : ℂ)) ^ (m + 2)) ^
      ((2 : ℂ) / ((m : ℂ) + 2)) / ((1 - k : ℂ) ^ ((2 : ℂ) / ((m : ℂ) + 2)))) ζ₀ :=
    (continuousAt_id.mul hcp).div_const _
  refine hG.congr ?_
  filter_upwards [eventually_ne_nhds hζ₀] with ζ hζ
  rw [teichStretchZero, if_neg hζ]

/-- Continuity at `0`, from `|ζ'| ≤ C |ζ|`. -/
theorem continuousAt_teichStretchZero_zero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) :
    ContinuousAt (teichStretchZero k m) 0 := by
  have h0 : teichStretchZero k m 0 = 0 := by simp [teichStretchZero]
  rw [ContinuousAt, h0]
  have hlim : Tendsto (fun ζ : ℂ => ‖ζ‖ *
      ((1 + k) ^ ((2 : ℝ) / ((m : ℝ) + 2)) / (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2)))) (𝓝 0)
      (𝓝 (‖(0 : ℂ)‖ *
        ((1 + k) ^ ((2 : ℝ) / ((m : ℝ) + 2)) / (1 - k) ^ ((2 : ℝ) / ((m : ℝ) + 2))))) :=
    (continuous_norm.mul continuous_const).tendsto 0
  rw [norm_zero, zero_mul] at hlim
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) (fun ζ => norm_teichStretchZero_le hk₀ hk m ζ) hlim)

/-- The new parameter at a zero is a closed map: `|ζ| ≤ |ζ'|` makes it proper. -/
theorem isClosedMap_teichStretchZero {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ)
    (hcont : Continuous (teichStretchZero k m)) : IsClosedMap (teichStretchZero k m) := by
  refine (isProperMap_iff_tendsto_cocompact.2 ⟨hcont, ?_⟩).isClosedMap
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, tendsto_comap_iff]
  exact tendsto_atTop_mono (fun ζ => norm_le_norm_teichStretchZero hk₀ hk m ζ) tendsto_comap

/-- The new parameter at a zero is surjective.  For `y ≠ 0` with direction `d`, take `e² = d^{m+2}`
and `q = (e - k ē)/|e - k ē|`, so that `q + k q̄ = ((1 - k²)/|e - k ē|) e`.  An `(m+2)`-th root
`u₀` of `q²` then has `T(u₀)^{m+2} = ((1 + k)/|e - k ē|)² d^{m+2}`; a root of unity rotates `T(u₀)`
onto the ray of `y`, and a real factor scales it to `y`. -/
theorem teichStretchZero_surjective {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) :
    Function.Surjective (teichStretchZero k m) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [teichStretchZero, hy]⟩
  have hny : (‖y‖ : ℂ) ≠ 0 := by simpa using hy
  have h1k : (1 - (k : ℂ)) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  -- the direction `d` of `y`
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = y / (‖y‖ : ℂ) := ⟨_, rfl⟩
  have hdn : ‖d‖ = 1 := by
    rw [hd, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 hy)]
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hdn
  -- a square root `e` of `d^{m+2}`
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (d ^ (m + 2)) two_pos
  have hen : ‖e‖ = 1 := by
    have h := congrArg norm he
    rw [norm_pow, norm_pow, hdn, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  -- `q = (e - k ē)/N`
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ‖e - (k : ℂ) * (starRingEnd ℂ) e‖ := ⟨_, rfl⟩
  have hN : 0 < N := by
    have h := norm_sub_norm_le e ((k : ℂ) * (starRingEnd ℂ) e)
    rw [norm_mul, Complex.norm_conj, hen, mul_one, Complex.norm_real, Real.norm_of_nonneg hk₀,
      ← hNdef] at h
    linarith
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = (e - (k : ℂ) * (starRingEnd ℂ) e) / (N : ℂ) := ⟨_, rfl⟩
  have hqn : ‖q‖ = 1 := by
    rw [hqdef, norm_div, Complex.norm_real, Real.norm_of_nonneg hN.le, ← hNdef, div_self hN.ne']
  have hqq : q * (starRingEnd ℂ) q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hqn]
    norm_num
  have hqk : q + (k : ℂ) * (starRingEnd ℂ) q = (((1 - k ^ 2) / N : ℝ) : ℂ) * e := by
    rw [hqdef, map_div₀, Complex.conj_ofReal, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    push_cast
    field_simp
    ring
  -- an `(m+2)`-th root `u₀` of `q²`
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ 2) (by omega : 0 < m + 2)
  have hu₀n : ‖u₀‖ = 1 := by
    have h := congrArg norm hu₀
    rw [norm_pow, norm_pow, hqn, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    simp at hu₀n
  -- `T(u₀)^{m+2} = ((1 + k)/N)² d^{m+2}`
  have hT : teichStretchZero k m u₀ ^ (m + 2) = ((((1 + k) / N) ^ 2 : ℝ) : ℂ) * d ^ (m + 2) := by
    have h1 := teichStretchZero_pow_mul hk m hu₀0
    rw [hu₀n, Complex.ofReal_one, div_one, ← map_pow (starRingEnd ℂ) u₀ (m + 2), hu₀] at h1
    have h2 : q ^ 2 * (1 + (k : ℂ) * (starRingEnd ℂ) (q ^ 2)) ^ 2 =
        (q + (k : ℂ) * (starRingEnd ℂ) q) ^ 2 := by
      rw [map_pow]
      linear_combination (2 * (k : ℂ) * q * (starRingEnd ℂ) q +
        (k : ℂ) ^ 2 * (starRingEnd ℂ) q ^ 2 * (q * (starRingEnd ℂ) q + 1)) * hqq
    rw [h2, hqk, mul_pow, he] at h1
    refine mul_right_cancel₀ (pow_ne_zero 2 h1k) ?_
    rw [h1]
    push_cast
    field_simp
    ring
  -- rotate by a root of unity
  have hTu₀ := teichStretchZero_ne_zero hk₀ hk m hu₀0
  obtain ⟨t, htdef⟩ : ∃ t : ℂ, t = teichStretchZero k m u₀ := ⟨_, rfl⟩
  rw [← htdef] at hT hTu₀
  have hP : 0 < ((1 + k) / N) ^ 2 := pow_pos (div_pos (by linarith) hN) 2
  have htn : ‖t‖ ^ (m + 2) = ((1 + k) / N) ^ 2 := by
    have h := congrArg norm hT
    rw [norm_pow, norm_mul, norm_pow, hdn, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hP.le] at h
    exact h
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℂ, ε = (‖t‖ : ℂ) * d / t := ⟨_, rfl⟩
  have hεn : ε ^ (m + 2) = 1 := by
    rw [hεdef, div_pow, mul_pow, hT, ← Complex.ofReal_pow, htn]
    exact div_self (mul_ne_zero (Complex.ofReal_ne_zero.2 hP.ne') (pow_ne_zero _ hd0))
  have hTε : teichStretchZero k m (ε * u₀) = (‖t‖ : ℂ) * d := by
    rw [teichStretchZero_mul_of_pow_eq_one hεn, ← htdef, hεdef, div_mul_cancel₀ _ hTu₀]
  -- scale
  have hnt : (‖t‖ : ℂ) ≠ 0 := by simpa using hTu₀
  have hpos : 0 < ‖y‖ / ‖t‖ := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hTu₀)
  refine ⟨((‖y‖ / ‖t‖ : ℝ) : ℂ) * (ε * u₀), ?_⟩
  rw [teichStretchZero_ofReal_mul hpos, hTε, hd]
  push_cast
  field_simp

/-- §26.2: the new parameter at a zero is a homeomorphism of a neighbourhood of `0` onto a
neighbourhood of `0`, conformally compatible with the new parameters at nearby regular points.

Proof (no invariance of domain is needed): the map is continuous away from `0`, because
`1 + k (ζ̄/|ζ|)^{m+2}` has real part `≥ 1 - k > 0`, and at `0`, because
`|ζ'| ≤ |ζ| ((1 + k)/(1 - k))^{2/(m+2)}`.  Since `|ζ| ≤ |ζ'|` it is proper, hence a closed map.  It
is injective (`eq26_5_injective`) and surjective (`teichStretchZero_surjective`, by an explicit
preimage), so it maps an open `U` to `(T '' Uᶜ)ᶜ`, which is open. -/
theorem teichStretchZero_localHomeomorph {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) :
    Continuous (teichStretchZero k m) ∧ teichStretchZero k m 0 = 0 ∧
      ∀ U : Set ℂ, IsOpen U → IsOpen (teichStretchZero k m '' U) := by
  have hcont : Continuous (teichStretchZero k m) := continuous_iff_continuousAt.2 fun ζ₀ => by
    by_cases h : ζ₀ = 0
    · subst h
      exact continuousAt_teichStretchZero_zero hk₀ hk m
    · exact continuousAt_teichStretchZero_of_ne hk₀ hk m h
  have hbij : Function.Bijective (teichStretchZero k m) :=
    ⟨eq26_5_injective hk₀ hk m, teichStretchZero_surjective hk₀ hk m⟩
  refine ⟨hcont, by simp [teichStretchZero], fun U hU => ?_⟩
  rw [← compl_compl U, Set.image_compl_eq hbij]
  exact (isClosedMap_teichStretchZero hk₀ hk m hcont _ hU.isClosed_compl).isOpen_compl

/-- `p ∈ S₀` is a regular point of the quadratic differential `q`. -/
def IsRegularPoint (q : S₀ → ℂ → ℂ) (p : S₀) : Prop := q p (chartAt ℂ p p) ≠ 0

/-- `p ∈ S₀` is a zero of order `m` of the quadratic differential `q`. -/
def IsZeroOfOrder (q : S₀ → ℂ → ℂ) (p : S₀) (m : ℕ) : Prop :=
  meromorphicOrderAt (q p) (chartAt ℂ p p) = (m : ℤ)

/-- A natural parameter `ζ` of `q` at a regular point `p`, as a function of the preferred chart
coordinate: `ζ` is a local conformal coordinate at `φ_p(p)` with `ζ(φ_p(p)) = 0` and `q = ζ'²`
(so that `q dz² = dζ²`). -/
def IsNaturalParameterAt (q : S₀ → ℂ → ℂ) (p : S₀) (ζ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ ζ (chartAt ℂ p p) ∧ ζ (chartAt ℂ p p) = 0 ∧ deriv ζ (chartAt ℂ p p) ≠ 0 ∧
    ∀ᶠ z in 𝓝 (chartAt ℂ p p), deriv ζ z ^ 2 = q p z

/-- A natural parameter `ζ` of `q` at a zero `p` of order `m`: `q dz² = ((m+2)/2)² ζ^m dζ²`. -/
def IsNaturalParameterAtZero (q : S₀ → ℂ → ℂ) (p : S₀) (m : ℕ) (ζ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ ζ (chartAt ℂ p p) ∧ ζ (chartAt ℂ p p) = 0 ∧ deriv ζ (chartAt ℂ p p) ≠ 0 ∧
    ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2

/-! ### Helpers for `exists_teichDeformation` (`s26d_a_`): the Teichmüller deformation `S_{q,k}` -/

/-- `teichStretchZero k 0 = teichStretch k`: at a zero of order `0` (a regular point) the new parameter of
(26.5) is that of a regular point. -/
theorem s26d_a_teichStretchZero_zero (k : ℝ) : teichStretchZero k 0 = teichStretch k := by
  funext ζ
  unfold teichStretchZero teichStretch
  by_cases hζ : ζ = 0
  · simp [hζ]
  simp only [hζ, ite_false]
  have h1 : ((2 : ℂ) / (((0 : ℕ) : ℂ) + 2)) = 1 := by norm_num
  rw [h1, Complex.cpow_one, Complex.cpow_one]
  congr 1
  have hn : (‖ζ‖ : ℂ) ≠ 0 := by simpa using hζ
  have hDD : (‖ζ‖ : ℂ) ^ 2 = ζ * conj ζ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [div_pow, hDD]
  have hc : conj ζ ≠ 0 := by simpa using hζ
  field_simp
  ring

/-- `teichStretch k` is continuous. -/
theorem s26d_a_continuous_teichStretch (k : ℝ) : Continuous (teichStretch k) :=
  (continuous_id.add (continuous_const.mul Complex.continuous_conj)).div_const _

/-- The new parameter `teichStretchZero k m` at a zero of order `m` as a homeomorphism of `ℂ`
(`teichStretchZero_localHomeomorph`, `eq26_5_injective`, `teichStretchZero_surjective`). -/
def s26d_a_T {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) : ℂ ≃ₜ ℂ :=
  (Equiv.ofBijective (teichStretchZero k m)
      ⟨eq26_5_injective hk₀ hk m, teichStretchZero_surjective hk₀ hk m⟩).toHomeomorphOfContinuousOpen
    (teichStretchZero_localHomeomorph hk₀ hk m).1
    (fun U hU => (teichStretchZero_localHomeomorph hk₀ hk m).2.2 U hU)

/-- If `G² = ξ^{m+2}` near `s ≠ 0` for a holomorphic `G`, then `G'² = ((m+2)/2)² ξ^m` near `s`. -/
theorem s26d_a_deriv_sq {G : ℂ → ℂ} {m : ℕ} {s : ℂ} (hs : s ≠ 0) (hG : AnalyticAt ℂ G s)
    (hsq : ∀ᶠ ξ in 𝓝 s, G ξ ^ 2 = ξ ^ (m + 2)) :
    ∀ᶠ ξ in 𝓝 s, deriv G ξ ^ 2 = ((m + 2 : ℂ) / 2) ^ 2 * ξ ^ m := by
  filter_upwards [hG.eventually_analyticAt, eventually_eventually_nhds.2 hsq, eventually_ne_nhds hs]
    with ξ hGξ hsqξ hξ
  have h1 : HasDerivAt (fun η => G η ^ 2) (((2 : ℕ) : ℂ) * G ξ ^ (2 - 1) * deriv G ξ) ξ :=
    hGξ.differentiableAt.hasDerivAt.pow 2
  have h2 : HasDerivAt (fun η : ℂ => η ^ (m + 2)) (((m + 2 : ℕ) : ℂ) * ξ ^ (m + 2 - 1) * 1) ξ :=
    (hasDerivAt_id ξ).pow (m + 2)
  have h3 : ((2 : ℕ) : ℂ) * G ξ ^ (2 - 1) * deriv G ξ = ((m + 2 : ℕ) : ℂ) * ξ ^ (m + 2 - 1) * 1 := by
    have h4 := h1.congr_of_eventuallyEq (hsqξ.mono fun η hη => hη.symm)
    exact h2.unique h4 |>.symm
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h3
  push_cast at h3
  have hG2 : G ξ ^ 2 = ξ ^ (m + 2) := hsqξ.self_of_nhds
  have hne : ξ ^ (m + 2) * 4 ≠ 0 := mul_ne_zero (pow_ne_zero _ hξ) (by norm_num)
  refine mul_right_cancel₀ hne ?_
  have h5 : (2 * G ξ * deriv G ξ) ^ 2 = ((m + 2 : ℂ) * ξ ^ (m + 1)) ^ 2 := by
    rw [h3]
    ring
  linear_combination h5 - (4 * deriv G ξ ^ 2) * hG2

/-- **Matched branches of `ξ^{(m+2)/2}`** ((26.6)).  For `m = 0` or `s ≠ 0` there are `h` holomorphic at `s` with
`h'(ξ)² = ((m+2)/2)² ξ^m` near `s`, and `N` holomorphic at `u₀ = T(s)` (`T = teichStretchZero k m`) with
`N'(u₀) ≠ 0` and `N'(u)² = ((m+2)/2)² u^m` near `u₀`, such that `N ∘ T = S ∘ h` near `s` (`S = teichStretch k`).
For `m = 0` both are the identity; otherwise `h² = ξ^{m+2}`, and `S ∘ h ∘ T⁻¹` is a continuous square root of
`u^{m+2}` near `u₀ ≠ 0` (`eq26_6`), hence a holomorphic one. -/
theorem s26d_a_branches {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : ℕ) {s : ℂ} (hs : m = 0 ∨ s ≠ 0) :
    ∃ h N : ℂ → ℂ, AnalyticAt ℂ h s ∧ (∀ᶠ ξ in 𝓝 s, deriv h ξ ^ 2 = ((m + 2 : ℂ) / 2) ^ 2 * ξ ^ m) ∧
      AnalyticAt ℂ N (teichStretchZero k m s) ∧ deriv N (teichStretchZero k m s) ≠ 0 ∧
      (∀ᶠ u in 𝓝 (teichStretchZero k m s), deriv N u ^ 2 = ((m + 2 : ℂ) / 2) ^ 2 * u ^ m) ∧
      ∀ᶠ ξ in 𝓝 s, N (teichStretchZero k m ξ) = teichStretch k (h ξ) := by
  rcases hs with rfl | hs
  · refine ⟨id, id, analyticAt_id, Eventually.of_forall fun ξ => ?_, analyticAt_id, ?_,
      Eventually.of_forall fun u => ?_, Eventually.of_forall fun ξ => ?_⟩
    · rw [deriv_id]
      norm_num
    · rw [deriv_id]
      exact one_ne_zero
    · rw [deriv_id]
      norm_num
    · rw [s26d_a_teichStretchZero_zero]
      rfl
  set T : ℂ ≃ₜ ℂ := s26d_a_T hk₀ hk m with hTdef
  have hTa : ∀ ξ, T ξ = teichStretchZero k m ξ := fun ξ => rfl
  -- the branch `h` of `ξ^{(m+2)/2}` near `s`
  obtain ⟨h, hh, -, hhsq, -⟩ := exists_analyticAt_sq_eq (q := fun ξ : ℂ => ξ ^ (m + 2)) (a := s)
    (analyticAt_id.pow _) (pow_ne_zero _ hs)
  have hhd := s26d_a_deriv_sq hs hh (Eventually.of_forall hhsq)
  -- `u₀ = T s ≠ 0` and a holomorphic square root `R` of `u^{m+2}` near `u₀`
  set u₀ : ℂ := teichStretchZero k m s with hu₀
  have hu₀0 : u₀ ≠ 0 := teichStretchZero_ne_zero hk₀ hk m hs
  obtain ⟨R, hR, hR0, hRsq, -⟩ := exists_analyticAt_sq_eq (q := fun u : ℂ => u ^ (m + 2)) (a := u₀)
    (analyticAt_id.pow _) (pow_ne_zero _ hu₀0)
  -- `F = S ∘ h ∘ T⁻¹` squares to `u^{m+2}` near `u₀`
  set F : ℂ → ℂ := fun u => teichStretch k (h (T.symm u)) with hFdef
  have hTs : T.symm u₀ = s := by
    rw [hu₀, ← hTa, Homeomorph.symm_apply_apply]
  have hFc : ContinuousAt F u₀ := by
    have h1 : ContinuousAt h (T.symm u₀) := by rw [hTs]; exact hh.continuousAt
    exact (s26d_a_continuous_teichStretch k).continuousAt.comp (h1.comp T.symm.continuous.continuousAt)
  have hFsq : ∀ᶠ u in 𝓝 u₀, F u ^ 2 = u ^ (m + 2) := by
    have h1 : ∀ᶠ u in 𝓝 u₀, T.symm u ≠ 0 := by
      have h2 : ContinuousAt T.symm u₀ := T.symm.continuous.continuousAt
      rw [← hTs] at hs
      exact h2.eventually_ne hs
    filter_upwards [h1] with u hu
    have h3 := eq26_6 k m hu (hhsq (T.symm u))
    rw [← hTa, Homeomorph.apply_symm_apply] at h3
    exact h3
  -- choose the sign of `R` matching `F` at `u₀`
  obtain ⟨N, hN, hN0, hNsq, hNF⟩ : ∃ N : ℂ → ℂ, AnalyticAt ℂ N u₀ ∧ N u₀ ≠ 0 ∧
      (∀ u, N u ^ 2 = u ^ (m + 2)) ∧ N u₀ = F u₀ := by
    have h1 : F u₀ ^ 2 = R u₀ ^ 2 := by rw [hFsq.self_of_nhds, hRsq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact ⟨R, hR, hR0, hRsq, h2.symm⟩
    · refine ⟨fun u => -R u, hR.neg, neg_ne_zero.2 hR0, fun u => by rw [neg_sq, hRsq], ?_⟩
      show -R u₀ = F u₀
      rw [h2]
  -- `F = N` near `u₀`
  have hFN : ∀ᶠ u in 𝓝 u₀, F u = N u := by
    have h1 : ContinuousAt (fun u => F u + N u) u₀ := hFc.add hN.continuousAt
    have h2 : F u₀ + N u₀ ≠ 0 := by
      rw [← hNF, ← two_mul]
      exact mul_ne_zero two_ne_zero hN0
    filter_upwards [hFsq, h1.eventually_ne h2] with u hu1 hu2
    have h3 : (F u - N u) * (F u + N u) = 0 := by
      linear_combination hu1 - hNsq u
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hu2)
  have hNd := s26d_a_deriv_sq hu₀0 hN (Eventually.of_forall hNsq)
  have hNd0 : deriv N u₀ ≠ 0 := by
    intro h0
    have h1 := hNd.self_of_nhds
    rw [h0, zero_pow two_ne_zero] at h1
    have h2 : ((m + 2 : ℂ) / 2) ^ 2 * u₀ ^ m ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (div_ne_zero ?_ two_ne_zero)) (pow_ne_zero _ hu₀0)
      exact_mod_cast (by omega : (m + 2 : ℕ) ≠ 0)
    exact h2 h1.symm
  refine ⟨h, N, hh, hhd, hN, hNd0, hNd, ?_⟩
  have hTc : Tendsto (teichStretchZero k m) (𝓝 s) (𝓝 u₀) := T.continuous.tendsto s
  filter_upwards [hTc.eventually hFN] with ξ hξ
  rw [← hξ]
  simp only [hFdef]
  rw [← hTa, Homeomorph.symm_apply_apply]

/-- A continuous `g` such that `N ∘ g` is differentiable at `a`, with `N` holomorphic and `N' ≠ 0` at `g a`, is
differentiable at `a` (inverse function theorem: `g = N⁻¹ ∘ (N ∘ g)` near `a`). -/
theorem s26d_a_differentiableAt_of_comp {g N F : ℂ → ℂ} {a : ℂ} (hg : ContinuousAt g a)
    (hN : AnalyticAt ℂ N (g a)) (hN' : deriv N (g a) ≠ 0) (hF : DifferentiableAt ℂ F a)
    (hNg : ∀ᶠ w in 𝓝 a, N (g w) = F w) : DifferentiableAt ℂ g a := by
  have hs : HasStrictDerivAt N (deriv N (g a)) (g a) := hN.hasStrictDerivAt
  have hL : HasStrictDerivAt (hs.localInverse N (deriv N (g a)) (g a) hN') (deriv N (g a))⁻¹ (N (g a)) :=
    hs.to_localInverse hN'
  have hleft := hs.eventually_left_inverse hN'
  have hFa : F a = N (g a) := hNg.self_of_nhds.symm
  have hLF : DifferentiableAt ℂ (fun w => hs.localInverse N (deriv N (g a)) (g a) hN' (F w)) a := by
    refine DifferentiableAt.comp (g := hs.localInverse N (deriv N (g a)) (g a) hN') a ?_ hF
    rw [hFa]
    exact (HasStrictDerivAt.hasDerivAt hL).differentiableAt
  refine hLF.congr_of_eventuallyEq ?_
  filter_upwards [hg.eventually hleft, hNg] with w hw1 hw2
  rw [← hw2, hw1]

/-- (25.3) on the surface: two natural parameters `W`, `W'` at a regular point `x` (holomorphic in the preferred
chart at `x`, with squared derivative `q_x`) agree up to sign and an additive constant near `x`. -/
theorem s26d_a_natural_unique {q : S₀ → ℂ → ℂ} {x : S₀} (hx : IsRegularPoint q x) {W W' : S₀ → ℂ}
    (hW : AnalyticAt ℂ (fun z => W ((chartAt ℂ x).symm z)) (chartAt ℂ x x))
    (hWd : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W ((chartAt ℂ x).symm z)) z ^ 2 = q x z)
    (hW' : AnalyticAt ℂ (fun z => W' ((chartAt ℂ x).symm z)) (chartAt ℂ x x))
    (hWd' : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W' ((chartAt ℂ x).symm z)) z ^ 2 = q x z) :
    ∃ ε c : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ y in 𝓝 x, W y = ε * W' y + c := by
  have hxx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hG : AnalyticAt ℂ (fun z => W ((chartAt ℂ x).symm z) - W x) (chartAt ℂ x x) :=
    hW.sub analyticAt_const
  have hG' : AnalyticAt ℂ (fun z => W' ((chartAt ℂ x).symm z) - W' x) (chartAt ℂ x x) :=
    hW'.sub analyticAt_const
  have hGd : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W ((chartAt ℂ x).symm z) - W x) z ^ 2 = q x z :=
    hWd.mono fun z hz => by rw [deriv_sub_const]; exact hz
  have hGd' : ∀ᶠ z in 𝓝 (chartAt ℂ x x), deriv (fun z => W' ((chartAt ℂ x).symm z) - W' x) z ^ 2 = q x z :=
    hWd'.mono fun z hz => by rw [deriv_sub_const]; exact hz
  have key := eq25_3_natural_parameter_unique hG hG' (by simp only [hxx, sub_self])
    (by simp only [hxx, sub_self]) hGd hGd' hx
  have hφ : Tendsto (chartAt ℂ x) (𝓝 x) (𝓝 (chartAt ℂ x x)) :=
    ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).tendsto
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  rcases key with h | h
  · refine ⟨1, W x - W' x, Or.inl rfl, ?_⟩
    filter_upwards [hφ.eventually h, hsrc] with y hy hys
    simp only [(chartAt ℂ x).left_inv hys] at hy
    linear_combination hy
  · refine ⟨-1, W x + W' x, Or.inr rfl, ?_⟩
    filter_upwards [hφ.eventually h, hsrc] with y hy hys
    simp only [(chartAt ℂ x).left_inv hys] at hy
    linear_combination hy

/-- The transformation law of a holomorphic quadratic differential `q`, specialised: for `z` in the
chart target at `x` with `p = φ_x⁻¹ z` in the chart source at `y`, `q_x(z) = q_y(τ z) τ'(z)²`,
`τ = φ_y ∘ φ_x⁻¹`. -/
theorem s26d_a_law {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source) :
    q x z = q y (chartTransition y x z) * deriv (chartTransition y x) z ^ 2 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  rw [hq'.1.2 y x z hz hzy]
  norm_num

/-- Regularity in an arbitrary chart: for `z` in the chart target at `x`, the point `φ_x⁻¹ z` is a
regular point of `q` (a condition in the preferred chart at that point) iff `q_x(z) ≠ 0` (the
transformation law in both directions). -/
theorem s26d_a_isRegularPoint_iff {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    IsRegularPoint q ((chartAt ℂ x).symm z) ↔ q x z ≠ 0 := by
  set p := (chartAt ℂ x).symm z with hp
  have hpx : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  constructor
  · intro hr h0
    have hw : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hwp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hlaw := s26d_a_law hq p x hw (by rw [hwp]; exact hpx)
    have hT : chartTransition x p (chartAt ℂ p p) = z := by
      show chartAt ℂ x ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [hwp]
      exact (chartAt ℂ x).right_inv hz
    rw [hT, h0, zero_mul] at hlaw
    exact hr hlaw
  · intro hne h0
    apply hne
    have hlaw := s26d_a_law hq x p hz (mem_chart_source ℂ p)
    have hT : chartTransition p x z = chartAt ℂ p p := rfl
    rw [hlaw, hT, h0, zero_mul]

/-- If regular points of `q` accumulate at `φ_x⁻¹ z`, then `q_x` has no zeros in a punctured
neighbourhood of `z` (isolated zeros of the holomorphic `q_x`). -/
theorem s26d_a_eventually_ne_zero {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hfr : ∃ᶠ p in 𝓝 ((chartAt ℂ x).symm z), IsRegularPoint q p) :
    ∀ᶠ w in 𝓝[≠] z, q x w ≠ 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have han : AnalyticAt ℂ (q x) z := (hq'.2 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds hz)
  refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
  have hpx : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcont : Tendsto (chartAt ℂ x) (𝓝 ((chartAt ℂ x).symm z)) (𝓝 z) := by
    have h := ((chartAt ℂ x).continuousAt hpx).tendsto
    rwa [(chartAt ℂ x).right_inv hz] at h
  refine hfr ?_
  filter_upwards [hcont.eventually h0, (chartAt ℂ x).open_source.mem_nhds hpx] with p' hp' hsrc hreg
  have h1 := (s26d_a_isRegularPoint_iff hq x ((chartAt ℂ x).map_source hsrc)).1
    (by rw [(chartAt ℂ x).left_inv hsrc]; exact hreg)
  exact h1 hp'

/-- On a connected (T1) surface, regular points of a holomorphic quadratic differential `q ≠ 0`
accumulate at every point: the set of points near which no point is regular is clopen
(`s26d_a_eventually_ne_zero`), and if it were everything then `q = 0` (`s26d_a_isRegularPoint_iff`). -/
theorem s26d_a_frequently_regular [ConnectedSpace S₀] [T1Space S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S₀) : ∃ᶠ p' in 𝓝 p, IsRegularPoint q p' := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set B : Set S₀ := {p | ∀ᶠ p' in 𝓝 p, ¬ IsRegularPoint q p'} with hBdef
  have hBo : IsOpen B := isOpen_setOfPred_eventually_nhds
  have hBc : IsClosed B := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p₀ hp₀
    have hfr : ∃ᶠ p' in 𝓝 p₀, IsRegularPoint q p' := hp₀
    have hsrc : (chartAt ℂ p₀).source ∈ 𝓝 p₀ :=
      (chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀)
    have hl : (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀) = p₀ :=
      (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)
    have hw := s26d_a_eventually_ne_zero hq p₀ ((chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀))
      (by rw [hl]; exact hfr)
    have ht : Tendsto (chartAt ℂ p₀) (𝓝[≠] p₀) (𝓝[≠] (chartAt ℂ p₀ p₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hsrc] with p' hp' hne'
      exact fun heq => hne' ((chartAt ℂ p₀).injOn hp' (mem_chart_source ℂ p₀) heq)
    have hpunct : ∀ᶠ p' in 𝓝 p₀, p' ≠ p₀ → IsRegularPoint q p' := by
      have h2 := ht.eventually hw
      rw [eventually_nhdsWithin_iff] at h2
      filter_upwards [h2, hsrc] with p' h1 h3 hne'
      have h4 := (s26d_a_isRegularPoint_iff hq p₀ ((chartAt ℂ p₀).map_source h3)).2 (h1 hne')
      rwa [(chartAt ℂ p₀).left_inv h3] at h4
    filter_upwards [eventually_eventually_nhds.2 hpunct] with p₁ hp₁
    by_cases hp₁₀ : p₁ = p₀
    · rw [hp₁₀]
      exact hp₀
    · show ∃ᶠ p' in 𝓝 p₁, IsRegularPoint q p'
      refine Eventually.frequently ?_
      filter_upwards [hp₁, eventually_ne_nhds hp₁₀] with p'' h1 h2 using h1 h2
  rcases isClopen_iff.1 ⟨hBc, hBo⟩ with hB | hB
  · intro hp
    have hpB : p ∈ B := hp
    rw [hB] at hpB
    exact hpB
  · exfalso
    apply hne
    funext x z
    show q x z = 0
    by_cases hz : z ∈ (chartAt ℂ x).target
    · have hB' : (chartAt ℂ x).symm z ∈ B := by
        rw [hB]
        exact mem_univ _
      by_contra h0
      exact hB'.self_of_nhds ((s26d_a_isRegularPoint_iff hq x hz).2 h0)
    · exact hq'.1.1 x z hz


/-- **Chart data at `p`** (§26.2): the order `m` of `q` at `p`, a natural parameter `ζ` of (25.2)/(25.5) at `p`, and
the local homeomorphism `Z` of `ℂ` given by `ζ` on an open neighbourhood of `φ_p(p)` inside the chart target on
which `ζ` is holomorphic, `q_p = ((m+2)/2)² ζ^m ζ'²`, and `q_p` vanishes at most at `φ_p(p)`. -/
structure s26d_a_Data (q : S₀ → ℂ → ℂ) (p : S₀) (m : ℕ) (ζ : ℂ → ℂ) (Z : OpenPartialHomeomorph ℂ ℂ) :
    Prop where
  order : IsZeroOfOrder q p m
  regular_iff : IsRegularPoint q p ↔ m = 0
  natural : IsNaturalParameterAtZero q p m ζ
  coe : ⇑Z = ζ
  center : chartAt ℂ p p ∈ Z.source
  source_sub : Z.source ⊆ (chartAt ℂ p).target
  analytic : ∀ z ∈ Z.source, AnalyticAt ℂ ζ z
  identity : ∀ z ∈ Z.source, q p z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2
  ne_zero : ∀ z ∈ Z.source, z ≠ chartAt ℂ p p → q p z ≠ 0

/-- Chart data exist at every point of a connected surface: `q_p` does not vanish identically near `φ_p(p)`
(`s26d_a_frequently_regular`), so it has a finite order `m` there and a natural parameter by (25.2) (`m = 0`) or
(25.5) (`m > 0`), which is a local homeomorphism near `φ_p(p)` (inverse function theorem). -/
theorem s26d_a_data_exists [T2Space S₀] [ConnectedSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) (p : S₀) : ∃ (m : ℕ) (ζ : ℂ → ℂ) (Z : OpenPartialHomeomorph ℂ ℂ), s26d_a_Data q p m ζ Z := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set z₀ := chartAt ℂ p p with hz₀def
  have hz₀ : z₀ ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have han : AnalyticAt ℂ (q p) z₀ := (hq'.2 p).analyticAt ((chartAt ℂ p).open_target.mem_nhds hz₀)
  have hl : (chartAt ℂ p).symm z₀ = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hpunct : ∀ᶠ w in 𝓝[≠] z₀, q p w ≠ 0 :=
    s26d_a_eventually_ne_zero hq p hz₀ (by rw [hl]; exact s26d_a_frequently_regular hq hne p)
  have hnz : ¬ ∀ᶠ z in 𝓝 z₀, q p z = 0 := by
    intro h
    obtain ⟨z, hz1, hz2⟩ := ((h.filter_mono nhdsWithin_le_nhds).and hpunct).exists
    exact hz2 hz1
  obtain ⟨n, g, hg, hg0, hfg⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hfg
  have hord : IsZeroOfOrder q p n := by
    show meromorphicOrderAt (q p) z₀ = (n : ℤ)
    rw [meromorphicOrderAt_eq_int_iff han.meromorphicAt]
    refine ⟨g, hg, hg0, (hfg.filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_⟩
    rw [hz, zpow_natCast, smul_eq_mul]
  have hval : q p z₀ = (z₀ - z₀) ^ n * g z₀ := hfg.self_of_nhds
  have hreg : IsRegularPoint q p ↔ n = 0 := by
    show q p z₀ ≠ 0 ↔ n = 0
    rw [hval, sub_self]
    constructor
    · intro h
      by_contra hn
      exact h (by rw [zero_pow hn, zero_mul])
    · intro hn
      rw [hn, pow_zero, one_mul]
      exact hg0
  -- a natural parameter
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ → ℂ, IsNaturalParameterAtZero q p n ζ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain ⟨ζ, h1, h2, h3, h4⟩ := eq25_2_natural_parameter han (hreg.2 rfl)
      refine ⟨ζ, h1, h2, h3, h4.mono fun z hz => ?_⟩
      rw [← hz]
      norm_num
    · exact eq25_5_natural_parameter_zero hn hg hg0 hfg
  obtain ⟨hζa, hζ0, hζd, hζid⟩ := hζ
  -- the inverse function theorem at `z₀`
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ hζd)
  have hfd : HasStrictFDerivAt ζ i.toContinuousLinearMap z₀ := hζa.hasStrictDerivAt
  have hsrc : z₀ ∈ (hfd.toOpenPartialHomeomorph ζ).source := hfd.mem_toOpenPartialHomeomorph_source
  -- the good neighbourhood
  have hG : {z | z ∈ (chartAt ℂ p).target ∧ AnalyticAt ℂ ζ z ∧
      q p z = ((n + 2 : ℂ) / 2) ^ 2 * ζ z ^ n * deriv ζ z ^ 2 ∧ (z ≠ z₀ → q p z ≠ 0)} ∈ 𝓝 z₀ := by
    filter_upwards [(chartAt ℂ p).open_target.mem_nhds hz₀, hζa.eventually_analyticAt, hζid,
      eventually_nhdsWithin_iff.1 hpunct] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨V, hVG, hVo, hz₀V⟩ := _root_.mem_nhds_iff.1 hG
  refine ⟨n, ζ, (hfd.toOpenPartialHomeomorph ζ).restrOpen V hVo, ⟨hord, hreg, ⟨hζa, hζ0, hζd, hζid⟩,
    hfd.toOpenPartialHomeomorph_coe, ⟨hsrc, hz₀V⟩, fun z hz => (hVG hz.2).1, fun z hz => (hVG hz.2).2.1,
    fun z hz => (hVG hz.2).2.2.1, fun z hz => (hVG hz.2).2.2.2⟩⟩

/-- **The new chart at `p`** (§26.2): `ψ_p = T_{k,m_p} ∘ ζ_p ∘ φ_p` on `φ_p⁻¹(Z_p.source)`, where `Z_p` is the
natural parameter `ζ_p` on its domain and `T_{k,m}` the homeomorphism `teichStretchZero k m`. -/
def s26d_a_psi {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : S₀ → ℕ) (Z : S₀ → OpenPartialHomeomorph ℂ ℂ) (p : S₀) :
    OpenPartialHomeomorph S₀ ℂ :=
  ((chartAt ℂ p).trans (Z p)).transHomeomorph (s26d_a_T hk₀ hk (m p))

/-- The new chart at `p` is `teichStretchZero k m_p ∘ Z_p ∘ φ_p`. -/
theorem s26d_a_psi_apply {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : S₀ → ℕ) (Z : S₀ → OpenPartialHomeomorph ℂ ℂ)
    (p y : S₀) : s26d_a_psi hk₀ hk m Z p y = teichStretchZero k (m p) (Z p (chartAt ℂ p y)) := rfl

/-- The source of the new chart at `p` is `φ_p⁻¹(Z_p.source)`. -/
theorem s26d_a_psi_source {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (m : S₀ → ℕ) (Z : S₀ → OpenPartialHomeomorph ℂ ℂ)
    (p y : S₀) :
    y ∈ (s26d_a_psi hk₀ hk m Z p).source ↔ y ∈ (chartAt ℂ p).source ∧ chartAt ℂ p y ∈ (Z p).source :=
  Iff.rfl

/-- `p` lies in the source of its new chart, and `ψ_p(p) = 0`. -/
theorem s26d_a_psi_center {q : S₀ → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ}
    {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p))
    (p : S₀) : p ∈ (s26d_a_psi hk₀ hk m Z p).source ∧ s26d_a_psi hk₀ hk m Z p p = 0 := by
  refine ⟨⟨mem_chart_source ℂ p, (hD p).center⟩, ?_⟩
  rw [s26d_a_psi_apply, (hD p).coe, (hD p).natural.2.1]
  simp [teichStretchZero]

/-- In the chart `φ_p`, the new chart at `p` is `teichStretchZero k m_p ∘ ζ_p`. -/
theorem s26d_a_psi_chart {q : S₀ → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ}
    {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ} (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p))
    (p : S₀) {z : ℂ} (hz : z ∈ (chartAt ℂ p).target) :
    s26d_a_psi hk₀ hk m Z p ((chartAt ℂ p).symm z) = teichStretchZero k (m p) (ζ p z) := by
  rw [s26d_a_psi_apply, (hD p).coe, (chartAt ℂ p).right_inv hz]

/-- A point `x ≠ p` of the new chart at `p` is a regular point of `q`. -/
theorem s26d_a_regular_of_mem {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ}
    (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p)) (p : S₀) {x : S₀}
    (hx : x ∈ (s26d_a_psi hk₀ hk m Z p).source) (hxp : x ≠ p) : IsRegularPoint q x := by
  obtain ⟨hx1, hx2⟩ := (s26d_a_psi_source hk₀ hk m Z p x).1 hx
  have hne : chartAt ℂ p x ≠ chartAt ℂ p p := fun h =>
    hxp ((chartAt ℂ p).injOn hx1 (mem_chart_source ℂ p) h)
  have h1 := (s26d_a_isRegularPoint_iff hq p ((chartAt ℂ p).map_source hx1)).2
    ((hD p).ne_zero _ hx2 hne)
  rwa [(chartAt ℂ p).left_inv hx1] at h1

/-- At a regular point `x` of the new chart at `p`, either `m_p = 0` or `ζ_p(φ_p x) ≠ 0`. -/
theorem s26d_a_ne_zero_of_mem {q : S₀ → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ}
    (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p)) (p : S₀) {x : S₀}
    (hx : x ∈ (s26d_a_psi hk₀ hk m Z p).source) (hreg : IsRegularPoint q x) :
    m p = 0 ∨ ζ p (chartAt ℂ p x) ≠ 0 := by
  by_cases hm : m p = 0
  · exact Or.inl hm
  right
  obtain ⟨hx1, hx2⟩ := (s26d_a_psi_source hk₀ hk m Z p x).1 hx
  have hxp : x ≠ p := by
    rintro rfl
    exact hm ((hD x).regular_iff.1 hreg)
  have hne : chartAt ℂ p x ≠ chartAt ℂ p p := fun h =>
    hxp ((chartAt ℂ p).injOn hx1 (mem_chart_source ℂ p) h)
  intro h0
  apply hne
  have hinj := (Z p).injOn hx2 (hD p).center
  rw [(hD p).coe] at hinj
  exact hinj (by rw [h0, (hD p).natural.2.1])

/-- **Natural parameters from the new charts.**  For a regular point `x` of the new chart at `p` and a branch `h`
with `h'(ξ)² = ((m+2)/2)² ξ^m` near `ζ_p(φ_p x)`, the function `W = h ∘ ζ_p ∘ φ_p` is a natural parameter of `q` at
`x`: in the chart `φ_x`, `W ∘ φ_x⁻¹` is holomorphic at `φ_x(x)` with `(W ∘ φ_x⁻¹)'² = q_x` (transformation law). -/
theorem s26d_a_W_natural [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {p : S₀} {m : ℕ}
    {ζ : ℂ → ℂ} {Z : OpenPartialHomeomorph ℂ ℂ} (hD : s26d_a_Data q p m ζ Z) {x : S₀}
    (hx : x ∈ (chartAt ℂ p).source) (hxZ : chartAt ℂ p x ∈ Z.source) {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h (ζ (chartAt ℂ p x)))
    (hhd : ∀ᶠ ξ in 𝓝 (ζ (chartAt ℂ p x)), deriv h ξ ^ 2 = ((m + 2 : ℂ) / 2) ^ 2 * ξ ^ m) :
    AnalyticAt ℂ (fun z => h (ζ (chartAt ℂ p ((chartAt ℂ x).symm z)))) (chartAt ℂ x x) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ x x),
        deriv (fun z => h (ζ (chartAt ℂ p ((chartAt ℂ x).symm z)))) z ^ 2 = q x z := by
  have hzx : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hxx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hO : (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (chartAt ℂ x x) :=
    ((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds
      ⟨hzx, by rw [mem_preimage, hxx]; exact hx⟩
  have hτd : ∀ z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source,
      DifferentiableAt ℂ (chartTransition p x) z := fun z hz =>
    s23_transition_differentiableAt p x hz.1 hz.2
  have hτa : AnalyticAt ℂ (chartTransition p x) (chartAt ℂ x x) :=
    DifferentiableOn.analyticAt (fun z hz => (hτd z hz).differentiableWithinAt) hO
  have hτzx : chartTransition p x (chartAt ℂ x x) = chartAt ℂ p x := by
    show chartAt ℂ p ((chartAt ℂ x).symm (chartAt ℂ x x)) = chartAt ℂ p x
    rw [hxx]
  have hζa : AnalyticAt ℂ ζ (chartTransition p x (chartAt ℂ x x)) := by
    rw [hτzx]
    exact hD.analytic _ hxZ
  have hha : AnalyticAt ℂ h (ζ (chartTransition p x (chartAt ℂ x x))) := by
    rw [hτzx]
    exact hh
  refine ⟨AnalyticAt.comp (g := h) (f := ζ ∘ chartTransition p x) hha (hζa.comp hτa), ?_⟩
  have hτt : Tendsto (chartTransition p x) (𝓝 (chartAt ℂ x x)) (𝓝 (chartAt ℂ p x)) := by
    rw [← hτzx]
    exact hτa.continuousAt.tendsto
  have hζt : Tendsto (fun z => ζ (chartTransition p x z)) (𝓝 (chartAt ℂ x x)) (𝓝 (ζ (chartAt ℂ p x))) :=
    (hD.analytic _ hxZ).continuousAt.tendsto.comp hτt
  filter_upwards [hO, hτt.eventually (Z.open_source.mem_nhds hxZ), hζt.eventually hhd,
    hζt.eventually hh.eventually_analyticAt] with z hzO hzZ hzh hzha
  have hζz := hD.analytic _ hzZ
  have hd : HasDerivAt (fun z => h (ζ (chartAt ℂ p ((chartAt ℂ x).symm z))))
      (deriv h (ζ (chartTransition p x z)) * (deriv ζ (chartTransition p x z) *
        deriv (chartTransition p x) z)) z :=
    hzha.differentiableAt.hasDerivAt.comp z (hζz.differentiableAt.hasDerivAt.comp z (hτd z hzO).hasDerivAt)
  rw [hd.deriv, s26d_a_law hq x p hzO.1 hzO.2, hD.identity _ hzZ, mul_pow, mul_pow, hzh]
  ring

/-- **Transitions of the new atlas.**  At a point `w` of `ψ_{p'}(U_p ∩ U_{p'})` the transition `τ = ψ_p ∘ ψ_{p'}⁻¹`
is holomorphic, and the coefficients `((m+2)/2)² u^m` transform as a quadratic differential:
`((m'+2)/2)² w^{m'} = ((m+2)/2)² τ(w)^m τ'(w)²`.  At a zero `x = ψ_{p'}⁻¹ w` of `q` the two charts coincide
(`p = x = p'`); at a regular point the matched branches `N`, `N'` of `u^{(m+2)/2}` (`s26d_a_branches`) satisfy
`N ∘ τ = ±N' + c`: the natural parameters `h ∘ ζ_p ∘ φ_p` agree up to sign and a constant ((25.3)), and
`teichStretch k` is real-linear ((26.4)). -/
theorem s26d_a_transition [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) {m : S₀ → ℕ} {ζ : S₀ → ℂ → ℂ} {Z : S₀ → OpenPartialHomeomorph ℂ ℂ}
    (hD : ∀ p, s26d_a_Data q p (m p) (ζ p) (Z p)) (p p' : S₀) {w : ℂ}
    (hw : w ∈ (s26d_a_psi hk₀ hk m Z p').target)
    (hwp : (s26d_a_psi hk₀ hk m Z p').symm w ∈ (s26d_a_psi hk₀ hk m Z p).source) :
    DifferentiableAt ℂ (fun w => s26d_a_psi hk₀ hk m Z p ((s26d_a_psi hk₀ hk m Z p').symm w)) w ∧
      ((m p' + 2 : ℂ) / 2) ^ 2 * w ^ m p' =
        ((m p + 2 : ℂ) / 2) ^ 2 * s26d_a_psi hk₀ hk m Z p ((s26d_a_psi hk₀ hk m Z p').symm w) ^ m p *
          deriv (fun w => s26d_a_psi hk₀ hk m Z p ((s26d_a_psi hk₀ hk m Z p').symm w)) w ^ 2 := by
  set ψ := s26d_a_psi hk₀ hk m Z with hψ
  set x := (ψ p').symm w with hxdef
  have hxp' : x ∈ (ψ p').source := (ψ p').map_target hw
  have hwx : ψ p' x = w := (ψ p').right_inv hw
  by_cases hreg : IsRegularPoint q x
  swap
  · -- at a zero of `q` the two charts coincide
    have h1 : x = p := by
      by_contra h
      exact hreg (s26d_a_regular_of_mem hq hk₀ hk hD p hwp h)
    have h2 : x = p' := by
      by_contra h
      exact hreg (s26d_a_regular_of_mem hq hk₀ hk hD p' hxp' h)
    have hpp : p = p' := h1.symm.trans h2
    subst hpp
    have hid : (fun v => ψ p ((ψ p).symm v)) =ᶠ[𝓝 w] fun v => v := by
      filter_upwards [(ψ p).open_target.mem_nhds hw] with v hv
      exact (ψ p).right_inv hv
    have hd : deriv (fun v => ψ p ((ψ p).symm v)) w = 1 := by
      rw [hid.deriv_eq, deriv_id'']
    refine ⟨differentiableAt_id.congr_of_eventuallyEq hid, ?_⟩
    rw [hd, hwx]
    ring
  -- a regular point `x`
  obtain ⟨hx1, hx2⟩ := (s26d_a_psi_source hk₀ hk m Z p x).1 hwp
  obtain ⟨hx1', hx2'⟩ := (s26d_a_psi_source hk₀ hk m Z p' x).1 hxp'
  obtain ⟨h, N, hh, hhd, hN, hNd0, hNd, hNT⟩ :=
    s26d_a_branches hk₀ hk (m p) (s26d_a_ne_zero_of_mem hk₀ hk hD p hwp hreg)
  obtain ⟨h', N', hh', hhd', hN', -, hNd', hNT'⟩ :=
    s26d_a_branches hk₀ hk (m p') (s26d_a_ne_zero_of_mem hk₀ hk hD p' hxp' hreg)
  obtain ⟨hWa, hWd⟩ := s26d_a_W_natural hq (hD p) hx1 hx2 hh hhd
  obtain ⟨hWa', hWd'⟩ := s26d_a_W_natural hq (hD p') hx1' hx2' hh' hhd'
  obtain ⟨ε, c, hε, hWW⟩ := s26d_a_natural_unique (W := fun y => h (ζ p (chartAt ℂ p y)))
    (W' := fun y => h' (ζ p' (chartAt ℂ p' y))) hreg hWa hWd hWa' hWd'
  -- `N ∘ ψ_p = S ∘ W` and `N' ∘ ψ_{p'} = S ∘ W'` near `x`
  have hNψ : ∀ (p₁ : S₀) (h₁ N₁ : ℂ → ℂ), x ∈ (chartAt ℂ p₁).source → chartAt ℂ p₁ x ∈ (Z p₁).source →
      (∀ᶠ ξ in 𝓝 (ζ p₁ (chartAt ℂ p₁ x)), N₁ (teichStretchZero k (m p₁) ξ) = teichStretch k (h₁ ξ)) →
      ∀ᶠ y in 𝓝 x, N₁ (ψ p₁ y) = teichStretch k (h₁ (ζ p₁ (chartAt ℂ p₁ y))) := by
    intro p₁ h₁ N₁ hy1 hy2 hT
    have hc : Tendsto (fun y => ζ p₁ (chartAt ℂ p₁ y)) (𝓝 x) (𝓝 (ζ p₁ (chartAt ℂ p₁ x))) :=
      ((hD p₁).analytic _ hy2).continuousAt.tendsto.comp ((chartAt ℂ p₁).continuousAt hy1).tendsto
    filter_upwards [hc.eventually hT] with y hy
    rw [hψ, s26d_a_psi_apply, (hD p₁).coe]
    exact hy
  have hrel : ∀ᶠ y in 𝓝 x, N (ψ p y) = ε * N' (ψ p' y) + teichStretch k c := by
    filter_upwards [hNψ p h N hx1 hx2 hNT, hNψ p' h' N' hx1' hx2' hNT', hWW] with y h1 h2 h3
    rw [h1, h2, ← eq26_4 k ε hε]
    exact congrArg (teichStretch k) h3
  -- transport to `w`
  have hrelw : ∀ᶠ v in 𝓝 w, N (ψ p ((ψ p').symm v)) = ε * N' v + teichStretch k c := by
    filter_upwards [((ψ p').continuousAt_symm hw).tendsto.eventually hrel,
      (ψ p').open_target.mem_nhds hw] with v hv1 hv2
    rw [(ψ p').right_inv hv2] at hv1
    exact hv1
  have hψx : ψ p x = teichStretchZero k (m p) (ζ p (chartAt ℂ p x)) := by
    rw [hψ, s26d_a_psi_apply, (hD p).coe]
  have hψx' : w = teichStretchZero k (m p') (ζ p' (chartAt ℂ p' x)) := by
    rw [← hwx, hψ, s26d_a_psi_apply, (hD p').coe]
  have hτc : ContinuousAt (fun v => ψ p ((ψ p').symm v)) w :=
    ContinuousAt.comp (g := ψ p) (f := (ψ p').symm) ((ψ p).continuousAt hwp) ((ψ p').continuousAt_symm hw)
  have hN1 : AnalyticAt ℂ N (ψ p x) := by rw [hψx]; exact hN
  have hN2 : deriv N (ψ p x) ≠ 0 := by rw [hψx]; exact hNd0
  have hN'w : AnalyticAt ℂ N' w := by rw [hψx']; exact hN'
  have hF : HasDerivAt (fun v => ε * N' v + teichStretch k c) (ε * deriv N' w) w :=
    (hN'w.differentiableAt.hasDerivAt.const_mul ε).add_const _
  have hdiff := s26d_a_differentiableAt_of_comp hτc hN1 hN2 hF.differentiableAt hrelw
  refine ⟨hdiff, ?_⟩
  have hcomp : HasDerivAt (fun v => N (ψ p ((ψ p').symm v)))
      (deriv N (ψ p x) * deriv (fun v => ψ p ((ψ p').symm v)) w) w :=
    hN1.differentiableAt.hasDerivAt.comp w hdiff.hasDerivAt
  have huniq := hcomp.unique (hF.congr_of_eventuallyEq hrelw)
  have e1 : deriv N (ψ p x) ^ 2 = ((m p + 2 : ℂ) / 2) ^ 2 * (ψ p x) ^ m p := by
    rw [hψx]
    exact hNd.self_of_nhds
  have e2 : deriv N' w ^ 2 = ((m p' + 2 : ℂ) / 2) ^ 2 * w ^ m p' := by
    have h1 := hNd'.self_of_nhds
    rw [← hψx'] at h1
    exact h1
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  linear_combination -e2 + deriv (fun v => ψ p ((ψ p').symm v)) w ^ 2 * e1 - deriv N' w ^ 2 * hε2 -
    (deriv N (ψ p x) * deriv (fun v => ψ p ((ψ p').symm v)) w + ε * deriv N' w) * huniq


/-- The carrier of the deformed surface: a type synonym of `Y` (so that no instance of `Y` applies to it). -/
def s26d_a_X (Y : Type u) : Type u := Y

/-- **Packaging.**  A family of charts `ψ p` of `Y` (`p ∈ (ψ p).source`) with holomorphic transitions, and a
family `Q` of coefficients obeying the transformation law of quadratic differentials in these charts, define a
closed Riemann surface `X` (the synonym `s26d_a_X Y` with the atlas `{ψ p}`) homeomorphic to `Y` by `e` (the
identity of the point set), with preferred charts `ψ p`, and a holomorphic quadratic differential `q'` on it with
coefficients `Q`. -/
theorem s26d_a_package {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [CompactSpace Y]
    (ψ : Y → OpenPartialHomeomorph Y ℂ) (hmem : ∀ p, p ∈ (ψ p).source)
    (hcompat : ∀ p p', ∀ w ∈ (ψ p').target, (ψ p').symm w ∈ (ψ p).source →
      DifferentiableAt ℂ (fun w => ψ p ((ψ p').symm w)) w)
    (Q : Y → ℂ → ℂ) (hQ0 : ∀ p z, z ∉ (ψ p).target → Q p z = 0)
    (hQd : ∀ p, DifferentiableOn ℂ (Q p) (ψ p).target)
    (hQlaw : ∀ p p', ∀ w ∈ (ψ p').target, (ψ p').symm w ∈ (ψ p).source →
      Q p' w = Q p (ψ p ((ψ p').symm w)) * deriv (fun w => ψ p ((ψ p').symm w)) w ^ 2) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ChartedSpace ℂ X), T2Space X ∧ ConnectedSpace X ∧
      CompactSpace X ∧ IsManifold 𝓘(ℂ) ω X ∧ ∃ (e : Y ≃ₜ X) (q' : X → ℂ → ℂ), IsHolQuadDiff q' ∧
        ∀ p, (∀ x, chartAt ℂ (e p) (e x) = ψ p x) ∧ q' (e p) = Q p := by
  let τ : TopologicalSpace (s26d_a_X Y) := ‹TopologicalSpace Y›
  let cs : ChartedSpace ℂ (s26d_a_X Y) := ChartedSpace.mk (Set.range ψ) ψ hmem (fun p => ⟨p, rfl⟩)
  have hman : IsManifold 𝓘(ℂ) ω (s26d_a_X Y) := by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨p', rfl⟩ ⟨p, rfl⟩
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
    have hopen : IsOpen ((ψ p').symm.trans (ψ p)).source := ((ψ p').symm.trans (ψ p)).open_source
    refine (DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen).contDiffOn_of_completeSpace
    rw [OpenPartialHomeomorph.trans_source] at hw
    exact (hcompat p p' w hw.1 hw.2).differentiableWithinAt
  refine ⟨s26d_a_X Y, τ, cs, ‹T2Space Y›, ‹ConnectedSpace Y›, ‹CompactSpace Y›, hman,
    ⟨Equiv.refl _, continuous_id, continuous_id⟩, Q, ?_, fun p => ⟨fun x => rfl, rfl⟩⟩
  refine ⟨⟨fun x z hz => hQ0 x z hz, fun x y z hz hzx => ?_⟩, fun x => hQd x⟩
  rw [zpow_zero, mul_one, zpow_two, ← pow_two]
  exact hQlaw x y z hz hzx


/-- **Existence of the Teichmüller deformation** (the content of `exists_teichDeformation`): the new charts
`ψ_p = T_{k,m_p} ∘ ζ_p ∘ φ_p` (`s26d_a_psi`) form a holomorphic atlas (`s26d_a_transition`) on the point set of `S₀`;
`q'` is `((m_p+2)/2)² w^{m_p}` on the target of `ψ_p`, and in the fields of `IsTeichDeformation` one takes
`ζ = ζ_p` and `ζ' = id`. -/
theorem s26d_a_exists [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ChartedSpace ℂ X), T2Space X ∧ ConnectedSpace X ∧
      CompactSpace X ∧ IsManifold 𝓘(ℂ) ω X ∧ ∃ (e : S₀ ≃ₜ X) (q' : X → ℂ → ℂ), IsHolQuadDiff q' ∧
        (∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
          ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
            ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ z)) ∧
        ∀ (p : S₀) (m : ℕ), IsZeroOfOrder q p m → IsZeroOfOrder q' (e p) m ∧
          ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAtZero q p m ζ ∧ IsNaturalParameterAtZero q' (e p) m ζ' ∧
            ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretchZero k m (ζ z) := by
  choose m ζ Z hD using s26d_a_data_exists hq hne
  set ψ := s26d_a_psi hk₀ hk m Z with hψ
  set Q : S₀ → ℂ → ℂ := fun p => (ψ p).target.indicator (fun w => ((m p + 2 : ℂ) / 2) ^ 2 * w ^ m p)
    with hQ
  have hQt : ∀ p, ∀ w ∈ (ψ p).target, Q p w = ((m p + 2 : ℂ) / 2) ^ 2 * w ^ m p := fun p w hw =>
    Set.indicator_of_mem hw _
  obtain ⟨X, τ, cs, h2, hc2, hc3, hman, e, q', hq', hX⟩ :=
    s26d_a_package ψ (fun p => (s26d_a_psi_center hk₀ hk hD p).1)
    (fun p p' w hw hwp => (s26d_a_transition hq hk₀ hk hD p p' hw hwp).1) Q
    (fun p z hz => Set.indicator_of_notMem hz _)
    (fun p => ((differentiable_const _).mul (differentiable_pow _)).differentiableOn.congr
      fun w hw => hQt p w hw)
    (fun p p' w hw hwp => by
      rw [hQt p' w hw, hQt p _ ((ψ p).map_source hwp)]
      exact (s26d_a_transition hq hk₀ hk hD p p' hw hwp).2)
  -- common facts
  have hc : ∀ p, chartAt ℂ (e p) (e p) = 0 := fun p => by
    rw [(hX p).1 p]
    exact (s26d_a_psi_center hk₀ hk hD p).2
  have hq'Q : ∀ p, q' (e p) = Q p := fun p => (hX p).2
  have htarget : ∀ p, (ψ p).target ∈ 𝓝 (0 : ℂ) := fun p => by
    have h1 := (ψ p).map_source (s26d_a_psi_center hk₀ hk hD p).1
    rw [(s26d_a_psi_center hk₀ hk hD p).2] at h1
    exact (ψ p).open_target.mem_nhds h1
  have hloc : ∀ p, ∀ᶠ z in 𝓝 (chartAt ℂ p p), localMapExpr e p z = teichStretchZero k (m p) (ζ p z) :=
    fun p => by
      filter_upwards [(chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))]
        with z hz
      show chartAt ℂ (e p) (e ((chartAt ℂ p).symm z)) = _
      rw [(hX p).1, s26d_a_psi_chart hk₀ hk hD p hz]
  have hnat : ∀ p, IsNaturalParameterAtZero q' (e p) (m p) id := fun p => by
    refine ⟨analyticAt_id, by rw [hc p]; rfl, by rw [deriv_id]; exact one_ne_zero, ?_⟩
    rw [hc p, hq'Q p]
    filter_upwards [htarget p] with z hz
    rw [hQt p z hz, deriv_id, id_eq, one_pow, mul_one]
  refine ⟨X, τ, cs, h2, hc2, hc3, hman, e, q', hq', fun p hp => ?_, fun p n hn => ?_⟩
  · -- regular points: `m p = 0`
    have hm : m p = 0 := (hD p).regular_iff.1 hp
    have hnp := hnat p
    have hnq := (hD p).natural
    rw [hm] at hnp hnq
    refine ⟨?_, ζ p, id, ⟨hnq.1, hnq.2.1, hnq.2.2.1, hnq.2.2.2.mono fun z hz => ?_⟩,
      ⟨hnp.1, hnp.2.1, hnp.2.2.1, hnp.2.2.2.mono fun z hz => ?_⟩, (hloc p).mono fun z hz => ?_⟩
    · show q' (e p) (chartAt ℂ (e p) (e p)) ≠ 0
      rw [hc p, hq'Q p, hQt p 0 (mem_of_mem_nhds (htarget p)), hm]
      norm_num
    · rw [hz]
      norm_num
    · rw [hz]
      norm_num
    · rw [id_eq, hz, hm, s26d_a_teichStretchZero_zero]
  · -- zeros of order `n`: `n = m p`
    have hnm : n = m p := by
      have h1 := hn.symm.trans (hD p).order
      exact_mod_cast h1
    subst hnm
    refine ⟨?_, ζ p, id, (hD p).natural, hnat p, (hloc p).mono fun z hz => by rw [id_eq, hz]⟩
    show meromorphicOrderAt (q' (e p)) (chartAt ℂ (e p) (e p)) = ((m p : ℕ) : ℤ)
    have hev : Q p =ᶠ[𝓝 0] fun z => ((m p + 2 : ℂ) / 2) ^ 2 * z ^ m p := by
      filter_upwards [htarget p] with z hz
      exact hQt p z hz
    have han : AnalyticAt ℂ (Q p) 0 :=
      (analyticAt_const.mul (analyticAt_id.pow _)).congr hev.symm
    rw [hc p, hq'Q p, meromorphicOrderAt_eq_int_iff han.meromorphicAt]
    refine ⟨fun _ => ((m p + 2 : ℂ) / 2) ^ 2, analyticAt_const, ?_,
      (hev.filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_⟩
    · refine pow_ne_zero _ (div_ne_zero ?_ two_ne_zero)
      exact_mod_cast (by omega : (m p + 2 : ℕ) ≠ 0)
    · rw [hz, sub_zero, zpow_natCast, smul_eq_mul, mul_comm]

/-- A closed Riemann surface, bundled with its analytic structure. -/
structure ClosedRS : Type (u + 1) where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [connectedSpace : ConnectedSpace carrier]
  [compactSpace : CompactSpace carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) ω carrier]

attribute [instance] ClosedRS.topologicalSpace ClosedRS.t2Space ClosedRS.connectedSpace
  ClosedRS.compactSpace ClosedRS.chartedSpace ClosedRS.isManifold

/-- **§26.2 (Teichmüller 形变).**  `(X, e, q')` is a Teichmüller deformation `S_{q,k}` of `S₀` with
respect to `q ∈ Q(S₀) ∖ {0}` and `k ∈ [0, 1)`: `X` is a Riemann surface with the same underlying
topological space (`e : S₀ ≃ₜ X` is the identity of the point set, the deformation map `f₀`),
`q' ∈ Q(X)` is the terminal differential, and in the natural parameters `ζ` of `q` and `ζ'` of
`q'` the map `f₀` is `ζ ↦ (ζ + kζ̄)/(1-k)` at regular points and `ζ ↦ ζ'` of `teichStretchZero`
at a zero of order `m`; regular points and zeros of order `m` of `q` correspond to those of
`q'`. -/
structure IsTeichDeformation (q : S₀ → ℂ → ℂ) (k : ℝ) (X : ClosedRS.{u}) (e : S₀ ≃ₜ X.carrier)
    (q' : X.carrier → ℂ → ℂ) : Prop where
  initial : IsHolQuadDiff q
  initial_ne : q ≠ 0
  k_nonneg : 0 ≤ k
  k_lt_one : k < 1
  terminal : IsHolQuadDiff q'
  regular : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (e p) ∧
    ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (e p) ζ' ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretch k (ζ z)
  zero : ∀ (p : S₀) (m : ℕ), IsZeroOfOrder q p m → IsZeroOfOrder q' (e p) m ∧
    ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAtZero q p m ζ ∧ IsNaturalParameterAtZero q' (e p) m ζ' ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr e p z) = teichStretchZero k m (ζ z)

/-- §26.2: the new parameters `{(U_p, ζ'(p))}` define a new complex structure on the topological
surface underlying `S₀`, and `q'` (`= dζ'²` at regular points, `((m+2)/2)² ζ'^m dζ'²` at zeros)
is a holomorphic quadratic differential on it: Teichmüller deformations `S_{q,k}` exist. -/
theorem exists_teichDeformation [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {k : ℝ} (hk₀ : 0 ≤ k)
    (hk : k < 1) :
    ∃ (X : ClosedRS.{u}) (e : S₀ ≃ₜ X.carrier) (q' : X.carrier → ℂ → ℂ), IsTeichDeformation q k X e q' := by
  obtain ⟨X, τ, cs, h2, hc, hcp, hman, e, q', hq', hreg, hzero⟩ := s26d_a_exists hq hne hk₀ hk
  exact ⟨⟨X⟩, e, q', hq, hne, hk₀, hk, hq', hreg, hzero⟩

/-! ### Helpers for `teichDeformation_real_form` (`s26u_`): the deformation map is `K`-quasiconformal -/

/-- The real form of `teichStretch` (the second conjunct of `teichDeformation_real_form`):
`ξ' = ((1+k)/(1-k)) ξ`, `η' = η`, for `k < 1`. -/
theorem s26u_teichStretch_real_form {k : ℝ} (hk : k < 1) (ζ : ℂ) :
    (teichStretch k ζ).re = (1 + k) / (1 - k) * ζ.re ∧ (teichStretch k ζ).im = ζ.im := by
  have h1k : (1 - k) ≠ 0 := by linarith
  have h1k' : (1 - (k : ℂ)) ≠ 0 := by exact_mod_cast h1k
  have hmul : ((1 - k : ℝ) : ℂ) * teichStretch k ζ = ζ + (k : ℂ) * conj ζ := by
    unfold teichStretch
    push_cast
    field_simp
  have hre := congrArg Complex.re hmul
  have him := congrArg Complex.im hmul
  simp only [re_ofReal_mul, im_ofReal_mul, add_re, add_im, conj_re, conj_im, mul_neg] at hre him
  constructor
  · rw [div_mul_eq_mul_div, eq_div_iff h1k]
    linarith
  · have h2 : (1 - k) * (teichStretch k ζ).im = (1 - k) * ζ.im := by linarith
    exact mul_left_cancel₀ h1k h2

/-- `K = (1+k)/(1-k) ≥ 1` for `0 ≤ k < 1`. -/
theorem s26u_one_le_K {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) : 1 ≤ (1 + k) / (1 - k) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The new parameter `teichStretch k` at a regular point is the real stretch `x + iy ↦ Kx + iy`,
`K = (1+k)/(1-k)`, hence `K`-quasiconformal on the plane (`td_Stretch_isKQC`). -/
theorem s26u_teichStretch_isKQC {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    IsKQC (teichStretch k) univ ((1 + k) / (1 - k)) := by
  have h1k : 0 < 1 - k := by linarith
  have hα : (1 + k) / (1 - k) ≠ 0 := (div_pos (by linarith) h1k).ne'
  have h := td_Stretch_isKQC hα one_ne_zero one_pos (s26u_one_le_K hk₀ hk)
  rw [div_one] at h
  refine ad_isKQC_congr h fun z _ => ?_
  obtain ⟨hre, him⟩ := s26u_teichStretch_real_form hk z
  rw [td_Stretch_apply]
  apply Complex.ext
  · rw [hre, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
  · rw [him, add_im, ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add, one_mul]

/-- A holomorphic map with nonzero derivative at `z₀` is holomorphic and injective on an open
neighbourhood of `z₀` (inverse function theorem). -/
theorem s26u_exists_open_injOn {A : ℂ → ℂ} {z₀ : ℂ} (hA : AnalyticAt ℂ A z₀) (hA' : deriv A z₀ ≠ 0) :
    ∃ W : Set ℂ, IsOpen W ∧ z₀ ∈ W ∧ DifferentiableOn ℂ A W ∧ InjOn A W := by
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ hA')
  have hfd : HasStrictFDerivAt A i.toContinuousLinearMap z₀ := hA.hasStrictDerivAt
  have hx : z₀ ∈ (hfd.toOpenPartialHomeomorph A).source := hfd.mem_toOpenPartialHomeomorph_source
  have hinj : InjOn A (hfd.toOpenPartialHomeomorph A).source := by
    have h := (hfd.toOpenPartialHomeomorph A).injOn
    rwa [hfd.toOpenPartialHomeomorph_coe] at h
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.1 hA.eventually_analyticAt
  exact ⟨(hfd.toOpenPartialHomeomorph A).source ∩ V,
    (hfd.toOpenPartialHomeomorph A).open_source.inter hVo, ⟨hx, hzV⟩,
    fun w hw => (hVsub hw.2).differentiableAt.differentiableWithinAt, hinj.mono inter_subset_left⟩

/-- **Local conjugation lemma**: if near `z₀` one has `B ∘ g = F ∘ A` with `A`, `B` holomorphic with
nonzero derivative (at `z₀`, resp. `g z₀`), `g` continuous at `z₀` and `F` `K`-q.c. on the plane,
then `g` is `K`-q.c. on an open neighbourhood of `z₀` inside any given neighbourhood `V`: there
`g = B⁻¹ ∘ F ∘ A` (`thm7_1_comp` with the conformal maps `A` and `B⁻¹`). -/
theorem s26u_isKQC_local_of_conj {g A B F : ℂ → ℂ} {z₀ : ℂ} {K : ℝ} (hF : IsKQC F univ K)
    (hA : AnalyticAt ℂ A z₀) (hA' : deriv A z₀ ≠ 0) (hB : AnalyticAt ℂ B (g z₀))
    (hB' : deriv B (g z₀) ≠ 0) (hg : ContinuousAt g z₀) (hBg : ∀ᶠ w in 𝓝 z₀, B (g w) = F (A w))
    {V : Set ℂ} (hV : V ∈ 𝓝 z₀) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ V ∧ IsKQC g U K := by
  obtain ⟨WA, hWAo, hzA, hAd, hAi⟩ := s26u_exists_open_injOn hA hA'
  obtain ⟨WB, hWBo, hzB, hBd, hBi⟩ := s26u_exists_open_injOn hB hB'
  set S : Set ℂ := {w | w ∈ V ∧ w ∈ WA ∧ g w ∈ WB ∧ B (g w) = F (A w)} with hSdef
  have hS : S ∈ 𝓝 z₀ := by
    filter_upwards [hV, hWAo.mem_nhds hzA, hg.preimage_mem_nhds (hWBo.mem_nhds hzB), hBg]
      with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hUo : IsOpen (interior S) := isOpen_interior
  have hzU : z₀ ∈ interior S := mem_interior_iff_mem_nhds.2 hS
  have hUS : interior S ⊆ S := interior_subset
  have hA1 : IsKQC A (interior S) 1 := isKQC_one_of_conformal hUo
    ⟨hAd.mono fun w hw => (hUS hw).2.1, hAi.mono fun w hw => (hUS hw).2.1, rfl⟩
  have hFA := thm7_1_comp hA1 hF (subset_univ _)
  have hBc : IsConformalOnto B WB (B '' WB) := ⟨hBd, hBi, rfl⟩
  have hBinv : IsKQC (Function.invFunOn B WB) (B '' WB) 1 :=
    isKQC_one_of_conformal (hBc.isOpen hWBo) (hBc.symm hWBo)
  have hsub : (F ∘ A) '' interior S ⊆ B '' WB := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨g w, (hUS hw).2.2.1, (hUS hw).2.2.2⟩
  have hall := thm7_1_comp hFA hBinv hsub
  rw [one_mul, mul_one] at hall
  refine ⟨interior S, hUo, hzU, fun w hw => (hUS hw).1, ad_isKQC_congr hall fun w hw => ?_⟩
  show g w = Function.invFunOn B WB (F (A w))
  rw [← (hUS hw).2.2.2]
  exact (hBi.leftInvOn_invFunOn (hUS hw).2.2.1).symm

/-- The transformation law of a holomorphic quadratic differential `q`, specialised: for `z` in the
chart target at `x` with `p = φ_x⁻¹ z` in the chart source at `y`, `q_x(z) = q_y(τ z) τ'(z)²`,
`τ = φ_y ∘ φ_x⁻¹`. -/
theorem s26u_law {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source) :
    q x z = q y (chartTransition y x z) * deriv (chartTransition y x) z ^ 2 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  rw [hq'.1.2 y x z hz hzy]
  norm_num

/-- Regularity in an arbitrary chart: for `z` in the chart target at `x`, the point `φ_x⁻¹ z` is a
regular point of `q` (a condition in the preferred chart at that point) iff `q_x(z) ≠ 0` (the
transformation law in both directions). -/
theorem s26u_isRegularPoint_iff {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    IsRegularPoint q ((chartAt ℂ x).symm z) ↔ q x z ≠ 0 := by
  set p := (chartAt ℂ x).symm z with hp
  have hpx : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  constructor
  · intro hr h0
    have hw : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hwp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hlaw := s26u_law hq p x hw (by rw [hwp]; exact hpx)
    have hT : chartTransition x p (chartAt ℂ p p) = z := by
      show chartAt ℂ x ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [hwp]
      exact (chartAt ℂ x).right_inv hz
    rw [hT, h0, zero_mul] at hlaw
    exact hr hlaw
  · intro hne h0
    apply hne
    have hlaw := s26u_law hq x p hz (mem_chart_source ℂ p)
    have hT : chartTransition p x z = chartAt ℂ p p := rfl
    rw [hlaw, hT, h0, zero_mul]

/-- Where `q_x ≠ 0`, the chart transition `τ = φ_y ∘ φ_x⁻¹` is holomorphic with `τ' ≠ 0`: the
transformation law `q_x = q_y(τ) τ'²` forces `τ' ≠ 0` (hence complex differentiability) at every
point of a neighbourhood.  No holomorphic atlas on the surface is assumed. -/
theorem s26u_transition_analyticAt {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source)
    (hq0 : q x z ≠ 0) : AnalyticAt ℂ (chartTransition y x) z ∧ deriv (chartTransition y x) z ≠ 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hd : ∀ w, w ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source →
      q x w ≠ 0 → deriv (chartTransition y x) w ≠ 0 := by
    intro w hw hwy hw0 h0
    have hlaw := s26u_law hq x y hw hwy
    rw [h0, zero_pow two_ne_zero, mul_zero] at hlaw
    exact hw0 hlaw
  have hc : ContinuousAt (q x) z :=
    ((hq'.2 x).differentiableAt ((chartAt ℂ x).open_target.mem_nhds hz)).continuousAt
  have hN : {w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source ∧
      q x w ≠ 0} ∈ 𝓝 z := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds
      ⟨hz, hzy⟩, hc.eventually_ne hq0] with w hw hw'
    exact ⟨hw.1, hw.2, hw'⟩
  refine ⟨DifferentiableOn.analyticAt (fun w hw =>
    (differentiableAt_of_deriv_ne_zero (hd w hw.1 hw.2.1 hw.2.2)).differentiableWithinAt) hN,
    hd z hz hzy hq0⟩

/-- If regular points of `q` accumulate at `φ_x⁻¹ z`, then `q_x` has no zeros in a punctured
neighbourhood of `z` (isolated zeros of the holomorphic `q_x`). -/
theorem s26u_eventually_ne_zero {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (x : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hfr : ∃ᶠ p in 𝓝 ((chartAt ℂ x).symm z), IsRegularPoint q p) :
    ∀ᶠ w in 𝓝[≠] z, q x w ≠ 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have han : AnalyticAt ℂ (q x) z := (hq'.2 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds hz)
  refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
  have hpx : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcont : Tendsto (chartAt ℂ x) (𝓝 ((chartAt ℂ x).symm z)) (𝓝 z) := by
    have h := ((chartAt ℂ x).continuousAt hpx).tendsto
    rwa [(chartAt ℂ x).right_inv hz] at h
  refine hfr ?_
  filter_upwards [hcont.eventually h0, (chartAt ℂ x).open_source.mem_nhds hpx] with p' hp' hsrc hreg
  have h1 := (s26u_isRegularPoint_iff hq x ((chartAt ℂ x).map_source hsrc)).1
    (by rw [(chartAt ℂ x).left_inv hsrc]; exact hreg)
  exact h1 hp'

/-- On a connected (T1) surface, regular points of a holomorphic quadratic differential `q ≠ 0`
accumulate at every point: the set of points near which no point is regular is clopen
(`s26u_eventually_ne_zero`), and if it were everything then `q = 0` (`s26u_isRegularPoint_iff`). -/
theorem s26u_frequently_regular [ConnectedSpace S₀] [T1Space S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S₀) : ∃ᶠ p' in 𝓝 p, IsRegularPoint q p' := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set B : Set S₀ := {p | ∀ᶠ p' in 𝓝 p, ¬ IsRegularPoint q p'} with hBdef
  have hBo : IsOpen B := isOpen_setOfPred_eventually_nhds
  have hBc : IsClosed B := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p₀ hp₀
    have hfr : ∃ᶠ p' in 𝓝 p₀, IsRegularPoint q p' := hp₀
    have hsrc : (chartAt ℂ p₀).source ∈ 𝓝 p₀ :=
      (chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀)
    have hl : (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀) = p₀ :=
      (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)
    have hw := s26u_eventually_ne_zero hq p₀ ((chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀))
      (by rw [hl]; exact hfr)
    have ht : Tendsto (chartAt ℂ p₀) (𝓝[≠] p₀) (𝓝[≠] (chartAt ℂ p₀ p₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hsrc] with p' hp' hne'
      exact fun heq => hne' ((chartAt ℂ p₀).injOn hp' (mem_chart_source ℂ p₀) heq)
    have hpunct : ∀ᶠ p' in 𝓝 p₀, p' ≠ p₀ → IsRegularPoint q p' := by
      have h2 := ht.eventually hw
      rw [eventually_nhdsWithin_iff] at h2
      filter_upwards [h2, hsrc] with p' h1 h3 hne'
      have h4 := (s26u_isRegularPoint_iff hq p₀ ((chartAt ℂ p₀).map_source h3)).2 (h1 hne')
      rwa [(chartAt ℂ p₀).left_inv h3] at h4
    filter_upwards [eventually_eventually_nhds.2 hpunct] with p₁ hp₁
    by_cases hp₁₀ : p₁ = p₀
    · rw [hp₁₀]
      exact hp₀
    · show ∃ᶠ p' in 𝓝 p₁, IsRegularPoint q p'
      refine Eventually.frequently ?_
      filter_upwards [hp₁, eventually_ne_nhds hp₁₀] with p'' h1 h2 using h1 h2
  rcases isClopen_iff.1 ⟨hBc, hBo⟩ with hB | hB
  · intro hp
    have hpB : p ∈ B := hp
    rw [hB] at hpB
    exact hpB
  · exfalso
    apply hne
    funext x z
    show q x z = 0
    by_cases hz : z ∈ (chartAt ℂ x).target
    · have hB' : (chartAt ℂ x).symm z ∈ B := by
        rw [hB]
        exact mem_univ _
      by_contra h0
      exact hB'.self_of_nhds ((s26u_isRegularPoint_iff hq x hz).2 h0)
    · exact hq'.1.1 x z hz

/-- On a connected (T1) surface the zeros of a holomorphic quadratic differential `q ≠ 0` in any
chart target form a countable set (they are isolated, `s26u_frequently_regular`). -/
theorem s26u_zeros_countable [ConnectedSpace S₀] [T1Space S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (x : S₀) :
    {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0}.Countable := by
  have hdisc : DiscreteTopology {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0} := by
    refine discreteTopology_subtype_iff.2 fun z hz => ?_
    have hw := s26u_eventually_ne_zero hq x hz.1 (s26u_frequently_regular hq hne _)
    rw [inf_principal_eq_bot]
    filter_upwards [hw] with w hw hwZ
    exact hw hwZ.2
  exact Set.countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)

/-- **The local form at a point where `q_x ≠ 0`.**  With `p = φ_x⁻¹ z₀` (a regular point), natural
parameters `ζ` at `p` and `ζ'` at `e p`, `τ = φ_p ∘ φ_x⁻¹` (holomorphic by
`s26u_transition_analyticAt`) and `σ = φ_{e p} ∘ φ_{e x}⁻¹` (holomorphic: `X` is a Riemann
surface), the local expression `g` of `e` at `x` satisfies `(ζ' ∘ σ) ∘ g = S_k ∘ (ζ ∘ τ)` near
`z₀`; so `g` is `K`-q.c. near `z₀` (`s26u_isKQC_local_of_conj`). -/
theorem s26u_local {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier}
    {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') (x : S₀) {z₀ : ℂ}
    (hz₀ : z₀ ∈ localMapDomain e x) (hq0 : q x z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ localMapDomain e x ∧
      IsKQC (localMapExpr e x) U ((1 + k) / (1 - k)) := by
  have hz₀t : z₀ ∈ (chartAt ℂ x).target := hz₀.1
  set p := (chartAt ℂ x).symm z₀ with hp
  have hep : e p ∈ (chartAt ℂ (e x)).source := hz₀.2
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff h.initial x hz₀t).2 hq0
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := h.regular p hreg
  obtain ⟨hτan, hτd⟩ := s26u_transition_analyticAt h.initial x p hz₀t (mem_chart_source ℂ p) hq0
  have hτz : chartTransition p x z₀ = chartAt ℂ p p := rfl
  have hζan : AnalyticAt ℂ ζ (chartTransition p x z₀) := by
    rw [hτz]
    exact hζ.1
  have hAan : AnalyticAt ℂ (ζ ∘ chartTransition p x) z₀ := hζan.comp hτan
  have hAd : deriv (ζ ∘ chartTransition p x) z₀ ≠ 0 := by
    rw [deriv_comp z₀ hζan.differentiableAt hτan.differentiableAt, hτz]
    exact mul_ne_zero hζ.2.2.1 hτd
  have hgt : localMapExpr e x z₀ ∈ (chartAt ℂ (e x)).target := (chartAt ℂ (e x)).map_source hep
  have hgs : (chartAt ℂ (e x)).symm (localMapExpr e x z₀) = e p := (chartAt ℂ (e x)).left_inv hep
  have hgs' : (chartAt ℂ (e x)).symm (localMapExpr e x z₀) ∈ (chartAt ℂ (e p)).source := by
    rw [hgs]
    exact mem_chart_source ℂ (e p)
  have hσan : AnalyticAt ℂ (chartTransition (e p) (e x)) (localMapExpr e x z₀) :=
    DifferentiableOn.analyticAt (fun w hw => (s23_transition (e p) (e x) hw.1 hw.2).1.differentiableWithinAt)
      (((chartAt ℂ (e x)).isOpen_inter_preimage_symm (chartAt ℂ (e p)).open_source).mem_nhds ⟨hgt, hgs'⟩)
  have hσd : deriv (chartTransition (e p) (e x)) (localMapExpr e x z₀) ≠ 0 :=
    (s23_transition (e p) (e x) hgt hgs').2
  have hσz : chartTransition (e p) (e x) (localMapExpr e x z₀) = chartAt ℂ (e p) (e p) := by
    simp only [chartTransition, hgs]
  have hζ'an : AnalyticAt ℂ ζ' (chartTransition (e p) (e x) (localMapExpr e x z₀)) := by
    rw [hσz]
    exact hζ'.1
  have hBan : AnalyticAt ℂ (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x z₀) := hζ'an.comp hσan
  have hBd : deriv (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x z₀) ≠ 0 := by
    rw [deriv_comp _ hζ'an.differentiableAt hσan.differentiableAt, hσz]
    exact mul_ne_zero hζ'.2.2.1 hσd
  have hgc : ContinuousAt (localMapExpr e x) z₀ := by
    have h1 : ContinuousAt (fun z => e ((chartAt ℂ x).symm z)) z₀ :=
      e.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz₀t)
    exact ContinuousAt.comp (g := chartAt ℂ (e x)) (f := fun z => e ((chartAt ℂ x).symm z))
      ((chartAt ℂ (e x)).continuousAt hep) h1
  have hΩ : localMapDomain e x ∈ 𝓝 z₀ := (s23_localMapDomain_isOpen e.continuous x).mem_nhds hz₀
  have hτc : Tendsto (chartTransition p x) (𝓝 z₀) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]
    exact hτan.continuousAt.tendsto
  have hBg : ∀ᶠ w in 𝓝 z₀, (ζ' ∘ chartTransition (e p) (e x)) (localMapExpr e x w) =
      teichStretch k ((ζ ∘ chartTransition p x) w) := by
    filter_upwards [hτc.eventually hrel, hΩ, ((chartAt ℂ x).isOpen_inter_preimage_symm
      (chartAt ℂ p).open_source).mem_nhds ⟨hz₀t, mem_chart_source ℂ p⟩] with w hw1 hw2 hw3
    simp only [Function.comp_apply]
    rw [← hw1]
    congr 1
    simp only [chartTransition, localMapExpr]
    rw [(chartAt ℂ (e x)).left_inv hw2.2, (chartAt ℂ p).left_inv hw3.2]
  exact s26u_isKQC_local_of_conj (s26u_teichStretch_isKQC h.k_nonneg h.k_lt_one) hAan hAd hBan hBd hgc
    hBg hΩ

/-- **Each local expression of the deformation map is `K`-q.c.**  `S₀` is connected and T2 (it is
homeomorphic to `X` via `e`), so the zeros of `q_x` in the chart target are countable
(`s26u_zeros_countable`); away from them `e` is locally `K`-q.c. (`s26u_local`), and the countable
set is removable (`s13x_removable`). -/
theorem s26u_isKQC_chart {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier}
    {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') (x : S₀) :
    IsKQC (localMapExpr e x) (localMapDomain e x) ((1 + k) / (1 - k)) := by
  have hconn : ConnectedSpace S₀ := e.symm.surjective.connectedSpace e.symm.continuous
  have hT2 : T2Space S₀ := e.isEmbedding.t2Space
  have hΩ := s23_localMapDomain_isOpen e.continuous x
  have hcont : ContinuousOn (localMapExpr e x) (localMapDomain e x) := fun z hz => by
    have h1 : ContinuousAt (fun z => e ((chartAt ℂ x).symm z)) z :=
      e.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
    have h2 : e ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (e x)).source := hz.2
    exact (ContinuousAt.comp (g := chartAt ℂ (e x)) (f := fun z => e ((chartAt ℂ x).symm z))
      ((chartAt ℂ (e x)).continuousAt h2) h1).continuousWithinAt
  have hinj : InjOn (localMapExpr e x) (localMapDomain e x) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 : e ((chartAt ℂ x).symm w₁) = e ((chartAt ℂ x).symm w₂) :=
      (chartAt ℂ (e x)).injOn hw₁.2 hw₂.2 heq
    exact (chartAt ℂ x).symm.injOn hw₁.1 hw₂.1 (e.injective h1)
  have hLc : (localMapDomain e x ∩ {z | q x z = 0}).Countable := by
    refine Set.Countable.mono ?_ (s26u_zeros_countable h.initial h.initial_ne x)
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  refine s13x_removable (L := localMapDomain e x ∩ {z | q x z = 0}) hΩ
    (s26u_one_le_K h.k_nonneg h.k_lt_one) (qcl_f_isHomeomorphOnto_of_injOn hΩ hcont hinj)
    (hLc.measure_zero _) (Eventually.of_forall fun a => ?_) (Eventually.of_forall fun b => ?_)
    fun z hz => s26u_local h x hz.1 fun h0 => hz.2 ⟨hz.1, h0⟩
  · refine hLc.preimage (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I) fun y₁ y₂ hy => ?_
    have := congrArg Complex.im hy
    simpa using this
  · refine hLc.preimage (f := fun x : ℝ => (x : ℂ) + (b : ℂ) * I) fun x₁ x₂ hx => ?_
    have := congrArg Complex.re hx
    simpa using this

/-- The deformation map is `K`-quasiconformal, `K = (1+k)/(1-k)`. -/
theorem s26u_isKQCRS {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier}
    {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') :
    IsKQCRS e ((1 + k) / (1 - k)) :=
  ⟨s26u_one_le_K h.k_nonneg h.k_lt_one, fun x => s26u_isKQC_chart h x⟩

/-- §26.2: the deformation map `f₀ : S₀ → S_{q,k}` is `K`-quasiconformal with `K = (1+k)/(1-k)`; in
the natural parameters `ζ = ξ + iη`, `ζ' = ξ' + iη'` it has the real form `ξ' = Kξ`, `η' = η`:
horizontal (vertical) trajectories of `q` go to horizontal (vertical) trajectories of `q'`, with a
stretching by the factor `K` along the horizontal trajectories. -/
theorem teichDeformation_real_form {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier}
    {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') :
    IsKQCRS e ((1 + k) / (1 - k)) ∧
      ∀ ζ : ℂ, (teichStretch k ζ).re = (1 + k) / (1 - k) * ζ.re ∧ (teichStretch k ζ).im = ζ.im := by
  exact ⟨s26u_isKQCRS h, fun ζ => s26u_teichStretch_real_form h.k_lt_one ζ⟩

/-- A countable measurable partition of a Riemann surface subordinate to charts: `P i` lies in the
chart at `x i`, the `P i` are pairwise disjoint with measurable chart images and cover `S`. -/
def IsChartPartition (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (x : ℕ → S)
    (P : ℕ → Set S) : Prop :=
  (∀ i, P i ⊆ (chartAt ℂ (x i)).source ∧ MeasurableSet (chartAt ℂ (x i) '' P i)) ∧
    Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = univ

/-- The integral `∬_S u dA_q` of a function `u` (given by its local expressions `u x z` in the
chart at `x`) with respect to the area element `|φ| dx dy` of `q = φ dz²`, computed on a chart
partition (all partitions give the same value for a chart-invariant integrand). -/
def surfaceIntegral {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ)
    (u : S → ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (x : ℕ → S) (P : ℕ → Set S) (_ : IsChartPartition S x P),
    ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖

/-- §26.2: the norm `‖q‖ = ∬_S |φ| dx dy` of a quadratic differential `q = φ dz²`. -/
def quadDiffNorm {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) : ℝ≥0∞ :=
  surfaceIntegral q fun _ _ => 1

/-! ### Helpers for `quadDiffNorm_finite` (`s26_`): chart partitions exist on a compact surface; the
surface integral is finite, homogeneous, and positive for `q ≠ 0` (change of variables through the
holomorphic chart transitions) -/

/-- The chart image of `W ∩ ⋂_{j<i} Wⱼᶜ` (all `W`'s open, `W ⊆` the chart source) is measurable. -/
theorem s26_measurableSet_chart_image {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (x : S)
    (W : ℕ → Set S) (hW : ∀ j, IsOpen (W j)) (i : ℕ) (hs : W i ⊆ (chartAt ℂ x).source) :
    MeasurableSet (chartAt ℂ x '' (W i ∩ ⋂ j < i, (W j)ᶜ)) := by
  set e := chartAt ℂ x
  have hsub : W i ∩ ⋂ j < i, (W j)ᶜ ⊆ e.source := inter_subset_left.trans hs
  have h1 : e '' (W i ∩ ⋂ j < i, (W j)ᶜ) =
      (e.target ∩ e.symm ⁻¹' W i) ∩ ⋂ j < i, (e.target ∩ e.symm ⁻¹' W j)ᶜ := by
    rw [← inter_eq_right.2 hsub, e.image_source_inter_eq']
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_iInter, mem_compl_iff]
    constructor
    · rintro ⟨hz, hWi, hj⟩
      exact ⟨⟨hz, hWi⟩, fun j hj' h => hj j hj' h.2⟩
    · rintro ⟨⟨hz, hWi⟩, hj⟩
      exact ⟨hz, hWi, fun j hj' h => hj j hj' ⟨hz, h⟩⟩
  rw [h1]
  exact (e.isOpen_inter_preimage_symm (hW i)).measurableSet.inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (e.isOpen_inter_preimage_symm (hW j)).measurableSet.compl)

/-- On a compact nonempty charted space, for open `V p ∋ p` inside the chart source at `p`, there is a
chart partition with `P i ⊆ V (x i)` and `P i = ∅` for `i ≥ N`. -/
theorem s26_exists_chartPartition {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] (V : S → Set S) (hVo : ∀ p, IsOpen (V p)) (hVp : ∀ p, p ∈ V p)
    (hVs : ∀ p, V p ⊆ (chartAt ℂ p).source) :
    ∃ (x : ℕ → S) (P : ℕ → Set S) (N : ℕ), IsChartPartition S x P ∧ (∀ i, P i ⊆ V (x i)) ∧
      ∀ i, N ≤ i → P i = ∅ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hVp p⟩)
  let x : ℕ → S := fun i =>
    if h : i < t.card then ((t.equivFin.symm ⟨i, h⟩ : t) : S) else Classical.arbitrary S
  let W : ℕ → Set S := fun i => if i < t.card then V (x i) else ∅
  have hWo : ∀ i, IsOpen (W i) := fun i => by
    by_cases h : i < t.card
    · simp only [W, h, ↓reduceIte]; exact hVo _
    · simp only [W, h, ↓reduceIte]; exact isOpen_empty
  have hWV : ∀ i, W i ⊆ V (x i) := fun i => by
    by_cases h : i < t.card
    · simp only [W, h, ↓reduceIte]; exact subset_rfl
    · simp only [W, h, ↓reduceIte]; exact empty_subset _
  refine ⟨x, disjointed W, t.card, ⟨fun i => ⟨?_, ?_⟩, disjoint_disjointed W, ?_⟩, ?_, ?_⟩
  · exact (disjointed_subset W i).trans ((hWV i).trans (hVs _))
  · rw [disjointed_eq_inter_compl]
    exact s26_measurableSet_chart_image (x i) W hWo i ((hWV i).trans (hVs _))
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht (mem_univ p))
    refine mem_iUnion.2 ⟨(t.equivFin ⟨q, hq⟩ : ℕ), ?_⟩
    have hlt : ((t.equivFin ⟨q, hq⟩ : Fin t.card) : ℕ) < t.card := (t.equivFin ⟨q, hq⟩).isLt
    have hx : x (t.equivFin ⟨q, hq⟩ : ℕ) = q := by
      simp only [x, hlt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
    simp only [W, hlt, ↓reduceIte, hx]
    exact hpq
  · exact fun i => (disjointed_subset W i).trans (hWV i)
  · intro i hi
    refine subset_empty_iff.1 ((disjointed_subset W i).trans ?_)
    simp only [W, not_lt.2 hi, ↓reduceIte]
    exact subset_rfl

/-- On a compact nonempty charted space a chart partition exists. -/
theorem s26_exists_chartPartition' {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] : ∃ (x : ℕ → S) (P : ℕ → Set S), IsChartPartition S x P := by
  obtain ⟨x, P, -, hP, -, -⟩ := s26_exists_chartPartition (S := S) (fun p => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  exact ⟨x, P, hP⟩

/-- The surface integral of an integrand vanishing identically is `0` (a chart partition exists). -/
theorem s26_surfaceIntegral_eq_zero {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] (q : S → ℂ → ℂ) {u : S → ℂ → ℝ≥0∞}
    (hu : ∀ x z, u x z * ENNReal.ofReal ‖q x z‖ = 0) :
    surfaceIntegral q u = 0 := by
  obtain ⟨x, P, hP⟩ := s26_exists_chartPartition' (S := S)
  refine le_antisymm ?_ bot_le
  unfold surfaceIntegral
  refine iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP (le_of_eq ?_)))
  simp only [hu, lintegral_zero, tsum_zero]

/-- (i) `‖q‖ < ∞` on a compact surface: a partition subordinate to relatively compact chart balls. -/
theorem s26_quadDiffNorm_lt_top {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) : quadDiffNorm q < ⊤ := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hr : ∀ p : S, ∃ r > 0, closedBall (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target := by
    intro p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (chartAt ℂ p).open_target _ (mem_chart_target ℂ p)
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose r hr0 hrs using hr
  obtain ⟨x, P, N, hP, hPV, hPN⟩ := s26_exists_chartPartition
    (fun p => (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) (r p))
    (fun p => (chartAt ℂ p).isOpen_inter_preimage isOpen_ball)
    (fun p => ⟨mem_chart_source ℂ p, mem_ball_self (hr0 p)⟩) (fun _ => inter_subset_left)
  have hterm : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖ < ⊤ := by
    intro i
    set B := closedBall (chartAt ℂ (x i) (x i)) (r (x i))
    have hcont : ContinuousOn (q (x i)) B := (hq'.2 (x i)).continuousOn.mono (hrs (x i))
    obtain ⟨C, hC⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn hcont
    have hsub : chartAt ℂ (x i) '' P i ⊆ B := by
      rintro _ ⟨y, hy, rfl⟩
      exact ball_subset_closedBall (hPV i hy).2
    calc ∫⁻ z in chartAt ℂ (x i) '' P i, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖
        ≤ ∫⁻ z in B, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖ := lintegral_mono_set hsub
      _ ≤ ∫⁻ _ in B, ENNReal.ofReal C :=
          setLIntegral_mono' measurableSet_closedBall fun z hz => by
            rw [one_mul]
            exact ENNReal.ofReal_le_ofReal (hC z hz)
      _ = ENNReal.ofReal C * volume B := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have hzero : ∀ i ∉ Finset.range N,
      ∫⁻ z in chartAt ℂ (x i) '' P i, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖ = 0 := by
    intro i hi
    rw [hPN i (not_lt.1 (Finset.mem_range.not.1 hi)), image_empty, Measure.restrict_empty,
      lintegral_zero_measure]
  calc quadDiffNorm q
      ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖ := by
        unfold quadDiffNorm surfaceIntegral
        exact iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP le_rfl))
    _ = ∑ i ∈ Finset.range N,
          ∫⁻ z in chartAt ℂ (x i) '' P i, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q (x i) z‖ :=
        tsum_eq_sum hzero
    _ < ⊤ := ENNReal.sum_lt_top.2 fun i _ => hterm i

/-- (iii) homogeneity of the surface integral in `q` (a chart partition exists). -/
theorem s26_surfaceIntegral_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] (q : S → ℂ → ℂ) (u : S → ℂ → ℝ≥0∞) (c : ℂ) :
    surfaceIntegral (c • q) u = ENNReal.ofReal ‖c‖ * surfaceIntegral q u := by
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero, ENNReal.ofReal_zero, zero_mul]
    obtain ⟨x, P, hP⟩ := s26_exists_chartPartition' (S := S)
    refine le_antisymm ?_ bot_le
    unfold surfaceIntegral
    refine iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP (le_of_eq ?_)))
    simp
  have h0 : ENNReal.ofReal ‖c‖ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact norm_pos_iff.2 hc
  have htop : ENNReal.ofReal ‖c‖ ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold surfaceIntegral
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun x => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [← lintegral_const_mul' _ _ htop]
  refine lintegral_congr fun z => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [ENNReal.ofReal_mul (norm_nonneg _)]
  ring

/-- (ii, `←`) `‖0‖ = 0`. -/
theorem s26_quadDiffNorm_zero {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [CompactSpace S] [Nonempty S] : quadDiffNorm (0 : S → ℂ → ℂ) = 0 :=
  s26_surfaceIntegral_eq_zero _ fun x z => by
    simp

/-- (ii, `→`) a non-zero holomorphic quadratic differential has positive norm: for any chart
partition, the pieces pulled back to a ball `B` where `q_{x₀} ≠ 0` cover `B`, and the change of
variables through the holomorphic transitions (with `|q_{xᵢ}| = |q_{x₀} ∘ τ| |τ'|²`) bounds the sum
below by `∫_B |q_{x₀}|`. -/
theorem s26_quadDiffNorm_pos [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) : quadDiffNorm q ≠ 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hx₀
  simp only [Pi.zero_apply] at hz₀
  have hz₀t : z₀ ∈ (chartAt ℂ x₀).target := by
    by_contra h
    exact hz₀ (hq'.1.1 x₀ z₀ h)
  -- a ball where `‖q x₀‖ ≥ ‖q x₀ z₀‖ / 2`
  have hcont : ContinuousAt (q x₀) z₀ :=
    ((hq'.2 x₀).differentiableAt ((chartAt ℂ x₀).open_target.mem_nhds hz₀t)).continuousAt
  have hpos : 0 < ‖q x₀ z₀‖ / 2 := half_pos (norm_pos_iff.2 hz₀)
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ball z₀ ε ⊆ (chartAt ℂ x₀).target ∧
      ∀ z ∈ ball z₀ ε, ‖q x₀ z₀‖ / 2 ≤ ‖q x₀ z‖ := by
    obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 (chartAt ℂ x₀).open_target _ hz₀t
    obtain ⟨ε₂, hε₂, h₂⟩ := Metric.continuousAt_iff.1 hcont _ hpos
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (ball_subset_ball (min_le_left _ _)).trans h₁, fun z hz => ?_⟩
    have h := h₂ (lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _))
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (q x₀ z₀) (q x₀ z)
    rw [norm_sub_rev] at h
    linarith
  set B := ball z₀ ε
  have hBpos : 0 < ENNReal.ofReal (‖q x₀ z₀‖ / 2) * volume B :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hpos).ne' (measure_ball_pos volume z₀ hε).ne'
  refine (lt_of_lt_of_le hBpos ?_).ne'
  unfold quadDiffNorm surfaceIntegral
  refine le_iInf fun x => le_iInf fun P => le_iInf fun hP => ?_
  obtain ⟨hPsm, -, hcov⟩ := hP
  have hPs : ∀ i, P i ⊆ (chartAt ℂ (x i)).source := fun i => (hPsm i).1
  have hPm : ∀ i, MeasurableSet (chartAt ℂ (x i) '' P i) := fun i => (hPsm i).2
  set e₀ := chartAt ℂ x₀
  -- the transition `σᵢ = φ_{x₀} ∘ φ_{xᵢ}⁻¹` and the pulled back pieces `Sᵢ`
  let σ : ℕ → ℂ → ℂ := fun i => chartTransition x₀ (x i)
  let D : ℕ → Set ℂ := fun i => (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' e₀.source
  let T : ℕ → Set ℂ := fun i => chartAt ℂ (x i) '' P i ∩ (D i ∩ σ i ⁻¹' B)
  have hDo : ∀ i, IsOpen (D i ∩ σ i ⁻¹' B) := fun i => by
    have hco : ContinuousOn (σ i) (D i) := fun w hw =>
      (s23_transition_differentiableAt x₀ (x i) hw.1 hw.2).continuousAt.continuousWithinAt
    exact hco.isOpen_inter_preimage ((chartAt ℂ (x i)).isOpen_inter_preimage_symm e₀.open_source)
      isOpen_ball
  have hTm : ∀ i, MeasurableSet (T i) := fun i => (hPm i).inter (hDo i).measurableSet
  have hTD : ∀ i, T i ⊆ D i := fun i w hw => hw.2.1
  -- the pieces cover `B`
  have hcoverB : B ⊆ ⋃ i, σ i '' T i := by
    intro z hz
    have hzt : z ∈ e₀.target := hball.1 hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ (e₀.symm z) : e₀.symm z ∈ ⋃ i, P i)
    refine mem_iUnion.2 ⟨i, chartAt ℂ (x i) (e₀.symm z), ⟨⟨e₀.symm z, hi, rfl⟩, ?_, ?_⟩, ?_⟩
    · refine ⟨(chartAt ℂ (x i)).map_source (hPs i hi), ?_⟩
      rw [mem_preimage, (chartAt ℂ (x i)).left_inv (hPs i hi)]
      exact e₀.map_target hzt
    · show chartTransition x₀ (x i) (chartAt ℂ (x i) (e₀.symm z)) ∈ B
      simp only [chartTransition]
      rw [(chartAt ℂ (x i)).left_inv (hPs i hi), e₀.right_inv hzt]
      exact hz
    · show chartTransition x₀ (x i) (chartAt ℂ (x i) (e₀.symm z)) = z
      simp only [chartTransition]
      rw [(chartAt ℂ (x i)).left_inv (hPs i hi), e₀.right_inv hzt]
  -- change of variables on each piece
  have hcv : ∀ i, ∫⁻ z in σ i '' T i, ENNReal.ofReal ‖q x₀ z‖ =
      ∫⁻ w in T i, ENNReal.ofReal ‖q (x i) w‖ := by
    intro i
    have hdiff : ∀ w ∈ T i, DifferentiableAt ℂ (σ i) w := fun w hw =>
      s23_transition_differentiableAt x₀ (x i) (hTD i hw).1 (hTD i hw).2
    have hinj : InjOn (σ i) (T i) := by
      intro w₁ hw₁ w₂ hw₂ h
      have h' : e₀ ((chartAt ℂ (x i)).symm w₁) = e₀ ((chartAt ℂ (x i)).symm w₂) := h
      have h'' := e₀.injOn (hTD i hw₁).2 (hTD i hw₂).2 h'
      rw [← (chartAt ℂ (x i)).right_inv (hTD i hw₁).1, ← (chartAt ℂ (x i)).right_inv (hTD i hw₂).1,
        h'']
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hTm i)
      (fun w hw => ((hdiff w hw).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
    refine setLIntegral_congr_fun (hTm i) fun w hw => ?_
    have hd := hdiff w hw
    have hdet : (fderiv ℝ (σ i) w).det = ‖deriv (σ i) w‖ ^ 2 := by
      have e := det_fderiv_eq_jacobian (hd.restrictScalars ℝ)
      rw [show (fderiv ℝ (σ i) w).det = LinearMap.det (fderiv ℝ (σ i) w : ℂ →ₗ[ℝ] ℂ) from rfl, e,
        jacobian, dz_eq_deriv hd, (cauchyRiemann_iff.1 hd).2, norm_zero]
      ring
    have hlaw : q (x i) w = q x₀ (σ i w) * deriv (σ i) w ^ 2 := by
      have h := hq'.1.2 x₀ (x i) w (hTD i hw).1 (hTD i hw).2
      rw [h]
      norm_num
      rfl
    rw [hdet, abs_of_nonneg (by positivity), hlaw, norm_mul, norm_pow, ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  calc ENNReal.ofReal (‖q x₀ z₀‖ / 2) * volume B
      = ∫⁻ _ in B, ENNReal.ofReal (‖q x₀ z₀‖ / 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in B, ENNReal.ofReal ‖q x₀ z‖ :=
        setLIntegral_mono' measurableSet_ball fun z hz => ENNReal.ofReal_le_ofReal (hball.2 z hz)
    _ ≤ ∫⁻ z in ⋃ i, σ i '' T i, ENNReal.ofReal ‖q x₀ z‖ := lintegral_mono_set hcoverB
    _ ≤ ∑' i, ∫⁻ z in σ i '' T i, ENNReal.ofReal ‖q x₀ z‖ := lintegral_iUnion_le _ _
    _ = ∑' i, ∫⁻ w in T i, ENNReal.ofReal ‖q (x i) w‖ := tsum_congr hcv
    _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, (fun _ _ => (1 : ℝ≥0∞)) (x i) z *
          ENNReal.ofReal ‖q (x i) z‖ :=
        ENNReal.tsum_le_tsum fun i => by
          simp only [one_mul]
          exact lintegral_mono_set inter_subset_left

/-- §26.2: `‖·‖` is a norm on `Q(S₀)`, finite on a compact surface. -/
theorem quadDiffNorm_finite [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) :
    quadDiffNorm q < ⊤ ∧ (quadDiffNorm q = 0 ↔ q = 0) ∧
      ∀ c : ℂ, quadDiffNorm (c • q) = ENNReal.ofReal ‖c‖ * quadDiffNorm q := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  refine ⟨s26_quadDiffNorm_lt_top hq, ⟨fun h => ?_, fun h => h ▸ s26_quadDiffNorm_zero⟩,
    fun c => s26_surfaceIntegral_smul q _ c⟩
  by_contra hne
  exact s26_quadDiffNorm_pos hq hne h

/-- §26.2: `Q₁(S₀) = {q ∈ Q(S₀) : ‖q‖ = 1}`. -/
def unitQuadDiffs (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] : Set (S → ℂ → ℂ) :=
  {q | IsHolQuadDiff q ∧ quadDiffNorm q = 1}

/-! ### Helpers for `teichDeformation_smul` (`s26_`): regular points, zeros and natural parameters of
`c • q` -/

/-- `c • q` is regular at `p` iff `q` is (for `c ≠ 0`). -/
theorem s26_isRegularPoint_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {q : S → ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (p : S) :
    IsRegularPoint (c • q) p ↔ IsRegularPoint q p := by
  simp only [IsRegularPoint, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]

/-- `c • q` has a zero of order `m` at `p` iff `q` has (for `c ≠ 0`). -/
theorem s26_isZeroOfOrder_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {q : S → ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (p : S) (m : ℕ) :
    IsZeroOfOrder (c • q) p m ↔ IsZeroOfOrder q p m := by
  unfold IsZeroOfOrder
  rw [Pi.smul_apply, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]

/-- The new parameter at a regular point is real-homogeneous: `S_k(rζ) = r S_k(ζ)` for real `r`. -/
theorem s26_teichStretch_ofReal_mul (k r : ℝ) (ζ : ℂ) :
    teichStretch k ((r : ℂ) * ζ) = (r : ℂ) * teichStretch k ζ := by
  unfold teichStretch
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- A natural parameter of `q` at a regular point, scaled by `√c`, is one of `c q` (`c > 0`). -/
theorem s26_isNaturalParameterAt_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {q : S → ℂ → ℂ} {p : S} {ζ : ℂ → ℂ} (h : IsNaturalParameterAt q p ζ) {c : ℝ} (hc : 0 < c) :
    IsNaturalParameterAt ((c : ℂ) • q) p (fun z => (Real.sqrt c : ℂ) * ζ z) := by
  obtain ⟨ha, h0, hd, hev⟩ := h
  have hs : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hc).ne'
  have hs2 : (Real.sqrt c : ℂ) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc.le]
  refine ⟨analyticAt_const.mul ha, by simp [h0], ?_, ?_⟩
  · rw [deriv_const_mul_field']
    exact mul_ne_zero hs hd
  · filter_upwards [hev] with z hz
    rw [deriv_const_mul_field', mul_pow, hz, hs2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]

/-- A natural parameter of `q` at a zero of order `m`, scaled by `c^{1/(m+2)}`, is one of `c q`. -/
theorem s26_isNaturalParameterAtZero_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {q : S → ℂ → ℂ} {p : S} {m : ℕ} {ζ : ℂ → ℂ} (h : IsNaturalParameterAtZero q p m ζ) {c : ℝ}
    (hc : 0 < c) :
    IsNaturalParameterAtZero ((c : ℂ) • q) p m
      (fun z => ((c ^ (((m + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) * ζ z) := by
  obtain ⟨ha, h0, hd, hev⟩ := h
  set r : ℝ := c ^ (((m + 2 : ℕ) : ℝ)⁻¹) with hr_def
  have hr : 0 < r := Real.rpow_pos_of_pos hc _
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrn : (r : ℂ) ^ (m + 2) = (c : ℂ) := by
    rw [← Complex.ofReal_pow, hr_def, Real.rpow_inv_natCast_pow hc.le (by omega)]
  refine ⟨analyticAt_const.mul ha, by simp [h0], ?_, ?_⟩
  · rw [deriv_const_mul_field']
    exact mul_ne_zero hr0 hd
  · filter_upwards [hev] with z hz
    rw [deriv_const_mul_field', Pi.smul_apply, Pi.smul_apply, smul_eq_mul, hz, ← hrn]
    ring

/-- §26.2: for `c > 0`, `cq` and `q` have the same natural parameters, so `S_{cq,k} = S_{q,k}`: a
Teichmüller deformation for `q` is one for `cq` (with terminal differential `cq'`). -/
theorem teichDeformation_smul {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier}
    {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') {c : ℝ} (hc : 0 < c) :
    IsTeichDeformation ((c : ℂ) • q) k X e ((c : ℂ) • q') := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨(holQuadDiffSubmodule S₀).smul_mem (c : ℂ) h.initial, smul_ne_zero hc0 h.initial_ne,
    h.k_nonneg, h.k_lt_one, (holQuadDiffSubmodule X.carrier).smul_mem (c : ℂ) h.terminal, ?_, ?_⟩
  · intro p hp
    obtain ⟨hr, ζ, ζ', hζ, hζ', hrel⟩ := h.regular p ((s26_isRegularPoint_smul hc0 p).1 hp)
    refine ⟨(s26_isRegularPoint_smul hc0 (e p)).2 hr, fun z => (Real.sqrt c : ℂ) * ζ z,
      fun w => (Real.sqrt c : ℂ) * ζ' w, s26_isNaturalParameterAt_smul hζ hc,
      s26_isNaturalParameterAt_smul hζ' hc, ?_⟩
    filter_upwards [hrel] with z hz
    rw [hz, s26_teichStretch_ofReal_mul]
  · intro p m hp
    obtain ⟨hr, ζ, ζ', hζ, hζ', hrel⟩ := h.zero p m ((s26_isZeroOfOrder_smul hc0 p m).1 hp)
    have hpos : 0 < c ^ (((m + 2 : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos hc _
    refine ⟨(s26_isZeroOfOrder_smul hc0 (e p) m).2 hr,
      fun z => ((c ^ (((m + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) * ζ z,
      fun w => ((c ^ (((m + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) * ζ' w,
      s26_isNaturalParameterAtZero_smul hζ hc, s26_isNaturalParameterAtZero_smul hζ' hc, ?_⟩
    filter_upwards [hrel] with z hz
    rw [hz, teichStretchZero_ofReal_mul hpos]

/-- §26.2 (Teichmüller 形变空间): the deformation space `T̃(S₀)` is described by `q ∈ Q₁(S₀)` (`6g - 7`
real parameters) and `k ∈ [0, 1)`, i.e. by `6g - 6` real parameters: it corresponds to the open unit
ball of `ℝ^{6g-6}` via `(q, k) ↦ k · (coordinates of q)` for a basis of `Q(S₀)`. -/
theorem teichDeformationSpace_parameters [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    Module.finrank ℝ (holQuadDiffSubmodule S₀) = 6 * g - 6 ∧
      ∃ e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)),
        ∀ v : EuclideanSpace ℝ (Fin (6 * g - 6)), ‖v‖ < 1 →
          (v = 0 ∨ ∃ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), 0 < k ∧ k < 1 ∧
            ‖e q‖ = 1 ∧ v = k • e q) := by
  sorry

/-! ## §26.3 Teichmüller maps -/

/-- **§26.3 (Teichmüller 映射).**  `f : S₀ → S` is a Teichmüller map with initial quadratic
differential `q ∈ Q(S₀)` and terminal quadratic differential `q' ∈ Q(S)`, `k ∈ [0, 1)`: `f` is
quasiconformal, maps regular points of `q` to regular points of `q'` and zeros of order `n` to
zeros of order `n`, and near regular points its local expression in the natural parameters is
`ζ ↦ ζ' = (ζ + kζ̄)/(1 - k)`. -/
structure IsTeichmullerMap (f : S₀ ≃ₜ S₁) (q : S₀ → ℂ → ℂ) (q' : S₁ → ℂ → ℂ) (k : ℝ) : Prop where
  qc : IsQCRS f
  initial : IsHolQuadDiff q
  initial_ne : q ≠ 0
  terminal : IsHolQuadDiff q'
  k_nonneg : 0 ≤ k
  k_lt_one : k < 1
  regular : ∀ p : S₀, IsRegularPoint q p → IsRegularPoint q' (f p) ∧
    ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAt q p ζ ∧ IsNaturalParameterAt q' (f p) ζ' ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr f p z) = teichStretch k (ζ z)
  zero : ∀ (p : S₀) (n : ℕ), IsZeroOfOrder q p n → IsZeroOfOrder q' (f p) n

/-- §26.2 (Teichmüller 形变映射): the deformation map `f₀ : S₀ → S_{q,k}` is a Teichmüller map with
initial differential `q` and terminal differential `q'`. -/
theorem teichDeformation_isTeichmullerMap {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}}
    {e : S₀ ≃ₜ X.carrier} {q' : X.carrier → ℂ → ℂ} (h : IsTeichDeformation q k X e q') :
    IsTeichmullerMap e q q' k := by
  exact ⟨⟨_, s26u_isKQCRS h⟩, h.initial, h.initial_ne, h.terminal, h.k_nonneg, h.k_lt_one, h.regular,
    fun p n hp => (h.zero p n hp).1⟩

/-- §26.3: the Beltrami differential `k φ̄/|φ|` associated with `q = φ dz²` and `k`; in natural
parameters it is `k dζ̄/dζ`. -/
def teichmullerBeltrami (k : ℝ) (q : S₀ → ℂ → ℂ) : S₀ → ℂ → ℂ :=
  fun x z => (k : ℂ) * conj (q x z) / (‖q x z‖ : ℂ)

/-- The `(-1, 1)` transformation law of `k φ̄/|φ|` under `φ ↦ φ τ'²`, pointwise and with no condition
on `τ'`: for `τ' = 0` (or `φ = 0`) both sides vanish. -/
theorem teichmullerBeltrami_transform_aux (k : ℝ) (Q D : ℂ) :
    (k : ℂ) * conj (Q * D ^ 2) / (‖Q * D ^ 2‖ : ℂ) =
      (k : ℂ) * conj Q / (‖Q‖ : ℂ) * D ^ (-1 : ℤ) * conj D ^ (1 : ℤ) := by
  by_cases hD : D = 0
  · simp [hD]
  by_cases hQ : Q = 0
  · simp [hQ]
  have hQn : (‖Q‖ : ℂ) ≠ 0 := by simpa using hQ
  have hDc : conj D ≠ 0 := by simpa using hD
  have hDD : (‖D‖ : ℂ) ^ 2 = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [zpow_neg_one, zpow_one, map_mul, map_pow, norm_mul, norm_pow, Complex.ofReal_mul,
    Complex.ofReal_pow, hDD]
  field_simp

/-- §26.3: `k φ̄/|φ|` is a Beltrami differential with `‖μ‖_∞ = k` (undefined at the zeros of `q`,
which are isolated).

In Lean, `μ` takes the value `0` at the zeros of `q` (since `x/0 = 0`), and the statement asserts
`‖μ‖_∞ ≤ k`.

Proof: the `(-1, 1)` law holds at every point of a chart overlap (`teichmullerBeltrami_transform_aux`).
From `q_y = q_x(τ) τ'²` one gets `conj(τ')²/|τ'|² = τ'⁻¹ conj τ'`, and when `τ' = 0` or
`q_x(τ) = 0` both sides vanish.  Measurability comes from the continuity of `q x` on the chart
target, and `|μ| = k|q|/|q| ≤ k` holds pointwise. -/
theorem teichmullerBeltrami_isBeltramiDifferential {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) : IsBeltramiDifferential (teichmullerBeltrami k q) k := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  refine ⟨fun x y => ?_, fun x => ⟨?_, ?_⟩⟩
  · -- the `(-1, 1)` law holds at every point of the overlap
    have hS : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
      ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).measurableSet
    refine ae_restrict_of_forall_mem hS fun z hz => ?_
    have h2 : q y z = q x (chartTransition x y z) * deriv (chartTransition x y) z ^ 2 := by
      rw [hq'.1.2 x y z hz.1 hz.2]
      norm_num
    show (k : ℂ) * conj (q y z) / (‖q y z‖ : ℂ) =
      (k : ℂ) * conj (q x (chartTransition x y z)) / (‖q x (chartTransition x y z)‖ : ℂ) *
        deriv (chartTransition x y) z ^ (-1 : ℤ) * conj (deriv (chartTransition x y) z) ^ (1 : ℤ)
    rw [h2]
    exact teichmullerBeltrami_transform_aux k _ _
  · -- measurability: `q x` is continuous on the chart target
    have hcont : ContinuousOn (q x) (chartAt ℂ x).target := (hq'.2 x).continuousOn
    have hm : AEMeasurable (q x) (volume.restrict (chartAt ℂ x).target) :=
      (hcont.aestronglyMeasurable (chartAt ℂ x).open_target.measurableSet).aemeasurable
    have hc : AEMeasurable (fun z => conj (q x z)) (volume.restrict (chartAt ℂ x).target) :=
      Complex.continuous_conj.measurable.comp_aemeasurable hm
    have hn : AEMeasurable (fun z => (‖q x z‖ : ℂ)) (volume.restrict (chartAt ℂ x).target) :=
      Complex.measurable_ofReal.comp_aemeasurable hm.norm
    have hmeas : AEMeasurable (fun z => (k : ℂ) * conj (q x z) / (‖q x z‖ : ℂ))
        (volume.restrict (chartAt ℂ x).target) :=
      (hc.const_mul (k : ℂ)).div hn
    exact hmeas.aestronglyMeasurable
  · -- `|k φ̄/|φ|| ≤ k` everywhere
    refine ae_of_all _ fun z => ?_
    show ‖(k : ℂ) * conj (q x z) / (‖q x z‖ : ℂ)‖ ≤ k
    by_cases h0 : q x z = 0
    · simp [h0, hk₀]
    refine le_of_eq ?_
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hk₀, Real.norm_of_nonneg (norm_nonneg _), mul_div_assoc,
      div_self (norm_ne_zero_iff.2 h0), mul_one]

/-! ### Helpers for `teichmullerMap_beltrami` (`s26b_`): the Beltrami differential of a Teichmüller map -/

/-- The Wirtinger derivatives of the stretch `teichStretch k ζ = (ζ + k ζ̄)/(1 - k)`: `∂ = 1/(1-k)` and
`∂̄ = k/(1-k)` at every point (it is the affine map `ζ ↦ (1-k)⁻¹ ζ + (k/(1-k)) ζ̄`). -/
theorem s26b_teichStretch_dz_dzbar (k : ℝ) (w : ℂ) :
    dz (teichStretch k) w = (1 - (k : ℂ))⁻¹ ∧ dzbar (teichStretch k) w = (k : ℂ) / (1 - k) := by
  have heq : teichStretch k = fun z => (1 - (k : ℂ))⁻¹ * z + ((k : ℂ) / (1 - k)) * conj z := by
    funext z
    simp only [teichStretch]
    ring
  have hd : HasFDerivAt (teichStretch k) ((1 - (k : ℂ))⁻¹ • ContinuousLinearMap.id ℝ ℂ +
      ((k : ℂ) / (1 - k)) • (conjCLE : ℂ →L[ℝ] ℂ)) w := by
    rw [heq]
    exact ((hasFDerivAt_id w).const_mul _).add ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul _)
  constructor
  · rw [dz, hd.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination ((((k : ℂ) / (1 - k)) - (1 - (k : ℂ))⁻¹) / 2) * I_sq
  · rw [dzbar, hd.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination (((1 - (k : ℂ))⁻¹ - ((k : ℂ) / (1 - k))) / 2) * I_sq

/-- The complex dilatation of the stretch `teichStretch k` is the constant `k` (for `k < 1`). -/
theorem s26b_teichStretch_dilatation {k : ℝ} (hk : k < 1) (w : ℂ) :
    complexDilatation (teichStretch k) w = k := by
  obtain ⟨h1, h2⟩ := s26b_teichStretch_dz_dzbar k w
  have h1k : (1 - (k : ℂ)) ≠ 0 := by
    have : (1 - k : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  rw [complexDilatation, h1, h2]
  field_simp

/-- The dilatation quotient `(|∂| + |∂̄|)/(|∂| - |∂̄|)` of the stretch `teichStretch k` is
`(1 + k)/(1 - k)` at every point (for `0 ≤ k < 1`). -/
theorem s26b_teichStretch_quot {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (w : ℂ) :
    (‖dz (teichStretch k) w‖ + ‖dzbar (teichStretch k) w‖) /
      (‖dz (teichStretch k) w‖ - ‖dzbar (teichStretch k) w‖) = (1 + k) / (1 - k) := by
  obtain ⟨h1, h2⟩ := s26b_teichStretch_dz_dzbar k w
  have h1k : 0 < 1 - k := by linarith
  have hc : (1 - (k : ℂ)) = ((1 - k : ℝ) : ℂ) := by push_cast; ring
  have hn1 : ‖(1 - (k : ℂ))⁻¹‖ = 1 / (1 - k) := by
    rw [hc, norm_inv, Complex.norm_real, Real.norm_of_nonneg h1k.le, one_div]
  have hn2 : ‖(k : ℂ) / (1 - k)‖ = k / (1 - k) := by
    rw [hc, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hk₀,
      Real.norm_of_nonneg h1k.le]
  rw [h1, h2, hn1, hn2, ← add_div, ← sub_div, div_div_div_cancel_right₀ h1k.ne']

/-- **Local conjugation, dilatation form.**  If near `z₀` one has `B ∘ g = S_k ∘ A`, `S_k = teichStretch k`,
with `A`, `B` holomorphic with nonzero derivative (at `z₀`, resp. `g z₀`) and `g` continuous at `z₀`, then
`μ_g(z₀) = k conj A'(z₀)/A'(z₀)` and the dilatation quotient of `g` at `z₀` is `(1 + k)/(1 - k)`
(`s23_dilatation_comp_left/right`, `s23_quot_comp_left/right`, with the local inverses of `A` and `B`). -/
theorem s26b_conj_local {g A B : ℂ → ℂ} {z₀ : ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hA : AnalyticAt ℂ A z₀) (hA' : deriv A z₀ ≠ 0) (hB : AnalyticAt ℂ B (g z₀))
    (hB' : deriv B (g z₀) ≠ 0) (hg : ContinuousAt g z₀)
    (hBg : ∀ᶠ w in 𝓝 z₀, B (g w) = teichStretch k (A w)) :
    complexDilatation g z₀ = k * (conj (deriv A z₀) / deriv A z₀) ∧
      (‖dz g z₀‖ + ‖dzbar g z₀‖) / (‖dz g z₀‖ - ‖dzbar g z₀‖) = (1 + k) / (1 - k) := by
  have hAs := hA.hasStrictDerivAt
  have hBs := hB.hasStrictDerivAt
  have hBl := hBs.eventually_left_inverse hB'
  have hBi := (HasStrictDerivAt.hasDerivAt (hBs.to_localInverse hB')).differentiableAt
  have hAl := hAs.eventually_left_inverse hA'
  have hAr := hAs.eventually_right_inverse hA'
  have hAi := (HasStrictDerivAt.hasDerivAt (hAs.to_localInverse hA')).differentiableAt
  have hev : (B ∘ g) =ᶠ[𝓝 z₀] (teichStretch k ∘ A) := hBg
  have hdz : dz (B ∘ g) z₀ = dz (teichStretch k ∘ A) z₀ := by
    simp only [dz, hev.fderiv_eq (𝕜 := ℝ)]
  have hdzbar : dzbar (B ∘ g) z₀ = dzbar (teichStretch k ∘ A) z₀ := by
    simp only [dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  constructor
  · rw [← s23_dilatation_comp_left hg hB.differentiableAt hBi hBl, complexDilatation, hdz, hdzbar,
      ← complexDilatation, s23_dilatation_comp_right hA.differentiableAt hAi hAl hAr,
      s26b_teichStretch_dilatation hk]
  · rw [← s23_quot_comp_left hg hB.differentiableAt hBi hBl, hdz, hdzbar,
      s23_quot_comp_right hA.differentiableAt hAi hAl hAr, s26b_teichStretch_quot hk₀ hk]

/-- **The local form of a Teichmüller map at a point where `q_x ≠ 0`.**  With `p = φ_x⁻¹ z₀` (a regular
point of `q`, so `f p` is a regular point of `q'`), natural parameters `ζ` at `p` and `ζ'` at `f p`,
`τ = φ_p ∘ φ_x⁻¹` and `σ = φ_{f p} ∘ φ_{f x}⁻¹` (both holomorphic with nonzero derivative by
`s26u_transition_analyticAt`, the second one through `q'`), the local expression `g` of `f` at `x`
satisfies `(ζ' ∘ σ) ∘ g = S_k ∘ (ζ ∘ τ)` near `z₀`, and `((ζ ∘ τ)'(z₀))² = q_x(z₀)`
(the transformation law `s26u_law`). -/
theorem s26b_local {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (x : S₀) {z₀ : ℂ} (hz₀ : z₀ ∈ localMapDomain f x)
    (hq0 : q x z₀ ≠ 0) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ deriv A z₀ ^ 2 = q x z₀ ∧
      AnalyticAt ℂ B (localMapExpr f x z₀) ∧ deriv B (localMapExpr f x z₀) ≠ 0 ∧
      ∀ᶠ w in 𝓝 z₀, B (localMapExpr f x w) = teichStretch k (A w) := by
  have hz₀t : z₀ ∈ (chartAt ℂ x).target := hz₀.1
  set p := (chartAt ℂ x).symm z₀
  have hfp : f p ∈ (chartAt ℂ (f x)).source := hz₀.2
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff hf.initial x hz₀t).2 hq0
  obtain ⟨hreg', ζ, ζ', hζ, hζ', hrel⟩ := hf.regular p hreg
  obtain ⟨hτan, -⟩ := s26u_transition_analyticAt hf.initial x p hz₀t (mem_chart_source ℂ p) hq0
  have hτz : chartTransition p x z₀ = chartAt ℂ p p := rfl
  have hζan : AnalyticAt ℂ ζ (chartTransition p x z₀) := by
    rw [hτz]
    exact hζ.1
  have hAan : AnalyticAt ℂ (ζ ∘ chartTransition p x) z₀ := hζan.comp hτan
  have hAd : deriv (ζ ∘ chartTransition p x) z₀ ^ 2 = q x z₀ := by
    rw [deriv_comp z₀ hζan.differentiableAt hτan.differentiableAt, hτz, mul_pow,
      hζ.2.2.2.self_of_nhds, s26u_law hf.initial x p hz₀t (mem_chart_source ℂ p), hτz]
  have hgt : localMapExpr f x z₀ ∈ (chartAt ℂ (f x)).target := (chartAt ℂ (f x)).map_source hfp
  have hgs : (chartAt ℂ (f x)).symm (localMapExpr f x z₀) = f p := (chartAt ℂ (f x)).left_inv hfp
  have hgs' : (chartAt ℂ (f x)).symm (localMapExpr f x z₀) ∈ (chartAt ℂ (f p)).source := by
    rw [hgs]
    exact mem_chart_source ℂ (f p)
  have hq'0 : q' (f x) (localMapExpr f x z₀) ≠ 0 :=
    (s26u_isRegularPoint_iff hf.terminal (f x) hgt).1 (by rw [hgs]; exact hreg')
  obtain ⟨hσan, hσd⟩ := s26u_transition_analyticAt hf.terminal (f x) (f p) hgt hgs' hq'0
  have hσz : chartTransition (f p) (f x) (localMapExpr f x z₀) = chartAt ℂ (f p) (f p) := by
    simp only [chartTransition, hgs]
  have hζ'an : AnalyticAt ℂ ζ' (chartTransition (f p) (f x) (localMapExpr f x z₀)) := by
    rw [hσz]
    exact hζ'.1
  have hBan : AnalyticAt ℂ (ζ' ∘ chartTransition (f p) (f x)) (localMapExpr f x z₀) := hζ'an.comp hσan
  have hBd : deriv (ζ' ∘ chartTransition (f p) (f x)) (localMapExpr f x z₀) ≠ 0 := by
    rw [deriv_comp _ hζ'an.differentiableAt hσan.differentiableAt, hσz]
    exact mul_ne_zero hζ'.2.2.1 hσd
  have hΩ : localMapDomain f x ∈ 𝓝 z₀ := (s23_localMapDomain_isOpen f.continuous x).mem_nhds hz₀
  have hτc : Tendsto (chartTransition p x) (𝓝 z₀) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]
    exact hτan.continuousAt.tendsto
  refine ⟨ζ ∘ chartTransition p x, ζ' ∘ chartTransition (f p) (f x), hAan, hAd, hBan, hBd, ?_⟩
  filter_upwards [hτc.eventually hrel, hΩ, ((chartAt ℂ x).isOpen_inter_preimage_symm
    (chartAt ℂ p).open_source).mem_nhds ⟨hz₀t, mem_chart_source ℂ p⟩] with w hw1 hw2 hw3
  simp only [Function.comp_apply]
  rw [← hw1]
  congr 1
  simp only [chartTransition, localMapExpr]
  rw [(chartAt ℂ (f x)).left_inv hw2.2, (chartAt ℂ p).left_inv hw3.2]

/-- **The pointwise identities at a point where `q_x ≠ 0`.**  There the local expression `g` of a
Teichmüller map has `μ_g = k q̄_x/|q_x|` (`μ_g = k conj A'/A'` with `A'² = q_x`) and dilatation quotient
`(1 + k)/(1 - k)` (`s26b_local`, `s26b_conj_local`). -/
theorem s26b_pointwise {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (x : S₀) {z₀ : ℂ} (hz₀ : z₀ ∈ localMapDomain f x)
    (hq0 : q x z₀ ≠ 0) :
    complexDilatation (localMapExpr f x) z₀ = teichmullerBeltrami k q x z₀ ∧
      (‖dz (localMapExpr f x) z₀‖ + ‖dzbar (localMapExpr f x) z₀‖) /
        (‖dz (localMapExpr f x) z₀‖ - ‖dzbar (localMapExpr f x) z₀‖) = (1 + k) / (1 - k) := by
  obtain ⟨A, B, hA, hAq, hB, hB', hBg⟩ := s26b_local hf x hz₀ hq0
  have hA' : deriv A z₀ ≠ 0 := fun h0 => hq0 (by rw [← hAq, h0]; ring)
  have hgc : ContinuousAt (localMapExpr f x) z₀ := by
    have h1 : ContinuousAt (fun z => f ((chartAt ℂ x).symm z)) z₀ :=
      f.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz₀.1)
    exact ContinuousAt.comp (g := chartAt ℂ (f x)) (f := fun z => f ((chartAt ℂ x).symm z))
      ((chartAt ℂ (f x)).continuousAt hz₀.2) h1
  obtain ⟨h1, h2⟩ := s26b_conj_local hf.k_nonneg hf.k_lt_one hA hA' hB hB' hgc hBg
  refine ⟨?_, h2⟩
  rw [h1]
  show _ = (k : ℂ) * conj (q x z₀) / (‖q x z₀‖ : ℂ)
  rw [← hAq]
  have hDc : conj (deriv A z₀) ≠ 0 := by simpa using hA'
  have hDD : (‖deriv A z₀‖ : ℂ) ^ 2 = deriv A z₀ * conj (deriv A z₀) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [map_pow, norm_pow, Complex.ofReal_pow, hDD]
  field_simp

/-- §26.3: the Beltrami differential of a Teichmüller map is `k φ̄/|φ| dz̄/dz`
(`k dζ̄/dζ = k q̄/|q| = k φ̄/|φ| · dz̄²/|dz|²`), and its maximal dilatation is `K = (1+k)/(1-k)`.

**Correction.**  The hypothesis `[ConnectedSpace S₀]` was missing, and the statement was **false**: on
the disconnected surface `{Re z ≠ 0}` with `q = 0` on the left half-plane, a Teichmüller map may have
complex dilatation `1/3` there, while `k q̄/|q| = 0`. -/
theorem teichmullerMap_beltrami [ConnectedSpace S₀] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) :
    (∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) ∧
      maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) := by
  have hT1 : T1Space S₀ := ChartedSpace.t1Space ℂ S₀
  have hae : ∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)), q x z ≠ 0 := by
    intro x
    refine (ae_restrict_iff' (s23_localMapDomain_isOpen f.continuous x).measurableSet).2 ?_
    filter_upwards [(s26u_zeros_countable hf.initial hf.initial_ne x).ae_notMem volume] with z hzZ hz h0
    exact hzZ ⟨hz.1, h0⟩
  refine ⟨fun x => ?_, ?_⟩
  · filter_upwards [hae x, ae_restrict_mem (s23_localMapDomain_isOpen f.continuous x).measurableSet]
      with z hz0 hz
    exact (s26b_pointwise hf x hz hz0).1
  · have hK : ∀ x : S₀, maxDilatation (localMapExpr f x) (localMapDomain f x) =
        ENNReal.ofReal ((1 + k) / (1 - k)) := by
      intro x
      have hΩ := s23_localMapDomain_isOpen f.continuous x
      have hne : (localMapDomain f x).Nonempty := by
        refine ⟨chartAt ℂ x x, (chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
        show f ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ (chartAt ℂ (f x)).source
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        exact mem_chart_source ℂ (f x)
      have hμ : volume.restrict (localMapDomain f x) ≠ 0 := by
        rw [Ne, Measure.restrict_eq_zero]
        exact hΩ.measure_ne_zero volume hne
      rw [maxDilatation, essSup_congr_ae (g := fun _ => ENNReal.ofReal ((1 + k) / (1 - k))),
        essSup_const _ hμ]
      filter_upwards [hae x, ae_restrict_mem hΩ.measurableSet] with z hz0 hz
      rw [(s26b_pointwise hf x hz hz0).2]
    rw [maxDilatationRS]
    simp only [hK]
    exact iSup_const

/-! ### Helpers for `teichmullerMap_factor` (`s26d_b_`): the pull-back of the structure of `S₁` by a
Teichmüller map is a Teichmüller deformation of `S₀` -/

/-- A punctured open disc is preconnected: it is the image of `(0, δ) × ℝ` under polar coordinates. -/
theorem s26d_b_isPreconnected_punctured (z₀ : ℂ) (δ : ℝ) : IsPreconnected (ball z₀ δ \ {z₀}) := by
  have h : (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo 0 δ ×ˢ univ) =
      ball z₀ δ \ {z₀} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      show z₀ + (r : ℂ) * exp (θ * I) ∈ ball z₀ δ \ {z₀}
      have hn : ‖(r : ℂ) * exp (θ * I)‖ = r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr.1.le]
      refine ⟨?_, fun h0 => ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hn]
        exact hr.2
      · have h2 : z₀ + (r : ℂ) * exp (θ * I) = z₀ := h0
        have h1 : (r : ℂ) * exp (θ * I) = 0 := by linear_combination h2
        rw [← norm_eq_zero, hn] at h1
        exact hr.1.ne' h1
    · rintro ⟨hz, hz0⟩
      refine ⟨(‖z - z₀‖, arg (z - z₀)), ⟨⟨norm_pos_iff.2 (sub_ne_zero.2 hz0), ?_⟩, mem_univ _⟩, ?_⟩
      · rwa [mem_ball, dist_eq_norm] at hz
      · show z₀ + ((‖z - z₀‖ : ℝ) : ℂ) * exp ((arg (z - z₀) : ℂ) * I) = z
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
  rw [← h]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (Continuous.continuousOn (by fun_prop))

/-- A continuous `n`-th root of unity on a preconnected set is constant: if `G^n = H^n` there, with `G`, `H`
continuous and `H ≠ 0`, then `G = εH` for a single `ε` with `εⁿ = 1`. -/
theorem s26d_b_eq_root_mul {D : Set ℂ} (hD : IsPreconnected D) {n : ℕ} (hn : 0 < n) {G H : ℂ → ℂ}
    (hG : ContinuousOn G D) (hH : ContinuousOn H D) (hH0 : ∀ z ∈ D, H z ≠ 0)
    (hGH : ∀ z ∈ D, G z ^ n = H z ^ n) : ∃ ε : ℂ, ε ^ n = 1 ∧ ∀ z ∈ D, G z = ε * H z := by
  have hfin : ({ε : ℂ | ε ^ n = 1}).Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun ε hε => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hn).2 hε
  have hc : ContinuousOn (fun z => G z / H z) D := hG.div hH hH0
  have hmaps : MapsTo (fun z => G z / H z) D {ε : ℂ | ε ^ n = 1} := fun z hz => by
    show (G z / H z) ^ n = 1
    rw [div_pow, hGH z hz, div_self (pow_ne_zero _ (hH0 z hz))]
  rcases D.eq_empty_or_nonempty with hDe | ⟨z₁, hz₁⟩
  · exact ⟨1, one_pow _, fun z hz => by simp [hDe] at hz⟩
  refine ⟨G z₁ / H z₁, hmaps hz₁, fun z hz => ?_⟩
  have h : G z / H z = G z₁ / H z₁ := hD.constant_of_mapsTo hfin.isDiscrete hc hmaps hz hz₁
  rw [← h, div_mul_cancel₀ _ (hH0 z hz)]

/-- **Propagation to the puncture.**  Suppose that near every point `z₁` of the punctured disc
`D = B(z₀, δ) ∖ {z₀}` one has `P = T²` and `Φ = (T + c)²` for a constant `c` and a function `T` injective near
`z₁`, and that `Φ`, `P` are continuous at `z₀` and vanish there.  Then `Φ = P` on the whole disc.

Proof: `β = c²` is determined near each point by `(Φ - P - β)² = 4βP` (two values `β ≠ β'` would force
`2T² + 2cT + c² = const`, i.e. `T` takes at most two values); the sets where a given `β` works are open and
disjoint and cover the preconnected `D`, so one `β` works on all of `D`; letting `z → z₀` gives `β² = 0`. -/
theorem s26d_b_eq_of_local {Φ P : ℂ → ℂ} {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hΦ : ContinuousAt Φ z₀) (hP : ContinuousAt P z₀) (hΦ0 : Φ z₀ = 0) (hP0 : P z₀ = 0)
    (hloc : ∀ z₁ ∈ ball z₀ δ \ {z₀}, ∃ T : ℂ → ℂ, ∃ c : ℂ, ∃ U ∈ 𝓝 z₁,
      InjOn T U ∧ ∀ z ∈ U, T z ^ 2 = P z ∧ Φ z = (T z + c) ^ 2) :
    ∀ z ∈ ball z₀ δ, Φ z = P z := by
  set D : Set ℂ := ball z₀ δ \ {z₀} with hDdef
  have hDo : IsOpen D := isOpen_ball.sdiff isClosed_singleton
  set E : ℂ → Set ℂ := fun β => {z | z ∈ D ∧ ∀ᶠ w in 𝓝 z, (Φ w - P w - β) ^ 2 = 4 * β * P w}
    with hEdef
  have hEo : ∀ β, IsOpen (E β) := by
    intro β
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hDo.mem_nhds hz.1, hz.2.eventually_nhds] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  have hex : ∀ z₁ ∈ D, ∃ β, z₁ ∈ E β := by
    intro z₁ hz₁
    obtain ⟨T, c, U, hU, -, hTU⟩ := hloc z₁ hz₁
    refine ⟨c ^ 2, hz₁, ?_⟩
    filter_upwards [hU] with w hw
    obtain ⟨h1, h2⟩ := hTU w hw
    rw [h2, ← h1]
    ring
  have huniq : ∀ z₁ ∈ D, ∀ β β', z₁ ∈ E β → z₁ ∈ E β' → β = β' := by
    intro z₁ hz₁ β β' hβ hβ'
    by_contra hne
    obtain ⟨T, c, U, hU, hTi, hTU⟩ := hloc z₁ hz₁
    have hq : ∀ᶠ w in 𝓝 z₁, w ∈ U ∧ 4 * T w ^ 2 + 4 * c * T w + (2 * c ^ 2 - β - β') = 0 := by
      filter_upwards [hU, hβ.2, hβ'.2] with w hw h1 h2
      refine ⟨hw, ?_⟩
      obtain ⟨h3, h4⟩ := hTU w hw
      have h5 : (β - β') * (β + β' - 2 * (Φ w - P w) - 4 * P w) = 0 := by linear_combination h1 - h2
      have h6 : β + β' - 2 * (Φ w - P w) - 4 * P w = 0 :=
        (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hne)
      rw [h4, ← h3] at h6
      linear_combination -h6
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hq
    have hp : ∀ t : ℝ, 0 ≤ t → t < ε → dist (z₁ + (t : ℂ)) z₁ < ε := fun t ht0 ht => by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht0]
      exact ht
    obtain ⟨hU1, e1⟩ := hball (mem_ball_self hε)
    obtain ⟨hU2, e2⟩ := hball (hp (ε / 2) (by positivity) (by linarith))
    obtain ⟨hU3, e3⟩ := hball (hp (ε / 3) (by positivity) (by linarith))
    have hne12 : T z₁ ≠ T (z₁ + ((ε / 2 : ℝ) : ℂ)) := fun h => by
      have h1 := hTi hU1 hU2 h
      have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination -h1
      have h3 : ε / 2 = 0 := by exact_mod_cast h2
      linarith
    have hne13 : T z₁ ≠ T (z₁ + ((ε / 3 : ℝ) : ℂ)) := fun h => by
      have h1 := hTi hU1 hU3 h
      have h2 : ((ε / 3 : ℝ) : ℂ) = 0 := by linear_combination -h1
      have h3 : ε / 3 = 0 := by exact_mod_cast h2
      linarith
    have hne23 : T (z₁ + ((ε / 2 : ℝ) : ℂ)) ≠ T (z₁ + ((ε / 3 : ℝ) : ℂ)) := fun h => by
      have h1 := hTi hU2 hU3 h
      have h2 : ((ε / 2 : ℝ) : ℂ) = ((ε / 3 : ℝ) : ℂ) := by linear_combination h1
      have h3 : ε / 2 = ε / 3 := by exact_mod_cast h2
      linarith
    have h12 : T z₁ + T (z₁ + ((ε / 2 : ℝ) : ℂ)) + c = 0 := by
      have h : (T z₁ - T (z₁ + ((ε / 2 : ℝ) : ℂ))) * (4 * (T z₁ + T (z₁ + ((ε / 2 : ℝ) : ℂ)) + c)) = 0 := by
        linear_combination e1 - e2
      exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne12))).resolve_left
        (by norm_num : (4 : ℂ) ≠ 0)
    have h13 : T z₁ + T (z₁ + ((ε / 3 : ℝ) : ℂ)) + c = 0 := by
      have h : (T z₁ - T (z₁ + ((ε / 3 : ℝ) : ℂ))) * (4 * (T z₁ + T (z₁ + ((ε / 3 : ℝ) : ℂ)) + c)) = 0 := by
        linear_combination e1 - e3
      exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne13))).resolve_left
        (by norm_num : (4 : ℂ) ≠ 0)
    exact hne23 (by linear_combination h12 - h13)
  -- `D` is nonempty and preconnected, so a single `β₁` works on all of `D`
  have hzD : z₀ + ((δ / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, fun h => ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    · have h2 : z₀ + ((δ / 2 : ℝ) : ℂ) = z₀ := h
      have h3 : ((δ / 2 : ℝ) : ℂ) = 0 := by linear_combination h2
      have h4 : δ / 2 = 0 := by exact_mod_cast h3
      linarith
  obtain ⟨β₁, hβ₁⟩ := hex _ hzD
  have hsub : D ⊆ E β₁ := by
    refine (s26d_b_isPreconnected_punctured z₀ δ).subset_left_of_subset_union (hEo β₁)
      (isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≠ β₁ => hEo β) ?_ ?_ ⟨_, hzD, hβ₁⟩
    · rw [Set.disjoint_left]
      intro z hz hz'
      rw [mem_iUnion₂] at hz'
      obtain ⟨β, hβ, hzβ⟩ := hz'
      exact hβ (huniq z hz.1 β β₁ hzβ hz)
    · intro z hz
      obtain ⟨β, hzβ⟩ := hex z hz
      by_cases hβ : β = β₁
      · left
        rw [← hβ]
        exact hzβ
      · right
        exact mem_iUnion₂.2 ⟨β, hβ, hzβ⟩
  -- the limit at the puncture gives `β₁ = 0`
  have hF : ContinuousAt (fun w => (Φ w - P w - β₁) ^ 2 - 4 * β₁ * P w) z₀ := by fun_prop
  have hDn : D ∈ 𝓝[≠] z₀ :=
    mem_nhdsWithin.2 ⟨ball z₀ δ, isOpen_ball, mem_ball_self hδ, fun w hw => ⟨hw.1, hw.2⟩⟩
  have hFD : ∀ᶠ w in 𝓝[≠] z₀, (fun w => (Φ w - P w - β₁) ^ 2 - 4 * β₁ * P w) w = (fun _ => (0 : ℂ)) w := by
    filter_upwards [hDn] with w hw
    have h1 := (hsub hw).2.self_of_nhds
    show (Φ w - P w - β₁) ^ 2 - 4 * β₁ * P w = 0
    rw [h1]
    ring
  have h0 : (Φ z₀ - P z₀ - β₁) ^ 2 - 4 * β₁ * P z₀ = 0 :=
    eq_of_continuousAt_of_eventuallyEq_nhdsNE hF continuousAt_const hFD
  rw [hΦ0, hP0] at h0
  have hβ0 : β₁ = 0 := by
    have h1 : β₁ ^ 2 = 0 := by linear_combination h0
    exact (pow_eq_zero_iff two_ne_zero).1 h1
  intro z hz
  by_cases hz0 : z = z₀
  · rw [hz0, hΦ0, hP0]
  · have h1 := (hsub ⟨hz, hz0⟩).2.self_of_nhds
    rw [hβ0] at h1
    have h2 : (Φ z - P z) ^ 2 = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

/-- The stretch `teichStretch k` is injective for `0 ≤ k < 1`: its real form is `x + iy ↦ Kx + iy` with `K > 0`. -/
theorem s26d_b_teichStretch_injective {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) :
    Function.Injective (teichStretch k) := by
  intro a b h
  obtain ⟨ha1, ha2⟩ := s26u_teichStretch_real_form hk a
  obtain ⟨hb1, hb2⟩ := s26u_teichStretch_real_form hk b
  have hK : 0 < (1 + k) / (1 - k) := div_pos (by linarith) (by linarith)
  apply Complex.ext
  · have h1 := congrArg Complex.re h
    rw [ha1, hb1] at h1
    exact mul_left_cancel₀ hK.ne' h1
  · have h1 := congrArg Complex.im h
    rwa [ha2, hb2] at h1

/-- `teichStretchZero k 0 = teichStretch k`: at a zero of order `0` (a regular point) the new parameter is the
stretch. -/
theorem s26d_b_teichStretchZero_zero (k : ℝ) : teichStretchZero k 0 = teichStretch k := by
  funext ζ
  unfold teichStretchZero teichStretch
  by_cases hζ : ζ = 0
  · simp [hζ]
  simp only [hζ, ite_false]
  have h1 : ((2 : ℂ) / (((0 : ℕ) : ℂ) + 2)) = 1 := by norm_num
  rw [h1, Complex.cpow_one, Complex.cpow_one]
  congr 1
  have hDD : (‖ζ‖ : ℂ) ^ 2 = ζ * conj ζ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [div_pow, hDD]
  have hc : conj ζ ≠ 0 := by simpa using hζ
  field_simp
  ring

/-- **A branch of `ζ^{(m+2)/2}` is a natural parameter** near a point `a` with `ζ(a) ≠ 0`, when
`φ = ((m+2)/2)² ζ^m ζ'²` near `a`: an analytic `W` with `W² = ζ^{m+2}` (everywhere) and `W'² = φ` near `a`. -/
theorem s26d_b_branch {ζ φ : ℂ → ℂ} {a : ℂ} {m : ℕ} (hζ : AnalyticAt ℂ ζ a) (hζa : ζ a ≠ 0)
    (hφ : ∀ᶠ z in 𝓝 a, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) :
    ∃ W : ℂ → ℂ, AnalyticAt ℂ W a ∧ (∀ z, W z ^ 2 = ζ z ^ (m + 2)) ∧
      ∀ᶠ z in 𝓝 a, deriv W z ^ 2 = φ z := by
  obtain ⟨W, hW, -, hW2', -⟩ := exists_analyticAt_sq_eq (hζ.pow (m + 2)) (pow_ne_zero _ hζa)
  have hW2 : ∀ z, W z ^ 2 = ζ z ^ (m + 2) := fun z => by rw [hW2' z, Pi.pow_apply]
  refine ⟨W, hW, hW2, ?_⟩
  have hfun : (fun z => W z ^ 2) = fun z => ζ z ^ (m + 2) := funext hW2
  filter_upwards [hφ, hW.eventually_analyticAt, hζ.eventually_analyticAt,
    hζ.continuousAt.eventually_ne hζa] with z hφz hWz hζz hζ0
  have h1 : HasDerivAt (fun z => W z ^ 2) (((2 : ℕ) : ℂ) * W z ^ (2 - 1) * deriv W z) z :=
    hWz.differentiableAt.hasDerivAt.pow 2
  have h2 : HasDerivAt (fun z => ζ z ^ (m + 2)) (((m + 2 : ℕ) : ℂ) * ζ z ^ (m + 2 - 1) * deriv ζ z) z :=
    hζz.differentiableAt.hasDerivAt.pow (m + 2)
  rw [hfun] at h1
  have h3 := h1.unique h2
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1] at h3
  norm_num at h3
  have h4 : (2 * W z * deriv W z) ^ 2 = (((m : ℂ) + 2) * ζ z ^ (m + 1) * deriv ζ z) ^ 2 := by rw [h3]
  have hWz2 := hW2 z
  rw [hφz]
  refine mul_left_cancel₀ (pow_ne_zero (m + 2) hζ0) ?_
  linear_combination (1 / 4 : ℂ) * h4 - deriv W z ^ 2 * hWz2

/-- A zero of order `m` in the preferred chart: `q_p(z) = (z - z₀)^m ψ(z)` near `z₀ = φ_p(p)`, with `ψ` analytic
at `z₀` and `ψ(z₀) ≠ 0` (the coefficient `q_p` is holomorphic on the chart target). -/
theorem s26d_b_zero_factor {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {p : S₀} {m : ℕ}
    (hm : IsZeroOfOrder q p m) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (chartAt ℂ p p) ∧ ψ (chartAt ℂ p p) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), q p z = (z - chartAt ℂ p p) ^ m * ψ z := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have han : AnalyticAt ℂ (q p) (chartAt ℂ p p) :=
    (hq'.2 p).analyticAt ((chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))
  have h1 : analyticOrderAt (q p) (chartAt ℂ p p) = m := by
    have h : meromorphicOrderAt (q p) (chartAt ℂ p p) = (m : ℤ) := hm
    rw [han.meromorphicOrderAt_eq] at h
    cases h2 : analyticOrderAt (q p) (chartAt ℂ p p) with
    | top =>
      rw [h2, ENat.map_top] at h
      exact absurd h WithTop.top_ne_coe
    | coe n =>
      rw [h2, ENat.map_natCast] at h
      have h3 : ((n : ℕ) : ℤ) = (m : ℤ) := WithTop.coe_injective h
      have h4 : n = m := by exact_mod_cast h3
      rw [h4]
  obtain ⟨ψ, hψ, hψ0, hψq⟩ := han.analyticOrderAt_eq_natCast.1 h1
  exact ⟨ψ, hψ, hψ0, by simpa only [smul_eq_mul] using hψq⟩

/-- **Local comparison with fixed branches.**  If `B ∘ L = S_k ∘ A` near `z₁` (`S_k = teichStretch k`), where
`A`, `W` are natural parameters of the same `φ` near `z₁` (`A'² = W'² = φ`, `φ(z₁) ≠ 0`) and `B`, `W'` are natural
parameters of the same `φ'` near `L z₁`, then `W' ∘ L = ε S_k(W) + c` near `z₁` with `ε = ±1`
(`eq25_3_natural_parameter_unique` twice, then `eq26_4`). -/
theorem s26d_b_local_affine {k : ℝ} {A W B W' L φ φ' : ℂ → ℂ} {z₁ : ℂ}
    (hA : AnalyticAt ℂ A z₁) (hAd : ∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = φ z)
    (hW : AnalyticAt ℂ W z₁) (hWd : ∀ᶠ z in 𝓝 z₁, deriv W z ^ 2 = φ z) (hφ : φ z₁ ≠ 0)
    (hB : AnalyticAt ℂ B (L z₁)) (hBd : ∀ᶠ w in 𝓝 (L z₁), deriv B w ^ 2 = φ' w)
    (hW' : AnalyticAt ℂ W' (L z₁)) (hW'd : ∀ᶠ w in 𝓝 (L z₁), deriv W' w ^ 2 = φ' w)
    (hφ' : φ' (L z₁) ≠ 0) (hL : ContinuousAt L z₁)
    (hrel : ∀ᶠ z in 𝓝 z₁, B (L z) = teichStretch k (A z)) :
    ∃ ε c : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ z in 𝓝 z₁, W' (L z) = ε * teichStretch k (W z) + c := by
  have hsA : ∃ ε₁ : ℂ, (ε₁ = 1 ∨ ε₁ = -1) ∧
      ∀ᶠ z in 𝓝 z₁, A z = ε₁ * W z + (A z₁ - ε₁ * W z₁) := by
    have h := eq25_3_natural_parameter_unique (φ := φ) (ζ := fun z => A z - A z₁)
      (ζ₁ := fun z => W z - W z₁) (hA.sub analyticAt_const) (hW.sub analyticAt_const) (sub_self _)
      (sub_self _) (by simpa only [deriv_sub_const] using hAd) (by simpa only [deriv_sub_const] using hWd) hφ
    rcases h with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      filter_upwards [h] with z hz
      linear_combination hz
    · refine ⟨-1, Or.inr rfl, ?_⟩
      filter_upwards [h] with z hz
      linear_combination hz
  have hsB : ∃ ε₂ : ℂ, (ε₂ = 1 ∨ ε₂ = -1) ∧
      ∀ᶠ w in 𝓝 (L z₁), B w = ε₂ * W' w + (B (L z₁) - ε₂ * W' (L z₁)) := by
    have h := eq25_3_natural_parameter_unique (φ := φ') (ζ := fun w => B w - B (L z₁))
      (ζ₁ := fun w => W' w - W' (L z₁)) (hB.sub analyticAt_const) (hW'.sub analyticAt_const) (sub_self _)
      (sub_self _) (by simpa only [deriv_sub_const] using hBd) (by simpa only [deriv_sub_const] using hW'd)
      hφ'
    rcases h with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      filter_upwards [h] with w hw
      linear_combination hw
    · refine ⟨-1, Or.inr rfl, ?_⟩
      filter_upwards [h] with w hw
      linear_combination hw
  obtain ⟨ε₁, hε₁, hA1⟩ := hsA
  obtain ⟨ε₂, hε₂, hB1⟩ := hsB
  have hε₂sq : ε₂ * ε₂ = 1 := by rcases hε₂ with rfl | rfl <;> norm_num
  refine ⟨ε₂ * ε₁, ε₂ * (teichStretch k (A z₁ - ε₁ * W z₁) - (B (L z₁) - ε₂ * W' (L z₁))), ?_, ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> norm_num
  · filter_upwards [hrel, hA1, hL.eventually hB1] with z h1 h2 h3
    rw [h2, eq26_4 k ε₁ hε₁, h3] at h1
    linear_combination ε₂ * h1 - W' (L z) * hε₂sq

/-- **The local form at a regular point, with natural parameters read in the chart at `x`** (a strengthening of
`s26b_local`): near a point `z₀` of the domain of `L = localMapExpr f x` with `q_x(z₀) ≠ 0` one has
`B ∘ L = S_k ∘ A` with `A'² = q_x` near `z₀`, `B'² = q'_{f x}` near `L z₀` and `B'(L z₀) ≠ 0`. -/
theorem s26d_b_local {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (x : S₀) {z₀ : ℂ} (hz₀ : z₀ ∈ localMapDomain f x)
    (hq0 : q x z₀ ≠ 0) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ (∀ᶠ z in 𝓝 z₀, deriv A z ^ 2 = q x z) ∧
      AnalyticAt ℂ B (localMapExpr f x z₀) ∧ deriv B (localMapExpr f x z₀) ≠ 0 ∧
      (∀ᶠ w in 𝓝 (localMapExpr f x z₀), deriv B w ^ 2 = q' (f x) w) ∧
      ∀ᶠ w in 𝓝 z₀, B (localMapExpr f x w) = teichStretch k (A w) := by
  have hz₀t : z₀ ∈ (chartAt ℂ x).target := hz₀.1
  set p := (chartAt ℂ x).symm z₀
  have hfp : f p ∈ (chartAt ℂ (f x)).source := hz₀.2
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff hf.initial x hz₀t).2 hq0
  obtain ⟨hreg', ζ, ζ', hζ, hζ', hrel⟩ := hf.regular p hreg
  obtain ⟨hτan, -⟩ := s26u_transition_analyticAt hf.initial x p hz₀t (mem_chart_source ℂ p) hq0
  have hτz : chartTransition p x z₀ = chartAt ℂ p p := rfl
  have hζan : AnalyticAt ℂ ζ (chartTransition p x z₀) := by
    rw [hτz]
    exact hζ.1
  have hAan : AnalyticAt ℂ (ζ ∘ chartTransition p x) z₀ := hζan.comp hτan
  have hτc : Tendsto (chartTransition p x) (𝓝 z₀) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]
    exact hτan.continuousAt.tendsto
  have hAd : ∀ᶠ z in 𝓝 z₀, deriv (ζ ∘ chartTransition p x) z ^ 2 = q x z := by
    filter_upwards [hτc.eventually hζ.2.2.2, hτc.eventually hζ.1.eventually_analyticAt,
      hτan.eventually_analyticAt, ((chartAt ℂ x).isOpen_inter_preimage_symm
        (chartAt ℂ p).open_source).mem_nhds ⟨hz₀t, mem_chart_source ℂ p⟩] with z h1 h2 h3 h4
    rw [deriv_comp z h2.differentiableAt h3.differentiableAt, mul_pow, h1,
      s26u_law hf.initial x p h4.1 h4.2]
  have hgt : localMapExpr f x z₀ ∈ (chartAt ℂ (f x)).target := (chartAt ℂ (f x)).map_source hfp
  have hgs : (chartAt ℂ (f x)).symm (localMapExpr f x z₀) = f p := (chartAt ℂ (f x)).left_inv hfp
  have hgs' : (chartAt ℂ (f x)).symm (localMapExpr f x z₀) ∈ (chartAt ℂ (f p)).source := by
    rw [hgs]
    exact mem_chart_source ℂ (f p)
  have hq'0 : q' (f x) (localMapExpr f x z₀) ≠ 0 :=
    (s26u_isRegularPoint_iff hf.terminal (f x) hgt).1 (by rw [hgs]; exact hreg')
  obtain ⟨hσan, hσd⟩ := s26u_transition_analyticAt hf.terminal (f x) (f p) hgt hgs' hq'0
  have hσz : chartTransition (f p) (f x) (localMapExpr f x z₀) = chartAt ℂ (f p) (f p) := by
    simp only [chartTransition, hgs]
  have hζ'an : AnalyticAt ℂ ζ' (chartTransition (f p) (f x) (localMapExpr f x z₀)) := by
    rw [hσz]
    exact hζ'.1
  have hBan : AnalyticAt ℂ (ζ' ∘ chartTransition (f p) (f x)) (localMapExpr f x z₀) := hζ'an.comp hσan
  have hBd : deriv (ζ' ∘ chartTransition (f p) (f x)) (localMapExpr f x z₀) ≠ 0 := by
    rw [deriv_comp _ hζ'an.differentiableAt hσan.differentiableAt, hσz]
    exact mul_ne_zero hζ'.2.2.1 hσd
  have hσc : Tendsto (chartTransition (f p) (f x)) (𝓝 (localMapExpr f x z₀))
      (𝓝 (chartAt ℂ (f p) (f p))) := by
    rw [← hσz]
    exact hσan.continuousAt.tendsto
  have hBd2 : ∀ᶠ w in 𝓝 (localMapExpr f x z₀),
      deriv (ζ' ∘ chartTransition (f p) (f x)) w ^ 2 = q' (f x) w := by
    filter_upwards [hσc.eventually hζ'.2.2.2, hσc.eventually hζ'.1.eventually_analyticAt,
      hσan.eventually_analyticAt, ((chartAt ℂ (f x)).isOpen_inter_preimage_symm
        (chartAt ℂ (f p)).open_source).mem_nhds ⟨hgt, hgs'⟩] with w h1 h2 h3 h4
    rw [deriv_comp w h2.differentiableAt h3.differentiableAt, mul_pow, h1,
      s26u_law hf.terminal (f x) (f p) h4.1 h4.2]
  have hΩ : localMapDomain f x ∈ 𝓝 z₀ := (s23_localMapDomain_isOpen f.continuous x).mem_nhds hz₀
  refine ⟨ζ ∘ chartTransition p x, ζ' ∘ chartTransition (f p) (f x), hAan, hAd, hBan, hBd, hBd2, ?_⟩
  filter_upwards [hτc.eventually hrel, hΩ, ((chartAt ℂ x).isOpen_inter_preimage_symm
    (chartAt ℂ p).open_source).mem_nhds ⟨hz₀t, mem_chart_source ℂ p⟩] with w hw1 hw2 hw3
  simp only [Function.comp_apply]
  rw [← hw1]
  congr 1
  simp only [chartTransition, localMapExpr]
  rw [(chartAt ℂ (f x)).left_inv hw2.2, (chartAt ℂ p).left_inv hw3.2]

/-- **The `zero` field of the pulled-back deformation.**  At a zero `p` of order `m` of `q` take natural parameters
`ζ` at `p` and `ζ₂` at `f p` (`eq25_5_natural_parameter_zero`), and put `L = localMapExpr f p`,
`S_{k,m} = teichStretchZero k m`.  Near each point `z₁ ≠ φ_p(p)` a branch `W` of `ζ^{(m+2)/2}` is a natural parameter of
`q` (`s26d_b_branch`), and the regular form gives `W₂ ∘ L = ±S_k(W) + c` (`s26d_b_local_affine`), so that
`(ζ₂ ∘ L)^{m+2} = (T + c)²` with `T² = S_{k,m}(ζ)^{m+2}` (`eq26_6`); `s26d_b_eq_of_local` gives
`(ζ₂ ∘ L)^{m+2} = S_{k,m}(ζ)^{m+2}`.  The quotient `(ζ₂ ∘ L)/S_{k,m}(ζ)` is then a continuous `(m+2)`-th root of
unity on the punctured disc, hence a constant `ε` (`s26d_b_eq_root_mul`), and `ζ' = ε⁻¹ ζ₂` works.  For `m = 0` this
is the `regular` field (`s26d_b_teichStretchZero_zero`). -/
theorem s26d_b_zero_local {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (p : S₀) (m : ℕ) (hm : IsZeroOfOrder q p m) :
    ∃ ζ ζ' : ℂ → ℂ, IsNaturalParameterAtZero q p m ζ ∧ IsNaturalParameterAtZero q' (f p) m ζ' ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), ζ' (localMapExpr f p z) = teichStretchZero k m (ζ z) := by
  have hk₀ := hf.k_nonneg
  have hk := hf.k_lt_one
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- `m = 0`: a regular point, and `teichStretchZero k 0 = teichStretch k`
    obtain ⟨ψ, -, hψ0, hψq⟩ := s26d_b_zero_factor hf.initial hm
    have hreg : IsRegularPoint q p := by
      show q p (chartAt ℂ p p) ≠ 0
      rw [hψq.self_of_nhds, pow_zero, one_mul]
      exact hψ0
    obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hf.regular p hreg
    refine ⟨ζ, ζ', ⟨hζ.1, hζ.2.1, hζ.2.2.1, ?_⟩, ⟨hζ'.1, hζ'.2.1, hζ'.2.2.1, ?_⟩, ?_⟩
    · filter_upwards [hζ.2.2.2] with z hz
      rw [← hz]
      norm_num
    · filter_upwards [hζ'.2.2.2] with z hz
      rw [← hz]
      norm_num
    · rw [s26d_b_teichStretchZero_zero]
      exact hrel
  -- `m ≥ 1`: natural parameters at the two zeros
  obtain ⟨ψ, hψ, hψ0, hψq⟩ := s26d_b_zero_factor hf.initial hm
  obtain ⟨ψ', hψ', hψ'0, hψ'q⟩ := s26d_b_zero_factor hf.terminal (hf.zero p m hm)
  obtain ⟨ζ, hζan, hζ0, hζd, hζq⟩ := eq25_5_natural_parameter_zero hm0 hψ hψ0 hψq
  obtain ⟨ζ₂, hζ₂an, hζ₂0, hζ₂d, hζ₂q⟩ := eq25_5_natural_parameter_zero hm0 hψ' hψ'0 hψ'q
  obtain ⟨hz₀D, hLz₀⟩ := s23_h_center f p
  have hLc : ∀ z ∈ localMapDomain f p, ContinuousAt (localMapExpr f p) z := fun z hz => by
    have h1 : ContinuousAt (fun z => f ((chartAt ℂ p).symm z)) z :=
      f.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz.1)
    exact ContinuousAt.comp (g := chartAt ℂ (f p)) (f := fun z => f ((chartAt ℂ p).symm z))
      ((chartAt ℂ (f p)).continuousAt hz.2) h1
  have hLt : Tendsto (localMapExpr f p) (𝓝 (chartAt ℂ p p)) (𝓝 (chartAt ℂ (f p) (f p))) := by
    have h := (hLc _ hz₀D).tendsto
    rwa [hLz₀] at h
  obtain ⟨V, hVo, hz₀V, -, hVi⟩ := s26u_exists_open_injOn hζan hζd
  have hgood2 : ∀ᶠ w in 𝓝 (chartAt ℂ (f p) (f p)), AnalyticAt ℂ ζ₂ w ∧
      q' (f p) w = ((m + 2 : ℂ) / 2) ^ 2 * ζ₂ w ^ m * deriv ζ₂ w ^ 2 :=
    hζ₂an.eventually_analyticAt.and hζ₂q
  have hN : ∀ᶠ z in 𝓝 (chartAt ℂ p p), z ∈ localMapDomain f p ∧ z ∈ V ∧ AnalyticAt ℂ ζ z ∧
      (∀ᶠ z' in 𝓝 z, q p z' = ((m + 2 : ℂ) / 2) ^ 2 * ζ z' ^ m * deriv ζ z' ^ 2) ∧
      q p z = (z - chartAt ℂ p p) ^ m * ψ z ∧ ψ z ≠ 0 ∧
      (∀ᶠ w in 𝓝 (localMapExpr f p z), AnalyticAt ℂ ζ₂ w ∧
        q' (f p) w = ((m + 2 : ℂ) / 2) ^ 2 * ζ₂ w ^ m * deriv ζ₂ w ^ 2) := by
    filter_upwards [(s23_localMapDomain_isOpen f.continuous p).mem_nhds hz₀D, hVo.mem_nhds hz₀V,
      hζan.eventually_analyticAt, hζq.eventually_nhds, hψq, hψ.continuousAt.eventually_ne hψ0,
      hLt.eventually hgood2.eventually_nhds] with z h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hN
  -- the local representation near every point of the punctured disc
  have hloc : ∀ z₁ ∈ ball (chartAt ℂ p p) δ \ {chartAt ℂ p p}, ∃ T : ℂ → ℂ, ∃ c : ℂ, ∃ U ∈ 𝓝 z₁,
      InjOn T U ∧ ∀ z ∈ U, T z ^ 2 = teichStretchZero k m (ζ z) ^ (m + 2) ∧
        ζ₂ (localMapExpr f p z) ^ (m + 2) = (T z + c) ^ 2 := by
    intro z₁ hz₁
    obtain ⟨hD1, hV1, hζ1, hq1, hψq1, hψ1, hg1⟩ := hball hz₁.1
    have hz₁0 : z₁ ≠ chartAt ℂ p p := hz₁.2
    have hζz₁ : ζ z₁ ≠ 0 := fun h => hz₁0 (hVi hV1 hz₀V (h.trans hζ0.symm))
    have hqz₁ : q p z₁ ≠ 0 := by
      rw [hψq1]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hz₁0)) hψ1
    obtain ⟨A, B, hA, hAd, hB, hB', hBd, hBA⟩ := s26d_b_local hf p hD1 hqz₁
    obtain ⟨W, hW, hW2, hWd⟩ := s26d_b_branch hζ1 hζz₁ hq1
    have hq'1 : q' (f p) (localMapExpr f p z₁) ≠ 0 := by
      rw [← hBd.self_of_nhds]
      exact pow_ne_zero 2 hB'
    have hζ₂1 : ζ₂ (localMapExpr f p z₁) ≠ 0 := by
      intro h0
      apply hq'1
      rw [(hg1.self_of_nhds).2, h0, zero_pow hm0.ne', mul_zero, zero_mul]
    obtain ⟨W₂, hW₂, hW₂2, hW₂d⟩ := s26d_b_branch hg1.self_of_nhds.1 hζ₂1 (hg1.mono fun w hw => hw.2)
    obtain ⟨ε, c, hε, hrel⟩ :=
      s26d_b_local_affine hA hAd hW hWd hqz₁ hB hBd hW₂ hW₂d hq'1 (hLc z₁ hD1) hBA
    have hWd1 : deriv W z₁ ≠ 0 := fun h0 => hqz₁ (by rw [← hWd.self_of_nhds, h0]; ring)
    obtain ⟨U₀, hU₀o, hz₁U₀, -, hU₀i⟩ := s26u_exists_open_injOn hW hWd1
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    refine ⟨fun z => ε * teichStretch k (W z), c, {z | z ∈ U₀ ∧ ζ z ≠ 0 ∧
      ζ₂ (localMapExpr f p z) ^ (m + 2) = (ε * teichStretch k (W z) + c) ^ 2}, ?_, ?_, ?_⟩
    · filter_upwards [hU₀o.mem_nhds hz₁U₀, hζ1.continuousAt.eventually_ne hζz₁, hrel] with z h1 h2 h3
      refine ⟨h1, h2, ?_⟩
      rw [← hW₂2 (localMapExpr f p z), h3]
    · intro a ha b hb hab
      have h1 : teichStretch k (W a) = teichStretch k (W b) := mul_left_cancel₀ hε0 hab
      exact hU₀i ha.1 hb.1 (s26d_b_teichStretch_injective hk₀ hk h1)
    · intro z hz
      refine ⟨?_, hz.2.2⟩
      show (ε * teichStretch k (W z)) ^ 2 = teichStretchZero k m (ζ z) ^ (m + 2)
      rw [mul_pow, hεsq, one_mul, eq26_6 k m hz.2.1 (hW2 z)]
  -- `(ζ₂ ∘ L)^{m+2} = S_{k,m}(ζ)^{m+2}` on the disc
  have hTZc : Continuous (teichStretchZero k m) := (teichStretchZero_localHomeomorph hk₀ hk m).1
  have hTZ0 : teichStretchZero k m 0 = 0 := (teichStretchZero_localHomeomorph hk₀ hk m).2.1
  have hΦc : ContinuousAt (fun z => ζ₂ (localMapExpr f p z) ^ (m + 2)) (chartAt ℂ p p) := by
    have h1 : ContinuousAt ζ₂ (localMapExpr f p (chartAt ℂ p p)) := by
      rw [hLz₀]
      exact hζ₂an.continuousAt
    exact (h1.comp (hLc _ hz₀D)).pow (m + 2)
  have hPc : ContinuousAt (fun z => teichStretchZero k m (ζ z) ^ (m + 2)) (chartAt ℂ p p) :=
    (hTZc.continuousAt.comp hζan.continuousAt).pow (m + 2)
  have hΦ0 : ζ₂ (localMapExpr f p (chartAt ℂ p p)) ^ (m + 2) = 0 := by
    rw [hLz₀, hζ₂0, zero_pow (by omega)]
  have hP0 : teichStretchZero k m (ζ (chartAt ℂ p p)) ^ (m + 2) = 0 := by
    rw [hζ0, hTZ0, zero_pow (by omega)]
  have hEq := s26d_b_eq_of_local hδ hΦc hPc hΦ0 hP0 hloc
  -- the quotient is a constant root of unity
  obtain ⟨ε, hε, hεeq⟩ := s26d_b_eq_root_mul (s26d_b_isPreconnected_punctured (chartAt ℂ p p) δ)
    (by omega : 0 < m + 2) (G := fun z => ζ₂ (localMapExpr f p z)) (H := fun z => teichStretchZero k m (ζ z))
    (fun z hz => ((hball hz.1).2.2.2.2.2.2.self_of_nhds.1.continuousAt.comp
      (hLc z (hball hz.1).1)).continuousWithinAt)
    (fun z hz => (hTZc.continuousAt.comp (hball hz.1).2.2.1.continuousAt).continuousWithinAt)
    (fun z hz => teichStretchZero_ne_zero hk₀ hk m fun h =>
      hz.2 (hVi (hball hz.1).2.1 hz₀V (h.trans hζ0.symm)))
    (fun z hz => hEq z hz.1)
  have hε0 : ε ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hε
    exact zero_ne_one hε
  have hεinv : ε⁻¹ ^ (m + 2) = 1 := by rw [inv_pow, hε, inv_one]
  refine ⟨ζ, fun w => ε⁻¹ * ζ₂ w, ⟨hζan, hζ0, hζd, hζq⟩,
    ⟨analyticAt_const.mul hζ₂an, by simp [hζ₂0], ?_, ?_⟩, ?_⟩
  · rw [deriv_const_mul _ hζ₂an.differentiableAt]
    exact mul_ne_zero (inv_ne_zero hε0) hζ₂d
  · filter_upwards [hζ₂q, hζ₂an.eventually_analyticAt] with w hw hwa
    show q' (f p) w = ((m + 2 : ℂ) / 2) ^ 2 * (ε⁻¹ * ζ₂ w) ^ m * deriv (fun w => ε⁻¹ * ζ₂ w) w ^ 2
    rw [deriv_const_mul _ hwa.differentiableAt, hw]
    linear_combination (-(((m + 2 : ℂ) / 2) ^ 2 * ζ₂ w ^ m * deriv ζ₂ w ^ 2)) * hεinv
  · filter_upwards [ball_mem_nhds (chartAt ℂ p p) hδ] with z hz
    show ε⁻¹ * ζ₂ (localMapExpr f p z) = teichStretchZero k m (ζ z)
    by_cases hz0 : z = chartAt ℂ p p
    · rw [hz0, hLz₀, hζ₂0, hζ0, hTZ0, mul_zero]
    · have h1 : ζ₂ (localMapExpr f p z) = ε * teichStretchZero k m (ζ z) := hεeq z ⟨hz, hz0⟩
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hε0, one_mul]

/-- The underlying type of the pulled-back surface: a type synonym of `S`, so that instance search does not see the
charted-space structure of `S` on it. -/
def s26d_b_Pb (S : Type u) : Type u := S

/-- A charted space `M` whose charts are `φ_{F x} ∘ F` for a homeomorphism `F : M → S₁` onto a Riemann surface is a
Riemann surface: `(φ_{F x} ∘ F)⁻¹ ≫ (φ_{F y} ∘ F) = φ_{F x}⁻¹ ≫ φ_{F y}` is a chart transition of `S₁`.  The
topology and charts of `M` are implicit arguments, found by unification. -/
theorem s26d_b_isManifold {M : Type u} {tM : TopologicalSpace M} {cM : ChartedSpace ℂ M} [IsManifold 𝓘(ℂ) ω S₁]
    (F : M ≃ₜ S₁) (hch : ∀ x : M, chartAt ℂ x = F.transOpenPartialHomeomorph (chartAt ℂ (F x)))
    (hatlas : ∀ e ∈ atlas ℂ M, ∃ x : M, e = chartAt ℂ x) : IsManifold 𝓘(ℂ) ω M := by
  have hG : HasGroupoid M (contDiffGroupoid ω 𝓘(ℂ)) := by
    refine ⟨fun {e e'} he he' => ?_⟩
    obtain ⟨x, rfl⟩ := hatlas e he
    obtain ⟨y, rfl⟩ := hatlas e' he'
    have h : (F.transOpenPartialHomeomorph (chartAt ℂ (F x))).symm.trans
        (F.transOpenPartialHomeomorph (chartAt ℂ (F y))) = (chartAt ℂ (F x)).symm.trans (chartAt ℂ (F y)) := by
      rw [Homeomorph.transOpenPartialHomeomorph_eq_trans, Homeomorph.transOpenPartialHomeomorph_eq_trans,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc F.toOpenPartialHomeomorph.symm,
        ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
        Homeomorph.symm_trans_self, Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]
    rw [hch x, hch y, h]
    exact HasGroupoid.compatible (chart_mem_atlas ℂ (F x)) (chart_mem_atlas ℂ (F y))
  exact IsManifold.mk' 𝓘(ℂ) ω M

/-- `S₀` with the holomorphic structure pulled back from `S₁` by `f` (charts `φ_{f x} ∘ f`), as a closed Riemann
surface (`s26d_b_isManifold`). -/
def s26d_b_X [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₁] (f : S₀ ≃ₜ S₁) :
    ClosedRS.{u} :=
  @ClosedRS.mk (s26d_b_Pb S₀) (inferInstance : TopologicalSpace S₀) (inferInstance : T2Space S₀)
    (inferInstance : ConnectedSpace S₀) (inferInstance : CompactSpace S₀)
    (@ChartedSpace.mk ℂ _ (s26d_b_Pb S₀) (inferInstance : TopologicalSpace S₀)
      (Set.range fun x : S₀ => f.transOpenPartialHomeomorph (chartAt ℂ (f x)))
      (fun x : S₀ => f.transOpenPartialHomeomorph (chartAt ℂ (f x)))
      (fun x : S₀ => mem_chart_source ℂ (f x)) (fun x : S₀ => ⟨x, rfl⟩))
    (s26d_b_isManifold (M := s26d_b_Pb S₀) f (fun _ => rfl) fun _ ⟨x, hx⟩ => ⟨x, hx.symm⟩)

/-- The deformation map: the identity of the point set, from `S₀` onto the pulled-back surface. -/
def s26d_b_e [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₁] (f : S₀ ≃ₜ S₁) :
    S₀ ≃ₜ (s26d_b_X f).carrier :=
  Homeomorph.refl S₀

/-- `f` read as a homeomorphism from the pulled-back surface. -/
def s26d_b_F [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₁] (f : S₀ ≃ₜ S₁) :
    (s26d_b_X f).carrier ≃ₜ S₁ :=
  f

/-- A homeomorphism `F : X → S₁` whose charts are compatible, `φ_x = φ_{F x} ∘ F` (with inverse `F⁻¹ ∘ φ_{F x}⁻¹`), is
biholomorphic: in these charts `F` and `F⁻¹` are the identity. -/
theorem s26d_b_biholomorphic {X : ClosedRS.{u}} [IsManifold 𝓘(ℂ) ω S₁] (F : X.carrier ≃ₜ S₁)
    (hF : ∀ x y : X.carrier, chartAt ℂ x y = chartAt ℂ (F x) (F y))
    (hFs : ∀ (x : X.carrier) (z : ℂ), (chartAt ℂ x).symm z = F.symm ((chartAt ℂ (F x)).symm z)) :
    IsBiholomorphic (F : X.carrier → S₁) := by
  refine ⟨fun x => ?_, F.symm, fun y => ?_, F.symm_apply_apply, F.apply_symm_apply⟩
  · refine (s23_mdifferentiableAt_iff (mem_chart_source ℂ x) (mem_chart_source ℂ (F x))).2
      ⟨F.continuous.continuousAt, ?_⟩
    have hx : chartAt ℂ x x ∈ (chartAt ℂ (F x)).target := by
      rw [hF]
      exact (chartAt ℂ (F x)).map_source (mem_chart_source ℂ (F x))
    have heq : (fun z => chartAt ℂ (F x) (F ((chartAt ℂ x).symm z))) =ᶠ[𝓝 (chartAt ℂ x x)] id := by
      filter_upwards [(chartAt ℂ (F x)).open_target.mem_nhds hx] with z hz
      rw [hFs, F.apply_symm_apply, (chartAt ℂ (F x)).right_inv hz, id]
    exact differentiableAt_id.congr_of_eventuallyEq heq
  · refine (s23_mdifferentiableAt_iff (mem_chart_source ℂ y) (mem_chart_source ℂ (F.symm y))).2
      ⟨F.symm.continuous.continuousAt, ?_⟩
    have hy : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have heq : (fun z => chartAt ℂ (F.symm y) (F.symm ((chartAt ℂ y).symm z))) =ᶠ[𝓝 (chartAt ℂ y y)] id := by
      filter_upwards [(chartAt ℂ y).open_target.mem_nhds hy] with z hz
      rw [hF, F.apply_symm_apply, F.apply_symm_apply, (chartAt ℂ y).right_inv hz, id]
    exact differentiableAt_id.congr_of_eventuallyEq heq

/-- Under the chart compatibility `φ_x = φ_{F x} ∘ F` of a homeomorphism `F : X → S₁`, a holomorphic quadratic
differential `q'` on `S₁` read on `X`, `q' ∘ F`, is a holomorphic quadratic differential on `X`: the chart transitions
of `X` are those of `S₁`. -/
theorem s26d_b_terminal {X : ClosedRS.{u}} (F : X.carrier ≃ₜ S₁)
    (hF : ∀ x y : X.carrier, chartAt ℂ x y = chartAt ℂ (F x) (F y))
    (hFs : ∀ (x : X.carrier) (z : ℂ), (chartAt ℂ x).symm z = F.symm ((chartAt ℂ (F x)).symm z))
    (ht : ∀ x : X.carrier, (chartAt ℂ x).target = (chartAt ℂ (F x)).target)
    (hs : ∀ x : X.carrier, (chartAt ℂ x).source = F ⁻¹' (chartAt ℂ (F x)).source)
    {q' : S₁ → ℂ → ℂ} (hq' : IsHolQuadDiff q') : IsHolQuadDiff (fun x : X.carrier => q' (F x)) := by
  have h' : IsDiffFamily 2 0 q' ∧ ∀ y : S₁, DifferentiableOn ℂ (q' y) (chartAt ℂ y).target := hq'
  have key : IsDiffFamily 2 0 (fun x : X.carrier => q' (F x)) ∧
      ∀ x : X.carrier, DifferentiableOn ℂ (q' (F x)) (chartAt ℂ x).target := by
    refine ⟨⟨fun x z hz => h'.1.1 (F x) z (by rwa [ht] at hz), fun x y z hz hzx => ?_⟩,
      fun x => by rw [ht]; exact h'.2 (F x)⟩
    have hT : (chartTransition x y : ℂ → ℂ) = chartTransition (F x) (F y) := by
      funext w
      simp only [chartTransition]
      rw [hFs, hF, F.apply_symm_apply]
    have hzx' : (chartAt ℂ (F y)).symm z ∈ (chartAt ℂ (F x)).source := by
      rw [hs, hFs, Set.mem_preimage, F.apply_symm_apply] at hzx
      exact hzx
    rw [hT]
    exact h'.1.2 (F x) (F y) z (by rwa [ht] at hz) hzx'
  exact key

/-- §26.3: every Teichmüller map `f : S₀ → S` is a Teichmüller deformation map followed by a
conformal map: pulling the structure of `S` back by `f` gives `S' = S_{q,k}` with `f₀ = id`, and
`F = f : S' → S` is conformal. -/
theorem teichmullerMap_factor [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    ∃ (X : ClosedRS.{u}) (e : S₀ ≃ₜ X.carrier) (q'' : X.carrier → ℂ → ℂ) (F : X.carrier → S₁),
      IsTeichDeformation q k X e q'' ∧ IsBiholomorphic F ∧ ∀ p, f p = F (e p) := by
  have hF : ∀ x y : (s26d_b_X f).carrier, chartAt ℂ x y = chartAt ℂ (s26d_b_F f x) (s26d_b_F f y) :=
    fun _ _ => rfl
  have hFs : ∀ (x : (s26d_b_X f).carrier) (z : ℂ),
      (chartAt ℂ x).symm z = (s26d_b_F f).symm ((chartAt ℂ (s26d_b_F f x)).symm z) := fun _ _ => rfl
  have ht : ∀ x : (s26d_b_X f).carrier, (chartAt ℂ x).target = (chartAt ℂ (s26d_b_F f x)).target :=
    fun _ => rfl
  have hs : ∀ x : (s26d_b_X f).carrier,
      (chartAt ℂ x).source = s26d_b_F f ⁻¹' (chartAt ℂ (s26d_b_F f x)).source := fun _ => rfl
  exact ⟨s26d_b_X f, s26d_b_e f, fun x => q' (s26d_b_F f x), s26d_b_F f,
    ⟨hf.initial, hf.initial_ne, hf.k_nonneg, hf.k_lt_one, s26d_b_terminal (s26d_b_F f) hF hFs ht hs hf.terminal,
      hf.regular, fun p m hm => ⟨hf.zero p m hm, s26d_b_zero_local hf p m hm⟩⟩,
    s26d_b_biholomorphic (s26d_b_F f) hF hFs, fun p => rfl⟩

/-! ## §26.4 The uniqueness theorem -/

/-- A closed path (loop) on `S` with base point `p`. -/
abbrev Loop (S : Type u) [TopologicalSpace S] := Σ p : S, Path p p

/-- A horizontal trajectory arc of `q` on a Riemann surface: a path whose chart images (in the
chart at any of its points) are horizontal trajectory arcs of the local coefficient. -/
def IsHorizontalArcRS (q : S₀ → ℂ → ℂ) {a b : S₀} (γ : Path a b) : Prop :=
  ∀ t₀ : ℝ, t₀ ∈ Icc (0 : ℝ) 1 → ∃ δ > 0, ∃ x : S₀,
    γ.extend '' Ioo (t₀ - δ) (t₀ + δ) ⊆ (chartAt ℂ x).source ∧
      IsHorizontalArc (q x) (fun t => chartAt ℂ x (γ.extend t)) (max 0 (t₀ - δ)) (min 1 (t₀ + δ))

/-- The `q`-length of a path up to reparametrization: the infimum of `phiLengthPath` over the monotone
continuous reparametrizations `σ` of `[0, 1]` (`σ 0 = 0`, `σ 1 = 1`).  `phiLengthPath` only admits Lipschitz
chart pieces, so it depends on the parametrization; this is the true `φ`-length: for a rectifiable path
the arc-length parametrization is Lipschitz and attains it, and all Lipschitz parametrizations agree. -/
def phiLengthPathInv {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) {a b : S}
    (γ : Path a b) : ℝ≥0∞ :=
  ⨅ (σ : unitInterval → unitInterval) (hσ : Continuous σ) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (_ : Monotone σ),
    phiLengthPath q (γ.reparam σ hσ h0 h1)

/-- **Lemma 26.1** (26.8).  Let `S₀` be a closed Riemann surface, `f : S₀ → S₀` a homeomorphism
homotopic to the identity, `q ∈ Q(S₀)` not identically zero.  Then there is `M > 0` such that every
horizontal trajectory arc `α` of finite `q`-length satisfies `l_q(f(α)) ≥ l_q(α) - 2M`.

**Correction.**  The hypothesis `phiLengthPath q α < ⊤` was missing, and the statement was **false**:
`phiLengthPath` counts only Lipschitz chart pieces, so it depends on the parametrization; an arc
parametrized like `p + L√t` has length `⊤`, while a quasiconformal `f` homotopic to the identity (a
radial squaring) straightens it, so `l_q(f(α)) < ⊤` and `⊤ ≤ l_q(f(α)) + 2M` fails.

**Correction (2026-09-26).**  The image `f(α)` is measured by the true length `phiLengthPathInv` (the infimum
over reparametrizations) instead of `phiLengthPath`: a quasiconformal image is generally not Lipschitz
parametrized, so `phiLengthPath q (f ∘ α) = ⊤` on exactly the arcs of the averaging argument, and the
statement said nothing there.  The new statement is stronger (`phiLengthPathInv ≤ phiLengthPath`). -/
theorem lemma26_1 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    (f : S₀ ≃ₜ S₀) (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (a b : S₀) (α : Path a b), IsHorizontalArcRS q α → phiLengthPath q α < ⊤ →
      phiLengthPath q α ≤ phiLengthPathInv q (α.map f.continuous) + ENNReal.ofReal (2 * M) := by
  sorry

/-- §26.4 (the proof of Lemma 26.1): for `F` a homotopy from the identity to `f`, `β_p` the track
`t ↦ F(p, t)` and `β̄_p` the shortest curve in `[β_p]` (Theorem 25.4), `p ↦ l_q(β̄_p)` is continuous,
hence bounded on the compact surface.

**Correction (2026-09-26).**  The first conjunct stated the continuity of the plain `φ`-distance
`phiDistRS q p (f p)`; the book's proof needs (and this docstring states) the continuity of the length
`l_q(β̄_p)` of the shortest curve in the homotopy class of the track, which it now states. -/
theorem lemma26_1_track_length_continuous [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] (f : S₀ ≃ₜ S₀) (F : ContinuousMap.Homotopy (ContinuousMap.id S₀) (f : C(S₀, S₀)))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    Continuous (fun p : S₀ => ⨅ (γ' : Path p (f p))
      (_ : γ'.Homotopic ⟨⟨fun t => F (t, p), by fun_prop⟩, by simp, by simp⟩), phiLengthPath q γ') ∧
      ∀ p : S₀, ∃ γ : Path p (f p),
        γ.Homotopic ⟨⟨fun t => F (t, p), by fun_prop⟩, by simp, by simp⟩ ∧
          phiLengthPath q γ = ⨅ (γ' : Path p (f p))
            (_ : γ'.Homotopic ⟨⟨fun t => F (t, p), by fun_prop⟩, by simp, by simp⟩), phiLengthPath q γ' := by
  sorry

/-- The stretching function `λ_f` (§26.4) of a map `g` between plane domains carrying the
quadratic differentials `φ dz²` (source) and `φ' dw²` (target): in natural parameters
`λ = |∂_ξ g̃| = |∂_ζ g̃ + ∂_ζ̄ g̃|`, which in the parameters `z`, `w` reads
`λ = |φ'(g(z))|^{1/2} |∂_z g + ∂_z̄ g · φ/|φ|| / |φ(z)|^{1/2}` (cf. (35.4)). -/
def lambdaStretchPlane (φ φ' g : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.sqrt ‖φ' (g z)‖ * ‖dz g z + dzbar g z * (φ z / ‖φ z‖)‖ / Real.sqrt ‖φ z‖

/-- The local expression of `f` near `z = φ_x(p)`, read in the chart at the image point `f p`,
`p = (chartAt ℂ x).symm z` (it agrees with `localMapExpr f x` near `z` when `f p` lies in the chart at
`f x`, up to the holomorphic transition). -/
def localMapExprAt (f : S₀ → S₁) (x : S₀) (z : ℂ) : ℂ → ℂ :=
  fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))

/-- §26.4: `λ_f(p)`, the limit of `l_q'(f(α))/l_q(α)` over horizontal arcs `α` through `p` of
`q`-length tending to `0`, at `p = (chartAt ℂ x).symm z`: read in the chart at `x` on the source side
and in the chart at the image point `f p` on the target side.

**Correction.**  `λ` was read in the chart at `f x` on the target side, which need not contain `f p`;
under the infimum over chart partitions in `surfaceIntegral`, pieces whose image leaves the chart at
`f x` then contributed junk values, and Lemma 26.2 and (26.14) were **false** as stated. -/
def lambdaStretch (q : S₀ → ℂ → ℂ) (q' : S₁ → ℂ → ℂ) (f : S₀ → S₁) (x : S₀) (z : ℂ) : ℝ :=
  lambdaStretchPlane (q x) (q' (f ((chartAt ℂ x).symm z))) (localMapExprAt f x z) z

/-- The Jacobian `J_f = |∂_ξ f̃|² - |∂_ξ̄ f̃|²` of `f` with respect to the metrics of `q` and `q'`, at
`p = (chartAt ℂ x).symm z`, in the chart at `x` and the chart at the image point `f p` (**Correction**
as for `lambdaStretch`: it was read in the chart at `f x`). -/
def jacobianQD (q : S₀ → ℂ → ℂ) (q' : S₁ → ℂ → ℂ) (f : S₀ → S₁) (x : S₀) (z : ℂ) : ℝ :=
  ‖q' (f ((chartAt ℂ x).symm z)) (localMapExprAt f x z z)‖ * jacobian (localMapExprAt f x z) z / ‖q x z‖

/-! ### Helpers for `eq26_9` (`s26n_`): (26.9), length of the image of a horizontal arc -/

/-- Chart invariance of the `q`-density times the speed of a curve `c` at a time `u`, for two charts at
`y` and `y'` whose sources contain `c u`: the transition is holomorphic with a holomorphic local inverse,
and the transformation law of `q` absorbs its derivative (both sides vanish where neither chart
expression of `c` is differentiable). -/
theorem s26n_density_speed_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (y y' : S₀) {c : ℝ → S₀} {u : ℝ} (hc : ContinuousAt c u) (hy : c u ∈ (chartAt ℂ y).source)
    (hy' : c u ∈ (chartAt ℂ y').source) :
    phiDensity (q y) (chartAt ℂ y (c u)) * ‖deriv (fun v => chartAt ℂ y (c v)) u‖ₑ =
      phiDensity (q y') (chartAt ℂ y' (c u)) * ‖deriv (fun v => chartAt ℂ y' (c v)) u‖ₑ := by
  have hw : chartAt ℂ y (c u) ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hws : (chartAt ℂ y).symm (chartAt ℂ y (c u)) = c u := (chartAt ℂ y).left_inv hy
  have hw' : chartAt ℂ y' (c u) ∈ (chartAt ℂ y').target := (chartAt ℂ y').map_source hy'
  have hws' : (chartAt ℂ y').symm (chartAt ℂ y' (c u)) = c u := (chartAt ℂ y').left_inv hy'
  obtain ⟨hT, -⟩ := s23_transition y' y hw (by rw [hws]; exact hy')
  obtain ⟨hS, -⟩ := s23_transition y y' hw' (by rw [hws']; exact hy)
  have hlaw := s26u_law hq y y' hw (by rw [hws]; exact hy')
  have hTw : chartTransition y' y (chartAt ℂ y (c u)) = chartAt ℂ y' (c u) := by
    show chartAt ℂ y' ((chartAt ℂ y).symm (chartAt ℂ y (c u))) = chartAt ℂ y' (c u)
    rw [hws]
  have hev : (fun v => chartAt ℂ y' (c v)) =ᶠ[𝓝 u]
      chartTransition y' y ∘ fun v => chartAt ℂ y (c v) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hy)] with v hv
    show chartAt ℂ y' (c v) = chartAt ℂ y' ((chartAt ℂ y).symm (chartAt ℂ y (c v)))
    rw [(chartAt ℂ y).left_inv hv]
  have hev' : (fun v => chartAt ℂ y (c v)) =ᶠ[𝓝 u]
      chartTransition y y' ∘ fun v => chartAt ℂ y' (c v) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ y').open_source.mem_nhds hy')] with v hv
    show chartAt ℂ y (c v) = chartAt ℂ y ((chartAt ℂ y').symm (chartAt ℂ y' (c v)))
    rw [(chartAt ℂ y').left_inv hv]
  by_cases hd : DifferentiableAt ℝ (fun v => chartAt ℂ y (c v)) u
  · have hder : deriv (fun v => chartAt ℂ y' (c v)) u =
        deriv (chartTransition y' y) (chartAt ℂ y (c u)) * deriv (fun v => chartAt ℂ y (c v)) u := by
      rw [hev.deriv_eq]
      exact (hT.hasDerivAt.comp u hd.hasDerivAt).deriv
    simp only [phiDensity]
    rw [hder, hlaw, hTw, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), enorm_mul, ofReal_norm, mul_assoc]
  · have hd' : ¬ DifferentiableAt ℝ (fun v => chartAt ℂ y' (c v)) u := by
      intro hg
      exact hd ((hS.hasDerivAt.comp u hg.hasDerivAt).differentiableAt.congr_of_eventuallyEq hev')
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
    simp

/-- For a monotone subdivision `τ`, the integral over `(τ 0, τ n)` is at most the sum of the integrals over
the pieces `(τ i, τ (i + 1))`. -/
theorem s26n_lintegral_le_sum (G : ℝ → ℝ≥0∞) :
    ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ), Monotone τ →
      ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)), G u ≤
        ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ), G u := by
  intro n
  induction n with
  | zero => intro τ _; simp
  | succ n ih =>
    intro τ hτ
    have hτ' : Monotone fun i : Fin (n + 1) => τ i.castSucc := fun i j hij =>
      hτ (Fin.castSucc_le_castSucc_iff.2 hij)
    have h1 := ih (fun i => τ i.castSucc) hτ'
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at h1
    rw [Fin.sum_univ_castSucc, Fin.succ_last]
    have hsub : Ioo (τ 0) (τ (Fin.last (n + 1))) ⊆
        Ioo (τ 0) (τ (Fin.last n).castSucc) ∪ Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))) := by
      intro u hu
      rcases lt_or_ge u (τ (Fin.last n).castSucc) with h | h
      · exact Or.inl ⟨hu.1, h⟩
      · exact Or.inr ⟨h, hu.2.le⟩
    calc ∫⁻ u in Ioo (τ 0) (τ (Fin.last (n + 1))), G u
        ≤ ∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc) ∪
            Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := lintegral_mono_set hsub
      _ ≤ (∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc), G u) +
            ∫⁻ u in Icc (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := lintegral_union_le _ _ _
      _ = (∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc), G u) +
            ∫⁻ u in Ioo (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := by
          congr 1
          exact (setLIntegral_congr Ioo_ae_eq_Icc).symm
      _ ≤ _ := add_le_add_left h1 _

/-- On a horizontal direction (`Q w² > 0`) the conjugate direction is `w̄ = w · Q/|Q|`. -/
theorem s26n_conj_eq {Q w : ℂ} (hw : w ≠ 0) (him : (Q * w ^ 2).im = 0) (hre : 0 < (Q * w ^ 2).re) :
    conj w = w * (Q / (‖Q‖ : ℂ)) := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hre
  have hQn : (‖Q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hQ
  have h1 : Q * w ^ 2 = (((Q * w ^ 2).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have h2 : ‖Q‖ * ‖w‖ ^ 2 = (Q * w ^ 2).re := by
    have := congrArg norm h1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre] at this
    exact this
  have h3 : (‖Q‖ : ℂ) * (w * conj w) = Q * w ^ 2 := by
    rw [Complex.mul_conj', h1, ← h2]
    push_cast
    ring
  rw [← mul_div_assoc, eq_div_iff hQn]
  apply mul_left_cancel₀ hw
  linear_combination h3

/-- In the chart at `x`, a horizontal arc is differentiable at every interior time, with nonzero derivative
`z'` and `q_x(z) z'² > 0` (transferred from the chart in which it is horizontal by the transformation
law). -/
theorem s26n_horizontal_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S₀}
    {α : Path a b} (hα : IsHorizontalArcRS q α) (x : S₀) (hx : range α ⊆ (chartAt ℂ x).source) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ∃ z' : ℂ, HasDerivAt (fun v => chartAt ℂ x (α.extend v)) z' u ∧ z' ≠ 0 ∧
      (q x (chartAt ℂ x (α.extend u)) * z' ^ 2).im = 0 ∧
        0 < (q x (chartAt ℂ x (α.extend u)) * z' ^ 2).re := by
  have hαx : ∀ t, α.extend t ∈ (chartAt ℂ x).source := fun t =>
    hx (by rw [← Path.extend_range]; exact mem_range_self t)
  obtain ⟨δ, hδ, x', hsub, hh⟩ := hα u (Ioo_subset_Icc_self hu)
  have hu' : u ∈ Ioo (max 0 (u - δ)) (min 1 (u + δ)) :=
    ⟨max_lt hu.1 (by linarith), lt_min hu.2 (by linarith)⟩
  obtain ⟨hcd, hc0, -, him, hre⟩ := hh u hu'
  have hux : α.extend u ∈ (chartAt ℂ x').source := hsub ⟨u, ⟨by linarith, by linarith⟩, rfl⟩
  have hcu : chartAt ℂ x' (α.extend u) ∈ (chartAt ℂ x').target := (chartAt ℂ x').map_source hux
  have hcs : (chartAt ℂ x').symm (chartAt ℂ x' (α.extend u)) = α.extend u := (chartAt ℂ x').left_inv hux
  obtain ⟨hT, hT0⟩ := s23_transition x x' hcu (by rw [hcs]; exact hαx u)
  have hlaw := s26u_law hq x' x hcu (by rw [hcs]; exact hαx u)
  have hTc : chartTransition x x' (chartAt ℂ x' (α.extend u)) = chartAt ℂ x (α.extend u) := by
    show chartAt ℂ x ((chartAt ℂ x').symm (chartAt ℂ x' (α.extend u))) = _
    rw [hcs]
  rw [hTc] at hlaw
  have hev : (fun v => chartAt ℂ x (α.extend v)) =ᶠ[𝓝 u]
      chartTransition x x' ∘ fun v => chartAt ℂ x' (α.extend v) := by
    filter_upwards [Ioo_mem_nhds (show u - δ < u by linarith) (show u < u + δ by linarith)] with v hv
    show chartAt ℂ x (α.extend v) = chartAt ℂ x ((chartAt ℂ x').symm (chartAt ℂ x' (α.extend v)))
    rw [(chartAt ℂ x').left_inv (hsub ⟨v, hv, rfl⟩)]
  have hD := (hT.hasDerivAt.comp u hcd.hasDerivAt).congr_of_eventuallyEq hev
  have key : q x (chartAt ℂ x (α.extend u)) *
      (deriv (chartTransition x x') (chartAt ℂ x' (α.extend u)) *
        deriv (fun t => chartAt ℂ x' (α.extend t)) u) ^ 2 =
      q x' (chartAt ℂ x' (α.extend u)) * deriv (fun t => chartAt ℂ x' (α.extend t)) u ^ 2 := by
    rw [hlaw]
    ring
  refine ⟨_, hD, mul_ne_zero hT0 hc0, ?_, ?_⟩
  · rw [key]
    exact him
  · rw [key]
    exact hre


/-- The pointwise identity behind (26.9) at an interior time `u` of the horizontal arc `α` at which the local
expression of `f` is differentiable: `|q_{f x}|^{1/2} |(f ∘ α)'| = λ_f |q_x|^{1/2} |α'|`, with `λ_f` read in the
chart at `x` and the chart at the image point `f p`. -/
theorem s26n_pointwise [IsManifold 𝓘(ℂ) ω S₀] (f : S₀ ≃ₜ S₀) {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {a b : S₀} {α : Path a b} (hα : IsHorizontalArcRS q α) (x : S₀) (hx : range α ⊆ (chartAt ℂ x).source)
    (hfx : f '' range α ⊆ (chartAt ℂ (f x)).source) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ (localMapExpr f x) (chartAt ℂ x (α.extend u))) :
    phiDensity (q (f x)) (chartAt ℂ (f x) (f (α.extend u))) *
        ‖deriv (fun v => chartAt ℂ (f x) (f (α.extend v))) u‖ₑ =
      ENNReal.ofReal (lambdaStretch q q f x (chartAt ℂ x (α.extend u))) *
        phiDensity (q x) (chartAt ℂ x (α.extend u)) *
          ‖deriv (fun s : ℝ => chartAt ℂ x (α.extend s)) u‖ₑ := by
  have hαx : ∀ t, α.extend t ∈ (chartAt ℂ x).source := fun t =>
    hx (by rw [← Path.extend_range]; exact mem_range_self t)
  obtain ⟨z', hz', hz'0, him, hre⟩ := s26n_horizontal_chart hq hα x hx hu
  have hconj := s26n_conj_eq hz'0 him hre
  have hg : (fun v => chartAt ℂ (f x) (f (α.extend v))) =
      localMapExpr f x ∘ fun v => chartAt ℂ x (α.extend v) := by
    funext v
    simp only [Function.comp, localMapExpr, (chartAt ℂ x).left_inv (hαx v)]
  have hgd : deriv (fun v => chartAt ℂ (f x) (f (α.extend v))) u =
      z' * (dz (localMapExpr f x) (chartAt ℂ x (α.extend u)) +
        dzbar (localMapExpr f x) (chartAt ℂ x (α.extend u)) *
          (q x (chartAt ℂ x (α.extend u)) / ‖q x (chartAt ℂ x (α.extend u))‖)) := by
    rw [hg, (hd.hasFDerivAt.comp_hasDerivAt u hz').deriv, fderiv_eq_dz_dzbar hd, hconj]
    ring
  rw [hgd, hz'.deriv]
  set p := α.extend u with hp
  set z := chartAt ℂ x p with hz
  set Q := q x z with hQ
  set L := localMapExpr f x with hL
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hre
    simp at hre
  have hpx : p ∈ (chartAt ℂ x).source := hαx u
  have hzt : z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
  have hzs : (chartAt ℂ x).symm z = p := (chartAt ℂ x).left_inv hpx
  have hfp : f p ∈ (chartAt ℂ (f x)).source :=
    hfx ⟨p, by rw [hp, ← Path.extend_range]; exact mem_range_self u, rfl⟩
  have hLz : L z = chartAt ℂ (f x) (f p) := by simp only [hL, localMapExpr, hzs]
  have hLzt : L z ∈ (chartAt ℂ (f x)).target := hLz ▸ (chartAt ℂ (f x)).map_source hfp
  have hLzs : (chartAt ℂ (f x)).symm (L z) = f p := by rw [hLz]; exact (chartAt ℂ (f x)).left_inv hfp
  have hsrc : (chartAt ℂ (f x)).symm (L z) ∈ (chartAt ℂ (f p)).source := by
    rw [hLzs]; exact mem_chart_source ℂ (f p)
  obtain ⟨hT, -⟩ := s23_transition (f p) (f x) hLzt hsrc
  have hlaw := s26u_law hq (f x) (f p) hLzt hsrc
  have hTL : chartTransition (f p) (f x) (L z) = chartAt ℂ (f p) (f p) := by
    simp only [chartTransition, hLzs]
  have hM : localMapExprAt f x z =ᶠ[𝓝 z] chartTransition (f p) (f x) ∘ L := by
    have hcont : ContinuousAt (fun w => f ((chartAt ℂ x).symm w)) z :=
      f.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hzt)
    have hmem : (chartAt ℂ (f x)).source ∈ 𝓝 (f ((chartAt ℂ x).symm z)) := by
      rw [hzs]; exact (chartAt ℂ (f x)).open_source.mem_nhds hfp
    filter_upwards [hcont.preimage_mem_nhds hmem] with w hw
    simp only [localMapExprAt, Function.comp, chartTransition, hL, localMapExpr, hzs]
    rw [(chartAt ℂ (f x)).left_inv hw]
  obtain ⟨hdzM, hdzbarM⟩ := eq6_5 hd hT
  have e1 : dz (localMapExprAt f x z) z = deriv (chartTransition (f p) (f x)) (L z) * dz L z := by
    rw [← hdzM]; simp only [dz, hM.fderiv_eq]
  have e2 : dzbar (localMapExprAt f x z) z = deriv (chartTransition (f p) (f x)) (L z) * dzbar L z := by
    rw [← hdzbarM]; simp only [dzbar, hM.fderiv_eq]
  have hMz : localMapExprAt f x z z = chartAt ℂ (f p) (f p) := by simp only [localMapExprAt, hzs]
  have hlam : lambdaStretch q q f x z = Real.sqrt ‖q (f p) (chartAt ℂ (f p) (f p))‖ *
      ‖deriv (chartTransition (f p) (f x)) (L z)‖ * ‖dz L z + dzbar L z * (Q / ‖Q‖)‖ / Real.sqrt ‖Q‖ := by
    simp only [lambdaStretch, lambdaStretchPlane, hMz, e1, e2, hzs, ← hQ]
    have hfac : deriv (chartTransition (f p) (f x)) (L z) * dz L z +
        deriv (chartTransition (f p) (f x)) (L z) * dzbar L z * (Q / ‖Q‖) =
        deriv (chartTransition (f p) (f x)) (L z) * (dz L z + dzbar L z * (Q / ‖Q‖)) := by ring
    rw [hfac, norm_mul, mul_assoc (Real.sqrt _)]
  rw [hlam, ← hLz]
  simp only [phiDensity]
  rw [hlaw, hTL, ← hQ]
  have hsQ : 0 < Real.sqrt ‖Q‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hQ0)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_mul, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- (26.9): if `f̃` is Lipschitz on the horizontal trajectory arc `α` and differentiable at almost every
point of it, and `f(α)` lies in the chart at `f x`, then `l_q(f(α)) = ∫_α λ_f ds_q`; for a quasiconformal
`f` this holds for almost all horizontal arcs (A.C.L.).

**Correction.**  The hypotheses were only absolute continuity along `α`, and the statement was **false**:
`λ` is built from the full derivative of the local expression, which a quasiconformal map may lack at
every point of the arc (`f z = z + i max(Im z, 0)` is `2`-quasiconformal on `ℂ`; for `q = dz²` and the
unit segment the left side is `≥ 1` and the right side is `0`); moreover `phiLengthOn` only admits
Lipschitz pieces.  Now: Lipschitz (`hlip`), a.e. differentiability (`hdiff`), and `hfx`. -/
theorem eq26_9 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] (f : S₀ ≃ₜ S₀) (hf : IsQCRS f)
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {a b : S₀} (α : Path a b)
    (hα : IsHorizontalArcRS q α) (x : S₀) (hx : range α ⊆ (chartAt ℂ x).source)
    (hfx : f '' range α ⊆ (chartAt ℂ (f x)).source)
    (hlip : ∃ K : ℝ≥0, LipschitzOnWith K
      (fun t : ℝ => localMapExpr f x (chartAt ℂ x (α.extend t))) (Icc 0 1))
    (hdiff : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      DifferentiableAt ℝ (localMapExpr f x) (chartAt ℂ x (α.extend t))) :
    phiLengthPath q (α.map f.continuous) =
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (lambdaStretch q q f x (chartAt ℂ x (α.extend t))) *
        phiDensity (q x) (chartAt ℂ x (α.extend t)) *
          ‖deriv (fun s : ℝ => chartAt ℂ x (α.extend s)) t‖ₑ := by
  have _ := hf
  have _ := hne
  have hαx : ∀ t, α.extend t ∈ (chartAt ℂ x).source := fun t =>
    hx (by rw [← Path.extend_range]; exact mem_range_self t)
  have hγ : ∀ t, (α.map f.continuous).extend t ∈ (chartAt ℂ (f x)).source := fun t =>
    hfx ⟨α.extend t, by rw [← Path.extend_range]; exact mem_range_self t, rfl⟩
  have hlen : phiLengthPath q (α.map f.continuous) = ∫⁻ u in Ioo (0 : ℝ) 1,
      phiDensity (q (f x)) (chartAt ℂ (f x) ((α.map f.continuous).extend u)) *
        ‖deriv (fun v : ℝ => chartAt ℂ (f x) ((α.map f.continuous).extend v)) u‖ₑ := by
    unfold phiLengthPath phiLengthOn
    apply le_antisymm
    · -- the one-piece partition in the chart at `f x`
      obtain ⟨K, hK⟩ := hlip
      have hK' : LipschitzOnWith K (fun v : ℝ => chartAt ℂ (f x) ((α.map f.continuous).extend v))
          (Icc 0 1) := by
        have e : (fun v : ℝ => chartAt ℂ (f x) ((α.map f.continuous).extend v)) =
            fun t : ℝ => localMapExpr f x (chartAt ℂ x (α.extend t)) := by
          funext t
          simp only [localMapExpr, (chartAt ℂ x).left_inv (hαx t)]
          rfl
        rw [e]
        exact hK
      refine iInf_le_of_le 1 (iInf_le_of_le ![0, 1] (iInf_le_of_le (fun _ => f x)
        (iInf_le_of_le ⟨rfl, rfl, ?_, fun i => ?_⟩ ?_)))
      · rw [Fin.monotone_iff_le_succ]
        intro i
        fin_cases i
        simp
      · fin_cases i
        refine ⟨?_, K, ?_⟩
        · rintro _ ⟨t, -, rfl⟩
          exact hγ t
        · simpa using hK'
      · simp
    · refine le_iInf fun n => le_iInf fun τ => le_iInf fun y => le_iInf fun hP => ?_
      obtain ⟨h0, h1, hmono, hpc⟩ := hP
      calc ∫⁻ u in Ioo (0 : ℝ) 1,
            phiDensity (q (f x)) (chartAt ℂ (f x) ((α.map f.continuous).extend u)) *
              ‖deriv (fun v : ℝ => chartAt ℂ (f x) ((α.map f.continuous).extend v)) u‖ₑ
          ≤ ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
            phiDensity (q (f x)) (chartAt ℂ (f x) ((α.map f.continuous).extend u)) *
              ‖deriv (fun v : ℝ => chartAt ℂ (f x) ((α.map f.continuous).extend v)) u‖ₑ := by
            rw [← h0, ← h1]
            exact s26n_lintegral_le_sum _ n τ hmono
        _ = _ := by
            refine Finset.sum_congr rfl fun i _ => setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
            exact (s26n_density_speed_chart hq (y i) (f x)
              (α.map f.continuous).continuous_extend.continuousAt
              ((hpc i).1 ⟨u, Ioo_subset_Icc_self hu, rfl⟩) (hγ u)).symm
  rw [hlen]
  refine lintegral_congr_ae ?_
  filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with t ht htm
  exact s26n_pointwise f hq hα x hx hfx htm ht

/-- **Lemma 26.2** (26.10).  Let `S₀` be a closed Riemann surface of genus `g > 1`, `f` a
quasiconformal self-map of `S₀` homotopic to the identity, and `q ≢ 0` a holomorphic quadratic
differential.  Then `∬_{S₀} dA_q ≤ ∬_{S₀} λ_f(p) dA_q`. -/
theorem lemma26_2 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    quadDiffNorm q ≤ surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z) := by
  sorry

/-! ### Stage P8 (coordinator 553e2d): the averaging identity behind Lemma 26.2 (`s26v_`)

The interface of the proof of `lemma26_2_averaging` (scout A's plan T1–T4).  Horizontal trajectories are
unit-speed curves `c` with `q c'² = 1` (`s26v_IsTrajAt`).  A point off the critical set `s26v_E q` lies on a
bi-infinite one, chosen by `s26v_traj`; `α_p` is its arc over `[-L, L]` (`s26v_arc`).
* **T1/T2:** `s26v_E q` is null in every chart (`s26v_E_null`, from [V3] and [V4]).
* **T3:** the horizontal flow preserves `dA_q` (the pair form [V5a], the averaged form [V5b], and its a.e. consequence
  [V9c]).
* **T4:** for almost every `p`, `l_q(f(α_p)) = ∫_{-L}^{L} λ_f(α_p(t)) dt` (`s26v_length_ae`, from [V9a] and [V9b]).
* [V6]: `λ_f` is chart independent and Borel in charts; [V7]: `α_p` is a horizontal arc of `q`-length `2L`.
* Shared infrastructure: [V0] (the surface integral of a chart-independent integrand is a partition sum), [V1], [V2b],
  [V2c], [V2d] (natural-parameter flow boxes, local trajectories, uniqueness, null ranges).

Declarations tagged `[Vn, stub]` are the stubs; everything else in this block is proved. -/

/-- `c` is a **unit-speed horizontal trajectory** of `q` at the time `t`: `c` is continuous at `t` and, in the chart at
the point `c t`, its chart expression has a derivative `v` at `t` with `q v² = 1` (so `q c'² > 0`, and the `q`-speed
`|q|^{1/2} |c'|` is `1`).  Only chart values near `c t` enter (by the continuity of `c` at `t`). -/
def s26v_IsTrajAt (q : S₀ → ℂ → ℂ) (c : ℝ → S₀) (t : ℝ) : Prop :=
  ContinuousAt c t ∧ ∃ v : ℂ, HasDerivAt (fun s => chartAt ℂ (c t) (c s)) v t ∧
    q (c t) (chartAt ℂ (c t) (c t)) * v ^ 2 = 1

/-- A bi-infinite unit-speed horizontal trajectory of `q`. -/
def s26v_IsTraj (q : S₀ → ℂ → ℂ) (c : C(ℝ, S₀)) : Prop := ∀ t : ℝ, s26v_IsTrajAt q c t

/-- The **critical set**: the points through which no bi-infinite unit-speed horizontal trajectory passes (the zeros of
`q` and the points of the critical trajectories). -/
def s26v_E (q : S₀ → ℂ → ℂ) : Set S₀ := {p | ¬ ∃ c : C(ℝ, S₀), s26v_IsTraj q c ∧ c 0 = p}

/-- The trajectory through `p`: a choice of a bi-infinite unit-speed horizontal trajectory `c` with `c 0 = p` (any
choice: two of them differ at most by the reversal `t ↦ -t`, [V2c]); the constant curve at `p` for `p ∈ s26v_E q`. -/
def s26v_traj (q : S₀ → ℂ → ℂ) (p : S₀) : C(ℝ, S₀) := by
  classical
  exact if h : ∃ c : C(ℝ, S₀), s26v_IsTraj q c ∧ c 0 = p then Classical.choose h else ContinuousMap.const ℝ p

/-- The arc `t ↦ c(-L + 2Lt)` of `c` over `[-L, L]`, parametrized by `[0, 1]`. -/
def s26v_arc {X : Type*} [TopologicalSpace X] (c : C(ℝ, X)) (L : ℝ) : Path (c (-L)) (c L) where
  toFun t := c (-L + 2 * L * (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    congr 1
    ring

/-- The stretching function `λ_f(p)`, read in the chart at `p` itself (it is chart independent, [V6a]). -/
def s26v_lam (q : S₀ → ℂ → ℂ) (f : S₀ → S₀) (p : S₀) : ℝ≥0∞ :=
  ENNReal.ofReal (lambdaStretch q q f p (chartAt ℂ p p))

/-- `U` is Borel in charts: in every chart it agrees on the chart target with a Borel function. -/
def s26v_IsBorelInCharts (U : S₀ → ℝ≥0∞) : Prop :=
  ∀ x : S₀, ∃ g : ℂ → ℝ≥0∞, Measurable g ∧ ∀ z ∈ (chartAt ℂ x).target, U ((chartAt ℂ x).symm z) = g z

/-- A **critical arc** of `q`: a unit-speed horizontal trajectory on `(0, b)` converging, as `t → b`, to a zero of
`q`. -/
def s26v_IsCritArc (q : S₀ → ℂ → ℂ) (c : ℝ → S₀) (b : ℝ) : Prop :=
  0 < b ∧ (∀ t ∈ Ioo (0 : ℝ) b, s26v_IsTrajAt q c t) ∧
    ∃ z₀ : S₀, q z₀ (chartAt ℂ z₀ z₀) = 0 ∧ Tendsto c (𝓝[<] b) (𝓝 z₀)

/-- A **natural-parameter flow box**: an open set `B` on which `Z` is a continuous injective map with open image and,
at every `y ∈ B`, a natural parameter of `q`: `Z ∘ φ_y⁻¹` has a complex derivative `D ≠ 0` at `φ_y(y)` with
`D² = q_y(φ_y(y))` (so `q dz² = dZ²` on `B`, and horizontal trajectories are the lines `Im Z = const`). -/
def s26v_IsFlowBox (q : S₀ → ℂ → ℂ) (B : Set S₀) (Z : S₀ → ℂ) : Prop :=
  IsOpen B ∧ ContinuousOn Z B ∧ InjOn Z B ∧ IsOpen (Z '' B) ∧
    ∀ y ∈ B, ∃ D : ℂ, HasDerivAt (fun w => Z ((chartAt ℂ y).symm w)) D (chartAt ℂ y y) ∧ D ≠ 0 ∧
      D ^ 2 = q y (chartAt ℂ y y)

/-- A path is **good** for the length formula [V9a]: it avoids the zeros of `q`, and its chart expressions are
absolutely continuous on every subinterval whose image lies in the chart. -/
def s26v_IsGoodPath (q : S₀ → ℂ → ℂ) {a b : S₀} (γ : Path a b) : Prop :=
  (∀ s ∈ Icc (0 : ℝ) 1, q (γ.extend s) (chartAt ℂ (γ.extend s) (γ.extend s)) ≠ 0) ∧
    ∀ (x : S₀) (s t : ℝ), 0 ≤ s → s < t → t ≤ 1 → γ.extend '' Icc s t ⊆ (chartAt ℂ x).source →
      AbsolutelyContinuousOnInterval (fun v => chartAt ℂ x (γ.extend v)) s t

/-- The `q`-speed `|q|^{1/2} |γ'|` of a path at the time `u`, read in the chart at the point `γ u`. -/
def s26v_speed (q : S₀ → ℂ → ℂ) {a b : S₀} (γ : Path a b) (u : ℝ) : ℝ≥0∞ :=
  phiDensity (q (γ.extend u)) (chartAt ℂ (γ.extend u) (γ.extend u)) *
    ‖deriv (fun v => chartAt ℂ (γ.extend u) (γ.extend v)) u‖ₑ

/-! #### Proved glue: charts, time shifts and reversal of trajectories -/

/-- A unit-speed horizontal trajectory in the chart at `c t` is one in every chart whose source contains `c t`: the
chart transition is holomorphic, and `q v² = 1` is invariant by the transformation law. -/
theorem s26v_trajAt_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : ℝ → S₀}
    {t : ℝ} (hc : s26v_IsTrajAt q c t) (x : S₀) (hx : c t ∈ (chartAt ℂ x).source) :
    ∃ v : ℂ, HasDerivAt (fun s => chartAt ℂ x (c s)) v t ∧ q x (chartAt ℂ x (c t)) * v ^ 2 = 1 := by
  obtain ⟨hcont, v, hv, hqv⟩ := hc
  have hyy : c t ∈ (chartAt ℂ (c t)).source := mem_chart_source ℂ (c t)
  have hw : chartAt ℂ (c t) (c t) ∈ (chartAt ℂ (c t)).target := (chartAt ℂ (c t)).map_source hyy
  have hws : (chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c t)) = c t := (chartAt ℂ (c t)).left_inv hyy
  obtain ⟨hT, -⟩ := s23_transition x (c t) hw (by rw [hws]; exact hx)
  have hlaw := s26u_law hq (c t) x hw (by rw [hws]; exact hx)
  have hTw : chartTransition x (c t) (chartAt ℂ (c t) (c t)) = chartAt ℂ x (c t) := by
    show chartAt ℂ x ((chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c t))) = _
    rw [hws]
  have hev : (fun s => chartAt ℂ x (c s)) =ᶠ[𝓝 t]
      chartTransition x (c t) ∘ fun s => chartAt ℂ (c t) (c s) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (c t)).open_source.mem_nhds hyy)] with s hs
    show chartAt ℂ x (c s) = chartAt ℂ x ((chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c s)))
    rw [(chartAt ℂ (c t)).left_inv hs]
  refine ⟨deriv (chartTransition x (c t)) (chartAt ℂ (c t) (c t)) * v,
    (hT.hasDerivAt.comp t hv).congr_of_eventuallyEq hev, ?_⟩
  rw [← hTw]
  rw [hlaw] at hqv
  linear_combination hqv

/-- Time shifts of trajectories: `s ↦ c (s + a)` is a unit-speed horizontal trajectory at `t` if `c` is one at
`t + a`. -/
theorem s26v_trajAt_shift {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {t a : ℝ} (hc : s26v_IsTrajAt q c (t + a)) :
    s26v_IsTrajAt q (fun s => c (s + a)) t := by
  obtain ⟨hcont, v, hv, hqv⟩ := hc
  have hadd : ContinuousAt (fun s : ℝ => s + a) t := by fun_prop
  refine ⟨ContinuousAt.comp (g := c) hcont hadd, v, ?_, hqv⟩
  exact HasDerivAt.comp_add_const t a hv

/-- Reversal of trajectories: `s ↦ c (-s)` is a unit-speed horizontal trajectory at `t` if `c` is one at `-t`. -/
theorem s26v_trajAt_neg {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {t : ℝ} (hc : s26v_IsTrajAt q c (-t)) :
    s26v_IsTrajAt q (fun s => c (-s)) t := by
  obtain ⟨hcont, v, hv, hqv⟩ := hc
  have hneg : ContinuousAt (fun s : ℝ => -s) t := by fun_prop
  refine ⟨ContinuousAt.comp (g := c) hcont hneg, -v, ?_, by rw [neg_sq]; exact hqv⟩
  have h := HasDerivAt.scomp t hv (hasDerivAt_neg t)
  simpa [Function.comp_def] using h

/-- **[V2a], proved.**  In a flow box, a unit-speed horizontal trajectory runs along a horizontal line at unit
speed: `(Z ∘ c)'(t) = ±1` (the chain rule in the chart at `c t`, and `(D v)² = q v² = 1`). -/
theorem s26v_flowBox_deriv {q : S₀ → ℂ → ℂ} {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z)
    {c : ℝ → S₀} {t : ℝ} (hc : s26v_IsTrajAt q c t) (hct : c t ∈ B) :
    HasDerivAt (fun s => Z (c s)) 1 t ∨ HasDerivAt (fun s => Z (c s)) (-1) t := by
  obtain ⟨hcont, v, hv, hqv⟩ := hc
  obtain ⟨D, hD, -, hD2⟩ := hB.2.2.2.2 (c t) hct
  have hyy : c t ∈ (chartAt ℂ (c t)).source := mem_chart_source ℂ (c t)
  have hev : (fun s => Z (c s)) =ᶠ[𝓝 t]
      (fun w => Z ((chartAt ℂ (c t)).symm w)) ∘ fun s => chartAt ℂ (c t) (c s) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (c t)).open_source.mem_nhds hyy)] with s hs
    simp only [Function.comp_apply, (chartAt ℂ (c t)).left_inv hs]
  have hder : HasDerivAt (fun s => Z (c s)) (D * v) t := (hD.comp t hv).congr_of_eventuallyEq hev
  have h1 : (D * v) ^ 2 = 1 := by rw [mul_pow, hD2]; exact hqv
  rcases sq_eq_one_iff.1 h1 with h | h
  · exact Or.inl (h ▸ hder)
  · exact Or.inr (h ▸ hder)

/-- The chosen trajectory through a point off the critical set is a bi-infinite unit-speed horizontal trajectory
through that point. -/
theorem s26v_traj_spec {q : S₀ → ℂ → ℂ} {p : S₀} (hp : p ∉ s26v_E q) :
    s26v_IsTraj q (s26v_traj q p) ∧ s26v_traj q p 0 = p := by
  have h : ∃ c : C(ℝ, S₀), s26v_IsTraj q c ∧ c 0 = p := by
    by_contra h'
    exact hp h'
  unfold s26v_traj
  split_ifs
  exact Classical.choose_spec h

/-- The arc of `c` over `[-L, L]` passes through `c 0` (at the time `1/2`). -/
theorem s26v_mem_range_arc {X : Type*} [TopologicalSpace X] (c : C(ℝ, X)) (L : ℝ) :
    c 0 ∈ range (s26v_arc c L) := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
  show c (-L + 2 * L * (1 / 2 : ℝ)) = c 0
  congr 1
  ring

/-! #### Shared infrastructure stubs -/

/-! #### Prover A helpers: partition independence -/

/-- The chart image of the intersection of two pieces lying in two charts is measurable when the chart images of the
pieces are: `φ_x(P ∩ Q) = φ_x(P) ∩ τ⁻¹(φ_y(Q))` on the open domain of the continuous transition `τ = φ_y ∘ φ_x⁻¹`. -/
theorem s26v_a_measurableSet_inter {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (x y : S) {P Q : Set S}
    (hP : P ⊆ (chartAt ℂ x).source) (hQ : Q ⊆ (chartAt ℂ y).source)
    (hPm : MeasurableSet (chartAt ℂ x '' P)) (hQm : MeasurableSet (chartAt ℂ y '' Q)) :
    MeasurableSet (chartAt ℂ x '' (P ∩ Q)) := by
  classical
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  set D := φ.target ∩ φ.symm ⁻¹' ψ.source with hD
  have hDo : IsOpen D := φ.isOpen_inter_preimage_symm ψ.open_source
  have hGc : ContinuousOn (fun w => ψ (φ.symm w)) D :=
    ψ.continuousOn.comp (φ.continuousOn_symm.mono inter_subset_left) fun w hw => hw.2
  have hm : Measurable (D.piecewise (fun w => ψ (φ.symm w)) (fun _ => 0)) :=
    hGc.measurable_piecewise continuousOn_const hDo.measurableSet
  have heq : φ '' (P ∩ Q) =
      φ '' P ∩ (D ∩ (D.piecewise (fun w => ψ (φ.symm w)) (fun _ => 0)) ⁻¹' (ψ '' Q)) := by
    ext z
    constructor
    · rintro ⟨a, ⟨haP, haQ⟩, rfl⟩
      have hl : φ.symm (φ a) = a := φ.left_inv (hP haP)
      have hD' : φ a ∈ D := ⟨φ.map_source (hP haP), by rw [mem_preimage, hl]; exact hQ haQ⟩
      refine ⟨⟨a, haP, rfl⟩, hD', ?_⟩
      rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hD', hl]
      exact ⟨a, haQ, rfl⟩
    · rintro ⟨⟨a, haP, rfl⟩, hD', hb⟩
      rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hD'] at hb
      obtain ⟨b, hbQ, hb⟩ := hb
      have hl : φ.symm (φ a) = a := φ.left_inv (hP haP)
      rw [hl] at hb
      have ha' : a ∈ ψ.source := by
        have h := hD'.2
        rwa [mem_preimage, hl] at h
      have hab : b = a := ψ.injOn (hQ hbQ) ha' hb
      exact ⟨a, ⟨haP, hab ▸ hbQ⟩, rfl⟩
  rw [heq]
  exact hPm.inter (hDo.measurableSet.inter (hm hQm))

/-- **Chart change of variables for a chart-independent integrand.**  For a piece `A` lying in the charts at `x` and
`y`, with measurable chart image in the chart at `x`, the integral of `U |q|` over `A` is the same in both charts: the
transition `τ = φ_y ∘ φ_x⁻¹` is holomorphic and injective, with Jacobian `|τ'|²` and `|q_x| = |q_y ∘ τ| |τ'|²`. -/
theorem s26v_a_lintegral_chart_change [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (U : S₀ → ℝ≥0∞) (x y : S₀) {A : Set S₀} (hAx : A ⊆ (chartAt ℂ x).source) (hAy : A ⊆ (chartAt ℂ y).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ w in chartAt ℂ y '' A, U ((chartAt ℂ y).symm w) * ENNReal.ofReal ‖q y w‖ =
      ∫⁻ z in chartAt ℂ x '' A, U ((chartAt ℂ x).symm z) * ENNReal.ofReal ‖q x z‖ := by
  set τ := chartTransition y x with hτ
  set s := chartAt ℂ x '' A with hs
  have hmem : ∀ z ∈ s, z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨(chartAt ℂ x).map_source (hAx ha), ?_⟩
    rw [(chartAt ℂ x).left_inv (hAx ha)]
    exact hAy ha
  have hdiff : ∀ z ∈ s, DifferentiableAt ℂ τ z := fun z hz =>
    s23_transition_differentiableAt y x (hmem z hz).1 (hmem z hz).2
  have hinj : InjOn τ s := by
    intro z₁ hz₁ z₂ hz₂ h
    have h' : (chartAt ℂ x).symm z₁ = (chartAt ℂ x).symm z₂ :=
      (chartAt ℂ y).injOn (hmem z₁ hz₁).2 (hmem z₂ hz₂).2 h
    rw [← (chartAt ℂ x).right_inv (hmem z₁ hz₁).1, ← (chartAt ℂ x).right_inv (hmem z₂ hz₂).1, h']
  have himg : τ '' s = chartAt ℂ y '' A := by
    ext w
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      show chartAt ℂ y a = chartAt ℂ y ((chartAt ℂ x).symm (chartAt ℂ x a))
      rw [(chartAt ℂ x).left_inv (hAx ha)]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, ?_⟩
      show chartAt ℂ y ((chartAt ℂ x).symm (chartAt ℂ x a)) = chartAt ℂ y a
      rw [(chartAt ℂ x).left_inv (hAx ha)]
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm
    (fun z hz => ((hdiff z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  have hd := hdiff z hz
  have hdet : (fderiv ℝ τ z).det = ‖deriv τ z‖ ^ 2 := by
    have e := det_fderiv_eq_jacobian (hd.restrictScalars ℝ)
    rw [show (fderiv ℝ τ z).det = LinearMap.det (fderiv ℝ τ z : ℂ →ₗ[ℝ] ℂ) from rfl, e,
      jacobian, dz_eq_deriv hd, (cauchyRiemann_iff.1 hd).2, norm_zero]
    ring
  have hlaw : q x z = q y (τ z) * deriv τ z ^ 2 := s26u_law hq x y (hmem z hz).1 (hmem z hz).2
  have hsymm : (chartAt ℂ y).symm (τ z) = (chartAt ℂ x).symm z := (chartAt ℂ y).left_inv (hmem z hz).2
  rw [hdet, abs_of_nonneg (by positivity), hsymm, hlaw, norm_mul, norm_pow,
    ENNReal.ofReal_mul (norm_nonneg _)]
  ring

/-- **Partition independence.**  Two chart partitions give the same partition sum of a chart-independent integrand
(the common refinement `Pᵢ ∩ Qⱼ`, and the chart change of variables on each piece). -/
theorem s26v_a_partition_sum_eq [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (U : S₀ → ℝ≥0∞) {x : ℕ → S₀} {P : ℕ → Set S₀} (hP : IsChartPartition S₀ x P) {y : ℕ → S₀}
    {Q : ℕ → Set S₀} (hQ : IsChartPartition S₀ y Q) :
    ∑' j, ∫⁻ w in chartAt ℂ (y j) '' Q j, U ((chartAt ℂ (y j)).symm w) * ENNReal.ofReal ‖q (y j) w‖ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ := by
  obtain ⟨hPsm, hPd, hPc⟩ := hP
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  have hAm : ∀ i j, MeasurableSet (chartAt ℂ (x i) '' (P i ∩ Q j)) := fun i j =>
    s26v_a_measurableSet_inter (x i) (y j) (hPsm i).1 (hQsm j).1 (hPsm i).2 (hQsm j).2
  have hBm : ∀ i j, MeasurableSet (chartAt ℂ (y j) '' (P i ∩ Q j)) := fun i j => by
    rw [inter_comm]
    exact s26v_a_measurableSet_inter (y j) (x i) (hQsm j).1 (hPsm i).1 (hQsm j).2 (hPsm i).2
  have hsrc : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ =
      ∑' j, ∫⁻ z in chartAt ℂ (x i) '' (P i ∩ Q j),
        U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ := by
    intro i
    have hU : chartAt ℂ (x i) '' P i = ⋃ j, chartAt ℂ (x i) '' (P i ∩ Q j) := by
      rw [← image_iUnion, ← inter_iUnion, hQc, inter_univ]
    rw [hU, lintegral_iUnion (hAm i)]
    intro j j' hjj'
    exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hQd hjj'))
      (chartAt ℂ (x i)).injOn (inter_subset_left.trans (hPsm i).1) (inter_subset_left.trans (hPsm i).1)
  have htgt : ∀ j, ∫⁻ w in chartAt ℂ (y j) '' Q j, U ((chartAt ℂ (y j)).symm w) * ENNReal.ofReal ‖q (y j) w‖ =
      ∑' i, ∫⁻ w in chartAt ℂ (y j) '' (P i ∩ Q j),
        U ((chartAt ℂ (y j)).symm w) * ENNReal.ofReal ‖q (y j) w‖ := by
    intro j
    have hU : chartAt ℂ (y j) '' Q j = ⋃ i, chartAt ℂ (y j) '' (P i ∩ Q j) := by
      rw [← image_iUnion, ← iUnion_inter, hPc, univ_inter]
    rw [hU, lintegral_iUnion (hBm · j)]
    intro i i' hii'
    exact Disjoint.image (Disjoint.mono inter_subset_left inter_subset_left (hPd hii'))
      (chartAt ℂ (y j)).injOn (inter_subset_right.trans (hQsm j).1) (inter_subset_right.trans (hQsm j).1)
  simp only [htgt, hsrc]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => tsum_congr fun j => ?_
  exact s26v_a_lintegral_chart_change hq U (x i) (y j) (inter_subset_left.trans (hPsm i).1)
    (inter_subset_right.trans (hQsm j).1) (hAm i j)

/-- **[V0, stub]** (partition independence).  The surface integral of a chart-independent integrand `U` is its
partition sum over *any* chart partition: on a common refinement of two partitions, the pieces correspond through the
holomorphic chart transitions `τ`, with `|q_x| = |q_y ∘ τ| |τ'|²` and Jacobian `|τ'|²`. -/
theorem s26v_surfaceIntegral_eq_tsum [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (U : S₀ → ℝ≥0∞) {x : ℕ → S₀} {P : ℕ → Set S₀} (hP : IsChartPartition S₀ x P) :
    surfaceIntegral q (fun y z => U ((chartAt ℂ y).symm z)) =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ := by
  unfold surfaceIntegral
  refine le_antisymm (iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP le_rfl))) ?_
  exact le_iInf fun y => le_iInf fun Q => le_iInf fun hQ => le_of_eq (s26v_a_partition_sum_eq hq U hP hQ).symm

/-- **[V1, stub]** (flow boxes).  Every regular point of `q` has arbitrarily small natural-parameter flow boxes
(`eq25_2_natural_parameter` composed with the chart, restricted to a disc where it is injective). -/
theorem s26v_exists_flowBox [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {p : S₀}
    (hp : q p (chartAt ℂ p p) ≠ 0) {W : Set S₀} (hW : W ∈ 𝓝 p) :
    ∃ (B : Set S₀) (Z : S₀ → ℂ), p ∈ B ∧ B ⊆ W ∧ s26v_IsFlowBox q B Z := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set e := chartAt ℂ p with he
  have hpe : p ∈ e.source := mem_chart_source ℂ p
  have hz₀ : e p ∈ e.target := e.map_source hpe
  have han : AnalyticAt ℂ (q p) (e p) := (hq'.2 p).analyticAt (e.open_target.mem_nhds hz₀)
  obtain ⟨ζ, hζan, -, hζd, hζsq⟩ := eq25_2_natural_parameter han hp
  obtain ⟨V, hVo, hzV, -, hVinj⟩ := s26u_exists_open_injOn hζan hζd
  have hqc : ContinuousAt (q p) (e p) := han.continuousAt
  have hWe : e.symm ⁻¹' W ∈ 𝓝 (e p) := by
    have h := (e.continuousAt_symm hz₀).preimage_mem_nhds (by rw [e.left_inv hpe]; exact hW)
    exact h
  have hgood : {z | AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = q p z ∧ q p z ≠ 0 ∧ z ∈ V ∧ z ∈ e.target ∧
      e.symm z ∈ W} ∈ 𝓝 (e p) := by
    filter_upwards [hζan.eventually_analyticAt, hζsq, hqc.eventually_ne hp, hVo.mem_nhds hzV,
      e.open_target.mem_nhds hz₀, hWe] with z h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨O, hOsub, hOo, hzO⟩ := _root_.mem_nhds_iff.1 hgood
  refine ⟨e.source ∩ e ⁻¹' O, fun y => ζ (e y), ⟨hpe, hzO⟩, fun y hy => ?_, ?_⟩
  · have h := (hOsub hy.2).2.2.2.2.2
    rwa [e.left_inv hy.1] at h
  refine ⟨e.isOpen_inter_preimage hOo, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have h1 : ContinuousAt ζ (e y) := (hOsub hy.2).1.continuousAt
    exact (h1.comp (e.continuousAt hy.1)).continuousWithinAt
  · intro y₁ hy₁ y₂ hy₂ h
    have h' : e y₁ = e y₂ := hVinj (hOsub hy₁.2).2.2.2.1 (hOsub hy₂.2).2.2.2.1 h
    exact e.injOn hy₁.1 hy₂.1 h'
  · have himg : (fun y => ζ (e y)) '' (e.source ∩ e ⁻¹' O) = ζ '' O := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e y, hy.2, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        have hwt : w ∈ e.target := (hOsub hw).2.2.2.2.1
        refine ⟨e.symm w, ⟨e.map_target hwt, ?_⟩, ?_⟩
        · show e (e.symm w) ∈ O
          rw [e.right_inv hwt]
          exact hw
        · show ζ (e (e.symm w)) = ζ w
          rw [e.right_inv hwt]
    rw [himg, isOpen_iff_mem_nhds]
    rintro _ ⟨w, hw, rfl⟩
    have hs : HasStrictDerivAt ζ (deriv ζ w) w := (hOsub hw).1.hasStrictDerivAt
    have hd0 : deriv ζ w ≠ 0 := by
      intro h0
      apply (hOsub hw).2.2.1
      rw [← (hOsub hw).2.1, h0]
      ring
    rw [← hs.map_nhds_eq hd0]
    exact image_mem_map (hOo.mem_nhds hw)
  · intro y hy
    have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
    have hw₀ : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hyy
    have hsy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv hyy
    have hys : (chartAt ℂ y).symm (chartAt ℂ y y) ∈ (chartAt ℂ p).source := by rw [hsy]; exact hy.1
    obtain ⟨hTd, hTd'⟩ := s23_transition p y hw₀ hys
    have hTw : chartTransition p y (chartAt ℂ y y) = e y := by
      simp only [chartTransition, hsy, he]
    obtain ⟨hζy, hsqy, hqy, -⟩ := hOsub hy.2
    have hζd' : HasDerivAt ζ (deriv ζ (e y)) (chartTransition p y (chartAt ℂ y y)) := by
      rw [hTw]
      exact hζy.differentiableAt.hasDerivAt
    refine ⟨deriv ζ (e y) * deriv (chartTransition p y) (chartAt ℂ y y), HasDerivAt.comp _ hζd' hTd.hasDerivAt,
      mul_ne_zero (fun h0 => hqy (by rw [← hsqy, h0]; ring)) hTd', ?_⟩
    rw [mul_pow, hsqy, s26u_law hq y p hw₀ hys, hTw]

/-! #### Prover A helpers: flow boxes and local trajectories -/

/-- In a flow box, `Z` read in any chart `x` has, at every point `w` of the chart target whose preimage lies in the
box, a complex derivative `D ≠ 0` with `D² = q_x(w)` (the flow-box condition at `φ_x⁻¹ w`, the holomorphic chart
transition and the transformation law). -/
theorem s26v_a_flowBox_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {B : Set S₀}
    {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z) (x : S₀) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hwB : (chartAt ℂ x).symm w ∈ B) :
    ∃ D : ℂ, HasDerivAt (fun v => Z ((chartAt ℂ x).symm v)) D w ∧ D ≠ 0 ∧ D ^ 2 = q x w := by
  set y := (chartAt ℂ x).symm w with hy
  obtain ⟨D, hD, hD0, hD2⟩ := hB.2.2.2.2 y hwB
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  obtain ⟨hTd, hTd'⟩ := s23_transition y x hw hyy
  have hev : (fun v => Z ((chartAt ℂ x).symm v)) =ᶠ[𝓝 w]
      (fun v => Z ((chartAt ℂ y).symm v)) ∘ chartTransition y x := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds
      ⟨hw, hyy⟩] with v hv
    simp only [Function.comp_apply, chartTransition, (chartAt ℂ y).left_inv hv.2]
  refine ⟨D * deriv (chartTransition y x) w, (HasDerivAt.comp w hD hTd.hasDerivAt).congr_of_eventuallyEq hev,
    mul_ne_zero hD0 hTd', ?_⟩
  rw [mul_pow, hD2, s26u_law hq x y hw hyy]
  rfl

/-- In a flow box, `Z` read in the chart at `x` is holomorphic on the open set of chart points whose preimage lies in
the box. -/
theorem s26v_a_flowBox_differentiableOn [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z) (x : S₀) :
    IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' B) ∧
      DifferentiableOn ℂ (fun v => Z ((chartAt ℂ x).symm v)) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' B) := by
  refine ⟨(chartAt ℂ x).isOpen_inter_preimage_symm hB.1, fun w hw => ?_⟩
  obtain ⟨D, hD, -, -⟩ := s26v_a_flowBox_chart hq hB x hw.1 hw.2
  exact hD.differentiableAt.differentiableWithinAt

/-- In a flow box, `Z` read in any chart has a *strict* complex derivative `D ≠ 0`, `D² = q_x`, at every point of the
box (it is holomorphic nearby). -/
theorem s26v_a_flowBox_strict [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {B : Set S₀}
    {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z) (x : S₀) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hwB : (chartAt ℂ x).symm w ∈ B) :
    ∃ D : ℂ, HasStrictDerivAt (fun v => Z ((chartAt ℂ x).symm v)) D w ∧ D ≠ 0 ∧ D ^ 2 = q x w := by
  obtain ⟨D, hD, hD0, hD2⟩ := s26v_a_flowBox_chart hq hB x hw hwB
  obtain ⟨hO, hdiff⟩ := s26v_a_flowBox_differentiableOn hq hB x
  have han : AnalyticAt ℂ (fun v => Z ((chartAt ℂ x).symm v)) w := hdiff.analyticAt (hO.mem_nhds ⟨hw, hwB⟩)
  refine ⟨D, ?_, hD0, hD2⟩
  have h := han.hasStrictDerivAt
  rwa [hD.deriv] at h

/-- **[V2b, stub]** (local trajectories).  In a flow box, the horizontal line through `y` is a unit-speed horizontal
trajectory as long as it stays in the box: `c s = (Z|_B)⁻¹ (Z y + s)` (the inverse of the holomorphic `Z ∘ φ⁻¹`,
continuous since `Z|_B` is a local homeomorphism; derivative `1/D` in the chart, and `q (1/D)² = 1`). -/
theorem s26v_flowBox_line [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {B : Set S₀}
    {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z) {y : S₀} (hy : y ∈ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ s ∈ Ioo a b, Z y + (s : ℂ) ∈ Z '' B) :
    ∃ c : ℝ → S₀, c 0 = y ∧ ∀ s ∈ Ioo a b, c s ∈ B ∧ Z (c s) = Z y + (s : ℂ) ∧ s26v_IsTrajAt q c s := by
  have _ := ha
  have _ := hb
  classical
  have : Nonempty S₀ := ⟨y⟩
  set c : ℝ → S₀ := fun s => Function.invFunOn Z B (Z y + (s : ℂ)) with hcdef
  have hcB : ∀ s ∈ Ioo a b, c s ∈ B := fun s hs => Function.invFunOn_mem (hab s hs)
  have hcZ : ∀ s ∈ Ioo a b, Z (c s) = Z y + (s : ℂ) := fun s hs => Function.invFunOn_eq (hab s hs)
  refine ⟨c, ?_, fun s hs => ⟨hcB s hs, hcZ s hs, ?_⟩⟩
  · show Function.invFunOn Z B (Z y + ((0 : ℝ) : ℂ)) = y
    rw [Complex.ofReal_zero, add_zero]
    exact hB.2.2.1.leftInvOn_invFunOn hy
  -- the trajectory property at `s`, through the local inverse of `Z` in the chart at `c s`
  set y' := c s with hy'
  set e' := chartAt ℂ y' with he'
  have hy'B : y' ∈ B := hcB s hs
  have hyy : y' ∈ e'.source := mem_chart_source ℂ y'
  have hw₀ : e' y' ∈ e'.target := e'.map_source hyy
  have hsy : e'.symm (e' y') = y' := e'.left_inv hyy
  obtain ⟨D, hDs, hD0, hD2⟩ := s26v_a_flowBox_strict hq hB y' hw₀ (by rw [hsy]; exact hy'B)
  set G : ℂ → ℂ := fun v => Z (e'.symm v) with hG
  set Ginv := hDs.localInverse G D (e' y') hD0 with hGinv
  have hGinvd : HasStrictDerivAt Ginv D⁻¹ (G (e' y')) := hDs.to_localInverse hD0
  have hright : ∀ᶠ u in 𝓝 (G (e' y')), G (Ginv u) = u := hDs.eventually_right_inverse hD0
  have hleft : ∀ᶠ w in 𝓝 (e' y'), Ginv (G w) = w := hDs.eventually_left_inverse hD0
  have hGw : G (e' y') = Z y + (s : ℂ) := by
    show Z (e'.symm (e' y')) = _
    rw [hsy]
    exact hcZ s hs
  have hGinvw : Ginv (G (e' y')) = e' y' := hleft.self_of_nhds
  have hO : e'.target ∩ e'.symm ⁻¹' B ∈ 𝓝 (e' y') :=
    (e'.isOpen_inter_preimage_symm hB.1).mem_nhds ⟨hw₀, by rw [mem_preimage, hsy]; exact hy'B⟩
  have hGinvc : Tendsto Ginv (𝓝 (G (e' y'))) (𝓝 (e' y')) := by
    have h := hGinvd.hasDerivAt.continuousAt.tendsto
    rwa [hGinvw] at h
  have hlin : Tendsto (fun r : ℝ => Z y + (r : ℂ)) (𝓝 s) (𝓝 (G (e' y'))) := by
    rw [hGw]
    exact (continuous_const.add Complex.continuous_ofReal).tendsto s
  have hev : ∀ᶠ r in 𝓝 s, c r = e'.symm (Ginv (Z y + (r : ℂ))) ∧ Ginv (Z y + (r : ℂ)) ∈ e'.target := by
    filter_upwards [isOpen_Ioo.mem_nhds hs, hlin.eventually (hGinvc.eventually hO), hlin.eventually hright]
      with r hr h1 h2
    refine ⟨hB.2.2.1 (hcB r hr) h1.2 ?_, h1.1⟩
    rw [hcZ r hr]
    exact h2.symm
  have hlc : Continuous (fun r : ℝ => Z y + (r : ℂ)) := by fun_prop
  have hcont : ContinuousAt c s := by
    have h2 : ContinuousAt Ginv (Z y + (s : ℂ)) := by
      rw [← hGw]
      exact hGinvd.hasDerivAt.continuousAt
    have h3 : ContinuousAt e'.symm (Ginv (Z y + (s : ℂ))) := by
      rw [← hGw, hGinvw]
      exact e'.continuousAt_symm hw₀
    have h1 : ContinuousAt (fun r : ℝ => e'.symm (Ginv (Z y + (r : ℂ)))) s :=
      ContinuousAt.comp (g := e'.symm) (f := fun r : ℝ => Ginv (Z y + (r : ℂ))) h3
        (ContinuousAt.comp (g := Ginv) (f := fun r : ℝ => Z y + (r : ℂ)) h2 hlc.continuousAt)
    exact h1.congr (hev.mono fun r hr => hr.1.symm)
  have hderiv : HasDerivAt (fun r => e' (c r)) D⁻¹ s := by
    have h1 : HasDerivAt (fun r : ℝ => Z y + (r : ℂ)) 1 s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_add (Z y)
    have h2 : HasDerivAt Ginv D⁻¹ (Z y + (s : ℂ)) := by
      rw [← hGw]
      exact hGinvd.hasDerivAt
    have h3 := HasDerivAt.comp s h2 h1
    rw [mul_one] at h3
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hev] with r hr
    show e' (c r) = Ginv (Z y + (r : ℂ))
    rw [hr.1]
    exact e'.right_inv hr.2
  refine ⟨hcont, D⁻¹, hderiv, ?_⟩
  show q y' (e' y') * (D⁻¹) ^ 2 = 1
  rw [← hD2, inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hD0)

/-- A unit-speed horizontal trajectory passes only through regular points of `q`. -/
theorem s26v_a_trajAt_regular {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {t : ℝ} (hc : s26v_IsTrajAt q c t) :
    q (c t) (chartAt ℂ (c t) (c t)) ≠ 0 := by
  obtain ⟨-, v, -, hv⟩ := hc
  intro h
  rw [h, zero_mul] at hv
  exact zero_ne_one hv

/-- **Local form in a flow box.**  On an open interval on which a curve is a unit-speed horizontal trajectory inside a
flow box `(B, Z)`, it runs along a horizontal line at unit speed with a constant orientation:
`Z (c s) = Z (c s₀) + σ (s - s₀)`, `σ = ±1` (`(Z ∘ c)' = ±1` ([V2a]) has the intermediate value property). -/
theorem s26v_a_line_of_box {q : S₀ → ℂ → ℂ} {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z)
    {c : ℝ → S₀} {α β : ℝ} (hc : ∀ s ∈ Ioo α β, s26v_IsTrajAt q c s ∧ c s ∈ B) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo α β) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ s ∈ Ioo α β, Z (c s) = Z (c s₀) + ((σ * (s - s₀) : ℝ) : ℂ) := by
  classical
  set d : ℝ → ℝ := fun s => if HasDerivAt (fun r => Z (c r)) 1 s then 1 else -1 with hd
  have hd1 : ∀ s, d s = 1 ∨ d s = -1 := fun s => by
    simp only [hd]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hder : ∀ s ∈ Ioo α β, HasDerivAt (fun r => Z (c r)) ((d s : ℝ) : ℂ) s := by
    intro s hs
    by_cases h1 : HasDerivAt (fun r => Z (c r)) 1 s
    · simp only [hd, h1, ↓reduceIte]
      simpa using h1
    · rcases s26v_flowBox_deriv hB (hc s hs).1 (hc s hs).2 with h | h
      · exact absurd h h1
      · simp only [hd, h1, ↓reduceIte]
        simpa using h
  have hre : ∀ s ∈ Ioo α β, HasDerivWithinAt (fun r => (Z (c r)).re) (d s) (Ioo α β) s := by
    intro s hs
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hder s hs)
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
    exact h.hasDerivWithinAt
  have hconst : ∀ s ∈ Ioo α β, d s = d s₀ := by
    intro s hs
    have hoc := (ordConnected_Ioo (a := α) (b := β)).image_hasDerivWithinAt hre
    by_contra hne
    have h0 : (0 : ℝ) ∈ d '' Ioo α β := by
      rcases hd1 s with h | h <;> rcases hd1 s₀ with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact hoc.out ⟨s₀, hs₀, h'⟩ ⟨s, hs, h⟩ ⟨by norm_num, by norm_num⟩
      · exact hoc.out ⟨s, hs, h⟩ ⟨s₀, hs₀, h'⟩ ⟨by norm_num, by norm_num⟩
      · exact absurd (h.trans h'.symm) hne
    obtain ⟨s₃, -, hs₃⟩ := h0
    rcases hd1 s₃ with h | h <;> linarith
  refine ⟨d s₀, hd1 s₀, fun s hs => ?_⟩
  set g : ℝ → ℂ := fun r => Z (c r) - ((d s₀ * (r - s₀) : ℝ) : ℂ) with hg
  have hgd : ∀ r ∈ Ioo α β, HasDerivAt g 0 r := by
    intro r hr
    have h1 : HasDerivAt (fun r : ℝ => d s₀ * (r - s₀)) (d s₀) r := by
      simpa using ((hasDerivAt_id r).sub_const s₀).const_mul (d s₀)
    have h2 := (hder r hr).sub h1.ofReal_comp
    rw [hconst r hr, sub_self] at h2
    exact h2
  have hgc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hgd r hr).differentiableAt.differentiableWithinAt) (fun r hr => (hgd r hr).deriv) hs hs₀
  simp only [hg, sub_self, mul_zero, Complex.ofReal_zero, sub_zero] at hgc
  rw [← hgc]
  ring

/-- Time shift of trajectories, in the form `s ↦ c (t + s)`. -/
theorem s26v_a_trajAt_shift_add {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {t r : ℝ} (hc : s26v_IsTrajAt q c (t + r)) :
    s26v_IsTrajAt q (fun s => c (t + s)) r := by
  have h := s26v_trajAt_shift (c := c) (t := r) (a := t) (by rwa [add_comm] at hc)
  have heq : (fun s => c (s + t)) = (fun s => c (t + s)) := funext fun s => by rw [add_comm]
  rwa [heq] at h

/-- **Two trajectories through one point, in a common flow box.**  If `c` is a unit-speed horizontal trajectory near
`t`, `c'` one near `t'`, and `c t = c' t'`, there are a flow box `(B, Z)` at this point, `ε > 0` and orientations
`σ, σ' = ±1` with `Z (c (t + r)) = Z (c t) + σ r` and `Z (c' (t' + r)) = Z (c t) + σ' r` for `|r| < ε`. -/
theorem s26v_a_two_lines [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c c' : ℝ → S₀}
    {t t' : ℝ} (hc : ∀ᶠ s in 𝓝 t, s26v_IsTrajAt q c s) (hc' : ∀ᶠ s in 𝓝 t', s26v_IsTrajAt q c' s)
    (h : c t = c' t') :
    ∃ (B : Set S₀) (Z : S₀ → ℂ) (ε σ σ' : ℝ), s26v_IsFlowBox q B Z ∧ 0 < ε ∧ (σ = 1 ∨ σ = -1) ∧
      (σ' = 1 ∨ σ' = -1) ∧ ∀ r ∈ Ioo (-ε) ε, c (t + r) ∈ B ∧ c' (t' + r) ∈ B ∧
        Z (c (t + r)) = Z (c t) + ((σ * r : ℝ) : ℂ) ∧ Z (c' (t' + r)) = Z (c t) + ((σ' * r : ℝ) : ℂ) := by
  obtain ⟨B, Z, hpB, -, hB⟩ := s26v_exists_flowBox hq (s26v_a_trajAt_regular hc.self_of_nhds)
    (univ_mem : univ ∈ 𝓝 (c t))
  have hc1 : ∀ᶠ r in 𝓝 (0 : ℝ), s26v_IsTrajAt q c (t + r) ∧ c (t + r) ∈ B := by
    have ht : Tendsto (fun r : ℝ => t + r) (𝓝 0) (𝓝 t) := by
      simpa using (continuous_const.add continuous_id).tendsto (0 : ℝ) (f := fun r : ℝ => t + r)
    have hB' : ∀ᶠ s in 𝓝 t, c s ∈ B := hc.self_of_nhds.1.preimage_mem_nhds (hB.1.mem_nhds hpB)
    exact ht.eventually (hc.and hB')
  have hc2 : ∀ᶠ r in 𝓝 (0 : ℝ), s26v_IsTrajAt q c' (t' + r) ∧ c' (t' + r) ∈ B := by
    have ht : Tendsto (fun r : ℝ => t' + r) (𝓝 0) (𝓝 t') := by
      simpa using (continuous_const.add continuous_id).tendsto (0 : ℝ) (f := fun r : ℝ => t' + r)
    have hB' : ∀ᶠ s in 𝓝 t', c' s ∈ B :=
      hc'.self_of_nhds.1.preimage_mem_nhds (hB.1.mem_nhds (by rw [← h]; exact hpB))
    exact ht.eventually (hc'.and hB')
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc1.and hc2)
  have hball' : ∀ r ∈ Ioo (-ε) ε, (s26v_IsTrajAt q c (t + r) ∧ c (t + r) ∈ B) ∧
      (s26v_IsTrajAt q c' (t' + r) ∧ c' (t' + r) ∈ B) := by
    intro r hr
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact hr
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  obtain ⟨σ, hσ, hσl⟩ := s26v_a_line_of_box hB (c := fun r => c (t + r))
    (fun r hr => ⟨s26v_a_trajAt_shift_add (hball' r hr).1.1, (hball' r hr).1.2⟩) h0
  obtain ⟨σ', hσ', hσl'⟩ := s26v_a_line_of_box hB (c := fun r => c' (t' + r))
    (fun r hr => ⟨s26v_a_trajAt_shift_add (hball' r hr).2.1, (hball' r hr).2.2⟩) h0
  refine ⟨B, Z, ε, σ, σ', hB, hε, hσ, hσ', fun r hr => ⟨(hball' r hr).1.2, (hball' r hr).2.2, ?_, ?_⟩⟩
  · have h1 := hσl r hr
    simp only [add_zero, sub_zero] at h1
    exact h1
  · have h1 := hσl' r hr
    simp only [add_zero, sub_zero] at h1
    rw [h1, h]

/-- **Local uniqueness with orientation.**  Two unit-speed horizontal trajectories through one point agree near it up
to the orientation: `c' (t' + r) = c (t + σ r)` for small `r`, `σ = ±1`. -/
theorem s26v_a_local_unique [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c c' : ℝ → S₀}
    {t t' : ℝ} (hc : ∀ᶠ s in 𝓝 t, s26v_IsTrajAt q c s) (hc' : ∀ᶠ s in 𝓝 t', s26v_IsTrajAt q c' s)
    (h : c t = c' t') : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ᶠ r in 𝓝 (0 : ℝ), c' (t' + r) = c (t + σ * r) := by
  obtain ⟨B, Z, ε, σ, σ', hB, hε, hσ, hσ', hl⟩ := s26v_a_two_lines hq hc hc' h
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habs : ∀ r : ℝ, |σ * σ' * r| = |r| := fun r => by
    rw [abs_mul, abs_mul]
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> norm_num
  refine ⟨σ * σ', by rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> norm_num, ?_⟩
  have hn : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨neg_lt_zero.2 hε, hε⟩
  filter_upwards [hn] with r hr
  have hr' : σ * σ' * r ∈ Ioo (-ε) ε := by
    have h1 : |r| < ε := abs_lt.2 hr
    rw [← habs r] at h1
    exact abs_lt.1 h1
  refine hB.2.2.1 (hl r hr).2.1 (hl _ hr').1 ?_
  rw [(hl r hr).2.2.2, (hl _ hr').2.2.1]
  congr 2
  rw [← mul_assoc, ← mul_assoc, hσσ, one_mul]

/-- **Local dichotomy.**  Two unit-speed horizontal trajectories through a point at the same time either agree near
that time, or differ at all nearby other times (they run in opposite directions). -/
theorem s26v_a_dichotomy [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c c' : ℝ → S₀}
    {t : ℝ} (hc : ∀ᶠ s in 𝓝 t, s26v_IsTrajAt q c s) (hc' : ∀ᶠ s in 𝓝 t, s26v_IsTrajAt q c' s)
    (h : c t = c' t) : c =ᶠ[𝓝 t] c' ∨ ∀ᶠ s in 𝓝[≠] t, c s ≠ c' s := by
  obtain ⟨B, Z, ε, σ, σ', hB, hε, hσ, hσ', hl⟩ := s26v_a_two_lines hq hc hc' h
  have hn : ∀ᶠ s in 𝓝 t, s - t ∈ Ioo (-ε) ε := by
    have h1 : Ioo (t - ε) (t + ε) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [h1] with s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  by_cases hσσ : σ = σ'
  · left
    filter_upwards [hn] with s hs
    have h1 := hl (s - t) hs
    rw [add_sub_cancel] at h1
    refine hB.2.2.1 h1.1 h1.2.1 ?_
    rw [h1.2.2.1, h1.2.2.2, hσσ]
  · right
    filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with s hs hst heq
    have h1 := hl (s - t) hs
    rw [add_sub_cancel] at h1
    have h2 : Z (c s) = Z (c' s) := by rw [heq]
    rw [h1.2.2.1, h1.2.2.2, add_right_inj, Complex.ofReal_inj] at h2
    have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
    have h3 : σ = σ' := mul_right_cancel₀ hst' h2
    exact hσσ h3

/-- **Uniqueness on an interval.**  Two curves that are unit-speed horizontal trajectories at every time of an open
preconnected set `J` and agree near one time of `J` agree on `J` (the set of times near which they agree is open, and
closed in `J` by the local dichotomy). -/
theorem s26v_a_eqOn_of_eventuallyEq [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) {c c' : ℝ → S₀} {J : Set ℝ} (hJo : IsOpen J) (hJ : IsPreconnected J)
    (hc : ∀ s ∈ J, s26v_IsTrajAt q c s) (hc' : ∀ s ∈ J, s26v_IsTrajAt q c' s) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h : c =ᶠ[𝓝 t₀] c') : ∀ s ∈ J, c s = c' s := by
  set u : Set ℝ := {s | c =ᶠ[𝓝 s] c'} with hu
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : J ⊆ u := by
    refine hJ.subset_of_closure_inter_subset huo ⟨t₀, ht₀, h⟩ ?_
    rintro s ⟨hscl, hsJ⟩
    have hev : ∀ᶠ r in 𝓝 s, s26v_IsTrajAt q c r := by
      filter_upwards [hJo.mem_nhds hsJ] with r hr using hc r hr
    have hev' : ∀ᶠ r in 𝓝 s, s26v_IsTrajAt q c' r := by
      filter_upwards [hJo.mem_nhds hsJ] with r hr using hc' r hr
    have hfreq : ∃ᶠ r in 𝓝 s, c r = c' r :=
      (mem_closure_iff_frequently.1 hscl).mono fun r hr => hr.eq_of_nhds
    have heq : c s = c' s := tendsto_nhds_unique_of_frequently_eq (hc s hsJ).1 (hc' s hsJ).1 hfreq
    rcases s26v_a_dichotomy hq hev hev' heq with h1 | h1
    · exact h1
    · by_contra hsu
      have hcl : s ∈ closure (u \ {s}) := by rwa [sdiff_singleton_eq_self hsu]
      have hfr := mem_closure_ne_iff_frequently_within.1 hcl
      obtain ⟨r, hr1, hr2⟩ := (hfr.and_eventually h1).exists
      exact hr2 hr1.eq_of_nhds
  exact fun s hs => (hsub hs).eq_of_nhds

/-- **[V2c, stub]** (uniqueness).  Two bi-infinite unit-speed horizontal trajectories through the same point coincide
up to the reversal `t ↦ -t`: in a flow box `(Z ∘ cᵢ)' = ±1` with a constant sign (Darboux, [V2a]) and `Z` is
injective, so they agree locally up to reversal; the agreement set is clopen in `ℝ`. -/
theorem s26v_traj_unique [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c₁ c₂ : C(ℝ, S₀)} (h₁ : s26v_IsTraj q c₁) (h₂ : s26v_IsTraj q c₂) (h0 : c₁ 0 = c₂ 0) :
    (∀ t, c₂ t = c₁ t) ∨ ∀ t, c₂ t = c₁ (-t) := by
  obtain ⟨σ, hσ, hev⟩ := s26v_a_local_unique hq (c := c₁) (c' := c₂) (t := 0) (t' := 0)
    (Eventually.of_forall h₁) (Eventually.of_forall h₂) h0
  simp only [zero_add] at hev
  rcases hσ with rfl | rfl
  · left
    have h := s26v_a_eqOn_of_eventuallyEq hq (c := c₂) (c' := c₁) isOpen_univ isPreconnected_univ
      (fun s _ => h₂ s) (fun s _ => h₁ s) (mem_univ 0) (hev.mono fun r hr => by rw [hr, one_mul])
    exact fun t => h t (mem_univ t)
  · right
    have h := s26v_a_eqOn_of_eventuallyEq hq (c := c₂) (c' := fun s => c₁ (-s)) isOpen_univ
      isPreconnected_univ (fun s _ => h₂ s) (fun s _ => s26v_trajAt_neg (h₁ (-s)))
      (mem_univ 0) (hev.mono fun r hr => by rw [hr, neg_one_mul])
    exact fun t => h t (mem_univ t)

/-- The chart image of the points of a curve at the times where it is a unit-speed horizontal trajectory is
Lebesgue-null: it is the image of a subset of the real axis (null in `ℂ`) under `z ↦ φ_x(c(Re z))`, which is
differentiable there (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). -/
theorem s26v_b_image_null [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : ℝ → S₀}
    {J : Set ℝ} (hc : ∀ t ∈ J, s26v_IsTrajAt q c t) (x : S₀) :
    volume (chartAt ℂ x '' (c '' J ∩ (chartAt ℂ x).source)) = 0 := by
  set G : ℂ → ℂ := fun z => chartAt ℂ x (c z.re) with hG
  set s : Set ℂ := {z | z.im = 0 ∧ z.re ∈ J ∧ c z.re ∈ (chartAt ℂ x).source} with hs
  have hline : volume {z : ℂ | z.im = 0} = 0 := by
    have hne : LinearMap.ker Complex.imLm ≠ ⊤ := by
      intro h
      have hI : Complex.I ∈ LinearMap.ker Complex.imLm := by
        rw [h]
        exact Submodule.mem_top
      simp [LinearMap.mem_ker] at hI
    have h := Measure.addHaar_submodule volume (LinearMap.ker Complex.imLm) hne
    convert h using 2
    ext z
    simp [LinearMap.mem_ker]
  have hs0 : volume s = 0 := measure_mono_null (fun z hz => hz.1) hline
  have hGd : DifferentiableOn ℝ G s := by
    intro z hz
    obtain ⟨v, hv, -⟩ := s26v_trajAt_chart hq (hc z.re hz.2.1) x hz.2.2
    have h1 : DifferentiableAt ℝ (fun t : ℝ => chartAt ℂ x (c t)) (Complex.reCLM z) := hv.differentiableAt
    exact (h1.comp z Complex.reCLM.differentiableAt).differentiableWithinAt
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hGd hs0)
  rintro _ ⟨p, ⟨⟨t, ht, rfl⟩, hpx⟩, rfl⟩
  exact ⟨(t : ℂ), ⟨by simp, by simpa using ht, by simpa using hpx⟩, by simp [hG]⟩

/-- **[V2d, stub]** (null ranges).  The range of a bi-infinite unit-speed horizontal trajectory is null in every
chart: its chart expressions are `C¹` curves (the image of a compact interval under a locally Lipschitz map `ℝ → ℂ`
is null), and `ℝ` is a countable union of compact intervals. -/
theorem s26v_traj_range_null [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) (x : S₀) :
    volume (chartAt ℂ x '' (range c ∩ (chartAt ℂ x).source)) = 0 := by
  have h := s26v_b_image_null hq (J := univ) (fun t _ => hc t) x
  rwa [image_univ] at h

/-! #### T1–T2: the critical set is null -/

/-! #### Prover A helpers: continuation of trajectories -/

/-- `s26v_IsTrajAt` depends only on the germ of the curve at the time considered. -/
theorem s26v_a_trajAt_congr {q : S₀ → ℂ → ℂ} {c c' : ℝ → S₀} {t : ℝ} (hc : s26v_IsTrajAt q c t)
    (h : c =ᶠ[𝓝 t] c') : s26v_IsTrajAt q c' t := by
  obtain ⟨hcont, v, hv, hqv⟩ := hc
  have ht : c t = c' t := h.eq_of_nhds
  refine ⟨hcont.congr h, v, ?_, ?_⟩
  · rw [← ht]
    refine hv.congr_of_eventuallyEq ?_
    filter_upwards [h] with s hs
    rw [hs]
  · rw [← ht]
    exact hqv

/-- On a connected surface the zeros of `q ≠ 0` are isolated: near any point, all other points are regular
(`s26u_eventually_ne_zero`, read through the chart at the point). -/
theorem s26v_a_zero_isolated [T2Space S₀] [ConnectedSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) (z : S₀) : ∀ᶠ w in 𝓝[≠] z, q w (chartAt ℂ w w) ≠ 0 := by
  set e := chartAt ℂ z with he
  have hsrc : e.source ∈ 𝓝 z := e.open_source.mem_nhds (mem_chart_source ℂ z)
  have hl : e.symm (e z) = z := e.left_inv (mem_chart_source ℂ z)
  have hw := s26u_eventually_ne_zero hq z (e.map_source (mem_chart_source ℂ z))
    (by rw [hl]; exact s26u_frequently_regular hq hne z)
  have ht : Tendsto e (𝓝[≠] z) (𝓝[≠] (e z)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((e.continuousAt (mem_chart_source ℂ z)).tendsto.mono_left nhdsWithin_le_nhds) ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hsrc] with p' hp' hne'
    exact fun heq => hne' (e.injOn hp' (mem_chart_source ℂ z) heq)
  filter_upwards [ht.eventually hw, nhdsWithin_le_nhds hsrc] with p' h1 h3
  have h4 := (s26u_isRegularPoint_iff hq z (e.map_source h3)).2 h1
  rwa [e.left_inv h3] at h4

/-- Affine reparametrizations `s ↦ c (σ (s - t))`, `σ = ±1`, of unit-speed horizontal trajectories are unit-speed
horizontal trajectories. -/
theorem s26v_a_trajAt_affine {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {σ t u : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hc : s26v_IsTrajAt q c (σ * (u - t))) : s26v_IsTrajAt q (fun s => c (σ * (s - t))) u := by
  rcases hσ with rfl | rfl
  · have h1 : s26v_IsTrajAt q c (u + -t) := by
      convert hc using 2
      ring
    have h2 := s26v_trajAt_shift (c := c) (t := u) (a := -t) h1
    have heq : (fun s => c (s + -t)) = (fun s => c (1 * (s - t))) := funext fun s => by
      congr 1
      ring
    rwa [heq] at h2
  · have h1 : s26v_IsTrajAt q c (-(u + -t)) := by
      convert hc using 2
      ring
    have h2 := s26v_trajAt_shift (c := fun s => c (-s)) (t := u) (a := -t) (s26v_trajAt_neg h1)
    have heq : (fun s => (fun s => c (-s)) (s + -t)) = (fun s => c (-1 * (s - t))) := funext fun s => by
      show c (-(s + -t)) = c (-1 * (s - t))
      congr 1
      ring
    rwa [heq] at h2

/-- **The right end of a non-extendable trajectory.**  On a compact surface, if a unit-speed horizontal trajectory `c`
on `(a, b)` cannot be continued past `b` (no trajectory on `(a, b')`, `b' > b`, agrees with it near a time of
`(a, b)`), then `c t` converges to a zero of `q` as `t → b⁻`: every cluster point is a zero (a flow box at a regular
cluster point would continue `c`, [V2b]); the zeros are isolated, and a second cluster point would force a cluster point
on the frontier of a small neighbourhood of the first one (the curve crosses it), which contains no zero. -/
theorem s26v_a_right_end [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {c : ℝ → S₀} {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Ioo a b, s26v_IsTrajAt q c t)
    (hNE : ∀ (c' : ℝ → S₀) (b' : ℝ), b < b' → (∀ t ∈ Ioo a b', s26v_IsTrajAt q c' t) →
      ∀ t₀ ∈ Ioo a b, c' =ᶠ[𝓝 t₀] c → False) :
    ∃ z₀ : S₀, q z₀ (chartAt ℂ z₀ z₀) = 0 ∧ Tendsto c (𝓝[<] b) (𝓝 z₀) := by
  classical
  -- every cluster point is a zero
  have hclu : ∀ w, MapClusterPt w (𝓝[<] b) c → q w (chartAt ℂ w w) = 0 := by
    intro w hw
    by_contra hwr
    obtain ⟨B, Z, hwB, -, hB⟩ := s26v_exists_flowBox hq hwr (univ_mem : univ ∈ 𝓝 w)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hB.2.2.2.1 (Z w) ⟨w, hwB, rfl⟩
    set δ := min (r / 4) ((b - a) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hδr : δ ≤ r / 4 := min_le_left _ _
    have hδb : δ ≤ (b - a) / 2 := min_le_right _ _
    have hN : B ∩ Z ⁻¹' ball (Z w) δ ∈ 𝓝 w :=
      inter_mem (hB.1.mem_nhds hwB)
        ((hB.2.1.continuousAt (hB.1.mem_nhds hwB)).preimage_mem_nhds (ball_mem_nhds _ hδ0))
    have hev : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo (b - δ) b := Ioo_mem_nhdsLT (by linarith)
    obtain ⟨t, ⟨htB, htZ⟩, ht⟩ := ((hw.frequently hN).and_eventually hev).exists
    have hta : t ∈ Ioo a b := ⟨by linarith [ht.1], ht.2⟩
    have hline : ∀ s ∈ Ioo (-(2 * δ)) (2 * δ), Z (c t) + (s : ℂ) ∈ Z '' B := by
      intro s hs
      refine hball ?_
      rw [mem_preimage, mem_ball, dist_eq_norm] at htZ
      rw [mem_ball, dist_eq_norm, show Z (c t) + (s : ℂ) - Z w = (Z (c t) - Z w) + (s : ℂ) by ring]
      have hs' : ‖(s : ℂ)‖ < 2 * δ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_lt.2 hs
      calc ‖(Z (c t) - Z w) + (s : ℂ)‖ ≤ ‖Z (c t) - Z w‖ + ‖(s : ℂ)‖ := norm_add_le _ _
        _ < δ + 2 * δ := add_lt_add htZ hs'
        _ ≤ r := by linarith
    obtain ⟨c₁, hc₁0, hc₁⟩ := s26v_flowBox_line hq hB htB (a := -(2 * δ)) (b := 2 * δ) (by linarith)
      (by linarith) hline
    have hct : ∀ᶠ s in 𝓝 t, s26v_IsTrajAt q c s := by
      filter_upwards [isOpen_Ioo.mem_nhds hta] with s hs using hc s hs
    have hc₁' : ∀ᶠ s in 𝓝 (0 : ℝ), s26v_IsTrajAt q c₁ s := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Ioo (-(2 * δ)) (2 * δ))]
        with s hs using (hc₁ s hs).2.2
    obtain ⟨σ, hσ, hloc⟩ := s26v_a_local_unique hq (c := c₁) (c' := c) (t := 0) (t' := t) hc₁' hct hc₁0
    set ch : ℝ → S₀ := fun u => if u ≤ t then c u else c₁ (σ * (u - t)) with hch
    have hsub : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 0) := (continuous_sub_right t).tendsto' t 0 (sub_self t)
    have heqt : c =ᶠ[𝓝 t] ch := by
      filter_upwards [hsub.eventually hloc] with u hu
      simp only [zero_add, add_sub_cancel] at hu
      by_cases hut : u ≤ t
      · simp only [hch, hut, ↓reduceIte]
      · simp only [hch, hut, ↓reduceIte]
        exact hu
    have hT : ∀ u ∈ Ioo a (t + 2 * δ), s26v_IsTrajAt q ch u := by
      intro u hu
      rcases lt_trichotomy u t with hut | rfl | hut
      · refine s26v_a_trajAt_congr (hc u ⟨hu.1, lt_trans hut hta.2⟩) ?_
        filter_upwards [isOpen_Iio.mem_nhds hut] with v hv
        simp only [hch, le_of_lt (show v < t from hv), ↓reduceIte]
      · exact s26v_a_trajAt_congr (hc u hta) heqt
      · have hmem : σ * (u - t) ∈ Ioo (-(2 * δ)) (2 * δ) := by
          rcases hσ with rfl | rfl
          · exact ⟨by linarith, by linarith [hu.2]⟩
          · exact ⟨by linarith [hu.2], by linarith⟩
        refine s26v_a_trajAt_congr (s26v_a_trajAt_affine hσ (hc₁ _ hmem).2.2) ?_
        filter_upwards [isOpen_Ioi.mem_nhds hut] with v hv
        have hv' : ¬ v ≤ t := not_le.2 hv
        simp only [hch, hv', ↓reduceIte]
    exact hNE ch (t + 2 * δ) (by linarith [ht.1]) hT t hta heqt.symm
  -- the zeros are isolated
  have hiso := s26v_a_zero_isolated hq hne
  -- a cluster point exists, and it is the only one
  obtain ⟨z₁, -, hz₁⟩ := isCompact_univ.exists_mapClusterPt (f := 𝓝[<] b) (u := c)
    (le_principal_iff.2 univ_mem)
  refine ⟨z₁, hclu z₁ hz₁, tendsto_nhds_of_unique_mapClusterPt fun z₂ hz₂ => ?_⟩
  by_contra h12
  obtain ⟨U, hU, hUreg⟩ : ∃ U ∈ 𝓝 z₁, ∀ w ∈ U, w ≠ z₁ → q w (chartAt ℂ w w) ≠ 0 :=
    ⟨_, eventually_nhdsWithin_iff.1 (hiso z₁), fun w hw => hw⟩
  have hU' : U ∩ {z₂}ᶜ ∈ 𝓝 z₁ := inter_mem hU (isOpen_compl_singleton.mem_nhds (Ne.symm h12))
  obtain ⟨V, hV, hVc, hVU⟩ := exists_mem_nhds_isClosed_subset hU'
  set W := interior V with hWdef
  have hWo : IsOpen W := isOpen_interior
  have hz₁W : z₁ ∈ W := mem_interior_iff_mem_nhds.2 hV
  have hclW : closure W ⊆ V := closure_minimal interior_subset hVc
  set F := closure W ∩ Wᶜ with hFdef
  have hFc : IsCompact F := (isClosed_closure.inter hWo.isClosed_compl).isCompact
  have h1 : ∃ᶠ t in 𝓝[<] b, c t ∈ W := hz₁.frequently (hWo.mem_nhds hz₁W)
  have hz₂W : z₂ ∉ closure W := fun h => (hVU (hclW h)).2 rfl
  have h2 : ∃ᶠ t in 𝓝[<] b, c t ∈ (closure W)ᶜ :=
    hz₂.frequently (isClosed_closure.isOpen_compl.mem_nhds hz₂W)
  have h3 : ∃ᶠ t in 𝓝[<] b, c t ∈ F := by
    rw [(nhdsLT_basis b).frequently_iff] at h1 h2 ⊢
    intro t₀ ht₀
    obtain ⟨t₁, ht₁, hct₁⟩ := h1 (max t₀ a) (max_lt ht₀ hab)
    obtain ⟨t₂, ht₂, hct₂⟩ := h2 t₁ ht₁.2
    have hat₁ : a < t₁ := lt_of_le_of_lt (le_max_right _ _) ht₁.1
    have ht₀₁ : t₀ < t₁ := lt_of_le_of_lt (le_max_left _ _) ht₁.1
    have hsub : Icc t₁ t₂ ⊆ Ioo a b := fun s hs => ⟨lt_of_lt_of_le hat₁ hs.1, lt_of_le_of_lt hs.2 ht₂.2⟩
    have hconn : IsPreconnected (c '' Icc t₁ t₂) :=
      isPreconnected_Icc.image c fun s hs => (hc s (hsub hs)).1.continuousWithinAt
    by_contra hno
    have hcov : c '' Icc t₁ t₂ ⊆ W ∪ (closure W)ᶜ := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hsW : c s ∈ W
      · exact Or.inl hsW
      · refine Or.inr fun hcl => hno ⟨s, ⟨lt_of_lt_of_le ht₀₁ hs.1, lt_of_le_of_lt hs.2 ht₂.2⟩, hcl, hsW⟩
    obtain ⟨_, -, hw1, hw2⟩ := hconn W (closure W)ᶜ hWo isClosed_closure.isOpen_compl hcov
      ⟨c t₁, ⟨t₁, left_mem_Icc.2 ht₂.1.le, rfl⟩, hct₁⟩ ⟨c t₂, ⟨t₂, right_mem_Icc.2 ht₂.1.le, rfl⟩, hct₂⟩
    exact hw2 (subset_closure hw1)
  obtain ⟨w, hwF, hw⟩ := hFc.exists_mapClusterPt_of_frequently h3
  exact hUreg w (hVU (hclW hwF.1)).1 (fun h => hwF.2 (h ▸ hz₁W)) (hclu w hw)

/-- A unit-speed horizontal trajectory on `(-r, β)` through `p = c 0` converging to a zero of `q` as `t → β⁻` gives a
critical arc through `p` (shift the time by `r`). -/
theorem s26v_a_arc_of_end {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {r β : ℝ} {p z₀ : S₀} (hr : 0 < r) (hβ : 0 < β)
    (hc : ∀ t ∈ Ioo (-r) β, s26v_IsTrajAt q c t) (hp : c 0 = p) (hz₀ : q z₀ (chartAt ℂ z₀ z₀) = 0)
    (hlim : Tendsto c (𝓝[<] β) (𝓝 z₀)) :
    ∃ (c' : ℝ → S₀) (b : ℝ), s26v_IsCritArc q c' b ∧ p ∈ c' '' Ioo 0 b := by
  have h1 : Tendsto (fun s : ℝ => s + -r) (𝓝[<] (β + r)) (𝓝[<] β) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun s : ℝ => s + -r) := by fun_prop
      exact (hcont.tendsto' (β + r) β (by ring)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      show s + -r < β
      have hs' : s < β + r := hs
      linarith
  refine ⟨fun s => c (s + -r), β + r, ⟨by linarith, fun t ht => s26v_trajAt_shift
    (hc (t + -r) ⟨by linarith [ht.1], by linarith [ht.2]⟩), z₀, hz₀, hlim.comp h1⟩, r, ⟨hr, by linarith⟩, ?_⟩
  show c (r + -r) = p
  rw [add_neg_cancel, hp]

/-- **[V3, stub]** (T1, trajectory continuation).  On a compact surface, a regular point through which no bi-infinite
trajectory passes lies on a critical arc.  (The maximal trajectory through `p` has a finite end `b`, after a
reversal; every cluster point of `c(t)`, `t → b`, is a zero — at a regular cluster point a flow box would continue
`c` past `b` ([V1], [V2b], [V2c]); the cluster set is connected and the zeros are isolated, so `c(t)` converges to a
zero.) -/
theorem s26v_mem_critArc [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p : S₀} (hp : p ∈ s26v_E q)
    (hreg : q p (chartAt ℂ p p) ≠ 0) : ∃ (c : ℝ → S₀) (b : ℝ), s26v_IsCritArc q c b ∧ p ∈ c '' Ioo 0 b := by
  classical
  -- the reference local trajectory `c₀` through `p`
  obtain ⟨B, Z, hpB, -, hB⟩ := s26v_exists_flowBox hq hreg (univ_mem : univ ∈ 𝓝 p)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hB.2.2.2.1 (Z p) ⟨p, hpB, rfl⟩
  obtain ⟨c₀, hc₀0, hc₀⟩ := s26v_flowBox_line hq hB hpB (a := -r) (b := r) (by linarith) hr fun s hs => hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.2 hs)
  -- admissible trajectories through `p`: those agreeing with `c₀` near `0`
  set Adm : (ℝ → S₀) → ℝ → ℝ → Prop := fun c a b =>
    a < 0 ∧ 0 < b ∧ (∀ t ∈ Ioo a b, s26v_IsTrajAt q c t) ∧ c =ᶠ[𝓝 0] c₀ with hAdm
  have hAdm₀ : Adm c₀ (-r) r := ⟨by linarith, hr, fun t ht => (hc₀ t ht).2.2, EventuallyEq.rfl⟩
  have huniq : ∀ (c : ℝ → S₀) (a b : ℝ) (c' : ℝ → S₀) (a' b' : ℝ), Adm c a b → Adm c' a' b' →
      ∀ t ∈ Ioo (max a a') (min b b'), c t = c' t := by
    intro c a b c' a' b' h h' t ht
    exact s26v_a_eqOn_of_eventuallyEq hq isOpen_Ioo isPreconnected_Ioo
      (fun s hs => h.2.2.1 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (fun s hs => h'.2.2.1 s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
      (⟨max_lt h.1 h'.1, lt_min h.2.1 h'.2.1⟩ : (0 : ℝ) ∈ Ioo (max a a') (min b b'))
      (h.2.2.2.trans h'.2.2.2.symm) t ht
  -- the glued maximal trajectory
  set cs : ℝ → S₀ := fun t => if h : ∃ x : (ℝ → S₀) × ℝ × ℝ, Adm x.1 x.2.1 x.2.2 ∧ t ∈ Ioo x.2.1 x.2.2 then
    (Classical.choose h).1 t else p with hcsdef
  have hcs : ∀ (c : ℝ → S₀) (a b : ℝ), Adm c a b → ∀ t ∈ Ioo a b, cs t = c t := by
    intro c a b h t ht
    have hex : ∃ x : (ℝ → S₀) × ℝ × ℝ, Adm x.1 x.2.1 x.2.2 ∧ t ∈ Ioo x.2.1 x.2.2 := ⟨(c, a, b), h, ht⟩
    have hspec := Classical.choose_spec hex
    have hval : cs t = (Classical.choose hex).1 t := by
      simp only [hcsdef, hex, ↓reduceDIte]
    rw [hval]
    exact huniq _ _ _ c a b hspec.1 h t ⟨max_lt hspec.2.1 ht.1, lt_min hspec.2.2 ht.2⟩
  have hcsT : ∀ (c : ℝ → S₀) (a b : ℝ), Adm c a b → ∀ t ∈ Ioo a b, s26v_IsTrajAt q cs t := by
    intro c a b h t ht
    refine s26v_a_trajAt_congr (h.2.2.1 t ht) ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using (hcs c a b h s hs).symm
  have h0r : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hcs0 : cs =ᶠ[𝓝 0] c₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds h0r] with s hs using hcs c₀ (-r) r hAdm₀ s hs
  have hcsp : cs 0 = p := by rw [hcs c₀ (-r) r hAdm₀ 0 h0r, hc₀0]
  -- the right and left ends of the admissible trajectories
  set Bs : Set ℝ := {b | ∃ (c : ℝ → S₀) (a : ℝ), Adm c a b} with hBs
  set As : Set ℝ := {a | ∃ (c : ℝ → S₀) (b : ℝ), Adm c a b} with hAs
  have hrB : r ∈ Bs := ⟨c₀, -r, hAdm₀⟩
  have hrA : -r ∈ As := ⟨c₀, r, hAdm₀⟩
  by_cases hBd : BddAbove Bs
  · -- a finite right end
    set bp := sSup Bs with hbp
    have hrbp : r ≤ bp := le_csSup hBd hrB
    have hT : ∀ t ∈ Ioo (-r) bp, s26v_IsTrajAt q cs t := by
      intro t ht
      by_cases htr : t < r
      · exact hcsT c₀ (-r) r hAdm₀ t ⟨ht.1, htr⟩
      · obtain ⟨b', ⟨c', a', h'⟩, hb'⟩ := exists_lt_of_lt_csSup ⟨r, hrB⟩ ht.2
        exact hcsT c' a' b' h' t ⟨by linarith [h'.1], hb'⟩
    have hNE : ∀ (c' : ℝ → S₀) (b' : ℝ), bp < b' → (∀ t ∈ Ioo (-r) b', s26v_IsTrajAt q c' t) →
        ∀ t₀ ∈ Ioo (-r) bp, c' =ᶠ[𝓝 t₀] cs → False := by
      intro c' b' hb' hc' t₀ ht₀ heq
      have hJ := s26v_a_eqOn_of_eventuallyEq hq isOpen_Ioo isPreconnected_Ioo
        (fun s hs => hc' s ⟨hs.1, by linarith [hs.2]⟩) hT ht₀ heq
      have h0 : c' =ᶠ[𝓝 0] c₀ := by
        have h1 : c' =ᶠ[𝓝 0] cs := by
          filter_upwards [isOpen_Ioo.mem_nhds (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Ioo (-r) bp)]
            with s hs using hJ s hs
        exact h1.trans hcs0
      have hmem : b' ∈ Bs := ⟨c', -r, by linarith, by linarith, hc', h0⟩
      linarith [le_csSup hBd hmem]
    obtain ⟨z₀, hz₀, hlim⟩ := s26v_a_right_end hq hne (by linarith : -r < bp) hT hNE
    exact s26v_a_arc_of_end hr (by linarith) hT hcsp hz₀ hlim
  by_cases hAd : BddBelow As
  · -- a finite left end: reverse the trajectory
    set ap := sInf As with hap
    have hapr : ap ≤ -r := csInf_le hAd hrA
    have hT' : ∀ t ∈ Ioo ap r, s26v_IsTrajAt q cs t := by
      intro t ht
      by_cases htr : -r < t
      · exact hcsT c₀ (-r) r hAdm₀ t ⟨htr, ht.2⟩
      · obtain ⟨a', ⟨c', b', h'⟩, ha'⟩ := exists_lt_of_csInf_lt ⟨-r, hrA⟩ ht.1
        exact hcsT c' a' b' h' t ⟨ha', by linarith [h'.2.1]⟩
    set cr : ℝ → S₀ := fun t => cs (-t) with hcr
    have hT : ∀ t ∈ Ioo (-r) (-ap), s26v_IsTrajAt q cr t := fun t ht =>
      s26v_trajAt_neg (hT' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hNE : ∀ (c' : ℝ → S₀) (b' : ℝ), -ap < b' → (∀ t ∈ Ioo (-r) b', s26v_IsTrajAt q c' t) →
        ∀ t₀ ∈ Ioo (-r) (-ap), c' =ᶠ[𝓝 t₀] cr → False := by
      intro c' b' hb' hc' t₀ ht₀ heq
      have hneg : Tendsto (fun v : ℝ => -v) (𝓝 (-t₀)) (𝓝 t₀) := continuous_neg.tendsto' (-t₀) t₀ (neg_neg t₀)
      have heq' : (fun s => c' (-s)) =ᶠ[𝓝 (-t₀)] cs := by
        filter_upwards [hneg.eventually heq] with v hv
        simp only [hcr, neg_neg] at hv
        exact hv
      have hJ := s26v_a_eqOn_of_eventuallyEq hq (c := fun s => c' (-s)) isOpen_Ioo isPreconnected_Ioo
        (fun s hs => s26v_trajAt_neg (hc' (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)) hT'
        (⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩ : -t₀ ∈ Ioo ap r) heq'
      have h0 : (fun s => c' (-s)) =ᶠ[𝓝 0] c₀ := by
        have h1 : (fun s => c' (-s)) =ᶠ[𝓝 0] cs := by
          filter_upwards [isOpen_Ioo.mem_nhds (⟨by linarith, hr⟩ : (0 : ℝ) ∈ Ioo ap r)] with s hs using hJ s hs
        exact h1.trans hcs0
      have hmem : -b' ∈ As := ⟨fun s => c' (-s), r, by linarith, hr,
        fun s hs => s26v_trajAt_neg (hc' (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩), h0⟩
      linarith [csInf_le hAd hmem]
    obtain ⟨z₀, hz₀, hlim⟩ := s26v_a_right_end hq hne (by linarith : -r < -ap) hT hNE
    exact s26v_a_arc_of_end hr (by linarith) hT (by simp only [hcr, neg_zero]; exact hcsp) hz₀ hlim
  · -- otherwise the glued trajectory is bi-infinite, contradicting `p ∈ s26v_E q`
    exfalso
    rw [not_bddAbove_iff] at hBd
    rw [not_bddBelow_iff] at hAd
    have hT : ∀ t, s26v_IsTrajAt q cs t := by
      intro t
      by_cases ht : 0 ≤ t
      · obtain ⟨b', ⟨c', a', h'⟩, hb'⟩ := hBd t
        exact hcsT c' a' b' h' t ⟨by linarith [h'.1], hb'⟩
      · obtain ⟨a', ⟨c', b', h'⟩, ha'⟩ := hAd t
        exact hcsT c' a' b' h' t ⟨ha', by linarith [h'.2.1]⟩
    exact hp ⟨⟨cs, continuous_iff_continuousAt.2 fun t => (hT t).1⟩, hT, hcsp⟩

/-- A curve with constant derivative `σ` on an open interval is affine there: `W s = W t₀ + σ (s - t₀)`. -/
theorem s26v_b_affine {W : ℝ → ℂ} {J : Set ℝ} (hJo : IsOpen J) (hJc : Convex ℝ J) {σ : ℂ}
    (hW : ∀ t ∈ J, HasDerivAt W σ t) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∀ s ∈ J, W s = W t₀ + σ * ((s - t₀ : ℝ) : ℂ) := by
  have hlin : ∀ s : ℝ, HasDerivAt (fun s : ℝ => W t₀ + σ * ((s - t₀ : ℝ) : ℂ)) σ s := by
    intro s
    have h := (((hasDerivAt_id s).sub_const t₀).ofReal_comp).const_mul σ
    simpa using h.const_add (W t₀)
  intro s hs
  have h := hJo.eqOn_of_deriv_eq hJc.isPreconnected (f := W)
    (g := fun s : ℝ => W t₀ + σ * ((s - t₀ : ℝ) : ℂ))
    (fun t ht => (hW t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hlin t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hW t ht).deriv, (hlin t).deriv]) ht₀ (by simp)
  exact h hs

/-- **Darboux**: a curve in `ℂ` whose derivative is `1` or `-1` at every point of an interval has one sign there
(the real part has derivative `±1 ≠ 0`, `hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`). -/
theorem s26v_b_sign_const {W : ℝ → ℂ} {J : Set ℝ} (hJ : Convex ℝ J)
    (hW : ∀ t ∈ J, HasDerivAt W 1 t ∨ HasDerivAt W (-1) t) :
    (∀ t ∈ J, HasDerivAt W 1 t) ∨ ∀ t ∈ J, HasDerivAt W (-1) t := by
  classical
  set σ : ℝ → ℝ := fun t => if HasDerivAt W 1 t then 1 else -1 with hσ
  have hWσ : ∀ t ∈ J, HasDerivAt W (σ t : ℂ) t := by
    intro t ht
    by_cases h : HasDerivAt W 1 t
    · simp only [hσ, ite_eq_left h]
      exact_mod_cast h
    · simp only [hσ, ite_eq_right h]
      push_cast
      exact (hW t ht).resolve_left h
  have hre : ∀ t ∈ J, HasDerivWithinAt (fun s => (W s).re) (σ t) J t := by
    intro t ht
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hWσ t ht)
    have h2 : HasDerivAt (fun s => (W s).re) (σ t) t := by
      simpa [Function.comp_def] using h
    exact h2.hasDerivWithinAt
  have hne : ∀ t ∈ J, σ t ≠ 0 := by
    intro t _
    simp only [hσ]
    split_ifs <;> norm_num
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hJ hre hne with h | h
  · right
    intro t ht
    have h1 := h t ht
    have h2 : ¬ HasDerivAt W 1 t := by
      intro h3
      simp only [hσ, ite_eq_left h3] at h1
      norm_num at h1
    exact (hW t ht).resolve_left h2
  · left
    intro t ht
    have h1 := h t ht
    by_contra h3
    simp only [hσ, ite_eq_right h3] at h1
    norm_num at h1

/-- In a flow box, a unit-speed horizontal trajectory staying in the box on an open interval runs along a horizontal
line at unit speed: `Z (c s) = Z (c t₀) + σ (s - t₀)` with one sign `σ = ±1` (`s26v_flowBox_deriv` and Darboux). -/
theorem s26v_b_line_of_box {q : S₀ → ℂ → ℂ} {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z)
    {c : ℝ → S₀} {J : Set ℝ} (hJo : IsOpen J) (hJc : Convex ℝ J) (hc : ∀ t ∈ J, s26v_IsTrajAt q c t)
    (hcB : ∀ t ∈ J, c t ∈ B) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ ∀ s ∈ J, Z (c s) = Z (c t₀) + σ * ((s - t₀ : ℝ) : ℂ) := by
  rcases s26v_b_sign_const hJc fun t ht => s26v_flowBox_deriv hB (hc t ht) (hcB t ht) with h | h
  · exact ⟨1, Or.inl rfl, s26v_b_affine (W := fun s => Z (c s)) hJo hJc h ht₀⟩
  · exact ⟨-1, Or.inr rfl, s26v_b_affine (W := fun s => Z (c s)) hJo hJc h ht₀⟩

/-- **Uniqueness of trajectories on an interval**: two unit-speed horizontal trajectories on an open interval `J` that
agree near one of its points agree on all of `J`.  (The set of times near which they agree is open; it is relatively
closed in `J`: at a limit time the curves meet (T2), and in a flow box ([V1]) around the meeting point both run along
horizontal lines with signs that agree at nearby common times (`s26v_b_line_of_box`), and `Z` is injective.) -/
theorem s26v_b_traj_eqOn [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c₁ c₂ : ℝ → S₀} {J : Set ℝ} (hJo : IsOpen J) (hJc : Convex ℝ J)
    (h₁ : ∀ t ∈ J, s26v_IsTrajAt q c₁ t) (h₂ : ∀ t ∈ J, s26v_IsTrajAt q c₂ t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h0 : c₁ =ᶠ[𝓝 t₀] c₂) : ∀ t ∈ J, c₁ t = c₂ t := by
  set A : Set ℝ := {t | c₁ =ᶠ[𝓝 t] c₂} with hA
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hJA : J ⊆ A := by
    refine hJc.isPreconnected.subset_of_closure_inter_subset hAo ⟨t₀, ht₀, h0⟩ ?_
    rintro t ⟨htA, htJ⟩
    have hct : c₁ t = c₂ t := by
      have hne : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htA
      have hl1 : Tendsto c₁ (𝓝[A] t) (𝓝 (c₁ t)) := (h₁ t htJ).1.tendsto.mono_left nhdsWithin_le_nhds
      have hl2 : Tendsto c₂ (𝓝[A] t) (𝓝 (c₂ t)) := (h₂ t htJ).1.tendsto.mono_left nhdsWithin_le_nhds
      have heq : c₁ =ᶠ[𝓝[A] t] c₂ := eventually_nhdsWithin_of_forall fun s hs => hs.self_of_nhds
      exact tendsto_nhds_unique (hl1.congr' heq) hl2
    obtain ⟨-, v, -, hqv⟩ := h₁ t htJ
    have hp : q (c₁ t) (chartAt ℂ (c₁ t) (c₁ t)) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hqv
      exact zero_ne_one hqv
    obtain ⟨B, Z, hpB, -, hB⟩ := s26v_exists_flowBox hq hp (W := univ) univ_mem
    have hev : ∀ᶠ s in 𝓝 t, s ∈ J ∧ c₁ s ∈ B ∧ c₂ s ∈ B := by
      filter_upwards [hJo.mem_nhds htJ, (h₁ t htJ).1.preimage_mem_nhds (hB.1.mem_nhds hpB),
        (h₂ t htJ).1.preimage_mem_nhds (hB.1.mem_nhds (hct ▸ hpB))] with s h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    have hIo : IsOpen (ball t δ) := isOpen_ball
    have hIc : Convex ℝ (ball t δ) := convex_ball t δ
    obtain ⟨σ₁, -, hσ₁⟩ := s26v_b_line_of_box hB hIo hIc (fun s hs => h₁ s (hball s hs).1)
      (fun s hs => (hball s hs).2.1) (mem_ball_self hδ)
    obtain ⟨σ₂, -, hσ₂⟩ := s26v_b_line_of_box hB hIo hIc (fun s hs => h₂ s (hball s hs).1)
      (fun s hs => (hball s hs).2.2) (mem_ball_self hδ)
    obtain ⟨s₀, hs₀A, hs₀I⟩ : (A ∩ ball t δ).Nonempty :=
      mem_closure_iff_nhds.1 htA _ (isOpen_ball.mem_nhds (mem_ball_self hδ)) |>.mono fun s hs => ⟨hs.2, hs.1⟩
    obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hAo.inter isOpen_ball) s₀ ⟨hs₀A, hs₀I⟩
    obtain ⟨s, ⟨hsA, hsI⟩, hst⟩ : ∃ s, s ∈ A ∩ ball t δ ∧ s ≠ t := by
      by_cases h : s₀ = t
      · refine ⟨s₀ + ε / 2, hεs ?_, ?_⟩
        · rw [mem_ball, Real.dist_eq]
          rw [abs_of_pos (by linarith)]
          linarith
        · rw [h]
          linarith
      · exact ⟨s₀, ⟨hs₀A, hs₀I⟩, h⟩
    have hσ : σ₁ = σ₂ := by
      have e := congrArg Z hsA.self_of_nhds
      rw [hσ₁ s hsI, hσ₂ s hsI, hct] at e
      have hne : ((s - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hst
      exact mul_right_cancel₀ hne (add_left_cancel e)
    show c₁ =ᶠ[𝓝 t] c₂
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with s hs
    apply hB.2.2.1 (hball s hs).2.1 (hball s hs).2.2
    rw [hσ₁ s hs, hσ₂ s hs, hct, hσ]
  intro t ht
  exact (hJA ht).self_of_nhds

/-- **The local square root in `V'² = 4V`**: if `V` is differentiable with `(V')² = 4V ≠ 0` on an open set `J`, then
`V'` has derivative `2` at every point of `J`.  (A holomorphic square root `sq` near `V(t₀)` with
`sq(V t₀) = V'(t₀)/2` makes `sq ∘ V` a curve with derivative `±1`, of one sign by Darboux (`s26v_b_sign_const`), so
`V = (V'(t₀)/2 ± (t - t₀))²` near `t₀`.) -/
theorem s26v_b_ode_local {V : ℝ → ℂ} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, HasDerivAt V (deriv V t) t) (hV' : ∀ t ∈ J, deriv V t ^ 2 = 4 * V t)
    (hV0 : ∀ t ∈ J, V t ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ J) : HasDerivAt (deriv V) 2 t₀ := by
  set V₀ := V t₀ with hV₀def
  have hV₀ : V₀ ≠ 0 := hV0 t₀ ht₀
  set s₀ := deriv V t₀ / 2 with hs₀def
  have hs₀ : s₀ ^ 2 = V₀ := by
    rw [hs₀def, div_pow, hV' t₀ ht₀]
    ring
  set sq : ℂ → ℂ := fun w => s₀ * (w / V₀) ^ (((2 : ℕ) : ℂ)⁻¹) with hsqdef
  have hsq2 : ∀ w, sq w ^ 2 = w := by
    intro w
    simp only [hsqdef]
    rw [mul_pow, Complex.cpow_nat_inv_pow _ two_ne_zero, hs₀]
    field_simp
  set U : Set ℂ := (fun w => w / V₀) ⁻¹' ball 1 1 with hU
  have hUo : IsOpen U := isOpen_ball.preimage (continuous_id.div_const V₀)
  have hV₀U : V₀ ∈ U := by
    simp [hU, div_self hV₀]
  have hsqd : ∀ w ∈ U, ∃ d : ℂ, HasDerivAt sq d w ∧ 2 * sq w * d = 1 := by
    intro w hw
    have hslit : w / V₀ ∈ slitPlane := ball_one_subset_slitPlane hw
    have h1 : HasDerivAt (fun w : ℂ => w / V₀) (1 / V₀) w := (hasDerivAt_id w).div_const V₀
    have h2 := (h1.cpow_const (c := ((2 : ℕ) : ℂ)⁻¹) hslit).const_mul s₀
    obtain ⟨d, hd⟩ : ∃ d, HasDerivAt sq d w := ⟨_, h2⟩
    refine ⟨d, hd, ?_⟩
    have h3 := hd.fun_pow 2
    have h4 : HasDerivAt (fun w => sq w ^ 2) 1 w := by
      have e : (fun w => sq w ^ 2) = id := funext hsq2
      rw [e]
      exact hasDerivAt_id w
    have h5 := h3.unique h4
    simpa using h5
  choose! d hd hd2 using hsqd
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ J ∧ V t ∈ U := by
    filter_upwards [hJ.mem_nhds ht₀, (hV t₀ ht₀).continuousAt.preimage_mem_nhds (hUo.mem_nhds hV₀U)]
      with t h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hI : ∀ t ∈ ball t₀ δ, HasDerivAt (fun t => sq (V t)) (d (V t) * deriv V t) t := by
    intro t ht
    exact (hd (V t) (hball t ht).2).comp t (hV t (hball t ht).1)
  have hI1 : ∀ t ∈ ball t₀ δ, HasDerivAt (fun t => sq (V t)) 1 t ∨ HasDerivAt (fun t => sq (V t)) (-1) t := by
    intro t ht
    have he : (d (V t) * deriv V t) ^ 2 = 1 := by
      have h1 := hd2 (V t) (hball t ht).2
      have h2 := hV' t (hball t ht).1
      have h3 := hsq2 (V t)
      calc (d (V t) * deriv V t) ^ 2 = d (V t) ^ 2 * (4 * V t) := by rw [mul_pow, h2]
        _ = d (V t) ^ 2 * (4 * sq (V t) ^ 2) := by rw [h3]
        _ = (2 * sq (V t) * d (V t)) ^ 2 := by ring
        _ = 1 := by rw [h1, one_pow]
    rcases sq_eq_one_iff.1 he with h | h
    · exact Or.inl (h ▸ hI t ht)
    · exact Or.inr (h ▸ hI t ht)
  have hW0 : sq (V t₀) = s₀ := by
    simp only [hsqdef, ← hV₀def, div_self hV₀, Complex.one_cpow, mul_one]
  have hform : ∃ σ : ℂ, σ ^ 2 = 1 ∧ ∀ t ∈ ball t₀ δ, V t = (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) ^ 2 := by
    rcases s26v_b_sign_const (convex_ball t₀ δ) hI1 with h | h
    · refine ⟨1, one_pow 2, fun t ht => ?_⟩
      rw [← hsq2 (V t), s26v_b_affine isOpen_ball (convex_ball t₀ δ) h (mem_ball_self hδ) t ht, hW0]
    · refine ⟨-1, by ring, fun t ht => ?_⟩
      rw [← hsq2 (V t), s26v_b_affine isOpen_ball (convex_ball t₀ δ) h (mem_ball_self hδ) t ht, hW0]
  obtain ⟨σ, hσ, hVI⟩ := hform
  have hP : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) ^ 2)
      (2 * (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) * σ) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => s₀ + σ * ((t - t₀ : ℝ) : ℂ)) σ t := by
      have h := (((hasDerivAt_id t).sub_const t₀).ofReal_comp).const_mul σ
      simpa using h.const_add s₀
    have h2 := h1.fun_pow 2
    convert h2 using 1
    push_cast
    ring
  have hdV : ∀ t ∈ ball t₀ δ, deriv V t = 2 * (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) * σ := by
    intro t ht
    have hev' : V =ᶠ[𝓝 t] fun t : ℝ => (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) ^ 2 := by
      filter_upwards [isOpen_ball.mem_nhds ht] with s hs
      exact hVI s hs
    exact (hV t (hball t ht).1).unique ((hP t).congr_of_eventuallyEq hev')
  have hQ : HasDerivAt (fun t : ℝ => 2 * (s₀ + σ * ((t - t₀ : ℝ) : ℂ)) * σ) 2 t₀ := by
    have h1 : HasDerivAt (fun t : ℝ => s₀ + σ * ((t - t₀ : ℝ) : ℂ)) σ t₀ := by
      have h := (((hasDerivAt_id t₀).sub_const t₀).ofReal_comp).const_mul σ
      simpa using h.const_add s₀
    have h2 := (h1.const_mul 2).mul_const σ
    have e : 2 * σ * σ = 2 := by rw [mul_assoc, ← pow_two, hσ, mul_one]
    rw [e] at h2
    exact h2
  refine hQ.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with t ht
  exact hdV t ht

/-- **The critical-arc ODE**: if on `(a, b)` the curve `V` is differentiable with `(V')² = 4V ≠ 0`, and `V → 0` as
`t → b⁻`, then `V(t) = (b - t)²`.  (`V'' = 2` by `s26v_b_ode_local`, so `V = t² + C₁ t + C₂`; `(V')² = 4V` forces
`C₁² = 4C₂`, and the limit fixes `C₁ = -2b`.) -/
theorem s26v_b_ode {V : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hV : ∀ t ∈ Ioo a b, HasDerivAt V (deriv V t) t) (hV' : ∀ t ∈ Ioo a b, deriv V t ^ 2 = 4 * V t)
    (hV0 : ∀ t ∈ Ioo a b, V t ≠ 0) (hlim : Tendsto V (𝓝[<] b) (𝓝 0)) :
    ∀ t ∈ Ioo a b, V t = ((b - t : ℝ) : ℂ) ^ 2 := by
  have h2 : ∀ t ∈ Ioo a b, HasDerivAt (deriv V) 2 t := fun t ht =>
    s26v_b_ode_local isOpen_Ioo hV hV' hV0 ht
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 2 * (t : ℂ)) 2 t := by
    intro t
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (2 : ℂ)
  obtain ⟨C₁, hC₁⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq (convex_Ioo a b).isPreconnected
    (f := deriv V) (g := fun t : ℝ => 2 * (t : ℂ))
    (fun t ht => (h2 t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hlin t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(h2 t ht).deriv, (hlin t).deriv])
  have hquad : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 + C₁ * t) (2 * (t : ℂ) + C₁) t := by
    intro t
    have h1 := ((hasDerivAt_id' t).ofReal_comp).fun_pow 2
    have h2 := ((hasDerivAt_id' t).ofReal_comp).const_mul C₁
    have h3 := h1.add h2
    convert h3 using 1
    push_cast
    ring
  obtain ⟨C₂, hC₂⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq (convex_Ioo a b).isPreconnected
    (f := V) (g := fun t : ℝ => (t : ℂ) ^ 2 + C₁ * t)
    (fun t ht => (hV t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hquad t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hquad t).deriv, hC₁ ht])
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hC : C₁ ^ 2 = 4 * C₂ := by
    have h := hV' _ hmid
    rw [hC₁ hmid, hC₂ hmid] at h
    linear_combination h
  have hform : ∀ t ∈ Ioo a b, V t = ((t : ℂ) + C₁ / 2) ^ 2 := by
    intro t ht
    rw [hC₂ ht]
    linear_combination (-1 / 4 : ℂ) * hC
  have hb : ((b : ℂ) + C₁ / 2) ^ 2 = 0 := by
    have h1 : Tendsto (fun t : ℝ => ((t : ℂ) + C₁ / 2) ^ 2) (𝓝[<] b) (𝓝 (((b : ℂ) + C₁ / 2) ^ 2)) :=
      ((Complex.continuous_ofReal.add continuous_const).pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : V =ᶠ[𝓝[<] b] fun t : ℝ => ((t : ℂ) + C₁ / 2) ^ 2 := by
      filter_upwards [Ioo_mem_nhdsLT hab] with t ht
      exact hform t ht
    exact tendsto_nhds_unique (hlim.congr' h2) h1 |>.symm
  have hb' : C₁ / 2 = -(b : ℂ) := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hb
    linear_combination this
  intro t ht
  rw [hform t ht, hb']
  push_cast
  ring

/-- The `n`-th roots of unity form a finite set. -/
theorem s26v_b_roots_finite {n : ℕ} (hn : 0 < n) : ({w : ℂ | w ^ n = 1}).Finite := by
  classical
  refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun w hw => ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_nthRoots hn).2 hw

/-- A continuous function on a preconnected set whose values are `n`-th roots of unity is constant (the roots of
unity form a finite, hence discrete, set). -/
theorem s26v_b_root_const {f : ℝ → ℂ} {J : Set ℝ} (hJ : IsPreconnected J) (hf : ContinuousOn f J) {n : ℕ}
    (hn : 0 < n) (hroot : ∀ t ∈ J, f t ^ n = 1) {t t' : ℝ} (ht : t ∈ J) (ht' : t' ∈ J) : f t = f t' :=
  hJ.constant_of_mapsTo (s26v_b_roots_finite hn).isDiscrete hf (fun s hs => hroot s hs) ht ht'

/-- **The local structure at a zero** `z₀` of `q ≢ 0` on a connected surface: its order `m ≥ 1`, a natural parameter
`ζ` at `w₀ = φ_{z₀}(z₀)` (`eq25_5_natural_parameter_zero`: `q_{z₀} = ((m+2)/2)² ζ^m ζ'²`, `ζ(w₀) = 0`), and an open
neighbourhood `W` of `w₀` in the chart target on which `ζ` is holomorphic and injective (`s26u_exists_open_injOn`) and
the factorization holds. -/
theorem s26v_b_zero_structure [T2Space S₀] [ConnectedSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) {z₀ : S₀} (hz₀ : q z₀ (chartAt ℂ z₀ z₀) = 0) :
    ∃ (m : ℕ) (ζ : ℂ → ℂ) (W : Set ℂ), 0 < m ∧ IsOpen W ∧ chartAt ℂ z₀ z₀ ∈ W ∧
      W ⊆ (chartAt ℂ z₀).target ∧ InjOn ζ W ∧ ζ (chartAt ℂ z₀ z₀) = 0 ∧
      ∀ w ∈ W, DifferentiableAt ℂ ζ w ∧ q z₀ w = ((m + 2 : ℂ) / 2) ^ 2 * ζ w ^ m * deriv ζ w ^ 2 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  set w₀ := chartAt ℂ z₀ z₀ with hw₀def
  have hw₀ : w₀ ∈ (chartAt ℂ z₀).target := (chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀)
  have han : AnalyticAt ℂ (q z₀) w₀ := (hq'.2 z₀).analyticAt ((chartAt ℂ z₀).open_target.mem_nhds hw₀)
  have hnz : ¬ ∀ᶠ w in 𝓝 w₀, q z₀ w = 0 := by
    intro h
    have hsymm : (chartAt ℂ z₀).symm w₀ = z₀ := (chartAt ℂ z₀).left_inv (mem_chart_source ℂ z₀)
    have hw := s26u_eventually_ne_zero hq z₀ hw₀ (by rw [hsymm]; exact s26u_frequently_regular hq hne z₀)
    have h2 : ∀ᶠ w in 𝓝[≠] w₀, q z₀ w = 0 := nhdsWithin_le_nhds h
    obtain ⟨w, hw1, hw2⟩ := (h2.and hw).exists
    exact hw2 hw1
  obtain ⟨m, g, hg, hg0, hfac⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at hfac
      have h1 := hfac.self_of_nhds
      simp only [pow_zero, one_smul] at h1
      exact hg0 (h1 ▸ hz₀)
    · exact h
  obtain ⟨ζ, hζ, hζ0, hζ', hζfac⟩ := eq25_5_natural_parameter_zero hm hg hg0
    (by simpa only [smul_eq_mul] using hfac)
  obtain ⟨W₁, hW₁o, hw₀W₁, hζd, hζi⟩ := s26u_exists_open_injOn hζ hζ'
  refine ⟨m, ζ, W₁ ∩ (chartAt ℂ z₀).target ∩
      interior {w | q z₀ w = ((m + 2 : ℂ) / 2) ^ 2 * ζ w ^ m * deriv ζ w ^ 2}, hm,
    (hW₁o.inter (chartAt ℂ z₀).open_target).inter isOpen_interior,
    ⟨⟨hw₀W₁, hw₀⟩, mem_interior_iff_mem_nhds.2 hζfac⟩, fun w hw => hw.1.2,
    hζi.mono fun w hw => hw.1.1, hζ0, fun w hw => ⟨hζd.differentiableAt (hW₁o.mem_nhds hw.1.1),
      (interior_subset hw.2 : w ∈ {w | q z₀ w = ((m + 2 : ℂ) / 2) ^ 2 * ζ w ^ m * deriv ζ w ^ 2})⟩⟩

/-- **The tail of a critical arc** ending at a zero `z₀`: in the natural parameter `ζ` of `s26v_b_zero_structure`,
`u = ζ ∘ φ_{z₀} ∘ c` satisfies `((m+2)/2)² u^m u'² = 1`, so `V = u^{m+2}` has `V'² = 4V ≠ 0` and `V → 0`, whence
`V(t) = (b - t)²` (`s26v_b_ode`) and `u(t) = ϑ (b - t)^{2/(m+2)}` with a constant `ϑ`, `ϑ^{m+2} = 1`
(`s26v_b_root_const`). -/
theorem s26v_b_tail [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {z₀ : S₀} {m : ℕ}
    {ζ : ℂ → ℂ} {W : Set ℂ} (hm : 0 < m) (hWo : IsOpen W) (hw₀ : chartAt ℂ z₀ z₀ ∈ W)
    (hζ0 : ζ (chartAt ℂ z₀ z₀) = 0)
    (hζ : ∀ w ∈ W, DifferentiableAt ℂ ζ w ∧ q z₀ w = ((m + 2 : ℂ) / 2) ^ 2 * ζ w ^ m * deriv ζ w ^ 2)
    {c : ℝ → S₀} {b : ℝ} (hb : 0 < b) (hc : ∀ t ∈ Ioo (0 : ℝ) b, s26v_IsTrajAt q c t)
    (hlim : Tendsto c (𝓝[<] b) (𝓝 z₀)) :
    ∃ ϑ : ℂ, ϑ ^ (m + 2) = 1 ∧ ∃ ε > 0, ε ≤ b ∧ ∀ t ∈ Ioo (b - ε) b, c t ∈ (chartAt ℂ z₀).source ∧
      chartAt ℂ z₀ (c t) ∈ W ∧ ζ (chartAt ℂ z₀ (c t)) = ϑ * (((b - t) ^ ((2 : ℝ) / (m + 2)) : ℝ) : ℂ) := by
  have hF : Tendsto (fun t => chartAt ℂ z₀ (c t)) (𝓝[<] b) (𝓝 (chartAt ℂ z₀ z₀)) :=
    ((chartAt ℂ z₀).continuousAt (mem_chart_source ℂ z₀)).tendsto.comp hlim
  have hev : ∀ᶠ t in 𝓝[<] b, c t ∈ (chartAt ℂ z₀).source ∧ chartAt ℂ z₀ (c t) ∈ W :=
    (hlim.eventually ((chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀))).and
      (hF.eventually (hWo.mem_nhds hw₀))
  obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl' : l < b := hl
  set ε := min (b - l) b with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) hb
  have hεb : ε ≤ b := min_le_right _ _
  have hεl : ε ≤ b - l := min_le_left _ _
  have hJ : ∀ t ∈ Ioo (b - ε) b, t ∈ Ioo (0 : ℝ) b ∧ c t ∈ (chartAt ℂ z₀).source ∧ chartAt ℂ z₀ (c t) ∈ W := by
    intro t ht
    exact ⟨⟨by linarith [ht.1], ht.2⟩, hlsub ⟨by linarith [ht.1], ht.2⟩⟩
  set u : ℝ → ℂ := fun t => ζ (chartAt ℂ z₀ (c t)) with hu
  have hder : ∀ t ∈ Ioo (b - ε) b, ∃ u' : ℂ, HasDerivAt u u' t ∧
      ((m + 2 : ℂ) / 2) ^ 2 * u t ^ m * u' ^ 2 = 1 := by
    intro t ht
    obtain ⟨ht0, hts, htW⟩ := hJ t ht
    obtain ⟨v, hv, hqv⟩ := s26v_trajAt_chart hq (hc t ht0) z₀ hts
    obtain ⟨hζd, hζq⟩ := hζ _ htW
    refine ⟨deriv ζ (chartAt ℂ z₀ (c t)) * v, hζd.hasDerivAt.comp t hv, ?_⟩
    rw [hζq] at hqv
    simp only [hu]
    linear_combination hqv
  choose! u' hu' hu'q using hder
  have hu0 : ∀ t ∈ Ioo (b - ε) b, u t ≠ 0 := by
    intro t ht h
    have h1 := hu'q t ht
    rw [h, zero_pow hm.ne', mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  set V : ℝ → ℂ := fun t => u t ^ (m + 2) with hV
  have hVd : ∀ t ∈ Ioo (b - ε) b, HasDerivAt V (((m + 2 : ℕ) : ℂ) * u t ^ (m + 1) * u' t) t := by
    intro t ht
    have h := (hu' t ht).fun_pow (m + 2)
    convert h using 2
    norm_num
  have hVd' : ∀ t ∈ Ioo (b - ε) b, HasDerivAt V (deriv V t) t := fun t ht => by
    rw [(hVd t ht).deriv]
    exact hVd t ht
  have hVsq : ∀ t ∈ Ioo (b - ε) b, deriv V t ^ 2 = 4 * V t := by
    intro t ht
    rw [(hVd t ht).deriv]
    have h := hu'q t ht
    simp only [hV]
    push_cast
    linear_combination (4 * u t ^ (m + 2)) * h
  have hV0 : ∀ t ∈ Ioo (b - ε) b, V t ≠ 0 := fun t ht => pow_ne_zero _ (hu0 t ht)
  have hVlim : Tendsto V (𝓝[<] b) (𝓝 0) := by
    have h1 : Tendsto u (𝓝[<] b) (𝓝 (ζ (chartAt ℂ z₀ z₀))) :=
      ((hζ _ hw₀).1.continuousAt.tendsto).comp hF
    rw [hζ0] at h1
    have h2 := h1.pow (m + 2)
    rwa [zero_pow (by omega)] at h2
  have hVform := s26v_b_ode (a := b - ε) (by linarith) hVd' hVsq hV0 hVlim
  set ρ : ℝ → ℝ := fun t => (b - t) ^ ((2 : ℝ) / (m + 2)) with hρ
  have hρpos : ∀ t ∈ Ioo (b - ε) b, 0 < ρ t := fun t ht =>
    Real.rpow_pos_of_pos (by linarith [ht.2]) _
  have hρpow : ∀ t ∈ Ioo (b - ε) b, ρ t ^ (m + 2) = (b - t) ^ 2 := by
    intro t ht
    simp only [hρ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [ht.2])]
    have e : (2 : ℝ) / (m + 2) * ((m + 2 : ℕ) : ℝ) = 2 := by
      push_cast
      field_simp
    rw [e, Real.rpow_two]
  set Ω : ℝ → ℂ := fun t => u t / (ρ t : ℂ) with hΩ
  have hΩroot : ∀ t ∈ Ioo (b - ε) b, Ω t ^ (m + 2) = 1 := by
    intro t ht
    simp only [hΩ, div_pow]
    have h1 : u t ^ (m + 2) = ((b - t : ℝ) : ℂ) ^ 2 := hVform t ht
    rw [h1, ← Complex.ofReal_pow (ρ t), hρpow t ht]
    have hne : ((b - t : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (sub_pos.2 ht.2).ne')
    push_cast at hne ⊢
    exact div_self hne
  have hΩc : ContinuousOn Ω (Ioo (b - ε) b) := by
    intro t ht
    have hut : ContinuousAt u t := (hu' t ht).continuousAt
    have hρt : ContinuousAt (fun t => (ρ t : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (sub_pos.2 ht.2).ne'))
    exact (hut.div hρt (by exact_mod_cast (hρpos t ht).ne')).continuousWithinAt
  have htm : b - ε / 2 ∈ Ioo (b - ε) b := ⟨by linarith, by linarith⟩
  refine ⟨Ω (b - ε / 2), hΩroot _ htm, ε, hεpos, hεb, fun t ht => ⟨(hJ t ht).2.1, (hJ t ht).2.2, ?_⟩⟩
  have e := s26v_b_root_const (convex_Ioo _ _).isPreconnected hΩc (by omega) hΩroot ht htm
  show u t = Ω (b - ε / 2) * (ρ t : ℂ)
  rw [← e]
  simp only [hΩ]
  rw [div_mul_cancel₀]
  exact_mod_cast (hρpos t ht).ne'

/-- On a compact connected surface the zeros of `q ≢ 0` form a countable set (finitely many chart sources cover, and
the zeros in each chart target are countable, `s26u_zeros_countable`). -/
theorem s26v_b_zeros_countable [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) : {z₀ : S₀ | q z₀ (chartAt ℂ z₀ z₀) = 0}.Countable := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S₀ => (chartAt ℂ x).source)
    (fun x => (chartAt ℂ x).open_source) (fun p _ => mem_iUnion.2 ⟨p, mem_chart_source ℂ p⟩)
  refine ((t.countable_toSet).biUnion fun x _ =>
    (s26u_zeros_countable hq hne x).image (chartAt ℂ x).symm).mono ?_
  intro z₀ hz₀
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.1 (ht (mem_univ z₀))
  refine mem_iUnion₂.2 ⟨x, hxt, chartAt ℂ x z₀, ⟨(chartAt ℂ x).map_source hx, ?_⟩, (chartAt ℂ x).left_inv hx⟩
  by_contra h
  have h1 := (s26u_isRegularPoint_iff hq x ((chartAt ℂ x).map_source hx)).2 h
  rw [(chartAt ℂ x).left_inv hx] at h1
  exact h1 hz₀

/-- **[V4, stub]** (T2, the critical arcs are null).  The union of the critical arcs is null in every chart.  (At a
zero `z₀` of order `m`, in the natural parameter `ζ` of `eq25_5_natural_parameter_zero`, a unit-speed trajectory
`u = ζ ∘ c` has `((m+2)/2)² u^m u'² = 1`, so `V = u^{m+2}` satisfies `V'² = 4V`; converging to `0` at `b` forces
`V(t) = (b - t)²`, i.e. `c` runs along one of the `m + 2` rays `arg ζ ∈ 2πℤ/(m+2)`.  By uniqueness every critical arc
lies on the maximal extension of one of these countably many rays, and ranges of trajectories are null ([V2d]).) -/
theorem s26v_critArc_null [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (x : S₀) :
    volume (chartAt ℂ x '' ({p | ∃ (c : ℝ → S₀) (b : ℝ), s26v_IsCritArc q c b ∧ p ∈ c '' Ioo 0 b} ∩
      (chartAt ℂ x).source)) = 0 := by
  classical
  have hZc := s26v_b_zeros_countable hq hne
  have hstr : ∀ z₀ : S₀, ∃ (m : ℕ) (ζ : ℂ → ℂ) (W : Set ℂ), q z₀ (chartAt ℂ z₀ z₀) = 0 → 0 < m ∧ IsOpen W ∧
      chartAt ℂ z₀ z₀ ∈ W ∧ W ⊆ (chartAt ℂ z₀).target ∧ InjOn ζ W ∧ ζ (chartAt ℂ z₀ z₀) = 0 ∧
      ∀ w ∈ W, DifferentiableAt ℂ ζ w ∧ q z₀ w = ((m + 2 : ℂ) / 2) ^ 2 * ζ w ^ m * deriv ζ w ^ 2 := by
    intro z₀
    by_cases h : q z₀ (chartAt ℂ z₀ z₀) = 0
    · obtain ⟨m, ζ, W, h1⟩ := s26v_b_zero_structure hq hne h
      exact ⟨m, ζ, W, fun _ => h1⟩
    · exact ⟨0, 0, ∅, fun h' => absurd h' h⟩
  choose m ζ W hmζW using hstr
  set P : S₀ → ℂ → (ℝ → S₀) → ℝ → Prop := fun z₀ ϑ c b =>
    0 < b ∧ (∀ t ∈ Ioo (0 : ℝ) b, s26v_IsTrajAt q c t) ∧
      ∃ ε > 0, ε ≤ b ∧ ∀ t ∈ Ioo (b - ε) b, c t ∈ (chartAt ℂ z₀).source ∧ chartAt ℂ z₀ (c t) ∈ W z₀ ∧
        ζ z₀ (chartAt ℂ z₀ (c t)) = ϑ * (((b - t) ^ ((2 : ℝ) / (m z₀ + 2)) : ℝ) : ℂ) with hP
  have hsel : ∀ (z₀ : S₀) (ϑ : ℂ) (r : ℚ), ∃ (c : ℝ → S₀) (b : ℝ),
      (∃ c' b', P z₀ ϑ c' b' ∧ (r : ℝ) < b') → P z₀ ϑ c b ∧ (r : ℝ) < b := by
    intro z₀ ϑ r
    by_cases h : ∃ c' b', P z₀ ϑ c' b' ∧ (r : ℝ) < b'
    · obtain ⟨c', b', h'⟩ := h
      exact ⟨c', b', fun _ => h'⟩
    · exact ⟨fun _ => z₀, 0, fun h' => absurd h' h⟩
  choose C Bd hCB using hsel
  set S : S₀ → ℂ → ℚ → Set S₀ := fun z₀ ϑ r =>
    {p | (∃ c' b', P z₀ ϑ c' b' ∧ (r : ℝ) < b') ∧ p ∈ C z₀ ϑ r '' Ioo 0 (Bd z₀ ϑ r)} with hS
  have hSnull : ∀ z₀ ϑ r, volume (chartAt ℂ x '' (S z₀ ϑ r ∩ (chartAt ℂ x).source)) = 0 := by
    intro z₀ ϑ r
    by_cases h : ∃ c' b', P z₀ ϑ c' b' ∧ (r : ℝ) < b'
    · refine measure_mono_null ?_ (s26v_b_image_null hq (hCB z₀ ϑ r h).1.2.1 x)
      exact image_mono (inter_subset_inter_left _ fun p hp => hp.2)
    · have he : S z₀ ϑ r = ∅ := by
        ext p
        simp only [hS, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h' => absurd h' h
      simp [he]
  have hcov : {p | ∃ (c : ℝ → S₀) (b : ℝ), s26v_IsCritArc q c b ∧ p ∈ c '' Ioo 0 b} ⊆
      ⋃ z₀ ∈ {z₀ : S₀ | q z₀ (chartAt ℂ z₀ z₀) = 0}, ⋃ ϑ ∈ {ϑ : ℂ | ϑ ^ (m z₀ + 2) = 1},
        ⋃ r : ℚ, S z₀ ϑ r := by
    rintro p ⟨c, b, ⟨hb, hc, z₀, hz₀, hlim⟩, t, ht, rfl⟩
    obtain ⟨hm, hWo, hw₀, -, hinj, hζ0, hζ⟩ := hmζW z₀ hz₀
    obtain ⟨ϑ, hϑ, ε, hε, hεb, htail⟩ := s26v_b_tail hq hm hWo hw₀ hζ0 hζ hb hc hlim
    have hPc : P z₀ ϑ c b := ⟨hb, hc, ε, hε, hεb, htail⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show b - t < b by linarith [ht.1])
    have hex : ∃ c' b', P z₀ ϑ c' b' ∧ (r : ℝ) < b' := ⟨c, b, hPc, hr2⟩
    obtain ⟨⟨hB₀, hC₀, ε', hε', hε'b, htail'⟩, hrB⟩ := hCB z₀ ϑ r hex
    refine mem_iUnion₂.2 ⟨z₀, hz₀, mem_iUnion₂.2 ⟨ϑ, hϑ, mem_iUnion.2 ⟨r, hex, ?_⟩⟩⟩
    have hrev : ∀ (c₁ : ℝ → S₀) (b₁ : ℝ), (∀ t ∈ Ioo (0 : ℝ) b₁, s26v_IsTrajAt q c₁ t) →
        ∀ s ∈ Ioo (0 : ℝ) b₁, s26v_IsTrajAt q (fun s => c₁ (-s + b₁)) s := by
      intro c₁ b₁ hc₁ s hs
      have h1 : -s + b₁ ∈ Ioo (0 : ℝ) b₁ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact s26v_trajAt_neg (s26v_trajAt_shift (hc₁ _ h1))
    have hmin1 : min b (Bd z₀ ϑ r) ≤ b := min_le_left _ _
    have hmin2 : min b (Bd z₀ ϑ r) ≤ Bd z₀ ϑ r := min_le_right _ _
    have hagree : ∀ s ∈ Ioo (0 : ℝ) (min ε ε'), c (-s + b) = C z₀ ϑ r (-s + Bd z₀ ϑ r) := by
      intro s hs
      have hs1 : s < ε := lt_of_lt_of_le hs.2 (min_le_left _ _)
      have hs2 : s < ε' := lt_of_lt_of_le hs.2 (min_le_right _ _)
      obtain ⟨h1s, h1W, h1ζ⟩ := htail (-s + b) ⟨by linarith, by linarith [hs.1]⟩
      obtain ⟨h2s, h2W, h2ζ⟩ := htail' (-s + Bd z₀ ϑ r) ⟨by linarith, by linarith [hs.1]⟩
      have e1 : b - (-s + b) = s := by ring
      have e2 : Bd z₀ ϑ r - (-s + Bd z₀ ϑ r) = s := by ring
      rw [e1] at h1ζ
      rw [e2] at h2ζ
      have h3 := hinj h1W h2W (h1ζ.trans h2ζ.symm)
      exact (chartAt ℂ z₀).injOn h1s h2s h3
    have ht₀ : min ε ε' / 2 ∈ Ioo (0 : ℝ) (min b (Bd z₀ ϑ r)) := by
      have hpos : 0 < min ε ε' := lt_min hε hε'
      refine ⟨by linarith, ?_⟩
      have : min ε ε' ≤ min b (Bd z₀ ϑ r) := min_le_min hεb hε'b
      linarith
    have hev : (fun s => c (-s + b)) =ᶠ[𝓝 (min ε ε' / 2)] fun s => C z₀ ϑ r (-s + Bd z₀ ϑ r) := by
      have hpos : 0 < min ε ε' := lt_min hε hε'
      filter_upwards [isOpen_Ioo.mem_nhds (show min ε ε' / 2 ∈ Ioo (0 : ℝ) (min ε ε') from
        ⟨by linarith, by linarith⟩)] with s hs
      exact hagree s hs
    have huniq := s26v_b_traj_eqOn hq isOpen_Ioo (convex_Ioo _ _)
      (fun s hs => hrev c b hc s ⟨hs.1, lt_of_lt_of_le hs.2 hmin1⟩)
      (fun s hs => hrev (C z₀ ϑ r) (Bd z₀ ϑ r) hC₀ s ⟨hs.1, lt_of_lt_of_le hs.2 hmin2⟩) ht₀ hev
    have hsJ : b - t ∈ Ioo (0 : ℝ) (min b (Bd z₀ ϑ r)) :=
      ⟨by linarith [ht.2], lt_min (by linarith [ht.1]) (by linarith)⟩
    have hct := huniq (b - t) hsJ
    rw [show -(b - t) + b = t by ring] at hct
    exact ⟨-(b - t) + Bd z₀ ϑ r, ⟨by linarith, by linarith [ht.2]⟩, hct.symm⟩
  refine measure_mono_null (image_mono (inter_subset_inter_left _ hcov)) ?_
  have hsub : chartAt ℂ x '' ((⋃ z₀ ∈ {z₀ : S₀ | q z₀ (chartAt ℂ z₀ z₀) = 0},
      ⋃ ϑ ∈ {ϑ : ℂ | ϑ ^ (m z₀ + 2) = 1}, ⋃ r : ℚ, S z₀ ϑ r) ∩ (chartAt ℂ x).source) ⊆
      ⋃ z₀ ∈ {z₀ : S₀ | q z₀ (chartAt ℂ z₀ z₀) = 0}, ⋃ ϑ ∈ {ϑ : ℂ | ϑ ^ (m z₀ + 2) = 1},
        ⋃ r : ℚ, chartAt ℂ x '' (S z₀ ϑ r ∩ (chartAt ℂ x).source) := by
    rintro _ ⟨p, ⟨hp, hps⟩, rfl⟩
    simp only [mem_iUnion] at hp ⊢
    obtain ⟨z₀, hz₀, ϑ, hϑ, r, hr⟩ := hp
    exact ⟨z₀, hz₀, ϑ, hϑ, r, p, ⟨hr, hps⟩, rfl⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hZc).2 fun z₀ hz₀ => ?_)
  have hfin := (s26v_b_roots_finite (n := m z₀ + 2) (by omega)).countable
  exact (measure_biUnion_null_iff hfin).2 fun ϑ _ => measure_iUnion_null fun r => hSnull z₀ ϑ r

/-- **T1 + T2, proved:** the critical set is null in every chart: its regular points lie on critical arcs ([V3]), which
are null ([V4]), and its other points are zeros of `q`, countable in every chart (`s26u_zeros_countable`). -/
theorem s26v_E_null [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (x : S₀) :
    volume (chartAt ℂ x '' (s26v_E q ∩ (chartAt ℂ x).source)) = 0 := by
  have hZ : volume {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0} = 0 :=
    (s26u_zeros_countable hq hne x).measure_zero volume
  refine measure_mono_null ?_ (measure_union_null hZ (s26v_critArc_null hq hne x))
  rintro _ ⟨p, ⟨hpE, hpx⟩, rfl⟩
  have hzt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
  by_cases hreg : q p (chartAt ℂ p p) = 0
  · left
    refine ⟨hzt, ?_⟩
    by_contra h0
    have h1 := (s26u_isRegularPoint_iff hq x hzt).2 h0
    rw [(chartAt ℂ x).left_inv hpx] at h1
    exact h1 hreg
  · right
    obtain ⟨c, b, hc, hpc⟩ := s26v_mem_critArc hq hne hpE hreg
    exact ⟨p, ⟨⟨c, b, hc, hpc⟩, hpx⟩, rfl⟩

/-! #### T3: the horizontal flow preserves `dA_q` -/

/-! #### Prover A helpers: natural maps (local inverses of natural parameters) -/

/-- `G : ℂ → S₀` is a **natural map** at `u` (a local inverse of a natural parameter, `G*q = du²`): `G` is continuous
at `u` and, in the chart at `G u`, has a complex derivative `v` at `u` with `q v² = 1`. -/
def s26v_a_IsNatAt (q : S₀ → ℂ → ℂ) (G : ℂ → S₀) (u : ℂ) : Prop :=
  ContinuousAt G u ∧ ∃ v : ℂ, HasDerivAt (fun u' => chartAt ℂ (G u) (G u')) v u ∧
    q (G u) (chartAt ℂ (G u) (G u)) * v ^ 2 = 1

/-- A natural map is natural in every chart whose source contains the value (holomorphic chart transitions and the
transformation law). -/
theorem s26v_a_natAt_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {G : ℂ → S₀}
    {u : ℂ} (hG : s26v_a_IsNatAt q G u) (x : S₀) (hx : G u ∈ (chartAt ℂ x).source) :
    ∃ v : ℂ, HasDerivAt (fun u' => chartAt ℂ x (G u')) v u ∧ q x (chartAt ℂ x (G u)) * v ^ 2 = 1 := by
  obtain ⟨hcont, v, hv, hqv⟩ := hG
  have hyy : G u ∈ (chartAt ℂ (G u)).source := mem_chart_source ℂ (G u)
  have hw : chartAt ℂ (G u) (G u) ∈ (chartAt ℂ (G u)).target := (chartAt ℂ (G u)).map_source hyy
  have hws : (chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G u)) = G u := (chartAt ℂ (G u)).left_inv hyy
  obtain ⟨hT, -⟩ := s23_transition x (G u) hw (by rw [hws]; exact hx)
  have hlaw := s26u_law hq (G u) x hw (by rw [hws]; exact hx)
  have hTw : chartTransition x (G u) (chartAt ℂ (G u) (G u)) = chartAt ℂ x (G u) := by
    show chartAt ℂ x ((chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G u))) = _
    rw [hws]
  have hev : (fun u' => chartAt ℂ x (G u')) =ᶠ[𝓝 u]
      chartTransition x (G u) ∘ fun u' => chartAt ℂ (G u) (G u') := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (G u)).open_source.mem_nhds hyy)] with s hs
    show chartAt ℂ x (G s) = chartAt ℂ x ((chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G s)))
    rw [(chartAt ℂ (G u)).left_inv hs]
  refine ⟨deriv (chartTransition x (G u)) (chartAt ℂ (G u) (G u)) * v,
    (hT.hasDerivAt.comp u hv).congr_of_eventuallyEq hev, ?_⟩
  rw [← hTw]
  rw [hlaw] at hqv
  linear_combination hqv

/-- `s26v_a_IsNatAt` depends only on the germ of the map. -/
theorem s26v_a_natAt_congr {q : S₀ → ℂ → ℂ} {G G' : ℂ → S₀} {u : ℂ} (hG : s26v_a_IsNatAt q G u)
    (h : G =ᶠ[𝓝 u] G') : s26v_a_IsNatAt q G' u := by
  obtain ⟨hcont, v, hv, hqv⟩ := hG
  have hu : G u = G' u := h.eq_of_nhds
  refine ⟨hcont.congr h, v, ?_, ?_⟩
  · rw [← hu]
    refine hv.congr_of_eventuallyEq ?_
    filter_upwards [h] with s hs
    rw [hs]
  · rw [← hu]
    exact hqv

/-- A natural map is complex differentiable in any chart at the points where it is natural. -/
theorem s26v_a_natAt_differentiableAt [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {G : ℂ → S₀} {u : ℂ} (hG : s26v_a_IsNatAt q G u) (x : S₀) (hx : G u ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun u' => chartAt ℂ x (G u')) u :=
  (s26v_a_natAt_chart hq hG x hx).choose_spec.1.differentiableAt

/-- Along horizontal lines, a natural map is a unit-speed horizontal trajectory: if `G` is natural at `w + σ s`
(`σ = ±1`), then `s' ↦ G (w + σ s')` is a unit-speed horizontal trajectory at `s`. -/
theorem s26v_a_trajAt_of_natAt {q : S₀ → ℂ → ℂ} {G : ℂ → S₀} {w : ℂ} {σ s : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hG : s26v_a_IsNatAt q G (w + (σ : ℂ) * (s : ℂ))) :
    s26v_IsTrajAt q (fun s' : ℝ => G (w + (σ : ℂ) * (s' : ℂ))) s := by
  obtain ⟨hcont, v, hv, hqv⟩ := hG
  have hl : HasDerivAt (fun s' : ℝ => w + (σ : ℂ) * (s' : ℂ)) (σ : ℂ) s := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (σ : ℂ)).const_add w
    simpa using h
  have hcomp := HasDerivAt.comp s hv hl
  refine ⟨ContinuousAt.comp (g := G) (f := fun s' : ℝ => w + (σ : ℂ) * (s' : ℂ)) hcont hl.continuousAt,
    v * σ, hcomp, ?_⟩
  have hσ2 : ((σ : ℂ)) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [mul_pow, hσ2, mul_one]
  exact hqv

/-- Affine reparametrizations `u ↦ G (a + σ u)`, `σ² = 1`, of natural maps are natural. -/
theorem s26v_a_natAt_affine {q : S₀ → ℂ → ℂ} {G : ℂ → S₀} {a σ u : ℂ} (hσ : σ ^ 2 = 1)
    (hG : s26v_a_IsNatAt q G (a + σ * u)) : s26v_a_IsNatAt q (fun u' => G (a + σ * u')) u := by
  obtain ⟨hcont, v, hv, hqv⟩ := hG
  have hl : HasDerivAt (fun u' : ℂ => a + σ * u') σ u := by
    simpa using ((hasDerivAt_id u).const_mul σ).const_add a
  have hcomp := HasDerivAt.comp u hv hl
  refine ⟨ContinuousAt.comp (g := G) (f := fun u' : ℂ => a + σ * u') hcont hl.continuousAt, v * σ, hcomp, ?_⟩
  rw [mul_pow, hσ, mul_one]
  exact hqv

/-- The inverse of a flow-box parameter is natural: for `u ∈ Z(B)`, `(Z|_B)⁻¹` is natural at `u` (its chart expression
is the local inverse of the holomorphic `Z ∘ φ⁻¹`, of derivative `1/D`, and `q (1/D)² = 1`). -/
theorem s26v_a_natAt_flowBox_inv [IsManifold 𝓘(ℂ) ω S₀] [Nonempty S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z) {u : ℂ} (hu : u ∈ Z '' B) :
    s26v_a_IsNatAt q (Function.invFunOn Z B) u := by
  classical
  set H := Function.invFunOn Z B with hH
  have hHB : ∀ u' ∈ Z '' B, H u' ∈ B := fun u' hu' => Function.invFunOn_mem hu'
  have hHZ : ∀ u' ∈ Z '' B, Z (H u') = u' := fun u' hu' => Function.invFunOn_eq hu'
  set y' := H u with hy'
  set e' := chartAt ℂ y' with he'
  have hy'B : y' ∈ B := hHB u hu
  have hyy : y' ∈ e'.source := mem_chart_source ℂ y'
  have hw₀ : e' y' ∈ e'.target := e'.map_source hyy
  have hsy : e'.symm (e' y') = y' := e'.left_inv hyy
  obtain ⟨D, hDs, hD0, hD2⟩ := s26v_a_flowBox_strict hq hB y' hw₀ (by rw [hsy]; exact hy'B)
  set G : ℂ → ℂ := fun v => Z (e'.symm v) with hG
  set Ginv := hDs.localInverse G D (e' y') hD0 with hGinv
  have hGinvd : HasStrictDerivAt Ginv D⁻¹ (G (e' y')) := hDs.to_localInverse hD0
  have hright : ∀ᶠ u' in 𝓝 (G (e' y')), G (Ginv u') = u' := hDs.eventually_right_inverse hD0
  have hleft : ∀ᶠ w in 𝓝 (e' y'), Ginv (G w) = w := hDs.eventually_left_inverse hD0
  have hGw : G (e' y') = u := by
    show Z (e'.symm (e' y')) = u
    rw [hsy]
    exact hHZ u hu
  have hGinvw : Ginv (G (e' y')) = e' y' := hleft.self_of_nhds
  have hO : e'.target ∩ e'.symm ⁻¹' B ∈ 𝓝 (e' y') :=
    (e'.isOpen_inter_preimage_symm hB.1).mem_nhds ⟨hw₀, by rw [mem_preimage, hsy]; exact hy'B⟩
  have hGinvc : Tendsto Ginv (𝓝 u) (𝓝 (e' y')) := by
    have h := hGinvd.hasDerivAt.continuousAt.tendsto
    rwa [hGinvw, hGw] at h
  have hZB : Z '' B ∈ 𝓝 u := hB.2.2.2.1.mem_nhds hu
  have hev : ∀ᶠ u' in 𝓝 u, H u' = e'.symm (Ginv u') ∧ Ginv u' ∈ e'.target := by
    rw [hGw] at hright
    filter_upwards [hZB, hGinvc.eventually hO, hright] with u' hu' h1 h2
    refine ⟨hB.2.2.1 (hHB u' hu') h1.2 ?_, h1.1⟩
    rw [hHZ u' hu']
    exact h2.symm
  have hcont : ContinuousAt H u := by
    have h2 : ContinuousAt Ginv u := by
      rw [← hGw]
      exact hGinvd.hasDerivAt.continuousAt
    have h3 : ContinuousAt e'.symm (Ginv u) := by
      rw [← hGw, hGinvw]
      exact e'.continuousAt_symm hw₀
    exact (ContinuousAt.comp (g := e'.symm) (f := Ginv) h3 h2).congr (hev.mono fun r hr => hr.1.symm)
  have hderiv : HasDerivAt (fun u' => e' (H u')) D⁻¹ u := by
    have h2 : HasDerivAt Ginv D⁻¹ u := by
      rw [← hGw]
      exact hGinvd.hasDerivAt
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hev] with r hr
    show e' (H r) = Ginv r
    rw [hr.1]
    exact e'.right_inv hr.2
  refine ⟨hcont, D⁻¹, hderiv, ?_⟩
  show q y' (e' y') * (D⁻¹) ^ 2 = 1
  rw [← hD2, inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hD0)

/-- **Identity theorem for natural maps.**  Two maps natural at every point of an open preconnected `O ⊆ ℂ` that agree
at points accumulating at a point of `O` agree on `O` (in the chart at a common value both are holomorphic; the set of
points near which they agree is open and closed in `O`). -/
theorem s26v_a_natAt_eqOn [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {G₁ G₂ : ℂ → S₀} {O : Set ℂ} (hOo : IsOpen O) (hO : IsPreconnected O)
    (h₁ : ∀ u ∈ O, s26v_a_IsNatAt q G₁ u) (h₂ : ∀ u ∈ O, s26v_a_IsNatAt q G₂ u) {u₀ : ℂ} (hu₀ : u₀ ∈ O)
    (hfr : ∃ᶠ u in 𝓝[≠] u₀, G₁ u = G₂ u) : EqOn G₁ G₂ O := by
  have hloc : ∀ u ∈ O, (∃ᶠ u' in 𝓝[≠] u, G₁ u' = G₂ u') → G₁ =ᶠ[𝓝 u] G₂ := by
    intro u hu hf
    have heq : G₁ u = G₂ u := tendsto_nhds_unique_of_frequently_eq
      ((h₁ u hu).1.tendsto.mono_left nhdsWithin_le_nhds) ((h₂ u hu).1.tendsto.mono_left nhdsWithin_le_nhds) hf
    set x := G₁ u with hx
    have hs1 : ∀ᶠ u' in 𝓝 u, G₁ u' ∈ (chartAt ℂ x).source :=
      (h₁ u hu).1.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
    have hs2 : ∀ᶠ u' in 𝓝 u, G₂ u' ∈ (chartAt ℂ x).source :=
      (h₂ u hu).1.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds (by rw [← heq]; exact mem_chart_source ℂ x))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hs1.and (hs2.and (hOo.mem_nhds hu)))
    have hd1 : DifferentiableOn ℂ (fun u' => chartAt ℂ x (G₁ u')) (ball u r) := fun u' hu' =>
      (s26v_a_natAt_differentiableAt hq (h₁ u' (hball u' hu').2.2) x (hball u' hu').1).differentiableWithinAt
    have hd2 : DifferentiableOn ℂ (fun u' => chartAt ℂ x (G₂ u')) (ball u r) := fun u' hu' =>
      (s26v_a_natAt_differentiableAt hq (h₂ u' (hball u' hu').2.2) x (hball u' hu').2.1).differentiableWithinAt
    have heqOn := (hd1.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (hd2.analyticOnNhd isOpen_ball) (convex_ball u r).isPreconnected (mem_ball_self hr)
      (hf.mono fun u' h => by simp only [h])
    filter_upwards [ball_mem_nhds u hr] with u' hu'
    exact (chartAt ℂ x).injOn (hball u' hu').1 (hball u' hu').2.1 (heqOn hu')
  set A := {u | G₁ =ᶠ[𝓝 u] G₂} with hA
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hsub : O ⊆ A := by
    refine hO.subset_of_closure_inter_subset hAo ⟨u₀, hu₀, hloc u₀ hu₀ hfr⟩ ?_
    rintro u ⟨hucl, huO⟩
    by_cases huA : u ∈ A
    · exact huA
    · have hcl : u ∈ closure (A \ {u}) := by rwa [sdiff_singleton_eq_self huA]
      have hfr' := mem_closure_ne_iff_frequently_within.1 hcl
      exact hloc u huO (hfr'.mono fun u' hu' => hu'.eq_of_nhds)
  exact fun u hu => (hsub hu).eq_of_nhds

/-- A map natural on a disc around `u` is injective on a smaller disc around `u` (its chart expression has a nonzero
derivative, `s26u_exists_open_injOn`). -/
theorem s26v_a_natAt_injOn [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {G : ℂ → S₀}
    {u : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀) (hG : ∀ u' ∈ ball u r₀, s26v_a_IsNatAt q G u') :
    ∃ r > 0, InjOn G (ball u r) := by
  set x := G u with hx
  have hGu := hG u (mem_ball_self hr₀)
  have hs : ∀ᶠ u' in 𝓝 u, G u' ∈ (chartAt ℂ x).source :=
    hGu.1.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (ball_mem_nhds u hr₀))
  have hd : DifferentiableOn ℂ (fun u' => chartAt ℂ x (G u')) (ball u r₁) := fun u' hu' =>
    (s26v_a_natAt_differentiableAt hq (hG u' (hball u' hu').2) x (hball u' hu').1).differentiableWithinAt
  have han : AnalyticAt ℂ (fun u' => chartAt ℂ x (G u')) u := hd.analyticAt (ball_mem_nhds u hr₁)
  obtain ⟨v, hv, hqv⟩ := s26v_a_natAt_chart hq hGu x (mem_chart_source ℂ x)
  have hv0 : deriv (fun u' => chartAt ℂ x (G u')) u ≠ 0 := by
    rw [hv.deriv]
    intro h
    rw [h] at hqv
    simp at hqv
  obtain ⟨V, hVo, huV, -, hVinj⟩ := s26u_exists_open_injOn han hv0
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo u huV
  refine ⟨min r r₁, lt_min hr hr₁, fun u₁ hu₁ u₂ hu₂ h => ?_⟩
  exact hVinj (hrV (ball_subset_ball (min_le_left _ _) hu₁)) (hrV (ball_subset_ball (min_le_left _ _) hu₂))
    (by simp only [h])

/-- A map natural on an open set `O` maps `O` onto an open set (in the chart at a value the chart expression has a
nonzero strict derivative, so it maps neighbourhoods onto neighbourhoods). -/
theorem s26v_a_natAt_isOpen_image [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {G : ℂ → S₀} {O : Set ℂ} (hOo : IsOpen O) (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u) : IsOpen (G '' O) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, rfl⟩
  set x := G u with hx
  set g : ℂ → ℂ := fun u' => chartAt ℂ x (G u') with hg
  have hs : ∀ᶠ u' in 𝓝 u, G u' ∈ (chartAt ℂ x).source :=
    (hG u hu).1.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (hOo.mem_nhds hu))
  have hd : DifferentiableOn ℂ g (ball u r₁) := fun u' hu' =>
    (s26v_a_natAt_differentiableAt hq (hG u' (hball u' hu').2) x (hball u' hu').1).differentiableWithinAt
  have hstrict : HasStrictDerivAt g (deriv g u) u := (hd.analyticAt (ball_mem_nhds u hr₁)).hasStrictDerivAt
  obtain ⟨v, hv, hqv⟩ := s26v_a_natAt_chart hq (hG u hu) x (mem_chart_source ℂ x)
  have hv0 : deriv g u ≠ 0 := by
    rw [hv.deriv]
    intro h
    rw [h] at hqv
    simp at hqv
  have himg : g '' ball u r₁ ∈ 𝓝 (g u) := by
    rw [← hstrict.map_nhds_eq hv0]
    exact image_mem_map (ball_mem_nhds u hr₁)
  have hN : (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' (g '' ball u r₁) ∈ 𝓝 (G u) :=
    inter_mem ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
      (((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds himg)
  refine mem_of_superset hN ?_
  rintro p ⟨hps, u', hu', hpu⟩
  exact ⟨u', (hball u' hu').2, (chartAt ℂ x).injOn (hball u' hu').1 hps hpu⟩

/-! #### Prover A helpers: developments of trajectories -/

/-- A **development** of the curve `c` over `[a, b]`, of width `ρ`: a map `G : ℂ → S₀`, natural on the open rectangle
`(a - ρ, b + ρ) × i(-ρ, ρ)` and equal to `c` at its real points. -/
def s26v_a_IsDev (q : S₀ → ℂ → ℂ) (c : ℝ → S₀) (a b ρ : ℝ) (G : ℂ → S₀) : Prop :=
  (∀ u : ℂ, u.re ∈ Ioo (a - ρ) (b + ρ) → u.im ∈ Ioo (-ρ) ρ → s26v_a_IsNatAt q G u) ∧
    ∀ s : ℝ, s ∈ Ioo (a - ρ) (b + ρ) → G s = c s

/-- The open rectangle of a development is convex. -/
theorem s26v_a_convex_rect (a b ρ : ℝ) :
    Convex ℝ {u : ℂ | u.re ∈ Ioo (a - ρ) (b + ρ) ∧ u.im ∈ Ioo (-ρ) ρ} := by
  have h1 : Convex ℝ (Complex.reLm ⁻¹' Ioo (a - ρ) (b + ρ)) := (convex_Ioo _ _).linear_preimage _
  have h2 : Convex ℝ (Complex.imLm ⁻¹' Ioo (-ρ) ρ) := (convex_Ioo _ _).linear_preimage _
  exact h1.inter h2

/-- The open rectangle of a development is open. -/
theorem s26v_a_isOpen_rect (a b ρ : ℝ) :
    IsOpen {u : ℂ | u.re ∈ Ioo (a - ρ) (b + ρ) ∧ u.im ∈ Ioo (-ρ) ρ} :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

/-- **Development in a flow box.**  Near a time `s₀` near which `c` is a unit-speed horizontal trajectory, the inverse
of a flow-box parameter at `c s₀`, composed with `u ↦ Z(c s₀) + σ (u - s₀)`, is natural on a disc around `s₀` and
equals `c` at its real points. -/
theorem s26v_a_dev_box [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : ℝ → S₀}
    {s₀ : ℝ} (hc : ∀ᶠ s in 𝓝 s₀, s26v_IsTrajAt q c s) :
    ∃ r > 0, ∃ G : ℂ → S₀, (∀ u ∈ ball (s₀ : ℂ) r, s26v_a_IsNatAt q G u) ∧
      ∀ s : ℝ, |s - s₀| < r → G s = c s := by
  classical
  have : Nonempty S₀ := ⟨c s₀⟩
  obtain ⟨B, Z, hpB, -, hB⟩ := s26v_exists_flowBox hq (s26v_a_trajAt_regular hc.self_of_nhds)
    (univ_mem : univ ∈ 𝓝 (c s₀))
  have hB' : ∀ᶠ s in 𝓝 s₀, c s ∈ B := hc.self_of_nhds.1.preimage_mem_nhds (hB.1.mem_nhds hpB)
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 (hc.and hB')
  have hint : ∀ s ∈ Ioo (s₀ - ε) (s₀ + ε), s26v_IsTrajAt q c s ∧ c s ∈ B := fun s hs =>
    hεs (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  obtain ⟨σ, hσ, hline⟩ := s26v_a_line_of_box hB hint (show s₀ ∈ Ioo (s₀ - ε) (s₀ + ε) from
    ⟨by linarith, by linarith⟩)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hB.2.2.2.1 (Z (c s₀)) ⟨c s₀, hpB, rfl⟩
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨min ε r₀, lt_min hε hr₀, fun u => Function.invFunOn Z B (Z (c s₀) + (σ : ℂ) * (u - s₀)), ?_, ?_⟩
  · intro u hu
    have hmem : Z (c s₀) - (σ : ℂ) * s₀ + (σ : ℂ) * u ∈ Z '' B := by
      refine hball ?_
      rw [mem_ball, dist_eq_norm, show Z (c s₀) - (σ : ℂ) * s₀ + (σ : ℂ) * u - Z (c s₀) =
        (σ : ℂ) * (u - s₀) by ring, norm_mul, hσn, one_mul]
      exact lt_of_lt_of_le (mem_ball_iff_norm.1 hu) (min_le_right _ _)
    have h := s26v_a_natAt_affine (G := Function.invFunOn Z B) (a := Z (c s₀) - (σ : ℂ) * s₀) (u := u) hσ2
      (s26v_a_natAt_flowBox_inv hq hB hmem)
    have heq : (fun u' => Function.invFunOn Z B (Z (c s₀) - (σ : ℂ) * s₀ + (σ : ℂ) * u')) =
        (fun u' => Function.invFunOn Z B (Z (c s₀) + (σ : ℂ) * (u' - s₀))) := by
      funext u'
      congr 1
      ring
    rwa [heq] at h
  · intro s hs
    have hs' : s ∈ Ioo (s₀ - ε) (s₀ + ε) := by
      have h := lt_of_lt_of_le hs (min_le_left _ _)
      rw [abs_lt] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    show Function.invFunOn Z B (Z (c s₀) + (σ : ℂ) * ((s : ℂ) - s₀)) = c s
    have h := hline s hs'
    rw [show Z (c s₀) + (σ : ℂ) * ((s : ℂ) - s₀) = Z (c s) by rw [h]; push_cast; ring]
    exact hB.2.2.1.leftInvOn_invFunOn (hint s hs').2

/-- Developments shrink: a development over `[a, b]` of width `ρ` is one over `[a, b']`, `b' ≤ b + ρ/2`, of width
`ρ/2`. -/
theorem s26v_a_dev_mono {q : S₀ → ℂ → ℂ} {c : ℝ → S₀} {a b ρ : ℝ} {G : ℂ → S₀} (h : s26v_a_IsDev q c a b ρ G)
    (hρ : 0 < ρ) {b' : ℝ} (hb' : b' ≤ b + ρ / 2) : s26v_a_IsDev q c a b' (ρ / 2) G := by
  refine ⟨fun u hre him => h.1 u ⟨by linarith [hre.1], by linarith [hre.2]⟩ ⟨by linarith [him.1], by linarith [him.2]⟩,
    fun s hs => h.2 s ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩

/-- **The development step.**  At a time `b''` near which `c` is a unit-speed horizontal trajectory there is `r > 0`
such that any development over `[a, b']`, `b'' - r < b' ≤ b''`, yields one over `[a, b'']`: glue it with a flow-box
development at `b''`; the two agree near `b'` by the identity theorem (they agree with `c` at real points). -/
theorem s26v_a_dev_step [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : ℝ → S₀} {b'' : ℝ} (hc : ∀ᶠ s in 𝓝 b'', s26v_IsTrajAt q c s) :
    ∃ r > 0, ∀ (a b' ρ₁ : ℝ) (G₁ : ℂ → S₀), a ≤ b' → b' ≤ b'' → b'' - b' < r → 0 < ρ₁ →
      s26v_a_IsDev q c a b' ρ₁ G₁ → ∃ ρ > 0, ∃ G : ℂ → S₀, s26v_a_IsDev q c a b'' ρ G := by
  classical
  obtain ⟨R, hR, G₂, hG₂, hG₂c⟩ := s26v_a_dev_box hq hc
  refine ⟨R / 2, half_pos hR, fun a b' ρ₁ G₁ hab' hb'b hdist hρ₁ hdev => ?_⟩
  set O : Set ℂ := {u : ℂ | u.re ∈ Ioo (a - ρ₁) (b' + ρ₁) ∧ u.im ∈ Ioo (-ρ₁) ρ₁} ∩ ball (b'' : ℂ) R with hO
  have hOo : IsOpen O := (s26v_a_isOpen_rect a b' ρ₁).inter isOpen_ball
  have hOc : IsPreconnected O := ((s26v_a_convex_rect a b' ρ₁).inter (convex_ball _ _)).isPreconnected
  have hdb : dist (b' : ℂ) (b'' : ℂ) < R := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hb'O : (b' : ℂ) ∈ O := ⟨⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩, hdb⟩
  -- the two developments agree on `O`
  have hreal : ∀ᶠ s : ℝ in 𝓝 b', G₁ (s : ℂ) = G₂ (s : ℂ) := by
    have h1 : Ioo (a - ρ₁) (b' + ρ₁) ∈ 𝓝 b' := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have h2 : {s : ℝ | |s - b''| < R} ∈ 𝓝 b' := by
      refine (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds ?_
      show |b' - b''| < R
      rw [abs_lt]
      constructor <;> linarith
    filter_upwards [h1, h2] with s hs1 hs2
    rw [hdev.2 s hs1, hG₂c s hs2]
  have hfr : ∃ᶠ u in 𝓝[≠] (b' : ℂ), G₁ u = G₂ u := by
    have hT : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] b') (𝓝[≠] (b' : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun h => hs (Complex.ofReal_injective h)
    exact hT.frequently (hreal.filter_mono nhdsWithin_le_nhds).frequently
  have hEq : EqOn G₁ G₂ O := s26v_a_natAt_eqOn hq hOo hOc (fun u hu => hdev.1 u hu.1.1 hu.1.2)
    (fun u hu => hG₂ u hu.2) hb'O hfr
  -- the glued development
  set ρ := min ρ₁ (R / 4) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ (by linarith)
  have hρ1 : ρ ≤ ρ₁ := min_le_left _ _
  have hρ2 : ρ ≤ R / 4 := min_le_right _ _
  set G : ℂ → S₀ := fun u => if u.re ≤ b' then G₁ u else G₂ u with hGdef
  have hball_of : ∀ u : ℂ, u.re ∈ Ioo (b'' - R / 2) (b'' + ρ) → u.im ∈ Ioo (-ρ) ρ → u ∈ ball (b'' : ℂ) R := by
    intro u hre him
    rw [mem_ball, dist_eq_norm]
    have h1 := Complex.norm_le_abs_re_add_abs_im (u - b'')
    have h2 : |(u - (b'' : ℂ)).re| < R / 2 := by
      rw [Complex.sub_re, Complex.ofReal_re, abs_lt]
      constructor <;> linarith [hre.1, hre.2]
    have h3 : |(u - (b'' : ℂ)).im| < R / 4 := by
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_lt]
      constructor <;> linarith [him.1, him.2]
    linarith
  refine ⟨ρ, hρ0, G, fun u hre him => ?_, fun s hs => ?_⟩
  · rcases lt_trichotomy u.re b' with hlt | heq | hgt
    · refine s26v_a_natAt_congr (hdev.1 u ⟨by linarith [hre.1], by linarith⟩
        ⟨by linarith [him.1], by linarith [him.2]⟩) ?_
      have hopen : IsOpen {u' : ℂ | u'.re < b'} := isOpen_lt Complex.continuous_re continuous_const
      filter_upwards [hopen.mem_nhds hlt] with u' hu'
      have hle : u'.re ≤ b' := le_of_lt hu'
      simp only [hGdef, hle, ↓reduceIte]
    · have huO : u ∈ O := by
        refine ⟨⟨⟨by linarith [hre.1], by linarith⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩,
          hball_of u ⟨by linarith, by linarith⟩ him⟩
      refine s26v_a_natAt_congr (hdev.1 u huO.1.1 huO.1.2) ?_
      filter_upwards [hOo.mem_nhds huO] with u' hu'
      by_cases hle : u'.re ≤ b'
      · simp only [hGdef, hle, ↓reduceIte]
      · simp only [hGdef, hle, ↓reduceIte]
        exact hEq hu'
    · refine s26v_a_natAt_congr (hG₂ u (hball_of u ⟨by linarith, hre.2⟩ him)) ?_
      have hopen : IsOpen {u' : ℂ | b' < u'.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hgt] with u' hu'
      have hle : ¬ u'.re ≤ b' := not_le.2 hu'
      simp only [hGdef, hle, ↓reduceIte]
  · by_cases hle : s ≤ b'
    · have hle' : (s : ℂ).re ≤ b' := by simpa using hle
      simp only [hGdef, hle', ↓reduceIte]
      exact hdev.2 s ⟨by linarith [hs.1], by linarith⟩
    · have hle' : ¬ (s : ℂ).re ≤ b' := by simpa using hle
      simp only [hGdef, hle', ↓reduceIte]
      refine hG₂c s ?_
      rw [abs_lt]
      constructor <;> linarith [hs.2, not_le.1 hle]

/-- **Existence of developments.**  A curve that is a unit-speed horizontal trajectory near every time of `[a, b]` has
a development over `[a, b]`: the supremum of the `b'` admitting a development over `[a, b']` is attained (by the
development step) and equals `b`, since developments extend a little beyond their right end. -/
theorem s26v_a_dev_exists [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : ℝ → S₀} {a b : ℝ} (hab : a ≤ b) (hc : ∀ s ∈ Icc a b, ∀ᶠ s' in 𝓝 s, s26v_IsTrajAt q c s') :
    ∃ ρ > 0, ∃ G : ℂ → S₀, s26v_a_IsDev q c a b ρ G := by
  set S : Set ℝ := {b' | b' ∈ Icc a b ∧ ∃ ρ > 0, ∃ G : ℂ → S₀, s26v_a_IsDev q c a b' ρ G} with hS
  have haS : a ∈ S := by
    obtain ⟨r, hr, G, hG, hGc⟩ := s26v_a_dev_box hq (hc a ⟨le_rfl, hab⟩)
    refine ⟨⟨le_rfl, hab⟩, r / 2, half_pos hr, G, fun u hre him => hG u ?_, fun s hs => hGc s ?_⟩
    · rw [mem_ball, dist_eq_norm]
      have h1 := Complex.norm_le_abs_re_add_abs_im (u - a)
      have h2 : |(u - (a : ℂ)).re| < r / 2 := by
        rw [Complex.sub_re, Complex.ofReal_re, abs_lt]
        constructor <;> linarith [hre.1, hre.2]
      have h3 : |(u - (a : ℂ)).im| < r / 2 := by
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_lt]
        constructor <;> linarith [him.1, him.2]
      linarith
    · rw [abs_lt]
      constructor <;> linarith [hs.1, hs.2]
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  have hne : S.Nonempty := ⟨a, haS⟩
  set β := sSup S with hβ
  have haβ : a ≤ β := le_csSup hbdd haS
  have hβb : β ≤ b := csSup_le hne fun x hx => hx.1.2
  -- the supremum is attained
  have hβS : β ∈ S := by
    obtain ⟨r, hr, hstep⟩ := s26v_a_dev_step hq (hc β ⟨haβ, hβb⟩)
    obtain ⟨b', hb'S, hb'⟩ := exists_lt_of_lt_csSup hne (show β - r < β by linarith)
    obtain ⟨ρ₁, hρ₁, G₁, hG₁⟩ := hb'S.2
    exact ⟨⟨haβ, hβb⟩, hstep a b' ρ₁ G₁ hb'S.1.1 (le_csSup hbdd hb'S) (by linarith) hρ₁ hG₁⟩
  -- and equals `b`
  obtain ⟨-, ρ, hρ, G, hG⟩ := hβS
  by_cases hβb' : β = b
  · exact ⟨ρ, hρ, G, hβb' ▸ hG⟩
  · exfalso
    have hlt : β < b := lt_of_le_of_ne hβb hβb'
    set b₂ := min b (β + ρ / 2) with hb₂
    have hb₂S : b₂ ∈ S := ⟨⟨le_min hab (by linarith), min_le_left _ _⟩, ρ / 2, half_pos hρ, G,
      s26v_a_dev_mono hG hρ (min_le_right _ _)⟩
    have h1 := le_csSup hbdd hb₂S
    have h2 : β < b₂ := lt_min hlt (by linarith)
    linarith

/-! #### Prover A helpers: tubes around trajectories off the critical set -/

/-- A **tube** of time `T` at `p₀`, of width `ρ`: a map `G` with `G 0 = p₀`, natural on the strip
`(-T - 2ρ, T + 2ρ) × i(-2ρ, 2ρ)` and injective on every disc `ball s ρ`, `s ∈ [-T, T]`. -/
def s26v_a_IsTube (q : S₀ → ℂ → ℂ) (T : ℝ) (p₀ : S₀) (ρ : ℝ) (G : ℂ → S₀) : Prop :=
  0 < ρ ∧ G 0 = p₀ ∧
    (∀ u : ℂ, u.re ∈ Ioo (-T - 2 * ρ) (T + 2 * ρ) → u.im ∈ Ioo (-(2 * ρ)) (2 * ρ) → s26v_a_IsNatAt q G u) ∧
    ∀ s ∈ Icc (-T) T, InjOn G (ball (s : ℂ) ρ)

/-- Every point of a bi-infinite unit-speed horizontal trajectory lies off the critical set. -/
theorem s26v_a_not_mem_E {q : S₀ → ℂ → ℂ} {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) (s : ℝ) : c s ∉ s26v_E q := by
  intro h
  refine h ⟨⟨fun r => c (s + r), by fun_prop⟩, fun r => s26v_a_trajAt_shift_add (hc (s + r)), ?_⟩
  show c (s + 0) = c s
  rw [add_zero]

/-- **Existence of tubes.**  Off the critical set, every point has tubes of any time `T ≥ 0`: develop its trajectory
over `[-T - 1, T + 1]`, and take the width below a Lebesgue number of the local injectivity discs along `[-T, T]`. -/
theorem s26v_a_tube_exists [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {p₀ : S₀} (hp₀ : p₀ ∉ s26v_E q) {T : ℝ} (hT : 0 ≤ T) : ∃ (ρ : ℝ) (G : ℂ → S₀), s26v_a_IsTube q T p₀ ρ G := by
  obtain ⟨htr, h0⟩ := s26v_traj_spec hp₀
  obtain ⟨ρ₀, hρ₀, G, hdev⟩ := s26v_a_dev_exists hq (c := s26v_traj q p₀) (a := -(T + 1)) (b := T + 1)
    (by linarith) fun s _ => Eventually.of_forall htr
  set ρ₁ := min 1 ρ₀ with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min one_pos hρ₀
  have hρ₁1 : ρ₁ ≤ 1 := min_le_left _ _
  have hρ₁2 : ρ₁ ≤ ρ₀ := min_le_right _ _
  have hnat : ∀ s ∈ Icc (-T) T, ∀ u ∈ ball (s : ℂ) ρ₁, s26v_a_IsNatAt q G u := by
    intro s hs u hu
    have hre : |(u - (s : ℂ)).re| < ρ₁ := lt_of_le_of_lt (Complex.abs_re_le_norm _) (mem_ball_iff_norm.1 hu)
    have him : |(u - (s : ℂ)).im| < ρ₁ := lt_of_le_of_lt (Complex.abs_im_le_norm _) (mem_ball_iff_norm.1 hu)
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_lt] at him
    exact hdev.1 u ⟨by linarith [hs.1, hre.1], by linarith [hs.2, hre.2]⟩ ⟨by linarith [him.1], by linarith [him.2]⟩
  have hinj : ∀ s : Icc (-T) T, ∃ r > 0, InjOn G (ball ((s : ℝ) : ℂ) r) := fun s =>
    s26v_a_natAt_injOn hq hρ₁0 (hnat s s.2)
  choose r hr hrinj using hinj
  have hcpt : IsCompact ((fun s : ℝ => (s : ℂ)) '' Icc (-T) T) := isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hcpt
    (c := fun s : Icc (-T) T => ball ((s : ℝ) : ℂ) (r s)) (fun _ => isOpen_ball) (by
      rintro _ ⟨s, hs, rfl⟩
      exact mem_iUnion.2 ⟨⟨s, hs⟩, mem_ball_self (hr _)⟩)
  set ρ := min δ (ρ₁ / 4) with hρ
  have hρ0 : 0 < ρ := lt_min hδ (by linarith)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρ4 : ρ ≤ ρ₁ / 4 := min_le_right _ _
  refine ⟨ρ, G, hρ0, ?_, fun u hre him => hdev.1 u ⟨by linarith [hre.1], by linarith [hre.2]⟩
    ⟨by linarith [him.1], by linarith [him.2]⟩, fun s hs => ?_⟩
  · have h := hdev.2 0 ⟨by linarith, by linarith⟩
    rw [Complex.ofReal_zero] at h
    rw [h, h0]
  · obtain ⟨i, hi⟩ := hleb (s : ℂ) ⟨s, hs, rfl⟩
    exact (hrinj i).mono ((ball_subset_ball hρδ).trans hi)

/-- **Trajectories in a tube.**  If `w'` lies in the strip of a tube and `G w'` is off the critical set, the chosen
trajectory through `G w'` runs along `r ↦ G (w' + r)` or along `r ↦ G (w' - r)`, as long as this stays in the
strip. -/
theorem s26v_a_tube_traj [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    {p₀ : S₀} {ρ : ℝ} {G : ℂ → S₀} (hG : s26v_a_IsTube q T p₀ ρ G) {w' : ℂ}
    (hre : w'.re ∈ Ioo (-T - 2 * ρ) (T + 2 * ρ)) (him : w'.im ∈ Ioo (-(2 * ρ)) (2 * ρ)) (hE : G w' ∉ s26v_E q) :
    (∀ r ∈ Ioo (-T - 2 * ρ - w'.re) (T + 2 * ρ - w'.re), s26v_traj q (G w') r = G (w' + (r : ℂ))) ∨
      ∀ r ∈ Ioo (w'.re - T - 2 * ρ) (w'.re + T + 2 * ρ), s26v_traj q (G w') r = G (w' - (r : ℂ)) := by
  obtain ⟨htr, h0⟩ := s26v_traj_spec hE
  have hlp : ∀ r ∈ Ioo (-T - 2 * ρ - w'.re) (T + 2 * ρ - w'.re),
      s26v_IsTrajAt q (fun r' : ℝ => G (w' + ((1 : ℝ) : ℂ) * (r' : ℂ))) r := by
    intro r hr
    refine s26v_a_trajAt_of_natAt (Or.inl rfl) (hG.2.2.1 _ ?_ ?_)
    · simp only [Complex.ofReal_one, one_mul, Complex.add_re, Complex.ofReal_re]
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · simp only [Complex.ofReal_one, one_mul, Complex.add_im, Complex.ofReal_im, add_zero]
      exact him
  have hlm : ∀ r ∈ Ioo (w'.re - T - 2 * ρ) (w'.re + T + 2 * ρ),
      s26v_IsTrajAt q (fun r' : ℝ => G (w' + ((-1 : ℝ) : ℂ) * (r' : ℂ))) r := by
    intro r hr
    refine s26v_a_trajAt_of_natAt (Or.inr rfl) (hG.2.2.1 _ ?_ ?_)
    · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, Complex.add_re, Complex.neg_re,
        Complex.ofReal_re]
      exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, Complex.add_im, Complex.neg_im,
        Complex.ofReal_im, neg_zero, add_zero]
      exact him
  have hJ0 : (0 : ℝ) ∈ Ioo (-T - 2 * ρ - w'.re) (T + 2 * ρ - w'.re) := ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hJ0' : (0 : ℝ) ∈ Ioo (w'.re - T - 2 * ρ) (w'.re + T + 2 * ρ) := ⟨by linarith [hre.2], by linarith [hre.1]⟩
  have hc0 : ∀ᶠ r in 𝓝 (0 : ℝ), s26v_IsTrajAt q (fun r' : ℝ => G (w' + ((1 : ℝ) : ℂ) * (r' : ℂ))) r := by
    filter_upwards [isOpen_Ioo.mem_nhds hJ0] with r hr using hlp r hr
  have hval : (fun r' : ℝ => G (w' + ((1 : ℝ) : ℂ) * (r' : ℂ))) 0 = s26v_traj q (G w') 0 := by
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    exact h0.symm
  obtain ⟨σ, hσ, hloc⟩ := s26v_a_local_unique hq hc0 (Eventually.of_forall htr) hval
  simp only [zero_add] at hloc
  rcases hσ with rfl | rfl
  · left
    have h := s26v_a_eqOn_of_eventuallyEq hq (c := s26v_traj q (G w'))
      (c' := fun r' : ℝ => G (w' + ((1 : ℝ) : ℂ) * (r' : ℂ))) isOpen_Ioo isPreconnected_Ioo
      (fun r _ => htr r) hlp hJ0 (hloc.mono fun r hr => by rw [hr, one_mul])
    intro r hr
    rw [h r hr, Complex.ofReal_one, one_mul]
  · right
    have h := s26v_a_eqOn_of_eventuallyEq hq (c := s26v_traj q (G w'))
      (c' := fun r' : ℝ => G (w' + ((-1 : ℝ) : ℂ) * (r' : ℂ))) isOpen_Ioo isPreconnected_Ioo
      (fun r _ => htr r) hlm hJ0' (hloc.mono fun r hr => by
        rw [hr]
        simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul])
    intro r hr
    rw [h r hr]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_eq_add_neg]

/-- **The pair of flow points in a tube.**  For `w` in the central disc of a tube with `G w` off the critical set and
`t ∈ [-T, T]`, the two points `c_{G w}(±t)` are `G (w ± t)`, in one order or the other. -/
theorem s26v_a_tube_pair [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    {p₀ : S₀} {ρ : ℝ} {G : ℂ → S₀} (hG : s26v_a_IsTube q T p₀ ρ G) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ)
    (hE : G w ∉ s26v_E q) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    (s26v_traj q (G w) t = G (w + t) ∧ s26v_traj q (G w) (-t) = G (w - t)) ∨
      (s26v_traj q (G w) t = G (w - t) ∧ s26v_traj q (G w) (-t) = G (w + t)) := by
  have hw' : ‖w‖ < ρ := by simpa using hw
  have hre : |w.re| < ρ := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
  have him : |w.im| < ρ := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw'
  rw [abs_lt] at hre him
  obtain ⟨hre1, hre2⟩ := hre
  obtain ⟨him1, him2⟩ := him
  obtain ⟨ht1, ht2⟩ := ht
  have hρ := hG.1
  rcases s26v_a_tube_traj hq hG ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hE with h | h
  · left
    refine ⟨h t ⟨by linarith, by linarith⟩, ?_⟩
    rw [h (-t) ⟨by linarith, by linarith⟩, Complex.ofReal_neg, ← sub_eq_add_neg]
  · right
    refine ⟨h t ⟨by linarith, by linarith⟩, ?_⟩
    rw [h (-t) ⟨by linarith, by linarith⟩, Complex.ofReal_neg, sub_neg_eq_add]

/-- In a tube, a point `G w` of the central disc lies off the critical set as soon as a point `G (w + s)`,
`s ∈ [-T, T]`, of its horizontal line does (both lie on one bi-infinite trajectory). -/
theorem s26v_a_tube_not_mem_E [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {T : ℝ} {p₀ : S₀} {ρ : ℝ} {G : ℂ → S₀} (hG : s26v_a_IsTube q T p₀ ρ G) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ)
    {s : ℝ} (hs : s ∈ Icc (-T) T) (hE : G (w + s) ∉ s26v_E q) : G w ∉ s26v_E q := by
  have hw' : ‖w‖ < ρ := by simpa using hw
  have hre : |w.re| < ρ := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
  have him : |w.im| < ρ := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw'
  rw [abs_lt] at hre him
  obtain ⟨hre1, hre2⟩ := hre
  obtain ⟨him1, him2⟩ := him
  obtain ⟨hs1, hs2⟩ := hs
  have hρ := hG.1
  obtain ⟨htr, -⟩ := s26v_traj_spec hE
  have hre' : (w + (s : ℂ)).re = w.re + s := by simp
  have him' : (w + (s : ℂ)).im = w.im := by simp
  rcases s26v_a_tube_traj hq hG (w' := w + s) (by rw [hre']; exact ⟨by linarith, by linarith⟩)
    (by rw [him']; exact ⟨by linarith, by linarith⟩) hE with h | h
  · have h1 := h (-s) (by rw [hre']; exact ⟨by linarith, by linarith⟩)
    rw [Complex.ofReal_neg, ← sub_eq_add_neg, add_sub_cancel_right] at h1
    rw [← h1]
    exact s26v_a_not_mem_E htr (-s)
  · have h1 := h s (by rw [hre']; exact ⟨by linarith, by linarith⟩)
    rw [add_sub_cancel_right] at h1
    rw [← h1]
    exact s26v_a_not_mem_E htr s

/-! #### Prover A helpers: integration in natural coordinates -/

/-- The part of a measurable set `A` on which a map continuous on `A` takes values in a measurable set is measurable. -/
theorem s26v_a_measurableSet_inter_preimage {A M : Set ℂ} {g : ℂ → ℂ} (hA : MeasurableSet A)
    (hg : ContinuousOn g A) (hM : MeasurableSet M) : MeasurableSet {u | u ∈ A ∧ g u ∈ M} := by
  classical
  have hm : Measurable (A.piecewise g (fun _ => 0)) := hg.measurable_piecewise continuousOn_const hA
  have heq : {u | u ∈ A ∧ g u ∈ M} = A ∩ (A.piecewise g (fun _ => 0)) ⁻¹' M := by
    ext u
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [Set.piecewise_eq_of_mem _ _ _ h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [Set.piecewise_eq_of_mem _ _ _ h1] at h2; exact h2⟩
  rw [heq]
  exact hA.inter (hm hM)

/-- The chart expression of a map natural on `A` and landing in the chart at `x` is continuous on `A`. -/
theorem s26v_a_natAt_continuousOn {q : S₀ → ℂ → ℂ} {G : ℂ → S₀} {A : Set ℂ}
    (hG : ∀ u ∈ A, s26v_a_IsNatAt q G u) (x : S₀) (hAx : ∀ u ∈ A, G u ∈ (chartAt ℂ x).source) :
    ContinuousOn (fun u => chartAt ℂ x (G u)) A := fun u hu =>
  (ContinuousAt.comp (g := chartAt ℂ x) (f := G) ((chartAt ℂ x).continuousAt (hAx u hu)) (hG u hu).1).continuousWithinAt

/-- **Change of variables between a chart and a natural map.**  If `G` is natural and injective on a measurable set `A`
mapped into the chart at `x`, then `∫_{φ_x(G A)} f |q_x| = ∫_A f ∘ φ_x ∘ G`: the chart expression `g = φ_x ∘ G` has
Jacobian `|g'|²` and `|g'|² |q_x ∘ g| = 1`. -/
theorem s26v_a_lintegral_nat [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {G : ℂ → S₀}
    {A : Set ℂ} (hAm : MeasurableSet A) (hG : ∀ u ∈ A, s26v_a_IsNatAt q G u) (hinj : InjOn G A) (x : S₀)
    (hAx : ∀ u ∈ A, G u ∈ (chartAt ℂ x).source) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z in (fun u => chartAt ℂ x (G u)) '' A, f z * ENNReal.ofReal ‖q x z‖ =
      ∫⁻ u in A, f (chartAt ℂ x (G u)) := by
  set g : ℂ → ℂ := fun u => chartAt ℂ x (G u) with hg
  have hderiv : ∀ u ∈ A, ∃ v, HasDerivAt g v u ∧ q x (g u) * v ^ 2 = 1 := fun u hu =>
    s26v_a_natAt_chart hq (hG u hu) x (hAx u hu)
  have hdiff : ∀ u ∈ A, DifferentiableAt ℂ g u := fun u hu => (hderiv u hu).choose_spec.1.differentiableAt
  have hginj : InjOn g A := fun u₁ h₁ u₂ h₂ h => hinj h₁ h₂ ((chartAt ℂ x).injOn (hAx u₁ h₁) (hAx u₂ h₂) h)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm
    (fun u hu => ((hdiff u hu).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hginj]
  refine setLIntegral_congr_fun hAm fun u hu => ?_
  obtain ⟨v, hv, hqv⟩ := hderiv u hu
  have hd := hdiff u hu
  have hdet : (fderiv ℝ g u).det = ‖deriv g u‖ ^ 2 := by
    have e := det_fderiv_eq_jacobian (hd.restrictScalars ℝ)
    rw [show (fderiv ℝ g u).det = LinearMap.det (fderiv ℝ g u : ℂ →ₗ[ℝ] ℂ) from rfl, e,
      jacobian, dz_eq_deriv hd, (cauchyRiemann_iff.1 hd).2, norm_zero]
    ring
  have h1 : ‖v‖ ^ 2 * ‖q x (g u)‖ = 1 := by
    have h := congrArg (‖·‖) hqv
    simp only [norm_mul, norm_pow, norm_one] at h
    linarith
  rw [hdet, abs_of_nonneg (by positivity), hv.deriv]
  calc ENNReal.ofReal (‖v‖ ^ 2) * (f (g u) * ENNReal.ofReal ‖q x (g u)‖)
      = f (g u) * ENNReal.ofReal (‖v‖ ^ 2 * ‖q x (g u)‖) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
    _ = f (g u) := by rw [h1, ENNReal.ofReal_one, mul_one]

/-- **Null sets pull back along natural maps.**  If `G` is natural and injective on a measurable set `A` mapped into the
chart at `x`, the points of `A` whose chart image lies in a null set form a null set (the change of variables for the
indicator of a measurable null hull). -/
theorem s26v_a_null_preimage [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {G : ℂ → S₀}
    {A : Set ℂ} (hAm : MeasurableSet A) (hG : ∀ u ∈ A, s26v_a_IsNatAt q G u) (hinj : InjOn G A) (x : S₀)
    (hAx : ∀ u ∈ A, G u ∈ (chartAt ℂ x).source) {M : Set ℂ} (hM : volume M = 0) :
    volume {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M} = 0 := by
  set M' := toMeasurable volume M with hM'
  have hM'm : MeasurableSet M' := measurableSet_toMeasurable _ _
  have hM'0 : volume M' = 0 := by rw [hM', measure_toMeasurable]; exact hM
  have hmeas : MeasurableSet {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'} :=
    s26v_a_measurableSet_inter_preimage hAm (s26v_a_natAt_continuousOn hG x hAx) hM'm
  refine measure_mono_null (t := {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'})
    (fun u hu => ⟨hu.1, subset_toMeasurable _ _ hu.2⟩) ?_
  rw [← lintegral_indicator_one hmeas]
  have h1 : ∫⁻ u, {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'}.indicator 1 u =
      ∫⁻ u in A, M'.indicator 1 (chartAt ℂ x (G u)) := by
    rw [← lintegral_indicator hAm]
    refine lintegral_congr fun u => ?_
    by_cases huA : u ∈ A
    · by_cases huM : chartAt ℂ x (G u) ∈ M'
      · simp [huA, huM, Set.indicator_of_mem, show u ∈ {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'} from ⟨huA, huM⟩]
      · have hn : u ∉ {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'} := fun h => huM h.2
        simp [huA, huM, hn]
    · have hn : u ∉ {u | u ∈ A ∧ chartAt ℂ x (G u) ∈ M'} := fun h => huA h.1
      simp [huA, hn]
  rw [h1, ← s26v_a_lintegral_nat hq hAm hG hinj x hAx]
  have hae : (fun z => M'.indicator 1 z * ENNReal.ofReal ‖q x z‖) =ᵐ[volume.restrict
      ((fun u => chartAt ℂ x (G u)) '' A)] 0 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM'0] with z hz
    simp [Set.indicator_of_notMem hz]
  rw [lintegral_congr_ae hae]
  simp

/-! #### Prover A helpers: tube families and the development formula -/

/-- In a tube, `G` is natural and injective on each disc `ball s ρ`, `s ∈ [-T, T]`. -/
theorem s26v_a_tube_ball {q : S₀ → ℂ → ℂ} {T : ℝ} {p₀ : S₀} {ρ : ℝ} {G : ℂ → S₀}
    (hG : s26v_a_IsTube q T p₀ ρ G) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    (∀ u ∈ ball (s : ℂ) ρ, s26v_a_IsNatAt q G u) ∧ InjOn G (ball (s : ℂ) ρ) := by
  refine ⟨fun u hu => ?_, hG.2.2.2 s hs⟩
  have hu' : ‖u - s‖ < ρ := mem_ball_iff_norm.1 hu
  have hre : |(u - (s : ℂ)).re| < ρ := lt_of_le_of_lt (Complex.abs_re_le_norm _) hu'
  have him : |(u - (s : ℂ)).im| < ρ := lt_of_le_of_lt (Complex.abs_im_le_norm _) hu'
  rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at hre
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_lt] at him
  have hρ := hG.1
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hre1, hre2⟩ := hre
  obtain ⟨him1, him2⟩ := him
  exact hG.2.2.1 u ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

/-- The pieces of a tube family: the points of the central disc of the `k`-th tube whose image is not covered by the
central discs of the earlier tubes. -/
def s26v_a_W (G : ℕ → ℂ → S₀) (ρ : ℕ → ℝ) (k : ℕ) : Set ℂ :=
  {w | w ∈ ball (0 : ℂ) (ρ k) ∧ ∀ j < k, G k w ∉ G j '' ball (0 : ℂ) (ρ j)}

/-- A **tube family** of time `T`: tubes whose central discs cover the complement of the critical set. -/
def s26v_a_IsTubeFamily (q : S₀ → ℂ → ℂ) (T : ℝ) (ρ : ℕ → ℝ) (G : ℕ → ℂ → S₀) : Prop :=
  (∀ k, ∃ p₀, s26v_a_IsTube q T p₀ (ρ k) (G k)) ∧ ∀ p, p ∉ s26v_E q → ∃ k, p ∈ G k '' ball (0 : ℂ) (ρ k)

/-- The complement of the critical set is nonempty (the critical set is null in every chart). -/
theorem s26v_a_exists_not_mem_E [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) : ∃ p, p ∉ s26v_E q := by
  obtain ⟨p⟩ : Nonempty S₀ := inferInstance
  by_contra h'
  have h : ∀ y, y ∈ s26v_E q := fun y => by_contra fun hy => h' ⟨y, hy⟩
  have h0 := s26v_E_null hq hne p
  have heq : chartAt ℂ p '' (s26v_E q ∩ (chartAt ℂ p).source) = (chartAt ℂ p).target := by
    rw [inter_eq_right.2 fun y _ => h y]
    exact (chartAt ℂ p).image_source_eq_target
  rw [heq] at h0
  exact ((chartAt ℂ p).open_target.measure_pos volume ⟨_, mem_chart_target ℂ p⟩).ne' h0

/-- **Tube families exist** (tubes at every point off the critical set; second countability). -/
theorem s26v_a_tubeFamily_exists [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (ρ : ℕ → ℝ) (G : ℕ → ℂ → S₀), s26v_a_IsTubeFamily q T ρ G := by
  have hsc : SecondCountableTopology S₀ := ChartedSpace.secondCountable_of_sigmaCompact ℂ S₀
  have htube : ∀ p : {p : S₀ // p ∉ s26v_E q}, ∃ (ρ : ℝ) (G : ℂ → S₀), s26v_a_IsTube q T p ρ G :=
    fun p => s26v_a_tube_exists hq p.2 hT
  choose ρ G hG using htube
  have h0T : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hopen : ∀ p, IsOpen (G p '' ball (0 : ℂ) (ρ p)) := fun p =>
    s26v_a_natAt_isOpen_image hq isOpen_ball (by simpa using (s26v_a_tube_ball (hG p) h0T).1)
  have hself : ∀ p : {p : S₀ // p ∉ s26v_E q}, (p : S₀) ∈ G p '' ball (0 : ℂ) (ρ p) := fun p =>
    ⟨0, mem_ball_self (hG p).1, (hG p).2.1⟩
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p => G p '' ball (0 : ℂ) (ρ p)) hopen
  obtain ⟨p₁, hp₁⟩ := s26v_a_exists_not_mem_E hq hne
  have hmem : p₁ ∈ ⋃ p, G p '' ball (0 : ℂ) (ρ p) := mem_iUnion.2 ⟨⟨p₁, hp₁⟩, hself ⟨p₁, hp₁⟩⟩
  rw [← hSU] at hmem
  obtain ⟨p₂, hp₂S, -⟩ := mem_iUnion₂.1 hmem
  obtain ⟨f, hf⟩ := hSc.exists_eq_range ⟨p₂, hp₂S⟩
  refine ⟨fun k => ρ (f k), fun k => G (f k), ⟨fun k => ⟨f k, hG (f k)⟩, fun p hp => ?_⟩⟩
  have hmem' : p ∈ ⋃ p', G p' '' ball (0 : ℂ) (ρ p') := mem_iUnion.2 ⟨⟨p, hp⟩, hself ⟨p, hp⟩⟩
  rw [← hSU] at hmem'
  obtain ⟨p', hp'S, hpp'⟩ := mem_iUnion₂.1 hmem'
  rw [hf] at hp'S
  obtain ⟨k, rfl⟩ := hp'S
  exact ⟨k, hpp'⟩

/-- In a tube family, each tube is natural and injective on its central disc, which is mapped onto an open set. -/
theorem s26v_a_family_center [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) (k : ℕ) :
    (∀ u ∈ ball (0 : ℂ) (ρ k), s26v_a_IsNatAt q (G k) u) ∧ InjOn (G k) (ball (0 : ℂ) (ρ k)) ∧
      IsOpen (G k '' ball (0 : ℂ) (ρ k)) := by
  obtain ⟨p₀, hG⟩ := hfam.1 k
  have h := s26v_a_tube_ball hG (s := 0) ⟨by linarith, hT⟩
  simp only [Complex.ofReal_zero] at h
  exact ⟨h.1, h.2, s26v_a_natAt_isOpen_image hq isOpen_ball h.1⟩

/-- The pieces of a tube family are measurable. -/
theorem s26v_a_W_measurable [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) (k : ℕ) :
    MeasurableSet (s26v_a_W G ρ k) := by
  have hc : ContinuousOn (G k) (ball (0 : ℂ) (ρ k)) := fun u hu =>
    ((s26v_a_family_center hq hT hfam k).1 u hu).1.continuousWithinAt
  have heq : s26v_a_W G ρ k = ball (0 : ℂ) (ρ k) ∩
      ⋂ j ∈ {j : ℕ | j < k}, (ball (0 : ℂ) (ρ k) ∩ G k ⁻¹' (G j '' ball (0 : ℂ) (ρ j)))ᶜ := by
    ext w
    simp only [s26v_a_W, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff, mem_preimage, not_and]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨hw, fun j hj _ => h j hj⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, fun j hj => h j hj hw⟩
  rw [heq]
  refine measurableSet_ball.inter (MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_)
  exact (hc.isOpen_inter_preimage isOpen_ball (s26v_a_family_center hq hT hfam j).2.2).measurableSet.compl

/-- The images of the pieces of a tube family are pairwise disjoint. -/
theorem s26v_a_W_disjoint {G : ℕ → ℂ → S₀} {ρ : ℕ → ℝ} {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (G j '' s26v_a_W G ρ j) (G k '' s26v_a_W G ρ k) := by
  have _ : ChartedSpace ℂ S₀ := inferInstance
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨wj, hwj, rfl⟩ ⟨wk, hwk, hk⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hwk.2 j h ⟨wj, hwj.1, hk.symm⟩
  · exact hwj.2 k h ⟨wk, hwk.1, hk⟩

/-- The images of the pieces of a tube family cover the complement of the critical set. -/
theorem s26v_a_W_cover {q : S₀ → ℂ → ℂ} {T : ℝ} {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀}
    (hfam : s26v_a_IsTubeFamily q T ρ G) {p : S₀} (hp : p ∉ s26v_E q) : ∃ k, p ∈ G k '' s26v_a_W G ρ k := by
  classical
  have hex : ∃ k, p ∈ G k '' ball (0 : ℂ) (ρ k) := hfam.2 p hp
  obtain ⟨w, hw, hwp⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, w, ⟨hw, fun j hj h => Nat.find_min hex hj ?_⟩, hwp⟩
  rw [← hwp]
  exact h

/-- **The development formula.**  For a tube family, the surface integral of any chart-independent integrand `f` is the
sum over the pieces of the Lebesgue integrals of `f ∘ G_k` in natural coordinates (a chart partition, refined by the
pieces; the critical set is null; the change of variables `s26v_a_lintegral_nat`). -/
theorem s26v_a_dev_formula [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {T : ℝ} (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀}
    (hfam : s26v_a_IsTubeFamily q T ρ G) (f : S₀ → ℝ≥0∞) :
    surfaceIntegral q (fun x z => f ((chartAt ℂ x).symm z)) = ∑' k, ∫⁻ w in s26v_a_W G ρ k, f (G k w) := by
  obtain ⟨x, Q, hQ⟩ := s26_exists_chartPartition' (S := S₀)
  rw [s26v_surfaceIntegral_eq_tsum hq f hQ]
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  have hnatW : ∀ k, ∀ u ∈ s26v_a_W G ρ k, s26v_a_IsNatAt q (G k) u := fun k u hu =>
    (s26v_a_family_center hq hT hfam k).1 u hu.1
  have hinjW : ∀ k, InjOn (G k) (s26v_a_W G ρ k) := fun k =>
    (s26v_a_family_center hq hT hfam k).2.1.mono fun u hu => hu.1
  set Wm : ℕ → ℕ → Set ℂ := fun m k => {w | w ∈ s26v_a_W G ρ k ∧ G k w ∈ Q m} with hWm
  have hWm_meas : ∀ m k, MeasurableSet (Wm m k) := by
    intro m k
    set D := {w | w ∈ s26v_a_W G ρ k ∧ G k w ∈ (chartAt ℂ (x m)).source} with hD
    have hDo : MeasurableSet D := by
      have hc : ContinuousOn (G k) (ball (0 : ℂ) (ρ k)) := fun u hu =>
        ((s26v_a_family_center hq hT hfam k).1 u hu).1.continuousWithinAt
      have h1 := (hc.isOpen_inter_preimage isOpen_ball (chartAt ℂ (x m)).open_source).measurableSet
      have heq : D = s26v_a_W G ρ k ∩ (ball (0 : ℂ) (ρ k) ∩ G k ⁻¹' (chartAt ℂ (x m)).source) := by
        ext w
        simp only [hD, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
        exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [heq]
      exact (s26v_a_W_measurable hq hT hfam k).inter h1
    have hm := s26v_a_measurableSet_inter_preimage hDo
      (s26v_a_natAt_continuousOn (fun u hu => hnatW k u hu.1) (x m) fun u hu => hu.2) (hQsm m).2
    convert hm using 1
    ext w
    simp only [hWm, hD, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, (hQsm m).1 h2⟩, ⟨G k w, h2, rfl⟩⟩
    · rintro ⟨⟨h1, h2⟩, p, hpQ, hp⟩
      exact ⟨h1, (chartAt ℂ (x m)).injOn ((hQsm m).1 hpQ) h2 hp ▸ hpQ⟩
  have hpiece : ∀ m k, ∫⁻ z in (fun w => chartAt ℂ (x m) (G k w)) '' Wm m k,
      f ((chartAt ℂ (x m)).symm z) * ENNReal.ofReal ‖q (x m) z‖ = ∫⁻ w in Wm m k, f (G k w) := by
    intro m k
    rw [s26v_a_lintegral_nat hq (hWm_meas m k) (fun u hu => hnatW k u hu.1) ((hinjW k).mono fun u hu => hu.1)
      (x m) (fun u hu => (hQsm m).1 hu.2)]
    refine setLIntegral_congr_fun (hWm_meas m k) fun w hw => ?_
    rw [(chartAt ℂ (x m)).left_inv ((hQsm m).1 hw.2)]
  have hsplit : ∀ m, ∫⁻ z in chartAt ℂ (x m) '' Q m, f ((chartAt ℂ (x m)).symm z) * ENNReal.ofReal ‖q (x m) z‖ =
      ∑' k, ∫⁻ w in Wm m k, f (G k w) := by
    intro m
    set φ := chartAt ℂ (x m) with hφ
    set Ak : ℕ → Set ℂ := fun k => (fun w => φ (G k w)) '' Wm m k with hAk
    have hAk_meas : ∀ k, MeasurableSet (Ak k) := fun k =>
      (hWm_meas m k).image_of_continuousOn_injOn
        (s26v_a_natAt_continuousOn (fun u hu => hnatW k u hu.1) (x m) fun u hu => (hQsm m).1 hu.2)
        fun u₁ h₁ u₂ h₂ h => hinjW k h₁.1 h₂.1 (φ.injOn ((hQsm m).1 h₁.2) ((hQsm m).1 h₂.2) h)
    have hAk_disj : Pairwise (fun k k' => Disjoint (Ak k) (Ak k')) := by
      intro k k' hkk'
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', h⟩
      have h' : G k' w' = G k w := φ.injOn ((hQsm m).1 hw'.2) ((hQsm m).1 hw.2) h
      exact Set.disjoint_left.1 (s26v_a_W_disjoint (G := G) (ρ := ρ) hkk') ⟨w, hw.1, rfl⟩ ⟨w', hw'.1, h'⟩
    have hAk_sub : (⋃ k, Ak k) ⊆ φ '' Q m := by
      rintro _ ⟨_, ⟨k, rfl⟩, w, hw, rfl⟩
      exact ⟨G k w, hw.2, rfl⟩
    have hrest : φ '' Q m ⊆ (⋃ k, Ak k) ∪ φ '' (s26v_E q ∩ φ.source) := by
      rintro _ ⟨p, hpQ, rfl⟩
      by_cases hpE : p ∈ s26v_E q
      · exact Or.inr ⟨p, ⟨hpE, (hQsm m).1 hpQ⟩, rfl⟩
      · obtain ⟨k, w, hw, hwp⟩ := s26v_a_W_cover hfam hpE
        refine Or.inl (mem_iUnion.2 ⟨k, w, ⟨hw, hwp ▸ hpQ⟩, ?_⟩)
        show φ (G k w) = φ p
        rw [hwp]
    have hnull := s26v_E_null hq hne (x m)
    set F := fun z => f (φ.symm z) * ENNReal.ofReal ‖q (x m) z‖ with hF
    have hsum : ∫⁻ z in ⋃ k, Ak k, F z = ∑' k, ∫⁻ w in Wm m k, f (G k w) := by
      rw [lintegral_iUnion hAk_meas hAk_disj]
      exact tsum_congr (hpiece m)
    apply le_antisymm
    · calc ∫⁻ z in φ '' Q m, F z ≤ ∫⁻ z in (⋃ k, Ak k) ∪ φ '' (s26v_E q ∩ φ.source), F z :=
            lintegral_mono_set hrest
        _ ≤ (∫⁻ z in ⋃ k, Ak k, F z) + ∫⁻ z in φ '' (s26v_E q ∩ φ.source), F z :=
            lintegral_union_le F (⋃ k, Ak k) (φ '' (s26v_E q ∩ φ.source))
        _ = ∑' k, ∫⁻ w in Wm m k, f (G k w) := by rw [setLIntegral_measure_zero _ _ hnull, add_zero, hsum]
    · rw [← hsum]
      exact lintegral_mono_set hAk_sub
  rw [tsum_congr hsplit, ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  have hU : s26v_a_W G ρ k = ⋃ m, Wm m k := by
    ext w
    simp only [hWm, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hw
      obtain ⟨m, hm⟩ := mem_iUnion.1 (hQc.symm ▸ mem_univ (G k w) : G k w ∈ ⋃ m, Q m)
      exact ⟨m, hw, hm⟩
    · rintro ⟨m, hw, -⟩
      exact hw
  rw [hU, lintegral_iUnion (fun m => hWm_meas m k)]
  intro m m' hmm'
  refine Set.disjoint_left.2 fun w hw hw' => ?_
  exact Set.disjoint_left.1 (hQd hmm') hw.2 hw'.2

/-! #### Prover A helpers: surface integrals of images of natural maps -/

/-- For `G` natural and injective on an open set `O ⊇ A` (`A` measurable), the part of `A` mapped into a chart piece
`Q` (with measurable chart image) is measurable, and so is its chart image. -/
theorem s26v_a_piece_measurable [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} {G : ℂ → S₀} {O A : Set ℂ}
    (hO : IsOpen O) (hAO : A ⊆ O) (hAm : MeasurableSet A) (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u)
    (hinj : InjOn G O) (x : S₀) {Q : Set S₀} (hQs : Q ⊆ (chartAt ℂ x).source)
    (hQm : MeasurableSet (chartAt ℂ x '' Q)) :
    MeasurableSet {u | u ∈ A ∧ G u ∈ Q} ∧
      MeasurableSet ((fun u => chartAt ℂ x (G u)) '' {u | u ∈ A ∧ G u ∈ Q}) := by
  have hGc : ContinuousOn G O := fun u hu => (hG u hu).1.continuousWithinAt
  set D := {u | u ∈ A ∧ G u ∈ (chartAt ℂ x).source} with hD
  have hDm : MeasurableSet D := by
    have h1 := (hGc.isOpen_inter_preimage hO (chartAt ℂ x).open_source).measurableSet
    have heq : D = A ∩ (O ∩ G ⁻¹' (chartAt ℂ x).source) := by
      ext u
      simp only [hD, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
      exact ⟨fun h => ⟨h.1, hAO h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact hAm.inter h1
  have hc : ContinuousOn (fun u => chartAt ℂ x (G u)) D :=
    s26v_a_natAt_continuousOn (fun u hu => hG u (hAO hu.1)) x fun u hu => hu.2
  have hm := s26v_a_measurableSet_inter_preimage hDm hc hQm
  have heq : {u | u ∈ A ∧ G u ∈ Q} = {u | u ∈ D ∧ chartAt ℂ x (G u) ∈ chartAt ℂ x '' Q} := by
    ext u
    simp only [hD, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, hQs h2⟩, ⟨G u, h2, rfl⟩⟩
    · rintro ⟨⟨h1, h2⟩, p, hpQ, hp⟩
      exact ⟨h1, (chartAt ℂ x).injOn (hQs hpQ) h2 hp ▸ hpQ⟩
  rw [heq]
  refine ⟨hm, hm.image_of_continuousOn_injOn (hc.mono fun u hu => hu.1) ?_⟩
  intro u₁ h₁ u₂ h₂ h
  exact hinj (hAO h₁.1.1) (hAO h₂.1.1) ((chartAt ℂ x).injOn h₁.1.2 h₂.1.2 h)

/-- **The target formula.**  For `G` natural and injective on an open set `O ⊇ A`, `A` measurable, the surface
integral of `U` times the indicator of `G(A)` is the Lebesgue integral of `U ∘ G` over `A` (a chart partition; on each
piece the change of variables `s26v_a_lintegral_nat`). -/
theorem s26v_a_target_formula [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] [Nonempty S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) {G : ℂ → S₀} {O A : Set ℂ} (hO : IsOpen O) (hAO : A ⊆ O) (hAm : MeasurableSet A)
    (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u) (hinj : InjOn G O) (U : S₀ → ℝ≥0∞) :
    surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z) * (G '' A).indicator 1 ((chartAt ℂ x).symm z)) =
      ∫⁻ u in A, U (G u) := by
  obtain ⟨x, Q, hQ⟩ := s26_exists_chartPartition' (S := S₀)
  have hV0 := s26v_surfaceIntegral_eq_tsum hq (fun p => U p * (G '' A).indicator 1 p) hQ
  refine hV0.trans ?_
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  set Am : ℕ → Set ℂ := fun m => {u | u ∈ A ∧ G u ∈ Q m} with hAmdef
  have hmeas : ∀ m, MeasurableSet (Am m) ∧
      MeasurableSet ((fun u => chartAt ℂ (x m) (G u)) '' Am m) := fun m =>
    s26v_a_piece_measurable hO hAO hAm hG hinj (x m) (hQsm m).1 (hQsm m).2
  have hpt : ∀ m, ∫⁻ z in chartAt ℂ (x m) '' Q m, U ((chartAt ℂ (x m)).symm z) *
      (G '' A).indicator 1 ((chartAt ℂ (x m)).symm z) * ENNReal.ofReal ‖q (x m) z‖ = ∫⁻ u in Am m, U (G u) := by
    intro m
    set φ := chartAt ℂ (x m) with hφ
    set S := (fun u => φ (G u)) '' Am m with hS
    have hSsub : S ⊆ φ '' Q m := by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨G u, hu.2, rfl⟩
    have hind : ∀ z ∈ φ '' Q m, U (φ.symm z) * (G '' A).indicator 1 (φ.symm z) * ENNReal.ofReal ‖q (x m) z‖ =
        S.indicator (fun z => U (φ.symm z) * ENNReal.ofReal ‖q (x m) z‖) z := by
      rintro _ ⟨p, hpQ, rfl⟩
      have hps : p ∈ φ.source := (hQsm m).1 hpQ
      rw [φ.left_inv hps]
      by_cases hpA : p ∈ G '' A
      · obtain ⟨u, hu, rfl⟩ := hpA
        have hzS : φ (G u) ∈ S := ⟨u, ⟨hu, hpQ⟩, rfl⟩
        rw [Set.indicator_of_mem (show G u ∈ G '' A from ⟨u, hu, rfl⟩), Set.indicator_of_mem hzS,
          φ.left_inv hps]
        simp
      · have hzS : φ p ∉ S := by
          rintro ⟨u, hu, hup⟩
          exact hpA ⟨u, hu.1, φ.injOn ((hQsm m).1 hu.2) hps hup⟩
        rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hzS]
        simp
    rw [setLIntegral_congr_fun (hQsm m).2 hind, setLIntegral_indicator (hmeas m).2,
      inter_eq_left.2 hSsub]
    rw [s26v_a_lintegral_nat hq (hmeas m).1 (fun u hu => hG u (hAO hu.1)) (hinj.mono fun u hu => hAO hu.1) (x m)
      (fun u hu => (hQsm m).1 hu.2) (fun z => U (φ.symm z))]
    refine setLIntegral_congr_fun (hmeas m).1 fun u hu => ?_
    rw [φ.left_inv ((hQsm m).1 hu.2)]
  rw [tsum_congr hpt]
  have hU : A = ⋃ m, Am m := by
    ext u
    simp only [hAmdef, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hu
      obtain ⟨m, hm⟩ := mem_iUnion.1 (hQc.symm ▸ mem_univ (G u) : G u ∈ ⋃ m, Q m)
      exact ⟨m, hu, hm⟩
    · rintro ⟨m, hu, -⟩
      exact hu
  rw [hU, lintegral_iUnion (fun m => (hmeas m).1)]
  intro m m' hmm'
  exact Set.disjoint_left.2 fun u hu hu' => Set.disjoint_left.1 (hQd hmm') hu.2 hu'.2

/-- **Countable additivity of the surface integral** for integrands a.e.-measurable in every chart. -/
theorem s26v_a_surfaceIntegral_tsum [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] [Nonempty S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (F : ℕ → S₀ → ℝ≥0∞)
    (hF : ∀ j (x : S₀), AEMeasurable (fun z => F j ((chartAt ℂ x).symm z)) (volume.restrict (chartAt ℂ x).target)) :
    surfaceIntegral q (fun x z => ∑' j, F j ((chartAt ℂ x).symm z)) =
      ∑' j, surfaceIntegral q (fun x z => F j ((chartAt ℂ x).symm z)) := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  obtain ⟨x, Q, hQ⟩ := s26_exists_chartPartition' (S := S₀)
  rw [s26v_surfaceIntegral_eq_tsum hq (fun p => ∑' j, F j p) hQ]
  rw [tsum_congr fun j => s26v_surfaceIntegral_eq_tsum hq (F j) hQ]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => ?_
  have hsub : chartAt ℂ (x m) '' Q m ⊆ (chartAt ℂ (x m)).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (chartAt ℂ (x m)).map_source ((hQ.1 m).1 hp)
  have hqm : AEMeasurable (fun z => ENNReal.ofReal ‖q (x m) z‖) (volume.restrict (chartAt ℂ (x m) '' Q m)) := by
    have h : AEMeasurable (fun z => ENNReal.ofReal ‖q (x m) z‖) (volume.restrict (chartAt ℂ (x m)).target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hq'.2 (x m)).continuousOn.norm).aemeasurable
        (chartAt ℂ (x m)).open_target.measurableSet
    exact h.mono_measure (Measure.restrict_mono hsub le_rfl)
  simp only [← ENNReal.tsum_mul_right]
  refine lintegral_tsum fun j => ?_
  exact ((hF j (x m)).mono_measure (Measure.restrict_mono hsub le_rfl)).mul hqm

/-- **Additivity of the surface integral** for two integrands, one a.e.-measurable in every chart. -/
theorem s26v_a_surfaceIntegral_add [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] [Nonempty S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (F₁ F₂ : S₀ → ℝ≥0∞)
    (hF : ∀ x : S₀, AEMeasurable (fun z => F₁ ((chartAt ℂ x).symm z)) (volume.restrict (chartAt ℂ x).target)) :
    surfaceIntegral q (fun x z => F₁ ((chartAt ℂ x).symm z) + F₂ ((chartAt ℂ x).symm z)) =
      surfaceIntegral q (fun x z => F₁ ((chartAt ℂ x).symm z)) +
        surfaceIntegral q (fun x z => F₂ ((chartAt ℂ x).symm z)) := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  obtain ⟨x, Q, hQ⟩ := s26_exists_chartPartition' (S := S₀)
  rw [s26v_surfaceIntegral_eq_tsum hq (fun p => F₁ p + F₂ p) hQ, s26v_surfaceIntegral_eq_tsum hq F₁ hQ,
    s26v_surfaceIntegral_eq_tsum hq F₂ hQ, ← ENNReal.tsum_add]
  refine tsum_congr fun m => ?_
  have hsub : chartAt ℂ (x m) '' Q m ⊆ (chartAt ℂ (x m)).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (chartAt ℂ (x m)).map_source ((hQ.1 m).1 hp)
  have hqm : AEMeasurable (fun z => ENNReal.ofReal ‖q (x m) z‖) (volume.restrict (chartAt ℂ (x m) '' Q m)) := by
    have h : AEMeasurable (fun z => ENNReal.ofReal ‖q (x m) z‖) (volume.restrict (chartAt ℂ (x m)).target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hq'.2 (x m)).continuousOn.norm).aemeasurable
        (chartAt ℂ (x m)).open_target.measurableSet
    exact h.mono_measure (Measure.restrict_mono hsub le_rfl)
  simp only [add_mul]
  exact lintegral_add_left' (((hF (x m)).mono_measure (Measure.restrict_mono hsub le_rfl)).mul hqm) _

/-- The surface integral is homogeneous for finite constant factors. -/
theorem s26v_a_surfaceIntegral_const_mul [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] [Nonempty S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (U : S₀ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    surfaceIntegral q (fun x z => c * U ((chartAt ℂ x).symm z)) =
      c * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) := by
  obtain ⟨x, Q, hQ⟩ := s26_exists_chartPartition' (S := S₀)
  rw [s26v_surfaceIntegral_eq_tsum hq (fun p => c * U p) hQ, s26v_surfaceIntegral_eq_tsum hq U hQ,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_congr fun z => ?_
  ring

/-- A function Borel in charts is a.e.-measurable on every chart target. -/
theorem s26v_a_aemeasurable_chart {U : S₀ → ℝ≥0∞} (hU : s26v_IsBorelInCharts U) (x : S₀) :
    AEMeasurable (fun z => U ((chartAt ℂ x).symm z)) (volume.restrict (chartAt ℂ x).target) := by
  obtain ⟨g, hg, hgU⟩ := hU x
  refine hg.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem (chartAt ℂ x).open_target.measurableSet] with z hz
  exact (hgU z hz).symm

/-- The indicator of the image of a measurable set under a map natural and injective on an open neighbourhood of it is
measurable on every chart target (Lusin–Souslin). -/
theorem s26v_a_aemeasurable_indicator [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} {G : ℂ → S₀} {O A : Set ℂ}
    (hO : IsOpen O) (hAO : A ⊆ O) (hAm : MeasurableSet A) (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u)
    (hinj : InjOn G O) (x : S₀) :
    AEMeasurable (fun z => (G '' A).indicator (1 : S₀ → ℝ≥0∞) ((chartAt ℂ x).symm z))
      (volume.restrict (chartAt ℂ x).target) := by
  have hm := (s26v_a_piece_measurable hO hAO hAm hG hinj x (Q := (chartAt ℂ x).source) subset_rfl
    (by rw [(chartAt ℂ x).image_source_eq_target]; exact (chartAt ℂ x).open_target.measurableSet)).2
  set S := (fun u => chartAt ℂ x (G u)) '' {u | u ∈ A ∧ G u ∈ (chartAt ℂ x).source} with hS
  have hmi : Measurable (S.indicator (fun _ : ℂ => (1 : ℝ≥0∞))) := measurable_const.indicator hm
  refine hmi.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem (chartAt ℂ x).open_target.measurableSet] with z hz
  have hzs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  by_cases h : (chartAt ℂ x).symm z ∈ G '' A
  · obtain ⟨u, hu, hGu⟩ := h
    have hzS : z ∈ S := ⟨u, ⟨hu, hGu ▸ hzs⟩, by simp only [hGu, (chartAt ℂ x).right_inv hz]⟩
    rw [Set.indicator_of_mem hzS, Set.indicator_of_mem (show (chartAt ℂ x).symm z ∈ G '' A from ⟨u, hu, hGu⟩)]
    rfl
  · have hzS : z ∉ S := by
      rintro ⟨u, hu, hzu⟩
      apply h
      refine ⟨u, hu.1, ?_⟩
      rw [← hzu, (chartAt ℂ x).left_inv hu.2]
    rw [Set.indicator_of_notMem hzS, Set.indicator_of_notMem h]

/-! #### Prover A helpers: the two-to-one count of the flow correspondence -/

/-- A bi-infinite unit-speed horizontal trajectory never reverses: it is not symmetric about any time (in a flow box it
runs along a line at unit speed). -/
theorem s26v_a_no_reversal [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : C(ℝ, S₀)}
    (hc : s26v_IsTraj q c) (u : ℝ) : ¬ ∀ r : ℝ, c (u + r) = c (u - r) := by
  intro h
  obtain ⟨B, Z, ε, σ, σ', -, hε, hσ, -, hl⟩ := s26v_a_two_lines hq (c := c) (c' := c) (t := u) (t' := u)
    (Eventually.of_forall hc) (Eventually.of_forall hc) rfl
  have h1 := (hl (ε / 2) ⟨by linarith, by linarith⟩).2.2.1
  have h2 := (hl (-(ε / 2)) ⟨by linarith, by linarith⟩).2.2.1
  have h3 : Z (c (u + ε / 2)) = Z (c (u + -(ε / 2))) := by rw [h (ε / 2), sub_eq_add_neg]
  rw [h1, h2, add_right_inj, Complex.ofReal_inj] at h3
  rcases hσ with rfl | rfl <;> linarith

/-- A bi-infinite unit-speed horizontal trajectory returning to its starting point is periodic. -/
theorem s26v_a_period [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) {τ : ℝ} (hτ : c τ = c 0) : ∀ s, c (τ + s) = c s := by
  have hc' : s26v_IsTraj q ⟨fun s => c (τ + s), by fun_prop⟩ := fun s => s26v_a_trajAt_shift_add (hc (τ + s))
  rcases s26v_traj_unique hq hc hc' (by show c 0 = c (τ + 0); rw [add_zero, hτ]) with h | h
  · exact h
  · exfalso
    refine s26v_a_no_reversal hq hc (τ / 2) fun r => ?_
    have h1 := h (-(τ / 2) + r)
    have e1 : τ + (-(τ / 2) + r) = τ / 2 + r := by ring
    have e2 : -(-(τ / 2) + r) = τ / 2 - r := by ring
    simp only [ContinuousMap.coe_mk, e1, e2] at h1
    exact h1

/-- The chosen trajectory through a point `c a` of a bi-infinite trajectory `c` is `c (a ± ·)`, so its points at the
times `±t` are `c (a + t)` and `c (a - t)`, in one order or the other. -/
theorem s26v_a_pair_of_point [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) (a t : ℝ) :
    (s26v_traj q (c a) t = c (a + t) ∧ s26v_traj q (c a) (-t) = c (a - t)) ∨
      (s26v_traj q (c a) t = c (a - t) ∧ s26v_traj q (c a) (-t) = c (a + t)) := by
  obtain ⟨htr, h0⟩ := s26v_traj_spec (s26v_a_not_mem_E hc a)
  have hc' : s26v_IsTraj q ⟨fun s => c (a + s), by fun_prop⟩ := fun s => s26v_a_trajAt_shift_add (hc (a + s))
  rcases s26v_traj_unique hq hc' htr (by show c (a + 0) = _; rw [add_zero, h0]) with h | h
  · left
    refine ⟨h t, ?_⟩
    rw [h (-t)]
    show c (a + -t) = c (a - t)
    rw [sub_eq_add_neg]
  · right
    refine ⟨?_, ?_⟩
    · rw [h t]
      show c (a + -t) = c (a - t)
      rw [sub_eq_add_neg]
    · rw [h (-t)]
      show c (a + - -t) = c (a + t)
      rw [neg_neg]

/-- A point off the critical set whose trajectory hits `y` at a time `±t` is one of the two points `c_y(±t)`. -/
theorem s26v_a_hit_point [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {p y : S₀}
    (hp : p ∉ s26v_E q) {t : ℝ} (h : s26v_traj q p t = y ∨ s26v_traj q p (-t) = y) :
    p = s26v_traj q y t ∨ p = s26v_traj q y (-t) := by
  obtain ⟨htr, h0⟩ := s26v_traj_spec hp
  rcases h with h | h
  · rcases s26v_a_pair_of_point hq htr t t with h' | h'
    · right
      rw [← h, h'.2, sub_self, h0]
    · left
      rw [← h, h'.1, sub_self, h0]
  · rcases s26v_a_pair_of_point hq htr (-t) t with h' | h'
    · left
      rw [← h, h'.1, neg_add_cancel, h0]
    · right
      rw [← h, h'.2, neg_add_cancel, h0]

/-- **The local count.**  For one tube `g` with piece `W`, the number of the two shifted pieces `g(W ± t)` containing
`y` equals the number of the two points `pP, pM` lying in `g(W)`, under the incidence properties of the flow. -/
theorem s26v_a_count_local {g : ℂ → S₀} {W : Set ℂ} {t : ℂ} {y pP pM : S₀} (hinj : InjOn g W)
    (hinjP : InjOn (fun w => g (w + t)) W) (hinjM : InjOn (fun w => g (w - t)) W)
    (h2 : ∀ w ∈ W, (g (w + t) = y ∨ g (w - t) = y) → g w = pP ∨ g w = pM)
    (h3 : ∀ w ∈ W, g w = pP → (g (w + t) = y ∨ g (w - t) = y) ∧ (g (w + t) = y → g (w - t) = y → pP = pM))
    (h4 : ∀ w ∈ W, g w = pM → (g (w + t) = y ∨ g (w - t) = y) ∧ (g (w + t) = y → g (w - t) = y → pP = pM))
    (h5 : pP = pM → ∀ w ∈ W, g w = pP → g (w + t) = y ∧ g (w - t) = y) :
    (g '' ((fun w => w + t) '' W)).indicator (1 : S₀ → ℝ≥0∞) y +
        (g '' ((fun w => w - t) '' W)).indicator 1 y =
      (g '' W).indicator 1 pP + (g '' W).indicator 1 pM := by
  have _ : ChartedSpace ℂ S₀ := inferInstance
  have hA : y ∈ g '' ((fun w => w + t) '' W) ↔ ∃ w ∈ W, g (w + t) = y := by
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
      exact ⟨w, hw, h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w + t, ⟨w, hw, rfl⟩, h⟩
  have hB : y ∈ g '' ((fun w => w - t) '' W) ↔ ∃ w ∈ W, g (w - t) = y := by
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
      exact ⟨w, hw, h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w - t, ⟨w, hw, rfl⟩, h⟩
  by_cases hP : pP ∈ g '' W <;> by_cases hM : pM ∈ g '' W
  · obtain ⟨wP, hwP, hgP⟩ := hP
    obtain ⟨wM, hwM, hgM⟩ := hM
    have hboth : (∃ w ∈ W, g (w + t) = y) ∧ ∃ w ∈ W, g (w - t) = y := by
      by_cases hpp : pP = pM
      · obtain ⟨e1, e2⟩ := h5 hpp wP hwP hgP
        exact ⟨⟨wP, hwP, e1⟩, ⟨wP, hwP, e2⟩⟩
      · have hw : wP ≠ wM := fun h => hpp (by rw [← hgP, ← hgM, h])
        rcases (h3 wP hwP hgP).1 with e1 | e1 <;> rcases (h4 wM hwM hgM).1 with e2 | e2
        · exact absurd (hinjP hwP hwM (by simp only [e1, e2])) hw
        · exact ⟨⟨wP, hwP, e1⟩, ⟨wM, hwM, e2⟩⟩
        · exact ⟨⟨wM, hwM, e2⟩, ⟨wP, hwP, e1⟩⟩
        · exact absurd (hinjM hwP hwM (by simp only [e1, e2])) hw
    rw [Set.indicator_of_mem (hA.2 hboth.1), Set.indicator_of_mem (hB.2 hboth.2),
      Set.indicator_of_mem (show pP ∈ g '' W from ⟨wP, hwP, hgP⟩),
      Set.indicator_of_mem (show pM ∈ g '' W from ⟨wM, hwM, hgM⟩)]
    rfl
  · obtain ⟨wP, hwP, hgP⟩ := hP
    have hpp : pP ≠ pM := fun h => hM ⟨wP, hwP, hgP.trans h⟩
    have hAe : (∃ w ∈ W, g (w + t) = y) ↔ g (wP + t) = y := by
      refine ⟨fun ⟨w, hw, h⟩ => ?_, fun h => ⟨wP, hwP, h⟩⟩
      rcases h2 w hw (Or.inl h) with h' | h'
      · rw [← hinj hw hwP (h'.trans hgP.symm)]
        exact h
      · exact absurd ⟨w, hw, h'⟩ hM
    have hBe : (∃ w ∈ W, g (w - t) = y) ↔ g (wP - t) = y := by
      refine ⟨fun ⟨w, hw, h⟩ => ?_, fun h => ⟨wP, hwP, h⟩⟩
      rcases h2 w hw (Or.inr h) with h' | h'
      · rw [← hinj hw hwP (h'.trans hgP.symm)]
        exact h
      · exact absurd ⟨w, hw, h'⟩ hM
    rw [Set.indicator_of_mem (show pP ∈ g '' W from ⟨wP, hwP, hgP⟩), Set.indicator_of_notMem hM]
    rcases (h3 wP hwP hgP).1 with e | e
    · have hn : g (wP - t) ≠ y := fun e' => hpp ((h3 wP hwP hgP).2 e e')
      rw [Set.indicator_of_mem (hA.2 (hAe.2 e)), Set.indicator_of_notMem fun h => hn (hBe.1 (hB.1 h))]
      simp
    · have hn : g (wP + t) ≠ y := fun e' => hpp ((h3 wP hwP hgP).2 e' e)
      rw [Set.indicator_of_notMem fun h => hn (hAe.1 (hA.1 h)), Set.indicator_of_mem (hB.2 (hBe.2 e))]
      simp
  · obtain ⟨wM, hwM, hgM⟩ := hM
    have hpp : pP ≠ pM := fun h => hP ⟨wM, hwM, hgM.trans h.symm⟩
    have hAe : (∃ w ∈ W, g (w + t) = y) ↔ g (wM + t) = y := by
      refine ⟨fun ⟨w, hw, h⟩ => ?_, fun h => ⟨wM, hwM, h⟩⟩
      rcases h2 w hw (Or.inl h) with h' | h'
      · exact absurd ⟨w, hw, h'⟩ hP
      · rw [← hinj hw hwM (h'.trans hgM.symm)]
        exact h
    have hBe : (∃ w ∈ W, g (w - t) = y) ↔ g (wM - t) = y := by
      refine ⟨fun ⟨w, hw, h⟩ => ?_, fun h => ⟨wM, hwM, h⟩⟩
      rcases h2 w hw (Or.inr h) with h' | h'
      · exact absurd ⟨w, hw, h'⟩ hP
      · rw [← hinj hw hwM (h'.trans hgM.symm)]
        exact h
    rw [Set.indicator_of_notMem hP, Set.indicator_of_mem (show pM ∈ g '' W from ⟨wM, hwM, hgM⟩)]
    rcases (h4 wM hwM hgM).1 with e | e
    · have hn : g (wM - t) ≠ y := fun e' => hpp ((h4 wM hwM hgM).2 e e')
      rw [Set.indicator_of_mem (hA.2 (hAe.2 e)), Set.indicator_of_notMem fun h => hn (hBe.1 (hB.1 h))]
      simp
    · have hn : g (wM + t) ≠ y := fun e' => hpp ((h4 wM hwM hgM).2 e' e)
      rw [Set.indicator_of_notMem fun h => hn (hAe.1 (hA.1 h)), Set.indicator_of_mem (hB.2 (hBe.2 e))]
      simp
  · have hAn : y ∉ g '' ((fun w => w + t) '' W) := by
      rw [hA]
      rintro ⟨w, hw, h⟩
      rcases h2 w hw (Or.inl h) with h' | h'
      · exact hP ⟨w, hw, h'⟩
      · exact hM ⟨w, hw, h'⟩
    have hBn : y ∉ g '' ((fun w => w - t) '' W) := by
      rw [hB]
      rintro ⟨w, hw, h⟩
      rcases h2 w hw (Or.inr h) with h' | h'
      · exact hP ⟨w, hw, h'⟩
      · exact hM ⟨w, hw, h'⟩
    rw [Set.indicator_of_notMem hAn, Set.indicator_of_notMem hBn, Set.indicator_of_notMem hP,
      Set.indicator_of_notMem hM]

/-- A point off the critical set lies in exactly one image of a piece of a tube family. -/
theorem s26v_a_tsum_indicator_W {q : S₀ → ℂ → ℂ} {T : ℝ} {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀}
    (hfam : s26v_a_IsTubeFamily q T ρ G) {p : S₀} (hp : p ∉ s26v_E q) :
    ∑' k, (G k '' s26v_a_W G ρ k).indicator (1 : S₀ → ℝ≥0∞) p = 1 := by
  classical
  obtain ⟨k₀, hk₀⟩ := s26v_a_W_cover hfam hp
  have heq : (fun k => (G k '' s26v_a_W G ρ k).indicator (1 : S₀ → ℝ≥0∞) p) =
      fun k => if k = k₀ then 1 else 0 := by
    funext k
    by_cases hk : k = k₀
    · simp only [hk, ↓reduceIte]
      rw [Set.indicator_of_mem hk₀]
      rfl
    · simp only [hk, ↓reduceIte]
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (s26v_a_W_disjoint hk) h hk₀) _
  rw [heq, tsum_ite_eq]

/-- **The two-to-one count.**  For a tube family of time `T`, `t ∈ [-T, T]` and `y` off the critical set, exactly two
of the shifted images `G_k(W_k ± t)` contain `y` (with multiplicity): the pieces containing `c_y(t)` and `c_y(-t)`. -/
theorem s26v_a_count [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) {t : ℝ}
    (ht : t ∈ Icc (-T) T) {y : S₀} (hy : y ∉ s26v_E q) :
    ∑' k, ((G k '' ((fun w => w + (t : ℂ)) '' s26v_a_W G ρ k)).indicator (1 : S₀ → ℝ≥0∞) y +
      (G k '' ((fun w => w - (t : ℂ)) '' s26v_a_W G ρ k)).indicator 1 y) = 2 := by
  obtain ⟨hc, hc0⟩ := s26v_traj_spec hy
  set c := s26v_traj q y with hcdef
  have hpP : c t ∉ s26v_E q := s26v_a_not_mem_E hc t
  have hpM : c (-t) ∉ s26v_E q := s26v_a_not_mem_E hc (-t)
  have hmt : -t ∈ Icc (-T) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- consequences of periodicity
  have hperP : c (2 * t) = y → c t = c (-t) := by
    intro h
    have h1 := s26v_a_period hq hc (τ := 2 * t) (by rw [h, hc0]) (-t)
    rw [show 2 * t + -t = t by ring] at h1
    exact h1
  have hperM : c (-(2 * t)) = y → c t = c (-t) := by
    intro h
    have h1 := s26v_a_period hq hc (τ := -(2 * t)) (by rw [h, hc0]) t
    rw [show -(2 * t) + t = -t by ring] at h1
    exact h1.symm
  have hper : c t = c (-t) → c (2 * t) = y := by
    intro h
    have hc' : s26v_IsTraj q ⟨fun s => c (-t + s), by fun_prop⟩ := fun s => s26v_a_trajAt_shift_add (hc (-t + s))
    have h1 := s26v_a_period hq hc' (τ := 2 * t) (by
      show c (-t + 2 * t) = c (-t + 0)
      rw [show -t + 2 * t = t by ring, add_zero, h]) t
    simp only [ContinuousMap.coe_mk] at h1
    rw [show -t + (2 * t + t) = 2 * t by ring, show -t + t = 0 by ring, hc0] at h1
    exact h1
  have hk : ∀ k, (G k '' ((fun w => w + (t : ℂ)) '' s26v_a_W G ρ k)).indicator (1 : S₀ → ℝ≥0∞) y +
      (G k '' ((fun w => w - (t : ℂ)) '' s26v_a_W G ρ k)).indicator 1 y =
      (G k '' s26v_a_W G ρ k).indicator 1 (c t) + (G k '' s26v_a_W G ρ k).indicator 1 (c (-t)) := by
    intro k
    obtain ⟨p₀, hG⟩ := hfam.1 k
    have hW : ∀ w ∈ s26v_a_W G ρ k, w ∈ ball (0 : ℂ) (ρ k) := fun w hw => hw.1
    have hball : ∀ (s : ℝ), ∀ w ∈ s26v_a_W G ρ k, w + (s : ℂ) ∈ ball (s : ℂ) (ρ k) := by
      intro s w hw
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      simpa using (hW w hw)
    have hinj₀ : InjOn (G k) (s26v_a_W G ρ k) := by
      have h := (s26v_a_tube_ball hG (s := 0) ⟨by linarith, hT⟩).2
      simp only [Complex.ofReal_zero] at h
      exact h.mono hW
    have hinjP : InjOn (fun w => G k (w + (t : ℂ))) (s26v_a_W G ρ k) := by
      intro w₁ h₁ w₂ h₂ h
      exact add_right_cancel ((s26v_a_tube_ball hG ht).2 (hball t w₁ h₁) (hball t w₂ h₂) h)
    have hinjM : InjOn (fun w => G k (w - (t : ℂ))) (s26v_a_W G ρ k) := by
      intro w₁ h₁ w₂ h₂ h
      have e : ∀ w, w - (t : ℂ) = w + ((-t : ℝ) : ℂ) := fun w => by push_cast; ring
      have h' : G k (w₁ + ((-t : ℝ) : ℂ)) = G k (w₂ + ((-t : ℝ) : ℂ)) := by
        simpa only [e] using h
      exact add_right_cancel ((s26v_a_tube_ball hG hmt).2 (hball (-t) w₁ h₁) (hball (-t) w₂ h₂) h')
    have hnotE : ∀ w ∈ s26v_a_W G ρ k, (G k (w + t) = y ∨ G k (w - t) = y) → G k w ∉ s26v_E q := by
      intro w hw h
      rcases h with h | h
      · exact s26v_a_tube_not_mem_E hq hG (hW w hw) ht (by rw [h]; exact hy)
      · refine s26v_a_tube_not_mem_E hq hG (hW w hw) hmt ?_
        have e : w + ((-t : ℝ) : ℂ) = w - t := by push_cast; ring
        rw [e, h]
        exact hy
    -- the pair at `G w = c t` and at `G w = c (-t)`
    have hpairP : ∀ w ∈ s26v_a_W G ρ k, G k w = c t →
        ((G k (w + t) = c (t + t) ∧ G k (w - t) = c (t - t)) ∨
          (G k (w + t) = c (t - t) ∧ G k (w - t) = c (t + t))) := by
      intro w hw hwp
      have hE : G k w ∉ s26v_E q := by rw [hwp]; exact hpP
      rcases s26v_a_tube_pair hq hG (hW w hw) hE ht with h1 | h1 <;>
        rcases s26v_a_pair_of_point hq hc t t with h2 | h2 <;> rw [hwp] at h1
      · exact Or.inl ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
      · exact Or.inr ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
      · exact Or.inr ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩
      · exact Or.inl ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩
    have hpairM : ∀ w ∈ s26v_a_W G ρ k, G k w = c (-t) →
        ((G k (w + t) = c (-t + t) ∧ G k (w - t) = c (-t - t)) ∨
          (G k (w + t) = c (-t - t) ∧ G k (w - t) = c (-t + t))) := by
      intro w hw hwp
      have hE : G k w ∉ s26v_E q := by rw [hwp]; exact hpM
      rcases s26v_a_tube_pair hq hG (hW w hw) hE ht with h1 | h1 <;>
        rcases s26v_a_pair_of_point hq hc (-t) t with h2 | h2 <;> rw [hwp] at h1
      · exact Or.inl ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
      · exact Or.inr ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
      · exact Or.inr ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩
      · exact Or.inl ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩
    have e1 : t + t = 2 * t := by ring
    have e2 : t - t = 0 := by ring
    have e3 : -t + t = 0 := by ring
    have e4 : -t - t = -(2 * t) := by ring
    refine s26v_a_count_local hinj₀ hinjP hinjM ?_ ?_ ?_ ?_
    · intro w hw h
      have hE := hnotE w hw h
      have h' : s26v_traj q (G k w) t = y ∨ s26v_traj q (G k w) (-t) = y := by
        rcases s26v_a_tube_pair hq hG (hW w hw) hE ht with h1 | h1 <;> rw [h1.1, h1.2] <;> tauto
      exact s26v_a_hit_point hq hE h'
    · intro w hw hwp
      rw [e1, e2, hc0] at hpairP
      rcases hpairP w hw hwp with h | h
      · refine ⟨Or.inr h.2, fun h' _ => hperP (h.1.symm.trans h')⟩
      · refine ⟨Or.inl h.1, fun _ h' => hperP (h.2.symm.trans h')⟩
    · intro w hw hwp
      rw [e3, e4, hc0] at hpairM
      rcases hpairM w hw hwp with h | h
      · refine ⟨Or.inl h.1, fun _ h' => hperM (h.2.symm.trans h')⟩
      · refine ⟨Or.inr h.2, fun h' _ => hperM (h.1.symm.trans h')⟩
    · intro hpp w hw hwp
      have h2t := hper hpp
      rw [e1, e2, hc0, h2t] at hpairP
      rcases hpairP w hw hwp with h | h
      · exact h
      · exact ⟨h.1, h.2⟩
  rw [tsum_congr hk, ENNReal.tsum_add, s26v_a_tsum_indicator_W hfam hpP, s26v_a_tsum_indicator_W hfam hpM]
  norm_num

/-! #### Prover A helpers: the pair identity in natural coordinates -/

/-- A function Borel in charts, composed with a map natural on an open set `O`, agrees on `O` with a Borel function
(a countable chart cover, made disjoint). -/
theorem s26v_a_borel_comp [CompactSpace S₀] {q : S₀ → ℂ → ℂ} {U : S₀ → ℝ≥0∞} (hU : s26v_IsBorelInCharts U)
    {G : ℂ → S₀} {O : Set ℂ} (hOo : IsOpen O) (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u) :
    ∃ H : ℂ → ℝ≥0∞, Measurable H ∧ ∀ u ∈ O, U (G u) = H u := by
  classical
  choose g hg hgU using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S₀ => (chartAt ℂ x).source)
    (fun x => (chartAt ℂ x).open_source) (fun p _ => mem_iUnion.2 ⟨p, mem_chart_source ℂ p⟩)
  have htne : (t : Set S₀).Nonempty := by
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 (ht (mem_univ (G 0)))
    exact ⟨x, hx⟩
  obtain ⟨e, he⟩ := (t.finite_toSet.countable).exists_eq_range htne
  have hcov : ∀ p : S₀, ∃ i, p ∈ (chartAt ℂ (e i)).source := by
    intro p
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (ht (mem_univ p))
    have hx' : x ∈ range e := he ▸ hx
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i, hpx⟩
  have hGc : ContinuousOn G O := fun u hu => (hG u hu).1.continuousWithinAt
  set D : ℕ → Set ℂ := fun i => O ∩ G ⁻¹' (chartAt ℂ (e i)).source with hD
  have hDo : ∀ i, IsOpen (D i) := fun i => hGc.isOpen_inter_preimage hOo (chartAt ℂ (e i)).open_source
  set D' : ℕ → Set ℂ := fun i => {u | u ∈ D i ∧ ∀ j < i, u ∉ D j} with hD'
  have hD'm : ∀ i, MeasurableSet (D' i) := by
    intro i
    have heq : D' i = D i ∩ ⋂ j ∈ {j : ℕ | j < i}, (D j)ᶜ := by
      ext u
      simp only [hD', Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff]
    rw [heq]
    exact (hDo i).measurableSet.inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (hDo j).measurableSet.compl)
  set h : ℕ → ℂ → ℝ≥0∞ := fun i u =>
    g (e i) ((D i).piecewise (fun u => chartAt ℂ (e i) (G u)) (fun _ => 0) u) with hh
  have hhm : ∀ i, Measurable (h i) := by
    intro i
    have hc : ContinuousOn (fun u => chartAt ℂ (e i) (G u)) (D i) := fun u hu =>
      (ContinuousAt.comp (g := chartAt ℂ (e i)) (f := G) ((chartAt ℂ (e i)).continuousAt hu.2)
        (hG u hu.1).1).continuousWithinAt
    exact (hg (e i)).comp (hc.measurable_piecewise continuousOn_const (hDo i).measurableSet)
  refine ⟨fun u => ∑' i, (D' i).indicator (h i) u,
    Measurable.tsum fun i => (hhm i).indicator (hD'm i), fun u hu => ?_⟩
  have hex : ∃ i, u ∈ D i := by
    obtain ⟨i, hi⟩ := hcov (G u)
    exact ⟨i, hu, hi⟩
  set i₀ := Nat.find hex with hi₀
  have hi₀D : u ∈ D i₀ := Nat.find_spec hex
  have hi₀D' : u ∈ D' i₀ := ⟨hi₀D, fun j hj => Nat.find_min hex hj⟩
  show U (G u) = ∑' i, (D' i).indicator (h i) u
  rw [tsum_eq_single i₀]
  · rw [Set.indicator_of_mem hi₀D']
    simp only [hh, Set.piecewise_eq_of_mem _ _ _ hi₀D]
    have h1 := hgU (e i₀) (chartAt ℂ (e i₀) (G u)) ((chartAt ℂ (e i₀)).map_source hi₀D.2)
    rw [(chartAt ℂ (e i₀)).left_inv hi₀D.2] at h1
    exact h1
  · intro i hi
    refine Set.indicator_of_notMem (fun hu' => ?_) _
    rcases lt_or_gt_of_ne hi with h' | h'
    · exact Nat.find_min hex h' hu'.1
    · exact hu'.2 i₀ h' hi₀D

/-- **Null sets pull back along natural maps**, for sets null in every chart (finitely many charts cover). -/
theorem s26v_a_null_preimage_all [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) {G : ℂ → S₀} {O A : Set ℂ} (hO : IsOpen O) (hAO : A ⊆ O) (hAm : MeasurableSet A)
    (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u) (hinj : InjOn G O) {N : Set S₀}
    (hN : ∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0) :
    volume {u | u ∈ A ∧ G u ∈ N} = 0 := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S₀ => (chartAt ℂ x).source)
    (fun x => (chartAt ℂ x).open_source) (fun p _ => mem_iUnion.2 ⟨p, mem_chart_source ℂ p⟩)
  have hGc : ContinuousOn G O := fun u hu => (hG u hu).1.continuousWithinAt
  have hsub : {u | u ∈ A ∧ G u ∈ N} ⊆ ⋃ x ∈ (t : Set S₀),
      {u | u ∈ {u | u ∈ A ∧ G u ∈ (chartAt ℂ x).source} ∧
        chartAt ℂ x (G u) ∈ chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)} := by
    rintro u ⟨huA, huN⟩
    obtain ⟨x, hx, hux⟩ := mem_iUnion₂.1 (ht (mem_univ (G u)))
    exact mem_iUnion₂.2 ⟨x, hx, ⟨huA, hux⟩, ⟨G u, ⟨huN, hux⟩, rfl⟩⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff t.countable_toSet).2 fun x _ => ?_)
  have hAx : MeasurableSet {u | u ∈ A ∧ G u ∈ (chartAt ℂ x).source} := by
    have h1 := (hGc.isOpen_inter_preimage hO (chartAt ℂ x).open_source).measurableSet
    have heq : {u | u ∈ A ∧ G u ∈ (chartAt ℂ x).source} = A ∩ (O ∩ G ⁻¹' (chartAt ℂ x).source) := by
      ext u
      simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
      exact ⟨fun h => ⟨h.1, hAO h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact hAm.inter h1
  exact s26v_a_null_preimage hq hAx (fun u hu => hG u (hAO hu.1)) (hinj.mono fun u hu => hAO hu.1) x
    (fun u hu => hu.2) (hN x)

/-- Translation invariance of set integrals: `∫_W f(w + a) dw = ∫_{W + a} f`. -/
theorem s26v_a_lintegral_translate {W : Set ℂ} (hW : MeasurableSet W) (a : ℂ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ w in W, f (w + a) = ∫⁻ w in (fun w => w + a) '' W, f w := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW (f := fun w => w + a)
    (f' := fun _ => ContinuousLinearMap.id ℝ ℂ)
    (fun w _ => ((hasFDerivAt_id (𝕜 := ℝ) w).add_const a).hasFDerivWithinAt) (add_left_injective a).injOn f
  have hdet : (ContinuousLinearMap.id ℝ ℂ).det = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [h]
  simp [hdet]

/-- On the disc `ball s ρ` around a real time `s ∈ [-T, T]`, the tubes of a tube family are natural and injective; the
translate of a piece by `s` lies in that disc. -/
theorem s26v_a_family_ball {q : S₀ → ℂ → ℂ} {T : ℝ} {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀}
    (hfam : s26v_a_IsTubeFamily q T ρ G) (k : ℕ) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    (∀ u ∈ ball (s : ℂ) (ρ k), s26v_a_IsNatAt q (G k) u) ∧ InjOn (G k) (ball (s : ℂ) (ρ k)) ∧
      (fun w => w + (s : ℂ)) '' s26v_a_W G ρ k ⊆ ball (s : ℂ) (ρ k) := by
  obtain ⟨p₀, hG⟩ := hfam.1 k
  refine ⟨(s26v_a_tube_ball hG hs).1, (s26v_a_tube_ball hG hs).2, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
  simpa using hw.1

/-- The translate of a piece of a tube family is measurable. -/
theorem s26v_a_W_translate_measurable [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) (k : ℕ) (a : ℂ) :
    MeasurableSet ((fun w => w + a) '' s26v_a_W G ρ k) :=
  (s26v_a_W_measurable hq hT hfam k).image_of_continuousOn_injOn
    (by fun_prop : Continuous fun w : ℂ => w + a).continuousOn (add_left_injective a).injOn

/-- In a tube family, `∫_{W_k} U(G_k(w + s)) dw = ∬ U · 1_{G_k(W_k + s)} dA_q` for `s ∈ [-T, T]` (translation and the
target formula). -/
theorem s26v_a_family_shift [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) (U : S₀ → ℝ≥0∞)
    (k : ℕ) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    ∫⁻ w in s26v_a_W G ρ k, U (G k (w + s)) =
      surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z) *
        (G k '' ((fun w => w + (s : ℂ)) '' s26v_a_W G ρ k)).indicator 1 ((chartAt ℂ x).symm z)) := by
  have : Nonempty S₀ := ⟨G k 0⟩
  obtain ⟨hnat, hinj, hsub⟩ := s26v_a_family_ball hfam k hs
  rw [s26v_a_lintegral_translate (s26v_a_W_measurable hq hT hfam k) (s : ℂ) (fun u => U (G k u))]
  exact (s26v_a_target_formula hq isOpen_ball hsub (s26v_a_W_translate_measurable hq hT hfam k _) hnat hinj
    U).symm

/-- `surfaceIntegral` is unchanged by a change of the integrand off a set null in every chart (a copy of the glue
`s26v_surfaceIntegral_congr_off`, which is stated further below). -/
theorem s26v_a_surfaceIntegral_congr_off (q : S₀ → ℂ → ℂ) {u w : S₀ → ℂ → ℝ≥0∞} (N : Set S₀)
    (hN : ∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0)
    (huw : ∀ x : S₀, ∀ p ∈ (chartAt ℂ x).source, p ∉ N → u x (chartAt ℂ x p) = w x (chartAt ℂ x p)) :
    surfaceIntegral q u = surfaceIntegral q w := by
  have key : ∀ (u w : S₀ → ℂ → ℝ≥0∞), (∀ x : S₀, ∀ p ∈ (chartAt ℂ x).source, p ∉ N →
      u x (chartAt ℂ x p) ≤ w x (chartAt ℂ x p)) → surfaceIntegral q u ≤ surfaceIntegral q w := by
    intro u w huw
    unfold surfaceIntegral
    refine iInf_mono fun x => iInf_mono fun P => iInf_mono fun hP => ENNReal.tsum_le_tsum fun i => ?_
    refine lintegral_mono_ae ?_
    have h1 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), z ∈ chartAt ℂ (x i) '' P i :=
      ae_restrict_mem (hP.1 i).2
    have h2 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        z ∉ chartAt ℂ (x i) '' (N ∩ (chartAt ℂ (x i)).source) :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (hN (x i)))
    filter_upwards [h1, h2] with z hz1 hz2
    obtain ⟨p, hpP, rfl⟩ := hz1
    have hps : p ∈ (chartAt ℂ (x i)).source := (hP.1 i).1 hpP
    have hpN : p ∉ N := fun h => hz2 ⟨p, ⟨h, hps⟩, rfl⟩
    exact mul_le_mul_left (huw (x i) p hps hpN) _
  exact le_antisymm (key u w fun x p hp hpN => (huw x p hp hpN).le)
    (key w u fun x p hp hpN => (huw x p hp hpN).ge)

/-- **The pair identity in natural coordinates.**  For a tube family of time `T` and `t ∈ [-T, T]`,
`Σ_k ∫_{W_k} (U(G_k(w + t)) + U(G_k(w - t))) dw = 2 ∬ U dA_q`: each integral is the surface integral of `U` times the
indicator of a shifted piece; sum them (countable additivity) and use the two-to-one count off the critical set. -/
theorem s26v_a_pair_core [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (U : S₀ → ℝ≥0∞) (hU : s26v_IsBorelInCharts U)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    ∑' k, ((∫⁻ w in s26v_a_W G ρ k, U (G k (w + t))) + ∫⁻ w in s26v_a_W G ρ k, U (G k (w + ((-t : ℝ) : ℂ)))) =
      2 * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) := by
  have hne' : Nonempty S₀ := inferInstance
  have hmt : -t ∈ Icc (-T) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  set F₁ : ℕ → S₀ → ℝ≥0∞ := fun k p => U p * (G k '' ((fun w => w + (t : ℂ)) '' s26v_a_W G ρ k)).indicator 1 p
    with hF₁
  set F₂ : ℕ → S₀ → ℝ≥0∞ := fun k p =>
    U p * (G k '' ((fun w => w + ((-t : ℝ) : ℂ)) '' s26v_a_W G ρ k)).indicator 1 p with hF₂
  have hm₁ : ∀ k x, AEMeasurable (fun z => F₁ k ((chartAt ℂ x).symm z)) (volume.restrict (chartAt ℂ x).target) := by
    intro k x
    obtain ⟨hnat, hinj, hsub⟩ := s26v_a_family_ball hfam k ht
    exact (s26v_a_aemeasurable_chart hU x).mul (s26v_a_aemeasurable_indicator isOpen_ball hsub
      (s26v_a_W_translate_measurable hq hT hfam k _) hnat hinj x)
  have hm₂ : ∀ k x, AEMeasurable (fun z => F₂ k ((chartAt ℂ x).symm z)) (volume.restrict (chartAt ℂ x).target) := by
    intro k x
    obtain ⟨hnat, hinj, hsub⟩ := s26v_a_family_ball hfam k hmt
    exact (s26v_a_aemeasurable_chart hU x).mul (s26v_a_aemeasurable_indicator isOpen_ball hsub
      (s26v_a_W_translate_measurable hq hT hfam k _) hnat hinj x)
  have h1 : ∀ k, ((∫⁻ w in s26v_a_W G ρ k, U (G k (w + t))) + ∫⁻ w in s26v_a_W G ρ k, U (G k (w + ((-t : ℝ) : ℂ))))
      = surfaceIntegral q (fun x z => F₁ k ((chartAt ℂ x).symm z) + F₂ k ((chartAt ℂ x).symm z)) := by
    intro k
    rw [s26v_a_surfaceIntegral_add hq (F₁ k) (F₂ k) (hm₁ k), s26v_a_family_shift hq hT hfam U k ht,
      s26v_a_family_shift hq hT hfam U k hmt]
  rw [tsum_congr h1, ← s26v_a_surfaceIntegral_tsum hq (fun k p => F₁ k p + F₂ k p)
    (fun k x => (hm₁ k x).add (hm₂ k x)), ← s26v_a_surfaceIntegral_const_mul hq U (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  refine s26v_a_surfaceIntegral_congr_off q (s26v_E q) (s26v_E_null hq hne) fun x p hp hpE => ?_
  simp only [(chartAt ℂ x).left_inv hp]
  have hc := s26v_a_count hq hT hfam ht hpE
  have e : ∀ k, (G k '' ((fun w => w - (t : ℂ)) '' s26v_a_W G ρ k)) =
      (G k '' ((fun w => w + ((-t : ℝ) : ℂ)) '' s26v_a_W G ρ k)) := fun k => by
    congr 2
    funext w
    push_cast
    ring
  simp only [e] at hc
  rw [← hc, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  simp only [hF₁, hF₂]
  ring

/-- **[V5a, stub]** (T3 core: the 2-to-1 flow correspondence).  For every time `t` and every `U` Borel in charts,
`∬ (U(c_p(t)) + U(c_p(-t))) dA_q(p) = 2 ∬ U dA_q`.  (The integrand does not depend on the orientation chosen by
`s26v_traj` ([V2c]); on `s26v_E q` it is `2U(p)`.  Off `s26v_E q`, near each `p₀` the two maps `p ↦ c_p(±t)` are, in
flow boxes along the compact segment `c_{p₀}([-t, t])`, translations `Z ↦ Z ± t` in natural parameters, hence preserve
`dA_q = |dZ|²`; and every `y` off `s26v_E q` is hit exactly twice, by `p = c_y(t)` and `p = c_y(-t)`, each with one
sign.) -/
theorem s26v_pair_average [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (U : S₀ → ℝ≥0∞) (hU : s26v_IsBorelInCharts U)
    (t : ℝ) :
    surfaceIntegral q (fun x z => U (s26v_traj q ((chartAt ℂ x).symm z) t) +
        U (s26v_traj q ((chartAt ℂ x).symm z) (-t))) =
      2 * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) := by
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  have ht : t ∈ Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  obtain ⟨ρ, G, hfam⟩ := s26v_a_tubeFamily_exists hq hne hT
  refine (s26v_a_dev_formula hq hne hT hfam (fun p => U (s26v_traj q p t) + U (s26v_traj q p (-t)))).trans ?_
  rw [← s26v_a_pair_core hq hne U hU hT hfam ht]
  refine tsum_congr fun k => ?_
  obtain ⟨p₀, hG⟩ := hfam.1 k
  have hWm := s26v_a_W_measurable hq hT hfam k
  obtain ⟨hnat, -, hsub⟩ := s26v_a_family_ball hfam k ht
  obtain ⟨H, hH, hHU⟩ := s26v_a_borel_comp hU isOpen_ball hnat
  have hmeas : AEMeasurable (fun w => U (G k (w + t))) (volume.restrict (s26v_a_W G ρ k)) := by
    refine (hH.comp (measurable_id.add_const (t : ℂ))).aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem hWm] with w hw
    exact (hHU (w + t) (hsub ⟨w, hw, rfl⟩)).symm
  rw [← lintegral_add_left' hmeas]
  have hc0 := s26v_a_family_center hq hT hfam k
  have hnull : volume {u | u ∈ s26v_a_W G ρ k ∧ G k u ∈ s26v_E q} = 0 :=
    s26v_a_null_preimage_all hq isOpen_ball (fun w hw => hw.1) hWm hc0.1 hc0.2.1 (s26v_E_null hq hne)
  have hae : ∀ᵐ w ∂(volume.restrict (s26v_a_W G ρ k)), G k w ∉ s26v_E q := by
    rw [ae_iff, Measure.restrict_apply' hWm]
    exact measure_mono_null (t := {u | u ∈ s26v_a_W G ρ k ∧ G k u ∈ s26v_E q})
      (fun w hw => ⟨hw.2, not_not.1 hw.1⟩) hnull
  refine lintegral_congr_ae ?_
  filter_upwards [hae, ae_restrict_mem hWm] with w hwE hw
  have e : w + ((-t : ℝ) : ℂ) = w - t := by
    push_cast
    ring
  show U (s26v_traj q (G k w) t) + U (s26v_traj q (G k w) (-t)) = U (G k (w + t)) + U (G k (w + ((-t : ℝ) : ℂ)))
  rw [e]
  rcases s26v_a_tube_pair hq hG hw.1 hwE ht with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

/-! #### Prover A helpers: the averaged flow invariance -/

/-- Reflection invariance of integrals over symmetric intervals: `∫_{-L}^{L} f(-t) dt = ∫_{-L}^{L} f(t) dt`. -/
theorem s26v_a_lintegral_neg (L : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo (-L) L, f (-t) = ∫⁻ t in Ioo (-L) L, f t := by
  have hd : ∀ x : ℝ, HasFDerivWithinAt (fun t : ℝ => -t)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-1 : ℝ)) (Ioo (-L) L) x :=
    fun x => (hasDerivAt_neg x).hasFDerivAt.hasFDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_Ioo (f := fun t : ℝ => -t)
    (fun x _ => hd x) neg_injective.injOn f
  have himg : (fun t : ℝ => -t) '' Ioo (-L) L = Ioo (-L) L := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    · intro ht
      exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
  rw [himg] at h
  rw [h]
  have hdet : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-1 : ℝ)).det = -1 := by
    rw [ContinuousLinearMap.det_smulRight]
    simp
  simp [hdet]

/-- In a tube family of time `T`, `u ↦ U (G_k u)` agrees on the strip around `[-T, T]` with a Borel function. -/
theorem s26v_a_family_borel [CompactSpace S₀] {q : S₀ → ℂ → ℂ} {U : S₀ → ℝ≥0∞} (hU : s26v_IsBorelInCharts U)
    {T : ℝ} {ρ : ℕ → ℝ} {G : ℕ → ℂ → S₀} (hfam : s26v_a_IsTubeFamily q T ρ G) (k : ℕ) :
    ∃ H : ℂ → ℝ≥0∞, Measurable H ∧ ∀ w ∈ s26v_a_W G ρ k, ∀ t ∈ Icc (-T) T, U (G k (w + t)) = H (w + t) := by
  obtain ⟨p₀, hG⟩ := hfam.1 k
  obtain ⟨H, hH, hHU⟩ := s26v_a_borel_comp hU (O := {u : ℂ | u.re ∈ Ioo (-T - 2 * ρ k) (T + 2 * ρ k) ∧
    u.im ∈ Ioo (-(2 * ρ k)) (2 * ρ k)}) ((isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)) (fun u hu => hG.2.2.1 u hu.1 hu.2)
  refine ⟨H, hH, fun w hw t ht => hHU (w + t) ?_⟩
  have hw' : ‖w‖ < ρ k := by simpa using hw.1
  have hre : |w.re| < ρ k := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
  have him : |w.im| < ρ k := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw'
  rw [abs_lt] at hre him
  obtain ⟨hre1, hre2⟩ := hre
  obtain ⟨him1, him2⟩ := him
  obtain ⟨ht1, ht2⟩ := ht
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **[V5b, stub]** (T3, the averaged flow invariance).  `∬ (∫_{-L}^{L} U(c_p(t)) dt) dA_q(p) = 2L ∬ U dA_q`: split
`(-L, L)` into `(-L, 0) ∪ (0, L)`, reflect, apply Tonelli on a fixed partition ([V0]; the pair integrand is jointly
measurable through the flow boxes) and [V5a] for every `t ∈ (0, L)`. -/
theorem s26v_flow_average [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (U : S₀ → ℝ≥0∞) (hU : s26v_IsBorelInCharts U)
    {L : ℝ} (hL : 0 < L) :
    surfaceIntegral q (fun x z => ∫⁻ t in Ioo (-L) L, U (s26v_traj q ((chartAt ℂ x).symm z) t)) =
      ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) := by
  have hT : (0 : ℝ) ≤ L := hL.le
  obtain ⟨ρ, G, hfam⟩ := s26v_a_tubeFamily_exists hq hne hT
  choose H hH hHU using s26v_a_family_borel hU hfam
  have hWm := s26v_a_W_measurable hq hT hfam
  set φ : ℝ → ℝ≥0∞ := fun t => ∑' k, ∫⁻ w in s26v_a_W G ρ k, H k (w + t) with hφdef
  have hφm : Measurable φ := by
    refine Measurable.tsum fun k => ?_
    exact ((hH k).comp (measurable_fst.add (Complex.measurable_ofReal.comp measurable_snd))).lintegral_prod_left'
  -- the left side is `∫_{-L}^{L} φ`
  have h1 : surfaceIntegral q (fun x z => ∫⁻ t in Ioo (-L) L, U (s26v_traj q ((chartAt ℂ x).symm z) t)) =
      ∫⁻ t in Ioo (-L) L, φ t := by
    refine (s26v_a_dev_formula hq hne hT hfam (fun p => ∫⁻ t in Ioo (-L) L, U (s26v_traj q p t))).trans ?_
    have hk : ∀ k, ∫⁻ w in s26v_a_W G ρ k, (fun p => ∫⁻ t in Ioo (-L) L, U (s26v_traj q p t)) (G k w) =
        ∫⁻ t in Ioo (-L) L, ∫⁻ w in s26v_a_W G ρ k, H k (w + t) := by
      intro k
      obtain ⟨p₀, hG⟩ := hfam.1 k
      have hc0 := s26v_a_family_center hq hT hfam k
      have hnull : volume {u | u ∈ s26v_a_W G ρ k ∧ G k u ∈ s26v_E q} = 0 :=
        s26v_a_null_preimage_all hq isOpen_ball (fun w hw => hw.1) (hWm k) hc0.1 hc0.2.1 (s26v_E_null hq hne)
      have hae : ∀ᵐ w ∂(volume.restrict (s26v_a_W G ρ k)), G k w ∉ s26v_E q := by
        rw [ae_iff, Measure.restrict_apply' (hWm k)]
        exact measure_mono_null (t := {u | u ∈ s26v_a_W G ρ k ∧ G k u ∈ s26v_E q})
          (fun w hw => ⟨hw.2, not_not.1 hw.1⟩) hnull
      have hstep : ∫⁻ w in s26v_a_W G ρ k, (fun p => ∫⁻ t in Ioo (-L) L, U (s26v_traj q p t)) (G k w) =
          ∫⁻ w in s26v_a_W G ρ k, ∫⁻ t in Ioo (-L) L, H k (w + t) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae, ae_restrict_mem (hWm k)] with w hwE hw
        show ∫⁻ t in Ioo (-L) L, U (s26v_traj q (G k w) t) = ∫⁻ t in Ioo (-L) L, H k (w + t)
        have hw' : ‖w‖ < ρ k := by simpa using hw.1
        have hre : |w.re| < ρ k := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
        have him : |w.im| < ρ k := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw'
        rw [abs_lt] at hre him
        obtain ⟨hre1, hre2⟩ := hre
        obtain ⟨him1, him2⟩ := him
        have hρ := hG.1
        rcases s26v_a_tube_traj hq hG ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hwE with h | h
        · refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          rw [h t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
          exact hHU k w hw t ⟨ht.1.le, ht.2.le⟩
        · have h2 : ∫⁻ t in Ioo (-L) L, U (s26v_traj q (G k w) t) =
              ∫⁻ t in Ioo (-L) L, H k (w + ((-t : ℝ) : ℂ)) := by
            refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
            rw [h t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
            have e : w - (t : ℂ) = w + ((-t : ℝ) : ℂ) := by
              push_cast
              ring
            rw [e]
            exact hHU k w hw (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
          rw [h2]
          exact s26v_a_lintegral_neg L (fun t => H k (w + (t : ℂ)))
      rw [hstep]
      exact lintegral_lintegral_swap
        ((hH k).comp (measurable_fst.add (Complex.measurable_ofReal.comp measurable_snd))).aemeasurable
    have hmeas : ∀ k, AEMeasurable (fun t : ℝ => ∫⁻ w in s26v_a_W G ρ k, H k (w + t))
        (volume.restrict (Ioo (-L) L)) := fun k =>
      (Measurable.lintegral_prod_left' (μ := volume.restrict (s26v_a_W G ρ k))
        (f := fun p : ℂ × ℝ => H k (p.1 + (p.2 : ℂ))) ((hH k).comp (by fun_prop))).aemeasurable
    rw [tsum_congr hk]
    exact (lintegral_tsum hmeas).symm
  -- the pair identity at each time
  have h2 : ∀ t ∈ Ioo (-L) L, φ t + φ (-t) = 2 * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) := by
    intro t ht
    have ht' : t ∈ Icc (-L) L := ⟨ht.1.le, ht.2.le⟩
    have hmt : -t ∈ Icc (-L) L := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [← s26v_a_pair_core hq hne U hU hT hfam ht', hφdef, ← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    congr 1
    · exact setLIntegral_congr_fun (hWm k) fun w hw => (hHU k w hw t ht').symm
    · exact setLIntegral_congr_fun (hWm k) fun w hw => (hHU k w hw (-t) hmt).symm
  -- symmetrize
  have h3 : 2 * ∫⁻ t in Ioo (-L) L, φ t =
      2 * (ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z))) := by
    calc 2 * ∫⁻ t in Ioo (-L) L, φ t = (∫⁻ t in Ioo (-L) L, φ t) + ∫⁻ t in Ioo (-L) L, φ (-t) := by
          rw [s26v_a_lintegral_neg L φ, two_mul]
      _ = ∫⁻ t in Ioo (-L) L, (φ t + φ (-t)) := (lintegral_add_left hφm _).symm
      _ = ∫⁻ _ in Ioo (-L) L, 2 * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z)) :=
          setLIntegral_congr_fun measurableSet_Ioo h2
      _ = 2 * (ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => U ((chartAt ℂ x).symm z))) := by
          rw [setLIntegral_const, Real.volume_Ioo, show L - -L = 2 * L by ring]
          ring
  rw [h1]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h3

/-! #### Prover A helpers: almost every trajectory avoids a null set -/

/-- **A Borel hull in natural coordinates.**  For `G` natural on an open set `O` and `N` null in every chart, there is a
Borel set `B ⊆ ℂ` containing the points of `O` mapped into `N`, and null on every open subset of `O` on which `G` is
injective (finitely many charts; measurable null hulls of the chart images of `N`). -/
theorem s26v_a_hull [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {G : ℂ → S₀} {O : Set ℂ} (hOo : IsOpen O) (hG : ∀ u ∈ O, s26v_a_IsNatAt q G u) {N : Set S₀}
    (hN : ∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0) :
    ∃ B : Set ℂ, MeasurableSet B ∧ (∀ u ∈ O, G u ∈ N → u ∈ B) ∧
      ∀ O' : Set ℂ, IsOpen O' → O' ⊆ O → InjOn G O' → volume (B ∩ O') = 0 := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S₀ => (chartAt ℂ x).source)
    (fun x => (chartAt ℂ x).open_source) (fun p _ => mem_iUnion.2 ⟨p, mem_chart_source ℂ p⟩)
  have hGc : ContinuousOn G O := fun u hu => (hG u hu).1.continuousWithinAt
  set M : S₀ → Set ℂ := fun x => toMeasurable volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) with hM
  set D : S₀ → Set ℂ := fun x => O ∩ G ⁻¹' (chartAt ℂ x).source with hD
  have hDo : ∀ x, IsOpen (D x) := fun x => hGc.isOpen_inter_preimage hOo (chartAt ℂ x).open_source
  refine ⟨⋃ x ∈ (t : Set S₀), {u | u ∈ D x ∧ chartAt ℂ x (G u) ∈ M x}, ?_, ?_, ?_⟩
  · refine MeasurableSet.biUnion t.countable_toSet fun x _ => ?_
    exact s26v_a_measurableSet_inter_preimage (hDo x).measurableSet
      (s26v_a_natAt_continuousOn (fun u hu => hG u hu.1) x fun u hu => hu.2) (measurableSet_toMeasurable _ _)
  · intro u hu huN
    obtain ⟨x, hx, hux⟩ := mem_iUnion₂.1 (ht (mem_univ (G u)))
    exact mem_iUnion₂.2 ⟨x, hx, ⟨hu, hux⟩, subset_toMeasurable _ _ ⟨G u, ⟨huN, hux⟩, rfl⟩⟩
  · intro O' hO' hO'O hinj
    rw [iUnion₂_inter]
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun x _ => ?_
    have hA : MeasurableSet {u | u ∈ O' ∧ G u ∈ (chartAt ℂ x).source} :=
      ((hGc.mono hO'O).isOpen_inter_preimage hO' (chartAt ℂ x).open_source).measurableSet
    have h0 := s26v_a_null_preimage hq hA (fun u hu => hG u (hO'O hu.1)) (hinj.mono fun u hu => hu.1) x
      (fun u hu => hu.2) (M := M x) (by rw [hM, measure_toMeasurable]; exact hN x)
    refine measure_mono_null ?_ h0
    intro u hu
    exact ⟨⟨hu.2, hu.1.1.2⟩, hu.1.2⟩

/-- **Null sections (Tonelli).**  If for every `t ∈ (-L, L)` the points `w ∈ W` with `w + σ t ∈ B` form a null set,
then for almost every `w ∈ W` the times `t ∈ (-L, L)` with `w + σ t ∈ B` form a null set. -/
theorem s26v_a_ae_section {W B : Set ℂ} (hW : MeasurableSet W) (hB : MeasurableSet B) {L σ : ℝ}
    (hnull : ∀ t ∈ Ioo (-L) L, volume {w | w ∈ W ∧ w + ((σ * t : ℝ) : ℂ) ∈ B} = 0) :
    ∀ᵐ w ∂(volume.restrict W), volume {t | t ∈ Ioo (-L) L ∧ w + ((σ * t : ℝ) : ℂ) ∈ B} = 0 := by
  set S : Set (ℂ × ℝ) := {p | p.1 + ((σ * p.2 : ℝ) : ℂ) ∈ B} with hSdef
  have hS : MeasurableSet S :=
    hB.preimage (by fun_prop : Measurable fun p : ℂ × ℝ => p.1 + ((σ * p.2 : ℝ) : ℂ))
  have h0 : ((volume.restrict W).prod (volume.restrict (Ioo (-L) L))) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    have h1 : ∀ t ∈ Ioo (-L) L, (volume.restrict W) ((fun w => (w, t)) ⁻¹' S) = 0 := by
      intro t ht
      rw [Measure.restrict_apply' hW]
      refine measure_mono_null ?_ (hnull t ht)
      intro w hw
      exact ⟨hw.2, hw.1⟩
    rw [setLIntegral_congr_fun measurableSet_Ioo h1]
    simp
  have h2 := (Measure.measure_prod_null hS).1 h0
  filter_upwards [h2] with w hw
  have hw' : (volume.restrict (Ioo (-L) L)) (Prod.mk w ⁻¹' S) = 0 := hw
  rw [Measure.restrict_apply' measurableSet_Ioo] at hw'
  refine measure_mono_null ?_ hw'
  intro t ht
  exact ⟨ht.2, ht.1⟩

/-- **[V9c, stub]** (T3, a.e. trajectories avoid null sets).  If `N` is null in every chart, then for almost every
`p` the trajectory `c_p` spends a null set of times `t ∈ (-L, L)` in `N`.  ([V5b] for the indicator of a Borel hull
of `N` that is null in every chart, and `∬ G dA_q = 0 ⇒ G = 0` a.e. for the measurable `G(p) = |{t : c_p(t) ∈ N}|`.) -/
theorem s26v_ae_traj_null [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (N : Set S₀)
    (hN : ∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0) {L : ℝ} (hL : 0 < L) :
    ∃ N' : Set S₀, (∀ x : S₀, volume (chartAt ℂ x '' (N' ∩ (chartAt ℂ x).source)) = 0) ∧
      ∀ p, p ∉ N' → volume {t | t ∈ Ioo (-L) L ∧ s26v_traj q p t ∈ N} = 0 := by
  have hT : (0 : ℝ) ≤ L := hL.le
  obtain ⟨ρ, G, hfam⟩ := s26v_a_tubeFamily_exists hq hne hT
  have hWm := s26v_a_W_measurable hq hT hfam
  -- Borel hulls of the preimages of `N` in the strips of the tubes
  have hhull : ∀ k, ∃ B : Set ℂ, MeasurableSet B ∧
      (∀ u : ℂ, u.re ∈ Ioo (-L - 2 * ρ k) (L + 2 * ρ k) → u.im ∈ Ioo (-(2 * ρ k)) (2 * ρ k) →
        G k u ∈ N → u ∈ B) ∧ ∀ s ∈ Icc (-L) L, volume (B ∩ ball (s : ℂ) (ρ k)) = 0 := by
    intro k
    obtain ⟨p₀, hG⟩ := hfam.1 k
    have hOo : IsOpen {u : ℂ | u.re ∈ Ioo (-L - 2 * ρ k) (L + 2 * ρ k) ∧ u.im ∈ Ioo (-(2 * ρ k)) (2 * ρ k)} :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    obtain ⟨B, hBm, hBN, hBnull⟩ := s26v_a_hull hq hOo (fun u hu => hG.2.2.1 u hu.1 hu.2) hN
    refine ⟨B, hBm, fun u h1 h2 h3 => hBN u ⟨h1, h2⟩ h3, fun s hs =>
      hBnull _ isOpen_ball (fun u hu => ?_) (s26v_a_tube_ball hG hs).2⟩
    have hu' : ‖u - s‖ < ρ k := mem_ball_iff_norm.1 hu
    have hre : |(u - (s : ℂ)).re| < ρ k := lt_of_le_of_lt (Complex.abs_re_le_norm _) hu'
    have him : |(u - (s : ℂ)).im| < ρ k := lt_of_le_of_lt (Complex.abs_im_le_norm _) hu'
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_lt] at him
    have hρ := hG.1
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨hre1, hre2⟩ := hre
    obtain ⟨him1, him2⟩ := him
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  choose B hBm hBN hBnull using hhull
  -- for almost every point of a piece, both horizontal time sections of the hull are null
  have hsec : ∀ k (σ : ℝ), (σ = 1 ∨ σ = -1) → ∀ᵐ w ∂(volume.restrict (s26v_a_W G ρ k)),
      volume {t | t ∈ Ioo (-L) L ∧ w + ((σ * t : ℝ) : ℂ) ∈ B k} = 0 := by
    intro k σ hσ
    refine s26v_a_ae_section (hWm k) (hBm k) fun t ht => ?_
    have hst : σ * t ∈ Icc (-L) L := by
      rcases hσ with rfl | rfl <;> constructor <;> linarith [ht.1, ht.2]
    refine measure_mono_null (t := (fun w => w + ((σ * t : ℝ) : ℂ)) ⁻¹' (B k ∩ ball ((σ * t : ℝ) : ℂ) (ρ k)))
      (fun w hw => ⟨hw.2, ?_⟩) ?_
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      simpa using hw.1.1
    · rw [measure_preimage_add_right]
      exact hBnull k _ hst
  set Z : ℕ → Set ℂ := fun k => {w | w ∈ s26v_a_W G ρ k ∧
      (volume {t | t ∈ Ioo (-L) L ∧ w + (((1 : ℝ) * t : ℝ) : ℂ) ∈ B k} ≠ 0 ∨
        volume {t | t ∈ Ioo (-L) L ∧ w + (((-1 : ℝ) * t : ℝ) : ℂ) ∈ B k} ≠ 0)} with hZdef
  have hZ : ∀ k, volume (Z k) = 0 := by
    intro k
    have h1 := hsec k 1 (Or.inl rfl)
    have h2 := hsec k (-1) (Or.inr rfl)
    rw [ae_iff, Measure.restrict_apply' (hWm k)] at h1 h2
    refine measure_mono_null ?_ (measure_union_null h1 h2)
    rintro w ⟨hw, h | h⟩
    · exact Or.inl ⟨h, hw⟩
    · exact Or.inr ⟨h, hw⟩
  refine ⟨s26v_E q ∪ ⋃ k, G k '' Z k, fun x => ?_, fun p hp => ?_⟩
  · have hsub : chartAt ℂ x '' ((s26v_E q ∪ ⋃ k, G k '' Z k) ∩ (chartAt ℂ x).source) ⊆
        chartAt ℂ x '' (s26v_E q ∩ (chartAt ℂ x).source) ∪
          ⋃ k, (fun u => chartAt ℂ x (G k u)) '' {u | u ∈ Z k ∧ G k u ∈ (chartAt ℂ x).source} := by
      rintro _ ⟨p, ⟨hp | hp, hps⟩, rfl⟩
      · exact Or.inl ⟨p, ⟨hp, hps⟩, rfl⟩
      · obtain ⟨k, u, hu, rfl⟩ := mem_iUnion.1 hp
        exact Or.inr (mem_iUnion.2 ⟨k, u, ⟨hu, hps⟩, rfl⟩)
    refine measure_mono_null hsub (measure_union_null (s26v_E_null hq hne x) (measure_iUnion_null fun k => ?_))
    have hc0 := s26v_a_family_center hq hT hfam k
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun u hu => ?_)
      (measure_mono_null (fun u hu => hu.1) (hZ k))
    exact ((s26v_a_natAt_differentiableAt hq (hc0.1 u hu.1.1.1) x hu.2).restrictScalars ℝ).differentiableWithinAt
  · have hpE : p ∉ s26v_E q := fun h => hp (Or.inl h)
    obtain ⟨k, w, hw, rfl⟩ := s26v_a_W_cover hfam hpE
    have hwZ : w ∉ Z k := fun h => hp (Or.inr (mem_iUnion.2 ⟨k, w, h, rfl⟩))
    have hs1 : volume {t | t ∈ Ioo (-L) L ∧ w + (((1 : ℝ) * t : ℝ) : ℂ) ∈ B k} = 0 := by
      by_contra h
      exact hwZ ⟨hw, Or.inl h⟩
    have hs2 : volume {t | t ∈ Ioo (-L) L ∧ w + (((-1 : ℝ) * t : ℝ) : ℂ) ∈ B k} = 0 := by
      by_contra h
      exact hwZ ⟨hw, Or.inr h⟩
    obtain ⟨p₀, hG⟩ := hfam.1 k
    have hw' : ‖w‖ < ρ k := by simpa using hw.1
    have hre : |w.re| < ρ k := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
    have him : |w.im| < ρ k := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw'
    rw [abs_lt] at hre him
    obtain ⟨hre1, hre2⟩ := hre
    obtain ⟨him1, him2⟩ := him
    have hρ := hG.1
    rcases s26v_a_tube_traj hq hG ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hpE with h | h
    · refine measure_mono_null ?_ hs1
      intro t ht
      refine ⟨ht.1, ?_⟩
      obtain ⟨⟨ht1, ht2⟩, htN⟩ := ht
      have ht' := h t ⟨by linarith, by linarith⟩
      have hN' : G k (w + t) ∈ N := by
        rw [← ht']
        exact htN
      have e : w + (((1 : ℝ) * t : ℝ) : ℂ) = w + t := by
        push_cast
        ring
      rw [e]
      refine hBN k (w + t) ?_ ?_ hN'
      · rw [Complex.add_re, Complex.ofReal_re]
        exact ⟨by linarith, by linarith⟩
      · rw [Complex.add_im, Complex.ofReal_im, add_zero]
        exact ⟨by linarith, by linarith⟩
    · refine measure_mono_null ?_ hs2
      intro t ht
      refine ⟨ht.1, ?_⟩
      obtain ⟨⟨ht1, ht2⟩, htN⟩ := ht
      have ht' := h t ⟨by linarith, by linarith⟩
      have hN' : G k (w - t) ∈ N := by
        rw [← ht']
        exact htN
      have e : w + (((-1 : ℝ) * t : ℝ) : ℂ) = w - t := by
        push_cast
        ring
      rw [e]
      refine hBN k (w - t) ?_ ?_ hN'
      · rw [Complex.sub_re, Complex.ofReal_re]
        exact ⟨by linarith, by linarith⟩
      · rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
        exact ⟨by linarith, by linarith⟩

/-! #### The stretching function and the arcs -/

/-- The algebra of the source-chart change in `λ_f`: for `a ≠ 0`, the numerator gains `‖a‖` and so does the square
root of `‖Q a²‖`. -/
theorem s26v_b_lambdaPlane_alg (A B Q a : ℂ) (ha : a ≠ 0) (c : ℝ) :
    c * ‖A * a + B * conj a * (Q * a ^ 2 / ((‖Q * a ^ 2‖ : ℝ) : ℂ))‖ / Real.sqrt ‖Q * a ^ 2‖ =
      c * ‖A + B * (Q / ((‖Q‖ : ℝ) : ℂ))‖ / Real.sqrt ‖Q‖ := by
  by_cases hQ : Q = 0
  · subst hQ
    simp
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  have hac : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have hnorm : ‖Q * a ^ 2‖ = ‖Q‖ * ‖a‖ ^ 2 := by rw [norm_mul, norm_pow]
  have key : A * a + B * conj a * (Q * a ^ 2 / ((‖Q * a ^ 2‖ : ℝ) : ℂ)) =
      a * (A + B * (Q / ((‖Q‖ : ℝ) : ℂ))) := by
    rw [hnorm]
    have h1 : ((‖Q‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnQ.ne'
    have h2 : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hna.ne'
    push_cast
    field_simp
    linear_combination (B * Q) * hac
  rw [key, norm_mul, hnorm, Real.sqrt_mul hnQ.le, Real.sqrt_sq hna.le]
  field_simp

/-- **[V6a, stub]** (chart independence of `λ_f`).  At `p` in the chart at `x`, `λ_f` read in the chart at `x` equals
`λ_f` read in the chart at `p`: with `τ = φ_p ∘ φ_x⁻¹` holomorphic, `∂(g ∘ τ) = ∂g · τ'`, `∂̄(g ∘ τ) = ∂̄g · τ̄'`
(`s23_wirtinger_comp_right`, both sides `0` where `g` is not differentiable), `q_x = q_p(τ) τ'²`, and the factor
`|τ'|` cancels (both sides are `0` where `q` vanishes). -/
theorem s26v_lambdaStretch_chart [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (f : S₀ ≃ₜ S₀) (x : S₀) {p : S₀} (hp : p ∈ (chartAt ℂ x).source) :
    lambdaStretch q q f x (chartAt ℂ x p) = lambdaStretch q q f p (chartAt ℂ p p) := by
  set z := chartAt ℂ x p with hz
  set z' := chartAt ℂ p p with hz'
  have hzt : z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp
  have hzs : (chartAt ℂ x).symm z = p := (chartAt ℂ x).left_inv hp
  have hpp : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hz't : z' ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hpp
  have hz's : (chartAt ℂ p).symm z' = p := (chartAt ℂ p).left_inv hpp
  obtain ⟨hT, hT0⟩ := s23_transition p x hzt (by rw [hzs]; exact hpp)
  have hTz : chartTransition p x z = z' := by
    show chartAt ℂ p ((chartAt ℂ x).symm z) = z'
    rw [hzs]
  obtain ⟨hS, -⟩ := s23_transition x p hz't (by rw [hz's]; exact hp)
  have hST := s23_transition_inv p x hzt (by rw [hzs]; exact hpp)
  have hTS := s23_transition_inv x p hz't (by rw [hz's]; exact hp)
  set g : ℂ → ℂ := localMapExprAt f p z' with hg
  have hev : localMapExprAt f x z =ᶠ[𝓝 z] g ∘ chartTransition p x := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds
      ⟨hzt, show (chartAt ℂ x).symm z ∈ (chartAt ℂ p).source by rw [hzs]; exact hpp⟩] with w hw
    simp only [localMapExprAt, Function.comp_apply, hg, hzs, hz's, chartTransition]
    rw [(chartAt ℂ p).left_inv hw.2]
  obtain ⟨hdz, hdzbar⟩ := s23_wirtinger_comp_right (g := g) hT (by rw [hTz]; exact hS) hST
    (by rw [hTz]; exact hTS)
  rw [hTz] at hdz hdzbar
  have e1 : dz (localMapExprAt f x z) z = dz g z' * deriv (chartTransition p x) z := by
    rw [← hdz]; simp only [dz, hev.fderiv_eq]
  have e2 : dzbar (localMapExprAt f x z) z = dzbar g z' * conj (deriv (chartTransition p x) z) := by
    rw [← hdzbar]; simp only [dzbar, hev.fderiv_eq]
  have hlaw := s26u_law hq x p hzt (by rw [hzs]; exact hpp)
  rw [hTz] at hlaw
  have hgz : localMapExprAt f x z z = g z' := by
    simp only [localMapExprAt, hg, hzs, hz's]
  simp only [lambdaStretch, lambdaStretchPlane]
  rw [e1, e2, hgz, hlaw, hzs, hz's]
  exact s26v_b_lambdaPlane_alg _ _ _ _ hT0 _

/-- The coefficients of a holomorphic quadratic differential are Borel functions (holomorphic on the chart target,
`0` off it). -/
theorem s26v_b_measurable_q {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (y : S₀) : Measurable (q y) := by
  classical
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have h : (chartAt ℂ y).target.piecewise (q y) (fun _ => 0) = q y := by
    funext z
    by_cases hz : z ∈ (chartAt ℂ y).target
    · simp [hz]
    · simp [hz, hq'.1.1 y z hz]
  rw [← h]
  exact (hq'.2 y).continuousOn.measurable_piecewise continuousOn_const
    (chartAt ℂ y).open_target.measurableSet

/-- Target-side chart independence of `λ_f`: at `z` in the chart target at `x`, if `f` maps `φ_x⁻¹ z` into the chart at
`y`, then `λ_f` may be read in the fixed target chart at `y` (`s23_wirtinger_comp_left` and the transformation law). -/
theorem s26v_b_lambdaStretch_target [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    (f : S₀ ≃ₜ S₀) (x y : S₀) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source) :
    lambdaStretch q q f x z =
      lambdaStretchPlane (q x) (q y) (fun w => chartAt ℂ y (f ((chartAt ℂ x).symm w))) z := by
  set p := (chartAt ℂ x).symm z with hp
  set G : ℂ → ℂ := fun w => chartAt ℂ y (f ((chartAt ℂ x).symm w)) with hG
  have hGz : G z ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hzy
  have hGzs : (chartAt ℂ y).symm (G z) = f p := (chartAt ℂ y).left_inv hzy
  have hfp : f p ∈ (chartAt ℂ (f p)).source := mem_chart_source ℂ (f p)
  obtain ⟨hh, -⟩ := s23_transition (f p) y hGz (by rw [hGzs]; exact hfp)
  have hσG : chartTransition (f p) y (G z) = chartAt ℂ (f p) (f p) := by
    simp only [chartTransition, hGzs]
  have hσGt : chartTransition (f p) y (G z) ∈ (chartAt ℂ (f p)).target := by
    rw [hσG]; exact (chartAt ℂ (f p)).map_source hfp
  have hσGs : (chartAt ℂ (f p)).symm (chartTransition (f p) y (G z)) = f p := by
    rw [hσG]; exact (chartAt ℂ (f p)).left_inv hfp
  obtain ⟨hk, -⟩ := s23_transition y (f p) hσGt (by rw [hσGs]; exact hzy)
  have hkh := s23_transition_inv (f p) y hGz (by rw [hGzs]; exact hfp)
  have hc1 : ContinuousAt (fun w => f ((chartAt ℂ x).symm w)) z :=
    f.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hGc : ContinuousAt G z :=
    ContinuousAt.comp (g := chartAt ℂ y) (f := fun w => f ((chartAt ℂ x).symm w)) ((chartAt ℂ y).continuousAt hzy) hc1
  obtain ⟨hdz, hdzbar⟩ := s23_wirtinger_comp_left hGc hh hk hkh
  have hev : localMapExprAt f x z =ᶠ[𝓝 z] chartTransition (f p) y ∘ G := by
    filter_upwards [hc1.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hzy)] with w hw
    simp only [localMapExprAt, Function.comp_apply, chartTransition, hG]
    rw [(chartAt ℂ y).left_inv hw]
  have e1 : dz (localMapExprAt f x z) z = deriv (chartTransition (f p) y) (G z) * dz G z := by
    rw [← hdz]; simp only [dz, hev.fderiv_eq]
  have e2 : dzbar (localMapExprAt f x z) z = deriv (chartTransition (f p) y) (G z) * dzbar G z := by
    rw [← hdzbar]; simp only [dzbar, hev.fderiv_eq]
  have hlaw := s26u_law hq y (f p) hGz (by rw [hGzs]; exact hfp)
  have hMz : localMapExprAt f x z z = chartTransition (f p) y (G z) := by
    rw [hσG]
    rfl
  simp only [lambdaStretch, lambdaStretchPlane]
  rw [e1, e2, hMz, hlaw, ← hp]
  rw [norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hfac : deriv (chartTransition (f p) y) (G z) * dz G z +
      deriv (chartTransition (f p) y) (G z) * dzbar G z * (q x z / ((‖q x z‖ : ℝ) : ℂ)) =
      deriv (chartTransition (f p) y) (G z) * (dz G z + dzbar G z * (q x z / ((‖q x z‖ : ℝ) : ℂ))) := by
    ring
  rw [hfac, norm_mul]
  ring

/-- **[V6b, stub]** (`λ_f` is Borel in charts).  On a neighbourhood of each point of a chart target, `λ_f` is
`lambdaStretchPlane (q x) (q y) (φ_y ∘ f ∘ φ_x⁻¹)` for a fixed target chart `y` (target-side chart independence,
`s23_wirtinger_comp_left`), which is Borel (`measurable_fderiv`); countably many such neighbourhoods cover the
target. -/
theorem s26v_lam_borel [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (f : S₀ ≃ₜ S₀) :
    s26v_IsBorelInCharts (s26v_lam q f) := by
  classical
  intro x
  have hloc : ∀ z₀ ∈ (chartAt ℂ x).target, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ (chartAt ℂ x).target ∧
      ∃ M : ℂ → ℝ≥0∞, Measurable M ∧ ∀ z ∈ V, ENNReal.ofReal (lambdaStretch q q f x z) = M z := by
    intro z₀ hz₀
    set y := f ((chartAt ℂ x).symm z₀) with hy
    set V : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' (chartAt ℂ y).source) with hV
    have hVo : IsOpen V :=
      (chartAt ℂ x).isOpen_inter_preimage_symm ((chartAt ℂ y).open_source.preimage f.continuous)
    set G : ℂ → ℂ := fun w => chartAt ℂ y (f ((chartAt ℂ x).symm w)) with hG
    have hGc : ContinuousOn G V := fun z hz => by
      have hc1 : ContinuousAt (fun w => f ((chartAt ℂ x).symm w)) z :=
        f.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
      exact (ContinuousAt.comp (g := chartAt ℂ y) (f := fun w => f ((chartAt ℂ x).symm w))
        ((chartAt ℂ y).continuousAt hz.2) hc1).continuousWithinAt
    have hGcm : Measurable (V.piecewise G (fun _ => 0)) :=
      hGc.measurable_piecewise continuousOn_const hVo.measurableSet
    have hqx := s26v_b_measurable_q hq x
    have hqy := s26v_b_measurable_q hq y
    have hdz : Measurable (dz G) := by
      unfold dz
      exact ((measurable_fderiv_apply_const ℝ G 1).sub
        ((measurable_fderiv_apply_const ℝ G I).const_mul I)).div_const 2
    have hdzbar : Measurable (dzbar G) := by
      unfold dzbar
      exact ((measurable_fderiv_apply_const ℝ G 1).add
        ((measurable_fderiv_apply_const ℝ G I).const_mul I)).div_const 2
    refine ⟨V, hVo, ⟨hz₀, mem_chart_source ℂ y⟩, fun z hz => hz.1, fun z => ENNReal.ofReal
      (Real.sqrt ‖q y (V.piecewise G (fun _ => 0) z)‖ *
        ‖dz G z + dzbar G z * (q x z / ((‖q x z‖ : ℝ) : ℂ))‖ / Real.sqrt ‖q x z‖), ?_, ?_⟩
    · refine Measurable.ennreal_ofReal ?_
      refine Measurable.div (Measurable.mul ?_ ?_) ?_
      · exact (hqy.comp hGcm).norm.sqrt
      · exact (hdz.add (hdzbar.mul (hqx.div (Complex.measurable_ofReal.comp hqx.norm)))).norm
      · exact hqx.norm.sqrt
    · intro z hz
      rw [s26v_b_lambdaStretch_target hq f x y hz.1 hz.2]
      simp only [lambdaStretchPlane, Set.piecewise_eq_of_mem _ _ _ hz, hG]
  choose! V hVo hzV hVt M hM hVM using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : (chartAt ℂ x).target => V i) (fun i => hVo i i.2)
  have hcov : ∀ z ∈ (chartAt ℂ x).target, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have h1 : z ∈ ⋃ i : (chartAt ℂ x).target, V i := mem_iUnion.2 ⟨⟨z, hz⟩, hzV z hz⟩
    rw [← hTU] at h1
    obtain ⟨i, hi⟩ := mem_iUnion.1 h1
    obtain ⟨hiT, hzi⟩ := mem_iUnion.1 hi
    exact ⟨i, hiT, hzi⟩
  have hval : ∀ z ∈ (chartAt ℂ x).target,
      s26v_lam q f ((chartAt ℂ x).symm z) = ENNReal.ofReal (lambdaStretch q q f x z) := by
    intro z hz
    have hps : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    unfold s26v_lam
    rw [← s26v_lambdaStretch_chart hq f x hps, (chartAt ℂ x).right_inv hz]
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨fun _ => 0, measurable_const, fun z hz => ?_⟩
    obtain ⟨i, hi, -⟩ := hcov z hz
    rw [hT] at hi
    exact absurd hi (notMem_empty i)
  obtain ⟨e, he⟩ := hTc.exists_eq_range hT
  set W : ℕ → Set ℂ := fun n => V (e n) with hW
  have hWm : ∀ n, MeasurableSet (W n) := fun n => (hVo _ (e n).2).measurableSet
  refine ⟨fun z => ∑' n, (disjointed W n).indicator (M (e n)) z,
    Measurable.tsum fun n => (hM _ (e n).2).indicator (MeasurableSet.disjointed hWm n),
    fun z hz => ?_⟩
  obtain ⟨i, hiT, hzi⟩ := hcov z hz
  rw [he] at hiT
  obtain ⟨k, rfl⟩ := hiT
  have hzU : z ∈ ⋃ n, W n := mem_iUnion.2 ⟨k, hzi⟩
  rw [← iUnion_disjointed] at hzU
  obtain ⟨n, hn⟩ := mem_iUnion.1 hzU
  show _ = ∑' n, (disjointed W n).indicator (M (e n)) z
  rw [tsum_eq_single n, indicator_of_mem hn, hval z hz]
  · exact hVM _ (e n).2 z (disjointed_subset W n hn)
  · intro m hm
    exact indicator_of_notMem (fun hm' => (disjoint_disjointed W hm).le_bot ⟨hm', hn⟩) _

/-- Telescoping over a subdivision `τ : Fin (n + 1) → ℝ`: `∑ᵢ (τ (i + 1) - τ i) = τ n - τ 0`. -/
theorem s26v_b_sum_telescope : ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ),
    ∑ i : Fin n, (τ i.succ - τ i.castSucc) = τ (Fin.last n) - τ 0 := by
  intro n
  induction n with
  | zero => intro τ; simp
  | succ n ih =>
    intro τ
    have h1 := ih (fun i => τ i.castSucc)
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at h1
    rw [Fin.sum_univ_castSucc, h1, Fin.succ_last]
    ring

/-- In any chart containing the point, the arc parameter `r ↦ c(-L + 2Lr)` of a bi-infinite trajectory has chart
derivative `2L v` with `q v² = 1`. -/
theorem s26v_b_arc_deriv [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : C(ℝ, S₀)}
    (hc : s26v_IsTraj q c) (L : ℝ) (x : S₀) {t : ℝ} (hx : c (-L + 2 * L * t) ∈ (chartAt ℂ x).source) :
    ∃ v : ℂ, HasDerivAt (fun r => chartAt ℂ x (c (-L + 2 * L * r))) (((2 * L : ℝ) : ℂ) * v) t ∧
      q x (chartAt ℂ x (c (-L + 2 * L * t))) * v ^ 2 = 1 := by
  obtain ⟨v, hv, hqv⟩ := s26v_trajAt_chart hq (hc (-L + 2 * L * t)) x hx
  have haff : HasDerivAt (fun r : ℝ => -L + 2 * L * r) (2 * L) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * L)).const_add (-L)
  refine ⟨v, ?_, hqv⟩
  have h := hv.scomp t haff
  simpa [Function.comp_def, Complex.real_smul] using h

/-- **[V7, stub]** (the arcs).  The arc of a bi-infinite unit-speed horizontal trajectory over `[-L, L]` is a
horizontal arc of `q`-length `2L`: in any chart (`s26v_trajAt_chart`) its derivative is `2L v` with `q v² = 1`; every
admissible Lipschitz partition sums `∫ |q|^{1/2} |2L v| = 2L` over `(0, 1)`, and one exists (Lebesgue number, chart
expressions with bounded derivative). -/
theorem s26v_arc_props [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {c : C(ℝ, S₀)}
    (hc : s26v_IsTraj q c) {L : ℝ} (hL : 0 < L) :
    IsHorizontalArcRS q (s26v_arc c L) ∧ phiLengthPath q (s26v_arc c L) = ENNReal.ofReal (2 * L) := by
  set γ := s26v_arc c L with hγ
  have hext : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = c (-L + 2 * L * t) := fun t ht => by
    rw [Path.extend_apply γ ht]
    rfl
  have hext_ev : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend =ᶠ[𝓝 t] fun s => c (-L + 2 * L * s) := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hext s (Ioo_subset_Icc_self hs)
  have hder : ∀ (x : S₀) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 → γ.extend t ∈ (chartAt ℂ x).source →
      ∃ v : ℂ, HasDerivAt (fun r => chartAt ℂ x (γ.extend r)) (((2 * L : ℝ) : ℂ) * v) t ∧
        q x (chartAt ℂ x (γ.extend t)) * v ^ 2 = 1 := by
    intro x t ht hx
    rw [hext t (Ioo_subset_Icc_self ht)] at hx ⊢
    obtain ⟨v, hv, hqv⟩ := s26v_b_arc_deriv hq hc L x hx
    refine ⟨v, hv.congr_of_eventuallyEq ?_, hqv⟩
    filter_upwards [hext_ev t ht] with s hs
    rw [hs]
  have hint : ∀ (x : S₀) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 → γ.extend t ∈ (chartAt ℂ x).source →
      phiDensity (q x) (chartAt ℂ x (γ.extend t)) * ‖deriv (fun v => chartAt ℂ x (γ.extend v)) t‖ₑ =
        ENNReal.ofReal (2 * L) := by
    intro x t ht hx
    obtain ⟨v, hv, hqv⟩ := hder x t ht hx
    rw [hv.deriv]
    simp only [phiDensity]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    have h1 : ‖q x (chartAt ℂ x (γ.extend t))‖ * ‖v‖ ^ 2 = 1 := by
      have := congrArg norm hqv
      rwa [norm_mul, norm_pow, norm_one] at this
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h2 : Real.sqrt ‖q x (chartAt ℂ x (γ.extend t))‖ * ‖v‖ = 1 := by
      rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (norm_nonneg _), h1, Real.sqrt_one]
    calc Real.sqrt ‖q x (chartAt ℂ x (γ.extend t))‖ * (2 * L * ‖v‖)
        = 2 * L * (Real.sqrt ‖q x (chartAt ℂ x (γ.extend t))‖ * ‖v‖) := by ring
      _ = 2 * L := by rw [h2, mul_one]
  have hval : ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ) (y : Fin n → S₀), τ 0 = 0 → τ (Fin.last n) = 1 → Monotone τ →
      (∀ i, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (y i)).source) →
      ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (y i)) (chartAt ℂ (y i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (y i) (γ.extend v)) u‖ₑ = ENNReal.ofReal (2 * L) := by
    intro n τ y h0 h1 hmono hsrc
    have hpiece : ∀ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (y i)) (chartAt ℂ (y i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (y i) (γ.extend v)) u‖ₑ =
        ENNReal.ofReal (2 * L) * ENNReal.ofReal (τ i.succ - τ i.castSucc) := by
      intro i
      have hu01 : ∀ u ∈ Ioo (τ i.castSucc) (τ i.succ), u ∈ Ioo (0 : ℝ) 1 := by
        intro u hu
        have ha : τ 0 ≤ τ i.castSucc := hmono (Fin.zero_le _)
        have hb : τ i.succ ≤ τ (Fin.last n) := hmono (Fin.le_last _)
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [setLIntegral_congr_fun measurableSet_Ioo (fun u hu => hint (y i) u (hu01 u hu)
        (hsrc i ⟨u, Ioo_subset_Icc_self hu, rfl⟩)), setLIntegral_const, Real.volume_Ioo]
    rw [Finset.sum_congr rfl fun i _ => hpiece i, ← Finset.mul_sum,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => sub_nonneg.2 (hmono (Fin.castSucc_le_succ i)),
      s26v_b_sum_telescope, h0, h1, sub_zero, ENNReal.ofReal_one, mul_one]
  refine ⟨?_, ?_⟩
  · intro t₀ _
    set x := γ.extend t₀ with hx
    have hmem : γ.extend ⁻¹' (chartAt ℂ x).source ∈ 𝓝 t₀ :=
      γ.continuous_extend.continuousAt.preimage_mem_nhds
        ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨δ, hδ, x, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      apply hball
      rw [Real.ball_eq_Ioo]
      exact ht
    · intro t ht
      have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
      have htx : γ.extend t ∈ (chartAt ℂ x).source := hball (by
        rw [Real.ball_eq_Ioo]
        exact ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩)
      obtain ⟨v, hv, hqv⟩ := hder x t ht01 htx
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hqv
      have hq0 : q x (chartAt ℂ x (γ.extend t)) ≠ 0 := by
        intro h
        rw [h, zero_mul] at hqv
        exact zero_ne_one hqv
      have hkey : q x (chartAt ℂ x (γ.extend t)) * (((2 * L : ℝ) : ℂ) * v) ^ 2 = ((4 * L ^ 2 : ℝ) : ℂ) := by
        push_cast
        linear_combination (4 * (L : ℂ) ^ 2) * hqv
      have h2L : ((2 * L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * L : ℝ) ≠ 0)
      refine ⟨hv.differentiableAt, ?_, hq0, ?_, ?_⟩
      · rw [hv.deriv]
        exact mul_ne_zero h2L hv0
      · rw [hv.deriv, hkey, Complex.ofReal_im]
      · rw [hv.deriv, hkey, Complex.ofReal_re]
        positivity
  · unfold phiLengthPath phiLengthOn
    apply le_antisymm
    · -- an admissible partition: Lebesgue number of the cover by the chart sources where `|q|` is bounded below
      set cov : S₀ → Set ℝ := fun y => γ.extend ⁻¹' {p | p ∈ (chartAt ℂ y).source ∧
        q y (chartAt ℂ y y) ≠ 0 ∧ ‖q y (chartAt ℂ y y)‖ < 2 * ‖q y (chartAt ℂ y p)‖} with hcov
      have hcovo : ∀ y, IsOpen (cov y) := by
        intro y
        refine IsOpen.preimage γ.continuous_extend ?_
        by_cases hy : q y (chartAt ℂ y y) = 0
        · convert isOpen_empty
          ext p
          simp [hy]
        · have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
          have hcont : ContinuousOn (fun p => ‖q y (chartAt ℂ y p)‖) (chartAt ℂ y).source :=
            ((hq'.2 y).continuousOn.comp (chartAt ℂ y).continuousOn (chartAt ℂ y).mapsTo).norm
          have h := hcont.isOpen_inter_preimage (chartAt ℂ y).open_source
            (isOpen_Ioi (a := ‖q y (chartAt ℂ y y)‖ / 2))
          convert h using 1
          ext p
          simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
          constructor
          · rintro ⟨h1, -, h3⟩
            exact ⟨h1, by linarith⟩
          · rintro ⟨h1, h3⟩
            exact ⟨h1, hy, by linarith⟩
      have hcovU : Icc (0 : ℝ) 1 ⊆ ⋃ y, cov y := by
        intro t ht
        refine mem_iUnion.2 ⟨γ.extend t, mem_chart_source ℂ _, ?_, ?_⟩
        · rw [hext t ht]
          obtain ⟨-, v, -, hqv⟩ := hc (-L + 2 * L * t)
          intro h
          rw [h, zero_mul] at hqv
          exact zero_ne_one hqv
        · have hpos : 0 < ‖q (γ.extend t) (chartAt ℂ (γ.extend t) (γ.extend t))‖ := by
            rw [hext t ht]
            obtain ⟨-, v, -, hqv⟩ := hc (-L + 2 * L * t)
            refine norm_pos_iff.2 fun h => ?_
            rw [h, zero_mul] at hqv
            exact zero_ne_one hqv
          linarith
      obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hcovo hcovU
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      have hN1 : (0 : ℝ) < N + 1 := by positivity
      set τ : Fin (N + 1 + 1) → ℝ := fun i => (i : ℝ) / (N + 1) with hτ
      have hτ01 : ∀ i : Fin (N + 1), τ i.castSucc ∈ Icc (0 : ℝ) 1 := by
        intro i
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hN1]
        have := i.2
        simp only [Fin.val_castSucc]
        exact_mod_cast this.le
      choose y hy using fun i : Fin (N + 1) => hleb (τ i.castSucc) (hτ01 i)
      have hsub : ∀ i : Fin (N + 1), Icc (τ i.castSucc) (τ i.succ) ⊆ cov (y i) := by
        intro i t ht
        apply hy i
        rw [Real.ball_eq_Ioo]
        have hlen : τ i.succ - τ i.castSucc = 1 / (N + 1) := by
          simp only [hτ, Fin.val_succ, Fin.val_castSucc]
          push_cast
          field_simp
          ring
        constructor
        · linarith [ht.1]
        · linarith [ht.2]
      refine iInf_le_of_le (N + 1) (iInf_le_of_le τ (iInf_le_of_le y (iInf_le_of_le ⟨?_, ?_, ?_, fun i => ?_⟩ ?_)))
      · simp [hτ]
      · simp only [hτ, Fin.val_last]
        push_cast
        field_simp
      · intro i j hij
        simp only [hτ]
        gcongr
        exact_mod_cast hij
      · refine ⟨fun p hp => ?_, ?_⟩
        · obtain ⟨t, ht, rfl⟩ := hp
          exact (hsub i ht).1
        · -- Lipschitz: derivative bounded by `2L / √(|q_y(φ_y y)| / 2)`
          set m : ℝ := ‖q (y i) (chartAt ℂ (y i) (y i))‖ / 2 with hm
          have hIcc : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc (0 : ℝ) 1 := by
            intro t ht
            have h1 := hτ01 i
            have h2 : τ i.succ ≤ 1 := by
              simp only [hτ, Fin.val_succ]
              rw [div_le_one hN1]
              have := i.2
              push_cast
              exact_mod_cast this
            exact ⟨h1.1.trans ht.1, ht.2.trans h2⟩
          have hmpos : 0 < m := by
            obtain ⟨t, ht⟩ : (Icc (τ i.castSucc) (τ i.succ)).Nonempty :=
              nonempty_Icc.2 (by simp only [hτ]; gcongr; simp)
            have := (hsub i ht).2.1
            positivity
          refine ⟨⟨2 * L / Real.sqrt m, by positivity⟩, ?_⟩
          have hF : ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), ∃ w : ℂ,
              HasDerivAt (fun r => chartAt ℂ (y i) (c (-L + 2 * L * r))) w t ∧ ‖w‖₊ ≤
                ⟨2 * L / Real.sqrt m, by positivity⟩ := by
            intro t ht
            have hct : c (-L + 2 * L * t) ∈ (chartAt ℂ (y i)).source := by
              rw [← hext t (hIcc ht)]
              exact (hsub i ht).1
            obtain ⟨v, hv, hqv⟩ := s26v_b_arc_deriv hq hc L (y i) hct
            refine ⟨_, hv, ?_⟩
            have hlow : m < ‖q (y i) (chartAt ℂ (y i) (c (-L + 2 * L * t)))‖ := by
              have := (hsub i ht).2.2
              rw [hext t (hIcc ht)] at this
              rw [hm]
              linarith
            have h1 : ‖q (y i) (chartAt ℂ (y i) (c (-L + 2 * L * t)))‖ * ‖v‖ ^ 2 = 1 := by
              have := congrArg norm hqv
              rwa [norm_mul, norm_pow, norm_one] at this
            refine NNReal.coe_le_coe.1 ?_
            rw [coe_nnnorm]
            show ‖((2 * L : ℝ) : ℂ) * v‖ ≤ 2 * L / Real.sqrt m
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
            have hv2 : ‖v‖ ^ 2 ≤ 1 / m := by
              rw [le_div_iff₀ hmpos]
              nlinarith [sq_nonneg ‖v‖]
            have hv3 : ‖v‖ ≤ 1 / Real.sqrt m := by
              rw [← Real.sqrt_sq (norm_nonneg v), one_div, ← Real.sqrt_inv]
              exact Real.sqrt_le_sqrt (by rwa [one_div] at hv2)
            calc 2 * L * ‖v‖ ≤ 2 * L * (1 / Real.sqrt m) := by gcongr
              _ = 2 * L / Real.sqrt m := by ring
          choose! w hw hwb using hF
          have hlip := (convex_Icc (τ i.castSucc) (τ i.succ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
            (fun t ht => (hw t ht).hasDerivWithinAt) hwb
          intro a ha b hb
          simp only
          rw [hext a (hIcc ha), hext b (hIcc hb)]
          exact hlip ha hb
      · exact (hval (N + 1) τ y (by simp [hτ]) (by simp only [hτ, Fin.val_last]; push_cast; field_simp)
          (fun i j hij => by simp only [hτ]; gcongr; exact_mod_cast hij)
          (fun i => fun p hp => by obtain ⟨t, ht, rfl⟩ := hp; exact (hsub i ht).1)).le
    · refine le_iInf fun n => le_iInf fun τ => le_iInf fun y => le_iInf fun hP => ?_
      obtain ⟨h0, h1, hmono, hpc⟩ := hP
      exact (hval n τ y h0 h1 hmono fun i => (hpc i).1).ge

/-! #### T4: the length of `f(α_p)` for almost every `p` -/

/-- A compact horizontal segment `[a, b] + iη` in an open set `D` lies in a closed rectangle with rational corners
around it inside `D`. -/
theorem s26v_b_rat_rect {D : Set ℂ} (hD : IsOpen D) {a b η : ℝ} (hab : a ≤ b)
    (hseg : ∀ ξ ∈ Icc a b, (ξ : ℂ) + (η : ℂ) * I ∈ D) :
    ∃ a' b' c d : ℚ, (a' : ℝ) < a ∧ b < b' ∧ (c : ℝ) < η ∧ η < d ∧ closedRect a' b' c d ⊆ D := by
  have hK : IsCompact ((fun ξ : ℝ => (ξ : ℂ) + (η : ℂ) * I) '' Icc a b) :=
    isCompact_Icc.image (by fun_prop)
  have hKD : (fun ξ : ℝ => (ξ : ℂ) + (η : ℂ) * I) '' Icc a b ⊆ D := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact hseg ξ hξ
  obtain ⟨ε, hε, hth⟩ := hK.exists_thickening_subset_open hD hKD
  obtain ⟨a', ha'1, ha'2⟩ := exists_rat_btwn (show a - ε / 3 < a by linarith)
  obtain ⟨b', hb'1, hb'2⟩ := exists_rat_btwn (show b < b + ε / 3 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show η - ε / 3 < η by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show η < η + ε / 3 by linarith)
  refine ⟨a', b', c, d, ha'2, hb'1, hc2, hd1, fun z hz => hth ?_⟩
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  · set ξ₀ := max a (min z.re b) with hξ₀
    have hξ₀I : ξ₀ ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
    rw [mem_thickening_iff]
    refine ⟨(ξ₀ : ℂ) + (η : ℂ) * I, ⟨ξ₀, hξ₀I, rfl⟩, ?_⟩
    rw [Complex.dist_eq]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, sub_im, add_im, mul_im, zero_add]
    have h1 : |z.re - ξ₀| < ε / 3 := by
      rw [abs_lt]
      constructor
      · have : ξ₀ ≤ max a z.re := max_le_max le_rfl (min_le_left _ _)
        rcases le_total a z.re with h | h
        · rw [max_eq_right h] at this; linarith
        · rw [max_eq_left h] at this; linarith
      · have : min a b ≤ ξ₀ := le_trans (min_le_left _ _) (le_max_left _ _)
        rcases le_total z.re b with h | h
        · have : z.re ≤ ξ₀ := le_trans (le_min le_rfl h) (le_max_right _ _)
          linarith
        · have : ξ₀ = b := by rw [hξ₀, min_eq_right h, max_eq_right hab]
          linarith
    have h2 : |z.im - η| < ε / 3 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith

/-- **[V8, stub]** (T4, plane).  A `K`-quasiconformal map is, along almost every horizontal line, absolutely
continuous on every segment in its domain and differentiable at almost every point.  (`thm9_1_isACL` on rational
rectangles, glued along overlapping intervals; `thm9_3_differentiable_ae` and Fubini through `ℂ ≃ ℝ × ℝ`.) -/
theorem s26v_isKQC_ae_line {G : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hG : IsKQC G D K) :
    ∀ᵐ η : ℝ, (∀ a b : ℝ, a < b → (∀ ξ ∈ Icc a b, (ξ : ℂ) + (η : ℂ) * I ∈ D) →
        AbsolutelyContinuousOnInterval (fun ξ : ℝ => G ((ξ : ℂ) + (η : ℂ) * I)) a b) ∧
      ∀ᵐ ξ : ℝ, (ξ : ℂ) + (η : ℂ) * I ∈ D → DifferentiableAt ℝ G ((ξ : ℂ) + (η : ℂ) * I) := by
  have hacl := thm9_1_isACL hG
  have h1 : ∀ᵐ η : ℝ, ∀ r : ℚ × ℚ × ℚ × ℚ, (r.1 : ℝ) < r.2.1 → (r.2.2.1 : ℝ) < r.2.2.2 →
      closedRect r.1 r.2.1 r.2.2.1 r.2.2.2 ⊆ D → η ∈ Ioo (r.2.2.1 : ℝ) r.2.2.2 →
      AbsolutelyContinuousOnInterval (fun ξ : ℝ => G ((ξ : ℂ) + (η : ℂ) * I)) r.1 r.2.1 := by
    rw [ae_all_iff]
    intro r
    by_cases hab : (r.1 : ℝ) < r.2.1
    · by_cases hcd : (r.2.2.1 : ℝ) < r.2.2.2
      · by_cases hR : closedRect r.1 r.2.1 r.2.2.1 r.2.2.2 ⊆ D
        · have h := (hacl.2 _ _ _ _ hab hcd hR).2
          rw [ae_restrict_iff' measurableSet_Ioo] at h
          filter_upwards [h] with η hη _ _ _ hηI
          exact hη hηI
        · exact Eventually.of_forall fun η _ _ h => absurd h hR
      · exact Eventually.of_forall fun η _ h => absurd h hcd
    · exact Eventually.of_forall fun η h => absurd h hab
  have h2 : ∀ᵐ z : ℂ, z ∈ D → DifferentiableAt ℝ G z := by
    have h := thm9_3_differentiable_ae hG
    rwa [ae_restrict_iff' hG.1.measurableSet] at h
  have h3 : ∀ᵐ p : ℝ × ℝ, (p.1 : ℂ) + (p.2 : ℂ) * I ∈ D →
      DifferentiableAt ℝ G ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    have hq := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae h2
    filter_upwards [hq] with p hp
    rwa [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I] at hp
  have h4 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), (p.2 : ℂ) + (p.1 : ℂ) * I ∈ D →
      DifferentiableAt ℝ G ((p.2 : ℂ) + (p.1 : ℂ) * I) := by
    have h3' : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), (p.1 : ℂ) + (p.2 : ℂ) * I ∈ D →
        DifferentiableAt ℝ G ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
      rw [← Measure.volume_eq_prod]
      exact h3
    exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae h3'
  have h5 := Measure.ae_ae_of_ae_prod h4
  filter_upwards [h1, h5] with η hη1 hη2
  refine ⟨fun a b hab hseg => ?_, hη2⟩
  obtain ⟨a', b', c, d, ha', hb', hc, hd, hR⟩ := s26v_b_rat_rect hG.1 hab.le hseg
  have hAC := hη1 (a', b', c, d) (by simp only; linarith) (by simp only; linarith) hR ⟨hc, hd⟩
  refine hAC.mono ?_
  rw [uIcc_of_le hab.le, uIcc_of_le (by simp only; linarith)]
  exact Icc_subset_Icc ha'.le hb'.le

/-- For monotone `u : ℕ → ℝ`, the integrals over the consecutive intervals `(u i, u (i+1))`, `i < n`, add up to at
most the integral over `(u 0, u n)`. -/
theorem s26v_b_sum_lintegral_le (f : ℝ → ℝ≥0∞) {u : ℕ → ℝ} (hu : Monotone u) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, ∫⁻ x in Ioo (u i) (u (i + 1)), f x ≤ ∫⁻ x in Ioo (u 0) (u n), f x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc (∑ i ∈ Finset.range n, ∫⁻ x in Ioo (u i) (u (i + 1)), f x) + ∫⁻ x in Ioo (u n) (u (n + 1)), f x
        ≤ (∫⁻ x in Ioo (u 0) (u n), f x) + ∫⁻ x in Ioo (u n) (u (n + 1)), f x := add_le_add ih le_rfl
      _ = ∫⁻ x in Ioo (u 0) (u n) ∪ Ioo (u n) (u (n + 1)), f x :=
          (lintegral_union measurableSet_Ioo (disjoint_left.2 fun x hx hx' => lt_asymm hx.2 hx'.1)).symm
      _ ≤ ∫⁻ x in Ioo (u 0) (u (n + 1)), f x :=
          lintegral_mono_set (union_subset (Ioo_subset_Ioo_right (hu (Nat.le_succ n)))
            (Ioo_subset_Ioo_left (hu (Nat.zero_le n))))

/-- For a monotone subdivision `τ : Fin (n + 1) → ℝ`, the integrals over the pieces `(τ i, τ (i + 1))` add up to at
most the integral over `(τ 0, τ n)` (the reverse of `s26n_lintegral_le_sum`). -/
theorem s26v_b_sum_le_lintegral (G : ℝ → ℝ≥0∞) :
    ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ), Monotone τ →
      ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ), G u ≤ ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)), G u := by
  intro n
  induction n with
  | zero => intro τ _; simp
  | succ n ih =>
    intro τ hτ
    have hτ' : Monotone fun i : Fin (n + 1) => τ i.castSucc := fun i j hij =>
      hτ (Fin.castSucc_le_castSucc_iff.2 hij)
    have h1 := ih (fun i => τ i.castSucc) hτ'
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc] at h1
    rw [Fin.sum_univ_castSucc, Fin.succ_last]
    calc _ ≤ (∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc), G u) +
          ∫⁻ u in Ioo (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u := add_le_add h1 le_rfl
      _ = ∫⁻ u in Ioo (τ 0) (τ (Fin.last n).castSucc) ∪
          Ioo (τ (Fin.last n).castSucc) (τ (Fin.last (n + 1))), G u :=
          (lintegral_union measurableSet_Ioo (disjoint_left.2 fun x hx hx' => lt_asymm hx.2 hx'.1)).symm
      _ ≤ _ := lintegral_mono_set (union_subset (Ioo_subset_Ioo_right (hτ (Fin.le_last _)))
          (Ioo_subset_Ioo_left (hτ (Fin.zero_le _))))

/-- The fundamental theorem of calculus as an estimate: for `H` absolutely continuous on `[w, v]`,
`‖H v - H w‖ₑ ≤ ∫⁻_{(w, v)} ‖H'‖ₑ`. -/
theorem s26v_b_edist_le_lintegral {H : ℝ → ℂ} {w v : ℝ} (hwv : w ≤ v)
    (hH : AbsolutelyContinuousOnInterval H w v) :
    edist (H v) (H w) ≤ ∫⁻ u in Ioo w v, ‖deriv H u‖ₑ := by
  rw [edist_eq_enorm_sub, ← integral_deriv_eq_sub_of_absolutelyContinuous hH, intervalIntegral.integral_of_le hwv]
  calc ‖∫ x in Ioc w v, deriv H x‖ₑ ≤ ∫⁻ x in Ioc w v, ‖deriv H x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ u in Ioo w v, ‖deriv H u‖ₑ := setLIntegral_congr Ioo_ae_eq_Ioc.symm

/-- The variation of a curve absolutely continuous on `[s, t]` is at most `∫⁻_{(s, t)} ‖H'‖ₑ`. -/
theorem s26v_b_eVariation_le {H : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hH : AbsolutelyContinuousOnInterval H s t) :
    eVariationOn H (Icc s t) ≤ ∫⁻ u in Ioo s t, ‖deriv H u‖ₑ := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ Finset.range n, edist (H (u (i + 1))) (H (u i))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ x in Ioo (u i) (u (i + 1)), ‖deriv H x‖ₑ := by
        refine Finset.sum_le_sum fun i _ => s26v_b_edist_le_lintegral (hu (Nat.le_succ i)) (hH.mono ?_)
        rw [uIcc_of_le (hu (Nat.le_succ i)), uIcc_of_le hst]
        exact Icc_subset_Icc (hus i).1 (hus (i + 1)).2
    _ ≤ ∫⁻ x in Ioo (u 0) (u n), ‖deriv H x‖ₑ := s26v_b_sum_lintegral_le _ hu n
    _ ≤ ∫⁻ x in Ioo s t, ‖deriv H x‖ₑ := lintegral_mono_set (Ioo_subset_Ioo (hus 0).1 (hus n).2)

/-- `∫⁻_{(s, t)} ‖H'‖ₑ` is at most the variation of `H` on `[s, t]`, for any curve: where the variation function `v`
and `H` are differentiable, `‖H'‖ ≤ v'`, and `∫ v' ≤ v(t) - v(s)` for the monotone `v`
(`MonotoneOn.intervalIntegral_deriv_mem_uIcc`). -/
theorem s26v_b_lintegral_le_eVariation (H : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t) :
    ∫⁻ u in Ioo s t, ‖deriv H u‖ₑ ≤ eVariationOn H (Icc s t) := by
  by_cases hbv : eVariationOn H (Icc s t) = ⊤
  · rw [hbv]
    exact le_top
  set v : ℝ → ℝ := fun r => (eVariationOn H (Icc s r)).toReal with hv
  have hfin : ∀ r r', s ≤ r → r' ≤ t → eVariationOn H (Icc r r') ≠ ⊤ := fun r r' hr hr' =>
    ne_top_of_le_ne_top hbv (eVariationOn.mono H (Icc_subset_Icc hr hr'))
  have hadd : ∀ r r', s ≤ r → r ≤ r' → r' ≤ t → v r' - v r = (eVariationOn H (Icc r r')).toReal := by
    intro r r' hr hrr' hr't
    have h := eVariationOn.Icc_add_Icc H (s := univ) hr hrr' (mem_univ r)
    simp only [univ_inter] at h
    simp only [hv]
    rw [← h, ENNReal.toReal_add (hfin s r le_rfl (hrr'.trans hr't)) (hfin r r' hr hr't)]
    ring
  have hmono : MonotoneOn v (Icc s t) := by
    intro r hr r' hr' hrr'
    have h := hadd r r' hr.1 hrr' hr'.2
    have h0 : 0 ≤ (eVariationOn H (Icc r r')).toReal := ENNReal.toReal_nonneg
    linarith
  have hinc : ∀ r r', s ≤ r → r ≤ r' → r' ≤ t → ‖H r' - H r‖ ≤ v r' - v r := by
    intro r r' hr hrr' hr't
    rw [hadd r r' hr hrr' hr't, ← dist_eq_norm, dist_edist]
    exact ENNReal.toReal_mono (hfin r r' hr hr't)
      (eVariationOn.edist_le H ⟨hrr', le_rfl⟩ ⟨le_rfl, hrr'⟩)
  have hdnn : ∀ r ∈ Ioo s t, 0 ≤ deriv v r := by
    intro r hr
    have h := hmono.derivWithin_nonneg (x := r)
    rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)] at h
  have hae : ∀ᵐ r, r ∈ Ioo s t → ‖deriv H r‖ ≤ deriv v r := by
    filter_upwards [hmono.ae_differentiableWithinAt_of_mem] with r hr hrI
    have hvd : DifferentiableAt ℝ v r :=
      (hr (Ioo_subset_Icc_self hrI)).differentiableAt (Icc_mem_nhds hrI.1 hrI.2)
    by_cases hHd : DifferentiableAt ℝ H r
    · have hne : 𝓝[>] r ≤ 𝓝[≠] r := nhdsWithin_mono _ fun y hy => ne_of_gt hy
      have h1 : Tendsto (fun y => ‖slope H r y‖) (𝓝[>] r) (𝓝 ‖deriv H r‖) :=
        ((hasDerivAt_iff_tendsto_slope.1 hHd.hasDerivAt).mono_left hne).norm
      have h2 : Tendsto (slope v r) (𝓝[>] r) (𝓝 (deriv v r)) :=
        (hasDerivAt_iff_tendsto_slope.1 hvd.hasDerivAt).mono_left hne
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [Ioo_mem_nhdsGT hrI.2] with y hy
      have hyr : 0 < y - r := sub_pos.2 hy.1
      rw [slope_def_module, slope_def_field, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hyr,
        inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hinc r y hrI.1.le hy.1.le hy.2.le) hyr.le
    · rw [deriv_zero_of_not_differentiableAt hHd, norm_zero]
      exact hdnn r hrI
  have hvI : MonotoneOn v (uIcc s t) := by rwa [uIcc_of_le hst]
  have hint := hvI.intervalIntegrable_deriv
  have hmem := hvI.intervalIntegral_deriv_mem_uIcc
  have hvst : 0 ≤ v t - v s := by
    have h := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    linarith
  rw [uIcc_of_le hvst] at hmem
  have hvs : v s = 0 := by
    simp only [hv, Icc_self, eVariationOn.subsingleton H (subsingleton_singleton), ENNReal.toReal_zero]
  calc ∫⁻ u in Ioo s t, ‖deriv H u‖ₑ ≤ ∫⁻ u in Ioo s t, ENNReal.ofReal (deriv v u) := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hae] with r hr hrI
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hr hrI)
    _ = ENNReal.ofReal (∫ u in Ioo s t, deriv v u) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hst).1 hint
        · exact ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => hdnn r hr
    _ = ENNReal.ofReal (∫ u in s..t, deriv v u) := by
        rw [intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]
    _ ≤ ENNReal.ofReal (v t - v s) := ENNReal.ofReal_le_ofReal hmem.2
    _ = eVariationOn H (Icc s t) := by
        rw [hvs, sub_zero]
        exact ENNReal.ofReal_toReal hbv

/-- **Variation = `∫|H'|`** for a curve absolutely continuous on `[s, t]`. -/
theorem s26v_b_eVariation_eq {H : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hH : AbsolutelyContinuousOnInterval H s t) :
    eVariationOn H (Icc s t) = ∫⁻ u in Ioo s t, ‖deriv H u‖ₑ :=
  le_antisymm (s26v_b_eVariation_le hst hH) (s26v_b_lintegral_le_eVariation H hst)

/-- A monotone continuous function maps `[a, b]` onto `[σ a, σ b]`. -/
theorem s26v_b_image_Icc {σ : ℝ → ℝ} (hσm : Monotone σ) (hσc : Continuous σ) {a b : ℝ} (hab : a ≤ b) :
    σ '' Icc a b = Icc (σ a) (σ b) := by
  refine subset_antisymm ?_ (intermediate_value_Icc hab hσc.continuousOn)
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨hσm hu.1, hσm hu.2⟩

/-- **Reparametrization of weighted lengths**: if `F` is absolutely continuous on `[σ α, σ β]`, `σ` is monotone and
continuous, and `F ∘ σ` is absolutely continuous on `[α, β]`, then for every Borel weight `g`,
`∫_{(α,β)} g(σ u) ‖(F ∘ σ)'(u)‖ du = ∫_{(σ α, σ β)} g(t) ‖F'(t)‖ dt`.  (`σ` pushes the measure `‖(F ∘ σ)'‖ du` on
`(α, β)` to `‖F'‖ dt` on `(σ α, σ β)`: both give `Iic c` the variation of `F` over `[σ α, c]`, by
`s26v_b_eVariation_eq` and the invariance of the variation under monotone reparametrization.) -/
theorem s26v_b_reparam_lintegral {F : ℝ → ℂ} {σ : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hσm : Monotone σ) (hσc : Continuous σ) (hF : AbsolutelyContinuousOnInterval F (σ α) (σ β))
    (hG : AbsolutelyContinuousOnInterval (F ∘ σ) α β) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u in Ioo α β, g (σ u) * ‖deriv (F ∘ σ) u‖ₑ = ∫⁻ t in Ioo (σ α) (σ β), g t * ‖deriv F t‖ₑ := by
  have hσαβ : σ α ≤ σ β := hσm hαβ
  have hkey : ∀ w ∈ Icc α β,
      ∫⁻ u in Ioo α w, ‖deriv (F ∘ σ) u‖ₑ = ∫⁻ t in Ioo (σ α) (σ w), ‖deriv F t‖ₑ := by
    intro w hw
    have hG' : AbsolutelyContinuousOnInterval (F ∘ σ) α w := hG.mono (by
      rw [uIcc_of_le hw.1, uIcc_of_le hαβ]
      exact Icc_subset_Icc_right hw.2)
    have hF' : AbsolutelyContinuousOnInterval F (σ α) (σ w) := hF.mono (by
      rw [uIcc_of_le (hσm hw.1), uIcc_of_le hσαβ]
      exact Icc_subset_Icc_right (hσm hw.2))
    rw [← s26v_b_eVariation_eq hw.1 hG', ← s26v_b_eVariation_eq (hσm hw.1) hF',
      eVariationOn.comp_eq_of_monotoneOn F σ (hσm.monotoneOn _), s26v_b_image_Icc hσm hσc hw.1]
  have hmG : Measurable fun u => ‖deriv (F ∘ σ) u‖ₑ := (measurable_deriv _).enorm
  have hmF : Measurable fun t => ‖deriv F t‖ₑ := (measurable_deriv _).enorm
  have hfinG : ∫⁻ u in Ioo α β, ‖deriv (F ∘ σ) u‖ₑ ≠ ⊤ := by
    rw [hkey β ⟨hαβ, le_rfl⟩, ← s26v_b_eVariation_eq hσαβ hF, ← uIcc_of_le hσαβ]
    exact hF.boundedVariationOn
  have hfm : IsFiniteMeasure ((volume.restrict (Ioo α β)).withDensity fun u => ‖deriv (F ∘ σ) u‖ₑ) :=
    isFiniteMeasure_withDensity hfinG
  have hmap : ((volume.restrict (Ioo α β)).withDensity fun u => ‖deriv (F ∘ σ) u‖ₑ).map σ =
      (volume.restrict (Ioo (σ α) (σ β))).withDensity fun t => ‖deriv F t‖ₑ := by
    refine Measure.ext_of_Iic _ _ fun c => ?_
    rw [Measure.map_apply hσm.measurable measurableSet_Iic,
      withDensity_apply _ (hσm.measurable measurableSet_Iic), withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict (hσm.measurable measurableSet_Iic), Measure.restrict_restrict measurableSet_Iic]
    rcases lt_or_ge c (σ α) with hc | hc
    · have h1 : σ ⁻¹' Iic c ∩ Ioo α β = ∅ := by
        refine eq_empty_of_forall_notMem fun u hu => ?_
        have := hσm hu.2.1.le
        exact absurd (lt_of_lt_of_le hc this) (not_lt.2 hu.1)
      have h2 : Iic c ∩ Ioo (σ α) (σ β) = ∅ := by
        refine eq_empty_of_forall_notMem fun t ht => ?_
        exact absurd (lt_of_le_of_lt ht.1 hc) (not_lt.2 ht.2.1.le)
      rw [h1, h2]
      simp
    rcases le_or_gt (σ β) c with hc' | hc'
    · have h1 : σ ⁻¹' Iic c ∩ Ioo α β = Ioo α β :=
        inter_eq_right.2 fun u hu => (hσm hu.2.le).trans hc'
      have h2 : Iic c ∩ Ioo (σ α) (σ β) = Ioo (σ α) (σ β) :=
        inter_eq_right.2 fun t ht => ht.2.le.trans hc'
      rw [h1, h2, hkey β ⟨hαβ, le_rfl⟩]
    · set T := Icc α β ∩ σ ⁻¹' Iic c with hT
      have hTc : IsCompact T := isCompact_Icc.inter_right (isClosed_Iic.preimage hσc)
      have hTne : T.Nonempty := ⟨α, ⟨le_rfl, hαβ⟩, hc⟩
      have hwT : sSup T ∈ T := hTc.sSup_mem hTne
      have hle : ∀ u ∈ T, u ≤ sSup T := fun u hu => le_csSup hTc.bddAbove hu
      have hwβ : sSup T < β := by
        refine lt_of_le_of_ne hwT.1.2 fun h => ?_
        have h' := hwT.2
        rw [h] at h'
        exact absurd (lt_of_le_of_lt (mem_Iic.1 h') hc') (lt_irrefl _)
      have hσw : σ (sSup T) = c := by
        refine le_antisymm hwT.2 (not_lt.1 fun hlt => ?_)
        obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hσc.continuousAt (c - σ (sSup T)) (by linarith)
        have hu1 : sSup T < min (sSup T + δ / 2) β := lt_min (by linarith) hwβ
        have hu : min (sSup T + δ / 2) β ∈ T := by
          refine ⟨⟨le_trans hwT.1.1 hu1.le, min_le_right _ _⟩, ?_⟩
          have hd : dist (min (sSup T + δ / 2) β) (sSup T) < δ := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            have := min_le_left (sSup T + δ / 2) β
            linarith
          have h2 := hball hd
          rw [Real.dist_eq] at h2
          have h3 := (abs_lt.1 h2).2
          show σ (min (sSup T + δ / 2) β) ≤ c
          linarith
        exact absurd (hle _ hu) (not_le.2 hu1)
      have h1 : σ ⁻¹' Iic c ∩ Ioo α β = Ioc α (sSup T) := by
        ext u
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
        constructor
        · rintro ⟨hu, hαu, huβ⟩
          exact ⟨hαu, hle u ⟨⟨hαu.le, huβ.le⟩, hu⟩⟩
        · rintro ⟨hαu, huw⟩
          exact ⟨(hσm huw).trans hσw.le, hαu, lt_of_le_of_lt huw hwβ⟩
      have h2 : Iic c ∩ Ioo (σ α) (σ β) = Ioc (σ α) c := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
        constructor
        · rintro ⟨htc, hαt, -⟩
          exact ⟨hαt, htc⟩
        · rintro ⟨hαt, htc⟩
          exact ⟨htc, hαt, lt_of_le_of_lt htc hc'⟩
      rw [h1, h2, setLIntegral_congr Ioo_ae_eq_Ioc.symm, setLIntegral_congr Ioo_ae_eq_Ioc.symm,
        hkey _ hwT.1, hσw]
  calc ∫⁻ u in Ioo α β, g (σ u) * ‖deriv (F ∘ σ) u‖ₑ
      = ∫⁻ u, g (σ u) ∂((volume.restrict (Ioo α β)).withDensity fun u => ‖deriv (F ∘ σ) u‖ₑ) := by
        have e := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioo α β)) hmG
          (hg.comp hσm.measurable)
        refine Eq.trans ?_ e.symm
        refine lintegral_congr fun u => ?_
        simp only [Pi.mul_apply, Function.comp_apply]
        ring
    _ = ∫⁻ t, g t ∂(((volume.restrict (Ioo α β)).withDensity fun u => ‖deriv (F ∘ σ) u‖ₑ).map σ) :=
        (lintegral_map hg hσm.measurable).symm
    _ = ∫⁻ t, g t ∂((volume.restrict (Ioo (σ α) (σ β))).withDensity fun t => ‖deriv F t‖ₑ) := by
        rw [hmap]
    _ = ∫⁻ t in Ioo (σ α) (σ β), g t * ‖deriv F t‖ₑ := by
        have e := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioo (σ α) (σ β))) hmF hg
        refine e.trans ?_
        refine lintegral_congr fun t => ?_
        simp only [Pi.mul_apply]
        ring

/-- **An arclength-type reparametrization**: for `f ≥ 0` with finite integral `I` over `(0, 1)`, there are a monotone
continuous `σ : [0, 1] → [0, 1]` fixing `0` and `1` and a strictly monotone `λ` inverse to it on `[0, 1]` with
`∫⁻_{(s₁, s₂)} f ≤ (I + 1)(λ s₂ - λ s₁)` for `0 ≤ s₁ ≤ s₂ ≤ 1`: `λ(t) = (ℓ(t) + t)/(I + 1)` with
`ℓ(t) = ∫_{(0, t]} f`, continuous by the absolute continuity of the integral, and `σ = λ⁻¹`. -/
theorem s26v_b_arclength (f : ℝ → ℝ≥0∞) (hf : ∫⁻ u in Ioo (0 : ℝ) 1, f u ≠ ⊤) :
    ∃ (σ : unitInterval → unitInterval) (_ : Continuous σ) (_ : σ 0 = 0) (_ : σ 1 = 1) (lam : ℝ → ℝ),
      Monotone σ ∧ StrictMono lam ∧ lam 0 = 0 ∧ lam 1 = 1 ∧
      (∀ u ∈ Icc (0 : ℝ) 1, lam (σ (projIcc 0 1 zero_le_one u)) = u) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (σ (projIcc 0 1 zero_le_one (lam t)) : ℝ) = t) ∧
      ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
        ∫⁻ u in Ioo s₁ s₂, f u ≤ ENNReal.ofReal (((∫⁻ u in Ioo (0 : ℝ) 1, f u).toReal + 1) * (lam s₂ - lam s₁)) := by
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  set L : ℝ → ℝ≥0∞ := fun t => ∫⁻ u in Iic t, f u ∂μ with hL
  have hLle : ∀ t, L t ≤ ∫⁻ u in Ioo (0 : ℝ) 1, f u := fun t => setLIntegral_le_lintegral _ _
  have hLfin : ∀ t, L t ≠ ⊤ := fun t => ne_top_of_le_ne_top hf (hLle t)
  set I := (∫⁻ u in Ioo (0 : ℝ) 1, f u).toReal with hI
  set ℓ : ℝ → ℝ := fun t => (L t).toReal with hℓ
  have hLadd : ∀ t t', t ≤ t' → L t' = L t + ∫⁻ u in Ioc t t', f u ∂μ := by
    intro t t' htt'
    simp only [hL]
    rw [← Iic_union_Ioc_eq_Iic htt', lintegral_union measurableSet_Ioc (Iic_disjoint_Ioc le_rfl)]
  have hinc : ∀ t t', t ≤ t' → ℓ t' - ℓ t = (∫⁻ u in Ioc t t', f u ∂μ).toReal := by
    intro t t' htt'
    have hX : ∫⁻ u in Ioc t t', f u ∂μ ≠ ⊤ := ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)
    simp only [hℓ]
    rw [hLadd t t' htt', ENNReal.toReal_add (hLfin t) hX]
    ring
  have hℓm : Monotone ℓ := fun t t' htt' => by
    have h := hinc t t' htt'
    have h0 : 0 ≤ (∫⁻ u in Ioc t t', f u ∂μ).toReal := ENNReal.toReal_nonneg
    linarith
  have hℓ0 : ℓ 0 = 0 := by
    have h : L 0 = 0 := by
      simp only [hL, hμ, Measure.restrict_restrict measurableSet_Iic]
      rw [show Iic (0 : ℝ) ∩ Ioo 0 1 = ∅ from
        eq_empty_of_forall_notMem fun u hu => absurd (mem_Iic.1 hu.1) (not_le.2 hu.2.1)]
      simp
    simp [hℓ, h]
  have hℓ1 : ℓ 1 = I := by
    have h : L 1 = ∫⁻ u in Ioo (0 : ℝ) 1, f u := by
      simp only [hL, hμ, Measure.restrict_restrict measurableSet_Iic]
      rw [show Iic (1 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 from inter_eq_right.2 fun u hu => mem_Iic.2 hu.2.le]
    simp [hℓ, h, hI]
  have hℓbd : ∀ t, 0 ≤ ℓ t ∧ ℓ t ≤ I := fun t =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hf (hLle t)⟩
  have hℓc : Continuous ℓ := by
    rw [Metric.continuous_iff]
    intro t ε hε
    obtain ⟨δ, hδ, hδs⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := μ) (f := f) hf
      (ENNReal.ofReal_pos.2 hε).ne'
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
    have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
    have key : ∀ a b, a ≤ b → b - a < r → ℓ b - ℓ a < ε := by
      intro a b hab hba
      rw [hinc a b hab]
      have hm : μ (Ioc a b) < δ := by
        calc μ (Ioc a b) ≤ volume (Ioc a b) := Measure.restrict_apply_le _ _
          _ = ENNReal.ofReal (b - a) := Real.volume_Ioc
          _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hba
          _ < δ := hr2
      exact ENNReal.toReal_lt_of_lt_ofReal (hδs _ hm)
    refine ⟨r, hrpos, fun t' ht' => ?_⟩
    rw [Real.dist_eq, abs_lt] at ht' ⊢
    rcases le_total t t' with h | h
    · have h1 := key t t' h (by linarith [ht'.2])
      have h2 := hℓm h
      constructor <;> linarith
    · have h1 := key t' t h (by linarith [ht'.1])
      have h2 := hℓm h
      constructor <;> linarith
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hI1 : 0 < I + 1 := by linarith
  set lam : ℝ → ℝ := fun t => (ℓ t + t) / (I + 1) with hlam
  have hlm : StrictMono lam := fun t t' htt' =>
    div_lt_div_of_pos_right (add_lt_add_of_le_of_lt (hℓm htt'.le) htt') hI1
  have hlc : Continuous lam := (hℓc.add continuous_id).div_const _
  have hl0 : lam 0 = 0 := by simp [hlam, hℓ0]
  have hl1 : lam 1 = 1 := by
    simp only [hlam, hℓ1]
    exact div_self hI1.ne'
  have hsurj : Function.Surjective lam := by
    refine hlc.surjective ?_ ?_
    · refine tendsto_atTop_mono (fun t => ?_) (tendsto_id.atTop_div_const hI1)
      exact div_le_div_of_nonneg_right (by simp only [id]; linarith [(hℓbd t).1]) hI1.le
    · refine tendsto_atBot_mono (fun t => ?_)
        ((tendsto_atBot_add_const_right _ I tendsto_id).atBot_div_const hI1)
      exact div_le_div_of_nonneg_right (by simp only [id]; linarith [(hℓbd t).2]) hI1.le
  set e := StrictMono.orderIsoOfSurjective lam hlm hsurj with he
  have he0 : e.symm 0 = 0 := by
    have h := StrictMono.orderIsoOfSurjective_symm_apply_self lam hlm hsurj 0
    rwa [hl0] at h
  have he1 : e.symm 1 = 1 := by
    have h := StrictMono.orderIsoOfSurjective_symm_apply_self lam hlm hsurj 1
    rwa [hl1] at h
  have heI : ∀ u ∈ Icc (0 : ℝ) 1, e.symm u ∈ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨he0 ▸ e.symm.monotone hu.1, he1 ▸ e.symm.monotone hu.2⟩
  refine ⟨fun u => ⟨e.symm u, heI u u.2⟩,
    Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _, Subtype.ext he0, Subtype.ext he1,
    lam, fun u v huv => e.symm.monotone huv, hlm, hl0, hl1, ?_, ?_, ?_⟩
  · intro u hu
    simp only [projIcc_of_mem _ hu]
    exact StrictMono.orderIsoOfSurjective_self_symm_apply lam hlm hsurj u
  · intro t ht
    have hlt : lam t ∈ Icc (0 : ℝ) 1 := ⟨hl0 ▸ hlm.monotone ht.1, hl1 ▸ hlm.monotone ht.2⟩
    simp only [projIcc_of_mem _ hlt]
    exact StrictMono.orderIsoOfSurjective_symm_apply_self lam hlm hsurj t
  · intro s₁ s₂ hs₁ hs₁₂ hs₂
    have hsub : Ioo s₁ s₂ ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo hs₁ hs₂
    have e1 : ∫⁻ u in Ioo s₁ s₂, f u = ∫⁻ u in Ioo s₁ s₂, f u ∂μ := by
      rw [hμ, Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 hsub]
    have hX : ∫⁻ u in Ioc s₁ s₂, f u ∂μ ≠ ⊤ := ne_top_of_le_ne_top hf (setLIntegral_le_lintegral _ _)
    have hlin : (I + 1) * (lam s₂ - lam s₁) = (ℓ s₂ + s₂) - (ℓ s₁ + s₁) := by
      simp only [hlam]
      field_simp
    calc ∫⁻ u in Ioo s₁ s₂, f u = ∫⁻ u in Ioo s₁ s₂, f u ∂μ := e1
      _ ≤ ∫⁻ u in Ioc s₁ s₂, f u ∂μ := lintegral_mono_set Ioo_subset_Ioc_self
      _ = ENNReal.ofReal (ℓ s₂ - ℓ s₁) := by rw [hinc s₁ s₂ hs₁₂, ENNReal.ofReal_toReal hX]
      _ ≤ ENNReal.ofReal ((I + 1) * (lam s₂ - lam s₁)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hlin]
          linarith

/-- The extension of a reparametrized path: `(γ ∘ σ).extend u = γ.extend (σ (proj u))`. -/
theorem s26v_b_reparam_extend {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (σ : unitInterval → unitInterval) (hσ : Continuous σ) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (u : ℝ) :
    (γ.reparam σ hσ h0 h1).extend u = γ.extend (σ (projIcc 0 1 zero_le_one u)) := by
  rw [Path.extend_extends']
  rfl

/-- The real reparametrization `u ↦ σ (proj u)` induced by a monotone continuous `σ : [0, 1] → [0, 1]` is monotone
and continuous. -/
theorem s26v_b_reparam_real (σ : unitInterval → unitInterval) (hσ : Continuous σ) (hmono : Monotone σ) :
    Monotone (fun u : ℝ => (σ (projIcc 0 1 zero_le_one u) : ℝ)) ∧
      Continuous (fun u : ℝ => (σ (projIcc 0 1 zero_le_one u) : ℝ)) :=
  ⟨fun _ _ huv => hmono (monotone_projIcc zero_le_one huv),
    continuous_subtype_val.comp (hσ.comp continuous_projIcc)⟩

/-- **One chart piece of a reparametrized good path**: the `q`-length integrand of `γ ∘ σ` over `(α, β)` in the chart
at `x` integrates to `∫_{(σ α, σ β)} speed(γ)` (`s26v_b_reparam_lintegral` with the weight `|q_x|^{1/2}`, and the
chart independence of the speed, `s26n_density_speed_chart`). -/
theorem s26v_b_piece [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S₀} {γ : Path a b}
    (hγ : s26v_IsGoodPath q γ) (σ : unitInterval → unitInterval) (hσ : Continuous σ) (h0 : σ 0 = 0)
    (h1 : σ 1 = 1) (hmono : Monotone σ) (x : S₀) {α β : ℝ} (hαβ : α ≤ β)
    (hsrc : (γ.reparam σ hσ h0 h1).extend '' Icc α β ⊆ (chartAt ℂ x).source)
    (hAC : AbsolutelyContinuousOnInterval (fun v => chartAt ℂ x ((γ.reparam σ hσ h0 h1).extend v)) α β) :
    ∫⁻ u in Ioo α β, phiDensity (q x) (chartAt ℂ x ((γ.reparam σ hσ h0 h1).extend u)) *
        ‖deriv (fun v => chartAt ℂ x ((γ.reparam σ hσ h0 h1).extend v)) u‖ₑ =
      ∫⁻ t in Ioo ((σ (projIcc 0 1 zero_le_one α) : ℝ)) ((σ (projIcc 0 1 zero_le_one β) : ℝ)),
        s26v_speed q γ t := by
  set σ' : ℝ → ℝ := fun u => (σ (projIcc 0 1 zero_le_one u) : ℝ) with hσ'
  obtain ⟨hσ'm, hσ'c⟩ := s26v_b_reparam_real σ hσ hmono
  have hext : ∀ u, (γ.reparam σ hσ h0 h1).extend u = γ.extend (σ' u) := fun u =>
    s26v_b_reparam_extend γ σ hσ h0 h1 u
  set F : ℝ → ℂ := fun t => chartAt ℂ x (γ.extend t) with hF
  have hFG : (fun v => chartAt ℂ x ((γ.reparam σ hσ h0 h1).extend v)) = F ∘ σ' := by
    funext v
    simp only [Function.comp_apply, hF, hext]
  have hσ'αβ : σ' α ≤ σ' β := hσ'm hαβ
  have hsrc' : γ.extend '' Icc (σ' α) (σ' β) ⊆ (chartAt ℂ x).source := by
    rw [← s26v_b_image_Icc hσ'm hσ'c hαβ, image_image]
    intro p hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact hsrc ⟨u, hu, hext u⟩
  have hσ'I : ∀ u, σ' u ∈ Icc (0 : ℝ) 1 := fun u => (σ (projIcc 0 1 zero_le_one u)).2
  have hFAC : AbsolutelyContinuousOnInterval F (σ' α) (σ' β) := by
    rcases hσ'αβ.lt_or_eq with hlt | heq
    · exact hγ.2 x (σ' α) (σ' β) (hσ'I α).1 hlt (hσ'I β).2 hsrc'
    · rw [heq]
  have hGAC : AbsolutelyContinuousOnInterval (F ∘ σ') α β := hFG ▸ hAC
  have hFc : ContinuousOn F (Icc (σ' α) (σ' β)) := fun t ht =>
    (((chartAt ℂ x).continuousAt (hsrc' ⟨t, ht, rfl⟩)).comp
      γ.continuous_extend.continuousAt).continuousWithinAt
  set g : ℝ → ℝ≥0∞ := fun t => phiDensity (q x) (F (projIcc (σ' α) (σ' β) hσ'αβ t)) with hg
  have hgm : Measurable g := by
    have h1 : Continuous fun t => F (projIcc (σ' α) (σ' β) hσ'αβ t) :=
      hFc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t => (projIcc _ _ _ t).2
    have h2 : Measurable fun z => phiDensity (q x) z :=
      (s26v_b_measurable_q hq x).norm.sqrt.ennreal_ofReal
    exact h2.comp h1.measurable
  have hB := s26v_b_reparam_lintegral hαβ hσ'm hσ'c hFAC hGAC hgm
  rw [hFG]
  calc ∫⁻ u in Ioo α β, phiDensity (q x) (chartAt ℂ x ((γ.reparam σ hσ h0 h1).extend u)) *
        ‖deriv (F ∘ σ') u‖ₑ
      = ∫⁻ u in Ioo α β, g (σ' u) * ‖deriv (F ∘ σ') u‖ₑ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        have hmem : σ' u ∈ Icc (σ' α) (σ' β) := ⟨hσ'm hu.1.le, hσ'm hu.2.le⟩
        simp only [hg, hext u, projIcc_of_mem _ hmem, hF]
    _ = ∫⁻ t in Ioo (σ' α) (σ' β), g t * ‖deriv F t‖ₑ := hB
    _ = ∫⁻ t in Ioo (σ' α) (σ' β), s26v_speed q γ t := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        have hmem : t ∈ Icc (σ' α) (σ' β) := Ioo_subset_Icc_self ht
        simp only [hg, projIcc_of_mem _ hmem, s26v_speed]
        exact s26n_density_speed_chart hq x (γ.extend t) γ.continuous_extend.continuousAt
          (hsrc' ⟨t, hmem, rfl⟩) (mem_chart_source ℂ _)

/-- **[V9a, stub]** (T4, the length of a good path).  For a good path, the reparametrization-invariant length is the
integral of the `q`-speed.  (Every admissible Lipschitz reparametrization has the same weighted length, by the
invariance of the variation under monotone reparametrization; the inverse of `t ↦ ℓ_q(t) + εt` gives one with
Lipschitz chart pieces, since `|q|` is bounded below on the compact image.) -/
theorem s26v_phiLengthPathInv_eq [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S₀}
    {γ : Path a b} (hγ : s26v_IsGoodPath q γ) :
    phiLengthPathInv q γ = ∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q γ u := by
  apply le_antisymm
  · by_cases hItop : ∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q γ u = ⊤
    · rw [hItop]
      exact le_top
    obtain ⟨σ, hσ, h0, h1, lam, hσm, hlm, hl0, hl1, hlσ, hσl, hbound⟩ := s26v_b_arclength _ hItop
    set I := (∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q γ u).toReal with hI
    have hI1 : 0 < I + 1 := by
      have h := ENNReal.toReal_nonneg (a := ∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q γ u)
      linarith
    obtain ⟨hσ'm, -⟩ := s26v_b_reparam_real σ hσ hσm
    have hext : ∀ u, (γ.reparam σ hσ h0 h1).extend u = γ.extend (σ (projIcc 0 1 zero_le_one u)) := fun u =>
      s26v_b_reparam_extend γ σ hσ h0 h1 u
    refine iInf_le_of_le σ (iInf_le_of_le hσ (iInf_le_of_le h0 (iInf_le_of_le h1 (iInf_le_of_le hσm ?_))))
    unfold phiLengthPath phiLengthOn
    set cov : S₀ → Set ℝ := fun y => γ.extend ⁻¹' {p | p ∈ (chartAt ℂ y).source ∧
      q y (chartAt ℂ y y) ≠ 0 ∧ ‖q y (chartAt ℂ y y)‖ < 2 * ‖q y (chartAt ℂ y p)‖} with hcov
    have hcovo : ∀ y, IsOpen (cov y) := by
      intro y
      refine IsOpen.preimage γ.continuous_extend ?_
      by_cases hy : q y (chartAt ℂ y y) = 0
      · convert isOpen_empty
        ext p
        simp [hy]
      · have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
        have hcont : ContinuousOn (fun p => ‖q y (chartAt ℂ y p)‖) (chartAt ℂ y).source :=
          ((hq'.2 y).continuousOn.comp (chartAt ℂ y).continuousOn (chartAt ℂ y).mapsTo).norm
        have h := hcont.isOpen_inter_preimage (chartAt ℂ y).open_source
          (isOpen_Ioi (a := ‖q y (chartAt ℂ y y)‖ / 2))
        convert h using 1
        ext p
        simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
        constructor
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, hy, by linarith⟩
    have hcovU : Icc (0 : ℝ) 1 ⊆ ⋃ y, cov y := by
      intro t ht
      have hne := hγ.1 t ht
      have hpos : 0 < ‖q (γ.extend t) (chartAt ℂ (γ.extend t) (γ.extend t))‖ := norm_pos_iff.2 hne
      exact mem_iUnion.2 ⟨γ.extend t, mem_chart_source ℂ _, hne, by linarith⟩
    obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hcovo hcovU
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    set tt : Fin (N + 1 + 1) → ℝ := fun i => (i : ℝ) / (N + 1) with htt
    have htt01 : ∀ i : Fin (N + 1 + 1), tt i ∈ Icc (0 : ℝ) 1 := by
      intro i
      refine ⟨by positivity, ?_⟩
      rw [htt, div_le_one hN1]
      exact_mod_cast Nat.lt_succ_iff.1 i.2
    have httm : Monotone tt := fun i j hij => by
      simp only [htt]
      gcongr
      exact_mod_cast hij
    choose y hy using fun i : Fin (N + 1) => hleb (tt i.castSucc) (htt01 _)
    have hsub : ∀ i : Fin (N + 1), Icc (tt i.castSucc) (tt i.succ) ⊆ cov (y i) := by
      intro i t ht
      apply hy i
      rw [Real.ball_eq_Ioo]
      have hlen : tt i.succ - tt i.castSucc = 1 / (N + 1) := by
        simp only [htt, Fin.val_succ, Fin.val_castSucc]
        push_cast
        field_simp
        ring
      constructor
      · linarith [ht.1]
      · linarith [ht.2]
    set τ : Fin (N + 1 + 1) → ℝ := fun i => lam (tt i) with hτ
    have hτm : Monotone τ := hlm.monotone.comp httm
    have htt0 : tt 0 = 0 := by simp [htt]
    have htt1 : tt (Fin.last (N + 1)) = 1 := by
      simp only [htt, Fin.val_last]
      push_cast
      exact div_self hN1.ne'
    have hτ0 : τ 0 = 0 := by simp only [hτ, htt0, hl0]
    have hτ1 : τ (Fin.last (N + 1)) = 1 := by simp only [hτ, htt1, hl1]
    have hτI : ∀ i, τ i ∈ Icc (0 : ℝ) 1 := fun i =>
      ⟨hl0 ▸ hlm.monotone (htt01 i).1, hl1 ▸ hlm.monotone (htt01 i).2⟩
    have hστ : ∀ i, (σ (projIcc 0 1 zero_le_one (τ i)) : ℝ) = tt i := fun i => hσl (tt i) (htt01 i)
    have hsI : ∀ (i : Fin (N + 1)), ∀ v ∈ Icc (τ i.castSucc) (τ i.succ),
        (σ (projIcc 0 1 zero_le_one v) : ℝ) ∈ Icc (tt i.castSucc) (tt i.succ) := by
      intro i v hv
      rw [← hστ, ← hστ]
      exact ⟨hσ'm hv.1, hσ'm hv.2⟩
    have hvI : ∀ (i : Fin (N + 1)), ∀ v ∈ Icc (τ i.castSucc) (τ i.succ), v ∈ Icc (0 : ℝ) 1 := fun i v hv =>
      ⟨(hτI _).1.trans hv.1, hv.2.trans (hτI _).2⟩
    have himg : ∀ i : Fin (N + 1),
        (γ.reparam σ hσ h0 h1).extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (y i)).source := by
      intro i p hp
      obtain ⟨v, hv, rfl⟩ := hp
      rw [hext v]
      exact (hsub i (hsI i v hv)).1
    have hLip : ∀ i : Fin (N + 1), ∃ K : ℝ≥0, LipschitzOnWith K
        (fun v => chartAt ℂ (y i) ((γ.reparam σ hσ h0 h1).extend v)) (Icc (τ i.castSucc) (τ i.succ)) := by
      intro i
      set m : ℝ := ‖q (y i) (chartAt ℂ (y i) (y i))‖ / 2 with hm
      have hmpos : 0 < m := by
        have h := (hsub i ⟨le_rfl, httm (Fin.castSucc_le_succ i)⟩).2.1
        have := norm_pos_iff.2 h
        rw [hm]
        positivity
      set F : ℝ → ℂ := fun t => chartAt ℂ (y i) (γ.extend t) with hF
      have hest : ∀ v₁ ∈ Icc (τ i.castSucc) (τ i.succ), ∀ v₂ ∈ Icc (τ i.castSucc) (τ i.succ), v₁ ≤ v₂ →
          edist (F (σ (projIcc 0 1 zero_le_one v₂))) (F (σ (projIcc 0 1 zero_le_one v₁))) ≤
            ENNReal.ofReal ((I + 1) / Real.sqrt m) * edist v₂ v₁ := by
        intro v₁ hv₁ v₂ hv₂ hv₁₂
        have hs₁ := hsI i v₁ hv₁
        have hs₂ := hsI i v₂ hv₂
        have hs₁₂ : (σ (projIcc 0 1 zero_le_one v₁) : ℝ) ≤ σ (projIcc 0 1 zero_le_one v₂) := hσ'm hv₁₂
        have hsrc : γ.extend '' Icc (σ (projIcc 0 1 zero_le_one v₁) : ℝ) (σ (projIcc 0 1 zero_le_one v₂)) ⊆
            (chartAt ℂ (y i)).source := by
          rintro _ ⟨t, ht, rfl⟩
          exact (hsub i ⟨hs₁.1.trans ht.1, ht.2.trans hs₂.2⟩).1
        have hFAC : AbsolutelyContinuousOnInterval F (σ (projIcc 0 1 zero_le_one v₁))
            (σ (projIcc 0 1 zero_le_one v₂)) := by
          rcases hs₁₂.lt_or_eq with hlt | heq
          · exact hγ.2 (y i) _ _ ((htt01 _).1.trans hs₁.1) hlt (hs₂.2.trans (htt01 _).2) hsrc
          · rw [heq]
        have h1 := s26v_b_edist_le_lintegral hs₁₂ hFAC
        have h2 : ∫⁻ t in Ioo (σ (projIcc 0 1 zero_le_one v₁) : ℝ) (σ (projIcc 0 1 zero_le_one v₂)),
            ‖deriv F t‖ₑ ≤ ENNReal.ofReal (1 / Real.sqrt m) *
              ∫⁻ t in Ioo (σ (projIcc 0 1 zero_le_one v₁) : ℝ) (σ (projIcc 0 1 zero_le_one v₂)),
                s26v_speed q γ t := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          have htI : t ∈ Icc (tt i.castSucc) (tt i.succ) := ⟨hs₁.1.trans ht.1.le, ht.2.le.trans hs₂.2⟩
          obtain ⟨htsrc, -, htq⟩ := hsub i htI
          have hspeed : s26v_speed q γ t = phiDensity (q (y i)) (F t) * ‖deriv F t‖ₑ :=
            (s26n_density_speed_chart hq (y i) (γ.extend t) γ.continuous_extend.continuousAt htsrc
              (mem_chart_source ℂ _)).symm
          have hone : 1 ≤ ENNReal.ofReal (1 / Real.sqrt m) * phiDensity (q (y i)) (F t) := by
            simp only [phiDensity, hF]
            rw [← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal]
            have hsq : Real.sqrt m ≤ Real.sqrt ‖q (y i) (chartAt ℂ (y i) (γ.extend t))‖ :=
              Real.sqrt_le_sqrt (by rw [hm]; linarith)
            have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
            rw [one_div, inv_mul_eq_div, one_le_div hsm]
            exact hsq
          rw [hspeed, ← mul_assoc]
          calc ‖deriv F t‖ₑ = 1 * ‖deriv F t‖ₑ := (one_mul _).symm
            _ ≤ ENNReal.ofReal (1 / Real.sqrt m) * phiDensity (q (y i)) (F t) * ‖deriv F t‖ₑ := by
                gcongr
        have h3 := hbound _ _ ((htt01 _).1.trans hs₁.1) hs₁₂ (hs₂.2.trans (htt01 _).2)
        rw [hlσ v₁ (hvI i v₁ hv₁), hlσ v₂ (hvI i v₂ hv₂)] at h3
        calc edist (F (σ (projIcc 0 1 zero_le_one v₂))) (F (σ (projIcc 0 1 zero_le_one v₁)))
            ≤ ∫⁻ t in Ioo (σ (projIcc 0 1 zero_le_one v₁) : ℝ) (σ (projIcc 0 1 zero_le_one v₂)),
                ‖deriv F t‖ₑ := h1
          _ ≤ ENNReal.ofReal (1 / Real.sqrt m) *
              ∫⁻ t in Ioo (σ (projIcc 0 1 zero_le_one v₁) : ℝ) (σ (projIcc 0 1 zero_le_one v₂)),
                s26v_speed q γ t := h2
          _ ≤ ENNReal.ofReal (1 / Real.sqrt m) * ENNReal.ofReal ((I + 1) * (v₂ - v₁)) := by
              gcongr
          _ = ENNReal.ofReal ((I + 1) / Real.sqrt m) * edist v₂ v₁ := by
              rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hv₁₂),
                ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
      refine ⟨((I + 1) / Real.sqrt m).toNNReal, fun v₁ hv₁ v₂ hv₂ => ?_⟩
      simp only [hext]
      rcases le_total v₁ v₂ with h | h
      · rw [edist_comm, edist_comm v₁]
        exact hest v₁ hv₁ v₂ hv₂ h
      · exact hest v₂ hv₂ v₁ hv₁ h
    refine iInf_le_of_le (N + 1) (iInf_le_of_le τ (iInf_le_of_le y
      (iInf_le_of_le ⟨hτ0, hτ1, hτm, fun i => ⟨himg i, hLip i⟩⟩ ?_)))
    calc ∑ i : Fin (N + 1), ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
          phiDensity (q (y i)) (chartAt ℂ (y i) ((γ.reparam σ hσ h0 h1).extend u)) *
            ‖deriv (fun v => chartAt ℂ (y i) ((γ.reparam σ hσ h0 h1).extend v)) u‖ₑ
        = ∑ i : Fin (N + 1), ∫⁻ t in Ioo (tt i.castSucc) (tt i.succ), s26v_speed q γ t := by
          refine Finset.sum_congr rfl fun i _ => ?_
          obtain ⟨K, hK⟩ := hLip i
          have hαβ : τ i.castSucc ≤ τ i.succ := hτm (Fin.castSucc_le_succ i)
          have hAC := (show LipschitzOnWith K _ (uIcc (τ i.castSucc) (τ i.succ)) by
            rwa [uIcc_of_le hαβ]).absolutelyContinuousOnInterval
          rw [s26v_b_piece hq hγ σ hσ h0 h1 hσm (y i) hαβ (himg i) hAC, hστ, hστ]
      _ ≤ ∫⁻ t in Ioo (tt 0) (tt (Fin.last (N + 1))), s26v_speed q γ t :=
          s26v_b_sum_le_lintegral _ (N + 1) tt httm
      _ = ∫⁻ t in Ioo (0 : ℝ) 1, s26v_speed q γ t := by rw [htt0, htt1]
  · refine le_iInf fun σ => le_iInf fun hσ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hmono => ?_
    unfold phiLengthPath phiLengthOn
    refine le_iInf fun n => le_iInf fun τ => le_iInf fun x => le_iInf fun hP => ?_
    obtain ⟨hτ0, hτ1, hτm, hpc⟩ := hP
    set σ' : ℝ → ℝ := fun u => (σ (projIcc 0 1 zero_le_one u) : ℝ) with hσ'
    obtain ⟨hσ'm, -⟩ := s26v_b_reparam_real σ hσ hmono
    have hp0 : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp)
    have hp1 : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := Subtype.ext (by simp)
    have hσ'0 : σ' 0 = 0 := by simp only [hσ', hp0, h0, Set.Icc.coe_zero]
    have hσ'1 : σ' 1 = 1 := by simp only [hσ', hp1, h1, Set.Icc.coe_one]
    have hτ'm : Monotone fun i => σ' (τ i) := hσ'm.comp hτm
    calc ∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q γ u
        = ∫⁻ u in Ioo (σ' (τ 0)) (σ' (τ (Fin.last n))), s26v_speed q γ u := by rw [hτ0, hτ1, hσ'0, hσ'1]
      _ ≤ ∑ i : Fin n, ∫⁻ u in Ioo (σ' (τ i.castSucc)) (σ' (τ i.succ)), s26v_speed q γ u :=
          s26n_lintegral_le_sum _ n (fun i => σ' (τ i)) hτ'm
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          obtain ⟨hsrc, K, hK⟩ := hpc i
          have hαβ : τ i.castSucc ≤ τ i.succ := hτm (Fin.castSucc_le_succ i)
          have hAC := (show LipschitzOnWith K _ (uIcc (τ i.castSucc) (τ i.succ)) by
            rwa [uIcc_of_le hαβ]).absolutelyContinuousOnInterval
          exact (s26v_b_piece hq hγ σ hσ h0 h1 hmono (x i) hαβ hsrc hAC).symm

/-- Under an affine map `u ↦ α + β u` (`β ≠ 0`), disjoint intervals `uIoc` go to disjoint intervals `uIoc` (a common
point of the images forces a common interior point, whose preimage lies in both intervals). -/
theorem s26v_b_uIoc_affine_disjoint {α β x y x' y' : ℝ} (hβ : β ≠ 0) (h : Disjoint (uIoc x y) (uIoc x' y')) :
    Disjoint (uIoc (α + β * x) (α + β * y)) (uIoc (α + β * x') (α + β * y')) := by
  rw [Set.disjoint_left] at h ⊢
  have hbet : ∀ w p p' : ℝ, 0 < (w - p) * (p' - w) → w ∈ uIoc p p' := by
    intro w p p' hw
    rw [mem_uIoc]
    rcases lt_trichotomy w p with h1 | h1 | h1
    · right
      have h2 : p' - w < 0 := by
        by_contra hc
        have hc' := not_lt.1 hc
        nlinarith
      constructor <;> linarith
    · subst h1
      simp at hw
    · left
      have h2 : 0 < p' - w := by
        by_contra hc
        have hc' := not_lt.1 hc
        nlinarith
      constructor <;> linarith
  intro z hz hz'
  have hlow : ∀ p p' : ℝ, z ∈ uIoc p p' →
      ∃ l, l < z ∧ ∀ z₀, l < z₀ → z₀ < z → 0 < (z₀ - p) * (p' - z₀) := by
    intro p p' hzp
    rw [mem_uIoc] at hzp
    rcases hzp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, h1, fun z₀ h3 h4 => mul_pos (by linarith) (by linarith)⟩
    · exact ⟨p', h1, fun z₀ h3 h4 => mul_pos_of_neg_of_neg (by linarith) (by linarith)⟩
  obtain ⟨l₁, hl₁, hb₁⟩ := hlow _ _ hz
  obtain ⟨l₂, hl₂, hb₂⟩ := hlow _ _ hz'
  have hm : max l₁ l₂ < z := max_lt hl₁ hl₂
  have h1 := hb₁ ((max l₁ l₂ + z) / 2) (by linarith [le_max_left l₁ l₂]) (by linarith)
  have h2 := hb₂ ((max l₁ l₂ + z) / 2) (by linarith [le_max_right l₁ l₂]) (by linarith)
  set w := ((max l₁ l₂ + z) / 2 - α) / β with hw
  have hβw : β * w = (max l₁ l₂ + z) / 2 - α := by
    rw [hw, mul_comm, div_mul_cancel₀ _ hβ]
  have hzw : (max l₁ l₂ + z) / 2 = α + β * w := by linarith
  rw [hzw] at h1 h2
  have e1 : 0 < (w - x) * (y - w) := by
    have e : (α + β * w - (α + β * x)) * (α + β * y - (α + β * w)) = β ^ 2 * ((w - x) * (y - w)) := by ring
    rw [e] at h1
    exact pos_of_mul_pos_right h1 (sq_nonneg β)
  have e2 : 0 < (w - x') * (y' - w) := by
    have e : (α + β * w - (α + β * x')) * (α + β * y' - (α + β * w)) = β ^ 2 * ((w - x') * (y' - w)) := by
      ring
    rw [e] at h2
    exact pos_of_mul_pos_right h2 (sq_nonneg β)
  exact h (hbet w x y e1) (hbet w x' y' e2)

/-- Absolute continuity is preserved by an affine change of variable `v ↦ α + β v`, `β ≠ 0` (disjoint interval
families correspond, `s26v_b_uIoc_affine_disjoint`, and lengths scale by `|β|`). -/
theorem s26v_b_ac_affine {X : Type*} [PseudoMetricSpace X] {h : ℝ → X} {a b α β : ℝ} (hβ : β ≠ 0)
    (hac : AbsolutelyContinuousOnInterval h (α + β * a) (α + β * b)) :
    AbsolutelyContinuousOnInterval (fun v => h (α + β * v)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hac ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hac ε hε
  have hβpos : 0 < |β| := abs_pos.2 hβ
  refine ⟨δ / |β|, div_pos hδ hβpos, fun E hE hlen => ?_⟩
  have hmem : ∀ u ∈ uIcc a b, α + β * u ∈ uIcc (α + β * a) (α + β * b) := by
    intro u hu
    rw [mem_uIcc] at hu ⊢
    rcases lt_or_gt_of_ne hβ with hneg | hpos
    · rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        constructor <;> nlinarith
      · left
        constructor <;> nlinarith
    · rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        constructor <;> nlinarith
      · right
        constructor <;> nlinarith
  have e : ∑ i ∈ Finset.range E.1, dist (α + β * (E.2 i).1) (α + β * (E.2 i).2) =
      |β| * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.dist_eq, Real.dist_eq, ← abs_mul]
    congr 1
    ring
  have hlen' : ∑ i ∈ Finset.range E.1, dist (α + β * (E.2 i).1) (α + β * (E.2 i).2) < δ := by
    rw [e]
    calc |β| * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < |β| * (δ / |β|) :=
          mul_lt_mul_of_pos_left hlen hβpos
      _ = δ := by field_simp [hβpos.ne']
  exact hδε (E.1, fun i => (α + β * (E.2 i).1, α + β * (E.2 i).2))
    ⟨fun i hi => ⟨hmem _ (hE.1 i hi).1, hmem _ (hE.1 i hi).2⟩,
      fun i hi j hj hij => s26v_b_uIoc_affine_disjoint hβ (hE.2 hi hj hij)⟩ hlen'

/-- Absolute continuity of a real function glues along adjacent intervals: on `[a, c]` the function is `g a` plus the
primitive of its integrable derivative (the fundamental theorem of calculus on both pieces). -/
theorem s26v_b_ac_glue_real {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : AbsolutelyContinuousOnInterval g a b) (h2 : AbsolutelyContinuousOnInterval g b c) :
    AbsolutelyContinuousOnInterval g a c := by
  have hint : IntervalIntegrable (deriv g) volume a c :=
    h1.intervalIntegrable_deriv.trans h2.intervalIntegrable_deriv
  have hprim := hint.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g a) a c :=
    (LipschitzWith.const (g a)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (hprim.add hconst).congr fun t ht => ?_
  rw [uIcc_of_le (hab.trans hbc)] at ht
  show (∫ v in a..t, deriv g v) + g a = g t
  rcases le_total t b with htb | htb
  · have h1' : AbsolutelyContinuousOnInterval g a t := h1.mono (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right htb)
    rw [h1'.integral_deriv_eq_sub]
    ring
  · have h2' : AbsolutelyContinuousOnInterval g b t := h2.mono (by
      rw [uIcc_of_le htb, uIcc_of_le hbc]
      exact Icc_subset_Icc_right ht.2)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1.intervalIntegrable_deriv
      h2'.intervalIntegrable_deriv, h1.integral_deriv_eq_sub, h2'.integral_deriv_eq_sub]
    ring

/-- Absolute continuity of a curve in `ℂ` glues along adjacent intervals (real and imaginary parts,
`s26v_b_ac_glue_real`). -/
theorem s26v_b_ac_glue {H : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : AbsolutelyContinuousOnInterval H a b) (h2 : AbsolutelyContinuousOnInterval H b c) :
    AbsolutelyContinuousOnInterval H a c := by
  have hre : ∀ {s t : ℝ}, AbsolutelyContinuousOnInterval H s t →
      AbsolutelyContinuousOnInterval (fun v => (H v).re) s t := fun h =>
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h
  have him : ∀ {s t : ℝ}, AbsolutelyContinuousOnInterval H s t →
      AbsolutelyContinuousOnInterval (fun v => (H v).im) s t := fun h =>
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h
  have e1 : AbsolutelyContinuousOnInterval (fun v => ((H v).re : ℂ)) a c :=
    Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
      (s26v_b_ac_glue_real hab hbc (hre h1) (hre h2))
  have e2 : AbsolutelyContinuousOnInterval (fun v => ((H v).im : ℂ)) a c :=
    Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
      (s26v_b_ac_glue_real hab hbc (him h1) (him h2))
  refine (e1.add (e2.const_smul I)).congr fun v _ => ?_
  simp only [Pi.add_apply, smul_eq_mul]
  rw [mul_comm I]
  exact Complex.re_add_im (H v)

/-- Absolute continuity on `[s, t]` from absolute continuity near every point of `[s, t]` (a Lebesgue number of the
local neighbourhoods and `s26v_b_ac_glue` along a uniform subdivision). -/
theorem s26v_b_ac_of_local {H : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hloc : ∀ v ∈ Icc s t, ∃ r > 0, ∀ a b, v - r ≤ a → b ≤ v + r → a ≤ b →
      AbsolutelyContinuousOnInterval H a b) :
    AbsolutelyContinuousOnInterval H s t := by
  rcases hst.eq_or_lt with heq | hlt
  · rw [heq]
  choose! r hr hrac using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := s) (b := t))
    (c := fun v : Icc s t => ball (v : ℝ) (r v)) (fun v => isOpen_ball)
    (fun v hv => mem_iUnion.2 ⟨⟨v, hv⟩, mem_ball_self (hr v hv)⟩)
  have hts : 0 < t - s := sub_pos.2 hlt
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hδ hts)
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set h := (t - s) / (N + 1) with hh
  have hhpos : 0 < h := div_pos hts hN1
  have hhδ : h < δ := by
    have h1 : 1 / ((N : ℝ) + 1) * (t - s) < δ / (t - s) * (t - s) := mul_lt_mul_of_pos_right hN hts
    rw [div_mul_cancel₀ _ hts.ne'] at h1
    calc h = 1 / ((N : ℝ) + 1) * (t - s) := by rw [hh]; ring
      _ < δ := h1
  have hNh : ((N : ℝ) + 1) * h = t - s := by
    rw [hh]
    field_simp
  have key : ∀ k : ℕ, k ≤ N + 1 → AbsolutelyContinuousOnInterval H s (s + k * h) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) + 1 ≤ N + 1 := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hks : s + k * h ∈ Icc s t := ⟨by nlinarith, by nlinarith⟩
      obtain ⟨v, hv⟩ := hleb (s + k * h) hks
      have hsub : Icc (s + k * h) (s + (k + 1) * h) ⊆ ball (v : ℝ) (r v) := by
        intro u hu
        apply hv
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> nlinarith [hu.1, hu.2]
      have ha := hsub ⟨le_rfl, by nlinarith⟩
      have hb := hsub ⟨by nlinarith, le_rfl⟩
      rw [mem_ball, Real.dist_eq, abs_lt] at ha hb
      have hac := hrac v v.2 (s + k * h) (s + (k + 1) * h) (by linarith [ha.1]) (by linarith [hb.2])
        (by nlinarith)
      push_cast
      exact s26v_b_ac_glue (by nlinarith) (by nlinarith) (ih (by omega)) hac
  have hfin := key (N + 1) le_rfl
  have e : s + ((N + 1 : ℕ) : ℝ) * h = t := by
    push_cast
    linarith [hNh]
  rwa [e] at hfin

/-- **Natural-parameter boxes adapted to `f`**: every regular point `y₀` lies in a flow box `(B, Z)` ([V1]) inside the
chart at `y₀` and mapped by `f` into the chart at `f y₀`.  The inverse `ψ` of `Z ∘ φ_{y₀}⁻¹` is holomorphic on `Z(B)`
(`IsConformalOnto.symm`), so `G = (φ_{f y₀} ∘ f ∘ φ_{y₀}⁻¹) ∘ ψ` is `K`-quasiconformal on `Z(B)` (`thm7_1_comp`), with
`ψ (Z y) = φ_{y₀} y` and `G (Z y) = φ_{f y₀} (f y)` on `B`. -/
theorem s26v_b_box [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (f : S₀ ≃ₜ S₀) {K : ℝ}
    (hfK : IsKQCRS f K) {y₀ : S₀} (hy₀ : q y₀ (chartAt ℂ y₀ y₀) ≠ 0) :
    ∃ (B : Set S₀) (Z : S₀ → ℂ) (ψ G : ℂ → ℂ), y₀ ∈ B ∧ B ⊆ (chartAt ℂ y₀).source ∧
      B ⊆ f ⁻¹' (chartAt ℂ (f y₀)).source ∧ s26v_IsFlowBox q B Z ∧ DifferentiableOn ℂ ψ (Z '' B) ∧
      (∀ y ∈ B, ψ (Z y) = chartAt ℂ y₀ y) ∧ IsKQC G (Z '' B) K ∧
      ∀ y ∈ B, G (Z y) = chartAt ℂ (f y₀) (f y) := by
  have hW : (chartAt ℂ y₀).source ∩ f ⁻¹' (chartAt ℂ (f y₀)).source ∈ 𝓝 y₀ :=
    ((chartAt ℂ y₀).open_source.inter ((chartAt ℂ (f y₀)).open_source.preimage f.continuous)).mem_nhds
      ⟨mem_chart_source ℂ y₀, mem_chart_source ℂ (f y₀)⟩
  obtain ⟨B, Z, hy₀B, hBW, hB⟩ := s26v_exists_flowBox hq hy₀ hW
  have hBs : B ⊆ (chartAt ℂ y₀).source := fun y hy => (hBW hy).1
  have hUo : IsOpen (chartAt ℂ y₀ '' B) :=
    ((chartAt ℂ y₀).isOpen_image_iff_of_subset_source hBs).2 hB.1
  have hhd : DifferentiableOn ℂ (fun w => Z ((chartAt ℂ y₀).symm w)) (chartAt ℂ y₀ '' B) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨D, hD, -, -⟩ := hB.2.2.2.2 y hy
    have hwt : chartAt ℂ y₀ y ∈ (chartAt ℂ y₀).target := (chartAt ℂ y₀).map_source (hBs hy)
    have hws : (chartAt ℂ y₀).symm (chartAt ℂ y₀ y) = y := (chartAt ℂ y₀).left_inv (hBs hy)
    obtain ⟨hT, -⟩ := s23_transition y y₀ hwt (by rw [hws]; exact mem_chart_source ℂ y)
    have hTw : chartTransition y y₀ (chartAt ℂ y₀ y) = chartAt ℂ y y := by
      simp only [chartTransition, hws]
    have hev : (fun w => Z ((chartAt ℂ y₀).symm w)) =ᶠ[𝓝 (chartAt ℂ y₀ y)]
        (fun w => Z ((chartAt ℂ y).symm w)) ∘ chartTransition y y₀ := by
      filter_upwards [((chartAt ℂ y₀).isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds
        ⟨hwt, show (chartAt ℂ y₀).symm (chartAt ℂ y₀ y) ∈ (chartAt ℂ y).source by
          rw [hws]; exact mem_chart_source ℂ y⟩] with w hw
      simp only [Function.comp_apply, chartTransition]
      rw [(chartAt ℂ y).left_inv hw.2]
    rw [← hTw] at hD
    exact ((hD.comp _ hT.hasDerivAt).congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
  have hhi : InjOn (fun w => Z ((chartAt ℂ y₀).symm w)) (chartAt ℂ y₀ '' B) := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ h12
    simp only [(chartAt ℂ y₀).left_inv (hBs hy₁), (chartAt ℂ y₀).left_inv (hBs hy₂)] at h12
    rw [hB.2.2.1 hy₁ hy₂ h12]
  have hhU : (fun w => Z ((chartAt ℂ y₀).symm w)) '' (chartAt ℂ y₀ '' B) = Z '' B := by
    rw [image_image]
    refine image_congr fun y hy => ?_
    simp only [(chartAt ℂ y₀).left_inv (hBs hy)]
  have hψ := IsConformalOnto.symm hUo ⟨hhd, hhi, hhU⟩
  have hψQC := isKQC_one_of_conformal hB.2.2.2.1 hψ
  have hsub : Function.invFunOn (fun w => Z ((chartAt ℂ y₀).symm w)) (chartAt ℂ y₀ '' B) '' (Z '' B) ⊆
      localMapDomain f y₀ := by
    rw [hψ.2.2]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(chartAt ℂ y₀).map_source (hBs hy), ?_⟩
    show f ((chartAt ℂ y₀).symm (chartAt ℂ y₀ y)) ∈ (chartAt ℂ (f y₀)).source
    rw [(chartAt ℂ y₀).left_inv (hBs hy)]
    exact (hBW hy).2
  have hG := thm7_1_comp hψQC (hfK.2 y₀) hsub
  rw [one_mul] at hG
  have hψZ : ∀ y ∈ B, Function.invFunOn (fun w => Z ((chartAt ℂ y₀).symm w)) (chartAt ℂ y₀ '' B) (Z y) =
      chartAt ℂ y₀ y := by
    intro y hy
    have h1 : Z y = (fun w => Z ((chartAt ℂ y₀).symm w)) (chartAt ℂ y₀ y) := by
      simp only [(chartAt ℂ y₀).left_inv (hBs hy)]
    rw [h1]
    exact hhi.leftInvOn_invFunOn ⟨y, hy, rfl⟩
  refine ⟨B, Z, _, _, hy₀B, hBs, fun y hy => (hBW hy).2, hB, hψ.1, hψZ, hG, fun y hy => ?_⟩
  simp only [Function.comp_apply, hψZ y hy, localMapExpr, (chartAt ℂ y₀).left_inv (hBs hy)]

/-- Differentiability of `f` in charts transfers from the chart pair `(y₀, f y₀)` to the chart pair at the point
itself (holomorphic transitions on both sides). -/
theorem s26v_b_diff_transfer [IsManifold 𝓘(ℂ) ω S₀] (f : S₀ ≃ₜ S₀) {y y₀ : S₀}
    (hy : y ∈ (chartAt ℂ y₀).source) (hfy : f y ∈ (chartAt ℂ (f y₀)).source)
    (hd : DifferentiableAt ℝ (localMapExpr f y₀) (chartAt ℂ y₀ y)) :
    DifferentiableAt ℝ (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y) := by
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hzt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hyy
  have hzs : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv hyy
  obtain ⟨hτ, -⟩ := s23_transition y₀ y hzt (by rw [hzs]; exact hy)
  have hτz : chartTransition y₀ y (chartAt ℂ y y) = chartAt ℂ y₀ y := by
    simp only [chartTransition, hzs]
  have hLy : localMapExpr f y₀ (chartAt ℂ y₀ y) = chartAt ℂ (f y₀) (f y) := by
    simp only [localMapExpr, (chartAt ℂ y₀).left_inv hy]
  have hwt : localMapExpr f y₀ (chartAt ℂ y₀ y) ∈ (chartAt ℂ (f y₀)).target := by
    rw [hLy]
    exact (chartAt ℂ (f y₀)).map_source hfy
  have hws : (chartAt ℂ (f y₀)).symm (localMapExpr f y₀ (chartAt ℂ y₀ y)) = f y := by
    rw [hLy]
    exact (chartAt ℂ (f y₀)).left_inv hfy
  obtain ⟨hσ, -⟩ := s23_transition (f y) (f y₀) hwt (by rw [hws]; exact mem_chart_source ℂ (f y))
  have hcomp : DifferentiableAt ℝ (chartTransition (f y) (f y₀) ∘ localMapExpr f y₀ ∘ chartTransition y₀ y)
      (chartAt ℂ y y) := by
    refine DifferentiableAt.comp (chartAt ℂ y y) ?_ ?_
    · rw [Function.comp_apply, hτz]
      exact hσ.restrictScalars ℝ
    · refine DifferentiableAt.comp (chartAt ℂ y y) ?_ (hτ.restrictScalars ℝ)
      rw [hτz]
      exact hd
  refine hcomp.congr_of_eventuallyEq ?_
  have hopen : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹'
      ((chartAt ℂ y₀).source ∩ f ⁻¹' (chartAt ℂ (f y₀)).source)) :=
    (chartAt ℂ y).isOpen_inter_preimage_symm
      ((chartAt ℂ y₀).open_source.inter ((chartAt ℂ (f y₀)).open_source.preimage f.continuous))
  filter_upwards [hopen.mem_nhds ⟨hzt, show (chartAt ℂ y).symm (chartAt ℂ y y) ∈
      (chartAt ℂ y₀).source ∩ f ⁻¹' (chartAt ℂ (f y₀)).source by rw [hzs]; exact ⟨hy, hfy⟩⟩] with w hw
  have hw1 : (chartAt ℂ y).symm w ∈ (chartAt ℂ y₀).source := hw.2.1
  have hw2 : f ((chartAt ℂ y).symm w) ∈ (chartAt ℂ (f y₀)).source := hw.2.2
  simp only [Function.comp_apply, localMapExprAt, localMapExpr, chartTransition, hzs]
  rw [(chartAt ℂ y₀).left_inv hw1, (chartAt ℂ (f y₀)).left_inv hw2]

/-- The points where `f` is not differentiable in charts form a set null in every chart (Theorem 9.3 for the local
expressions `localMapExpr f y₀`, `s26v_b_diff_transfer`, holomorphic transitions and a countable cover). -/
theorem s26v_b_nondiff_null [IsManifold 𝓘(ℂ) ω S₀] [SecondCountableTopology S₀] (f : S₀ ≃ₜ S₀) {K : ℝ}
    (hfK : IsKQCRS f K) (x : S₀) :
    volume (chartAt ℂ x '' ({y | ¬ DifferentiableAt ℝ (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y)} ∩
      (chartAt ℂ x).source)) = 0 := by
  set Nf := {y | ¬ DifferentiableAt ℝ (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y)} with hNf
  set W : S₀ → Set S₀ := fun y₀ =>
    (chartAt ℂ x).source ∩ (chartAt ℂ y₀).source ∩ f ⁻¹' (chartAt ℂ (f y₀)).source with hW
  have hWo : ∀ y₀, IsOpen (W y₀) := fun y₀ =>
    ((chartAt ℂ x).open_source.inter (chartAt ℂ y₀).open_source).inter
      ((chartAt ℂ (f y₀)).open_source.preimage f.continuous)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  have hcov : (chartAt ℂ x).source ⊆ ⋃ y₀ ∈ T, W y₀ := by
    intro y hy
    rw [hTU]
    exact mem_iUnion.2 ⟨y, ⟨hy, mem_chart_source ℂ y⟩, mem_chart_source ℂ (f y)⟩
  have hloc : ∀ y₀, volume (chartAt ℂ x '' (Nf ∩ W y₀)) = 0 := by
    intro y₀
    set M := {z | ¬ DifferentiableAt ℝ (localMapExpr f y₀) z} ∩ localMapDomain f y₀ with hM
    have hQ := thm9_3_differentiable_ae (hfK.2 y₀)
    rw [ae_restrict_iff' (hfK.2 y₀).1.measurableSet] at hQ
    have hM0 : volume M = 0 := by
      have h0 := ae_iff.1 hQ
      refine measure_mono_null (fun z hz => ?_) h0
      exact fun h => hz.1 (h hz.2)
    have himg : chartAt ℂ x '' (Nf ∩ W y₀) ⊆ chartTransition x y₀ '' (M ∩ chartAt ℂ y₀ '' W y₀) := by
      rintro _ ⟨y, ⟨hyN, hyW⟩, rfl⟩
      refine ⟨chartAt ℂ y₀ y, ⟨⟨fun hd => hyN (s26v_b_diff_transfer f hyW.1.2 hyW.2 hd), ?_⟩,
        ⟨y, hyW, rfl⟩⟩, ?_⟩
      · refine ⟨(chartAt ℂ y₀).map_source hyW.1.2, ?_⟩
        show f ((chartAt ℂ y₀).symm (chartAt ℂ y₀ y)) ∈ (chartAt ℂ (f y₀)).source
        rw [(chartAt ℂ y₀).left_inv hyW.1.2]
        exact hyW.2
      · simp only [chartTransition, (chartAt ℂ y₀).left_inv hyW.1.2]
    refine measure_mono_null himg (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null inter_subset_left hM0))
    rintro _ ⟨-, ⟨y, hy, rfl⟩⟩
    have hyt := (chartAt ℂ y₀).map_source hy.1.2
    exact ((s23_transition x y₀ hyt (by rw [(chartAt ℂ y₀).left_inv hy.1.2]; exact hy.1.1)).1.restrictScalars
      ℝ).differentiableWithinAt
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun y₀ _ => hloc y₀)
  rintro _ ⟨y, ⟨hyN, hyx⟩, rfl⟩
  obtain ⟨y₀, hy₀T, hyW⟩ := mem_iUnion₂.1 (hcov hyx)
  exact mem_iUnion₂.2 ⟨y₀, hy₀T, y, ⟨hyN, hyW⟩, rfl⟩

/-- In a box, the points whose height lies in a null set `H` are null in every chart: they are the image of the null
set `{w : Im w ∈ H}` under the holomorphic `φ_x ∘ φ_{y₀}⁻¹ ∘ ψ`. -/
theorem s26v_b_height_null [IsManifold 𝓘(ℂ) ω S₀] {B : Set S₀} {Z : S₀ → ℂ} {ψ : ℂ → ℂ} {y₀ : S₀}
    (hBo : IsOpen (Z '' B)) (hBs : B ⊆ (chartAt ℂ y₀).source) (hψ : DifferentiableOn ℂ ψ (Z '' B))
    (hψZ : ∀ y ∈ B, ψ (Z y) = chartAt ℂ y₀ y) {H : Set ℝ} (hH : volume H = 0) (x : S₀) :
    volume (chartAt ℂ x '' ({y | y ∈ B ∧ (Z y).im ∈ H} ∩ (chartAt ℂ x).source)) = 0 := by
  have hnull : volume {w : ℂ | w.im ∈ H} = 0 := by
    have e : {w : ℂ | w.im ∈ H} = Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ H) := by
      ext w
      simp [Complex.measurableEquivRealProd]
    rw [e, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
      Measure.prod_prod, hH, mul_zero]
  set S := {w : ℂ | w ∈ Z '' (B ∩ (chartAt ℂ x).source) ∧ w.im ∈ H} with hS
  have hS0 : volume S = 0 := measure_mono_null (fun w hw => hw.2) hnull
  have hd : DifferentiableOn ℝ (fun w => chartTransition x y₀ (ψ w)) S := by
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩
    have hyt : chartAt ℂ y₀ y ∈ (chartAt ℂ y₀).target := (chartAt ℂ y₀).map_source (hBs hy.1)
    have hT := (s23_transition x y₀ hyt (by rw [(chartAt ℂ y₀).left_inv (hBs hy.1)]; exact hy.2)).1
    have hψd : DifferentiableAt ℂ ψ (Z y) := hψ.differentiableAt (hBo.mem_nhds ⟨y, hy.1, rfl⟩)
    rw [← hψZ y hy.1] at hT
    exact ((hT.comp _ hψd).restrictScalars ℝ).differentiableWithinAt
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd hS0)
  rintro _ ⟨y, ⟨⟨hyB, hyH⟩, hyx⟩, rfl⟩
  refine ⟨Z y, ⟨⟨y, ⟨hyB, hyx⟩, rfl⟩, hyH⟩, ?_⟩
  show chartTransition x y₀ (ψ (Z y)) = chartAt ℂ x y
  rw [hψZ y hyB]
  simp only [chartTransition, (chartAt ℂ y₀).left_inv (hBs hyB)]

/-- A trajectory through a point of a flow box runs, for a while, along the horizontal line through it:
`Z (c T) = Z (c T₀) + σ (T - T₀)` with a real sign `σ = ±1`. -/
theorem s26v_b_line_near {q : S₀ → ℂ → ℂ} {B : Set S₀} {Z : S₀ → ℂ} (hB : s26v_IsFlowBox q B Z)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) {T₀ : ℝ} (hT₀ : c T₀ ∈ B) :
    ∃ δ > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ T ∈ ball T₀ δ, c T ∈ B ∧ Z (c T) = Z (c T₀) + (σ : ℂ) * ((T - T₀ : ℝ) : ℂ) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hB.1.preimage c.continuous) T₀ hT₀
  obtain ⟨σ, hσ, hline⟩ := s26v_b_line_of_box hB isOpen_ball (convex_ball T₀ δ) (fun T _ => hc T)
    (fun T hT => hball hT) (mem_ball_self hδ)
  rcases hσ with rfl | rfl
  · exact ⟨δ, hδ, 1, Or.inl rfl, fun T hT => ⟨hball hT, by rw [hline T hT]; push_cast; ring⟩⟩
  · exact ⟨δ, hδ, -1, Or.inr rfl, fun T hT => ⟨hball hT, by rw [hline T hT]; push_cast; ring⟩⟩

/-- A bi-infinite trajectory `c` puts `c 0` on the chosen trajectory through each of its points `c t` (uniqueness up to
reversal, [V2c]). -/
theorem s26v_b_mem_range_traj [T2Space S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) (t : ℝ) : c 0 ∈ range (s26v_traj q (c t)) := by
  set c' : C(ℝ, S₀) := c.comp ⟨fun s => s + t, by fun_prop⟩ with hc'
  have hc'T : s26v_IsTraj q c' := fun s => s26v_trajAt_shift (hc (s + t))
  have hc'0 : c' 0 = c t := by simp [hc']
  have hnE : c t ∉ s26v_E q := fun h => h ⟨c', hc'T, hc'0⟩
  obtain ⟨hT, hT0⟩ := s26v_traj_spec hnE
  rcases s26v_traj_unique hq hT hc'T (hT0.trans hc'0.symm) with h | h
  · refine ⟨-t, ?_⟩
    rw [← h (-t)]
    simp [hc']
  · refine ⟨t, ?_⟩
    have h1 := h (-t)
    rw [neg_neg] at h1
    rw [← h1]
    simp [hc']

/-- **The `q`-speed of `f(α)`**: at an interior time `u` of the arc of a bi-infinite trajectory, where `f` is
differentiable in charts at `c(t)`, `t = -L + 2Lu`, the `q`-speed of `f ∘ α` is `2L λ_f(c(t))` (the computation of
`s26n_pointwise`, with `c̄' = c' q/|q|` since `q c'² = 1`). -/
theorem s26v_b_speed_eq [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (f : S₀ ≃ₜ S₀)
    {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ (localMapExprAt f (c (-L + 2 * L * u))
      (chartAt ℂ (c (-L + 2 * L * u)) (c (-L + 2 * L * u)))) (chartAt ℂ (c (-L + 2 * L * u)) (c (-L + 2 * L * u)))) :
    s26v_speed q ((s26v_arc c L).map f.continuous) u =
      ENNReal.ofReal (2 * L) * s26v_lam q f (c (-L + 2 * L * u)) := by
  set y := c (-L + 2 * L * u) with hy
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hzs : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv hyy
  have hext : ∀ v ∈ Icc (0 : ℝ) 1, ((s26v_arc c L).map f.continuous).extend v = f (c (-L + 2 * L * v)) :=
    fun v hv => by
      rw [Path.extend_apply _ hv]
      rfl
  have hextu : ((s26v_arc c L).map f.continuous).extend u = f y := hext u (Ioo_subset_Icc_self hu)
  obtain ⟨v, hv, hqv⟩ := s26v_b_arc_deriv hq hc L y hyy
  have hqv' : q y (chartAt ℂ y y) * v ^ 2 = 1 := hqv
  have hcont : ContinuousAt (fun r : ℝ => c (-L + 2 * L * r)) u := by fun_prop
  have hev : (fun r => chartAt ℂ (f y) (((s26v_arc c L).map f.continuous).extend r)) =ᶠ[𝓝 u]
      localMapExprAt f y (chartAt ℂ y y) ∘ fun r => chartAt ℂ y (c (-L + 2 * L * r)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2, hcont.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hyy)]
      with r hr hrs
    rw [hext r (Ioo_subset_Icc_self hr)]
    simp only [Function.comp_apply, localMapExprAt, hzs]
    rw [(chartAt ℂ y).left_inv hrs]
  have hderiv := hd.hasFDerivAt.comp_hasDerivAt u hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hqv'
  have hconj := s26n_conj_eq (Q := q y (chartAt ℂ y y)) hv0 (by rw [hqv']; simp) (by rw [hqv']; norm_num)
  have hnv : ‖q y (chartAt ℂ y y)‖ * ‖v‖ ^ 2 = 1 := by
    have h1 := congrArg norm hqv'
    rwa [norm_mul, norm_pow, norm_one] at h1
  have hsv : Real.sqrt ‖q y (chartAt ℂ y y)‖ * ‖v‖ = 1 := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (norm_nonneg _), hnv, Real.sqrt_one]
  have hvinv : ‖v‖ = 1 / Real.sqrt ‖q y (chartAt ℂ y y)‖ := eq_one_div_of_mul_eq_one_right hsv
  have hgz : localMapExprAt f y (chartAt ℂ y y) (chartAt ℂ y y) = chartAt ℂ (f y) (f y) := by
    simp only [localMapExprAt, hzs]
  simp only [s26v_speed, hextu]
  rw [hev.deriv_eq, hderiv.deriv, fderiv_eq_dz_dzbar hd, map_mul, Complex.conj_ofReal, hconj]
  simp only [s26v_lam, lambdaStretch, lambdaStretchPlane, phiDensity, hzs, hgz]
  have hfac : dz (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y) * (((2 * L : ℝ) : ℂ) * v) +
      dzbar (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y) *
        (((2 * L : ℝ) : ℂ) * (v * (q y (chartAt ℂ y y) / ((‖q y (chartAt ℂ y y)‖ : ℝ) : ℂ)))) =
      ((2 * L : ℝ) : ℂ) * v * (dz (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y) +
        dzbar (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y) *
          (q y (chartAt ℂ y y) / ((‖q y (chartAt ℂ y y)‖ : ℝ) : ℂ))) := by
    ring
  rw [hfac, ← ofReal_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < 2 * L), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L)]
  congr 1
  rw [hvinv]
  ring

/-- **Local absolute continuity of `f` along a trajectory at a good height**: in a box `(B, Z, G)` at `y₀` whose
height through `c T₀` is good for `G` ([V8]), `v ↦ φ_x(f(c(-L + 2Lv)))` is absolutely continuous near
`v₀ = (T₀ + L)/(2L)` (the line in `Z`, the affine change of variable `s26v_b_ac_affine`, and the holomorphic
transition from the chart at `f y₀` to the chart at `x`, Lipschitz on a closed ball). -/
theorem s26v_b_local_ac [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (f : S₀ ≃ₜ S₀) {y₀ : S₀} {B : Set S₀}
    {Z : S₀ → ℂ} {G : ℂ → ℂ} (hBf : B ⊆ f ⁻¹' (chartAt ℂ (f y₀)).source) (hB : s26v_IsFlowBox q B Z)
    (hG : ∀ y ∈ B, G (Z y) = chartAt ℂ (f y₀) (f y)) {c : C(ℝ, S₀)} (hc : s26v_IsTraj q c) {L : ℝ}
    (hL : 0 < L) {T₀ : ℝ} (hT₀ : c T₀ ∈ B)
    (hgood : ∀ a b : ℝ, a < b → (∀ ξ ∈ Icc a b, (ξ : ℂ) + ((Z (c T₀)).im : ℂ) * I ∈ Z '' B) →
      AbsolutelyContinuousOnInterval (fun ξ : ℝ => G ((ξ : ℂ) + ((Z (c T₀)).im : ℂ) * I)) a b)
    (x : S₀) (hx : f (c T₀) ∈ (chartAt ℂ x).source) :
    ∃ r > 0, AbsolutelyContinuousOnInterval (fun v => chartAt ℂ x (f (c (-L + 2 * L * v))))
      ((T₀ + L) / (2 * L) - r) ((T₀ + L) / (2 * L) + r) := by
  obtain ⟨δ₁, hδ₁, σ, hσ, hline⟩ := s26v_b_line_near hB hc hT₀
  have hfy₀ : f (c T₀) ∈ (chartAt ℂ (f y₀)).source := hBf hT₀
  have hOo : IsOpen (chartAt ℂ (f y₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ (f y₀)).source)) :=
    ((chartAt ℂ (f y₀)).isOpen_image_iff_of_subset_source inter_subset_right).2
      ((chartAt ℂ x).open_source.inter (chartAt ℂ (f y₀)).open_source)
  have hw₀O : chartAt ℂ (f y₀) (f (c T₀)) ∈
      chartAt ℂ (f y₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ (f y₀)).source) := ⟨f (c T₀), ⟨hx, hfy₀⟩, rfl⟩
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hOo _ hw₀O
  have hcb : closedBall (chartAt ℂ (f y₀) (f (c T₀))) (ρ / 2) ⊆
      chartAt ℂ (f y₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ (f y₀)).source) :=
    (closedBall_subset_ball (by linarith)).trans hρO
  have hτd : DifferentiableOn ℂ (chartTransition x (f y₀))
      (chartAt ℂ (f y₀) '' ((chartAt ℂ x).source ∩ (chartAt ℂ (f y₀)).source)) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpt := (chartAt ℂ (f y₀)).map_source hp.2
    exact (s23_transition x (f y₀) hpt (by rw [(chartAt ℂ (f y₀)).left_inv hp.2]; exact hp.1)).1.differentiableWithinAt
  have hτc : ContDiffOn ℂ 1 (chartTransition x (f y₀)) (closedBall (chartAt ℂ (f y₀) (f (c T₀))) (ρ / 2)) :=
    (hτd.contDiffOn hOo).mono hcb
  obtain ⟨Kτ, hKτ⟩ := (hτc.restrict_scalars ℝ).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  have hcont : ContinuousAt (fun T => chartAt ℂ (f y₀) (f (c T))) T₀ :=
    ContinuousAt.comp (g := chartAt ℂ (f y₀)) (f := fun T => f (c T)) ((chartAt ℂ (f y₀)).continuousAt hfy₀)
      (f.continuous.comp c.continuous).continuousAt
  have hev : ∀ᶠ T in 𝓝 T₀, f (c T) ∈ (chartAt ℂ x).source ∧
      chartAt ℂ (f y₀) (f (c T)) ∈ closedBall (chartAt ℂ (f y₀) (f (c T₀))) (ρ / 2) := by
    filter_upwards [(f.continuous.comp c.continuous).continuousAt.preimage_mem_nhds
      ((chartAt ℂ x).open_source.mem_nhds hx),
      hcont.preimage_mem_nhds (closedBall_mem_nhds _ (by linarith : (0 : ℝ) < ρ / 2))] with T h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set δ := min δ₁ δ₂ with hδ
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  set r := δ / (4 * L) with hr
  have hrpos : 0 < r := by positivity
  have h2Lr : 2 * L * r = δ / 2 := by
    rw [hr]
    field_simp
    ring
  refine ⟨r, hrpos, ?_⟩
  set v₀ := (T₀ + L) / (2 * L) with hv₀
  have hTv : ∀ v : ℝ, -L + 2 * L * v - T₀ = 2 * L * (v - v₀) := by
    intro v
    rw [hv₀]
    field_simp
    ring
  have hwin : ∀ v ∈ uIcc (v₀ - r) (v₀ + r),
      -L + 2 * L * v ∈ ball T₀ δ₁ ∧ -L + 2 * L * v ∈ ball T₀ δ₂ := by
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    have h1 : |(-L + 2 * L * v) - T₀| ≤ δ / 2 := by
      rw [hTv, abs_le]
      constructor <;> nlinarith [hv.1, hv.2]
    have h2 : δ / 2 < δ := by linarith
    constructor
    · rw [mem_ball, Real.dist_eq]
      linarith [min_le_left δ₁ δ₂]
    · rw [mem_ball, Real.dist_eq]
      linarith [min_le_right δ₁ δ₂]
  set a₀ := (Z (c T₀)).re with ha₀
  set η₀ := (Z (c T₀)).im with hη₀
  have hZ0 : Z (c T₀) = (a₀ : ℂ) + (η₀ : ℂ) * I := (Complex.re_add_im _).symm
  have hσσ : (σ : ℂ) * σ = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hsegAC : AbsolutelyContinuousOnInterval (fun ξ : ℝ => G ((ξ : ℂ) + (η₀ : ℂ) * I))
      (a₀ - δ / 2) (a₀ + δ / 2) := by
    refine hgood _ _ (by linarith) fun ξ hξ => ?_
    have hT : T₀ + σ * (ξ - a₀) ∈ ball T₀ δ₁ := by
      rw [mem_ball, Real.dist_eq]
      have h1 : |σ * (ξ - a₀)| ≤ δ / 2 := by
        rw [abs_mul, hσabs, one_mul, abs_le]
        constructor <;> linarith [hξ.1, hξ.2]
      have h2 : δ ≤ δ₁ := min_le_left _ _
      calc |T₀ + σ * (ξ - a₀) - T₀| = |σ * (ξ - a₀)| := by ring_nf
        _ < δ₁ := by linarith
    obtain ⟨hTB, hTZ⟩ := hline _ hT
    refine ⟨c (T₀ + σ * (ξ - a₀)), hTB, ?_⟩
    rw [hTZ, hZ0]
    push_cast
    linear_combination ((ξ : ℂ) - (a₀ : ℂ)) * hσσ
  have hβ : 2 * L * σ ≠ 0 := by
    rcases hσ with rfl | rfl
    · simp [hL.ne']
    · simp [hL.ne']
  set α := a₀ + σ * (-L - T₀) with hα
  have haff : ∀ v : ℝ, α + 2 * L * σ * v = a₀ + σ * (-L + 2 * L * v - T₀) := by
    intro v
    rw [hα]
    ring
  have hAC1 : AbsolutelyContinuousOnInterval
      (fun v => G (((α + 2 * L * σ * v : ℝ) : ℂ) + (η₀ : ℂ) * I)) (v₀ - r) (v₀ + r) := by
    refine s26v_b_ac_affine (h := fun ξ : ℝ => G ((ξ : ℂ) + (η₀ : ℂ) * I)) hβ (hsegAC.mono ?_)
    have hend : ∀ v ∈ uIcc (v₀ - r) (v₀ + r),
        α + 2 * L * σ * v ∈ uIcc (a₀ - δ / 2) (a₀ + δ / 2) := by
      intro v hv
      rw [uIcc_of_le (by linarith), mem_Icc, haff]
      have h1 : |σ * (-L + 2 * L * v - T₀)| ≤ δ / 2 := by
        rw [abs_mul, hσabs, one_mul, hTv]
        rw [uIcc_of_le (by linarith)] at hv
        rw [abs_le]
        constructor <;> nlinarith [hv.1, hv.2]
      rw [abs_le] at h1
      constructor <;> linarith [h1.1, h1.2]
    exact uIcc_subset_uIcc (hend _ left_mem_uIcc) (hend _ right_mem_uIcc)
  have hAC2 : AbsolutelyContinuousOnInterval (fun v => chartAt ℂ (f y₀) (f (c (-L + 2 * L * v))))
      (v₀ - r) (v₀ + r) := by
    refine hAC1.congr fun v hv => ?_
    obtain ⟨hTB, hTZ⟩ := hline _ (hwin v hv).1
    show G _ = _
    rw [← hG _ hTB, hTZ, haff, hZ0]
    congr 1
    push_cast
    ring
  have hmaps : MapsTo (fun v => chartAt ℂ (f y₀) (f (c (-L + 2 * L * v)))) (uIcc (v₀ - r) (v₀ + r))
      (closedBall (chartAt ℂ (f y₀) (f (c T₀))) (ρ / 2)) := fun v hv => (hball₂ _ (hwin v hv).2).2
  have hAC3 := hKτ.comp_absolutelyContinuousOnInterval hmaps hAC2
  refine hAC3.congr fun v hv => ?_
  obtain ⟨hTB, -⟩ := hline _ (hwin v hv).1
  have hfy : f (c (-L + 2 * L * v)) ∈ (chartAt ℂ (f y₀)).source := hBf hTB
  simp only [Function.comp_apply, chartTransition, (chartAt ℂ (f y₀)).left_inv hfy]

/-- **[V9b, stub]** (T4, almost every arc).  For almost every `p`, `f(α_p)` is a good path whose `q`-speed integrates
to `∫_{-L}^{L} λ_f(c_p(t)) dt`.  (Avoiding zeros: off the ranges of the trajectories through the countable set
`f⁻¹(zeros)` ([V2d]).  Absolute continuity: in countably many flow boxes, `f` in natural parameters is
quasiconformal, hence absolutely continuous along almost every horizontal line ([V8]); by [V9c] almost every
trajectory crosses the boxes only along good lines.  Speed: where `f` is differentiable at `c_p(t)` ([V8], [V9c]), the
`q`-speed of `f ∘ c_p` is `λ_f(c_p(t))` (the computation of `s26n_pointwise` with `q v² = 1`); the substitution
`t = -L + 2Lu`.) -/
theorem s26v_arc_good_ae [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) {L : ℝ} (hL : 0 < L) :
    ∃ N : Set S₀, (∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0) ∧
      ∀ p, p ∉ N → s26v_IsGoodPath q ((s26v_arc (s26v_traj q p) L).map f.continuous) ∧
        ∫⁻ u in Ioo (0 : ℝ) 1, s26v_speed q ((s26v_arc (s26v_traj q p) L).map f.continuous) u =
          ∫⁻ t in Ioo (-L) L, s26v_lam q f (s26v_traj q p t) := by
  classical
  obtain ⟨K, hfK⟩ := hf
  have hsc : SecondCountableTopology S₀ := ChartedSpace.secondCountable_of_sigmaCompact ℂ S₀
  have hbox : ∀ y₀ : S₀, ∃ (B : Set S₀) (Z : S₀ → ℂ) (ψ G : ℂ → ℂ), q y₀ (chartAt ℂ y₀ y₀) ≠ 0 →
      y₀ ∈ B ∧ B ⊆ (chartAt ℂ y₀).source ∧ B ⊆ f ⁻¹' (chartAt ℂ (f y₀)).source ∧ s26v_IsFlowBox q B Z ∧
      DifferentiableOn ℂ ψ (Z '' B) ∧ (∀ y ∈ B, ψ (Z y) = chartAt ℂ y₀ y) ∧ IsKQC G (Z '' B) K ∧
      ∀ y ∈ B, G (Z y) = chartAt ℂ (f y₀) (f y) := by
    intro y₀
    by_cases h : q y₀ (chartAt ℂ y₀ y₀) ≠ 0
    · obtain ⟨B, Z, ψ, G, hB⟩ := s26v_b_box hq f hfK h
      exact ⟨B, Z, ψ, G, fun _ => hB⟩
    · exact ⟨∅, 0, 0, 0, fun h' => absurd h' h⟩
  choose B Z ψ G hBZ using hbox
  have hBo : ∀ i : {y₀ : S₀ // q y₀ (chartAt ℂ y₀ y₀) ≠ 0}, IsOpen (B i) := fun i =>
    (hBZ i i.2).2.2.2.1.1
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {y₀ : S₀ // q y₀ (chartAt ℂ y₀ y₀) ≠ 0} => B i) hBo
  have hcovB : ∀ y, q y (chartAt ℂ y y) ≠ 0 → ∃ i ∈ T, y ∈ B (i : S₀) := by
    intro y hy
    have h1 : y ∈ ⋃ i : {y₀ : S₀ // q y₀ (chartAt ℂ y₀ y₀) ≠ 0}, B i :=
      mem_iUnion.2 ⟨⟨y, hy⟩, (hBZ y hy).1⟩
    rw [← hTU] at h1
    obtain ⟨i, hi⟩ := mem_iUnion.1 h1
    obtain ⟨hiT, hyi⟩ := mem_iUnion.1 hi
    exact ⟨i, hiT, hyi⟩
  have hH : ∀ y₀ : S₀, ∃ H : Set ℝ, volume H = 0 ∧ (q y₀ (chartAt ℂ y₀ y₀) ≠ 0 → ∀ η, η ∉ H →
      ∀ a b : ℝ, a < b → (∀ ξ ∈ Icc a b, (ξ : ℂ) + (η : ℂ) * I ∈ Z y₀ '' B y₀) →
        AbsolutelyContinuousOnInterval (fun ξ : ℝ => G y₀ ((ξ : ℂ) + (η : ℂ) * I)) a b) := by
    intro y₀
    by_cases h : q y₀ (chartAt ℂ y₀ y₀) ≠ 0
    · have hV8 := s26v_isKQC_ae_line (hBZ y₀ h).2.2.2.2.2.2.1
      refine ⟨{η | ¬ ((∀ a b : ℝ, a < b → (∀ ξ ∈ Icc a b, (ξ : ℂ) + (η : ℂ) * I ∈ Z y₀ '' B y₀) →
          AbsolutelyContinuousOnInterval (fun ξ : ℝ => G y₀ ((ξ : ℂ) + (η : ℂ) * I)) a b) ∧
          ∀ᵐ ξ : ℝ, (ξ : ℂ) + (η : ℂ) * I ∈ Z y₀ '' B y₀ →
            DifferentiableAt ℝ (G y₀) ((ξ : ℂ) + (η : ℂ) * I))}, ae_iff.1 hV8, fun _ η hη => ?_⟩
      exact (not_not.1 hη).1
    · exact ⟨∅, measure_empty, fun h' => absurd h' h⟩
  choose H hH0 hHgood using hH
  set Nh : Set S₀ := ⋃ i ∈ T, {y | y ∈ B (i : S₀) ∧ (Z (i : S₀) y).im ∈ H (i : S₀)} with hNh
  set Nf : Set S₀ := {y | ¬ DifferentiableAt ℝ (localMapExprAt f y (chartAt ℂ y y)) (chartAt ℂ y y)} with hNf
  have hNnull : ∀ x, volume (chartAt ℂ x '' ((Nh ∪ Nf) ∩ (chartAt ℂ x).source)) = 0 := by
    intro x
    rw [union_inter_distrib_right, image_union]
    refine measure_union_null ?_ (s26v_b_nondiff_null f hfK x)
    have h1 : chartAt ℂ x '' (Nh ∩ (chartAt ℂ x).source) ⊆ ⋃ i ∈ T,
        chartAt ℂ x '' ({y | y ∈ B (i : S₀) ∧ (Z (i : S₀) y).im ∈ H (i : S₀)} ∩ (chartAt ℂ x).source) := by
      rintro _ ⟨y, ⟨hy, hyx⟩, rfl⟩
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion₂.2 ⟨i, hi, y, ⟨hyi, hyx⟩, rfl⟩
    refine measure_mono_null h1 ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
    obtain ⟨-, hBs, -, hB, hψ, hψZ, -⟩ := hBZ i i.2
    exact s26v_b_height_null hB.2.2.2.1 hBs hψ hψZ (hH0 i) x
  obtain ⟨N', hN'null, hN'⟩ := s26v_ae_traj_null hq hne (Nh ∪ Nf) hNnull hL
  set Zf : Set S₀ := f ⁻¹' {z | q z (chartAt ℂ z z) = 0} with hZf
  have hZfc : Zf.Countable := (s26v_b_zeros_countable hq hne).preimage f.injective
  set Nz : Set S₀ := ⋃ y ∈ Zf, range (s26v_traj q y) with hNz
  have hNznull : ∀ x, volume (chartAt ℂ x '' (Nz ∩ (chartAt ℂ x).source)) = 0 := by
    intro x
    have h1 : chartAt ℂ x '' (Nz ∩ (chartAt ℂ x).source) ⊆
        ⋃ y ∈ Zf, chartAt ℂ x '' (range (s26v_traj q y) ∩ (chartAt ℂ x).source) := by
      rintro _ ⟨p, ⟨hp, hpx⟩, rfl⟩
      obtain ⟨y, hy, hpy⟩ := mem_iUnion₂.1 hp
      exact mem_iUnion₂.2 ⟨y, hy, p, ⟨hpy, hpx⟩, rfl⟩
    refine measure_mono_null h1 ((measure_biUnion_null_iff hZfc).2 fun y _ => ?_)
    by_cases hyE : y ∈ s26v_E q
    · have hconst : ∀ t, s26v_traj q y t = y := by
        intro t
        have hne' : ¬ ∃ c : C(ℝ, S₀), s26v_IsTraj q c ∧ c 0 = y := hyE
        unfold s26v_traj
        rw [dite_eq_right hne']
        rfl
      refine measure_mono_null ?_ (measure_singleton (chartAt ℂ x y))
      rintro _ ⟨p, ⟨⟨t, rfl⟩, -⟩, rfl⟩
      rw [hconst t]
      rfl
    · exact s26v_traj_range_null hq (s26v_traj_spec hyE).1 x
  refine ⟨s26v_E q ∪ N' ∪ Nz, fun x => ?_, fun p hp => ?_⟩
  · rw [union_inter_distrib_right, union_inter_distrib_right, image_union, image_union]
    exact measure_union_null (measure_union_null (s26v_E_null hq hne x) (hN'null x)) (hNznull x)
  have hpE : p ∉ s26v_E q := fun h => hp (Or.inl (Or.inl h))
  have hpN' : p ∉ N' := fun h => hp (Or.inl (Or.inr h))
  have hpNz : p ∉ Nz := fun h => hp (Or.inr h)
  obtain ⟨hcT, hc0⟩ := s26v_traj_spec hpE
  have hvol := hN' p hpN'
  set c := s26v_traj q p with hc
  have hext : ∀ v ∈ Icc (0 : ℝ) 1, ((s26v_arc c L).map f.continuous).extend v = f (c (-L + 2 * L * v)) :=
    fun v hv => by
      rw [Path.extend_apply _ hv]
      rfl
  have hreg : ∀ t : ℝ, q (f (c t)) (chartAt ℂ (f (c t)) (f (c t))) ≠ 0 := by
    intro t h
    apply hpNz
    refine mem_iUnion₂.2 ⟨c t, h, ?_⟩
    have h1 := s26v_b_mem_range_traj hq hcT t
    rwa [hc0] at h1
  have hgood : ∀ T₀ ∈ Icc (-L) L, ∀ i ∈ T, c T₀ ∈ B (i : S₀) → (Z (i : S₀) (c T₀)).im ∉ H (i : S₀) := by
    intro T₀ hT₀ i hi hcB hbad
    obtain ⟨δ, hδ, σ, -, hline⟩ := s26v_b_line_near (hBZ i i.2).2.2.2.1 hcT hcB
    have hsub : Ioo (max (-L) (T₀ - δ)) (min L (T₀ + δ)) ⊆ {t | t ∈ Ioo (-L) L ∧ c t ∈ Nh ∪ Nf} := by
      intro t ht
      have ht1 : -L < t := lt_of_le_of_lt (le_max_left _ _) ht.1
      have ht2 : t < L := lt_of_lt_of_le ht.2 (min_le_left _ _)
      have ht4 : T₀ - δ < t := lt_of_le_of_lt (le_max_right _ _) ht.1
      have ht5 : t < T₀ + δ := lt_of_lt_of_le ht.2 (min_le_right _ _)
      have ht3 : t ∈ ball T₀ δ := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      obtain ⟨htB, htZ⟩ := hline t ht3
      refine ⟨⟨ht1, ht2⟩, Or.inl (mem_iUnion₂.2 ⟨i, hi, htB, ?_⟩)⟩
      show (Z (i : S₀) (c t)).im ∈ H (i : S₀)
      rw [htZ]
      simpa using hbad
    have hpos : 0 < volume (Ioo (max (-L) (T₀ - δ)) (min L (T₀ + δ))) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos]
      exact max_lt (lt_min (by linarith) (by linarith [hT₀.1])) (lt_min (by linarith [hT₀.2]) (by linarith))
    exact absurd (measure_mono_null hsub hvol) hpos.ne'
  refine ⟨⟨fun s hs => ?_, fun x s t hs hst ht hsrc => ?_⟩, ?_⟩
  · rw [hext s hs]
    exact hreg _
  · have hloc : ∀ v ∈ Icc s t, ∃ r > 0, ∀ a b, v - r ≤ a → b ≤ v + r → a ≤ b →
        AbsolutelyContinuousOnInterval (fun v => chartAt ℂ x (f (c (-L + 2 * L * v)))) a b := by
      intro v₀ hv₀
      have hv₀01 : v₀ ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hv₀.1, hv₀.2.trans ht⟩
      have hT₀ : -L + 2 * L * v₀ ∈ Icc (-L) L := ⟨by nlinarith [hv₀01.1], by nlinarith [hv₀01.2]⟩
      have hregc : q (c (-L + 2 * L * v₀)) (chartAt ℂ (c (-L + 2 * L * v₀)) (c (-L + 2 * L * v₀))) ≠ 0 := by
        obtain ⟨-, w, -, hqw⟩ := hcT (-L + 2 * L * v₀)
        intro h
        rw [h, zero_mul] at hqw
        exact zero_ne_one hqw
      obtain ⟨i, hiT, hci⟩ := hcovB _ hregc
      obtain ⟨-, -, hBf, hB, -, -, -, hGZ⟩ := hBZ i i.2
      have hx : f (c (-L + 2 * L * v₀)) ∈ (chartAt ℂ x).source := by
        have h1 := hsrc ⟨v₀, hv₀, rfl⟩
        rwa [hext v₀ hv₀01] at h1
      obtain ⟨r, hr, hac⟩ := s26v_b_local_ac f hBf hB hGZ hcT hL hci
        (hHgood i i.2 _ (hgood _ hT₀ i hiT hci)) x hx
      have hv₀eq : (-L + 2 * L * v₀ + L) / (2 * L) = v₀ := by
        field_simp
        ring
      rw [hv₀eq] at hac
      refine ⟨r, hr, fun a b ha hb hab => hac.mono ?_⟩
      rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc ha hb
    refine (s26v_b_ac_of_local hst.le hloc).congr fun v hv => ?_
    rw [uIcc_of_le hst.le] at hv
    show chartAt ℂ x (f (c (-L + 2 * L * v))) = chartAt ℂ x (((s26v_arc c L).map f.continuous).extend v)
    rw [hext v ⟨hs.trans hv.1, hv.2.trans ht⟩]
  · have hae : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), s26v_speed q ((s26v_arc c L).map f.continuous) u =
        ENNReal.ofReal (2 * L) * s26v_lam q f (c (-L + 2 * L * u)) := by
      have hnull : volume {u : ℝ | u ∈ Ioo (0 : ℝ) 1 ∧ c (-L + 2 * L * u) ∈ Nf} = 0 := by
        have hsub : {u : ℝ | u ∈ Ioo (0 : ℝ) 1 ∧ c (-L + 2 * L * u) ∈ Nf} ⊆
            (fun u => 2 * L * u) ⁻¹' ((fun t => -L + t) ⁻¹' {t | t ∈ Ioo (-L) L ∧ c t ∈ Nh ∪ Nf}) := by
          intro u hu
          simp only [mem_preimage, mem_ofPred_eq]
          exact ⟨⟨by nlinarith [hu.1.1], by nlinarith [hu.1.2]⟩, Or.inr hu.2⟩
        refine measure_mono_null hsub ?_
        rw [Real.volume_preimage_mul_left (by positivity), measure_preimage_add, hvol, mul_zero]
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun u hu hu01 => ?_
      have hd : c (-L + 2 * L * u) ∉ Nf := fun h => hu ⟨hu01, h⟩
      simp only [hNf, mem_ofPred_eq, not_not] at hd
      exact s26v_b_speed_eq hq f hcT hL hu01 hd
    rw [lintegral_congr_ae hae]
    have himg : (fun u : ℝ => -L + 2 * L * u) '' Ioo (0 : ℝ) 1 = Ioo (-L) L := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
      · intro ht
        refine ⟨(t + L) / (2 * L), ⟨?_, ?_⟩, ?_⟩
        · exact div_pos (by linarith [ht.1]) (by positivity)
        · rw [div_lt_one (by positivity)]
          linarith [ht.2]
        · field_simp
          ring
    have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioo (0 : ℝ) 1)
      (f := fun u : ℝ => -L + 2 * L * u) (f' := fun _ => 2 * L) measurableSet_Ioo
      (fun u _ => by
        have h := ((hasDerivAt_id u).const_mul (2 * L)).const_add (-L)
        simp only [id, mul_one] at h
        exact h.hasDerivWithinAt)
      (fun u _ w _ huw => by
        have h2 : 2 * L * u = 2 * L * w := by
          simp only at huw
          linarith
        exact mul_left_cancel₀ (by positivity) h2)
      (fun t => s26v_lam q f (c t))
    rw [himg] at hcv
    rw [hcv]
    refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * L)]

/-- **T4, proved:** for almost every `p`, `l_q(f(α_p)) = ∫_{-L}^{L} λ_f(c_p(t)) dt` ([V9a] and [V9b]). -/
theorem s26v_length_ae [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) {L : ℝ} (hL : 0 < L) :
    ∃ N : Set S₀, (∀ x : S₀, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0) ∧
      ∀ p, p ∉ N → phiLengthPathInv q ((s26v_arc (s26v_traj q p) L).map f.continuous) =
        ∫⁻ t in Ioo (-L) L, s26v_lam q f (s26v_traj q p t) := by
  obtain ⟨N, hN, h⟩ := s26v_arc_good_ae hq hne f hf hL
  exact ⟨N, hN, fun p hp => by rw [s26v_phiLengthPathInv_eq hq (h p hp).1, (h p hp).2]⟩

/-! #### Proved glue: surface integrals off null sets -/

/-- Monotonicity of `surfaceIntegral` off a set `N` that is null in every chart. -/
theorem s26v_surfaceIntegral_mono_off {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (q : S → ℂ → ℂ) {u w : S → ℂ → ℝ≥0∞} (N : Set S)
    (hN : ∀ x : S, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0)
    (huw : ∀ x : S, ∀ p ∈ (chartAt ℂ x).source, p ∉ N → u x (chartAt ℂ x p) ≤ w x (chartAt ℂ x p)) :
    surfaceIntegral q u ≤ surfaceIntegral q w := by
  unfold surfaceIntegral
  refine iInf_mono fun x => iInf_mono fun P => iInf_mono fun hP => ENNReal.tsum_le_tsum fun i => ?_
  refine lintegral_mono_ae ?_
  have h1 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), z ∈ chartAt ℂ (x i) '' P i :=
    ae_restrict_mem (hP.1 i).2
  have h2 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
      z ∉ chartAt ℂ (x i) '' (N ∩ (chartAt ℂ (x i)).source) :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (hN (x i)))
  filter_upwards [h1, h2] with z hz1 hz2
  obtain ⟨p, hpP, rfl⟩ := hz1
  have hps : p ∈ (chartAt ℂ (x i)).source := (hP.1 i).1 hpP
  have hpN : p ∉ N := fun h => hz2 ⟨p, ⟨h, hps⟩, rfl⟩
  exact mul_le_mul_left (huw (x i) p hps hpN) _

/-- `surfaceIntegral` is unchanged by a change of the integrand off a set that is null in every chart. -/
theorem s26v_surfaceIntegral_congr_off {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (q : S → ℂ → ℂ) {u w : S → ℂ → ℝ≥0∞} (N : Set S)
    (hN : ∀ x : S, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0)
    (huw : ∀ x : S, ∀ p ∈ (chartAt ℂ x).source, p ∉ N → u x (chartAt ℂ x p) = w x (chartAt ℂ x p)) :
    surfaceIntegral q u = surfaceIntegral q w :=
  le_antisymm (s26v_surfaceIntegral_mono_off q N hN fun x p hp hpN => (huw x p hp hpN).le)
    (s26v_surfaceIntegral_mono_off q N hN fun x p hp hpN => (huw x p hp hpN).ge)

/-! #### Proved assembly -/

/-- **The arc clause, proved:** off the critical set, the arc `α_p` is a horizontal arc through `p` of `q`-length
`2L` ([V7]). -/
theorem s26v_arc_clause [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) {L : ℝ} (hL : 0 < L)
    {p : S₀} (hp : p ∉ s26v_E q) :
    IsHorizontalArcRS q (s26v_arc (s26v_traj q p) L) ∧ p ∈ range (s26v_arc (s26v_traj q p) L) ∧
      phiLengthPath q (s26v_arc (s26v_traj q p) L) = ENNReal.ofReal (2 * L) := by
  obtain ⟨htr, h0⟩ := s26v_traj_spec hp
  obtain ⟨hh, hlen⟩ := s26v_arc_props hq htr hL
  refine ⟨hh, ?_, hlen⟩
  have hmem := s26v_mem_range_arc (s26v_traj q p) L
  rwa [h0] at hmem

/-- **The averaging identity, proved:** `∬ l_q(f(α_p)) dA_q = ∬ (∫_{-L}^{L} λ_f(c_p(t)) dt) dA_q = 2L ∬ λ_f dA_q` (T4
off a null set, then T3 for `U = λ_f`, then the chart independence of `λ_f`). -/
theorem s26v_averaging_identity [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) {L : ℝ} (hL : 0 < L) :
    surfaceIntegral q (fun x z => phiLengthPathInv q
        ((s26v_arc (s26v_traj q ((chartAt ℂ x).symm z)) L).map f.continuous)) =
      ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z)) := by
  obtain ⟨N, hN, hlen⟩ := s26v_length_ae hq hne f hf hL
  have h1 : surfaceIntegral q (fun x z => phiLengthPathInv q
        ((s26v_arc (s26v_traj q ((chartAt ℂ x).symm z)) L).map f.continuous)) =
      surfaceIntegral q (fun x z => ∫⁻ t in Ioo (-L) L,
        s26v_lam q f (s26v_traj q ((chartAt ℂ x).symm z) t)) := by
    refine s26v_surfaceIntegral_congr_off q N hN fun x p hp hpN => ?_
    show phiLengthPathInv q ((s26v_arc (s26v_traj q ((chartAt ℂ x).symm (chartAt ℂ x p))) L).map f.continuous) =
      ∫⁻ t in Ioo (-L) L, s26v_lam q f (s26v_traj q ((chartAt ℂ x).symm (chartAt ℂ x p)) t)
    rw [(chartAt ℂ x).left_inv hp]
    exact hlen p hpN
  have h2 : surfaceIntegral q (fun x z => s26v_lam q f ((chartAt ℂ x).symm z)) =
      surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z)) := by
    refine s26v_surfaceIntegral_congr_off q ∅ (fun x => by simp) fun x p hp _ => ?_
    show s26v_lam q f ((chartAt ℂ x).symm (chartAt ℂ x p)) =
      ENNReal.ofReal (lambdaStretch q q f x (chartAt ℂ x p))
    rw [(chartAt ℂ x).left_inv hp, s26v_lambdaStretch_chart hq f x hp]
    rfl
  rw [h1, s26v_flow_average hq hne (s26v_lam q f) (s26v_lam_borel hq f) hL, h2]

/-- §26.4 (the proof of Lemma 26.2): for `L > 0` and a regular point `p` from which the horizontal
trajectory can be followed a length `L` in both directions without meeting a critical point, let
`α(p, L)` be the arc so obtained (of `q`-length `2L`); the exceptional set `E` is null (in every chart),
and `∬ l_q(f(α_p)) dA_q = 2L ∬ λ_f dA_q`.

**Correction.**  The statement was **vacuous**: each `α_p` could be a `Loop`, of which nothing was
required, and the averaging identity `∬ l_q(f(α_p)) dA_q = 2L ∬ λ_f dA_q` (the substance of the step) was
missing.  Now `α` is total, the arc clause is required off `E`, and the identity is stated, with
* the true length `phiLengthPathInv` of `f(α_p)` on the left (`phiLengthPath` is `⊤` for the generally
  non-Lipschitz, merely absolutely continuous, paths `f ∘ α_p`, which would make the identity false);
* `E` null in every chart as an outer-measure condition (the `surfaceIntegral` of the indicator is a
  lower integral, so a non-measurable `E` of inner measure `0` would have passed as null). -/
theorem lemma26_2_averaging [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ (E : Set S₀) (α : S₀ → Σ a b : S₀, Path a b),
      (∀ x : S₀, volume (chartAt ℂ x '' (E ∩ (chartAt ℂ x).source)) = 0) ∧
      (∀ p, p ∉ E → IsHorizontalArcRS q (α p).2.2 ∧ p ∈ range (α p).2.2 ∧
        phiLengthPath q (α p).2.2 = ENNReal.ofReal (2 * L)) ∧
      surfaceIntegral q (fun x z => phiLengthPathInv q ((α ((chartAt ℂ x).symm z)).2.2.map f.continuous)) =
        ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z)) := by
  have _ := hg
  have : CompactSpace S₀ := hS.1
  exact ⟨s26v_E q, fun p => ⟨s26v_traj q p (-L), s26v_traj q p L, s26v_arc (s26v_traj q p) L⟩,
    s26v_E_null hq hne, fun p hp => s26v_arc_clause hq hL hp, s26v_averaging_identity hq hne f hf hL⟩

/-! ### Stage 0 (coordinator 553e2d): the pointwise inequality (26.12)–(26.13) -/

/-- The square of the plane stretching function:
`λ² = |φ'(g z)| · |∂g + ∂̄g · φ/|φ||² / |φ(z)|`. -/
theorem z26_lambdaStretchPlane_sq (φ φ' g : ℂ → ℂ) (z : ℂ) :
    lambdaStretchPlane φ φ' g z ^ 2 =
      ‖φ' (g z)‖ * ‖dz g z + dzbar g z * (φ z / ‖φ z‖)‖ ^ 2 / ‖φ z‖ := by
  unfold lambdaStretchPlane
  rw [div_pow, mul_pow, Real.sq_sqrt (norm_nonneg _), Real.sq_sqrt (norm_nonneg _)]

/-- Where `|∂̄g| < |∂g|`, the dilatation quotient times the Jacobian is `(|∂g| + |∂̄g|)²`. -/
theorem z26_dilatationQuotient_mul_jacobian (g : ℂ → ℂ) (z : ℂ)
    (hz : ‖dzbar g z‖ < ‖dz g z‖) :
    dilatationQuotient g z * jacobian g z = (‖dz g z‖ + ‖dzbar g z‖) ^ 2 := by
  have hb0 : 0 ≤ ‖dzbar g z‖ := norm_nonneg _
  have ha : 0 < ‖dz g z‖ := lt_of_le_of_lt hb0 hz
  have hsub : 0 < ‖dz g z‖ - ‖dzbar g z‖ := sub_pos.mpr hz
  unfold dilatationQuotient jacobian complexDilatation
  rw [norm_div]
  have h1 : 1 + ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ + ‖dzbar g z‖) / ‖dz g z‖ := by
    field_simp
  have h2 : 1 - ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ - ‖dzbar g z‖) / ‖dz g z‖ := by
    field_simp
  rw [h1, h2, div_div_div_cancel_right₀ ha.ne']
  field_simp
  ring

/-- For `|u| = 1` and `a ≠ 0`: `|a + b u| = |a| + |b|` iff `b u` is a non-negative real multiple
of `a`. -/
theorem z26_norm_add_eq_iff (a b u : ℂ) (hu : ‖u‖ = 1) (ha : a ≠ 0) :
    ‖a + b * u‖ = ‖a‖ + ‖b‖ ↔ ∃ r : ℝ, 0 ≤ r ∧ b * u = r * a := by
  have hbu : ‖b * u‖ = ‖b‖ := by rw [norm_mul, hu, mul_one]
  rw [← hbu, ← sameRay_iff_norm_add, ← exists_nonneg_left_iff_sameRay ha]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by rw [← h, Complex.real_smul]⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by rw [h, Complex.real_smul]⟩

/-- The triangle inequality `|a + b u| ≤ |a| + |b|` for `|u| = 1`. -/
theorem z26_norm_add_le (a b u : ℂ) (hu : ‖u‖ = 1) : ‖a + b * u‖ ≤ ‖a‖ + ‖b‖ := by
  calc ‖a + b * u‖ ≤ ‖a‖ + ‖b * u‖ := norm_add_le _ _
    _ = ‖a‖ + ‖b‖ := by rw [norm_mul, hu, mul_one]

/-- (26.12)–(26.13) (pointwise): with `f* = f ∘ f₀⁻¹`, `f₀` the Teichmüller map with dilatation
`K₀ = (1+k)/(1-k)`, `λ_{f*} = |∂_ξ f̃|/K₀` and
`λ_{f*}² ≤ K₀⁻² (|∂_ζ f̃| + |∂_ζ̄ f̃|)² ≤ K₀⁻² K[f] J_f`, i.e. `λ_{f*}² ≤ K₀⁻² D_f J_f`.
Here the pointwise inequality `λ² ≤ D_f · J_f` for the stretching function and the Jacobian of `f`
in the metrics of `q` and `q'`, at a point where neither differential vanishes.

**Correction.**  The hypothesis `hq'` was missing, and the equality clause was **false** at zeros of
`q'`: there `λ = J = 0`, so equality holds, while `∂̄f · q/|q|` need not be a non-negative multiple of
`∂f` (identity charts on `ℂ`, `q ≡ 1`, `q' ≡ 0`, `f z = z - z̄/2`).  Restated with the local expression
`localMapExprAt f x z` read in the chart at the image point (see `lambdaStretch`). -/
theorem eq26_13 {f : S₀ → S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} (x : S₀) {z : ℂ}
    (hdiff : DifferentiableAt ℝ (localMapExprAt f x z) z)
    (hz : ‖dzbar (localMapExprAt f x z) z‖ < ‖dz (localMapExprAt f x z) z‖)
    (hq : q x z ≠ 0) (hq' : q' (f ((chartAt ℂ x).symm z)) (localMapExprAt f x z z) ≠ 0) :
    lambdaStretch q q' f x z ^ 2 ≤ dilatationQuotient (localMapExprAt f x z) z * jacobianQD q q' f x z ∧
      (lambdaStretch q q' f x z ^ 2 = dilatationQuotient (localMapExprAt f x z) z * jacobianQD q q' f x z ↔
        (∃ r : ℝ, 0 ≤ r ∧ dzbar (localMapExprAt f x z) z * (q x z / ‖q x z‖) = r * dz (localMapExprAt f x z) z)) := by
  have _ := hdiff
  set g := localMapExprAt f x z with hg
  set a := dz g z with ha_def
  set b := dzbar g z with hb_def
  set u : ℂ := q x z / (‖q x z‖ : ℂ) with hu_def
  have hP : 0 < ‖q x z‖ := norm_pos_iff.mpr hq
  have hQ : 0 < ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ := norm_pos_iff.mpr hq'
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP, div_self hP.ne']
  have ha0 : a ≠ 0 := by
    intro h
    have : ‖a‖ = 0 := by rw [h, norm_zero]
    have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
    linarith
  have hL : lambdaStretch q q' f x z ^ 2 = ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ * ‖a + b * u‖ ^ 2 / ‖q x z‖ := by
    unfold lambdaStretch
    exact z26_lambdaStretchPlane_sq _ _ _ _
  have hR : dilatationQuotient g z * jacobianQD q q' f x z =
      ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ * (‖a‖ + ‖b‖) ^ 2 / ‖q x z‖ := by
    unfold jacobianQD
    rw [← hg, mul_div_assoc', mul_left_comm, z26_dilatationQuotient_mul_jacobian g z hz]
  rw [hL, hR]
  have hN0 : 0 ≤ ‖a + b * u‖ := norm_nonneg _
  have hle : ‖a + b * u‖ ≤ ‖a‖ + ‖b‖ := z26_norm_add_le a b u hu
  have hc : 0 < ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ / ‖q x z‖ := div_pos hQ hP
  have e1 : ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ * ‖a + b * u‖ ^ 2 / ‖q x z‖ =
      ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ / ‖q x z‖ * ‖a + b * u‖ ^ 2 := by ring
  have e2 : ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ * (‖a‖ + ‖b‖) ^ 2 / ‖q x z‖ =
      ‖q' (f ((chartAt ℂ x).symm z)) (g z)‖ / ‖q x z‖ * (‖a‖ + ‖b‖) ^ 2 := by ring
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN0 hle 2) hc.le
  · rw [mul_right_inj' hc.ne', ← z26_norm_add_eq_iff a b u hu ha0]
    exact sq_eq_sq₀ hN0 (by positivity)

/-! ### Helpers for `eq26_14` (`s26w_`): (26.14), norms under Teichmüller maps -/

/-- The new parameter `teichStretch k` is the real-linear map `ζ ↦ (ζ + k ζ̄)/(1 - k)`:
`∂ = 1/(1-k)`, `∂̄ = k/(1-k)` everywhere. -/
theorem s26w_dz_teichStretch (k : ℝ) (w : ℂ) :
    DifferentiableAt ℝ (teichStretch k) w ∧ dz (teichStretch k) w = 1 / (1 - k) ∧
      dzbar (teichStretch k) w = k / (1 - k) := by
  set L : ℂ →L[ℝ] ℂ := ((1 - k)⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ ℂ + k • conjCLE.toContinuousLinearMap)
    with hL
  have hfun : teichStretch k = ⇑L := by
    funext ζ
    simp only [teichStretch, hL, FunLike.coe_smul, FunLike.coe_add,
      ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, Complex.real_smul]
    push_cast
    ring
  have hd : fderiv ℝ (teichStretch k) w = L := by rw [hfun]; exact L.fderiv
  refine ⟨by rw [hfun]; exact L.differentiableAt, ?_, ?_⟩
  · rw [dz, hd]
    simp only [hL, FunLike.coe_smul, FunLike.coe_add,
      ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, Complex.real_smul, map_one, Complex.conj_I]
    by_cases hk : (1 : ℂ) - k = 0
    · have : ((1 - k : ℝ) : ℂ) = 0 := by push_cast; exact hk
      simp [this, hk]
    · push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
  · rw [dzbar, hd]
    simp only [hL, FunLike.coe_smul, FunLike.coe_add,
      ContinuousLinearMap.coe_id', Pi.smul_apply, Pi.add_apply, id_eq,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, Complex.real_smul, map_one, Complex.conj_I]
    by_cases hk : (1 : ℂ) - k = 0
    · have : ((1 - k : ℝ) : ℂ) = 0 := by push_cast; exact hk
      simp [this, hk]
    · push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
/-- **The local area factor of a Teichmüller map.**  At a point `z` of the chart at `x` where `q_x(z) ≠ 0`
and whose image lies in the chart at `y`, the local expression `g = φ_y ∘ f₀ ∘ φ_x⁻¹` is real
differentiable with `J_g(z) ≥ 0` and `J_g(z) |q'_y(g z)| = K |q_x(z)|`, `K = (1+k)/(1-k)`: near `z`,
`B ∘ g = S_k ∘ A` with `A = ζ ∘ τ`, `B = ζ' ∘ σ` holomorphic (natural parameters composed with chart
transitions), `|q_x| = |A'|²`, `|q'_y ∘ g| = |B' ∘ g|²`, and `S_k` has Jacobian `K`. -/
theorem s26w_teich_jacobian [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (x : S₀) (y : S₁) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : f₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source) (hq0 : q x z ≠ 0) :
    DifferentiableAt ℝ (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z ∧
      0 ≤ jacobian (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z ∧
      jacobian (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z *
        ‖q' y (chartAt ℂ y (f₀ ((chartAt ℂ x).symm z)))‖ = (1 + k) / (1 - k) * ‖q x z‖ := by
  set g : ℂ → ℂ := fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w)) with hg
  set p := (chartAt ℂ x).symm z with hp
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff hf₀.initial x hz).2 hq0
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hf₀.regular p hreg
  -- the source side: `A = ζ ∘ τ`, `τ = φ_p ∘ φ_x⁻¹`, `q_x(z) = A'(z)²`
  set τ := chartTransition p x with hτ
  obtain ⟨hτd, -⟩ := s23_transition p x hz (mem_chart_source ℂ p)
  have hτz : τ z = chartAt ℂ p p := rfl
  have hζd : DifferentiableAt ℂ ζ (τ z) := by rw [hτz]; exact hζ.1.differentiableAt
  set A := ζ ∘ τ with hA
  have hAd : DifferentiableAt ℂ A z := hζd.comp z hτd
  have hqA : q x z = deriv A z ^ 2 := by
    rw [s26u_law hf₀.initial x p hz (mem_chart_source ℂ p), hA, deriv_comp z hζd hτd, mul_pow]
    congr 1
    rw [hτz]
    exact hζ.2.2.2.self_of_nhds.symm
  -- the target side: `B = ζ' ∘ σ`, `σ = φ_{f₀ p} ∘ φ_y⁻¹`, `q'_y(b) = B'(b)²`
  set b := g z with hb
  have hbt : b ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hzy
  have hbs : (chartAt ℂ y).symm b = f₀ p := (chartAt ℂ y).left_inv hzy
  have hbs' : (chartAt ℂ y).symm b ∈ (chartAt ℂ (f₀ p)).source := by
    rw [hbs]; exact mem_chart_source ℂ (f₀ p)
  set σ := chartTransition (f₀ p) y with hσ
  have hσd' : deriv σ b ≠ 0 := (s23_transition (f₀ p) y hbt hbs').2
  have hσb : σ b = chartAt ℂ (f₀ p) (f₀ p) := by simp only [hσ, chartTransition, hbs]
  have hσan : AnalyticAt ℂ σ b :=
    DifferentiableOn.analyticAt (fun w hw => (s23_transition (f₀ p) y hw.1 hw.2).1.differentiableWithinAt)
      (((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (f₀ p)).open_source).mem_nhds ⟨hbt, hbs'⟩)
  have hζ'an : AnalyticAt ℂ ζ' (σ b) := by rw [hσb]; exact hζ'.1
  set B := ζ' ∘ σ with hB
  have hBan : AnalyticAt ℂ B b := hζ'an.comp hσan
  have hB' : deriv B b ≠ 0 := by
    rw [hB, deriv_comp b hζ'an.differentiableAt hσan.differentiableAt, hσb]
    exact mul_ne_zero hζ'.2.2.1 hσd'
  have hqB : q' y b = deriv B b ^ 2 := by
    rw [s26u_law hf₀.terminal y (f₀ p) hbt hbs', hB, deriv_comp b hζ'an.differentiableAt
      hσan.differentiableAt, mul_pow]
    congr 1
    change q' (f₀ p) (σ b) = _
    rw [hσb]
    exact hζ'.2.2.2.self_of_nhds.symm
  -- the local inverse of `B`
  have hBs : HasStrictDerivAt B (deriv B b) b := hBan.hasStrictDerivAt
  set Binv := hBs.localInverse B (deriv B b) b hB' with hBinv_def
  have hBinv : HasStrictDerivAt Binv (deriv B b)⁻¹ (B b) := hBs.to_localInverse hB'
  have hleft : ∀ᶠ v in 𝓝 b, Binv (B v) = v := hBs.eventually_left_inverse hB'
  -- `B ∘ g = S_k ∘ A` near `z`
  have hgc : ContinuousAt g z := by
    have h1 : ContinuousAt (fun w => f₀ ((chartAt ℂ x).symm w)) z :=
      f₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
    exact ContinuousAt.comp (g := chartAt ℂ y) (f := fun w => f₀ ((chartAt ℂ x).symm w))
      ((chartAt ℂ y).continuousAt hzy) h1
  have hτc : Tendsto τ (𝓝 z) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]; exact hτd.continuousAt.tendsto
  have hN1 : {w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ (chartAt ℂ p).source} ∈ 𝓝 z :=
    ((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds
      ⟨hz, mem_chart_source ℂ p⟩
  have hN2 : ∀ᶠ w in 𝓝 z, f₀ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ y).source :=
    (f₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds hzy)
  have hBg : ∀ᶠ w in 𝓝 z, B (g w) = teichStretch k (A w) := by
    filter_upwards [hτc.eventually hrel, hN1, hN2] with w h1 h2 h3
    simp only [hB, hA, Function.comp_apply]
    rw [← h1]
    congr 1
    simp only [hσ, hg, hτ, chartTransition, localMapExpr]
    rw [(chartAt ℂ y).left_inv h3, (chartAt ℂ p).left_inv h2.2]
  have hgeq : g =ᶠ[𝓝 z] Binv ∘ (teichStretch k ∘ A) := by
    filter_upwards [hBg, hgc.eventually hleft] with w h1 h2
    simp only [Function.comp_apply]
    rw [← h1, h2]
  -- derivatives
  obtain ⟨hSd, hSdz, hSdzbar⟩ := s26w_dz_teichStretch k (A z)
  have hFd : DifferentiableAt ℝ (teichStretch k ∘ A) z := hSd.comp z (hAd.restrictScalars ℝ)
  have hFz : (teichStretch k ∘ A) z = B b := (hBg.self_of_nhds).symm
  have hBinvd : DifferentiableAt ℂ Binv ((teichStretch k ∘ A) z) := by
    rw [hFz]; exact hBinv.hasDerivAt.differentiableAt
  have hdBinv : deriv Binv ((teichStretch k ∘ A) z) = (deriv B b)⁻¹ := by
    rw [hFz]; exact hBinv.hasDerivAt.deriv
  obtain ⟨hSA1, hSA2⟩ := eq6_4 hAd hSd
  obtain ⟨hall1, hall2⟩ := eq6_5 hFd hBinvd
  have hgd : DifferentiableAt ℝ g z :=
    ((hBinvd.restrictScalars ℝ).comp z hFd).congr_of_eventuallyEq hgeq
  have hdz : dz g z = (deriv B b)⁻¹ * (1 / (1 - k) * deriv A z) := by
    unfold dz
    rw [hgeq.fderiv_eq]
    rw [← dz, hall1, hdBinv, hSA1, hSdz]
  have hdzbar : dzbar g z = (deriv B b)⁻¹ * (k / (1 - k) * conj (deriv A z)) := by
    unfold dzbar
    rw [hgeq.fderiv_eq]
    rw [← dzbar, hall2, hdBinv, hSA2, hSdzbar]
  have h1k : (0 : ℝ) < 1 - k := by linarith [hf₀.k_lt_one]
  have hn1k : ‖(1 : ℂ) - (k : ℂ)‖ = 1 - k := by
    rw [show (1 : ℂ) - (k : ℂ) = ((1 - k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg h1k.le]
  have hnk : ‖(k : ℂ)‖ = k := by rw [Complex.norm_real, Real.norm_of_nonneg hf₀.k_nonneg]
  have hβ : 0 < ‖deriv B b‖ := norm_pos_iff.2 hB'
  have hJ : jacobian g z = ‖deriv A z‖ ^ 2 * ((1 + k) / (1 - k)) / ‖deriv B b‖ ^ 2 := by
    unfold jacobian
    rw [hdz, hdzbar]
    simp only [norm_mul, norm_inv, norm_div, norm_one, hn1k, hnk, Complex.norm_conj]
    field_simp
    ring
  refine ⟨hgd, ?_, ?_⟩
  · rw [hJ]; have := hf₀.k_nonneg; positivity
  · rw [hJ, hqB, hqA, norm_pow, norm_pow]
    field_simp

/-- The part of an open set `D` where a map continuous on `D` takes values in a measurable set is
measurable. -/
theorem s26w_measurableSet_inter_preimage {D M : Set ℂ} {G : ℂ → ℂ} (hD : IsOpen D)
    (hG : ContinuousOn G D) (hM : MeasurableSet M) : MeasurableSet (D ∩ G ⁻¹' M) := by
  classical
  have hm : Measurable (D.piecewise G (fun _ => 0)) :=
    hG.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ G ⁻¹' M = D ∩ (D.piecewise G (fun _ => 0)) ⁻¹' M := by
    ext w
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [Set.piecewise_eq_of_mem _ _ _ h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [Set.piecewise_eq_of_mem _ _ _ h1] at h2; exact h2⟩
  rw [heq]
  exact hD.measurableSet.inter (hm hM)

/-- For a continuous `F : X → Y`, pieces `P ⊆ U_x`, `Q ⊆ U_y` with measurable chart images, the chart
image `φ_x(P ∩ F⁻¹ Q)` is measurable: it is `φ_x(P)` intersected with the preimage of `φ_y(Q)` under
the local expression `φ_y ∘ F ∘ φ_x⁻¹`, continuous on its open domain. -/
theorem s26w_measurableSet_chart_piece {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {F : X → Y} (hF : Continuous F) (x : X) (y : Y)
    {P : Set X} {Q : Set Y} (hP : P ⊆ (chartAt ℂ x).source) (hQ : Q ⊆ (chartAt ℂ y).source)
    (hPm : MeasurableSet (chartAt ℂ x '' P)) (hQm : MeasurableSet (chartAt ℂ y '' Q)) :
    MeasurableSet (chartAt ℂ x '' (P ∩ F ⁻¹' Q)) := by
  set φ := chartAt ℂ x
  set ψ := chartAt ℂ y
  have hFc : ContinuousOn (fun w => F (φ.symm w)) φ.target := hF.comp_continuousOn φ.continuousOn_symm
  set D := φ.target ∩ (fun w => F (φ.symm w)) ⁻¹' ψ.source with hD
  have hDo : IsOpen D := hFc.isOpen_inter_preimage φ.open_target ψ.open_source
  have hGc : ContinuousOn (fun w => ψ (F (φ.symm w))) D :=
    ψ.continuousOn.comp (hFc.mono inter_subset_left) fun w hw => hw.2
  have heq : φ '' (P ∩ F ⁻¹' Q) = φ '' P ∩ (D ∩ (fun w => ψ (F (φ.symm w))) ⁻¹' (ψ '' Q)) := by
    ext z
    constructor
    · rintro ⟨a, ⟨haP, haQ⟩, rfl⟩
      have hl : φ.symm (φ a) = a := φ.left_inv (hP haP)
      refine ⟨⟨a, haP, rfl⟩, ⟨φ.map_source (hP haP), ?_⟩, ?_⟩
      · show F (φ.symm (φ a)) ∈ ψ.source
        rw [hl]; exact hQ haQ
      · show ψ (F (φ.symm (φ a))) ∈ ψ '' Q
        rw [hl]; exact ⟨F a, haQ, rfl⟩
    · rintro ⟨⟨a, haP, rfl⟩, ⟨-, hsrc⟩, ⟨b, hbQ, hb⟩⟩
      have hl : φ.symm (φ a) = a := φ.left_inv (hP haP)
      have hsrc' : F a ∈ ψ.source := by
        have h := hsrc
        simp only [mem_preimage, hl] at h
        exact h
      have hb' : ψ b = ψ (F a) := by
        simp only [hl] at hb
        exact hb
      have hFa : F a = b := (ψ.injOn (hQ hbQ) hsrc' hb').symm
      exact ⟨a, ⟨haP, show F a ∈ Q by rw [hFa]; exact hbQ⟩, rfl⟩
  rw [heq]
  exact hPm.inter (s26w_measurableSet_inter_preimage hDo hGc hQm)

/-- Images of disjoint subsets of `s` under a map injective on `s` are disjoint. -/
theorem s26w_disjoint_image {α β : Type*} {f : α → β} {s A B : Set α} (hf : InjOn f s) (hA : A ⊆ s)
    (hB : B ⊆ s) (hAB : Disjoint A B) : Disjoint (f '' A) (f '' B) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have h := hf (hB hb) (hA ha) hab
  exact Set.disjoint_left.1 hAB ha (h ▸ hb)

/-- **Assembly over two chart partitions.**  If for every chart pair `(x, y)` and every piece `A` in the
chart at `x` with `F(A)` in the chart at `y` (measurable chart images) the `q'`-area of `F(A)` equals the
integral of `u` against the `q`-area over `A`, then the partition sums of `|q'|` over any chart partition of
`Y` and of `u |q|` over any chart partition of `X` agree (refine by `A_{ij} = P_i ∩ F⁻¹ Q_j`). -/
theorem s26w_partition_sum_eq {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (F : X ≃ₜ Y) (q : X → ℂ → ℂ) (q' : Y → ℂ → ℂ)
    (u : X → ℂ → ℝ≥0∞)
    (hloc : ∀ (x : X) (y : Y) (A : Set X), A ⊆ (chartAt ℂ x).source → F '' A ⊆ (chartAt ℂ y).source →
      MeasurableSet (chartAt ℂ x '' A) → MeasurableSet (chartAt ℂ y '' (F '' A)) →
      ∫⁻ w in chartAt ℂ y '' (F '' A), ENNReal.ofReal ‖q' y w‖ =
        ∫⁻ z in chartAt ℂ x '' A, u x z * ENNReal.ofReal ‖q x z‖)
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) {y : ℕ → Y} {Q : ℕ → Set Y}
    (hQ : IsChartPartition Y y Q) :
    ∑' j, ∫⁻ w in chartAt ℂ (y j) '' Q j, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q' (y j) w‖ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ := by
  obtain ⟨hPsm, hPd, hPc⟩ := hP
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  set A : ℕ → ℕ → Set X := fun i j => P i ∩ F ⁻¹' Q j with hAdef
  have hFA : ∀ i j, F '' A i j = Q j ∩ F.symm ⁻¹' P i := by
    intro i j
    rw [hAdef]
    dsimp only
    rw [image_inter_preimage, F.image_eq_preimage_symm, inter_comm]
  have hAs : ∀ i j, A i j ⊆ (chartAt ℂ (x i)).source := fun i j => inter_subset_left.trans (hPsm i).1
  have hFAs : ∀ i j, F '' A i j ⊆ (chartAt ℂ (y j)).source := fun i j => by
    rw [hFA]; exact inter_subset_left.trans (hQsm j).1
  have hAm : ∀ i j, MeasurableSet (chartAt ℂ (x i) '' A i j) := fun i j =>
    s26w_measurableSet_chart_piece F.continuous (x i) (y j) (hPsm i).1 (hQsm j).1 (hPsm i).2 (hQsm j).2
  have hFAm : ∀ i j, MeasurableSet (chartAt ℂ (y j) '' (F '' A i j)) := fun i j => by
    rw [hFA]
    exact s26w_measurableSet_chart_piece F.symm.continuous (y j) (x i) (hQsm j).1 (hPsm i).1
      (hQsm j).2 (hPsm i).2
  -- the source pieces
  have hsrc : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ =
      ∑' j, ∫⁻ z in chartAt ℂ (x i) '' A i j, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ := by
    intro i
    have hU : chartAt ℂ (x i) '' P i = ⋃ j, chartAt ℂ (x i) '' A i j := by
      rw [← image_iUnion]
      congr 1
      rw [hAdef]
      dsimp only
      rw [← inter_iUnion, ← preimage_iUnion, hQc, preimage_univ, inter_univ]
    rw [hU, lintegral_iUnion (hAm i)]
    intro j j' hjj'
    exact s26w_disjoint_image (chartAt ℂ (x i)).injOn (hAs i j) (hAs i j')
      (Disjoint.mono inter_subset_right inter_subset_right ((hQd hjj').preimage F))
  -- the target pieces
  have htgt : ∀ j, ∫⁻ w in chartAt ℂ (y j) '' Q j, (1 : ℝ≥0∞) * ENNReal.ofReal ‖q' (y j) w‖ =
      ∑' i, ∫⁻ w in chartAt ℂ (y j) '' (F '' A i j), ENNReal.ofReal ‖q' (y j) w‖ := by
    intro j
    have hU : chartAt ℂ (y j) '' Q j = ⋃ i, chartAt ℂ (y j) '' (F '' A i j) := by
      rw [← image_iUnion]
      congr 1
      simp only [hFA]
      rw [← inter_iUnion, ← preimage_iUnion, hPc, preimage_univ, inter_univ]
    simp only [one_mul]
    rw [hU, lintegral_iUnion (hFAm · j)]
    intro i i' hii'
    exact s26w_disjoint_image (chartAt ℂ (y j)).injOn (hFAs i j) (hFAs i' j)
      (by
        rw [hFA, hFA]
        exact Disjoint.mono inter_subset_right inter_subset_right ((hPd hii').preimage F.symm))
  simp only [htgt, hsrc]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => tsum_congr fun j => ?_
  exact hloc (x i) (y j) (A i j) (hAs i j) (hFAs i j) (hAm i j) (hFAm i j)

/-- **Chart invariance by a homeomorphism.**  Under the hypothesis of `s26w_partition_sum_eq`, on compact
nonempty surfaces `‖q'‖ = ∬ u dA_q` (every partition sum on either side has the same value). -/
theorem s26w_quadDiffNorm_eq_surfaceIntegral {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [CompactSpace X] [Nonempty X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [CompactSpace Y]
    [Nonempty Y] (F : X ≃ₜ Y) (q : X → ℂ → ℂ) (q' : Y → ℂ → ℂ) (u : X → ℂ → ℝ≥0∞)
    (hloc : ∀ (x : X) (y : Y) (A : Set X), A ⊆ (chartAt ℂ x).source → F '' A ⊆ (chartAt ℂ y).source →
      MeasurableSet (chartAt ℂ x '' A) → MeasurableSet (chartAt ℂ y '' (F '' A)) →
      ∫⁻ w in chartAt ℂ y '' (F '' A), ENNReal.ofReal ‖q' y w‖ =
        ∫⁻ z in chartAt ℂ x '' A, u x z * ENNReal.ofReal ‖q x z‖) :
    quadDiffNorm q' = surfaceIntegral q u := by
  obtain ⟨x₀, P₀, hP₀⟩ := s26_exists_chartPartition' (S := X)
  obtain ⟨y₀, Q₀, hQ₀⟩ := s26_exists_chartPartition' (S := Y)
  unfold quadDiffNorm surfaceIntegral
  refine le_antisymm ?_ ?_
  · refine le_iInf fun x => le_iInf fun P => le_iInf fun hP => ?_
    exact iInf_le_of_le y₀ (iInf_le_of_le Q₀ (iInf_le_of_le hQ₀
      (le_of_eq (s26w_partition_sum_eq F q q' u hloc hP hQ₀))))
  · refine le_iInf fun y => le_iInf fun Q => le_iInf fun hQ => ?_
    exact iInf_le_of_le x₀ (iInf_le_of_le P₀ (iInf_le_of_le hP₀
      (le_of_eq (s26w_partition_sum_eq F q q' u hloc hP₀ hQ).symm)))

/-- The surface integral of a constant `c ≠ 0, ∞` is `c ‖q‖`. -/
theorem s26w_surfaceIntegral_const {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ)
    {c : ℝ≥0∞} (h0 : c ≠ 0) (htop : c ≠ ⊤) :
    surfaceIntegral q (fun _ _ => c) = c * quadDiffNorm q := by
  unfold quadDiffNorm surfaceIntegral
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun x => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine iInf_congr fun _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [← lintegral_const_mul' _ _ htop]
  simp only [one_mul]

/-- **A Teichmüller map multiplies `q`-areas by `K`, piecewise.**  For a piece `A` in the chart at `x` with
`f₀(A)` in the chart at `y`: `∬_{φ_y(f₀ A)} |q'_y| = K ∬_{φ_x(A)} |q_x|`, by the change of variables through
`g = φ_y ∘ f₀ ∘ φ_x⁻¹` off the countable zero set of `q_x` (`s26w_teich_jacobian`). -/
theorem s26w_teich_piece [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (x : S₀) (y : S₁) (A : Set S₀) (hA : A ⊆ (chartAt ℂ x).source) (hFA : f₀ '' A ⊆ (chartAt ℂ y).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ w in chartAt ℂ y '' (f₀ '' A), ENNReal.ofReal ‖q' y w‖ =
      ∫⁻ z in chartAt ℂ x '' A, ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖ := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  set g : ℂ → ℂ := fun w => ψ (f₀ (φ.symm w)) with hg
  set s := φ '' A with hs
  set Z := {z | z ∈ φ.target ∧ q x z = 0} with hZ
  have hZc : Z.Countable := s26u_zeros_countable hf₀.initial hf₀.initial_ne x
  have hZ0 : volume Z = 0 := hZc.measure_zero _
  set s' := s \ Z with hs'
  have hs'm : MeasurableSet s' := hAm.diff hZc.measurableSet
  have himg : ψ '' (f₀ '' A) = g '' s := by
    rw [hs, image_image, image_image]
    refine image_congr fun a ha => ?_
    simp only [hg, φ.left_inv (hA ha)]
  -- the points of `s'`
  have hpt : ∀ z ∈ s', z ∈ φ.target ∧ f₀ (φ.symm z) ∈ ψ.source ∧ q x z ≠ 0 := by
    rintro z ⟨⟨a, ha, rfl⟩, hzZ⟩
    have hl : φ.symm (φ a) = a := φ.left_inv (hA ha)
    refine ⟨φ.map_source (hA ha), by rw [hl]; exact hFA ⟨a, ha, rfl⟩, fun h0 => hzZ ⟨φ.map_source (hA ha), h0⟩⟩
  have hjac := fun z (hz : z ∈ s') =>
    s26w_teich_jacobian hf₀ x y (hpt z hz).1 (hpt z hz).2.1 (hpt z hz).2.2
  have hinj : InjOn g s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    have h' : ψ (f₀ a) = ψ (f₀ b) := by
      simp only [hg, φ.left_inv (hA ha), φ.left_inv (hA hb)] at h
      exact h
    have h'' := f₀.injective (ψ.injOn (hFA ⟨a, ha, rfl⟩) (hFA ⟨b, hb, rfl⟩) h')
    rw [h'']
  -- the null parts
  have hs's : s' ⊆ s := sdiff_subset
  have hsrc_ae : s' =ᵐ[volume] s := sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right hZ0)
  have htgt_ae : g '' s' =ᵐ[volume] g '' s := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 (image_mono hs's), measure_empty]
    · refine measure_mono_null (t := g '' (s ∩ Z)) ?_ ((hZc.mono inter_subset_right).image g |>.measure_zero _)
      rintro _ ⟨⟨z, hz, rfl⟩, hz'⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      by_contra hzZ
      exact hz' ⟨z, ⟨hz, hzZ⟩, rfl⟩
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs'm
    (fun z hz => (hjac z hz).1.hasFDerivAt.hasFDerivWithinAt) (hinj.mono hs's)
    (fun w => ENNReal.ofReal ‖q' y w‖)
  rw [himg, ← setLIntegral_congr htgt_ae, hcv, ← setLIntegral_congr hsrc_ae]
  refine setLIntegral_congr_fun hs'm fun z hz => ?_
  obtain ⟨hd, hJ0, hJ⟩ := hjac z hz
  have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian hd
  have hK : 0 ≤ (1 + k) / (1 - k) := by
    have := hf₀.k_nonneg
    have := hf₀.k_lt_one
    exact div_nonneg (by linarith) (by linarith)
  rw [e, abs_of_nonneg hJ0, ← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul hK]
  exact congrArg ENNReal.ofReal hJ

/-- **Conjunct 1 of (26.14)**: a Teichmüller map multiplies the norm by `K = (1+k)/(1-k)`:
`‖q'‖ = K ‖q‖` (`s26w_teich_piece` on every chart piece, assembled by `s26w_quadDiffNorm_eq_surfaceIntegral`). -/
theorem s26w_quadDiffNorm_teich [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) :
    quadDiffNorm q' = ENNReal.ofReal ((1 + k) / (1 - k)) * quadDiffNorm q := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : Nonempty S₁ := ConnectedSpace.toNonempty
  have hK : 0 < (1 + k) / (1 - k) := by
    have := hf₀.k_nonneg
    have := hf₀.k_lt_one
    exact div_pos (by linarith) (by linarith)
  rw [s26w_quadDiffNorm_eq_surfaceIntegral f₀ q q' (fun _ _ => ENNReal.ofReal ((1 + k) / (1 - k)))
    fun x y A hA hFA hAm _ => s26w_teich_piece hf₀ x y A hA hFA hAm]
  exact s26w_surfaceIntegral_const q (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top

/-- **Local conjugation, general form**: if near `z₀` one has `g = σ ∘ F ∘ τ` with `τ`, `σ` holomorphic with
nonzero derivative (at `z₀`, resp. `F (τ z₀)`) and `F` `K`-q.c. on an open set `V ∋ τ z₀`, then `g` is
`K`-q.c. on an open neighbourhood of `z₀` inside any given neighbourhood `N` (`thm7_1_comp` with the
conformal maps `τ` and `σ`). -/
theorem s26w_isKQC_local_comp {g τ σ F : ℂ → ℂ} {z₀ : ℂ} {K : ℝ} {V : Set ℂ} (hF : IsKQC F V K)
    (hτV : τ z₀ ∈ V) (hτ : AnalyticAt ℂ τ z₀) (hτ' : deriv τ z₀ ≠ 0) (hσ : AnalyticAt ℂ σ (F (τ z₀)))
    (hσ' : deriv σ (F (τ z₀)) ≠ 0) (hg : ∀ᶠ w in 𝓝 z₀, g w = σ (F (τ w))) {N : Set ℂ} (hN : N ∈ 𝓝 z₀) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ N ∧ IsKQC g U K := by
  obtain ⟨W₁, hW₁o, hzW₁, hτd, hτi⟩ := s26u_exists_open_injOn hτ hτ'
  obtain ⟨W₂, hW₂o, hW₂, hσd, hσi⟩ := s26u_exists_open_injOn hσ hσ'
  have hFc : ContinuousAt F (τ z₀) := hF.2.2.1.1.continuousAt (hF.1.mem_nhds hτV)
  have hτc : ContinuousAt τ z₀ := hτ.continuousAt
  have hFτc : ContinuousAt (F ∘ τ) z₀ := hFc.comp hτc
  set S : Set ℂ := {w | w ∈ N ∧ w ∈ W₁ ∧ τ w ∈ V ∧ F (τ w) ∈ W₂ ∧ g w = σ (F (τ w))} with hSdef
  have hS : S ∈ 𝓝 z₀ := by
    filter_upwards [hN, hW₁o.mem_nhds hzW₁, hτc.preimage_mem_nhds (hF.1.mem_nhds hτV),
      hFτc.preimage_mem_nhds (hW₂o.mem_nhds hW₂), hg] with w h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hUo : IsOpen (interior S) := isOpen_interior
  have hzU : z₀ ∈ interior S := mem_interior_iff_mem_nhds.2 hS
  have hUS : interior S ⊆ S := interior_subset
  have hτ1 : IsKQC τ (interior S) 1 := isKQC_one_of_conformal hUo
    ⟨hτd.mono fun w hw => (hUS hw).2.1, hτi.mono fun w hw => (hUS hw).2.1, rfl⟩
  have hFτ := thm7_1_comp hτ1 hF (by rintro _ ⟨w, hw, rfl⟩; exact (hUS hw).2.2.1)
  have hσ1 : IsKQC σ W₂ 1 := isKQC_one_of_conformal hW₂o ⟨hσd, hσi, rfl⟩
  have hall := thm7_1_comp hFτ hσ1 (by rintro _ ⟨w, hw, rfl⟩; exact (hUS hw).2.2.2.1)
  rw [one_mul, mul_one] at hall
  exact ⟨interior S, hUo, hzU, fun w hw => (hUS hw).1, ad_isKQC_congr hall fun w hw => (hUS hw).2.2.2.2⟩

/-- **The local expression of a q.c. map in an arbitrary chart pair is locally `K`-q.c.**:
`g = φ_y ∘ f ∘ φ_x⁻¹` near a point `z` of its (open) domain is `σ ∘ F ∘ τ`, with `F` the local expression of
`f` at `p = φ_x⁻¹ z` (`K`-q.c.) and `τ`, `σ` holomorphic chart transitions. -/
theorem s26w_qc_chart_local [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ}
    (hf : IsKQCRS f K) (x : S₀) (y : S₁) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target ∩ (fun w => f ((chartAt ℂ x).symm w)) ⁻¹' (chartAt ℂ y).source) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      U ⊆ (chartAt ℂ x).target ∩ (fun w => f ((chartAt ℂ x).symm w)) ⁻¹' (chartAt ℂ y).source ∧
      IsKQC (fun w => chartAt ℂ y (f ((chartAt ℂ x).symm w))) U K := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  obtain ⟨hzt, hzy⟩ := hz
  have hzy' : f (φ.symm z) ∈ ψ.source := hzy
  set p := φ.symm z with hp
  have hFc : ContinuousOn (fun w => f (φ.symm w)) φ.target :=
    f.continuous.comp_continuousOn φ.continuousOn_symm
  have hDo : IsOpen (φ.target ∩ (fun w => f (φ.symm w)) ⁻¹' ψ.source) :=
    hFc.isOpen_inter_preimage φ.open_target ψ.open_source
  -- the source transition `τ`
  set τ := chartTransition p x with hτ
  have hτan : AnalyticAt ℂ τ z :=
    DifferentiableOn.analyticAt (fun w hw => (s23_transition p x hw.1 hw.2).1.differentiableWithinAt)
      ((φ.isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds ⟨hzt, mem_chart_source ℂ p⟩)
  have hτd : deriv τ z ≠ 0 := (s23_transition p x hzt (mem_chart_source ℂ p)).2
  have hτz : τ z = chartAt ℂ p p := rfl
  have hpp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hτV : τ z ∈ localMapDomain f p := by
    rw [hτz]
    refine ⟨mem_chart_target ℂ p, ?_⟩
    show f ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (f p)).source
    rw [hpp]; exact mem_chart_source ℂ (f p)
  -- the target transition `σ`
  have hFτz : localMapExpr f p (τ z) = chartAt ℂ (f p) (f p) := by
    simp only [localMapExpr, hτz, hpp]
  set σ := chartTransition y (f p) with hσ
  have hbt : chartAt ℂ (f p) (f p) ∈ (chartAt ℂ (f p)).target := mem_chart_target ℂ (f p)
  have hbs : (chartAt ℂ (f p)).symm (chartAt ℂ (f p) (f p)) ∈ ψ.source := by
    rw [(chartAt ℂ (f p)).left_inv (mem_chart_source ℂ (f p))]; exact hzy'
  have hσan : AnalyticAt ℂ σ (localMapExpr f p (τ z)) := by
    rw [hFτz]
    exact DifferentiableOn.analyticAt
      (fun w hw => (s23_transition y (f p) hw.1 hw.2).1.differentiableWithinAt)
      (((chartAt ℂ (f p)).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hbt, hbs⟩)
  have hσd : deriv σ (localMapExpr f p (τ z)) ≠ 0 := by
    rw [hFτz]; exact (s23_transition y (f p) hbt hbs).2
  -- `g = σ ∘ F ∘ τ` near `z`
  have hg : ∀ᶠ w in 𝓝 z, (fun w => ψ (f (φ.symm w))) w = σ (localMapExpr f p (τ w)) := by
    have h1 : ∀ᶠ w in 𝓝 z, f (φ.symm w) ∈ (chartAt ℂ (f p)).source :=
      (f.continuous.continuousAt.comp (φ.continuousAt_symm hzt)).preimage_mem_nhds
        ((chartAt ℂ (f p)).open_source.mem_nhds (mem_chart_source ℂ (f p)))
    filter_upwards [h1, (φ.isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds
      ⟨hzt, mem_chart_source ℂ p⟩] with w hw1 hw2
    simp only [hσ, hτ, chartTransition, localMapExpr]
    rw [(chartAt ℂ p).left_inv hw2.2, (chartAt ℂ (f p)).left_inv hw1]
  exact s26w_isKQC_local_comp (hf.2 p) hτV hτan hτd hσan hσd hg (hDo.mem_nhds ⟨hzt, hzy⟩)

/-- A map that is `K`-q.c. near every point of a set `D` is differentiable a.e. on `D`, has nonnegative
Jacobian at its points of differentiability in `D`, and maps null subsets of `D` to null sets (Theorems 9.3
and 9.6 on a countable subcover). -/
theorem s26w_locally_qc {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hloc : ∀ z ∈ D, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ D ∧ IsKQC g U K) :
    (∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ g z) ∧
      (∀ z ∈ D, DifferentiableAt ℝ g z → 0 ≤ jacobian g z) ∧
      (∀ E ⊆ D, volume E = 0 → volume (g '' E) = 0) := by
  choose U hUo hzU hUD hUK using hloc
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun i : D => U i.1 i.2) (fun i => hUo i.1 i.2)
  have hD : D = ⋃ i ∈ T, U i.1 i.2 := by
    rw [hTU]
    ext z
    simp only [mem_iUnion]
    exact ⟨fun hz => ⟨⟨z, hz⟩, hzU z hz⟩, fun ⟨i, hi⟩ => hUD i.1 i.2 hi⟩
  refine ⟨?_, fun z hz hd => ac_j_jacobian_nonneg (hUK z hz) (hzU z hz) hd, fun E hED hE => ?_⟩
  · rw [hD, ae_restrict_biUnion_iff _ hTc]
    exact fun i _ => thm9_3_differentiable_ae (hUK i.1 i.2)
  · have hE' : g '' E = ⋃ i ∈ T, g '' (E ∩ U i.1 i.2) := by
      rw [← image_iUnion₂, ← inter_iUnion₂, ← hD, inter_eq_left.2 hED]
    rw [hE', measure_biUnion_null_iff hTc]
    exact fun i _ => ac_n_volume_image_null_of_isKQC (hUK i.1 i.2) inter_subset_right
      (measure_mono_null inter_subset_left hE)

/-- **Change of variables through a locally quasiconformal map** (weighted form of Theorem 9.6):
`∬_{g(s)} h = ∬_s h(g) J_g` for measurable `s ⊆ D` on which `g` is injective. -/
theorem s26w_lintegral_image {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hloc : ∀ z ∈ D, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ D ∧ IsKQC g U K) {s : Set ℂ}
    (hs : MeasurableSet s) (hsD : s ⊆ D) (hinj : InjOn g s) (h : ℂ → ℝ≥0∞) :
    ∫⁻ w in g '' s, h w = ∫⁻ z in s, ENNReal.ofReal (jacobian g z) * h (g z) := by
  obtain ⟨hdiff, hjac, hN⟩ := s26w_locally_qc hloc
  set E : Set ℂ := s ∩ {z | DifferentiableAt ℝ g z} with hEdef
  have hEm : MeasurableSet E := hs.inter (measurableSet_of_differentiableAt ℝ g)
  have hEs : E ⊆ s := inter_subset_left
  have hnull : volume (s \ E) = 0 := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hsD hdiff
    rw [ae_restrict_iff' hs, ae_iff] at h1
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' hz.1⟩) h1
  have himg_null : volume (g '' (s \ E)) = 0 := hN _ (fun z hz => hsD hz.1) hnull
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hEm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt) (hinj.mono hEs) h
  have htgt : g '' E =ᵐ[volume] g '' s := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 (image_mono hEs), measure_empty]
    · refine measure_mono_null ?_ himg_null
      rintro _ ⟨⟨z, hz, rfl⟩, hz'⟩
      exact ⟨z, ⟨hz, fun hzE => hz' ⟨z, hzE, rfl⟩⟩, rfl⟩
  have hsrc : E =ᵐ[volume] s := ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hEs, measure_empty], hnull⟩
  rw [← setLIntegral_congr htgt, hcv, ← setLIntegral_congr hsrc]
  refine setLIntegral_congr_fun hEm fun z hz => ?_
  have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian hz.2
  rw [e, abs_of_nonneg (hjac z (hsD hz.1) hz.2)]

/-- **`J_f` in the chart at the image point is chart invariant**: for `z` in the chart at `x` with
`f(φ_x⁻¹ z)` in the chart at `y` and `q_x(z) ≠ 0`, `J_f(z) |q_x(z)| = J_g(z) |q'_y(g z)|`,
`g = φ_y ∘ f ∘ φ_x⁻¹` (`g = σ ∘ localMapExprAt f x z` near `z` with a holomorphic transition `σ`, and the
transformation law of `q'`). -/
theorem s26w_jacobianQD_mul [IsManifold 𝓘(ℂ) ω S₁] {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    (hq' : IsHolQuadDiff q') {f : S₀ → S₁} (hf : Continuous f) (x : S₀) (y : S₁) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source)
    (hq0 : q x z ≠ 0) :
    jacobianQD q q' f x z * ‖q x z‖ =
      jacobian (fun w => chartAt ℂ y (f ((chartAt ℂ x).symm w))) z *
        ‖q' y (chartAt ℂ y (f ((chartAt ℂ x).symm z)))‖ := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  set p := φ.symm z with hp
  set G := localMapExprAt f x z with hG
  set g : ℂ → ℂ := fun w => ψ (f (φ.symm w)) with hg
  have hq0' : ‖q x z‖ ≠ 0 := norm_ne_zero_iff.2 hq0
  have hL : jacobianQD q q' f x z * ‖q x z‖ = ‖q' (f p) (G z)‖ * jacobian G z := by
    unfold jacobianQD
    rw [div_mul_cancel₀ _ hq0']
  set b := G z with hb
  have hbv : b = chartAt ℂ (f p) (f p) := rfl
  have hbt : b ∈ (chartAt ℂ (f p)).target := by rw [hbv]; exact mem_chart_target ℂ (f p)
  have hbs0 : (chartAt ℂ (f p)).symm b = f p := by
    rw [hbv]; exact (chartAt ℂ (f p)).left_inv (mem_chart_source ℂ (f p))
  have hbs : (chartAt ℂ (f p)).symm b ∈ ψ.source := by rw [hbs0]; exact hzy
  set σ := chartTransition y (f p) with hσ
  have hσb : σ b = g z := by
    simp only [hσ, chartTransition, hbs0, hg]
    rfl
  have hσd : DifferentiableAt ℂ σ b := (s23_transition y (f p) hbt hbs).1
  obtain ⟨hm1, hm2, -⟩ := s23_transition_mem hbt hbs
  have hk : DifferentiableAt ℂ (chartTransition (f p) y) (σ b) :=
    s23_transition_differentiableAt (f p) y hm1 hm2
  have hkh := s23_transition_inv y (f p) hbt hbs
  have hGc : ContinuousAt G z := by
    have h1 : ContinuousAt (fun w => f (φ.symm w)) z :=
      hf.continuousAt.comp (φ.continuousAt_symm hz)
    exact ContinuousAt.comp (g := chartAt ℂ (f p)) (f := fun w => f (φ.symm w))
      ((chartAt ℂ (f p)).continuousAt (mem_chart_source ℂ (f p))) h1
  obtain ⟨hW1, hW2⟩ := s23_wirtinger_comp_left hGc hσd hk hkh
  have hgeq : g =ᶠ[𝓝 z] σ ∘ G := by
    have h1 : ∀ᶠ w in 𝓝 z, f (φ.symm w) ∈ (chartAt ℂ (f p)).source :=
      (hf.continuousAt.comp (φ.continuousAt_symm hz)).preimage_mem_nhds
        ((chartAt ℂ (f p)).open_source.mem_nhds (mem_chart_source ℂ (f p)))
    filter_upwards [h1] with w hw
    simp only [hg, hσ, hG, Function.comp_apply, chartTransition, localMapExprAt]
    rw [(chartAt ℂ (f p)).left_inv hw]
  have hdz : dz g z = dz (σ ∘ G) z := by unfold dz; rw [hgeq.fderiv_eq]
  have hdzbar : dzbar g z = dzbar (σ ∘ G) z := by unfold dzbar; rw [hgeq.fderiv_eq]
  have hJ : jacobian g z = ‖deriv σ b‖ ^ 2 * jacobian G z := by
    unfold jacobian
    rw [hdz, hdzbar, hW1, hW2, norm_mul, norm_mul]
    ring
  have hlaw : q' (f p) b = q' y (σ b) * deriv σ b ^ 2 := s26u_law hq' (f p) y hbt hbs
  rw [hL, show chartAt ℂ y (f ((chartAt ℂ x).symm z)) = σ b from hσb.symm, hJ, hlaw, norm_mul, norm_pow]
  ring

/-- **Change of variables through a quasiconformal map, piecewise.**  For a piece `A` in the chart at `x`
with `f(A)` in the chart at `y`: `∬_{φ_y(f A)} |q'_y| = ∬_{φ_x(A)} J_f |q_x|` (`s26w_lintegral_image` for the
locally q.c. `g = φ_y ∘ f ∘ φ_x⁻¹`, then `s26w_jacobianQD_mul` off the countable zero set of `q_x`). -/
theorem s26w_qc_piece [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hq' : IsHolQuadDiff q')
    {f : S₀ ≃ₜ S₁} (hf : IsQCRS f) (x : S₀) (y : S₁) (A : Set S₀) (hA : A ⊆ (chartAt ℂ x).source)
    (hFA : f '' A ⊆ (chartAt ℂ y).source) (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ w in chartAt ℂ y '' (f '' A), ENNReal.ofReal ‖q' y w‖ =
      ∫⁻ z in chartAt ℂ x '' A, ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖ := by
  obtain ⟨K, hK⟩ := hf
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  set g : ℂ → ℂ := fun w => ψ (f (φ.symm w)) with hg
  set s := φ '' A with hs
  have hsD : s ⊆ φ.target ∩ (fun w => f (φ.symm w)) ⁻¹' ψ.source := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨φ.map_source (hA ha), ?_⟩
    show f (φ.symm (φ a)) ∈ ψ.source
    rw [φ.left_inv (hA ha)]; exact hFA ⟨a, ha, rfl⟩
  have himg : ψ '' (f '' A) = g '' s := by
    rw [hs, image_image, image_image]
    refine image_congr fun a ha => ?_
    simp only [hg, φ.left_inv (hA ha)]
  have hinj : InjOn g s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    have h' : ψ (f a) = ψ (f b) := by
      simp only [hg, φ.left_inv (hA ha), φ.left_inv (hA hb)] at h
      exact h
    have h'' := f.injective (ψ.injOn (hFA ⟨a, ha, rfl⟩) (hFA ⟨b, hb, rfl⟩) h')
    rw [h'']
  rw [himg, s26w_lintegral_image (fun z hz => s26w_qc_chart_local hK x y hz) hAm hsD hinj]
  set Z := {z | z ∈ φ.target ∧ q x z = 0} with hZ
  have hZ0 : volume Z = 0 := (s26u_zeros_countable hq hne x).measure_zero _
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ0] with z hzZ hzs
  have hzD := hsD hzs
  have hq0 : q x z ≠ 0 := fun h0 => hzZ ⟨hzD.1, h0⟩
  rw [← ENNReal.ofReal_mul' (norm_nonneg _), ← ENNReal.ofReal_mul' (norm_nonneg _),
    s26w_jacobianQD_mul hq' f.continuous x y hzD.1 hzD.2 hq0]

/-- **Conjunct 2 of (26.14)**: for a quasiconformal `f : S₀ → S`, `∬_S dA_{q'} = ∬_{S₀} J_f dA_q`
(`s26w_qc_piece` on every chart piece, assembled by `s26w_quadDiffNorm_eq_surfaceIntegral`). -/
theorem s26w_quadDiffNorm_qc [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁] {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hq' : IsHolQuadDiff q') {f : S₀ ≃ₜ S₁} (hf : IsQCRS f) :
    quadDiffNorm q' = surfaceIntegral q fun x z => ENNReal.ofReal (jacobianQD q q' f x z) := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : Nonempty S₁ := ConnectedSpace.toNonempty
  exact s26w_quadDiffNorm_eq_surfaceIntegral f q q' _ fun x y A hA hFA hAm _ =>
    s26w_qc_piece hq hne hq' hf x y A hA hFA hAm

/-- (26.14): `∬_S dA_{q'} ≤ K₀⁻² K[f] ∬_S J_f dA_{q'} = K₀⁻¹ K[f] ∬_{S₀} dA_q = K₀⁻¹ K[f] ∬_S dA_{q'}`,
the last equality because `f₀` multiplies `q`-areas by `K₀`: for a Teichmüller map
`‖q'‖ = K₀ ‖q‖`, and for a quasiconformal `f : S₀ → S` the change of variables
`∬_S dA_{q'} = ∬_{S₀} J_f dA_q`. -/
theorem eq26_14 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} (hf : IsQCRS f) :
    quadDiffNorm q' = ENNReal.ofReal ((1 + k) / (1 - k)) * quadDiffNorm q ∧
      quadDiffNorm q' = surfaceIntegral q fun x z => ENNReal.ofReal (jacobianQD q q' f x z) := by
  exact ⟨s26w_quadDiffNorm_teich hf₀, s26w_quadDiffNorm_qc hf₀.initial hf₀.initial_ne hf₀.terminal hf⟩

/-- **Theorem 26.2 (Teichmüller 唯一性定理)** (26.7).  Let `S₀` and `S` be closed Riemann surfaces of
genus `g > 1` and `f₀ : S₀ → S` a Teichmüller map (dilatation `K[f₀] = (1+k)/(1-k)`).  Then `f₀` is
the unique extremal map of its homotopy class: every `f ∈ [f₀]` satisfies `K[f] ≥ K[f₀]`, with
equality only for `f = f₀`. -/
theorem thm26_2_uniqueness [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁))) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS f ∧
      (maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) → ⇑f = ⇑f₀) := by
  sorry

/-- (26.15)–(26.16) (the equality case of Theorem 26.2): if `K[f] = K[f₀]`, then almost everywhere
`|∂_ξ f̃| = |∂_ζ f̃| + |∂_ζ̄ f̃|` and `K₀ = (1 + |∂_ζ̄ f̃/∂_ζ f̃|)/(1 - |∂_ζ̄ f̃/∂_ζ f̃|)`, so
`∂_ζ̄ f̃/∂_ζ f̃ = k₀ = (K₀-1)/(K₀+1)` is a non-negative real constant: `f` has the same complex
dilatation as `f₀`, `f ∘ f₀⁻¹` is conformal and homotopic to the identity, hence the identity
(Corollary of Theorem 23.1). -/
theorem eq26_15_16 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)))
    (heq : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k))) :
    (∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) ∧
      IsBiholomorphic (f₀.symm.trans f) := by
  sorry

/-- §26.4 (the conformal case, `k = 0`): a conformal map is the unique extremal map in its
homotopy class; a quasiconformal map homotopic to a conformal map `c` with `K[h] = 1` equals `c`. -/
theorem conformal_unique_extremal [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {c h : S₀ ≃ₜ S₁} (hc : IsBiholomorphic c)
    (hh : IsQCRS h) (hhom : ContinuousMap.Homotopic (c : C(S₀, S₁)) (h : C(S₀, S₁)))
    (h1 : maxDilatationRS h = 1) : ⇑h = ⇑c := by
  sorry

/-- §26.4: a Teichmüller map is extremal in its homotopy class (and it is the unique extremal
map there). -/
theorem teichmullerMap_isExtremal [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    IsExtremalInHomotopyClass f ∧ ∀ h : S₀ ≃ₜ S₁, IsExtremalInHomotopyClass h →
      ContinuousMap.Homotopic (f : C(S₀, S₁)) (h : C(S₀, S₁)) → ⇑h = ⇑f := by
  sorry

end LiZhongQC
