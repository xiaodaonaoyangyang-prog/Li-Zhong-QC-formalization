import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Lemmas.Quadrilateral
import LiZhongQC.Lemmas.Mobius
import LiZhongQC.Lemmas.SchwarzChristoffelRect
import LiZhongQC.Lemmas.Caratheodory
import LiZhongQC.Lemmas.JordanBridge
import LiZhongQC.Lemmas.ConnectedComplement
import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.CaratheodoryJordan
import LiZhongQC.RiemannMapping

/-!
# Images of quadrilaterals under conformal maps, and Jordan domains onto the upper half-plane

Bundle 2 of the Theorem 7.2 / Theorem 6.1 support: the image of a `TopQuad` under an injective
continuous open map is again a Jordan domain with a natural `OnePoint.map` extension (`4a`), a
bounded Jordan domain has a conformal map onto `upperHalf` with a homeomorphic extension (`4b`,
via Carathéodory's theorem `caratheodory_jordan_clean` and the Cayley transform), and that
uniformizer can be normalized so that four prescribed boundary points land on finite reals
(`exists_uniformizer_finite_vertices`, used by Theorem 6.1's orientation step).

Also holds the canonical copies of several small helpers shared across bundles (so each has
exactly one definition project-wide): `closure_toExt_image_subset` (moved from
`S07_GeometricDefinition.lean`), `isHomeoExtension_invFunOn` and `isHomeomorphOnto_invFunOn`
(symmetry of `IsHomeoExtension`/`IsHomeomorphOnto` under `Function.invFunOn`), and
`isBounded_of_extInf_notMem_closure_toExt`.
-/

open Complex Set Metric Filter Topology MeasureTheory

noncomputable section

namespace LiZhongQC

/-! ### canonical copies of small helpers shared across bundles -/

/-- If `Q̄ ⊆ D` (in `ℂ̄`) and `f` is continuous on `D`, then the closure of `f(Q)` lies in `f(D)`.
(Canonical copy; moved here from `S07_GeometricDefinition.lean:96`.) -/
theorem closure_toExt_image_subset {f : ℂ → ℂ} {D D' U : Set ℂ} (hf : ContinuousOn f D)
    (hU : closure (toExt U) ⊆ toExt D) (hfD : f '' D ⊆ D') :
    closure (toExt (f '' U)) ⊆ toExt D' := by
  obtain ⟨K, hK_def⟩ : ∃ K : Set ℂ, K = ((↑) : ℂ → ExtPlane) ⁻¹' closure (toExt U) := ⟨_, rfl⟩
  have hKD : K ⊆ D := fun z hz => by
    rw [hK_def] at hz
    obtain ⟨w, hw, hwz⟩ := hU hz
    rw [← OnePoint.coe_injective hwz]
    exact hw
  have hKc : IsCompact K := by
    rw [hK_def]
    exact OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage' isClosed_closure.isCompact
      (hU.trans (image_subset_range _ _))
  have hUK : U ⊆ K := fun z hz => by
    rw [hK_def]
    exact subset_closure (mem_image_of_mem _ hz)
  have himc : IsCompact (((↑) : ℂ → ExtPlane) '' (f '' K)) :=
    (hKc.image_of_continuousOn (hf.mono hKD)).image OnePoint.continuous_coe
  exact (closure_minimal (image_mono (image_mono hUK)) himc.isClosed).trans
    (image_mono ((image_mono hKD).trans hfD))

/-- `IsHomeoExtension` is symmetric under `invFunOn`. (Canonical copy; moved here from the
part-S/thm6_1 work — the `sw_partS_scratch.lean` copy is retired.) -/
theorem isHomeoExtension_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hf : IsConformalOnto f U V) (hF : IsHomeoExtension f U V F) :
    IsHomeoExtension (Function.invFunOn f U) V U (Function.invFunOn F (closure (toExt U))) := by
  obtain ⟨hfd, hfi, hfimg⟩ := hf
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwU : w ∈ f '' U := hfimg ▸ hw
    obtain ⟨z, hz, rfl⟩ := hwU
    have hzmem : ((z : ℂ) : ExtPlane) ∈ closure (toExt U) := subset_closure (mem_image_of_mem _ hz)
    have hFz : F ((z : ℂ) : ExtPlane) = ((f z : ℂ) : ExtPlane) := hF1 z hz
    rw [hfi.leftInvOn_invFunOn hz, ← hFz]
    exact hF3.leftInvOn_invFunOn hzmem
  · rw [← hF4]
    exact continuousOn_invFunOn_of_isClosed isClosed_closure hF2 hF3
  · rw [← hF4]
    intro p hp q hq hpq
    calc p = F (Function.invFunOn F (closure (toExt U)) p) := (Function.invFunOn_eq hp).symm
      _ = F (Function.invFunOn F (closure (toExt U)) q) := by rw [hpq]
      _ = q := Function.invFunOn_eq hq
  · rw [← hF4]
    exact hF3.leftInvOn_invFunOn.image_image

/-- `IsHomeomorphOnto` is symmetric under `invFunOn`. (Canonical copy; moved here from
`s7_2inv_scratch.lean`.) -/
theorem isHomeomorphOnto_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} (hf : IsHomeomorphOnto f U V) :
    IsHomeomorphOnto (Function.invFunOn f U) V U := by
  obtain ⟨hc, hi, himg, hic⟩ := hf
  have hi' : InjOn (Function.invFunOn f U) V := by
    intro p hp q hq hpq
    rw [← himg] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    rw [hi.leftInvOn_invFunOn ha, hi.leftInvOn_invFunOn hb] at hpq
    rw [hpq]
  have himg' : Function.invFunOn f U '' V = U := by
    rw [← himg]; exact hi.leftInvOn_invFunOn.image_image
  have heq : Set.EqOn (Function.invFunOn (Function.invFunOn f U) V) f U := by
    intro z hz
    have hgfz : Function.invFunOn f U (f z) = z := hi.leftInvOn_invFunOn hz
    have hfzV : f z ∈ V := himg ▸ mem_image_of_mem f hz
    have hh := hi'.leftInvOn_invFunOn hfzV
    rw [hgfz] at hh
    exact hh
  exact ⟨hic, hi', himg', hc.congr heq⟩

/-- If `extInf` is not a closure point of `toExt A`, then `A` is bounded. (Canonical copy; moved
here from `s7_2inv_scratch.lean`.) -/
theorem isBounded_of_extInf_notMem_closure_toExt {A : Set ℂ} (h : extInf ∉ closure (toExt A)) :
    Bornology.IsBounded A := by
  rw [mem_closure_iff_nhds] at h
  push Not at h
  obtain ⟨V, hV, hVA⟩ := h
  rw [OnePoint.nhds_infty_eq, Filter.mem_sup] at hV
  obtain ⟨hV1, hV2⟩ := hV
  rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact, Filter.mem_map] at hV1
  have hVc : Bornology.IsBounded (OnePoint.some ⁻¹' V)ᶜ :=
    Bornology.isBounded_compl_iff.mpr hV1
  refine hVc.subset ?_
  intro a ha
  simp only [mem_compl_iff, mem_preimage]
  intro haV
  have : (OnePoint.some a : ExtPlane) ∈ V ∩ toExt A := ⟨haV, ⟨a, ha, rfl⟩⟩
  rw [hVA] at this
  exact this

/-! ### 4a -/

/-- **4a**: the image of a quadrilateral `Q` with `Q̄ ⊆ D` under an injective continuous map
whose image is open is again a Jordan domain, with the natural `OnePoint.map f` extension and
frontier-image formula. Generalizes `TopQuad.exists_image_conformal`'s first half, with openness
of the image supplied as a hypothesis (discharged by the caller: `t3b_isOpenMap` for `IsKQC`,
the inverse-function theorem for `C¹` maps with positive Jacobian, or direct continuity for
`f⁻¹`). -/
theorem image_isJordanDomain_of_open {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {Q : TopQuad}
    (hQ : closure (toExt Q.dom) ⊆ toExt D) (hfo : IsOpen (f '' Q.dom)) :
    IsJordanDomain (f '' Q.dom) ∧
      IsHomeoExtension f Q.dom (f '' Q.dom) (OnePoint.map f) ∧
      frontier (toExt (f '' Q.dom)) = OnePoint.map f '' frontier (toExt Q.dom) := by
  obtain ⟨hJ, hQv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := Q.isTopQuad
  set C := closure (toExt Q.dom) with hC
  set F : ExtPlane → ExtPlane := OnePoint.map f with hF
  have hQo : IsOpen Q.dom := hJ.1
  have hsubD : Q.dom ⊆ D := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hQ (subset_closure (mem_image_of_mem _ hz))
    rw [← OnePoint.coe_injective hwz]
    exact hw
  have htoExt : ∀ S : Set ℂ, F '' toExt S = toExt (f '' S) := fun S => by
    simp only [toExt, image_image]
    rfl
  have hFC : ContinuousOn F C := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := hQ hp
    refine ContinuousAt.continuousWithinAt (OnePoint.continuousAt_coe.2 ?_)
    exact OnePoint.continuous_coe.continuousAt.comp
      (hfc.continuousAt (hD.mem_nhds hz))
  have hFinj : InjOn F C := by
    intro p hp q hq hpq
    obtain ⟨z, hz, rfl⟩ := hQ hp
    obtain ⟨w, hw, rfl⟩ := hQ hq
    rw [hfi hz hw (OnePoint.coe_injective hpq)]
  have hFimg : F '' C = closure (toExt (f '' Q.dom)) := by
    refine subset_antisymm ?_ ?_
    · rw [← htoExt]
      exact hFC.image_closure
    · refine closure_minimal ?_ (isClosed_closure.isCompact.image_of_continuousOn hFC).isClosed
      rw [← htoExt]
      exact image_mono subset_closure
  have hext : IsHomeoExtension f Q.dom (f '' Q.dom) F := ⟨fun z _ => rfl, hFC, hFinj, hFimg⟩
  have hfr : F '' frontier (toExt Q.dom) = frontier (toExt (f '' Q.dom)) :=
    hext.image_frontier hQo hfo rfl
  have hfrC : frontier (toExt Q.dom) ⊆ C := frontier_subset_closure
  have hJD : IsJordanDomain (f '' Q.dom) := by
    refine ⟨hfo, hJ.2.1.image f (hfc.mono hsubD), ?_⟩
    rw [← hfr]
    obtain ⟨γ, hγc, hγi, hγr⟩ := hJ.2.2
    have hγC : ∀ t, γ t ∈ C := fun t => hfrC (hγr ▸ mem_range_self t)
    exact ⟨F ∘ γ, hFC.comp_continuous hγc hγC,
      fun s t hst => hγi (hFinj (hγC s) (hγC t) hst), by rw [range_comp, hγr]⟩
  exact ⟨hJD, hext, hfr.symm⟩

/-! ### 4b -/

/-- **4b step 1**: `IsConnected (toExt Ω)ᶜ` for a bounded Jordan domain `Ω`. -/
theorem isConnected_compl_toExt_of_isJordanDomain {Ω : Set ℂ} (hΩJD : IsJordanDomain Ω)
    (hΩb : Bornology.IsBounded Ω) : IsConnected (toExt Ω)ᶜ := by
  obtain ⟨hΩo, hΩc, hΩJC⟩ := hΩJD
  have hC : IsJordanCurve (toExt (frontier Ω)) := by
    rw [← frontier_toExt_of_isBounded hΩb hΩo]; exact hΩJC
  have hBopen : IsOpen (closure Ω)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨hBconn, hBunbdd⟩ := isConnected_compl_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hC
  have hcl : closure Ω = Ω ∪ frontier Ω := by
    rw [closure_eq_interior_union_frontier, hΩo.interior_eq]
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]; exact Set.disjoint_sdiff_right
  have hAB : Disjoint Ω (closure Ω)ᶜ := fun s hs1 hs2 => by
    exact fun z hz => hs2 hz (subset_closure (hs1 hz))
  have hBC : Disjoint (closure Ω)ᶜ (frontier Ω) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz1 (frontier_subset_closure hz2)
  have huniv : Ω ∪ (closure Ω)ᶜ ∪ frontier Ω = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    by_cases h : z ∈ closure Ω
    · rw [hcl, mem_union] at h
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · exact Or.inl (Or.inr h)
  obtain ⟨-, hBfr⟩ := frontier_pieces_eq_of_jordan_curve_theorem_complex hC hΩo hBopen hΩc
    hBconn hAB hΩfr hBC huniv
  -- `frontier Ω ⊆ closure ((closure Ω)ᶜ)`
  have hfrsub : frontier Ω ⊆ closure ((closure Ω)ᶜ) := hBfr ▸ frontier_subset_closure
  set S : Set ExtPlane := toExt (closure Ω)ᶜ with hSdef
  have hSconn : IsConnected S := hBconn.image _ OnePoint.continuous_coe.continuousOn
  have hS1 : S ⊆ (toExt Ω)ᶜ := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := hp
    intro ⟨w, hw, hwz⟩
    rw [← OnePoint.coe_injective hwz] at hz
    exact hz (subset_closure hw)
  have hS2 : (toExt Ω)ᶜ ⊆ closure S := by
    rw [compl_toExt]
    rintro p (⟨z, hz, rfl⟩ | rfl)
    · have hzΩc : z ∈ Ωᶜ := hz
      by_cases hzcl : z ∈ closure Ω
      · rw [hcl] at hzcl
        rcases hzcl with h | h
        · exact absurd h hzΩc
        · have : ((z : ℂ) : ExtPlane) ∈ toExt (frontier Ω) := mem_image_of_mem _ h
          have hsub2 : toExt (frontier Ω) ⊆ closure S := by
            rw [hSdef]
            calc toExt (frontier Ω) ⊆ toExt (closure (closure Ω)ᶜ) := image_mono hfrsub
              _ ⊆ closure (toExt (closure Ω)ᶜ) :=
                OnePoint.continuous_coe.continuousOn.image_closure
          exact hsub2 this
      · exact subset_closure ⟨z, hzcl, rfl⟩
    · exact extInf_mem_closure_toExt_compl_of_isBounded hΩb.closure
  exact hSconn.subset_closure hS1 hS2

/-- The Cayley transform `iq_cayley z = (z - i)/(z + i)`, upper half-plane to unit disc. -/
def iq_cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `iq_cayleyInv w = i(1 + w)/(1 - w)`. -/
def iq_cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem iq_cayley_den_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro hcon
  have him := congrArg Complex.im hcon
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem iq_cayleyInv_den_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro hcon
  rw [show w = 1 by linear_combination -hcon] at hw
  simp at hw

theorem iq_cayleyInv_mem_upperHalf {w : ℂ} (hw : ‖w‖ < 1) : iq_cayleyInv w ∈ upperHalf := by
  have hden := iq_cayleyInv_den_ne_zero hw
  have hpos : 0 < normSq (1 - w) := normSq_pos.mpr hden
  have hws : normSq w < 1 := normSq_lt_one_iff.mpr hw
  have hval : (iq_cayleyInv w).im = (1 - normSq w) / normSq (1 - w) := by
    rw [iq_cayleyInv, Complex.div_im]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      normSq_apply]
    field_simp
    ring
  show 0 < (iq_cayleyInv w).im
  rw [hval]
  exact div_pos (by linarith) hpos

theorem iq_cayley_cayleyInv {w : ℂ} (hw : ‖w‖ < 1) : iq_cayley (iq_cayleyInv w) = w := by
  have hden := iq_cayleyInv_den_ne_zero hw
  have h1 : iq_cayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [iq_cayleyInv]; field_simp; ring
  have h2 : iq_cayleyInv w + I = I * 2 / (1 - w) := by
    rw [iq_cayleyInv]; field_simp; ring
  have h2ne : iq_cayleyInv w + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [iq_cayley, div_eq_iff h2ne, h1, h2]
  field_simp

theorem iq_cayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : iq_cayleyInv (iq_cayley z) = z := by
  have hden := iq_cayley_den_ne_zero hz
  have h1 : (1 : ℂ) + iq_cayley z = 2 * z / (z + I) := by
    rw [iq_cayley]; field_simp; ring
  have h2 : (1 : ℂ) - iq_cayley z = 2 * I / (z + I) := by
    rw [iq_cayley]; field_simp; ring
  have h2ne : (1 : ℂ) - iq_cayley z ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [iq_cayleyInv, div_eq_iff h2ne, h1, h2]
  field_simp

theorem iq_cayley_mem_unitDisc {z : ℂ} (hz : 0 < z.im) : iq_cayley z ∈ unitDisc := by
  have hden := iq_cayley_den_ne_zero hz
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  have hlt : normSq (z - I) < normSq (z + I) := by
    have h : normSq (z + I) - normSq (z - I) = 4 * z.im := by
      simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.I_re, Complex.I_im]
      ring
    linarith
  rw [unitDisc, mem_ball_zero_iff, ← normSq_lt_one_iff, iq_cayley, normSq_div, div_lt_one hpos]
  exact hlt

/-- **4b**: a bounded Jordan domain has a conformal map onto `upperHalf`, with a homeomorphic
extension. -/
theorem exists_conformalOnto_upperHalf_of_isJordanDomain {Ω : Set ℂ} (hΩJD : IsJordanDomain Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ f : ℂ → ℂ, IsConformalOnto f Ω upperHalf ∧
      ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f Ω upperHalf F := by
  obtain ⟨hΩo, hΩc, hΩJC⟩ := hΩJD
  have hΩne : Ωᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hΩb.subset_closedBall (0 : ℂ)
    set R' : ℝ := max R 0 with hR'def
    refine ⟨(((R' + 1 : ℝ)) : ℂ), fun hmem => ?_⟩
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ R' + 1)] at h1
    have : R ≤ R' := le_max_left _ _
    linarith
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  have hH : RMT.HasHolomorphicSqrt Ω :=
    hasHolomorphicSqrt_of_isConnected_compl hΩo hΩc
      (isConnected_compl_toExt_of_isJordanDomain ⟨hΩo, hΩc, hΩJC⟩ hΩb)
  obtain ⟨g, hgcomp, hgbij⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hΩo hΩc hΩne hH hz₀
  have hgbij' : BijOn g Ω unitDisc := hgbij
  obtain ⟨hfdiff, hfbij⟩ :=
    RMT.invFunOn_riemannMap hΩo hgcomp.diff hgcomp.injOn hgbij
  set f : ℂ → ℂ := Function.invFunOn g Ω with hfdef
  have hfbij' : BijOn f unitDisc Ω := hfbij
  have hfconf : IsConformalOnto f unitDisc Ω := ⟨hfdiff, hfbij'.injOn, hfbij'.image_eq⟩
  obtain ⟨F, hF1, hF2, hF3, hF4⟩ := caratheodory_jordan_clean hΩb hfconf hΩJC
  -- invert `F` to get `g`'s own extension `Ω → unitDisc`
  have hfinj : InjOn f unitDisc := hfbij'.injOn
  have hgU : MapsTo g Ω unitDisc := hgbij'.mapsTo
  have hGext : IsHomeoExtension g Ω unitDisc (Function.invFunOn F (closure (toExt unitDisc))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      have hgzmem : ((g z : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) :=
        subset_closure (mem_image_of_mem _ (hgU hz))
      have hFgz : F ((g z : ℂ) : ExtPlane) = ((z : ℂ) : ExtPlane) := by
        rw [hF1 (g z) (hgU hz)]
        congr 1
        exact hgbij'.injOn.leftInvOn_invFunOn hz
      rw [← hFgz]
      exact hF3.leftInvOn_invFunOn hgzmem
    · rw [← hF4]
      exact continuousOn_invFunOn_of_isClosed isClosed_closure hF2 hF3
    · rw [← hF4]
      intro p hp q hq hpq
      calc p = F (Function.invFunOn F (closure (toExt unitDisc)) p) :=
            (Function.invFunOn_eq hp).symm
        _ = F (Function.invFunOn F (closure (toExt unitDisc)) q) := by rw [hpq]
        _ = q := Function.invFunOn_eq hq
    · rw [← hF4]
      exact hF3.leftInvOn_invFunOn.image_image
  set e : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph I I (-1) 1 scExt_cayley_det with hedef
  have he : ∀ w ∈ unitDisc, e (w : ExtPlane) = ((iq_cayleyInv w : ℂ) : ExtPlane) := fun w hw => by
    have hw1 : (-1 : ℂ) * w + 1 ≠ 0 := by
      intro h
      have : w = 1 := by linear_combination -h
      rw [this] at hw
      simp [unitDisc] at hw
    show mobiusExt I I (-1) 1 (w : ExtPlane) = _
    rw [mobiusExt_coe hw1]
    congr 1
    show (I * w + I) / (-1 * w + 1) = iq_cayleyInv w
    rw [iq_cayleyInv]; ring
  have himg : e '' toExt unitDisc = toExt upperHalf := scExt_cayley_image_disc
  have hextcomp := IsHomeoExtension.comp_homeomorph hGext hgU e he himg
  have hconfcomp : IsConformalOnto (iq_cayleyInv ∘ g) Ω upperHalf := by
    have hcayleyInvConf : IsConformalOnto iq_cayleyInv unitDisc upperHalf := by
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have hw1 : (1 : ℂ) - w ≠ 0 := iq_cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
        have hdiff : DifferentiableAt ℂ iq_cayleyInv w := by
          have h1 : DifferentiableAt ℂ (fun w : ℂ => I * (1 + w)) w :=
            (differentiableAt_const I).mul ((differentiableAt_const (1:ℂ)).add differentiableAt_id)
          have h2 : DifferentiableAt ℂ (fun w : ℂ => (1:ℂ) - w) w :=
            (differentiableAt_const (1:ℂ)).sub differentiableAt_id
          exact h1.div h2 hw1
        exact hdiff.differentiableWithinAt
      · intro w hw v hv heq
        have hw' := iq_cayley_cayleyInv (mem_ball_zero_iff.mp hw)
        have hv' := iq_cayley_cayleyInv (mem_ball_zero_iff.mp hv)
        rw [← hw', ← hv', heq]
      · ext w
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact iq_cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hv)
        · intro hw
          exact ⟨iq_cayley w, iq_cayley_mem_unitDisc hw, iq_cayleyInv_cayley hw⟩
    exact IsConformalOnto.comp hcayleyInvConf ⟨hgcomp.diff, hgbij'.injOn, hgbij'.image_eq⟩
  exact ⟨iq_cayleyInv ∘ g, hconfcomp, e ∘ Function.invFunOn F (closure (toExt unitDisc)), hextcomp⟩

/-! ### normalize a uniformizer so four boundary points land on finite reals -/

/-- normalize a uniformizer so four boundary points land on finite reals. (Canonical copy; moved
here from `s7_2inv_scratch.lean`.) -/
theorem exists_uniformizer_finite_vertices {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    {Φ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ Ω upperHalf)
    (hΦ : IsHomeoExtension φ Ω upperHalf Φ) {v : Fin 4 → ExtPlane}
    (hv : ∀ i, v i ∈ frontier (toExt Ω)) :
    ∃ (ψ : ℂ → ℂ) (Ψ : ExtPlane → ExtPlane) (x : Fin 4 → ℝ),
      IsConformalOnto ψ Ω upperHalf ∧ IsHomeoExtension ψ Ω upperHalf Ψ ∧
        ∀ i, Ψ (v i) = (((x i : ℝ) : ℂ) : ExtPlane) := by
  classical
  have hΦfr : Φ '' frontier (toExt Ω) = frontier (toExt upperHalf) :=
    IsHomeoExtension.image_frontier hΩ scExt_isOpen_upperHalf hφ.2.2 hΦ
  have hΦv : ∀ i, Φ (v i) ∈ frontier (toExt upperHalf) := fun i =>
    hΦfr ▸ mem_image_of_mem Φ (hv i)
  rw [scExt_frontier_toExt_upperHalf] at hΦv
  have hcases : ∀ i, (∃ t : ℝ, Φ (v i) = ((t : ℂ) : ExtPlane)) ∨ Φ (v i) = extInf := by
    intro i
    rcases hΦv i with h | h
    · obtain ⟨z, hz, hzeq⟩ := h
      left
      refine ⟨z.re, ?_⟩
      rw [← hzeq]
      congr 1
      exact Complex.ext_iff.2 ⟨rfl, hz⟩
    · right; exact h
  set t : Fin 4 → ℝ := fun i => if h : ∃ s : ℝ, Φ (v i) = ((s : ℂ) : ExtPlane) then h.choose else 0
    with htdef
  have htspec : ∀ i, Φ (v i) ≠ extInf → Φ (v i) = ((t i : ℂ) : ExtPlane) := by
    intro i hne
    have hex : ∃ s : ℝ, Φ (v i) = ((s : ℂ) : ExtPlane) := (hcases i).resolve_right hne
    rw [htdef]
    simp only [dif_pos hex]
    exact hex.choose_spec
  set r : ℝ := 1 + ∑ i, |t i| with hrdef
  have hrne : ∀ i, t i ≠ r := by
    intro i hti
    have h1 : |t i| ≤ ∑ j, |t j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    have h2 : t i ≤ |t i| := le_abs_self _
    rw [hrdef] at hti
    linarith
  have hdet : (0:ℝ) * (-r) - (-1) * (1:ℝ) = 1 := by ring
  have hdetpos : (0:ℝ) < (0:ℝ) * (-r) - (-1) * (1:ℝ) := by rw [hdet]; norm_num
  have hMconf : IsConformalOnto (mobiusFn ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ))
      upperHalf upperHalf := isConformalOnto_mobius_upperHalf hdetpos
  have hdetC : ((0:ℝ):ℂ) * ((-r:ℝ):ℂ) - ((-1:ℝ):ℂ) * ((1:ℝ):ℂ) ≠ 0 := by
    have h0 : ((0:ℝ) * (-r) - (-1) * (1:ℝ) : ℝ) ≠ 0 := hdetpos.ne'
    exact_mod_cast h0
  set e : ExtPlane ≃ₜ ExtPlane :=
    mobiusHomeomorph ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ) hdetC with hedef
  have heapp : ∀ w : ExtPlane, e w = mobiusExt ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ) w :=
    fun w => rfl
  have he : ∀ w ∈ upperHalf, e (w : ExtPlane) =
      ((mobiusFn ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ) w : ℂ) : ExtPlane) := fun w hw => by
    rw [heapp]
    exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetpos.ne' hw)
  have himg : e '' toExt upperHalf = toExt upperHalf := mobiusExt_image_toExt_upperHalf hdetpos
  set ψ : ℂ → ℂ := mobiusFn ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ) ∘ φ with hψdef
  set Ψ : ExtPlane → ExtPlane := e ∘ Φ with hΨdef
  have hψconf : IsConformalOnto ψ Ω upperHalf := IsConformalOnto.comp hMconf hφ
  have hΨext : IsHomeoExtension ψ Ω upperHalf Ψ :=
    IsHomeoExtension.comp_homeomorph hΦ hφ.mapsTo e he himg
  have hfinal : ∀ i, ∃ s : ℝ, Ψ (v i) = ((s : ℂ) : ExtPlane) := by
    intro i
    have hΨeq : Ψ (v i) = e (Φ (v i)) := rfl
    by_cases h : Φ (v i) = extInf
    · refine ⟨0, ?_⟩
      rw [hΨeq, h, heapp, mobiusExt_infty_of_ne (show ((1:ℝ):ℂ) ≠ 0 by norm_num)]
      norm_num
    · obtain ⟨s, hs⟩ : ∃ s : ℝ, Φ (v i) = ((s : ℂ) : ExtPlane) := (hcases i).resolve_right h
      have hst : s = t i := by
        have heq := hs.symm.trans (htspec i h)
        have heq2 := OnePoint.coe_injective heq
        exact_mod_cast heq2
      have hsr : s ≠ r := hst ▸ hrne i
      have hdeneq : ((1:ℝ):ℂ) * ((s:ℝ):ℂ) + ((-r:ℝ):ℂ) = ((s - r : ℝ):ℂ) := by push_cast; ring
      have hden : ((1:ℝ):ℂ) * ((s:ℝ):ℂ) + ((-r:ℝ):ℂ) ≠ 0 := by
        rw [hdeneq]
        exact_mod_cast sub_ne_zero.mpr hsr
      refine ⟨(0 * s + (-1)) / (1 * s + (-r)), ?_⟩
      rw [hΨeq, hs, heapp, mobiusExt_coe hden]
      congr 1
      show mobiusFn ((0:ℝ):ℂ) ((-1:ℝ):ℂ) ((1:ℝ):ℂ) ((-r:ℝ):ℂ) ((s:ℝ):ℂ) =
        (((0 * s + (-1)) / (1 * s + (-r)) : ℝ) : ℂ)
      rw [mobiusFn]
      push_cast
      ring
  choose x hx using hfinal
  exact ⟨ψ, Ψ, x, hψconf, hΨext, hx⟩

end LiZhongQC
