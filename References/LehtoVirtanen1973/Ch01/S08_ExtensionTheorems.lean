import References.LehtoVirtanen1973.Ch01.S07_RingCharacterization
import LiZhongQC.Ch04.S16_Quasicircles

/-!
# Lehto–Virtanen, Chapter I §8: Extension theorems for quasiconformal mappings

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §8
(pp. 41–47; `full.md` P1:1137–1304).

Circular arcs are arcs of generalized circles of `ℂ̄`, i.e. images of the extended real line
`LiZhongQC.extRealLine` under linear (Möbius) transformations; the reflection in such a circle is the conjugate of
`z ↦ z̄` by the transformation.

* Definition (isolated boundary point; removable singularity, §8.1) — `IsIsolatedBoundaryPoint`,
  `IsRemovableSingularity`
* Theorem 8.1 (§8.1) — `thm1_8_1`
* Unlabelled (§8.1, P1:1169, Remark): quasiconformal and conformal mappings divide simply connected domains into
  the same equivalence classes — `qcEquivalent_iff_conformalEquivalent`
* Theorem 8.2 (§8.2) — `thm1_8_2`
* Definition (maximal dilatation `K(G)` for an open set `G`, §8.3) — exists:
  `LehtoVirtanen1973.maxDilatationK` (defined for every set in §3)
* Theorem 8.3 (§8.3) — `thm1_8_3`
* Definition (circular arc; reflection in a circular arc; "`G` can be reflected in `C`", §8.4) — `IsGenCircle`,
  `genCircleReflection`, `IsCircularArc`, `CanReflectIn`
* Reflection principle (§8.4) — `reflection_principle`

The claim of the remark after Theorem 8.1 is stated because it is cited later (P1:2531, 6031); the immediate
"`G ∪ C ∪ G*` is a domain" (P1:1285) and "`G ∪ {z₀}` is then a domain" (P1:1141) are not stated.
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §8.1 Isolated boundary points -/

/-- **Definition** (isolated boundary point, Ch. I §8.1). A boundary point `z₀` of `G` having a neighbourhood which
consists entirely of points of `G`, apart from `z₀` itself. -/
def IsIsolatedBoundaryPoint (G : Set ExtPlane) (z₀ : ExtPlane) : Prop :=
  z₀ ∈ frontier G ∧ ∃ U ∈ 𝓝 z₀, U \ {z₀} ⊆ G

/-- **Definition** (removable singularity, Ch. I §8.1). The isolated boundary point `z₀` of `G` is a removable
singularity of the `K`-quasiconformal mapping `w` of `G` if `w` can be extended to a `K`-quasiconformal mapping of
`G ∪ {z₀}`. -/
def IsRemovableSingularity (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (K : ℝ) (z₀ : ExtPlane) : Prop :=
  ∃ W : ExtPlane → ExtPlane, EqOn W w G ∧ IsKQuasiconformal W (insert z₀ G) K

/-- **Theorem 8.1** (Ch. I §8.1). The isolated boundary points of a domain `G` are removable singularities of every
`K`-quasiconformal mapping of `G`. -/
theorem thm1_8_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    {z₀ : ExtPlane} (hz₀ : IsIsolatedBoundaryPoint G z₀) : IsRemovableSingularity w G K z₀ := by
  sorry

/-- **Unlabelled** (Ch. I §8.1, P1:1169, Remark). Quasiconformal and conformal mappings divide simply connected
domains into the same equivalence classes: two simply connected domains are quasiconformally equivalent if and
only if they are conformally equivalent. -/
theorem qcEquivalent_iff_conformalEquivalent {G G' : Set ExtPlane} (hG : IsSimplyConnectedDomain G)
    (hG' : IsSimplyConnectedDomain G') :
    (∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G ∧ w '' G = G') ↔
      ∃ f : ExtPlane → ExtPlane, IsConformalMap f G ∧ f '' G = G' := by
  sorry

/-! ## §8.2 Extension to free boundary arcs -/

/-- **Theorem 8.2** (Ch. I §8.2). Let `G` and `G′` be two domains, `C` and `C′` free boundary arcs or curves of `G`
and `G′`, and `w : G → G′` a quasiconformal mapping. If `C` and `C′` correspond under `w`, then `w` can be extended to
a homeomorphism of `G ∪ C` onto `G′ ∪ C′`. -/
theorem thm1_8_2 {w : ExtPlane → ExtPlane} {G G' C C' : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hwG : w '' G = G') (hC : IsFreeBoundaryArc G C ∨ IsFreeBoundaryCurve G C)
    (hC' : IsFreeBoundaryArc G' C' ∨ IsFreeBoundaryCurve G' C') (hcorr : Corresponds w G G' C C') :
    ∃ W : ExtPlane → ExtPlane, EqOn W w G ∧ IsHomeoOn W (G ∪ C) (G' ∪ C') := by
  sorry

/-! ## §8.3 Removability of an analytic arc -/

/-- **Theorem 8.3** (Ch. I §8.3, Ahlfors). Let `w` be a homeomorphism of a domain `G` and `C` a closed analytic arc
which lies in `G` with the possible exception of its end points. For the maximal dilatation of `w` we then have
`K(G) = K(G \ C)`.
Modelling: `w` is assumed sense-preserving; the maximal dilatation `K(·)` is defined in §3.1 only for sense-preserving
homeomorphisms (P1:371). -/
theorem thm1_8_3 {w : ExtPlane → ExtPlane} {G C : Set ExtPlane} {p q : ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (hC : IsAnalyticClosedArcFromTo C p q) (hCG : C \ {p, q} ⊆ G) :
    maxDilatationK w G = maxDilatationK w (G \ C) := by
  sorry

/-! ## §8.4 Reflection principle -/

/-- **Definition** (circle of `ℂ̄`, Ch. I §8.4): a circle, or the image of a circle under a linear transformation
(lines included): the image of the extended real line under a Möbius transformation. -/
def IsGenCircle (Γ : Set ExtPlane) : Prop := ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ Γ = M '' LiZhongQC.extRealLine

open scoped Classical in
/-- **Definition** (reflection `z ↦ z*` in a circle `Γ`, Ch. I §8.4): `M ∘ conj ∘ M⁻¹` for a Möbius `M` carrying
the extended real line onto `Γ` (the map does not depend on the choice of `M`; a choice is made). Junk: the identity
if `Γ` is not a circle. -/
def genCircleReflection (Γ : Set ExtPlane) : ExtPlane → ExtPlane :=
  if h : ∃ m : Fin 4 → ℂ, m 0 * m 3 - m 1 * m 2 ≠ 0 ∧
      Γ = LiZhongQC.mobiusExt (m 0) (m 1) (m 2) (m 3) '' LiZhongQC.extRealLine then
    LiZhongQC.mobiusExt (h.choose 0) (h.choose 1) (h.choose 2) (h.choose 3) ∘ OnePoint.map (starRingEnd ℂ) ∘
      LiZhongQC.mobiusExt (h.choose 3) (-h.choose 1) (-h.choose 2) (h.choose 0)
  else id

/-- **Definition** (circular arc, Ch. I §8.4): an open arc of a circle, a full circle, or their images under a linear
transformation. -/
def IsCircularArc (C : Set ExtPlane) : Prop :=
  ∃ Γ, IsGenCircle Γ ∧ (C = Γ ∨ (IsOpenJordanArc C ∧ C ⊆ Γ))

/-- **Definition** (Ch. I §8.4). The domain `G` can be reflected in the circular arc `C` (lying on the circle `Γ`):
1° `C` is a free boundary arc (or curve) of `G`; 2° `G` has no common points with the domain `G*` obtained from `G` by
reflection in `C`. -/
def CanReflectIn (G C Γ : Set ExtPlane) : Prop :=
  IsGenCircle Γ ∧ (C = Γ ∨ (IsOpenJordanArc C ∧ C ⊆ Γ)) ∧ (IsFreeBoundaryArc G C ∨ IsFreeBoundaryCurve G C) ∧
    Disjoint G (genCircleReflection Γ '' G)

/-- Helper (Tier B, B3). The reflection `z ↦ z̄` of `ℂ̄` (fixing `∞`) is a homeomorphism; it is an involution and
fixes the extended real line pointwise. -/
theorem lv18_conj_homeo :
    ∃ h : ExtPlane ≃ₜ ExtPlane, ⇑h = OnePoint.map (starRingEnd ℂ) ∧
      (∀ q, OnePoint.map (starRingEnd ℂ) (OnePoint.map (starRingEnd ℂ) q) = q) ∧
      ∀ q ∈ LiZhongQC.extRealLine, OnePoint.map (starRingEnd ℂ) q = q := by
  refine ⟨Complex.conjCLE.toHomeomorph.onePointCongr, ?_, fun q => ?_, ?_⟩
  · funext q
    induction q using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  · induction q using OnePoint.rec with
    | infty => rfl
    | coe z => exact congrArg _ (Complex.conj_conj z)
  · rintro q (⟨u, hu, rfl⟩ | hq)
    · exact congrArg _ (Complex.conj_eq_iff_im.2 hu)
    · rw [mem_singleton_iff.1 hq]
      rfl

/-- Helper (Tier B, B3). Every point `x` of the extended real line has arbitrarily small open neighbourhoods `B`
which are symmetric under `z ↦ z̄`, whose upper half `B ∩ {Im z > 0}` is connected, and whose real points are limits of
that upper half: discs about finite points, and `{|z| > R} ∪ {∞}` about `∞`. -/
theorem lv18_good_nhds {x : ExtPlane} (hx : x ∈ LiZhongQC.extRealLine) {N : Set ExtPlane} (hN : N ∈ 𝓝 x) :
    ∃ B ⊆ N, IsOpen B ∧ x ∈ B ∧ IsPreconnected (B ∩ toExt {z : ℂ | 0 < z.im}) ∧
      (∀ y ∈ B, OnePoint.map (starRingEnd ℂ) y ∈ B) ∧
      B ∩ LiZhongQC.extRealLine ⊆ closure (B ∩ toExt {z : ℂ | 0 < z.im}) := by
  -- a finite real point of an open set `B` is a limit of points of `B` in the upper half-plane
  have hlim : ∀ (B : Set ExtPlane) (u : ℂ), IsOpen B → (u : ExtPlane) ∈ B → u.im = 0 →
      (u : ExtPlane) ∈ closure (B ∩ toExt {z : ℂ | 0 < z.im}) := by
    intro B u hB hu hu0
    have h0 : Continuous (fun t : ℝ => (u + t * I : ℂ)) := by fun_prop
    have ht : Tendsto (fun t : ℝ => ((u + t * I : ℂ) : ExtPlane)) (𝓝[>] 0) (𝓝 (u : ExtPlane)) := by
      have h1 : Tendsto (fun t : ℝ => (u + t * I : ℂ)) (𝓝[>] 0) (𝓝 u) := by
        simpa using (h0.tendsto 0).mono_left nhdsWithin_le_nhds
      exact (OnePoint.continuous_coe.tendsto u).comp h1
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [ht.eventually (hB.mem_nhds hu), self_mem_nhdsWithin] with t h1 h2
    refine ⟨h1, u + t * I, ?_, rfl⟩
    show 0 < (u + t * I).im
    simpa [hu0] using h2
  rcases hx with ⟨a, ha, rfl⟩ | hx
  · -- a finite real point: discs
    have ha0 : a.im = 0 := ha
    have hN' : ((↑) : ℂ → ExtPlane) ⁻¹' N ∈ 𝓝 a := OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hN
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN'
    have hBo : IsOpen (toExt (Metric.ball a r)) := OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
    refine ⟨toExt (Metric.ball a r), ?_, hBo, ⟨a, Metric.mem_ball_self hr, rfl⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact hball hu
    · have h : toExt (Metric.ball a r) ∩ toExt {z : ℂ | 0 < z.im} =
          ((↑) : ℂ → ExtPlane) '' (Metric.ball a r ∩ {z : ℂ | 0 < z.im}) :=
        (image_inter OnePoint.coe_injective).symm
      rw [h]
      have hcv : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_gt Complex.imLm.isLinear 0
      exact ((convex_ball a r).inter hcv).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(starRingEnd ℂ) u, ?_, rfl⟩
      rw [Metric.mem_ball, ← Complex.conj_eq_iff_im.2 ha0, Complex.dist_conj_conj]
      exact hu
    · rintro _ ⟨⟨u, hu, rfl⟩, hR⟩
      refine hlim _ u hBo ⟨u, hu, rfl⟩ ?_
      rcases hR with ⟨v, hv, hvu⟩ | h
      · rw [← OnePoint.coe_injective hvu]
        exact hv
      · exact absurd h (OnePoint.coe_ne_infty u)
  · -- the point `∞`: exteriors of discs
    rw [mem_singleton_iff.1 hx] at hN ⊢
    obtain ⟨s, ⟨-, hs⟩, hsN⟩ := (OnePoint.hasBasis_nhds_infty.1 N).1 hN
    obtain ⟨R₀, hR₀⟩ := hs.isBounded.subset_closedBall 0
    set R : ℝ := max R₀ 1 with hR_def
    have hR1 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hBmem : ∀ z : ℂ, (z : ExtPlane) ∈ (((↑) : ℂ → ExtPlane) '' Metric.closedBall 0 R)ᶜ ↔ R < ‖z‖ := by
      intro z
      rw [mem_compl_iff, OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall, dist_zero_right, not_le]
    have hBo : IsOpen (((↑) : ℂ → ExtPlane) '' Metric.closedBall 0 R)ᶜ :=
      ((isCompact_closedBall 0 R).image OnePoint.continuous_coe).isClosed.isOpen_compl
    have hinf : extInf ∈ (((↑) : ℂ → ExtPlane) '' Metric.closedBall 0 R)ᶜ := by
      rintro ⟨z, -, hz⟩
      exact OnePoint.coe_ne_infty z hz
    refine ⟨_, ?_, hBo, hinf, ?_, ?_, ?_⟩
    · intro q hq
      induction q using OnePoint.rec with
      | infty => exact hsN (Or.inr rfl)
      | coe z =>
        refine hsN (Or.inl ⟨z, fun hz => ?_, rfl⟩)
        have h1 := (hBmem z).1 hq
        have h2 := hR₀ hz
        rw [Metric.mem_closedBall, dist_zero_right] at h2
        linarith [le_max_left R₀ 1]
    · -- the upper half is the image of a half disc under `w ↦ -1/w`
      have hS : (((↑) : ℂ → ExtPlane) '' Metric.closedBall 0 R)ᶜ ∩ toExt {z : ℂ | 0 < z.im} =
          ((↑) : ℂ → ExtPlane) '' ((fun w : ℂ => -w⁻¹) '' (Metric.ball 0 R⁻¹ ∩ {z : ℂ | 0 < z.im})) := by
        have hkey : ∀ w : ℂ, 0 < w.im → 0 < (-w⁻¹).im ∧ ‖-w⁻¹‖ = ‖w‖⁻¹ := by
          intro w hw
          have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
          refine ⟨?_, by rw [norm_neg, norm_inv]⟩
          rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
          exact div_pos hw (Complex.normSq_pos.2 hw0)
        ext q
        constructor
        · rintro ⟨hq1, z, hz, rfl⟩
          have hzR := (hBmem z).1 hq1
          have hz0 : (0 : ℝ) < ‖z‖ := hR1.trans hzR
          obtain ⟨h1, h2⟩ := hkey z hz
          refine ⟨z, ⟨-z⁻¹, ⟨?_, h1⟩, ?_⟩, rfl⟩
          · rw [Metric.mem_ball, dist_zero_right, h2]
            exact (inv_lt_inv₀ hz0 hR1).2 hzR
          · show -(-z⁻¹)⁻¹ = z
            rw [inv_neg, inv_inv, neg_neg]
        · rintro ⟨_, ⟨w, ⟨hw1, hw2⟩, rfl⟩, rfl⟩
          have hw2' : (0 : ℝ) < w.im := hw2
          obtain ⟨h1, h2⟩ := hkey w hw2'
          rw [Metric.mem_ball, dist_zero_right] at hw1
          have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 fun h => by
            rw [h, Complex.zero_im] at hw2'
            exact lt_irrefl 0 hw2'
          refine ⟨(hBmem _).2 ?_, -w⁻¹, h1, rfl⟩
          rw [h2]
          exact (lt_inv_comm₀ hw0 hR1).1 hw1
      rw [hS]
      have hcv : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_gt Complex.imLm.isLinear 0
      have hT := ((convex_ball (0 : ℂ) R⁻¹).inter hcv).isPreconnected
      refine (hT.image _ fun w hw => ?_).image _ OnePoint.continuous_coe.continuousOn
      have hw0 : w ≠ 0 := fun h => by
        have h2 : (0 : ℝ) < w.im := hw.2
        rw [h, Complex.zero_im] at h2
        exact lt_irrefl 0 h2
      exact (continuousAt_inv₀ hw0).neg.continuousWithinAt
    · intro q hq
      induction q using OnePoint.rec with
      | infty => exact hinf
      | coe z =>
        refine (hBmem _).2 ?_
        show R < ‖(starRingEnd ℂ) z‖
        rw [Complex.norm_conj]
        exact (hBmem z).1 hq
    · rintro q ⟨hq, hqR⟩
      induction q using OnePoint.rec with
      | infty =>
        rw [mem_closure_iff_nhds]
        intro t ht
        obtain ⟨s', ⟨-, hs'⟩, hst⟩ := (OnePoint.hasBasis_nhds_infty.1 t).1 ht
        obtain ⟨R', hR'⟩ := hs'.isBounded.subset_closedBall 0
        set ρ : ℝ := max R R' + 1 with hρ
        have hρpos : 0 < ρ := by linarith [le_max_left R R']
        have hnorm : ‖((ρ : ℂ) * I)‖ = ρ := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
        refine ⟨(((ρ : ℂ) * I : ℂ) : ExtPlane), hst (Or.inl ⟨(ρ : ℂ) * I, fun h => ?_, rfl⟩),
          (hBmem _).2 ?_, (ρ : ℂ) * I, ?_, rfl⟩
        · have h2 := hR' h
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at h2
          linarith [le_max_right R R']
        · rw [hnorm]
          linarith [le_max_left R R']
        · show 0 < ((ρ : ℂ) * I).im
          simpa using hρpos
      | coe z =>
        refine hlim _ z hBo hq ?_
        rcases hqR with ⟨v, hv, hvu⟩ | h
        · rw [← OnePoint.coe_injective hvu]
          exact hv
        · exact absurd h (OnePoint.coe_ne_infty z)

/-- Helper (Tier B, B3). For a circle `Γ` of `ℂ̄` the reflection `genCircleReflection Γ` is `e ∘ z̄ ∘ e⁻¹`, where `e`
is the fractional linear transformation chosen in the definition: a homeomorphism of `ℂ̄`, with fractional linear
inverse, carrying the extended real line onto `Γ`. -/
theorem lv18_reflection_eq {Γ : Set ExtPlane} (hΓ : IsGenCircle Γ) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, IsMobius ⇑e ∧ IsMobius ⇑e.symm ∧ Γ = e '' LiZhongQC.extRealLine ∧
      genCircleReflection Γ = ⇑e ∘ OnePoint.map (starRingEnd ℂ) ∘ ⇑e.symm := by
  have h : ∃ m : Fin 4 → ℂ, m 0 * m 3 - m 1 * m 2 ≠ 0 ∧
      Γ = LiZhongQC.mobiusExt (m 0) (m 1) (m 2) (m 3) '' LiZhongQC.extRealLine := by
    obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, hΓM⟩ := hΓ
    exact ⟨![a, b, c, d], hdet, hΓM⟩
  obtain ⟨hdet, hΓm⟩ := h.choose_spec
  have hM : IsMobius (LiZhongQC.mobiusExt (h.choose 0) (h.choose 1) (h.choose 2) (h.choose 3)) :=
    ⟨_, _, _, _, hdet, rfl⟩
  obtain ⟨e, he, hes⟩ := lv15_mobius_homeomorph hM
  have hinv : LiZhongQC.mobiusExt (h.choose 3) (-h.choose 1) (-h.choose 2) (h.choose 0) = ⇑e.symm := by
    funext q
    have h1 := LiZhongQC.mobiusExt_inv_apply hdet (e.symm q)
    rwa [← he, Homeomorph.apply_symm_apply] at h1
  refine ⟨e, he ▸ hM, hes, he ▸ hΓm, ?_⟩
  unfold genCircleReflection
  split
  · rw [he, hinv]
  · contradiction

/-- Helper (Tier B, B3). Normalization of a reflectable domain: if `G` can be reflected in `C ⊆ Γ`, `Γ = e(ℝ̄)` and
the reflection in `Γ` is `e ∘ z̄ ∘ e⁻¹`, then `C₀ = e⁻¹(C)` is a nonempty free boundary set of `G₀ = e⁻¹(G)` on the
extended real line, and `G₀` is disjoint from its mirror image `z̄(G₀)`. -/
theorem lv18_normalize {G C Γ : Set ExtPlane} (hG : CanReflectIn G C Γ) (e : ExtPlane ≃ₜ ExtPlane)
    (hΓ : Γ = e '' LiZhongQC.extRealLine)
    (hR : genCircleReflection Γ = ⇑e ∘ OnePoint.map (starRingEnd ℂ) ∘ ⇑e.symm) :
    e.symm '' C ⊆ LiZhongQC.extRealLine ∧ (e.symm '' C).Nonempty ∧ e.symm '' C ⊆ frontier (e.symm '' G) ∧
      Disjoint (e.symm '' C) (closure (frontier (e.symm '' G) \ e.symm '' C)) ∧
      Disjoint (e.symm '' G) (OnePoint.map (starRingEnd ℂ) '' (e.symm '' G)) := by
  obtain ⟨-, hCΓ, hfree, hdisj⟩ := hG
  have hsub : C ⊆ Γ := by
    rcases hCΓ with h | h
    · exact h.subset
    · exact h.2
  obtain ⟨hfr, hfr2, hne⟩ : C ⊆ frontier G ∧ Disjoint C (closure (frontier G \ C)) ∧ C.Nonempty := by
    rcases hfree with ⟨⟨γ, -, hγ⟩, h1, h2, -⟩ | ⟨⟨γ, -, -, hγ⟩, h1, h2⟩
    · refine ⟨h1, h2, γ (1 / 2), ?_⟩
      rw [← hγ]
      exact mem_image_of_mem γ ⟨by norm_num, by norm_num⟩
    · refine ⟨h1, h2, γ 1, ?_⟩
      rw [← hγ]
      exact mem_range_self 1
  refine ⟨?_, hne.image _, ?_, ?_, ?_⟩
  · calc ⇑e.symm '' C ⊆ ⇑e.symm '' Γ := image_mono hsub
      _ = LiZhongQC.extRealLine := by rw [hΓ, lv15_symm_image_image]
  · rw [← e.symm.image_frontier]
    exact image_mono hfr
  · rw [← e.symm.image_frontier, ← image_sdiff e.symm.injective, ← e.symm.image_closure]
    exact (disjoint_image_iff e.symm.injective).2 hfr2
  · have h := (disjoint_image_iff e.symm.injective).2 hdisj
    rwa [hR, image_comp, image_comp, lv15_symm_image_image] at h

/-- Helper (Tier B, B3; "`G ∪ C ∪ G*` is obviously a domain", P1:1285, normalized). If a domain `G` is disjoint from
its mirror image `z̄(G)` and `C` is a nonempty part of its boundary on the extended real line with
`C ∩ closure (Fr G \ C) = ∅`, then `G ∪ C ∪ z̄(G)` is a domain. -/
theorem lv18_isDomain_union {G C : Set ExtPlane} (hG : IsDomainExt G) (hCR : C ⊆ LiZhongQC.extRealLine)
    (hCne : C.Nonempty) (hCfr : C ⊆ frontier G) (hfree : Disjoint C (closure (frontier G \ C)))
    (hdisj : Disjoint G (OnePoint.map (starRingEnd ℂ) '' G)) :
    IsDomainExt (G ∪ C ∪ OnePoint.map (starRingEnd ℂ) '' G) := by
  obtain ⟨ch, hch, hcc, hcR⟩ := lv18_conj_homeo
  set c : ExtPlane → ExtPlane := OnePoint.map (starRingEnd ℂ) with hc_def
  have hcont : Continuous c := hch ▸ ch.continuous
  have hcGo : IsOpen (c '' G) := by
    rw [← hch]
    exact ch.isOpenMap _ hG.1
  have hcfr : frontier (c '' G) = c '' frontier G := by rw [← hch, ch.image_frontier]
  have hccl : closure (c '' G) = c '' closure G := by rw [← hch, ch.image_closure]
  have hGR : ∀ q ∈ G, q ∉ LiZhongQC.extRealLine := fun q hq hqR =>
    disjoint_left.1 hdisj hq ⟨q, hq, hcR q hqR⟩
  -- openness at the points of `C`
  have hD : IsOpen (G ∪ C ∪ c '' G) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ((hx | hx) | hx)
    · exact mem_of_superset (hG.1.mem_nhds hx) fun y hy => Or.inl (Or.inl hy)
    · have hN : (closure (frontier G \ C))ᶜ ∈ 𝓝 x :=
        isClosed_closure.isOpen_compl.mem_nhds (disjoint_left.1 hfree hx)
      obtain ⟨B, hBN, hBo, hxB, hP, hBc, hBR⟩ := lv18_good_nhds (hCR hx) hN
      set P := B ∩ toExt {z : ℂ | 0 < z.im} with hP_def
      have hBfr : ∀ y ∈ B, y ∈ frontier G → y ∈ C := fun y hy hyf => by
        by_contra hyC
        exact hBN hy (subset_closure ⟨hyf, hyC⟩)
      have hPR : ∀ y ∈ P, y ∉ LiZhongQC.extRealLine := by
        rintro _ ⟨-, z, hz, rfl⟩ (⟨u, hu, hue⟩ | h)
        · have h0 : u.im = 0 := hu
          rw [OnePoint.coe_injective hue] at h0
          exact lt_irrefl (0 : ℝ) (h0 ▸ hz)
        · exact OnePoint.coe_ne_infty z h
      have hBsplit : ∀ y ∈ B, y ∉ LiZhongQC.extRealLine → y ∈ P ∨ c y ∈ P := by
        intro y hy hyR
        induction y using OnePoint.rec with
        | infty => exact absurd (Or.inr rfl) hyR
        | coe z =>
          rcases lt_trichotomy z.im 0 with h | h | h
          · right
            refine ⟨hBc _ hy, (starRingEnd ℂ) z, ?_, rfl⟩
            show 0 < ((starRingEnd ℂ) z).im
            rw [Complex.conj_im]
            linarith
          · exact absurd (Or.inl ⟨z, h, rfl⟩) hyR
          · exact Or.inl ⟨hy, z, h, rfl⟩
      have hsplit : ∀ U : Set ExtPlane, IsOpen U → (∀ y ∈ P, y ∈ frontier U → False) →
          P ⊆ U ∨ P ⊆ (closure U)ᶜ := fun U hU hfr =>
        hP.subset_or_subset hU isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure)
          fun y hy => by
            by_cases hyU : y ∈ U
            · exact Or.inl hyU
            · refine Or.inr fun hcl => hfr y hy ?_
              rw [hU.frontier_eq]
              exact ⟨hcl, hyU⟩
      have hfrG : ∀ y ∈ P, y ∈ frontier G → False := fun y hy hyf =>
        hPR y hy (hCR (hBfr y hy.1 hyf))
      have hfrcG : ∀ y ∈ P, y ∈ frontier (c '' G) → False := by
        intro y hy hyf
        rw [hcfr] at hyf
        obtain ⟨f, hf, rfl⟩ := hyf
        have hfB : f ∈ B := by
          have h := hBc _ hy.1
          change c (c f) ∈ B at h
          rwa [hcc] at h
        have hfR := hCR (hBfr f hfB hf)
        rw [hcR f hfR] at hy
        exact hPR f hy hfR
      have hside : P ⊆ G ∨ P ⊆ c '' G := by
        obtain ⟨g, hgB, hgG⟩ := mem_closure_iff.1 (frontier_subset_closure (hCfr hx)) B hBo hxB
        rcases hBsplit g hgB (hGR g hgG) with hgP | hgP
        · left
          rcases hsplit G hG.1 hfrG with h | h
          · exact h
          · exact absurd (subset_closure hgG) (h hgP)
        · right
          rcases hsplit (c '' G) hcGo hfrcG with h | h
          · exact h
          · exact absurd (subset_closure (mem_image_of_mem c hgG)) (h hgP)
      refine mem_of_superset (hBo.mem_nhds hxB) fun y hy => ?_
      by_cases hyR : y ∈ LiZhongQC.extRealLine
      · have hcl := hBR ⟨hy, hyR⟩
        have hyG : y ∈ closure G := by
          rcases hside with h | h
          · exact closure_mono h hcl
          · have h1 := closure_mono h hcl
            rw [hccl] at h1
            obtain ⟨f, hf, hfy⟩ := h1
            have : f = y := by rw [← hcc f, hfy, hcR y hyR]
            exact this ▸ hf
        have hyf : y ∈ frontier G := by
          rw [hG.1.frontier_eq]
          exact ⟨hyG, fun h => hGR y h hyR⟩
        exact Or.inl (Or.inr (hBfr y hy hyf))
      · rcases hBsplit y hy hyR with hyP | hyP <;> rcases hside with h | h
        · exact Or.inl (Or.inl (h hyP))
        · exact Or.inr (h hyP)
        · exact Or.inr ⟨c y, h hyP, hcc y⟩
        · obtain ⟨g, hg, hgy⟩ := h hyP
          have : g = y := by rw [← hcc g, hgy, hcc]
          exact Or.inl (Or.inl (this ▸ hg))
    · exact mem_of_superset (hcGo.mem_nhds hx) fun y hy => Or.inr hy
  -- connectedness: `G ∪ C` and `z̄(G) ∪ C` are connected and meet in `C`
  have hGC : IsPreconnected (G ∪ C) := hG.2.isPreconnected.subset_closure subset_union_left
    (union_subset subset_closure (hCfr.trans frontier_subset_closure))
  have hcGC : IsPreconnected (c '' G ∪ C) := by
    have h1 : IsPreconnected (c '' G) := hG.2.isPreconnected.image c hcont.continuousOn
    refine h1.subset_closure subset_union_left (union_subset subset_closure ?_)
    intro y hy
    rw [hccl]
    exact ⟨y, frontier_subset_closure (hCfr hy), hcR y (hCR hy)⟩
  obtain ⟨x₀, hx₀⟩ := hCne
  have hconn := hGC.union x₀ (Or.inr hx₀) (Or.inr hx₀) hcGC
  have heq : G ∪ C ∪ (c '' G ∪ C) = G ∪ C ∪ c '' G := by
    rw [union_comm (c '' G) C, ← union_assoc, union_assoc G C C, union_self]
  rw [heq] at hconn
  exact ⟨hD, ⟨x₀, Or.inl (Or.inr hx₀)⟩, hconn⟩

/-- Helper (Tier B, B3; the continuation (8.4) is a homeomorphism, normalized). Let `X` be continuous and one-to-one
on `G ∪ C`, with `X(G ∪ C) = G′ ∪ C′`, `X(G) = G′`, `C, C′` on the extended real line, `C′ ⊆ Fr G′`,
`G′ ∩ z̄(G′) = ∅`, `G ∩ C = ∅`, and `X(z̄) = conj X(z)` on `G`. Then `X` is continuous and one-to-one on the open set
`G ∪ C ∪ z̄(G)`. -/
theorem lv18_continuousOn_injOn {X : ExtPlane → ExtPlane} {G C G' C' : Set ExtPlane} (hG : IsOpen G)
    (hG' : IsOpen G') (hCR : C ⊆ LiZhongQC.extRealLine) (hC'R : C' ⊆ LiZhongQC.extRealLine)
    (hC'fr : C' ⊆ frontier G') (hGC : Disjoint G C)
    (hdisj' : Disjoint G' (OnePoint.map (starRingEnd ℂ) '' G'))
    (hD : IsOpen (G ∪ C ∪ OnePoint.map (starRingEnd ℂ) '' G)) (hc : ContinuousOn X (G ∪ C))
    (hi : InjOn X (G ∪ C)) (himg : X '' (G ∪ C) = G' ∪ C') (hXG : X '' G = G')
    (hX : ∀ z ∈ G, X (OnePoint.map (starRingEnd ℂ) z) = OnePoint.map (starRingEnd ℂ) (X z)) :
    ContinuousOn X (G ∪ C ∪ OnePoint.map (starRingEnd ℂ) '' G) ∧
      InjOn X (G ∪ C ∪ OnePoint.map (starRingEnd ℂ) '' G) := by
  obtain ⟨ch, hch, hcc, hcR⟩ := lv18_conj_homeo
  set c : ExtPlane → ExtPlane := OnePoint.map (starRingEnd ℂ) with hc_def
  have hcont : Continuous c := hch ▸ ch.continuous
  have hcGo : IsOpen (c '' G) := by
    rw [← hch]
    exact ch.isOpenMap _ hG
  have hG'C' : Disjoint G' C' :=
    Disjoint.mono_right hC'fr (disjoint_iff_inter_eq_empty.2 hG'.inter_frontier_eq)
  have hXGC : ∀ a ∈ G ∪ C, X a ∈ G' ∪ C' := fun a ha => himg ▸ mem_image_of_mem X ha
  have hXGG : ∀ z ∈ G, X z ∈ G' := fun z hz => hXG ▸ mem_image_of_mem X hz
  have hXC : ∀ y ∈ C, X y ∈ C' := fun y hy => by
    rcases hXGC y (Or.inr hy) with h1 | h1
    · rw [← hXG] at h1
      obtain ⟨g, hg, hgy⟩ := h1
      have hgy' := hi (Or.inl hg) (Or.inr hy) hgy
      rw [hgy'] at hg
      exact (disjoint_left.1 hGC hg hy).elim
    · exact h1
  have hEq : EqOn X (c ∘ X ∘ c) (c '' G ∪ C) := by
    rintro y (⟨z, hz, rfl⟩ | hy)
    · show X (c z) = c (X (c (c z)))
      rw [hcc, hX z hz]
    · show X y = c (X (c y))
      rw [hcR y (hCR hy), hcR _ (hC'R (hXC y hy))]
  have hmapc : MapsTo c (c '' G ∪ C) (G ∪ C) := by
    rintro y (⟨z, hz, rfl⟩ | hy)
    · left
      rw [hcc]
      exact hz
    · right
      rw [hcR y (hCR hy)]
      exact hy
  refine ⟨fun x hx => ?_, ?_⟩
  · apply ContinuousAt.continuousWithinAt
    have hcw : ∀ y ∈ c '' G ∪ C, ContinuousWithinAt X (c '' G ∪ C) y := fun y hy => by
      have h1 : ContinuousWithinAt X (G ∪ C) (c y) := hc _ (hmapc hy)
      exact (hcont.continuousAt.comp_continuousWithinAt
        (h1.comp hcont.continuousWithinAt hmapc)).congr hEq (hEq hy)
    rcases hx with (hx | hx) | hx
    · exact (hc x (Or.inl hx)).continuousAt (mem_of_superset (hG.mem_nhds hx) subset_union_left)
    · refine ((hc x (Or.inr hx)).union (hcw x (Or.inr hx))).continuousAt ?_
      refine mem_of_superset (hD.mem_nhds (Or.inl (Or.inr hx))) ?_
      rintro y ((hy | hy) | hy)
      · exact Or.inl (Or.inl hy)
      · exact Or.inl (Or.inr hy)
      · exact Or.inr (Or.inl hy)
    · exact (hcw x (Or.inl hx)).continuousAt (mem_of_superset (hcGo.mem_nhds hx) subset_union_left)
  · have key : ∀ a ∈ G ∪ C, ∀ z ∈ G, X a ≠ X (c z) := by
      intro a ha z hz h
      rw [hX z hz] at h
      rcases hXGC a ha with h1 | h1
      · rw [h] at h1
        exact disjoint_left.1 hdisj' h1 ⟨X z, hXGG z hz, rfl⟩
      · have h2 : X z = X a := by rw [← hcR _ (hC'R h1), h, hcc]
        exact disjoint_left.1 hG'C' (hXGG z hz) (by rw [h2]; exact h1)
    rintro a₁ (h₁ | ⟨z₁, hz₁, rfl⟩) a₂ (h₂ | ⟨z₂, hz₂, rfl⟩) h12
    · exact hi h₁ h₂ h12
    · exact (key a₁ h₁ z₂ hz₂ h12).elim
    · exact (key a₂ h₂ z₁ hz₁ h12.symm).elim
    · rw [hX z₁ hz₁, hX z₂ hz₂] at h12
      have h3 := congrArg c h12
      rw [hcc, hcc] at h3
      rw [hi (Or.inl hz₁) (Or.inl hz₂) h3]

/-- Helper (Tier B, B3; removability of the real axis, Li Zhong's `s13x_removable`). A continuous one-to-one map `g`
of an open set `Ω ⊆ ℂ` which is `K`-quasiconformal near every point of `Ω` off the real axis is `K`-quasiconformal
in `Ω`. -/
theorem lv18_isKQC_of_off_real {g : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hc : ContinuousOn g Ω) (hi : InjOn g Ω)
    (hloc : ∀ z ∈ Ω, z.im ≠ 0 → ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ LiZhongQC.IsKQC g U K) :
    LiZhongQC.IsKQC g Ω K := by
  have hg := LiZhongQC.qcl_f_isHomeomorphOnto_of_injOn hΩ hc hi
  refine LiZhongQC.s13x_removable (L := Ω ∩ {z : ℂ | z.im = 0}) hΩ hK hg
    (MeasureTheory.measure_mono_null inter_subset_right LiZhongQC.gzE_volume_im_eq_zero) ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => by
      have h := hy.2
      simp only [mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero] at h
      exact h
  · filter_upwards [(MeasureTheory.compl_mem_ae_iff.2 (MeasureTheory.measure_singleton (0 : ℝ)) :
      ({0}ᶜ : Set ℝ) ∈ MeasureTheory.ae MeasureTheory.volume)] with y hy
    refine countable_empty.mono fun x hx => (hy ?_).elim
    have h := hx.2
    simp only [mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero] at h
    exact h
  · intro z hz
    exact hloc z hz.1 fun h => hz.2 ⟨hz.1, h⟩

/-- Helper (Tier B, B3; reflected mappings, Li Zhong's `abR_x_isKQC_conj`). If the finite part of `v` is
`K`-quasiconformal on the finite core over `G`, then the finite part of `z̄ ∘ v ∘ z̄` is `K`-quasiconformal on the
finite core over `z̄(G)`. -/
theorem lv18_isKQC_conj {v : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hK : LiZhongQC.IsKQC (finiteMap v) {z : ℂ | (z : ExtPlane) ∈ G ∧ v z ≠ extInf} K) :
    LiZhongQC.IsKQC (finiteMap (OnePoint.map (starRingEnd ℂ) ∘ v ∘ OnePoint.map (starRingEnd ℂ)))
      {z : ℂ | (z : ExtPlane) ∈ OnePoint.map (starRingEnd ℂ) '' G ∧
        (OnePoint.map (starRingEnd ℂ) ∘ v ∘ OnePoint.map (starRingEnd ℂ)) z ≠ extInf} K := by
  obtain ⟨-, -, hcc, -⟩ := lv18_conj_homeo
  set c : ExtPlane → ExtPlane := OnePoint.map (starRingEnd ℂ) with hc_def
  have hcinf : ∀ q, c q = extInf ↔ q = extInf := fun q => by
    induction q using OnePoint.rec with
    | infty => exact iff_of_true rfl rfl
    | coe z => exact iff_of_false (OnePoint.coe_ne_infty _) (OnePoint.coe_ne_infty _)
  have hset : {z : ℂ | (z : ExtPlane) ∈ c '' G ∧ (c ∘ v ∘ c) z ≠ extInf} =
      (starRingEnd ℂ) ⁻¹' {z : ℂ | (z : ExtPlane) ∈ G ∧ v z ≠ extInf} := by
    ext z
    have h1 : c (z : ExtPlane) = (((starRingEnd ℂ) z : ℂ) : ExtPlane) := rfl
    show ((z : ExtPlane) ∈ c '' G ∧ c (v (c z)) ≠ extInf) ↔
      ((((starRingEnd ℂ) z : ℂ) : ExtPlane) ∈ G ∧ v (((starRingEnd ℂ) z : ℂ) : ExtPlane) ≠ extInf)
    rw [h1, Ne, hcinf]
    constructor
    · rintro ⟨⟨y, hy, hyz⟩, h2⟩
      refine ⟨?_, h2⟩
      rw [← h1, ← hyz, hcc]
      exact hy
    · rintro ⟨hz1, hz2⟩
      refine ⟨⟨_, hz1, ?_⟩, hz2⟩
      rw [← h1, hcc]
  rw [hset]
  refine LiZhongQC.ad_isKQC_congr (LiZhongQC.abR_x_isKQC_conj hK) fun z hz => ?_
  have hz2 : v (((starRingEnd ℂ) z : ℂ) : ExtPlane) ≠ extInf := hz.2
  obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.1 hz2
  show finiteValue (c (v (c z))) = (starRingEnd ℂ) (finiteValue (v (((starRingEnd ℂ) z : ℂ) : ExtPlane)))
  have h1 : c (z : ExtPlane) = (((starRingEnd ℂ) z : ℂ) : ExtPlane) := rfl
  rw [h1, ← hζ]
  rfl

/-- **Reflection principle** (Ch. I §8.4). Let `G` and `G′` be two domains which can be reflected in circular arcs
`C` and `C′`, and let `w : G → G′` be a `K`-quasiconformal mapping under which `C` and `C′` correspond. Then the
continued mapping `w : G ∪ C ∪ G* → G′ ∪ C′ ∪ G′*` satisfying `w(z*) = w(z)*` (8.4) is `K`-quasiconformal.
Modelling: the continued mapping `W` equals `w` in `G`, is a homeomorphic extension to `G ∪ C` (Theorem 8.2), and
satisfies (8.4) on `G*`. -/
theorem reflection_principle {w W : ExtPlane → ExtPlane} {G G' C C' Γ Γ' : Set ExtPlane} {K : ℝ}
    (hG : CanReflectIn G C Γ) (hG' : CanReflectIn G' C' Γ') (hw : IsKQuasiconformal w G K) (hwG : w '' G = G')
    (hcorr : Corresponds w G G' C C') (hW₁ : EqOn W w G) (hW₂ : IsHomeoOn W (G ∪ C) (G' ∪ C'))
    (hW₃ : ∀ z ∈ G, W (genCircleReflection Γ z) = genCircleReflection Γ' (w z)) :
    IsKQuasiconformal W (G ∪ C ∪ genCircleReflection Γ '' G) K := by
  have _ := hcorr
  obtain ⟨e, he, hes, hΓe, hRe⟩ := lv18_reflection_eq hG.1
  obtain ⟨e', he', hes', hΓe', hRe'⟩ := lv18_reflection_eq hG'.1
  obtain ⟨hC₀R, hC₀ne, hC₀fr, hC₀free, hG₀disj⟩ := lv18_normalize hG e hΓe hRe
  obtain ⟨hC₀'R, -, hC₀'fr, -, hG₀'disj⟩ := lv18_normalize hG' e' hΓe' hRe'
  set c : ExtPlane → ExtPlane := OnePoint.map (starRingEnd ℂ) with hc_def
  have hcc : ∀ q, c (c q) = q := fun q => by
    induction q using OnePoint.rec with
    | infty => rfl
    | coe z => exact congrArg _ (Complex.conj_conj z)
  have hee : ∀ s : Set ExtPlane, ⇑e '' (⇑e.symm '' s) = s := fun s => by
    rw [image_image]
    simp
  have hGd : IsDomainExt G := hw.1
  have hG'd : IsDomainExt G' := by
    rw [← hwG]
    exact ⟨invariance_of_open_sets hw.1.1 hw.2.1.1.1 hw.2.1.1.2.1, hw.1.2.image w hw.2.1.1.1⟩
  -- the normalized domain `D₀ = G₀ ∪ C₀ ∪ z̄(G₀)` and the normalized mapping `X = e′⁻¹ ∘ W ∘ e`
  have hG₀ : IsDomainExt (e.symm '' G) :=
    ⟨e.symm.isOpenMap _ hGd.1, hGd.2.image _ e.symm.continuous.continuousOn⟩
  have hG₀' : IsOpen (e'.symm '' G') := e'.symm.isOpenMap _ hG'd.1
  have hD₀ := lv18_isDomain_union hG₀ hC₀R hC₀ne hC₀fr hC₀free hG₀disj
  set X : ExtPlane → ExtPlane := ⇑e'.symm ∘ W ∘ ⇑e with hX_def
  have hmaps : MapsTo e (e.symm '' G ∪ e.symm '' C) (G ∪ C) := by
    intro x hx
    rw [← image_union, mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Homeomorph.apply_symm_apply]
    exact hy
  have hXc : ContinuousOn X (e.symm '' G ∪ e.symm '' C) :=
    e'.symm.continuous.comp_continuousOn (hW₂.1.comp e.continuous.continuousOn hmaps)
  have hXi : InjOn X (e.symm '' G ∪ e.symm '' C) :=
    e'.symm.injective.injOn.comp (hW₂.2.1.comp e.injective.injOn hmaps) (mapsTo_univ _ _)
  have hWG : W '' G = G' := by
    rw [← hwG]
    exact image_congr hW₁
  have himg : X '' (e.symm '' G ∪ e.symm '' C) = e'.symm '' G' ∪ e'.symm '' C' := by
    rw [hX_def, image_comp, image_comp, ← image_union, hee, hW₂.2.2.1, image_union]
  have hXG : X '' (e.symm '' G) = e'.symm '' G' := by
    rw [hX_def, image_comp, image_comp, hee, hWG]
  have hXw : ∀ y ∈ G, X (e.symm y) = e'.symm (w y) := fun y hy => by
    show e'.symm (W (e (e.symm y))) = _
    rw [Homeomorph.apply_symm_apply, hW₁ hy]
  have hX3 : ∀ z ∈ e.symm '' G, X (c z) = c (X z) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : e (c (e.symm y)) = genCircleReflection Γ y := by rw [hRe]; rfl
    have h2 : genCircleReflection Γ' (w y) = e' (c (e'.symm (w y))) := by rw [hRe']; rfl
    show e'.symm (W (e (c (e.symm y)))) = c (X (e.symm y))
    rw [h1, hW₃ y hy, h2, Homeomorph.symm_apply_apply, hXw y hy]
  have hGC : Disjoint (e.symm '' G) (e.symm '' C) :=
    Disjoint.mono_right hC₀fr (disjoint_iff_inter_eq_empty.2 hG₀.1.inter_frontier_eq)
  obtain ⟨hXcD, hXiD⟩ := lv18_continuousOn_injOn hG₀.1 hG₀' hC₀R hC₀'R hC₀'fr hGC hG₀'disj hD₀.1 hXc hXi himg
    hXG hX3
  -- the finite part of `X` is `K`-quasiconformal on the finite core of `D₀`
  have hk := lv13_isKQC_of_isKQuasiconformal hw
  have hK1 : 1 ≤ K := hk.2.1
  set D₀ := e.symm '' G ∪ e.symm '' C ∪ c '' (e.symm '' G) with hD₀_def
  have hΩo : IsOpen {z : ℂ | (z : ExtPlane) ∈ D₀ ∧ X z ≠ extInf} :=
    (hXcD.isOpen_inter_preimage hD₀.1 (isOpen_compl_singleton : IsOpen ({extInf}ᶜ : Set ExtPlane))).preimage
      OnePoint.continuous_coe
  have hΩc : ContinuousOn (finiteMap X) {z : ℂ | (z : ExtPlane) ∈ D₀ ∧ X z ≠ extInf} := by
    intro z hz
    obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.1 hz.2
    have h1 := lv15_finiteValue_continuousAt ζ
    rw [hζ] at h1
    exact (ContinuousAt.comp (g := finiteValue) (f := X ∘ ((↑) : ℂ → ExtPlane)) h1
      ((hXcD.continuousAt (hD₀.1.mem_nhds hz.1)).comp OnePoint.continuous_coe.continuousAt)).continuousWithinAt
  have hΩi : InjOn (finiteMap X) {z : ℂ | (z : ExtPlane) ∈ D₀ ∧ X z ≠ extInf} := by
    intro z₁ h₁ z₂ h₂ h12
    have h : X z₁ = X z₂ := by
      rw [← lv15_coe_finiteValue h₁.2, ← lv15_coe_finiteValue h₂.2]
      exact congrArg _ h12
    exact OnePoint.coe_injective (hXiD h₁.1 h₂.1 h)
  -- over `G₀`, `X = e′⁻¹ ∘ w ∘ e`
  have hv := lv15_isKQC_mobius_conj hGd.1 hw.2.1.1.1 hw.2.1.1.2.1 hk he hes'
  have hcore : {ζ : ℂ | e (ζ : ExtPlane) ∈ G ∧ e'.symm (w (e (ζ : ExtPlane))) ≠ extInf} =
      {z : ℂ | (z : ExtPlane) ∈ e.symm '' G ∧ (⇑e'.symm ∘ w ∘ ⇑e) z ≠ extInf} := by
    ext ζ
    rw [Homeomorph.image_symm]
    rfl
  rw [hcore] at hv
  have hXv : ∀ z ∈ e.symm '' G, X z = (⇑e'.symm ∘ w ∘ ⇑e) z := by
    rintro _ ⟨y, hy, rfl⟩
    show X (e.symm y) = e'.symm (w (e (e.symm y)))
    rw [hXw y hy, Homeomorph.apply_symm_apply]
  have hXcv : ∀ z ∈ c '' (e.symm '' G), X z = (c ∘ (⇑e'.symm ∘ w ∘ ⇑e) ∘ c) z := by
    rintro _ ⟨u, hu, rfl⟩
    show X (c u) = c ((⇑e'.symm ∘ w ∘ ⇑e) (c (c u)))
    rw [hcc, hX3 u hu, hXv u hu]
  -- over `z̄(G₀)`, `X = z̄ ∘ (e′⁻¹ ∘ w ∘ e) ∘ z̄`
  have hv' := lv18_isKQC_conj hv
  have hloc : ∀ z ∈ {z : ℂ | (z : ExtPlane) ∈ D₀ ∧ X z ≠ extInf}, z.im ≠ 0 →
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ {z : ℂ | (z : ExtPlane) ∈ D₀ ∧ X z ≠ extInf} ∧
        LiZhongQC.IsKQC (finiteMap X) U K := by
    intro z hz hzim
    have hzC : (z : ExtPlane) ∉ e.symm '' C := fun h => by
      rcases hC₀R h with ⟨u, hu, hue⟩ | h'
      · rw [OnePoint.coe_injective hue] at hu
        exact hzim hu
      · exact OnePoint.coe_ne_infty z h'
    rcases hz.1 with (h | h) | h
    · -- `z ∈ G₀`
      refine ⟨_, hv.1, ⟨h, by rw [← hXv _ h]; exact hz.2⟩, fun u hu => ⟨Or.inl (Or.inl hu.1), ?_⟩,
        LiZhongQC.ad_isKQC_congr hv fun u hu => congrArg finiteValue (hXv _ hu.1)⟩
      rw [hXv _ hu.1]
      exact hu.2
    · exact absurd h hzC
    · -- `z ∈ z̄(G₀)`
      refine ⟨_, hv'.1, ⟨h, by rw [← hXcv _ h]; exact hz.2⟩, fun u hu => ⟨Or.inr hu.1, ?_⟩,
        LiZhongQC.ad_isKQC_congr hv' fun u hu => congrArg finiteValue (hXcv _ hu.1)⟩
      rw [hXcv _ hu.1]
      exact hu.2
  have hk₀ := lv18_isKQC_of_off_real hΩo hK1 hΩc hΩi hloc
  -- back to `W` on `D = e(D₀)`
  have hfun : W = ⇑e' ∘ X ∘ ⇑e.symm := by
    funext q
    show W q = e' (e'.symm (W (e (e.symm q))))
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  have hDe : G ∪ C ∪ genCircleReflection Γ '' G = e '' D₀ := by
    rw [hD₀_def, image_union, image_union, hee, hee, hRe, image_comp, image_comp, hc_def]
  have hkW := lv15_isKQC_mobius_conj hD₀.1 hXcD hXiD hk₀ hes he'
  rw [hDe, hfun]
  have hDd : IsDomainExt (e '' D₀) := ⟨e.isOpenMap _ hD₀.1, hD₀.2.image _ e.continuous.continuousOn⟩
  have hmaps' : MapsTo e.symm (e '' D₀) D₀ := by
    rintro _ ⟨y, hy, rfl⟩
    rwa [Homeomorph.symm_apply_apply]
  refine lv15_isKQuasiconformal_of_isKQC hDd
    (e'.continuous.comp_continuousOn (hXcD.comp e.symm.continuous.continuousOn hmaps'))
    (e'.injective.injOn.comp (hXiD.comp e.symm.injective.injOn hmaps') (mapsTo_univ _ _)) ?_
  have hcoreD : {ζ : ℂ | e.symm (ζ : ExtPlane) ∈ D₀ ∧ e' (X (e.symm (ζ : ExtPlane))) ≠ extInf} =
      {z : ℂ | (z : ExtPlane) ∈ e '' D₀ ∧ (⇑e' ∘ X ∘ ⇑e.symm) z ≠ extInf} := by
    ext ζ
    rw [e.image_eq_preimage_symm]
    rfl
  rw [hcoreD] at hkW
  exact hkW

end LehtoVirtanen1973
