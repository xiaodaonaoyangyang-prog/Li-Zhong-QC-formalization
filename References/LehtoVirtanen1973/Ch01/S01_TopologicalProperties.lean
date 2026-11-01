import References.Common.ExtendedPlane
import LiZhongQC.Lemmas.InvarianceOfDomain

/-!
# Lehto–Virtanen, Chapter I §1: Topological properties of plane sets

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §1
(pp. 5–13; `full.md` P1:169–316).

Standing conventions of the book, as modelled here (see the root file `References/LehtoVirtanen1973.lean`):
the *plane* is the extended plane `ℂ̄ = LiZhongQC.ExtPlane` (P1:171) and the *finite plane* is `ℂ`; the empty set
counts as connected (footnote 3), so "connected" is `IsPreconnected` wherever a set may be empty.

* Definition (the plane, the finite plane, §1.1) — exists: `LiZhongQC.ExtPlane`
* Definition (spherical distance, §1.1) — `sphericalDist`, `sphericalBall`
* Definition (open, closed in `A`, §1.1) — exists: `IsOpen`, `IsClosed` (Mathlib subspace topology on a subtype)
* Definition (domain) — exists: `References.IsDomainExt`
* Definition (homeomorphism of `A` onto `A′`, §1.2) — `IsHomeoOn`
* Lemma 1.1 (§1.2) — `lemma1_1_1`
* Theorem on the invariance of open sets (§1.2) — `invariance_of_open_sets`
* Theorem on the invariance of domains (§1.2) — `invariance_of_domains`
* Definition (line, finite line, extended line, line segment, §1.3) — omitted: terminology; every use is modelled
  concretely (segments of the finite plane, the extended real line, generalized circles in §8)
* Definition (Jordan curve, §1.3) — exists: `LiZhongQC.IsJordanCurve`
* Definition (Jordan arc, open and closed arcs, parametric representation, endpoints, §1.3) — `IsJordanArcOver`,
  `IsJordanArc`, `IsOpenJordanArc`, `IsClosedJordanArc`, `IsArcFromTo`, `JoinableByArcIn`
* Definition ((closed) polygonal arc, closed polygon, §1.3) — `IsPolygonalArc`, `IsClosedPolygon`
* Definition (`A` separates `A₁` and `A₂`, in `E`, §1.3) — `SeparatesIn`, `Separates`
* Unlabelled (§1.3, P1:205): a Jordan arc has a connected complement — `jordanArc_compl_isConnected`
* Jordan curve theorem (§1.3) — `jordan_curve_theorem`
* Definition (continuum) — `IsContinuum`
* Lemma 1.2 (§1.3) — `lemma1_1_2`
* Lemma 1.2′ (§1.3) — `lemma1_1_2'`
* Lemma 1.3 (§1.3) — `lemma1_1_3`
* Lemma 1.4 (§1.3) — `lemma1_1_4`
* Definition (orientation of a Jordan arc, oriented arc, orientation of a Jordan curve, §1.4) — omitted: modelled by
  parametrizations (see the next item), and in III.2 by the initial endpoint of a closed arc; no statement
  quantifies over oriented arcs
* Definition (orientation by points `p₁, p₂, p₃`; positive orientation with respect to a domain, §1.4) —
  `IsLoopParam`, `IsPositiveBoundaryParam`, `IsPositivelyOrdered`
* Definition (Jordan domain; the boundary `Fr G` as a point set, §1.4) — exists: `References.IsJordanDomainExt`,
  `frontier`
* Definition (`∂G`, the positively oriented boundary curve, §1.4) — omitted: notation; modelled by the positively
  oriented parametrizations of the item above
* Definition (`w` preserves the orientation of the boundary of `D`; sense-preserving homeomorphism, §1.5) —
  `PreservesBoundaryOrientation`, `IsSensePreservingOn`
* Orientation theorem (§1.5) — `orientation_theorem`
* Unlabelled (§1.5, P1:257): inverse and composition of sense-preserving homeomorphisms — `sensePreserving_inv`,
  `sensePreserving_comp`
* Definition (differentiability at `∞` and at a pole, the Jacobian and its sign, regular point, §1.6; finite points
  and finite functions from I.9 on) — `extChart`, `extChartInv`, `localRep`, `chartJacobian`, `IsRegularPointOf`,
  `finiteValue`, `finiteMap`
* Unlabelled (§1.6, P1:271): the sign of the Jacobian at regular points of a (sense-preserving) homeomorphism —
  `sensePreserving_of_jacobian_pos`, `jacobian_pos_of_sensePreserving`
* Definition (simply connected, `n`-tuply connected, §1.7) — `IsSimplyConnectedDomain`, `IsNTuplyConnected`
* Unlabelled (§1.7, P1:277): the complement of a component of the complement of a domain is a simply connected
  domain — `compl_component_isSimplyConnected`
* Unlabelled (§1.7, P1:281): a crosscut splits a simply connected domain into two simply connected domains, and
  in a Jordan domain its closure separates the two complementary boundary arcs — `crosscut_simplyConnected`,
  `crosscut_separates_boundaryArcs`
* Definition (set of limit points of `E` under `w`; correspondence, §1.8) — `limitSetUnder`, `Corresponds`
* Unlabelled (§1.8, P1:285): the boundary components of homeomorphic `n`-tuply connected domains correspond —
  `boundaryComponents_correspond`
* Definition (free boundary arc, free boundary curve, closed free boundary arc, §1.9) — `IsFreeBoundaryArc`,
  `IsFreeBoundaryCurve`, `IsClosedFreeBoundaryArc`
* Unlabelled (§1.9, P1:297): every point of a free boundary arc of `G` is a limit point of `G` and of `-Ḡ` —
  `freeBoundaryArc_limitPoint`
* Unlabelled (§1.9, P1:297, quoted from Newman): the components of the complement of a closed connected set are
  simply connected domains — `component_compl_isSimplyConnected`
* Lemma 1.5 (§1.9) — `lemma1_1_5_i`, `lemma1_1_5_ii`
* Lemma 1.6 (§1.9) — `lemma1_1_6`

The claims of P1:281 (cited at P1:629) and P1:297 (cited at P1:2900, 2934) are stated above. The unlabelled facts
of §1.5 (P1:247), §1.7 (P1:275, 279) and §1.9 (P1:295: a subarc of a free arc is free; a free boundary curve is a
boundary component, cited at P1:2609) are used only inside proofs or follow at once from the definitions, and are
not stated (inventory U−). [OCR] cross-references later in the book: P1:2900 "Lemma I.4.4" is Lemma I.1.4, and
P1:2934 "I.4.9" is I.1.9.
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §1.1 The plane -/

/-- **Definition** (spherical distance, Ch. I §1.1). For finite `z₁, z₂`,
`k(z₁, z₂) = arctan |(z₁ - z₂)/(1 + z̄₁ z₂)|`, and `k(z, ∞) = arctan |1/z|`; `0 ≤ k ≤ π/2`.
Modelling: `arctan (y/x)` for `x, y ≥ 0` is written `arg (x + i y)`, which is also correct when the book's quotient
is infinite (`1 + z̄₁ z₂ = 0`, value `π/2`; `z = 0` in `k(z, ∞)`), so no division by zero occurs. -/
def sphericalDist (z₁ z₂ : ExtPlane) : ℝ :=
  OnePoint.elim z₁ (OnePoint.elim z₂ 0 fun b => arg ((‖b‖ : ℂ) + I))
    fun a => OnePoint.elim z₂ (arg ((‖a‖ : ℂ) + I))
      fun b => arg ((‖1 + (starRingEnd ℂ) a * b‖ : ℂ) + (‖a - b‖ : ℂ) * I)

/-- The open spherical disc `{z : k(a, z) < r}`: the "disc neighbourhoods" of the book (§1.9). -/
def sphericalBall (a : ExtPlane) (r : ℝ) : Set ExtPlane := {z | sphericalDist a z < r}

/-! ## §1.2 Homeomorphisms -/

/-- **Definition** (homeomorphism, Ch. I §1.2). `w` is a homeomorphism of `A` onto `A′`: one-to-one on `A`,
`w(A) = A′`, and `w` and its inverse are continuous. -/
def IsHomeoOn (w : ExtPlane → ExtPlane) (A A' : Set ExtPlane) : Prop :=
  ContinuousOn w A ∧ InjOn w A ∧ w '' A = A' ∧ ContinuousOn (Function.invFunOn w A) A'

/-- Helper (D-II). The inversion `M = mobiusExt 0 1 1 0` of `ℂ̄` (`ζ ↦ 1/ζ`, `0 ↔ ∞`) is a continuous involution. -/
theorem lv11_inv_involutive :
    Continuous (LiZhongQC.mobiusExt 0 1 1 0) ∧
      ∀ q, LiZhongQC.mobiusExt 0 1 1 0 (LiZhongQC.mobiusExt 0 1 1 0 q) = q := by
  refine ⟨LiZhongQC.continuous_mobiusExt (by norm_num), fun q => ?_⟩
  induction q using OnePoint.rec with
  | infty => simp [LiZhongQC.mobiusExt]
  | coe b =>
    by_cases h : b = 0
    · simp [LiZhongQC.mobiusExt, h]
    · simp [LiZhongQC.mobiusExt, h]

/-- Helper (D-II). Every point `p` of `ℂ̄` is sent to a finite point by a continuous involution of `ℂ̄`: the identity,
or the inversion when `p = ∞`. -/
theorem lv11_normalize (p : ExtPlane) :
    ∃ A : ExtPlane → ExtPlane, Continuous A ∧ (∀ q, A (A q) = q) ∧ ∃ a : ℂ, A p = (a : ExtPlane) := by
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨LiZhongQC.mobiusExt 0 1 1 0, lv11_inv_involutive.1, lv11_inv_involutive.2, 0, ?_⟩
    simp [LiZhongQC.mobiusExt]
  | coe a => exact ⟨id, continuous_id, fun _ => rfl, a, rfl⟩

/-- Helper (D-II, invariance of domain in `ℂ̄`). A mapping `w`, continuous and one-to-one on an open set `G` of `ℂ̄`,
maps `G` onto a neighbourhood of every image point `w(z)`, `z ∈ G`: after Möbius normalizations making `z` and `w(z)`
finite, this is the plane invariance of domain (`LiZhongQC.isOpen_image_of_continuousOn_injOn`). -/
theorem lv11_image_mem_nhds {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G) (hc : ContinuousOn w G)
    (hi : InjOn w G) {z : ExtPlane} (hz : z ∈ G) : w '' G ∈ 𝓝 (w z) := by
  -- normalize `z` and `w z` to finite points by continuous involutions `A`, `B`
  obtain ⟨A, hAc, hAA, a, ha⟩ := lv11_normalize z
  obtain ⟨B, hBc, hBB, c, hc'⟩ := lv11_normalize (w z)
  have hAinj : Function.Injective A := fun x y h => by rw [← hAA x, h, hAA]
  set v : ExtPlane → ExtPlane := fun q => B (w (A q)) with hvdef
  set G' := A ⁻¹' G with hG'def
  have hG'o : IsOpen G' := hG.preimage hAc
  have hvc : ContinuousOn v G' := hBc.comp_continuousOn (hc.comp hAc.continuousOn fun q hq => hq)
  have hvi : InjOn v G' := fun x hx y hy h => by
    have h1 : w (A x) = w (A y) := by rw [← hBB (w (A x)), ← hBB (w (A y))]; exact congrArg B h
    exact hAinj (hi hx hy h1)
  have haG' : (a : ExtPlane) ∈ G' := by
    show A a ∈ G
    rw [← ha, hAA]
    exact hz
  have hva : v a = (c : ExtPlane) := by
    show B (w (A a)) = c
    rw [← ha, hAA, hc']
  -- the finite part of `v` near `a` is a continuous injection of an open set of the plane
  set fv : ExtPlane → ℂ := fun q => OnePoint.elim q 0 id with hfvdef
  set U : Set ℂ := {x : ℂ | (x : ExtPlane) ∈ G' ∧ v x ≠ extInf} with hUdef
  have hUo : IsOpen U := by
    have h := hvc.isOpen_inter_preimage hG'o (isOpen_compl_singleton (x := extInf))
    have e : U = ((↑) : ℂ → ExtPlane) ⁻¹' (G' ∩ v ⁻¹' {extInf}ᶜ) := by
      ext x
      simp [hUdef]
    rw [e]
    exact h.preimage OnePoint.continuous_coe
  have hfin : ∀ x ∈ U, v x = ((fv (v x) : ℂ) : ExtPlane) := fun x hx => by
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hx.2
    rw [← hu]
    rfl
  have hfc : ContinuousOn (fun x : ℂ => fv (v x)) U := by
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuousOn_iff]
    exact (hvc.comp OnePoint.continuous_coe.continuousOn fun x (hx : x ∈ U) => hx.1).congr fun x hx => (hfin x hx).symm
  have hfi : InjOn (fun x : ℂ => fv (v x)) U := fun x hx y hy h => by
    have h' : v x = v y := by rw [hfin x hx, hfin y hy]; exact congrArg _ h
    exact OnePoint.coe_injective (hvi hx.1 hy.1 h')
  have hfo : IsOpen ((fun x : ℂ => fv (v x)) '' U) := LiZhongQC.isOpen_image_of_continuousOn_injOn hUo hfc hfi
  have haU : a ∈ U := ⟨haG', by rw [hva]; exact OnePoint.coe_ne_infty c⟩
  -- so `v(G')` is a neighbourhood of `v a = c`
  have hvn : v '' G' ∈ 𝓝 (v a) := by
    have h1 : ((↑) : ℂ → ExtPlane) '' ((fun x : ℂ => fv (v x)) '' U) ∈ 𝓝 (v a) := by
      refine (OnePoint.isOpen_image_coe.2 hfo).mem_nhds ⟨fv (v a), ⟨a, haU, rfl⟩, ?_⟩
      exact (hfin a haU).symm
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx.1, hfin x hx⟩
  -- and `w(G) = B⁻¹(v(G'))`, a neighbourhood of `w z`
  have hwG : w '' G = B ⁻¹' (v '' G') := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨A x, show A (A x) ∈ G by rw [hAA]; exact hx, ?_⟩
      show B (w (A (A x))) = B (w x)
      rw [hAA]
    · rintro ⟨y, hy, hyq⟩
      refine ⟨A y, hy, ?_⟩
      rw [← hBB q, ← hyq]
      show w (A y) = B (B (w (A y)))
      rw [hBB]
  rw [hwG]
  have hBw : B (w z) = v a := by rw [hva, hc']
  exact hBc.continuousAt.preimage_mem_nhds (by rw [hBw]; exact hvn)

/-- **Lemma 1.1** (Ch. I §1.2). Every one-to-one and continuous mapping of an open set of the plane onto a plane
set is a homeomorphism. -/
theorem lemma1_1_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G) (hc : ContinuousOn w G)
    (hi : InjOn w G) : IsHomeoOn w G (w '' G) := by
  refine ⟨hc, hi, rfl, ?_⟩
  -- `w` maps open subsets of `G` onto open sets
  have hopen : ∀ V : Set ExtPlane, IsOpen V → IsOpen (w '' (G ∩ V)) := fun V hV => by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact lv11_image_mem_nhds (hG.inter hV) (hc.mono inter_subset_left) (hi.mono inter_subset_left) hx
  have hGo : IsOpen (w '' G) := by simpa using hopen univ isOpen_univ
  rw [continuousOn_open_iff hGo]
  intro V hV
  convert hopen V hV using 1
  ext q
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxV⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rwa [mem_preimage, hi.leftInvOn_invFunOn hx] at hxV
  · rintro ⟨x, ⟨hx, hxV⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rwa [mem_preimage, hi.leftInvOn_invFunOn hx]

/-- **Theorem on the invariance of open sets** (Ch. I §1.2). If `w` is a one-to-one continuous mapping of an open
set `G` of the plane onto `G′`, then `G′` is open. -/
theorem invariance_of_open_sets {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsOpen G)
    (hc : ContinuousOn w G) (hi : InjOn w G) : IsOpen (w '' G) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact lv11_image_mem_nhds hG hc hi hx

/-- **Theorem on the invariance of domains** (Ch. I §1.2). The image of a domain under a one-to-one continuous
mapping is a domain. -/
theorem invariance_of_domains {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hc : ContinuousOn w G) (hi : InjOn w G) : IsDomainExt (w '' G) := by
  exact ⟨invariance_of_open_sets hG.1 hc hi, hG.2.image w hc⟩

/-! ## §1.3 Separation theorems -/

/-- `C` is the topological image of the interval `I`: `C = γ(I)` with `γ|_I` an embedding (a parametric
representation of `C`, Ch. I §1.3). -/
def IsJordanArcOver (I : Set ℝ) (C : Set ExtPlane) : Prop :=
  ∃ γ : ℝ → ExtPlane, IsEmbedding (I.domRestrict γ) ∧ γ '' I = C

/-- **Definition** (Jordan arc, Ch. I §1.3): the topological image of a line segment (a nondegenerate real
interval). -/
def IsJordanArc (C : Set ExtPlane) : Prop :=
  ∃ I : Set ℝ, I.OrdConnected ∧ I.Nontrivial ∧ IsJordanArcOver I C

/-- **Definition** (open Jordan arc, Ch. I §1.3): homeomorphic to an open segment. -/
def IsOpenJordanArc (C : Set ExtPlane) : Prop := IsJordanArcOver (Ioo 0 1) C

/-- **Definition** (closed Jordan arc, Ch. I §1.3): homeomorphic to a closed segment. -/
def IsClosedJordanArc (C : Set ExtPlane) : Prop := IsJordanArcOver (Icc 0 1) C

/-- `C` is a closed Jordan arc with endpoints `z₁` and `z₂` (a "Jordan arc joining `z₁` and `z₂`"). -/
def IsArcFromTo (C : Set ExtPlane) (z₁ z₂ : ExtPlane) : Prop :=
  ∃ γ : ℝ → ExtPlane, IsEmbedding ((Icc (0 : ℝ) 1).domRestrict γ) ∧ γ '' Icc 0 1 = C ∧ γ 0 = z₁ ∧ γ 1 = z₂

/-- The points `z₁, z₂` can be joined by a Jordan arc lying in `S` (trivially when `z₁ = z₂ ∈ S`). -/
def JoinableByArcIn (S : Set ExtPlane) (z₁ z₂ : ExtPlane) : Prop :=
  (z₁ = z₂ ∧ z₁ ∈ S) ∨ ∃ C, IsArcFromTo C z₁ z₂ ∧ C ⊆ S

/-- **Definition** (polygonal arc, Ch. I §1.3): a (closed) Jordan arc consisting of finitely many line segments.
Modelling: the segments are closed segments of the finite plane; an open polygonal arc is the interior of such an
arc and is not used separately. -/
def IsPolygonalArc (C : Set ExtPlane) : Prop :=
  IsClosedJordanArc C ∧ ∃ s : Finset (ℂ × ℂ), C = toExt (⋃ p ∈ s, segment ℝ p.1 p.2)

/-- **Definition** (closed polygon, Ch. I §1.3): a Jordan curve consisting of finitely many line segments. -/
def IsClosedPolygon (C : Set ExtPlane) : Prop :=
  IsJordanCurve C ∧ ∃ s : Finset (ℂ × ℂ), C = toExt (⋃ p ∈ s, segment ℝ p.1 p.2)

/-- **Definition** (separation in `E`, Ch. I §1.3). `A` separates `A₁` and `A₂` in `E`: `A₁` and `A₂` lie in two
different components of `E \ A`. -/
def SeparatesIn (E A A₁ A₂ : Set ExtPlane) : Prop :=
  ∃ x₁ ∈ E \ A, ∃ x₂ ∈ E \ A, A₁ ⊆ connectedComponentIn (E \ A) x₁ ∧
    A₂ ⊆ connectedComponentIn (E \ A) x₂ ∧ connectedComponentIn (E \ A) x₁ ≠ connectedComponentIn (E \ A) x₂

/-- **Definition** (separation, Ch. I §1.3). `A` separates `A₁` and `A₂`: they lie in different components of the
complement `-A = ℂ̄ \ A`. -/
def Separates (A A₁ A₂ : Set ExtPlane) : Prop := SeparatesIn univ A A₁ A₂

/-- **Unlabelled** (Ch. I §1.3, P1:205). A Jordan arc has a connected complement. -/
theorem jordanArc_compl_isConnected {C : Set ExtPlane} (hC : IsJordanArc C) : IsConnected Cᶜ := by
  sorry

/-- **Jordan curve theorem** (Ch. I §1.3, quoted from Newman). The complement of a Jordan curve `C` of the plane
consists of two disjoint domains, which both have `C` as boundary. -/
theorem jordan_curve_theorem {C : Set ExtPlane} (hC : IsJordanCurve C) :
    ∃ G₁ G₂ : Set ExtPlane, IsDomainExt G₁ ∧ IsDomainExt G₂ ∧ Disjoint G₁ G₂ ∧ Cᶜ = G₁ ∪ G₂ ∧
      frontier G₁ = C ∧ frontier G₂ = C := by
  sorry

/-- A continuum: a compact connected set. -/
def IsContinuum (F : Set ExtPlane) : Prop := IsCompact F ∧ IsConnected F

/-- **Lemma 1.2** (Ch. I §1.3). If `F₁` and `F₂` are two continua whose intersection is not connected, then the
complement of `F₁ ∪ F₂` is not connected. -/
theorem lemma1_1_2 {F₁ F₂ : Set ExtPlane} (h₁ : IsContinuum F₁) (h₂ : IsContinuum F₂)
    (h : ¬ IsPreconnected (F₁ ∩ F₂)) : ¬ IsPreconnected (F₁ ∪ F₂)ᶜ := by
  sorry

/-- **Lemma 1.2′** (Ch. I §1.3). Let `F₁, …, Fₙ` (`n ≥ 2`) be continua of which any three have no common points.
If `F₁ ∩ F₂` is not connected, then the complement of the union of the `Fᵢ` is not connected.
Modelling: the continua are indexed by `Fin (n + 2)`, `F₁, F₂` being `F 0, F 1`. -/
theorem lemma1_1_2' {n : ℕ} {F : Fin (n + 2) → Set ExtPlane} (hF : ∀ i, IsContinuum (F i))
    (h3 : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → F i ∩ F j ∩ F k = ∅) (h : ¬ IsPreconnected (F 0 ∩ F 1)) :
    ¬ IsPreconnected (⋃ i, F i)ᶜ := by
  sorry

/-- **Lemma 1.3** (Ch. I §1.3). Let `F₁` and `F₂` be closed sets with a connected intersection. Two points which
are separated neither by `F₁` nor by `F₂` are not separated by `F₁ ∪ F₂`. -/
theorem lemma1_1_3 {F₁ F₂ : Set ExtPlane} (h₁ : IsClosed F₁) (h₂ : IsClosed F₂)
    (h : IsPreconnected (F₁ ∩ F₂)) {a b : ExtPlane} (ha : ¬ Separates F₁ {a} {b})
    (hb : ¬ Separates F₂ {a} {b}) : ¬ Separates (F₁ ∪ F₂) {a} {b} := by
  sorry

/-- **Lemma 1.4** (Ch. I §1.3). Let `G` be a domain with a connected complement and `F` a closed subset of `G`.
Then `F` and the complement of `G` can be separated by a closed polygon.
Modelling: the complement of `G` is assumed nonempty (the book separates `F` from it); the polygon lies in
`G \ F`. -/
theorem lemma1_1_4 {G F : Set ExtPlane} (hG : IsDomainExt G) (hc : IsPreconnected Gᶜ)
    (hne : Gᶜ.Nonempty) (hF : IsClosed F) (hFG : F ⊆ G) :
    ∃ P : Set ExtPlane, IsClosedPolygon P ∧ P ⊆ G \ F ∧ Separates P F Gᶜ := by
  sorry

/-! ## §1.4 Orientation -/

/-- `γ` runs once around `C`: continuous, `1`-periodic, one-to-one on `[0, 1)`, with range `C` (a parametrization
of the Jordan curve `C` by the circle `ℝ/ℤ`). -/
def IsLoopParam (C : Set ExtPlane) (γ : ℝ → ExtPlane) : Prop :=
  Continuous γ ∧ Function.Periodic γ 1 ∧ InjOn γ (Ico 0 1) ∧ range γ = C

/-- **Definition** (positive orientation with respect to `G`, Ch. I §1.4). The parametrization `γ` of the boundary
of `G` is positively oriented with respect to `G`: for a linear (Möbius) transformation `t` with `t(G)` a bounded
domain containing the origin, a continuous branch of `arg t(γ(s))` increases by `2π` as `s` runs over `[0, 1]`.
Modelling: the branch of `arg` is the imaginary part of a continuous logarithm `L` of `t ∘ γ`; the book notes that
the choice of `t` does not matter, so `t` is existentially quantified. -/
def IsPositiveBoundaryParam (G : Set ExtPlane) (γ : ℝ → ExtPlane) : Prop :=
  IsLoopParam (frontier G) γ ∧ ∃ t : ExtPlane → ExtPlane, IsMobius t ∧
    ∃ U : Set ℂ, t '' G = toExt U ∧ Bornology.IsBounded U ∧ (0 : ℂ) ∈ U ∧
      ∃ L : ℝ → ℂ, Continuous L ∧ (∀ s, t (γ s) = ((exp (L s) : ℂ) : ExtPlane)) ∧
        L 1 - L 0 = 2 * Real.pi * I

/-- **Definition** (orientation by points, Ch. I §1.4). The boundary points `p₁, …, pₙ` of `G` (in this order)
give the positive orientation with respect to `G`: they are met in this order, within one turn, by a positively
oriented parametrization. -/
def IsPositivelyOrdered {n : ℕ} (G : Set ExtPlane) (p : Fin n → ExtPlane) : Prop :=
  ∃ γ : ℝ → ExtPlane, IsPositiveBoundaryParam G γ ∧ ∃ (a : ℝ) (s : Fin n → ℝ), StrictMono s ∧
    (∀ i, s i ∈ Ico a (a + 1)) ∧ ∀ i, γ (s i) = p i

/-! ## §1.5 Sense-preserving homeomorphisms -/

/-- **Definition** (Ch. I §1.5). `w` preserves the orientation of the boundary of the Jordan domain `D`: whenever
`p₁, p₂, p₃` is the positive orientation of `Fr D` with respect to `D`, `w(p₁), w(p₂), w(p₃)` is the positive
orientation of `Fr w(D)` with respect to `w(D)`. -/
def PreservesBoundaryOrientation (w : ExtPlane → ExtPlane) (D : Set ExtPlane) : Prop :=
  ∀ p : Fin 3 → ExtPlane, IsPositivelyOrdered D p → IsPositivelyOrdered (w '' D) (w ∘ p)

/-- **Definition** (sense-preserving homeomorphism, Ch. I §1.5). `w` is a homeomorphism of `A` onto `w(A)` which
preserves the orientation of the boundary of every Jordan domain `D` with `D̄ ⊂ A`. -/
def IsSensePreservingOn (w : ExtPlane → ExtPlane) (A : Set ExtPlane) : Prop :=
  IsHomeoOn w A (w '' A) ∧ ∀ D, IsJordanDomainExt D → closure D ⊆ A → PreservesBoundaryOrientation w D

/-- **Orientation theorem** (Ch. I §1.5, quoted from Newman). Let `G` be a domain or the closure of a Jordan
domain, and `w` a homeomorphism of `G`. If there is a Jordan domain `D`, `D̄ ⊂ G`, such that `w` preserves the
orientation of the boundary of `D`, then `w` is sense-preserving. -/
theorem orientation_theorem {w : ExtPlane → ExtPlane} {G : Set ExtPlane}
    (hG : IsDomainExt G ∨ ∃ D₀, IsJordanDomainExt D₀ ∧ G = closure D₀) (hw : IsHomeoOn w G (w '' G))
    {D : Set ExtPlane} (hD : IsJordanDomainExt D) (hDG : closure D ⊆ G)
    (hpres : PreservesBoundaryOrientation w D) : IsSensePreservingOn w G := by
  sorry

/-- **Unlabelled** (Ch. I §1.5, P1:257). The inverse of a sense-preserving homeomorphism is sense-preserving. -/
theorem sensePreserving_inv {w : ExtPlane → ExtPlane} {A : Set ExtPlane} (hw : IsSensePreservingOn w A) :
    IsSensePreservingOn (Function.invFunOn w A) (w '' A) := by
  sorry

/-- Helper (converse bridge C5, Jordan-image lemma). Let `D` be a Jordan domain of `ℂ̄` and `w` continuous and
one-to-one on `D̄`. Then `w(D)` is a Jordan domain, `closure (w(D)) = w(D̄)` and `frontier (w(D)) = w(frontier D)`
(invariance of open sets on `D`, compactness of `D̄`, and the image of a Jordan curve under an injective continuous
map). -/
theorem lv11_jordanDomain_image {w : ExtPlane → ExtPlane} {D : Set ExtPlane} (hD : IsJordanDomainExt D)
    (hc : ContinuousOn w (closure D)) (hi : InjOn w (closure D)) :
    IsJordanDomainExt (w '' D) ∧ closure (w '' D) = w '' closure D ∧ frontier (w '' D) = w '' frontier D := by
  obtain ⟨⟨hDo, hDc⟩, hJ⟩ := hD
  have hDcl : D ⊆ closure D := subset_closure
  -- `w(D)` is open (invariance of open sets) and connected
  have hwo : IsOpen (w '' D) := invariance_of_open_sets hDo (hc.mono hDcl) (hi.mono hDcl)
  have hwc : IsConnected (w '' D) := hDc.image w (hc.mono hDcl)
  -- `w(D̄)` is compact, hence closed, and it is the closure of `w(D)`
  have hwK : IsClosed (w '' closure D) := (isClosed_closure.isCompact.image_of_continuousOn hc).isClosed
  have hcl : closure (w '' D) = w '' closure D :=
    Subset.antisymm (closure_minimal (image_mono hDcl) hwK) hc.image_closure
  have hfr : frontier (w '' D) = w '' frontier D := by
    rw [hwo.frontier_eq, hDo.frontier_eq, hcl]
    ext q
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxD⟩
      exact ⟨x, ⟨hx, fun h => hxD ⟨x, h, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxD⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hxD (hi (hDcl hy) hx hyx ▸ hy)
  refine ⟨⟨⟨hwo, hwc⟩, ?_⟩, hcl, hfr⟩
  -- the image of the Jordan curve `frontier D` under the injective continuous `w`
  obtain ⟨γ, hγc, hγi, hγr⟩ := hJ
  have hγD : ∀ x, γ x ∈ closure D := fun x => frontier_subset_closure (hγr ▸ mem_range_self x)
  rw [hfr, ← hγr]
  refine ⟨w ∘ γ, hc.comp_continuous hγc hγD, fun x y h => hγi (hi (hγD x) (hγD y) h), ?_⟩
  rw [range_comp]

/-- **Unlabelled** (Ch. I §1.5, P1:257). A composition of sense-preserving homeomorphisms is sense-preserving. -/
theorem sensePreserving_comp {w₁ w₂ : ExtPlane → ExtPlane} {A : Set ExtPlane} (h₁ : IsSensePreservingOn w₁ A)
    (h₂ : IsSensePreservingOn w₂ (w₁ '' A)) : IsSensePreservingOn (w₂ ∘ w₁) A := by
  obtain ⟨⟨hc₁, hi₁, -, hinv₁⟩, hp₁⟩ := h₁
  obtain ⟨⟨hc₂, hi₂, -, hinv₂⟩, hp₂⟩ := h₂
  have hmaps : MapsTo w₁ A (w₁ '' A) := mapsTo_image w₁ A
  have hi : InjOn (w₂ ∘ w₁) A := hi₂.comp hi₁ hmaps
  refine ⟨⟨hc₂.comp hc₁ hmaps, hi, rfl, ?_⟩, fun D hD hDA p hp => ?_⟩
  · -- the inverse of `w₂ ∘ w₁` is `w₁⁻¹ ∘ w₂⁻¹`
    have hmaps' : MapsTo (Function.invFunOn w₂ (w₁ '' A)) ((w₂ ∘ w₁) '' A) (w₁ '' A) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Function.comp_apply, hi₂.leftInvOn_invFunOn (mem_image_of_mem w₁ hx)]
      exact mem_image_of_mem w₁ hx
    have heq : EqOn (Function.invFunOn (w₂ ∘ w₁) A)
        (Function.invFunOn w₁ A ∘ Function.invFunOn w₂ (w₁ '' A)) ((w₂ ∘ w₁) '' A) := by
      rintro _ ⟨x, hx, rfl⟩
      have e1 : Function.invFunOn (w₂ ∘ w₁) A ((w₂ ∘ w₁) x) = x := hi.leftInvOn_invFunOn hx
      simp only [Function.comp_apply] at e1 ⊢
      rw [e1, hi₂.leftInvOn_invFunOn (mem_image_of_mem w₁ hx), hi₁.leftInvOn_invFunOn hx]
    have himg : (w₂ ∘ w₁) '' A = w₂ '' (w₁ '' A) := image_comp w₂ w₁ A
    refine (hinv₁.comp ?_ hmaps').congr heq
    rw [himg]
    exact hinv₂
  · -- orientation: through the Jordan domain `w₁(D)`, `closure (w₁(D)) = w₁(D̄) ⊆ w₁(A)`
    obtain ⟨hJ, hcl, -⟩ := lv11_jordanDomain_image hD (hc₁.mono hDA) (hi₁.mono hDA)
    have h1 := hp₁ D hD hDA p hp
    have h2 := hp₂ (w₁ '' D) hJ (by rw [hcl]; exact image_mono hDA) (w₁ ∘ p) h1
    rw [image_comp]
    exact h2

/-! ## §1.6 Regular points of a mapping -/

/-- The chart of `ℂ̄` at `p` used in §1.6 and §2.1: `q ↦ q - p` for finite `p`, and `q ↦ 1/q` (`∞ ↦ 0`) at
`p = ∞`. The values off the chart domain (`q = ∞` for finite `p`, `q = 0` for `p = ∞`) are junk; they are never
seen, since only germs at `p` of maps continuous at `p` are used. -/
def extChart (p q : ExtPlane) : ℂ :=
  OnePoint.elim p (OnePoint.elim q 0 fun b => b⁻¹) fun a => OnePoint.elim q 0 fun b => b - a

/-- The inverse chart at `p`: `ζ ↦ p + ζ` for finite `p`, and `ζ ↦ 1/ζ` (`0 ↦ ∞`) at `p = ∞`. -/
def extChartInv (p : ExtPlane) (ζ : ℂ) : ExtPlane :=
  OnePoint.elim p (if ζ = 0 then extInf else ((ζ⁻¹ : ℂ) : ExtPlane)) fun a => ((a + ζ : ℂ) : ExtPlane)

/-- The local representation of `w` at `z` (Ch. I §1.6): `w` read in the charts at `z` and at `w(z)`. At a finite
point with a finite value this is `ζ ↦ w(z + ζ) - w(z)`; at `z = ∞` it is `w(1/ζ)`, and where `w(z) = ∞` it is
`1/w`, as in the book. -/
def localRep (w : ExtPlane → ExtPlane) (z : ExtPlane) : ℂ → ℂ :=
  fun ζ => extChart (w z) (w (extChartInv z ζ))

/-- The Jacobian of the local representation of `w` at `z` (Ch. I §1.6). At a finite point with a finite value it
is the Jacobian `J_w(z)`; at `z = ∞` or where `w(z) = ∞` only its sign is meaningful, as in the book. -/
def chartJacobian (w : ExtPlane → ExtPlane) (z : ExtPlane) : ℝ :=
  LinearMap.det (fderiv ℝ (localRep w z) 0 : ℂ →ₗ[ℝ] ℂ)

/-- **Definition** (regular point, Ch. I §1.6). `z` is a regular point of `w : G → G′`: `z` is an interior point of
`G`, `w` is differentiable at `z` (in the charts at `z` and `w(z)`), and `J_w(z) ≠ 0`.
Modelling: `ContinuousAt w z` is added so that the chart representation is a germ of `w` (automatic for the
homeomorphisms the book considers). -/
def IsRegularPointOf (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (z : ExtPlane) : Prop :=
  z ∈ interior G ∧ ContinuousAt w z ∧ DifferentiableAt ℝ (localRep w z) 0 ∧ chartJacobian w z ≠ 0

/-- The finite value of a point of `ℂ̄` (`∞ ↦ 0`, a junk value). Used for "finite functions" (from I.9 on the book's
"differentiable" refers only to finite points and finite values): every use is at a point where the value is
finite. -/
def finiteValue (q : ExtPlane) : ℂ := OnePoint.elim q 0 id

/-- The finite function `z ↦ w(z)` on the finite plane (junk `0` where `w(z) = ∞`, never used). -/
def finiteMap (w : ExtPlane → ExtPlane) : ℂ → ℂ := fun z => finiteValue (w z)

/-- **Unlabelled** (Ch. I §1.6, P1:271, first half). If the homeomorphism `w : G → G′` (`G` a domain or the
closure of a Jordan domain) possesses a regular point `z` where `J_w(z) > 0`, then `w` is sense-preserving. -/
theorem sensePreserving_of_jacobian_pos {w : ExtPlane → ExtPlane} {G : Set ExtPlane}
    (hG : IsDomainExt G ∨ ∃ D₀, IsJordanDomainExt D₀ ∧ G = closure D₀) (hw : IsHomeoOn w G (w '' G))
    {z : ExtPlane} (hz : IsRegularPointOf w G z) (hJ : 0 < chartJacobian w z) : IsSensePreservingOn w G := by
  sorry

/-- **Unlabelled** (Ch. I §1.6, P1:271, second half). The Jacobian of a sense-preserving homeomorphism is positive
at every regular point. -/
theorem jacobian_pos_of_sensePreserving {w : ExtPlane → ExtPlane} {G : Set ExtPlane}
    (hG : IsDomainExt G ∨ ∃ D₀, IsJordanDomainExt D₀ ∧ G = closure D₀) (hw : IsSensePreservingOn w G)
    {z : ExtPlane} (hz : IsRegularPointOf w G z) : 0 < chartJacobian w z := by
  sorry

/-! ## §1.7 Connectivity of a domain -/

/-- **Definition** (simply connected, Ch. I §1.7): a domain whose complement is connected (the empty complement
included, footnote 3, so that `ℂ̄` is simply connected). -/
def IsSimplyConnectedDomain (G : Set ExtPlane) : Prop := IsDomainExt G ∧ IsPreconnected Gᶜ

/-- **Definition** (`n`-tuply connected, Ch. I §1.7): a domain whose complement consists of `n` components,
`1 < n < ∞`. -/
def IsNTuplyConnected (G : Set ExtPlane) (n : ℕ) : Prop :=
  IsDomainExt G ∧ 1 < n ∧ Nat.card (ConnectedComponents ↥Gᶜ) = n

/-- **Unlabelled** (Ch. I §1.7, P1:277). Let `F` be a component of the complement of a domain `G`. Then the
complement of `F` is a simply connected domain. -/
theorem compl_component_isSimplyConnected {G : Set ExtPlane} (hG : IsDomainExt G) {x : ExtPlane}
    (hx : x ∈ Gᶜ) : IsSimplyConnectedDomain (connectedComponentIn Gᶜ x)ᶜ := by
  sorry

/-- **Unlabelled** (Ch. I §1.7, P1:281, first part). Let `G` be a simply connected domain. A Jordan arc `C ⊂ G`
with endpoints on `Fr G` separates `G` into two simply connected domains both having each point of `C` as a
boundary point.
Modelling: `C` is the open arc (endpoints `p ≠ q` removed) of the closed arc `C ∪ {p, q}`. -/
theorem crosscut_simplyConnected {G C : Set ExtPlane} {p q : ExtPlane} (hG : IsSimplyConnectedDomain G)
    (hC : IsArcFromTo (C ∪ {p, q}) p q) (hp : p ∉ C) (hq : q ∉ C) (hCG : C ⊆ G) (hpG : p ∈ frontier G)
    (hqG : q ∈ frontier G) :
    ∃ G₁ G₂ : Set ExtPlane, IsSimplyConnectedDomain G₁ ∧ IsSimplyConnectedDomain G₂ ∧ Disjoint G₁ G₂ ∧
      G \ C = G₁ ∪ G₂ ∧ C ⊆ frontier G₁ ∧ C ⊆ frontier G₂ := by
  sorry

/-- **Unlabelled** (Ch. I §1.7, P1:281, second part). If, besides, `G` is a Jordan domain, then `C̄` separates in
`Ḡ` the open subarcs of `Fr G` which are bounded by the endpoints of `C`. -/
theorem crosscut_separates_boundaryArcs {G C : Set ExtPlane} {p q : ExtPlane} (hG : IsJordanDomainExt G)
    (hC : IsArcFromTo (C ∪ {p, q}) p q) (hp : p ∉ C) (hq : q ∉ C) (hCG : C ⊆ G) (hpG : p ∈ frontier G)
    (hqG : q ∈ frontier G) :
    ∀ x ∈ frontier G \ {p, q}, ∀ y ∈ frontier G \ {p, q},
      connectedComponentIn (frontier G \ {p, q}) x ≠ connectedComponentIn (frontier G \ {p, q}) y →
        SeparatesIn (closure G) (C ∪ {p, q}) (connectedComponentIn (frontier G \ {p, q}) x)
          (connectedComponentIn (frontier G \ {p, q}) y) := by
  sorry

/-! ## §1.8 Boundary behaviour of topological mappings -/

/-- **Definition** (set of limit points of `E` under `w`, Ch. I §1.8): the union of the sets of limit points of the
images `w(A)` of all sets `A ⊂ G` whose limit points belong to `E`. -/
def limitSetUnder (w : ExtPlane → ExtPlane) (G E : Set ExtPlane) : Set ExtPlane :=
  ⋃ (A : Set ExtPlane) (_ : A ⊆ G) (_ : derivedSet A ⊆ E), derivedSet (w '' A)

/-- **Definition** (correspondence, Ch. I §1.8). The boundary sets `E` of `G` and `E′` of `G′` correspond under the
homeomorphism `w : G → G′`: each is the set of limit points of the other (under `w`, resp. `w⁻¹`). -/
def Corresponds (w : ExtPlane → ExtPlane) (G G' E E' : Set ExtPlane) : Prop :=
  limitSetUnder w G E = E' ∧ limitSetUnder (Function.invFunOn w G) G' E' = E

/-- **Unlabelled** (Ch. I §1.8, P1:285). Under a homeomorphism `w : G → G′` between two `n`-tuply connected domains
the `n` boundary components of `G` and `G′` correspond pairwise.
Modelling: stated as "every boundary component of `G` corresponds to a boundary component of `G′`"; applied to
`w⁻¹` this gives the pairing (`Corresponds` is symmetric and determines the partner). -/
theorem boundaryComponents_correspond {w : ExtPlane → ExtPlane} {G G' : Set ExtPlane} {n : ℕ}
    (hG : IsNTuplyConnected G n) (hG' : IsNTuplyConnected G' n) (hw : IsHomeoOn w G G') :
    ∀ x ∈ frontier G, ∃ y ∈ frontier G',
      Corresponds w G G' (connectedComponentIn (frontier G) x) (connectedComponentIn (frontier G') y) := by
  sorry

/-! ## §1.9 Free boundary arcs -/

/-- **Definition** (free boundary arc, Ch. I §1.9). An open Jordan arc `C` on the boundary of `G` such that
1° `C ∩ closure (Fr G \ C) = ∅`, and 2° `E \ C` is connected, `E` being the boundary component of `G` containing `C`.
[OCR] 1° is printed "`C ∩ (Fr G - C)` is empty", which is vacuous; the overline was lost, and the book's use (no
other boundary points accumulate at `C`) requires the closure. -/
def IsFreeBoundaryArc (G C : Set ExtPlane) : Prop :=
  IsOpenJordanArc C ∧ C ⊆ frontier G ∧ Disjoint C (closure (frontier G \ C)) ∧
    ∀ x ∈ C, IsPreconnected (connectedComponentIn (frontier G) x \ C)

/-- **Definition** (free boundary curve, Ch. I §1.9). A Jordan curve `C` on the boundary of `G` with
`C ∩ closure (Fr G \ C) = ∅` (condition 2° follows from 1° for curves, as the book notes). -/
def IsFreeBoundaryCurve (G C : Set ExtPlane) : Prop :=
  IsJordanCurve C ∧ C ⊆ frontier G ∧ Disjoint C (closure (frontier G \ C))

/-- **Definition** (closed free boundary arc, Ch. I §1.9): a closed subarc of an open free boundary arc. -/
def IsClosedFreeBoundaryArc (G C : Set ExtPlane) : Prop :=
  IsClosedJordanArc C ∧ ∃ C', IsFreeBoundaryArc G C' ∧ C ⊆ C'

/-- **Unlabelled** (Ch. I §1.9, P1:297). Every point of a free boundary arc `C` of `G` is a limit point both of `G`
and of `-Ḡ`. -/
theorem freeBoundaryArc_limitPoint {G C : Set ExtPlane} (hG : IsDomainExt G) (hC : IsFreeBoundaryArc G C)
    {a : ExtPlane} (ha : a ∈ C) : a ∈ derivedSet G ∧ a ∈ derivedSet (closure G)ᶜ := by
  sorry

/-- **Unlabelled** (Ch. I §1.9, P1:297, quoted from Newman). The components of the complement of a closed
connected set are simply connected domains. -/
theorem component_compl_isSimplyConnected {F : Set ExtPlane} (hF : IsClosed F) (hFc : IsPreconnected F)
    {x : ExtPlane} (hx : x ∉ F) : IsSimplyConnectedDomain (connectedComponentIn Fᶜ x) := by
  sorry

/-- **Lemma 1.5, 1°** (Ch. I §1.9). Let `a` be a point of a free boundary arc of the domain `G` and `U` a
neighbourhood of `a`. There exists a disc neighbourhood `V` of `a`, `V̄ ⊂ U`, such that every pair of points of
`G ∩ V` can be joined by a Jordan arc in `G ∩ U`.
Modelling: the disc is a spherical disc centred at `a`; the conclusion is the same for Euclidean discs, since each
kind of disc about `a` contains one of the other kind and the property passes to smaller `V`. -/
theorem lemma1_1_5_i {G C : Set ExtPlane} (hG : IsDomainExt G) (hC : IsFreeBoundaryArc G C) {a : ExtPlane}
    (ha : a ∈ C) {U : Set ExtPlane} (hU : U ∈ 𝓝 a) :
    ∃ r > 0, closure (sphericalBall a r) ⊆ U ∧
      ∀ z₁ ∈ G ∩ sphericalBall a r, ∀ z₂ ∈ G ∩ sphericalBall a r, JoinableByArcIn (G ∩ U) z₁ z₂ := by
  sorry

/-- **Lemma 1.5, 2°** (Ch. I §1.9). If the neighbourhood `V` of `a` has the property of 1°, and `U₁` is a disc
neighbourhood of `a` contained in `V`, then there exists a neighbourhood `V₁ ⊂ U₁` of `a` such that every pair of
points of `(V \ Ū₁) ∩ G` can be joined by a Jordan arc lying in `(U \ V̄₁) ∩ G`.
Modelling: `V` is any neighbourhood of `a` with the property of 1° (`V̄ ⊂ U` and joinability in `G ∩ U`); `U₁` is
any spherical disc `{z : k(b, z) < r₁}`, `0 < r₁ < π/2`, containing `a` and contained in `V` (spherical discs
comprise the Euclidean discs, the exteriors of discs and the half-planes, i.e. the book's discs of `ℂ̄`). -/
theorem lemma1_1_5_ii {G C : Set ExtPlane} (hG : IsDomainExt G) (hC : IsFreeBoundaryArc G C) {a : ExtPlane}
    (ha : a ∈ C) {U : Set ExtPlane} (hU : U ∈ 𝓝 a) {V : Set ExtPlane} (hVa : V ∈ 𝓝 a)
    (hV : closure V ⊆ U ∧ ∀ z₁ ∈ G ∩ V, ∀ z₂ ∈ G ∩ V, JoinableByArcIn (G ∩ U) z₁ z₂)
    {b : ExtPlane} {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < Real.pi / 2) (haU₁ : a ∈ sphericalBall b r₁)
    (hU₁ : sphericalBall b r₁ ⊆ V) :
    ∃ V₁ ∈ 𝓝 a, V₁ ⊆ sphericalBall b r₁ ∧
      ∀ z₁ ∈ (V \ closure (sphericalBall b r₁)) ∩ G, ∀ z₂ ∈ (V \ closure (sphericalBall b r₁)) ∩ G,
        JoinableByArcIn ((U \ closure V₁) ∩ G) z₁ z₂ := by
  sorry

/-- **Lemma 1.6** (Ch. I §1.9). Let `a` be a point of a free boundary arc of the domain `G` and `zₙ` a sequence of
points of `G` converging to `a`. Then there exists a Jordan arc `C` passing through the points `zₙ`, with
`C \ {a} ⊂ G` and with an endpoint at `a`.
Modelling: `C` is the closed arc `γ([0, 1])` with `γ(1) = a`. -/
theorem lemma1_1_6 {G C : Set ExtPlane} (hG : IsDomainExt G) (hC : IsFreeBoundaryArc G C) {a : ExtPlane}
    (ha : a ∈ C) {z : ℕ → ExtPlane} (hz : ∀ n, z n ∈ G) (hlim : Tendsto z atTop (𝓝 a)) :
    ∃ γ : ℝ → ExtPlane, IsEmbedding ((Icc (0 : ℝ) 1).domRestrict γ) ∧ γ 1 = a ∧ γ '' Ico 0 1 ⊆ G ∧
      ∀ n, z n ∈ γ '' Icc 0 1 := by
  sorry

end LehtoVirtanen1973
