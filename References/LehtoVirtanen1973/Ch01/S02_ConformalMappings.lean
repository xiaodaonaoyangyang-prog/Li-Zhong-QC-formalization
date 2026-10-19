import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties
import LiZhongQC.Ch01.S01_Quadrilateral

/-!
# Lehto–Virtanen, Chapter I §2: Conformal mappings of plane domains

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §2
(pp. 13–16; `full.md` P1:317–368).

Domains are domains of `ℂ̄`; conformality at `∞` and at a point where `w = ∞` is read in the charts of §1.6
(`localRep`), as in the book (P1:319).

* Definition (conformal mapping of a domain, conformality at `∞` and at poles, §2.1) — `IsConformalMap`
* Theorem on correspondence of boundaries (§2.2) — `boundary_correspondence`
* Unlabelled (§2.2, P1:339): three-point normalization of conformal maps of Jordan domains — `conformal_three_point`
* Definition (quadrilateral, vertices, sides, a-sides and b-sides, §2.3) — `Quadrilateral`, `Quadrilateral.side`
* Definition (homeomorphism and conformal mapping of quadrilaterals, §2.3) — `IsQuadHomeo`, `IsQuadConformal`
* Definition (rectangle as a quadrilateral; canonical mapping, canonical rectangle; module `M(Q)`, §2.4) —
  `Quadrilateral.IsRectangle`, `IsCanonicalMap`, `quadModule`, `Quadrilateral.module`
* Unlabelled (§2.4, P1:359–361): quadrilaterals are conformally equivalent iff their modules agree —
  `quad_confEquiv_iff_module_eq`
* Unlabelled (§2.4, P1:361): all canonical rectangles of `Q` have the ratio `M(Q)` — `module_eq_of_isCanonicalMap`
* Unlabelled (§2.4, P1:365): the module under a rearrangement of the vertices — `module_rotate`

Unlabelled facts of §2.1–2.2 used only in proofs or immediate (P1:321, 327, 333, 337) are not stated (inventory U−);
the elliptic-integral construction of §2.4 (P1:349–355) is a construction, not an item. The free-arc extension of
conformal maps (P1:333) is subsumed by `thm1_8_2` together with `conformal_isKQuasiconformal_one`. Not stated
either (U−): P1:347 (three boundary points determine a conformal map of quadrilaterals) and P1:359 (conformal maps
between rectangles are similarities; contained in `quad_confEquiv_iff_module_eq`).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §2.1 The Riemann mapping theorem -/

/-- **Definition** (conformal mapping, Ch. I §2.1). `w` is a (one-to-one) conformal mapping of the domain `G`:
continuous and one-to-one on `G` and analytic at every point of `G`, where analyticity at `∞` and at a point where
`w = ∞` means analyticity of `w(1/z)` at `0`, resp. of `1/w` (read through the charts, `localRep`). -/
def IsConformalMap (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  IsDomainExt G ∧ ContinuousOn w G ∧ InjOn w G ∧ ∀ z ∈ G, DifferentiableAt ℂ (localRep w z) 0

/-! ## §2.2 Boundary behaviour of conformal mappings -/

/-- **Theorem on correspondence of boundaries** (Ch. I §2.2). Let `G` and `G′` be `n`-tuply connected domains
which both have `n` Jordan curves as boundary components. Then every conformal mapping `w : G → G′` can be extended
to a homeomorphism of `Ḡ` onto `Ḡ′`.
Modelling: `n ≥ 1` (the book uses the case `n = 1` of Jordan domains in §2.2–2.4); "`n`-tuply connected" is written
as "the complement has `n` components"; every boundary component is a Jordan curve. -/
theorem boundary_correspondence {G G' : Set ExtPlane} {n : ℕ} (hn : 1 ≤ n)
    (hG : IsDomainExt G ∧ Nat.card (ConnectedComponents ↥Gᶜ) = n)
    (hG' : IsDomainExt G' ∧ Nat.card (ConnectedComponents ↥G'ᶜ) = n)
    (hJ : ∀ x ∈ frontier G, IsJordanCurve (connectedComponentIn (frontier G) x))
    (hJ' : ∀ x ∈ frontier G', IsJordanCurve (connectedComponentIn (frontier G') x))
    {w : ExtPlane → ExtPlane} (hw : IsConformalMap w G) (hwG : w '' G = G') :
    ∃ W : ExtPlane → ExtPlane, EqOn W w G ∧ IsHomeoOn W (closure G) (closure G') := by
  sorry

/-- **Unlabelled** (Ch. I §2.2, P1:339). If `G`, `G′` are Jordan domains and `p₁, p₂, p₃`, `q₁, q₂, q₃` are positive
orientations of their boundaries, there is a uniquely determined conformal mapping `w : G → G′` (extended to `Ḡ`)
with `w(pᵢ) = qᵢ`. -/
theorem conformal_three_point {G G' : Set ExtPlane} (hG : IsJordanDomainExt G) (hG' : IsJordanDomainExt G')
    {p q : Fin 3 → ExtPlane} (hp : IsPositivelyOrdered G p) (hq : IsPositivelyOrdered G' q) :
    ∃ w : ExtPlane → ExtPlane, IsConformalMap w G ∧ w '' G = G' ∧ IsHomeoOn w (closure G) (closure G') ∧
      (∀ i, w (p i) = q i) ∧
      ∀ w' : ExtPlane → ExtPlane, IsConformalMap w' G → w' '' G = G' →
        IsHomeoOn w' (closure G) (closure G') → (∀ i, w' (p i) = q i) → EqOn w' w (closure G) := by
  sorry

/-! ## §2.3 Quadrilaterals and their mappings -/

/-- **Definition** (quadrilateral, Ch. I §2.3). A Jordan domain `Q` of `ℂ̄` with a sequence `z₁, z₂, z₃, z₄` of
boundary points (the vertices) which agrees with the positive orientation of `Fr Q` with respect to `Q`. -/
structure Quadrilateral where
  /-- The Jordan domain `Q`. -/
  dom : Set ExtPlane
  /-- The vertices `z₁, z₂, z₃, z₄` (indices `0, 1, 2, 3`). -/
  vert : Fin 4 → ExtPlane
  isJordanDomain : IsJordanDomainExt dom
  vert_mem : ∀ i, vert i ∈ frontier dom
  positive : IsPositivelyOrdered dom vert

/-- **Definition** (sides, Ch. I §2.3). The side from `zᵢ` to `zᵢ₊₁` (indices mod 4) as a closed arc of `Fr Q`: the
two vertices together with the component of `Fr Q \ {zᵢ, zᵢ₊₁}` not containing `zᵢ₊₂`. Sides `0` and `2`
(`z₁z₂`, `z₃z₄`) are the a-sides, sides `1` and `3` the b-sides. -/
def Quadrilateral.side (Q : Quadrilateral) (i : Fin 4) : Set ExtPlane :=
  {p ∈ frontier Q.dom | p = Q.vert i ∨ p = Q.vert (i + 1) ∨
    connectedComponentIn (frontier Q.dom \ {Q.vert i, Q.vert (i + 1)}) p ≠
      connectedComponentIn (frontier Q.dom \ {Q.vert i, Q.vert (i + 1)}) (Q.vert (i + 2))}

/-- **Definition** (homeomorphism of quadrilaterals, Ch. I §2.3). A topological mapping `w : Q̄ → Q̄′` which carries
the vertices `zᵢ` into the vertices `wᵢ = w(zᵢ)`. -/
def IsQuadHomeo (w : ExtPlane → ExtPlane) (Q Q' : Quadrilateral) : Prop :=
  IsHomeoOn w (closure Q.dom) (closure Q'.dom) ∧ ∀ i, w (Q.vert i) = Q'.vert i

/-- **Definition** (conformal mapping of quadrilaterals, Ch. I §2.3): a homeomorphism of quadrilaterals whose
restriction to `Q` is conformal. -/
def IsQuadConformal (w : ExtPlane → ExtPlane) (Q Q' : Quadrilateral) : Prop :=
  IsQuadHomeo w Q Q' ∧ IsConformalMap w Q.dom

/-! ## §2.4 Conformal module of a quadrilateral -/

/-- **Definition** (rectangle, Ch. I §2.4). `Q` "is a rectangle": its domain is a Euclidean rectangle and its
vertices are the corners, i.e. `Q` is the image of `R(0, a, a + ib, ib)` under a similarity `z ↦ αz + β`. -/
def Quadrilateral.IsRectangle (Q : Quadrilateral) : Prop :=
  ∃ (a b : ℝ) (α β : ℂ), 0 < a ∧ 0 < b ∧ α ≠ 0 ∧
    Q.dom = toExt ((fun z => α * z + β) '' LiZhongQC.rectangle a b) ∧
      ∀ i, Q.vert i = OnePoint.map (fun z => α * z + β) (LiZhongQC.rectVert a b i)

/-- **Definition** (canonical mapping, Ch. I §2.4), for raw data `(D, (z₁, z₂, z₃, z₄))`: a conformal mapping of
the quadrilateral onto the rectangle `R(0, a, a + ib, ib)`, i.e. conformal in `D`, extended to a homeomorphism of the
closures, and carrying the vertices to the corners `0, a, a + ib, ib`. -/
def IsCanonicalMap (D : Set ExtPlane) (v : Fin 4 → ExtPlane) (a b : ℝ) (f : ExtPlane → ExtPlane) : Prop :=
  0 < a ∧ 0 < b ∧ IsConformalMap f D ∧ f '' D = toExt (LiZhongQC.rectangle a b) ∧
    IsHomeoOn f (closure D) (closure (toExt (LiZhongQC.rectangle a b))) ∧ ∀ i, f (v i) = LiZhongQC.rectVert a b i

/-- **Definition** (module, Ch. I §2.4), for raw data: `M = a/b` for a canonical rectangle `R(0, a, a + ib, ib)`
(`a` the length of the a-sides). All canonical rectangles give the same ratio (`quad_confEquiv_iff_module_eq`), so
the supremum is over a one-point set. Junk: `0` when there is no canonical mapping, e.g. for vertices not in the
positive order (the image data of a non-sense-preserving map); every statement using it avoids this case. That the
set is a singleton `{M(Q)}` for a quadrilateral is `module_eq_of_isCanonicalMap` with `exists_canonicalMap`. -/
def quadModule (D : Set ExtPlane) (v : Fin 4 → ExtPlane) : ℝ :=
  sSup {m : ℝ | ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap D v a b f ∧ m = a / b}

/-- **Definition** (module `M(Q)`, Ch. I §2.4). -/
def Quadrilateral.module (Q : Quadrilateral) : ℝ := quadModule Q.dom Q.vert

/-- **Unlabelled** (Ch. I §2.4, P1:359–361). Two quadrilaterals are conformally equivalent if and only if they have
the same module (every conformal mapping between rectangles being a similarity). -/
theorem quad_confEquiv_iff_module_eq (Q Q' : Quadrilateral) :
    (∃ w : ExtPlane → ExtPlane, IsQuadConformal w Q Q') ↔ Q.module = Q'.module := by
  sorry

/-- Auxiliary (the local representation at a finite point, §1.6). If `F` agrees on the open set `U ⊆ ℂ` with the
plane map `f` (finite values), then at `z ∈ U` the local representation `localRep F z` is `ζ ↦ f(z + ζ) - f(z)` near
`0`. Used by the module bridge `lv12_quadModule_toExt`. -/
theorem lv12_localRep_coe_eventuallyEq {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : ∀ w ∈ U, F (w : ExtPlane) = ((f w : ℂ) : ExtPlane)) {z : ℂ} (hz : z ∈ U) :
    localRep F (z : ExtPlane) =ᶠ[𝓝 0] fun ζ => f (z + ζ) - f z := by
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), z + ζ ∈ U :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hz)
  filter_upwards [hev] with ζ hζ
  simp only [localRep, extChartInv, OnePoint.elim_some]
  rw [hF z hz, hF _ hζ]
  rfl

/-- Auxiliary (conformality read in the charts, §1.6, §2.1). If `F` agrees on the open set `U ⊆ ℂ` with the plane
map `f` and the local representation of `F` at `z ∈ U` is differentiable at `0` (`IsConformalMap`), then `f` is
complex differentiable at `z`. -/
theorem lv12_differentiableAt_of_localRep {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : ∀ w ∈ U, F (w : ExtPlane) = ((f w : ℂ) : ExtPlane)) {z : ℂ} (hz : z ∈ U)
    (hd : DifferentiableAt ℂ (localRep F (z : ExtPlane)) 0) : DifferentiableAt ℂ f z := by
  have hd0 : DifferentiableAt ℂ (fun ζ => f (z + ζ) - f z) 0 :=
    hd.congr_of_eventuallyEq (lv12_localRep_coe_eventuallyEq hU hF hz).symm
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - z) z := differentiableAt_id.sub_const z
  have hcomp : DifferentiableAt ℂ ((fun ζ => f (z + ζ) - f z) ∘ fun w : ℂ => w - z) z := by
    refine DifferentiableAt.comp (g := fun ζ => f (z + ζ) - f z) z ?_ hsub
    simpa using hd0
  convert hcomp.add_const (f z) using 1
  funext w
  simp

/-- Auxiliary (module bridge B1, LiZhongQC → LV). For an open connected `U ⊆ ℂ`, a standard conformal map of the
plane quadrilateral `U(v)` onto `R(0, a, a + ib, ib)` in the project's sense (`LiZhongQC.IsStdConformalMap`: a
conformal `f : U → R` with the homeomorphic extension `F` of the closures in `ℂ̄`) gives, through `F`, a canonical
mapping of `(toExt U, v)` (`IsCanonicalMap`). With `LiZhongQC.thm1_1_exists_rectangle` it yields
`exists_canonicalMap` for quadrilaterals whose domain lies in `ℂ` (that target stays open: its domain may contain
`∞`). -/
theorem lv12_isCanonicalMap_of_isStdConformalMap {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {v : Fin 4 → ExtPlane} {a b : ℝ} {f : ℂ → ℂ} {F : ExtPlane → ExtPlane} (ha : 0 < a) (hb : 0 < b)
    (hf : LiZhongQC.IsConformalOnto f U (LiZhongQC.rectangle a b))
    (hF : LiZhongQC.IsHomeoExtension f U (LiZhongQC.rectangle a b) F)
    (hv : ∀ i, F (v i) = LiZhongQC.rectVert a b i) :
    IsCanonicalMap (toExt U) v a b F := by
  obtain ⟨hF1, hFc, hFi, hFim⟩ := hF
  have hUo : IsOpen (toExt U) := OnePoint.isOpen_image_coe.2 hU
  refine ⟨ha, hb, ⟨⟨hUo, hUc.image _ OnePoint.continuous_coe.continuousOn⟩, hFc.mono subset_closure,
    hFi.mono subset_closure, ?_⟩, ?_, ⟨hFc, hFi, hFim, ?_⟩, hv⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hfz : DifferentiableAt ℂ f z := (hf.1 z hz).differentiableAt (hU.mem_nhds hz)
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => z + ζ) 0 := (differentiableAt_const z).add differentiableAt_id
    have h2 : DifferentiableAt ℂ f (z + 0) := by
      rw [add_zero]
      exact hfz
    exact ((h2.comp (0 : ℂ) h1).sub_const (f z)).congr_of_eventuallyEq
      (lv12_localRep_coe_eventuallyEq hU hF1 hz)
  · show F '' (((↑) : ℂ → ExtPlane) '' U) = ((↑) : ℂ → ExtPlane) '' LiZhongQC.rectangle a b
    rw [← hf.2.2, image_image, image_image]
    exact image_congr hF1
  · have h := LiZhongQC.continuousOn_invFunOn_image_of_isCompact isClosed_closure.isCompact hFc hFi
    rwa [hFim] at h

/-- Auxiliary (module bridge B2, LV → LiZhongQC). A canonical mapping of `(toExt U, v)` (`U ⊆ ℂ`) restricts to a
standard conformal map of `U(v)` onto `R(0, a, a + ib, ib)`: `U(v)` is conformally equivalent to the rectangle in the
sense of `LiZhongQC.EquivRect`. -/
theorem lv12_equivRect_of_isCanonicalMap {U : Set ℂ} {v : Fin 4 → ExtPlane} {a b : ℝ}
    {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap (toExt U) v a b f) : LiZhongQC.EquivRect U v a b := by
  obtain ⟨ha, hb, ⟨⟨hUo, -⟩, -, hfi, hfd⟩, hfim, ⟨hFc, hFi, hFim, -⟩, hv⟩ := hf
  have hU : IsOpen U := OnePoint.isOpen_image_coe.1 hUo
  have hfin : ∀ z ∈ U, ∃ w ∈ LiZhongQC.rectangle a b, f (z : ExtPlane) = (w : ExtPlane) := by
    intro z hz
    have h : f (z : ExtPlane) ∈ toExt (LiZhongQC.rectangle a b) := hfim ▸ mem_image_of_mem f ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hw'⟩ := h
    exact ⟨w, hw, hw'.symm⟩
  set g : ℂ → ℂ := fun z => OnePoint.elim (f (z : ExtPlane)) 0 id with hg
  have hgF : ∀ z ∈ U, f (z : ExtPlane) = ((g z : ℂ) : ExtPlane) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hfin z hz
    rw [hg]
    simp only [hw]
    rfl
  refine ⟨g, ha, hb, ⟨fun z hz => ?_, fun z hz w hw h => ?_, ?_⟩, f, ⟨hgF, hFc, hFi, hFim⟩, hv⟩
  · exact (lv12_differentiableAt_of_localRep hU hgF hz (hfd _ ⟨z, hz, rfl⟩)).differentiableWithinAt
  · apply OnePoint.coe_injective
    apply hfi ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    rw [hgF z hz, hgF w hw, h]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w', hw', hfw⟩ := hfin z hz
      rw [hgF z hz] at hfw
      rwa [OnePoint.coe_injective hfw]
    · intro hw
      have h : (w : ExtPlane) ∈ f '' toExt U := hfim ▸ ⟨w, hw, rfl⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, hzw⟩ := h
      rw [hgF z hz] at hzw
      exact ⟨z, hz, OnePoint.coe_injective hzw⟩

/-- Auxiliary (module bridge B3: LV's module is the project's modulus). For an open connected `U ⊆ ℂ` and any
vertices `v`, `quadModule (toExt U) v = LiZhongQC.quadModulusOf U v`: the two sets of side ratios coincide by
`lv12_isCanonicalMap_of_isStdConformalMap` and `lv12_equivRect_of_isCanonicalMap`. This is the References ↔
LiZhongQC module bridge (used for `module_upperHalf_infty`, II.6.3, through `lv21_module_upperHalf`). -/
theorem lv12_quadModule_toExt {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) (v : Fin 4 → ExtPlane) :
    quadModule (toExt U) v = LiZhongQC.quadModulusOf U v := by
  unfold quadModule LiZhongQC.quadModulusOf
  congr 1
  ext m
  constructor
  · rintro ⟨a, b, f, hf, rfl⟩
    exact ⟨a, b, lv12_equivRect_of_isCanonicalMap hf, rfl⟩
  · rintro ⟨a, b, ⟨f, ha, hb, hf, F, hF, hv⟩, rfl⟩
    exact ⟨a, b, F, lv12_isCanonicalMap_of_isStdConformalMap hU hUc ha hb hf hF hv, rfl⟩

/-- Auxiliary (uniqueness of the canonical rectangle, §2.4, P1:361). Two canonical mappings of the same raw data
`(D, v)`, all vertices in `D̄`, give the same ratio `a/b = a'/b'`. The domain may contain `∞`: `f' ∘ f⁻¹` is a
homeomorphism of the closed rectangles, conformal off the single point `f(∞)` (removable singularity), and
`LiZhongQC.rect_rigidity` applies. Closes `module_eq_of_isCanonicalMap` and `module_rotate`. -/
theorem lv12_ratio_unique {D : Set ExtPlane} {v : Fin 4 → ExtPlane} (hv : ∀ i, v i ∈ closure D)
    {a b a' b' : ℝ} {f f' : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f)
    (hf' : IsCanonicalMap D v a' b' f') : a / b = a' / b' := by
  obtain ⟨ha, hb, ⟨⟨hDo, -⟩, -, -, hfd⟩, hfim, ⟨hFc, hFi, hFim, hFinvc⟩, hFv⟩ := hf
  obtain ⟨ha', hb', ⟨-, -, -, hfd'⟩, hfim', ⟨hFc', hFi', hFim', -⟩, hF'v⟩ := hf'
  set K := closure D with hK
  have hDK : D ⊆ K := subset_closure
  have hbdd : ∀ c d : ℝ, Bornology.IsBounded (LiZhongQC.rectangle c d) := fun c d => by
    rw [LiZhongQC.rectangle_eq_Ioo_reProdIm_Ioo]
    exact (Metric.isBounded_Ioo 0 c).reProdIm (Metric.isBounded_Ioo 0 d)
  have hRo : IsOpen (LiZhongQC.rectangle a b) := by
    rw [LiZhongQC.rectangle_eq_Ioo_reProdIm_Ioo]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hclR : closure (toExt (LiZhongQC.rectangle a b)) = toExt (closure (LiZhongQC.rectangle a b)) :=
    LiZhongQC.closure_toExt_eq_toExt_closure_of_isBounded (hbdd a b)
  have hclR' : closure (toExt (LiZhongQC.rectangle a' b')) = toExt (closure (LiZhongQC.rectangle a' b')) :=
    LiZhongQC.closure_toExt_eq_toExt_closure_of_isBounded (hbdd a' b')
  have hmemR : ∀ z ∈ closure (LiZhongQC.rectangle a b),
      (z : ExtPlane) ∈ closure (toExt (LiZhongQC.rectangle a b)) := fun z hz => by
    rw [hclR]
    exact mem_image_of_mem _ hz
  have hFinv_mem : ∀ w ∈ closure (toExt (LiZhongQC.rectangle a b)), Function.invFunOn f K w ∈ K :=
    fun w hw => by
      rw [← hFim] at hw
      exact Function.invFunOn_mem hw
  have hFFinv : ∀ w ∈ closure (toExt (LiZhongQC.rectangle a b)), f (Function.invFunOn f K w) = w :=
    fun w hw => by
      rw [← hFim] at hw
      exact Function.invFunOn_eq hw
  have hFinvF : ∀ p ∈ K, Function.invFunOn f K (f p) = p := fun p hp => hFi.leftInvOn_invFunOn hp
  -- finite values on `D`
  have hfin : ∀ p ∈ D, ∃ w ∈ LiZhongQC.rectangle a b, f p = (w : ExtPlane) := by
    intro p hp
    obtain ⟨w, hw, hw'⟩ : f p ∈ toExt (LiZhongQC.rectangle a b) := hfim ▸ mem_image_of_mem f hp
    exact ⟨w, hw, hw'.symm⟩
  have hfin' : ∀ p ∈ D, ∃ w ∈ LiZhongQC.rectangle a' b', f' p = (w : ExtPlane) := by
    intro p hp
    obtain ⟨w, hw, hw'⟩ : f' p ∈ toExt (LiZhongQC.rectangle a' b') := hfim' ▸ mem_image_of_mem f' hp
    exact ⟨w, hw, hw'.symm⟩
  -- the preimage of a point of the open rectangle lies in `D`
  have hinvD : ∀ w ∈ LiZhongQC.rectangle a b, Function.invFunOn f K (w : ExtPlane) ∈ D := by
    intro w hw
    obtain ⟨p, hp, hpw⟩ : (w : ExtPlane) ∈ f '' D := hfim ▸ mem_image_of_mem _ hw
    rw [← hpw, hFinvF p (hDK hp)]
    exact hp
  -- the composite `G = f' ∘ f⁻¹` of the closed rectangles
  have hGc : ContinuousOn (fun w => f' (Function.invFunOn f K w)) (closure (toExt (LiZhongQC.rectangle a b))) :=
    hFc'.comp hFinvc hFinv_mem
  have hGinj : InjOn (fun w => f' (Function.invFunOn f K w)) (closure (toExt (LiZhongQC.rectangle a b))) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 := hFi' (hFinv_mem w₁ hw₁) (hFinv_mem w₂ hw₂) heq
    rw [← hFFinv w₁ hw₁, ← hFFinv w₂ hw₂, h1]
  have hGimg : (fun w => f' (Function.invFunOn f K w)) '' closure (toExt (LiZhongQC.rectangle a b)) =
      closure (toExt (LiZhongQC.rectangle a' b')) := by
    rw [← hFim']
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hFinv_mem u hu, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨f p, ?_, ?_⟩
      · rw [← hFim]
        exact mem_image_of_mem f hp
      · show f' (Function.invFunOn f K (f p)) = f' p
        rw [hFinvF p hp]
  -- the induced map `g` of the closed rectangles in `ℂ`
  have hcoe : ∀ (q : ExtPlane) (w : ℂ), q = (w : ExtPlane) → Function.invFun ((↑) : ℂ → ExtPlane) q = w := by
    intro q w hqw
    apply OnePoint.coe_injective
    rw [Function.invFun_eq ⟨w, hqw.symm⟩, hqw]
  have hG_coe : ∀ z ∈ closure (LiZhongQC.rectangle a b), ∃ w ∈ closure (LiZhongQC.rectangle a' b'),
      f' (Function.invFunOn f K (z : ExtPlane)) = (w : ExtPlane) := by
    intro z hz
    have h1 : f' (Function.invFunOn f K (z : ExtPlane)) ∈ closure (toExt (LiZhongQC.rectangle a' b')) := by
      rw [← hGimg]
      exact mem_image_of_mem _ (hmemR z hz)
    rw [hclR'] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    exact ⟨w, hw, hwe.symm⟩
  set g : ℂ → ℂ := fun z => Function.invFun ((↑) : ℂ → ExtPlane) (f' (Function.invFunOn f K (z : ExtPlane)))
    with hg
  have hgG : ∀ z ∈ closure (LiZhongQC.rectangle a b), (g z : ExtPlane) = f' (Function.invFunOn f K (z : ExtPlane)) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hG_coe z hz
    rw [hw]
    exact congrArg _ (hcoe _ w hw)
  have hgc : ContinuousOn g (closure (LiZhongQC.rectangle a b)) := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    have h1 : ContinuousOn (fun z : ℂ => f' (Function.invFunOn f K (z : ExtPlane)))
        (closure (LiZhongQC.rectangle a b)) :=
      hGc.comp OnePoint.continuous_coe.continuousOn hmemR
    exact h1.congr fun z hz => hgG z hz
  have hginj : InjOn g (closure (LiZhongQC.rectangle a b)) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have h1 : f' (Function.invFunOn f K (z₁ : ExtPlane)) = f' (Function.invFunOn f K (z₂ : ExtPlane)) := by
      rw [← hgG z₁ hz₁, ← hgG z₂ hz₂, heq]
    exact OnePoint.coe_injective (hGinj (hmemR z₁ hz₁) (hmemR z₂ hz₂) h1)
  have hgimg : g '' closure (LiZhongQC.rectangle a b) = closure (LiZhongQC.rectangle a' b') := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hGw⟩ := hG_coe z hz
      rw [show g z = w from hcoe _ w hGw]
      exact hw
    · intro hw
      have h1 : (w : ExtPlane) ∈ (fun w => f' (Function.invFunOn f K w)) ''
          closure (toExt (LiZhongQC.rectangle a b)) := by
        rw [hGimg, hclR']
        exact mem_image_of_mem _ hw
      obtain ⟨p, hp, hpw⟩ := h1
      rw [hclR] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      exact ⟨z, hz, hcoe _ w hpw⟩
  -- the finite part of `D` and the plane maps `f₀`, `f'₀`
  set D₀ : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' D with hD₀
  have hD₀o : IsOpen D₀ := hDo.preimage OnePoint.continuous_coe
  set f₀ : ℂ → ℂ := fun z => Function.invFun ((↑) : ℂ → ExtPlane) (f (z : ExtPlane)) with hf₀
  set f'₀ : ℂ → ℂ := fun z => Function.invFun ((↑) : ℂ → ExtPlane) (f' (z : ExtPlane)) with hf'₀
  have hf₀e : ∀ z ∈ D₀, f (z : ExtPlane) = ((f₀ z : ℂ) : ExtPlane) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hfin _ hz
    rw [hw]
    exact congrArg _ (hcoe _ w hw).symm
  have hf'₀e : ∀ z ∈ D₀, f' (z : ExtPlane) = ((f'₀ z : ℂ) : ExtPlane) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hfin' _ hz
    rw [hw]
    exact congrArg _ (hcoe _ w hw).symm
  have hf₀d : DifferentiableOn ℂ f₀ D₀ := fun z hz =>
    (lv12_differentiableAt_of_localRep hD₀o hf₀e hz (hfd _ hz)).differentiableWithinAt
  have hf'₀d : DifferentiableOn ℂ f'₀ D₀ := fun z hz =>
    (lv12_differentiableAt_of_localRep hD₀o hf'₀e hz (hfd' _ hz)).differentiableWithinAt
  have hf₀i : InjOn f₀ D₀ := by
    intro z₁ hz₁ z₂ hz₂ heq
    apply OnePoint.coe_injective
    apply hFi (hDK hz₁) (hDK hz₂)
    rw [hf₀e z₁ hz₁, hf₀e z₂ hz₂, heq]
  set W := f₀ '' D₀ with hW
  have hinv := LiZhongQC.IsConformalOnto.symm hD₀o
    (show LiZhongQC.IsConformalOnto f₀ D₀ W from ⟨hf₀d, hf₀i, rfl⟩)
  -- membership in `W`
  have hWiff : ∀ w : ℂ, w ∈ W ↔ w ∈ LiZhongQC.rectangle a b ∧ Function.invFunOn f K (w : ExtPlane) ≠ extInf := by
    intro w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hfy⟩ := hfin _ hz
      have hy' : f₀ z = y := OnePoint.coe_injective ((hf₀e z hz).symm.trans hfy)
      refine ⟨hy' ▸ hy, ?_⟩
      rw [← hf₀e z hz, hFinvF _ (hDK hz)]
      exact OnePoint.coe_ne_infty z
    · rintro ⟨hw, hne⟩
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.1 hne
      have hzD : z ∈ D₀ := by
        show (z : ExtPlane) ∈ D
        rw [hz]
        exact hinvD w hw
      refine ⟨z, hzD, OnePoint.coe_injective ?_⟩
      rw [← hf₀e z hzD, hz, hFFinv _ (subset_closure (mem_image_of_mem _ hw))]
  have hWo : IsOpen W := by
    have h1 : IsOpen (toExt (LiZhongQC.rectangle a b) ∩
        Function.invFunOn f K ⁻¹' (D \ {extInf})) :=
      (hFinvc.mono subset_closure).isOpen_inter_preimage (OnePoint.isOpen_image_coe.2 hRo)
        (hDo.sdiff isClosed_singleton)
    have h2 : W = ((↑) : ℂ → ExtPlane) ⁻¹' (toExt (LiZhongQC.rectangle a b) ∩
        Function.invFunOn f K ⁻¹' (D \ {extInf})) := by
      ext w
      rw [hWiff]
      simp only [mem_preimage, mem_inter_iff, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hw, hne⟩
        exact ⟨mem_image_of_mem _ hw, hinvD w hw, hne⟩
      · rintro ⟨⟨y, hy, hyw⟩, -, hne⟩
        rw [OnePoint.coe_injective hyw] at hy
        exact ⟨hy, hne⟩
    rw [h2]
    exact h1.preimage OnePoint.continuous_coe
  -- `g = f'₀ ∘ f₀⁻¹` on `W`
  have hgW : EqOn g (f'₀ ∘ Function.invFunOn f₀ D₀) W := by
    rintro w ⟨z, hz, rfl⟩
    have hz' : Function.invFunOn f₀ D₀ (f₀ z) = z := hf₀i.leftInvOn_invFunOn hz
    show g (f₀ z) = f'₀ (Function.invFunOn f₀ D₀ (f₀ z))
    rw [hz']
    apply hcoe
    rw [← hf₀e z hz, hFinvF _ (hDK hz), hf'₀e z hz]
  have hdW : DifferentiableOn ℂ g W :=
    (hf'₀d.comp hinv.1 (fun w hw => Function.invFunOn_mem hw)).congr hgW
  -- `g` is holomorphic on the open rectangle (removable singularity at `f(∞)`)
  have hgd : DifferentiableOn ℂ g (LiZhongQC.rectangle a b) := by
    intro w hw
    by_cases hwW : w ∈ W
    · exact (hdW.differentiableAt (hWo.mem_nhds hwW)).differentiableWithinAt
    · have hinf : Function.invFunOn f K (w : ExtPlane) = extInf := by
        by_contra hne
        exact hwW ((hWiff w).2 ⟨hw, hne⟩)
      have hsub : LiZhongQC.rectangle a b \ {w} ⊆ W := by
        rintro y ⟨hy, hyw⟩
        by_contra hyW
        have hinf' : Function.invFunOn f K (y : ExtPlane) = extInf := by
          by_contra hne
          exact hyW ((hWiff y).2 ⟨hy, hne⟩)
        apply hyw
        apply OnePoint.coe_injective
        rw [← hFFinv _ (subset_closure (mem_image_of_mem _ hy)), hinf',
          ← hinf, hFFinv _ (subset_closure (mem_image_of_mem _ hw))]
      have hcont : ContinuousAt g w :=
        hgc.continuousAt (mem_of_superset (hRo.mem_nhds hw) subset_closure)
      exact ((differentiableOn_compl_singleton_and_continuousAt_iff (hRo.mem_nhds hw)).1
        ⟨hdW.mono hsub, hcont⟩ w hw)
  -- `g` maps the open rectangle onto the open rectangle
  have hgimg' : g '' LiZhongQC.rectangle a b = LiZhongQC.rectangle a' b' := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, hfy⟩ := hfin' _ (hinvD w hw)
      rw [show g w = y from hcoe _ y hfy]
      exact hy
    · intro hy
      obtain ⟨p, hp, hpy⟩ : (y : ExtPlane) ∈ f' '' D := hfim' ▸ mem_image_of_mem _ hy
      obtain ⟨w, hw, hfw⟩ := hfin p hp
      refine ⟨w, hw, hcoe _ y ?_⟩
      rw [← hfw, hFinvF p (hDK hp), hpy]
  have hgconf : LiZhongQC.IsConformalOnto g (LiZhongQC.rectangle a b) (LiZhongQC.rectangle a' b') :=
    ⟨hgd, hginj.mono subset_closure, hgimg'⟩
  -- the vertices
  have hvert : ∀ i : Fin 4, f' (Function.invFunOn f K (LiZhongQC.rectVert a b i)) = LiZhongQC.rectVert a' b' i := by
    intro i
    rw [← hFv i, hFinvF _ (hv i), hF'v i]
  have hv0 : LiZhongQC.rectVert a b 0 = ((0 : ℂ) : ExtPlane) := rfl
  have hv1 : LiZhongQC.rectVert a b 1 = (((a : ℝ) : ℂ) : ExtPlane) := rfl
  have hv2 : LiZhongQC.rectVert a b 2 = (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv3 : LiZhongQC.rectVert a b 3 = (((b : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv0' : LiZhongQC.rectVert a' b' 0 = ((0 : ℂ) : ExtPlane) := rfl
  have hv1' : LiZhongQC.rectVert a' b' 1 = (((a' : ℝ) : ℂ) : ExtPlane) := rfl
  have hv2' : LiZhongQC.rectVert a' b' 2 = (((a' : ℂ) + (b' : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv3' : LiZhongQC.rectVert a' b' 3 = (((b' : ℂ) * I : ℂ) : ExtPlane) := rfl
  have h0 : g 0 = 0 := hcoe _ 0 (by have := hvert 0; rwa [hv0, hv0'] at this)
  have h1 : g (a : ℂ) = (a' : ℂ) := hcoe _ _ (by have := hvert 1; rwa [hv1, hv1'] at this)
  have h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I :=
    hcoe _ _ (by have := hvert 2; rwa [hv2, hv2'] at this)
  have h3 : g ((b : ℂ) * I) = (b' : ℂ) * I := hcoe _ _ (by have := hvert 3; rwa [hv3, hv3'] at this)
  obtain ⟨hab, -⟩ := LiZhongQC.rect_rigidity ha hb ha' hb' hgconf hgc hginj hgimg h0 h1 h2 h3
  rw [div_eq_div_iff ha.ne' hb.ne'] at hab
  rw [div_eq_div_iff hb.ne' hb'.ne']
  linear_combination -hab

/-- Auxiliary. If `(D, v)` has a canonical mapping onto `R(0, a, a + ib, ib)` and all vertices lie in `D̄`, then
`quadModule D v = a/b` (the set in `quadModule` is `{a/b}` by `lv12_ratio_unique`). -/
theorem lv12_quadModule_eq {D : Set ExtPlane} {v : Fin 4 → ExtPlane} (hv : ∀ i, v i ∈ closure D)
    {a b : ℝ} {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f) : quadModule D v = a / b := by
  have hset : {m : ℝ | ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap D v a b f ∧ m = a / b} = {a / b} := by
    ext m
    constructor
    · rintro ⟨a', b', f', hf', rfl⟩
      exact (lv12_ratio_unique hv hf hf').symm
    · rintro rfl
      exact ⟨a, b, f, hf, rfl⟩
  unfold quadModule
  rw [hset, csSup_singleton]

/-- Auxiliary. Post-composing a canonical mapping onto `R(0, a, a + ib, ib)` with an affine map `z ↦ cz + d`
(`c ≠ 0`, read on `ℂ̄` as the Möbius map `LiZhongQC.mobiusExt c d 0 1`) carrying the rectangle onto
`R(0, a', a' + ib', ib')` gives a canonical mapping of `(D, v')` whenever the images of the vertices `v' i` are the
corners. Used for the rotations of `module_rotate`. -/
theorem lv12_isCanonicalMap_comp_affine {D : Set ExtPlane} {v v' : Fin 4 → ExtPlane} {a b a' b' : ℝ}
    {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f) {c d : ℂ} (hc : c ≠ 0) (ha' : 0 < a')
    (hb' : 0 < b') (himg : (fun z => c * z + d) '' LiZhongQC.rectangle a b = LiZhongQC.rectangle a' b')
    (hv' : ∀ i, LiZhongQC.mobiusExt c d 0 1 (f (v' i)) = LiZhongQC.rectVert a' b' i) :
    IsCanonicalMap D v' a' b' (LiZhongQC.mobiusExt c d 0 1 ∘ f) := by
  obtain ⟨ha, hb, ⟨hD, hfc, hfi, hfd⟩, hfim, ⟨hFc, hFi, hFim, -⟩, -⟩ := hf
  have hdet : c * 1 - d * 0 ≠ 0 := by simpa using hc
  set M := LiZhongQC.mobiusHomeomorph c d 0 1 hdet with hM
  have hMe : ∀ q, M q = LiZhongQC.mobiusExt c d 0 1 q := fun q => rfl
  have hMc : ∀ y : ℂ, LiZhongQC.mobiusExt c d 0 1 (y : ExtPlane) = ((c * y + d : ℂ) : ExtPlane) := by
    intro y
    rw [LiZhongQC.mobiusExt_coe (by simp)]
    simp [LiZhongQC.mobiusFn]
  have hMinf : LiZhongQC.mobiusExt c d 0 1 extInf = extInf := LiZhongQC.mobiusExt_infty_of_eq rfl
  -- the chart identity: `extChart (m w) (m q) = c * extChart w q` at a finite `w`
  have hchart : ∀ (w : ℂ) (q : ExtPlane), extChart (LiZhongQC.mobiusExt c d 0 1 (w : ExtPlane))
      (LiZhongQC.mobiusExt c d 0 1 q) = c * extChart (w : ExtPlane) q := by
    intro w q
    induction q using OnePoint.rec with
    | infty =>
      rw [hMc, hMinf]
      simp [extChart]
    | coe y =>
      rw [hMc, hMc]
      simp only [extChart, OnePoint.elim_some]
      ring
  have himgT : ∀ S : Set ℂ, LiZhongQC.mobiusExt c d 0 1 '' toExt S = toExt ((fun z => c * z + d) '' S) := by
    intro S
    unfold LiZhongQC.toExt
    rw [image_image, image_image]
    exact image_congr fun y _ => hMc y
  have himgE : (LiZhongQC.mobiusExt c d 0 1 ∘ f) '' closure D = closure (toExt (LiZhongQC.rectangle a' b')) := by
    rw [image_comp, hFim, ← himg, ← himgT]
    exact M.image_closure (toExt (LiZhongQC.rectangle a b))
  refine ⟨ha', hb', ⟨hD, M.continuous.comp_continuousOn hfc, M.injective.comp_injOn hfi, fun z hz => ?_⟩, ?_,
    ⟨M.continuous.comp_continuousOn hFc, M.injective.comp_injOn hFi, himgE, ?_⟩, hv'⟩
  · obtain ⟨w, -, hw⟩ : f z ∈ toExt (LiZhongQC.rectangle a b) := hfim ▸ mem_image_of_mem f hz
    have h : localRep (LiZhongQC.mobiusExt c d 0 1 ∘ f) z = fun ζ => c * localRep f z ζ := by
      funext ζ
      simp only [localRep, Function.comp]
      rw [← hw, hchart]
    rw [h]
    exact (hfd z hz).const_mul c
  · rw [image_comp, hfim, himgT, himg]
  · have h := LiZhongQC.continuousOn_invFunOn_image_of_isCompact (F := LiZhongQC.mobiusExt c d 0 1 ∘ f)
      isClosed_closure.isCompact (M.continuous.comp_continuousOn hFc) (M.injective.comp_injOn hFi)
    rwa [himgE] at h

/-- Auxiliary (the half-turn of the rectangle). A canonical mapping of `(D, v)` onto `R(0, a, a + ib, ib)` gives one
of `(D, (v₃, v₄, v₁, v₂))` onto the same rectangle, through `z ↦ -z + a + ib`. -/
theorem lv12_isCanonicalMap_rotate_two {D : Set ExtPlane} {v : Fin 4 → ExtPlane} {a b : ℝ}
    {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f) :
    ∃ g : ExtPlane → ExtPlane, IsCanonicalMap D (fun i => v (i + 2)) a b g := by
  have hfv := hf.2.2.2.2.2
  have hMc : ∀ y : ℂ, LiZhongQC.mobiusExt (-1) ((a : ℂ) + (b : ℂ) * I) 0 1 (y : ExtPlane) =
      ((-1 * y + ((a : ℂ) + (b : ℂ) * I) : ℂ) : ExtPlane) := fun y => by
    rw [LiZhongQC.mobiusExt_coe (by simp)]
    simp [LiZhongQC.mobiusFn]
  refine ⟨_, lv12_isCanonicalMap_comp_affine hf (c := -1) (d := (a : ℂ) + (b : ℂ) * I) (by norm_num) hf.1 hf.2.1 ?_
    fun i => ?_⟩
  · ext w
    simp only [mem_image, LiZhongQC.rectangle, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
      simp only [add_re, add_im, neg_mul, one_mul, neg_re, neg_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re,
        I_im]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨-w + (a + b * I), ⟨?_, ?_, ?_, ?_⟩, by ring⟩ <;>
        simp only [add_re, add_im, neg_re, neg_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im] <;>
        linarith
  · rw [hfv]
    fin_cases i
    · show LiZhongQC.mobiusExt (-1) ((a : ℂ) + (b : ℂ) * I) 0 1 (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) =
        ((0 : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring
    · show LiZhongQC.mobiusExt (-1) ((a : ℂ) + (b : ℂ) * I) 0 1 (((b : ℂ) * I : ℂ) : ExtPlane) =
        (((a : ℝ) : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring
    · show LiZhongQC.mobiusExt (-1) ((a : ℂ) + (b : ℂ) * I) 0 1 ((0 : ℂ) : ExtPlane) =
        (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring
    · show LiZhongQC.mobiusExt (-1) ((a : ℂ) + (b : ℂ) * I) 0 1 (((a : ℝ) : ℂ) : ExtPlane) =
        (((b : ℂ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring

/-- Auxiliary (the quarter-turn of the rectangle). A canonical mapping of `(D, v)` onto `R(0, a, a + ib, ib)` gives
one of `(D, (v₂, v₃, v₄, v₁))` onto `R(0, b, b + ia, ia)`, through `z ↦ -i(z - a)`. -/
theorem lv12_isCanonicalMap_rotate_one {D : Set ExtPlane} {v : Fin 4 → ExtPlane} {a b : ℝ}
    {f : ExtPlane → ExtPlane} (hf : IsCanonicalMap D v a b f) :
    ∃ g : ExtPlane → ExtPlane, IsCanonicalMap D (fun i => v (i + 1)) b a g := by
  have hfv := hf.2.2.2.2.2
  have hMc : ∀ y : ℂ, LiZhongQC.mobiusExt (-I) (I * (a : ℂ)) 0 1 (y : ExtPlane) =
      ((-I * y + I * (a : ℂ) : ℂ) : ExtPlane) := fun y => by
    rw [LiZhongQC.mobiusExt_coe (by simp)]
    simp [LiZhongQC.mobiusFn]
  refine ⟨_, lv12_isCanonicalMap_comp_affine hf (c := -I) (d := I * (a : ℂ)) (by simp) hf.2.1 hf.1 ?_ fun i => ?_⟩
  · ext w
    simp only [mem_image, LiZhongQC.rectangle, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
      simp only [add_re, add_im, neg_mul, neg_re, neg_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨I * w + a, ⟨?_, ?_, ?_, ?_⟩, by ring_nf; rw [I_sq]; ring⟩ <;>
        simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im] <;>
        linarith
  · rw [hfv]
    fin_cases i
    · show LiZhongQC.mobiusExt (-I) (I * (a : ℂ)) 0 1 (((a : ℝ) : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring
    · show LiZhongQC.mobiusExt (-I) (I * (a : ℂ)) 0 1 (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) =
        (((b : ℝ) : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    · show LiZhongQC.mobiusExt (-I) (I * (a : ℂ)) 0 1 (((b : ℂ) * I : ℂ) : ExtPlane) =
        (((b : ℂ) + (a : ℂ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    · show LiZhongQC.mobiusExt (-I) (I * (a : ℂ)) 0 1 ((0 : ℂ) : ExtPlane) = (((a : ℂ) * I : ℂ) : ExtPlane)
      rw [hMc]
      congr 1
      ring

/-- **Unlabelled** (Ch. I §2.4, P1:361). All canonical rectangles of a given quadrilateral `Q` have the same ratio of
sides `a/b = M(Q)`. -/
theorem module_eq_of_isCanonicalMap (Q : Quadrilateral) {a b : ℝ} {f : ExtPlane → ExtPlane}
    (hf : IsCanonicalMap Q.dom Q.vert a b f) : Q.module = a / b := by
  exact lv12_quadModule_eq (fun i => frontier_subset_closure (Q.vert_mem i)) hf

/-- **Unlabelled** (Ch. I §2.4, P1:365–367). `M(Q(z₁, z₂, z₃, z₄)) = M(Q(z₃, z₄, z₁, z₂)) = 1/M(Q(z₂, z₃, z₄, z₁))`.
-/
theorem module_rotate (Q : Quadrilateral) :
    quadModule Q.dom (fun i => Q.vert (i + 2)) = Q.module ∧
      quadModule Q.dom (fun i => Q.vert (i + 1)) = 1 / Q.module := by
  have hv : ∀ i, Q.vert i ∈ closure Q.dom := fun i => frontier_subset_closure (Q.vert_mem i)
  have hzero : ∀ w : Fin 4 → ExtPlane,
      (¬ ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom w a b f) → quadModule Q.dom w = 0 := by
    intro w hw
    have hset : {m : ℝ | ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom w a b f ∧ m = a / b} = ∅ := by
      ext m
      constructor
      · rintro ⟨a, b, f, hf, -⟩
        exact absurd ⟨a, b, f, hf⟩ hw
      · intro hm
        exact hm.elim
    unfold quadModule
    rw [hset, Real.sSup_empty]
  by_cases h : ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom Q.vert a b f
  · obtain ⟨a, b, f, hf⟩ := h
    obtain ⟨g₂, hg₂⟩ := lv12_isCanonicalMap_rotate_two hf
    obtain ⟨g₁, hg₁⟩ := lv12_isCanonicalMap_rotate_one hf
    rw [Quadrilateral.module, lv12_quadModule_eq hv hf, lv12_quadModule_eq (fun i => hv _) hg₂,
      lv12_quadModule_eq (fun i => hv _) hg₁, one_div_div]
    exact ⟨rfl, rfl⟩
  · -- No canonical mapping of `Q` exists. Mathematically this branch is vacuous (every quadrilateral has one,
    -- `exists_canonicalMap`, still open in this file); it only checks that both sides then take the same junk value
    -- (`sSup ∅ = 0` and `1 / 0 = 0`). It is not a proof through junk values.
    have h2 : ¬ ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom (fun i => Q.vert (i + 2)) a b f := by
      rintro ⟨a, b, f, hf⟩
      obtain ⟨g, hg⟩ := lv12_isCanonicalMap_rotate_two hf
      refine h ⟨a, b, g, ?_⟩
      convert hg using 2 with i
      fin_cases i <;> rfl
    have h1 : ¬ ∃ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom (fun i => Q.vert (i + 1)) a b f := by
      rintro ⟨a, b, f, hf⟩
      obtain ⟨g, hg⟩ := lv12_isCanonicalMap_rotate_one hf
      obtain ⟨g', hg'⟩ := lv12_isCanonicalMap_rotate_one hg
      obtain ⟨g'', hg''⟩ := lv12_isCanonicalMap_rotate_one hg'
      refine h ⟨b, a, g'', ?_⟩
      convert hg'' using 2 with i
      fin_cases i <;> rfl
    rw [Quadrilateral.module, hzero _ h, hzero _ h2, hzero _ h1, div_zero]
    exact ⟨rfl, rfl⟩

end LehtoVirtanen1973
