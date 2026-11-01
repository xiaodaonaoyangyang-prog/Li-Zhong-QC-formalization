import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC
import References.LehtoVirtanen1973.Ch03.S06_LpDerivatives
import References.LehtoVirtanen1973.Ch01.S09_LocalCharacterization

/-!
# Lehto–Virtanen, Chapter IV §1: Analytic properties of a quasiconformal mapping

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. IV §1
(pp. 162–166; `full.md` P1:5037–5184). The Introduction to Chapter IV (pp. 161–162, P1:5021–5035) announces results
of §1–§5 and contains no items of its own.

Conventions of Chapter IV. As in Chapter I, a quasiconformal mapping `w : G → G′` is a sense-preserving homeomorphism
of a domain `G` of `ℂ̄` (`IsQuasiconformalMap`, `IsKQuasiconformal`), given as a map `ExtPlane → ExtPlane` whose
values outside `G` do not matter, and `G′ = w(G)`. "Differentiable" refers to finite points with finite values (I.9):
`w` is differentiable at `z : ℂ` when its finite part `finiteMap w` is (real Fréchet differentiability), and
`∂_α w(z)` is `dirDeriv (finiteMap w) z α`; `max_α |∂_α w(z)|` and `min_α |∂_α w(z)|` are the supremum and the
infimum over `α` of `‖dirDeriv (finiteMap w) z α‖` (a bounded set of reals). The dilatation condition (1.5) is
stated in the book's form `max_α |∂_α w| ≤ K min_α |∂_α w|`, always together with the differentiability at the point,
so the value of the derivative at points of non-differentiability is never used. The Jacobian `J` is the book's
Jacobian from the partial derivatives, `partialJacobian (finiteMap w)` (III.3.3); at points of differentiability it
is the determinant of the derivative. The measure is the area measure of the finite plane: the area of a set `A` of
`ℂ̄` is that of its finite part `finitePart A` (III.4.1), "almost everywhere in `G`" is
`∀ᵐ z ∂(volume.restrict (finitePart G))` (the points `∞` and `w⁻¹(∞)` form a null set), and "measurable" is Lebesgue
measurability (`NullMeasurableSet` for `volume`). Absolute continuity on lines and `L^p`-derivatives of a mapping of a
domain of `ℂ̄` are the notions of III.3.1 and III.6.1 for the finite part of `w` on `G − {∞} − {w⁻¹(∞)}`.

* Definition (the set `G − {∞} − {w⁻¹(∞)}`; absolute continuity on lines and `L^p`-derivatives in a domain of `ℂ̄`,
  §1.1) — `finiteCore`, `IsACLExt`, `HasLpDerivativesExt`
* Lemma 1.1 (§1.1, Strebel, Mori) — `lemma4_1_1`
* Definition (horizontal rectangle, §1.1, Remark) — `Quadrilateral.IsHorizontalRectangle`
* Unlabelled (§1.1, P1:5101, Remark): the conclusion of Lemma 1.1 holds for every (sense-preserving) homeomorphism
  with `M(R)/K ≤ M(w(R)) ≤ K M(R)` for all horizontal rectangles `R`, `R̄ ⊂ G` —
  `isACL_of_horizontalRectangle_bound`
* Definition (the dilatation condition (1.5), §1.2) — omitted: terminology; the inequality is written out in every
  statement
* Theorem 1.1 (§1.2, Mori) — `thm4_1_1`
* Rademacher–Stepanoff theorem (§1.2, named) — omitted: named only in the historical note on the original proof of
  Theorem 1.1 (a reference to Saks), never stated or used in the book
* Formula (1.6) (§1.3) — `eq4_1_6`
* Theorem 1.2 (§1.3, Bers) — `thm4_1_2`
* Theorem 1.3 (§1.4, cf. Morrey) — `thm4_1_3`
* Unlabelled (§1.4, P1:5151): a quasiconformal mapping transforms area-measurable sets into area-measurable sets and
  preserves null sets — `qc_image_measurable`, `qc_image_null`
* Formula (1.8) (§1.4) — `eq4_1_8`
* Theorem 1.4 (§1.5) — `thm4_1_4`

Not stated (inventory: omitted): the remark that a `K`-quasiconformal mapping need not be absolutely continuous on
every closed segment (P1:5103, by II.8.10); the remark after Theorem 1.1 with footnote 40 (for regular mappings (1.5)
holds everywhere by definition); the identity `J = max_α |∂_α w| · min_α |∂_α w|` at points of differentiability
(P1:5121–5127, immediate from I (9.4)–(9.5) and `J ≥ 0`); formula (1.7) (P1:5136, not cited by number, immediate from
(1.6)); the remark on linear measure (P1:5161); the positivity of `J` almost everywhere (P1:5163, contained in
Theorem 1.4); the conditions (1.9) at regular points (P1:5169–5175, those of I.9.6, almost everywhere by Theorem 1.4);
and `D(z) ≤ K` almost everywhere (P1:5177–5183, a rewriting of (1.5) at the regular points of Theorem 1.4). The
numbered formulas (1.1)–(1.4) are steps of the proof of Lemma 1.1.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)

/-! ## §1.1 Absolute continuity on lines -/

/-- **Definition** (the set `G − {∞} − {w⁻¹(∞)}`, Ch. IV §1.1): the finite points of `G` at which `w` is finite, as a
subset of the finite plane. For a homeomorphism `w` of a domain `G` of `ℂ̄` it is a domain of the finite plane (at
most two points of `G` are removed). -/
def finiteCore (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Set ℂ :=
  {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}

/-- **Definition** (absolute continuity on lines in a domain of `ℂ̄`, Ch. IV §1.1). A homeomorphism `w` is absolutely
continuous on lines in the domain `G` if it is absolutely continuous on lines in the sense of III.3.1 in the domain
`G − {∞} − {w⁻¹(∞)}` of the finite plane.
Modelling: the notion of III.3.1 (continuity, and absolute continuity on almost all horizontal and vertical segments
of every closed rectangle in the set, `LiZhongQC.IsACL`) for the finite function `finiteMap w` on `finiteCore w G`.
The homeomorphism property is not part of the definition; every statement assumes it. -/
def IsACLExt (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  LiZhongQC.IsACL (finiteMap w) (finiteCore w G)

/-- **Definition** (`L^p`-derivatives in a domain of `ℂ̄`, Ch. IV §1.1). A homeomorphism `w` has `L^p`-derivatives in
the domain `G` if it has `L^p`-derivatives in the sense of III.6.1 in `G − {∞} − {w⁻¹(∞)}`.
Modelling: `HasLpDerivatives` (III.6.1) of the finite function `finiteMap w` on `finiteCore w G`; the exponent is
real, and the book's range is `p ≥ 1`. As for `IsACLExt`, the homeomorphism property is assumed by the statements. -/
def HasLpDerivativesExt (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (p : ℝ) : Prop :=
  HasLpDerivatives (finiteMap w) (finiteCore w G) p

/-- Helper (Tier 2). A quasiconformal mapping `w` of `G` is, on its finite core, a `K`-quasiconformal mapping in Li
Zhong's sense, with `K = K(G)` finite (`lv13_isKQC_of_isKQuasiconformal`). -/
theorem lv41_isKQC {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    ∃ K : ℝ, LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := by
  obtain ⟨hG, hsp, hlt⟩ := hw
  refine ⟨(maxDilatationK w G).toReal, lv13_isKQC_of_isKQuasiconformal ⟨hG, hsp, ?_⟩⟩
  rw [ENNReal.ofReal_toReal hlt.ne]

/-- **Lemma 1.1** (Ch. IV §1.1, Strebel, Mori). A quasiconformal mapping `w` of a domain `G` is absolutely continuous
on lines in `G`. (Cited at P2:217 as "Lemma IV.4.1", a misprint for IV.1.1.) -/
theorem lemma4_1_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    IsACLExt w G := by
  obtain ⟨K, hK⟩ := lv41_isKQC hw
  exact LiZhongQC.thm9_1_isACL hK

/-- **Definition** (horizontal rectangle, Ch. IV §1.1, Remark). A quadrilateral consisting of a rectangle and its
corners is called a horizontal rectangle if its a-sides are parallel to the `x`-axis.
Modelling: `Q` is the image of `R(0, a, a + ib, ib)`, whose a-sides `[0, a]` and `[ib, a + ib]` are horizontal, under
a mapping `z ↦ αz + β` with a real factor `α ≠ 0`. For `α > 0` the vertices are the corners
`x₁ + iy₁, x₂ + iy₁, x₂ + iy₂, x₁ + iy₂` of the rectangle `{x₁ < x < x₂, y₁ < y < y₂}`, for `α < 0` they are these
corners shifted by two; these are the two positively ordered labellings of a rectangle with sides parallel to the
axes whose a-sides are horizontal. -/
def Quadrilateral.IsHorizontalRectangle (Q : Quadrilateral) : Prop :=
  ∃ (a b α : ℝ) (β : ℂ), 0 < a ∧ 0 < b ∧ α ≠ 0 ∧
    Q.dom = toExt ((fun z => (α : ℂ) * z + β) '' LiZhongQC.rectangle a b) ∧
      ∀ i, Q.vert i = OnePoint.map (fun z => (α : ℂ) * z + β) (LiZhongQC.rectVert a b i)

/-- **Unlabelled** (Ch. IV §1.1, P1:5101, Remark after Lemma 1.1). The proof of Lemma 1.1 shows that its conclusion
holds for every homeomorphism `w` of the domain `G` which satisfies the dilatation condition
`M(R)/K ≤ M(w(R)) ≤ K M(R)` for all horizontal rectangles `R`, `R̄ ⊂ G`: such a `w` is absolutely continuous on lines
in `G`. (Cited in the proofs of Theorems 3.3 and 3.4, P1:5421, 5437.)
Modelling: `M(w(R))` is the module `quadModule (w '' R.dom) (w ∘ R.vert)` of the image quadrilateral with the
vertices `w(zᵢ)`, which is the book's module only when the image vertices are positively ordered; the hypothesis
"sense-preserving" is therefore added, as in Ch. I Theorem 8.3 (the book applies the claim to sense-preserving
mappings only, in 3.5 and 3.6). The inequalities are multiplied out. `1 ≤ K` is the book's standing `K ≥ 1`: for
`K < 1` the hypothesis on the horizontal rectangles is unsatisfiable. -/
theorem isACL_of_horizontalRectangle_bound {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hG : IsDomainExt G) (hw : IsSensePreservingOn w G) (hK : 1 ≤ K)
    (hR : ∀ R : Quadrilateral, R.IsHorizontalRectangle → closure R.dom ⊆ G →
      R.module ≤ K * quadModule (w '' R.dom) (w ∘ R.vert) ∧ quadModule (w '' R.dom) (w ∘ R.vert) ≤ K * R.module) :
    IsACLExt w G := by
  sorry

/-! ## §1.2 Differentiability and local dilatation conditions -/

/-- Helper (Tier 2). For `w` injective on `G`, the area measure on the finite part of `G` and on the finite core
`G − {∞} − {w⁻¹(∞)}` agree: the two sets differ by at most the one point `w⁻¹(∞)`. -/
theorem lv41_restrict_eq {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : InjOn w G) :
    volume.restrict (finitePart G) = volume.restrict (finiteCore w G) := by
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (t := {z : ℂ | (z : ExtPlane) ∈ G ∧ w z = extInf}) (fun z hz => ?_)
      (Set.Subsingleton.measure_zero (fun z hz z' hz' => ?_) _)
    · refine ⟨hz.1, ?_⟩
      by_contra h
      exact hz.2 ⟨hz.1, h⟩
    · exact OnePoint.coe_injective (hw hz.1 hz'.1 (hz.2.trans hz'.2.symm))
  · rw [sdiff_eq_empty.2 fun z (hz : z ∈ finiteCore w G) => hz.1, measure_empty]

/-- Helper (Tier 2). At a point of differentiability the book's Jacobian `u_x v_y − u_y v_x` (III.3.3) is
`det f′(z) = |f_z|² − |f_{\bar z}|²`. -/
theorem lv41_partialJacobian_eq {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ f z) :
    partialJacobian f z = LiZhongQC.jacobian f z := by
  rw [← LiZhongQC.det_fderiv_eq_jacobian hd, partialJacobian, LiZhongQC.partialX_eq_of_differentiableAt hd,
    LiZhongQC.partialY_eq_of_differentiableAt hd, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]

/-- Helper (Tier 2). `|f_z| + |f_{\bar z}| ≤ K(|f_z| − |f_{\bar z}|)` with `K ≥ 1` forces `|f_{\bar z}| ≤ |f_z|`. -/
theorem lv41_le_of_dil {a b K : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a) (h : a + b ≤ K * (a - b)) : b ≤ a := by
  by_contra hlt
  rw [not_le] at hlt
  have : K * (a - b) ≤ 1 * (a - b) := mul_le_mul_of_nonpos_right hK (by linarith)
  linarith

/-- **Theorem 1.1** (Ch. IV §1.2, Mori). A `K`-quasiconformal mapping `w` of the domain `G` is differentiable and
satisfies the dilatation condition `max_α |∂_α w(z)| ≤ K min_α |∂_α w(z)|` (1.5) at almost all points `z` of `G`.
Modelling: almost every point of `G` is a finite point with a finite image (the points `∞` and `w⁻¹(∞)` are null), at
which the book's differentiability is that of `finiteMap w` (I.9). -/
theorem thm4_1_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    ∀ᵐ z ∂(volume.restrict (finitePart G)), DifferentiableAt ℝ (finiteMap w) z ∧
      (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) ≤ K * ⨅ α : ℝ, ‖dirDeriv (finiteMap w) z α‖ := by
  obtain ⟨hG, hsp, hK⟩ := hw
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := lv13_isKQC_of_isKQuasiconformal ⟨hG, hsp, hK⟩
  rw [lv41_restrict_eq hsp.1.2.1]
  filter_upwards [LiZhongQC.thm9_3_differentiable_ae hk, LiZhongQC.thm9_4_dilatation_ae hk] with z hd hdil
  refine ⟨hd, ?_⟩
  have hle := lv41_le_of_dil hk.2.1 (norm_nonneg _) hdil
  obtain ⟨hsup, hinf⟩ := eq1_9_5 hd hle
  rw [hsup, hinf]
  exact hdil

/-! ## §1.3 `L²`-derivatives of a quasiconformal mapping -/

/-- **Formula (1.6)** (Ch. IV §1.3). A `K`-quasiconformal mapping `w` of `G` is differentiable and satisfies the
dilatation condition in the form `max_α |∂_α w(z)|² ≤ K J(z)` (1.6) at almost all points `z` of `G`. (The book
obtains (1.6) from (1.5) through `J = max_α |∂_α w| min_α |∂_α w|` at the points of differentiability, and cites it
later as "the dilatation condition (1.6)".)
Modelling: the Jacobian is `partialJacobian (finiteMap w)` (III.3.3), which at the points of differentiability
asserted here is the determinant of the derivative. The pointwise equivalence (1.5) ⇔ (1.6) at a point of
differentiability (used at P2:1755) is U−: it follows from `eq1_9_5` and `J = |w_z|² − |w_{\bar z}|²`. -/
theorem eq4_1_6 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    ∀ᵐ z ∂(volume.restrict (finitePart G)), DifferentiableAt ℝ (finiteMap w) z ∧
      (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) ^ 2 ≤ K * partialJacobian (finiteMap w) z := by
  obtain ⟨hG, hsp, hK⟩ := hw
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := lv13_isKQC_of_isKQuasiconformal ⟨hG, hsp, hK⟩
  rw [lv41_restrict_eq hsp.1.2.1]
  filter_upwards [LiZhongQC.thm9_3_differentiable_ae hk, LiZhongQC.thm9_4_dilatation_ae hk] with z hd hdil
  refine ⟨hd, ?_⟩
  have ha := norm_nonneg (LiZhongQC.dz (finiteMap w) z)
  have hb := norm_nonneg (LiZhongQC.dzbar (finiteMap w) z)
  have hle := lv41_le_of_dil hk.2.1 ha hdil
  rw [(eq1_9_5 hd hle).1, lv41_partialJacobian_eq hd, LiZhongQC.jacobian]
  -- `(a + b)² ≤ K (a − b)(a + b) = K (a² − b²)`
  have hm := mul_le_mul_of_nonneg_right hdil (add_nonneg ha hb)
  nlinarith [hm]

/-- **Theorem 1.2** (Ch. IV §1.3, Bers). A quasiconformal mapping of a domain `G` has `L²`-derivatives in `G`. -/
theorem thm4_1_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    HasLpDerivativesExt w G 2 := by
  obtain ⟨K, hK⟩ := lv41_isKQC hw
  refine ⟨LiZhongQC.thm9_1_isACL hK, fun C hC hCc => ?_⟩
  have h := (LiZhongQC.thm9_5_L2_derivatives hK).1.1 C hC hCc
  rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by simp]
  exact h

/-! ## §1.4 Absolute continuity with respect to the area measure -/

/-- Helper (Tier 3, area). For a quasiconformal `w` and a measurable set `t` in the finite core, the area of `f(t)`,
`f = finiteMap w`, is `∬_t J`: Li Zhong's Theorem 9.6 (`LiZhongQC.thm9_6_absolutelyContinuous`), with the book's
Jacobian `partialJacobian`, which equals Li Zhong's `jacobian` at the points of differentiability (almost all). -/
theorem lv41_volume_image_eq {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {t : Set ℂ} (ht : MeasurableSet t) (htD : t ⊆ finiteCore w G) :
    volume (finiteMap w '' t) = ∫⁻ z in t, ENNReal.ofReal (partialJacobian (finiteMap w) z) := by
  obtain ⟨K, hk⟩ := lv41_isKQC hw
  rw [LiZhongQC.thm9_6_absolutelyContinuous hk ht htD]
  -- the book's Jacobian is Li Zhong's at the points of differentiability (almost all)
  have hd : ∀ᵐ z ∂volume, z ∈ finiteCore w G → DifferentiableAt ℝ (finiteMap w) z :=
    (ae_restrict_iff' hk.1.measurableSet).1 (LiZhongQC.thm9_3_differentiable_ae hk)
  refine setLIntegral_congr_fun_ae ht ?_
  filter_upwards [hd] with z hz hzt
  rw [lv41_partialJacobian_eq (hz (htD hzt))]

/-- **Theorem 1.3** (Ch. IV §1.4, cf. Morrey). A quasiconformal mapping `w` of the domain `G` is locally absolutely
continuous (with respect to the area measure) in `G − {∞} − {w⁻¹(∞)}`.
Modelling: local absolute continuity of III.2.2 (`IsLocAbsContHomeo`, the area measure on both sides) of the
homeomorphism `finiteMap w` of the domain `finiteCore w G` of the finite plane. -/
theorem thm4_1_3 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    IsLocAbsContHomeo volume volume (finiteMap w) (finiteCore w G) := by
  obtain ⟨K', hk⟩ := lv41_isKQC hw
  intro C hC hCc ε hε
  -- `∬_C J = m(f(C)) < ∞`, and the integral is absolutely continuous
  have hfin : ∫⁻ z in C, ENNReal.ofReal (partialJacobian (finiteMap w) z) ≠ ⊤ := by
    rw [← lv41_volume_image_eq hw hCc.measurableSet hC]
    exact (hCc.image_of_continuousOn (hk.2.2.1.1.mono hC)).measure_lt_top.ne
  obtain ⟨δ', hδ', hδ⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin (ENNReal.ofReal_pos.2 hε).ne'
  obtain ⟨δ, -, hδpos, hδlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ'
  refine ⟨δ, ENNReal.ofReal_pos.1 hδpos, fun B hB hBC hBv => ?_⟩
  show volume (finiteMap w '' (B ∩ finiteCore w G)) < ENNReal.ofReal ε
  rw [inter_eq_left.2 (hBC.trans hC), lv41_volume_image_eq hw hB (hBC.trans hC)]
  have h1 : (volume.restrict C) B < δ' := by
    rw [Measure.restrict_apply hB]
    exact (measure_mono inter_subset_left).trans_lt (hBv.trans hδlt)
  have h2 := hδ B h1
  rwa [Measure.restrict_restrict hB, inter_eq_left.2 hBC] at h2

/-- Helper (Tier 2). For `A ⊆ G`, the finite part of `w(A)` lies in the image of `finitePart A ∩ finiteCore w G` under
`finiteMap w`, together with the one point `finiteValue (w ∞)`. -/
theorem lv41_finitePart_image_subset {w : ExtPlane → ExtPlane} {G A : Set ExtPlane} (hAG : A ⊆ G) :
    finitePart (w '' A) ⊆ finiteMap w '' (finitePart A ∩ finiteCore w G) ∪ {finiteValue (w extInf)} := by
  intro v hv
  obtain ⟨q, hqA, hqv⟩ := hv
  induction q using OnePoint.rec with
  | infty =>
    right
    show v = finiteValue (w extInf)
    rw [show w extInf = (v : ExtPlane) from hqv]
    rfl
  | coe z =>
    left
    refine ⟨z, ⟨hqA, hAG hqA, ?_⟩, ?_⟩
    · show w z ≠ extInf
      rw [hqv]
      exact OnePoint.coe_ne_infty v
    · show finiteValue (w z) = v
      rw [hqv]
      rfl

/-- **Unlabelled** (Ch. IV §1.4, P1:5151). A quasiconformal mapping of `G` transforms every area-measurable subset of
`G` into an area-measurable set.
Modelling: `A ⊆ G` is a set of `ℂ̄` (it may contain `∞` or `w⁻¹(∞)`); its area and its measurability are those of
its finite part (III.4.1), measurability being Lebesgue measurability. -/
theorem qc_image_measurable {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {A : Set ExtPlane} (hAG : A ⊆ G) (hA : NullMeasurableSet (finitePart A) volume) :
    NullMeasurableSet (finitePart (w '' A)) volume := by
  obtain ⟨K, hK⟩ := lv41_isKQC hw
  have hfc : ContinuousOn (finiteMap w) (finiteCore w G) := hK.2.2.1.1
  have hfi : InjOn (finiteMap w) (finiteCore w G) := hK.2.2.1.2.1
  set E := finitePart A ∩ finiteCore w G with hEdef
  have hEm : NullMeasurableSet E volume := hA.inter hK.1.measurableSet.nullMeasurableSet
  obtain ⟨t, htE, htm, hte⟩ := hEm.exists_measurable_subset_ae_eq
  -- `f(t)` is measurable (Lusin–Souslin), `f(E \ t)` is null (Lusin (N))
  have htD : t ⊆ finiteCore w G := htE.trans inter_subset_right
  have hft : MeasurableSet (finiteMap w '' t) := htm.image_of_continuousOn_injOn (hfc.mono htD) (hfi.mono htD)
  have hfEt : volume (finiteMap w '' (E \ t)) = 0 :=
    LiZhongQC.ac_n_volume_image_null_of_isKQC hK (sdiff_subset.trans inter_subset_right) (ae_eq_set.1 hte).2
  have hfE : NullMeasurableSet (finiteMap w '' E) volume := by
    have e : finiteMap w '' E = finiteMap w '' t ∪ finiteMap w '' (E \ t) := by
      rw [← image_union, union_sdiff_cancel htE]
    rw [e]
    exact hft.nullMeasurableSet.union (NullMeasurableSet.of_null hfEt)
  -- the finite part of `w(A)` is `f(E)` up to the point `finiteValue (w ∞)`
  have hsub : finiteMap w '' E ⊆ finitePart (w '' A) := by
    rintro _ ⟨z, ⟨hzA, -, hzf⟩, rfl⟩
    refine ⟨z, hzA, ?_⟩
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hzf
    show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
    rw [← hv]
    rfl
  have hS : finitePart (w '' A) = finiteMap w '' E ∪ (finitePart (w '' A) ∩ {finiteValue (w extInf)}) := by
    refine Subset.antisymm (fun v hv => ?_) (union_subset hsub inter_subset_left)
    rcases lv41_finitePart_image_subset hAG hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hv, h⟩
  rw [hS]
  exact hfE.union (NullMeasurableSet.of_null (measure_mono_null inter_subset_right (measure_singleton _)))

/-- **Unlabelled** (Ch. IV §1.4, P1:5151; cited P2:169, 271, "preserves null sets (see IV.1.4)"). A quasiconformal
mapping of `G` preserves null sets: every subset of `G` of area zero is mapped onto a set of area zero.
Modelling: as in `qc_image_measurable`. -/
theorem qc_image_null {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {A : Set ExtPlane} (hAG : A ⊆ G) (hA : volume (finitePart A) = 0) :
    volume (finitePart (w '' A)) = 0 := by
  obtain ⟨K, hK⟩ := lv41_isKQC hw
  have hE : volume (finitePart A ∩ finiteCore w G) = 0 := measure_mono_null inter_subset_left hA
  have h1 := LiZhongQC.ac_n_volume_image_null_of_isKQC hK inter_subset_right hE
  exact measure_mono_null (lv41_finitePart_image_subset hAG) (measure_union_null h1 (measure_singleton _))

/-- Helper (Tier 3, area). For `A ⊆ G` with a null-measurable finite part there is a measurable `t ⊆ finitePart A` in
the finite core such that `finitePart A \ t` is null and `finitePart (w(A))` is `f(t)` up to a null set
(`f = finiteMap w`; Lusin (N) for the null rest and the point `w(∞)`). -/
theorem lv41_measurable_core {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {A : Set ExtPlane} (hAG : A ⊆ G) (hA : NullMeasurableSet (finitePart A) volume) :
    ∃ t ⊆ finitePart A ∩ finiteCore w G, MeasurableSet t ∧ volume (finitePart A \ t) = 0 ∧
      finiteMap w '' t ⊆ finitePart (w '' A) ∧ volume (finitePart (w '' A) \ finiteMap w '' t) = 0 := by
  obtain ⟨K, hK⟩ := lv41_isKQC hw
  set E := finitePart A ∩ finiteCore w G with hEdef
  have hEm : NullMeasurableSet E volume := hA.inter hK.1.measurableSet.nullMeasurableSet
  obtain ⟨t, htE, htm, hte⟩ := hEm.exists_measurable_subset_ae_eq
  have hEt : volume (E \ t) = 0 := (ae_eq_set.1 hte).2
  refine ⟨t, htE, htm, ?_, ?_, ?_⟩
  · -- `finitePart A \ t` lies in `E \ t` and the at most one point `w⁻¹(∞)`
    have hsub : finitePart A \ t ⊆ (E \ t) ∪ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z = extInf} := by
      rintro z ⟨hzA, hzt⟩
      by_cases hz : w z = extInf
      · exact Or.inr ⟨hAG hzA, hz⟩
      · exact Or.inl ⟨⟨hzA, hAG hzA, hz⟩, hzt⟩
    refine measure_mono_null hsub (measure_union_null hEt ?_)
    refine Set.Subsingleton.measure_zero (fun z hz z' hz' => ?_) _
    exact OnePoint.coe_injective (hw.2.1.1.2.1 hz.1 hz'.1 (hz.2.trans hz'.2.symm))
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzA, -, hzf⟩ := htE hz
    refine ⟨z, hzA, ?_⟩
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hzf
    show w z = ((finiteValue (w z) : ℂ) : ExtPlane)
    rw [← hv]
    rfl
  · -- the rest of `finitePart (w(A))` lies in `f(E \ t)` (Lusin (N)) and the point `w(∞)`
    have hfEt : volume (finiteMap w '' (E \ t)) = 0 :=
      LiZhongQC.ac_n_volume_image_null_of_isKQC hK (sdiff_subset.trans inter_subset_right) hEt
    refine measure_mono_null (fun v hv => ?_) (measure_union_null hfEt (measure_singleton (finiteValue (w extInf))))
    obtain ⟨hvA, hvt⟩ := hv
    rcases lv41_finitePart_image_subset hAG hvA with ⟨z, hzE, rfl⟩ | h
    · exact Or.inl ⟨z, ⟨hzE, fun hzt => hvt ⟨z, hzt, rfl⟩⟩, rfl⟩
    · exact Or.inr h

/-- **Formula (1.8)** (Ch. IV §1.4, by Lemma III.3.3). A quasiconformal mapping `w` of `G` satisfies
`∬_A J dσ = m(w(A))` (1.8) for every measurable set `A ⊂ G`.
Modelling: `A ⊆ G` as in `qc_image_measurable`, and `J` as in `eq4_1_6`. Both sides are in `[0, ∞]` (the area of
`w(A)` may be infinite). The integrand `ofReal J` is the book's `J`, since `J ≥ 0` almost everywhere in `G`
(`eq4_1_6` with any finite `K ≥ K(G)`; also `J > 0` a.e. by Theorem 1.4 with Ch. I §1.6); the point `w⁻¹(∞)`,
where `finiteMap w` takes its junk value, is null. -/
theorem eq4_1_8 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {A : Set ExtPlane}
    (hAG : A ⊆ G) (hA : NullMeasurableSet (finitePart A) volume) :
    ∫⁻ z in finitePart A, ENNReal.ofReal (partialJacobian (finiteMap w) z) = volume (finitePart (w '' A)) := by
  obtain ⟨t, htE, htm, hAt, hft, hnull⟩ := lv41_measurable_core hw hAG hA
  have htA : t ⊆ finitePart A := htE.trans inter_subset_left
  have htD : t ⊆ finiteCore w G := htE.trans inter_subset_right
  -- both sides are their values on `t`, up to null sets
  have hL : ∫⁻ z in finitePart A, ENNReal.ofReal (partialJacobian (finiteMap w) z) =
      ∫⁻ z in t, ENNReal.ofReal (partialJacobian (finiteMap w) z) :=
    setLIntegral_congr (ae_eq_set.2 ⟨hAt, by rw [sdiff_eq_empty.2 htA, measure_empty]⟩)
  have hR : volume (finitePart (w '' A)) = volume (finiteMap w '' t) :=
    measure_congr (ae_eq_set.2 ⟨hnull, by rw [sdiff_eq_empty.2 hft, measure_empty]⟩)
  rw [hL, hR, lv41_volume_image_eq hw htm htD]

/-! ## §1.5 Regular points of a quasiconformal mapping -/

/-- Helper (Tier 3, finite-chart bridge). At a finite point `z` at which `w` is continuous and finite, the local
representation `localRep w z` (I.1.6) agrees near `0` with `ζ ↦ w(z + ζ) - w(z)`, read through `finiteMap`. -/
theorem lv41_localRep_eventuallyEq {w : ExtPlane → ExtPlane} {z : ℂ} (hc : ContinuousAt w z)
    (hfin : w z ≠ extInf) : localRep w z =ᶠ[𝓝 0] fun ζ => finiteMap w (z + ζ) - finiteMap w z := by
  -- `w(z + ζ)` is finite for `ζ` near `0`
  have hcont : ContinuousAt (fun ζ : ℂ => w ((z + ζ : ℂ) : ExtPlane)) 0 := by
    have h1 : ContinuousAt (fun ζ : ℂ => ((z + ζ : ℂ) : ExtPlane)) 0 :=
      (OnePoint.continuous_coe.comp (continuous_const.add continuous_id)).continuousAt
    have h2 : ContinuousAt w (((z + 0 : ℂ) : ExtPlane)) := by
      rw [add_zero]
      exact hc
    exact ContinuousAt.comp (g := w) h2 h1
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), w ((z + ζ : ℂ) : ExtPlane) ≠ extInf := by
    refine hcont.eventually_ne ?_
    show w ((z + 0 : ℂ) : ExtPlane) ≠ extInf
    rw [add_zero]
    exact hfin
  filter_upwards [hev] with ζ hζ
  obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hfin
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hζ
  show extChart (w z) (w (extChartInv z ζ)) = finiteValue (w ((z + ζ : ℂ) : ExtPlane)) - finiteValue (w z)
  have e : extChartInv (z : ExtPlane) ζ = ((z + ζ : ℂ) : ExtPlane) := rfl
  rw [e, ← hu, ← hv]
  rfl

/-- Helper (Tier 3, finite-chart bridge). At such a point the chart quantities of I.1.6 and I.3.3 are those of
`finiteMap w` at `z`: differentiability, the derivative, the dilatation quotient `D` and the Jacobian. -/
theorem lv41_chart {w : ExtPlane → ExtPlane} {z : ℂ} (hc : ContinuousAt w z) (hfin : w z ≠ extInf) :
    (DifferentiableAt ℝ (localRep w z) 0 ↔ DifferentiableAt ℝ (finiteMap w) z) ∧
      fderiv ℝ (localRep w z) 0 = fderiv ℝ (finiteMap w) z ∧ dilQuot w z = dilQuotient (finiteMap w) z ∧
        chartJacobian w z = LinearMap.det (fderiv ℝ (finiteMap w) z : ℂ →ₗ[ℝ] ℂ) := by
  have hev := lv41_localRep_eventuallyEq hc hfin
  have hfd : fderiv ℝ (localRep w z) 0 = fderiv ℝ (finiteMap w) z := by
    rw [hev.fderiv_eq, fderiv_sub_const, fderiv_comp_add_left, add_zero]
  refine ⟨?_, hfd, ?_, ?_⟩
  · rw [hev.differentiableAt_iff]
    simp only [sub_eq_add_neg, differentiableAt_add_const_iff]
    rw [differentiableAt_comp_add_left, add_zero]
  · simp only [dilQuot, dilQuotient, dirDeriv, hfd]
  · rw [chartJacobian, hfd]

/-- **Theorem 1.4** (Ch. IV §1.5). A quasiconformal mapping `w` of the domain `G` is regular at almost every point of
`G`.
Modelling: regular points in the sense of Ch. I §1.6 (`IsRegularPointOf`); at a finite point with a finite value this
is "`w` is differentiable at `z` and `J(z) ≠ 0`", that is `J(z) > 0` for the sense-preserving `w` (P1:5165). -/
theorem thm4_1_4 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    ∀ᵐ (z : ℂ) ∂(volume.restrict (finitePart G)), IsRegularPointOf w G z := by
  obtain ⟨K, hk⟩ := lv41_isKQC hw
  obtain ⟨hG, hsp, -⟩ := hw
  rw [lv41_restrict_eq hsp.1.2.1]
  filter_upwards [LiZhongQC.thm9_3_differentiable_ae hk, LiZhongQC.thm9_6_cor2_jacobian_pos hk,
    ae_restrict_mem hk.1.measurableSet] with z hd hJ hz
  obtain ⟨hzG, hfin⟩ := hz
  have hc : ContinuousAt w z := hsp.1.1.continuousAt (hG.1.mem_nhds hzG)
  obtain ⟨hdiff, -, -, hJe⟩ := lv41_chart hc hfin
  refine ⟨by rw [hG.1.interior_eq]; exact hzG, hc, hdiff.2 hd, ?_⟩
  rw [hJe, LiZhongQC.det_fderiv_eq_jacobian hd]
  exact hJ.ne'

end LehtoVirtanen1973
