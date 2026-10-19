import References.LehtoVirtanen1973.Ch02.S09_CircularDilatation
import References.LehtoVirtanen1973.Ch04.S01_AnalyticProperties

/-!
# Lehto–Virtanen, Chapter IV §4: Characterization of quasiconformality with the help of the circular dilatation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. IV §4
(pp. 177–182; `full.md` P1:5539–5678).

Conventions. The circular dilatation `H` of a homeomorphism (II.9.1) is `circularDilatation w z : ℝ≥0∞`, read in
the charts of I.1.6 at `z = ∞` and where `w(z) = ∞`, as in the book; it may be infinite. A `K`-quasiconformal mapping
`w : G → G′` is `IsKQuasiconformal w G K` (Ch. I §3.2), with `G′ = w(G)`. "Almost everywhere in `G`" refers to the
area measure, which lives on the finite plane (III.1, footnote 32): `∀ᵐ z : ℂ ∂(volume.restrict (finitePart G))`, the
point `∞` being ignored.

* Theorem 4.1 (§4.1) — `thm4_4_1_i`, `thm4_4_1_ii`
* Theorem 4.2 (§4.2) — `thm4_4_2`
* Footnote 44 (§4.2: Theorem 4.2 with `H` finite only outside a set of σ-finite linear measure) — omitted: a
  sharpening formulated by Yûjôbô and proved only by reference (Gehring); not used later in the book (the
  footnote's cf. V.3.4 refers to Theorem V.3.2, proved independently)

Not stated (inventory: omitted): the remark of §4.2 (P1:5551) that `H(z) ≤ K` almost everywhere alone does not imply
quasiconformality, which rests on the example of §2.2; the closing remarks of §4.2 (P1:5675–5677) on the
characterization by the distortion of angles (Agard–Gehring, Taari) and on Volkovyskij's class (Näätänen), which
give references only. The discussion of §4.1 (P1:5545–5547) is the proof of Theorem 4.1. The numbered formulas
(4.1)–(4.6) are steps of the proof of Theorem 4.2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane)
open References (IsDomainExt finitePart)

/-! ## §4.1 Necessary conditions for the circular dilatation -/

/-- **Theorem 4.1** (Ch. IV §4.1), first half. The circular dilatation of a `K`-quasiconformal mapping `w : G → G′`
is bounded in `G`.
Modelling: "bounded" as printed: a finite real bound for `H` at every point of `G` (including `∞` and `w⁻¹(∞)`); that
the bound can be chosen depending only on `K` is Theorem II.9.1 (`thm2_9_1`). -/
theorem thm4_4_1_i {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    ∃ C : ℝ, ∀ z ∈ G, circularDilatation w z ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := thm2_9_1 K
  exact ⟨C, fun z hz => hC G w z hw hz⟩

/-- **Theorem 4.1** (Ch. IV §4.1), second half. The circular dilatation of a `K`-quasiconformal mapping `w : G → G′`
is at most equal to `K` almost everywhere in `G`. -/
theorem thm4_4_1_ii {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), circularDilatation w (z : ExtPlane) ≤ ENNReal.ofReal K := by
  obtain ⟨hG, hsp, hK⟩ := hw
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := lv13_isKQC_of_isKQuasiconformal ⟨hG, hsp, hK⟩
  have hq : IsQuasiconformalMap w G := ⟨hG, hsp, lt_of_le_of_lt hK ENNReal.ofReal_lt_top⟩
  have hreg := thm4_1_4 hq
  rw [lv41_restrict_eq hsp.1.2.1] at hreg ⊢
  -- at almost every point: regular (Theorem 1.4), so `H = D` (II §9.1), and `D ≤ K` by (1.5)
  filter_upwards [hreg, ae_restrict_mem hk.1.measurableSet, LiZhongQC.thm9_4_dilatation_ae hk,
    LiZhongQC.thm9_3_differentiable_ae hk] with z hz hzD hdil hd
  rw [circularDilatation_eq_dilQuot hsp.1 hz]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨-, hfin⟩ := hzD
  obtain ⟨-, -, hD, hJe⟩ := lv41_chart hz.2.1 hfin
  have hle := lv41_le_of_dil hk.2.1 (norm_nonneg _) hdil
  -- `J ≠ 0` at the regular point, so `|w_{\bar z}| < |w_z|`
  have hlt : ‖LiZhongQC.dzbar (finiteMap w) z‖ < ‖LiZhongQC.dz (finiteMap w) z‖ := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hz.2.2.2
      rw [hJe, LiZhongQC.det_fderiv_eq_jacobian hd, LiZhongQC.jacobian, h]
      ring
  obtain ⟨hsup, hinf⟩ := eq1_9_5 hd hle
  rw [hD, dilQuotient, hsup, hinf, div_le_iff₀ (sub_pos.2 hlt)]
  exact hdil

/-! ## §4.2 Sufficient conditions for the circular dilatation -/

/-- **Theorem 4.2** (Ch. IV §4.2). A sense-preserving homeomorphism `w : G → G′` is `K`-quasiconformal if its
circular dilatation is finite at every point of `G` and satisfies `H(z) ≤ K` almost everywhere in `G`.
Modelling: `G` is a domain of `ℂ̄` and `G′ = w(G)`; finiteness is required at every point of `G`, including `∞` and
`w⁻¹(∞)`. `1 ≤ K` is the book's standing `K ≥ 1` (harmonization H8): the circular dilatation of a homeomorphism is
at least `1` at every point, so for `K < 1` the hypothesis `H ≤ K` almost everywhere cannot hold on the nonempty open
finite part of `G`. -/
theorem thm4_4_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (hK : 1 ≤ K) (hfin : ∀ z ∈ G, circularDilatation w z < ⊤)
    (hH : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), circularDilatation w (z : ExtPlane) ≤ ENNReal.ofReal K) :
    IsKQuasiconformal w G K := by
  sorry

end LehtoVirtanen1973
