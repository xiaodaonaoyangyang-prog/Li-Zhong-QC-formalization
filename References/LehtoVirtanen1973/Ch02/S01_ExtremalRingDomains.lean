import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain
import LiZhongQC.Ch01.S05_ExtremalProblems

/-!
# Lehto–Virtanen, Chapter II §1: Ring domains with extremal module

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §1
(pp. 53–59; `full.md` P1:1517–1713).

Ring domains, their module `M(B)` (`ringModule`, with values in `(0, ∞]`) and separation are those of Chapter I
(§6.1, §1.3). The module `μ(r)` of Grötzsch's extremal domain is real and finite for `0 < r < 1`, the only range in
which it is used; a bound `M(B) ≤ μ(…)` is stated as `ringModule B ≤ ENNReal.ofReal (μ …)`. Points of the finite
plane are written `↑z`, and `∞` is `extInf`.

* Definition (Grötzsch's extremal domain `B(r)`, §1.1) — exists: `LiZhongQC.grotzschDomain` (a set of the finite
  plane, the unit disc slit along the segment from 0 to r; LV's B(r) is its image in the extended plane, which does
  not contain the point at infinity)
* Definition (the module `μ(r) = M(B(r))`, §1.1) — exists: `LiZhongQC.grotzschMu` (LV defines μ(r) = M(B(r)) with
  its ring module; the project's function is the doubly-connected modulus of the same planar ring, taken as a real
  number, which is finite for 0 < r < 1, the only range in which it is used)
* Grötzsch's module theorem (§1.1) — `grotzsch_module_theorem`
* Unlabelled (§1.1, P1:1538; recalled P1:1720, used P1:1776, cited P1:1898, 1904): a canonical mapping of `B(r)`
  onto `1 < |w| < e^{μ(r)}` symmetric in the real axis, the unit circle going to the outer circle —
  `grotzschDomain_symm_canonicalMap`
* Unlabelled (§1.1, P1:1556): `μ(r)` decreases with increasing `r` — exists: `LiZhongQC.grotzschMu_strictAntiOn`
  (strictly decreasing on the open unit interval)
* Definition (Teichmüller's extremal domain, §1.2) — `teichmullerExtremalDomain`
* Theorem 1.1 (§1.2) — `thm2_1_1_i`, `thm2_1_1_ii`
* Teichmüller's module theorem (§1.3) — `teichmuller_module_theorem`
* Koebe distortion formula (§1.3, quoted from Behnke–Sommer, p. 394) — exists: `LiZhongQC.koebe_growth_scaled`
  (the growth estimate for a holomorphic univalent function g of the unit disc with g(0) = 0, in the form applied in
  (1.4))
* Koebe's one-quarter theorem (§1.3, quoted) — exists: `LiZhongQC.koebe_quarter_of_not_mem` (the unnormalized form
  applied in (1.5): the derivative at 0 is at most 4 times the modulus of an omitted value)
* Theorem 1.2 (§1.4) — `thm2_1_2`
* Definition (Mori's extremal domain, §1.5) — `moriExtremalDomain`
* Mori's module theorem (§1.5) — `mori_module_theorem_i`, `mori_module_theorem_ii`

The claim of §1.1 that for connected `E₁`, `E₂` a component of the complement of `E₁ ∪ E₂` is doubly connected and
extremal (P1:1521; asserted without proof, footnote 15, and not used) is not stated; nor are the proof steps (1.1),
(1.3), (1.7)–(1.10), nor the explicit conformal maps through the Koebe function (P1:1605, used only in the proof). The
estimates (1.4) and (1.5) are the Koebe theorems indexed above; (1.2), (1.6) and (1.11) are parts of the theorems.
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius grotzschMu grotzschDomain)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §1.1 Grötzsch's module theorem -/

/-- **Grötzsch's module theorem** (Ch. II §1.1). Let `0 < r < 1`. If the ring domain `B` separates the points `0` and
`r` from the circle `|z| = 1`, then `M(B) ≤ μ(r)`. -/
theorem grotzsch_module_theorem {B : Set ExtPlane} (hB : IsRingDomain B) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (hsep : Separates B {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)} (toExt (Metric.sphere (0 : ℂ) 1))) :
    ringModule B ≤ ENNReal.ofReal (grotzschMu r) := by
  sorry

/-- **Unlabelled** (Ch. II §1.1, P1:1538; recalled P1:1720, used P1:1776, cited P1:1898 "cf. 1.1" and P1:1904). For
`0 < r < 1`, Grötzsch's extremal domain `B(r)` has a canonical mapping `f` onto the annulus `1 < |w| < e^{μ(r)}`
which is symmetric with respect to the real axis (`f(z̄) = \overline{f(z)}`, obtained by mapping the upper half and
reflecting) and under which the circle `|z| = 1` corresponds to the outer circle `|w| = e^{μ(r)}`. -/
theorem grotzschDomain_symm_canonicalMap {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
    ∃ f : ExtPlane → ExtPlane,
      IsCanonicalRingMap (toExt (grotzschDomain r)) f 1 (ENNReal.ofReal (Real.exp (grotzschMu r))) ∧
      (∀ z ∈ toExt (grotzschDomain r),
        f (OnePoint.map (starRingEnd ℂ) z) = OnePoint.map (starRingEnd ℂ) (f z)) ∧
      Corresponds f (toExt (grotzschDomain r)) (f '' toExt (grotzschDomain r)) (toExt (Metric.sphere 0 1))
        (toExt (Metric.sphere 0 (Real.exp (grotzschMu r)))) := by
  sorry

/-! ## §1.2 Teichmüller's extremal domain -/

/-- **Definition** (Teichmüller's extremal domain, Ch. II §1.2). For `r₁, r₂ > 0`, the plane slit along the real
axis from `-r₁` to `0` and from `r₂` to `∞`. The point `∞` lies on the second slit, so the domain is a set of the
finite plane. Meaningful for `r₁, r₂ > 0`, the only case used. -/
def teichmullerExtremalDomain (r₁ r₂ : ℝ) : Set ExtPlane :=
  toExt {z : ℂ | ¬(z.im = 0 ∧ ((-r₁ ≤ z.re ∧ z.re ≤ 0) ∨ r₂ ≤ z.re))}

/-- **Theorem 1.1** (Ch. II §1.2), inequality. If the ring domain `B` separates the points `0` and `-r₁ < 0` from the
points `r₂ > 0` and `∞`, then `M(B) ≤ 2μ(√(r₁/(r₁ + r₂)))` (1.2). -/
theorem thm2_1_1_i {B : Set ExtPlane} (hB : IsRingDomain B) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hsep : Separates B {((0 : ℂ) : ExtPlane), (((-r₁ : ℝ) : ℂ) : ExtPlane)} {((r₂ : ℂ) : ExtPlane), extInf}) :
    ringModule B ≤ ENNReal.ofReal (2 * grotzschMu (Real.sqrt (r₁ / (r₁ + r₂)))) := by
  sorry

/-- **Theorem 1.1** (Ch. II §1.2), equality case. Equality holds in (1.2) for Teichmüller's extremal domain: it is a
ring domain separating `0` and `-r₁` from `r₂` and `∞`, and its module is `2μ(√(r₁/(r₁ + r₂)))`.
Modelling: the admissibility of the extremal domain, which "equality holds in (1.2)" presupposes, is part of the
conclusion. -/
theorem thm2_1_1_ii {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    IsRingDomain (teichmullerExtremalDomain r₁ r₂) ∧
      Separates (teichmullerExtremalDomain r₁ r₂) {((0 : ℂ) : ExtPlane), (((-r₁ : ℝ) : ℂ) : ExtPlane)}
        {((r₂ : ℂ) : ExtPlane), extInf} ∧
      ringModule (teichmullerExtremalDomain r₁ r₂) = ENNReal.ofReal (2 * grotzschMu (Real.sqrt (r₁ / (r₁ + r₂)))) := by
  sorry

/-! ## §1.3 Teichmüller's module theorem -/

/-- **Teichmüller's module theorem** (Ch. II §1.3). If the ring domain `B` separates the points `0` and `z₁` from
`z₂` and `∞`, then `M(B) ≤ 2μ(√(|z₁|/(|z₁| + |z₂|)))`.
Modelling: `z₁ ≠ 0` (the book's "points `0` and `z₁`" are two points). For `z₁ = 0` the bound would be `2μ(0)`, a value
outside the range `0 < r < 1` of `μ`, while the annuli `ε < |z| < |z₂|` separate `0` from `z₂` and `∞` and have
arbitrarily large module. The separation gives `z₂ ≠ 0`, so the argument of `μ` lies in `(0, 1)`. -/
theorem teichmuller_module_theorem {B : Set ExtPlane} (hB : IsRingDomain B) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0)
    (hsep : Separates B {((0 : ℂ) : ExtPlane), (z₁ : ExtPlane)} {(z₂ : ExtPlane), extInf}) :
    ringModule B ≤ ENNReal.ofReal (2 * grotzschMu (Real.sqrt (‖z₁‖ / (‖z₁‖ + ‖z₂‖)))) := by
  sorry

/-! ## §1.4 Modification of Teichmüller's module theorem -/

/-- **Theorem 1.2** (Ch. II §1.4). If the ring domain `B` separates `z₁` and `z₂` from `0` and `∞`, then
`M(B) ≤ μ(|√z₁ - √z₂| / √(2(|z₁| + |z₂|)))` (1.6), where `√z₁` and `√z₂` belong to the same branch of the square
root, single-valued in `B`.
[OCR] The denominator is printed `√2 (|z₁| + |z₂|)`; the formula (1.8) (P1:1660) from which (1.6) is derived, and
its application in §3.4 (P1:2069), have `√(2(|z₁| + |z₂|))`.
Modelling: the branch is any `s`, continuous with `s(z)² = z` on the finite part of `G = ℂ̄ \ (-B)₂`, where `(-B)₂`
is the component of the complement of `B` containing `0` and `∞`: this is the book's proof domain, which contains
`B`, `z₁` and `z₂`, and a branch single-valued in `B` extends uniquely to it; the two branches `±s` give the same
bound. Hypothesis `z₁ ≠ z₂` (two points): for `z₁ = z₂` the bound would be `μ(0)`, outside the range of `μ`, while
small annuli around `z₁` have arbitrarily large module; for `z₁ ≠ z₂` the argument of `μ` lies in `(0, 1)`. -/
theorem thm2_1_2 {B : Set ExtPlane} (hB : IsRingDomain B) {z₁ z₂ : ℂ} (hz : z₁ ≠ z₂)
    (hsep : Separates B {(z₁ : ExtPlane), (z₂ : ExtPlane)} {((0 : ℂ) : ExtPlane), extInf}) {s : ℂ → ℂ}
    (hs : ContinuousOn s (finitePart (connectedComponentIn Bᶜ ((0 : ℂ) : ExtPlane))ᶜ))
    (hsq : ∀ z ∈ finitePart (connectedComponentIn Bᶜ ((0 : ℂ) : ExtPlane))ᶜ, s z ^ 2 = z) :
    ringModule B ≤ ENNReal.ofReal (grotzschMu (‖s z₁ - s z₂‖ / Real.sqrt (2 * (‖z₁‖ + ‖z₂‖)))) := by
  sorry

/-! ## §1.5 Mori's module theorem -/

/-- **Definition** (Mori's extremal domain, Ch. II §1.5). For `|z₁| = 1`, `|z₁ - 1| ≤ √2`, the ring domain whose
boundary consists of the half-line `x ≤ 0` (with `∞`) and the circular arc `{z : |z| = 1, |z - 1| ≤ |z₁ - 1|}`, with
end points `z₁` and `z̄₁`. Meaningful for `|z₁| = 1`, `0 < |z₁ - 1| ≤ √2`, the only case used (the arc then lies in
`Re z ≥ 0` and does not meet the half-line). -/
def moriExtremalDomain (z₁ : ℂ) : Set ExtPlane :=
  toExt {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ 0) ∧ ¬(‖z‖ = 1 ∧ ‖z - 1‖ ≤ ‖z₁ - 1‖)}

/-- **Mori's module theorem** (Ch. II §1.5), inequality. If the ring domain `B` separates the points `0` and `∞` from
the points `z₁` and `z₂` of the closed unit disc, then `M(B) ≤ μ(½√(2 - √(4 - |z₁ - z₂|²)))` (1.11).
Modelling: `z₁ ≠ z₂` (two points): for `z₁ = z₂` the bound would be `μ(0)`, outside the range of `μ`, while small
annuli around `z₁` have arbitrarily large module; for `z₁ ≠ z₂` the argument of `μ` lies in `(0, 1/√2]`. -/
theorem mori_module_theorem_i {B : Set ExtPlane} (hB : IsRingDomain B) {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ ≤ 1)
    (h₂ : ‖z₂‖ ≤ 1) (hz : z₁ ≠ z₂)
    (hsep : Separates B {((0 : ℂ) : ExtPlane), extInf} {(z₁ : ExtPlane), (z₂ : ExtPlane)}) :
    ringModule B ≤ ENNReal.ofReal (grotzschMu (Real.sqrt (2 - Real.sqrt (4 - ‖z₁ - z₂‖ ^ 2)) / 2)) := by
  sorry

/-- **Mori's module theorem** (Ch. II §1.5), equality case. Equality holds in (1.11) if `B` is Mori's extremal domain
and `z₁`, `z₂ = z̄₁` are the end points of its arc: the domain is a ring domain separating `0` and `∞` from `z₁` and
`z̄₁`, and its module is `μ(½√(2 - √(4 - |z₁ - z̄₁|²)))`.
Modelling: `z₁ ≠ 1` excludes the degenerate arc `{1}`; the admissibility of the extremal domain, which "equality
holds" presupposes, is part of the conclusion. -/
theorem mori_module_theorem_ii {z₁ : ℂ} (h₁ : ‖z₁‖ = 1) (h₀ : z₁ ≠ 1) (h₂ : ‖z₁ - 1‖ ≤ Real.sqrt 2) :
    IsRingDomain (moriExtremalDomain z₁) ∧
      Separates (moriExtremalDomain z₁) {((0 : ℂ) : ExtPlane), extInf}
        {(z₁ : ExtPlane), ((starRingEnd ℂ z₁ : ℂ) : ExtPlane)} ∧
      ringModule (moriExtremalDomain z₁) =
        ENNReal.ofReal (grotzschMu (Real.sqrt (2 - Real.sqrt (4 - ‖z₁ - starRingEnd ℂ z₁‖ ^ 2)) / 2)) := by
  sorry

/-! ## Auxiliary: the module of a half-plane quadrilateral with a vertex at `∞` (used in §2.1 and §6.3) -/

/-- Auxiliary. For real `x₁ < x₂ < x₃`, `ℍ(∞, x₁, x₂, x₃)` is a topological quadrilateral of the project
(`LiZhongQC.IsTopQuad`; the Möbius map `z ↦ -1/(z - x₁ + 1)` of `ℍ` sends the vertices to
`0, -1, -1/(x₂ - x₁ + 1), -1/(x₃ - x₁ + 1)`), as `LiZhongQC.isTopQuad_upperHalf_lambda` for `ℍ(∞, -1, 0, ρ)`. -/
theorem lv21_isTopQuad_upperHalf_infty {x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) :
    LiZhongQC.IsTopQuad LiZhongQC.upperHalf
      ![extInf, ((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane)] := by
  refine ⟨LiZhongQC.isJordanDomain_upperHalf, fun i => ?_, ?_⟩
  · fin_cases i
    · exact LiZhongQC.infty_mem_frontier_upperHalf
    · exact LiZhongQC.ofReal_mem_frontier_upperHalf x₁
    · exact LiZhongQC.ofReal_mem_frontier_upperHalf x₂
    · exact LiZhongQC.ofReal_mem_frontier_upperHalf x₃
  · have hdet : (0 : ℝ) < 0 * (1 - x₁) - (-1) * 1 := by norm_num
    have hS' : ((0 : ℝ) : ℂ) * ((1 - x₁ : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdet.ne'
    set e := LiZhongQC.mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((1 - x₁ : ℝ) : ℂ) hS'
      with he
    have heS : ∀ w ∈ LiZhongQC.upperHalf, e (w : ExtPlane) =
        ((LiZhongQC.mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((1 - x₁ : ℝ) : ℂ) w : ℂ) :
          ExtPlane) :=
      fun w hw => by
        rw [he, LiZhongQC.mobiusHomeomorph_apply]
        exact LiZhongQC.mobiusExt_coe (LiZhongQC.mobiusFn_den_ne_zero_real hdet.ne' hw)
    have himgS : e '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf := by
      rw [he]
      exact LiZhongQC.mobiusExt_image_toExt_upperHalf hdet
    have h2 : (-1 : ℝ) < -1 / (x₂ - x₁ + 1) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have h3 : (-1 / (x₂ - x₁ + 1) : ℝ) < -1 / (x₃ - x₁ + 1) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      linarith
    have h4 : (-1 / (x₃ - x₁ + 1) : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
    refine ⟨_, _, ![0, -1, -1 / (x₂ - x₁ + 1), -1 / (x₃ - x₁ + 1)],
      (LiZhongQC.isConformalOnto_mobius_upperHalf hdet).comp
        (LiZhongQC.isConformalOnto_id LiZhongQC.upperHalf),
      (LiZhongQC.isHomeoExtension_id LiZhongQC.upperHalf).comp_homeomorph
        (LiZhongQC.isConformalOnto_id LiZhongQC.upperHalf).mapsTo e heS himgS,
      ⟨1, Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩, fun i => ?_⟩
    · fin_cases i
      · exact h2
      · exact h3
      · exact h4
    · fin_cases i
      · show e extInf = (((0 : ℝ) : ℂ) : ExtPlane)
        rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_infty one_ne_zero]
        norm_num
      · show e ((x₁ : ℂ) : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane)
        rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_coe (by ring_nf; norm_num)]
        congr 2
        ring
      · show e ((x₂ : ℂ) : ExtPlane) = (((-1 / (x₂ - x₁ + 1) : ℝ) : ℂ) : ExtPlane)
        rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_coe (by linarith)]
        congr 2
        ring
      · show e ((x₃ : ℂ) : ExtPlane) = (((-1 / (x₃ - x₁ + 1) : ℝ) : ℂ) : ExtPlane)
        rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_coe (by linarith)]
        congr 2
        ring

/-- Auxiliary. For real `x₁ < x₂ < x₃`, `M(ℍ(∞, x₁, x₂, x₃)) = Λ((x₃ - x₂)/(x₂ - x₁))` in the project's sense: the
affine map `z ↦ (x₂ - x₁) z + x₂` carries `ℍ(∞, -1, 0, ρ)`, `ρ = (x₃ - x₂)/(x₂ - x₁)`, onto it
(`LiZhongQC.thm1_3_modulus_conformal_invariant`). -/
theorem lv21_quadModulusOf_upperHalf_infty {x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) :
    LiZhongQC.quadModulusOf LiZhongQC.upperHalf
        ![extInf, ((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane)] =
      LiZhongQC.quadLambda ((x₃ - x₂) / (x₂ - x₁)) := by
  have hρ : 0 < (x₃ - x₂) / (x₂ - x₁) := div_pos (by linarith) (by linarith)
  have h21 : x₂ - x₁ ≠ 0 := (sub_pos.2 h₁₂).ne'
  set Q₀ : LiZhongQC.TopQuad := ⟨LiZhongQC.upperHalf, _, LiZhongQC.isTopQuad_upperHalf_lambda hρ⟩ with hQ₀
  set Q₁ : LiZhongQC.TopQuad := ⟨LiZhongQC.upperHalf, _, lv21_isTopQuad_upperHalf_infty h₁₂ h₂₃⟩ with hQ₁
  have hconf : Q₀.ConfEquiv Q₁ := by
    have hdet : (0 : ℝ) < (x₂ - x₁) * 1 - x₂ * 0 := by linarith
    have hS' : ((x₂ - x₁ : ℝ) : ℂ) * ((1 : ℝ) : ℂ) - ((x₂ : ℝ) : ℂ) * ((0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdet.ne'
    set e := LiZhongQC.mobiusHomeomorph ((x₂ - x₁ : ℝ) : ℂ) ((x₂ : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((1 : ℝ) : ℂ) hS'
      with he
    have heS : ∀ w ∈ LiZhongQC.upperHalf, e (w : ExtPlane) =
        ((LiZhongQC.mobiusFn ((x₂ - x₁ : ℝ) : ℂ) ((x₂ : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((1 : ℝ) : ℂ) w : ℂ) :
          ExtPlane) :=
      fun w hw => by
        rw [he, LiZhongQC.mobiusHomeomorph_apply]
        exact LiZhongQC.mobiusExt_coe (LiZhongQC.mobiusFn_den_ne_zero_real hdet.ne' hw)
    have himgS : e '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf := by
      rw [he]
      exact LiZhongQC.mobiusExt_image_toExt_upperHalf hdet
    refine ⟨_, _, (LiZhongQC.isConformalOnto_mobius_upperHalf hdet).comp
        (LiZhongQC.isConformalOnto_id LiZhongQC.upperHalf),
      (LiZhongQC.isHomeoExtension_id LiZhongQC.upperHalf).comp_homeomorph
        (LiZhongQC.isConformalOnto_id LiZhongQC.upperHalf).mapsTo e heS himgS, fun i => ?_⟩
    fin_cases i
    · show e extInf = extInf
      rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_infty_of_eq (by simp)]
    · show e (((-1 : ℝ) : ℂ) : ExtPlane) = ((x₁ : ℂ) : ExtPlane)
      rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_coe (by norm_num)]
      congr 2
      ring
    · show e ((0 : ℂ) : ExtPlane) = ((x₂ : ℂ) : ExtPlane)
      rw [he, LiZhongQC.mobiusHomeomorph_apply, ← ofReal_zero,
        LiZhongQC.mobiusExt_ofReal_coe (by norm_num)]
      congr 2
      ring
    · show e ((((x₃ - x₂) / (x₂ - x₁) : ℝ) : ℂ) : ExtPlane) = ((x₃ : ℂ) : ExtPlane)
      rw [he, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_ofReal_coe (by norm_num)]
      congr 2
      have hm : (x₂ - x₁) * ((x₃ - x₂) / (x₂ - x₁)) = x₃ - x₂ := by field_simp
      rw [hm]
      ring
  exact (LiZhongQC.thm1_3_modulus_conformal_invariant hconf).symm

/-- Auxiliary (the module of `Q(x₁, x₂, x₃, ∞)`, LV II.2 / II.6.3). For real `x₁ < x₂ < x₃`, the upper half-plane
with the vertices `x₁, x₂, x₃, ∞` has the module `(2/π) μ(√((x₃ - x₂)/(x₃ - x₁)))`: the rotation of
`ℍ(∞, x₁, x₂, x₃)` (`LiZhongQC.thm1_2_modulus_rotate`), its modulus `Λ(ρ)` by (5.18), and (5.19), through the module
bridge `lv12_quadModule_toExt`. Proves `module_upperHalf_infty` (II.6.3) and serves `eq2_2_1` (II.2.1). -/
theorem lv21_module_upperHalf {x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) :
    quadModule (toExt LiZhongQC.upperHalf)
        ![((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane), extInf] =
      2 / Real.pi * grotzschMu (Real.sqrt ((x₃ - x₂) / (x₃ - x₁))) := by
  set Q₁ : LiZhongQC.TopQuad := ⟨LiZhongQC.upperHalf,
    ![extInf, ((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane)],
    lv21_isTopQuad_upperHalf_infty h₁₂ h₂₃⟩ with hQ₁
  have hrot : Q₁.rotate.vert = ![((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane), extInf] := by
    funext i
    fin_cases i <;> rfl
  have hM : quadModule (toExt LiZhongQC.upperHalf)
      ![((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane), extInf] = Q₁.rotate.modulus := by
    rw [lv12_quadModule_toExt LiZhongQC.isOpen_upperHalf LiZhongQC.isConnected_upperHalf, ← hrot]
    rfl
  have h1 : Q₁.modulus = LiZhongQC.quadLambda ((x₃ - x₂) / (x₂ - x₁)) :=
    lv21_quadModulusOf_upperHalf_infty h₁₂ h₂₃
  have h2 := LiZhongQC.thm1_2_modulus_rotate Q₁
  rw [hM]
  have hρ : 0 < (x₃ - x₂) / (x₂ - x₁) := div_pos (by linarith) (by linarith)
  have h21 : x₂ - x₁ ≠ 0 := (sub_pos.2 h₁₂).ne'
  have h31 : x₃ - x₁ ≠ 0 := (sub_pos.2 (h₁₂.trans h₂₃)).ne'
  have h3 := LiZhongQC.eq5_19 hρ
  have h1ρ : 1 + (x₃ - x₂) / (x₂ - x₁) = (x₃ - x₁) / (x₂ - x₁) := by
    field_simp
    ring
  have hr : 1 / (1 + (x₃ - x₂) / (x₂ - x₁)) = (x₂ - x₁) / (x₃ - x₁) := by
    rw [h1ρ, one_div_div]
  have hr' : (x₃ - x₂) / (x₂ - x₁) / (1 + (x₃ - x₂) / (x₂ - x₁)) = (x₃ - x₂) / (x₃ - x₁) := by
    rw [h1ρ]
    field_simp
  rw [hr, hr'] at h3
  rw [h1, LiZhongQC.eq5_18 hρ, hr] at h2
  have hπ := Real.pi_pos
  have hprod : 2 / Real.pi * grotzschMu (Real.sqrt ((x₃ - x₂) / (x₃ - x₁))) *
      (2 / Real.pi * grotzschMu (Real.sqrt ((x₂ - x₁) / (x₃ - x₁)))) = 1 := by
    rw [show 2 / Real.pi * grotzschMu (Real.sqrt ((x₃ - x₂) / (x₃ - x₁))) *
        (2 / Real.pi * grotzschMu (Real.sqrt ((x₂ - x₁) / (x₃ - x₁)))) =
        4 / Real.pi ^ 2 * (grotzschMu (Real.sqrt ((x₂ - x₁) / (x₃ - x₁))) *
          grotzschMu (Real.sqrt ((x₃ - x₂) / (x₃ - x₁)))) by ring, h3]
    field_simp
  rw [eq_one_div_of_mul_eq_one_left hprod, h2, one_div_one_div]


end LehtoVirtanen1973
