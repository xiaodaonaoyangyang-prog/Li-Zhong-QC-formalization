import References.LehtoVirtanen1973.Ch02.S05_ConvergenceTheorems
import LiZhongQC.Ch03.S14_PoincareMetric
import LiZhongQC.Ch03.S15_Distortion
import References.LehtoVirtanen1973.Ch02.S02_GrotzschModule
import LiZhongQC.Ch04.S17_BoundaryValues

/-!
# Lehto–Virtanen, Chapter II §6: Boundary values of a quasiconformal mapping

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §6
(pp. 79–88; `full.md` P1:2367–2669).

Except in §6.6 the mappings are between Jordan domains of `ℂ̄`. By Theorem I.8.2 and the orientation theorem a
quasiconformal mapping `w : G → G′` then extends to a sense-preserving homeomorphism of the closures, whose values on
the boundary are the boundary values of `w` (P1:2373). In §6.3–6.5 the domains are the upper half-plane
`H = toExt LiZhongQC.upperHalf`, the mappings preserve `∞`, and the boundary values on the real axis form a real
function `φ`. `μ` is `LiZhongQC.grotzschMu` (II.1.1) and the distortion function `λ` is `LiZhongQC.lambdaInv`. The
double inequalities (6.1), (6.2), (6.6), (6.11) and the quotients of (6.5), (6.23) are multiplied out (every
denominator is positive).

* Definition (boundary values of a quasiconformal mapping; boundary homeomorphism preserving the positive orientation,
  §6.1) — `HasBoundaryValuesExt`, `IsOrientedBoundaryMap`
* Theorem 6.1 (§6.2) — `thm2_6_1_i`, `thm2_6_1_ii`
* Definition (boundary values `w(x) = φ(x)` of a self-mapping of the upper half-plane preserving `∞`, §6.3) —
  `HasRealBoundaryValues`
* Unlabelled (§6.3, P1:2403; the claim of §2.2, P1:1777–1779, used at P1:2083, cited P1:3171): the module of the
  quadrilateral `Q(x₁, x₂, x₃, ∞)` of the upper half-plane — `module_upperHalf_infty`
* Definition (the distortion function `λ(K)`, formula (6.4), §6.3) — exists: `LiZhongQC.lambdaInv` (LV defines
  λ(K) = 1/μ⁻¹(πK/2)² − 1 by (6.4), i.e. μ(1/√(1 + λ(K))) = πK/2. The project defines lambdaInv as the inverse of
  quadLambda, the module (2/π) μ(√(1/(1 + ρ))) of the half-plane quadrilateral with vertices ∞, −1, 0, ρ (eq5_18);
  so it is the same function as LV's λ on K > 0. LV uses λ(K) for K ≥ 1, and λ(1/K) in (6.5); the junk value 0 of
  lambdaInv is for K ≤ 0 only, where LV's formula is undefined, and no statement sees it; the identity (6.4) for
  lambdaInv follows from td_quadLambda_lambdaInv and eq5_18, stated as eq2_6_4 below)
* Formula (6.4) (§6.3, for the pointed `λ`; cited P1:3171–3174) — `eq2_6_4`
* Formula (6.5) (§6.3) — `eq2_6_5`
* Theorem 6.2 (§6.3) — `thm2_6_2`
* Unlabelled (§6.3, P1:2443): the inequality (6.6) is sharp — `thm2_6_2_sharp`
* Formula (6.7) (§6.4) — `eq2_6_7`
* Formula (6.10) (§6.4) — `eq2_6_10`
* Theorem 6.3 (§6.5, Beurling–Ahlfors) — `thm2_6_3`
* Theorem 6.4 (§6.6, Väisälä) — `thm2_6_4`
* Formula (6.23) (§6.6, footnote 22) — `eq2_6_23`

Not stated (inventory: omitted): (6.3) (P1:2409–2412, an intermediate form of (6.6)); the remark P1:2401 (U−, a proof
step: `G(x - t, x, x + t, ∞)` is conformally equivalent to a square); the functional equation of `μ⁻¹` (P1:2447–2450, a
step toward (6.7)); the values `λ(1) = 1`, `λ(2) = 16 + 12√2` and the remark on `λ(2ⁿ)` (P1:2461–2467, not cited); the
remark quoting the bounds `ϱ²` (Beurling–Ahlfors) and `8ϱ` (Reed) (P1:2605); the remark that a solution for `G`
restricts to one for `D ⊂ G` (P1:2611, immediate); the proof steps (6.8), (6.9), (6.12)–(6.22).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §6.1 Statement of the boundary value problem -/

/-- **Definition** (boundary values, Ch. II §6.1). The quasiconformal mapping `w : G → G′` has the boundary values `φ`
on the boundary of `G`: `w` extends to a homeomorphism `W` of `Ḡ` onto `Ḡ′` (Theorem I.8.2) which equals `φ` on
`Fr G`. The extension is unique (`G` is dense in `Ḡ`). The suffix `Ext` distinguishes the notion from the project's
`LiZhongQC.HasBoundaryValues` (self-mappings of the unit disc). -/
def HasBoundaryValuesExt (w : ExtPlane → ExtPlane) (G G' : Set ExtPlane) (φ : ExtPlane → ExtPlane) : Prop :=
  ∃ W : ExtPlane → ExtPlane, EqOn W w G ∧ IsHomeoOn W (closure G) (closure G') ∧ EqOn W φ (frontier G)

/-- **Definition** (boundary homeomorphism preserving the positive orientation, Ch. II §6.1, cf. I.1.4). `φ` is a
homeomorphism of the boundary `C` of `G` onto the boundary `C′` of `G′` which preserves the positive orientation: it
carries every triple of points of `C` giving the positive orientation with respect to `G` to a triple giving the
positive orientation of `C′` with respect to `G′`. -/
def IsOrientedBoundaryMap (G G' : Set ExtPlane) (φ : ExtPlane → ExtPlane) : Prop :=
  IsHomeoOn φ (frontier G) (frontier G') ∧
    ∀ p : Fin 3 → ExtPlane, IsPositivelyOrdered G p → IsPositivelyOrdered G' (φ ∘ p)

/-! ## §6.2 A general boundary condition -/

/-- **Theorem 6.1**, first part (Ch. II §6.2). Let `φ` be a homeomorphism between the boundaries of the Jordan domains
`G` and `G′` which preserves the positive orientation, and `Q = G(z₁, z₂, z₃, z₄)` a quadrilateral. If there exists a
`K`-quasiconformal mapping `w : G → G′` with the boundary values `φ`, then `M(Q)/K ≤ M(Q′) ≤ K M(Q)` (6.1) holds for
the quadrilateral `Q′ = G′(φ(z₁), φ(z₂), φ(z₃), φ(z₄))`.
Modelling: `Q′` is the quadrilateral with domain `G′` and vertices `φ(zᵢ)` (they are positively ordered, `φ`
preserving the orientation); (6.1) is multiplied out by `K`. -/
theorem thm2_6_1_i {G G' : Set ExtPlane} {φ : ExtPlane → ExtPlane} (hG : IsJordanDomainExt G)
    (hG' : IsJordanDomainExt G') (hφ : IsOrientedBoundaryMap G G' φ) {K : ℝ} {w : ExtPlane → ExtPlane}
    (hw : IsKQuasiconformal w G K) (hwG : w '' G = G') (hbv : HasBoundaryValuesExt w G G' φ)
    (Q Q' : Quadrilateral) (hQ : Q.dom = G) (hQ' : Q'.dom = G') (hv : Q'.vert = φ ∘ Q.vert) :
    Q.module ≤ K * Q'.module ∧ Q'.module ≤ K * Q.module := by
  sorry

/-- **Theorem 6.1**, converse part (Ch. II §6.2). Let `φ` be a homeomorphism between the boundaries of the Jordan
domains `G` and `G′` which preserves the positive orientation. If `1/K ≤ M(Q′) ≤ K` (6.2) holds for the family of
quadrilaterals `Q = G(z₁, z₂, z₃, z₄)` with unit module and fixed `z₄`, `Q′ = G′(φ(z₁), φ(z₂), φ(z₃), φ(z₄))`, then
there exists a quasiconformal mapping `w : G → G′` with the boundary values `φ` and with a maximal dilatation bounded
above by a number depending only on `K`.
Modelling: `∀ K, ∃ K′, ∀ G G′ φ z₄, …` (the bound depends only on `K`); `Q′` as in the first part; the fixed vertex
`z₄ = Q.vert 3` is a boundary point of `G` (a vertex; for `z₄ ∉ Fr G` the family would be empty and the claim false);
(6.2) is multiplied out by `K`. -/
theorem thm2_6_1_ii (K : ℝ) :
    ∃ K' : ℝ, ∀ (G G' : Set ExtPlane) (φ : ExtPlane → ExtPlane) (z₄ : ExtPlane),
      IsJordanDomainExt G → IsJordanDomainExt G' → IsOrientedBoundaryMap G G' φ → z₄ ∈ frontier G →
      (∀ Q Q' : Quadrilateral, Q.dom = G → Q'.dom = G' → Q'.vert = φ ∘ Q.vert → Q.vert 3 = z₄ → Q.module = 1 →
        1 ≤ K * Q'.module ∧ Q'.module ≤ K) →
      ∃ w : ExtPlane → ExtPlane, IsKQuasiconformal w G K' ∧ w '' G = G' ∧ HasBoundaryValuesExt w G G' φ := by
  sorry

/-! ## §6.3 Necessary condition for the half-plane -/

/-- **Definition** (boundary values on the real axis, Ch. II §6.3, §6.5). The self-mapping `w` of the upper half-plane
`H` preserving the point `∞` has the boundary values `w(x) = φ(x)`, `x` real: `w` extends to a homeomorphism `W` of the
closure `H̄ = H ∪ ℝ ∪ {∞}` onto itself with `W(∞) = ∞` and `W(x) = φ(x)` for every real `x`. -/
def HasRealBoundaryValues (w : ExtPlane → ExtPlane) (φ : ℝ → ℝ) : Prop :=
  ∃ W : ExtPlane → ExtPlane, EqOn W w (toExt LiZhongQC.upperHalf) ∧
    IsHomeoOn W (closure (toExt LiZhongQC.upperHalf)) (closure (toExt LiZhongQC.upperHalf)) ∧ W extInf = extInf ∧
      ∀ x : ℝ, W ((x : ℂ) : ExtPlane) = ((φ x : ℂ) : ExtPlane)

/-- Helper (WP6, W6-4; LZ ⇒ LV for the half-plane). Li Zhong's `K`-quasiconformal extensions with boundary values `φ`
(`LiZhongQC.HasQCExtensionH`, §17) give LV `K`-quasiconformal self-mappings of the upper half-plane with the real
boundary values `φ`. The homeomorphic extension `G` of the closed half-plane is `K`-quasiconformal in `ℍ` by the
converse bridge (`lv15_isKQuasiconformal_of_isKQC`): there `G = g` is finite, and its inverse is continuous on the
compact `H̄`. -/
theorem lv26_of_hasQCExtensionH {φ : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (h : LiZhongQC.HasQCExtensionH φ g K) :
    ∃ w : ExtPlane → ExtPlane, IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K ∧
      w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf ∧ HasRealBoundaryValues w φ := by
  obtain ⟨hk, himg, G, ⟨hGf, hGc, hGi, hGim⟩, hGinf, hGφ⟩ := h
  have hH : IsDomainExt (toExt LiZhongQC.upperHalf) :=
    (lv13_isJordanDomainExt_toExt LiZhongQC.isJordanDomain_upperHalf).1
  have hsub : toExt LiZhongQC.upperHalf ⊆ closure (toExt LiZhongQC.upperHalf) := subset_closure
  -- the finite core of `G` in `ℍ` is `ℍ`, where `finiteMap G = g`
  have hcore : {z : ℂ | (z : ExtPlane) ∈ toExt LiZhongQC.upperHalf ∧ G z ≠ extInf} = LiZhongQC.upperHalf := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, hue⟩, -⟩
      rw [← OnePoint.coe_injective hue]
      exact hu
    · intro hz
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [hGf z hz]
      exact OnePoint.coe_ne_infty _
  have hk' : LiZhongQC.IsKQC (finiteMap G) {z : ℂ | (z : ExtPlane) ∈ toExt LiZhongQC.upperHalf ∧ G z ≠ extInf} K := by
    rw [hcore]
    refine LiZhongQC.ad_isKQC_congr hk fun z hz => ?_
    show finiteValue (G z) = g z
    rw [hGf z hz]
    rfl
  refine ⟨G, lv15_isKQuasiconformal_of_isKQC hH (hGc.mono hsub) (hGi.mono hsub) hk', ?_, G, fun _ _ => rfl,
    ⟨hGc, hGi, hGim, ?_⟩, hGinf, hGφ⟩
  · -- `G(ℍ) = g(ℍ) = ℍ`
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hGf z hz]
      exact ⟨g z, himg ▸ mem_image_of_mem g hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rw [← himg] at hv
      obtain ⟨z, hz, rfl⟩ := hv
      exact ⟨z, ⟨z, hz, rfl⟩, hGf z hz⟩
  · -- the inverse is continuous on the compact `H̄`
    have h := LiZhongQC.continuousOn_invFunOn_image_of_isCompact isClosed_closure.isCompact hGc hGi
    rwa [hGim] at h

/-- Helper (WP6, W6-4; LV ⇒ LZ for the half-plane). An LV `K`-quasiconformal self-mapping `w` of the upper
half-plane with real boundary values `φ` gives Li Zhong's extension `HasQCExtensionH φ (finiteMap w) K`, through the
forward bridge (`lv13_isKQC_of_isKQuasiconformal`), as in the proof of `thm2_6_2`. -/
theorem lv26_hasQCExtensionH_of {w : ExtPlane → ExtPlane} {K : ℝ} {φ : ℝ → ℝ}
    (hw : IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K)
    (hwH : w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf) (hφ : HasRealBoundaryValues w φ) :
    LiZhongQC.HasQCExtensionH φ (finiteMap w) K := by
  obtain ⟨W, hWw, hWh, hWinf, hWφ⟩ := hφ
  have hk := lv13_isKQC_of_isKQuasiconformal hw
  -- `w` is finite on `ℍ`, so its finite core there is `ℍ` and `finiteMap w` maps `ℍ` onto `ℍ`
  have hfinH : ∀ z ∈ LiZhongQC.upperHalf, ∃ v ∈ LiZhongQC.upperHalf, w z = (v : ExtPlane) := fun z hz => by
    have h : w z ∈ toExt LiZhongQC.upperHalf := hwH ▸ mem_image_of_mem w ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hve⟩ := h
    exact ⟨v, hv, hve.symm⟩
  have hval : ∀ z ∈ LiZhongQC.upperHalf, ∀ v : ℂ, w z = (v : ExtPlane) → finiteMap w z = v := fun z _ v hv => by
    show finiteValue (w z) = v
    rw [hv]
    rfl
  have hcore : {z : ℂ | (z : ExtPlane) ∈ toExt LiZhongQC.upperHalf ∧ w z ≠ extInf} = LiZhongQC.upperHalf := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, hue⟩, -⟩
      rw [← OnePoint.coe_injective hue]
      exact hu
    · intro hz
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      obtain ⟨v, -, hv⟩ := hfinH z hz
      rw [hv]
      exact OnePoint.coe_ne_infty v
  rw [hcore] at hk
  have himg : finiteMap w '' LiZhongQC.upperHalf = LiZhongQC.upperHalf := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hue⟩ := hfinH z hz
      rw [hval z hz u hue]
      exact hu
    · intro hv
      have h : (v : ExtPlane) ∈ w '' toExt LiZhongQC.upperHalf := by
        rw [hwH]
        exact ⟨v, hv, rfl⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, hze⟩ := h
      exact ⟨z, hz, hval z hz v hze⟩
  refine ⟨hk, himg, W, ⟨fun z hz => ?_, hWh.1, hWh.2.1, hWh.2.2.1⟩, hWinf, hWφ⟩
  obtain ⟨v, -, hv⟩ := hfinH z hz
  rw [hWw ⟨z, hz, rfl⟩, hval z hz v hv, hv]

/-- Helper (WP6, W6-4). A continuous strictly increasing `φ` satisfying (6.11) with the constant `ϱ` is
`ϱ`-quasisymmetric in Li Zhong's sense (Definition 17.1). (6.11) is the two-sided bound of the quotient, and
`φ(x) → ±∞` as `x → ±∞` by doubling: `φ(2t) - φ(0) ≥ (1 + 1/ϱ)(φ(t) - φ(0))`. -/
theorem lv26_isQuasisymmetric {φ : ℝ → ℝ} {ϱ : ℝ} (hc : Continuous φ) (hm : StrictMono φ)
    (h : ∀ x t : ℝ, 0 < t → φ x - φ (x - t) ≤ ϱ * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ ϱ * (φ x - φ (x - t))) :
    LiZhongQC.IsQuasisymmetric φ ϱ := by
  have hpos : ∀ x t : ℝ, 0 < t → 0 < φ x - φ (x - t) ∧ 0 < φ (x + t) - φ x := fun x t ht =>
    ⟨sub_pos.2 (hm (by linarith)), sub_pos.2 (hm (by linarith))⟩
  have hϱ : 0 < ϱ := by
    obtain ⟨h1, -⟩ := h 0 1 one_pos
    obtain ⟨ha, hb⟩ := hpos 0 1 one_pos
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hb.le
    linarith
  have hq : 1 < 1 + ϱ⁻¹ := lt_add_of_pos_right 1 (inv_pos.2 hϱ)
  -- doubling to the right and to the left
  have hright : ∀ t : ℝ, 0 < t → (1 + ϱ⁻¹) * (φ t - φ 0) ≤ φ (2 * t) - φ 0 := fun t ht => by
    obtain ⟨h1, -⟩ := h t t ht
    rw [sub_self, show t + t = 2 * t by ring] at h1
    have h2 : ϱ⁻¹ * (φ t - φ 0) ≤ φ (2 * t) - φ t := by
      rw [inv_mul_le_iff₀ hϱ]
      exact h1
    linarith
  have hleft : ∀ t : ℝ, 0 < t → (1 + ϱ⁻¹) * (φ 0 - φ (-t)) ≤ φ 0 - φ (-(2 * t)) := fun t ht => by
    obtain ⟨-, h1⟩ := h (-t) t ht
    rw [neg_add_cancel, show -t - t = -(2 * t) by ring] at h1
    have h2 : ϱ⁻¹ * (φ 0 - φ (-t)) ≤ φ (-t) - φ (-(2 * t)) := by
      rw [inv_mul_le_iff₀ hϱ]
      exact h1
    linarith
  have hgrow : ∀ n : ℕ, (1 + ϱ⁻¹) ^ n * (φ 1 - φ 0) ≤ φ (2 ^ n) - φ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 := hright (2 ^ n) (by positivity)
      rw [pow_succ, mul_assoc, show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring]
      calc (1 + ϱ⁻¹) ^ n * ((1 + ϱ⁻¹) * (φ 1 - φ 0)) = (1 + ϱ⁻¹) * ((1 + ϱ⁻¹) ^ n * (φ 1 - φ 0)) := by ring
        _ ≤ (1 + ϱ⁻¹) * (φ (2 ^ n) - φ 0) := by gcongr
        _ ≤ φ (2 * 2 ^ n) - φ 0 := h2
  have hgrow' : ∀ n : ℕ, (1 + ϱ⁻¹) ^ n * (φ 0 - φ (-1)) ≤ φ 0 - φ (-(2 ^ n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 := hleft (2 ^ n) (by positivity)
      rw [pow_succ, mul_assoc, show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring]
      calc (1 + ϱ⁻¹) ^ n * ((1 + ϱ⁻¹) * (φ 0 - φ (-1))) = (1 + ϱ⁻¹) * ((1 + ϱ⁻¹) ^ n * (φ 0 - φ (-1))) := by
            ring
        _ ≤ (1 + ϱ⁻¹) * (φ 0 - φ (-(2 ^ n))) := by gcongr
        _ ≤ φ 0 - φ (-(2 * 2 ^ n)) := h2
  have hd1 : 0 < φ 1 - φ 0 := by simpa using (hpos 0 1 one_pos).2
  have hd2 : 0 < φ 0 - φ (-1) := by simpa using (hpos 0 1 one_pos).1
  refine ⟨hm, hc, hm.monotone.tendsto_atTop_atTop fun b => ?_, hm.monotone.tendsto_atBot_atBot fun b => ?_,
    fun x t ht => ?_⟩
  · obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_ge_atTop ((b - φ 0) / (φ 1 - φ 0))).exists
    refine ⟨2 ^ n, ?_⟩
    have := hgrow n
    rw [div_le_iff₀ hd1] at hn
    linarith
  · obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_ge_atTop ((φ 0 - b) / (φ 0 - φ (-1)))).exists
    refine ⟨-(2 ^ n), ?_⟩
    have := hgrow' n
    rw [div_le_iff₀ hd2] at hn
    linarith
  · obtain ⟨ha, hb⟩ := hpos x t ht
    obtain ⟨h1, h2⟩ := h x t ht
    rw [LiZhongQC.qsRatio]
    constructor
    · rw [inv_le_iff_one_le_mul₀' hϱ, ← mul_div_assoc, le_div_iff₀ ha, one_mul]
      exact h1
    · rw [div_le_iff₀ ha]
      exact h2

/-- Helper (WP6, W6-4). A `K`-quasiconformal self-mapping `f` of `ℍ` whose homeomorphic extension `F` to `H̄` fixes `∞`
has the real boundary values `x ↦ Re F(x)`: `F` maps `H̄ − ℍ = ℝ ∪ {∞}` onto itself and, being one-to-one, the real
axis onto the real axis. -/
theorem lv26_hasQCExtensionH_of_homeoExt {f : ℂ → ℂ} {F : ExtPlane → ExtPlane} {K : ℝ}
    (hf : LiZhongQC.IsKQC f LiZhongQC.upperHalf K) (himg : f '' LiZhongQC.upperHalf = LiZhongQC.upperHalf)
    (hF : LiZhongQC.IsHomeoExtension f LiZhongQC.upperHalf LiZhongQC.upperHalf F) (hinf : F extInf = extInf) :
    LiZhongQC.HasQCExtensionH (fun x => (finiteValue (F ((x : ℂ) : ExtPlane))).re) f K := by
  obtain ⟨hFf, hFc, hFi, hFim⟩ := hF
  refine ⟨hf, himg, F, ⟨hFf, hFc, hFi, hFim⟩, hinf, fun x => ?_⟩
  have hxcl : (((x : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt LiZhongQC.upperHalf) :=
    LiZhongQC.wd_b_real_mem_closure_upper x
  have hFx : F (((x : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt LiZhongQC.upperHalf) := by
    rw [← hFim]
    exact mem_image_of_mem F hxcl
  -- `F(x)` is neither `∞ = F(∞)` nor a point `F(z) = f(z)` of `ℍ` (`F` is one-to-one on `H̄`)
  have hne : F (((x : ℝ) : ℂ) : ExtPlane) ≠ extInf := fun h0 =>
    OnePoint.coe_ne_infty _ (hFi hxcl LiZhongQC.wd_b_infty_mem_closure_upper (h0.trans hinf.symm))
  have hnotH : ∀ z ∈ LiZhongQC.upperHalf, F (((x : ℝ) : ℂ) : ExtPlane) ≠ (z : ExtPlane) := by
    intro z hz hzx
    rw [← himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 := hFi (subset_closure ⟨y, hy, rfl⟩) hxcl ((hFf y hy).trans hzx.symm)
    have h2 : y = ((x : ℝ) : ℂ) := OnePoint.coe_injective h1
    have h3 : (0 : ℝ) < y.im := hy
    rw [h2, Complex.ofReal_im] at h3
    exact lt_irrefl 0 h3
  rcases LiZhongQC.wd_b_closure_upper_cases hFx with h0 | ⟨y, hy⟩ | ⟨z, hz, hzx⟩
  · exact absurd h0 hne
  · show F (((x : ℝ) : ℂ) : ExtPlane) = ((((finiteValue (F (((x : ℝ) : ℂ) : ExtPlane))).re : ℝ) : ℂ) : ExtPlane)
    rw [hy]
    show (((y : ℝ) : ℂ) : ExtPlane) = (((((y : ℝ) : ℂ)).re : ℝ) : ℂ)
    rw [Complex.ofReal_re]
  · exact absurd hzx (hnotH z hz)

/-- Helper (WP6, W6-4). Reflection in the imaginary axis: if `g` is a `K`-quasiconformal extension with boundary
values `φ`, then `z ↦ -conj(g(-conj z))` is one with boundary values `x ↦ -φ(-x)` (`LiZhongQC.abR_x_isKQC_conj`,
composed with the conformal `z ↦ -z`). -/
theorem lv26_reflect_hasQCExtensionH {φ : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (h : LiZhongQC.HasQCExtensionH φ g K) :
    LiZhongQC.HasQCExtensionH (fun x => -φ (-x)) (fun z => -(starRingEnd ℂ) (g (-(starRingEnd ℂ) z))) K := by
  obtain ⟨hk, himg, G, ⟨hGf, hGc, hGi, hGim⟩, hGinf, hGφ⟩ := h
  -- the reflection `r(z) = -z̄` of `ℂ̄`, a homeomorphism preserving `ℍ`
  set e : ℂ ≃ₜ ℂ :=
    { toFun := fun z => -(starRingEnd ℂ) z
      invFun := fun z => -(starRingEnd ℂ) z
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      continuous_toFun := (continuous_conj).neg
      continuous_invFun := (continuous_conj).neg } with he
  set r : ExtPlane → ExtPlane := ⇑e.onePointCongr with hr
  have hrc : ∀ z : ℂ, r z = ((-(starRingEnd ℂ) z : ℂ) : ExtPlane) := fun z => rfl
  have hrr : ∀ q, r (r q) = q := fun q => e.onePointCongr.symm_apply_apply q
  have hrH : ∀ z : ℂ, z ∈ LiZhongQC.upperHalf → -(starRingEnd ℂ) z ∈ LiZhongQC.upperHalf := fun z hz => by
    show (0 : ℝ) < (-(starRingEnd ℂ) z).im
    rw [Complex.neg_im, Complex.conj_im, neg_neg]
    exact hz
  have hrimg : r '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf := by
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, hrH z hz, (hrc z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨r z, ⟨_, hrH z hz, (hrc z).symm⟩, hrr _⟩
  have hrcl : r '' closure (toExt LiZhongQC.upperHalf) = closure (toExt LiZhongQC.upperHalf) := by
    rw [e.onePointCongr.image_closure, hrimg]
  have hmaps : MapsTo r (closure (toExt LiZhongQC.upperHalf)) (closure (toExt LiZhongQC.upperHalf)) := by
    rintro q hq
    rw [← hrcl]
    exact mem_image_of_mem r hq
  have hGmaps : MapsTo G (closure (toExt LiZhongQC.upperHalf)) (closure (toExt LiZhongQC.upperHalf)) := by
    rintro q hq
    rw [← hGim]
    exact mem_image_of_mem G hq
  -- `g' = -conj ∘ g ∘ (-conj)` is `K`-q.c. in `ℍ`: `conj ∘ g ∘ conj` (`abR_x_isKQC_conj`) between two maps `z ↦ -z`
  have hneg1 : LiZhongQC.IsKQC (fun z : ℂ => -z) LiZhongQC.upperHalf 1 :=
    LiZhongQC.isKQC_one_of_conformal LiZhongQC.isOpen_upperHalf
      ⟨differentiable_neg.differentiableOn, neg_injective.injOn, rfl⟩
  have hneg2 : LiZhongQC.IsKQC (fun z : ℂ => -z) univ 1 :=
    LiZhongQC.isKQC_one_of_conformal isOpen_univ ⟨differentiable_neg.differentiableOn, neg_injective.injOn, rfl⟩
  have hc := LiZhongQC.abR_x_isKQC_conj hk
  have hsub1 : (fun z : ℂ => -z) '' LiZhongQC.upperHalf ⊆ (starRingEnd ℂ) ⁻¹' LiZhongQC.upperHalf := by
    rintro _ ⟨z, hz, rfl⟩
    show (0 : ℝ) < ((starRingEnd ℂ) (-z)).im
    rw [Complex.conj_im, Complex.neg_im, neg_neg]
    exact hz
  have h12 := LiZhongQC.thm7_1_comp hneg1 hc hsub1
  have h123 := LiZhongQC.thm7_1_comp h12 hneg2 (subset_univ _)
  rw [one_mul, mul_one] at h123
  refine ⟨LiZhongQC.ad_isKQC_congr h123 fun z _ => ?_, ?_, fun q => r (G (r q)),
    ⟨fun z hz => ?_, ?_, ?_, ?_⟩, ?_, fun x => ?_⟩
  · simp [map_neg]
  · -- `g'(ℍ) = ℍ`
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : g (-(starRingEnd ℂ) z) ∈ LiZhongQC.upperHalf := himg ▸ mem_image_of_mem g (hrH z hz)
      exact hrH _ h1
    · intro hv
      have h1 : -(starRingEnd ℂ) v ∈ g '' LiZhongQC.upperHalf := himg.symm ▸ hrH v hv
      obtain ⟨z, hz, hzv⟩ := h1
      refine ⟨-(starRingEnd ℂ) z, hrH z hz, ?_⟩
      show -(starRingEnd ℂ) (g (-(starRingEnd ℂ) (-(starRingEnd ℂ) z))) = v
      rw [show -(starRingEnd ℂ) (-(starRingEnd ℂ) z) = z by simp, hzv]
      simp
  · show r (G (r z)) = _
    rw [hrc, hGf _ (hrH z hz), hrc]
  · exact (e.onePointCongr.continuous.comp_continuousOn (hGc.comp e.onePointCongr.continuous.continuousOn hmaps))
  · intro p hp q hq hpq
    exact hrr p ▸ hrr q ▸ congrArg r (hGi (hmaps hp) (hmaps hq) (e.onePointCongr.injective hpq))
  · rw [show (fun q => r (G (r q))) = r ∘ G ∘ r from rfl, image_comp, image_comp, hrcl, hGim, hrcl]
  · show r (G (r extInf)) = extInf
    have h1 : r extInf = extInf := rfl
    rw [h1, hGinf, h1]
  · show r (G (r (((x : ℝ) : ℂ) : ExtPlane))) = (((-φ (-x) : ℝ) : ℂ) : ExtPlane)
    rw [hrc, show -(starRingEnd ℂ) ((x : ℝ) : ℂ) = (((-x : ℝ)) : ℂ) by simp, hGφ, hrc]
    congr 1
    simp

/-- **Unlabelled** (Ch. II §6.3, P1:2403, "by 1.2"). For real `x₁ < x₂ < x₃`, the quadrilateral `Q(x₁, x₂, x₃, ∞)`
consisting of the upper half-plane and these vertices has the module `M(Q) = (2/π) μ(√((x₃ - x₂)/(x₃ - x₁)))` (used in
(6.3) and in the proofs of Theorems 3.2 and 9.2).
Modelling: for every quadrilateral with this domain and these vertices (they are positively ordered). -/
theorem module_upperHalf_infty {x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) (Q : Quadrilateral)
    (hQ : Q.dom = toExt LiZhongQC.upperHalf)
    (hv : Q.vert = ![((x₁ : ℂ) : ExtPlane), ((x₂ : ℂ) : ExtPlane), ((x₃ : ℂ) : ExtPlane), extInf]) :
    Q.module = 2 / Real.pi * LiZhongQC.grotzschMu (Real.sqrt ((x₃ - x₂) / (x₃ - x₁))) := by
  rw [Quadrilateral.module, hQ, hv]
  exact lv21_module_upperHalf h₁₂ h₂₃

/-- **Formula (6.4)** (Ch. II §6.3, for the pointed `λ`; P1:2418–2421, cited P1:3171–3174). For `K > 0`, `λ(K)` is
positive and `μ(1/√(1 + λ(K))) = πK/2`, i.e. `λ(K) = 1/μ⁻¹(πK/2)² - 1`, LV's definition of `λ`. -/
theorem eq2_6_4 {K : ℝ} (hK : 0 < K) :
    0 < LiZhongQC.lambdaInv K ∧
      LiZhongQC.grotzschMu (Real.sqrt (1 / (1 + LiZhongQC.lambdaInv K))) = Real.pi * K / 2 := by
  obtain ⟨h0, h1⟩ := LiZhongQC.td_quadLambda_lambdaInv hK
  refine ⟨h0, ?_⟩
  rw [LiZhongQC.eq5_18 h0] at h1
  set m := LiZhongQC.grotzschMu (Real.sqrt (1 / (1 + LiZhongQC.lambdaInv K)))
  have hπ := Real.pi_pos
  calc m = Real.pi / 2 * (2 / Real.pi * m) := by field_simp
    _ = Real.pi * K / 2 := by rw [h1]; ring

/-- **Formula (6.5)** (Ch. II §6.3). `λ(1/K) = 1/λ(K)`.
Modelling: for `K > 0`, where (6.4) defines `λ(K)` and `λ(1/K)`; multiplied out, `λ(1/K) λ(K) = 1` (`λ(K) > 0`). -/
theorem eq2_6_5 {K : ℝ} (hK : 0 < K) : LiZhongQC.lambdaInv (1 / K) * LiZhongQC.lambdaInv K = 1 := by
  obtain ⟨h0, h1⟩ := LiZhongQC.td_quadLambda_lambdaInv hK
  have h2 := LiZhongQC.eq5_20 h0
  rw [h1] at h2
  rw [(eq_one_div_of_mul_eq_one_right h2).symm, LiZhongQC.lambdaInv_quadLambda (one_div_pos.mpr h0)]
  exact one_div_mul_cancel h0.ne'

/-- **Theorem 6.2** (Ch. II §6.3). The boundary values of a `K`-quasiconformal self-mapping `w` of the upper half-plane
preserving the point `∞` satisfy the double inequality `1/λ(K) ≤ (w(x + t) - w(x))/(w(x) - w(x - t)) ≤ λ(K)` (6.6)
for all real `x` and `t`, `t ≠ 0`.
Modelling: `φ` is the boundary function on the real axis (`HasRealBoundaryValues`). Stated for `t > 0`: the quotient
at `-t` is the reciprocal of the quotient at `t`, and the range `[1/λ(K), λ(K)]` is closed under reciprocals. Multiplied
out: `φ` is increasing, so both differences are positive, and `λ(K) > 0` (a `K`-quasiconformal mapping has
`K ≥ 1`, I.3.1). -/
theorem thm2_6_2 {w : ExtPlane → ExtPlane} {K : ℝ} {φ : ℝ → ℝ}
    (hw : IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K)
    (hwH : w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf) (hφ : HasRealBoundaryValues w φ)
    (x t : ℝ) (ht : 0 < t) :
    φ x - φ (x - t) ≤ LiZhongQC.lambdaInv K * (φ (x + t) - φ x) ∧
      φ (x + t) - φ x ≤ LiZhongQC.lambdaInv K * (φ x - φ (x - t)) := by
  obtain ⟨W, hWw, hWh, hWinf, hWφ⟩ := hφ
  have hk := lv13_isKQC_of_isKQuasiconformal hw
  -- `w` is finite on `ℍ`, so its finite core there is `ℍ` and `finiteMap w` maps `ℍ` onto `ℍ`
  have hfinH : ∀ z ∈ LiZhongQC.upperHalf, ∃ v ∈ LiZhongQC.upperHalf, w z = (v : ExtPlane) := fun z hz => by
    have h : w z ∈ toExt LiZhongQC.upperHalf := hwH ▸ mem_image_of_mem w ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hve⟩ := h
    exact ⟨v, hv, hve.symm⟩
  have hval : ∀ z ∈ LiZhongQC.upperHalf, ∀ v : ℂ, w z = (v : ExtPlane) → finiteMap w z = v := fun z _ v hv => by
    show finiteValue (w z) = v
    rw [hv]
    rfl
  have hcore : {z : ℂ | (z : ExtPlane) ∈ toExt LiZhongQC.upperHalf ∧ w z ≠ extInf} = LiZhongQC.upperHalf := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, hue⟩, -⟩
      rw [← OnePoint.coe_injective hue]
      exact hu
    · intro hz
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      obtain ⟨v, -, hv⟩ := hfinH z hz
      rw [hv]
      exact OnePoint.coe_ne_infty v
  rw [hcore] at hk
  have himg : finiteMap w '' LiZhongQC.upperHalf = LiZhongQC.upperHalf := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hue⟩ := hfinH z hz
      rw [hval z hz u hue]
      exact hu
    · intro hv
      have h : (v : ExtPlane) ∈ w '' toExt LiZhongQC.upperHalf := by
        rw [hwH]
        exact ⟨v, hv, rfl⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, hze⟩ := h
      exact ⟨z, hz, hval z hz v hze⟩
  -- Li Zhong's Theorem 17.1: the boundary values are `λ(K)`-quasisymmetric
  have hext : LiZhongQC.HasQCExtensionH φ (finiteMap w) K := by
    refine ⟨hk, himg, W, ⟨fun z hz => ?_, hWh.1, hWh.2.1, hWh.2.2.1⟩, hWinf, hWφ⟩
    obtain ⟨v, -, hv⟩ := hfinH z hz
    rw [hWw ⟨z, hz, rfl⟩, hval z hz v hv, hv]
  obtain ⟨hmono, -, -, -, hratio⟩ := LiZhongQC.thm17_1_quasisymmetric hext
  obtain ⟨hlo, hhi⟩ := hratio x t ht
  have hd1 : 0 < φ x - φ (x - t) := sub_pos.2 (hmono (by linarith))
  have hd2 : 0 < φ (x + t) - φ x := sub_pos.2 (hmono (by linarith))
  rw [LiZhongQC.qsRatio] at hlo hhi
  have hr : 0 < (φ (x + t) - φ x) / (φ x - φ (x - t)) := div_pos hd2 hd1
  have hlam : 0 < LiZhongQC.lambdaInv K := hr.trans_le hhi
  constructor
  · have h := (le_div_iff₀ hd1).1 hlo
    have h' := mul_le_mul_of_nonneg_left h hlam.le
    rwa [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
  · exact (div_le_iff₀ hd1).1 hhi

/-- **Unlabelled** (Ch. II §6.3, P1:2443). The inequality (6.6) is sharp: for every `K ≥ 1` there are
`K`-quasiconformal self-mappings of the upper half-plane preserving `∞` whose boundary values attain the upper bound
`λ(K)`, resp. the lower bound `1/λ(K)`, of the quotient in (6.6) for some real `x` and `t > 0` (the lower bound is used
in the proof of Theorem 9.2, P1:3171).
Modelling: `1 ≤ K` (no `K`-quasiconformal mapping exists for `K < 1`); the equalities are multiplied out. -/
theorem thm2_6_2_sharp {K : ℝ} (hK : 1 ≤ K) :
    (∃ (w : ExtPlane → ExtPlane) (φ : ℝ → ℝ) (x t : ℝ), 0 < t ∧
      IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K ∧
      w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf ∧ HasRealBoundaryValues w φ ∧
      φ (x + t) - φ x = LiZhongQC.lambdaInv K * (φ x - φ (x - t))) ∧
    ∃ (w : ExtPlane → ExtPlane) (φ : ℝ → ℝ) (x t : ℝ), 0 < t ∧
      IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K ∧
      w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf ∧ HasRealBoundaryValues w φ ∧
      φ x - φ (x - t) = LiZhongQC.lambdaInv K * (φ (x + t) - φ x) := by
  obtain ⟨f, F, hf, himg, hF, hv⟩ := LiZhongQC.td_half_plane_map hK
  have hv0 : F extInf = extInf := hv 0
  have hv1 : F (((-1 : ℝ) : ℂ) : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane) := hv 1
  have hv2 : F ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := hv 2
  have hv3 : F (((1 : ℝ) : ℂ) : ExtPlane) = (((LiZhongQC.lambdaInv K : ℝ) : ℂ) : ExtPlane) :=
    hv 3
  have hext := lv26_hasQCExtensionH_of_homeoExt hf himg hF hv0
  set φ : ℝ → ℝ := fun x => (finiteValue (F ((x : ℂ) : ExtPlane))).re with hφ
  have hφm1 : φ (-1) = -1 := by
    rw [hφ]
    simp only
    rw [hv1]
    rfl
  have hφ0 : φ 0 = 0 := by
    rw [hφ]
    simp only [Complex.ofReal_zero]
    rw [hv2]
    rfl
  have hφ1 : φ 1 = LiZhongQC.lambdaInv K := by
    rw [hφ]
    simp only
    rw [hv3]
    rfl
  obtain ⟨w, hw, hwH, hbv⟩ := lv26_of_hasQCExtensionH hext
  obtain ⟨w', hw', hwH', hbv'⟩ := lv26_of_hasQCExtensionH (lv26_reflect_hasQCExtensionH hext)
  refine ⟨⟨w, φ, 0, 1, one_pos, hw, hwH, hbv, ?_⟩, ⟨w', fun x => -φ (-x), 0, 1, one_pos, hw', hwH', hbv', ?_⟩⟩
  · rw [zero_add, zero_sub, hφ1, hφ0, hφm1]
    ring
  · simp only [zero_add, zero_sub, neg_zero, neg_neg]
    rw [hφ1, hφ0, hφm1]
    ring

/-! ## §6.4 The distortion function `λ` -/

/-- **Formula (6.7)** (Ch. II §6.4). `1 + λ(2K) = (√(1 + λ(K)) + √λ(K))⁴` for every `K`.
Modelling: for `K > 0`, where (6.4) defines `λ(K)`. -/
theorem eq2_6_7 {K : ℝ} (hK : 0 < K) :
    1 + LiZhongQC.lambdaInv (2 * K) =
      (Real.sqrt (1 + LiZhongQC.lambdaInv K) + Real.sqrt (LiZhongQC.lambdaInv K)) ^ 4 := by
  obtain ⟨hρ, -⟩ := LiZhongQC.td_quadLambda_lambdaInv hK
  have hμ := (eq2_6_4 hK).2
  set ρ := LiZhongQC.lambdaInv K
  set a := Real.sqrt (1 + ρ)
  set b := Real.sqrt ρ
  have ha : a ^ 2 = 1 + ρ := Real.sq_sqrt (by linarith)
  have hb : b ^ 2 = ρ := Real.sq_sqrt hρ.le
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.2 hρ
  have hba : b < a := by nlinarith
  have hab1 : (a - b) * (a + b) = 1 := by nlinarith
  have hu0 : 0 < b / a := div_pos hb0 ha0
  have hu1 : b / a < 1 := (div_lt_one ha0).2 hba
  -- `√(1 - u²) = √(1/(1+ρ))` for `u = b/a`
  have hs : Real.sqrt (1 - (b / a) ^ 2) = Real.sqrt (1 / (1 + ρ)) := by
    congr 1
    rw [div_pow, hb, ha]
    field_simp
    ring
  -- `(1 - u)/(1 + u) = 1/(a + b)²`
  have hkey : (1 - b / a) / (1 + b / a) = 1 / (a + b) ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    linear_combination hab1
  set ρ' := (a + b) ^ 4 - 1 with hρ'def
  have hab : 1 < a + b := by nlinarith
  have hρ' : 0 < ρ' := by
    have : 1 < (a + b) ^ 4 := one_lt_pow₀ hab (by norm_num)
    linarith
  have hsq : Real.sqrt (1 / (1 + ρ')) = 1 / (a + b) ^ 2 := by
    rw [hρ'def, show 1 + ((a + b) ^ 4 - 1) = ((a + b) ^ 2) ^ 2 by ring, one_div, Real.sqrt_inv,
      Real.sqrt_sq (by positivity), one_div]
  have hΛ : LiZhongQC.quadLambda ρ' = 2 * K := by
    rw [LiZhongQC.eq5_18 hρ', hsq, ← hkey, LiZhongQC.em_mu_landen hu0 hu1, hs, hμ]
    field_simp
  rw [← hΛ, LiZhongQC.lambdaInv_quadLambda hρ', hρ'def]
  ring

/-- Auxiliary (the estimate behind (6.8)–(6.10)). For `K > 0` the remainder
`R(K) = λ(K) - (e^{πK}/16 - 1/2)` satisfies `0 < R(K) < 12 e^{-πK}`: with `s = √(1 + λ(K))`, `t = √λ(K)` and
`r = 1/s`, (6.4) gives `μ(r) = πK/2`, and (2.13) (`eq2_2_13`) gives `2(s + t) = e^{πK/2} + δ`, `0 < δ < r³` (6.8); then
`R = (s - t)²/4 + (s + t)δ/4 - δ²/16`. -/
theorem lv26_remainder_bounds {K : ℝ} (hK : 0 < K) :
    0 < LiZhongQC.lambdaInv K - (Real.exp (Real.pi * K) / 16 - 1 / 2) ∧
      LiZhongQC.lambdaInv K - (Real.exp (Real.pi * K) / 16 - 1 / 2) < 12 * Real.exp (-(Real.pi * K)) := by
  obtain ⟨hρ, hμ⟩ := eq2_6_4 hK
  set ρ := LiZhongQC.lambdaInv K
  set s := Real.sqrt (1 + ρ) with hsdef
  set t := Real.sqrt ρ with htdef
  have hs2 : s ^ 2 = 1 + ρ := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have ht0 : 0 < t := Real.sqrt_pos.2 hρ
  have hs1 : 1 < s := by nlinarith
  have hts : t < s := by nlinarith
  have hst1 : (s - t) * (s + t) = 1 := by linear_combination hs2 - ht2
  -- `r = 1/√(1 + λ(K)) = 1/s` and `√(1 - r²) = t/s`
  have hr : Real.sqrt (1 / (1 + ρ)) = 1 / s := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hr0 : 0 < 1 / s := by positivity
  have hr1 : 1 / s < 1 := (div_lt_one hs0).2 hs1
  have hr' : Real.sqrt (1 - (1 / s) ^ 2) = t / s := by
    rw [show 1 - (1 / s) ^ 2 = (t / s) ^ 2 by rw [div_pow, div_pow, ht2]; field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  have h13 := eq2_2_13 hr0 hr1
  rw [← hr, hμ, hr, hr'] at h13
  have hsimp : 2 * (1 + t / s) / (1 / s) = 2 * (s + t) := by
    field_simp
  rw [hsimp] at h13
  set E := Real.exp (Real.pi * K / 2) with hE
  set δ := 2 * (s + t) - E with hδ
  obtain ⟨hδ0, hδ1⟩ := h13
  have hδ' : δ * s ^ 3 < 1 := by
    rw [div_pow, one_pow, lt_div_iff₀ (by positivity)] at hδ1
    exact hδ1
  have hE0 : 0 < E := Real.exp_pos _
  have hEsq : Real.exp (Real.pi * K) = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add]
    ring_nf
  have hR : ρ - (Real.exp (Real.pi * K) / 16 - 1 / 2) = (s - t) ^ 2 / 4 + (s + t) * δ / 4 - δ ^ 2 / 16 := by
    rw [hEsq, hδ]
    linear_combination (-1 / 2 : ℝ) * hs2 + (-1 / 2 : ℝ) * ht2
  have hδ1' : δ < 1 := by
    have : 1 < s ^ 3 := one_lt_pow₀ hs1 (by norm_num)
    nlinarith
  rw [hR]
  constructor
  · have h1 : 0 < (s - t) ^ 2 := by
      have := sub_pos.2 hts
      positivity
    have h2 : 0 < δ * (4 * (s + t) - δ) := mul_pos hδ0 (by linarith)
    nlinarith
  · have hss : s * (s - t) < 1 := by nlinarith
    have hA : s ^ 2 * (s - t) ^ 2 < 1 := by
      have h0 : 0 < s * (s - t) := mul_pos hs0 (sub_pos.2 hts)
      nlinarith
    have hB : s ^ 2 * ((s + t) * δ) < 2 := by
      have h1 := mul_lt_mul_of_pos_right (show s + t < 2 * s by linarith) (mul_pos (pow_pos hs0 2) hδ0)
      calc s ^ 2 * ((s + t) * δ) = (s + t) * (s ^ 2 * δ) := by ring
        _ < 2 * s * (s ^ 2 * δ) := h1
        _ = 2 * (δ * s ^ 3) := by ring
        _ < 2 := by linarith
    have hEs : E < 4 * s := by linarith
    have hlt : (s - t) ^ 2 / 4 + (s + t) * δ / 4 - δ ^ 2 / 16 < 3 / (4 * s ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      have he : ((s - t) ^ 2 / 4 + (s + t) * δ / 4 - δ ^ 2 / 16) * (4 * s ^ 2) =
          s ^ 2 * (s - t) ^ 2 + s ^ 2 * ((s + t) * δ) - s ^ 2 * δ ^ 2 / 4 := by ring
      have hn : 0 ≤ s ^ 2 * δ ^ 2 / 4 := by positivity
      rw [he]
      linarith
    have hE2 : E ^ 2 < 16 * s ^ 2 := by
      have h := pow_lt_pow_left₀ hEs hE0.le two_ne_zero
      calc E ^ 2 < (4 * s) ^ 2 := h
        _ = 16 * s ^ 2 := by ring
    have hle : 3 / (4 * s ^ 2) < 12 * Real.exp (-(Real.pi * K)) := by
      rw [Real.exp_neg, hEsq, ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith

/-- **Formula (6.10)** (Ch. II §6.4). `λ(K) = e^{πK}/16 - 1/2 + O(e^{-πK})` as `K → ∞`, where the remainder is
positive.
Modelling: the remainder `R(K) = λ(K) - (e^{πK}/16 - 1/2)` satisfies `R(K) = O(e^{-πK})` as `K → ∞`
(`Asymptotics.IsBigO`, footnote 14) and `R(K) > 0` for `K ≥ 1`, the range of the derivation (6.8)–(6.9). -/
theorem eq2_6_10 :
    Asymptotics.IsBigO atTop (fun K : ℝ => LiZhongQC.lambdaInv K - (Real.exp (Real.pi * K) / 16 - 1 / 2))
        (fun K : ℝ => Real.exp (-(Real.pi * K))) ∧
      ∀ K : ℝ, 1 ≤ K → 0 < LiZhongQC.lambdaInv K - (Real.exp (Real.pi * K) / 16 - 1 / 2) := by
  refine ⟨Asymptotics.IsBigO.of_bound 12 ?_, fun K hK => (lv26_remainder_bounds (by linarith)).1⟩
  filter_upwards [eventually_gt_atTop 0] with K hK
  obtain ⟨h0, h1⟩ := lv26_remainder_bounds hK
  rw [Real.norm_of_nonneg h0.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact h1.le

/-! ## §6.5 Solution of the boundary value problem -/

/-- **Theorem 6.3** (Ch. II §6.5, Beurling–Ahlfors). Let `φ` be a function which is continuous and strictly increasing
on the real axis and which satisfies the condition `1/ϱ ≤ (φ(x + t) - φ(x))/(φ(x) - φ(x - t)) ≤ ϱ` (6.11) for every
real `x` and `t`, `t > 0`. Then there exists a quasiconformal mapping `w` of the upper half-plane onto itself, which
has the boundary values `w(x) = φ(x)` and a maximal dilatation less than a bound depending on `ϱ`.
Modelling: `∀ ϱ, ∃ K₀, ∀ φ, …` (the bound depends only on `ϱ`; the proof gives `8ϱ(1 + ϱ)²`, (6.19)); "less than a
bound" is `≤ K₀` (equivalent under `∃ K₀`); (6.11) is multiplied out (the denominators are positive, `φ` being strictly
increasing); `w` preserves `∞` (`HasRealBoundaryValues`), as it must, `φ` mapping the real axis onto itself by
(6.11). -/
theorem thm2_6_3 (ϱ : ℝ) :
    ∃ K₀ : ℝ, ∀ φ : ℝ → ℝ, Continuous φ → StrictMono φ →
      (∀ x t : ℝ, 0 < t → φ x - φ (x - t) ≤ ϱ * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ ϱ * (φ x - φ (x - t))) →
      ∃ w : ExtPlane → ExtPlane, IsKQuasiconformal w (toExt LiZhongQC.upperHalf) K₀ ∧
        w '' toExt LiZhongQC.upperHalf = toExt LiZhongQC.upperHalf ∧ HasRealBoundaryValues w φ := by
  refine ⟨8 * ϱ * (ϱ + 1), fun φ hc hm h => ?_⟩
  exact lv26_of_hasQCExtensionH (LiZhongQC.thm17_2_beurling_ahlfors (lv26_isQuasisymmetric hc hm h)).2

/-! ## §6.6 Boundary value problem for a boundary component of a multiply connected domain -/

/-- **Theorem 6.4** (Ch. II §6.6, Väisälä). Let `D` and `D′` be domains with the free boundary curves `C` and `C′`,
respectively, and `w : D → D′` a `K`-quasiconformal mapping which can be extended to a homeomorphism of `D ∪ C` onto
`D′ ∪ C′`. Let `G` and `G′` be the components of the complement of `C` and `C′` which contain `D` and `D′`,
respectively. Then there exists a quasiconformal mapping of `G` onto `G′` which has the same boundary values as `w` on
`C` and whose maximal dilatation is less than a bound depending only on `K` and the domain `D`.
Modelling: `∀ D C K, ∃ K′, ∀ D′ C′ G G′ w W, …` (the bound depends on `K` and on `D` with its free boundary curve
`C`); `W` is the homeomorphic extension of `w` to `D ∪ C`; `G` is the component of `ℂ̄ \ C` of a point of `D`, whose
boundary is `C`, so "the same boundary values as `w` on `C`" is `HasBoundaryValuesExt v G G′ W`; "less than a bound"
is `≤ K′`. -/
theorem thm2_6_4 (D C : Set ExtPlane) (K : ℝ) (hD : IsDomainExt D) (hC : IsFreeBoundaryCurve D C) :
    ∃ K' : ℝ, ∀ (D' C' G G' : Set ExtPlane) (w W : ExtPlane → ExtPlane), IsDomainExt D' →
      IsFreeBoundaryCurve D' C' → IsKQuasiconformal w D K → w '' D = D' → EqOn W w D →
      IsHomeoOn W (D ∪ C) (D' ∪ C') → (∃ z ∈ D, G = connectedComponentIn Cᶜ z) →
      (∃ z ∈ D', G' = connectedComponentIn C'ᶜ z) →
      ∃ v : ExtPlane → ExtPlane, IsKQuasiconformal v G K' ∧ v '' G = G' ∧ HasBoundaryValuesExt v G G' W := by
  sorry

/-- **Formula (6.23)** (Ch. II §6.6, footnote 22). Every quadrilateral `Q` with module `M(Q) = 1` satisfies
`s_a(Q)/s_b(Q) ≥ 2/(e^{π + √(π² + π)} - 1) > 10⁻³` (derived in the proof of Theorem 6.4; footnote 22 states it for
every quadrilateral with module one "in view of later applications"; cited in §8.7).
Modelling: `s_a`, `s_b` are the distances between the a-sides and the b-sides measured in `Q` (`Quadrilateral.aDist`,
`Quadrilateral.bDist`, I.4.3), with `0 < s_a, s_b < ∞`; the quotient is multiplied out in `ℝ≥0∞`. -/
theorem eq2_6_23 :
    (1 / 1000 : ℝ) < 2 / (Real.exp (Real.pi + Real.sqrt (Real.pi ^ 2 + Real.pi)) - 1) ∧
      ∀ Q : Quadrilateral, Q.module = 1 →
        ENNReal.ofReal (2 / (Real.exp (Real.pi + Real.sqrt (Real.pi ^ 2 + Real.pi)) - 1)) * Q.bDist ≤ Q.aDist := by
  sorry

end LehtoVirtanen1973
