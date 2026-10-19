import References.LehtoVirtanen1973.Ch04.S01_AnalyticProperties

/-!
# Lehto–Virtanen, Chapter IV §2: Analytic definition of quasiconformality

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. IV §2
(pp. 166–170; `full.md` P1:5185–5280).

Conventions as in §1: `w : ExtPlane → ExtPlane` is a mapping of the domain `G` of `ℂ̄`; absolute continuity on lines
in `G` is `IsACLExt` (§1.1); differentiability, `∂_α w`, "almost everywhere in `G`" are read at the finite points
with finite values, for the finite part `finiteMap w`.

* Analytic definition (§2.3, Gehring–Lehto) — `analytic_definition`

Not stated (inventory: omitted): the counterexample of 2.2 (P1:5191–5203, with footnote 41), a homeomorphism of a
square, conformal outside a null set and measure-preserving, which is not quasiconformal (an example, referred to later
only in remarks, P1:5279, 5551; its existence claims used in V.3.7 are stated there); and the history of the analytic
definition in 2.4 (P1:5277–5279). The numbered formulas (2.1)–(2.4) are steps of the proof of the analytic definition.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane)
open References (IsDomainExt finitePart)

/-! ## §2.3 Analytic definition -/

/-- **Analytic definition** (Ch. IV §2.3, Gehring–Lehto). Let a sense-preserving homeomorphism `w` of the domain `G`
satisfy the following two conditions: 1. `w` is absolutely continuous on lines in `G`; 2. the dilatation condition
`max_α |∂_α w(z)| ≤ K min_α |∂_α w(z)|` holds almost everywhere in `G`. Then `w` is a `K`-quasiconformal mapping of
`G`.
Modelling: condition 2 is required at the points of differentiability: it makes sense only where `w` is
differentiable (P1:5189), and the book makes no assumption about the differentiability of `w` (P1:5205), which holds
almost everywhere by condition 1 (Lemma III.3.1 and Theorem III.3.1). `1 ≤ K` is the book's standing `K ≥ 1`: for
`K < 1` condition 2 forces `∂_α w = 0` almost everywhere, which no homeomorphism satisfying condition 1 does. -/
theorem analytic_definition {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (hK : 1 ≤ K) (hacl : IsACLExt w G)
    (hdil : ∀ᵐ z ∂(volume.restrict (finitePart G)), DifferentiableAt ℝ (finiteMap w) z →
      (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) ≤ K * ⨅ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) :
    IsKQuasiconformal w G K := by
  obtain ⟨hDo, hhom⟩ := lv13_finiteCore_homeo hG.1 hw.1
  have hres : volume.restrict (finitePart G) = volume.restrict (finiteCore w G) := lv41_restrict_eq hw.1.2.1
  rw [hres] at hdil
  -- at a point of differentiability, `max_α |∂_α w| = |w_z| + |w_{\bar z}|` and `min_α |∂_α w| = |w_z| - |w_{\bar z}|`
  -- (`|w_{\bar z}| ≤ |w_z|`, sense-preservation); elsewhere both derivatives are `0`
  have hineq : ∀ᵐ z ∂(volume.restrict (finiteCore w G)),
      ‖LiZhongQC.dz (finiteMap w) z‖ + ‖LiZhongQC.dzbar (finiteMap w) z‖ ≤
        K * (‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖) := by
    filter_upwards [hdil, ae_restrict_mem hDo.measurableSet] with z hz hzD
    by_cases hd : DifferentiableAt ℝ (finiteMap w) z
    · obtain ⟨hsup, hinf⟩ := eq1_9_5 hd (sensePreserving_jacobian_nonneg hG hw hzD.1 hzD.2 hd).2
      have h := hz hd
      rwa [hsup, hinf] at h
    · simp [LiZhongQC.dz, LiZhongQC.dzbar, fderiv_zero_of_not_differentiableAt hd]
  -- so the finite part is `K`-q.c. on the finite core (Li Zhong's Theorem 10.1), and the converse bridge applies
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K :=
    (LiZhongQC.thm10_1_isKQC_iff hDo hK hhom).2 ⟨hacl, hineq⟩
  exact lv15_isKQuasiconformal_of_isKQC hG hw.1.1 hw.1.2.1 hk

end LehtoVirtanen1973
