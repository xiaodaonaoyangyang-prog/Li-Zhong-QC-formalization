import LiZhongQC.Ch02.S13_Representation

/-!
# Imayoshi–Taniguchi, Chapter 4 §4.1: Quasiconformal mappings (W2 batch I2)

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 4 §4.1 (`full.md` IT1:2352–3015,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: as in `Ch03/S02_FenchelNielsen`. A quasiconformal mapping is `LiZhongQC.IsQuasiconformal f D` (a quasiconformal homeomorphism
of the plane domain `D` onto `f(D)`, the geometric definition; the equivalence with IT's analytic definition is IT Theorem 4.4), its complex
dilatation is `LiZhongQC.complexDilatation f` (`f_z̄ / f_z`), a conformal mapping of `A` onto `B` is `LiZhongQC.IsConformalOnto h A B`.

* Proposition 4.1 (a homeomorphism with partial derivatives a.e. is differentiable a.e.) — exists: `Lehto1987.para1_3_3`
* Proposition 4.2 (`f_z, f_z̄ ∈ L²_loc`) — exists: `LiZhongQC.thm9_5_L2_derivatives`
* Proposition 4.3 (classical and distributional derivatives agree) — exists: `LiZhongQC.lemma9_2_genPartials_of_isACL`
* Theorem 4.4 (the definitions A and A′ agree) — exists: `LiZhongQC.thm10_2_isQuasiconformal_iff`
* Lemma 4.5 (`L^p` distributional derivatives imply ACL) — exists: `LiZhongQC.lemma9_2_isACL_of_genPartials`
* Lemma 4.6 (Weyl's lemma) — exists: `LiZhongQC.sp_w_weyl`
* Proposition 4.7 (a quadrilateral is conformally a rectangle) — exists: `LiZhongQC.thm1_1_exists_rectangle`
* Lemma 4.8 (`M(Q)/K ≤ M(f(Q)) ≤ K M(Q)`) — exists: `GardinerLakic2000.prop1_3`
* Theorem 4.9 (the definitions A and G agree) — exists: `LiZhongQC.thm10_1_isKQC_iff`
* Theorem 4.10 (inverse and composition of quasiconformal mappings) — exists: `LiZhongQC.thm7_2_inv`, `LiZhongQC.thm7_1_comp`
* Proposition 4.11 (`f_z ≠ 0` a.e.) — exists: `LiZhongQC.thm9_6_cor2_jacobian_pos`
* Lemma 4.12 (`∬_E J_f = A(f(E))`) — exists: `LiZhongQC.thm9_6_absolutelyContinuous`
* Proposition 4.13 (the complex dilatation of `g ∘ f⁻¹`) — exists: `LehtoVirtanen1973.eq4_5_9`
* Lemma 4.14 (a geometrically quasiconformal map is ACL) — exists: `LiZhongQC.thm9_1_isACL`
* Lemma 4.15 (`|f_z̄| ≤ k |f_z|` a.e.) — exists: `LiZhongQC.thm9_4_dilatation_ae`
* Theorem 4.16 (Mori's theorem) — exists: `LiZhongQC.thm15_2_mori`
* Theorem 4.17 (normality of `K`-quasiconformal self-maps of `ℂ` fixing `0`, `1`) — exists: `LehtoVirtanen1973.thm2_5_1_iii`
* Proposition 4.18 (maps with the same complex dilatation differ by a conformal map) — `prop4_18_a`, `prop4_18_b`
-/

open Set Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsQuasiconformal complexDilatation IsConformalOnto)

/-- **Proposition 4.18, first part** (Ch. 4 §4.1.4, IT1:2988). Let `μ` be an element of `B(D)₁` and suppose that there exists a
quasiconformal mapping `f` of the domain `D` with the complex dilatation `μ_f = μ`. Then for every conformal mapping `h` of `f(D)`,
the composed mapping `h ∘ f` has the same complex dilatation `μ`. -/
theorem prop4_18_a {f h : ℂ → ℂ} {D B : Set ℂ} (hD : IsOpen D) (hf : IsQuasiconformal f D) (hh : IsConformalOnto h (f '' D) B) :
    ∀ᵐ z ∂(volume.restrict D), complexDilatation (h ∘ f) z = complexDilatation f z := by
  sorry

/-- **Proposition 4.18, second part** (Ch. 4 §4.1.4, IT1:2988). In the situation of the first part, for every quasiconformal mapping `g`
of `D` with `μ_g = μ`, the composed mapping `g ∘ f⁻¹` is a conformal mapping of `f(D)` (onto `g(D)`). -/
theorem prop4_18_b {f g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : IsQuasiconformal f D) (hg : IsQuasiconformal g D)
    (hμ : ∀ᵐ z ∂(volume.restrict D), complexDilatation g z = complexDilatation f z) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ (f '' D) (g '' D) ∧ ∀ z ∈ D, g z = φ (f z) := by
  sorry

end ImayoshiTaniguchi1992
