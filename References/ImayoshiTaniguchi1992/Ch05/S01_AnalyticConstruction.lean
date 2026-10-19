import LiZhongQC.Ch10.S33_BersEmbedding
import References.GardinerLakic2000.Ch08.S06_IsometryProperty
import References.Lehto1987.Ch05.S09_TeichmullerSpacesOfCompactSurfaces

/-!
# Imayoshi–Taniguchi, Chapter 5 §5.1: Analytic construction of Teichmüller spaces

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 5 §5.1 (`full.md` IT1:4194–4473,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Every result of this section is already stated in the project for closed surfaces of genus `g ≥ 2` (the setting of
`LiZhongQC.MarkedRS`, whose surfaces are closed `ClosedRS`); this file is the item index (no declarations). Conventions as in
`Ch06/S04_Royden`: `T(R)` is `LiZhongQC.TeichSpace S₀`, `T(Γ)` is `LiZhongQC.TeichGamma Γ`, the canonical lift `f̃` of a
quasiconformal map is the normalized lift of `LiZhongQC.IsNormalizedLift`, and `θ_{f̃}(γ) = f̃ γ f̃⁻¹`. The Teichmüller
distance is `LiZhongQC.teichDistance` (half of IT's `d`, IT-D3).

* Definition (Teichmüller space `T(R)` of an arbitrary Riemann surface, IT1:4200) — exists: `LiZhongQC.TeichSpace`
* Lemma 5.1 (`[S₁, f₁] = [S₂, f₂]` iff `θ_{f̃₁} = θ_{f̃₂}`, IT1:4248) — exists: `LiZhongQC.thm27_1`
  (closed surfaces of genus at least 2, Lemmas 5.1 and 5.2 combined, with `LiZhongQC.thm23_1_homotopy_iff`); the case of a
  non-compact surface is deferred: the marked surfaces of LiZhongQC.MarkedRS are closed
* Definition (reduced Teichmüller space `T^#(Γ)` and Teichmüller space `T(Γ)` of a Fuchsian group, IT1:4278) — exists:
  `LiZhongQC.TeichGamma`
* Lemma 5.2 (`θ_{f̃₁} = θ_{f̃₂}` iff `f̃₁ = f̃₂` on `ℝ`, `R` compact, IT1:4300) — exists: `LiZhongQC.thm27_1`
* Proposition 5.3 (`T(R) = T^#(Γ)`, IT1:4314) — exists: `LiZhongQC.teichGamma_equiv_teichSpace`, `Lehto1987.thm5_3_1`
* Theorem 5.4 (`T(R)` is complete for the Teichmüller distance, IT1:4408) — exists: `Lehto1987.thm5_3_2`,
  `LiZhongQC.thm29_2_complete`
* Proposition 5.5 (`[f₁]_*` is an isometric homeomorphism, IT1:4460) — exists:
  `GardinerLakic2000.para2_4_geometric_isometry`, `Lehto1987.thm5_5_5`
-/

namespace ImayoshiTaniguchi1992

end ImayoshiTaniguchi1992
