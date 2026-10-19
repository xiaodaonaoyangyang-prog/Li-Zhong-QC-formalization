import LiZhongQC.Ch10.S33_BersEmbedding
import References.GardinerLakic2000.Ch06.S03_BersEmbedding
import References.Lehto1987.Ch05.S05_ComplexStructuresOnTeichmullerSpaces

/-!
# Imayoshi–Taniguchi, Chapter 6 §6.1: Bers' embedding and the complex structure of Teichmüller space

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 6 §6.1 (`full.md` IT1:5207–5420,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Every result of this section is already stated in the project; this file is the item index (no declarations). Conventions as in
`Ch06/S04_Royden`: `T(Γ)` is `LiZhongQC.TeichGamma Γ`, `T_β(Γ)` is identified with it through Lemma 6.1 (the class of
`w_μ` on `H*` is the class of `w^μ` on `ℝ`), `Φ(μ) = S(w_μ)|_{H*}` is `LiZhongQC.bersFunctionGamma`, Bers' embedding is
`LiZhongQC.bersMapGamma`.

* Lemma 6.1 (`w^μ = w^ν` on `ℝ` iff `w_μ = w_ν` on `H*`, IT1:5252) — exists: `LiZhongQC.lemma33_1`
* Proposition 6.2 (`β : B(H, Γ)₁ → T_β(Γ)` is a continuous surjection, IT1:5262) — omitted: it holds by the definition of
  `T_β(Γ)` as a set of classes with the topology induced from `T(Γ)`
* Lemma 6.3 (Schwarzian chain rule, IT1:5276) — exists: `LiZhongQC.eq19_1_chain_rule`
* Lemma 6.4 (`Φ(μ)` is `Γ`-automorphic, IT1:5302) — exists: `LiZhongQC.eq33_11`, `LiZhongQC.bersMapGamma_mem`
* Proposition 6.5 (Bers projection and Bers embedding are continuous, IT1:5340) — exists: `LiZhongQC.lemma33_2`
* Theorem 6.6 (`T_B(Γ)` lies in the ball of radius `3/2`, IT1:5352) — exists: `LiZhongQC.bersFunctionGamma_mem`
* Lemma 6.7 (Nehari–Kraus, IT1:5356) — exists: `LiZhongQC.thm19_2_nehari`
-/

namespace ImayoshiTaniguchi1992

end ImayoshiTaniguchi1992
