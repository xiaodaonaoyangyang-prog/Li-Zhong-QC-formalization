import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation
import LiZhongQC.Ch02.S12_Existence

/-!
# Lehto–Virtanen, Chapter V §5: Application of the Hilbert transformation to quasiconformal mappings

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §5
(pp. 211–219; `full.md` P2:439–762).

Conventions. Where the book works with finite domains and finite mappings (§5.1–§5.2, §5.6–§5.7), a domain `G` of the
finite plane is `toExt D` for `D : Set ℂ`, and a finite mapping is `OnePoint.map f` for `f : ℂ → ℂ` (`∞ ↦ ∞`); a
quasiconformal mapping "of the plane" is a quasiconformal mapping of `ℂ̄ = univ` which fixes `∞`, hence of this form.
For such a mapping the derivatives `w_z`, `w_{\bar z}` and the complex dilatation `κ = w_{\bar z}/w_z` are
`LiZhongQC.dz f`, `LiZhongQC.dzbar f` and `LiZhongQC.complexDilatation f`: the book's values at the points of
differentiability, i.e. almost everywhere (Theorem IV.1.1); their junk values (the derivative of a non-differentiable
function is `0`, and `0/0 = 0`) lie on a null set, and every statement uses them only almost everywhere, in `L^p`
norms, or inside `LiZhongQC.hilbertH`, which does not see null sets (`LiZhongQC.hilbertH_congr_ae`). The measure is the
area measure `volume` of the finite plane `Ω`; `L^p(Ω)` is `MeasureTheory.MemLp` with the real exponent `p` (H6); a
measurable function is an almost everywhere strongly measurable one. The Hilbert transformation `S` (III.7.6) is
`LiZhongQC.hilbertH` (on `L²`, a representative of the book's `L²`-class, so identities involving `S` hold almost
everywhere), the operator `T` (III.7.2) is `LiZhongQC.cauchyT` and `‖S‖_p` is `LiZhongQC.hilbertNorm p`, the norm
`‖S‖₂ = 1` of III.7.6 being `LiZhongQC.thm11_3_cor1` (Ch. III §7). The limit exponent `p(K)` is `ℝ≥0∞`-valued (H6).

* Formula (5.2) (§5.1; cited P2:595) — exists: `LehtoVirtanen1973.uniqueness_theorem` (w̃ = φ ∘ w in D, with φ
  conformal in w(D): the Uniqueness theorem applied in D to w and w̃, whose complex dilatations agree almost
  everywhere in D)
* Formula (5.3) (§5.1), with the relation `w̃_{\bar z} = κ + κ S w̃_{\bar z}` it implies — `eq5_5_3`
* Definition (solution of the integral equation `ω = κ + κ S ω` (5.4), §5.2) — `IsIntegralEqSolution`
* Unlabelled (§5.2, P2:487): the solution of (5.4) is uniquely determined up to a null set —
  `integralEq_solution_unique`
* Unlabelled (§5.2, P2:495–551; "the solution" cited P2:573, 595, 759): the iterates `ω_n` of (5.5)–(5.6) converge
  in `L²` to a solution of (5.4) — `integralEq_solution_neumann`
* Definition (the `L^p`-norm `‖S‖_p` of the Hilbert transformation, §5.3) — exists: `LiZhongQC.hilbertNorm` (the
  supremum of the ratios of the L^p norms of Sω and ω over the ω in L^p with nonzero norm, which equals the
  supremum over the unit sphere by homogeneity; used by the book, and here, only for p > 1. Caveat: the definition
  is a real sSup of toReal ratios, exact only where every Sω has a finite L^p norm and the ratio set is bounded; for
  p = 2 this is the isometry, for the other p > 1 it rests on the Calderón–Zygmund theorem below (in the project
  LiZhongQC.zygmund_calderon); for p ≤ 1 the value is junk and no statement uses it)
* Calderón–Zygmund theorem (§5.3, quoted: the Hilbert transformation is bounded in every `L^p(Ω)`, `p > 1`) — exists:
  `LiZhongQC.hilbertNorm_bddAbove`, `LiZhongQC.hilbertH_memLp`, `LiZhongQC.eq11_16` (for 1 < p: S maps L^p into L^p,
  the ratio set defining the norm is bounded above, and the L^p norm of Sω is at most the norm of S times that of ω)
* Unlabelled (§5.3, P2:563, by Riesz's convexity theorem): `log ‖S‖_p` is a convex function of `1/p` — exists:
  `LiZhongQC.thm11_2_riesz_thorin` (convexity of the logarithm of the norm at 1/s on 0 < s < 1, i.e. p = 1/s > 1)
* Unlabelled (§5.3, P2:563; used P2:697, "possible by 5.3"): `‖S‖_p` is a continuous function of `p` — exists:
  `LiZhongQC.hilbertNorm_continuousOn` (continuity on p > 1, the range where the book uses the norm)
* Riesz's convexity theorem (§5.3, named) — omitted: quoted by name only; its consequences used in the book are the
  two items above
* Formula (5.8) (§5.3, quoted from Calderón–Zygmund) — `eq5_5_8`
* Lemma 5.1 (§5.3, Bojarski) — `lemma5_5_1`
* Definition (the limit exponent `p(K)`, §5.4) — `limitExponent`
* Theorem 5.1 (§5.4), with the inequalities (5.10) — `thm5_5_1_i`, `thm5_5_1_ii`
* Unlabelled (§5.4, P2:621–635; cited in footnote 49 and in VI.2.2, P2:1733, 1769): `p(K) → 2` as `K → ∞`,
  `p(K) → ∞` as `K → 1`, and `(K − 1) p(K)` stays between two finite positive bounds as `K → 1` —
  `limitExponent_tendsto_atTop`, `limitExponent_tendsto_one`, `limitExponent_mul_bounds`
* Unlabelled (§5.4, P2:1733; recalled P2:1769, not stated in V.5.4): `p(1) = ∞` and `p(K)` decreases with `K` —
  `limitExponent_one`, `limitExponent_antitoneOn`
* Conjecture (§5.4, P2:637: `p(K) = 2K/(K − 1)`) — omitted: an open problem
* Theorem 5.2 (§5.5, Bojarski) — `thm5_5_2`
* Theorem 5.3 (§5.6) — `thm5_5_3`
* Formula (5.17) (§5.7, with footnote 50) — `eq5_5_17`

Not stated (inventory: omitted): the construction of the auxiliary mapping `w̃` of §5.1 with its normalization (5.1)
(P2:443–449; (5.1) enters the hypotheses of `eq5_5_3` and `eq5_5_17`); the steps (5.5)–(5.7) of the iteration (their
outcome is `integralEq_solution_neumann`); the part of Riesz's theorem that `‖S‖_p` increases for `p > 2` and tends
to `∞` (P2:563, not cited); the derivation P2:595–603 (`p(K) ≥ 2` by Theorem IV.1.2, the local `L^p`-classes of the
derivatives), which is summarized in Theorem 5.1; the remark that the exponent `2` in Theorem IV.1.2 cannot be
replaced by a larger number (P2:627, immediate from `p(K) → 2`); the example (5.9); the remark on `δ(K) ≤ 1/K` with
footnote 49 (P2:663); the steps (5.12)–(5.16) of the proof of Theorem 5.3;
the consequence that a subsequence of the derivatives converges almost everywhere (P2:749, not cited); the remark
P2:761 (Bojarski, Vekua) that the right-hand side of (5.17) is quasiconformal. [OCR] P2:465 has the Beltrami equation
`w̃_{\bar z} = κ w̃_z` OCR'd as `w̃_z = κ w̃_z`, and P2:465, 595 have `w̃_z` for `w̃_{\bar z}` (where it is the
solution of (5.4)).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt hilbertH hilbertNorm cauchyT neumannIter)
open References (IsDomainExt finitePart)

/-! ## §5.1 Transformation of the Beltrami equation into an integral equation -/

/-- **Formula (5.3)** (Ch. V §5.1). Let `w̃` be a quasiconformal mapping of the plane which is conformal in a
neighbourhood of `∞` and has there the expansion `w̃(z) = z + Σ_{n ≥ 1} aₙ z⁻ⁿ` (5.1), and let `κ` be its complex
dilatation. Then `w̃_{\bar z}` is square integrable over the plane, `w̃_z = 1 + S w̃_{\bar z}` (5.3) almost everywhere,
and consequently `w̃_{\bar z} = κ + κ S w̃_{\bar z}` almost everywhere.
Modelling: `w̃ = OnePoint.map f`; the normalization (5.1) is "`f` is holomorphic in `|z| > R` for some `R` and
`f(z) − z → 0` as `z → ∞`", which is equivalent to (5.1) by the Laurent expansion at `∞`. The square integrability
(P2:459: `f = w̃ − z` has `L²`-integrable derivatives) is stated because `S` is applied to `w̃_{\bar z}` as an
element of `L²`. The book derives (5.3) for the mapping `w̃` of its construction (complex dilatation that of `w` in a
bounded domain and `0` elsewhere); the derivation uses only the quasiconformality and (5.1), and the book applies it
again in §5.6 and §5.7, so the claim is stated for every such `w̃`. -/
theorem eq5_5_3 {f : ℂ → ℂ} (hf : IsQuasiconformalMap (OnePoint.map f) univ)
    (hhol : ∃ R : ℝ, DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hnorm : Tendsto (fun z => f z - z) (Bornology.cobounded ℂ) (𝓝 0)) :
    MemLp (LiZhongQC.dzbar f) 2 volume ∧
      (∀ᵐ z ∂volume, LiZhongQC.dz f z = 1 + hilbertH (LiZhongQC.dzbar f) z) ∧
      ∀ᵐ z ∂volume, LiZhongQC.dzbar f z =
        LiZhongQC.complexDilatation f z + LiZhongQC.complexDilatation f z * hilbertH (LiZhongQC.dzbar f) z := by
  sorry

/-! ## §5.2 Solution of the integral equation -/

/-- **Definition** (solution of the integral equation (5.4), Ch. V §5.2). A solution of `ω = κ + κ S ω` (5.4) is a
function `ω` of the class `L²(Ω)` which satisfies (5.4) almost everywhere in the finite plane `Ω`.
Modelling: `S ω` is `LiZhongQC.hilbertH ω`, the Hilbert transform of the `L²` function `ω`. The book's standing
assumptions on `κ` (measurable, with compact support and `sup |κ| < 1`) are hypotheses of the statements, not part of
the definition. -/
def IsIntegralEqSolution (κ ω : ℂ → ℂ) : Prop :=
  MemLp ω 2 volume ∧ ω =ᵐ[volume] fun z => κ z + κ z * hilbertH ω z

/-- **Unlabelled** (Ch. V §5.2, P2:487). Let `κ` be a measurable function in the finite plane with compact support and
`sup |κ| = k < 1`. The solution of the integral equation (5.4) is uniquely determined up to its values in a set of
area zero.
Modelling: `k` is any bound `< 1` of `|κ|` (the book's `k` is the supremum). -/
theorem integralEq_solution_unique {κ : ℂ → ℂ} {k : ℝ} (hκm : AEStronglyMeasurable κ volume)
    (hκs : HasCompactSupport κ) (hk : k < 1) (hκ : ∀ z, ‖κ z‖ ≤ k) {ω₁ ω₂ : ℂ → ℂ}
    (h₁ : IsIntegralEqSolution κ ω₁) (h₂ : IsIntegralEqSolution κ ω₂) : ω₁ =ᵐ[volume] ω₂ := by
  sorry

/-- **Unlabelled** (Ch. V §5.2, P2:495–551). Let `κ` be as in `integralEq_solution_unique`. The iterates
`ω_n = Σ_{i=0}^{n} κ S_i κ` (5.5), which satisfy `ω₀ = κ` and `ω_n = κ + κ S ω_{n−1}` (5.6), converge in `L²` to a
function `ω`, and `ω` is a solution of (5.4).
Modelling: the iterates are defined by the recursion (5.6), `LiZhongQC.neumannIter κ κ` (`ω₀ = κ`,
`ω_{n+1} = κ S ω_n + κ`), which agrees almost everywhere with the sums (5.5) by the linearity of `S` on `L²`
(`LiZhongQC.hilbertH_add_ae`, `LiZhongQC.hilbertH_smul_ae`); `k` as in `integralEq_solution_unique`. -/
theorem integralEq_solution_neumann {κ : ℂ → ℂ} {k : ℝ} (hκm : AEStronglyMeasurable κ volume)
    (hκs : HasCompactSupport κ) (hk : k < 1) (hκ : ∀ z, ‖κ z‖ ≤ k) :
    ∃ ω : ℂ → ℂ, IsIntegralEqSolution κ ω ∧
      Tendsto (fun n => eLpNorm (neumannIter κ κ n - ω) 2 volume) atTop (𝓝 0) := by
  sorry

/-! ## §5.3 `L^p`-integrability of the solution of the integral equation -/

/-- **Formula (5.8)** (Ch. V §5.3, quoted from Calderón–Zygmund). `‖S‖_p / p < M < ∞` (5.8) as `p → ∞`.
Modelling: there is a finite `M` with `‖S‖_p < M p` for all sufficiently large `p` (`p > 0` there). -/
theorem eq5_5_8 : ∃ M : ℝ, ∀ᶠ p in atTop, hilbertNorm p < M * p := by
  sorry

/-- **Lemma 5.1** (Ch. V §5.3, Bojarski). Let `κ` be as in §5.2: measurable in the finite plane, with compact support
and `sup |κ| = k < 1`. The solution of the integral equation (5.4) belongs to the class `L^p(Ω)` for every `p` for
which `‖S‖_p < 1/k`.
Modelling: `‖S‖_p` is used by the book only for `p > 1` (5.3), hence `1 < p`; the condition is multiplied out,
`k ‖S‖_p < 1` (no `1/0` for `κ = 0`); `k` is any bound `< 1` of `|κ|`, which gives the book's statement for
`k = sup |κ|` and follows from it for larger `k`. -/
theorem lemma5_5_1 {κ : ℂ → ℂ} {k : ℝ} (hκm : AEStronglyMeasurable κ volume) (hκs : HasCompactSupport κ)
    (hk : k < 1) (hκ : ∀ z, ‖κ z‖ ≤ k) {ω : ℂ → ℂ} (hω : IsIntegralEqSolution κ ω) {p : ℝ} (hp : 1 < p)
    (hSp : k * hilbertNorm p < 1) : MemLp ω (ENNReal.ofReal p) volume := by
  sorry

/-! ## §5.4 Integrability of the derivatives of a quasiconformal mapping -/

/-- **Definition** (the limit exponent `p(K)`, Ch. V §5.4): the supremum of all numbers `p` for which all
`K`-quasiconformal mappings have `L^p`-derivatives.
Modelling: `ℝ≥0∞`-valued (H6); `L^p`-derivatives of a mapping of a domain of `ℂ̄` are those of IV.1.1
(`HasLpDerivativesExt`), which the book defines for `p ≥ 1` (III.6.1), and all domains `G` of `ℂ̄` are admitted. The
supremum is over a set containing `2` (Theorem IV.1.2). Junk: for `K < 1` there are no `K`-quasiconformal mappings
and the value is `⊤`; the book uses `p(K)` only for `K ≥ 1`, and every statement below concerns `K ≥ 1` (or
`K → 1` from above, `K → ∞`) or `K`-quasiconformal mappings. -/
def limitExponent (K : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : 1 ≤ p) (_ : ∀ (G : Set ExtPlane) (w : ExtPlane → ExtPlane), IsKQuasiconformal w G K →
    HasLpDerivativesExt w G p), ENNReal.ofReal p

/-- **Theorem 5.1** (Ch. V §5.4), first part. A `K`-quasiconformal mapping has `L^p`-derivatives for every
`p < p(K)`.
Modelling: `1 ≤ p`, the range in which `L^p`-derivatives are defined (III.6.1). -/
theorem thm5_5_1_i {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) {p : ℝ}
    (hp : 1 ≤ p) (hpK : ENNReal.ofReal p < limitExponent K) : HasLpDerivativesExt w G p := by
  sorry

/-- **Theorem 5.1** (Ch. V §5.4), the inequalities (5.10). The limit exponent satisfies
`‖S‖_{p(K)} ≥ (K + 1)/(K − 1)` and `2 < p(K) ≤ 2K/(K − 1)` (5.10).
Modelling: `1 < K`: the bounds of (5.10) are undefined at `K = 1` (where `p(1) = ∞`). The upper bound makes `p(K)`
finite, so `(limitExponent K).toReal` is `p(K)`, and `p(K) > 2 > 1`, where `‖S‖_p = LiZhongQC.hilbertNorm p` is the
book's norm. -/
theorem thm5_5_1_ii {K : ℝ} (hK : 1 < K) :
    2 < limitExponent K ∧ limitExponent K ≤ ENNReal.ofReal (2 * K / (K - 1)) ∧
      (K + 1) / (K - 1) ≤ hilbertNorm (limitExponent K).toReal := by
  sorry

/-- **Unlabelled** (Ch. V §5.4, P2:621–625). `lim_{K → ∞} p(K) = 2`. -/
theorem limitExponent_tendsto_atTop : Tendsto limitExponent atTop (𝓝 2) := by
  sorry

/-- **Unlabelled** (Ch. V §5.4, P2:629–633). `lim_{K → 1} p(K) = ∞`.
Modelling: `K → 1` from above (`K ≥ 1` is the book's standing assumption). -/
theorem limitExponent_tendsto_one : Tendsto limitExponent (𝓝[>] 1) (𝓝 ⊤) := by
  sorry

/-- **Unlabelled** (Ch. V §5.4, P2:635; cited in footnote 49: `0 < α ≤ 2` for `α = liminf_{K → 1} (K − 1) p(K)`).
As `K → 1`, `p(K) → ∞` in such a way that `(K − 1) p(K)` remains between two finite positive bounds.
Modelling: [OCR] `φ(K)` is OCR'd for `p(K)`. There are reals `0 < a` and `0 < b` with
`a ≤ (K − 1) p(K) ≤ b` for all `K > 1` sufficiently close to `1`; the products are taken in `[0, ∞]`, so the upper
bound also asserts that `p(K)` is finite. -/
theorem limitExponent_mul_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ K in 𝓝[>] 1,
      ENNReal.ofReal a ≤ ENNReal.ofReal (K - 1) * limitExponent K ∧
        ENNReal.ofReal (K - 1) * limitExponent K ≤ ENNReal.ofReal b := by
  sorry

/-- **Unlabelled** (Ch. V §5.4; recalled as a fact of V.5.4 in VI.2.2, P2:1733, and at P2:1769). `p(1) = ∞`: every
`1`-quasiconformal mapping has `L^p`-derivatives for every `p`.
Modelling: not stated in V.5.4 itself; it follows from the definition of `p(K)`, `1`-quasiconformal mappings being
conformal (Theorem I.5.1). The value `⊤` here is genuine (`K = 1` is in the book's range). -/
theorem limitExponent_one : limitExponent 1 = ⊤ := by
  sorry

/-- **Unlabelled** (Ch. V §5.4; recalled as a fact of V.5.4 in VI.2.2, P2:1733). `p(K)` decreases monotonically as `K`
increases (and tends to `2` as `K → ∞`, `limitExponent_tendsto_atTop`).
Modelling: "decreases monotonically" is read as non-increasing, which is what follows from the definition (a
`K`-quasiconformal mapping is `K′`-quasiconformal for `K′ ≥ K`); it is stated on `K ≥ 1`, the book's range, so the
junk value `⊤` for `K < 1` is not used. -/
theorem limitExponent_antitoneOn : AntitoneOn limitExponent (Set.Ici 1) := by
  sorry

/-! ## §5.5 Change of area under quasiconformal mappings -/

/-- **Theorem 5.2** (Ch. V §5.5, Bojarski). Let `w` be a `K`-quasiconformal mapping of a domain `G` and `F` a compact
subset of `G − {∞} − {w⁻¹(∞)}`. Then for every `δ < 1 − 2/p(K)` there exists a finite number `C` such that
`m(w(E)) ≤ C (m(E))^δ` (5.11) for every measurable set `E ⊂ F`.
Modelling: `G − {∞} − {w⁻¹(∞)}` is `finiteCore w G` (IV.1.1); `m(w(E))` is the area of the finite part of the image
(III.4.1). Since `p(K) ≥ 2`, the book's range `δ < 1 − 2/p(K)` gives `δ < 1`, and for `δ < 1` it is equivalent to
`2/(1 − δ) < p(K)`, which is also correct for `p(K) = ∞`. Every such `δ` is admitted, as in the book: for `δ ≤ 0`
the power `(m(E))^δ` in `[0, ∞]` has the standard values `0^0 = 1` and `0^δ = ∞` (`δ < 0`) at `m(E) = 0`, and (5.11)
then holds (it is trivial, `m(w(F))` being finite). `C` depends on `w`, `F` and `δ`, not on `E`. -/
theorem thm5_5_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) {F : Set ℂ}
    (hF : IsCompact F) (hFG : F ⊆ finiteCore w G) {δ : ℝ} (hδ₁ : δ < 1)
    (hδ : ENNReal.ofReal (2 / (1 - δ)) < limitExponent K) :
    ∃ C : ℝ≥0, ∀ E ⊆ F, NullMeasurableSet E volume →
      volume (finitePart (w '' toExt E)) ≤ C * volume E ^ δ := by
  sorry

/-! ## §5.6 `L^p`-convergence of the derivatives -/

/-- **Theorem 5.3** (Ch. V §5.6). Let `wₙ` be a sequence of finite-valued `K`-quasiconformal mappings of a domain `G`
of the finite plane. If `wₙ` is a good approximation of the quasiconformal mapping `w` in `G`, then for some `p > 2`
the derivatives `(wₙ)_z` and `(wₙ)_{\bar z}` converge in the `L^p` metric of any compact subset `F` of `G` to `w_z`
and `w_{\bar z}`, respectively.
Modelling: `G = toExt D`, `wₙ = OnePoint.map fₙ`. Added hypothesis: `w` is finite-valued too (`w = OnePoint.map f`),
the book's set-up in 5.6 ("converges … to a finite-valued function `w`", P2:665); it also follows from the
hypotheses. The good approximation is IV.5.4's (`IsGoodApproximation`, which contains the quasiconformality of `w`).
The `L^p` metric of `F` is the `L^p` norm of the difference for the area measure on `F`, which does not see the
junk values of the derivatives on null sets; `p` is chosen before `F`, as in the book. -/
theorem thm5_5_3 {D : Set ℂ} {K : ℝ} {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfn : ∀ n, IsKQuasiconformal (OnePoint.map (fn n)) (toExt D) K)
    (hgood : IsGoodApproximation (fun n => OnePoint.map (fn n)) (OnePoint.map f) (toExt D)) :
    ∃ p : ℝ, 2 < p ∧ ∀ F ⊆ D, IsCompact F →
      Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dz (fn n) z - LiZhongQC.dz f z) (ENNReal.ofReal p)
        (volume.restrict F)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dzbar (fn n) z - LiZhongQC.dzbar f z) (ENNReal.ofReal p)
        (volume.restrict F)) atTop (𝓝 0) := by
  sorry

/-! ## §5.7 Representation of a mapping with prescribed complex dilatation -/

/-- **Formula (5.17)** (Ch. V §5.7). Let `κ` be a measurable function in the plane having bounded support and
satisfying `sup_z |κ(z)| < 1`, and let `w` be the quasiconformal mapping of the plane with complex dilatation equal to
`κ` almost everywhere, normalized by (5.1). Then `w(z) = z + T ω(z)` (5.17) for every `z`, where `ω = w_{\bar z}` is
the solution of the integral equation (5.4) (footnote 50: `T = T_D`, `D` containing the support of `κ`).
Modelling: `w = OnePoint.map f` and (5.1) as in `eq5_5_3`; "the" mapping is any such mapping (it is unique by the
Uniqueness theorem). The integrand of `T ω(z)` is asserted to be integrable over the plane, so the value of
`LiZhongQC.cauchyT`, a Lebesgue integral over the plane, is the book's `T_D ω(z)`: `ω` vanishes almost everywhere
outside the support of `κ`, hence outside `D`. -/
theorem eq5_5_17 {κ : ℂ → ℂ} (hκm : AEStronglyMeasurable κ volume) (hκb : Bornology.IsBounded (Function.support κ))
    (hκ : ∃ k : ℝ, k < 1 ∧ ∀ z, ‖κ z‖ ≤ k) {f : ℂ → ℂ} (hf : IsQuasiconformalMap (OnePoint.map f) univ)
    (hfκ : ∀ᵐ z ∂volume, LiZhongQC.complexDilatation f z = κ z)
    (hhol : ∃ R : ℝ, DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hnorm : Tendsto (fun z => f z - z) (Bornology.cobounded ℂ) (𝓝 0)) :
    IsIntegralEqSolution κ (LiZhongQC.dzbar f) ∧
      ∀ z : ℂ, Integrable (fun ζ => LiZhongQC.dzbar f ζ / (ζ - z)) ∧
        f z = z + cauchyT (LiZhongQC.dzbar f) z := by
  sorry

end LehtoVirtanen1973
