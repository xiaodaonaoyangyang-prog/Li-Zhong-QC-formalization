import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC

/-!
# Lehto–Virtanen, Chapter V §7: Regularity of a mapping with prescribed complex dilatation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §7
(pp. 233–238; `full.md` P2:1328–1567).

Conventions. The book considers only finite points and domains of the finite plane (P2:1330, 1426): a domain `G` of
the finite plane is `toExt D` for `D : Set ℂ`, and a quasiconformal mapping `w : G → G′` onto a domain `G′` of the
finite plane is `OnePoint.map f` for `f : ℂ → ℂ`. Its complex dilatation `κ = w_{\bar z}/w_z` is
`LiZhongQC.complexDilatation f`, the book's value at the regular points of `w` (where `w_z ≠ 0`), i.e. almost
everywhere (Theorem IV.1.4); every statement uses it almost everywhere, in integrals, or at a point asserted to be
regular. "Almost everywhere in `G`" refers to the area measure on `D`, and a measurable function is an almost
everywhere strongly measurable one. A regular point and a regular quasiconformal mapping are those of Ch. I (§1.6,
§3.3; the book restates the latter at P2:1416).

* Theorem 7.1 (§7.1) — `thm5_7_1`
* Definition (uniform convergence of the integral of (7.1), with `κ₀ = κ(z₀)`, on the compact subsets of `G`, §7.2) —
  `DilIntegralConvergesUniformly`
* Definition (regular quasiconformal mapping of `G`: regular at every point, with continuous partial derivatives,
  recalled §7.2) — exists: `LehtoVirtanen1973.IsRegularQuasiconformal` (Ch. I §3.3)
* Theorem 7.2 (§7.2) — `thm5_7_2`

Not stated (inventory: omitted): the remark that the restriction to finite points can be removed by a linear mapping
(P2:1330); the remark that the regularity of a quasiconformal mapping at `z₀` cannot be deduced from its dilatation
quotient for `z ≠ z₀` (P2:1332); the remarks of 7.2 that continuous differentiability does not follow from
regularity at every point, nor from (7.1) at every point (P2:1416, cf. 6.2), and that `κ(z₀)` in the uniform
condition must be the complex dilatation at `z₀` (P2:1424, a consequence of Theorem 7.1); the steps (7.2)–(7.10) of
the proofs; Bojarski's condition (7.11) and the remark that it is contained in Theorem 7.1 (P2:1472–1478); and the
examples of 7.3 on the sharpness of the conditions, including the quoted result of Reich and Walczak with its
construction (7.12) (P2:1480–1566). Footnote 52 is bibliographic (a refinement of (7.1) by Reich and Walczak, not
stated in the book). The recollection (P2:1332) of the equivalence noted in 6.2 is stated in §6
(`dilQuot_integral_lt_top_iff`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)

/-! ## §7.1 Complex dilatation and regular points -/

/-- **Theorem 7.1** (Ch. V §7.1). Let `G` and `G′` be domains of the finite plane, `z₀` a point of `G`, and
`w : G → G′` a quasiconformal mapping with complex dilatation `κ`, where `|κ(z)| ≤ k < 1` almost everywhere in `G`.
If there exists a number `κ₀` such that `∬_{|z − z₀| < r} |κ(z) − κ₀|/|z − z₀|² dσ < ∞` (7.1) for some `r > 0`, then
`w` is regular at `z₀` and `κ(z₀) = κ₀`.
Modelling: [OCR] (7.1) is OCR'd with `τ` for `r` (P2:1343). `G = toExt D`, `w = OnePoint.map f`; the disc of (7.1) is
taken inside `D`, where `κ` is defined (the finiteness for one `r` gives it for every smaller `r`). At a regular point
of the sense-preserving `w` the Jacobian is positive, so `w_z(z₀) ≠ 0` and `LiZhongQC.complexDilatation f z₀` is the
book's `κ(z₀)`. -/
theorem thm5_7_1 {D : Set ℂ} {f : ℂ → ℂ} (hf : IsQuasiconformalMap (OnePoint.map f) (toExt D)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) {k : ℝ} (hk : k < 1)
    (hκ : ∀ᵐ z ∂(volume.restrict D), ‖LiZhongQC.complexDilatation f z‖ ≤ k) {κ₀ : ℂ}
    (h71 : ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ D ∧
      ∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal (‖LiZhongQC.complexDilatation f z - κ₀‖ / ‖z - z₀‖ ^ 2) < ⊤) :
    IsRegularPointOf (OnePoint.map f) (toExt D) z₀ ∧ LiZhongQC.complexDilatation f z₀ = κ₀ := by
  sorry

/-! ## §7.2 Continuous differentiability -/

/-- **Definition** (uniform convergence on compact sets of the integral of (7.1), Ch. V §7.2). The integral
`∬ |κ(z) − κ(z₀)|/|z − z₀|² dσ_z` converges uniformly in every compact subset `F` of `G`: for every `ε > 0` there
exists a `δ > 0` such that `∬_{|z − z₀| < δ} |κ(z) − κ(z₀)|/|z − z₀|² dσ < ε` for every `z₀ ∈ F`.
Modelling: [OCR or misprint] the source reads "`z₀ ∉ F`" (P2:1424); the condition is for the points of `F`.
`G = toExt D`; the disc is intersected with `D`, where `κ` is defined, which changes nothing for the small `δ` that
matter (the condition passes to smaller `δ`, and for `δ` below the distance from `F` to the complement of `D` the disc
lies in `D`). `κ` is evaluated at every point `z₀ ∈ F`, so it is a genuine function on `D` (not a class of functions
equal almost everywhere), as in the book. -/
def DilIntegralConvergesUniformly (κ : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ F ⊆ D, IsCompact F → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ ∈ F,
    ∫⁻ z in Metric.ball z₀ δ ∩ D, ENNReal.ofReal (‖κ z - κ z₀‖ / ‖z - z₀‖ ^ 2) < ENNReal.ofReal ε

/-- **Theorem 7.2** (Ch. V §7.2). Let `κ`, `|κ| ≤ k < 1`, be a measurable function in a domain `G` (of the finite
plane) such that the integral `∬ |κ(z) − κ(z₀)|/|z − z₀|² dσ_z` converges uniformly in every compact subset of `G`.
Then every quasiconformal mapping `w : G → G′` whose complex dilatation coincides with `κ` almost everywhere in `G` is a
regular quasiconformal mapping of `G` and has the complex dilatation `κ(z)` for every `z ∈ G`.
Modelling: `G = toExt D`, `w = OnePoint.map f`; `|κ| ≤ k` at every point of `D` (the book uses `κ` pointwise). Every
point of `G` is then a regular point of `w`, so `LiZhongQC.complexDilatation f z` is the book's `κ(z)` everywhere. -/
theorem thm5_7_2 {D : Set ℂ} (hD : IsDomainExt (toExt D)) {κ : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hκm : AEStronglyMeasurable κ (volume.restrict D)) (hκ : ∀ z ∈ D, ‖κ z‖ ≤ k)
    (hunif : DilIntegralConvergesUniformly κ D) {f : ℂ → ℂ} (hf : IsQuasiconformalMap (OnePoint.map f) (toExt D))
    (hfκ : ∀ᵐ z ∂(volume.restrict D), LiZhongQC.complexDilatation f z = κ z) :
    IsRegularQuasiconformal (OnePoint.map f) (toExt D) ∧ ∀ z ∈ D, LiZhongQC.complexDilatation f z = κ z := by
  sorry

end LehtoVirtanen1973
