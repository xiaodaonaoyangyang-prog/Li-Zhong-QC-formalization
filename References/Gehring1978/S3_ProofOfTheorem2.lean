import References.Gehring1978.S1_Introduction
import References.Gehring1978.S2_Spirals

/-!
# Gehring 1978, §3 Proof of Theorem 2

F. W. Gehring, *Spirals and the universal Teichmüller space*, Acta Math. 141 (1978), §3; source `full.md` of
`Spirals and the universal Teichmüller space.pdf-602096dc…`, lines 439–625 (and lines 69–83 of §1).

* Definition (the spirals `α₁`, `α₂`, the Jordan curve `β`, the arc `γ`, the domains `D₁`, `D₂` and `D = ℂ̄ - γ`,
  for `a ∈ (0, ∞)`; §3, previewed in §1) — `alpha1`, `alpha2`, `betaCurve`, `gammaArc`, `domD1`, `domD2`, `domD`
* Unlabelled (§3, l. 447: `β` is a Jordan curve which separates `α₁` and `α₂`; `D` is a simply connected domain of
  hyperbolic type) — `betaCurve_separates`
* Lemma 6 — `lemma6`
* Unlabelled (§3, l. 483: the Remark after Lemma 6, the limits `f₁(0)`, `f₂(0)`) — `lemma6_remark`
* Lemma 7 — `lemma7`
* Lemma 8 — `lemma8`
* Lemma 9 — `lemma9`
* Unlabelled (§1, l. 69–75: Theorem 2 holds with `D = ℂ̄ - γ` for every `a ∈ (0, 1/8π)`; proved in §3,
  l. 609–625) — `thm2_explicit`

Not items (DESIGN §3):
- `D ⊇ D₁ ∪ D₂` (l. 447): immediate, since `γ ⊆ β` (U−);
- the outline of l. 449 (restated as `thm2_explicit` and Lemmas 8, 9);
- the Remark after Lemma 7 (l. 531: an alternative proof method).

**Standing assumptions.**
- The sets are defined for every `a > 0` (l. 441).
- Lemmas 6 and 9 are stated for `a > 0`: the paper's `a ∈ (0, 1/8π)` (l. 449) is used only in Lemma 8, which repeats
  it.
- "`f` fixes `∞`" means `f(z) → ∞` as `z → ∞` (through `LiZhongQC.meroToExt`).
- `‖S_f‖_D` is Gehring's `hypNorm`.
- `D` is simply connected of hyperbolic type (l. 447, `betaCurve_separates`), so `hypDensity (domD a)` is the genuine
  density. The norm hypotheses of the lemmas therefore never see the junk value of `hypDensity`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Gehring1978

open LiZhongQC References

/-- **Definition** (§3, also §1). `α₁ = {e^{(-a+i)t} : t ∈ (0, ∞)}`. -/
def alpha1 (a : ℝ) : Set ℂ :=
  logSpiral a '' Ioi 0

/-- **Definition** (§3, also §1). `α₂ = {z : -z ∈ α₁}`. -/
def alpha2 (a : ℝ) : Set ℂ :=
  {z | -z ∈ alpha1 a}

/-- **Definition** (§3). `β = {± i e^{(-a+i)t} : t ∈ (-∞, ∞)} ∪ {0, ∞}`, a subset of `ℂ̄`. -/
def betaCurve (a : ℝ) : Set ExtPlane :=
  toExt {z : ℂ | ∃ t : ℝ, z = I * logSpiral a t ∨ z = -(I * logSpiral a t)} ∪ {((0 : ℂ) : ExtPlane), extInf}

/-- **Definition** (§3, also §1). `γ = {z ∈ β : |z| ≤ 1}`, that is `{± i e^{(-a+i)t} : t ∈ [0, ∞)} ∪ {0}`. -/
def gammaArc (a : ℝ) : Set ExtPlane :=
  toExt {z : ℂ | (z : ExtPlane) ∈ betaCurve a ∧ ‖z‖ ≤ 1}

/-- **Definition** (§3, also §1). The domain `D = ℂ̄ - γ` (it contains `∞`). -/
def domD (a : ℝ) : Set ExtPlane :=
  (gammaArc a)ᶜ

/-- **Definition** (§3). `D₁`, the component of `ℂ̄ - β` which contains `α₁`, as a subset of `ℂ` (`∞ ∈ β`).
Modelling: the union of the components of `ℂ̄ - β` meeting `α₁`; this is one component because `α₁` is connected and
disjoint from `β`. -/
def domD1 (a : ℝ) : Set ℂ :=
  finitePart (⋃ w ∈ alpha1 a, connectedComponentIn (betaCurve a)ᶜ (w : ExtPlane))

/-- **Definition** (§3). `D₂`, the component of `ℂ̄ - β` which contains `α₂`, as a subset of `ℂ`; modelled as
`domD1`. -/
def domD2 (a : ℝ) : Set ℂ :=
  finitePart (⋃ w ∈ alpha2 a, connectedComponentIn (betaCurve a)ᶜ (w : ExtPlane))

/-- **Unlabelled claim** (§3, l. 447). For `a > 0`, `β` is a Jordan curve which separates `α₁` and `α₂`, and
`D = ℂ̄ - γ` is a simply connected domain of hyperbolic type.
Modelling: `α_j` lies in one component `D_j` of `ℂ̄ - β` (presupposed by the definition of `D_j`), and "separates"
means that these components differ, i.e. are disjoint. The paper's `D ⊇ D₁ ∪ D₂` is immediate (`γ ⊆ β`) and not
restated. -/
theorem betaCurve_separates {a : ℝ} (ha : 0 < a) :
    IsJordanCurve (betaCurve a) ∧ alpha1 a ⊆ domD1 a ∧ alpha2 a ⊆ domD2 a ∧ Disjoint (domD1 a) (domD2 a) ∧
      IsHypSimplyConnectedExt (domD a) := by
  sorry

/-- **Lemma 6** (§3). There exists `δ₁ = δ₁(a) > 0` with the following property. If `f` is conformal in `D` and
`‖S_f‖_D ≤ δ₁`, then for `j = 1, 2` the mapping `f_j = f|D_j` has a quasiconformal extension `g_j` to `ℂ̄` and (19)
`K(g_j) ≤ (1 - c ‖S_f‖_D)⁻¹`, where `c = c(a)` and `K(g_j)` denotes the maximal dilatation of `g_j`.
Modelling: `a > 0` (standing assumptions of this file); "a quasiconformal extension with `K(g_j) ≤ K`" is
`LiZhongQC.HasQCExtensionExt f D_j K`; the bound (19) is meaningful only when `c ‖S_f‖_D < 1`, which is recorded as
`c δ₁ < 1`. -/
theorem lemma6 {a : ℝ} (ha : 0 < a) :
    ∃ δ₁ > (0 : ℝ), ∃ c > (0 : ℝ), c * δ₁ < 1 ∧ ∀ f : ℂ → ℂ, IsConformalExt f (domD a) →
      hypNorm (schwarzian f) (domD a) ≤ ENNReal.ofReal δ₁ →
        HasQCExtensionExt f (domD1 a) (1 - c * (hypNorm (schwarzian f) (domD a)).toReal)⁻¹ ∧
          HasQCExtensionExt f (domD2 a) (1 - c * (hypNorm (schwarzian f) (domD a)).toReal)⁻¹ := by
  sorry

/-- **Remark after Lemma 6** (§3, l. 483; unlabelled claim). If `f` is conformal in `D` with `‖S_f‖_D ≤ δ₁`, then
`f_j = f|D_j` has a homeomorphic extension to `D_j ∪ {0}`, and hence `f(z)` has limits `f₁(0)`, `f₂(0)` as `z → 0` in
`D₁` and in `D₂`.
Modelling: `a > 0`. The paper's `δ₁` is that of Lemma 6; here it is existential. Both properties pass to smaller `δ₁`,
so a common `δ₁` exists (the minimum) and nothing is lost. Values and limits are in `ℂ̄` (through
`LiZhongQC.meroToExt`), since without a normalization `f_j(0)` may be `∞`. The homeomorphic extension is an extension
of `f|D_j` which is an embedding of `D_j ∪ {0}` into `ℂ̄`. -/
theorem lemma6_remark {a : ℝ} (ha : 0 < a) :
    ∃ δ₁ > (0 : ℝ), ∀ f : ℂ → ℂ, IsConformalExt f (domD a) → hypNorm (schwarzian f) (domD a) ≤ ENNReal.ofReal δ₁ →
      (∃ F : ExtPlane → ExtPlane, (∀ z ∈ domD1 a, F z = meroToExt f z) ∧
          IsEmbedding ((toExt (domD1 a) ∪ {((0 : ℂ) : ExtPlane)}).domRestrict F)) ∧
        (∃ F : ExtPlane → ExtPlane, (∀ z ∈ domD2 a, F z = meroToExt f z) ∧
          IsEmbedding ((toExt (domD2 a) ∪ {((0 : ℂ) : ExtPlane)}).domRestrict F)) ∧
        (∃ w : ExtPlane, Tendsto (meroToExt f) (𝓝[domD1 a] 0) (𝓝 w)) ∧
        ∃ w : ExtPlane, Tendsto (meroToExt f) (𝓝[domD2 a] 0) (𝓝 w) := by
  sorry

/-- **Lemma 7** (§3). For each `η > 0` there exists `K₁ = K₁(η) ∈ (1, ∞)` with the following property. If `g` is a
sense preserving quasiconformal mapping of `ℂ̄` with `K(g) ≤ K₁` and if `g` fixes three points `z₁, z₂, ∞`, then (22)
`|g(z) - z| ≤ η |z₁ - z₂|` for `z` with `|z - z₁| < |z₁ - z₂|`.
Modelling: the OCR's `Ū` is read as `ℂ̄` (the proof, l. 507, says `ℂ̄`); a quasiconformal self-map of `ℂ̄` fixing `∞`
is a `K₁`-quasiconformal (hence sense preserving) homeomorphism of `ℂ` onto `ℂ` (`LiZhongQC.IsKQC`); "three points"
gives `z₁ ≠ z₂`. -/
theorem lemma7 {η : ℝ} (hη : 0 < η) :
    ∃ K₁ > (1 : ℝ), ∀ g : ℂ → ℂ, IsKQC g univ K₁ → g '' univ = univ → ∀ z₁ z₂ : ℂ, z₁ ≠ z₂ → g z₁ = z₁ →
      g z₂ = z₂ → ∀ z : ℂ, ‖z - z₁‖ < ‖z₁ - z₂‖ → ‖g z - z‖ ≤ η * ‖z₁ - z₂‖ := by
  sorry

/-- **Lemma 8** (§3). For each `a ∈ (0, 1/8π)` there exists `δ₂ = δ₂(a) ∈ (0, δ₁]` with the following property. If `f`
is conformal in `D` with `‖S_f‖_D ≤ δ₂` and if `f` fixes `∞`, then for `j = 1, 2`, `α_j* = f(α_j)` is a `b*`-spiral
onto `f_j(0)` where `b* ∈ (1, 2)`.
Modelling: `b*` depends only on `a`, as in the proof, which fixes `b*` before `δ₂`. The spirals start at `f(1)` and
`f(-1)` (the proof). `f_j(0)` is the limit of `f` at `0` from `D_j` (Remark after Lemma 6, `lemma6_remark`); its
existence is part of the conclusion, and this replaces the bound `δ₂ ≤ δ₁`, whose only role is to make `f_j(0)`
exist. -/
theorem lemma8 {a : ℝ} (ha : 0 < a) (ha' : a < 1 / (8 * π)) :
    ∃ δ₂ > (0 : ℝ), ∃ b' ∈ Ioo (1 : ℝ) 2, ∀ f : ℂ → ℂ, IsConformalExt f (domD a) →
      hypNorm (schwarzian f) (domD a) ≤ ENNReal.ofReal δ₂ → Tendsto (meroToExt f) (cocompact ℂ) (𝓝 extInf) →
        (∃ w : ℂ, Tendsto f (𝓝[domD1 a] 0) (𝓝 w) ∧ IsBSpiral (f '' alpha1 a) (f 1) w b') ∧
          (∃ w : ℂ, Tendsto f (𝓝[domD2 a] 0) (𝓝 w) ∧ IsBSpiral (f '' alpha2 a) (f (-1)) w b') := by
  sorry

/-- **Lemma 9** (§3). For each `ε > 0` there exists `δ₃ = δ₃(a, ε) ∈ (0, δ₁]` with the following property. If `f` is
conformal in `D` with `‖S_f‖_D ≤ δ₃` and if `f` fixes `1, -1, ∞`, then `|f₁(0)| ≤ ε` and `|f₂(0)| ≤ ε`.
Modelling: `a > 0` (standing assumptions of this file); the limits `f_j(0)` and the bound `δ₃ ≤ δ₁` are handled as in
`lemma8`. -/
theorem lemma9 {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₃ > (0 : ℝ), ∀ f : ℂ → ℂ, IsConformalExt f (domD a) → hypNorm (schwarzian f) (domD a) ≤ ENNReal.ofReal δ₃ →
      f 1 = 1 → f (-1) = -1 → Tendsto (meroToExt f) (cocompact ℂ) (𝓝 extInf) →
        (∃ w : ℂ, Tendsto f (𝓝[domD1 a] 0) (𝓝 w) ∧ ‖w‖ ≤ ε) ∧
          (∃ w : ℂ, Tendsto f (𝓝[domD2 a] 0) (𝓝 w) ∧ ‖w‖ ≤ ε) := by
  sorry

/-- **Theorem 2, explicit form** (§1, l. 69–75, unlabelled; proved in §3, l. 609–625). For every `a ∈ (0, 1/8π)`
the domain `D = ℂ̄ - γ` is a simply connected domain of hyperbolic type, and there is `δ = δ(a) > 0` such that `f(D)`
is not a Jordan domain whenever `f` is conformal in `D` with `‖S_f‖_D ≤ δ`.
Modelling: as in `thm2`; the claim that `D` is simply connected of hyperbolic type is that of l. 447
(`betaCurve_separates`). -/
theorem thm2_explicit {a : ℝ} (ha : 0 < a) (ha' : a < 1 / (8 * π)) :
    IsHypSimplyConnectedExt (domD a) ∧ ∃ δ > (0 : ℝ), ∀ f : ℂ → ℂ, IsConformalExt f (domD a) →
      hypNorm (schwarzian f) (domD a) ≤ ENNReal.ofReal δ → ¬ IsJordanDomainExt (imageExt f (domD a)) := by
  sorry

end Gehring1978
