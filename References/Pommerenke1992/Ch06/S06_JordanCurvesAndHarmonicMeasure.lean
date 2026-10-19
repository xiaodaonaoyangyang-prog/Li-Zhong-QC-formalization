import References.Pommerenke1992.Ch06.S05_SectorialAccessibility

/-!
# Pommerenke 1992, Ch. 6 §6.6 Jordan Curves and Harmonic Measure

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §6.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 6439–6591.

* Definition (the harmonic measures `ω`, `ω*` of (6.6.1); used in (6.6.4)–(6.6.6), (6.6.9)) —
  `boundaryHarmonicMeasure`
* Definition (the sets `S`, `S*` of (6.6.2)) and the claim `S = f(Sect(f))` of (6.6.2) (used in (6.6.4), (6.6.6) and
  in the proofs of Proposition 6.28 and Theorem 6.30) — `triangleVertexSet`, `eq6_6_2`
* Definition (the set `T` of the points where `J` has a tangent, (6.6.3); index "tangent … 151, 153") —
  `tangentPointSet`
* Unlabelled (§6.6, l. 6455: `T ⊆ S ∩ S*`, "It is clear"; used for (6.6.5) and in the proof of Proposition 6.28) —
  `tangentPointSet_subset`
* Formula (6.6.4) (the McMillan sector theorem in the form of §6.6; cited "(4)" at l. 6469, 6494, 6572) — `eq6_6_4`
* Formula (6.6.5) (cited "(5)" in the remarks at l. 6518, 6526) — `eq6_6_5`
* Unlabelled (§6.6, l. 6469: `S ∩ S* ≗ T`; used in the proof of Theorem 6.30, l. 6572) —
  `inter_ae_eq_tangentPointSet`
* Proposition 6.28 ((6.6.7)) — `prop6_28`
* Proposition 6.29 ((6.6.8); cited at l. 6526) — `prop6_29`
* Theorem 6.30 (BiCaGaJo89; (6.6.9) cited "(9)" at l. 6526; cited at P2 l. 1318) — `thm6_30`

Helper definitions: `outerDomain` (the outer domain `G*` of `J`, written inline in `cor5_13`) and `IsJordanSetting`
(the standing assumption of the section).

Not items (DESIGN §3): the identifications `ω(E) ≡ ω(f(0), E, G)` and `ω*(E) ≡ ω(f*(∞), E, G*)` in (6.6.1) (U−, by
(4.4.5) and (4.4.9); leader ruling QC5); "`f` is conformal at `f⁻¹(w)` for almost all `w ∈ S`" (l. 6469, a step
towards `inter_ae_eq_tangentPointSet`); (6.6.6), the Makarov compression theorem in the form of §6.6, and the remarks
on the concentration of `ω` on a set of sigma-finite linear measure (l. 6474–6480, Mak84; a restatement of Theorem
6.25, not cited); the remarks after Theorem 6.30 (l. 6518: `ω` and `ω*` are mutually singular if and only if
`Λ(T) = 0`; Dirichlet algebras, BrWe63; Bis88; BiJo92); the conformal welding (6.6.10) and "`φ` is singular if and
only if `Λ(T) = 0`" (l. 6520–6526, a recall of §2.3, §5.4 and a remark); Exercises 6.6.1–6.6.5.

**Standing assumption** (l. 6441): `J ⊆ ℂ` is a Jordan curve with inner domain `G` and outer domain `G*`; `f` maps `𝔻`
conformally onto `G` and `f*` maps `𝔻* = {|z| > 1} ∪ {∞}` conformally onto `G*`; both have continuous injective
extensions `F`, `F*` to `𝕋` (Theorem 2.6). This is `IsJordanSetting J f F fs Fs`, with `f*` a map of `Ĉ` (the Ch. 5
convention of `cor5_13`, `LehtoVirtanen1973.IsConformalMap` on `extDiscExterior`).

**Conventions.** As in §6.2–§6.5.
- `ω`, `ω*` are modelled literally by (6.6.1) (leader ruling QC5): `ω(E) = Λ(f⁻¹(E))/(2π)` with
  `f⁻¹(E) = {ζ ∈ 𝕋 : F(ζ) ∈ E}` and the arc length `Λ` on `𝕋` (outer measure, all `E`), and likewise
  `ω*(E) = Λ(f*⁻¹(E))/(2π)` with `F*`; values in `[0, ∞]`.
- `Sect(f*)` is transported by conjugation (leader ruling Q6.9): `ζ ∈ Sect(f*)` if and only if
  `ζ̄ ∈ Sect(z ↦ f*(1/z))`, where `z ↦ 1/z` is the Möbius map `LiZhongQC.mobiusExt 0 1 1 0` of `Ĉ` (it sends `0` to
  `∞`), and `1/ζ = ζ̄` on `𝕋`.
- `E ≗ E'` is written as the two null differences, with `Λ = μH[1]` for sets on `J` and the arc length for sets on
  `𝕋`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve mobiusExt)
open LehtoVirtanen1973 (IsConformalMap)

/-- The outer domain `G*` of a Jordan curve `J ⊆ ℂ` (helper, §6.6, l. 6441): the component of `Ĉ ∖ J` that contains
`∞`, that is, the points of `ℂ` off `J` and off the inner domain of `J`, together with `∞` (as in `cor5_13`). -/
def outerDomain (J : Set ℂ) : Set ExtPlane :=
  toExt {z | z ∉ J ∧ z ∉ innerDomain J} ∪ {extInf}

/-- The standing assumption of §6.6 (helper, l. 6441): `J ⊆ ℂ` is a Jordan curve; `f` maps `𝔻` conformally onto the
inner domain `G` of `J` and `F` is its continuous injective extension to `𝔻̄`; `f*` maps `𝔻*` conformally onto the
outer domain `G*` of `J` and `F*` is its continuous injective extension to `{|z| ≥ 1}` (Theorem 2.6). -/
def IsJordanSetting (J : Set ℂ) (f F : ℂ → ℂ) (fs : ExtPlane → ExtPlane) (Fs : ℂ → ExtPlane) : Prop :=
  IsJordanCurve (toExt J) ∧ IsConformalOnto f unitDisc (innerDomain J) ∧ ContinuousOn F (closedBall 0 1) ∧
    InjOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧ IsConformalMap fs extDiscExterior ∧
    fs '' extDiscExterior = outerDomain J ∧ ContinuousOn Fs {z : ℂ | 1 ≤ ‖z‖} ∧ InjOn Fs {z : ℂ | 1 ≤ ‖z‖} ∧
    ∀ z : ℂ, 1 < ‖z‖ → Fs z = fs z

/-- **Definition (6.6.1)** (§6.6; used in (6.6.4)–(6.6.6), (6.6.9)). The harmonic measures
`ω(E) = Λ(f⁻¹(E))/(2π)` and `ω*(E) = Λ(f*⁻¹(E))/(2π)` of `E ⊆ J`, where `f⁻¹(E) = {ζ ∈ 𝕋 : f(ζ) ∈ E}` for the
boundary map `F` of `f` (resp. `F*` of `f*`).
Modelling: `ω(E)` is `boundaryHarmonicMeasure F E` and `ω*(E)` is `boundaryHarmonicMeasure Fs (toExt E)`; `Λ` is the
arc length on `𝕋` (outer measure, so every `E` is allowed); values in `[0, ∞]` (at most `1`). -/
def boundaryHarmonicMeasure {X : Type*} (F : ℂ → X) (E : Set X) : ℝ≥0∞ :=
  circleMeasure {ζ ∈ sphere (0 : ℂ) 1 | F ζ ∈ E} / ENNReal.ofReal (2 * π)

/-- **Definition (6.6.2)** (§6.6). `S = {w ∈ J : there is an open triangle of vertex w in G}`, similarly `S*` with
`G*` instead of `G`.
Modelling: `S` is `triangleVertexSet (toExt G) J` and `S*` is `triangleVertexSet G* J`; the triangles are triangles
of `ℂ`. -/
def triangleVertexSet (D : Set ExtPlane) (J : Set ℂ) : Set ℂ :=
  {w ∈ J | ∃ T : Set ℂ, IsOpenTriangleAt T w ∧ toExt T ⊆ D}

/-- **Definition (6.6.3)** (§6.6). `T = {w ∈ J : J has a tangent at w}`.
Modelling: `J` has a tangent at `w = f(e^{iϑ})` when `∂G = J` has a tangent there in the sense of §3.4 (a corner of
opening `π` of the boundary map `F`, `HasTangentAt`); this depends only on the curve `J` (the one-sided limit
directions of the chords at `w` differ by `π`). -/
def tangentPointSet (F : ℂ → ℂ) : Set ℂ :=
  {w | ∃ ϑ β : ℝ, F (exp (ϑ * I)) = w ∧ HasTangentAt (fun z => (F z : ExtPlane)) ϑ β}

/-- **Unlabelled claim (6.6.2)** (§6.6, l. 6449; used in (6.6.4), (6.6.6) and in the proofs of Proposition 6.28 and
Theorem 6.30). `S = f(Sect(f))`, and similarly `S* = f*(Sect(f*))`.
Modelling: `f(Sect(f))` is the image of `Sect(f)` under the boundary map `F`; `f*(Sect(f*))` is the image under `F*`
of the conjugation transport of `Sect` (see the file header). -/
theorem eq6_6_2 {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) :
    triangleVertexSet (toExt (innerDomain J)) J = F '' sect (fun z => (f z : ExtPlane)) ∧
      triangleVertexSet (outerDomain J) J =
        {w : ℂ | ∃ ζ ∈ sphere (0 : ℂ) 1,
          conj ζ ∈ sect (fun z => fs (mobiusExt 0 1 1 0 z)) ∧ Fs ζ = (w : ExtPlane)} := by
  sorry

/-- **Unlabelled claim** (§6.6, l. 6455: "It is clear that `T ⊆ S ∩ S*`"; used for (6.6.5) and in the proof of
Proposition 6.28). -/
theorem tangentPointSet_subset {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) :
    tangentPointSet F ⊆ triangleVertexSet (toExt (innerDomain J)) J ∩ triangleVertexSet (outerDomain J) J := by
  sorry

/-- **Formula (6.6.4)** (§6.6; the McMillan sector theorem in the form of §6.6; cited "(4)" at l. 6469, 6494, 6572).
`Λ(E) = 0 ⇔ ω(E) = 0` and `Λ(E*) = 0 ⇔ ω*(E*) = 0` for `E ⊆ S` and `E* ⊆ S*`.
Modelling: `E`, `E*` are any subsets (outer measures). -/
theorem eq6_6_4 {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) :
    (∀ E ⊆ triangleVertexSet (toExt (innerDomain J)) J, μH[1] E = 0 ↔ boundaryHarmonicMeasure F E = 0) ∧
      ∀ E ⊆ triangleVertexSet (outerDomain J) J, μH[1] E = 0 ↔ boundaryHarmonicMeasure Fs (toExt E) = 0 := by
  sorry

/-- **Formula (6.6.5)** (§6.6; cited "(5)" in the remarks at l. 6518, 6526). For `E ⊆ T`,
`Λ(E) = 0 ⇔ ω(E) = 0 ⇔ ω*(E) = 0`. -/
theorem eq6_6_5 {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) {E : Set ℂ} (hE : E ⊆ tangentPointSet F) :
    (μH[1] E = 0 ↔ boundaryHarmonicMeasure F E = 0) ∧
      (boundaryHarmonicMeasure F E = 0 ↔ boundaryHarmonicMeasure Fs (toExt E) = 0) := by
  sorry

/-- **Unlabelled claim** (§6.6, l. 6469; used in the proof of Theorem 6.30, l. 6572). `S ∩ S* ≗ T`, that is, the two
differences have zero linear measure. -/
theorem inter_ae_eq_tangentPointSet {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) :
    μH[1] ((triangleVertexSet (toExt (innerDomain J)) J ∩ triangleVertexSet (outerDomain J) J) \
        tangentPointSet F) = 0 ∧
      μH[1] (tangentPointSet F \
        (triangleVertexSet (toExt (innerDomain J)) J ∩ triangleVertexSet (outerDomain J) J)) = 0 := by
  sorry

/-- **Proposition 6.28** (§6.6). If `J` is a quasicircle, then (6.6.7) `T ≗ S ≗ S*`, `f⁻¹(T) ≗ Sect(f)`.
Modelling: `T ≗ S ≗ S*` is `T ≗ S` and `S ≗ S*`; `f⁻¹(T) = {ζ ∈ 𝕋 : F(ζ) ∈ T}`, and `≗` on `𝕋` is measured by arc
length; quasicircles are those of Ch. 5 (`IsQuasicircle`). -/
theorem prop6_28 {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) (hJq : IsQuasicircle J) :
    (μH[1] (tangentPointSet F \ triangleVertexSet (toExt (innerDomain J)) J) = 0 ∧
      μH[1] (triangleVertexSet (toExt (innerDomain J)) J \ tangentPointSet F) = 0) ∧
    (μH[1] (triangleVertexSet (toExt (innerDomain J)) J \ triangleVertexSet (outerDomain J) J) = 0 ∧
      μH[1] (triangleVertexSet (outerDomain J) J \ triangleVertexSet (toExt (innerDomain J)) J) = 0) ∧
    circleMeasure ({ζ ∈ sphere (0 : ℂ) 1 | F ζ ∈ tangentPointSet F} \ sect (fun z => (f z : ExtPlane))) = 0 ∧
    circleMeasure (sect (fun z => (f z : ExtPlane)) \ {ζ ∈ sphere (0 : ℂ) 1 | F ζ ∈ tangentPointSet F}) = 0 := by
  sorry

/-- **Proposition 6.29** (§6.6; cited at l. 6526). There is a starlike Jordan curve `J` such that (6.6.8) `T = ∅`,
`Sect(f) ≗ Sect(f*) ≗ 𝕋`.
Modelling: a starlike Jordan curve is a Jordan curve whose inner domain is starlike with respect to `0` (§3.6; the
curve of the proof is a polar graph `r(ϑ)e^{iϑ}`); the conclusion holds for all maps `f`, `f*` of the standing
assumption; `Sect(f*)` is the conjugation transport of `Sect` (see the file header); `≗ 𝕋` is a null complement in
`𝕋`, measured by arc length. -/
theorem prop6_29 :
    ∃ J : Set ℂ, IsJordanCurve (toExt J) ∧ StarConvex ℝ 0 (innerDomain J) ∧
      ∀ (f F : ℂ → ℂ) (fs : ExtPlane → ExtPlane) (Fs : ℂ → ExtPlane), IsJordanSetting J f F fs Fs →
        tangentPointSet F = ∅ ∧ circleMeasure (sphere (0 : ℂ) 1 \ sect (fun z => (f z : ExtPlane))) = 0 ∧
        circleMeasure (sphere (0 : ℂ) 1 \
          {ζ ∈ sphere (0 : ℂ) 1 | conj ζ ∈ sect (fun z => fs (mobiusExt 0 1 1 0 z))}) = 0 := by
  sorry

/-- **Theorem 6.30** (§6.6; BiCaGaJo89; (6.6.9) cited "(9)" at l. 6526; cited at P2 l. 1318). There is a partition
(6.6.9) `J = T ∪ B ∪ B*` with `ω(B) = 0`, `ω*(B*) = 0`.
Modelling: [misprint] the crop prints `w*(B*) = 0` with an italic `w`; it is read `ω*(B*) = 0` (leader ruling), as in
the §6.1 form (6.1.3), l. 5435. The three pieces are pairwise disjoint ("partition"; the proof ends by replacing `B`
with `B ∖ (B ∩ B*)`, leader ruling, Q6.8(f)). -/
theorem thm6_30 {J : Set ℂ} {f F : ℂ → ℂ} {fs : ExtPlane → ExtPlane} {Fs : ℂ → ExtPlane}
    (hS : IsJordanSetting J f F fs Fs) :
    ∃ B Bs : Set ℂ, J = tangentPointSet F ∪ B ∪ Bs ∧ Disjoint (tangentPointSet F) B ∧
      Disjoint (tangentPointSet F) Bs ∧ Disjoint B Bs ∧ boundaryHarmonicMeasure F B = 0 ∧
      boundaryHarmonicMeasure Fs (toExt Bs) = 0 := by
  sorry

end Pommerenke1992
