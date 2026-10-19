import References.LehtoVirtanen1973.Ch04.S02_AnalyticDefinition
import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain

/-!
# Lehto–Virtanen, Chapter IV §3: Variants of the geometric definition

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. IV §3
(pp. 170–177; `full.md` P1:5281–5538).

Conventions as in §1–§2. The module of a family of arcs or curves is that of III.4 (`arcFamilyModule`, on families of
point sets of `ℂ̄`; only the locally rectifiable members count and the admissible functions are Borel, footnote 42),
with values in `[0, ∞]`; the image family of `𝒞` under `w` is the family of the images `w(C)`, `C ∈ 𝒞`. A family of
arcs "in `G`" consists of Jordan arcs of `ℂ̄` contained in `G`. The module of the image `w(R)` of a quadrilateral `R`
is the module `quadModule (w '' R.dom) (w ∘ R.vert)` of the image domain with the image vertices, which is the book's
module since every mapping considered here is sense-preserving. Inequalities between modules are multiplied out.

* Theorem 3.1 (§3.2) — `thm4_3_1`
* Theorem 3.2 (§3.3, general module condition, Väisälä) — `thm4_3_2`
* Unlabelled (§3.4, P1:5397–5403): the module of the family of the arcs joining the a-sides of a quadrilateral `Q`
  inside `Q` is `M(Q)` — `module_quad_joining_arcs`
* Unlabelled (§3.4, P1:5405–5411): for a ring domain `B`, the family of the Jordan curves separating the components
  of the complement has the module `M(B)/2π`, and the family of the arcs joining them has the module `2π/M(B)` —
  `module_ring_separating_curves`, `module_ring_joining_arcs`
* Definition (module condition, §3.1–3.6) — omitted: terminology; the inequality between modules is written out in
  every statement
* Theorem 3.3 (§3.5) — `thm4_3_3`
* Theorem 3.4 (§3.6, Gehring–Väisälä) — `thm4_3_4_i`, `thm4_3_4_ii`
* Renggli's theorem (§3.7, P1:5537, quoted; the index's "characterization … 177") — `renggli_theorem`

Not stated (inventory: omitted): the remark that Theorem 3.1 contains Lemma 1.1, and the open question after it
(P1:5293–5295); formula (3.8) (P1:5381–5385), a step of the proof of Theorem 3.2 (its consequence cited in Chapter V
is stated there, V (6.6)); the conformal invariance of the module of a family of arcs (P1:5395, the case `K = 1` of
Theorem 3.2, conformal mappings being `1`-quasiconformal; used only within 3.4); the sharpening of Theorem 3.3 to
horizontal rectangles and squares (P1:5431, not cited later); the examples, open questions and the restatement of
Theorem I.7.2 in 3.7 (P1:5531–5535). The numbered formulas (3.2)–(3.7) and (3.9)–(3.13) are steps of proofs; (3.1)
is the conclusion of Theorem 3.2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve)
open References (IsDomainExt finitePart)

/-! ## §3.2 Absolute continuity on arcs -/

/-- **Theorem 3.1** (Ch. IV §3.2). A quasiconformal mapping `w : G → G′` is absolutely continuous on all closed arcs
`C ⊂ G` with the exception of a family of module zero.
Modelling: the family of the closed Jordan arcs `C ⊂ G` on which `w` is not absolutely continuous (as a function of
the arc length, III.2.10: `IsAbsContOnArc` of `finiteMap w` on the arc, which then lies in the finite plane) has
module zero; by the monotonicity of the module (III.4.2) this is the existence of an exceptional family of module
zero. The arcs through `∞` or through `w⁻¹(∞)` are put in the exceptional family, as in the book's proof (the arcs
through a fixed point form a family of module zero, III.4.3); the non-rectifiable arcs belong to it and do not affect
the module (III.4.1). -/
theorem thm4_3_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    arcFamilyModule {C : Set ExtPlane | IsClosedJordanArc C ∧ C ⊆ G ∧
      ¬ (extInf ∉ C ∧ extInf ∉ w '' C ∧ IsAbsContOnArc (finiteMap w) (finitePart C))} = 0 := by
  sorry

/-! ## §3.3 General module condition -/

/-- **Theorem 3.2** (Ch. IV §3.3, general module condition, Väisälä). Let `w : G → G′` be a `K`-quasiconformal
mapping, `𝒞` a family of arcs `C ⊂ G` and `𝒞′` the image family of `𝒞` under `w`. Then
`M(𝒞)/K ≤ M(𝒞′) ≤ K M(𝒞)` (3.1).
Modelling: the arcs are Jordan arcs of `ℂ̄` (open, closed or half-open); the inequalities are multiplied out in
`[0, ∞]` (`M = ∞` is allowed). -/
theorem thm4_3_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    {𝒞 : Set (Set ExtPlane)} (h𝒞 : ∀ C ∈ 𝒞, IsJordanArc C ∧ C ⊆ G) :
    arcFamilyModule 𝒞 ≤ ENNReal.ofReal K * arcFamilyModule ((fun C => w '' C) '' 𝒞) ∧
      arcFamilyModule ((fun C => w '' C) '' 𝒞) ≤ ENNReal.ofReal K * arcFamilyModule 𝒞 := by
  sorry

/-! ## §3.4 Conformal invariance of the module -/

/-- **Unlabelled** (Ch. IV §3.4, P1:5397–5403; cited P2:867, 1140, "IV.3.4"). If `Q` is a quadrilateral and `𝒞` denotes
the family of all Jordan arcs which join the a-sides of `Q` inside `Q`, then `M(𝒞) = M(Q)`.
Modelling: the members of `𝒞` are the closed Jordan arcs with one endpoint on each a-side (`Q.side 0`, `Q.side 2`)
and all their other points in `Q`; as in III.4, only the locally rectifiable members count (footnote 42). -/
theorem module_quad_joining_arcs (Q : Quadrilateral) :
    arcFamilyModule {C : Set ExtPlane | ∃ p ∈ Q.side 0, ∃ q ∈ Q.side 2, IsArcFromTo C p q ∧ C \ {p, q} ⊆ Q.dom} =
      ENNReal.ofReal Q.module := by
  sorry

/-- **Unlabelled** (Ch. IV §3.4, P1:5405–5411; cited P2:881, "IV.3.4"). For a ring domain `B`, the family `𝒞′` of the
Jordan curves separating the components of the complement of `B` has the module `M(𝒞′) = M(B)/2π`.
Modelling: the curves of `𝒞′` lie in `B` (a curve separating the two components of `-B` meets neither of them), and
separate every pair of points taken from different components of `-B`; the division is in `[0, ∞]`, so that
`M(𝒞′) = ∞` when `M(B) = ∞`. -/
theorem module_ring_separating_curves {B : Set ExtPlane} (hB : IsRingDomain B) :
    arcFamilyModule {C : Set ExtPlane | IsJordanCurve C ∧ C ⊆ B ∧ ∀ x ∈ Bᶜ, ∀ y ∈ Bᶜ,
      connectedComponentIn Bᶜ x ≠ connectedComponentIn Bᶜ y →
        Separates C (connectedComponentIn Bᶜ x) (connectedComponentIn Bᶜ y)} =
      ringModule B / ENNReal.ofReal (2 * Real.pi) := by
  sorry

/-- **Unlabelled** (Ch. IV §3.4, P1:5405–5411; cited P2:899, "IV.3.4"). For a ring domain `B`, the family `𝒞″` of the
arcs which join the components of the complement of `B` has the module `M(𝒞″) = 2π/M(B)`.
Modelling: the members of `𝒞″` are the closed Jordan arcs with one endpoint in each component of `-B` and all their
other points in `B`. The division is in `[0, ∞]`: `M(B) > 0` for a ring domain, and `2π/∞ = 0` is the degenerate case
of a component consisting of one point (the arcs ending at a fixed point form a family of module zero). The closed
arcs lose nothing against LV's arcs joining the components in the limit sense of I.6.2: for almost every angle the
preimage of a radius under the canonical map is rectifiable and lands at both ends (Fatou, Beurling), so it is an
arc of the family, which gives `≥ 2π/M(B)`; the family is contained in LV's, which gives `≤`. -/
theorem module_ring_joining_arcs {B : Set ExtPlane} (hB : IsRingDomain B) :
    arcFamilyModule {C : Set ExtPlane | ∃ p ∈ Bᶜ, ∃ q ∈ Bᶜ, connectedComponentIn Bᶜ p ≠ connectedComponentIn Bᶜ q ∧
      IsArcFromTo C p q ∧ C \ {p, q} ⊆ B} = ENNReal.ofReal (2 * Real.pi) / ringModule B := by
  sorry

/-! ## §3.5 Characterization of quasiconformality by means of rectangles -/

/-- **Theorem 3.3** (Ch. IV §3.5). If a sense-preserving homeomorphism `w : G → G′` satisfies the module condition
`M(w(R)) ≤ K M(R)` for every rectangle `R`, `R̄ ⊂ G`, then `w` is a `K`-quasiconformal mapping of `G`.
Modelling: a rectangle is a quadrilateral whose domain is a Euclidean rectangle in any position and whose vertices
are its corners, in any of the admissible labellings (`Quadrilateral.IsRectangle`, Ch. I §2.4; the proof uses the
horizontal rectangles in both labellings, footnote 43, and the squares). `1 ≤ K` is the book's standing `K ≥ 1`: for
`K < 1` the hypothesis is unsatisfiable (apply it to one rectangle in two labellings whose modules are reciprocal). -/
theorem thm4_3_3 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (hK : 1 ≤ K)
    (hR : ∀ R : Quadrilateral, R.IsRectangle → closure R.dom ⊆ G →
      quadModule (w '' R.dom) (w ∘ R.vert) ≤ K * R.module) :
    IsKQuasiconformal w G K := by
  sorry

/-! ## §3.6 Module condition for horizontal rectangles -/

/-- **Theorem 3.4** (Ch. IV §3.6, Gehring–Väisälä). A sense-preserving homeomorphism `w : G → G′` satisfying the module
condition `M(R)/K ≤ M(w(R)) ≤ K M(R)` for all horizontal rectangles `R`, `R̄ ⊂ G`, is `(K + √(K² − 1))`-quasiconformal.
Modelling: `1 ≤ K` is the book's standing `K ≥ 1`, which also keeps `√(K² − 1)` real; for `K < 1` the hypothesis is
unsatisfiable. -/
theorem thm4_3_4_i {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (hK : 1 ≤ K)
    (hR : ∀ R : Quadrilateral, R.IsHorizontalRectangle → closure R.dom ⊆ G →
      R.module ≤ K * quadModule (w '' R.dom) (w ∘ R.vert) ∧ quadModule (w '' R.dom) (w ∘ R.vert) ≤ K * R.module) :
    IsKQuasiconformal w G (K + Real.sqrt (K ^ 2 - 1)) := by
  sorry

/-- **Theorem 3.4**, the bound (Ch. IV §3.6). The bound `K + √(K² − 1)` is best possible, as the mapping
`w(z) = z + i √((K − 1)/(K + 1)) z̄` shows: it satisfies the module condition `M(R)/K ≤ M(w(R)) ≤ K M(R)` for all
horizontal rectangles `R`, and its maximal dilatation is `K + √(K² − 1)`.
Modelling: the book names no domain; the mapping is taken as a homeomorphism of the finite plane (`toExt univ`),
extended by `∞ ↦ ∞`. `1 ≤ K` as in `thm4_3_4_i`; it also makes `(K − 1)/(K + 1)` non-negative. -/
theorem thm4_3_4_ii {K : ℝ} (hK : 1 ≤ K) (w₀ : ExtPlane → ExtPlane)
    (hw₀ : w₀ = OnePoint.map fun z : ℂ => z + I * (Real.sqrt ((K - 1) / (K + 1)) : ℂ) * conj z) :
    IsSensePreservingOn w₀ (toExt univ) ∧
      (∀ R : Quadrilateral, R.IsHorizontalRectangle → closure R.dom ⊆ toExt univ →
        R.module ≤ K * quadModule (w₀ '' R.dom) (w₀ ∘ R.vert) ∧
          quadModule (w₀ '' R.dom) (w₀ ∘ R.vert) ≤ K * R.module) ∧
      maxDilatationK w₀ (toExt univ) = ENNReal.ofReal (K + Real.sqrt (K ^ 2 - 1)) := by
  sorry

/-! ## §3.7 Other characterizations -/

/-- **Renggli's theorem** (Ch. IV §3.7, P1:5537, quoted from Renggli [1]). A sense-preserving homeomorphism `w` of
the domain `G` is quasiconformal if it carries every family of arcs and curves with module `∞` into a family with
module `∞`.
Modelling: the families are point-set families of Jordan arcs and curves contained in `G`, with the module of
III.4 (`arcFamilyModule`); the image family is `{w(C) | C ∈ 𝒞}`; "sense-preserving homeomorphism" is
`IsSensePreservingOn w G` as in `thm4_3_3`. -/
theorem renggli_theorem {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G)
    (hmod : ∀ 𝒞 : Set (Set ExtPlane), (∀ C ∈ 𝒞, (IsJordanArc C ∨ IsJordanCurve C) ∧ C ⊆ G) →
      arcFamilyModule 𝒞 = ⊤ → arcFamilyModule ((fun C => w '' C) '' 𝒞) = ⊤) :
    IsQuasiconformalMap w G := by
  sorry

end LehtoVirtanen1973
