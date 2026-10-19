import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC
import LiZhongQC.Ch01.S03_ExtremalLength

/-!
# Lehto–Virtanen, Chapter I §4: Conformal module and extremal length

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §4
(pp. 19–28; `full.md` P1:469–730).

The book leaves the classes of arcs `𝒞_a` and of densities `P` "deliberately indefinite" (P1:499) and makes them
precise in III.4 (footnote 7): locally rectifiable arcs and Borel densities; only densities for which numerator and
denominator of (4.6) are not simultaneously `0` or `∞` are admitted (footnote 8). This is modelled with the project's
locally rectifiable curves `LiZhongQC.LRCurve` in the finite part of `Q` and the class `LiZhongQC.densitiesP0`
(`0 < m_ρ < ∞`). Arcs through `∞` are not in the families; this changes nothing, since the arcs through a fixed
point form a family of module zero (cf. III.4, P1:5291). Using all locally rectifiable curves instead of Jordan arcs
changes no infimum (every such curve contains a Jordan arc of no greater `ρ`-length). The book states (4.6),
Rengel's inequality and (4.7) "for every admissible family `𝒞_a`"; the formalization fixes the maximal family.

* Definition (`l_ρ(C)`, `m_ρ(Q)` (4.5), §4.2) — exists: `LiZhongQC.LRCurve.rhoLength`, `LiZhongQC.rhoArea`
* Definition (euclidean length `l(C)`, §4.3) — exists: `LiZhongQC.LRCurve.length`
* Definition (the finite part `Q ∩ ℂ` of `Q`, over which the areas are taken, §4.1) — exists: `References.finitePart`
* Definition (the admissible densities `P`, §4.2, footnotes 7–8) — exists: `LiZhongQC.densitiesP0`
* Definition (the family `𝒞_a` of arcs joining the a-sides, §4.1; distances `s_a`, `s_b` between the sides and the
  area `m(Q)`, §4.3) — `Quadrilateral.IsJoiningCurve`, `Quadrilateral.aCurves`,
  `Quadrilateral.bCurves`, `Quadrilateral.aDist`, `Quadrilateral.bDist`, `Quadrilateral.area`, `derivDensity`
* Theorem 4.1 (§4.2) — `thm1_4_1`
* Definition (extremal length of `𝒞_a`, §4.2) — exists: `LiZhongQC.extremalLength` (densities on the finite plane
  with areas over the whole plane; for the a-curves this equals the version with areas over the finite part of Q,
  by extremalLengthIn_eq)
* Rengel's inequality (§4.3) — `rengel_inequality`, `rengel_eq_left_iff`, `rengel_eq_right_iff`
* Lemma 4.1 (§4.4) — `lemma1_4_1`
* Unlabelled (§4.5, P1:640–646): the module of degenerating quadrilaterals tends to `0` — `module_tendsto_zero`
* Definition (degenerate quadrilateral; (4.12), §4.5) — omitted: used only in remarks and inside the proof of
  Theorem 8.3; no statement quantifies over degenerate quadrilaterals
* Lemma 4.2 (§4.6) — `lemma1_4_2_i`, `lemma1_4_2_ii`
* Definition (convergence from inside, §4.7) — `QuadConvergesFromInside`
* Lemma 4.3 (§4.7) — `lemma1_4_3`
* Definition (analytic curve, closed and open analytic arcs (footnote 6); analytic quadrilateral, §4.8) —
  `IsAnalyticCurve`, `IsAnalyticClosedArcFromTo`, `IsAnalyticClosedArc`, `IsAnalyticOpenArc`,
  `Quadrilateral.IsAnalytic`
* Lemma 4.4 (§4.8) — `lemma1_4_4`
* Definition (convergence of quadrilaterals, §4.9) — `QuadConvergesTo`
* Theorem on the convergence of the module (§4.9) — `module_convergence`
* Definition (convergence of Jordan curves in the sense of Fréchet, §4.9) — `FrechetConverges`
* Radó's convergence theorem (§4.9, quoted from Golusin) — `rado_convergence`

The derivation (4.1)–(4.4) (P1:477–512) consists of proof steps and is not stated; neither are the remarks P1:597
and P1:607 (U−: no inference from an upper bound for `s_a`; the arc `C₀` of length `s_b`, a proof step).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius LRCurve)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §4.1–4.3 The curve families and the module -/

/-- A locally rectifiable curve in the finite part of `Q` joining the side `i` to the opposite side `i + 2`
(`i = 0`: the a-sides, `i = 1`: the b-sides; Ch. I §4.1). -/
def Quadrilateral.IsJoiningCurve (Q : Quadrilateral) (i : Fin 4) (γ : LRCurve) : Prop :=
  γ.trace ⊆ finitePart Q.dom ∧
    (∃ p ∈ Q.side i, Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) (𝓝[>] 0) (𝓝 p)) ∧
      ∃ q ∈ Q.side (i + 2), Tendsto (fun t => ((γ.toFun t : ℂ) : ExtPlane)) (𝓝[<] 1) (𝓝 q)

/-- **Definition** (the family `𝒞_a`, Ch. I §4.1): the curves in `Q` joining the a-sides. -/
def Quadrilateral.aCurves (Q : Quadrilateral) : Set LRCurve := {γ | Q.IsJoiningCurve 0 γ}

/-- The curves in `Q` joining the b-sides. -/
def Quadrilateral.bCurves (Q : Quadrilateral) : Set LRCurve := {γ | Q.IsJoiningCurve 1 γ}

/-- **Definition** (Ch. I §4.3). `s_a(Q)`, the distance between the a-sides: the infimum of the euclidean lengths of
the curves in `Q` joining the a-sides. For every quadrilateral `0 < s_a < ∞` (the a-sides are disjoint closed arcs,
at most one containing `∞`, and polygonal joining arcs exist). -/
def Quadrilateral.aDist (Q : Quadrilateral) : ℝ≥0∞ := ⨅ γ ∈ Q.aCurves, γ.length

/-- **Definition** (Ch. I §4.3). `s_b(Q)`, the distance between the b-sides. -/
def Quadrilateral.bDist (Q : Quadrilateral) : ℝ≥0∞ := ⨅ γ ∈ Q.bCurves, γ.length

/-- **Definition** (Ch. I §4.3). The euclidean area `m(Q)` of the finite part of `Q`: `= ∞` when `∞ ∈ Q`; possibly
finite when `∞ ∈ Fr Q` (e.g. a cusp `{x > 1, |y| < x⁻²}`). -/
def Quadrilateral.area (Q : Quadrilateral) : ℝ≥0∞ := volume (finitePart Q.dom)

/-- The density `|f′|` on the finite part `D` of the domain of a conformal mapping `f` with finite values
(`0` outside `D`). -/
def derivDensity (f : ExtPlane → ExtPlane) (D : Set ℂ) : ℂ → ℝ≥0∞ :=
  D.indicator fun z => ENNReal.ofReal ‖deriv (finiteMap f) z‖

/-- **Theorem 4.1** (Ch. I §4.2, Ahlfors–Beurling). The module of a quadrilateral admits the representation
`M(Q) = inf_{ρ ∈ P} m_ρ(Q) / (inf_{C ∈ 𝒞_a} l_ρ(C))²` (4.6); the infimum is attained for `ρ = |f′|`, where `f` is a
canonical mapping of `Q`.
Modelling: `P` = Borel densities with `0 < m_ρ(Q) < ∞` (footnotes 7, 8); `𝒞_a` = `Q.aCurves`. -/
theorem thm1_4_1 (Q : Quadrilateral) :
    ENNReal.ofReal Q.module = ⨅ ρ ∈ LiZhongQC.densitiesP0 (finitePart Q.dom),
      LiZhongQC.rhoArea ρ (finitePart Q.dom) / (⨅ γ ∈ Q.aCurves, γ.rhoLength ρ) ^ 2 ∧
    ∀ (a b : ℝ) (f : ExtPlane → ExtPlane), IsCanonicalMap Q.dom Q.vert a b f →
      derivDensity f (finitePart Q.dom) ∈ LiZhongQC.densitiesP0 (finitePart Q.dom) ∧
      ENNReal.ofReal Q.module = LiZhongQC.rhoArea (derivDensity f (finitePart Q.dom)) (finitePart Q.dom) /
        (⨅ γ ∈ Q.aCurves, γ.rhoLength (derivDensity f (finitePart Q.dom))) ^ 2 := by
  sorry

/-- **Rengel's inequality** (Ch. I §4.3). The module of a quadrilateral `Q` satisfies
`(s_b(Q))² / m(Q) ≤ M(Q) ≤ m(Q) / (s_a(Q))²`.
Modelling: in `ℝ≥0∞`; since `0 < s_a, s_b < ∞`, no `⊤/⊤` occurs, also when `m(Q) = ∞`. -/
theorem rengel_inequality (Q : Quadrilateral) :
    Q.bDist ^ 2 / Q.area ≤ ENNReal.ofReal Q.module ∧ ENNReal.ofReal Q.module ≤ Q.area / Q.aDist ^ 2 := by
  sorry

/-- **Rengel's inequality**, equality case on the left (Ch. I §4.3): equality holds if and only if `Q` is a
rectangle. -/
theorem rengel_eq_left_iff (Q : Quadrilateral) :
    Q.bDist ^ 2 / Q.area = ENNReal.ofReal Q.module ↔ Q.IsRectangle := by
  sorry

/-- **Rengel's inequality**, equality case on the right (Ch. I §4.3): equality holds if and only if `Q` is a
rectangle. -/
theorem rengel_eq_right_iff (Q : Quadrilateral) :
    ENNReal.ofReal Q.module = Q.area / Q.aDist ^ 2 ↔ Q.IsRectangle := by
  sorry

/-! ## §4.4–4.6 Estimates, degenerate quadrilaterals, superadditivity -/

/-- **Lemma 4.1** (Ch. I §4.4). The module of a quadrilateral `Q` satisfies
`M(Q) ≤ π (1 + 2 log(1 + 2 s_a/s_b)) / (log(1 + 2 s_a/s_b))²` (4.7).
Modelling: `s_a/s_b` is a positive real number since `0 < s_a, s_b < ∞`. -/
theorem lemma1_4_1 (Q : Quadrilateral) :
    Q.module ≤ Real.pi * (1 + 2 * Real.log (1 + 2 * (Q.aDist / Q.bDist).toReal)) /
      Real.log (1 + 2 * (Q.aDist / Q.bDist).toReal) ^ 2 := by
  sorry

/-- **Unlabelled** (Ch. I §4.5, P1:640–646). If `s_b(Qₙ) → 0` and `liminf s_a(Qₙ) > 0` (4.11), then `M(Qₙ) → 0`. -/
theorem module_tendsto_zero {Qn : ℕ → Quadrilateral} (hb : Tendsto (fun n => (Qn n).bDist) atTop (𝓝 0))
    (ha : 0 < liminf (fun n => (Qn n).aDist) atTop) : Tendsto (fun n => (Qn n).module) atTop (𝓝 0) := by
  sorry

/-- **Lemma 4.2** (Ch. I §4.6), superadditivity. Let `Qₙ` be quadrilaterals without common interior points and with
closures contained in the closure of a quadrilateral `Q`. If the a-sides of every `Qₙ` are contained one in each
a-side of `Q`, then `∑ₙ M(Qₙ) ≤ M(Q)` (4.13).
Modelling: the family is indexed by any type `ι`; a disjoint family of nonempty open subsets of `ℂ̄` is
countable, so this is the book's `n = 1, 2, …` (finite families included). -/
theorem lemma1_4_2_i {ι : Type*} (Q : Quadrilateral) (Qn : ι → Quadrilateral)
    (hdisj : Pairwise fun m n => Disjoint (Qn m).dom (Qn n).dom) (hcl : ∀ n, closure (Qn n).dom ⊆ closure Q.dom)
    (hsides : ∀ n, ((Qn n).side 0 ⊆ Q.side 0 ∧ (Qn n).side 2 ⊆ Q.side 2) ∨
      ((Qn n).side 0 ⊆ Q.side 2 ∧ (Qn n).side 2 ⊆ Q.side 0)) :
    ∑' n, ENNReal.ofReal (Qn n).module ≤ ENNReal.ofReal Q.module := by
  sorry

/-- **Lemma 4.2** (Ch. I §4.6), equality case. Under the hypotheses of `lemma1_4_2_i`, if `Q` is a rectangle, then
equality holds in (4.13) if and only if all `Qₙ` are rectangles and `∑ m(Qₙ) = m(Q)`.
Modelling: the family is indexed by any type `ι`; a disjoint family of nonempty open subsets of `ℂ̄` is
countable, so this is the book's `n = 1, 2, …` (finite families included). -/
theorem lemma1_4_2_ii {ι : Type*} (Q : Quadrilateral) (Qn : ι → Quadrilateral)
    (hdisj : Pairwise fun m n => Disjoint (Qn m).dom (Qn n).dom) (hcl : ∀ n, closure (Qn n).dom ⊆ closure Q.dom)
    (hsides : ∀ n, ((Qn n).side 0 ⊆ Q.side 0 ∧ (Qn n).side 2 ⊆ Q.side 2) ∨
      ((Qn n).side 0 ⊆ Q.side 2 ∧ (Qn n).side 2 ⊆ Q.side 0)) (hQ : Q.IsRectangle) :
    ∑' n, ENNReal.ofReal (Qn n).module = ENNReal.ofReal Q.module ↔
      (∀ n, (Qn n).IsRectangle) ∧ ∑' n, (Qn n).area = Q.area := by
  sorry

/-! ## §4.7–4.8 Continuity of the module; approximation from inside -/

/-- **Definition** (convergence from inside, Ch. I §4.7). `Q̄ₙ ⊂ Q̄` for every `n`, and for every `ε > 0` there is an
`n_ε` such that for `n ≥ n_ε` every point of every side of `Qₙ` has a spherical distance `< ε` from the corresponding
side of `Q`. -/
def QuadConvergesFromInside (Qn : ℕ → Quadrilateral) (Q : Quadrilateral) : Prop :=
  (∀ n, closure (Qn n).dom ⊆ closure Q.dom) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin 4, ∀ z ∈ (Qn n).side i, ∃ z' ∈ Q.side i, sphericalDist z z' < ε

/-- **Lemma 4.3** (Ch. I §4.7). If the sequence `Qₙ` of quadrilaterals converges to the quadrilateral `Q` from
inside, then `lim M(Qₙ) = M(Q)` (4.14). -/
theorem lemma1_4_3 {Qn : ℕ → Quadrilateral} {Q : Quadrilateral} (h : QuadConvergesFromInside Qn Q) :
    Tendsto (fun n => (Qn n).module) atTop (𝓝 Q.module) := by
  sorry

/-- **Definition** (analytic curve, Ch. I §4.1, footnote 6): the image of a circle under a conformal mapping of a
neighbourhood of this circle. -/
def IsAnalyticCurve (C : Set ExtPlane) : Prop :=
  ∃ (c : ℂ) (r : ℝ) (U : Set ExtPlane) (f : ExtPlane → ExtPlane), 0 < r ∧ toExt (Metric.sphere c r) ⊆ U ∧
    IsConformalMap f U ∧ C = f '' toExt (Metric.sphere c r)

/-- **Definition** (closed analytic arc, footnote 6): the image of a closed segment `I` under a conformal mapping of
a neighbourhood of `I`; here with endpoints `p`, `q`. -/
def IsAnalyticClosedArcFromTo (C : Set ExtPlane) (p q : ExtPlane) : Prop :=
  ∃ (a b : ℂ) (U : Set ExtPlane) (f : ExtPlane → ExtPlane), a ≠ b ∧ toExt (segment ℝ a b) ⊆ U ∧
    IsConformalMap f U ∧ C = f '' toExt (segment ℝ a b) ∧ f a = p ∧ f b = q

/-- **Definition** (closed analytic arc, footnote 6). -/
def IsAnalyticClosedArc (C : Set ExtPlane) : Prop := ∃ p q, IsAnalyticClosedArcFromTo C p q

/-- **Definition** (open analytic arc, footnote 6): an open arc all of whose closed subarcs are analytic. -/
def IsAnalyticOpenArc (C : Set ExtPlane) : Prop :=
  IsOpenJordanArc C ∧ ∀ C' ⊆ C, IsClosedJordanArc C' → IsAnalyticClosedArc C'

/-- **Definition** (analytic quadrilateral, Ch. I §4.8): a quadrilateral whose boundary is an analytic curve. -/
def Quadrilateral.IsAnalytic (Q : Quadrilateral) : Prop := IsAnalyticCurve (frontier Q.dom)

/-- **Lemma 4.4** (Ch. I §4.8). Every quadrilateral `Q` is the limit of a sequence of analytic quadrilaterals having
closures in `Q` and converging to `Q` from inside. -/
theorem lemma1_4_4 (Q : Quadrilateral) :
    ∃ Qn : ℕ → Quadrilateral, (∀ n, (Qn n).IsAnalytic ∧ closure (Qn n).dom ⊆ Q.dom) ∧
      QuadConvergesFromInside Qn Q := by
  sorry

/-! ## §4.9 Generalized continuity theorem -/

/-- **Definition** (convergence of quadrilaterals, Ch. I §4.9). For every `ε > 0`, for `n` large every point of every
side of `Qₙ` and every interior point of `Qₙ` has a spherical distance at most `ε` from the corresponding side of `Q`,
resp. from `Q`.
Modelling: "distance at most `ε` from a set" is written `∃ z′ ∈ set, k(z, z′) ≤ ε`; the two readings agree since
`ε` is arbitrary. -/
def QuadConvergesTo (Qn : ℕ → Quadrilateral) (Q : Quadrilateral) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, (∀ i : Fin 4, ∀ z ∈ (Qn n).side i, ∃ z' ∈ Q.side i, sphericalDist z z' ≤ ε) ∧
    ∀ z ∈ (Qn n).dom, ∃ z' ∈ Q.dom, sphericalDist z z' ≤ ε

/-- **Theorem on the convergence of the module** (Ch. I §4.9). If the sequence of quadrilaterals `Qₙ` converges to a
quadrilateral `Q`, then `lim M(Qₙ) = M(Q)`. -/
theorem module_convergence {Qn : ℕ → Quadrilateral} {Q : Quadrilateral} (h : QuadConvergesTo Qn Q) :
    Tendsto (fun n => (Qn n).module) atTop (𝓝 Q.module) := by
  sorry

/-- **Definition** (convergence in the sense of Fréchet, Ch. I §4.9). For every `ε > 0`, for `n` large there is a
homeomorphism of `Cₙ` onto `C` moving every point by a spherical distance less than `ε`. -/
def FrechetConverges (Cn : ℕ → Set ExtPlane) (C : Set ExtPlane) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∃ h : ExtPlane → ExtPlane, IsHomeoOn h (Cn n) C ∧ ∀ z ∈ Cn n, sphericalDist z (h z) < ε

/-- **Radó's convergence theorem** (Ch. I §4.9, quoted from Golusin). Let `G₁ ⊃ G₂ ⊃ ⋯ ⊃ Q̄` be Jordan domains
whose boundaries converge to that of the Jordan domain `Q` in the sense of Fréchet, and let `fₙ`, `f` be conformal
mappings of a Jordan domain `R` onto `Gₙ` and `Q` (extended to the closures), normalized at a point `z₀ ∈ R` by
`fₙ(z₀) = f(z₀)`, `arg fₙ′(z₀) = arg f′(z₀)`. Then `fₙ → f` uniformly in `R̄`.
Modelling: `z₀` and `f(z₀)` are finite (the normalization uses the derivative); uniform convergence is spherical. -/
theorem rado_convergence {Gn : ℕ → Set ExtPlane} {Q R : Set ExtPlane} (hGn : ∀ n, IsJordanDomainExt (Gn n))
    (hQ : IsJordanDomainExt Q) (hR : IsJordanDomainExt R) (hmono : ∀ n, Gn (n + 1) ⊆ Gn n)
    (hQG : ∀ n, closure Q ⊆ Gn n) (hF : FrechetConverges (fun n => frontier (Gn n)) (frontier Q))
    {fn : ℕ → ExtPlane → ExtPlane} {f : ExtPlane → ExtPlane}
    (hfn : ∀ n, IsConformalMap (fn n) R ∧ fn n '' R = Gn n ∧ IsHomeoOn (fn n) (closure R) (closure (Gn n)))
    (hf : IsConformalMap f R ∧ f '' R = Q ∧ IsHomeoOn f (closure R) (closure Q))
    {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ R) (hfin : f z₀ ≠ extInf)
    (hnorm : ∀ n, fn n z₀ = f z₀ ∧ arg (deriv (finiteMap (fn n)) z₀) = arg (deriv (finiteMap f) z₀)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ closure R, sphericalDist (fn n z) (f z) < ε := by
  sorry

end LehtoVirtanen1973
