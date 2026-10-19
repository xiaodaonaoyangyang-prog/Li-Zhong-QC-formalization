import References.Pommerenke1992.Ch02.S02_LocalConnection

/-!
# Pommerenke 1992, Ch. 2 §2.3 Cut Points and Jordan Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1163–1272.

* Definition (cut point of a locally connected continuum, §2.3) — `IsCutPoint`
* Proposition 2.5 — `prop2_5`
* Theorem 2.6 (Carathéodory) — `thm2_6`
* Corollary 2.7 — `cor2_7`
* Corollary 2.8 — `cor2_8`
* Corollary 2.9 (Schoenflies theorem) — `cor2_9`
* Corollary 2.10 — `cor2_10`
* Theorem 2.11 (Radó) — `thm2_11`

Not items (DESIGN §3): the examples of cut points (l. 1165); the forward references after Proposition 2.5; the
conformal welding `φ` of `𝕋` in the proof of Corollary 2.8 (a proof step; referred to at l. 6520 as "studied in
Section 2.3"); the univalence criterion stated as a special case of Corollary 2.10 (l. 1240, not cited).

**Standing assumption** (§2.2, l. 1004): the domains are bounded domains of `ℂ`; conformal maps of `𝔻` onto them are
`LiZhongQC.IsConformalOnto`. Jordan domains of `ℂ` are `LiZhongQC.IsJordanDomain`; the orientation of boundary points
is `LehtoVirtanen1973.IsPositivelyOrdered`, and homeomorphisms of `Ĉ` are `LehtoVirtanen1973.IsHomeoOn`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto IsJordanCurve IsJordanDomain)
open LehtoVirtanen1973 (IsPositivelyOrdered IsHomeoOn)

/-- **Definition** (§2.3). Let `E` be a locally connected continuum. The point `a ∈ E` is a cut point of `E` if
`E ∖ {a}` is no longer connected. -/
def IsCutPoint (E : Set ℂ) (a : ℂ) : Prop :=
  a ∈ E ∧ ¬ IsPreconnected (E \ {a})

/-- **Proposition 2.5** (§2.3). Let `f` map `𝔻` conformally onto the bounded domain `G` with locally connected
boundary. Let `a ∈ ∂G` and `A = f⁻¹({a}) = {ζ ∈ 𝕋 : f(ζ) = a}`, `m = card A ≤ ∞`. Then `a` is a cut point if and only
if `m > 1`, and the components of `∂G ∖ {a}` are the `f(I_k)`, where the `I_k` (`k = 1, …, m`) are the arcs that make
up `𝕋 ∖ A`.
Modelling: `f` on `𝕋` is its continuous extension `F` (Theorem 2.1); the arcs of `𝕋 ∖ A` are its components. The
correspondence `I_k ↦ f(I_k)` is one-to-one: the images of distinct arcs are disjoint. -/
theorem prop2_5 {G : Set ℂ} (hG : Bornology.IsBounded G) {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc G)
    (hlc : IsLocConn (frontier G)) {F : ℂ → ℂ} (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc)
    {a : ℂ} (ha : a ∈ frontier G) :
    (IsCutPoint (frontier G) a ↔ 1 < {ζ ∈ sphere (0 : ℂ) 1 | F ζ = a}.encard) ∧
      {K | ∃ x ∈ frontier G \ {a}, K = connectedComponentIn (frontier G \ {a}) x} =
        {K | ∃ ζ ∈ sphere (0 : ℂ) 1 \ {ζ | F ζ = a},
          K = F '' connectedComponentIn (sphere (0 : ℂ) 1 \ {ζ | F ζ = a}) ζ} ∧
      ∀ ζ₁ ∈ sphere (0 : ℂ) 1 \ {ζ | F ζ = a}, ∀ ζ₂ ∈ sphere (0 : ℂ) 1 \ {ζ | F ζ = a},
        connectedComponentIn (sphere (0 : ℂ) 1 \ {ζ | F ζ = a}) ζ₁ ≠
          connectedComponentIn (sphere (0 : ℂ) 1 \ {ζ | F ζ = a}) ζ₂ →
        Disjoint (F '' connectedComponentIn (sphere (0 : ℂ) 1 \ {ζ | F ζ = a}) ζ₁)
          (F '' connectedComponentIn (sphere (0 : ℂ) 1 \ {ζ | F ζ = a}) ζ₂) := by
  sorry

/-- **Theorem 2.6** (§2.3; Carathéodory's theorem). Let `f` map `𝔻` conformally onto the bounded domain `G`. Then the
following three conditions are equivalent: (i) `f` has a continuous injective extension to `𝔻̄`; (ii) `∂G` is a
Jordan curve; (iii) `∂G` is locally connected and has no cut points.
(The project's `LiZhongQC.caratheodory_jordan` and `LiZhongQC.isJordanCurve_frontier_of_isHomeoExtension` give (i)
⇔ (ii) only.) -/
theorem thm2_6 {G : Set ℂ} (hG : Bornology.IsBounded G) {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc G) :
    List.TFAE
      [∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ InjOn F (closedBall 0 1) ∧ EqOn F f unitDisc,
        IsJordanCurve (toExt (frontier G)),
        IsLocConn (frontier G) ∧ ∀ a ∈ frontier G, ¬ IsCutPoint (frontier G) a] := by
  sorry

/-- **Corollary 2.7** (§2.3). Let `G` and `H` be Jordan domains and let the points `z₁, z₂, z₃ ∈ ∂G` and
`w₁, w₂, w₃ ∈ ∂H` have the same cyclic order. Then there is a unique conformal map `h` of `G` onto `H` that satisfies
(2.3.2) `h(z_j) = w_j` for `j = 1, 2, 3`.
Modelling: bounded Jordan domains (standing assumption); `h` on `∂G` is its continuous extension; "the same cyclic
order" is: `(z_j)` is positively ordered on `∂G` if and only if `(w_j)` is positively ordered on `∂H`. -/
theorem cor2_7 {G H : Set ℂ} (hG : IsJordanDomain G) (hGb : Bornology.IsBounded G) (hH : IsJordanDomain H)
    (hHb : Bornology.IsBounded H) {z w : Fin 3 → ℂ} (hz : Function.Injective z) (hw : Function.Injective w)
    (hzG : ∀ j, z j ∈ frontier G) (hwH : ∀ j, w j ∈ frontier H)
    (hord : IsPositivelyOrdered (toExt G) (fun j => (z j : ExtPlane)) ↔
      IsPositivelyOrdered (toExt H) (fun j => (w j : ExtPlane))) :
    ∃ h : ℂ → ℂ, IsConformalOnto h G H ∧ ContinuousOn h (closure G) ∧ (∀ j, h (z j) = w j) ∧
      ∀ h' : ℂ → ℂ, IsConformalOnto h' G H → ContinuousOn h' (closure G) → (∀ j, h' (z j) = w j) →
        EqOn h' h G := by
  sorry

/-- **Corollary 2.8** (§2.3). A conformal map of `𝔻` onto a Jordan domain can be extended to a homeomorphism of `Ĉ`
onto `Ĉ`.
Modelling: a bounded Jordan domain (standing assumption; the proof takes `G` bounded). -/
theorem cor2_8 {G : Set ℂ} (hG : IsJordanDomain G) (hGb : Bornology.IsBounded G) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc G) :
    ∃ F : ExtPlane → ExtPlane, IsHomeoOn F univ univ ∧ ∀ z ∈ unitDisc, F z = f z := by
  sorry

/-- **Corollary 2.9** (§2.3; the Schoenflies theorem). A bijective continuous map of a Jordan curve onto another can
be extended to a homeomorphism of `ℂ` onto `ℂ`.
Modelling: the Jordan curves `J, J'` lie in `ℂ`. -/
theorem cor2_9 {J J' : Set ℂ} (hJ : IsJordanCurve (toExt J)) (hJ' : IsJordanCurve (toExt J')) {φ : ℂ → ℂ}
    (hφc : ContinuousOn φ J) (hφ : BijOn φ J J') : ∃ Φ : ℂ ≃ₜ ℂ, ∀ z ∈ J, Φ z = φ z := by
  sorry

/-- **Corollary 2.10** (§2.3). Let `G` be a bounded Jordan domain and let `f` be non-constant and analytic in `𝔻`. If
(2.3.5) `dist(f(z), ∂G) → 0` as `|z| → 1`, then `f(𝔻) = G` and `f` has a continuous extension to `𝔻̄`. There exists
`m = 1, 2, …` such that `f` assumes every value of `Ḡ` exactly `m` times in `𝔻̄`.
Modelling: the values are counted with multiplicity in `𝔻` (`analyticOrderAt` of `f - w`) and once on `𝕋` (there the
map is locally the finite Blaschke product of the proof); the count is summed in `ℝ≥0∞`. -/
theorem cor2_10 {G : Set ℂ} (hG : IsJordanDomain G) (hGb : Bornology.IsBounded G) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hnc : ∃ z₁ ∈ unitDisc, ∃ z₂ ∈ unitDisc, f z₁ ≠ f z₂)
    (hbd : ∀ ε > (0 : ℝ), ∃ r < (1 : ℝ), ∀ z ∈ unitDisc, r < ‖z‖ → infDist (f z) (frontier G) < ε) :
    f '' unitDisc = G ∧ ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∀ w ∈ closure G,
        (∑' z : ↥(unitDisc ∩ f ⁻¹' {w}), ENat.toENNReal (analyticOrderAt (fun ζ => f ζ - w) z)) +
          ENat.toENNReal (sphere (0 : ℂ) 1 ∩ F ⁻¹' {w}).encard = m := by
  sorry

/-- **Theorem 2.11** (§2.3; Radó). For `n = 1, 2, …` let `Jₙ : φₙ(ζ), ζ ∈ 𝕋` and `J : φ(ζ), ζ ∈ 𝕋` be Jordan curves
and let `fₙ` and `f` map `𝔻` conformally onto the inner domains of `Jₙ` and `J` such that `fₙ(0) = f(0)` and
`fₙ'(0) > 0`, `f'(0) > 0` for all `n`. If (2.3.7) `φₙ → φ` uniformly on `𝕋`, then (2.3.8) `fₙ → f` uniformly in `𝔻̄`.
Modelling: the Jordan curves are given by continuous maps injective on `𝕋`; `f'(0) > 0` is `Re > 0, Im = 0`; on `𝔻̄`
the maps are their continuous extensions (Theorem 2.6). -/
theorem thm2_11 {φ : ℕ → ℂ → ℂ} {φ₀ : ℂ → ℂ}
    (hφ : ∀ n, ContinuousOn (φ n) (sphere 0 1) ∧ InjOn (φ n) (sphere 0 1))
    (hφ₀ : ContinuousOn φ₀ (sphere 0 1) ∧ InjOn φ₀ (sphere 0 1)) {f : ℕ → ℂ → ℂ} {f₀ : ℂ → ℂ}
    (hf : ∀ n, IsConformalOnto (f n) unitDisc (innerDomain (φ n '' sphere 0 1)) ∧ f n 0 = f₀ 0 ∧
      0 < (deriv (f n) 0).re ∧ (deriv (f n) 0).im = 0)
    (hf₀ : IsConformalOnto f₀ unitDisc (innerDomain (φ₀ '' sphere 0 1)) ∧ 0 < (deriv f₀ 0).re ∧
      (deriv f₀ 0).im = 0)
    (hconv : TendstoUniformlyOn φ φ₀ atTop (sphere 0 1)) :
    ∃ F : ℕ → ℂ → ℂ, ∃ F₀ : ℂ → ℂ, (∀ n, ContinuousOn (F n) (closedBall 0 1) ∧ EqOn (F n) (f n) unitDisc) ∧
      ContinuousOn F₀ (closedBall 0 1) ∧ EqOn F₀ f₀ unitDisc ∧ TendstoUniformlyOn F F₀ atTop (closedBall 0 1) := by
  sorry

end Pommerenke1992
