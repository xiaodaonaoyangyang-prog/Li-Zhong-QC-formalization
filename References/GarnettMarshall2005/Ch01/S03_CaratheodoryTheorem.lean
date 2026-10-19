import References.GarnettMarshall2005.Ch01.S02_FatouMaximalFunctions
import References.LehtoVirtanen1973.Ch01.S02_ConformalMappings
import References.Common.ExtPlaneBorel

/-!
# Garnett–Marshall, Chapter I §3: Carathéodory's theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. I §3 (pp. 13–16;
`full.md` P1:727–853).

Conventions as in §1–§2. Jordan domains are domains of the extended plane `ℂ*` (they may contain `∞`), and
closures and boundaries are taken in `ℂ*`. A conformal mapping of `𝔻` onto a domain of `ℂ*` is
`LehtoVirtanen1973.IsConformalMap φ (toExt 𝔻)` with `φ '' toExt 𝔻 = Ω`, `φ : ℂ* → ℂ*` read at the points of `𝔻`
through the coercion `ℂ → ℂ*`; its continuous extension to `𝔻̄` (Theorem 3.1) is a map `Φ` with `Φ = φ` on `𝔻`,
continuous on `𝔻̄`. Borel sets, Borel functions and Borel measures on `ℂ*` use the Borel σ-algebra of `ℂ*` of the
shared layer (`open scoped References`). The harmonic measure `ω(z, ·, Ω)` of a Jordan domain is a measure on `ℂ*`.

* Definition (Jordan curve in `ℂ*`, §3) — exists: `LiZhongQC.IsJordanCurve` (a homeomorphic image of the circle in
  ℂ*)
* Definition (Jordan domain: a simply connected domain of `ℂ*` whose boundary is a Jordan curve in `ℂ*`, §3) —
  exists: `References.IsJordanDomainExt` (a domain of ℂ* whose frontier is a Jordan curve; simple connectivity
  follows, the domain being a complementary component of the curve)
* Definition (conformal mapping from `𝔻` onto a domain of `ℂ*`, §3) — exists: `LehtoVirtanen1973.IsConformalMap`
  (continuous, one-to-one and analytic in the charts of ℂ*; the image is a separate hypothesis)
* Theorem 3.1 (Carathéodory, §3) — `thm1_3_1`
* Unlabelled (§3, P1:735–747): (3.1) is harmonic on `Ω`, (3.2) holds at the points where `f ∘ φ` is continuous, and
  for continuous `f` the function `u_f` solves the Dirichlet problem on `Ω` — `eq1_3_2`
* Definition (Borel sets, Borel functions and Borel measures on `ℂ*`, §3) — exists:
  `References.extPlaneMeasurableSpace` (the Borel sigma-algebra of ℂ*, a scoped instance of the shared layer, with
  the scoped BorelSpace instance beside it)
* Definition ((3.3), harmonic measure `ω(z, E, Ω)` of a Borel set `E ⊆ ∂Ω` relative to a Jordan domain `Ω`, §3) —
  `harmonicMeasureJordan`
* Unlabelled (§3, P1:755–758): `E ↦ ω(z, E)` is a Borel measure on `∂Ω`, and (3.4) — `eq1_3_4`
* Unlabelled (§3, P1:761–765): (3.3) and (3.4) do not depend on the choice of `φ` — `harmonicMeasureJordan_eq`

Not stated (inventory U−): the extension of `φ` maps `∂𝔻` onto `Γ = ∂Ω` and parametrizes `Γ` (P1:733; immediate from
Theorem 3.1, since `φ(𝔻) = Ω` is open); for a bounded Borel function `f` on `∂Ω`, `sup_Ω |u_f| = ‖f‖_{L^∞(ω)}`, and
every bounded harmonic function on `Ω` has the form (3.4) (P1:767–773; consequences of (3.4), Fatou's theorem and
Corollary 2.5, not cited later); the "length–area argument" (P1:852, a name for the method of the proof). (3.5)–(3.7)
are steps of the proof of Theorem 3.1.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc)
open LehtoVirtanen1973 (IsConformalMap)
open References (IsJordanDomainExt)

/-- **Theorem 3.1** (Carathéodory; Ch. I §3). Let `φ` be a conformal mapping from the unit disc `𝔻` onto a Jordan
domain `Ω`. Then `φ` has a continuous extension to `𝔻̄`, and the extension is a one-to-one map from `𝔻̄` onto `Ω̄`.
Modelling: `Ω` is a Jordan domain of `ℂ*`; `𝔻̄` and `Ω̄` are closures in `ℂ*`. Near misses (not pointers):
Pommerenke1992.caratheodory_theorem (on `ℂ̂`, without `Φ(𝔻̄) = Ω̄`) and LehtoVirtanen1973.boundary_correspondence
(which assumes a connected complement). -/
theorem thm1_3_1 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {φ : ExtPlane → ExtPlane}
    (hφ : IsConformalMap φ (toExt unitDisc)) (hφΩ : φ '' toExt unitDisc = Ω) :
    ∃ Φ : ExtPlane → ExtPlane, EqOn Φ φ (toExt unitDisc) ∧ ContinuousOn Φ (closure (toExt unitDisc)) ∧
      InjOn Φ (closure (toExt unitDisc)) ∧ Φ '' closure (toExt unitDisc) = closure Ω := by
  sorry

/-- **Unlabelled** (Ch. I §3, P1:735–747; (3.1) and (3.2); cited in Ch. II at P1:2226 and P1:2236 as "(3.2) of
Chapter I"). Let `φ` be a conformal map of `𝔻` onto a Jordan domain `Ω` with boundary `Γ`, continuously extended to
`𝔻̄`, and let `f` be a Borel function on `Γ` such that `f ∘ φ` is integrable on `∂𝔻`. If `w = φ⁻¹(z)`, then
(3.1) `u(z) = u_f(z) = ∫₀^{2π} f ∘ φ(e^{iθ}) (1 − |w|²)/|e^{iθ} − w|² dθ/2π` is harmonic on `Ω`, and
(3.2) `lim_{Ω∋z→ζ} u(z) = f(ζ)` whenever `φ⁻¹(ζ) ∈ ∂𝔻` is a point of continuity of `f ∘ φ`. In particular, if `f`
is continuous on `Γ`, then (3.2) holds for all `ζ ∈ Γ` and `u = u_f` solves the Dirichlet problem for `f` on `Ω`.
Modelling: (3.1) is not a separate definition: `u` is any function on `ℂ*` with `u(φ(w)) = u_{f∘φ}(w)` for `w ∈ 𝔻`,
which determines `u` on `Ω`; the boundary point is written `ζ = Φ(w)` with `w ∈ ∂𝔻` (`Φ` maps `∂𝔻` one-to-one onto
`Γ` by Theorem 3.1); the solution of the Dirichlet problem is any function equal to `u` on `Ω` and to `f` on `Γ`.
`f` is complex-valued and Borel on `ℂ*` (a Borel function on the closed set `Γ` extends by `0`). -/
theorem eq1_3_2 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {φ Φ : ExtPlane → ExtPlane}
    (hφ : IsConformalMap φ (toExt unitDisc)) (hφΩ : φ '' toExt unitDisc = Ω) (hΦφ : EqOn Φ φ (toExt unitDisc))
    (hΦ : ContinuousOn Φ (closure (toExt unitDisc))) {f : ExtPlane → ℂ} (hf : Measurable f)
    (hfi : Integrable (fun ζ : ℂ => f (Φ ζ)) arcMeasure) {u : ExtPlane → ℂ}
    (hu : ∀ w ∈ unitDisc, u (φ w) = poissonIntegral (fun ζ : ℂ => f (Φ ζ)) w) :
    HarmonicOnExt u Ω ∧
      (∀ w ∈ sphere (0 : ℂ) 1, ContinuousWithinAt (fun ζ : ℂ => f (Φ ζ)) (sphere 0 1) w →
        Tendsto u (𝓝[Ω] (Φ w)) (𝓝 (f (Φ w)))) ∧
      (ContinuousOn f (frontier Ω) →
        ∀ U : ExtPlane → ℂ, EqOn U u Ω → EqOn U f (frontier Ω) → IsDirichletSolution Ω f U) := by
  sorry

/-- **Definition** (harmonic measure relative to a Jordan domain, (3.3), Ch. I §3, P1:749–753). For a Jordan domain
`Ω`, `z ∈ Ω` and a Borel set `E ⊆ Γ = ∂Ω`, `ω(z, E, Ω) = ω(w, φ⁻¹(E), 𝔻)` with `w = φ⁻¹(z)`, for a conformal map `φ`
of `𝔻` onto `Ω` extended to `𝔻̄` (Theorem 3.1): the image of the disc measure `ω(w, ·, 𝔻)` under the extension `Φ`.
Modelling (leader ruling D1): a measure on `ℂ*`. The value does not depend on `φ` (`harmonicMeasureJordan_eq`), so it
is written as the supremum of the set of these measures over all such `φ`, `Φ` and `w` with `φ(w) = z`, a one-point
set (the registered "value over all maps" pattern of `Gehring1978.hypDensity`). Junk: the zero measure when there is
no such map (`z ∉ Ω`, or `Ω` has no conformal map from `𝔻` extending continuously to `𝔻̄`); never used there. -/
def harmonicMeasureJordan (Ω : Set ExtPlane) (z : ExtPlane) : Measure ExtPlane :=
  sSup {μ : Measure ExtPlane | ∃ (φ Φ : ExtPlane → ExtPlane) (w : ℂ), IsConformalMap φ (toExt unitDisc) ∧
    φ '' toExt unitDisc = Ω ∧ EqOn Φ φ (toExt unitDisc) ∧ ContinuousOn Φ (closure (toExt unitDisc)) ∧
    w ∈ unitDisc ∧ φ w = z ∧ μ = (harmonicMeasureDisc w).map fun ζ : ℂ => Φ ζ}

/-- **Unlabelled** (Ch. I §3, P1:755–758; (3.4); cited at P1:761–773). For `z ∈ Ω`, `E ↦ ω(z, E)` is a Borel measure on
`∂Ω`, and (3.1) can be rewritten as (3.4) `u(z) = ∫_{∂Ω} f(ζ) dω(z, ζ)`.
Modelling: `harmonicMeasureJordan Ω z` is a Borel measure on `ℂ*` by construction; "on `∂Ω`" is
`ω(z, ℂ* \ ∂Ω) = 0`. `z = φ(w)` for a conformal map `φ` of `𝔻` onto `Ω` with continuous extension `Φ`, and (3.4) is
stated for every `f` as in (3.1): Borel with `f ∘ φ` integrable on `∂𝔻`. -/
theorem eq1_3_4 {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {φ Φ : ExtPlane → ExtPlane}
    (hφ : IsConformalMap φ (toExt unitDisc)) (hφΩ : φ '' toExt unitDisc = Ω) (hΦφ : EqOn Φ φ (toExt unitDisc))
    (hΦ : ContinuousOn Φ (closure (toExt unitDisc))) {w : ℂ} (hw : w ∈ unitDisc) :
    harmonicMeasureJordan Ω (φ w) (frontier Ω)ᶜ = 0 ∧
      ∀ f : ExtPlane → ℂ, Measurable f → Integrable (fun ζ : ℂ => f (Φ ζ)) arcMeasure →
        poissonIntegral (fun ζ : ℂ => f (Φ ζ)) w = ∫ ζ in frontier Ω, f ζ ∂(harmonicMeasureJordan Ω (φ w)) := by
  sorry

/-- **Unlabelled** (Ch. I §3, P1:761–765; the definition (3.3) rests on it). Equations (3.3) and (3.4) do not
depend on the choice of `φ`, because `ω(T(w), T(φ⁻¹(E)), 𝔻) = ω(w, φ⁻¹(E), 𝔻)` for every conformal self-map `T` of
`𝔻`: for every conformal map `φ` of `𝔻` onto `Ω` with continuous extension `Φ` to `𝔻̄` and every `w ∈ 𝔻`,
`ω(φ(w), ·, Ω)` is the image of `ω(w, ·, 𝔻)` under `Φ`. -/
theorem harmonicMeasureJordan_eq {Ω : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) {φ Φ : ExtPlane → ExtPlane}
    (hφ : IsConformalMap φ (toExt unitDisc)) (hφΩ : φ '' toExt unitDisc = Ω) (hΦφ : EqOn Φ φ (toExt unitDisc))
    (hΦ : ContinuousOn Φ (closure (toExt unitDisc))) {w : ℂ} (hw : w ∈ unitDisc) :
    harmonicMeasureJordan Ω (φ w) = (harmonicMeasureDisc w).map fun ζ : ℂ => Φ ζ := by
  sorry

end GarnettMarshall2005
