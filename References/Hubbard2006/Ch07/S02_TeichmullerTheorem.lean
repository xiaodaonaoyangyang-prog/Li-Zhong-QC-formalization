import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

/-!
# Hubbard 2006, Chapter 7 §7.2: Teichmüller's theorem

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3803–3866.

**Conventions.** Hubbard's `T_X` for a Riemann surface `X` of finite type is the project's
`LiZhongQC.TeichSpaceFiniteType S₀ g n 0` (marked surfaces `(X, φ)` with `φ : S₀ → X` quasiconformal, modulo conformal
maps homotopic to the change of marking); `Q¹(X)` is the space of integrable quadratic differentials, which for finite
type is `LiZhongQC.admissibleQDInterior F₀` (at most simple poles at the punctures) with the norm `‖q‖₁ = ∬ |q|`
(`LiZhongQC.quadDiffNorm`), `B(X)` its open unit ball; the Beltrami form `‖q‖₁ q̄/|q|` is the Beltrami form of the
Teichmüller map with initial differential `q` and dilatation `k = ‖q‖₁` (the form `k ω̄/|ω|` of
`LiZhongQC.IsTeichmullerMap`), so the point `F(q) = [X_q, id]` is the class of the target of the Teichmüller map `f₀` of
dilatation `‖q‖₁` in the homotopy class of the marking.

**Teichmüller distance (decision D18).** Hubbard's Teichmüller distance (Def. 6.4.4, display (6.4.2), H2:2342, repeated
at H2:2966, H2:3056, H2:3842 (7.2.5) and H2:4525 (7.6.5)) is `d((X₁,φ₁),(X₂,φ₂)) := inf_f ln K(f)`, with no factor `½`
(the remark at H2:2853 explains that the `½` of Thm 6.6.5 comes from the factor 2 in the metric of `𝔻`). The installed
`LiZhongQC.teichDistance` (`Ch08/S29_TeichmullerMetric`, lines 34–39) and `LiZhongQC.teichDistanceFT`
(`Ch09/S32_FiniteTypeTeichmuller`, lines 708–713) are `sInf {d | … d = (1/2) * Real.log (maxDilatationRS g).toReal}`.
Hence **Hubbard's `d` is `2 · LiZhongQC.teichDistanceFT`**; the statements below use that factor explicitly and no new
distance is defined.

**Near misses.** `LiZhongQC.teichSpaceFiniteType_ball` states a bijection of the Euclidean unit ball with `T_{g,n,m}`
without continuity, and `LiZhongQC.teichDistanceFT_complete_metric` states the homeomorphism for an unspecified
bijection `Φ` of the Euclidean ball (via the normalized Teichmüller data); Hubbard's `F` is the specific map `q ↦ [X_q,
id]` of the `L¹` ball, so `thm7_2_1` is a new item.

* Setup (the unit ball `B(X)`, the Beltrami forms `‖q‖₁ q̄/|q|`, the surfaces `X_q`, the map `F`) — omitted: modelled in
  `thm7_2_1`
* Theorem 7.2.1 (Teichmüller's theorem on contractibility: `F : B(X) → T_X` is a homeomorphism) — `thm7_2_1`
* Exercise 7.2.2 — omitted: exercise
* Corollary 7.2.3 (a) (existence and uniqueness of the Teichmüller map homotopic to `f`) — exists:
  `LiZhongQC.thm32_2_existence_gn`, `LiZhongQC.thm32_1_uniqueness_gn`
* Corollary 7.2.3 (b) (`d(X, σ_f(X)) = ln K(g)`) — `cor7_2_3_b`
-/

open Set Filter Topology
open scoped Manifold ContDiff
open LiZhongQC

namespace Hubbard2006

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **Theorem 7.2.1** (Teichmüller's theorem on contractibility, Ch. 7 §7.2, H2:3811). Let `X = S₀` be a Riemann surface
of finite type `(g, n, 0)`, not exceptional, with its structure `F₀`. The map `F : B(X) → T_X`, `q ↦ [X_q, id]`, from
the open unit ball of `Q¹(X)` (the admissible quadratic differentials with `‖q‖₁ < 1`) to the Teichmüller space is a
homeomorphism: for each such `q` the class `F q` is that of a marked surface whose marking is homotopic to a Teichmüller
map `f₀` with initial differential `q` and dilatation `k = ‖q‖₁` (`f₀` conformal for `q = 0`); `F` is injective and
onto; and `F`, `F⁻¹` are continuous for the `L¹` norm on the ball and the Teichmüller metric `teichDistanceFT` (a
sequence converges in `B(X)` iff its image converges in `T_X`; both topologies are metric, so this is the homeomorphism
property). Modelling: `Q¹(X)` carries the `L¹` norm `quadDiffNorm`. -/
theorem thm7_2_1 {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0) :
    ∃ F : {q : admissibleQDInterior F₀ // quadDiffNorm (q : S₀ → ℂ → ℂ) < 1} → TeichSpaceFiniteType S₀ g n 0,
      (∀ q, ∃ (m₁ : MarkedFiniteTypeRS S₀ g n 0) (f₀ : S₀ ≃ₜ m₁.X.carrier) (q' : m₁.X.carrier → ℂ → ℂ),
        Quot.mk _ m₁ = F q ∧ ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₀ : C(S₀, m₁.X.carrier)) ∧
          (((q : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) = 0 ∧ IsBiholomorphic f₀ ∨
            ((q : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) ≠ 0 ∧
              IsAdmissibleTeichmullerMap F₀ f₀ (q : admissibleQDInterior F₀) q'
                (quadDiffNorm (q : S₀ → ℂ → ℂ)).toReal)) ∧
      Function.Bijective F ∧
      ∀ (q : {q : admissibleQDInterior F₀ // quadDiffNorm (q : S₀ → ℂ → ℂ) < 1})
        (qs : ℕ → {q : admissibleQDInterior F₀ // quadDiffNorm (q : S₀ → ℂ → ℂ) < 1}),
        Tendsto (fun i => quadDiffNorm (((qs i : admissibleQDInterior F₀) : S₀ → ℂ → ℂ) -
          ((q : admissibleQDInterior F₀) : S₀ → ℂ → ℂ))) atTop (𝓝 0) ↔
        Tendsto (fun i => teichDistanceFT (F (qs i)) (F q)) atTop (𝓝 0) := by
  sorry

/-- **Corollary 7.2.3 (b)** (Ch. 7 §7.2, H2:3839). Let `X = S₀` be of finite type `(g, n, 0)` (not exceptional,
structure `F₀`), `f : X → X` a quasiconformal homeomorphism and `g` a Teichmüller map of `X` (admissible, or conformal)
homotopic to `f`. Then `d(X, σ_f(X)) = ln K(g)`, where `σ_f(X)` is the marked surface `(X, f)` and `X = (X, id)`. In the
project's normalization of the Teichmüller distance (decision D18, see the module docstring) this reads `2 · d_T([X,
id], [X, f]) = ln K(g)`. Modelling: the identity is required to be quasiconformal (`hid`, true for every surface);
`K(g)` is `(LiZhongQC.maxDilatationRS g).toReal`. -/
theorem cor7_2_3_b {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hid : IsQCRS (Homeomorph.refl S₀)) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) (t : S₀ ≃ₜ S₀)
    (ht : IsBiholomorphic t ∨ ∃ (q q' : S₀ → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ t q q' k)
    (hh : ContinuousMap.Homotopic (f : C(S₀, S₀)) (t : C(S₀, S₀))) :
    2 * teichDistanceFT
        (Quot.mk _ (⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, hid⟩ : MarkedFiniteTypeRS S₀ g n 0))
        (Quot.mk _ (⟨⟨S₀, F₀⟩, f, hf⟩ : MarkedFiniteTypeRS S₀ g n 0)) =
      Real.log (maxDilatationRS t).toReal := by
  sorry

end Hubbard2006
