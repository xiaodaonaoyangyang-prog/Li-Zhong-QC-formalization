import LiZhongQC.Ch09.S31_FiniteType
import LiZhongQC.Lemmas.LocalRoots

/-!
# §32 有限型曲面的 Teichmüller 定理 — Teichmüller's theorem for surfaces of finite type

* §32.1 surfaces of type `(g, n)`: Theorem 32.1 (uniqueness, (32.1)) via the two-sheeted covering
  branched at the punctures (the lifted differential `4ζ²φ(ζ²)dζ²` is holomorphic); Theorem 32.2
  (existence), (32.2)                 — `thm32_1_uniqueness_gn`, `thm32_2_existence_gn`
* §32.2 surfaces of type `(g, n, m)`, `m ≠ 0`, via the Schottky double: Theorem 32.3 (uniqueness),
  Theorem 32.4 (existence), (32.3)     — `thm32_3_uniqueness_gnm`, `thm32_4_existence_gnm`
* §32.3 the Teichmüller space `T_{g,n,m}` of marked surfaces of finite type: every point
  corresponds to `(k, ω)` with `ω ∈ Q̃(S₀)` normalized; `T_{g,n,m} ↔` unit ball of
  `ℝ^{6g-6+2n+3m}`; the Teichmüller distance; the modular group and `R_{g,n,m} = T/Mod`;
  `T_{g,n,m}` has no complex structure when its dimension is odd
                                       — `MarkedFiniteTypeRS`, `TeichSpaceFiniteType`,
                                         `teichSpaceFiniteType_ball`, `teichDistanceFT`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- The pull-back `q ∘ ι` (in charts) of a quadratic differential on the closed surface `X` of a
finite type structure `F` to the interior `S`. -/
def pullbackQD {g n m : ℕ} (F : FiniteTypeStructure S g n m) (q : F.X.carrier → ℂ → ℂ) : S → ℂ → ℂ :=
  fun x z => q (F.ι x) (chartAt ℂ (F.ι x) (F.ι ((chartAt ℂ x).symm z))) *
    deriv (fun w => chartAt ℂ (F.ι x) (F.ι ((chartAt ℂ x).symm w))) z ^ 2

/-- The pull-back is real linear. -/
def pullbackQDLinear {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (F.X.carrier → ℂ → ℂ) →ₗ[ℝ] (S → ℂ → ℂ) where
  toFun := pullbackQD F
  map_add' q₁ q₂ := by
    funext x z
    simp only [pullbackQD, Pi.add_apply]
    ring
  map_smul' c q := by
    funext x z
    simp only [pullbackQD, Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

/-- §32.1: the admissible quadratic differentials of `S₀`, viewed on the interior `S₀` itself: the
pull-backs of the elements of `Q̃(S₀)`. -/
def admissibleQDInterior {g n m : ℕ} (F : FiniteTypeStructure S g n m) : Submodule ℝ (S → ℂ → ℂ) :=
  (admissibleQDSpace F).map (pullbackQDLinear F)

/-- §32.1: the pull-back of an admissible differential is a holomorphic quadratic differential on the
interior, and `q ↦ q ∘ ι` is injective on `Q̃(S₀)`. -/
theorem admissibleQDInterior_holomorphic [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) :
    (∀ q ∈ admissibleQDInterior F, IsHolQuadDiff q) ∧
      InjOn (pullbackQDLinear F) (admissibleQDSpace F) := by
  sorry

/-- §32.1: a Teichmüller map `f₀ : S₀ → S` between surfaces of finite type whose initial differential
is an admissible quadratic differential (its Beltrami differential is `k ω̄/|ω|`). -/
def IsAdmissibleTeichmullerMap {g n m : ℕ} (F : FiniteTypeStructure S₀ g n m) (f : S₀ ≃ₜ S)
    (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ) : Prop :=
  q ∈ admissibleQDInterior F ∧ IsTeichmullerMap f q q' k

/-! ## §32.1 Surfaces of type `(g, n)` -/

/-- §32.1 (the two-sheeted covering): a closed surface `X` with an even number `2n` of marked points
`P` has a two-sheeted covering `X̃ → X` (a closed surface of genus `2g + n - 1`) branched exactly
at `P` (branching order `1`); it is obtained by cutting along `n` disjoint arcs joining the points
of `P` in pairs and gluing two copies crosswise. -/
theorem exists_branched_double_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] {g n : ℕ} (hX : HasGenus X g) (P : Finset X)
    (hP : P.card = 2 * n) :
    ∃ (X' : ClosedRS.{u}) (pr : X'.carrier → X), HasGenus X'.carrier (2 * g + n - 1) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ (∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) ∧
      ∃ h : X'.carrier ≃ₜ X'.carrier, IsBiholomorphic h ∧ (∀ y, h (h y) = y) ∧ (∀ y, pr (h y) = pr y) ∧
        ∀ y, h y = y ↔ pr y ∈ P := by
  sorry

/-- §32.1: the lift of an admissible differential to the branched double cover: if `ω = φ(z) dz²`
near a puncture (`z = 0`), then in the parameter `ζ = √z` of the point above it,
`ω̃ = 4ζ²φ(ζ²) dζ²`; a differential of order `n ≥ -1` at the puncture lifts to one of order
`2n + 2 ≥ 0`.  Hence the lift of an admissible differential is holomorphic.

Correction to the book's statement: the hypothesis `MeromorphicAt φ 0` is added.  It is implicit
in the book (`φ` is the coefficient of a meromorphic quadratic differential), and without it the
statement is false: Mathlib gives `meromorphicOrderAt` the junk value `0` at a point where the
function is not meromorphic, so a non-meromorphic `φ` satisfies the hypothesis with `N = 0`
while the left-hand side is `0`, not `2`. -/
theorem lift_admissibleQD_order {φ : ℂ → ℂ} {N : ℤ} (hφ0 : MeromorphicAt φ 0) (_hN : -1 ≤ N)
    (hφ : meromorphicOrderAt φ 0 = N) :
    meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2 := by
  -- the squaring map `g : ζ ↦ ζ²` is analytic and vanishes to order `2` at `0`
  have hg : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2) 0 := by fun_prop
  have hpow : (fun ζ : ℂ => ζ ^ 2) = (id : ℂ → ℂ) ^ 2 := by funext ζ; simp
  have hsq : analyticOrderAt (fun ζ : ℂ => ζ ^ 2) (0 : ℂ) = 2 := by
    rw [hpow, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  have hgo : analyticOrderAt (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) (0 : ℂ) = 2 := by
    have hsub : (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) = fun ζ : ℂ => ζ ^ 2 := by
      funext ζ; simp
    rw [hsub, hsq]
  -- hence `g` is not locally constant at `0`
  have hnc : ¬ EventuallyConst (fun ζ : ℂ => ζ ^ 2) (𝓝 (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
    simp
  -- `φ` is meromorphic at `g 0 = 0`, and its order there is `N`
  have hφ0' : MeromorphicAt φ ((fun ζ : ℂ => ζ ^ 2) 0) := by simpa using hφ0
  have harg : meromorphicOrderAt φ ((fun ζ : ℂ => ζ ^ 2) 0) = (N : WithTop ℤ) := by
    simpa using hφ
  -- the order of `ζ ↦ φ(ζ²)` is `2N`
  have hcompm : MeromorphicAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 :=
    MeromorphicAt.comp_analyticAt (f := φ) (g := fun ζ : ℂ => ζ ^ 2) (x := (0 : ℂ)) hφ0' hg
  have hco : meromorphicOrderAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 = 2 * (N : WithTop ℤ) := by
    have h := MeromorphicAt.meromorphicOrderAt_comp (f := φ) (g := fun ζ : ℂ => ζ ^ 2)
      (x := (0 : ℂ)) hφ0' hg hnc
    rw [hgo, harg] at h
    show meromorphicOrderAt (φ ∘ fun ζ : ℂ => ζ ^ 2) 0 = 2 * (N : WithTop ℤ)
    rw [h]
    simp [mul_comm]
  -- the order of `ζ ↦ 4ζ²` is `2`
  have h4a : AnalyticAt ℂ (fun ζ : ℂ => 4 * ζ ^ 2) 0 := by fun_prop
  have h4o : analyticOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) (0 : ℂ) = 2 := by
    rw [show (fun ζ : ℂ => 4 * ζ ^ 2) = (fun _ : ℂ => (4 : ℂ)) * fun ζ : ℂ => ζ ^ 2 from rfl,
      analyticOrderAt_mul analyticAt_const hg,
      (analyticAt_const (v := (4 : ℂ))).analyticOrderAt_eq_zero.mpr (by norm_num), zero_add, hsq]
  have h4 : meromorphicOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) 0 = 2 := by
    rw [h4a.meromorphicOrderAt_eq, h4o]
    simp
  -- the order of a product is the sum of the orders
  rw [show (fun ζ : ℂ => 4 * ζ ^ 2 * φ (ζ ^ 2))
        = (fun ζ : ℂ => 4 * ζ ^ 2) * fun ζ : ℂ => φ (ζ ^ 2) from rfl,
    meromorphicOrderAt_mul h4a.meromorphicAt hcompm, h4, hco, add_comm]

variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.1: the Teichmüller map `f₀` and any `f ≃ f₀` lift to the branched double covers; the lift of
`f₀` is again a Teichmüller map, with the holomorphic lifted differential, and the lift of `f` can be
chosen homotopic to the lift of `f₀` (by lifting the track of a point under the homotopy). -/
theorem lift_teichmullerMap_double_cover {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * n) 0)
    (F₁ : FiniteTypeStructure S g (2 * n) 0) {X₀' X₁' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    {pr₁ : X₁'.carrier → F₁.X.carrier} (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ ∀ x, (pr₀ ⁻¹' {x}).ncard ≤ 2)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ ∀ x, (pr₁ ⁻¹' {x}).ncard ≤ 2) {f₀ f : S₀ ≃ₜ S}
    {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    ∃ (f₀' f' : X₀'.carrier ≃ₜ X₁'.carrier) (qtil : X₀'.carrier → ℂ → ℂ) (qtil' : X₁'.carrier → ℂ → ℂ),
      IsTeichmullerMap f₀' qtil qtil' k ∧ IsQCRS f' ∧ maxDilatationRS f' = maxDilatationRS f ∧
      ContinuousMap.Homotopic (f₀' : C(X₀'.carrier, X₁'.carrier)) (f' : C(X₀'.carrier, X₁'.carrier)) := by
  sorry

/-- **Theorem 32.1** (32.1).  Let `S₀` be a non-exceptional surface of type `(g, n)` and
`f₀ : S₀ → S` a Teichmüller map with Beltrami differential `k ω̄/|ω|`, `ω` an admissible quadratic
differential, `k ∈ [0, 1)`.  Then `f₀` is the unique extremal map of its homotopy class: every
quasiconformal `f ≃ f₀` satisfies `K[f₀] ≤ K[f]`, with equality only for `f = f₀`.
(The cases `n` even, `n` odd, and `(0, 4)` are reduced to Theorem 26.2 by branched double
coverings.) -/
theorem thm32_1_uniqueness_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  sorry

/-- (32.2): with `h₀`, `h₁` the non-trivial covering transformations of the double covers, the
Teichmüller map `ftil₀ : S̃₀ → S̃` obtained from Theorem 27.2 satisfies `h₁ ∘ ftil₀ ∘ h₀⁻¹ = ftil₀`, i.e.
`h₁ ∘ ftil₀ = ftil₀ ∘ h₀` (by uniqueness, since `h₁ ∘ ftil₀ ∘ h₀⁻¹` is a Teichmüller map of the same dilatation
homotopic to `ftil₀`); hence `ftil₀` and its Beltrami differential descend to `S₀ → S`. -/
theorem eq32_2_symmetric_lift {X₀' X₁' : ClosedRS.{u}} {g' : ℕ} (hg' : 1 < g') (h₀' : HasGenus X₀'.carrier g')
    (h₁' : HasGenus X₁'.carrier g') {h₀ : X₀'.carrier ≃ₜ X₀'.carrier} {h₁ : X₁'.carrier ≃ₜ X₁'.carrier}
    (hh₀ : IsBiholomorphic h₀) (hh₁ : IsBiholomorphic h₁) {ftil ftil₀ : X₀'.carrier ≃ₜ X₁'.carrier}
    (hsym : ∀ y, ftil (h₀ y) = h₁ (ftil y)) {q : X₀'.carrier → ℂ → ℂ} {q' : X₁'.carrier → ℂ → ℂ} {k : ℝ}
    (hftil₀ : IsTeichmullerMap ftil₀ q q' k)
    (hhom : ContinuousMap.Homotopic (ftil : C(X₀'.carrier, X₁'.carrier)) (ftil₀ : C(X₀'.carrier, X₁'.carrier))) :
    ∀ y, ftil₀ (h₀ y) = h₁ (ftil₀ y) := by
  sorry

/-- The lift formula of `lift_admissibleQD_order` without the side condition `-1 ≤ N`, which its
proof never uses: for `φ` meromorphic at `0` of order `N ∈ ℤ`, `4ζ²φ(ζ²)` has order `2N + 2`. -/
theorem meromorphicOrderAt_lift_sq {φ : ℂ → ℂ} {N : ℤ} (hφ0 : MeromorphicAt φ 0)
    (hφ : meromorphicOrderAt φ 0 = N) :
    meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2 := by
  -- the squaring map `g : ζ ↦ ζ²` is analytic and vanishes to order `2` at `0`
  have hg : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2) 0 := by fun_prop
  have hpow : (fun ζ : ℂ => ζ ^ 2) = (id : ℂ → ℂ) ^ 2 := by funext ζ; simp
  have hsq : analyticOrderAt (fun ζ : ℂ => ζ ^ 2) (0 : ℂ) = 2 := by
    rw [hpow, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  have hgo : analyticOrderAt (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) (0 : ℂ) = 2 := by
    have hsub : (fun ζ : ℂ => ζ ^ 2 - (fun ζ : ℂ => ζ ^ 2) 0) = fun ζ : ℂ => ζ ^ 2 := by
      funext ζ; simp
    rw [hsub, hsq]
  -- hence `g` is not locally constant at `0`
  have hnc : ¬ EventuallyConst (fun ζ : ℂ => ζ ^ 2) (𝓝 (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
    simp
  -- `φ` is meromorphic at `g 0 = 0`, and its order there is `N`
  have hφ0' : MeromorphicAt φ ((fun ζ : ℂ => ζ ^ 2) 0) := by simpa using hφ0
  have harg : meromorphicOrderAt φ ((fun ζ : ℂ => ζ ^ 2) 0) = (N : WithTop ℤ) := by
    simpa using hφ
  -- the order of `ζ ↦ φ(ζ²)` is `2N`
  have hcompm : MeromorphicAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 :=
    MeromorphicAt.comp_analyticAt (f := φ) (g := fun ζ : ℂ => ζ ^ 2) (x := (0 : ℂ)) hφ0' hg
  have hco : meromorphicOrderAt (fun ζ : ℂ => φ (ζ ^ 2)) 0 = 2 * (N : WithTop ℤ) := by
    have h := MeromorphicAt.meromorphicOrderAt_comp (f := φ) (g := fun ζ : ℂ => ζ ^ 2)
      (x := (0 : ℂ)) hφ0' hg hnc
    rw [hgo, harg] at h
    show meromorphicOrderAt (φ ∘ fun ζ : ℂ => ζ ^ 2) 0 = 2 * (N : WithTop ℤ)
    rw [h]
    simp [mul_comm]
  -- the order of `ζ ↦ 4ζ²` is `2`
  have h4a : AnalyticAt ℂ (fun ζ : ℂ => 4 * ζ ^ 2) 0 := by fun_prop
  have h4o : analyticOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) (0 : ℂ) = 2 := by
    rw [show (fun ζ : ℂ => 4 * ζ ^ 2) = (fun _ : ℂ => (4 : ℂ)) * fun ζ : ℂ => ζ ^ 2 from rfl,
      analyticOrderAt_mul analyticAt_const hg,
      (analyticAt_const (v := (4 : ℂ))).analyticOrderAt_eq_zero.mpr (by norm_num), zero_add, hsq]
  have h4 : meromorphicOrderAt (fun ζ : ℂ => 4 * ζ ^ 2) 0 = 2 := by
    rw [h4a.meromorphicOrderAt_eq, h4o]
    simp
  -- the order of a product is the sum of the orders
  rw [show (fun ζ : ℂ => 4 * ζ ^ 2 * φ (ζ ^ 2))
        = (fun ζ : ℂ => 4 * ζ ^ 2) * fun ζ : ℂ => φ (ζ ^ 2) from rfl,
    meromorphicOrderAt_mul h4a.meromorphicAt hcompm, h4, hco, add_comm]

/-- §32.1: the projection of the lifted differential: if `ω̃` is regular at the point above a
puncture, `ω` has a simple pole there; if `ω̃` has a zero there, `ω` is regular (a differential of
order `2(n+1)` above projects to one of order `n`). -/
theorem project_admissibleQD_order {φ : ℂ → ℂ} {N : ℤ} (hN : 0 ≤ N)
    (hφ : meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = 2 * N + 2) : meromorphicOrderAt φ 0 = N := by
  -- `ψ = 4ζ²φ(ζ²)` is meromorphic at `0`, since its order is not the junk value `0`
  have hcast : ∀ k : ℤ, ((2 * k + 2 : ℤ) : WithTop ℤ) = 2 * (k : WithTop ℤ) + 2 := fun k => by
    norm_cast
  have hψ : MeromorphicAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 := by
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    rw [hφ, ← hcast N]
    have h : (2 * N + 2 : ℤ) ≠ 0 := by omega
    exact fun h' => h (WithTop.coe_eq_coe.1 (h'.trans WithTop.coe_zero.symm))
  -- hence `φ` is meromorphic at `0`
  have hφ0 : MeromorphicAt φ 0 := by
    obtain ⟨m, hm⟩ := hψ
    refine ⟨m + 2, ?_⟩
    have hG : AnalyticAt ℂ (fun ζ => ζ ^ (2 * (m + 2)) * φ (ζ ^ 2)) 0 := by
      have h1 : AnalyticAt ℂ
          (fun ζ : ℂ => 1 / 4 * ζ ^ (m + 2) * ((ζ - 0) ^ m • (4 * ζ ^ 2 * φ (ζ ^ 2)))) 0 :=
        (analyticAt_const.mul (analyticAt_id.pow (m + 2))).mul hm
      refine h1.congr (Eventually.of_forall fun ζ => ?_)
      simp only [sub_zero, smul_eq_mul]
      ring
    have := analyticAt_of_analyticAt_pow_mul_comp_sq hG
    simpa using this
  -- the order of `φ` at `0`
  cases h : meromorphicOrderAt φ 0 using WithTop.recTopCoe with
  | top =>
    -- order `⊤`: `φ` vanishes near `0`, hence so does `ψ`, contradicting `ord ψ = 2N + 2`
    exfalso
    rw [meromorphicOrderAt_eq_top_iff] at h
    have hψtop : meromorphicOrderAt (fun ζ => 4 * ζ ^ 2 * φ (ζ ^ 2)) 0 = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      have hsq : Tendsto (fun ζ : ℂ => ζ ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have : Tendsto (fun ζ : ℂ => ζ ^ 2) (𝓝 0) (𝓝 ((0 : ℂ) ^ 2)) :=
            (continuous_pow 2).tendsto 0
          rw [zero_pow two_ne_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · exact eventually_nhdsWithin_of_forall fun ζ hζ => pow_ne_zero 2 hζ
      exact (hsq.eventually h).mono fun ζ hζ => by simp [hζ]
    rw [hφ, ← hcast N] at hψtop
    exact WithTop.coe_ne_top hψtop
  | coe m =>
    have hlift := meromorphicOrderAt_lift_sq hφ0 h
    rw [hφ, ← hcast N, ← hcast m] at hlift
    have h2 : (2 * N + 2 : ℤ) = 2 * m + 2 := WithTop.coe_eq_coe.1 hlift
    have h3 : m = N := by omega
    rw [h3]

/-- **Theorem 32.2**: let `S₀`, `S₁` be non-exceptional surfaces of type `(g, n)` and `f : S₀ → S₁`
a quasiconformal homeomorphism.  Then the homotopy class of `f` contains a Teichmüller map `f₀`
whose associated quadratic differential is admissible (or `f₀` is conformal). -/
theorem thm32_2_existence_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  sorry

/-! ## §32.2 Surfaces of type `(g, n, m)`, `m ≠ 0` -/

/-- §32.2: the symmetric extension of a map `f : S₀ → S` to the Schottky doubles:
`f^d ∘ ιd₀ = ιd₁ ∘ f` and `f^d ∘ J₀ = J₁ ∘ f^d`. -/
def IsSymmetricExtension {Xd₀ Xd₁ : ClosedRS.{u}} (J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier) (J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier)
    (ιd₀ : S₀ → Xd₀.carrier) (ιd₁ : S → Xd₁.carrier) (f : S₀ → S) (fd : Xd₀.carrier ≃ₜ Xd₁.carrier) : Prop :=
  (∀ x, fd (ιd₀ x) = ιd₁ (f x)) ∧ ∀ y, fd (J₀ y) = J₁ (fd y)

/-- §32.2: quasiconformal maps, homotopies and admissible differentials extend symmetrically to the
doubles; `K[f^d] = K[f]`, `f ≃ f₀` implies `f^d ≃ f₀^d`, and the extension of a Teichmüller map with
admissible differential `ω` is a Teichmüller map with differential `ω^d`. -/
theorem symmetric_extension_properties {g n m : ℕ} (hm : m ≠ 0) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier}
    {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier}
    {Pd₁ : Finset Xd₁.carrier} (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ fd : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd ∧ IsQCRS fd ∧
      maxDilatationRS fd = maxDilatationRS f ∧
      ∀ f' : S₀ ≃ₜ S, ∀ fd' : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f' fd' →
        ContinuousMap.Homotopic (f : C(S₀, S)) (f' : C(S₀, S)) →
        ContinuousMap.Homotopic (fd : C(Xd₀.carrier, Xd₁.carrier)) (fd' : C(Xd₀.carrier, Xd₁.carrier)) := by
  sorry

/-- **Theorem 32.3**: let `S₀` be a non-exceptional surface of type `(g, n, m)`, `ω` an admissible
quadratic differential on `S₀`, and `f : S₀ → S` a Teichmüller map with associated differential `ω`.
Then `f` is the unique extremal map of its homotopy class. -/
theorem thm32_3_uniqueness_gnm {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  sorry

/-- (32.3): the Teichmüller map `f₀ : S₀^d → S₁^d` in the class of `f^d` commutes with the
reflections, `g₁ ∘ f₀ = f₀ ∘ g₀` (uniqueness applied to `g₁ ∘ f₀ ∘ g₀⁻¹`, which is again a Teichmüller
map homotopic to `f^d`); hence `f₀` maps the boundary curves of `S₀` (the fixed curves of `g₀`) onto
those of `S₁`, so `f₀(S₀) = S₁`. -/
theorem eq32_3_teichmuller_commutes_reflection {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁) (f : S₀ ≃ₜ S)
    {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd)
    {f₀ : Xd₀.carrier ≃ₜ Xd₁.carrier} {q : Xd₀.carrier → ℂ → ℂ} {q' : Xd₁.carrier → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsTeichmullerMap f₀ q q' k)
    (hhom : ContinuousMap.Homotopic (fd : C(Xd₀.carrier, Xd₁.carrier)) (f₀ : C(Xd₀.carrier, Xd₁.carrier))) :
    (∀ y, f₀ (J₀ y) = J₁ (f₀ y)) ∧ f₀ '' range ιd₀ = range ιd₁ := by
  sorry

/-- **Theorem 32.4**: let `S₀`, `S₁` be non-exceptional surfaces of type `(g, n, m)` and
`f : S₀ → S₁` a quasiconformal map.  Then the homotopy class of `f` contains a Teichmüller map whose
associated quadratic differential is admissible (or a conformal map).  (Method of Ahlfors.) -/
theorem thm32_4_existence_gnm {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  sorry

/-! ## §32.3 The Teichmüller space of a surface of finite type -/

/-- A Riemann surface of finite type `(g, n, m)`, bundled. -/
structure FiniteTypeRS (g n m : ℕ) : Type (u + 1) where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [connectedSpace : ConnectedSpace carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) ω carrier]
  structure' : FiniteTypeStructure carrier g n m

attribute [instance] FiniteTypeRS.topologicalSpace FiniteTypeRS.t2Space FiniteTypeRS.connectedSpace
  FiniteTypeRS.chartedSpace FiniteTypeRS.isManifold

/-- **§32.3 (标记曲面).**  A surface `X` of type `(g, n, m)` marked by a quasiconformal
homeomorphism `f : S₀ → X`. -/
structure MarkedFiniteTypeRS (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (g n m : ℕ) where
  X : FiniteTypeRS.{u} g n m
  marking : S₀ ≃ₜ X.carrier
  qc : IsQCRS marking

/-- §32.3: `(S₁, f₁) ~ (S₂, f₂)` iff there is a conformal `φ : S₁ → S₂` homotopic to `f₂ ∘ f₁⁻¹`. -/
def MarkedFiniteTypeRS.Equiv {g n m : ℕ} (m₁ m₂ : MarkedFiniteTypeRS S₀ g n m) : Prop :=
  ∃ c : m₁.X.carrier ≃ₜ m₂.X.carrier, IsBiholomorphic c ∧
    ContinuousMap.Homotopic ((m₁.marking.trans c : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
      (m₂.marking : C(S₀, m₂.X.carrier))

/-- **§32.3**: the Teichmüller space `T(S₀) = T_{g,n,m}` of a surface of finite type. -/
def TeichSpaceFiniteType (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (g n m : ℕ) : Type (u + 1) :=
  Quot (MarkedFiniteTypeRS.Equiv (S₀ := S₀) (g := g) (n := n) (m := m))

/-- §32.3: every marked surface `(S, f)` corresponds to a Teichmüller map `f₀ : S₀ → S` in the class
of `f` with admissible differential `ω`, unique up to a positive factor, and to `k ∈ [0, 1)`;
equivalent marked surfaces give the same `(ω, k)` (the Beltrami differential is unchanged by
composition with a conformal map). -/
theorem markedFiniteType_teichmuller_data {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (m₁ : MarkedFiniteTypeRS S₀ g n m) :
    ∃ (f₀ : S₀ ≃ₜ m₁.X.carrier) (k : ℝ), 0 ≤ k ∧ k < 1 ∧
      ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₀ : C(S₀, m₁.X.carrier)) ∧
      ((k = 0 ∧ IsBiholomorphic f₀) ∨ (0 < k ∧ ∃ (q : S₀ → ℂ → ℂ) (q' : m₁.X.carrier → ℂ → ℂ),
        IsAdmissibleTeichmullerMap F₀ f₀ q q' k ∧
        ∀ (q₂ : S₀ → ℂ → ℂ) (q₂' : m₁.X.carrier → ℂ → ℂ) (k₂ : ℝ) (f₂ : S₀ ≃ₜ m₁.X.carrier),
          IsAdmissibleTeichmullerMap F₀ f₂ q₂ q₂' k₂ →
          ContinuousMap.Homotopic (m₁.marking : C(S₀, m₁.X.carrier)) (f₂ : C(S₀, m₁.X.carrier)) →
          k₂ = k ∧ ∃ c : ℝ, 0 < c ∧ q₂ = (c : ℂ) • q)) := by
  sorry

/-- **§32.3**: `T_{g,n,m}` is in bijection with the open unit ball of `ℝ^{6g-6+2n+3m}`, via the
Teichmüller data `(k, ω)`, `ω` normalized on the unit sphere of `Q̃(S₀)` (in a basis). -/
theorem teichSpaceFiniteType_ball {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (Module.finrank ℝ (admissibleQDInterior F₀) : ℤ) = 6 * g - 6 + 2 * n + 3 * m ∧
      ∃ Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m,
        InjOn Φ (ball 0 1) ∧ ∀ p, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p := by
  sorry

/-- §32.3: the Teichmüller distance `d_T(τ₁, τ₂) = ½ ln K[f₀]`, `f₀` the extremal map in the class of
`f₂ ∘ f₁⁻¹`.

Written as the `sInf` of a set of reals.  The nested form `⨅ m₁ m₂ g (_ : …), …` is identically `0` in `ℝ`:
for a triple outside the classes the innermost infimum is over an empty proposition, `sInf ∅ = 0`, and all values
are `≥ 0` (corrected 2026-09-25, as for `UniversalTeichmuller.dist`). -/
def teichDistanceFT {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) : ℝ :=
  sInf {d | ∃ (m₁ : MarkedFiniteTypeRS S₀ g n m) (m₂ : MarkedFiniteTypeRS S₀ g n m) (h : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS h ∧
      ContinuousMap.Homotopic ((m₁.marking.trans h : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
    d = (1 / 2) * Real.log (maxDilatationRS h).toReal}

/-- §32.3: `d_T` is a complete metric on `T_{g,n,m}`, and the bijection with the unit ball of
`ℝ^{6g-6+2n+3m}` is a homeomorphism (the proof repeats Chapter 7 without essential change). -/
theorem teichDistanceFT_complete_metric {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = 0 ↔ p = q) ∧
      (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = teichDistanceFT q p) ∧
      (∀ p q r : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p r ≤ teichDistanceFT p q + teichDistanceFT q r) ∧
      ∀ p : ℕ → TeichSpaceFiniteType S₀ g n m, (∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, teichDistanceFT (p i) (p j) < ε) →
        ∃ q, Tendsto (fun i => teichDistanceFT (p i) q) atTop (𝓝 0) := by
  sorry

/-- §32.3: the modular group `Mod_{g,n,m}` (quasiconformal self-maps `σ` of `S₀` acting by
`[S, f] ↦ [S, f ∘ σ]`), and `R_{g,n,m} = T_{g,n,m}/Mod_{g,n,m}`: two marked surfaces have conformally
equivalent underlying surfaces iff they are related by a modular transformation. -/
theorem moduliFiniteType_eq_quotient {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (m₁ m₂ : MarkedFiniteTypeRS S₀ g n m) :
    RSConformallyEquivalent m₁.X.carrier m₂.X.carrier ↔
      ∃ (σ : S₀ ≃ₜ S₀) (hσ : IsQCRS (σ.trans m₂.marking)),
        MarkedFiniteTypeRS.Equiv ⟨m₂.X, σ.trans m₂.marking, hσ⟩ m₁ := by
  sorry

/-- §32.3 (remark): for `m ≠ 0` the dimension `6g - 6 + 2n + 3m` of `T_{g,n,m}` can be odd, so
`T_{g,n,m}` cannot be a complex manifold in general (e.g. type `(0, 0, 3)` has dimension `3`). -/
theorem teichSpaceFiniteType_odd_dimension : Odd (6 * 0 - 6 + 2 * 0 + 3 * 3 : ℤ) := by
  decide

end LiZhongQC
