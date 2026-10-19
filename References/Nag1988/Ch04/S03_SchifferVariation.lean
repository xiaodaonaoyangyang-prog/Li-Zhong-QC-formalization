import References.Nag1988.Ch04.S01_PeriodMap
import References.Nag1988.Ch04.S02_QuasiconformalDeformations

/-!
# Nag, Chapter 4 §4.3: Schiffer variation parameters as coordinates for Teichmüller space

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 4 §4.3 (`full.md` N2:3300–3590,
folder
`The Complex Analytic Theory … c10f6cd1`; cited `N2:<line>`). New items only.

**Model.** The surface is `X₀ = U/G`, `G = Γ` a Fuchsian group in `SL(2, ℝ)`, and `T(X₀) = T(G)` is
`LiZhongQC.TeichGamma Γ`
read through the Bers embedding (no manifold instance is put on it): "holomorphic" means `Nag1988.IsBHolOn` for the cusp
norm of `bersFunctionGamma`. A *parametric unit disk* on `X₀` is a disk `D = t⁻¹(Δ)` lifted to `ℍ` for a holomorphic
local
parameter `t` (injective on an open set `W ⊆ ℍ` with `t(W) ⊇ D(0, r)`, `r > 1`), `ParamDisk`. The Schiffer variation
`t* = t + ε/t` on `∂D` is the quasiconformal deformation with the Beltrami coefficient `ε dt̄/dt` on `D` (3.4)–(3.5),
extended
by `G`-automorphy to all of `ℍ`: `IsSchifferForm` (Nag proves in 4.3.4 that `X*_ε = Φ(Σ ε_k μ_k)` for these forms,
which is
how the map `S` is defined here). [CORRECTION, Nag-fix1] The Schiffer forms `m_k` have `|m_k| = 1` on the disks, so they are `Γ`-compatible bounded coefficients with
`‖m_k‖_∞ ≤ 1` (`IsSchifferForm`), not elements of the open unit ball `BeltramiGamma Γ`; the parameters `ε` range over the open unit
ball of the sup norm (`polydisc`). The disks have disjoint closures and disjoint `G`-orbits (`IsDisjointSystem`). The
holomorphic parameters live in the polydisc of `ℂⁿ` or of `ℓ^∞` with the sup norm `supNorm`. Nag's pairing
`⟨ψ, μ⟩ = ∬ ψ μ dz ∧ dz̄` is `−2i` times the pairing with `dx dy` of `LiZhongQC.beltramiPairing`; the mean value
theorem gives
`∬_{|t| ≤ 1} ψ_k(t) dt ∧ dt̄ = −2iπ ψ_k(0)`, i.e. `π ψ_k(0)` for `dx dy`.

* Definition (parametric unit disk, disjoint system, Schiffer form, the polydisc) — `ParamDisk`, `ParamDisk.D`,
  `IsDisjointSystem`, `IsSchifferForm`, `supNorm`, `polydisc`
* Theorem 4.3.2 (the Schiffer variation map `S : (ε_1, …, ε_n) ↦ X*_ε` is holomorphic from a neighbourhood of zero in
  `ℂⁿ`
  into `T(X₀)`) — `thm4_3_2`
* Theorem 4.3.2 A (for `T(X₀)` of finite dimension `d`, any `d` points can be moved inside arbitrarily small
  neighbourhoods
  so that the variation parameters are holomorphic coordinates) — `IsSchifferCoordinates`, `thm4_3_2_A`
* Theorem 4.3.2 C (the parameters of disks centred at `p_1, …, p_d` are coordinates iff every integrable holomorphic
  quadratic differential vanishing at every `p_k` vanishes identically) — `thm4_3_2_C`
* Theorem 4.3.2 B (prescribed disk boundaries, suitable local parameters) — deferred: needs the parametrization of
  the disks
  by Riemann maps `D_k → Δ` with prescribed boundary `β_k` and the change of the parameters by disc automorphisms
* Theorem 4.3.3 (the Schiffer variation map `S^#` into the reduced Teichmüller space `T^#(X₀) ↪ T(X̂₀)` of the double
  is real
  analytic, with the real-part coordinates A, B, C) — deferred: it needs the double `X̂₀` and the reduced Teichmüller
  space of
  a bordered surface (the group version of `T^#` of `Nag1988.Ch02` is for groups without ideal boundary)
* 4.3.4 Claim (the functionals `l_a(ψ) = ψ(a)`, `a ∈ N`, span `A₂(X₀)*`) — `claim4_3_4`
* 4.3.4 (3.8) (the pairing of a Schiffer form with a quadratic differential: `π ψ_k(0)`) — `lemma4_3_4_pairing`
* 4.3.5 (3.11) (the variation of the periods under a Schiffer variation: `−2iπ ε φ_i(0) φ_j(0)`) — `prop4_3_5`
* 4.3.5 (3.12) (the variation of the puncture coordinates `w^μ(ζ_j)` with the Schiffer parameters) — deferred: needs the
  Poincaré series `θ_j` and the coordinates of `T(g, n)` of §4.2.5
* Theorem 4.3.6 (the derivative `d₀S` of the Schiffer map for countably many disks is the dual of
  `θ : A₂(U, G) → ℓ¹`, `θ(φ) = (∬_{D_j} φ)_j`) — `schifferTheta`, `thm4_3_6_a`
* Theorem 4.3.6 (the Schiffer map `S : ℓ^∞₁ → T(G)` gives local holomorphic coordinates iff `θ` is a Banach space
  isomorphism) — `thm4_3_6_b`
* Examples (universal Teichmüller space), Remarks 1–3 and the Exercises — omitted: example / remark / exercise
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Manifold ContDiff ComplexConjugate Real

noncomputable section

namespace Nag1988

open LiZhongQC GardinerLakic2000 FarkasKra1992

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **A parametric unit disk** (4.3.1, N2:3317), lifted to `ℍ`: a holomorphic local parameter `t`, injective on an open
set `W ⊆ ℍ`, whose image contains a disk of radius `r > 1` about `0`; the disk is `D = {z ∈ W | |t z| < 1}`. -/
structure ParamDisk where
  W : Set ℂ
  t : ℂ → ℂ
  r : ℝ
  hr : 1 < r
  W_open : IsOpen W
  W_sub : W ⊆ upperHalf
  t_hol : DifferentiableOn ℂ t W
  t_inj : InjOn t W
  t_img : Metric.ball (0 : ℂ) r ⊆ t '' W

/-- The open disk `D = t⁻¹(Δ)`. -/
def ParamDisk.D (d : ParamDisk) : Set ℂ := {z | z ∈ d.W ∧ ‖d.t z‖ < 1}

/-- The closed disk `D̄ = {|t| ≤ 1}`. -/
def ParamDisk.Dbar (d : ParamDisk) : Set ℂ := {z | z ∈ d.W ∧ ‖d.t z‖ ≤ 1}

/-- The image `γ z` of `z` by the Möbius transformation of `γ ∈ SL(2, ℝ)`. -/
def mobiusAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)

/-- **A system of disks with disjoint `G`-orbits** (4.3.2): the closures of the disks `D_j`, `γ D_k` are disjoint unless
`j = k` and `γ = ±1`, so that independent variations can be made on the surface `X₀`. -/
def IsDisjointSystem (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) {ι : Type} (d : ι → ParamDisk) : Prop :=
  ∀ j k, ∀ γ ∈ Γ, (j ≠ k ∨ (γ ≠ 1 ∧ γ ≠ -1)) → Disjoint (d j).Dbar (mobiusAct γ '' (d k).Dbar)

/-- **The Schiffer Beltrami form** of a disk (4.3.4, (3.5), (3.7)): the `G`-invariant coefficient `m` equal to
`d t̄/dt = conj t'/t'` on `D` and to `0` outside the `G`-orbit of `D`. [CORRECTION] `m` has `|m| = 1` on `D`, so it is *not* an
element of the open unit ball `BeltramiGamma Γ` (`‖μ‖_∞ < 1`): it is a `Γ`-compatible coefficient on `ℍ` (zero on the closed lower
half-plane) with `‖m‖_∞ ≤ 1`; only the combinations `Σ ε_k m_k` with `‖ε‖_∞ < 1` (disjoint supports) are in `BeltramiGamma Γ`. -/
def IsSchifferForm (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (d : ParamDisk) (m : ℂ → ℂ) : Prop :=
  IsGammaCompatible Γ m ∧ (∀ z : ℂ, z.im ≤ 0 → m z = 0) ∧ IsBeltramiCoeff m univ 1 ∧
    (∀ z ∈ d.D, m z = conj (deriv d.t z) / deriv d.t z) ∧
    ∀ z ∈ upperHalf, (∀ γ ∈ Γ, mobiusAct γ z ∉ d.D) → m z = 0

/-- The sup norm `‖ε‖_∞` of a family of complex parameters (valued in `[0, ∞]`). -/
def supNorm {ι : Type} (ε : ι → ℂ) : ℝ≥0∞ := ⨆ k, ENNReal.ofReal ‖ε k‖

/-- The open unit ball of the parameters `ε` for the sup norm (the polydisc for finite `ι`; for infinite `ι` the ball of `ℓ^∞`,
`sup ‖ε_k‖ < 1`, not the product of the open discs: [CORRECTION]). -/
def polydisc (ι : Type) : Set (ι → ℂ) := {ε | supNorm ε < 1}

/-- **Theorem 4.3.2, holomorphy of `S`** (N2:3305). For independent Schiffer variations in `n` parametric unit disks
with
disjoint `G`-orbits, the Beltrami coefficients `Σ ε_k μ_k` exist on the polydisc (they are `G`-invariant of norm
`max |ε_k| < 1`) and the map `S : ε ↦ X*_ε = Φ(Σ ε_k μ_k)` is holomorphic into `T(X₀)`: its composite with the Bers
embedding is Banach-holomorphic on the polydisc, for every such family of representatives. -/
theorem thm4_3_2 (hΓ : IsFuchsian Γ) {n : ℕ} (d : Fin n → ParamDisk) (hd : IsDisjointSystem Γ d)
    (m : Fin n → ℂ → ℂ) (hm : ∀ k, IsSchifferForm Γ (d k) (m k)) :
    (∃ ν : (Fin n → ℂ) → BeltramiGamma Γ, ∀ ε ∈ polydisc (Fin n),
      ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ∑ k, ε k * m k z) ∧
    ∀ ν : (Fin n → ℂ) → BeltramiGamma Γ, (∀ ε ∈ polydisc (Fin n),
        ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ∑ k, ε k * m k z) →
      IsBHolOn supNorm (cuspNorm lowerHalf) (polydisc (Fin n)) (fun ε => bersFunctionGamma (ν ε)) := by
  sorry

/-- **The parameters `ε` are holomorphic coordinates around the origin** (helper): `S` is a biholomorphism of a
neighbourhood `U` of `0` in `ℂⁿ` (inside the polydisc) onto an open subset `V` of `T_B(Γ) ⊆ B(Γ)`, containing the origin
of `T(G)` (`Ψ(0) = 0`). -/
def IsSchifferCoordinates {n : ℕ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (ν : (Fin n → ℂ) → BeltramiGamma Γ) : Prop :=
  ∃ (U : Set (Fin n → ℂ)) (V : Set (ℂ → ℂ)), IsBOpen supNorm univ U ∧ (0 : Fin n → ℂ) ∈ U ∧ U ⊆ polydisc (Fin n) ∧
    IsBOpen (cuspNorm lowerHalf) (bersImage Γ) V ∧
    IsBBiholOn supNorm (cuspNorm lowerHalf) U V (fun ε => bersFunctionGamma (ν ε))

/-- **Theorem 4.3.2 A** (N2:3320). Let `T(X₀)` have finite dimension `d` (`dim B(Γ) = d`, with `B(Γ)` the span of the bounded cusp forms `cuspFormsL Γ`, not `automorphicQD`,
which has no growth condition at the cusps). Given any `d` points `p_k
∈ ℍ` and
neighbourhoods `N_k` of them, one can choose parametric unit disks with centres `q_k ∈ N_k`, disjoint `G`-orbits,
Schiffer
forms `m_k` and a family `ν_ε = Σ ε_k m_k`, such that the variation parameters `(ε_1, …, ε_d)` are holomorphic
coordinates
for `T(X₀)` around the origin. -/
theorem thm4_3_2_A (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ) {d : ℕ} (hd : Module.finrank ℂ (Submodule.span ℂ (cuspFormsL Γ)) = d)
    (hfin : Module.Finite ℂ (Submodule.span ℂ (cuspFormsL Γ))) (p : Fin d → ℂ) (hp : ∀ k, p k ∈ upperHalf)
    (N : Fin d → Set ℂ) (hN : ∀ k, IsOpen (N k) ∧ p k ∈ N k) :
    ∃ (dk : Fin d → ParamDisk) (m : Fin d → ℂ → ℂ) (ν : (Fin d → ℂ) → BeltramiGamma Γ),
      (∀ k, ∃ q ∈ N k, q ∈ (dk k).W ∧ (dk k).t q = 0) ∧ IsDisjointSystem Γ dk ∧ (∀ k, IsSchifferForm Γ (dk k) (m k)) ∧
      (∀ ε ∈ polydisc (Fin d), ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ∑ k, ε k * m k z) ∧
      IsSchifferCoordinates Γ ν := by
  sorry

/-- **Theorem 4.3.2 C** (N2:3330). For parametric unit disks centred at `p_1, …, p_d` (disjoint `G`-orbits, Schiffer
forms
`m_k`, the family `ν_ε = Σ ε_k m_k`), the variation parameters are local coordinates if and only if any integrable
holomorphic
quadratic differential `ψ ∈ A₂(X₀)` (over a fundamental domain `F`) that vanishes at every `p_k` vanishes
identically. -/
theorem thm4_3_2_C (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ) {d : ℕ} (hd : Module.finrank ℂ (Submodule.span ℂ (cuspFormsL Γ)) = d)
    (hfin : Module.Finite ℂ (Submodule.span ℂ (cuspFormsL Γ))) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (dk : Fin d → ParamDisk) (hdisj : IsDisjointSystem Γ dk) (m : Fin d → ℂ → ℂ)
    (hm : ∀ k, IsSchifferForm Γ (dk k) (m k)) (c : Fin d → ℂ) (hc : ∀ k, c k ∈ (dk k).W ∧ (dk k).t (c k) = 0)
    (ν : (Fin d → ℂ) → BeltramiGamma Γ)
    (hν : ∀ ε ∈ polydisc (Fin d), ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ∑ k, ε k * m k z) :
    IsSchifferCoordinates Γ ν ↔
      ∀ ψ ∈ integrableAutomorphicQD Γ F, (∀ k, ψ (c k) = 0) → ∀ z ∈ upperHalf, ψ z = 0 := by
  sorry

/-- **4.3.4 Claim** (N2:3355). For a nonempty open set `N ⊆ ℍ` (a neighbourhood of the centre of a disk), the
functionals
`l_a(ψ) = ψ(a)`, `a ∈ N`, span the dual of the finite dimensional space `A₂(X₀)` of integrable holomorphic quadratic
differentials: every linear functional `ℓ` on `A₂` is a finite combination of evaluations at points of `N`.
[CORRECTION] `integrableAutomorphicQD` constrains `ψ` on `ℍ` only, so `ℓ` is required to depend only on `ψ|ℍ` (`hℍ`); without it
`ℓ ψ = ψ(−i)` is a counterexample. -/
theorem claim4_3_4 (hΓ : IsFuchsian Γ) (hfk : IsFGFirstKind Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (hfin : Module.Finite ℂ (Submodule.span ℂ (cuspFormsL Γ))) {N : Set ℂ} (hN : IsOpen N) (hNne : N.Nonempty) (hNU : N ⊆ upperHalf)
    {ℓ : (ℂ → ℂ) → ℂ}
    (hℍ : ∀ ψ ∈ integrableAutomorphicQD Γ F, ∀ ψ' ∈ integrableAutomorphicQD Γ F, Set.EqOn ψ ψ' upperHalf → ℓ ψ = ℓ ψ')
    (hadd : ∀ ψ ∈ integrableAutomorphicQD Γ F, ∀ ψ' ∈ integrableAutomorphicQD Γ F, ℓ (ψ + ψ') = ℓ ψ + ℓ ψ')
    (hsmul : ∀ ψ ∈ integrableAutomorphicQD Γ F, ∀ c : ℂ, ℓ (c • ψ) = c * ℓ ψ) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), (↑s ⊆ N) ∧ ∀ ψ ∈ integrableAutomorphicQD Γ F, ℓ ψ = ∑ a ∈ s, c a * ψ a := by
  sorry

/-- **(3.8)** (N2:3410). For a Schiffer form `m` of a parametric unit disk `D ⊆ F` with centre `c` (`t(c) = 0`) and an
integrable automorphic quadratic differential `ψ`, `⟨ψ, m⟩ = ∬_D ψ conj t'/t' dx dy = π ψ(c)/t'(c)²` (the coefficient
of `ψ`
in the parameter `t` at `0` times `π`; Nag's `dz ∧ dz̄` pairing is `−2i` times this). -/
theorem lemma4_3_4_pairing (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (d : ParamDisk)
    (hDF : d.D ⊆ F) {m : ℂ → ℂ} (hm : IsSchifferForm Γ d m) {c : ℂ} (hc : c ∈ d.W ∧ d.t c = 0)
    {ψ : ℂ → ℂ} (hψ : ψ ∈ integrableAutomorphicQD Γ F) :
    beltramiPairing F m ψ = π * ψ c / (deriv d.t c) ^ 2 := by
  sorry

/-- **4.3.5 (3.11), variation of the periods** (N2:3467). Let `X₀ = ℍ/Γ` be a compact surface of genus `g ≥ 2` with a
canonical
homology basis, `ζ` the normalized basis of holomorphic 1-forms with lifts `f_i`, and `D` a parametric unit disk in a
fundamental domain with centre `c` and parameter `t`. For the Schiffer variation of the single disk, the period
`π_ij(X*_ε) − π_ij(X₀) = −2iπ ε φ_i(0) φ_j(0) + O(ε²)`, where `φ_i(0)` is the coefficient of `φ_i` in the parameter
`t` at
`0`, i.e. `f_i(c)/t'(c)`: the derivative at `ε = 0` of `ε ↦ π_ij(ν_ε)` is `−2iπ f_i(c) f_j(c)/t'(c)²`. -/
theorem prop4_3_5 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {x₀ : S} {g : ℕ} (hS : HasGenus S g) (hg : 2 ≤ g)
    {p : UpperHalfPlane → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {a b : Fin g → Abelianization (FundamentalGroup S x₀)} (hab : IsCanonicalHomologyBasis a b) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {ζ : Fin g → Forster1981.Form1 S} (hζ : IsNormalizedBasis a ζ) {f : Fin g → ℂ → ℂ}
    (hf : ∀ i, IsFormLift p (ζ i) (f i)) (d : ParamDisk) (hDF : d.D ⊆ F) {m : ℂ → ℂ}
    (hm : IsSchifferForm Γ d m) {c : ℂ} (hc : c ∈ d.W ∧ d.t c = 0) (ν : ℂ → BeltramiGamma Γ)
    (hν : ∀ ε ∈ Metric.ball (0 : ℂ) 1, ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ε * m z) (i j : Fin g) :
    HasDerivAt (fun ε => periodMatrix p a b (ν ε) i j)
      ((-2 * π * Complex.I) * (f i c * f j c / (deriv d.t c) ^ 2)) 0 := by
  sorry

/-- **The map `θ : A₂(U, G) → ℓ¹`** (4.3.6, (3.16)): `θ(φ)_k = ∬_{D_k} φ` in the parameter `t_k`; with `dx dy` it is
`π φ(c_k)/t_k'(c_k)²` (the centres `c_k`; Nag's factor `−2i` of `dt ∧ dt̄` is dropped consistently with
`lemma4_3_4_pairing`). -/
def schifferTheta (d : ℕ → ParamDisk) (c : ℕ → ℂ) (ψ : ℂ → ℂ) : ℕ → ℂ :=
  fun k => π * ψ (c k) / (deriv (d k).t (c k)) ^ 2

/-- **Theorem 4.3.6 (the derivative of `S` is the dual of `θ`)** (N2:3540, (3.15)–(3.16)). For countably many parametric
unit disks inside a fundamental domain `F` of an arbitrary Fuchsian group, with disjoint `G`-orbits and Schiffer
forms `m_k`,
and every bounded sequence `c = (c_k)` and `ψ ∈ A₂(U, G)`: `⟨ψ, Σ c_k μ_k⟩ = Σ c_k θ(ψ)_k` (so that `d₀S(c) = Σ c_k
μ_k` is
`θ*` under `T_{[0]}T(G) = L^∞(U, G)/A₂(U, G)^⊥`). -/
theorem thm4_3_6_a (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (d : ℕ → ParamDisk)
    (hd : IsDisjointSystem Γ d) (hDF : ∀ k, (d k).D ⊆ F) (m : ℕ → ℂ → ℂ)
    (hm : ∀ k, IsSchifferForm Γ (d k) (m k)) (cen : ℕ → ℂ) (hcen : ∀ k, cen k ∈ (d k).W ∧ (d k).t (cen k) = 0)
    (μ : BeltramiGamma Γ) (e : ℕ → ℂ) (he : ∃ C : ℝ, ∀ k, ‖e k‖ ≤ C)
    (hμ : ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = ∑' k, e k * m k z)
    {ψ : ℂ → ℂ} (hψ : ψ ∈ integrableAutomorphicQD Γ F) :
    beltramiPairing F μ.1.1 ψ = ∑' k, e k * schifferTheta d cen ψ k := by
  sorry

/-- **Theorem 4.3.6 (coordinates iff `θ` is a Banach space isomorphism)** (N2:3540). With countably many disks as
above, the
Schiffer map `S : ℓ^∞₁ → T(G)`, `ε ↦ Φ(Σ ε_k μ_k)`, gives local holomorphic coordinates around the origin (a
biholomorphism of
a neighbourhood of `0` in `ℓ^∞` onto an open set of `T_B(Γ)`) if and only if `θ : A₂(U, G) → ℓ¹` is a Banach space
isomorphism: bijective, bounded, with bounded inverse (`‖ψ‖₁ ≤ C ‖θ(ψ)‖_{ℓ¹}`). -/
theorem thm4_3_6_b (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (d : ℕ → ParamDisk)
    (hd : IsDisjointSystem Γ d) (hDF : ∀ k, (d k).D ⊆ F) (m : ℕ → ℂ → ℂ)
    (hm : ∀ k, IsSchifferForm Γ (d k) (m k)) (cen : ℕ → ℂ) (hcen : ∀ k, cen k ∈ (d k).W ∧ (d k).t (cen k) = 0)
    (ν : (ℕ → ℂ) → BeltramiGamma Γ)
    (hν : ∀ ε ∈ polydisc ℕ, ∀ᵐ z ∂(volume.restrict upperHalf), (ν ε).1.1 z = ∑' k, ε k * m k z) :
    (∃ (U : Set (ℕ → ℂ)) (V : Set (ℂ → ℂ)), IsBOpen supNorm univ U ∧ (0 : ℕ → ℂ) ∈ U ∧ U ⊆ polydisc ℕ ∧
      IsBOpen (cuspNorm lowerHalf) (bersImage Γ) V ∧
      IsBBiholOn supNorm (cuspNorm lowerHalf) U V (fun ε => bersFunctionGamma (ν ε))) ↔
    ((∀ s : ℕ → ℂ, Summable (fun k => ‖s k‖) → ∃ ψ ∈ integrableAutomorphicQD Γ F, schifferTheta d cen ψ = s) ∧
      (∀ ψ ∈ integrableAutomorphicQD Γ F, Summable (fun k => ‖schifferTheta d cen ψ k‖)) ∧
      ∃ C : ℝ, ∀ ψ ∈ integrableAutomorphicQD Γ F,
        phiArea ψ F ≤ ENNReal.ofReal C * ENNReal.ofReal (∑' k, ‖schifferTheta d cen ψ k‖)) := by
  sorry

end Nag1988
