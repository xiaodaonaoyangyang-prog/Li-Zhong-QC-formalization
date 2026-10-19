import References.GardinerLakic2000.Ch04.S06_MainInequalityUniqueness

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.7 The frame mapping theorem

Source `teichmuller.txt`, lines 4112–4191.

* Definition (frame mapping, l. 4123–4129) — `IsFrameMapping`
* Definition (Hamilton sequence (4.24), degenerating Hamilton sequence, l. 4133–4141) — `IsHamiltonSeq`,
  `IsDegHamiltonSeq`
* Theorem 6 (the frame mapping theorem [Str84], l. 4131) — `thm4_6`
* Corollary 1 (Teichmüller's existence theorem, l. 4184) — `cor4_6_1`
* Definition 1 (Strebel point, l. 4190) — `IsStrebelPoint`

Not items (DESIGN §3): (4.25) (the Hamilton–Krushkal theorem, stated as Theorem 6.7) and the other steps of the proof.
Near misses: `LiZhongQC.thm35_8_strebel` (the frame mapping theorem on the disc), `LiZhongQC.IsHamiltonSequence` (on
the disc, with `lim`), `LiZhongQC.thm32_2_existence_gn` and `LiZhongQC.thm27_2_existence` (Teichmüller's existence
theorem for surfaces of type `(g, n)` resp. closed surfaces, without the uniqueness of `k₀` and `φ₀`).

**Conventions.** A frame mapping is recorded through its Beltrami coefficient `μ₁` (a map with this coefficient
exists, Part A's `para2_4_deformation`); `sup_{R − C} K_z(f₁) < K₀` is `ess sup_{R − C} |μ₁| < k₀` (`K_z` is increasing
in `|μ|`). (4.24) is read `limsup Re ∬ μ₀ φₙ = ‖μ₀‖∞` [reading: the book writes the complex integral]. Corollary 1
keeps Part A's standing assumption that `R` has a uniformization by a Fuchsian group (compact tori and the sphere,
where `T(R)` has no ℍ-uniformization, are not covered) [modelling].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS IsFuchsian IsUniformization quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Definition** (frame mapping, §4.7, l. 4123–4129). A representative `μ₁` of the class `P` is (the Beltrami
coefficient of) a frame mapping for `P` if there is a compact set `C ⊆ R` with `ess sup_{R − C} |μ₁| < k₀`, `k₀` the
norm of an extremal representative. -/
def IsFrameMapping (p : UpperHalfPlane → R) (P : TeichSpace R p) (μ₁ : beltramiBall R) : Prop :=
  Quot.mk (teichRel p) μ₁ = P ∧ ∃ C : Set R, IsCompact C ∧
    (⨆ x : R, eLpNorm (μ₁.1 x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ))) <
      ENNReal.ofReal (extremalK p P)

/-- **Definition** ((4.24), §4.7, l. 4133). `φₙ` is a Hamilton sequence for `μ₀`: `φₙ ∈ A(R)`, `‖φₙ‖ = 1`, and
`limsup Re ∬_R μ₀ φₙ = ‖μ₀‖∞`. -/
def IsHamiltonSeq (μ₀ : R → ℂ → ℂ) (φ : ℕ → R → ℂ → ℂ) : Prop :=
  (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) ∧
    limsup (fun n => (pairingRS (φ n) μ₀).re) atTop = (beltramiNormRS μ₀).toReal

/-- **Definition** (§4.7, l. 4141). A degenerating Hamilton sequence: a Hamilton sequence which converges to `0`
uniformly on compact subsets of `R` (Part A's `IsDegeneratingSeq`). -/
def IsDegHamiltonSeq (μ₀ : R → ℂ → ℂ) (φ : ℕ → R → ℂ → ℂ) : Prop :=
  IsHamiltonSeq μ₀ φ ∧ IsDegeneratingSeq φ

/-- **Definition 1** (Strebel point, §4.7, l. 4190). A point `τ ∈ T(R)` whose mapping class has a frame mapping. -/
def IsStrebelPoint (p : UpperHalfPlane → R) (P : TeichSpace R p) : Prop :=
  ∃ μ₁ : beltramiBall R, IsFrameMapping p P μ₁

/-- **Theorem 6** (the frame mapping theorem [Str84], §4.7, l. 4131). If the class `P` has a frame mapping, then it
has an extremal representative `μ₀ = k₀|φ₀|/φ₀`, `φ₀ ∈ A(R)` with `‖φ₀‖ = 1`, `0 ≤ k₀ < 1`. `k₀` is uniquely
determined, and if `0 < k₀ < 1`, `φ₀` is uniquely determined: any representative of Teichmüller form `k|φ|/φ` has
`k = k₀`, and `φ = φ₀` when `k₀ > 0`. -/
theorem thm4_6 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (P : TeichSpace R p) (hP : IsStrebelPoint p P) :
    ∃ (μ₀ : beltramiBall R) (φ₀ : R → ℂ → ℂ) (k₀ : ℝ), Quot.mk (teichRel p) μ₀ = P ∧ IsExtremalRS p μ₀ ∧
      IsTeichmullerForm μ₀.1 φ₀ k₀ ∧
      ∀ (ν : beltramiBall R) (φ : R → ℂ → ℂ) (k : ℝ), Quot.mk (teichRel p) ν = P → IsTeichmullerForm ν.1 φ k →
        k = k₀ ∧ (0 < k₀ → φ = φ₀) := by
  sorry

/-- **[CORRECTION]** (AUDIT4 G8) `A(R) ≠ 0` is added: for `R = ℂ ∖ {0, 1}` (type `(0, 3, 0)`, `A(R) = 0`) there is no `φ₀` of norm 1.
**Corollary 1** (Teichmüller's existence theorem, §4.7, l. 4184). Let `R` be compact or a compact surface with
finitely many points removed, and `f : R → R₁` quasiconformal. Then the Teichmüller class of `f` has a unique
extremal representative `μ₀`; it has the form `k₀|φ₀|/φ₀`, `0 ≤ k₀ < 1`, `‖φ₀‖ = 1`; `k₀` is uniquely determined,
and if `0 < k₀ < 1` so is `φ₀`. Modelling: classes `P ∈ T(R)`; "unique extremal" is: every extremal `ν ∈ P` equals
`μ₀` almost everywhere in every chart. -/
theorem cor4_6_1 {g n : ℕ} (hR : LiZhongQC.IsFiniteType R g n 0) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1)
    (P : TeichSpace R p) :
    ∃ (μ₀ : beltramiBall R) (φ₀ : R → ℂ → ℂ) (k₀ : ℝ), Quot.mk (teichRel p) μ₀ = P ∧ IsExtremalRS p μ₀ ∧
      IsTeichmullerForm μ₀.1 φ₀ k₀ ∧
      (∀ ν : beltramiBall R, Quot.mk (teichRel p) ν = P → IsExtremalRS p ν →
        ∀ x : R, ν.1 x =ᵐ[volume.restrict (chartAt ℂ x).target] μ₀.1 x) ∧
      ∀ (ν : beltramiBall R) (φ : R → ℂ → ℂ) (k : ℝ), Quot.mk (teichRel p) ν = P → IsTeichmullerForm ν.1 φ k →
        k = k₀ ∧ (0 < k₀ → φ = φ₀) := by
  sorry

end GardinerLakic2000
