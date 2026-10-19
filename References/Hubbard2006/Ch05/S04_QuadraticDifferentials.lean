import References.Common.HyperbolicSurface
import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Hubbard 2006, Chapter 5 §5.4: Spaces of quadratic differentials (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 1254–1780.

**Conventions.** A hyperbolic surface is `X = ℍ/Γ` for a torsion-free Fuchsian group `Γ ⊂ SL(2, ℝ)` and its
holomorphic quadratic differentials are read on the universal cover (Remark 5.4.7): `Γ`-automorphic holomorphic
functions `φ` on `ℍ`, `φ((a z + b)/(c z + d)) = (c z + d)⁴ φ(z)` (`IsAutomorphicQD`, the installed
`LiZhongQC.integrableAutomorphicQD` is this condition together with integrability). The hyperbolic density is
`ρ = 1/Im z`, so `‖φ‖_∞ = sup |φ(z)| (Im z)²` and `‖φ‖_1 = ∬_F |φ| dx dy` over a fundamental domain `F`
(`LiZhongQC.IsFundamentalDomainH`, `LiZhongQC.phiArea`). The conjugate surface `X*` is `ℍ*/Γ` (lower half plane):
its quadratic differentials are the `Γ`-automorphic holomorphic functions on `ℍ*`, with sup norm `|φ(z)| (Im z)²`. The
pairing of `q ∈ Q(X)` and `p ∈ Q(X*)` is `∬_F q(z) p(z̄) (Im z)² dx dy` (`qdPairing`).

* Def. 5.4.1 (the Banach space `Q¹(X)` of integrable quadratic differentials) — exists:
  `LiZhongQC.integrableAutomorphicQD`, `GardinerLakic2000.integrableHolQDSet`
* Def. 5.4.2 (the Banach space `Q^∞(X)` of bounded quadratic differentials) — `IsAutomorphicQD`, `qdSupNorm`,
  `boundedAutomorphicQD`
* Prop. 5.4.3 (for a surface of finite type, `Q¹ = Q^∞`; finite type is read as finite hyperbolic area) — `prop5_4_3`
* Prop. 5.4.4 (`Q¹(𝔻) ⊂ Q^∞(𝔻)` with `‖q‖_∞ ≤ ‖q‖_1 / (4π)`) — `prop5_4_4`
* Def. 5.4.6 (the conjugate Riemann surface `X*`, with the conjugate charts) — `ConjRS`, `conjRS_isManifold`
* Prop. 5.4.9 (reproducing formula for `Q^∞`) — `prop5_4_9`
* Prop. 5.4.11 (reproducing formula for `Q¹`) — `prop5_4_11`
* Thm 5.4.12 (duality: `Q^∞(X*)` is the dual of `Q¹(X)`) — `qdPairing`, `thm5_4_12_a`, `thm5_4_12_b`, `thm5_4_12_c`
* Def. 5.4.15 (the direct image operator `π_*` of a covering) — `directImage`
* Prop. 5.4.16 (`π_*` is a continuous linear operator `Q¹(Y) → Q¹(X)` of norm `≤ 1`; needs `−1 ∈ Γ_X → −1 ∈ Γ_Y`) —
  `prop5_4_16`
* Prop. 5.4.17 (`π_*` is onto, with `‖φ‖_1 ≤ 3 ‖ψ‖_1`: the image of the unit ball contains the ball of radius `1/3`) —
  `prop5_4_17`
* Example 5.4.5, Remark 5.4.7, Exercise 5.4.8, Lemma 5.4.10, Remark 5.4.13–5.4.14 (restatement), the proofs of the
  reproducing formulas — omitted: example / remark / exercise / proof step
-/

open Set MeasureTheory
open scoped ENNReal Real Manifold ContDiff ComplexConjugate

namespace Hubbard2006

open LiZhongQC

/-- **`Γ`-automorphic holomorphic quadratic differential on an open set `U ⊂ ℂ∖ℝ`** (generalizing
`LiZhongQC.automorphicQD`, which is the case `U = ℍ`) (the half plane `ℍ` or `ℍ*`): a
holomorphic `φ` with `φ(γ z) = (c z + d)⁴ φ(z)` for all `γ = [[a, b], [c, d]] ∈ Γ` and `z ∈ U`. -/
def IsAutomorphicQD (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (U : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ φ U ∧
    ∀ γ ∈ Γ, ∀ z ∈ U, φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z

/-- **The sup norm** `‖φ‖_∞ = sup_{z ∈ U} |φ(z)| (Im z)²` (equation (5.4.5): `|q| / ρ²` with `ρ = 1/|Im z|`), valued in
`[0, ∞]`. -/
noncomputable def qdSupNorm (U : Set ℂ) (φ : ℂ → ℂ) : ℝ≥0∞ := ⨆ z ∈ U, ENNReal.ofReal (‖φ z‖ * z.im ^ 2)

/-- **Bounded quadratic differentials `Q^∞`** (Definition 5.4.2, H2:1296), for the half plane `U` (`ℍ` for `X`, `ℍ*` for
`X*`): the `Γ`-automorphic holomorphic `φ` on `U` with `‖φ‖_∞ < ∞`. -/
def boundedAutomorphicQD (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (U : Set ℂ) : Set (ℂ → ℂ) :=
  {φ | IsAutomorphicQD Γ U φ ∧ qdSupNorm U φ < ⊤}

/-- **Proposition 5.4.3** (H2:1328). For a surface `X = ℍ/Γ` of finite type (finite hyperbolic area
`∬_F dx dy / y² < ∞` for a fundamental domain `F`), `Q¹(X) = Q^∞(X)`. -/
theorem prop5_4_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hfin : ∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2) < ⊤) :
    integrableAutomorphicQD Γ F = boundedAutomorphicQD Γ upperHalf := by
  sorry

/-- **Proposition 5.4.4** (H2:1359). `Q¹(𝔻) ⊂ Q^∞(𝔻)` and `‖q‖_∞ ≤ ‖q‖_1 / (4π)`, where
`‖q‖_∞ = sup_{z ∈ 𝔻} |q(z)| (1 − |z|²)² / 4` and `‖q‖_1 = ∬_𝔻 |q| dx dy`: for a holomorphic `q` on the unit disc,
`sup |q(z)| (1 − |z|²)² / 4 ≤ (1 / 4π) ∬_𝔻 |q|`. -/
theorem prop5_4_4 {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q unitDisc) :
    (⨆ z ∈ unitDisc, ENNReal.ofReal (‖q z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4)) ≤
      ENNReal.ofReal (1 / (4 * π)) * ∫⁻ z in unitDisc, ‖q z‖ₑ := by
  sorry

/-- **The conjugate Riemann surface `X*`** (Definition 5.4.6, H2:1380): the same space with the conjugate charts
`φ̄ = conj ∘ φ` for the local coordinates `φ` of `X`. -/
def ConjRS (X : Type*) : Type _ := X

noncomputable instance (X : Type*) [TopologicalSpace X] : TopologicalSpace (ConjRS X) := ‹TopologicalSpace X›

/-- The conjugation `z ↦ z̄` as a partial homeomorphism of `ℂ`. -/
noncomputable def conjPartialHomeo : OpenPartialHomeomorph ℂ ℂ := Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph

/-- The underlying point of a point of `X*` (the identity). -/
def ConjRS.val {X : Type*} (x : ConjRS X) : X := x

noncomputable instance (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : ChartedSpace ℂ (ConjRS X) where
  atlas := {e | ∃ e' ∈ atlas ℂ X, e = e'.trans conjPartialHomeo}
  chartAt x := (chartAt ℂ x.val).trans conjPartialHomeo
  mem_chart_source x := by
    show x.val ∈ ((chartAt ℂ x.val).trans conjPartialHomeo).source
    simp [conjPartialHomeo]
  chart_mem_atlas x := ⟨chartAt ℂ x.val, chart_mem_atlas ℂ x.val, rfl⟩

/-- **`X*` is a Riemann surface** (Definition 5.4.6): the conjugate charts form a holomorphic atlas. -/
theorem conjRS_isManifold (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    IsManifold 𝓘(ℂ) ω (ConjRS X) := by
  sorry

/-- **Proposition 5.4.9 (Reproducing formula for `Q^∞`)** (H2:1475). Let `q ∈ (Q^∞)^Γ(ℍ*)`. Then for every
`w ∈ ℍ*`, `q(w) = (12/π) ∬_ℍ q(z̄) y² / (z − w)⁴ |dz|²` (`z = x + i y`; the integral converges absolutely). -/
theorem prop5_4_9 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {q : ℂ → ℂ} (hq : q ∈ boundedAutomorphicQD Γ lowerHalf) {w : ℂ} (hw : w ∈ lowerHalf) :
    IntegrableOn (fun z => q (conj z) * z.im ^ 2 / (z - w) ^ 4) upperHalf ∧
      q w = (12 / π) * ∫ z in upperHalf, q (conj z) * z.im ^ 2 / (z - w) ^ 4 := by
  sorry

/-- **Proposition 5.4.11 (Reproducing formula for `Q¹`)** (H2:1563). Let `q ∈ (Q¹)^Γ(ℍ)` (integrable over a fundamental
domain `F`). Then for every `w ∈ ℍ`, `q(w) = (12/π) ∬_{ℍ*} q(z̄) y² / (z − w)⁴ |dz|²` (the integral converges). -/
theorem prop5_4_11 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {q : ℂ → ℂ} (hq : q ∈ integrableAutomorphicQD Γ F) {w : ℂ}
    (hw : w ∈ upperHalf) :
    IntegrableOn (fun z => q (conj z) * z.im ^ 2 / (z - w) ^ 4) lowerHalf ∧
      q w = (12 / π) * ∫ z in lowerHalf, q (conj z) * z.im ^ 2 / (z - w) ^ 4 := by
  sorry

/-- **The pairing** `⟨q, p⟩ = ∫_X q p / ρ²` of `q ∈ Q(X)` and `p ∈ Q(X*)` (equation (5.4.41), H2:1607):
`∬_F q(z) p(z̄) (Im z)² dx dy`. -/
noncomputable def qdPairing (F : Set ℂ) (q p : ℂ → ℂ) : ℂ := ∫ z in F, q z * p (conj z) * z.im ^ 2

/-- **Theorem 5.4.12 (Duality theorem), the pairing is bounded** (H2:1607). For `q ∈ Q¹(X)` and `p ∈ Q^∞(X*)` the
pairing is defined and `|⟨q, p⟩| ≤ ‖q‖_1 ‖p‖_∞`. -/
theorem thm5_4_12_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {q p : ℂ → ℂ} (hq : q ∈ integrableAutomorphicQD Γ F)
    (hp : p ∈ boundedAutomorphicQD Γ lowerHalf) :
    ENNReal.ofReal ‖qdPairing F q p‖ ≤ phiArea q F * qdSupNorm lowerHalf p := by
  sorry

/-- **Theorem 5.4.12, injectivity with bounded inverse** (H2:1607). The map `p ↦ ⟨·, p⟩` from `Q^∞(X*)` to the dual of
`Q¹(X)` is bounded below: there is `c` with `‖p‖_∞ ≤ c · sup { |⟨q, p⟩| : q ∈ Q¹(X), ‖q‖_1 ≤ 1 }`. -/
theorem thm5_4_12_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∃ c : ℝ, ∀ p ∈ boundedAutomorphicQD Γ lowerHalf,
      qdSupNorm lowerHalf p ≤ ENNReal.ofReal c * ⨆ (q : ℂ → ℂ) (_ : q ∈ integrableAutomorphicQD Γ F ∧ phiArea q F ≤ 1),
        ENNReal.ofReal ‖qdPairing F q p‖ := by
  sorry

/-- **Theorem 5.4.12, surjectivity** (H2:1607). Every continuous linear functional `ℓ` on `Q¹(X)` is of the form
`⟨·, p⟩` for some `p ∈ Q^∞(X*)`. Here `ℓ : (ℂ → ℂ) → ℂ` is additive and homogeneous on `Q¹(X)` with
`|ℓ q| ≤ C ‖q‖_1` for `q ∈ Q¹(X)`. -/
theorem thm5_4_12_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {ℓ : (ℂ → ℂ) → ℂ}
    (hadd : ∀ q ∈ integrableAutomorphicQD Γ F, ∀ q' ∈ integrableAutomorphicQD Γ F, ℓ (q + q') = ℓ q + ℓ q')
    (hsmul : ∀ q ∈ integrableAutomorphicQD Γ F, ∀ c : ℂ, ℓ (c • q) = c * ℓ q) {C : ℝ}
    (hbd : ∀ q ∈ integrableAutomorphicQD Γ F, ENNReal.ofReal ‖ℓ q‖ ≤ ENNReal.ofReal C * phiArea q F) :
    ∃ p ∈ boundedAutomorphicQD Γ lowerHalf, ∀ q ∈ integrableAutomorphicQD Γ F, ℓ q = qdPairing F q p := by
  sorry

/-- **The direct image operator** `π_*` of a covering (Definition 5.4.15, H2:1713). Let `Γ_Y ⊂ Γ_X` be torsion-free
Fuchsian groups (so `π : Y = ℍ/Γ_Y → X = ℍ/Γ_X` is a covering). For a `Γ_Y`-automorphic `φ`,
`(π_* φ)(z) = ∑_{γ ∈ Γ_Y∖Γ_X} φ(γ z) · (c z + d)⁻⁴` over right coset representatives (equation (5.4.55): the sum
over the
preimages of the point). *Junk:* the sum is over the quotient by `Quotient.out` and is only meaningful for automorphic
`φ`, for which it does not depend on the representatives. *Warning:* if `−1 ∈ Γ_X` but `−1 ∉ Γ_Y`, the cosets
`Γ_Y γ` and `Γ_Y (−γ)` are distinct and give the same pull-back, so each preimage is counted twice; the statements about
`π_*` therefore assume `−1 ∈ Γ_X → −1 ∈ Γ_Y`. -/
noncomputable def directImage (ΓY ΓX : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' c : Quotient (QuotientGroup.rightRel (ΓY.subgroupOf ΓX)),
    φ ((((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 * z +
        ((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1) /
      (((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 * z +
        ((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1)) /
      ((((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
        ((Quotient.out c : ΓX) : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4

/-- **Proposition 5.4.16** (H2:1725). For a covering `π : Y → X` of hyperbolic surfaces (`Γ_Y ⊂ Γ_X` torsion-free
Fuchsian, fundamental domains `F_Y`, `F_X`, and `−1 ∈ Γ_X → −1 ∈ Γ_Y`, see `directImage`), the direct image operator
`π_*` maps `Q¹(Y)` to `Q¹(X)`, linearly, with `‖π_* φ‖_1 ≤ ‖φ‖_1` (norm `≤ 1`). -/
theorem prop5_4_16 {ΓY ΓX : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hle : ΓY ≤ ΓX) (hX : IsFuchsian ΓX)
    (hXfree : ActsFreely ΓX) (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ ΓX →
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ ΓY)
    {FY FX : Set ℂ} (hFY : IsFundamentalDomainH ΓY FY) (hFX : IsFundamentalDomainH ΓX FX) :
    (∀ φ ∈ integrableAutomorphicQD ΓY FY, directImage ΓY ΓX φ ∈ integrableAutomorphicQD ΓX FX ∧
      phiArea (directImage ΓY ΓX φ) FX ≤ phiArea φ FY) ∧
    (∀ φ ∈ integrableAutomorphicQD ΓY FY, ∀ ψ ∈ integrableAutomorphicQD ΓY FY, ∀ c : ℂ,
      directImage ΓY ΓX (φ + c • ψ) = directImage ΓY ΓX φ + c • directImage ΓY ΓX ψ) := by
  sorry

/-- **Proposition 5.4.17** (H2:1735). Let `X` be a hyperbolic surface and `π : Y → X` a covering (with
`−1 ∈ Γ_X → −1 ∈ Γ_Y`). Then `π_* : Q¹(Y) → Q¹(X)` is surjective with a bounded right inverse: every `ψ ∈ Q¹(X)` is
`π_* φ` for some `φ ∈ Q¹(Y)` with `‖φ‖_1 ≤ 3 ‖ψ‖_1`. *Correction to the book:* the book says the image of the unit
ball contains the ball of radius `3`, which contradicts `‖π_*‖ ≤ 1` (Prop. 5.4.16); the proof gives `‖φ‖_1 ≤ 3 ‖ψ‖_1`,
i.e. the image of the unit ball contains the ball of radius `1/3`. -/
theorem prop5_4_17 {ΓY ΓX : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hle : ΓY ≤ ΓX) (hX : IsFuchsian ΓX)
    (hXfree : ActsFreely ΓX) (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ ΓX →
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ ΓY)
    {FY FX : Set ℂ} (hFY : IsFundamentalDomainH ΓY FY) (hFX : IsFundamentalDomainH ΓX FX) :
    ∀ ψ ∈ integrableAutomorphicQD ΓX FX,
      ∃ φ ∈ integrableAutomorphicQD ΓY FY, directImage ΓY ΓX φ = ψ ∧ phiArea φ FY ≤ 3 * phiArea ψ FX := by
  sorry

end Hubbard2006
