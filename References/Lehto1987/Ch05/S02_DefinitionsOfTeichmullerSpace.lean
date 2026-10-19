import References.Lehto1987.Ch05.S01_QuasiconformalMappingsOfRiemannSurfaces

/-!
# Lehto, Chapter V §2: Definitions of Teichmüller space

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §2 (`full.md`
P1:6107–6282).

Conventions (see §1; decision B0.5). The Teichmüller space of a surface `S` with the disc as universal covering
surface is Gardiner–Lakic's `GardinerLakic2000.TeichSpace S p`. It is taken for a uniformization `p : ℍ → S`, and it is
the quotient of the Beltrami coefficients `GardinerLakic2000.beltramiBall S` by Teichmüller equivalence:
- `GardinerLakic2000.IsTeichEquiv` is homotopy (modulo the boundary, through lifts fixing `ℝ̂`) to a conformal
  mapping, which is Lehto's definition for covering groups of both kinds (Theorems 1.2, 1.4);
- its distance (2.1) is `GardinerLakic2000.teichDist`;
- the origin is the class of the zero coefficient; statements about it carry the hypothesis `0 ∈ beltramiBall S`, as
  Gardiner–Lakic do;
- the torus (plane as universal covering surface) is treated in §6.

Conformal structures on `S` are conformal atlases `A : Set (OpenPartialHomeomorph S ℂ)` (`IsConformalAtlas`, §1); a
homeomorphism `f` is conformal from `(S, A)` to `(S, A′)` when its expressions in the charts are holomorphic
(`IsConformalBetween`).

- **Known gap** (audit AUDIT2_Lehto, left as documented). `para5_2_3` states `τ(p_t, 0) = t τ(p, 0)` only; the book's full geodesic
  property `τ(p_s, p_t) = |s − t| τ(p, 0)` needs the family `t ↦ μ_t` as one object and is not stated.

* Definition (the Riemann space `R_S`, §2.1) — exists: `GardinerLakic2000.qcModuliSpace` (the classes of the
  surfaces quasiconformally equivalent to S under conformal equivalence)
* Unlabelled (§2.1, P1:6115): `R_H` is a single point — omitted: U−, not cited
* Definition (Teichmüller equivalence, the Teichmüller space `T_S`, §2.1) — exists: `GardinerLakic2000.IsTeichEquiv`,
  `GardinerLakic2000.teichRel`, `GardinerLakic2000.TeichSpace` (surfaces covered by the disc)
* Unlabelled (§2.1, P1:6123): `T_H` is the universal Teichmüller space — `para5_2_1`
* Definition (reduced Teichmüller space, §2.1) — omitted: not used in any statement
* Formula (2.1) (§2.2) — exists: `GardinerLakic2000.teichDist`
* Theorem 2.1 (§2.2) — exists: `GardinerLakic2000.para2_4_extremal_exists` (every class has an extremal
  representative)
* Formula (2.2) (§2.2) — `eq5_2_2`
* Unlabelled (§2.2, P1:6155): `(T_S, τ)` is a metric space — exists: `GardinerLakic2000.para2_4_dist_eq_zero` (the
  non-trivial axiom; symmetry and the triangle inequality are immediate)
* Definition (the origin of `T_S`, §2.2) — omitted: the class of the zero coefficient, written inline (U−)
* Definition (equivalent Beltrami differentials, §2.3) — exists: `GardinerLakic2000.teichRel`
* Formula (2.3) (§2.3) — `eq5_2_3`
* Formula (2.4) (§2.3) — `para5_2_3`
* Unlabelled (§2.3, P1:6167–6175): `μ_t` is extremal for `[μ_t]`, and `τ(p_t, 0) = t τ(p, 0)` — `para5_2_3`
* Theorem 2.2 (§2.3) — `thm5_2_2`
* Definition (the structure `f_*(H)`, §2.4) — `IsConformalBetween` (f is conformal from (S, H) to (S, f_*(H)))
* Unlabelled (§2.4, P1:6187): `f_*(H)` does not depend on the atlas; `H′ = f_*(H)` when `f` is conformal — omitted:
  U−
* Definition (deformation equivalent structures, §2.4) — `AreDeformationEquivalent`
* Formula (2.5) (§2.4) — `eq5_2_5`
* Theorem 2.3 (§2.4) — `thm5_2_3`
* Theorem 2.4 (§2.5) — `thm5_2_4`
* Theorem 2.5 (§2.5) — `thm5_2_5`
* Unlabelled (§2.5, P1:6227–6233): `T_S ≃ 𝓗(S)/Homeo₀(S)` — omitted: a restatement of Theorem 2.5
* Theorem 2.6 (§2.6) — exists: `GardinerLakic2000.para2_4_geometric_isometry`
* Formula (2.6) (§2.6) — exists: `GardinerLakic2000.IsGeometricIsomorphism`
* Unlabelled (§2.6, P1:6255): compact surfaces of the same genus have isometric Teichmüller spaces — `para5_2_6`
* Definition (the modular group `Mod(S)`, §2.7) — `modularGroup`
* Unlabelled (§2.7, P1:6265–6269): `Qc(S)/Qc₀(S) → Mod(S)` — omitted: not cited
* Theorem 2.7 (§2.7) — `thm5_2_7`
* Unlabelled (§2.7, P1:6281): `T_S` is a point for the sphere minus three points — `para5_2_7`

Helper (not a book notion): `IsInducedSensePreserving` (the identity of `(S, H)` onto `(S, c)` is sense-preserving).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsQCRS IsUniformization IsFuchsian ActsFreely HomotopicModBoundary HasGenus RSConformallyEquivalent
  maxDilatationRS UniversalTeichmuller)
open GardinerLakic2000 (RSBundle beltramiBall beltramiNormRS HasBeltramiCoeff IsTeichEquiv teichRel TeichSpace
  IsGeometricIsomorphism)

/-! ## §2.1 Riemann space and Teichmüller space -/

/-- **Unlabelled** (Ch. V §2.1, P1:6123). If `S = H`, the Teichmüller space `T_S` agrees with the universal
Teichmüller space: equivalence reduces to equality of `f^μ` on the real axis.
Modelling: `ℍ` uniformized by the identity (`Γ` trivial); a bijection `T_ℍ → T` sending the class of a coefficient to
the class of the same coefficient on the plane (`μ` read through the single chart of `ℍ`, extended by `0`).
**Correction** (Lehto-fix1, audit AUDIT2_Lehto finding 1): an element of `beltramiBall ℍ` obeys the transformation law only
almost everywhere, so each slice `μ x` is defined up to a null set; the earlier diagonal read `ν z = μ (ofComplex z) z` was not
well defined (e.g. `μ x z := if z = ↑x then ν₀ z else 0`, with `ν₀` the Beurling–Ahlfors dilatation of `x ↦ x` (`x < 0`), `x ↦ 2x` (`x > 0`), has all
slices `0` a.e., so `[μ] = [0]`, but its diagonal is the non-trivial `ν₀`; the constant `1/2` would not do, `x + iy/3` fixes `ℝ`). The coefficient `ν` is now required to agree almost everywhere on `ℍ` with the slice `μ x` for every `x`. -/
theorem para5_2_1 :
    ∃ Φ : TeichSpace ℍ id → UniversalTeichmuller, Function.Bijective Φ ∧
      ∀ (μ : beltramiBall ℍ) (ν : LiZhongQC.BeltramiH),
        (∀ x : ℍ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf), ν.1 z = μ.1 x z) →
        Φ (Quot.mk (teichRel id) μ) = Quotient.mk LiZhongQC.teichSetoid ν := by
  sorry

/-! ## §2.2 Teichmüller metric -/

/-- **Formula (2.2)** (Ch. V §2.2). For fixed `f₀ ∈ p`, `g₀ ∈ q`, let `F` be the class of quasiconformal mappings of
`f₀(S)` onto `g₀(S)` homotopic to `g₀ ∘ f₀⁻¹`. Then `τ(p, q) = ½ inf {log K_f | f ∈ F}`.
Modelling: "homotopic to `g₀ ∘ f₀⁻¹`" up to the conformal mappings allowed by Teichmüller equivalence
(`f ∘ f₀` Teichmüller equivalent to `g₀`), which does not change the infimum. -/
theorem eq5_2_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {μ ν : beltramiBall S} {Y₀ Y₁ : RSBundle.{u}} {f₀ : S ≃ₜ Y₀.carrier}
    {g₀ : S ≃ₜ Y₁.carrier} (hf₀ : IsQCRS f₀) (hg₀ : IsQCRS g₀) (hμ : HasBeltramiCoeff f₀ μ.1)
    (hν : HasBeltramiCoeff g₀ ν.1) :
    GardinerLakic2000.teichDist p (Quot.mk (teichRel p) μ) (Quot.mk (teichRel p) ν) =
      (1 / 2) * sInf {d | ∃ f : Y₀.carrier ≃ₜ Y₁.carrier, IsQCRS f ∧ IsTeichEquiv p (f₀.trans f) g₀ ∧
        d = Real.log (maxDilatationRS f).toReal} := by
  sorry

/-! ## §2.3 Teichmüller space and Beltrami differentials -/

/-- **Formula (2.3)** (Ch. V §2.3).
`τ(p, q) = ½ inf {log ((1 + ‖(μ − ν)/(1 − μ̄ν)‖∞)/(1 − ‖(μ − ν)/(1 − μ̄ν)‖∞)) | μ ∈ p, ν ∈ q}`.
Modelling: the quotient is formed chartwise; `‖·‖∞` is `GardinerLakic2000.beltramiNormRS`. -/
theorem eq5_2_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) (P Q : TeichSpace S p) :
    GardinerLakic2000.teichDist p P Q = (1 / 2) * sInf {d | ∃ μ ν : beltramiBall S, Quot.mk (teichRel p) μ = P ∧
      Quot.mk (teichRel p) ν = Q ∧
      d = Real.log ((1 + (beltramiNormRS fun x z => (μ.1 x z - ν.1 x z) / (1 - conj (μ.1 x z) * ν.1 x z)).toReal) /
        (1 - (beltramiNormRS fun x z => (μ.1 x z - ν.1 x z) / (1 - conj (μ.1 x z) * ν.1 x z)).toReal))} := by
  sorry

/-- **Formula (2.4)** (Ch. V §2.3) and its properties. If `μ` is an extremal complex dilatation for `p ∈ T_S`, then
`μ_t = ((1 + |μ|)^t − (1 − |μ|)^t)/((1 + |μ|)^t + (1 − |μ|)^t) · μ/|μ|`, `0 ≤ t ≤ 1`, is a Beltrami differential which
is extremal for `p_t = [μ_t]`, and `τ(p_t, 0) = t τ(p, 0)`: `t ↦ p_t` is a geodesic from `0` to `p`.
Modelling: extremal: `‖μ‖∞` is minimal in its class; `μ_t` chartwise (`0` where `μ = 0`); `μ_t ∈ B` is part of the
conclusion. [misprint, root Corrections] The book's "from 0 to `p_t`" is read "from 0 to `p`". -/
theorem para5_2_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) (h0 : (0 : S → ℂ → ℂ) ∈ beltramiBall S) {μ : beltramiBall S}
    (hext : ∀ ν : beltramiBall S, Quot.mk (teichRel p) ν = Quot.mk (teichRel p) μ →
      beltramiNormRS μ.1 ≤ beltramiNormRS ν.1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ μt : beltramiBall S,
      (∀ x z, μt.1 x z = ((((1 + ‖μ.1 x z‖) ^ t - (1 - ‖μ.1 x z‖) ^ t) /
        ((1 + ‖μ.1 x z‖) ^ t + (1 - ‖μ.1 x z‖) ^ t) : ℝ) : ℂ) * (μ.1 x z / (‖μ.1 x z‖ : ℂ))) ∧
      (∀ ν : beltramiBall S, Quot.mk (teichRel p) ν = Quot.mk (teichRel p) μt →
        beltramiNormRS μt.1 ≤ beltramiNormRS ν.1) ∧
      GardinerLakic2000.teichDist p (Quot.mk (teichRel p) μt) (Quot.mk (teichRel p) ⟨0, h0⟩) =
        t * GardinerLakic2000.teichDist p (Quot.mk (teichRel p) μ) (Quot.mk (teichRel p) ⟨0, h0⟩) := by
  sorry

/-- **Theorem 2.2** (Ch. V §2.3). The Teichmüller space `T_S` is pathwise connected.
Modelling: `T_S` has no topology instance; a path from the origin to `P` continuous for `τ` (`ε–δ`). -/
theorem thm5_2_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) (h0 : (0 : S → ℂ → ℂ) ∈ beltramiBall S) (P : TeichSpace S p) :
    ∃ γ : ℝ → TeichSpace S p, γ 0 = Quot.mk (teichRel p) ⟨0, h0⟩ ∧ γ 1 = P ∧
      ∀ t₀ ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ →
        GardinerLakic2000.teichDist p (γ t) (γ t₀) < ε := by
  sorry

/-! ## §2.4 Teichmüller space and conformal structures -/

/-- **Definition** (the structure `f_*(H)`, Ch. V §2.4). For conformal structures (atlases) `A`, `A′` of `S` and a
homeomorphism `f`, `f` is conformal from `(S, A)` onto `(S, A′)`: its expressions in the charts are holomorphic. By
the book's remark, `A′` is `f_*(A)` (up to the maximal atlas) exactly when this holds. -/
def IsConformalBetween {S : Type u} [TopologicalSpace S] (A A' : Set (OpenPartialHomeomorph S ℂ)) (f : S ≃ₜ S) :
    Prop :=
  ∀ e ∈ A, ∀ e' ∈ A', DifferentiableOn ℂ (fun z => e' (f (e.symm z))) (e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source))

/-- **Definition** (deformation equivalent structures, Ch. V §2.4): there is a conformal mapping of `(S, A)` onto
`(S, A′)` homotopic to the identity.
Modelling: homotopy modulo the boundary for a uniformization `p` (decision B0.6). -/
def AreDeformationEquivalent {S : Type u} [TopologicalSpace S] (p : ℍ → S) (A A' : Set (OpenPartialHomeomorph S ℂ)) :
    Prop :=
  ∃ f : S ≃ₜ S, IsConformalBetween A A' f ∧ HomotopicModBoundary p p f id

/-- **Formula (2.5)** (Ch. V §2.4). If `f : (S, H) → (S, H′)` is quasiconformal with complex dilatation `μ`, then
`H′ = f_*(H_μ)`.
Modelling: `H′` is a conformal atlas `A′` of `S`; `f` is quasiconformal from `(S, H)` to `(S, A′)` with complex
dilatation `μ` (its expressions in the preferred charts of `H` and the charts of `A′`); the conclusion is that `f` is
conformal from `(S, H_μ)` to `(S, A′)`. -/
theorem eq5_2_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {μ : beltramiBall S} {A A' : Set (OpenPartialHomeomorph S ℂ)}
    (hA : IsInducedStructure μ.1 A) (hA' : IsConformalAtlas A') {f : S ≃ₜ S}
    (hqc : ∀ x : S, ∀ e' ∈ A',
      LiZhongQC.IsQuasiconformal (fun w => e' (f ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' e'.source)) ∧
        ∀ᵐ z ∂(volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' e'.source))),
          LiZhongQC.complexDilatation (fun w => e' (f ((chartAt ℂ x).symm w))) z = μ.1 x z) :
    IsConformalBetween A A' f := by
  sorry

/-- **Theorem 2.3** (Ch. V §2.4). The conformal structures `H₁` and `H₂` induced by the Beltrami differentials `μ₁` and
`μ₂` on `S` are deformation equivalent if and only if `μ₁` and `μ₂` determine the same point of `T_S`. -/
theorem thm5_2_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {μ₁ μ₂ : beltramiBall S} {A₁ A₂ : Set (OpenPartialHomeomorph S ℂ)}
    (h₁ : IsInducedStructure μ₁.1 A₁) (h₂ : IsInducedStructure μ₂.1 A₂) :
    AreDeformationEquivalent p A₁ A₂ ↔ Quot.mk (teichRel p) μ₁ = Quot.mk (teichRel p) μ₂ := by
  sorry

/-! ## §2.5 Conformal structures on a compact surface -/

/-- Helper. The identity of `(S, H)` onto `(S, A)` is sense-preserving: the changes of charts are sense-preserving. -/
def IsInducedSensePreserving {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (A : Set (OpenPartialHomeomorph S ℂ)) : Prop :=
  ∀ x : S, ∀ e' ∈ A, LiZhongQC.IsSensePreserving (fun z => e' ((chartAt ℂ x).symm z))
    ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' e'.source)

/-- **Theorem 2.4** (Ch. V §2.5). On a compact Riemann surface `S`, every conformal structure is deformation
equivalent to a structure induced by a Beltrami differential of `S`.
Modelling: the conformal atlases `A` for which the identity of `(S, H)` onto `(S, A)` is sense-preserving (the
standing assumption of §2.5). -/
theorem thm5_2_4 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {A : Set (OpenPartialHomeomorph S ℂ)}
    (hA : IsConformalAtlas A) (hsp : IsInducedSensePreserving A) :
    ∃ (μ : beltramiBall S) (Aμ : Set (OpenPartialHomeomorph S ℂ)), IsInducedStructure μ.1 Aμ ∧
      AreDeformationEquivalent p Aμ A := by
  sorry

/-- **Theorem 2.5** (Ch. V §2.5). The Teichmüller space of a compact Riemann surface is isomorphic to the set of
equivalence classes of conformal structures modulo deformation.
Modelling: a bijection from `T_S` onto the quotient of the sense-preserving conformal atlases by
`AreDeformationEquivalent`, sending `[μ]` to the class of an induced structure `H_μ`. -/
theorem thm5_2_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    ∃ Φ : TeichSpace S p → Quot fun (A A' : {A : Set (OpenPartialHomeomorph S ℂ) // IsConformalAtlas A ∧
        IsInducedSensePreserving A}) => AreDeformationEquivalent p A.1 A'.1,
      Function.Bijective Φ ∧ ∀ (μ : beltramiBall S) (A : {A : Set (OpenPartialHomeomorph S ℂ) //
        IsConformalAtlas A ∧ IsInducedSensePreserving A}), IsInducedStructure μ.1 A.1 →
        Φ (Quot.mk (teichRel p) μ) = Quot.mk _ A := by
  sorry

/-! ## §2.6 Isomorphisms of Teichmüller spaces -/

/-- **Unlabelled** (Ch. V §2.6, P1:6255). Compact Riemann surfaces of the same genus have isometric Teichmüller
spaces. -/
theorem para5_2_6 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {g : ℕ} (hS : HasGenus S g) (hS' : HasGenus S' g) {Γ Γ' : Subgroup SL(2, ℝ)}
    {p : ℍ → S} {p' : ℍ → S'} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hp' : IsUniformization Γ' p') :
    ∃ Φ : TeichSpace S p → TeichSpace S' p', Function.Bijective Φ ∧
      ∀ P Q, GardinerLakic2000.teichDist p' (Φ P) (Φ Q) = GardinerLakic2000.teichDist p P Q := by
  sorry

/-! ## §2.7 Modular group -/

/-- **Definition** (the modular group `Mod(S)`, Ch. V §2.7): the isometries `[f] ↦ [f ∘ h⁻¹]` (2.6) of `T_S` onto
itself, `h` a quasiconformal self-mapping of `S` (near miss: `LiZhongQC.ModAction`, closed surfaces; not
`Katok1992.modularGroup`, the elliptic modular group `PSL(2, ℤ)`). -/
def modularGroup {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p : ℍ → S) :
    Set (TeichSpace S p → TeichSpace S p) :=
  {Φ | ∃ h : S ≃ₜ S, IsQCRS h ∧ IsGeometricIsomorphism h p p Φ}

/-- **Theorem 2.7** (Ch. V §2.7). The Riemann space is the quotient of the Teichmüller space by the modular group:
`[f₁]` and `[f₂]` are equivalent under `Mod(S)` if and only if `f₁(S)` and `f₂(S)` are conformally equivalent.
Modelling: for the classes of coefficients `μ`, `ν` and quasiconformal mappings `f₁`, `f₂` with these coefficients
(near miss: `LiZhongQC.eq28_1_moduli_eq_quotient`). -/
theorem thm5_2_7 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {μ ν : beltramiBall S} {Y₁ Y₂ : RSBundle.{u}} {f₁ : S ≃ₜ Y₁.carrier}
    {f₂ : S ≃ₜ Y₂.carrier} (h₁ : IsQCRS f₁) (h₂ : IsQCRS f₂) (hμ : HasBeltramiCoeff f₁ μ.1)
    (hν : HasBeltramiCoeff f₂ ν.1) :
    (∃ Φ ∈ modularGroup p, Φ (Quot.mk (teichRel p) μ) = Quot.mk (teichRel p) ν) ↔
      RSConformallyEquivalent Y₁.carrier Y₂.carrier := by
  sorry

/-- **Unlabelled** (Ch. V §2.7, P1:6281). If `S` is the sphere minus three points, its Teichmüller space reduces to a
single point.
Modelling: `S = ℂ ∖ {0, 1}` (`LiZhongQC.puncturedOpens`); the cases with fewer punctures are not covered by the disc. -/
theorem para5_2_7 {Γ : Subgroup SL(2, ℝ)} {p : ℍ → LiZhongQC.puncturedOpens ({0, 1} : Finset ℂ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    Subsingleton (TeichSpace (LiZhongQC.puncturedOpens ({0, 1} : Finset ℂ)) p) := by
  sorry

end Lehto1987
