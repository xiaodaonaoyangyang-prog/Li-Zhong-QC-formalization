import References.Lehto1987.Ch04.S07_GeodesicsOfQuadraticDifferentials

/-!
# Lehto, Chapter V §1: Quasiconformal mappings of Riemann surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §1 (`full.md`
P1:5991–6106).

Conventions of Chapter V (INVENTORY Part B, decisions B0.2, B0.5, B0.6, B0.12; see Ch. IV):
- Quasiconformal mappings of Riemann surfaces are the project's `LiZhongQC.IsKQCRS`, `LiZhongQC.IsQCRS` (homeomorphisms
  `S ≃ₜ S′`).
- Complex dilatations on a surface are `GardinerLakic2000.beltramiCoeffRS` and `GardinerLakic2000.HasBeltramiCoeff`.
  Beltrami differentials are `GardinerLakic2000.beltramiBall` (`LiZhongQC.IsBeltramiDifferential` with `k < 1`).
- A surface with a disc as universal covering surface is uniformized by `ℍ`: `LiZhongQC.IsUniformization Γ p` with
  `LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.ActsFreely Γ`.
- Lifts of maps are `LiZhongQC.IsLift p p′ f F` (`F : ℍ ≃ₜ ℍ`), read in the plane through `LiZhongQC.liftToC`. Their
  homeomorphic extensions to `cl ℍ ⊂ ℂ̄` are `LiZhongQC.IsHomeoExtension`.
- A covering group is non-elementary when its limit set has more than two points.
- Homotopy modulo the boundary is the project's `LiZhongQC.HomotopicModBoundary` (decision B0.6).
- A second conformal structure on `S` is an atlas `A : Set (OpenPartialHomeomorph S ℂ)` (`IsConformalAtlas`), not a
  `ChartedSpace` instance, which would compete with the structure of `S`.

* Definition (`K`-quasiconformal mapping of Riemann surfaces, §1.1) — exists: `LiZhongQC.IsKQCRS`,
  `LiZhongQC.IsQCRS`
* Unlabelled (§1.1, P1:5997): the definition does not depend on the local parameters — omitted: U−
* Definition (complex dilatation of a quasiconformal mapping of Riemann surfaces, §1.1) — exists:
  `GardinerLakic2000.beltramiCoeffRS`, `GardinerLakic2000.HasBeltramiCoeff`
* Formula (1.1) (§1.1) — `eq5_1_1`
* Unlabelled (§1.1, P1:6005–6011): the complex dilatation is a Beltrami differential on the surface — exists:
  `LiZhongQC.eq23_1_beltrami_differential`
* Unlabelled (§1.1, P1:6013–6015): quasiconformally equivalent surfaces have the same universal covering surface —
  omitted: U−
* Theorem 1.1 (§1.1) — exists: `GardinerLakic2000.para2_4_deformation`, `GardinerLakic2000.para2_4_same_coeff`
  (jointly: existence of a quasiconformal map with the given Beltrami coefficient, and uniqueness up to conformal maps)
* Definition (the conformal structure `H_μ` induced by a Beltrami differential, §1.2) — `IsInducedStructure`
* Unlabelled (§1.2, P1:6029): a Beltrami differential defines a conformal structure — `para5_1_2`
* Unlabelled (§1.2, P1:6033): `‖μ‖∞ < 1` on compact subsets suffices — omitted: not cited
* Unlabelled (§1.3, P1:6039): lifts of quasiconformal mappings extend to the boundary and map the limit set of `G`
  onto that of `G′` — `para5_1_3`
* Theorem 1.2 (§1.3) — `thm5_1_2`
* Formula (1.2) (§1.3) — `thm5_1_2` (the common induced isomorphism)
* Theorem 1.3 (§1.3) — `thm5_1_3`
* Unlabelled (§1.4, P1:6071–6081): quasiconformal mappings extend to homeomorphisms of the bordered surfaces —
  `para5_1_4`
* Definition (homotopy modulo the boundary, §1.4) — exists: `LiZhongQC.HomotopicModBoundary` (through lifts constant
  on the real axis, decision B0.6)
* Theorem 1.4 (§1.4) — exists: `LiZhongQC.thm36_1`
* Theorem 1.5 (§1.5, Teichmüller) — exists: `LiZhongQC.exists_qc_in_homotopy_class` (for closed surfaces of a common
  genus, which compact homeomorphic surfaces have)
* Unlabelled (§1.5, P1:6103–6105): Theorem 1.5 fails for general surfaces; real-analytic representatives — omitted:
  remarks (the latter is Theorems 4.5 and 6.3)

Helper (not a book notion): `IsConformalAtlas` (a conformal atlas of `S`, decision B0.9).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (ExtPlane extRealLine IsQCRS IsKQCRS IsUniformization IsFuchsian ActsFreely IsLift liftToC
  IsHomeoExtension upperHalf fuchsianLimitSet ordinarySet IsGammaCompatible complexDilatation IsBiholomorphic)

/-! ## §1.1 Complex dilatation on Riemann surfaces -/

/-- **Formula (1.1)** (Ch. V §1.1). The complex dilatation `μ` of a lift of a quasiconformal mapping `f : S₁ → S₂` to
the universal covering surface satisfies `μ = (μ ∘ g) ḡ′/g′` for every cover transformation `g`.
Modelling: `D = ℍ`, covering groups `Γᵢ ≤ SL(2, ℝ)`; the lift `F` read in the plane (`LiZhongQC.liftToC`); the
relation a.e. in `ℍ` (`LiZhongQC.IsGammaCompatible`). -/
theorem eq5_1_1 {S₁ S₂ : Type u} [TopologicalSpace S₁] [T2Space S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [ConnectedSpace S₂] [ChartedSpace ℂ S₂]
    [IsManifold 𝓘(ℂ) ω S₂] {Γ₁ Γ₂ : Subgroup SL(2, ℝ)} {p₁ : ℍ → S₁} {p₂ : ℍ → S₂} (hΓ₁ : IsFuchsian Γ₁)
    (hfree₁ : ActsFreely Γ₁) (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) {f : S₁ ≃ₜ S₂}
    (hf : IsQCRS f) {F : ℍ ≃ₜ ℍ} (hF : IsLift p₁ p₂ f F) :
    IsGammaCompatible Γ₁ (complexDilatation (liftToC F)) := by
  sorry

/-! ## §1.2 Conformal structures -/

/-- Helper. `A` is a conformal (complex analytic) atlas of `S`: its charts cover `S` and its changes of charts are
holomorphic (decision B0.9; an atlas, not an instance, so that it can coexist with the structure of `S`). -/
def IsConformalAtlas {S : Type u} [TopologicalSpace S] (A : Set (OpenPartialHomeomorph S ℂ)) : Prop :=
  (∀ x : S, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, DifferentiableOn ℂ (fun z => e' (e.symm z)) (e.target ∩ e.symm ⁻¹' e'.source)

/-- **Definition** (the conformal structure `H_μ` induced by a Beltrami differential, Ch. V §1.2): the structure
determined by the quasiconformal mappings of open subsets of `S` into the plane whose complex dilatations are the
restrictions of `μ`.
Modelling: `A` is a conformal atlas (`IsConformalAtlas`) whose charts, read in the preferred charts of `S`, are
quasiconformal with complex dilatation `μ` a.e. -/
def IsInducedStructure {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (μ : S → ℂ → ℂ)
    (A : Set (OpenPartialHomeomorph S ℂ)) : Prop :=
  IsConformalAtlas A ∧ ∀ e ∈ A, ∀ x : S,
    LiZhongQC.IsQuasiconformal (fun w => e ((chartAt ℂ x).symm w))
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' e.source) ∧
      ∀ᵐ z ∂(volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' e.source)),
        complexDilatation (fun w => e ((chartAt ℂ x).symm w)) z = μ x z

/-- **Unlabelled** (Ch. V §1.2, P1:6029). A Beltrami differential of `S` defines a conformal structure on `S`. -/
theorem para5_1_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {μ : S → ℂ → ℂ} (hμ : μ ∈ GardinerLakic2000.beltramiBall S) :
    ∃ A : Set (OpenPartialHomeomorph S ℂ), IsInducedStructure μ A := by
  sorry

/-! ## §1.3 Group isomorphisms induced by quasiconformal mappings -/

/-- **Unlabelled** (Ch. V §1.3, P1:6039). A lift `f : D → D` of a quasiconformal mapping of a Riemann surface with
covering group `G` onto one with covering group `G′` has a homeomorphic extension to the boundary, which maps the
fixed points of `G` onto those of `G′` and the limit set `L` of `G` onto the limit set `L′` of `G′`. -/
theorem para5_1_3 {S₁ S₂ : Type u} [TopologicalSpace S₁] [T2Space S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [ConnectedSpace S₂] [ChartedSpace ℂ S₂]
    [IsManifold 𝓘(ℂ) ω S₂] {Γ₁ Γ₂ : Subgroup SL(2, ℝ)} {p₁ : ℍ → S₁} {p₂ : ℍ → S₂} (hΓ₁ : IsFuchsian Γ₁)
    (hfree₁ : ActsFreely Γ₁) (hΓ₂ : IsFuchsian Γ₂) (hfree₂ : ActsFreely Γ₂) (hp₁ : IsUniformization Γ₁ p₁)
    (hp₂ : IsUniformization Γ₂ p₂) {f : S₁ ≃ₜ S₂} (hf : IsQCRS f) {F : ℍ ≃ₜ ℍ} (hF : IsLift p₁ p₂ f F) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F) upperHalf upperHalf G ∧
      G '' {ξ | ξ ∈ closure (LiZhongQC.toExt upperHalf) \ LiZhongQC.toExt upperHalf ∧ ∃ γ ∈ Γ₁, γ ≠ 1 ∧ γ ≠ -1 ∧
        LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) ξ = ξ} =
        {ξ | ξ ∈ closure (LiZhongQC.toExt upperHalf) \ LiZhongQC.toExt upperHalf ∧ ∃ γ ∈ Γ₂, γ ≠ 1 ∧ γ ≠ -1 ∧
          LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) ξ = ξ} ∧
      G '' fuchsianLimitSet Γ₁ = fuchsianLimitSet Γ₂ := by
  sorry

/-- **Theorem 1.2** (Ch. V §1.3). Let `S`, `S′` be Riemann surfaces with non-elementary covering groups `G`, `G′`,
`φᵢ : S → S′` (`i = 0, 1`) quasiconformal mappings and `f₀` a lift of `φ₀`. Then `φ₀` and `φ₁` induce the same group
isomorphism between `G` and `G′` if and only if there is a lift `f₁` of `φ₁` which agrees with `f₀` on the limit set of
`G`.
Modelling: "the same isomorphism": `f₀ ∘ g ∘ f₀⁻¹ = f₁ ∘ g ∘ f₁⁻¹` on `ℍ` for `g ∈ G` (1.2); agreement on `L` is
agreement of the boundary extensions. -/
theorem thm5_1_2 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {Γ Γ' : Subgroup SL(2, ℝ)} {p : ℍ → S} {p' : ℍ → S'} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hp : IsUniformization Γ p)
    (hp' : IsUniformization Γ' p') (hne : 2 < (fuchsianLimitSet Γ).encard) {φ₀ φ₁ : S ≃ₜ S'} (h₀ : IsQCRS φ₀)
    (h₁ : IsQCRS φ₁) {f₀ : ℍ ≃ₜ ℍ} (hf₀ : IsLift p p' φ₀ f₀) :
    (∃ f₁ : ℍ ≃ₜ ℍ, IsLift p p' φ₁ f₁ ∧ ∀ γ ∈ Γ, ∀ τ : ℍ, f₀ (γ • f₀.symm τ) = f₁ (γ • f₁.symm τ)) ↔
      ∃ (f₁ : ℍ ≃ₜ ℍ) (G₀ G₁ : ExtPlane → ExtPlane), IsLift p p' φ₁ f₁ ∧
        IsHomeoExtension (liftToC f₀) upperHalf upperHalf G₀ ∧ IsHomeoExtension (liftToC f₁) upperHalf upperHalf G₁ ∧
        ∀ z ∈ fuchsianLimitSet Γ, G₀ z = G₁ z := by
  sorry

/-- **Theorem 1.3** (Ch. V §1.3). Let `S` be a Riemann surface with a non-elementary covering group. If `f : S → S`
is a conformal mapping homotopic to the identity, then `f` is the identity mapping (near miss:
`LiZhongQC.thm23_1_cor`, closed surfaces of genus `> 1`). -/
theorem thm5_1_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) (hne : 2 < (fuchsianLimitSet Γ).encard) {f : S ≃ₜ S} (hf : IsBiholomorphic f)
    (hh : ContinuousMap.Homotopic (f : C(S, S)) (ContinuousMap.id S)) : ⇑f = id := by
  sorry

/-! ## §1.4 Homotopy modulo the boundary -/

/-- **Unlabelled** (Ch. V §1.4, P1:6071–6081). Let `S = D/G` and `S′ = D/G′` with `G` of the second kind. A
quasiconformal mapping `φ` of `S` onto `S′` can be extended to a homeomorphism of the bordered surface
`S* = (D ∪ B)/G` onto `(S′)*`.
Modelling: through a lift `F` of `φ`: its boundary extension maps `ℍ ∪ (ℝ̂ ∖ L)` onto `ℍ ∪ (ℝ̂ ∖ L′)` and induces a
homeomorphism `e` of the bordered quotients (`borderedQuotient`) compatible with it. -/
theorem para5_1_4 {S₁ S₂ : Type u} [TopologicalSpace S₁] [T2Space S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [ConnectedSpace S₂] [ChartedSpace ℂ S₂]
    [IsManifold 𝓘(ℂ) ω S₂] {Γ₁ Γ₂ : Subgroup SL(2, ℝ)} {p₁ : ℍ → S₁} {p₂ : ℍ → S₂} (hΓ₁ : IsFuchsian Γ₁)
    (hfree₁ : ActsFreely Γ₁) (hΓ₂ : IsFuchsian Γ₂) (hfree₂ : ActsFreely Γ₂) (hp₁ : IsUniformization Γ₁ p₁)
    (hp₂ : IsUniformization Γ₂ p₂) (hsecond : ¬ GardinerLakic2000.IsFirstKind Γ₁) {φ : S₁ ≃ₜ S₂} (hφ : IsQCRS φ)
    {F : ℍ ≃ₜ ℍ} (hF : IsLift p₁ p₂ φ F) :
    ∃ (G : ExtPlane → ExtPlane) (e : borderedQuotient Γ₁ ≃ₜ borderedQuotient Γ₂),
      IsHomeoExtension (liftToC F) upperHalf upperHalf G ∧ G '' ordinarySet Γ₁ = ordinarySet Γ₂ ∧
      ∀ (x : ↥(LiZhongQC.toExt upperHalf ∪ ordinarySet Γ₁)) (y : ↥(LiZhongQC.toExt upperHalf ∪ ordinarySet Γ₂)),
        G x = y → e (Quot.mk _ x) = Quot.mk _ y := by
  sorry

end Lehto1987
