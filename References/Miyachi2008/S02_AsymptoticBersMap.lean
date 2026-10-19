import References.GardinerLakic2000.Ch14.S07_ManifoldStructure
import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC
import References.Common.Quasidisk
import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Miyachi 2008, §2: The Bers embedding and the asymptotic Bers map

H. Miyachi, *Image of asymptotic Bers map*, J. Math. Soc. Japan **60** (2008), no. 4, 1255–1276
(`refs/Miyachi2008_asymptotic_Bers_map.pdf`; page numbers `p. n` are the journal pages 1255–1276).

**Model.** The paper works in the unit disk `D` and its exterior `D*` (`Ĉ ∖ cl D`). Everything is invariant under Möbius
transformations, and the project's Bers embedding (`LiZhongQC.bersMapGamma`, Gardiner–Lakic Ch. 6, 14) lives on the half-plane
model: `D` is replaced by the upper half-plane `ℍ` and `D*` by the lower half-plane `𝕃 = LiZhongQC.lowerHalf` (Cayley
transform), `Γ` is a Fuchsian group `Γ ≤ SL(2, ℝ)`, `S¹ = ∂D` becomes `∂𝕃 = ℝ ∪ {∞}`. The space `B(Γ)` of bounded automorphic
forms of weight `−4` on `D*` is `GardinerLakic2000.cuspFormsL Γ` (forms on `𝕃`, extended by `0` off `𝕃`, norm
`GardinerLakic2000.cuspNorm`, with the hyperbolic metric of curvature `−4`, as in the paper, p. 1260), the subspace `B₀(Γ)` of
forms vanishing at infinity is `GardinerLakic2000.boundedCuspForms0` (the `b*`-condition of Gardiner–Lakic §14.2 and the paper's
definition coincide: the `(−1, 1)`-form `λ⁻² φ̄` descends to a Beltrami differential vanishing at infinity), `B̂(Γ) = B(Γ)/B₀(Γ)` is
a genuine quotient of vector spaces (`bHat`), with the quotient norm `hatNorm`. The Bers embedding `β_Γ` has image
`T_Γ = Set.range (LiZhongQC.bersMapGamma Γ)` and the asymptotic Bers map has the image `asymBersImage Γ`, defined directly as the
image of `T_Γ` in `B̂(Γ)` ((2.3) of the paper). The developing mapping `f_φ` of `φ` is any locally univalent meromorphic
function `f` on `𝕃` with Schwarzian derivative `𝒮(f) = φ` (`IsDevelopingMap`); any two differ by a Möbius transformation, and
every notion below is invariant under it, so statements are made for all developing mappings.

* Definition (the space `B(Γ)` of bounded automorphic forms of weight `−4`, its norm; p. 1260) — exists: `GardinerLakic2000.cuspFormsL`, `GardinerLakic2000.cuspNorm`
* Definition (the Bers embedding `β_Γ`, p. 1261) — exists: `LiZhongQC.bersMapGamma`
* Definition (asymptotic equivalence of Teichmüller classes, `AT(R)`, p. 1260) — exists: `GardinerLakic2000.IsAsymEquivGamma`
* Definition (the space `B̂(Γ) = B(Γ)/B₀(Γ)`, its elements and its quotient norm, p. 1260) — `bZero`, `bHat`, `bHatMk`, `hatNorm`
* Definition (the closure in `B̂(Γ)` for the quotient norm) — `hatClosure`
* Definition (the developing mapping `f_φ`, p. 1261) — `IsDevelopingMap`
* Definition ((2.3), the image `𝒜𝒯_Γ` of the asymptotic Bers map, p. 1261) — `asymBersImage`
* Proposition 2.1 (Ahlfors, p. 1261) — `prop2_1`
* §2.2.2 (existence and injectivity of the asymptotic Bers map `β̂_Γ : AT(D/Γ) → B̂(Γ)`, Earle–Gardiner–Lakic; Earle–Markovic–Šarić;
  p. 1261) — `thm2_2_2`

Not items: §2.1 (the definitions of Teichmüller space, asymptotic Teichmüller space and Beltrami differentials vanishing at
infinity are reused: `LiZhongQC.TeichGamma`, `GardinerLakic2000.IsAsymEquivGamma`, `GardinerLakic2000.IsInT0Gamma`), (2.1) (the chain
rule of the Schwarzian derivative), the characterization of `T_Γ` by developing mappings (quoted from Ahlfors, Bers).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Miyachi2008

open LiZhongQC (lowerHalf toExt ExtPlane schwarzian IsLocUnivMero meroToExt IsFuchsian TeichGamma bersMapGamma IsKQuasidisc)
open GardinerLakic2000 (cuspFormsL cuspNorm boundedCuspForms0 orbitMapsR IsAsymEquivGamma poincareDensityGL)
open LehtoVirtanen1973 (IsKQuasiconformal)

/-- **The subspace `B₀(Γ)`** (p. 1260). The forms of `B(Γ)` vanishing at infinity with respect to `Γ`:
`GardinerLakic2000.boundedCuspForms0` for the orbit maps of `Γ` on `𝕃` (the condition `b*(λ⁻² φ̄, Γ) = 0`). -/
def bZero (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  boundedCuspForms0 (orbitMapsR Γ) lowerHalf (cuspFormsL Γ)

/-- **The quotient `B̂(Γ) = B(Γ)/B₀(Γ)`** (p. 1260). The quotient of the vector space of forms spanned by `B(Γ)` by the span of
`B₀(Γ)` (the sets are subspaces; the span is the book's vector space). -/
abbrev bHat (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  (Submodule.span ℂ (cuspFormsL Γ)) ⧸ (Submodule.span ℂ (bZero Γ)).comap (Submodule.span ℂ (cuspFormsL Γ)).subtype

/-- **The class `[φ] ∈ B̂(Γ)`** (p. 1260) of a form `φ ∈ B(Γ)`. -/
def bHatMk (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) (h : φ ∈ cuspFormsL Γ) : bHat Γ :=
  Submodule.Quotient.mk ⟨φ, Submodule.subset_span h⟩

/-- **The quotient norm `‖·‖^_{D*}`** (p. 1260). `‖x‖^ = inf {‖φ‖_{𝕃} : [φ] = x}`. -/
def hatNorm (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (x : bHat Γ) : ℝ≥0∞ :=
  ⨅ (φ : ℂ → ℂ) (h : φ ∈ cuspFormsL Γ) (_ : bHatMk Γ φ h = x), cuspNorm lowerHalf φ

/-- **Closure in `B̂(Γ)`** (p. 1258). `x ∈ cl S` for the topology of the quotient norm: for every `ε > 0` there is `y ∈ S` with
`‖x − y‖^ < ε`. -/
def hatClosure (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (S : Set (bHat Γ)) : Set (bHat Γ) :=
  {x | ∀ ε : ℝ, 0 < ε → ∃ y ∈ S, hatNorm Γ (x - y) < ENNReal.ofReal ε}

/-- **Developing mapping** (p. 1261). `f` is a developing mapping for `φ`: a locally univalent meromorphic function on `𝕃`
(`D*`) with Schwarzian derivative `𝒮(f) = φ` on `𝕃`. -/
def IsDevelopingMap (φ f : ℂ → ℂ) : Prop :=
  IsLocUnivMero f lowerHalf ∧ ∀ z ∈ lowerHalf, schwarzian f z = φ z

/-- **The image `𝒜𝒯_Γ` of the asymptotic Bers map** (p. 1261, (2.3): `𝒜𝒯_Γ = {[φ] | φ ∈ 𝒯_Γ}`). The classes in `B̂(Γ)` of the
images `β_Γ([f]_T) = 𝒮(W_f|_{D*})` of the Bers embedding (`LiZhongQC.bersMapGamma`), i.e. the image of `T_Γ`. -/
def asymBersImage (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (bHat Γ) :=
  {x | ∃ P : TeichGamma Γ, ∃ h : bersMapGamma Γ P ∈ cuspFormsL Γ, bHatMk Γ (bersMapGamma Γ P) h = x}

/-- **Proposition 2.1** (Ahlfors; p. 1261). For `L ≥ 1` there is a constant `c(L) > 0` such that any locally univalent function
`g` on an `L`-quasidisk `Ω` satisfying `‖𝒮(g)‖_Ω ≤ c(L)` admits a `2`-quasiconformal extension on `Ĉ`.
Modelling: `Ω ⊂ ℂ` (the case used in the paper, Section 3), `‖𝒮(g)‖_Ω = sup_Ω λ_Ω⁻² |𝒮(g)|` with the hyperbolic metric of
curvature `−4` (`GardinerLakic2000.poincareDensityGL`); the extension agrees with `g` (read in `Ĉ`) on `Ω`. -/
theorem prop2_1 {L : ℝ} (hL : 1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Set ℂ) (g : ℂ → ℂ), IsKQuasidisc Ω L → IsLocUnivMero g Ω →
      (∀ z ∈ Ω, ‖schwarzian g z‖ * poincareDensityGL Ω z ^ (-2 : ℤ) ≤ c) →
        ∃ E : ExtPlane → ExtPlane, IsKQuasiconformal E univ 2 ∧ ∀ z ∈ Ω, E z = meroToExt g z := by
  sorry

/-- **Unlabelled** (§2.2.2, p. 1261; Earle–Gardiner–Lakic, Earle–Markovic–Šarić). For a Fuchsian group `Γ`, there is a holomorphic
embedding `β̂_Γ : AT(D/Γ) → B̂(Γ)` making the diagram (2.2) commute. Stated, without the complex structure, as: there is a map
`ι` on the Teichmüller space `T(Γ)` with `ι(P) = [β_Γ(P)]` for all `P` that identifies exactly the asymptotically equivalent
points (`IsAsymEquivGamma`), so that it descends to an injective map of `AT(D/Γ)`. -/
theorem thm2_2_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    ∃ ι : TeichGamma Γ → bHat Γ,
      (∀ P, ∃ h : bersMapGamma Γ P ∈ cuspFormsL Γ, ι P = bHatMk Γ (bersMapGamma Γ P) h) ∧
        ∀ P Q, ι P = ι Q ↔ IsAsymEquivGamma Γ P Q := by
  sorry

end Miyachi2008
