import References.Nag1988.Ch05.S03_BersIsomorphism
import References.Miyachi2008.S02_AsymptoticBersMap
import References.Lehto1987.Ch04.S04_GroupsOfMobiusTransformations
import References.GardinerLakic2000.Ch02.S09_FundamentalDomains
import LiZhongQC.Ch10.S34_BersFiberSpace

/-!
# Nag, Chapter 4 §4.4: Schwarzian derivatives, deformations of Fuchsian groups, Theorem S (W2 batch N3)

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 4 §4.4 (`full.md` N2:3593–3905,
folder `The Complex Analytic Theory … c10f6cd1`).

Conventions (see `Ch05/S01_BersFiberSpace` and the root file): `G = Γ` is a Fuchsian group, a subgroup of `SL(2, ℝ)` acting on
`ℍ = U`; Nag's `L` is `𝕃 = LiZhongQC.lowerHalf`; `Q(L, G)` is `LiZhongQC.automorphicQD Γ` (holomorphic quadratic differentials for `G`
on `𝕃`, extended by `0`), `B₂(L, G)` is `GardinerLakic2000.cuspFormsL Γ` with the norm `GardinerLakic2000.cuspNorm lowerHalf`, and
`T_β(G)` is the Bers image `LiZhongQC.bersImage Γ` (so "`T(G)`"). No manifold instance is put on `B₂(L, G)`; openness and holomorphy are the
predicates `IsBOpen`, `IsBHolOn` of `Ch05/S01`. A *deformation* of `G` is a pair `(σ, f)`: `f` a locally schlicht meromorphic function on
`𝕃` and `σ` a homomorphism of `G` into `Möb(ℂ)` (maps of `ℂ̂`) with `f ∘ g = σ(g) ∘ f`; `(σ, f)` and `(Mσ M⁻¹, M ∘ f)`, `M ∈ Möb(ℂ)`, are
equivalent. The developing mapping `f^φ` with `S f^φ = φ` is `Miyachi2008.IsDevelopingMap φ f` (any two differ by a Möbius map; global
schlichtness and the image group do not depend on the choice). `dim T(G) < ∞` is `FiniteDimensional ℂ` of the span of `B₂(L, G)`
(leader ruling 6). The Kleinian notions are `Lehto1987.IsKleinian`, `Lehto1987.discontinuitySet`.

* Definition (deformation of `G`, §4.4.1, N2:3593) — `IsDeformation`
* Proposition 4.4.1 (a) (the Schwarzian of a deformation lies in `Q(L, G)`, N2:3609) — `prop4_4_1_a`
* Proposition 4.4.1 (b) (equivalent deformations are those with the same Schwarzian, N2:3609) — `prop4_4_1_b`
* Proposition 4.4.1 (c) (every `φ ∈ Q(L, G)` is the Schwarzian of a deformation, N2:3609) — `prop4_4_1_c`
* Theorem 4.4.1 (description of `T(G)` by deformations, N2:3645) — `thm4_4_1`
* Definition (`S(G)`, `K(G)`, the image group `σ^φ(G)`, N2:3664) — `IsImageGroup`, `schlichtSet`, `kleinianSet`, `IsBInteriorPt`
* Theorem S (`T_β(G)` is the interior of `S(G)`, N2:3672) — `thmS`
* Theorem K, part (i) (N2:3676) — `thmK_a`
* Theorem K, part (ii) (N2:3677) — `thmK_b`
* Proposition 4.4.3 (`φ ↦ η_i^φ(z)` is holomorphic on `B₂(L, G)`, N2:3699) — `IsODESolution`, `prop4_4_3`
* Corollary 4.4.3 (i) (`φ ↦ f^φ(z)` is holomorphic, N2:3788) — `cor4_4_3_a`
* Corollary 4.4.3 (iii) (`φ ↦ (trace σ^φ(g))²` is holomorphic, N2:3788) — `IsTraceSqOf`, `cor4_4_3_c`
* Corollary 4.4.3 (ii) (`φ ↦ σ^φ(g)` is holomorphic, N2:3788) — omitted: `Möb(ℂ)` has no complex manifold structure in the project; the
  content is carried by (i) (the Möbius map `σ^φ(g)` is determined by three values of `f^φ`) and (iii)
* Sections 4.4.4–4.4.6 (deformations as projective structures, monodromy; Propositions on `T^#(G)` and projective atlases) — omitted:
  projective structures on a Riemann surface are not available (leader ruling on the Nag R4)

Reading: "`T(G)` is exactly the set of equivalence classes of deformations which have Nehari-bounded Schwarzians such that `S f = φ`
has a schlicht solution which extends to a quasiconformal self-homeomorphism `w` of `Ĉ` compatible with `G`" (Theorem 4.4.1) is stated with
the Bers image `T_β(G)`; Nehari-bounded is `‖φ‖ ≤ 6` in the cusp norm (curvature `−4`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (lowerHalf ExtPlane toExt meroToExt schwarzian IsLocUnivMero IsMobius mobiusSL IsFuchsian automorphicQD bersImage
  IsQuasiconformal IsConformalOnto)
open GardinerLakic2000 (cuspNorm cuspFormsL IsFirstKind)
open Lehto1987 (IsKleinian discontinuitySet)
open Miyachi2008 (IsDevelopingMap)

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Deformation of `G`** (Ch. 4 §4.4.1, N2:3593). `σ` is a homomorphism of `G` into `Möb(ℂ)` (Möbius maps of `ℂ̂`), `f` is a locally
schlicht meromorphic function on `𝕃`, and `f ∘ g = σ(g) ∘ f` for every `g ∈ G` (the developing map `f`, the image group `σ(G)`). -/
def IsDeformation (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (σ : Γ → ExtPlane → ExtPlane) (f : ℂ → ℂ) : Prop :=
  IsLocUnivMero f lowerHalf ∧ (∀ g, IsMobius (σ g)) ∧ (∀ g h, σ (g * h) = σ g ∘ σ h) ∧
    ∀ g : Γ, ∀ z ∈ lowerHalf, meroToExt f (mobAct (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) z) = σ g (meroToExt f z)

/-- **Proposition 4.4.1 (a)** (Ch. 4 §4.4.1, N2:3609). The Schwarzian derivative `S f` of a deformation `(σ, f)` of `G` belongs to the
space `Q(L, G)` of holomorphic quadratic differentials for `G` on `L`. -/
theorem prop4_4_1_a {σ : Γ → ExtPlane → ExtPlane} {f φ : ℂ → ℂ} (hd : IsDeformation Γ σ f)
    (hφ : (∀ z ∈ lowerHalf, φ z = schwarzian f z) ∧ ∀ z ∉ lowerHalf, φ z = 0) : φ ∈ automorphicQD Γ := by
  sorry

/-- **Proposition 4.4.1 (b)** (Ch. 4 §4.4.1, N2:3609). Two deformations `(σ, f)`, `(σ', f')` of `G` have the same Schwarzian derivative
if and only if they are equivalent: `f' = M ∘ f` and `σ'(g) ∘ M = M ∘ σ(g)` for a Möbius transformation `M` of `ℂ̂`. -/
theorem prop4_4_1_b {σ σ' : Γ → ExtPlane → ExtPlane} {f f' : ℂ → ℂ} (hd : IsDeformation Γ σ f) (hd' : IsDeformation Γ σ' f') :
    (∀ z ∈ lowerHalf, schwarzian f' z = schwarzian f z) ↔
      ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ (∀ z ∈ lowerHalf, meroToExt f' z = M (meroToExt f z)) ∧
        ∀ g, σ' g ∘ M = M ∘ σ g := by
  sorry

/-- **Proposition 4.4.1 (c)** (Ch. 4 §4.4.1, N2:3609). Every `φ ∈ Q(L, G)` is the Schwarzian derivative of a deformation of `G`
(Lemma 3.8.1: `S f = φ` has a meromorphic solution on `L`; then `f ∘ g = σ(g) ∘ f` for a Möbius map `σ(g)`). -/
theorem prop4_4_1_c {φ : ℂ → ℂ} (hφ : φ ∈ automorphicQD Γ) :
    ∃ (σ : Γ → ExtPlane → ExtPlane) (f : ℂ → ℂ), IsDeformation Γ σ f ∧ ∀ z ∈ lowerHalf, schwarzian f z = φ z := by
  sorry

/-- **Theorem 4.4.1** (Ch. 4 §4.4.1, N2:3645). `T(G)` is exactly the set of those equivalence classes of deformations of `G` which have
Nehari-bounded Schwarzians `φ` (`‖φ‖ ≤ 6`) such that `S f = φ` has a (globally) schlicht solution `f` on `L` which extends to a
quasiconformal self-homeomorphism `w` of `ℂ̂`, `w` being compatible with `G` (`w G w⁻¹` is a group of Möbius transformations).
[CORRECTION] (AUDIT1_Nag A1, AUDITR2_Nag R2N-1) The compatibility `w ∘ g = M ∘ w` is stated on `ℂ̂` with the Möbius map
`mobiusSL g` of `g`. The earlier form `∀ z : ℂ, w (mobAct g z) = M (w z)` used the junk value `mobAct g (−d/c) = 0` at the
real pole of `g`, which forces `w 0 = w ∞`, so the right side was false for every `G` with an element having `c ≠ 0`. -/
theorem thm4_4_1 (hΓ : IsFuchsian Γ) {φ : ℂ → ℂ} :
    φ ∈ bersImage Γ ↔ φ ∈ automorphicQD Γ ∧ cuspNorm lowerHalf φ ≤ 6 ∧
      ∃ f : ℂ → ℂ, IsDevelopingMap φ f ∧ InjOn (meroToExt f) lowerHalf ∧
        ∃ w : ExtPlane → ExtPlane, LehtoVirtanen1973.IsQuasiconformalMap w univ ∧ (∀ z ∈ lowerHalf, w z = meroToExt f z) ∧
          ∀ g ∈ Γ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧
            ∀ p : ExtPlane, w (mobiusSL (LiZhongQC.slRealToComplex g) p) = M (w p) := by
  sorry

/-- **The image group** `σ^φ(G)` (Ch. 4 §4.4.2, N2:3664). `H ≤ SL(2, ℂ)` is the group of matrices of the Möbius maps `σ(g)`, `g ∈ G`:
`{σ(g) | g ∈ G} = {mobiusSL A | A ∈ H}`. -/
def IsImageGroup (σ : Γ → ExtPlane → ExtPlane) (H : Subgroup SL(2, ℂ)) : Prop :=
  {m | ∃ g, σ g = m} = {m | ∃ A ∈ H, mobiusSL A = m}

/-- **The set `S(G)`** (Ch. 4 §4.4.2, N2:3664). The forms `φ ∈ B₂(L, G)` for which `f^φ` is globally schlicht on `L`
(`S f^φ = φ`). -/
def schlichtSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {φ | φ ∈ cuspFormsL Γ ∧ ∃ f : ℂ → ℂ, IsDevelopingMap φ f ∧ InjOn (meroToExt f) lowerHalf}

/-- **The set `K(G)`** (Ch. 4 §4.4.2, N2:3664). The forms `φ ∈ B₂(L, G)` whose image group `σ^φ(G)` is Kleinian. -/
def kleinianSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {φ | φ ∈ cuspFormsL Γ ∧ ∀ (σ : Γ → ExtPlane → ExtPlane) (f : ℂ → ℂ), IsDeformation Γ σ f →
    (∀ z ∈ lowerHalf, schwarzian f z = φ z) → ∃ H : Subgroup SL(2, ℂ), IsImageGroup σ H ∧ IsKleinian H}

/-- **Interior point of `S ⊆ B₂(L, G)`** for the norm topology of `B₂(L, G)`: a norm ball of `B₂(L, G)` around `φ` lies in `S`. -/
def IsBInteriorPt (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (S : Set (ℂ → ℂ)) (φ : ℂ → ℂ) : Prop :=
  φ ∈ S ∧ ∃ δ > (0 : ℝ), ∀ ψ ∈ cuspFormsL Γ, cuspNorm lowerHalf (ψ - φ) < ENNReal.ofReal δ → ψ ∈ S

/-- **Theorem S** (Shiga; Ch. 4 §4.4.2, N2:3672). Let `G` be a finitely generated Fuchsian group of the first kind (so `dim T(G) < ∞`).
Then `T_β(G)` is the interior of `S(G)` in `B₂(L, G)`. -/
theorem thmS (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ) (hfirst : IsFirstKind Γ)
    (hdim : FiniteDimensional ℂ (Submodule.span ℂ (cuspFormsL Γ))) :
    bersImage Γ = {φ | IsBInteriorPt Γ (schlichtSet Γ) φ} := by
  sorry

/-- **Theorem K, part (i)** (Shiga; Ch. 4 §4.4.2, N2:3676). Under the hypotheses of Theorem S, if `φ ∈ interior K(G) ∖ T_β(G)`,
then `f^φ` maps `L` onto `ℂ̂`. -/
theorem thmK_a (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ) (hfirst : IsFirstKind Γ)
    (hdim : FiniteDimensional ℂ (Submodule.span ℂ (cuspFormsL Γ))) {φ : ℂ → ℂ}
    (hφ : IsBInteriorPt Γ (kleinianSet Γ) φ) (hT : φ ∉ bersImage Γ) {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) :
    meroToExt f '' lowerHalf = univ := by
  sorry

/-- **Theorem K, part (ii)** (Shiga; Ch. 4 §4.4.2, N2:3677). Under the hypotheses of Theorem S, `T_β(G)` is a component of the interior of
`K(G)` (the component containing `0`): `T_β(G)` is a connected subset (for the norm topology `bersImageTopology`) of the interior
of `K(G)` which is open and closed in it. [AUDIT1_Nag M2] Openness of `T_β(G)` (in `B₂(L, G)`, hence in the interior of `K(G)`)
is the conjunct `IsBOpen`; without it the conjuncts would not characterize a component. -/
theorem thmK_b (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ) (hfirst : IsFirstKind Γ)
    (hdim : FiniteDimensional ℂ (Submodule.span ℂ (cuspFormsL Γ))) :
    @IsConnected (bersImage Γ) (bersImageTopology Γ) univ ∧ IsBOpen (cuspNorm lowerHalf) (cuspFormsL Γ) (bersImage Γ) ∧
      (∀ φ ∈ bersImage Γ, IsBInteriorPt Γ (kleinianSet Γ) φ) ∧
      (∀ φ, IsBInteriorPt Γ (kleinianSet Γ) φ → (∀ δ > (0 : ℝ), ∃ ψ ∈ bersImage Γ, cuspNorm lowerHalf (ψ - φ) < ENNReal.ofReal δ) →
        φ ∈ bersImage Γ) := by
  sorry

/-- **ODE solution** (Ch. 4 §4.4.2, (4.5)). `y` is a holomorphic solution on `L` of the linear differential equation
`2 y'' + φ y = 0`, which is the equation (4.5) equivalent to the Schwarzian equation `S f = φ`. -/
def IsODESolution (φ y : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ y lowerHalf ∧ ∀ z ∈ lowerHalf, 2 * deriv (deriv y) z + φ z * y z = 0

/-- **Proposition 4.4.3** (Ch. 4 §4.4.3, N2:3699). Let `G` be a Fuchsian group. For `φ ∈ B₂(L, G)` there are the solutions `η₁^φ`, `η₂^φ` of
`2 y'' + φ y = 0` on `L` with the normalizations (4.6) at `−i`: `η₁(−i) = 1`, `η₁'(−i) = 0`, `η₂(−i) = 0`, `η₂'(−i) = 1`; and
for each fixed `z ∈ L` the maps `φ ↦ η_i^φ(z)`, `i = 1, 2`, are holomorphic functions on `B₂(L, G)`. -/
theorem prop4_4_3 :
    ∃ η₁ η₂ : (ℂ → ℂ) → ℂ → ℂ, (∀ φ ∈ cuspFormsL Γ, IsODESolution φ (η₁ φ) ∧ IsODESolution φ (η₂ φ) ∧
        η₁ φ (-I) = 1 ∧ deriv (η₁ φ) (-I) = 0 ∧ η₂ φ (-I) = 0 ∧ deriv (η₂ φ) (-I) = 1) ∧
      ∀ z ∈ lowerHalf, IsBHolOn (cuspNorm lowerHalf) (fun v : ℂ => ENNReal.ofReal ‖v‖) (cuspFormsL Γ) (fun φ => η₁ φ z) ∧
        IsBHolOn (cuspNorm lowerHalf) (fun v : ℂ => ENNReal.ofReal ‖v‖) (cuspFormsL Γ) (fun φ => η₂ φ z) := by
  sorry

/-- **Corollary 4.4.3 (i)** (Ch. 4 §4.4.3, N2:3788). For `φ ∈ B₂(L, G)`, `G` an arbitrary Fuchsian group, the map `φ ↦ f^φ(z) ∈ ℂ̂`,
`f^φ = η₁^φ/η₂^φ` the canonical developing map, is holomorphic for any `z ∈ L ∖ {−i}`: `φ ↦ f^φ(z)` is holomorphic into `ℂ` where
`η₂^φ(z) ≠ 0`, and `φ ↦ 1/f^φ(z)` is holomorphic into `ℂ` where `η₁^φ(z) ≠ 0`. Modelling: for the canonical pair `(η₁, η₂)` of
Proposition 4.4.3 (the normalized solutions, which are unique). -/
theorem cor4_4_3_a {η₁ η₂ : (ℂ → ℂ) → ℂ → ℂ}
    (hη : ∀ φ ∈ cuspFormsL Γ, IsODESolution φ (η₁ φ) ∧ IsODESolution φ (η₂ φ) ∧
        η₁ φ (-I) = 1 ∧ deriv (η₁ φ) (-I) = 0 ∧ η₂ φ (-I) = 0 ∧ deriv (η₂ φ) (-I) = 1)
    {z : ℂ} (hz : z ∈ lowerHalf) (hz' : z ≠ -I) :
    IsBHolOn (cuspNorm lowerHalf) (fun v : ℂ => ENNReal.ofReal ‖v‖) {φ | φ ∈ cuspFormsL Γ ∧ η₂ φ z ≠ 0}
        (fun φ => η₁ φ z / η₂ φ z) ∧
      IsBHolOn (cuspNorm lowerHalf) (fun v : ℂ => ENNReal.ofReal ‖v‖) {φ | φ ∈ cuspFormsL Γ ∧ η₁ φ z ≠ 0}
        (fun φ => η₂ φ z / η₁ φ z) := by
  sorry

/-- **`t` is `(trace M)²` of the Möbius map `M`** (Ch. 4 §4.4.3, Corollary (iii)): `M` is the map of a matrix of `SL(2, ℂ)` of squared
trace `t` (well defined since `±A` give the same map and `(−tr)² = tr²`). -/
def IsTraceSqOf (M : ExtPlane → ExtPlane) (t : ℂ) : Prop :=
  ∃ A : SL(2, ℂ), mobiusSL A = M ∧ (A 0 0 + A 1 1) ^ 2 = t

/-- **Corollary 4.4.3 (iii)** (Ch. 4 §4.4.3, N2:3788). For `g ∈ G`, the map `φ ↦ (trace σ^φ(g))²` is holomorphic on `B₂(L, G)`
(it does not depend on the choice of the representative of the deformation). Modelling: for the family of canonical deformations
`(σ^φ, f^φ)`, `f^φ = η₁^φ/η₂^φ` (Proposition 4.4.3) and any function `t` with `t φ = (trace σ^φ(g))²`. -/
theorem cor4_4_3_c {η₁ η₂ : (ℂ → ℂ) → ℂ → ℂ}
    (hη : ∀ φ ∈ cuspFormsL Γ, IsODESolution φ (η₁ φ) ∧ IsODESolution φ (η₂ φ) ∧
        η₁ φ (-I) = 1 ∧ deriv (η₁ φ) (-I) = 0 ∧ η₂ φ (-I) = 0 ∧ deriv (η₂ φ) (-I) = 1)
    {σ : (ℂ → ℂ) → Γ → ExtPlane → ExtPlane} (hσ : ∀ φ ∈ cuspFormsL Γ, IsDeformation Γ (σ φ) (fun z => η₁ φ z / η₂ φ z))
    (g : Γ) {t : (ℂ → ℂ) → ℂ} (ht : ∀ φ ∈ cuspFormsL Γ, IsTraceSqOf (σ φ g) (t φ)) :
    IsBHolOn (cuspNorm lowerHalf) (fun v : ℂ => ENNReal.ofReal ‖v‖) (cuspFormsL Γ) t := by
  sorry

end Nag1988
