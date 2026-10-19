import References.Lehto1987.Ch04.S04_GroupsOfMobiusTransformations
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations
import References.Common.RiemannSurface
import References.Common.RiemannSphere
import LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# Farkas–Kra, Chapter IV §5: Uniformization of arbitrary Riemann surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §5 (`full.md` FK2:857–1048).

Conventions: a Riemann surface is a charted space over `ℂ` with the binders `[TopologicalSpace M] [T2Space M]`
`[ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]` (`References.IsRiemannSurface` in existential positions);
no second countability is assumed (FK prove it, IV.3.18 Cor 3). `ℂ̂` is `References.RiemannSphere` (scoped charts, open
scoped `References`). A group of Möbius transformations is a subgroup `G` of `SL(2, ℂ)` acting through
`LiZhongQC.mobiusSL`; `−I` acts trivially, so FK's `G ⊂ PSL(2, ℂ)` is `G` modulo `±I`. Statements about "the quotient
`D/G` as a Riemann surface" use the predicate `IsOrbitProjection` (a holomorphic open surjection whose fibres are the
`G`-orbits), which determines the Riemann surface `D/G` up to conformal equivalence. `Ω(G)`, `Λ(G)`, "Kleinian" and
"elementary" are those of `Lehto1987` (`discontinuitySet G = (limitSet G)ᶜ`; this agrees with FK's pointwise
definition of `Ω(G)` for every subgroup of `SL(2, ℂ)`). Discreteness of `G ⊂ PSL(2, ℂ)` is `IsDiscreteGroup`.

* IV.5.1 (Ω(G), Λ(G), Kleinian group) — exists: `Lehto1987.discontinuitySet`, `LiZhongQC.limitSet`, `Lehto1987.IsKleinian`
* IV.5.1 (function group) — `IsFunctionGroup`
* IV.5.1 (orbit space `D/G` as a Riemann surface; helpers) — `IsRelProjection`, `IsOrbitProjection`, `HasOrbitSurface`
* IV.5.1 (the quotients `Ω_j/G_j` are Riemann surfaces, `Ω_j → Ω_j/G_j` holomorphic) — `para4_5_1`
* Proposition IV.5.2 — `prop4_5_2`
* IV.5.3 (discrete group) — `IsDiscreteGroup`
* Proposition IV.5.3 — `prop4_5_3`
* IV.5.4 (Fuchsian group) — `IsGeneralizedDisc`, `IsFuchsianFK`
* Theorem IV.5.4 — `thm4_5_4`
* Corollary IV.5.4 — `cor4_5_4`
* Definition IV.5.4 (elementary group) — exists: `Lehto1987.IsElementary`
* IV.5.5 (universal covering, covering group) — exists: `Forster1981.IsUniversalCovering`, `deck`
* IV.5.5 (the covering group acts properly discontinuously, freely, by conformal automorphisms) — `para4_5_5`
* IV.5.6 (automorphism groups of `ℂ̂`, `ℂ`, `U`) — `para4_5_6_a`, `para4_5_6_b`, `para4_5_6_c`
* Theorem IV.5.6 — `thm4_5_6`
* Theorem IV.5.7 — `thm4_5_7`
* IV.5.8 (prolongable) — `IsProlongable`
* Definition IV.5.8 (first and second kind) — `IsFuchsianFirstKind`, `IsFuchsianSecondKind`
* Theorem IV.5.8 — `thm4_5_8`

Helpers (not book notions): the open subsets `finitePlaneOpens`, `upperHalfPlaneOpens` of `ℂ̂` and the set `unitDiscExt`.
Omitted (U−): the Picard group example (IV.5.3), Remarks 1–2 after IV.5.6, the Remark after IV.5.8, the Exercise.
-/

open scoped Manifold ContDiff MatrixGroups Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

universe u

open LiZhongQC (mobiusSL toExt limitSet IsMobius slRealToComplex upperHalf unitDisc IsBiholomorphic
  RSConformallyEquivalent)
open Lehto1987 (discontinuitySet IsKleinian IsElementary)
open References (RiemannSphere)

/-- The complex plane `ℂ ⊂ ℂ̂` as an open subset of the Riemann sphere (helper). -/
def finitePlaneOpens : TopologicalSpace.Opens RiemannSphere :=
  ⟨toExt univ, OnePoint.isOpen_image_coe.2 isOpen_univ⟩

/-- The upper half plane `U ⊂ ℂ̂` as an open subset of the Riemann sphere (helper). -/
def upperHalfPlaneOpens : TopologicalSpace.Opens RiemannSphere :=
  ⟨toExt upperHalf, OnePoint.isOpen_image_coe.2 (isOpen_lt continuous_const Complex.continuous_im)⟩

/-- The unit disc `Δ ⊂ ℂ̂` (helper). -/
def unitDiscExt : Set RiemannSphere := toExt unitDisc

/-- **Relation projection** (Ch. IV §5.1, helper). `π : X → N` is the canonical projection of the quotient of the
Riemann surface `X` by the equivalence relation `r` onto the Riemann surface `N`: holomorphic, open, onto, and
`π x = π y` exactly when `r x y`. -/
def IsRelProjection {X N : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace N] [ChartedSpace ℂ N]
    (π : X → N) (r : X → X → Prop) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ Function.Surjective π ∧ IsOpenMap π ∧ ∀ x y, π x = π y ↔ r x y

/-- **Orbit projection** (Ch. IV §5.1, helper). `π : D → N` is the canonical projection of the orbit space `D/G`
onto the Riemann surface `N = D/G`: holomorphic, open, onto, and `π x = π y` exactly when `x` and `y` are
`G`-equivalent. Modelling: the Riemann surface structure on `D/G` of FK (via III.7.7) is characterized by this
predicate. -/
def IsOrbitProjection {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] (G : Subgroup SL(2, ℂ))
    (D : TopologicalSpace.Opens RiemannSphere) (π : D → N) : Prop :=
  IsRelProjection π fun x y => ∃ g ∈ G, mobiusSL g (x : RiemannSphere) = (y : RiemannSphere)

/-- **The orbit space as a Riemann surface** (Ch. IV §5.1, helper). `D ⊆ ℂ̂` is open and the orbit space `D/G` carries
a Riemann surface structure for which the canonical projection is an orbit projection. -/
def HasOrbitSurface (G : Subgroup SL(2, ℂ)) (D : Set RiemannSphere) : Prop :=
  ∃ hD : IsOpen D, ∃ (N : Type) (_ : TopologicalSpace N) (_ : ChartedSpace ℂ N),
    References.IsRiemannSurface N ∧ ∃ π : (⟨D, hD⟩ : TopologicalSpace.Opens RiemannSphere) → N,
      IsOrbitProjection G ⟨D, hD⟩ π

/-- **Function group** (Ch. IV §5.1). A Kleinian group `G` is a *function group* if `Ω(G)` contains a `G`-invariant
component. Modelling: `∃ A, Lehto1987.IsInvariantDomain G A` (the invariant domain of Lehto is a `G`-invariant
component of `Ω(G)`); Kleinian-ness is not part of the definition, as in `Lehto1987`. -/
def IsFunctionGroup (G : Subgroup SL(2, ℂ)) : Prop := ∃ A, Lehto1987.IsInvariantDomain G A

/-- **Unlabelled** (Ch. IV §5.1, FK2:911, citing III.7.7). For a Kleinian group `G` and a component `Ω_j` of `Ω(G)`,
with stabilizer `G_j`, the orbit space `Ω_j/G_j` is a Riemann surface and the canonical projection
`Ω_j → Ω_j/G_j` is holomorphic.
Modelling: `Ω_j` is `connectedComponentIn Ω z`; the orbit relation of the projection is taken in `G` (for `x`, `y` in
`Ω_j`, `g x = y` with `g ∈ G` forces `g ∈ G_j`, since `G` permutes the components of `Ω`), so `G_j` need not be
named; the statement includes that `Ω_j` is open. -/
theorem para4_5_1 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) :
    ∀ z ∈ discontinuitySet G, HasOrbitSurface G (connectedComponentIn (discontinuitySet G) z) := by
  sorry

/-- **Proposition IV.5.2** (Ch. IV §5.2). A Kleinian group is finite or countable.
Modelling: `G ⊂ SL(2, ℂ)` is countable (equivalently, its image in `PSL(2, ℂ)` is). -/
theorem prop4_5_2 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) : (G : Set SL(2, ℂ)).Countable := by
  sorry

/-- **Discrete group** (Ch. IV §5.3). A group `G ⊂ PSL(2, ℂ) = SL(2, ℂ)/±I` is *discrete* if it is a discrete subset of
`PSL(2, ℂ)`. Modelling: every `g ∈ G` has a neighbourhood in `SL(2, ℂ)` meeting `G` only in `±g` (the quotient
map `SL(2, ℂ) → PSL(2, ℂ)` is open and its fibres are `{g, −g}`). -/
def IsDiscreteGroup (G : Subgroup SL(2, ℂ)) : Prop :=
  ∀ g ∈ G, ∃ V : Set SL(2, ℂ), IsOpen V ∧ g ∈ V ∧ ∀ h ∈ G, h ∈ V → h = g ∨ h = -g

/-- **Proposition IV.5.3** (Ch. IV §5.3). Every Kleinian group is discrete. -/
theorem prop4_5_3 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) : IsDiscreteGroup G := by
  sorry

/-- **Disc or half plane** (Ch. IV §5.4, helper). A disc or half plane of `ℂ̂`: the image of the unit disc under a
Möbius transformation. -/
def IsGeneralizedDisc (D : Set RiemannSphere) : Prop :=
  ∃ M : RiemannSphere → RiemannSphere, IsMobius M ∧ D = M '' unitDiscExt

/-- **Fuchsian group** (Ch. IV §5.4). A Kleinian group `G` is *Fuchsian* if there is a disc (or half plane) invariant
under `G`. Near misses: `LiZhongQC.IsFuchsian` (a discrete subgroup of `SL(2, ℝ)` acting on `ℍ`), `Katok1992.IsFuchsian`
(`PSL(2, ℝ)`). -/
def IsFuchsianFK (G : Subgroup SL(2, ℂ)) : Prop :=
  IsKleinian G ∧ ∃ D, IsGeneralizedDisc D ∧ ∀ g ∈ G, mobiusSL g '' D = D

/-- **Theorem IV.5.4** (Ch. IV §5.4). Let `G ⊂ Aut Δ` (a group of Möbius transformations preserving the unit disc).
The following are equivalent: (a) `Δ ⊂ Ω(G)`; (b) `Δ ∩ Ω(G) ≠ ∅`; (c) `G` is discrete. -/
theorem thm4_5_4 {G : Subgroup SL(2, ℂ)} (hG : ∀ g ∈ G, mobiusSL g '' unitDiscExt = unitDiscExt) :
    List.TFAE [unitDiscExt ⊆ discontinuitySet G, (unitDiscExt ∩ discontinuitySet G).Nonempty,
      IsDiscreteGroup G] := by
  sorry

/-- **Corollary IV.5.4** (Ch. IV §5.4). If `G` is a Fuchsian group with invariant disc `D`, then `Λ(G) ⊂ δD`. -/
theorem cor4_5_4 {G : Subgroup SL(2, ℂ)} (hK : IsKleinian G) {D : Set RiemannSphere} (hD : IsGeneralizedDisc D)
    (hinv : ∀ g ∈ G, mobiusSL g '' D = D) : limitSet G ⊆ frontier D := by
  sorry

/-- **Unlabelled** (Ch. IV §5.5, FK2:1001–1011). Let `M` be a Riemann surface, `π : M̃ → M` its universal covering
(with the analytic structure induced from `M`, so `π` is holomorphic) and `G` its covering group. Then `G` acts
properly discontinuously and fixed point freely on `M̃`, and every element of `G` is a conformal automorphism of `M̃`.
Modelling: properly discontinuous = every point has a neighbourhood `V` with `σ(V) ∩ V = ∅` for all `σ ∈ G`,
`σ ≠ 1`; `G` is `deck π`; "conformal automorphism" = `IsBiholomorphic`. (`G ≅ π₁(M)` is
`Forster1981.thm5_6_b`.) -/
theorem para4_5_5 {M Mt : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace Mt] [T2Space Mt] [ConnectedSpace Mt] [ChartedSpace ℂ Mt]
    [IsManifold 𝓘(ℂ) ω Mt] {p : Mt → M} (hp : Forster1981.IsUniversalCovering p)
    (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    (∀ σ ∈ deck p, IsBiholomorphic (σ : Mt → Mt)) ∧ (∀ σ ∈ deck p, σ ≠ 1 → ∀ x, σ x ≠ x) ∧
      ∀ x : Mt, ∃ V : Set Mt, IsOpen V ∧ x ∈ V ∧ ∀ σ ∈ deck p, σ ≠ 1 → σ '' V ∩ V = ∅ := by
  sorry

/-- **Unlabelled** (Ch. IV §5.6, FK2:1013–1019, with IV.5.5). The conformal automorphisms of `ℂ̂` are exactly the
Möbius transformations `z ↦ (az + b)/(cz + d)`, `ad − bc = 1` (`Aut ℂ̂ ≅ PSL(2, ℂ)`). -/
theorem para4_5_6_a (φ : RiemannSphere ≃ₜ RiemannSphere) :
    IsBiholomorphic (φ : RiemannSphere → RiemannSphere) ↔ ∃ g : SL(2, ℂ), ∀ z, φ z = mobiusSL g z := by
  sorry

/-- **Unlabelled** (Ch. IV §5.6, FK2:1013–1019). The conformal automorphisms of `ℂ` are exactly the affine maps
`z ↦ az + b`, `a ≠ 0` (`Aut ℂ ≅ PΔ(2, ℂ)`, the projective group of upper triangular matrices). -/
theorem para4_5_6_b (φ : ↥finitePlaneOpens ≃ₜ ↥finitePlaneOpens) :
    IsBiholomorphic (φ : ↥finitePlaneOpens → ↥finitePlaneOpens) ↔
      ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ,
        (φ ⟨(z : RiemannSphere), ⟨z, mem_univ z, rfl⟩⟩ : RiemannSphere) = ((a * z + b : ℂ) : RiemannSphere) := by
  sorry

/-- **Unlabelled** (Ch. IV §5.6, FK2:1013–1019). The conformal automorphisms of the upper half plane `U` are exactly
the Möbius transformations of `SL(2, ℝ)` (`Aut U ≅ PSL(2, ℝ)`). -/
theorem para4_5_6_c (φ : ↥upperHalfPlaneOpens ≃ₜ ↥upperHalfPlaneOpens) :
    IsBiholomorphic (φ : ↥upperHalfPlaneOpens → ↥upperHalfPlaneOpens) ↔
      ∃ g : SL(2, ℝ), ∀ z : ↥upperHalfPlaneOpens,
        (φ z : RiemannSphere) = mobiusSL (slRealToComplex g) (z : RiemannSphere) := by
  sorry

/-- **Theorem IV.5.6** (Ch. IV §5.6, general uniformization). Every Riemann surface `M` is conformally equivalent to
`D/G` with `D = ℂ̂`, `ℂ` or `U` and `G` a freely acting discontinuous group of Möbius transformations preserving `D`;
furthermore `G ≅ π₁(M)`.
Modelling: `D/G` is given by an orbit projection `D → M` (`IsOrbitProjection`, which makes `M ≅ D/G`); "freely
acting" = no element of `G` other than `±I` has a fixed point in `D`; "discontinuous" = `D ⊆ Ω(G)`; the isomorphism
`G ≅ π₁(M)` is for the image of `G` in `PSL(2, ℂ) = SL(2, ℂ)/center`. -/
theorem thm4_5_6 {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] (x₀ : M) :
    ∃ (D : TopologicalSpace.Opens RiemannSphere) (G : Subgroup SL(2, ℂ)),
      (D = ⊤ ∨ D = finitePlaneOpens ∨ D = upperHalfPlaneOpens) ∧ (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧
      (∀ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) → ∀ z ∈ (D : Set RiemannSphere), mobiusSL g z ≠ z) ∧
      (D : Set RiemannSphere) ⊆ discontinuitySet G ∧ (∃ π : D → M, IsOrbitProjection G D π) ∧
      Nonempty (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℂ))) ≃* FundamentalGroup M x₀) := by
  sorry

/-- **Theorem IV.5.7** (Ch. IV §5.7). Every Riemann surface can be represented as a domain in the plane factored by a
fixed point free Fuchsian or elementary group.
Modelling: as `thm4_5_6`, with the extra conclusion that `G` is Fuchsian (`IsFuchsianFK`) or elementary
(`Lehto1987.IsElementary`); the plane domain is `D ∈ {ℂ̂, ℂ, U}`. -/
theorem thm4_5_7 {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] :
    ∃ (D : TopologicalSpace.Opens RiemannSphere) (G : Subgroup SL(2, ℂ)),
      (D = ⊤ ∨ D = finitePlaneOpens ∨ D = upperHalfPlaneOpens) ∧ (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧
      (∀ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) → ∀ z ∈ (D : Set RiemannSphere), mobiusSL g z ≠ z) ∧
      (D : Set RiemannSphere) ⊆ discontinuitySet G ∧ (∃ π : D → M, IsOrbitProjection G D π) ∧
      (IsFuchsianFK G ∨ IsElementary G) := by
  sorry

/-- **Prolongable** (Ch. IV §5.8). A Riemann surface `M` is *prolongable* if there is a Riemann surface `M'` and a
one-to-one holomorphic mapping `f : M → M'` such that `M' ∖ f(M)` has a non-empty interior. -/
def IsProlongable (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace ℂ M'), References.IsRiemannSurface M' ∧
    ∃ f : M → M', MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ Function.Injective f ∧ (interior (range f)ᶜ).Nonempty

/-- **Fuchsian group of the first kind** (Ch. IV §5.8). A Fuchsian group `G` leaving invariant the disc `D` (with
boundary circle `C = δD`) is of the *first kind* if `Λ(G) = C`. -/
def IsFuchsianFirstKind (G : Subgroup SL(2, ℂ)) (D : Set RiemannSphere) : Prop :=
  IsKleinian G ∧ IsGeneralizedDisc D ∧ (∀ g ∈ G, mobiusSL g '' D = D) ∧ limitSet G = frontier D

/-- **Fuchsian group of the second kind** (Ch. IV §5.8). A Fuchsian group `G` leaving invariant the disc `D` (with
boundary circle `C = δD`) is of the *second kind* if `Λ(G) ⊊ C`. -/
def IsFuchsianSecondKind (G : Subgroup SL(2, ℂ)) (D : Set RiemannSphere) : Prop :=
  IsKleinian G ∧ IsGeneralizedDisc D ∧ (∀ g ∈ G, mobiusSL g '' D = D) ∧ limitSet G ⊂ frontier D

/-- **Theorem IV.5.8** (Ch. IV §5.8). Let `G` be a fixed point free Fuchsian group acting on `U`. Then `U/G` is
prolongable if `G` is of the second kind.
Modelling: for every Riemann surface `N` with an orbit projection `U → N`. -/
theorem thm4_5_8 {G : Subgroup SL(2, ℂ)} (hG : IsFuchsianSecondKind G (upperHalfPlaneOpens : Set RiemannSphere))
    (hfree : ∀ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) → ∀ z ∈ (upperHalfPlaneOpens : Set RiemannSphere),
      mobiusSL g z ≠ z) {N : Type} [TopologicalSpace N] [ChartedSpace ℂ N] (hN : References.IsRiemannSurface N)
    {π : upperHalfPlaneOpens → N} (hπ : IsOrbitProjection G upperHalfPlaneOpens π) : IsProlongable N := by
  sorry

end FarkasKra1992
