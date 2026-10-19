import Jacobians.Abel.AbelDbarKill
import RiemannDynamics.Uniformization.Trichotomy
import Jacobians.TailDuality.RiemannRochUnconditional
import Jacobians.DolbeaultComparison.LerayCoverExists
import Jacobians.DolbeaultComparison.DolbeaultComparisonInverse
import Mathlib.Topology.Subpath
import Jacobians.Cech.ChartDiskCover
import Jacobians.DolbeaultComparison.DolbeaultComparison
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import LiZhongQC.Ch05.S19_Schwarzian
import LiZhongQC.Ch02.S13_Representation

/-!
# §22 Riemann 曲面 — Riemann surfaces

A Riemann surface is a connected Hausdorff topological space `S` with a complex analytic atlas;
in Mathlib terms `[TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
[IsManifold 𝓘(ℂ) ω S]` (§22.1).

* holomorphic maps, biholomorphisms, conformal equivalence       — `IsBiholomorphic`
* genus of a closed surface (via the presentation of `π₁`)       — `surfaceGroup`, `HasGenus`
* Theorem 22.1 (monodromy theorem)                               — `thm22_1_monodromy`
* universal coverings                                            — `exists_universal_covering`
* Theorem 22.2 (uniformization), Theorem 22.3 (the five types)   — `thm22_2_uniformization`,
                                                                   `thm22_3_classification`
* Fuchsian groups; Gauss–Bonnet for closed surfaces of genus `g > 1`
* §22.5 differentials of type `(m, n)`, divisors, Riemann–Roch (Theorem 22.4),
  `dim Q = 3g - 3` (Theorem 22.5)
* §22.6 classification of fractional linear transformations
* Möbius and Cayley support moved from §23 — `liftToC`, `h23l_liftToC_eq`,
  `k24_d_den_ne_zero`, `k24_det_realR`, `h36t_coe_smul`, `h36t_den_ne`,
  `s35a_x_isConformalOnto_cayleyInv`
* Upper-half-plane matrix support moved from §23 — `utm_im_mobius`,
  `utm_sl2_eq_of_bounded_displacement`, `utm_re_sq_add_im_sq`, `utm_rot`,
  `utm_cayley_rot_alg`, `utm_cayley_rot`, `utm_eq_smul_of_isKQC_one`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {S' : Type v} [TopologicalSpace S'] [ChartedSpace ℂ S']

/-! ## §22.1 Basic notions -/

/-- `f : S → S'` is biholomorphic (共形映射 between Riemann surfaces): holomorphic, bijective,
with holomorphic inverse. -/
def IsBiholomorphic (f : S → S') : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
    ∃ g : S' → S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ Function.LeftInverse g f ∧ Function.RightInverse g f

/-- Two Riemann surfaces are conformally equivalent. -/
def RSConformallyEquivalent (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S]
    (S' : Type v) [TopologicalSpace S'] [ChartedSpace ℂ S'] : Prop :=
  ∃ f : S → S', IsBiholomorphic f

/-- The identity map of a Riemann surface is biholomorphic. -/
theorem isBiholomorphic_id : IsBiholomorphic (id : S → S) :=
  ⟨mdifferentiable_id, id, mdifferentiable_id, fun _ => rfl, fun _ => rfl⟩

/-- The inverse of a biholomorphic homeomorphism is biholomorphic.  (The holomorphic inverse
supplied by `IsBiholomorphic` is necessarily the inverse homeomorphism.) -/
theorem IsBiholomorphic.homeomorph_symm {e : S ≃ₜ S'} (he : IsBiholomorphic (e : S → S')) :
    IsBiholomorphic (e.symm : S' → S) := by
  obtain ⟨hf, g, hg, hlg, -⟩ := he
  have hge : g = (e.symm : S' → S) := by
    funext y
    have h := hlg (e.symm y)
    rwa [e.apply_symm_apply] at h
  exact ⟨hge ▸ hg, (e : S → S'), hf, e.apply_symm_apply, e.symm_apply_apply⟩

/-- Biholomorphic maps compose. -/
theorem IsBiholomorphic.comp {S'' : Type*} [TopologicalSpace S''] [ChartedSpace ℂ S'']
    {f : S → S'} {h : S' → S''} (hh : IsBiholomorphic h) (hf : IsBiholomorphic f) :
    IsBiholomorphic (h ∘ f) := by
  obtain ⟨hhd, k, hkd, hlk, hrk⟩ := hh
  obtain ⟨hfd, g, hgd, hlg, hrg⟩ := hf
  refine ⟨hhd.comp hfd, g ∘ k, hgd.comp hkd, fun x => ?_, fun z => ?_⟩
  · show g (k (h (f x))) = x
    rw [hlk (f x), hlg x]
  · show h (f (g (k z))) = z
    rw [hrg (k z), hrk z]

/-- The continuous map underlying a composite homeomorphism is the composite of the underlying
continuous maps. -/
theorem coe_homeomorph_trans {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] (e : A ≃ₜ B) (f : B ≃ₜ C) :
    ((e.trans f : A ≃ₜ C) : C(A, C)) = (f : C(B, C)).comp (e : C(A, B)) := rfl

/-- The unit disc as an open subset of `ℂ` (a Riemann surface). -/
def unitDiscOpens : TopologicalSpace.Opens ℂ := ⟨unitDisc, isOpen_ball⟩

/-- The punctured plane `ℂ ∖ {0}` as an open subset of `ℂ`. -/
def puncturedPlaneOpens : TopologicalSpace.Opens ℂ := ⟨puncturedPlane, isOpen_compl_singleton⟩

/-- A holomorphic function on a Riemann surface is (in charts) a holomorphic function. -/
def IsHolomorphicRS (f : S → ℂ) : Prop := MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f

/-- The local expression `f ∘ φ⁻¹` of a function in the preferred chart at `x`. -/
def localExpr (f : S → ℂ) (x : S) : ℂ → ℂ := fun z => f ((chartAt ℂ x).symm z)

/-- A meromorphic function on a Riemann surface (meromorphic in every chart). -/
def IsMeromorphicRS (f : S → ℂ) : Prop :=
  ∀ x : S, MeromorphicAt (localExpr f x) (chartAt ℂ x x)

/-- The order of a meromorphic function at a point (zero order: positive; pole: negative). -/
def ordRS (f : S → ℂ) (x : S) : WithTop ℤ := meromorphicOrderAt (localExpr f x) (chartAt ℂ x x)

/-! ## Genus -/

/-- The fundamental group of a closed surface of genus `g`:
`⟨a₁, b₁, …, a_g, b_g | a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_g b_g a_g⁻¹ b_g⁻¹⟩` (§22.4). -/
def surfaceGroup (g : ℕ) : Type :=
  PresentedGroup {(List.ofFn fun i : Fin g =>
    FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
      (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod}

instance (g : ℕ) : Group (surfaceGroup g) := by unfold surfaceGroup; infer_instance

/-- The two standard free generators do not commute. Uses the reduced-word
criterion already in FreeGroup.Basic, without introducing a new definition. -/
theorem s22c2_free_two_generators_ne_commute :
    FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ≠
      FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) := by
  intro h
  change FreeGroup.mk [((0 : Fin 2), true), ((1 : Fin 2), true)] =
    FreeGroup.mk [((1 : Fin 2), true), ((0 : Fin 2), true)] at h
  obtain ⟨L, h01, h10⟩ := FreeGroup.Red.exact.mp h
  have hn01 : ((0 : Fin 2), false) ≠ ((1 : Fin 2), true) := by decide
  have hn10 : ((1 : Fin 2), false) ≠ ((0 : Fin 2), true) := by decide
  have hL01 : L = [((0 : Fin 2), true), ((1 : Fin 2), true)] :=
    (FreeGroup.Red.red_iff_irreducible hn01).mp h01
  have hL10 : L = [((1 : Fin 2), true), ((0 : Fin 2), true)] :=
    (FreeGroup.Red.red_iff_irreducible hn10).mp h10
  have hne : [((0 : Fin 2), true), ((1 : Fin 2), true)] ≠
      [((1 : Fin 2), true), ((0 : Fin 2), true)] := by decide
  exact hne (hL01.symm.trans hL10)

/-- Kill every b-generator in the frozen surface presentation. The first
a-generator maps to the first free generator and every other a-generator maps
to the second; g>1 supplies both, so the descended homomorphism is surjective. -/
theorem s22c2_surfaceGroup_surjects_free_two (g : ℕ) (hg : 1 < g) :
    ∃ φ : surfaceGroup g →* FreeGroup (Fin 2), Function.Surjective φ := by
  classical
  have h2 : 2 ≤ g := by omega
  let f : (Fin g ⊕ Fin g) → FreeGroup (Fin 2) :=
    Sum.elim
      (fun i => if i.val = 0 then FreeGroup.of 0 else FreeGroup.of 1)
      (fun _ => 1)
  have hb (i : Fin g) : f (Sum.inr i) = 1 := rfl
  have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin g =>
      FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
      Set (FreeGroup (Fin g ⊕ Fin g))), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    rw [map_list_prod, List.map_ofFn]
    apply List.prod_eq_one
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    rw [← hi]
    change FreeGroup.lift f
      (FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹) = 1
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hb, mul_one,
      inv_one, mul_inv_cancel]
  let φ : surfaceGroup g →* FreeGroup (Fin 2) := PresentedGroup.toGroup hrel
  let ψ : FreeGroup (Fin 2) →* surfaceGroup g :=
    FreeGroup.lift (fun j : Fin 2 =>
      (PresentedGroup.of (Sum.inl (Fin.castLE h2 j)) : surfaceGroup g))
  have hcomp : φ.comp ψ = MonoidHom.id (FreeGroup (Fin 2)) := by
    apply FreeGroup.ext_hom
    intro j
    change PresentedGroup.toGroup hrel
      ((FreeGroup.lift (fun k : Fin 2 =>
        (PresentedGroup.of (Sum.inl (Fin.castLE h2 k)) : surfaceGroup g)))
          (FreeGroup.of j)) = FreeGroup.of j
    rw [FreeGroup.lift_apply_of, PresentedGroup.toGroup.of]
    fin_cases j <;> rfl
  refine ⟨φ, ?_⟩
  intro w
  exact ⟨ψ w, DFunLike.congr_fun hcomp w⟩

/-- The surface presentation for g>1 is infinite and has an explicit pair
of noncommuting elements. Infinite FreeGroup is reused from Cardinal.Free. -/
theorem s22c2_surfaceGroup_infinite_noncommutative {g : ℕ} (hg : 1 < g) :
    Infinite (surfaceGroup g) ∧
      ∃ x y : surfaceGroup g, x * y ≠ y * x := by
  obtain ⟨φ, hφ⟩ := s22c2_surfaceGroup_surjects_free_two g hg
  refine ⟨Infinite.of_surjective φ hφ, ?_⟩
  obtain ⟨x, hx⟩ := hφ (FreeGroup.of (0 : Fin 2))
  obtain ⟨y, hy⟩ := hφ (FreeGroup.of (1 : Fin 2))
  refine ⟨x, y, ?_⟩
  intro hxy
  have h := congrArg φ hxy
  simp only [map_mul, hx, hy] at h
  exact s22c2_free_two_generators_ne_commute h

/-- A closed (compact) Riemann surface of genus `g`: its fundamental group is the surface group
of genus `g` (by the classification of closed orientable surfaces, `S` is then a sphere with `g`
handles). -/
def HasGenus (S : Type u) [TopologicalSpace S] (g : ℕ) : Prop :=
  CompactSpace S ∧ ∀ x : S, Nonempty (FundamentalGroup S x ≃* surfaceGroup g)

/-- Evaluating loop precomposition at the constant-path basepoint recovers
the loop class itself. -/
theorem s22c1_deck_base {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ : FundamentalGroup S x₀) :
    RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀) =
      (⟨x₀, γ.toPath⟩ : RiemannDynamics.PathCover x₀) := by
  change (⟨x₀, γ.toPath.trans (Path.Homotopic.Quotient.refl x₀)⟩ :
    RiemannDynamics.PathCover x₀) = ⟨x₀, γ.toPath⟩
  exact congrArg (RiemannDynamics.PathCover.mk x₀)
    (Path.Homotopic.Quotient.trans_refl γ.toPath)

/-- The identity loop class acts as the identity on the concrete path cover. -/
theorem s22c1_deck_one {S : Type u} [TopologicalSpace S] (x₀ : S)
    (pc : RiemannDynamics.PathCover x₀) :
    RiemannDynamics.pathCoverDeck x₀ (1 : FundamentalGroup S x₀) pc = pc := by
  rcases pc with ⟨y, c⟩
  change (⟨y, (Path.Homotopic.Quotient.refl x₀).trans c⟩ :
    RiemannDynamics.PathCover x₀) = ⟨y, c⟩
  exact congrArg (RiemannDynamics.PathCover.mk y)
    (Path.Homotopic.Quotient.refl_trans c)

/-- Mathlib multiplies loop classes by reverse path concatenation. Thus deck
precomposition is an antihomomorphism into functions under composition. -/
theorem s22c1_deck_mul {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ δ : FundamentalGroup S x₀) (pc : RiemannDynamics.PathCover x₀) :
    RiemannDynamics.pathCoverDeck x₀ (γ * δ) pc =
      RiemannDynamics.pathCoverDeck x₀ δ
        (RiemannDynamics.pathCoverDeck x₀ γ pc) := by
  change (⟨pc.pt, (δ.toPath.trans γ.toPath).trans pc.cls⟩ :
    RiemannDynamics.PathCover x₀) =
      ⟨pc.pt, δ.toPath.trans (γ.toPath.trans pc.cls)⟩
  exact congrArg (RiemannDynamics.PathCover.mk pc.pt)
    (Path.Homotopic.Quotient.trans_assoc δ.toPath γ.toPath pc.cls)

/-- Reversing a loop gives both inverse identities for its deck map. -/
theorem s22c1_deck_inv {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ : FundamentalGroup S x₀) (pc : RiemannDynamics.PathCover x₀) :
    RiemannDynamics.pathCoverDeck x₀ (γ⁻¹ : FundamentalGroup S x₀)
        (RiemannDynamics.pathCoverDeck x₀ γ pc) = pc ∧
      RiemannDynamics.pathCoverDeck x₀ γ
        (RiemannDynamics.pathCoverDeck x₀ (γ⁻¹ : FundamentalGroup S x₀) pc) = pc := by
  constructor
  · rw [← s22c1_deck_mul, mul_inv_cancel]
    exact s22c1_deck_one x₀ pc
  · rw [← s22c1_deck_mul, inv_mul_cancel]
    exact s22c1_deck_one x₀ pc

/-- Distinct fundamental-group elements move the canonical basepoint to
distinct points of its fiber. -/
theorem s22c1_deck_base_injective {S : Type u} [TopologicalSpace S] (x₀ : S) :
    Function.Injective (fun γ : FundamentalGroup S x₀ =>
      RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀)) := by
  intro γ δ h
  have h' : (⟨x₀, γ.toPath⟩ : RiemannDynamics.PathCover x₀) = ⟨x₀, δ.toPath⟩ :=
    (s22c1_deck_base x₀ γ).symm.trans (h.trans (s22c1_deck_base x₀ δ))
  rw [RiemannDynamics.PathCover.mk.injEq] at h'
  exact eq_of_heq h'.2

/-- The actual loop-to-deck-function map is faithful. -/
theorem s22c1_deck_injective {S : Type u} [TopologicalSpace S] (x₀ : S) :
    Function.Injective (fun γ : FundamentalGroup S x₀ =>
      RiemannDynamics.pathCoverDeck x₀ γ) := by
  intro γ δ h
  exact s22c1_deck_base_injective x₀
    (congrFun h (RiemannDynamics.pathCoverBase x₀))

/-- A loop deck map fixing any point has trivial loop class. This is path-class
cancellation and needs no manifold, connectedness or covering-lift hypothesis. -/
theorem s22c1_deck_fixed_eq_one {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ : FundamentalGroup S x₀) (pc : RiemannDynamics.PathCover x₀)
    (hfix : RiemannDynamics.pathCoverDeck x₀ γ pc = pc) : γ = 1 := by
  rcases pc with ⟨y, c⟩
  change (⟨y, γ.toPath.trans c⟩ : RiemannDynamics.PathCover x₀) = ⟨y, c⟩ at hfix
  rw [RiemannDynamics.PathCover.mk.injEq] at hfix
  have hc : γ.toPath.trans c = c := eq_of_heq hfix.2
  have hcancel := congrArg
    (fun η : Path.Homotopic.Quotient x₀ y => η.trans c.symm) hc
  change γ.toPath = Path.Homotopic.Quotient.refl x₀
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl] using hcancel

/-- Commutation of two deck maps at the canonical basepoint is already
equivalent to commutation of their actual fundamental-group elements. -/
theorem s22c1_deck_base_commute_iff {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ δ : FundamentalGroup S x₀) :
    RiemannDynamics.pathCoverDeck x₀ γ
        (RiemannDynamics.pathCoverDeck x₀ δ (RiemannDynamics.pathCoverBase x₀)) =
      RiemannDynamics.pathCoverDeck x₀ δ
        (RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀)) ↔
      γ * δ = δ * γ := by
  constructor
  · intro h
    apply s22c1_deck_base_injective x₀
    calc
      RiemannDynamics.pathCoverDeck x₀ (γ * δ) (RiemannDynamics.pathCoverBase x₀) =
          RiemannDynamics.pathCoverDeck x₀ δ
            (RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀)) :=
        s22c1_deck_mul x₀ γ δ _
      _ = RiemannDynamics.pathCoverDeck x₀ γ
          (RiemannDynamics.pathCoverDeck x₀ δ (RiemannDynamics.pathCoverBase x₀)) := h.symm
      _ = RiemannDynamics.pathCoverDeck x₀ (δ * γ) (RiemannDynamics.pathCoverBase x₀) :=
        (s22c1_deck_mul x₀ δ γ _).symm
  · intro h
    calc
      RiemannDynamics.pathCoverDeck x₀ γ
          (RiemannDynamics.pathCoverDeck x₀ δ (RiemannDynamics.pathCoverBase x₀)) =
        RiemannDynamics.pathCoverDeck x₀ (δ * γ) (RiemannDynamics.pathCoverBase x₀) :=
          (s22c1_deck_mul x₀ δ γ _).symm
      _ = RiemannDynamics.pathCoverDeck x₀ (γ * δ) (RiemannDynamics.pathCoverBase x₀) :=
        congrArg (fun η : FundamentalGroup S x₀ =>
          RiemannDynamics.pathCoverDeck x₀ η (RiemannDynamics.pathCoverBase x₀)) h.symm
      _ = RiemannDynamics.pathCoverDeck x₀ δ
          (RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀)) :=
        s22c1_deck_mul x₀ γ δ _

/-- Pointwise commutation of the actual deck functions detects precisely
commutation in the fundamental group, despite the reverse-order convention. -/
theorem s22c1_deck_commute_iff {S : Type u} [TopologicalSpace S] (x₀ : S)
    (γ δ : FundamentalGroup S x₀) :
    (∀ pc : RiemannDynamics.PathCover x₀,
      RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverDeck x₀ δ pc) =
        RiemannDynamics.pathCoverDeck x₀ δ (RiemannDynamics.pathCoverDeck x₀ γ pc)) ↔
      γ * δ = δ * γ := by
  constructor
  · intro h
    exact (s22c1_deck_base_commute_iff x₀ γ δ).mp
      (h (RiemannDynamics.pathCoverBase x₀))
  · intro h pc
    rw [← s22c1_deck_mul, ← s22c1_deck_mul, h]

/-- Genus greater than one supplies concrete loop deck maps that fail to
commute already at the basepoint. Uses only HasGenus and the C2 group theorem. -/
theorem s22c1_exists_noncommuting_deck_of_genus_gt_one
    {S : Type u} [TopologicalSpace S] (x₀ : S) {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) :
    ∃ γ δ : FundamentalGroup S x₀,
      RiemannDynamics.pathCoverDeck x₀ γ
          (RiemannDynamics.pathCoverDeck x₀ δ (RiemannDynamics.pathCoverBase x₀)) ≠
        RiemannDynamics.pathCoverDeck x₀ δ
          (RiemannDynamics.pathCoverDeck x₀ γ (RiemannDynamics.pathCoverBase x₀)) := by
  obtain ⟨e⟩ := hS.2 x₀
  obtain ⟨a, b, hab⟩ := (s22c2_surfaceGroup_infinite_noncommutative hg).2
  refine ⟨e.symm a, e.symm b, ?_⟩
  intro hdeck
  have hcomm := (s22c1_deck_base_commute_iff x₀ (e.symm a) (e.symm b)).mp hdeck
  apply hab
  simpa only [map_mul, e.apply_symm_apply] using congrArg e hcomm

/-- A compact concrete path cover has a finite basepoint fiber. Loop classes
inject into that actual fiber, so the fundamental group is finite. -/
theorem s22c3_compact_pathCover_fundamentalGroup_finite
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    (x₀ : S) (hcompact : CompactSpace (RiemannDynamics.PathCover x₀)) :
    Finite (FundamentalGroup S x₀) := by
  letI : CompactSpace (RiemannDynamics.PathCover x₀) := hcompact
  have hfinite :
      (RiemannDynamics.pathCoverProj x₀ ⁻¹' ({x₀} : Set S)).Finite := by
    simpa only [Set.inter_univ] using
      (RiemannDynamics.finite_fiber_inter_compact x₀
        (K := Set.univ) isCompact_univ x₀)
  letI : Finite ↥(RiemannDynamics.pathCoverProj x₀ ⁻¹' ({x₀} : Set S)) :=
    hfinite.to_subtype
  let f : FundamentalGroup S x₀ →
      ↥(RiemannDynamics.pathCoverProj x₀ ⁻¹' ({x₀} : Set S)) :=
    fun γ => ⟨⟨x₀, γ.toPath⟩, by change x₀ = x₀; rfl⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have hp : (⟨x₀, γ.toPath⟩ : RiemannDynamics.PathCover x₀) =
        ⟨x₀, δ.toPath⟩ := congrArg Subtype.val h
    rw [RiemannDynamics.PathCover.mk.injEq] at hp
    exact eq_of_heq hp.2
  exact Finite.of_injective f hf

/-- The concrete path cover of a surface with genus greater than one cannot
be compact. Only the group-equivalence component of HasGenus is needed. -/
theorem s22c3_pathCover_not_compact_of_genus_gt_one
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    (x₀ : S) {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) :
    ¬ CompactSpace (RiemannDynamics.PathCover x₀) := by
  intro hcompact
  letI : Finite (FundamentalGroup S x₀) :=
    s22c3_compact_pathCover_fundamentalGroup_finite x₀ hcompact
  obtain ⟨e⟩ := hS.2 x₀
  have hfinite : Finite (surfaceGroup g) :=
    Finite.of_surjective e e.surjective
  letI : Infinite (surfaceGroup g) :=
    (s22c2_surfaceGroup_infinite_noncommutative hg).1
  exact hfinite.false

/-- Every complex additive character of the frozen surface presentation is
determined by its values on the 2*g generators, and every assignment extends. -/
theorem k22rr_sg_character_eval_bijective (g : ℕ) :
    Function.Bijective
      (fun χ : Additive (surfaceGroup g) →+ ℂ =>
        fun i : Fin g ⊕ Fin g =>
          χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))) := by
  constructor
  · intro χ ψ h
    have hm : χ.toMultiplicativeRight = ψ.toMultiplicativeRight := by
      apply PresentedGroup.ext
      intro i
      change Multiplicative.ofAdd
          (χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))) =
        Multiplicative.ofAdd
          (ψ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g)))
      exact congrArg Multiplicative.ofAdd (congrFun h i)
    exact AddMonoidHom.toMultiplicativeRight.injective hm
  · intro v
    let f : (Fin g ⊕ Fin g) → Multiplicative ℂ :=
      fun i => Multiplicative.ofAdd (v i)
    have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin g =>
        FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
        Set (FreeGroup (Fin g ⊕ Fin g))),
        FreeGroup.lift f r = 1 := by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      rw [map_list_prod, List.map_ofFn]
      apply List.prod_eq_one
      intro a ha
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
      rw [← hi]
      change FreeGroup.lift f
        (FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹) = 1
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_right_comm (f (Sum.inl i)) (f (Sum.inr i)) ((f (Sum.inl i))⁻¹)]
      simp only [mul_inv_cancel, one_mul]
    let φ : surfaceGroup g →* Multiplicative ℂ := PresentedGroup.toGroup hrel
    refine ⟨φ.toAdditiveLeft, ?_⟩
    funext i
    change (φ (PresentedGroup.of i : surfaceGroup g)).toAdd = v i
    exact congrArg Multiplicative.toAdd (PresentedGroup.toGroup.of hrel)

/-- The coordinate equivalence is complex linear and evaluates generators. -/
theorem k22rr_sg_character_coordinates (g : ℕ) :
    ∃ e : (Additive (surfaceGroup g) →+ ℂ) ≃ₗ[ℂ]
        ((Fin g ⊕ Fin g) → ℂ),
      ∀ (χ : Additive (surfaceGroup g) →+ ℂ) (i : Fin g ⊕ Fin g),
        e χ i = χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g)) := by
  let L : (Additive (surfaceGroup g) →+ ℂ) →ₗ[ℂ] ((Fin g ⊕ Fin g) → ℂ) :=
    { toFun := fun χ i => χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let e : (Additive (surfaceGroup g) →+ ℂ) ≃ₗ[ℂ] ((Fin g ⊕ Fin g) → ℂ) :=
    { L, Equiv.ofBijective L (k22rr_sg_character_eval_bijective g) with }
  exact ⟨e, fun _ _ => rfl⟩

/-- In particular the complex character space is linearly equivalent to
the space of arbitrary complex values on the generators. -/
theorem k22rr_sg_character_linearEquiv (g : ℕ) :
    Nonempty ((Additive (surfaceGroup g) →+ ℂ) ≃ₗ[ℂ]
      ((Fin g ⊕ Fin g) → ℂ)) := by
  obtain ⟨e, _he⟩ := k22rr_sg_character_coordinates g
  exact ⟨e⟩

/-- Finite dimensionality is included to rule out the infinite-dimensional
zero convention of finrank, including when g=0. -/
theorem k22rr_sg_character_dimension (g : ℕ) :
    FiniteDimensional ℂ (Additive (surfaceGroup g) →+ ℂ) ∧
      Module.finrank ℂ (Additive (surfaceGroup g) →+ ℂ) = 2 * g := by
  obtain ⟨e⟩ := k22rr_sg_character_linearEquiv g
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin]
  omega

/-- Real additive characters of the frozen surface group are parametrized by
arbitrary real values on its 2*g specified generators. -/
theorem k22rr_sg_real_character_eval_bijective (g : ℕ) :
    Function.Bijective
      (fun χ : Additive (surfaceGroup g) →+ ℝ =>
        fun i : Fin g ⊕ Fin g =>
          χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))) := by
  constructor
  · intro χ ψ h
    have hm : χ.toMultiplicativeRight = ψ.toMultiplicativeRight := by
      apply PresentedGroup.ext
      intro i
      change Multiplicative.ofAdd
          (χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))) =
        Multiplicative.ofAdd
          (ψ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g)))
      exact congrArg Multiplicative.ofAdd (congrFun h i)
    exact AddMonoidHom.toMultiplicativeRight.injective hm
  · intro v
    -- Reuse the proved exact-presentation extension over ℂ, then take real parts.
    obtain ⟨χ, hχ⟩ := (k22rr_sg_character_eval_bijective g).2
      (fun i => (v i : ℂ))
    let ψ : Additive (surfaceGroup g) →+ ℝ :=
      { toFun := fun a => (χ a).re
        map_zero' := by rw [map_zero]; rfl
        map_add' := by intro a b; rw [map_add]; rfl }
    refine ⟨ψ, ?_⟩
    funext i
    change (χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))).re = v i
    have hi : χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g)) =
        (v i : ℂ) := congrFun hχ i
    exact (congrArg Complex.re hi).trans (Complex.ofReal_re (v i))

/-- The real coordinate equivalence evaluates the specified generators. -/
theorem k22rr_sg_real_character_coordinates (g : ℕ) :
    ∃ e : (Additive (surfaceGroup g) →+ ℝ) ≃ₗ[ℝ]
        ((Fin g ⊕ Fin g) → ℝ),
      ∀ (χ : Additive (surfaceGroup g) →+ ℝ) (i : Fin g ⊕ Fin g),
        e χ i = χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g)) := by
  let L : (Additive (surfaceGroup g) →+ ℝ) →ₗ[ℝ] ((Fin g ⊕ Fin g) → ℝ) :=
    { toFun := fun χ i => χ (Additive.ofMul (PresentedGroup.of i : surfaceGroup g))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let e : (Additive (surfaceGroup g) →+ ℝ) ≃ₗ[ℝ] ((Fin g ⊕ Fin g) → ℝ) :=
    { L, Equiv.ofBijective L (k22rr_sg_real_character_eval_bijective g) with }
  exact ⟨e, fun _ _ => rfl⟩

/-- A real linear coordinate equivalence for the surface-group characters. -/
theorem k22rr_sg_real_character_linearEquiv (g : ℕ) :
    Nonempty ((Additive (surfaceGroup g) →+ ℝ) ≃ₗ[ℝ]
      ((Fin g ⊕ Fin g) → ℝ)) := by
  obtain ⟨e, _he⟩ := k22rr_sg_real_character_coordinates g
  exact ⟨e⟩

/-- The real character space is finite dimensional with dimension 2*g. -/
theorem k22rr_sg_real_character_dimension (g : ℕ) :
    FiniteDimensional ℝ (Additive (surfaceGroup g) →+ ℝ) ∧
      Module.finrank ℝ (Additive (surfaceGroup g) →+ ℝ) = 2 * g := by
  obtain ⟨e⟩ := k22rr_sg_real_character_linearEquiv g
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin]
  omega

/-- The original HasGenus group equivalence transports real characters at
the specified base point to the same real coordinate space. -/
theorem k22rr_sg_pi1_real_character_linearEquiv
    {S : Type u} [TopologicalSpace S] {g : ℕ}
    (hS : HasGenus S g) (x : S) :
    Nonempty ((Additive (FundamentalGroup S x) →+ ℝ) ≃ₗ[ℝ]
      ((Fin g ⊕ Fin g) → ℝ)) := by
  obtain ⟨ρ⟩ := hS.2 x
  let T : (Additive (FundamentalGroup S x) →+ ℝ) ≃ₗ[ℝ]
      (Additive (surfaceGroup g) →+ ℝ) :=
    { toFun := fun χ => χ.comp ρ.symm.toMonoidHom.toAdditive
      invFun := fun ψ => ψ.comp ρ.toMonoidHom.toAdditive
      left_inv := by
        intro χ
        apply AddMonoidHom.ext
        intro z
        change χ (Additive.ofMul (ρ.symm (ρ z.toMul))) = χ z
        rw [ρ.symm_apply_apply]
        rfl
      right_inv := by
        intro ψ
        apply AddMonoidHom.ext
        intro z
        change ψ (Additive.ofMul (ρ (ρ.symm z.toMul))) = ψ z
        rw [ρ.apply_symm_apply]
        rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  obtain ⟨e⟩ := k22rr_sg_real_character_linearEquiv g
  exact ⟨T.trans e⟩

/-- The original HasGenus assumption gives true finite dimensionality and
dimension 2*g for the real additive fundamental-group characters. -/
theorem k22rr_sg_pi1_real_character_dimension
    {S : Type u} [TopologicalSpace S] {g : ℕ}
    (hS : HasGenus S g) (x : S) :
    FiniteDimensional ℝ (Additive (FundamentalGroup S x) →+ ℝ) ∧
      Module.finrank ℝ (Additive (FundamentalGroup S x) →+ ℝ) = 2 * g := by
  obtain ⟨e⟩ := k22rr_sg_pi1_real_character_linearEquiv hS x
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin]
  omega

section
open scoped Manifold ContDiff Topology
open Set Metric Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Pending small bridge: concatenate two arbitrary continuous paths, using
the existing local primitive chain definition, without any cycle hypothesis. -/
theorem k22rr_pathPrimValue_concat (η : Jacobians.HolomorphicOneForms X)
    {x y z : X} (p : Path x y) (q : Path y z) :
    Jacobians.pathPrimValue η (p.trans q).extend
      (p.trans q).continuous_extend.continuousOn =
    Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn +
      Jacobians.pathPrimValue η q.extend q.continuous_extend.continuousOn := by
  classical
  obtain ⟨C⟩ := Jacobians.exists_primitiveChain η p.continuous_extend.continuousOn
  obtain ⟨D⟩ := Jacobians.exists_primitiveChain η q.continuous_extend.continuousOn
  let t : ℕ → ℝ := fun k =>
    if k ≤ C.n then C.t k / 2 else (D.t (k - C.n) + 1) / 2
  have ht_left : ∀ k, k ≤ C.n → t k = C.t k / 2 := by
    intro k hk
    exact ite_eq_left hk
  have ht_right : ∀ k, C.n ≤ k → t k = (D.t (k - C.n) + 1) / 2 := by
    intro k hk
    rcases eq_or_lt_of_le hk with heq | hlt
    · subst k
      rw [ht_left C.n le_rfl, C.t_stab C.n le_rfl, Nat.sub_self, D.t_zero]
      norm_num
    · exact ite_eq_right (not_le.mpr hlt)
  have htmono : Monotone t := by
    intro a b hab
    by_cases hb : b ≤ C.n
    · rw [ht_left a (hab.trans hb), ht_left b hb]
      linarith [C.mono hab]
    · have hbn : C.n ≤ b := le_of_lt (not_le.mp hb)
      rw [ht_right b hbn]
      by_cases ha : a ≤ C.n
      · rw [ht_left a ha]
        linarith [C.t_le_one a, D.t_nonneg (b - C.n)]
      · rw [ht_right a (le_of_lt (not_le.mp ha))]
        linarith [D.mono (Nat.sub_le_sub_right hab C.n)]
  let E : Jacobians.PrimitiveChain η (p.trans q).extend :=
    { n := C.n + D.n
      t := t
      t_zero := by rw [ht_left 0 (Nat.zero_le _), C.t_zero]; norm_num
      t_stab := by
        intro k hk
        rw [ht_right k (by omega), D.t_stab (k - C.n) (by omega)]
        norm_num
      mono := htmono
      U := fun k => if k < C.n then C.U k else D.U (k - C.n)
      F := fun k => if k < C.n then C.F k else D.F (k - C.n)
      isOpen := by
        intro k
        change IsOpen (if k < C.n then C.U k else D.U (k - C.n))
        split_ifs with hk
        · exact C.isOpen k
        · exact D.isOpen (k - C.n)
      prim := by
        intro k
        change Jacobians.IsLocalPrimitiveOn η
          (if k < C.n then C.F k else D.F (k - C.n))
          (if k < C.n then C.U k else D.U (k - C.n))
        split_ifs with hk
        · exact C.prim k
        · exact D.prim (k - C.n)
      covers := by
        intro k s hs
        change (p.trans q).extend s ∈
          (if k < C.n then C.U k else D.U (k - C.n))
        change t k ≤ s ∧ s ≤ t (k + 1) at hs
        by_cases hk : k < C.n
        · rw [ite_eq_left hk]
          rw [ht_left k hk.le, ht_left (k + 1) (by omega)] at hs
          have hs2 : s ≤ 1 / 2 := by linarith [hs.2, C.t_le_one (k + 1)]
          rw [Path.extend_trans_of_le_half p q hs2]
          exact C.covers k (2 * s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
        · rw [ite_eq_right hk]
          have hkn : C.n ≤ k := Nat.le_of_not_gt hk
          rw [ht_right k hkn, ht_right (k + 1) (by omega)] at hs
          have hs2 : 1 / 2 ≤ s := by linarith [hs.1, D.t_nonneg (k - C.n)]
          rw [Path.extend_trans_of_half_le p q hs2]
          apply D.covers (k - C.n) (2 * s - 1)
          rw [show k + 1 - C.n = k - C.n + 1 by omega] at hs
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩ }
  rw [Jacobians.pathPrimValue_eq η _ E, Jacobians.pathPrimValue_eq η _ C,
    Jacobians.pathPrimValue_eq η _ D]
  change (∑ k ∈ Finset.range (C.n + D.n),
    (E.F k ((p.trans q).extend (t (k + 1))) -
      E.F k ((p.trans q).extend (t k)))) = C.value + D.value
  rw [Finset.sum_range_add]
  congr 1
  · change (∑ k ∈ Finset.range C.n, _) =
      ∑ k ∈ Finset.range C.n,
        (C.F k (p.extend (C.t (k + 1))) - C.F k (p.extend (C.t k)))
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn := Finset.mem_range.mp hk
    have hF : E.F k = C.F k := ite_eq_left hkn
    rw [hF, ht_left (k + 1) (by omega), ht_left k hkn.le,
      Path.extend_trans_of_le_half p q (by linarith [C.t_le_one (k + 1)]),
      Path.extend_trans_of_le_half p q (by linarith [C.t_le_one k])]
    rw [show 2 * (C.t (k + 1) / 2) = C.t (k + 1) by ring,
      show 2 * (C.t k / 2) = C.t k by ring]
  · change (∑ k ∈ Finset.range D.n, _) =
      ∑ k ∈ Finset.range D.n,
        (D.F k (q.extend (D.t (k + 1))) - D.F k (q.extend (D.t k)))
    refine Finset.sum_congr rfl fun k hk => ?_
    have hF : E.F (C.n + k) = D.F k := by
      change (if C.n + k < C.n then C.F (C.n + k) else D.F (C.n + k - C.n)) = _
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [hF, ht_right (C.n + k + 1) (by omega), ht_right (C.n + k) (by omega)]
    rw [show C.n + k + 1 - C.n = k + 1 by omega, Nat.add_sub_cancel_left]
    rw [Path.extend_trans_of_half_le p q (by linarith [D.t_nonneg (k + 1)]),
      Path.extend_trans_of_half_le p q (by linarith [D.t_nonneg k])]
    rw [show 2 * ((D.t (k + 1) + 1) / 2) - 1 = D.t (k + 1) by ring,
      show 2 * ((D.t k + 1) / 2) - 1 = D.t k by ring]

/-- Literal quotient descent of the actual primitive value. The only supplied
law is concatenation, to be discharged by the preceding bridge; homotopy
invariance is reused from the accepted external closure. This conditional
assembly itself contains no sorry and adds no global definition or instance. -/
theorem k22rr_exists_pi1_period_of_concat
    (η : Jacobians.HolomorphicOneForms X) (x : X)
    (hconcat : ∀ {a b c : X} (p : Path a b) (q : Path b c),
      Jacobians.pathPrimValue η (p.trans q).extend
        (p.trans q).continuous_extend.continuousOn =
      Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn +
        Jacobians.pathPrimValue η q.extend q.continuous_extend.continuousOn) :
    ∃ P : Additive (FundamentalGroup X x) →+ ℂ,
      ∀ p : Path x x,
        P (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
          Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn := by
  classical
  let value : FundamentalGroup X x → ℂ := Quotient.lift
    (fun p : Path x x =>
      Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn)
    (fun p q hpq => Jacobians.pathPrimValue_eq_of_homotopic η hpq)
  have value_mul : ∀ a b : FundamentalGroup X x,
      value (a * b) = value a + value b := by
    intro a b
    refine Quotient.inductionOn₂ a b (fun p q => ?_)
    change Jacobians.pathPrimValue η (q.trans p).extend
      (q.trans p).continuous_extend.continuousOn =
      Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn +
        Jacobians.pathPrimValue η q.extend q.continuous_extend.continuousOn
    rw [hconcat q p]
    exact add_comm _ _
  let P : Additive (FundamentalGroup X x) →+ ℂ :=
    AddMonoidHom.mk' (fun a => value a.toMul) (by
      intro a b
      exact value_mul a.toMul b.toMul)
  refine ⟨P, ?_⟩
  intro p
  rfl

/-- A common subdivision for two forms, obtained by intersecting their
primitive neighbourhoods before subdividing the actual path. -/
theorem k22rr_exists_common_primitive_chains
    (η θ : Jacobians.HolomorphicOneForms X) {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    ∃ C : Jacobians.PrimitiveChain η γ,
      ∃ D : Jacobians.PrimitiveChain θ γ, C.n = D.n ∧ C.t = D.t ∧ C.U = D.U := by
  classical
  have hdata : ∀ x : X, ∃ (U : Set X) (F G : X → ℂ),
      IsOpen U ∧ x ∈ U ∧ Jacobians.IsLocalPrimitiveOn η F U ∧
        Jacobians.IsLocalPrimitiveOn θ G U := by
    intro x
    obtain ⟨U, F, hU, hxU, _, hF⟩ := Jacobians.exists_isLocalPrimitiveOn η x
    obtain ⟨V, G, hV, hxV, _, hG⟩ := Jacobians.exists_isLocalPrimitiveOn θ x
    exact ⟨U ∩ V, F, G, hU.inter hV, ⟨hxU, hxV⟩,
      hF.mono inter_subset_left, hG.mono inter_subset_right⟩
  choose U F G hU hxU hF hG using hdata
  let γ' : Icc (0 : ℝ) 1 → X := fun s => γ s
  let cover : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun s => γ' ⁻¹' U (γ' s)
  have hcover : ∀ s, IsOpen (cover s) := fun s => (hU _).preimage hγ.domRestrict
  have hcovers : (univ : Set (Icc (0 : ℝ) 1)) ⊆ ⋃ s, cover s := by
    intro s _
    exact Set.mem_iUnion.mpr ⟨s, hxU (γ' s)⟩
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hblocks⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc zero_le_one hcover hcovers
  choose s hs using hblocks
  have hblock : ∀ i r, r ∈ Icc (t i : ℝ) (t (i + 1)) → γ r ∈ U (γ' (s i)) := by
    intro i r hr
    have hr01 : r ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (t i).2.1 hr.1, le_trans hr.2 (t (i + 1)).2.2⟩
    exact hs i (show (⟨r, hr01⟩ : Icc (0 : ℝ) 1) ∈ Icc (t i) (t (i + 1)) from hr)
  let C : Jacobians.PrimitiveChain η γ :=
    { n := m + 1
      t := fun k => (t k : ℝ)
      t_zero := by exact_mod_cast ht0
      t_stab := fun k hk => by exact_mod_cast hm k (by omega)
      mono := fun a b hab => Subtype.coe_le_coe.mpr (htmono hab)
      U := fun i => U (γ' (s i))
      F := fun i => F (γ' (s i))
      isOpen := fun i => hU _
      prim := fun i => hF _
      covers := hblock }
  let D : Jacobians.PrimitiveChain θ γ :=
    { n := C.n
      t := C.t
      t_zero := C.t_zero
      t_stab := C.t_stab
      mono := C.mono
      U := C.U
      F := fun i => G (γ' (s i))
      isOpen := C.isOpen
      prim := fun i => hG _
      covers := C.covers }
  exact ⟨C, D, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Addition of the actual primitive-chain values in the form variable. -/
theorem k22rr_pathPrimValue_add (η θ : Jacobians.HolomorphicOneForms X)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    Jacobians.pathPrimValue (η + θ) γ hγ =
      Jacobians.pathPrimValue η γ hγ + Jacobians.pathPrimValue θ γ hγ := by
  classical
  obtain ⟨C, D, hn, ht, hU⟩ := k22rr_exists_common_primitive_chains η θ hγ
  let E : Jacobians.PrimitiveChain (η + θ) γ :=
    { n := C.n
      t := C.t
      t_zero := C.t_zero
      t_stab := C.t_stab
      mono := C.mono
      U := C.U
      F := fun i => C.F i + D.F i
      isOpen := C.isOpen
      prim := by
        intro i y hy
        obtain ⟨hC, hCv⟩ := C.prim i y hy
        obtain ⟨hD, hDv⟩ := D.prim i y (hU ▸ hy)
        refine ⟨hC.add hD, ?_⟩
        intro v
        change η.toFun y v + θ.toFun y v =
          mfderiv 𝓘(ℂ) 𝓘(ℂ) (C.F i + D.F i) y v
        rw [mfderiv_add hC hD]
        exact congrArg₂ (fun a b : ℂ => a + b) (hCv v) (hDv v)
      covers := C.covers }
  rw [Jacobians.pathPrimValue_eq (η + θ) _ E, Jacobians.pathPrimValue_eq η _ C,
    Jacobians.pathPrimValue_eq θ _ D]
  change (∑ i ∈ Finset.range C.n,
    ((C.F i (γ (C.t (i + 1))) + D.F i (γ (C.t (i + 1)))) -
      (C.F i (γ (C.t i)) + D.F i (γ (C.t i))))) =
    (∑ i ∈ Finset.range C.n, (C.F i (γ (C.t (i + 1))) - C.F i (γ (C.t i)))) +
      ∑ i ∈ Finset.range D.n, (D.F i (γ (D.t (i + 1))) - D.F i (γ (D.t i)))
  rw [← hn, ← ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Complex scalar multiplication of the actual primitive-chain values. -/
theorem k22rr_pathPrimValue_smul (c : ℂ) (η : Jacobians.HolomorphicOneForms X)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    Jacobians.pathPrimValue (c • η) γ hγ = c • Jacobians.pathPrimValue η γ hγ := by
  classical
  obtain ⟨C⟩ := Jacobians.exists_primitiveChain η hγ
  let E : Jacobians.PrimitiveChain (c • η) γ :=
    { n := C.n
      t := C.t
      t_zero := C.t_zero
      t_stab := C.t_stab
      mono := C.mono
      U := C.U
      F := fun i => c • C.F i
      isOpen := C.isOpen
      prim := by
        intro i y hy
        obtain ⟨hC, hCv⟩ := C.prim i y hy
        refine ⟨hC.const_smul c, ?_⟩
        intro v
        change c • η.toFun y v = mfderiv 𝓘(ℂ) 𝓘(ℂ) (c • C.F i) y v
        rw [const_smul_mfderiv hC c]
        change _ = c • mfderiv 𝓘(ℂ) 𝓘(ℂ) (C.F i) y v
        rw [hCv v]
        rfl
      covers := C.covers }
  rw [Jacobians.pathPrimValue_eq (c • η) _ E, Jacobians.pathPrimValue_eq η _ C]
  change (∑ i ∈ Finset.range C.n,
    (c • C.F i (γ (C.t (i + 1))) - c • C.F i (γ (C.t i)))) =
    c • ∑ i ∈ Finset.range C.n, (C.F i (γ (C.t (i + 1))) - C.F i (γ (C.t i)))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (smul_sub c _ _).symm

/-- Pending linear assembly: the real-part pairing on the actual basis-form
primitive values, as real additive characters of the fundamental group. No lattice
or period-cycle premise is introduced. Its surjectivity is NOT asserted. -/
theorem k22rr_exists_real_period_map (x : X) :
    ∃ P : (Fin (genus X) → ℂ) →ₗ[ℝ]
        (Additive (FundamentalGroup X x) →+ ℝ),
      ∀ (v : Fin (genus X) → ℂ) (p : Path x x),
        P v (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
        (Jacobians.pathPrimValue (Jacobians.ambientIso X v)
          p.extend p.continuous_extend.continuousOn).re := by
  classical
  have hperiod : ∀ v : Fin (genus X) → ℂ,
      ∃ Q : Additive (FundamentalGroup X x) →+ ℂ,
        ∀ p : Path x x, Q (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
          Jacobians.pathPrimValue (Jacobians.ambientIso X v)
            p.extend p.continuous_extend.continuousOn := by
    intro v
    exact k22rr_exists_pi1_period_of_concat (Jacobians.ambientIso X v) x
      (fun p q => k22rr_pathPrimValue_concat _ p q)
  choose Q hQ using hperiod
  let P : (Fin (genus X) → ℂ) →ₗ[ℝ]
      (Additive (FundamentalGroup X x) →+ ℝ) :=
    { toFun := fun v => Complex.reAddGroupHom.comp (Q v)
      map_add' := by
        intro v w
        apply AddMonoidHom.ext
        intro a
        change (Q (v + w) a).re = (Q v a).re + (Q w a).re
        obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
        refine Quotient.inductionOn a (fun p => ?_)
        rw [hQ (v + w) p, hQ v p, hQ w p, map_add,
          k22rr_pathPrimValue_add]
        exact Complex.add_re _ _
      map_smul' := by
        intro r v
        apply AddMonoidHom.ext
        intro a
        change (Q (r • v) a).re = r • (Q v a).re
        obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
        refine Quotient.inductionOn a (fun p => ?_)
        rw [hQ (r • v) p, hQ v p]
        have hform : Jacobians.ambientIso X (r • v) =
            (r : ℂ) • Jacobians.ambientIso X v := by
          have hv : r • v = (r : ℂ) • v := by
            ext i
            change r • v i = (r : ℂ) * v i
            exact Complex.real_smul
          rw [hv, map_smul]
        rw [hform, k22rr_pathPrimValue_smul]
        simp only [smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
  refine ⟨P, ?_⟩
  intro v p
  change (Q v (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧))).re = _
  rw [hQ v p]

end

section PeriodInjectivity
open scoped Manifold ContDiff Topology
open Set Metric Filter
variable [T2Space S] [CompactSpace S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S]

/-- A global real potential, locally the real part of genuine holomorphic
primitives, forces the underlying form to vanish on a compact connected surface. -/
theorem k22rr_pi_form_zero_of_real_potential (η : Jacobians.HolomorphicOneForms S)
    (U : S → ℝ) (hU : Continuous U)
    (hlocal : ∀ a : S, ∃ B : Set S, ∃ G : S → ℂ,
      IsOpen B ∧ a ∈ B ∧ Jacobians.IsLocalPrimitiveOn η G B ∧
        ∀ z ∈ B, U z = (G z).re + U a - (G a).re) : η = 0 := by
  classical
  choose B G hBo haB hG hloc using hlocal
  have hGA : ∀ a : S, AnalyticAt ℂ (G a ∘ (chartAt ℂ a).symm) (chartAt ℂ a a) := by
    intro a
    let e := chartAt ℂ a
    let T : Set ℂ := e.target ∩ e.symm ⁻¹' B a
    have hTop : IsOpen T := e.isOpen_inter_preimage_symm (hBo a)
    have hcenter : e a ∈ T := by
      refine ⟨e.map_source (mem_chart_source ℂ a), ?_⟩
      change e.symm (e a) ∈ B a
      rw [e.left_inv (mem_chart_source ℂ a)]
      exact haB a
    have hdiff : DifferentiableOn ℂ (G a ∘ e.symm) T := by
      intro z hz
      have hs : e.symm z ∈ e.source := e.map_target hz.1
      have h := Jacobians.differentiableAt_comp_chart_symm hs (hG a _ hz.2).1
      rw [e.right_inv hz.1] at h
      exact h.differentiableWithinAt
    exact hdiff.analyticAt (hTop.mem_nhds hcenter)
  obtain ⟨y₀, _, hy₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hU.continuousOn
  have hymax : ∀ z : S, U z ≤ U y₀ := fun z => hy₀ (Set.mem_univ z)
  have hkey : ∀ a : S, U a = U y₀ → ∀ᶠ z in 𝓝 a, G a z = G a a := by
    intro a ha
    let e := chartAt ℂ a
    let H : ℂ → ℂ := G a ∘ e.symm
    have hself : H (e a) = G a a := by
      change G a (e.symm (e a)) = G a a
      rw [e.left_inv (mem_chart_source ℂ a)]
    have hsymm : Filter.Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
      exact e.tendsto_symm (mem_chart_source ℂ a)
    have hRe : ∀ᶠ z in 𝓝 (e a), (H z).re ≤ (H (e a)).re := by
      filter_upwards [hsymm.eventually ((hBo a).mem_nhds (haB a))] with z hz
      have h := hymax (e.symm z)
      rw [hloc a _ hz] at h
      rw [hself]
      change (G a (e.symm z)).re ≤ (G a a).re
      linarith
    have hconst : ∀ᶠ z in 𝓝 (e a), H z = H (e a) := by
      rcases (hGA a).eventually_constant_or_nhds_le_map_nhds with hc | hopen
      · exact hc
      · exfalso
        have hV : {w : ℂ | w.re ≤ (H (e a)).re} ∈ 𝓝 (H (e a)) := hopen (by
          rw [Filter.mem_map]
          exact hRe.mono fun z hz => hz)
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
        have hmem : H (e a) + (ε / 2 : ℝ) ∈ Metric.ball (H (e a)) ε := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        have h := hball hmem
        rw [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re] at h
        linarith
    have he : Filter.Tendsto e (𝓝 a) (𝓝 (e a)) :=
      (e.continuousAt (mem_chart_source ℂ a)).tendsto
    filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ a),
      he.eventually hconst] with z hz hc
    change G a (e.symm (e z)) = G a (e.symm (e a)) at hc
    rwa [e.left_inv hz, e.left_inv (mem_chart_source ℂ a)] at hc
  have hopen : IsOpen {z : S | U z = U y₀} := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    change U a = U y₀ at ha
    filter_upwards [(hBo a).mem_nhds (haB a), hkey a ha] with z hz hc
    show U z = U y₀
    rw [hloc a z hz, hc]
    linarith
  have hlevel : {z : S | U z = U y₀} = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_eq hU continuous_const, hopen⟩ ⟨y₀, rfl⟩
  by_contra hη
  obtain ⟨a, ha⟩ := Jacobians.Dolbeault.exists_localRep_self_ne_zero η hη
  have hamax : U a = U y₀ := by
    have h : a ∈ {z : S | U z = U y₀} := by
      rw [hlevel]
      trivial
    exact h
  have hconst : G a =ᶠ[𝓝 a] (fun _ => G a a) := hkey a hamax
  have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) (G a) a = 0 := by
    rw [hconst.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
  have hzero : Jacobians.Montel.localRep η a a = 0 := by
    change η.toFun a
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) a).symmL ℂ a 1) = 0
    rw [(hG a a (haB a)).2, hmf]
    rfl
  exact ha hzero

/-- Internal construction of the real potential. The concatenation input is
the genuine path-value identity assigned to the period-map construction. -/
theorem k22rr_pi_real_potential_of_concat (η : Jacobians.HolomorphicOneForms S)
    (hconcat : ∀ {a b c : S} (p : Path a b) (q : Path b c),
      Jacobians.pathPrimValue η (p.trans q).extend
          (p.trans q).continuous_extend.continuousOn =
        Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn +
          Jacobians.pathPrimValue η q.extend q.continuous_extend.continuousOn)
    (x : S)
    (hloop : ∀ p : Path x x,
      (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re = 0) :
    ∃ U : S → ℝ, Continuous U ∧
      ∀ a : S, ∃ B : Set S, ∃ G : S → ℂ,
        IsOpen B ∧ a ∈ B ∧ Jacobians.IsLocalPrimitiveOn η G B ∧
          ∀ z ∈ B, U z = (G z).re + U a - (G a).re := by
  classical
  have : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (H := ℂ) S
  have : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  have hrefl : ∀ a : S,
      Jacobians.pathPrimValue η (Path.refl a).extend
        (Path.refl a).continuous_extend.continuousOn = 0 := by
    intro a
    let p := Path.refl a
    let A := Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn
    have hc := hconcat p p
    have ht := Jacobians.pathPrimValue_eq_of_homotopic η (Path.Homotopic.refl_trans p)
    have heq : A + 0 = A + A := (add_zero A).trans (ht.symm.trans hc)
    exact (add_left_cancel heq).symm
  have hsymm : ∀ {a b : S} (p : Path a b),
      Jacobians.pathPrimValue η p.symm.extend p.symm.continuous_extend.continuousOn =
        -Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn := by
    intro a b p
    have hc := hconcat p p.symm
    have ht := Jacobians.pathPrimValue_eq_of_homotopic η (Path.Homotopic.trans_symm p)
    apply eq_neg_iff_add_eq_zero.mpr
    rw [add_comm]
    exact hc.symm.trans (ht.trans (hrefl a))
  have hind : ∀ {z : S} (p q : Path x z),
      (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re =
        (Jacobians.pathPrimValue η q.extend q.continuous_extend.continuousOn).re := by
    intro z p q
    have h := hloop (p.trans q.symm)
    rw [hconcat p q.symm, hsymm q, Complex.add_re, Complex.neg_re] at h
    linarith
  let U : S → ℝ := fun z =>
    (Jacobians.pathPrimValue η (PathConnectedSpace.somePath x z).extend
      (PathConnectedSpace.somePath x z).continuous_extend.continuousOn).re
  have hlocal : ∀ a : S, ∃ B : Set S, ∃ G : S → ℂ,
      IsOpen B ∧ a ∈ B ∧ Jacobians.IsLocalPrimitiveOn η G B ∧
        ∀ z ∈ B, U z = (G z).re + U a - (G a).re := by
    intro a
    obtain ⟨B, G, hBo, haB, hBpc, hG⟩ := Jacobians.exists_isLocalPrimitiveOn η a
    refine ⟨B, G, hBo, haB, hG, ?_⟩
    intro z hz
    let hjoin := hBpc.joinedIn a haB z hz
    let q : Path a z := hjoin.somePath
    have hqB : ∀ τ : unitInterval, q τ ∈ B := hjoin.somePath_mem
    have h1 := hind ((PathConnectedSpace.somePath x a).trans q)
      (PathConnectedSpace.somePath x z)
    have h2 := Jacobians.pathPrimValue_trans_primitive_block η
      (PathConnectedSpace.somePath x a) hBo hG q hqB
    change U z = (G z).re + U a - (G a).re
    change _ = U z at h1
    rw [h2, Complex.add_re, Complex.sub_re] at h1
    change U a + ((G z).re - (G a).re) = U z at h1
    linarith
  refine ⟨U, ?_, hlocal⟩
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨B, G, hBo, haB, hG, hloc⟩ := hlocal a
  have heq : U =ᶠ[𝓝 a] (fun z => (G z).re + U a - (G a).re) := by
    filter_upwards [hBo.mem_nhds haB] with z hz
    exact hloc z hz
  have hGC : ContinuousAt G a := (hG a haB).1.continuousAt
  have hcont : ContinuousAt (fun z => (G z).re + U a - (G a).re) a :=
    ((Complex.continuous_re.continuousAt.comp hGC).add continuousAt_const).sub
      continuousAt_const
  exact hcont.congr_of_eventuallyEq heq

/-- Zero real based periods give a global continuous real potential, with
the actual local holomorphic primitive germs. -/
theorem k22rr_pi_real_potential (η : Jacobians.HolomorphicOneForms S) (x : S)
    (hloop : ∀ p : Path x x,
      (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re = 0) :
    ∃ U : S → ℝ, Continuous U ∧
      ∀ a : S, ∃ B : Set S, ∃ G : S → ℂ,
        IsOpen B ∧ a ∈ B ∧ Jacobians.IsLocalPrimitiveOn η G B ∧
          ∀ z ∈ B, U z = (G z).re + U a - (G a).re := by
  exact k22rr_pi_real_potential_of_concat η (k22rr_pathPrimValue_concat η) x hloop

/-- A holomorphic form whose genuine real based periods vanish is zero. -/
theorem k22rr_pi_form_zero_of_real_periods (η : Jacobians.HolomorphicOneForms S) (x : S)
    (hloop : ∀ p : Path x x,
      (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re = 0) :
    η = 0 := by
  obtain ⟨U, hU, hlocal⟩ := k22rr_pi_real_potential η x hloop
  exact k22rr_pi_form_zero_of_real_potential η U hU hlocal

/-- The actual real period-character map is injective. -/
theorem k22rr_pi_injective (x : S)
    (P : (Fin (genus S) → ℂ) →ₗ[ℝ]
      (Additive (FundamentalGroup S x) →+ ℝ))
    (hP : ∀ (v : Fin (genus S) → ℂ) (p : Path x x),
      P v (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
      (Jacobians.pathPrimValue (Jacobians.ambientIso S v)
        p.extend p.continuous_extend.continuousOn).re) :
    Function.Injective P := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hη : Jacobians.ambientIso S v = 0 :=
    k22rr_pi_form_zero_of_real_periods (Jacobians.ambientIso S v) x (by
      intro p
      rw [← hP v p, hv]
      rfl)
  apply (Jacobians.ambientIso S).injective
  rw [map_zero]
  exact hη

end PeriodInjectivity

/-- An injective real linear map from complex analytic-genus coordinates to
real fundamental-group characters bounds analytic genus by the original g.
The actual period map and its injectivity remain separate obligations. -/
theorem k22rr_sg_analytic_genus_le_of_period_injective
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {g : ℕ} (hS : HasGenus S g) (x : S)
    (P : (Fin (genus S) → ℂ) →ₗ[ℝ] (Additive (FundamentalGroup S x) →+ ℝ))
    (hP : Function.Injective P) : genus S ≤ g := by
  obtain ⟨hfinite, hdim⟩ := k22rr_sg_pi1_real_character_dimension hS x
  letI := hfinite
  have hsource : Module.finrank ℝ (Fin (genus S) → ℂ) = 2 * genus S := by
    rw [finrank_real_of_complex, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hbound := LinearMap.finrank_le_finrank_of_injective (f := P) hP
  rw [hsource, hdim] at hbound
  omega

/-- A bijective real linear map from complex analytic-genus coordinates to
real fundamental-group characters identifies the two genus numbers.
This conditional assembly does not establish such a map or its bijectivity. -/
theorem k22rr_sg_analytic_genus_eq_of_period_bijective
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {g : ℕ} (hS : HasGenus S g) (x : S)
    (P : (Fin (genus S) → ℂ) →ₗ[ℝ] (Additive (FundamentalGroup S x) →+ ℝ))
    (hP : Function.Bijective P) : genus S = g := by
  obtain ⟨hfinite, hdim⟩ := k22rr_sg_pi1_real_character_dimension hS x
  letI := hfinite
  have hsource : Module.finrank ℝ (Fin (genus S) → ℂ) = 2 * genus S := by
    rw [finrank_real_of_complex, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hlower := LinearMap.finrank_le_finrank_of_injective (f := P) hP.1
  have hupper := LinearMap.finrank_le_finrank_of_surjective (f := P) hP.2
  rw [hsource, hdim] at hlower hupper
  omega

section
open scoped Manifold ContDiff Topology
open Set Metric Filter
open TopologicalSpace (Opens)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Reversing a composition of actual path classes reverses its factors. -/
theorem k22rr_path_class_symm_trans {a b c : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) :
    (p.trans q).symm = q.symm.trans p.symm := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
    Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_symm]

/-- The real character respects chronological loop composition, although the
fundamental group's multiplication has the reverse chronological convention. -/
theorem k22rr_real_character_trans (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ)
    (p q : Path.Homotopic.Quotient x x) :
    χ (Additive.ofMul (FundamentalGroup.fromPath (p.trans q))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath p)) +
        χ (Additive.ofMul (FundamentalGroup.fromPath q)) := by
  exact (χ.map_add (Additive.ofMul (FundamentalGroup.fromPath q))
    (Additive.ofMul (FundamentalGroup.fromPath p))).trans (add_comm _ _)

/-- Transition characters from three paths satisfy the exact additive cocycle law. -/
theorem k22rr_real_character_cocycle (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ) {y : X}
    (a b c : Path.Homotopic.Quotient x y) :
    χ (Additive.ofMul (FundamentalGroup.fromPath (a.trans b.symm))) +
      χ (Additive.ofMul (FundamentalGroup.fromPath (b.trans c.symm))) =
        χ (Additive.ofMul (FundamentalGroup.fromPath (a.trans c.symm))) := by
  rw [← k22rr_real_character_trans]
  rw [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc b.symm b c.symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- Appending the same path to two based path classes preserves their transition. -/
theorem k22rr_real_character_common_tail (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ) {y z : X}
    (a b : Path.Homotopic.Quotient x y) (p : Path.Homotopic.Quotient y z) :
    χ (Additive.ofMul (FundamentalGroup.fromPath
      ((a.trans p).trans (b.trans p).symm))) =
        χ (Additive.ofMul (FundamentalGroup.fromPath (a.trans b.symm))) := by
  rw [k22rr_path_class_symm_trans, Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc p p.symm b.symm,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

/-- A finite disk cover has based local path classes which continue along every
path contained in the disk. No universal-cover lift formula is supplied. -/
theorem k22rr_exists_disk_path_classes (x : X) :
    ∃ (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
      (a : ∀ i : 𝔇.ι, ∀ y : X, Path.Homotopic.Quotient x y),
      ∀ i, ∀ y ∈ 𝔇.U i, ∀ z ∈ 𝔇.U i, ∀ p : Path y z,
        (∀ t, p t ∈ 𝔇.U i) → (a i y).trans ⟦p⟧ = a i z := by
  classical
  let 𝔇 := Jacobians.Dolbeault.chartDiskCover (X := X)
  letI (i : 𝔇.ι) : SimplyConnectedSpace ↥(𝔇.U i) :=
    Jacobians.Dolbeault.chartDiskCover_simplyConnected i
  have hc : ∀ i : 𝔇.ι, 𝔇.center i ∈ 𝔇.U i := by
    intro i
    exact Jacobians.Dolbeault.mem_chartDiskNbhd _
  let b (i : 𝔇.ι) := PathConnectedSpace.somePath x (𝔇.center i)
  let d (i : 𝔇.ι) (y : 𝔇.U i) :=
    PathConnectedSpace.somePath (⟨𝔇.center i, hc i⟩ : 𝔇.U i) y
  let a : ∀ i : 𝔇.ι, ∀ y : X, Path.Homotopic.Quotient x y := fun i y =>
    if hy : y ∈ 𝔇.U i then
      Path.Homotopic.Quotient.mk ((b i).trans ((d i ⟨y, hy⟩).map continuous_subtype_val))
    else Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)
  refine ⟨𝔇, a, ?_⟩
  intro i y hy z hz p hp
  let p' : Path (⟨y, hy⟩ : 𝔇.U i) ⟨z, hz⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk hp
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  have heq : (⟦(d i ⟨y, hy⟩).trans p'⟧ : Path.Homotopic.Quotient _ _) =
      ⟦d i ⟨z, hz⟩⟧ :=
    Quotient.sound (SimplyConnectedSpace.paths_homotopic _ _)
  have hmap := congrArg (fun q => Path.Homotopic.Quotient.map q
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(𝔇.U i), X))) heq
  have hpmap : p'.map continuous_subtype_val = p := by
    ext t
    rfl
  change (⟦((d i ⟨y, hy⟩).trans p').map continuous_subtype_val⟧ :
    Path.Homotopic.Quotient _ _) = ⟦(d i ⟨z, hz⟩).map continuous_subtype_val⟧ at hmap
  rw [Path.map_trans, hpmap] at hmap
  change (Path.Homotopic.Quotient.mk ((d i ⟨y, hy⟩).map continuous_subtype_val)).trans
    (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk ((d i ⟨z, hz⟩).map continuous_subtype_val) at hmap
  have hay : a i y = (Path.Homotopic.Quotient.mk (b i)).trans
      (Path.Homotopic.Quotient.mk ((d i ⟨y, hy⟩).map continuous_subtype_val)) := by
    change (if hy : y ∈ 𝔇.U i then _ else _) = _
    rw [dite_eq_left hy]
    rfl
  have haz : a i z = (Path.Homotopic.Quotient.mk (b i)).trans
      (Path.Homotopic.Quotient.mk ((d i ⟨z, hz⟩).map continuous_subtype_val)) := by
    change (if hz : z ∈ 𝔇.U i then _ else _) = _
    rw [dite_eq_left hz]
    rfl
  change (a i y).trans (Path.Homotopic.Quotient.mk p) = a i z
  rw [hay, haz, Path.Homotopic.Quotient.trans_assoc]
  exact congrArg (fun q => (Path.Homotopic.Quotient.mk (b i)).trans q) hmap

/-- A transition character is locally constant on actual overlaps, using a
small path-connected neighborhood and the proven continuation law. -/
theorem k22rr_real_transition_locally_constant (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ)
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
    (a : ∀ i : 𝔇.ι, ∀ y : X, Path.Homotopic.Quotient x y)
    (ha : ∀ i, ∀ y ∈ 𝔇.U i, ∀ z ∈ 𝔇.U i, ∀ p : Path y z,
      (∀ t, p t ∈ 𝔇.U i) → (a i y).trans ⟦p⟧ = a i z)
    (i j : 𝔇.ι) {y : X} (hy : y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
      ∀ z ∈ W,
        χ (Additive.ofMul (FundamentalGroup.fromPath ((a i z).trans (a j z).symm))) =
          χ (Additive.ofMul (FundamentalGroup.fromPath ((a i y).trans (a j y).symm))) := by
  obtain ⟨W, ⟨hWo, hyW, hWpc⟩, hWsub⟩ :=
    (isOpen_isPathConnected_basis y).mem_iff.mp ((𝔇.U i).isOpen.inter (𝔇.U j).isOpen |>.mem_nhds hy)
  refine ⟨W, hWo, hyW, hWsub, ?_⟩
  intro z hzW
  have hjoin := hWpc.joinedIn y hyW z hzW
  have hi := ha i y hy.1 z (hWsub hzW).1 hjoin.somePath
    (fun t => (hWsub (hjoin.somePath_mem t)).1)
  have hj := ha j y hy.2 z (hWsub hzW).2 hjoin.somePath
    (fun t => (hWsub (hjoin.somePath_mem t)).2)
  rw [← hi, ← hj]
  exact k22rr_real_character_common_tail x χ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- A real locally constant transition cocycle has actual real smooth local
potentials, obtained from a genuine subordinate partition of unity. -/
theorem k22rr_exists_smooth_real_cocycle_potentials
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X) (c : 𝔇.ι → 𝔇.ι → X → ℝ)
    (hc : ∀ i j k y, c i j y + c j k y = c i k y)
    (hlc : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, c i j z = c i j y) :
    ∃ F : 𝔇.ι → X → ℂ,
      (∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i)) ∧
      (∀ i y, (F i y).im = 0) ∧
      ∀ i j y, F i y - F j y = (c i j y : ℂ) := by
  classical
  obtain ⟨ρ, hρ⟩ := Jacobians.Dolbeault.exists_smoothPartitionOfUnity_subordinate 𝔇.toFiniteCover
  let F : 𝔇.ι → X → ℂ := fun i y => ∑ j, ((ρ j y * c i j y : ℝ) : ℂ)
  have hsum : ∀ y : X, ∑ j, ρ j y = 1 := by
    intro y
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ y)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i y hy
    refine (show ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) y from ?_).contMDiffWithinAt
    apply contMDiffAt_finsetSum
    intro j _
    by_cases hj : y ∈ tsupport (ρ j)
    · obtain ⟨W, hWo, hyW, _, hW⟩ := hlc i j y ⟨hy, hρ j hj⟩
      have hceq : c i j =ᶠ[𝓝 y] fun _ => c i j y := by
        filter_upwards [hWo.mem_nhds hyW] with z hz
        exact hW z hz
      have hcAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (c i j) y :=
        contMDiffAt_const.congr_of_eventuallyEq hceq
      exact Complex.ofRealCLM.contMDiff.contMDiffAt.comp y ((ρ j).contMDiff y |>.mul hcAt)
    · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport (ρ j)).isOpen_compl.mem_nhds hj] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, Complex.ofReal_zero]
  · intro i y
    change (∑ j, ((ρ j y * c i j y : ℝ) : ℂ)).im = 0
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_im _
  · intro i j y
    change (∑ k, ((ρ k y * c i k y : ℝ) : ℂ)) -
      (∑ k, ((ρ k y * c j k y : ℝ) : ℂ)) = (c i j y : ℂ)
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub]
    apply congrArg Complex.ofReal
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ k, (ρ k y * c i k y - ρ k y * c j k y)) = ∑ k, ρ k y * c i j y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hc i j k y]
        ring
      _ = c i j y := by rw [← Finset.sum_mul, hsum y, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The actual differential of a function smooth at a point is a smooth
cotangent section near that point, with the trivial target fiber identified. -/
theorem k22rr_local_mfderiv_contMDiff (f : X → ℂ) {x : X}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) f x) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun y => (⟨y, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f y⟩ :
        Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
          (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] (Bundle.Trivial X ℂ) y))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have h := hf.mfderiv_const (m := (⊤ : ℕ∞)) (by simp)
  convert h using 3 with y
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt',
    TangentBundle.continuousLinearMapAt_trivializationAt, ContinuousLinearMap.id_comp, mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-- Locally constant differences make the genuine projected local differentials
descend to an existing smooth (0,1) form, rather than a supplied formal cocycle. -/
theorem k22rr_exists_glued_local_differentials
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X) (F : 𝔇.ι → X → ℂ)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i))
    (hlc : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, F i z - F j z = F i y - F j y) :
    ∃ μ : Jacobians.Dolbeault.SmoothCOneForms X,
      μ ∈ Jacobians.Dolbeault.OneFormsZeroOne X ∧
      ∀ i, ∀ y ∈ 𝔇.U i, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
        μ.toFun y v =
          (Jacobians.Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y)) v := by
  classical
  have hcov : ∀ y : X, ∃ i, y ∈ 𝔇.U i := by
    have h : (univ : Set X) ⊆ ⋃ i, (𝔇.U i : Set X) := by
      rw [univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔇.covers]
      rfl
    intro y
    exact mem_iUnion.mp (h (mem_univ y))
  choose index hindex using hcov
  have hdiff : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y : TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℂ) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F j) y := by
    intro i j y hy
    obtain ⟨W, hWo, hyW, _, hW⟩ := hlc i j y hy
    have heq : F i =ᶠ[𝓝 y] F j + fun _ => F i y - F j y := by
      filter_upwards [hWo.mem_nhds hyW] with z hz
      have h := hW z hz
      change F i z = F j z + (F i y - F j y)
      linear_combination h
    have hj : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F j) y :=
      ((hF j).contMDiffAt ((𝔇.U j).isOpen.mem_nhds hy.2)).mdifferentiableAt (by simp)
    rw [heq.mfderiv_eq, mfderiv_add hj mdifferentiableAt_const, mfderiv_const]
    exact add_zero _
  let α : Jacobians.Dolbeault.SmoothCOneForms X :=
    { toFun := fun y => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F (index y)) y
      contMDiff_toFun := by
        intro y
        have h := k22rr_local_mfderiv_contMDiff (F (index y))
          ((hF (index y)).contMDiffAt ((𝔇.U (index y)).isOpen.mem_nhds (hindex y)))
        refine h.congr_of_eventuallyEq ?_
        filter_upwards [(𝔇.U (index y)).isOpen.mem_nhds (hindex y)] with z hz
        exact congrArg (Bundle.TotalSpace.mk z) (hdiff (index z) (index y) z ⟨hindex z, hz⟩) }
  refine ⟨Jacobians.Dolbeault.proj01L α, LinearMap.mem_range_self _ _, ?_⟩
  intro i y hy v
  change Jacobians.Dolbeault.proj01 (α.toFun y) v = _
  change Jacobians.Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F (index y)) y) v = _
  rw [hdiff (index y) i y ⟨hindex y, hy⟩]

/-- Endpoint casts commute with actual path-class composition. -/
theorem k22rr_path_class_cast_trans {a b c a' b' c' : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c)
    (ha : a' = a) (hb : b' = b) (hc : c' = c) :
    (p.trans q).cast ha hc = (p.cast ha hb).trans (q.cast hb hc) := by
  cases ha
  cases hb
  cases hc
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Casting both endpoints of the constant path gives the constant path. -/
theorem k22rr_path_class_cast_refl {a b : X} (h : b = a) :
    (Path.Homotopic.Quotient.refl a).cast h h = Path.Homotopic.Quotient.refl b := by
  cases h
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- Casting the common endpoint of two based paths preserves their transition. -/
theorem k22rr_real_character_cast_endpoint (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ) {y z : X}
    (p q : Path.Homotopic.Quotient x y) (h : z = y) :
    χ (Additive.ofMul (FundamentalGroup.fromPath (p.trans q.symm))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath
        ((p.cast rfl h).trans (q.cast rfl h).symm))) := by
  cases h
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Consecutive prefixes of a loop differ by its genuine intervening subpath. -/
theorem k22rr_path_prefix_trans (x : X) (p : Path x x) (s t : unitInterval) :
    ((Path.Homotopic.Quotient.mk (p.subpath 0 s)).cast p.source.symm rfl).trans
        (Path.Homotopic.Quotient.mk (p.subpath s t)) =
      (Path.Homotopic.Quotient.mk (p.subpath 0 t)).cast p.source.symm rfl := by
  calc
    _ = ((Path.Homotopic.Quotient.mk (p.subpath 0 s)).trans
        (Path.Homotopic.Quotient.mk (p.subpath s t))).cast p.source.symm rfl := by
      simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using
        (k22rr_path_class_cast_trans _ _ p.source.symm rfl rfl).symm
    _ = _ := congrArg (fun q => q.cast p.source.symm rfl)
      (Path.Homotopic.mk_subpath_trans_mk_subpath p 0 s t)

/-- Equal continuation laws make differences of transition characters agree. -/
theorem k22rr_real_character_increment (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ) {y z : X}
    (a b u : Path.Homotopic.Quotient x y)
    (A B v : Path.Homotopic.Quotient x z) (p : Path.Homotopic.Quotient y z)
    (hA : a.trans p = A) (hB : b.trans p = B) :
    χ (Additive.ofMul (FundamentalGroup.fromPath (A.trans v.symm))) -
        χ (Additive.ofMul (FundamentalGroup.fromPath (a.trans u.symm))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath (B.trans v.symm))) -
        χ (Additive.ofMul (FundamentalGroup.fromPath (b.trans u.symm))) := by
  have hz := k22rr_real_character_cocycle x χ A B v
  have hy := k22rr_real_character_cocycle x χ a b u
  have ht := k22rr_real_character_common_tail x χ a b p
  rw [hA, hB] at ht
  linarith

/-- Every continuous loop has an actual monotone finite subdivision in the disk cover. -/
theorem k22rr_exists_disk_loop_subdivision (x : X)
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X) (p : Path x x) :
    ∃ (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
      t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) ∧
      ∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k) := by
  classical
  have hcov : ∀ y : X, ∃ i, y ∈ 𝔇.U i := by
    have h : (univ : Set X) ⊆ ⋃ i, (𝔇.U i : Set X) := by
      rw [univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔇.covers]
      rfl
    intro y
    exact mem_iUnion.mp (h (mem_univ y))
  choose index hindex using hcov
  let γ : Icc (0 : ℝ) 1 → X := fun s => p.extend s
  let cover : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) :=
    fun s => γ ⁻¹' 𝔇.U (index (γ s))
  have hcover : ∀ s, IsOpen (cover s) :=
    fun s => (𝔇.U _).isOpen.preimage (p.continuous_extend.comp continuous_subtype_val)
  have hcovers : (univ : Set (Icc (0 : ℝ) 1)) ⊆ ⋃ s, cover s := by
    intro s _
    exact Set.mem_iUnion.mpr ⟨s, hindex (γ s)⟩
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hblocks⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc zero_le_one hcover hcovers
  choose s hs using hblocks
  refine ⟨m + 1, (fun k => (t k : ℝ)), (fun k => index (γ (s k))), ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast ht0
  · exact_mod_cast hm (m + 1) (by omega)
  · exact fun a b hab => Subtype.coe_le_coe.mpr (htmono hab)
  · exact fun k _ => (t k).2
  · intro k _ r hr
    have hr01 : r ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (t k).2.1 hr.1, le_trans hr.2 (t (k + 1)).2.2⟩
    exact hs k (show (⟨r, hr01⟩ : Icc (0 : ℝ) 1) ∈ Icc (t k) (t (k + 1)) from hr)

/-- A dependent family of based path classes respects endpoint casts. -/
theorem k22rr_based_path_family_cast (x : X)
    (b : ∀ y : X, Path.Homotopic.Quotient x y) {y z : X} (h : z = y) :
    (b y).cast rfl h = b z := by
  cases h
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- The difference of the first and last prefix transition characters is the loop character. -/
theorem k22rr_path_prefix_character_endpoints (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ) (p : Path x x)
    (b : ∀ y : X, Path.Homotopic.Quotient x y) :
    χ (Additive.ofMul (FundamentalGroup.fromPath
        (((Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm rfl).trans
          (b (p 1)).symm))) -
      χ (Additive.ofMul (FundamentalGroup.fromPath
        (((Path.Homotopic.Quotient.mk (p.subpath 0 0)).cast p.source.symm rfl).trans
          (b (p 0)).symm))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) := by
  let q : ∀ s : unitInterval, Path.Homotopic.Quotient x (p s) :=
    fun s => (Path.Homotopic.Quotient.mk (p.subpath 0 s)).cast p.source.symm rfl
  have hq0 : (q 0).cast rfl p.source.symm = Path.Homotopic.Quotient.refl x := by
    change ((Path.Homotopic.Quotient.mk (p.subpath 0 0)).cast p.source.symm rfl).cast
      rfl p.source.symm = _
    rw [Path.subpath_self, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.cast_cast]
    exact k22rr_path_class_cast_refl p.source.symm
  have hq1 : (q 1).cast rfl p.target.symm = Path.Homotopic.Quotient.mk p := by
    change ((Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm rfl).cast
      rfl p.target.symm = _
    rw [Path.subpath_zero_one, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_cast]
    change (Path.Homotopic.Quotient.mk p).cast rfl rfl = _
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  have h0 := k22rr_real_character_cast_endpoint x χ (q 0) (b (p 0)) p.source.symm
  have h1 := k22rr_real_character_cast_endpoint x χ (q 1) (b (p 1)) p.target.symm
  rw [hq0, k22rr_based_path_family_cast, Path.Homotopic.Quotient.refl_trans] at h0
  rw [hq1, k22rr_based_path_family_cast, k22rr_real_character_trans] at h1
  change χ (Additive.ofMul (FundamentalGroup.fromPath ((q 1).trans (b (p 1)).symm))) -
    χ (Additive.ofMul (FundamentalGroup.fromPath ((q 0).trans (b (p 0)).symm))) = _
  rw [h1, h0]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Every valid subdivision evaluates the character by its literal potential increments. -/
theorem k22rr_disk_potential_character_sum (x : X)
    (χ : Additive (FundamentalGroup X x) →+ ℝ)
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
    (a : ∀ i : 𝔇.ι, ∀ y : X, Path.Homotopic.Quotient x y)
    (ha : ∀ i, ∀ y ∈ 𝔇.U i, ∀ z ∈ 𝔇.U i, ∀ p : Path y z,
      (∀ t, p t ∈ 𝔇.U i) → (a i y).trans ⟦p⟧ = a i z)
    (F : 𝔇.ι → X → ℂ)
    (hF : ∀ i j y, F i y - F j y =
      (χ (Additive.ofMul (FundamentalGroup.fromPath ((a i y).trans (a j y).symm))) : ℂ))
    (p : Path x x) (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι)
    (ht0 : t 0 = 0) (htN : t N = 1) (htmono : Monotone t)
    (ht01 : ∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1)
    (hcover : ∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) :
    (∑ k ∈ Finset.range N,
      (F (σ k) (p.extend (t (k + 1))) - F (σ k) (p.extend (t k)))) =
        (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ) := by
  classical
  have hcov : ∃ j : 𝔇.ι, x ∈ 𝔇.U j := by
    have h : (univ : Set X) ⊆ ⋃ i, (𝔇.U i : Set X) := by
      rw [univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔇.covers]
      rfl
    exact mem_iUnion.mp (h (mem_univ x))
  obtain ⟨j, _⟩ := hcov
  let τ : ℕ → unitInterval := fun k => if hk : k ≤ N then ⟨t k, ht01 k hk⟩ else 1
  have hτ : ∀ k ≤ N, (τ k : ℝ) = t k := by
    intro k hk
    simp only [τ, dite_eq_left hk]
  have hτ0 : τ 0 = 0 := Subtype.ext ((hτ 0 (Nat.zero_le _)).trans ht0)
  have hτN : τ N = 1 := Subtype.ext ((hτ N (le_refl _)).trans htN)
  have heval : ∀ k ≤ N, p.extend (t k) = p (τ k) := by
    intro k hk
    rw [← hτ k hk]
    exact p.extend_extends' (τ k)
  let q : ∀ s : unitInterval, Path.Homotopic.Quotient x (p s) :=
    fun s => (Path.Homotopic.Quotient.mk (p.subpath 0 s)).cast p.source.symm rfl
  let R : unitInterval → ℝ := fun s =>
    χ (Additive.ofMul (FundamentalGroup.fromPath ((q s).trans (a j (p s)).symm)))
  let Z : ℕ → ℂ := fun k => (R (τ k) : ℂ) + F j (p (τ k))
  have hinc : ∀ k < N,
      F (σ k) (p.extend (t (k + 1))) - F (σ k) (p.extend (t k)) = Z (k + 1) - Z k := by
    intro k hk
    have hkN : k ≤ N := by omega
    have hk1N : k + 1 ≤ N := by omega
    have hle : τ k ≤ τ (k + 1) := by
      change (τ k : ℝ) ≤ (τ (k + 1) : ℝ)
      rw [hτ k hkN, hτ (k + 1) hk1N]
      exact htmono (by omega)
    have hinside : ∀ s, (p.subpath (τ k) (τ (k + 1))) s ∈ 𝔇.U (σ k) := by
      intro s
      have hs : (p.subpath (τ k) (τ (k + 1))) s ∈ Set.range (p.subpath (τ k) (τ (k + 1))) :=
        mem_range_self s
      rw [Path.range_subpath_of_le p _ _ hle] at hs
      obtain ⟨u, hu, heq⟩ := hs
      rw [← heq, ← p.extend_extends' u]
      apply hcover k hk
      change (t k ≤ (u : ℝ)) ∧ ((u : ℝ) ≤ t (k + 1))
      rw [← hτ k hkN, ← hτ (k + 1) hk1N]
      exact hu
    have hleft : p (τ k) ∈ 𝔇.U (σ k) := by
      rw [← heval k hkN]
      exact hcover k hk _ ⟨le_refl _, htmono (by omega)⟩
    have hright : p (τ (k + 1)) ∈ 𝔇.U (σ k) := by
      rw [← heval (k + 1) hk1N]
      exact hcover k hk _ ⟨htmono (by omega), le_refl _⟩
    have hA := ha (σ k) _ hleft _ hright (p.subpath (τ k) (τ (k + 1))) hinside
    have hB := k22rr_path_prefix_trans x p (τ k) (τ (k + 1))
    have hχ := k22rr_real_character_increment x χ
      (a (σ k) (p (τ k))) (q (τ k)) (a j (p (τ k)))
      (a (σ k) (p (τ (k + 1)))) (q (τ (k + 1))) (a j (p (τ (k + 1))))
      (Path.Homotopic.Quotient.mk (p.subpath (τ k) (τ (k + 1)))) hA hB
    have hfleft := hF (σ k) j (p (τ k))
    have hfright := hF (σ k) j (p (τ (k + 1)))
    have hχC := congrArg Complex.ofReal hχ
    rw [Complex.ofReal_sub, Complex.ofReal_sub] at hχC
    change _ = (R (τ (k + 1)) : ℂ) - (R (τ k) : ℂ) at hχC
    rw [heval k hkN, heval (k + 1) hk1N]
    change _ = ((R (τ (k + 1)) : ℂ) + F j (p (τ (k + 1)))) -
      ((R (τ k) : ℂ) + F j (p (τ k)))
    linear_combination hfright - hfleft + hχC
  calc
    _ = ∑ k ∈ Finset.range N, (Z (k + 1) - Z k) := by
      exact Finset.sum_congr rfl fun k hk => hinc k (Finset.mem_range.mp hk)
    _ = Z N - Z 0 := Finset.sum_range_sub Z N
    _ = (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ) := by
      change ((R (τ N) : ℂ) + F j (p (τ N))) - ((R (τ 0) : ℂ) + F j (p (τ 0))) =
        (χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) : ℂ)
      rw [hτN, hτ0, p.source, p.target]
      have hR := k22rr_path_prefix_character_endpoints x χ p (a j)
      change R 1 - R 0 = _ at hR
      have hRC := congrArg Complex.ofReal hR
      rw [Complex.ofReal_sub] at hRC
      linear_combination hRC

set_option backward.isDefEq.respectTransparency false in
/-- A genuine real character has local real smooth potentials on a finite
chart-disk cover. Their locally constant overlap differences make their actual
Dolbeault differentials a global smooth (0,1) form. Valid finite subdivisions
exist for every continuous loop, and every such subdivision evaluates the
character by the literal sum of local potential increments. -/
theorem k22rr_exists_real_character_potentials
    (x : X) (χ : Additive (FundamentalGroup X x) →+ ℝ) :
    ∃ (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
      (F : 𝔇.ι → X → ℂ) (μ : Jacobians.Dolbeault.SmoothCOneForms X),
      μ ∈ Jacobians.Dolbeault.OneFormsZeroOne X ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i)) ∧
      (∀ i, ∀ y ∈ 𝔇.U i, (F i y).im = 0) ∧
      (∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
        ∃ W : Set X, IsOpen W ∧ y ∈ W ∧
          W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
          ∀ z ∈ W, F i z - F j z = F i y - F j y) ∧
      (∀ i, ∀ y ∈ 𝔇.U i, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
        μ.toFun y v =
          (Jacobians.Dolbeault.proj01
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y)) v) ∧
      (∀ p : Path x x, ∃ (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
        t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
        (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) ∧
        ∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) ∧
      (∀ (p : Path x x) (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
        t 0 = 0 → t N = 1 → Monotone t →
        (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) →
        (∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) →
        (∑ k ∈ Finset.range N,
          (F (σ k) (p.extend (t (k + 1))) - F (σ k) (p.extend (t k)))) =
          (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ)) := by
  classical
  obtain ⟨𝔇, a, ha⟩ := k22rr_exists_disk_path_classes x
  let c : 𝔇.ι → 𝔇.ι → X → ℝ := fun i j y =>
    χ (Additive.ofMul (FundamentalGroup.fromPath ((a i y).trans (a j y).symm)))
  have hc : ∀ i j k y, c i j y + c j k y = c i k y := by
    intro i j k y
    exact k22rr_real_character_cocycle x χ (a i y) (a j y) (a k y)
  have hlc : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, c i j z = c i j y := by
    intro i j y hy
    exact k22rr_real_transition_locally_constant x χ 𝔇 a ha i j hy
  obtain ⟨F, hF, hreal, hFd⟩ := k22rr_exists_smooth_real_cocycle_potentials 𝔇 c hc hlc
  have hFlc : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, F i z - F j z = F i y - F j y := by
    intro i j y hy
    obtain ⟨W, hWo, hyW, hWsub, hW⟩ := hlc i j y hy
    refine ⟨W, hWo, hyW, hWsub, ?_⟩
    intro z hz
    rw [hFd i j z, hFd i j y, hW z hz]
  obtain ⟨μ, hμ, hμeval⟩ := k22rr_exists_glued_local_differentials 𝔇 F hF hFlc
  refine ⟨𝔇, F, μ, hμ, hF, (fun i y _ => hreal i y), hFlc, hμeval, ?_, ?_⟩
  · exact k22rr_exists_disk_loop_subdivision x 𝔇
  · intro p N t σ ht0 htN htmono ht01 hcover
    exact k22rr_disk_potential_character_sum x χ 𝔇 a ha F hFd p N t σ
      ht0 htN htmono ht01 hcover

end

theorem k22rr_pd_local_cr :
∀ {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (η : Jacobians.HolomorphicOneForms X)
    (f : Jacobians.Dolbeault.SmoothCFunctions X) (F H : X → ℂ) (B : Set X),
    IsOpen B →
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F B →
    Jacobians.IsLocalPrimitiveOn η H B →
    (∀ y ∈ B, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      (Jacobians.Dolbeault.proj01
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y)) v =
      (Jacobians.Dolbeault.proj01
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
        (starRingEnd ℂ) (η.toFun y v)) →
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun z => F z - f z - (starRingEnd ℂ) (H z)) B := by
  intro X _ _ _ _ _ _ η f F H B hB hF hH hproj
  intro y hy
  have hFmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y :=
    (hF.contMDiffAt (hB.mem_nhds hy)).mdifferentiableAt (by simp)
  have hfmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y :=
    (f.contMDiff y).mdifferentiableAt (by simp)
  have hHmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H y := (hH y hy).1
  let c := extChartAt 𝓘(ℝ, ℂ) y
  let z₀ := c y
  let a : ℂ → ℂ := fun z => F (c.symm z)
  let b : ℂ → ℂ := fun z => f (c.symm z)
  let h : ℂ → ℂ := fun z => H (c.symm z)
  let g : ℂ → ℂ := fun z => a z - b z - (starRingEnd ℂ) (h z)
  have hpullR : ∀ w : X → ℂ,
      writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) y w = fun z => w (c.symm z) := by
    intro w
    ext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rfl
  have hpullC : ∀ w : X → ℂ,
      writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) y w = fun z => w (c.symm z) := by
    intro w
    ext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rfl
  have ha : DifferentiableAt ℝ a z₀ := by
    have hd := hFmd.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      hpullR] at hd
    exact hd
  have hb : DifferentiableAt ℝ b z₀ := by
    have hd := hfmd.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      hpullR] at hd
    exact hd
  have hh : DifferentiableAt ℂ h z₀ := by
    have hd := hHmd.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      hpullC] at hd
    exact hd
  have hHmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) H y = fderiv ℂ h z₀ := by
    rw [hHmd.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ,
      fderivWithin_univ, hpullC]
    rfl
  have hcond := hproj y hy (1 : ℂ)
  erw [Jacobians.Dolbeault.proj01_apply_one (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y),
    Jacobians.Dolbeault.proj01_apply_one (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y),
    Jacobians.Dolbeault.mfderiv_apply_eq_fderiv_pullback' hFmd 1,
    Jacobians.Dolbeault.mfderiv_apply_eq_fderiv_pullback' hFmd Complex.I,
    Jacobians.Dolbeault.mfderiv_apply_eq_fderiv_pullback' hfmd 1,
    Jacobians.Dolbeault.mfderiv_apply_eq_fderiv_pullback' hfmd Complex.I,
    (hH y hy).2 (1 : ℂ), hHmf] at hcond
  change (2 : ℂ)⁻¹ * (fderiv ℝ a z₀ 1 + Complex.I * fderiv ℝ a z₀ Complex.I) =
    (2 : ℂ)⁻¹ * (fderiv ℝ b z₀ 1 + Complex.I * fderiv ℝ b z₀ Complex.I) +
      (starRingEnd ℂ) (fderiv ℂ h z₀ 1) at hcond
  have hconj : HasFDerivAt (fun z => (starRingEnd ℂ) (h z))
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((fderiv ℂ h z₀).restrictScalars ℝ)) z₀ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z₀
      (hh.hasFDerivAt.restrictScalars ℝ)
  have hgr : HasFDerivAt g
      ((fderiv ℝ a z₀ - fderiv ℝ b z₀) -
        Complex.conjCLE.toContinuousLinearMap.comp
          ((fderiv ℂ h z₀).restrictScalars ℝ)) z₀ :=
    (ha.hasFDerivAt.sub hb.hasFDerivAt).sub hconj
  have hDhI : fderiv ℂ h z₀ Complex.I = Complex.I * fderiv ℂ h z₀ 1 := by
    simp [smul_eq_mul]
  have hzero : fderiv ℝ g z₀ 1 + Complex.I * fderiv ℝ g z₀ Complex.I = 0 := by
    rw [hgr.fderiv]
    change (fderiv ℝ a z₀ 1 - fderiv ℝ b z₀ 1 -
        (starRingEnd ℂ) (fderiv ℂ h z₀ 1)) + Complex.I *
      (fderiv ℝ a z₀ Complex.I - fderiv ℝ b z₀ Complex.I -
        (starRingEnd ℂ) (fderiv ℂ h z₀ Complex.I)) = 0
    rw [hDhI, map_mul, Complex.conj_I]
    field_simp at hcond
    ring_nf
    rw [Complex.I_sq]
    linear_combination hcond
  have hgC : DifferentiableAt ℂ g z₀ := by
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨hgr.differentiableAt, ?_⟩
    have hD1 : fderiv ℝ g z₀ 1 = -(Complex.I * fderiv ℝ g z₀ Complex.I) := by
      linear_combination hzero
    rw [hD1, smul_eq_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]
    ring
  apply MDifferentiableAt.mdifferentiableWithinAt
  refine (mdifferentiableAt_iff _ _).mpr ⟨?_, ?_⟩
  · exact (hFmd.continuousAt.sub hfmd.continuousAt).sub
      (Complex.conjCLE.continuous.continuousAt.comp hHmd.continuousAt)
  · rw [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      hpullC]
    exact hgC

section PeriodDescentCore
open scoped Manifold ContDiff Topology
open Set Metric Filter
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Locally constant differences have identical genuine intrinsic derivatives. -/
theorem k22rr_pd_mfderiv_eq_of_constant_difference {G H : X → ℂ} {y : X}
    (hG : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G y)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H y)
    (hc : (fun z => G z - H z) =ᶠ[𝓝 y] (fun _ => G y - H y)) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) G y = mfderiv 𝓘(ℂ) 𝓘(ℂ) H y := by
  have heq := hc.mfderiv_eq (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun z => G z - H z) y =
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun _ : X => G y - H y) y at heq
  rw [mfderiv_const] at heq
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (G - H) y = 0 at heq
  rw [mfderiv_sub hG hH] at heq
  exact sub_eq_zero.mp heq

/-- A local holomorphic function has an analytic own-chart pullback germ. -/
theorem k22rr_pd_analytic_pullback {G : X → ℂ} {B : Set X} {a : X}
    (hB : IsOpen B) (ha : a ∈ B)
    (hG : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) G B) :
    AnalyticAt ℂ (G ∘ (chartAt ℂ a).symm) (chartAt ℂ a a) := by
  let e := chartAt ℂ a
  let T : Set ℂ := e.target ∩ e.symm ⁻¹' B
  have hTop : IsOpen T := e.isOpen_inter_preimage_symm hB
  have hcenter : e a ∈ T := by
    refine ⟨e.map_source (mem_chart_source ℂ a), ?_⟩
    change e.symm (e a) ∈ B
    rw [e.left_inv (mem_chart_source ℂ a)]
    exact ha
  have hdiff : DifferentiableOn ℂ (G ∘ e.symm) T := by
    intro z hz
    have hs : e.symm z ∈ e.source := e.map_target hz.1
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (e.symm z) :=
      (hG _ hz.2).mdifferentiableAt (hB.mem_nhds hz.2)
    have h := Jacobians.differentiableAt_comp_chart_symm hs hm
    rw [e.right_inv hz.1] at h
    exact h.differentiableWithinAt
  exact hdiff.analyticAt (hTop.mem_nhds hcenter)

/-- A covector agreeing locally with a genuine holomorphic differential
has the analytic own-chart coefficient needed by section assembly. -/
theorem k22rr_pd_analytic_differential_section
    (L : (y : X) → TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hlocal : ∀ a : X, ∃ (B : Set X) (G : X → ℂ),
      IsOpen B ∧ a ∈ B ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) G B ∧
        ∀ y ∈ B, L y = mfderiv 𝓘(ℂ) 𝓘(ℂ) G y) :
    ∀ a : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) a
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ a).symm z)
          (e.symmL ℂ ((chartAt ℂ a).symm z) 1)) ((chartAt ℂ a) a) := by
  intro a
  obtain ⟨B, G, hB, ha, hG, hL⟩ := hlocal a
  have hAn := k22rr_pd_analytic_pullback hB ha hG
  let e := chartAt ℂ a
  have hs := e.tendsto_symm (mem_chart_source ℂ a)
  apply hAn.deriv.congr
  filter_upwards [hs.eventually (hB.mem_nhds ha),
    e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ a))] with z hz hzt
  rw [hL _ hz]
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (e.symm z) :=
    (hG _ hz).mdifferentiableAt (hB.mem_nhds hz)
  have he := Jacobians.Dolbeault.mfderiv_apply_symmL_eq_deriv G (e.map_target hzt) hm
  rw [e.right_inv hzt] at he
  exact he.symm

/-- Differences of corrected local primitives are locally constant on an
overlap, so their actual intrinsic differentials agree. -/
theorem k22rr_pd_mfderiv_corrections_eq
    (η : Jacobians.HolomorphicOneForms X) (f F G H J : X → ℂ)
    {U : Set X} (hU : IsOpen U)
    (hH : Jacobians.IsLocalPrimitiveOn η H U)
    (hJ : Jacobians.IsLocalPrimitiveOn η J U) {y : X} (hy : y ∈ U)
    (hFG : (fun z => F z - G z) =ᶠ[𝓝 y] (fun _ => F y - G y))
    (hK : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun z => F z - f z - (starRingEnd ℂ) (H z)) y)
    (hK' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun z => G z - f z - (starRingEnd ℂ) (J z)) y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun z => F z - f z - (starRingEnd ℂ) (H z)) y =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun z => G z - f z - (starRingEnd ℂ) (J z)) y := by
  apply k22rr_pd_mfderiv_eq_of_constant_difference hK hK'
  have hHJ := Jacobians.isLocalPrimitiveOn_sub_locally_const hU hH hJ hy
  filter_upwards [hFG, hHJ] with z hz hz'
  calc
    (F z - f z - (starRingEnd ℂ) (H z)) -
        (G z - f z - (starRingEnd ℂ) (J z)) =
      F z - G z - (starRingEnd ℂ) (H z - J z) := by
        rw [map_sub]; ring
    _ = F y - G y - (starRingEnd ℂ) (H y - J y) := by rw [hz, hz']
    _ = (F y - f y - (starRingEnd ℂ) (H y)) -
        (G y - f y - (starRingEnd ℂ) (J y)) := by
        rw [map_sub]; ring

/-- Conditional assembly of genuine analytic cotangent gluing. The single
internal CR input is discharged by the separately proved local CR theorem. -/
theorem k22rr_pd_glue_local_primitives_of_cr
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
    (F : 𝔇.ι → X → ℂ) (μ : Jacobians.Dolbeault.SmoothCOneForms X)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η : Jacobians.HolomorphicOneForms X)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i))
    (hconst : ∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧
        W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, F i z - F j z = F i y - F j y)
    (hμ : ∀ i, ∀ y ∈ 𝔇.U i, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v = (Jacobians.Dolbeault.proj01
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y)) v)
    (hdec : ∀ y : X, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v = (Jacobians.Dolbeault.proj01
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
        (starRingEnd ℂ) (η.toFun y v))
    (hCR : ∀ (G H : X → ℂ) (B : Set X), IsOpen B →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) G B →
      Jacobians.IsLocalPrimitiveOn η H B →
      (∀ y ∈ B, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
        (Jacobians.Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G y)) v =
          (Jacobians.Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
            (starRingEnd ℂ) (η.toFun y v)) →
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (fun z => G z - f z - (starRingEnd ℂ) (H z)) B) :
    ∃ η' : Jacobians.HolomorphicOneForms X,
      ∀ i, ∀ y ∈ 𝔇.U i, ∃ (B : Set X) (H : X → ℂ),
        IsOpen B ∧ y ∈ B ∧ B ⊆ (𝔇.U i : Set X) ∧
        Jacobians.IsLocalPrimitiveOn η H B ∧
        Jacobians.IsLocalPrimitiveOn η'
          (fun z => F i z - f z - (starRingEnd ℂ) (H z)) B := by
  classical
  have hK : ∀ (i : 𝔇.ι) (B : Set X) (H : X → ℂ),
      IsOpen B → B ⊆ (𝔇.U i : Set X) → Jacobians.IsLocalPrimitiveOn η H B →
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (fun z => F i z - f z - (starRingEnd ℂ) (H z)) B := by
    intro i B H hB hBU hH
    apply hCR (F i) H B hB ((hF i).mono hBU) hH
    intro y hy v
    exact (hμ i y (hBU hy) v).symm.trans (hdec y v)
  have hdeq : ∀ (i j : 𝔇.ι) (B C : Set X) (H J : X → ℂ),
      IsOpen B → IsOpen C → B ⊆ (𝔇.U i : Set X) → C ⊆ (𝔇.U j : Set X) →
      Jacobians.IsLocalPrimitiveOn η H B → Jacobians.IsLocalPrimitiveOn η J C →
      ∀ y ∈ B ∩ C,
        mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun z => F i z - f z - (starRingEnd ℂ) (H z)) y =
          mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun z => F j z - f z - (starRingEnd ℂ) (J z)) y := by
    intro i j B C H J hB hC hBU hCU hH hJ y hy
    obtain ⟨W, hW, hyW, _, heq⟩ := hconst i j y ⟨hBU hy.1, hCU hy.2⟩
    have hFG : (fun z => F i z - F j z) =ᶠ[𝓝 y] (fun _ => F i y - F j y) := by
      filter_upwards [hW.mem_nhds hyW] with z hz
      exact heq z hz
    exact k22rr_pd_mfderiv_corrections_eq η (⇑f) (F i) (F j) H J (hB.inter hC)
      (hH.mono Set.inter_subset_left) (hJ.mono Set.inter_subset_right) hy hFG
      ((hK i B H hB hBU hH y hy.1).mdifferentiableAt (hB.mem_nhds hy.1))
      ((hK j C J hC hCU hJ y hy.2).mdifferentiableAt (hC.mem_nhds hy.2))
  have hcover : ∀ a : X, ∃ i : 𝔇.ι, a ∈ 𝔇.U i := by
    intro a
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [𝔇.covers]
    trivial
  choose index hindex using hcover
  have hprim : ∀ a : X, ∃ (U : Set X) (H : X → ℂ),
      IsOpen U ∧ a ∈ U ∧ IsPathConnected U ∧ Jacobians.IsLocalPrimitiveOn η H U :=
    fun a => Jacobians.exists_isLocalPrimitiveOn η a
  choose U H hU haU _ hH using hprim
  let B : X → Set X := fun a => U a ∩ (𝔇.U (index a) : Set X)
  let K : X → X → ℂ := fun a z => F (index a) z - f z - (starRingEnd ℂ) (H a z)
  have hB : ∀ a : X, IsOpen (B a) := fun a => (hU a).inter (𝔇.U (index a)).isOpen
  have haB : ∀ a : X, a ∈ B a := fun a => ⟨haU a, hindex a⟩
  have hBH : ∀ a : X, Jacobians.IsLocalPrimitiveOn η (H a) (B a) :=
    fun a => (hH a).mono Set.inter_subset_left
  have hBK : ∀ a : X, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (K a) (B a) :=
    fun a => hK (index a) (B a) (H a) (hB a) Set.inter_subset_right (hBH a)
  let L : (y : X) → TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y :=
    fun y => mfderiv 𝓘(ℂ) 𝓘(ℂ) (K y) y
  have hL : ∀ a : X, ∀ y ∈ B a, L y = mfderiv 𝓘(ℂ) 𝓘(ℂ) (K a) y := by
    intro a y hy
    exact hdeq (index y) (index a) (B y) (B a) (H y) (H a) (hB y) (hB a)
      Set.inter_subset_right Set.inter_subset_right (hBH y) (hBH a) y ⟨haB y, hy⟩
  have hAn := k22rr_pd_analytic_differential_section L (by
    intro a
    exact ⟨B a, K a, hB a, haB a, hBK a, hL a⟩)
  let η' : Jacobians.HolomorphicOneForms X := Jacobians.Dolbeault.holOfLocalRepAnalyticAt L hAn
  refine ⟨η', ?_⟩
  intro i y hy
  obtain ⟨V, J, hV, hyV, _, hJ⟩ := Jacobians.exists_isLocalPrimitiveOn η y
  let C : Set X := V ∩ (𝔇.U i : Set X)
  have hC : IsOpen C := hV.inter (𝔇.U i).isOpen
  have hCJ : Jacobians.IsLocalPrimitiveOn η J C := hJ.mono Set.inter_subset_left
  have hCK := hK i C J hC Set.inter_subset_right hCJ
  refine ⟨C, J, hC, ⟨hyV, hy⟩, Set.inter_subset_right, hCJ, ?_⟩
  intro z hz
  refine ⟨(hCK z hz).mdifferentiableAt (hC.mem_nhds hz), ?_⟩
  intro v
  change L z v = mfderiv 𝓘(ℂ) 𝓘(ℂ)
    (fun w => F i w - f w - (starRingEnd ℂ) (J w)) z v
  have he := hdeq (index z) i (B z) C (H z) J (hB z) hC
    Set.inter_subset_right Set.inter_subset_right (hBH z) hCJ z ⟨haB z, hz⟩
  exact DFunLike.congr_fun he v

/-- Internal terminal assembly: the actual complex period representation of
every real character, together with the actual P formula, gives surjectivity. -/
theorem k22rr_pd_surjective_of_period_descent (x : X)
    (P : (Fin (genus X) → ℂ) →ₗ[ℝ]
      (Additive (FundamentalGroup X x) →+ ℝ))
    (hP : ∀ (v : Fin (genus X) → ℂ) (p : Path x x),
      P v (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
      (Jacobians.pathPrimValue (Jacobians.ambientIso X v)
        p.extend p.continuous_extend.continuousOn).re)
    (hdesc : ∀ χ : Additive (FundamentalGroup X x) →+ ℝ,
      ∃ η' η : Jacobians.HolomorphicOneForms X, ∀ p : Path x x,
        (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ) =
          Jacobians.pathPrimValue η' p.extend p.continuous_extend.continuousOn +
            (starRingEnd ℂ)
              (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn)) :
    Function.Surjective P := by
  classical
  intro χ
  obtain ⟨η', η, hη⟩ := hdesc χ
  have hsub : ∀ p : Path x x,
      Jacobians.pathPrimValue (η' - η) p.extend p.continuous_extend.continuousOn =
        Jacobians.pathPrimValue η' p.extend p.continuous_extend.continuousOn -
          Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn := by
    intro p
    have ha := k22rr_pathPrimValue_add η' ((-1 : ℂ) • η) p.continuous_extend.continuousOn
    have hn := k22rr_pathPrimValue_smul (-1 : ℂ) η p.continuous_extend.continuousOn
    rw [neg_one_smul] at ha hn
    change Jacobians.pathPrimValue (η' - η) p.extend p.continuous_extend.continuousOn = _ at ha
    rw [hn, smul_eq_mul, neg_one_mul] at ha
    exact ha
  have hzero : Complex.I • (η' - η) = 0 :=
    k22rr_pi_form_zero_of_real_periods (Complex.I • (η' - η)) x (by
      intro p
      have him := congrArg Complex.im (hη p)
      rw [Complex.ofReal_im, Complex.add_im, Complex.conj_im] at him
      rw [k22rr_pathPrimValue_smul, smul_eq_mul, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, hsub, Complex.sub_im]
      linarith)
  have heq : η' = η :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero)
  have hreal : ∀ p : Path x x,
      χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
        2 * (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re := by
    intro p
    have h := congrArg Complex.re (hη p)
    rw [heq, Complex.ofReal_re, Complex.add_re, Complex.conj_re] at h
    linarith
  let v := (Jacobians.ambientIso X).symm ((2 : ℂ) • η)
  refine ⟨v, ?_⟩
  apply AddMonoidHom.ext
  intro γ
  obtain ⟨p, hp⟩ : ∃ p : Path x x, FundamentalGroup.fromPath ⟦p⟧ = γ.toMul :=
    Quotient.inductionOn γ.toMul (fun p => ⟨p, rfl⟩)
  change P v (Additive.ofMul γ.toMul) = χ (Additive.ofMul γ.toMul)
  rw [← hp, hP]
  have hav : Jacobians.ambientIso X v = (2 : ℂ) • η :=
    (Jacobians.ambientIso X).apply_symm_apply _
  rw [hav, k22rr_pathPrimValue_smul]
  change ((2 : ℂ) *
    Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re = _
  rw [Complex.mul_re]
  change 2 * (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).re -
    0 * (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn).im = _
  rw [zero_mul, sub_zero]
  exact (hreal p).symm


end PeriodDescentCore

section RRFinalPeriodAssembly
open scoped Manifold ContDiff Topology
open Set Metric Filter

section
open scoped Manifold ContDiff Topology
open Set Metric Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Genuine local primitives of two holomorphic forms and their actual local
potential relation give a common finite subdivision of every continuous path.
The sum of cover-potential increments is the two path values plus the global
correction's endpoint increment; no primitive on an entire chart disk is assumed. -/
theorem k22rr_pd_period_exists_subdivision_value
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X) (F : 𝔇.ι → X → ℂ)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η η' : Jacobians.HolomorphicOneForms X)
    (hlocal : ∀ i, ∀ y ∈ 𝔇.U i,
      ∃ (B : Set X) (H K : X → ℂ), IsOpen B ∧ y ∈ B ∧ B ⊆ 𝔇.U i ∧
        Jacobians.IsLocalPrimitiveOn η H B ∧
        Jacobians.IsLocalPrimitiveOn η' K B ∧
        ∀ z ∈ B, K z = F i z - f z - (starRingEnd ℂ) (H z))
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    ∃ (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
      t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) ∧
      (∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), γ s ∈ 𝔇.U (σ k)) ∧
      (∑ k ∈ Finset.range N,
        (F (σ k) (γ (t (k + 1))) - F (σ k) (γ (t k)))) =
        Jacobians.pathPrimValue η' γ hγ +
          (starRingEnd ℂ) (Jacobians.pathPrimValue η γ hγ) + (f (γ 1) - f (γ 0)) := by
  classical
  have hcov : ∀ y : X, ∃ i, y ∈ 𝔇.U i := by
    have h : (univ : Set X) ⊆ ⋃ i, (𝔇.U i : Set X) := by
      rw [univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔇.covers]
      rfl
    intro y
    exact mem_iUnion.mp (h (mem_univ y))
  have hdata : ∀ y : X, ∃ (i : 𝔇.ι) (B : Set X) (H K : X → ℂ),
      IsOpen B ∧ y ∈ B ∧ B ⊆ 𝔇.U i ∧
        Jacobians.IsLocalPrimitiveOn η H B ∧
        Jacobians.IsLocalPrimitiveOn η' K B ∧
        ∀ z ∈ B, K z = F i z - f z - (starRingEnd ℂ) (H z) := by
    intro y
    obtain ⟨i, hy⟩ := hcov y
    obtain ⟨B, H, K, hBo, hyB, hBsub, hH, hK, hrel⟩ := hlocal i y hy
    exact ⟨i, B, H, K, hBo, hyB, hBsub, hH, hK, hrel⟩
  choose index B H K hBo hyB hBsub hH hK hrel using hdata
  let γ' : Icc (0 : ℝ) 1 → X := fun s => γ s
  let cover : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun s => γ' ⁻¹' B (γ' s)
  have hcover : ∀ s, IsOpen (cover s) := fun s => (hBo _).preimage hγ.domRestrict
  have hcovers : (univ : Set (Icc (0 : ℝ) 1)) ⊆ ⋃ s, cover s := by
    intro s _
    exact Set.mem_iUnion.mpr ⟨s, hyB (γ' s)⟩
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hblocks⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc zero_le_one hcover hcovers
  choose s hs using hblocks
  have hblock : ∀ k r, r ∈ Icc (t k : ℝ) (t (k + 1)) → γ r ∈ B (γ' (s k)) := by
    intro k r hr
    have hr01 : r ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (t k).2.1 hr.1, le_trans hr.2 (t (k + 1)).2.2⟩
    exact hs k (show (⟨r, hr01⟩ : Icc (0 : ℝ) 1) ∈ Icc (t k) (t (k + 1)) from hr)
  let C : Jacobians.PrimitiveChain η γ :=
    { n := m + 1
      t := fun k => (t k : ℝ)
      t_zero := by exact_mod_cast ht0
      t_stab := fun k hk => by exact_mod_cast hm k (by omega)
      mono := fun a b hab => Subtype.coe_le_coe.mpr (htmono hab)
      U := fun k => B (γ' (s k))
      F := fun k => H (γ' (s k))
      isOpen := fun k => hBo _
      prim := fun k => hH _
      covers := hblock }
  let D : Jacobians.PrimitiveChain η' γ :=
    { n := C.n
      t := C.t
      t_zero := C.t_zero
      t_stab := C.t_stab
      mono := C.mono
      U := C.U
      F := fun k => K (γ' (s k))
      isOpen := C.isOpen
      prim := fun k => hK _
      covers := C.covers }
  let σ : ℕ → 𝔇.ι := fun k => index (γ' (s k))
  have hinc : ∀ k,
      F (σ k) (γ (C.t (k + 1))) - F (σ k) (γ (C.t k)) =
        (D.F k (γ (C.t (k + 1))) - D.F k (γ (C.t k))) +
          (starRingEnd ℂ) (C.F k (γ (C.t (k + 1))) - C.F k (γ (C.t k))) +
          (f (γ (C.t (k + 1))) - f (γ (C.t k))) := by
    intro k
    have hleft := C.covers k (C.t k) ⟨le_refl _, C.mono (Nat.le_succ k)⟩
    have hright := C.covers k (C.t (k + 1)) ⟨C.mono (Nat.le_succ k), le_refl _⟩
    have hKleft := hrel (γ' (s k)) (γ (C.t k)) hleft
    have hKright := hrel (γ' (s k)) (γ (C.t (k + 1))) hright
    change F (index (γ' (s k))) (γ (C.t (k + 1))) -
      F (index (γ' (s k))) (γ (C.t k)) =
        (K (γ' (s k)) (γ (C.t (k + 1))) - K (γ' (s k)) (γ (C.t k))) +
          (starRingEnd ℂ) (H (γ' (s k)) (γ (C.t (k + 1))) - H (γ' (s k)) (γ (C.t k))) +
          (f (γ (C.t (k + 1))) - f (γ (C.t k)))
    rw [map_sub]
    linear_combination -hKright + hKleft
  refine ⟨C.n, C.t, σ, C.t_zero, C.t_stab C.n (le_refl _), C.mono,
    (fun k _ => ⟨C.t_nonneg k, C.t_le_one k⟩), ?_, ?_⟩
  · intro k _ r hr
    exact hBsub (γ' (s k)) (C.covers k r hr)
  · rw [Jacobians.pathPrimValue_eq η' hγ D, Jacobians.pathPrimValue_eq η hγ C]
    calc
      _ = ∑ k ∈ Finset.range C.n,
          ((D.F k (γ (C.t (k + 1))) - D.F k (γ (C.t k))) +
            (starRingEnd ℂ) (C.F k (γ (C.t (k + 1))) - C.F k (γ (C.t k))) +
            (f (γ (C.t (k + 1))) - f (γ (C.t k)))) :=
        Finset.sum_congr rfl fun k _ => hinc k
      _ = D.value + (starRingEnd ℂ) (C.value) + (f (γ 1) - f (γ 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← map_sum,
          Finset.sum_range_sub (fun k => f (γ (C.t k))) C.n,
          C.t_stab C.n (le_refl _), C.t_zero]
        rfl

/-- The actual A1 increment formula and genuine local primitive relation imply
the exact complex period comparison on every continuous loop. The local relation
is required only on smaller open neighborhoods inside the cover sets. -/
theorem k22rr_pd_period_character_eq
    (x : X) (χ : Additive (FundamentalGroup X x) →+ ℝ)
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X) (F : 𝔇.ι → X → ℂ)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η η' : Jacobians.HolomorphicOneForms X)
    (hlocal : ∀ i, ∀ y ∈ 𝔇.U i,
      ∃ (B : Set X) (H K : X → ℂ), IsOpen B ∧ y ∈ B ∧ B ⊆ 𝔇.U i ∧
        Jacobians.IsLocalPrimitiveOn η H B ∧
        Jacobians.IsLocalPrimitiveOn η' K B ∧
        ∀ z ∈ B, K z = F i z - f z - (starRingEnd ℂ) (H z))
    (hcharacter : ∀ (p : Path x x) (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
      t 0 = 0 → t N = 1 → Monotone t →
      (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) →
      (∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) →
      (∑ k ∈ Finset.range N,
        (F (σ k) (p.extend (t (k + 1))) - F (σ k) (p.extend (t k)))) =
        (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ)) :
    ∀ p : Path x x,
      (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ) =
        Jacobians.pathPrimValue η' p.extend p.continuous_extend.continuousOn +
          (starRingEnd ℂ) (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn) := by
  intro p
  obtain ⟨N, t, σ, ht0, htN, htmono, ht01, hcover, hvalue⟩ :=
    k22rr_pd_period_exists_subdivision_value 𝔇 F f η η' hlocal
      p.continuous_extend.continuousOn
  rw [hcharacter p N t σ ht0 htN htmono ht01 hcover] at hvalue
  simpa only [Path.extend_zero, Path.extend_one, sub_self, add_zero] using hvalue

end

section RRFinalA2
/-- Every smooth `(0,1)` form on a compact connected Riemann surface is the sum
of an exact `∂̄` term and the conjugate of a holomorphic one-form. -/
theorem k22rr_sg_exists_dbar_conj_decomposition
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    (μ : Jacobians.Dolbeault.SmoothCOneForms S)
    (hμ : μ ∈ Jacobians.Dolbeault.OneFormsZeroOne S) :
    ∃ (f : Jacobians.Dolbeault.SmoothCFunctions S)
      (η : Jacobians.HolomorphicOneForms S),
      μ = Jacobians.Dolbeault.dbarL f +
        Jacobians.Dolbeault.AbelPairing.conjForm η := by
  classical
  let w : Fin (genus S) → ℂ := fun i =>
    Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i) μ
  have hdet : IsUnit (Jacobians.Dolbeault.AbelPairing.pairMatrix S).det :=
    isUnit_iff_ne_zero.mpr (Jacobians.Dolbeault.AbelPairing.pairMatrix_det_ne_zero (X := S))
  let e := (Jacobians.Dolbeault.AbelPairing.pairMatrix S).toLinearEquiv'
    ((Jacobians.Dolbeault.AbelPairing.pairMatrix S).invertibleOfIsUnitDet hdet)
  let v : Fin (genus S) → ℂ := e.symm w
  have hev : (Jacobians.Dolbeault.AbelPairing.pairMatrix S).mulVec v = w := by
    have h := e.apply_symm_apply w
    change (Jacobians.Dolbeault.AbelPairing.pairMatrix S).mulVec v = w at h
    exact h
  -- Conjugate the solved coefficients because conjForm is conjugate-linear.
  let d : Fin (genus S) → ℂ := fun j => (starRingEnd ℂ) (v j)
  let η : Jacobians.HolomorphicOneForms S := Jacobians.ambientIso S d
  have hη : η = ∑ j, d j • Jacobians.periodBasisForm S j :=
    Jacobians.Dolbeault.AbelPairing.ambientIso_eq_sum d
  have hconj : Jacobians.Dolbeault.AbelPairing.conjForm η =
      ∑ j, Jacobians.Dolbeault.cSmulForm
        (Jacobians.Dolbeault.AbelPairing.constCF (v j))
        (Jacobians.Dolbeault.AbelPairing.conjForm (Jacobians.periodBasisForm S j)) := by
    rw [hη, Jacobians.Dolbeault.AbelPairing.conjForm_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Jacobians.Dolbeault.AbelPairing.conjForm_smul]
    congr 2
    exact Complex.conj_conj (v j)
  have hpair (i : Fin (genus S)) :
      Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i)
        (Jacobians.Dolbeault.AbelPairing.conjForm η) =
      Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i) μ := by
    rw [hconj, Jacobians.Dolbeault.AbelPairing.pairForm_sum]
    calc
      (∑ j, Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i)
        (Jacobians.Dolbeault.cSmulForm (Jacobians.Dolbeault.AbelPairing.constCF (v j))
          (Jacobians.Dolbeault.AbelPairing.conjForm (Jacobians.periodBasisForm S j)))) =
          ∑ j, Jacobians.Dolbeault.AbelPairing.pairMatrix S i j * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Jacobians.Dolbeault.AbelPairing.pairForm_cSmul_const]
        change v j * Jacobians.Dolbeault.AbelPairing.pairMatrix S i j =
          Jacobians.Dolbeault.AbelPairing.pairMatrix S i j * v j
        exact mul_comm _ _
      _ = Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i) μ := by
        have hmv := congrFun hev i
        change (∑ j, Jacobians.Dolbeault.AbelPairing.pairMatrix S i j * v j) = w i at hmv
        exact hmv
  have hs : μ - Jacobians.Dolbeault.AbelPairing.conjForm η ∈
      Jacobians.Dolbeault.OneFormsZeroOne S :=
    (Jacobians.Dolbeault.OneFormsZeroOne S).sub_mem hμ
      (Jacobians.Dolbeault.AbelPairing.conjForm_mem_zeroOne η)
  have h0 : ∀ i : Fin (genus S),
      Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i)
        (μ - Jacobians.Dolbeault.AbelPairing.conjForm η) = 0 := by
    intro i
    change (Jacobians.Dolbeault.AbelPairing.pairFormL (Jacobians.periodBasisForm S i))
      (μ - Jacobians.Dolbeault.AbelPairing.conjForm η) = 0
    rw [map_sub]
    change Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i) μ -
      Jacobians.Dolbeault.AbelPairing.pairForm (Jacobians.periodBasisForm S i)
        (Jacobians.Dolbeault.AbelPairing.conjForm η) = 0
    rw [hpair i, sub_self]
  obtain ⟨f, hf⟩ := Jacobians.Dolbeault.AbelPairing.exists_dbarL_eq_of_pairForm_eq_zero hs h0
  exact ⟨f, η, (eq_sub_iff_add_eq.mp hf).symm⟩

end RRFinalA2

/-- Genuine global holomorphic differential gluing with local primitives. -/
theorem k22rr_pd_glue_local_primitives :
∀ {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
    (F : 𝔇.ι → X → ℂ) (μ : Jacobians.Dolbeault.SmoothCOneForms X)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η : Jacobians.HolomorphicOneForms X),
    (∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i)) →
    (∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧
        W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, F i z - F j z = F i y - F j y) →
    (∀ i, ∀ y ∈ 𝔇.U i, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v =
        (Jacobians.Dolbeault.proj01
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y)) v) →
    (∀ y : X, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v =
        (Jacobians.Dolbeault.proj01
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
          (starRingEnd ℂ) (η.toFun y v)) →
    ∃ η' : Jacobians.HolomorphicOneForms X,
      ∀ i, ∀ y ∈ 𝔇.U i, ∃ (B : Set X) (H : X → ℂ),
        IsOpen B ∧ y ∈ B ∧ B ⊆ (𝔇.U i : Set X) ∧
        Jacobians.IsLocalPrimitiveOn η H B ∧
        Jacobians.IsLocalPrimitiveOn η'
          (fun z => F i z - f z - (starRingEnd ℂ) (H z)) B := by
  intro X _ _ _ _ _ _ 𝔇 F μ f η hF hconst hμ hdec
  exact k22rr_pd_glue_local_primitives_of_cr 𝔇 F μ f η hF hconst hμ hdec
    (k22rr_pd_local_cr η f)

/-- Exact A1/A2 local descent gives the genuine complex period identity. -/
theorem k22rr_pd_exists_period_descent :
∀ {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (x : X) (χ : Additive (FundamentalGroup X x) →+ ℝ)
    (𝔇 : Jacobians.Dolbeault.ChartDiskCover X)
    (F : 𝔇.ι → X → ℂ) (μ : Jacobians.Dolbeault.SmoothCOneForms X)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η : Jacobians.HolomorphicOneForms X),
    μ ∈ Jacobians.Dolbeault.OneFormsZeroOne X →
    (∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F i) (𝔇.U i)) →
    (∀ i, ∀ y ∈ 𝔇.U i, (F i y).im = 0) →
    (∀ i j, ∀ y ∈ (𝔇.U i : Set X) ∩ 𝔇.U j,
      ∃ W : Set X, IsOpen W ∧ y ∈ W ∧
        W ⊆ (𝔇.U i : Set X) ∩ 𝔇.U j ∧
        ∀ z ∈ W, F i z - F j z = F i y - F j y) →
    (∀ i, ∀ y ∈ 𝔇.U i, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v =
        (Jacobians.Dolbeault.proj01
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F i) y)) v) →
    (∀ p : Path x x, ∃ (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
      t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) ∧
      ∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) →
    (∀ (p : Path x x) (N : ℕ) (t : ℕ → ℝ) (σ : ℕ → 𝔇.ι),
      t 0 = 0 → t N = 1 → Monotone t →
      (∀ k ≤ N, t k ∈ Icc (0 : ℝ) 1) →
      (∀ k < N, ∀ s ∈ Icc (t k) (t (k + 1)), p.extend s ∈ 𝔇.U (σ k)) →
      (∑ k ∈ Finset.range N,
        (F (σ k) (p.extend (t (k + 1))) - F (σ k) (p.extend (t k)))) =
        (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ)) →
    (∀ y : X, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v =
        (Jacobians.Dolbeault.proj01
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
          (starRingEnd ℂ) (η.toFun y v)) →
    ∃ η' : Jacobians.HolomorphicOneForms X, ∀ p : Path x x,
      (χ (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) : ℂ) =
        Jacobians.pathPrimValue η' p.extend p.continuous_extend.continuousOn +
          (starRingEnd ℂ)
            (Jacobians.pathPrimValue η p.extend p.continuous_extend.continuousOn) := by
  intro X _ _ _ _ _ _ x χ 𝔇 F μ f η hμ01 hF hreal hconst hμ hsubdivision hcharacter hdec
  -- These frozen A1 obligations remain true. This assembly also holds without
  -- them: the period helper constructs valid subdivisions from genuine local
  -- primitives, and fiberwise decomposition already supplies the CR input.
  have _hμ01 := hμ01
  have _hreal := hreal
  have _hsubdivision := hsubdivision
  obtain ⟨η', hlocal⟩ := k22rr_pd_glue_local_primitives 𝔇 F μ f η hF hconst hμ hdec
  refine ⟨η', ?_⟩
  apply k22rr_pd_period_character_eq x χ 𝔇 F f η η' ?_ hcharacter
  intro i y hy
  obtain ⟨B, H, hB, hyB, hBU, hH, hK⟩ := hlocal i y hy
  refine ⟨B, H, (fun z => F i z - f z - (starRingEnd ℂ) (H z)),
    hB, hyB, hBU, hH, hK, ?_⟩
  intro z _
  rfl

section A3FiberBridge

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The actual intrinsic A2 operator equality gives exactly the fiber relation
used in the frozen local-CR and period-descent statements, with coefficient one. -/
theorem k22rr_pd_fiber_decomposition
    (μ : Jacobians.Dolbeault.SmoothCOneForms X)
    (f : Jacobians.Dolbeault.SmoothCFunctions X)
    (η : Jacobians.HolomorphicOneForms X)
    (hdec : μ = Jacobians.Dolbeault.dbarL f +
      Jacobians.Dolbeault.AbelPairing.conjForm η) :
    ∀ y : X, ∀ v : TangentSpace 𝓘(ℝ, ℂ) y,
      μ.toFun y v = (Jacobians.Dolbeault.proj01
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
          (starRingEnd ℂ) (η.toFun y v) := by
  intro y v
  have h := congrArg (fun α : Jacobians.Dolbeault.SmoothCOneForms X => α.toFun y v) hdec
  change μ.toFun y v = (Jacobians.Dolbeault.proj01
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑f) y)) v +
      (starRingEnd ℂ) (η.toFun y v) at h
  exact h

end A3FiberBridge

section A3UnconditionalSurjectivity
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The genuine real period map is surjective: A1 constructs local potentials,
A2 supplies the actual Dolbeault decomposition, and proved A3 gives periods. -/
theorem k22rr_pd_surjective (x : X)
    (P : (Fin (genus X) → ℂ) →ₗ[ℝ]
      (Additive (FundamentalGroup X x) →+ ℝ))
    (hP : ∀ (v : Fin (genus X) → ℂ) (p : Path x x),
      P v (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
      (Jacobians.pathPrimValue (Jacobians.ambientIso X v)
        p.extend p.continuous_extend.continuousOn).re) :
    Function.Surjective P := by
  apply k22rr_pd_surjective_of_period_descent x P hP
  intro χ
  obtain ⟨𝔇, F, μ, hμ01, hF, hreal, hconst, hμ, hsubdivision, hcharacter⟩ :=
    k22rr_exists_real_character_potentials x χ
  obtain ⟨f, η, hdec⟩ := k22rr_sg_exists_dbar_conj_decomposition μ hμ01
  obtain ⟨η', hperiod⟩ := k22rr_pd_exists_period_descent x χ 𝔇 F μ f η
    hμ01 hF hreal hconst hμ hsubdivision hcharacter
    (k22rr_pd_fiber_decomposition μ f η hdec)
  exact ⟨η', η, hperiod⟩

end A3UnconditionalSurjectivity

/-- The actual real period map identifies analytic and frozen topological genus. -/
theorem k22rr_genus_eq :
∀ {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {g : ℕ}, LiZhongQC.HasGenus S g → genus S = g := by
  classical
  intro S _ _ _ _ _ _ g hS
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨P, hP⟩ := k22rr_exists_real_period_map x
  exact k22rr_sg_analytic_genus_eq_of_period_bijective hS x P
    ⟨k22rr_pi_injective x P hP, k22rr_pd_surjective x P hP⟩

end RRFinalPeriodAssembly

-- closed_surface_has_genus (§22.1) is stated and proved in LiZhongQC/Lemmas/SchottkyClosedGenus.lean
-- (it needs the topological classification of surfaces).

/-- §22.1: the genus of a closed Riemann surface is unique.  `k22rr_genus_eq` identifies both values with
the analytic genus. -/
theorem closed_surface_genus_unique [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] {g g' : ℕ} (h : HasGenus S g) (h' : HasGenus S g') : g = g' :=
  (k22rr_genus_eq h).symm.trans (k22rr_genus_eq h')

/-! ## §22.2 Fundamental group and coverings -/

/-- **Theorem 22.1** (单值性定理, monodromy theorem): lifts of homotopic paths starting at the same
point end at the same point and are homotopic. -/
theorem thm22_1_monodromy {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
    (hp : IsCoveringMap p) {x₀ x₁ : X} {γ₁ γ₂ : Path x₀ x₁} (hγ : γ₁.Homotopic γ₂) {e₀ e₁ e₂ : E}
    {Γ₁ : Path e₀ e₁} {Γ₂ : Path e₀ e₂} (h₁ : ∀ t, p (Γ₁ t) = γ₁ t) (h₂ : ∀ t, p (Γ₂ t) = γ₂ t) :
    ∃ h : e₁ = e₂, (Γ₁.cast rfl h.symm).Homotopic Γ₂ := by
  have hγ' : γ₁.toContinuousMap.HomotopicRel γ₂.toContinuousMap {0, 1} := hγ
  have h₁0 : γ₁.toContinuousMap 0 = p e₀ := by
    rw [Path.coe_toContinuousMap, ← h₁ 0, Path.source]
  have h₂0 : γ₂.toContinuousMap 0 = p e₀ := by
    rw [Path.coe_toContinuousMap, ← h₂ 0, Path.source]
  -- `Γ₁`, `Γ₂` are the lifts of `γ₁`, `γ₂` starting at `e₀`
  have hL₁ : Γ₁.toContinuousMap = hp.liftPath γ₁.toContinuousMap e₀ h₁0 :=
    (hp.eq_liftPath_iff' h₁0).2 ⟨funext h₁, Γ₁.source⟩
  have hL₂ : Γ₂.toContinuousMap = hp.liftPath γ₂.toContinuousMap e₀ h₂0 :=
    (hp.eq_liftPath_iff' h₂0).2 ⟨funext h₂, Γ₂.source⟩
  -- the endpoints agree
  have hend : e₁ = e₂ := by
    have := hp.liftPath_apply_one_eq_of_homotopicRel hγ' e₀ h₁0 h₂0
    rw [← hL₁, ← hL₂, Path.coe_toContinuousMap, Path.coe_toContinuousMap, Path.target,
      Path.target] at this
    exact this
  refine ⟨hend, ?_⟩
  -- the homotopy of the projections lifts
  have key := hp.homotopicRel_iff_comp (A := unitInterval)
    (f₀ := (Γ₁.cast rfl hend.symm).toContinuousMap) (f₁ := Γ₂.toContinuousMap) (S := {0, 1})
    ⟨0, by simp, by simp⟩
  show (Γ₁.cast rfl hend.symm).toContinuousMap.HomotopicRel Γ₂.toContinuousMap {0, 1}
  rw [key]
  have e1 : (⟨p, hp.continuous⟩ : C(E, X)).comp (Γ₁.cast rfl hend.symm).toContinuousMap =
      γ₁.toContinuousMap := by
    ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap,
      Path.cast_coe]
    exact h₁ t
  have e2 : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂.toContinuousMap = γ₂.toContinuousMap := by
    ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
    exact h₂ t
  rw [e1, e2]
  exact hγ'

/-- §22.2: every Riemann surface has a universal covering: a simply connected Riemann surface `E`
with a holomorphic covering map `p : E → S`; its group of covering transformations is in
bijection with `π₁(S)`. -/
theorem exists_universal_covering [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S) :
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : ChartedSpace ℂ E), IsManifold 𝓘(ℂ) ω E ∧
      SimplyConnectedSpace E ∧ ∃ p : E → S, IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
        Nonempty ({h : E ≃ₜ E // p ∘ h = p} ≃ FundamentalGroup S x₀) := by
  classical
  let E := RiemannDynamics.PathCover x₀
  let p : E → S := RiemannDynamics.pathCoverProj x₀
  let b : E := RiemannDynamics.pathCoverBase x₀
  letI : SimplyConnectedSpace E :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  have hp : IsCoveringMap p :=
    RiemannDynamics.pathCoverProj_isCoveringMap x₀
  have hpHol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p := by
    intro pc
    obtain ⟨e, he, f, hf, hpc, hppc, hall, hcomm⟩ :=
      RiemannDynamics.exists_charts_pathCoverProj_comm x₀ pc
    have hA : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e pc :=
      contMDiffAt_of_mem_maximalAtlas he hpc
    have hepc : e pc ∈ f.target := by
      rw [← hcomm pc hpc]
      exact f.map_source hppc
    have hB : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.symm (e pc) :=
      contMDiffAt_symm_of_mem_maximalAtlas hf hepc
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun qc : E => f.symm (e qc)) pc := hB.comp pc hA
    have hP : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω p pc := by
      refine hF.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hpc) ?_)
      intro qc hqc
      change RiemannDynamics.pathCoverProj x₀ qc = f.symm (e qc)
      rw [← hcomm qc hqc]
      exact (f.left_inv (hall qc hqc)).symm
    exact hP.mdifferentiableAt (by simp)
  let Fiber := {pc : E // p pc = x₀}
  let ev : {h : E ≃ₜ E // p ∘ h = p} → Fiber := fun h =>
    ⟨h.val b, (congrFun h.property b).trans (show p b = x₀ from rfl)⟩
  have hev_injective : Function.Injective ev := by
    intro h k hab
    have heval : h.val b = k.val b := congrArg Subtype.val hab
    have hfun : (h.val : E → E) = (k.val : E → E) :=
      hp.eq_of_comp_eq h.val.continuous k.val.continuous
        (h.property.trans k.property.symm) b heval
    apply Subtype.ext
    ext pc
    exact congrFun hfun pc
  have hev_surjective : Function.Surjective ev := by
    rintro ⟨qc, hqc⟩
    obtain ⟨γ, hγ⟩ := RiemannDynamics.pathCoverDeck_transitive x₀ b qc
      (show RiemannDynamics.pathCoverProj x₀ b =
        RiemannDynamics.pathCoverProj x₀ qc from hqc.symm)
    obtain ⟨e, he⟩ := RiemannDynamics.exists_pathCoverDeck_diffeomorph x₀ γ
    have heCover : p ∘ e.toHomeomorph = p := by
      funext pc
      change RiemannDynamics.pathCoverProj x₀ (e pc) =
        RiemannDynamics.pathCoverProj x₀ pc
      rw [he pc]
      exact RiemannDynamics.pathCoverProj_deck x₀ γ pc
    refine ⟨⟨e.toHomeomorph, heCover⟩, ?_⟩
    apply Subtype.ext
    change e b = qc
    rw [he b]
    exact hγ
  let ef : Fiber ≃ FundamentalGroup S x₀ :=
    { toFun := fun a => by
        have h : a.val.pt = x₀ := a.property
        exact Eq.ndrec (motive := fun y : S => Path.Homotopic.Quotient x₀ y)
          a.val.cls h
      invFun := fun γ => ⟨⟨x₀, γ⟩, rfl⟩
      left_inv := by
        intro a
        rcases a with ⟨⟨y, c⟩, hy⟩
        change y = x₀ at hy
        subst y
        rfl
      right_inv := by
        intro γ
        rfl }
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    p, hp, hpHol, ?_⟩
  exact ⟨(Equiv.ofBijective ev ⟨hev_injective, hev_surjective⟩).trans ef⟩

/-! ## §22.3 Uniformization -/

theorem k22u_diffeomorph_isBiholomorphic
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace ℂ S] [ChartedSpace ℂ T]
    (e : S ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ T) : IsBiholomorphic (e : S → T) := by
  exact ⟨e.contMDiff.mdifferentiable (by simp), e.symm,
    e.symm.contMDiff.mdifferentiable (by simp), e.symm_apply_apply, e.apply_symm_apply⟩

theorem k22u_biholomorphic_homeomorph
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace ℂ S] [ChartedSpace ℂ T]
    {f : S → T} (hf : IsBiholomorphic f) :
    ∃ e : S ≃ₜ T, (e : S → T) = f := by
  obtain ⟨hfd, g, hgd, hgf, hfg⟩ := hf
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := hfd.continuous
    continuous_invFun := hgd.continuous }, rfl⟩

theorem k22u_plane_disc_separation
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] :
    ¬ (RSConformallyEquivalent S ℂ ∧ RSConformallyEquivalent S unitDiscOpens) := by
  rintro ⟨⟨f, hfd, g, hgd, hgf, hfg⟩, ⟨h, hhd, k, hkd, hkh, hhk⟩⟩
  have hd : Differentiable ℂ (Subtype.val ∘ h ∘ g : ℂ → ℂ) :=
    (mdifferentiable_iff_differentiable.mp
      (((contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)).comp (hhd.comp hgd)))
  have hb : Bornology.IsBounded (Set.range (Subtype.val ∘ h ∘ g : ℂ → ℂ)) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
      (Set.range_subset_iff.mpr fun z => (h (g z)).2)
  have h01 : (h (g 0) : ℂ) = (h (g 1) : ℂ) :=
    hd.apply_eq_apply_of_bounded hb 0 1
  have hh : h (g 0) = h (g 1) := Subtype.ext h01
  have hg : g 0 = g 1 := hkh.injective hh
  exact zero_ne_one (hfg.injective hg)

theorem k22u_compact_separation
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] :
    CompactSpace S → ¬ RSConformallyEquivalent S ℂ ∧
      ¬ RSConformallyEquivalent S unitDiscOpens := by
  intro hcs
  have := hcs
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨e, he⟩ := k22u_biholomorphic_homeomorph hf
    exact not_compactSpace_iff.mpr inferInstance e.compactSpace
  · rintro ⟨f, hf⟩
    obtain ⟨e, he⟩ := k22u_biholomorphic_homeomorph hf
    have hc : IsCompact (Metric.ball (0 : ℂ) 1) :=
      isCompact_iff_compactSpace.mpr e.compactSpace
    have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.ball (0 : ℂ) 1 :=
      hc.isClosed.closure_eq
    rw [closure_ball (0 : ℂ) one_ne_zero] at hcl
    have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, dist_eq_norm]
    rw [hcl] at h1
    simp [Metric.mem_ball, dist_eq_norm] at h1

theorem k22u_sphere_puncture
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [IsManifold 𝓘(ℂ) ω S]
    (e : letI : TopologicalSpace (OnePoint ℂ) := OnePoint.instTopologicalSpace;
      letI : ChartedSpace ℂ (OnePoint ℂ) := RiemannDynamics.chartedSpaceSphere;
      S ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ) :
    CompactSpace S ∧ ∃ p : S,
      RSConformallyEquivalent (⟨{p}ᶜ, isOpen_compl_singleton⟩ :
        TopologicalSpace.Opens S) ℂ := by
  classical
  letI : TopologicalSpace (OnePoint ℂ) := OnePoint.instTopologicalSpace
  letI : ChartedSpace ℂ (OnePoint ℂ) := RiemannDynamics.chartedSpaceSphere
  refine ⟨e.toHomeomorph.symm.compactSpace, e.symm OnePoint.infty, ?_⟩
  let U : TopologicalSpace.Opens S :=
    ⟨{e.symm OnePoint.infty}ᶜ, isOpen_compl_singleton⟩
  obtain ⟨V, hV, ⟨e₁⟩⟩ := RiemannDynamics.exists_diffeomorph_opens_image e U
  have hVset : (V : Set (OnePoint ℂ)) = {OnePoint.infty}ᶜ := by
    rw [hV]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ≠ OnePoint.infty
      intro he
      apply hx
      exact e.toEquiv.injective (he.trans (e.apply_symm_apply _).symm)
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ≠ e.symm OnePoint.infty
      exact fun he => hy (e.symm.toEquiv.injective he)
  have hinfty : OnePoint.infty ∉ (V : Set (OnePoint ℂ)) := by
    rw [hVset]
    simp
  obtain ⟨W, hW, ⟨e₂⟩⟩ := RiemannDynamics.exists_diffeomorph_opens_planar V hinfty
  have hWtop : W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro z
    have hz : (z : OnePoint ℂ) ∈ (V : Set (OnePoint ℂ)) := by
      rw [hVset]
      simp
    rw [← hW] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    exact OnePoint.coe_injective hwz ▸ hw
  subst W
  obtain ⟨e₃⟩ := RiemannDynamics.nonempty_diffeomorph_top ℂ
  exact ⟨(e₁.trans e₂).trans e₃,
    k22u_diffeomorph_isBiholomorphic ((e₁.trans e₂).trans e₃)⟩

theorem k22u_mdifferentiable_contMDiff
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace ℂ S] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω T]
    {f : S → T} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  apply contMDiff_iff.mpr
  refine ⟨hf.continuous, fun x y => ?_⟩
  apply ((mdifferentiable_iff.mp hf).2 x y).contDiffOn
  exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x)
    (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source y))

theorem k22u_biholomorphic_diffeomorph
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace ℂ S] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω T]
    {f : S → T} (hf : IsBiholomorphic f) :
    ∃ e : S ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ T, (e : S → T) = f := by
  obtain ⟨hfd, g, hgd, hgf, hfg⟩ := hf
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    contMDiff_toFun := k22u_mdifferentiable_contMDiff hfd
    contMDiff_invFun := k22u_mdifferentiable_contMDiff hgd }, rfl⟩

theorem k22u_conformal_iff_diffeomorph
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace ℂ S] [ChartedSpace ℂ T]
    [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ) ω T] :
    RSConformallyEquivalent S T ↔ Nonempty (S ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ T) := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨e, he⟩ := k22u_biholomorphic_diffeomorph hf
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨e, k22u_diffeomorph_isBiholomorphic e⟩

theorem k22u_compact_secondCountable
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S] :
    SecondCountableTopology S :=
  ChartedSpace.secondCountable_of_sigmaCompact ℂ S

/-- Complete book conclusion conditional on the missing topology bridge.
The frozen book theorem itself has no second-countability premise. -/
theorem k22u_uniformization_of_secondCountable
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [SimplyConnectedSpace S] [SecondCountableTopology S] :
    ((CompactSpace S ∧ ∃ p : S,
        RSConformallyEquivalent (⟨{p}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens S) ℂ) ∨
      RSConformallyEquivalent S ℂ ∨ RSConformallyEquivalent S unitDiscOpens) ∧
    ¬ (RSConformallyEquivalent S ℂ ∧ RSConformallyEquivalent S unitDiscOpens) ∧
    (CompactSpace S → ¬ RSConformallyEquivalent S ℂ ∧ ¬ RSConformallyEquivalent S unitDiscOpens) := by
  refine ⟨?_, k22u_plane_disc_separation, k22u_compact_separation⟩
  rcases RiemannDynamics.uniformization_trichotomy S with h | h | h
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr ⟨e, k22u_diffeomorph_isBiholomorphic e⟩)
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨e, k22u_diffeomorph_isBiholomorphic e⟩)
  · obtain ⟨e⟩ := h
    exact Or.inl (k22u_sphere_puncture e)

section
open TopologicalSpace

/-- Strict Schwarz: a disc self-map fixing zero with proper image contracts
the derivative strictly. No injectivity hypothesis is needed. -/
theorem k22u_schwarz_strict_of_not_onto
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1))
    (hzero : f 0 = 0)
    (hproper : ¬ Metric.ball (0 : ℂ) 1 ⊆ f '' Metric.ball (0 : ℂ) 1) :
    ‖deriv f 0‖ < 1 := by
  have hc : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    rw [hzero]
    exact fun z hz => ball_subset_closedBall (hmap hz)
  have hle : ‖deriv f 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hf hc one_pos
  by_contra hlt
  have heq : ‖deriv f 0‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf hc
    (mem_ball_self one_pos) (by simpa using heq)
  have hd : deriv f 0 ≠ 0 := norm_ne_zero_iff.mp (by rw [heq]; norm_num)
  apply hproper
  intro z hz
  have hw : z / deriv f 0 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, heq, div_one]
    exact mem_ball_zero_iff.mp hz
  refine ⟨z / deriv f 0, hw, ?_⟩
  have hwf := haff hw
  simpa [hzero, smul_eq_mul, hd] using hwf

/-- A nonnegative family admitting a lower bound from the family for every
countable subfamily has a minimum attained in the family. -/
theorem k22u_minimum_of_countable_lower_bounds
    {ι : Type u} [Nonempty ι] (a : ι → ℝ)
    (hpos : ∀ i, 0 ≤ a i)
    (hdir : ∀ t : Set ι, t.Countable → ∃ i, ∀ j ∈ t, a i ≤ a j) :
    ∃ i, ∀ j, a i ≤ a j := by
  classical
  have hb : BddBelow (range a) := ⟨0, by
    rintro x ⟨i, rfl⟩
    exact hpos i⟩
  obtain ⟨b, _, ht, hm⟩ := exists_seq_tendsto_sInf (range_nonempty a) hb
  have hex : ∀ n : ℕ, ∃ i, a i = b n := hm
  choose j hj using hex
  obtain ⟨i, hi⟩ := hdir (range j) (countable_range j)
  have hli : a i ≤ sInf (range a) :=
    ge_of_tendsto ht (Eventually.of_forall fun n => by
      rw [← hj n]
      exact hi (j n) (mem_range_self n))
  exact ⟨i, fun k => hli.trans (csInf_le hb (mem_range_self k))⟩

/-- Injective entire maps are onto, using only the accepted image-domain RMT. -/
theorem k22u_injective_entire_surjective {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hinj : Function.Injective f) :
    Function.Surjective f := by
  classical
  obtain hconst | hopen :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).is_constant_or_isOpenMap
  · obtain ⟨c, hc⟩ := hconst
    exact False.elim (zero_ne_one (hinj ((hc 0).trans (hc 1).symm)))
  let V : Opens ℂ := ⟨range f, hopen.isOpen_range⟩
  have himg : f '' (⊤ : Opens ℂ) = (V : Set ℂ) := by
    simp only [Opens.coe_top, image_univ]
    rfl
  obtain ⟨e⟩ := RiemannDynamics.nonempty_diffeomorph_of_injOn_differentiableOn
    (⊤ : Opens ℂ) V f hf.differentiableOn hinj.injOn himg
  obtain ⟨t⟩ := RiemannDynamics.nonempty_diffeomorph_top ℂ
  have hsc : SimplyConnectedSpace ↥V :=
    RiemannDynamics.simplyConnectedSpace_of_homeomorph
      (t.symm.trans e).toHomeomorph inferInstance
  by_contra hsurj
  have hne : (V : Set ℂ) ≠ univ := by
    intro heq
    apply hsurj
    intro y
    have hy : y ∈ (V : Set ℂ) := heq.symm ▸ mem_univ y
    exact hy
  obtain ⟨g, hg, hginj, hgimg⟩ :=
    RiemannDynamics.exists_riemannMap_of_simplyConnectedSpace V.isOpen hne hsc
  obtain ⟨d⟩ := RiemannDynamics.nonempty_diffeomorph_of_injOn_differentiableOn
    V RiemannDynamics.unitDiscOpens g hg hginj hgimg
  exact RiemannDynamics.not_nonempty_diffeomorph_complex_unitDisc
    ⟨(t.symm.trans e).trans d⟩

/-- A nonempty open domain in a connected noncompact Hausdorff space cannot
be compact; otherwise it is clopen and equals the ambient space. -/
theorem k22u_noncompact_opens
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [NoncompactSpace S] (U : Opens S) (hU : (U : Set S).Nonempty) :
    NoncompactSpace ↥U := by
  rw [← not_compactSpace_iff]
  intro hcomp
  have hc : IsCompact (U : Set S) := isCompact_iff_compactSpace.mpr hcomp
  have heq : (U : Set S) = univ := IsClopen.eq_univ ⟨hc.isClosed, U.isOpen⟩ hU
  rw [heq] at hc
  exact not_compactSpace_iff.mpr inferInstance (isCompact_univ_iff.mp hc)

/-- The partial inverse of open-subspace inclusion is analytically regular
on its domain, by the inherited charted structure. -/
theorem k22u_mdifferentiable_opens_inclusion
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (U : Opens S) (hU : Nonempty ↥U) :
    (U.openPartialHomeomorphSubtypeCoe hU).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  let i := U.openPartialHomeomorphSubtypeCoe hU
  refine ⟨?_, ?_⟩
  · change MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : ↥U → S) univ
    exact (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp) |>.mdifferentiableOn
  · intro p hp
    have hpU : p ∈ (U : Set S) := by
      simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hp
    let z : ↥U := ⟨p, hpU⟩
    have heq : (fun y : ↥U => i.symm (y : S)) = id := by
      funext y
      exact i.left_inv (by change y ∈ (univ : Set ↥U); trivial)
    have hd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥U => i.symm (y : S)) := by
      rw [heq]
      exact contMDiff_id
    exact (contMDiffAt_subtype_iff.mp (hd z)).mdifferentiableAt (by simp)
      |>.mdifferentiableWithinAt

/-- A disc uniformization becomes a normalized analytic partial chart on
the ambient surface. Its source is the actual supplied open domain. -/
theorem k22u_disc_chart_of_diffeomorph
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (U : Opens S) (p : S) (hp : p ∈ (U : Set S))
    (d : ↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥RiemannDynamics.unitDiscOpens) :
    ∃ e : OpenPartialHomeomorph S ℂ,
      e.source = (U : Set S) ∧ e.target = ball 0 1 ∧
      e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ∧ e p = 0 := by
  classical
  let hU : Nonempty ↥U := ⟨⟨p, hp⟩⟩
  let hD : Nonempty ↥RiemannDynamics.unitDiscOpens := ⟨⟨0, mem_ball_self one_pos⟩⟩
  let i := U.openPartialHomeomorphSubtypeCoe hU
  let j := RiemannDynamics.unitDiscOpens.openPartialHomeomorphSubtypeCoe hD
  let e := i.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans j)
  have hes : e.source = (U : Set S) := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      Opens.openPartialHomeomorphSubtypeCoe_source,
      Opens.openPartialHomeomorphSubtypeCoe_target, preimage_univ, inter_univ, i, j]
  have het : e.target = ball 0 1 := by
    simp only [e, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Homeomorph.toOpenPartialHomeomorph_target,
      Opens.openPartialHomeomorphSubtypeCoe_source,
      Opens.openPartialHomeomorphSubtypeCoe_target, preimage_univ, inter_univ, i, j]
    rfl
  have hd : d.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨d.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      d.symm.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  have he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    (k22u_mdifferentiable_opens_inclusion U hU).symm.trans
      (hd.trans (k22u_mdifferentiable_opens_inclusion RiemannDynamics.unitDiscOpens hD))
  have hps : p ∈ e.source := hes.symm ▸ hp
  let a : ℂ := e p
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp (het ▸ e.map_source hps)
  have hna : ‖-a‖ < 1 := by simpa using ha
  let m : OpenPartialHomeomorph ℂ ℂ := {
    toFun := blaschke a
    invFun := blaschke (-a)
    source := ball 0 1
    target := ball 0 1
    map_source' := fun z hz => mem_ball_zero_iff.mpr
      (blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp hz))
    map_target' := fun z hz => mem_ball_zero_iff.mpr
      (blaschke_mem_unitDisc hna (mem_ball_zero_iff.mp hz))
    left_inv' := fun z hz => blaschke_neg_blaschke ha (mem_ball_zero_iff.mp hz)
    right_inv' := fun z hz => blaschke_blaschke_neg ha (mem_ball_zero_iff.mp hz)
    continuousOn_toFun := (differentiableOn_blaschke ha).continuousOn
    continuousOn_invFun := (differentiableOn_blaschke hna).continuousOn
    open_source := isOpen_ball
    open_target := isOpen_ball }
  have hm : m.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨(differentiableOn_blaschke ha).mdifferentiableOn,
      (differentiableOn_blaschke hna).mdifferentiableOn⟩
  refine ⟨e.trans m, ?_, ?_, he.trans hm, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    change e.source ∩ e ⁻¹' ball 0 1 = (U : Set S)
    rw [← hes]
    exact inter_eq_left.mpr fun x hx => het ▸ e.map_source hx
  · rw [OpenPartialHomeomorph.trans_target]
    change ball 0 1 ∩ m.symm ⁻¹' e.target = ball 0 1
    exact inter_eq_left.mpr fun z hz => het.symm ▸ m.map_target hz
  · change blaschke a (e p) = 0
    exact blaschke_self a

/-- Derivatives use the same ambient tangent chart at p. True inclusion
strictly decreases the normalized forward derivative norm. -/
theorem k22u_disc_chart_derivative_compare
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (p : S) (e f : OpenPartialHomeomorph S ℂ)
    (he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (hf : f.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (hp : p ∈ e.source) (hsub : e.source ⊆ f.source)
    (het : e.target = ball 0 1) (hft : f.target = ball 0 1)
    (hep : e p = 0) (hfp : f p = 0) :
    ‖mvfderiv 𝓘(ℂ) (f : S → ℂ) p (1 : ℂ)‖ ≤
      ‖mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)‖ ∧
    (e.source ≠ f.source →
      ‖mvfderiv 𝓘(ℂ) (f : S → ℂ) p (1 : ℂ)‖ <
        ‖mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)‖) := by
  let F : ℂ → ℂ := f ∘ e.symm
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro z hz
    have hzt : z ∈ e.target := het.symm ▸ hz
    have hx : e.symm z ∈ e.source := e.map_target hzt
    exact ((hf.mdifferentiableAt (hsub hx)).comp z
      (he.mdifferentiableAt_symm hzt)).differentiableAt.differentiableWithinAt
  have hFm : MapsTo F (ball 0 1) (ball 0 1) := by
    intro z hz
    exact hft ▸ f.map_source (hsub (e.map_target (het.symm ▸ hz)))
  have hF0 : F 0 = 0 := by
    change f (e.symm 0) = 0
    have hz : e.symm 0 = p := by rw [← hep, e.left_inv hp]
    exact (congrArg f hz).trans hfp
  have hFd0 : DifferentiableAt ℂ F 0 :=
    hFd.differentiableAt (ball_mem_nhds 0 one_pos)
  have hclosed : MapsTo F (ball 0 1) (closedBall (F 0) 1) := by
    rw [hF0]
    exact fun z hz => ball_subset_closedBall (hFm hz)
  have hbound : ‖deriv F 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hFd hclosed one_pos
  have hEq : (F ∘ e : S → ℂ) =ᶠ[𝓝 p] f := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    change f (e.symm (e x)) = f x
    rw [e.left_inv hx]
  have hdf : mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ e) p = mfderiv 𝓘(ℂ) 𝓘(ℂ) f p := by
    exact hEq.mfderiv_eq
  have hchain := mvfderiv_comp_apply_of_eq p hFd0.mdifferentiableAt
    (he.mdifferentiableAt hp) hep (1 : ℂ)
  have hvalue : mvfderiv 𝓘(ℂ) (f : S → ℂ) p (1 : ℂ) =
      (fderiv ℂ F 0) (mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)) := by
    calc
      _ = mvfderiv 𝓘(ℂ) (F ∘ e) p (1 : ℂ) := by
        change (NormedSpace.fromTangentSpace (f p))
            (mfderiv 𝓘(ℂ) 𝓘(ℂ) f p (1 : ℂ)) =
          (NormedSpace.fromTangentSpace (F (e p)))
            (mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ e) p (1 : ℂ))
        rw [hdf]
        rfl
      _ = _ := by
        rw [mvfderiv_eq_fderiv] at hchain
        change mvfderiv 𝓘(ℂ) (F ∘ e) p (1 : ℂ) =
          (fderiv ℂ F 0) (mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)) at hchain
        exact hchain
  have hnorm : ‖mvfderiv 𝓘(ℂ) (f : S → ℂ) p (1 : ℂ)‖ =
      ‖deriv F 0‖ * ‖mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)‖ := by
    rw [hvalue, fderiv_eq_smul_deriv, norm_smul, mul_comm]
  have hpos : 0 < ‖mvfderiv 𝓘(ℂ) (e : S → ℂ) p (1 : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hz' : mfderiv 𝓘(ℂ) 𝓘(ℂ) e p (1 : ℂ) = 0 := by
      apply (NormedSpace.fromTangentSpace (𝕜 := ℂ) (e p)).injective
      exact hz
    have h10 : (1 : ℂ) = (0 : ℂ) := he.mfderiv_injective hp
      (show mfderiv 𝓘(ℂ) 𝓘(ℂ) e p (1 : ℂ) =
        mfderiv 𝓘(ℂ) 𝓘(ℂ) e p (0 : ℂ) from hz'.trans (map_zero _).symm)
    exact one_ne_zero h10
  rw [hnorm]
  refine ⟨by nlinarith, fun hneq => ?_⟩
  have hproper : ¬ ball (0 : ℂ) 1 ⊆ F '' ball (0 : ℂ) 1 := by
    intro honto
    apply hneq
    apply Subset.antisymm hsub
    intro x hx
    obtain ⟨z, hz, hzx⟩ := honto (hft ▸ f.map_source hx)
    have hez : e.symm z ∈ e.source := e.map_target (het.symm ▸ hz)
    have hident : e.symm z = x := f.injOn (hsub hez) hx hzx
    exact hident ▸ hez
  have hstrict := k22u_schwarz_strict_of_not_onto hFd hFm hF0 hproper
  nlinarith

/-- A chart ball supplies one independently second-countable simply connected
domain at any selected point; no analytic or global countability assumption. -/
theorem k22u_initial_countable_sc_domain
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p : S) :
    ∃ U : Opens S, p ∈ (U : Set S) ∧ SecondCountableTopology ↥U ∧
      IsSimplyConnected (U : Set S) := by
  let c := chartAt ℂ p
  have hpc : p ∈ c.source := mem_chart_source ℂ p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c p) (c.map_source hpc)
  let B : Set ℂ := ball (c p) r
  let U : Opens S := ⟨c.symm '' B, c.symm.isOpen_image_of_subset_source isOpen_ball hball⟩
  let e : ↥B ≃ₜ ↥U := c.symm.homeomorphOfImageSubsetSource hball rfl
  have : ContractibleSpace ↥B :=
    (convex_ball (c p) r).contractibleSpace ⟨c p, mem_ball_self hr⟩
  have hsc : IsSimplyConnected (U : Set S) :=
    RiemannDynamics.simplyConnectedSpace_of_homeomorph e inferInstance
  refine ⟨U, ?_, e.symm.secondCountableTopology, hsc⟩
  exact ⟨c p, mem_ball_self hr, c.left_inv hpc⟩

/-- Analytic Radó assembly from the exact approved topological envelope.
The premise is an explicit reusable interface, not a new axiom or a premise
on the frozen book theorem. -/
theorem k22u_secondCountable_of_countable_sc_envelope
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [SimplyConnectedSpace S]
    (henv : ∀ (p : S) (U : ℕ → Opens S),
      (∀ n, p ∈ (U n : Set S)) →
      (∀ n, SecondCountableTopology ↥(U n)) →
      (∀ n, IsSimplyConnected (U n : Set S)) →
      ∀ (A : Set S), A.Countable →
        ∃ V : Opens S, p ∈ (V : Set S) ∧ SecondCountableTopology ↥V ∧
          IsSimplyConnected (V : Set S) ∧
          (∀ n, (U n : Set S) ⊆ (V : Set S)) ∧ A ⊆ (V : Set S)) :
    SecondCountableTopology S := by
  classical
  by_cases hcompact : CompactSpace S
  · have := hcompact
    exact k22u_compact_secondCountable
  have : NoncompactSpace S := not_compactSpace_iff.mp hcompact
  let p : S := Classical.arbitrary S
  obtain ⟨U₀, hp₀, hcnt₀, hsc₀⟩ := k22u_initial_countable_sc_domain p
  let ι := {U : Opens S // p ∈ (U : Set S) ∧
    SecondCountableTopology ↥U ∧ IsSimplyConnected (U : Set S)}
  have : Nonempty ι := ⟨⟨U₀, hp₀, hcnt₀, hsc₀⟩⟩
  have hmodels : ∀ i : ι,
      Nonempty (↥i.val ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥RiemannDynamics.unitDiscOpens) ∨
      Nonempty (↥i.val ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
    intro i
    have := i.property.2.1
    have : SimplyConnectedSpace ↥i.val := i.property.2.2
    have : NoncompactSpace ↥i.val := k22u_noncompact_opens i.val ⟨p, i.property.1⟩
    rcases RiemannDynamics.uniformization_trichotomy ↥i.val with hd | hp | hs
    · exact Or.inl hd
    · exact Or.inr hp
    · letI : TopologicalSpace (OnePoint ℂ) := OnePoint.instTopologicalSpace
      letI : ChartedSpace ℂ (OnePoint ℂ) := RiemannDynamics.chartedSpaceSphere
      obtain ⟨s⟩ := hs
      have hc : CompactSpace ↥i.val := s.toHomeomorph.symm.compactSpace
      exact False.elim (not_compactSpace_iff.mpr inferInstance hc)
  have htransport : ∀ i : ι, (i.val : Set S) = univ → SecondCountableTopology S := by
    intro i hfull
    have hc := i.property.2.1
    have htop : i.val = ⊤ := Opens.ext hfull
    rw [htop] at hc
    have := hc
    exact (Homeomorph.Set.univ S).symm.secondCountableTopology
  by_cases hplane : ∃ i : ι, Nonempty (↥i.val ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ)
  · obtain ⟨w, ⟨ew⟩⟩ := hplane
    apply htransport w
    apply eq_univ_of_forall
    intro x
    obtain ⟨V, hpV, hcV, hsV, hUV, hxV⟩ := henv p (fun _ => w.val)
      (fun _ => w.property.1) (fun _ => w.property.2.1)
      (fun _ => w.property.2.2) {x} (countable_singleton x)
    let v : ι := ⟨V, hpV, hcV, hsV⟩
    have hwv : w.val ≤ V := hUV 0
    let inc : ↥w.val → ↥V := Opens.inclusion hwv
    let g : ℂ → ↥V := inc ∘ ew.symm
    have hgd : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g :=
      (contMDiff_inclusion hwv).comp ew.symm.contMDiff
    have hgi : Function.Injective g :=
      (Set.inclusion_injective hwv).comp ew.symm.injective
    have hx : x ∈ (V : Set S) := hxV (mem_singleton x)
    rcases hmodels v with hd | hv
    · obtain ⟨ed⟩ := hd
      let F : ℂ → ℂ := Subtype.val ∘ ed ∘ g
      have hFd : Differentiable ℂ F :=
        ((contMDiff_subtype_val (n := ω)).comp (ed.contMDiff.comp hgd)).contDiff
          |>.differentiable (by simp)
      have hFi : Function.Injective F := Subtype.val_injective.comp (ed.injective.comp hgi)
      have hFb : Bornology.IsBounded (range F) :=
        (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
          (range_subset_iff.mpr fun z => (ed (g z)).property)
      exact False.elim (zero_ne_one (hFi (hFd.apply_eq_apply_of_bounded hFb 0 1)))
    · obtain ⟨ev⟩ := hv
      let F : ℂ → ℂ := ev ∘ g
      have hFd : Differentiable ℂ F :=
        (ev.contMDiff.comp hgd).contDiff.differentiable (by simp)
      obtain ⟨z, hz⟩ := k22u_injective_entire_surjective hFd
        (ev.injective.comp hgi) (ev ⟨x, hx⟩)
      have hg : g z = ⟨x, hx⟩ := ev.injective hz
      have hval : (ew.symm z : S) = x := congrArg Subtype.val hg
      exact hval ▸ (ew.symm z).property
  have hdisc : ∀ i : ι,
      Nonempty (↥i.val ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥RiemannDynamics.unitDiscOpens) := by
    intro i
    exact (hmodels i).resolve_right fun hi => hplane ⟨i, hi⟩
  let d := fun i : ι => Classical.choice (hdisc i)
  have hcharts : ∀ i : ι, ∃ e : OpenPartialHomeomorph S ℂ,
      e.source = (i.val : Set S) ∧ e.target = ball 0 1 ∧
      e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ∧ e p = 0 :=
    fun i => k22u_disc_chart_of_diffeomorph i.val p i.property.1 (d i)
  choose e hes het he hep using hcharts
  let a : ι → ℝ := fun i => ‖mvfderiv 𝓘(ℂ) (e i : S → ℂ) p (1 : ℂ)‖
  have hcompare : ∀ i j : ι, (i.val : Set S) ⊆ (j.val : Set S) →
      a j ≤ a i ∧ ((i.val : Set S) ≠ (j.val : Set S) → a j < a i) := by
    intro i j hij
    have hp : p ∈ (e i).source := (hes i).symm ▸ i.property.1
    have hsub : (e i).source ⊆ (e j).source := by
      rw [hes i, hes j]
      exact hij
    have h := k22u_disc_chart_derivative_compare p (e i) (e j) (he i) (he j)
      hp hsub (het i) (het j) (hep i) (hep j)
    refine ⟨h.1, fun hneq => h.2 ?_⟩
    intro heq
    apply hneq
    exact (hes i).symm.trans (heq.trans (hes j))
  have hdir : ∀ t : Set ι, t.Countable → ∃ i, ∀ j ∈ t, a i ≤ a j := by
    intro t ht
    obtain ⟨q, hq⟩ := countable_iff_exists_subset_range.mp ht
    obtain ⟨V, hpV, hcV, hsV, hUV, _⟩ := henv p (fun n => (q n).val)
      (fun n => (q n).property.1) (fun n => (q n).property.2.1)
      (fun n => (q n).property.2.2) ∅ countable_empty
    let v : ι := ⟨V, hpV, hcV, hsV⟩
    refine ⟨v, ?_⟩
    intro j hj
    obtain ⟨n, rfl⟩ := hq hj
    exact (hcompare (q n) v (hUV n)).1
  obtain ⟨w, hw⟩ := k22u_minimum_of_countable_lower_bounds a
    (fun i => norm_nonneg _) hdir
  apply htransport w
  apply eq_univ_of_forall
  intro x
  obtain ⟨V, hpV, hcV, hsV, hUV, hxV⟩ := henv p (fun _ => w.val)
    (fun _ => w.property.1) (fun _ => w.property.2.1)
    (fun _ => w.property.2.2) {x} (countable_singleton x)
  let v : ι := ⟨V, hpV, hcV, hsV⟩
  have hcmp := hcompare w v (hUV 0)
  have heq : (w.val : Set S) = (V : Set S) := by
    by_contra hneq
    exact not_lt_of_ge (hw v) (hcmp.2 hneq)
  rw [heq]
  exact hxV (mem_singleton x)

end

section
open RiemannDynamics TopologicalSpace
open scoped unitInterval ContinuousMap

/-- A: path homotopy classes on a second-countable complex-charted Hausdorff
space are countable. No ambient compactness, connectedness, or analytic atlas
compatibility is required. The proof generalizes the fixed CoverCountable source
using a countable good-chart cover instead of its finite compact cover. -/
theorem k22u_countable_pathClasses (M : Type u) [TopologicalSpace M]
    [ChartedSpace ℂ M] [T2Space M] [SecondCountableTopology M] (x y : M) :
    Countable (Path.Homotopic.Quotient x y) := by
  classical
  have hdisc : ∀ (ycen : M) (W : Set M), IsOpen W → ycen ∈ W →
      ∃ V : Set M, V ⊆ W ∧ IsOpen V ∧ ycen ∈ V ∧
        (∀ z, z ∈ V → ∀ w, w ∈ V → ∃ η : Path z w, ∀ t, η t ∈ V) ∧
        (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
          Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) := by
    intro ycen W hW hyW
    set φ := chartAt ℂ ycen
    have hy : ycen ∈ φ.source := mem_chart_source ℂ ycen
    have hOopen : IsOpen (φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source)) :=
      φ.continuousOn_symm.isOpen_inter_preimage φ.open_target (hW.inter φ.open_source)
    have hyO : φ ycen ∈ φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source) := by
      refine ⟨φ.map_source hy, ?_⟩
      rw [Set.mem_preimage, φ.left_inv hy]
      exact ⟨hyW, hy⟩
    obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hOopen (φ ycen) hyO
    have hmemV : ∀ c ∈ Metric.ball (φ ycen) r,
        φ.symm c ∈ φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r := by
      intro c hc
      refine ⟨φ.map_target (hball hc).1, ?_⟩
      rw [Set.mem_preimage, φ.right_inv (hball hc).1]
      exact hc
    refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r, ?_, ?_, ⟨hy, ?_⟩, ?_, ?_⟩
    · intro z hz
      have h3 : φ.symm (φ z) ∈ W ∩ φ.source := (hball hz.2).2
      rw [φ.left_inv hz.1] at h3
      exact h3.1
    · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
    · exact Metric.mem_ball_self hr0
    · intro z hz w hw
      have hcm : ∀ t : unitInterval,
          (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w ∈ Metric.ball (φ ycen) r := by
        intro t
        have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by
          have := t.2.2
          linarith
        exact (convex_ball (φ ycen) r) hz.2 hw.2 h1 t.2.1 (by ring)
      have hcombo : Continuous fun t : unitInterval => (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w := by
        have hcoe : Continuous fun t : unitInterval => (t : ℝ) := continuous_subtype_val
        have h2 : Continuous fun t : unitInterval =>
            ((1 - (t : ℝ) : ℝ) : ℂ) * φ z + ((t : ℝ) : ℂ) * φ w :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul
            continuous_const).add ((Complex.continuous_ofReal.comp hcoe).mul continuous_const)
        refine h2.congr fun t => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine ⟨⟨⟨fun t => φ.symm ((1 - (t : ℝ)) • φ z + (t : ℝ) • φ w), ?_⟩, ?_, ?_⟩, ?_⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun t => (hball (hcm t)).1
      · change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ z + ((0 : unitInterval) : ℝ) • φ w) = z
        norm_num
        exact φ.left_inv hz.1
      · change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ z + ((1 : unitInterval) : ℝ) • φ w) = w
        norm_num
        exact φ.left_inv hw.1
      · intro t
        exact hmemV _ (hcm t)
    · intro a b η₁ η₂ hη₁ hη₂
      have hcm : ∀ st : unitInterval × unitInterval,
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) ∈
            Metric.ball (φ ycen) r := by
        intro st
        have h1 : (0 : ℝ) ≤ 1 - (st.1 : ℝ) := by
          have := st.1.2.2
          linarith
        exact (convex_ball (φ ycen) r) (hη₁ st.2).2 (hη₂ st.2).2 h1 st.1.2.1 (by ring)
      have hc1 : Continuous fun st : unitInterval × unitInterval => φ (η₁ st.2) :=
        φ.continuousOn.comp_continuous (η₁.continuous.comp continuous_snd)
          fun st => (hη₁ st.2).1
      have hc2 : Continuous fun st : unitInterval × unitInterval => φ (η₂ st.2) :=
        φ.continuousOn.comp_continuous (η₂.continuous.comp continuous_snd)
          fun st => (hη₂ st.2).1
      have hcombo : Continuous fun st : unitInterval × unitInterval =>
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) := by
        have hcoe : Continuous fun st : unitInterval × unitInterval => (st.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have h2 : Continuous fun st : unitInterval × unitInterval =>
            ((1 - (st.1 : ℝ) : ℝ) : ℂ) * φ (η₁ st.2) + ((st.1 : ℝ) : ℂ) * φ (η₂ st.2) :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul hc1).add
            ((Complex.continuous_ofReal.comp hcoe).mul hc2)
        refine h2.congr fun st => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine Quotient.sound ⟨⟨⟨⟨fun st =>
        φ.symm ((1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2)), ?_⟩, ?_, ?_⟩, ?_⟩⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun st => (hball (hcm st)).1
      · intro t
        change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((0 : unitInterval) : ℝ) • φ (η₂ t)) = η₁ t
        norm_num
        exact φ.left_inv (hη₁ t).1
      · intro t
        change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((1 : unitInterval) : ℝ) • φ (η₂ t)) = η₂ t
        norm_num
        exact φ.left_inv (hη₂ t).1
      · intro s t ht
        have hcoinc : η₁ t = η₂ t := by
          rcases ht with h0 | h1
          · rw [h0, η₁.source, η₂.source]
          · rw [Set.mem_singleton_iff] at h1
            rw [h1, η₁.target, η₂.target]
        have hmemsrc : η₁ t ∈ φ.source := (hη₁ t).1
        change φ.symm ((1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₂ t)) = η₁ t
        rw [← hcoinc]
        have hone : (1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₁ t) = φ (η₁ t) := by
          module
        rw [hone]
        exact φ.left_inv hmemsrc
  -- Concatenations of paths inside a set stay inside the set.
  have htmem : ∀ (S : Set M) {a b c : M} (p : Path a b)
      (q : Path b c),
      (∀ t, p t ∈ S) → (∀ t, q t ∈ S) → ∀ t, (p.trans q) t ∈ S := by
    intro S a b c p q hp hq t
    have h := Set.mem_range_self (f := ⇑(p.trans q)) t
    rw [Path.trans_range] at h
    rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact hs ▸ hp s
    · exact hs ▸ hq s
  -- Concatenation of homotopy classes of paths.
  have hq1 : ∀ {a b c : M} (p : Path a b) (q : Path b c),
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) =
        Path.Homotopic.Quotient.mk (p.trans q) := by
    intros
    rfl
  -- Reversals of paths inside a set stay inside the set.
  have hsymmem : ∀ (S : Set M) {a b : M} (p : Path a b),
      (∀ t, p t ∈ S) → ∀ t, p.symm t ∈ S := by
    intro S a b p hp t
    rw [Path.symm_apply]
    exact hp _
  -- Cancellation of a path class against its reverse.
  have hcancel : ∀ {a b : M} (cls : Path.Homotopic.Quotient x a) (η : Path a b),
      (cls.trans (Path.Homotopic.Quotient.mk η)).trans (Path.Homotopic.Quotient.mk η.symm) =
        cls := by
    intro a b cls η
    rw [Path.Homotopic.Quotient.trans_assoc, hq1 η η.symm]
    have h2 : Path.Homotopic.Quotient.mk (η.trans η.symm) =
        Path.Homotopic.Quotient.refl a :=
      Quotient.sound (Path.Homotopic.trans_symm η)
    rw [h2, Path.Homotopic.Quotient.trans_refl]
  -- Sheets over open sets containing the endpoint are open.
  have hopen : ∀ (pc : PathCover x) (U : Set M), IsOpen U → pc.pt ∈ U →
      IsOpen (pathCoverSheet x pc U) := fun pc U hU hpU =>
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨pc, U, hU, hpU, rfl⟩
  -- Every point lies on its own sheet.
  have hself : ∀ (pc : PathCover x) (U : Set M), pc.pt ∈ U →
      pc ∈ pathCoverSheet x pc U := fun pc U hpU =>
    ⟨Path.refl pc.pt, fun _ => hpU, (Path.Homotopic.Quotient.trans_refl pc.cls).symm⟩
  -- Members of a sheet have endpoint inside the base open.
  have hpt : ∀ (pc qc : PathCover x) (U : Set M),
      qc ∈ pathCoverSheet x pc U → qc.pt ∈ U := by
    intro pc qc U h
    obtain ⟨η, hη, -⟩ := h
    exact η.target ▸ hη 1
  -- Sheets are monotone in the base open.
  have hmono : ∀ (pc : PathCover x) {U U' : Set M}, U ⊆ U' →
      pathCoverSheet x pc U ⊆ pathCoverSheet x pc U' := by
    intro pc U U' hUU' qc hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    exact ⟨η, fun t => hUU' (hη t), hcls⟩
  -- The sheet through a member of a sheet is inside that sheet.
  have htrans : ∀ (pc qc : PathCover x) (U : Set M), qc ∈ pathCoverSheet x pc U →
      pathCoverSheet x qc U ⊆ pathCoverSheet x pc U := by
    intro pc qc U hqc rc hrc
    obtain ⟨η₀, hη₀, hcls₀⟩ := hqc
    obtain ⟨η₁, hη₁, hcls₁⟩ := hrc
    refine ⟨η₀.trans η₁, htmem U η₀ η₁ hη₀ hη₁, ?_⟩
    rw [hcls₁, hcls₀, Path.Homotopic.Quotient.trans_assoc, hq1 η₀ η₁]
  -- Sheet membership is symmetric.
  have hsymm : ∀ (pc qc : PathCover x) (U : Set M), qc ∈ pathCoverSheet x pc U →
      pc ∈ pathCoverSheet x qc U := by
    intro pc qc U hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    refine ⟨η.symm, hsymmem U η hη, ?_⟩
    rw [hcls, hcancel pc.cls η]
  -- Two sheets over a common open sharing a point coincide.
  have hsheeteq : ∀ (pc rc : PathCover x) (U : Set M), rc ∈ pathCoverSheet x pc U →
      pathCoverSheet x rc U = pathCoverSheet x pc U := fun pc rc U hrc =>
    Set.Subset.antisymm (htrans pc rc U hrc) (htrans rc pc U (hsymm pc rc U hrc))
  -- Sheets over chart-linearly connected opens surject onto the open.
  have hsurj : ∀ (pc : PathCover x) (V : Set M),
      (∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) → pc.pt ∈ V →
      ∀ z ∈ V, ∃ rc, rc ∈ pathCoverSheet x pc V ∧ rc.pt = z := by
    intro pc V hlinV hpV z hzV
    obtain ⟨η, hη⟩ := hlinV pc.pt hpV z hzV
    exact ⟨⟨z, pc.cls.trans (Path.Homotopic.Quotient.mk η)⟩, ⟨η, hη, rfl⟩, rfl⟩
  -- A sheet over a homotopy-rigid open meets each fiber at most once.
  have hfiber1 : ∀ (pc : PathCover x) (V : Set M),
      (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
        Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) →
      ∀ qc rc : PathCover x, qc ∈ pathCoverSheet x pc V → rc ∈ pathCoverSheet x pc V →
        qc.pt = rc.pt → qc = rc := by
    intro pc V hhomoV qc rc hqc hrc hpteq
    obtain ⟨qpt, qcls⟩ := qc
    obtain ⟨rpt, rcls⟩ := rc
    obtain rfl : qpt = rpt := hpteq
    obtain ⟨η₁, hη₁, hcls₁⟩ := hqc
    obtain ⟨η₂, hη₂, hcls₂⟩ := hrc
    have hcls₁' : qcls = pc.cls.trans (Path.Homotopic.Quotient.mk η₁) := hcls₁
    have hcls₂' : rcls = pc.cls.trans (Path.Homotopic.Quotient.mk η₂) := hcls₂
    have hcc : qcls = rcls := by
      rw [hcls₁', hcls₂', hhomoV pc.pt qpt η₁ η₂ hη₁ hη₂]
    exact congrArg (PathCover.mk qpt) hcc
  have hkey : ∀ {a b c d : M} (γ' : Path c d) (p q : Path a b) (f g : unitInterval → ℝ),
      Continuous f → Continuous g → f 0 = g 0 → f 1 = g 1 →
      (∀ u, p u = γ'.extend (f u)) → (∀ u, q u = γ'.extend (g u)) →
      Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := by
    intro a b c d γ' p q f g hf hg h0 h1 hp hq
    refine Quotient.sound ⟨⟨⟨⟨fun st =>
      γ'.extend ((1 - (st.1 : ℝ)) * f st.2 + (st.1 : ℝ) * g st.2), ?_⟩, ?_, ?_⟩, ?_⟩⟩
    · exact γ'.continuous_extend.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (hf.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).mul (hg.comp continuous_snd)))
    · intro u
      change γ'.extend ((1 - ((0 : unitInterval) : ℝ)) * f u + ((0 : unitInterval) : ℝ) * g u) = p u
      rw [hp u, show ((1 - ((0 : unitInterval) : ℝ)) * f u +
        ((0 : unitInterval) : ℝ) * g u) = f u by norm_num]
    · intro u
      change γ'.extend ((1 - ((1 : unitInterval) : ℝ)) * f u + ((1 : unitInterval) : ℝ) * g u) = q u
      rw [hq u, show ((1 - ((1 : unitInterval) : ℝ)) * f u +
        ((1 : unitInterval) : ℝ) * g u) = g u by norm_num]
    · intro s u hu
      rcases hu with h0' | h1'
      · rw [h0']
        change γ'.extend ((1 - (s : ℝ)) * f 0 + (s : ℝ) * g 0) = p 0
        rw [hp 0, ← h0, show ((1 - (s : ℝ)) * f 0 + (s : ℝ) * f 0) = f 0 by ring]
      · rw [Set.mem_singleton_iff] at h1'
        rw [h1']
        change γ'.extend ((1 - (s : ℝ)) * f 1 + (s : ℝ) * g 1) = p 1
        rw [hp 1, ← h1, show ((1 - (s : ℝ)) * f 1 + (s : ℝ) * f 1) = f 1 by ring]
  -- Equality of cover points across an equality of endpoints, through `Path.cast`.
  have hPC : ∀ {a b : M} (h : a = b) (p : Path x a),
      (⟨a, Path.Homotopic.Quotient.mk p⟩ : PathCover x) =
        ⟨b, Path.Homotopic.Quotient.mk (p.cast rfl h.symm)⟩ := by
    rintro a b rfl p
    rfl
  -- Every point of the cover is joined to the basepoint class by the canonical lift.
  have hjoin : ∀ pc : PathCover x, Joined (pathCoverBase x) pc := by
    rintro ⟨w, cls⟩
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep cls
    -- The initial segments of `γ`, reparametrized to full paths.
    obtain ⟨sp, hspfun⟩ : ∃ sp : ∀ t : unitInterval, Path x (γ t),
        ∀ t u, (sp t) u = γ.extend ((u : ℝ) * (t : ℝ)) := by
      refine ⟨fun t => ⟨⟨fun u => γ.extend ((u : ℝ) * (t : ℝ)),
        γ.continuous_extend.comp (continuous_subtype_val.mul continuous_const)⟩, ?_, ?_⟩,
        fun t u => rfl⟩
      · change γ.extend (((0 : unitInterval) : ℝ) * (t : ℝ)) = x
        norm_num
      · change γ.extend (((1 : unitInterval) : ℝ) * (t : ℝ)) = γ t
        rw [show (((1 : unitInterval) : ℝ) * (t : ℝ)) = (t : ℝ) by norm_num]
        exact γ.extend_extends' t
    -- Continuity of the canonical lift into the sheet topology.
    have hLcont : Continuous fun t : unitInterval =>
        (⟨γ t, Path.Homotopic.Quotient.mk (sp t)⟩ : PathCover x) := by
      refine continuous_generateFrom_iff.mpr ?_
      rintro s ⟨pc, U, hUopen, -, rfl⟩
      rw [isOpen_iff_forall_mem_open]
      intro t₀ ht₀
      obtain ⟨η₀, hη₀, hcls₀⟩ := ht₀
      have hcls₀' : Path.Homotopic.Quotient.mk (sp t₀) =
          pc.cls.trans (Path.Homotopic.Quotient.mk η₀) := hcls₀
      have hγt₀U : γ t₀ ∈ U := by
        have h := hη₀ 1
        rw [η₀.target] at h
        exact h
      have hJopen : IsOpen {u : unitInterval | γ u ∈ U} := hUopen.preimage γ.continuous
      obtain ⟨δ, hδ0, hδball⟩ := Metric.isOpen_iff.mp hJopen t₀ hγt₀U
      refine ⟨Metric.ball t₀ δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδ0⟩
      intro t ht
      -- The parameter segment from `t₀` to `t` stays in the unit interval and in the ball.
      have hseg : ∀ u : unitInterval,
          ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
        intro u
        constructor
        · nlinarith [t₀.2.1, t.2.1, u.2.1, u.2.2]
        · nlinarith [t₀.2.2, t.2.2, u.2.1, u.2.2]
      have hsegBall : ∀ u : unitInterval,
          (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval) ∈
            Metric.ball t₀ δ := by
        intro u
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have htd : |(t : ℝ) - (t₀ : ℝ)| < δ := by
          have h := ht
          rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at h
          exact h
        have hd : |((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) : ℝ) - (t₀ : ℝ)| =
            (u : ℝ) * |(t : ℝ) - (t₀ : ℝ)| := by
          rw [show ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) - (t₀ : ℝ) : ℝ) =
            (u : ℝ) * ((t : ℝ) - (t₀ : ℝ)) by ring, abs_mul, abs_of_nonneg u.2.1]
        change |((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) : ℝ) - (t₀ : ℝ)| < δ
        rw [hd]
        have habs : (0 : ℝ) ≤ |(t : ℝ) - (t₀ : ℝ)| := abs_nonneg _
        nlinarith [u.2.1, u.2.2]
      have hsegU : ∀ u : unitInterval,
          γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) ∈ U := by
        intro u
        have hmem := hδball (hsegBall u)
        have hx : γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) =
            γ (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval) :=
          γ.extend_extends'
            (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval)
        rw [hx]
        exact hmem
      -- The chart-free connector along `γ` from `γ t₀` to `γ t`.
      obtain ⟨c, hcfun⟩ : ∃ c : Path (γ t₀) (γ t),
          ∀ u, c u = γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) := by
        refine ⟨⟨⟨fun u => γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)),
          γ.continuous_extend.comp
            (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
              (continuous_subtype_val.mul continuous_const))⟩, ?_, ?_⟩, fun u => rfl⟩
        · change γ.extend
              ((1 - ((0 : unitInterval) : ℝ)) * (t₀ : ℝ) +
                ((0 : unitInterval) : ℝ) * (t : ℝ)) = γ t₀
          rw [show ((1 - ((0 : unitInterval) : ℝ)) * (t₀ : ℝ) +
            ((0 : unitInterval) : ℝ) * (t : ℝ)) = (t₀ : ℝ) by norm_num]
          exact γ.extend_extends' t₀
        · change γ.extend
              ((1 - ((1 : unitInterval) : ℝ)) * (t₀ : ℝ) +
                ((1 : unitInterval) : ℝ) * (t : ℝ)) = γ t
          rw [show ((1 - ((1 : unitInterval) : ℝ)) * (t₀ : ℝ) +
            ((1 : unitInterval) : ℝ) * (t : ℝ)) = (t : ℝ) by norm_num]
          exact γ.extend_extends' t
      -- The concatenated witness runs inside `U`.
      have htmem : ∀ u, (η₀.trans c) u ∈ U := by
        intro u
        have h := Set.mem_range_self (f := ⇑(η₀.trans c)) u
        rw [Path.trans_range] at h
        rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
        · exact hv ▸ hη₀ v
        · have hcv : c v ∈ U := by
            rw [hcfun v]
            exact hsegU v
          exact hv ▸ hcv
      -- The class of `sp t` is the class of `sp t₀` continued by the connector.
      have hclseq : Path.Homotopic.Quotient.mk (sp t) =
          Path.Homotopic.Quotient.mk ((sp t₀).trans c) := by
        refine hkey γ (sp t) ((sp t₀).trans c) (fun u => (u : ℝ) * (t : ℝ))
          (fun u => if (u : ℝ) ≤ 1 / 2 then 2 * (u : ℝ) * (t₀ : ℝ)
            else (1 - (2 * (u : ℝ) - 1)) * (t₀ : ℝ) + (2 * (u : ℝ) - 1) * (t : ℝ))
          (continuous_subtype_val.mul continuous_const) ?_ ?_ ?_ (fun u => hspfun t u) ?_
        · refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const ?_
          · exact (continuous_const.mul continuous_subtype_val).mul continuous_const
          · exact ((continuous_const.sub ((continuous_const.mul continuous_subtype_val).sub
              continuous_const)).mul continuous_const).add
              (((continuous_const.mul continuous_subtype_val).sub continuous_const).mul
                continuous_const)
          · intro u hu
            rw [hu]
            norm_num
        · norm_num
        · norm_num
        · intro u
          rw [Path.trans_apply]
          split_ifs with h
          · rw [hspfun t₀]
          · rw [hcfun]
      refine ⟨η₀.trans c, htmem, ?_⟩
      have hfin : Path.Homotopic.Quotient.mk (sp t) =
          pc.cls.trans (Path.Homotopic.Quotient.mk (η₀.trans c)) := by
        rw [hclseq, ← hq1 (sp t₀) c, hcls₀', Path.Homotopic.Quotient.trans_assoc, hq1]
      exact hfin
    -- Endpoint identifications of the canonical lift.
    have hL0 : (⟨γ 0, Path.Homotopic.Quotient.mk (sp 0)⟩ : PathCover x) = pathCoverBase x := by
      rw [hPC γ.source (sp 0)]
      have hpath : (sp 0).cast rfl γ.source.symm = Path.refl x := by
        ext u
        change (sp 0) u = x
        rw [hspfun 0 u]
        norm_num
      rw [hpath]
      rfl
    have hL1 : (⟨γ 1, Path.Homotopic.Quotient.mk (sp 1)⟩ : PathCover x) =
        ⟨w, Path.Homotopic.Quotient.mk γ⟩ := by
      rw [hPC γ.target (sp 1)]
      have hpath : (sp 1).cast rfl γ.target.symm = γ := by
        ext u
        change (sp 1) u = γ u
        rw [hspfun 1 u, show ((u : ℝ) * ((1 : unitInterval) : ℝ)) = (u : ℝ) by norm_num]
        exact γ.extend_extends' u
      rw [hpath]
    exact ⟨⟨⟨fun t => (⟨γ t, Path.Homotopic.Quotient.mk (sp t)⟩ : PathCover x), hLcont⟩, hL0, hL1⟩⟩
  -- A countable cover from second countability, without ambient compactness.
  have hgoodAt : ∀ z : M, ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      (∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) ∧
      (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
        Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) := by
    intro z
    obtain ⟨V, -, hVo, hzV, hlin, hhomo⟩ := hdisc z Set.univ isOpen_univ (Set.mem_univ z)
    exact ⟨V, hVo, hzV, hlin, hhomo⟩
  choose Vf hVfo hVfmem hVflin hVfhomo using hgoodAt
  obtain ⟨tf, htfCountable, htf⟩ :=
    isLindelof_univ.elim_countable_subcover Vf hVfo fun z _ =>
      Set.mem_iUnion.mpr ⟨z, hVfmem z⟩
  obtain ⟨D, hDcnt, hDdense⟩ := TopologicalSpace.exists_countable_dense M
  -- The family of sheets over the countable good cover.
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Set (Set (PathCover x)), ∀ S, S ∈ 𝒮 ↔
      ∃ pc : PathCover x, ∃ z ∈ tf, pc.pt ∈ Vf z ∧ S = pathCoverSheet x pc (Vf z) :=
    ⟨{S | ∃ pc : PathCover x, ∃ z ∈ tf, pc.pt ∈ Vf z ∧ S = pathCoverSheet x pc (Vf z)},
      fun _ => Iff.rfl⟩
  -- Each sheet of the family meets at most countably many members of the family.
  have hmeets : ∀ S ∈ 𝒮, Set.Countable {T | T ∈ 𝒮 ∧ (T ∩ S).Nonempty} := by
    intro S hS𝒮
    obtain ⟨pc, z, hztf, hpz, rfl⟩ := (h𝒮 S).mp hS𝒮
    have hD'cnt : Set.Countable
        {rc : PathCover x | rc ∈ pathCoverSheet x pc (Vf z) ∧ rc.pt ∈ D} := by
      rw [← Set.countable_coe_iff]
      have : Countable ↥D := hDcnt.to_subtype
      have hinj : Function.Injective fun rc :
          ↥{rc : PathCover x | rc ∈ pathCoverSheet x pc (Vf z) ∧ rc.pt ∈ D} =>
          (⟨rc.1.pt, rc.2.2⟩ : ↥D) := by
        intro rc rc' h
        have hpteq : rc.1.pt = rc'.1.pt := congrArg Subtype.val h
        exact Subtype.ext (hfiber1 pc (Vf z) (hVfhomo z) rc.1 rc'.1 rc.2.1 rc'.2.1 hpteq)
      exact hinj.countable
    have hper : ∀ rc : PathCover x, Set.Countable {T | T ∈ 𝒮 ∧ rc ∈ T} := by
      intro rc
      refine Set.Countable.mono ?_
        (htfCountable.image fun z' => pathCoverSheet x rc (Vf z'))
      rintro T ⟨hT𝒮, hrcT⟩
      obtain ⟨pc', z', hz'tf, hp'z', rfl⟩ := (h𝒮 T).mp hT𝒮
      exact ⟨z', hz'tf, hsheeteq pc' rc (Vf z') hrcT⟩
    refine Set.Countable.mono ?_ (hD'cnt.biUnion fun rc _ => hper rc)
    rintro T ⟨hT𝒮, qc, hqcT, hqcS⟩
    obtain ⟨pc', z', hz'tf, hp'z', rfl⟩ := (h𝒮 T).mp hT𝒮
    have hqp1 : qc.pt ∈ Vf z' := hpt pc' qc (Vf z') hqcT
    have hqp2 : qc.pt ∈ Vf z := hpt pc qc (Vf z) hqcS
    obtain ⟨V₃, hV₃sub, hV₃o, hqV₃, hlin₃, hhomo₃⟩ :=
      hdisc qc.pt (Vf z' ∩ Vf z) ((hVfo z').inter (hVfo z)) ⟨hqp1, hqp2⟩
    have hsheet₃T : pathCoverSheet x qc V₃ ⊆ pathCoverSheet x pc' (Vf z') :=
      Set.Subset.trans (hmono qc fun w hw => (hV₃sub hw).1) (htrans pc' qc (Vf z') hqcT)
    have hsheet₃S : pathCoverSheet x qc V₃ ⊆ pathCoverSheet x pc (Vf z) :=
      Set.Subset.trans (hmono qc fun w hw => (hV₃sub hw).2) (htrans pc qc (Vf z) hqcS)
    obtain ⟨d, hdV₃, hdD⟩ := hDdense.inter_open_nonempty V₃ hV₃o ⟨qc.pt, hqV₃⟩
    obtain ⟨rc, hrc₃, hrcpt⟩ := hsurj qc V₃ hlin₃ hqV₃ d hdV₃
    exact Set.mem_biUnion ⟨hsheet₃S hrc₃, hrcpt.symm ▸ hdD⟩ ⟨hT𝒮, hsheet₃T hrc₃⟩
  -- The chain-reachable sheets from the basepoint sheet.
  obtain ⟨zb, hzbtf, hxzb⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ x))
  obtain ⟨C, hCzero, hCsucc⟩ : ∃ C : ℕ → Set (Set (PathCover x)),
      C 0 = {pathCoverSheet x (pathCoverBase x) (Vf zb)} ∧
      ∀ n, C (n + 1) = C n ∪ {T | T ∈ 𝒮 ∧ ∃ S ∈ C n, (T ∩ S).Nonempty} :=
    ⟨fun n => Nat.rec {pathCoverSheet x (pathCoverBase x) (Vf zb)}
      (fun _ Cn => Cn ∪ {T | T ∈ 𝒮 ∧ ∃ S ∈ Cn, (T ∩ S).Nonempty}) n, rfl, fun _ => rfl⟩
  have hbase𝒮 : pathCoverSheet x (pathCoverBase x) (Vf zb) ∈ 𝒮 :=
    (h𝒮 _).mpr ⟨pathCoverBase x, zb, hzbtf, hxzb, rfl⟩
  have hCsub : ∀ n, C n ⊆ 𝒮 := by
    intro n
    induction n with
    | zero =>
      rw [hCzero]
      intro S hS
      rw [Set.mem_singleton_iff.mp hS]
      exact hbase𝒮
    | succ n ih =>
      rw [hCsucc n]
      exact Set.union_subset ih fun T hT => hT.1
  have hCcnt : ∀ n, Set.Countable (C n) := by
    intro n
    induction n with
    | zero =>
      rw [hCzero]
      exact Set.countable_singleton _
    | succ n ih =>
      rw [hCsucc n]
      refine ih.union (Set.Countable.mono ?_ (ih.biUnion fun S hS => hmeets S (hCsub n hS)))
      rintro T ⟨hT𝒮, S, hSCn, hTS⟩
      exact Set.mem_biUnion hSCn ⟨hT𝒮, hTS⟩
  -- The union of the chained sheets is open, closed, and contains the basepoint class.
  obtain ⟨W, hWmem⟩ : ∃ W : Set (PathCover x), ∀ qc, qc ∈ W ↔ ∃ n, ∃ S ∈ C n, qc ∈ S :=
    ⟨{qc | ∃ n, ∃ S ∈ C n, qc ∈ S}, fun _ => Iff.rfl⟩
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro qc hqc
    obtain ⟨n, S, hSn, hqcS⟩ := (hWmem qc).mp hqc
    obtain ⟨pc, z, hztf, hpz, hSeq⟩ := (h𝒮 S).mp (hCsub n hSn)
    refine ⟨S, fun rc hrc => (hWmem rc).mpr ⟨n, S, hSn, hrc⟩, ?_, hqcS⟩
    rw [hSeq]
    exact hopen pc (Vf z) (hVfo z) hpz
  have hbaseW : pathCoverBase x ∈ W := by
    refine (hWmem _).mpr ⟨0, pathCoverSheet x (pathCoverBase x) (Vf zb), ?_,
      hself (pathCoverBase x) (Vf zb) hxzb⟩
    rw [hCzero]
    exact rfl
  have hWclosed : IsClosed W := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro qc hqc
    rw [Set.mem_compl_iff] at hqc
    obtain ⟨z, hztf, hqz⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ qc.pt))
    refine ⟨pathCoverSheet x qc (Vf z), fun rc hrc => ?_,
      hopen qc (Vf z) (hVfo z) hqz, hself qc (Vf z) hqz⟩
    rw [Set.mem_compl_iff]
    intro hrcW
    obtain ⟨n, S, hSn, hrcS⟩ := (hWmem rc).mp hrcW
    refine hqc ((hWmem qc).mpr ⟨n + 1, pathCoverSheet x qc (Vf z), ?_,
      hself qc (Vf z) hqz⟩)
    rw [hCsucc n]
    exact Or.inr ⟨(h𝒮 _).mpr ⟨qc, z, hztf, hqz, rfl⟩, S, hSn, rc, hrc, hrcS⟩
  -- Every fiber point over `y` joins to the basepoint class, hence lies in the union.
  have hfibW : ∀ c : Path.Homotopic.Quotient x y, (⟨y, c⟩ : PathCover x) ∈ W := by
    intro c
    obtain ⟨p⟩ := hjoin ⟨y, c⟩
    have hclop : IsClopen (⇑p ⁻¹' W) :=
      ⟨hWclosed.preimage p.continuous, hWopen.preimage p.continuous⟩
    have hne : (⇑p ⁻¹' W).Nonempty := ⟨0, by
      rw [Set.mem_preimage, p.source]
      exact hbaseW⟩
    have huniv := hclop.eq_univ hne
    have h1 : (1 : unitInterval) ∈ ⇑p ⁻¹' W := by
      rw [huniv]
      exact Set.mem_univ _
    rwa [Set.mem_preimage, p.target] at h1
  -- The path classes inject into the countable family of chained sheets.
  obtain ⟨F, hFmem⟩ : ∃ F : Set (Set (PathCover x)), ∀ S, S ∈ F ↔ ∃ n, S ∈ C n :=
    ⟨{S | ∃ n, S ∈ C n}, fun _ => Iff.rfl⟩
  have hFcnt : Set.Countable F := by
    have hFeq : F = ⋃ n, C n := Set.ext fun S => (hFmem S).trans Set.mem_iUnion.symm
    rw [hFeq]
    exact Set.countable_iUnion hCcnt
  have : Countable ↥F := hFcnt.to_subtype
  have hchoose : ∀ c : Path.Homotopic.Quotient x y,
      ∃ S, S ∈ F ∧ (⟨y, c⟩ : PathCover x) ∈ S := by
    intro c
    obtain ⟨n, S, hSn, hmem⟩ := (hWmem _).mp (hfibW c)
    exact ⟨S, (hFmem S).mpr ⟨n, hSn⟩, hmem⟩
  refine Function.Injective.countable (f := fun c : Path.Homotopic.Quotient x y =>
    (⟨(hchoose c).choose, ((hchoose c).choose_spec).1⟩ : ↥F)) ?_
  intro c c' hcc'
  have h1 := ((hchoose c).choose_spec).2
  have h2 := ((hchoose c').choose_spec).2
  have hSS : (hchoose c).choose = (hchoose c').choose := congrArg Subtype.val hcc'
  rw [hSS] at h1
  obtain ⟨n, hSn⟩ := (hFmem _).mp ((hchoose c').choose_spec).1
  obtain ⟨pc, z, hztf, hpz, hSdef⟩ := (h𝒮 _).mp (hCsub n hSn)
  rw [hSdef] at h1 h2
  have heq := hfiber1 pc (Vf z) (hVfhomo z) ⟨y, c⟩ ⟨y, c'⟩ h1 h2 rfl
  injection heq

/-- A countable union of second-countable open subspaces is second countable
with its subtype topology, without any countability premise on the ambient. -/
theorem k22u_secondCountable_open_union
    {S : Type u} [TopologicalSpace S] {ι : Type v} [Countable ι]
    (V : ι → Opens S) (hcnt : ∀ i, SecondCountableTopology ↥(V i)) :
    SecondCountableTopology ↥(⋃ i, (V i : Set S)) := by
  let W : Set S := ⋃ i, (V i : Set S)
  let T : ι → Set ↥W := fun i => ((↑) : ↥W → S) ⁻¹' (V i : Set S)
  haveI : ∀ i, SecondCountableTopology ↥(T i) := by
    intro i
    letI : SecondCountableTopology ↥(V i) := hcnt i
    have he : Topology.IsEmbedding (fun x : ↥(T i) => (x.1.1 : S)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact (he.codRestrict (V i : Set S) fun x => x.2).secondCountableTopology
  refine secondCountableTopology_of_countable_cover
    (U := T) (fun i => (V i).isOpen.preimage continuous_subtype_val) ?_
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.2
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- Enlarge a countable open domain by a countable family of compact,
path-connected images all meeting the domain at the chosen point. Only the
images are compact; neither the ambient surface nor either open domain is. -/
theorem k22u_enlarge_compact_images
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {ι : Type v} [Countable ι] (p : S) (W : Opens S)
    (hpW : p ∈ (W : Set S)) (hWcnt : SecondCountableTopology ↥W)
    (hWconn : IsPathConnected (W : Set S))
    (K : ι → Set S) (hKcompact : ∀ i, IsCompact (K i))
    (hKconn : ∀ i, IsPathConnected (K i)) (hpK : ∀ i, p ∈ K i) :
    ∃ V : Opens S, p ∈ (V : Set S) ∧ SecondCountableTopology ↥V ∧
      IsPathConnected (V : Set S) ∧ (W : Set S) ⊆ (V : Set S) ∧
      ∀ i, K i ⊆ (V : Set S) := by
  classical
  haveI : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := S)
  have hcover : ∀ i, ∃ t : Finset S, K i ⊆ ⋃ x ∈ t, (chartAt ℂ x).source := by
    intro i
    exact (hKcompact i).elim_finite_subcover
      (fun x : S => (chartAt ℂ x).source)
      (fun x => (chartAt ℂ x).open_source)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩)
  choose t ht using hcover
  let J := (i : ι) × ↥(t i)
  let Z : Unit ⊕ J → Opens S := Sum.elim (fun _ => W)
    (fun j => ⟨(chartAt ℂ j.2.1).source, (chartAt ℂ j.2.1).open_source⟩)
  let P : Set S := ⋃ j, (Z j : Set S)
  have hPo : IsOpen P := isOpen_iUnion fun j => (Z j).isOpen
  have hWP : (W : Set S) ⊆ P := fun x hx => mem_iUnion.mpr ⟨Sum.inl (), hx⟩
  have hKP : ∀ i, K i ⊆ P := by
    intro i x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht i hx)
    exact mem_iUnion.mpr ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, hxz⟩
  have hPcnt : SecondCountableTopology ↥P := by
    apply k22u_secondCountable_open_union Z
    intro j
    rcases j with a | b
    · exact hWcnt
    · exact (chartAt ℂ b.2.1).secondCountableTopology_source
  let V : Opens S := ⟨pathComponentIn P p, hPo.pathComponentIn p⟩
  have hVcnt : SecondCountableTopology ↥V := by
    letI : SecondCountableTopology ↥P := hPcnt
    exact (Topology.IsEmbedding.inclusion
      (pathComponentIn_subset : pathComponentIn P p ⊆ P)).secondCountableTopology
  exact ⟨V, mem_pathComponentIn_self (hWP hpW), hVcnt,
    isPathConnected_pathComponentIn (hWP hpW),
    hWconn.subset_pathComponentIn hpW hWP,
    fun i => (hKconn i).subset_pathComponentIn (hpK i) (hKP i)⟩

/-- One enlargement kills every based loop of a second-countable stage.
Countability is used only on that stage, and compactness only on nullhomotopy
images of the parameter square. -/
theorem k22u_kill_stage_loops
    {S : Type u} [TopologicalSpace S] [T2Space S] [ChartedSpace ℂ S]
    [SimplyConnectedSpace S] (p : S) (W : Opens S)
    (hpW : p ∈ (W : Set S)) (hWcnt : SecondCountableTopology ↥W)
    (hWconn : IsPathConnected (W : Set S)) :
    ∃ V : Opens S, ∃ hpV : p ∈ (V : Set S),
      SecondCountableTopology ↥V ∧ IsPathConnected (V : Set S) ∧
      (W : Set S) ⊆ (V : Set S) ∧
      ∀ γ : Path (⟨p, hpW⟩ : ↥W) (⟨p, hpW⟩ : ↥W),
        ∃ F : (γ.map continuous_subtype_val).Homotopy (Path.refl p),
          ∀ st, F st ∈ (V : Set S) := by
  classical
  haveI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.mpr zero_le_one))
  letI : SecondCountableTopology ↥W := hWcnt
  let b : ↥W := ⟨p, hpW⟩
  let Q := Path.Homotopic.Quotient b b
  letI : Countable Q := k22u_countable_pathClasses ↥W b b
  let r : Q → Path b b := Quotient.out
  let a : Q → Path p p := fun c => (r c).map continuous_subtype_val
  let F : (c : Q) → (a c).Homotopy (Path.refl p) := fun c =>
    (SimplyConnectedSpace.paths_homotopic (a c) (Path.refl p)).some
  let K : Q → Set S := fun c => range (F c)
  have hKcompact : ∀ c, IsCompact (K c) := fun c => isCompact_range (F c).continuous
  have hKconn : ∀ c, IsPathConnected (K c) := fun c =>
    isPathConnected_range (F c).continuous
  have hpK : ∀ c, p ∈ K c := by
    intro c
    exact ⟨(0, 0), (F c).source 0⟩
  obtain ⟨V, hpV, hVcnt, hVconn, hWV, hKV⟩ :=
    k22u_enlarge_compact_images p W hpW hWcnt hWconn K hKcompact hKconn hpK
  refine ⟨V, hpV, hVcnt, hVconn, hWV, ?_⟩
  intro γ
  let c : Q := Path.Homotopic.Quotient.mk γ
  have hrep : γ.Homotopic (r c) :=
    Path.Homotopic.Quotient.eq.mp (Quotient.out_eq c).symm
  let H : γ.Homotopy (r c) := hrep.some
  let f : C(↥W, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let G := (H.map f).trans (F c)
  refine ⟨G, ?_⟩
  intro st
  change ((H.map f).trans (F c)) st ∈ (V : Set S)
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hWV (H _).2
  · exact hKV c (mem_range_self _)

/-- In a path-connected space it suffices to contract loops at one fixed
basepoint: concatenate paths to that point and cancel in the path groupoid. -/
theorem k22u_simplyConnected_of_based_loops
    {X : Type u} [TopologicalSpace X] (p : X) (hpath : PathConnectedSpace X)
    (hloops : ∀ γ : Path p p, γ.Homotopic (Path.refl p)) :
    SimplyConnectedSpace X := by
  letI : PathConnectedSpace X := hpath
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpath, ?_⟩
  intro x y γ δ
  let α := PathConnectedSpace.somePath p x
  let β := PathConnectedSpace.somePath y p
  have h := (hloops ((α.trans γ).trans β)).trans
    (hloops ((α.trans δ).trans β)).symm
  have heq :
      ((Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk γ)).trans
        (Path.Homotopic.Quotient.mk β) =
      ((Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk δ)).trans
        (Path.Homotopic.Quotient.mk β) := Quotient.sound h
  have hright :
      (Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk γ) =
      (Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk δ) := by
    have hcancel := congrArg (fun q : Path.Homotopic.Quotient p p =>
      q.trans (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk β))) heq
    simpa only [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl] using hcancel
  have hcancel := congrArg (fun q : Path.Homotopic.Quotient p y =>
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk α)).trans q) hright
  apply Path.Homotopic.Quotient.eq.mp
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] at hcancel
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] at hcancel
  exact hcancel

/-- B: a countable family of second-countable simply connected open domains
containing the same point, and a countable set of selected points, can be
engulfed in one second-countable simply connected open domain of a simply
connected ambient complex-charted Hausdorff space. No ambient or stage
compactness is assumed; compactness is only available for parameter images. -/
theorem k22u_countable_sc_envelope
    {S : Type u} [TopologicalSpace S] [T2Space S]
    [ChartedSpace ℂ S] [SimplyConnectedSpace S]
    (p : S) (U : ℕ → TopologicalSpace.Opens S)
    (hp : ∀ n, p ∈ (U n : Set S))
    (hcnt : ∀ n, SecondCountableTopology ↥(U n))
    (hsc : ∀ n, IsSimplyConnected (U n : Set S))
    (A : Set S) (hA : A.Countable) :
    ∃ V : TopologicalSpace.Opens S,
      p ∈ (V : Set S) ∧ SecondCountableTopology ↥V ∧
      IsSimplyConnected (V : Set S) ∧
      (∀ n, (U n : Set S) ⊆ (V : Set S)) ∧ A ⊆ (V : Set S) := by
  classical
  haveI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.mpr zero_le_one))
  let W₀ : Opens S := ⟨⋃ n, (U n : Set S), isOpen_iUnion fun n => (U n).isOpen⟩
  have hp₀ : p ∈ (W₀ : Set S) := mem_iUnion.mpr ⟨0, hp 0⟩
  have hc₀ : SecondCountableTopology ↥W₀ := k22u_secondCountable_open_union U hcnt
  have hpc₀ : IsPathConnected (W₀ : Set S) := by
    refine ⟨p, hp₀, ?_⟩
    intro y hy
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
    exact ((hsc n).isPathConnected.joinedIn p (hp n) y hyn).mono
      (subset_iUnion (fun n => (U n : Set S)) n)
  letI : Countable ↥A := hA.to_subtype
  let q : (a : ↥A) → Path p a.1 := fun a => PathConnectedSpace.somePath p a.1
  let K : ↥A → Set S := fun a => range (q a)
  have hKc : ∀ a, IsCompact (K a) := fun a => isCompact_range (q a).continuous
  have hKp : ∀ a, IsPathConnected (K a) := fun a => isPathConnected_range (q a).continuous
  have hpK : ∀ a, p ∈ K a := fun a => ⟨0, (q a).source⟩
  obtain ⟨W, hpW, hcW, hpcW, h₀W, hKW⟩ :=
    k22u_enlarge_compact_images p W₀ hp₀ hc₀ hpc₀ K hKc hKp hpK
  have hAW : A ⊆ (W : Set S) := by
    intro a ha
    exact hKW ⟨a, ha⟩ ⟨1, (q ⟨a, ha⟩).target⟩
  let D := {V : Opens S // p ∈ (V : Set S) ∧
    SecondCountableTopology ↥V ∧ IsPathConnected (V : Set S)}
  let start : D := ⟨W, hpW, hcW, hpcW⟩
  have hstep : ∀ d : D, ∃ e : D, (d.1 : Set S) ⊆ (e.1 : Set S) ∧
      ∀ η : Path (⟨p, d.2.1⟩ : ↥d.1) (⟨p, d.2.1⟩ : ↥d.1),
        ∃ F : (η.map continuous_subtype_val).Homotopy (Path.refl p),
          ∀ st, F st ∈ (e.1 : Set S) := by
    intro d
    obtain ⟨V, hpV, hcV, hpcV, hdV, hkill⟩ :=
      k22u_kill_stage_loops p d.1 d.2.1 d.2.2.1 d.2.2.2
    exact ⟨⟨V, hpV, hcV, hpcV⟩, hdV, hkill⟩
  choose next hnextSubset hnextKill using hstep
  let stage : ℕ → D := fun n => Nat.rec start (fun _ d => next d) n
  let V : Opens S := ⟨⋃ n, (stage n).1, isOpen_iUnion fun n => (stage n).1.isOpen⟩
  have hmono : Monotone (fun n => ((stage n).1 : Set S)) :=
    monotone_nat_of_le_succ fun n => hnextSubset (stage n)
  have hstageV : ∀ n, ((stage n).1 : Set S) ⊆ (V : Set S) := fun n =>
    subset_iUnion (fun n => ((stage n).1 : Set S)) n
  have hpV : p ∈ (V : Set S) := hstageV 0 hpW
  have hcntV : SecondCountableTopology ↥V :=
    k22u_secondCountable_open_union (fun n => (stage n).1) (fun n => (stage n).2.2.1)
  have hconnV : IsPathConnected (V : Set S) := by
    refine ⟨p, hpV, ?_⟩
    intro y hy
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
    exact ((stage n).2.2.2.joinedIn p (stage n).2.1 y hyn).mono (hstageV n)
  have hscV : IsSimplyConnected (V : Set S) := by
    apply k22u_simplyConnected_of_based_loops (⟨p, hpV⟩ : ↥V)
      (isPathConnected_iff_pathConnectedSpace.mp hconnV)
    intro η
    let a : Path p p := η.map continuous_subtype_val
    have ha : range a ⊆ ⋃ n, ((stage n).1 : Set S) := by
      rintro x ⟨t, rfl⟩
      exact (η t).2
    obtain ⟨t, ht⟩ := (isCompact_range a.continuous).elim_finite_subcover
      (fun n => ((stage n).1 : Set S)) (fun n => (stage n).1.isOpen)
      (fun x hx => ha hx)
    let N := t.sup id
    have haN : ∀ s, a s ∈ ((stage N).1 : Set S) := by
      intro s
      obtain ⟨n, hnt, han⟩ := mem_iUnion₂.mp (ht (mem_range_self s))
      exact hmono (Finset.le_sup (f := id) hnt) han
    let b : Path (⟨p, (stage N).2.1⟩ : ↥(stage N).1)
        (⟨p, (stage N).2.1⟩ : ↥(stage N).1) := {
      toFun := fun s => ⟨a s, haN s⟩
      continuous_toFun := a.continuous.subtype_mk haN
      source' := Subtype.ext a.source
      target' := Subtype.ext a.target }
    have hk := hnextKill (stage N) b
    change ∃ F : a.Homotopy (Path.refl p),
      ∀ st, F st ∈ ((stage (N + 1)).1 : Set S) at hk
    obtain ⟨F, hF⟩ := hk
    refine ⟨{
      toFun := fun st => ⟨F st, hstageV (N + 1) (hF st)⟩
      continuous_toFun := F.continuous.subtype_mk _
      map_zero_left := fun s => Subtype.ext (F.map_zero_left s)
      map_one_left := fun s => Subtype.ext (F.map_one_left s)
      prop' := fun s t ht => Subtype.ext (F.prop' s t ht) }⟩
  refine ⟨V, hpV, hcntV, hscV, ?_, ?_⟩
  · intro n
    exact (subset_iUnion (fun n => (U n : Set S)) n).trans (h₀W.trans (hstageV 0))
  · exact hAW.trans (hstageV 0)

end

/-- Missing topology bridge under exactly the frozen book hypotheses.
This proposed interface awaits the leader's review; it is not a completed proof. -/
theorem k22u_secondCountable
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [SimplyConnectedSpace S] : SecondCountableTopology S := by
  exact k22u_secondCountable_of_countable_sc_envelope
    (fun p U hp hcnt hsc A hA =>
      k22u_countable_sc_envelope p U hp hcnt hsc A hA)

/-- **Theorem 22.2** (Klein–Poincaré–Koebe 单值化定理).  A simply connected Riemann surface is
conformally equivalent to exactly one of `ℂ̄` (i.e. it is compact and the complement of a point is
conformally `ℂ`), `ℂ`, or the unit disc `Δ`. -/
theorem thm22_2_uniformization [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [SimplyConnectedSpace S] :
    ((CompactSpace S ∧ ∃ p : S,
        RSConformallyEquivalent (⟨{p}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens S) ℂ) ∨
      RSConformallyEquivalent S ℂ ∨ RSConformallyEquivalent S unitDiscOpens) ∧
    ¬ (RSConformallyEquivalent S ℂ ∧ RSConformallyEquivalent S unitDiscOpens) ∧
    (CompactSpace S → ¬ RSConformallyEquivalent S ℂ ∧ ¬ RSConformallyEquivalent S unitDiscOpens) := by
  have := k22u_secondCountable (S := S)
  exact k22u_uniformization_of_secondCountable

/-- The map `ℍ → ℍ` viewed as a map `ℂ → ℂ` (junk value `0` off `ℍ`). -/
def liftToC (F : UpperHalfPlane → UpperHalfPlane) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then (F ⟨z, hz⟩ : ℂ) else 0

/-- On `ℍ`, `liftToC F` is `F ∘ ofComplex`. -/
theorem h23l_liftToC_eq (F : UpperHalfPlane → UpperHalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    liftToC F z = F (UpperHalfPlane.ofComplex z) := by
  have hz' : 0 < z.im := hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold liftToC
  simp only [hz', ↓reduceDIte]

/-- A real Möbius transformation of determinant `1` has its pole on the real axis: `c z + d ≠ 0` for `Im z ≠ 0`. -/
theorem k24_d_den_ne_zero {a b c d : ℝ} (h : a * d - b * c = 1) {z : ℂ} (hz : z.im ≠ 0) :
    (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him : c * z.im = 0 := by simpa using congrArg Complex.im h0
  have hc : c = 0 := (mul_eq_zero.1 him).resolve_right hz
  have hd : d = 0 := by simpa [hc] using congrArg Complex.re h0
  rw [hc, hd, mul_zero, mul_zero, sub_zero] at h
  exact zero_ne_one h

/-- The determinant of `γ ∈ SL(2, ℝ)` in coordinates. -/
theorem k24_det_realR (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

/-- `(g • τ : ℂ) = (a τ + b) / (c τ + d)` for `g ∈ SL(2, ℝ)`. -/
theorem h36t_coe_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ((g • τ : UpperHalfPlane) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The denominator `c τ + d` of `g ∈ SL(2, ℝ)` does not vanish on `ℍ`. -/
theorem h36t_den_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    (g 1 0 : ℂ) * τ + g 1 1 ≠ 0 :=
  k24_d_den_ne_zero (k24_det_realR g) τ.coe_im_pos.ne'

/-- The inverse Cayley transform `w ↦ i(1 + w)/(1 - w)` maps the unit disc conformally onto the upper half-plane. -/
theorem s35a_x_isConformalOnto_cayleyInv : IsConformalOnto cayleyInv unitDisc upperHalf := by
  refine ⟨?_, fun w₁ h₁ w₂ h₂ heq => ?_, ?_⟩
  · intro w hw
    have hden := cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hfun : cayleyInv = fun v : ℂ => I * (1 + v) / (1 - v) := rfl
    rw [hfun]
    exact (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) w).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - v) w) hden
  · calc w₁ = cayley (cayleyInv w₁) := (cayley_cayleyInv (mem_ball_zero_iff.mp h₁)).symm
      _ = cayley (cayleyInv w₂) := by rw [heq]
      _ = w₂ := cayley_cayleyInv (mem_ball_zero_iff.mp h₂)
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
    · intro hz
      exact ⟨cayley z, cayley_mem_unitDisc hz, cayleyInv_cayley hz⟩

section S22PhaseAUpperHalfSupport

open scoped UpperHalfPlane

open UpperHalfPlane

/-- `Im((a z + b)/(c z + d)) = Im z / |c z + d|²` for real `a, b, c, d` with `a d - b c = 1`. -/
theorem utm_im_mobius {a b c d : ℝ} (hdet : a * d - b * c = 1) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [div_sub_div_same]
  congr 1
  linear_combination z.im * hdet

/-- **A non-`±1` element of `SL(2, ℝ)` has unbounded displacement on `ℍ`.**  (From `cosh_dist'`:
`(Re w - Re z)² + (Im z)² + (Im w)² ≤ 2 cosh C · Im z · Im w` for `w = m z`; `c ≠ 0` fails for `z = iy`, `y` large;
`c = 0`, `a² ≠ 1` fails for `Im z = 1`, `Re z` large; `c = 0`, `a² = 1`, `b ≠ 0` fails for `Im z` small.) -/
theorem utm_sl2_eq_of_bounded_displacement (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) {C : ℝ}
    (hC : ∀ z : ℍ, dist (m • z) z ≤ C) : m = 1 ∨ m = -1 := by
  have e1 : (m : Matrix (Fin 2) (Fin 2) ℝ) = !![m 0 0, m 0 1; m 1 0, m 1 1] := Matrix.eta_fin_two _
  obtain ⟨a, ha⟩ : ∃ a, m 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, m 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, m 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, m 1 1 = d := ⟨_, rfl⟩
  rw [ha, hb, hc, hd] at e1
  have hdet : a * d - b * c = 1 := by
    have h := m.det_coe
    rw [e1, Matrix.det_fin_two_of] at h
    exact h
  set B := Real.cosh C with hB
  have hB1 : 1 ≤ B := Real.one_le_cosh C
  -- the key inequality at every point
  have key : ∀ z : ℍ, ((m • z).re - z.re) ^ 2 + (m • z).im ^ 2 + z.im ^ 2 ≤ 2 * B * (m • z).im * z.im := by
    intro z
    have h1 : Real.cosh (dist (m • z) z) ≤ B := by
      rw [hB, Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
      exact (hC z).trans (le_abs_self C)
    rw [cosh_dist'] at h1
    have hpos : 0 < 2 * (m • z).im * z.im := by have := (m • z).im_pos; have := z.im_pos; positivity
    rw [div_le_iff₀ hpos] at h1
    linarith
  -- the action in coordinates
  have hcoe : ∀ z : ℍ, ((m • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := fun z => by
    rw [h36t_coe_smul, ha, hb, hc, hd]
  have him : ∀ z : ℍ, (m • z).im = z.im / Complex.normSq ((c : ℂ) * z + d) := fun z => by
    rw [show (m • z).im = ((m • z : ℍ) : ℂ).im from rfl, hcoe z, utm_im_mobius hdet]
    rfl
  by_cases hc0 : c = 0
  · -- `c = 0`: `m z = a² z + a b`
    have had : a * d = 1 := by rw [hc0, mul_zero, sub_zero] at hdet; exact hdet
    have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one had
    have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hda : d⁻¹ = a := by
      field_simp
      linarith
    have hw : ∀ z : ℍ, ((m • z : ℍ) : ℂ) = ((a ^ 2 : ℝ) : ℂ) * z + ((a * b : ℝ) : ℂ) := by
      intro z
      rw [hcoe z, hc0]
      push_cast
      rw [zero_mul, zero_add, div_eq_mul_inv, ← Complex.ofReal_inv, hda]
      ring
    have hre : ∀ z : ℍ, (m • z).re = a ^ 2 * z.re + a * b := by
      intro z
      have h := congrArg Complex.re (hw z)
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at h
      exact h
    have him' : ∀ z : ℍ, (m • z).im = a ^ 2 * z.im := by
      intro z
      have h := congrArg Complex.im (hw z)
      rw [Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero] at h
      exact h
    -- `((a² - 1) x + a b)² ≤ 2 B a² y²`
    have hineq : ∀ z : ℍ, ((a ^ 2 - 1) * z.re + a * b) ^ 2 ≤ 2 * B * a ^ 2 * z.im ^ 2 := by
      intro z
      have h := key z
      rw [hre z, him' z] at h
      nlinarith [sq_nonneg (a ^ 2 * z.im), sq_nonneg z.im]
    have ha2 : a ^ 2 = 1 := by
      by_contra hne
      have hne' : a ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hne
      set N : ℝ := 2 * B * a ^ 2 + 1 with hN
      set x : ℝ := (N - a * b) / (a ^ 2 - 1) with hx
      have h := hineq (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp))
      have hre' : (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp)).re = x := by
        show ((x : ℂ) + Complex.I).re = x
        simp
      have him'' : (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp)).im = 1 := by
        show ((x : ℂ) + Complex.I).im = 1
        simp
      rw [hre', him''] at h
      have hxe : (a ^ 2 - 1) * x + a * b = N := by
        rw [hx]
        field_simp
        ring
      rw [hxe] at h
      have hN1 : 1 ≤ N := by
        have : 0 ≤ 2 * B * a ^ 2 := by positivity
        linarith
      nlinarith
    have hab : a * b = 0 := by
      by_contra hne
      set y : ℝ := |a * b| / (2 * B + 1) with hy
      have hy0 : 0 < y := div_pos (abs_pos.2 hne) (by linarith)
      have h := hineq (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0))
      have hre' : (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0)).re = 0 := by
        show ((y : ℂ) * Complex.I).re = 0
        simp
      have him'' : (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0)).im = y := by
        show ((y : ℂ) * Complex.I).im = y
        simp
      rw [hre', him'', ha2] at h
      simp only [mul_zero, zero_add, mul_one] at h
      -- `(ab)² ≤ 2 B y² = 2 B (ab)²/(2B+1)² < (ab)²`
      have habs : 0 < |a * b| := abs_pos.2 hne
      have h2B : 0 < 2 * B + 1 := by linarith
      have hyy : y * (2 * B + 1) = |a * b| := by rw [hy]; field_simp
      have hsq : (a * b) ^ 2 = |a * b| ^ 2 := (sq_abs _).symm
      rw [hsq, ← hyy] at h
      have : 0 < y ^ 2 := by positivity
      nlinarith
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 hab with h | h
      · exact absurd h ha0
      · exact h
    have hda' : d = a := by
      have h1 : a * a = 1 := by nlinarith
      have h2 : a * d = a * a := by rw [had, h1]
      exact mul_left_cancel₀ ha0 h2
    rcases mul_eq_zero.1 (show (a - 1) * (a + 1) = 0 by nlinarith) with h1 | h1
    · left
      have ha1 : a = 1 := by linarith
      apply Subtype.ext
      rw [e1, Matrix.SpecialLinearGroup.coe_one, hb0, hc0, hda', ha1]
      exact Matrix.one_fin_two.symm
    · right
      have ha1 : a = -1 := by linarith
      apply Subtype.ext
      rw [e1, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, hb0, hc0, hda', ha1,
        Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · -- `c ≠ 0`: at `z = i y`, `Im(m z) = y/(d² + c² y²)` while `y ≤ 2 B Im(m z)`
    exfalso
    set y : ℝ := (2 * B + 1) / |c| with hy
    have hy0 : 0 < y := div_pos (by linarith) (abs_pos.2 hc0)
    set z : ℍ := UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0) with hz
    have hzim : z.im = y := by
      show ((y : ℂ) * Complex.I).im = y
      simp
    have hD : Complex.normSq ((c : ℂ) * z + d) = d ^ 2 + c ^ 2 * y ^ 2 := by
      show Complex.normSq ((c : ℂ) * ((y : ℂ) * Complex.I) + d) = _
      rw [Complex.normSq_apply]
      simp
      ring
    have h := key z
    rw [him z, hD, hzim] at h
    have hDpos : 0 < d ^ 2 + c ^ 2 * y ^ 2 := by
      have : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc0))
      positivity
    have h1 : y * y ≤ 2 * B * (y / (d ^ 2 + c ^ 2 * y ^ 2)) * y := by
      nlinarith [sq_nonneg ((m • z).re - z.re), sq_nonneg (y / (d ^ 2 + c ^ 2 * y ^ 2))]
    have h2 : y ≤ 2 * B * (y / (d ^ 2 + c ^ 2 * y ^ 2)) := le_of_mul_le_mul_right h1 hy0
    have h3 : d ^ 2 + c ^ 2 * y ^ 2 ≤ 2 * B := by
      rw [mul_div_assoc', le_div_iff₀ hDpos] at h2
      nlinarith
    have hcy : c ^ 2 * y ^ 2 = (2 * B + 1) ^ 2 := by
      rw [hy, div_pow, sq_abs]
      have : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
      field_simp
    nlinarith [sq_nonneg d]

/-- `p² + q² = 1` for `p = Re u`, `q = Im u`, `|u| = 1`. -/
theorem utm_re_sq_add_im_sq {u : ℂ} (hu : ‖u‖ = 1) : u.re ^ 2 + u.im ^ 2 = 1 := by
  have h : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu, one_pow]
  nlinarith [h]

/-- The rotation `!![p, q; -q, p]` (`p² + q² = 1`) of `ℍ` about `i`. -/
def utm_rot (u : ℂ) (hu : ‖u‖ = 1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![u.re, u.im; -u.im, u.re], by
    rw [Matrix.det_fin_two_of]
    have h := utm_re_sq_add_im_sq hu
    nlinarith [h]⟩

/-- The algebra behind `utm_cayley_rot`. -/
theorem utm_cayley_rot_alg {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) {τ : ℂ}
    (hden : -(q : ℂ) * τ + p ≠ 0) :
    cayley (((p : ℂ) * τ + q) / (-(q : ℂ) * τ + p)) = ((p : ℂ) + q * Complex.I) ^ 2 * cayley τ := by
  have hpq' : (p : ℂ) ^ 2 + (q : ℂ) ^ 2 = 1 := by exact_mod_cast hpq
  set N : ℂ := (p : ℂ) * τ + q
  set Dn : ℂ := -(q : ℂ) * τ + p
  have e1 : N - Complex.I * Dn = ((p : ℂ) + q * Complex.I) * (τ - Complex.I) := by
    simp only [N, Dn]
    linear_combination (q : ℂ) * Complex.I_sq
  have e2 : N + Complex.I * Dn = ((p : ℂ) - q * Complex.I) * (τ + Complex.I) := by
    simp only [N, Dn]
    linear_combination (q : ℂ) * Complex.I_sq
  have e3 : ((p : ℂ) + q * Complex.I) * ((p : ℂ) - q * Complex.I) = 1 := by
    linear_combination hpq' - (q : ℂ) ^ 2 * Complex.I_sq
  have hm : (p : ℂ) - q * Complex.I ≠ 0 := right_ne_zero_of_mul_eq_one e3
  have hc : cayley (N / Dn) = (N - Complex.I * Dn) / (N + Complex.I * Dn) := by
    unfold cayley
    rw [div_sub' hden, div_add' _ _ _ hden, div_div_div_cancel_right₀ hden]
    ring_nf
  rw [hc, e1, e2, mul_div_mul_comm]
  have e4 : ((p : ℂ) + q * Complex.I) / ((p : ℂ) - q * Complex.I) = ((p : ℂ) + q * Complex.I) ^ 2 := by
    rw [div_eq_iff hm]
    linear_combination (-((p : ℂ) + q * Complex.I)) * e3
  rw [e4]
  rfl

/-- The Cayley conjugate of the rotation `utm_rot u` is `w ↦ u² w`. -/
theorem utm_cayley_rot (u : ℂ) (hu : ‖u‖ = 1) (τ : ℍ) :
    cayley ((utm_rot u hu • τ : ℍ) : ℂ) = u ^ 2 * cayley τ := by
  have hcoe : ((utm_rot u hu • τ : ℍ) : ℂ) = ((u.re : ℂ) * τ + u.im) / (-(u.im : ℂ) * τ + u.re) := by
    rw [h36t_coe_smul]
    simp [utm_rot]
  have hden : -(u.im : ℂ) * τ + u.re ≠ 0 := by
    have := h36t_den_ne (utm_rot u hu) τ
    simpa [utm_rot] using this
  rw [hcoe, utm_cayley_rot_alg (utm_re_sq_add_im_sq hu) hden,
    Complex.re_add_im]

/-- **The lift of a conformal automorphism is Möbius.**  A self-homeomorphism `F` of `ℍ` whose lift
`liftToC F` is `1`-quasiconformal on `ℍ` is the action of some `m ∈ SL(2, ℝ)`. -/
theorem utm_eq_smul_of_isKQC_one (F : ℍ ≃ₜ ℍ) (hF : IsKQC (liftToC F) upperHalf 1) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F τ = m • τ := by
  set G := liftToC F with hG
  have hGτ : ∀ τ : ℍ, G (τ : ℂ) = (F τ : ℂ) := by
    intro τ
    simp only [hG, liftToC, τ.coe_im_pos, ↓reduceDIte]
  have himg : G '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h := hGτ ⟨z, hz⟩
      change G z = _ at h
      rw [h]
      exact (F ⟨z, hz⟩).coe_im_pos
    · intro hw
      obtain ⟨τ, hτ⟩ := F.surjective ⟨w, hw⟩
      refine ⟨τ, τ.coe_im_pos, ?_⟩
      rw [hGτ, hτ]
  have hconf : IsConformalOnto G upperHalf upperHalf := by
    have h := thm7_3_one_qc_conformal hF
    rwa [himg] at h
  -- move `F I` back to `I`
  obtain ⟨m₀, hm₀⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) (F UpperHalfPlane.I)
    UpperHalfPlane.I
  have hdet : 0 < m₀ 0 0 * m₀ 1 1 - m₀ 0 1 * m₀ 1 0 := by
    have h := m₀.det_coe
    rw [Matrix.det_fin_two] at h
    rw [h]
    exact one_pos
  have hT := isConformalOnto_mobius_upperHalf hdet
  have hTτ : ∀ τ : ℍ, mobiusFn (m₀ 0 0) (m₀ 0 1) (m₀ 1 0) (m₀ 1 1) (τ : ℂ) = ((m₀ • τ : ℍ) : ℂ) := by
    intro τ
    rw [h36t_coe_smul]
    rfl
  -- the Cayley conjugate fixes `0`, hence is a rotation
  set g : ℂ → ℂ := cayley ∘ (mobiusFn (m₀ 0 0) (m₀ 0 1) (m₀ 1 0) (m₀ 1 1) ∘ G) ∘ cayleyInv with hgdef
  have hg : IsConformalOnto g unitDisc unitDisc :=
    isConformalOnto_cayley.comp ((hT.comp hconf).comp s35a_x_isConformalOnto_cayleyInv)
  have hI : cayleyInv 0 = ((UpperHalfPlane.I : ℍ) : ℂ) := by
    simp [cayleyInv, UpperHalfPlane.coe_I]
  have hg0 : g 0 = 0 := by
    simp only [hgdef, Function.comp]
    rw [hI, hGτ, hTτ, hm₀]
    simp [cayley, UpperHalfPlane.coe_I]
  obtain ⟨c', hc'1, hc'⟩ := exists_rotation_of_isConformalOnto_fix_zero hg hg0
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq c' (by norm_num : 0 < 2)
  have hu1 : ‖u‖ = 1 := by
    have h := congrArg norm hu
    rw [norm_pow, hc'1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h
  refine ⟨m₀⁻¹ * utm_rot u hu1, fun τ => ?_⟩
  have h1 : cayley ((m₀ • F τ : ℍ) : ℂ) = cayley ((utm_rot u hu1 • τ : ℍ) : ℂ) := by
    have h := hc' (cayley_mem_unitDisc τ.im_pos)
    simp only [hgdef, Function.comp] at h
    rw [cayleyInv_cayley τ.im_pos, hGτ, hTτ] at h
    rw [h, utm_cayley_rot, hu]
  have h2 : m₀ • F τ = utm_rot u hu1 • τ := by
    apply UpperHalfPlane.ext
    have h := congrArg cayleyInv h1
    rwa [cayleyInv_cayley (m₀ • F τ).im_pos, cayleyInv_cayley (utm_rot u hu1 • τ).im_pos] at h
  rw [mul_smul, ← h2, inv_smul_smul]

end S22PhaseAUpperHalfSupport

/-- A holomorphic plane homeomorphism whose fixed point forces pointwise identity
is a translation. The fixed-point condition is available for actual deck maps. -/
theorem s22c4_eq_add_of_mdifferentiable (F : ℂ ≃ₜ ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hfix : ∀ z : ℂ, F z = z → ∀ w : ℂ, F w = w) :
    ∃ b : ℂ, ∀ z : ℂ, F z = z + b := by
  have hconf : IsConformalOnto (F : ℂ → ℂ) univ univ := by
    refine ⟨hF.differentiable.differentiableOn, F.injective.injOn, ?_⟩
    exact Set.image_univ_of_surjective F.surjective
  obtain ⟨a, b, -, hlin⟩ := nx_entire_affine hconf
  by_cases ha1 : a = 1
  · refine ⟨b, fun z => ?_⟩
    simpa only [ha1, one_mul] using hlin z
  · have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    have hfixed : F (b / (1 - a)) = b / (1 - a) := by
      rw [hlin]
      field_simp [hden] <;> ring
    refine ⟨0, fun z => ?_⟩
    simpa only [add_zero] using hfix (b / (1 - a)) hfixed z

/-- Two holomorphic plane homeomorphisms whose fixed points force identity commute,
because both are translations. -/
theorem s22c4_commute_of_mdifferentiable (F G : ℂ ≃ₜ ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hfixF : ∀ z : ℂ, F z = z → ∀ w : ℂ, F w = w)
    (hfixG : ∀ z : ℂ, G z = z → ∀ w : ℂ, G w = w) :
    ∀ z : ℂ, F (G z) = G (F z) := by
  obtain ⟨b, hb⟩ := s22c4_eq_add_of_mdifferentiable F hF hfixF
  obtain ⟨c, hc⟩ := s22c4_eq_add_of_mdifferentiable G hG hfixG
  intro z
  simp only [hb, hc]
  ring

/-- Holomorphic homeomorphisms preserving an actual covering projection of the plane
commute. Uniqueness of covering lifts supplies the fixed-point condition. -/
theorem s22c4_commute_of_deck {S : Type*} [TopologicalSpace S]
    (p : ℂ → S) (hp : IsCoveringMap p) (F G : ℂ ≃ₜ ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hdeckF : ∀ z : ℂ, p (F z) = p z) (hdeckG : ∀ z : ℂ, p (G z) = p z) :
    ∀ z : ℂ, F (G z) = G (F z) := by
  apply s22c4_commute_of_mdifferentiable F G hF hG
  · intro z hz w
    have hcomp : p ∘ (F : ℂ → ℂ) = p ∘ id := funext hdeckF
    exact congrFun (hp.eq_of_comp_eq F.continuous continuous_id hcomp z hz) w
  · intro z hz w
    have hcomp : p ∘ (G : ℂ → ℂ) = p ∘ id := funext hdeckG
    exact congrFun (hp.eq_of_comp_eq G.continuous continuous_id hcomp z hz) w

/-- A holomorphic homeomorphism of the upper half-plane is the action of a real
determinant-one matrix on every point. -/
theorem k22c5_eq_smul_of_mdifferentiable (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ : UpperHalfPlane, F τ = m • τ := by
  have hcoe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => (F τ : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hF
  have hhol : DifferentiableOn ℂ
      (fun z : ℂ => (F (UpperHalfPlane.ofComplex z) : ℂ)) upperHalf :=
    UpperHalfPlane.mdifferentiable_iff.mp hcoe
  have hconf : IsConformalOnto (liftToC F) upperHalf upperHalf := by
    refine ⟨hhol.congr (fun z hz => h23l_liftToC_eq F hz), ?_, ?_⟩
    · intro z hz w hw heq
      rw [h23l_liftToC_eq F hz, h23l_liftToC_eq F hw] at heq
      have h := F.injective (UpperHalfPlane.coe_injective heq)
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        UpperHalfPlane.ofComplex_apply_of_im_pos hw] at h
      exact congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) h
    · ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [h23l_liftToC_eq F hw]
        exact (F (UpperHalfPlane.ofComplex w)).coe_im_pos
      · intro hz
        obtain ⟨τ, hτ⟩ := F.surjective ⟨z, hz⟩
        refine ⟨(τ : ℂ), τ.coe_im_pos, ?_⟩
        rw [h23l_liftToC_eq F τ.coe_im_pos, UpperHalfPlane.ofComplex_apply, hτ]
  have hqc : IsKQC (liftToC F) upperHalf 1 :=
    isKQC_one_of_conformal isOpen_upperHalf hconf
  exact utm_eq_smul_of_isKQC_one F hqc

/-- The existing Cayley maps realize an analytic equivalence from the actual
upper half-plane to the actual open unit disc, in both complex coordinates. -/
theorem s22c6_cayley_diffeomorph :
    ∃ e : UpperHalfPlane ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ unitDiscOpens,
      (∀ z : UpperHalfPlane, (e z : ℂ) = cayley (z : ℂ)) ∧
      (∀ w : unitDiscOpens, (e.symm w : ℂ) = cayleyInv (w : ℂ)) := by
  let f : UpperHalfPlane → unitDiscOpens :=
    fun z => ⟨cayley (z : ℂ), cayley_mem_unitDisc z.im_pos⟩
  let g : unitDiscOpens → UpperHalfPlane :=
    fun w => ⟨cayleyInv (w : ℂ),
      cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp w.2)⟩
  have hf₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : UpperHalfPlane => cayley (z : ℂ)) := by
    intro z
    have hd : DifferentiableAt ℂ cayley (z : ℂ) :=
      (isConformalOnto_cayley.1 (z : ℂ) z.im_pos).differentiableAt
        (isOpen_upperHalf.mem_nhds z.im_pos)
    exact hd.mdifferentiableAt.comp z (UpperHalfPlane.mdifferentiable_coe z)
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (Subtype.val ∘ f) :=
      (k22u_mdifferentiable_contMDiff hf₀).of_le le_top
    exact ((ContMDiff.subtypeVal_comp_iff unitDiscOpens f).mp hsmooth).mdifferentiable
      (by simp)
  have hsub : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : unitDiscOpens → ℂ) :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  have hg₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun w : unitDiscOpens => cayleyInv (w : ℂ)) := by
    intro w
    have hd : DifferentiableAt ℂ cayleyInv (w : ℂ) :=
      (s35a_x_isConformalOnto_cayleyInv.1 (w : ℂ) w.2).differentiableAt
        (isOpen_ball.mem_nhds w.2)
    exact hd.mdifferentiableAt.comp w (hsub w)
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    have heq : g =
        UpperHalfPlane.ofComplex ∘ (fun w : unitDiscOpens => cayleyInv (w : ℂ)) := by
      funext w
      exact (UpperHalfPlane.ofComplex_apply_of_im_pos
        (cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp w.2))).symm
    rw [heq]
    intro w
    exact (UpperHalfPlane.mdifferentiableAt_ofComplex
      (cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp w.2))).comp w (hg₀ w)
  have hgf : Function.LeftInverse g f := by
    intro z
    apply UpperHalfPlane.coe_injective
    change cayleyInv (cayley (z : ℂ)) = (z : ℂ)
    exact cayleyInv_cayley z.im_pos
  have hfg : Function.RightInverse g f := by
    intro w
    apply Subtype.ext
    change cayley (cayleyInv (w : ℂ)) = (w : ℂ)
    exact cayley_cayleyInv (mem_ball_zero_iff.mp w.2)
  obtain ⟨e, he⟩ := k22u_biholomorphic_diffeomorph (show IsBiholomorphic f from
    ⟨hf, g, hg, hgf, hfg⟩)
  refine ⟨e, ?_, ?_⟩
  · intro z
    change (e z : ℂ) = (f z : ℂ)
    exact congrArg (fun w : unitDiscOpens => (w : ℂ)) (congrFun he z)
  · intro w
    have heg : e (g w) = w := (congrFun he (g w)).trans (hfg w)
    have hback : e.symm w = g w :=
      e.toEquiv.injective ((e.apply_symm_apply w).trans heg.symm)
    change (e.symm w : ℂ) = (g w : ℂ)
    exact congrArg UpperHalfPlane.coe hback

/-- The concrete path-cover projection is holomorphic in the commuting charts
already supplied by the installed analytic path-cover construction. -/
theorem s22c0_pathCoverProj_mdifferentiable
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (x₀ : S) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (RiemannDynamics.pathCoverProj x₀) := by
  intro pc
  obtain ⟨e, he, f, hf, hpc, hppc, hall, hcomm⟩ :=
    RiemannDynamics.exists_charts_pathCoverProj_comm x₀ pc
  have hA : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e pc :=
    contMDiffAt_of_mem_maximalAtlas he hpc
  have hepc : e pc ∈ f.target := by
    rw [← hcomm pc hpc]
    exact f.map_source hppc
  have hB : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.symm (e pc) :=
    contMDiffAt_symm_of_mem_maximalAtlas hf hepc
  have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun qc : RiemannDynamics.PathCover x₀ => f.symm (e qc)) pc := hB.comp pc hA
  have hP : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (RiemannDynamics.pathCoverProj x₀) pc := by
    refine hF.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hpc) ?_)
    intro qc hqc
    change RiemannDynamics.pathCoverProj x₀ qc = f.symm (e qc)
    rw [← hcomm qc hqc]
    exact (f.left_inv (hall qc hqc)).symm
  exact hP.mdifferentiableAt (by simp)

/-- Connectedness of the charted base supplies an actual path from x₀ to
each endpoint, hence a point of the concrete cover over every base point. -/
theorem s22c0_pathCoverProj_surjective
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] (x₀ : S) :
    Function.Surjective (RiemannDynamics.pathCoverProj x₀) := by
  letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  intro y
  exact ⟨⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩, rfl⟩

/-- Conjugating an actual analytic loop deck map by an actual analytic
diffeomorphism gives a holomorphic homeomorphism with the same fiber action. -/
theorem s22ct_pathCover_conjugate_deck
    {S : Type u} {T : Type v} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace T] [ChartedSpace ℂ T]
    (x₀ : S) (e : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ T)
    (γ : FundamentalGroup S x₀) :
    ∃ F : T ≃ₜ T, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
      (∀ y, F y = e (RiemannDynamics.pathCoverDeck x₀ γ (e.symm y))) ∧
      (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) ∘ F =
        RiemannDynamics.pathCoverProj x₀ ∘ e.symm ∧
      (∀ y, F y = y → ∀ z, F z = z) := by
  obtain ⟨d, hd⟩ := RiemannDynamics.exists_pathCoverDeck_diffeomorph x₀ γ
  let a : T ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ T := (e.symm.trans d).trans e
  have hform : ∀ y, a y = e (RiemannDynamics.pathCoverDeck x₀ γ (e.symm y)) := by
    intro y
    change e (d (e.symm y)) = e (RiemannDynamics.pathCoverDeck x₀ γ (e.symm y))
    rw [hd]
  refine ⟨a.toHomeomorph, a.contMDiff.mdifferentiable (by simp), hform, ?_, ?_⟩
  · funext y
    change RiemannDynamics.pathCoverProj x₀ (e.symm (a y)) =
      RiemannDynamics.pathCoverProj x₀ (e.symm y)
    rw [hform, e.symm_apply_apply]
    exact RiemannDynamics.pathCoverProj_deck x₀ γ (e.symm y)
  · intro y hy z
    have hfix : RiemannDynamics.pathCoverDeck x₀ γ (e.symm y) = e.symm y := by
      apply e.toEquiv.injective
      exact (hform y).symm.trans (hy.trans (e.apply_symm_apply y).symm)
    have hγ : γ = 1 := s22c1_deck_fixed_eq_one x₀ γ (e.symm y) hfix
    change a z = z
    rw [hform, hγ, s22c1_deck_one, e.apply_symm_apply]

/-- A genus greater than one gives two noncommuting actual loop deck maps;
their analytic conjugates on the plane would be commuting translations. -/
theorem s22cp_pathCover_not_plane_of_genus_gt_one
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (x₀ : S) {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) :
    ¬ RSConformallyEquivalent (RiemannDynamics.PathCover x₀) ℂ := by
  rintro ⟨f, hf⟩
  obtain ⟨e, -⟩ := k22u_biholomorphic_diffeomorph hf
  obtain ⟨γ, δ, hnoncomm⟩ := s22c1_exists_noncommuting_deck_of_genus_gt_one x₀ hg hS
  obtain ⟨F, hF, hformF, -, hfixF⟩ := s22ct_pathCover_conjugate_deck x₀ e γ
  obtain ⟨G, hG, hformG, -, hfixG⟩ := s22ct_pathCover_conjugate_deck x₀ e δ
  have hcomm := s22c4_commute_of_mdifferentiable F G hF hG hfixF hfixG
  apply hnoncomm
  apply EquivLike.injective e
  have h := hcomm (e (RiemannDynamics.pathCoverBase x₀))
  simpa only [hformF, hformG, e.symm_apply_apply] using h

/-- Analytic conjugacy with the upper half-plane transports the actual
projection and concrete transitive loop action to the four exact C6 inputs. -/
theorem s22ct_pathCover_upperHalf_input
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    (e : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ UpperHalfPlane) :
    IsCoveringMap (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) ∧
      Function.Surjective (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) ∧
      (∀ τ₁ τ₂ : UpperHalfPlane,
        (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) τ₁ =
          (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) τ₂ →
        ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
          MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
          (RiemannDynamics.pathCoverProj x₀ ∘ e.symm) ∘ F =
            RiemannDynamics.pathCoverProj x₀ ∘ e.symm ∧ F τ₁ = τ₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph
      e.symm.toHomeomorph
  · exact (s22c0_pathCoverProj_mdifferentiable x₀).comp
      (e.symm.contMDiff.mdifferentiable (by simp))
  · exact (s22c0_pathCoverProj_surjective x₀).comp e.symm.toEquiv.surjective
  · intro τ₁ τ₂ hτ
    obtain ⟨γ, hγ⟩ := RiemannDynamics.pathCoverDeck_transitive
      x₀ (e.symm τ₁) (e.symm τ₂) hτ
    obtain ⟨F, hF, hform, hpres, -⟩ := s22ct_pathCover_conjugate_deck
      x₀ e (FundamentalGroup.fromPath γ)
    refine ⟨F, hF, hpres, ?_⟩
    rw [hform, hγ, e.apply_symm_apply]

/-- The installed biholomorphic-to-diffeomorphism bridge and the actual
Cayley diffeomorphism turn the disc alternative into the exact C6 v2 data. -/
theorem s22ct_pathCover_disc_c6_input
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    (hdisc : RSConformallyEquivalent (RiemannDynamics.PathCover x₀) unitDiscOpens) :
    ∃ p : UpperHalfPlane → S, IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
      Function.Surjective p ∧
      (∀ τ₁ τ₂ : UpperHalfPlane, p τ₁ = p τ₂ →
        ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
          MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ p ∘ F = p ∧ F τ₁ = τ₂) := by
  obtain ⟨f, hf⟩ := hdisc
  obtain ⟨d, -⟩ := k22u_biholomorphic_diffeomorph hf
  obtain ⟨c, -, -⟩ := s22c6_cayley_diffeomorph
  let e : RiemannDynamics.PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ UpperHalfPlane :=
    d.trans c.symm
  exact ⟨RiemannDynamics.pathCoverProj x₀ ∘ e.symm,
    s22ct_pathCover_upperHalf_input x₀ e⟩

/-- A Fuchsian group: a subgroup of `SL(2, ℝ)` acting properly discontinuously on `ℍ`. -/
def IsFuchsian (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ∀ C : Set UpperHalfPlane, IsCompact C → {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty}.Finite

/-- `Γ` acts freely on `ℍ` (no element other than `±I` has a fixed point): the covering group of a
Riemann surface. -/
def ActsFreely (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1

/-- `p : ℍ → S` realizes `S` as `ℍ/Γ`: `p` is a holomorphic covering map whose fibres are
exactly the `Γ`-orbits. -/
def IsUniformization (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S) :
    Prop :=
  IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ Function.Surjective p ∧
    ∀ τ₁ τ₂ : UpperHalfPlane, p τ₁ = p τ₂ ↔ ∃ γ ∈ Γ, γ • τ₁ = τ₂

/-- Genuine holomorphic fiber-transitive deck maps give the full subgroup of
SL(2,R) preserving p, with exactly its orbits as the fibers of the same p.
No representative-sign choice or lifted action homomorphism is needed. -/
theorem s22c6_full_stabilizer_isUniformization
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (p : UpperHalfPlane → S) (hcover : IsCoveringMap p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hsurj : Function.Surjective p)
    (hdeck : ∀ τ₁ τ₂ : UpperHalfPlane, p τ₁ = p τ₂ →
      ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ p ∘ F = p ∧ F τ₁ = τ₂) :
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ m : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        m ∈ Γ ↔ ∀ z : UpperHalfPlane, p (m • z) = p z) ∧
      IsUniformization Γ p := by
  let Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    { carrier := {m | ∀ z : UpperHalfPlane, p (m • z) = p z}
      one_mem' := by
        intro z
        rw [one_smul]
      mul_mem' := by
        intro m n hm hn z
        rw [mul_smul]
        exact (hm (n • z)).trans (hn z)
      inv_mem' := by
        intro m hm z
        have h := hm (m⁻¹ • z)
        rw [smul_inv_smul] at h
        exact h.symm }
  refine ⟨Γ, ?_, ?_⟩
  · intro m
    rfl
  · refine ⟨hcover, hhol, hsurj, ?_⟩
    intro τ₁ τ₂
    constructor
    · intro hτ
      obtain ⟨F, hF, hpF, hFτ⟩ := hdeck τ₁ τ₂ hτ
      obtain ⟨m, hm⟩ := k22c5_eq_smul_of_mdifferentiable F hF
      refine ⟨m, ?_, ?_⟩
      · change ∀ z : UpperHalfPlane, p (m • z) = p z
        intro z
        rw [← hm z]
        exact congrFun hpF z
      · exact (hm τ₁).symm.trans hFτ
    · intro horbit
      obtain ⟨m, hm, hmove⟩ := horbit
      have hpres : p (m • τ₁) = p τ₁ :=
        (show ∀ z : UpperHalfPlane, p (m • z) = p z from hm) τ₁
      exact hpres.symm.trans (congrArg p hmove)

/-- A Hausdorff connected analytic Riemann surface of genus greater than one
has a genuine holomorphic upper-half-plane uniformization. The concrete path
cover is neither compact nor conformally equivalent to the plane; its disc
alternative yields the full subgroup preserving the same projection. -/
theorem s22hg_exists_fuchsian_uniformization
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p := by
  classical
  let x₀ : S := Classical.choice (inferInstance : Nonempty S)
  letI : T2Space (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.t2space_pathCover x₀
  letI : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  have hdisc : RSConformallyEquivalent (RiemannDynamics.PathCover x₀) unitDiscOpens := by
    rcases (thm22_2_uniformization (S := RiemannDynamics.PathCover x₀)).1 with
      hcompact | hplane | hdisc
    · exact False.elim ((s22c3_pathCover_not_compact_of_genus_gt_one x₀ hg hS) hcompact.1)
    · exact False.elim ((s22cp_pathCover_not_plane_of_genus_gt_one x₀ hg hS) hplane)
    · exact hdisc
  obtain ⟨p, hcover, hhol, hsurj, hdeck⟩ :=
    s22ct_pathCover_disc_c6_input x₀ hdisc
  obtain ⟨Γ, _hfull, hp⟩ :=
    s22c6_full_stabilizer_isUniformization p hcover hhol hsurj hdeck
  -- Local reuse of S27 s27g_actsFreely and utm_x2_isFuchsian: S27 already imports S22,
  -- so importing their module here would create a cycle. Their public declarations stay in S27.
  have hfree : ActsFreely Γ := by
    intro γ hγ τ hτ
    have hcomp : p ∘ (fun z : UpperHalfPlane => γ • z) = p ∘ id := by
      funext z
      exact ((hp.2.2.2 z (γ • z)).2 ⟨γ, hγ, rfl⟩).symm
    have heq : (fun z : UpperHalfPlane => γ • z) = id :=
      hp.1.eq_of_comp_eq (continuous_const_smul γ) continuous_id hcomp τ hτ
    exact utm_sl2_eq_of_bounded_displacement γ (C := 0) fun z => by
      rw [show γ • z = z from congrFun heq z, dist_self]
  have hF : IsFuchsian Γ := by
    intro C hC
    by_contra hinf
    let e := Set.Infinite.natEmbedding _ hinf
    set γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun n => (e n : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      with hγs
    have hγinj : Function.Injective γs := fun m n h => e.injective (Subtype.ext h)
    have hγΓ : ∀ n, γs n ∈ Γ := fun n => (e n).2.1
    have hex : ∀ n, ∃ c ∈ C, γs n • c ∈ C := by
      intro n
      obtain ⟨_, ⟨c, hc, rfl⟩, hy⟩ := (e n).2.2
      exact ⟨c, hc, hy⟩
    choose c hcC hγcC using hex
    have hpair : ∀ n, (c n, γs n • c n) ∈ C ×ˢ C := fun n => ⟨hcC n, hγcC n⟩
    obtain ⟨⟨a, a'⟩, -, φ, hφ, hlim⟩ := (hC.prod hC).tendsto_subseq hpair
    have h1 : Tendsto (fun k => c (φ k)) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hlim
    have h2 : Tendsto (fun k => γs (φ k) • c (φ k)) atTop (𝓝 a') := (continuous_snd.tendsto _).comp hlim
    have hpfib : ∀ n, p (γs n • c n) = p (c n) := fun n =>
      ((hp.2.2.2 (c n) (γs n • c n)).2 ⟨γs n, hγΓ n, rfl⟩).symm
    have hpa : p a = p a' := by
      have t1 : Tendsto (fun k => p (c (φ k))) atTop (𝓝 (p a)) := (hp.1.continuous.tendsto a).comp h1
      have t2 : Tendsto (fun k => p (γs (φ k) • c (φ k))) atTop (𝓝 (p a')) :=
        (hp.1.continuous.tendsto a').comp h2
      simp only [hpfib] at t2
      exact tendsto_nhds_unique t1 t2
    obtain ⟨g, hgΓ, hga⟩ := (hp.2.2.2 a a').1 hpa
    have h3 : Tendsto (fun k => (g⁻¹ * γs (φ k)) • c (φ k)) atTop (𝓝 a) := by
      have h := ((continuous_const_smul g⁻¹).tendsto a').comp h2
      rw [← hga, inv_smul_smul] at h
      refine h.congr fun k => ?_
      simp only [Function.comp_apply, mul_smul]
    obtain ⟨E, haE, hpE⟩ := hp.1.isLocalHomeomorph a
    have hEn : E.source ∈ 𝓝 a := E.open_source.mem_nhds haE
    have hev : ∀ᶠ k in atTop, γs (φ k) = g ∨ γs (φ k) = g * -1 := by
      filter_upwards [h1 hEn, h3 hEn] with k hk1 hk3
      have hmem : g⁻¹ * γs (φ k) ∈ Γ := Γ.mul_mem (Γ.inv_mem hgΓ) (hγΓ _)
      have hpeq : p ((g⁻¹ * γs (φ k)) • c (φ k)) = p (c (φ k)) :=
        ((hp.2.2.2 (c (φ k)) _).2 ⟨_, hmem, rfl⟩).symm
      rw [hpE] at hpeq
      have hfix : (g⁻¹ * γs (φ k)) • c (φ k) = c (φ k) := E.injOn hk3 hk1 hpeq
      rcases hfree _ hmem _ hfix with h | h
      · exact Or.inl (inv_mul_eq_one.1 h).symm
      · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hinj : Function.Injective fun k => γs (φ (k + N)) := fun m n h =>
      add_right_cancel (hφ.injective (hγinj h))
    have hmem : ∀ k, γs (φ (k + N)) ∈ ({g, g * -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := fun k => by
      rcases hN (k + N) (Nat.le_add_left N k) with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact Set.infinite_of_injective_forall_mem hinj hmem (Set.toFinite _)
  exact ⟨Γ, p, hF, hfree, hp⟩

/-- The disc alternative of the path cover gives a torsion-free Fuchsian uniformization `ℍ/Γ`
(the proof of `s22hg_exists_fuchsian_uniformization` after the trichotomy, without the genus hypothesis). -/
theorem s22tc_disc_case
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    (hdisc : RSConformallyEquivalent (RiemannDynamics.PathCover x₀) unitDiscOpens) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p := by
  classical
  obtain ⟨p, hcover, hhol, hsurj, hdeck⟩ :=
    s22ct_pathCover_disc_c6_input x₀ hdisc
  obtain ⟨Γ, _hfull, hp⟩ :=
    s22c6_full_stabilizer_isUniformization p hcover hhol hsurj hdeck
  -- Local reuse of S27 s27g_actsFreely and utm_x2_isFuchsian: S27 already imports S22,
  -- so importing their module here would create a cycle. Their public declarations stay in S27.
  have hfree : ActsFreely Γ := by
    intro γ hγ τ hτ
    have hcomp : p ∘ (fun z : UpperHalfPlane => γ • z) = p ∘ id := by
      funext z
      exact ((hp.2.2.2 z (γ • z)).2 ⟨γ, hγ, rfl⟩).symm
    have heq : (fun z : UpperHalfPlane => γ • z) = id :=
      hp.1.eq_of_comp_eq (continuous_const_smul γ) continuous_id hcomp τ hτ
    exact utm_sl2_eq_of_bounded_displacement γ (C := 0) fun z => by
      rw [show γ • z = z from congrFun heq z, dist_self]
  have hF : IsFuchsian Γ := by
    intro C hC
    by_contra hinf
    let e := Set.Infinite.natEmbedding _ hinf
    set γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun n => (e n : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      with hγs
    have hγinj : Function.Injective γs := fun m n h => e.injective (Subtype.ext h)
    have hγΓ : ∀ n, γs n ∈ Γ := fun n => (e n).2.1
    have hex : ∀ n, ∃ c ∈ C, γs n • c ∈ C := by
      intro n
      obtain ⟨_, ⟨c, hc, rfl⟩, hy⟩ := (e n).2.2
      exact ⟨c, hc, hy⟩
    choose c hcC hγcC using hex
    have hpair : ∀ n, (c n, γs n • c n) ∈ C ×ˢ C := fun n => ⟨hcC n, hγcC n⟩
    obtain ⟨⟨a, a'⟩, -, φ, hφ, hlim⟩ := (hC.prod hC).tendsto_subseq hpair
    have h1 : Tendsto (fun k => c (φ k)) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hlim
    have h2 : Tendsto (fun k => γs (φ k) • c (φ k)) atTop (𝓝 a') := (continuous_snd.tendsto _).comp hlim
    have hpfib : ∀ n, p (γs n • c n) = p (c n) := fun n =>
      ((hp.2.2.2 (c n) (γs n • c n)).2 ⟨γs n, hγΓ n, rfl⟩).symm
    have hpa : p a = p a' := by
      have t1 : Tendsto (fun k => p (c (φ k))) atTop (𝓝 (p a)) := (hp.1.continuous.tendsto a).comp h1
      have t2 : Tendsto (fun k => p (γs (φ k) • c (φ k))) atTop (𝓝 (p a')) :=
        (hp.1.continuous.tendsto a').comp h2
      simp only [hpfib] at t2
      exact tendsto_nhds_unique t1 t2
    obtain ⟨g, hgΓ, hga⟩ := (hp.2.2.2 a a').1 hpa
    have h3 : Tendsto (fun k => (g⁻¹ * γs (φ k)) • c (φ k)) atTop (𝓝 a) := by
      have h := ((continuous_const_smul g⁻¹).tendsto a').comp h2
      rw [← hga, inv_smul_smul] at h
      refine h.congr fun k => ?_
      simp only [Function.comp_apply, mul_smul]
    obtain ⟨E, haE, hpE⟩ := hp.1.isLocalHomeomorph a
    have hEn : E.source ∈ 𝓝 a := E.open_source.mem_nhds haE
    have hev : ∀ᶠ k in atTop, γs (φ k) = g ∨ γs (φ k) = g * -1 := by
      filter_upwards [h1 hEn, h3 hEn] with k hk1 hk3
      have hmem : g⁻¹ * γs (φ k) ∈ Γ := Γ.mul_mem (Γ.inv_mem hgΓ) (hγΓ _)
      have hpeq : p ((g⁻¹ * γs (φ k)) • c (φ k)) = p (c (φ k)) :=
        ((hp.2.2.2 (c (φ k)) _).2 ⟨_, hmem, rfl⟩).symm
      rw [hpE] at hpeq
      have hfix : (g⁻¹ * γs (φ k)) • c (φ k) = c (φ k) := E.injOn hk3 hk1 hpeq
      rcases hfree _ hmem _ hfix with h | h
      · exact Or.inl (inv_mul_eq_one.1 h).symm
      · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hinj : Function.Injective fun k => γs (φ (k + N)) := fun m n h =>
      add_right_cancel (hφ.injective (hγinj h))
    have hmem : ∀ k, γs (φ (k + N)) ∈ ({g, g * -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := fun k => by
      rcases hN (k + N) (Nat.le_add_left N k) with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact Set.infinite_of_injective_forall_mem hinj hmem (Set.toFinite _)
  exact ⟨Γ, p, hF, hfree, hp⟩

/-- A holomorphic homeomorphism of a compact Riemann surface `P` with `P ∖ {p} ≅ ℂ` has a fixed
point: either `F p = p`, or `φ F φ⁻¹` is a Möbius map `c + 1 / (α (z - a))` whose fixed-point
equation is a quadratic. -/
theorem s22tc_fixed_point {P : Type u} [TopologicalSpace P] [ChartedSpace ℂ P] [T2Space P]
    [IsManifold 𝓘(ℂ) ω P] [CompactSpace P] (p : P)
    (hφ : RSConformallyEquivalent (⟨{p}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens P) ℂ)
    (F : P ≃ₜ P) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : ∃ x, F x = x := by
  classical
  by_cases hp : F p = p
  · exact ⟨p, hp⟩
  obtain ⟨φ, hφb⟩ := hφ
  obtain ⟨e, he⟩ := k22u_biholomorphic_homeomorph hφb
  have hem : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (e : _ → ℂ) := by rw [he]; exact hφb.1
  have hesm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (e.symm : ℂ → _) :=
    (IsBiholomorphic.homeomorph_symm (e := e) (by rw [he]; exact hφb)).1
  let U : TopologicalSpace.Opens P := ⟨{p}ᶜ, isOpen_compl_singleton⟩
  have hne : Nonempty ↥U := ⟨e.symm 0⟩
  let Φ : P → ℂ := fun x => if hx : x = p then 0 else e ⟨x, hx⟩
  have hΦ : ∀ (x : P) (hx : x ≠ p), Φ x = e ⟨x, hx⟩ := fun x hx => by
    simp only [Φ, hx, ↓reduceDIte]
  have hΦinj : ∀ (x y : P), x ≠ p → y ≠ p → Φ x = Φ y → x = y := by
    intro x y hx hy hxy
    rw [hΦ x hx, hΦ y hy] at hxy
    exact congrArg Subtype.val (e.injective hxy)
  have hΦm : ∀ x : P, x ≠ p → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ x := by
    intro x hx
    let i := U.openPartialHomeomorphSubtypeCoe hne
    have hi := k22u_mdifferentiable_opens_inclusion U hne
    have htg : i.target = {p}ᶜ :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target U hne
    have hxt : x ∈ i.target := by rw [htg]; exact hx
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => e (i.symm y)) x :=
      (hem (i.symm x)).comp x ((hi.2 x hxt).mdifferentiableAt (i.open_target.mem_nhds hxt))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [i.open_target.mem_nhds hxt] with y hy
    have hy' : y ≠ p := by rw [htg] at hy; exact hy
    rw [hΦ y hy']
    congr 1
    apply Subtype.ext
    exact (i.right_inv hy).symm
  have hq : F.symm p ≠ p := fun h => hp (by
    have := F.apply_symm_apply p
    rwa [h] at this)
  let ι : ℂ → P := fun z => ((e.symm z : ↥U) : P)
  have hι : ∀ z, ι z ≠ p := fun z => (e.symm z).2
  have hιm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp) |>.comp hesm
  let X : ℂ → P := fun z => F (ι z)
  have hXm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X := hF.comp hιm
  let a : ℂ := e ⟨F.symm p, hq⟩
  let c : ℂ := e ⟨F p, hp⟩
  have hXp : ∀ z, X z = p ↔ z = a := by
    intro z
    constructor
    · intro hX
      have h1 : ι z = F.symm p := (F.toEquiv.eq_symm_apply).2 hX
      have h2 : e.symm z = ⟨F.symm p, hq⟩ := Subtype.ext h1
      rw [← e.apply_symm_apply z, h2]
    · intro hz
      rw [hz]
      have h2 : e.symm a = ⟨F.symm p, hq⟩ := e.symm_apply_apply _
      have h1 : ι a = F.symm p := congrArg Subtype.val h2
      change F (ι a) = p
      rw [h1, F.apply_symm_apply]
  have hXr : ∀ z, X z ≠ F p := fun z h => hι z (F.injective h)
  let h : ℂ → ℂ := fun z => Φ (X z)
  have hhd : ∀ z, z ≠ a → DifferentiableAt ℂ h z := by
    intro z hz
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h z :=
      (hΦm (X z) (fun hh => hz ((hXp z).1 hh))).comp z (hXm z)
    exact mdifferentiableAt_iff_differentiableAt.mp h1
  have hhc : ∀ z, z ≠ a → h z - c ≠ 0 := by
    intro z hz hh
    have hz' : X z ≠ p := fun h' => hz ((hXp z).1 h')
    have : Φ (X z) = Φ (F p) := by
      rw [hΦ (F p) hp]
      exact sub_eq_zero.mp hh
    exact hXr z (hΦinj _ _ hz' hp this)
  have hXa : X a = p := (hXp a).2 rfl
  -- `‖h z‖ → ∞` as `z → a`
  have hinf : Filter.Tendsto (fun z => ‖h z‖) (𝓝[≠] a) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro R
    have hK : IsCompact (e.symm '' Metric.closedBall (0 : ℂ) R) :=
      (isCompact_closedBall (0 : ℂ) R).image e.symm.continuous
    have hK' : IsCompact (Subtype.val '' (e.symm '' Metric.closedBall (0 : ℂ) R) : Set P) :=
      hK.image continuous_subtype_val
    have hpK : p ∉ (Subtype.val '' (e.symm '' Metric.closedBall (0 : ℂ) R) : Set P) := by
      rintro ⟨y, -, hy⟩
      exact y.2 hy
    have hXc : Filter.Tendsto X (𝓝 a) (𝓝 p) := by
      have : Continuous X := hXm.continuous
      rw [← hXa]
      exact this.tendsto a
    have hev : ∀ᶠ z in 𝓝 a, X z ∈ (Subtype.val '' (e.symm '' Metric.closedBall (0 : ℂ) R) : Set P)ᶜ :=
      hXc (hK'.isClosed.isOpen_compl.mem_nhds hpK)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hza
    have hz' : X z ≠ p := fun h' => hza ((hXp z).1 h')
    by_contra hlt
    have hlt := not_le.mp hlt
    apply hz
    have hmem : e ⟨X z, hz'⟩ ∈ Metric.closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff]
      have : h z = e ⟨X z, hz'⟩ := hΦ (X z) hz'
      rw [← this]
      exact hlt.le
    exact ⟨_, ⟨_, hmem, rfl⟩, by simp⟩
  let u : ℂ → ℂ := fun z => if z = a then 0 else (h z - c)⁻¹
  have hu_ne : ∀ z, z ≠ a → u z = (h z - c)⁻¹ := fun z hz => by simp only [u, hz, ↓reduceIte]
  have hua : u a = 0 := by simp only [u, ↓reduceIte]
  have hu0 : ∀ z, z ≠ a → u z ≠ 0 := fun z hz => by
    rw [hu_ne z hz]; exact inv_ne_zero (hhc z hz)
  have hutend : Filter.Tendsto u (𝓝[≠] a) (𝓝 0) := by
    have h0 : Filter.Tendsto (fun z => ‖h z‖ - ‖c‖) (𝓝[≠] a) Filter.atTop := by
      simpa only [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-‖c‖) hinf
    have h1 := Filter.tendsto_atTop_mono (fun z => norm_sub_norm_le (h z) c) h0
    have h2 : Filter.Tendsto (fun z => (‖h z - c‖)⁻¹) (𝓝[≠] a) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hu_ne z hz, norm_inv]
  have hucont : ContinuousAt u a :=
    continuousWithinAt_compl_self.mp (by rw [ContinuousWithinAt, hua]; exact hutend)
  have hud_ne : ∀ z, z ≠ a → DifferentiableAt ℂ u z := by
    intro z hz
    have : DifferentiableAt ℂ (fun w => (h w - c)⁻¹) z :=
      ((hhd z hz).sub_const c).inv (hhc z hz)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact hu_ne w hw
  have hud : Differentiable ℂ u := by
    intro z
    by_cases hz : z = a
    · rw [hz]
      refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hucont).differentiableAt
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hud_ne w hw
    · exact hud_ne z hz
  have huinj : Set.InjOn u Set.univ := by
    intro z _ w _ hzw
    by_cases hz : z = a
    · by_cases hw : w = a
      · rw [hz, hw]
      · exact absurd (by rw [← hzw, hz, hua]) (hu0 w hw)
    · by_cases hw : w = a
      · exact absurd (by rw [hzw, hw, hua]) (hu0 z hz)
      · rw [hu_ne z hz, hu_ne w hw, inv_inj, sub_left_inj] at hzw
        have hz' : X z ≠ p := fun h' => hz ((hXp z).1 h')
        have hw' : X w ≠ p := fun h' => hw ((hXp w).1 h')
        have h1 : X z = X w := hΦinj _ _ hz' hw' hzw
        have h2 : ι z = ι w := F.injective h1
        have h3 : e.symm z = e.symm w := Subtype.ext h2
        exact e.symm.injective h3
  have huimg : u '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y = 0
    · exact ⟨a, trivial, by rw [hua, hy]⟩
    · let w0 : ℂ := c + y⁻¹
      let x' : P := ((e.symm w0 : ↥U) : P)
      have hx'p : x' ≠ p := (e.symm w0).2
      have hx'r : x' ≠ F p := by
        intro h'
        have h2 : e.symm w0 = ⟨F p, hp⟩ := Subtype.ext h'
        have h3 : w0 = c := by rw [← e.apply_symm_apply w0, h2]
        exact inv_ne_zero hy (by simpa [w0] using h3)
      have hFx : F.symm x' ≠ p := by
        intro h'
        apply hx'r
        rw [← F.apply_symm_apply x', h']
      let z : ℂ := e ⟨F.symm x', hFx⟩
      have hιz : ι z = F.symm x' := by
        have : e.symm z = ⟨F.symm x', hFx⟩ := e.symm_apply_apply _
        exact congrArg Subtype.val this
      have hXz : X z = x' := by
        change F (ι z) = x'
        rw [hιz, F.apply_symm_apply]
      have hza : z ≠ a := fun h' => hx'p (by rw [← hXz]; exact (hXp z).2 h')
      refine ⟨z, trivial, ?_⟩
      rw [hu_ne z hza]
      have : h z = w0 := by
        change Φ (X z) = w0
        rw [hXz, hΦ x' hx'p]
        exact e.apply_symm_apply w0
      rw [this]
      simp only [w0, add_sub_cancel_left, inv_inv]
  obtain ⟨α, β, hα, hl⟩ := nx_entire_affine (φ := u) ⟨hud.differentiableOn, huinj, huimg⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim α (β - α * c) (-(β * c + 1)))
  obtain ⟨z0, hz0⟩ := exists_quadratic_eq_zero hα ⟨s, hs⟩
  have hprod : (z0 - c) * (α * z0 + β) = 1 := by linear_combination hz0
  have hz0a : z0 ≠ a := by
    intro hz
    have : α * z0 + β = 0 := by rw [← hl z0, hz, hua]
    rw [this, mul_zero] at hprod
    exact zero_ne_one hprod
  have hhz : h z0 = z0 := by
    have h1 : u z0 = (h z0 - c)⁻¹ := hu_ne z0 hz0a
    rw [hl z0] at h1
    have h2 : (h z0 - c)⁻¹ * (z0 - c) = 1 := by rw [← h1, mul_comm]; exact hprod
    have := (inv_mul_eq_one₀ (hhc z0 hz0a)).1 h2
    linear_combination this
  refine ⟨ι z0, ?_⟩
  have hz' : X z0 ≠ p := fun h' => hz0a ((hXp z0).1 h')
  apply hΦinj _ _ hz' (hι z0)
  rw [hΦ (ι z0) (hι z0)]
  have : e ⟨ι z0, hι z0⟩ = z0 := e.apply_symm_apply z0
  rw [this]
  exact hhz

/-- The compact alternative of the uniformization trichotomy for the path cover gives a compact,
simply connected surface: every deck map of the sphere has a fixed point, hence is trivial. -/
theorem s22tc_sphere_case {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    [T2Space (RiemannDynamics.PathCover x₀)] (hc : CompactSpace (RiemannDynamics.PathCover x₀))
    (hp : ∃ p : RiemannDynamics.PathCover x₀, RSConformallyEquivalent
      (⟨{p}ᶜ, isOpen_compl_singleton⟩ :
        TopologicalSpace.Opens (RiemannDynamics.PathCover x₀)) ℂ) :
    CompactSpace S ∧ SimplyConnectedSpace S := by
  classical
  have : CompactSpace (RiemannDynamics.PathCover x₀) := hc
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (RiemannDynamics.pathCoverProj x₀) :=
      (RiemannDynamics.pathCoverProj_isCoveringMap x₀).continuous
    have hr := isCompact_range hcont
    rw [(s22c0_pathCoverProj_surjective x₀).range_eq] at hr
    exact isCompact_univ_iff.mp hr
  · have htriv : ∀ γ : FundamentalGroup S x₀, γ = 1 := by
      intro γ
      obtain ⟨p, hφ⟩ := hp
      obtain ⟨d, hd⟩ := RiemannDynamics.exists_pathCoverDeck_diffeomorph x₀ γ
      obtain ⟨x, hx⟩ := s22tc_fixed_point p hφ d.toHomeomorph
        (d.contMDiff.mdifferentiable (by simp))
      exact s22c1_deck_fixed_eq_one x₀ γ x (by rw [← hd]; exact hx)
    have : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
    have : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
    refine simply_connected_iff_paths_homotopic.mpr ⟨inferInstance, fun x y => ⟨fun u v => ?_⟩⟩
    have hx : ∀ γ : FundamentalGroup S x, γ = 1 := by
      intro γ
      obtain ⟨γ', rfl⟩ :=
        (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ x).surjective γ
      rw [htriv γ', map_one]
    have h1 : u.trans v.symm = Path.Homotopic.Quotient.refl x := hx (u.trans v.symm)
    have h2 := congrArg (fun η : Path.Homotopic.Quotient x x => η.trans v) h1
    simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] using h2

/-- Chart transfer for maps out of `ℂ`: if `p : ℂ → X` is holomorphic at `u` (into a Riemann surface with a
holomorphic atlas) and `p u` lies in the source of the chart at `y`, then `φ_y ∘ p` is complex differentiable at
`u` (the chart `φ_y` is holomorphic on its source since the atlas is holomorphic). -/
theorem s22tc_d_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {p : ℂ → X} {u : ℂ} (hp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) p u) (y : X)
    (hu : p u ∈ (chartAt ℂ y).source) : DifferentiableAt ℂ (fun z => chartAt ℂ y (p z)) u :=
  ((mdifferentiableAt_atlas (chart_mem_atlas ℂ y) hu).comp u hp).differentiableAt

/-- Holomorphic local sections: if `p : ℂ → X` is a holomorphic local homeomorphism into a Riemann surface with
a holomorphic atlas, then for every `u₀` there is a map `s : X → ℂ`, holomorphic at `p u₀`, with `s (p u₀) = u₀`
and `p ∘ s = id` near `p u₀` (`s = (φ ∘ p|_W)⁻¹ ∘ φ` for the chart `φ` at `p u₀` and a neighbourhood `W` of `u₀`
on which `p` is injective; the inverse of the injective holomorphic `φ ∘ p` is holomorphic). -/
theorem s22tc_local_section {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {p : ℂ → X} (hpl : IsLocalHomeomorph p) (hpd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (u₀ : ℂ) :
    ∃ s : X → ℂ, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s (p u₀) ∧ s (p u₀) = u₀ ∧
      ∀ᶠ y in 𝓝 (p u₀), p (s y) = y := by
  obtain ⟨e, he, hpe⟩ := hpl u₀
  have hpcont : Continuous p := hpl.continuous
  let W : Set ℂ := e.source ∩ p ⁻¹' (chartAt ℂ (p u₀)).source
  have hW : IsOpen W := e.open_source.inter (hpcont.isOpen_preimage _ (chartAt ℂ (p u₀)).open_source)
  let h : ℂ → ℂ := fun z => chartAt ℂ (p u₀) (p z)
  have hhd : DifferentiableOn ℂ h W := fun z hz =>
    (s22tc_d_chart (hpd z) (p u₀) hz.2).differentiableWithinAt
  have hinj : InjOn h W := by
    intro a ha b hb hab
    have hab' : p a = p b := (chartAt ℂ (p u₀)).injOn ha.2 hb.2 hab
    rw [hpe] at hab'
    exact e.injOn ha.1 hb.1 hab'
  obtain ⟨hopen, hgd⟩ := RMT.differentiableOn_invFunOn_of_injOn hW hhd hinj
  have hu₀W : u₀ ∈ W := ⟨he, mem_chart_source ℂ (p u₀)⟩
  have hmem : chartAt ℂ (p u₀) (p u₀) ∈ h '' W := ⟨u₀, hu₀W, rfl⟩
  have hgD : DifferentiableAt ℂ (Function.invFunOn h W) (chartAt ℂ (p u₀) (p u₀)) :=
    hgd.differentiableAt (hopen.mem_nhds hmem)
  refine ⟨Function.invFunOn h W ∘ chartAt ℂ (p u₀), ?_, ?_, ?_⟩
  · exact hgD.mdifferentiableAt.comp (p u₀)
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ (p u₀)) (mem_chart_source ℂ (p u₀)))
  · exact hinj.leftInvOn_invFunOn hu₀W
  · have hxt : p u₀ ∈ e.target := by
      rw [hpe]
      exact e.map_source he
    have hnhds : e.target ∩ (chartAt ℂ (p u₀)).source ∈ 𝓝 (p u₀) :=
      (e.open_target.inter (chartAt ℂ (p u₀)).open_source).mem_nhds ⟨hxt, mem_chart_source ℂ (p u₀)⟩
    filter_upwards [hnhds] with y hy
    have h1 : e.symm y ∈ e.source := e.map_target hy.1
    have h2 : p (e.symm y) = y := by
      rw [hpe]
      exact e.right_inv hy.1
    have h3 : e.symm y ∈ W := ⟨h1, by rw [Set.mem_preimage, h2]; exact hy.2⟩
    have h4 : Function.invFunOn h W (chartAt ℂ (p u₀) y) = e.symm y := by
      have h5 : chartAt ℂ (p u₀) y = h (e.symm y) := by
        simp only [h, h2]
      rw [h5]
      exact hinj.leftInvOn_invFunOn h3
    show p (Function.invFunOn h W (chartAt ℂ (p u₀) y)) = y
    rw [h4, h2]

/-- **D** (descent of holomorphy): if `p : ℂ → X` is a surjective holomorphic covering of a Riemann surface with a
holomorphic atlas and `f : X → Y` has `f ∘ p` holomorphic, then `f` is holomorphic (near every point
`f = (f ∘ p) ∘ s` for a local section `s` of `p`, which is holomorphic in charts). -/
theorem s22tc_descend {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y] {p : ℂ → X}
    (hpc : IsCoveringMap p) (hpd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hps : Function.Surjective p) {f : X → Y}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∘ p)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro x
  obtain ⟨u₀, rfl⟩ := hps x
  obtain ⟨s, hs, hsx, hps'⟩ := s22tc_local_section hpc.isLocalHomeomorph hpd u₀
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ((f ∘ p) ∘ s) (p u₀) := by
    refine MDifferentiableAt.comp (p u₀) ?_ hs
    rw [hsx]
    exact hf u₀
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hps'] with y hy
  show f y = f (p (s y))
  rw [hy]

/-- The period group of a plane covering whose deck maps are holomorphic: a discrete `ℤ`-submodule
of `ℂ` whose cosets are the fibres. -/
theorem s22tc_period_group {S : Type u} [TopologicalSpace S] (p : ℂ → S) (hcov : IsCoveringMap p)
    (hdeck : ∀ z w, p z = p w → ∃ F : ℂ ≃ₜ ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ p ∘ F = p ∧ F z = w) :
    ∃ L : Submodule ℤ ℂ, DiscreteTopology L ∧ ∀ z w, p z = p w ↔ z - w ∈ L := by
  classical
  let Λ : AddSubgroup ℂ :=
    { carrier := {b | ∀ z, p (z + b) = p z}
      zero_mem' := fun z => by simp only [add_zero]
      add_mem' := by
        intro b c hb hc z
        rw [← add_assoc, hc (z + b), hb z]
      neg_mem' := by
        intro b hb z
        have := hb (z + -b)
        rw [neg_add_cancel_right] at this
        exact this.symm }
  have hfib : ∀ z w, p z = p w ↔ w - z ∈ Λ := by
    intro z w
    constructor
    · intro hzw
      obtain ⟨F, hF, hpF, hFz⟩ := hdeck z w hzw
      have hfix : ∀ z' : ℂ, F z' = z' → ∀ w' : ℂ, F w' = w' := by
        intro z' hz' w'
        have hcomp : p ∘ (F : ℂ → ℂ) = p ∘ id := hpF
        exact congrFun (hcov.eq_of_comp_eq F.continuous continuous_id hcomp z' hz') w'
      obtain ⟨b, hb⟩ := s22c4_eq_add_of_mdifferentiable F hF hfix
      have hbw : w - z = b := by rw [← hFz, hb z]; ring
      rw [hbw]
      intro z'
      have := congrFun hpF z'
      rw [Function.comp_apply, hb z'] at this
      exact this
    · intro hmem
      have := hmem z
      rw [add_sub_cancel] at this
      exact this.symm
  refine ⟨Λ.toIntSubmodule, ?_, ?_⟩
  · obtain ⟨E, hE0, hpE⟩ := hcov.isLocalHomeomorph 0
    have hnhds : E.source ∈ 𝓝 (0 : ℂ) := E.open_source.mem_nhds hE0
    rw [discreteTopology_iff_isOpen_singleton_zero]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hset : ({0} : Set ↥Λ.toIntSubmodule) =
        Subtype.val ⁻¹' Metric.ball (0 : ℂ) ε := by
      ext ⟨b, hb⟩
      constructor
      · intro h
        have h0 : b = 0 := congrArg Subtype.val h
        show b ∈ Metric.ball (0 : ℂ) ε
        rw [h0]
        exact Metric.mem_ball_self hε
      · intro h
        have hbs : b ∈ E.source := hball h
        have hpb : p b = p 0 := by simpa using (show ∀ z, p (z + b) = p z from hb) 0
        rw [hpE] at hpb
        have : b = 0 := E.injOn hbs hE0 hpb
        exact Subtype.ext this
    rw [hset]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  · intro z w
    rw [hfib z w, ← neg_sub w z]
    exact (AddSubgroup.neg_mem_iff Λ).symm

/-- A discrete `ℤ`-submodule of `ℂ` is `0`, `ℤ o0` or `ℤ o1 + ℤ o2` with `o1, o2` `ℝ`-independent. -/
theorem s22tc_lattice_cases (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    L = ⊥ ∨ (∃ o0 : ℂ, o0 ≠ 0 ∧ L = Submodule.span ℤ {o0}) ∨
      (∃ o1 o2 : ℂ, LinearIndependent ℝ ![o1, o2] ∧ L = Submodule.span ℤ {o1, o2}) := by
  classical
  let b := Module.finBasis ℤ L
  let r := Module.finrank ℤ L
  let v : Fin r → ℂ := fun i => (b i : ℂ)
  have hvL : ∀ i, v i ∈ L := fun i => (b i).2
  have hspan : Submodule.span ℤ (Set.range v) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hvL i
    · intro x hx
      have h1 := b.sum_repr ⟨x, hx⟩
      have h2 : x = ∑ i, b.repr ⟨x, hx⟩ i • v i := by
        have := congrArg Subtype.val h1
        rw [Submodule.coe_sum] at this
        simpa [v] using this.symm
      rw [h2]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrank : Set.finrank ℝ (L : Set ℂ) = r := by
    have hs : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)) := by
      rw [Submodule.span_eq]; infer_instance
    have h1 := Real.finrank_eq_int_finrank_of_discrete hs
    rw [h1]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ (Submodule.span_eq L))
  have hli : LinearIndependent ℝ v := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    have h2 : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (L : Set ℂ) := by
      apply le_antisymm
      · exact Submodule.span_mono (Set.range_subset_iff.mpr hvL)
      · rw [Submodule.span_le]
        intro x hx
        have : x ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; exact hx
        exact (Submodule.span_le_restrictScalars ℤ ℝ _) this
    rw [Set.finrank, h2]
    exact hrank.symm
  have hr2 : r ≤ 2 := by
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Complex.finrank_real_complex] at this
  obtain h | h | h : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · left
    have : IsEmpty (Fin r) := by rw [h]; infer_instance
    rw [← hspan, Set.range_eq_empty, Submodule.span_empty]
  · right; left
    let i0 : Fin r := ⟨0, by omega⟩
    refine ⟨v i0, hli.ne_zero i0, ?_⟩
    rw [← hspan]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have : i = i0 := Fin.ext (by have := i.2; simp only [i0]; omega)
      rw [this]; rfl
    · rintro rfl; exact ⟨i0, rfl⟩
  · right; right
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    refine ⟨v i0, v i1, ?_, ?_⟩
    · have hinj : Function.Injective ![i0, i1] := by
        intro a c hac
        fin_cases a <;> fin_cases c <;> simp_all [i0, i1, Fin.ext_iff]
      have := hli.comp _ hinj
      convert this using 1
      funext a
      fin_cases a <;> rfl
    · rw [← hspan]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        have : i = i0 ∨ i = i1 := by
          have h3 := i.2
          rcases (by omega : i.1 = 0 ∨ i.1 = 1) with h1 | h1
          · left; exact Fin.ext (by simp only [i0]; omega)
          · right; exact Fin.ext (by simp only [i1]; omega)
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨i0, rfl⟩
        · exact ⟨i1, rfl⟩

/-- A map into an open subset of a Riemann surface is holomorphic when its composite with the
inclusion is. -/
theorem s22tc_mdiff_into_opens {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (U : TopologicalSpace.Opens M)
    (f : X → U) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => ((f x : U) : M))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro x
  have hne : Nonempty ↥U := ⟨f x⟩
  let i := U.openPartialHomeomorphSubtypeCoe hne
  have hi := k22u_mdifferentiable_opens_inclusion U hne
  have htg : i.target = (U : Set M) :=
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target U hne
  have hmem : ((f x : U) : M) ∈ i.target := by rw [htg]; exact (f x).2
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => i.symm ((f y : U) : M)) x :=
    ((hi.2 _ hmem).mdifferentiableAt (i.open_target.mem_nhds hmem)).comp x (hf x)
  have h2 : (fun y => i.symm ((f y : U) : M)) = f := by
    funext y
    have hs : i.source = Set.univ :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source U hne
    have hc : i (f y) = ((f y : U) : M) :=
      congrFun (TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe U hne) (f y)
    rw [← hc]
    exact i.left_inv (by rw [hs]; trivial)
  rw [h2] at h1
  exact h1

/-- Plane coverings with holomorphic translation deck maps: the three cases of Theorem 22.3. -/
theorem s22tc_plane_classify {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [IsManifold 𝓘(ℂ) ω S] (p : ℂ → S) (hcov : IsCoveringMap p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hsurj : Function.Surjective p)
    (hdeck : ∀ z w, p z = p w →
      ∃ F : ℂ ≃ₜ ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ p ∘ F = p ∧ F z = w) :
    RSConformallyEquivalent S ℂ ∨ RSConformallyEquivalent S puncturedPlaneOpens ∨
      (∃ (L : PeriodPair) (p : ℂ → S), IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
        Function.Surjective p ∧ ∀ z w, p z = p w ↔ z - w ∈ L.lattice) := by
  classical
  obtain ⟨L, hdisc, hfib⟩ := s22tc_period_group p hcov hdeck
  rcases s22tc_lattice_cases L with hL | ⟨o0, ho, hL⟩ | ⟨o1, o2, hli, hL⟩
  · left
    have hinj : ∀ z w, p z = p w → z = w := by
      intro z w h
      have := (hfib z w).1 h
      rw [hL, Submodule.mem_bot] at this
      exact sub_eq_zero.mp this
    let g : S → ℂ := fun x => Classical.choose (hsurj x)
    have hg : ∀ x, p (g x) = x := fun x => Classical.choose_spec (hsurj x)
    have hgp : ∀ z, g (p z) = z := fun z => hinj _ _ (hg (p z))
    have hgd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
      refine s22tc_descend hcov hhol hsurj (f := g) ?_
      have : g ∘ p = id := funext hgp
      rw [this]
      exact mdifferentiable_id
    exact ⟨g, hgd, p, hhol, hg, hgp⟩
  · right; left
    let c' : ℂ := 2 * π * Complex.I / o0
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc'0 : c' ≠ 0 := div_ne_zero hpi ho
    have hco : c' * o0 = 2 * π * Complex.I := div_mul_cancel₀ _ ho
    let E : ℂ → ℂ := fun z => Complex.exp (c' * z)
    have hEfib : ∀ z w, E z = E w ↔ z - w ∈ L := by
      intro z w
      rw [hL, Submodule.mem_span_singleton]
      simp only [E]
      rw [Complex.exp_eq_exp_iff_exists_int]
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [zsmul_eq_mul]
        have h2 : c' * (z - w) = c' * (n * o0) := by linear_combination hn - (n : ℂ) * hco
        have := mul_left_cancel₀ hc'0 h2
        exact this.symm
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [zsmul_eq_mul] at hn
        linear_combination (-c') * hn + (n : ℂ) * hco
    have hEne : ∀ z, E z ≠ 0 := fun z => Complex.exp_ne_zero _
    let Eq : ℂ → ↥puncturedPlaneOpens := fun z => ⟨E z, hEne z⟩
    have hEd : Differentiable ℂ E := by
      intro z
      exact (Complex.differentiable_exp.comp ((differentiable_const c').mul differentiable_id)) z
    have hEqd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Eq :=
      s22tc_mdiff_into_opens _ _ (mdifferentiable_iff_differentiable.mpr hEd)
    have hEqcov : IsCoveringMap Eq := by
      have h1 := Complex.isCoveringMap_exp.comp_homeomorph (Homeomorph.mulLeft₀ c' hc'0)
      exact h1
    have hEqsurj : Function.Surjective Eq := by
      rintro ⟨w, hw⟩
      have hw0 : w ≠ 0 := hw
      refine ⟨o0 * Complex.log w / (2 * π * Complex.I), ?_⟩
      apply Subtype.ext
      change Complex.exp (c' * (o0 * Complex.log w / (2 * π * Complex.I))) = w
      have : c' * (o0 * Complex.log w / (2 * π * Complex.I)) = Complex.log w := by
        simp only [c']
        field_simp
      rw [this, Complex.exp_log hw0]
    let g : S → ℂ := fun x => Classical.choose (hsurj x)
    have hg : ∀ x, p (g x) = x := fun x => Classical.choose_spec (hsurj x)
    let f : S → ↥puncturedPlaneOpens := fun x => Eq (g x)
    have hfp : ∀ z, f (p z) = Eq z := by
      intro z
      apply Subtype.ext
      exact (hEfib _ _).2 ((hfib _ _).1 (hg (p z)))
    have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
      refine s22tc_descend hcov hhol hsurj (f := f) ?_
      have : f ∘ p = Eq := funext hfp
      rw [this]
      exact hEqd
    let H : ↥puncturedPlaneOpens → S := fun w => p (Classical.choose (hEqsurj w))
    have hHE : ∀ z, H (Eq z) = p z := by
      intro z
      have h1 : Eq (Classical.choose (hEqsurj (Eq z))) = Eq z := Classical.choose_spec (hEqsurj (Eq z))
      have h2 : E (Classical.choose (hEqsurj (Eq z))) = E z := congrArg Subtype.val h1
      exact (hfib _ _).2 ((hEfib _ _).1 h2)
    have hHd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := by
      refine s22tc_descend hEqcov hEqd hEqsurj (f := H) ?_
      have : H ∘ Eq = p := funext hHE
      rw [this]
      exact hhol
    refine ⟨f, hfd, H, hHd, ?_, ?_⟩
    · intro x
      change H (Eq (g x)) = x
      rw [hHE, hg]
    · intro w
      obtain ⟨z, rfl⟩ := hEqsurj w
      rw [hHE, hfp]
  · right; right
    refine ⟨⟨o1, o2, hli⟩, p, hcov, hhol, hsurj, fun z w => ?_⟩
    rw [hfib z w, hL]
    rfl

/-- The plane alternative of the path cover gives a holomorphic covering `ℂ → S` with holomorphic
fibre-transitive deck maps. -/
theorem s22tc_plane_input
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    (hplane : RSConformallyEquivalent (RiemannDynamics.PathCover x₀) ℂ) :
    ∃ p : ℂ → S, IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ Function.Surjective p ∧
      ∀ z w, p z = p w →
        ∃ F : ℂ ≃ₜ ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ p ∘ F = p ∧ F z = w := by
  obtain ⟨f, hf⟩ := hplane
  obtain ⟨e, -⟩ := k22u_biholomorphic_diffeomorph hf
  refine ⟨RiemannDynamics.pathCoverProj x₀ ∘ e.symm, ?_, ?_, ?_, ?_⟩
  · exact (RiemannDynamics.pathCoverProj_isCoveringMap x₀).comp_homeomorph e.symm.toHomeomorph
  · exact (s22c0_pathCoverProj_mdifferentiable x₀).comp
      (e.symm.contMDiff.mdifferentiable (by simp))
  · exact (s22c0_pathCoverProj_surjective x₀).comp e.symm.toEquiv.surjective
  · intro z w hzw
    obtain ⟨γ, hγ⟩ := RiemannDynamics.pathCoverDeck_transitive
      x₀ (e.symm z) (e.symm w) hzw
    obtain ⟨F, hF, hform, hpres, -⟩ := s22ct_pathCover_conjugate_deck
      x₀ e (FundamentalGroup.fromPath γ)
    refine ⟨F, hF, hpres, ?_⟩
    rw [hform, hγ, e.apply_symm_apply]

/-- **Theorem 22.3** (the five types).  Every Riemann surface is conformally equivalent to one of:
(i) `ℂ̄`, (ii) `ℂ`, (iii) `ℂ ∖ {0}`, (iv) a torus `ℂ/(ℤω₁ + ℤω₂)`, (v) `ℍ/Γ` (equivalently
`Δ/Γ`) for a torsion free Fuchsian group `Γ`.  Here (iv) is expressed by a holomorphic covering
`ℂ → S` whose fibres are the cosets of a lattice. -/
theorem thm22_3_classification [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] :
    (CompactSpace S ∧ SimplyConnectedSpace S) ∨ RSConformallyEquivalent S ℂ ∨
      RSConformallyEquivalent S puncturedPlaneOpens ∨
      (∃ (L : PeriodPair) (p : ℂ → S), IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
        Function.Surjective p ∧ ∀ z w, p z = p w ↔ z - w ∈ L.lattice) ∨
      ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
        IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  have : T2Space (RiemannDynamics.PathCover x₀) := RiemannDynamics.t2space_pathCover x₀
  have : SimplyConnectedSpace (RiemannDynamics.PathCover x₀) :=
    RiemannDynamics.simplyConnectedSpace_pathCover x₀
  rcases (thm22_2_uniformization (S := RiemannDynamics.PathCover x₀)).1 with
    hcompact | hplane | hdisc
  · exact Or.inl (s22tc_sphere_case x₀ hcompact.1 hcompact.2)
  · obtain ⟨p, hcov, hhol, hsurj, hdeck⟩ := s22tc_plane_input x₀ hplane
    rcases s22tc_plane_classify p hcov hhol hsurj hdeck with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (s22tc_disc_case x₀ hdisc))))

-- gauss_bonnet_area is stated and proved in LiZhongQC/Lemmas/S22gbFinal.lean
-- (it needs the Chern-Weil machinery and the canonical divisor degree downstream of this file).

/-! ## §22.5 Differentials, divisors and the Riemann–Roch theorem -/

/-- The transition map `φ_x ∘ φ_y⁻¹` between the preferred charts at `y` and `x`. -/
def chartTransition (x y : S) : ℂ → ℂ := fun z => chartAt ℂ x ((chartAt ℂ y).symm z)

/-- A differential form of type `(m, n)` (`φ(z) dz^m dz̄^n`), given by its coefficient `q x` in the
preferred chart at every `x` (vanishing off the chart), subject to the transformation law
`q_y(z) = q_x(τ(z)) τ'(z)^m conj(τ'(z))^n`, `τ = φ_x ∘ φ_y⁻¹`. -/
def IsDiffFamily (m n : ℤ) (q : S → ℂ → ℂ) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → q x z = 0) ∧
    ∀ x y : S, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
      q y z = q x (chartTransition x y z) * deriv (chartTransition x y) z ^ m *
        conj (deriv (chartTransition x y) z) ^ n

/-- The complex vector space of `(m, n)` differentials. -/
def diffFamilySubmodule (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (m n : ℤ) :
    Submodule ℂ (S → ℂ → ℂ) where
  carrier := {q | IsDiffFamily m n q}
  add_mem' := by
    intro q₁ q₂ h₁ h₂
    refine ⟨fun x z hz => ?_, fun x y z hz hs => ?_⟩
    · simp [h₁.1 x z hz, h₂.1 x z hz]
    · simp only [Pi.add_apply]
      rw [h₁.2 x y z hz hs, h₂.2 x y z hz hs]
      ring
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩
  smul_mem' := by
    intro c q h
    refine ⟨fun x z hz => ?_, fun x y z hz hs => ?_⟩
    · simp [h.1 x z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [h.2 x y z hz hs]
      ring

/-- The space `Q(S)` of holomorphic quadratic differentials `φ(z) dz²`. -/
def holQuadDiffSubmodule (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] :
    Submodule ℂ (S → ℂ → ℂ) where
  carrier := {q | IsDiffFamily 2 0 q ∧ ∀ x : S, DifferentiableOn ℂ (q x) (chartAt ℂ x).target}
  add_mem' := by
    intro q₁ q₂ h₁ h₂
    exact ⟨(diffFamilySubmodule S 2 0).add_mem h₁.1 h₂.1, fun x => (h₁.2 x).add (h₂.2 x)⟩
  zero_mem' := ⟨(diffFamilySubmodule S 2 0).zero_mem, fun _ => differentiableOn_const 0⟩
  smul_mem' := by
    intro c q h
    exact ⟨(diffFamilySubmodule S 2 0).smul_mem c h.1, fun x => (h.2 x).const_smul c⟩

/-- A divisor `α = Σ nⱼ pⱼ` on `S`. -/
abbrev Divisor (S : Type u) := S →₀ ℤ

/-- The degree `deg α = Σ nⱼ`. -/
def Divisor.deg (α : Divisor S) : ℤ := α.sum fun _ n => n

/-- The functions which vanish off a discrete closed set (identified with `0` as meromorphic
functions). -/
def codiscreteNull (S : Type u) [TopologicalSpace S] : Submodule ℂ (S → ℂ) where
  carrier := {f | ∀ᶠ x in Filter.codiscrete S, f x = 0}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    filter_upwards [hf, hg] with x h₁ h₂
    simp [h₁, h₂]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Filter.Eventually.of_forall fun _ => rfl
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    filter_upwards [hf] with x h
    simp [h]

/-- The space `D₀[-α] = {f meromorphic : (f) ≥ -α}` (as a space of meromorphic functions, i.e.
modulo functions vanishing off a discrete set). -/
def meroFunctionSpace (α : Divisor S) : Submodule ℂ ((S → ℂ) ⧸ codiscreteNull S) :=
  Submodule.map (codiscreteNull S).mkQ
    (Submodule.span ℂ {f : S → ℂ | IsMeromorphicRS f ∧ ∀ x, ((-α x : ℤ) : WithTop ℤ) ≤ ordRS f x})

/-- `ℓ(α) = dim D₀[-α]`. -/
def ellDim (α : Divisor S) : ℕ := Module.finrank ℂ (meroFunctionSpace α)

/-- `K` is a canonical divisor: the divisor of a meromorphic differential `ω = q dz`, `q ≢ 0`. -/
def IsCanonicalDivisor (K : Divisor S) : Prop :=
  ∃ q : S → ℂ → ℂ, IsDiffFamily 1 0 q ∧ (∀ x, MeromorphicAt (q x) (chartAt ℂ x x)) ∧
    ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q x) (chartAt ℂ x x)

theorem k22rr_divisor_type_eq : Jacobians.Divisor S = Divisor S := rfl

theorem k22rr_degree_eq (D : Divisor S) :
    Jacobians.Divisor.deg S D = Divisor.deg D := rfl

theorem k22rr_meromorphic_iff (f : S → ℂ) :
    Jacobians.IsMeromorphic S f ↔ IsMeromorphicRS f := Iff.rfl

theorem k22rr_order_eq (f : Jacobians.MeromorphicFunction S) (x : S) :
    f.orderW x = ordRS f.toFun x := rfl

theorem k22rr_germZero_iff (f : Jacobians.MeromorphicFunction S) :
    f ∈ Jacobians.germZeroSubmodule ↔ f.toFun ∈ codiscreteNull S := by
  change (∀ x, f.orderW x = ⊤) ↔ ∀ᶠ x in Filter.codiscrete S, f.toFun x = 0
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  exact forall_congr' fun x => Jacobians.MeromorphicFunction.orderW_eq_top_iff f x

theorem k22rr_quotient_equiv (D : Divisor S) :
    Nonempty
      ((↥(Jacobians.linearSystem (X := S) D) ⧸
          (Jacobians.germZeroSubmodule (X := S)).submoduleOf
            (Jacobians.linearSystem (X := S) D))
        ≃ₗ[ℂ] meroFunctionSpace D) := by
  let T : Jacobians.linearSystem (X := S) D →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun f => f.1.toFun
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : (LinearMap.range T : Set (S → ℂ)) =
      {f : S → ℂ | IsMeromorphicRS f ∧
        ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x} := by
    ext f
    constructor
    · intro hf
      obtain ⟨F, hF⟩ := hf
      subst f
      refine ⟨F.1.meromorphic, ?_⟩
      intro x
      exact F.2 x
    · intro hf
      refine ⟨⟨⟨f, hf.1⟩, ?_⟩, rfl⟩
      intro x
      exact hf.2 x
  have hspan : Submodule.span ℂ
      {f : S → ℂ | IsMeromorphicRS f ∧
        ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x} = LinearMap.range T := by
    rw [← hrange]
    exact Submodule.span_eq _
  let F := (codiscreteNull S).mkQ.comp T
  have hker : LinearMap.ker F =
      (Jacobians.germZeroSubmodule (X := S)).submoduleOf
        (Jacobians.linearSystem (X := S) D) := by
    ext f
    change (codiscreteNull S).mkQ f.1.toFun = 0 ↔
      f.1 ∈ Jacobians.germZeroSubmodule
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (k22rr_germZero_iff f.1).symm
  have hFR : LinearMap.range F = meroFunctionSpace D := by
    change LinearMap.range ((codiscreteNull S).mkQ.comp T) =
      Submodule.map (codiscreteNull S).mkQ
        (Submodule.span ℂ {f : S → ℂ | IsMeromorphicRS f ∧
          ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x})
    rw [hspan, LinearMap.range_comp]
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hFR))⟩

/-- Reviewed Q2 interface stub `k22q_quotient_equiv_mkQ`; proof awaits separate GO. -/
theorem k22q_quotient_equiv_mkQ (D : Divisor S) :
    ∃ e :
      (↥(Jacobians.linearSystem (X := S) D) ⧸
          (Jacobians.germZeroSubmodule (X := S)).submoduleOf
            (Jacobians.linearSystem (X := S) D))
        ≃ₗ[ℂ] meroFunctionSpace D,
      ∀ f : Jacobians.linearSystem (X := S) D,
        (e (((Jacobians.germZeroSubmodule (X := S)).submoduleOf
              (Jacobians.linearSystem (X := S) D)).mkQ f) :
            (S → ℂ) ⧸ codiscreteNull S) =
          (codiscreteNull S).mkQ f.1.toFun := by
  let T : Jacobians.linearSystem (X := S) D →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun f => f.1.toFun
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : (LinearMap.range T : Set (S → ℂ)) =
      {f : S → ℂ | IsMeromorphicRS f ∧
        ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x} := by
    ext f
    constructor
    · intro hf
      obtain ⟨F, hF⟩ := hf
      subst f
      refine ⟨F.1.meromorphic, ?_⟩
      intro x
      exact F.2 x
    · intro hf
      refine ⟨⟨⟨f, hf.1⟩, ?_⟩, rfl⟩
      intro x
      exact hf.2 x
  have hspan : Submodule.span ℂ
      {f : S → ℂ | IsMeromorphicRS f ∧
        ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x} = LinearMap.range T := by
    rw [← hrange]
    exact Submodule.span_eq _
  let F := (codiscreteNull S).mkQ.comp T
  have hker : LinearMap.ker F =
      (Jacobians.germZeroSubmodule (X := S)).submoduleOf
        (Jacobians.linearSystem (X := S) D) := by
    ext f
    change (codiscreteNull S).mkQ f.1.toFun = 0 ↔
      f.1 ∈ Jacobians.germZeroSubmodule
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (k22rr_germZero_iff f.1).symm
  have hFR : LinearMap.range F = meroFunctionSpace D := by
    change LinearMap.range ((codiscreteNull S).mkQ.comp T) =
      Submodule.map (codiscreteNull S).mkQ
        (Submodule.span ℂ {f : S → ℂ | IsMeromorphicRS f ∧
          ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ ordRS f x})
    rw [hspan, LinearMap.range_comp]
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hFR))
  refine ⟨e, ?_⟩
  intro f
  simpa only [e, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearEquiv.coe_ofEq_apply,
    LinearMap.quotKerEquivRange_apply_mk] using
    (show F f = (codiscreteNull S).mkQ f.1.toFun from rfl)

theorem k22rr_ellDim_eq_lDim (D : Divisor S) :
    ellDim D = Jacobians.lDim (X := S) D := by
  obtain ⟨e⟩ := k22rr_quotient_equiv D
  exact e.finrank_eq.symm

section k22rr_canonical_context
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]

theorem k22rr_coeff_section (q : S → ℂ → ℂ) (hq : IsDiffFamily 1 0 q) :
    ∃ σ : ∀ x, Jacobians.Dolbeault.FormFiber S x,
      ∀ x z, z ∈ (chartAt ℂ x).target →
        Jacobians.Dolbeault.formCoeff σ x z = q x z := by
  let σ : ∀ p, Jacobians.Dolbeault.FormFiber S p := fun p =>
    q p (chartAt ℂ p p) •
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) p).continuousLinearMapAt ℂ p
  refine ⟨σ, ?_⟩
  intro x z hz
  let p := (chartAt ℂ x).symm z
  have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcz : chartAt ℂ x p = z := (chartAt ℂ x).right_inv hz
  have hframe := Jacobians.Dolbeault.symmL_frame_change hp (mem_chart_source ℂ p)
  rw [hcz] at hframe
  change q p (chartAt ℂ p p) •
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) p).continuousLinearMapAt ℂ p
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) x).symmL ℂ p 1) = q x z
  rw [hframe, ContinuousLinearMap.map_smul,
    Bundle.Trivialization.continuousLinearMapAt_symmL]
  · simp only [smul_eq_mul, mul_one]
    have hqz := hq.2 p x z hz (mem_chart_source ℂ p)
    change q x z = q p (chartAt ℂ p p) *
      deriv (chartAt ℂ p ∘ (chartAt ℂ x).symm) z ^ 1 *
      (starRingEnd ℂ) (deriv (chartAt ℂ p ∘ (chartAt ℂ x).symm) z) ^ 0 at hqz
    simpa only [zpow_one, zpow_zero, mul_one] using hqz.symm
  · exact mem_baseSet_trivializationAt ℂ _ p

theorem k22rr_canonical_data {K : Divisor S} (hK : IsCanonicalDivisor K) :
    ∃ data : Jacobians.Dolbeault.CanonicalForm17Data S, data.K = K := by
  obtain ⟨q, hfamily, hmer, horder⟩ := hK
  obtain ⟨σ, hσ⟩ := k22rr_coeff_section q hfamily
  have hcoeff : ∀ x, Jacobians.Dolbeault.formCoeff σ x =ᶠ[
      𝓝[≠] (chartAt ℂ x x)] q x := by
    intro x
    have ht : (chartAt ℂ x).target ∈ 𝓝 (chartAt ℂ x x) :=
      (chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds ht] with z hz
    exact hσ x z hz
  let ω₀ : Jacobians.Dolbeault.MeromorphicOneForm S :=
    { toFun := σ
      meromorphic := fun x => (hmer x).congr (hcoeff x).symm }
  have hωorder : ∀ x, ω₀.formOrderW x = (K x : WithTop ℤ) := by
    intro x
    change meromorphicOrderAt (Jacobians.Dolbeault.formCoeff σ x)
      (chartAt ℂ x x) = (K x : WithTop ℤ)
    rw [meromorphicOrderAt_congr (hcoeff x)]
    exact (horder x).symm
  refine ⟨{ ω₀ := ω₀, nontrivial := ?_, K := K, order_eq := hωorder }, rfl⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  refine ⟨x, ?_⟩
  rw [hωorder]
  exact WithTop.coe_ne_top

theorem k22rr_canonical_data_dimension
    (data : Jacobians.Dolbeault.CanonicalForm17Data S) (D : Divisor S) :
    Jacobians.lDim (X := S) (data.K - D) =
      Jacobians.Dolbeault.omegaDim (X := S) (-D) := by
  have h := data.lDim_add_K_eq_omegaDim (-D)
  rw [add_comm (-D) data.K] at h
  exact h

theorem k22rr_canonical_data_transport
    (data₁ data₂ : Jacobians.Dolbeault.CanonicalForm17Data S) (D : Divisor S) :
    Jacobians.lDim (X := S) (data₁.K - D) =
      Jacobians.lDim (X := S) (data₂.K - D) :=
  (k22rr_canonical_data_dimension data₁ D).trans
    (k22rr_canonical_data_dimension data₂ D).symm

theorem k22rr_canonical_transport {K : Divisor S} (hK : IsCanonicalDivisor K)
    (f : Jacobians.MeromorphicFunction S) (hf : ¬ Jacobians.Dolbeault.IsGermConstant f)
    (D : Divisor S) :
    Jacobians.lDim (X := S) (K - D) =
      Jacobians.lDim (X := S) (Jacobians.LaurentTail.pairCanonicalDivisor f hf - D) := by
  obtain ⟨data, hdata⟩ := k22rr_canonical_data hK
  let pairData := Jacobians.Dolbeault.canonicalForm17DataOfDivisor f hf
    (Jacobians.LaurentTail.pairCanonicalDivisor f hf)
    (Jacobians.LaurentTail.formOrderW_pairCanonicalDivisor f hf)
  have h := k22rr_canonical_data_transport data pairData D
  change Jacobians.lDim (X := S) (data.K - D) =
    Jacobians.lDim (X := S) (Jacobians.LaurentTail.pairCanonicalDivisor f hf - D) at h
  rwa [hdata] at h

theorem k22rr_riemann_roch_analytic {K : Divisor S} (hK : IsCanonicalDivisor K)
    (D : Divisor S) :
    (ellDim D : ℤ) - ellDim (K - D) = D.deg - genus S + 1 := by
  obtain ⟨_A, f, _hfmem, hf⟩ := Jacobians.Dolbeault.exists_nonconstant_meromorphic (X := S)
  have hRR := Jacobians.LaurentTail.riemannRoch_tailForm (X := S) D
  rw [Jacobians.LaurentTail.h1TailDim_eq_lDim_pairCanonical_sub f hf D,
    Jacobians.LaurentTail.h1TailDim_zero_eq_genus_unconditional] at hRR
  rw [← k22rr_canonical_transport hK f hf D, k22rr_degree_eq D] at hRR
  rw [k22rr_ellDim_eq_lDim D, k22rr_ellDim_eq_lDim (K - D)]
  omega

end k22rr_canonical_context


/-- §22.5: `deg (ω) = 2g - 2` for a meromorphic differential and `deg (f) = 0` for a meromorphic
function on a closed surface of genus `g`. -/
theorem deg_canonical [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hS : HasGenus S g) {K : Divisor S} (hK : IsCanonicalDivisor K) : K.deg = 2 * (g : ℤ) - 2 := by
  letI : CompactSpace S := hS.1
  have h0 := k22rr_riemann_roch_analytic hK (0 : Divisor S)
  have hK' := k22rr_riemann_roch_analytic hK K
  rw [sub_zero, ← k22rr_degree_eq (0 : Divisor S),
    Jacobians.Divisor.deg_zero, k22rr_genus_eq hS] at h0
  rw [sub_self, k22rr_genus_eq hS] at hK'
  omega

/-- **Theorem 22.4** (Riemann–Roch).  On a closed Riemann surface of genus `g`,
`ℓ(α) - ℓ(K - α) = deg α - g + 1`.  Since `D[α] = {ω : (ω) ≥ α}` is isomorphic to `D₀[α - K]`,
this is the book's formula `dim D[α] = dim D₀[-α] - deg α + g - 1`. -/
theorem thm22_4_riemann_roch [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hS : HasGenus S g) {K : Divisor S} (hK : IsCanonicalDivisor K) (α : Divisor S) :
    (ellDim α : ℤ) - ellDim (K - α) = α.deg - g + 1 := by
  letI : CompactSpace S := hS.1
  have h := k22rr_riemann_roch_analytic hK α
  rw [k22rr_genus_eq hS] at h
  exact h

section k22q_context
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]

/-- Reviewed Q2 interface stub `k22q_canonical_chart_coefficients`; proof awaits separate GO. -/
theorem k22q_canonical_chart_coefficients
    (data : Jacobians.Dolbeault.CanonicalForm17Data S) :
    ∃ q₀ : S → ℂ → ℂ,
      IsDiffFamily 1 0 q₀ ∧
      (∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x)) ∧
      ∀ x, (data.K x : WithTop ℤ) =
        meromorphicOrderAt (q₀ x) (chartAt ℂ x x) := by
  classical
  let q₀ : S → ℂ → ℂ := fun x =>
    (chartAt ℂ x).target.indicator (Jacobians.Dolbeault.formCoeff data.ω₀.toFun x)
  have heq (x : S) : q₀ x =ᶠ[𝓝 (chartAt ℂ x x)]
      Jacobians.Dolbeault.formCoeff data.ω₀.toFun x := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz
    exact Set.indicator_of_mem hz _
  refine ⟨q₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x z hz
    exact Set.indicator_of_notMem hz _
  · intro x y z hz hs
    let p := (chartAt ℂ y).symm z
    have hyS : p ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hz
    have hxT : chartTransition x y z ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source hs
    have hyBack : chartAt ℂ y p = z := (chartAt ℂ y).right_inv hz
    have hxBack : (chartAt ℂ x).symm (chartTransition x y z) = p :=
      (chartAt ℂ x).left_inv hs
    have hframe := Jacobians.Dolbeault.symmL_frame_change
      (x := y) (y := x) (q := p) hyS hs
    rw [hyBack] at hframe
    change (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) y).symmL ℂ p 1 =
      deriv (chartTransition x y) z •
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) x).symmL ℂ p 1 at hframe
    simp only [q₀, Set.indicator_of_mem hz, Set.indicator_of_mem hxT,
      zpow_one, zpow_zero, mul_one]
    change data.ω₀.toFun p
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) y).symmL ℂ p 1) =
      data.ω₀.toFun ((chartAt ℂ x).symm (chartTransition x y z))
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := S)) x).symmL ℂ
          ((chartAt ℂ x).symm (chartTransition x y z)) 1) * deriv (chartTransition x y) z
    rw [hxBack, hframe, map_smul, smul_eq_mul, mul_comm]
  · intro x
    exact (data.ω₀.meromorphic x).congr
      ((heq x).filter_mono nhdsWithin_le_nhds).symm
  · intro x
    calc
      (data.K x : WithTop ℤ) =
          meromorphicOrderAt (Jacobians.Dolbeault.formCoeff data.ω₀.toFun x)
            (chartAt ℂ x x) := (data.order_eq x).symm
      _ = meromorphicOrderAt (q₀ x) (chartAt ℂ x x) :=
        (meromorphicOrderAt_congr ((heq x).filter_mono nhdsWithin_le_nhds)).symm

/-- Reviewed Q2 interface stub `k22q_canonical_exists`; proof awaits separate GO. -/
theorem k22q_canonical_exists :
    ∃ K : Divisor S, IsCanonicalDivisor K := by
  obtain ⟨f, hf⟩ := Jacobians.Dolbeault.exists_nonconstant_meromorphicFunction (X := S)
  let K := Jacobians.LaurentTail.pairCanonicalDivisor f hf
  let data := Jacobians.Dolbeault.canonicalForm17DataOfDivisor f hf K
    (Jacobians.LaurentTail.formOrderW_pairCanonicalDivisor f hf)
  refine ⟨data.K, ?_⟩
  exact k22q_canonical_chart_coefficients data

/-- Reviewed Q2 interface stub `k22q_scalar_chart_pullback`; proof awaits separate GO. -/
theorem k22q_scalar_chart_pullback
    (f : Jacobians.MeromorphicFunction S) (x y : S)
    (hy : y ∈ (chartAt ℂ x).source) :
    MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) ∧
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
        (chartAt ℂ x y) = f.orderW y := by
  let ψ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm
  have hψ_an : AnalyticAt ℂ ψ (chartAt ℂ x y) :=
    Jacobians.Dolbeault.transition_analyticAt_of_mem hy (mem_chart_source ℂ y)
  have hψ_ne : deriv ψ (chartAt ℂ x y) ≠ 0 :=
    Jacobians.Dolbeault.transition_deriv_ne_zero hy (mem_chart_source ℂ y)
  have hψ_val : ψ (chartAt ℂ x y) = chartAt ℂ y y := by
    show (chartAt ℂ y) ((chartAt ℂ x).symm (chartAt ℂ x y)) = _
    rw [(chartAt ℂ x).left_inv hy]
  have hpre : ∀ᶠ w in 𝓝 (chartAt ℂ x y),
      (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source := by
    have hcont := (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hy)
    apply hcont.preimage_mem_nhds
    rw [(chartAt ℂ x).left_inv hy]
    exact (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
  have heq : (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x y)]
      (f.toFun ∘ (chartAt ℂ y).symm) ∘ ψ := by
    filter_upwards [hpre] with w hw
    show f.toFun ((chartAt ℂ x).symm w) =
      f.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ x).symm w)))
    rw [(chartAt ℂ y).left_inv hw]
  have hown : MeromorphicAt (f.toFun ∘ (chartAt ℂ y).symm)
      (ψ (chartAt ℂ x y)) := by
    rw [hψ_val]
    exact f.meromorphic y
  have hcomp := hown.comp_analyticAt hψ_an
  refine ⟨hcomp.congr (heq.filter_mono nhdsWithin_le_nhds).symm, ?_⟩
  -- Work with the full order, including the zero germ's value `⊤`.
  change meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) =
    meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_comp_of_deriv_ne_zero hψ_an hψ_ne, hψ_val]

/-- Reviewed Q2 interface stub `k22q_square_product_order`; proof awaits separate GO. -/
theorem k22q_square_product_order {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (f : Jacobians.MeromorphicFunction S)
    (hf : f ∈ Jacobians.linearSystem (X := S) (2 • K)) :
    ∀ x z, z ∈ (chartAt ℂ x).target →
      MeromorphicAt
        (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z ∧
      0 ≤ meromorphicOrderAt
        (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z := by
  -- Construct a form from this given coefficient family, not an arbitrary canonical form.
  obtain ⟨σ, hσ⟩ := k22rr_coeff_section q₀ hfamily
  have hcoeff : ∀ x z, z ∈ (chartAt ℂ x).target →
      Jacobians.Dolbeault.formCoeff σ x =ᶠ[𝓝 z] q₀ x := by
    intro x z hz
    have ht := (chartAt ℂ x).open_target.mem_nhds hz
    filter_upwards [ht] with w hw
    exact hσ x w hw
  let α : Jacobians.Dolbeault.MeromorphicOneForm S :=
    { toFun := σ
      meromorphic := by
        intro x
        have hx : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
          (chartAt ℂ x).map_source (mem_chart_source ℂ x)
        exact (hmero x).congr
          ((hcoeff x (chartAt ℂ x x) hx).filter_mono nhdsWithin_le_nhds).symm }
  have hαorder : ∀ x, α.formOrderW x = (K x : WithTop ℤ) := by
    intro x
    change meromorphicOrderAt (Jacobians.Dolbeault.formCoeff σ x)
      (chartAt ℂ x x) = (K x : WithTop ℤ)
    have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    rw [meromorphicOrderAt_congr
      ((hcoeff x (chartAt ℂ x x) hx).filter_mono nhdsWithin_le_nhds)]
    exact (horder x).symm
  intro x z hz
  let y : S := (chartAt ℂ x).symm z
  have hy : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcz : chartAt ℂ x y = z := (chartAt ℂ x).right_inv hz
  have hscalar := k22q_scalar_chart_pullback f x y hy
  rw [hcz] at hscalar
  obtain ⟨hfm, hfo⟩ := hscalar
  let ψ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm
  have hψ_an : AnalyticAt ℂ ψ z := by
    have h : AnalyticAt ℂ ψ (chartAt ℂ x y) :=
      Jacobians.Dolbeault.transition_analyticAt_of_mem hy (mem_chart_source ℂ y)
    rwa [hcz] at h
  have hψ_val : ψ z = chartAt ℂ y y := rfl
  have hown : MeromorphicAt (Jacobians.Dolbeault.formCoeff α.toFun y) (ψ z) := by
    rw [hψ_val]
    exact α.meromorphic y
  have hcomp := hown.comp_analyticAt hψ_an
  have hchange : Jacobians.Dolbeault.formCoeff α.toFun x =ᶠ[𝓝 z]
      (fun w => deriv ψ w • Jacobians.Dolbeault.formCoeff α.toFun y (ψ w)) := by
    simpa only [hcz] using Jacobians.Dolbeault.formCoeff_change α x y hy
  have hαmero : MeromorphicAt (Jacobians.Dolbeault.formCoeff α.toFun x) z := by
    have hprod : MeromorphicAt
        ((fun w => deriv ψ w) • (Jacobians.Dolbeault.formCoeff α.toFun y ∘ ψ)) z :=
      hψ_an.deriv.meromorphicAt.smul hcomp
    exact hprod.congr (hchange.filter_mono nhdsWithin_le_nhds).symm
  have hqm : MeromorphicAt (q₀ x) z :=
    hαmero.congr ((hcoeff x z hz).filter_mono nhdsWithin_le_nhds)
  have hqo : meromorphicOrderAt (q₀ x) z = (K y : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr ((hcoeff x z hz).filter_mono nhdsWithin_le_nhds)]
    calc
      meromorphicOrderAt (Jacobians.Dolbeault.formCoeff σ x) z = α.formOrderW y := by
        have h := Jacobians.Dolbeault.formOrderW_chart_invariant α x y hy
        rw [hcz] at h
        exact h.symm
      _ = (K y : WithTop ℤ) := hαorder y
  have hraw : (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) =
      (f.toFun ∘ (chartAt ℂ x).symm) * ((q₀ x) * (q₀ x)) := by
    funext w
    show f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2 =
      f.toFun ((chartAt ℂ x).symm w) * (q₀ x w * q₀ x w)
    rw [pow_two]
  have hraworder : meromorphicOrderAt
      (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z =
      f.orderW y + ((K y : WithTop ℤ) + (K y : WithTop ℤ)) := by
    rw [hraw, meromorphicOrderAt_mul hfm (hqm.mul hqm),
      meromorphicOrderAt_mul hqm hqm, hfo, hqo]
  refine ⟨?_, ?_⟩
  · rw [hraw]
    exact hfm.mul (hqm.mul hqm)
  · rw [hraworder]
    have hfy : ((-((2 • K) y) : ℤ) : WithTop ℤ) ≤ f.orderW y := by
      change ∀ t, ((-((2 • K) t) : ℤ) : WithTop ℤ) ≤ f.orderW t at hf
      exact hf y
    have hbound : ((-(K y + K y) : ℤ) : WithTop ℤ) ≤ f.orderW y := by
      simpa only [Finsupp.smul_apply, two_smul, Finsupp.add_apply] using hfy
    have hcancel : ((-(K y + K y) : ℤ) : WithTop ℤ) +
        ((K y : WithTop ℤ) + (K y : WithTop ℤ)) = 0 := by
      rw [← WithTop.coe_add (K y) (K y),
        ← WithTop.coe_add (-(K y + K y)) (K y + K y)]
      simp only [neg_add_cancel, WithTop.coe_zero]
    -- Adding finite coefficient orders also covers `f.orderW y = ⊤`.
    calc
      0 = ((-(K y + K y) : ℤ) : WithTop ℤ) +
          ((K y : WithTop ℤ) + (K y : WithTop ℤ)) := hcancel.symm
      _ ≤ f.orderW y + ((K y : WithTop ℤ) + (K y : WithTop ℤ)) :=
        add_le_add_left hbound _

/- Insert this block in the existing k22q_context, immediately before the frozen
   k22q_regularize_square docstring. No imports or section/namespace changes. -/

/-- Full-target meromorphic/nonnegative-order input gives an analytic indicator repair,
    with the original punctured germs and literal zero outside the target. -/
theorem k22q_c_indicator_normal_form (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : MeromorphicOn f U) (ho : ∀ z ∈ U, 0 ≤ meromorphicOrderAt f z) :
    AnalyticOnNhd ℂ (U.indicator (toMeromorphicNFOn f U)) U ∧
      (∀ z ∈ U, U.indicator (toMeromorphicNFOn f U) =ᶠ[𝓝[≠] z] f) ∧
      ∀ z, z ∉ U → U.indicator (toMeromorphicNFOn f U) z = 0 := by
  have he : ∀ z ∈ U, U.indicator (toMeromorphicNFOn f U) =ᶠ[𝓝 z]
      toMeromorphicNFOn f U := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with w hw
    exact Set.indicator_of_mem hw _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hNF : MeromorphicNFAt (toMeromorphicNFOn f U) z :=
      (meromorphicNFOn_toMeromorphicNFOn f U) hz
    have hnonneg : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) z := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hf hz]
      exact ho z hz
    exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 hnonneg).congr (he z hz).symm
  · intro z hz
    exact ((he z hz).filter_mono nhdsWithin_le_nhds).trans
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz)
  · intro z hz
    exact Set.indicator_of_notMem hz _

/-- Holomorphic quadratic families are determined by their own-chart punctured germs. -/
theorem k22q_c_quadratic_ext (v w : holQuadDiffSubmodule S)
    (h : ∀ p, (v : S → ℂ → ℂ) p =ᶠ[𝓝[≠] (chartAt ℂ p p)]
      (w : S → ℂ → ℂ) p) : v = w := by
  apply Subtype.ext
  funext x z
  change (v : S → ℂ → ℂ) x z = (w : S → ℂ → ℂ) x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · let p : S := (chartAt ℂ x).symm z
    let c : ℂ := chartAt ℂ p p
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hc : c ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hps : (chartAt ℂ p).symm c ∈ (chartAt ℂ x).source := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact hp
    have ht : chartTransition x p c = z := by
      change (chartAt ℂ x) ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ x).right_inv hz
    have hv := v.property.1.2 x p c hc hps
    have hw := w.property.1.2 x p c hc hps
    simp only [ht, zpow_ofNat, pow_zero, mul_one] at hv hw
    have hd : deriv (chartTransition x p) c ≠ 0 :=
      Jacobians.Dolbeault.transition_deriv_ne_zero (y := p) (z := x) (x := p)
        (mem_chart_source ℂ p) hp
    have hcenter : (v : S → ℂ → ℂ) p c = (w : S → ℂ → ℂ) p c :=
      tendsto_nhds_unique_of_eventuallyEq
        (((v.property.2 p).differentiableAt
          ((chartAt ℂ p).open_target.mem_nhds hc)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds)
        (((w.property.2 p).differentiableAt
          ((chartAt ℂ p).open_target.mem_nhds hc)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds) (h p)
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    exact hv.symm.trans (hcenter.trans hw)
  · rw [v.property.1.1 x z hz, w.property.1.1 x z hz]

/-- Reviewed Q2 interface stub `k22q_regularize_square`; proof awaits separate GO. -/
theorem k22q_regularize_square {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (f : Jacobians.MeromorphicFunction S)
    (hf : f ∈ Jacobians.linearSystem (X := S) (2 • K)) :
    ∃! v : holQuadDiffSubmodule S,
      ∀ x, (v : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
        (fun z => f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  classical
  let raw : S → ℂ → ℂ := fun x z =>
    f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2
  let q : S → ℂ → ℂ := fun x => (chartAt ℂ x).target.indicator
    (toMeromorphicNFOn (raw x) (chartAt ℂ x).target)
  have hmer : ∀ x, MeromorphicOn (raw x) (chartAt ℂ x).target := by
    intro x z hz
    exact (k22q_square_product_order q₀ hfamily hmero horder f hf x z hz).1
  have hord : ∀ x z, z ∈ (chartAt ℂ x).target →
      0 ≤ meromorphicOrderAt (raw x) z := by
    intro x z hz
    exact (k22q_square_product_order q₀ hfamily hmero horder f hf x z hz).2
  have hrepair : ∀ x,
      AnalyticOnNhd ℂ (q x) (chartAt ℂ x).target ∧
        (∀ z ∈ (chartAt ℂ x).target, q x =ᶠ[𝓝[≠] z] raw x) ∧
        ∀ z, z ∉ (chartAt ℂ x).target → q x z = 0 := by
    intro x
    exact k22q_c_indicator_normal_form (raw x) (chartAt ℂ x).target
      (chartAt ℂ x).open_target (hmer x) (hord x)
  have hq : q ∈ holQuadDiffSubmodule S := by
    change IsDiffFamily 2 0 q ∧
      ∀ x, DifferentiableOn ℂ (q x) (chartAt ℂ x).target
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x z hz
      exact (hrepair x).2.2 z hz
    · intro x y z hz hx
      have hxt : chartTransition x y z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source hx
      have ha : AnalyticAt ℂ (chartTransition x y) z := by
        change AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) z
        simpa only [(chartAt ℂ y).right_inv hz] using
          (Jacobians.Dolbeault.transition_analyticAt_of_mem
            (y := y) (z := x) (x := (chartAt ℂ y).symm z)
            ((chartAt ℂ y).map_target hz) hx)
      have ht : Tendsto (chartTransition x y) (𝓝[≠] z)
          (𝓝[≠] (chartTransition x y z)) :=
        ((chartAt ℂ x).tendsto_nhdsNE hx).comp
          ((chartAt ℂ y).symm.tendsto_nhdsNE hz)
      have hpre : ∀ᶠ u in 𝓝 z,
          (chartAt ℂ y).symm u ∈ (chartAt ℂ x).source :=
        ((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
          ((chartAt ℂ x).open_source.mem_nhds hx)
      have he : q y =ᶠ[𝓝[≠] z]
          (fun u => q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2) := by
        filter_upwards [(hrepair y).2.1 z hz,
          ht.eventually ((hrepair x).2.1 (chartTransition x y z) hxt),
          nhdsWithin_le_nhds ((chartAt ℂ y).open_target.mem_nhds hz),
          nhdsWithin_le_nhds hpre] with u huy hux hut hus
        have hcoeff := hfamily.2 x y u hut hus
        simp only [zpow_one, zpow_zero, mul_one] at hcoeff
        have hscalar : f.toFun ((chartAt ℂ y).symm u) =
            f.toFun ((chartAt ℂ x).symm (chartTransition x y u)) := by
          change f.toFun ((chartAt ℂ y).symm u) =
            f.toFun ((chartAt ℂ x).symm ((chartAt ℂ x) ((chartAt ℂ y).symm u)))
          rw [(chartAt ℂ x).left_inv hus]
        calc
          q y u = raw y u := huy
          _ = raw x (chartTransition x y u) * (deriv (chartTransition x y) u)^2 := by
            change f.toFun ((chartAt ℂ y).symm u) * (q₀ y u)^2 =
              f.toFun ((chartAt ℂ x).symm (chartTransition x y u)) *
                (q₀ x (chartTransition x y u))^2 * (deriv (chartTransition x y) u)^2
            rw [hscalar, hcoeff]
            ring
          _ = q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2 := by
            rw [hux]
      have hl : Tendsto (q y) (𝓝[≠] z) (𝓝 (q y z)) :=
        ((hrepair y).1 z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hr : Tendsto
          (fun u => q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2)
          (𝓝[≠] z)
          (𝓝 (q x (chartTransition x y z) * (deriv (chartTransition x y) z)^2)) :=
        ((((hrepair x).1 (chartTransition x y z) hxt).continuousAt.comp
          ha.continuousAt).mul (ha.deriv.continuousAt.pow 2)).tendsto.mono_left
            nhdsWithin_le_nhds
      have hexact := tendsto_nhds_unique_of_eventuallyEq hl hr he
      simpa only [zpow_ofNat, pow_zero, mul_one] using hexact
    · intro x z hz
      exact ((hrepair x).1 z hz).differentiableAt.differentiableWithinAt
  let v : holQuadDiffSubmodule S := ⟨q, hq⟩
  have hv : ∀ x, (v : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)] raw x := by
    intro x
    exact (hrepair x).2.1 _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  refine ⟨v, hv, ?_⟩
  intro w hw
  apply k22q_c_quadratic_ext w v
  intro x
  exact (hw x).trans (hv x).symm

/-- Reviewed Q2 interface stub `k22q_division_representative`; proof awaits separate GO. -/
theorem k22q_division_representative {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (v : holQuadDiffSubmodule S) :
    ∃ f : Jacobians.MeromorphicFunction S,
      f ∈ Jacobians.linearSystem (X := S) (2 • K) ∧
      ∀ x z, z ∈ (chartAt ℂ x).target →
        f.toFun ((chartAt ℂ x).symm z) =
          (v : S → ℂ → ℂ) x z / (q₀ x z)^2 := by
  classical
  let g : S → ℂ := fun p =>
    (v : S → ℂ → ℂ) p (chartAt ℂ p p) / (q₀ p (chartAt ℂ p p))^2
  have hrep : ∀ x z, z ∈ (chartAt ℂ x).target →
      g ((chartAt ℂ x).symm z) = (v : S → ℂ → ℂ) x z / (q₀ x z)^2 := by
    intro x z hz
    let p : S := (chartAt ℂ x).symm z
    let c : ℂ := chartAt ℂ p p
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hc : c ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hps : (chartAt ℂ p).symm c ∈ (chartAt ℂ x).source := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact hp
    have ht : chartTransition x p c = z := by
      change (chartAt ℂ x) ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ x).right_inv hz
    have hv := v.property.1.2 x p c hc hps
    have hq := hfamily.2 x p c hc hps
    have hd : deriv (chartTransition x p) c ≠ 0 :=
      Jacobians.Dolbeault.transition_deriv_ne_zero (y := p) (z := x) (x := p)
        (mem_chart_source ℂ p) hp
    simp only [ht, zpow_ofNat, pow_zero, mul_one] at hv
    simp only [ht, zpow_one, zpow_zero, mul_one] at hq
    change (v : S → ℂ → ℂ) p c / (q₀ p c)^2 =
      (v : S → ℂ → ℂ) x z / (q₀ x z)^2
    rw [hv, hq, mul_pow]
    exact mul_div_mul_right ((v : S → ℂ → ℂ) x z) ((q₀ x z)^2)
      (pow_ne_zero 2 hd)
  have he : ∀ x, (g ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (fun z => (v : S → ℂ → ℂ) x z / (q₀ x z)^2) := by
    intro x
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz
    exact hrep x z hz
  have hvana : ∀ x, AnalyticAt ℂ ((v : S → ℂ → ℂ) x) (chartAt ℂ x x) := by
    intro x
    exact (v.property.2 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have hg : Jacobians.IsMeromorphic S g := by
    intro x
    exact ((hvana x).meromorphicAt.div ((hmero x).pow 2)).congr
      ((he x).filter_mono nhdsWithin_le_nhds).symm
  let f : Jacobians.MeromorphicFunction S := ⟨g, hg⟩
  refine ⟨f, ?_, hrep⟩
  intro x
  change (((-((2 • K) x) : ℤ) : WithTop ℤ)) ≤
    meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
  rw [meromorphicOrderAt_congr ((he x).filter_mono nhdsWithin_le_nhds)]
  change (((-((2 • K) x) : ℤ) : WithTop ℤ)) ≤
    meromorphicOrderAt ((v : S → ℂ → ℂ) x / (q₀ x)^2) (chartAt ℂ x x)
  rw [meromorphicOrderAt_div (hvana x).meromorphicAt ((hmero x).pow 2)]
  have hden : meromorphicOrderAt ((q₀ x)^2) (chartAt ℂ x x) =
      (((2 • K) x : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow (hmero x), ← horder x]
    norm_cast <;> simp only [two_smul, Finsupp.add_apply, two_mul]
  rw [hden, sub_eq_add_neg]
  simpa only [zero_add, WithTop.LinearOrderedAddCommGroup.coe_neg] using
    add_le_add_left (hvana x).meromorphicOrderAt_nonneg
      (-(((2 • K) x : ℤ) : WithTop ℤ))

/-- Reviewed Q2 interface stub `k22q_regularize_linearMap`; proof awaits separate GO. -/
theorem k22q_regularize_linearMap {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x)) :
    ∃ F : Jacobians.linearSystem (X := S) (2 • K) →ₗ[ℂ]
        holQuadDiffSubmodule S,
      ∀ f x, (F f : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
        (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  classical
  have hreg := fun (f : Jacobians.linearSystem (X := S) (2 • K)) =>
    k22q_regularize_square q₀ hfamily hmero horder f.1 f.2
  let A : Jacobians.linearSystem (X := S) (2 • K) → holQuadDiffSubmodule S :=
    fun f => Classical.choose (hreg f).exists
  have hA : ∀ f x, (A f : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) :=
    fun f => Classical.choose_spec (hreg f).exists
  -- The repaired coefficients are linear by uniqueness of the holomorphic repair.
  let F : Jacobians.linearSystem (X := S) (2 • K) →ₗ[ℂ]
      holQuadDiffSubmodule S :=
    { toFun := A
      map_add' := by
        intro f g
        apply (hreg (f + g)).unique (hA (f + g))
        intro x
        filter_upwards [hA f x, hA g x] with z hzf hzg
        change (A f : S → ℂ → ℂ) x z + (A g : S → ℂ → ℂ) x z =
          (f.1.toFun ((chartAt ℂ x).symm z) +
            g.1.toFun ((chartAt ℂ x).symm z)) * (q₀ x z)^2
        rw [hzf, hzg]
        ring
      map_smul' := by
        intro c f
        apply (hreg (c • f)).unique (hA (c • f))
        intro x
        filter_upwards [hA f x] with z hz
        change c * (A f : S → ℂ → ℂ) x z =
          (c * f.1.toFun ((chartAt ℂ x).symm z)) * (q₀ x z)^2
        rw [hz]
        ring }
  exact ⟨F, hA⟩

/-- Reviewed Q2 interface stub `k22q_regularize_kernel`; proof awaits separate GO. -/
theorem k22q_regularize_kernel {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (F : Jacobians.linearSystem (X := S) (2 • K) →ₗ[ℂ]
      holQuadDiffSubmodule S)
    (hF : ∀ f x, (F f : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2)) :
    LinearMap.ker F =
      (Jacobians.germZeroSubmodule (X := S)).submoduleOf
        (Jacobians.linearSystem (X := S) (2 • K)) := by
  ext f
  change F f = 0 ↔ ∀ x, f.1.orderW x = ⊤
  constructor
  · intro hf x
    have hprod := hF f x
    rw [hf] at hprod
    -- The integer-valued divisor excludes top, so cancellation is valid on the germ.
    have hqne : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q₀ x z ≠ 0 := by
      apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero x)).mp
      rw [← horder x]
      exact WithTop.coe_ne_top
    change meromorphicOrderAt (f.1.toFun ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x x) = ⊤
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hprod, hqne] with z hz hqz
    change f.1.toFun ((chartAt ℂ x).symm z) = 0
    change 0 = f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2 at hz
    exact (mul_eq_zero.mp hz.symm).resolve_right (pow_ne_zero 2 hqz)
  · intro hf
    apply (k22q_regularize_square q₀ hfamily hmero horder f.1 f.2).unique (hF f)
    intro x
    have hfx := hf x
    change meromorphicOrderAt (f.1.toFun ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x x) = ⊤ at hfx
    have hzero : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x),
        f.1.toFun ((chartAt ℂ x).symm z) = 0 :=
      meromorphicOrderAt_eq_top_iff.mp hfx
    filter_upwards [hzero] with z hz
    change 0 = f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2
    rw [hz, zero_mul]

/-- Reviewed Q2 interface stub `k22q_regularize_surjective`; proof awaits separate GO. -/
theorem k22q_regularize_surjective {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (F : Jacobians.linearSystem (X := S) (2 • K) →ₗ[ℂ]
      holQuadDiffSubmodule S)
    (hF : ∀ f x, (F f : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2)) :
    Function.Surjective F := by
  intro v
  obtain ⟨f, hf, hdiv⟩ :=
    k22q_division_representative q₀ hfamily hmero horder v
  refine ⟨⟨f, hf⟩, ?_⟩
  apply (k22q_regularize_square q₀ hfamily hmero horder f hf).unique (hF ⟨f, hf⟩)
  intro x
  have hqne : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q₀ x z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero x)).mp
    rw [← horder x]
    exact WithTop.coe_ne_top
  -- Use the division representative only where its denominator is nonzero.
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (chart_target_mem_nhds ℂ x), hqne] with z hz hqz
  rw [hdiv x z hz]
  exact (div_mul_cancel₀ _ (pow_ne_zero 2 hqz)).symm

/-- Finite coefficient order permits division followed by multiplication on punctured chart germs. -/
theorem k22q_e_division_product_germ {K : Divisor S}
    (q₀ : S → ℂ → ℂ)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (f : Jacobians.MeromorphicFunction S) (v : holQuadDiffSubmodule S)
    (hdiv : ∀ x z, z ∈ (chartAt ℂ x).target →
      f.toFun ((chartAt ℂ x).symm z) =
        (v : S → ℂ → ℂ) x z / (q₀ x z)^2) :
    ∀ x, (v : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  intro x
  have ht : (chartAt ℂ x).target ∈ 𝓝 (chartAt ℂ x x) :=
    (chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have hn : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q₀ x z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero x)).mp
    rw [← horder x]
    exact WithTop.coe_ne_top
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds ht, hn] with z hz hnz
  rw [hdiv x z hz]
  exact (div_mul_cancel₀ ((v : S → ℂ → ℂ) x z) (pow_ne_zero 2 hnz)).symm

/-- Reviewed Q2 interface stub `k22q_quotient_chart_equiv`; proof awaits separate GO. -/
theorem k22q_quotient_chart_equiv {K : Divisor S}
    (q₀ : S → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) =
      meromorphicOrderAt (q₀ x) (chartAt ℂ x x)) :
    ∃ e : meroFunctionSpace (2 • K) ≃ₗ[ℂ] holQuadDiffSubmodule S,
      (∀ (f : Jacobians.MeromorphicFunction S)
          (hf : f ∈ Jacobians.linearSystem (X := S) (2 • K))
          (u : meroFunctionSpace (2 • K)),
        (u : (S → ℂ) ⧸ codiscreteNull S) =
            (codiscreteNull S).mkQ f.toFun →
        ∀ x, (e u : S → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
          (fun z => f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2)) ∧
      (∀ v : holQuadDiffSubmodule S,
        ∃ f : Jacobians.MeromorphicFunction S,
          f ∈ Jacobians.linearSystem (X := S) (2 • K) ∧
          ((e.symm v : meroFunctionSpace (2 • K)) :
              (S → ℂ) ⧸ codiscreteNull S) =
            (codiscreteNull S).mkQ f.toFun ∧
          ∀ x, (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
            (fun z => (v : S → ℂ → ℂ) x z / (q₀ x z)^2)) := by
  classical
  obtain ⟨eD, hmkD⟩ := k22q_quotient_equiv_mkQ (2 • K)
  obtain ⟨F, hF⟩ := k22q_regularize_linearMap q₀ hfamily hmero horder
  have hker := k22q_regularize_kernel q₀ hfamily hmero horder F hF
  have hs := k22q_regularize_surjective q₀ hfamily hmero horder F hF
  let N := (Jacobians.germZeroSubmodule (X := S)).submoduleOf
    (Jacobians.linearSystem (X := S) (2 • K))
  let b : (↥(Jacobians.linearSystem (X := S) (2 • K)) ⧸ N)
      ≃ₗ[ℂ] holQuadDiffSubmodule S :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (F.quotKerEquivOfSurjective hs)
  have hb (a : Jacobians.linearSystem (X := S) (2 • K)) :
      b (N.mkQ a) = F a := by
    simpa only [b, LinearEquiv.trans_apply, Submodule.mkQ_apply,
      Submodule.quotEquivOfEq_mk] using
      F.quotKerEquivOfSurjective_apply_mk hs a
  let e : meroFunctionSpace (2 • K) ≃ₗ[ℂ] holQuadDiffSubmodule S :=
    eD.symm.trans b
  refine ⟨e, ?_, ?_⟩
  · intro f hf u hu x
    let a : Jacobians.linearSystem (X := S) (2 • K) := ⟨f, hf⟩
    have hu' : u = eD (N.mkQ a) := by
      apply Subtype.ext
      exact hu.trans (hmkD a).symm
    have he : e u = F a := by
      calc
        e u = b (eD.symm u) := rfl
        _ = b (N.mkQ a) := by rw [hu', eD.symm_apply_apply]
        _ = F a := hb a
    simpa only [he] using hF a x
  · intro v
    obtain ⟨f, hf, hdiv⟩ := k22q_division_representative q₀ hfamily hmero horder v
    let a : Jacobians.linearSystem (X := S) (2 • K) := ⟨f, hf⟩
    have hvprod := k22q_e_division_product_germ q₀ hmero horder f v hdiv
    obtain ⟨w, hw, hunique⟩ := k22q_regularize_square q₀ hfamily hmero horder f hf
    have hFv : F a = v :=
      (hunique (F a) (hF a)).trans (hunique v hvprod).symm
    have hev : e (eD (N.mkQ a)) = v := by
      calc
        e (eD (N.mkQ a)) = b (eD.symm (eD (N.mkQ a))) := rfl
        _ = b (N.mkQ a) := by rw [eD.symm_apply_apply]
        _ = F a := hb a
        _ = v := hFv
    have hinv : e.symm v = eD (N.mkQ a) := by
      calc
        e.symm v = e.symm (e (eD (N.mkQ a))) := congrArg e.symm hev.symm
        _ = eD (N.mkQ a) := e.symm_apply_apply _
    refine ⟨f, hf, ?_, ?_⟩
    · simpa only [hinv] using hmkD a
    · intro x
      have ht : (chartAt ℂ x).target ∈ 𝓝 (chartAt ℂ x x) :=
        (chartAt ℂ x).open_target.mem_nhds
          ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds ht] with z hz
      exact hdiv x z hz

/-- Reviewed Q2 interface stub `k22q_canonical_equiv`; proof awaits separate GO. -/
theorem k22q_canonical_equiv {K : Divisor S}
    (hK : IsCanonicalDivisor K) :
    Nonempty (meroFunctionSpace (2 • K) ≃ₗ[ℂ] holQuadDiffSubmodule S) := by
  obtain ⟨q₀, hfamily, hmero, horder⟩ := hK
  obtain ⟨e, _, _⟩ := k22q_quotient_chart_equiv q₀ hfamily hmero horder
  exact ⟨e⟩

/-- Reviewed Q2 interface stub `k22q_finite_mero`; proof awaits separate GO. -/
theorem k22q_finite_mero (D : Divisor S) :
    FiniteDimensional ℂ (meroFunctionSpace D) := by
  obtain ⟨e⟩ := k22rr_quotient_equiv D
  letI : FiniteDimensional ℂ (Jacobians.Dolbeault.lSysModule (X := S) D) :=
    Jacobians.LaurentTail.finiteDimensional_lSysModule D
  exact e.finiteDimensional

/-- Reviewed Q2 interface stub `k22q_finite_quadratic`; proof awaits separate GO. -/
theorem k22q_finite_quadratic :
    FiniteDimensional ℂ (holQuadDiffSubmodule S) := by
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := S)
  obtain ⟨e⟩ := k22q_canonical_equiv hK
  letI : FiniteDimensional ℂ (meroFunctionSpace (2 • K)) := k22q_finite_mero (2 • K)
  exact e.finiteDimensional

end k22q_context

/-- **Theorem 22.5**: on a closed Riemann surface of genus `g > 1`, `dim Q = 3g - 3`. -/
theorem thm22_5_dim_quadratic_differentials [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) :
    Module.finrank ℂ (holQuadDiffSubmodule S) = 3 * g - 3 := by
  letI : CompactSpace S := hS.1
  letI : FiniteDimensional ℂ (holQuadDiffSubmodule S) := k22q_finite_quadratic (S := S)
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := S)
  obtain ⟨e⟩ := k22q_canonical_equiv hK
  have hdeg := deg_canonical hS hK
  have hnegdeg : Jacobians.Divisor.deg S (-K) < 0 := by
    rw [map_neg, k22rr_degree_eq, hdeg]
    omega
  have hneg : ellDim (-K) = 0 := by
    rw [k22rr_ellDim_eq_lDim]
    exact Jacobians.lDim_eq_zero_of_deg_neg (-K) hnegdeg
  have hsub : K - 2 • K = -K := by
    simp only [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hdegdouble : (2 • K).deg = 2 * K.deg := by
    change Jacobians.Divisor.deg S (2 • K) = 2 * Jacobians.Divisor.deg S K
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      (map_nsmul (Jacobians.Divisor.deg S) 2 K)
  have hrr2 := thm22_4_riemann_roch hS hK (2 • K)
  rw [hsub, hneg, hdegdouble, hdeg] at hrr2
  have hdim : ellDim (2 • K) = 3 * g - 3 := by omega
  exact e.finrank_eq.symm.trans hdim

/-! ## §22.6 Fractional linear transformations -/

/-- The fixed points of `z ↦ (az + b)/(cz + d)` in `ℂ̄`. -/
def mobiusFixedPoints (a b c d : ℂ) : Set ExtPlane := {p | mobiusExt a b c d p = p}

/-- `∞` is a fixed point of `z ↦ (az+b)/(cz+d)` exactly when `c = 0`. -/
theorem mem_mobiusFixedPoints_infty_iff (a b c d : ℂ) :
    extInf ∈ mobiusFixedPoints a b c d ↔ c = 0 := by
  constructor
  · intro hfix
    by_contra hc
    rw [mobiusFixedPoints, Set.mem_setOf_eq, mobiusExt_infty_of_ne hc] at hfix
    exact OnePoint.coe_ne_infty _ hfix
  · intro hc
    exact mobiusExt_infty_of_eq hc

/-- Under `ad - bc = 1` a finite point is a fixed point exactly when it is a root of
`c z² + (d - a) z - b`.

There is no exception at the pole: if `c z + d = 0` then `mobiusExt` sends `z` to `∞`, so `z` is
not fixed, and `z` is not a root either — `a d - b c = (a - c z)(c z + d) + c (c z² + (d-a) z - b)`
would force `a d - b c = 0`. -/
theorem mem_mobiusFixedPoints_coe_iff {a b c d : ℂ} (h : a * d - b * c = 1) (z : ℂ) :
    (z : ExtPlane) ∈ mobiusFixedPoints a b c d ↔ c * z ^ 2 + (d - a) * z - b = 0 := by
  rcases eq_or_ne (c * z + d) 0 with hp | hp
  · rw [mobiusFixedPoints, Set.mem_setOf_eq, mobiusExt_coe_of_eq_zero hp]
    constructor
    · intro hcon
      exact absurd hcon.symm (OnePoint.coe_ne_infty z)
    · intro hroot
      exfalso
      have hzero : a * d - b * c = 0 := by
        linear_combination (a - c * z) * hp + c * hroot
      rw [hzero] at h
      exact zero_ne_one h
  · rw [mobiusFixedPoints, Set.mem_setOf_eq, mobiusExt_coe hp, OnePoint.coe_eq_coe, mobiusFn,
      div_eq_iff hp]
    constructor
    · intro hh
      linear_combination -hh
    · intro hh
      linear_combination -hh

/-- §22.6: a fractional linear transformation other than the identity (`ad - bc = 1`) has one or
two fixed points; it has exactly one (it is parabolic) iff `(a + d)² = 4`.

Proof.  Under `ad - bc = 1` the finite fixed points are exactly the roots of
`c z² + (d - a) z - b` (`mem_mobiusFixedPoints_coe_iff`) and `∞` is fixed iff `c = 0`
(`mem_mobiusFixedPoints_infty_iff`).

* `c ≠ 0`: `∞` is not fixed and the quadratic is genuine, with discriminant
  `(d - a)² + 4bc = (a + d)² - 4` after substituting `bc = ad - 1`.  So there are two roots,
  equal exactly when `(a + d)² = 4`.
* `c = 0`: then `ad = 1` and `∞` is fixed.  If `a ≠ d` there is also the finite fixed point
  `b/(d - a)`, so two in all, and `(a + d)² - 4 = (a - d)² ≠ 0`.  If `a = d` then `a² = 1` and
  `hne` forces `b ≠ 0`, so no finite point is fixed, `∞` is the only one, and
  `(a + d)² = 4a² = 4`.  This last case is the parabolic one. -/
theorem mobius_fixed_points {a b c d : ℂ} (h : a * d - b * c = 1)
    (hne : ¬ (b = 0 ∧ c = 0 ∧ a = d)) :
    (mobiusFixedPoints a b c d).Nonempty ∧ (mobiusFixedPoints a b c d).ncard ≤ 2 ∧
      ((mobiusFixedPoints a b c d).ncard = 1 ↔ (a + d) ^ 2 = 4) := by
  -- packaging the three conclusions from an explicit one- or two-element fixed-point set
  have one_pt : ∀ (S : Set ExtPlane) (x : ExtPlane) (P : Prop), S = {x} → P →
      S.Nonempty ∧ S.ncard ≤ 2 ∧ (S.ncard = 1 ↔ P) := by
    intro S x P hS hP
    subst hS
    refine ⟨⟨x, rfl⟩, ?_, ?_⟩
    · rw [Set.ncard_singleton]; norm_num
    · rw [Set.ncard_singleton]; simp [hP]
  have two_pt : ∀ (S : Set ExtPlane) (x y : ExtPlane) (P : Prop), S = {x, y} → x ≠ y → ¬ P →
      S.Nonempty ∧ S.ncard ≤ 2 ∧ (S.ncard = 1 ↔ P) := by
    intro S x y P hS hxy hP
    subst hS
    refine ⟨⟨x, by simp⟩, ?_, ?_⟩
    · simpa [Set.ncard_singleton] using Set.ncard_insert_le x ({y} : Set ExtPlane)
    · rw [Set.ncard_pair hxy]
      simp [hP]
  rcases eq_or_ne c 0 with hc | hc
  · -- `c = 0`: `∞` is fixed and `a d = 1`
    subst hc
    have had : a * d = 1 := by linear_combination h
    rcases eq_or_ne a d with hadeq | hadne
    · -- parabolic: `∞` is the only fixed point
      have hb : b ≠ 0 := fun hb0 => hne ⟨hb0, rfl, hadeq⟩
      refine one_pt _ extInf _ ?_ ?_
      · ext p
        induction p using OnePoint.rec with
        | infty =>
          simp only [Set.mem_singleton_iff, iff_true]
          exact (mem_mobiusFixedPoints_infty_iff a b 0 d).2 rfl
        | coe z =>
          rw [mem_mobiusFixedPoints_coe_iff h z]
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hroot
            exact absurd (by linear_combination -hroot - z * hadeq : b = 0) hb
          · intro hcon
            exact absurd hcon (OnePoint.coe_ne_infty z)
      · subst hadeq
        linear_combination 4 * had
    · -- two fixed points: `∞` and `b/(d - a)`
      have hda : d - a ≠ 0 := sub_ne_zero.2 (Ne.symm hadne)
      refine two_pt _ extInf ((b / (d - a) : ℂ) : ExtPlane) _ ?_
        (OnePoint.infty_ne_coe _) ?_
      · ext p
        induction p using OnePoint.rec with
        | infty =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, iff_true]
          exact (mem_mobiusFixedPoints_infty_iff a b 0 d).2 rfl
        | coe z =>
          rw [mem_mobiusFixedPoints_coe_iff h z]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OnePoint.coe_eq_coe,
            OnePoint.coe_ne_infty, false_or]
          rw [eq_div_iff hda]
          constructor
          · intro hroot
            linear_combination hroot
          · intro hz
            linear_combination hz
      · intro h4
        exact hadne (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num)
          |>.1 (by linear_combination h4 - 4 * had : (a - d) ^ 2 = 0)))
  · -- `c ≠ 0`: `∞` is not fixed, and the quadratic has two roots
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((a + d) ^ 2 - 4) (n := 2) (by norm_num)
    -- the two roots, described without division so the algebra stays polynomial
    obtain ⟨r₁, r₂, hsum, hprod, hdiff⟩ :
        ∃ r₁ r₂ : ℂ, c * (r₁ + r₂) = a - d ∧ c * (r₁ * r₂) = -b ∧ c * (r₁ - r₂) = s := by
      have hnum : (a - d) ^ 2 - s ^ 2 = -(4 * b * c) := by
        rw [hs]
        linear_combination -4 * h
      refine ⟨(a - d + s) / (2 * c), (a - d - s) / (2 * c), ?_, ?_, ?_⟩
      · field_simp
        ring
      · have hid : c * ((a - d + s) / (2 * c) * ((a - d - s) / (2 * c)))
            = ((a - d) ^ 2 - s ^ 2) / (4 * c) := by
          field_simp
          ring
        rw [hid, hnum]
        field_simp
      · field_simp
        ring
    have hfac : ∀ z : ℂ, c * z ^ 2 + (d - a) * z - b = c * (z - r₁) * (z - r₂) := by
      intro z
      linear_combination z * hsum - hprod
    have hset : mobiusFixedPoints a b c d = {(r₁ : ExtPlane), (r₂ : ExtPlane)} := by
      ext p
      induction p using OnePoint.rec with
      | infty =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OnePoint.infty_ne_coe,
          or_self, iff_false]
        rw [mem_mobiusFixedPoints_infty_iff]
        exact hc
      | coe z =>
        rw [mem_mobiusFixedPoints_coe_iff h z, hfac z]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OnePoint.coe_eq_coe, mul_assoc,
          mul_eq_zero, sub_eq_zero, hc, false_or]
    rcases eq_or_ne s 0 with hs0 | hs0
    · -- a double root: one fixed point
      have hr : r₁ = r₂ := by
        have h0 : c * (r₁ - r₂) = 0 := by rw [hdiff, hs0]
        exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hc)
      refine one_pt _ ((r₁ : ℂ) : ExtPlane) _ ?_ ?_
      · rw [hset, hr, Set.pair_eq_singleton]
      · rw [hs0] at hs
        linear_combination -hs
    · -- two distinct roots
      have hr : (r₁ : ExtPlane) ≠ (r₂ : ExtPlane) := by
        rw [Ne, OnePoint.coe_eq_coe, ← sub_eq_zero]
        intro h0
        rw [h0, mul_zero] at hdiff
        exact hs0 hdiff.symm
      refine two_pt _ _ _ _ hset hr ?_
      intro h4
      apply hs0
      have : s ^ 2 = 0 := by rw [hs, h4]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- The multiplier `K` of a transformation with two fixed points `z₁, z₂`:
`(w - z₁)/(w - z₂) = K (z - z₁)/(z - z₂)`. -/
def IsMultiplier (a b c d z₁ z₂ K : ℂ) : Prop :=
  z₁ ≠ z₂ ∧ ∀ z : ℂ, c * z + d ≠ 0 → z ≠ z₂ → (a * z + b) / (c * z + d) ≠ z₂ →
    ((a * z + b) / (c * z + d) - z₁) / ((a * z + b) / (c * z + d) - z₂) = K * ((z - z₁) / (z - z₂))

/-- The zero set of a nontrivial affine function `z ↦ c z + d` is finite. -/
theorem finite_setOf_linear_eq_zero {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) :
    {z : ℂ | c * z + d = 0}.Finite := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : d ≠ 0 := h.resolve_left fun h => h rfl
    have : {z : ℂ | 0 * z + d = 0} = ∅ := by
      ext z
      simp [hd]
    rw [this]
    exact Set.finite_empty
  · apply (Set.finite_singleton (-d / c)).subset
    intro z hz
    simp only [mem_setOf_eq] at hz
    simp only [mem_singleton_iff]
    rw [eq_div_iff hc]
    linear_combination hz

/-- The real-variable core of `mobius_classification_trace`.  Write `K = x + i y`,
`N = x² + y² > 0`, `a + d = p + i q`; the trace relation `(a + d)² = K + 2 + K⁻¹` reads
`(p² − q²) N = x N + 2 N + x` and `2 p q N = y N − y`.  Then `|K| = 1` iff `a + d` is real with
`|a + d| < 2`; `K` is real positive iff `a + d` is real with `|a + d| > 2`; and neither iff
`a + d` is not real. -/
theorem trace_classification_real {p q x y N : ℝ} (hNpos : 0 < N) (hNxy : N = x ^ 2 + y ^ 2)
    (hR : (p ^ 2 - q ^ 2) * N = x * N + 2 * N + x) (hI : 2 * p * q * N = y * N - y)
    (hK1 : ¬ (x = 1 ∧ y = 0)) :
    (N = 1 ↔ q = 0 ∧ |p| < 2) ∧ ((y = 0 ∧ 0 < x) ↔ q = 0 ∧ 2 < |p|) ∧
      ((N ≠ 1 ∧ ¬ (y = 0 ∧ 0 < x)) ↔ q ≠ 0) := by
  have hN0 : N ≠ 0 := hNpos.ne'
  -- (i) `|K| = 1`
  have hi : N = 1 ↔ q = 0 ∧ |p| < 2 := by
    constructor
    · intro hN1
      rw [hN1] at hR hI hNxy
      have hpq : p * q = 0 := by linear_combination hI / 2
      have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
      have hx1' : x < 1 := by
        rcases lt_or_eq_of_le hx1 with h1 | h1
        · exact h1
        · exfalso
          apply hK1
          refine ⟨h1, ?_⟩
          have hy2 : y ^ 2 = 0 := by
            rw [h1] at hNxy
            linarith
          exact pow_eq_zero_iff two_ne_zero |>.1 hy2
      rcases mul_eq_zero.1 hpq with hp0 | hq0
      · rw [hp0] at hR
        have hq2 : q ^ 2 ≤ 0 := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
        have hq0 : q = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hq2 (sq_nonneg q))
        exact ⟨hq0, by rw [hp0, abs_zero]; norm_num⟩
      · rw [hq0] at hR
        have hp2 : p ^ 2 < 4 := by nlinarith
        exact ⟨hq0, abs_lt.2 ⟨by nlinarith, by nlinarith⟩⟩
    · rintro ⟨hq0, hp2⟩
      rw [hq0] at hR hI
      have hp4 : p ^ 2 < 4 := by
        obtain ⟨h1, h2⟩ := abs_lt.1 hp2
        nlinarith
      have hy : y * (N - 1) = 0 := by linear_combination -hI
      rcases mul_eq_zero.1 hy with hy0 | hN1
      · rw [hy0] at hNxy
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hNxy
          simp at hNxy
          exact hN0 hNxy
        have hxx : (x + 1) ^ 2 = p ^ 2 * x := by
          have h1 : x * ((x + 1) ^ 2 - p ^ 2 * x) = 0 := by
            rw [hNxy] at hR
            linear_combination -hR
          exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hx0)
        rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
        · have h1 : (x + 1) ^ 2 ≤ 0 := by nlinarith [sq_nonneg p]
          have h2 : (x + 1) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
          have hx1 : x = -1 := by
            have := pow_eq_zero_iff two_ne_zero |>.1 h2
            linarith
          rw [hNxy, hx1]
          norm_num
        · exfalso
          have h1 : (x - 1) ^ 2 < 0 := by nlinarith
          exact absurd h1 (not_lt.2 (sq_nonneg _))
      · exact sub_eq_zero.1 hN1
  -- (ii) `K` real positive
  have hii : (y = 0 ∧ 0 < x) ↔ q = 0 ∧ 2 < |p| := by
    constructor
    · rintro ⟨hy0, hxpos⟩
      have hx1 : x ≠ 1 := fun h1 => hK1 ⟨h1, hy0⟩
      rw [hy0] at hNxy hI
      rw [hNxy] at hR hI
      have hpq : p * q = 0 := by
        have h1 : x ^ 2 * (2 * (p * q)) = 0 := by linear_combination hI
        have h2 := (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 hxpos.ne')
        linarith
      rcases mul_eq_zero.1 hpq with hp0 | hq0
      · exfalso
        rw [hp0] at hR
        nlinarith [mul_nonneg (sq_nonneg q) (sq_nonneg x), pow_pos hxpos 3, pow_pos hxpos 2]
      · refine ⟨hq0, ?_⟩
        rw [hq0] at hR
        have hxx : p ^ 2 * x = (x + 1) ^ 2 := by
          have h1 : x * (p ^ 2 * x - (x + 1) ^ 2) = 0 := by linear_combination hR
          exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hxpos.ne')
        have hp4 : 4 < p ^ 2 := by
          have h1 : 0 < (x - 1) ^ 2 := by
            have : x - 1 ≠ 0 := sub_ne_zero.2 hx1
            positivity
          nlinarith
        have h5 := sq_abs p
        nlinarith [abs_nonneg p]
    · rintro ⟨hq0, hp2⟩
      rw [hq0] at hR hI
      have hp4 : 4 < p ^ 2 := by
        have h5 := sq_abs p
        nlinarith [abs_nonneg p]
      have hy : y * (N - 1) = 0 := by linear_combination -hI
      rcases mul_eq_zero.1 hy with hy0 | hN1
      · refine ⟨hy0, ?_⟩
        rw [hy0] at hNxy
        rw [hNxy] at hR
        have hx0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hNxy
          simp at hNxy
          exact hN0 hNxy
        have hxx : p ^ 2 * x = (x + 1) ^ 2 := by
          have h1 : x * (p ^ 2 * x - (x + 1) ^ 2) = 0 := by linear_combination hR
          exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hx0)
        rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
        · exfalso
          nlinarith [sq_nonneg (x + 1)]
        · exact hxpos
      · exfalso
        have hN1' : N = 1 := sub_eq_zero.1 hN1
        rw [hN1'] at hR hNxy
        nlinarith [sq_nonneg y]
  refine ⟨hi, hii, ?_⟩
  -- (iii) loxodromic: the complement of (i) and (ii); `|a + d| = 2` would force `K = 1`
  constructor
  · rintro ⟨hn, hne⟩ hq0
    rcases lt_trichotomy (|p|) 2 with hp2 | hp2 | hp2
    · exact hn (hi.2 ⟨hq0, hp2⟩)
    · have hp4 : p ^ 2 = 4 := by
        have h5 := sq_abs p
        rw [hp2] at h5
        linarith
      rw [hq0] at hI hR
      have hy : y * (N - 1) = 0 := by linear_combination -hI
      have hy0 : y = 0 := (mul_eq_zero.1 hy).resolve_right (sub_ne_zero.2 hn)
      rw [hy0] at hNxy
      rw [hNxy, hp4] at hR
      have hx0 : x ≠ 0 := by
        intro hx0
        rw [hx0] at hNxy
        simp at hNxy
        exact hN0 hNxy
      have hxx : x * (x - 1) ^ 2 = 0 := by linear_combination -hR
      have hx1 : x = 1 := by
        have h1 := (mul_eq_zero.1 hxx).resolve_left hx0
        have h2 := pow_eq_zero_iff two_ne_zero |>.1 h1
        linarith
      exact hK1 ⟨hx1, hy0⟩
    · exact hne (hii.2 ⟨hq0, hp2⟩)
  · intro hq0
    exact ⟨fun hn => hq0 (hi.1 hn).1, fun hne => hq0 (hii.1 hne).1⟩

/-- Elliptic (`K = e^{iθ} ≠ 1`), hyperbolic (`K > 0`, `K ≠ 1`) and loxodromic
(`|K| ≠ 1`, `K ∉ ℝ`) transformations are distinguished by the trace:
elliptic iff `a + d ∈ (-2, 2)`, hyperbolic iff `a + d ∈ ℝ`, `|a + d| > 2`, loxodromic iff
`a + d ∉ ℝ`. -/
theorem mobius_classification_trace {a b c d z₁ z₂ K : ℂ} (h : a * d - b * c = 1)
    (hK : IsMultiplier a b c d z₁ z₂ K) (hK1 : K ≠ 1) :
    (‖K‖ = 1 ↔ (a + d).im = 0 ∧ |(a + d).re| < 2) ∧
      ((K.im = 0 ∧ 0 < K.re) ↔ (a + d).im = 0 ∧ 2 < |(a + d).re|) ∧
      ((‖K‖ ≠ 1 ∧ ¬ (K.im = 0 ∧ 0 < K.re)) ↔ (a + d).im ≠ 0) := by
  obtain ⟨h12, hmul⟩ := hK
  -- Step 1: the multiplier identity, cleared of denominators, is a polynomial identity valid on a
  -- cofinite set, hence for all `z`
  have hall : ∀ z : ℂ, (a * z + b - z₁ * (c * z + d)) * (z - z₂) =
      K * (z - z₁) * (a * z + b - z₂ * (c * z + d)) := by
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨rfl, rfl⟩ := hcon
      simp at h
    have hab : a - z₂ * c ≠ 0 ∨ b - z₂ * d ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have : a * d - b * c = 0 := by
        rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2]
        ring
      rw [this] at h
      exact zero_ne_one h
    have hfin : ({z : ℂ | c * z + d = 0} ∪
        ({z₂} ∪ {z : ℂ | (a - z₂ * c) * z + (b - z₂ * d) = 0})).Finite :=
      (finite_setOf_linear_eq_zero hcd).union
        ((Set.finite_singleton _).union (finite_setOf_linear_eq_zero hab))
    set P : Polynomial ℂ := (Polynomial.C a * Polynomial.X + Polynomial.C b -
      Polynomial.C z₁ * (Polynomial.C c * Polynomial.X + Polynomial.C d)) *
      (Polynomial.X - Polynomial.C z₂) with hP
    set Q : Polynomial ℂ := Polynomial.C K * (Polynomial.X - Polynomial.C z₁) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b -
        Polynomial.C z₂ * (Polynomial.C c * Polynomial.X + Polynomial.C d)) with hQ
    have hPQ : P = Q := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine hfin.infinite_compl.mono ?_
      intro z hz
      simp only [mem_compl_iff, mem_union, mem_singleton_iff, mem_setOf_eq, not_or] at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      have hM : (a * z + b) / (c * z + d) ≠ z₂ := by
        intro hM
        apply hz3
        rw [div_eq_iff hz1] at hM
        linear_combination hM
      have hid := hmul z hz1 hz2 hM
      have hz2' : z - z₂ ≠ 0 := sub_ne_zero.2 hz2
      have hM' : (a * z + b) / (c * z + d) - z₂ ≠ 0 := sub_ne_zero.2 hM
      rw [div_eq_iff hM'] at hid
      have e2 : (a * z + b) / (c * z + d) - z₁ =
          K * (z - z₁) * ((a * z + b) / (c * z + d) - z₂) / (z - z₂) := by
        rw [hid]
        ring
      rw [eq_div_iff hz2'] at e2
      have e3 : ((a * z + b) / (c * z + d) - z₁) * (c * z + d) = a * z + b - z₁ * (c * z + d) := by
        rw [sub_mul, div_mul_cancel₀ _ hz1]
      have e4 : ((a * z + b) / (c * z + d) - z₂) * (c * z + d) = a * z + b - z₂ * (c * z + d) := by
        rw [sub_mul, div_mul_cancel₀ _ hz1]
      show Polynomial.eval z P = Polynomial.eval z Q
      simp only [hP, hQ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [← e3, ← e4]
      linear_combination (c * z + d) * e2
    intro z
    have := congrArg (Polynomial.eval z) hPQ
    simp only [hP, hQ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X] at this
    exact this
  -- Step 2: `K ≠ 0`
  have hK0 : K ≠ 0 := by
    intro hK0
    have e1 := hall (z₂ + 1)
    have e2 := hall (z₂ + 2)
    rw [hK0] at e1 e2
    have f1 : a * (z₂ + 1) + b - z₁ * (c * (z₂ + 1) + d) = 0 := by linear_combination e1
    have f2 : a * (z₂ + 2) + b - z₁ * (c * (z₂ + 2) + d) = 0 := by linear_combination e2 / 2
    have g1 : a - z₁ * c = 0 := by linear_combination f2 - f1
    have g2 : b - z₁ * d = 0 := by linear_combination f1 - (z₂ + 1) * g1
    have : a * d - b * c = 0 := by linear_combination d * g1 - c * g2
    rw [this] at h
    exact zero_ne_one h
  -- Step 3: `z₁`, `z₂` are fixed points, and the leading coefficients agree
  have hF1 : a * z₁ + b - z₁ * (c * z₁ + d) = 0 := by
    have e := hall z₁
    have : (a * z₁ + b - z₁ * (c * z₁ + d)) * (z₁ - z₂) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h12)
  have hF2 : a * z₂ + b - z₂ * (c * z₂ + d) = 0 := by
    have e := hall z₂
    have : K * (z₂ - z₁) * (a * z₂ + b - z₂ * (c * z₂ + d)) = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hK0 (sub_ne_zero.2 h12.symm))
  have hlead : a - z₁ * c = K * (a - z₂ * c) := by
    have e0 := hall z₂
    have e1 := hall (z₂ + 1)
    have e2 := hall (z₂ + 2)
    linear_combination (e2 - 2 * e1 + e0) / 2
  -- Step 4: `c ≠ 0`
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0] at hF1 hF2 hlead h
    have had : a = d := by
      have : (a - d) * (z₁ - z₂) = 0 := by linear_combination hF1 - hF2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h12))
    have hb0 : b = 0 := by
      rw [had] at hF1
      linear_combination hF1
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha] at h
      simp at h
    apply hK1
    have h3 : a * (K - 1) = 0 := by linear_combination -hlead
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left ha0)
  -- Step 5: Vieta
  have hsum : a - d = c * (z₁ + z₂) := by
    have : (z₁ - z₂) * ((a - d) - c * (z₁ + z₂)) = 0 := by linear_combination hF1 - hF2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h12))
  have hprod : b = -(c * z₁ * z₂) := by linear_combination hF1 - z₁ * hsum
  -- Step 6: the trace relation `(a + d)² = K + 2 + K⁻¹` via `u = c z₁ + d`
  set u : ℂ := c * z₁ + d with hu
  have huu : u * (c * z₂ + d) = 1 := by
    simp only [hu]
    linear_combination h - d * hsum + c * hprod
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at huu
    exact zero_ne_one huu
  have hu2 : u⁻¹ = c * z₂ + d := inv_eq_of_mul_eq_one_right huu
  have htr : a + d = u + u⁻¹ := by
    rw [hu2, hu]
    linear_combination hsum
  have hKu : K = u⁻¹ ^ 2 := by
    have h1 : K * u = c * z₂ + d := by
      simp only [hu]
      linear_combination -hlead + (1 - K) * hsum
    rw [← hu2] at h1
    calc K = K * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
      _ = u⁻¹ ^ 2 := by rw [h1]; ring
  have hcore : (a + d) ^ 2 = K + 2 + K⁻¹ := by
    rw [htr, hKu]
    field_simp
    ring
  -- Step 7: real and imaginary parts, then the real classification
  have hNpos : 0 < Complex.normSq K := Complex.normSq_pos.2 hK0
  have hNxy : Complex.normSq K = K.re ^ 2 + K.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have hNinv : Complex.normSq K * (Complex.normSq K)⁻¹ = 1 := mul_inv_cancel₀ hNpos.ne'
  have hre : (a + d).re ^ 2 - (a + d).im ^ 2 = K.re + 2 + K.re / Complex.normSq K := by
    have := congrArg Complex.re hcore
    rw [sq, Complex.mul_re, Complex.add_re (K + 2) K⁻¹, Complex.add_re K 2, Complex.inv_re,
      Complex.re_ofNat] at this
    linear_combination this
  have him : 2 * (a + d).re * (a + d).im = K.im + -K.im / Complex.normSq K := by
    have := congrArg Complex.im hcore
    rw [sq, Complex.mul_im, Complex.add_im (K + 2) K⁻¹, Complex.add_im K 2, Complex.inv_im,
      Complex.im_ofNat] at this
    linear_combination this
  have hR : ((a + d).re ^ 2 - (a + d).im ^ 2) * Complex.normSq K =
      K.re * Complex.normSq K + 2 * Complex.normSq K + K.re := by
    linear_combination Complex.normSq K * hre + K.re * hNinv
  have hI : 2 * (a + d).re * (a + d).im * Complex.normSq K = K.im * Complex.normSq K - K.im := by
    linear_combination Complex.normSq K * him - K.im * hNinv
  have hK1' : ¬ (K.re = 1 ∧ K.im = 0) := by
    rintro ⟨hx1, hy0⟩
    exact hK1 (Complex.ext (by simp [hx1]) (by simp [hy0]))
  have hnorm : ‖K‖ = 1 ↔ Complex.normSq K = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h1
      rw [h1]
      norm_num
    · intro h1
      have h3 : (‖K‖ - 1) * (‖K‖ + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · linarith [norm_nonneg K]
  obtain ⟨hi, hii, hiii⟩ := trace_classification_real hNpos hNxy hR hI hK1'
  refine ⟨hnorm.trans hi, hii, ?_⟩
  simp only [ne_eq] at hiii ⊢
  rw [hnorm]
  exact hiii

/-- The fractional linear transformation of `ℂ̄` defined by `γ ∈ SL(2, ℂ)`. -/
def mobiusSL (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ExtPlane → ExtPlane :=
  mobiusExt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

/-- The limit set `Λ(Γ)`: limits of orbits along infinitely many distinct group elements. -/
def limitSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) : Set ExtPlane :=
  {p | ∃ (q : ExtPlane) (γs : ℕ → Γ), Function.Injective γs ∧
    Tendsto (fun n => mobiusSL (γs n) q) atTop (𝓝 p)}

/-- A Klein group: a discontinuous group with non-empty set of discontinuity `Ω(Γ) = ℂ̄ ∖ Λ(Γ)`
and more than two limit points. -/
def IsKleinGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) : Prop :=
  (limitSet Γ)ᶜ.Nonempty ∧ 2 < (limitSet Γ).encard ∧
    ∀ C : Set ExtPlane, IsCompact C → C ⊆ (limitSet Γ)ᶜ →
      {γ ∈ Γ | (mobiusSL γ '' C ∩ C).Nonempty}.Finite

/-! ### s24k track (coordinator 553e2d): the convergence property and limit sets of Klein groups -/

/-! ## Convergence property of `SL(2, ℂ)` (helpers `k22_…`) -/

/-- The point `(x : y)` of `ℂ̄`: `x / y`, or `∞` when `y = 0`. -/
def k22_ratio (x y : ℂ) : ExtPlane := if y = 0 then extInf else ((x / y : ℂ) : ExtPlane)

/-- Scale invariance of `k22_ratio`: `(c x : c y) = (x : y)` for `c ≠ 0`. -/
theorem k22_ratio_mul {c : ℂ} (hc : c ≠ 0) (x y : ℂ) :
    k22_ratio (c * x) (c * y) = k22_ratio x y := by
  by_cases hy : y = 0
  · simp [k22_ratio, hy]
  · simp only [k22_ratio, hy, mul_eq_zero, hc, or_self, ↓reduceIte]
    rw [mul_div_mul_left x y hc]

/-- The inversion `w ↦ 1/w` swaps the two coordinates of `(y : x)` when `x ≠ 0`. -/
theorem k22_ratio_inv {x : ℂ} (hx : x ≠ 0) (y : ℂ) :
    mobiusExt 0 1 1 0 (k22_ratio y x) = k22_ratio x y := by
  by_cases hy : y = 0
  · simp [k22_ratio, hx, hy, mobiusExt]
  · simp [k22_ratio, hx, hy, mobiusExt]

/-- Continuity of `(x : y)` at pairs `≠ (0, 0)`: if `u → x`, `v → y` and `(x, y) ≠ (0, 0)`, then
`(u : v) → (x : y)` in `ℂ̄`. -/
theorem k22_ratio_tendsto {α : Type*} {L : Filter α} {u v : α → ℂ} {x y : ℂ}
    (hu : Tendsto u L (𝓝 x)) (hv : Tendsto v L (𝓝 y)) (hxy : y = 0 → x ≠ 0) :
    Tendsto (fun t => k22_ratio (u t) (v t)) L (𝓝 (k22_ratio x y)) := by
  have key : ∀ {u v : α → ℂ} {x y : ℂ}, Tendsto u L (𝓝 x) → Tendsto v L (𝓝 y) → y ≠ 0 →
      Tendsto (fun t => k22_ratio (u t) (v t)) L (𝓝 (k22_ratio x y)) := by
    intro u v x y hu hv hy
    have h1 : Tendsto (fun t => ((u t / v t : ℂ) : ExtPlane)) L (𝓝 ((x / y : ℂ) : ExtPlane)) :=
      (OnePoint.continuous_coe.tendsto _).comp (hu.div hv hy)
    have h2 : k22_ratio x y = ((x / y : ℂ) : ExtPlane) := by simp [k22_ratio, hy]
    rw [h2]
    refine h1.congr' ?_
    filter_upwards [hv.eventually_ne hy] with t ht
    simp [k22_ratio, ht]
  by_cases hy : y = 0
  · have hx := hxy hy
    have h1 := ((continuous_mobiusExt (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num)).tendsto _).comp
      (key hv hu hx)
    rw [Function.comp_def, k22_ratio_inv hx] at h1
    refine h1.congr' ?_
    filter_upwards [hu.eventually_ne hx] with t ht
    exact k22_ratio_inv ht _
  · exact key hu hv hy

/-- `mobiusExt` at a finite point is the ratio of the image vector `(a w + b, c w + d)`. -/
theorem k22_mobiusExt_coe (a b c d w : ℂ) :
    mobiusExt a b c d (w : ExtPlane) = k22_ratio (a * w + b) (c * w + d) := by
  by_cases h : c * w + d = 0 <;> simp [mobiusExt, k22_ratio, h]

/-- `mobiusExt` at `∞` is the ratio of the first column `(a, c)`. -/
theorem k22_mobiusExt_infty (a b c d : ℂ) :
    mobiusExt a b c d extInf = k22_ratio a c := by
  by_cases h : c = 0 <;> simp [mobiusExt, k22_ratio, h]

/-- The entries of the inverse in `SL(2, ℂ)`: `γ⁻¹ = [[d, -b], [-c, a]]`. -/
theorem k22_inv_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    γ⁻¹ 0 0 = γ 1 1 ∧ γ⁻¹ 0 1 = -γ 0 1 ∧ γ⁻¹ 1 0 = -γ 1 0 ∧ γ⁻¹ 1 1 = γ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- The determinant identity `a d - b c = 1` for `γ ∈ SL(2, ℂ)`. -/
theorem k22_det (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

/-- **Rank one.** A nonzero `2 × 2` matrix with zero determinant is `u vᵀ` with `u, v ≠ 0`; real
entries give real `u, v`. -/
theorem k22_rank_one {p00 p01 p10 p11 : ℂ} (hdet : p00 * p11 - p01 * p10 = 0)
    (hne : p00 ≠ 0 ∨ p01 ≠ 0 ∨ p10 ≠ 0 ∨ p11 ≠ 0) :
    ∃ u1 u2 v1 v2 : ℂ, (u1 ≠ 0 ∨ u2 ≠ 0) ∧ (v1 ≠ 0 ∨ v2 ≠ 0) ∧
      p00 = u1 * v1 ∧ p01 = u1 * v2 ∧ p10 = u2 * v1 ∧ p11 = u2 * v2 ∧
      (p00.im = 0 → p01.im = 0 → p10.im = 0 → p11.im = 0 →
        u1.im = 0 ∧ u2.im = 0 ∧ v1.im = 0 ∧ v2.im = 0) := by
  by_cases h0 : p00 = 0
  · by_cases h1 : p01 = 0
    · have h23 : p10 ≠ 0 ∨ p11 ≠ 0 := by
        rcases hne with h | h | h
        · exact absurd h0 h
        · exact absurd h1 h
        · exact h
      refine ⟨0, 1, p10, p11, Or.inr one_ne_zero, h23, by simp [h0], by simp [h1], by ring,
        by ring, ?_⟩
      intro _ _ h2 h3
      exact ⟨by simp, by simp, h2, h3⟩
    · have h2 : p10 = 0 := by
        have : p01 * p10 = 0 := by linear_combination -hdet + p11 * h0
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h h1
        · exact h
      refine ⟨1, p11 / p01, p00, p01, Or.inl one_ne_zero, Or.inr h1, by ring, by ring,
        by simp [h0, h2], (div_mul_cancel₀ p11 h1).symm, ?_⟩
      intro r0 r1 _ r3
      exact ⟨by simp, by simp [Complex.div_im, r1, r3], r0, r1⟩
  · refine ⟨1, p10 / p00, p00, p01, Or.inl one_ne_zero, Or.inl h0, by ring, by ring,
      (div_mul_cancel₀ p10 h0).symm, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hdet
    · intro r0 r1 r2 _
      exact ⟨by simp, by simp [Complex.div_im, r0, r2], r0, r1⟩

/-- The limit of the image ratios under matrices converging to a rank-one `u vᵀ`: if
`(A, B; C, D) → u vᵀ`, `(X, Y) → (x, y)` and `v · (x, y) ≠ 0`, then
`(A X + B Y : C X + D Y) → (u₁ : u₂)`. -/
theorem k22_tendsto_rank_one {β : Type*} {L : Filter β} {A B C D X Y : β → ℂ}
    {u1 u2 v1 v2 x y : ℂ}
    (hA : Tendsto A L (𝓝 (u1 * v1))) (hB : Tendsto B L (𝓝 (u1 * v2)))
    (hC : Tendsto C L (𝓝 (u2 * v1))) (hD : Tendsto D L (𝓝 (u2 * v2)))
    (hX : Tendsto X L (𝓝 x)) (hY : Tendsto Y L (𝓝 y))
    (hu : u1 ≠ 0 ∨ u2 ≠ 0) (ht : v1 * x + v2 * y ≠ 0) :
    Tendsto (fun z => k22_ratio (A z * X z + B z * Y z) (C z * X z + D z * Y z)) L
      (𝓝 (k22_ratio u1 u2)) := by
  have h1 : Tendsto (fun z => A z * X z + B z * Y z) L (𝓝 ((v1 * x + v2 * y) * u1)) := by
    have := (hA.mul hX).add (hB.mul hY)
    convert this using 2
    ring
  have h2 : Tendsto (fun z => C z * X z + D z * Y z) L (𝓝 ((v1 * x + v2 * y) * u2)) := by
    have := (hC.mul hX).add (hD.mul hY)
    convert this using 2
    ring
  have h3 := k22_ratio_tendsto h1 h2 (by
    intro h
    rcases hu with hu | hu
    · exact mul_ne_zero ht hu
    · exact absurd h (mul_ne_zero ht hu))
  rwa [k22_ratio_mul ht] at h3

/-- **Local uniform convergence.** If the rescaled matrices `c n • γ n` converge to a rank-one
`u vᵀ`, then `γ n → (u₁ : u₂)` locally uniformly at every point `p ≠ (-v₂ : v₁)`. -/
theorem k22_conv_local (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ) (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n ≠ 0) {u1 u2 v1 v2 : ℂ} (hu : u1 ≠ 0 ∨ u2 ≠ 0)
    (hv : v1 ≠ 0 ∨ v2 ≠ 0)
    (h00 : Tendsto (fun n => c n * γs n 0 0) atTop (𝓝 (u1 * v1)))
    (h01 : Tendsto (fun n => c n * γs n 0 1) atTop (𝓝 (u1 * v2)))
    (h10 : Tendsto (fun n => c n * γs n 1 0) atTop (𝓝 (u2 * v1)))
    (h11 : Tendsto (fun n => c n * γs n 1 1) atTop (𝓝 (u2 * v2)))
    {p : ExtPlane} (hp : p ≠ k22_ratio (-v2) v1) :
    Tendsto (fun z : ℕ × ExtPlane => mobiusSL (γs z.1) z.2) (atTop ×ˢ 𝓝 p)
      (𝓝 (k22_ratio u1 u2)) := by
  induction p using OnePoint.rec with
  | infty =>
    have hv1 : v1 ≠ 0 := by
      intro h
      apply hp
      simp [k22_ratio, h]
    rw [OnePoint.nhds_infty_eq, prod_sup, tendsto_sup]
    constructor
    · rw [prod_map_right, tendsto_map'_iff, coclosedCompact_eq_cocompact,
        ← Metric.cobounded_eq_cocompact]
      have hY : Tendsto (fun z : ℕ × ℂ => z.2⁻¹) (atTop ×ˢ Bornology.cobounded ℂ) (𝓝 0) :=
        tendsto_inv₀_cobounded.comp tendsto_snd
      have key := k22_tendsto_rank_one (h00.comp tendsto_fst) (h01.comp tendsto_fst)
        (h10.comp tendsto_fst) (h11.comp tendsto_fst) tendsto_const_nhds hY hu
        (x := 1) (by simpa using hv1)
      refine key.congr' ?_
      have hw : ∀ᶠ z : ℕ × ℂ in atTop ×ˢ Bornology.cobounded ℂ, c z.1 ≠ 0 ∧ z.2 ≠ 0 := by
        have h2 : ∀ᶠ w : ℂ in Bornology.cobounded ℂ, w ≠ 0 := by
          rw [Metric.cobounded_eq_cocompact]
          exact (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
        exact (hc.prod_inl _).and (h2.prod_inr _)
      filter_upwards [hw] with z hz
      obtain ⟨n, w⟩ := z
      obtain ⟨hcn, hw0⟩ := hz
      simp only [Function.comp_apply, Prod.map_apply, id, mobiusSL]
      rw [k22_mobiusExt_coe]
      refine Eq.trans ?_ (k22_ratio_mul (mul_ne_zero hcn (inv_ne_zero hw0)) _ _)
      congr 1
      · field_simp
      · field_simp
    · rw [prod_pure, tendsto_map'_iff]
      have key := k22_tendsto_rank_one h00 h01 h10 h11 (tendsto_const_nhds (x := (1 : ℂ)))
        (tendsto_const_nhds (x := (0 : ℂ))) hu (by simpa using hv1)
      refine key.congr' ?_
      filter_upwards [hc] with n hn
      simp only [Function.comp_apply, mobiusSL]
      rw [k22_mobiusExt_infty]
      refine Eq.trans ?_ (k22_ratio_mul hn _ _)
      congr 1 <;> ring
  | coe z0 =>
    have ht : v1 * z0 + v2 * 1 ≠ 0 := by
      intro h
      by_cases hv1 : v1 = 0
      · rcases hv with hv | hv
        · exact hv hv1
        · apply hv
          simpa [hv1] using h
      · apply hp
        simp only [k22_ratio, hv1, ite_false]
        congr 1
        rw [eq_div_iff hv1]
        linear_combination h
    rw [OnePoint.nhds_coe_eq, prod_map_right, tendsto_map'_iff]
    have key := k22_tendsto_rank_one (h00.comp tendsto_fst) (h01.comp tendsto_fst)
      (h10.comp tendsto_fst) (h11.comp tendsto_fst) tendsto_snd tendsto_const_nhds hu ht
    refine key.congr' ?_
    filter_upwards [hc.prod_inl _] with z hz
    obtain ⟨n, w⟩ := z
    simp only [Function.comp_apply, Prod.map_apply, id, mobiusSL]
    rw [k22_mobiusExt_coe]
    refine Eq.trans ?_ (k22_ratio_mul hz _ _)
    congr 1 <;> ring

/-- **Uniform convergence on compacta.** Under the hypotheses of `k22_conv_local`, `γ n` maps
every compact set avoiding `(-v₂ : v₁)` eventually into any neighbourhood of `(u₁ : u₂)`. -/
theorem k22_conv_compact (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ) (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n ≠ 0) {u1 u2 v1 v2 : ℂ} (hu : u1 ≠ 0 ∨ u2 ≠ 0)
    (hv : v1 ≠ 0 ∨ v2 ≠ 0)
    (h00 : Tendsto (fun n => c n * γs n 0 0) atTop (𝓝 (u1 * v1)))
    (h01 : Tendsto (fun n => c n * γs n 0 1) atTop (𝓝 (u1 * v2)))
    (h10 : Tendsto (fun n => c n * γs n 1 0) atTop (𝓝 (u2 * v1)))
    (h11 : Tendsto (fun n => c n * γs n 1 1) atTop (𝓝 (u2 * v2)))
    (K : Set ExtPlane) (hK : IsCompact K) (hbK : k22_ratio (-v2) v1 ∉ K)
    (U : Set ExtPlane) (hU : U ∈ 𝓝 (k22_ratio u1 u2)) :
    ∀ᶠ n in atTop, mobiusSL (γs n) '' K ⊆ U := by
  have hall : ∀ᶠ n in atTop, ∀ q ∈ K, mobiusSL (γs n) q ∈ U := by
    refine hK.induction_on (p := fun S => ∀ᶠ n in atTop, ∀ q ∈ S, mobiusSL (γs n) q ∈ U)
      ?_ ?_ ?_ ?_
    · exact Eventually.of_forall (by simp)
    · intro s t hst ht
      filter_upwards [ht] with n hn q hq using hn q (hst hq)
    · intro s t hs ht
      filter_upwards [hs, ht] with n hn hn' q hq
      rcases hq with hq | hq
      · exact hn q hq
      · exact hn' q hq
    · intro x hx
      have hxb : x ≠ k22_ratio (-v2) v1 := fun h => hbK (h ▸ hx)
      have hloc := k22_conv_local γs c hc hu hv h00 h01 h10 h11 hxb
      have hev : ∀ᶠ z in atTop ×ˢ 𝓝 x, mobiusSL (γs z.1) z.2 ∈ U := hloc hU
      obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 hev
      refine ⟨{q | pb q}, mem_nhdsWithin_of_mem_nhds hpb, ?_⟩
      filter_upwards [hpa] with n hn q hq using hab hn hq
  filter_upwards [hall] with n hn
  rintro _ ⟨q, hq, rfl⟩
  exact hn q hq

/-- A ratio of two real numbers lies on the extended real line `ℝ̄ = ℝ ∪ {∞}`. -/
theorem k22_ratio_mem_real {x y : ℂ} (hx : x.im = 0) (hy : y.im = 0) :
    k22_ratio x y ∈ toExt {z : ℂ | z.im = 0} ∪ {extInf} := by
  by_cases h : y = 0
  · right
    simp [k22_ratio, h]
  · left
    simp only [k22_ratio, h, ite_false]
    exact ⟨x / y, by simp [Complex.div_im, hx, hy], rfl⟩

/-- **Convergence property, with the real refinement.** A sequence in `SL(2, ℂ)` with unbounded
entries has a subsequence converging locally uniformly off `b` to the constant `a`, with the
inverses converging to `b` off `a`; for real matrices, `a, b ∈ ℝ̄`. -/
theorem k22_convergence_aux (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hγ : Tendsto (fun n => ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (a b : ExtPlane), StrictMono φ ∧
      (∀ K : Set ExtPlane, IsCompact K → b ∉ K → ∀ U ∈ 𝓝 a,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n)) '' K ⊆ U) ∧
      (∀ K : Set ExtPlane, IsCompact K → a ∉ K → ∀ U ∈ 𝓝 b,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n))⁻¹ '' K ⊆ U) ∧
      ((∀ n (i j : Fin 2), (γs n i j).im = 0) →
        a ∈ toExt {z : ℂ | z.im = 0} ∪ {extInf} ∧ b ∈ toExt {z : ℂ | z.im = 0} ∪ {extInf}) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ,
      s = fun n => ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖ := ⟨_, rfl⟩
  rw [← hs] at hγ
  have hsn : ∀ n, s n = ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖ := fun n => by rw [hs]
  have hs0 : ∀ n, 0 ≤ s n := fun n => by rw [hsn n]; positivity
  have hb : ∀ n (z : ℂ), ‖z‖ ≤ s n → z / (s n : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro n z hz
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_of_nonneg (hs0 n)]
    exact div_le_one_of_le₀ hz (hs0 n)
  let m : ℕ → (ℂ × ℂ) × (ℂ × ℂ) := fun n =>
    ((γs n 0 0 / s n, γs n 0 1 / s n), (γs n 1 0 / s n, γs n 1 1 / s n))
  have hmem : ∀ n, m n ∈ (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1) ×ˢ
      (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1) := by
    intro n
    have n0 := norm_nonneg (γs n 0 0)
    have n1 := norm_nonneg (γs n 0 1)
    have n2 := norm_nonneg (γs n 1 0)
    have n3 := norm_nonneg (γs n 1 1)
    refine ⟨⟨hb n _ ?_, hb n _ ?_⟩, ⟨hb n _ ?_, hb n _ ?_⟩⟩ <;> rw [hsn n] <;> linarith
  have hB : Bornology.IsBounded ((closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1) ×ˢ
      (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1)) :=
    (isBounded_closedBall.prod isBounded_closedBall).prod
      (isBounded_closedBall.prod isBounded_closedBall)
  obtain ⟨P, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hB hmem
  have t00 : Tendsto (fun n => γs (φ n) 0 0 / (s (φ n) : ℂ)) atTop (𝓝 P.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto P).comp hlim
  have t01 : Tendsto (fun n => γs (φ n) 0 1 / (s (φ n) : ℂ)) atTop (𝓝 P.1.2) :=
    ((continuous_snd.comp continuous_fst).tendsto P).comp hlim
  have t10 : Tendsto (fun n => γs (φ n) 1 0 / (s (φ n) : ℂ)) atTop (𝓝 P.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto P).comp hlim
  have t11 : Tendsto (fun n => γs (φ n) 1 1 / (s (φ n) : ℂ)) atTop (𝓝 P.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto P).comp hlim
  have hsφ : Tendsto (fun n => s (φ n)) atTop atTop := hγ.comp hφ.tendsto_atTop
  have hpos : ∀ᶠ n in atTop, 0 < s (φ n) := hsφ.eventually_gt_atTop 0
  -- the limit is nonzero
  have hsum : ‖P.1.1‖ + ‖P.1.2‖ + ‖P.2.1‖ + ‖P.2.2‖ = 1 := by
    have h1 := ((t00.norm.add t01.norm).add t10.norm).add t11.norm
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [hpos] with n hn
    simp only [norm_div, Complex.norm_of_nonneg hn.le]
    rw [← add_div, ← add_div, ← add_div, ← hsn, div_self hn.ne']
  have hne : P.1.1 ≠ 0 ∨ P.1.2 ≠ 0 ∨ P.2.1 ≠ 0 ∨ P.2.2 ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2] at hsum
    norm_num at hsum
  -- the limit has determinant zero
  have hdet : P.1.1 * P.2.2 - P.1.2 * P.2.1 = 0 := by
    have h1 := (t00.mul t11).sub (t01.mul t10)
    have hr : Tendsto (fun n => (((s (φ n))⁻¹ ^ 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h2 := (tendsto_inv_atTop_zero.comp hsφ).pow 2
      rw [zero_pow two_ne_zero] at h2
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp h2
      rw [Complex.ofReal_zero] at h3
      exact h3
    refine tendsto_nhds_unique h1 (hr.congr' ?_)
    filter_upwards [hpos] with n hn
    have hs' : (s (φ n) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hd := k22_det (γs (φ n))
    push_cast
    field_simp
    linear_combination -hd
  obtain ⟨u1, u2, v1, v2, hu, hv, e00, e01, e10, e11, hreal⟩ := k22_rank_one hdet hne
  -- the rescaling factors
  set c : ℕ → ℂ := fun n => ((s (φ n) : ℂ))⁻¹ with hc_def
  have hc : ∀ᶠ n in atTop, c n ≠ 0 := by
    filter_upwards [hpos] with n hn
    exact inv_ne_zero (by exact_mod_cast hn.ne')
  have r00 : Tendsto (fun n => c n * γs (φ n) 0 0) atTop (𝓝 (u1 * v1)) := by
    rw [← e00]; exact t00.congr fun n => div_eq_inv_mul _ _
  have r01 : Tendsto (fun n => c n * γs (φ n) 0 1) atTop (𝓝 (u1 * v2)) := by
    rw [← e01]; exact t01.congr fun n => div_eq_inv_mul _ _
  have r10 : Tendsto (fun n => c n * γs (φ n) 1 0) atTop (𝓝 (u2 * v1)) := by
    rw [← e10]; exact t10.congr fun n => div_eq_inv_mul _ _
  have r11 : Tendsto (fun n => c n * γs (φ n) 1 1) atTop (𝓝 (u2 * v2)) := by
    rw [← e11]; exact t11.congr fun n => div_eq_inv_mul _ _
  refine ⟨φ, k22_ratio u1 u2, k22_ratio (-v2) v1, hφ, ?_, ?_, ?_⟩
  · intro K hK hbK U hU
    exact k22_conv_compact (fun n => γs (φ n)) c hc hu hv r00 r01 r10 r11 K hK hbK U hU
  · -- the inverses: `γ⁻¹ = [[d, -b], [-c, a]]` rescales to `(v₂, -v₁)ᵀ (u₂, -u₁)`
    intro K hK haK U hU
    have hu' : v2 ≠ 0 ∨ -v1 ≠ 0 := by
      rcases hv with h | h
      · exact Or.inr (neg_ne_zero.2 h)
      · exact Or.inl h
    have hv' : u2 ≠ 0 ∨ -u1 ≠ 0 := by
      rcases hu with h | h
      · exact Or.inr (neg_ne_zero.2 h)
      · exact Or.inl h
    have q00 : Tendsto (fun n => c n * (γs (φ n))⁻¹ 0 0) atTop (𝓝 (v2 * u2)) := by
      rw [mul_comm v2]
      exact r11.congr fun n => by rw [(k22_inv_apply _).1]
    have q01 : Tendsto (fun n => c n * (γs (φ n))⁻¹ 0 1) atTop (𝓝 (v2 * -u1)) := by
      have := r01.neg
      rw [show -(u1 * v2) = v2 * -u1 by ring] at this
      exact this.congr fun n => by rw [(k22_inv_apply _).2.1]; ring
    have q10 : Tendsto (fun n => c n * (γs (φ n))⁻¹ 1 0) atTop (𝓝 (-v1 * u2)) := by
      have := r10.neg
      rw [show -(u2 * v1) = -v1 * u2 by ring] at this
      exact this.congr fun n => by rw [(k22_inv_apply _).2.2.1]; ring
    have q11 : Tendsto (fun n => c n * (γs (φ n))⁻¹ 1 1) atTop (𝓝 (-v1 * -u1)) := by
      rw [show -v1 * -u1 = u1 * v1 by ring]
      exact r00.congr fun n => by rw [(k22_inv_apply _).2.2.2]
    have hb' : k22_ratio v2 (-v1) = k22_ratio (-v2) v1 := by
      have := k22_ratio_mul (c := -1) (by norm_num) v2 (-v1)
      rw [← this]
      congr 1 <;> ring
    have ha' : k22_ratio (-(-u1)) u2 = k22_ratio u1 u2 := by rw [neg_neg]
    rw [← hb'] at hU
    rw [← ha'] at haK
    exact k22_conv_compact (fun n => (γs (φ n))⁻¹) c hc hu' hv' q00 q01 q10 q11 K hK haK U hU
  · intro hγr
    have him : ∀ (i j : Fin 2) (p : ℂ),
        Tendsto (fun n => γs (φ n) i j / (s (φ n) : ℂ)) atTop (𝓝 p) → p.im = 0 := by
      intro i j p hp
      have h1 := (Complex.continuous_im.tendsto p).comp hp
      refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (Eventually.of_forall ?_))
      intro n
      simp [Complex.div_ofReal_im, hγr (φ n) i j]
    obtain ⟨a1, a2, b1, b2⟩ := hreal (him 0 0 _ t00) (him 0 1 _ t01) (him 1 0 _ t10)
      (him 1 1 _ t11)
    exact ⟨k22_ratio_mem_real a1 a2, k22_ratio_mem_real (by simp [b2]) b1⟩

/-- **Convergence property.** A sequence in SL(2, ℂ) with unbounded entries has a subsequence
converging, locally uniformly off one point `b`, to the constant `a`, with the inverses converging
to `b` off `a`. -/
theorem k22_convergence (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hγ : Tendsto (fun n => ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (a b : ExtPlane), StrictMono φ ∧
      (∀ K : Set ExtPlane, IsCompact K → b ∉ K → ∀ U ∈ 𝓝 a,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n)) '' K ⊆ U) ∧
      (∀ K : Set ExtPlane, IsCompact K → a ∉ K → ∀ U ∈ 𝓝 b,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n))⁻¹ '' K ⊆ U) := by
  obtain ⟨φ, a, b, h1, h2, h3, -⟩ := k22_convergence_aux γs hγ
  exact ⟨φ, a, b, h1, h2, h3⟩

/-- **Convergence property, real case.** For a sequence in `SL(2, ℝ) ⊆ SL(2, ℂ)` (all entries
real) with unbounded entries, the attracting and repelling points `a, b` of
`k22_convergence` can be taken on the extended real line `ℝ̄ = toExt {Im = 0} ∪ {∞}`. -/
theorem k22_convergence_real (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hγ : Tendsto (fun n => ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖) atTop atTop)
    (hreal : ∀ n (i j : Fin 2), (γs n i j).im = 0) :
    ∃ (φ : ℕ → ℕ) (a b : ExtPlane), StrictMono φ ∧
      (∀ K : Set ExtPlane, IsCompact K → b ∉ K → ∀ U ∈ 𝓝 a,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n)) '' K ⊆ U) ∧
      (∀ K : Set ExtPlane, IsCompact K → a ∉ K → ∀ U ∈ 𝓝 b,
        ∀ᶠ n in atTop, mobiusSL (γs (φ n))⁻¹ '' K ⊆ U) ∧
      a ∈ toExt {z : ℂ | z.im = 0} ∪ {extInf} ∧ b ∈ toExt {z : ℂ | z.im = 0} ∪ {extInf} := by
  obtain ⟨φ, a, b, h1, h2, h3, h4⟩ := k22_convergence_aux γs hγ
  exact ⟨φ, a, b, h1, h2, h3, h4 hreal⟩

/-! ## Limit sets of Klein groups (helpers `k22_t_…`) -/

/-- `mobiusSL γ` is the `GL(2, ℂ)` action of `γ` on `OnePoint ℂ`. -/
theorem k22_t_mobiusSL_eq_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (w : ExtPlane) :
    mobiusSL γ w = (Matrix.SpecialLinearGroup.toGL γ) • w := by
  induction w using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases h : γ 1 0 = 0
    · rw [mobiusSL, mobiusExt_infty_of_eq h]
      simp [h]
    · simp [mobiusSL, mobiusExt_infty_of_ne h, h]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : γ 1 0 * z + γ 1 1 = 0
    · simp [mobiusSL, mobiusExt_coe_of_eq_zero h, h]
    · simp [mobiusSL, mobiusExt_coe h, h, mobiusFn]

/-- `mobiusSL` turns products into compositions. -/
theorem k22_t_mobiusSL_mul (g h : Matrix.SpecialLinearGroup (Fin 2) ℂ) (w : ExtPlane) :
    mobiusSL (g * h) w = mobiusSL g (mobiusSL h w) := by
  rw [k22_t_mobiusSL_eq_smul, k22_t_mobiusSL_eq_smul, k22_t_mobiusSL_eq_smul, map_mul, mul_smul]

/-- `mobiusSL 1` is the identity. -/
theorem k22_t_mobiusSL_one (w : ExtPlane) : mobiusSL 1 w = w := by
  rw [k22_t_mobiusSL_eq_smul, map_one, one_smul]

/-- `mobiusSL g⁻¹` undoes `mobiusSL g`. -/
theorem k22_t_mobiusSL_inv_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) (w : ExtPlane) :
    mobiusSL g⁻¹ (mobiusSL g w) = w := by
  rw [← k22_t_mobiusSL_mul, inv_mul_cancel, k22_t_mobiusSL_one]

/-- The determinant of `γ ∈ SL(2, ℂ)` in entries. -/
theorem k22_t_det (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

/-- `mobiusSL γ` is continuous. -/
theorem k22_t_continuous (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Continuous (mobiusSL γ) :=
  continuous_mobiusExt (by rw [k22_t_det]; exact one_ne_zero)

/-- `mobiusSL γ` is injective. -/
theorem k22_t_injective (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    Function.Injective (mobiusSL γ) := fun x y hxy => by
  rw [← k22_t_mobiusSL_inv_apply γ x, hxy, k22_t_mobiusSL_inv_apply]

/-- Direct case: when the limit denominator at `z` does not vanish, `mobiusExt` at `z`
depends continuously on the coefficients. -/
theorem k22_t_tendsto_mobiusExt_coe_of_ne {α : Type*} {l : Filter α} {a b c d : α → ℂ}
    {a₀ b₀ c₀ d₀ : ℂ} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀)) {z : ℂ} (hz : c₀ * z + d₀ ≠ 0) :
    Tendsto (fun n => mobiusExt (a n) (b n) (c n) (d n) (z : ExtPlane)) l
      (𝓝 (mobiusExt a₀ b₀ c₀ d₀ (z : ExtPlane))) := by
  have hden : Tendsto (fun n => c n * z + d n) l (𝓝 (c₀ * z + d₀)) :=
    (hc.mul_const z).add hd
  have hnum : Tendsto (fun n => a n * z + b n) l (𝓝 (a₀ * z + b₀)) :=
    (ha.mul_const z).add hb
  have hne : ∀ᶠ n in l, c n * z + d n ≠ 0 := hden.eventually_ne hz
  rw [mobiusExt_coe hz]
  have hlim : Tendsto (fun n => ((mobiusFn (a n) (b n) (c n) (d n) z : ℂ) : ExtPlane)) l
      (𝓝 ((mobiusFn a₀ b₀ c₀ d₀ z : ℂ) : ExtPlane)) :=
    (OnePoint.continuous_coe.tendsto _).comp (hnum.div hden hz)
  refine hlim.congr' ?_
  filter_upwards [hne] with n hn
  exact (mobiusExt_coe hn).symm

/-- Post-composing with `w ↦ 1/w` swaps the rows of the coefficient matrix. -/
theorem k22_t_inv_mobiusExt_coe {a b c d : ℂ} (h : a * d - b * c ≠ 0) (z : ℂ) :
    mobiusExt 0 1 1 0 (mobiusExt a b c d (z : ExtPlane)) = mobiusExt c d a b (z : ExtPlane) := by
  by_cases hz : c * z + d = 0
  · have hn : a * z + b ≠ 0 := by
      intro hab
      apply h
      linear_combination a * hz - c * hab
    rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_infty_of_ne one_ne_zero, mobiusExt_coe hn]
    simp [mobiusFn, hz]
  · rw [mobiusExt_coe hz]
    by_cases hn : a * z + b = 0
    · rw [mobiusExt_coe_of_eq_zero hn, mobiusExt_coe_of_eq_zero]
      simp [mobiusFn, hn]
    · rw [mobiusExt_coe, mobiusExt_coe hn]
      · congr 1
        simp only [mobiusFn, zero_mul, zero_add, add_zero, one_mul, one_div_div]
      · simp only [mobiusFn, one_mul, add_zero]
        exact div_ne_zero hn hz

/-- The value at `∞` is the value at `0` of the column-swapped transformation. -/
theorem k22_t_mobiusExt_infty_eq (a b c d : ℂ) :
    mobiusExt a b c d extInf = mobiusExt b a d c ((0 : ℂ) : ExtPlane) := by
  by_cases hc : c = 0
  · rw [mobiusExt_infty_of_eq hc, mobiusExt_coe_of_eq_zero (by rw [hc]; ring)]
  · rw [mobiusExt_infty_of_ne hc, mobiusExt_coe (by rw [mul_zero, zero_add]; exact hc)]
    simp [mobiusFn]

/-- Finite points: `mobiusExt` at a fixed `z` depends continuously on the coefficients at a
nondegenerate limit. -/
theorem k22_t_tendsto_mobiusExt_coe {α : Type*} {l : Filter α} {a b c d : α → ℂ}
    {a₀ b₀ c₀ d₀ : ℂ} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀)) (hdet : a₀ * d₀ - b₀ * c₀ ≠ 0)
    (z : ℂ) :
    Tendsto (fun n => mobiusExt (a n) (b n) (c n) (d n) (z : ExtPlane)) l
      (𝓝 (mobiusExt a₀ b₀ c₀ d₀ (z : ExtPlane))) := by
  by_cases hz : c₀ * z + d₀ = 0
  · have hn : a₀ * z + b₀ ≠ 0 := by
      intro hab
      apply hdet
      linear_combination a₀ * hz - c₀ * hab
    have hsw := k22_t_tendsto_mobiusExt_coe_of_ne hc hd ha hb hn
    have hdetl : Tendsto (fun n => a n * d n - b n * c n) l (𝓝 (a₀ * d₀ - b₀ * c₀)) :=
      (ha.mul hd).sub (hb.mul hc)
    have hev : ∀ᶠ n in l, a n * d n - b n * c n ≠ 0 := hdetl.eventually_ne hdet
    have h1 : Tendsto (fun n => mobiusExt 0 1 1 0 (mobiusExt (a n) (b n) (c n) (d n) (z : ExtPlane)))
        l (𝓝 (mobiusExt 0 1 1 0 (mobiusExt a₀ b₀ c₀ d₀ (z : ExtPlane)))) := by
      rw [k22_t_inv_mobiusExt_coe hdet]
      refine hsw.congr' ?_
      filter_upwards [hev] with n hn
      exact (k22_t_inv_mobiusExt_coe hn z).symm
    have hI : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
    have hI' : (0 : ℂ) * 0 - (-1) * (-1) ≠ 0 := by norm_num
    have h2 := ((continuous_mobiusExt hI').tendsto _).comp h1
    simpa only [Function.comp_def, mobiusExt_inv_apply hI] using h2
  · exact k22_t_tendsto_mobiusExt_coe_of_ne ha hb hc hd hz

/-- `mobiusExt` at a fixed point depends continuously on the coefficients at a nondegenerate
limit. -/
theorem k22_t_tendsto_mobiusExt {α : Type*} {l : Filter α} {a b c d : α → ℂ}
    {a₀ b₀ c₀ d₀ : ℂ} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀)) (hdet : a₀ * d₀ - b₀ * c₀ ≠ 0)
    (w : ExtPlane) :
    Tendsto (fun n => mobiusExt (a n) (b n) (c n) (d n) w) l (𝓝 (mobiusExt a₀ b₀ c₀ d₀ w)) := by
  induction w using OnePoint.rec with
  | infty =>
    simp only [k22_t_mobiusExt_infty_eq]
    exact k22_t_tendsto_mobiusExt_coe hb ha hd hc
      (by intro h; apply hdet; linear_combination -h) 0
  | coe z => exact k22_t_tendsto_mobiusExt_coe ha hb hc hd hdet z

/-- `ℂ̄` is first countable (it is homeomorphic to the unit sphere of `ℝ³`). -/
theorem k22_t_firstCountable : FirstCountableTopology ExtPlane := by
  have h : Module.finrank ℝ ℂ + 1 = Fintype.card (Fin 3) := by
    simp [Complex.finrank_real_complex]
  exact (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) h).isEmbedding.firstCountableTopology

/-- The limits of the orbit of the single point `z₀` along injective sequences in `Γ`. -/
def k22_t_orbitLim (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (z₀ : ExtPlane) :
    Set ExtPlane :=
  {p | ∃ γs : ℕ → Γ, Function.Injective γs ∧
    Tendsto (fun n => mobiusSL (γs n) z₀) atTop (𝓝 p)}

/-- The orbit-limit set of a single point lies in the limit set. -/
theorem k22_t_orbitLim_subset {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (z₀ : ExtPlane) : k22_t_orbitLim Γ z₀ ⊆ limitSet Γ :=
  fun _ hp => ⟨z₀, hp⟩

/-- The orbit-limit set of a point is `Γ`-invariant. -/
theorem k22_t_orbitLim_smul {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℂ} (hg : g ∈ Γ) {z₀ p : ExtPlane}
    (hp : p ∈ k22_t_orbitLim Γ z₀) : mobiusSL g p ∈ k22_t_orbitLim Γ z₀ := by
  obtain ⟨γs, hinj, hlim⟩ := hp
  refine ⟨fun n => ⟨g * γs n, Γ.mul_mem hg (γs n).2⟩, ?_, ?_⟩
  · intro m n hmn
    apply hinj
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hmn)
  · have h2 := ((k22_t_continuous g).tendsto p).comp hlim
    refine h2.congr fun n => ?_
    exact (k22_t_mobiusSL_mul g (γs n) z₀).symm

/-- The limit set is `Γ`-invariant. -/
theorem k22_t_limitSet_smul {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℂ} (hg : g ∈ Γ) {p : ExtPlane}
    (hp : p ∈ limitSet Γ) : mobiusSL g p ∈ limitSet Γ := by
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, k22_t_orbitLim_smul hg hq⟩

/-- The complement of the limit set is `Γ`-invariant. -/
theorem k22_t_mem_limitSet_of_smul {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℂ} (hg : g ∈ Γ) {p : ExtPlane}
    (hp : mobiusSL g p ∈ limitSet Γ) : p ∈ limitSet Γ := by
  have h := k22_t_limitSet_smul (Γ.inv_mem hg) hp
  rwa [k22_t_mobiusSL_inv_apply] at h

/-- Discreteness: if `Λ(Γ)ᶜ ≠ ∅`, every injective sequence in `Γ` has entries tending to `∞`.
(A bounded injective subsequence would converge to some `g ∈ SL(2, ℂ)`, making every `g w` a
limit point, i.e. `Λ(Γ) = ℂ̄`.) -/
theorem k22_t_tendsto_norm {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hΩ : (limitSet Γ)ᶜ.Nonempty) {γs : ℕ → Γ} (hinj : Function.Injective γs) :
    Tendsto (fun n => ‖(γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 0‖ +
      ‖(γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 1‖ +
      ‖(γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 0‖ +
      ‖(γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 1‖) atTop atTop := by
  by_contra hcon
  rw [Filter.tendsto_atTop] at hcon
  simp only [not_forall, Filter.not_eventually, not_le] at hcon
  obtain ⟨M, hM⟩ := hcon
  let v : ℕ → (Fin 2 → Fin 2 → ℂ) := fun n i j => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) i j
  have hfreq : ∃ᶠ n in atTop, v n ∈ closedBall (0 : Fin 2 → Fin 2 → ℂ) M := by
    refine hM.mono fun n hn => ?_
    have h00 := norm_nonneg ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 0)
    have h01 := norm_nonneg ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 1)
    have h10 := norm_nonneg ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 0)
    have h11 := norm_nonneg ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 1)
    have hM0 : 0 ≤ M := by linarith
    have hij : ∀ i j, ‖v n i j‖ ≤ M := by
      simp only [Fin.forall_fin_two, v]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hM0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM0).2 fun j => hij i j
  obtain ⟨G, -, φ, hφ, hG⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
  have hent : ∀ i j, Tendsto (fun n => (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ) i j)
      atTop (𝓝 (G i j)) := fun i j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hG i) j
  have hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1 := by
    have h1 := ((hent 0 0).mul (hent 1 1)).sub ((hent 0 1).mul (hent 1 0))
    have h2 : (fun n => (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 0 *
        (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 1 -
        (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 1 *
        (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 0) = fun _ => (1 : ℂ) := by
      funext n
      exact k22_t_det _
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hdet' : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hall : ∀ w : ExtPlane, mobiusExt (G 0 0) (G 0 1) (G 1 0) (G 1 1) w ∈ limitSet Γ := by
    intro w
    exact ⟨w, fun n => γs (φ n), hinj.comp hφ.injective,
      k22_t_tendsto_mobiusExt (hent 0 0) (hent 0 1) (hent 1 0) (hent 1 1) hdet' w⟩
  obtain ⟨z₀, hz₀⟩ := hΩ
  apply hz₀
  have := hall ((mobiusHomeomorph _ _ _ _ hdet').symm z₀)
  rwa [← mobiusHomeomorph_apply hdet', Homeomorph.apply_symm_apply] at this

/-- A sequence with infinite range has an injective reindexing `δ ∘ ψ` with `ψ → ∞`. -/
theorem k22_t_injective_reindex {β : Type*} (δ : ℕ → β) (hδ : (range δ).Infinite) :
    ∃ ψ : ℕ → ℕ, Function.Injective (δ ∘ ψ) ∧ Tendsto ψ atTop atTop := by
  let e := hδ.natEmbedding
  have hmem : ∀ j, ∃ n, δ n = (e j : β) := fun j => (e j).2
  choose ψ hψ using hmem
  have hinj : Function.Injective (δ ∘ ψ) := by
    intro i j hij
    have h' : (e i : β) = e j := by
      simp only [Function.comp_apply, hψ] at hij
      exact hij
    exact e.injective (Subtype.ext h')
  exact ⟨ψ, hinj, hinj.of_comp.nat_tendsto_atTop⟩

/-- The orbit-limit set of a point is closed (diagonal argument; needs discreteness). -/
theorem k22_t_orbitLim_closed {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hΩ : (limitSet Γ)ᶜ.Nonempty) (z₀ : ExtPlane) : IsClosed (k22_t_orbitLim Γ z₀) := by
  have := k22_t_firstCountable
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨U, hU⟩ := (𝓝 p).exists_antitone_basis
  have hchoice : ∀ k : ℕ, ∃ g : Γ, (k : ℝ) ≤ ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 0‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 1‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 0‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 1‖ ∧ mobiusSL g z₀ ∈ U k := by
    intro k
    have hopen : interior (U k) ∈ 𝓝 p := interior_mem_nhds.2 (hU.mem k)
    obtain ⟨a, ha, haA⟩ := mem_closure_iff_nhds.1 hp _ hopen
    obtain ⟨γs, hinj, hlim⟩ := haA
    have h1 : ∀ᶠ n in atTop, mobiusSL (γs n) z₀ ∈ interior (U k) :=
      hlim (isOpen_interior.mem_nhds ha)
    have h2 := (k22_t_tendsto_norm hΩ hinj).eventually_ge_atTop (k : ℝ)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    exact ⟨γs n, hn2, interior_subset hn1⟩
  choose δ hδN hδU using hchoice
  have hrange : (range δ).Infinite := by
    intro hfin
    obtain ⟨C, hC⟩ := (hfin.image fun g : Γ =>
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 0‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 0 1‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 0‖ +
      ‖(g : Matrix.SpecialLinearGroup (Fin 2) ℂ) 1 1‖).bddAbove
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have := hC (mem_image_of_mem _ (mem_range_self k))
    linarith [hδN k]
  obtain ⟨ψ, hψinj, hψ⟩ := k22_t_injective_reindex δ hrange
  exact ⟨δ ∘ ψ, hψinj, (hU.tendsto hδU).comp hψ⟩

/-- Convergence along an injective sequence in `Γ` with `Λ(Γ)ᶜ ≠ ∅`: a subsequence converges
pointwise to `a` off `b`, its inverses to `b` off `a`, and `a, b ∈ Λ(Γ)`. -/
theorem k22_t_conv {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hΩ : (limitSet Γ)ᶜ.Nonempty) {γs : ℕ → Γ} (hinj : Function.Injective γs) :
    ∃ (φ : ℕ → ℕ) (a b : ExtPlane), StrictMono φ ∧ a ∈ limitSet Γ ∧ b ∈ limitSet Γ ∧
      (∀ w, w ≠ b → Tendsto (fun n => mobiusSL (γs (φ n)) w) atTop (𝓝 a)) ∧
      (∀ w, w ≠ a → Tendsto (fun n => mobiusSL ((γs (φ n))⁻¹ : Γ) w) atTop (𝓝 b)) := by
  obtain ⟨φ, a, b, hφ, hA, hB⟩ :=
    k22_convergence (fun n => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ))
      (k22_t_tendsto_norm hΩ hinj)
  have hA' : ∀ w, w ≠ b → Tendsto (fun n => mobiusSL (γs (φ n)) w) atTop (𝓝 a) := by
    intro w hw
    rw [tendsto_def]
    intro U hU
    have h := hA {w} isCompact_singleton (fun h => hw (mem_singleton_iff.1 h).symm) U hU
    filter_upwards [h] with n hn
    exact hn (mem_image_of_mem _ (mem_singleton w))
  have hB' : ∀ w, w ≠ a → Tendsto (fun n => mobiusSL ((γs (φ n))⁻¹ : Γ) w) atTop (𝓝 b) := by
    intro w hw
    rw [tendsto_def]
    intro U hU
    have h := hB {w} isCompact_singleton (fun h => hw (mem_singleton_iff.1 h).symm) U hU
    filter_upwards [h] with n hn
    exact hn (mem_image_of_mem _ (mem_singleton w))
  have hinjφ : Function.Injective (fun n => γs (φ n)) := hinj.comp hφ.injective
  have hinjinv : Function.Injective (fun n => (γs (φ n))⁻¹) :=
    fun m n h => hinjφ (inv_injective h)
  obtain ⟨wb, hwb⟩ := exists_ne b
  obtain ⟨wa, hwa⟩ := exists_ne a
  exact ⟨φ, a, b, hφ, ⟨wb, _, hinjφ, hA' wb hwb⟩, ⟨wa, _, hinjinv, hB' wa hwa⟩, hA', hB'⟩

/-- Every limit point is a limit of the orbit of any fixed ordinary point `z₀`. -/
theorem k22_t_limitSet_subset_orbitLim {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {z₀ : ExtPlane} (hz₀ : z₀ ∉ limitSet Γ) : limitSet Γ ⊆ k22_t_orbitLim Γ z₀ := by
  have hΩ : (limitSet Γ)ᶜ.Nonempty := ⟨z₀, hz₀⟩
  rintro p ⟨q, γs, hinj, hlim⟩
  obtain ⟨φ, a, b, hφ, ha, hb, hA, hB⟩ := k22_t_conv hΩ hinj
  have hza : z₀ ≠ a := fun h => hz₀ (h ▸ ha)
  have hzb : z₀ ≠ b := fun h => hz₀ (h ▸ hb)
  have hinjφ : Function.Injective (fun n => γs (φ n)) := hinj.comp hφ.injective
  have hinjinv : Function.Injective (fun n => (γs (φ n))⁻¹) :=
    fun m n h => hinjφ (inv_injective h)
  have hbO : b ∈ k22_t_orbitLim Γ z₀ := ⟨_, hinjinv, hB z₀ hza⟩
  have hsub : Tendsto (fun n => mobiusSL (γs (φ n)) q) atTop (𝓝 p) :=
    hlim.comp hφ.tendsto_atTop
  by_cases hqb : q = b
  · rw [hqb] at hsub
    exact (k22_t_orbitLim_closed hΩ z₀).mem_of_tendsto hsub
      (Eventually.of_forall fun n => k22_t_orbitLim_smul (γs (φ n)).2 hbO)
  · have hpa : p = a := tendsto_nhds_unique hsub (hA q hqb)
    rw [hpa]
    exact ⟨_, hinjφ, hA z₀ hzb⟩

/-- §22.6: a Klein group has a nowhere dense perfect limit set. -/
theorem kleinGroup_limitSet_perfect {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hΓ : IsKleinGroup Γ) : Perfect (limitSet Γ) ∧ interior (closure (limitSet Γ)) = ∅ := by
  obtain ⟨⟨z₀, hz₀⟩, hcard, -⟩ := hΓ
  have hΩ : (limitSet Γ)ᶜ.Nonempty := ⟨z₀, hz₀⟩
  have heq : limitSet Γ = k22_t_orbitLim Γ z₀ :=
    (k22_t_limitSet_subset_orbitLim hz₀).antisymm (k22_t_orbitLim_subset z₀)
  have hclosed : IsClosed (limitSet Γ) := heq ▸ k22_t_orbitLim_closed hΩ z₀
  refine ⟨⟨hclosed, ?_⟩, ?_⟩
  · intro p hp
    rw [accPt_iff_nhds]
    intro U hU
    rw [heq] at hp
    obtain ⟨γs, hinj, hlim⟩ := hp
    obtain ⟨φ, a, b, hφ, -, hb, hA, -⟩ := k22_t_conv hΩ hinj
    have hzb : z₀ ≠ b := fun h => hz₀ (h ▸ hb)
    have hpa : p = a := tendsto_nhds_unique (hlim.comp hφ.tendsto_atTop) (hA z₀ hzb)
    have h2 : 1 < (limitSet Γ \ {b}).encard := by
      by_contra hle
      rw [not_lt] at hle
      have h3 := Set.encard_sdiff_singleton_add_one hb
      have h4 : (limitSet Γ \ {b}).encard + 1 ≤ 1 + 1 := add_le_add hle le_rfl
      rw [h3, one_add_one_eq_two] at h4
      exact absurd hcard (not_lt.2 h4)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := Set.one_lt_encard_iff.1 h2
    have e1 := hA y₁ hy₁.2
    have e2 := hA y₂ hy₂.2
    rw [← hpa] at e1 e2
    obtain ⟨n, hn1, hn2⟩ := ((e1.eventually_mem hU).and (e2.eventually_mem hU)).exists
    by_cases h : mobiusSL (γs (φ n)) y₁ = p
    · refine ⟨mobiusSL (γs (φ n)) y₂, ⟨hn2, k22_t_limitSet_smul (γs (φ n)).2 hy₂.1⟩, ?_⟩
      intro h'
      exact hne (k22_t_injective _ (h.trans h'.symm))
    · exact ⟨mobiusSL (γs (φ n)) y₁, ⟨hn1, k22_t_limitSet_smul (γs (φ n)).2 hy₁.1⟩, h⟩
  · rw [hclosed.closure_eq]
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hxΛ : x ∈ limitSet Γ := interior_subset hx
    rw [heq] at hxΛ
    obtain ⟨γs, hinj, hlim⟩ := hxΛ
    obtain ⟨n, hn⟩ := (hlim.eventually_mem (isOpen_interior.mem_nhds hx)).exists
    exact hz₀ (k22_t_mem_limitSet_of_smul (γs n).2 (interior_subset hn))

end LiZhongQC
