import References.Lehto1987.Ch04.S01_ManifoldsAndTheirStructures

/-!
# Lehto, Chapter IV §2: Topology of covering surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §2 (`full.md`
P1:4918–5071).

Conventions (see §1; decision B0.7). Surfaces are second countable connected Hausdorff charted spaces over `ℂ`.
Lehto's covering notions are his own:
- a *smooth covering surface* `(W, f)` is a local homeomorphism `f : W → S` (Mathlib `IsLocalHomeomorph`);
- *unlimited* means that every path lifts (`IsUnlimitedCovering`);
- a *covering surface* in general is branched (`IsCoveringSurface`).

They are not Mathlib's `IsCoveringMap`. The covering group of `W` over `S` is Mathlib's `deck f`, a subgroup of
`W ≃ₜ W` acting on `W`; the quotient `W/G` by a subgroup `G` of `W ≃ₜ W` is `MulAction.orbitRel.Quotient G W`, with
the quotient topology. A lift of a path `γ` is a path `γ′` with `f ∘ γ′ = γ`, written inline. The fundamental group
`F_a` is Mathlib's `FundamentalGroup S a`.

* Definition (smooth covering surface, projection, §2.1) — exists: `IsLocalHomeomorph`
* Definition (lift of a path, §2.1) — omitted: written inline as `f ∘ γ′ = γ` (U−)
* Unlabelled (§2.1, P1:4926): lifts from a fixed point are unique — omitted: quoted (Ahlfors–Sario), not cited
* Definition (unlimited covering surface, §2.1) — `IsUnlimitedCovering`
* Unlabelled (§2.1, P1:4930): an unlimited covering is surjective with fibres of equal cardinality — omitted: U−
* Theorem 2.1 (§2.1, Monodromy Theorem) — `thm4_2_1`
* Unlabelled (§2.1, P1:4938–4940): an unlimited covering of a simply connected surface is a homeomorphism —
  omitted: not cited
* Definition (the subgroup `Γ_{a′}` of `F_a` determined by `(W, f, a′)`, §2.2) — `coveringSubgroup`
* Unlabelled (§2.2, P1:4946): independence of the base points up to isomorphism and conjugation — omitted: U−
* Definition (normal covering surface, §2.2) — `IsNormalCovering`
* Unlabelled (§2.2, P1:4952): the fundamental group of `W` is isomorphic to `Γ_{a′}` — `para4_2_2_a`
* Definition (universal covering surface, §2.2) — `IsUniversalCoveringSurface`
* Unlabelled (§2.2, P1:4956–4964): every surface has a universal covering surface; it is simply connected and
  normal — `para4_2_2_b`
* Definition (covering surface, branched covering surface, §2.3) — `IsCoveringSurface`, `IsBranchedCovering`
* Lemma 2.1 (§2.3) — `lemma4_2_1`
* Formula (2.1) (§2.3) — `lemma4_2_1` (the conclusion of Lemma 2.1)
* Unlabelled (§2.3, P1:4986–4988): the converse of Lemma 2.1, Stoilov's characterizations — omitted: remarks, not
  cited
* Definition (cover transformation, covering group, §2.4) — exists: `deck`
* Definition (transitive covering group, §2.4) — `IsTransitiveCoveringGroup`
* Theorem 2.2 (§2.4) — `thm4_2_2`
* Formula (2.2) (§2.4) — `thm4_2_2` (the homeomorphism of Theorem 2.2)
* Unlabelled (§2.4, P1:5012): every point of `W` has a neighbourhood without equivalent points — `para4_2_4_a`
* Unlabelled (§2.4, P1:5016): a cover transformation other than the identity has no fixed points — `para4_2_4_b`
* Theorem 2.3 (§2.4) — `thm4_2_3`
* Theorem 2.4 (§2.4) — `thm4_2_4`
* Definition (properly discontinuous group, §2.5) — exists: `ProperlyDiscontinuousSMul`
* Definition (limit point of a group, §2.5) — `IsGroupLimitPoint`
* Unlabelled (§2.5, P1:5042): a properly discontinuous group has no limit points — `para4_2_5_a`
* Unlabelled (§2.5, P1:5044): a fixed point free properly discontinuous group has neighbourhoods without equivalent
  points — `para4_2_5_b`
* Theorem 2.5 (§2.5) — `thm4_2_5`
* Theorem 2.6 (§2.5) — `thm4_2_6_a`, `thm4_2_6_b`, `thm4_2_6_c`
-/

open Complex Set Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace Lehto1987

universe u v

/-! ## §2.1 Lifting of paths -/

/-- **Definition** (unlimited covering surface, Ch. IV §2.1): a smooth covering surface `(W, f)` (`f` a local
homeomorphism) such that every path of `S` has a lift from each point lying over its initial point. -/
def IsUnlimitedCovering {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) : Prop :=
  IsLocalHomeomorph f ∧ ∀ (x y : S) (γ : Path x y) (a : W), f a = x →
    ∃ γ' : C(unitInterval, W), γ' 0 = a ∧ ∀ t, f (γ' t) = γ t

/-- **Theorem 2.1** (Ch. IV §2.1, Monodromy Theorem). Let `(W, f)` be an unlimited covering surface of a surface `S`,
and `γ₀`, `γ₁` homotopic paths on `S`. Then the lifts of `γ₀` and `γ₁` from the same initial point have the same
terminal point, and they are homotopic.
Modelling: the lifts are paths `Γ₀`, `Γ₁` of `W` from `a`; near miss `LiZhongQC.thm22_1_monodromy` (for Mathlib
covering maps). -/
theorem thm4_2_1 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsUnlimitedCovering f) {x y : S}
    {γ₀ γ₁ : Path x y} (hγ : γ₀.Homotopic γ₁) {a b₀ b₁ : W} {Γ₀ : Path a b₀} {Γ₁ : Path a b₁}
    (h₀ : ∀ t, f (Γ₀ t) = γ₀ t) (h₁ : ∀ t, f (Γ₁ t) = γ₁ t) :
    ∃ h : b₀ = b₁, (Γ₀.cast rfl h.symm).Homotopic Γ₁ := by
  sorry

/-! ## §2.2 Covering surfaces and the fundamental group -/

/-- **Definition** (the subgroup `Γ_{a′}` determined by `(W, f, a′)`, Ch. IV §2.2): the classes `[γ]` of closed
paths of `S` from `a = f(a′)` whose lift from `a′` is closed.
Modelling: a set of elements of `FundamentalGroup S (f a′)` (that it is a subgroup is part of `para4_2_2_a`). -/
def coveringSubgroup {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) (a' : W) :
    Set (FundamentalGroup S (f a')) :=
  {g | ∃ γ : Path (f a') (f a'), FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = g ∧
    ∃ Γ : Path a' a', ∀ t, f (Γ t) = γ t}

/-- **Definition** (normal covering surface, Ch. IV §2.2): an unlimited covering surface for which the subgroups
`Γ_{a′}` are normal. -/
def IsNormalCovering {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) : Prop :=
  IsUnlimitedCovering f ∧ ∀ a' : W, ∀ g ∈ coveringSubgroup f a', ∀ h : FundamentalGroup S (f a'),
    h * g * h⁻¹ ∈ coveringSubgroup f a'

/-- **Unlabelled** (Ch. IV §2.2, P1:4952). Let `(W, f)` be an unlimited covering surface of `S`. Then the fundamental
group of `W` is isomorphic to the subgroup `Γ_{a′}` of `F_{f(a′)}`, by `[γ] ↦ [f ∘ γ]`.
Modelling: an injective homomorphism `π₁(W, a′) → π₁(S, f(a′))` with image `Γ_{a′}` (so `Γ_{a′}` is a subgroup). -/
theorem para4_2_2_a {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsUnlimitedCovering f) (a' : W) :
    ∃ φ : FundamentalGroup W a' →* FundamentalGroup S (f a'), Function.Injective φ ∧
      Set.range φ = coveringSubgroup f a' := by
  sorry

/-- **Definition** (universal covering surface, Ch. IV §2.2): an unlimited covering surface which determines the
trivial subgroup of the fundamental group. -/
def IsUniversalCoveringSurface {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) :
    Prop :=
  IsUnlimitedCovering f ∧ ∀ a' : W, coveringSubgroup f a' = {1}

/-- **Unlabelled** (Ch. IV §2.2, P1:4956–4964). Every surface possesses universal covering surfaces; a universal
covering surface is simply connected and normal.
Modelling: a surface `W` in the universe of `S`. -/
theorem para4_2_2_b (S : Type u) [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace ℂ W), T2Space W ∧ SecondCountableTopology W ∧
      ConnectedSpace W ∧ SimplyConnectedSpace W ∧ ∃ f : W → S, IsUniversalCoveringSurface f ∧ IsNormalCovering f := by
  sorry

/-! ## §2.3 Branched covering surfaces -/

/-- **Definition** (covering surface, Ch. IV §2.3): `f : W → S` is continuous and every point `p ∈ W` has a
neighbourhood `U` such that `(U ∖ {p}, f|U ∖ {p})` is a smooth covering surface of `S ∖ {f(p)}`.
Modelling: `U` is open and `U ∖ {p}` connected (a surface); `f` is a local homeomorphism on `U ∖ {p}` with values
in `S ∖ {f(p)}`. -/
def IsCoveringSurface {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) : Prop :=
  Continuous f ∧ ∀ p : W, ∃ U : Set W, IsOpen U ∧ p ∈ U ∧ IsConnected (U \ {p}) ∧
    MapsTo f (U \ {p}) {f p}ᶜ ∧ IsLocalHomeomorphOn f (U \ {p})

/-- **Definition** (branched covering surface, Ch. IV §2.3): a covering surface which is not smooth. -/
def IsBranchedCovering {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] (f : W → S) : Prop :=
  IsCoveringSurface f ∧ ¬ IsLocalHomeomorph f

/-- **Lemma 2.1** (Ch. IV §2.3). Let `(W, f)` be a covering surface of `S`. For every `p ∈ W` there are parameter
discs `U ∋ p` and `f(U)`, with local parameters `k` and `h` normalized by `k(p) = h(f(p)) = 0`, such that
`h ∘ f = kⁿ` in `U` (2.1), `n` a natural number.
Modelling: the local parameters are partial homeomorphisms to `ℂ` onto discs about `0`; `n ≥ 1`. -/
theorem lemma4_2_1 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsCoveringSurface f) (p : W) :
    ∃ (n : ℕ) (k : OpenPartialHomeomorph W ℂ) (h : OpenPartialHomeomorph S ℂ) (r s : ℝ), 1 ≤ n ∧
      p ∈ k.source ∧ k p = 0 ∧ k.target = Metric.ball 0 r ∧ f p ∈ h.source ∧ h (f p) = 0 ∧
      h.target = Metric.ball 0 s ∧ f '' k.source = h.source ∧ ∀ q ∈ k.source, h (f q) = k q ^ n := by
  sorry

/-! ## §2.4 Covering groups -/

/-- **Definition** (transitive covering group, Ch. IV §2.4): any two points of `W` over the same point of `S` are
equivalent under the covering group `deck f`. -/
def IsTransitiveCoveringGroup {W : Type u} {S : Type v} [TopologicalSpace W] (f : W → S) : Prop :=
  ∀ p q : W, f p = f q → ∃ g ∈ deck f, g p = q

/-- **Theorem 2.2** (Ch. IV §2.4). Let `(W, f)` be a smooth covering surface of `S`. If `f` is surjective and the
covering group `G` of `W` over `S` is transitive, then `W/G` and `S` are homeomorphic, by `[p] ↦ f(p)` (2.2). -/
theorem thm4_2_2 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsLocalHomeomorph f) (hs : Function.Surjective f)
    (ht : IsTransitiveCoveringGroup f) :
    ∃ e : MulAction.orbitRel.Quotient (deck f) W ≃ₜ S,
      ∀ p : W, e (Quotient.mk (MulAction.orbitRel (deck f) W) p) = f p := by
  sorry

/-- **Unlabelled** (Ch. IV §2.4, P1:5012). Each point of a smooth covering surface `W` has a neighbourhood in which no
two points are equivalent under the covering group. -/
theorem para4_2_4_a {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsLocalHomeomorph f) (p : W) :
    ∃ U ∈ 𝓝 p, ∀ q ∈ U, ∀ g ∈ deck f, g q ∈ U → g q = q := by
  sorry

/-- **Unlabelled** (Ch. IV §2.4, P1:5016). Except for the identity, a cover transformation of a smooth covering
surface has no fixed points. -/
theorem para4_2_4_b {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsLocalHomeomorph f) {g : W ≃ₜ W} (hg : g ∈ deck f)
    {q : W} (hq : g q = q) : g = 1 := by
  sorry

/-- **Theorem 2.3** (Ch. IV §2.4). The covering group of a universal covering surface `W` over a surface `S` is
transitive. -/
theorem thm4_2_3 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsUniversalCoveringSurface f) :
    IsTransitiveCoveringGroup f := by
  sorry

/-- **Theorem 2.4** (Ch. IV §2.4). The covering group of a universal covering surface of `S` is isomorphic to the
fundamental group of `S`. -/
theorem thm4_2_4 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsUniversalCoveringSurface f) (a : W) :
    Nonempty (deck f ≃* FundamentalGroup S (f a)) := by
  sorry

/-! ## §2.5 Properly discontinuous groups -/

/-- **Definition** (limit point of a group, Ch. IV §2.5): `p` is a limit point of `G` if `p = lim gₙ(q)` for distinct
`gₙ ∈ G` and some `q ∈ W`. -/
def IsGroupLimitPoint {W : Type u} [TopologicalSpace W] (G : Subgroup (W ≃ₜ W)) (p : W) : Prop :=
  ∃ (q : W) (gs : ℕ → G), Function.Injective gs ∧ Tendsto (fun n => ((gs n : W ≃ₜ W) : W → W) q) atTop (𝓝 p)

/-- **Unlabelled** (Ch. IV §2.5, P1:5042). A properly discontinuous group has no limit points. -/
theorem para4_2_5_a {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W] (p : W) :
    ¬ IsGroupLimitPoint G p := by
  sorry

/-- **Unlabelled** (Ch. IV §2.5, P1:5044). A fixed point free properly discontinuous group `G` has the property that
every point of `W` has a neighbourhood in which no two points are equivalent modulo `G`. -/
theorem para4_2_5_b {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hfree : ∀ g : G, ∀ q : W, g • q = q → g = 1) (p : W) :
    ∃ U ∈ 𝓝 p, ∀ q ∈ U, ∀ g : G, g • q ∈ U → g = 1 := by
  sorry

/-- **Theorem 2.5** (Ch. IV §2.5). A transitive covering group is properly discontinuous.
Modelling: the covering group of a smooth covering surface `(W, f)`. -/
theorem thm4_2_5 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [ConnectedSpace S] [ChartedSpace ℂ S] {f : W → S} (hf : IsLocalHomeomorph f)
    (ht : IsTransitiveCoveringGroup f) : ProperlyDiscontinuousSMul (deck f) W := by
  sorry

/-- **Theorem 2.6** (Ch. IV §2.5), part 1. Let `W` be a surface, `G` a properly discontinuous fixed point free group
of homeomorphisms of `W` onto itself. Then `W/G` is a surface.
Modelling: Hausdorff, second countable, connected and locally homeomorphic to open subsets of `ℂ`. -/
theorem thm4_2_6_a {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hfree : ∀ g : G, ∀ q : W, g • q = q → g = 1) :
    T2Space (MulAction.orbitRel.Quotient G W) ∧ SecondCountableTopology (MulAction.orbitRel.Quotient G W) ∧
      ConnectedSpace (MulAction.orbitRel.Quotient G W) ∧
      ∀ x : MulAction.orbitRel.Quotient G W, ∃ e : OpenPartialHomeomorph (MulAction.orbitRel.Quotient G W) ℂ,
        x ∈ e.source := by
  sorry

/-- **Theorem 2.6** (Ch. IV §2.5), part 2. In the situation of `thm4_2_6_a`, `(W, f)` is an unlimited covering
surface of `W/G`, `f` the canonical projection. -/
theorem thm4_2_6_b {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hfree : ∀ g : G, ∀ q : W, g • q = q → g = 1) :
    IsUnlimitedCovering (Quotient.mk (MulAction.orbitRel G W)) := by
  sorry

/-- **Theorem 2.6** (Ch. IV §2.5), part 3. In the situation of `thm4_2_6_a`, `G` is the (transitive) covering group of
`W` over `W/G`. -/
theorem thm4_2_6_c {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hfree : ∀ g : G, ∀ q : W, g • q = q → g = 1) :
    deck (Quotient.mk (MulAction.orbitRel G W)) = G ∧
      IsTransitiveCoveringGroup (Quotient.mk (MulAction.orbitRel G W)) := by
  sorry

end Lehto1987
