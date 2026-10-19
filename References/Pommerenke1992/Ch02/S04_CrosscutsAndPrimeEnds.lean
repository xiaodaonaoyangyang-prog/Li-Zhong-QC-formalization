import References.Pommerenke1992.Ch02.S03_CutPointsAndJordanDomains

/-!
# Pommerenke 1992, Ch. 2 §2.4 Crosscuts and Prime Ends

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1286–1431.

* Definition (crosscut, §2.4) — `IsCrosscut`
* Proposition 2.12 — `prop2_12`
* Proposition 2.13 — `prop2_13`
* Proposition 2.14 — `prop2_14`
* Definition (null-chain, §2.4; the domains `V_n`) — `IsNullChain`, `nullChainDomain`
* Unlabelled (§2.4, l. 1360: `V_n` is the unique component of `G ∖ C_n` missing `C_0`, and (iii) can be written as
  (2.4.7); cited as (2.4.7)) — `eq2_4_7`
* Definition (equivalence of null-chains, (2.4.8)) — `NullChainEquiv`
* Unlabelled (§2.4, l. 1380: the equivalence (2.4.8) expressed by (2.4.9); cited as (2.4.9)) — `eq2_4_9`
* Unlabelled (§2.4, l. 1386: this defines an equivalence relation between null-chains, on which the definition of
  prime ends rests) — `nullChainEquiv_equivalence`
* Definition (prime ends `P(G)`, §2.4) — `primeEnds`
* Theorem 2.15 (prime end theorem) — `thm2_15`

The correspondence of Theorem 2.15 is named by the helper predicate `IsPrimeEndCorrespondence`, which §2.5–2.6 use for
the book's `f̂`.

Not items (DESIGN §3): the remark on crosscuts of non-simply-connected domains (quoted, l. 1298); the consequence
after Proposition 2.13 on points of the other component (not cited); "the preimage of a crosscut of `G` is a crosscut
of `𝔻`" (l. 1334, immediate from Proposition 2.14, and later cited as "by Proposition 2.14"); "if `∂G` is bounded,
`diam#` can be replaced by the euclidean diameter" (l. 1358, a remark on the definition); "the prime ends of `𝔻`
correspond to the points of `𝕋`" (immediate); the remark on alternative definitions of prime ends.

**Standing assumption** (l. 1288): simply connected domains `G ⊆ Ĉ` (`LehtoVirtanen1973.IsSimplyConnectedDomain`), with
the spherical (chordal) metric. A conformal map `f` of `𝔻` onto `G` is `LehtoVirtanen1973.IsConformalMap f (toExt 𝔻)`
with `f(𝔻) = G`, and `f⁻¹` is `Function.invFunOn f (toExt 𝔻)`.
The project's `LiZhongQC.IsCrosscut`, `LiZhongQC.IsNullChain`, `LiZhongQC.NullChainEquiv` and `LiZhongQC.PrimeEnd` are
the same notions for bounded domains of `ℂ` (Euclidean diameters); the book's are for `Ĉ`, so they are defined here.
Prime ends are modelled as sets of null-chains (the equivalence classes), not as a quotient type.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve)
open References (IsDomainExt)
open LehtoVirtanen1973 (IsSimplyConnectedDomain IsConformalMap SeparatesIn)

/-- **Definition** (§2.4). A crosscut `C` of `G ⊆ Ĉ`: an open Jordan arc in `G` such that `C̄ = C ∪ {a, b}` with
`a, b ∈ ∂G`; `a = b` is allowed.
Modelling: `C` is an open Jordan arc `φ(t)`, `α < t < β` (1.1.6), whose ends converge, `φ(t) → a` as `t → α` and
`φ(t) → b` as `t → β`; then `C̄ = C ∪ {a, b}`. The book's `a, b` are these end points. The literal reading of
`C̄ = C ∪ {a, b}` for an injective, not necessarily embedded, arc would also admit a "figure 6" whose end accumulates on
`C` itself, and Proposition 2.12 fails for it. -/
def IsCrosscut (G C : Set ExtPlane) : Prop :=
  C ⊆ G ∧ ∃ (φ : ℝ → ExtPlane) (α β : ℝ), α < β ∧ ContinuousOn φ (Ioo α β) ∧ InjOn φ (Ioo α β) ∧
    φ '' Ioo α β = C ∧ ∃ a ∈ frontier G, ∃ b ∈ frontier G,
      Tendsto φ (𝓝[>] α) (𝓝 a) ∧ Tendsto φ (𝓝[<] β) (𝓝 b)

/-- **Proposition 2.12** (§2.4). If `C` is a crosscut of the simply connected domain `G ⊆ Ĉ`, then `G ∖ C` has exactly
two components `G₀` and `G₁`, and these satisfy (2.4.1) `G ∩ ∂G₀ = G ∩ ∂G₁ = C`.
Modelling: "exactly two components" is: `G ∖ C` is the union of the two disjoint domains `G₀, G₁`. -/
theorem prop2_12 {G C : Set ExtPlane} (hG : IsSimplyConnectedDomain G) (hC : IsCrosscut G C) :
    ∃ G₀ G₁ : Set ExtPlane, IsDomainExt G₀ ∧ IsDomainExt G₁ ∧ Disjoint G₀ G₁ ∧ G \ C = G₀ ∪ G₁ ∧
      G ∩ frontier G₀ = C ∧ G ∩ frontier G₁ = C := by
  sorry

/-- **Proposition 2.13** (§2.4). Let `G` be simply connected and `J` a Jordan curve with `G ∩ J ≠ ∅`. If
`z₀ ∈ G ∖ J`, then there are countably many crosscuts `C_k ⊆ J` of `G` such that (2.4.4)
`G = G₀ ∪ ⋃_k G_k ∪ ⋃_k C_k`, where `G₀` is the component of `G ∖ J` containing `z₀` and the `G_k` are disjoint
domains with (2.4.5) `C_k = G ∩ ∂G_k ⊆ G ∩ ∂G₀` for `k ≥ 1`.
Modelling: the crosscuts are indexed by a countable type; "the `G_k` are disjoint domains" is a partition together
with `G₀`, so the `G_k` are also disjoint from `G₀` (the proofs of Proposition 2.14, l. 1340, and Proposition 5.1,
l. 4031, use that `G_k` is the component of `G ∖ C_k` not containing `z₀`).
[CORRECTION] The hypothesis `J ∩ ∂G ≠ ∅` (`hJG`) is added. As printed (only `G ∩ J ≠ ∅`) the statement is false
for `J ⊆ G`: for `G = 𝔻`, `J = {|z| = 1/2}`, `z₀ = 0` no crosscut of `𝔻` lies in `J`. The proof and the uses of the
proposition (the proof of Proposition 5.1, l. 4031) have `J` meeting `∂G`; with `G ∩ J ≠ ∅` this is `J ⊄ G`. -/
theorem prop2_13 {G J : Set ExtPlane} (hG : IsSimplyConnectedDomain G) (hJ : IsJordanCurve J)
    (hGJ : (G ∩ J).Nonempty) (hJG : (J ∩ frontier G).Nonempty) {z₀ : ExtPlane} (hz₀ : z₀ ∈ G \ J) :
    ∃ (ι : Type) (_ : Countable ι) (C Gk : ι → Set ExtPlane),
      (∀ k, IsCrosscut G (C k) ∧ C k ⊆ J) ∧ (∀ k, IsDomainExt (Gk k)) ∧
      Pairwise (fun i j => Disjoint (Gk i) (Gk j)) ∧ (∀ k, Disjoint (connectedComponentIn (G \ J) z₀) (Gk k)) ∧
      G = connectedComponentIn (G \ J) z₀ ∪ (⋃ k, Gk k) ∪ ⋃ k, C k ∧
      ∀ k, C k = G ∩ frontier (Gk k) ∧ C k ⊆ G ∩ frontier (connectedComponentIn (G \ J) z₀) := by
  sorry

/-- **Proposition 2.14** (§2.4). If `f` maps `𝔻` conformally onto `G`, then the preimage of a curve in `G` ending at a
point of `∂G` is a curve in `𝔻` ending at a point of `𝕋`, and curves with distinct endpoints on `∂G` have preimages
with distinct endpoints on `𝕋`. (Given a curve `Γ : w(t), 0 < t ≤ 1` in `G` with `w(t) → ω ∈ ∂G` as `t → 0`, the
preimage `z(t) = f⁻¹(w(t))` has a limit `ζ ∈ 𝕋` as `t → 0`.) -/
theorem prop2_14 {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) :
    (∀ w : ℝ → ExtPlane, ContinuousOn w (Ioc 0 1) → MapsTo w (Ioc 0 1) G →
      ∀ ω ∈ frontier G, Tendsto w (𝓝[>] 0) (𝓝 ω) →
        ∃ ζ ∈ sphere (0 : ℂ) 1,
          Tendsto (Function.invFunOn f (toExt unitDisc) ∘ w) (𝓝[>] 0) (𝓝 (ζ : ExtPlane))) ∧
    ∀ w w' : ℝ → ExtPlane, ContinuousOn w (Ioc 0 1) → MapsTo w (Ioc 0 1) G →
      ContinuousOn w' (Ioc 0 1) → MapsTo w' (Ioc 0 1) G →
      ∀ ω ∈ frontier G, ∀ ω' ∈ frontier G, Tendsto w (𝓝[>] 0) (𝓝 ω) → Tendsto w' (𝓝[>] 0) (𝓝 ω') → ω ≠ ω' →
      ∀ ζ ζ' : ℂ, Tendsto (Function.invFunOn f (toExt unitDisc) ∘ w) (𝓝[>] 0) (𝓝 (ζ : ExtPlane)) →
        Tendsto (Function.invFunOn f (toExt unitDisc) ∘ w') (𝓝[>] 0) (𝓝 (ζ' : ExtPlane)) → ζ ≠ ζ' := by
  sorry

/-- **Definition** (§2.4). `(C_n)` is a null-chain of `G`: (i) `C_n` is a crosscut of `G` (`n = 0, 1, …`);
(ii) `C̄_n ∩ C̄_{n+1} = ∅`; (iii) `C_n` separates `C_0` and `C_{n+1}` (`n = 1, 2, …`); (iv) `diam# C_n → 0`.
Modelling: "separates" is `LehtoVirtanen1973.SeparatesIn G` (the two sets lie in different components of
`G ∖ C_n`); `diam#` is the chordal diameter. -/
def IsNullChain (G : Set ExtPlane) (C : ℕ → Set ExtPlane) : Prop :=
  (∀ n, IsCrosscut G (C n)) ∧ (∀ n, Disjoint (closure (C n)) (closure (C (n + 1)))) ∧
    (∀ n, 1 ≤ n → SeparatesIn G (C n) (C 0) (C (n + 1))) ∧ Tendsto (fun n => chordalDiam (C n)) atTop (𝓝 0)

/-- **Definition** (§2.4, l. 1360). The domain `V_n` of a null-chain: the component of `G ∖ C_n` that does not
contain `C_0`.
Modelling: the union of the components of `G ∖ C_n` disjoint from `C_0`; for a null-chain and `n ≥ 1` there is
exactly one (`eq2_4_7`). The book defines `V_n` for `n ≥ 1` only; the value at `n = 0` (all of `G ∖ C_0`) is not
used by the statements. -/
def nullChainDomain (G : Set ExtPlane) (C : ℕ → Set ExtPlane) (n : ℕ) : Set ExtPlane :=
  {x | x ∈ G \ C n ∧ Disjoint (connectedComponentIn (G \ C n) x) (C 0)}

/-- **Unlabelled claim** (§2.4, l. 1360; cited as (2.4.7)). Let `G` be simply connected and let the crosscuts `C_n`
satisfy (i), (ii), with `C_0` disjoint from the `C_n`, `n ≥ 1`. By Proposition 2.12 there is exactly one component
`V_n` of `G ∖ C_n` that does not contain `C_0`, and condition (iii) can be written as (2.4.7) `V_{n+1} ⊆ V_n`,
`n = 1, 2, …`. -/
theorem eq2_4_7 {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {C : ℕ → Set ExtPlane}
    (hi : ∀ n, IsCrosscut G (C n)) (hii : ∀ n, Disjoint (closure (C n)) (closure (C (n + 1))))
    (h0 : ∀ n, 1 ≤ n → Disjoint (C 0) (C n)) :
    (∀ n, 1 ≤ n → ∃ x ∈ G \ C n, nullChainDomain G C n = connectedComponentIn (G \ C n) x) ∧
      ((∀ n, 1 ≤ n → SeparatesIn G (C n) (C 0) (C (n + 1))) ↔
        ∀ n, 1 ≤ n → nullChainDomain G C (n + 1) ⊆ nullChainDomain G C n) := by
  sorry

/-- **Definition (2.4.8)** (§2.4). The null-chain `(C'_n)` is equivalent to `(C_n)`: for every sufficiently large `m`
there exists `n` such that `C'_m` separates `C_n` from `C_0`, and `C_m` separates `C'_n` from `C'_0`. -/
def NullChainEquiv (G : Set ExtPlane) (C C' : ℕ → Set ExtPlane) : Prop :=
  ∀ᶠ m in atTop, ∃ n, SeparatesIn G (C' m) (C n) (C 0) ∧ SeparatesIn G (C m) (C' n) (C' 0)

/-- **Unlabelled claim** (§2.4, l. 1380; cited as (2.4.9)). For null-chains of a simply connected domain, the
equivalence (2.4.8) can be expressed as (2.4.9) `V_n ⊆ V'_m`, `V'_n ⊆ V_m`. -/
theorem eq2_4_9 {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {C C' : ℕ → Set ExtPlane}
    (hC : IsNullChain G C) (hC' : IsNullChain G C') :
    NullChainEquiv G C C' ↔
      ∀ᶠ m in atTop, ∃ n, 1 ≤ n ∧ nullChainDomain G C n ⊆ nullChainDomain G C' m ∧
        nullChainDomain G C' n ⊆ nullChainDomain G C m := by
  sorry

/-- **Unlabelled claim** (§2.4, l. 1386; the definition of prime ends rests on it). The relation (2.4.8) is an
equivalence relation between null-chains. -/
theorem nullChainEquiv_equivalence {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) :
    Equivalence fun c c' : {C : ℕ → Set ExtPlane // IsNullChain G C} => NullChainEquiv G c.1 c'.1 := by
  sorry

/-- **Definition** (§2.4). The prime ends of `G`: the equivalence classes of null-chains of `G`; `P(G)` is the set of
all prime ends.
Modelling: a prime end is the set of the null-chains equivalent to a given one (`nullChainEquiv_equivalence`). -/
def primeEnds (G : Set ExtPlane) : Set (Set (ℕ → Set ExtPlane)) :=
  {P | ∃ C, IsNullChain G C ∧ P = {C' | IsNullChain G C' ∧ NullChainEquiv G C C'}}

/-- The correspondence of Theorem 2.15 (helper): `f̂ : 𝕋 → P(G)` is bijective, and for `ζ ∈ 𝕋` and a null-chain
`(C_n)` representing `f̂(ζ)`, `(f⁻¹(C_n))` is a null-chain of `𝔻` with (2.4.11)
`f⁻¹(C_n) ⊆ {z ∈ 𝔻 : δ_n < |z - ζ| < δ'_n}` (`n = 1, 2, …`) for suitable `0 < δ_n < δ'_n → 0`; that is, it
separates `0` from `ζ` for large `n`. -/
def IsPrimeEndCorrespondence (G : Set ExtPlane) (f : ExtPlane → ExtPlane) (fhat : ℂ → Set (ℕ → Set ExtPlane)) :
    Prop :=
  BijOn fhat (sphere 0 1) (primeEnds G) ∧
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ C ∈ fhat ζ,
      IsNullChain (toExt unitDisc) (fun n => Function.invFunOn f (toExt unitDisc) '' C n) ∧
        ∃ δ δ' : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n < δ' n) ∧ Tendsto δ' atTop (𝓝 0) ∧
          ∀ n, 1 ≤ n → Function.invFunOn f (toExt unitDisc) '' C n ⊆
            toExt {z | z ∈ unitDisc ∧ δ n < ‖z - ζ‖ ∧ ‖z - ζ‖ < δ' n}

/-- **Theorem 2.15** (§2.4; the prime end theorem, Carathéodory). Let `f` map `𝔻` conformally onto `G`. Then there is
a bijective mapping (2.4.10) `f̂ : 𝕋 → P(G)` such that, if `ζ ∈ 𝕋` and if `(C_n)` is a null-chain representing the
prime end `f̂(ζ)`, then `(f⁻¹(C_n))` is a null-chain that separates `0` from `ζ` for large `n`, in the precise form
(2.4.11).
(The project's `LiZhongQC.caratheodory_primeEnd` is a bijection for bounded plane domains, characterized by
impressions.) -/
theorem thm2_15 {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) : ∃ fhat : ℂ → Set (ℕ → Set ExtPlane), IsPrimeEndCorrespondence G f fhat := by
  sorry

end Pommerenke1992
