import References.LehtoVirtanen1973.Ch06.S00_Introduction

/-!
# Lehto–Virtanen, Chapter VI §1: Geometric characterization of a quasiconformal function

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. VI §1
(pp. 240–246; `full.md` second part P2:1594–1721).

Conventions as in the Introduction (`S00_Introduction`): mappings `ExtPlane → ExtPlane` of domains `G` of `ℂ̄`, not
necessarily one-to-one, continuous in the spherical metric (footnote 53). For a mapping `f` of `G`, `f⁻¹(A)` is the
preimage in `G`, `G ∩ f ⁻¹' A`; closures are taken in `ℂ̄`, so that `Ā ⊂ G` makes `Ā` a compact subset of `G`; a
component of a set is a connected component (`connectedComponentIn`). A "disc" is an open spherical disc
`sphericalBall c r` with `r > 0` (I.1.9): the discs of 1.4–1.6 are centred at image points such as `w₀ = f(z₀)`,
which may be `∞`. For `r < π/2` a spherical disc is a euclidean disc, the exterior of one, or a half-plane; in
Lemma 1.3 the closures of the discs lie in `f(G) ≠ ℂ̄`, which forces `r < π/2`.

* Unlabelled (§1.1, P2:1596; cited P2:1705, "cf. the remark at the beginning of 1.1"): if a continuous `f`, locally
  homeomorphic up to isolated points, is sense-preserving on one subdomain on which it is homeomorphic, it is
  sense-preserving on every such subdomain — `sensePreserving_of_sensePreserving_subdomain`
* Theorem 1.1 (§1.1) — `thm6_1_1`
* Formula (1.1) (§1.1) — omitted: the module condition, a display in the hypothesis of Theorems 1.1 and 1.1′ and
  formalized there; not a result
* Definition (open mapping, §1.2) — exists: `IsOpenMap` (applied to the restriction of f to the domain G; G being
  open, the open subsets of the subspace G are the open sets of the plane contained in G, and an open subset of the
  domain G′ is open in the plane)
* Formula (1.2) (§1.2; cited P2:1676, 1678) — exists: `IsOpenMap.preimage_closure_eq_closure_preimage` (for the
  restriction of the continuous open f to G: the preimage in G of the closure of A is the closure in the subspace G
  of the preimage, that is its closure in the plane intersected with G, for every set A)
* Definition (light mapping, interior mapping, §1.2) — `IsLightOn`, `IsInteriorMap`
* Unlabelled (§1.2, P2:1632): non-constant analytic functions are interior mappings — omitted: an example, not used
  later in the book
* Stoilow's theorem (§1.2, quoted: "a theorem of Stoilow [1]") — `stoilow_theorem`
* Unlabelled (§1.2, P2:1622, 1634): an interior mapping is locally homeomorphic up to isolated points and conversely,
  so that "interior" may replace this hypothesis in Theorem 1.1 — omitted: the direction used later is Theorem 1.2,
  and the resulting version of Theorem 1.1 is Theorem 1.1′; the converse is only asserted, never used
* Lemma 1.1 (§1.3) — `lemma6_1_1`
* Lemma 1.2 (§1.4) — `lemma6_1_2`
* Formula (1.3) (§1.4) — omitted: a step of the proof of Lemma 1.2
* Unlabelled (§1.4, P2:1664, quoted from Newman): the intersection of a decreasing sequence of non-empty (connected)
  compact sets is non-empty (connected) — omitted: quoted inside the proof of Lemma 1.2 only
* Definition (the components of `f⁻¹(E)` in `A`, notation of Lemma 1.3, §1.5) — `preimageComponentsIn`
* Lemma 1.3 (§1.5) — `lemma6_1_3`
* Theorem 1.2 (§1.6) — `thm6_1_2`
* Definition (sense-preserving interior mapping, §1.7) — `IsSensePreservingInteriorMap`
* Theorem 1.1′ (§1.7) — `thm6_1_1'`
* Unlabelled (§1.7, P2:1709–1721): Theorems 1.1 and 1.1′ remain true when (1.1) is replaced by the corresponding
  condition for analytic quadrilaterals, ring domains or rectangles, by `sup_{G − E} F(z) ≤ K`, or by `H(z)` finite
  and `≤ K` almost everywhere in `G − E` — omitted: derived in passing from the proof of Theorem 1.1 and Theorems
  I.5.3, I.7.2, IV.3.3, I.9.1 and IV.4.2 ("for example"), and not cited later

[OCR or misprint] P2:1622 reads "Theorem 1.4" for Theorem 1.1. [OCR] P2:1600, 1670, 1687 have `<` for `⊂`. The
decomposition `G = E ∪ ⋃ Uᵢ` of P2:1711 (the `Uᵢ` domains on which `f` is a sense-preserving homeomorphism) is the
content of the hypotheses of Theorems 1.1 and 1.1′ and is not stated separately. Lemma I.1.2′ (`lemma1_1_2'`), the
Existence theorem (`existence_theorem`) and the Uniqueness theorem (`uniqueness_theorem`) are only used in proofs.
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)

/-! ## §1.1 Quasiconformality and module conditions -/

/-- **Unlabelled** (Ch. VI §1.1, P2:1596; cited at P2:1705, "cf. the remark at the beginning of 1.1"). Let `f` be a
continuous function which is locally homeomorphic except at isolated points in a domain `G`. If the restriction of `f`
to a domain `U ⊂ G` is a sense-preserving homeomorphism, then `f` preserves the orientation in every subdomain of `G`
where it is homeomorphic ("a simple connectivity argument"). -/
theorem sensePreserving_of_sensePreserving_subdomain {f : ExtPlane → ExtPlane} {G E U : Set ExtPlane}
    (hG : IsDomainExt G) (hc : ContinuousOn f G) (hE : IsLocalHomeoOffIsolated f G E) (hU : IsDomainExt U)
    (hUG : U ⊆ G) (hfU : IsSensePreservingOn f U) {V : Set ExtPlane} (hV : IsDomainExt V) (hVG : V ⊆ G)
    (hfV : IsHomeoOn f V (f '' V)) : IsSensePreservingOn f V := by
  sorry

/-- **Theorem 1.1** (Ch. VI §1.1). Let `f` be a continuous mapping of a domain `G` which is locally homeomorphic and
sense-preserving up to a set `E ⊂ G` of isolated points. If `f` satisfies the module condition `M(f(Q)) ≤ K M(Q)`
(1.1) for every quadrilateral `Q` such that `Q̄ ⊂ G` and `f` maps `Q̄` topologically, then `f` is `K`-quasiconformal
in `G`.
Modelling: continuity is spherical (footnote 53), i.e. in the topology of `ℂ̄`; [OCR] `E < G` is `E ⊂ G`. (1.1) is
required for every quadrilateral `Q`, `Q̄ ⊂ G`, which `f` maps topologically onto a quadrilateral `Q′` whose vertices
are the images of those of `Q` (a homeomorphism of quadrilaterals, I.2.3, `IsQuadHomeo`). Under the other hypotheses
every `Q`, `Q̄ ⊂ G`, which `f` maps topologically is of this kind (`Q − E ≠ ∅`, so `f` is sense-preserving on `Q̄` by
the orientation theorem and the image vertices are positively ordered); this is therefore the book's condition, and
the module of the image data is always that of a quadrilateral. No hypothesis `K ≥ 1` is needed: (1.1) for a small
quadrilateral in `G − E` and for its relabelling `Q(z₂, z₃, z₄, z₁)`, whose module is `1/M(Q)`, forces it. -/
theorem thm6_1_1 {f : ExtPlane → ExtPlane} {G E : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hc : ContinuousOn f G) (hE : IsSensePreservingLocalHomeoOffIsolated f G E)
    (h11 : ∀ Q Q' : Quadrilateral, closure Q.dom ⊆ G → IsQuadHomeo f Q Q' → Q'.module ≤ K * Q.module) :
    IsKQuasiconformalFunction f G K := by
  sorry

/-! ## §1.2 Interior mappings -/

/-- **Definition** (light mapping, Ch. VI §1.2, P2:1630). The mapping `f` of the domain `G` is called light if every
component of the preimage `f⁻¹(ζ)` of any point `ζ ∈ f(G)` consists of a single point.
Modelling: `f⁻¹(ζ)` is the preimage in `G`; every `ζ ∈ f(G)` is `f(z)` for a point `z ∈ G`, whose component in
`f⁻¹(f(z))` is required to be `{z}`. -/
def IsLightOn (f : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  ∀ z ∈ G, connectedComponentIn (G ∩ f ⁻¹' {f z}) z = {z}

/-- **Definition** (interior mapping, Ch. VI §1.2, P2:1630). If the mapping `f` of the domain `G` is continuous, open
and light, then it is called an interior mapping of `G`.
Modelling: "a mapping of the domain `G`" makes `G` a domain (as in `IsConformalMap`). "Open" (P2:1624: the image of
every open subset of `G` is open) is `IsOpenMap` of the restriction of `f` to `G`; `G` is open, so the open subsets of
the subspace `G` are the open sets of the plane contained in `G`. -/
def IsInteriorMap (f : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  IsDomainExt G ∧ ContinuousOn f G ∧ IsOpenMap (G.domRestrict f) ∧ IsLightOn f G

/-- **Stoilow's theorem** (Ch. VI §1.2, quoted: "a theorem of Stoilow [1]"). An interior mapping `f` of a domain `G`
can always be represented in the form `f = φ ∘ w`, where `w` is a homeomorphism of `G` and `φ` is analytic in `w(G)`.
Modelling: `w` is a homeomorphism of `G` onto `w(G)` (I.1.2) and is not required to be sense-preserving (the interior
mapping `z ↦ z̄` of the plane has no representation with a sense-preserving `w`); `φ` is analytic in the sense of the
Introduction (poles allowed, `IsExtAnalyticOn`); `f = φ ∘ w` on `G`. The book proves only the part of the theorem it
uses, Theorem 1.2 (P2:1636). -/
theorem stoilow_theorem {f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hf : IsInteriorMap f G) :
    ∃ w φ : ExtPlane → ExtPlane, IsHomeoOn w G (w '' G) ∧ IsExtAnalyticOn φ (w '' G) ∧
      ∀ z ∈ G, f z = φ (w z) := by
  sorry

/-! ## §1.3 A lemma on open mappings -/

/-- **Lemma 1.1** (Ch. VI §1.3). Let `f` be a continuous open mapping of a domain `G`, `D` a subdomain of `f(G)`, and
`A`, `Ā ⊂ G`, a component of `f⁻¹(D)`. Then `f(A) = D`.
Modelling: "open" as in `IsInteriorMap`; `f⁻¹(D)` is the preimage in `G`; `Ā` is the closure in `ℂ̄`. -/
theorem lemma6_1_1 {f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G) (hc : ContinuousOn f G)
    (ho : IsOpenMap (G.domRestrict f)) {D : Set ExtPlane} (hD : IsDomainExt D) (hDG : D ⊆ f '' G)
    {A : Set ExtPlane} (hA : ∃ z ∈ G ∩ f ⁻¹' D, A = connectedComponentIn (G ∩ f ⁻¹' D) z)
    (hAG : closure A ⊆ G) : f '' A = D := by
  sorry

/-! ## §1.4 A lemma on light mappings -/

/-- **Lemma 1.2** (Ch. VI §1.4). Let `f` be a continuous light mapping of a domain `G`, `z₀` a point of `G`, and `U` a
neighbourhood of `z₀` with `Ū ⊂ G`. Then there exists a neighbourhood `V` of `w₀ = f(z₀)` such that the component of
`f⁻¹(V̄)` which contains `z₀` lies in `U`.
Modelling: neighbourhoods are filter neighbourhoods (`𝓝`); open ones give the same statement, since `U` may be
shrunk to its interior in the hypothesis and `V` to its interior in the conclusion (the component shrinks with `V̄`).
`w₀ = ∞` is allowed. -/
theorem lemma6_1_2 {f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G) (hc : ContinuousOn f G)
    (hl : IsLightOn f G) {z₀ : ExtPlane} (hz₀ : z₀ ∈ G) {U : Set ExtPlane} (hU : U ∈ 𝓝 z₀)
    (hUG : closure U ⊆ G) :
    ∃ V ∈ 𝓝 (f z₀), connectedComponentIn (G ∩ f ⁻¹' closure V) z₀ ⊆ U := by
  sorry

/-! ## §1.5 A lemma on interior mappings -/

/-- **Definition** (the components of `f⁻¹(E)` in `A`, Ch. VI §1.5, P2:1670, notation of Lemma 1.3): the components
of the preimage `f⁻¹(E)` (in `G`) which lie in `A` (P2:1674: "all components of `f⁻¹(D₁)` lying in `A`"). In
Lemma 1.3, where `E ⊂ V` and `A` is a component of `f⁻¹(V)`, every component of `f⁻¹(E)` either lies in `A` or does
not meet `A` (P2:1672). -/
def preimageComponentsIn (f : ExtPlane → ExtPlane) (G E A : Set ExtPlane) : Set (Set ExtPlane) :=
  {C | ∃ z ∈ G ∩ f ⁻¹' E, C = connectedComponentIn (G ∩ f ⁻¹' E) z ∧ C ⊆ A}

/-- **Lemma 1.3** (Ch. VI §1.5). Let `f` be an interior mapping of a simply connected domain `G` such that `f(G)` is
not the whole plane, and `V`, `V̄ ⊂ f(G)`, a disc. Let `D₁` and `D₂` be discs, `D̄₁ ∪ D̄₂ ⊂ V`, `D̄₁ ∩ D̄₂ = ∅`, and
`w ∈ V` a point outside `D̄₁ ∪ D̄₂`. If `A`, `Ā ⊂ G`, is a component of `f⁻¹(V)`, then the sets `f⁻¹(w)`, `f⁻¹(D₁)`,
`f⁻¹(D₂)` each have a finite positive number `n`, `n₁`, `n₂` of components in `A`, and these numbers satisfy
`n ≤ n₁ n₂`.
Modelling: [OCR] `<` is `⊂`. The discs are spherical discs of positive radius (module docstring); an empty `Dᵢ` would
make `nᵢ = 0`. The numbers of components are the cardinalities in `ℕ∞` (`Set.encard`) of the sets
`preimageComponentsIn`; their finiteness and positivity are asserted, so no truncation is used. -/
theorem lemma6_1_3 {f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hf : IsInteriorMap f G)
    (hG : IsSimplyConnectedDomain G) (hfG : f '' G ≠ univ) {V D₁ D₂ : Set ExtPlane}
    (hV : ∃ (c : ExtPlane) (r : ℝ), 0 < r ∧ V = sphericalBall c r) (hVG : closure V ⊆ f '' G)
    (hD₁ : ∃ (c : ExtPlane) (r : ℝ), 0 < r ∧ D₁ = sphericalBall c r)
    (hD₂ : ∃ (c : ExtPlane) (r : ℝ), 0 < r ∧ D₂ = sphericalBall c r)
    (hDV : closure D₁ ∪ closure D₂ ⊆ V) (hD₁₂ : Disjoint (closure D₁) (closure D₂)) {w : ExtPlane}
    (hw : w ∈ V) (hw' : w ∉ closure D₁ ∪ closure D₂) {A : Set ExtPlane}
    (hA : ∃ z ∈ G ∩ f ⁻¹' V, A = connectedComponentIn (G ∩ f ⁻¹' V) z) (hAG : closure A ⊆ G) :
    (preimageComponentsIn f G {w} A).encard ≠ 0 ∧ (preimageComponentsIn f G {w} A).encard ≠ ⊤ ∧
      (preimageComponentsIn f G D₁ A).encard ≠ 0 ∧ (preimageComponentsIn f G D₁ A).encard ≠ ⊤ ∧
      (preimageComponentsIn f G D₂ A).encard ≠ 0 ∧ (preimageComponentsIn f G D₂ A).encard ≠ ⊤ ∧
      (preimageComponentsIn f G {w} A).encard ≤
        (preimageComponentsIn f G D₁ A).encard * (preimageComponentsIn f G D₂ A).encard := by
  sorry

/-! ## §1.6 Local behaviour of interior mappings -/

/-- **Theorem 1.2** (Ch. VI §1.6). An interior mapping `f` of a domain `G` is locally homeomorphic in `G` with the
possible exception of isolated points.
Modelling: the exceptional set `E` has no accumulation point in `G` (`IsLocalHomeoOffIsolated`, the stronger reading;
the proof shows that it is closed and discrete in `G`). -/
theorem thm6_1_2 {f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hf : IsInteriorMap f G) :
    ∃ E : Set ExtPlane, IsLocalHomeoOffIsolated f G E := by
  sorry

/-! ## §1.7 Other forms of the geometric characterization -/

/-- **Definition** (sense-preserving interior mapping, Ch. VI §1.7, P2:1705). "Once in possession of Theorem 1.2 we
can define when an interior mapping is sense-preserving": an interior mapping `f` of `G` is sense-preserving if its
restriction to every subdomain of `G` on which it is homeomorphic is sense-preserving (I.1.5).
Modelling: such subdomains exist by Theorem 1.2, and by the remark at the beginning of 1.1
(`sensePreserving_of_sensePreserving_subdomain`) it suffices that the restriction to one of them is sense-preserving;
the definition states the "every subdomain" form. -/
def IsSensePreservingInteriorMap (f : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  IsInteriorMap f G ∧ ∀ U, IsDomainExt U → U ⊆ G → IsHomeoOn f U (f '' U) → IsSensePreservingOn f U

/-- **Theorem 1.1′** (Ch. VI §1.7). Let `f` be a sense-preserving interior mapping of the domain `G`. If every
quadrilateral `Q`, `Q̄ ⊂ G`, which is mapped by `f` topologically onto a quadrilateral `Q′` satisfies the module
condition `M(Q′) ≤ K M(Q)`, then `f` is `K`-quasiconformal in `G`.
Modelling: "mapped topologically onto `Q′`" is a homeomorphism of quadrilaterals (I.2.3, `IsQuadHomeo`: `Q̄` onto
`Q̄′`, the vertices of `Q` onto those of `Q′`), as in `thm6_1_1`. As there, `K ≥ 1` is forced by the hypothesis. -/
theorem thm6_1_1' {f : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hf : IsSensePreservingInteriorMap f G)
    (h11 : ∀ Q Q' : Quadrilateral, closure Q.dom ⊆ G → IsQuadHomeo f Q Q' → Q'.module ≤ K * Q.module) :
    IsKQuasiconformalFunction f G K := by
  sorry

end LehtoVirtanen1973
