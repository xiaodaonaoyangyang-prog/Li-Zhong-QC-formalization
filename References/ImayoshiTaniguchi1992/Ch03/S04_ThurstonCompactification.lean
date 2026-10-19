import References.ImayoshiTaniguchi1992.Ch03.S03_FrickeKlein
import References.GardinerLakic2000.Ch12.S04_IntersectionNumbers
import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Imayoshi–Taniguchi, Chapter 3 §3.4: Thurston's compactification

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 3 §3.4 (`full.md` IT1:2158–2335,
folder `An Introduction to Teichmuller Spaces … ef13744b`). The results are quoted from Fathi–Laudenbach–Poénaru (FLP) and have no
proofs in the book; they are items (DESIGN §3).

Conventions: `S` is the set of free homotopy classes of essential simple closed curves of `R = S₀` (`SimpleClass`, unoriented:
a curve and its inverse give one class); `ℓ_*(c) ∈ (ℝ⁺)^S` is the family of lengths of the geodesics of the classes on a marked
surface with Fricke coordinates `c` (`IsLengthStar`), with the product topology. `P(ℝ⁺)^S` and `P(ℝ̄⁺)^S` are the quotients by
positive scalars (`ProjPos`, `ProjBar`; the latter on the nonnegative nonzero functions). The geometric intersection number is
`GardinerLakic2000.intersectionNumber` (the same definition as IT's `i`), read as a real number (`intersectionPairing`; it is
finite for essential simple loops). `MF` and `PMF` are IT's closure definitions (IT-D7); the identification with measured
foliations (FLP) is a quoted claim. `Quot.out` (a choice) is used to evaluate class functions on a representative; every value
used is independent of the representative.

* Definition (`S`, `ℓ_*`, IT1:2158) — `SimpleClass`, `IsLengthStar`
* Corollary to Theorem 3.12 (`ℓ_*` is a proper embedding, IT1:2172) — `thm3_12_cor`
* Definition (`P(ℝ⁺)^S`, `Pℓ_*`, IT1:2174) — `ProjPos`, `ProjBar`, `NonnegNonzero`
* Theorem 3.15 (`Pℓ_*` is an embedding, FLP, IT1:2176) — `thm3_15`
* Definition (geometric intersection number `i`, `i_*`, IT1:2180) — `intersectionPairing`, `iStar`; exists:
  `GardinerLakic2000.intersectionNumber`
* Theorem 3.16 (`closure Pi_*(S) ≅ S^{6g-7}`, FLP, IT1:2210) — `PiStarClosure`, `thm3_16`
* Definition (`MF`, `PMF`, IT1:2212) — `MFset`, `PMFset`
* Definition (measured foliation, `μ[β]`, IT1:2214, 2222) — exists: `GardinerLakic2000.IsMeasuredFoliation`,
  `GardinerLakic2000.folHeight`
* Hubbard–Masur theorem (named, quoted, IT1:2236) — `qdHeightFn`, `hubbard_masur`
* Proposition 3.17 (`ℓ_*(F_g) ∩ MF = ∅`, IT1:2238) — `prop3_17`
* Theorem 3.18 (FLP, IT1:2246) — `classOf`, `thm3_18`
* Theorem 3.19 (a) (`Pℓ_*(F_g) ∪ PMF` is a compact manifold with boundary `PMF`, FLP, IT1:2278) — `thurstonCompactification`,
  `thm3_19_a`
* Theorem 3.19 (b) (it is homeomorphic to the closed ball, IT1:2278) — `thm3_19_b`
* Definition (Thurston's compactification, IT1:2328) — `thurstonCompactification`
* Corollary to Theorem 3.19 (homeomorphisms act, IT1:2330) — `thm3_19_cor`
* Definition (type `(g, n, m)`, Notes, IT1:2338) — exists: `LiZhongQC.IsFiniteType`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (MarkedRS StandardGenerators IsUniformization IsFuchsian ActsFreely HasGenus Loop FreelyHomotopic ModTransform
  IsQCRS quadDiffNorm)
open GardinerLakic2000 (IsEssentialLoop intersectionNumber integrableHolQDSet qdHeight)
open References (markedLength)

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **`S`**: the set of free homotopy classes of essential simple closed curves of `S₀` (a curve and its inverse in one class). -/
def SimpleClass (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Type :=
  Quot fun α β : {α : Loop S₀ // IsEssentialLoop α} => FreelyHomotopic α.1 β.1 ∨ FreelyHomotopic α.1 ⟨β.1.1, β.1.2.symm⟩

/-- **`ℓ_*`** (Ch. 3 §3.4): `x = ℓ_*(m)` is the family of lengths of the closed geodesics of the classes on the marked surface
`m`: for every essential simple loop `α`, `x [α]` is the length of the geodesic of `α` on `m.X`. -/
def IsLengthStar (m : MarkedRS S₀) (x : SimpleClass S₀ → ℝ) : Prop :=
  ∀ α : {α : Loop S₀ // IsEssentialLoop α}, markedLength m α.1 (x (Quot.mk _ α))

/-- `ℓ_*` as a function on the Fricke space: `ℓs c` is `ℓ_*` of every marked surface with Fricke coordinates `c`. -/
def IsLengthStarFn {g : ℕ} {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) (ℓs : FC g → SimpleClass S₀ → ℝ) : Prop :=
  ∀ (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → IsLengthStar m (ℓs c)

/-- **Corollary to Theorem 3.12** (Ch. 3 §3.4). `ℓ_* : F_g → (ℝ⁺)^S` is a proper embedding: positive values, an embedding for the
product topology, and compact preimages in `F_g` of compact subsets of `(ℝ⁺)^S`. -/
theorem thm3_12_cor {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧ (∀ c ∈ frickeSpaceIT p₀ G, ∀ s, 0 < ℓs c s) ∧
      Topology.IsEmbedding ((frickeSpaceIT p₀ G).domRestrict ℓs) ∧
      ∀ K : Set (SimpleClass S₀ → ℝ), IsCompact K → (∀ x ∈ K, ∀ s, 0 < x s) →
        IsCompact (frickeSpaceIT p₀ G ∩ ℓs ⁻¹' K) := by
  sorry

/-- Nonnegative nonzero functions on `S`: the points of `(ℝ̄⁺)^S - {0}`. -/
def NonnegNonzero (x : SimpleClass S₀ → ℝ) : Prop := (∀ s, 0 ≤ x s) ∧ x ≠ 0

/-- **`P(ℝ⁺)^S`** (Ch. 3 §3.4): the positive functions on `S` modulo positive scalars. -/
abbrev ProjPos (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Type :=
  Quot fun x y : {x : SimpleClass S₀ → ℝ // ∀ s, 0 < x s} => ∃ r : ℝ, 0 < r ∧ y.1 = r • x.1

/-- **`P(ℝ̄⁺)^S`** (Ch. 3 §3.4, IT1:2190): `((ℝ̄⁺)^S - {0})/ℝ⁺`. -/
abbrev ProjBar (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Type :=
  Quot fun x y : {x : SimpleClass S₀ → ℝ // NonnegNonzero x} => ∃ r : ℝ, 0 < r ∧ y.1 = r • x.1

/-- **Theorem 3.15** (Ch. 3 §3.4, FLP Exposé 7). `Pℓ_* : F_g → P(ℝ⁺)^S` is an embedding. -/
theorem thm3_15 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧
      ∃ hpos : ∀ c ∈ frickeSpaceIT p₀ G, ∀ s, 0 < ℓs c s,
        Topology.IsEmbedding (fun c : ↥(frickeSpaceIT p₀ G) => (Quot.mk _ ⟨ℓs c, hpos c c.2⟩ : ProjPos S₀)) := by
  sorry

/-- **Geometric intersection number as a real number** `i(α, β)` of two classes (Ch. 3 §3.4, IT1:2180):
`GardinerLakic2000.intersectionNumber` of representatives (the infimum of the numbers of intersection points over the simple
loops in the classes), as a real. *Junk:* `⊤ ↦ 0`; the number is finite for essential simple loops of a closed surface. -/
def intersectionPairing (a b : SimpleClass S₀) : ℝ :=
  ((intersectionNumber (Quot.out a).1 (Quot.out b).1).toNat : ℝ)

/-- **`i_*(a, α)`** (Ch. 3 §3.4, IT1:2196): the function `β ↦ a · i(α, β)` on `S`, for `a > 0`. -/
def iStar (a : ℝ) (α : SimpleClass S₀) : SimpleClass S₀ → ℝ := fun β => a * intersectionPairing α β

/-- **`closure Pi_*(S)`** (Ch. 3 §3.4, IT1:2192, 2210): the closure in `P(ℝ̄⁺)^S` of the image of `S` under
`α ↦ [i(α, ·)]`. -/
def PiStarClosure (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Set (ProjBar S₀) :=
  closure {q | ∃ α : SimpleClass S₀, ∃ h : NonnegNonzero (iStar 1 α), q = Quot.mk _ ⟨iStar 1 α, h⟩}

/-- **Theorem 3.16** (Ch. 3 §3.4, FLP Exposé 4). The closure of `Pi_*(S)` in `P(ℝ̄⁺)^S` is homeomorphic to the sphere
`S^{6g-7} = {x ∈ ℝ^{6g-6} : |x| = 1}`. -/
theorem thm3_16 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) :
    Nonempty (↥(PiStarClosure S₀) ≃ₜ ↥(sphere (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1)) := by
  sorry

/-- **`MF`** (Ch. 3 §3.4, Remark, IT1:2212): `\overline{i_*(ℝ⁺ × S)} - {0} ⊆ (ℝ̄⁺)^S`, the closure of the set of functions
`a · i(α, ·)`, without `0`; identified with the space of measured foliations on `R` by FLP Exposé 6 (not formalized). -/
def MFset (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Set (SimpleClass S₀ → ℝ) :=
  closure (range fun q : {a : ℝ // 0 < a} × SimpleClass S₀ => iStar q.1 q.2) \ {0}

/-- **`PMF`** (Ch. 3 §3.4): the projection of `MF` to `P(ℝ̄⁺)^S`. -/
def PMFset (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Set (ProjBar S₀) :=
  {q | ∃ x ∈ MFset S₀, ∃ h : NonnegNonzero x, q = Quot.mk _ ⟨x, h⟩}

/-- The height function `α ↦ h_φ[α]` of a quadratic differential `φ` on the classes of `S` (`GardinerLakic2000.qdHeight` of a
representative; `0` for `φ = 0`). -/
def qdHeightFn (φ : S₀ → ℂ → ℂ) (a : SimpleClass S₀) : ℝ := (qdHeight φ (Quot.out a).1).toReal

/-- **Hubbard–Masur theorem (quoted)** (Ch. 3 §3.4, IT1:2236). For the complex structure of `R`, `MF ∪ {0}` is identified with
the space `A(R)` of holomorphic quadratic differentials by `φ ↦ (α ↦ h_φ[α])`: this map is a bijection of `A(R)` onto `MF ∪ {0}`,
and it is a homeomorphism (convergence in the norm of `A(R)` ⇔ convergence of all heights). Modelling: the extra statement
"`≅ ℝ^{6g-6}`" is the dimension of `A(R)` and is not repeated. Near miss: `GardinerLakic2000.thm12_1_b` (heights into
measured foliations of GL's model). -/
theorem hubbard_masur {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) :
    BijOn qdHeightFn (integrableHolQDSet S₀) (MFset S₀ ∪ {0}) ∧
      ∀ (φs : ℕ → S₀ → ℂ → ℂ) (φ : S₀ → ℂ → ℂ), (∀ n, φs n ∈ integrableHolQDSet S₀) → φ ∈ integrableHolQDSet S₀ →
        (Tendsto (fun n => quadDiffNorm (φs n - φ)) atTop (𝓝 0) ↔
          Tendsto (fun n => qdHeightFn (φs n)) atTop (𝓝 (qdHeightFn φ))) := by
  sorry

/-- **Proposition 3.17** (Ch. 3 §3.4). The image `ℓ_*(F_g)` is disjoint from `MF` in `(ℝ̄⁺)^S`. -/
theorem prop3_17 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧ (∀ c ∈ frickeSpaceIT p₀ G, ∀ s, 0 < ℓs c s) ∧
      ∀ c ∈ frickeSpaceIT p₀ G, ℓs c ∉ MFset S₀ := by
  sorry

/-- The class in `S` of an essential simple loop. -/
def classOf (α : Loop S₀) (h : IsEssentialLoop α) : SimpleClass S₀ := Quot.mk _ ⟨α, h⟩

/-- **Theorem 3.18** (Ch. 3 §3.4, FLP Exposé 8). For every system of decomposing curves `𝓛 = {L_j}` of `R` there is a
homeomorphism `q_𝓛 : ℓ_*(F_g) → U(𝓛)` onto `U(𝓛) = {p ∈ MF : i_*(p)(L_j) > 0 for all j}` with
`i_*(q_𝓛(x))(L_j) = x(L_j)` for every `x = ℓ_*(t)` (the lengths `ℓ(L_j(t)) = μ_t[L_j]`). Modelling: "natural" is read as
this displayed property. -/
theorem thm3_18 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) (hess : ∀ j, IsEssentialLoop (L j)) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧ (∀ c ∈ frickeSpaceIT p₀ G, ∀ s, 0 < ℓs c s) ∧
      ∃ q : ↥(ℓs '' frickeSpaceIT p₀ G) ≃ₜ
          ↥{x ∈ MFset S₀ | ∀ j, 0 < x (classOf (L j) (hess j))},
        ∀ y j, ((q y : SimpleClass S₀ → ℝ) (classOf (L j) (hess j))) = y.1 (classOf (L j) (hess j)) := by
  sorry

/-- **Thurston's compactification** `\overline{T_g}^{Th} = Pℓ_*(F_g) ∪ PMF ⊆ P(ℝ̄⁺)^S` (Ch. 3 §3.4, IT1:2328), with boundary
`PMF`: the union of the image of `F_g` under `Pℓ_*` and `PMF`. -/
def thurstonCompactification {g : ℕ} (ℓs : FC g → SimpleClass S₀ → ℝ) (F : Set (FC g)) : Set (ProjBar S₀) :=
  {q | ∃ c ∈ F, ∃ h : NonnegNonzero (ℓs c), q = Quot.mk _ ⟨ℓs c, h⟩} ∪ PMFset S₀

/-- **Theorem 3.19 (a)** (Ch. 3 §3.4, FLP Exposé 8). `Pℓ_*(F_g) ∪ PMF ⊆ P(ℝ̄⁺)^S`, with the relative topology, is a compact
(topological) manifold with boundary `PMF`: it is compact and has a half-space atlas of dimension `6g - 6` whose boundary is
`PMF`. -/
theorem thm3_19_a {g n : ℕ} [NeZero n] (hn : n = 6 * g - 6) (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧
      CompactSpace ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)) ∧
      ∃ _ : ChartedSpace (EuclideanHalfSpace n) ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)),
        (modelWithCornersEuclideanHalfSpace n).boundary ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)) =
          {q | q.1 ∈ PMFset S₀} := by
  sorry

/-- **Theorem 3.19 (b)** (Ch. 3 §3.4, FLP Exposé 8). `Pℓ_*(F_g) ∪ PMF` is homeomorphic to the closed ball
`{x ∈ ℝ^{6g-6} : |x| ≤ 1}`, with boundary `PMF` corresponding to the sphere. -/
theorem thm3_19_b {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    ∃ ℓs : FC g → SimpleClass S₀ → ℝ, IsLengthStarFn p₀ G ℓs ∧
      ∃ e : ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)) ≃ₜ
          ↥(closedBall (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1),
        ∀ q, q.1 ∈ PMFset S₀ ↔ ‖(e q : EuclideanSpace ℝ (Fin (6 * g - 6)))‖ = 1 := by
  sorry

/-- **Corollary to Theorem 3.19** (Ch. 3 §3.4). Every orientation-preserving (quasiconformal, up to homotopy) homeomorphism
`f` of `R` induces a homeomorphism of `Pℓ_*(F_g) ∪ PMF` onto itself, preserving `PMF`, and acting on the points of `F_g` as
the modular transformation `[S, m] ↦ [S, m ∘ f]`. -/
theorem thm3_19_cor {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    (ℓs : FC g → SimpleClass S₀ → ℝ) (hℓs : IsLengthStarFn p₀ G ℓs) (f : ModTransform S₀) :
    ∃ h : ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)) ≃ₜ ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G)),
      (∀ q, q.1 ∈ PMFset S₀ → (h q).1 ∈ PMFset S₀) ∧
        ∀ (m : MarkedRS S₀) (hqc : IsQCRS (f.1.trans m.marking)) (c c' : FC g) (hc : IsFrickeCoordsIT p₀ G m c)
          (hc' : IsFrickeCoordsIT p₀ G ⟨m.X, f.1.trans m.marking, hqc⟩ c') (h1 : NonnegNonzero (ℓs c))
          (h2 : NonnegNonzero (ℓs c')) (q : ↥(thurstonCompactification ℓs (frickeSpaceIT p₀ G))),
          q.1 = Quot.mk _ ⟨ℓs c, h1⟩ → (h q).1 = Quot.mk _ ⟨ℓs c', h2⟩ := by
  sorry

end ImayoshiTaniguchi1992
