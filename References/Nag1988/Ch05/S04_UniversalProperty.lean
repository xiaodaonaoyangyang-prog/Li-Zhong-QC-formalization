import References.Nag1988.Ch05.S03_BersIsomorphism

/-!
# Nag, Chapter 5 §5.4: Marked families and the universal property (§5.4.1–§5.4.5)

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 5 §5.4.1–§5.4.5 (`full.md`
N2:5560–5860, folder `The Complex Analytic Theory … c10f6cd1`). §5.4.6–§5.4.8 (Subtheorem 5.4.6, Propositions A–D, the
Earle–Fowler theorem) need the `C^∞`/Hölder topology on diffeomorphism groups and are deferred.

[CORRECTION, Nag-fix1] A bare `ChartedSpace` makes `MDifferentiableAt` a purely pointwise notion (each point is read in its own
chart), so families whose fibre complex structures vary discontinuously were "holomorphic families" and the universal property
was false. `MarkedPointedFamily` and everything quantifying over families now carries `[T2Space]` and `[IsManifold 𝓘(ℂ, _) ω]`
on the total space and base; markings are orientation preserving (`qc`: the marking is the restriction of a quasiconformal
homeomorphism `S₀ ≃ₜ Y` sending `P j` to `pts j`), so `PointedTeichSpace` is `T(g, n)` and not `T(g, n) ⊔` its mirror.

Conventions (leader rulings on N-D4, N-D5): a marking is a fiberwise homotopy class of homeomorphisms
`X_n ≃ₜ (fiber minus the sections)`, locally constant over trivializing neighbourhoods; this replaces the book's reduction of
the structure group to `Diff₀(X, n)` (standard equivalence: homotopic diffeomorphisms of a surface are isotopic,
Baer–Epstein). A family is a holomorphic family of closed Riemann surfaces in the sense of `LiZhongQC.IsHolomorphicFamily`
(finite-dimensional base and total space), with the fibers and their embeddings given as data. `T(g,n)` is the set of
classes of marked `n`-pointed surfaces (`PointedTeichSpace`, the analogue of `LiZhongQC.TeichSpace` for punctured markings);
its complex structure and the universal family `(V(g,n), π, T(g,n))` of §5.2.4 are not constructed here: Theorem 5.4.3 is
stated as the existence of a universal marked family over a complex manifold `T` identified with `T(g,n)` by the classifying
map (the universal family is unique up to isomorphism by the universal property, so this is the book's family).

* Definition (holomorphic family of genus-`g` Riemann surfaces, §5.4.1, N2:5572) — exists: `LiZhongQC.IsHolomorphicFamily`
  (with the fibers and their genus given as data in the marked families below)
* Theorem (Ehresmann, quoted, §5.4.1, N2:5578) — `thm_ehresmann`
* Definition (transition maps, marking, marked family, classifying map `h`, §5.4.1, N2:5580) — `PuncturedHomotopic`,
  `PointedMarkedRS`, `PointedMarkedRS.Equiv`, `PointedTeichSpace`, `MarkedPointedFamily`, `MarkedPointedFamily.classify`
* Definition (`n`-pointed family, marked `n`-pointed family, morphism, §5.4.2, N2:5618) — `IsFibrewiseMarkedMap`,
  `IsMarkedMorphism`, `IsUniversalMarkedFamily`
* Unlabelled (§5.4.2, `(V(g,n), π, T(g,n))` is a marked `n`-pointed family, N2:5648) — deferred: the Bers family `V(g,n)` is a
  manifold only chart-wise (`IsQuotientManifoldOfDim`), so it cannot be an object of `MarkedPointedFamily`
* Theorem 5.4.3 (Grothendieck–Earle universal property, N2:5664) — `thm5_4_3`
* Theorem 5.4.3, Remark 1 (`h` is the classifying map, `E ≅ h^*V`, N2:5672) — `thm5_4_3_b`
* Corollary 5.4.3 (global triviality, N2:5678) — `cor5_4_3`
* Fact 5.4.3 (no universal unmarked family, N2:5686) — deferred: rests on Examples 5.4.4, which need complex projective curves
  in `ℙ² × ℂ*` (complex submanifolds are not available)
* Example 5.4.4 (i) (N2:5748) — deferred: needs the desingularization of a singular projective curve over `ℂ*`
* Example 5.4.4 (iii) (N2:5780) — deferred: needs complex submanifolds of `ℙ² × ℂ*`
* Lemma 5.4.5 (holomorphy of `H` from that of `h`, N2:5830) — `lemma5_4_5`
* Subtheorem 5.4.6, Propositions A–D (5.4.7), Earle–Fowler (5.4.8) — deferred: needs the C^∞/Hölder topology on
  diffeomorphism groups
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace Nag1988

open LiZhongQC (ClosedRS IsHolomorphicFamily IsBiholomorphic HasGenus)

/-! ## Marked pointed surfaces and their Teichmüller space -/

/-- **Homotopy of maps avoiding the points `pts`**: `f` and `g` are homotopic through maps `A → Y` that never meet any
`pts j` (a homotopy in `Y − {pts j}`). -/
def PuncturedHomotopic {A Y : Type} [TopologicalSpace A] [TopologicalSpace Y] {n : ℕ} (pts : Fin n → Y) (f g : A → Y) :
    Prop :=
  ∃ K : C(unitInterval × A, Y), (∀ a, K (0, a) = f a) ∧ (∀ a, K (1, a) = g a) ∧ ∀ t a j, K (t, a) ≠ pts j

/-- **Marked `n`-pointed surface** (§5.4.2): a closed Riemann surface `Y` with `n` distinct points `pts` and a marking, a
homeomorphism `S₀ − {P j} ≃ₜ Y − {pts j}`. Modelling: as `LiZhongQC.MarkedRS`, with punctured surfaces; quasiconformality of
the marking is not required (every homotopy class contains quasiconformal maps). -/
structure PointedMarkedRS (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (n : ℕ) (P : Fin n → S₀) where
  Y : ClosedRS.{0}
  pts : Fin n → Y.carrier
  pts_inj : Function.Injective pts
  marking : ↥(range P)ᶜ ≃ₜ {y : Y.carrier // ∀ j, y ≠ pts j}
  qc : ∃ φ : S₀ ≃ₜ Y.carrier, LiZhongQC.IsQCRS φ ∧ (∀ x : ↥(range P)ᶜ, (marking x).1 = φ x.1) ∧ ∀ j, φ (P j) = pts j

/-- Equivalence of marked `n`-pointed surfaces: a conformal map respecting the points whose composite with the first
marking is homotopic, in the punctured surface, to the second marking (as in `LiZhongQC.MarkedRS.Equiv`). -/
def PointedMarkedRS.Equiv {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] {n : ℕ} {P : Fin n → S₀} (m₁ m₂ : PointedMarkedRS S₀ n P) : Prop :=
  ∃ c : m₁.Y.carrier ≃ₜ m₂.Y.carrier, IsBiholomorphic c ∧ (∀ j, c (m₁.pts j) = m₂.pts j) ∧
    PuncturedHomotopic m₂.pts (fun x => c (m₁.marking x).1) (fun x => (m₂.marking x).1)

/-- **The Teichmüller space `T(g, n) = T(X_n)`** of the `n`-punctured surface (§5.4.2, (4.8)): classes of marked `n`-pointed
surfaces. -/
def PointedTeichSpace (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (n : ℕ) (P : Fin n → S₀) : Type 1 :=
  Quot (PointedMarkedRS.Equiv (S₀ := S₀) (P := P))

/-! ## Marked `n`-pointed families -/

/-- **Marked `n`-pointed holomorphic family** (§5.4.1–§5.4.2, (4.1)–(4.8)): a holomorphic family `proj : E → B` of closed
Riemann surfaces (fibers `fibre b` embedded holomorphically in `E` by `incl b`, `incl_range`), `n` pairwise disjoint holomorphic
sections `b ↦ incl b (secPt j b)`, and a marking: for each `b` a homeomorphism `mark b : S₀ − {P j} ≃ₜ fibre b − {sections}`,
locally constant in `b`: near every `b₀` it is homotopic (in the punctured fiber) to a family `Θ b` of homeomorphisms that
depends continuously on `b` as a map `U × (S₀ − {P j}) → E`. Modelling: the topological reduction of the structure group to
the maps homotopic to the identity (see the file header). -/
structure MarkedPointedFamily (S₀ : Type) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] (n : ℕ) (P : Fin n → S₀) (nb : ℕ) (E B : Type)
    [TopologicalSpace E] [ChartedSpace (Fin (nb + 1) → ℂ) E] [T2Space E] [IsManifold 𝓘(ℂ, Fin (nb + 1) → ℂ) ω E] [TopologicalSpace B] [ChartedSpace (Fin nb → ℂ) B] [T2Space B] [IsManifold 𝓘(ℂ, Fin nb → ℂ) ω B] where
  proj : E → B
  isFamily : IsHolomorphicFamily (n := nb) proj
  fibre : B → ClosedRS.{0}
  incl : ∀ b, (fibre b).carrier → E
  incl_hol : ∀ b, MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (nb + 1) → ℂ) (incl b)
  incl_emb : ∀ b, Topology.IsEmbedding (incl b)
  incl_range : ∀ b, range (incl b) = proj ⁻¹' {b}
  secPt : Fin n → ∀ b, (fibre b).carrier
  secPt_inj : ∀ b, Function.Injective fun j => secPt j b
  sec_hol : ∀ j, MDifferentiable 𝓘(ℂ, Fin nb → ℂ) 𝓘(ℂ, Fin (nb + 1) → ℂ) fun b => incl b (secPt j b)
  mark : ∀ b, ↥(range P)ᶜ ≃ₜ {y : (fibre b).carrier // ∀ j, y ≠ secPt j b}
  mark_qc : ∀ b, ∃ φ : S₀ ≃ₜ (fibre b).carrier, LiZhongQC.IsQCRS φ ∧ (∀ x : ↥(range P)ᶜ, (mark b x).1 = φ x.1) ∧
    ∀ j, φ (P j) = secPt j b
  mark_loc : ∀ b₀, ∃ U ∈ 𝓝 b₀, ∃ Θ : ∀ b, ↥(range P)ᶜ ≃ₜ {y : (fibre b).carrier // ∀ j, y ≠ secPt j b},
    Continuous (fun q : U × ↥(range P)ᶜ => incl q.1.1 (Θ q.1.1 q.2).1) ∧
      ∀ b ∈ U, PuncturedHomotopic (fun j => secPt j b) (fun x => (mark b x).1) (fun x => (Θ b x).1)

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] {n : ℕ} {P : Fin n → S₀}

/-- **The classifying map `h : B → T(g,n)`** (§5.4.2, (4.5), (4.8)): `b ↦ [fibre b, sections, mark b]`. -/
def MarkedPointedFamily.classify {nb : ℕ} {E B : Type} [TopologicalSpace E] [ChartedSpace (Fin (nb + 1) → ℂ) E] [T2Space E] [IsManifold 𝓘(ℂ, Fin (nb + 1) → ℂ) ω E]
    [TopologicalSpace B] [ChartedSpace (Fin nb → ℂ) B] [T2Space B] [IsManifold 𝓘(ℂ, Fin nb → ℂ) ω B] (F : MarkedPointedFamily S₀ n P nb E B) (b : B) :
    PointedTeichSpace S₀ n P :=
  Quot.mk _ ⟨F.fibre b, fun j => F.secPt j b, F.secPt_inj b, F.mark b, F.mark_qc b⟩

/-- **Fiberwise marking-preserving map over `h`** (§5.4.2, (4.10)): `H : E₁ → E₂` covers `h : B₁ → B₂`, and over each `b` it
is a biholomorphism `c` of the fibers (`incl₂ ∘ c = H ∘ incl₁`) carrying sections to sections and the marking `mark₁ b` to
`mark₂ (h b)` up to homotopy in the punctured fiber. -/
def IsFibrewiseMarkedMap {nb₁ nb₂ : ℕ} {E₁ B₁ E₂ B₂ : Type} [TopologicalSpace E₁]
    [ChartedSpace (Fin (nb₁ + 1) → ℂ) E₁] [T2Space E₁] [IsManifold 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) ω E₁] [TopologicalSpace B₁] [ChartedSpace (Fin nb₁ → ℂ) B₁] [T2Space B₁] [IsManifold 𝓘(ℂ, Fin nb₁ → ℂ) ω B₁] [TopologicalSpace E₂]
    [ChartedSpace (Fin (nb₂ + 1) → ℂ) E₂] [T2Space E₂] [IsManifold 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) ω E₂] [TopologicalSpace B₂] [ChartedSpace (Fin nb₂ → ℂ) B₂] [T2Space B₂] [IsManifold 𝓘(ℂ, Fin nb₂ → ℂ) ω B₂]
    (F₁ : MarkedPointedFamily S₀ n P nb₁ E₁ B₁) (F₂ : MarkedPointedFamily S₀ n P nb₂ E₂ B₂) (h : B₁ → B₂) (H : E₁ → E₂) :
    Prop :=
  (∀ e, F₂.proj (H e) = h (F₁.proj e)) ∧
    ∀ b, ∃ c : (F₁.fibre b).carrier ≃ₜ (F₂.fibre (h b)).carrier, IsBiholomorphic c ∧
      (∀ x, F₂.incl (h b) (c x) = H (F₁.incl b x)) ∧ (∀ j, c (F₁.secPt j b) = F₂.secPt j (h b)) ∧
      PuncturedHomotopic (fun j => F₂.secPt j (h b)) (fun x => c (F₁.mark b x).1) (fun x => (F₂.mark (h b) x).1)

/-- **Morphism of marked `n`-pointed holomorphic families** (§5.4.2, (4.10)): `(H, h)` holomorphic and fiberwise
marking-preserving (`IsFibrewiseMarkedMap`). -/
def IsMarkedMorphism {nb₁ nb₂ : ℕ} {E₁ B₁ E₂ B₂ : Type} [TopologicalSpace E₁] [ChartedSpace (Fin (nb₁ + 1) → ℂ) E₁] [T2Space E₁] [IsManifold 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) ω E₁]
    [TopologicalSpace B₁] [ChartedSpace (Fin nb₁ → ℂ) B₁] [T2Space B₁] [IsManifold 𝓘(ℂ, Fin nb₁ → ℂ) ω B₁] [TopologicalSpace E₂] [ChartedSpace (Fin (nb₂ + 1) → ℂ) E₂] [T2Space E₂] [IsManifold 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) ω E₂]
    [TopologicalSpace B₂] [ChartedSpace (Fin nb₂ → ℂ) B₂] [T2Space B₂] [IsManifold 𝓘(ℂ, Fin nb₂ → ℂ) ω B₂] (F₁ : MarkedPointedFamily S₀ n P nb₁ E₁ B₁)
    (F₂ : MarkedPointedFamily S₀ n P nb₂ E₂ B₂) (h : B₁ → B₂) (H : E₁ → E₂) : Prop :=
  IsFibrewiseMarkedMap F₁ F₂ h H ∧ MDifferentiable 𝓘(ℂ, Fin nb₁ → ℂ) 𝓘(ℂ, Fin nb₂ → ℂ) h ∧
    MDifferentiable 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) H

/-- **Universal marked `n`-pointed family** (Theorem 5.4.3): every marked `n`-pointed holomorphic family with connected base
and total space admits exactly one morphism into `U`. -/
def IsUniversalMarkedFamily {nb : ℕ} {E B : Type} [TopologicalSpace E] [ChartedSpace (Fin (nb + 1) → ℂ) E] [T2Space E] [IsManifold 𝓘(ℂ, Fin (nb + 1) → ℂ) ω E]
    [TopologicalSpace B] [ChartedSpace (Fin nb → ℂ) B] [T2Space B] [IsManifold 𝓘(ℂ, Fin nb → ℂ) ω B] (U : MarkedPointedFamily S₀ n P nb E B) : Prop :=
  ∀ (nb' : ℕ) (E' B' : Type) (_ : TopologicalSpace E') (_ : ChartedSpace (Fin (nb' + 1) → ℂ) E') (_ : T2Space E') (_ : IsManifold 𝓘(ℂ, Fin (nb' + 1) → ℂ) ω E')
    (_ : TopologicalSpace B') (_ : ChartedSpace (Fin nb' → ℂ) B') (_ : T2Space B') (_ : IsManifold 𝓘(ℂ, Fin nb' → ℂ) ω B') (_ : ConnectedSpace E') (_ : ConnectedSpace B')
    (F : MarkedPointedFamily S₀ n P nb' E' B'), ∃! hH : (B' → B) × (E' → E), IsMarkedMorphism F U hH.1 hH.2

/-! ## §5.4.1 – §5.4.5 -/

/-- **Theorem (Ehresmann, quoted)** (Ch. 5 §5.4.1). A proper surjective submersion `p : E → B` of finite-dimensional
smooth manifolds (`dim E = m + k`, `dim B = m`) is a locally trivial `C^∞` fiber bundle: every `b ∈ B` has an open
neighbourhood `U` with a diffeomorphism of `p⁻¹(U)` onto `U × F` (`F` a smooth `k`-manifold) commuting with the projections. -/
theorem thm_ehresmann {m k : ℕ} {E B : Type} [TopologicalSpace E] [T2Space E]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) E] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + k))) ∞ E]
    [TopologicalSpace B] [T2Space B] [ChartedSpace (EuclideanSpace ℝ (Fin m)) B]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ B] (p : E → B)
    (hp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + k))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ p)
    (hsurj : Function.Surjective p)
    (hsub : ∀ x, Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + k))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) p x))
    (hprop : IsProperMap p) :
    ∀ b : B, ∃ U : TopologicalSpace.Opens B, b ∈ U ∧ ∃ (F : Type) (_ : TopologicalSpace F)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin k)) F) (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ F),
      ∃ Ψ : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + k)))
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin m))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
        (U.comap ⟨p, hp.continuous⟩) (↥U × F) ∞, ∀ x, ((Ψ x).1 : B) = p x.1 := by
  sorry

/-- **Theorem 5.4.3 (Grothendieck–Earle universal property)** (Ch. 5 §5.4.3). Let `2g - 2 + n > 0`. There is a marked
`n`-pointed holomorphic family `(V, π, T)` of genus-`g` Riemann surfaces (finite-dimensional, `dim T = 3g - 3 + n`) over a
complex manifold `T` identified with `T(g,n)` (`e`, the classifying map of the family is `e⁻¹`), such that for every marked
`n`-pointed holomorphic family `(E, p, B)` of genus-`g` Riemann surfaces (with `E`, `B` connected) there is a unique morphism
of marked families `(H, h) : (E, p, B) → (V, π, T)`. Modelling: see the file header (the universal family is determined up
to isomorphism by this property; its construction as the Bers family `V(g,n)` is §5.2.4). -/
theorem thm5_4_3 [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : HasGenus S₀ g) (hP : Function.Injective P) (hhyp : 2 < 2 * g + n) :
    ∃ (TT VV : Type) (_ : TopologicalSpace TT) (_ : ChartedSpace (Fin (3 * g + n - 3) → ℂ) TT) (_ : T2Space TT)
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g + n - 3) → ℂ) ω TT)
      (_ : TopologicalSpace VV) (_ : ChartedSpace (Fin (3 * g + n - 3 + 1) → ℂ) VV) (_ : T2Space VV)
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g + n - 3 + 1) → ℂ) ω VV)
      (U : MarkedPointedFamily S₀ n P (3 * g + n - 3) VV TT) (e : TT ≃ PointedTeichSpace S₀ n P),
      (∀ t, U.classify t = e t) ∧ IsUniversalMarkedFamily U := by
  sorry

/-- **Theorem 5.4.3, Remark 1** (Ch. 5 §5.4.3, N2:5672). For a morphism `(H, h)` from a marked family `(E, p, B)` into a
marked family `U` (in particular the universal one), `h` is the classifying map (`[U.fibre (h b)] = [F.fibre b]` in
`T(g,n)`), and `(E, p, B)` is the pull-back `h^*U`: `e ↦ (p e, H e)` is a bijection of `E` onto
`{(b, v) : h b = π v}`. -/
theorem thm5_4_3_b {nb₁ nb₂ : ℕ} {E₁ B₁ E₂ B₂ : Type} [TopologicalSpace E₁] [ChartedSpace (Fin (nb₁ + 1) → ℂ) E₁] [T2Space E₁] [IsManifold 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) ω E₁]
    [TopologicalSpace B₁] [ChartedSpace (Fin nb₁ → ℂ) B₁] [T2Space B₁] [IsManifold 𝓘(ℂ, Fin nb₁ → ℂ) ω B₁] [TopologicalSpace E₂] [ChartedSpace (Fin (nb₂ + 1) → ℂ) E₂] [T2Space E₂] [IsManifold 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) ω E₂]
    [TopologicalSpace B₂] [ChartedSpace (Fin nb₂ → ℂ) B₂] [T2Space B₂] [IsManifold 𝓘(ℂ, Fin nb₂ → ℂ) ω B₂] (F : MarkedPointedFamily S₀ n P nb₁ E₁ B₁)
    (U : MarkedPointedFamily S₀ n P nb₂ E₂ B₂) (h : B₁ → B₂) (H : E₁ → E₂) (hM : IsMarkedMorphism F U h H) :
    (∀ b, U.classify (h b) = F.classify b) ∧
      BijOn (fun x => (F.proj x, H x)) univ {q : B₁ × E₂ | h q.1 = U.proj q.2} := by
  sorry

/-- **Corollary 5.4.3** (Ch. 5 §5.4.3). Every marked `n`-pointed holomorphic family of genus-`g` Riemann surfaces
(`2g - 2 + n > 0`) is globally trivial over its base: `E ≃ B × X` over `B`, carrying the `j`th section to `b ↦ (b, x_j)`, so
that `E' ≅ B × X_n`. Modelling: topological triviality (homeomorphisms); the `C^∞` refinement of the book is not formalized
(the real-smooth structure of the holomorphic charts is not an instance). -/
theorem cor5_4_3 [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : HasGenus S₀ g) (hP : Function.Injective P) (hhyp : 2 < 2 * g + n) {nb : ℕ} {E B : Type} [TopologicalSpace E]
    [ChartedSpace (Fin (nb + 1) → ℂ) E] [T2Space E] [IsManifold 𝓘(ℂ, Fin (nb + 1) → ℂ) ω E] [TopologicalSpace B] [ChartedSpace (Fin nb → ℂ) B] [T2Space B] [IsManifold 𝓘(ℂ, Fin nb → ℂ) ω B] [ConnectedSpace E]
    [ConnectedSpace B] (F : MarkedPointedFamily S₀ n P nb E B) :
    ∃ Φ : E ≃ₜ (B × S₀), (∀ x, (Φ x).1 = F.proj x) ∧ ∀ j b, Φ (F.incl b (F.secPt j b)) = (b, P j) := by
  sorry

/-- **Lemma 5.4.5** (Ch. 5 §5.4.5). In the setting of Theorem 5.4.3, let `H : E → V` be the fiberwise marking-preserving
biholomorphism over a map `h : B → T`. If `h` is holomorphic, then `H` is holomorphic. -/
theorem lemma5_4_5 {nb₁ nb₂ : ℕ} {E₁ B₁ E₂ B₂ : Type} [TopologicalSpace E₁] [ChartedSpace (Fin (nb₁ + 1) → ℂ) E₁] [T2Space E₁] [IsManifold 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) ω E₁]
    [TopologicalSpace B₁] [ChartedSpace (Fin nb₁ → ℂ) B₁] [T2Space B₁] [IsManifold 𝓘(ℂ, Fin nb₁ → ℂ) ω B₁] [TopologicalSpace E₂] [ChartedSpace (Fin (nb₂ + 1) → ℂ) E₂] [T2Space E₂] [IsManifold 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) ω E₂]
    [TopologicalSpace B₂] [ChartedSpace (Fin nb₂ → ℂ) B₂] [T2Space B₂] [IsManifold 𝓘(ℂ, Fin nb₂ → ℂ) ω B₂] (F : MarkedPointedFamily S₀ n P nb₁ E₁ B₁)
    (U : MarkedPointedFamily S₀ n P nb₂ E₂ B₂) (hU : IsUniversalMarkedFamily U) (h : B₁ → B₂) (H : E₁ → E₂)
    (hfib : IsFibrewiseMarkedMap F U h H) (hh : MDifferentiable 𝓘(ℂ, Fin nb₁ → ℂ) 𝓘(ℂ, Fin nb₂ → ℂ) h) :
    MDifferentiable 𝓘(ℂ, Fin (nb₁ + 1) → ℂ) 𝓘(ℂ, Fin (nb₂ + 1) → ℂ) H := by
  sorry

end Nag1988
