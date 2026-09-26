import LiZhongQC.Ch05.S19_Schwarzian

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

/-- A closed (compact) Riemann surface of genus `g`: its fundamental group is the surface group
of genus `g` (by the classification of closed orientable surfaces, `S` is then a sphere with `g`
handles). -/
def HasGenus (S : Type u) [TopologicalSpace S] (g : ℕ) : Prop :=
  CompactSpace S ∧ ∀ x : S, Nonempty (FundamentalGroup S x ≃* surfaceGroup g)

/-- §22.1: every closed Riemann surface has a (unique) genus. -/
theorem closed_surface_has_genus [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S] : ∃! g : ℕ, HasGenus S g := by
  sorry

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
  sorry

/-! ## §22.3 Uniformization -/

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
  sorry

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
  sorry

/-- §22.4 (Gauss–Bonnet): for a closed Riemann surface of genus `g > 1` uniformized as `ℍ/Γ`,
the hyperbolic area of a fundamental domain of `Γ` is `4π(g - 1)`. -/
theorem gauss_bonnet_area [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {F : Set ℂ} (hF : F ⊆ upperHalf)
    (hFund : MeasurableSet F ∧ (∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ F) ∧
      ∀ τ₁ τ₂ : UpperHalfPlane, (τ₁ : ℂ) ∈ interior F → (τ₂ : ℂ) ∈ interior F → p τ₁ = p τ₂ → τ₁ = τ₂) :
    ∫⁻ z in F, ENNReal.ofReal (1 / z.im ^ 2) = ENNReal.ofReal (4 * π * (g - 1)) := by
  sorry

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

/-- §22.5: `deg (ω) = 2g - 2` for a meromorphic differential and `deg (f) = 0` for a meromorphic
function on a closed surface of genus `g`. -/
theorem deg_canonical [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hS : HasGenus S g) {K : Divisor S} (hK : IsCanonicalDivisor K) : K.deg = 2 * (g : ℤ) - 2 := by
  sorry

/-- **Theorem 22.4** (Riemann–Roch).  On a closed Riemann surface of genus `g`,
`ℓ(α) - ℓ(K - α) = deg α - g + 1`.  Since `D[α] = {ω : (ω) ≥ α}` is isomorphic to `D₀[α - K]`,
this is the book's formula `dim D[α] = dim D₀[-α] - deg α + g - 1`. -/
theorem thm22_4_riemann_roch [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ}
    (hS : HasGenus S g) {K : Divisor S} (hK : IsCanonicalDivisor K) (α : Divisor S) :
    (ellDim α : ℤ) - ellDim (K - α) = α.deg - g + 1 := by
  sorry

/-- **Theorem 22.5**: on a closed Riemann surface of genus `g > 1`, `dim Q = 3g - 3`. -/
theorem thm22_5_dim_quadratic_differentials [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) :
    Module.finrank ℂ (holQuadDiffSubmodule S) = 3 * g - 3 := by
  sorry

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
