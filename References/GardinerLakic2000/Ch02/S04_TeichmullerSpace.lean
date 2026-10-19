import References.GardinerLakic2000.Ch02.S03_ExtremalLength

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.4 Teichmüller space

Source `teichmuller.txt`, lines 1306–1383 (Chapter 2, §2.4).

* Definition 5 (Beltrami differential, (2.3), the Banach space `L∞(R)`, `‖μ‖∞`, l. 1307–1315) — `beltramiSpace`,
  `beltramiNormRS` (on the project's chart-family notion of Beltrami differential, Li Zhong §23)
* Definition (the open unit ball `M(R)`, Beltrami coefficients, l. 1317) — `beltramiBall`
* Definition (the Beltrami coefficient of a quasiconformal map `f : R → R′`, l. 1331) — `beltramiCoeffRS`,
  `HasBeltramiCoeff`
* Unlabelled (the surface `R^μ`, l. 1317–1329; used throughout) — `para2_4_deformation`
* Unlabelled (a quasiconformal map determines an element of `M(R)`, and two maps with the same coefficient differ
  by a conformal map, l. 1331) — `para2_4_coeff_mem`, `para2_4_same_coeff`
* Definition 6 (Teichmüller equivalence, l. 1335–1343) — `IsTeichEquiv`
* Definition 7 (Teichmüller space `T(R)`, l. 1345) — `teichRel`, `TeichSpace`
* Formula (2.4) (the Teichmüller distance, l. 1353; cited at l. 5776) — `teichDist`
* Unlabelled (geometric isomorphisms are isometries, l. 1359; the term is used in Ch. 8) — `IsGeometricIsomorphism`,
  `para2_4_geometric_isometry`
* Unlabelled (an extremal representative exists; `d([f], [g]) = 0` iff `[f] = [g]`, l. 1365; `K₀` is used in Ch. 4)
  — `minimalDilatation`, `para2_4_extremal_exists`, `para2_4_dist_eq_zero`
* Definition (well-posed extremal-length problem, l. 1367–1373) — `IsTeichTrivialPlane`, `minimalDilatationPlane`,
  `IsWellPosedFamily`, `para2_4_well_posed_bound`
* Definition 8 (sufficient family, l. 1375) — `IsSufficientFamily`

Not items: the pseudo-metric on maps (l. 1347, U−); the measured-foliation remark (l. 1382). Modelling:
- **The boundary in Definition 6** (leader ruling A0.4(iii)): `R` comes with a uniformization `p : ℍ → R`; the
  homotopy `g_t` lifts to `ℍ`, the lift extends continuously to `ℍ̄ ⊆ ℂ̄`, and the extension fixes `ℝ̂` pointwise
  (the lift of `g_0 = id` is the identity). This is the meaning the book gives in Chapter 5 (l. 1343 defers it); for a
  surface without border it is the usual "homotopic to the identity". The same device is used by
  `LiZhongQC.HomotopicModBoundary`.
- **`T(R)`** is the quotient (`Quot`, no equivalence proof) of `M(R)` by "some quasiconformal maps with these
  coefficients are Teichmüller equivalent"; target surfaces are bundled (`RSBundle`) in the universe of `R`.
- **The factor ½.** (2.4) has `½ inf log K`; l. 1362 and 1365 drop the `½` ("`d([id],[f]) = inf log K(f₁)`",
  "`log K₀ = d([id],[f])`") [misprint]; stated with the `½` of (2.4), which is what later chapters cite (l. 5776).
- **Well-posed and sufficient families** are stated for plane domains (leader ruling A0.3), where the book's
  boundary is the set-theoretic one (l. 1343): `IsTeichTrivialPlane Ω g` is Definition 6 for `f₀ = g`, `f₁ = id`
  read literally in the plane.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsBeltramiDifferential IsQCRS maxDilatationRS localMapExpr localMapDomain complexDilatation
  IsBiholomorphic IsFuchsian IsUniformization ExtPlane extRealLine IsKQC maxDilatation LRCurve IsCurveImage
  extremalLength)

section Surface

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition 5** (§2.4, l. 1307–1315). The Banach space `L∞(R)` of essentially bounded measurable Beltrami
differentials `μ dz̄/dz` on `R`: families of coefficients `μ x` in the preferred charts obeying (2.3) almost
everywhere and bounded by some `k` (as a set of chart families). -/
def beltramiSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set (R → ℂ → ℂ) :=
  {μ | ∃ k : ℝ, IsBeltramiDifferential μ k}

/-- **Definition 5** (§2.4, l. 1315). `‖μ‖∞ = sup_α ‖μ^α‖∞`, independent of the charts. -/
def beltramiNormRS (μ : R → ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict (chartAt ℂ x).target)

/-- **Definition** (§2.4, l. 1317). `M(R)`, the open unit ball of `L∞(R)`: the Beltrami coefficients on `R`. -/
def beltramiBall (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set (R → ℂ → ℂ) :=
  {μ | ∃ k : ℝ, k < 1 ∧ IsBeltramiDifferential μ k}

/-- **Definition** (§2.4, l. 1331). The Beltrami coefficient of a map `f : R → R′`: in the chart at `x` it is the
complex dilatation of the local expression `w_β ∘ f ∘ z_α⁻¹` (the chart at `f x` on the target). -/
def beltramiCoeffRS {R' : Type*} [TopologicalSpace R'] [ChartedSpace ℂ R'] (f : R → R') : R → ℂ → ℂ :=
  fun x => complexDilatation (localMapExpr f x)

/-- Helper (§2.4). `f` has Beltrami coefficient `μ`: in every chart, almost everywhere on the domain of the local
expression. -/
def HasBeltramiCoeff {R' : Type*} [TopologicalSpace R'] [ChartedSpace ℂ R'] (f : R → R') (μ : R → ℂ → ℂ) :
    Prop :=
  ∀ x : R, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)), beltramiCoeffRS f x z = μ x z

/-- **Unlabelled** (§2.4, l. 1317–1329). For every `μ ∈ M(R)` there are a Riemann surface `R^μ` and a quasiconformal
homeomorphism `R → R^μ` (the identity of the point set in new charts) with Beltrami coefficient `μ`. -/
theorem para2_4_deformation [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {μ : R → ℂ → ℂ}
    (hμ : μ ∈ beltramiBall R) :
    ∃ (Y : RSBundle.{u}) (f : R ≃ₜ Y.carrier), IsQCRS f ∧ HasBeltramiCoeff f μ := by
  sorry

/-- **Unlabelled** (§2.4, l. 1331), first part. The Beltrami coefficient of a quasiconformal map `f : R → R′` is an
element of `M(R)`. -/
theorem para2_4_coeff_mem [IsManifold 𝓘(ℂ) ω R] {Y : RSBundle.{u}} {f : R ≃ₜ Y.carrier} (hf : IsQCRS f) :
    ∃ μ ∈ beltramiBall R, HasBeltramiCoeff f μ := by
  sorry

/-- **Unlabelled** (§2.4, l. 1331), second part. Two quasiconformal maps `f : R → R′`, `g : R → R″` with the same
Beltrami coefficient `μ` (`HasBeltramiCoeff`) differ by a conformal map: `g ∘ f⁻¹` is biholomorphic.
[CORRECTION] (AUDIT4 G9) The hypothesis was `HasBeltramiCoeff f (beltramiCoeffRS g)`, which compares the dilatation of `f` with that of `g` outside
the local domain of `g`'s expression (junk) and is practically unsatisfiable; now both maps have the coefficient `μ`. -/
theorem para2_4_same_coeff [IsManifold 𝓘(ℂ) ω R] {Y Z : RSBundle.{u}} {f : R ≃ₜ Y.carrier} {g : R ≃ₜ Z.carrier}
    (hf : IsQCRS f) (hg : IsQCRS g) {μ : R → ℂ → ℂ} (hfμ : HasBeltramiCoeff f μ) (hgμ : HasBeltramiCoeff g μ) :
    IsBiholomorphic ((g ∘ f.symm : Y.carrier → Z.carrier)) := by
  sorry

/-- **Definition 6** (§2.4, l. 1335–1343). Two quasiconformal maps `f₀ : R → R₀`, `f₁ : R → R₁` are Teichmüller
equivalent if there are a conformal map `c : R₀ → R₁` and a homotopy through quasiconformal self-maps `g_t` of `R`
with `g_0 = id`, `g_1 = f₁⁻¹ ∘ c ∘ f₀`, fixing the boundary of `R`: the lift `g̃_t` to `ℍ` (through the uniformization
`p`) extends continuously to `ℍ̄ ⊆ ℂ̄` and fixes `ℝ̂` pointwise for every `t` (see the module docstring). -/
def IsTeichEquiv (p : UpperHalfPlane → R) {Y₀ Y₁ : RSBundle.{u}} (f₀ : R ≃ₜ Y₀.carrier) (f₁ : R ≃ₜ Y₁.carrier) :
    Prop :=
  ∃ c : Y₀.carrier ≃ₜ Y₁.carrier, IsBiholomorphic (c : Y₀.carrier → Y₁.carrier) ∧
    ∃ (H : R → unitInterval → R) (Ht : UpperHalfPlane → unitInterval → UpperHalfPlane)
      (G : ExtPlane → unitInterval → ExtPlane),
      Continuous (fun x : R × unitInterval => H x.1 x.2) ∧ (∀ x, H x 0 = x) ∧ (∀ x, H x 1 = f₁.symm (c (f₀ x))) ∧
      (∀ t, ∃ e : R ≃ₜ R, (⇑e = fun x => H x t) ∧ IsQCRS e) ∧
      (∀ τ t, p (Ht τ t) = H (p τ) t) ∧ Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2) ∧
      (∀ (τ : UpperHalfPlane) t, G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane)) ∧
      ∀ x ∈ extRealLine, ∀ t, G x t = x

/-- **Definition 7** (§2.4, l. 1345), the relation. `μ ∼ ν` in `M(R)` if some quasiconformal maps with coefficients
`μ` and `ν` are Teichmüller equivalent. -/
def teichRel (p : UpperHalfPlane → R) (μ ν : beltramiBall R) : Prop :=
  ∃ (Y₀ Y₁ : RSBundle.{u}) (f₀ : R ≃ₜ Y₀.carrier) (f₁ : R ≃ₜ Y₁.carrier), IsQCRS f₀ ∧ IsQCRS f₁ ∧
    HasBeltramiCoeff f₀ μ.1 ∧ HasBeltramiCoeff f₁ ν.1 ∧ IsTeichEquiv p f₀ f₁

/-- **Definition 7** (§2.4, l. 1345). The Teichmüller space `T(R)`: the equivalence classes in `M(R)`. -/
def TeichSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] (p : UpperHalfPlane → R) : Type u :=
  Quot (teichRel p)

/-- **Formula (2.4)** (§2.4, l. 1353). The Teichmüller distance
`d([f], [g]) = ½ inf log K(f₁ ∘ g₁⁻¹)` over quasiconformal `f₁`, `g₁` in the classes of `f` and `g`. -/
def teichDist (p : UpperHalfPlane → R) (P Q : TeichSpace R p) : ℝ :=
  sInf {d | ∃ (μ ν : beltramiBall R) (Y₀ Y₁ : RSBundle.{u}) (f₁ : R ≃ₜ Y₀.carrier) (g₁ : R ≃ₜ Y₁.carrier),
    Quot.mk (teichRel p) μ = P ∧ Quot.mk (teichRel p) ν = Q ∧ IsQCRS f₁ ∧ IsQCRS g₁ ∧
      HasBeltramiCoeff f₁ μ.1 ∧ HasBeltramiCoeff g₁ ν.1 ∧
      d = 1 / 2 * Real.log (maxDilatationRS (f₁ ∘ g₁.symm : Y₁.carrier → Y₀.carrier)).toReal}

/-- **Definition** (§2.4, l. 1365; `K₀` of Ch. 4). The minimal dilatation `K₀` of a Teichmüller class: the infimum of
`K(f₁)` over the quasiconformal maps `f₁` in the class. -/
def minimalDilatation (p : UpperHalfPlane → R) (P : TeichSpace R p) : ℝ≥0∞ :=
  ⨅ (μ : beltramiBall R) (Y : RSBundle.{u}) (f : R ≃ₜ Y.carrier)
    (_ : Quot.mk (teichRel p) μ = P ∧ IsQCRS f ∧ HasBeltramiCoeff f μ.1), maxDilatationRS f

/-- **Unlabelled** (§2.4, l. 1365). Every Teichmüller class `[f]` has an extremal quasiconformal representative
`f₀`, `K(f₀) = K₀`, and `d([id], [f]) = ½ log K₀` (with the `½` of (2.4), see the module docstring). -/
theorem para2_4_extremal_exists [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) (P : TeichSpace R p) :
    ∃ (μ : beltramiBall R) (Y : RSBundle.{u}) (f : R ≃ₜ Y.carrier), Quot.mk (teichRel p) μ = P ∧ IsQCRS f ∧
      HasBeltramiCoeff f μ.1 ∧ maxDilatationRS f = minimalDilatation p P ∧
      teichDist p (Quot.mk (teichRel p) ⟨0, h0⟩) P = 1 / 2 * Real.log (minimalDilatation p P).toReal := by
  sorry

/-- **Unlabelled** (§2.4, l. 1365). `d([f], [g]) = 0` if and only if `[f] = [g]`. -/
theorem para2_4_dist_eq_zero [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p) (P Q : TeichSpace R p) : teichDist p P Q = 0 ↔ P = Q := by
  sorry

/-- **Definition** (geometric isomorphism, §2.4, l. 1359). `Φ : T(R₁) → T(R₂)` is the map `[f] ↦ [f ∘ h⁻¹]` induced
by the quasiconformal map `h : R₁ → R₂`. -/
def IsGeometricIsomorphism {R₂ : Type u} [TopologicalSpace R₂] [ChartedSpace ℂ R₂] (h : R ≃ₜ R₂)
    (p₁ : UpperHalfPlane → R) (p₂ : UpperHalfPlane → R₂) (Φ : TeichSpace R p₁ → TeichSpace R₂ p₂) : Prop :=
  ∀ (Y : RSBundle.{u}) (f : R ≃ₜ Y.carrier) (μ : beltramiBall R) (ν : beltramiBall R₂), IsQCRS f →
    HasBeltramiCoeff f μ.1 → HasBeltramiCoeff (h.symm.trans f) ν.1 →
      Φ (Quot.mk (teichRel p₁) μ) = Quot.mk (teichRel p₂) ν

/-- **Unlabelled** (§2.4, l. 1359). A quasiconformal map `h : R₁ → R₂` induces a bijection `[f] ↦ [f ∘ h⁻¹]` from
`T(R₁)` onto `T(R₂)` which is an isometry for Teichmüller's metric. -/
theorem para2_4_geometric_isometry [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {R₂ : Type u}
    [TopologicalSpace R₂] [T2Space R₂] [ConnectedSpace R₂] [ChartedSpace ℂ R₂] [IsManifold 𝓘(ℂ) ω R₂]
    {h : R ≃ₜ R₂} (hh : IsQCRS h) {p₁ : UpperHalfPlane → R} {p₂ : UpperHalfPlane → R₂}
    (hp₁ : ∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p₁) (hp₂ : ∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p₂) :
    ∃ Φ : TeichSpace R p₁ → TeichSpace R₂ p₂, IsGeometricIsomorphism h p₁ p₂ Φ ∧ Function.Bijective Φ ∧
      ∀ P Q, teichDist p₂ (Φ P) (Φ Q) = teichDist p₁ P Q := by
  sorry

end Surface

/-- Helper (§2.4, l. 1343, 1367; plane reading). A quasiconformal self-map `g` of the plane domain `Ω` is Teichmüller
equivalent to the identity: there is a homotopy through quasiconformal self-maps of `Ω` from the identity to `g`,
continuous on `Ω̄ × [0, 1]` and fixing every point of the (set-theoretic) boundary of `Ω`. -/
def IsTeichTrivialPlane (Ω : Set ℂ) (g : ℂ → ℂ) : Prop :=
  ∃ H : ℂ → unitInterval → ℂ, ContinuousOn (fun x : ℂ × unitInterval => H x.1 x.2) (closure Ω ×ˢ univ) ∧
    (∀ z ∈ Ω, H z 0 = z) ∧ (∀ z ∈ Ω, H z 1 = g z) ∧
    (∀ t, (∃ K : ℝ, IsKQC (fun z => H z t) Ω K) ∧ (fun z => H z t) '' Ω = Ω) ∧ ∀ z ∈ frontier Ω, ∀ t, H z t = z

/-- Helper (§2.4, l. 1365–1378; plane reading). `K₀(g)`: the least maximal dilatation of a quasiconformal map `g₁` of
`Ω` onto `g(Ω)` Teichmüller equivalent to `g` (`g₁⁻¹ ∘ g` is Teichmüller trivial). -/
def minimalDilatationPlane (Ω : Set ℂ) (g : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (g₁ : ℂ → ℂ) (_ : (∃ K : ℝ, IsKQC g₁ Ω K) ∧ g₁ '' Ω = g '' Ω ∧
      IsTeichTrivialPlane Ω (Function.invFunOn g₁ Ω ∘ g)), maxDilatation g₁ Ω

/-- **Definition** (well-posed, §2.4, l. 1367–1373; plane reading). The curve family `F` in `Ω` is invariant under
the quasiconformal self-maps of `Ω` Teichmüller equivalent to the identity. -/
def IsWellPosedFamily (Ω : Set ℂ) (F : Set LRCurve) : Prop :=
  ∀ g : ℂ → ℂ, IsTeichTrivialPlane Ω g → IsCurveImage g F F

/-- **Unlabelled** (§2.4, l. 1370). For a well-posed family `F` and a quasiconformal `g`, `Λ(g(F)) ≤ K₀ Λ(F)`. -/
theorem para2_4_well_posed_bound {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) {F F' : Set LRCurve}
    (hF : ∀ γ ∈ F, γ.trace ⊆ Ω) (hwp : IsWellPosedFamily Ω F) {g : ℂ → ℂ} (hg : ∃ K : ℝ, IsKQC g Ω K)
    (himg : IsCurveImage g F F') :
    extremalLength F' ≤ minimalDilatationPlane Ω g * extremalLength F := by
  sorry

/-- **Definition 8** (sufficient family, §2.4, l. 1375; plane reading). A family `F_j` of well-posed extremal-length
problems in `Ω` is sufficient for Teichmüller's metric if `K₀(g) = sup_j Λ(g(F_j))/Λ(F_j)` for every quasiconformal
map `g` of `Ω`. The problems are non-degenerate, `0 < Λ(F_j) < ∞`, as in the book.
[CORRECTION] (AUDITR2_GL15 R2G-3) The bounds `0 < Λ(F_j) < ⊤` are added: in `ℝ≥0∞` the quotient is `⊤` for `Λ(F_j) = 0` and
`⊤/⊤ = 0` for `Λ(F_j) = ⊤`, junk values. -/
def IsSufficientFamily {ι : Type*} (Ω : Set ℂ) (F : ι → Set LRCurve) : Prop :=
  (∀ j, IsWellPosedFamily Ω (F j) ∧ 0 < extremalLength (F j) ∧ extremalLength (F j) < ⊤) ∧
    ∀ g : ℂ → ℂ, (∃ K : ℝ, IsKQC g Ω K) →
      minimalDilatationPlane Ω g =
        ⨆ (j : ι) (F' : Set LRCurve) (_ : IsCurveImage g (F j) F'), extremalLength F' / extremalLength (F j)

end GardinerLakic2000
