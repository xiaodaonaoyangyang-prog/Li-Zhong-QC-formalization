import References.Forster1981.Ch02.S13_DolbeaultsLemma

/-!
# Forster, Chapter 2 §14: A finiteness theorem

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 (`full.md` F1:4657–5196).

Conventions (rulings B0.4): `‖f‖_{L²(D)}` is `MeasureTheory.eLpNorm f 2 (volume.restrict D)` (in `ℝ≥0∞`); `L²(D, 𝒪)` is
the span `l2Hol D`; "closed subspace" is closedness under `L²`-convergent sequences; `V ⋐ U` is `IsRelCompactIn V U`
(`closure V` compact and inside `U`). A finite family of charts `(U_i*, z_i)` with disc images and open subsets `U_i ⊆ U_i*`
is `IsDiscChartFamily e U` (`e i` the charts, `U_i* = (e i).source`); the `L²`-norms of 0- and 1-cochains of `𝒪` over
`𝔘 = (U_i)` are computed in these charts on representatives of the classes (independent of the choice) and are
`cechL2Norm0`, `cechL2Norm1`; the restriction `H¹(Y₂) → H¹(Y₁)` appears through its image `h1RestrictImage` (a span). The
genus of a compact Riemann surface is `genus X := finrank ℂ H¹(X, 𝒪)`; near miss `LiZhongQC.HasGenus` (topological).

* Paragraph 14.1 (the `L²`-norm, `L²(D, 𝒪)`, Parseval, F1:4661) — `l2Hol`, `para14_1`
* Theorem 14.2 (F1:4717) — `thm14_2`
* Consequence of 14.2 (completeness of `L²(D, 𝒪)`, F1:4737) — `thm14_2_cons`
* Lemma 14.3 (F1:4741) — `IsRelCompactIn`, `IsL2ClosedIn`, `lemma14_3`
* Paragraph 14.4 (square integrable cochains, F1:4791) — `IsDiscChartFamily`, `holRep`, `cechL2Norm0`, `cechL2Norm1`,
  `cechZ1L2`, `IsCechL2Closed`
* Paragraph 14.5 (shrinkings, F1:4823) — `IsShrinking`, `para14_5_a`, `para14_5_b`
* Lemma 14.6 (F1:4829) — `lemma14_6`
* Lemma 14.7 (F1:4905) — `lemma14_7`
* Paragraph 14.8 (the restriction homomorphism, F1:5013) — `h1RestrictImage`
* Theorem 14.9 (F1:5021) — `thm14_9`
* Corollary 14.10 (F1:5045) — `cor14_10`
* Definition 14.11 (genus, F1:5053) — `genus`
* Theorem 14.12 (F1:5063) — `thm14_12`
* Corollary 14.13 (F1:5101) — `cor14_13`
* Corollary 14.14 (F1:5125) — `cor14_14`
* Theorem 14.15 (F1:5129) — `thm14_15`
* Corollary 14.16 (F1:5163) — `cor14_16`

Omitted (U−): the sup bound and the orthogonality of the monomials (14.1), the Hilbert space structures of 14.4, the two
remarks of 14.7, the composition claim of 14.8, "`ℙ¹` has genus 0" (14.11), the remark after 14.16.
-/

open scoped Manifold ContDiff Topology References ENNReal NNReal Real
open Set Filter MeasureTheory TopologicalSpace CategoryTheory Opposite

namespace Forster1981

/-- **Relatively compact** (`V ⋐ U`, Ch. 2 §14, F1:4741): the closure of `V` is compact and contained in `U`. -/
def IsRelCompactIn {Z : Type*} [TopologicalSpace Z] (V U : Set Z) : Prop := IsCompact (closure V) ∧ closure V ⊆ U

/-- **The space `L²(D, 𝒪)`** (14.1, Ch. 2 §14, F1:4661): the square integrable holomorphic functions on the open set `D`. -/
def l2Hol (D : Set ℂ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {f | DifferentiableOn ℂ f D ∧ eLpNorm f 2 (volume.restrict D) < (⊤ : ℝ≥0∞)}

/-- **Closedness in `L²(D)`**: a subspace of `L²(D, 𝒪)` containing the `L²(D)`-limits (lying in `L²(D, 𝒪)`) of its sequences.
Modelling: the limit `g` is required to lie in `l2Hol D` (the ambient space): an arbitrary `g` at `L²(D)`-distance `0` from `0`
(e.g. the indicator of a point of `D`) is not holomorphic, so without this the notion is unsatisfiable. -/
def IsL2ClosedIn (D : Set ℂ) (A : Submodule ℂ (ℂ → ℂ)) : Prop :=
  ∀ (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ), (∀ k, f k ∈ A) → g ∈ l2Hol D →
    Tendsto (fun k => eLpNorm (f k - g) 2 (volume.restrict D)) atTop (𝓝 0) → g ∈ A

/-- **Paragraph 14.1** (Parseval's formula `(*)`, Ch. 2 §14, F1:4661). For a disc `B = B(0, r)` and `f ∈ L²(B, 𝒪)` with
Taylor series `Σ c_n z^n`: `‖f‖²_{L²(B)} = Σ π r^{2n+2}/(n+1) |c_n|²`. -/
theorem para14_1 {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : f ∈ l2Hol (Metric.ball 0 r)) :
    eLpNorm f 2 (volume.restrict (Metric.ball (0 : ℂ) r)) ^ 2 =
      ENNReal.ofReal (∑' n : ℕ, π * r ^ (2 * n + 2) / (n + 1) * ‖iteratedDeriv n f 0 / (n.factorial : ℂ)‖ ^ 2) := by
  sorry

/-- **Theorem 14.2** (Ch. 2 §14, F1:4717). Let `D ⊆ ℂ` be open, `r > 0` and `D_r = {z : B(z, r) ⊆ D}`. Then for every
`f ∈ L²(D, 𝒪)`: `‖f‖_{D_r} ≤ (1/(√π r)) ‖f‖_{L²(D)}`, where `‖f‖_{D_r} = sup {|f(a)| : a ∈ D_r}`. -/
theorem thm14_2 {D : Set ℂ} (hD : IsOpen D) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : f ∈ l2Hol D) :
    (⨆ a ∈ {z : ℂ | Metric.ball z r ⊆ D}, (‖f a‖₊ : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 / (Real.sqrt π * r)) * eLpNorm f 2 (volume.restrict D) := by
  sorry

/-- **Consequence of Theorem 14.2** (Ch. 2 §14, F1:4737). `L²(D, 𝒪)` is complete: an `L²(D)`-Cauchy sequence in
`L²(D, 𝒪)` has an `L²(D)`-limit in `L²(D, 𝒪)`. -/
theorem thm14_2_cons {D : Set ℂ} (hD : IsOpen D) {f : ℕ → ℂ → ℂ} (hf : ∀ k, f k ∈ l2Hol D)
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ k ≥ N, eLpNorm (f m - f k) 2 (volume.restrict D) < ε) :
    ∃ g ∈ l2Hol D, Tendsto (fun k => eLpNorm (f k - g) 2 (volume.restrict D)) atTop (𝓝 0) := by
  sorry

/-- **Lemma 14.3** (Ch. 2 §14, F1:4741). Let `D′ ⋐ D` be open subsets of `ℂ`. For every `ε > 0` there is a closed vector
subspace `A ⊆ L²(D, 𝒪)` of finite codimension with `‖f‖_{L²(D′)} ≤ ε ‖f‖_{L²(D)}` for all `f ∈ A`. -/
theorem lemma14_3 {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D') (hrel : IsRelCompactIn D' D) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Submodule ℂ (ℂ → ℂ), A ≤ l2Hol D ∧ IsL2ClosedIn D A ∧
      Module.Finite ℂ (↥(l2Hol D) ⧸ A.comap (l2Hol D).subtype) ∧
      ∀ f ∈ A, eLpNorm f 2 (volume.restrict D') ≤ ENNReal.ofReal ε * eLpNorm f 2 (volume.restrict D) := by
  sorry

section Cochains

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ}

/-- **Finite families of disc charts** (14.4, Ch. 2 §14, F1:4791): charts `e i` (`z_i`) of the complex structure whose
images are open discs, and open subsets `U_i ⊆ U_i* = (e i).source`. The family `𝔘* = (U_i*)` need not cover. -/
def IsDiscChartFamily (e : Fin n → OpenPartialHomeomorph X ℂ) (U : Fin n → Opens X) : Prop :=
  (∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) ∧ (∀ i, ∃ (c : ℂ) (r : ℝ), (e i).target = Metric.ball c r) ∧
    ∀ i, (U i : Set X) ⊆ (e i).source

/-- **Shrinkings** `𝔙 ≪ 𝔘` (14.5, Ch. 2 §14, F1:4823): `V_i ⋐ U_i` for all `i`. -/
def IsShrinking (V U : Fin n → Opens X) : Prop :=
  (∀ i, V i ≤ U i) ∧ ∀ i, IsRelCompactIn (V i : Set X) (U i : Set X)

/-- A representative function of a class in `𝒪(V)`, for the `L²`-norms of 14.4. -/
noncomputable def holRep {V : Opens X} (c : ↥((modO X).obj (op V))) : X → ℂ :=
  (Quotient.out (show ↥(repSpan (R := ℂ) IsHolFunAt (V : Set X)) ⧸
    (repSpan (R := ℂ) VanishesAt (V : Set X)).comap (repSpan (R := ℂ) IsHolFunAt (V : Set X)).subtype from c)).1

/-- **The `L²`-norm of a 0-cochain** (14.4(i), Ch. 2 §14, F1:4791): `‖η‖²_{L²(𝔘)} = Σ_i ‖f_i‖²_{L²(U_i)}`, the norms
computed in the charts `z_i`. -/
noncomputable def cechL2Norm0 (e : Fin n → OpenPartialHomeomorph X ℂ) (U : Fin n → Opens X)
    (c : CechC0 (modO X) U) : ℝ≥0∞ :=
  (∑ i, eLpNorm (holRep (c i) ∘ (e i).symm) 2 (volume.restrict ((e i) '' (U i : Set X))) ^ 2) ^ (1 / 2 : ℝ)

/-- **The `L²`-norm of a 1-cochain** (14.4(ii), Ch. 2 §14, F1:4791): `‖ξ‖²_{L²(𝔘)} = Σ_{i,j} ‖f_ij‖²_{L²(U_i ∩ U_j)}`,
the norms computed in the charts `z_i`. -/
noncomputable def cechL2Norm1 (e : Fin n → OpenPartialHomeomorph X ℂ) (U : Fin n → Opens X)
    (ξ : CechC1 (modO X) U) : ℝ≥0∞ :=
  (∑ i, ∑ j, eLpNorm (holRep (ξ i j) ∘ (e i).symm) 2
    (volume.restrict ((e i) '' ((U i ⊓ U j : Opens X) : Set X))) ^ 2) ^ (1 / 2 : ℝ)

/-- **Square integrable cocycles** `Z¹_{L²}(𝔘, 𝒪)` (14.4, Ch. 2 §14, F1:4791). -/
noncomputable def cechZ1L2 (e : Fin n → OpenPartialHomeomorph X ℂ) (U : Fin n → Opens X) :
    Submodule ℂ (CechC1 (modO X) U) :=
  Submodule.span ℂ {ξ | ξ ∈ cechZ1 (modO X) U ∧ cechL2Norm1 e U ξ < (⊤ : ℝ≥0∞)}

/-- Closedness in the `L²(𝔘)`-norm of 1-cochains. -/
def IsCechL2Closed (e : Fin n → OpenPartialHomeomorph X ℂ) (U : Fin n → Opens X)
    (A : Submodule ℂ (CechC1 (modO X) U)) : Prop :=
  ∀ (ξ : ℕ → CechC1 (modO X) U) (ξ₀ : CechC1 (modO X) U), (∀ k, ξ k ∈ A) →
    Tendsto (fun k => cechL2Norm1 e U (ξ k - ξ₀)) atTop (𝓝 0) → ξ₀ ∈ A

end Cochains

section RiemannSurface

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {n : ℕ}

/-- **Paragraph 14.5(a)** (Ch. 2 §14, F1:4823). For a shrinking `𝔙 ≪ 𝔘` and every 1-cochain `ξ` of `𝔘`, the restriction of
`ξ` to `𝔙` has finite `L²(𝔙)`-norm. -/
theorem para14_5_a {e : Fin n → OpenPartialHomeomorph X ℂ} {U V : Fin n → Opens X} (hU : IsDiscChartFamily e U)
    (hV : IsShrinking V U) (ξ : CechC1 (modO X) U) :
    cechL2Norm1 e V (cechRefine (modO X) U V id hV.1 ξ) < (⊤ : ℝ≥0∞) := by
  sorry

/-- **Paragraph 14.5(b)** (Ch. 2 §14, F1:4823). For a shrinking `𝔙 ≪ 𝔘` and `ε > 0` there is a closed vector subspace
`A ⊆ Z¹_{L²}(𝔘, 𝒪)` of finite codimension with `‖ξ‖_{L²(𝔙)} ≤ ε ‖ξ‖_{L²(𝔘)}` for all `ξ ∈ A`. -/
theorem para14_5_b {e : Fin n → OpenPartialHomeomorph X ℂ} {U V : Fin n → Opens X} (hU : IsDiscChartFamily e U)
    (hV : IsShrinking V U) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Submodule ℂ (CechC1 (modO X) U), A ≤ cechZ1L2 e U ∧ IsCechL2Closed e U A ∧
      Module.Finite ℂ (↥(cechZ1L2 e U) ⧸ A.comap (cechZ1L2 e U).subtype) ∧
      ∀ ξ ∈ A, cechL2Norm1 e V (cechRefine (modO X) U V id hV.1 ξ) ≤ ENNReal.ofReal ε * cechL2Norm1 e U ξ := by
  sorry

/-- **Lemma 14.6** (Ch. 2 §14, F1:4829). For shrinkings `𝔚 ≪ 𝔙 ≪ 𝔘 ≪ 𝔘*` there is a constant `C > 0` such that for every
`ξ ∈ Z¹_{L²}(𝔙, 𝒪)` there are `ζ ∈ Z¹_{L²}(𝔘, 𝒪)` and `η ∈ C⁰_{L²}(𝔚, 𝒪)` with `ζ = ξ + δη` on `𝔚` and
`max (‖ζ‖_{L²(𝔘)}, ‖η‖_{L²(𝔚)}) ≤ C ‖ξ‖_{L²(𝔙)}`. -/
theorem lemma14_6 {e : Fin n → OpenPartialHomeomorph X ℂ} {U V W : Fin n → Opens X} (hU : IsDiscChartFamily e U)
    (hWV : IsShrinking W V) (hVU : IsShrinking V U) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ ξ ∈ cechZ1L2 e V, ∃ ζ ∈ cechZ1L2 e U, ∃ η : CechC0 (modO X) W,
      cechRefine (modO X) U W id (fun i => (hWV.1 i).trans (hVU.1 i)) ζ =
        cechRefine (modO X) V W id hWV.1 ξ + cechD0 (modO X) W η ∧
      max (cechL2Norm1 e U ζ) (cechL2Norm0 e W η) ≤ (C : ℝ≥0∞) * cechL2Norm1 e V ξ := by
  sorry

/-- **Lemma 14.7** (Ch. 2 §14, F1:4905). Under the assumptions of 14.6 there is a finite dimensional subspace
`S ⊆ Z¹(𝔘, 𝒪)` such that for every `ξ ∈ Z¹(𝔘, 𝒪)` there are `σ ∈ S` and `η ∈ C⁰(𝔚, 𝒪)` with `σ = ξ + δη` on `𝔚`. -/
theorem lemma14_7 {e : Fin n → OpenPartialHomeomorph X ℂ} {U V W : Fin n → Opens X} (hU : IsDiscChartFamily e U)
    (hWV : IsShrinking W V) (hVU : IsShrinking V U) :
    ∃ S : Submodule ℂ (CechC1 (modO X) U), S ≤ cechZ1 (modO X) U ∧ FiniteDimensional ℂ S ∧
      ∀ ξ ∈ cechZ1 (modO X) U, ∃ σ ∈ S, ∃ η : CechC0 (modO X) W,
        cechRefine (modO X) U W id (fun i => (hWV.1 i).trans (hVU.1 i)) σ =
          cechRefine (modO X) U W id (fun i => (hWV.1 i).trans (hVU.1 i)) ξ + cechD0 (modO X) W η := by
  sorry

/-- **The image of the restriction homomorphism** `H¹(Y₂, F) → H¹(Y₁, F)` (14.8, Ch. 2 §14, F1:5013), for `Y₁ ⊆ Y₂`: the
span of the classes of the restrictions `ξ|𝔙` of cocycles `ξ` of coverings `𝔘` of `Y₂`, for coverings `𝔙` of `Y₁`
refining `𝔘`. -/
def h1RestrictImage {R : Type} [CommRing R] {Z : Type} [TopologicalSpace Z]
    (F : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of Z)) (Y₁ Y₂ : Opens Z) (_h : Y₁ ≤ Y₂) : Submodule R (H1 F Y₁) :=
  Submodule.span R {z | ∃ (𝔘 : CechCover Z Y₂) (𝔙 : CechCover Z Y₁) (τ : 𝔙.ι → 𝔘.ι)
    (hτ : IsRefinementMap 𝔘.U 𝔙.U τ) (ξ : ↥(cechZ1 F 𝔘.U)) (η : ↥(cechZ1 F 𝔙.U)),
    (η : CechC1 F 𝔙.U) = cechRefine F 𝔘.U 𝔙.U τ hτ ξ ∧ z = cechClass F 𝔙 η}

/-- **The genus** (Definition 14.11, Ch. 2 §14, F1:5053): `g = dim H¹(X, 𝒪)`. -/
noncomputable def genus (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : ℕ :=
  Module.finrank ℂ (H1 (modO X) ⊤)

/-- **Theorem 14.9** (Ch. 2 §14, F1:5021). Let `X` be a Riemann surface and `Y₁ ⋐ Y₂ ⊆ X` open. Then the restriction
homomorphism `H¹(Y₂, 𝒪) → H¹(Y₁, 𝒪)` has a finite dimensional image. -/
theorem thm14_9 {Y₁ Y₂ : Opens X} (hrel : IsRelCompactIn (Y₁ : Set X) (Y₂ : Set X)) (h : Y₁ ≤ Y₂) :
    FiniteDimensional ℂ (h1RestrictImage (modO X) Y₁ Y₂ h) := by
  sorry

/-- **Corollary 14.10** (Ch. 2 §14, F1:5045). For a compact Riemann surface `X`, `dim H¹(X, 𝒪) < ∞`. -/
theorem cor14_10 [CompactSpace X] : FiniteDimensional ℂ (H1 (modO X) ⊤) := by
  sorry

/-- **Theorem 14.12** (Ch. 2 §14, F1:5063). Let `Y ⋐ X` be a relatively compact open subset of a Riemann surface. For every
`a ∈ Y` there is a meromorphic function on `Y` with a pole at `a` which is holomorphic on `Y ∖ {a}`. -/
theorem thm14_12 {Y : Set X} (hY : IsOpen Y) (hrel : IsRelCompactIn Y (univ : Set X)) {a : X} (ha : a ∈ Y) :
    ∃ f : X → ℂ, IsMeromorphicOn f Y ∧ poles f Y = {a} := by
  sorry

/-- **Corollary 14.13** (Ch. 2 §14, F1:5101). On a compact Riemann surface, for distinct points `a_1, …, a_n` and complex
numbers `c_1, …, c_n` there is a meromorphic function `f` with `f(a_i) = c_i`. -/
theorem cor14_13 [CompactSpace X] {m : ℕ} {a : Fin m → X} (ha : Function.Injective a) (c : Fin m → ℂ) :
    ∃ f : X → ℂ, IsMeromorphicOn f univ ∧ (∀ i, a i ∉ poles f univ) ∧ ∀ i, f (a i) = c i := by
  sorry

/-- **Corollary 14.14** (Ch. 2 §14, F1:5125). Let `Y` be a relatively compact open subset of a non-compact Riemann
surface. Then there is a holomorphic function on `Y` which is not constant on any connected component of `Y`. -/
theorem cor14_14 [NoncompactSpace X] {Y : Set X} (hY : IsOpen Y) (hrel : IsRelCompactIn Y (univ : Set X)) :
    ∃ f : X → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f Y ∧
      ∀ x ∈ Y, ¬ ∃ c : ℂ, ∀ y ∈ connectedComponentIn Y x, f y = c := by
  sorry

/-- **Theorem 14.15** (Ch. 2 §14, F1:5129). Let `X` be a non-compact Riemann surface and `Y ⋐ Y′ ⊆ X` open. Then the image
of `H¹(Y′, 𝒪) → H¹(Y, 𝒪)` is zero. -/
theorem thm14_15 [NoncompactSpace X] {Y Y' : Opens X} (hrel : IsRelCompactIn (Y : Set X) (Y' : Set X)) (h : Y ≤ Y') :
    h1RestrictImage (modO X) Y Y' h = ⊥ := by
  sorry

/-- **Corollary 14.16** (Ch. 2 §14, F1:5163). Let `X` be a non-compact Riemann surface and `Y ⋐ Y′ ⊆ X` open. For every
`ω ∈ ℰ^{0,1}(Y′)` there is `f ∈ 𝓔(Y)` with `d″f = ω|Y`. -/
theorem cor14_16 [NoncompactSpace X] {Y Y' : Set X} (hY : IsOpen Y) (hY' : IsOpen Y') (hrel : IsRelCompactIn Y Y')
    {w : Form1 X} (hw : w.IsFormOn Y') (hs : w.IsSmoothOn Y') (h01 : w.IsType01On Y') :
    ∃ f : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f Y ∧ Form1.EqOn (dFormBar f) w Y := by
  sorry

end RiemannSurface

end Forster1981
