import References.Forster1981.Ch02.S18_FunctionsAndDifferentialFormsWithPrescribedPrincipalParts

/-!
# Forster, Chapter 2 §19: Harmonic differential forms

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (`full.md` F1:6852–7163).

Conventions (ruling B0.9): complex conjugation `ω̄`, the star operator `*ω` and the real part `Re ω` of 1-forms are relations
(`Form1.IsConjOf`, `Form1.IsStarOf`, `Form1.IsRealPartOf`), which avoids the proof of the transformation law; in the preferred
charts, for `ω = a dz + b dz̄`: `ω̄ = b̄ dz + ā dz̄`, `*ω = −i b̄ dz + i ā dz̄` (`*ω = i(ω̄₁ − ω̄₂)`), `Re ω = ½(ω + ω̄)`.
`Ω̄(X)` and `Harm¹(X)` are spans. The scalar product `⟨ω₁, ω₂⟩ = ∬_X ω₁ ∧ *ω₂` is used only inside `HasIntegral2` (the
relation `InnerForms`), with `ω ∧ *ω = 2(|f|² + |g|²) dx ∧ dy`. Decompositions are `⊔` plus `Disjoint` plus orthogonality
(`SubspacesOrthogonal`). Spaces of forms are the global spaces of representatives (`smoothForms1On X ⊤`, `holFormsOn X ⊤`, …);
`d′ℰ(X)`, `d″ℰ(X)`, `dℰ(X)` are spans of the images of `smoothFunOn X ⊤`.

* Paragraph 19.1 (complex conjugation, F1:6856) — `Form1.IsConjOf`, `Form1.IsReal`, `Form1.IsRealPartOf`, `antiHolForms`
* Paragraph 19.2 (the `*`-operator, F1:6870) — `Form1.IsStarOf`, `para19_2_a`, `para19_2_b`, `para19_2_c`, `para19_2_d`
* Paragraph 19.3 (harmonic forms, F1:6894) — `Form1.IsHarmonic`, `harmForms`, `thm19_3`, `para19_3_a`, `para19_3_b`
* Theorem 19.4 (F1:6928) — `thm19_4`
* Paragraph 19.5 (scalar products, F1:6934) — `InnerForms`, `para19_5`
* Lemma 19.6 (F1:6966) — `FormsOrthogonal`, `SubspacesOrthogonal`, `dHolImage`, `starSpan`, `lemma19_6_a`, `lemma19_6_b`
* Corollary 19.7 (F1:7008) — `cor19_7_a`, `cor19_7_b`
* Corollary 19.8 (F1:7012) — `cor19_8_a`, `cor19_8_b`
* Theorem 19.9 (F1:7022) — `thm19_9`
* Corollary 19.10 (F1:7036) — `cor19_10`
* Theorem 19.11 (F1:7044) — `thm19_11`
* Theorem 19.12 (F1:7058) — `thm19_12`
* Corollary 19.13 (F1:7082) — `cor19_13`
* Theorem 19.14 (de Rham–Hodge, F1:7090) — `thm19_14`

Omitted (U−): the integral identities of 19.1, the decomposition claim of 19.2, the other claims of 19.5, the remarks of 19.10
and 19.14.
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Complex conjugation of 1-forms** (19.1, Ch. 2 §19, F1:6856): `w′ = w̄` where `conj (a dz + b dz̄) = b̄ dz + ā dz̄`. -/
def Form1.IsConjOf (w' w : Form1 X) : Prop :=
  ∀ x z, w'.1 x z = starRingEnd ℂ (w.2 x z) ∧ w'.2 x z = starRingEnd ℂ (w.1 x z)

/-- **Real 1-forms** (19.1, Ch. 2 §19, F1:6856): `ω = ω̄`. -/
def Form1.IsReal (w : Form1 X) : Prop := w.IsConjOf w

/-- **The real part** (19.1, Ch. 2 §19, F1:6856): `v = Re w = ½(w + w̄)`. -/
def Form1.IsRealPartOf (v w : Form1 X) : Prop :=
  ∀ x z, v.1 x z = (w.1 x z + starRingEnd ℂ (w.2 x z)) / 2 ∧ v.2 x z = (w.2 x z + starRingEnd ℂ (w.1 x z)) / 2

/-- **Anti-holomorphic forms** `Ω̄(X)` (19.1, Ch. 2 §19, F1:6856): the span of the conjugates of holomorphic 1-forms. -/
def antiHolForms (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ {v | ∃ w ∈ holFormsOn X ⊤, v.IsConjOf w}

/-- **The `*`-operator** (19.2, Ch. 2 §19, F1:6870): `s = *w` where `*(a dz + b dz̄) = i(ω̄₁ − ω̄₂) = −i b̄ dz + i ā dz̄`. -/
def Form1.IsStarOf (s w : Form1 X) : Prop :=
  ∀ x z, s.1 x z = -Complex.I * starRingEnd ℂ (w.2 x z) ∧ s.2 x z = Complex.I * starRingEnd ℂ (w.1 x z)

/-- **Harmonic 1-forms** (19.3, Ch. 2 §19, F1:6894): differentiable `ω` with `dω = d*ω = 0`. -/
def Form1.IsHarmonic (w : Form1 X) : Prop :=
  w ∈ smoothForms1On X ⊤ ∧ Form2.VanishOn w.d ⊤ ∧ ∃ s : Form1 X, s.IsStarOf w ∧ Form2.VanishOn s.d ⊤

/-- **The space `Harm¹(X)`** of harmonic 1-forms (19.3, Ch. 2 §19, F1:6894), as a span. -/
def harmForms (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ {w | w.IsHarmonic}

/-- **The scalar product** `⟨ω₁, ω₂⟩ = ∬_X ω₁ ∧ *ω₂ = v` (19.5, Ch. 2 §19, F1:6934). -/
def InnerForms (w₁ w₂ : Form1 X) (v : ℂ) : Prop := ∃ s, s.IsStarOf w₂ ∧ HasIntegral2 (Form1.wedge w₁ s) v

/-- **Orthogonality** of two 1-forms (19.6, Ch. 2 §19, F1:6966): `⟨ω₁, ω₂⟩ = 0`. -/
def FormsOrthogonal (w₁ w₂ : Form1 X) : Prop := InnerForms w₁ w₂ 0

/-- **Orthogonality of subspaces** (19.6, Ch. 2 §19, F1:6966). -/
def SubspacesOrthogonal (A B : Submodule ℂ (Form1 X)) : Prop := ∀ u ∈ A, ∀ v ∈ B, FormsOrthogonal u v

/-- The space `d′ℰ(X)`. -/
def dHolImage (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ (dFormHol '' (smoothFunOn X ⊤ : Set (X → ℂ)))

/-- The space `*A = {*ω : ω ∈ A}` for a subspace `A` of 1-forms. -/
def starSpan (A : Submodule ℂ (Form1 X)) : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ {s | ∃ w ∈ A, s.IsStarOf w}

end Defs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Paragraph 19.2(a)** (Ch. 2 §19, F1:6870). `** ω = −ω` and `conj (*ω) = * ω̄`. -/
theorem para19_2_a {w s s' c sc : Form1 X} (hs : s.IsStarOf w) (hss : s'.IsStarOf s) (hc : c.IsConjOf w)
    (hsc : sc.IsStarOf c) : s' = -w ∧ sc.IsConjOf s := by
  sorry

/-- **Paragraph 19.2(b)** (Ch. 2 §19, F1:6870). For `ω₁ ∈ ℰ^{1,0}(X)`, `ω₂ ∈ ℰ^{0,1}(X)`:
`d*(ω₁ + ω₂) = i d′ω̄₁ − i d″ω̄₂`. -/
theorem para19_2_b {w₁ w₂ s c₁ c₂ : Form1 X} (h₁ : w₁ ∈ smoothForms10On X ⊤) (h₂ : w₂ ∈ smoothForms01On X ⊤)
    (hs : s.IsStarOf (w₁ + w₂)) (hc₁ : c₁.IsConjOf w₁) (hc₂ : c₂.IsConjOf w₂) :
    Form2.EqOn s.d (Complex.I • Form1.dHol c₁ - Complex.I • Form1.dBar c₂) ⊤ := by
  sorry

/-- **Paragraph 19.2(c)** (Ch. 2 §19, F1:6870). For `f ∈ 𝓔(X)`: `*d′f = i d″f̄` and `*d″f = −i d′f̄`. -/
theorem para19_2_c {f : X → ℂ} (hf : f ∈ smoothFunOn X ⊤) {s₁ s₂ : Form1 X} (h₁ : s₁.IsStarOf (dFormHol f))
    (h₂ : s₂.IsStarOf (dFormBar f)) :
    Form1.EqOn s₁ (Complex.I • dFormBar (fun x => starRingEnd ℂ (f x))) ⊤ ∧
      Form1.EqOn s₂ ((-Complex.I) • dFormHol (fun x => starRingEnd ℂ (f x))) ⊤ := by
  sorry

/-- **Paragraph 19.2(d)** (Ch. 2 §19, F1:6870). For `f ∈ 𝓔(X)`: `d*df = 2i d′d″f̄`. -/
theorem para19_2_d {f : X → ℂ} (hf : f ∈ smoothFunOn X ⊤) {s : Form1 X} (hs : s.IsStarOf (dForm f)) :
    Form2.EqOn s.d ((2 * Complex.I) • Form1.dHol (dFormBar fun x => starRingEnd ℂ (f x))) ⊤ := by
  sorry

/-- **Theorem 19.3** (Ch. 2 §19, F1:6894). For `ω ∈ ℰ^(1)(X)` the following are equivalent: (i) `ω` is harmonic; (ii)
`d′ω = d″ω = 0`; (iii) `ω = ω₁ + ω₂` with `ω₁ ∈ Ω(X)`, `ω₂ ∈ Ω̄(X)`; (iv) near every point `a`, `ω = df` for a harmonic
function `f` on a neighbourhood of `a`. -/
theorem thm19_3 {w : Form1 X} (hw : w ∈ smoothForms1On X ⊤) :
    List.TFAE [w.IsHarmonic, Form2.VanishOn w.dHol ⊤ ∧ Form2.VanishOn w.dBar ⊤,
      ∃ w₁ ∈ holFormsOn X ⊤, ∃ w₂ ∈ antiHolForms X, w = w₁ + w₂,
      ∀ a : X, ∃ U ∈ 𝓝 a, ∃ f : X → ℂ, IsHarmonicOn f U ∧ Form1.EqOn w (dForm f) U] := by
  sorry

/-- **Paragraph 19.3(a)** (Ch. 2 §19, F1:6894). `Harm¹(X) = Ω(X) ⊕ Ω̄(X)`. -/
theorem para19_3_a : harmForms X = holFormsOn X ⊤ ⊔ antiHolForms X ∧ Disjoint (holFormsOn X ⊤) (antiHolForms X) := by
  sorry

/-- **Paragraph 19.3(b)** (Ch. 2 §19, F1:6894). On a compact Riemann surface of genus `g`, `dim Harm¹(X) = 2g`. -/
theorem para19_3_b [CompactSpace X] : Module.finrank ℂ (harmForms X) = 2 * genus X := by
  sorry

/-- **Theorem 19.4** (Ch. 2 §19, F1:6928). Every real harmonic 1-form `σ ∈ Harm¹(X)` is the real part of exactly one
holomorphic 1-form `ω ∈ Ω(X)`. -/
theorem thm19_4 {σ : Form1 X} (hσ : σ ∈ harmForms X) (hr : σ.IsReal) :
    ∃! w : Form1 X, w ∈ holFormsOn X ⊤ ∧ σ.IsRealPartOf w := by
  sorry

/-- **Paragraph 19.5** (Ch. 2 §19, F1:6934). On a compact Riemann surface the scalar product is positive definite:
`⟨ω, ω⟩ ≥ 0`, with `⟨ω, ω⟩ = 0` only for `ω = 0`. -/
theorem para19_5 [CompactSpace X] {w : Form1 X} (hw : w ∈ smoothForms1On X ⊤) {v : ℂ} (hv : InnerForms w w v) :
    (0 ≤ v.re ∧ v.im = 0) ∧ (v = 0 → w.VanishOn ⊤) := by
  sorry

/-- **Lemma 19.6(a)** (Ch. 2 §19, F1:6966). On a compact Riemann surface, `d′ℰ(X)`, `d″ℰ(X)`, `Ω(X)` and `Ω̄(X)` are
pairwise orthogonal vector subspaces of `ℰ^(1)(X)`. -/
theorem lemma19_6_a [CompactSpace X] :
    SubspacesOrthogonal (dHolImage X) (dBarImage X) ∧ SubspacesOrthogonal (dHolImage X) (holFormsOn X ⊤) ∧
      SubspacesOrthogonal (dHolImage X) (antiHolForms X) ∧ SubspacesOrthogonal (dBarImage X) (holFormsOn X ⊤) ∧
      SubspacesOrthogonal (dBarImage X) (antiHolForms X) ∧ SubspacesOrthogonal (holFormsOn X ⊤) (antiHolForms X) := by
  sorry

/-- **Lemma 19.6(b)** (Ch. 2 §19, F1:6966). On a compact Riemann surface, `dℰ(X)` and `*dℰ(X)` are orthogonal subspaces
and `dℰ(X) ⊕ *dℰ(X) = d′ℰ(X) ⊕ d″ℰ(X)`. -/
theorem lemma19_6_b [CompactSpace X] :
    SubspacesOrthogonal (exactForms X) (starSpan (exactForms X)) ∧
      Disjoint (exactForms X) (starSpan (exactForms X)) ∧ Disjoint (dHolImage X) (dBarImage X) ∧
      exactForms X ⊔ starSpan (exactForms X) = dHolImage X ⊔ dBarImage X := by
  sorry

/-- **Corollary 19.7(a)** (Ch. 2 §19, F1:7008). On a compact Riemann surface every exact harmonic 1-form vanishes. -/
theorem cor19_7_a [CompactSpace X] {σ : Form1 X} (h₁ : σ ∈ harmForms X) (h₂ : σ ∈ exactForms X) : σ.VanishOn ⊤ := by
  sorry

/-- **Corollary 19.7(b)** (Ch. 2 §19, F1:7008). On a compact Riemann surface every harmonic function is constant. -/
theorem cor19_7_b [CompactSpace X] {f : X → ℂ} (hf : IsHarmonicOn f ⊤) : ∃ c : ℂ, ∀ x, f x = c := by
  sorry

/-- **Corollary 19.8(a)** (Ch. 2 §19, F1:7012). On a compact Riemann surface, a harmonic 1-form `σ` with
`∫_γ σ = 0` for every closed curve `γ` vanishes. -/
theorem cor19_8_a [CompactSpace X] {σ : Form1 X} (hσ : σ ∈ harmForms X)
    (hp : ∀ (x₀ : X) (γ : FundamentalGroup X x₀), period σ γ = 0) : σ.VanishOn ⊤ := by
  sorry

/-- **Corollary 19.8(b)** (Ch. 2 §19, F1:7012). On a compact Riemann surface, a holomorphic 1-form `ω` with
`Re ∫_γ ω = 0` for every closed curve `γ` vanishes. -/
theorem cor19_8_b [CompactSpace X] {w : Form1 X} (hw : w ∈ holFormsOn X ⊤)
    (hp : ∀ (x₀ : X) (γ : FundamentalGroup X x₀), (period w γ).re = 0) : w.VanishOn ⊤ := by
  sorry

/-- **Theorem 19.9** (Ch. 2 §19, F1:7022). On a compact Riemann surface there is an orthogonal decomposition
`ℰ^{0,1}(X) = d″ℰ(X) ⊕ Ω̄(X)`. -/
theorem thm19_9 [CompactSpace X] :
    smoothForms01On X ⊤ = dBarImage X ⊔ antiHolForms X ∧ Disjoint (dBarImage X) (antiHolForms X) ∧
      SubspacesOrthogonal (dBarImage X) (antiHolForms X) := by
  sorry

/-- **Corollary 19.10** (Ch. 2 §19, F1:7036). On a compact Riemann surface, for `σ ∈ ℰ^{0,1}(X)` the equation `d″f = σ` has
a solution `f ∈ 𝓔(X)` if and only if `∬_X σ ∧ ω = 0` for every `ω ∈ Ω(X)`. -/
theorem cor19_10 [CompactSpace X] {σ : Form1 X} (hσ : σ ∈ smoothForms01On X ⊤) :
    (∃ f ∈ smoothFunOn X ⊤, Form1.EqOn (dFormBar f) σ ⊤) ↔
      ∀ s ∈ holFormsOn X ⊤, HasIntegral2 (Form1.wedge σ s) 0 := by
  sorry

/-- **Theorem 19.11** (Ch. 2 §19, F1:7044). On a compact Riemann surface there is an orthogonal decomposition
`ℰ^(1)(X) = *dℰ(X) ⊕ dℰ(X) ⊕ Harm¹(X)`. -/
theorem thm19_11 [CompactSpace X] :
    smoothForms1On X ⊤ = starSpan (exactForms X) ⊔ exactForms X ⊔ harmForms X ∧
      Disjoint (starSpan (exactForms X)) (exactForms X) ∧ Disjoint (starSpan (exactForms X) ⊔ exactForms X) (harmForms X) ∧
      SubspacesOrthogonal (starSpan (exactForms X)) (exactForms X) ∧
      SubspacesOrthogonal (starSpan (exactForms X)) (harmForms X) ∧ SubspacesOrthogonal (exactForms X) (harmForms X) := by
  sorry

/-- **Theorem 19.12** (Ch. 2 §19, F1:7058). On a compact Riemann surface, `Ker (d : ℰ^(1)(X) → ℰ^(2)(X)) = dℰ(X) ⊕ Harm¹(X)`. -/
theorem thm19_12 [CompactSpace X] :
    {w : Form1 X | w ∈ smoothForms1On X ⊤ ∧ Form2.VanishOn w.d ⊤} = ↑(exactForms X ⊔ harmForms X) ∧
      Disjoint (exactForms X) (harmForms X) := by
  sorry

/-- **Corollary 19.13** (Ch. 2 §19, F1:7082). On a compact Riemann surface, `σ ∈ ℰ^(1)(X)` is exact if and only if
`∬_X σ ∧ ω = 0` for every closed 1-form `ω ∈ ℰ^(1)(X)`. -/
theorem cor19_13 [CompactSpace X] {σ : Form1 X} (hσ : σ ∈ smoothForms1On X ⊤) :
    σ ∈ exactForms X ↔
      ∀ s ∈ smoothForms1On X ⊤, Form2.VanishOn s.d ⊤ → HasIntegral2 (Form1.wedge σ s) 0 := by
  sorry

/-- **Theorem 19.14** (de Rham–Hodge, Ch. 2 §19, F1:7090). On a compact Riemann surface,
`H¹(X, ℂ) ≅ Rh¹(X) ≅ Harm¹(X)`. -/
theorem thm19_14 [CompactSpace X] :
    Nonempty (H1 (modC X) ⊤ ≃ₗ[ℂ] deRham1 X) ∧ Nonempty (deRham1 X ≃ₗ[ℂ] ↥(harmForms X)) := by
  sorry

end Statements

end Forster1981
