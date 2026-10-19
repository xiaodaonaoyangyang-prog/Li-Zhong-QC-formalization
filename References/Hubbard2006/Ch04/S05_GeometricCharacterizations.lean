import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.5: Geometric characterizations of quasiconformal maps (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 3771–4240.

**Conventions.** A triple of points is a map `a : Fin 3 → ℂ`; the triples considered are injective (three distinct
points: for coinciding points the quotient in the skew has junk value `0`). A modulus function `h` is a monotone
increasing continuous function `[1, ∞) → [1, ∞)` (`IsModulusFn`). The quasiconformal maps are `LiZhongQC.IsKQC` (they
preserve orientation, as in Hubbard's Definition 4.1.1: `|∂f/∂z̄| ≤ k |∂f/∂z|` forces `Jac ≥ 0`).

* Def. 4.5.1 (the skew of a triple; quasisymmetric mapping with modulus `h`) — `skew`, `IsModulusFn`, `IsSkewQS`
* Prop. 4.5.3 (1) (composition of quasisymmetric maps has modulus `max (h₂ ∘ h₁) (h₁ ∘ h₂)`, corrected) — `prop4_5_3_a`
* Prop. 4.5.3 (2) (the inverse of a quasisymmetric map is quasisymmetric with the same modulus) — `prop4_5_3_b`
* Thm 4.5.4 (a) (quasisymmetric and orientation preserving implies `K`-quasiconformal, `K` depending only on `h`) —
  `thm4_5_4_a`
* Thm 4.5.4 (b) (`K`-quasiconformal implies quasisymmetric with a modulus `h` depending only on `K`) — `thm4_5_4_b`
* Cor. 4.5.10 (1) (composition of quasiconformal maps is `K₁K₂`-quasiconformal) — `cor4_5_10_a`
* Cor. 4.5.10 (2) (the inverse of a `K`-quasiconformal map is `K`-quasiconformal) — `cor4_5_10_b`
* Cor. 4.5.11 (skew of triangles with skew `≤ 3` controls quasiconformality, `K = 3C²/π`) — `cor4_5_11`
* Def. 4.5.13 (labeled quasisymmetry of modulus `η`, metric spaces) — `IsLabeledQS`
* Prop. 4.5.14 (a homeomorphism of open sets is `K`-quasiconformal iff locally labeled quasisymmetric with `η`
  depending only on `K`) — `IsLocallyLabeledQS`, `prop4_5_14_a`, `prop4_5_14_b`
* Lemma 4.5.5–4.5.9, 4.5.12, 4.5.15 (annularity, area and diameter estimates, triangle lemmas) — omitted: proof step
* Remark 4.5.2 (1)–(2), Exercises 4.5.6–4.5.8 — omitted: exercise
-/

open Set
open scoped ENNReal Real

namespace Hubbard2006

open LiZhongQC

/-- **The skew of a triple of points** (equation (4.5.1), H1:3777): the supremum, over the six permutations, of
`|a_i − a_j| / |a_i − a_k|` (long side over short side). *Junk:* the quotient is `0` when two points coincide;
every statement uses injective triples. -/
noncomputable def skew (a : Fin 3 → ℂ) : ℝ :=
  ⨆ σ : Equiv.Perm (Fin 3), ‖a (σ 0) - a (σ 1)‖ / ‖a (σ 0) - a (σ 2)‖

/-- **A modulus function** (Definition 4.5.1, H1:3785): a monotone increasing continuous function
`h : [1, ∞) → [1, ∞)`. -/
def IsModulusFn (h : ℝ → ℝ) : Prop :=
  MonotoneOn h (Ici 1) ∧ ContinuousOn h (Ici 1) ∧ MapsTo h (Ici 1) (Ici 1)

/-- **Quasisymmetric mapping with modulus `h`** (Definition 4.5.1, H1:3785). `f : U → V` is a homeomorphism and (1)
every `u ∈ U` has a neighbourhood `D_u ⊂ U` on which `skew (f a, f b, f c) ≤ h (skew (a, b, c))` for all triples of
distinct points of `D_u`, and (2) the same holds for the inverse on neighbourhoods `D_v ⊂ V`. -/
def IsSkewQS (h : ℝ → ℝ) (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  IsHomeomorphOnto f U V ∧
    (∀ u ∈ U, ∃ D : Set ℂ, IsOpen D ∧ u ∈ D ∧ D ⊆ U ∧ ∀ a : Fin 3 → ℂ, (∀ i, a i ∈ D) →
      Function.Injective a → skew (f ∘ a) ≤ h (skew a)) ∧
    (∀ v ∈ V, ∃ D : Set ℂ, IsOpen D ∧ v ∈ D ∧ D ⊆ V ∧ ∀ a : Fin 3 → ℂ, (∀ i, a i ∈ D) →
      Function.Injective a → skew (Function.invFunOn f U ∘ a) ≤ h (skew a))

/-- **Proposition 4.5.3 (1)** (H1:3814). If `f : U → V` is quasisymmetric with modulus `h₁` and `g : V → W` with modulus
`h₂`, then `g ∘ f : U → W` is quasisymmetric with modulus `h₂ ∘ h₁`. *Correction:* `IsSkewQS` bounds the inverse by the same
modulus, and the inverse of `g ∘ f` is `f⁻¹ ∘ g⁻¹`, controlled by `h₁ ∘ h₂`, so the modulus of the composite is stated as
`max (h₂ ∘ h₁) (h₁ ∘ h₂)` (a modulus function by monotonicity; the book's Remark 4.5.2 (1) derives the inverse clause
from the forward one, which gives `h₂ ∘ h₁` only on the forward clause). -/
theorem prop4_5_3_a {h₁ h₂ : ℝ → ℝ} (hh₁ : IsModulusFn h₁) (hh₂ : IsModulusFn h₂) {f g : ℂ → ℂ} {U V W : Set ℂ}
    (hf : IsSkewQS h₁ f U V) (hg : IsSkewQS h₂ g V W) : IsSkewQS (fun s => max (h₂ (h₁ s)) (h₁ (h₂ s))) (g ∘ f) U W := by
  sorry

/-- **Proposition 4.5.3 (2)** (H1:3814). If `f : U → V` is quasisymmetric with modulus `h`, so is its inverse
`f⁻¹ : V → U`. -/
theorem prop4_5_3_b {h : ℝ → ℝ} {f : ℂ → ℂ} {U V : Set ℂ} (hf : IsSkewQS h f U V) :
    IsSkewQS h (Function.invFunOn f U) V U := by
  sorry

/-- **Theorem 4.5.4 (quasisymmetric ⟹ quasiconformal)** (H1:3822). For a modulus function `h` there is `K`, depending
only on `h`, such that every orientation preserving homeomorphism `f : U → V` of open sets of `ℂ` that is
quasisymmetric with modulus `h` is `K`-quasiconformal. *Correction to the book:* the orientation hypothesis is
needed (the conjugation `z ↦ z̄` is quasisymmetric with modulus `h = id` and is not quasiconformal in the sense of
Definition 4.1.1, since `|∂f/∂z̄| ≤ k |∂f/∂z|` forces orientation preservation). -/
theorem thm4_5_4_a {h : ℝ → ℝ} (hh : IsModulusFn h) :
    ∃ K : ℝ, ∀ (U V : Set ℂ) (f : ℂ → ℂ), IsOpen U → IsOpen V → IsSkewQS h f U V → IsSensePreserving f U →
      IsKQC f U K := by
  sorry

/-- **Theorem 4.5.4 (quasiconformal ⟹ quasisymmetric)** (H1:3822). For `K ≥ 1` there is a modulus function `h`,
depending only on `K`, such that every `K`-quasiconformal homeomorphism `f : U → V` of open sets of `ℂ` is
quasisymmetric with modulus `h`. -/
theorem thm4_5_4_b {K : ℝ} (hK : 1 ≤ K) :
    ∃ h : ℝ → ℝ, IsModulusFn h ∧ ∀ (U V : Set ℂ) (f : ℂ → ℂ), IsOpen U → IsOpen V → f '' U = V → IsKQC f U K →
      IsSkewQS h f U V := by
  sorry

/-- **Corollary 4.5.10 (1)** (H1:4069). If `f : U → V` is `K₁`-quasiconformal and `g : V → W` is
`K₂`-quasiconformal, then `g ∘ f : U → W` is `K₁K₂`-quasiconformal (planar open sets, not necessarily connected: the
installed `LehtoVirtanen1973.kqc_comp` is for domains of `ℂ̂`, a near miss). -/
theorem cor4_5_10_a {U V : Set ℂ} {f g : ℂ → ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f U K₁) (hV : f '' U = V)
    (hg : IsKQC g V K₂) : IsKQC (g ∘ f) U (K₁ * K₂) := by
  sorry

/-- **Corollary 4.5.10 (2)** (H1:4069). If `f : U → V` is `K`-quasiconformal, so is `f⁻¹ : V → U`. -/
theorem cor4_5_10_b {U V : Set ℂ} {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f U K) (hV : f '' U = V) :
    IsKQC (Function.invFunOn f U) V K := by
  sorry

/-- **Corollary 4.5.11** (H1:4080). Let `U`, `V ⊂ ℂ` be open, `f : U → V` an orientation preserving homeomorphism,
and `C` a constant such that every `u ∈ U` has a neighbourhood `D_u` in which every triple of distinct points `a`
with `skew a ≤ 3` has `skew (f a) ≤ C`. Then `f` is `K`-quasiconformal with `K = 3 C² / π` (the book's "skew
`(a, b, d) ≤ 3`" is a misprint for the triple `(a, b, c)`). -/
theorem cor4_5_11 {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {f : ℂ → ℂ} (hhom : IsHomeomorphOnto f U V)
    (hsp : IsSensePreserving f U) {C : ℝ}
    (hC : ∀ u ∈ U, ∃ D : Set ℂ, IsOpen D ∧ u ∈ D ∧ D ⊆ U ∧ ∀ a : Fin 3 → ℂ, (∀ i, a i ∈ D) →
      Function.Injective a → skew a ≤ 3 → skew (f ∘ a) ≤ C) :
    IsKQC f U (3 / π * C ^ 2) := by
  sorry

/-- **Labeled quasisymmetry of modulus `η`** (Definition 4.5.13, H1:4114): for a homeomorphism
`η : [0, ∞) → [0, ∞)` and metric spaces `X`, `Y`, a map `f : X → Y` is L-quasisymmetric of modulus `η` if
`d(f x, f y) / d(f x, f z) ≤ η (d(x, y) / d(x, z))` for all distinct `x`, `y`, `z`. -/
def IsLabeledQS {X Y : Type*} [MetricSpace X] [MetricSpace Y] (η : ℝ → ℝ) (f : X → Y) : Prop :=
  Continuous η ∧ StrictMonoOn η (Ici 0) ∧ η 0 = 0 ∧ Filter.Tendsto η Filter.atTop Filter.atTop ∧
    ∀ x y z : X, x ≠ y → x ≠ z → y ≠ z →
      dist (f x) (f y) / dist (f x) (f z) ≤ η (dist x y / dist x z)

/-- **Locally labeled quasisymmetric of modulus `η`** (the planar notion of Proposition 4.5.14): every point of `U`
has an open neighbourhood `W ⊂ U` on which `|f x − f y| / |f x − f z| ≤ η (|x − y| / |x − z|)` for all distinct
`x`, `y`, `z ∈ W`. *Correction to the book:* Proposition 4.5.14 must be read with this local notion (the "`W`" of
Definition 4.5.13), because the global notion fails for `K`-quasiconformal maps of open sets, as Remark 4.5.2 (2)
itself shows with the conformal map of a disc onto a slit disc. -/
def IsLocallyLabeledQS (η : ℝ → ℝ) (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  Continuous η ∧ StrictMonoOn η (Ici 0) ∧ η 0 = 0 ∧ Filter.Tendsto η Filter.atTop Filter.atTop ∧
    ∀ u ∈ U, ∃ W : Set ℂ, IsOpen W ∧ u ∈ W ∧ W ⊆ U ∧ ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, x ≠ y → x ≠ z → y ≠ z →
      ‖f x - f y‖ / ‖f x - f z‖ ≤ η (‖x - y‖ / ‖x - z‖)

/-- **Proposition 4.5.14 (a)** (H1:4126). A `K`-quasiconformal homeomorphism of open sets of `ℂ` is locally labeled
quasisymmetric with a modulus `η` depending only on `K`. -/
theorem prop4_5_14_a {K : ℝ} (hK : 1 ≤ K) :
    ∃ η : ℝ → ℝ, ∀ (U : Set ℂ) (f : ℂ → ℂ), IsOpen U → IsKQC f U K → IsLocallyLabeledQS η f U := by
  sorry

/-- **Proposition 4.5.14 (b)** (H1:4126). Conversely, for a modulus `η` there is `K` such that every orientation
preserving homeomorphism of open sets of `ℂ` that is locally labeled quasisymmetric of modulus `η` is
`K`-quasiconformal. -/
theorem prop4_5_14_b (η : ℝ → ℝ) :
    ∃ K : ℝ, ∀ (U V : Set ℂ) (f : ℂ → ℂ), IsOpen U → IsOpen V → IsHomeomorphOnto f U V →
      IsSensePreserving f U → IsLocallyLabeledQS η f U → IsKQC f U K := by
  sorry

end Hubbard2006
