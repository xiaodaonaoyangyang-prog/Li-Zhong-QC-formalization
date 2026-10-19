import References.GardinerLakic2000.Ch13.S04_BoundednessOfNorm

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.5 Schiffer and Beltrami variations

Source `teichmuller.txt`, lines 9687–9728.

* Lemma 3 (sewing in a quasidisc, l. 9695) — `lemma13_3`
* Definition (local parameter `z` on `V`, `z(V) = U`, l. 9701) — `IsUnitLocalParameter`
* Definition (the quasidisc `W`, `|w(z(p))| < 2ε`, l. 9711) — `schifferQuasidisc`
* Definition (Schiffer interior variation `S_ε`, l. 9701–9709) — `IsSchifferVariation`
* Definition (Beltrami variation `S_{μ(ε)}`, l. 9711) — `IsBeltramiVariation`
* Theorem 5 (l. 9713) — `thm13_5`

Not items (DESIGN §3): the introduction (l. 9688, motivation), the buttonhole picture (l. 9699), the prime ends
`z±`, `J±` (l. 9701, steps of the construction).

**Modelling (calibration D0.6).** The sewn surfaces are characterized, not constructed (the root's deferred list:
"constructions replaced by characterizing predicates"). A variation is a marked surface `F : S → S′` (an A:
`RSBundle` with a quasiconformal homeomorphism) that is conformal off `W̄` and whose chart on the new piece is the
book's map. In Lemma 3, "`Sᵢ` is `S` with `W` replaced by `Wᵢ` along `hᵢ`" is: `fᵢ` is quasiconformal and conformal
off `W̄`, and some `ωᵢ : Sᵢ → ℂ` is injective and continuous on `fᵢ(W̄)` and holomorphic on `fᵢ(W)` (the identity
chart of the sewn-in `Wᵢ`), with `Wᵢ = ωᵢ(fᵢ(W))` a quasidisc and `hᵢ = ωᵢ ∘ fᵢ` on `∂W`. `W` is a quasidisc in a
chart of `S`.

For the Schiffer variation, `w(z)` is the branch of `z = w − ε²w⁻¹` with `|w| > ε` on `U ∖ I`. The level set
`|w| = 2ε` is the ellipse `z = (3ε/2) cos θ + i (5ε/2) sin θ`, so
`W = {p ∈ V : (Re z / (3ε/2))² + (Im z / (5ε/2))² < 1}`.
`S_ε` carries the chart `w̃` on `F(V) = V_ε`, with `w̃ ∘ F = w ∘ z` on `V ∖ W`, and `w̃(F(W))` is the disc
`|w| < 2ε` (the attached `D_ε` together with the image of `W ∖ J`). `S_{μ(ε)}` carries the chart `ζ` of the new disc,
with `ζ ∘ F = z + ¼ z̄` on `W̄`. The book leaves the range of `ε` implicit; `0 < ε < 2/5` is the range for which
`W̄ ⊆ V` [reading].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS IsKQuasidisc unitDisc)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- **Definition** (§13.5, l. 9701). `z` is a local parameter on the open set `V` with `z(V) = U`, the unit disc: `z`
is holomorphic and injective on `V`. -/
def IsUnitLocalParameter (V : Set S) (z : S → ℂ) : Prop :=
  IsOpen V ∧ InjOn z V ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) z V ∧ z '' V = unitDisc

/-- **Definition** (§13.5, l. 9711). The quasidisc `W = {p ∈ V : |w(z(p))| < 2ε}`, bounded in the `z`-plane by the
ellipse with semi-axes `3ε/2` and `5ε/2`. -/
def schifferQuasidisc (V : Set S) (z : S → ℂ) (ε : ℝ) : Set S :=
  V ∩ z ⁻¹' {u : ℂ | (u.re / (3 * ε / 2)) ^ 2 + (u.im / (5 * ε / 2)) ^ 2 < 1}

/-- **Definition** (Schiffer interior variation, §13.5, l. 9701–9709). `F : S → S_ε` is the Schiffer interior variation
of `S` by attaching the disc `D_ε` along `J = z⁻¹([−2iε, 2iε])`: `F` is quasiconformal and conformal off `W̄`, and the
chart `w̃` of `S_ε` on `F(V)` satisfies `w̃ − ε² w̃⁻¹ = z` (with `|w̃| ≥ 2ε`) on `F(V ∖ W)` and maps `F(W)` onto
the disc `|w| < 2ε`. -/
def IsSchifferVariation (V : Set S) (z : S → ℂ) (ε : ℝ) {Y : RSBundle.{u}} (F : S ≃ₜ Y.carrier) : Prop :=
  IsQCRS F ∧ (∀ p ∉ closure (schifferQuasidisc V z ε), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F p) ∧
    ∃ wt : Y.carrier → ℂ, InjOn wt (F '' V) ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) wt (F '' V) ∧
      (∀ p ∈ V \ schifferQuasidisc V z ε, wt (F p) - (ε : ℂ) ^ 2 / wt (F p) = z p ∧ 2 * ε ≤ ‖wt (F p)‖) ∧
      wt '' (F '' schifferQuasidisc V z ε) = ball 0 (2 * ε)

/-- **Definition** (Beltrami variation, §13.5, l. 9711). `F : S → S_{μ(ε)}` deletes the interior of `W` and attaches a
new disc with local parameter `ζ = z + ¼ z̄`: `F` is quasiconformal and conformal off `W̄`, and the chart `ζ` of the new
disc is injective and continuous on `F(W̄)`, holomorphic on `F(W)`, with `ζ ∘ F = z + ¼ z̄` on `W̄` (so the Beltrami
coefficient of `F` is `1/4` in `W` with respect to `z`). -/
def IsBeltramiVariation (V : Set S) (z : S → ℂ) (ε : ℝ) {Y : RSBundle.{u}} (F : S ≃ₜ Y.carrier) : Prop :=
  IsQCRS F ∧ (∀ p ∉ closure (schifferQuasidisc V z ε), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F p) ∧
    ∃ ζ : Y.carrier → ℂ, InjOn ζ (F '' closure (schifferQuasidisc V z ε)) ∧
      ContinuousOn ζ (F '' closure (schifferQuasidisc V z ε)) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) ζ (F '' schifferQuasidisc V z ε) ∧
      ∀ p ∈ closure (schifferQuasidisc V z ε), ζ (F p) = z p + conj (z p) / 4

variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Lemma 3** (§13.5, l. 9695). Let `W` be a quasidisc in `S` and let `fᵢ : S → Sᵢ` (`i = 0, 1`) replace `W` by the
quasidisc `Wᵢ` along the boundary map `hᵢ` (see the module docstring). If a conformal map `c` of `W₁` onto `W₀` has
`h₀⁻¹ ∘ c ∘ h₁ = id` on `∂W`, then `(f₀, S₀)` and `(f₁, S₁)` represent the same point of `T(S)`.
[CORRECTION/modelling] (leader -ea, from the skillor's F0 audit, 2026-10-06): `p` is now a Fuchsian uniformization
(`hp`), as in `lemma13_2`; for an unconstrained (e.g. constant) `p` the conclusion can fail. -/
theorem lemma13_3 (p : UpperHalfPlane → S) (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p)
    {W : Set S} {x₀ : S} (hWx : closure W ⊆ (chartAt ℂ x₀).source)
    (hW : ∃ K, IsKQuasidisc (chartAt ℂ x₀ '' W) K) {Y₀ Y₁ : RSBundle.{u}} {f₀ : S ≃ₜ Y₀.carrier}
    {f₁ : S ≃ₜ Y₁.carrier} (hf₀ : IsQCRS f₀) (hf₁ : IsQCRS f₁)
    (hc₀ : ∀ x ∉ closure W, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f₀ x)
    (hc₁ : ∀ x ∉ closure W, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f₁ x) {ω₀ : Y₀.carrier → ℂ} {ω₁ : Y₁.carrier → ℂ}
    (hω₀ : InjOn ω₀ (f₀ '' closure W) ∧ ContinuousOn ω₀ (f₀ '' closure W) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) ω₀ (f₀ '' W))
    (hω₁ : InjOn ω₁ (f₁ '' closure W) ∧ ContinuousOn ω₁ (f₁ '' closure W) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) ω₁ (f₁ '' W))
    (hW₀ : ∃ K, IsKQuasidisc (ω₀ '' (f₀ '' W)) K) (hW₁ : ∃ K, IsKQuasidisc (ω₁ '' (f₁ '' W)) K) {c : ℂ → ℂ}
    (hc : ContinuousOn c (closure (ω₁ '' (f₁ '' W))) ∧ DifferentiableOn ℂ c (ω₁ '' (f₁ '' W)) ∧
      InjOn c (ω₁ '' (f₁ '' W)) ∧ c '' (ω₁ '' (f₁ '' W)) = ω₀ '' (f₀ '' W))
    (hbd : ∀ x ∈ frontier W, c (ω₁ (f₁ x)) = ω₀ (f₀ x)) :
    IsTeichEquiv p f₁ f₀ := by
  sorry

/-- **Theorem 5** (§13.5, l. 9713). In `T(S)` the marked Riemann surfaces `S_{μ(ε)}` and `S_ε` represent the same
point: any Beltrami variation and any Schiffer variation for the same local parameter and `ε` are Teichmüller
equivalent.
[CORRECTION/modelling] (leader -ea, from the skillor's F0 audit, 2026-10-06): `p` is now a Fuchsian uniformization
(`hp`), as in `lemma13_2`; for an unconstrained (e.g. constant) `p` the conclusion can fail. -/
theorem thm13_5 (p : UpperHalfPlane → S) (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p)
    {V : Set S} {z : S → ℂ} (hz : IsUnitLocalParameter V z) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 2 / 5) {Y₀ Y₁ : RSBundle.{u}} {F₀ : S ≃ₜ Y₀.carrier} {F₁ : S ≃ₜ Y₁.carrier}
    (h₀ : IsBeltramiVariation V z ε F₀) (h₁ : IsSchifferVariation V z ε F₁) :
    IsTeichEquiv p F₁ F₀ := by
  sorry

end GardinerLakic2000
