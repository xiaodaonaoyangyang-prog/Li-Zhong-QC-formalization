import References.GardinerLakic2000.Ch05.S02_QuasiconformalIsotopies

/-!
# Gardiner–Lakic 2000, Ch. 5 §5.3 Isotopies over plane domains

Source `teichmuller.txt`, lines 5104–5143.

* Definition 7 (frontier equivalence, l. 5107) — `IsFrontierEquiv`
* Definition 8 (sphere equivalence, l. 5119) — `IsSphereEquiv`
* Theorem 5 (the five equivalences over a plane domain, l. 5128) — `thm5_5`
* Lemma 2 ([EM88], the lifts of spherically small paths are small, l. 5137) — `lemma5_2`

Not items (DESIGN §3): frontier and frontier closure (l. 5105; `frontier` and `closure` of the domain), the claims
inside the proof (l. 5115–5117), the traces (l. 5140).

**Conventions (B0.7).** A plane domain is `Ω : TopologicalSpace.Opens ℂ` (a Riemann surface by Mathlib's charts),
connected, whose complement in `ℂ` has at least two points (so `Ω` is hyperbolic: `ℂ̄ ∖ Ω` has at least three);
the frontier and the frontier closure are taken in `ℂ` (the point `∞`, when on the frontier, is fixed by every map
considered). A self-map `f` of `Ω` acts on `ℂ` through `planeMap f` (the identity off `Ω`). Spherical diameters are
`Pommerenke1992.chordalDiam`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane IsKQC IsKQCRS IsFuchsian IsUniformization)

open Classical in
/-- Helper. A self-map of the plane domain `Ω` as a map of `ℂ` (the identity off `Ω`). -/
def planeMap {Ω : TopologicalSpace.Opens ℂ} (f : Ω → Ω) (z : ℂ) : ℂ :=
  if h : z ∈ Ω then (f ⟨z, h⟩ : ℂ) else z

/-- **Definition 7** (frontier equivalence, §5.3, l. 5107). Quasiconformal maps `f₀ : Ω → Ω₀`, `f₁ : Ω → Ω₁` of
plane domains are frontier equivalent if there are a conformal map `c : Ω₀ → Ω₁` and a homotopy `g_t` of self-maps
of the frontier closure `Ω̄` with `g₀ = id`, `g₁ = f₁⁻¹ ∘ c ∘ f₀` on `Ω`, and `g_t(p) = p` for every frontier point
`p`. Modelling: `c` is holomorphic and bijective `Ω₀ → Ω₁`; the maps are plane maps; each `g_t` maps `Ω` into `Ω` (a
self-map of `R`, continuous on the frontier closure and fixing the frontier).
[CORRECTION] (AUDITR2_GL15 R2G-1) `g_t(Ω) ⊆ Ω` was missing: with only `g_t(Ω̄) ⊆ Ω̄` and `Ω̄ = ℂ` (the plane minus finitely many
points) the straight-line homotopy `(1 − t) z + t g₁(z)` made every map fixing the punctures frontier equivalent to the identity
(e.g. a Dehn twist on `ℂ ∖ {0, 1, 2}`), and `thm5_5` was false. The book's proof of (iv) ⇒ (ii) (l. 5136) lifts `g_t` to the
universal covering of `R`, which needs `g_t(R) ⊆ R`. -/
def IsFrontierEquiv (Ω : Set ℂ) (f₀ f₁ : ℂ → ℂ) : Prop :=
  ∃ c : ℂ → ℂ, DifferentiableOn ℂ c (f₀ '' Ω) ∧ BijOn c (f₀ '' Ω) (f₁ '' Ω) ∧
    ∃ H : ℂ → unitInterval → ℂ, ContinuousOn (fun x : ℂ × unitInterval => H x.1 x.2) (closure Ω ×ˢ univ) ∧
      (∀ z ∈ Ω, H z 0 = z) ∧ (∀ z ∈ Ω, H z 1 = Function.invFunOn f₁ Ω (c (f₀ z))) ∧
      (∀ t, MapsTo (fun z => H z t) (closure Ω) (closure Ω)) ∧ (∀ t, MapsTo (fun z => H z t) Ω Ω) ∧
      ∀ z ∈ frontier Ω, ∀ t, H z t = z

/-- **Definition 8** (sphere equivalence, §5.3, l. 5119). `f₀`, `f₁` are sphere equivalent (constant `K′`) if there
are a conformal map `c : Ω₀ → Ω₁` and an isotopy `g_t` of the whole sphere with `g₀ = id`, `g₁ = f₁⁻¹ ∘ c ∘ f₀` on
`Ω`, `g_t(p) = p` for every `p` in the complement `Λ` of `Ω`, every `g_t` being `K′`-quasiconformal. Modelling: the
`g_t` are `K′`-quasiconformal homeomorphisms of `ℂ` (they fix the points of `Λ`, hence `∞`). -/
def IsSphereEquiv (Ω : Set ℂ) (K' : ℝ) (f₀ f₁ : ℂ → ℂ) : Prop :=
  ∃ c : ℂ → ℂ, DifferentiableOn ℂ c (f₀ '' Ω) ∧ BijOn c (f₀ '' Ω) (f₁ '' Ω) ∧
    ∃ H : ℂ → unitInterval → ℂ, Continuous (fun x : ℂ × unitInterval => H x.1 x.2) ∧
      (∀ z, H z 0 = z) ∧ (∀ z ∈ Ω, H z 1 = Function.invFunOn f₁ Ω (c (f₀ z))) ∧
      (∀ t, IsKQC (fun z => H z t) univ K' ∧ (fun z => H z t) '' univ = univ) ∧ ∀ z ∉ Ω, ∀ t, H z t = z

/-- **Theorem 5** (§5.3, l. 5128). Let `Ω` be a plane domain and `f : Ω → Ω` quasiconformal. The following are
equivalent: (i) `f` is isotopically equivalent to the identity; (ii) Teichmüller equivalent; (iii) circle
equivalent; (iv) frontier equivalent; (v) sphere equivalent to the identity. Modelling: `f` is `K`-quasiconformal,
the isotopies in (i) and (v) are `K′`-quasiconformal with `K′` depending only on `K` (`∀ K ∃ K′`); (i)–(iii) with
respect to a uniformization `p` of `Ω` (Definitions 3–5). -/
theorem thm5_5 (K : ℝ) : ∃ K' : ℝ, ∀ (Ω : TopologicalSpace.Opens ℂ) [ConnectedSpace Ω],
    ((Ω : Set ℂ)ᶜ).encard ≠ 0 → ((Ω : Set ℂ)ᶜ).encard ≠ 1 →
    ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → Ω), IsFuchsian Γ →
    IsUniformization Γ p → ∀ f : Ω ≃ₜ Ω, IsKQCRS f K →
      List.TFAE [IsIsotopyEquiv p K' (Y₀ := selfBundle Ω) (Y₁ := selfBundle Ω) f (Homeomorph.refl Ω),
        IsTeichEquiv p (Y₀ := selfBundle Ω) (Y₁ := selfBundle Ω) f (Homeomorph.refl Ω),
        IsCircleEquiv p (Y₀ := selfBundle Ω) (Y₁ := selfBundle Ω) f (Homeomorph.refl Ω),
        IsFrontierEquiv Ω (planeMap f) id, IsSphereEquiv Ω K' (planeMap f) id] := by
  sorry

/-- **Lemma 2** ([EM88], §5.3, l. 5137). Let `π : Δ → Ω` be a universal covering of the plane domain `Ω`. If `γₙ`
are paths in `Ω` whose spherical diameters tend to `0`, then the Euclidean diameters of any lifts `γ̃ₙ` to `Δ` tend
to `0`. Modelling: paths are continuous maps of `[0, 1]`; `π` is a holomorphic covering map of `Ω` by the unit disc. -/
theorem lemma5_2 (Ω : TopologicalSpace.Opens ℂ) [ConnectedSpace Ω] (hΩ₀ : ((Ω : Set ℂ)ᶜ).encard ≠ 0)
    (hΩ₁ : ((Ω : Set ℂ)ᶜ).encard ≠ 1) (cov : LiZhongQC.unitDiscOpens → Ω) (hcov : IsCoveringMap cov)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) cov) (γ : ℕ → C(unitInterval, Ω))
    (γ' : ℕ → C(unitInterval, LiZhongQC.unitDiscOpens)) (hlift : ∀ n t, cov (γ' n t) = γ n t)
    (hsmall : Tendsto (fun n => Pommerenke1992.chordalDiam (range fun t => ((γ n t : ℂ) : ExtPlane))) atTop (𝓝 0)) :
    Tendsto (fun n => Metric.diam (range fun t => (γ' n t : ℂ))) atTop (𝓝 0) := by
  sorry

end GardinerLakic2000
