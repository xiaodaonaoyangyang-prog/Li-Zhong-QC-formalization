import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.S34mManifold
import LiZhongQC.Lemmas.S34fFibre
import LiZhongQC.Lemmas.S34fProper

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

/-! R83 S34 (精英下属5): final module.  The book theorems `bersQuotient_manifold` (S34:1114) and `thm34_1_bers`
(S34:1135), as helpers `s34m_bersQuotient_manifold` / `s34m_thm34_1_bers` with byte-identical statements, proved
from `s34m_family` (S34mManifold) and `s34f_fibre` (S34fFibre, 下属2) / `s34f_proper` (S34fProper); relocated into this module at install. -/

noncomputable section

namespace LiZhongQC

universe u v

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- §34.2: `V(G₀)` is a complex manifold of dimension `3g - 2`: a point `[φ, z]` has the local
coordinates `(t₁, …, t_{3g-3}, z)` of `(φ, z)` in a neighbourhood `N` on which the action is free,
`φ = t₁φ₁ + ⋯ + t_{3g-3}φ_{3g-3}`; and `pr` is holomorphic, `(t, z) ↦ t` in these coordinates.

**Statement change (2026-10-13, user decision).**  The topology and the atlas were free existentials, so
the statement held by a set-theoretic bijection `V(G₀) ≃ range coords × ℂ` with one transported chart.
Now the topology `τ` is the quotient topology of `F(G₀) ⊆ (ℂ → ℂ) × ℂ`, where `ℂ → ℂ` carries the topology
of pointwise convergence (on the finite-dimensional space `Q(G₀, 𝕃)` containing `T_{G₀}` this is the
Euclidean topology).  The chart clause says that every point of `F(G₀)` has an open neighbourhood `N`
whose image is the source of an atlas chart that reads `[φ, z] ↦ (coords φ, z)` on `N`. -/
theorem s34m_bersQuotient_manifold {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (τ : TopologicalSpace (BersQuotient Γ))
      (_ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
      (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)),
      IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ) ∧
      (∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2) ∧
      ∃ pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)),
        MDifferentiable 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) pr ∧
        ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q → (pr v : Fin (3 * g - 3) → ℂ) = coords q := by
  obtain ⟨coords, hinj, hopen, τ, hτ, cs, hM, hchart, pr, hmd, hpr, -, -⟩ := s34m_family hg hS hΓ hfree hp
  exact ⟨coords, hinj, hopen, τ, hτ, cs, hM, hchart, pr, hmd, hpr⟩

/-- **Theorem 34.1 (Bers)**: `(V(G₀), T_{G₀}, pr)` is a holomorphic family, in the sense of
Kodaira–Spencer, of closed Riemann surfaces of genus `g > 1`; the fibre over `φ` is `D_φ/G_φ`, the
Riemann surface corresponding to the point `φ ∈ T_{G₀}`. -/
theorem s34m_thm34_1_bers {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (_ : TopologicalSpace (BersQuotient Γ)) (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ))
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ))
      (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ))),
      IsHolomorphicFamily (n := 3 * g - 3) pr ∧
      ∀ q : TeichGamma Γ, ∃ (X : ClosedRS.{u}) (j : X.carrier → BersQuotient Γ) (cov : ℂ → X.carrier),
        HasGenus X.carrier g ∧ Topology.IsEmbedding j ∧
        (range j = pr ⁻¹' {⟨coords q, mem_range_self q⟩}) ∧
        (∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)), j (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩) ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov (bersDisc Γ (bersMapGamma Γ q)) ∧
        ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∀ w ∈ bersDisc Γ (bersMapGamma Γ q),
          (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersMapGamma Γ q) z) := by
  obtain ⟨coords, hinj, hopen, τ, hτ, cs, hM, hchart, pr, hmd, hpr, hsurj, hder⟩ :=
    s34m_family hg hS hΓ hfree hp
  have hproj : ∀ v : BersQuotient Γ, ∃ q, bersProjection Γ v = bersMapGamma Γ q := by
    intro v
    induction v using Quot.ind with
    | mk x =>
      obtain ⟨q, hq⟩ := x.2.1
      exact ⟨q, hq.symm⟩
  have hrange : ∀ q : TeichGamma Γ, pr ⁻¹' {⟨coords q, mem_range_self q⟩} =
      bersProjection Γ ⁻¹' {bersMapGamma Γ q} := by
    intro q
    ext v
    rw [mem_preimage, mem_singleton_iff, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨q', hq'⟩ := hproj v
      rw [hinj ((congrArg Subtype.val h).symm.trans (hpr q' v hq'))]
      exact hq'
    · intro h
      exact Subtype.ext (hpr q v h)
  refine ⟨coords, hinj, hopen, τ, cs, hM, pr,
    ⟨hmd, hsurj, hder, s34f_proper hg hS hΓ hfree hp coords hinj hopen τ hτ cs hM hchart pr hpr, ?_⟩, fun q => ?_⟩
  · rintro ⟨_, q, rfl⟩
    obtain ⟨X, j, cov, -, hj, hje, hjr, -, -, -⟩ :=
      s34f_fibre hg hS hΓ hfree hp coords hinj hopen τ hτ cs hM hchart q
    exact ⟨X, j, hj, hje, hjr.trans (hrange q).symm⟩
  · obtain ⟨X, j, cov, hX, -, hje, hjr, hjc, hcov, hiff⟩ :=
      s34f_fibre hg hS hΓ hfree hp coords hinj hopen τ hτ cs hM hchart q
    exact ⟨X, j, cov, hX, hje, hjr.trans (hrange q).symm, hjc, hcov, hiff⟩

section RelocatedS34


/-- §34.2: `V(G₀)` is a complex manifold of dimension `3g - 2`: a point `[φ, z]` has the local
coordinates `(t₁, …, t_{3g-3}, z)` of `(φ, z)` in a neighbourhood `N` on which the action is free,
`φ = t₁φ₁ + ⋯ + t_{3g-3}φ_{3g-3}`; and `pr` is holomorphic, `(t, z) ↦ t` in these coordinates.

**Statement change (2026-10-13, user decision).**  The topology and the atlas were free existentials, so
the statement held by a set-theoretic bijection `V(G₀) ≃ range coords × ℂ` with one transported chart.
Now the topology `τ` is the quotient topology of `F(G₀) ⊆ (ℂ → ℂ) × ℂ`, where `ℂ → ℂ` carries the topology
of pointwise convergence (on the finite-dimensional space `Q(G₀, 𝕃)` containing `T_{G₀}` this is the
Euclidean topology).  The chart clause says that every point of `F(G₀)` has an open neighbourhood `N`
whose image is the source of an atlas chart that reads `[φ, z] ↦ (coords φ, z)` on `N`. -/
theorem bersQuotient_manifold {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (τ : TopologicalSpace (BersQuotient Γ))
      (_ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
      (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)),
      IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ) ∧
      (∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2) ∧
      ∃ pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)),
        MDifferentiable 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) pr ∧
        ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q → (pr v : Fin (3 * g - 3) → ℂ) = coords q := by
  exact s34m_bersQuotient_manifold hg hS hΓ hfree hp

/-- **Theorem 34.1 (Bers)**: `(V(G₀), T_{G₀}, pr)` is a holomorphic family, in the sense of
Kodaira–Spencer, of closed Riemann surfaces of genus `g > 1`; the fibre over `φ` is `D_φ/G_φ`, the
Riemann surface corresponding to the point `φ ∈ T_{G₀}`. -/
theorem thm34_1_bers {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (_ : TopologicalSpace (BersQuotient Γ)) (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ))
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ))
      (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ))),
      IsHolomorphicFamily (n := 3 * g - 3) pr ∧
      ∀ q : TeichGamma Γ, ∃ (X : ClosedRS.{u}) (j : X.carrier → BersQuotient Γ) (cov : ℂ → X.carrier),
        HasGenus X.carrier g ∧ Topology.IsEmbedding j ∧
        (range j = pr ⁻¹' {⟨coords q, mem_range_self q⟩}) ∧
        (∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)), j (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩) ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov (bersDisc Γ (bersMapGamma Γ q)) ∧
        ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∀ w ∈ bersDisc Γ (bersMapGamma Γ q),
          (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersMapGamma Γ q) z) := by
  exact s34m_thm34_1_bers hg hS hΓ hfree hp

end RelocatedS34

end LiZhongQC
