import LiZhongQC.Lemmas.SchottkyAnticonformalEigen
import LiZhongQC.Lemmas.SchottkyDoubleConnected
import LiZhongQC.Lemmas.SchottkyDoubleGeometry
import LiZhongQC.Lemmas.SchottkyDoubleAtlas
import LiZhongQC.Lemmas.SchottkyGenusBridge6
import LiZhongQC.Lemmas.SchottkyClosedGenus
import LiZhongQC.Lemmas.SchottkyGenusBridge11
import LiZhongQC.Lemmas.SchottkyBoundaryRank

/-!
# The Schottky double of a surface of finite type (`exists_schottkyDouble`, §31.1)

`s31tm_exists_schottkyDouble` has the hypotheses and conclusion of `LiZhongQC.exists_schottkyDouble` (S31)
verbatim; on install, the book theorem is relocated here (S31 cannot import this module).

The double is the concrete quotient `s31dt_Double F` (SchottkyDoubleCarrier), with `J = s31dt_flipHomeomorph F`,
`ιd = s31dt_embed F false` and the concrete `Pd` of `s31sd_concrete_marked_points`. Its complex atlas, the
holomorphy of `ιd` and the anticonformality of `J` are `s78ra_double_complex_atlas` (SchottkyDoubleAtlas); the
remaining fields of `IsSchottkyDouble` other than the genus come from SchottkyDoubleCarrier/Geometry/Connected.

**The genus** (`s78fa_double_genus`, route C): with the atlas, the double has genus `2g + m - 1`.
Notation: `x₀` a boundary point of the core (so `q₀ = side false x₀` is `J`-fixed),
`V = Hom(π₁(Xd, q₀), ℝ)`, `W = Hom(π₁(Core, x₀), ℝ)`, `A` the involution of `V` induced by `J`.

1. `s78fa_fold_injective`: `ψ ↦ ψ ∘ project_*` embeds `W` into `ker (A - 1)`.
2. `s78fa_core_characters_ge`: `2g + m - 1 ≤ dim W` (the kernel of the boundary evaluation has dimension
   `2g` (iii-a), and the boundary evaluation has rank `≥ m - 1` (B5)).
3. `s78fa_minus_le`: `dim ker (A + 1) ≤ 2g + m - 1` (restriction to the core lands in the kernel of
   the boundary evaluation; with the `m - 1` crossing values it is injective on `ker (A + 1)` by the
   generation lemma `s78dg_double_generation`).
4. `s78fa_double_genus`: `s78no_anticonformal_character_eigen` gives `dim ker (A ∓ 1) = genus Xd`; with the
   genus from `s78fa_closed_surface_has_genus`, `2g + m - 1 ≤ dim W ≤ genus ≤ 2g + m - 1`.

The `s78fa_ext_*` theorems are the agreed consumer statements of other lanes, each discharged by the upstream
theorem (`s78dg_double_generation`, (iii-a) `s78dg_core_kernel_dim`, B5 `s78rb_boundary_characters_pi1`,
`s78fa_closed_surface_has_genus`).
-/

open Set Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u

/-! ### Consumer statements of other lanes -/

/-- = `s78dg_double_generation` (下属3, (ii)). -/
theorem s78fa_ext_generation {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) :
    ∃ (x₀ : s31dt_Core F) (p : Fin m → s31dt_Core F),
      x₀ ∈ s31dt_boundary F ∧ (∀ j, (p j).val ∈ frontier (F.D j)) ∧
      ∀ H : Subgroup (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)),
        (∀ (b : Bool) (e : s31dt_side F b x₀ = s31dt_side F false x₀)
          (γ : FundamentalGroup (s31dt_Core F) x₀),
          FundamentalGroup.mapOfEq (⟨s31dt_side F b, s31dt_continuous_side F b⟩ :
            C(s31dt_Core F, s31dt_Double F)) e γ ∈ H) →
        (∀ (j : Fin m) (a0 a1 : Path (s31dt_side F false x₀) (s31dt_side F false (p j))),
          range a0 ⊆ range (s31dt_side F false) → range a1 ⊆ range (s31dt_side F true) →
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a0.trans a1.symm)) ∈ H) →
        H = ⊤ :=
  s78dg_double_generation F hm

/-- (iii-a) (下属3), proposed: boundary loop classes `c j = [a · ℓ_j · a⁻¹]` (`ℓ_j` a parametrization of
the `j`-th boundary circle, in the hypothesis form of B5) whose joint kernel in `W` has dimension `2g`. -/
theorem s78fa_ext_core_kernel {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (x₀ : s31dt_Core F) :
    ∃ (c : Fin m → FundamentalGroup (s31dt_Core F) x₀)
      (L : (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) →ₗ[ℝ] (Fin m → ℝ)),
      (∀ ψ j, L ψ j = ψ (Additive.ofMul (c j))) ∧
      Module.finrank ℝ (LinearMap.ker L) = 2 * g ∧
      ∀ j, ∃ (β : C(ℝ, s31dt_Core F)) (ℓ : Path (β 0) (β 0)) (a : Path x₀ (β 0)),
        (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧
        range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} ∧
        (∀ t : unitInterval, ℓ t = β t) ∧
        c j = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)) :=
  s78dg_core_kernel_dim F hm x₀

/-- = `s78rb_boundary_characters_pi1` (下属1, B5). -/
theorem s78fa_ext_boundary_characters {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (x₀ : s31dt_Core F) :
    ∃ ψ : Fin m → (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ),
      ∀ (j : Fin m) (β : C(ℝ, s31dt_Core F)), (∀ t, β (t + 1) = β t) → InjOn β (Ico 0 1) →
        range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ∀ (k : Fin m) (ℓ : Path (β 0) (β 0)), (∀ t : unitInterval, ℓ t = β t) →
            ∀ a : Path x₀ (β 0),
              ψ k (Additive.ofMul (FundamentalGroup.fromPath
                (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)))) =
                ((ε * ((if j = k then 1 else 0) -
                  (if j = ⟨0, Nat.pos_of_ne_zero hm⟩ then 1 else 0)) : ℤ) : ℝ) :=
  s78rb_boundary_characters_pi1 F hm x₀

/-- = `s78fa_closed_surface_has_genus` (part (A)). -/
theorem s78fa_ext_closed_genus {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    [CompactSpace X] : ∃ g : ℕ, HasGenus X g :=
  s78fa_closed_surface_has_genus

/-! ### The genus of the double -/

/-- Cancellation in path classes: `γ⁻¹ · (γ · δ) = δ`. -/
theorem s78fa_qcancel_left {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) :
    γ.symm.trans (γ.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- A real character splits a loop `a · c⁻¹` through any third path `b`. -/
theorem s78fa_char_split {X : Type*} [TopologicalSpace X] {x y : X}
    (χ : Additive (FundamentalGroup X x) →+ ℝ) (a b c : Path x y) :
    χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans c.symm)))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b.symm)))) +
      χ (Additive.ofMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (b.trans c.symm)))) := by
  have h : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans c.symm)) :
      FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (b.trans c.symm)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b.symm)) := by
    rw [FundamentalGroup.mul_def]
    simp only [FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, s78fa_qcancel_left]
  rw [h, ofMul_mul, map_add, add_comm]

/-- Real characters agree on the loops `a · ℓ · a⁻¹` and `a' · ℓ · a'⁻¹` (they are conjugate). -/
theorem s78fa_char_conj {X : Type*} [TopologicalSpace X] {x y : X}
    (χ : Additive (FundamentalGroup X x) →+ ℝ) (a a' : Path x y) (ℓ : Path y y) :
    χ (Additive.ofMul
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)))) =
    χ (Additive.ofMul
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a'.trans ℓ).trans a'.symm)))) := by
  have h1 : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a'.trans ℓ).trans a'.symm)) :
      FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans a'.symm)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a'.trans a.symm)) := by
    rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def]
    simp only [FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, s78fa_qcancel_left]
  have h2 : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans a'.symm)) :
      FundamentalGroup X x) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a'.trans a.symm)) = 1 := by
    rw [FundamentalGroup.mul_def, FundamentalGroup.one_def]
    simp only [FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, s78fa_qcancel_left,
      Path.Homotopic.Quotient.trans_symm]
  have h3 := congrArg (fun γ => χ (Additive.ofMul γ)) h2
  simp only [ofMul_mul, map_add, ofMul_one, map_zero] at h3
  rw [h1, ofMul_mul, ofMul_mul, map_add, map_add]
  linarith

/-- `mapOfEq` on a based loop class is the class of the image loop. -/
theorem s78fa_mapOfEq_fromPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (p : Path x x) :
    FundamentalGroup.mapOfEq f h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((p.map f.continuous).cast h.symm h.symm)) := by
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

/-- A loop of the double lying in one sheet is the image of its projection to the core. -/
theorem s78fa_sheet_loop {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) (x₀ : s31dt_Core F) (b : Bool)
    (e : s31dt_side F b x₀ = s31dt_side F false x₀)
    (ℓ : Path (s31dt_side F false x₀) (s31dt_side F false x₀))
    (hℓ : range ℓ ⊆ range (s31dt_side F b)) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ) =
      FundamentalGroup.mapOfEq (⟨s31dt_side F b, s31dt_continuous_side F b⟩ :
        C(s31dt_Core F, s31dt_Double F)) e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((ℓ.map (s31dt_continuous_project F)).cast rfl rfl))) := by
  rw [s78fa_mapOfEq_fromPath]
  refine congrArg (fun r => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk r)) ?_
  apply Path.ext
  funext t
  obtain ⟨z, hz⟩ := hℓ ⟨t, rfl⟩
  change ℓ t = s31dt_side F b (s31dt_project F (ℓ t))
  rw [← hz]
  rfl

/-- On the core's loops, the mirror sheet is the flip of the original sheet. -/
theorem s78fa_side_true_eq_flip {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) (x₀ : s31dt_Core F)
    (e : s31dt_side F true x₀ = s31dt_side F false x₀)
    (hx : s31dt_flipHomeomorph F (s31dt_side F false x₀) = s31dt_side F false x₀)
    (γ : FundamentalGroup (s31dt_Core F) x₀) :
    FundamentalGroup.mapOfEq (⟨s31dt_side F true, s31dt_continuous_side F true⟩ :
        C(s31dt_Core F, s31dt_Double F)) e γ =
      FundamentalGroup.mapOfEq (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx
        (FundamentalGroup.mapOfEq (⟨s31dt_side F false, s31dt_continuous_side F false⟩ :
          C(s31dt_Core F, s31dt_Double F)) rfl γ) := by
  obtain ⟨γ⟩ := γ
  refine Quotient.inductionOn γ (fun p => ?_)
  let sT : C(s31dt_Core F, s31dt_Double F) := ⟨s31dt_side F true, s31dt_continuous_side F true⟩
  let sF : C(s31dt_Core F, s31dt_Double F) := ⟨s31dt_side F false, s31dt_continuous_side F false⟩
  let Jc : C(s31dt_Double F, s31dt_Double F) := s31dt_flipHomeomorph F
  have e1 := s78fa_mapOfEq_fromPath sT e p
  have e2 := s78fa_mapOfEq_fromPath sF (rfl : sF x₀ = s31dt_side F false x₀) p
  have e3 := s78fa_mapOfEq_fromPath Jc hx ((p.map sF.continuous).cast rfl rfl)
  exact e1.trans ((congrArg (FundamentalGroup.mapOfEq Jc hx) e2).trans e3).symm

/-- **Fold.**  `ψ ↦ ψ ∘ project_*` embeds the real characters of the core into the `J`-invariant
characters of the double. -/
theorem s78fa_fold_injective {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) (x₀ : s31dt_Core F)
    (hx : s31dt_flipHomeomorph F (s31dt_side F false x₀) = s31dt_side F false x₀)
    (A : Module.End ℝ (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ))
    (hA : ∀ χ (γ : FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)),
      A χ (Additive.ofMul γ) =
        χ (Additive.ofMul (FundamentalGroup.mapOfEq
          (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx γ))) :
    ∃ T : (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) →ₗ[ℝ]
        (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ),
      Function.Injective T ∧ ∀ ψ, T ψ ∈ LinearMap.ker (A - 1) := by
  let πc : C(s31dt_Double F, s31dt_Core F) := ⟨s31dt_project F, s31dt_continuous_project F⟩
  have hpr : πc (s31dt_side F false x₀) = x₀ := rfl
  let π := FundamentalGroup.mapOfEq πc hpr
  let σc : C(s31dt_Core F, s31dt_Double F) := ⟨s31dt_side F false, s31dt_continuous_side F false⟩
  have hσ0 : σc x₀ = s31dt_side F false x₀ := rfl
  let σ := FundamentalGroup.mapOfEq σc hσ0
  have hπσ : ∀ γ, π (σ γ) = γ := by
    intro γ
    obtain ⟨γ⟩ := γ
    refine Quotient.inductionOn γ (fun p => ?_)
    have e1 := s78fa_mapOfEq_fromPath σc hσ0 p
    have e2 := s78fa_mapOfEq_fromPath πc hpr ((p.map σc.continuous).cast hσ0.symm hσ0.symm)
    exact (congrArg π e1).trans e2
  have hπJ : ∀ γ, π (FundamentalGroup.mapOfEq
      (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx γ) = π γ := by
    intro γ
    obtain ⟨γ⟩ := γ
    refine Quotient.inductionOn γ (fun p => ?_)
    let Jc : C(s31dt_Double F, s31dt_Double F) := s31dt_flipHomeomorph F
    have e1 := s78fa_mapOfEq_fromPath Jc hx p
    have e2 := s78fa_mapOfEq_fromPath πc hpr ((p.map Jc.continuous).cast hx.symm hx.symm)
    have e3 := s78fa_mapOfEq_fromPath πc hpr p
    refine ((congrArg π e1).trans e2).trans (Eq.trans ?_ e3.symm)
    refine congrArg (fun r => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk r)) ?_
    apply Path.ext
    funext t
    change s31dt_project F (s31dt_flip F (p t)) = s31dt_project F (p t)
    induction p t using Quotient.inductionOn
    rfl
  refine ⟨{ toFun := fun ψ => ψ.comp (MonoidHom.toAdditive π)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }, ?_, ?_⟩
  · intro ψ₁ ψ₂ h
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨γ, rfl⟩ := Additive.ofMul.surjective a
    have h1 := congrArg (fun χ : Additive (FundamentalGroup (s31dt_Double F)
      (s31dt_side F false x₀)) →+ ℝ => χ (Additive.ofMul (σ γ))) h
    change ψ₁ (Additive.ofMul (π (σ γ))) = ψ₂ (Additive.ofMul (π (σ γ))) at h1
    rwa [hπσ] at h1
  · intro ψ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨γ, rfl⟩ := Additive.ofMul.surjective a
    rw [hA]
    change ψ (Additive.ofMul (π (FundamentalGroup.mapOfEq _ hx γ))) = ψ (Additive.ofMul (π γ))
    rw [hπJ]

/-- **Lower bound.**  The real characters of the core have dimension at least `2g + m - 1`. -/
theorem s78fa_core_characters_ge {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (x₀ : s31dt_Core F)
    [FiniteDimensional ℝ (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ)] :
    2 * g + m - 1 ≤ Module.finrank ℝ (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) := by
  classical
  obtain ⟨c, L, hL, hker, hc⟩ := s78fa_ext_core_kernel F hm x₀
  obtain ⟨ψ, hψ⟩ := s78fa_ext_boundary_characters F hm x₀
  set k₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩ with hk₀
  have hε : ∀ j, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ k, ψ k (Additive.ofMul (c j)) =
      ((ε * ((if j = k then 1 else 0) - (if j = k₀ then 1 else 0)) : ℤ) : ℝ) := by
    intro j
    obtain ⟨β, ℓ, a, hper, hinj, hrange, hℓ, hcj⟩ := hc j
    obtain ⟨ε, hε, hval⟩ := hψ j β hper hinj hrange
    exact ⟨ε, hε, fun k => by rw [hcj]; exact hval k ℓ hℓ a⟩
  choose ε hε1 hε2 using hε
  have hεsq : ∀ j, (ε j : ℝ) * ε j = 1 := by
    intro j
    rcases hε1 j with h | h <;> rw [h] <;> norm_num
  -- the boundary evaluation, read off the coordinates `k ≠ k₀`
  let R : (Fin m → ℝ) →ₗ[ℝ] ({k : Fin m // k ≠ k₀} → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Subtype.val : {k : Fin m // k ≠ k₀} → Fin m)
  have hsurj : Function.Surjective (R ∘ₗ L) := by
    intro y
    refine ⟨∑ k : {k : Fin m // k ≠ k₀}, (y k * ε k.1) • ψ k.1, ?_⟩
    funext j
    change L _ j.1 = y j
    rw [hL, AddMonoidHom.finsetSum_apply]
    rw [Finset.sum_eq_single j]
    · rw [AddMonoidHom.smul_apply, hε2, smul_eq_mul]
      have hj : j.1 ≠ k₀ := j.2
      simp only [hj, ↓reduceIte]
      push_cast
      rw [mul_one, mul_assoc, hεsq, mul_one]
    · intro k _ hk
      rw [AddMonoidHom.smul_apply, hε2, smul_eq_mul]
      have hj : j.1 ≠ k₀ := j.2
      have hjk : j.1 ≠ k.1 := fun h => hk (Subtype.ext h).symm
      simp only [hj, hjk, ↓reduceIte]
      push_cast
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hrange : Module.finrank ℝ ({k : Fin m // k ≠ k₀} → ℝ) ≤
      Module.finrank ℝ (LinearMap.range L) := by
    have h1 : LinearMap.range (R ∘ₗ L) = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have h2 : LinearMap.range (R ∘ₗ L) = (LinearMap.range L).map R := LinearMap.range_comp L R
    have h3 := Submodule.finrank_map_le R (LinearMap.range L)
    rw [← h2, h1, finrank_top] at h3
    exact h3
  have hcard : Module.finrank ℝ ({k : Fin m // k ≠ k₀} → ℝ) = m - 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  omega

/-- **Upper bound.**  For `x₀` and seam points `p` as in the generation lemma, the anti-invariant
characters of the double have dimension at most `2g + m - 1`. -/
theorem s78fa_minus_le {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0)
    (x₀ : s31dt_Core F) (p : Fin m → s31dt_Core F) (hx₀ : x₀ ∈ s31dt_boundary F)
    (hp : ∀ j, (p j).val ∈ frontier (F.D j))
    (hgen : ∀ H : Subgroup (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)),
        (∀ (b : Bool) (e : s31dt_side F b x₀ = s31dt_side F false x₀)
          (γ : FundamentalGroup (s31dt_Core F) x₀),
          FundamentalGroup.mapOfEq (⟨s31dt_side F b, s31dt_continuous_side F b⟩ :
            C(s31dt_Core F, s31dt_Double F)) e γ ∈ H) →
        (∀ (j : Fin m) (a0 a1 : Path (s31dt_side F false x₀) (s31dt_side F false (p j))),
          range a0 ⊆ range (s31dt_side F false) → range a1 ⊆ range (s31dt_side F true) →
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a0.trans a1.symm)) ∈ H) →
        H = ⊤)
    (hx : s31dt_flipHomeomorph F (s31dt_side F false x₀) = s31dt_side F false x₀)
    (A : Module.End ℝ (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ))
    (hA : ∀ χ (γ : FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)),
      A χ (Additive.ofMul γ) =
        χ (Additive.ofMul (FundamentalGroup.mapOfEq
          (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx γ)))
    [FiniteDimensional ℝ
      (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ)] :
    Module.finrank ℝ (LinearMap.ker (A + 1)) ≤ 2 * g + m - 1 := by
  classical
  let sF : C(s31dt_Core F, s31dt_Double F) := ⟨s31dt_side F false, s31dt_continuous_side F false⟩
  let Jc : C(s31dt_Double F, s31dt_Double F) := s31dt_flipHomeomorph F
  have hsF0 : sF x₀ = s31dt_side F false x₀ := rfl
  let σ := FundamentalGroup.mapOfEq sF hsF0
  have eT : s31dt_side F true x₀ = s31dt_side F false x₀ :=
    ((s31dt_opposite_eq_iff F x₀ x₀).mpr ⟨rfl, hx₀⟩).symm
  -- `W` is finite-dimensional (fold)
  obtain ⟨T, hTinj, -⟩ := s78fa_fold_injective F x₀ hx A hA
  have : FiniteDimensional ℝ (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) :=
    Module.Finite.of_injective T hTinj
  -- restriction to the core
  let ρ : (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ) →ₗ[ℝ]
      (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) :=
    { toFun := fun χ => χ.comp (MonoidHom.toAdditive σ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- anti-invariance
  have hneg : ∀ χ ∈ LinearMap.ker (A + 1), ∀ γ,
      χ (Additive.ofMul (FundamentalGroup.mapOfEq Jc hx γ)) = -χ (Additive.ofMul γ) := by
    intro χ hχ γ
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hχ
    rw [← hA, hχ]
    rfl
  have hTside : ∀ χ ∈ LinearMap.ker (A + 1), ∀ (e : s31dt_side F true x₀ = s31dt_side F false x₀) γ,
      χ (Additive.ofMul (FundamentalGroup.mapOfEq (⟨s31dt_side F true, s31dt_continuous_side F true⟩ :
        C(s31dt_Core F, s31dt_Double F)) e γ)) = -ρ χ (Additive.ofMul γ) := by
    intro χ hχ e γ
    rw [s78fa_side_true_eq_flip F x₀ e hx γ]
    exact hneg χ hχ _
  -- the boundary loops
  obtain ⟨c, L, hL, hker, hc⟩ := s78fa_ext_core_kernel F hm x₀
  have hbd : ∀ χ ∈ LinearMap.ker (A + 1), ∀ j, ρ χ (Additive.ofMul (c j)) = 0 := by
    intro χ hχ j
    obtain ⟨β, ℓ, a, -, -, hrange, hℓ, hcj⟩ := hc j
    have hβ : ∀ s, β s ∈ s31dt_boundary F := by
      intro s
      have h : β s ∈ range β := ⟨s, rfl⟩
      rw [hrange] at h
      exact ⟨j, h⟩
    have hy : Jc (sF (β 0)) = sF (β 0) :=
      (s31dt_flip_fixed_side_iff F false (β 0)).mpr (hβ 0)
    let A' := a.map sF.continuous
    let L' := ℓ.map sF.continuous
    let A'' := (A'.map Jc.continuous).cast hx.symm hy.symm
    have hL'' : (L'.map Jc.continuous).cast hy.symm hy.symm = L' := by
      apply Path.ext
      funext t
      change s31dt_flip F (s31dt_side F false (ℓ t)) = s31dt_side F false (ℓ t)
      rw [hℓ t]
      exact (s31dt_flip_fixed_side_iff F false (β t)).mpr (hβ t)
    have e1 : σ (c j) = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((A'.trans L').trans A'.symm)) := by
      rw [hcj, s78fa_mapOfEq_fromPath, Path.map_trans, Path.map_trans, Path.map_symm]
      rfl
    have e2 : FundamentalGroup.mapOfEq Jc hx (σ (c j)) = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((A''.trans L').trans A''.symm)) := by
      rw [e1, s78fa_mapOfEq_fromPath, Path.map_trans, Path.map_trans, Path.map_symm]
      refine congrArg (fun r => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk r)) ?_
      calc _ = (A''.trans ((L'.map Jc.continuous).cast hy.symm hy.symm)).trans A''.symm := rfl
        _ = _ := by rw [hL'']
    have h1 := hneg χ hχ (σ (c j))
    rw [e2, s78fa_char_conj χ A'' A' L', ← e1] at h1
    change χ (Additive.ofMul (σ (c j))) = 0
    linarith
  have hρ : ∀ χ ∈ LinearMap.ker (A + 1), ρ χ ∈ LinearMap.ker L := by
    intro χ hχ
    rw [LinearMap.mem_ker]
    funext j
    rw [hL]
    exact hbd χ hχ j
  -- the boundary circle through `x₀`
  obtain ⟨j₁, hj₁⟩ := hx₀
  have hB0 : ∃ B0 : Path (s31dt_side F false x₀) (s31dt_side F false (p j₁)),
      range B0 ⊆ range (s31dt_side F false) ∧ range B0 ⊆ range (s31dt_side F true) := by
    obtain ⟨β, -, -, -, -, hrange, -, -⟩ := hc j₁
    have h0 : x₀ ∈ range β := by rw [hrange]; exact hj₁
    have h1 : p j₁ ∈ range β := by rw [hrange]; exact hp j₁
    obtain ⟨s₀, hs₀⟩ := h0
    obtain ⟨s₁, hs₁⟩ := h1
    let b0 : Path x₀ (p j₁) :=
      { toFun := fun t => β (s₀ + (t : ℝ) * (s₁ - s₀))
        continuous_toFun := β.continuous.comp (by fun_prop)
        source' := by simp [hs₀]
        target' := by simp [hs₁] }
    refine ⟨b0.map sF.continuous, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨t, rfl⟩
      have hb : β (s₀ + (t : ℝ) * (s₁ - s₀)) ∈ s31dt_boundary F := by
        have h : β (s₀ + (t : ℝ) * (s₁ - s₀)) ∈ range β := ⟨_, rfl⟩
        rw [hrange] at h
        exact ⟨j₁, h⟩
      exact ⟨β (s₀ + (t : ℝ) * (s₁ - s₀)),
        ((s31dt_opposite_eq_iff F _ _).mpr ⟨rfl, hb⟩).symm⟩
  obtain ⟨B0, hB0F, hB0T⟩ := hB0
  -- reference crossing loops
  have hpj : ∀ j, Jc (s31dt_side F false (p j)) = s31dt_side F false (p j) := fun j =>
    (s31dt_flip_fixed_side_iff F false (p j)).mpr ⟨j, hp j⟩
  let ex : Fin m → Prop := fun j => ∃ a0 : Path (s31dt_side F false x₀) (s31dt_side F false (p j)),
    range a0 ⊆ range (s31dt_side F false)
  let mir : ∀ j, Path (s31dt_side F false x₀) (s31dt_side F false (p j)) →
      Path (s31dt_side F false x₀) (s31dt_side F false (p j)) := fun j a0 =>
    (a0.map Jc.continuous).cast hx.symm (hpj j).symm
  have hmir : ∀ j (a0 : Path (s31dt_side F false x₀) (s31dt_side F false (p j))),
      range a0 ⊆ range (s31dt_side F false) →
      range (mir j a0) ⊆ range (s31dt_side F true) := by
    intro j a0 ha0
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz⟩ := ha0 ⟨t, rfl⟩
    refine ⟨z, ?_⟩
    change s31dt_side F true z = s31dt_flip F (a0 t)
    rw [← hz]
    rfl
  let ℓr : Fin m → FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀) := fun j =>
    if h : ex j then FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (h.choose.trans (mir j h.choose).symm)) else 1
  -- loops in one sheet
  have hloopF : ∀ χ, ρ χ = 0 → ∀ lp : Path (s31dt_side F false x₀) (s31dt_side F false x₀),
      range lp ⊆ range (s31dt_side F false) →
      χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))) = 0 := by
    intro χ hχ lp hlp
    rw [s78fa_sheet_loop F x₀ false rfl lp hlp]
    exact congrArg (fun ψ : Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ =>
      ψ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((lp.map (s31dt_continuous_project F)).cast rfl rfl))))) hχ
  have hloopT : ∀ χ ∈ LinearMap.ker (A + 1), ρ χ = 0 →
      ∀ lp : Path (s31dt_side F false x₀) (s31dt_side F false x₀),
      range lp ⊆ range (s31dt_side F true) →
      χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))) = 0 := by
    intro χ hχ hρ0 lp hlp
    rw [s78fa_sheet_loop F x₀ true eT lp hlp, hTside χ hχ eT, hρ0]
    simp
  have hrange2 : ∀ {y : s31dt_Double F} (b : Bool) (u v : Path (s31dt_side F false x₀) y),
      range u ⊆ range (s31dt_side F b) → range v ⊆ range (s31dt_side F b) →
      range (u.trans v.symm) ⊆ range (s31dt_side F b) := by
    intro y b u v hu hv
    rw [Path.trans_range, Path.symm_range]
    exact union_subset hu hv
  -- the crossing loops are controlled by the reference values
  have hcross : ∀ χ ∈ LinearMap.ker (A + 1), ρ χ = 0 →
      (∀ j, j ≠ j₁ → χ (Additive.ofMul (ℓr j)) = 0) →
      ∀ (j : Fin m) (a0 a1 : Path (s31dt_side F false x₀) (s31dt_side F false (p j))),
        range a0 ⊆ range (s31dt_side F false) → range a1 ⊆ range (s31dt_side F true) →
        χ (Additive.ofMul (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (a0.trans a1.symm)))) = 0 := by
    intro χ hχ hρ0 hval j a0 a1 ha0 ha1
    have hex : ex j := ⟨a0, ha0⟩
    set r0 := hex.choose with hr0
    have hr0F : range r0 ⊆ range (s31dt_side F false) := hex.choose_spec
    rw [s78fa_char_split χ a0 r0 a1, s78fa_char_split χ r0 (mir j r0) a1,
      hloopF χ hρ0 _ (hrange2 false a0 r0 ha0 hr0F),
      hloopT χ hχ hρ0 _ (hrange2 true (mir j r0) a1 (hmir j r0 hr0F) ha1)]
    have href : χ (Additive.ofMul (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (r0.trans (mir j r0).symm)))) = 0 := by
      by_cases hj : j = j₁
      · subst hj
        rw [s78fa_char_split χ r0 B0 (mir j r0), hloopF χ hρ0 _ (hrange2 false r0 B0 hr0F hB0F),
          hloopT χ hχ hρ0 _ (hrange2 true B0 (mir j r0) hB0T (hmir j r0 hr0F))]
        simp
      · have h := hval j hj
        simp only [ℓr, hex, ↓reduceDIte] at h
        exact h
    rw [href]
    simp
  -- the comparison maps: crossing values, then restriction to the core on their kernel
  let k₁ := {j : Fin m // j ≠ j₁}
  let Ψ : (Additive (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) →+ ℝ) →ₗ[ℝ]
      (k₁ → ℝ) :=
    { toFun := fun χ j => χ (Additive.ofMul (ℓr j.1))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hzero : ∀ χ ∈ LinearMap.ker (A + 1), Ψ χ = 0 → ρ χ = 0 → χ = 0 := by
    intro χ hχ hΨ hρ0
    have hv : ∀ j, j ≠ j₁ → χ (Additive.ofMul (ℓr j)) = 0 := fun j hj =>
      congrFun hΨ ⟨j, hj⟩
    let H : Subgroup (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)) :=
      { carrier := {γ | χ (Additive.ofMul γ) = 0}
        mul_mem' := by
          intro a b ha hb
          change χ (Additive.ofMul (a * b)) = 0
          rw [ofMul_mul, map_add, ha, hb, add_zero]
        one_mem' := by
          change χ (Additive.ofMul 1) = 0
          rw [ofMul_one, map_zero]
        inv_mem' := by
          intro a ha
          change χ (Additive.ofMul a⁻¹) = 0
          rw [ofMul_inv, map_neg, ha, neg_zero] }
    have hH : H = ⊤ := by
      apply hgen H
      · intro b e γ
        cases b
        · change ρ χ (Additive.ofMul γ) = 0
          rw [hρ0]
          rfl
        · change χ (Additive.ofMul _) = 0
          rw [hTside χ hχ e γ, hρ0]
          simp
      · intro j a0 a1 ha0 ha1
        exact hcross χ hχ hρ0 hv j a0 a1 ha0 ha1
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨γ, rfl⟩ := Additive.ofMul.surjective a
    have hγ : γ ∈ H := hH ▸ Subgroup.mem_top γ
    exact hγ
  have hN : ∀ χ ∈ LinearMap.ker (A + 1) ⊓ LinearMap.ker Ψ, ρ χ ∈ LinearMap.ker L := fun χ hχ => hρ χ hχ.1
  have hinj : Function.Injective (ρ.restrict hN) := by
    intro a b hab
    have h1 : ρ a.1 = ρ b.1 := congrArg Subtype.val hab
    have hmem : a.1 - b.1 ∈ LinearMap.ker (A + 1) ⊓ LinearMap.ker Ψ := sub_mem a.2 b.2
    have h2 : Ψ (a.1 - b.1) = 0 := LinearMap.mem_ker.mp hmem.2
    have h3 : ρ (a.1 - b.1) = 0 := by rw [map_sub, h1, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hzero _ hmem.1 h2 h3))
  have h1 : Module.finrank ℝ (LinearMap.ker (A + 1) ⊓ LinearMap.ker Ψ : Submodule ℝ _) ≤ 2 * g := by
    rw [← hker]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℝ (LinearMap.range Ψ) ≤ m - 1 := by
    have h := Submodule.finrank_le (LinearMap.range Ψ)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique] at h
  have h3 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (A + 1)) (LinearMap.ker Ψ)
  have h5 := Submodule.finrank_le (LinearMap.ker (A + 1) ⊔ LinearMap.ker Ψ)
  omega

/-! ### The genus: assembly -/

/-- **The genus of the concrete Schottky double.**  If the double carries a complex atlas, analytic,
for which the flip is an anticonformal involution, it has genus `2g + m - 1`. -/
theorem s78fa_double_genus {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0)
    (F : FiniteTypeStructure S g n m) (cs : ChartedSpace ℂ (s31dt_Double F))
    (hman : letI := cs; IsManifold 𝓘(ℂ) ω (s31dt_Double F))
    (hJ : letI := cs; IsAnticonformalInvolution (s31dt_flipHomeomorph F)) :
    HasGenus (s31dt_Double F) (2 * g + m - 1) := by
  classical
  let _ := cs
  have : IsManifold 𝓘(ℂ) ω (s31dt_Double F) := hman
  have := s31dt_double_t2 F
  have := s31dt_double_compact F
  have := s31dt_double_connected F hm
  obtain ⟨x₀, p, hx₀, hp, hgen⟩ := s78fa_ext_generation F hm
  have hx : s31dt_flipHomeomorph F (s31dt_side F false x₀) = s31dt_side F false x₀ :=
    (s31dt_flip_fixed_side_iff F false x₀).mpr hx₀
  let q₀ := s31dt_side F false x₀
  let A : Module.End ℝ (Additive (FundamentalGroup (s31dt_Double F) q₀) →+ ℝ) :=
    { toFun := fun χ => χ.comp (MonoidHom.toAdditive (FundamentalGroup.mapOfEq
        (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hA : ∀ χ (γ : FundamentalGroup (s31dt_Double F) q₀),
      A χ (Additive.ofMul γ) =
        χ (Additive.ofMul (FundamentalGroup.mapOfEq
          (s31dt_flipHomeomorph F : C(s31dt_Double F, s31dt_Double F)) hx γ)) := fun _ _ => rfl
  obtain ⟨hplus, hminus⟩ :=
    s78no_anticonformal_character_eigen (s31dt_Double F) (s31dt_flipHomeomorph F) hJ q₀ hx A hA
  -- finite dimensionality of `V` (real period map) and of `W` (fold)
  obtain ⟨P, hP⟩ := k22rr_exists_real_period_map (X := s31dt_Double F) q₀
  have hbij : Function.Bijective P := ⟨k22rr_pi_injective q₀ P hP, k22rr_pd_surjective q₀ P hP⟩
  have : FiniteDimensional ℝ (Additive (FundamentalGroup (s31dt_Double F) q₀) →+ ℝ) :=
    LinearEquiv.finiteDimensional (LinearEquiv.ofBijective P hbij)
  obtain ⟨T, hTinj, hTmem⟩ := s78fa_fold_injective F x₀ hx A hA
  have : FiniteDimensional ℝ (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ) :=
    Module.Finite.of_injective T hTinj
  have hW := LinearMap.finrank_le_finrank_of_injective (f := T.codRestrict _ hTmem)
    (fun a b h => hTinj (congrArg Subtype.val h))
  have hge := s78fa_core_characters_ge F hm x₀
  have hle := s78fa_minus_le F hm x₀ p hx₀ hp hgen hx A hA
  obtain ⟨g', hg'⟩ := s78fa_ext_closed_genus (X := s31dt_Double F)
  have hgg := k22rr_genus_eq hg'
  have h1 : 2 * g + m - 1 ≤ genus (s31dt_Double F) := hge.trans (hW.trans_eq hplus)
  have h2 : genus (s31dt_Double F) ≤ 2 * g + m - 1 := hminus ▸ hle
  have h : g' = 2 * g + m - 1 := by rw [← hgg]; exact le_antisymm h2 h1
  rw [← h]
  exact hg'

/-! ### Terminal assembly -/

/-- The two sheets of the concrete double meet the original surface's images disjointly: `ιd(S)` and `J(ιd(S))` are
disjoint (the original surface avoids the seam). -/
theorem s31tm_disjoint {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) :
    Disjoint (range (s31dt_embed F false)) (range (s31dt_flipHomeomorph F ∘ s31dt_embed F false)) := by
  have e1 : range (s31dt_embed F false) = s31dt_side F false '' range (s31dt_originalCore F) :=
    range_comp _ _
  have e2 : range (s31dt_flipHomeomorph F ∘ s31dt_embed F false) =
      s31dt_side F true '' range (s31dt_originalCore F) := by
    ext q
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
  rw [e1, e2]
  apply s31dt_disjoint_opposite_images
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨s, rfl⟩
  exact s31dt_originalCore_not_boundary F s

/-- **Terminal assembly**: the statement of `exists_schottkyDouble` (S31), from the concrete double. -/
theorem s31tm_exists_schottkyDouble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) :
    ∃ (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier) (Pd : Finset Xd.carrier),
      IsSchottkyDouble F Xd J ιd Pd := by
  obtain ⟨cs, hman, hhol, hJ⟩ := s78ra_double_complex_atlas F
  let _ := cs
  have : IsManifold 𝓘(ℂ) ω (s31dt_Double F) := hman
  have := s31dt_double_t2 F
  have := s31dt_double_compact F
  have := s31dt_double_connected F hm
  obtain ⟨Pd, hPd, hcard, hinv, -⟩ := s31sd_concrete_marked_points F
  refine ⟨{ carrier := s31dt_Double F }, s31dt_flipHomeomorph F, s31dt_embed F false, Pd, ?_⟩
  exact
    { genus := s78fa_double_genus hm F cs hman hJ
      involution := hJ
      embedding := s31dt_embed_openEmbedding F false
      holomorphic := hhol
      disjoint := s31tm_disjoint F
      card_Pd := hcard
      Pd_invariant := hinv
      cover := s31sd_concrete_cover F _ (fun _ => rfl) Pd hPd
      fixed_curves := s31dt_fixed_curves F Pd hPd }

/-- §31.1: every surface of finite type with `m ≠ 0` holes has a Schottky double (obtained by gluing
`S` to its mirror image along the boundary curves). -/
theorem exists_schottkyDouble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) :
    ∃ (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier) (Pd : Finset Xd.carrier),
      IsSchottkyDouble F Xd J ιd Pd := by
  exact s31tm_exists_schottkyDouble hm F

end LiZhongQC
