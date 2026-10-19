/-
  The concrete Čech layer of the Riemann–Roch build: sections of the sheaf `𝒪_D`.

    * Sections of `𝒪_D` over an open `U ⊆ X` are modelled **intrinsically on the open
      submanifold `↥U`** (Mathlib gives `↥U` a `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` structure
      automatically), as a `Submodule ℂ` of the bare function space `↥U → ℂ`.
    * The membership predicate bundles meromorphy-on-`↥U` with the order bound `-D x ≤ ord_x f`.
    * Because sections are genuine functions on `↥U`, the Čech differential is plain **restriction**
      (precomposition with `Set.inclusion`), with no chart-transition cocycle data.

  The meromorphy infrastructure (`IsMeromorphic.zero` in `Jacobians.Abel`, the
  `MeromorphicFunction` ℂ-module instances in `Jacobians.RiemannRoch`) requires only
  `[ChartedSpace ℂ]`, so it applies to the non-compact open submanifold `↥U`. The bare-function
  encoding `Submodule ℂ (↥U → ℂ)` is used (rather than `Submodule ℂ (MeromorphicFunction ↥U)`)
  because it makes the Čech differential plain restriction.
-/
import Jacobians.Meromorphic.LinearSystem

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X]

/-- Order of a bare function on the open submanifold `↥U`, read in `U`'s own chart at `x`.
(Chart-invariant; intrinsic to `↥U`.) -/
noncomputable def ordU [ChartedSpace ℂ X] {U : Opens X} (f : U → ℂ) (x : U) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

/-- The order of the zero function on `↥U` is `⊤`. -/
theorem ordU_zero [ChartedSpace ℂ X] {U : Opens X} (x : U) : ordU (0 : U → ℂ) x = ⊤ := by
  rw [ordU, show ((0 : U → ℂ) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (0 : ℂ)) from rfl,
    meromorphicOrderAt_eq_top_iff]
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- `ordU f x = ⊤` forces `f` to be meromorphic at `x` (the order is the junk value `0` for
non-meromorphic functions, and `0 ≠ ⊤`). -/
private theorem meromorphicAt_of_ordU_eq_top [ChartedSpace ℂ X] {U : Opens X} {f : U → ℂ} {x : U}
    (h : ordU f x = ⊤) :
    MeromorphicAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) := by
  by_contra hc
  rw [ordU, meromorphicOrderAt_of_not_meromorphicAt hc] at h
  exact absurd h (by simp)

/-- **Sections of `𝒪_D` over an open `U`** (Forster's `𝒪_D(U)`): functions meromorphic on the open
submanifold `↥U` whose order is `≥ −D` at every point of `U`. A `Submodule ℂ` of `↥U → ℂ`. -/
noncomputable def OmegaD [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (U : Opens X) : Submodule ℂ (U → ℂ) where
  carrier := {f | IsMeromorphic (U : Type _) f ∧ ∀ x : U, (-(D x.1) : WithTop ℤ) ≤ ordU f x}
  add_mem' {f g} hf hg :=
    ⟨hf.1.add hg.1, fun x => le_trans (le_min (hf.2 x) (hg.2 x))
      (meromorphicOrderAt_add (hf.1 x) (hg.1 x))⟩
  zero_mem' := ⟨IsMeromorphic.zero _, fun x => by rw [ordU_zero]; exact le_top⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · simpa only [hc, zero_smul, ordU_zero] using le_top
    · refine le_trans (hf.2 x) (le_of_eq ?_)
      show ordU f x = ordU (c • f) x
      rw [ordU, ordU]
      exact (meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)).symm⟩

@[simp] theorem mem_OmegaD [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} {U : Opens X} {f : U → ℂ} :
    f ∈ OmegaD D U ↔ IsMeromorphic (U : Type _) f ∧ ∀ x : U, (-(D x.1) : WithTop ℤ) ≤ ordU f x :=
  Iff.rfl

/-! ### Sheaf restriction — the building block of the Čech differential

For `V ≤ U` (opens), restriction `𝒪_D(U) → 𝒪_D(V)` is plain precomposition with the open
inclusion `↥V → ↥U`. Both `↥V`- and `↥U`-charts are `OpenPartialHomeomorph.subtypeRestr`s of the
*same* ambient chart `chartAt ℂ v.1` (`TopologicalSpace.Opens.chartAt_eq`), so meromorphy and
order are preserved. -/

section Restriction
variable {U V : Opens X}

/-- The open inclusion `↥V → ↥U` for `V ≤ U`. -/
def openIncl (h : V ≤ U) : V → U := fun v => ⟨v.1, h v.2⟩

@[simp] theorem openIncl_val (h : V ≤ U) (v : V) : (openIncl h v).1 = v.1 := rfl

/-- The base point and the chart-pullback agree between `↥V`'s chart at `v` and `↥U`'s chart at
`openIncl h v`: both charts are `subtypeRestr`s of the *same* ambient chart `chartAt ℂ v.1`
(`Opens.chartAt_eq`), so they read `f` at the same ambient point near `v`. The shared core of the
two restriction lemmas. -/
theorem restrict_chart_aux [ChartedSpace ℂ X] (h : V ≤ U) (f : U → ℂ) (v : V) :
    (chartAt (H := ℂ) v) v = (chartAt (H := ℂ) (openIncl h v)) (openIncl h v) ∧
    ((f ∘ openIncl h) ∘ (chartAt (H := ℂ) v).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) v) v)]
      (f ∘ (chartAt (H := ℂ) (openIncl h v)).symm) := by
  have hbase : (chartAt (H := ℂ) v) v = (chartAt (H := ℂ) (openIncl h v)) (openIncl h v) := by
    simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
    rfl
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) v).target ∈ 𝓝 ((chartAt (H := ℂ) v) v) :=
    (chartAt (H := ℂ) v).open_target.mem_nhds
      ((chartAt (H := ℂ) v).map_source (mem_chart_source ℂ v))
  have ht2 : (chartAt (H := ℂ) (openIncl h v)).target ∈ 𝓝 ((chartAt (H := ℂ) v) v) := by
    rw [hbase]
    exact (chartAt (H := ℂ) (openIncl h v)).open_target.mem_nhds
      ((chartAt (H := ℂ) (openIncl h v)).map_source (mem_chart_source ℂ (openIncl h v)))
  refine Filter.eventuallyEq_of_mem (Filter.inter_mem ht1 ht2) fun w hw => ?_
  obtain ⟨hw1, hw2⟩ := hw
  show f (openIncl h ((chartAt (H := ℂ) v).symm w)) = f ((chartAt (H := ℂ) (openIncl h v)).symm w)
  congr 1
  apply Subtype.ext
  simp only [openIncl_val]
  have e1 : ((chartAt (H := ℂ) v).symm w).1 = (chartAt (H := ℂ) v.1).symm w := by
    simpa [Function.comp_def, TopologicalSpace.Opens.chartAt_eq] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) v.1) ⟨v⟩ hw1
  have e2 : ((chartAt (H := ℂ) (openIncl h v)).symm w).1 = (chartAt (H := ℂ) v.1).symm w := by
    simpa [Function.comp_def, TopologicalSpace.Opens.chartAt_eq] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) (openIncl h v).1)
        ⟨openIncl h v⟩ hw2
  rw [e1, e2]

/-- Restriction preserves the order at corresponding points (chart bookkeeping via
`Opens.chartAt_eq` + `subtypeRestr`). -/
theorem ordU_comp_openIncl [ChartedSpace ℂ X] (h : V ≤ U) (f : U → ℂ) (v : V) :
    ordU (f ∘ openIncl h) v = ordU f (openIncl h v) := by
  obtain ⟨hbase, hev⟩ := restrict_chart_aux h f v
  unfold ordU
  rw [show (chartAt (H := ℂ) (openIncl h v)) (openIncl h v) = (chartAt (H := ℂ) v) v
    from hbase.symm]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- Meromorphy on `↥U` restricts to the open sub-submanifold `↥V`. -/
theorem isMeromorphic_comp_openIncl [ChartedSpace ℂ X] (h : V ≤ U) {f : U → ℂ}
    (hf : IsMeromorphic (U : Type _) f) : IsMeromorphic (V : Type _) (f ∘ openIncl h) := by
  intro v
  obtain ⟨hbase, hev⟩ := restrict_chart_aux h f v
  have hmer := hf (openIncl h v)
  rw [← hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

/-- Restriction of sections `𝒪_D(U) → 𝒪_D(V)` for `V ≤ U`. -/
noncomputable def OmegaD.restrict [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (h : V ≤ U) :
    OmegaD D U →ₗ[ℂ] OmegaD D V :=
  ((LinearMap.funLeft ℂ ℂ (openIncl h)).domRestrict (OmegaD D U)).codRestrict (OmegaD D V)
    fun f => ⟨isMeromorphic_comp_openIncl h f.2.1, fun v => by
      show (-(D v.1) : WithTop ℤ) ≤ ordU ((f : U → ℂ) ∘ openIncl h) v
      rw [ordU_comp_openIncl h]; exact f.2.2 (openIncl h v)⟩

end Restriction

/-! ### Germ-class sections — the junk-free representation (`Filter.Germ` over `codiscreteWithin`)

Meromorphic functions are taken modulo `=ᶠ[codiscreteWithin]` (equality off a discrete set — the
removable-singularity junk), the standard equivalence of `Analysis.Meromorphic.NormalForm`.
Mathlib's `Filter.Germ` realises this quotient as a clean `ℂ`-algebra with *no* manual quotient
bookkeeping, so `𝒪_D`-sections and `h⁰` are junk-free automatically. -/

/-- **Germ-class functions on `↥U`**: `(↥U → ℂ)` modulo codiscrete equality — the junk-free section
space. A `ℂ`-module via `Filter.Germ`. -/
abbrev MGerm (U : Opens X) : Type _ := Filter.Germ (Filter.codiscreteWithin (Set.univ : Set U)) ℂ

/-- The germ projection `(↥U → ℂ) →ₗ[ℂ] MGerm U` (quotient by germ-zero junk). -/
def toGerm (U : Opens X) : (U → ℂ) →ₗ[ℂ] MGerm U where
  toFun f := (f : MGerm U)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section GermRestriction
variable {U V : Opens X}

/-- The open inclusion `↥V → ↥U` pulls codiscrete sets back to codiscrete sets (it is an open
embedding), so precomposition descends to germ-classes. -/
theorem tendsto_openIncl (h : V ≤ U) :
    Filter.Tendsto (openIncl h) (Filter.codiscreteWithin (Set.univ : Set V))
      (Filter.codiscreteWithin (Set.univ : Set U)) := by
  have hemb := TopologicalSpace.Opens.isOpenEmbedding_of_le h
  rw [Filter.codiscreteWithin]
  refine Filter.tendsto_iSup.2 fun v => Filter.tendsto_iSup.2 fun _ => ?_
  refine Filter.Tendsto.mono_right ?_
    (le_iSup₂_of_le (openIncl h v) (Set.mem_univ _) le_rfl)
  refine (hemb.continuous.continuousWithinAt).tendsto_nhdsWithin (fun w hw => ?_)
  simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hw ⊢
  exact fun hc => hw (hemb.injective hc)

/-- Restriction on germ-classes `MGerm U →ₗ[ℂ] MGerm V` (`V ≤ U`): precomposition with the open
inclusion, descended to germs. -/
noncomputable def rawRestrictG (h : V ≤ U) : MGerm U →ₗ[ℂ] MGerm V where
  toFun f := f.compTendsto (openIncl h) (tendsto_openIncl h)
  map_add' f g := by
    induction f using Filter.Germ.inductionOn with | _ f =>
    induction g using Filter.Germ.inductionOn with | _ g =>
    rfl
  map_smul' c f := by
    induction f using Filter.Germ.inductionOn with | _ f => rfl

@[simp] theorem rawRestrictG_coe (h : V ≤ U) (f : U → ℂ) :
    rawRestrictG h (toGerm U f) = toGerm V (f ∘ openIncl h) := rfl

end GermRestriction

/-- Germ restriction along the reflexive containment `U ≤ U` is the identity (`openIncl h` is the
identity map on `↥U` for any `h : U ≤ U`, so the germ pullback is the identity).  The `≤`-proof is
taken explicitly so this canonical form covers every call site (`le_rfl`, `le_refl U`, or a generic
`h : U ≤ U`); the `@[simp]` form fires regardless of which proof is supplied. -/
@[simp] theorem rawRestrictG_le_rfl {U : Opens X} (h : U ≤ U) (f : MGerm U) :
    rawRestrictG h f = f := by
  induction f using Filter.Germ.inductionOn with | _ f => rfl

/-- **`𝒪_D`-sections as germ-classes**: the image of `OmegaD` under the germ projection — junk-free,
no quotient. -/
noncomputable def OmegaDGerm [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (U : Opens X) : Submodule ℂ (MGerm U) :=
  Submodule.map (toGerm U) (OmegaD D U)

/-- Germ restriction preserves `𝒪_D`-sections. -/
theorem rawRestrictG_omegaDGerm [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} {U V : Opens X} (h : V ≤ U) {f : MGerm U}
    (hf : f ∈ OmegaDGerm D U) : rawRestrictG h f ∈ OmegaDGerm D V := by
  obtain ⟨g, hg, rfl⟩ := hf
  exact ⟨g ∘ openIncl h, (OmegaD.restrict h ⟨g, hg⟩).2, rfl⟩

end Jacobians.Dolbeault
