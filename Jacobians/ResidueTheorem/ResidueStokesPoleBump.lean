/-
  Pole bumps for the genus-uniform residue theorem (geometry).

  For the finite enlarged pole set `S` (poles ∪ the finite analytic-bad locus), this file
  constructs the per-pole radial bump data Forster's proof of the Residue Theorem (GTM 81,
  10.21) chooses: pairwise-separated coordinate balls around the poles and smooth radial
  cutoffs `≡ 1` near each pole, supported inside its ball.

  * `PoleBumpData` — per pole `a ∈ S`: a radius `ε a` with the closed coordinate ball inside
    the chart target and its `X`-side ball (`poleBall`) meeting `S` only in `{a}`, plus a
    SMOOTH radial profile `η a` going `1 → 0` between `ε²/4` and `ε²/2`.
  * `exists_poleBumpData` — existence (chart targets are open; `S` is finite and `X` is T1,
    so each pole has a chart neighbourhood avoiding the other members of `S`).
  * `PoleBumpData.bump a : X → ℝ` — the bump `η_a(normSq(chart_a · − chart_a a))` extended by
    `0` (supported in `poleBall a`), with: global smoothness, `≡ 1` near `a`, `≡ 0` near every
    other point of `S` and outside `poleBall a`.
  * `PoleBumpData.totalBump = ∑_{a ∈ S} bump a` — Forster's `f₁ + ⋯ + f_n`: smooth, `≡ 1`
    near EVERY point of `S`.

  Everything here is complete and depends on no unproved lemma.
-/
import Jacobians.PlanarStokes.AnnulusResidueMeromorphic
import Jacobians.Surface.RealManifold
set_option backward.isDefEq.respectTransparency false

open Complex Metric MeasureTheory Filter Set Topology
open scoped Manifold ContDiff

namespace Jacobians.Dolbeault.StokesResidue

open Jacobians.Dolbeault Jacobians

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### A smooth cutoff profile (the `C^∞` upgrade of `exists_cutoff_profile`) -/

/-- A `C^∞` profile `η` with `η ≡ 1` on `(-∞, s₀]` and `η ≡ 0` on `[s₁, ∞)` (the smooth version
of `exists_cutoff_profile` — same `Real.smoothTransition` construction). -/
theorem exists_smooth_cutoff_profile {s₀ s₁ : ℝ} (h : s₀ < s₁) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ s ≤ s₀, η s = 1) ∧ (∀ s, s₁ ≤ s → η s = 0) := by
  refine ⟨fun s => Real.smoothTransition ((s₁ - s) / (s₁ - s₀)), ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      ((contDiff_const.sub contDiff_id).div_const _)
  · intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))
  · intro s hs
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-! ### The per-pole bump data -/

/-- **Per-pole radial bump data over the finite set `S`** (Forster 10.21's choice of coordinate
neighbourhoods and cutoffs): for each `a ∈ S`, a radius `ε a > 0` with the closed coordinate
ball inside the chart target, whose `X`-side ball meets `S` only in `{a}`, and a smooth radial
profile `η a` going `1 → 0` between `(ε a)²/4` and `(ε a)²/2`. -/
structure PoleBumpData (S : Finset X) where
  ε : X → ℝ
  η : X → ℝ → ℝ
  hε : ∀ a ∈ S, 0 < ε a
  hball : ∀ a ∈ S,
    closedBall ((chartAt (H := ℂ) a) a) (ε a) ⊆ (chartAt (H := ℂ) a).target
  hsep : ∀ a ∈ S, ∀ x ∈ S,
    x ∈ (chartAt (H := ℂ) a).symm '' closedBall ((chartAt (H := ℂ) a) a) (ε a) → x = a
  hη : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (η a)
  hη1 : ∀ a ∈ S, ∀ s ≤ ε a ^ 2 / 4, η a s = 1
  hη0 : ∀ a ∈ S, ∀ s, ε a ^ 2 / 2 ≤ s → η a s = 0

/-- **Existence of the bump data**: chart targets are open, `S` is finite and `X` is T1, so each
`a ∈ S` has a chart-image neighbourhood whose `X`-side ball avoids `S \ {a}`. -/
theorem exists_poleBumpData [T2Space X] [CompactSpace X] (S : Finset X) :
    Nonempty (PoleBumpData S) := by
  classical
  -- the global fallback profile (for the junk values off `S`)
  obtain ⟨η₀, hη₀, _, _⟩ := exists_smooth_cutoff_profile (show (0 : ℝ) < 1 by norm_num)
  -- per-point choice
  have hchoice : ∀ a : X, ∃ (ε : ℝ) (η : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) η ∧
      (a ∈ S → 0 < ε
        ∧ closedBall ((chartAt (H := ℂ) a) a) ε ⊆ (chartAt (H := ℂ) a).target
        ∧ (∀ x ∈ S, x ∈ (chartAt (H := ℂ) a).symm '' closedBall ((chartAt (H := ℂ) a) a) ε
            → x = a)
        ∧ (∀ s ≤ ε ^ 2 / 4, η s = 1) ∧ (∀ s, ε ^ 2 / 2 ≤ s → η s = 0)) := by
    intro a
    by_cases haS : a ∈ S
    · set φ := chartAt (H := ℂ) a with hφdef
      -- the open neighbourhood of `a` avoiding the rest of `S`
      set N : Set X := φ.source ∩ (↑(S.erase a) : Set X)ᶜ with hNdef
      have hNopen : IsOpen N := φ.open_source.inter
        (((S.erase a).finite_toSet.isClosed).isOpen_compl)
      have haN : a ∈ N := ⟨mem_chart_source ℂ a, by simp⟩
      have hNsub : N ⊆ φ.source := Set.inter_subset_left
      have himg_open : IsOpen (φ '' N) := φ.isOpen_image_of_subset_source hNopen hNsub
      have himg_mem : φ a ∈ φ '' N := Set.mem_image_of_mem _ haN
      obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp himg_open _ himg_mem
      refine ⟨δ / 2, ?_⟩
      obtain ⟨η, hη, hη1, hη0⟩ :=
        exists_smooth_cutoff_profile (show (δ / 2) ^ 2 / 4 < (δ / 2) ^ 2 / 2 by
          have : 0 < (δ / 2) ^ 2 := by positivity
          linarith)
      refine ⟨η, hη, fun _ => ⟨by positivity, ?_, ?_, hη1, hη0⟩⟩
      · -- the closed `δ/2`-ball sits inside `φ '' N ⊆ φ.target`
        intro z hz
        have hzN : z ∈ φ '' N :=
          hδball (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
        obtain ⟨x, hxN, rfl⟩ := hzN
        exact φ.map_source (hNsub hxN)
      · -- the `X`-side ball avoids `S \ {a}`
        intro x hxS hximg
        obtain ⟨z, hz, rfl⟩ := hximg
        have hzN : z ∈ φ '' N :=
          hδball (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
        obtain ⟨x', hx'N, rfl⟩ := hzN
        rw [φ.left_inv (hNsub hx'N)] at hxS ⊢
        by_contra hne
        exact hx'N.2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hxS⟩))
    · exact ⟨1, η₀, hη₀, fun hmem => absurd hmem haS⟩
  choose ε η hηall hspec using hchoice
  exact ⟨{
    ε := ε
    η := η
    hε := fun a ha => (hspec a ha).1
    hball := fun a ha => (hspec a ha).2.1
    hsep := fun a ha => (hspec a ha).2.2.1
    hη := hηall
    hη1 := fun a ha => (hspec a ha).2.2.2.1
    hη0 := fun a ha => (hspec a ha).2.2.2.2 }⟩

namespace PoleBumpData

variable {S : Finset X} (D : PoleBumpData S)

/-- The `X`-side closed coordinate ball around the pole `a`. -/
noncomputable def poleBall (a : X) : Set X :=
  (chartAt (H := ℂ) a).symm '' closedBall ((chartAt (H := ℂ) a) a) (D.ε a)

theorem poleBall_subset_source {a : X} (ha : a ∈ S) :
    D.poleBall a ⊆ (chartAt (H := ℂ) a).source := by
  rintro x ⟨z, hz, rfl⟩
  exact (chartAt (H := ℂ) a).map_target (D.hball a ha hz)

theorem isCompact_poleBall {a : X} (ha : a ∈ S) : IsCompact (D.poleBall a) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt (H := ℂ) a).continuousOn_symm.mono (D.hball a ha))

/-- Membership of the chart image in the closed coordinate ball, for source points. -/
theorem mem_poleBall_iff {a : X} (ha : a ∈ S) {x : X}
    (hx : x ∈ (chartAt (H := ℂ) a).source) :
    x ∈ D.poleBall a ↔ (chartAt (H := ℂ) a) x ∈ closedBall ((chartAt (H := ℂ) a) a) (D.ε a) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [(chartAt (H := ℂ) a).right_inv (D.hball a ha hz)]
  · intro hz
    exact ⟨(chartAt (H := ℂ) a) x, hz, (chartAt (H := ℂ) a).left_inv hx⟩

/-! ### The bump functions -/

open scoped Classical in
/-- The radial bump at the pole `a`: `η_a(normSq(chart_a x − chart_a a))` on the chart source,
extended by `0` (the extension is smooth: the bump is supported in `poleBall a`). -/
noncomputable def bump (a : X) : X → ℝ := fun x =>
  if x ∈ (chartAt (H := ℂ) a).source
    then D.η a (Complex.normSq ((chartAt (H := ℂ) a) x - (chartAt (H := ℂ) a) a))
    else 0

/-- The bump vanishes outside `poleBall a` (pointwise). -/
theorem bump_eq_zero_of_notMem {a : X} (ha : a ∈ S) {x : X} (hx : x ∉ D.poleBall a) :
    D.bump a x = 0 := by
  rw [bump]
  by_cases hsrc : x ∈ (chartAt (H := ℂ) a).source
  · rw [if_pos hsrc]
    set φ := chartAt (H := ℂ) a with hφdef
    have hz : φ x ∉ closedBall (φ a) (D.ε a) := fun hmem =>
      hx ((D.mem_poleBall_iff ha hsrc).mpr hmem)
    have hgt : D.ε a ^ 2 < Complex.normSq (φ x - φ a) := by
      rw [mem_closedBall, not_le, Complex.dist_eq] at hz
      have habs : Complex.normSq (φ x - φ a) = ‖φ x - φ a‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      nlinarith [norm_nonneg (φ x - φ a), (D.hε a ha).le]
    refine D.hη0 a ha _ ?_
    nlinarith [sq_nonneg (D.ε a)]
  · rw [if_neg hsrc]

/-- The bump is `≡ 1` near its own pole. -/
theorem bump_eventually_one {a : X} (ha : a ∈ S) : ∀ᶠ x in 𝓝 a, D.bump a x = 1 := by
  set φ := chartAt (H := ℂ) a with hφdef
  have hcont : ContinuousAt (fun x => Complex.normSq (φ x - φ a)) a := by
    refine (contDiff_normSq_sub (φ a)).continuous.continuousAt.comp ?_
    exact φ.continuousAt (mem_chart_source ℂ a)
  have hval : Complex.normSq (φ a - φ a) < D.ε a ^ 2 / 4 := by
    have := D.hε a ha
    simp only [sub_self, Complex.normSq_zero]
    positivity
  have h1 : ∀ᶠ x in 𝓝 a, Complex.normSq (φ x - φ a) < D.ε a ^ 2 / 4 :=
    hcont.preimage_mem_nhds (Iio_mem_nhds hval)
  have h2 : ∀ᶠ x in 𝓝 a, x ∈ φ.source :=
    φ.open_source.mem_nhds (mem_chart_source ℂ a)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [bump, if_pos hx2]
  exact D.hη1 a ha _ hx1.le

/-- The chart-`a` read of `bump a` is the planar radial cutoff, near every target point. -/
theorem bump_read_eventuallyEq {a : X} (_ha : a ∈ S) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) a).target) :
    (fun w => ((D.bump a ((chartAt (H := ℂ) a).symm w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((D.η a (Complex.normSq (w - (chartAt (H := ℂ) a) a)) : ℝ) : ℂ) := by
  set φ := chartAt (H := ℂ) a with hφdef
  filter_upwards [φ.open_target.mem_nhds hz] with w hw
  rw [bump, if_pos (φ.map_target hw), φ.right_inv hw]

variable [T2Space X]

/-- The bump of `a` is `≡ 0` near every other point of `S` (the separation field). -/
theorem bump_eventually_zero_of_ne {a : X} (ha : a ∈ S) {p : X} (hp : p ∈ S) (hne : p ≠ a) :
    ∀ᶠ x in 𝓝 p, D.bump a x = 0 := by
  have hpB : p ∉ D.poleBall a := fun hmem => hne (D.hsep a ha p hp hmem)
  have hopen : IsOpen (D.poleBall a)ᶜ := (D.isCompact_poleBall ha).isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds hpB] with x hx
  exact D.bump_eq_zero_of_notMem ha hx

/-- The bump is `≡ 0` near every point outside `poleBall a`. -/
theorem bump_eventually_zero_of_notMem {a : X} (ha : a ∈ S) {p : X}
    (hp : p ∉ D.poleBall a) : ∀ᶠ x in 𝓝 p, D.bump a x = 0 := by
  have hopen : IsOpen (D.poleBall a)ᶜ := (D.isCompact_poleBall ha).isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds hp] with x hx
  exact D.bump_eq_zero_of_notMem ha hx

/-! ### The total bump `u = ∑ bump a` -/

/-- Forster's `f₁ + ⋯ + f_n`: the sum of the per-pole bumps. -/
noncomputable def totalBump : X → ℝ := fun x => ∑ a ∈ S, D.bump a x

/-- **The total bump is `≡ 1` near every point of `S`** (its own bump is `1`, the others
vanish — the separation field). -/
theorem totalBump_eventually_one {p : X} (hp : p ∈ S) :
    ∀ᶠ x in 𝓝 p, D.totalBump x = 1 := by
  classical
  have hall : ∀ᶠ x in 𝓝 p, ∀ a ∈ S, D.bump a x = if a = p then 1 else 0 := by
    rw [eventually_all_finset]
    intro a ha
    rcases eq_or_ne a p with rfl | hne
    · filter_upwards [D.bump_eventually_one ha] with x hx
      rw [hx, if_pos rfl]
    · filter_upwards [D.bump_eventually_zero_of_ne ha hp hne.symm] with x hx
      rw [hx, if_neg hne]
  filter_upwards [hall] with x hx
  rw [totalBump, Finset.sum_congr rfl hx, Finset.sum_ite_eq' S p (fun _ => (1 : ℝ)), if_pos hp]

variable [IsManifold 𝓘(ℂ) ω X]

/-- **The bump is globally smooth** (`C^∞` chart read on the source; locally `0` off the
compact `poleBall`). -/
theorem contMDiff_bump {a : X} (ha : a ∈ S) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (D.bump a) := by
  set φ := chartAt (H := ℂ) a with hφdef
  intro x
  by_cases hsrc : x ∈ φ.source
  · -- on the source: the honest chart read, smooth
    have hev : D.bump a =ᶠ[𝓝 x]
        fun x' => D.η a (Complex.normSq (φ x' - φ a)) := by
      filter_upwards [φ.open_source.mem_nhds hsrc] with x' hx'
      rw [bump, if_pos hx']
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ x :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := a)) _ hsrc).contMDiffAt
        (φ.open_source.mem_nhds hsrc)
    have hplanar : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => D.η a (Complex.normSq (z - φ a))) :=
      (D.hη a).comp (contDiff_normSq_sub (φ a))
    exact hplanar.contMDiff.contMDiffAt.comp x hchart
  · -- off the source (hence off `poleBall`): locally `0`
    have hxB : x ∉ D.poleBall a := fun hmem => hsrc (D.poleBall_subset_source ha hmem)
    refine ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (D.bump_eventually_zero_of_notMem ha hxB)

theorem contMDiff_totalBump : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) D.totalBump := by
  show ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) fun x => ∑ a ∈ S, D.bump a x
  exact ContMDiff.sum fun a ha => D.contMDiff_bump ha

end PoleBumpData

end Jacobians.Dolbeault.StokesResidue
