/-
  THE GENUS-UNIFORM PAIR-FORM RESIDUE THEOREM (Forster GTM 81, Theorem 10.21).

  For meromorphic `g₀ h` on the compact Riemann surface `X` (the pair-form `ω = h·dg₀`) and any
  finite `poles` off which the pair integrand is honestly analytic at the chart centres,

    `∑ a ∈ poles, pairFormResidue g₀ h a = 0`    (`residueSum_pairForm_eq_zero_unconditional`)

  with **no genus hypothesis** — the planar-Stokes proof, not the ω₀-factorization reduction of
  `PairFormResidueTheorem.residueSum_pairForm_eq_zero` (which needs `0 < genus X` to pick a
  nonzero holomorphic form).

  ## The ledger (Forster's proof, with the global `∫∫_X` UNFOLDED into chart reads)

  Work over the enlarged pole set `S = poles ∪ {¬ReadsAnalyticAt}` (finite).  Choose the
  Forster bump data (`PoleBumpData`): radial cutoffs `bump a ≡ 1` near each `a ∈ S`, supported
  in pairwise-`S`-separated coordinate balls; `u = totalBump = ∑ bump a`.  Take the genuine
  chart-cover PoU `ρ_j` (`ChartCoverDbarGlue`).  All integrals are plane integrals of the ONE
  canonical `ledgerIntegrand` shape (`ResidueLedgerTransport`); every step below is a finite
  sum/integral identity:

  1. per `a ∈ S`:  `∫_ℂ ∂̄(χ_a·f_a) = −π·Res_a` — the single-pole atom, in chart `a`;
  2. insert `1 = ∑_j ρ_j` under the integral, transport each `(a,j)` piece to chart `j`
     (the chart-change invariance), and aggregate `∑_a ∂̄(bump a) = ∂̄u`:
     `−π·∑_{a∈S} Res_a = ∑_j ∫_ℂ ρ̂_j·∂̄û·f̂_j`;
  3. per `j`, planar Stokes (Forster 10.20): `∫_ℂ ∂̄(ρ̂_j·(û−1)·f̂_j) = 0` — the
     function is `C¹` (`(û−1)f̂` extends by `0` across the poles since `u ≡ 1` there) with
     compact support; Leibniz gives `∫ ρ̂_j·∂̄û·f̂_j = −∫ (û−1)·∂̄ρ̂_j·f̂_j`;
  4. for the right side, repeat the insert-and-transport shuffle with `∑_i ρ_i = 1` and use
     `∑_j ∂̄ρ̂_j = 0` (the PoU sums to `1`): it vanishes.

  Hence `−π·∑_{a∈S} Res_a = 0`; the `S \ poles` terms vanish by the analyticity hypothesis.

  Also provided: `residueSum_pairForm_mul_eq_zero_unconditional` (the product-numerator wrapper,
  same shape as the genus ≥ 1 version) — the LaurentTail consumer can swap `hgenus`-versions for
  these by deleting the genus argument.
-/
import Jacobians.ResidueTheorem.ResidueLedgerTransport
import Jacobians.ResidueTheorem.ResidueStokesPoleBump
import Jacobians.ResidueTheorem.ResidueStokesCoverPoU
import Jacobians.ResidueTheorem.PairFormResidueTheorem

set_option backward.isDefEq.respectTransparency false

open Complex Metric MeasureTheory Filter Set Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.StokesResidue

open Jacobians.Dolbeault Jacobians Jacobians.Montel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Two more pointwise ledger lemmas (scalar-field sums; constant cutoffs) -/

/-- Scalar-field sums pass through the ledger integrand (the field enters by value). -/
theorem ledgerIntegrand_sum_P {ι : Type*} (s : Finset ι) (PF : ι → X → ℂ)
    (g₀ h : MeromorphicFunction X) (v : X → ℝ) (y : X) (V : Set X) (z : ℂ) :
    ∑ i ∈ s, ledgerIntegrand g₀ h (PF i) v y V z
      = ledgerIntegrand g₀ h (fun x => ∑ i ∈ s, PF i x) v y V z := by
  rw [ledgerIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · simp only [ledgerIntegrand, if_pos hz]
    rw [Finset.sum_mul, Finset.sum_mul]
  · simp only [ledgerIntegrand, if_neg hz, Finset.sum_const_zero]

/-- A constant cutoff has vanishing `∂̄`-read: the ledger integrand is identically `0`. -/
theorem ledgerIntegrand_const_v (g₀ h : MeromorphicFunction X) (P : X → ℂ) (cst : ℝ)
    (y : X) (V : Set X) : ledgerIntegrand g₀ h P (fun _ => cst) y V = fun _ => 0 := by
  funext z
  rw [ledgerIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) y) '' V
  · rw [if_pos hz]
    have hconst : (fun w => (((fun _ : X => cst) ((chartAt (H := ℂ) y).symm w) : ℝ) : ℂ))
        = fun _ => ((cst : ℝ) : ℂ) := rfl
    rw [hconst, DbarDisk.dbar_const, mul_zero, zero_mul]
  · rw [if_neg hz]

/-! ### The pair coefficient at a pole: meromorphy and the bump `∂̄`-read -/

/-- The pair coefficient is meromorphic at its own chart centre. -/
theorem meromorphicAt_pairRead (g₀ h : MeromorphicFunction X) (a : X) :
    MeromorphicAt (pairRead g₀ h a) ((chartAt (H := ℂ) a) a) := by
  have hh := h.meromorphic a
  have hg := (g₀.meromorphic a).deriv
  exact hh.mul hg

/-- The `∂̄`-read of the pole bump in its own chart is the explicit radial closed form
`η′(normSq(z−c))·(z−c)`. -/
theorem PoleBumpData.dbar_bumpRead {S : Finset X} (D : PoleBumpData S) {a : X} (ha : a ∈ S)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) a).target) :
    DbarDisk.dbar (fun w => ((D.bump a ((chartAt (H := ℂ) a).symm w) : ℝ) : ℂ)) z
      = Complex.ofReal (deriv (D.η a) (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
        * (z - (chartAt (H := ℂ) a) a) := by
  rw [DbarDisk.dbar_congr (D.bump_read_eventuallyEq ha hz),
    dbar_comp_normSq ((D.hη a).of_le (by simp)) _ z]

/-! ### Assembly context

Throughout: `g₀ h` meromorphic, `S` the enlarged pole set (containing the analytic-bad locus),
`D` the bump data, `ρ_j` the genuine chart-cover PoU over `c_j := coverCenter j`. -/

section Assembly

variable (g₀ h : MeromorphicFunction X) {S : Finset X} (D : PoleBumpData S)

/-- The complexified total bump. -/
noncomputable def uC (D : PoleBumpData S) : X → ℂ := fun x => ((D.totalBump x : ℝ) : ℂ)

theorem continuous_uC [CompactSpace X] [T2Space X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] : Continuous (uC D) :=
  Complex.continuous_ofReal.comp D.contMDiff_totalBump.continuous

/-- Good points off `S`. -/
theorem readsAnalyticAt_of_notMem (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    (x : X) (hx : x ∉ (S : Set X)) :
    ReadsAnalyticAt g₀ h x := by
  by_contra hbad
  exact hx (hSbad x hbad)

/-! #### Step 1 — the per-pole atom in the pole's own chart -/

/-- **(L1)** `∫_ℂ η′_a(normSq(z−c_a))·(z−c_a)·f_a(z) = −π·pairFormResidue g₀ h a` — the
closed-form single-pole atom, applied to the pair coefficient in the chart at `a`. -/
theorem integral_psi_eq [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    {a : X} (ha : a ∈ S) :
    ∫ z : ℂ, (Complex.ofReal (deriv (D.η a)
        (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
      * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z)
      = -(π : ℂ) * pairFormResidue g₀ h a := by
  set φ := chartAt (H := ℂ) a with hφdef
  have hε := D.hε a ha
  have hε2 : (0 : ℝ) < D.ε a ^ 2 := by positivity
  have hs₀ : (0 : ℝ) < D.ε a ^ 2 / 4 := by positivity
  have hs : D.ε a ^ 2 / 4 < D.ε a ^ 2 / 2 := by linarith
  have hs₁r : D.ε a ^ 2 / 2 < D.ε a ^ 2 := by linarith
  have hman : ∀ z ∈ ball (φ a) (D.ε a) \ {φ a}, AnalyticAt ℂ (pairRead g₀ h a) z := by
    -- punctured analyticity: the ball avoids `S` except at the centre
    intro z hz
    obtain ⟨hzball, hzne⟩ := hz
    have hzC : z ∈ closedBall (φ a) (D.ε a) := ball_subset_closedBall hzball
    have hz_tgt : z ∈ φ.target := D.hball a ha hzC
    set x := φ.symm z with hxdef
    have hzx : φ x = z := φ.right_inv hz_tgt
    have hxB : x ∈ D.poleBall a := ⟨z, hzC, rfl⟩
    have hxsrc : x ∈ φ.source := D.poleBall_subset_source ha hxB
    have hxa : x ≠ a := by
      intro hcontra
      apply (Set.mem_singleton_iff.not.mp hzne)
      rw [← hzx, hcontra]
    have hxS : x ∉ (S : Set X) := by
      intro hmem
      exact hxa (D.hsep a ha x hmem hxB)
    have hgood := readsAnalyticAt_of_notMem g₀ h hSbad x hxS
    have := analyticAt_pairRead hgood hxsrc
    rwa [hzx] at this
  have hres : resAt (pairRead g₀ h a) (φ a) = pairFormResidue g₀ h a := rfl
  rw [← hres]
  exact integral_radialDeriv_mul_eq_resAt (φ a) ((D.hη a).of_le (by simp))
    hs₀ hs (D.hη1 a ha) (D.hη0 a ha) (meromorphicAt_pairRead g₀ h a) hε hs₁r hman

/-! #### Step 2 — bridging the per-pole integrand to the ledger shape -/

/-- The window of the `(a,j)` ledger piece: the pole chart's source meets the PoU chart. -/
def poleWindow [T2Space X] [CompactSpace X] (a : X)
    (j : Fin ((chartCover : Finset X).card)) : Set X :=
  (chartAt (H := ℂ) a).source ∩ chartOpen (X := X) (coverCenter j)

theorem poleWindow_isOpen [T2Space X] [CompactSpace X] (a : X)
    (j : Fin ((chartCover : Finset X).card)) :
    IsOpen (poleWindow (X := X) a j) :=
  (chartAt (H := ℂ) a).open_source.inter (chartOpen_isOpen (coverCenter j))

theorem poleWindow_subset_pole [T2Space X] [CompactSpace X] (a : X)
    (j : Fin ((chartCover : Finset X).card)) :
    poleWindow (X := X) a j ⊆ (chartAt (H := ℂ) a).source := Set.inter_subset_left

theorem poleWindow_subset_cover [T2Space X] [CompactSpace X] (a : X)
    (j : Fin ((chartCover : Finset X).card)) :
    poleWindow (X := X) a j ⊆ (chartAt (H := ℂ) (coverCenter j)).source :=
  Set.inter_subset_right.trans
    (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))

/-- **(L2 bridge)** the raw `ρ_j`-weighted pole integrand IS the `(a,j)` ledger integrand:

`ρ_j(chart_a⁻¹ z)·[η′_a·(z−c_a)·f_a(z)] = ledgerIntegrand (ρC_j) (bump a) a (poleWindow a j)`.

Off the window everything vanishes pointwise (the profile derivative below `ε²/4`/above
`ε²/2`; the PoU factor off `tsupport ρ_j` on the annulus). -/
theorem rho_psi_eq_ledger [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] {a : X} (ha : a ∈ S) (j : Fin ((chartCover : Finset X).card)) :
    (fun z : ℂ => coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
        * (Complex.ofReal (deriv (D.η a) (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
          * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z))
      = ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a) a (poleWindow a j) := by
  classical
  set φ := chartAt (H := ℂ) a with hφdef
  funext z
  rw [ledgerIntegrand]
  by_cases hz : z ∈ φ '' poleWindow (X := X) a j
  · rw [if_pos hz]
    have hz_tgt : z ∈ φ.target :=
      (symm_mem_of_mem_image (poleWindow_subset_pole a j) hz).1
    rw [D.dbar_bumpRead ha hz_tgt]
    ring
  · rw [if_neg hz]
    -- trichotomy on the radius
    rcases lt_or_ge (Complex.normSq (z - φ a)) (D.ε a ^ 2 / 4) with hlt | hge
    · rw [radialDeriv_eq_zero_of_lt (D.hη1 a ha) hlt, Complex.ofReal_zero, zero_mul,
        zero_mul, mul_zero]
    rcases lt_or_ge (D.ε a ^ 2 / 2) (Complex.normSq (z - φ a)) with hgt | hle
    · rw [radialDeriv_eq_zero_of_gt (D.hη0 a ha) hgt, Complex.ofReal_zero, zero_mul,
        zero_mul, mul_zero]
    -- the annulus: the point is honest, so it must be off `tsupport ρ_j`
    · have hε := D.hε a ha
      have hzC : z ∈ closedBall (φ a) (D.ε a) := by
        rw [mem_closedBall, Complex.dist_eq]
        have habs : Complex.normSq (z - φ a) = ‖z - φ a‖ ^ 2 := Complex.normSq_eq_norm_sq _
        nlinarith [norm_nonneg (z - φ a)]
      have hz_tgt : z ∈ φ.target := D.hball a ha hzC
      set x := φ.symm z with hxdef
      have hzx : φ x = z := φ.right_inv hz_tgt
      have hxB : x ∈ D.poleBall a := ⟨z, hzC, rfl⟩
      have hxsrc : x ∈ φ.source := D.poleBall_subset_source ha hxB
      have hxW : x ∉ poleWindow (X := X) a j := by
        intro hmem
        exact hz ⟨x, hmem, hzx⟩
      have hxopen : x ∉ chartOpen (X := X) (coverCenter j) := fun hmem => hxW ⟨hxsrc, hmem⟩
      have hxts : x ∉ tsupport (coverPoU (X := X) j) := fun hmem =>
        hxopen (coverPoU_tsupport_subset (X := X) j hmem)
      rw [coverRhoC_eq_zero_of_notMem (X := X) j hxts, zero_mul]

/-! #### Local-constancy kills at the poles -/

/-- Every pole bump is locally constant near every point of `S` (`1` near its own pole, `0`
near the others). -/
theorem bump_locally_const_on_S [T2Space X] {a : X} (ha : a ∈ S) {p : X} (hp : p ∈ S) :
    ∃ cst : ℝ, ∀ᶠ x' in 𝓝 p, D.bump a x' = cst := by
  rcases eq_or_ne p a with rfl | hne
  · exact ⟨1, D.bump_eventually_one ha⟩
  · exact ⟨0, D.bump_eventually_zero_of_ne ha hp hne⟩

/-- The total bump is locally `≡ 1` near every point of `S`. -/
theorem totalBump_locally_const_on_S [T2Space X] {p : X} (hp : p ∈ S) :
    ∃ cst : ℝ, ∀ᶠ x' in 𝓝 p, D.totalBump x' = cst :=
  ⟨1, D.totalBump_eventually_one hp⟩

/-- `uC − 1` vanishes locally near every point of `S`. -/
theorem uC_sub_one_eventually_zero [T2Space X]
    (_hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    {p : X} (hp : p ∈ S) : ∀ᶠ x' in 𝓝 p, uC D x' - 1 = 0 := by
  filter_upwards [D.totalBump_eventually_one hp] with x' hx'
  rw [uC]
  simp only [hx', Complex.ofReal_one, sub_self]

/-! #### Integrability of the ledger pieces -/

/-- Integrability of the `(a,j)` pole pieces (in either chart, over any window containing the
compact core `poleBall a ∩ tsupport ρ_j`). -/
theorem integrable_polePiece [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    {a : X} (ha : a ∈ S) (j : Fin ((chartCover : Finset X).card))
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    (hKV : D.poleBall a ∩ tsupport (coverPoU (X := X) j) ⊆ V) :
    Integrable (ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a) y V) volume := by
  refine integrable_ledgerIntegrand g₀ h (continuous_coverRhoC (X := X) j)
    (D.contMDiff_bump ha) hVopen hVsub
    ((D.isCompact_poleBall ha).inter_right (isClosed_tsupport _)) hKV ?_ ?_
  · intro x hxV hxK
    by_cases hxB : x ∈ D.poleBall a
    · refine Or.inl (coverRhoC_eq_zero_of_notMem (X := X) j fun hts => hxK ⟨hxB, hts⟩)
    · exact Or.inr ⟨0, D.bump_eventually_zero_of_notMem ha hxB⟩
  · intro x hxV hbad
    exact Or.inr (bump_locally_const_on_S D ha (hSbad x hbad))

/-- Integrability of `∂̄ρ_j`-pieces: scalar field `P` vanishing near every point of `S`,
cutoff `ρ_j`, any window with a compact core outside which `P` vanishes or `ρ_j` does. -/
theorem integrable_dRhoPiece [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ) ω X]
    (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    {P : X → ℂ} (hP : Continuous P) (hPkill : ∀ p ∈ S, ∀ᶠ x' in 𝓝 p, P x' = 0)
    (j : Fin ((chartCover : Finset X).card))
    {y : X} {V : Set X} (hVopen : IsOpen V) (hVsub : V ⊆ (chartAt (H := ℂ) y).source)
    {K : Set X} (hK : IsCompact K) (hKV : K ⊆ V)
    (hkill : ∀ x ∈ V, x ∉ K → P x = 0 ∨ x ∉ tsupport (coverPoU (X := X) j)) :
    Integrable (ledgerIntegrand g₀ h P (fun x => coverPoU (X := X) j x) y V) volume := by
  refine integrable_ledgerIntegrand g₀ h hP (contMDiff_coverPoU (X := X) j)
    hVopen hVsub hK hKV ?_ ?_
  · intro x hxV hxK
    rcases hkill x hxV hxK with h0 | hts
    · exact Or.inl h0
    · exact Or.inr ⟨0, coverPoU_eventually_zero_of_notMem (X := X) j hts⟩
  · intro x hxV hbad
    exact Or.inl (hPkill x (hSbad x hbad))

/-- Integrability of the `B_j` aggregate (PoU scalar, total-bump cutoff). -/
theorem integrable_B [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    (j : Fin ((chartCover : Finset X).card)) :
    Integrable (ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump
      (coverCenter j) (chartOpen (X := X) (coverCenter j))) volume := by
  refine integrable_ledgerIntegrand g₀ h (continuous_coverRhoC (X := X) j)
    D.contMDiff_totalBump (chartOpen_isOpen _)
    (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))
    (isCompact_tsupport_coverPoU (X := X) j) (coverPoU_tsupport_subset (X := X) j) ?_ ?_
  · intro x hxV hxK
    exact Or.inl (coverRhoC_eq_zero_of_notMem (X := X) j hxK)
  · intro x hxV hbad
    exact Or.inr (totalBump_locally_const_on_S D (hSbad x hbad))

/-! #### Step 3 — the chart-local planar Stokes pairing `∫A_j + ∫B_j = 0` -/

/-- **(L5)** Per PoU chart `j`, planar Stokes for `Φ = ρ̂_j·(û−1)·f̂_j` (which is `C¹` with
compact support: `û ≡ 1` near the poles kills the singularities of `f̂`) gives, via Leibniz,

  `∫_ℂ (û−1)·∂̄ρ̂_j·f̂_j + ∫_ℂ ρ̂_j·∂̄û·f̂_j = 0`. -/
theorem integral_A_add_integral_B [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    (j : Fin ((chartCover : Finset X).card)) :
    (∫ w, ledgerIntegrand g₀ h (fun x => uC D x - 1) (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j)) w)
      + (∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump
        (coverCenter j) (chartOpen (X := X) (coverCenter j)) w) = 0 := by
  classical
  set cj := coverCenter j with hcjdef
  set φ := chartAt (H := ℂ) cj with hφdef
  set V := chartOpen (X := X) cj with hVdef
  have hVopen : IsOpen V := chartOpen_isOpen cj
  have hVsub : V ⊆ φ.source := chartOpen_subset_chartAt_source cj (coverCenter_mem j)
  have hUopen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVsub
  set q : X → ℂ := fun x => coverRhoC (X := X) j x * (uC D x - 1) with hqdef
  set Φ : ℂ → ℂ :=
    fun w => if w ∈ φ '' V then q (φ.symm w) * pairRead g₀ h cj w else 0 with hΦdef
  set Kts := tsupport (coverPoU (X := X) j) with hKtsdef
  have hKtsV : Kts ⊆ V := coverPoU_tsupport_subset (X := X) j
  have hKimg : IsCompact (φ '' Kts) :=
    (isCompact_tsupport_coverPoU (X := X) j).image_of_continuousOn
      (φ.continuousOn.mono (hKtsV.trans hVsub))
  -- `q` vanishes off the support and locally near every point of `S`
  have hq0 : ∀ x ∉ Kts, q x = 0 := fun x hx => by
    rw [hqdef]
    simp only [coverRhoC_eq_zero_of_notMem (X := X) j hx, zero_mul]
  have hq_germ_S : ∀ p ∈ S, ∀ᶠ x' in 𝓝 p, q x' = 0 := by
    intro p hp
    filter_upwards [uC_sub_one_eventually_zero g₀ h D hSbad hp] with x' hx'
    rw [hqdef]
    simp only [hx', mul_zero]
  -- `Φ ≡ 0` near every point off the (closed) compact core image
  have hΦzero_near : ∀ w : ℂ, w ∉ φ '' Kts → Φ =ᶠ[𝓝 w] fun _ => 0 := by
    intro w hw
    filter_upwards [hKimg.isClosed.isOpen_compl.mem_nhds hw] with w' hw'
    simp only [hΦdef]
    by_cases hw'V : w' ∈ φ '' V
    · rw [if_pos hw'V]
      obtain ⟨hw'_tgt, hx'_mem⟩ := symm_mem_of_mem_image hVsub hw'V
      have hx'K : φ.symm w' ∉ Kts := fun hmem => hw' ⟨_, hmem, φ.right_inv hw'_tgt⟩
      rw [hq0 _ hx'K, zero_mul]
    · rw [if_neg hw'V]
  -- Φ is C¹
  have hΦC1 : ContDiff ℝ 1 Φ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hwK : w ∈ φ '' Kts
    · have hwV : w ∈ φ '' V := Set.image_mono hKtsV hwK
      obtain ⟨hw_tgt, hx_mem⟩ := symm_mem_of_mem_image hVsub hwV
      by_cases hgood : ReadsAnalyticAt g₀ h (φ.symm w)
      · -- honest point: germ to the raw product, a C¹ product
        have hev : Φ =ᶠ[𝓝 w] fun w' => q (φ.symm w') * pairRead g₀ h cj w' := by
          filter_upwards [hUopen.mem_nhds hwV] with w' hw'
          simp only [hΦdef]
          rw [if_pos hw']
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev
        have h1 : ContDiffAt ℝ 1 (fun w' => coverRhoC (X := X) j (φ.symm w')) w :=
          (contDiffAt_complexRead (contMDiff_coverPoU (X := X) j) cj hw_tgt).of_le (by simp)
        have h2 : ContDiffAt ℝ 1 (fun w' => uC D (φ.symm w') - 1) w :=
          ((contDiffAt_complexRead D.contMDiff_totalBump cj hw_tgt).of_le (by simp)).sub
            contDiffAt_const
        have hqread : ContDiffAt ℝ 1 (fun w' => q (φ.symm w')) w := h1.mul h2
        have hf : ContDiffAt ℝ 1 (pairRead g₀ h cj) w := by
          have hzx : φ (φ.symm w) = w := φ.right_inv hw_tgt
          have hcd := (analyticAt_pairRead hgood (hVsub hx_mem)).contDiffAt (n := 1)
          rw [hzx] at hcd
          exact ContDiffAt.restrict_scalars ℝ hcd
        exact hqread.mul hf
      · -- bad point: `q ≡ 0` near it kills everything
        have hxS := hSbad _ hgood
        have hev0 : Φ =ᶠ[𝓝 w] fun _ => 0 := by
          filter_upwards [(φ.continuousAt_symm hw_tgt).eventually (hq_germ_S _ hxS)]
            with w' hw'
          simp only [hΦdef]
          by_cases hw'V : w' ∈ φ '' V
          · rw [if_pos hw'V, hw', zero_mul]
          · rw [if_neg hw'V]
        exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev0
    · exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const (hΦzero_near w hwK)
  -- compact support
  have hΦsupp : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hKimg ?_
    intro w hw
    simp only [hΦdef]
    by_cases hwV : w ∈ φ '' V
    · rw [if_pos hwV]
      obtain ⟨hw_tgt, hx_mem⟩ := symm_mem_of_mem_image hVsub hwV
      have hxK : φ.symm w ∉ Kts := fun hmem => hw ⟨_, hmem, φ.right_inv hw_tgt⟩
      rw [hq0 _ hxK, zero_mul]
    · rw [if_neg hwV]
  -- planar Stokes
  have hstokes : (∫ w, DbarDisk.dbar Φ w) = 0 := integral_dbar_eq_zero Φ hΦC1 hΦsupp
  -- a.e. Leibniz expansion into A + B
  have hae : (fun w => DbarDisk.dbar Φ w) =ᵐ[volume]
      fun w => ledgerIntegrand g₀ h (fun x => uC D x - 1)
          (fun x => coverPoU (X := X) j x) cj V w
        + ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump cj V w := by
    have hfin : ((φ '' ((S : Set X) ∩ V)) : Set ℂ).Finite :=
      (S.finite_toSet.inter_of_left V).image _
    filter_upwards [compl_mem_ae_iff.mpr (hfin.measure_zero volume)] with w hwE
    by_cases hwV : w ∈ φ '' V
    · obtain ⟨hw_tgt, hx_mem⟩ := symm_mem_of_mem_image hVsub hwV
      have hzx : φ (φ.symm w) = w := φ.right_inv hw_tgt
      have hxS : φ.symm w ∉ (S : Set X) := fun hmem =>
        hwE ⟨φ.symm w, ⟨hmem, hx_mem⟩, hzx⟩
      have hgood := readsAnalyticAt_of_notMem g₀ h hSbad _ hxS
      have hf_an : AnalyticAt ℂ (pairRead g₀ h cj) w := by
        have := analyticAt_pairRead hgood (hVsub hx_mem)
        rwa [hzx] at this
      -- the germ of Φ
      have hev : Φ =ᶠ[𝓝 w] fun w' => q (φ.symm w') * pairRead g₀ h cj w' := by
        filter_upwards [hUopen.mem_nhds hwV] with w' hw'
        simp only [hΦdef]
        rw [if_pos hw']
      -- differentiability of the reads at `w`
      have hρdiff : DifferentiableAt ℝ (fun w' => coverRhoC (X := X) j (φ.symm w')) w :=
        differentiableAt_complexRead (contMDiff_coverPoU (X := X) j) cj hw_tgt
      have hudiff : DifferentiableAt ℝ (fun w' => uC D (φ.symm w')) w :=
        differentiableAt_complexRead D.contMDiff_totalBump cj hw_tgt
      have hqdiff : DifferentiableAt ℝ (fun w' => q (φ.symm w')) w :=
        hρdiff.mul (hudiff.sub (differentiableAt_const 1))
      have hfdiffR : DifferentiableAt ℝ (pairRead g₀ h cj) w :=
        hf_an.differentiableAt.restrictScalars ℝ
      -- Leibniz, with `∂̄f = 0`
      rw [DbarDisk.dbar_congr hev,
        DbarDisk.dbar_fun_mul hqdiff hfdiffR,
        DbarDisk.dbar_eq_zero_of_differentiableAt hf_an.differentiableAt, mul_zero, zero_add]
      -- expand `∂̄(q-read)` by Leibniz
      have hqsplit : DbarDisk.dbar (fun w' => q (φ.symm w')) w
          = coverRhoC (X := X) j (φ.symm w)
              * DbarDisk.dbar (fun w' => uC D (φ.symm w')) w
            + (uC D (φ.symm w) - 1)
              * DbarDisk.dbar (fun w' => coverRhoC (X := X) j (φ.symm w')) w := by
        have hsplit := DbarDisk.dbar_fun_mul (f := fun w' => coverRhoC (X := X) j (φ.symm w'))
          (g := fun w' => uC D (φ.symm w') - 1) hρdiff (hudiff.sub (differentiableAt_const 1))
        have hsub := DbarDisk.dbar_fun_sub (f := fun w' => uC D (φ.symm w'))
          (g := fun _ => (1 : ℂ)) hudiff (differentiableAt_const 1)
        rw [DbarDisk.dbar_const] at hsub
        rw [sub_zero] at hsub
        calc DbarDisk.dbar (fun w' => q (φ.symm w')) w
            = DbarDisk.dbar (fun w' => coverRhoC (X := X) j (φ.symm w')
                * (uC D (φ.symm w') - 1)) w := rfl
          _ = coverRhoC (X := X) j (φ.symm w)
                * DbarDisk.dbar (fun w' => uC D (φ.symm w') - 1) w
              + (uC D (φ.symm w) - 1)
                * DbarDisk.dbar (fun w' => coverRhoC (X := X) j (φ.symm w')) w := hsplit
          _ = _ := by rw [hsub]
      rw [hqsplit, ledgerIntegrand, ledgerIntegrand, if_pos hwV, if_pos hwV]
      -- the `∂̄` factors in the ledger pieces are the same reads (definitional)
      rw [← hφdef]
      have e1 : (fun w' => ((D.totalBump (φ.symm w') : ℝ) : ℂ))
          = fun w' => uC D (φ.symm w') := rfl
      have e2 : (fun w' => (((coverPoU (X := X) j) (φ.symm w') : ℝ) : ℂ))
          = fun w' => coverRhoC (X := X) j (φ.symm w') := rfl
      rw [e1, e2]
      ring
    · -- off the window: both sides vanish
      have hwK : w ∉ φ '' Kts := fun hmem => hwV (Set.image_mono hKtsV hmem)
      rw [DbarDisk.dbar_congr (hΦzero_near w hwK), DbarDisk.dbar_const,
        ledgerIntegrand, ledgerIntegrand, if_neg hwV, if_neg hwV, add_zero]
  -- conclude
  have hAint : Integrable (ledgerIntegrand g₀ h (fun x => uC D x - 1)
      (fun x => coverPoU (X := X) j x) cj V) volume := by
    refine integrable_dRhoPiece g₀ h hSbad
      ((continuous_uC D).sub continuous_const)
      (fun p hp => uC_sub_one_eventually_zero g₀ h D hSbad hp) j hVopen hVsub
      (isCompact_tsupport_coverPoU (X := X) j) hKtsV ?_
    intro x hxV hxK
    exact Or.inr hxK
  have hBint : Integrable (ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump cj V)
      volume := integrable_B g₀ h D hSbad j
  rw [← integral_add hAint hBint, ← integral_congr_ae hae]
  exact hstokes

/-! #### Step 4 — the `∂̄ρ`-shuffle: `∑_j ∫ A_j = 0` -/

/-- The `(j,i)` transported piece: shrink to the chart overlap (the `ρ_i` factor vanishes off
`chartOpen c_i`), transport `c_j → c_i`, enlarge (the `ρ_j` cutoff dies off `chartOpen c_j`). -/
theorem integral_Xi_transport [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S)
    (j i : Fin ((chartCover : Finset X).card)) :
    (∫ w, ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
        (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j)) w)
      = ∫ w, ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
          (fun x => coverPoU (X := X) j x)
          (coverCenter i) (chartOpen (X := X) (coverCenter i)) w := by
  classical
  set Ω := chartOpen (X := X) (coverCenter j) ∩ chartOpen (X := X) (coverCenter i) with hΩdef
  have hΩopen : IsOpen Ω := (chartOpen_isOpen _).inter (chartOpen_isOpen _)
  have hΩj : Ω ⊆ (chartAt (H := ℂ) (coverCenter j)).source :=
    Set.inter_subset_left.trans
      (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))
  have hΩi : Ω ⊆ (chartAt (H := ℂ) (coverCenter i)).source :=
    Set.inter_subset_right.trans
      (chartOpen_subset_chartAt_source (coverCenter i) (coverCenter_mem i))
  -- shrink the `j`-side window to `Ω`
  have h1 : ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
      (fun x => coverPoU (X := X) j x) (coverCenter j) Ω
      = ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
        (fun x => coverPoU (X := X) j x) (coverCenter j)
        (chartOpen (X := X) (coverCenter j)) := by
    refine ledgerIntegrand_congr_superset g₀ h _ _ _ Set.inter_subset_left
      (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j)) ?_
    intro x hxW hxV
    have hxi : x ∉ chartOpen (X := X) (coverCenter i) := fun hmem => hxV ⟨hxW, hmem⟩
    refine Or.inl ?_
    rw [coverRhoC_eq_zero_of_notMem (X := X) i
      (fun hts => hxi (coverPoU_tsupport_subset (X := X) i hts)), zero_mul]
  -- enlarge the `i`-side window from `Ω`
  have h2 : ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
      (fun x => coverPoU (X := X) j x) (coverCenter i) Ω
      = ledgerIntegrand g₀ h (fun x => coverRhoC (X := X) i x * (uC D x - 1))
        (fun x => coverPoU (X := X) j x) (coverCenter i)
        (chartOpen (X := X) (coverCenter i)) := by
    refine ledgerIntegrand_congr_superset g₀ h _ _ _ Set.inter_subset_right
      (chartOpen_subset_chartAt_source (coverCenter i) (coverCenter_mem i)) ?_
    intro x hxW hxV
    have hxj : x ∉ chartOpen (X := X) (coverCenter j) := fun hmem => hxV ⟨hmem, hxW⟩
    refine Or.inr ⟨0, coverPoU_eventually_zero_of_notMem (X := X) j
      (fun hts => hxj (coverPoU_tsupport_subset (X := X) j hts))⟩
  rw [← h1, ← h2]
  exact integral_ledgerIntegrand_transport g₀ h _ _ (contMDiff_coverPoU (X := X) j)
    hΩopen hΩj hΩi S.finite_toSet
    (fun x _ hxS => readsAnalyticAt_of_notMem g₀ h hSbad x hxS)

/-- **(L6)** `∑_j ∫ A_j = 0`: insert `1 = ∑_i ρ_i`, transport each `(j,i)` piece to chart `i`,
and let `∑_j ∂̄ρ̂_j = ∂̄(1) = 0` kill each chart-`i` aggregate. -/
theorem sum_integral_A_eq_zero [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S) :
    ∑ j, (∫ w, ledgerIntegrand g₀ h (fun x => uC D x - 1)
        (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j)) w) = 0 := by
  classical
  have hPcont : ∀ i : Fin ((chartCover : Finset X).card),
      Continuous (fun x => coverRhoC (X := X) i x * (uC D x - 1)) := fun i =>
    (continuous_coverRhoC (X := X) i).mul ((continuous_uC D).sub continuous_const)
  have hPkill : ∀ (i : Fin ((chartCover : Finset X).card)), ∀ p ∈ S,
      ∀ᶠ x' in 𝓝 p, coverRhoC (X := X) i x' * (uC D x' - 1) = 0 := by
    intro i p hp
    filter_upwards [uC_sub_one_eventually_zero g₀ h D hSbad hp] with x' hx'
    rw [hx', mul_zero]
  -- the (j,i)-piece integrability in chart `j` (core = `tsupport ρ_j`)
  have hintJ : ∀ j i : Fin ((chartCover : Finset X).card),
      Integrable (ledgerIntegrand g₀ h
        (fun x => coverRhoC (X := X) i x * (uC D x - 1))
        (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j))) volume := by
    intro j i
    exact integrable_dRhoPiece g₀ h hSbad (hPcont i) (hPkill i) j (chartOpen_isOpen _)
      (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))
      (isCompact_tsupport_coverPoU (X := X) j) (coverPoU_tsupport_subset (X := X) j)
      (fun x _ hxK => Or.inr hxK)
  -- the (j,i)-piece integrability in chart `i` (core = `tsupport ρ_i`)
  have hintI : ∀ j i : Fin ((chartCover : Finset X).card),
      Integrable (ledgerIntegrand g₀ h
        (fun x => coverRhoC (X := X) i x * (uC D x - 1))
        (fun x => coverPoU (X := X) j x)
        (coverCenter i) (chartOpen (X := X) (coverCenter i))) volume := by
    intro j i
    exact integrable_dRhoPiece g₀ h hSbad (hPcont i) (hPkill i) j (chartOpen_isOpen _)
      (chartOpen_subset_chartAt_source (coverCenter i) (coverCenter_mem i))
      (isCompact_tsupport_coverPoU (X := X) i) (coverPoU_tsupport_subset (X := X) i)
      (fun x _ hxK =>
        Or.inl (by rw [coverRhoC_eq_zero_of_notMem (X := X) i hxK, zero_mul]))
  -- expand each `A_j` into the `(j,i)`-pieces (insert `∑_i ρ_i = 1`)
  have hexpand : ∀ j : Fin ((chartCover : Finset X).card),
      ledgerIntegrand g₀ h (fun x => uC D x - 1) (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j))
      = fun w => ∑ i, ledgerIntegrand g₀ h
          (fun x => coverRhoC (X := X) i x * (uC D x - 1))
          (fun x => coverPoU (X := X) j x)
          (coverCenter j) (chartOpen (X := X) (coverCenter j)) w := by
    intro j
    funext w
    rw [ledgerIntegrand_sum_P]
    congr 1
    funext x
    rw [← Finset.sum_mul, sum_coverRhoC_eq_one, one_mul]
  calc ∑ j, (∫ w, ledgerIntegrand g₀ h (fun x => uC D x - 1)
        (fun x => coverPoU (X := X) j x)
        (coverCenter j) (chartOpen (X := X) (coverCenter j)) w)
      = ∑ j, ∑ i, ∫ w, ledgerIntegrand g₀ h
          (fun x => coverRhoC (X := X) i x * (uC D x - 1))
          (fun x => coverPoU (X := X) j x)
          (coverCenter j) (chartOpen (X := X) (coverCenter j)) w := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexpand j]
        exact integral_finsetSum _ (fun i _ => hintJ j i)
    _ = ∑ j, ∑ i, ∫ w, ledgerIntegrand g₀ h
          (fun x => coverRhoC (X := X) i x * (uC D x - 1))
          (fun x => coverPoU (X := X) j x)
          (coverCenter i) (chartOpen (X := X) (coverCenter i)) w :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
          integral_Xi_transport g₀ h D hSbad j i
    _ = ∑ i, ∑ j, ∫ w, ledgerIntegrand g₀ h
          (fun x => coverRhoC (X := X) i x * (uC D x - 1))
          (fun x => coverPoU (X := X) j x)
          (coverCenter i) (chartOpen (X := X) (coverCenter i)) w := Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [← integral_finsetSum _ (fun j _ => hintI j i)]
        have hpt : (fun w => ∑ j, ledgerIntegrand g₀ h
            (fun x => coverRhoC (X := X) i x * (uC D x - 1))
            (fun x => coverPoU (X := X) j x)
            (coverCenter i) (chartOpen (X := X) (coverCenter i)) w)
            = fun _ => (0 : ℂ) := by
          funext w
          rw [sum_ledgerIntegrand Finset.univ (fun j => fun x => coverPoU (X := X) j x)
            (fun j _ => contMDiff_coverPoU (X := X) j) g₀ h _ (coverCenter i)
            (chartOpen_subset_chartAt_source (coverCenter i) (coverCenter_mem i)) w]
          have hone : (fun x => ∑ j, coverPoU (X := X) j x) = fun _ : X => (1 : ℝ) := by
            funext x
            exact sum_coverPoU_eq_one x
          rw [hone]
          exact congrFun (ledgerIntegrand_const_v g₀ h _ 1 _ _) w
        rw [hpt, integral_zero]

/-! #### Step 5 — the assembled `S`-sum -/

include D in
/-- **The residue ledger assembled**: over the enlarged pole set `S` (containing the analytic
bad locus), `∑_{a ∈ S} pairFormResidue g₀ h a = 0`. -/
theorem residueSum_pairForm_eq_zero_S [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [IsManifold 𝓘(ℂ) ω X]
    (hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S) :
    ∑ a ∈ S, pairFormResidue g₀ h a = 0 := by
  classical
  have hπ : (-(π : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  -- the per-pole chain: `−π·Res_a = ∑_j ∫ (a,j)-piece` (in the cover charts, full windows)
  have hchain : ∀ a ∈ S, -(π : ℂ) * pairFormResidue g₀ h a
      = ∑ j, ∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a)
          (coverCenter j) (chartOpen (X := X) (coverCenter j)) w := by
    intro a ha
    rw [← integral_psi_eq g₀ h D hSbad ha]
    have hKV1 : ∀ j : Fin ((chartCover : Finset X).card),
        D.poleBall a ∩ tsupport (coverPoU (X := X) j) ⊆ poleWindow (X := X) a j :=
      fun j => Set.inter_subset_inter (D.poleBall_subset_source ha)
        (coverPoU_tsupport_subset (X := X) j)
    -- insert `1 = ∑_j ρ_j` under the integral
    have hins : (fun z : ℂ => Complex.ofReal (deriv (D.η a)
          (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
        * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z)
        = fun z => ∑ j, coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
            * (Complex.ofReal (deriv (D.η a)
                (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
              * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z) := by
      funext z
      rw [← Finset.sum_mul, sum_coverRhoC_eq_one, one_mul]
    calc ∫ z : ℂ, (Complex.ofReal (deriv (D.η a)
            (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
          * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z)
        = ∫ z : ℂ, ∑ j, coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
            * (Complex.ofReal (deriv (D.η a)
                (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
              * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z) := by rw [← hins]
      _ = ∑ j, ∫ z : ℂ, coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
            * (Complex.ofReal (deriv (D.η a)
                (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
              * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z) := by
          refine integral_finsetSum _ (fun j _ => ?_)
          rw [show (fun z : ℂ => coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
              * (Complex.ofReal (deriv (D.η a)
                  (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
                * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z))
            = ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a) a
                (poleWindow a j) from rho_psi_eq_ledger g₀ h D ha j]
          exact integrable_polePiece g₀ h D hSbad ha j (poleWindow_isOpen a j)
            (poleWindow_subset_pole a j) (hKV1 j)
      _ = ∑ j, ∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a)
            (coverCenter j) (chartOpen (X := X) (coverCenter j)) w := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show (fun z : ℂ => coverRhoC (X := X) j ((chartAt (H := ℂ) a).symm z)
              * (Complex.ofReal (deriv (D.η a)
                  (Complex.normSq (z - (chartAt (H := ℂ) a) a)))
                * (z - (chartAt (H := ℂ) a) a) * pairRead g₀ h a z))
            = ledgerIntegrand g₀ h (coverRhoC (X := X) j) (D.bump a) a
                (poleWindow a j) from rho_psi_eq_ledger g₀ h D ha j]
          -- transport to the cover chart, then enlarge the window
          rw [integral_ledgerIntegrand_transport g₀ h _ _ (D.contMDiff_bump ha)
            (poleWindow_isOpen a j) (poleWindow_subset_pole a j)
            (poleWindow_subset_cover a j) S.finite_toSet
            (fun x _ hxS => readsAnalyticAt_of_notMem g₀ h hSbad x hxS)]
          rw [ledgerIntegrand_congr_superset g₀ h (coverRhoC (X := X) j) (D.bump a)
            (coverCenter j)
            (show poleWindow (X := X) a j ⊆ chartOpen (X := X) (coverCenter j) from
              Set.inter_subset_right)
            (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j)) ?_]
          intro x hxW hxV
          have hxa : x ∉ (chartAt (H := ℂ) a).source := fun hmem => hxV ⟨hmem, hxW⟩
          have hxB : x ∉ D.poleBall a := fun hmem =>
            hxa (D.poleBall_subset_source ha hmem)
          exact Or.inr ⟨0, D.bump_eventually_zero_of_notMem ha hxB⟩
  -- sum over the poles, swap with the cover sum, and aggregate the bumps
  have hsum1 : -(π : ℂ) * ∑ a ∈ S, pairFormResidue g₀ h a
      = ∑ j, ∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump
          (coverCenter j) (chartOpen (X := X) (coverCenter j)) w := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hchain, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_finsetSum _ (fun a ha => integrable_polePiece g₀ h D hSbad ha j
      (chartOpen_isOpen _)
      (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))
      (Set.inter_subset_right.trans (coverPoU_tsupport_subset (X := X) j)))]
    congr 1
    funext w
    rw [sum_ledgerIntegrand S (fun a => D.bump a) (fun a ha => D.contMDiff_bump ha) g₀ h _
      (coverCenter j)
      (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j)) w]
    rfl
  -- the Stokes pairing turns the `B`-sum into the (vanishing) `A`-sum
  have hABsum : ∑ j, ∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump
      (coverCenter j) (chartOpen (X := X) (coverCenter j)) w = 0 := by
    have hBA : ∀ j : Fin ((chartCover : Finset X).card),
        (∫ w, ledgerIntegrand g₀ h (coverRhoC (X := X) j) D.totalBump
          (coverCenter j) (chartOpen (X := X) (coverCenter j)) w)
        = -(∫ w, ledgerIntegrand g₀ h (fun x => uC D x - 1)
            (fun x => coverPoU (X := X) j x)
            (coverCenter j) (chartOpen (X := X) (coverCenter j)) w) := by
      intro j
      have := integral_A_add_integral_B g₀ h D hSbad j
      linear_combination this
    rw [Finset.sum_congr rfl fun j _ => hBA j, Finset.sum_neg_distrib,
      sum_integral_A_eq_zero g₀ h D hSbad, neg_zero]
  rw [hABsum] at hsum1
  rcases mul_eq_zero.mp hsum1 with hcontra | hgoal
  · exact absurd hcontra hπ
  · exact hgoal

end Assembly

end Jacobians.Dolbeault.StokesResidue

/-! ## The headline theorems (genus-uniform; same shapes as the genus ≥ 1 versions) -/

namespace Jacobians.Dolbeault

open Jacobians Jacobians.Dolbeault.StokesResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **THE PAIR-FORM RESIDUE THEOREM, ALL GENERA** (Forster GTM 81, 10.21): the total residue of
a meromorphic pair-form `h·dg₀` over any finite set containing its poles vanishes,

  `∑ a ∈ poles, pairFormResidue g₀ h a = 0`,

provided the pair integrand is honestly `AnalyticAt` at every chart centre off `poles`.
NO genus hypothesis: the planar-Stokes ledger (single-pole annulus atoms + chart transport +
partition of unity + Forster 10.20) replaces the ω₀-factorization of the genus ≥ 1 proof. -/
theorem residueSum_pairForm_eq_zero_unconditional
    (g₀ h : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x, x ∉ poles → AnalyticAt ℂ
      (fun z => h.toFun ((chartAt (H := ℂ) x).symm z)
         * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z)
      ((chartAt (H := ℂ) x) x)) :
    ∑ a ∈ poles, pairFormResidue g₀ h a = 0 := by
  classical
  set S : Finset X := poles ∪ (finite_not_readsAnalyticAt g₀ h).toFinset with hSdef
  have hSbad : ∀ x : X, ¬ ReadsAnalyticAt g₀ h x → x ∈ S := fun x hx =>
    Finset.mem_union_right _ ((finite_not_readsAnalyticAt g₀ h).mem_toFinset.mpr hx)
  obtain ⟨D⟩ := exists_poleBumpData S
  have hSsum := residueSum_pairForm_eq_zero_S g₀ h D hSbad
  have hsub : poles ⊆ S := Finset.subset_union_left
  rw [← Finset.sum_sdiff hsub] at hSsum
  have hextra : ∑ a ∈ S \ poles, pairFormResidue g₀ h a = 0 :=
    Finset.sum_eq_zero fun a ha =>
      pairFormResidue_eq_zero_of_analyticAt g₀ h a (hpoles a (Finset.mem_sdiff.mp ha).2)
  rw [hextra, zero_add] at hSsum
  exact hSsum

/-- **Convenience wrapper for product numerators, all genera** (the downstream
Mittag–Leffler/Serre-pairing shape `∑Res(f·h·dg₀) = 0`): the main theorem at the pair
`(g₀, f·h)`, with the analyticity hypothesis stated on the unfolded product integrand. -/
theorem residueSum_pairForm_mul_eq_zero_unconditional
    (g₀ f h : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x, x ∉ poles → AnalyticAt ℂ
      (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) * h.toFun ((chartAt (H := ℂ) x).symm z)
         * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z)
      ((chartAt (H := ℂ) x) x)) :
    ∑ a ∈ poles, pairFormResidue g₀ (f * h) a = 0 := by
  refine residueSum_pairForm_eq_zero_unconditional g₀ (f * h) poles (fun x hx => ?_)
  have hfh := hpoles x hx
  simpa only [MeromorphicFunction.mul_toFun, Pi.mul_apply] using hfh

end Jacobians.Dolbeault
