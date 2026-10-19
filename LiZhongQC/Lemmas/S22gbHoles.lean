import LiZhongQC.Lemmas.S22gbGeom

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetHoles

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

theorem s22gb_W_continuousAt {q : S → ℂ → ℂ} {α : S → ℂ → ℂ → ℝ}
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (ρ : S → ℝ) (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ) (x : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hm : MeromorphicAt (q x) z)
    (ho : meromorphicOrderAt (q x) z = 0) :
    ContinuousAt (fun w => fderiv ℝ (fun w' => ρ ((chartAt ℂ x).symm w')) w 1 * α x w I -
      fderiv ℝ (fun w' => ρ ((chartAt ℂ x).symm w')) w I * α x w 1) z := by
  have hc1 : ContDiffAt ℝ 1 (fun w' => ρ ((chartAt ℂ x).symm w')) z :=
    (s22gb_rho_contDiffAt ρ hρ x hz).of_le (by exact_mod_cast le_top)
  have h1 : ContinuousAt (fderiv ℝ (fun w' => ρ ((chartAt ℂ x).symm w'))) z :=
    (hc1.fderiv_right (m := 0) (by simp)).continuousAt
  have h2 := (hsm x z hz hm ho I).continuousAt
  have h3 := (hsm x z hz hm ho 1).continuousAt
  exact ((h1.clm_apply continuousAt_const).mul h2).sub ((h1.clm_apply continuousAt_const).mul h3)

set_option maxHeartbeats 4000000 in
/-- (P2b) Global Stokes with holes (the multi-chart PoU construction). `Z` is a finite set containing
all zeros and poles of the differential `q`; `A r` is the surface minus the closed chart squares of
half-side `r` around the points of `Z`. For small `r` its hyperbolic area is finite and equals minus the
sum of the boundary integrals of the gauge `α` over those squares (positive orientation). -/
theorem s22gb_area_holes {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {F : Set ℂ} (hFH : IsFundamentalDomainH Γ F)
    {q : S → ℂ → ℂ} (hq : IsDiffFamily 1 0 q)
    (hmer : ∀ x, MeromorphicAt (q x) (chartAt ℂ x x))
    (hord : ∀ x, meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤)
    (Z : Finset S) (hZ : ∀ x, x ∉ Z → meromorphicOrderAt (q x) (chartAt ℂ x x) = 0)
    (α : S → ℂ → ℂ → ℝ)
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
        meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      s22gm_surfaceArea p F
          (Set.univ \ ⋃ x ∈ Z, (chartAt ℂ x).symm ''
            wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I))) ≠ ⊤ ∧
      (s22gm_surfaceArea p F
          (Set.univ \ ⋃ x ∈ Z, (chartAt ℂ x).symm ''
            wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)))).toReal =
        -∑ x ∈ Z, s22cd_rectBoundary (α x)
            (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) := by
  classical
  have _ho := hord
  -- regular points
  have hreg : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∉ Z →
      MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0 := by
    intro x z hz hnz
    obtain ⟨hm, ho⟩ := s22gb_order_transport hq hmer x hz
    exact ⟨hm, by rw [ho]; exact hZ _ hnz⟩
  -- lift discs and separation of the points of `Z`
  choose ε hε ψ0 hball hψ0 using fun y => s22gb_lift_ball hp y
  obtain ⟨U, hU, hUdisj⟩ := (Z.finite_toSet).t2_separation
  have hRex : ∀ x, ∃ R : ℝ, 0 < R ∧ ∀ w ∈ Metric.ball (chartAt ℂ x x) R,
      w ∈ Metric.ball (chartAt ℂ x x) (ε x) ∧ (chartAt ℂ x).symm w ∈ U x := by
    intro x
    have hct : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ x x), (chartAt ℂ x).symm w ∈ U x := by
      have := ((chartAt ℂ x).continuousAt_symm hct).preimage_mem_nhds
        ((hU x).2.mem_nhds (by rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact (hU x).1))
      exact this
    have h2 : ∀ᶠ w in 𝓝 (chartAt ℂ x x), w ∈ Metric.ball (chartAt ℂ x x) (ε x) :=
      Metric.ball_mem_nhds _ (hε x)
    obtain ⟨R, hR, hball'⟩ := Metric.eventually_nhds_iff_ball.1 (h2.and h1)
    exact ⟨R, hR, hball'⟩
  choose R hR0 hR using hRex
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Z, m ≤ R x := by
    by_cases hne : Z.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := Z.exists_min_image R hne
      exact ⟨R x0, hR0 x0, hmin⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  refine ⟨m / 8, by positivity, fun r hr0 hr => ?_⟩
  have hm' : ∀ x ∈ Z, 4 * r < R x := fun x hx => by have := hm x hx; linarith
  -- squares of half-side `2r` stay inside the lift disc and inside the separating neighbourhood
  have hSqb : ∀ x ∈ Z, wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) ⊆ Metric.ball (chartAt ℂ x x) (R x) :=
    fun x hx => s22gb_sq_subset_ball (by positivity) (by have := hm' x hx; linarith)
  have hSqt : ∀ x ∈ Z, wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) ⊆ (chartAt ℂ x).target :=
    fun x hx z hz => hball x (hR x z (hSqb x hx hz)).1
  have hSqU : ∀ x ∈ Z, ∀ z ∈ wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)), (chartAt ℂ x).symm z ∈ U x :=
    fun x hx z hz => (hR x z (hSqb x hx hz)).2
  have hsmall : ∀ x : S, wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) ⊆
      wv_rectO (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
        (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) := fun x => s22gb_sq_subset_osq hr0
  have hosq : ∀ x : S, wv_rectO (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) ⊆ wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) := fun x => s22gb_osq_subset_sq (by positivity)
  -- the holes
  set B : S → Set S := fun x => (chartAt ℂ x).symm ''
    wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) with hB
  set Bg : S → Set S := fun x => (chartAt ℂ x).symm ''
    wv_rectO (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) with hBg
  have hBcomp : ∀ x ∈ Z, IsCompact (B x) := fun x hx =>
    (wv_isCompact_rectK _ _).image_of_continuousOn
      ((chartAt ℂ x).continuousOn_symm.mono
        (fun z hz => hSqt x hx (hosq x (hsmall x hz))))
  have hAo : IsOpen (univ \ ⋃ x ∈ Z, B x) := by
    rw [diff_eq, univ_inter]
    exact (isClosed_biUnion_finset (fun x hx => (hBcomp x hx).isClosed)).isOpen_compl
  have hBgo : ∀ x ∈ Z, IsOpen (Bg x) := fun x hx =>
    (chartAt ℂ x).symm.isOpen_image_of_subset_source (s22gb_rectO_isOpen _ _)
      (fun z hz => hSqt x hx (hosq x hz))
  have hBBg : ∀ x, B x ⊆ Bg x := fun x => image_mono (hsmall x)
  have hxB : ∀ x, x ∈ B x := fun x => by
    refine ⟨chartAt ℂ x x, ?_, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
    exact s22gb_osq_subset_sq hr0.le (s22gb_center_mem_osq _ hr0)
  have hBU : ∀ x ∈ Z, Bg x ⊆ U x := by
    rintro x hx _ ⟨z, hz, rfl⟩
    exact hSqU x hx z (hosq x hz)
  have hBgdisj : ∀ x ∈ Z, ∀ x' ∈ Z, x ≠ x' → Disjoint (Bg x) (Bg x') := fun x hx x' hx' hne =>
    (hUdisj hx hx' hne).mono (hBU x hx) (hBU x' hx')
  -- the complement of the big sheets is compact and contained in `A`
  set A : Set S := univ \ ⋃ x ∈ Z, B x with hA
  set C : Set S := univ \ ⋃ x ∈ Z, Bg x with hC
  have hCc : IsCompact C := by
    refine IsClosed.isCompact ?_
    rw [hC, diff_eq, univ_inter]
    exact (isOpen_biUnion (fun x hx => hBgo x hx)).isClosed_compl
  have hCA : ∀ y ∈ C, y ∈ A := by
    intro y hy
    refine ⟨mem_univ _, fun h => ?_⟩
    simp only [mem_iUnion] at h
    obtain ⟨x, hx, hyx⟩ := h
    exact hy.2 (mem_iUnion₂.2 ⟨x, hx, hBBg x hyx⟩)
  -- small squares around the points of `C`
  have hδ : ∀ y : S, ∃ δ : ℝ, 0 < δ ∧ (y ∈ C → 2 * δ < ε y ∧
      ∀ w ∈ wv_rectK (chartAt ℂ y y - (δ : ℂ) * (1 + I)) (chartAt ℂ y y + (δ : ℂ) * (1 + I)),
        (chartAt ℂ y).symm w ∈ A) := by
    intro y
    by_cases hyC : y ∈ C
    · have hct : chartAt ℂ y y ∈ (chartAt ℂ y).target :=
        (chartAt ℂ y).map_source (mem_chart_source ℂ y)
      have hev : ∀ᶠ w in 𝓝 (chartAt ℂ y y), (chartAt ℂ y).symm w ∈ A := by
        have h1 : A ∈ 𝓝 ((chartAt ℂ y).symm (chartAt ℂ y y)) := by
          rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
          exact hAo.mem_nhds (hCA y hyC)
        exact ((chartAt ℂ y).continuousAt_symm hct).preimage_mem_nhds h1
      obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.1 hev
      have hmin : 0 < min (ε y) ρ := lt_min (hε y) hρ
      refine ⟨min (ε y) ρ / 4, by positivity, fun _ => ⟨?_, fun w hw => ?_⟩⟩
      · linarith [min_le_left (ε y) ρ]
      · exact hρb w (s22gb_sq_subset_ball (δ := min (ε y) ρ / 4) (by positivity)
          (by linarith [min_le_right (ε y) ρ]) hw)
    · exact ⟨1, one_pos, fun h => absurd h hyC⟩
  choose δ hδ0 hδy using hδ
  have hVn : ∀ y ∈ C, (chartAt ℂ y).symm '' wv_rectO (chartAt ℂ y y - (δ y : ℂ) * (1 + I))
      (chartAt ℂ y y + (δ y : ℂ) * (1 + I)) ∈ 𝓝 y := by
    intro y hy
    have hsq := hδy y hy
    have hot : wv_rectO (chartAt ℂ y y - (δ y : ℂ) * (1 + I))
        (chartAt ℂ y y + (δ y : ℂ) * (1 + I)) ⊆ (chartAt ℂ y).target := fun z hz =>
      hball y (s22gb_sq_subset_ball (δ := δ y) (hδ0 y).le hsq.1
        (s22gb_osq_subset_sq (hδ0 y).le hz))
    have hopen := (chartAt ℂ y).symm.isOpen_image_of_subset_source (s22gb_rectO_isOpen _ _) hot
    exact hopen.mem_nhds ⟨chartAt ℂ y y, s22gb_center_mem_osq _ (hδ0 y),
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)⟩
  obtain ⟨t, htC, hCt⟩ := hCc.elim_nhds_subcover (fun y => (chartAt ℂ y).symm ''
    wv_rectO (chartAt ℂ y y - (δ y : ℂ) * (1 + I)) (chartAt ℂ y y + (δ y : ℂ) * (1 + I))) hVn
  -- the pieces
  let ι := ↥Z ⊕ ↥t
  let xs : ι → S := Sum.elim (fun x => (x : S)) (fun y => (y : S))
  let δ' : ι → ℝ := Sum.elim (fun _ => 2 * r) (fun y => δ y)
  let Dom : ι → Set ℂ := fun i => wv_rectO (chartAt ℂ (xs i) (xs i) - (δ' i : ℂ) * (1 + I))
    (chartAt ℂ (xs i) (xs i) + (δ' i : ℂ) * (1 + I))
  have hδ'0 : ∀ i, 0 < δ' i := by
    rintro (x | y)
    · exact mul_pos two_pos hr0
    · exact hδ0 y
  have hsqε : ∀ i, wv_rectK (chartAt ℂ (xs i) (xs i) - (δ' i : ℂ) * (1 + I))
      (chartAt ℂ (xs i) (xs i) + (δ' i : ℂ) * (1 + I)) ⊆
        Metric.ball (chartAt ℂ (xs i) (xs i)) (ε (xs i)) := by
    rintro (x | y)
    · intro z hz
      exact (hR x z (hSqb x x.2 hz)).1
    · exact s22gb_sq_subset_ball (hδ0 y).le (hδy y (htC y y.2)).1
  have hopenU : ∀ i, IsOpen ((chartAt ℂ (xs i)).symm '' Dom i) := fun i =>
    (chartAt ℂ (xs i)).symm.isOpen_image_of_subset_source (s22gb_rectO_isOpen _ _)
      (fun z hz => hball (xs i) (hsqε i (s22gb_osq_subset_sq (hδ'0 i).le hz)))
  have hcoverU : (univ : Set S) ⊆ ⋃ i, (chartAt ℂ (xs i)).symm '' Dom i := by
    intro y _
    by_cases hyC : y ∈ C
    · have := hCt hyC
      simp only [mem_iUnion] at this
      obtain ⟨y', hy't, hmem⟩ := this
      exact mem_iUnion.2 ⟨Sum.inr ⟨y', hy't⟩, hmem⟩
    · have : y ∈ ⋃ x ∈ Z, Bg x := by
        by_contra hn
        exact hyC ⟨mem_univ _, hn⟩
      simp only [mem_iUnion] at this
      obtain ⟨x, hx, hmem⟩ := this
      exact mem_iUnion.2 ⟨Sum.inl ⟨x, hx⟩, hmem⟩
  obtain ⟨ρ, hρsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i => (chartAt ℂ (xs i)).symm '' Dom i) hopenU hcoverU
  have hρs : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (ρ i) := fun i => (ρ i).contMDiff
  have hρ0 : ∀ i y, 0 ≤ ρ i y := fun i y => ρ.nonneg i y
  have hρsum : ∀ y, ∑ i, ρ i y = 1 := fun y => by
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ y)
  have hZA : ∀ y ∈ A, y ∉ Z := by
    intro y hy hyZ
    exact hy.2 (mem_iUnion₂.2 ⟨y, hyZ, hxB y⟩)
  have hDt : ∀ i, Dom i ⊆ (chartAt ℂ (xs i)).target := fun i z hz =>
    hball (xs i) (hsqε i (s22gb_osq_subset_sq (hδ'0 i).le hz))
  have hψ : ∀ i, ∀ z ∈ wv_rectK (chartAt ℂ (xs i) (xs i) - (δ' i : ℂ) * (1 + I))
      (chartAt ℂ (xs i) (xs i) + (δ' i : ℂ) * (1 + I)), z ∈ (chartAt ℂ (xs i)).target ∧
      AnalyticAt ℂ (ψ0 (xs i)) z ∧ deriv (ψ0 (xs i)) z ≠ 0 ∧ ψ0 (xs i) z ∈ upperHalf ∧
      (fun w => s22gm_projectionExtension p (ψ0 (xs i) w)) =ᶠ[𝓝 z]
        fun w => (chartAt ℂ (xs i)).symm w := fun i z hz =>
    ⟨hball (xs i) (hsqε i hz), hψ0 (xs i) z (hsqε i hz)⟩
  have hDo : ∀ i, IsOpen (Dom i) := fun i => s22gb_rectO_isOpen _ _
  have hDsub : ∀ i, Dom i ⊆ wv_rectK (chartAt ℂ (xs i) (xs i) - (δ' i : ℂ) * (1 + I))
      (chartAt ℂ (xs i) (xs i) + (δ' i : ℂ) * (1 + I)) := fun i => s22gb_osq_subset_sq (hδ'0 i).le
  have hDbd : ∀ i, ∃ C : ℝ, ∀ z ∈ Dom i, s22gc_areaDensity (ψ0 (xs i)) z ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (wv_isCompact_rectK _ _).exists_bound_of_continuousOn
      (f := s22gc_areaDensity (ψ0 (xs i)))
      (fun z hz => (s22gc_areaDensity_continuousAt (hψ i z hz).2.1
        (show 0 < (ψ0 (xs i) z).im from (hψ i z hz).2.2.2.1)).continuousWithinAt)
    exact ⟨C, fun z hz => (le_abs_self _).trans (by simpa using hC z (hDsub i hz))⟩
  have hDvol : ∀ i, volume (Dom i) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_mono (hDsub i)) (wv_isCompact_rectK _ _).measure_lt_top
  have hAreg : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ A →
      MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0 := fun x z hz hzA =>
    hreg x z hz (hZA _ hzA)
  -- compact regular regions carrying each piece
  have hWreg : ∀ i, ∃ T : Set ℂ, IsCompact T ∧
      (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A) ⊆ T ∧
      ∀ z ∈ T, z ∈ (chartAt ℂ (xs i)).target ∧ (chartAt ℂ (xs i)).symm z ∉ Z := by
    rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · -- the annulus around the hole
      refine ⟨wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
          (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) \
        wv_rectO (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)),
        (wv_isCompact_rectK _ _).diff (s22gb_rectO_isOpen _ _), ?_, ?_⟩
      · intro z hz
        refine ⟨hosq x hz.1, fun hO => ?_⟩
        have hzA := hz.2
        exact hzA.2 (mem_iUnion₂.2 ⟨x, hx, z, s22gb_osq_subset_sq hr0.le hO, rfl⟩)
      · intro z hz
        refine ⟨hSqt x hx hz.1, fun hzZ => ?_⟩
        by_cases hxx : (chartAt ℂ x).symm z = x
        · apply hz.2
          have : z = chartAt ℂ x x := by
            have h := (chartAt ℂ x).right_inv (hSqt x hx hz.1)
            rw [hxx] at h
            exact h.symm
          rw [this]
          exact s22gb_center_mem_osq _ hr0
        · have h1 := hSqU x hx z hz.1
          exact (Set.disjoint_left.1 (hUdisj (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hzZ)
            (fun h => hxx h.symm)) h1) (hU _).1
    · refine ⟨wv_rectK (chartAt ℂ y y - (δ y : ℂ) * (1 + I)) (chartAt ℂ y y + (δ y : ℂ) * (1 + I)),
        wv_isCompact_rectK _ _, fun z hz => hDsub (Sum.inr ⟨y, hy⟩) hz.1, fun z hz => ?_⟩
      exact ⟨hball y (hsqε (Sum.inr ⟨y, hy⟩) hz), hZA _ ((hδy y (htC y hy)).2 z hz)⟩
  -- the wedge terms
  set W : ι → ℂ → ℝ := fun i z => fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z 1 *
      α (xs i) z I - fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z I * α (xs i) z 1
    with hWdef
  have hWcT : ∀ i, ∀ T : Set ℂ, (∀ z ∈ T, z ∈ (chartAt ℂ (xs i)).target ∧
      (chartAt ℂ (xs i)).symm z ∉ Z) → ContinuousOn (W i) T := fun i T hT z hz =>
    (s22gb_W_continuousAt hsm (ρ i) (hρs i) (xs i) (hT z hz).1
      (hreg _ _ (hT z hz).1 (hT z hz).2).1 (hreg _ _ (hT z hz).1 (hT z hz).2).2).continuousWithinAt
  have hWc : ∀ i, ContinuousOn (W i) (Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A) := fun i => by
    obtain ⟨T, hTc, hsub, hTr⟩ := hWreg i
    exact (hWcT i T hTr).mono hsub
  have hWbd : ∀ i, ∃ C : ℝ, ∀ z ∈ Dom i, (chartAt ℂ (xs i)).symm z ∈ A → |W i z| ≤ C := fun i => by
    obtain ⟨T, hTc, hsub, hTr⟩ := hWreg i
    obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn (hWcT i T hTr)
    exact ⟨C, fun z hz hzA => by simpa using hC z (hsub ⟨hz, hzA⟩)⟩
  have hρvan : ∀ i, ∀ z ∈ (chartAt ℂ (xs i)).target, z ∉ Dom i → ρ i ((chartAt ℂ (xs i)).symm z) = 0 := by
    intro i z hzt hzD
    refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
    obtain ⟨z', hz', hz'z⟩ := hρsub i h
    have := (chartAt ℂ (xs i)).symm.injOn (hDt i hz') hzt hz'z
    exact hzD (this ▸ hz')
  have hregInl : ∀ x ∈ Z, ∀ z ∈ wv_rectK (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
      (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) \
        wv_rectO (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)),
      (chartAt ℂ x).symm z ∉ Z := by
    intro x hx z hz hzZ
    by_cases hxx : (chartAt ℂ x).symm z = x
    · apply hz.2
      have h := (chartAt ℂ x).right_inv (hSqt x hx hz.1)
      rw [hxx] at h
      have : z = chartAt ℂ x x := h.symm
      rw [this]
      exact s22gb_center_mem_osq _ hr0
    · have h1 := hSqU x hx z hz.1
      exact (Set.disjoint_left.1 (hUdisj (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hzZ)
        (fun h => hxx h.symm)) h1) (hU _).1
  set s : ι → ℝ := Sum.elim (fun x : ↥Z => -s22cd_rectBoundary (α (x : S))
      (chartAt ℂ (x : S) (x : S) - (r : ℂ) * (1 + I))
      (chartAt ℂ (x : S) (x : S) + (r : ℂ) * (1 + I))) (fun _ => 0)
    with hs
  have hstokes : ∀ i, (∫ z in Dom i ∩ (chartAt ℂ (xs i)).symm ⁻¹' A,
      (ρ i ((chartAt ℂ (xs i)).symm z) * s22gc_areaDensity (ψ0 (xs i)) z + W i z)) = s i := by
    rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · obtain ⟨a1, a2, a3, a4⟩ := s22gb_sq_corners (c := chartAt ℂ x x) (δ := 2 * r)
      obtain ⟨b1, b2, b3, b4⟩ := s22gb_sq_corners (c := chartAt ℂ x x) (δ := r)
      have hset : Dom (Sum.inl ⟨x, hx⟩) ∩ (chartAt ℂ x).symm ⁻¹' A =
          wv_rectO (chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
            (chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I)) \
          wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)) := by
        ext z
        constructor
        · rintro ⟨hzD, hzA⟩
          refine ⟨hzD, fun hzK => hzA.2 (mem_iUnion₂.2 ⟨x, hx, z, hzK, rfl⟩)⟩
        · rintro ⟨hzD, hzK⟩
          refine ⟨hzD, mem_univ _, fun hzB => ?_⟩
          obtain ⟨x', hx', w, hw, hwz⟩ := mem_iUnion₂.1 hzB
          have hzt : z ∈ (chartAt ℂ x).target := hDt (Sum.inl ⟨x, hx⟩) hzD
          by_cases hxx : x' = x
          · subst hxx
            have hwt : w ∈ (chartAt ℂ x').target := hSqt x' hx' (hosq x' (hsmall x' hw))
            exact hzK (by rw [← (chartAt ℂ x').symm.injOn hwt hzt hwz]; exact hw)
          · have hA1 : (chartAt ℂ x).symm z ∈ Bg x := ⟨z, hzD, rfl⟩
            have hA2 : (chartAt ℂ x).symm z ∈ Bg x' := hBBg x' ⟨w, hw, hwz⟩
            exact Set.disjoint_left.1 (hBgdisj x hx x' hx' (fun h => hxx h.symm)) hA1 hA2
      show (∫ z in Dom (Sum.inl ⟨x, hx⟩) ∩ (chartAt ℂ x).symm ⁻¹' A, _) = _
      rw [hset]
      refine s22gb_piece_hole hp hα hsm (ρ (Sum.inl ⟨x, hx⟩)) (hρs _) x
        (a := chartAt ℂ x x - ((2 * r : ℝ) : ℂ) * (1 + I))
        (b := chartAt ℂ x x + ((2 * r : ℝ) : ℂ) * (1 + I))
        (c := chartAt ℂ x x - (r : ℂ) * (1 + I)) (d := chartAt ℂ x x + (r : ℂ) * (1 + I))
        (by rw [a1, b1]; linarith) (by rw [b1, b2]; linarith) (by rw [b2, a2]; linarith)
        (by rw [a3, b3]; linarith) (by rw [b3, b4]; linarith) (by rw [b4, a4]; linarith)
        (hψ (Sum.inl ⟨x, hx⟩)) (fun z hz => hreg x z (hSqt x hx hz.1) (hregInl x hx z hz))
        (fun z hz => hρvan (Sum.inl ⟨x, hx⟩) z (hSqt x hx hz.1) hz.2) ?_
      intro z hz
      have hzK : z ∈ wv_rectK (chartAt ℂ x x - (r : ℂ) * (1 + I))
          (chartAt ℂ x x + (r : ℂ) * (1 + I)) := hz.1
      have hB' : (chartAt ℂ x).symm z ∈ B x := ⟨z, hzK, rfl⟩
      have hother : ∀ j, j ≠ Sum.inl ⟨x, hx⟩ → ρ j ((chartAt ℂ x).symm z) = 0 := by
        rintro (⟨x', hx'⟩ | ⟨y', hy'⟩) hj
        · have hne : x' ≠ x := fun h => hj (by subst h; rfl)
          refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
          have := hρsub (Sum.inl ⟨x', hx'⟩) h
          exact Set.disjoint_left.1 (hBgdisj x hx x' hx' (fun h => hne h.symm)) (hBBg x hB') this
        · refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
          obtain ⟨w, hw, hwz⟩ := hρsub (Sum.inr ⟨y', hy'⟩) h
          have hAm := (hδy y' (htC y' hy')).2 w (s22gb_osq_subset_sq (hδ0 y').le hw)
          have hwz' : (chartAt ℂ y').symm w = (chartAt ℂ x).symm z := hwz
          rw [hwz'] at hAm
          exact hAm.2 (mem_iUnion₂.2 ⟨x, hx, hB'⟩)
      have hsum := hρsum ((chartAt ℂ x).symm z)
      rw [Finset.sum_eq_single (Sum.inl ⟨x, hx⟩) (fun j _ hj => hother j hj)
        (fun h => absurd (Finset.mem_univ _) h)] at hsum
      exact hsum
    · obtain ⟨c1, c2, c3, c4⟩ := s22gb_sq_corners (c := chartAt ℂ y y) (δ := δ y)
      have hset : Dom (Sum.inr ⟨y, hy⟩) ∩ (chartAt ℂ y).symm ⁻¹' A = Dom (Sum.inr ⟨y, hy⟩) :=
        inter_eq_left.2 (fun z hz => (hδy y (htC y hy)).2 z (hDsub _ hz))
      show (∫ z in Dom (Sum.inr ⟨y, hy⟩) ∩ (chartAt ℂ y).symm ⁻¹' A, _) = 0
      rw [hset]
      exact s22gb_piece_full hp hα hsm (ρ (Sum.inr ⟨y, hy⟩)) (hρs _) y
        (a := chartAt ℂ y y - (δ y : ℂ) * (1 + I)) (b := chartAt ℂ y y + (δ y : ℂ) * (1 + I))
        (by rw [c1, c2]; linarith [hδ0 y]) (by rw [c3, c4]; linarith [hδ0 y])
        (hψ (Sum.inr ⟨y, hy⟩))
        (fun z hz => hreg y z (hball y (hsqε (Sum.inr ⟨y, hy⟩) hz))
          (hZA _ ((hδy y (htC y hy)).2 z hz)))
        (fun z hz => hρvan (Sum.inr ⟨y, hy⟩) z (hball y (hsqε (Sum.inr ⟨y, hy⟩) hz.1)) hz.2)
  obtain ⟨hfin, hval⟩ := s22gb_assembly hp hFH hq hα hsm (fun i => ρ i) hρs hρ0 hρsum xs Dom
    (fun i => ψ0 (xs i)) hDo hDt (fun i z hz => (hψ i z (hDsub i hz)).2.1)
    (fun i z hz => (hψ i z (hDsub i hz)).2.2.1) (fun i z hz => (hψ i z (hDsub i hz)).2.2.2.1)
    (fun i z hz => (hψ i z (hDsub i hz)).2.2.2.2.self_of_nhds)
    (fun i => hρsub i) hDbd hDvol A hAo hAreg W (fun i z => rfl) hWc hWbd s hstokes
  refine ⟨hfin, ?_⟩
  rw [hval, Fintype.sum_sum_type]
  simp only [hs, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_coe_sort Z (fun x => s22cd_rectBoundary (α x)
    (chartAt ℂ x x - (r : ℂ) * (1 + I)) (chartAt ℂ x x + (r : ℂ) * (1 + I)))

end GaussBonnetHoles

end LiZhongQC
