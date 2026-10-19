import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Prime ends: the theorems that need §20

The open part of Carathéodory's prime-end theory of `LZ3.txt`, moved here from `Lemmas/Caratheodory.lean` and
`ClusterSets.lean` with byte-identical statements (docstrings refreshed; user decision, 2026-09-27) so that the proofs
can use §20 (planar separation `s20v_ps`, the continuous extension `s20g_ext_continuous` under clause (ii′) of
`s20g_QLC`) and the Jordan curve theorem (`jordan_curve_theorem_complex_bounded`, `isJordanCurve_of_loop`).  The
definitions (crosscuts, null-chains, prime ends, impressions, principal points, cluster sets) stay in those files.

* Theorem C1 `caratheodory_continuous_iff` (proved) and the Carathéodory–Torhorst criterion
  `locallyConnected_iff_clusterSet_subsingleton` (proved from C1);
* `crosscut_separates` (proved, by collapsing `∂Δ` to a point and the Jordan curve theorem);
* `locallyConnectedSpace_frontier_iff` (proved: a σ-chain of circle arcs along Wolff radii chosen off a
  Jensen–Fatou null set);
* `lindelof` (proved: Lindelöf's reflection argument after a Cayley transfer, with a half-disc and a
  quarter-disc harmonic majorant);
* `principalPoints_isCompact_isConnected` (proved: the principal points of a prime end are the radial cluster set of
  `f` at the corresponding point of the circle, a decreasing intersection of continua);
* `caratheodory_primeEnd` (proved: prime ends are the classes of circular chains `f(Δ ∩ sphere ζ rₙ)` along Wolff
  radii chosen off a Jensen–Fatou null set; surjectivity is Pommerenke's Thm 2.15 (c) run on the chain ends);
* `caratheodory_primeEnd_principal` (proved: the radius crosses the late crosscuts of a representing chain, and Wolff
  radii in windows with Koebe's distortion along the radius give a circular chain converging to a radial cluster
  point).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **First hit.**  If `y ∉ Ω` (open) and `w ∈ closure Ω`, the segment from `y` towards `w` meets
`frontier Ω` at a point `z` with `[y, z] ⊆ Ωᶜ`. -/
theorem pe1_first_hit {Ω : Set ℂ} (hΩo : IsOpen Ω) {y w : ℂ} (hy : y ∉ Ω) (hw : w ∈ closure Ω) :
    ∃ z ∈ segment ℝ y w, z ∈ frontier Ω ∧ segment ℝ y z ⊆ Ωᶜ := by
  set g : ℝ → ℂ := fun s => y + (s : ℂ) * (w - y) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  set T : Set ℝ := Icc 0 1 ∩ g ⁻¹' closure Ω with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_closure.preimage hgc)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simp [hg, hw]⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have hbelow : ∀ s, 0 ≤ s → s < s₀ → g s ∉ closure Ω := by
    intro s hs0 hss hcl
    have hs1 : s ≤ 1 := (hss.trans_le (csInf_le hTb h1T)).le
    exact absurd (csInf_le hTb ⟨⟨hs0, hs1⟩, hcl⟩) (not_le.2 hss)
  have hzΩ : g s₀ ∉ Ω := by
    intro hzΩ
    rcases eq_or_lt_of_le hs₀T.1.1 with h0 | hpos
    · apply hy
      have : g s₀ = y := by rw [← h0]; simp [hg]
      rwa [this] at hzΩ
    · -- points slightly before `s₀` are still in `Ω`
      have hev : ∀ᶠ s in 𝓝 s₀, g s ∈ Ω := hgc.continuousAt.eventually_mem (hΩo.mem_nhds hzΩ)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      set s := max 0 (s₀ - ε / 2) with hsdef
      have hs0 : 0 ≤ s := le_max_left _ _
      have hss : s < s₀ := max_lt hpos (by linarith)
      have hds : dist s s₀ < ε := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · have : s₀ - ε / 2 ≤ s := le_max_right _ _
          linarith
        · linarith
      exact hbelow s hs0 hss (subset_closure (hball hds))
  refine ⟨g s₀, ?_, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨s₀, hs₀T.1, by simp [hg]⟩
  · rw [hΩo.frontier_eq]
    exact ⟨hs₀T.2, hzΩ⟩
  · rw [segment_eq_image']
    rintro _ ⟨u, hu, rfl⟩
    show y + u • (g s₀ - y) ∉ Ω
    have hmul : y + u • (g s₀ - y) = g (u * s₀) := by
      simp only [hg, Complex.real_smul]
      push_cast
      ring
    rw [hmul]
    rcases eq_or_lt_of_le hu.2 with h1 | h1
    · rw [h1, one_mul]
      exact hzΩ
    · rcases eq_or_lt_of_le hs₀T.1.1 with h0 | hpos
      · rw [← h0, mul_zero]
        have : g 0 = y := by simp [hg]
        rw [this]
        exact hy
      · exact fun h => hbelow (u * s₀) (mul_nonneg hu.1 hs₀T.1.1)
          (by nlinarith [hu.1]) (subset_closure h)

/-- **Local connectivity of `∂Ω` ⇒ clause (ii′) of `s20g_QLC` at each `w ∈ ∂Ω`** (for `Ω` open and connected; only
the connected neighbourhoods of `w` in `∂Ω` are used; no simple connectivity, no boundedness). -/
theorem pe1_ii_of_lc {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hlc : LocallyConnectedSpace (frontier Ω)) {w : ℂ} (hw : w ∈ frontier Ω) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > 0, ∀ p ∈ Ω \ ball w R, ∀ q ∈ Ω \ ball w R, JoinedIn (Ω \ ball w ρ) p q := by
  set ε := R / 2 with hε
  have hε0 : 0 < ε := by positivity
  -- a connected neighbourhood `V` of `w` in `∂Ω`, inside `ball w ε`
  obtain ⟨V, hVsub, hVc, hwV, δ, hδ, hδV⟩ : ∃ V ⊆ frontier Ω ∩ ball w ε, IsPreconnected V ∧ w ∈ V ∧
      ∃ δ > 0, frontier Ω ∩ ball w δ ⊆ V := by
    set x : frontier Ω := ⟨w, hw⟩
    have hN : (Subtype.val ⁻¹' ball w ε : Set (frontier Ω)) ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε0))
    obtain ⟨s, ⟨hso, hxs, hsc⟩, hss⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 hN
    obtain ⟨U, hUo, hUs⟩ := isOpen_induced_iff.1 hso
    have hwU : w ∈ U := by
      have : x ∈ Subtype.val ⁻¹' U := by rw [hUs]; exact hxs
      exact this
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hUo w hwU
    refine ⟨Subtype.val '' s, ?_, hsc.isPreconnected.image _ continuous_subtype_val.continuousOn,
      ⟨x, hxs, rfl⟩, δ, hδ, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.2, hss hz⟩
    · rintro z ⟨hzf, hzb⟩
      refine ⟨⟨z, hzf⟩, ?_, rfl⟩
      rw [← hUs]
      exact hδU hzb
  set ρ := min (δ / 2) (ε / 2) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ : ρ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hfrΩ : frontier Ω ⊆ Ωᶜ := by
    rw [hΩo.frontier_eq]
    exact fun z hz => hz.2
  have hVcl : closure V ⊆ frontier Ω := closure_minimal (fun z hz => (hVsub hz).1) isClosed_frontier
  have hVclε : closure V ⊆ closedBall w ε :=
    closure_minimal (fun z hz => ball_subset_closedBall (hVsub hz).2) isClosed_closedBall
  set A₂ : Set ℂ := closedBall w ρ ∪ closure V with hA₂
  have hA₂c : IsClosed A₂ := isClosed_closedBall.union isClosed_closure
  have hA₂ε : A₂ ⊆ closedBall w ε :=
    union_subset (closedBall_subset_closedBall hρε.le) hVclε
  set S : Set ℂ := Ωᶜ ∩ A₂ with hS
  have hwS : w ∈ S := ⟨hfrΩ hw, Or.inl (mem_closedBall_self hρ0.le)⟩
  -- `S` is preconnected: first-hit segments join its points to `closure V`
  have hSc : IsPreconnected S := by
    refine isPreconnected_of_forall w fun y hy => ?_
    have hVS : closure V ⊆ S := fun z hz => ⟨hfrΩ (hVcl hz), Or.inr hz⟩
    rcases hy.2 with hyb | hyV
    · have hwcl : w ∈ closure Ω := frontier_subset_closure hw
      obtain ⟨z, hzs, hzf, hseg⟩ := pe1_first_hit hΩo hy.1 hwcl
      have hsegB : segment ℝ y w ⊆ closedBall w ρ :=
        (convex_closedBall w ρ).segment_subset hyb (mem_closedBall_self hρ0.le)
      have hzb : z ∈ closedBall w ρ := hsegB hzs
      have hzV : z ∈ V := hδV ⟨hzf, closedBall_subset_ball hρδ hzb⟩
      refine ⟨segment ℝ y z ∪ closure V, ?_, Or.inr (subset_closure hwV),
        Or.inl (left_mem_segment ℝ y z), ?_⟩
      · refine union_subset (fun u hu => ⟨hseg hu, Or.inl ?_⟩) hVS
        exact (convex_closedBall w ρ).segment_subset hyb hzb hu
      · exact IsPreconnected.union z (right_mem_segment ℝ y z) (subset_closure hzV)
          (convex_segment y z).isPreconnected hVc.closure
    · exact ⟨closure V, hVS, subset_closure hwV, hyV, hVc.closure⟩
  refine ⟨ρ, hρ0, fun p hp q hq => ?_⟩
  have hpz : ∀ u ∈ Ω \ ball w R, R ≤ ‖u - w‖ := by
    intro u hu
    have h := hu.2
    rwa [mem_ball, not_lt, dist_eq_norm] at h
  have hpw := hpz p hp
  have hqw := hpz q hq
  set E : Set ℂ := {ζ : ℂ | ε < ‖ζ - w‖} with hE
  have hEo : IsOpen E := isOpen_lt continuous_const (by fun_prop)
  have hEc : IsPreconnected E := by
    have h := (isPreconnected_setOf_lt_norm (r := ε) hε0.le).image (fun ζ => ζ + w)
      (continuous_id.add continuous_const).continuousOn
    convert h using 1
    ext ζ
    constructor
    · intro hζ
      exact ⟨ζ - w, show ε < ‖ζ - w‖ from hζ, sub_add_cancel ζ w⟩
    · rintro ⟨u, hu, rfl⟩
      show ε < ‖u + w - w‖
      simpa using hu
  have hEA : E ⊆ A₂ᶜ := fun ζ hζ hA => by
    have h1 := hA₂ε hA
    rw [mem_closedBall, dist_eq_norm] at h1
    exact absurd hζ (not_lt.2 h1)
  have hpE : p ∈ E := show ε < ‖p - w‖ by linarith
  have hqE : q ∈ E := show ε < ‖q - w‖ by linarith
  by_contra hJ
  have hsep : ¬ JoinedIn (Ω ∩ A₂ᶜ) p q := fun h =>
    hJ (h.mono fun z hz => ⟨hz.1, fun hzb => hz.2 (Or.inl (ball_subset_closedBall hzb))⟩)
  have hp' : p ∈ Ω ∩ A₂ᶜ := ⟨hp.1, hEA hpE⟩
  have hq' : q ∈ Ω ∩ A₂ᶜ := ⟨hq.1, hEA hqE⟩
  obtain ⟨lβ, hβ, hβe⟩ := s20v_polygon_path hΩo hΩc hp.1 hq.1
  obtain ⟨lc, hc, hce⟩ := s20v_polygon_path hEo hEc hqE hpE
  have htr : polyTrace (p :: (lβ ++ lc)) ⊆ Ω ∪ E := s20v_trace_subset hp.1 hβ hβe hc hce
  have hnot : ∀ x ∈ S, x ∉ polyTrace (p :: (lβ ++ lc)) := by
    intro x hx hxt
    rcases htr hxt with h | h
    · exact hx.1 h
    · exact hEA h hx.2
  obtain ⟨N, hN0⟩ := exists_int_polyWinding (hnot w hwS)
  have hN : ∀ x ∈ S, polyWinding (p :: (lβ ++ lc)) x = N := fun x hx =>
    (s20v_b_polyWinding_const hSc hnot hwS hx).trans hN0
  obtain ⟨lN, hlN, hlNe, hlNw⟩ :=
    s20v_ext_loop (z := w) (q := p) (t := ε) hε0.le (by linarith) (-N)
  have hA : lastOf p (lβ ++ lc) = p := by rw [lastOf_append, hβe, hce]
  have hc' : SegsIn A₂ᶜ q (lc ++ lN) := by
    rw [segsIn_append]
    refine ⟨s20v_segsIn_mono hEA hc, ?_⟩
    rw [hce]
    exact s20v_segsIn_mono hEA hlN
  have hce' : lastOf q (lc ++ lN) = p := by rw [lastOf_append, hce, hlNe]
  obtain ⟨x, hxΩ, hxB, hx⟩ := s20v_ps hΩo hA₂c.isOpen_compl hp' hq' hsep hβ hβe hc' hce'
  have hxA : x ∈ A₂ := not_not.1 hxB
  have hxS : x ∈ S := ⟨hxΩ, hxA⟩
  have hxε : ‖x - w‖ ≤ ε := by
    have h1 := hA₂ε hxA
    rwa [mem_closedBall, dist_eq_norm] at h1
  rw [← List.append_assoc, s20v_polyWinding_append hA hlNe, hN x hxS, hlNw x hxε] at hx
  simp at hx

/-- **C1, (c) ⇒ (b)**: a continuous image of the circle is locally connected. -/
theorem pe1_lc_of_circle_image {K : Set ℂ} {γ : Circle → ℂ} (hγ : Continuous γ) (hK : range γ = K) :
    LocallyConnectedSpace K := by
  have : LocallyConnectedSpace Circle :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  set q : Circle → K := fun ζ => ⟨γ ζ, hK ▸ mem_range_self ζ⟩ with hqdef
  have hq : Continuous q := hγ.subtype_mk _
  have hsurj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [← hK] at hz
    obtain ⟨ζ, rfl⟩ := hz
    exact ⟨ζ, rfl⟩
  exact locallyConnectedSpace_of_isQuotientMap (Topology.IsQuotientMap.of_surjective_continuous hsurj hq)

/-- **Theorem C1.**  For a conformal map `f` of the disc onto a bounded domain `Ω`, the following
are equivalent: `f` extends continuously from the closed disc onto `closure Ω`; `∂Ω` is locally
connected; `∂Ω` is a continuous image of the circle.

Proof (s21r, 2026-09-27): (a) ⇒ (c) restricts the extension to the circle; (c) ⇒ (b) since a continuous
image of the circle is locally connected; (b) ⇒ (a): local connectivity of `∂Ω` gives clause (ii′) of `s20g_QLC` by
planar separation (`s20v_ps`, `s20v_ext_loop`), and then `s20g_ext_continuous` extends `f` (Carathéodory's
argument of Theorem C2 with local connectivity in place of the Jordan input).  No Hahn–Mazurkiewicz theorem is
needed.  Moved here from `Lemmas/Caratheodory.lean`, since the proof uses §20. -/
theorem caratheodory_continuous_iff {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    List.TFAE
      [∃ F : ℂ → ℂ, (∀ z ∈ unitDisc, F z = f z) ∧ ContinuousOn F (closedBall 0 1) ∧
          F '' closedBall 0 1 = closure Ω,
        LocallyConnectedSpace (frontier Ω),
        ∃ γ : Circle → ℂ, Continuous γ ∧ range γ = frontier Ω] := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩc : IsPreconnected Ω := by
    rw [← hf.2.2]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image f hf.1.continuousOn
  have hmem : ∀ ζ : Circle, (ζ : ℂ) ∈ closedBall (0 : ℂ) 1 := fun ζ =>
    mem_closedBall_zero_iff.2 (Circle.norm_coe ζ).le
  tfae_have 1 → 3 := by
    rintro ⟨F, hFf, hFc, hFi⟩
    refine ⟨fun ζ => F ζ, hFc.comp_continuous continuous_subtype_val hmem, ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨ζ, rfl⟩
      have hζ1 : ‖(ζ : ℂ)‖ = 1 := Circle.norm_coe ζ
      rw [hΩo.frontier_eq]
      refine ⟨hFi ▸ mem_image_of_mem F (hmem ζ), ?_⟩
      -- `F ζ` is a limit of `f` along `(1 - 1/(n+2)) ζ`
      set z : ℕ → ℂ := fun n => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * ζ with hz
      have hzn : ∀ n, ‖z n‖ = 1 - 1 / ((n : ℝ) + 2) := fun n => by
        have h1 : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
          have : 1 / ((n : ℝ) + 2) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
          linarith
        rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1, hζ1, mul_one]
      have hzD : ∀ n, z n ∈ unitDisc := fun n => by
        rw [unitDisc, mem_ball_zero_iff, hzn]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      have hzζ : Tendsto z atTop (𝓝 (ζ : ℂ)) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 - 0)) := by
          refine tendsto_const_nhds.sub ?_
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          push_cast
          ring
        rw [sub_zero] at h1
        have h2 := ((Complex.continuous_ofReal.tendsto 1).comp h1).mul_const (ζ : ℂ)
        simpa [hz, Function.comp_def] using h2
      have hFt : Tendsto (fun n => f (z n)) atTop (𝓝 (F ζ)) := by
        have h1 : Tendsto (fun n => F (z n)) atTop (𝓝 (F ζ)) :=
          ((hFc _ (hmem ζ)).tendsto.comp (tendsto_nhdsWithin_iff.2
            ⟨hzζ, Eventually.of_forall fun n => ball_subset_closedBall (hzD n)⟩))
        exact h1.congr fun n => hFf _ (hzD n)
      exact tendsto_boundary_of_isConformalOnto hf hζ1 hzD hzζ hFt
    · intro w hw
      have hwcl : w ∈ F '' closedBall 0 1 := hFi ▸ frontier_subset_closure hw
      obtain ⟨z, hz, rfl⟩ := hwcl
      rcases eq_or_lt_of_le (mem_closedBall_zero_iff.1 hz) with h | h
      · exact ⟨⟨z, mem_sphere_zero_iff_norm.2 h⟩, rfl⟩
      · have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 h
        rw [hΩo.frontier_eq, hFf z hzD] at hw
        exact absurd (hf.mapsTo hzD) hw.2
  tfae_have 3 → 2 := fun ⟨γ, hγ, hr⟩ => pe1_lc_of_circle_image hγ hr
  tfae_have 2 → 1 := by
    intro hlc
    obtain ⟨F, hFc, hFf, -, hFi⟩ :=
      s20g_ext_continuous hΩ hf fun w hw R hR => pe1_ii_of_lc hΩo hΩc hlc hw hR
    exact ⟨F, fun z hz => hFf hz, hFc, hFi⟩
  tfae_finish

/-- **Carathéodory–Torhorst, cluster-set form.**  For a conformal map `f` of the disc onto a bounded
domain, `∂Ω` is locally connected iff every cluster set at a boundary point is a single point.

Proved from Theorem C1 (`caratheodory_continuous_iff`, above) and
`continuous_extension_iff_forall_clusterSet_subsingleton`. -/
theorem locallyConnected_iff_clusterSet_subsingleton {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LocallyConnectedSpace ↥(frontier Ω) ↔
      ∀ ξ ∈ sphere (0 : ℂ) 1, ∃ w, clusterSet f unitDisc ξ = {w} := by
  have h01 := (caratheodory_continuous_iff hΩ hf).out 1 2
  rw [← h01, ← continuous_extension_iff_forall_clusterSet_subsingleton hf.1]
  have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
  constructor
  · rintro ⟨F, hFf, hFc, -⟩
    refine ⟨F, ?_, fun z hz => hFf z hz⟩
    rw [hcl]
    exact hFc
  · rintro ⟨g, hgc, hgf⟩
    have hgc' : ContinuousOn g (closedBall 0 1) := by
      rw [← hcl]
      exact hgc
    refine ⟨g, fun z hz => hgf hz, hgc', ?_⟩
    have himg : g '' unitDisc = Ω := by
      rw [hgf.image_eq]
      exact hf.2.2
    apply Subset.antisymm
    · have h1 : g '' closure unitDisc ⊆ closure (g '' unitDisc) := hgc.image_closure
      rw [hcl, himg] at h1
      exact h1
    · refine closure_minimal ?_ ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hgc').isClosed
      rw [← himg]
      exact Set.image_mono ball_subset_closedBall

/-- The collapse map `ψ(z) = ((1 - |z|)/|z|²) z`, a homeomorphism `Δ ∖ {0} → ℂ ∖ {0}` sending
`|z| → 1` to `0` and `z → 0` to `∞`. -/
def pe2_psi (z : ℂ) : ℂ := (((1 - ‖z‖) / ‖z‖ ^ 2 : ℝ) : ℂ) * z

/-- The inverse of `pe2_psi`: `Φ(u) = u / (|u| (1 + |u|))`. -/
def pe2_Phi (u : ℂ) : ℂ := ((1 / (‖u‖ * (1 + ‖u‖)) : ℝ) : ℂ) * u

/-- The modulus of the collapse map: `‖ψ z‖ = (1 - ‖z‖)/‖z‖` on `Δ ∖ {0}`. -/
theorem pe2_norm_psi {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) : ‖pe2_psi z‖ = (1 - ‖z‖) / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [pe2_psi, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
  field_simp

/-- The modulus of the inverse collapse map: `‖Φ u‖ = 1/(1 + ‖u‖)` for `u ≠ 0`. -/
theorem pe2_norm_Phi {u : ℂ} (hu : u ≠ 0) : ‖pe2_Phi u‖ = 1 / (1 + ‖u‖) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [pe2_Phi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- `Φ ∘ ψ = id` on `Δ ∖ {0}`. -/
theorem pe2_Phi_psi {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) : pe2_Phi (pe2_psi z) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have h1 : 0 < 1 - ‖z‖ := by linarith
  rw [pe2_Phi, pe2_norm_psi hz0 hz1, pe2_psi, ← mul_assoc, ← ofReal_mul]
  have : (1 / ((1 - ‖z‖) / ‖z‖ * (1 + (1 - ‖z‖) / ‖z‖)) * ((1 - ‖z‖) / ‖z‖ ^ 2) : ℝ) = 1 := by
    field_simp
    ring
  rw [this, ofReal_one, one_mul]

/-- `ψ ∘ Φ = id` on `ℂ ∖ {0}`. -/
theorem pe2_psi_Phi {u : ℂ} (hu : u ≠ 0) : pe2_psi (pe2_Phi u) = u := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [pe2_psi, pe2_norm_Phi hu, pe2_Phi, ← mul_assoc, ← ofReal_mul]
  have : ((1 - 1 / (1 + ‖u‖)) / (1 / (1 + ‖u‖)) ^ 2 * (1 / (‖u‖ * (1 + ‖u‖))) : ℝ) = 1 := by
    field_simp
    ring
  rw [this, ofReal_one, one_mul]

/-- `Φ` does not vanish on `ℂ ∖ {0}`. -/
theorem pe2_Phi_ne_zero {u : ℂ} (hu : u ≠ 0) : pe2_Phi u ≠ 0 := by
  intro h
  have := pe2_norm_Phi hu
  rw [h, norm_zero] at this
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have : 0 < 1 / (1 + ‖u‖) := by positivity
  linarith

/-- `Φ` maps `ℂ ∖ {0}` into the unit disc. -/
theorem pe2_Phi_mem_unitDisc {u : ℂ} (hu : u ≠ 0) : pe2_Phi u ∈ unitDisc := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [unitDisc, mem_ball_zero_iff, pe2_norm_Phi hu, div_lt_one (by positivity)]
  linarith

/-- `ψ` does not vanish on `Δ ∖ {0}`. -/
theorem pe2_psi_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) : pe2_psi z ≠ 0 := by
  intro h
  have := pe2_norm_psi hz0 hz1
  rw [h, norm_zero] at this
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have : 0 < (1 - ‖z‖) / ‖z‖ := div_pos (by linarith) hn
  linarith

/-- `ψ` is continuous away from `0`. -/
theorem pe2_continuousAt_psi {z : ℂ} (hz0 : z ≠ 0) : ContinuousAt pe2_psi z := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hz0)
  have hr : ContinuousAt (fun w : ℂ => (1 - ‖w‖) / ‖w‖ ^ 2) z :=
    ((continuous_const.sub continuous_norm).continuousAt).div
      ((continuous_norm.pow 2).continuousAt) hn
  exact (continuous_ofReal.continuousAt.comp hr).mul continuousAt_id

/-- `Φ` is continuous away from `0`. -/
theorem pe2_continuousAt_Phi {u : ℂ} (hu : u ≠ 0) : ContinuousAt pe2_Phi u := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hne : ‖u‖ * (1 + ‖u‖) ≠ 0 := by positivity
  have hr : ContinuousAt (fun w : ℂ => 1 / (‖w‖ * (1 + ‖w‖))) u :=
    continuousAt_const.div (continuous_norm.mul (continuous_const.add continuous_norm)).continuousAt
      hne
  exact (continuous_ofReal.continuousAt.comp hr).mul continuousAt_id

/-- `f⁻¹` of a conformal `f : Δ → Ω`. -/
def pe2_ginv (f : ℂ → ℂ) : ℂ → ℂ := Function.invFunOn f unitDisc

/-- For `w ∈ Ω`, `f⁻¹ w` lies in the unit disc and `f (f⁻¹ w) = w`. -/
theorem pe2_ginv_mem {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) : pe2_ginv f w ∈ unitDisc ∧ f (pe2_ginv f w) = w := by
  rw [← hf.2.2] at hw
  exact ⟨Function.invFunOn_mem hw, Function.invFunOn_eq hw⟩

/-- **Properness.**  Near a parameter `t₀` with `γ t₀ ∉ Ω`, the points `f⁻¹(γ t)` (for
`γ t ∈ Ω`) leave every closed disc `|z| ≤ r < 1`.  No landing of `f⁻¹ ∘ γ` is used. -/
theorem pe2_eventually_lt_norm_ginv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} {s : Set ℝ} {t₀ : ℝ} (hγ : ContinuousWithinAt γ s t₀) (ht₀ : γ t₀ ∉ Ω)
    {r : ℝ} (hr : r < 1) : ∀ᶠ t in 𝓝[s] t₀, γ t ∈ Ω → r < ‖pe2_ginv f (γ t)‖ := by
  set K : Set ℂ := f '' closedBall 0 r with hK
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := closedBall_subset_ball hr
  have hKc : IsCompact K := (isCompact_closedBall 0 r).image_of_continuousOn
    (hf.1.continuousOn.mono hsub)
  have hKΩ : K ⊆ Ω := by
    rw [hK, ← hf.2.2]
    exact image_mono hsub
  have hγK : γ t₀ ∈ Kᶜ := fun h => ht₀ (hKΩ h)
  filter_upwards [hγ (hKc.isClosed.isOpen_compl.mem_nhds hγK)] with t ht htΩ
  by_contra hle
  push Not at hle
  obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf htΩ
  apply ht
  exact ⟨pe2_ginv f (γ t), mem_closedBall_zero_iff.2 hle, hfg⟩

/-- The collapsed loop `F = ψ ∘ f⁻¹ ∘ γ` on `(0,1)`, `0` elsewhere. -/
def pe2_collapseLoop (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℝ → ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun t => pe2_psi (pe2_ginv f (γ t)))

/-- The collapsed loop on `(0,1)` is `ψ ∘ f⁻¹ ∘ γ`. -/
theorem pe2_collapseLoop_of_mem {f : ℂ → ℂ} {γ : ℝ → ℂ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    pe2_collapseLoop f γ t = pe2_psi (pe2_ginv f (γ t)) :=
  indicator_of_mem ht _

/-- The collapsed loop vanishes off `(0,1)`. -/
theorem pe2_collapseLoop_of_notMem {f : ℂ → ℂ} {γ : ℝ → ℂ} {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    pe2_collapseLoop f γ t = 0 :=
  indicator_of_notMem ht _

/-- `f⁻¹(γ t) ≠ 0` on `(0,1)` once `f 0 ∉ C`. -/
theorem pe2_ginv_ne_zero {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγΩ : γ '' Ioo 0 1 ⊆ Ω) (hf0 : f 0 ∉ γ '' Ioo 0 1) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : pe2_ginv f (γ t) ≠ 0 := by
  intro h
  apply hf0
  refine ⟨t, ht, ?_⟩
  rw [← h, (pe2_ginv_mem hf (hγΩ ⟨t, ht, rfl⟩)).2]

/-- Continuity of the collapsed loop at an endpoint parameter `t₀` with `γ t₀ ∉ Ω`. -/
theorem pe2_continuousWithinAt_collapseLoop_end {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {γ : ℝ → ℂ} (hγΩ : γ '' Ioo 0 1 ⊆ Ω)
    {t₀ : ℝ} (hγ : ContinuousWithinAt γ (Icc 0 1) t₀) (ht₀ : γ t₀ ∉ Ω)
    (ht₀' : t₀ ∉ Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (pe2_collapseLoop f γ) (Icc 0 1) t₀ := by
  rw [ContinuousWithinAt, pe2_collapseLoop_of_notMem ht₀', Metric.tendsto_nhds]
  intro ε hε
  have hr : 1 / (1 + ε) < 1 := by rw [div_lt_one (by linarith)]; linarith
  filter_upwards [pe2_eventually_lt_norm_ginv hf hγ ht₀ hr] with t ht
  by_cases htI : t ∈ Ioo (0 : ℝ) 1
  · have htΩ : γ t ∈ Ω := hγΩ ⟨t, htI, rfl⟩
    have hlt := ht htΩ
    obtain ⟨hgD, -⟩ := pe2_ginv_mem hf htΩ
    have hg1 : ‖pe2_ginv f (γ t)‖ < 1 := mem_ball_zero_iff.1 hgD
    have hpos : 0 < 1 / (1 + ε) := by positivity
    have hg0 : pe2_ginv f (γ t) ≠ 0 := by
      intro h; rw [h, norm_zero] at hlt; linarith
    rw [pe2_collapseLoop_of_mem htI, dist_zero_right, pe2_norm_psi hg0 hg1]
    have hn : 0 < ‖pe2_ginv f (γ t)‖ := norm_pos_iff.2 hg0
    rw [div_lt_iff₀ hn]
    rw [div_lt_iff₀ (by linarith)] at hlt
    linarith
  · rw [pe2_collapseLoop_of_notMem htI, dist_self]
    exact hε

/-- **The decisive step of the collapse route.**  For a conformal `f : Δ → Ω` and a crosscut
`γ` of `Ω` (continuous on `[0,1]`, injective on `(0,1)`, `γ(0,1) ⊆ Ω`, `γ 0, γ 1 ∉ Ω`, loops
allowed) with `f 0 ∉ γ(0,1)`, the collapsed loop `ψ ∘ f⁻¹ ∘ γ` (closed up by `0`) is a Jordan
curve.  Nothing about the landing of `f⁻¹ ∘ γ` on `∂Δ` (Pommerenke Prop. 2.14) is used. -/
theorem pe2_isJordanCurve_collapseLoop {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Ioo 0 1))
    (hγΩ : γ '' Ioo 0 1 ⊆ Ω) (h0 : γ 0 ∉ Ω) (h1 : γ 1 ∉ Ω) (hf0 : f 0 ∉ γ '' Ioo 0 1) :
    IsJordanCurve (toExt (pe2_collapseLoop f γ '' Icc 0 1)) := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hgc : ContinuousOn (pe2_ginv f) Ω := (hf.symm isOpen_ball).1.continuousOn
  have h0I : (0 : ℝ) ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ h.1
  have h1I : (1 : ℝ) ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ h.2
  apply isJordanCurve_of_loop
  · intro t ht
    by_cases htI : t ∈ Ioo (0 : ℝ) 1
    · -- interior parameter: `F = ψ ∘ f⁻¹ ∘ γ` near `t`
      have htΩ : γ t ∈ Ω := hγΩ ⟨t, htI, rfl⟩
      have hγt : ContinuousAt γ t := hγc.continuousAt (Icc_mem_nhds htI.1 htI.2)
      have hgt : ContinuousAt (pe2_ginv f) (γ t) := hgc.continuousAt (hΩo.mem_nhds htΩ)
      have hpt : ContinuousAt pe2_psi (pe2_ginv f (γ t)) := pe2_continuousAt_psi (pe2_ginv_ne_zero hf hγΩ hf0 htI)
      have hcomp : ContinuousAt (fun s => pe2_psi (pe2_ginv f (γ s))) t :=
        hpt.comp (f := fun s => pe2_ginv f (γ s)) (hgt.comp (f := γ) hγt)
      have heq : (fun s => pe2_psi (pe2_ginv f (γ s))) =ᶠ[𝓝 t] pe2_collapseLoop f γ := by
        filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
        rw [pe2_collapseLoop_of_mem hs]
      exact (hcomp.congr heq).continuousWithinAt
    · rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        exact pe2_continuousWithinAt_collapseLoop_end hf hγΩ (hγc 0 ht) h0 h0I
      · have : t = 1 := by
          by_contra hne
          exact htI ⟨h, lt_of_le_of_ne ht.2 hne⟩
        subst this
        exact pe2_continuousWithinAt_collapseLoop_end hf hγΩ (hγc 1 ht) h1 h1I
  · intro s hs t ht hst
    have key : ∀ u ∈ Ico (0 : ℝ) 1, u ∉ Ioo (0 : ℝ) 1 → u = 0 := by
      intro u hu huI
      rcases eq_or_lt_of_le hu.1 with h | h
      · exact h.symm
      · exact absurd ⟨h, hu.2⟩ huI
    have hnz : ∀ u ∈ Ioo (0 : ℝ) 1, pe2_collapseLoop f γ u ≠ 0 := by
      intro u hu
      rw [pe2_collapseLoop_of_mem hu]
      exact pe2_psi_ne_zero (pe2_ginv_ne_zero hf hγΩ hf0 hu)
        (mem_ball_zero_iff.1 (pe2_ginv_mem hf (hγΩ ⟨u, hu, rfl⟩)).1)
    by_cases hsI : s ∈ Ioo (0 : ℝ) 1
    · by_cases htI : t ∈ Ioo (0 : ℝ) 1
      · rw [pe2_collapseLoop_of_mem hsI, pe2_collapseLoop_of_mem htI] at hst
        have hsΩ : γ s ∈ Ω := hγΩ ⟨s, hsI, rfl⟩
        have htΩ : γ t ∈ Ω := hγΩ ⟨t, htI, rfl⟩
        obtain ⟨hsD, hfs⟩ := pe2_ginv_mem hf hsΩ
        obtain ⟨htD, hft⟩ := pe2_ginv_mem hf htΩ
        have hg := congrArg pe2_Phi hst
        rw [pe2_Phi_psi (pe2_ginv_ne_zero hf hγΩ hf0 hsI) (mem_ball_zero_iff.1 hsD),
          pe2_Phi_psi (pe2_ginv_ne_zero hf hγΩ hf0 htI) (mem_ball_zero_iff.1 htD)] at hg
        apply hγi hsI htI
        rw [← hfs, ← hft, hg]
      · rw [pe2_collapseLoop_of_notMem htI] at hst
        exact absurd hst (hnz s hsI)
    · by_cases htI : t ∈ Ioo (0 : ℝ) 1
      · rw [pe2_collapseLoop_of_notMem hsI] at hst
        exact absurd hst.symm (hnz t htI)
      · rw [key s hs hsI, key t ht htI]
  · rw [pe2_collapseLoop_of_notMem h0I, pe2_collapseLoop_of_notMem h1I]

/-- Membership transfer through the collapse: for `z ∈ Δ ∖ {0}`, `ψ z` lies on the collapsed curve
iff `f z` lies on the crosscut. -/
theorem pe2_psi_mem_image_collapseLoop_iff {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {γ : ℝ → ℂ} (hγΩ : γ '' Ioo 0 1 ⊆ Ω)
    (hf0 : f 0 ∉ γ '' Ioo 0 1) {z : ℂ} (hzD : z ∈ unitDisc) (hz0 : z ≠ 0) :
    pe2_psi z ∈ pe2_collapseLoop f γ '' Icc 0 1 ↔ f z ∈ γ '' Ioo 0 1 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hzD
  constructor
  · rintro ⟨t, -, hFt⟩
    by_cases htI : t ∈ Ioo (0 : ℝ) 1
    · rw [pe2_collapseLoop_of_mem htI] at hFt
      obtain ⟨htD, hft⟩ := pe2_ginv_mem hf (hγΩ ⟨t, htI, rfl⟩)
      have hg := congrArg pe2_Phi hFt
      rw [pe2_Phi_psi (pe2_ginv_ne_zero hf hγΩ hf0 htI) (mem_ball_zero_iff.1 htD), pe2_Phi_psi hz0 hz1] at hg
      exact ⟨t, htI, by rw [← hft, hg]⟩
    · rw [pe2_collapseLoop_of_notMem htI] at hFt
      exact absurd hFt.symm (pe2_psi_ne_zero hz0 hz1)
  · rintro ⟨t, htI, hγt⟩
    refine ⟨t, Ioo_subset_Icc_self htI, ?_⟩
    rw [pe2_collapseLoop_of_mem htI, hγt, show pe2_ginv f (f z) = z from hf.2.1.leftInvOn_invFunOn hzD]

/-- **The count, normalized case** (`f 0` off the crosscut): the two JCT pieces of the collapsed curve, mapped into
the disc by `Φ = ψ⁻¹` (the unbounded piece together with `0`) and then by `f`, are the two components of `Ω ∖ C`. -/
theorem pe2_card_eq_two_of_zero {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Ioo 0 1))
    (hγΩ : γ '' Ioo 0 1 ⊆ Ω) (h0 : γ 0 ∉ Ω) (h1 : γ 1 ∉ Ω) (hf0 : f 0 ∉ γ '' Ioo 0 1) :
    Nat.card (ConnectedComponents ↥(Ω \ γ '' Ioo 0 1)) = 2 := by
  set J := pe2_collapseLoop f γ '' Icc 0 1 with hJdef
  have hJ : IsJordanCurve (toExt J) := pe2_isJordanCurve_collapseLoop hf hγc hγi hγΩ h0 h1 hf0
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAJ, hBJ, huniv, hAb, -⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  have h0I : (0 : ℝ) ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ h.1
  have h0J : (0 : ℂ) ∈ J := ⟨0, left_mem_Icc.2 zero_le_one, pe2_collapseLoop_of_notMem h0I⟩
  have hA0 : ∀ u ∈ A, u ≠ 0 := fun u hu h => Set.disjoint_left.1 hAJ hu (h ▸ h0J)
  have hB0 : ∀ u ∈ B, u ≠ 0 := fun u hu h => Set.disjoint_left.1 hBJ hu (h ▸ h0J)
  -- the exterior of a large disc lies in `B`
  obtain ⟨R, hR0, hRB⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ u : ℂ, R < ‖u‖ → u ∈ B := by
    obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1
      (hAb.union (isCompact_of_isJordanCurve_toExt hJ).isBounded)
    refine ⟨max R 0, le_max_right _ _, fun u hu => ?_⟩
    have hnot : u ∉ A ∪ J := fun h => by
      have := mem_closedBall_zero_iff.1 (hR h)
      linarith [le_max_left R 0]
    have : u ∈ A ∪ B ∪ J := by rw [huniv]; exact mem_univ u
    rcases this with (h | h) | h
    · exact absurd (Or.inl h) hnot
    · exact h
    · exact absurd (Or.inr h) hnot
  -- the two pieces on the disc side
  have hpsi_cont : ContinuousOn pe2_psi (unitDisc ∩ {0}ᶜ) := fun z hz =>
    (pe2_continuousAt_psi hz.2).continuousWithinAt
  have hPhi_cont : ContinuousOn pe2_Phi {0}ᶜ := fun u hu => (pe2_continuousAt_Phi hu).continuousWithinAt
  have hU0o : IsOpen (unitDisc ∩ {0}ᶜ) := isOpen_ball.inter isOpen_compl_singleton
  have hAD : pe2_Phi '' A = (unitDisc ∩ {0}ᶜ) ∩ pe2_psi ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨pe2_Phi_mem_unitDisc (hA0 u hu), pe2_Phi_ne_zero (hA0 u hu)⟩, ?_⟩
      show pe2_psi (pe2_Phi u) ∈ A
      rw [pe2_psi_Phi (hA0 u hu)]
      exact hu
    · rintro ⟨⟨hzD, hz0⟩, hzA⟩
      exact ⟨pe2_psi z, hzA, pe2_Phi_psi hz0 (mem_ball_zero_iff.1 hzD)⟩
  have hBD : pe2_Phi '' B ∪ {0} = ((unitDisc ∩ {0}ᶜ) ∩ pe2_psi ⁻¹' B) ∪ ball 0 (1 / (1 + R)) := by
    ext z
    constructor
    · rintro (⟨u, hu, rfl⟩ | hz)
      · refine Or.inl ⟨⟨pe2_Phi_mem_unitDisc (hB0 u hu), pe2_Phi_ne_zero (hB0 u hu)⟩, ?_⟩
        show pe2_psi (pe2_Phi u) ∈ B
        rw [pe2_psi_Phi (hB0 u hu)]
        exact hu
      · rw [mem_singleton_iff] at hz
        subst hz
        exact Or.inr (mem_ball_self (by positivity))
    · rintro (⟨⟨hzD, hz0⟩, hzB⟩ | hz)
      · exact Or.inl ⟨pe2_psi z, hzB, pe2_Phi_psi hz0 (mem_ball_zero_iff.1 hzD)⟩
      · by_cases hz0 : z = 0
        · exact Or.inr hz0
        · have hzr := mem_ball_zero_iff.1 hz
          have hr1 : 1 / (1 + R) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzr hr1
          refine Or.inl ⟨pe2_psi z, hRB _ ?_, pe2_Phi_psi hz0 hz1⟩
          rw [pe2_norm_psi hz0 hz1]
          have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
          rw [lt_div_iff₀ hn]
          rw [lt_div_iff₀ (by linarith)] at hzr
          linarith
  have hADo : IsOpen (pe2_Phi '' A) := by
    rw [hAD]; exact hpsi_cont.isOpen_inter_preimage hU0o hAo
  have hBDo : IsOpen (pe2_Phi '' B ∪ {0}) := by
    rw [hBD]; exact (hpsi_cont.isOpen_inter_preimage hU0o hBo).union isOpen_ball
  have hADc : IsConnected (pe2_Phi '' A) := hAc.image pe2_Phi (hPhi_cont.mono fun u hu => hA0 u hu)
  have hBDc : IsConnected (pe2_Phi '' B ∪ {0}) := by
    have hc : IsConnected (pe2_Phi '' B) := hBc.image pe2_Phi (hPhi_cont.mono fun u hu => hB0 u hu)
    refine hc.subset_closure subset_union_left (union_subset subset_closure ?_)
    rw [singleton_subset_iff, Metric.mem_closure_iff]
    intro ε hε
    have hε' : 0 < 1 / ε := one_div_pos.2 hε
    have hx : 0 < R + 1 / ε := add_pos_of_nonneg_of_pos hR0 hε'
    have hxB : ((R + 1 / ε : ℝ) : ℂ) ∈ B := by
      apply hRB
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      linarith
    refine ⟨pe2_Phi ((R + 1 / ε : ℝ) : ℂ), ⟨_, hxB, rfl⟩, ?_⟩
    rw [dist_zero_left, pe2_norm_Phi (hB0 _ hxB), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
    have hεx : ε * (R + 1 / ε) = ε * R + 1 := by rw [mul_add, mul_one_div_cancel hε.ne']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_nonneg hε.le hR0]
  -- push forward by `f`
  have hsubAD : pe2_Phi '' A ⊆ unitDisc := by
    rintro _ ⟨u, hu, rfl⟩
    exact pe2_Phi_mem_unitDisc (hA0 u hu)
  have hsubBD : pe2_Phi '' B ∪ {0} ⊆ unitDisc := by
    refine union_subset ?_ (singleton_subset_iff.2 (mem_ball_self one_pos))
    rintro _ ⟨u, hu, rfl⟩
    exact pe2_Phi_mem_unitDisc (hB0 u hu)
  have hopen_img : ∀ U ⊆ unitDisc, IsOpen U → IsOpen (f '' U) := fun U hU hUo =>
    (show IsConformalOnto f U (f '' U) from ⟨hf.1.mono hU, hf.2.1.mono hU, rfl⟩).isOpen hUo
  refine card_connectedComponents_eq_two_of_union (hopen_img _ hsubAD hADo)
    (hopen_img _ hsubBD hBDo) (hADc.image f (hf.1.continuousOn.mono hsubAD))
    (hBDc.image f (hf.1.continuousOn.mono hsubBD)) ?_ ?_
  · -- disjointness
    rw [Set.disjoint_left]
    rintro w ⟨a, ha, rfl⟩ ⟨b, hb, hfab⟩
    have hab : b = a := hf.2.1 (hsubBD hb) (hsubAD ha) hfab
    have hb' : a ∈ pe2_Phi '' B ∪ {0} := hab ▸ hb
    obtain ⟨u, hu, rfl⟩ := ha
    rcases hb' with ⟨v, hv, hvu⟩ | hb0
    · have hvu' := congrArg pe2_psi hvu
      rw [pe2_psi_Phi (hB0 v hv), pe2_psi_Phi (hA0 u hu)] at hvu'
      exact Set.disjoint_left.1 hAB hu (hvu' ▸ hv)
    · exact pe2_Phi_ne_zero (hA0 u hu) hb0
  · -- the union is `Ω ∖ C`
    ext w
    constructor
    · rintro ⟨hwΩ, hwC⟩
      obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf hwΩ
      by_cases hz0 : pe2_ginv f w = 0
      · exact Or.inr ⟨pe2_ginv f w, Or.inr hz0, hfg⟩
      · have hz1 : ‖pe2_ginv f w‖ < 1 := mem_ball_zero_iff.1 hgD
        have hnJ : pe2_psi (pe2_ginv f w) ∉ J := fun h => by
          apply hwC
          rw [← hfg]
          exact (pe2_psi_mem_image_collapseLoop_iff hf hγΩ hf0 hgD hz0).1 h
        have : pe2_psi (pe2_ginv f w) ∈ A ∪ B ∪ J := by rw [huniv]; exact mem_univ _
        rcases this with (hA | hB) | hJ'
        · exact Or.inl ⟨pe2_ginv f w, ⟨_, hA, pe2_Phi_psi hz0 hz1⟩, hfg⟩
        · exact Or.inr ⟨pe2_ginv f w, Or.inl ⟨_, hB, pe2_Phi_psi hz0 hz1⟩, hfg⟩
        · exact absurd hJ' hnJ
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨hf.mapsTo (hsubAD hz), ?_⟩
        obtain ⟨u, hu, rfl⟩ := hz
        intro hC
        have := (pe2_psi_mem_image_collapseLoop_iff hf hγΩ hf0 (pe2_Phi_mem_unitDisc (hA0 u hu))
          (pe2_Phi_ne_zero (hA0 u hu))).2 hC
        rw [pe2_psi_Phi (hA0 u hu)] at this
        exact Set.disjoint_left.1 hAJ hu this
      · refine ⟨hf.mapsTo (hsubBD hz), ?_⟩
        rcases hz with ⟨u, hu, rfl⟩ | hz0
        · intro hC
          have := (pe2_psi_mem_image_collapseLoop_iff hf hγΩ hf0 (pe2_Phi_mem_unitDisc (hB0 u hu))
            (pe2_Phi_ne_zero (hB0 u hu))).2 hC
          rw [pe2_psi_Phi (hB0 u hu)] at this
          exact Set.disjoint_left.1 hBJ hu this
        · rw [mem_singleton_iff] at hz0
          rw [hz0]
          exact hf0

/-- **A point of `Ω` off the crosscut** (no invariance of domain): if `Ω ⊆ γ(0,1)`, then
`∂Ω ⊆ {γ 0, γ 1}`, and the connected set `ℂ ∖ {γ 0, γ 1}` would be split by `Ω` and
`ℂ ∖ closure Ω` (the latter nonempty since `Ω` is bounded). -/
theorem pe2_exists_mem_diff_image {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (hne : Ω.Nonempty) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγΩ : γ '' Ioo 0 1 ⊆ Ω)
    (h0 : γ 0 ∉ Ω) (h1 : γ 1 ∉ Ω) : ∃ w ∈ Ω, w ∉ γ '' Ioo 0 1 := by
  by_contra hcon
  push Not at hcon
  set P : Set ℂ := {γ 0, γ 1} with hP
  have hK : closure Ω ⊆ γ '' Icc 0 1 :=
    (isCompact_Icc.image_of_continuousOn hγc).isClosed.closure_subset_iff.2
      (fun w hw => image_mono Ioo_subset_Icc_self (hcon w hw))
  have hcl : ∀ x, x ∉ P → x ∈ closure Ω → x ∈ Ω := by
    intro x hxP hx
    obtain ⟨t, ht, rfl⟩ := hK hx
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact absurd (mem_insert _ _) hxP
    · rcases eq_or_lt_of_le ht.2 with h' | h'
      · subst h'
        exact absurd (mem_insert_of_mem _ (mem_singleton _)) hxP
      · exact hγΩ ⟨t, ⟨h, h'⟩, rfl⟩
  have hconn : IsPreconnected Pᶜ :=
    ((((countable_singleton _).insert _) : P.Countable).isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two)).isPreconnected
  obtain ⟨w, hw⟩ := hne
  have hwP : w ∉ P := by
    rintro (h | h)
    · exact h0 (h ▸ hw)
    · exact h1 ((mem_singleton_iff.1 h) ▸ hw)
  obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1
    (hΩ.closure.union (Set.toFinite P).isBounded)
  have hx : ((|R| + 1 : ℝ) : ℂ) ∉ closure Ω ∪ P := fun h => by
    have := mem_closedBall_zero_iff.1 (hR h)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  rcases isPreconnected_iff_subset_of_disjoint.1 hconn Ω (closure Ω)ᶜ hΩo
      isClosed_closure.isOpen_compl
      (fun y hy => by
        by_cases hyΩ : y ∈ closure Ω
        · exact Or.inl (hcl y hy hyΩ)
        · exact Or.inr hyΩ)
      (by
        rw [eq_empty_iff_forall_notMem]
        rintro y ⟨-, hyΩ, hycl⟩
        exact hycl (subset_closure hyΩ)) with h | h
  · exact hx (Or.inl (subset_closure (h fun hxP => hx (Or.inr hxP))))
  · exact h hwP (subset_closure hw)

/-- A crosscut of a bounded simply connected domain separates it into exactly two components.

Proof (s21r, 2026-09-27): collapse `∂Δ` to a point.  A point of `Ω ∖ C` exists without invariance of domain
(`pe2_exists_mem_diff_image`), and a disc automorphism moves its preimage to `0`, so that `f 0 ∉ C`.  Then
`ψ(z) = ((1 - |z|)/|z|²) z` turns `f⁻¹(C)` into a Jordan curve through `0` using only properness (`f(closedBall 0 r)`
is a compact subset of `Ω`), and the Jordan curve theorem splits the plane into a bounded and an unbounded piece;
`f ∘ ψ⁻¹` maps the bounded piece onto one component of `Ω ∖ C` and the unbounded piece onto the other one minus
`f 0`.  No boundary behaviour of `f⁻¹ ∘ γ` (Pommerenke Prop. 2.14) and no invariance of domain is needed.  Moved
here from `Lemmas/Caratheodory.lean` with the other open prime-end statements. -/
theorem crosscut_separates {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : Set ℂ} (hC : IsCrosscut Ω C) :
    Nat.card (ConnectedComponents ↥(Ω \ C)) = 2 := by
  obtain ⟨γ, hγc, hγi, rfl, hCΩ, h0, h1⟩ := hC
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have h0' : γ 0 ∉ Ω := by
    have h := h0
    rw [hΩo.frontier_eq] at h
    exact h.2
  have h1' : γ 1 ∉ Ω := by
    have h := h1
    rw [hΩo.frontier_eq] at h
    exact h.2
  have hne : Ω.Nonempty := ⟨f 0, hf.mapsTo (mem_ball_self one_pos)⟩
  obtain ⟨w₀, hw₀Ω, hw₀C⟩ := pe2_exists_mem_diff_image hΩ hΩo hne hγc hCΩ h0' h1'
  obtain ⟨ha, hfa⟩ := pe2_ginv_mem hf hw₀Ω
  have ha' : ‖-pe2_ginv f w₀‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.1 ha
  have hf₁ : IsConformalOnto (f ∘ blaschke (-pe2_ginv f w₀)) unitDisc Ω :=
    hf.comp (isConformalOnto_blaschke ha')
  refine pe2_card_eq_two_of_zero hf₁ hγc hγi hCΩ h0' h1' ?_
  rw [Function.comp_apply, blaschke_neg_zero, hfa]
  exact hw₀C

/-! ### The proof of `locallyConnectedSpace_frontier_iff` (s21r, 2026-09-27): a σ-chain of circle arcs

(⇒) is `pe6_impression_subsingleton_of_lc`: clause (ii′) of local connectivity (`pe1_ii_of_lc`) at a limit point of
the crosscut ends.  (⇐) is `pe6_lc_of_forall_subsingleton`: if `∂Ω` is not locally connected, some cluster set
`clusterSet f unitDisc ξ` has two points (`locallyConnected_iff_clusterSet_subsingleton`, used in its easy direction:
point cluster sets ⇒ continuous extension ⇒ `∂Ω` a curve ⇒ locally connected), and the σ-chain
`Cₙ = f(Δ ∩ sphere ξ rₙ)` along Wolff radii (the construction in the proof of Pommerenke Thm 2.15) is a null-chain
whose impression contains that cluster set (the first inclusion in the proof of Pommerenke Thm 2.16).  The radii
avoid the null sets of radii at which an arc end value equals one of the previous two end values (Jensen–Fatou,
Stage A), so consecutive closures are disjoint; Pommerenke instead modifies the crosscuts near coinciding ends.
Book: Pommerenke Thm 2.1 and Cor 2.17 (ii); null-chains and impressions as in §2.4–§2.5. -/

/-! ### Stage 0: arcs of circles about a boundary point -/

/-- The closure of `γ '' (0,1)` is `γ '' [0,1]` when `γ` is continuous on `[0,1]`. -/
theorem pe6_closure_image_Ioo {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) :
    closure (γ '' Ioo 0 1) = γ '' Icc 0 1 := by
  have hcl : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  apply Subset.antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) (isCompact_Icc.image_of_continuousOn hγ).isClosed
  · have hγ' : ContinuousOn γ (closure (Ioo (0 : ℝ) 1)) := by
      rw [hcl]
      exact hγ
    rw [← hcl]
    exact hγ'.image_closure

/-- The point `(1 - r) ξ` lies on the arc `Δ ∩ sphere ξ r` (`‖ξ‖ = 1`, `0 < r < 1`). -/
theorem pe6_mem_arc {ξ : ℂ} (hξ : ‖ξ‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((1 - r : ℝ) : ℂ) * ξ ∈ unitDisc ∩ sphere ξ r := by
  constructor
  · rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hξ,
      mul_one]
    linarith
  · have h : ((1 - r : ℝ) : ℂ) * ξ - ξ = ((-r : ℝ) : ℂ) * ξ := by
      push_cast
      ring
    rw [mem_sphere, dist_eq_norm, h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr0, hξ,
      mul_one]

/-- Images under an injective `f` of the arcs of two different circles about `ξ` are disjoint. -/
theorem pe6_disjoint_image_arc {f : ℂ → ℂ} (hf : InjOn f unitDisc) {ξ : ℂ} {r r' : ℝ} (h : r ≠ r') :
    Disjoint (f '' (unitDisc ∩ sphere ξ r)) (f '' (unitDisc ∩ sphere ξ r')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  have hwz' : w = z := hf hw.1 hz.1 hwz
  subst hwz'
  exact h ((mem_sphere.1 hz.2).symm.trans (mem_sphere.1 hw.2))

/-- **A middle circle separates.**  For `r₂ < r₁ < r₀`, a point of `f(Δ ∩ sphere ξ r₀)` and a point of
`f(Δ ∩ sphere ξ r₂)` lie in different components of `Ω ∖ f(Δ ∩ sphere ξ r₁)`: pulled back by `f⁻¹`, a connected
set containing both would meet `sphere ξ r₁` (intermediate value theorem for `dist · ξ`). -/
theorem pe6_connectedComponentIn_ne {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    {r₀ r₁ r₂ : ℝ} (h21 : r₂ < r₁) (h10 : r₁ < r₀) {x y : ℂ} (hx : x ∈ f '' (unitDisc ∩ sphere ξ r₀))
    (hy : y ∈ f '' (unitDisc ∩ sphere ξ r₂)) :
    connectedComponentIn (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) x ≠
      connectedComponentIn (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) y := by
  intro hxy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have huF : f u ∈ Ω \ f '' (unitDisc ∩ sphere ξ r₁) :=
    ⟨hf.mapsTo hu.1, Set.disjoint_left.1 (pe6_disjoint_image_arc hf.2.1 h10.ne') ⟨u, hu, rfl⟩⟩
  have hvF : f v ∈ Ω \ f '' (unitDisc ∩ sphere ξ r₁) :=
    ⟨hf.mapsTo hv.1, Set.disjoint_left.1 (pe6_disjoint_image_arc hf.2.1 h21.ne) ⟨v, hv, rfl⟩⟩
  have huK : f u ∈ connectedComponentIn (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) (f u) :=
    mem_connectedComponentIn huF
  have hvK : f v ∈ connectedComponentIn (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) (f u) := by
    rw [hxy]
    exact mem_connectedComponentIn hvF
  have hKF := connectedComponentIn_subset (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) (f u)
  have hgc : ContinuousOn (Function.invFunOn f unitDisc) Ω := (hf.symm isOpen_ball).1.continuousOn
  have hgK : IsPreconnected (Function.invFunOn f unitDisc ''
      connectedComponentIn (Ω \ f '' (unitDisc ∩ sphere ξ r₁)) (f u)) :=
    isPreconnected_connectedComponentIn.image _ (hgc.mono fun z hz => (hKF hz).1)
  have hgu : Function.invFunOn f unitDisc (f u) = u := hf.2.1.leftInvOn_invFunOn hu.1
  have hgv : Function.invFunOn f unitDisc (f v) = v := hf.2.1.leftInvOn_invFunOn hv.1
  have hIcc := hgK.intermediate_value (f := fun z => dist z ξ) ⟨f v, hvK, hgv⟩ ⟨f u, huK, hgu⟩
    (continuous_id.dist continuous_const).continuousOn
  have hr₁ : r₁ ∈ Icc (dist v ξ) (dist u ξ) := by
    rw [mem_sphere.1 hv.2, mem_sphere.1 hu.2]
    exact ⟨h21.le, h10.le⟩
  obtain ⟨_, ⟨z, hzK, rfl⟩, hz⟩ := hIcc hr₁
  have hzF := hKF hzK
  have hzΩ : z ∈ f '' unitDisc := by
    rw [hf.2.2]
    exact hzF.1
  exact hzF.2 ⟨Function.invFunOn f unitDisc z, ⟨Function.invFunOn_mem hzΩ, mem_sphere.2 hz⟩,
    Function.invFunOn_eq hzΩ⟩

/-! ### (⇒): local connectivity gives one-point impressions -/

/-- **(⇒).**  If `∂Ω` is locally connected, every null-chain has at most one impression point.  A subsequence of
crosscut ends converges to `w ∈ ∂Ω`; clause (ii′) at `w` (`pe1_ii_of_lc`) joins every point of `Ω ∖ ball w R` to a
fixed `x₀ ∈ C₀` off the small crosscut `Cₙ ⊆ ball w ρ`, so the end `chainEnd n` (a component other than that of
`x₀`) lies in `ball w R`.  No nesting of the ends is needed. -/
theorem pe6_impression_subsingleton_of_lc {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hlc : LocallyConnectedSpace (frontier Ω)) {C : ℕ → Set ℂ}
    (hC : IsNullChain Ω C) : (chainImpression Ω C).Subsingleton := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩc : IsPreconnected Ω := by
    rw [← hf.2.2]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image f hf.1.continuousOn
  obtain ⟨hcc, -, hsep, hdiam⟩ := hC
  have hend : ∀ n, ∃ e ∈ frontier Ω, e ∈ closure (C n) := by
    intro n
    obtain ⟨γ, hγc, -, hγC, -, h0, -⟩ := hcc n
    refine ⟨γ 0, h0, ?_⟩
    rw [← hγC, pe6_closure_image_Ioo hγc]
    exact ⟨0, left_mem_Icc.2 zero_le_one, rfl⟩
  choose e he hecl using hend
  have hfc : IsCompact (frontier Ω) :=
    hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨w, hw, φ, hφ, hφt⟩ := hfc.tendsto_subseq he
  have hwΩ : w ∉ Ω := by
    rw [hΩo.frontier_eq] at hw
    exact hw.2
  have hCΩ : ∀ n, C n ⊆ Ω := fun n => by
    obtain ⟨_, _, _, _, h, _⟩ := hcc n
    exact h
  obtain ⟨x₀, hx₀⟩ : (C 0).Nonempty := by
    obtain ⟨γ, -, -, hγC, -⟩ := hcc 0
    rw [← hγC]
    exact ⟨γ (1 / 2), 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hx₀Ω : x₀ ∈ Ω := hCΩ 0 hx₀
  have hx₀w : 0 < dist x₀ w := dist_pos.2 fun h => hwΩ (h ▸ hx₀Ω)
  have key : ∀ R, 0 < R → R < dist x₀ w → chainImpression Ω C ⊆ closedBall w R := by
    intro R hR hRx
    obtain ⟨ρ, hρ, hjoin⟩ := pe1_ii_of_lc hΩo hΩc hlc hw hR
    have h1 : ∀ᶠ k in atTop, 1 ≤ φ k := hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)
    have h2 : ∀ᶠ k in atTop, Metric.diam (C (φ k)) < ρ / 2 :=
      hφ.tendsto_atTop.eventually (hdiam.eventually (Iio_mem_nhds (by positivity)))
    have h3 : ∀ᶠ k in atTop, dist (e (φ k)) w < ρ / 2 :=
      hφt.eventually (Metric.ball_mem_nhds w (by positivity))
    obtain ⟨k, hk1, hk2, hk3⟩ := (h1.and (h2.and h3)).exists
    have hCn : C (φ k) ⊆ ball w ρ := by
      intro y hy
      have hb : Bornology.IsBounded (C (φ k)) := hΩ.subset (hCΩ (φ k))
      have hye : dist y (e (φ k)) ≤ Metric.diam (C (φ k)) := by
        rw [← Metric.diam_closure]
        exact Metric.dist_le_diam_of_mem hb.closure (subset_closure hy) (hecl (φ k))
      rw [mem_ball]
      calc dist y w ≤ dist y (e (φ k)) + dist (e (φ k)) w := dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := by linarith
        _ = ρ := by ring
    have hEnd : chainEnd Ω C (φ k) ⊆ ball w R := by
      intro p hp
      simp only [chainEnd, mem_iUnion] at hp
      obtain ⟨y, hy, hpy⟩ := hp
      by_contra hpR
      have hpF : p ∈ Ω \ C (φ k) := connectedComponentIn_subset _ _ hpy
      have hx₀R : x₀ ∈ Ω \ ball w R := by
        refine ⟨hx₀Ω, fun h => ?_⟩
        rw [mem_ball] at h
        linarith
      obtain ⟨γ, hγ⟩ := hjoin p ⟨hpF.1, hpR⟩ x₀ hx₀R
      have hγF : ∀ t, γ t ∈ Ω \ C (φ k) := fun t => ⟨(hγ t).1, fun h => (hγ t).2 (hCn h)⟩
      have hrange : range γ ⊆ connectedComponentIn (Ω \ C (φ k)) p :=
        (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn ⟨0, γ.source⟩
          (range_subset_iff.2 hγF)
      have hx₀p : x₀ ∈ connectedComponentIn (Ω \ C (φ k)) p := hrange ⟨1, γ.target⟩
      apply (hsep (φ k) hk1).2 x₀ hx₀ y hy
      rw [← connectedComponentIn_eq hx₀p, connectedComponentIn_eq hpy]
    calc chainImpression Ω C ⊆ closure (chainEnd Ω C (φ k)) := iInter_subset _ (φ k)
      _ ⊆ closure (ball w R) := closure_mono hEnd
      _ ⊆ closedBall w R := closure_ball_subset_closedBall
  intro a ha b hb
  by_contra hne
  have hd : 0 < dist a b := dist_pos.2 hne
  set R : ℝ := min (dist a b / 4) (dist x₀ w / 2) with hRdef
  have hR0 : 0 < R := lt_min (by positivity) (by positivity)
  have hRx : R < dist x₀ w := (min_le_right _ _).trans_lt (by linarith)
  have ha' := mem_closedBall.1 (key R hR0 hRx ha)
  have hb' := mem_closedBall.1 (key R hR0 hRx hb)
  have hRd : R ≤ dist a b / 4 := min_le_left _ _
  have htri := dist_triangle_right a b w
  linarith

/-! ### Stage A: the Jensen–Fatou null set of bad radii -/

/-- The point `s ξ e^{-iσθ}` of the circle `|z| = s` (for `‖ξ‖ = 1`; `σ = ±1` selects the orientation). -/
def pe6_circlePt (ξ : ℂ) (σ s θ : ℝ) : ℂ := (s : ℂ) * ξ * Complex.exp (((-(σ * θ) : ℝ) : ℂ) * I)

/-- The radii `r ∈ (0,1)` at which `f` tends to `a` at an end of the arc `Δ ∩ sphere ξ r`; the ends of the arc are
the points `p` with `‖p‖ = 1` and `‖p - ξ‖ = r`. -/
def pe6_badRadii (f : ℂ → ℂ) (ξ a : ℂ) : Set ℝ :=
  {r | r ∈ Ioo 0 1 ∧ ∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = r ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ r] p) (𝓝 a)}

/-- **Jensen on a circle, zero-free, `lintegral` form.**  If `g` is holomorphic and zero-free on `Δ` with
`‖g‖ ≤ M` there, then for `0 < s < 1` the nonnegative function `log M - log ‖g‖` integrates to at most
`2π (log M - log ‖g 0‖)` over the circle `|z| = s`, parametrized by `θ ↦ s ξ e^{-iσθ}`, `θ ∈ (-π, π]`, `σ = ±1`.
The point is `circleMap 0 s (arg ξ - σθ)`; Mathlib's zero-free Jensen formula
(`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`) gives the mean `log ‖g 0‖` over `[0, 2π]`; a shift (and, for
`σ = 1`, a reflection) of the `2π`-periodic integrand moves the period to `(-π, π]`; and the integrand is continuous
and nonnegative, so the `lintegral` is `ofReal` of the interval integral.  Equality holds. -/
theorem pe6_lintegral_log_circlePt_le {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hg0 : ∀ z ∈ unitDisc, g z ≠ 0) {M : ℝ} (hM : ∀ z ∈ unitDisc, ‖g z‖ ≤ M) {ξ : ℂ} (hξ : ‖ξ‖ = 1)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫⁻ θ in Ioc (-π) π, ENNReal.ofReal (Real.log M - Real.log ‖g (pe6_circlePt ξ σ s θ)‖) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
  have hξexp : Complex.exp ((Complex.arg ξ : ℂ) * I) = ξ := by
    have h := Complex.norm_mul_exp_arg_mul_I ξ
    rwa [hξ, Complex.ofReal_one, one_mul] at h
  -- the parametrized point is `circleMap 0 s (arg ξ - σθ)`
  have hpt : ∀ θ : ℝ, pe6_circlePt ξ σ s θ = circleMap 0 s (Complex.arg ξ - σ * θ) := by
    intro θ
    rw [circleMap_zero, pe6_circlePt]
    conv_lhs => rw [← hξexp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hmem : ∀ t : ℝ, circleMap 0 s t ∈ unitDisc := by
    intro t
    rw [unitDisc, mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hs0]
    exact hs1
  have hne : ∀ t : ℝ, ‖g (circleMap 0 s t)‖ ≠ 0 := fun t => norm_ne_zero_iff.2 (hg0 _ (hmem t))
  have hgc : Continuous fun t : ℝ => g (circleMap 0 s t) :=
    hg.continuousOn.comp_continuous (continuous_circleMap 0 s) hmem
  -- Jensen: the mean of `log ‖g‖` over `|z| = s` is `log ‖g 0‖`
  have hJ : ∫ t in (0 : ℝ)..2 * π, Real.log ‖g (circleMap 0 s t)‖ = 2 * π * Real.log ‖g 0‖ := by
    have hsub : closedBall (0 : ℂ) |s| ⊆ unitDisc := by
      rw [abs_of_pos hs0]
      exact closedBall_subset_ball hs1
    have hana : AnalyticOnNhd ℂ g (closedBall 0 |s|) := (hg.analyticOnNhd isOpen_ball).mono hsub
    have h := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hana fun u hu => hg0 u (hsub hu)
    rw [Real.circleAverage_def, smul_eq_mul] at h
    have h2π : (2 * π) ≠ 0 := by positivity
    rw [← h, ← mul_assoc, mul_inv_cancel₀ h2π, one_mul]
  -- the shifted (and, for `σ = 1`, reflected) period
  have hper : Function.Periodic (fun t : ℝ => Real.log ‖g (circleMap 0 s t)‖) (2 * π) := fun t => by
    simp only [periodic_circleMap 0 s t]
  have hshift : ∫ θ in (-π)..π, Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖ =
      2 * π * Real.log ‖g 0‖ := by
    rw [← hJ]
    rcases hσ with rfl | rfl
    · simp only [one_mul]
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => Real.log ‖g (circleMap 0 s t)‖) (Complex.arg ξ),
        show Complex.arg ξ - -π = Complex.arg ξ - π + 2 * π by ring,
        hper.intervalIntegral_add_eq (Complex.arg ξ - π) 0, zero_add]
    · simp only [neg_one_mul, sub_neg_eq_add]
      rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => Real.log ‖g (circleMap 0 s t)‖) (Complex.arg ξ),
        show Complex.arg ξ + π = Complex.arg ξ + -π + 2 * π by ring,
        hper.intervalIntegral_add_eq (Complex.arg ξ + -π) 0, zero_add]
  have hlogc : Continuous fun θ : ℝ => Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖ :=
    (hgc.comp (continuous_const.sub (continuous_const.mul continuous_id))).norm.log fun θ => hne _
  have hcont : Continuous fun θ : ℝ => Real.log M - Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖ :=
    continuous_const.sub hlogc
  have hnn : ∀ θ : ℝ, 0 ≤ Real.log M - Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖ := by
    intro θ
    have hpos : 0 < ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖ := norm_pos_iff.2 (hg0 _ (hmem _))
    exact sub_nonneg.2 (Real.log_le_log hpos (hM _ (hmem _)))
  have hInt : IntegrableOn (fun θ : ℝ => Real.log M - Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖)
      (Ioc (-π) π) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  refine le_of_eq ?_
  calc ∫⁻ θ in Ioc (-π) π, ENNReal.ofReal (Real.log M - Real.log ‖g (pe6_circlePt ξ σ s θ)‖)
      = ∫⁻ θ in Ioc (-π) π,
          ENNReal.ofReal (Real.log M - Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖) := by
        simp only [hpt]
    _ = ENNReal.ofReal (∫ θ in Ioc (-π) π,
          (Real.log M - Real.log ‖g (circleMap 0 s (Complex.arg ξ - σ * θ))‖)) :=
        (ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hnn)).symm
    _ = ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
        congr 1
        rw [← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_sub intervalIntegrable_const
          (hlogc.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, hshift]
        ring

/-- **The foliation Jacobian.**  For `0 < r₁` and `1 - r₁ < s < 1`, the angle `φ(r) = arccos ((1 + s² - r²)/(2s))`
of the points of `|z| = s` at distance `r` from `1` satisfies `∫_{(r₁,1)} G (φ r) dr ≤ (1/r₁) ∫_{(0,π)} G` for
every `G : ℝ → ℝ≥0∞`.  On `(r₁, 1)` (empty unless `r₁ < 1`) the argument `x(r)` lies in `(-1, 1)`, `φ` is strictly
increasing with `φ'(r) = r / (s √(1 - x²)) ≥ r > r₁`, and `φ '' (r₁, 1) ⊆ (0, π)`; then the one-dimensional change
of variables `lintegral_image_eq_lintegral_abs_deriv_mul` (no measurability of `G` needed). -/
theorem pe6_lintegral_comp_arccos_le {r₁ s : ℝ} (hr₁ : 0 < r₁) (hs : 1 - r₁ < s) (hs1 : s < 1)
    (G : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioo r₁ 1, G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) ≤
      ENNReal.ofReal (1 / r₁) * ∫⁻ θ in Ioo 0 π, G θ := by
  rcases le_or_gt 1 r₁ with h1 | h1
  · rw [Ioo_eq_empty (not_lt.2 h1), Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  have hs0 : 0 < s := by linarith
  have h2s : 0 < 2 * s := by positivity
  have hxmem : ∀ r ∈ Ioo r₁ 1, -1 < (1 + s ^ 2 - r ^ 2) / (2 * s) ∧ (1 + s ^ 2 - r ^ 2) / (2 * s) < 1 := by
    intro r hr
    have hr0 : 0 < r := hr₁.trans hr.1
    constructor
    · rw [lt_div_iff₀ h2s]
      nlinarith [hr.2]
    · rw [div_lt_one h2s]
      have h3 : 0 < r - (1 - s) := by linarith [hr.1]
      nlinarith
  have hderiv : ∀ r ∈ Ioo r₁ 1, HasDerivAt (fun r : ℝ => Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))
      (1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)) r := by
    intro r hr
    obtain ⟨hx1, hx2⟩ := hxmem r hr
    have hxd : HasDerivAt (fun r : ℝ => (1 + s ^ 2 - r ^ 2) / (2 * s)) (-(2 * r) / (2 * s)) r := by
      have h := ((hasDerivAt_pow 2 r).const_sub (1 + s ^ 2)).div_const (2 * s)
      convert h using 1
      push_cast
      ring
    have h := (Real.hasDerivAt_arccos hx1.ne' hx2.ne).comp r hxd
    have heq : -(1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2)) * (-(2 * r) / (2 * s)) =
        1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s) := by
      rw [neg_div, neg_mul_neg, mul_div_mul_left r s two_ne_zero]
    exact h.congr_deriv heq
  have hbound : ∀ r ∈ Ioo r₁ 1, r₁ ≤ |1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)| := by
    intro r hr
    obtain ⟨hx1, hx2⟩ := hxmem r hr
    have hr0 : 0 < r := hr₁.trans hr.1
    have hq : 0 < 1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2 := by nlinarith
    have hsq0 : 0 < √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) := Real.sqrt_pos.2 hq
    have hsq1 : √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) ≤ 1 :=
      Real.sqrt_le_one.2 (by nlinarith)
    have hA : 1 ≤ 1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) := one_le_one_div hsq0 hsq1
    have hB : r ≤ r / s := le_div_self hr0.le hs0 hs1.le
    rw [abs_of_pos (by positivity)]
    calc r₁ ≤ r := hr.1.le
      _ ≤ r / s := hB
      _ = 1 * (r / s) := (one_mul _).symm
      _ ≤ 1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
  have hmono : StrictMonoOn (fun r : ℝ => Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) (Ioo r₁ 1) := by
    intro r hr r' hr' hrr'
    have hr0 : 0 < r := hr₁.trans hr.1
    have hlt : (1 + s ^ 2 - r' ^ 2) / (2 * s) < (1 + s ^ 2 - r ^ 2) / (2 * s) := by
      apply div_lt_div_of_pos_right _ h2s
      nlinarith
    exact Real.strictAntiOn_arccos ⟨(hxmem r' hr').1.le, (hxmem r' hr').2.le⟩
      ⟨(hxmem r hr).1.le, (hxmem r hr).2.le⟩ hlt
  have himg : (fun r : ℝ => Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) '' Ioo r₁ 1 ⊆ Ioo 0 π := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨Real.arccos_pos.2 (hxmem r hr).2, Real.arccos_lt_pi.2 (hxmem r hr).1⟩
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun r hr => (hderiv r hr).hasDerivWithinAt) hmono.injOn G
  calc ∫⁻ r in Ioo r₁ 1, G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))
      ≤ ∫⁻ r in Ioo r₁ 1, ENNReal.ofReal (1 / r₁) *
          (ENNReal.ofReal |1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)| *
            G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / r₁) *
            ENNReal.ofReal |1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)| := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hr₁, one_mul]
          exact hbound r hr
        calc G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))
            = 1 * G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) := (one_mul _).symm
          _ ≤ (ENNReal.ofReal (1 / r₁) *
              ENNReal.ofReal |1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)|) *
                G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) := mul_le_mul_left h1 _
          _ = _ := mul_assoc _ _ _
    _ = ENNReal.ofReal (1 / r₁) * ∫⁻ r in Ioo r₁ 1,
          ENNReal.ofReal |1 / √(1 - ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2) * (r / s)| *
            G (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (1 / r₁) *
          ∫⁻ θ in (fun r : ℝ => Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) '' Ioo r₁ 1, G θ := by
        rw [hcov]
    _ ≤ ENNReal.ofReal (1 / r₁) * ∫⁻ θ in Ioo 0 π, G θ := by
        gcongr

/-- **The foliation reaches the ends of the arc.**  Let `‖ξ‖ = 1`, `0 < r < 1`, and let `p` be an end of the arc
`Δ ∩ sphere ξ r` (`‖p‖ = 1`, `‖p - ξ‖ = r`).  For one of the two branches `σ = ±1`, the point
`s ↦ s ξ e^{-iσ φ_s(r)}`, `φ_s(r) = arccos ((1 + s² - r²)/(2s))`, runs along the arc for `s ∈ (1 - r, 1)` (modulus
`s`, and `|s e^{-iσφ} - 1|² = 1 + s² - 2s cos φ = r²`) and tends to `p` as `s → 1⁻`: with `q = p ξ̄` one has
`Re q = 1 - r²/2`, `|Im q| = sin (arccos (1 - r²/2))`, and `σ = 1` if `Im q ≤ 0`, `σ = -1` otherwise. -/
theorem pe6_tendsto_circlePt_arccos {ξ : ℂ} (hξ : ‖ξ‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {p : ℂ}
    (hp : ‖p‖ = 1) (hpr : ‖p - ξ‖ = r) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ Tendsto (fun s : ℝ => pe6_circlePt ξ σ s
      (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))) (𝓝[<] 1) (𝓝[unitDisc ∩ sphere ξ r] p) := by
  -- for `s ∈ (1 - r, 1)` both branches lie on the arc
  have harc : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ s ∈ Ioo (1 - r) 1,
      pe6_circlePt ξ σ s (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) ∈ unitDisc ∩ sphere ξ r := by
    intro σ hσ s hs
    have hs1 : s < 1 := hs.2
    have hs2 : 1 - r < s := hs.1
    have hs0 : 0 < s := by linarith
    have h2s : 0 < 2 * s := by positivity
    have hx1 : -1 ≤ (1 + s ^ 2 - r ^ 2) / (2 * s) := by
      rw [le_div_iff₀ h2s]
      nlinarith
    have hx2 : (1 + s ^ 2 - r ^ 2) / (2 * s) ≤ 1 := by
      rw [div_le_one h2s]
      have h3 : 0 < r - (1 - s) := by linarith
      nlinarith
    have hx' : 2 * s * ((1 + s ^ 2 - r ^ 2) / (2 * s)) = 1 + s ^ 2 - r ^ 2 := mul_div_cancel₀ _ h2s.ne'
    have hcos : Real.cos (-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))) =
        (1 + s ^ 2 - r ^ 2) / (2 * s) := by
      rw [Real.cos_neg]
      rcases hσ with rfl | rfl
      · rw [one_mul, Real.cos_arccos hx1 hx2]
      · rw [neg_one_mul, Real.cos_neg, Real.cos_arccos hx1 hx2]
    have he : ‖Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    constructor
    · rw [unitDisc, mem_ball_zero_iff, pe6_circlePt, norm_mul, norm_mul, he, hξ, Complex.norm_real,
        Real.norm_of_nonneg hs0.le, mul_one, mul_one]
      exact hs1
    · rw [mem_sphere, dist_eq_norm, pe6_circlePt]
      have hfac : (s : ℂ) * ξ * Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I) -
          ξ = ξ * ((s : ℂ) * Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I) -
            1) := by ring
      rw [hfac, norm_mul, hξ, one_mul]
      have hsq : ‖(s : ℂ) * Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I) -
          1‖ ^ 2 = r ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re,
          Complex.one_im]
        have hsc := Real.sin_sq_add_cos_sq (-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))))
        linear_combination s ^ 2 * hsc - 2 * s * hcos - hx'
      calc ‖(s : ℂ) * Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I) - 1‖
          = √(‖(s : ℂ) * Complex.exp (((-(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))) : ℝ) : ℂ) * I) -
              1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = √(r ^ 2) := by rw [hsq]
        _ = r := Real.sqrt_sq hr0.le
  -- the end `p` is `ξ q` with `q = e^{-iσφ₁}`, `φ₁ = arccos (1 - r²/2)`
  have hξc : ξ * (starRingEnd ℂ) ξ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    norm_num
  set q : ℂ := p * (starRingEnd ℂ) ξ with hq
  have hpq : p = ξ * q := by
    rw [hq]
    linear_combination (-p) * hξc
  have hqn : ‖q‖ = 1 := by rw [hq, norm_mul, Complex.norm_conj, hp, hξ, one_mul]
  have hq1 : ‖q - 1‖ = r := by
    have h : q - 1 = (p - ξ) * (starRingEnd ℂ) ξ := by
      rw [hq]
      linear_combination hξc
    rw [h, norm_mul, Complex.norm_conj, hpr, hξ, mul_one]
  have h1 : q.re * q.re + q.im * q.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hqn, one_pow]
  have h2 : (q.re - 1) * (q.re - 1) + q.im * q.im = r ^ 2 := by
    have h := Complex.normSq_apply (q - 1)
    rw [← Complex.sq_norm, hq1] at h
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hre : q.re = 1 - r ^ 2 / 2 := by linear_combination (h1 - h2) / 2
  have hc1 : -1 ≤ 1 - r ^ 2 / 2 := by nlinarith
  have hc2 : 1 - r ^ 2 / 2 ≤ 1 := by nlinarith
  have hsin : Real.sin (Real.arccos (1 - r ^ 2 / 2)) = |q.im| := by
    rw [Real.sin_arccos, ← Real.sqrt_sq_eq_abs]
    congr 1
    rw [← hre]
    linear_combination -1 * h1
  have hcos1 : Real.cos (Real.arccos (1 - r ^ 2 / 2)) = q.re := by
    rw [Real.cos_arccos hc1 hc2, hre]
  have hbranch : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      q = Complex.exp (((-(σ * Real.arccos (1 - r ^ 2 / 2)) : ℝ) : ℂ) * I) := by
    rcases le_or_gt q.im 0 with him | him
    · refine ⟨1, Or.inl rfl, Complex.ext ?_ ?_⟩
      · rw [Complex.exp_ofReal_mul_I_re, one_mul, Real.cos_neg, hcos1]
      · rw [Complex.exp_ofReal_mul_I_im, one_mul, Real.sin_neg, hsin, abs_of_nonpos him, neg_neg]
    · refine ⟨-1, Or.inr rfl, Complex.ext ?_ ?_⟩
      · rw [Complex.exp_ofReal_mul_I_re, neg_one_mul, neg_neg, hcos1]
      · rw [Complex.exp_ofReal_mul_I_im, neg_one_mul, neg_neg, hsin, abs_of_pos him]
  obtain ⟨σ, hσ, hqσ⟩ := hbranch
  refine ⟨σ, hσ, tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩⟩
  · have hx : ContinuousAt (fun s : ℝ => (1 + s ^ 2 - r ^ 2) / (2 * s)) 1 :=
      (((continuous_const.add (continuous_pow 2)).sub continuous_const).continuousAt).div
        ((continuous_const.mul continuous_id).continuousAt) (by norm_num)
    have ht : ContinuousAt (fun s : ℝ => -(σ * Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))) 1 :=
      ((Real.continuous_arccos.continuousAt.comp hx).const_mul σ).neg
    have hcont : ContinuousAt (fun s : ℝ => pe6_circlePt ξ σ s
        (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))) 1 := by
      unfold pe6_circlePt
      exact (Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul
        (Complex.continuous_exp.continuousAt.comp
          ((Complex.continuous_ofReal.continuousAt.comp ht).mul continuousAt_const))
    have hF1 : pe6_circlePt ξ σ 1 (Real.arccos ((1 + 1 ^ 2 - r ^ 2) / (2 * 1))) = p := by
      rw [show (1 + 1 ^ 2 - r ^ 2) / (2 * 1) = 1 - r ^ 2 / 2 by ring, pe6_circlePt, ← hqσ, hpq,
        Complex.ofReal_one, one_mul]
    exact (hcont.tendsto.mono_right (le_of_eq (congrArg 𝓝 hF1))).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show 1 - r < 1 by linarith)] with s hs
    exact harc σ hσ s hs

/-- **Jensen–Fatou along one branch.**  For `a ∉ Ω` and `0 < r₁ < 1`, the radii `r ∈ (r₁, 1)` at which
`f (s ξ e^{-iσ φ_s(r)}) → a` as `s → 1⁻` (`φ_s(r)` as in `pe6_tendsto_circlePt_arccos`) form a null set.

Proof: `g = f - a` is holomorphic and zero-free on `Δ` (`a ∉ Ω = f(Δ)`) and bounded by `M = R + ‖a‖` there (`Ω` is
bounded).  Put `s_k = 1 - r₁/(k+2) ↑ 1` (so `s_k > 1 - r₁`) and
`F_k(r) = ofReal (log M - log ‖g (s_k ξ e^{-iσ φ_{s_k}(r)})‖)`, continuous in `r` (the point has modulus `s_k < 1`
for every `r`).  By `pe6_lintegral_comp_arccos_le` and `pe6_lintegral_log_circlePt_le`,
`∫_{(r₁,1)} F_k ≤ (1/r₁) · 2π (log M - log ‖g 0‖) < ∞` for every `k`, so by Fatou (`lintegral_liminf_le'`)
`liminf_k F_k < ∞` a.e. on `(r₁, 1)`; at a radius of the set, `‖g‖ → 0` along the points, so `F_k → ∞`.  This is the
zero-free (`H^∞`) case of the Riesz uniqueness theorem along the arcs themselves: no angular limits and no
Lindelöf theorem are needed. -/
theorem pe6_volume_branch_eq_zero {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {a : ℂ} (ha : a ∉ Ω) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {r₁ : ℝ} (hr₁0 : 0 < r₁) (hr₁1 : r₁ < 1) :
    volume {r : ℝ | r ∈ Ioo r₁ 1 ∧ Tendsto (fun s : ℝ =>
      f (pe6_circlePt ξ σ s (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))))) (𝓝[<] 1) (𝓝 a)} = 0 := by
  -- `f - a` is holomorphic, zero-free and bounded by `R + ‖a‖` on `Δ`
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hΩ
  have hg : DifferentiableOn ℂ (fun z => f z - a) unitDisc := hf.1.sub_const a
  have hg0 : ∀ z ∈ unitDisc, f z - a ≠ 0 := by
    intro z hz h
    apply ha
    rw [← sub_eq_zero.1 h]
    exact hf.mapsTo hz
  have hgM : ∀ z ∈ unitDisc, ‖f z - a‖ ≤ R + ‖a‖ := by
    intro z hz
    have h1 : ‖f z‖ ≤ R := by simpa using hR (hf.mapsTo hz)
    calc ‖f z - a‖ ≤ ‖f z‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ R + ‖a‖ := by linarith
  have hptD : ∀ c θ : ℝ, 0 < c → c < 1 → pe6_circlePt ξ σ c θ ∈ unitDisc := by
    intro c θ hc0 hc1
    rw [unitDisc, mem_ball_zero_iff, pe6_circlePt, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, hξ,
      Complex.norm_real, Real.norm_of_nonneg hc0.le, mul_one, mul_one]
    exact hc1
  -- the radii `s_k = 1 - r₁/(k+2) ↑ 1`
  obtain ⟨sk, hsk⟩ : ∃ sk : ℕ → ℝ, sk = fun k : ℕ => 1 - r₁ / ((k : ℝ) + 2) := ⟨_, rfl⟩
  have hsk1 : ∀ k, sk k < 1 := fun k => by
    rw [hsk]
    have : 0 < r₁ / ((k : ℝ) + 2) := by positivity
    linarith
  have hskr : ∀ k, 1 - r₁ < sk k := fun k => by
    rw [hsk]
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have : r₁ / ((k : ℝ) + 2) < r₁ := div_lt_self hr₁0 hk
    linarith
  have hsk0 : ∀ k, 0 < sk k := fun k => by linarith [hskr k]
  have hsklim : Tendsto sk atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hsk1⟩
    have h1 : Tendsto (fun k : ℕ => r₁ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    rw [sub_zero] at h2
    rw [hsk]
    exact h2
  -- Fatou's functions `F k r = G k (φ_{s_k}(r))`
  set G : ℕ → ℝ → ℝ≥0∞ := fun k θ =>
    ENNReal.ofReal (Real.log (R + ‖a‖) - Real.log ‖f (pe6_circlePt ξ σ (sk k) θ) - a‖) with hG
  set F : ℕ → ℝ → ℝ≥0∞ := fun k r => G k (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k))) with hF
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    have hpt : Continuous fun r : ℝ =>
        pe6_circlePt ξ σ (sk k) (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k))) := by
      unfold pe6_circlePt
      fun_prop
    have hfpt : Continuous fun r : ℝ =>
        f (pe6_circlePt ξ σ (sk k) (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k)))) :=
      hf.1.continuousOn.comp_continuous hpt fun r => hptD _ _ (hsk0 k) (hsk1 k)
    have hc : Continuous (F k) :=
      ENNReal.continuous_ofReal.comp (continuous_const.sub ((hfpt.sub continuous_const).norm.log
        fun r => norm_ne_zero_iff.2 (hg0 _ (hptD _ _ (hsk0 k) (hsk1 k)))))
    exact hc.measurable
  -- the uniform bound (foliation Jacobian + Jensen)
  have hK : ENNReal.ofReal (1 / r₁) * ENNReal.ofReal (2 * π * (Real.log (R + ‖a‖) - Real.log ‖f 0 - a‖)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound : ∀ k, ∫⁻ r in Ioo r₁ 1, F k r ≤
      ENNReal.ofReal (1 / r₁) * ENNReal.ofReal (2 * π * (Real.log (R + ‖a‖) - Real.log ‖f 0 - a‖)) := by
    intro k
    have hJ := pe6_lintegral_log_circlePt_le (g := fun z => f z - a) hg hg0 hgM hξ hσ (hsk0 k) (hsk1 k)
    have hsubset : Ioo 0 π ⊆ Ioc (-π) π := fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
    calc ∫⁻ r in Ioo r₁ 1, F k r ≤ ENNReal.ofReal (1 / r₁) * ∫⁻ θ in Ioo 0 π, G k θ :=
          pe6_lintegral_comp_arccos_le hr₁0 (hskr k) (hsk1 k) (G k)
      _ ≤ ENNReal.ofReal (1 / r₁) * ∫⁻ θ in Ioc (-π) π, G k θ :=
          mul_le_mul_right (lintegral_mono_set hsubset) _
      _ ≤ _ := mul_le_mul_right hJ _
  -- Fatou: `liminf F_k < ∞` almost everywhere on `(r₁, 1)`
  have hae : ∀ᵐ r ∂(volume.restrict (Ioo r₁ 1)), liminf (fun k => F k r) atTop < ⊤ := by
    have h1 := lintegral_liminf_le' (μ := volume.restrict (Ioo r₁ 1)) (u := atTop)
      (fun k => (hFm k).aemeasurable)
    have h2 : liminf (fun k => ∫⁻ r in Ioo r₁ 1, F k r) atTop ≤
        ENNReal.ofReal (1 / r₁) * ENNReal.ofReal (2 * π * (Real.log (R + ‖a‖) - Real.log ‖f 0 - a‖)) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hbound)
    exact ae_lt_top' (Measurable.liminf hFm).aemeasurable (ne_top_of_le_ne_top hK (h1.trans h2))
  -- at a radius of the set, `F_k → ∞`
  have hsub : {r : ℝ | r ∈ Ioo r₁ 1 ∧ Tendsto (fun s : ℝ =>
      f (pe6_circlePt ξ σ s (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s))))) (𝓝[<] 1) (𝓝 a)} ⊆
      {r | ¬ liminf (fun k => F k r) atTop < ⊤} ∩ Ioo r₁ 1 := by
    rintro r ⟨hr, ht⟩
    refine ⟨?_, hr⟩
    have h1 : Tendsto (fun k => f (pe6_circlePt ξ σ (sk k)
        (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k))))) atTop (𝓝 a) := ht.comp hsklim
    have hpos : ∀ k, 0 < ‖f (pe6_circlePt ξ σ (sk k)
        (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k)))) - a‖ :=
      fun k => norm_pos_iff.2 (hg0 _ (hptD _ _ (hsk0 k) (hsk1 k)))
    have h2 : Tendsto (fun k => ‖f (pe6_circlePt ξ σ (sk k)
        (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k)))) - a‖) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hpos⟩
      have h := (h1.sub_const a).norm
      rwa [sub_self, norm_zero] at h
    have h4 : Tendsto (fun k => Real.log (R + ‖a‖) + -Real.log ‖f (pe6_circlePt ξ σ (sk k)
        (Real.arccos ((1 + sk k ^ 2 - r ^ 2) / (2 * sk k)))) - a‖) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h2))
    have h5 : Tendsto (fun k => F k r) atTop (𝓝 ⊤) := by
      refine (ENNReal.tendsto_ofReal_atTop.comp h4).congr fun k => ?_
      simp only [hF, hG, Function.comp_apply, sub_eq_add_neg]
    show ¬ liminf (fun k => F k r) atTop < ⊤
    rw [h5.liminf_eq]
    exact lt_irrefl _
  have hnull : volume ({r | ¬ liminf (fun k => F k r) atTop < ⊤} ∩ Ioo r₁ 1) = 0 := by
    rw [← Measure.restrict_apply' measurableSet_Ioo]
    exact measure_eq_zero_iff_ae_notMem.2 (hae.mono fun r hr h => h hr)
  exact measure_mono_null hsub hnull

/-- **The bad radii are null.**  For `a ∉ Ω` the radii at which `f` tends to `a` at an end of the arc
`Δ ∩ sphere ξ r` form a null set: each such end is reached by one foliation branch (`pe6_tendsto_circlePt_arccos`),
and each branch is null on `(1/(m+2), 1)` (`pe6_volume_branch_eq_zero`). -/
theorem pe6_volume_badRadii_eq_zero {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {a : ℂ} (ha : a ∉ Ω) :
    volume (pe6_badRadii f ξ a) = 0 := by
  have hB0 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ m : ℕ, volume {r : ℝ | r ∈ Ioo (1 / ((m : ℝ) + 2)) 1 ∧
      Tendsto (fun s : ℝ => f (pe6_circlePt ξ σ s (Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)))))
        (𝓝[<] 1) (𝓝 a)} = 0 := by
    intro σ hσ m
    have hm1 : 1 / ((m : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact pe6_volume_branch_eq_zero hΩ hf hξ ha hσ (by positivity) hm1
  refine measure_mono_null ?_ (measure_iUnion_null fun m : ℕ =>
    measure_union_null (hB0 1 (Or.inl rfl) m) (hB0 (-1) (Or.inr rfl) m))
  rintro r ⟨hr, p, hp, hpr, ht⟩
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr.1
  have hm2 : 1 / ((m : ℝ) + 2) < r :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hm
  obtain ⟨σ, hσ, hw⟩ := pe6_tendsto_circlePt_arccos hξ hr.1 hr.2 hp hpr
  refine mem_iUnion.2 ⟨m, ?_⟩
  rcases hσ with rfl | rfl
  · exact Or.inl ⟨⟨hm2, hr.2⟩, ht.comp hw⟩
  · exact Or.inr ⟨⟨hm2, hr.2⟩, ht.comp hw⟩

/-! ### Stage B: the crosscuts, Wolff radii off a null set, and the choice of radii -/

/-- **The arc image is a crosscut with named ends.**  For `0 < r < 1` with finite arc length, `f(Δ ∩ sphere ξ r)`
is `γ '' (0,1)` for some `γ` continuous on `[0,1]` and injective on `(0,1)`, whose ends `γ 0`, `γ 1` lie in `∂Ω`
and are the limits of `f` at the two ends `p` (`‖p‖ = 1`, `‖p - ξ‖ = r`) of the arc.

Proof: the parametrization built inside `exists_ends_of_circleArc_image` (`Lemmas/CaratheodoryJordan.lean`), whose
statement keeps the ends existential, copied here.  With `c s = circleMap ξ r (arg ξ + π + s)` and
`β₀ = arccos (r/2)`, the limits `a`, `b` of `f` at the ends `c β₀`, `c (-β₀)` of the arc exist
(`exists_tendsto_circleArc_end_of_arcLength_ne_top`) and lie in `∂Ω` (`tendsto_boundary_of_isConformalOnto`), and
`γ u = f (c (β₀ - 2β₀u))` on `(0,1)`, `γ 0 = a`, `γ 1 = b`. -/
theorem pe6_arc_crosscut {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hlen : arcLength f ξ r ≠ ⊤) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ioo 0 1) ∧
      γ '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ r) ∧ γ 0 ∈ frontier Ω ∧ γ 1 ∈ frontier Ω ∧
      (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = r ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ r] p) (𝓝 (γ 0))) ∧
      (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = r ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ r] p) (𝓝 (γ 1))) := by
  have hfdiff := hf.1
  have hfinj := hf.2.1
  have hfrange := hf.2.2
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔo
  set α := Complex.arg ξ with hα_def
  set β₀ := Real.arccos (r / 2) with hβ₀_def
  have hβ₀0 : 0 < β₀ := Real.arccos_pos.mpr (by linarith)
  have hβ₀π : β₀ < π := Real.arccos_lt_pi.mpr (by linarith)
  have hcosβ₀ : Real.cos β₀ = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  set c : ℝ → ℂ := fun s => circleMap ξ r (α + π + s) with hc_def
  have hc_sphere : ∀ s, c s ∈ sphere ξ r := fun s => circleMap_mem_sphere ξ hr0.le _
  have hc_normsq : ∀ s, ‖c s‖ ^ 2 = 1 - 2 * r * Real.cos s + r ^ 2 :=
    fun s => norm_sq_circleMap_arg_add_pi_add hξ r s
  have hβmem : β₀ ∈ Icc (0 : ℝ) π := ⟨hβ₀0.le, hβ₀π.le⟩
  have hcos_iff_mem : ∀ s ∈ Ioc (-π) π, (c s ∈ unitDisc ↔ s ∈ Ioo (-β₀) β₀) := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg s, abs_le.mpr ⟨by linarith [hs.1], hs.2⟩⟩
    have hkey : Real.cos β₀ < Real.cos |s| ↔ |s| < β₀ :=
      Real.strictAntiOn_cos.lt_iff_gt hβmem habs
    rw [Real.cos_abs] at hkey
    rw [unitDisc, mem_ball_zero_iff, ← abs_of_nonneg (norm_nonneg (c s)),
      ← sq_lt_one_iff_abs_lt_one, hc_normsq]
    constructor
    · intro h1
      have h2 : Real.cos β₀ < Real.cos s := by rw [hcosβ₀]; nlinarith
      exact abs_lt.mp (hkey.mp h2)
    · intro hmem
      have h2 : Real.cos β₀ < Real.cos s := hkey.mpr (abs_lt.mpr hmem)
      rw [hcosβ₀] at h2; nlinarith
  have hIooβ_sub : Ioo (-β₀) β₀ ⊆ Ioc (-π) π := fun s hs =>
    ⟨lt_trans (by linarith) hs.1, le_of_lt (lt_trans hs.2 hβ₀π)⟩
  have hS_eq : unitDisc ∩ sphere ξ r = c '' Ioo (-β₀) β₀ := by
    apply Subset.antisymm
    · rintro w ⟨hw1, hw2⟩
      obtain ⟨s, hs_mem, hcs_eq⟩ := exists_mem_Ioc_circleMap_arg_add_pi_add hr0 hw2
      have hcs_eq' : c s = w := hcs_eq
      exact ⟨s, (hcos_iff_mem s hs_mem).mp (hcs_eq' ▸ hw1), hcs_eq⟩
    · rintro w ⟨s, hs, rfl⟩
      exact ⟨(hcos_iff_mem s (hIooβ_sub hs)).mpr hs, hc_sphere s⟩
  have hc_hasDerivAt : ∀ s : ℝ, HasDerivAt c (circleMap 0 r (α + π + s) * I) s :=
    fun s => (hasDerivAt_circleMap ξ r (α + π + s)).comp_const_add (α + π) s
  have hc_cont : Continuous c :=
    (continuous_circleMap ξ r).comp (continuous_const.add continuous_id)
  have hfc_hasDerivAt : ∀ s ∈ Ioo (-β₀) β₀,
      HasDerivAt (f ∘ c) (deriv f (c s) * (circleMap 0 r (α + π + s) * I)) s := by
    intro s hs
    have hcsmem : c s ∈ unitDisc := (hcos_iff_mem s (hIooβ_sub hs)).mpr hs
    have hf_deriv : HasDerivAt f (deriv f (c s)) (c s) :=
      (hfdiff.differentiableAt (hΔo.mem_nhds hcsmem)).hasDerivAt
    exact hf_deriv.comp s (hc_hasDerivAt s)
  have hc_inj : InjOn c (Icc (-β₀) β₀) := by
    intro s hs t ht hst
    have h1 : |(α + π + s) - (α + π + t)| < 2 * π := by
      have h2 : |s - t| ≤ 2 * β₀ := by
        rw [abs_le]
        constructor <;> [linarith [hs.1, ht.2]; linarith [hs.2, ht.1]]
      calc |(α + π + s) - (α + π + t)| = |s - t| := by congr 1; ring
        _ ≤ 2 * β₀ := h2
        _ < 2 * π := by linarith
    have h2 : α + π + s = α + π + t := eq_of_circleMap_eq hr0.ne' h1 hst
    linarith
  -- the two endpoint limits, via the already-proven C1 theorem
  have hcβ₀_norm : ‖c β₀‖ = 1 := by
    have h1 : ‖c β₀‖ ^ 2 = 1 := by rw [hc_normsq, hcosβ₀]; ring
    have h2 : ‖c β₀‖ = Real.sqrt (‖c β₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, Real.sqrt_one] at h2; exact h2
  have hcβ₀_sphere : ‖c β₀ - ξ‖ = r := by
    have h := hc_sphere β₀; rwa [Metric.mem_sphere, Complex.dist_eq] at h
  obtain ⟨a, ha⟩ := exists_tendsto_circleArc_end_of_arcLength_ne_top hfdiff hξ hr0 hr1 hlen
    hcβ₀_norm hcβ₀_sphere
  have hcnβ₀_norm : ‖c (-β₀)‖ = 1 := by
    have h1 : ‖c (-β₀)‖ ^ 2 = 1 := by rw [hc_normsq, Real.cos_neg, hcosβ₀]; ring
    have h2 : ‖c (-β₀)‖ = Real.sqrt (‖c (-β₀)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, Real.sqrt_one] at h2; exact h2
  have hcnβ₀_sphere : ‖c (-β₀) - ξ‖ = r := by
    have h := hc_sphere (-β₀); rwa [Metric.mem_sphere, Complex.dist_eq] at h
  obtain ⟨b, hb⟩ := exists_tendsto_circleArc_end_of_arcLength_ne_top hfdiff hξ hr0 hr1 hlen
    hcnβ₀_norm hcnβ₀_sphere
  -- frontier membership, via mem_closure_of_tendsto and C2 (properness)
  have hSΔ : unitDisc ∩ sphere ξ r ⊆ unitDisc := inter_subset_left
  have hinv_tendsto : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have hmono : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono hmono (tendsto_natCast_atTop_atTop (R := ℝ))
    exact tendsto_inv_atTop_zero.comp h1
  -- sequence approaching c β₀ from within the arc, and its NeBot-witnessing tendsto-within
  set zna : ℕ → ℂ := fun n => c (β₀ - β₀ * ((n : ℝ) + 1)⁻¹) with hzna_def
  have hzna_mem : ∀ n : ℕ, zna n ∈ unitDisc := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), h1, h2]
    have hmem : β₀ - β₀ * ((n : ℝ) + 1)⁻¹ ∈ Ioo (-β₀) β₀ := ⟨by nlinarith, by nlinarith⟩
    exact (hcos_iff_mem _ (hIooβ_sub hmem)).mpr hmem
  have hzna_tendsto : Tendsto zna atTop (𝓝 (c β₀)) := by
    have hstend : Tendsto (fun n : ℕ => β₀ - β₀ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 β₀) := by
      have := (tendsto_const_nhds (x := β₀)).mul hinv_tendsto
      simp only [mul_zero] at this
      simpa using tendsto_const_nhds.sub this
    exact (hc_cont.continuousAt.tendsto).comp hstend
  have hzna_tendsto' : Tendsto zna atTop (𝓝[unitDisc ∩ sphere ξ r] (c β₀)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzna_tendsto, Filter.Eventually.of_forall fun n => ⟨hzna_mem n, hc_sphere _⟩⟩
  have hNeBotA : (𝓝[unitDisc ∩ sphere ξ r] (c β₀)).NeBot :=
    Filter.neBot_of_le hzna_tendsto'
  set znb : ℕ → ℂ := fun n => c (-β₀ + β₀ * ((n : ℝ) + 1)⁻¹) with hznb_def
  have hznb_mem : ∀ n : ℕ, znb n ∈ unitDisc := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), h1, h2]
    have hmem : -β₀ + β₀ * ((n : ℝ) + 1)⁻¹ ∈ Ioo (-β₀) β₀ := ⟨by nlinarith, by nlinarith⟩
    exact (hcos_iff_mem _ (hIooβ_sub hmem)).mpr hmem
  have hznb_tendsto : Tendsto znb atTop (𝓝 (c (-β₀))) := by
    have hstend : Tendsto (fun n : ℕ => -β₀ + β₀ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 (-β₀)) := by
      have := (tendsto_const_nhds (x := β₀)).mul hinv_tendsto
      simp only [mul_zero] at this
      simpa using tendsto_const_nhds.add this
    exact (hc_cont.continuousAt.tendsto).comp hstend
  have hznb_tendsto' : Tendsto znb atTop (𝓝[unitDisc ∩ sphere ξ r] (c (-β₀))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hznb_tendsto, Filter.Eventually.of_forall fun n => ⟨hznb_mem n, hc_sphere _⟩⟩
  have hNeBotB : (𝓝[unitDisc ∩ sphere ξ r] (c (-β₀))).NeBot :=
    Filter.neBot_of_le hznb_tendsto'
  have haΩc : a ∈ closure Ω := by
    apply mem_closure_of_tendsto ha
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hfrange ▸ ⟨z, hSΔ hz, rfl⟩
  have hbΩc : b ∈ closure Ω := by
    apply mem_closure_of_tendsto hb
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hfrange ▸ ⟨z, hSΔ hz, rfl⟩
  have haΩ : a ∉ Ω := by
    have hfa_tendsto : Tendsto (fun n => f (zna n)) atTop (𝓝 a) := ha.comp hzna_tendsto'
    exact tendsto_boundary_of_isConformalOnto hf hcβ₀_norm hzna_mem hzna_tendsto hfa_tendsto
  have hbΩ : b ∉ Ω := by
    have hfb_tendsto : Tendsto (fun n => f (znb n)) atTop (𝓝 b) := hb.comp hznb_tendsto'
    exact tendsto_boundary_of_isConformalOnto hf hcnβ₀_norm hznb_mem hznb_tendsto hfb_tendsto
  have ha_frontier : a ∈ frontier Ω := by rw [frontier, hΩo.interior_eq]; exact ⟨haΩc, haΩ⟩
  have hb_frontier : b ∈ frontier Ω := by rw [frontier, hΩo.interior_eq]; exact ⟨hbΩc, hbΩ⟩
  -- the loop/arc parametrization `F`
  have hFa_lim : Tendsto (fun s => f (c s)) (𝓝[<] β₀) (𝓝 a) := by
    apply ha.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (-β₀ : ℝ) < β₀ by linarith))]
      with s hs hs'
    exact ⟨(hcos_iff_mem s (hIooβ_sub ⟨hs', hs⟩)).mpr ⟨hs', hs⟩, hc_sphere s⟩
  have hFb_lim : Tendsto (fun s => f (c s)) (𝓝[>] (-β₀)) (𝓝 b) := by
    apply hb.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (-β₀ : ℝ) < β₀ by linarith))]
      with s hs hs'
    exact ⟨(hcos_iff_mem s (hIooβ_sub ⟨hs, hs'⟩)).mpr ⟨hs, hs'⟩, hc_sphere s⟩
  set H : ℝ → ℂ := fun u => f (c (β₀ - 2 * β₀ * u)) with hH_def
  set F : ℝ → ℂ := Function.update (Function.update H 0 a) 1 b with hF_def
  have hF0 : F 0 = a := by
    rw [hF_def, Function.update_of_ne (by norm_num : (0 : ℝ) ≠ 1), Function.update_self]
  have hF1 : F 1 = b := by rw [hF_def, Function.update_self]
  have hFH : ∀ u : ℝ, u ≠ 0 → u ≠ 1 → F u = H u := by
    intro u hu0 hu1
    rw [hF_def, Function.update_of_ne hu1, Function.update_of_ne hu0]
  have haffine_cont : Continuous (fun u : ℝ => β₀ - 2 * β₀ * u) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hH_tendsto_0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hcomp : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝[>] (0 : ℝ)) (𝓝[<] β₀) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝 (0 : ℝ)) (𝓝 β₀) := by
          have h2 := haffine_cont.continuousAt (x := (0 : ℝ))
          simpa [ContinuousAt] using h2
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Iio]; nlinarith [mem_Ioi.mp hu, hβ₀0]
    exact hFa_lim.comp hcomp
  have hH_tendsto_1 : Tendsto H (𝓝[<] (1 : ℝ)) (𝓝 b) := by
    have hcomp : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝[<] (1 : ℝ)) (𝓝[>] (-β₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun u : ℝ => β₀ - 2 * β₀ * u) (𝓝 (1 : ℝ)) (𝓝 (β₀ - 2 * β₀ * 1)) :=
          haffine_cont.continuousAt.tendsto
        have heq : β₀ - 2 * β₀ * (1 : ℝ) = -β₀ := by ring
        rw [heq] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Ioi]; nlinarith [mem_Iio.mp hu, hβ₀0]
    exact hFb_lim.comp hcomp
  have hfc_cont : ContinuousOn (f ∘ c) (Ioo (-β₀) β₀) := fun s hs =>
    (hfc_hasDerivAt s hs).continuousAt.continuousWithinAt
  have haffine_mapsTo : MapsTo (fun u : ℝ => β₀ - 2 * β₀ * u) (Ioo (0 : ℝ) 1) (Ioo (-β₀) β₀) :=
    fun u hu => ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
  have hHcont : ContinuousOn H (Ioo (0 : ℝ) 1) :=
    hfc_cont.comp haffine_cont.continuousOn haffine_mapsTo
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · -- u = 0
      have hu0' : u = 0 := hu0.symm
      subst hu0'
      rw [ContinuousWithinAt, hF0, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hH_tendsto_0 ε hε
      refine ⟨min δ₀ (1 / 2), by positivity, fun v hv hvd => ?_⟩
      rw [Real.dist_eq, sub_zero] at hvd
      rcases eq_or_ne v 0 with hv0 | hv0
      · rw [hv0, hF0]; simp only [dist_self]; exact hε
      · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
        have hvd2 : |v| < 1 / 2 := lt_of_lt_of_le hvd (min_le_right _ _)
        have hv1 : v ≠ 1 := by
          intro h; rw [h] at hvd2; norm_num at hvd2
        rw [hFH v hv0 hv1]
        have hvd' : dist v 0 < δ₀ := by rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hvd (min_le_left _ _)
        exact hδ₀' hvpos hvd'
    · rcases eq_or_lt_of_le hu.2 with hu1 | hu1
      · -- u = 1
        subst hu1
        rw [ContinuousWithinAt, hF1, Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hH_tendsto_1 ε hε
        refine ⟨min δ₀ (1 / 2), by positivity, fun v hv hvd => ?_⟩
        rw [Real.dist_eq] at hvd
        rcases eq_or_ne v 1 with hv1 | hv1
        · rw [hv1, hF1]; simp only [dist_self]; exact hε
        · have hvlt1 : v < 1 := lt_of_le_of_ne hv.2 hv1
          have hvd2 : |v - 1| < 1 / 2 := lt_of_lt_of_le hvd (min_le_right _ _)
          have hv0 : v ≠ 0 := by
            intro h; rw [h] at hvd2; norm_num at hvd2
          rw [hFH v hv0 hv1]
          have hvd' : dist v 1 < δ₀ := by rw [Real.dist_eq]; exact lt_of_lt_of_le hvd (min_le_left _ _)
          exact hδ₀' hvlt1 hvd'
      · have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu0, hu1⟩
        have hHc : ContinuousWithinAt H (Icc (0 : ℝ) 1) u :=
          ((hHcont u hu').continuousAt (isOpen_Ioo.mem_nhds hu')).continuousWithinAt
        have hFHu : F u = H u := hFH u hu0.ne' hu1.ne
        have heq : H =ᶠ[𝓝[Icc (0 : ℝ) 1] u] F := by
          filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hu')] with v hv
          exact (hFH v hv.1.ne' hv.2.ne).symm
        rw [ContinuousWithinAt, hFHu]
        exact hHc.tendsto.congr' heq
  have hFmem_Ω : ∀ u ∈ Ioo (0 : ℝ) 1, F u ∈ Ω := by
    intro u hu
    rw [hFH u hu.1.ne' hu.2.ne, hH_def]
    exact hfrange ▸ ⟨c (β₀ - 2 * β₀ * u),
      (hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hu))).mpr (haffine_mapsTo hu), rfl⟩
  have hFinj_Ico : InjOn F (Ico (0 : ℝ) 1) := by
    intro u hu v hv huv
    rcases eq_or_ne u 0 with hu0 | hu0
    · rcases eq_or_ne v 0 with hv0 | hv0
      · rw [hu0, hv0]
      · exfalso
        have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv.2⟩
        rw [hu0, hF0] at huv
        exact haΩ (huv ▸ hFmem_Ω v hv')
    · rcases eq_or_ne v 0 with hv0 | hv0
      · exfalso
        have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
        rw [hv0, hF0] at huv
        exact haΩ (huv.symm ▸ hFmem_Ω u hu')
      · have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
        have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv.2⟩
        rw [hFH u hu0 hu'.2.ne, hFH v hv0 hv'.2.ne, hH_def] at huv
        have hcuv : c (β₀ - 2 * β₀ * u) = c (β₀ - 2 * β₀ * v) :=
          hfinj ((hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hu'))).mpr (haffine_mapsTo hu'))
            ((hcos_iff_mem _ (hIooβ_sub (haffine_mapsTo hv'))).mpr (haffine_mapsTo hv')) huv
        have hs_eq : β₀ - 2 * β₀ * u = β₀ - 2 * β₀ * v :=
          hc_inj (Ioo_subset_Icc_self (haffine_mapsTo hu')) (Ioo_subset_Icc_self (haffine_mapsTo hv'))
            hcuv
        have h2 : β₀ * u = β₀ * v := by linarith
        exact mul_left_cancel₀ hβ₀0.ne' h2
  have hHrange : H '' Ioo (0 : ℝ) 1 = f '' (unitDisc ∩ sphere ξ r) := by
    rw [hS_eq]
    apply Subset.antisymm
    · rintro w ⟨u, hu, rfl⟩
      exact ⟨c (β₀ - 2 * β₀ * u), ⟨β₀ - 2 * β₀ * u, haffine_mapsTo hu, rfl⟩, rfl⟩
    · rintro w ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨(β₀ - t) / (2 * β₀),
        ⟨div_pos (by linarith [ht.2]) (by linarith),
          (div_lt_one (by linarith)).mpr (by linarith [ht.1])⟩, ?_⟩
      have heq : β₀ - 2 * β₀ * ((β₀ - t) / (2 * β₀)) = t := by
        field_simp
        ring
      show f (c (β₀ - 2 * β₀ * ((β₀ - t) / (2 * β₀)))) = f (c t)
      rw [heq]
  have hFimg : F '' Ioo (0 : ℝ) 1 = f '' (unitDisc ∩ sphere ξ r) := by
    rw [← hHrange]
    exact image_congr fun u hu => hFH u hu.1.ne' hu.2.ne
  refine ⟨F, hFcont, hFinj_Ico.mono Ioo_subset_Ico_self, hFimg, ?_, ?_, ⟨c β₀, hcβ₀_norm, hcβ₀_sphere, ?_⟩,
    ⟨c (-β₀), hcnβ₀_norm, hcnβ₀_sphere, ?_⟩⟩
  · rw [hF0]
    exact ha_frontier
  · rw [hF1]
    exact hb_frontier
  · rw [hF0]
    exact ha
  · rw [hF1]
    exact hb

/-- **Wolff's length–area estimate off a null set.**  The copy of `exists_radius_sq_arcLength_lt`
(`Lemmas/Caratheodory.lean`) with the radius chosen outside a given null set `N`: the proof is the same, since the
pointwise lower bound is needed only almost everywhere (`lintegral_mono_ae`). -/
theorem pe6_exists_radius_sq_arcLength_lt_notMem {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (z₀ : ℂ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {b : ℝ}
    (hb : (volume Ω).toReal * (4 * π) / Real.log (1 / δ) < b) {N : Set ℝ} (hN : volume N = 0) :
    ∃ ρ ∈ Ioo δ (Real.sqrt δ), ρ ∉ N ∧ arcLength f z₀ ρ ^ 2 < ENNReal.ofReal b := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hDo : IsOpen unitDisc := by
    unfold unitDisc
    exact isOpen_ball
  have harea : ∫⁻ z in unitDisc, ‖deriv f z‖ₑ ^ 2 = volume Ω := by
    have h := lintegral_image_conformal hDo hf (fun _ => 1)
    simp only [mul_one, setLIntegral_one] at h
    exact h.symm
  have hfin : volume Ω < ⊤ := by
    obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : ℂ)
    exact lt_of_le_of_lt (measure_mono hR) measure_closedBall_lt_top
  have hpolar := lintegral_unitDisc_eq_polar z₀ ((measurable_deriv f).enorm.pow_const 2)
  simp_rw [lintegral_Ioo_indicator_eq_arc] at hpolar
  rw [harea] at hpolar
  have hsqrt : δ < Real.sqrt δ := by
    rw [Real.lt_sqrt hδ0.le]
    nlinarith
  have hlog : 0 < Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_pos (one_lt_inv₀ hδ0 |>.2 hδ1)
  have hpt : ∀ ρ ∈ Ioo δ (Real.sqrt δ), ρ ∉ N →
      ENNReal.ofReal b * ENNReal.ofReal (1 / ρ) ≤ ENNReal.ofReal (2 * π) *
        ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
          ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
    intro ρ hρ hρN
    have hρ0 : 0 < ρ := hδ0.trans hρ.1
    have h := (hcon ρ hρ hρN).trans (sq_arcLength_le f z₀ ρ)
    have hρρ : ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ) = 1 := by
      rw [← ENNReal.ofReal_mul hρ0.le, mul_one_div_cancel hρ0.ne', ENNReal.ofReal_one]
    calc ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
        ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) * ENNReal.ofReal (1 / ρ) :=
          mul_le_mul_left h _
      _ = ENNReal.ofReal (2 * π) *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) *
            (ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ)) := by ring
      _ = _ := by rw [hρρ, mul_one]
  have hint : ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
      ≤ ENNReal.ofReal (2 * π) * volume Ω := by
    calc ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
        ≤ ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal (2 * π) *
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo,
            ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN)] with ρ hρ hρN
          exact hpt ρ hρ hρN
      _ = ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioo δ (Real.sqrt δ),
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioi (0 : ℝ),
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ :=
          mul_le_mul_right (lintegral_mono_set fun ρ hρ => hδ0.trans hρ.1) _
      _ = ENNReal.ofReal (2 * π) * volume Ω := by rw [← hpolar]
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  have hleft : ∫⁻ ρ in Ioo δ (Real.sqrt δ), ENNReal.ofReal b * ENNReal.ofReal (1 / ρ)
      = ENNReal.ofReal (b * (Real.log (1 / δ) / 2)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hInt : IntegrableOn (fun ρ : ℝ => 1 / ρ) (Ioo δ (Real.sqrt δ)) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
      exact continuousOn_const.div continuousOn_id fun ρ hρ => (hδ0.trans_le hρ.1).ne'
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo δ (Real.sqrt δ))] fun ρ => 1 / ρ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
      exact (one_div_pos.2 (hδ0.trans hρ.1)).le
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, ← ENNReal.ofReal_mul ?_]
    · congr 1
      rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hsqrt.le]
      simp_rw [one_div]
      rw [integral_inv (Set.notMem_uIcc_of_lt hδ0 (Real.sqrt_pos.2 hδ0)), Real.log_div
        (Real.sqrt_pos.2 hδ0).ne' hδ0.ne', Real.log_sqrt hδ0.le, Real.log_inv]
      ring
    · exact hb0
  have hRHS : ENNReal.ofReal (2 * π) * volume Ω = ENNReal.ofReal (2 * π * (volume Ω).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π), ENNReal.ofReal_toReal hfin.ne]
  rw [hleft, hRHS, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
  have : b ≤ (volume Ω).toReal * (4 * π) / Real.log (1 / δ) := by
    rw [le_div_iff₀ hlog]
    nlinarith [hint]
  exact absurd hb (not_lt.2 this)

/-- **One Wolff radius, small and off a null set.**  For `r, ε > 0` and a null set `N` there is a radius
`ρ ∈ (0, min r 1)`, `ρ ∉ N`, whose arc has length `< ε` (`pe6_exists_radius_sq_arcLength_lt_notMem` with
`δ ≤ min (r, 1)² / 4` and `log (1/δ) ≥ Area · 4π / ε² + 1`). -/
theorem pe6_exists_radius_notMem {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (z₀ : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {N : Set ℝ}
    (hN : volume N = 0) :
    ∃ ρ, 0 < ρ ∧ ρ < r ∧ ρ < 1 ∧ ρ ∉ N ∧ arcLength f z₀ ρ < ENNReal.ofReal ε := by
  have hA0 : 0 ≤ (volume Ω).toReal * (4 * π) := by positivity
  have hε2 : ε ^ 2 ≠ 0 := by positivity
  have hT0 : 0 < (volume Ω).toReal * (4 * π) / ε ^ 2 + 1 := by positivity
  have hm0 : 0 < min r 1 := lt_min hr one_pos
  have hδ0 : 0 < min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))) :=
    lt_min (by positivity) (Real.exp_pos _)
  have hδexp : min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))) ≤
      Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1)) := min_le_right _ _
  have hδ1 : min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))) < 1 :=
    hδexp.trans_lt (Real.exp_lt_one_iff.2 (by linarith))
  have hsqrt : Real.sqrt (min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1)))) ≤
      min r 1 / 2 := by
    calc Real.sqrt (min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))))
        ≤ Real.sqrt (min r 1 ^ 2 / 4) := Real.sqrt_le_sqrt (min_le_left _ _)
      _ = min r 1 / 2 := by
        rw [show min r 1 ^ 2 / 4 = (min r 1 / 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
  have hlogT : (volume Ω).toReal * (4 * π) / ε ^ 2 + 1 ≤
      Real.log (1 / min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1)))) := by
    rw [one_div, Real.log_inv, le_neg]
    calc Real.log (min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))))
        ≤ Real.log (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))) := Real.log_le_log hδ0 hδexp
      _ = -((volume Ω).toReal * (4 * π) / ε ^ 2 + 1) := Real.log_exp _
  have hlog := hT0.trans_le hlogT
  have hb : (volume Ω).toReal * (4 * π) /
      Real.log (1 / min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1)))) <
        ε ^ 2 := by
    rw [div_lt_iff₀ hlog]
    have h1 : ε ^ 2 * ((volume Ω).toReal * (4 * π) / ε ^ 2 + 1) = (volume Ω).toReal * (4 * π) + ε ^ 2 := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hε2]
    have h2 := mul_le_mul_of_nonneg_left hlogT (sq_nonneg ε)
    have h3 : 0 < ε ^ 2 := by positivity
    nlinarith
  obtain ⟨ρ, hρ, hρN, hρlt⟩ := pe6_exists_radius_sq_arcLength_lt_notMem hΩ hf z₀ hδ0 hδ1 hb hN
  have hρ0 : 0 < min (min r 1 ^ 2 / 4) (Real.exp (-((volume Ω).toReal * (4 * π) / ε ^ 2 + 1))) :=
    hδ0
  have hρm : ρ < min r 1 := by
    have := hρ.2
    linarith
  refine ⟨ρ, hρ0.trans hρ.1, hρm.trans_le (min_le_left _ _), hρm.trans_le (min_le_right _ _), hρN, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  have h2 : ENNReal.ofReal ε ^ 2 ≤ arcLength f z₀ ρ ^ 2 := pow_le_pow_left' hge 2
  rw [← ENNReal.ofReal_pow hε.le] at h2
  exact absurd hρlt (not_lt.2 h2)

/-- **The radii of the σ-chain.**  There are radii `rₙ ↓` in `(0, 1)` with arc lengths `< 1/(n+1)` and crosscut
parametrizations `γₙ` of `f(Δ ∩ sphere ξ rₙ)` (`pe6_arc_crosscut`) such that the two end values of `γₙ₊₁` differ
from the two end values of `γₙ` (also for `n = 0`).  Each `rₙ₊₁` is a Wolff radius off the null set
`pe6_badRadii f ξ (γₙ 0) ∪ pe6_badRadii f ξ (γₙ 1)` (`pe6_volume_badRadii_eq_zero`). -/
theorem pe6_exists_radii {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    ∃ r : ℕ → ℝ, ∃ γ : ℕ → ℝ → ℂ, (∀ n, 0 < r n ∧ r n < 1) ∧ StrictAnti r ∧
      (∀ n, arcLength f ξ (r n) < ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
      (∀ n, ContinuousOn (γ n) (Icc 0 1) ∧ InjOn (γ n) (Ioo 0 1) ∧
        γ n '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ (r n)) ∧ γ n 0 ∈ frontier Ω ∧ γ n 1 ∈ frontier Ω) ∧
      ∀ n, γ (n + 1) 0 ≠ γ n 0 ∧ γ (n + 1) 0 ≠ γ n 1 ∧ γ (n + 1) 1 ≠ γ n 0 ∧ γ (n + 1) 1 ≠ γ n 1 := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfr : ∀ {z : ℂ}, z ∈ frontier Ω → z ∉ Ω := fun hz => by
    rw [hΩo.frontier_eq] at hz
    exact hz.2
  have hcross : ∀ ρ : ℝ, ∃ γ : ℝ → ℂ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤ →
      ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ ρ) ∧
        γ 0 ∈ frontier Ω ∧ γ 1 ∈ frontier Ω ∧
        (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = ρ ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ ρ] p) (𝓝 (γ 0))) ∧
        (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = ρ ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ ρ] p) (𝓝 (γ 1))) := by
    intro ρ
    by_cases h : 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤
    · obtain ⟨γ, hγ⟩ := pe6_arc_crosscut hf hξ h.1 h.2.1 h.2.2
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose Γ hΓ using hcross
  have hstep : ∀ (n : ℕ) (ρ : ℝ), ∃ ρ' : ℝ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤ →
      0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' ∉ pe6_badRadii f ξ (Γ ρ 0) ∪ pe6_badRadii f ξ (Γ ρ 1) ∧
        arcLength f ξ ρ' < ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    intro n ρ
    by_cases h : 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤
    · obtain ⟨-, -, -, h0, h1, -, -⟩ := hΓ ρ h
      have hN : volume (pe6_badRadii f ξ (Γ ρ 0) ∪ pe6_badRadii f ξ (Γ ρ 1)) = 0 :=
        measure_union_null (pe6_volume_badRadii_eq_zero hΩ hf hξ (hfr h0))
          (pe6_volume_badRadii_eq_zero hΩ hf hξ (hfr h1))
      obtain ⟨ρ', h1', h2', h3', h4', h5'⟩ :=
        pe6_exists_radius_notMem hΩ hf ξ h.1 (by positivity : (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) + 1)) hN
      exact ⟨ρ', fun _ => ⟨h1', h2', h3', h4', h5'⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose nx hnx using hstep
  obtain ⟨r₀, hr₀0, -, hr₀1, -, hr₀len⟩ :=
    pe6_exists_radius_notMem hΩ hf ξ one_pos one_pos (N := ∅) measure_empty
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → ℝ, r 0 = r₀ ∧ ∀ n, r (n + 1) = nx n (r n) :=
    ⟨fun n => Nat.rec r₀ (fun k ρ => nx k ρ) n, rfl, fun n => rfl⟩
  have hgood : ∀ n, (0 < r n ∧ r n < 1 ∧ arcLength f ξ (r n) ≠ ⊤) ∧
      arcLength f ξ (r n) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    induction n with
    | zero =>
      rw [hr0]
      have h1 : arcLength f ξ r₀ < ENNReal.ofReal (1 / (((0 : ℕ) : ℝ) + 1)) := by
        simpa using hr₀len
      exact ⟨⟨hr₀0, hr₀1, h1.ne_top⟩, h1⟩
    | succ k ih =>
      obtain ⟨h1, -, h3, -, h5⟩ := hnx k (r k) ih.1
      rw [hrs k]
      exact ⟨⟨h1, h3, h5.ne_top⟩, h5⟩
  have hanti : StrictAnti r := by
    refine strictAnti_nat_of_succ_lt fun n => ?_
    rw [hrs n]
    exact (hnx n (r n) (hgood n).1).2.1
  have hγ : ∀ n, ContinuousOn (Γ (r n)) (Icc 0 1) ∧ InjOn (Γ (r n)) (Ioo 0 1) ∧
      Γ (r n) '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ (r n)) ∧ Γ (r n) 0 ∈ frontier Ω ∧
        Γ (r n) 1 ∈ frontier Ω := by
    intro n
    obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hΓ (r n) (hgood n).1
    exact ⟨h1, h2, h3, h4, h5⟩
  have hends : ∀ n, Γ (r (n + 1)) 0 ≠ Γ (r n) 0 ∧ Γ (r (n + 1)) 0 ≠ Γ (r n) 1 ∧
      Γ (r (n + 1)) 1 ≠ Γ (r n) 0 ∧ Γ (r (n + 1)) 1 ≠ Γ (r n) 1 := by
    intro n
    have hN := (hnx n (r n) (hgood n).1).2.2.2.1
    rw [← hrs n] at hN
    obtain ⟨-, -, -, -, -, ⟨p₀, hp₀, hp₀r, ht₀⟩, ⟨p₁, hp₁, hp₁r, ht₁⟩⟩ := hΓ (r (n + 1)) (hgood (n + 1)).1
    have hmem : r (n + 1) ∈ Ioo (0 : ℝ) 1 := ⟨(hgood (n + 1)).1.1, (hgood (n + 1)).1.2.1⟩
    refine ⟨fun h => hN (Or.inl ⟨hmem, p₀, hp₀, hp₀r, ?_⟩), fun h => hN (Or.inr ⟨hmem, p₀, hp₀, hp₀r, ?_⟩),
      fun h => hN (Or.inl ⟨hmem, p₁, hp₁, hp₁r, ?_⟩), fun h => hN (Or.inr ⟨hmem, p₁, hp₁, hp₁r, ?_⟩)⟩
    · rw [← h]
      exact ht₀
    · rw [← h]
      exact ht₀
    · rw [← h]
      exact ht₁
    · rw [← h]
      exact ht₁
  exact ⟨r, fun n => Γ (r n), fun n => ⟨(hgood n).1.1, (hgood n).1.2.1⟩, hanti, fun n => (hgood n).2, hγ,
    hends⟩

/-! ### Stage C: the σ-chain is a null-chain; (⇐) -/

/-- **The σ-chain.**  For `‖ξ‖ = 1` there is a null-chain `C` of `Ω` whose impression contains the cluster set of
`f` at `ξ`: `Cₙ = f(Δ ∩ sphere ξ rₙ)` with the radii of `pe6_exists_radii`.  Closures of consecutive crosscuts are
disjoint (only the four end values could meet), a middle circle separates (`pe6_connectedComponentIn_ne`),
`diam Cₙ ≤ ℓ(rₙ) < 1/(n+1)` (`exists_ends_of_circleArc_image`), and `f(Δ ∩ ball ξ rₙ)` is a connected subset of
`Ω ∖ Cₙ` containing `Cₙ₊₁`, hence of `chainEnd n`. -/
theorem pe6_exists_nullChain_clusterSet_subset {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    ∃ C : ℕ → Set ℂ, IsNullChain Ω C ∧ clusterSet f unitDisc ξ ⊆ chainImpression Ω C := by
  obtain ⟨r, γ, hr, hanti, hlen, hγ, hends⟩ := pe6_exists_radii hΩ hf hξ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfr : ∀ {z : ℂ}, z ∈ frontier Ω → z ∉ Ω := fun hz => by
    rw [hΩo.frontier_eq] at hz
    exact hz.2
  have hCΩ : ∀ n, f '' (unitDisc ∩ sphere ξ (r n)) ⊆ Ω := fun n => by
    rw [← hf.2.2]
    exact image_mono inter_subset_left
  have hdisj : ∀ m n, m ≠ n →
      Disjoint (f '' (unitDisc ∩ sphere ξ (r m))) (f '' (unitDisc ∩ sphere ξ (r n))) :=
    fun m n hmn => pe6_disjoint_image_arc hf.2.1 (hanti.injective.ne hmn)
  have hcl : ∀ n, closure (f '' (unitDisc ∩ sphere ξ (r n))) ⊆
      f '' (unitDisc ∩ sphere ξ (r n)) ∪ {γ n 0, γ n 1} := by
    intro n
    obtain ⟨hc, -, himg, -, -⟩ := hγ n
    rw [← himg, pe6_closure_image_Ioo hc]
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact Or.inr (Or.inl (congrArg (γ n) h0.symm))
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · exact Or.inr (Or.inr (congrArg (γ n) h1))
      · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩
  refine ⟨fun n => f '' (unitDisc ∩ sphere ξ (r n)), ⟨fun n => ?_, fun n => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · obtain ⟨hc, hi, himg, h0, h1⟩ := hγ n
    exact ⟨γ n, hc, hi, himg, hCΩ n, h0, h1⟩
  · refine Set.disjoint_of_subset (hcl n) (hcl (n + 1)) ?_
    obtain ⟨-, -, -, h0n, h1n⟩ := hγ n
    obtain ⟨-, -, -, h0m, h1m⟩ := hγ (n + 1)
    obtain ⟨e1, e2, e3, e4⟩ := hends n
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.1 (hdisj n (n + 1) (by omega)) hz hz'
    · simp only [mem_insert_iff, mem_singleton_iff] at hz'
      rcases hz' with rfl | rfl
      · exact hfr h0m (hCΩ n hz)
      · exact hfr h1m (hCΩ n hz)
    · simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hfr h0n (hCΩ (n + 1) hz')
      · exact hfr h1n (hCΩ (n + 1) hz')
    · simp only [mem_insert_iff, mem_singleton_iff] at hz hz'
      rcases hz with rfl | rfl
      · rcases hz' with h | h
        · exact e1 h.symm
        · exact e3 h.symm
      · rcases hz' with h | h
        · exact e2 h.symm
        · exact e4 h.symm
  · exact ⟨hdisj 0 n (by omega), fun x hx y hy =>
      pe6_connectedComponentIn_ne hf (hanti (Nat.lt_succ_self n)) (hanti (by omega : 0 < n)) hx hy⟩
  · refine squeeze_zero (fun n => Metric.diam_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨-, -, -, -, hd, -⟩ := exists_ends_of_circleArc_image hΩ hf hξ (hr n).1 (hr n).2 (hlen n).ne_top
    exact hd.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) (hlen n).le)
  · intro w hw
    simp only [chainImpression, mem_iInter]
    intro n
    have hw' : w ∈ closure (f '' (unitDisc ∩ ball ξ (r n))) := by
      simp only [clusterSet, mem_iInter] at hw
      exact hw (r n) (hr n).1
    refine closure_mono ?_ hw'
    have hy₀ := pe6_mem_arc hξ (hr (n + 1)).1 (hr (n + 1)).2
    have hS : IsPreconnected (f '' (unitDisc ∩ ball ξ (r n))) :=
      ((convex_ball (0 : ℂ) 1).inter (convex_ball ξ (r n))).isPreconnected.image f
        (hf.1.continuousOn.mono inter_subset_left)
    have hy₀S : f (((1 - r (n + 1) : ℝ) : ℂ) * ξ) ∈ f '' (unitDisc ∩ ball ξ (r n)) := by
      refine ⟨_, ⟨hy₀.1, ?_⟩, rfl⟩
      rw [mem_ball, mem_sphere.1 hy₀.2]
      exact hanti (Nat.lt_succ_self n)
    have hSF : f '' (unitDisc ∩ ball ξ (r n)) ⊆ Ω \ f '' (unitDisc ∩ sphere ξ (r n)) := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨hf.mapsTo hz.1, ?_⟩
      rintro ⟨u, hu, hfu⟩
      have huz : u = z := hf.2.1 hu.1 hz.1 hfu
      subst huz
      exact (mem_ball.1 hz.2).ne (mem_sphere.1 hu.2)
    intro z hz
    simp only [chainEnd, mem_iUnion]
    exact ⟨_, ⟨_, hy₀, rfl⟩, hS.subset_connectedComponentIn hy₀S hSF hz⟩

/-- **(⇐).**  If every null-chain has at most one impression point, `∂Ω` is locally connected: otherwise some
cluster set `clusterSet f unitDisc ξ` (nonempty, `clusterSet_isCompact_isConnected`) is not a single point
(`locallyConnected_iff_clusterSet_subsingleton`), yet it lies in the impression of the σ-chain at `ξ`. -/
theorem pe6_lc_of_forall_subsingleton {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω)
    (h : ∀ C : ℕ → Set ℂ, IsNullChain Ω C → (chainImpression Ω C).Subsingleton) :
    LocallyConnectedSpace (frontier Ω) := by
  rw [locallyConnected_iff_clusterSet_subsingleton hΩ hf]
  intro ξ hξ
  have hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hΩ
    exact ⟨R, fun z hz => by simpa using hR (hf.mapsTo hz)⟩
  obtain ⟨⟨w, hw⟩, -, -⟩ := clusterSet_isCompact_isConnected hξ hf.1.continuousOn hbdd
  obtain ⟨C, hC, hsub⟩ := pe6_exists_nullChain_clusterSet_subset hΩ hf (mem_sphere_zero_iff_norm.1 hξ)
  exact ⟨w, ((h C hC).anti hsub).eq_singleton_of_mem hw⟩

/-! ### The proofs of `caratheodory_primeEnd`, `caratheodory_primeEnd_principal` and
`principalPoints_isCompact_isConnected` (s21r PE2): circular chains

`P ζ` is the class of a circular chain `pe5_circ f ζ r`, `Cₙ = f(Δ ∩ sphere ζ rₙ)`, along Wolff radii `rₙ → 0` chosen
off the Jensen–Fatou null sets of `pe6_volume_badRadii_eq_zero` (Stage A; `pe5_exists_radii_of_step` is the recursion
of `pe6_exists_radii` with a pluggable step, so that the radii also tend to `0`).  The ends of a circular chain are
`f(Δ ∩ ball ζ rₙ)` (`pe5_chainEnd_circ`): two circular chains at `ζ` are equivalent, the impression is the cluster set
of `f` at `ζ`, and circular chains at distinct points are inequivalent.

Stage B is Pommerenke's proof of Thm 2.15 (c), run on the ends `Vₙ` of a null-chain `C` instead of on the preimage
crosscuts, and without Prop. 2.14: the compact set `⋂ₙ closure f⁻¹(Vₙ)` is nonempty, lies on the circle, and is a single
point `ζ`, since two points would force a late crosscut `Cₙ` (small diameter) to meet two consecutive circular
crosscuts at `ζ`, whose closures are disjoint (`pe5_eq_of_mem_closure_ends`).  A two-curves step with the same arcs
shows that `ζ` lies in the closure of at most one of `f⁻¹(C_m)`, `f⁻¹(C_{m+1})` (`pe5_two_curves`), which gives the
equivalence of `C` with the circular chain at `ζ` (`pe5_exists_equiv_circ`).

Stage D: the principal points of `P ζ` are the radial cluster set of `f` at `ζ` (Pommerenke Thm 2.16): the radius
crosses the late crosscuts of any representing chain (⊆, `pe9_mem_radialClusterSet_of_tendsto`); conversely Wolff radii
in the windows `(s/2, s)` (the local area tends to `0`) and Koebe's distortion along the radius
(`koebe_quarter_of_not_mem`, `koebe_growth_scaled`, Pommerenke (2.5.8)) give a circular chain converging to a given
radial cluster point (⊇, `pe9_exists_circChain_tendsto`).  Stage E: the radial cluster set is a decreasing
intersection of continua. -/

/-! ### Stage A (PE2): circular chains and the prime-end class -/

/-- Equivalence of null-chains is transitive. -/
theorem pe5_nullChainEquiv_trans {Ω : Set ℂ} {C C' C'' : ℕ → Set ℂ} (h : NullChainEquiv Ω C C')
    (h' : NullChainEquiv Ω C' C'') : NullChainEquiv Ω C C'' := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨n', hn'⟩ := h'.1 m
    obtain ⟨n, hn⟩ := h.1 n'
    exact ⟨n, hn.trans hn'⟩
  · obtain ⟨n', hn'⟩ := h.2 m
    obtain ⟨n, hn⟩ := h'.2 n'
    exact ⟨n, hn.trans hn'⟩

/-- `NullChainEquiv Ω` is an equivalence relation on null-chains (no nesting of the ends is needed). -/
theorem pe5_nullChainEquiv_equivalence (Ω : Set ℂ) :
    Equivalence fun c c' : {C : ℕ → Set ℂ // IsNullChain Ω C} => NullChainEquiv Ω c.1 c'.1 := by
  refine ⟨fun c => ⟨fun m => ⟨m, subset_rfl⟩, fun m => ⟨m, subset_rfl⟩⟩, fun h => ⟨h.2, h.1⟩, fun h h' => ?_⟩
  exact pe5_nullChainEquiv_trans h h'

/-- **The `Quot` collapse.**  Two null-chains define the same prime end iff they are equivalent
(`Quot.eqvGen_exact` + `Equivalence.eqvGen_iff`). -/
theorem pe5_quot_eq_iff {Ω : Set ℂ} {c c' : {C : ℕ → Set ℂ // IsNullChain Ω C}} :
    (Quot.mk _ c : PrimeEnd Ω) = Quot.mk _ c' ↔ NullChainEquiv Ω c.1 c'.1 := by
  constructor
  · intro h
    exact (pe5_nullChainEquiv_equivalence Ω).eqvGen_iff.1 (Quot.eqvGen_exact h)
  · intro h
    exact Quot.sound h

/-- The **circular chain** at `ξ` along the radii `r`: `Cₙ = f(Δ ∩ sphere ξ rₙ)`. -/
def pe5_circ (f : ℂ → ℂ) (ξ : ℂ) (r : ℕ → ℝ) (n : ℕ) : Set ℂ := f '' (unitDisc ∩ sphere ξ (r n))

/-- `r` defines a **circular null-chain** at `ξ`: radii in `(0, 1)`, strictly decreasing to `0`, whose circular chain
`pe5_circ f ξ r` is a null-chain of `Ω`. -/
def pe5_IsCircChain (Ω : Set ℂ) (f : ℂ → ℂ) (ξ : ℂ) (r : ℕ → ℝ) : Prop :=
  (∀ n, 0 < r n ∧ r n < 1) ∧ StrictAnti r ∧ Tendsto r atTop (𝓝 0) ∧ IsNullChain Ω (pe5_circ f ξ r)

/-- **The radii of a circular chain, with a pluggable step.**  The recursion of `pe6_exists_radii` (copied), where the
start radius comes from `h0` and each step from the oracle `hstep`, called with the Jensen–Fatou null set
`pe6_badRadii f ξ (γₙ 0) ∪ pe6_badRadii f ξ (γₙ 1)` of the previous crosscut (`pe6_volume_badRadii_eq_zero`); the
predicate `G` is carried along.  The conclusion is that of `pe6_exists_radii` plus `∀ n, G n (r n)`. -/
theorem pe5_exists_radii_of_step {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) (G : ℕ → ℝ → Prop)
    (h0 : ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ < ENNReal.ofReal 1 ∧ G 0 ρ)
    (hstep : ∀ (n : ℕ) (ρ : ℝ) (N : Set ℝ), 0 < ρ → volume N = 0 →
      ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' ∉ N ∧
        arcLength f ξ ρ' < ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) + 1)) ∧ G (n + 1) ρ') :
    ∃ r : ℕ → ℝ, ∃ γ : ℕ → ℝ → ℂ, (∀ n, G n (r n)) ∧ (∀ n, 0 < r n ∧ r n < 1) ∧ StrictAnti r ∧
      (∀ n, arcLength f ξ (r n) < ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
      (∀ n, ContinuousOn (γ n) (Icc 0 1) ∧ InjOn (γ n) (Ioo 0 1) ∧
        γ n '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ (r n)) ∧ γ n 0 ∈ frontier Ω ∧ γ n 1 ∈ frontier Ω) ∧
      ∀ n, γ (n + 1) 0 ≠ γ n 0 ∧ γ (n + 1) 0 ≠ γ n 1 ∧ γ (n + 1) 1 ≠ γ n 0 ∧ γ (n + 1) 1 ≠ γ n 1 := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfr : ∀ {z : ℂ}, z ∈ frontier Ω → z ∉ Ω := fun hz => by
    rw [hΩo.frontier_eq] at hz
    exact hz.2
  have hcross : ∀ ρ : ℝ, ∃ γ : ℝ → ℂ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤ →
      ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ ρ) ∧
        γ 0 ∈ frontier Ω ∧ γ 1 ∈ frontier Ω ∧
        (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = ρ ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ ρ] p) (𝓝 (γ 0))) ∧
        (∃ p : ℂ, ‖p‖ = 1 ∧ ‖p - ξ‖ = ρ ∧ Tendsto f (𝓝[unitDisc ∩ sphere ξ ρ] p) (𝓝 (γ 1))) := by
    intro ρ
    by_cases h : 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤
    · obtain ⟨γ, hγ⟩ := pe6_arc_crosscut hf hξ h.1 h.2.1 h.2.2
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose Γ hΓ using hcross
  have hstep' : ∀ (n : ℕ) (ρ : ℝ), ∃ ρ' : ℝ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤ →
      0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' ∉ pe6_badRadii f ξ (Γ ρ 0) ∪ pe6_badRadii f ξ (Γ ρ 1) ∧
        arcLength f ξ ρ' < ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) + 1)) ∧ G (n + 1) ρ' := by
    intro n ρ
    by_cases h : 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ ≠ ⊤
    · obtain ⟨-, -, -, h0, h1, -, -⟩ := hΓ ρ h
      have hN : volume (pe6_badRadii f ξ (Γ ρ 0) ∪ pe6_badRadii f ξ (Γ ρ 1)) = 0 :=
        measure_union_null (pe6_volume_badRadii_eq_zero hΩ hf hξ (hfr h0))
          (pe6_volume_badRadii_eq_zero hΩ hf hξ (hfr h1))
      obtain ⟨ρ', h1', h2', h3', h4', h5', h6'⟩ := hstep n ρ _ h.1 hN
      exact ⟨ρ', fun _ => ⟨h1', h2', h3', h4', h5', h6'⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose nx hnx using hstep'
  obtain ⟨r₀, hr₀0, hr₀1, hr₀len, hr₀G⟩ := h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → ℝ, r 0 = r₀ ∧ ∀ n, r (n + 1) = nx n (r n) :=
    ⟨fun n => Nat.rec r₀ (fun k ρ => nx k ρ) n, rfl, fun n => rfl⟩
  have hgood : ∀ n, (0 < r n ∧ r n < 1 ∧ arcLength f ξ (r n) ≠ ⊤) ∧
      arcLength f ξ (r n) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧ G n (r n) := by
    intro n
    induction n with
    | zero =>
      rw [hr0]
      have h1 : arcLength f ξ r₀ < ENNReal.ofReal (1 / (((0 : ℕ) : ℝ) + 1)) := by
        simpa using hr₀len
      exact ⟨⟨hr₀0, hr₀1, h1.ne_top⟩, h1, hr₀G⟩
    | succ k ih =>
      obtain ⟨h1, -, h3, -, h5, h6⟩ := hnx k (r k) ih.1
      rw [hrs k]
      exact ⟨⟨h1, h3, h5.ne_top⟩, h5, h6⟩
  have hanti : StrictAnti r := by
    refine strictAnti_nat_of_succ_lt fun n => ?_
    rw [hrs n]
    exact (hnx n (r n) (hgood n).1).2.1
  have hγ : ∀ n, ContinuousOn (Γ (r n)) (Icc 0 1) ∧ InjOn (Γ (r n)) (Ioo 0 1) ∧
      Γ (r n) '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ (r n)) ∧ Γ (r n) 0 ∈ frontier Ω ∧
        Γ (r n) 1 ∈ frontier Ω := by
    intro n
    obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hΓ (r n) (hgood n).1
    exact ⟨h1, h2, h3, h4, h5⟩
  have hends : ∀ n, Γ (r (n + 1)) 0 ≠ Γ (r n) 0 ∧ Γ (r (n + 1)) 0 ≠ Γ (r n) 1 ∧
      Γ (r (n + 1)) 1 ≠ Γ (r n) 0 ∧ Γ (r (n + 1)) 1 ≠ Γ (r n) 1 := by
    intro n
    have hN := (hnx n (r n) (hgood n).1).2.2.2.1
    rw [← hrs n] at hN
    obtain ⟨-, -, -, -, -, ⟨p₀, hp₀, hp₀r, ht₀⟩, ⟨p₁, hp₁, hp₁r, ht₁⟩⟩ := hΓ (r (n + 1)) (hgood (n + 1)).1
    have hmem : r (n + 1) ∈ Ioo (0 : ℝ) 1 := ⟨(hgood (n + 1)).1.1, (hgood (n + 1)).1.2.1⟩
    refine ⟨fun h => hN (Or.inl ⟨hmem, p₀, hp₀, hp₀r, ?_⟩), fun h => hN (Or.inr ⟨hmem, p₀, hp₀, hp₀r, ?_⟩),
      fun h => hN (Or.inl ⟨hmem, p₁, hp₁, hp₁r, ?_⟩), fun h => hN (Or.inr ⟨hmem, p₁, hp₁, hp₁r, ?_⟩)⟩
    · rw [← h]
      exact ht₀
    · rw [← h]
      exact ht₀
    · rw [← h]
      exact ht₁
    · rw [← h]
      exact ht₁
  exact ⟨r, fun n => Γ (r n), fun n => (hgood n).2.2, fun n => ⟨(hgood n).1.1, (hgood n).1.2.1⟩, hanti,
    fun n => (hgood n).2.1, hγ, hends⟩

/-- **A circular chain with separated ends is a null-chain.**  The four null-chain clauses of the proof of
`pe6_exists_nullChain_clusterSet_subset` (copied), for the explicit chain `pe5_circ f ξ r`: the crosscut
parametrizations `γₙ`, disjoint consecutive closures (only the four end values could meet), a middle circle separates
(`pe6_connectedComponentIn_ne`), and `diam Cₙ ≤ ℓ(rₙ) < 1/(n+1)` (`exists_ends_of_circleArc_image`). -/
theorem pe5_isNullChain_circ {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {r : ℕ → ℝ} {γ : ℕ → ℝ → ℂ}
    (hr : ∀ n, 0 < r n ∧ r n < 1) (hanti : StrictAnti r)
    (hlen : ∀ n, arcLength f ξ (r n) < ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    (hγ : ∀ n, ContinuousOn (γ n) (Icc 0 1) ∧ InjOn (γ n) (Ioo 0 1) ∧
      γ n '' Ioo 0 1 = f '' (unitDisc ∩ sphere ξ (r n)) ∧ γ n 0 ∈ frontier Ω ∧ γ n 1 ∈ frontier Ω)
    (hends : ∀ n, γ (n + 1) 0 ≠ γ n 0 ∧ γ (n + 1) 0 ≠ γ n 1 ∧ γ (n + 1) 1 ≠ γ n 0 ∧
      γ (n + 1) 1 ≠ γ n 1) :
    IsNullChain Ω (pe5_circ f ξ r) := by
  show IsNullChain Ω (fun n => f '' (unitDisc ∩ sphere ξ (r n)))
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfr : ∀ {z : ℂ}, z ∈ frontier Ω → z ∉ Ω := fun hz => by
    rw [hΩo.frontier_eq] at hz
    exact hz.2
  have hCΩ : ∀ n, f '' (unitDisc ∩ sphere ξ (r n)) ⊆ Ω := fun n => by
    rw [← hf.2.2]
    exact image_mono inter_subset_left
  have hdisj : ∀ m n, m ≠ n →
      Disjoint (f '' (unitDisc ∩ sphere ξ (r m))) (f '' (unitDisc ∩ sphere ξ (r n))) :=
    fun m n hmn => pe6_disjoint_image_arc hf.2.1 (hanti.injective.ne hmn)
  have hcl : ∀ n, closure (f '' (unitDisc ∩ sphere ξ (r n))) ⊆
      f '' (unitDisc ∩ sphere ξ (r n)) ∪ {γ n 0, γ n 1} := by
    intro n
    obtain ⟨hc, -, himg, -, -⟩ := hγ n
    rw [← himg, pe6_closure_image_Ioo hc]
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact Or.inr (Or.inl (congrArg (γ n) h0.symm))
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · exact Or.inr (Or.inr (congrArg (γ n) h1))
      · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩
  refine ⟨fun n => ?_, fun n => ?_, fun n hn => ?_, ?_⟩
  · obtain ⟨hc, hi, himg, h0, h1⟩ := hγ n
    exact ⟨γ n, hc, hi, himg, hCΩ n, h0, h1⟩
  · refine Set.disjoint_of_subset (hcl n) (hcl (n + 1)) ?_
    obtain ⟨-, -, -, h0n, h1n⟩ := hγ n
    obtain ⟨-, -, -, h0m, h1m⟩ := hγ (n + 1)
    obtain ⟨e1, e2, e3, e4⟩ := hends n
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.1 (hdisj n (n + 1) (by omega)) hz hz'
    · simp only [mem_insert_iff, mem_singleton_iff] at hz'
      rcases hz' with rfl | rfl
      · exact hfr h0m (hCΩ n hz)
      · exact hfr h1m (hCΩ n hz)
    · simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hfr h0n (hCΩ (n + 1) hz')
      · exact hfr h1n (hCΩ (n + 1) hz')
    · simp only [mem_insert_iff, mem_singleton_iff] at hz hz'
      rcases hz with rfl | rfl
      · rcases hz' with h | h
        · exact e1 h.symm
        · exact e3 h.symm
      · rcases hz' with h | h
        · exact e2 h.symm
        · exact e4 h.symm
  · exact ⟨hdisj 0 n (by omega), fun x hx y hy =>
      pe6_connectedComponentIn_ne hf (hanti (Nat.lt_succ_self n)) (hanti (by omega : 0 < n)) hx hy⟩
  · refine squeeze_zero (fun n => Metric.diam_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨-, -, -, -, hd, -⟩ := exists_ends_of_circleArc_image hΩ hf hξ (hr n).1 (hr n).2 (hlen n).ne_top
    exact hd.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) (hlen n).le)

/-- **Circular chains with a pluggable step.**  `pe5_exists_radii_of_step` + `pe5_isNullChain_circ`; a predicate `G`
forcing `rₙ < 1/(n+1)` makes the radii tend to `0`. -/
theorem pe5_exists_circChain_of_step {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) (G : ℕ → ℝ → Prop)
    (h0 : ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ < ENNReal.ofReal 1 ∧ G 0 ρ)
    (hstep : ∀ (n : ℕ) (ρ : ℝ) (N : Set ℝ), 0 < ρ → volume N = 0 →
      ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' ∉ N ∧
        arcLength f ξ ρ' < ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) + 1)) ∧ G (n + 1) ρ')
    (hG : ∀ n ρ, G n ρ → ρ < 1 / ((n : ℝ) + 1)) :
    ∃ r, pe5_IsCircChain Ω f ξ r ∧ ∀ n, G n (r n) := by
  obtain ⟨r, γ, hG', hr, hanti, hlen, hγ, hends⟩ := pe5_exists_radii_of_step hΩ hf hξ G h0 hstep
  refine ⟨r, ⟨hr, hanti, ?_, pe5_isNullChain_circ hΩ hf hξ hr hanti hlen hγ hends⟩, hG'⟩
  exact squeeze_zero (fun n => (hr n).1.le) (fun n => (hG n (r n) (hG' n)).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The canonical circular chain** at a point of the circle: `pe5_exists_circChain_of_step` with
`G n ρ := ρ < 1/(n+1)`, each radius from `pe6_exists_radius_notMem`. -/
theorem pe5_exists_circChain {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) : ∃ r, pe5_IsCircChain Ω f ξ r := by
  have h0 : ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ arcLength f ξ ρ < ENNReal.ofReal 1 ∧ ρ < 1 / (((0 : ℕ) : ℝ) + 1) := by
    obtain ⟨ρ, hρ0, hρ1, -, -, hρlen⟩ := pe6_exists_radius_notMem hΩ hf ξ one_pos one_pos (N := ∅) measure_empty
    exact ⟨ρ, hρ0, hρ1, hρlen, by simpa using hρ1⟩
  have hstep : ∀ (n : ℕ) (ρ : ℝ) (N : Set ℝ), 0 < ρ → volume N = 0 →
      ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' ∉ N ∧
        arcLength f ξ ρ' < ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) + 1)) ∧ ρ' < 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
    intro n ρ N hρ hN
    have hε : (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    obtain ⟨ρ', h1, h2, h3, h4, h5⟩ := pe6_exists_radius_notMem hΩ hf ξ (lt_min hρ hε) hε hN
    exact ⟨ρ', h1, h2.trans_le (min_le_left _ _), h3, h4, h5, h2.trans_le (min_le_right _ _)⟩
  obtain ⟨r, hr, -⟩ := pe5_exists_circChain_of_step hΩ hf hξ (fun n ρ => ρ < 1 / ((n : ℝ) + 1)) h0 hstep
    (fun n ρ h => h)
  exact ⟨r, hr⟩

/-- The ends of a null-chain of `f(Δ)` decrease (`car3_chainEnd_succ_subset`). -/
theorem pe5_chainEnd_mono {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ}
    (hC : IsNullChain Ω C) {m n : ℕ} (hmn : m ≤ n) : chainEnd Ω C n ⊆ chainEnd Ω C m := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩc : IsPreconnected Ω := by
    rw [← hf.2.2]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image f hf.1.continuousOn
  exact antitone_nat_of_succ_le (f := chainEnd Ω C) (car3_chainEnd_succ_subset hΩo hΩc hC) hmn

/-- **A preconnected set meeting an end lies in it**, if it misses the crosscut: `chainEnd n` is a component of
`Ω ∖ Cₙ` (`car3_chainEnd_eq`). -/
theorem pe5_subset_chainEnd {Ω : Set ℂ} {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) {S : Set ℂ}
    (hS : IsPreconnected S) (hSΩ : S ⊆ Ω \ C n) (hSV : (S ∩ chainEnd Ω C n).Nonempty) :
    S ⊆ chainEnd Ω C n := by
  obtain ⟨x, hxS, hxV⟩ := hSV
  obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hC.1 (n + 1))
  rw [car3_chainEnd_eq hC n hy] at hxV ⊢
  rw [connectedComponentIn_eq hxV]
  exact hS.subset_connectedComponentIn hxS hSΩ

/-- **A preconnected set that enters an end and leaves it meets the crosscut.** -/
theorem pe5_crosscut_meets {Ω : Set ℂ} {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) {S : Set ℂ}
    (hS : IsPreconnected S) (hSΩ : S ⊆ Ω) (hSV : (S ∩ chainEnd Ω C n).Nonempty) {q : ℂ} (hqS : q ∈ S)
    (hq : q ∉ chainEnd Ω C n) : (S ∩ C n).Nonempty := by
  by_contra hne
  refine hq (pe5_subset_chainEnd hC n hS (fun z hz => ⟨hSΩ hz, fun hzC => hne ⟨z, hz, hzC⟩⟩) hSV hqS)

/-- **The ends of a circular chain** are the images of the half-discs: `chainEnd n = f(Δ ∩ ball ξ rₙ)`.  (⊇) is the
argument of `pe6_exists_nullChain_clusterSet_subset`; (⊆): `f(Δ ∩ ball ξ rₙ)` and `f(Δ ∖ closedBall ξ rₙ)` are disjoint
open sets covering `Ω ∖ Cₙ`. -/
theorem pe5_chainEnd_circ {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {r : ℕ → ℝ} (hr : pe5_IsCircChain Ω f ξ r) (n : ℕ) :
    chainEnd Ω (pe5_circ f ξ r) n = f '' (unitDisc ∩ ball ξ (r n)) := by
  obtain ⟨hr01, hanti, -, hnull⟩ := hr
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hy₀ := pe6_mem_arc hξ (hr01 (n + 1)).1 (hr01 (n + 1)).2
  have hy₀C : f (((1 - r (n + 1) : ℝ) : ℂ) * ξ) ∈ pe5_circ f ξ r (n + 1) := ⟨_, hy₀, rfl⟩
  rw [car3_chainEnd_eq hnull n hy₀C]
  have hopen_img : ∀ U ⊆ unitDisc, IsOpen U → IsOpen (f '' U) := fun U hU hUo =>
    (show IsConformalOnto f U (f '' U) from ⟨hf.1.mono hU, hf.2.1.mono hU, rfl⟩).isOpen hUo
  have hy₀S : f (((1 - r (n + 1) : ℝ) : ℂ) * ξ) ∈ f '' (unitDisc ∩ ball ξ (r n)) := by
    refine ⟨_, ⟨hy₀.1, ?_⟩, rfl⟩
    rw [mem_ball, mem_sphere.1 hy₀.2]
    exact hanti (Nat.lt_succ_self n)
  have hSF : f '' (unitDisc ∩ ball ξ (r n)) ⊆ Ω \ pe5_circ f ξ r n := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hf.mapsTo hz.1, ?_⟩
    rintro ⟨u, hu, hfu⟩
    have huz : u = z := hf.2.1 hu.1 hz.1 hfu
    subst huz
    exact (mem_ball.1 hz.2).ne (mem_sphere.1 hu.2)
  apply Subset.antisymm
  · have hu : IsOpen (f '' (unitDisc ∩ ball ξ (r n))) :=
      hopen_img _ inter_subset_left (hΔo.inter isOpen_ball)
    have hv : IsOpen (f '' (unitDisc \ closedBall ξ (r n))) :=
      hopen_img _ Set.sdiff_subset (hΔo.sdiff isClosed_closedBall)
    have huv : Disjoint (f '' (unitDisc ∩ ball ξ (r n))) (f '' (unitDisc \ closedBall ξ (r n))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ ⟨u, hu, hfu⟩
      have huz : u = z := hf.2.1 hu.1 hz.1 hfu
      subst huz
      exact hu.2 (ball_subset_closedBall hz.2)
    have hcov : Ω \ pe5_circ f ξ r n ⊆
        f '' (unitDisc ∩ ball ξ (r n)) ∪ f '' (unitDisc \ closedBall ξ (r n)) := by
      rintro w ⟨hwΩ, hwC⟩
      obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf hwΩ
      rcases lt_trichotomy (dist (pe2_ginv f w) ξ) (r n) with h | h | h
      · exact Or.inl ⟨_, ⟨hgD, h⟩, hfg⟩
      · exact (hwC ⟨_, ⟨hgD, h⟩, hfg⟩).elim
      · exact Or.inr ⟨_, ⟨hgD, fun h' => (not_le.2 h) (mem_closedBall.1 h')⟩, hfg⟩
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hu hv huv
      ((connectedComponentIn_subset _ _).trans hcov) ⟨_, mem_connectedComponentIn (hSF hy₀S), hy₀S⟩
  · exact (((convex_ball (0 : ℂ) 1).inter (convex_ball ξ (r n))).isPreconnected.image f
      (hf.1.continuousOn.mono inter_subset_left)).subset_connectedComponentIn hy₀S hSF

/-- **Two circular chains at the same point are equivalent** (their ends are `f(Δ ∩ ball ξ ·)` and the radii tend
to `0`). -/
theorem pe5_circ_equiv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {r r' : ℕ → ℝ} (hr : pe5_IsCircChain Ω f ξ r) (hr' : pe5_IsCircChain Ω f ξ r') :
    NullChainEquiv Ω (pe5_circ f ξ r) (pe5_circ f ξ r') := by
  have key : ∀ {r r' : ℕ → ℝ}, pe5_IsCircChain Ω f ξ r → pe5_IsCircChain Ω f ξ r' →
      ∀ m, ∃ n, chainEnd Ω (pe5_circ f ξ r) n ⊆ chainEnd Ω (pe5_circ f ξ r') m := by
    intro r r' hr hr' m
    obtain ⟨n, hn⟩ := (hr.2.2.1.eventually_lt_const (hr'.1 m).1).exists
    refine ⟨n, ?_⟩
    rw [pe5_chainEnd_circ hf hξ hr n, pe5_chainEnd_circ hf hξ hr' m]
    exact image_mono (inter_subset_inter_right _ (ball_subset_ball hn.le))
  exact ⟨key hr hr', key hr' hr⟩

/-- **The impression of a circular chain is the cluster set** of `f` at `ξ`. -/
theorem pe5_circ_impression {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {r : ℕ → ℝ} (hr : pe5_IsCircChain Ω f ξ r) :
    chainImpression Ω (pe5_circ f ξ r) = clusterSet f unitDisc ξ := by
  have hE := pe5_chainEnd_circ hf hξ hr
  unfold chainImpression clusterSet
  simp only [hE]
  apply Subset.antisymm
  · refine subset_iInter₂ fun ρ hρ => ?_
    obtain ⟨n, hn⟩ := (hr.2.2.1.eventually_lt_const hρ).exists
    exact (iInter_subset _ n).trans
      (closure_mono (image_mono (inter_subset_inter_right _ (ball_subset_ball hn.le))))
  · exact subset_iInter fun n => iInter₂_subset (r n) (hr.1 n).1

/-- **Circular chains at distinct points are inequivalent**: a small half-disc at `ξ` cannot lie in a small half-disc
at `ξ' ≠ ξ` (injectivity of `f`). -/
theorem pe5_eq_of_circ_equiv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ ξ' : ℂ}
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) {r r' : ℕ → ℝ} (hr : pe5_IsCircChain Ω f ξ r)
    (hr' : pe5_IsCircChain Ω f ξ' r') (h : NullChainEquiv Ω (pe5_circ f ξ r) (pe5_circ f ξ' r')) :
    ξ = ξ' := by
  by_contra hne
  have hd : 0 < dist ξ ξ' := dist_pos.2 hne
  obtain ⟨m, hm⟩ := (hr'.2.2.1.eventually_lt_const (half_pos hd)).exists
  obtain ⟨n, hn⟩ := h.1 m
  rw [pe5_chainEnd_circ hf hξ hr n, pe5_chainEnd_circ hf hξ' hr' m] at hn
  have hmin : 0 < min (r n) (dist ξ ξ' / 2) := lt_min (hr.1 n).1 (half_pos hd)
  have ht0 : 0 < min (r n) (dist ξ ξ' / 2) / 2 := half_pos hmin
  have htr : min (r n) (dist ξ ξ' / 2) / 2 < r n := by
    have := min_le_left (r n) (dist ξ ξ' / 2)
    linarith
  have htd : min (r n) (dist ξ ξ' / 2) / 2 ≤ dist ξ ξ' / 4 := by
    have := min_le_right (r n) (dist ξ ξ' / 2)
    linarith
  have hz := pe6_mem_arc hξ ht0 (htr.trans (hr.1 n).2)
  obtain ⟨u, hu, hfu⟩ := hn ⟨_, ⟨hz.1, by rw [mem_ball, mem_sphere.1 hz.2]; exact htr⟩, rfl⟩
  have huz := hf.2.1 hu.1 hz.1 hfu
  rw [huz] at hu
  have h1 := (mem_ball.1 hu.2).trans hm
  have h2 := mem_sphere.1 hz.2
  have h3 := dist_triangle_left ξ ξ' (((1 - min (r n) (dist ξ ξ' / 2) / 2 : ℝ) : ℂ) * ξ)
  linarith

/-! ### Stage B (PE2): every null-chain is equivalent to a circular chain -/

/-- A compact set and a disjoint closed set of `ℂ` are at positive distance. -/
theorem pe5_exists_pos_le_dist {s t : Set ℂ} (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ δ > (0 : ℝ), ∀ x ∈ s, ∀ y ∈ t, δ ≤ dist x y := by
  obtain ⟨r, hr, h⟩ := Metric.exists_pos_forall_lt_edist hs ht hst
  refine ⟨r, NNReal.coe_pos.2 hr, fun x hx y hy => ?_⟩
  have h1 := h x hx y hy
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at h1
  exact h1.1.le

/-- **A point of `Ω` eventually leaves the ends** of a null-chain: it is not in the impression (`⊆ ∂Ω`), and the ends
decrease. -/
theorem pe5_eventually_notMem_chainEnd {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {q : ℂ} (hq : q ∈ Ω) :
    ∃ N, ∀ n, N ≤ n → q ∉ chainEnd Ω C n := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hqI : q ∉ chainImpression Ω C := fun h => by
    have h1 := (chainImpression_isCompact_isConnected hΩ hf hC).2.2 h
    rw [hΩo.frontier_eq] at h1
    exact h1.2 hq
  simp only [chainImpression, mem_iInter, not_forall] at hqI
  obtain ⟨N, hN⟩ := hqI
  exact ⟨N, fun n hn hqn => hN (subset_closure (pe5_chainEnd_mono hf hC hn hqn))⟩

/-- **Intermediate values on an image sphere.**  A preconnected `S ⊆ Ω` containing points `a`, `b` with
`|f⁻¹ a - ξ| ≤ ρ ≤ |f⁻¹ b - ξ|` meets `f(Δ ∩ sphere ξ ρ)`. -/
theorem pe5_exists_mem_image_sphere {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {S : Set ℂ} (hS : IsPreconnected S) (hSΩ : S ⊆ Ω) {ξ : ℂ} {ρ : ℝ} {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hal : dist (pe2_ginv f a) ξ ≤ ρ) (hbl : ρ ≤ dist (pe2_ginv f b) ξ) :
    (S ∩ f '' (unitDisc ∩ sphere ξ ρ)).Nonempty := by
  have hgc : ContinuousOn (pe2_ginv f) Ω := (hf.symm isOpen_ball).1.continuousOn
  obtain ⟨y, hyS, hy⟩ := hS.intermediate_value (f := fun w => dist (pe2_ginv f w) ξ) ha hb
    ((continuous_id.dist continuous_const).comp_continuousOn (hgc.mono hSΩ)) ⟨hal, hbl⟩
  obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf (hSΩ hyS)
  exact ⟨y, hyS, pe2_ginv f y, ⟨hgD, hy⟩, hfg⟩

/-- **The limit points of the ends lie on the circle** (Stage B4): a point `z ∈ Δ` of `⋂ₙ closure f⁻¹(Vₙ)` would give
`f z ∈ chainImpression ⊆ ∂Ω`, against `f z ∈ Ω`. -/
theorem pe5_norm_eq_one_of_mem_closure_ends {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {z : ℂ}
    (hz : ∀ n, z ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)) : ‖z‖ = 1 := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hz1 : ‖z‖ ≤ 1 := by
    have h := closure_mono (inter_subset_left (s := unitDisc)) (hz 0)
    rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff] at h
    exact h
  refine le_antisymm hz1 (not_lt.1 fun hlt => ?_)
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hlt
  have hfc : ContinuousAt f z := (hf.1.differentiableAt (isOpen_ball.mem_nhds hzD)).continuousAt
  have hI : f z ∈ chainImpression Ω C := by
    refine mem_iInter.2 fun n => closure_mono ?_ (mem_closure_image hfc (hz n))
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2
  have h1 := (chainImpression_isCompact_isConnected hΩ hf hC).2.2 hI
  rw [hΩo.frontier_eq] at h1
  exact h1.2 (hf.mapsTo hzD)

/-- **The limit set of the ends is nonempty** (Stage B5): nested nonempty compacts `closure f⁻¹(Vₙ)`. -/
theorem pe5_exists_mem_closure_ends {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) :
    ∃ z, ∀ n, z ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n) := by
  have hKd : ∀ n, closure (unitDisc ∩ f ⁻¹' chainEnd Ω C (n + 1)) ⊆
      closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n) := fun n =>
    closure_mono (inter_subset_inter_right _ (preimage_mono (pe5_chainEnd_mono hf hC (Nat.le_succ n))))
  have hKne : ∀ n, (closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)).Nonempty := by
    intro n
    obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hC.1 (n + 1))
    have hyV : y ∈ chainEnd Ω C n := by
      rw [car3_chainEnd_eq hC n hy]
      exact mem_connectedComponentIn (car3_mem_diff_of_succ hC n hy)
    obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf (car3_crosscut_subset (hC.1 (n + 1)) hy)
    refine ⟨pe2_ginv f y, subset_closure ⟨hgD, ?_⟩⟩
    show f (pe2_ginv f y) ∈ chainEnd Ω C n
    rw [hfg]
    exact hyV
  have hK0 : IsCompact (closure (unitDisc ∩ f ⁻¹' chainEnd Ω C 0)) :=
    (isBounded_ball.subset inter_subset_left).isCompact_closure
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)) hKd hKne hK0 (fun n => isClosed_closure)
  exact ⟨z, fun n => mem_iInter.1 hz n⟩

/-- **An end meets the small image spheres** about a limit point of the ends: if `ζ, ζ'` lie in
`closure f⁻¹(Vₙ)` and `0 < ρ < |ζ - ζ'|`, then `Vₙ` meets `f(Δ ∩ sphere ζ ρ)` (intermediate values on the
preconnected `Vₙ`). -/
theorem pe5_chainEnd_meets_image_sphere {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) (n : ℕ) {ζ ζ' : ℂ}
    (hζ : ζ ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n))
    (hζ' : ζ' ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < dist ζ ζ') :
    (chainEnd Ω C n ∩ f '' (unitDisc ∩ sphere ζ ρ)).Nonempty := by
  obtain ⟨y, hy⟩ := car3_crosscut_nonempty (hC.1 (n + 1))
  have hVp : IsPreconnected (chainEnd Ω C n) := by
    rw [car3_chainEnd_eq hC n hy]
    exact isPreconnected_connectedComponentIn
  have hVΩ : chainEnd Ω C n ⊆ Ω := by
    rw [car3_chainEnd_eq hC n hy]
    exact (connectedComponentIn_subset _ _).trans Set.sdiff_subset
  obtain ⟨u, hu, hud⟩ := Metric.mem_closure_iff.1 hζ ρ hρ0
  obtain ⟨u', hu', hud'⟩ := Metric.mem_closure_iff.1 hζ' (dist ζ ζ' - ρ) (by linarith)
  have hgu : pe2_ginv f (f u) = u := hf.2.1.leftInvOn_invFunOn hu.1
  have hgu' : pe2_ginv f (f u') = u' := hf.2.1.leftInvOn_invFunOn hu'.1
  refine pe5_exists_mem_image_sphere hf hVp hVΩ (show f u ∈ chainEnd Ω C n from hu.2)
    (show f u' ∈ chainEnd Ω C n from hu'.2) ?_ ?_
  · rw [hgu, dist_comm]
    exact hud.le
  · rw [hgu']
    have h1 := dist_triangle ζ u' ζ'
    have h2 := dist_comm ζ u'
    have h3 := dist_comm u' ζ'
    linarith

/-- **The heart of Stage B: the limit set of the ends is a single point.**  If `ζ ≠ ζ'` both lie in every
`closure f⁻¹(Vₙ)`, take the circular chain `r` at `ζ` (`‖ζ‖ = 1`) and `k` with `r_k < |ζ - ζ'|`.  The closures of the
circular crosscuts `k`, `k+1` are disjoint compacts, at distance `δ > 0`.  For `n` large, `diam Cₙ < δ` and fixed points
of both circular crosscuts are outside `Vₙ`; each circular crosscut meets `Vₙ`
(`pe5_chainEnd_meets_image_sphere`), hence meets `Cₙ` (`pe5_crosscut_meets`), and `δ ≤ diam Cₙ`. -/
theorem pe5_eq_of_mem_closure_ends {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {ζ ζ' : ℂ}
    (hζ : ∀ n, ζ ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n))
    (hζ' : ∀ n, ζ' ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)) : ζ = ζ' := by
  by_contra hne
  have hd : 0 < dist ζ ζ' := dist_pos.2 hne
  obtain ⟨r, hr⟩ := pe5_exists_circChain hΩ hf (pe5_norm_eq_one_of_mem_closure_ends hΩ hf hC hζ)
  obtain ⟨hr01, hanti, hr0, hnull⟩ := hr
  obtain ⟨k, hk⟩ := (hr0.eventually_lt_const hd).exists
  have hcΩ : ∀ j, pe5_circ f ζ r j ⊆ Ω := fun j => car3_crosscut_subset (hnull.1 j)
  obtain ⟨δ, hδ, hδd⟩ := pe5_exists_pos_le_dist (hΩ.subset (hcΩ k)).isCompact_closure isClosed_closure
    (hnull.2.1 k)
  obtain ⟨q₀, hq₀⟩ := car3_crosscut_nonempty (hnull.1 k)
  obtain ⟨q₁, hq₁⟩ := car3_crosscut_nonempty (hnull.1 (k + 1))
  obtain ⟨N₀, hN₀⟩ := pe5_eventually_notMem_chainEnd hΩ hf hC (hcΩ k hq₀)
  obtain ⟨N₁, hN₁⟩ := pe5_eventually_notMem_chainEnd hΩ hf hC (hcΩ (k + 1) hq₁)
  obtain ⟨N₂, hN₂⟩ := (hC.2.2.2.eventually_lt_const hδ).exists_forall_of_atTop
  obtain ⟨n, hn₀, hn₁, hn₂⟩ : ∃ n, N₀ ≤ n ∧ N₁ ≤ n ∧ N₂ ≤ n :=
    ⟨max (max N₀ N₁) N₂, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  have hmeet : ∀ j, r j < dist ζ ζ' → ∀ q ∈ pe5_circ f ζ r j, q ∉ chainEnd Ω C n →
      (pe5_circ f ζ r j ∩ C n).Nonempty := by
    intro j hj q hq hqn
    obtain ⟨x, hx1, hx2⟩ := pe5_chainEnd_meets_image_sphere hf hC n (hζ n) (hζ' n) (hr01 j).1 hj
    exact pe5_crosscut_meets hC n (car3_crosscut_isPreconnected (hnull.1 j)) (hcΩ j) ⟨x, hx2, hx1⟩ hq hqn
  obtain ⟨p₀, hp₀c, hp₀C⟩ := hmeet k hk q₀ hq₀ (hN₀ n hn₀)
  obtain ⟨p₁, hp₁c, hp₁C⟩ := hmeet (k + 1) ((hanti (Nat.lt_succ_self k)).trans hk) q₁ hq₁ (hN₁ n hn₁)
  have h1 := hδd p₀ (subset_closure hp₀c) p₁ (subset_closure hp₁c)
  have h2 : dist p₀ p₁ ≤ Metric.diam (C n) :=
    Metric.dist_le_diam_of_mem (hΩ.subset (car3_crosscut_subset (hC.1 n))) hp₀C hp₁C
  have h3 := hN₂ n hn₂
  linarith

/-- **The ends shrink to the limit point** (Stage B7): if `ζ` lies in every `closure f⁻¹(Vₙ)`, then
`f⁻¹(Vₙ) ⊆ ball ζ ε` for some `n` (else nested compacts `closure f⁻¹(Vₙ) ∖ ball ζ ε` give a second limit point). -/
theorem pe5_ends_subset_ball {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {ζ : ℂ}
    (hζ : ∀ n, ζ ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, unitDisc ∩ f ⁻¹' chainEnd Ω C n ⊆ ball ζ ε := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hKd : ∀ n, closure (unitDisc ∩ f ⁻¹' chainEnd Ω C (n + 1)) \ ball ζ ε ⊆
      closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n) \ ball ζ ε := fun n =>
    Set.sdiff_subset_sdiff_left
      (closure_mono (inter_subset_inter_right _ (preimage_mono (pe5_chainEnd_mono hf hC (Nat.le_succ n)))))
  have hKne : ∀ n, (closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n) \ ball ζ ε).Nonempty := by
    intro n
    obtain ⟨z, hz, hzb⟩ := not_subset.1 (hcon n)
    exact ⟨z, subset_closure hz, hzb⟩
  have hK0 : IsCompact (closure (unitDisc ∩ f ⁻¹' chainEnd Ω C 0) \ ball ζ ε) :=
    (isBounded_ball.subset inter_subset_left).isCompact_closure.diff isOpen_ball
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n) \ ball ζ ε) hKd hKne hK0
    (fun n => isClosed_closure.sdiff isOpen_ball)
  rw [mem_iInter] at hz
  have hzζ : z = ζ := pe5_eq_of_mem_closure_ends hΩ hf hC (fun n => (hz n).1) hζ
  exact (hz 0).2 (by rw [hzζ]; exact mem_ball_self hε)

/-- **Two curves** (Stage B8, the second half of Pommerenke Prop. 2.14 with circular arcs): a point `ζ` of the
circle is not in both `closure f⁻¹(C_m)` and `closure f⁻¹(C_{m+1})`.  Otherwise a small circular crosscut at `ζ`
(diameter `< δ = dist (closure C_m) (closure C_{m+1})`) would meet both `C_m` and `C_{m+1}` (intermediate values on
the preconnected crosscuts, which also reach points far from `ζ` in the disc). -/
theorem pe5_two_curves {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (m : ℕ) : ζ ∉ closure (unitDisc ∩ f ⁻¹' C m) ∨ ζ ∉ closure (unitDisc ∩ f ⁻¹' C (m + 1)) := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨hm, hm1⟩ := hcon
  have hCΩ : ∀ j, C j ⊆ Ω := fun j => car3_crosscut_subset (hC.1 j)
  obtain ⟨δ, hδ, hδd⟩ := pe5_exists_pos_le_dist (hΩ.subset (hCΩ m)).isCompact_closure isClosed_closure
    (hC.2.1 m)
  have hfar : ∀ j, ∃ b ∈ C j, 0 < dist (pe2_ginv f b) ζ := by
    intro j
    obtain ⟨b, hb⟩ := car3_crosscut_nonempty (hC.1 j)
    obtain ⟨hgD, -⟩ := pe2_ginv_mem hf (hCΩ j hb)
    refine ⟨b, hb, dist_pos.2 fun h => ?_⟩
    rw [h] at hgD
    have h1 := mem_ball_zero_iff.1 hgD
    rw [hζ] at h1
    exact lt_irrefl _ h1
  obtain ⟨b₀, hb₀, hb₀d⟩ := hfar m
  obtain ⟨b₁, hb₁, hb₁d⟩ := hfar (m + 1)
  obtain ⟨r, hr⟩ := pe5_exists_circChain hΩ hf hζ
  obtain ⟨hr01, -, hr0, hnull⟩ := hr
  obtain ⟨k, hk₀, hk₁, hkd⟩ : ∃ k, r k < dist (pe2_ginv f b₀) ζ ∧ r k < dist (pe2_ginv f b₁) ζ ∧
      Metric.diam (pe5_circ f ζ r k) < δ :=
    ((hr0.eventually_lt_const hb₀d).and ((hr0.eventually_lt_const hb₁d).and
      (hnull.2.2.2.eventually_lt_const hδ))).exists
  have hmeet : ∀ j, ζ ∈ closure (unitDisc ∩ f ⁻¹' C j) → ∀ b ∈ C j, r k < dist (pe2_ginv f b) ζ →
      (C j ∩ f '' (unitDisc ∩ sphere ζ (r k))).Nonempty := by
    intro j hj b hb hbd
    obtain ⟨u, hu, hud⟩ := Metric.mem_closure_iff.1 hj (r k) (hr01 k).1
    have hgu : pe2_ginv f (f u) = u := hf.2.1.leftInvOn_invFunOn hu.1
    refine pe5_exists_mem_image_sphere hf (car3_crosscut_isPreconnected (hC.1 j)) (hCΩ j)
      (show f u ∈ C j from hu.2) hb ?_ hbd.le
    rw [hgu, dist_comm]
    exact hud.le
  obtain ⟨p₀, hp₀C, hp₀c⟩ := hmeet m hm b₀ hb₀ hk₀
  obtain ⟨p₁, hp₁C, hp₁c⟩ := hmeet (m + 1) hm1 b₁ hb₁ hk₁
  have h1 := hδd p₀ (subset_closure hp₀C) p₁ (subset_closure hp₁C)
  have h2 : dist p₀ p₁ ≤ Metric.diam (pe5_circ f ζ r k) :=
    Metric.dist_le_diam_of_mem (hΩ.subset (car3_crosscut_subset (hnull.1 k))) hp₀c hp₁c
  linarith

/-- **A small half-disc lies in an end** (Stage B9): if `ζ` lies in every `closure f⁻¹(Vₙ)` but not in
`closure f⁻¹(C_m)`, then `f(Δ ∩ ball ζ ε) ⊆ V_m` for some `ε > 0` (`pe5_subset_chainEnd`). -/
theorem pe5_ball_subset_chainEnd {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) {ζ : ℂ} (hζ : ∀ n, ζ ∈ closure (unitDisc ∩ f ⁻¹' chainEnd Ω C n))
    {m : ℕ} (hm : ζ ∉ closure (unitDisc ∩ f ⁻¹' C m)) :
    ∃ ε > (0 : ℝ), f '' (unitDisc ∩ ball ζ ε) ⊆ chainEnd Ω C m := by
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl ζ hm
  refine ⟨ε, hε, pe5_subset_chainEnd hC m ?_ ?_ ?_⟩
  · exact ((convex_ball (0 : ℂ) 1).inter (convex_ball ζ ε)).isPreconnected.image f
      (hf.1.continuousOn.mono inter_subset_left)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨hf.mapsTo hz.1, fun hzC => hεb hz.2 (subset_closure ⟨hz.1, hzC⟩)⟩
  · obtain ⟨u, hu, hud⟩ := Metric.mem_closure_iff.1 (hζ m) ε hε
    exact ⟨f u, ⟨u, ⟨hu.1, by rw [mem_ball, dist_comm]; exact hud⟩, rfl⟩, hu.2⟩

/-- **Surjectivity (Pommerenke Thm 2.15 (c), run on the ends).**  Every null-chain is equivalent to every circular
chain at the limit point `ζ ∈ 𝕋` of its ends: the ends shrink to `ζ` (`pe5_ends_subset_ball`), and by the two-curves
step a half-disc at `ζ` lies in each end (`pe5_two_curves`, `pe5_ball_subset_chainEnd`). -/
theorem pe5_exists_equiv_circ {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {C : ℕ → Set ℂ} (hC : IsNullChain Ω C) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ∀ r, pe5_IsCircChain Ω f ξ r → NullChainEquiv Ω C (pe5_circ f ξ r) := by
  obtain ⟨ζ, hζ⟩ := pe5_exists_mem_closure_ends hf hC
  have hζ1 := pe5_norm_eq_one_of_mem_closure_ends hΩ hf hC hζ
  have hVΩ : ∀ n, chainEnd Ω C n ⊆ Ω := fun n =>
    iUnion₂_subset fun y _ => (connectedComponentIn_subset _ _).trans Set.sdiff_subset
  refine ⟨ζ, hζ1, fun r hr => ⟨fun m => ?_, fun m => ?_⟩⟩
  · obtain ⟨n, hn⟩ := pe5_ends_subset_ball hΩ hf hC hζ (hr.1 m).1
    refine ⟨n, fun w hw => ?_⟩
    rw [pe5_chainEnd_circ hf hζ1 hr m]
    obtain ⟨hgD, hfg⟩ := pe2_ginv_mem hf (hVΩ n hw)
    have hgV : pe2_ginv f w ∈ unitDisc ∩ f ⁻¹' chainEnd Ω C n := by
      refine ⟨hgD, ?_⟩
      show f (pe2_ginv f w) ∈ chainEnd Ω C n
      rw [hfg]
      exact hw
    exact ⟨pe2_ginv f w, ⟨hgD, hn hgV⟩, hfg⟩
  · obtain ⟨m', hmm', hm'⟩ : ∃ m', m ≤ m' ∧ ζ ∉ closure (unitDisc ∩ f ⁻¹' C m') := by
      rcases pe5_two_curves hΩ hf hC hζ1 m with h | h
      · exact ⟨m, le_rfl, h⟩
      · exact ⟨m + 1, Nat.le_succ m, h⟩
    obtain ⟨ε, hε, hεV⟩ := pe5_ball_subset_chainEnd hf hC hζ hm'
    obtain ⟨n, hn⟩ := (hr.2.2.1.eventually_lt_const hε).exists
    refine ⟨n, ?_⟩
    rw [pe5_chainEnd_circ hf hζ1 hr n]
    exact (image_mono (inter_subset_inter_right _ (ball_subset_ball hn.le))).trans
      (hεV.trans (pe5_chainEnd_mono hf hC hmm'))

/-! ### Stage C (PE2): Theorem 2.15 -/

/-- **The prime-end correspondence.**  `P ζ` is the class of a circular chain at `ζ`; a null-chain represents `P ζ`
iff it is equivalent to every circular chain at `ζ`; `P` is injective (`pe5_eq_of_circ_equiv`) and surjective
(`pe5_exists_equiv_circ`). -/
theorem pe5_exists_P {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧ ∀ ζ : Circle,
      ∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C},
        (Quot.mk _ c = P ζ ↔ ∀ r, pe5_IsCircChain Ω f ζ r → NullChainEquiv Ω c.1 (pe5_circ f ζ r)) := by
  choose R hR using fun ζ : Circle => pe5_exists_circChain hΩ hf (Circle.norm_coe ζ)
  have hchar : ∀ ζ : Circle, ∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C},
      ((Quot.mk _ c : PrimeEnd Ω) = Quot.mk _ ⟨pe5_circ f ζ (R ζ), (hR ζ).2.2.2⟩ ↔
        ∀ r, pe5_IsCircChain Ω f ζ r → NullChainEquiv Ω c.1 (pe5_circ f ζ r)) := by
    intro ζ c
    constructor
    · intro h r hr
      exact pe5_nullChainEquiv_trans (pe5_quot_eq_iff.1 h) (pe5_circ_equiv hf (Circle.norm_coe ζ) (hR ζ) hr)
    · intro h
      exact pe5_quot_eq_iff.2 (h (R ζ) (hR ζ))
  refine ⟨fun ζ => Quot.mk _ ⟨pe5_circ f ζ (R ζ), (hR ζ).2.2.2⟩, ⟨fun ζ ζ' h => ?_, fun p => ?_⟩, hchar⟩
  · exact Circle.ext (pe5_eq_of_circ_equiv hf (Circle.norm_coe ζ) (Circle.norm_coe ζ') (hR ζ) (hR ζ')
      (pe5_quot_eq_iff.1 h))
  · obtain ⟨c, rfl⟩ := Quot.exists_rep p
    obtain ⟨ξ, hξ, hequiv⟩ := pe5_exists_equiv_circ hΩ hf c.2
    exact ⟨⟨ξ, mem_sphere_zero_iff_norm.2 hξ⟩, ((hchar ⟨ξ, mem_sphere_zero_iff_norm.2 hξ⟩ c).2 hequiv).symm⟩

/-- **The impression of a representative of `P ζ`** is the cluster set (class invariance of the impression,
`chainImpression_eq_of_nullChainEquiv`, and `pe5_circ_impression`). -/
theorem pe5_impression_eq_clusterSet {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {C : ℕ → Set ℂ}
    (hC : ∀ r, pe5_IsCircChain Ω f ξ r → NullChainEquiv Ω C (pe5_circ f ξ r)) :
    chainImpression Ω C = clusterSet f unitDisc ξ := by
  obtain ⟨r, hr⟩ := pe5_exists_circChain hΩ hf hξ
  rw [chainImpression_eq_of_nullChainEquiv (hC r hr), pe5_circ_impression hf hξ hr]

/-- **Theorem 2.15 (core of `caratheodory_primeEnd`).**  The statement of `caratheodory_primeEnd`. -/
theorem pe5_caratheodory_primeEnd_core {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧
      ∀ ζ : Circle, ∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = P ζ →
        chainImpression Ω c.1 = clusterSet f unitDisc ζ := by
  obtain ⟨P, hP, hchar⟩ := pe5_exists_P hΩ hf
  exact ⟨P, hP, fun ζ c hc => pe5_impression_eq_clusterSet hΩ hf (Circle.norm_coe ζ) ((hchar ζ c).1 hc)⟩

/-! ### Stage D (PE2): principal points and the radial cluster set -/

/-- **Radial points near a radial cluster point**: for `s₁ ∈ (0, 1)` and `ε > 0` some `s ∈ (0, s₁)` has
`|f((1 - s) ζ) - w| < ε`. -/
theorem pe9_exists_radial_point {f : ℂ → ℂ} {ζ w : ℂ} (hw : w ∈ radialClusterSet f ζ) {s₁ ε : ℝ}
    (hs₁ : 0 < s₁) (hs₁1 : s₁ < 1) (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < s₁ ∧ ‖f (((1 - s : ℝ) : ℂ) * ζ) - w‖ < ε := by
  simp only [radialClusterSet, mem_iInter] at hw
  obtain ⟨_, ⟨z, ⟨t, ht1, ht2, rfl⟩, rfl⟩, hd⟩ :=
    Metric.mem_closure_iff.1 (hw (1 - s₁) ⟨by linarith, by linarith⟩) ε hε
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  rw [sub_sub_cancel, ← dist_eq_norm, dist_comm]
  exact hd

/-- **Radial cluster points are not in `Ω`** (`tendsto_boundary_of_isConformalOnto` along radial points). -/
theorem pe9_radialClusterSet_notMem {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ζ w : ℂ}
    (hζ : ‖ζ‖ = 1) (hw : w ∈ radialClusterSet f ζ) : w ∉ Ω := by
  have hpt : ∀ n : ℕ, ∃ s, 0 < s ∧ s < 1 / ((n : ℝ) + 2) ∧
      ‖f (((1 - s : ℝ) : ℂ) * ζ) - w‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    exact pe9_exists_radial_point hw (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
      (by positivity)
  choose s hs0 hs1 hsw using hpt
  have hs1' : ∀ n : ℕ, s n < 1 / ((n : ℝ) + 1) := fun n =>
    (hs1 n).trans_le (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hslt : ∀ n : ℕ, s n < 1 := fun n => by
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    exact (hs1' n).trans_le (by rw [div_le_one (by positivity)]; linarith)
  have hs : Tendsto s atTop (𝓝 0) :=
    squeeze_zero (fun n => (hs0 n).le) (fun n => (hs1' n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_boundary_of_isConformalOnto hf hζ (z := fun n => ((1 - s n : ℝ) : ℂ) * ζ)
    (fun n => (pe6_mem_arc hζ (hs0 n) (hslt n)).1) ?_ ?_
  · rw [tendsto_iff_dist_tendsto_zero]
    exact hs.congr fun n => (mem_sphere.1 (pe6_mem_arc hζ (hs0 n) (hslt n)).2).symm
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hsw n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Wolff's length–area estimate in a window, with a local area.**  For `0 < a < b`, a null set `N` and
`B > 2π · A / log (b/a)`, where `A = area f(Δ ∩ ball z₀ b) < ∞`, some radius `ρ ∈ (a, b) ∖ N` has `ℓ(ρ)² < B`.

Proof: Pommerenke Prop. 2.2 / (2.2.6), with the area of `f(Δ ∩ ball z₀ b)` in place of that of `Ω`.  If
`ℓ(ρ)² ≥ B` for all `ρ ∈ (a, b) ∖ N`, Cauchy–Schwarz (`sq_arcLength_le`) gives `B/ρ ≤ 2π ∫_arc |f'|² ρ dθ` there;
the arcs of radius `ρ < b` lie in `ball z₀ b`, so integrating over `(a, b)` in polar coordinates about `z₀` gives
`B · log (b/a) ≤ 2π A`, a contradiction.  `A < ∞` (`hfin`) is needed for the `toReal`; `B > 0` follows from `hB`.
Uses: the proof of `pe6_exists_radius_sq_arcLength_lt_notMem` (copied), with `Ioo a b` for `Ioo δ (√δ)` and the
integrand `(ball z₀ b).indicator fun z => ‖deriv f z‖ₑ ^ 2`, whose integral over `Δ` is `A` by
`lintegral_image_conformal` on the open `Δ ∩ ball z₀ b`; `lintegral_unitDisc_eq_polar`,
`lintegral_Ioo_indicator_eq_arc` and `integral_inv` (`∫_a^b dρ/ρ = log (b/a)`). -/
theorem pe9_exists_radius_sq_arcLength_lt_window {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (z₀ : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfin : volume (f '' (unitDisc ∩ ball z₀ b)) ≠ ⊤) {B : ℝ}
    (hB : (volume (f '' (unitDisc ∩ ball z₀ b))).toReal * (2 * π) / Real.log (b / a) < B)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ ρ ∈ Ioo a b, ρ ∉ N ∧ arcLength f z₀ ρ ^ 2 < ENNReal.ofReal B := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hUo : IsOpen (unitDisc ∩ ball z₀ b) := isOpen_ball.inter isOpen_ball
  have hGm : Measurable ((ball z₀ b).indicator fun z => ‖deriv f z‖ₑ ^ 2) :=
    ((measurable_deriv f).enorm.pow_const 2).indicator measurableSet_ball
  have harea : ∫⁻ z in unitDisc, (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) z =
      volume (f '' (unitDisc ∩ ball z₀ b)) := by
    have h := lintegral_image_conformal hUo
      (show IsConformalOnto f (unitDisc ∩ ball z₀ b) (f '' (unitDisc ∩ ball z₀ b)) from
        ⟨hf.1.mono inter_subset_left, hf.2.1.mono inter_subset_left, rfl⟩) (fun _ => 1)
    simp only [mul_one, setLIntegral_one] at h
    rw [h, lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hpolar := lintegral_unitDisc_eq_polar z₀ hGm
  simp_rw [lintegral_Ioo_indicator_eq_arc] at hpolar
  rw [harea] at hpolar
  have hlog : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).2 hab)
  have hpt : ∀ ρ ∈ Ioo a b, ρ ∉ N →
      ENNReal.ofReal B * ENNReal.ofReal (1 / ρ) ≤ ENNReal.ofReal (2 * π) *
        ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
          (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) (circleMap z₀ ρ θ) * ENNReal.ofReal ρ := by
    intro ρ hρ hρN
    have hρ0 : 0 < ρ := ha.trans hρ.1
    have hG : ∀ θ : ℝ, (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) (circleMap z₀ ρ θ) =
        ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 := fun θ =>
      indicator_of_mem (mem_ball.2 ((mem_sphere.1 (circleMap_mem_sphere z₀ hρ0.le θ)).trans_lt hρ.2)) _
    simp_rw [hG]
    have h := (hcon ρ hρ hρN).trans (sq_arcLength_le f z₀ ρ)
    have hρρ : ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ) = 1 := by
      rw [← ENNReal.ofReal_mul hρ0.le, mul_one_div_cancel hρ0.ne', ENNReal.ofReal_one]
    calc ENNReal.ofReal B * ENNReal.ofReal (1 / ρ)
        ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) * ENNReal.ofReal (1 / ρ) :=
          mul_le_mul_left h _
      _ = ENNReal.ofReal (2 * π) *
            (∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              ‖deriv f (circleMap z₀ ρ θ)‖ₑ ^ 2 * ENNReal.ofReal ρ) *
            (ENNReal.ofReal ρ * ENNReal.ofReal (1 / ρ)) := by ring
      _ = _ := by rw [hρρ, mul_one]
  have hint : ∫⁻ ρ in Ioo a b, ENNReal.ofReal B * ENNReal.ofReal (1 / ρ)
      ≤ ENNReal.ofReal (2 * π) * volume (f '' (unitDisc ∩ ball z₀ b)) := by
    calc ∫⁻ ρ in Ioo a b, ENNReal.ofReal B * ENNReal.ofReal (1 / ρ)
        ≤ ∫⁻ ρ in Ioo a b, ENNReal.ofReal (2 * π) *
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) (circleMap z₀ ρ θ) * ENNReal.ofReal ρ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo,
            ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN)] with ρ hρ hρN
          exact hpt ρ hρ hρN
      _ = ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioo a b,
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) (circleMap z₀ ρ θ) * ENNReal.ofReal ρ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioi (0 : ℝ),
            ∫⁻ θ in {θ : ℝ | θ ∈ Ioc (-π) π ∧ circleMap z₀ ρ θ ∈ unitDisc},
              (ball z₀ b).indicator (fun z => ‖deriv f z‖ₑ ^ 2) (circleMap z₀ ρ θ) * ENNReal.ofReal ρ :=
          mul_le_mul_right (lintegral_mono_set fun ρ hρ => ha.trans hρ.1) _
      _ = ENNReal.ofReal (2 * π) * volume (f '' (unitDisc ∩ ball z₀ b)) := by rw [← hpolar]
  have hB0 : 0 ≤ B := le_trans (by positivity) hB.le
  have hleft : ∫⁻ ρ in Ioo a b, ENNReal.ofReal B * ENNReal.ofReal (1 / ρ)
      = ENNReal.ofReal (B * Real.log (b / a)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hInt : IntegrableOn (fun ρ : ℝ => 1 / ρ) (Ioo a b) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
      exact continuousOn_const.div continuousOn_id fun ρ hρ => (ha.trans_le hρ.1).ne'
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo a b)] fun ρ => 1 / ρ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
      exact (one_div_pos.2 (ha.trans hρ.1)).le
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, ← ENNReal.ofReal_mul hB0]
    congr 1
    rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hab.le]
    simp_rw [one_div]
    rw [integral_inv (Set.notMem_uIcc_of_lt ha (ha.trans hab))]
  have hRHS : ENNReal.ofReal (2 * π) * volume (f '' (unitDisc ∩ ball z₀ b)) =
      ENNReal.ofReal (2 * π * (volume (f '' (unitDisc ∩ ball z₀ b))).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π), ENNReal.ofReal_toReal hfin]
  rw [hleft, hRHS, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
  have : B ≤ (volume (f '' (unitDisc ∩ ball z₀ b))).toReal * (2 * π) / Real.log (b / a) := by
    rw [le_div_iff₀ hlog]
    nlinarith [hint]
  exact absurd hB (not_lt.2 this)

/-- **The local area tends to `0`**: `area f(Δ ∩ ball ξ s) → 0` as `s → 0⁺` (`‖ξ‖ = 1`).  The sets are open
(images of open subsets of `Δ` under the conformal `f`), increase with `s` and lie in the bounded `Ω`; their
intersection over `s > 0` is empty, since by injectivity a common point is `f z` with `z ∈ Δ` and `dist z ξ < s` for
every `s > 0`, so `z = ξ ∉ Δ` (continuity from above, `MeasureTheory.tendsto_measure_biInter_gt`). -/
theorem pe9_tendsto_volume_image_ball {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    Tendsto (fun s : ℝ => volume (f '' (unitDisc ∩ ball ξ s))) (𝓝[>] 0) (𝓝 0) := by
  have hopen : ∀ s : ℝ, IsOpen (f '' (unitDisc ∩ ball ξ s)) := fun s =>
    (show IsConformalOnto f (unitDisc ∩ ball ξ s) (f '' (unitDisc ∩ ball ξ s)) from
      ⟨hf.1.mono inter_subset_left, hf.2.1.mono inter_subset_left, rfl⟩).isOpen
        (isOpen_ball.inter isOpen_ball)
  have hsub : ∀ s : ℝ, f '' (unitDisc ∩ ball ξ s) ⊆ Ω := fun s => by
    rw [← hf.2.2]
    exact image_mono inter_subset_left
  have hfin : volume Ω ≠ ⊤ := by
    obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : ℂ)
    exact (lt_of_le_of_lt (measure_mono hR) measure_closedBall_lt_top).ne
  have h : Tendsto (fun s : ℝ => volume (f '' (unitDisc ∩ ball ξ s))) (𝓝[>] 0)
      (𝓝 (volume (⋂ r > (0 : ℝ), f '' (unitDisc ∩ ball ξ r)))) :=
    tendsto_measure_biInter_gt (μ := volume) (s := fun s : ℝ => f '' (unitDisc ∩ ball ξ s))
      (a := (0 : ℝ)) (fun r _ => (hopen r).nullMeasurableSet)
      (fun i j _ hij => image_mono (inter_subset_inter_right _ (ball_subset_ball hij)))
      ⟨1, one_pos, ne_top_of_le_ne_top hfin (measure_mono (hsub 1))⟩
  have hempty : (⋂ r > (0 : ℝ), f '' (unitDisc ∩ ball ξ r)) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro y hy
    simp only [mem_iInter] at hy
    obtain ⟨z, hz, rfl⟩ := hy 1 one_pos
    have hzξ : ∀ r : ℝ, 0 < r → dist z ξ < r := by
      intro r hr
      obtain ⟨u, hu, hfu⟩ := hy r hr
      rw [← hf.2.1 hu.1 hz.1 hfu]
      exact hu.2
    have hzeq : z = ξ := by
      by_contra hne
      exact lt_irrefl _ (hzξ (dist z ξ) (dist_pos.2 hne))
    have h1 := mem_ball_zero_iff.1 hz.1
    rw [hzeq, hξ] at h1
    exact lt_irrefl _ h1
  rw [hempty, measure_empty] at h
  exact h

/-- **Short arcs in every small window** `(s/2, s)` about a point of the circle, off any null set
(`pe9_tendsto_volume_image_ball` + `pe9_exists_radius_sq_arcLength_lt_window` with `log 2`). -/
theorem pe9_exists_window_radius {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s < s₀ → ∀ N : Set ℝ, volume N = 0 →
      ∃ ρ ∈ Ioo (s / 2) s, ρ ∉ N ∧ arcLength f ξ ρ < ENNReal.ofReal ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hT0 : 0 < ε ^ 2 * Real.log 2 / (4 * π) := by positivity
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      volume (f '' (unitDisc ∩ ball ξ s)) < ENNReal.ofReal (ε ^ 2 * Real.log 2 / (4 * π)) :=
    (pe9_tendsto_volume_image_ball hΩ hf hξ).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hT0))
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨s₀, hs₀, fun s hs0 hss₀ N hN => ?_⟩
  have hvol : volume (f '' (unitDisc ∩ ball ξ s)) < ENNReal.ofReal (ε ^ 2 * Real.log 2 / (4 * π)) :=
    hsub ⟨hs0, hss₀⟩
  have hfin : volume (f '' (unitDisc ∩ ball ξ s)) ≠ ⊤ := (hvol.trans ENNReal.ofReal_lt_top).ne
  have hA : (volume (f '' (unitDisc ∩ ball ξ s))).toReal < ε ^ 2 * Real.log 2 / (4 * π) := by
    have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hvol
    rwa [ENNReal.toReal_ofReal hT0.le] at h
  have hA0 : 0 ≤ (volume (f '' (unitDisc ∩ ball ξ s))).toReal := ENNReal.toReal_nonneg
  have hlog : Real.log (s / (s / 2)) = Real.log 2 := by
    have hs0' : s ≠ 0 := hs0.ne'
    congr 1
    field_simp
  have hB : (volume (f '' (unitDisc ∩ ball ξ s))).toReal * (2 * π) / Real.log (s / (s / 2)) < ε ^ 2 := by
    rw [hlog, div_lt_iff₀ hlog2]
    rw [lt_div_iff₀ (by positivity)] at hA
    nlinarith [mul_nonneg hA0 Real.pi_pos.le]
  obtain ⟨ρ, hρ, hρN, hρlt⟩ :=
    pe9_exists_radius_sq_arcLength_lt_window hf ξ (half_pos hs0) (half_lt_self hs0) hfin hB hN
  refine ⟨ρ, hρ, hρN, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  have h2 : ENNReal.ofReal ε ^ 2 ≤ arcLength f ξ ρ ^ 2 := pow_le_pow_left' hge 2
  rw [← ENNReal.ofReal_pow hε.le] at h2
  exact absurd hρlt (not_lt.2 h2)

/-- **Koebe along the radius.**  For `‖ξ‖ = 1`, `0 < s < 1`, `s/2 < ρ < s` and `a ∉ Ω`:
`‖f((1-ρ)ξ) - f((1-s)ξ)‖ ≤ 8 ‖a - f((1-s)ξ)‖`.

Proof: Pommerenke (2.5.8).  With `c = (1-s)ξ` the disc `ball c s` lies in `Δ` (`‖c‖ = 1 - s`);
`ψ u = f (c + s u) - f c` is holomorphic and injective on `ball 0 1` with `ψ 0 = 0`, and omits `a - f c`
(else `a = f (c + s u) ∈ f(Δ) = Ω`).  Koebe's quarter theorem gives `‖ψ'(0)‖ ≤ 4 ‖a - f c‖`; at
`u = ((s-ρ)/s) ξ` one has `‖u‖ = (s-ρ)/s < 1/2` and `c + s u = (1-ρ)ξ`, and the growth theorem gives
`‖ψ u‖ ≤ ‖ψ'(0)‖ ‖u‖/(1-‖u‖)² ≤ 2 ‖ψ'(0)‖`.  No derivative of the composition is computed: both Koebe
statements speak of `deriv ψ 0`.
Uses: `koebe_quarter_of_not_mem`, `koebe_growth_scaled` (`Lemmas/Koebe.lean`). -/
theorem pe9_koebe_radial {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) {s ρ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsρ : s / 2 < ρ) (hρs : ρ < s) {a : ℂ}
    (ha : a ∉ Ω) :
    ‖f (((1 - ρ : ℝ) : ℂ) * ξ) - f (((1 - s : ℝ) : ℂ) * ξ)‖ ≤ 8 * ‖a - f (((1 - s : ℝ) : ℂ) * ξ)‖ := by
  have hcn : ‖((1 - s : ℝ) : ℂ) * ξ‖ = 1 - s := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hξ, mul_one]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  -- the affine map `u ↦ c + s u` sends `ball 0 1` into `Δ`
  have hφD : MapsTo (fun u : ℂ => ((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) (ball (0 : ℂ) 1) unitDisc := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    show ((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    calc ‖((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u‖ ≤ ‖((1 - s : ℝ) : ℂ) * ξ‖ + ‖(s : ℂ) * u‖ := norm_add_le _ _
      _ = (1 - s) + s * ‖u‖ := by rw [hcn, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      _ < (1 - s) + s * 1 := by gcongr
      _ = 1 := by ring
  have hφd : DifferentiableOn ℂ (fun u : ℂ => ((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) (ball (0 : ℂ) 1) :=
    ((differentiable_const _).add ((differentiable_const _).mul differentiable_id)).differentiableOn
  have hψd : DifferentiableOn ℂ (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ))
      (ball (0 : ℂ) 1) :=
    (hf.1.comp hφd hφD).sub_const _
  have hψi : InjOn (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ))
      (ball (0 : ℂ) 1) := by
    intro u hu v hv huv
    have h1 : f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) = f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * v) :=
      sub_left_inj.1 huv
    have h2 := hf.2.1 (hφD hu) (hφD hv) h1
    exact mul_left_cancel₀ hs' (add_left_cancel h2)
  have hψ0 : (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ)) 0 = 0 := by
    simp
  have homit : a - f (((1 - s : ℝ) : ℂ) * ξ) ∉
      (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ)) '' ball (0 : ℂ) 1 := by
    rintro ⟨u, hu, hψu⟩
    apply ha
    have h1 : f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) = a := sub_left_inj.1 hψu
    rw [← h1, ← hf.2.2]
    exact mem_image_of_mem f (hφD hu)
  have hK := koebe_quarter_of_not_mem hψd hψi hψ0 homit
  have hun : ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖ = (s - ρ) / s := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) hs0.le), hξ, mul_one]
  have hu1 : ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [hun, div_lt_one hs0]
    linarith
  have hG := koebe_growth_scaled hψd hψi hψ0 hu1
  have hφu : ((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * ((((s - ρ) / s : ℝ) : ℂ) * ξ) = ((1 - ρ : ℝ) : ℂ) * ξ := by
    push_cast
    field_simp
    ring
  have hq : ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖ / (1 - ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖) ^ 2 ≤ 2 := by
    rw [hun]
    have h1 : (s - ρ) / s < 1 / 2 := by
      rw [div_lt_iff₀ hs0]
      linarith
    have h0 : 0 ≤ (s - ρ) / s := div_nonneg (by linarith) hs0.le
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * ((s - ρ) / s)) (by linarith : (0 : ℝ) ≤ 2 - (s - ρ) / s)]
  simp only [hφu] at hG
  calc ‖f (((1 - ρ : ℝ) : ℂ) * ξ) - f (((1 - s : ℝ) : ℂ) * ξ)‖
      ≤ ‖deriv (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ)) 0‖ *
          ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖ / (1 - ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖) ^ 2 := hG
    _ = ‖deriv (fun u : ℂ => f (((1 - s : ℝ) : ℂ) * ξ + (s : ℂ) * u) - f (((1 - s : ℝ) : ℂ) * ξ)) 0‖ *
          (‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖ / (1 - ‖(((s - ρ) / s : ℝ) : ℂ) * ξ‖) ^ 2) := by ring
    _ ≤ (4 * ‖a - f (((1 - s : ℝ) : ℂ) * ξ)‖) * 2 := mul_le_mul hK hq (by positivity) (by positivity)
    _ = 8 * ‖a - f (((1 - s : ℝ) : ℂ) * ξ)‖ := by ring

/-- **One window step** for the converging chain: given `ε, ρ > 0` and a null set `N`, a Wolff radius
`ρ' < min ρ (min ε 1)` off `N` with a short arc, lying in a window `(s/2, s)` whose radial point `f((1-s)ζ)` is
`ε`-close to the radial cluster point `w`. -/
theorem pe9_window_step {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : w ∈ radialClusterSet f ζ)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) {N : Set ℝ} (hN : volume N = 0) :
    ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧ ρ' < 1 ∧ ρ' < ε ∧ ρ' ∉ N ∧ arcLength f ζ ρ' < ENNReal.ofReal ε ∧
      ∃ s, 0 < s ∧ s < 1 ∧ s / 2 < ρ' ∧ ρ' < s ∧ ‖f (((1 - s : ℝ) : ℂ) * ζ) - w‖ < ε := by
  obtain ⟨s₀, hs₀, hwin⟩ := pe9_exists_window_radius hΩ hf hζ hε
  have hm : 0 < min (min ρ s₀) (min ε 1) := lt_min (lt_min hρ hs₀) (lt_min hε one_pos)
  have hm1 := min_le_left (min ρ s₀) (min ε 1)
  have hm2 := min_le_right (min ρ s₀) (min ε 1)
  have hρ1 := min_le_left ρ s₀
  have hρ2 := min_le_right ρ s₀
  have hε1 := min_le_left ε 1
  have hε2 := min_le_right ε 1
  obtain ⟨s, hs0, hss₁, hsw⟩ := pe9_exists_radial_point hw (half_pos hm) (by linarith) hε
  obtain ⟨ρ', hρ', hρ'N, hρ'len⟩ := hwin s hs0 (by linarith) N hN
  exact ⟨ρ', by linarith [hρ'.1], by linarith [hρ'.2], by linarith [hρ'.2], by linarith [hρ'.2], hρ'N, hρ'len,
    s, hs0, by linarith, hρ'.1, hρ'.2, hsw⟩

/-- **A circular chain converging to a radial cluster point** (the (⊇) half of Pommerenke Thm 2.16): the radii are
chosen by `pe9_window_step` (with `ε = 1/(n+1)`) in `pe5_exists_circChain_of_step`; for large `n`, a point `y` of
the `n`-th crosscut is within `diam Cₙ` of `f((1-rₙ)ζ)`, which is within `8/(n+1)` of the radial point `f((1-s)ζ)`
(`pe9_koebe_radial` with `a = w ∉ Ω`), which is within `1/(n+1)` of `w`. -/
theorem pe9_exists_circChain_tendsto {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : w ∈ radialClusterSet f ζ) :
    ∃ r, pe5_IsCircChain Ω f ζ r ∧ ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, pe5_circ f ζ r n ⊆ ball w ε := by
  obtain ⟨r, hr, hG⟩ := pe5_exists_circChain_of_step hΩ hf hζ
    (fun n ρ => ρ < 1 / ((n : ℝ) + 1) ∧ ∃ s, 0 < s ∧ s < 1 ∧ s / 2 < ρ ∧ ρ < s ∧
      ‖f (((1 - s : ℝ) : ℂ) * ζ) - w‖ < 1 / ((n : ℝ) + 1))
    (by
      obtain ⟨ρ, h1, -, h3, h4, -, h6, s, hs0, hs1, hs2, hs3, hs4⟩ :=
        pe9_window_step hΩ hf hζ hw one_pos one_pos (N := ∅) measure_empty
      refine ⟨ρ, h1, h3, h6, ?_, s, hs0, hs1, hs2, hs3, ?_⟩
      · simpa using h4
      · simpa using hs4)
    (fun n ρ N hρ hN => by
      obtain ⟨ρ', h1, h2, h3, h4, h5, h6, hs⟩ :=
        pe9_window_step hΩ hf hζ hw (by positivity : (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) + 1)) hρ hN
      exact ⟨ρ', h1, h2, h3, h5, h6, h4, hs⟩)
    (fun n ρ h => h.1)
  refine ⟨r, hr, fun ε hε => ?_⟩
  obtain ⟨hr01, -, -, hnull⟩ := hr
  have hwΩ : w ∉ Ω := pe9_radialClusterSet_notMem hf hζ hw
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 18 by positivity)
  filter_upwards [hnull.2.2.2.eventually_lt_const (half_pos hε), eventually_ge_atTop N] with n hn hnN
  intro y hy
  obtain ⟨-, s, hs0, hs1, hsρ, hρs, hsw⟩ := hG n
  have hx := pe6_mem_arc hζ (hr01 n).1 (hr01 n).2
  have hxC : f (((1 - r n : ℝ) : ℂ) * ζ) ∈ pe5_circ f ζ r n := ⟨_, hx, rfl⟩
  have hyx : dist y (f (((1 - r n : ℝ) : ℂ) * ζ)) ≤ Metric.diam (pe5_circ f ζ r n) :=
    Metric.dist_le_diam_of_mem (hΩ.subset (car3_crosscut_subset (hnull.1 n))) hy hxC
  have hK := pe9_koebe_radial hf hζ hs0 hs1 hsρ hρs hwΩ
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.2 hnN
  have hn1 : 1 / ((n : ℝ) + 1) < ε / 18 :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hN
  have t1 := norm_sub_le_norm_sub_add_norm_sub y (f (((1 - r n : ℝ) : ℂ) * ζ)) w
  have t2 := norm_sub_le_norm_sub_add_norm_sub (f (((1 - r n : ℝ) : ℂ) * ζ)) (f (((1 - s : ℝ) : ℂ) * ζ)) w
  have e1 : ‖w - f (((1 - s : ℝ) : ℂ) * ζ)‖ = ‖f (((1 - s : ℝ) : ℂ) * ζ) - w‖ := norm_sub_rev _ _
  rw [dist_eq_norm] at hyx
  rw [mem_ball, dist_eq_norm]
  linarith

/-- **Principal points are radial cluster points** (the (⊆) half of Pommerenke Thm 2.16): the radius crosses the late
crosscuts of any chain `C` equivalent to a circular chain at `ζ`.

Proof: given `r₀ ∈ (0, 1)` and `ε > 0`, let `C m ⊆ ball w ε` for `m ≥ M`.  Take `k₀` with `r_{k₀} < 1 - r₀`
and `n₀` with `V_{n₀} ⊆ chainEnd (circ) k₀ = f(Δ ∩ ball ζ r_{k₀})` (`hequiv.1`, `pe5_chainEnd_circ`), put
`m = max M n₀` (so `V_m ⊆ f(Δ ∩ ball ζ r_{k₀})` by `pe5_chainEnd_mono`), and take `k₁` with
`chainEnd (circ) k₁ ⊆ V_m` (`hequiv.2`) and `k₂ = max k₁ k₀` (so `f(Δ ∩ ball ζ r_{k₂}) ⊆ V_m`).  Then
`f(t₁ζ) ∈ V_m` for `t₁ = 1 - r_{k₂}/2`, while `f(t₀ζ) ∉ V_m` for `t₀ = 1 - r_{k₀}` (injectivity:
`|t₀ζ - ζ| = r_{k₀}`).  The preconnected `f([t₀, t₁] ζ) ⊆ Ω` therefore meets `C m` (`pe5_crosscut_meets`), at a point
`f(tζ)` with `r₀ < t₀ ≤ t ≤ t₁ < 1`, which is within `ε` of `w`.
Uses: `pe5_chainEnd_circ`, `pe5_chainEnd_mono`, `pe5_crosscut_meets`, `isPreconnected_Icc`. -/
theorem pe9_mem_radialClusterSet_of_tendsto {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℕ → ℝ} (hr : pe5_IsCircChain Ω f ζ r) {C : ℕ → Set ℂ}
    (hC : IsNullChain Ω C) (hequiv : NullChainEquiv Ω C (pe5_circ f ζ r)) {w : ℂ}
    (hw : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, C n ⊆ ball w ε) : w ∈ radialClusterSet f ζ := by
  simp only [radialClusterSet, mem_iInter]
  intro r₀ hr₀
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨hr01, hanti, hr0, hnull⟩ := id hr
  obtain ⟨M, hM⟩ := (hw ε hε).exists_forall_of_atTop
  obtain ⟨k₀, hk₀⟩ := (hr0.eventually_lt_const (sub_pos.2 hr₀.2)).exists
  obtain ⟨n₀, hn₀⟩ := hequiv.1 k₀
  -- the end `V_m`, `m = max M n₀`, lies in the half-disc of radius `r k₀` and contains the one of radius `r k₂`
  have hVm : chainEnd Ω C (max M n₀) ⊆ f '' (unitDisc ∩ ball ζ (r k₀)) := by
    rw [← pe5_chainEnd_circ hf hζ hr k₀]
    exact (pe5_chainEnd_mono hf hC (le_max_right M n₀)).trans hn₀
  obtain ⟨k₁, hk₁⟩ := hequiv.2 (max M n₀)
  have hk₂ : f '' (unitDisc ∩ ball ζ (r (max k₁ k₀))) ⊆ chainEnd Ω C (max M n₀) := by
    rw [← pe5_chainEnd_circ hf hζ hr (max k₁ k₀)]
    exact (pe5_chainEnd_mono hf hnull (le_max_left k₁ k₀)).trans hk₁
  have hrk₀ := hr01 k₀
  have hrk₂ := hr01 (max k₁ k₀)
  have hr20 : r (max k₁ k₀) ≤ r k₀ := hanti.antitone (le_max_right k₁ k₀)
  have ht01 : 1 - r k₀ ≤ 1 - r (max k₁ k₀) / 2 := by linarith
  have hr₀t₀ : r₀ < 1 - r k₀ := by linarith
  have ht₁1 : 1 - r (max k₁ k₀) / 2 < 1 := by linarith
  have hsegD : ∀ t ∈ Icc (1 - r k₀) (1 - r (max k₁ k₀) / 2), (t : ℂ) * ζ ∈ unitDisc := by
    intro t ht
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [ht.1, hr₀.1]), hζ, mul_one]
    linarith [ht.2]
  have hSp : IsPreconnected
      (f '' ((fun t : ℝ => (t : ℂ) * ζ) '' Icc (1 - r k₀) (1 - r (max k₁ k₀) / 2))) := by
    refine (isPreconnected_Icc.image _ (Complex.continuous_ofReal.mul continuous_const).continuousOn).image f
      (hf.1.continuousOn.mono ?_)
    rintro _ ⟨t, ht, rfl⟩
    exact hsegD t ht
  have hSΩ : f '' ((fun t : ℝ => (t : ℂ) * ζ) '' Icc (1 - r k₀) (1 - r (max k₁ k₀) / 2)) ⊆ Ω := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact hf.mapsTo (hsegD t ht)
  -- `f(t₁ ζ) ∈ V_m`, `t₁ = 1 - r k₂ / 2`
  have h1V : f (((1 - r (max k₁ k₀) / 2 : ℝ) : ℂ) * ζ) ∈ chainEnd Ω C (max M n₀) := by
    apply hk₂
    refine ⟨_, ⟨hsegD _ ⟨ht01, le_rfl⟩, ?_⟩, rfl⟩
    rw [mem_ball, dist_eq_norm]
    have e : (((1 - r (max k₁ k₀) / 2 : ℝ) : ℂ) * ζ) - ζ = ((-(r (max k₁ k₀) / 2) : ℝ) : ℂ) * ζ := by
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith), hζ, mul_one]
    linarith
  -- `f(t₀ ζ) ∉ V_m`, `t₀ = 1 - r k₀`
  have h0V : f (((1 - r k₀ : ℝ) : ℂ) * ζ) ∉ chainEnd Ω C (max M n₀) := by
    intro h
    obtain ⟨z, hz, hfz⟩ := hVm h
    have hzt : z = ((1 - r k₀ : ℝ) : ℂ) * ζ := hf.2.1 hz.1 (hsegD _ ⟨le_rfl, ht01⟩) hfz
    have h2 := mem_ball.1 hz.2
    rw [hzt, dist_eq_norm] at h2
    have e : (((1 - r k₀ : ℝ) : ℂ) * ζ) - ζ = ((-(r k₀)) : ℝ) * ζ := by
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hrk₀.1, hζ, mul_one] at h2
    exact lt_irrefl _ h2
  obtain ⟨p, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, hpC⟩ := pe5_crosscut_meets hC (max M n₀) hSp hSΩ
    ⟨_, ⟨_, ⟨1 - r (max k₁ k₀) / 2, ⟨ht01, le_rfl⟩, rfl⟩, rfl⟩, h1V⟩
    ⟨_, ⟨1 - r k₀, ⟨le_rfl, ht01⟩, rfl⟩, rfl⟩ h0V
  refine ⟨f ((t : ℂ) * ζ), ⟨(t : ℂ) * ζ, ⟨t, by linarith [ht.1], by linarith [ht.2], rfl⟩, rfl⟩, ?_⟩
  have h := hM (max M n₀) (le_max_left M n₀) hpC
  rw [mem_ball, dist_comm] at h
  exact h

/-- **Theorem 2.16 (core of `caratheodory_primeEnd_principal`).**  The statement of
`caratheodory_primeEnd_principal`, with the `P` of `pe5_exists_P`: (⊆) is
`pe9_mem_radialClusterSet_of_tendsto`, (⊇) is `pe9_exists_circChain_tendsto`. -/
theorem pe5_primeEnd_principal_core {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧ ∀ ζ : Circle,
      (∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = P ζ →
        chainImpression Ω c.1 = clusterSet f unitDisc ζ) ∧
      {w | IsPrincipalPoint Ω (P ζ) w} = radialClusterSet f ζ := by
  obtain ⟨P, hP, hchar⟩ := pe5_exists_P hΩ hf
  refine ⟨P, hP, fun ζ =>
    ⟨fun c hc => pe5_impression_eq_clusterSet hΩ hf (Circle.norm_coe ζ) ((hchar ζ c).1 hc), ?_⟩⟩
  ext w
  constructor
  · rintro ⟨c, hc, hconv⟩
    obtain ⟨r, hr⟩ := pe5_exists_circChain hΩ hf (Circle.norm_coe ζ)
    exact pe9_mem_radialClusterSet_of_tendsto hf (Circle.norm_coe ζ) hr c.2 ((hchar ζ c).1 hc r hr) hconv
  · intro hw
    obtain ⟨r, hr, hconv⟩ := pe9_exists_circChain_tendsto hΩ hf (Circle.norm_coe ζ) hw
    exact ⟨⟨pe5_circ f ζ r, hr.2.2.2⟩,
      (hchar ζ _).2 fun r' hr' => pe5_circ_equiv hf (Circle.norm_coe ζ) hr hr', hconv⟩

/-! ### Stage E (PE2): the radial cluster set is a continuum -/

/-- **The radial cluster set of a bounded continuous map is a nonempty compact connected set.**

Proof: `radialClusterSet f ζ = ⋂ₙ Kₙ` with `Kₙ = closure f(radialSegment ζ (1 - 1/(n+2)))`: the segments
decrease in `r`, and `1 - 1/(n+2) → 1` is cofinal in `(0, 1)`.  Each `Kₙ` is nonempty, bounded by `M` (the segment lies
in `Δ` since `‖ζ‖ = 1`), hence compact, and preconnected (`radialSegment ζ r` is the image of `Ioo r 1` under
`t ↦ t ζ`, and `f` is continuous on `Δ`); the `Kₙ` decrease.
Uses: the proof of `clusterSet_isCompact_isConnected` (`ClusterSets.lean`, copied) with these `Kₙ`, and
`isPreconnected_iInter_of_antitone_isCompact`. -/
theorem pe4_radialClusterSet_isCompact_isConnected {f : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hf : ContinuousOn f unitDisc) (hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M) :
    IsCompact (radialClusterSet f ζ) ∧ IsConnected (radialClusterSet f ζ) := by
  obtain ⟨M, hM⟩ := hbdd
  have hseg : ∀ r : ℝ, 0 ≤ r → radialSegment ζ r ⊆ unitDisc := by
    rintro r hr _ ⟨t, hrt, ht1, rfl⟩
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hζ,
      mul_one]
    exact ht1
  have hmono : ∀ r r' : ℝ, r ≤ r' → radialSegment ζ r' ⊆ radialSegment ζ r := by
    rintro r r' hrr' _ ⟨t, hrt, ht1, rfl⟩
    exact ⟨t, lt_of_le_of_lt hrr' hrt, ht1, rfl⟩
  have hr : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) ∧ 1 - 1 / ((n : ℝ) + 2) < 1 := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have h2 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    exact ⟨by linarith, by linarith⟩
  set K : ℕ → Set ℂ := fun n => closure (f '' radialSegment ζ (1 - 1 / ((n : ℝ) + 2)))
  have hKdef : ∀ n, K n = closure (f '' radialSegment ζ (1 - 1 / ((n : ℝ) + 2))) := fun n => rfl
  have hKeq : radialClusterSet f ζ = ⋂ n, K n := by
    unfold radialClusterSet
    apply Subset.antisymm
    · exact subset_iInter fun n => iInter₂_subset (1 - 1 / ((n : ℝ) + 2)) (hr n)
    · refine subset_iInter₂ fun r hr' => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr'.2)
      refine (iInter_subset _ n).trans (closure_mono (image_mono (hmono _ _ ?_)))
      have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h3 : 1 / ((n : ℝ) + 3) < 1 / ((n : ℝ) + 2) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have h4 : 0 < 1 / ((n : ℝ) + 3) := by positivity
    rw [hKdef]
    exact ⟨_, subset_closure ⟨_, ⟨1 - 1 / ((n : ℝ) + 3), by linarith, by linarith, rfl⟩, rfl⟩⟩
  have hKbdd : ∀ n, K n ⊆ closedBall 0 M := by
    intro n
    rw [hKdef]
    refine closure_minimal ?_ isClosed_closedBall
    rintro _ ⟨z, hz, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hM z (hseg _ (hr n).1.le hz))
  have hKcl : ∀ n, IsClosed (K n) := fun n => by
    rw [hKdef]
    exact isClosed_closure
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    isCompact_of_isClosed_isBounded (hKcl n) (isBounded_closedBall.subset (hKbdd n))
  have hKp : ∀ n, IsPreconnected (K n) := by
    intro n
    have hS : radialSegment ζ (1 - 1 / ((n : ℝ) + 2)) =
        (fun t : ℝ => (t : ℂ) * ζ) '' Ioo (1 - 1 / ((n : ℝ) + 2)) 1 := by
      ext z
      constructor
      · rintro ⟨t, h1, h2, rfl⟩
        exact ⟨t, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨t, h1, h2, rfl⟩
    have hsp : IsPreconnected (radialSegment ζ (1 - 1 / ((n : ℝ) + 2))) := by
      rw [hS]
      exact isPreconnected_Ioo.image _ (Complex.continuous_ofReal.mul continuous_const).continuousOn
    rw [hKdef]
    exact (hsp.image f (hf.mono (hseg _ (hr n).1.le))).closure
  have hKd : ∀ n, K (n + 1) ⊆ K n := by
    intro n
    rw [hKdef, hKdef]
    refine closure_mono (image_mono (hmono _ _ ?_))
    push_cast
    have : 1 / ((n : ℝ) + 1 + 2) ≤ 1 / ((n : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hint : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKd hKne (hKc 0) hKcl
  rw [hKeq]
  exact ⟨(hKc 0).of_isClosed_subset (isClosed_iInter hKcl) (iInter_subset _ 0),
    hint, isPreconnected_iInter_of_antitone_isCompact hKd hKc hKp⟩

/-- The principal points of a prime end form a nonempty compact connected set.

Proof (s21r PE2): every prime end is some `P ζ` (Theorem 2.15), whose principal points are the radial cluster set of
`f` at `ζ` (`pe5_primeEnd_principal_core`, Pommerenke Thm 2.16). The radial cluster set is a decreasing intersection
of continua (`pe4_radialClusterSet_isCompact_isConnected`). -/
theorem principalPoints_isCompact_isConnected {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) (p : PrimeEnd Ω) :
    IsCompact {w | IsPrincipalPoint Ω p w} ∧ IsConnected {w | IsPrincipalPoint Ω p w} := by
  obtain ⟨P, hP, hPζ⟩ := pe5_primeEnd_principal_core hΩ hf
  obtain ⟨ζ, rfl⟩ := hP.2 p
  rw [(hPζ ζ).2]
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hΩ
  exact pe4_radialClusterSet_isCompact_isConnected (Circle.norm_coe ζ) hf.1.continuousOn
    ⟨R, fun z hz => by simpa using hR (hf.mapsTo hz)⟩

/-- **Theorem (Carathéodory, prime-end form).**  For a conformal map `f` of the disc onto a bounded
domain `Ω`, the prime ends of `Ω` correspond bijectively to the points of the unit circle, the
prime end at `ζ` having impression equal to the cluster set of `f` at `ζ`.

Proof (s21r PE2): `P ζ` is the class of a circular chain `f(Δ ∩ sphere ζ rₙ)` along Wolff radii `rₙ → 0` chosen off
PE1's Jensen–Fatou null sets. Its ends are `f(Δ ∩ ball ζ rₙ)`, so its impression is the cluster set, and chains at
distinct points are inequivalent. Surjectivity (Pommerenke Thm 2.15 (c), run on the ends, without Prop 2.14): for a
null-chain with ends `Vₙ`, `⋂ closure f⁻¹(Vₙ)` is one point `ζ ∈ 𝕋`, because two points would force the late
crosscuts to meet two consecutive circular crosscuts at `ζ`, whose closures are disjoint. By a two-curves step with
the same arcs, `ζ` lies in the closure of at most one of `f⁻¹(C_m)`, `f⁻¹(C_{m+1})`, which gives the equivalence. -/
theorem caratheodory_primeEnd {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧
      ∀ ζ : Circle, ∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = P ζ →
        chainImpression Ω c.1 = clusterSet f unitDisc ζ := by
  exact pe5_caratheodory_primeEnd_core hΩ hf

/-- **Local connectivity and impressions.**  The boundary of a bounded simply connected domain is
locally connected iff every null-chain has a one-point impression.

Proof (s21r, 2026-09-27).  (⇒): clause (ii′) of local connectivity (`pe1_ii_of_lc`) at a limit point of the
crosscut ends puts the late ends `chainEnd n` into small discs (`pe6_impression_subsingleton_of_lc`).  (⇐): if
`∂Ω` is not locally connected, the easy half of Theorem C1 (`locallyConnected_iff_clusterSet_subsingleton`)
gives a point `ξ` of the circle whose cluster set has two points; the σ-chain of circle arcs
`f(Δ ∩ sphere ξ rₙ)` along Wolff radii chosen off a Jensen–Fatou null set, so that consecutive closures are
disjoint (the construction in the proof of Pommerenke Thm 2.15), is a null-chain whose impression contains that
cluster set (Pommerenke §2.5, Thm 2.16), a contradiction (`pe6_lc_of_forall_subsingleton`). -/
theorem locallyConnectedSpace_frontier_iff {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LocallyConnectedSpace (frontier Ω) ↔
      ∀ C : ℕ → Set ℂ, IsNullChain Ω C → (chainImpression Ω C).Subsingleton := by
  exact ⟨fun hlc C hC => pe6_impression_subsingleton_of_lc hΩ hf hlc hC, pe6_lc_of_forall_subsingleton hΩ hf⟩

/-! ### Lindelöf's theorem: the proof (`ld8_`)

Lindelöf's reflection argument (Lindelöf 1915; Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.5, Theorem 2.16
and Corollary 2.17 for conformal maps, and the Lehto–Virtanen theorem of §4.1 for normal functions).  The Cayley
transfer `z ↦ cayleyInv (-(conj ζ) * z)` sends `ζ` to `0`, and `F = (f ∘ κ - a) / C` is holomorphic on `upperHalf`
with `‖F‖ ≤ 1` and `F → 0` along a curve `Γ → 0`.
* **Radial limit** (`ld8_radial`): the tail `S` of `Γ` and its mirror image under `σ z = -conj z` cut the half disc
  (`ld8_sep`, by a parity argument for a reflected polygon), and `F z · conj (F (σ z))` is bounded by the harmonic
  majorant `ld8_u` (`ld8_halfDisc`).
* **Angular limit** (`ld8_cone`): the quarter-disc majorant `2/π · arg z - Im z / r` (`ld8_quarter`, Jordan's
  inequality) and the reflection `conj ∘ F ∘ σ`.

Both maximum principles are the installed `norm_le_of_frontier_limsup_le_of_bounded` (one exceptional boundary
point), through `ld8_maxmod_upper`. -/

/-! ### Stage 1a: the reflected polygon (parity, exp form) -/

/-- **R1.**  `lastOf` commutes with a map applied to every vertex. -/
theorem ld8_lastOf_map (φ : ℂ → ℂ) (a : ℂ) (l : List ℂ) :
    lastOf (φ a) (l.map φ) = φ (lastOf a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, lastOf]
    exact ih b

/-- **R2.**  The reflection `z ↦ -conj z` maps a polygonal path in a reflection-invariant set `W` to a polygonal path
in `W`. -/
theorem ld8_segsIn_reflect {W : Set ℂ} (hW : ∀ z ∈ W, -conj z ∈ W) {a : ℂ} {l : List ℂ}
    (hl : SegsIn W a l) : SegsIn W (-conj a) (l.map (fun z => -conj z)) := by
  induction l generalizing a with
  | nil => trivial
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := hl
    refine ⟨fun z hz => ?_, ih hbl⟩
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    have h := hW _ (hab ⟨s, t, hs, ht, hst, rfl⟩)
    convert h using 1
    simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
    ring

/-- **R3.**  The reflection `z ↦ -conj z` conjugates the segment integral of `1/z` (unconditionally: at `0` both sides
use the junk value `0⁻¹ = 0`). -/
theorem ld8_segIntegral_inv_reflect (p q : ℂ) :
    segIntegral (fun z => (z - 0)⁻¹) (-conj p) (-conj q) =
      conj (segIntegral (fun z => (z - 0)⁻¹) p q) := by
  unfold segIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  congr 1
  funext t
  simp only [sub_zero]
  have e1 : -conj p + (t : ℂ) * (-conj q - -conj p) = -conj (p + (t : ℂ) * (q - p)) := by
    simp only [map_add, map_mul, map_sub, Complex.conj_ofReal]
    ring
  have e2 : -conj q - -conj p = -conj (q - p) := by
    simp only [map_sub]
    ring
  rw [e1, e2, map_mul, map_inv₀, inv_neg, neg_mul_neg]

/-- **R3′.**  The reflection `z ↦ -conj z` conjugates the path integral of `1/z`. -/
theorem ld8_pathIntFrom_inv_reflect (a : ℂ) (l : List ℂ) :
    pathIntFrom (fun z => (z - 0)⁻¹) (-conj a) (l.map (fun z => -conj z)) =
      conj (pathIntFrom (fun z => (z - 0)⁻¹) a l) := by
  induction l generalizing a with
  | nil => simp [pathIntFrom]
  | cons b l ih => simp only [List.map_cons, pathIntFrom, map_add, ld8_segIntegral_inv_reflect, ih]

/-- **R4.**  Along a polygonal path avoiding `0`, `exp ∫ dz/z` is the ratio of the end points. -/
theorem ld8_exp_pathIntFrom_inv {a : ℂ} (ha : a ≠ 0) {l : List ℂ}
    (hl : SegsIn {z : ℂ | z ≠ 0} a l) :
    Complex.exp (pathIntFrom (fun z => (z - 0)⁻¹) a l) = lastOf a l / a := by
  induction l generalizing a with
  | nil => simp [pathIntFrom, lastOf, ha]
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := hl
    have h0 : (0 : ℂ) ∉ segment ℝ a b := fun h => hab h rfl
    have hb : b ≠ 0 := hab (right_mem_segment ℝ a b)
    simp only [pathIntFrom, lastOf]
    rw [segIntegral_inv_sub_eq_log h0, Complex.exp_add, ih hb hbl, sub_zero, sub_zero,
      Complex.exp_log (div_ne_zero hb ha)]
    field_simp

/-- A point of the imaginary axis is fixed by the reflection `z ↦ -conj z`. -/
theorem ld8_reflect_fix {z : ℂ} (hz : z.re = 0) : -conj z = z := by
  apply Complex.ext <;> simp [hz]

/-- The reflected path ends where the path ends when both end points lie on the imaginary axis. -/
theorem ld8_lastOf_reflect {a : ℂ} (hare : a.re = 0) {l : List ℂ} (hre : (lastOf a l).re = 0) :
    lastOf a (l.map (fun z => -conj z)) = lastOf a l := by
  have h : lastOf (-conj a) (l.map (fun z => -conj z)) = -conj (lastOf a l) :=
    ld8_lastOf_map (fun z => -conj z) a l
  rwa [ld8_reflect_fix hare, ld8_reflect_fix hre] at h

/-- **R5 (parity, exp form).**  Let `a ≠ 0` and the end `e` of a polygonal path `a, l` avoiding `0` lie on the
imaginary axis with `Re (e / a) < 0`.  Then the closed polygon made of the path and its mirror image under
`z ↦ -conj z`, run backwards, winds a non-zero number of times around `0`: its integral of `dz/z` is `I - conj I`,
and `exp I = e / a` has negative real part, so `I` is not real. -/
theorem ld8_polyWinding_reflect_ne_zero {a : ℂ} (ha : a ≠ 0) (hare : a.re = 0) {l : List ℂ}
    (hl : SegsIn {z : ℂ | z ≠ 0} a l) (hre : (lastOf a l).re = 0)
    (hneg : (lastOf a l / a).re < 0) :
    polyWinding (a :: (l ++ (a :: l.map (fun z => -conj z)).reverse.tail)) 0 ≠ 0 := by
  have hrefl : pathIntFrom (fun z => (z - 0)⁻¹) a (l.map (fun z => -conj z)) =
      conj (pathIntFrom (fun z => (z - 0)⁻¹) a l) := by
    have h := ld8_pathIntFrom_inv_reflect a l
    rwa [ld8_reflect_fix hare] at h
  have hint : polyIntegral (fun z => (z - 0)⁻¹)
      (a :: (l ++ (a :: l.map (fun z => -conj z)).reverse.tail)) =
      pathIntFrom (fun z => (z - 0)⁻¹) a l - conj (pathIntFrom (fun z => (z - 0)⁻¹) a l) := by
    rw [polyIntegral_cons, pathIntFrom_append, lastOf_append, ← ld8_lastOf_reflect hare hre,
      pathIntFrom_reverse, lastOf_reverse, segIntegral_self, hrefl]
    ring
  have hexp := ld8_exp_pathIntFrom_inv ha hl
  generalize pathIntFrom (fun z => (z - 0)⁻¹) a l = P at hint hexp
  intro h0
  have hden : 2 * (π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [polyWinding, hint, div_eq_zero_iff, or_iff_left hden, Complex.sub_conj] at h0
  have him : P.im = 0 := by simpa using congrArg Complex.im h0
  have hreal : P = (P.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hre' := Complex.exp_ofReal_re P.re
  rw [← hreal, hexp] at hre'
  linarith [Real.exp_pos P.re]

/-- The closed reflected polygon of `ld8_polyWinding_reflect_ne_zero` lies in `W` when the path does, `W` is invariant
under `z ↦ -conj z`, and both ends of the path lie on the imaginary axis. -/
theorem ld8_polyTrace_reflect_subset {W : Set ℂ} (hW : ∀ z ∈ W, -conj z ∈ W) {a : ℂ} (haW : a ∈ W)
    (hare : a.re = 0) {l : List ℂ} (hl : SegsIn W a l) (hre : (lastOf a l).re = 0) :
    polyTrace (a :: (l ++ (a :: l.map (fun z => -conj z)).reverse.tail)) ⊆ W := by
  have hl' : SegsIn W a (l.map (fun z => -conj z)) := by
    have h := ld8_segsIn_reflect hW hl
    rwa [ld8_reflect_fix hare] at h
  have hrev := segsIn_reverse hl'
  rw [ld8_lastOf_reflect hare hre] at hrev
  refine polyTrace_cons_subset (segsIn_append.2 ⟨hl, hrev⟩) ?_
  rw [lastOf_append, ← ld8_lastOf_reflect hare hre, lastOf_reverse, segment_same]
  exact singleton_subset_iff.2 haW

/-- **Zero winding.**  A closed polygon inside `ball 0 r` that misses a preconnected set `S ∋ 0` reaching the circle
`‖z‖ = r` winds `0` times around `0`: join `S` to `∞` by the ray through a point `s₀ ∈ S` with `r ≤ ‖s₀‖`. -/
theorem ld8_polyWinding_eq_zero {v : List ℂ} {r : ℝ} (hr : 0 < r) (htr : polyTrace v ⊆ ball 0 r)
    {S : Set ℂ} (hSp : IsPreconnected S) (hS0 : (0 : ℂ) ∈ S) {s₀ : ℂ} (hs₀ : s₀ ∈ S)
    (hs₀r : r ≤ ‖s₀‖) (hST : ∀ x ∈ S, x ∉ polyTrace v) : polyWinding v 0 = 0 := by
  have hs₀pos : 0 < ‖s₀‖ := hr.trans_le hs₀r
  have hray : IsPreconnected ((fun t : ℝ => (t : ℂ) * s₀) '' Ici 1) :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * s₀).continuousOn
  have hTp : IsPreconnected (S ∪ (fun t : ℝ => (t : ℂ) * s₀) '' Ici 1) :=
    IsPreconnected.union s₀ hs₀ ⟨1, self_mem_Ici, by simp⟩ hSp hray
  have hTtr : ∀ x ∈ S ∪ (fun t : ℝ => (t : ℂ) * s₀) '' Ici 1, x ∉ polyTrace v := by
    rintro x (hx | ⟨t, ht, rfl⟩)
    · exact hST x hx
    · intro hx
      have ht1 : (1 : ℝ) ≤ t := ht
      have h1 : ‖(t : ℂ) * s₀‖ < r := mem_ball_zero_iff.1 (htr hx)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)] at h1
      nlinarith [mul_le_mul_of_nonneg_right ht1 (norm_nonneg s₀)]
  obtain ⟨R, hR⟩ := exists_polyWinding_eq_zero_of_norm_gt v
  have ht1 : (1 : ℝ) ≤ max 1 ((|R| + 1) / ‖s₀‖) := le_max_left _ _
  have hnorm : R < ‖((max 1 ((|R| + 1) / ‖s₀‖) : ℝ) : ℂ) * s₀‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h2 : (|R| + 1) / ‖s₀‖ ≤ max 1 ((|R| + 1) / ‖s₀‖) := le_max_right _ _
    rw [div_le_iff₀ hs₀pos] at h2
    linarith [le_abs_self R]
  rw [s20v_b_polyWinding_const hTp hTtr (mem_union_right _ ⟨_, ht1, rfl⟩) (mem_union_left _ hS0)]
  exact hR _ hnorm

/-- `S ∪ σ(S)` is closed for closed `S`, where `σ z = -conj z` is a homeomorphic involution. -/
theorem ld8_isClosed_reflect_union {S : Set ℂ} (hS : IsClosed S) :
    IsClosed (S ∪ (fun z => -conj z) '' S) := by
  have hinv : Function.LeftInverse (fun z : ℂ => -conj z) (fun z : ℂ => -conj z) := fun z => by simp
  rw [image_eq_preimage_of_inverse hinv hinv]
  exact hS.union (hS.preimage Complex.continuous_conj.neg)

/-! ### Stage 1b: support (maximum principle on `upperHalf`, tail of the curve, majorants) -/

/-- Continuity at a frontier point turns a pointwise bound into the `limsup` form of the maximum principle. -/
theorem ld8_eventually_norm_le {G : ℂ → ℂ} {q : ℂ} (hG : ContinuousAt G q) {M : ℝ} (hq : ‖G q‖ ≤ M)
    (U : Set ℂ) : ∀ ε > 0, ∀ᶠ z in 𝓝[U] q, ‖G z‖ ≤ M + ε := by
  intro ε hε
  have h : ∀ᶠ z in 𝓝 q, ‖G z‖ < M + ε := hG.norm.eventually (eventually_lt_nhds (by linarith))
  exact (h.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.le

/-- A majorant continuous at a frontier point gives the `limsup` form: if `‖G‖ ≤ B` on `U` and `B` is continuous at
`q` with `B q ≤ M`, then eventually `‖G z‖ ≤ M + ε` in `𝓝[U] q` (`G` itself is never evaluated at `q`). -/
theorem ld8_eventually_norm_le_of_majorant {G : ℂ → ℂ} {B : ℂ → ℝ} {U : Set ℂ} (hGB : ∀ z ∈ U, ‖G z‖ ≤ B z)
    {q : ℂ} (hB : ContinuousAt B q) {M : ℝ} (hq : B q ≤ M) : ∀ ε > 0, ∀ᶠ z in 𝓝[U] q, ‖G z‖ ≤ M + ε := by
  intro ε hε
  have h : ∀ᶠ z in 𝓝 q, B z < M + ε := hB.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzU
  exact (hGB z hzU).trans hz.le

/-- **Maximum principle on a bounded open subset of `upperHalf` with `0` as the exceptional point.**  If `0 ∈ ∂U` this
is `norm_le_of_frontier_limsup_le_of_bounded` with `p = 0`, `c = -i`.  Otherwise (also for a pocket, `0 ∉ closure U`)
it is the same theorem at the point `p` of `closure U` of maximal imaginary part, with `c = i`: `p ∈ ∂U` because `U`
is open, and no frontier point is `0`. -/
theorem ld8_maxmod_upper {U : Set ℂ} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : IsPreconnected U) (hUH : U ⊆ upperHalf) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U)
    {K : ℝ} (hK : ∀ z ∈ U, ‖h z‖ ≤ K) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ q ∈ frontier U, q ≠ 0 → ∀ ε > 0, ∀ᶠ z in 𝓝[U] q, ‖h z‖ ≤ M + ε) :
    ∀ z ∈ U, ‖h z‖ ≤ M := by
  by_cases h0 : (0 : ℂ) ∈ frontier U
  · refine norm_le_of_frontier_limsup_le_of_bounded (c := -I) hUo hUb hUc h0 (fun z hz => ?_) hh hK hM hbd
    have hz' : 0 < z.im := hUH hz
    rw [mem_slitPlane_iff]
    left
    simpa using hz'
  rcases U.eq_empty_or_nonempty with hU | hU
  · intro z hz
    simp [hU] at hz
  obtain ⟨p, hpcl, hpmax⟩ :=
    hUb.isCompact_closure.exists_isMaxOn hU.closure Complex.continuous_im.continuousOn
  have hlt : ∀ z ∈ U, z.im < p.im := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo z hz
    have hz' : z + ((ε / 2 : ℝ) : ℂ) * I ∈ U := by
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have h1 := isMaxOn_iff.1 hpmax _ (subset_closure hz')
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at h1
    linarith
  have hpf : p ∈ frontier U := by
    rw [hUo.frontier_eq]
    exact ⟨hpcl, fun hp => lt_irrefl _ (hlt p hp)⟩
  refine norm_le_of_frontier_limsup_le_of_bounded (c := I) hUo hUb hUc hpf (fun z hz => ?_) hh hK hM
    (fun q hq _ => hbd q hq fun hq0 => h0 (by rw [← hq0]; exact hq))
  rw [mem_slitPlane_iff]
  left
  have := hlt z hz
  simp only [Complex.I_mul_re, Complex.sub_im]
  linarith

/-- **Maximum principle on a component of the cut half disc.**  Let `K` be closed, `z₀ ∈ (upperHalf ∩ ball 0 r) \ K`,
and suppose `0` is the only real point in the closure of the component of `z₀` (the conclusion of `ld8_sep`).  If
`G` is holomorphic and bounded on `upperHalf` with `‖G‖ ≤ 1` on `K ∩ upperHalf` and on the upper semicircle, then
`‖G z₀‖ ≤ 1`.  (Frontier points `≠ 0` of the component lie in `upperHalf` by the separation hypothesis and in
`K ∪ sphere 0 r` by `iod_frontier_connectedComponentIn_subset`.) -/
theorem ld8_component_maxmod {r : ℝ} {K : Set ℂ} (hK : IsClosed K) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (upperHalf ∩ ball 0 r) \ K)
    (hsep : ∀ x ∈ closure (connectedComponentIn ((upperHalf ∩ ball 0 r) \ K) z₀), x.im = 0 → x = 0)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G upperHalf) {C : ℝ} (hGC : ∀ z ∈ upperHalf, ‖G z‖ ≤ C)
    (hGb : ∀ q ∈ upperHalf, q ∈ K ∨ ‖q‖ = r → ‖G q‖ ≤ 1) : ‖G z₀‖ ≤ 1 := by
  have hVo : IsOpen ((upperHalf ∩ ball 0 r) \ K) := (isOpen_upperHalf.inter isOpen_ball).sdiff hK
  have hUV := connectedComponentIn_subset ((upperHalf ∩ ball 0 r) \ K) z₀
  have hUH : connectedComponentIn ((upperHalf ∩ ball 0 r) \ K) z₀ ⊆ upperHalf :=
    fun z hz => (hUV hz).1.1
  have hfr : frontier (connectedComponentIn ((upperHalf ∩ ball 0 r) \ K) z₀) ⊆
      ((upperHalf ∩ ball 0 r) \ K)ᶜ := by
    have h := iod_frontier_connectedComponentIn_subset hVo.isClosed_compl z₀
    rwa [compl_compl] at h
  have hclo : closure (connectedComponentIn ((upperHalf ∩ ball 0 r) \ K) z₀) ⊆
      {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ r} := by
    refine closure_minimal (fun z hz => ⟨(hUH hz).le, (mem_ball_zero_iff.1 (hUV hz).1.2).le⟩) ?_
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_norm continuous_const)
  refine ld8_maxmod_upper hVo.connectedComponentIn (isBounded_ball.subset fun z hz => (hUV hz).1.2)
    isPreconnected_connectedComponentIn hUH (hG.mono hUH) (fun z hz => hGC z (hUH hz)) zero_le_one
    (fun q hq hq0 => ?_) z₀ (mem_connectedComponentIn hz₀)
  have hqcl := frontier_subset_closure hq
  obtain ⟨hqim, hqr⟩ := hclo hqcl
  have hqH : q ∈ upperHalf := show 0 < q.im from
    lt_of_le_of_ne hqim fun h => hq0 (hsep q hqcl h.symm)
  refine ld8_eventually_norm_le ((hG.differentiableAt (isOpen_upperHalf.mem_nhds hqH)).continuousAt)
    (hGb q hqH ?_) _
  by_cases hqK : q ∈ K
  · exact Or.inl hqK
  · exact Or.inr (le_antisymm hqr (not_lt.1 fun hlt => hfr hq ⟨⟨hqH, mem_ball_zero_iff.2 hlt⟩, hqK⟩))

/-- **Tail of the curve.**  For `0 ≤ t₀ < 1`, `Γ([t₀, 1)) ∪ {0}` is compact and preconnected when `Γ` is continuous on
`[0, 1)` and tends to `0` at `1`: it is the image of `[t₀, 1]` under the extension of `Γ` by `Γ 1 = 0`. -/
theorem ld8_tail {Γ : ℝ → ℂ} (hΓc : ContinuousOn Γ (Ico 0 1)) (hΓ0 : Tendsto Γ (𝓝[<] 1) (𝓝 0))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht₀1 : t₀ < 1) :
    IsCompact (Γ '' Ico t₀ 1 ∪ {0}) ∧ IsPreconnected (Γ '' Ico t₀ 1 ∪ {0}) := by
  have himg : (fun t => if t < 1 then Γ t else 0) '' Icc t₀ 1 = Γ '' Ico t₀ 1 ∪ {0} := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h1 : t < 1
      · exact mem_union_left _ ⟨t, ⟨ht.1, h1⟩, by simp [h1]⟩
      · exact mem_union_right _ (by simp [h1])
    · rintro (⟨t, ht, rfl⟩ | hw)
      · exact ⟨t, ⟨ht.1, ht.2.le⟩, by simp [ht.2]⟩
      · exact ⟨1, ⟨ht₀1.le, le_rfl⟩, by simpa using (mem_singleton_iff.1 hw).symm⟩
  have hcont : ContinuousOn (fun t => if t < 1 then Γ t else 0) (Icc t₀ 1) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h1 | h1
    · have h2 : ContinuousWithinAt Γ (Icc t₀ 1 ∩ Iio 1) t :=
        (hΓc t ⟨ht₀.trans ht.1, h1⟩).mono fun s hs => ⟨ht₀.trans hs.1.1, hs.2⟩
      rw [continuousWithinAt_inter (Iio_mem_nhds h1)] at h2
      refine h2.congr_of_eventuallyEq ?_ (by simp [h1])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1)] with s hs
      simp [show s < 1 from hs]
    · subst h1
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 hΓ0 ε hε
      refine ⟨δ, hδ, fun {s} hs hsd => ?_⟩
      by_cases hs1 : s < 1
      · simpa [hs1] using hδε hs1 hsd
      · have hs' : s = 1 := le_antisymm hs.2 (not_lt.1 hs1)
        subst hs'
        simpa using hε
  rw [← himg]
  exact ⟨isCompact_Icc.image_of_continuousOn hcont, isPreconnected_Icc.image _ hcont⟩

/-- The reflection `conj ∘ F ∘ σ`, `σ z = -conj z`, of a function holomorphic on `upperHalf` is holomorphic on
`upperHalf`. -/
theorem ld8_reflect_differentiableOn {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf) :
    DifferentiableOn ℂ (fun z => conj (F (-conj z))) upperHalf := by
  intro z hz
  have hz0 : 0 < z.im := hz
  have hz' : -conj z ∈ upperHalf := by
    show 0 < (-conj z).im
    simpa using hz0
  have h1 : DifferentiableAt ℂ (fun u => F (-u)) (conj z) :=
    (hF.differentiableAt (isOpen_upperHalf.mem_nhds hz')).comp (conj z)
      (differentiable_neg (𝕜 := ℂ)).differentiableAt
  exact (differentiableAt_conj_conj_iff.2 h1).differentiableWithinAt

/-- The norm of `exp (w · L)` for real `L`. -/
theorem ld8_norm_exp_mul_ofReal (w : ℂ) (L : ℝ) : ‖Complex.exp (w * (L : ℂ))‖ = Real.exp (w.re * L) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The half-disc harmonic majorant `u = (2/π) · arg ((r + z)/(r - z))`: the harmonic measure of the upper semicircle
in the upper half disc (`0` on the diameter, `1` on the arc). -/
def ld8_u (r : ℝ) (z : ℂ) : ℝ := 2 / π * Complex.arg (((r : ℂ) + z) / ((r : ℂ) - z))

/-- **U1.**  Real and imaginary parts of `(r + z)/(r - z)` (unconditional: at `z = r` both sides are `0`). -/
theorem ld8_ratio_re_im (r : ℝ) (z : ℂ) :
    (((r : ℂ) + z) / ((r : ℂ) - z)).re = (r ^ 2 - ‖z‖ ^ 2) / ‖(r : ℂ) - z‖ ^ 2 ∧
      (((r : ℂ) + z) / ((r : ℂ) - z)).im = 2 * r * z.im / ‖(r : ℂ) - z‖ ^ 2 := by
  constructor
  · rw [Complex.div_re, ← add_div, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    congr 1
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
      Complex.ofReal_im, Complex.normSq_apply]
    ring
  · rw [Complex.div_im, div_sub_div_same, ← Complex.normSq_eq_norm_sq]
    congr 1
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
      Complex.ofReal_im]
    ring

/-- `r - z ≠ 0` for `z` in `upperHalf`. -/
theorem ld8_ofReal_sub_ne_zero (r : ℝ) {z : ℂ} (hz : 0 < z.im) : (r : ℂ) - z ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at h'
  linarith

/-- **U2.**  `ld8_u r ≥ 0` on `upperHalf`. -/
theorem ld8_u_nonneg {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) : 0 ≤ ld8_u r z := by
  have him : 0 < (((r : ℂ) + z) / ((r : ℂ) - z)).im := by
    rw [(ld8_ratio_re_im r z).2]
    exact div_pos (mul_pos (mul_pos two_pos hr) hz) (pow_pos (norm_pos_iff.2 (ld8_ofReal_sub_ne_zero r hz)) 2)
  rw [ld8_u]
  exact mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le) (Complex.arg_nonneg_iff.2 him.le)

/-- **U3.**  `ld8_u r = 1` on the upper semicircle. -/
theorem ld8_u_eq_one {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) (hzr : ‖z‖ = r) :
    ld8_u r z = 1 := by
  obtain ⟨hre, him⟩ := ld8_ratio_re_im r z
  have h1 : (((r : ℂ) + z) / ((r : ℂ) - z)).re = 0 := by rw [hre, hzr, sub_self, zero_div]
  have h2 : 0 < (((r : ℂ) + z) / ((r : ℂ) - z)).im := by
    rw [him]
    exact div_pos (mul_pos (mul_pos two_pos hr) hz) (pow_pos (norm_pos_iff.2 (ld8_ofReal_sub_ne_zero r hz)) 2)
  rw [ld8_u, Complex.arg_eq_pi_div_two_iff.2 ⟨h1, h2⟩]
  field_simp

/-- **U4.**  `ld8_u r` is continuous at `0` with value `0`. -/
theorem ld8_u_continuousAt_zero {r : ℝ} (hr : 0 < r) : ContinuousAt (ld8_u r) 0 ∧ ld8_u r 0 = 0 := by
  have h0 : ((r : ℂ) + 0) / ((r : ℂ) - 0) = 1 := by
    rw [add_zero, sub_zero, div_self (Complex.ofReal_ne_zero.2 hr.ne')]
  refine ⟨?_, by rw [ld8_u, h0, Complex.arg_one, mul_zero]⟩
  have hρ : ContinuousAt (fun z : ℂ => ((r : ℂ) + z) / ((r : ℂ) - z)) 0 :=
    ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by simp [hr.ne'])
  have harg : ContinuousAt Complex.arg 1 := Complex.continuousAt_arg (by simp)
  show ContinuousAt (fun z : ℂ => 2 / π * Complex.arg (((r : ℂ) + z) / ((r : ℂ) - z))) 0
  exact continuousAt_const.mul (harg.comp_of_eq hρ h0)

/-- **U5a.**  `log ((r + z)/(r - z))` is holomorphic on `upperHalf` (the ratio lies in `upperHalf ⊆ slitPlane`). -/
theorem ld8_logRatio_differentiableOn {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ (fun z => Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))) upperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hne := ld8_ofReal_sub_ne_zero r hz'
  have hslit : ((r : ℂ) + z) / ((r : ℂ) - z) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    right
    rw [(ld8_ratio_re_im r z).2]
    exact (div_pos (mul_pos (mul_pos two_pos hr) hz') (pow_pos (norm_pos_iff.2 hne) 2)).ne'
  have hd : DifferentiableAt ℂ (fun z => ((r : ℂ) + z) / ((r : ℂ) - z)) z := by
    fun_prop (disch := exact hne)
  exact (hd.clog hslit).differentiableWithinAt

/-- **U5b.**  `Re (-(2i/π) · log ((r + z)/(r - z))) = ld8_u r z` (unconditional). -/
theorem ld8_re_logRatio (r : ℝ) (z : ℂ) :
    (-(2 * I / (π : ℂ)) * Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))).re = ld8_u r z := by
  have h : -(2 * I / (π : ℂ)) = ((-(2 / π) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.log_im, ld8_u]
  ring

/-- **The half-disc auxiliary function, norm.**  With `Φ z = -(2i/π) log ((r + z)/(r - z))`,
`‖g z · exp (-(1 - Φ z) · L)‖ = ‖g z‖ · exp (-(1 - ld8_u r z) · L)` (unconditional). -/
theorem ld8_halfDisc_aux_norm (g : ℂ → ℂ) (r L : ℝ) (z : ℂ) :
    ‖g z * Complex.exp (-(1 - -(2 * I / (π : ℂ)) * Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))) * (L : ℂ))‖ =
      ‖g z‖ * Real.exp (-(1 - ld8_u r z) * L) := by
  rw [norm_mul, ld8_norm_exp_mul_ofReal, Complex.neg_re, Complex.sub_re, Complex.one_re, ld8_re_logRatio]

/-- **The half-disc auxiliary function, holomorphy.**  For `g` holomorphic on `upperHalf`, `r > 0` and real `L`,
`z ↦ g z · exp (-(1 - Φ z) · L)` is holomorphic on `upperHalf`. -/
theorem ld8_halfDisc_aux_differentiableOn {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g upperHalf) {r : ℝ} (hr : 0 < r)
    (L : ℝ) :
    DifferentiableOn ℂ (fun z => g z * Complex.exp (-(1 - -(2 * I / (π : ℂ)) *
      Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))) * (L : ℂ))) upperHalf := by
  intro z hz
  have h1 : DifferentiableWithinAt ℂ (fun z => Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))) upperHalf z :=
    ld8_logRatio_differentiableOn hr z hz
  exact (hg z hz).mul ((((h1.const_mul (-(2 * I / (π : ℂ)))).const_sub 1).neg.mul_const (L : ℂ)).cexp)

/-- `Re (-(2i/π) · log z + i z / r) = 2/π · arg z - Im z / r` (unconditional): the quarter-disc majorant. -/
theorem ld8_re_quarterExp (r : ℝ) (z : ℂ) :
    (-(2 * I / (π : ℂ)) * Complex.log z + I * z / (r : ℂ)).re = 2 / π * Complex.arg z - z.im / r := by
  have h : -(2 * I / (π : ℂ)) = ((-(2 / π) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [Complex.add_re, h, mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.log_im,
    Complex.div_ofReal_re, Complex.I_mul_re]
  ring

/-- **The quarter-disc auxiliary function, norm.**  With `Ψ z = -(2i/π) log z + i z / r`,
`‖F z · exp (-Ψ z · L)‖ = ‖F z‖ · exp (-(2/π · arg z - Im z / r) · L)` (unconditional). -/
theorem ld8_quarter_aux_norm (F : ℂ → ℂ) (r L : ℝ) (z : ℂ) :
    ‖F z * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log z + I * z / (r : ℂ)) * (L : ℂ))‖ =
      ‖F z‖ * Real.exp (-(2 / π * Complex.arg z - z.im / r) * L) := by
  rw [norm_mul, ld8_norm_exp_mul_ofReal, Complex.neg_re, ld8_re_quarterExp]

/-- **The quarter-disc auxiliary function, holomorphy.**  For `F` holomorphic on `U ⊆ {Re > 0}` and real `r`, `L`,
`z ↦ F z · exp (-Ψ z · L)` is holomorphic on `U`. -/
theorem ld8_quarter_aux_differentiableOn {F : ℂ → ℂ} {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    (hU : ∀ z ∈ U, 0 < z.re) (r L : ℝ) :
    DifferentiableOn ℂ (fun z => F z * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log z + I * z / (r : ℂ)) *
      (L : ℂ))) U := by
  intro z hz
  have h1 : DifferentiableAt ℂ Complex.log z :=
    Complex.differentiableAt_log (mem_slitPlane_iff.2 (Or.inl (hU z hz)))
  have h2 : DifferentiableAt ℂ
      (fun z => Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log z + I * z / (r : ℂ)) * (L : ℂ))) z := by
    fun_prop
  exact (hF z hz).mul h2.differentiableWithinAt

/-- **Jordan's inequality** in the closed first quadrant: `2/π · arg q ≤ Im q / ‖q‖`. -/
theorem ld8_jordan {q : ℂ} (hre : 0 ≤ q.re) (him : 0 ≤ q.im) : 2 / π * Complex.arg q ≤ q.im / ‖q‖ := by
  rw [← Complex.sin_arg]
  exact Real.mul_le_sin (Complex.arg_nonneg_iff.2 him) (Complex.arg_le_pi_div_two_iff.2 (Or.inl hre))

/-- The frontier of the open quarter disc `{0 < Re, 0 < Im, ‖z‖ < r}`: its points have `Re ≥ 0`, `Im ≥ 0`,
`‖q‖ ≤ r`, and lie on one of the three sides. -/
theorem ld8_frontier_quarter {r : ℝ} {q : ℂ} (hq : q ∈ frontier {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ ‖z‖ < r}) :
    0 ≤ q.re ∧ 0 ≤ q.im ∧ ‖q‖ ≤ r ∧ (q.re = 0 ∨ q.im = 0 ∨ ‖q‖ = r) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ ‖z‖ < r} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt continuous_norm continuous_const))
  rw [hopen.frontier_eq] at hq
  obtain ⟨hcl, hnot⟩ := hq
  have hsub : {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ ‖z‖ < r} ⊆ {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ ‖z‖ ≤ r} :=
    fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ ‖z‖ ≤ r} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter (isClosed_le continuous_norm continuous_const))
  obtain ⟨h1, h2, h3⟩ := closure_minimal hsub hclosed hcl
  refine ⟨h1, h2, h3, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  exact hnot ⟨lt_of_le_of_ne h1 (Ne.symm hcon.1), lt_of_le_of_ne h2 (Ne.symm hcon.2.1),
    lt_of_le_of_ne h3 hcon.2.2⟩

/-! ### Stage 1c: Cayley transfer (`ζ ↦ 0`) and Stolz angle ⇒ cone -/

/-- **T1.**  For `‖ζ‖ = 1` and `z ∈ Δ`, `τ z = cayleyInv (-(conj ζ) * z)` lies in `upperHalf` and
`κ (τ z) = z` for `κ w = -ζ * cayley w`. -/
theorem ld8_cayley_leftInv {ζ : ℂ} (hζ : ‖ζ‖ = 1) {z : ℂ} (hz : z ∈ unitDisc) :
    cayleyInv (-(conj ζ) * z) ∈ upperHalf ∧ -ζ * cayley (cayleyInv (-(conj ζ) * z)) = z := by
  have hv : ‖-(conj ζ) * z‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_conj, hζ, one_mul]
    exact mem_ball_zero_iff.1 hz
  refine ⟨cayleyInv_mem_upperHalf hv, ?_⟩
  rw [cayley_cayleyInv hv]
  have hζζ : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj', hζ]
    norm_num
  linear_combination z * hζζ

/-- **T2.**  `κ w = -ζ * cayley w` maps `upperHalf` into `Δ`. -/
theorem ld8_cayley_mem_unitDisc {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : w ∈ upperHalf) :
    -ζ * cayley w ∈ unitDisc := by
  have h := cayley_mem_unitDisc hw
  rw [unitDisc, mem_ball_zero_iff] at h ⊢
  rw [norm_mul, norm_neg, hζ, one_mul]
  exact h

/-- **T2′.**  `f ∘ κ` is holomorphic on `upperHalf`. -/
theorem ld8_cayley_differentiableOn {f : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hf : DifferentiableOn ℂ f unitDisc) :
    DifferentiableOn ℂ (fun w => f (-ζ * cayley w)) upperHalf := by
  intro w hw
  have hden : w + I ≠ 0 := cayley_den_ne_zero hw
  have hκ : DifferentiableAt ℂ (fun w => -ζ * cayley w) w := by
    simp only [cayley]
    fun_prop (disch := exact hden)
  have hfd : DifferentiableAt ℂ f (-ζ * cayley w) :=
    hf.differentiableAt (isOpen_ball.mem_nhds (ld8_cayley_mem_unitDisc hζ hw))
  exact (hfd.comp w hκ).differentiableWithinAt

/-- **T3.**  `τ` is continuous on `Δ`. -/
theorem ld8_cayleyInv_continuousOn {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ContinuousOn (fun z => cayleyInv (-(conj ζ) * z)) unitDisc := by
  intro z hz
  have hv : ‖-(conj ζ) * z‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_conj, hζ, one_mul]
    exact mem_ball_zero_iff.1 hz
  have hden := cayleyInv_den_ne_zero hv
  refine ContinuousAt.continuousWithinAt ?_
  simp only [cayleyInv]
  exact ContinuousAt.div₀ (by fun_prop) (by fun_prop) hden

/-- **T3′.**  `τ z → 0` as `z → ζ` (`τ` is continuous at `ζ`, where `1 + conj ζ · ζ = 2 ≠ 0`, and `τ ζ = 0`). -/
theorem ld8_cayleyInv_tendsto {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Tendsto (fun z => cayleyInv (-(conj ζ) * z)) (𝓝 ζ) (𝓝 0) := by
  have hζζ : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hζ]
    norm_num
  have hden : (1 : ℂ) - -(conj ζ) * ζ ≠ 0 := by
    rw [neg_mul, hζζ]
    norm_num
  have hval : cayleyInv (-(conj ζ) * ζ) = 0 := by
    rw [cayleyInv, neg_mul, hζζ]
    simp
  have hc : ContinuousAt (fun z => cayleyInv (-(conj ζ) * z)) ζ := by
    simp only [cayleyInv]
    exact ContinuousAt.div₀ (by fun_prop) (by fun_prop) hden
  have h2 : Tendsto (fun z => cayleyInv (-(conj ζ) * z)) (𝓝 ζ) (𝓝 (cayleyInv (-(conj ζ) * ζ))) := hc
  rwa [hval] at h2

/-- The imaginary part of `cayleyInv w` (the computation inside `cayleyInv_mem_upperHalf`; unconditional: at `w = 1`
both sides are `0`). -/
theorem ld8_cayleyInv_im (w : ℂ) : (cayleyInv w).im = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, cayleyInv, Complex.div_im, div_sub_div_same]
  congr 1
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

/-- **T5 (Stolz angle ⇒ cone).**  For `z ∈ stolzAngle ζ M`, `τ z` lies in the cone `‖w‖ < M · Im w`, and
`‖τ z‖ ≤ ‖z - ζ‖` when `‖z - ζ‖ ≤ 1`.  (`τ z = i (ζ - z)/(ζ + z)`, so `‖τ z‖ = ‖z - ζ‖/‖z + ζ‖` and
`Im τ z = (1 - ‖z‖²)/‖z + ζ‖²`.) -/
theorem ld8_stolz_cayley {ζ : ℂ} (hζ : ‖ζ‖ = 1) {M : ℝ} {z : ℂ} (hz : z ∈ stolzAngle ζ M)
    (hzζ : ‖z - ζ‖ ≤ 1) :
    ‖cayleyInv (-(conj ζ) * z)‖ < M * (cayleyInv (-(conj ζ) * z)).im ∧
      ‖cayleyInv (-(conj ζ) * z)‖ ≤ ‖z - ζ‖ := by
  obtain ⟨hzD, hzS⟩ := hz
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.1 hzD
  have hζζ : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hζ]
    norm_num
  have hv : ‖-(conj ζ) * z‖ = ‖z‖ := by rw [norm_mul, norm_neg, Complex.norm_conj, hζ, one_mul]
  have hvlt : ‖-(conj ζ) * z‖ < 1 := by rw [hv]; exact hzn
  have hden := cayleyInv_den_ne_zero hvlt
  have e1 : (1 : ℂ) + -(conj ζ) * z = conj ζ * (ζ - z) := by linear_combination -hζζ
  have e2 : (1 : ℂ) - -(conj ζ) * z = conj ζ * (ζ + z) := by linear_combination -hζζ
  have hB : ‖(1 : ℂ) - -(conj ζ) * z‖ = ‖z + ζ‖ := by
    rw [e2, norm_mul, Complex.norm_conj, hζ, one_mul, add_comm]
  have hA : ‖(1 : ℂ) + -(conj ζ) * z‖ = ‖z - ζ‖ := by
    rw [e1, norm_mul, Complex.norm_conj, hζ, one_mul, norm_sub_rev]
  have hnorm : ‖cayleyInv (-(conj ζ) * z)‖ = ‖z - ζ‖ / ‖z + ζ‖ := by
    rw [cayleyInv, norm_div, norm_mul, Complex.norm_I, one_mul, hA, hB]
  have him : (cayleyInv (-(conj ζ) * z)).im = (1 - ‖z‖ ^ 2) / ‖z + ζ‖ ^ 2 := by
    rw [ld8_cayleyInv_im, hv, hB]
  have hBpos : 0 < ‖z + ζ‖ := by
    rw [← hB]
    exact norm_pos_iff.2 hden
  have hBle : ‖z + ζ‖ ≤ 1 + ‖z‖ := by
    calc ‖z + ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by rw [hζ, add_comm]
  have hMpos : 0 ≤ M * (1 - ‖z‖) := (norm_nonneg _).trans hzS.le
  refine ⟨?_, ?_⟩
  · have key : ‖z - ζ‖ * ‖z + ζ‖ < M * (1 - ‖z‖ ^ 2) := by
      calc ‖z - ζ‖ * ‖z + ζ‖ < M * (1 - ‖z‖) * ‖z + ζ‖ := mul_lt_mul_of_pos_right hzS hBpos
        _ ≤ M * (1 - ‖z‖) * (1 + ‖z‖) := mul_le_mul_of_nonneg_left hBle hMpos
        _ = M * (1 - ‖z‖ ^ 2) := by ring
    rw [hnorm, him, mul_div_assoc', div_lt_div_iff₀ hBpos (pow_pos hBpos 2)]
    calc ‖z - ζ‖ * ‖z + ζ‖ ^ 2 = ‖z - ζ‖ * ‖z + ζ‖ * ‖z + ζ‖ := by ring
      _ < M * (1 - ‖z‖ ^ 2) * ‖z + ζ‖ := mul_lt_mul_of_pos_right key hBpos
  · rw [hnorm]
    apply div_le_self (norm_nonneg _)
    have h2 : ‖(z + ζ) - (z - ζ)‖ ≤ ‖z + ζ‖ + ‖z - ζ‖ := norm_sub_le _ _
    have e : (z + ζ) - (z - ζ) = 2 * ζ := by ring
    rw [e, norm_mul, hζ, mul_one] at h2
    norm_num at h2
    linarith

/-! ### Stage 1d: quarter disc and cone -/

/-- **Quarter-disc bound (two-constants form).**  Let `F` be holomorphic on `upperHalf` with `‖F‖ ≤ 1` there, and
`‖F (i y)‖ ≤ δ < 1` for `0 < y ≤ r`.  On the open quarter disc `Q = {0 < Re, 0 < Im, ‖z‖ < r}`,
`‖F z‖ ≤ exp ((2/π · arg z - Im z / r) · log δ)`.

Proof: `v z = 2/π · arg z - Im z / r = Re Ψ z` with `Ψ z = -(2i/π) log z + i z / r` (`ld8_re_quarterExp`) is
harmonic on `Q`, `v ≤ 1` there, `v = 1 - y/r` at `i y`, `v = 0` on `(0, r]`, and `v ≤ 0` on the arc (Jordan's
inequality, `ld8_jordan`).  So `G = F · exp (-Ψ · log δ)`, with `‖G‖ = ‖F‖ · exp (-v log δ)`, is holomorphic and
bounded on `Q`, and `limsup ‖G‖ ≤ 1` at every frontier point `q ≠ 0` (`ld8_frontier_quarter`): on `i (0, r]` and on
the arc by continuity of `G` at `q ∈ upperHalf`; on `(0, r]` through the continuous majorant `exp (-v log δ)`, so
that `F` is not evaluated off `upperHalf`.  The maximum principle `ld8_maxmod_upper` (exceptional point `0`) gives
`‖G‖ ≤ 1` on `Q`. -/
theorem ld8_quarter {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf)
    (hF1 : ∀ z ∈ upperHalf, ‖F z‖ ≤ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ y ∈ Ioc 0 r, ‖F ((y : ℂ) * I)‖ ≤ δ) {z : ℂ} (hzre : 0 < z.re) (hzim : 0 < z.im)
    (hzr : ‖z‖ < r) :
    ‖F z‖ ≤ Real.exp ((2 / π * Complex.arg z - z.im / r) * Real.log δ) := by
  have hL : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  have hQo : IsOpen {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt continuous_norm continuous_const))
  have hQb : Bornology.IsBounded {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r} :=
    isBounded_ball.subset fun w hw => mem_ball_zero_iff.2 hw.2.2
  have hQc : IsPreconnected {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r} := by
    have h := (convex_halfSpace_re_gt (0 : ℝ)).inter
      ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_ball (0 : ℂ) r))
    have e : {c : ℂ | 0 < c.re} ∩ ({c : ℂ | 0 < c.im} ∩ ball (0 : ℂ) r) =
        {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r} := by
      ext w
      simp only [mem_inter_iff, mem_ofPred_eq, mem_ball_zero_iff]
    rw [e] at h
    exact h.isPreconnected
  have hQH : {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r} ⊆ upperHalf := fun w hw => hw.2.1
  -- `‖G‖ ≤ δ⁻¹` on the quarter disc, since `v ≤ 1` there
  have hK : ∀ w ∈ {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r},
      ‖F w * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log w + I * w / (r : ℂ)) * (Real.log δ : ℂ))‖ ≤
        Real.exp (-Real.log δ) := by
    intro w hw
    rw [ld8_quarter_aux_norm]
    have h1 : Complex.arg w ≤ π / 2 := Complex.arg_le_pi_div_two_iff.2 (Or.inl hw.1.le)
    have h2 : 2 / π * Complex.arg w ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one Real.pi_pos]
      linarith
    have h3 : 0 ≤ w.im / r := div_nonneg hw.2.1.le hr.le
    calc ‖F w‖ * Real.exp (-(2 / π * Complex.arg w - w.im / r) * Real.log δ)
        ≤ 1 * Real.exp (-Real.log δ) := by
          refine mul_le_mul (hF1 w hw.2.1) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le zero_le_one
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (2 / π * Complex.arg w - w.im / r))
            (neg_nonneg.2 hL.le)]
      _ = Real.exp (-Real.log δ) := one_mul _
  -- the boundary values: `limsup ‖G‖ ≤ 1` at every frontier point `q ≠ 0`
  have hbd : ∀ q ∈ frontier {w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r}, q ≠ 0 → ∀ ε > 0,
      ∀ᶠ w in 𝓝[{w : ℂ | 0 < w.re ∧ 0 < w.im ∧ ‖w‖ < r}] q,
        ‖F w * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log w + I * w / (r : ℂ)) * (Real.log δ : ℂ))‖ ≤
          1 + ε := by
    intro q hq hq0
    obtain ⟨hqre, hqim, hqr, hside⟩ := ld8_frontier_quarter hq
    by_cases hqim0 : q.im = 0
    · -- the real side `(0, r]`: a continuous majorant, `F` is not evaluated at `q`
      have hqre' : 0 < q.re := by
        rcases hqre.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hq0
          apply Complex.ext
          · simp [← h]
          · simp [hqim0]
      refine ld8_eventually_norm_le_of_majorant
        (B := fun w => Real.exp (-(2 / π * Complex.arg w - w.im / r) * Real.log δ)) (fun w hw => ?_) ?_ ?_
      · rw [ld8_quarter_aux_norm]
        exact mul_le_of_le_one_left (Real.exp_pos _).le (hF1 w hw.2.1)
      · have ha : ContinuousAt Complex.arg q :=
          Complex.continuousAt_arg (mem_slitPlane_iff.2 (Or.inl hqre'))
        fun_prop
      · have h0 : Complex.arg q = 0 := Complex.arg_eq_zero_iff.2 ⟨hqre, hqim0⟩
        simp [h0, hqim0]
    · -- `q ∈ upperHalf`: the auxiliary function is continuous at `q`
      have hqpos : 0 < q.im := lt_of_le_of_ne hqim (Ne.symm hqim0)
      have hqH : q ∈ upperHalf := hqpos
      have hFc : ContinuousAt F q := (hF.differentiableAt (isOpen_upperHalf.mem_nhds hqH)).continuousAt
      have hlog : ContinuousAt Complex.log q :=
        continuousAt_clog (mem_slitPlane_iff.2 (Or.inr hqim0))
      have hGc : ContinuousAt (fun w => F w * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log w +
          I * w / (r : ℂ)) * (Real.log δ : ℂ))) q := by
        fun_prop
      have hGq : ‖F q * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log q + I * q / (r : ℂ)) *
          (Real.log δ : ℂ))‖ ≤ 1 := by
        rw [ld8_quarter_aux_norm]
        rcases hside with hre0 | him0 | hqr'
        · -- the imaginary side `i (0, r]`: `v = 1 - y/r` and `‖F‖ ≤ δ`
          have harg : Complex.arg q = π / 2 := Complex.arg_eq_pi_div_two_iff.2 ⟨hre0, hqpos⟩
          have hq' : q = ((q.im : ℝ) : ℂ) * I := by
            apply Complex.ext <;> simp [hre0]
          have hFq : ‖F q‖ ≤ δ := by
            calc ‖F q‖ = ‖F ((q.im : ℂ) * I)‖ := by rw [← hq']
              _ ≤ δ := hrad _ ⟨hqpos, (Complex.im_le_norm q).trans hqr⟩
          have hpi : (2 : ℝ) / π * (π / 2) = 1 := by field_simp
          rw [harg, hpi]
          calc ‖F q‖ * Real.exp (-(1 - q.im / r) * Real.log δ)
              ≤ δ * Real.exp (-(1 - q.im / r) * Real.log δ) :=
                mul_le_mul_of_nonneg_right hFq (Real.exp_pos _).le
            _ = Real.exp (Real.log δ) * Real.exp (-(1 - q.im / r) * Real.log δ) := by
                rw [Real.exp_log hδ0]
            _ = Real.exp (q.im / r * Real.log δ) := by
                rw [← Real.exp_add]
                congr 1
                ring
            _ ≤ Real.exp 0 :=
                Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hqpos.le hr.le) hL.le)
            _ = 1 := Real.exp_zero
        · exact absurd him0 hqim0
        · -- the arc: `v ≤ 0` by Jordan's inequality
          have hj := ld8_jordan hqre hqim
          rw [hqr'] at hj
          have hv : 2 / π * Complex.arg q - q.im / r ≤ 0 := by linarith
          calc ‖F q‖ * Real.exp (-(2 / π * Complex.arg q - q.im / r) * Real.log δ) ≤ 1 * Real.exp 0 := by
                refine mul_le_mul (hF1 q hqH) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le zero_le_one
                exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.2 hv) hL.le
            _ = 1 := by rw [Real.exp_zero, one_mul]
      exact ld8_eventually_norm_le hGc hGq _
  have hmax : ‖F z * Complex.exp (-(-(2 * I / (π : ℂ)) * Complex.log z + I * z / (r : ℂ)) *
      (Real.log δ : ℂ))‖ ≤ 1 :=
    ld8_maxmod_upper hQo hQb hQc hQH
      (ld8_quarter_aux_differentiableOn (hF.mono hQH) (fun w hw => hw.1) r (Real.log δ)) hK zero_le_one hbd z
      ⟨hzre, hzim, hzr⟩
  rw [ld8_quarter_aux_norm, neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)] at hmax
  exact hmax

/-- **Quarter cone.**  Under the hypotheses of `ld8_quarter`, on the closed-right half of the cone
`‖z‖ < M · Im z` near `0` (`‖z‖ < r/(π M)`), `‖F z‖ ≤ exp (log δ / (π M))`: there `arg z ≥ sin (arg z) > 1/M`. -/
theorem ld8_quarter_cone {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf)
    (hF1 : ∀ z ∈ upperHalf, ‖F z‖ ≤ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ y ∈ Ioc 0 r, ‖F ((y : ℂ) * I)‖ ≤ δ) {M : ℝ} (hM : 1 < M) {z : ℂ}
    (hzre : 0 ≤ z.re) (hz : ‖z‖ < M * z.im) (hzr : ‖z‖ < r / (π * M)) :
    ‖F z‖ ≤ Real.exp (Real.log δ / (π * M)) := by
  have hL : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  have hM0 : 0 < M := by linarith
  have hπM : 1 < π * M := by
    have := mul_lt_mul_of_pos_left hM Real.pi_pos
    linarith [Real.pi_gt_three]
  have hπM0 : 0 < π * M := by linarith
  have hzim : 0 < z.im := pos_of_mul_pos_right ((norm_nonneg z).trans_lt hz) hM0.le
  have hzn : 0 < ‖z‖ := hzim.trans_le (Complex.im_le_norm z)
  have hzr' : ‖z‖ < r := hzr.trans_le (div_le_self hr.le hπM.le)
  rcases hzre.lt_or_eq with hre | hre
  · refine (ld8_quarter hF hF1 hδ0 hδ1 hr hrad hre hzim hzr').trans (Real.exp_le_exp.2 ?_)
    have harg : 1 / M < Complex.arg z := by
      have h1 : Real.sin (Complex.arg z) ≤ Complex.arg z := Real.sin_le (Complex.arg_nonneg_iff.2 hzim.le)
      rw [Complex.sin_arg] at h1
      have h2 : 1 / M < z.im / ‖z‖ := by
        rw [div_lt_div_iff₀ hM0 hzn]
        linarith
      linarith
    have himr : z.im / r < 1 / (π * M) := by
      rw [div_lt_div_iff₀ hr hπM0]
      have h3 : ‖z‖ * (π * M) < r := by rwa [lt_div_iff₀ hπM0] at hzr
      have h4 := mul_le_mul_of_nonneg_right (Complex.im_le_norm z) hπM0.le
      linarith
    have hv : 1 / (π * M) < 2 / π * Complex.arg z - z.im / r := by
      have h4 : 2 / π * (1 / M) < 2 / π * Complex.arg z :=
        mul_lt_mul_of_pos_left harg (div_pos two_pos Real.pi_pos)
      have h5 : 2 / π * (1 / M) = 2 * (1 / (π * M)) := by ring
      linarith
    calc (2 / π * Complex.arg z - z.im / r) * Real.log δ ≤ 1 / (π * M) * Real.log δ :=
          mul_le_mul_of_nonpos_right hv.le hL.le
      _ = Real.log δ / (π * M) := by ring
  · have hz' : z = ((z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [← hre]
    have hy : z.im ∈ Ioc 0 r := ⟨hzim, (Complex.im_le_norm z).trans hzr'.le⟩
    have hLle : Real.log δ ≤ Real.log δ / (π * M) := by
      rw [le_div_iff₀ hπM0]
      nlinarith [mul_pos (neg_pos.2 hL) (sub_pos.2 hπM)]
    calc ‖F z‖ = ‖F ((z.im : ℂ) * I)‖ := by rw [← hz']
      _ ≤ δ := hrad _ hy
      _ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (Real.log δ / (π * M)) := Real.exp_le_exp.2 hLle

/-- **CONE.**  If `F` is holomorphic on `upperHalf`, `‖F‖ ≤ 1` there, and `F (i y) → 0` as `y → 0⁺`, then `F z → 0`
as `z → 0` in every cone `‖z‖ < M · Im z`, `M > 1`: `ld8_quarter_cone` for `Re z ≥ 0`, and for `Re z < 0` the same
applied to the reflection `conj ∘ F ∘ σ` at `σ z`, `σ z = -conj z`. -/
theorem ld8_cone {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf)
    (hF1 : ∀ z ∈ upperHalf, ‖F z‖ ≤ 1)
    (hrad : ∀ δ > (0 : ℝ), ∃ y₀ > (0 : ℝ), ∀ y ∈ Ioo (0 : ℝ) y₀, ‖F ((y : ℂ) * I)‖ ≤ δ) {M : ℝ} (hM : 1 < M)
    {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < M * z.im → ‖z‖ < ρ → ‖F z‖ ≤ η := by
  have hM0 : 0 < M := by linarith
  have hπM0 : 0 < π * M := mul_pos Real.pi_pos hM0
  have him : ∀ z : ℂ, ‖z‖ < M * z.im → 0 < z.im := fun z hz =>
    pos_of_mul_pos_right ((norm_nonneg z).trans_lt hz) hM0.le
  rcases le_or_gt 1 η with hη1 | hη1
  · exact ⟨1, one_pos, fun z hz _ => (hF1 z (him z hz)).trans hη1⟩
  have hL : π * M * Real.log η < 0 := mul_neg_of_pos_of_neg hπM0 (Real.log_neg hη hη1)
  obtain ⟨y₀, hy₀, hy₀δ⟩ := hrad (Real.exp (π * M * Real.log η)) (Real.exp_pos _)
  have hr : 0 < y₀ / 2 := half_pos hy₀
  have hrad' : ∀ y ∈ Ioc 0 (y₀ / 2), ‖F ((y : ℂ) * I)‖ ≤ Real.exp (π * M * Real.log η) :=
    fun y hy => hy₀δ y ⟨hy.1, hy.2.trans_lt (half_lt_self hy₀)⟩
  have hδ1 : Real.exp (π * M * Real.log η) < 1 := Real.exp_lt_one_iff.2 hL
  have hval : Real.exp (Real.log (Real.exp (π * M * Real.log η)) / (π * M)) = η := by
    rw [Real.log_exp, mul_div_cancel_left₀ _ hπM0.ne', Real.exp_log hη]
  refine ⟨y₀ / 2 / (π * M), div_pos hr hπM0, fun z hz hzρ => ?_⟩
  rw [← hval]
  rcases le_or_gt 0 z.re with hre | hre
  · exact ld8_quarter_cone hF hF1 (Real.exp_pos _) hδ1 hr hrad' hM hre hz hzρ
  · have hG1 : ∀ w ∈ upperHalf, ‖conj (F (-conj w))‖ ≤ 1 := fun w hw => by
      have hw0 : 0 < w.im := hw
      rw [Complex.norm_conj]
      exact hF1 _ (show 0 < (-conj w).im by simpa using hw0)
    have hGrad : ∀ y ∈ Ioc 0 (y₀ / 2),
        ‖conj (F (-conj ((y : ℂ) * I)))‖ ≤ Real.exp (π * M * Real.log η) := by
      intro y hy
      rw [Complex.norm_conj, show -conj ((y : ℂ) * I) = (y : ℂ) * I by simp]
      exact hrad' y hy
    have hz' : ‖-conj z‖ < M * (-conj z).im := by simpa using hz
    have hzρ' : ‖-conj z‖ < y₀ / 2 / (π * M) := by simpa using hzρ
    have hre' : 0 ≤ (-conj z).re := by
      simp only [Complex.neg_re, Complex.conj_re]
      linarith
    have h := ld8_quarter_cone (ld8_reflect_differentiableOn hF) hG1 (Real.exp_pos _) hδ1 hr hGrad hM hre'
      hz' hzρ'
    simpa using h

/-! ### Stage 2: separation -/

/-- **Separation by the curve and its mirror image.**  Let `S` be closed and preconnected with `0 ∈ S`,
`S \ {0} ⊆ upperHalf` and a point `s₀ ∈ S` with `r ≤ ‖s₀‖`, and let `K = S ∪ σ(S)`, `σ z = -conj z`.  If `U` is an
open preconnected subset of `(upperHalf ∩ ball 0 r) \ K` containing a point `i y`, then `0` is the only real point of
`closure U`.

Proof: suppose `x ∈ closure U` is real, `x ≠ 0`.  Then `x ∉ K` (`K` meets the real axis only at `0`), so some
`ball x ρ` misses the closed set `K`; pick `w ∈ U ∩ ball x ρ` and put `b = Im w > 0`.  The path from `i y` to `w`
inside `U` (`s20v_polygon_path`), followed by `[w, conj w] ⊆ ball x ρ` and `[conj w, -b i] ⊆ {Im < 0}`, lies in the
`σ`-invariant set `W = ball 0 r \ K`, which omits `0`.  Closed up by its mirror image, it winds a non-zero number of
times around `0` (`ld8_polyWinding_reflect_ne_zero`: `(-b i)/(i y) = -b/y < 0`), but also `0` times
(`ld8_polyTrace_reflect_subset`, `ld8_polyWinding_eq_zero`): its trace lies in `ball 0 r` and misses the preconnected
set `S`, which joins `0` to `s₀`. -/
theorem ld8_sep {r : ℝ} (hr : 0 < r) {S : Set ℂ} (hSc : IsClosed S) (hSp : IsPreconnected S)
    (hS0 : (0 : ℂ) ∈ S) (hSH : ∀ z ∈ S, z ≠ 0 → 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ S)
    (hs₀r : r ≤ ‖s₀‖) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUsub : U ⊆ (upperHalf ∩ ball 0 r) \ (S ∪ (fun z => -conj z) '' S))
    {y : ℝ} (hyU : (y : ℂ) * I ∈ U) {x : ℂ} (hx : x ∈ closure U) (hxim : x.im = 0) : x = 0 := by
  by_contra hx0
  have hKc : IsClosed (S ∪ (fun z => -conj z) '' S) := ld8_isClosed_reflect_union hSc
  have hσmem : ∀ z : ℂ, z ∈ (fun z => -conj z) '' S → -conj z ∈ S := by
    rintro z ⟨s, hs, rfl⟩
    simpa using hs
  -- `K = S ∪ σ(S)` lies in the closed upper half-plane and meets the real axis only at `0`
  have hKim : ∀ z ∈ S ∪ (fun z => -conj z) '' S, 0 ≤ z.im := by
    rintro z (hz | hz)
    · by_cases hz0 : z = 0
      · simp [hz0]
      · exact (hSH z hz hz0).le
    · by_cases hz0 : -conj z = 0
      · have hz0' : z = 0 := by simpa using hz0
        simp [hz0']
      · have h := hSH _ (hσmem z hz) hz0
        simp only [Complex.neg_im, Complex.conj_im, neg_neg] at h
        exact h.le
  have hxK : x ∉ S ∪ (fun z => -conj z) '' S := by
    rintro (hxS | hxS)
    · have h := hSH x hxS hx0
      linarith
    · have hne : -conj x ≠ 0 := fun h0 => hx0 (by simpa using h0)
      have h := hSH _ (hσmem x hxS) hne
      simp only [Complex.neg_im, Complex.conj_im, neg_neg] at h
      linarith
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl x hxK
  obtain ⟨w, hwU, hwx⟩ := Metric.mem_closure_iff.1 hx ρ hρ
  have hwH : 0 < w.im := (hUsub hwU).1.1
  have hwr : ‖w‖ < r := mem_ball_zero_iff.1 (hUsub hwU).1.2
  have hy : 0 < y := by
    have h : 0 < ((y : ℂ) * I).im := (hUsub hyU).1.1
    simpa using h
  -- the reflection-invariant set `W = ball 0 r \ K`, which omits `0`
  have hW : ∀ z ∈ ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S),
      -conj z ∈ ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S) := by
    rintro z ⟨hzb, hzK⟩
    refine ⟨by simpa using hzb, ?_⟩
    rintro (hz | hz)
    · exact hzK (Or.inr ⟨-conj z, hz, by simp⟩)
    · exact hzK (Or.inl (by simpa using hσmem _ hz))
  have hW0 : ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S) ⊆ {z : ℂ | z ≠ 0} := by
    rintro z ⟨-, hzK⟩ rfl
    exact hzK (Or.inl hS0)
  have hUW : U ⊆ ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S) := fun z hz =>
    ⟨(hUsub hz).1.2, (hUsub hz).2⟩
  -- the path `i y, P, conj w, -(Im w) i` in `W`: `P` in `U`, then across the real axis inside `ball x ρ`,
  -- then horizontally in the lower half-plane to the imaginary axis
  obtain ⟨P, hPU, hPw⟩ := s20v_polygon_path hUo hUc hyU hwU
  have hconj : ‖conj w - x‖ = ‖w - x‖ := by
    have hxc : conj x = x := Complex.conj_eq_iff_im.2 hxim
    rw [← Complex.norm_conj (w - x), map_sub, hxc]
  have hseg1 : segment ℝ w (conj w) ⊆ ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S) := by
    have h1 : segment ℝ w (conj w) ⊆ ball x ρ :=
      (convex_ball x ρ).segment_subset (by rw [mem_ball, dist_comm]; exact hwx)
        (by rw [mem_ball, dist_eq_norm, hconj, ← dist_eq_norm, dist_comm]; exact hwx)
    have h2 : segment ℝ w (conj w) ⊆ ball (0 : ℂ) r :=
      (convex_ball (0 : ℂ) r).segment_subset (mem_ball_zero_iff.2 hwr)
        (mem_ball_zero_iff.2 (by rwa [Complex.norm_conj]))
    exact fun z hz => ⟨h2 hz, hρK (h1 hz)⟩
  have he : ‖((-w.im : ℝ) : ℂ) * I‖ < r := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hwH]
    exact (Complex.im_le_norm w).trans_lt hwr
  have hseg2 : segment ℝ (conj w) (((-w.im : ℝ) : ℂ) * I) ⊆
      ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S) := by
    have h1 : segment ℝ (conj w) (((-w.im : ℝ) : ℂ) * I) ⊆ {c : ℂ | c.im < 0} :=
      (convex_halfSpace_im_lt (0 : ℝ)).segment_subset (by simpa using hwH) (by simpa using hwH)
    have h2 : segment ℝ (conj w) (((-w.im : ℝ) : ℂ) * I) ⊆ ball (0 : ℂ) r :=
      (convex_ball (0 : ℂ) r).segment_subset (mem_ball_zero_iff.2 (by rwa [Complex.norm_conj]))
        (mem_ball_zero_iff.2 he)
    exact fun z hz => ⟨h2 hz, fun hzK => absurd (hKim z hzK) (not_le.2 (h1 hz))⟩
  have hlQ : SegsIn (ball (0 : ℂ) r \ (S ∪ (fun z => -conj z) '' S)) ((y : ℂ) * I)
      (P ++ [conj w, ((-w.im : ℝ) : ℂ) * I]) := by
    rw [segsIn_append, hPw]
    exact ⟨s20v_segsIn_mono hUW hPU, hseg1, hseg2, trivial⟩
  have hlast : lastOf ((y : ℂ) * I) (P ++ [conj w, ((-w.im : ℝ) : ℂ) * I]) = ((-w.im : ℝ) : ℂ) * I := by
    rw [lastOf_append, hPw]
    rfl
  have hare : ((y : ℂ) * I).re = 0 := by simp
  have hre : (lastOf ((y : ℂ) * I) (P ++ [conj w, ((-w.im : ℝ) : ℂ) * I])).re = 0 := by
    rw [hlast]
    simp
  have ha0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hy.ne') Complex.I_ne_zero
  have hneg : (lastOf ((y : ℂ) * I) (P ++ [conj w, ((-w.im : ℝ) : ℂ) * I]) / ((y : ℂ) * I)).re < 0 := by
    rw [hlast, mul_div_mul_right _ _ Complex.I_ne_zero, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (neg_lt_zero.2 hwH) hy
  -- the reflected closed polygon winds `≠ 0` times around `0` (parity) and `0` times (it misses `S ∋ 0, s₀`)
  have hne := ld8_polyWinding_reflect_ne_zero ha0 hare (s20v_segsIn_mono hW0 hlQ) hre hneg
  have htrace := ld8_polyTrace_reflect_subset hW (hUW hyU) hare hlQ hre
  exact hne (ld8_polyWinding_eq_zero hr (htrace.trans sdiff_subset) hSp hS0 hs₀ hs₀r
    fun s hs hst => (htrace hst).2 (Or.inl hs))

/-! ### Stage 3: half disc -/

/-- **Half-disc bound (radial core).**  In the setting of `ld8_sep`, let moreover `F` be holomorphic on `upperHalf`
with `‖F‖ ≤ 1` there and `‖F‖ ≤ ε < 1` on `S \ {0}`.  Then for `0 < y < r`,
`‖F (i y)‖² ≤ exp ((1 - ld8_u r (i y)) · log ε)`.

Proof: `g z = F z · conj (F (σ z))` is holomorphic on `upperHalf` with `‖g‖ ≤ 1`, `‖g (i y)‖ = ‖F (i y)‖²`
(`σ` fixes `i y`) and `‖g‖ ≤ ε` on `K ∩ upperHalf`, `K = S ∪ σ(S)`.  If `i y ∈ K`, then `i y ∈ S` and the bound is
immediate.  Otherwise put `Φ z = -(2i/π) log ((r + z)/(r - z))`, so that `Re Φ = u = ld8_u r`: the function
`G = g · exp (-(1 - Φ) · log ε)` is holomorphic and bounded on `upperHalf` (`u ≥ 0`), with `‖G‖ ≤ exp (u log ε) ≤ 1` on
`K ∩ upperHalf` and `‖G‖ = ‖g‖ ≤ 1` on the upper semicircle (`u = 1` there).  By `ld8_sep`, `0` is the only real
boundary point of the component of `i y` in `(upperHalf ∩ ball 0 r) \ K`, and `ld8_component_maxmod` gives
`‖G (i y)‖ ≤ 1`, i.e. the claim. -/
theorem ld8_halfDisc {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf)
    (hF1 : ∀ z ∈ upperHalf, ‖F z‖ ≤ 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {r : ℝ} (hr : 0 < r)
    {S : Set ℂ} (hSc : IsClosed S) (hSp : IsPreconnected S) (hS0 : (0 : ℂ) ∈ S)
    (hSH : ∀ z ∈ S, z ≠ 0 → 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ S) (hs₀r : r ≤ ‖s₀‖)
    (hSε : ∀ z ∈ S, z ≠ 0 → ‖F z‖ ≤ ε) {y : ℝ} (hy : y ∈ Ioo 0 r) :
    ‖F ((y : ℂ) * I)‖ ^ 2 ≤ Real.exp ((1 - ld8_u r ((y : ℂ) * I)) * Real.log ε) := by
  have hL : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hyH : 0 < ((y : ℂ) * I).im := by simpa using hy.1
  have hσH : ∀ z ∈ upperHalf, -conj z ∈ upperHalf := fun z hz => by
    have hz0 : 0 < z.im := hz
    show 0 < (-conj z).im
    simpa using hz0
  -- `g = F · conj (F ∘ σ)`: holomorphic, `‖g‖ ≤ 1`, `‖g‖ ≤ ε` on `K ∩ upperHalf`, `‖g (i y)‖ = ‖F (i y)‖²`
  set g : ℂ → ℂ := fun z => F z * conj (F (-conj z))
  have hgd : DifferentiableOn ℂ g upperHalf := hF.mul (ld8_reflect_differentiableOn hF)
  have hg1 : ∀ z ∈ upperHalf, ‖g z‖ ≤ 1 := fun z hz => by
    show ‖F z * conj (F (-conj z))‖ ≤ 1
    rw [norm_mul, Complex.norm_conj]
    calc ‖F z‖ * ‖F (-conj z)‖ ≤ 1 * 1 :=
          mul_le_mul (hF1 z hz) (hF1 _ (hσH z hz)) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgK : ∀ q ∈ upperHalf, q ∈ S ∪ (fun z => -conj z) '' S → ‖g q‖ ≤ ε := by
    intro q hq hqK
    have hq0 : q ≠ 0 := by
      rintro rfl
      have h : (0 : ℝ) < (0 : ℂ).im := hq
      simp at h
    show ‖F q * conj (F (-conj q))‖ ≤ ε
    rw [norm_mul, Complex.norm_conj]
    rcases hqK with hqS | ⟨s, hs, hsq⟩
    · calc ‖F q‖ * ‖F (-conj q)‖ ≤ ε * 1 :=
            mul_le_mul (hSε q hqS hq0) (hF1 _ (hσH q hq)) (norm_nonneg _) hε0.le
        _ = ε := mul_one ε
    · have hsq' : -conj s = q := hsq
      have hqs : -conj q = s := by
        rw [← hsq']
        simp
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hq0
        rw [← hsq']
        simp
      rw [hqs]
      calc ‖F q‖ * ‖F s‖ ≤ 1 * ε := mul_le_mul (hF1 q hq) (hSε s hs hs0) (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
  have hgy : ‖g ((y : ℂ) * I)‖ = ‖F ((y : ℂ) * I)‖ ^ 2 := by
    show ‖F ((y : ℂ) * I) * conj (F (-conj ((y : ℂ) * I)))‖ = _
    rw [ld8_reflect_fix (by simp : ((y : ℂ) * I).re = 0), norm_mul, Complex.norm_conj, sq]
  have hu0 : 0 ≤ ld8_u r ((y : ℂ) * I) := ld8_u_nonneg hr hyH
  by_cases hyK : (y : ℂ) * I ∈ S ∪ (fun z => -conj z) '' S
  · -- `i y ∈ K`, hence `i y ∈ S` (`σ` fixes the imaginary axis): the bound is immediate
    have hyS : (y : ℂ) * I ∈ S := by
      rcases hyK with h | ⟨s, hs, hsq⟩
      · exact h
      · have hsq' : -conj s = (y : ℂ) * I := hsq
        have hs' : s = (y : ℂ) * I := by
          rw [← ld8_reflect_fix (by simp : ((y : ℂ) * I).re = 0), ← hsq']
          simp
        rw [← hs']
        exact hs
    have hy0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hy.1.ne') Complex.I_ne_zero
    calc ‖F ((y : ℂ) * I)‖ ^ 2 ≤ ‖F ((y : ℂ) * I)‖ := by
          rw [sq]
          exact mul_le_of_le_one_left (norm_nonneg _) (hF1 _ hyH)
      _ ≤ ε := hSε _ hyS hy0
      _ = Real.exp (Real.log ε) := (Real.exp_log hε0).symm
      _ ≤ Real.exp ((1 - ld8_u r ((y : ℂ) * I)) * Real.log ε) := by
          apply Real.exp_le_exp.2
          nlinarith [mul_nonneg hu0 (neg_nonneg.2 hL.le)]
  · -- the component of `i y` in `(upperHalf ∩ ball 0 r) \ K`: separation, then the maximum principle for
    -- `G = g · exp (-(1 - Φ) log ε)`
    have hyV : (y : ℂ) * I ∈ (upperHalf ∩ ball 0 r) \ (S ∪ (fun z => -conj z) '' S) := by
      refine ⟨⟨hyH, ?_⟩, hyK⟩
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy.1]
      exact hy.2
    have hsep : ∀ x ∈ closure (connectedComponentIn ((upperHalf ∩ ball 0 r) \ (S ∪ (fun z => -conj z) '' S))
        ((y : ℂ) * I)), x.im = 0 → x = 0 := fun x hx hxim =>
      ld8_sep hr hSc hSp hS0 hSH hs₀ hs₀r
        ((isOpen_upperHalf.inter isOpen_ball).sdiff (ld8_isClosed_reflect_union hSc)).connectedComponentIn
        isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) (mem_connectedComponentIn hyV)
        hx hxim
    have hGC : ∀ z ∈ upperHalf, ‖g z * Complex.exp (-(1 - -(2 * I / (π : ℂ)) *
        Complex.log (((r : ℂ) + z) / ((r : ℂ) - z))) * (Real.log ε : ℂ))‖ ≤ Real.exp (-Real.log ε) := by
      intro z hz
      rw [ld8_halfDisc_aux_norm g r (Real.log ε) z]
      have hu := ld8_u_nonneg hr hz
      calc ‖g z‖ * Real.exp (-(1 - ld8_u r z) * Real.log ε) ≤ 1 * Real.exp (-Real.log ε) := by
            refine mul_le_mul (hg1 z hz) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le zero_le_one
            nlinarith [mul_nonneg hu (neg_nonneg.2 hL.le)]
        _ = Real.exp (-Real.log ε) := one_mul _
    have hGb : ∀ q ∈ upperHalf, q ∈ S ∪ (fun z => -conj z) '' S ∨ ‖q‖ = r →
        ‖g q * Complex.exp (-(1 - -(2 * I / (π : ℂ)) *
          Complex.log (((r : ℂ) + q) / ((r : ℂ) - q))) * (Real.log ε : ℂ))‖ ≤ 1 := by
      intro q hq hqK
      rw [ld8_halfDisc_aux_norm g r (Real.log ε) q]
      have hu := ld8_u_nonneg hr hq
      rcases hqK with hqK | hqr
      · calc ‖g q‖ * Real.exp (-(1 - ld8_u r q) * Real.log ε)
            ≤ ε * Real.exp (-(1 - ld8_u r q) * Real.log ε) :=
              mul_le_mul_of_nonneg_right (hgK q hq hqK) (Real.exp_pos _).le
          _ = Real.exp (Real.log ε) * Real.exp (-(1 - ld8_u r q) * Real.log ε) := by
              rw [Real.exp_log hε0]
          _ = Real.exp (ld8_u r q * Real.log ε) := by
              rw [← Real.exp_add]
              congr 1
              ring
          _ ≤ Real.exp 0 := Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos hu hL.le)
          _ = 1 := Real.exp_zero
      · rw [ld8_u_eq_one hr hq hqr, sub_self, neg_zero, zero_mul, Real.exp_zero, mul_one]
        exact hg1 q hq
    have hmax : ‖g ((y : ℂ) * I) * Complex.exp (-(1 - -(2 * I / (π : ℂ)) *
        Complex.log (((r : ℂ) + (y : ℂ) * I) / ((r : ℂ) - (y : ℂ) * I))) * (Real.log ε : ℂ))‖ ≤ 1 :=
      ld8_component_maxmod (ld8_isClosed_reflect_union hSc) hyV hsep
        (ld8_halfDisc_aux_differentiableOn hgd hr (Real.log ε)) hGC hGb
    rw [ld8_halfDisc_aux_norm g r (Real.log ε) ((y : ℂ) * I), hgy, neg_mul, Real.exp_neg, ← div_eq_mul_inv,
      div_le_one (Real.exp_pos _)] at hmax
    exact hmax

/-! ### Stage 4: radial limit, angular limit -/

/-- **RAD.**  If `F` is holomorphic on `upperHalf`, `‖F‖ ≤ 1` there, and `F → 0` along a curve `Γ` in `upperHalf`
tending to `0`, then `F (i y) → 0` as `y → 0⁺`: `ld8_halfDisc` with `ε = δ⁴`, the tail `S` of `Γ` from a parameter
`t₂` beyond which `‖F ∘ Γ‖ ≤ ε`, `r = ‖Γ t₂‖`, and `ld8_u r (i y) ≤ 1/2` for small `y` (`ld8_u_continuousAt_zero`). -/
theorem ld8_radial {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf)
    (hF1 : ∀ z ∈ upperHalf, ‖F z‖ ≤ 1) {Γ : ℝ → ℂ} (hΓc : ContinuousOn Γ (Ico 0 1))
    (hΓH : MapsTo Γ (Ico 0 1) upperHalf) (hΓ0 : Tendsto Γ (𝓝[<] 1) (𝓝 0))
    (hFΓ : Tendsto (F ∘ Γ) (𝓝[<] 1) (𝓝 0)) :
    ∀ δ > (0 : ℝ), ∃ y₀ > (0 : ℝ), ∀ y ∈ Ioo (0 : ℝ) y₀, ‖F ((y : ℂ) * I)‖ ≤ δ := by
  intro δ hδ
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · refine ⟨1, one_pos, fun y hy => (hF1 _ ?_).trans hδ1⟩
    show 0 < ((y : ℂ) * I).im
    simpa using hy.1
  have hε0 : 0 < δ ^ 4 := pow_pos hδ 4
  have hε1 : δ ^ 4 < 1 := pow_lt_one₀ hδ.le hδ1 (by norm_num)
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), ‖F (Γ t)‖ ≤ δ ^ 4 :=
    (Metric.tendsto_nhds.1 hFΓ _ hε0).mono fun t ht => by
      rw [dist_zero_right] at ht
      exact ht.le
  obtain ⟨l, hl1, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl1' : l < 1 := hl1
  obtain ⟨t₂, ht₂0, hlt₂, ht₂1⟩ : ∃ t₂ : ℝ, 0 ≤ t₂ ∧ l < t₂ ∧ t₂ < 1 :=
    ⟨max ((l + 1) / 2) 0, le_max_right _ _, lt_of_lt_of_le (by linarith) (le_max_left _ _),
      max_lt (by linarith) one_pos⟩
  obtain ⟨hSc, hSp⟩ := ld8_tail hΓc hΓ0 ht₂0 ht₂1
  have hs₀H : 0 < (Γ t₂).im := hΓH ⟨ht₂0, ht₂1⟩
  have hr : 0 < ‖Γ t₂‖ := hs₀H.trans_le (Complex.im_le_norm _)
  have hSH : ∀ z ∈ Γ '' Ico t₂ 1 ∪ {0}, z ≠ 0 → 0 < z.im := by
    intro z hz hz0
    rcases hz with ⟨t, ht, rfl⟩ | hz'
    · exact hΓH ⟨ht₂0.trans ht.1, ht.2⟩
    · exact absurd (mem_singleton_iff.1 hz') hz0
  have hSε : ∀ z ∈ Γ '' Ico t₂ 1 ∪ {0}, z ≠ 0 → ‖F z‖ ≤ δ ^ 4 := by
    intro z hz hz0
    rcases hz with ⟨t, ht, rfl⟩ | hz'
    · exact hlsub ⟨hlt₂.trans_le ht.1, ht.2⟩
    · exact absurd (mem_singleton_iff.1 hz') hz0
  obtain ⟨hucont, hu0⟩ := ld8_u_continuousAt_zero hr
  obtain ⟨y₁, hy₁, hy₁u⟩ := Metric.continuousAt_iff.1 hucont (1 / 2) (by norm_num)
  refine ⟨min ‖Γ t₂‖ y₁, lt_min hr hy₁, fun y hy => ?_⟩
  have hyr : y ∈ Ioo 0 ‖Γ t₂‖ := ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hsq := ld8_halfDisc hF hF1 hε0 hε1 hr hSc.isClosed hSp (mem_union_right _ (mem_singleton 0)) hSH
    (mem_union_left _ ⟨t₂, ⟨le_rfl, ht₂1⟩, rfl⟩) le_rfl hSε hyr
  have hdist : dist ((y : ℂ) * I) 0 < y₁ := by
    rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy.1]
    exact hy.2.trans_le (min_le_right _ _)
  have hu : ld8_u ‖Γ t₂‖ ((y : ℂ) * I) < 1 / 2 := by
    have h := hy₁u hdist
    rw [hu0, Real.dist_eq, sub_zero] at h
    exact (abs_lt.1 h).2
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hlog4 : Real.log (δ ^ 4) = 4 * Real.log δ := by
    rw [Real.log_pow]
    norm_num
  have hexp2 : Real.exp (2 * Real.log δ) = δ ^ 2 := by
    rw [show (2 : ℝ) * Real.log δ = Real.log (δ ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hδ 2)]
  have hexp : Real.exp ((1 - ld8_u ‖Γ t₂‖ ((y : ℂ) * I)) * Real.log (δ ^ 4)) ≤ δ ^ 2 := by
    rw [hlog4, ← hexp2]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - ld8_u ‖Γ t₂‖ ((y : ℂ) * I))
      (by linarith : (0 : ℝ) ≤ -Real.log δ)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 (hsq.trans hexp)

/-- **Angular limit (AL).**  Under the hypotheses of `lindelof`, for every `M > 1` and `η > 0` there is `ρ > 0` with
`‖f z - a‖ ≤ η` on `stolzAngle ζ M ∩ ball ζ ρ`: transfer by `κ`/`τ` (Stage 1c), normalize by
`C = max K 0 + ‖a‖ + 1`, then `ld8_radial` and `ld8_cone`. -/
theorem ld8_angular_limit {f : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f unitDisc) (hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Ico 0 1)) (hγ : MapsTo γ (Ico 0 1) unitDisc)
    (hγζ : Tendsto γ (𝓝[<] 1) (𝓝 ζ)) {a : ℂ} (hlim : Tendsto (f ∘ γ) (𝓝[<] 1) (𝓝 a))
    {M : ℝ} (hM : 1 < M) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ z ∈ stolzAngle ζ M ∩ ball ζ ρ, ‖f z - a‖ ≤ η := by
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  obtain ⟨K, hK⟩ := hbdd
  have hC : 0 < max K 0 + ‖a‖ + 1 := by positivity
  have hFd : DifferentiableOn ℂ (fun w => (f (-ζ * cayley w) - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ))
      upperHalf :=
    ((ld8_cayley_differentiableOn hζ1 hf).sub_const a).div_const _
  have hF1 : ∀ w ∈ upperHalf, ‖(f (-ζ * cayley w) - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ)‖ ≤ 1 := by
    intro w hw
    have h1 := hK _ (ld8_cayley_mem_unitDisc hζ1 hw)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, div_le_one hC]
    calc ‖f (-ζ * cayley w) - a‖ ≤ ‖f (-ζ * cayley w)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ max K 0 + ‖a‖ := by
          gcongr
          exact h1.trans (le_max_left _ _)
      _ ≤ max K 0 + ‖a‖ + 1 := by linarith
  have hΓc : ContinuousOn (fun t => cayleyInv (-(conj ζ) * γ t)) (Ico 0 1) :=
    (ld8_cayleyInv_continuousOn hζ1).comp hγc hγ
  have hΓH : MapsTo (fun t => cayleyInv (-(conj ζ) * γ t)) (Ico 0 1) upperHalf :=
    fun t ht => (ld8_cayley_leftInv hζ1 (hγ ht)).1
  have hΓ0 : Tendsto (fun t => cayleyInv (-(conj ζ) * γ t)) (𝓝[<] 1) (𝓝 0) :=
    (ld8_cayleyInv_tendsto hζ1).comp hγζ
  have hFΓ : Tendsto ((fun w => (f (-ζ * cayley w) - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ)) ∘
      (fun t => cayleyInv (-(conj ζ) * γ t))) (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun t => ((f ∘ γ) t - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ)) (𝓝[<] 1)
        (𝓝 ((a - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ))) :=
      (hlim.sub_const a).div_const _
    rw [sub_self, zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    simp only [Function.comp_apply]
    rw [(ld8_cayley_leftInv hζ1 (hγ ⟨ht.1.le, ht.2⟩)).2]
  obtain ⟨ρ₀, hρ₀, hcone⟩ := ld8_cone hFd hF1 (ld8_radial hFd hF1 hΓc hΓH hΓ0 hFΓ) hM (div_pos hη hC)
  refine ⟨min ρ₀ 1, lt_min hρ₀ one_pos, fun z hz => ?_⟩
  have hzζ : ‖z - ζ‖ < min ρ₀ 1 := by
    rw [← dist_eq_norm]
    exact hz.2
  obtain ⟨hc1, hc2⟩ := ld8_stolz_cayley hζ1 hz.1 (hzζ.le.trans (min_le_right _ _))
  have hw : ‖(f (-ζ * cayley (cayleyInv (-(conj ζ) * z))) - a) / ((max K 0 + ‖a‖ + 1 : ℝ) : ℂ)‖ ≤
      η / (max K 0 + ‖a‖ + 1) :=
    hcone _ hc1 (hc2.trans_lt (hzζ.trans_le (min_le_left _ _)))
  rw [(ld8_cayley_leftInv hζ1 hz.1.1).2, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC,
    div_le_div_iff_of_pos_right hC] at hw
  exact hw

/-- **Lindelöf's theorem.**  A bounded holomorphic `f` on `Δ` with limit `a` along a curve ending at
`ζ ∈ ∂Δ` has angular limit `a` at `ζ`.

Proof (s21r, 2026-09-27): Lindelöf's reflection argument (Lindelöf 1915).  This is the bounded case of the
Lehto–Virtanen theorem (Pommerenke §4.1); for conformal maps see Pommerenke §2.5, Thm 2.16 and Cor 2.17 (i).
The Cayley transfer `z ↦ cayleyInv (-(conj ζ) * z)` sends `Δ` to the upper half-plane and `ζ` to `0`
(`ld8_angular_limit`).  Radial limit (`ld8_radial`): the tail of the curve and its mirror image in the imaginary
axis cut the half disc (`ld8_sep`, a parity argument for a reflected polygon), and the half-disc majorant
`(2/π) arg ((r + z)/(r - z))` bounds `f` on the radius (`ld8_halfDisc`).  Angular limit (`ld8_cone`): the
quarter-disc majorant `(2/π) arg z - Im z / r` with Jordan's inequality (`ld8_quarter`) and a reflection.  Both
maximum principles are `norm_le_of_frontier_limsup_le_of_bounded` (one exceptional boundary point). -/
theorem lindelof {f : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f unitDisc) (hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Ico 0 1)) (hγ : MapsTo γ (Ico 0 1) unitDisc)
    (hγζ : Tendsto γ (𝓝[<] 1) (𝓝 ζ)) {a : ℂ} (hlim : Tendsto (f ∘ γ) (𝓝[<] 1) (𝓝 a)) :
    ∀ M : ℝ, 1 < M → angularClusterSet f ζ M = {a} := by
  intro M hM
  ext b
  simp only [angularClusterSet, mem_iInter, mem_Ioi, mem_singleton_iff]
  constructor
  · intro hb
    refine eq_of_forall_dist_le fun η hη => ?_
    obtain ⟨ρ, hρ, hρη⟩ := ld8_angular_limit hζ hf hbdd hγc hγ hγζ hlim hM hη
    have hsub : f '' (stolzAngle ζ M ∩ ball ζ ρ) ⊆ closedBall a η := by
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_closedBall, dist_eq_norm]
      exact hρη z hz
    exact mem_closedBall.1 (closure_minimal hsub isClosed_closedBall (hb ρ hρ))
  · rintro rfl r hr
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨ρ, hρ, hρη⟩ := ld8_angular_limit hζ hf hbdd hγc hγ hγζ hlim hM (half_pos hη)
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have hm : 0 < min (min r ρ) 1 := lt_min (lt_min hr hρ) one_pos
    obtain ⟨s, hs0, hsm⟩ : ∃ s : ℝ, 0 < s ∧ s < min (min r ρ) 1 := ⟨_, half_pos hm, half_lt_self hm⟩
    have hs1 : s < 1 := hsm.trans_le (min_le_right _ _)
    have hsr : s < r := hsm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hsρ : s < ρ := hsm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hzn : ‖((1 - s : ℝ) : ℂ) * ζ‖ = 1 - s := by
      rw [norm_mul, Complex.norm_real, hζ1, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hzζ : ‖((1 - s : ℝ) : ℂ) * ζ - ζ‖ = s := by
      rw [show ((1 - s : ℝ) : ℂ) * ζ - ζ = -((s : ℂ) * ζ) by push_cast; ring, norm_neg, norm_mul,
        Complex.norm_real, hζ1, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
    have hzS : ((1 - s : ℝ) : ℂ) * ζ ∈ stolzAngle ζ M := by
      refine ⟨?_, ?_⟩
      · rw [unitDisc, mem_ball_zero_iff, hzn]
        linarith
      · rw [hzζ, hzn, sub_sub_cancel]
        exact lt_mul_of_one_lt_left hs0 hM
    have hzb : ∀ t, s < t → ((1 - s : ℝ) : ℂ) * ζ ∈ ball ζ t := fun t ht => by
      rw [mem_ball, dist_eq_norm, hzζ]
      exact ht
    refine ⟨f (((1 - s : ℝ) : ℂ) * ζ), ⟨_, ⟨hzS, hzb r hsr⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    linarith [hρη _ ⟨hzS, hzb ρ hsρ⟩]

/-- **Carathéodory's prime-end theorem, cluster-set form.**  The prime end at `ζ` has impression
equal to the cluster set and principal points equal to the radial cluster set of `f` at `ζ`.

Proof (s21r PE2), with the same `P`. (⊆) The radius crosses the late crosscuts of any representing chain. (⊇) Wolff
radii in the windows `(s/2, s)` (the local area tends to `0`) and Koebe's distortion along the radius
(`koebe_quarter_of_not_mem`, `koebe_growth_scaled`) give a circular chain converging to a given radial cluster point
(Pommerenke Thm 2.16, (2.5.8)). -/
theorem caratheodory_primeEnd_principal {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧ ∀ ζ : Circle,
      (∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = P ζ →
        chainImpression Ω c.1 = clusterSet f unitDisc ζ) ∧
      {w | IsPrincipalPoint Ω (P ζ) w} = radialClusterSet f ζ := by
  exact pe5_primeEnd_principal_core hΩ hf

end LiZhongQC
