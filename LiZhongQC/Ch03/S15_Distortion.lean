import LiZhongQC.Ch03.S14_PoincareMetric
import LiZhongQC.Ch01.S07_GeometricDefinition
import LiZhongQC.Ch02.S13_Representation

/-!
# §15 几个偏差定理 — Distortion theorems

* §15.1 distortion of quasiconformal maps of the disc: (15.1), (15.2), Theorem 15.1 (15.3)
* Theorem 15.2 (Mori)                                     — `thm15_2_mori`
* Theorem 15.3 (Teichmüller: `δ(z, f(z)) ≤ ln K`) and its sharpness
* Lemmas 15.1, 15.2 and Theorem 15.4 (Teichmüller: distortion of circles) and its sharpness
* historical notes: the constant `16` in Mori's theorem is best possible; Wang Chuanfang's sharp
  estimate `|f(z)| ≤ 4^{1-1/K} |z|^{1/K}`

## What is proved here

(15.1), (15.2), Theorem 15.1 and its Hölder form, Theorem 15.2 (Mori), (15.22), Theorem 15.3, Lemmas 15.1 and
15.2, Theorem 15.4 and its sharpness.  Theorem 15.3 is proved by a holomorphic motion: `t ↦ f_t(z)`, `f_t` the
normalized solution for `(t/s) μ_f`, is holomorphic (Theorems 13.7, 13.8), lifts through the covering `φ` of
`ℂ ∖ {0, 1}` (§14.2), and Schwarz–Pick gives `δ(z, f(z)) ≤ ln K`; Lemma 15.1 by the book's maximum principle for
the Poincaré density; Theorem 15.4 from Theorem 15.3, Lemma 15.1 and a radial lower bound for `δ`; Lemma 15.2
and the sharpness of Theorem 15.4 from an explicit extremal map (affine stretch and reflection).  Still `sorry`:
the sharpness of Theorem 15.3 and the historical notes.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- `f` is a `K`-q.c. map of the unit disc into itself. -/
def IsKQCDiscInto (f : ℂ → ℂ) (K : ℝ) : Prop := IsKQC f unitDisc K ∧ f '' unitDisc ⊆ unitDisc

/-! ### S15-A interface (coordinator 553e2d) -/

/-- The Grötzsch function `μ` is continuous on `(0, 1)` (`μ = π a/b` with `a, b` continuous). -/
theorem s15_grotzschMu_continuousOn : ContinuousOn grotzschMu (Ioo 0 1) := by
  have hcont : ContinuousOn (fun r : ℝ => π * scSideA r / scSideB r) (Ioo 0 1) :=
    (continuousOn_const.mul continuousOn_scSideA).div continuousOn_scSideB
      (fun r hr => (scSide_pos hr.1 hr.2).2.ne')
  exact hcont.congr (fun r hr => gm_grotzschMu_eq hr.1 hr.2)

/-- The slit `[0, s]` of the Grötzsch domain is the image of `[0, s]` under `ℝ → ℂ`. -/
theorem s15_ring_slit_eq (s : ℝ) :
    {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s} = (fun t : ℝ => (t : ℂ)) '' Icc 0 s := by
  ext w
  simp only [mem_ofPred_eq, mem_image, mem_Icc]
  constructor
  · rintro ⟨him, h0, h1⟩
    exact ⟨w.re, ⟨h0, h1⟩, Complex.ext (by simp) (by simp [him])⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    simp [h0, h1]

/-- If `g` is continuous and injective on `D ⊇ Δ`, `g(Δ)` is open and `g(Δ) ⊆ Δ`, then for
`0 ≤ s < 1` the image `g(B_s)` of the Grötzsch domain separates the unit circle from
`{g(0), g(s)}`: `ℂ̄ ∖ g(B_s)` is the union of the disjoint closed sets `g([0, s])` (connected,
containing `g 0, g s`) and `ℂ̄ ∖ g(Δ)` (containing the circle). -/
theorem s15_ring_separates {g : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn g D) (hi : InjOn g D)
    (hΔD : unitDisc ⊆ D) (hΔo : IsOpen (g '' unitDisc)) (hΔ : g '' unitDisc ⊆ unitDisc)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    SeparatesSets (g '' grotzschDomain s) (toExt (sphere 0 1))
      {((g 0 : ℂ) : ExtPlane), ((g s : ℂ) : ExtPlane)} := by
  have hTeq := s15_ring_slit_eq s
  set T : Set ℂ := {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s} with hT
  set S : Set ExtPlane := (toExt (g '' grotzschDomain s))ᶜ with hS
  set P : Set ExtPlane := toExt (g '' T) with hP
  set Q : Set ExtPlane := (toExt (g '' unitDisc))ᶜ with hQ
  have hTc : IsCompact T := by
    rw [hTeq]
    exact isCompact_Icc.image continuous_ofReal
  have hTconn : IsPreconnected T := by
    rw [hTeq]
    exact isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have hTΔ : T ⊆ unitDisc := by
    rw [hTeq]
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.trans_lt hs1
  have hTD : T ⊆ D := hTΔ.trans hΔD
  have hBΔ : grotzschDomain s ⊆ unitDisc := fun w hw => hw.1
  have h0T : (0 : ℂ) ∈ T := ⟨by simp, by simp, by simpa using hs0⟩
  have hsT : ((s : ℝ) : ℂ) ∈ T := ⟨by simp, by simpa using hs0, by simp⟩
  have hPc : IsClosed P :=
    ((hTc.image_of_continuousOn (hc.mono hTD)).image OnePoint.continuous_coe).isClosed
  have hQc : IsClosed Q := isClosed_compl_toExt hΔo
  have hPΔ : P ⊆ toExt (g '' unitDisc) := image_mono (image_mono hTΔ)
  have hQS : Q ⊆ S := compl_subset_compl.2 (image_mono (image_mono hBΔ))
  have hPS : P ⊆ S := by
    rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ ⟨v, ⟨u', hu', rfl⟩, hv⟩
    have huu : u' = u := hi (hΔD hu'.1) (hTD hu) (OnePoint.coe_injective hv)
    subst huu
    exact hu'.2 hu
  have hSPQ : S ⊆ P ∪ Q := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (extInf_notMem_toExt _)
    | coe w =>
      by_cases hw : w ∈ g '' unitDisc
      · left
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨g u, ⟨u, ?_, rfl⟩, rfl⟩
        by_contra hnot
        exact hx ⟨g u, ⟨u, ⟨hu, hnot⟩, rfl⟩, rfl⟩
      · right
        exact fun h' => hw (coe_mem_toExt_iff.1 h')
  have hPQ : P ∩ Q = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxP hxQ
    exact hxQ (hPΔ hxP)
  have hsph : IsPreconnected (toExt (sphere (0 : ℂ) 1)) :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1).image _
      OnePoint.continuous_coe.continuousOn
  have h1sph : ((1 : ℂ) : ExtPlane) ∈ toExt (sphere (0 : ℂ) 1) := ⟨1, by simp, rfl⟩
  have hsphQ : toExt (sphere (0 : ℂ) 1) ⊆ Q := by
    rintro _ ⟨w, hw, rfl⟩ hw'
    have hwΔ := hΔ (coe_mem_toExt_iff.1 hw')
    exact absurd (mem_sphere_zero_iff_norm.1 hw) (ne_of_lt (mem_ball_zero_iff.1 hwΔ))
  have hsphS : toExt (sphere (0 : ℂ) 1) ⊆ S := hsphQ.trans hQS
  have hPconn : IsPreconnected P :=
    (hTconn.image g (hc.mono hTD)).image _ OnePoint.continuous_coe.continuousOn
  have h0P : ((g 0 : ℂ) : ExtPlane) ∈ P := ⟨g 0, ⟨0, h0T, rfl⟩, rfl⟩
  have hsP : ((g s : ℂ) : ExtPlane) ∈ P := ⟨g s, ⟨s, hsT, rfl⟩, rfl⟩
  have hPcomp : P ⊆ connectedComponentIn S ((g 0 : ℂ) : ExtPlane) :=
    hPconn.subset_connectedComponentIn h0P hPS
  refine ⟨((1 : ℂ) : ExtPlane), hsphS h1sph, ((g 0 : ℂ) : ExtPlane), hPS h0P,
    hsph.subset_connectedComponentIn h1sph hsphS,
    insert_subset_iff.2 ⟨hPcomp h0P, singleton_subset_iff.2 (hPcomp hsP)⟩, ?_⟩
  intro heq
  have hC := isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_connectedComponentIn (x := ((g 0 : ℂ) : ExtPlane)) (F := S)) P Q hPc hQc
    ((connectedComponentIn_subset _ _).trans hSPQ) (by rw [hPQ, inter_empty])
  have hmem1 : ((1 : ℂ) : ExtPlane) ∈ connectedComponentIn S ((g 0 : ℂ) : ExtPlane) :=
    heq ▸ mem_connectedComponentIn (hsphS h1sph)
  have hmem0 : ((g 0 : ℂ) : ExtPlane) ∈ connectedComponentIn S ((g 0 : ℂ) : ExtPlane) :=
    mem_connectedComponentIn (hPS h0P)
  rcases hC with hC | hC
  · exact hsphQ h1sph (hPΔ (hC hmem1))
  · exact hC hmem0 (hPΔ h0P)

/-- (15.1) at scale `ρ`: for `|z| < ρ < 1`, `μ(|z|/ρ) ≤ K μ(|f(z)|)` — Theorem 7.4 applied to the
Grötzsch ring `B_{|z|/ρ}` pushed by `w ↦ (ρ z/|z|) w`, then Theorem 5.1 after a rotation. -/
theorem s15_eq15_1_rho {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCDiscInto f K) (hf0 : f 0 = 0) {z : ℂ}
    (hz0 : z ≠ 0) {ρ : ℝ} (hzρ : ‖z‖ < ρ) (hρ1 : ρ < 1) :
    grotzschMu (‖z‖ / ρ) ≤ K * grotzschMu ‖f z‖ := by
  obtain ⟨hfK, hfΔ⟩ := hf
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hρ0 : 0 < ρ := hzn.trans hzρ
  have hz1 : ‖z‖ < 1 := hzρ.trans hρ1
  have hzΔ : z ∈ unitDisc := mem_ball_zero_iff.2 hz1
  have h0Δ : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfinj : InjOn f unitDisc := hfK.2.2.1.2.1
  have hfz0 : f z ≠ 0 := fun h => hz0 (hfinj hzΔ h0Δ (h.trans hf0.symm))
  have hfzΔ : f z ∈ unitDisc := hfΔ (mem_image_of_mem f hzΔ)
  set r : ℝ := ‖f z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hfz0
  have hr1 : r < 1 := mem_ball_zero_iff.1 hfzΔ
  set s : ℝ := ‖z‖ / ρ with hs
  have hs0 : 0 < s := div_pos hzn hρ0
  have hs1 : s < 1 := (div_lt_one hρ0).2 hzρ
  -- the similarity `w ↦ c w` (`|c| = ρ`, `c s = z`) and the rotation `w ↦ d w` (`d f(z) = |f(z)|`)
  set c : ℂ := (ρ : ℂ) * z / (‖z‖ : ℂ) with hc
  have hc0 : c ≠ 0 :=
    div_ne_zero (mul_ne_zero (ofReal_ne_zero.2 hρ0.ne') hz0) (ofReal_ne_zero.2 hzn.ne')
  have hcn : ‖c‖ = ρ := by
    rw [hc, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hρ0, abs_of_pos hzn, mul_div_assoc, div_self hzn.ne', mul_one]
  have hcs : c * ((s : ℝ) : ℂ) = z := by
    have hρC : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.2 hρ0.ne'
    have hzC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hzn.ne'
    rw [hc, hs]
    push_cast
    field_simp
  set d : ℂ := conj (f z) / (r : ℂ) with hd
  have hd0 : d ≠ 0 := div_ne_zero ((map_ne_zero _).2 hfz0) (ofReal_ne_zero.2 hr0.ne')
  have hdn : ‖d‖ = 1 := by
    rw [hd, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hr0.ne']
  have hdf : d * f z = (r : ℂ) := by
    rw [hd, div_mul_eq_mul_div, Complex.conj_mul', hr]
    have hne : ((‖f z‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hr0.ne'
    field_simp
  -- the `K`-q.c. map `g = R ∘ f ∘ L` on `D = {|w| < 1/ρ}`
  set D : Set ℂ := ball (0 : ℂ) (1 / ρ) with hD
  have h1ρ : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0, one_mul]; exact hρ1
  have hΔD : unitDisc ⊆ D := ball_subset_ball h1ρ.le
  have hL : IsKQC (fun w => c * w) D 1 :=
    isKQC_one_of_conformal isOpen_ball ⟨(differentiable_id.const_mul c).differentiableOn,
      fun a _ b _ h => mul_left_cancel₀ hc0 h, rfl⟩
  have hLΔ : (fun w => c * w) '' D ⊆ unitDisc := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ‖w‖ < 1 / ρ := mem_ball_zero_iff.1 hw
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hcn]
    calc ρ * ‖w‖ < ρ * (1 / ρ) := mul_lt_mul_of_pos_left hw' hρ0
      _ = 1 := by field_simp
  have hR : IsKQC (fun w => d * w) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨(differentiable_id.const_mul d).differentiableOn,
      fun a _ b _ h => mul_left_cancel₀ hd0 h, rfl⟩
  set g : ℂ → ℂ := (fun w => d * w) ∘ (f ∘ fun w => c * w) with hg
  have hgK : IsKQC g D K := by
    have h1 := thm7_1_comp (thm7_1_comp hL hfK hLΔ) hR (subset_univ _)
    rwa [one_mul, mul_one] at h1
  have hgD : g '' D ⊆ unitDisc := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 : f (c * w) ∈ unitDisc := hfΔ (mem_image_of_mem f (hLΔ (mem_image_of_mem _ hw)))
    show d * f (c * w) ∈ unitDisc
    rw [unitDisc, mem_ball_zero_iff] at h1 ⊢
    rw [norm_mul, hdn, one_mul]
    exact h1
  have hg0 : g 0 = 0 := by
    show d * f (c * 0) = 0
    rw [mul_zero, hf0, mul_zero]
  have hgs : g ((s : ℝ) : ℂ) = (r : ℂ) := by
    show d * f (c * ((s : ℝ) : ℂ)) = (r : ℂ)
    rw [hcs, hdf]
  -- Theorem 7.4 on the Grötzsch domain `B_s`, then Theorem 5.1
  have hB := grotzschDomain_doublyConnected hs0 hs1
  have hBD : closure (toExt (grotzschDomain s)) ⊆ toExt D :=
    (nf_e_closure_toExt_subset (isCompact_closedBall (0 : ℂ) 1)
      fun w hw => mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 hw.1).le).trans
      (image_mono (closedBall_subset_ball h1ρ))
  obtain ⟨hB', hBB', -⟩ := thm7_4_dcModulus_quasi_invariance hgK hB.1 hBD
  have hgΔ : g '' unitDisc ⊆ unitDisc := (image_mono hΔD).trans hgD
  have hBsub : g '' grotzschDomain s ⊆ unitDisc :=
    (image_mono fun w (hw : w ∈ grotzschDomain s) => hw.1).trans hgΔ
  have hsep : SeparatesSets (g '' grotzschDomain s) (toExt (sphere 0 1))
      {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)} := by
    have h1 := s15_ring_separates hgK.2.2.1.1 hgK.2.2.1.2.1 hΔD
      (aqc_isOpen_image_of_isHomeomorphOnto hgK.2.2.1 (isOpen_image_of_isKQC hgK) hΔD
        isOpen_ball) hgΔ hs0.le hs1
    rwa [hg0, hgs] at h1
  have hgr := thm5_1_grotzsch hr0 hr1 hB' hBsub hsep
  have hK0 : 0 ≤ K := zero_le_one.trans hfK.2.1
  have hmur : 0 ≤ grotzschMu r := ENNReal.toReal_nonneg
  have hμs : dcModulus (grotzschDomain s) = ENNReal.ofReal (grotzschMu s) :=
    (ENNReal.ofReal_toReal hB.2.ne).symm
  have hμr : dcModulus (grotzschDomain r) = ENNReal.ofReal (grotzschMu r) :=
    (ENNReal.ofReal_toReal (grotzschDomain_doublyConnected hr0 hr1).2.ne).symm
  have key : ENNReal.ofReal (grotzschMu s) ≤ ENNReal.ofReal (K * grotzschMu r) := by
    rw [ENNReal.ofReal_mul hK0, ← hμs, ← hμr]
    calc dcModulus (grotzschDomain s) ≤ ENNReal.ofReal K * dcModulus (g '' grotzschDomain s) :=
          hBB'
      _ ≤ ENNReal.ofReal K * dcModulus (grotzschDomain r) := by gcongr
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hmur)).1 key

/-- The radial stretch with a real power: `z |z|^{1/K-1} = z · ((|z|^{1/K-1} : ℝ) : ℂ)`. -/
theorem s15_rh_eq_real (K : ℝ) (z : ℂ) :
    z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1) = z * ((‖z‖ ^ (1 / K - 1) : ℝ) : ℂ) := by
  have hcast : ((1 / K : ℂ) - 1) = (((1 / K - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, Complex.ofReal_cpow (norm_nonneg z)]

/-- `‖z |z|^{1/K-1}‖ = |z|^{1/K}` for every `z` (`K ≥ 1`). -/
theorem s15_rh_norm {K : ℝ} (hK : 1 ≤ K) (z : ℂ) :
    ‖z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)‖ = ‖z‖ ^ (1 / K) := by
  have hK0 : 0 < K := by linarith
  have hKinv : (1 / K : ℝ) ≠ 0 := (one_div_pos.2 hK0).ne'
  rw [s15_rh_eq_real K z]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [zero_mul, norm_zero, Real.zero_rpow hKinv]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    calc ‖z‖ * ‖z‖ ^ (1 / K - 1) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (1 / K - 1) := by rw [Real.rpow_one]
      _ = ‖z‖ ^ ((1 : ℝ) + (1 / K - 1)) := (Real.rpow_add hpos _ _).symm
      _ = ‖z‖ ^ (1 / K) := by congr 1; ring

/-- The radial stretch `z ↦ z |z|^{1/K-1}` is continuous on `ℂ` (`K ≥ 1`). -/
theorem s15_rh_continuous {K : ℝ} (hK : 1 ≤ K) :
    Continuous (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) := by
  have hK0 : 0 < K := by linarith
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : (0 : ℂ) * (‖(0 : ℂ)‖ : ℂ) ^ ((1 / K : ℂ) - 1) = 0 := zero_mul _
    show Tendsto (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) (𝓝 0)
      (𝓝 ((0 : ℂ) * (‖(0 : ℂ)‖ : ℂ) ^ ((1 / K : ℂ) - 1)))
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [s15_rh_norm hK]
    have hc : Continuous (fun z : ℂ => ‖z‖ ^ (1 / K)) :=
      continuous_norm.rpow_const (fun _ => Or.inr (one_div_pos.2 hK0).le)
    have := hc.tendsto 0
    rwa [norm_zero, Real.zero_rpow (one_div_pos.2 hK0).ne'] at this
  · have hslit : ((‖z‖ : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz)
    have hc : ContinuousAt (fun x : ℂ => ((‖x‖ : ℝ) : ℂ)) z :=
      (Complex.continuous_ofReal.comp continuous_norm).continuousAt
    exact continuousAt_id.mul (hc.cpow continuousAt_const hslit)

/-- The inverse radial stretch `w ↦ |w|^{K-1} w` is continuous on `ℂ` (`K ≥ 1`). -/
theorem s15_rh_inv_continuous {K : ℝ} (hK : 1 ≤ K) :
    Continuous (fun w : ℂ => ((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w) :=
  (Complex.continuous_ofReal.comp
    (continuous_norm.rpow_const (fun _ => Or.inr (by linarith)))).mul continuous_id

/-- `w ↦ |w|^{K-1} w` is a left inverse of the radial stretch `z ↦ z |z|^{1/K-1}`. -/
theorem s15_rh_left_inv {K : ℝ} (hK : 1 ≤ K) (z : ℂ) :
    ((‖z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)‖ ^ (K - 1) : ℝ) : ℂ) *
      (z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) = z := by
  have hK0 : 0 < K := by linarith
  rw [s15_rh_norm hK z, s15_rh_eq_real K z]
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have key : (‖z‖ ^ (1 / K)) ^ (K - 1) * ‖z‖ ^ (1 / K - 1) = 1 := by
      rw [← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
      have : 1 / K * (K - 1) + (1 / K - 1) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    calc (((‖z‖ ^ (1 / K)) ^ (K - 1) : ℝ) : ℂ) * (z * ((‖z‖ ^ (1 / K - 1) : ℝ) : ℂ))
        = z * ((((‖z‖ ^ (1 / K)) ^ (K - 1) * ‖z‖ ^ (1 / K - 1) : ℝ)) : ℂ) := by
          rw [Complex.ofReal_mul]; ring
      _ = z := by rw [key, Complex.ofReal_one, mul_one]

/-- `w ↦ |w|^{K-1} w` is a right inverse of the radial stretch `z ↦ z |z|^{1/K-1}`. -/
theorem s15_rh_right_inv {K : ℝ} (hK : 1 ≤ K) (w : ℂ) :
    (((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w) *
      (‖((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w‖ : ℂ) ^ ((1 / K : ℂ) - 1) = w := by
  have hK0 : 0 < K := by linarith
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hnorm : ‖((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w‖ = ‖w‖ ^ K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
      calc ‖w‖ ^ (K - 1) * ‖w‖ = ‖w‖ ^ (K - 1) * ‖w‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖w‖ ^ (K - 1 + 1) := (Real.rpow_add hpos _ _).symm
        _ = ‖w‖ ^ K := by congr 1; ring
    rw [s15_rh_eq_real K, hnorm]
    have key : ‖w‖ ^ (K - 1) * (‖w‖ ^ K) ^ (1 / K - 1) = 1 := by
      rw [← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
      have : K - 1 + K * (1 / K - 1) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    calc ((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w * (((‖w‖ ^ K) ^ (1 / K - 1) : ℝ) : ℂ)
        = w * (((‖w‖ ^ (K - 1) * (‖w‖ ^ K) ^ (1 / K - 1)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul]; ring
      _ = w := by rw [key, Complex.ofReal_one, mul_one]

/-- The radial stretch `z ↦ z|z|^{1/K-1}` is a homeomorphism of `Δ` onto itself. -/
theorem s15_radial_homeo {K : ℝ} (hK : 1 ≤ K) :
    IsHomeomorphOnto (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) unitDisc unitDisc := by
  have hK0 : 0 < K := by linarith
  set F : ℂ → ℂ := fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1) with hF
  set G : ℂ → ℂ := fun w : ℂ => ((‖w‖ ^ (K - 1) : ℝ) : ℂ) * w with hG
  have hGF : ∀ z, G (F z) = z := fun z => s15_rh_left_inv hK z
  have hFG : ∀ w, F (G w) = w := fun w => s15_rh_right_inv hK w
  have hFmaps : ∀ z ∈ unitDisc, F z ∈ unitDisc := by
    intro z hz
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    show F z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hF, s15_rh_norm hK]
    exact Real.rpow_lt_one (norm_nonneg z) hz' (one_div_pos.2 hK0)
  have hGmaps : ∀ w ∈ unitDisc, G w ∈ unitDisc := by
    intro w hw
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    show G w ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hG]
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
      have h1 : ‖w‖ ^ (K - 1) ≤ 1 :=
        Real.rpow_le_one (norm_nonneg w) hw'.le (by linarith)
      calc ‖w‖ ^ (K - 1) * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hw'
  have hinj : InjOn F unitDisc := fun a _ b _ hab => by rw [← hGF a, hab, hGF b]
  have himg : F '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hFmaps z hz
    · intro hw
      exact ⟨G w, hGmaps w hw, hFG w⟩
  have hinv : EqOn (Function.invFunOn F unitDisc) G unitDisc := by
    intro w hw
    have hex : ∃ z ∈ unitDisc, F z = w := ⟨G w, hGmaps w hw, hFG w⟩
    have h := Function.invFunOn_eq hex
    calc Function.invFunOn F unitDisc w = G (F (Function.invFunOn F unitDisc w)) := (hGF _).symm
      _ = G w := by rw [h]
  exact ⟨(s15_rh_continuous hK).continuousOn, hinj, himg,
    (s15_rh_inv_continuous hK).continuousOn.congr hinv⟩

/-- `|z|z|^{1/K-1}| = |z|^{1/K}` for every `z`. -/
theorem s15_radial_norm {K : ℝ} (hK : 1 ≤ K) (z : ℂ) :
    ‖z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)‖ = ‖z‖ ^ (1 / K) := by
  exact s15_rh_norm hK z

/-- The radial stretch written with a real power: `z |z|^{1/K-1} = |z|^{1/K-1} • z`. -/
theorem s15_ra_eq (K : ℝ) :
    (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) = fun w : ℂ => (‖w‖ ^ (1 / K - 1)) • w := by
  funext w
  have h1 : ((1 / K : ℂ) - 1) = ((1 / K - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cpow (norm_nonneg w), Complex.real_smul, mul_comm]

/-- `w ↦ |w|^p w` is `C^n` off `0`. -/
theorem s15_ra_contDiffAt {z : ℂ} (hz : z ≠ 0) (p : ℝ) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun w : ℂ => ‖w‖ ^ p • w) z :=
  ((contDiffAt_norm ℝ hz).rpow_const_of_ne (norm_ne_zero_iff.2 hz)).smul contDiffAt_id

/-- `w ↦ |w|^p w` is continuous on `ℂ` when `p + 1 > 0` (at `0`: `|w|^p |w| = |w|^{p+1} → 0`). -/
theorem s15_ra_continuous {p : ℝ} (hp : 0 < p + 1) :
    Continuous (fun w : ℂ => ‖w‖ ^ p • w) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, smul_zero]
    have hlim : Tendsto (fun w : ℂ => ‖w‖ ^ (p + 1)) (𝓝 0) (𝓝 0) := by
      have h := (continuous_norm.continuousAt (x := (0 : ℂ))).rpow_const (p := p + 1)
        (Or.inr hp.le)
      simpa [ContinuousAt, Real.zero_rpow hp.ne'] using h
    refine squeeze_zero_norm (fun w => le_of_eq ?_) hlim
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _),
      Real.rpow_add_one' (norm_nonneg w) hp.ne']
  · exact (s15_ra_contDiffAt hz p (n := 0)).continuousAt

/-- Along a vertical line `Re w = x ≠ 0` the map `w ↦ |w|^p w` is `C¹`. -/
theorem s15_ra_contDiff_vert {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
    ContDiff ℝ 1 (fun y : ℝ => (fun w : ℂ => ‖w‖ ^ p • w) ((x : ℂ) + (y : ℂ) * I)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    apply hx
    simpa using congrArg Complex.re h
  have hline : ContDiffAt ℝ 1 (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) y :=
    contDiffAt_const.add (ofRealCLM.contDiff.contDiffAt.mul contDiffAt_const)
  exact (s15_ra_contDiffAt hne p).comp y hline

/-- Along a horizontal line `Im w = y ≠ 0` the map `w ↦ |w|^p w` is `C¹`. -/
theorem s15_ra_contDiff_horiz {y : ℝ} (hy : y ≠ 0) (p : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => (fun w : ℂ => ‖w‖ ^ p • w) ((x : ℂ) + (y : ℂ) * I)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    apply hy
    simpa using congrArg Complex.im h
  have hline : ContDiffAt ℝ 1 (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) x :=
    ofRealCLM.contDiff.contDiffAt.add contDiffAt_const
  exact (s15_ra_contDiffAt hne p).comp x hline

/-- The radial stretch is A.C.L. in `Δ` (it is smooth off `0`). -/
theorem s15_radial_isACL {K : ℝ} (hK : 1 ≤ K) :
    IsACL (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) unitDisc := by
  have hK0 : 0 < K := by linarith
  have hp : 0 < 1 / K - 1 + 1 := by
    have : 0 < 1 / K := by positivity
    linarith
  rw [s15_ra_eq K]
  refine ⟨(s15_ra_continuous hp).continuousOn, fun a b c d _ _ _ => ⟨?_, ?_⟩⟩
  · have h0 : ∀ᵐ x ∂(volume.restrict (Ioo a b)), x ≠ (0 : ℝ) :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ)))
    filter_upwards [h0] with x hx
    exact (s15_ra_contDiff_vert hx _).contDiffOn.absolutelyContinuousOnInterval
  · have h0 : ∀ᵐ y ∂(volume.restrict (Ioo c d)), y ≠ (0 : ℝ) :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ)))
    filter_upwards [h0] with y hy
    exact (s15_ra_contDiff_horiz hy _).contDiffOn.absolutelyContinuousOnInterval

/-- Derivative of `w ↦ |w|^p` off `0`. -/
theorem s15_ra_hasFDerivAt_norm_rpow {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    HasFDerivAt (fun w : ℂ => ‖w‖ ^ p) ((p * ‖z‖ ^ (p - 2)) • innerSL ℝ z) z := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq z).rpow_const (p := p / 2) (by simp [hz]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- Derivative of `w ↦ |w|^p w` off `0`. -/
theorem s15_ra_hasFDerivAt {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    HasFDerivAt (fun w : ℂ => ‖w‖ ^ p • w)
      ((‖z‖ ^ p) • ContinuousLinearMap.id ℝ ℂ +
        ((p * ‖z‖ ^ (p - 2)) • innerSL ℝ z).smulRight z) z :=
  (s15_ra_hasFDerivAt_norm_rpow hz p).smul (hasFDerivAt_id z)

/-- `∂_x` of `w ↦ |w|^p w` at `z ≠ 0`. -/
theorem s15_ra_fderiv_one {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    fderiv ℝ (fun w : ℂ => ‖w‖ ^ p • w) z 1 =
      ((‖z‖ ^ p : ℝ) : ℂ) + ((p * ‖z‖ ^ (p - 2) * z.re : ℝ) : ℂ) * z := by
  rw [(s15_ra_hasFDerivAt hz p).fderiv]
  simp [Complex.inner, Complex.real_smul]

/-- `∂_y` of `w ↦ |w|^p w` at `z ≠ 0`. -/
theorem s15_ra_fderiv_I {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    fderiv ℝ (fun w : ℂ => ‖w‖ ^ p • w) z I =
      ((‖z‖ ^ p : ℝ) : ℂ) * I + ((p * ‖z‖ ^ (p - 2) * z.im : ℝ) : ℂ) * z := by
  rw [(s15_ra_hasFDerivAt hz p).fderiv]
  simp [Complex.inner, Complex.real_smul]

/-- `‖z‖^{p-2} ‖z‖² = ‖z‖^p` written with real and imaginary parts (`z ≠ 0`). -/
theorem s15_ra_key {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    ‖z‖ ^ (p - 2) * (z.re * z.re + z.im * z.im) = ‖z‖ ^ p := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : z.re * z.re + z.im * z.im = ‖z‖ ^ (2 : ℝ) := by
    rw [Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]
  rw [h2, ← Real.rpow_add hpos]
  ring_nf

/-- `∂_z` of `w ↦ |w|^p w` at `z ≠ 0`: `(p + 2)/2 · |z|^p`. -/
theorem s15_ra_dz {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    dz (fun w : ℂ => ‖w‖ ^ p • w) z = (((p + 2) / 2 * ‖z‖ ^ p : ℝ) : ℂ) := by
  have hk := s15_ra_key hz p
  unfold dz
  rw [s15_ra_fderiv_one hz p, s15_ra_fderiv_I hz p]
  apply Complex.ext
  · simp
    linear_combination (p / 2) * hk
  · simp
    ring

/-- `∂_{z̄}` of `w ↦ |w|^p w` at `z ≠ 0`: `p/2 · |z|^{p-2} z²`. -/
theorem s15_ra_dzbar {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    dzbar (fun w : ℂ => ‖w‖ ^ p • w) z = ((p / 2 * ‖z‖ ^ (p - 2) : ℝ) : ℂ) * z ^ 2 := by
  unfold dzbar
  rw [s15_ra_fderiv_one hz p, s15_ra_fderiv_I hz p]
  apply Complex.ext
  · simp [sq]
    ring
  · simp [sq]
    ring

/-- Off `0` the radial stretch satisfies `|f_z| + |f_z̄| ≤ K (|f_z| - |f_z̄|)` (with equality:
`|f_z| = (1 + 1/K)|z|^{1/K-1}/2`, `|f_z̄| = (1 - 1/K)|z|^{1/K-1}/2`). -/
theorem s15_radial_dilatation {K : ℝ} (hK : 1 ≤ K) {z : ℂ} (hz : z ≠ 0) :
    ‖dz (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) z‖ +
        ‖dzbar (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) z‖ ≤
      K * (‖dz (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) z‖ -
        ‖dzbar (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) z‖) := by
  have hK0 : 0 < K := by linarith
  have hα0 : 0 < 1 / K := by positivity
  have hα1 : 1 / K ≤ 1 := by rw [div_le_one hK0]; exact hK
  have hA : 0 < ‖z‖ ^ (1 / K - 1) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz) _
  have hB : 0 ≤ ‖z‖ ^ (1 / K - 1 - 2) := Real.rpow_nonneg (norm_nonneg z) _
  have hk := s15_ra_key hz (1 / K - 1)
  have hsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hn1 : ‖dz (fun w : ℂ => ‖w‖ ^ (1 / K - 1) • w) z‖ =
      (1 / K - 1 + 2) / 2 * ‖z‖ ^ (1 / K - 1) := by
    rw [s15_ra_dz hz]
    exact Complex.norm_of_nonneg (by nlinarith)
  have hn2 : ‖dzbar (fun w : ℂ => ‖w‖ ^ (1 / K - 1) • w) z‖ =
      (1 - 1 / K) / 2 * ‖z‖ ^ (1 / K - 1) := by
    rw [s15_ra_dzbar hz, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith), hsq, ← hk]
    ring
  have hKα : K * (1 / K) = 1 := by field_simp
  rw [s15_ra_eq K, hn1, hn2]
  nlinarith

/-- (15.1): for a `K`-q.c. map `f` of `Δ` into `Δ` with `f(0) = 0`, `μ(|z|) ≤ K μ(|f(z)|)`. -/
theorem eq15_1 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCDiscInto f K) (hf0 : f 0 = 0) {z : ℂ}
    (hz : z ∈ unitDisc) (hz0 : z ≠ 0) : grotzschMu ‖z‖ ≤ K * grotzschMu ‖f z‖ := by
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hr1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hlim : Tendsto (fun ρ : ℝ => ‖z‖ / ρ) (𝓝[<] 1) (𝓝 ‖z‖) := by
    have h : Tendsto (fun ρ : ℝ => ‖z‖ / ρ) (𝓝 1) (𝓝 (‖z‖ / 1)) :=
      tendsto_const_nhds.div tendsto_id one_ne_zero
    rw [div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hcontAt : ContinuousAt grotzschMu ‖z‖ :=
    s15_grotzschMu_continuousOn.continuousAt (Ioo_mem_nhds hr0 hr1)
  have hlim2 : Tendsto (fun ρ : ℝ => grotzschMu (‖z‖ / ρ)) (𝓝[<] 1) (𝓝 (grotzschMu ‖z‖)) :=
    hcontAt.tendsto.comp hlim
  have hev : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), grotzschMu (‖z‖ / ρ) ≤ K * grotzschMu ‖f z‖ := by
    filter_upwards [Ioo_mem_nhdsLT hr1] with ρ hρ
    exact s15_eq15_1_rho hf hf0 hz0 hρ.1 hρ.2
  exact le_of_tendsto hlim2 hev

/-- (15.2): `|f(z)| ≤ 4^{1-1/K} |z|^{1/K} / (1 - |z|²)^{1/(2K)}`. -/
theorem eq15_2 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCDiscInto f K) (hf0 : f 0 = 0) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖f z‖ ≤ (4 : ℝ) ^ (1 - 1 / K) * ‖z‖ ^ (1 / K) / (1 - ‖z‖ ^ 2) ^ (1 / (2 * K)) := by
  have hK1 : 1 ≤ K := hf.1.2.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hr1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h1r2 : 0 < 1 - ‖z‖ ^ 2 := by
    have := norm_nonneg z
    nlinarith
  rcases eq_or_ne z 0 with rfl | hz0
  · calc ‖f 0‖ = 0 := by rw [hf0, norm_zero]
      _ ≤ _ := div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (norm_nonneg _) _)) (Real.rpow_nonneg h1r2.le _)
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hfz : f z ∈ unitDisc := hf.2 (mem_image_of_mem f hz)
  have ht1 : ‖f z‖ < 1 := mem_ball_zero_iff.1 hfz
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfz0 : f z ≠ 0 := by
    intro h
    exact hz0 (hf.1.2.2.1.2.1 hz h0D (h.trans hf0.symm))
  have ht0 : 0 < ‖f z‖ := norm_pos_iff.2 hfz0
  set r := ‖z‖ with hr_def
  set t := ‖f z‖ with ht_def
  -- the chain `log(4√(1-r²)/r) ≤ μ(r) ≤ K μ(t) ≤ K log(4/t)`
  have hchain : Real.log (4 * Real.sqrt (1 - r ^ 2) / r) ≤ K * Real.log (4 / t) :=
    (em_lower hr0 hr1).trans ((eq15_1 hf hf0 hz hz0).trans
      (mul_le_mul_of_nonneg_left (em_upper ht0 ht1) hK0.le))
  have hsq : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 h1r2
  have hlogL : Real.log (4 * Real.sqrt (1 - r ^ 2) / r) =
      Real.log 4 + Real.log (1 - r ^ 2) / 2 - Real.log r := by
    rw [Real.log_div (mul_pos (by norm_num) hsq).ne' hr0.ne',
      Real.log_mul (by norm_num) hsq.ne', Real.log_sqrt h1r2.le]
  have hlogT : Real.log (4 / t) = Real.log 4 - Real.log t :=
    Real.log_div (by norm_num) ht0.ne'
  rw [hlogL, hlogT] at hchain
  have h4pos : 0 < (4 : ℝ) ^ (1 - 1 / K) := Real.rpow_pos_of_pos (by norm_num) _
  have hrpos : 0 < r ^ (1 / K) := Real.rpow_pos_of_pos hr0 _
  have hdpos : 0 < (1 - r ^ 2) ^ (1 / (2 * K)) := Real.rpow_pos_of_pos h1r2 _
  have hRpos : 0 < (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) / (1 - r ^ 2) ^ (1 / (2 * K)) :=
    div_pos (mul_pos h4pos hrpos) hdpos
  have hlogR : Real.log ((4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) / (1 - r ^ 2) ^ (1 / (2 * K))) =
      ((K - 1) * Real.log 4 + Real.log r - Real.log (1 - r ^ 2) / 2) / K := by
    rw [Real.log_div (mul_pos h4pos hrpos).ne' hdpos.ne', Real.log_mul h4pos.ne' hrpos.ne',
      Real.log_rpow (by norm_num), Real.log_rpow hr0, Real.log_rpow h1r2]
    field_simp
  rw [← Real.log_le_log_iff ht0 hRpos, hlogR, le_div_iff₀ hK0]
  linarith

/-- §15.1: the exponent `1/K` in (15.2) cannot be improved: `z ↦ z|z|^{1/K - 1}` is a `K`-q.c.
self-map of `Δ` fixing `0` with `|f(z)| = |z|^{1/K}`. -/
theorem radial_stretch_isKQC {K : ℝ} (hK : 1 ≤ K) :
    IsKQC (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) unitDisc K ∧
      (fun z : ℂ => z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)) '' unitDisc = unitDisc ∧
      ∀ z : ℂ, ‖z * (‖z‖ : ℂ) ^ ((1 / K : ℂ) - 1)‖ = ‖z‖ ^ (1 / K) := by
  have hH := s15_radial_homeo hK
  have hball : IsOpen unitDisc := isOpen_ball
  refine ⟨(thm10_1_isKQC_iff hball hK hH).2 ⟨s15_radial_isACL hK, ?_⟩, hH.2.2.1, s15_radial_norm hK⟩
  have h0 : ∀ᵐ z ∂(volume.restrict unitDisc), z ≠ (0 : ℂ) :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℂ)))
  filter_upwards [h0] with z hz
  exact s15_radial_dilatation hK hz

/-- **Theorem 15.1** (15.3): for a `K`-q.c. self-map `f` of `Δ` and `z₁, z₂ ∈ Δ`,
`|(f(z₁) - f(z₂))/(1 - conj(f(z₂)) f(z₁))| ≤ 4^{1-1/K} ρ^{1/K} / (1 - ρ²)^{1/(2K)}`,
`ρ = |(z₁ - z₂)/(1 - z̄₂ z₁)|`. -/
theorem thm15_1 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K) (himg : f '' unitDisc = unitDisc)
    {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    ‖(f z₁ - f z₂) / (1 - conj (f z₂) * f z₁)‖ ≤
      (4 : ℝ) ^ (1 - 1 / K) * ‖(z₁ - z₂) / (1 - conj z₂ * z₁)‖ ^ (1 / K) /
        (1 - ‖(z₁ - z₂) / (1 - conj z₂ * z₁)‖ ^ 2) ^ (1 / (2 * K)) := by
  have h₁n : ‖z₁‖ < 1 := mem_ball_zero_iff.mp h₁
  have h₂n : ‖z₂‖ < 1 := mem_ball_zero_iff.mp h₂
  have hfz₂ : f z₂ ∈ unitDisc := himg ▸ mem_image_of_mem f h₂
  have hfz₂n : ‖f z₂‖ < 1 := mem_ball_zero_iff.mp hfz₂
  have hneg : ‖-z₂‖ < 1 := by rwa [norm_neg]
  have hcB1 := isConformalOnto_blaschke hneg
  have hcB2 := isConformalOnto_blaschke hfz₂n
  have hB1 : IsKQC (blaschke (-z₂)) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hcB1
  have hB2 : IsKQC (blaschke (f z₂)) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hcB2
  have hc1 : IsKQC (f ∘ blaschke (-z₂)) unitDisc (1 * K) :=
    thm7_1_comp hB1 hf (Eq.subset hcB1.2.2)
  have hc1img : (f ∘ blaschke (-z₂)) '' unitDisc = unitDisc := by
    rw [image_comp, hcB1.2.2, himg]
  have hc2 : IsKQC (blaschke (f z₂) ∘ (f ∘ blaschke (-z₂))) unitDisc (1 * K * 1) :=
    thm7_1_comp hc1 hB2 (Eq.subset hc1img)
  have hKeq : (1 : ℝ) * K * 1 = K := by ring
  rw [hKeq] at hc2
  have himgg : (blaschke (f z₂) ∘ (f ∘ blaschke (-z₂))) '' unitDisc = unitDisc := by
    rw [image_comp, hc1img, hcB2.2.2]
  have hgInto : IsKQCDiscInto (blaschke (f z₂) ∘ (f ∘ blaschke (-z₂))) K :=
    ⟨hc2, Eq.subset himgg⟩
  have hg0 : (blaschke (f z₂) ∘ (f ∘ blaschke (-z₂))) 0 = 0 := by
    simp only [Function.comp_apply, blaschke_neg_zero, blaschke_self]
  have hζ : blaschke z₂ z₁ ∈ unitDisc := mem_ball_zero_iff.mpr (blaschke_mem_unitDisc h₂n h₁n)
  have key := eq15_2 hgInto hg0 hζ
  have hgζ : (blaschke (f z₂) ∘ (f ∘ blaschke (-z₂))) (blaschke z₂ z₁) =
      blaschke (f z₂) (f z₁) := by
    simp only [Function.comp_apply, blaschke_neg_blaschke h₂n h₁n]
  rw [hgζ] at key
  exact key

/-- A distance estimate `dist (f x) (f y) ≤ C dist(x, y)^α` on `s` gives `HolderOnWith C α f s`. -/
theorem s15_t_holderOnWith_of_dist_le {f : ℂ → ℂ} {s : Set ℂ} {C α : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) :
    HolderOnWith C α f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- For `|z₁|, |z₂| ≤ r < 1`, `ρ = |(z₁ - z₂)/(1 - z̄₂ z₁)|` satisfies `ρ ≤ |z₁ - z₂|/(1 - r²)` and
`(1 - r²)²/4 ≤ 1 - ρ²`. -/
theorem s15_t_blaschke_bounds {z₁ z₂ : ℂ} {r : ℝ} (hr : r < 1) (h₁ : ‖z₁‖ ≤ r)
    (h₂ : ‖z₂‖ ≤ r) :
    ‖blaschke z₂ z₁‖ ≤ ‖z₁ - z₂‖ / (1 - r ^ 2) ∧
      (1 - r ^ 2) ^ 2 / 4 ≤ 1 - ‖blaschke z₂ z₁‖ ^ 2 := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans h₁
  have h₁1 : ‖z₁‖ < 1 := h₁.trans_lt hr
  have h₂1 : ‖z₂‖ < 1 := h₂.trans_lt hr
  have hprod : ‖conj z₂ * z₁‖ ≤ r ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul h₂ h₁ (norm_nonneg _) hr0
  have hlow : 1 - r ^ 2 ≤ ‖1 - conj z₂ * z₁‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (conj z₂ * z₁)
    rw [norm_one] at h
    linarith
  have hup : ‖1 - conj z₂ * z₁‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (conj z₂ * z₁)
    rw [norm_one] at h
    nlinarith
  have hcpos : 0 < 1 - r ^ 2 := by nlinarith
  have hdpos : 0 < ‖1 - conj z₂ * z₁‖ := hcpos.trans_le hlow
  refine ⟨?_, ?_⟩
  · rw [blaschke, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hcpos hlow
  · have hkey := one_sub_normSq_blaschke h₂1 h₁1
    simp only [Complex.normSq_eq_norm_sq] at hkey
    rw [hkey]
    have hn1 : 1 - r ^ 2 ≤ 1 - ‖z₁‖ ^ 2 := by nlinarith [norm_nonneg z₁]
    have hn2 : 1 - r ^ 2 ≤ 1 - ‖z₂‖ ^ 2 := by nlinarith [norm_nonneg z₂]
    have hprod2 : (1 - r ^ 2) ^ 2 ≤ (1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2) := by
      rw [sq]
      exact mul_le_mul hn1 hn2 hcpos.le (hcpos.le.trans hn1)
    have h4 : ‖1 - conj z₂ * z₁‖ ^ 2 ≤ 4 := by nlinarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg (1 - r ^ 2))]

/-- Consequence of Theorem 15.1: a `K`-q.c. self-map of the disc is Hölder continuous with
exponent `1/K` on every smaller closed disc. -/
theorem thm15_1_holder {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K)
    (himg : f '' unitDisc = unitDisc) {r : ℝ} (hr : r < 1) :
    ∃ C : ℝ≥0, HolderOnWith C (Real.toNNReal (1 / K)) f (closedBall 0 r) := by
  have hK : 1 ≤ K := hf.2.1
  have hKpos : 0 < K := by linarith
  have ha0 : 0 ≤ 1 / K := by positivity
  rcases lt_or_ge r 0 with hr0 | hr0
  · refine ⟨0, ?_⟩
    rw [closedBall_eq_empty.mpr hr0]
    exact holderOnWith_empty _ _ _
  have hcpos : 0 < 1 - r ^ 2 := by nlinarith
  have hmpos : 0 < ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hC0 : 0 ≤ 2 * (4 : ℝ) ^ (1 - 1 / K) / (1 - r ^ 2) ^ (1 / K) /
      ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) := by positivity
  refine ⟨Real.toNNReal (2 * (4 : ℝ) ^ (1 - 1 / K) / (1 - r ^ 2) ^ (1 / K) /
      ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K))), s15_t_holderOnWith_of_dist_le ?_⟩
  intro x hx y hy
  rw [Real.coe_toNNReal (1 / K) ha0, Real.coe_toNNReal _ hC0, dist_eq_norm, dist_eq_norm]
  have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  have hyr : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp hy
  have hxn : ‖x‖ < 1 := hxr.trans_lt hr
  have hyn : ‖y‖ < 1 := hyr.trans_lt hr
  have hxD : x ∈ unitDisc := mem_ball_zero_iff.mpr hxn
  have hyD : y ∈ unitDisc := mem_ball_zero_iff.mpr hyn
  obtain ⟨hρ, h1ρ⟩ := s15_t_blaschke_bounds hr hxr hyr
  have hmain := thm15_1 hf himg hxD hyD
  change ‖blaschke (f y) (f x)‖ ≤ (4 : ℝ) ^ (1 - 1 / K) * ‖blaschke y x‖ ^ (1 / K) /
      (1 - ‖blaschke y x‖ ^ 2) ^ (1 / (2 * K)) at hmain
  have hden : ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) ≤ (1 - ‖blaschke y x‖ ^ 2) ^ (1 / (2 * K)) :=
    Real.rpow_le_rpow (by positivity) h1ρ (by positivity)
  have hnum : ‖blaschke y x‖ ^ (1 / K) ≤ ‖x - y‖ ^ (1 / K) / (1 - r ^ 2) ^ (1 / K) := by
    rw [← Real.div_rpow (norm_nonneg _) hcpos.le]
    exact Real.rpow_le_rpow (norm_nonneg _) hρ ha0
  have hB : ‖blaschke (f y) (f x)‖ ≤
      (4 : ℝ) ^ (1 - 1 / K) * (‖x - y‖ ^ (1 / K) / (1 - r ^ 2) ^ (1 / K)) /
        ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) := by
    calc ‖blaschke (f y) (f x)‖
        ≤ (4 : ℝ) ^ (1 - 1 / K) * ‖blaschke y x‖ ^ (1 / K) /
            (1 - ‖blaschke y x‖ ^ 2) ^ (1 / (2 * K)) := hmain
      _ ≤ (4 : ℝ) ^ (1 - 1 / K) * ‖blaschke y x‖ ^ (1 / K) /
            ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) :=
          div_le_div_of_nonneg_left (by positivity) hmpos hden
      _ ≤ (4 : ℝ) ^ (1 - 1 / K) * (‖x - y‖ ^ (1 / K) / (1 - r ^ 2) ^ (1 / K)) /
            ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) := by
          gcongr
  have hfxD : f x ∈ unitDisc := himg ▸ mem_image_of_mem f hxD
  have hfyD : f y ∈ unitDisc := himg ▸ mem_image_of_mem f hyD
  have hfx : ‖f x‖ < 1 := mem_ball_zero_iff.mp hfxD
  have hfy : ‖f y‖ < 1 := mem_ball_zero_iff.mp hfyD
  have hdne : (1 : ℂ) - conj (f y) * f x ≠ 0 := blaschke_den_ne_zero hfy hfx
  have hd2 : ‖(1 : ℂ) - conj (f y) * f x‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (conj (f y) * f x)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    nlinarith [norm_nonneg (f x), norm_nonneg (f y)]
  have heq : ‖f x - f y‖ = ‖blaschke (f y) (f x)‖ * ‖(1 : ℂ) - conj (f y) * f x‖ := by
    rw [← norm_mul, blaschke, div_mul_cancel₀ _ hdne]
  calc ‖f x - f y‖ = ‖blaschke (f y) (f x)‖ * ‖(1 : ℂ) - conj (f y) * f x‖ := heq
    _ ≤ ‖blaschke (f y) (f x)‖ * 2 := mul_le_mul_of_nonneg_left hd2 (norm_nonneg _)
    _ ≤ (4 : ℝ) ^ (1 - 1 / K) * (‖x - y‖ ^ (1 / K) / (1 - r ^ 2) ^ (1 / K)) /
          ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) * 2 := by gcongr
    _ = 2 * (4 : ℝ) ^ (1 - 1 / K) / (1 - r ^ 2) ^ (1 / K) /
          ((1 - r ^ 2) ^ 2 / 4) ^ (1 / (2 * K)) * ‖x - y‖ ^ (1 / K) := by ring

/-! ### Mori-15 track interface (coordinator 553e2d) -/

/-- Off-centre version of `s13x_ho_log_le`: if `G` is `K`-q.c. on `D ⊇ B̄(z₀, δ)`,
`G(B(z₀, δ)) ⊆ Δ`, `G a = 0` and `G b = r > 0` with `|a - z₀|, |b - z₀| ≤ ρ < δ`, then
`log(δ/ρ) ≤ K log(4/r)` (Theorem 7.4 on the annulus `ρ < |z - z₀| < δ`, the separation
`s13x_ho_separates`, Grötzsch's Theorem 5.1 and `μ(r) ≤ log(4/r)`). -/
theorem m15_in_log_le {G : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hG : IsKQC G D K) {z₀ a b : ℂ}
    {ρ δ r : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ) (hD : closedBall z₀ δ ⊆ D)
    (hsub : G '' ball z₀ δ ⊆ unitDisc) (ha : ‖a - z₀‖ ≤ ρ) (hb : ‖b - z₀‖ ≤ ρ) (h0 : G a = 0)
    (hr : 0 < r) (h2 : G b = (r : ℂ)) : Real.log (δ / ρ) ≤ K * Real.log (4 / r) := by
  have hGc : ContinuousOn G D := hG.2.2.1.1
  have hGi : InjOn G D := hG.2.2.1.2.1
  have hballD : ball z₀ δ ⊆ D := ball_subset_closedBall.trans hD
  have hopen : IsOpen (G '' ball z₀ δ) :=
    aqc_isOpen_image_of_isHomeomorphOnto hG.2.2.1 (isOpen_image_of_isKQC hG) hballD isOpen_ball
  have hbB : b ∈ ball z₀ δ := mem_ball_iff_norm.2 (hb.trans_lt hρδ)
  have hr1 : r < 1 := by
    have h := hsub ⟨b, hbB, rfl⟩
    rw [h2, unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    exact h
  have hA : IsDoublyConnected (annulusAt z₀ ρ δ) := nf_g_isDoublyConnected_annulusAt z₀ hρ hρδ
  have hAD : closure (toExt (annulusAt z₀ ρ δ)) ⊆ toExt D :=
    (nf_e_closure_toExt_subset (isCompact_closedBall z₀ δ)
      fun w hw => mem_closedBall_iff_norm.2 hw.2.le).trans (image_mono hD)
  obtain ⟨hB, hAB, -⟩ := thm7_4_dcModulus_quasi_invariance hG hA hAD
  have hBsub : G '' annulusAt z₀ ρ δ ⊆ unitDisc :=
    (image_mono fun w hw => mem_ball_iff_norm.2 hw.2).trans hsub
  have hsep : SeparatesSets (G '' annulusAt z₀ ρ δ) (toExt (sphere 0 1))
      {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)} := by
    have h := s13x_ho_separates hGc hGi hρδ hballD hopen hsub ha hb
    rwa [h0, h2] at h
  have hgr := thm5_1_grotzsch hr hr1 hB hBsub hsep
  rw [gz_dcModulus_grotzschDomain hr hr1, ← gm_grotzschMu_eq hr hr1] at hgr
  rw [nf_e_dcModulus_annulusAt z₀ hρ hρδ] at hAB
  have hK0 : 0 ≤ K := zero_le_one.trans hG.2.1
  have hmu0 : 0 ≤ grotzschMu r := ENNReal.toReal_nonneg
  have key : ENNReal.ofReal (Real.log (δ / ρ)) ≤ ENNReal.ofReal (K * grotzschMu r) := by
    rw [ENNReal.ofReal_mul hK0]
    calc ENNReal.ofReal (Real.log (δ / ρ))
        ≤ ENNReal.ofReal K * dcModulus (G '' annulusAt z₀ ρ δ) := hAB
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (grotzschMu r) := by gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hmu0)] at key
  exact key.trans (mul_le_mul_of_nonneg_left (em_upper hr hr1) hK0)

/-- Theorem 15.2, inner case `|z₁ + z₂| < 1`: the ring `{r < |z - z₀| < 1/2}` (`z₀ = (z₁+z₂)/2`,
`r = |z₁ - z₂|/2`) has closure in `Δ`; Theorem 7.4, Grötzsch (after the disc automorphism taking `f z₁` to `0` and a
rotation) and `μ(t) ≤ log(4/t)` give `|f z₁ - f z₂| ≤ 8 |z₁ - z₂|^{1/K}`. -/
theorem m15_case_inner {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K) (himg : f '' unitDisc = unitDisc)
    {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) (hne : z₁ ≠ z₂) (hlt : ‖z₁ - z₂‖ < 1)
    (hsum : ‖z₁ + z₂‖ < 1) :
    ‖f z₁ - f z₂‖ ≤ 8 * ‖z₁ - z₂‖ ^ (1 / K) := by
  have hK : 1 ≤ K := hf.2.1
  have hK0 : 0 < K := by linarith
  have hfz₁ : f z₁ ∈ unitDisc := himg ▸ mem_image_of_mem f h₁
  have hfz₂ : f z₂ ∈ unitDisc := himg ▸ mem_image_of_mem f h₂
  have hfn₁ : ‖f z₁‖ < 1 := mem_ball_zero_iff.1 hfz₁
  have hfn₂ : ‖f z₂‖ < 1 := mem_ball_zero_iff.1 hfz₂
  have hfne : f z₁ ≠ f z₂ := fun h => hne (hf.2.2.1.2.1 h₁ h₂ h)
  set s : ℝ := ‖z₁ - z₂‖ with hs
  have hs0 : 0 < s := norm_pos_iff.2 (sub_ne_zero.2 hne)
  -- the normalized map `G = R ∘ M_{f z₁} ∘ f` with `G z₁ = 0`, `G z₂ = t > 0`
  have hden : (1 : ℂ) - conj (f z₁) * f z₂ ≠ 0 := blaschke_den_ne_zero hfn₁ hfn₂
  set u : ℂ := blaschke (f z₁) (f z₂) with hu
  have hu0 : u ≠ 0 := by
    rw [hu, blaschke]
    exact div_ne_zero (sub_ne_zero.2 hfne.symm) hden
  set t : ℝ := ‖u‖ with ht
  have ht0 : 0 < t := norm_pos_iff.2 hu0
  set c : ℂ := conj u / (t : ℂ) with hc
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero _).2 hu0) (ofReal_ne_zero.2 ht0.ne')
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      div_self ht0.ne']
  have hcu : c * u = (t : ℂ) := by
    have htc : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', ← ht]
    field_simp
  have hB : IsKQC (blaschke (f z₁)) unitDisc 1 :=
    isKQC_one_of_conformal isOpen_ball (isConformalOnto_blaschke hfn₁)
  have hR : IsKQC (fun w => c * w) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨(differentiable_id.const_mul c).differentiableOn,
      fun a _ b _ h => mul_left_cancel₀ hc0 h, rfl⟩
  set G : ℂ → ℂ := (fun w => c * w) ∘ (blaschke (f z₁) ∘ f) with hG
  have hGK : IsKQC G unitDisc K := by
    have h1 := thm7_1_comp (thm7_1_comp hf hB (Eq.subset himg)) hR (subset_univ _)
    rwa [mul_one, mul_one] at h1
  have hGΔ : G '' unitDisc ⊆ unitDisc := by
    rintro _ ⟨w, hw, rfl⟩
    have hfwD : f w ∈ unitDisc := himg ▸ mem_image_of_mem f hw
    have hfw : ‖f w‖ < 1 := mem_ball_zero_iff.1 hfwD
    show c * blaschke (f z₁) (f w) ∈ unitDisc
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hcn, one_mul]
    exact blaschke_mem_unitDisc hfn₁ hfw
  have hG1 : G z₁ = 0 := by
    show c * blaschke (f z₁) (f z₁) = 0
    rw [blaschke_self, mul_zero]
  have hG2 : G z₂ = (t : ℂ) := hcu
  -- the ring `{s/2 < |z - z₀| < 1/2}`, `z₀ = (z₁ + z₂)/2`
  set z₀ : ℂ := (z₁ + z₂) / 2 with hz₀
  have hρ : 0 < s / 2 := by positivity
  have hρδ : s / 2 < 1 / 2 := by linarith
  have hz₀n : ‖z₀‖ = ‖z₁ + z₂‖ / 2 := by
    rw [hz₀, norm_div]
    norm_num
  have hD : closedBall z₀ (1 / 2) ⊆ unitDisc := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [unitDisc, mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - z₀) + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ < 1 := by rw [hz₀n]; linarith
  have hsub : G '' ball z₀ (1 / 2) ⊆ unitDisc :=
    (image_mono (ball_subset_closedBall.trans hD)).trans hGΔ
  have ha : ‖z₁ - z₀‖ ≤ s / 2 := by
    apply le_of_eq
    have h : z₁ - (z₁ + z₂) / 2 = (z₁ - z₂) / 2 := by ring
    rw [hz₀, h, norm_div, hs]
    norm_num
  have hb : ‖z₂ - z₀‖ ≤ s / 2 := by
    apply le_of_eq
    have h : z₂ - (z₁ + z₂) / 2 = -((z₁ - z₂) / 2) := by ring
    rw [hz₀, h, norm_neg, norm_div, hs]
    norm_num
  have hlog := m15_in_log_le hGK hρ hρδ hD hsub ha hb hG1 ht0 hG2
  -- `log(1/s) ≤ K log(4/t)` gives `t ≤ 4 s^{1/K}`
  have hδρ : (1 / 2 : ℝ) / (s / 2) = 1 / s := by
    field_simp
  rw [hδρ] at hlog
  have ht4 : t ≤ 4 * s ^ (1 / K) := by
    have hspos : 0 < s ^ (1 / K) := Real.rpow_pos_of_pos hs0 _
    have h4pos : 0 < 4 * s ^ (1 / K) := by positivity
    rw [← Real.log_le_log_iff ht0 h4pos, Real.log_mul (by norm_num) hspos.ne',
      Real.log_rpow hs0]
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) ht0.ne', one_div s, Real.log_inv] at hlog
    have h2 : Real.log t - Real.log 4 ≤ Real.log s / K := by
      rw [le_div_iff₀ hK0]
      linarith
    have h3 : 1 / K * Real.log s = Real.log s / K := by ring
    rw [h3]
    linarith
  -- `|f z₁ - f z₂| = t |1 - conj (f z₁) f z₂| ≤ 2t`
  have hd2 : ‖(1 : ℂ) - conj (f z₁) * f z₂‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (conj (f z₁) * f z₂)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    nlinarith [norm_nonneg (f z₁), norm_nonneg (f z₂)]
  have heq : ‖f z₁ - f z₂‖ = t * ‖(1 : ℂ) - conj (f z₁) * f z₂‖ := by
    rw [norm_sub_rev, ht, hu, ← norm_mul, blaschke, div_mul_cancel₀ _ hden]
  calc ‖f z₁ - f z₂‖ = t * ‖(1 : ℂ) - conj (f z₁) * f z₂‖ := heq
    _ ≤ t * 2 := mul_le_mul_of_nonneg_left hd2 ht0.le
    _ ≤ 4 * s ^ (1 / K) * 2 := by gcongr
    _ = 8 * s ^ (1 / K) := by ring

/-- The closed exterior `ℂ ∖ B(z₀, R)` of a disc is preconnected (polar coordinates about `z₀`). -/
theorem m15_mc_isPreconnected_compl_ball (z₀ : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (ball z₀ R)ᶜ := by
  have hmap : (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ici R ×ˢ univ)
      = (ball z₀ R)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      have hρ' : R ≤ ρ := hρ
      show z₀ + (ρ : ℂ) * exp ((θ : ℂ) * I) ∈ (ball z₀ R)ᶜ
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, add_sub_cancel_left, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hR.trans hρ')]
      exact hρ'
    · intro z hz
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hz
      refine ⟨(‖z - z₀‖, arg (z - z₀)), ⟨hz, mem_univ _⟩, ?_⟩
      show z₀ + ((‖z - z₀‖ : ℝ) : ℂ) * exp (((arg (z - z₀) : ℝ) : ℂ) * I) = z
      rw [Complex.norm_mul_exp_arg_mul_I]
      ring
  rw [← hmap]
  exact (isPreconnected_Ici.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

/-- The Mori condition for the image of an off-centre ring: if `F` is a homeomorphism of `ℂ` onto `ℂ` with `F 0 = 0`,
`0 < r < R ≤ |z₀|` and `a, b` lie in the inner closed disc with `F a, F b ∈ Δ̄`, then
`F({r < |z - z₀| < R})` satisfies the Mori condition with `d = |F a - F b|`. -/
theorem m15_moriCondition {F : ℂ → ℂ} (hF : IsHomeomorphOnto F univ univ) (hF0 : F 0 = 0) {z₀ : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R ≤ ‖z₀‖) {a b : ℂ} (ha : ‖a - z₀‖ ≤ r)
    (hb : ‖b - z₀‖ ≤ r) (hFa : ‖F a‖ ≤ 1) (hFb : ‖F b‖ ≤ 1) :
    MoriCondition (F '' annulusAt z₀ r R) ‖F a - F b‖ := by
  obtain ⟨e, rfl⟩ := s13x_de_exists_homeomorph hF
  set S : Set ExtPlane := (toExt (e '' annulusAt z₀ r R))ᶜ with hS
  set P : Set ExtPlane := toExt (e '' closedBall z₀ r) with hP
  set Q : Set ExtPlane := (toExt (e '' ball z₀ R))ᶜ with hQ
  have hR0 : 0 < R := hr.trans hrR
  have hsub : closedBall z₀ r ⊆ ball z₀ R := closedBall_subset_ball hrR
  have hann : annulusAt z₀ r R ⊆ ball z₀ R := fun z hz => by
    rw [mem_ball, dist_eq_norm]
    exact hz.2
  have hPc : IsClosed P :=
    (((isCompact_closedBall z₀ r).image e.continuous).image OnePoint.continuous_coe).isClosed
  have hQc : IsClosed Q := isClosed_compl_toExt (e.isOpenMap _ isOpen_ball)
  have hPconn : IsPreconnected P :=
    ((convex_closedBall z₀ r).isPreconnected.image _ e.continuous.continuousOn).image _
      OnePoint.continuous_coe.continuousOn
  have hQeq : Q = e.onePointCongr '' (toExt (ball z₀ R))ᶜ := by
    rw [hQ, e.onePointCongr.image_compl, s13x_de_image_toExt]
  have hQconn : IsPreconnected Q := by
    rw [hQeq]
    exact (isPreconnected_compl_toExt isBounded_ball
      (m15_mc_isPreconnected_compl_ball z₀ hR0.le)).image _ e.onePointCongr.continuous.continuousOn
  have hPB : P ⊆ toExt (e '' ball z₀ R) := image_mono (image_mono hsub)
  have hPS : P ⊆ S := by
    rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ ⟨v, ⟨u', hu', rfl⟩, hv⟩
    have huu : u' = u := e.injective (OnePoint.coe_injective hv)
    rw [huu] at hu'
    rw [mem_closedBall, dist_eq_norm] at hu
    exact absurd hu'.1 (not_lt.2 hu)
  have hQS : Q ⊆ S := compl_subset_compl.2 (image_mono (image_mono hann))
  have hSPQ : S ⊆ P ∪ Q := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (extInf_notMem_toExt _)
    | coe w =>
      by_cases hw : w ∈ e '' ball z₀ R
      · left
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨e u, ⟨u, ?_, rfl⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm]
        by_contra hnot
        rw [mem_ball, dist_eq_norm] at hu
        exact hx ⟨e u, ⟨u, ⟨lt_of_not_ge hnot, hu⟩, rfl⟩, rfl⟩
      · right
        exact fun h' => hw (coe_mem_toExt_iff.1 h')
  have hPQ : P ∩ Q = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxP hxQ
    exact hxQ (hPB hxP)
  have hinfQ : extInf ∈ Q := extInf_notMem_toExt _
  have h0Q : ((0 : ℂ) : ExtPlane) ∈ Q := by
    intro h
    obtain ⟨u, hu, hu0⟩ := coe_mem_toExt_iff.1 h
    have hu0' : u = 0 := e.injective (hu0.trans hF0.symm)
    rw [hu0', mem_ball, dist_eq_norm, zero_sub, norm_neg] at hu
    linarith
  have haP : ((e a : ℂ) : ExtPlane) ∈ P :=
    ⟨e a, ⟨a, by rw [mem_closedBall, dist_eq_norm]; exact ha, rfl⟩, rfl⟩
  have hbP : ((e b : ℂ) : ExtPlane) ∈ P :=
    ⟨e b, ⟨b, by rw [mem_closedBall, dist_eq_norm]; exact hb, rfl⟩, rfl⟩
  have hPcomp : P ⊆ connectedComponentIn S ((e a : ℂ) : ExtPlane) :=
    hPconn.subset_connectedComponentIn haP hPS
  have hQcomp : Q ⊆ connectedComponentIn S extInf :=
    hQconn.subset_connectedComponentIn hinfQ hQS
  refine ⟨extInf, hQS hinfQ,
    insert_subset_iff.2 ⟨hQcomp h0Q, singleton_subset_iff.2 (hQcomp hinfQ)⟩,
    ((e a : ℂ) : ExtPlane), hPS haP, ?_, ?_⟩
  · intro heq
    have hC := isPreconnected_iff_subset_of_disjoint_closed.1
      (isPreconnected_connectedComponentIn (x := ((e a : ℂ) : ExtPlane)) (F := S)) P Q hPc hQc
      ((connectedComponentIn_subset _ _).trans hSPQ) (by rw [hPQ, inter_empty])
    have hmemInf : extInf ∈ connectedComponentIn S ((e a : ℂ) : ExtPlane) :=
      heq ▸ mem_connectedComponentIn (hQS hinfQ)
    have hmema : ((e a : ℂ) : ExtPlane) ∈ connectedComponentIn S ((e a : ℂ) : ExtPlane) :=
      mem_connectedComponentIn (hPS haP)
    rcases hC with hC | hC
    · exact extInf_notMem_toExt _ (hC hmemInf)
    · exact hC hmema (hPB haP)
  · have hbdd : Bornology.IsBounded
        ({z : ℂ | (z : ExtPlane) ∈ connectedComponentIn S ((e a : ℂ) : ExtPlane)} ∩
          closedBall 0 1) :=
      isBounded_closedBall.subset inter_subset_right
    have ha' : e a ∈ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn S ((e a : ℂ) : ExtPlane)} ∩
        closedBall 0 1 :=
      ⟨hPcomp haP, mem_closedBall_zero_iff.2 hFa⟩
    have hb' : e b ∈ {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn S ((e a : ℂ) : ExtPlane)} ∩
        closedBall 0 1 :=
      ⟨hPcomp hbP, mem_closedBall_zero_iff.2 hFb⟩
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hbdd ha' hb'

/-- The final estimate of Theorem 15.2: `log(1/s) ≤ K μ(d/(2√(2+√(4-d²))))` implies `d < 16 s^{1/K}`
(`μ(r) ≤ log(4/r)` and `√(2+√(4-d²)) < 2` for `d > 0`). -/
theorem m15_final_ineq {K d s : ℝ} (hK : 1 ≤ K) (hd₀ : 0 < d) (hd₂ : d ≤ 2) (hs₀ : 0 < s) (hs₁ : s < 1)
    (h : Real.log (1 / s) ≤ K * grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) :
    d < 16 * s ^ (1 / K) := by
  obtain ⟨hr₀, hr₁⟩ := mo_radius_mem hd₀ hd₂
  have hμ := em_upper hr₀ hr₁
  have hK0 : 0 < K := by linarith
  have hsq : Real.sqrt (4 - d ^ 2) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith [sq_pos_of_pos hd₀]
  have hsq0 : 0 ≤ Real.sqrt (4 - d ^ 2) := Real.sqrt_nonneg _
  have hu2 : Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have hu0 : 0 < Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) := Real.sqrt_pos.2 (by linarith)
  have h4r : 4 / (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) =
      8 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) / d := by
    field_simp
    ring
  have h4r_lt : 4 / (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) < 16 / d := by
    rw [h4r]
    exact div_lt_div_of_pos_right (by linarith) hd₀
  have h4r_pos : 0 < 4 / (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) :=
    div_pos (by norm_num) hr₀
  have hlog_lt : Real.log (4 / (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) <
      Real.log (16 / d) := Real.log_lt_log h4r_pos h4r_lt
  have hmain : Real.log (1 / s) < K * Real.log (16 / d) := by
    calc Real.log (1 / s) ≤ K * grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) := h
      _ ≤ K * Real.log (4 / (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) :=
          mul_le_mul_of_nonneg_left hμ hK0.le
      _ < K * Real.log (16 / d) := mul_lt_mul_of_pos_left hlog_lt hK0
  have h1s : Real.log (1 / s) = -Real.log s := by
    rw [one_div, Real.log_inv]
  have h16d : Real.log (16 / d) = Real.log 16 - Real.log d := Real.log_div (by norm_num) hd₀.ne'
  rw [h1s, h16d] at hmain
  have hkey : Real.log d * K < Real.log 16 * K + Real.log s := by linarith
  have hrhs_pos : 0 < 16 * s ^ (1 / K) := by positivity
  have hlog_rhs : Real.log (16 * s ^ (1 / K)) = Real.log 16 + (1 / K) * Real.log s := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hs₀ _).ne', Real.log_rpow hs₀]
  have hdiv : Real.log d < Real.log 16 + (1 / K) * Real.log s := by
    have h2 : Real.log d = Real.log d * K / K := by field_simp
    have h3 : Real.log 16 + (1 / K) * Real.log s = (Real.log 16 * K + Real.log s) / K := by
      field_simp
    rw [h2, h3]
    exact div_lt_div_of_pos_right hkey hK0
  rw [← Real.log_lt_log_iff hd₀ hrhs_pos, hlog_rhs]
  exact hdiv

/-- Theorem 15.2, outer case `|z₁ + z₂| ≥ 1`: reflect `f` to a `K`-q.c. homeomorphism of `ℂ` (`ab_reflect` with the
boundary extension `s13x_disc_extension`); the image of `{r < |z - z₀| < 1/2}` satisfies the Mori condition with
`d = |f z₁ - f z₂|`, so Theorem 5.4 and the modulus of the Mori domain bound its modulus. -/
theorem m15_case_outer {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K) (himg : f '' unitDisc = unitDisc)
    (hf0 : f 0 = 0) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) (hne : z₁ ≠ z₂)
    (hlt : ‖z₁ - z₂‖ < 1) (hsum : 1 ≤ ‖z₁ + z₂‖) :
    ‖f z₁ - f z₂‖ < 16 * ‖z₁ - z₂‖ ^ (1 / K) := by
  have hK : 1 ≤ K := hf.2.1
  have hKpos : 0 < K := by linarith
  -- the boundary extension of `f` and the reflected `K`-q.c. homeomorphism `F` of `ℂ`
  obtain ⟨H, hH⟩ := s13x_disc_extension ⟨K, hf⟩ himg
  obtain ⟨F, hFK, hFimg, hFeq, -⟩ := ab_reflect hf himg hf0 hH
  have hFhom : IsHomeomorphOnto F univ univ := by
    have h := hFK.2.2.1
    rwa [hFimg] at h
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hF0 : F 0 = 0 := (hFeq h0D).trans hf0
  have hF₁ : F z₁ = f z₁ := hFeq h₁
  have hF₂ : F z₂ = f z₂ := hFeq h₂
  -- the ring `{r < |z - z₀| < 1/2}`, `z₀ = (z₁ + z₂)/2`, `r = |z₁ - z₂|/2`
  have hs0 : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hr : 0 < ‖z₁ - z₂‖ / 2 := by positivity
  have hrR : ‖z₁ - z₂‖ / 2 < 1 / 2 := by linarith
  have hR : (1 / 2 : ℝ) ≤ ‖(z₁ + z₂) / 2‖ := by
    rw [norm_div, Complex.norm_two]
    linarith
  have ha : ‖z₁ - (z₁ + z₂) / 2‖ ≤ ‖z₁ - z₂‖ / 2 := by
    have h : z₁ - (z₁ + z₂) / 2 = (z₁ - z₂) / 2 := by ring
    rw [h, norm_div, Complex.norm_two]
  have hb : ‖z₂ - (z₁ + z₂) / 2‖ ≤ ‖z₁ - z₂‖ / 2 := by
    have h : z₂ - (z₁ + z₂) / 2 = -((z₁ - z₂) / 2) := by ring
    rw [h, norm_neg, norm_div, Complex.norm_two]
  have hfD₁ : f z₁ ∈ unitDisc := himg ▸ mem_image_of_mem f h₁
  have hfD₂ : f z₂ ∈ unitDisc := himg ▸ mem_image_of_mem f h₂
  have hfz₁ : ‖f z₁‖ < 1 := mem_ball_zero_iff.1 hfD₁
  have hfz₂ : ‖f z₂‖ < 1 := mem_ball_zero_iff.1 hfD₂
  have hFa : ‖F z₁‖ ≤ 1 := by rw [hF₁]; exact hfz₁.le
  have hFb : ‖F z₂‖ ≤ 1 := by rw [hF₂]; exact hfz₂.le
  have hMori := m15_moriCondition hFhom hF0 hr hrR hR ha hb hFa hFb
  rw [hF₁, hF₂] at hMori
  -- Theorem 7.4 for `F` on the ring
  have hB := nf_g_isDoublyConnected_annulusAt ((z₁ + z₂) / 2) hr hrR
  have hBD : closure (toExt (annulusAt ((z₁ + z₂) / 2) (‖z₁ - z₂‖ / 2) (1 / 2))) ⊆ toExt univ :=
    (nf_e_closure_toExt_subset (isCompact_closedBall ((z₁ + z₂) / 2) (1 / 2))
      (fun z hz => mem_closedBall.2 (by rw [dist_eq_norm]; exact hz.2.le))).trans
      (image_mono (subset_univ _))
  obtain ⟨hFB, hle, -⟩ := thm7_4_dcModulus_quasi_invariance hFK hB hBD
  -- `d = |f z₁ - f z₂| ∈ (0, 2]`
  have hd0 : 0 < ‖f z₁ - f z₂‖ := by
    rw [← hF₁, ← hF₂]
    exact norm_pos_iff.2 (sub_ne_zero.2 fun h => hne (hFhom.2.1 (mem_univ _) (mem_univ _) h))
  have hd2 : ‖f z₁ - f z₂‖ ≤ 2 := by
    have h := norm_sub_le (f z₁) (f z₂)
    linarith
  -- Mori's theorem (5.15) for `F(B)`
  have hmori := eq5_15 hd0 hd2 hFB hMori
  rw [nf_e_dcModulus_annulusAt _ hr hrR] at hle
  have hcomb : ENNReal.ofReal (Real.log (1 / 2 / (‖z₁ - z₂‖ / 2))) ≤
      ENNReal.ofReal K * ENNReal.ofReal
        (grotzschMu (‖f z₁ - f z₂‖ /
          (2 * Real.sqrt (2 + Real.sqrt (4 - ‖f z₁ - f z₂‖ ^ 2))))) :=
    hle.trans (by gcongr)
  rw [← ENNReal.ofReal_mul hKpos.le] at hcomb
  have hlogpos : 0 < Real.log (1 / 2 / (‖z₁ - z₂‖ / 2)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hr]
    linarith
  have hlog := (ENNReal.ofReal_le_ofReal_iff'.1 hcomb).resolve_right (not_le.2 hlogpos)
  have heq : 1 / 2 / (‖z₁ - z₂‖ / 2) = 1 / ‖z₁ - z₂‖ := by
    field_simp
  rw [heq] at hlog
  exact m15_final_ineq hK hd0 hd2 hs0 hlt hlog

/-- **Theorem 15.2** (森, Mori).  For a `K`-q.c. self-map `f` of `Δ` with `f(0) = 0` and
`z₁ ≠ z₂` in `Δ`, `|f(z₁) - f(z₂)| < 16 |z₁ - z₂|^{1/K}`. -/
theorem thm15_2_mori {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K) (himg : f '' unitDisc = unitDisc)
    (hf0 : f 0 = 0) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) (hne : z₁ ≠ z₂) :
    ‖f z₁ - f z₂‖ < 16 * ‖z₁ - z₂‖ ^ (1 / K) := by
  have hK : 1 ≤ K := hf.2.1
  have hz₁ : f z₁ ∈ unitDisc := himg ▸ mem_image_of_mem f h₁
  have hz₂ : f z₂ ∈ unitDisc := himg ▸ mem_image_of_mem f h₂
  have hn₁ : ‖f z₁‖ < 1 := mem_ball_zero_iff.1 hz₁
  have hn₂ : ‖f z₂‖ < 1 := mem_ball_zero_iff.1 hz₂
  have hs : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  by_cases hge : 1 ≤ ‖z₁ - z₂‖
  · have hpow : 1 ≤ ‖z₁ - z₂‖ ^ (1 / K) := Real.one_le_rpow hge (by positivity)
    calc ‖f z₁ - f z₂‖ ≤ ‖f z₁‖ + ‖f z₂‖ := norm_sub_le _ _
      _ < 16 * 1 := by linarith
      _ ≤ 16 * ‖z₁ - z₂‖ ^ (1 / K) := by gcongr
  · have hlt : ‖z₁ - z₂‖ < 1 := lt_of_not_ge hge
    by_cases hsum : ‖z₁ + z₂‖ < 1
    · have h8 := m15_case_inner hf himg h₁ h₂ hne hlt hsum
      have hpos : 0 < ‖z₁ - z₂‖ ^ (1 / K) := Real.rpow_pos_of_pos hs _
      linarith
    · exact m15_case_outer hf himg hf0 h₁ h₂ hne hlt (le_of_not_gt hsum)

/-- The family `𝓕` of `K`-q.c. maps of the plane onto itself fixing `0` and `1` (and `∞`). -/
def IsKQCNormalizedPlane (f : ℂ → ℂ) (K : ℝ) : Prop :=
  IsKQC f univ K ∧ f '' univ = univ ∧ f 0 = 0 ∧ f 1 = 1

/-- `Λ(ρ) > 0` for `ρ > 0`: `Λ(ρ)` is the modulus of the quadrilateral `ℍ(∞, -1, 0, ρ)`. -/
theorem b4_num_quadLambda_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < quadLambda ρ := by
  have h : quadLambda ρ = (⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩ : TopQuad).modulus := rfl
  rw [h]
  exact modulus_pos _

/-- `Λ(1) = 1` (`Λ(1)² = 1` by (5.20), and `Λ(1) > 0`). -/
theorem b4_quadLambda_one : quadLambda 1 = 1 := by
  have h := eq5_20 (ρ := 1) one_pos
  rw [div_one] at h
  exact (mul_self_eq_one_iff.1 h).resolve_right (by linarith [b4_num_quadLambda_pos one_pos])

/-- If `Λ(ρ) ≤ K` then `ρ ≤ λ(K)` (`λ(K) = sup {ρ > 0 | Λ(ρ) ≤ K}`, bounded above since `Λ → ∞`). -/
theorem b4_le_lambdaInv {K ρ : ℝ} (hρ : 0 < ρ) (h : quadLambda ρ ≤ K) : ρ ≤ lambdaInv K := by
  obtain ⟨R₀, hKR₀, hR₀⟩ :=
    ((quadLambda_strictMono.2.2.eventually_gt_atTop K).and (eventually_gt_atTop 0)).exists
  have hbdd : BddAbove {σ : ℝ | 0 < σ ∧ quadLambda σ ≤ K} := by
    refine ⟨R₀, fun σ hσ => not_lt.1 fun hlt => ?_⟩
    have := quadLambda_strictMono.1 hR₀ hσ.1 hlt
    linarith [hσ.2]
  exact le_csSup hbdd ⟨hρ, h⟩

/-! ### tdist (coordinator 553e2d): Theorem 15.3 by a holomorphic motion -/

/-- `φ` maps `ℍ` into `ℂ ∖ {0, 1}` (no covering needed: `e₁, e₂, e₃` are distinct). -/
theorem td_modularPhi_mapsTo : MapsTo modularPhi upperHalf {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro w hw
  obtain ⟨h01, h02, h12⟩ := mphi_weierstrassE_pairwise_ne hw
  have hd : weierstrassE w 2 - weierstrassE w 1 ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  refine ⟨?_, ?_⟩
  · exact div_ne_zero (sub_ne_zero.2 (Ne.symm h02)) hd
  · show (weierstrassE w 2 - weierstrassE w 0) / (weierstrassE w 2 - weierstrassE w 1) ≠ 1
    rw [Ne, div_eq_one_iff_eq hd]
    intro h
    exact h01 (by linear_combination -h)

/-- The pointwise density comparison behind (A): `η(φ w) |φ'(w) v| ≤ |v| / Im w`. -/
theorem td_enorm_density_comp_le {w : ℂ} (hw : w ∈ upperHalf) (v : ℂ) :
    ENNReal.ofReal (puncturedSphereDensity (modularPhi w)) * ‖deriv modularPhi w * v‖ₑ ≤
      ENNReal.ofReal (poincareDensity upperHalf w) * ‖v‖ₑ := by
  have hy : 0 < w.im := hw
  rw [(eq14_6_well_defined hy hy rfl).2, poincareDensity_upperHalf hw, enorm_mul, ← mul_assoc]
  gcongr
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_ne ‖deriv modularPhi w‖ 0 with h0 | h0
  · rw [h0]; simp only [zero_mul, div_zero, mul_zero]; positivity
  · refine le_of_eq ?_
    field_simp

/-- **(A)**: `δ(φ z, φ w) ≤ d_ℍ(z, w)`. -/
theorem td_puncturedSphereDist_le_dist (z w : UpperHalfPlane) :
    puncturedSphereDist (modularPhi z) (modularPhi w) ≤ ENNReal.ofReal (dist z w) := by
  have hz : (z : ℂ) ∈ upperHalf := z.im_pos
  have hw : (w : ℂ) ∈ upperHalf := w.im_pos
  obtain ⟨γ, hγ, hlen, -⟩ := upperHalf_geodesic hz hw
  rw [poincareDist_upperHalf] at hlen
  obtain ⟨γ', hγ'eq, hγ'path⟩ := exists_isPathIn_comp isOpen_upperHalf
    mphi_differentiableOn_modularPhi_upperHalf td_modularPhi_mapsTo hγ
  refine (iInf₂_le γ' hγ'path).trans (le_of_le_of_eq ?_ hlen)
  obtain ⟨⟨K, hK⟩, -, -, htr⟩ := hγ
  have hKu : LipschitzOnWith K γ.toFun (uIcc 0 1) := by rw [uIcc_of_le zero_le_one]; exact hK
  have hγae := ae_differentiableAt_of_lipschitzOn hKu
  unfold LRCurve.rhoLength
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hγae] with t ht hdt
  have htI : t ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self ht
  have hmem : γ.toFun t ∈ upperHalf := htr ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hφd : DifferentiableAt ℂ modularPhi (γ.toFun t) :=
    mphi_differentiableOn_modularPhi_upperHalf.differentiableAt (isOpen_upperHalf.mem_nhds hmem)
  have hchain : deriv γ'.toFun t = deriv modularPhi (γ.toFun t) * deriv γ.toFun t := by
    rw [hγ'eq]
    exact (hφd.hasDerivAt.comp t (hdt htI).hasDerivAt).deriv
  rw [hchain, hγ'eq, Function.comp_apply]
  exact td_enorm_density_comp_le hmem _

/-! #### M0. the identity is the normalized solution of `μ = 0` -/

/-- The complex dilatation of the identity vanishes. -/
theorem td_complexDilatation_id (z : ℂ) : complexDilatation id z = 0 := by
  simp [complexDilatation, dzbar]

/-- The identity is the normalized solution of the Beltrami equation for an a.e. vanishing coefficient. -/
theorem td_id_normalized {μ : ℂ → ℂ} (hμ : ∀ᵐ z, μ z = 0) : IsNormalizedSolution id μ := by
  refine ⟨⟨1, isKQC_one_of_conformal isOpen_univ (isConformalOnto_id univ)⟩, image_id _, rfl, rfl, ?_⟩
  filter_upwards [hμ] with z hz
  rw [hz, td_complexDilatation_id]

/-! #### M1. the holomorphic motion `t ↦ f^{(t/s)μ_f}(z)` -/

/-- **Holomorphic motion.** For `f ∈ 𝓕`, `z ≠ 0, 1` and `(K-1)/(K+1) < s < 1`, the point `f_t(z)` of the normalized solution `f_t` for `(t/s) μ_f` depends holomorphically on `t ∈ Δ` (Theorems 13.7, 13.8), avoids `0` and `1`, and equals `z` at `t = 0` and `f z` at `t = s`. -/
theorem td_motion {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) {s : ℝ} (hks : (K - 1) / (K + 1) < s) (hs1 : s < 1) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (ball 0 1) ∧ Φ 0 = z ∧ Φ s = f z ∧
      ∀ t ∈ ball (0 : ℂ) 1, Φ t ≠ 0 ∧ Φ t ≠ 1 := by
  obtain ⟨hK, hfs, hf0, hf1⟩ := hf
  have hK1 : 1 ≤ K := hK.2.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hs0 : 0 < s := lt_of_le_of_lt hk0 hks
  have hμ : IsBeltramiCoeff (complexDilatation f) univ ((K - 1) / (K + 1)) :=
    (thm10_2_genHomeoSolution_of_isKQC hK).1
  have hk'0 : 0 ≤ (K - 1) / (K + 1) / s := div_nonneg hk0 hs0.le
  have hk'1 : (K - 1) / (K + 1) / s < 1 := (div_lt_one hs0).2 hks
  set μt : ℂ → ℂ → ℂ := fun t w => t / s * complexDilatation f w with hμtdef
  have hμt : ∀ t ∈ ball (0 : ℂ) 1, IsBeltramiCoeff (μt t) univ ((K - 1) / (K + 1) / s) := by
    intro t ht
    refine ⟨hμ.1.const_mul _, ?_⟩
    filter_upwards [hμ.2] with w hw
    have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
    have hsn : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    simp only [hμtdef, norm_mul, norm_div, hsn]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (by nlinarith [norm_nonneg (complexDilatation f w), norm_nonneg t]) hs0.le
  have hhol : ∀ w, DifferentiableOn ℂ (fun t => μt t w) (ball 0 1) := fun w =>
    ((differentiable_id.div_const (s : ℂ)).mul_const (complexDilatation f w)).differentiableOn
  classical
  let F : ℂ → ℂ → ℂ := fun t =>
    if ht : t ∈ ball (0 : ℂ) 1 then (thm13_7_normalized_existence hk'0 hk'1 (hμt t ht)).choose
    else id
  have hF : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (F t) (μt t) := by
    intro t ht
    simp only [F, dite_eq_left ht]
    exact (thm13_7_normalized_existence hk'0 hk'1 (hμt t ht)).choose_spec.1
  have hFuniq : ∀ t (ht : t ∈ ball (0 : ℂ) 1) (g : ℂ → ℂ), IsNormalizedSolution g (μt t) →
      g = F t := by
    intro t ht g hg
    simp only [F, dite_eq_left ht]
    exact (thm13_7_normalized_existence hk'0 hk'1 (hμt t ht)).choose_spec.2.2 g hg
  have hdiff := thm13_8_ahlfors_bers_holomorphic isOpen_ball hk'0 hk'1 hμt hhol hF
  refine ⟨fun t => F t z, hdiff z, ?_, ?_, ?_⟩
  · have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have hid := hFuniq 0 h0 id (td_id_normalized (Eventually.of_forall fun w => by simp [hμtdef]))
    show F 0 z = z
    rw [← hid]
    rfl
  · have hsb : (s : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      exact hs1
    have hfeq := hFuniq s hsb f ⟨⟨K, hK⟩, hfs, hf0, hf1, Eventually.of_forall fun w => by
      simp [hμtdef, div_self (ofReal_ne_zero.2 hs0.ne')]⟩
    show F s z = f z
    rw [← hfeq]
  · intro t ht
    obtain ⟨⟨K', hK'⟩, -, h0, h1, -⟩ := hF t ht
    have hinj := hK'.2.2.1.2.1
    exact ⟨fun h => hz0 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm)),
      fun h => hz1 (hinj (mem_univ _) (mem_univ _) (h.trans h1.symm))⟩

/-! #### M2. lifting a holomorphic `Φ : Δ → ℂ ∖ {0,1}` through `φ` to a holomorphic `Ψ : Δ → ℍ` -/

/-- `φ` is continuous on `ℍ`. -/
theorem td_continuous_modularPhiH : Continuous modularPhiH := by
  have h : ContinuousOn modularPhi upperHalf :=
    mphi_differentiableOn_modularPhi_upperHalf.continuousOn
  exact h.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)

/-- A holomorphic map `Φ : Δ → ℂ ∖ {0, 1}` lifts through the covering `φ` to a holomorphic map `Ψ : Δ → ℍ` with prescribed value at `0`. -/
theorem td_lift_holomorphic (hcov : IsCoveringMapOn modularPhiH {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (ball 0 1))
    (hΦs : ∀ t ∈ ball (0 : ℂ) 1, Φ t ≠ 0 ∧ Φ t ≠ 1) {a₀ : UpperHalfPlane}
    (ha₀ : modularPhiH a₀ = Φ 0) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (ball 0 1) ∧ Ψ 0 = a₀ ∧
      ∀ t ∈ ball (0 : ℂ) 1, 0 < (Ψ t).im ∧ modularPhi (Ψ t) = Φ t := by
  classical
  have : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  have : SimplyConnectedSpace (ball (0 : ℂ) 1) := SimplyConnectedSpace.ofContractible _
  have : LocallyPathConnectedSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).locallyPathConnectedSpace
  let Φc : C(ball (0 : ℂ) 1, ℂ) := ⟨fun t => Φ t, hΦ.continuousOn.domRestrict⟩
  let o : ball (0 : ℂ) 1 := ⟨0, mem_ball_self one_pos⟩
  obtain ⟨Ψ₀, ⟨hΨ₀0, hΨ₀⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts Φc (a₀ := o) (e₀ := a₀) ha₀ (fun t => hΦs t.1 t.2)
  let Ψ : ℂ → ℂ := fun t => if ht : t ∈ ball (0 : ℂ) 1 then (Ψ₀ ⟨t, ht⟩ : ℂ) else 0
  have hΨv : ∀ t (ht : t ∈ ball (0 : ℂ) 1), Ψ t = Ψ₀ ⟨t, ht⟩ := fun t ht => dite_eq_left ht
  have hΨφ : ∀ t (ht : t ∈ ball (0 : ℂ) 1), modularPhi (Ψ t) = Φ t := by
    intro t ht
    rw [hΨv t ht]
    exact congrFun hΨ₀ ⟨t, ht⟩
  have hΨc : ContinuousOn Ψ (ball 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (ball (0 : ℂ) 1).domRestrict Ψ = fun t => (Ψ₀ t : ℂ) := by
      funext t
      exact hΨv t.1 t.2
    rw [this]
    exact UpperHalfPlane.continuous_coe.comp Ψ₀.continuous
  refine ⟨Ψ, fun t₀ ht₀ => ?_, ?_, fun t ht => ⟨?_, hΨφ t ht⟩⟩
  · -- local inverse of `φ` near `Ψ t₀`
    set w₀ : UpperHalfPlane := Ψ₀ ⟨t₀, ht₀⟩
    have hw₀s : w₀ ∈ modularPhiH ⁻¹' {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
      rw [Set.mem_preimage]
      have := congrFun hΨ₀ ⟨t₀, ht₀⟩
      simp only [Function.comp_apply] at this
      rw [this]
      exact hΦs t₀ ht₀
    obtain ⟨e, hw₀e, hfe⟩ := hcov.isLocalHomeomorphOn w₀ hw₀s
    set U : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' e.source with hUdef
    have hUo : IsOpen U := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ e.open_source
    have hUH : U ⊆ upperHalf := by
      rintro _ ⟨x, -, rfl⟩
      exact x.im_pos
    have hUinj : InjOn modularPhi U := by
      rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ h
      have h' : e x₁ = e x₂ := by
        have e1 : modularPhiH x₁ = e x₁ := congrFun hfe x₁
        have e2 : modularPhiH x₂ = e x₂ := congrFun hfe x₂
        rw [← e1, ← e2]
        exact h
      rw [e.injOn hx₁ hx₂ h']
    have hconf : IsConformalOnto modularPhi U (modularPhi '' U) :=
      ⟨mphi_differentiableOn_modularPhi_upperHalf.mono hUH, hUinj, rfl⟩
    have hΨt₀ : Ψ t₀ = (w₀ : ℂ) := hΨv t₀ ht₀
    have hΨt₀U : Ψ t₀ ∈ U := by rw [hΨt₀]; exact ⟨w₀, hw₀e, rfl⟩
    have hinv := hconf.differentiableAt_invFunOn hUo hΨt₀U
    rw [hΨφ t₀ ht₀] at hinv
    have hΦd : DifferentiableAt ℂ Φ t₀ := hΦ.differentiableAt (isOpen_ball.mem_nhds ht₀)
    have hev : Ψ =ᶠ[𝓝 t₀] fun t => Function.invFunOn modularPhi U (Φ t) := by
      have hnear : ∀ᶠ t in 𝓝 t₀, Ψ t ∈ U :=
        (hΨc.continuousAt (isOpen_ball.mem_nhds ht₀)).preimage_mem_nhds (hUo.mem_nhds hΨt₀U)
      filter_upwards [hnear, isOpen_ball.mem_nhds ht₀] with t htU htb
      rw [← hΨφ t htb, hUinj.leftInvOn_invFunOn htU]
    exact ((hinv.comp t₀ hΦd).congr_of_eventuallyEq hev).differentiableWithinAt
  · rw [hΨv 0 (mem_ball_self one_pos)]
    exact congrArg _ hΨ₀0
  · rw [hΨv t ht]
    exact (Ψ₀ ⟨t, ht⟩).im_pos

/-! #### M3. Schwarz–Pick for holomorphic maps `Δ → ℍ` -/

/-- For `a, p ∈ ℍ`: `|a - p| ≤ |a - p̄|`. -/
theorem td_norm_sub_le_norm_sub_conj {a p : ℂ} (ha : 0 < a.im) (hp : 0 < p.im) :
    ‖a - p‖ ≤ ‖a - conj p‖ := by
  have h1 : ‖a - p‖ ^ 2 = (a.re - p.re) ^ 2 + (a.im - p.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖a - conj p‖ ^ 2 = (a.re - p.re) ^ 2 + (a.im + p.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have : ‖a - p‖ ^ 2 ≤ ‖a - conj p‖ ^ 2 := by rw [h1, h2]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- Schwarz–Pick for holomorphic maps `Ψ : Δ → ℍ`: `d_ℍ(Ψ 0, Ψ s) ≤ ln((1+s)/(1-s))` for `0 ≤ s < 1`. -/
theorem td_schwarz_pick_H {Ψ : ℂ → ℂ} (hΨ : DifferentiableOn ℂ Ψ (ball 0 1))
    (hΨH : ∀ t ∈ ball (0 : ℂ) 1, 0 < (Ψ t).im) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    dist (UpperHalfPlane.mk (Ψ 0) (hΨH 0 (mem_ball_self one_pos)))
        (UpperHalfPlane.mk (Ψ s) (hΨH s (by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
          exact hs1))) ≤
      Real.log ((1 + s) / (1 - s)) := by
  set p := Ψ 0 with hp
  have hpH : 0 < p.im := hΨH 0 (mem_ball_self one_pos)
  have hsb : (s : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  have hden : ∀ t ∈ ball (0 : ℂ) 1, Ψ t - conj p ≠ 0 := by
    intro t ht h
    have := congrArg Complex.im h
    simp at this
    linarith [hΨH t ht]
  set g : ℂ → ℂ := fun t => (Ψ t - p) / (Ψ t - conj p) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (hΨ.sub_const p).div (hΨ.sub_const (conj p)) hden
  have hg0 : g 0 = 0 := by simp [hg, hp]
  have hgmaps : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro t ht
    rw [hg0, mem_closedBall_zero_iff, hg, norm_div]
    exact div_le_one_of_le₀ (td_norm_sub_le_norm_sub_conj (hΨH t ht) hpH) (norm_nonneg _)
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hgmaps hsb
  rw [hg0, dist_zero_right, dist_zero_right, div_one, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs0] at hsch
  -- `tanh (d/2) = ‖g s‖ ≤ s`
  set P := UpperHalfPlane.mk (Ψ 0) (hΨH 0 (mem_ball_self one_pos))
  set Q := UpperHalfPlane.mk (Ψ s) (hΨH s hsb)
  have htanh : Real.tanh (dist P Q / 2) = ‖g s‖ := by
    rw [UpperHalfPlane.tanh_half_dist]
    simp only [P, Q, hg, norm_div, dist_eq_norm]
    congr 1
    · rw [← hp, norm_sub_rev]
    · rw [← hp, ← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]
  have hle : Real.tanh (dist P Q / 2) ≤ s := htanh ▸ hsch
  have h2 : dist P Q / 2 ≤ Real.artanh s := by
    rw [← Real.artanh_tanh (dist P Q / 2)]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh _) hs1 hle
  rw [Real.artanh_eq_half_log ⟨by linarith, hs1.le⟩] at h2
  linarith

/-! #### M4. assembly, from the covering property of `φ` and `δ(φ a, φ b) ≤ d_ℍ(a, b)` -/

/-- Theorem 15.3 from the covering property of `φ` and `δ(φ a, φ b) ≤ d_ℍ(a, b)`: lift the holomorphic motion `t ↦ f_t(z)` through `φ`, apply Schwarz–Pick and let `s ↓ k = (K-1)/(K+1)`. -/
theorem td_thm15_3_of_motion
    (hcov : range modularPhiH = {z : ℂ | z ≠ 0 ∧ z ≠ 1} ∧
      IsCoveringMapOn modularPhiH {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    (hproj : ∀ a b : UpperHalfPlane,
      puncturedSphereDist (modularPhiH a) (modularPhiH b) ≤ ENNReal.ofReal (dist a b))
    {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    puncturedSphereDist z (f z) ≤ ENNReal.ofReal (Real.log K) := by
  have hK1 : 1 ≤ K := hf.1.2.1
  set k := (K - 1) / (K + 1) with hkdef
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : UpperHalfPlane, modularPhiH a₀ = z := by
    have : z ∈ range modularPhiH := by rw [hcov.1]; exact ⟨hz0, hz1⟩
    exact this
  -- for every `s ∈ (k, 1)`
  have hmain : ∀ s, k < s → s < 1 →
      puncturedSphereDist z (f z) ≤ ENNReal.ofReal (Real.log ((1 + s) / (1 - s))) := by
    intro s hks hs1
    have hs0 : 0 ≤ s := hk0.trans hks.le
    obtain ⟨Φ, hΦ, hΦ0, hΦs, hΦne⟩ := td_motion hf hz0 hz1 hks hs1
    obtain ⟨Ψ, hΨ, hΨ0, hΨH⟩ := td_lift_holomorphic hcov.2 hΦ hΦne (a₀ := a₀) (by rw [ha₀, hΦ0])
    have hsp := td_schwarz_pick_H hΨ (fun t ht => (hΨH t ht).1) hs0 hs1
    have hsb : (s : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact hs1
    have e1 : modularPhiH (UpperHalfPlane.mk (Ψ 0) ((hΨH 0 (mem_ball_self one_pos)).1)) = z := by
      show modularPhi (Ψ 0) = z
      rw [(hΨH 0 (mem_ball_self one_pos)).2, hΦ0]
    have e2 : modularPhiH (UpperHalfPlane.mk (Ψ s) ((hΨH s hsb).1)) = f z := by
      show modularPhi (Ψ s) = f z
      rw [(hΨH s hsb).2, hΦs]
    have h3 := hproj (UpperHalfPlane.mk (Ψ 0) ((hΨH 0 (mem_ball_self one_pos)).1))
      (UpperHalfPlane.mk (Ψ s) ((hΨH s hsb).1))
    rw [e1, e2] at h3
    exact h3.trans (ENNReal.ofReal_le_ofReal hsp)
  -- `s ↓ k`
  have hKk : (1 + k) / (1 - k) = K := by
    rw [hkdef]; field_simp; ring
  have hcont : ContinuousAt (fun s : ℝ => ENNReal.ofReal (Real.log ((1 + s) / (1 - s)))) k := by
    have hden : (1 - k) ≠ 0 := by linarith
    have hpos : (1 + k) / (1 - k) ≠ 0 := by rw [hKk]; linarith
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
        hden).log hpos)
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (Real.log ((1 + s) / (1 - s)))) (𝓝[>] k)
      (𝓝 (ENNReal.ofReal (Real.log K))) := by
    rw [← hKk]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hk1] with s hs
  exact hmain s hs.1 hs.2

/-- **Theorem 15.3** (Teichmüller).  If `f` is a `K`-q.c. map of `ℂ̄` fixing `0, 1, ∞`, then
`δ(z, f(z)) ≤ ln K` for every `z ≠ 0, 1, ∞`. -/
theorem thm15_3_teichmuller {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    puncturedSphereDist z (f z) ≤ ENNReal.ofReal (Real.log K) := by
  exact td_thm15_3_of_motion modularPhi_covering (fun a b => td_puncturedSphereDist_le_dist a b) hf hz0 hz1

/-- **Theorem 15.3** (sharpness): for `K ≥ 1` and `z₀, w₀ ∈ ℂ̄(0, 1, ∞)` with
`ln K = δ(z₀, w₀)` there is a `K`-q.c. map fixing `0, 1, ∞` with `f(z₀) = w₀`. -/
theorem thm15_3_sharp {K : ℝ} (hK : 1 ≤ K) {z₀ w₀ : ℂ} (hz₀ : z₀ ≠ 0 ∧ z₀ ≠ 1)
    (hw₀ : w₀ ≠ 0 ∧ w₀ ≠ 1) (hδ : ENNReal.ofReal (Real.log K) = puncturedSphereDist z₀ w₀) :
    ∃ f : ℂ → ℂ, IsKQCNormalizedPlane f K ∧ f z₀ = w₀ := by
  sorry

/-! ### tdist: the Poincaré density of `ℂ̄(0, 1, ∞)` and the maximum principle of Lemma 15.1 -/

/-! #### `td_Twice` -/

/-- `F : ℝ → ℝ` has second derivative `c` at `0`: `F` has derivatives `F'(t)` for `t` near `0`, and `F'` has derivative `c` at `0`. -/
def td_Twice (F : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ F' : ℝ → ℝ, (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt F (F' t) t) ∧ HasDerivAt F' c 0

/-- If `td_Twice F c` then `F''(0) = c`. -/
theorem td_twice_deriv2 {F : ℝ → ℝ} {c : ℝ} (h : td_Twice F c) : deriv (deriv F) 0 = c := by
  obtain ⟨F', hF, hF'⟩ := h
  have e : deriv F =ᶠ[𝓝 0] F' := hF.mono fun t ht => ht.deriv
  rw [e.deriv_eq]
  exact hF'.deriv

/-- Second derivatives at `0` of a difference. -/
theorem td_twice_sub {F G : ℝ → ℝ} {c e : ℝ} (hF : td_Twice F c) (hG : td_Twice G e) :
    td_Twice (fun t => F t - G t) (c - e) := by
  obtain ⟨F', hF1, hF2⟩ := hF
  obtain ⟨G', hG1, hG2⟩ := hG
  exact ⟨fun t => F' t - G' t, (hF1.and hG1).mono fun t ht => ht.1.sub ht.2, hF2.sub hG2⟩

/-- `td_Twice F c` only depends on the germ of `F` at `0`. -/
theorem td_twice_congr {F G : ℝ → ℝ} {c : ℝ} (h : td_Twice F c) (hFG : F =ᶠ[𝓝 0] G) :
    td_Twice G c := by
  obtain ⟨F', hF1, hF2⟩ := h
  refine ⟨F', ?_, hF2⟩
  filter_upwards [hF1, hFG.eventuallyEq_nhds] with t ht hte
  exact ht.congr_of_eventuallyEq hte.symm

/-- Second derivative at `0` of `log F` for `F(0) > 0`: `c/F(0) - (F'(0)/F(0))²`. -/
theorem td_twice_log {F : ℝ → ℝ} {c a : ℝ} (hF : td_Twice F c) (ha : HasDerivAt F a 0)
    (hpos : 0 < F 0) : td_Twice (fun t => Real.log (F t)) (c / F 0 - (a / F 0) ^ 2) := by
  obtain ⟨F', hF1, hF2⟩ := hF
  have hF'0 : F' 0 = a := (hF1.self_of_nhds).unique ha
  have hposev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < F t :=
    ha.continuousAt.eventually (lt_mem_nhds hpos)
  refine ⟨fun t => F' t / F t, ?_, ?_⟩
  · filter_upwards [hF1, hposev] with t ht hp
    exact ht.log hp.ne'
  · have h := hF2.div ha hpos.ne'
    convert h using 1
    rw [hF'0]
    field_simp

/-- The derivative of the line `t ↦ ζ₀ + t d`. -/
theorem td_hasDerivAt_line (ζ₀ d : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ζ₀ + (t : ℂ) * d) d t := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := (hasDerivAt_id (t : ℂ)).comp_ofReal
  simpa using (h.mul_const d).const_add ζ₀

/-- `ζ₀ + t d → ζ₀` as `t → 0`. -/
theorem td_tendsto_line (ζ₀ d : ℂ) :
    Tendsto (fun t : ℝ => ζ₀ + (t : ℂ) * d) (𝓝 0) (𝓝 ζ₀) := by
  have hc : Continuous (fun t : ℝ => ζ₀ + (t : ℂ) * d) := by fun_prop
  simpa using hc.tendsto 0

/-- Along a line, `Re M(ζ₀ + t d)` has first and second derivatives `Re(M'(ζ₀) d)` and `Re(M''(ζ₀) d²)` at `0` (`M` analytic at `ζ₀`). -/
theorem td_twice_re {M : ℂ → ℂ} {ζ₀ : ℂ} (hM : AnalyticAt ℂ M ζ₀) (d : ℂ) :
    td_Twice (fun t : ℝ => (M (ζ₀ + t * d)).re) ((deriv (deriv M) ζ₀ * d * d).re) ∧
      HasDerivAt (fun t : ℝ => (M (ζ₀ + t * d)).re) ((deriv M ζ₀ * d).re) 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), AnalyticAt ℂ M (ζ₀ + (t : ℂ) * d) :=
    (td_tendsto_line ζ₀ d).eventually hM.eventually_analyticAt
  have hre : ∀ {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}, HasDerivAt g g' t →
      HasDerivAt (fun s => (g s).re) g'.re t := fun h =>
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ h)
  have hd1 : ∀ t : ℝ, AnalyticAt ℂ M (ζ₀ + t * d) →
      HasDerivAt (fun s : ℝ => M (ζ₀ + s * d)) (deriv M (ζ₀ + t * d) * d) t := fun t ht =>
    ht.differentiableAt.hasDerivAt.comp t (td_hasDerivAt_line ζ₀ d t)
  have h0 : ζ₀ + ((0 : ℝ) : ℂ) * d = ζ₀ := by simp
  refine ⟨⟨fun t => (deriv M (ζ₀ + t * d) * d).re, ?_, ?_⟩, ?_⟩
  · filter_upwards [hev] with t ht
    exact hre (hd1 t ht)
  · have hMd : AnalyticAt ℂ (deriv M) (ζ₀ + ((0 : ℝ) : ℂ) * d) := by rw [h0]; exact hM.deriv
    have h2 := (hMd.differentiableAt.hasDerivAt.comp (0 : ℝ) (td_hasDerivAt_line ζ₀ d 0)).mul_const d
    rw [h0] at h2
    exact hre h2
  · have h1 := hd1 0 (by rw [h0]; exact hM)
    rw [h0] at h1
    exact hre h1

/-- **Curvature identity** in axis form: for `ψ` analytic with `ψ' ≠ 0` and `Im ψ > 0`, the second derivatives of `ln(|ψ'|/Im ψ)` along a unit direction `d` and along `i d` add up to `(|ψ'|/Im ψ)²` (the Poincaré metric has curvature `-1`). -/
theorem td_curvature {ψ : ℂ → ℂ} {ζ₀ d : ℂ} (hψ : AnalyticAt ℂ ψ ζ₀) (hψ' : deriv ψ ζ₀ ≠ 0)
    (him : 0 < (ψ ζ₀).im) (hd : ‖d‖ = 1) :
    ∃ c₁ c₂ : ℝ,
      td_Twice (fun t : ℝ => Real.log (‖deriv ψ (ζ₀ + t * d)‖ / (ψ (ζ₀ + t * d)).im)) c₁ ∧
      td_Twice (fun t : ℝ => Real.log (‖deriv ψ (ζ₀ + t * (I * d))‖ /
        (ψ (ζ₀ + t * (I * d))).im)) c₂ ∧
      c₁ + c₂ = (‖deriv ψ ζ₀‖ / (ψ ζ₀).im) ^ 2 := by
  set g : ℂ → ℂ := deriv ψ with hgdef
  have hg : AnalyticAt ℂ g ζ₀ := hψ.deriv
  have hgn : 0 < ‖g ζ₀‖ := norm_pos_iff.2 hψ'
  set u : ℂ := conj (g ζ₀) / (‖g ζ₀‖ : ℂ) with hudef
  have hug : u * g ζ₀ = (‖g ζ₀‖ : ℂ) := by
    rw [hudef, div_mul_eq_mul_div, mul_comm (conj (g ζ₀)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : (‖g ζ₀‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 hgn.ne'
    field_simp
    push_cast
    ring
  have hun : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hgn.le,
      div_self hgn.ne']
  set L : ℂ → ℂ := fun ζ => Complex.log (u * g ζ) with hLdef
  have hL : AnalyticAt ℂ L ζ₀ := by
    have hslit : u * g ζ₀ ∈ slitPlane := by
      rw [hug]; exact ofReal_mem_slitPlane.2 hgn
    exact (analyticAt_const.mul hg).clog hslit
  have hlogg : ∀ ζ, Real.log ‖g ζ‖ = (L ζ).re := by
    intro ζ
    rw [hLdef, Complex.log_re, norm_mul, hun, one_mul]
  set M : ℂ → ℂ := fun ζ => -I * ψ ζ with hMdef
  have hM : AnalyticAt ℂ M ζ₀ := analyticAt_const.mul hψ
  have hMre : ∀ ζ, (M ζ).re = (ψ ζ).im := by
    intro ζ; simp [hMdef]
  have hM' : deriv M ζ₀ = -I * g ζ₀ := by
    rw [hMdef, deriv_const_mul _ hψ.differentiableAt]
  have piece : ∀ e : ℂ, td_Twice
      (fun t : ℝ => Real.log (‖g (ζ₀ + t * e)‖ / (ψ (ζ₀ + t * e)).im))
      ((deriv (deriv L) ζ₀ * e * e).re -
        ((deriv (deriv M) ζ₀ * e * e).re / (ψ ζ₀).im - ((deriv M ζ₀ * e).re / (ψ ζ₀).im) ^ 2)) := by
    intro e
    obtain ⟨hL2, -⟩ := td_twice_re hL e
    obtain ⟨hM2, hM1⟩ := td_twice_re hM e
    have h0 : ζ₀ + ((0 : ℝ) : ℂ) * e = ζ₀ := by simp
    have hMpos : 0 < (fun t : ℝ => (M (ζ₀ + t * e)).re) 0 := by
      simp only [h0, hMre]; exact him
    have hlogM := td_twice_log hM2 hM1 hMpos
    simp only [h0, hMre] at hlogM
    refine td_twice_congr (td_twice_sub hL2 hlogM) ?_
    have hgev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g (ζ₀ + (t : ℂ) * e) ≠ 0 :=
      (td_tendsto_line ζ₀ e).eventually (hg.continuousAt.eventually_ne hψ')
    have himev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), 0 < (ψ (ζ₀ + (t : ℂ) * e)).im :=
      (td_tendsto_line ζ₀ e).eventually
        ((Complex.continuous_im.continuousAt.comp hψ.continuousAt).eventually (lt_mem_nhds him))
    filter_upwards [hgev, himev] with t h1 h2
    rw [Real.log_div (norm_ne_zero_iff.2 h1) h2.ne', hlogg]
  refine ⟨_, _, piece d, piece (I * d), ?_⟩
  have hV : (ψ ζ₀).im ≠ 0 := him.ne'
  have hsq : ‖deriv M ζ₀ * d‖ ^ 2 = (deriv M ζ₀ * d).re ^ 2 + (deriv M ζ₀ * d).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnorm : ‖deriv M ζ₀ * d‖ = ‖g ζ₀‖ := by
    rw [norm_mul, hd, mul_one, hM', norm_mul, norm_neg, Complex.norm_I, one_mul]
  have e1 : ∀ X : ℂ, (X * (I * d) * (I * d)).re = -(X * d * d).re := by
    intro X
    have : X * (I * d) * (I * d) = -(X * d * d) := by
      linear_combination (X * d * d) * I_sq
    rw [this, Complex.neg_re]
  have e2 : (deriv M ζ₀ * (I * d)).re = -(deriv M ζ₀ * d).im := by
    rw [show deriv M ζ₀ * (I * d) = I * (deriv M ζ₀ * d) by ring, Complex.mul_re]
    simp
  rw [e1, e1, e2, ← hnorm, div_pow ‖deriv M ζ₀ * d‖, hsq]
  field_simp
  ring

/-! #### Second-derivative test -/

/-- At a local minimum of `f : ℝ → ℝ` (continuous there) the second derivative is nonnegative. -/
theorem td_deriv2_nonneg_of_isLocalMin {f : ℝ → ℝ} {x₀ : ℝ} (hmin : IsLocalMin f x₀)
    (hc : ContinuousAt f x₀) : 0 ≤ deriv (deriv f) x₀ := by
  by_contra hneg
  push Not at hneg
  have hmax : IsLocalMax f x₀ := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have hconst : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmin, hmax] with x h1 h2
    exact le_antisymm h2 h1
  have hd : deriv f =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventuallyEq_nhds] with x hx
    rw [hx.deriv_eq, deriv_const]
  rw [hd.deriv_eq, deriv_const] at hneg
  exact lt_irrefl _ hneg

/-- At a local minimum of `h : ℂ → ℝ` (continuous there) the second derivative of `h` along every line is nonnegative. -/
theorem td_line_isLocalMin {h : ℂ → ℝ} {z₀ : ℂ} (hmin : IsLocalMin h z₀) (hc : ContinuousAt h z₀)
    (v : ℂ) : 0 ≤ deriv (deriv fun t : ℝ => h (z₀ + t * v)) 0 := by
  set g : ℝ → ℂ := fun t => z₀ + (t : ℂ) * v with hg
  have hl : Continuous g := by rw [hg]; fun_prop
  have e : g 0 = z₀ := by simp [hg]
  have hmin' : IsLocalMin h (g 0) := by rw [e]; exact hmin
  have hc' : ContinuousAt h (g 0) := by rw [e]; exact hc
  exact td_deriv2_nonneg_of_isLocalMin (hmin'.comp_continuous hl.continuousAt)
    (hc'.comp hl.continuousAt)

/-! #### Regularity of `η` from the analytic local inverse -/

/-- `φ` is analytic at every point of `ℍ`. -/
theorem td_analyticAt_modularPhi {w₀ : ℂ} (hw₀ : 0 < w₀.im) : AnalyticAt ℂ modularPhi w₀ :=
  mphi_differentiableOn_modularPhi_upperHalf.analyticAt (isOpen_upperHalf.mem_nhds hw₀)

/-- Near `φ(w₀)` with `φ'(w₀) ≠ 0` the local inverse `ψ` of `φ` is analytic, `ψ(φ(w₀)) = w₀`, and `η = |ψ'|/Im ψ` there ((14.6)). -/
theorem td_eta_local {w₀ : ℂ} (hw₀ : 0 < w₀.im) (hd : deriv modularPhi w₀ ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (modularPhi w₀) ∧ ψ (modularPhi w₀) = w₀ ∧
      deriv ψ (modularPhi w₀) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (modularPhi w₀), 0 < (ψ z).im ∧
        puncturedSphereDensity z = ‖deriv ψ z‖ / (ψ z).im := by
  have hφa := td_analyticAt_modularPhi hw₀
  set ψ := hφa.hasStrictDerivAt.localInverse _ _ _ hd with hψdef
  have hψa : AnalyticAt ℂ ψ (modularPhi w₀) := hφa.analyticAt_localInverse hd
  have hψw₀ : ψ (modularPhi w₀) = w₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hright : ∀ᶠ z in 𝓝 (modularPhi w₀), modularPhi (ψ z) = z :=
    HasStrictDerivAt.eventually_right_inverse ..
  have hψd : HasStrictDerivAt ψ (deriv modularPhi w₀)⁻¹ (modularPhi w₀) :=
    HasStrictDerivAt.to_localInverse ..
  refine ⟨ψ, hψa, hψw₀, ?_, ?_⟩
  · rw [hψd.hasDerivAt.deriv]
    exact inv_ne_zero hd
  have him : ∀ᶠ z in 𝓝 (modularPhi w₀), 0 < (ψ z).im := by
    have hc : ContinuousAt (fun z => (ψ z).im) (modularPhi w₀) :=
      Complex.continuous_im.continuousAt.comp hψa.continuousAt
    exact hc.eventually (lt_mem_nhds (by show 0 < (ψ (modularPhi w₀)).im; rw [hψw₀]; exact hw₀))
  filter_upwards [him, hψa.eventually_analyticAt, hright.eventually_nhds, hright] with z hz hza hzr hz1
  refine ⟨hz, ?_⟩
  have hφz : AnalyticAt ℂ modularPhi (ψ z) := td_analyticAt_modularPhi hz
  have hcomp : HasDerivAt (fun y => modularPhi (ψ y)) (deriv modularPhi (ψ z) * deriv ψ z) z :=
    hφz.differentiableAt.hasDerivAt.comp z hza.differentiableAt.hasDerivAt
  have hid : HasDerivAt (fun y => modularPhi (ψ y)) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq hzr
  have hprod : deriv modularPhi (ψ z) * deriv ψ z = 1 := hcomp.unique hid
  have hψ' : deriv ψ z = (deriv modularPhi (ψ z))⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hη := (eq14_6_well_defined hz hz rfl).2
  rw [hz1] at hη
  rw [hη, hψ', norm_inv]
  field_simp

/-- `φ' ≠ 0` on `ℍ` (`φ` is a covering, hence locally injective). -/
theorem td_deriv_ne_zero_of_covering {w₀ : ℂ} (hw₀ : 0 < w₀.im) : deriv modularPhi w₀ ≠ 0 := by
  obtain ⟨hrange, hcov⟩ := modularPhi_covering
  set τ : UpperHalfPlane := ⟨w₀, hw₀⟩ with hτ
  have hτS : modularPhiH τ ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := hrange ▸ mem_range_self τ
  obtain ⟨e, hτe, he⟩ := hcov.isLocalHomeomorphOn τ hτS
  set U : Set ℂ := (↑) '' e.source with hU
  have hUo : IsOpen U := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ e.open_source
  have hUH : U ⊆ upperHalf := by
    rintro _ ⟨σ, -, rfl⟩
    exact σ.im_pos
  have hinj : InjOn modularPhi U := by
    rintro _ ⟨σ₁, h₁, rfl⟩ _ ⟨σ₂, h₂, rfl⟩ h
    have h' : e σ₁ = e σ₂ := by
      have e₁ : modularPhiH σ₁ = e σ₁ := by rw [he]
      have e₂ : modularPhiH σ₂ = e σ₂ := by rw [he]
      rw [← e₁, ← e₂]
      exact h
    exact congrArg _ (e.injOn h₁ h₂ h')
  exact deriv_ne_zero_of_injOn hUo (mphi_differentiableOn_modularPhi_upperHalf.mono hUH) hinj
    ⟨τ, hτe, rfl⟩

/-- Regularity at every point of `ℂ ∖ {0, 1}`. -/
theorem td_eta_regular {z₀ : ℂ} (h0 : z₀ ≠ 0) (h1 : z₀ ≠ 1) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ deriv ψ z₀ ≠ 0 ∧ 0 < (ψ z₀).im ∧
      puncturedSphereDensity z₀ = ‖deriv ψ z₀‖ / (ψ z₀).im ∧
      ∀ᶠ z in 𝓝 z₀, puncturedSphereDensity z = ‖deriv ψ z‖ / (ψ z).im := by
  obtain ⟨hrange, -⟩ := modularPhi_covering
  have hz₀ : z₀ ∈ range modularPhiH := hrange ▸ ⟨h0, h1⟩
  obtain ⟨τ, hτ⟩ := hz₀
  have hw : modularPhi (τ : ℂ) = z₀ := hτ
  obtain ⟨ψ, hψa, hψw, hψd, hev⟩ := td_eta_local τ.im_pos (td_deriv_ne_zero_of_covering τ.im_pos)
  rw [hw] at hψa hψw hψd hev
  refine ⟨ψ, hψa, hψd, by rw [hψw]; exact τ.im_pos, (hev.self_of_nhds).2, hev.mono fun z hz => hz.2⟩

/-- `η > 0` on `ℂ ∖ {0, 1}`. -/
theorem td_eta_pos {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) : 0 < puncturedSphereDensity z := by
  obtain ⟨ψ, -, hψd, him, heq, -⟩ := td_eta_regular h0 h1
  rw [heq]
  exact div_pos (norm_pos_iff.2 hψd) him

/-- `η` is continuous on `ℂ ∖ {0, 1}`. -/
theorem td_eta_continuousAt {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    ContinuousAt puncturedSphereDensity z := by
  obtain ⟨ψ, hψa, -, him, -, hev⟩ := td_eta_regular h0 h1
  have hc : ContinuousAt (fun y => ‖deriv ψ y‖ / (ψ y).im) z :=
    (hψa.deriv.continuousAt.norm).div (Complex.continuous_im.continuousAt.comp hψa.continuousAt)
      him.ne'
  exact hc.congr (hev.mono fun y hy => hy.symm)

/-- (b) for `η`: the curvature identity at every point of `ℂ ∖ {0, 1}`. -/
theorem td_eta_curv {z₀ : ℂ} (h0 : z₀ ≠ 0) (h1 : z₀ ≠ 1) {d : ℂ} (hd : ‖d‖ = 1) :
    ∃ c₁ c₂ : ℝ, td_Twice (fun t : ℝ => Real.log (puncturedSphereDensity (z₀ + t * d))) c₁ ∧
      td_Twice (fun t : ℝ => Real.log (puncturedSphereDensity (z₀ + t * (I * d)))) c₂ ∧
      c₁ + c₂ = puncturedSphereDensity z₀ ^ 2 := by
  obtain ⟨ψ, hψa, hψd, him, heq, hev⟩ := td_eta_regular h0 h1
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := td_curvature hψa hψd him hd
  refine ⟨c₁, c₂, td_twice_congr hc₁ ?_, td_twice_congr hc₂ ?_, by rw [hsum, heq]⟩
  · filter_upwards [(td_tendsto_line z₀ d).eventually hev] with t ht
    rw [ht]
  · filter_upwards [(td_tendsto_line z₀ (I * d)).eventually hev] with t ht
    rw [ht]

/-! #### Conjugation symmetry and the strip limit -/

/-- `℘` of the conjugate lattice: `℘(z̄; L') = conj ℘(z; L)` when `L' = conj L`. -/
theorem td_conj_weierstrassP (L L' : PeriodPair)
    (h : ∀ x : ℂ, x ∈ L'.lattice ↔ conj x ∈ L.lattice) (z : ℂ) :
    L'.weierstrassP (conj z) = conj (L.weierstrassP z) := by
  let e : L.lattice ≃ L'.lattice :=
    ⟨fun l => ⟨conj (l : ℂ), (h _).2 (by simp)⟩,
      fun l' => ⟨conj (l' : ℂ), (h _).1 l'.2⟩,
      fun l => Subtype.ext (by simp), fun l' => Subtype.ext (by simp)⟩
  simp only [PeriodPair.weierstrassP]
  rw [Complex.conj_tsum, ← e.tsum_eq]
  refine tsum_congr fun l => ?_
  simp [e, map_sub, map_pow]

/-- Reflection symmetry of the modular function: `φ(-w̄) = conj φ(w)`. -/
theorem td_modularPhi_neg_conj {w : ℂ} (hw : 0 < w.im) :
    modularPhi (-conj w) = conj (modularPhi w) := by
  have hw' : 0 < (-conj w).im := by simpa using hw
  set L := periodPairOf w hw
  set L' := periodPairOf (-conj w) hw'
  have hlat : ∀ x : ℂ, x ∈ L'.lattice ↔ conj x ∈ L.lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, L, L', periodPairOf]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, -n, by simp⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨m, -n, ?_⟩
      have := congrArg conj hmn
      simp only [map_add, map_mul, map_intCast, map_one, Complex.conj_conj] at this
      rw [← this]
      push_cast
      ring
  have hc := td_conj_weierstrassP L L' hlat
  have hω : (-conj w : ℂ) ∈ L'.lattice := L'.ω₂_mem_lattice
  have e0 : weierstrassE (-conj w) 0 = conj (weierstrassE w 0) := by
    rw [weierstrassE_zero_eq hw', weierstrassE_zero_eq hw, ← hc]
    congr 1
    simp [map_ofNat]
  have e1 : weierstrassE (-conj w) 1 = conj (weierstrassE w 1) := by
    rw [weierstrassE_one_eq hw', weierstrassE_one_eq hw, ← hc,
      show -conj w / 2 = -(conj (w / 2)) by simp [map_div₀, map_ofNat]; ring, PeriodPair.weierstrassP_neg]
  have e2 : weierstrassE (-conj w) 2 = conj (weierstrassE w 2) := by
    rw [weierstrassE_two_eq hw', weierstrassE_two_eq hw, ← hc,
      show (1 + -conj w) / 2 = conj ((1 + w) / 2) + (-conj w) by simp [map_div₀, map_ofNat]; ring]
    exact L'.weierstrassP_add_coe _ ⟨_, hω⟩
  simp only [modularPhi, e0, e1, e2, ← map_sub, ← map_div₀]

/-- `|φ'(-w̄)| = |φ'(w)|`. -/
theorem td_norm_deriv_modularPhi_neg_conj {w : ℂ} (hw : 0 < w.im) :
    ‖deriv modularPhi (-conj w)‖ = ‖deriv modularPhi w‖ := by
  have hw' : 0 < (-conj w).im := by simpa using hw
  have hd : DifferentiableAt ℂ modularPhi (-conj w) :=
    mphi_differentiableOn_modularPhi_upperHalf.differentiableAt (isOpen_upperHalf.mem_nhds hw')
  have hf : HasDerivAt (fun u => modularPhi (-u)) (-deriv modularPhi (-conj w)) (conj w) := by
    have h1 := hd.hasDerivAt.comp (conj w) (hasDerivAt_neg (conj w))
    convert h1 using 1
    · rfl
    · ring
  have hG := hf.conj_conj
  rw [Complex.conj_conj] at hG
  have heq : (conj ∘ (fun u => modularPhi (-u)) ∘ conj) =ᶠ[𝓝 w] modularPhi := by
    filter_upwards [isOpen_upperHalf.mem_nhds hw] with v hv
    simp only [Function.comp_apply]
    rw [td_modularPhi_neg_conj hv, Complex.conj_conj]
  have hφ : HasDerivAt modularPhi (conj (-deriv modularPhi (-conj w))) w :=
    hG.congr_of_eventuallyEq heq.symm
  rw [hφ.deriv, Complex.norm_conj, norm_neg]

/-- `η(z̄) = η(z)`. -/
theorem td_eta_conj (z : ℂ) : puncturedSphereDensity (conj z) = puncturedSphereDensity z := by
  unfold puncturedSphereDensity
  congr 1
  ext r
  constructor
  · rintro ⟨w, hw, hφ, rfl⟩
    have hw' : 0 < (-conj w).im := by simpa using hw
    refine ⟨-conj w, hw', ?_, ?_⟩
    · rw [td_modularPhi_neg_conj hw, hφ, Complex.conj_conj]
    · rw [td_norm_deriv_modularPhi_neg_conj hw]
      simp
  · rintro ⟨w, hw, hφ, rfl⟩
    have hw' : 0 < (-conj w).im := by simpa using hw
    refine ⟨-conj w, hw', ?_, ?_⟩
    · rw [td_modularPhi_neg_conj hw, hφ]
    · rw [td_norm_deriv_modularPhi_neg_conj hw]
      simp

/-- The cusp at `∞`: in the strip `0 ≤ Re w ≤ 1`, `|φ(w)| ln|φ(w)| / (|φ'(w)| Im w) → 1` as `Im w → ∞`. -/
theorem td_cusp_w :
    Tendsto (fun w => ‖modularPhi w‖ * Real.log ‖modularPhi w‖ / (‖deriv modularPhi w‖ * w.im))
      (comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 1) := by
  set F := comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} with hF
  have hq := mphi_modularPhi_mul_q_tendsto_strip
  have hD := mphi_deriv_modularPhi_div_tendsto_strip
  have him : Tendsto Complex.im F atTop := tendsto_comap.mono_left inf_le_left
  have hq' : Tendsto (fun w => ‖modularPhi w * cexp (π * I * w)‖) F (𝓝 (1 / 16)) := by
    have := hq.norm
    rwa [show ‖(-1 / 16 : ℂ)‖ = 1 / 16 by norm_num] at this
  have hφ0 : ∀ᶠ w in F, modularPhi w ≠ 0 := by
    filter_upwards [hq'.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with w hw h0
    rw [h0, zero_mul, norm_zero] at hw
    exact lt_irrefl 0 hw
  have hpos : ∀ᶠ w in F, 0 < w.im := him.eventually (eventually_gt_atTop 0)
  have hD' : Tendsto (fun w => ‖deriv modularPhi w‖ / ‖modularPhi w‖) F (𝓝 π) := by
    have := hD.norm
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] at this
    refine this.congr' ?_
    filter_upwards with w
    rw [norm_div]
  have hL : Tendsto (fun w => Real.log ‖modularPhi w‖ / w.im) F (𝓝 π) := by
    have h1 : Tendsto (fun w => Real.log ‖modularPhi w * cexp (π * I * w)‖) F
        (𝓝 (Real.log (1 / 16))) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp hq'
    have h2 : Tendsto (fun w => Real.log ‖modularPhi w * cexp (π * I * w)‖ / w.im + π) F
        (𝓝 (0 + π)) :=
      (h1.div_atTop him).add tendsto_const_nhds
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [hφ0, hpos] with w hw0 hwim
    have hexp : ‖cexp (π * I * w)‖ = Real.exp (-(π * w.im)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hw0) (by rw [hexp]; exact (Real.exp_pos _).ne'),
      hexp, Real.log_exp]
    field_simp
    ring
  have hprod := (hD'.inv₀ Real.pi_pos.ne').mul hL
  rw [inv_mul_cancel₀ Real.pi_pos.ne'] at hprod
  refine hprod.congr' ?_
  filter_upwards [hφ0, hpos] with w hw0 hwim
  rw [inv_div]
  field_simp

/-- The same in terms of `η`: `η(φ(w)) |φ(w)| ln|φ(w)| → 1` as `Im w → ∞` in the strip. -/
theorem td_cusp_eta_w :
    Tendsto (fun w => puncturedSphereDensity (modularPhi w) *
        (‖modularPhi w‖ * Real.log ‖modularPhi w‖))
      (comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 1) := by
  have him : Tendsto Complex.im (comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1})
      atTop := tendsto_comap.mono_left inf_le_left
  refine td_cusp_w.congr' ?_
  filter_upwards [him.eventually (eventually_gt_atTop 0)] with w hw
  rw [(eq14_6_well_defined hw hw rfl).2]
  field_simp

/-! #### `η(1 - z) = η(z)` -/

/-- `φ'(v + 1) = -φ'(v)` (from `φ(w+1) = 1 - φ(w)`, (14.11)). -/
theorem td_deriv_modularPhi_add_one {v : ℂ} (hv : 0 < v.im) :
    deriv modularPhi (v + 1) = -deriv modularPhi v := by
  have heq : (fun u => modularPhi (u + 1)) =ᶠ[𝓝 v] (fun u => 1 - modularPhi u) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hv] with u hu
    exact eq14_11 hu
  have h1 : deriv (fun u => modularPhi (u + 1)) v = deriv modularPhi (v + 1) :=
    deriv_comp_add_const ..
  rw [← h1, heq.deriv_eq, deriv_const_sub]

/-- `η(1 - z) = η(z)`. -/
theorem td_eta_one_sub (z : ℂ) : puncturedSphereDensity (1 - z) = puncturedSphereDensity z := by
  unfold puncturedSphereDensity
  congr 1
  ext r
  constructor
  · rintro ⟨w, hw, hφ, rfl⟩
    have hw' : 0 < (w - 1).im := by simpa using hw
    have e1 := eq14_11 hw'
    have e2 := td_deriv_modularPhi_add_one hw'
    rw [sub_add_cancel] at e1 e2
    refine ⟨w - 1, hw', by linear_combination e1 - hφ, ?_⟩
    rw [e2, norm_neg, show (w - 1).im = w.im by simp]
  · rintro ⟨w, hw, hφ, rfl⟩
    have hw' : 0 < (w + 1).im := by simpa using hw
    refine ⟨w + 1, hw', by rw [eq14_11 hw, hφ], ?_⟩
    rw [td_deriv_modularPhi_add_one hw, norm_neg, show (w + 1).im = w.im by simp]

/-! #### `η(z⁻¹) = |z|² η(z)` -/

/-- `φ ≠ 0` on `ℍ`. -/
theorem td_modularPhi_ne_zero {w : ℂ} (hw : 0 < w.im) : modularPhi w ≠ 0 := by
  obtain ⟨-, h02, h12⟩ := mphi_weierstrassE_pairwise_ne hw
  exact div_ne_zero (sub_ne_zero.2 (Ne.symm h02)) (sub_ne_zero.2 (Ne.symm h12))

/-- `w ↦ -1/w` preserves `ℍ`. -/
theorem td_im_neg_inv_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-1 / w).im := by
  rw [mphi_im_neg_one_div]
  have : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  exact div_pos hw this

/-- `|φ'(-1/w)| Im(-1/w) = |φ'(w)| Im w / |φ(w)|²`. -/
theorem td_norm_deriv_mul_im_neg_inv {w : ℂ} (hw : 0 < w.im) :
    ‖deriv modularPhi (-1 / w)‖ * (-1 / w).im =
      ‖deriv modularPhi w‖ * w.im / ‖modularPhi w‖ ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  have hw' := td_im_neg_inv_pos hw
  have hφ0 := td_modularPhi_ne_zero hw
  have hd : DifferentiableAt ℂ modularPhi (-1 / w) :=
    mphi_differentiableOn_modularPhi_upperHalf.differentiableAt (isOpen_upperHalf.mem_nhds hw')
  have hdw : DifferentiableAt ℂ modularPhi w :=
    mphi_differentiableOn_modularPhi_upperHalf.differentiableAt (isOpen_upperHalf.mem_nhds hw)
  -- `u ↦ -1/u` has derivative `1/w²`
  have hg : HasDerivAt (fun u : ℂ => -1 / u) (1 / w ^ 2) w := by
    have h := (hasDerivAt_inv hw0).neg
    convert h using 1
    · funext u; simp [neg_div, one_div]
    · simp [one_div]
  have h1 : HasDerivAt (fun u => modularPhi (-1 / u)) (deriv modularPhi (-1 / w) * (1 / w ^ 2)) w :=
    hd.hasDerivAt.comp w hg
  have h2 : HasDerivAt (fun u => 1 / modularPhi u) (-deriv modularPhi w / modularPhi w ^ 2) w := by
    have h := hdw.hasDerivAt.inv hφ0
    convert h using 1
    · funext u; simp [one_div]
  have heq : (fun u => modularPhi (-1 / u)) =ᶠ[𝓝 w] (fun u => 1 / modularPhi u) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hw] with u hu
    exact eq14_12 hu
  have hrel : deriv modularPhi (-1 / w) * (1 / w ^ 2) = -deriv modularPhi w / modularPhi w ^ 2 :=
    (h1.congr_of_eventuallyEq heq.symm).unique h2 |>.symm ▸ rfl
  have hnorm : ‖deriv modularPhi (-1 / w)‖ = ‖w‖ ^ 2 * ‖deriv modularPhi w‖ / ‖modularPhi w‖ ^ 2 := by
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    have : deriv modularPhi (-1 / w) = -deriv modularPhi w / modularPhi w ^ 2 * w ^ 2 := by
      rw [← hrel]; field_simp
    rw [this, norm_mul, norm_div, norm_neg, norm_pow, norm_pow]
    ring
  have him : (-1 / w).im = w.im / ‖w‖ ^ 2 := by
    rw [mphi_im_neg_one_div, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring_nf
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rw [hnorm, him]
  field_simp

/-- `η(1/z) = |z|² η(z)` (from `φ(-1/w) = 1/φ(w)`, (14.12)). -/
theorem td_eta_inv (z : ℂ) : puncturedSphereDensity z⁻¹ = ‖z‖ ^ 2 * puncturedSphereDensity z := by
  by_cases hz : z = 0
  · subst hz
    simp only [inv_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    unfold puncturedSphereDensity
    convert Real.sSup_empty
    ext r
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, hφ, -⟩
    exact td_modularPhi_ne_zero hw hφ
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold puncturedSphereDensity
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg (by positivity)]
  congr 1
  ext r
  constructor
  · rintro ⟨w, hw, hφ, rfl⟩
    -- `φ(w) = z⁻¹` ⇒ `φ(-1/w) = z`
    have hw' := td_im_neg_inv_pos hw
    refine ⟨1 / (‖deriv modularPhi (-1 / w)‖ * (-1 / w).im), ⟨-1 / w, hw', ?_, rfl⟩, ?_⟩
    · rw [eq14_12 hw, hφ, one_div, inv_inv]
    · dsimp only
      rw [td_norm_deriv_mul_im_neg_inv hw, hφ, norm_inv, smul_eq_mul, one_div_div]
      have key : ‖z‖ ^ 2 * (‖z‖⁻¹) ^ 2 = 1 := by field_simp
      calc ‖z‖ ^ 2 * ((‖z‖⁻¹) ^ 2 / (‖deriv modularPhi w‖ * w.im))
          = (‖z‖ ^ 2 * (‖z‖⁻¹) ^ 2) / (‖deriv modularPhi w‖ * w.im) := by ring
        _ = 1 / (‖deriv modularPhi w‖ * w.im) := by rw [key]
  · rintro ⟨r', ⟨w, hw, hφ, rfl⟩, rfl⟩
    have hw' := td_im_neg_inv_pos hw
    refine ⟨-1 / w, hw', by rw [eq14_12 hw, hφ, one_div], ?_⟩
    dsimp only
    rw [td_norm_deriv_mul_im_neg_inv hw, hφ, smul_eq_mul, one_div_div]
    ring


/-! #### Preimages high in the strip -/

/-- `φ(i Λ(ρ)) = -ρ` (14.19). -/
theorem td_modularPhi_iLambda {ρ : ℝ} (hρ : 0 < ρ) :
    modularPhi ((quadLambda ρ : ℂ) * I) = -(ρ : ℂ) := by
  have hv : 0 < quadLambda ρ := b4_num_quadLambda_pos hρ
  have h19 := eq14_19 hv
  rw [lambdaInv_quadLambda hρ] at h19
  have him0 : (modularPhi ((quadLambda ρ : ℂ) * I)).im = 0 :=
    mphi_modularPhi_im_eq_zero_of_side (by simpa using hv) (Or.inl (by simp))
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  · rw [him0]; simp

/-- Points of large modulus in the closed upper half-plane have `φ`-preimages high in the strip `0 ≤ Re w ≤ 1`. -/
theorem td_preimage_high (T : ℝ) : ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.im → R < ‖z‖ →
    ∃ w : ℂ, 0 < w.im ∧ modularPhi w = z ∧ 0 ≤ w.re ∧ w.re ≤ 1 ∧ T < w.im := by
  obtain ⟨hconf, hc0, hc1, -⟩ := eq14_20_modularPhi_conformal
  have hcont : ContinuousOn modularPhi upperHalf :=
    mphi_differentiableOn_modularPhi_upperHalf.continuousOn
  obtain ⟨M, hM⟩ := mphi_w4_bounded_low hcont hc0 hc1 T
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ∀ ρ, ρ₀ ≤ ρ → max T 0 < quadLambda ρ :=
    eventually_atTop.1 (quadLambda_strictMono.2.2.eventually (eventually_gt_atTop (max T 0)))
  refine ⟨max M (max (|ρ₀| + 1) 2), fun z hz hzR => ?_⟩
  have hRM : M < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hzR
  have hR2 : 2 < ‖z‖ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hzR
  have hRρ : |ρ₀| + 1 < ‖z‖ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hzR
  rcases hz.lt_or_eq with hz | hz
  · -- `Im z > 0`: a preimage in `A`
    have hzH : z ∈ upperHalf := hz
    rw [← hconf.2.2] at hzH
    obtain ⟨w, hwA, rfl⟩ := hzH
    refine ⟨w, hwA.2.2.2, rfl, hwA.1.le, hwA.2.1.le, ?_⟩
    by_contra hle
    push Not at hle
    linarith [hM w hwA hle]
  · -- `z` real, `|z| > 2`
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz.symm])
    have hnorm : ‖z‖ = |z.re| := by
      conv_lhs => rw [hzr]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hR2 hRρ
    rcases le_or_gt z.re 0 with hneg | hpos
    · -- `z < -2`: `w = i Λ(-z)`
      rw [abs_of_nonpos hneg] at hR2 hRρ
      have hρ : 0 < -z.re := by linarith
      have hΛ := hρ₀ (-z.re) (by linarith [le_abs_self ρ₀])
      refine ⟨(quadLambda (-z.re) : ℂ) * I, by simpa using lt_of_le_of_lt (le_max_right _ _) hΛ,
        ?_, by simp, by simp, by simpa using lt_of_le_of_lt (le_max_left _ _) hΛ⟩
      rw [td_modularPhi_iLambda hρ]
      conv_rhs => rw [hzr]
      push_cast
      ring
    · -- `z > 2`: `w = 1 + i Λ(z - 1)`
      rw [abs_of_pos hpos] at hR2 hRρ
      have hρ : 0 < z.re - 1 := by linarith
      have hΛ := hρ₀ (z.re - 1) (by linarith [le_abs_self ρ₀])
      have hv : 0 < quadLambda (z.re - 1) := lt_of_le_of_lt (le_max_right _ _) hΛ
      have hvI : 0 < ((quadLambda (z.re - 1) : ℂ) * I).im := by simpa using hv
      refine ⟨(quadLambda (z.re - 1) : ℂ) * I + 1, by simpa using hv, ?_, by simp, by simp,
        by simpa using lt_of_le_of_lt (le_max_left _ _) hΛ⟩
      rw [eq14_11 hvI, td_modularPhi_iLambda hρ]
      conv_rhs => rw [hzr]
      push_cast
      ring

/-! #### The cusps `∞` and `0` -/

/-- (15.15) at `∞`: `η(z) |z| ln|z| → 1` as `z → ∞`. -/
theorem td_cusp_infty :
    Tendsto (fun z => puncturedSphereDensity z * (‖z‖ * Real.log ‖z‖)) (cocompact ℂ) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.1 td_cusp_eta_w) ε hε
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 (Filter.mem_inf_principal.1 hev)
  obtain ⟨T, hT⟩ := mem_atTop_sets.1 ht
  obtain ⟨R, hR⟩ := td_preimage_high T
  have key : ∀ y : ℂ, 0 ≤ y.im → R < ‖y‖ →
      dist (puncturedSphereDensity y * (‖y‖ * Real.log ‖y‖)) 1 < ε := by
    intro y hy hyR
    obtain ⟨w, hw, hφ, hre0, hre1, hwT⟩ := hR y hy hyR
    have h := hts (show w ∈ Complex.im ⁻¹' t from hT w.im hwT.le) ⟨hre0, hre1⟩
    rw [← hφ]
    exact h
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop R)] with z hz
  rcases le_or_gt 0 z.im with h | h
  · exact key z h hz
  · have h' := key (conj z) (by rw [Complex.conj_im]; linarith) (by rwa [Complex.norm_conj])
    rwa [td_eta_conj, Complex.norm_conj] at h'

/-- (15.15) at `0`: `η(z) |z| ln(1/|z|) → 1` as `z → 0`. -/
theorem td_cusp_zero :
    Tendsto (fun z => puncturedSphereDensity z * (‖z‖ * Real.log ‖z‖⁻¹)) (𝓝[≠] 0) (𝓝 1) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  refine (td_cusp_infty.comp hinv).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  have h := td_eta_inv z⁻¹
  rw [inv_inv] at h
  simp only [Function.comp_apply]
  rw [h, norm_inv]
  field_simp

/-! #### The puncture `1` -/

/-- `η(z) → ∞` as `z → 1`. -/
theorem td_blowup_one : Tendsto puncturedSphereDensity (𝓝[≠] 1) atTop := by
  have hmap : Tendsto (fun z : ℂ => 1 - z) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℂ => 1 - z) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 (Ne.symm hz)
  -- `D(ζ) = |ζ| ln (1/|ζ|) → 0⁺`
  have hD : Tendsto (fun ζ : ℂ => ‖ζ‖ * Real.log ‖ζ‖⁻¹) (𝓝[≠] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Tendsto (fun ζ : ℂ => ‖ζ‖ * Real.log ‖ζ‖) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * Real.log ‖(0 : ℂ)‖)) :=
        (Real.continuous_mul_log.comp continuous_norm).tendsto 0
      simp only [norm_zero, Real.log_zero, mul_zero] at hc
      have hc' := hc.neg
      rw [neg_zero] at hc'
      refine (hc'.mono_left nhdsWithin_le_nhds).congr' (Eventually.of_forall fun ζ => ?_)
      show -(‖ζ‖ * Real.log ‖ζ‖) = ‖ζ‖ * Real.log ‖ζ‖⁻¹
      rw [Real.log_inv, mul_neg]
    · have hsmall : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ≠ 0 ∧ ‖ζ‖ < 1 := by
        have h1 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ≠ 0 := self_mem_nhdsWithin
        have h2 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ‖ζ‖ < 1 :=
          eventually_nhdsWithin_of_eventually_nhds (by
            filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with v hv
            exact mem_ball_zero_iff.1 hv)
        filter_upwards [h1, h2] with ζ h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hsmall] with ζ ⟨h0, h1⟩
      have hp : 0 < ‖ζ‖ := norm_pos_iff.2 h0
      exact mul_pos hp (Real.log_pos (one_lt_inv_iff₀.2 ⟨hp, h1⟩))
  have hη : Tendsto puncturedSphereDensity (𝓝[≠] (0 : ℂ)) atTop := by
    refine (td_cusp_zero.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hD)).congr' ?_
    filter_upwards [(tendsto_nhdsWithin_iff.1 hD).2] with ζ hζ
    have hζ' : ‖ζ‖ * Real.log ‖ζ‖⁻¹ ≠ 0 := (show 0 < ‖ζ‖ * Real.log ‖ζ‖⁻¹ from hζ).ne'
    simp only [Function.comp_apply]
    rw [mul_assoc, mul_inv_cancel₀ hζ', mul_one]
  refine (hη.comp hmap).congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  exact td_eta_one_sub z

/-! #### The comparison `η(ā w) ≤ η(a w)` on the lower half-plane (the maximum principle) -/

/-- `ln (η(a w)) - ln (η(b w)) → 0` along a filter on which `η(· w)|w| ℓ(w) → 1` for `a` and `b`, where `ℓ(w) > 0`
eventually: the common factor `|w| ℓ(w)` cancels. -/
theorem td_log_ratio_tendsto {l : Filter ℂ} {a b : ℂ} {c : ℂ → ℝ}
    (ha : Tendsto (fun w => puncturedSphereDensity (a * w) * c w) l (𝓝 1))
    (hb : Tendsto (fun w => puncturedSphereDensity (b * w) * c w) l (𝓝 1))
    (hpos : ∀ᶠ w in l, 0 < c w ∧ 0 < puncturedSphereDensity (a * w) ∧
      0 < puncturedSphereDensity (b * w)) :
    Tendsto (fun w => Real.log (puncturedSphereDensity (a * w)) -
      Real.log (puncturedSphereDensity (b * w))) l (𝓝 0) := by
  have hlog : Tendsto (fun w => Real.log (puncturedSphereDensity (a * w) * c w) -
      Real.log (puncturedSphereDensity (b * w) * c w)) l (𝓝 (Real.log 1 - Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto.comp ha).sub
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hb)
  rw [Real.log_one, sub_self] at hlog
  refine hlog.congr' ?_
  filter_upwards [hpos] with w ⟨hc, hA, hB⟩
  rw [Real.log_mul hA.ne' hc.ne', Real.log_mul hB.ne' hc.ne']
  ring

/-- **The maximum principle of Lemma 15.1**: for `|a| = 1`, `Im a > 0` and `Im w < 0`, `w ≠ ā`: `η(ā w) ≤ η(a w)` (the rotated densities of `ℂ̄(0, ā, ∞)` and `ℂ̄(0, a, ∞)` compared on the lower half-plane). -/
theorem td_compare {a : ℂ} (ha : ‖a‖ = 1) (ha' : 0 < a.im) {w : ℂ} (hw : w.im < 0)
    (hwb : w ≠ conj a) :
    puncturedSphereDensity (conj a * w) ≤ puncturedSphereDensity (a * w) := by
  set b : ℂ := conj a with hbdef
  set η : ℂ → ℝ := puncturedSphereDensity with hηdef
  have hb : ‖b‖ = 1 := by rw [hbdef, Complex.norm_conj, ha]
  have hb' : b.im < 0 := by rw [hbdef, Complex.conj_im]; linarith
  have hab : a * b = 1 := by
    rw [hbdef, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; norm_num
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  -- where the two densities are regular
  have haw1 : ∀ v : ℂ, v ≠ b → a * v ≠ 1 := by
    intro v hv h
    apply hv
    have : b * (a * v) = b * 1 := by rw [h]
    rw [← mul_assoc, mul_comm b a, hab, one_mul, mul_one] at this
    exact this
  have hbw1 : ∀ v : ℂ, v.im ≤ 0 → b * v ≠ 1 := by
    intro v hv h
    have hva : v = a := by
      have : a * (b * v) = a * 1 := by rw [h]
      rw [← mul_assoc, hab, one_mul, mul_one] at this
      exact this
    rw [hva] at hv
    linarith
  have hmul0 : ∀ c v : ℂ, c ≠ 0 → v ≠ 0 → c * v ≠ 0 := fun c v hc hv => mul_ne_zero hc hv
  set h : ℂ → ℝ := fun v => Real.log (η (a * v)) - Real.log (η (b * v)) with hhdef
  -- continuity of `h` off `0`, `b`, `a`
  have hcont : ∀ v : ℂ, v ≠ 0 → v ≠ b → v.im ≤ 0 → ContinuousAt h v := by
    intro v hv0 hvb hvim
    have hA := td_eta_continuousAt (hmul0 a v ha0 hv0) (haw1 v hvb)
    have hB := td_eta_continuousAt (hmul0 b v hb0 hv0) (hbw1 v hvim)
    have hApos := td_eta_pos (hmul0 a v ha0 hv0) (haw1 v hvb)
    have hBpos := td_eta_pos (hmul0 b v hb0 hv0) (hbw1 v hvim)
    exact ((hA.comp (continuousAt_const.mul continuousAt_id)).log hApos.ne').sub
      ((hB.comp (continuousAt_const.mul continuousAt_id)).log hBpos.ne')
  -- (F1) `h = 0` on the real axis
  have hreal : ∀ v : ℂ, v.im = 0 → h v = 0 := by
    intro v hv
    have hconj : b * v = conj (a * v) := by
      rw [map_mul, ← hbdef, Complex.conj_eq_iff_im.2 hv]
    simp only [hhdef, hconj, hηdef, td_eta_conj, sub_self]
  -- (F3) `h → 0` at `0`
  have hzero : Tendsto h (𝓝[≠] 0) (𝓝 0) := by
    have hmulc : ∀ c : ℂ, c ≠ 0 → Tendsto (fun v => c * v) (𝓝[≠] 0) (𝓝[≠] 0) := by
      intro c hc
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun v => c * v) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact mul_ne_zero hc hv
    have hA := td_cusp_zero.comp (hmulc a ha0)
    have hB := td_cusp_zero.comp (hmulc b hb0)
    have hnA : ∀ v, ‖a * v‖ = ‖v‖ := fun v => by rw [norm_mul, ha, one_mul]
    have hnB : ∀ v, ‖b * v‖ = ‖v‖ := fun v => by rw [norm_mul, hb, one_mul]
    simp only [Function.comp_def, hnA, hnB] at hA hB
    refine td_log_ratio_tendsto hA hB ?_
    have hsmall : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ≠ 0 ∧ ‖v‖ < 1 ∧ v ≠ b := by
      have h1 : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ≠ 0 := self_mem_nhdsWithin
      have h2 : ∀ᶠ v in 𝓝[≠] (0 : ℂ), ‖v‖ < 1 :=
        eventually_nhdsWithin_of_eventually_nhds (by
          filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with v hv
          exact mem_ball_zero_iff.1 hv)
      have h3 : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ≠ b :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hb0))
      filter_upwards [h1, h2, h3] with v h1 h2 h3
      exact ⟨h1, h2, h3⟩
    filter_upwards [hsmall] with v ⟨hv0, hv1, hvb⟩
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    refine ⟨mul_pos hvpos (Real.log_pos (one_lt_inv_iff₀.2 ⟨hvpos, hv1⟩)),
      td_eta_pos (hmul0 a v ha0 hv0) (haw1 v hvb), td_eta_pos (hmul0 b v hb0 hv0) ?_⟩
    intro h1
    have : ‖b * v‖ = 1 := by rw [h1, norm_one]
    rw [hnB] at this
    linarith
  -- (F4) `h → 0` at `∞`
  have hinfty : Tendsto h (cocompact ℂ) (𝓝 0) := by
    have hmulc : ∀ c : ℂ, c ≠ 0 → Tendsto (fun v => c * v) (cocompact ℂ) (cocompact ℂ) := by
      intro c hc
      have hn : ∀ v : ℂ, ‖c * v‖ = ‖c‖ * ‖v‖ := fun v => norm_mul c v
      rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, tendsto_comap_iff]
      simp only [Function.comp_def, hn]
      exact (tendsto_comap).const_mul_atTop (norm_pos_iff.2 hc)
    have hA := td_cusp_infty.comp (hmulc a ha0)
    have hB := td_cusp_infty.comp (hmulc b hb0)
    have hnA : ∀ v, ‖a * v‖ = ‖v‖ := fun v => by rw [norm_mul, ha, one_mul]
    have hnB : ∀ v, ‖b * v‖ = ‖v‖ := fun v => by rw [norm_mul, hb, one_mul]
    simp only [Function.comp_def, hnA, hnB] at hA hB
    refine td_log_ratio_tendsto hA hB ?_
    have hbig : ∀ᶠ v in cocompact ℂ, 2 < ‖v‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop 2)
    filter_upwards [hbig] with v hv
    have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hv; linarith
    have hvb : v ≠ b := by intro h0; rw [h0, hb] at hv; linarith
    refine ⟨mul_pos (by linarith) (Real.log_pos (by linarith)),
      td_eta_pos (hmul0 a v ha0 hv0) (haw1 v hvb), td_eta_pos (hmul0 b v hb0 hv0) ?_⟩
    intro h1
    have : ‖b * v‖ = 1 := by rw [h1, norm_one]
    rw [hnB] at this
    linarith
  -- (F5) `h → +∞` at `b` (the puncture `a w = 1`)
  have hpole : Tendsto h (𝓝[≠] b) atTop := by
    have hmap : Tendsto (fun v => a * v) (𝓝[≠] b) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun v => a * v) (𝓝 b) (𝓝 (a * b)) := tendsto_const_nhds.mul tendsto_id
        rw [hab] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact haw1 v hv
    have hA : Tendsto (fun v => Real.log (η (a * v))) (𝓝[≠] b) atTop :=
      Real.tendsto_log_atTop.comp (td_blowup_one.comp hmap)
    have hbb0 : b * b ≠ 0 := mul_ne_zero hb0 hb0
    have hbb1 : b * b ≠ 1 := hbw1 b hb'.le
    have hB : Tendsto (fun v => Real.log (η (b * v))) (𝓝[≠] b) (𝓝 (Real.log (η (b * b)))) := by
      have hc := ((td_eta_continuousAt hbb0 hbb1).comp
        (continuousAt_const.mul continuousAt_id : ContinuousAt (fun v => b * v) b)).log
          (td_eta_pos hbb0 hbb1).ne'
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    exact hA.atTop_add hB.neg
  -- the maximum-principle argument
  by_contra hcon
  push Not at hcon
  have hw0 : w ≠ 0 := by intro h0; rw [h0, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  have hm : h w < 0 := by
    have hA := td_eta_pos (hmul0 a w ha0 hw0) (haw1 w hwb)
    simp only [hhdef]
    have := Real.log_lt_log hA hcon
    linarith
  set m : ℝ := h w with hmdef
  -- radii around `0`, `b` and `∞` outside which `h ≤ m` is impossible
  obtain ⟨δ₀, hδ₀, hδ₀h⟩ : ∃ δ₀ > 0, ∀ v : ℂ, v ≠ 0 → ‖v‖ < δ₀ → m < h v := by
    have hev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), m < h v := hzero.eventually (lt_mem_nhds hm)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
    exact ⟨δ, hδ, fun v hv0 hvδ => hδs ⟨mem_ball_zero_iff.2 hvδ, hv0⟩⟩
  obtain ⟨δ₁, hδ₁, hδ₁h⟩ : ∃ δ₁ > 0, ∀ v : ℂ, v ≠ b → ‖v - b‖ < δ₁ → m < h v := by
    have hev : ∀ᶠ v in 𝓝[≠] b, m < h v := hpole.eventually (eventually_gt_atTop m)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
    exact ⟨δ, hδ, fun v hvb hvδ => hδs ⟨mem_ball_iff_norm.2 hvδ, hvb⟩⟩
  obtain ⟨R, hR, hRh⟩ : ∃ R > 0, ∀ v : ℂ, R ≤ ‖v‖ → m < h v := by
    have hev : ∀ᶠ v in cocompact ℂ, m < h v := hinfty.eventually (lt_mem_nhds hm)
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop] at hev
    obtain ⟨t, ht, hts⟩ := hev
    obtain ⟨R₀, hR₀⟩ := mem_atTop_sets.1 ht
    exact ⟨max R₀ 1, by positivity, fun v hv => hts (hR₀ _ ((le_max_left _ _).trans hv))⟩
  set r₀ : ℝ := δ₀ / 2 with hr₀
  set r₁ : ℝ := δ₁ / 2 with hr₁
  set C : Set ℂ := {v | v.im ≤ 0} ∩ closedBall 0 R ∩ {v | r₀ ≤ ‖v‖} ∩ {v | r₁ ≤ ‖v - b‖}
    with hCdef
  have hCc : IsCompact C := by
    refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset ?_ ?_
    · refine (((isClosed_le Complex.continuous_im continuous_const).inter
        isClosed_closedBall).inter (isClosed_le continuous_const continuous_norm)).inter
        (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
    · intro v hv; exact hv.1.1.2
  have hC0 : ∀ v ∈ C, v ≠ 0 := by
    intro v hv h0
    have h' : r₀ ≤ ‖v‖ := hv.1.2
    rw [h0, norm_zero] at h'
    linarith
  have hCb : ∀ v ∈ C, v ≠ b := by
    intro v hv h0
    have h' : r₁ ≤ ‖v - b‖ := hv.2
    rw [h0, sub_self, norm_zero] at h'
    linarith
  have hCcont : ContinuousOn h C := fun v hv =>
    (hcont v (hC0 v hv) (hCb v hv) hv.1.1.1).continuousWithinAt
  have hwC : w ∈ C := by
    refine ⟨⟨⟨hw.le, ?_⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      by_contra hlt; push Not at hlt
      exact lt_irrefl m (hRh w hlt.le)
    · show r₀ ≤ ‖w‖
      by_contra hlt; push Not at hlt
      exact lt_irrefl m (hδ₀h w hw0 (by linarith))
    · show r₁ ≤ ‖w - b‖
      by_contra hlt; push Not at hlt
      exact lt_irrefl m (hδ₁h w hwb (by linarith))
  obtain ⟨w₀, hw₀C, hw₀min⟩ := hCc.exists_isMinOn ⟨w, hwC⟩ hCcont
  have hw₀m : h w₀ ≤ m := hw₀min hwC
  -- `w₀` is interior
  have hw₀0 := hC0 w₀ hw₀C
  have hw₀b := hCb w₀ hw₀C
  have hw₀im : w₀.im < 0 := by
    have hle0 : w₀.im ≤ 0 := hw₀C.1.1.1
    rcases hle0.lt_or_eq with h1 | h1
    · exact h1
    · have := hreal w₀ h1
      linarith
  have hw₀R : ‖w₀‖ < R := by
    by_contra hge; push Not at hge
    linarith [hRh w₀ hge]
  have hw₀r₀ : r₀ < ‖w₀‖ := by
    by_contra hge; push Not at hge
    linarith [hδ₀h w₀ hw₀0 (by linarith)]
  have hw₀r₁ : r₁ < ‖w₀ - b‖ := by
    by_contra hge; push Not at hge
    linarith [hδ₁h w₀ hw₀b (by linarith)]
  have hCnhds : C ∈ 𝓝 w₀ := by
    have hO : IsOpen ({v : ℂ | v.im < 0} ∩ ball 0 R ∩ {v | r₀ < ‖v‖} ∩ {v | r₁ < ‖v - b‖}) :=
      (((isOpen_lt Complex.continuous_im continuous_const).inter isOpen_ball).inter
        (isOpen_lt continuous_const continuous_norm)).inter
        (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
    refine Filter.mem_of_superset (hO.mem_nhds ⟨⟨⟨hw₀im, mem_ball_zero_iff.2 hw₀R⟩, hw₀r₀⟩, hw₀r₁⟩)
      ?_
    rintro v ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    simp only [Set.mem_ofPred_eq] at h1 h3 h4
    exact ⟨⟨⟨le_of_lt h1, ball_subset_closedBall h2⟩, le_of_lt h3⟩, le_of_lt h4⟩
  have hlocmin : IsLocalMin h w₀ := hw₀min.isLocalMin hCnhds
  have hcw₀ : ContinuousAt h w₀ := hcont w₀ hw₀0 hw₀b hw₀im.le
  -- the curvature identity at `a w₀` (direction `a`) and at `b w₀` (direction `b`)
  have hA0 := hmul0 a w₀ ha0 hw₀0
  have hA1 := haw1 w₀ hw₀b
  have hB0 := hmul0 b w₀ hb0 hw₀0
  have hB1 := hbw1 w₀ hw₀im.le
  obtain ⟨c₁, c₂, hc₁, hc₂, hcsum⟩ := td_eta_curv hA0 hA1 ha
  obtain ⟨e₁, e₂, he₁, he₂, hesum⟩ := td_eta_curv hB0 hB1 hb
  have hline1 : td_Twice (fun t : ℝ => h (w₀ + t * 1)) (c₁ - e₁) := by
    refine td_twice_congr (td_twice_sub hc₁ he₁) (Eventually.of_forall fun t => ?_)
    simp only [hhdef, mul_one]
    rw [show a * (w₀ + t) = a * w₀ + t * a by ring, show b * (w₀ + t) = b * w₀ + t * b by ring]
  have hline2 : td_Twice (fun t : ℝ => h (w₀ + t * I)) (c₂ - e₂) := by
    refine td_twice_congr (td_twice_sub hc₂ he₂) (Eventually.of_forall fun t => ?_)
    simp only [hhdef]
    rw [show a * (w₀ + t * I) = a * w₀ + t * (I * a) by ring,
      show b * (w₀ + t * I) = b * w₀ + t * (I * b) by ring]
  have htest := add_nonneg (td_line_isLocalMin hlocmin hcw₀ 1) (td_line_isLocalMin hlocmin hcw₀ I)
  rw [td_twice_deriv2 hline1, td_twice_deriv2 hline2] at htest
  -- but `η(a w₀) < η(b w₀)` since `h(w₀) < 0`
  have hApos := td_eta_pos hA0 hA1
  have hBpos := td_eta_pos hB0 hB1
  have hlt : η (a * w₀) < η (b * w₀) := by
    have h' : Real.log (η (a * w₀)) < Real.log (η (b * w₀)) := by
      have : h w₀ < 0 := lt_of_le_of_lt hw₀m hm
      simp only [hhdef] at this
      linarith
    exact (Real.log_lt_log_iff hApos hBpos).1 h'
  have hsq : η (a * w₀) ^ 2 < η (b * w₀) ^ 2 := by
    exact pow_lt_pow_left₀ hlt hApos.le two_ne_zero
  have : c₁ - e₁ + (c₂ - e₂) < 0 := by
    have e : c₁ - e₁ + (c₂ - e₂) = (c₁ + c₂) - (e₁ + e₂) := by ring
    rw [e, hcsum, hesum]
    linarith
  linarith

/-- **Lemma 15.1**: the Poincaré density `η` of `ℂ̄(0, 1, ∞)` satisfies `η(z) ≥ η(-|z|)`. -/
theorem lemma15_1 {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    puncturedSphereDensity (-(‖z‖ : ℂ)) ≤ puncturedSphereDensity z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hpolar : (‖z‖ : ℂ) * exp (arg z * I) = z := Complex.norm_mul_exp_arg_mul_I z
  by_cases hπ : arg z = π
  · -- `z = -|z|`
    have : z = -(‖z‖ : ℂ) := by
      conv_lhs => rw [← hpolar]
      rw [hπ, exp_pi_mul_I, mul_neg_one]
    rw [← this]
  -- `a = i e^{i arg z / 2}`: `|a| = 1`, `Im a = cos(arg z / 2) > 0`, `-|z| a² = z`
  set a : ℂ := I * exp ((arg z / 2 : ℝ) * I) with hadef
  have ha : ‖a‖ = 1 := by rw [hadef, norm_mul, Complex.norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hlt : -π < arg z := neg_pi_lt_arg z
  have hle : arg z < π := lt_of_le_of_ne (arg_le_pi z) hπ
  have ha' : 0 < a.im := by
    rw [hadef, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ha2 : a * a = -exp (arg z * I) := by
    rw [hadef]
    have : exp ((arg z / 2 : ℝ) * I) * exp ((arg z / 2 : ℝ) * I) = exp (arg z * I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    linear_combination (exp ((arg z / 2 : ℝ) * I) * exp ((arg z / 2 : ℝ) * I)) * I_sq - this
  set w : ℂ := -(‖z‖ : ℂ) * a with hwdef
  have hw : w.im < 0 := by
    rw [hwdef, neg_mul, Complex.neg_im, Complex.im_ofReal_mul]
    have : 0 < ‖z‖ * a.im := mul_pos hr ha'
    linarith
  have haw : a * w = z := by
    conv_rhs => rw [← hpolar]
    rw [hwdef]
    linear_combination (-(‖z‖ : ℂ)) * ha2
  have hbw : conj a * w = -(‖z‖ : ℂ) := by
    have hab : conj a * a = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; norm_num
    rw [hwdef]
    linear_combination (-(‖z‖ : ℂ)) * hab
  have hwb : w ≠ conj a := by
    intro h
    apply hz1
    rw [← haw, h, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have := td_compare ha ha' hw hwb
  rwa [haw, hbw] at this

/-! ### tdist: a radial lower bound for `δ`, the circle bound `|f(e^{iθ})| ≤ λ(K)`, the extremal map -/

/-! #### The density on the negative axis -/

/-- `Λ` is continuous on `(0, ∞)`. -/
theorem td_continuousAt_quadLambda {r : ℝ} (hr : 0 < r) : ContinuousAt quadLambda r := by
  have heq : quadLambda =ᶠ[𝓝 r] fun ρ => 2 / π * grotzschMu (Real.sqrt (1 / (1 + ρ))) := by
    filter_upwards [Ioi_mem_nhds hr] with ρ hρ
    exact eq5_18 hρ
  refine ContinuousAt.congr ?_ heq.symm
  have hs0 : 0 < Real.sqrt (1 / (1 + r)) := Real.sqrt_pos.2 (by positivity)
  have hs1 : Real.sqrt (1 / (1 + r)) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  have hμ : ContinuousAt grotzschMu (Real.sqrt (1 / (1 + r))) :=
    s15_grotzschMu_continuousOn.continuousAt (Ioo_mem_nhds hs0 hs1)
  have hin : ContinuousAt (fun ρ : ℝ => Real.sqrt (1 / (1 + ρ))) r :=
    Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith))
  exact continuousAt_const.mul (ContinuousAt.comp (f := fun ρ : ℝ => Real.sqrt (1 / (1 + ρ))) hμ hin)

/-- `ℓ(v) = -Re φ(iv)`; `ℓ = λ` on `(0, ∞)` by (14.19). -/
def td_ell (v : ℝ) : ℝ := -(modularPhi ((v : ℂ) * I)).re

/-- The derivative of `t ↦ φ(it)`. -/
theorem td_hasDerivAt_phi_iv {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun t : ℝ => modularPhi ((t : ℂ) * I)) (deriv modularPhi ((v : ℂ) * I) * I) v := by
  have hvI : 0 < ((v : ℂ) * I).im := by simpa using hv
  have hd := (td_analyticAt_modularPhi hvI).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I v := by
    simpa using ((hasDerivAt_id (v : ℂ)).comp_ofReal).mul_const I
  exact hd.comp v hline

/-- `φ'(iv)` is purely imaginary (`φ` is real on the imaginary axis). -/
theorem td_re_deriv_iv {v : ℝ} (hv : 0 < v) : (deriv modularPhi ((v : ℂ) * I)).re = 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt v (td_hasDerivAt_phi_iv hv)
  have hzero : (fun t : ℝ => Complex.imCLM (modularPhi ((t : ℂ) * I))) =ᶠ[𝓝 v] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hv] with t ht
    exact mphi_modularPhi_im_eq_zero_of_side (by simpa using ht) (Or.inl (by simp))
  have h0 : HasDerivAt (fun t : ℝ => Complex.imCLM (modularPhi ((t : ℂ) * I))) 0 v :=
    (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq hzero
  have := h.unique h0
  simpa [Complex.mul_im] using this

/-- The derivative of `v ↦ -Re φ(iv) = λ(v)`. -/
theorem td_hasDerivAt_ell {v : ℝ} (hv : 0 < v) :
    HasDerivAt td_ell (deriv modularPhi ((v : ℂ) * I)).im v := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt v (td_hasDerivAt_phi_iv hv)).neg
  have hd : -(Complex.reCLM (deriv modularPhi ((v : ℂ) * I) * I)) =
      (deriv modularPhi ((v : ℂ) * I)).im := by
    simp [Complex.mul_re]
  rw [hd] at h
  exact h

/-- `-Re φ(iΛ(r)) = r`. -/
theorem td_ell_quadLambda {r : ℝ} (hr : 0 < r) : td_ell (quadLambda r) = r := by
  have hv := b4_num_quadLambda_pos hr
  rw [td_ell, ← eq14_19 hv, lambdaInv_quadLambda hr]

/-- `Im φ'(iΛ(r)) ≠ 0`. -/
theorem td_im_deriv_ne_zero {r : ℝ} (hr : 0 < r) :
    (deriv modularPhi ((quadLambda r : ℂ) * I)).im ≠ 0 := by
  have hv := b4_num_quadLambda_pos hr
  have hvI : 0 < ((quadLambda r : ℂ) * I).im := by simpa using hv
  intro h0
  apply td_deriv_ne_zero_of_covering hvI
  exact Complex.ext (td_re_deriv_iv hv) h0

/-- `Λ` is differentiable with `Λ'(r) = 1/Im φ'(iΛ(r))`. -/
theorem td_hasDerivAt_quadLambda {r : ℝ} (hr : 0 < r) :
    HasDerivAt quadLambda ((deriv modularPhi ((quadLambda r : ℂ) * I)).im)⁻¹ r := by
  refine HasDerivAt.of_local_left_inverse (td_continuousAt_quadLambda hr)
    (td_hasDerivAt_ell (b4_num_quadLambda_pos hr)) (td_im_deriv_ne_zero hr) ?_
  filter_upwards [Ioi_mem_nhds hr] with y hy
  exact td_ell_quadLambda hy

/-- `(ln Λ)'(r)`. -/
def td_U' (r : ℝ) : ℝ := ((deriv modularPhi ((quadLambda r : ℂ) * I)).im)⁻¹ / quadLambda r

/-- The derivative of `ln Λ`. -/
theorem td_hasDerivAt_logLambda {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Real.log (quadLambda s)) (td_U' r) r :=
  (td_hasDerivAt_quadLambda hr).log (b4_num_quadLambda_pos hr).ne'

/-- `|(ln Λ)'(r)| = η(-r)`. -/
theorem td_abs_U' {r : ℝ} (hr : 0 < r) : |td_U' r| = puncturedSphereDensity (-(r : ℂ)) := by
  have hv := b4_num_quadLambda_pos hr
  have hvI : 0 < ((quadLambda r : ℂ) * I).im := by simpa using hv
  have hη := (eq14_6_well_defined hvI hvI rfl).2
  rw [td_modularPhi_iLambda hr] at hη
  rw [hη, td_U']
  have hre := td_re_deriv_iv hv
  set d := deriv modularPhi ((quadLambda r : ℂ) * I) with hd
  have hdeq : d = ((d.im : ℝ) : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
  have hnorm : ‖d‖ = |d.im| := by
    conv_lhs => rw [hdeq]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hnorm, show ((quadLambda r : ℂ) * I).im = quadLambda r by simp, abs_div, abs_inv,
    abs_of_pos hv]
  field_simp

/-- The derivative of `ln Λ` is continuous on `(0, ∞)`. -/
theorem td_continuousOn_U' : ContinuousOn td_U' (Ioi 0) := by
  intro r hr
  have hr' : 0 < r := hr
  have hv := b4_num_quadLambda_pos hr'
  refine ContinuousAt.continuousWithinAt ?_
  have hΛ := td_continuousAt_quadLambda hr'
  have hvI : 0 < ((quadLambda r : ℂ) * I).im := by simpa using hv
  have hφ' : ContinuousAt (deriv modularPhi) ((quadLambda r : ℂ) * I) :=
    (td_analyticAt_modularPhi hvI).deriv.continuousAt
  have hline : ContinuousAt (fun s : ℝ => ((quadLambda s : ℂ) * I)) r :=
    (continuous_ofReal.continuousAt.comp hΛ).mul continuousAt_const
  exact ((Complex.continuous_im.continuousAt.comp
    (ContinuousAt.comp (f := fun s : ℝ => ((quadLambda s : ℂ) * I)) hφ' hline)).inv₀
    (td_im_deriv_ne_zero hr')).div hΛ hv.ne'

/-! #### The calibration -/

/-- Radial lower bound for the Poincaré distance of `ℂ̄(0, 1, ∞)`: `δ(z₁, z₂) ≥ |ln Λ(|z₂|) - ln Λ(|z₁|)|` (Lemma 15.1 and the density on the negative axis). -/
theorem td_dist_lower {z₁ z₂ : ℂ} (_h₁ : z₁ ≠ 0 ∧ z₁ ≠ 1) (_h₂ : z₂ ≠ 0 ∧ z₂ ≠ 1) :
    ENNReal.ofReal |Real.log (quadLambda ‖z₂‖) - Real.log (quadLambda ‖z₁‖)| ≤
      puncturedSphereDist z₁ z₂ := by
  unfold puncturedSphereDist metricDist
  refine le_iInf₂ fun γ hγ => ?_
  obtain ⟨⟨K, hK⟩, h0, h1, htr⟩ := hγ
  have huIcc : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hcont : ContinuousOn γ.toFun (Icc 0 1) := hK.continuousOn
  set u : ℝ → ℝ := fun t => ‖γ.toFun t‖ with hudef
  -- `0 < m ≤ u ≤ M` on `[0,1]`
  have hcompact : IsCompact (γ.toFun '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hcont
  have hne : (γ.toFun '' Icc (0 : ℝ) 1).Nonempty := ⟨γ.toFun 0, ⟨0, by norm_num, rfl⟩⟩
  obtain ⟨zm, hzm, hzmmin⟩ := hcompact.exists_isMinOn hne continuous_norm.continuousOn
  obtain ⟨zM, hzM, hzMmax⟩ := hcompact.exists_isMaxOn hne continuous_norm.continuousOn
  set m : ℝ := ‖zm‖ with hmdef
  set M : ℝ := ‖zM‖ with hMdef
  have hm : 0 < m := norm_pos_iff.2 (htr hzm).1
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ u t ∧ u t ≤ M := fun t ht =>
    ⟨hzmmin ⟨t, ht, rfl⟩, hzMmax ⟨t, ht, rfl⟩⟩
  -- `U = ln Λ` is Lipschitz on `[m, M]`
  set U : ℝ → ℝ := fun s => Real.log (quadLambda s) with hUdef
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ s ∈ Icc m M, ‖td_U' s‖₊ ≤ C := by
    have hc : ContinuousOn td_U' (Icc m M) :=
      td_continuousOn_U'.mono fun s hs => (lt_of_lt_of_le hm hs.1 : 0 < s)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨C.toNNReal, fun s hs => ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC s hs).trans (Real.le_coe_toNNReal C)
  have hUlip : LipschitzOnWith C U (Icc m M) :=
    (convex_Icc m M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := td_U')
      (fun s hs => (td_hasDerivAt_logLambda (lt_of_lt_of_le hm hs.1)).hasDerivWithinAt) hC
  have hu : LipschitzOnWith K u (Icc (0 : ℝ) 1) :=
    LipschitzWith.comp_lipschitzOnWith lipschitzWith_one_norm hK |>.weaken (one_mul K).le
  have hmaps : MapsTo u (Icc (0 : ℝ) 1) (Icc m M) := fun t ht => hbd t ht
  set G : ℝ → ℝ := fun t => U (u t) with hGdef
  have hGac : AbsolutelyContinuousOnInterval G 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C * K)
    rw [huIcc]
    exact hUlip.comp hu hmaps
  have huac : AbsolutelyContinuousOnInterval u 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K)
    rw [huIcc]; exact hu
  have hFTC : ∫ t in (0 : ℝ)..1, deriv G t = U ‖z₂‖ - U ‖z₁‖ := by
    rw [hGac.integral_deriv_eq_sub]
    simp only [hGdef, hudef, h0, h1]
  -- `|G'| ≤ η(-u) |u'| ≤ η(γ) |γ'|` a.e.
  have hae : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      |deriv G t| ≤ puncturedSphereDensity (γ.toFun t) * ‖deriv γ.toFun t‖ := by
    have hγae : ∀ᵐ t, t ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ.toFun t :=
      ae_differentiableAt_of_lipschitzOn (K := K) (by rw [huIcc]; exact hK)
    filter_upwards [hγae, huac.ae_differentiableAt] with t hγt hut ht
    have htI : t ∈ uIcc (0 : ℝ) 1 := by rw [huIcc]; exact Ioo_subset_Icc_self ht
    have hnorm : |deriv u t| ≤ ‖deriv γ.toFun t‖ :=
      abs_deriv_norm_le (hγt htI).hasDerivAt (hut htI).hasDerivAt
    have hutpos : 0 < u t := lt_of_lt_of_le hm (hbd t (Ioo_subset_Icc_self ht)).1
    have hGd : HasDerivAt G (td_U' (u t) * deriv u t) t :=
      (td_hasDerivAt_logLambda hutpos).comp t (hut htI).hasDerivAt
    have hγS := htr ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    have h151 := lemma15_1 hγS.1 hγS.2
    have hη0 : 0 ≤ |td_U' (u t)| := abs_nonneg _
    rw [hGd.deriv, abs_mul]
    calc |td_U' (u t)| * |deriv u t| ≤ |td_U' (u t)| * ‖deriv γ.toFun t‖ :=
          mul_le_mul_of_nonneg_left hnorm hη0
      _ = puncturedSphereDensity (-(‖γ.toFun t‖ : ℂ)) * ‖deriv γ.toFun t‖ := by
          rw [td_abs_U' hutpos]
      _ ≤ puncturedSphereDensity (γ.toFun t) * ‖deriv γ.toFun t‖ :=
          mul_le_mul_of_nonneg_right h151 (norm_nonneg _)
  -- assemble
  have hderivGint : IntegrableOn (deriv G) (Ioo (0 : ℝ) 1) :=
    (hGac.intervalIntegrable_deriv.1).mono_set Ioo_subset_Ioc_self
  have hIoo : ∫ t in (0 : ℝ)..1, deriv G t = ∫ t in Ioo (0 : ℝ) 1, deriv G t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
  calc ENNReal.ofReal |Real.log (quadLambda ‖z₂‖) - Real.log (quadLambda ‖z₁‖)|
      = ENNReal.ofReal |∫ t in Ioo (0 : ℝ) 1, deriv G t| := by rw [← hIoo, hFTC]
    _ ≤ ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, |deriv G t|) :=
        ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv G t| :=
        ofReal_setIntegral_le_lintegral hderivGint.abs
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (puncturedSphereDensity (γ.toFun t)) * ‖deriv γ.toFun t‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hae] with t ht hb
        have hle := hb ht
        calc ENNReal.ofReal |deriv G t|
            ≤ ENNReal.ofReal (puncturedSphereDensity (γ.toFun t) * ‖deriv γ.toFun t‖) :=
              ENNReal.ofReal_le_ofReal hle
          _ ≤ ENNReal.ofReal (puncturedSphereDensity (γ.toFun t)) * ‖deriv γ.toFun t‖ₑ := by
              rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm]
    _ = γ.rhoLength (fun z => ENNReal.ofReal (puncturedSphereDensity z)) := rfl

/-- `λ(K) ≥ 1` for `K ≥ 1`. -/
theorem td_one_le_lambdaInv {K : ℝ} (hK : 1 ≤ K) : 1 ≤ lambdaInv K :=
  b4_le_lambdaInv one_pos (by rw [b4_quadLambda_one]; exact hK)

/-- Shortcut (i): the unit-circle bound from Theorem 15.3 and the radial lower bound of `δ`. -/
theorem td_hyp_of_teich {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) (θ : ℝ) :
    ‖f (exp (θ * I))‖ ≤ lambdaInv K := by
  obtain ⟨hqc, hs, h0, h1⟩ := hf
  have hK : 1 ≤ K := hqc.2.1
  set z : ℂ := exp (θ * I) with hz
  have hz0 : z ≠ 0 := exp_ne_zero _
  have hzn : ‖z‖ = 1 := by rw [hz, norm_exp_ofReal_mul_I]
  have hinj := hqc.2.2.1.2.1
  by_cases hz1 : z = 1
  · rw [hz1, h1, norm_one]
    exact td_one_le_lambdaInv hK
  have hfz0 : f z ≠ 0 := fun h => hz0 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
  have hfz1 : f z ≠ 1 := fun h => hz1 (hinj (mem_univ _) (mem_univ _) (h.trans h1.symm))
  have hteich := thm15_3_teichmuller ⟨hqc, hs, h0, h1⟩ hz0 hz1
  have hlow := td_dist_lower ⟨hz0, hz1⟩ ⟨hfz0, hfz1⟩
  rw [hzn, b4_quadLambda_one, Real.log_one, sub_zero] at hlow
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have habs : |Real.log (quadLambda ‖f z‖)| ≤ Real.log K :=
    (ENNReal.ofReal_le_ofReal_iff hlogK).1 (hlow.trans hteich)
  have hs0 : 0 < ‖f z‖ := norm_pos_iff.2 hfz0
  have hΛ : 0 < quadLambda ‖f z‖ := b4_num_quadLambda_pos hs0
  have hle : quadLambda ‖f z‖ ≤ K :=
    (Real.log_le_log_iff hΛ (by linarith)).1 ((le_abs_self _).trans habs)
  exact b4_le_lambdaInv hs0 hle

/-- An affine map `z ↦ α z + β` with `α ≠ 0` is a conformal map of the plane onto itself. -/
theorem td_affine_conformal {α : ℂ} (β : ℂ) (hα : α ≠ 0) :
    IsConformalOnto (fun z => α * z + β) univ univ := by
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · intro z _ w _ hzw
    simpa [hα] using hzw
  · refine eq_univ_of_forall fun w => ⟨(w - β) / α, mem_univ _, ?_⟩
    field_simp
    ring

/-- Pre- and post-composing a `K`-q.c. map of the plane onto itself with affine maps. -/
theorem td_affine_comp {G₀ : ℂ → ℂ} {K : ℝ} (hG : IsKQC G₀ univ K) (hs : G₀ '' univ = univ)
    {α γ : ℂ} (β δ : ℂ) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    IsKQC (fun z => γ * G₀ (α * z + β) + δ) univ K ∧
      (fun z => γ * G₀ (α * z + β) + δ) '' univ = univ := by
  have h₁ := td_affine_conformal β hα
  have h₂ := td_affine_conformal δ hγ
  have hc := thm7_1_comp (thm7_1_comp (isKQC_one_of_conformal isOpen_univ h₁) hG (subset_univ _))
    (isKQC_one_of_conformal isOpen_univ h₂) (subset_univ _)
  rw [one_mul, mul_one] at hc
  refine ⟨hc, ?_⟩
  change ((fun w => γ * w + δ) ∘ (G₀ ∘ fun z => α * z + β)) '' univ = univ
  rw [image_comp, image_comp, h₁.2.2, hs, h₂.2.2]

/-- **Theorem 15.4**, literal statement, from the unit-circle bound `hyp`. -/
theorem td_thm15_4_of_hyp
    (hyp : ∀ (f : ℂ → ℂ) (K θ : ℝ), IsKQCNormalizedPlane f K → ‖f (exp (θ * I))‖ ≤ lambdaInv K)
    {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    sSup (range fun θ : ℝ => ‖f (z₀ + r * exp (θ * I)) - f z₀‖) ≤
      lambdaInv K * sInf (range fun θ : ℝ => ‖f (z₀ + r * exp (θ * I)) - f z₀‖) := by
  set g : ℝ → ℝ := fun θ => ‖f (z₀ + r * exp (θ * I)) - f z₀‖ with hg
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    simp only [hg]
    have h := exp_mul_I_periodic (θ : ℂ)
    simp only at h
    push_cast
    rw [h]
  -- the minimum is attained (compact range)
  have hcpt : IsCompact (range g) := hper.compact_of_continuous (by positivity) hgc
  obtain ⟨θ₁, hθ₁⟩ := hcpt.sInf_mem (range_nonempty g)
  set z₁ : ℂ := r * exp (θ₁ * I) with hz₁def
  have hz₁ : z₁ ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hr.ne') (exp_ne_zero _)
  set c : ℂ := f (z₀ + z₁) - f z₀ with hcdef
  -- the minimum is positive (injectivity)
  have hc : c ≠ 0 := by
    intro h
    have h' := hf.2.2.1.2.1 (mem_univ (z₀ + z₁)) (mem_univ z₀) (sub_eq_zero.1 h)
    exact hz₁ (by linear_combination h')
  -- the normalized map `F(z) = (f(z₀ + z₁ z) - f(z₀))/(f(z₀ + z₁) - f(z₀))`
  obtain ⟨hF, hFs⟩ := td_affine_comp hf hs z₀ (-(f z₀) / c) hz₁ (inv_ne_zero hc)
  set F : ℂ → ℂ := fun z => c⁻¹ * f (z₁ * z + z₀) + -f z₀ / c with hFdef
  have hF0 : F 0 = 0 := by
    simp only [hFdef, mul_zero, zero_add]
    field_simp
    ring
  have hF1 : F 1 = 1 := by
    simp only [hFdef, mul_one]
    rw [add_comm z₁ z₀]
    field_simp
    ring
  have hnorm : IsKQCNormalizedPlane F K := ⟨hF, hFs, hF0, hF1⟩
  have hmin : sInf (range g) = ‖c‖ := by
    rw [← hθ₁]
  rw [hmin]
  refine csSup_le (range_nonempty g) ?_
  rintro _ ⟨θ, rfl⟩
  have hpt : z₁ * exp (((θ - θ₁ : ℝ) : ℂ) * I) + z₀ = z₀ + r * exp (θ * I) := by
    rw [hz₁def, mul_assoc, ← exp_add]
    push_cast
    ring_nf
  have key : g θ = ‖F (exp (((θ - θ₁ : ℝ) : ℂ) * I))‖ * ‖c‖ := by
    rw [← norm_mul]
    simp only [hg, hFdef, hpt]
    congr 1
    field_simp
    ring
  rw [key]
  exact mul_le_mul_of_nonneg_right (hyp F K (θ - θ₁) hnorm) (norm_nonneg _)


/-- `λ(K) > 0` and `Λ(λ(K)) = K` for `K > 0`. -/
theorem td_quadLambda_lambdaInv {K : ℝ} (hK : 0 < K) :
    0 < lambdaInv K ∧ quadLambda (lambdaInv K) = K := by
  obtain ⟨hmono, hzero, hinf⟩ := quadLambda_strictMono
  -- `Λ(ρ₁) < K < Λ(ρ₂)`
  obtain ⟨ρ₁, hρ₁K, hρ₁⟩ : ∃ ρ₁ : ℝ, quadLambda ρ₁ < K ∧ 0 < ρ₁ :=
    ((hzero.eventually (gt_mem_nhds hK)).and self_mem_nhdsWithin).exists
  obtain ⟨ρ₂, hρ₂K, hρ₁₂⟩ : ∃ ρ₂ : ℝ, K < quadLambda ρ₂ ∧ ρ₁ < ρ₂ :=
    ((hinf.eventually (eventually_gt_atTop K)).and (eventually_gt_atTop ρ₁)).exists
  have hc : ContinuousOn quadLambda (Icc ρ₁ ρ₂) := fun s hs =>
    (td_continuousAt_quadLambda (lt_of_lt_of_le hρ₁ hs.1)).continuousWithinAt
  obtain ⟨ρ, hρ, hΛρ⟩ := intermediate_value_Icc hρ₁₂.le hc ⟨hρ₁K.le, hρ₂K.le⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρ₁ hρ.1
  have hlam : lambdaInv K = ρ := by rw [← hΛρ, lambdaInv_quadLambda hρ0]
  exact ⟨hlam ▸ hρ0, by rw [hlam, hΛρ]⟩

/-! #### The affine stretch -/

/-- `x + iy ↦ αx + iβy`. -/
def td_Stretch (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := ((α * z.re : ℝ) : ℂ) + ((β * z.im : ℝ) : ℂ) * I
  invFun w := ((w.re / α : ℝ) : ℂ) + ((w.im / β : ℝ) : ℂ) * I
  left_inv z := by
    apply Complex.ext <;> simp [hα, hβ]
  right_inv w := by
    apply Complex.ext <;> simp [hα, hβ, mul_div_cancel₀]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The stretch `x + iy ↦ αx + iβy`. -/
theorem td_Stretch_apply {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (z : ℂ) :
    td_Stretch α β hα hβ z = ((α * z.re : ℝ) : ℂ) + ((β * z.im : ℝ) : ℂ) * I := rfl

/-- The stretch as the affine map `z ↦ ((α+β)/2) z + ((α-β)/2) z̄`. -/
theorem td_Stretch_eq_affine {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (td_Stretch α β hα hβ : ℂ → ℂ) =
      fun z => ((α + β) / 2 : ℂ) * z + ((α - β) / 2 : ℂ) * conj z + 0 := by
  funext z
  rw [td_Stretch_apply]
  apply Complex.ext <;> simp <;> ring

/-- The stretch is `α/β`-q.c. on the plane when `0 < β ≤ α`. -/
theorem td_Stretch_isKQC {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hβ0 : 0 < β) (hαβ : β ≤ α) :
    IsKQC (td_Stretch α β hα hβ) univ (α / β) := by
  have hA : ‖((α + β) / 2 : ℂ)‖ = (α + β) / 2 := by
    rw [show ((α + β) / 2 : ℂ) = (((α + β) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hB : ‖((α - β) / 2 : ℂ)‖ = (α - β) / 2 := by
    rw [show ((α - β) / 2 : ℂ) = (((α - β) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hlt : ‖((α - β) / 2 : ℂ)‖ < ‖((α + β) / 2 : ℂ)‖ := by rw [hA, hB]; linarith
  have h := isKQC_of_isC1Quasiconformal (affine_isC1Quasiconformal (C := 0) hlt).1
  have e1 : (α + β) / 2 + (α - β) / 2 = α := by ring
  have e2 : (α + β) / 2 - (α - β) / 2 = β := by ring
  rw [hA, hB, e1, e2] at h
  rw [td_Stretch_eq_affine]
  exact h

/-- The stretch by `(a₂/a₁, b₂/b₁)` maps the rectangle `R(a₁, b₁)` onto `R(a₂, b₂)`. -/
theorem td_Stretch_image_rectangle {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂)
    (hb₂ : 0 < b₂) :
    td_Stretch (a₂ / a₁) (b₂ / b₁) (div_pos ha₂ ha₁).ne' (div_pos hb₂ hb₁).ne' '' rectangle a₁ b₁ =
      rectangle a₂ b₂ := by
  have hα : 0 < a₂ / a₁ := div_pos ha₂ ha₁
  have hβ : 0 < b₂ / b₁ := div_pos hb₂ hb₁
  ext w
  simp only [mem_image, rectangle, mem_ofPred_eq, td_Stretch_apply]
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    refine ⟨mul_pos hα h1, ?_, mul_pos hβ h3, ?_⟩
    · calc a₂ / a₁ * z.re < a₂ / a₁ * a₁ := mul_lt_mul_of_pos_left h2 hα
        _ = a₂ := by field_simp
    · calc b₂ / b₁ * z.im < b₂ / b₁ * b₁ := mul_lt_mul_of_pos_left h4 hβ
        _ = b₂ := by field_simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨((w.re / (a₂ / a₁) : ℝ) : ℂ) + ((w.im / (b₂ / b₁) : ℝ) : ℂ) * I, ?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      refine ⟨div_pos h1 hα, ?_, div_pos h3 hβ, ?_⟩
      · rw [div_lt_iff₀ hα]; field_simp; linarith
      · rw [div_lt_iff₀ hβ]; field_simp; linarith
    · have hsimp : ∀ x y : ℝ, (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I).re = x ∧
          (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I).im = y := fun x y => by simp
      apply Complex.ext
      · rw [(hsimp _ _).1, (hsimp _ _).1]
        field_simp
      · rw [(hsimp _ _).2, (hsimp _ _).2]
        field_simp


/-! #### The half-plane map `f : ℍ → ℍ`, `(∞, -1, 0, 1) ↦ (∞, -1, 0, λ(K))` -/

/-- The vertices `(∞, -1, 0, ρ)`. -/
def td_Vert (ρ : ℝ) : Fin 4 → ExtPlane :=
  ![extInf, (((-1 : ℝ) : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane), (((ρ : ℝ) : ℂ) : ExtPlane)]

/-- The quadrilateral `ℍ(∞, -1, 0, ρ)`, of modulus `Λ(ρ)`. -/
def td_Quad {ρ : ℝ} (hρ : 0 < ρ) : TopQuad := ⟨upperHalf, td_Vert ρ, isTopQuad_upperHalf_lambda hρ⟩

/-- The modulus of `ℍ(∞, -1, 0, ρ)` is `Λ(ρ)`. -/
theorem td_Quad_modulus {ρ : ℝ} (hρ : 0 < ρ) : (td_Quad hρ).modulus = quadLambda ρ := rfl

/-- The vertices of `ℍ(∞, -1, 0, ρ)` lie in the closure of `ℍ` in `ℂ̄`. -/
theorem td_Vert_mem_closure {ρ : ℝ} (hρ : 0 < ρ) (i : Fin 4) :
    td_Vert ρ i ∈ closure (toExt upperHalf) :=
  frontier_subset_closure ((isTopQuad_upperHalf_lambda hρ).2.1 i)

/-- A `K`-q.c. self-map of `ℍ` whose boundary extension takes `∞, -1, 0, 1` to `∞, -1, 0, λ(K)` (standard maps of Theorem 1.1 and an affine stretch). -/
theorem td_half_plane_map {K : ℝ} (hK : 1 ≤ K) :
    ∃ (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), IsKQC f upperHalf K ∧ f '' upperHalf = upperHalf ∧
      IsHomeoExtension f upperHalf upperHalf F ∧
      ∀ i, F (td_Vert 1 i) = td_Vert (lambdaInv K) i := by
  obtain ⟨hρ, hΛρ⟩ := td_quadLambda_lambdaInv (by linarith : (0 : ℝ) < K)
  obtain ⟨a₁, b₁, hQ₁⟩ := thm1_1_exists_rectangle (td_Quad one_pos)
  obtain ⟨a₂, b₂, hQ₂⟩ := thm1_1_exists_rectangle (td_Quad hρ)
  have hm₁ : a₁ / b₁ = 1 := by
    rw [← modulus_eq_of_equivRect _ hQ₁, td_Quad_modulus, b4_quadLambda_one]
  have hm₂ : a₂ / b₂ = K := by
    rw [← modulus_eq_of_equivRect _ hQ₂, td_Quad_modulus, hΛρ]
  obtain ⟨φ₁, ha₁, hb₁, hφ₁', Φ₁, hΦ₁', hΦ₁v'⟩ := hQ₁
  obtain ⟨φ₂, ha₂, hb₂, hφ₂', Φ₂, hΦ₂', hΦ₂v'⟩ := hQ₂
  have hφ₁ : IsConformalOnto φ₁ upperHalf (rectangle a₁ b₁) := hφ₁'
  have hΦ₁ : IsHomeoExtension φ₁ upperHalf (rectangle a₁ b₁) Φ₁ := hΦ₁'
  have hΦ₁v : ∀ i, Φ₁ (td_Vert 1 i) = rectVert a₁ b₁ i := hΦ₁v'
  have hφ₂ : IsConformalOnto φ₂ upperHalf (rectangle a₂ b₂) := hφ₂'
  have hΦ₂ : IsHomeoExtension φ₂ upperHalf (rectangle a₂ b₂) Φ₂ := hΦ₂'
  have hΦ₂v : ∀ i, Φ₂ (td_Vert (lambdaInv K) i) = rectVert a₂ b₂ i := hΦ₂v'
  -- the stretch `e`, of dilatation `α/β = K`
  have hα : 0 < a₂ / a₁ := div_pos ha₂ ha₁
  have hβ : 0 < b₂ / b₁ := div_pos hb₂ hb₁
  have hαβ : (a₂ / a₁) / (b₂ / b₁) = K := by
    rw [← hm₂, show a₂ / b₂ = (a₂ / b₂) / (a₁ / b₁) by rw [hm₁, div_one]]
    field_simp
  have hβα : b₂ / b₁ ≤ a₂ / a₁ := by
    have h' : a₂ / a₁ = K * (b₂ / b₁) := by rw [← hαβ]; field_simp
    rw [h']
    nlinarith
  set e := td_Stretch (a₂ / a₁) (b₂ / b₁) hα.ne' hβ.ne' with hedef
  have heK : IsKQC e univ K := hαβ ▸ td_Stretch_isKQC hα.ne' hβ.ne' hβ hβα
  have heR : e '' rectangle a₁ b₁ = rectangle a₂ b₂ := td_Stretch_image_rectangle ha₁ hb₁ ha₂ hb₂
  -- `f = ψ₂ ∘ e ∘ φ₁`
  set ψ₂ := Function.invFunOn φ₂ upperHalf with hψ₂def
  have hψ₂ : IsConformalOnto ψ₂ (rectangle a₂ b₂) upperHalf := hφ₂.symm isOpen_upperHalf
  have hq₁ := isKQC_one_of_conformal isOpen_upperHalf hφ₁
  have hqe : IsKQC e (rectangle a₁ b₁) K :=
    ac_t_isKQC_restrict heK (isOpen_rectangle _ _) (subset_univ _)
  have hq₂ := isKQC_one_of_conformal (isOpen_rectangle _ _) hψ₂
  have h1 : IsKQC (e ∘ φ₁) upperHalf (1 * K) := thm7_1_comp hq₁ hqe hφ₁.2.2.le
  have hmaps : MapsTo (e ∘ φ₁) upperHalf (rectangle a₂ b₂) := by
    intro z hz
    rw [← heR]
    exact mem_image_of_mem e (hφ₁.mapsTo hz)
  have h2 : IsKQC (ψ₂ ∘ (e ∘ φ₁)) upperHalf (1 * K * 1) :=
    thm7_1_comp h1 hq₂ (by rw [image_comp, hφ₁.2.2, heR])
  rw [one_mul, mul_one] at h2
  have himg : (ψ₂ ∘ (e ∘ φ₁)) '' upperHalf = upperHalf := by
    rw [image_comp, image_comp, hφ₁.2.2, heR, hψ₂.2.2]
  -- the extension `F = Ψ₂ ∘ E ∘ Φ₁`
  set E : ExtPlane ≃ₜ ExtPlane := e.onePointCongr with hEdef
  have hE : ∀ w : ℂ, E (w : ExtPlane) = ((e w : ℂ) : ExtPlane) := fun w => rfl
  have hEimg : E '' toExt (rectangle a₁ b₁) = toExt (rectangle a₂ b₂) := by
    rw [← heR]
    simp only [toExt, image_image, hE]
  have hext₁ : IsHomeoExtension (e ∘ φ₁) upperHalf (rectangle a₂ b₂) (E ∘ Φ₁) :=
    hΦ₁.comp_homeomorph hφ₁.mapsTo E (fun w _ => hE w) hEimg
  have hΨ₂ := isHomeoExtension_invFunOn hφ₂ hΦ₂
  have hF := hΨ₂.comp hext₁ hmaps
  refine ⟨_, _, h2, himg, hF, fun i => ?_⟩
  -- vertices: `Φ₁(v₁ i) = R₁ i`, `E(R₁ i) = R₂ i`, `Ψ₂(R₂ i) = v₂ i`
  have hER : E (rectVert a₁ b₁ i) = rectVert a₂ b₂ i := by
    have ha1 := ha₁.ne'
    have hb1 := hb₁.ne'
    fin_cases i
    · show E ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
      rw [hE]; congr 1; rw [hedef, td_Stretch_apply]; apply Complex.ext <;> simp
    · show E (((a₁ : ℝ) : ℂ) : ExtPlane) = (((a₂ : ℝ) : ℂ) : ExtPlane)
      rw [hE]; congr 1; rw [hedef, td_Stretch_apply]; apply Complex.ext <;> simp [ha1]
    · show E (((a₁ : ℂ) + (b₁ : ℂ) * I : ℂ) : ExtPlane) = (((a₂ : ℂ) + (b₂ : ℂ) * I : ℂ) : ExtPlane)
      rw [hE]; congr 1; rw [hedef, td_Stretch_apply]; apply Complex.ext <;> simp [ha1, hb1]
    · show E (((b₁ : ℂ) * I : ℂ) : ExtPlane) = (((b₂ : ℂ) * I : ℂ) : ExtPlane)
      rw [hE]; congr 1; rw [hedef, td_Stretch_apply]; apply Complex.ext <;> simp [hb1]
  have hΨ : Function.invFunOn Φ₂ (closure (toExt upperHalf)) (rectVert a₂ b₂ i) =
      td_Vert (lambdaInv K) i := by
    rw [← hΦ₂v i]
    exact hΦ₂.2.2.1.leftInvOn_invFunOn (td_Vert_mem_closure hρ i)
  show Function.invFunOn Φ₂ (closure (toExt upperHalf)) (E (Φ₁ (td_Vert 1 i))) = _
  have h1i : Φ₁ (td_Vert 1 i) = rectVert a₁ b₁ i := hΦ₁v i
  rw [h1i, hER, hΨ]


/-- **The extremal map**: `g ∈ 𝓕` with `g(-1) = -λ(K)`. -/
theorem td_sharp_map {K : ℝ} (hK : 1 ≤ K) :
    ∃ g : ℂ → ℂ, IsKQCNormalizedPlane g K ∧ g (-1) = -(lambdaInv K : ℂ) := by
  obtain ⟨f, F, hfK, hfimg, hF, hFv⟩ := td_half_plane_map hK
  have hFinf : F extInf = extInf := hFv 0
  -- `f → ∞` at `∞` in `ℍ`
  have hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    have hinfmem : extInf ∈ closure (toExt upperHalf) :=
      frontier_subset_closure infty_mem_frontier_upperHalf
    have hcoe : Tendsto (fun z : ℂ => (z : ExtPlane)) (cocompact ℂ ⊓ 𝓟 upperHalf)
        (𝓝[closure (toExt upperHalf)] extInf) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h := OnePoint.tendsto_coe_infty (X := ℂ)
        rw [coclosedCompact_eq_cocompact] at h
        exact h.mono_left inf_le_left
      · filter_upwards [mem_inf_of_right (mem_principal_self upperHalf)] with z hz
        exact subset_closure ⟨z, hz, rfl⟩
    have h2 : Tendsto (fun z : ℂ => F (z : ExtPlane)) (cocompact ℂ ⊓ 𝓟 upperHalf) (𝓝 extInf) := by
      have h := (hF.2.1 extInf hinfmem).tendsto.comp hcoe
      rwa [hFinf] at h
    have h3 : Tendsto (fun z : ℂ => ((f z : ℂ) : ExtPlane)) (cocompact ℂ ⊓ 𝓟 upperHalf)
        (𝓝 extInf) := by
      refine h2.congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self upperHalf)] with z hz
      exact hF.1 z hz
    have hcc : comap ((↑) : ℂ → ExtPlane) (𝓝 extInf) = cocompact ℂ := by
      rw [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact]
    have h4 : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (comap ((↑) : ℂ → ExtPlane) (𝓝 extInf)) :=
      tendsto_comap_iff.2 h3
    rwa [hcc] at h4
  obtain ⟨g, hgK, hgs, hgf, -⟩ := qc_reflection_extension hfK hfimg hinf
  have hgc : Continuous g := continuousOn_univ.1 hgK.2.2.1.1
  -- boundary values `g(x) = F(x)`
  have hbv : ∀ x : ℝ, (((g x : ℂ)) : ExtPlane) = F ((x : ℂ) : ExtPlane) := by
    intro x
    have hxcl : (x : ℂ) ∈ closure upperHalf := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
      · show 0 < ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        linarith
      · rw [dist_eq_norm, show (x : ℂ) - ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * I) =
          -(((ε / 2 : ℝ) : ℂ) * I) by ring, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
    have : (𝓝[upperHalf] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
    have hxmem : ((x : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
      frontier_subset_closure (ofReal_mem_frontier_upperHalf x)
    have hcoe : Tendsto (fun z : ℂ => (z : ExtPlane)) (𝓝[upperHalf] (x : ℂ))
        (𝓝[closure (toExt upperHalf)] ((x : ℂ) : ExtPlane)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(OnePoint.continuous_coe.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact subset_closure ⟨z, hz, rfl⟩
    have hA : Tendsto (fun z : ℂ => F (z : ExtPlane)) (𝓝[upperHalf] (x : ℂ))
        (𝓝 (F ((x : ℂ) : ExtPlane))) :=
      (hF.2.1 _ hxmem).tendsto.comp hcoe
    have hB : Tendsto (fun z : ℂ => ((g z : ℂ) : ExtPlane)) (𝓝[upperHalf] (x : ℂ))
        (𝓝 ((g x : ℂ) : ExtPlane)) :=
      ((OnePoint.continuous_coe.comp hgc).tendsto _).mono_left nhdsWithin_le_nhds
    have hAB : (fun z : ℂ => F (z : ExtPlane)) =ᶠ[𝓝[upperHalf] (x : ℂ)]
        (fun z : ℂ => ((g z : ℂ) : ExtPlane)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hF.1 z hz, hgf hz]
    exact tendsto_nhds_unique hB (hA.congr' hAB)
  have hgm1 : g (-1) = -1 := by
    have h := hbv (-1)
    have h' : F ((((-1 : ℝ) : ℂ)) : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane) := hFv 1
    rw [h'] at h
    have := OnePoint.coe_injective h
    simpa using this
  have hg0 : g 0 = 0 := by
    have h := hbv 0
    have h' : F (((0 : ℂ)) : ExtPlane) = ((0 : ℂ) : ExtPlane) := hFv 2
    rw [Complex.ofReal_zero, h'] at h
    exact OnePoint.coe_injective h
  have hg1 : g 1 = (lambdaInv K : ℂ) := by
    have h := hbv 1
    have h' : F ((((1 : ℝ) : ℂ)) : ExtPlane) = (((lambdaInv K : ℝ) : ℂ) : ExtPlane) := hFv 3
    rw [h'] at h
    have := OnePoint.coe_injective h
    simpa using this
  -- `G(z) = -g(-z)`
  obtain ⟨hG, hGs⟩ := td_affine_comp hgK hgs (α := -1) (γ := -1) 0 0 (by norm_num) (by norm_num)
  refine ⟨fun z => -1 * g (-1 * z + 0) + 0, ⟨hG, hGs, ?_, ?_⟩, ?_⟩
  · simp [hg0]
  · show -1 * g (-1 * 1 + 0) + 0 = 1
    simp [hgm1]
  · show -1 * g (-1 * -1 + 0) + 0 = -(lambdaInv K : ℂ)
    simp [hg1]

/-- **Lemma 15.2**: for `f ∈ 𝓕`, `|f(e^{iθ})| ≤ sup_{g ∈ 𝓕} |g(-1)|`. -/
theorem lemma15_2 {f : ℂ → ℂ} {K : ℝ} (hf : IsKQCNormalizedPlane f K) (θ : ℝ) :
    ‖f (exp (θ * I))‖ ≤ sSup {r : ℝ | ∃ g : ℂ → ℂ, IsKQCNormalizedPlane g K ∧ r = ‖g (-1)‖} := by
  obtain ⟨g, hg, hg1⟩ := td_sharp_map hf.1.2.1
  have hbdd : BddAbove {r : ℝ | ∃ g : ℂ → ℂ, IsKQCNormalizedPlane g K ∧ r = ‖g (-1)‖} := by
    refine ⟨lambdaInv K, ?_⟩
    rintro _ ⟨g', hg', rfl⟩
    have h := td_hyp_of_teich hg' π
    rwa [exp_pi_mul_I] at h
  have hlam : 0 ≤ lambdaInv K := zero_le_one.trans (td_one_le_lambdaInv hf.1.2.1)
  calc ‖f (exp (θ * I))‖ ≤ lambdaInv K := td_hyp_of_teich hf θ
    _ = ‖g (-1)‖ := by rw [hg1, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlam]
    _ ≤ _ := le_csSup hbdd ⟨g, hg, rfl⟩

/-! ### Batch-4 interface (coordinator 553e2d): Teichmüller-ring exhaustion, separation, `λ(K)` bounds -/

/-- The final inequality of (15.22): `π ≤ K · 2μ(√(r/(r+1)))` means `π ≤ K π Λ(1/r)` ((5.18) with `ρ = 1/r`), hence
`Λ(r) = 1/Λ(1/r) ≤ K` ((5.20)). -/
theorem b4_quadLambda_le_of_mu {K r : ℝ} (hr : 0 < r)
    (h : π ≤ K * (2 * grotzschMu (Real.sqrt (r / (r + 1))))) : quadLambda r ≤ K := by
  have hr' : 0 < 1 / r := one_div_pos.2 hr
  have h18 := eq5_18 hr'
  have harg : 1 / (1 + 1 / r) = r / (r + 1) := by
    field_simp
  rw [harg] at h18
  have h2μ : 2 * grotzschMu (Real.sqrt (r / (r + 1))) = π * quadLambda (1 / r) := by
    rw [h18]
    field_simp
  rw [h2μ] at h
  have h1 : 1 ≤ K * quadLambda (1 / r) := by
    nlinarith [Real.pi_pos]
  calc quadLambda r = quadLambda r * 1 := (mul_one _).symm
    _ ≤ quadLambda r * (K * quadLambda (1 / r)) :=
        mul_le_mul_of_nonneg_left h1 (b4_num_quadLambda_pos hr).le
    _ = K * (quadLambda r * quadLambda (1 / r)) := by ring
    _ = K := by rw [eq5_20 hr, mul_one]

/-- Choice of the radius: some `ρ ∈ (r₀, 1)` has `μ(r₀) - ε < μ(r₀/ρ)` (`r₀ = tmR0 R`; continuity of `μ` at `r₀`). -/
theorem b4_ex_exists_rho {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ ρ : ℝ, tmR0 R < ρ ∧ ρ < 1 ∧ grotzschMu (tmR0 R) - ε < grotzschMu (tmR0 R / ρ) := by
  have hr0 := tmR0_pos hR
  have hr1 := tmR0_lt_one hR
  have hlim : Tendsto (fun ρ : ℝ => tmR0 R / ρ) (𝓝[<] 1) (𝓝 (tmR0 R)) := by
    have h : Tendsto (fun ρ : ℝ => tmR0 R / ρ) (𝓝 1) (𝓝 (tmR0 R / 1)) :=
      tendsto_const_nhds.div tendsto_id one_ne_zero
    rw [div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hcontAt : ContinuousAt grotzschMu (tmR0 R) :=
    s15_grotzschMu_continuousOn.continuousAt (Ioo_mem_nhds hr0 hr1)
  have hev1 : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), grotzschMu (tmR0 R) - ε < grotzschMu (tmR0 R / ρ) :=
    (hcontAt.tendsto.comp hlim).eventually (lt_mem_nhds (by linarith))
  obtain ⟨ρ, h1, h2⟩ := (hev1.and (Ioo_mem_nhdsLT hr1)).exists
  exact ⟨ρ, h2.1, h2.2, h1⟩

/-- For `ρ > 0`, `z ↦ ρ z` maps the disc `|z| < 1/ρ` into `Δ`. -/
theorem b4_ex_mul_mem_unitDisc {ρ : ℝ} (hρ0 : 0 < ρ) :
    MapsTo (fun z : ℂ => (ρ : ℂ) * z) (ball 0 (1 / ρ)) unitDisc := by
  intro z hz
  have hz' : ‖z‖ < 1 / ρ := mem_ball_zero_iff.1 hz
  rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  calc ρ * ‖z‖ < ρ * (1 / ρ) := mul_lt_mul_of_pos_left hz' hρ0
    _ = 1 := by field_simp

/-- The rescaled map `z ↦ ψ(ρ z)` (`ψ = tmPsi R`, `ρ > 0`) is conformal on the disc `|z| < 1/ρ`. -/
theorem b4_ex_phi_conformal {R ρ : ℝ} (hR : 0 < R) (hρ0 : 0 < ρ) :
    IsConformalOnto (fun z : ℂ => tmPsi R ((ρ : ℂ) * z)) (ball 0 (1 / ρ))
      ((fun z : ℂ => tmPsi R ((ρ : ℂ) * z)) '' ball 0 (1 / ρ)) := by
  have hmaps := b4_ex_mul_mem_unitDisc hρ0
  refine ⟨(tmPsi_differentiableOn R).comp (differentiable_id.const_mul _).differentiableOn hmaps, ?_, rfl⟩
  intro a ha b hb h
  exact mul_left_cancel₀ (ofReal_ne_zero.2 hρ0.ne') (tmPsi_injOn hR (hmaps ha) (hmaps hb) h)

/-- `ℂ̄ ∖ g(B_s) = g([0, s]) ∪ (ℂ̄ ∖ g(Δ))`, a union of two disjoint closed sets, when `g` is continuous and
injective on `D ⊇ Δ`, `g(Δ)` is open and `s < 1`. -/
theorem b4_ex_compl_decomp {g : ℂ → ℂ} {D : Set ℂ} (hc : ContinuousOn g D) (hi : InjOn g D)
    (hΔD : unitDisc ⊆ D) (hΔo : IsOpen (g '' unitDisc)) {s : ℝ} (hs1 : s < 1) :
    (toExt (g '' grotzschDomain s))ᶜ =
        toExt (g '' {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s}) ∪ (toExt (g '' unitDisc))ᶜ ∧
      IsClosed (toExt (g '' {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s})) ∧
      IsClosed (toExt (g '' unitDisc))ᶜ ∧
      Disjoint (toExt (g '' {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s})) (toExt (g '' unitDisc))ᶜ := by
  have hTeq := s15_ring_slit_eq s
  set T : Set ℂ := {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ s} with hT
  have hTc : IsCompact T := by
    rw [hTeq]
    exact isCompact_Icc.image continuous_ofReal
  have hTΔ : T ⊆ unitDisc := by
    rw [hTeq]
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.trans_lt hs1
  have hTD : T ⊆ D := hTΔ.trans hΔD
  have hPS : toExt (g '' T) ⊆ (toExt (g '' grotzschDomain s))ᶜ := by
    rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ ⟨v, ⟨u', hu', rfl⟩, hv⟩
    have huu : u' = u := hi (hΔD hu'.1) (hTD hu) (OnePoint.coe_injective hv)
    subst huu
    exact hu'.2 hu
  have hQS : (toExt (g '' unitDisc))ᶜ ⊆ (toExt (g '' grotzschDomain s))ᶜ :=
    compl_subset_compl.2 (image_mono (image_mono fun w (hw : w ∈ grotzschDomain s) => hw.1))
  have hSPQ : (toExt (g '' grotzschDomain s))ᶜ ⊆ toExt (g '' T) ∪ (toExt (g '' unitDisc))ᶜ := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (extInf_notMem_toExt _)
    | coe w =>
      by_cases hw : w ∈ g '' unitDisc
      · left
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨g u, ⟨u, ?_, rfl⟩, rfl⟩
        by_contra hnot
        exact hx ⟨g u, ⟨u, ⟨hu, hnot⟩, rfl⟩, rfl⟩
      · right
        exact fun h' => hw (coe_mem_toExt_iff.1 h')
  refine ⟨subset_antisymm hSPQ (union_subset hPS hQS),
    ((hTc.image_of_continuousOn (hc.mono hTD)).image OnePoint.continuous_coe).isClosed,
    isClosed_compl_toExt hΔo, ?_⟩
  rw [disjoint_compl_right_iff_subset]
  exact image_mono (image_mono hTΔ)

/-- A point `ζ ∈ Δ` with `ψ(ζ)` real is the real number `a = Re ζ ∈ (-1, 1)`, and `ψ(ζ) = -4Ra/(1-a)²`. -/
theorem b4_ex_real_preimage {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : ζ ∈ unitDisc) {x : ℝ}
    (hψ : tmPsi R ζ = (x : ℂ)) :
    ζ = (ζ.re : ℂ) ∧ -1 < ζ.re ∧ ζ.re < 1 ∧ -4 * R * ζ.re / (1 - ζ.re) ^ 2 = x := by
  have hb : ζ.im = 0 := tmA_im_eq_zero hR hζ (by rw [hψ, Complex.ofReal_im])
  have hn := gzA_mem_unitDisc_iff.mp hζ
  rw [hb] at hn
  have hζr : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [hb])
  rw [hζr, tmA_psi_ofReal] at hψ
  exact ⟨hζr, by nlinarith, by nlinarith, Complex.ofReal_injective hψ⟩

/-- Every `x ∈ [-1, 0]` is `ψ(a)` for some `a ∈ [0, r₀]` (`ψ = tmPsi R`, `r₀ = tmR0 R`). -/
theorem b4_ex_mem_image_slit {R : ℝ} (hR : 0 < R) {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x ≤ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ tmR0 R ∧ tmPsi R (a : ℂ) = (x : ℂ) := by
  have hw : ¬ ((x : ℂ).im = 0 ∧ R ≤ (x : ℂ).re) := by
    rintro ⟨-, h⟩
    rw [Complex.ofReal_re] at h
    linarith
  obtain ⟨ζ, hζ, hψ⟩ := tmA_exists hR hw
  obtain ⟨hζr, -, ha1, hx⟩ := b4_ex_real_preimage hR hζ hψ
  obtain ⟨h0, hr⟩ := (tmA_real_iff hR ha1).mp ⟨by rw [hx]; exact hx1, by rw [hx]; exact hx0⟩
  exact ⟨ζ.re, h0, hr, by rw [← hζr, hψ]⟩

/-- `ψ(Δ)` misses `[R, +∞)` (`ψ = tmPsi R`). -/
theorem b4_ex_psi_ne {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : ζ ∈ unitDisc) {x : ℝ} (hx : R ≤ x) :
    tmPsi R ζ ≠ (x : ℂ) := by
  intro hψ
  obtain ⟨-, ha0, ha1, hx'⟩ := b4_ex_real_preimage hR hζ hψ
  exact tmA_not_ge hR ha0 ha1 (by rw [hx']; exact hx)

/-- Exhaustion of the Teichmüller domain `T_R` by bounded doubly connected domains: for `ε > 0` there is a doubly
connected `B` with `B̄ ⊆ ℂ` and `M(B) ≥ π Λ(R) - ε` (`π Λ(R) = M(T_R)`, (5.17)) whose complement in `ℂ̄` is the union of
two disjoint closed sets, one containing `[-1, 0]` and the other containing `[R, +∞)` and `∞`.  (Take
`B = ψ(B(0, ρ) ∖ [0, r₀])` with `ψ = tmPsi R`, `r₀ = tmR0 R` and `ρ < 1` close to `1`: `M(B) = μ(r₀/ρ) → μ(r₀)`.) -/
theorem b4_teich_exhaust {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ B : Set ℂ, IsDoublyConnected B ∧ closure (toExt B) ⊆ toExt univ ∧
      ENNReal.ofReal (π * quadLambda R - ε) ≤ dcModulus B ∧
      ∃ P Q : Set ExtPlane, (toExt B)ᶜ = P ∪ Q ∧ IsClosed P ∧ IsClosed Q ∧ Disjoint P Q ∧
        (∀ x : ℝ, -1 ≤ x → x ≤ 0 → (((x : ℝ) : ℂ) : ExtPlane) ∈ P) ∧
        (∀ x : ℝ, R ≤ x → (((x : ℝ) : ℂ) : ExtPlane) ∈ Q) ∧ extInf ∈ Q := by
  have hr0 := tmR0_pos hR
  obtain ⟨ρ, hρr, hρ1, hμ⟩ := b4_ex_exists_rho hR hε
  have hρ0 : 0 < ρ := hr0.trans hρr
  have hs0 : 0 < tmR0 R / ρ := div_pos hr0 hρ0
  have hs1 : tmR0 R / ρ < 1 := (div_lt_one hρ0).2 hρr
  have h1ρ : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0, one_mul]; exact hρ1
  have hΔD : unitDisc ⊆ ball (0 : ℂ) (1 / ρ) := ball_subset_ball h1ρ.le
  have hconf := b4_ex_phi_conformal hR hρ0
  have hK := isKQC_one_of_conformal isOpen_ball hconf
  have hhom := hK.2.2.1
  have hB := grotzschDomain_doublyConnected hs0 hs1
  have hBΔ : grotzschDomain (tmR0 R / ρ) ⊆ unitDisc := fun w hw => hw.1
  have hBc : grotzschDomain (tmR0 R / ρ) ⊆ closedBall 0 1 :=
    fun w hw => mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 hw.1).le
  have hBD : closure (toExt (grotzschDomain (tmR0 R / ρ))) ⊆ toExt (ball (0 : ℂ) (1 / ρ)) :=
    (nf_e_closure_toExt_subset (isCompact_closedBall (0 : ℂ) 1) hBc).trans
      (image_mono (closedBall_subset_ball h1ρ))
  obtain ⟨hceq, hPc, hQc, hPQ⟩ := b4_ex_compl_decomp hhom.1 hhom.2.1 hΔD
    (aqc_isOpen_image_of_isHomeomorphOnto hhom (isOpen_image_of_isKQC hK) hΔD isOpen_ball) hs1
  refine ⟨_, aqc_isDoublyConnected_image isOpen_ball hhom (isOpen_image_of_isKQC hK) hB.1 hBD,
    (nf_e_closure_toExt_subset ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
      (hhom.1.mono (closedBall_subset_ball h1ρ))) (image_mono hBc)).trans (image_mono (subset_univ _)),
    ?_, _, _, hceq, hPc, hQc, hPQ, ?_, ?_, extInf_mem_compl_toExt _⟩
  · have hmod := thm2_2_dcModulus_conformal_invariant hB.1
      ⟨_, hconf.1.mono (hBΔ.trans hΔD), hconf.2.1.mono (hBΔ.trans hΔD), rfl⟩
    rw [← hmod, ← ENNReal.ofReal_toReal hB.2.ne, eq5_17 hR, thm5_2_modulus_teichmullerDomain hR,
      mul_div_cancel₀ _ Real.pi_ne_zero]
    exact ENNReal.ofReal_le_ofReal hμ.le
  · intro x hx1 hx0
    obtain ⟨a, ha0, har, ha⟩ := b4_ex_mem_image_slit hR hx1 hx0
    refine ⟨_, ⟨((a / ρ : ℝ) : ℂ), ⟨by simp, div_nonneg ha0 hρ0.le, ?_⟩, rfl⟩, ?_⟩
    · rw [Complex.ofReal_re]
      exact div_le_div_of_nonneg_right har hρ0.le
    · dsimp only
      rw [ofReal_div, mul_div_cancel₀ _ (ofReal_ne_zero.2 hρ0.ne'), ha]
  · intro x hx
    rw [coe_mem_compl_toExt_iff]
    rintro ⟨z, hz, hzx⟩
    exact b4_ex_psi_ne hR (b4_ex_mul_mem_unitDisc hρ0 (hΔD hz)) hx hzx

/-- In a union `A ∪ B` of two disjoint closed sets, a point of `A` and a point of `B` have different connected
components (the component of `x ∈ A` is preconnected, hence contained in `A` or in `B`, and it meets `A`). -/
theorem b4_sep_connectedComponentIn_ne {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : Disjoint A B) {x y : X} (hx : x ∈ A) (hy : y ∈ B) :
    connectedComponentIn (A ∪ B) x ≠ connectedComponentIn (A ∪ B) y := by
  intro heq
  have hC := isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_connectedComponentIn (x := x) (F := A ∪ B)) A B hA hB
    (connectedComponentIn_subset _ _) (by rw [hAB.inter_eq, inter_empty])
  have hxC : x ∈ connectedComponentIn (A ∪ B) x := mem_connectedComponentIn (Or.inl hx)
  have hyC : y ∈ connectedComponentIn (A ∪ B) x := heq ▸ mem_connectedComponentIn (Or.inr hy)
  rcases hC with hC | hC
  · exact Set.disjoint_left.1 hAB (hC hyC) hy
  · exact Set.disjoint_left.1 hAB hx (hC hxC)

/-- The closed ray `[R, +∞]` of `ℂ̄` (the complement of the slit plane `ℂ ∖ [R, +∞)`) lies in any `Q ⊆ ℂ̄` that
contains `∞` and every real `x ≥ R`. -/
theorem b4_sep_ray_subset {R : ℝ} {Q : Set ExtPlane}
    (hQ₁ : ∀ x : ℝ, R ≤ x → (((x : ℝ) : ℂ) : ExtPlane) ∈ Q) (hQ₂ : extInf ∈ Q) :
    (toExt {w : ℂ | ¬ (w.im = 0 ∧ R ≤ w.re)})ᶜ ⊆ Q := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact hQ₂
  | coe w =>
    have hw : w.im = 0 ∧ R ≤ w.re := by
      by_contra hw
      exact hx (coe_mem_toExt_iff.2 hw)
    have hw' : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw.1])
    rw [hw']
    exact hQ₁ _ hw.2

/-- Separation under a homeomorphism `g` of the plane: if `ℂ̄ ∖ B = P ∪ Q` with `P, Q` disjoint and closed,
`[-1, 0] ⊆ P` and `[R, +∞) ∪ {∞} ⊆ Q`, then `g(B)` separates `{g(-1), g(0)}` from `{g(R), ∞}` (the complement of
`g(B)` is `ĝ(P) ∪ ĝ(Q)`; `ĝ([-1, 0])` and `ĝ([R, +∞]) ∋ ∞` are connected). -/
theorem b4_image_separates {g : ℂ → ℂ} (hg : IsHomeomorphOnto g univ univ) {R : ℝ} {B : Set ℂ}
    {P Q : Set ExtPlane} (hc : (toExt B)ᶜ = P ∪ Q) (hP : IsClosed P) (hQ : IsClosed Q) (hPQ : Disjoint P Q)
    (hP₁ : ∀ x : ℝ, -1 ≤ x → x ≤ 0 → (((x : ℝ) : ℂ) : ExtPlane) ∈ P)
    (hQ₁ : ∀ x : ℝ, R ≤ x → (((x : ℝ) : ℂ) : ExtPlane) ∈ Q) (hQ₂ : extInf ∈ Q) :
    SeparatesSets (g '' B) {((g (-1) : ℂ) : ExtPlane), ((g 0 : ℂ) : ExtPlane)}
      {((g (R : ℂ) : ℂ) : ExtPlane), extInf} := by
  obtain ⟨e, rfl⟩ := s13x_de_exists_homeomorph hg
  set E : ExtPlane ≃ₜ ExtPlane := e.onePointCongr with hE
  have hCeq : (toExt (e '' B))ᶜ = E '' P ∪ E '' Q := by
    rw [← s13x_de_image_toExt, ← E.image_compl, hc, image_union]
  have hEPc : IsClosed (E '' P) := E.isClosedMap P hP
  have hEQc : IsClosed (E '' Q) := E.isClosedMap Q hQ
  have hEPQ : Disjoint (E '' P) (E '' Q) := (disjoint_image_iff E.injective).2 hPQ
  -- the image of the segment `[-1, 0]`
  set I : Set ExtPlane := (fun x : ℝ => (((x : ℝ) : ℂ) : ExtPlane)) '' Icc (-1) 0
  have hIc : IsPreconnected (E '' I) :=
    (isPreconnected_Icc.image _ (OnePoint.continuous_coe.comp continuous_ofReal).continuousOn).image E
      E.continuous.continuousOn
  have hIC : E '' I ⊆ (toExt (e '' B))ᶜ := by
    rw [hCeq]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact Or.inl ⟨_, hP₁ x hx.1 hx.2, rfl⟩
  have hm1 : ((e (-1) : ℂ) : ExtPlane) ∈ E '' I :=
    ⟨_, ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩, by simp [hE]⟩
  have h0 : ((e 0 : ℂ) : ExtPlane) ∈ E '' I :=
    ⟨_, ⟨0, ⟨by norm_num, le_rfl⟩, rfl⟩, by simp [hE]⟩
  -- the image of the ray `[R, +∞]`
  set T : Set ExtPlane := (toExt {w : ℂ | ¬ (w.im = 0 ∧ R ≤ w.re)})ᶜ
  have hTc : IsPreconnected (E '' T) :=
    (t53_isConnected_compl_slit R).isPreconnected.image E E.continuous.continuousOn
  have hTC : E '' T ⊆ (toExt (e '' B))ᶜ := by
    rw [hCeq]
    exact (image_mono (b4_sep_ray_subset hQ₁ hQ₂)).trans subset_union_right
  have hRT : ((e (R : ℂ) : ℂ) : ExtPlane) ∈ E '' T :=
    ⟨((R : ℂ) : ExtPlane), fun h => (coe_mem_toExt_iff.1 h) ⟨by simp, by simp⟩, rfl⟩
  have hinf : extInf ∈ E '' T := ⟨extInf, extInf_notMem_toExt _, rfl⟩
  refine ⟨_, hIC h0, extInf, hTC hinf,
    insert_subset_iff.2 ⟨hIc.subset_connectedComponentIn h0 hIC hm1,
      singleton_subset_iff.2 (hIc.subset_connectedComponentIn h0 hIC h0)⟩,
    insert_subset_iff.2 ⟨hTc.subset_connectedComponentIn hinf hTC hRT,
      singleton_subset_iff.2 (hTc.subset_connectedComponentIn hinf hTC hinf)⟩, ?_⟩
  rw [hCeq]
  refine b4_sep_connectedComponentIn_ne hEPc hEQc hEPQ ⟨_, hP₁ 0 (by norm_num) le_rfl, ?_⟩ ⟨extInf, hQ₂, rfl⟩
  simp [hE]

/-- Three-point distortion by a `K`-q.c. map of the plane: if `F(-1) = -1`, `F(0) = 0` and `F(R) = R'` (`R, R' > 0`)
then `Λ(R) ≤ K Λ(R')`.  (Exhaust `T_R` by `b4_teich_exhaust`; Theorem 7.4, the separation `b4_image_separates` and
Teichmüller's Theorem 5.2 for `T_{R'}` give `π Λ(R) - ε ≤ K M(T_{R'}) = K π Λ(R')`.) -/
theorem b4_three_point_bound {F : ℂ → ℂ} {K R R' : ℝ} (hF : IsKQC F univ K) (hs : F '' univ = univ)
    (hR : 0 < R) (hR' : 0 < R') (h₁ : F (-1) = -1) (h₀ : F 0 = 0) (hRR' : F (R : ℂ) = (R' : ℂ)) :
    quadLambda R ≤ K * quadLambda R' := by
  have hhom : IsHomeomorphOnto F univ univ := by
    have h := hF.2.2.1
    rwa [hs] at h
  have hK0 : 0 ≤ K := zero_le_one.trans hF.2.1
  have hfin : dcModulus (teichmullerDomain R') ≠ ⊤ := by
    rw [tz_dcModulus_teichmullerDomain hR']
    exact ENNReal.ofReal_ne_top
  have hT : dcModulus (teichmullerDomain R') = ENNReal.ofReal (π * quadLambda R') := by
    rw [eq5_17 hR', mul_div_cancel₀ _ Real.pi_ne_zero, ENNReal.ofReal_toReal hfin]
  have hΛ' : 0 ≤ quadLambda R' := by
    rw [eq5_17 hR']
    exact div_nonneg ENNReal.toReal_nonneg Real.pi_pos.le
  suffices h : π * quadLambda R ≤ π * (K * quadLambda R') from le_of_mul_le_mul_left h Real.pi_pos
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨B, hB, hBcl, hBmod, P, Q, hc, hPc, hQc, hPQ, hP, hQ, hQi⟩ := b4_teich_exhaust hR hε
  obtain ⟨hB', hle, -⟩ := thm7_4_dcModulus_quasi_invariance hF hB hBcl
  have hsep := b4_image_separates hhom hc hPc hQc hPQ hP hQ hQi
  rw [h₁, h₀, hRR'] at hsep
  have hchain : ENNReal.ofReal (π * quadLambda R - ε) ≤ ENNReal.ofReal (K * (π * quadLambda R')) :=
    calc ENNReal.ofReal (π * quadLambda R - ε) ≤ dcModulus B := hBmod
      _ ≤ ENNReal.ofReal K * dcModulus (F '' B) := hle
      _ ≤ ENNReal.ofReal K * dcModulus (teichmullerDomain R') := by
          gcongr
          exact thm5_2_teichmuller hR' hB' hsep
      _ = ENNReal.ofReal (K * (π * quadLambda R')) := by rw [hT, ENNReal.ofReal_mul hK0]
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (mul_nonneg Real.pi_pos.le hΛ'))).1 hchain
  linarith

/-- (15.22): `|g(-1)| ≤ λ(K)` for all `g ∈ 𝓕`. -/
theorem eq15_22 {g : ℂ → ℂ} {K : ℝ} (hg : IsKQCNormalizedPlane g K) : ‖g (-1)‖ ≤ lambdaInv K := by
  obtain ⟨hqc, hs, h0, h1⟩ := hg
  have hhom : IsHomeomorphOnto g univ univ := by
    have h := hqc.2.2.1
    rwa [hs] at h
  have hK0 : 0 ≤ K := zero_le_one.trans hqc.2.1
  have hw : g (-1) ≠ 0 := by
    intro hw0
    have h := hqc.2.2.1.2.1 (mem_univ (-1 : ℂ)) (mem_univ (0 : ℂ)) (hw0.trans h0.symm)
    norm_num at h
  have hwpos : 0 < ‖g (-1)‖ := norm_pos_iff.2 hw
  refine b4_le_lambdaInv hwpos (b4_quadLambda_le_of_mu hwpos ?_)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨B, hB, hBcl, hBmod, P, Q, hc, hPc, hQc, hPQ, hP, hQ, hQi⟩ := b4_teich_exhaust one_pos hε
  rw [b4_quadLambda_one, mul_one] at hBmod
  obtain ⟨hB', hle, -⟩ := thm7_4_dcModulus_quasi_invariance hqc hB hBcl
  have hsep := b4_image_separates hhom hc hPc hQc hPQ hP hQ hQi
  rw [Complex.ofReal_one, h0, h1, Set.pair_comm] at hsep
  have h53 := thm5_3_teichmuller_modulus_theorem hw one_ne_zero hB' hsep
  rw [norm_one] at h53
  have hμ : 0 ≤ grotzschMu (Real.sqrt (‖g (-1)‖ / (‖g (-1)‖ + 1))) := ENNReal.toReal_nonneg
  have hchain : ENNReal.ofReal (π - ε) ≤
      ENNReal.ofReal (K * (2 * grotzschMu (Real.sqrt (‖g (-1)‖ / (‖g (-1)‖ + 1))))) :=
    calc ENNReal.ofReal (π - ε) ≤ dcModulus B := hBmod
      _ ≤ ENNReal.ofReal K * dcModulus (g '' B) := hle
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * grotzschMu (Real.sqrt (‖g (-1)‖ / (‖g (-1)‖ + 1)))) :=
          by gcongr
      _ = ENNReal.ofReal (K * (2 * grotzschMu (Real.sqrt (‖g (-1)‖ / (‖g (-1)‖ + 1))))) :=
          (ENNReal.ofReal_mul hK0).symm
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  linarith

/-- **Theorem 15.4** (Teichmüller, distortion of circles).  For a `K`-q.c. map `f` of the plane
onto itself, every `r > 0` and `z₀`,
`max_θ |f(z₀ + re^{iθ}) - f(z₀)| / min_θ |f(z₀ + re^{iθ}) - f(z₀)| ≤ λ(K)`. -/
theorem thm15_4_circle_distortion {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    sSup (range fun θ : ℝ => ‖f (z₀ + r * exp (θ * I)) - f z₀‖) ≤
      lambdaInv K * sInf (range fun θ : ℝ => ‖f (z₀ + r * exp (θ * I)) - f z₀‖) := by
  exact td_thm15_4_of_hyp (fun _ _ θ h => td_hyp_of_teich h θ) hf hs z₀ hr

/-- **Theorem 15.4** (sharpness): for every `K ≥ 1` the bound `λ(K)` is attained on the unit
circle by a `K`-q.c. map of the plane fixing `0` (obtained from the affine stretch of a square
onto a `K × 1` rectangle and reflection). -/
theorem thm15_4_sharp {K : ℝ} (hK : 1 ≤ K) :
    ∃ f : ℂ → ℂ, IsKQC f univ K ∧ f '' univ = univ ∧ f 0 = 0 ∧
      sSup (range fun θ : ℝ => ‖f (exp (θ * I))‖) =
        lambdaInv K * sInf (range fun θ : ℝ => ‖f (exp (θ * I))‖) := by
  obtain ⟨g, ⟨hqc, hs, h0, h1⟩, hg1⟩ := td_sharp_map hK
  refine ⟨g, hqc, hs, h0, le_antisymm ?_ ?_⟩
  · have h := thm15_4_circle_distortion hqc hs 0 one_pos
    simpa only [zero_add, Complex.ofReal_one, one_mul, h0, sub_zero] using h
  · set F : ℝ → ℝ := fun θ => ‖g (exp (θ * I))‖ with hF
    have hlam : 0 ≤ lambdaInv K := zero_le_one.trans (td_one_le_lambdaInv hK)
    have hgc : Continuous g := continuousOn_univ.1 hqc.2.2.1.1
    have hFc : Continuous F := by rw [hF]; fun_prop
    have hper : Function.Periodic F (2 * π) := by
      intro θ
      simp only [hF]
      have h := exp_mul_I_periodic (θ : ℂ)
      simp only at h
      push_cast
      rw [h]
    have hcpt : IsCompact (range F) := hper.compact_of_continuous (by positivity) hFc
    have hπ : F π = lambdaInv K := by
      simp only [hF, exp_pi_mul_I, hg1, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlam]
    have h0' : F 0 = 1 := by
      simp only [hF, Complex.ofReal_zero, zero_mul, Complex.exp_zero, h1, norm_one]
    calc lambdaInv K * sInf (range F) ≤ lambdaInv K * F 0 :=
          mul_le_mul_of_nonneg_left (csInf_le hcpt.bddBelow ⟨0, rfl⟩) hlam
      _ = F π := by rw [h0', mul_one, hπ]
      _ ≤ sSup (range F) := le_csSup hcpt.bddAbove ⟨π, rfl⟩

/-- Historical note: the constant `16` in Mori's theorem cannot be replaced by any smaller
absolute constant. -/
theorem mori_constant_sharp {c : ℝ} (hc : c < 16) :
    ∃ (K : ℝ) (f : ℂ → ℂ) (z₁ z₂ : ℂ), IsKQC f unitDisc K ∧ f '' unitDisc = unitDisc ∧ f 0 = 0 ∧
      z₁ ∈ unitDisc ∧ z₂ ∈ unitDisc ∧ z₁ ≠ z₂ ∧ c * ‖z₁ - z₂‖ ^ (1 / K) < ‖f z₁ - f z₂‖ := by
  sorry

/-! ### s15w track (coordinator 553e2d), part W1: Wang Chuanfang's estimate -/

/-- Upper bound `μ(r) + log r ≤ log 4` on `(0, 1)` (the upper half of (14.27)). -/
theorem w15_a_g_le_log4 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r + Real.log r ≤ Real.log 4 := by
  have h := em_upper hr₀ hr₁
  rw [Real.log_div (by norm_num) hr₀.ne'] at h
  linarith

/-- Lower bound `log 4 + log(1 - r²)/2 ≤ μ(r) + log r` on `(0, 1)` (the lower half of (14.27)). -/
theorem w15_a_g_ge {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Real.log 4 + Real.log (1 - r ^ 2) / 2 ≤ grotzschMu r + Real.log r := by
  have h := em_lower hr₀ hr₁
  have h1r2 : 0 < 1 - r ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 h1r2
  rw [Real.log_div (mul_pos (by norm_num) hsq).ne' hr₀.ne',
    Real.log_mul (by norm_num) hsq.ne', Real.log_sqrt h1r2.le] at h
  linarith

/-- A crude uniform lower bound `-1 ≤ μ(r) + log r` on `(0, 1)`. -/
theorem w15_a_g_ge_neg_one {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    -1 ≤ grotzschMu r + Real.log r := by
  have hμ : 0 ≤ grotzschMu r := ENNReal.toReal_nonneg
  rcases le_or_gt (r ^ 2) (15 / 16) with h | h
  · have h1 : Real.log (1 / 16) ≤ Real.log (1 - r ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h16 : Real.log (1 / 16) = -(2 * Real.log 4) := by
      rw [one_div, Real.log_inv, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have := w15_a_g_ge hr₀ hr₁
    linarith
  · have hr2 : 1 / 2 < r := by nlinarith
    have hl := Real.one_sub_inv_le_log_of_pos hr₀
    have hinv : r⁻¹ < 2 := by
      rw [inv_lt_comm₀ hr₀ (by norm_num)]
      linarith
    linarith

/-- Landen's identity for `g(r) = μ(r) + log r`: for `u ∈ (0, 1)`,
`g(√(1 - u²)) = g((1 - u)/(1 + u))/2 + log(1 + u)`. -/
theorem w15_a_landen_g {u : ℝ} (hu₀ : 0 < u) (hu₁ : u < 1) :
    grotzschMu (Real.sqrt (1 - u ^ 2)) + Real.log (Real.sqrt (1 - u ^ 2)) =
      (grotzschMu ((1 - u) / (1 + u)) + Real.log ((1 - u) / (1 + u))) / 2 +
        Real.log (1 + u) := by
  have hL := em_mu_landen hu₀ hu₁
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1u' : (0 : ℝ) < 1 - u := by linarith
  have hsq : Real.log (Real.sqrt (1 - u ^ 2)) = (Real.log (1 - u) + Real.log (1 + u)) / 2 := by
    rw [Real.log_sqrt (by nlinarith), show 1 - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.log_mul h1u'.ne' h1u.ne']
  rw [hsq, Real.log_div h1u'.ne' h1u.ne', hL]
  ring

/-- One Landen step for differences of `g(r) = μ(r) + log r`: for `0 < a ≤ b < 1` there are
`0 < ρ ≤ σ < 1` with `g(b) - g(a) ≤ (g(σ) - g(ρ))/2`. -/
theorem w15_a_landen_pair {a b : ℝ} (ha₀ : 0 < a) (hab : a ≤ b) (hb₁ : b < 1) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ ρ ≤ σ ∧ σ < 1 ∧
      (grotzschMu b + Real.log b) - (grotzschMu a + Real.log a) ≤
        ((grotzschMu σ + Real.log σ) - (grotzschMu ρ + Real.log ρ)) / 2 := by
  have ha₁ : a < 1 := hab.trans_lt hb₁
  have hb₀ : 0 < b := ha₀.trans_le hab
  set u := Real.sqrt (1 - a ^ 2) with hu_def
  set v := Real.sqrt (1 - b ^ 2) with hv_def
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith
  have hu₀ : 0 < u := Real.sqrt_pos.2 ha2
  have hv₀ : 0 < v := Real.sqrt_pos.2 hb2
  have hu₁ : u < 1 := by rw [hu_def, Real.sqrt_lt' one_pos]; nlinarith
  have hv₁ : v < 1 := by rw [hv_def, Real.sqrt_lt' one_pos]; nlinarith
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by nlinarith)
  have hau : Real.sqrt (1 - u ^ 2) = a := by
    rw [hu_def, Real.sq_sqrt ha2.le, sub_sub_cancel, Real.sqrt_sq ha₀.le]
  have hbv : Real.sqrt (1 - v ^ 2) = b := by
    rw [hv_def, Real.sq_sqrt hb2.le, sub_sub_cancel, Real.sqrt_sq hb₀.le]
  have hLa := w15_a_landen_g hu₀ hu₁
  have hLb := w15_a_landen_g hv₀ hv₁
  rw [hau] at hLa
  rw [hbv] at hLb
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1v : (0 : ℝ) < 1 + v := by linarith
  refine ⟨(1 - u) / (1 + u), (1 - v) / (1 + v), div_pos (by linarith) h1u, ?_,
    (div_lt_one h1v).2 (by linarith), ?_⟩
  · rw [div_le_div_iff₀ h1u h1v]
    nlinarith
  · have hlog : Real.log (1 + v) ≤ Real.log (1 + u) := Real.log_le_log h1v (by linarith)
    rw [hLa, hLb]
    linarith

/-- `g(r) = μ(r) + log r` is non-increasing on `(0, 1)` (Landen bootstrap: the oscillation
`sup_{a ≤ b} (g(b) - g(a))` is finite and at most half of itself). -/
theorem w15_a_g_antitoneOn : AntitoneOn (fun r : ℝ => grotzschMu r + Real.log r) (Ioo 0 1) := by
  set C : ℝ := Real.log 4 + 1 with hC
  have key : ∀ n : ℕ, ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      (grotzschMu b + Real.log b) - (grotzschMu a + Real.log a) ≤ C * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro a b ha₀ hab hb₁
      have h1 := w15_a_g_le_log4 (ha₀.trans_le hab) hb₁
      have h2 := w15_a_g_ge_neg_one ha₀ (hab.trans_lt hb₁)
      rw [pow_zero, mul_one]
      linarith
    | succ n ih =>
      intro a b ha₀ hab hb₁
      obtain ⟨ρ, σ, hρ₀, hρσ, hσ₁, hle⟩ := w15_a_landen_pair ha₀ hab hb₁
      have := ih ρ σ hρ₀ hρσ hσ₁
      rw [pow_succ]
      linarith
  intro a ha b hb hab
  have ht : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul C
  have := ge_of_tendsto' ht (fun n => key n a b ha.1 hab hb.2)
  simp only
  linarith

/-- `μ(r) + log r → log 4` as `r → 0⁺`. -/
theorem w15_a_tendsto_g :
    Tendsto (fun r : ℝ => grotzschMu r + Real.log r) (𝓝[>] 0) (𝓝 (Real.log 4)) := by
  have hlow : Tendsto (fun r : ℝ => Real.log 4 + Real.log (1 - r ^ 2) / 2) (𝓝[>] 0)
      (𝓝 (Real.log 4)) := by
    have hc : ContinuousAt (fun r : ℝ => Real.log 4 + Real.log (1 - r ^ 2) / 2) 0 := by
      apply ContinuousAt.add continuousAt_const
      apply ContinuousAt.div_const
      apply ContinuousAt.log (by fun_prop)
      norm_num
    have h := hc.tendsto
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Real.log_one,
      zero_div, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with r hr
    exact w15_a_g_ge hr.1 hr.2
  · filter_upwards [hev] with r hr
    exact w15_a_g_le_log4 hr.1 hr.2

/-- The key inequality of Wang Chuanfang's estimate: for `K ≥ 1`, `0 < r < 1` and
`s = 4^{1-1/K} r^{1/K} < 1`, `K μ(s) ≤ μ(r)`. -/
theorem w15_a_mu_le {K r : ℝ} (hK : 1 ≤ K) (hr₀ : 0 < r) (hr₁ : r < 1)
    (hs : (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) < 1) :
    K * grotzschMu ((4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K)) ≤ grotzschMu r := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set s := (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) with hs_def
  have h1K : 1 / K ≤ 1 := by rw [div_le_one hK0]; exact hK
  have h4 : 1 ≤ (4 : ℝ) ^ (1 - 1 / K) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hrr : r ≤ r ^ (1 / K) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ (1 / K) := Real.rpow_le_rpow_of_exponent_ge hr₀ hr₁.le h1K
  have hrpos : 0 < r ^ (1 / K) := Real.rpow_pos_of_pos hr₀ _
  have h4pos : 0 < (4 : ℝ) ^ (1 - 1 / K) := Real.rpow_pos_of_pos (by norm_num) _
  have hs₀ : 0 < s := mul_pos h4pos hrpos
  have hrs : r ≤ s := by
    calc r ≤ r ^ (1 / K) := hrr
      _ = 1 * r ^ (1 / K) := (one_mul _).symm
      _ ≤ s := mul_le_mul_of_nonneg_right h4 hrpos.le
  have hmono : grotzschMu s + Real.log s ≤ grotzschMu r + Real.log r :=
    w15_a_g_antitoneOn ⟨hr₀, hr₁⟩ ⟨hs₀, hs⟩ hrs
  have hup : grotzschMu s + Real.log s ≤ Real.log 4 := w15_a_g_le_log4 hs₀ hs
  have hlogs : K * Real.log s = (K - 1) * Real.log 4 + Real.log r := by
    rw [hs_def, Real.log_mul h4pos.ne' hrpos.ne', Real.log_rpow (by norm_num),
      Real.log_rpow hr₀]
    field_simp
  have hK1 : 0 ≤ K - 1 := by linarith
  have h1 : (K - 1) * (grotzschMu s + Real.log s) ≤ (K - 1) * Real.log 4 :=
    mul_le_mul_of_nonneg_left hup hK1
  nlinarith

/-- Historical note (Wang Chuanfang 王传芳): for a `K`-q.c. self-map of `Δ` with `f(0) = 0`,
`|f(z)| ≤ 4^{1-1/K} |z|^{1/K}`. -/
theorem wang_chuanfang {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f unitDisc K)
    (himg : f '' unitDisc = unitDisc) (hf0 : f 0 = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖f z‖ ≤ (4 : ℝ) ^ (1 - 1 / K) * ‖z‖ ^ (1 / K) := by
  have hK1 : 1 ≤ K := hf.2.1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hf0, norm_zero]
    positivity
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hr1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hfz : f z ∈ unitDisc := himg ▸ mem_image_of_mem f hz
  have ht1 : ‖f z‖ < 1 := mem_ball_zero_iff.1 hfz
  have hμ : grotzschMu ‖z‖ ≤ K * grotzschMu ‖f z‖ := eq15_1 ⟨hf, himg.subset⟩ hf0 hz hz0
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hs1 : (4 : ℝ) ^ (1 - 1 / K) * ‖z‖ ^ (1 / K) < 1 := hlt.trans ht1
  have hs0 : 0 < (4 : ℝ) ^ (1 - 1 / K) * ‖z‖ ^ (1 / K) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hr0 _)
  have hkey := w15_a_mu_le hK1 hr0 hr1 hs1
  have hstrict : grotzschMu ‖f z‖ < grotzschMu ((4 : ℝ) ^ (1 - 1 / K) * ‖z‖ ^ (1 / K)) :=
    grotzschMu_strictAntiOn ⟨hs0, hs1⟩ ⟨hs0.trans hlt, ht1⟩ hlt
  have := mul_lt_mul_of_pos_left hstrict hK0
  linarith

/-! ### s15w track (coordinator 553e2d), part W2: sharpness of Wang Chuanfang's constant -/

/-! ### Scout W2: the cos-conjugated stretch -/

/-- `E_a(ξ) = (a/2)(1 + cos ξ)`: the cosine, rescaled so that the real axis goes onto `[0, a]`. -/
def w15_b_E (a : ℝ) (ξ : ℂ) : ℂ := ((a / 2 : ℝ) : ℂ) * (1 + Complex.cos ξ)

/-- The vertical stretch `T_l(ξ) = Re ξ + i l Im ξ`. -/
def w15_b_T (l : ℝ) (ξ : ℂ) : ℂ := (ξ.re : ℂ) + ((l * ξ.im : ℝ) : ℂ) * I

/-- A chosen cosine-preimage: `cos (pre a w) = 2w/a - 1`. -/
def w15_b_pre (a : ℝ) (w : ℂ) : ℂ := Classical.choose (Complex.cos_surjective (2 * w / a - 1))

/-- The map `F(E_a ξ) = E_b(T_l ξ)` (well defined, see `w15_b_F_E`). -/
def w15_b_F (a b l : ℝ) (w : ℂ) : ℂ := w15_b_E b (w15_b_T l (w15_b_pre a w))

/-- `cos (pre a w) = 2w/a - 1`. -/
theorem w15_b_cos_pre (a : ℝ) (w : ℂ) : Complex.cos (w15_b_pre a w) = 2 * w / a - 1 :=
  Classical.choose_spec (Complex.cos_surjective (2 * w / a - 1))

/-- `E_a (pre a w) = w` for `a ≠ 0`. -/
theorem w15_b_E_pre {a : ℝ} (ha : a ≠ 0) (w : ℂ) : w15_b_E a (w15_b_pre a w) = w := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [w15_b_E, w15_b_cos_pre]
  push_cast
  field_simp
  ring

/-- `E_a ξ₁ = E_a ξ₂ ↔ cos ξ₁ = cos ξ₂` for `a ≠ 0`. -/
theorem w15_b_E_eq_iff {a : ℝ} (ha : a ≠ 0) {ξ₁ ξ₂ : ℂ} :
    w15_b_E a ξ₁ = w15_b_E a ξ₂ ↔ Complex.cos ξ₁ = Complex.cos ξ₂ := by
  have ha' : ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    have : a / 2 ≠ 0 := div_ne_zero ha two_ne_zero
    exact_mod_cast this
  unfold w15_b_E
  constructor
  · intro h
    have := mul_left_cancel₀ ha' h
    linear_combination this
  · intro h
    rw [h]

/-- `T_l` is additive. -/
theorem w15_b_T_add (l : ℝ) (ξ₁ ξ₂ : ℂ) : w15_b_T l (ξ₁ + ξ₂) = w15_b_T l ξ₁ + w15_b_T l ξ₂ := by
  apply Complex.ext
  · simp [w15_b_T]
  · simp [w15_b_T]
    ring

/-- `T_l` is odd. -/
theorem w15_b_T_neg (l : ℝ) (ξ : ℂ) : w15_b_T l (-ξ) = -w15_b_T l ξ := by
  apply Complex.ext <;> simp [w15_b_T]

/-- `T_l` fixes real points. -/
theorem w15_b_T_ofReal (l x : ℝ) : w15_b_T l (x : ℂ) = x := by
  apply Complex.ext <;> simp [w15_b_T]

/-- `T_l ∘ T_m = T_{lm}`. -/
theorem w15_b_T_T (l m : ℝ) (ξ : ℂ) : w15_b_T l (w15_b_T m ξ) = w15_b_T (l * m) ξ := by
  apply Complex.ext
  · simp [w15_b_T]
  · simp [w15_b_T]
    ring

/-- `T_1 = id`. -/
theorem w15_b_T_one (ξ : ℂ) : w15_b_T 1 ξ = ξ := by
  apply Complex.ext <;> simp [w15_b_T]

/-- `T_l` is continuous. -/
theorem w15_b_T_continuous (l : ℝ) : Continuous (w15_b_T l) := by
  unfold w15_b_T
  fun_prop

/-- `cos ξ₁ = cos ξ₂ ⇒ cos (T_l ξ₁) = cos (T_l ξ₂)`. -/
theorem w15_b_cos_T {l : ℝ} {ξ₁ ξ₂ : ℂ} (h : Complex.cos ξ₁ = Complex.cos ξ₂) :
    Complex.cos (w15_b_T l ξ₁) = Complex.cos (w15_b_T l ξ₂) := by
  obtain ⟨k, hk⟩ := Complex.cos_eq_cos_iff.1 h
  have hk' : (2 * (k : ℂ) * π) = ((2 * k * π : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.cos_eq_cos_iff]
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · left
    rw [hk, hk', w15_b_T_add, w15_b_T_ofReal]
  · right
    rw [hk, hk', sub_eq_add_neg, w15_b_T_add, w15_b_T_ofReal, w15_b_T_neg, ← sub_eq_add_neg]

/-- Converse of `w15_b_cos_T` for `l ≠ 0`. -/
theorem w15_b_cos_T_inv {l : ℝ} (hl : l ≠ 0) {ξ₁ ξ₂ : ℂ}
    (h : Complex.cos (w15_b_T l ξ₁) = Complex.cos (w15_b_T l ξ₂)) :
    Complex.cos ξ₁ = Complex.cos ξ₂ := by
  have h' := w15_b_cos_T (l := l⁻¹) h
  rwa [w15_b_T_T, w15_b_T_T, inv_mul_cancel₀ hl, w15_b_T_one, w15_b_T_one] at h'

/-- The defining identity `F(E_a ξ) = E_b(T_l ξ)`. -/
theorem w15_b_F_E {a : ℝ} (ha : a ≠ 0) (b l : ℝ) (ξ : ℂ) :
    w15_b_F a b l (w15_b_E a ξ) = w15_b_E b (w15_b_T l ξ) := by
  unfold w15_b_F
  have h1 : w15_b_E a (w15_b_pre a (w15_b_E a ξ)) = w15_b_E a ξ := w15_b_E_pre ha _
  have h3 := w15_b_cos_T (l := l) ((w15_b_E_eq_iff ha).1 h1)
  simp only [w15_b_E] at h3 ⊢
  rw [h3]

/-- `E_a` is entire. -/
theorem w15_b_E_differentiable (a : ℝ) : Differentiable ℂ (w15_b_E a) := by
  unfold w15_b_E
  fun_prop

/-- `E_a` is surjective for `a ≠ 0`. -/
theorem w15_b_E_surjective {a : ℝ} (ha : a ≠ 0) : Function.Surjective (w15_b_E a) :=
  fun w => ⟨w15_b_pre a w, w15_b_E_pre ha w⟩

/-- `E_a 0 = a`. -/
theorem w15_b_E_zero (a : ℝ) : w15_b_E a 0 = a := by
  simp only [w15_b_E, Complex.cos_zero]
  push_cast
  ring

/-- `E_a π = 0`. -/
theorem w15_b_E_pi (a : ℝ) : w15_b_E a π = 0 := by
  simp [w15_b_E]

/-- `E_a` is an open map for `a ≠ 0` (open mapping theorem). -/
theorem w15_b_E_isOpenMap {a : ℝ} (ha : a ≠ 0) : IsOpenMap (w15_b_E a) := by
  have han : AnalyticOnNhd ℂ (w15_b_E a) univ := fun z _ =>
    (w15_b_E_differentiable a).analyticAt z
  rcases han.is_constant_or_isOpenMap with ⟨w, hw⟩ | h
  · exfalso
    have h0 := hw 0
    have hπ := hw π
    rw [w15_b_E_zero] at h0
    rw [w15_b_E_pi] at hπ
    rw [← hπ] at h0
    exact ha (by exact_mod_cast h0)
  · exact h

/-- `E_a` is a quotient map for `a ≠ 0`. -/
theorem w15_b_E_isQuotientMap {a : ℝ} (ha : a ≠ 0) : IsQuotientMap (w15_b_E a) :=
  (w15_b_E_isOpenMap ha).isQuotientMap (w15_b_E_differentiable a).continuous
    (w15_b_E_surjective ha)

/-- `F` is continuous (it lifts through the quotient map `E_a` to `E_b ∘ T_l`). -/
theorem w15_b_F_continuous {a : ℝ} (ha : a ≠ 0) (b l : ℝ) : Continuous (w15_b_F a b l) := by
  rw [(w15_b_E_isQuotientMap ha).continuous_iff]
  have h : w15_b_F a b l ∘ w15_b_E a = w15_b_E b ∘ w15_b_T l :=
    funext fun ξ => w15_b_F_E ha b l ξ
  rw [h]
  exact (w15_b_E_differentiable b).continuous.comp (w15_b_T_continuous l)

/-- `F_{b,a,l⁻¹}` inverts `F_{a,b,l}`. -/
theorem w15_b_F_F {a b l : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hl : l ≠ 0) (w : ℂ) :
    w15_b_F b a l⁻¹ (w15_b_F a b l w) = w := by
  obtain ⟨ξ, rfl⟩ := w15_b_E_surjective ha w
  rw [w15_b_F_E ha, w15_b_F_E hb, w15_b_T_T, inv_mul_cancel₀ hl, w15_b_T_one]

/-- `F` is a homeomorphism of the plane. -/
theorem w15_b_exists_homeomorph {a b l : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hl : l ≠ 0) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = w15_b_F a b l := by
  refine ⟨{ toFun := w15_b_F a b l
            invFun := w15_b_F b a l⁻¹
            left_inv := w15_b_F_F ha hb hl
            right_inv := fun w => ?_
            continuous_toFun := w15_b_F_continuous ha b l
            continuous_invFun := w15_b_F_continuous hb a l⁻¹ }, rfl⟩
  have h := w15_b_F_F hb ha (inv_ne_zero hl) w
  rwa [inv_inv] at h

/-- `T_{1/K}` is `K`-q.c. on the plane. -/
theorem w15_b_T_isKQC {K : ℝ} (hK : 1 ≤ K) : IsKQC (w15_b_T (1 / K)) univ K := by
  have hK0 : 0 < K := by linarith
  have hβ : (1 / K : ℝ) ≠ 0 := one_div_ne_zero hK0.ne'
  have h := td_Stretch_isKQC one_ne_zero hβ (by positivity)
    (by rw [div_le_one hK0]; exact hK)
  rw [one_div_one_div] at h
  refine ad_isKQC_congr h fun z _ => ?_
  rw [td_Stretch_apply]
  simp [w15_b_T]

/-- On an open set `V` where `E_a` is injective, `F = E_b ∘ T_{1/K} ∘ (E_a|_V)⁻¹` is `K`-q.c. on
`E_a(V)`. -/
theorem w15_b_F_isKQC_local {a b K : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hK : 1 ≤ K) {V : Set ℂ}
    (hV : IsOpen V) (hinj : InjOn (w15_b_E a) V) :
    IsKQC (w15_b_F a b (1 / K)) (w15_b_E a '' V) K := by
  have hK0 : 0 < K := by linarith
  have hl : (1 / K : ℝ) ≠ 0 := one_div_ne_zero hK0.ne'
  have hconf : IsConformalOnto (w15_b_E a) V (w15_b_E a '' V) :=
    ⟨(w15_b_E_differentiable a).differentiableOn, hinj, rfl⟩
  have hU : IsOpen (w15_b_E a '' V) := hconf.isOpen hV
  have hψc : IsConformalOnto (Function.invFunOn (w15_b_E a) V) (w15_b_E a '' V) V :=
    hconf.symm hV
  have h1 : IsKQC (Function.invFunOn (w15_b_E a) V) (w15_b_E a '' V) 1 :=
    isKQC_one_of_conformal hU hψc
  have h12 : IsKQC (w15_b_T (1 / K) ∘ Function.invFunOn (w15_b_E a) V) (w15_b_E a '' V)
      (1 * K) :=
    thm7_1_comp h1 (w15_b_T_isKQC hK) (subset_univ _)
  have hV'eq : w15_b_T (1 / K) '' V = w15_b_T K ⁻¹' V :=
    congrFun (Set.image_eq_preimage_of_inverse (f := w15_b_T (1 / K)) (g := w15_b_T K)
      (fun ξ => by rw [w15_b_T_T, mul_one_div_cancel hK0.ne', w15_b_T_one])
      (fun ξ => by rw [w15_b_T_T, one_div_mul_cancel hK0.ne', w15_b_T_one])) V
  have hV'o : IsOpen (w15_b_T (1 / K) '' V) := by
    rw [hV'eq]
    exact hV.preimage (w15_b_T_continuous K)
  have hinj' : InjOn (w15_b_E b) (w15_b_T (1 / K) '' V) := by
    rintro _ ⟨ξ₁, h₁, rfl⟩ _ ⟨ξ₂, h₂, rfl⟩ h
    have hc := w15_b_cos_T_inv hl ((w15_b_E_eq_iff hb).1 h)
    rw [hinj h₁ h₂ ((w15_b_E_eq_iff ha).2 hc)]
  have h3 : IsKQC (w15_b_E b) (w15_b_T (1 / K) '' V) 1 :=
    isKQC_one_of_conformal hV'o ⟨(w15_b_E_differentiable b).differentiableOn, hinj', rfl⟩
  have hsub : (w15_b_T (1 / K) ∘ Function.invFunOn (w15_b_E a) V) '' (w15_b_E a '' V) ⊆
      w15_b_T (1 / K) '' V := by
    rw [image_comp, hψc.2.2]
  have h123 := thm7_1_comp h12 h3 hsub
  rw [one_mul, mul_one] at h123
  refine ad_isKQC_congr h123 ?_
  rintro _ ⟨ξ, hξ, rfl⟩
  show w15_b_F a b (1 / K) (w15_b_E a ξ) =
    w15_b_E b (w15_b_T (1 / K) (Function.invFunOn (w15_b_E a) V (w15_b_E a ξ)))
  rw [w15_b_F_E ha, hinj.leftInvOn_invFunOn hξ]

/-- Away from the critical values `0, a`, `E_a` is injective on an open set whose image contains
the given point (inverse function theorem, `sin ξ₀ ≠ 0`). -/
theorem w15_b_exists_injOn_nhds {a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz0 : z ≠ 0) (hza : z ≠ a) :
    ∃ V : Set ℂ, IsOpen V ∧ InjOn (w15_b_E a) V ∧ z ∈ w15_b_E a '' V := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hcos := w15_b_cos_pre a z
  have hsin : Complex.sin (w15_b_pre a z) ≠ 0 := by
    intro hs
    have h1 := Complex.sin_sq_add_cos_sq (w15_b_pre a z)
    rw [hs, hcos] at h1
    have h2 : (z - a) * z = 0 := by
      field_simp at h1
      linear_combination h1 / 4
    rcases mul_eq_zero.1 h2 with h | h
    · exact hza (sub_eq_zero.1 h)
    · exact hz0 h
  have hderiv : HasStrictDerivAt (w15_b_E a)
      (((a / 2 : ℝ) : ℂ) * -Complex.sin (w15_b_pre a z)) (w15_b_pre a z) :=
    ((Complex.hasStrictDerivAt_cos _).const_add 1).const_mul ((a / 2 : ℝ) : ℂ)
  have hne : ((a / 2 : ℝ) : ℂ) * -Complex.sin (w15_b_pre a z) ≠ 0 := by
    refine mul_ne_zero ?_ (neg_ne_zero.2 hsin)
    have : a / 2 ≠ 0 := div_ne_zero ha two_ne_zero
    exact_mod_cast this
  have hF := hderiv.hasStrictFDerivAt_equiv hne
  refine ⟨(hF.toOpenPartialHomeomorph (w15_b_E a)).source,
    (hF.toOpenPartialHomeomorph (w15_b_E a)).open_source, ?_,
    ⟨w15_b_pre a z, hF.mem_toOpenPartialHomeomorph_source, w15_b_E_pre ha z⟩⟩
  have h := (hF.toOpenPartialHomeomorph (w15_b_E a)).injOn
  rwa [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at h

/-- `F_{a,b,1/K}` is a `K`-q.c. map of the plane: the two critical values `0, a` are removable. -/
theorem w15_b_F_isKQC {a b K : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hK : 1 ≤ K) :
    IsKQC (w15_b_F a b (1 / K)) univ K := by
  have hK0 : 0 < K := by linarith
  obtain ⟨e, he⟩ := w15_b_exists_homeomorph ha hb (l := 1 / K) (one_div_ne_zero hK0.ne')
  have hg : IsHomeomorphOnto (w15_b_F a b (1 / K)) univ (w15_b_F a b (1 / K) '' univ) := by
    have h := nxI1_isHomeomorphOnto_of_homeomorph e
    rw [he] at h
    have hs : Function.Surjective (w15_b_F a b (1 / K)) := he ▸ e.surjective
    rwa [image_univ, hs.range_eq]
  refine s13x_removable (L := {0, (a : ℂ)}) isOpen_univ hK hg ?_ ?_ ?_ ?_
  · exact (Set.toFinite _).measure_zero _
  · refine Filter.Eventually.of_forall fun x => (Set.countable_singleton (0 : ℝ)).mono ?_
    intro y hy
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hy ⊢
    rcases hy with h | h
    · simpa using congrArg Complex.im h
    · simpa using congrArg Complex.im h
  · refine Filter.Eventually.of_forall fun y =>
      ((Set.countable_singleton (a : ℝ)).insert 0).mono ?_
    intro x hx
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hx ⊢
    rcases hx with h | h
    · left
      simpa using congrArg Complex.re h
    · right
      simpa using congrArg Complex.re h
  · intro z hz
    have hz0 : z ≠ 0 := fun h => hz.2 (by simp [h])
    have hza : z ≠ a := fun h => hz.2 (by simp [h])
    obtain ⟨V, hVo, hVi, hzV⟩ := w15_b_exists_injOn_nhds ha hz0 hza
    exact ⟨_, w15_b_E_isOpenMap ha V hVo, hzV, subset_univ _,
      w15_b_F_isKQC_local ha hb hK hVo hVi⟩

/-- `|cos ξ|² = (cos x cosh y)² + (sin x sinh y)²` for `ξ = x + iy`. -/
theorem w15_b_norm_cos_sq (ξ : ℂ) :
    ‖Complex.cos ξ‖ ^ 2 =
      (Real.cos ξ.re * Real.cosh ξ.im) ^ 2 + (Real.sin ξ.re * Real.sinh ξ.im) ^ 2 := by
  have h : Complex.cos ξ = ((Real.cos ξ.re * Real.cosh ξ.im : ℝ) : ℂ) +
      ((-(Real.sin ξ.re * Real.sinh ξ.im) : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im ξ]
    rw [Complex.cos_add_mul_I]
    push_cast
    ring
  rw [h, Complex.sq_norm, Complex.normSq_add_mul_I]
  ring

/-- `|sinh (Im ξ)| ≤ |cos ξ|`. -/
theorem w15_b_abs_sinh_le_norm_cos (ξ : ℂ) : |Real.sinh ξ.im| ≤ ‖Complex.cos ξ‖ := by
  have h := w15_b_norm_cos_sq ξ
  have hc := Real.cosh_sq ξ.im
  have hcs := Real.cos_sq_add_sin_sq ξ.re
  have hsq : |Real.sinh ξ.im| ^ 2 ≤ ‖Complex.cos ξ‖ ^ 2 := by
    rw [sq_abs, h]
    nlinarith [sq_nonneg (Real.cos ξ.re), sq_nonneg (Real.sinh ξ.im)]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- `|cos ξ| ≤ cosh (Im ξ)`. -/
theorem w15_b_norm_cos_le_cosh (ξ : ℂ) : ‖Complex.cos ξ‖ ≤ Real.cosh ξ.im := by
  have h := w15_b_norm_cos_sq ξ
  have hc := Real.cosh_sq ξ.im
  have hcs := Real.cos_sq_add_sin_sq ξ.re
  have hsq : ‖Complex.cos ξ‖ ^ 2 ≤ Real.cosh ξ.im ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg (Real.sin ξ.re), sq_nonneg (Real.sinh ξ.im)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos _).le two_ne_zero).1 hsq

/-- The key estimate: for `r = 4τ^K`, `s = 4τ` (`0 < τ ≤ 1`), `F` maps the unit disc into the
closed disc of radius `1 + 6τ`. -/
theorem w15_b_F_bound {K τ : ℝ} (hK : 1 ≤ K) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {w : ℂ}
    (hw : w ∈ unitDisc) : ‖w15_b_F (4 * τ ^ K) (4 * τ) (1 / K) w‖ ≤ 1 + 6 * τ := by
  have hK0 : 0 < K := by linarith
  have hτK : 0 < τ ^ K := Real.rpow_pos_of_pos hτ0 K
  have hr : 0 < 4 * τ ^ K := by positivity
  set ξ := w15_b_pre (4 * τ ^ K) w with hξ
  have hEw : w15_b_E (4 * τ ^ K) ξ = w := w15_b_E_pre hr.ne' w
  have hF : w15_b_F (4 * τ ^ K) (4 * τ) (1 / K) w = w15_b_E (4 * τ) (w15_b_T (1 / K) ξ) := by
    conv_lhs => rw [← hEw]
    exact w15_b_F_E hr.ne' _ _ _
  have hw1 : ‖w‖ < 1 := by simpa [unitDisc] using hw
  -- `|cos ξ| < 2/r + 1`
  have h1 : ‖1 + Complex.cos ξ‖ * (4 * τ ^ K) < 2 := by
    rw [← hEw, w15_b_E, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at hw1
    linarith
  have hcos : ‖Complex.cos ξ‖ * (4 * τ ^ K) < 2 + 4 * τ ^ K := by
    have : ‖Complex.cos ξ‖ ≤ ‖1 + Complex.cos ξ‖ + 1 := by
      calc ‖Complex.cos ξ‖ = ‖(1 + Complex.cos ξ) - 1‖ := by ring_nf
        _ ≤ ‖1 + Complex.cos ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖1 + Complex.cos ξ‖ + 1 := by rw [norm_one]
    nlinarith
  -- `sinh |y| · r < 2 + r`
  have hsinh : Real.sinh |ξ.im| * (4 * τ ^ K) < 2 + 4 * τ ^ K := by
    rw [← Real.abs_sinh]
    exact (mul_le_mul_of_nonneg_right (w15_b_abs_sinh_le_norm_cos ξ) hr.le).trans_lt hcos
  -- `e^{|y|} ≤ 2 sinh |y| + 1`
  have hexp1 : Real.exp |ξ.im| ≤ 2 * Real.sinh |ξ.im| + 1 := by
    rw [Real.sinh_eq]
    have : Real.exp (-|ξ.im|) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _))
    linarith
  -- `τ^K e^{|y|} < 1 + 3τ^K`
  have hexp : τ ^ K * Real.exp |ξ.im| < 1 + 3 * τ ^ K := by
    nlinarith
  -- `τ e^{|y|/K} ≤ 1 + 3τ^K` (take logarithms)
  have hkey : τ * Real.exp (|ξ.im| / K) ≤ 1 + 3 * τ ^ K := by
    have hA : 0 < 1 + 3 * τ ^ K := by positivity
    have hlog : K * Real.log τ + |ξ.im| < Real.log (1 + 3 * τ ^ K) := by
      have := Real.log_lt_log (by positivity) hexp
      rwa [Real.log_mul hτK.ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_rpow hτ0] at this
    have hL0 : 0 ≤ Real.log (1 + 3 * τ ^ K) := Real.log_nonneg (by linarith)
    have h2 : τ * Real.exp (|ξ.im| / K) = Real.exp (Real.log τ + |ξ.im| / K) := by
      rw [Real.exp_add, Real.exp_log hτ0]
    have heq : Real.log τ + |ξ.im| / K = (K * Real.log τ + |ξ.im|) / K := by
      field_simp
    rw [h2, heq]
    calc Real.exp ((K * Real.log τ + |ξ.im|) / K)
        ≤ Real.exp (Real.log (1 + 3 * τ ^ K)) := by
          apply Real.exp_le_exp.2
          calc (K * Real.log τ + |ξ.im|) / K ≤ Real.log (1 + 3 * τ ^ K) / K :=
                div_le_div_of_nonneg_right hlog.le hK0.le
            _ ≤ Real.log (1 + 3 * τ ^ K) := div_le_self hL0 hK
      _ = 1 + 3 * τ ^ K := Real.exp_log hA
  -- the image point
  have hT : (w15_b_T (1 / K) ξ).im = 1 / K * ξ.im := by simp [w15_b_T]
  have hc : ‖Complex.cos (w15_b_T (1 / K) ξ)‖ ≤ Real.cosh (|ξ.im| / K) := by
    refine (w15_b_norm_cos_le_cosh _).trans_eq ?_
    rw [hT, ← Real.cosh_abs, abs_mul, abs_of_pos (one_div_pos.2 hK0)]
    ring_nf
  have hcosh : Real.cosh (|ξ.im| / K) ≤ (Real.exp (|ξ.im| / K) + 1) / 2 := by
    rw [Real.cosh_eq]
    have : Real.exp (-(|ξ.im| / K)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (abs_nonneg _) hK0.le))
    linarith
  have hτKτ : τ ^ K ≤ τ := by
    have := Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1 hK
    rwa [Real.rpow_one] at this
  rw [hF, w15_b_E, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hn : ‖1 + Complex.cos (w15_b_T (1 / K) ξ)‖ ≤ 1 + Real.cosh (|ξ.im| / K) :=
    (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  calc 4 * τ / 2 * ‖1 + Complex.cos (w15_b_T (1 / K) ξ)‖
      ≤ 4 * τ / 2 * (1 + (Real.exp (|ξ.im| / K) + 1) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 3 * τ + τ * Real.exp (|ξ.im| / K) := by ring
    _ ≤ 1 + 6 * τ := by linarith

/-- Historical note (Wang Chuanfang): the constant `4^{1-1/K}` is best possible. -/
theorem wang_chuanfang_sharp {K : ℝ} (hK : 1 < K) {c : ℝ} (hc : c < (4 : ℝ) ^ (1 - 1 / K)) :
    ∃ (f : ℂ → ℂ) (z : ℂ), IsKQC f unitDisc K ∧ f '' unitDisc = unitDisc ∧ f 0 = 0 ∧
      z ∈ unitDisc ∧ c * ‖z‖ ^ (1 / K) < ‖f z‖ := by
  have hK1 : 1 ≤ K := hK.le
  have hK0 : 0 < K := by linarith
  have h4K : 0 < (4 : ℝ) ^ (1 / K) := by positivity
  set M := c * (4 : ℝ) ^ (1 / K) with hMdef
  have hM : M < 4 := by
    have h4 : (4 : ℝ) ^ (1 - 1 / K) = 4 / (4 : ℝ) ^ (1 / K) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    rw [h4, lt_div_iff₀ h4K] at hc
    exact hc
  set τ : ℝ := min (1 / 8) ((4 - M) / 64) with hτdef
  have hτ0 : 0 < τ := lt_min (by norm_num) (by linarith)
  have hτ8 : τ ≤ 1 / 8 := min_le_left _ _
  have hτM : τ ≤ (4 - M) / 64 := min_le_right _ _
  have hτK : 0 < τ ^ K := Real.rpow_pos_of_pos hτ0 K
  have hτKτ : τ ^ K ≤ τ := by
    have := Real.rpow_le_rpow_of_exponent_ge hτ0 (by linarith) hK1
    rwa [Real.rpow_one] at this
  set r : ℝ := 4 * τ ^ K with hrdef
  set s : ℝ := 4 * τ with hsdef
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by linarith
  have hs0 : 0 < s := by positivity
  set F := w15_b_F r s (1 / K) with hFdef
  have hFK : IsKQC F univ K := w15_b_F_isKQC hr0.ne' hs0.ne' hK1
  obtain ⟨e, he⟩ := w15_b_exists_homeomorph hr0.ne' hs0.ne' (l := 1 / K)
    (one_div_ne_zero hK0.ne')
  have heF : ⇑e = F := he
  have hF0 : F 0 = 0 := by
    have h := w15_b_F_E hr0.ne' s (1 / K) π
    rw [w15_b_E_pi, w15_b_T_ofReal, w15_b_E_pi] at h
    exact h
  have hFr : F r = s := by
    have h := w15_b_F_E hr0.ne' s (1 / K) ((0 : ℝ) : ℂ)
    rw [w15_b_T_ofReal, Complex.ofReal_zero, w15_b_E_zero, w15_b_E_zero] at h
    exact h
  have hrD : (r : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact hr1
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have := t1_simplyConnected_image e
  have hWo := t1_isOpen_image e
  have h0W : (0 : ℂ) ∈ e '' unitDisc := ⟨0, h0D, by rw [heF]; exact hF0⟩
  have hsW : (s : ℂ) ∈ e '' unitDisc := ⟨r, hrD, by rw [heF]; exact hFr⟩
  obtain ⟨φ, hφ, hφ0, -⟩ :=
    t1_riemannMap hWo (t1_isConnected_image e) (t1_compl_nonempty e) h0W
  refine ⟨φ ∘ F, (r : ℂ), ?_, ?_, ?_, hrD, ?_⟩
  · have h1 : IsKQC F unitDisc K := nx_isKQC_restrict hFK isOpen_ball (subset_univ _)
    have h2 : IsKQC φ (e '' unitDisc) 1 := isKQC_one_of_conformal hWo hφ
    have h3 := thm7_1_comp h1 h2 (by rw [heF])
    rwa [mul_one] at h3
  · rw [image_comp, ← heF, hφ.2.2]
  · show φ (F 0) = 0
    rw [hF0, hφ0]
  · -- Schwarz for `ψ = φ⁻¹ : Δ → e(Δ) ⊆ closedBall 0 (1 + 6τ)`
    have hψ : IsConformalOnto (Function.invFunOn φ (e '' unitDisc)) unitDisc (e '' unitDisc) :=
      hφ.symm hWo
    have hψ0 : Function.invFunOn φ (e '' unitDisc) 0 = 0 := by
      have := hφ.2.1.leftInvOn_invFunOn h0W
      rwa [hφ0] at this
    have hmaps : MapsTo (Function.invFunOn φ (e '' unitDisc)) (ball 0 1)
        (closedBall (Function.invFunOn φ (e '' unitDisc) 0) (1 + 6 * τ)) := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hψ.mapsTo hu
      rw [hψ0, mem_closedBall, dist_zero_right, ← hwu, heF]
      exact w15_b_F_bound hK1 hτ0 (by linarith) hw
    have hu : φ s ∈ ball (0 : ℂ) 1 := hφ.mapsTo hsW
    have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hψ.1 hmaps hu
    have hψs : Function.invFunOn φ (e '' unitDisc) (φ s) = s :=
      hφ.2.1.leftInvOn_invFunOn hsW
    rw [hψs, hψ0, dist_zero_right, dist_zero_right, div_one, Complex.norm_real,
      Real.norm_of_nonneg hs0.le] at hsch
    show c * ‖(r : ℂ)‖ ^ (1 / K) < ‖φ (F r)‖
    rw [hFr]
    have hrK : ‖(r : ℂ)‖ ^ (1 / K) = (4 : ℝ) ^ (1 / K) * τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr0.le, hrdef,
        Real.mul_rpow (by norm_num) hτK.le, ← Real.rpow_mul hτ0.le,
        mul_one_div_cancel hK0.ne', Real.rpow_one]
    rw [hrK]
    have hlt : M * (1 + 6 * τ) < 4 := by
      rcases le_or_gt M 0 with hM0 | hM0
      · nlinarith
      · have : M * τ ≤ 4 * τ := mul_le_mul_of_nonneg_right hM.le hτ0.le
        nlinarith
    have hφs0 : 0 ≤ ‖φ s‖ := norm_nonneg _
    have hkey : c * ((4 : ℝ) ^ (1 / K) * τ) * (1 + 6 * τ) < (1 + 6 * τ) * ‖φ s‖ := by
      have : c * ((4 : ℝ) ^ (1 / K) * τ) = M * τ := by rw [hMdef]; ring
      rw [this]
      nlinarith
    have hpos : 0 < 1 + 6 * τ := by positivity
    nlinarith

end LiZhongQC
