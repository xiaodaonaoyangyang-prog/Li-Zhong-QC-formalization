import References.GardinerLakic2000.Ch14.S02_HarmonicBeltrami

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.3 The Earle–Nag reflection

Source `teichmuller.txt`, lines 10158–10315.

* Definition (the configuration `Ω, C, Ω*`: a quasicircle and its complementary domains, l. 10159) —
  `IsQCConfiguration`
* Definition (reflection for `C`, l. 10159) — `IsReflectionGL`
* Formula (14.8) (conformally natural reflection, l. 10170) — `IsConformallyNaturalReflection`
* Formula (14.9) (the Earle–Nag reflection, l. 10186) — `IsEarleNagReflection`
* Lemma 3 ([Ahl64], l. 10228) — `lemma14_3_a`, `lemma14_3_b`, `lemma14_3_c`
* Formula (14.12) (`δ ≤ ρ⁻¹ ≤ 4δ`, l. 10265; cited in Lemma 4) — exists: `Pommerenke1992.cor1_4` (with
  `ρ⁻¹ = (1 − |ζ|²)|z′(ζ)|`)
* Lemma 4 ((14.13), [EN86], l. 10270) — `lemma14_4`
* Theorem 2 ((14.15), [EN86], l. 10293) — `thm14_2`

Not items (DESIGN §3): `j*` ((14.10), l. 10219) and the Remark (l. 10215–10225), not used later; (14.11) (l. 10251) and
(14.14) (l. 10283), steps of the proofs. Near miss: `LiZhongQC.lemma20_2` (part (b) for planar reflections).

**Modelling.** Configurations are normalized by `∞ ∈ C`, the book's normalization in Lemma 3 and in §§14.5–14.7
(`C = f(ℝ̂)`), so `Ω` and `Ω*` are plane domains and a reflection is a map `j : ℂ → ℂ` (fixing `∞`). Lemma 4 and
Theorem 2 are Möbius invariant (l. 10287) and are stated in this normalization [reading]; so is the Earle–Nag
reflection, which removes the point at infinity from the Riemann maps. A reflection is a continuous involution fixing
`C`, mapping `Ω` onto `Ω*`, with `z ↦ conj (j z)` `K`-quasiconformal on both domains (orientation reversing); it
refines the one-sided `LiZhongQC.IsQCReflection`. `ρ` is Part A's `poincareDensityGL` (`ρ|dz| = |dζ|/(1 − |ζ|²)`).
In (14.9) the conformal map `g : Ω* → Δ*` is replaced by `ĝ = 1/g : Ω* → Δ`, so that with the continuous extensions
`f̂` of `f : Δ → Ω` and `ĝ` to the boundary, `g ∘ f = conj (ĝ ∘ f̂)` on `∂Δ` and (14.9) reads
`ĝ(j(f(ζ))) = conj (DE(conj (ĝ ∘ f̂))(ζ))` [reading]. Theorem 2 has "`j(z)` in `Ω`" for `Ω*` [misprint; GL1:2990 prints
the same, GL1:2968 has `Ω*` in Lemma 4]. "`M` depends only on `K`" is `∀ K ∃ M` over all configurations.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane extInf toExt IsQuasicircle IsKQC unitDisc mobiusSL dzbar)

/-- **Definition** (§14.3, l. 10159; normalized by `∞ ∈ C`). `C ⊆ ℂ̄` is a quasicircle through `∞` separating `ℂ̄` into
the (plane) domains `Ω` and `Ω*`. -/
def IsQCConfiguration (C : Set ExtPlane) (Ω Ωs : Set ℂ) : Prop :=
  IsQuasicircle C ∧ extInf ∈ C ∧ IsOpen Ω ∧ IsOpen Ωs ∧ IsConnected Ω ∧ IsConnected Ωs ∧ Disjoint Ω Ωs ∧
    toExt Ω ∪ toExt Ωs = Cᶜ

/-- **Definition** (reflection for `C`, §14.3, l. 10159). A `K`-quasiconformal, orientation-reversing homeomorphism
`j` fixing every point of `C`, mapping `Ω` onto `Ω*`, with `j² = id`. -/
def IsReflectionGL (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ) (K : ℝ) : Prop :=
  Continuous j ∧ (∀ z, j (j z) = z) ∧ (∀ z : ℂ, (z : ExtPlane) ∈ C → j z = z) ∧ j '' Ω = Ωs ∧
    IsKQC (fun z => conj (j z)) Ω K ∧ IsKQC (fun z => conj (j z)) Ωs K

/-- **Formula (14.8)** (§14.3, l. 10166–10170). `j` is conformally natural: `j ∘ γ = γ ∘ j` for every Möbius `γ`
leaving `Ω`, `C` and `Ω*` invariant (`j` extended by `j(∞) = ∞`). -/
def IsConformallyNaturalReflection (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ) : Prop :=
  ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℂ, mobiusSL γ '' toExt Ω = toExt Ω → mobiusSL γ '' C = C →
    mobiusSL γ '' toExt Ωs = toExt Ωs → ∀ p : ExtPlane,
      OnePoint.elim (mobiusSL γ p) extInf (fun w => ((j w : ℂ) : ExtPlane)) =
        mobiusSL γ (OnePoint.elim p extInf (fun w => ((j w : ℂ) : ExtPlane)))

/-- **Formula (14.9)** (the Earle–Nag reflection, §14.3, l. 10182–10190; see the module docstring). There are conformal
maps `f : Δ → Ω` and `ĝ : Ω* → Δ` with continuous extensions `f̂ : Δ̄ → Ω̄`, `ĝ : Ω̄* → Δ̄` such that
`ĝ(j(f(ζ))) = conj (DE(conj (ĝ ∘ f̂))(ζ))` on `Δ`, `j = id` on `C`, and `j = j⁻¹` on `Ω*`.
The boundary map `ζ ↦ conj (ĝ (f̂ ζ))` is required to be a sense-preserving homeomorphism of `𝕋` (`ĝ ∘ f̂` reverses
orientation since `Ω*` lies on the other side of `C`, so the conjugate preserves it): this is the hypothesis under which
`Pommerenke1992.douadyEarleExt` (a `Classical.epsilon` choice of the unique zero, Lemma 5.20) is the Douady–Earle
extension, so the right-hand side of (14.9) is never a junk value. -/
def IsEarleNagReflection (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ) : Prop :=
  ∃ (f : ℂ → ℂ) (fh : ℂ → ExtPlane) (g : ℂ → ℂ) (gh : ExtPlane → ℂ),
    DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f '' unitDisc = Ω ∧ ContinuousOn fh (closedBall 0 1) ∧
    (∀ ζ ∈ unitDisc, fh ζ = f ζ) ∧ DifferentiableOn ℂ g Ωs ∧ InjOn g Ωs ∧ g '' Ωs = unitDisc ∧
    ContinuousOn gh (toExt Ωs ∪ C) ∧ (∀ z ∈ Ωs, gh z = g z) ∧
    Pommerenke1992.IsSensePreservingCircleHomeo (fun ξ => conj (gh (fh ξ))) ∧
    (∀ ζ ∈ unitDisc, g (j (f ζ)) =
      conj (Pommerenke1992.douadyEarleExt (fun ξ => conj (gh (fh ξ))) ζ)) ∧
    (∀ z : ℂ, (z : ExtPlane) ∈ C → j z = z) ∧ ∀ z, j (j z) = z

/-- Helper for `lemma14_3_a`: removability of the quasicircle. For a `K`-quasiconformal reflection `j` of a
configuration (`∞ ∈ C`), `z ↦ conj (j z)` is a `K`-quasiconformal map of `ℂ` onto `ℂ`: `C ∩ ℂ = g(ℝ)` for a q.c. map
`g` of the plane, `(conj ∘ j) ∘ g` is q.c. on both half-planes (hence on `ℂ`), and `C ∩ ℂ` is null, so the analytic
definition gives the constant `K`. -/
theorem gl14_refl_qc {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ} (hc : IsQCConfiguration C Ω Ωs)
    (hj : IsReflectionGL C Ω Ωs j K) :
    IsKQC (fun z => conj (j z)) univ K ∧ (fun z => conj (j z)) '' univ = univ := by
  obtain ⟨hjc, hjj, -, -, hKΩ, hKΩs⟩ := hj
  have hK : 1 ≤ K := hKΩ.2.1
  set F : ℂ → ℂ := fun z => conj (j z) with hF
  have hFinv : ∀ w, F (j (conj w)) = w := fun w => by simp [hF, hjj]
  have hFinj : Function.Injective F := fun u v h => by
    have h' : j (conj (F u)) = j (conj (F v)) := by rw [h]
    simpa [hF, hjj] using h'
  have hFs : F '' univ = univ := eq_univ_of_forall fun w => ⟨_, mem_univ _, hFinv w⟩
  have hFc : Continuous F := continuous_conj.comp hjc
  have hFh : LiZhongQC.IsHomeomorphOnto F univ univ := by
    refine ⟨hFc.continuousOn, hFinj.injOn, hFs, ?_⟩
    have heq : Function.invFunOn F univ = fun w => j (conj w) := by
      funext w
      apply hFinj
      rw [Function.invFunOn_eq ⟨_, mem_univ _, hFinv w⟩, hFinv]
    rw [heq]
    exact (hjc.comp continuous_conj).continuousOn
  refine ⟨?_, hFs⟩
  -- `C ∩ ℂ = g(ℝ)` for a q.c. map `g` of the plane onto itself
  obtain ⟨⟨K', hK'⟩, hinf, hΩo, hΩso, -, -, hdisj, hunion⟩ := hc
  obtain ⟨g, hg, hgs, hC⟩ := LiZhongQC.tp_quasicircle_through_inf hK' hinf
  have hK'1 : 1 ≤ K' := hg.2.1
  have hgh : LiZhongQC.IsHomeomorphOnto g univ univ := by
    have h := hg.2.2.1
    rwa [hgs] at h
  obtain ⟨eg, heg⟩ := LiZhongQC.s13x_de_exists_homeomorph hgh
  have hgc : Continuous g := continuousOn_univ.1 hgh.1
  have hginj : Function.Injective g := fun u v h => hgh.2.1 (mem_univ u) (mem_univ v) h
  -- off `g(ℝ)` we are in `Ω ∪ Ω*`
  have hoff : ∀ w : ℂ, w ∉ g '' LiZhongQC.realLine → w ∈ Ω ∪ Ωs := by
    intro w hw
    have hwC : ((w : ℂ) : ExtPlane) ∉ C := by
      rw [hC]
      rintro (⟨w', hw', hww'⟩ | h)
      · exact hw (OnePoint.coe_injective hww' ▸ hw')
      · exact OnePoint.coe_ne_infty w h
    have h : ((w : ℂ) : ExtPlane) ∈ toExt Ω ∪ toExt Ωs := by rw [hunion]; exact hwC
    rcases h with ⟨u, hu, hwu⟩ | ⟨u, hu, hwu⟩
    · exact Or.inl (OnePoint.coe_injective hwu ▸ hu)
    · exact Or.inr (OnePoint.coe_injective hwu ▸ hu)
  -- `F ∘ g` is q.c. on each half-plane (which `g` maps into `Ω` or `Ω*`)
  have hhalf : ∀ P : Set ℂ, IsOpen P → IsPreconnected P → (∀ u ∈ P, u.im ≠ 0) →
      IsKQC (F ∘ g) P (K' * K) := by
    intro P hPo hPc hPim
    have hgP : g '' P ⊆ Ω ∪ Ωs := by
      rintro _ ⟨u, hu, rfl⟩
      refine hoff (g u) fun ⟨v, hv, hvu⟩ => hPim u hu ?_
      rw [← hginj hvu]
      exact hv
    have hgPo : IsOpen (g '' P) := heg ▸ eg.isOpenMap P hPo
    have hgq : IsKQC g P K' := LiZhongQC.nx_isKQC_restrict hg hPo (subset_univ _)
    rcases (hPc.image g hgc.continuousOn).subset_or_subset hΩo hΩso hdisj hgP with h | h
    · exact LiZhongQC.thm7_1_comp hgq (LiZhongQC.nx_isKQC_restrict hKΩ hgPo h) subset_rfl
    · exact LiZhongQC.thm7_1_comp hgq (LiZhongQC.nx_isKQC_restrict hKΩs hgPo h) subset_rfl
  have hU := hhalf LiZhongQC.upperHalf LiZhongQC.isOpen_upperHalf LiZhongQC.isConnected_upperHalf.isPreconnected
    fun u hu => (ne_of_gt hu)
  have hL := hhalf LiZhongQC.lowerHalf LiZhongQC.isOpen_lowerHalf
    LiZhongQC.bA_isConnected_lowerHalf.isPreconnected fun u hu => ne_of_lt hu
  -- glue across `ℝ`, then undo `g`
  obtain ⟨eF, heF⟩ := LiZhongQC.s13x_de_exists_homeomorph hFh
  have hFgh : LiZhongQC.IsHomeomorphOnto (F ∘ g) univ ((F ∘ g) '' univ) := by
    have h := LiZhongQC.nxI1_isHomeomorphOnto_of_homeomorph (eg.trans eF)
    have hcoe : ⇑(eg.trans eF) = F ∘ g := by
      funext x
      simp only [Homeomorph.trans_apply, Function.comp_apply, heg, heF]
    rw [hcoe] at h
    have himg : (F ∘ g) '' univ = univ := by rw [image_comp, hgs, hFs]
    rw [himg]
    exact h
  have hFg := LiZhongQC.wd_glue (one_le_mul_of_one_le_of_one_le hK'1 hK) hFgh hU hL
  set G := Function.invFunOn g univ with hG
  have hgG : ∀ w, g (G w) = w := fun w => Function.invFunOn_eq (show ∃ x ∈ univ, g x = w from
    by obtain ⟨x, -, hx⟩ := (show w ∈ g '' univ by rw [hgs]; exact mem_univ w); exact ⟨x, mem_univ _, hx⟩)
  have hGq : IsKQC G univ K' := by
    have h := LiZhongQC.thm7_2_inv hg
    rwa [hgs] at h
  have hFq : IsKQC F univ (K' * (K' * K)) := by
    have h := LiZhongQC.thm7_1_comp hGq hFg (subset_univ _)
    have heq : (F ∘ g) ∘ G = F := funext fun w => by simp [hgG]
    rwa [heq] at h
  -- the dilatation is `≤ K` a.e.: on `Ω`, on `Ω*`, and `g(ℝ)` is null
  have hnull : volume (g '' LiZhongQC.realLine) = 0 :=
    LiZhongQC.ac_n_volume_image_null_of_isKQC hg (subset_univ _) LiZhongQC.gzE_volume_im_eq_zero
  have hae : ∀ᵐ z ∂(volume.restrict univ),
      ‖LiZhongQC.dz F z‖ + ‖dzbar F z‖ ≤ K * (‖LiZhongQC.dz F z‖ - ‖dzbar F z‖) := by
    rw [Measure.restrict_univ]
    have h1 := (ae_restrict_iff' hΩo.measurableSet).1 (LiZhongQC.thm9_4_dilatation_ae hKΩ)
    have h2 := (ae_restrict_iff' hΩso.measurableSet).1 (LiZhongQC.thm9_4_dilatation_ae hKΩs)
    have h3 : ∀ᵐ z ∂volume, z ∉ g '' LiZhongQC.realLine := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    rcases hoff z hz3 with hzΩ | hzΩs
    · exact hz1 hzΩ
    · exact hz2 hzΩs
  exact (LiZhongQC.thm10_1_isKQC_iff isOpen_univ hK hFh).2 ⟨LiZhongQC.thm9_1_isACL hFq, hae⟩

/-- Helper for `gl14_three_point`: a homeomorphism `e` of `ℂ` carries a separation by `B` to a separation by `e(B)`
(through its one-point extension to `ℂ̄`). -/
theorem gl14_sep_image (e : ℂ ≃ₜ ℂ) {B : Set ℂ} {E₁ E₂ : Set ExtPlane} (h : LiZhongQC.SeparatesSets B E₁ E₂) :
    LiZhongQC.SeparatesSets (e '' B) (e.onePointCongr '' E₁) (e.onePointCongr '' E₂) := by
  obtain ⟨x₁, hx₁, x₂, hx₂, h1, h2, hne⟩ := h
  have hcompl : (toExt (e '' B))ᶜ = e.onePointCongr '' (toExt B)ᶜ := by
    rw [← LiZhongQC.s13x_de_image_toExt, LiZhongQC.gsep_z_image_compl_of_homeomorph]
  refine ⟨e.onePointCongr x₁, ?_, e.onePointCongr x₂, ?_, ?_, ?_, ?_⟩
  · rw [hcompl]
    exact mem_image_of_mem _ hx₁
  · rw [hcompl]
    exact mem_image_of_mem _ hx₂
  · rw [hcompl, ← e.onePointCongr.image_connectedComponentIn hx₁]
    exact image_mono h1
  · rw [hcompl, ← e.onePointCongr.image_connectedComponentIn hx₂]
    exact image_mono h2
  · rw [hcompl, ← e.onePointCongr.image_connectedComponentIn hx₁,
      ← e.onePointCongr.image_connectedComponentIn hx₂]
    exact fun heq => hne (e.onePointCongr.injective.image_injective heq)

/-- Helper for `gl14_three_point`: the annulus `r₁ < |w − p| < r₂` separates `{p, u}` from `{v, ∞}` when
`|u − p| ≤ r₁` and `|v − p| = r₂`. -/
theorem gl14_sep_annulusAt {p u v : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) (hu : ‖u - p‖ ≤ r₁)
    (hv : ‖v - p‖ = r₂) :
    LiZhongQC.SeparatesSets (LiZhongQC.annulusAt p r₁ r₂) {((p : ℂ) : ExtPlane), (u : ExtPlane)}
      {(v : ExtPlane), extInf} := by
  set A := LiZhongQC.annulusAt p r₁ r₂ with hA
  set S : Set ExtPlane := (toExt A)ᶜ with hS
  have hAo : IsOpen A := by
    have hAe : A = {z : ℂ | r₁ < ‖z - p‖} ∩ {z : ℂ | ‖z - p‖ < r₂} := by
      rw [hA]
      rfl
    rw [hAe]
    exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)
  have hSc : IsClosed S := isClosed_compl_iff.2 (OnePoint.isOpenEmbedding_coe.isOpenMap _ hAo)
  have hpS : ((p : ℂ) : ExtPlane) ∈ S := by
    rintro ⟨w, hw, hwp⟩
    have h := hw.1
    rw [OnePoint.coe_injective hwp, sub_self, norm_zero] at h
    linarith
  have hinfS : (extInf : ExtPlane) ∈ S := fun ⟨w, _, hw⟩ => OnePoint.coe_ne_infty w hw
  refine ⟨_, hpS, _, hinfS, ?_, ?_, ?_⟩
  · -- the closed disc of radius `r₁`
    have hP : toExt (closedBall p r₁) ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
      rw [OnePoint.coe_injective hww'] at hw'
      have := mem_closedBall_iff_norm.1 hw
      exact absurd hw'.1 (not_lt.2 this)
    have hPc : IsPreconnected (toExt (closedBall p r₁)) :=
      (convex_closedBall p r₁).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    refine insert_subset_iff.2 ⟨mem_connectedComponentIn hpS, singleton_subset_iff.2 ?_⟩
    exact hPc.subset_connectedComponentIn ⟨p, mem_closedBall_self h₁.le, rfl⟩ hP
      ⟨u, mem_closedBall_iff_norm.2 hu, rfl⟩
  · -- the closure of the ray `p + t (v − p)`, `t ≥ 1`
    set R : Set ℂ := (fun t : ℝ => p + (t : ℂ) * (v - p)) '' Ici 1 with hR
    have hvp : 0 < ‖v - p‖ := hv ▸ (h₁.trans h₂)
    have hRA : toExt R ⊆ S := by
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ ⟨w', hw', hww'⟩
      rw [OnePoint.coe_injective hww'] at hw'
      have h := hw'.2
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [mem_Ici.1 ht])] at h
      nlinarith [mem_Ici.1 ht]
    have hQ : closure (toExt R) ⊆ S := closure_minimal hRA hSc
    have hQc : IsPreconnected (closure (toExt R)) :=
      ((isPreconnected_Ici.image _ (by fun_prop)).image _ OnePoint.continuous_coe.continuousOn).closure
    have hinfQ : (extInf : ExtPlane) ∈ closure (toExt R) := by
      refine LiZhongQC.extInf_mem_closure_toExt_of_unbounded fun M => ?_
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (|M| + ‖p‖ + 1) / ‖v - p‖ + 1 := ⟨_, rfl⟩
      have ht0 : 0 ≤ (|M| + ‖p‖ + 1) / ‖v - p‖ := by positivity
      have ht1 : 1 ≤ t := by rw [ht]; linarith
      refine ⟨_, ⟨t, mem_Ici.2 ht1, rfl⟩, ?_⟩
      have h1 : ‖((t : ℝ) : ℂ) * (v - p)‖ ≤ ‖p + ((t : ℝ) : ℂ) * (v - p)‖ + ‖p‖ := by
        calc ‖((t : ℝ) : ℂ) * (v - p)‖ = ‖(p + ((t : ℝ) : ℂ) * (v - p)) - p‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖p + ((t : ℝ) : ℂ) * (v - p)‖ + ‖p‖ := norm_sub_le _ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
      have h2 : t * ‖v - p‖ = |M| + ‖p‖ + 1 + ‖v - p‖ := by
        rw [ht]
        field_simp
      nlinarith [le_abs_self M]
    have hvQ : (v : ExtPlane) ∈ closure (toExt R) :=
      subset_closure ⟨v, ⟨1, mem_Ici.2 le_rfl, by simp⟩, rfl⟩
    refine insert_subset_iff.2 ⟨?_, singleton_subset_iff.2 (mem_connectedComponentIn hinfS)⟩
    exact (hQc.subset_connectedComponentIn hinfQ hQ) hvQ
  · -- `p` and `∞` lie in different components: split `ℂ̄ ∖ A` by the circle of radius `(r₁ + r₂)/2`
    set r := (r₁ + r₂) / 2 with hr
    have hr₁ : r₁ < r := by rw [hr]; linarith
    have hr₂ : r < r₂ := by rw [hr]; linarith
    have hU₁ : IsOpen (toExt (ball p r)) := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
    have hU₂ : IsOpen (toExt (closedBall p r))ᶜ :=
      isClosed_compl_iff.1 (by rw [compl_compl]; exact ((isCompact_closedBall p r).image
        OnePoint.continuous_coe).isClosed)
    have hdisj : Disjoint (toExt (ball p r)) (toExt (closedBall p r))ᶜ :=
      Set.disjoint_left.2 fun x hx hx' => hx' (image_mono ball_subset_closedBall hx)
    have hcover : S ⊆ toExt (ball p r) ∪ (toExt (closedBall p r))ᶜ := by
      intro x hx
      induction x using OnePoint.rec with
      | infty => exact Or.inr fun ⟨w, _, hw⟩ => OnePoint.coe_ne_infty w hw
      | coe w =>
        have hwA : w ∉ A := fun h => hx ⟨w, h, rfl⟩
        by_cases hw : ‖w - p‖ < r
        · exact Or.inl ⟨w, mem_ball_iff_norm.2 hw, rfl⟩
        · right
          rintro ⟨w', hw', hww'⟩
          rw [OnePoint.coe_injective hww'] at hw'
          have h1 := mem_closedBall_iff_norm.1 hw'
          have h2 : r₂ ≤ ‖w - p‖ := by
            by_contra h3
            exact hwA ⟨by linarith, by linarith⟩
          linarith
    intro heq
    have hsub := isPreconnected_connectedComponentIn.subset_left_of_subset_union hU₁ hU₂ hdisj
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨_, mem_connectedComponentIn hpS, ⟨p, mem_ball_self (h₁.trans hr₁), rfl⟩⟩
    have hinf : (extInf : ExtPlane) ∈ connectedComponentIn S ((p : ℂ) : ExtPlane) := by
      rw [heq]
      exact mem_connectedComponentIn hinfS
    obtain ⟨w, -, hw⟩ := hsub hinf
    exact OnePoint.coe_ne_infty w hw

/-- Helper for `lemma14_3_a`: three-point distortion of a `K`-quasiconformal map `F` of `ℂ` onto `ℂ`. If
`|a − b| ≤ |c − b|` then `|F(a) − F(b)| ≤ e^{Kπ} |F(c) − F(b)|`: the annulus about `F(b)` with radii `|F(c) − F(b)|`,
`|F(a) − F(b)|` has modulus `log t`; its preimage separates `{b, c}` from `{a, ∞}`, so by the modulus theorem of
Teichmüller its modulus is at most `2μ(1/√2) = π`, and the quasi-invariance of the modulus gives `log t ≤ Kπ`. -/
theorem gl14_three_point {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hFs : F '' univ = univ) {a b c : ℂ}
    (hab : a ≠ b) (habc : ‖a - b‖ ≤ ‖c - b‖) : ‖F a - F b‖ ≤ Real.exp (K * π) * ‖F c - F b‖ := by
  have hK : 1 ≤ K := hF.2.1
  have hFh : LiZhongQC.IsHomeomorphOnto F univ univ := by
    have h := hF.2.2.1
    rwa [hFs] at h
  have hFinj : Function.Injective F := fun u v h => hFh.2.1 (mem_univ u) (mem_univ v) h
  have hab0 : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hcb : c ≠ b := fun h => by
    rw [h, sub_self, norm_zero] at habc
    linarith
  have hcb0 : 0 < ‖c - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hcb)
  set r₁ := ‖F c - F b‖ with hr₁
  set r₂ := ‖F a - F b‖ with hr₂
  have hr₁0 : 0 < r₁ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hcb (hFinj h))
  have hexp : 1 ≤ Real.exp (K * π) := Real.one_le_exp (by positivity)
  rcases le_or_gt r₂ r₁ with hle | hlt
  · exact hle.trans (le_mul_of_one_le_left hr₁0.le hexp)
  -- `H = F⁻¹ − b` is a `K`-q.c. map of `ℂ` onto `ℂ` with `H(F z) = z − b`
  set G := Function.invFunOn F univ with hG
  have hGF : ∀ z, G (F z) = z := fun z => hFh.2.1.leftInvOn_invFunOn (mem_univ z)
  have hGq : IsKQC G univ K := by
    have h := LiZhongQC.thm7_2_inv hF
    rwa [hFs] at h
  have hGs : G '' univ = univ := eq_univ_of_forall fun z => ⟨F z, mem_univ _, hGF z⟩
  obtain ⟨hHq, hHs⟩ := LiZhongQC.bB_l_affine_isKQC hGq hGs b one_ne_zero
  set H : ℂ → ℂ := fun ζ => (G ζ - b) / 1 with hH
  have hHval : ∀ z, H (F z) = z - b := fun z => by simp [hH, hGF]
  have hHh : LiZhongQC.IsHomeomorphOnto H univ univ := by
    have h := hHq.2.2.1
    rwa [hHs] at h
  obtain ⟨e, he⟩ := LiZhongQC.s13x_de_exists_homeomorph hHh
  -- the annulus `A` about `F b` and its image `H(A)`
  set A := LiZhongQC.annulusAt (F b) r₁ r₂ with hA
  have hAdc : LiZhongQC.IsDoublyConnected A := LiZhongQC.nf_g_isDoublyConnected_annulusAt (F b) hr₁0 hlt
  have hAmod := LiZhongQC.nf_e_dcModulus_annulusAt (F b) hr₁0 hlt
  have hAcl : closure (toExt A) ⊆ toExt univ :=
    (LiZhongQC.nf_e_closure_toExt_subset (isCompact_closedBall (F b) r₂)
      fun w hw => mem_closedBall_iff_norm.2 hw.2.le).trans (image_mono (subset_univ _))
  obtain ⟨hDdc, hmodle, -⟩ := LiZhongQC.thm7_4_dcModulus_quasi_invariance hHq hAdc hAcl
  have hsep : LiZhongQC.SeparatesSets (H '' A) {((0 : ℂ) : ExtPlane), ((c - b : ℂ) : ExtPlane)}
      {((a - b : ℂ) : ExtPlane), extInf} := by
    have h := gl14_sep_image e (gl14_sep_annulusAt (u := F c) (v := F a) hr₁0 hlt le_rfl rfl)
    rw [he] at h
    convert h using 2 <;> simp [Homeomorph.onePointCongr_apply, he, hHval]
  have hT := LiZhongQC.thm5_3_teichmuller_modulus_theorem (sub_ne_zero.2 hcb) (sub_ne_zero.2 hab) hDdc hsep
  -- `μ(√(|c − b|/(|c − b| + |a − b|))) ≤ μ(1/√2) = π/2`
  have hmu : LiZhongQC.grotzschMu (Real.sqrt (‖c - b‖ / (‖c - b‖ + ‖a - b‖))) ≤ π / 2 := by
    rw [← LiZhongQC.eq5_21]
    have hx0 : 0 < ‖c - b‖ / (‖c - b‖ + ‖a - b‖) := by positivity
    have hx1 : ‖c - b‖ / (‖c - b‖ + ‖a - b‖) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hx2 : 1 / 2 ≤ ‖c - b‖ / (‖c - b‖ + ‖a - b‖) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hs2 : 1 / Real.sqrt 2 = Real.sqrt (1 / 2) := by
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    refine LiZhongQC.grotzschMu_strictAntiOn.antitoneOn ⟨by positivity, ?_⟩
      ⟨Real.sqrt_pos.2 hx0, ?_⟩ ?_
    · rw [hs2, Real.sqrt_lt' one_pos]
      norm_num
    · rw [Real.sqrt_lt' one_pos]
      linarith
    · rw [hs2]
      exact Real.sqrt_le_sqrt hx2
  rw [hAmod] at hmodle
  have hfin : ENNReal.ofReal (Real.log (r₂ / r₁)) ≤ ENNReal.ofReal (K * π) := by
    calc ENNReal.ofReal (Real.log (r₂ / r₁)) ≤ ENNReal.ofReal K * LiZhongQC.dcModulus (H '' A) := hmodle
      _ ≤ ENNReal.ofReal K *
          ENNReal.ofReal (2 * LiZhongQC.grotzschMu (Real.sqrt (‖c - b‖ / (‖c - b‖ + ‖a - b‖)))) := by
          gcongr
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal π := by
          gcongr
          linarith
      _ = ENNReal.ofReal (K * π) := (ENNReal.ofReal_mul (by linarith)).symm
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  have h := Real.exp_le_exp.2 hfin
  rw [Real.exp_log (div_pos (hr₁0.trans hlt) hr₁0), div_le_iff₀ hr₁0] at h
  exact h

/-- Helper for `lemma14_3_b`: `C ∩ ℂ` is closed and nonempty, and its complement in `ℂ` is `Ω ∪ Ω*`. -/
theorem gl14_cfin {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) :
    IsClosed {w : ℂ | (w : ExtPlane) ∈ C} ∧ {w : ℂ | (w : ExtPlane) ∈ C}.Nonempty ∧
      ∀ z : ℂ, (z : ExtPlane) ∉ C ↔ z ∈ Ω ∪ Ωs := by
  obtain ⟨⟨K', hK'⟩, hinf, -, -, -, -, -, hunion⟩ := hc
  obtain ⟨g, hg, hgs, hC⟩ := LiZhongQC.tp_quasicircle_through_inf hK' hinf
  have hCfin : {w : ℂ | (w : ExtPlane) ∈ C} = g '' LiZhongQC.realLine := by
    ext w
    constructor
    · intro hw
      have hw' : (w : ExtPlane) ∈ C := hw
      rw [hC] at hw'
      rcases hw' with ⟨u, hu, hwu⟩ | hw'
      · rw [← OnePoint.coe_injective hwu]
        exact hu
      · exact absurd hw' (OnePoint.coe_ne_infty w)
    · intro hw
      show (w : ExtPlane) ∈ C
      rw [hC]
      exact Or.inl ⟨w, hw, rfl⟩
  refine ⟨?_, ?_, fun z => ?_⟩
  · have hgh : LiZhongQC.IsHomeomorphOnto g univ univ := by
      have h := hg.2.2.1
      rwa [hgs] at h
    obtain ⟨e, he⟩ := LiZhongQC.s13x_de_exists_homeomorph hgh
    rw [hCfin, ← he, e.isClosed_image]
    exact isClosed_eq Complex.continuous_im continuous_const
  · exact ⟨g 0, hCfin ▸ ⟨0, by simp [LiZhongQC.realLine], rfl⟩⟩
  · constructor
    · intro hz
      have h : (z : ExtPlane) ∈ toExt Ω ∪ toExt Ωs := by rw [hunion]; exact hz
      rcases h with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
      · exact Or.inl (OnePoint.coe_injective hzu ▸ hu)
      · exact Or.inr (OnePoint.coe_injective hzu ▸ hu)
    · intro hz
      have h : (z : ExtPlane) ∈ toExt Ω ∪ toExt Ωs := by
        rcases hz with h | h
        · exact Or.inl ⟨z, h, rfl⟩
        · exact Or.inr ⟨z, h, rfl⟩
      rw [hunion] at h
      exact h

/-- Helper for `lemma14_3_b`: the disc of radius `δ(z)` about `z ∈ Ω` lies in `Ω` (it avoids `C`, is connected and
contains `z`). -/
theorem gl14_ball_subset {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    ball z (infDist z {w : ℂ | (w : ExtPlane) ∈ C}) ⊆ Ω := by
  obtain ⟨hcl, hne, hcomp⟩ := gl14_cfin hc
  have hsub : ball z (infDist z {w : ℂ | (w : ExtPlane) ∈ C}) ⊆ Ω ∪ Ωs := by
    intro w hw
    refine (hcomp w).1 (fun hwC => ?_)
    have h1 := infDist_le_dist_of_mem (show w ∈ {w : ℂ | (w : ExtPlane) ∈ C} from hwC) (x := z)
    rw [mem_ball, dist_comm] at hw
    linarith
  rcases (convex_ball z _).isPreconnected.subset_or_subset hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2.2.1 hsub with h | h
  · exact h
  · have hzC : z ∉ {w : ℂ | (w : ExtPlane) ∈ C} := fun h' => (hcomp z).2 (Or.inl hz) h'
    have hδ : 0 < infDist z {w : ℂ | (w : ExtPlane) ∈ C} := (hcl.notMem_iff_infDist_pos hne).1 hzC
    exact absurd (h (mem_ball_self hδ)) (Set.disjoint_left.1 hc.2.2.2.2.2.2.1 hz)

/-- Helper for `lemma14_4`: the disc of radius `δ(z)` about `z` is a competitor in `ρ_Ω(z)`. -/
theorem gl14_density_mem {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    (infDist z {w : ℂ | (w : ExtPlane) ∈ C})⁻¹ ∈ {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧
      MapsTo g unitDisc Ω ∧ g 0 = z ∧ deriv g 0 ≠ 0 ∧ r = 1 / ‖deriv g 0‖} := by
  obtain ⟨hcl, hne, hcomp⟩ := gl14_cfin hc
  have hzC : z ∉ {w : ℂ | (w : ExtPlane) ∈ C} := fun h' => (hcomp z).2 (Or.inl hz) h'
  have hδ : 0 < infDist z {w : ℂ | (w : ExtPlane) ∈ C} := (hcl.notMem_iff_infDist_pos hne).1 hzC
  have hball := gl14_ball_subset hc hz
  set δ := infDist z {w : ℂ | (w : ExtPlane) ∈ C} with hδdef
  have hd : HasDerivAt (fun ζ : ℂ => z + (δ : ℂ) * ζ) (δ : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (δ : ℂ)).const_add z
  refine ⟨fun ζ => z + (δ : ℂ) * ζ, by fun_prop, ?_, by simp, ?_, ?_⟩
  · intro ζ hζ
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
    have : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    nlinarith
  · rw [hd.deriv]
    exact ofReal_ne_zero.2 hδ.ne'
  · rw [hd.deriv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, one_div]

/-- Helper for `lemma14_4`: `ρ_Ω(z) ≤ 1/δ(z)` (the disc of radius `δ(z)` about `z` is a competitor). -/
theorem gl14_density_le {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    poincareDensityGL Ω z ≤ (infDist z {w : ℂ | (w : ExtPlane) ∈ C})⁻¹ := by
  unfold poincareDensityGL
  refine csInf_le ⟨0, ?_⟩ (gl14_density_mem hc hz)
  rintro r ⟨g, -, -, -, -, rfl⟩
  positivity

/-- Helper for `gl14_refl_qc`: a homeomorphism `g` of `ℂ` maps the real line onto an unbounded set. -/
theorem gl14_image_realLine_unbounded {g : ℂ → ℂ} (hg : LiZhongQC.IsHomeomorphOnto g univ univ) :
    ¬ Bornology.IsBounded (g '' LiZhongQC.realLine) := by
  obtain ⟨e, he⟩ := LiZhongQC.s13x_de_exists_homeomorph hg
  intro hb
  -- `ℝ = e⁻¹(e(ℝ))` would be bounded
  have hc : IsCompact (e.symm '' closure (g '' LiZhongQC.realLine)) :=
    hb.isCompact_closure.image e.symm.continuous
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ e.symm '' closure (g '' LiZhongQC.realLine) :=
    ⟨g ((R + 1 : ℝ) : ℂ), subset_closure ⟨_, by simp [LiZhongQC.realLine], rfl⟩, by
      rw [← he, e.symm_apply_apply]⟩
  have h := mem_closedBall_zero_iff.1 (hR hmem)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  have := le_abs_self (R + 1)
  linarith

/-- Helper for `gl14_density_ge`: the complement of `Ω` in `ℂ̄`, namely `Ω* ∪ C`, is connected (the closure of `Ω*`
meets the connected set `C = g(ℝ) ∪ {∞}`). -/
theorem gl14_compl_connected {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) :
    IsConnected (toExt Ω)ᶜ := by
  obtain ⟨⟨K', hK'⟩, hinf, hΩo, hΩso, hΩc, hΩsc, hdisj, hunion⟩ := hc
  obtain ⟨g, hg, hgs, hC⟩ := LiZhongQC.tp_quasicircle_through_inf hK' hinf
  have hgh : LiZhongQC.IsHomeomorphOnto g univ univ := by
    have h := hg.2.2.1
    rwa [hgs] at h
  have hgc : Continuous g := continuousOn_univ.1 hgh.1
  set T : Set ExtPlane := toExt Ωs with hT
  have hcomplEq : (toExt Ω)ᶜ = T ∪ C := by
    ext x
    constructor
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inr hxC
      · have h : x ∈ toExt Ω ∪ toExt Ωs := by rw [hunion]; exact hxC
        exact Or.inl (h.resolve_left hx)
    · rintro (hx | hx) hxΩ
      · obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨u', hu', hu'u⟩ := hxΩ
        exact Set.disjoint_left.1 hdisj (OnePoint.coe_injective hu'u ▸ hu') hu
      · have h : x ∈ Cᶜ := by rw [← hunion]; exact Or.inl hxΩ
        exact h hx
  rw [hcomplEq]
  -- `C = g(ℝ) ∪ {∞}` is connected
  have hRconn : IsPreconnected LiZhongQC.realLine :=
    (convex_hyperplane Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  have hgRconn : IsPreconnected (toExt (g '' LiZhongQC.realLine)) :=
    (hRconn.image g hgc.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  have hinfcl : (extInf : ExtPlane) ∈ closure (toExt (g '' LiZhongQC.realLine)) :=
    LiZhongQC.extInf_mem_closure_toExt_of_not_isBounded (gl14_image_realLine_unbounded hgh)
  have hCconn : IsPreconnected C := by
    rw [hC]
    refine hgRconn.subset_closure subset_union_left (union_subset subset_closure ?_)
    rw [singleton_subset_iff]
    exact hinfcl
  -- `closure T ⊆ T ∪ C`, and `closure T` meets `C`
  have hTo : IsOpen T := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩso
  have hΩo' : IsOpen (toExt Ω) := OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩo
  have hTΩ : Disjoint T (toExt Ω) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', hu'u⟩
    exact Set.disjoint_left.1 hdisj (OnePoint.coe_injective hu'u ▸ hu') hu
  have hclT : closure T ⊆ T ∪ C := by
    rw [← hcomplEq]
    exact closure_minimal (fun x hx hxΩ => Set.disjoint_left.1 hTΩ hx hxΩ) hΩo'.isClosed_compl
  have hTne : T.Nonempty := hΩsc.nonempty.image _
  have hmeet : (closure T ∩ C).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hTcl : IsClosed T := by
      refine closure_subset_iff_isClosed.1 fun x hx => ?_
      rcases hclT hx with h | h
      · exact h
      · exact absurd (show x ∈ closure T ∩ C from ⟨hx, h⟩) (by rw [hno]; exact notMem_empty x)
    rcases isClopen_iff.1 ⟨hTcl, hTo⟩ with h | h
    · exact hTne.ne_empty h
    · have : (extInf : ExtPlane) ∈ T := by rw [h]; exact mem_univ _
      obtain ⟨u, -, hu⟩ := this
      exact OnePoint.coe_ne_infty u hu
  have hU : IsPreconnected (closure T ∪ C) :=
    (hΩsc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).closure.union' hmeet hCconn
  have heq : closure T ∪ C = T ∪ C :=
    Subset.antisymm (union_subset hclT subset_union_right) (union_subset_union_left _ subset_closure)
  rw [← heq]
  exact ⟨hTne.mono (subset_closure.trans subset_union_left), hU⟩

/-- Helper for `lemma14_4`: `1/(4δ(z)) ≤ ρ_Ω(z)`. The complement of `Ω` in `ℂ̄` is connected, so `Ω` has a Riemann
map `f` with `f(0) = z`; every competitor factors through `f` (Schwarz's lemma), and `|f′(0)| ≤ 4δ(z)` by Koebe's
one-quarter theorem (Pommerenke `cor1_4`). -/
theorem gl14_density_ge {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    (4 * infDist z {w : ℂ | (w : ExtPlane) ∈ C})⁻¹ ≤ poincareDensityGL Ω z := by
  obtain ⟨hcl, hne, hcomp⟩ := gl14_cfin hc
  have hzC : z ∉ {w : ℂ | (w : ExtPlane) ∈ C} := fun h' => (hcomp z).2 (Or.inl hz) h'
  have hδ : 0 < infDist z {w : ℂ | (w : ExtPlane) ∈ C} := (hcl.notMem_iff_infDist_pos hne).1 hzC
  have hball := gl14_ball_subset hc hz
  have hcompl := gl14_compl_connected hc
  have hmem := gl14_density_mem hc hz
  set δ := infDist z {w : ℂ | (w : ExtPlane) ∈ C} with hδdef
  obtain ⟨-, -, hΩo, -, hΩc, -, -, -⟩ := hc
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀Ω : w₀ ∉ Ω := fun h => (hcomp w₀).2 (Or.inl h) hw₀
  -- the Riemann map `f : Ω → 𝔻` with `f z = 0` and its inverse `φ`
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hΩo hΩc ⟨w₀, hw₀Ω⟩
    (LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl hΩo hΩc hcompl) hz
  obtain ⟨hφd, hφb⟩ := RMT.invFunOn_riemannMap hΩo hf.diff hf.injOn hfb
  set φ := Function.invFunOn f Ω with hφ
  have hφ0 : φ 0 = z := by
    rw [← hf.center]
    exact hf.injOn.leftInvOn_invFunOn hz
  have h0D : (0 : ℂ) ∈ RMT.disc := mem_ball_self one_pos
  -- Koebe: `|φ′(0)| ≤ 4 dist(z, ∂Ω) ≤ 4 δ`
  have hK := (Pommerenke1992.cor1_4 hφd hφb.injOn h0D).1
  have hdist : Pommerenke1992.distToBoundary φ 0 ≤ δ := by
    obtain ⟨w, hwC, hwd⟩ := hcl.exists_infDist_eq_dist ⟨w₀, hw₀⟩ z
    show infDist (φ 0) (frontier (φ '' unitDisc)) ≤ δ
    rw [hφ0, show φ '' unitDisc = Ω from hφb.image_eq]
    have hwcl : w ∈ closure Ω := by
      refine closure_mono hball ?_
      rw [closure_ball z hδ.ne', mem_closedBall, dist_comm, ← hwd]
    have hwΩ : w ∉ Ω := fun h => (hcomp w).2 (Or.inl h) hwC
    have hwfr : w ∈ frontier Ω := ⟨hwcl, by rwa [hΩo.interior_eq]⟩
    exact (infDist_le_dist_of_mem hwfr).trans hwd.ge
  have hφ4 : ‖deriv φ 0‖ ≤ 4 * δ := by
    have h := hK.trans hdist
    rw [norm_zero, zero_pow two_ne_zero, sub_zero, mul_one] at h
    linarith
  -- every competitor `g` factors as `φ ∘ (f ∘ g)`, so `|g′(0)| ≤ |φ′(0)|` by Schwarz's lemma
  unfold poincareDensityGL
  refine le_csInf ⟨δ⁻¹, ?_⟩ ?_
  · exact hmem
  · rintro r ⟨g, hgd, hgm, hg0, hgd0, rfl⟩
    have hhd : DifferentiableOn ℂ (f ∘ g) unitDisc := hf.diff.comp hgd hgm
    have hhm : MapsTo (f ∘ g) unitDisc unitDisc := hf.mapsTo.comp hgm
    have hh0 : (f ∘ g) 0 = 0 := by simp [hg0, hf.center]
    have hschwarz : ‖deriv (f ∘ g) 0‖ ≤ 1 :=
      Complex.norm_deriv_le_one_of_mapsTo_ball hhd (by rw [hh0]; exact hhm.mono_right ball_subset_closedBall)
        one_pos
    have hgeq : ∀ ζ ∈ unitDisc, g ζ = φ ((f ∘ g) ζ) := fun ζ hζ =>
      (hf.injOn.leftInvOn_invFunOn (hgm hζ)).symm
    have hderiv : deriv g 0 = deriv φ 0 * deriv (f ∘ g) 0 := by
      have h1 : HasDerivAt (f ∘ g) (deriv (f ∘ g) 0) 0 :=
        (hhd.differentiableAt (ball_mem_nhds 0 one_pos)).hasDerivAt
      have h2 : HasDerivAt φ (deriv φ 0) ((f ∘ g) 0) := by
        rw [hh0]
        exact (hφd.differentiableAt (ball_mem_nhds 0 one_pos)).hasDerivAt
      have hev : g =ᶠ[𝓝 0] φ ∘ (f ∘ g) := Filter.eventually_of_mem (ball_mem_nhds 0 one_pos) hgeq
      exact ((h2.comp 0 h1).congr_of_eventuallyEq hev).deriv
    have hgφ : ‖deriv g 0‖ ≤ ‖deriv φ 0‖ := by
      rw [hderiv, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hschwarz
    rw [one_div]
    exact inv_anti₀ (norm_pos_iff.2 hgd0) (hgφ.trans hφ4)

/-- Helper for `lemma14_3_b`: the configuration `Ω, C, Ω*` is also one for `Ω*, C, Ω`. -/
theorem gl14_config_symm {C : Set ExtPlane} {Ω Ωs : Set ℂ} (hc : IsQCConfiguration C Ω Ωs) :
    IsQCConfiguration C Ωs Ω := by
  obtain ⟨hq, hinf, hΩo, hΩso, hΩc, hΩsc, hdisj, hunion⟩ := hc
  exact ⟨hq, hinf, hΩso, hΩo, hΩsc, hΩc, hdisj.symm, by rw [union_comm]; exact hunion⟩

/-- Helper for `lemma14_3_b`: a reflection of the configuration `Ω, C, Ω*` is also one of `Ω*, C, Ω`. -/
theorem gl14_refl_symm {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ} (hj : IsReflectionGL C Ω Ωs j K) :
    IsReflectionGL C Ωs Ω j K := by
  obtain ⟨hjc, hjj, hjC, hjΩ, hK1, hK2⟩ := hj
  refine ⟨hjc, hjj, hjC, ?_, hK2, hK1⟩
  rw [← hjΩ, image_image]
  simp only [hjj, image_id']

/-- Helper for `lemma14_3_a`: for `z ∈ Ω ∪ Ω*` and `z₀ ∈ C`, `|z − z₀| ≤ e^{Kπ} |j(z) − z₀|` and
`|j(z) − z₀| ≤ e^{Kπ} |z − z₀|` (`gl14_three_point` for `conj ∘ j`, which fixes `z₀` up to conjugation). -/
theorem gl14_refl_ratio {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ} (hc : IsQCConfiguration C Ω Ωs)
    (hj : IsReflectionGL C Ω Ωs j K) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ C) {z : ℂ} (hz : z ∈ Ω ∪ Ωs) :
    ‖z - z₀‖ ≤ Real.exp (K * π) * ‖j z - z₀‖ ∧ ‖j z - z₀‖ ≤ Real.exp (K * π) * ‖z - z₀‖ := by
  obtain ⟨hF, hFs⟩ := gl14_refl_qc hc hj
  have hK : 1 ≤ K := hF.2.1
  have hexp : 1 ≤ Real.exp (K * π) := Real.one_le_exp (by positivity)
  have hzC : (z : ExtPlane) ∉ C := ((gl14_cfin hc).2.2 z).2 hz
  have hz0 : z ≠ z₀ := fun h => hzC (h ▸ hz₀)
  have hjz0 : j z₀ = z₀ := hj.2.2.1 z₀ hz₀
  have hjz : j z ≠ z₀ := by
    intro h
    apply hz0
    rw [← hj.2.1 z, h, hjz0]
  have hnorm : ∀ u v : ℂ, ‖conj u - conj v‖ = ‖u - v‖ := fun u v => by
    rw [← map_sub, Complex.norm_conj]
  rcases le_total ‖j z - z₀‖ ‖z - z₀‖ with h | h
  · have h3 := gl14_three_point hF hFs hjz h
    simp only [hj.2.1 z, hjz0, hnorm] at h3
    exact ⟨h3, h.trans (le_mul_of_one_le_left (norm_nonneg _) hexp)⟩
  · have h3 := gl14_three_point hF hFs hz0 h
    simp only [hj.2.1 z, hjz0, hnorm] at h3
    exact ⟨h.trans (le_mul_of_one_le_left (norm_nonneg _) hexp), h3⟩

/-- Helper for `lemma14_3_b`: `0 < δ(z) ≤ |j(z) − z| ≤ (e^{Kπ} + 1) δ(z)` for `z ∈ Ω ∪ Ω*` (the disc of radius `δ(z)`
about `z` stays on the side of `z`; the nearest point of `C` and `gl14_refl_ratio`). -/
theorem gl14_refl_dist {C : Set ExtPlane} {Ω Ωs : Set ℂ} {j : ℂ → ℂ} {K : ℝ} (hc : IsQCConfiguration C Ω Ωs)
    (hj : IsReflectionGL C Ω Ωs j K) {z : ℂ} (hz : z ∈ Ω ∪ Ωs) :
    0 < infDist z {w : ℂ | (w : ExtPlane) ∈ C} ∧ infDist z {w : ℂ | (w : ExtPlane) ∈ C} ≤ ‖j z - z‖ ∧
      ‖j z - z‖ ≤ (Real.exp (K * π) + 1) * infDist z {w : ℂ | (w : ExtPlane) ∈ C} := by
  obtain ⟨hcl, hne, hcomp⟩ := gl14_cfin hc
  have hzC : z ∉ {w : ℂ | (w : ExtPlane) ∈ C} := (hcomp z).2 hz
  refine ⟨(hcl.notMem_iff_infDist_pos hne).1 hzC, ?_, ?_⟩
  · -- `j z` lies on the other side, outside the disc of radius `δ(z)` about `z`
    by_contra hlt
    rw [not_le] at hlt
    have hmem : j z ∈ ball z (infDist z {w : ℂ | (w : ExtPlane) ∈ C}) := by
      rw [mem_ball, dist_eq_norm]
      exact hlt
    rcases hz with hzΩ | hzΩs
    · have hjz : j z ∈ Ωs := hj.2.2.2.1 ▸ mem_image_of_mem j hzΩ
      exact Set.disjoint_left.1 hc.2.2.2.2.2.2.1 (gl14_ball_subset hc hzΩ hmem) hjz
    · have hjz : j z ∈ Ω := (gl14_refl_symm hj).2.2.2.1 ▸ mem_image_of_mem j hzΩs
      exact Set.disjoint_left.1 hc.2.2.2.2.2.2.1 hjz (gl14_ball_subset (gl14_config_symm hc) hzΩs hmem)
  · -- the nearest point `z₀ ∈ C ∩ ℂ`
    obtain ⟨z₀, hz₀, hdist⟩ := hcl.exists_infDist_eq_dist hne z
    have h := (gl14_refl_ratio hc hj hz₀ hz).2
    rw [hdist, dist_eq_norm]
    calc ‖j z - z‖ ≤ ‖j z - z₀‖ + ‖z₀ - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Real.exp (K * π) * ‖z - z₀‖ + ‖z - z₀‖ := by
          rw [norm_sub_rev z₀ z]
          gcongr
      _ = (Real.exp (K * π) + 1) * ‖z - z₀‖ := by ring

/-- **Lemma 3 (a)** (§14.3, l. 10228; [Ahl64]). For a `K`-quasiconformal reflection `j` (`∞ ∈ C`) and `z₀ ∈ C`,
`M⁻¹ ≤ |j(z) − z₀| / |z − z₀| ≤ M` with `M = M(K)`. -/
theorem lemma14_3_a (K : ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ),
    IsQCConfiguration C Ω Ωs → IsReflectionGL C Ω Ωs j K → ∀ z₀ : ℂ, (z₀ : ExtPlane) ∈ C → ∀ z ∈ Ω ∪ Ωs,
      M⁻¹ ≤ ‖j z - z₀‖ / ‖z - z₀‖ ∧ ‖j z - z₀‖ / ‖z - z₀‖ ≤ M := by
  refine ⟨Real.exp (K * π), Real.exp_pos _, fun C Ω Ωs j hc hj z₀ hz₀ z hz => ?_⟩
  obtain ⟨h1, h2⟩ := gl14_refl_ratio hc hj hz₀ hz
  have hzC : (z : ExtPlane) ∉ C := ((gl14_cfin hc).2.2 z).2 hz
  have hz0 : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hzC (h ▸ hz₀))
  have hM : 0 < Real.exp (K * π) := Real.exp_pos _
  constructor
  · rw [le_div_iff₀ hz0]
    calc (Real.exp (K * π))⁻¹ * ‖z - z₀‖ ≤ (Real.exp (K * π))⁻¹ * (Real.exp (K * π) * ‖j z - z₀‖) := by
          gcongr
      _ = ‖j z - z₀‖ := by field_simp
  · rw [div_le_iff₀ hz0]
    linarith

/-- **Lemma 3 (b)** (§14.3, l. 10230; [Ahl64]). `1 ≤ |j(z) − z| / δ(z) ≤ M`, `δ(z)` the Euclidean distance from `z` to
`C`. -/
theorem lemma14_3_b (K : ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ),
    IsQCConfiguration C Ω Ωs → IsReflectionGL C Ω Ωs j K → ∀ z ∈ Ω ∪ Ωs,
      1 ≤ ‖j z - z‖ / infDist z {w : ℂ | (w : ExtPlane) ∈ C} ∧
        ‖j z - z‖ / infDist z {w : ℂ | (w : ExtPlane) ∈ C} ≤ M := by
  refine ⟨Real.exp (K * π) + 1, by positivity, fun C Ω Ωs j hc hj z hz => ?_⟩
  obtain ⟨hδ, hlo, hhi⟩ := gl14_refl_dist hc hj hz
  exact ⟨(one_le_div hδ).2 hlo, (div_le_iff₀ hδ).2 hhi⟩

/-- **Lemma 3 (c)** (§14.3, l. 10231; [Ahl64]). `M⁻¹ ≤ δ(j(z)) / δ(z) ≤ M`. -/
theorem lemma14_3_c (K : ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ),
    IsQCConfiguration C Ω Ωs → IsReflectionGL C Ω Ωs j K → ∀ z ∈ Ω ∪ Ωs,
      M⁻¹ ≤ infDist (j z) {w : ℂ | (w : ExtPlane) ∈ C} / infDist z {w : ℂ | (w : ExtPlane) ∈ C} ∧
        infDist (j z) {w : ℂ | (w : ExtPlane) ∈ C} / infDist z {w : ℂ | (w : ExtPlane) ∈ C} ≤ M := by
  refine ⟨Real.exp (K * π) + 1, by positivity, fun C Ω Ωs j hc hj z hz => ?_⟩
  have hjz : j z ∈ Ω ∪ Ωs := by
    rcases hz with hzΩ | hzΩs
    · exact Or.inr (hj.2.2.2.1 ▸ mem_image_of_mem j hzΩ)
    · exact Or.inl ((gl14_refl_symm hj).2.2.2.1 ▸ mem_image_of_mem j hzΩs)
  obtain ⟨hδ, hlo, hhi⟩ := gl14_refl_dist hc hj hz
  obtain ⟨hδ', hlo', hhi'⟩ := gl14_refl_dist hc hj hjz
  rw [hj.2.1 z, norm_sub_rev] at hlo' hhi'
  have hM : 0 < Real.exp (K * π) + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hδ]
    calc (Real.exp (K * π) + 1)⁻¹ * infDist z {w : ℂ | (w : ExtPlane) ∈ C}
        ≤ (Real.exp (K * π) + 1)⁻¹ * ((Real.exp (K * π) + 1) * infDist (j z) {w : ℂ | (w : ExtPlane) ∈ C}) := by
          gcongr
          linarith
      _ = infDist (j z) {w : ℂ | (w : ExtPlane) ∈ C} := by field_simp
  · rw [div_le_iff₀ hδ]
    linarith

/-- **Lemma 4** ((14.13), §14.3, l. 10270; [EN86]). For a `K`-quasiconformal reflection `j`,
`1/16 ≤ |z − j(z)|² ρ(z) ρ(j(z)) ≤ M(K)` for `z ∈ Ω` (`ρ` the Poincaré densities of `Ω` and `Ω*`). -/
theorem lemma14_4 (K : ℝ) : ∃ M : ℝ, ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ),
    IsQCConfiguration C Ω Ωs → IsReflectionGL C Ω Ωs j K → ∀ z ∈ Ω,
      1 / 16 ≤ ‖z - j z‖ ^ 2 * poincareDensityGL Ω z * poincareDensityGL Ωs (j z) ∧
        ‖z - j z‖ ^ 2 * poincareDensityGL Ω z * poincareDensityGL Ωs (j z) ≤ M := by
  refine ⟨(Real.exp (K * π) + 1) ^ 2, fun C Ω Ωs j hc hj z hz => ?_⟩
  have hjz : j z ∈ Ωs := hj.2.2.2.1 ▸ mem_image_of_mem j hz
  obtain ⟨hδ, hlo, hhi⟩ := gl14_refl_dist hc hj (Or.inl hz)
  obtain ⟨hδ', hlo', hhi'⟩ := gl14_refl_dist hc hj (Or.inr hjz)
  rw [hj.2.1 z] at hlo' hhi'
  rw [norm_sub_rev] at hlo hhi
  have hρ1 := gl14_density_ge hc hz
  have hρ2 := gl14_density_ge (gl14_config_symm hc) hjz
  have hρ3 := gl14_density_le hc hz
  have hρ4 := gl14_density_le (gl14_config_symm hc) hjz
  set δ := infDist z {w : ℂ | (w : ExtPlane) ∈ C} with hδdef
  set δ' := infDist (j z) {w : ℂ | (w : ExtPlane) ∈ C} with hδ'def
  set d := ‖z - j z‖ with hd
  set M := Real.exp (K * π) + 1 with hMdef
  have hρ0 : 0 ≤ poincareDensityGL Ω z := (by positivity : (0 : ℝ) ≤ (4 * δ)⁻¹).trans hρ1
  have hρ0' : 0 ≤ poincareDensityGL Ωs (j z) := (by positivity : (0 : ℝ) ≤ (4 * δ')⁻¹).trans hρ2
  constructor
  · calc 1 / 16 ≤ d ^ 2 * (4 * δ)⁻¹ * (4 * δ')⁻¹ := by
          rw [show d ^ 2 * (4 * δ)⁻¹ * (4 * δ')⁻¹ = d ^ 2 / (16 * (δ * δ')) by field_simp; ring,
            le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ d ^ 2 * poincareDensityGL Ω z * poincareDensityGL Ωs (j z) := by gcongr
  · calc d ^ 2 * poincareDensityGL Ω z * poincareDensityGL Ωs (j z) ≤ d ^ 2 * δ⁻¹ * δ'⁻¹ := by gcongr
      _ ≤ M ^ 2 := by
          rw [show d ^ 2 * δ⁻¹ * δ'⁻¹ = d ^ 2 / (δ * δ') by field_simp, div_le_iff₀ (by positivity)]
          nlinarith

/-- **Theorem 2** ((14.15), §14.3, l. 10293; [EN86]). For the conformally natural Earle–Nag reflection `j`, if `j` is
`K`-quasiconformal then `M⁻¹ ≤ |z − j(z)|² ρ(j(z))² |j_z̄(z)| ≤ M(K)` for `z ∈ Ω` (`ρ` of `Ω*`). -/
theorem thm14_2 (K : ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ),
    IsQCConfiguration C Ω Ωs → IsEarleNagReflection C Ω Ωs j → IsReflectionGL C Ω Ωs j K → ∀ z ∈ Ω,
      M⁻¹ ≤ ‖z - j z‖ ^ 2 * poincareDensityGL Ωs (j z) ^ 2 * ‖dzbar j z‖ ∧
        ‖z - j z‖ ^ 2 * poincareDensityGL Ωs (j z) ^ 2 * ‖dzbar j z‖ ≤ M := by
  sorry

end GardinerLakic2000
