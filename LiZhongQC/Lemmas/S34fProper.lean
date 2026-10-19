import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.S34mManifold

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

/-! R83 S34 (精英下属5): `s34f_proper` (properness of `pr`, Kodaira–Spencer (ii)) for `thm34_1_bers`, with
the leader-approved statement (`cs hM hchart` added; IFACE_S34F_v3). -/

noncomputable section

namespace LiZhongQC

universe u v

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- `[·] : F(G₀) → V(G₀)` is continuous for the quotient topology. -/
theorem s34f_mk_cont [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance) :
    @Continuous (BersFiberSpace Γ) (BersQuotient Γ) _ τ (Quot.mk (bersFiberRel Γ)) := by
  subst hτ
  exact continuous_coinduced_rng

/-- A map out of `V(G₀)` is continuous when its composite with `[·]` is. -/
theorem s34f_cont_of_mk [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance) {Y : Type*} [TopologicalSpace Y]
    (f : BersQuotient Γ → Y) (h : Continuous fun x : BersFiberSpace Γ => f (Quot.mk (bersFiberRel Γ) x)) :
    Continuous f := by
  subst hτ
  exact continuous_coinduced_dom.2 h

/-- **`pr` is continuous**: on a chart source `[N]`, `pr = init ∘ ε` (chart clause). -/
theorem s34f_pr_cont {g : ℕ} (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (hopen : IsOpen (range coords))
    [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    [ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)]
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)))
    (hpr : ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q →
      (pr v : Fin (3 * g - 3) → ℂ) = coords q) :
    Continuous pr := by
  refine s34f_cont_of_mk hτ pr ?_
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨c, -, N, hN, hx₀, hs, hf⟩ := hchart x₀
  have hmk := s34f_mk_cont hτ
  have hsrc : ∀ x ∈ N, Quot.mk (bersFiberRel Γ) x ∈ c.source := fun x hx =>
    (Set.ext_iff.1 hs _).1 ⟨x, hx, rfl⟩
  have hca : ContinuousAt (fun x : BersFiberSpace Γ => Fin.init (c (Quot.mk (bersFiberRel Γ) x))) x₀ :=
    (continuous_pi fun j => continuous_apply _).continuousAt.comp
      ((c.continuousAt (hsrc x₀ hx₀)).comp hmk.continuousAt)
  refine hca.congr (Filter.eventually_of_mem (hN.mem_nhds hx₀) fun x hx => ?_)
  obtain ⟨q, hq⟩ := x.2.1
  show Fin.init (c (Quot.mk (bersFiberRel Γ) x)) = (pr (Quot.mk (bersFiberRel Γ) x) : Fin (3 * g - 3) → ℂ)
  rw [hf x hx q hq.symm, Fin.init_snoc, hpr q (Quot.mk (bersFiberRel Γ) x) hq.symm]

/-- **The given coordinates control the linear coordinates `e`**: if `coords qₙ → coords q₀` then
`e(Ψ(qₙ)) → e(Ψ(q₀))` (through the inverse of a chart of the chart clause at `(Ψ(q₀), f_{μ₀}(i))`). -/
theorem s34f_coord_tendsto (hΓ : IsFuchsian Γ) {g : ℕ} (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ)
    (hinj : Function.Injective coords) [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    [ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)]
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ)) (q₀ : TeichGamma Γ) {qs : ℕ → TeichGamma Γ}
    (hq : Tendsto (fun n => coords (qs n)) atTop (𝓝 (coords q₀))) :
    Tendsto (fun n => e ⟨bersMapGamma Γ (qs n), (bersMapGamma_mem hΓ (qs n)).1⟩) atTop
      (𝓝 (e ⟨bersMapGamma Γ q₀, (bersMapGamma_mem hΓ q₀).1⟩)) := by
  have hmem := s34m_fst_mem hΓ
  let E' : BersQuotient Γ → Fin m → ℂ := Quot.lift (fun x : BersFiberSpace Γ => e ⟨x.1.1, hmem x⟩) (by
    intro x y h
    obtain ⟨γ, -, hγ⟩ := h
    have h1 : (bersFiberSpaceAction Γ γ x.1).1 = y.1.1 := congrArg Prod.fst hγ
    exact congrArg e (Subtype.ext h1))
  have hE' : Continuous E' :=
    s34f_cont_of_mk hτ E' (e.continuous.comp (continuous_subtype_val.fst.subtype_mk hmem))
  have hI : Complex.I ∈ upperHalf := by
    show 0 < Complex.I.im
    rw [Complex.I_im]
    exact one_pos
  set z₀ := normalizedSolution (Quotient.out q₀).1.1 Complex.I with hz₀
  let x₀ : BersFiberSpace Γ := ⟨(bersMapGamma Γ q₀, z₀), ⟨q₀, rfl⟩, ⟨Quotient.out q₀, rfl, ⟨Complex.I, hI, rfl⟩⟩⟩
  obtain ⟨c, -, N, hN, hx₀, hs, hf⟩ := hchart x₀
  have hsrc : ∀ x ∈ N, Quot.mk (bersFiberRel Γ) x ∈ c.source := fun x hx =>
    (Set.ext_iff.1 hs _).1 ⟨x, hx, rfl⟩
  set w₀ : Fin (3 * g - 3 + 1) → ℂ := Fin.snoc (α := fun _ => ℂ) (coords q₀) z₀ with hw₀
  have hcx₀ : c (Quot.mk (bersFiberRel Γ) x₀) = w₀ := hf x₀ hx₀ q₀ rfl
  have hw₀t : w₀ ∈ c.target := hcx₀ ▸ c.map_source (hsrc x₀ hx₀)
  have hsw₀ : c.symm w₀ = Quot.mk (bersFiberRel Γ) x₀ := by
    rw [← hcx₀]
    exact c.left_inv (hsrc x₀ hx₀)
  have hsn : Continuous fun t : Fin (3 * g - 3) → ℂ => Fin.snoc (α := fun _ => ℂ) t z₀ :=
    Continuous.finSnoc (A := fun _ => ℂ) continuous_id continuous_const
  have hws : Tendsto (fun n => Fin.snoc (α := fun _ => ℂ) (coords (qs n)) z₀) atTop (𝓝 w₀) :=
    (hsn.tendsto (coords q₀)).comp hq
  have hG : Tendsto (fun n => E' (c.symm (Fin.snoc (α := fun _ => ℂ) (coords (qs n)) z₀))) atTop
      (𝓝 (E' (c.symm w₀))) :=
    (hE'.continuousAt.comp (c.continuousAt_symm hw₀t)).tendsto.comp hws
  rw [hsw₀] at hG
  refine hG.congr' ?_
  filter_upwards [hws.eventually (c.open_target.mem_nhds hw₀t)] with n hn
  obtain ⟨x, hx, hxe⟩ := (Set.ext_iff.1 hs _).2 (c.map_target hn)
  obtain ⟨q', hq'⟩ := x.2.1
  have h1 : Fin.snoc (α := fun _ => ℂ) (coords q') x.1.2 = Fin.snoc (α := fun _ => ℂ) (coords (qs n)) z₀ := by
    rw [← hf x hx q' hq'.symm, hxe]
    exact c.right_inv hn
  have h2 : coords q' = coords (qs n) := by
    have := congrArg Fin.init h1
    rwa [Fin.init_snoc, Fin.init_snoc] at this
  obtain rfl : q' = qs n := hinj h2
  rw [← hxe]
  exact congrArg e (Subtype.ext hq'.symm)

/-- **Convergent representatives** (`normalizedSolution_tendsto_of_bers`, `s34m_upper`): if `e(Ψ(qₙ)) → e(Ψ(q₀))`,
there are representatives `νₙ` of `qₙ` with `f_{νₙ} → f_{μ₀}` uniformly on compacta (`μ₀ = out q₀`). -/
theorem s34f_rep_tendsto (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) (q₀ : TeichGamma Γ) {qs : ℕ → TeichGamma Γ}
    (hE : Tendsto (fun n => e ⟨bersMapGamma Γ (qs n), (bersMapGamma_mem hΓ (qs n)).1⟩) atTop
      (𝓝 (e ⟨bersMapGamma Γ q₀, (bersMapGamma_mem hΓ q₀).1⟩))) :
    ∃ νs : ℕ → BeltramiGamma Γ, (∀ n, bersFunctionGamma (νs n) = bersMapGamma Γ (qs n)) ∧
      ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun n => normalizedSolution (νs n).1.1)
        (normalizedSolution (Quotient.out q₀).1.1) atTop K := by
  obtain ⟨b, hb, hup⟩ := s34m_upper hΓ e hfin
  have hn : Tendsto (fun n => ‖e ⟨bersMapGamma Γ (qs n), (bersMapGamma_mem hΓ (qs n)).1⟩ -
      e ⟨bersMapGamma Γ q₀, (bersMapGamma_mem hΓ q₀).1⟩‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hE
  have hu : Tendsto (fun n => ENNReal.ofReal (b * ‖e ⟨bersMapGamma Γ (qs n), (bersMapGamma_mem hΓ (qs n)).1⟩ -
      e ⟨bersMapGamma Γ q₀, (bersMapGamma_mem hΓ q₀).1⟩‖)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_nhds (x := b) |>.mul hn)
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  have hconv : Tendsto (fun n => bersNormL (bersFunctionGamma (Quotient.out (qs n)) -
      bersFunctionGamma (Quotient.out q₀))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
      (fun n => hup (Quotient.out (qs n)) (Quotient.out q₀))
  obtain ⟨νs, hrel, -, hunif⟩ := normalizedSolution_tendsto_of_bers hΓ hconv
  refine ⟨νs, fun n => ?_, hunif⟩
  exact (bersMapGamma_mem hΓ (qs n)).2.2 (νs n)
    ((Quotient.sound (s := teichSetoidGamma Γ) (hrel n)).trans (Quotient.out_eq (qs n)))

/-- **Local compactness of `pr` over `T_{G₀}`**: about every `coords q₀` there is a ball whose preimage under `pr`
lies in a compact set.  (A compact `C ⊂ ℍ` meets every `Γ`-orbit; `{(Ψ q₀, f_{μ₀}(τ)) : τ ∈ C}` is covered by
finitely many chart boxes; a sequence escaping their union contradicts `s34f_rep_tendsto`.) -/
theorem s34f_local_cover {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (hinj : Function.Injective coords)
    (hopen : IsOpen (range coords)) [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    [ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)]
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)))
    (hpr : ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q →
      (pr v : Fin (3 * g - 3) → ℂ) = coords q) (q₀ : TeichGamma Γ) :
    ∃ ε > 0, ∃ L : Set (BersQuotient Γ), IsCompact L ∧
      ∀ v, (pr v : Fin (3 * g - 3) → ℂ) ∈ ball (coords q₀) ε → v ∈ L := by
  classical
  have : CompactSpace S := hS.1
  obtain ⟨e, hfin, -, -⟩ := s34m_coords hg hS hΓ hp
  obtain ⟨C, hCc, hCorb⟩ := utm_exists_compact_translate hp
  have hmk := s34f_mk_cont hτ
  set μ₀ := Quotient.out q₀ with hμ₀
  have hf₀c : Continuous (normalizedSolution μ₀.1.1) := by
    obtain ⟨h₀, hh₀⟩ := b34_b_homeo μ₀.1
    rw [← hh₀]
    exact h₀.continuous
  have hup : ∀ τ' : UpperHalfPlane, (τ' : ℂ) ∈ upperHalf := fun τ' => τ'.im_pos
  let Φ : UpperHalfPlane → BersFiberSpace Γ := fun τ' =>
    ⟨(bersMapGamma Γ q₀, normalizedSolution μ₀.1.1 τ'), ⟨q₀, rfl⟩, ⟨μ₀, rfl, ⟨τ', hup τ', rfl⟩⟩⟩
  have hΦc : Continuous Φ :=
    (continuous_const.prodMk (hf₀c.comp UpperHalfPlane.continuous_coe)).subtype_mk _
  have hK₀ : IsCompact (Φ '' C) := hCc.image hΦc
  have hchart' := hchart
  choose c hcA N hNo hxN hs hf using hchart'
  have hsrc : ∀ x, ∀ y ∈ N x, Quot.mk (bersFiberRel Γ) y ∈ (c x).source := fun x y hy =>
    (Set.ext_iff.1 (hs x) _).1 ⟨y, hy, rfl⟩
  choose B hBc hBi hBt using fun x =>
    exists_compact_subset (c x).open_target ((c x).map_source (hsrc x x (hxN x)))
  let O : BersFiberSpace Γ → Set (BersFiberSpace Γ) := fun x =>
    N x ∩ (fun y => c x (Quot.mk (bersFiberRel Γ) y)) ⁻¹' interior (B x)
  have hOo : ∀ x, IsOpen (O x) := fun x =>
    ((c x).continuousOn.comp hmk.continuousOn (fun y hy => hsrc x y hy)).isOpen_inter_preimage (hNo x)
      isOpen_interior
  have hxO : ∀ x, x ∈ O x := fun x => ⟨hxN x, hBi x⟩
  have hOL : ∀ x, ∀ y ∈ O x, Quot.mk (bersFiberRel Γ) y ∈ (c x).symm '' B x := by
    intro x y hy
    exact ⟨_, interior_subset hy.2, (c x).left_inv (hsrc x y hy.1)⟩
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover O hOo fun y _ => mem_iUnion.2 ⟨y, hxO y⟩
  let L : Set (BersQuotient Γ) := ⋃ x ∈ t, (c x).symm '' B x
  have hLc : IsCompact L := t.isCompact_biUnion fun x _ =>
    (hBc x).image_of_continuousOn ((c x).continuousOn_symm.mono (hBt x))
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ v : BersQuotient Γ,
      (pr v : Fin (3 * g - 3) → ℂ) ∈ ball (coords q₀) (1 / ((n : ℝ) + 1)) ∧ v ∉ L :=
    fun n => hcon _ Nat.one_div_pos_of_nat L hLc
  choose vs hvU hvL using hseq
  choose xs hxs using fun n => Quot.exists_rep (vs n)
  choose qs hqs using fun n => (xs n).2.1
  have hprq : ∀ n, (pr (vs n) : Fin (3 * g - 3) → ℂ) = coords (qs n) := fun n =>
    hpr (qs n) (vs n) (by rw [← hxs n]; exact (hqs n).symm)
  have hconv : Tendsto (fun n => coords (qs n)) atTop (𝓝 (coords q₀)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h := hvU n
    rw [mem_ball, hprq n] at h
    exact h.le
  have hE := s34f_coord_tendsto hΓ coords hinj hτ hchart e q₀ hconv
  obtain ⟨νs, hνs, hunif⟩ := s34f_rep_tendsto hΓ e hfin q₀ hE
  have hpt : Tendsto (fun n => bersMapGamma Γ (qs n)) atTop (𝓝 (bersMapGamma Γ q₀)) := by
    have h := ((continuous_subtype_val.comp e.symm.continuous).tendsto _).comp hE
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h
  have hz : ∀ n, ∃ τ' : UpperHalfPlane, (xs n).1.2 = normalizedSolution (νs n).1.1 τ' := by
    intro n
    have h2 : (xs n).1.2 ∈ bersDisc Γ (xs n).1.1 := (xs n).2.2
    rw [← hqs n, ← hνs n, (bersDisc_wellDefined (μ := νs n) (ν := νs n) rfl).2] at h2
    obtain ⟨w, hw, hwe⟩ := h2
    exact ⟨⟨w, hw⟩, hwe.symm⟩
  choose τ' hτ' using hz
  choose γs hγs hγC using fun n => hCorb (τ' n)
  have hmemY : ∀ n, (bersMapGamma Γ (qs n),
      normalizedSolution (νs n).1.1 ((γs n • τ' n : UpperHalfPlane) : ℂ)) ∈ BersFiberSpace Γ :=
    fun n => ⟨⟨qs n, rfl⟩, ⟨νs n, hνs n, ⟨_, hup _, rfl⟩⟩⟩
  let ys : ℕ → BersFiberSpace Γ := fun n => ⟨_, hmemY n⟩
  have hvy : ∀ n, vs n = Quot.mk (bersFiberRel Γ) (ys n) := by
    intro n
    rw [← hxs n]
    refine Quot.sound ⟨γs n, hγs n, ?_⟩
    refine Prod.ext (hqs n).symm ?_
    show bersFiberAction Γ (γs n) (xs n).1.1 (xs n).1.2 =
      normalizedSolution (νs n).1.1 ((γs n • τ' n : UpperHalfPlane) : ℂ)
    rw [hτ' n, ← hqs n, ← hνs n, s34m_act_spec hΓ (νs n) (hγs n)]
  obtain ⟨τs, hτsC, φ, hφ, hlim⟩ := hCc.tendsto_subseq hγC
  have hy : Tendsto (fun k => ys (φ k)) atTop (𝓝 (Φ τs)) := by
    refine tendsto_subtype_rng.2 (Tendsto.prodMk_nhds (hpt.comp hφ.tendsto_atTop) ?_)
    have hsub : TendstoUniformlyOn (fun k => normalizedSolution (νs (φ k)).1.1) (normalizedSolution μ₀.1.1) atTop
        ((↑) '' C : Set ℂ) := fun u hu =>
      hφ.tendsto_atTop.eventually (hunif _ (hCc.image UpperHalfPlane.continuous_coe) u hu)
    refine hsub.tendsto_comp hf₀c.continuousWithinAt ?_
    exact tendsto_nhdsWithin_iff.2 ⟨(UpperHalfPlane.continuous_coe.tendsto _).comp hlim,
      Eventually.of_forall fun k => mem_image_of_mem _ (hγC _)⟩
  obtain ⟨x, hxt, hxO⟩ := mem_iUnion₂.1 (ht (mem_image_of_mem Φ hτsC))
  obtain ⟨k, hk⟩ := (hy.eventually ((hOo x).mem_nhds hxO)).exists
  apply hvL (φ k)
  rw [hvy (φ k)]
  exact mem_biUnion hxt (hOL x _ hk)

/-- **Properness of `pr`** (Kodaira–Spencer (ii)): the preimage of a compact subset of the parameter domain
`range coords` is compact in `V(G₀)`. -/
theorem s34f_proper {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (hinj : Function.Injective coords)
    (hopen : IsOpen (range coords)) (τ : TopologicalSpace (BersQuotient Γ))
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    (cs : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ))
    (hM : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ))
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)))
    (hpr : ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q →
      (pr v : Fin (3 * g - 3) → ℂ) = coords q) :
    IsProperMap pr := by
  classical
  -- `hfree` and `hM` are not needed: properness only uses the chart clause (the statement stays true without them).
  have _hfree := hfree
  have _hM := hM
  have hcont := s34f_pr_cont coords hopen hτ hchart pr hpr
  refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩
  have hcov : ∀ t ∈ K, ∃ ε > 0, ∃ L : Set (BersQuotient Γ), IsCompact L ∧
      ∀ v, (pr v : Fin (3 * g - 3) → ℂ) ∈ ball (t : Fin (3 * g - 3) → ℂ) ε → v ∈ L := by
    rintro ⟨_, q₀, rfl⟩ -
    exact s34f_local_cover hg hS hΓ hp coords hinj hopen hτ hchart pr hpr q₀
  choose! ε hε L hLc hL using hcov
  obtain ⟨T, hTK, hKT⟩ := hK.elim_nhds_subcover
    (fun t => Subtype.val ⁻¹' ball (t : Fin (3 * g - 3) → ℂ) (ε t))
    fun t ht => continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (hε t ht))
  refine (T.isCompact_biUnion fun t ht => hLc t (hTK t ht)).of_isClosed_subset
    (hK.isClosed.preimage hcont) fun v hv => ?_
  obtain ⟨t, htT, hvt⟩ := mem_iUnion₂.1 (hKT hv)
  exact mem_biUnion htT (hL t (hTK t htT) v hvt)

end LiZhongQC
