import References.Katok1992.Ch02.S01_GroupPSL2R

/-!
# Katok 1992, Ch. 2 §2.2 Discrete and properly discontinuous groups

S. Katok, *Fuchsian Groups* (1992), Chapter 2 *Fuchsian Groups*, §2.2; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 713–861.

* Definition (Fuchsian group, l. 715; cited throughout) — `IsFuchsian`
* Definition (locally finite family, with the Remark on repetitions, l. 723–725) — `IsLocallyFiniteFamily`
* Definition (G-orbit and stabilizer, l. 727) — exists: `MulAction.orbit` `MulAction.stabilizer` (the orbit as a
  family with multiplicity is the indexed family used in ActsProperlyDiscontinuously)
* Definition (acts properly discontinuously, l. 729) — `ActsProperlyDiscontinuously`
* Unlabelled (l. 731: PD iff orbits discrete and stabilizers finite; used at l. 739, 1657) —
  `actsPD_iff_orbit_stabilizer`
* Theorem 2.2.1 ((2.2.1), l. 733–737; cited at l. 731) — `thm2_2_1`
* Lemma 2.2.2 (l. 743–747; cited at l. 899, 2718) — `lemma2_2_2_i`, `lemma2_2_2_ii`
* Theorem 2.2.3 (l. 755–759; cited at l. 1155, 1655) — `thm2_2_3_i`, `thm2_2_3_ii`
* Example A (the modular group, l. 763–769; cited at l. 1115, 1343, 1661, 2375) — `modularGroup`,
  `exampleA_isFuchsian`
* Lemma 2.2.4 (l. 775–781) — `lemma2_2_4`
* Lemma 2.2.5 (l. 827; cited at l. 845, 1285) — `lemma2_2_5`
* Theorem 2.2.6 (l. 839; cited at l. 845, 849, 1657) — `thm2_2_6`
* Corollary 2.2.7 (l. 843; cited at l. 731, 853, 1303, 1923, 2106, 2220) — `cor2_2_7`
* Corollary 2.2.8 (l. 847) — `cor2_2_8`
* Definition (the limit set Λ(Γ), l. 855; cited in §3.4, §4.5) — `limitSet`
* Unlabelled (l. 853–857: Λ(Γ) ⊆ ℝ ∪ {∞}; cited at l. 1560) — `limitSet_subset_boundary`

Not items (DESIGN §3): "Γ⁺ of index ≤ 2 is Fuchsian" and the lattice remarks (l. 717–719; not cited); the
`PS*L(2,ℤ)` remark (l. 771); "the modular group does not act PD on `ℝ ∪ {∞}`" (l. 851; a remark); Examples B and A
of limit sets (l. 859–861; not cited, re-derived in §4.5); the exercises.

**Conventions.** Katok's `IsFuchsian` is `DiscreteTopology Γ` for `Γ : Subgroup PSL(2, ℝ)` (leader ruling); the
project's `LiZhongQC.IsFuchsian` and `LiZhongQC.limitSet` (subgroups of SL(2,ℂ)/SL(2,ℝ), Li Zhong's conditions)
are different notions and are not reused. Katok's "properly discontinuous" (locally finite orbits) is not Mathlib's
`ProperlyDiscontinuousSMul` (that is Exercise 2.6 (ii), which differs for homeomorphism groups). The standing
setting "X a metric space, G a group of homeomorphisms" is `G : Subgroup (X ≃ₜ X)`.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§2.2; l. 715). A Fuchsian group is a discrete subgroup of PSL(2,ℝ). -/
def IsFuchsian (Γ : Subgroup PSL(2, ℝ)) : Prop := DiscreteTopology Γ

/-- **Definition** (§2.2; l. 723–725). A family `{M_α}` is locally finite if every compact `K` meets only finitely
many `M_α`.
Modelling: an indexed family, so repetitions count (the Remark); not Mathlib's `LocallyFinite`. -/
def IsLocallyFiniteFamily {ι X : Type*} [TopologicalSpace X] (M : ι → Set X) : Prop :=
  ∀ K : Set X, IsCompact K → {a | (M a ∩ K).Nonempty}.Finite

/-- **Definition** (§2.2; l. 729). `G` acts properly discontinuously on `X` if every `G`-orbit (as a family indexed
by `G`) is locally finite. -/
def ActsProperlyDiscontinuously (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] : Prop :=
  ∀ x : X, IsLocallyFiniteFamily fun g : G => ({g • x} : Set X)

/-- Auxiliary (§2.2). A set with an accumulation point is infinite (metric form).
Copied from `GardinerLakic2000.l25g_infinite_of_accPt` (Mathlib-only; GL is not in this file's import closure). -/
theorem k92e_infinite_of_accPt {X : Type*} [MetricSpace X] {S : Set X} {x : X}
    (hacc : AccPt x (𝓟 S)) : S.Infinite := by
  rw [accPt_iff_nhds] at hacc
  by_contra hnf
  have hfin : S.Finite := by
    by_contra h
    exact hnf h
  by_cases hem : (S \ {x}).Nonempty
  · classical
    set F := ((hfin.sdiff (t := {x})).toFinset).image (fun s => dist s x) with hFdef
    have hFne : F.Nonempty := by
      obtain ⟨y, hy⟩ := hem
      exact ⟨dist y x, Finset.mem_image.2 ⟨y, (Set.Finite.mem_toFinset _).2 hy, rfl⟩⟩
    have hpos : 0 < F.min' hFne := by
      have hmem := F.min'_mem hFne
      simp only [hFdef, Finset.mem_image, Set.Finite.mem_toFinset] at hmem
      obtain ⟨y, hy, hye⟩ := hmem
      rw [← hye]
      exact dist_pos.2 (fun h => hy.2 (Set.mem_singleton_iff.2 h))
    obtain ⟨y, hyU, hyx⟩ := hacc (Metric.ball x (F.min' hFne)) (Metric.ball_mem_nhds x hpos)
    have hyS : y ∈ S \ {x} := ⟨hyU.2, fun h => hyx (Set.mem_singleton_iff.1 h)⟩
    have hle : F.min' hFne ≤ dist y x := by
      refine F.min'_le _ ?_
      simp only [hFdef, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨y, hyS, rfl⟩
    exact (lt_irrefl _) (lt_of_lt_of_le (Metric.mem_ball.1 hyU.1) hle)
  · rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hem
    obtain ⟨y, hyU, hyx⟩ := hacc (Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    exact hyx (Set.mem_singleton_iff.1 (hem hyU.2))

/-- Auxiliary (§2.2, l. 731). For any group action on a metric space: properly discontinuous (orbits locally
finite) iff no orbit has an accumulation point and every stabilizer is finite. -/
theorem k92e_pd_iff {G X : Type*} [Group G] [MulAction G X] [MetricSpace X] :
    ActsProperlyDiscontinuously G X ↔
      ∀ x : X, (∀ y : X, ¬ AccPt y (𝓟 (MulAction.orbit G x))) ∧ (MulAction.stabilizer G x : Set G).Finite := by
  constructor
  · intro hpd x
    constructor
    · -- orbit points `uₙ ≠ y`, `uₙ → y`: `{y} ∪ {uₙ}` is compact and meets the orbit in infinitely many points
      intro y hacc
      have hne : (𝓝[≠] y ⊓ 𝓟 (MulAction.orbit G x)).NeBot := hacc
      obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (𝓝[≠] y ⊓ 𝓟 (MulAction.orbit G x))
      have hu1 : Tendsto u atTop (𝓝 y) := hu.mono_right (inf_le_left.trans nhdsWithin_le_nhds)
      have hu2 : ∀ᶠ n in atTop, u n ∈ MulAction.orbit G x := tendsto_principal.1 (hu.mono_right inf_le_right)
      have hu3 : ∀ᶠ n in atTop, u n ∈ ({y} : Set X)ᶜ :=
        (tendsto_nhdsWithin_iff.1 (hu.mono_right inf_le_left)).2
      have hK : IsCompact (insert y (range u)) := hu1.isCompact_insert_range
      have hF : ((fun g : G => g • x) '' {g : G | ({g • x} ∩ insert y (range u)).Nonempty}).Finite :=
        (hpd x _ hK).image _
      have hev : ∀ᶠ n in atTop,
          u n ∈ ((fun g : G => g • x) '' {g : G | ({g • x} ∩ insert y (range u)).Nonempty}) \ {y} := by
        filter_upwards [hu2, hu3] with n h2 h3
        obtain ⟨g, hg⟩ := h2
        have hg' : g • x = u n := hg
        exact ⟨⟨g, ⟨g • x, rfl, by rw [hg']; exact Set.mem_insert_of_mem _ ⟨n, rfl⟩⟩, hg⟩, h3⟩
      have hcl := (hF.subset (Set.sdiff_subset (t := {y}))).isClosed
      exact (hcl.mem_of_tendsto hu1 hev).2 rfl
    · -- `K = {x}`
      refine (hpd x {x} isCompact_singleton).subset fun g hg => ⟨x, ?_, rfl⟩
      exact (MulAction.mem_stabilizer_iff.1 hg).symm
  · intro h x K hK
    obtain ⟨hacc, hstab⟩ := h x
    -- the orbit meets `K` in finitely many points
    have hOK : (MulAction.orbit G x ∩ K).Finite := by
      by_contra hinf
      obtain ⟨y, -, hy⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_right
      exact hacc y (hy.mono (Filter.principal_mono.2 Set.inter_subset_left))
    -- each of them has a coset of the (finite) stabilizer as preimage
    have hfib : ∀ z ∈ MulAction.orbit G x ∩ K, {g : G | g • x = z}.Finite := by
      intro z hz
      obtain ⟨g₀, hg₀⟩ := hz.1
      refine (hstab.image (fun s => g₀ * s)).subset fun g hg => ⟨g₀⁻¹ * g, ?_, by group⟩
      show (g₀⁻¹ * g) • x = x
      have hg' : g • x = z := hg
      have hg₀' : g₀ • x = z := hg₀
      rw [mul_smul, hg', ← hg₀', inv_smul_smul]
    refine Set.Finite.subset (hOK.biUnion hfib) ?_
    rintro g ⟨_, rfl, hgK⟩
    exact Set.mem_biUnion (x := g • x) ⟨⟨g, rfl⟩, hgK⟩ rfl

/-- **Unlabelled** (§2.2; l. 731). `G` acts properly discontinuously iff each orbit is discrete and each stabilizer
is finite.
Modelling: "orbit discrete" read as "no accumulation point in `X`", the reading under which the claim holds. -/
theorem actsPD_iff_orbit_stabilizer {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) :
    ActsProperlyDiscontinuously G X ↔
      ∀ x : X, (∀ y : X, ¬ AccPt y (𝓟 (MulAction.orbit G x))) ∧ (MulAction.stabilizer G x : Set G).Finite := by
  exact k92e_pd_iff

/-- **Theorem 2.2.1** (§2.2; l. 733–737). `G` acts properly discontinuously iff every `x` has a neighbourhood `V`
with `T(V) ∩ V ≠ ∅` for only finitely many `T ∈ G` (2.2.1).
[reading] The book's setting is groups of isometries; the hypothesis `hG` records it (the proof of (⇒) uses it,
and Exercise 2.6 (ii) fails for general homeomorphisms: `(x, y) ↦ (2x, y/2)` on `ℝ² ∖ {0}`). -/
theorem thm2_2_1 {X : Type*} [MetricSpace X] (G : Subgroup (X ≃ₜ X)) (hG : ∀ T ∈ G, Isometry (T : X → X)) :
    ActsProperlyDiscontinuously G X ↔
      ∀ x : X, ∃ V ∈ 𝓝 x, {T : G | ((fun y => T • y) '' V ∩ V).Nonempty}.Finite := by
  constructor
  · -- a ball `B(x, ε)` meets the orbit only at `x`; then `V = B(x, ε/2)` works (isometries)
    intro hpd x
    obtain ⟨hacc, hfin⟩ := k92e_pd_iff.1 hpd x
    have h0 := hacc x
    rw [AccPt, Filter.not_neBot, Filter.inf_principal_eq_bot, Metric.mem_nhdsWithin_iff] at h0
    obtain ⟨ε, hε, hεO⟩ := h0
    refine ⟨Metric.ball x (ε / 2), Metric.ball_mem_nhds x (half_pos hε), hfin.subset ?_⟩
    rintro T ⟨_, ⟨v, hv, rfl⟩, hTv⟩
    show T • x = x
    by_contra hne
    have hiso : Isometry (fun y => T • y) := hG T T.2
    have hd : dist (T • x) x < ε := by
      calc dist (T • x) x ≤ dist (T • x) (T • v) + dist (T • v) x := dist_triangle _ _ _
        _ = dist x v + dist (T • v) x := by rw [hiso.dist_eq]
        _ < ε / 2 + ε / 2 := by
          gcongr
          · rw [dist_comm]; exact hv
          · exact hTv
        _ = ε := add_halves ε
    exact hεO ⟨Metric.mem_ball.2 hd, hne⟩ ⟨T, rfl⟩
  · intro hV
    rw [k92e_pd_iff]
    intro x
    constructor
    · -- infinitely many orbit points near `y` would give infinitely many `T` with `T(V) ∩ V ≠ ∅`
      intro y hy
      obtain ⟨V, hVy, hfin⟩ := hV y
      have hacc : AccPt y (𝓟 (V ∩ MulAction.orbit G x)) := by
        rw [accPt_iff_nhds] at hy ⊢
        intro U hU
        obtain ⟨z, ⟨hzU, hzO⟩, hzy⟩ := hy (U ∩ V) (Filter.inter_mem hU hVy)
        exact ⟨z, ⟨hzU.1, hzU.2, hzO⟩, hzy⟩
      have hinf := k92e_infinite_of_accPt hacc
      obtain ⟨z₀, hz₀V, g₀, rfl⟩ := hinf.nonempty
      apply hinf
      refine (hfin.image fun T : G => T • (g₀ • x)).subset ?_
      rintro z ⟨hzV, g, rfl⟩
      refine ⟨g * g₀⁻¹, ⟨g • x, ⟨g₀ • x, hz₀V, ?_⟩, hzV⟩, ?_⟩
      · show (g * g₀⁻¹) • g₀ • x = g • x
        rw [mul_smul, inv_smul_smul]
      · show (g * g₀⁻¹) • g₀ • x = g • x
        rw [mul_smul, inv_smul_smul]
    · obtain ⟨V, hVx, hfin⟩ := hV x
      refine hfin.subset ?_
      intro T hT
      exact ⟨x, ⟨x, mem_of_mem_nhds hVx, hT⟩, mem_of_mem_nhds hVx⟩

/-- **Lemma 2.2.2 (i)** (§2.2; l. 743). Any non-trivial discrete subgroup of ℝ is infinite cyclic. -/
theorem lemma2_2_2_i (H : AddSubgroup ℝ) [DiscreteTopology H] (h : H ≠ ⊥) :
    ∃ a : ℝ, a ≠ 0 ∧ H = AddSubgroup.zmultiples a := by
  have hc : IsAddCyclic H := AddSubgroup.discrete_iff_addCyclic.2 inferInstance
  obtain ⟨a, ha⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).1 hc
  refine ⟨a, fun h0 => h ?_, ha.symm⟩
  rw [← ha, h0, AddSubgroup.zmultiples_zero_eq_bot]

/-- **Lemma 2.2.2 (ii)** (§2.2; l. 745). Any discrete subgroup of `S¹` is finite cyclic. -/
theorem lemma2_2_2_ii (H : Subgroup Circle) [DiscreteTopology H] : Finite H ∧ IsCyclic H := by
  have hcl : IsClosed (H : Set Circle) := Subgroup.isClosed_of_discreteTopology
  have hfin : (H : Set Circle).Finite := hcl.isCompact.finite (isDiscrete_iff_discreteTopology.2 ‹_›)
  have : Finite H := hfin.to_subtype
  refine ⟨inferInstance, isCyclic_of_injective_ringHom (Circle.coeHom.comp H.subtype) ?_⟩
  intro x y hxy
  exact Subtype.ext (Circle.coe_injective hxy)

/-- Auxiliary (§2.2). A finite set on which `f` is positive has a uniform positive lower bound. -/
theorem k92e_finite_pos {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) (hf : ∀ a ∈ s, 0 < f a) :
    ∃ δ > 0, ∀ a ∈ s, δ ≤ f a := by
  rcases s.eq_empty_or_nonempty with h0 | hne
  · exact ⟨1, one_pos, fun a ha => by rw [h0] at ha; exact absurd ha (Set.notMem_empty a)⟩
  · obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image s f hs hne
    exact ⟨f a₀, hf a₀ ha₀, hmin⟩

/-- Auxiliary (§2.2). `T ↦ T z` is continuous on PSL(2,ℝ) (through the quotient map from SL(2,ℝ)). -/
theorem k92e_smul_cont (z : ℍ) : Continuous fun T : PSL(2, ℝ) => T • z := by
  rw [(QuotientGroup.isQuotientMap_mk (Subgroup.center SL(2, ℝ))).continuous_iff]
  have e : (fun T : PSL(2, ℝ) => T • z) ∘ (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) = fun g => g • z :=
    funext fun g => k92_psl_smul_mk g z
  rw [e]
  exact continuous_id.smul continuous_const

/-- Auxiliary (§2.2). A transformation of PSL(2,ℝ) fixing two distinct points of ℍ is the identity (a non-identity
transformation with a fixed point in ℍ is elliptic, with a unique fixed point there). -/
theorem k92e_eq_one_of_two_fixed {T : PSL(2, ℝ)} {p q : ℍ} (hpq : p ≠ q) (hp : T • p = p) (hq : T • q = q) :
    T = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective T
  by_contra h1
  have hc := k92n_not_center g h1
  have hpos : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp
  have hp' : Matrix.SpecialLinearGroup.mapGL ℝ g • p = p := (k92_psl_smul_mk g p).symm.trans hp
  have hq' : Matrix.SpecialLinearGroup.mapGL ℝ g • q = q := (k92_psl_smul_mk g q).symm.trans hq
  have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hpos hc ⟨p, hp'⟩
  have e1 := (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).1 hp'
  have e2 := (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).1 hq'
  exact hpq (e1.trans e2.symm)

/-- Auxiliary (§2.2). The content of Lemma 2.2.4, needed before it: `{T | T z₀ ∈ K}` is compact (conjugate `z₀`
to `i` and use `k92t_proper`). -/
theorem k92e_compact_preimage (z₀ : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    IsCompact {T : PSL(2, ℝ) | T • z₀ ∈ K} := by
  set h : PSL(2, ℝ) := (z₀.toSL2R : PSL(2, ℝ))
  have hz : h • UpperHalfPlane.I = z₀ := by
    rw [k92_psl_smul_mk, UpperHalfPlane.toSL2R_smul_I]
  have e : {T : PSL(2, ℝ) | T • z₀ ∈ K} =
      (fun S : PSL(2, ℝ) => S * h⁻¹) '' {S : PSL(2, ℝ) | S • UpperHalfPlane.I ∈ K} := by
    ext T
    constructor
    · intro hT
      refine ⟨T * h, ?_, by simp⟩
      show (T * h) • UpperHalfPlane.I ∈ K
      rw [mul_smul, hz]
      exact hT
    · rintro ⟨S, hS, rfl⟩
      show (S * h⁻¹) • z₀ ∈ K
      rw [mul_smul, ← hz, inv_smul_smul]
      exact hS
  rw [e]
  exact (k92t_proper hK).image (continuous_id.mul continuous_const)

/-- Auxiliary (§2.2). A discrete subgroup meets a compact set in finitely many elements (an infinite intersection
would give a convergent sequence of distinct elements, whose consecutive quotients tend to `1`). -/
theorem k92e_finite_of_compact {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {E : Set PSL(2, ℝ)}
    (hE : IsCompact E) : {g : Γ | (g : PSL(2, ℝ)) ∈ E}.Finite := by
  by_contra hinf
  have hSL : FirstCountableTopology SL(2, ℝ) :=
    TopologicalSpace.firstCountableTopology_induced _ (Fin 2 → Fin 2 → ℝ)
      (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ))
  have hPSL : FirstCountableTopology PSL(2, ℝ) := inferInstance
  -- an injective sequence of elements of Γ ∩ E with a convergent subsequence
  set a : ℕ → Γ := fun n => (Set.Infinite.natEmbedding _ hinf n : Γ)
  have ha_inj : Function.Injective a := fun m n h =>
    (Set.Infinite.natEmbedding _ hinf).injective (Subtype.ext h)
  have haE : ∀ n, (a n : PSL(2, ℝ)) ∈ E := fun n => (Set.Infinite.natEmbedding _ hinf n).2
  obtain ⟨S, -, φ, hφ, hlim⟩ := hE.tendsto_subseq haE
  -- consecutive quotients tend to `1`
  have hq : Tendsto (fun n => ((a (φ n))⁻¹ * a (φ (n + 1)) : Γ)) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng]
    have h1 : Tendsto (fun n => (a (φ (n + 1)) : PSL(2, ℝ))) atTop (𝓝 S) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    have := hlim.inv.mul h1
    rw [inv_mul_cancel] at this
    simpa using this
  have hev := (discreteTopology_iff_tendsto_one Γ).1 hΓ (fun n => (((a (φ n))⁻¹ * a (φ (n + 1)) : Γ) : PSL(2, ℝ)))
    (fun n => ((a (φ n))⁻¹ * a (φ (n + 1))).2) (by rwa [tendsto_subtype_rng] at hq)
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : (a (φ n))⁻¹ * a (φ (n + 1)) = 1 := Subtype.ext hn
  have := ha_inj (inv_mul_eq_one.1 h1)
  exact absurd this (hφ (Nat.lt_succ_self n)).ne

/-- Auxiliary (§2.2). A subgroup whose non-identity elements move `w₁` or `w₂` by a uniform amount is discrete. -/
theorem k92e_discrete_of_sep {Γ : Subgroup PSL(2, ℝ)} (w₁ w₂ : ℍ) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ S ∈ Γ, S ≠ 1 → δ ≤ dist (S • w₁) w₁ + dist (S • w₂) w₂) : IsFuchsian Γ := by
  rw [IsFuchsian, discreteTopology_iff_tendsto_one]
  intro T hT hlim
  have hc : ∀ w : ℍ, Tendsto (fun n => dist (T n • w) w) atTop (𝓝 0) := fun w => by
    have h1 := ((k92e_smul_cont w).tendsto 1).comp hlim
    rw [one_smul] at h1
    exact tendsto_iff_dist_tendsto_zero.1 h1
  have hsum := (hc w₁).add (hc w₂)
  rw [add_zero] at hsum
  filter_upwards [hsum (Iio_mem_nhds hδ)] with n hn
  by_contra h1
  exact absurd (h (T n) (hT n) h1) (not_le.2 hn)

/-- Auxiliary (§2.2). A finite subgroup of PSL(2,ℝ) is discrete (each non-identity element moves `i` or `2i`, so a
neighbourhood of `1` avoids it). -/
theorem k92e_discrete_of_finite {Γ : Subgroup PSL(2, ℝ)} (hΓ : (Γ : Set PSL(2, ℝ)).Finite) : IsFuchsian Γ := by
  set s₂ : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ two_pos
  have hne : UpperHalfPlane.I ≠ s₂ := by
    intro h
    have := congrArg UpperHalfPlane.im h
    norm_num [s₂] at this
  obtain ⟨δ, hδ, hδF⟩ := k92e_finite_pos (hΓ.subset (t := {S | S ∈ Γ ∧ S ≠ 1}) fun S hS => hS.1)
    (fun S => dist (S • UpperHalfPlane.I) UpperHalfPlane.I + dist (S • s₂) s₂) fun S hS => by
      by_contra hle
      have h1 := dist_nonneg (x := S • UpperHalfPlane.I) (y := UpperHalfPlane.I)
      have h2 := dist_nonneg (x := S • s₂) (y := s₂)
      have e1 : dist (S • UpperHalfPlane.I) UpperHalfPlane.I = 0 := by linarith
      have e2 : dist (S • s₂) s₂ = 0 := by linarith
      exact hS.2 (k92e_eq_one_of_two_fixed hne (dist_eq_zero.1 e1) (dist_eq_zero.1 e2))
  exact k92e_discrete_of_sep _ _ hδ fun S hS hS1 => hδF S ⟨hS, hS1⟩

/-- Auxiliary (§2.2). The distance by which powers move a point is conjugation invariant:
`ρ(gᵏ(P⁻¹w₀), P⁻¹w₀) = ρ((PgP⁻¹)ᵏ w₀, w₀)`. -/
theorem k92e_conj_dist (g P : SL(2, ℝ)) (w₀ : ℍ) (k : ℤ) :
    dist ((g : PSL(2, ℝ)) ^ k • (P⁻¹ • w₀)) (P⁻¹ • w₀) = dist ((P * g * P⁻¹) ^ k • w₀) w₀ := by
  rw [← QuotientGroup.mk_zpow, k92_psl_smul_mk]
  have e : (P * g * P⁻¹) ^ k = P * g ^ k * P⁻¹ := by
    rw [show P * g * P⁻¹ = MulAut.conj P g from rfl, ← map_zpow]
    rfl
  rw [e, mul_smul, mul_smul, ← dist_smul P (g ^ k • P⁻¹ • w₀) (P⁻¹ • w₀), smul_inv_smul]

/-- Auxiliary (§2.2). If `D` acts on ℍ as `z ↦ αz + β`, then `Dⁿ` acts as `z ↦ αⁿz + β(1 + α + ⋯ + αⁿ⁻¹)`. -/
theorem k92e_pow_affine (D : SL(2, ℝ)) {α β : ℂ}
    (hD : ∀ z : ℍ, ((D • z : ℍ) : ℂ) = α * z + β) (z : ℍ) (k : ℕ) :
    ((D ^ k • z : ℍ) : ℂ) = α ^ k * z + β * ∑ i ∈ Finset.range k, α ^ i := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, ih, hD, Finset.sum_range_succ]
    ring

/-- Auxiliary (§2.2). Parabolic normal form: if `(a + d)² = 4` and `±g ≠ Id`, some conjugate `PgP⁻¹` acts as a
translation `z ↦ z + b`, `b ≠ 0` (`P(z) = −1/(z − x)` at the double fixed point `x`, or `P = 1` when `c = 0`).
Adapted from `GardinerLakic2000.para2_8_normal_form_par` (GL is not in this file's import closure). -/
theorem k92e_par_normal (g : SL(2, ℝ)) (ht4 : (g 0 0 + g 1 1) ^ 2 = 4) (hne : (g : PSL(2, ℝ)) ≠ 1) :
    ∃ P : SL(2, ℝ), ∃ b : ℝ, b ≠ 0 ∧ ∀ z : ℍ, (((P * g * P⁻¹) • z : ℍ) : ℂ) = z + b := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  set ε := (g 0 0 + g 1 1) / 2 with hεdef
  have hε : ε ^ 2 = 1 := by
    rw [hεdef]
    linear_combination ht4 / 4
  have hε0 : ε ≠ 0 := by
    rintro h0
    rw [h0] at hε
    norm_num at hε
  have hεC : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  have hεC0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε0
  rcases eq_or_ne (g 1 0) 0 with hc | hc
  · -- `c = 0`: `a = d = ε` and `b ≠ 0` (else `g = ±1`), so `g` itself is `z ↦ z + b/ε`
    have had : g 0 0 = g 1 1 := by
      have : (g 0 0 - g 1 1) ^ 2 = 0 := by
        rw [hc, mul_zero, sub_zero] at hdet
        linear_combination ht4 - 4 * hdet
      linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this]
    have haε : g 0 0 = ε := by rw [hεdef, ← had]; ring
    have hb : g 0 1 ≠ 0 := by
      intro hb
      apply hne
      rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨ε, by simpa using hε, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, haε]
    refine ⟨1, g 0 1 / ε, div_ne_zero hb hε0, fun z => ?_⟩
    rw [one_mul, inv_one, mul_one, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [hc, ← had, haε]
    push_cast
    rw [zero_mul, zero_add, add_div, mul_div_cancel_left₀ _ hεC0]
  · -- `c ≠ 0`: `P(z) = −1/(z − x)` moves the double fixed point `x = (a − d)/(2c)` to `∞`
    set x := (g 0 0 - g 1 1) / (2 * g 1 0) with hxdef
    have hx : 2 * g 1 0 * x = g 0 0 - g 1 1 := by
      rw [hxdef]
      field_simp
    clear_value x
    set P : SL(2, ℝ) := ⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩
    have hPg : ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![ε, -g 1 0; 0, ε] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.vecMul, dotProduct]
      · linear_combination (1 / 2 : ℝ) * hx - hεdef
      · apply mul_left_cancel₀ (mul_ne_zero (four_ne_zero (α := ℝ)) hc)
        linear_combination (2 * g 1 0 * x - (g 0 0 - g 1 1)) * hx - ht4 + 4 * hdet
      · linear_combination (-1 / 2 : ℝ) * hx - hεdef
    refine ⟨P, -(g 1 0 * ε), neg_ne_zero.2 (mul_ne_zero hc hε0), fun z => ?_⟩
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hPg, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [zero_mul, zero_add, div_eq_iff hεC0]
    linear_combination (g 1 0 : ℂ) * hεC

/-- Auxiliary (§2.2, Exercise 2.7). The non-trivial powers of a hyperbolic or parabolic `T` move some point by a
uniform amount: `T` is conjugate to `z ↦ λ²z`, `|λ| ≠ 1` (§2.1), or to `z ↦ z + b`, `b ≠ 0`. -/
theorem k92e_pow_sep {T : PSL(2, ℝ)} (hT : IsHyperbolic T ∨ IsParabolic T) :
    ∃ w : ℍ, ∃ δ > 0, ∀ k : ℤ, k ≠ 0 → δ ≤ dist (T ^ k • w) w := by
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set g := Quotient.out T
  -- a conjugate `D = P g P⁻¹` moves `i` by at least `δ` under all positive powers
  obtain ⟨P, δ, hδ, hD⟩ : ∃ P : SL(2, ℝ), ∃ δ > 0, ∀ n : ℕ, 1 ≤ n →
      δ ≤ dist ((P * g * P⁻¹) ^ (n : ℤ) • UpperHalfPlane.I) UpperHalfPlane.I := by
    rcases hT with hT | hT
    · -- hyperbolic: `D` acts as `z ↦ l² z`, `l² ≠ 1`, so `ρ(Dⁿ i, i) = n |log l²|`
      have h2 : 2 < |g 0 0 + g 1 1| := hTr ▸ hT
      have hhyp : (g : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
        show 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).discr
        rw [k92n_discr]
        nlinarith [abs_nonneg (g 0 0 + g 1 1), sq_abs (g 0 0 + g 1 1)]
      obtain ⟨l, hl1, hl2, P, hP⟩ := (hyperbolic_conj_diag g).1 hhyp
      have hd := (P * g * P⁻¹ : SL(2, ℝ)).2
      rw [hP, Matrix.det_fin_two_of] at hd
      have hl0 : l ≠ 0 := by
        rintro rfl
        simp at hd
      have hs : 0 < l ^ 2 := by positivity
      have hs1 : l ^ 2 ≠ 1 := by
        intro h
        have : (l - 1) * (l + 1) = 0 := by linear_combination h
        rcases mul_eq_zero.1 this with h0 | h0
        · exact hl1 (by linarith)
        · exact hl2 (by linarith)
      have hact : ∀ z : ℍ, (((P * g * P⁻¹) • z : ℍ) : ℂ) = ((l ^ 2 : ℝ) : ℂ) * z + 0 := fun z => by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, hP, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        have : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl0
        push_cast
        field_simp
        ring
      refine ⟨P, |Real.log (l ^ 2)|, abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hs hs1), fun n hn => ?_⟩
      rw [zpow_natCast]
      have hpow := k92e_pow_affine _ hact UpperHalfPlane.I n
      rw [zero_mul, add_zero, UpperHalfPlane.coe_I, ← Complex.ofReal_pow] at hpow
      have hre : ((P * g * P⁻¹) ^ n • UpperHalfPlane.I).re = UpperHalfPlane.I.re := by
        rw [← UpperHalfPlane.coe_re, hpow, ← UpperHalfPlane.coe_re, UpperHalfPlane.coe_I]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have him : ((P * g * P⁻¹) ^ n • UpperHalfPlane.I).im = (l ^ 2) ^ n := by
        rw [← UpperHalfPlane.coe_im, hpow]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have hlog : Real.log ((l ^ 2) ^ n) = n * Real.log (l ^ 2) := Real.log_pow _ _
      rw [UpperHalfPlane.dist_of_re_eq hre, him, UpperHalfPlane.I_im, Real.log_one, Real.dist_eq, sub_zero,
        hlog, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
      exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast hn)
    · -- parabolic: `D` acts as `z ↦ z + b`, `b ≠ 0`, so `ρ(Dⁿ i, i) = 2 arsinh(n|b|/2)`
      have h2 : |g 0 0 + g 1 1| = 2 := hTr ▸ hT.1
      have ht4 : (g 0 0 + g 1 1) ^ 2 = 4 := by
        rw [← sq_abs, h2]
        norm_num
      obtain ⟨P, b, hb, hact⟩ := k92e_par_normal g ht4 (by rw [hgT]; exact hT.2)
      have hact' : ∀ z : ℍ, (((P * g * P⁻¹) • z : ℍ) : ℂ) = 1 * z + b := fun z => by rw [hact, one_mul]
      refine ⟨P, 2 * Real.arsinh (|b| / 2),
        mul_pos two_pos (Real.arsinh_pos_iff.2 (div_pos (abs_pos.2 hb) two_pos)), fun n hn => ?_⟩
      rw [zpow_natCast]
      have hpow := k92e_pow_affine _ hact' UpperHalfPlane.I n
      simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hpow
      have him : ((P * g * P⁻¹) ^ n • UpperHalfPlane.I).im = 1 := by
        rw [← UpperHalfPlane.coe_im, hpow, UpperHalfPlane.coe_I]
        simp
      rw [UpperHalfPlane.dist_eq, him, UpperHalfPlane.I_im, mul_one, Real.sqrt_one, mul_one, hpow,
        UpperHalfPlane.coe_I, Complex.dist_eq, add_sub_cancel_left]
      gcongr
      rw [show (b : ℂ) * (n : ℂ) = ((b * n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
      exact le_mul_of_one_le_right (abs_nonneg _) (by exact_mod_cast hn)
  refine ⟨P⁻¹ • UpperHalfPlane.I, δ, hδ, fun k hk => ?_⟩
  have hdist : ∀ m : ℤ, dist (T ^ m • (P⁻¹ • UpperHalfPlane.I)) (P⁻¹ • UpperHalfPlane.I) =
      dist ((P * g * P⁻¹) ^ m • UpperHalfPlane.I) UpperHalfPlane.I := fun m => by
    rw [← hgT]
    exact k92e_conj_dist g P UpperHalfPlane.I m
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · -- negative powers: `ρ(T^k w, w) = ρ(w, T^{-k} w)`
    have hiso : dist (T ^ k • (P⁻¹ • UpperHalfPlane.I)) (P⁻¹ • UpperHalfPlane.I) =
        dist (T ^ (-k) • (P⁻¹ • UpperHalfPlane.I)) (P⁻¹ • UpperHalfPlane.I) := by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (T ^ (-k))
      have e : T ^ k = ((h : PSL(2, ℝ)))⁻¹ := by rw [hh, zpow_neg, inv_inv]
      rw [e, ← hh, ← QuotientGroup.mk_inv, k92_psl_smul_mk, k92_psl_smul_mk, dist_comm,
        ← dist_smul h, smul_inv_smul]
    rw [hiso, hdist, show -k = (((-k).toNat : ℕ) : ℤ) by omega]
    exact hD _ (by omega)
  · rw [hdist, show k = ((k.toNat : ℕ) : ℤ) by omega]
    exact hD _ (by omega)

/-- Auxiliary (§2.2). Every neighbourhood of a point of ℍ contains another point. -/
theorem k92e_exists_ne_mem {p : ℍ} {W : Set ℍ} (hW : W ∈ 𝓝 p) : ∃ q ∈ W, q ≠ p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  set q : ℍ := UpperHalfPlane.mk ⟨p.re, p.im * Real.exp (ε / 2)⟩ (mul_pos p.im_pos (Real.exp_pos _))
  have hd : dist q p = ε / 2 := by
    rw [UpperHalfPlane.dist_of_re_eq (by rfl)]
    show dist (Real.log (p.im * Real.exp (ε / 2))) (Real.log p.im) = ε / 2
    rw [Real.log_mul p.im_pos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (half_pos hε)]
  refine ⟨q, hball (Metric.mem_ball.2 (by rw [hd]; linarith)), fun h => ?_⟩
  rw [h, dist_self] at hd
  linarith

/-- **Theorem 2.2.3 (i)** (§2.2; l. 757). Hyperbolic and parabolic cyclic subgroups of PSL(2,ℝ) are Fuchsian. -/
theorem thm2_2_3_i {T : PSL(2, ℝ)} (hT : IsHyperbolic T ∨ IsParabolic T) : IsFuchsian (Subgroup.zpowers T) := by
  obtain ⟨w, δ, hδ, hsep⟩ := k92e_pow_sep hT
  refine k92e_discrete_of_sep w w hδ fun S hS hS1 => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hS
  have hk : k ≠ 0 := by
    rintro rfl
    exact hS1 (zpow_zero T)
  have h1 := hsep k hk
  have h2 := dist_nonneg (x := T ^ k • w) (y := w)
  linarith

/-- **Theorem 2.2.3 (ii)** (§2.2; l. 759; cited at l. 1655 as "Theorem 2.3.7" [misprint]). An elliptic cyclic
subgroup of PSL(2,ℝ) is Fuchsian iff it is finite. -/
theorem thm2_2_3_ii {T : PSL(2, ℝ)} (hT : IsElliptic T) :
    IsFuchsian (Subgroup.zpowers T) ↔ Finite (Subgroup.zpowers T) := by
  constructor
  · -- the powers of `T` fix its fixed point `p ∈ ℍ`, so they lie in the compact stabilizer of `p`
    intro hF
    obtain ⟨p, hp⟩ := fixedBy_of_isElliptic hT
    have hTp : T ∈ MulAction.stabilizer PSL(2, ℝ) p := by
      have hmem : (Sum.inl p : Hbar) ∈ MulAction.fixedBy Hbar T := by
        rw [hp]
        exact Set.mem_singleton _
      exact Sum.inl.inj hmem
    have hfin := k92e_finite_of_compact hF (k92e_compact_preimage p (isCompact_singleton (x := p)))
    have hall : {g : Subgroup.zpowers T | (g : PSL(2, ℝ)) ∈ {S : PSL(2, ℝ) | S • p ∈ ({p} : Set ℍ)}} =
        Set.univ := by
      ext ⟨S, hS⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hS
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact (MulAction.stabilizer PSL(2, ℝ) p).zpow_mem hTp k
    rw [hall] at hfin
    exact Set.finite_univ_iff.1 hfin
  · intro hfin
    exact k92e_discrete_of_finite (Set.toFinite _)

/-- **Example A** (§2.2; l. 763). The modular group `PSL(2,ℤ)`: the transformations `(az + b)/(cz + d)` with
`a, b, c, d ∈ ℤ`, `ad − bc = 1`, as a subgroup of PSL(2,ℝ). -/
def modularGroup : Subgroup PSL(2, ℝ) :=
  ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))).range

/-- Auxiliary (§2.2, Example A). An element of PSL(2,ℤ) represented by some `u ∈ SL(2,ℝ)` with
`|u_ij − δ_ij| < 1/2` is the identity: its integer lift is `±u`, hence `±1`. -/
theorem k92e_mod_aux (γ : SL(2, ℤ)) (u : SL(2, ℝ))
    (hu : u ∈ {g : SL(2, ℝ) | ∀ i j, |g i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < 1 / 2})
    (h : (u : PSL(2, ℝ)) = ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))) γ) :
    ((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))) γ = 1 := by
  set γ' := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ with hγ'def
  have h' : (u : PSL(2, ℝ)) = (γ' : PSL(2, ℝ)) := h
  rw [QuotientGroup.eq] at h'
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h'
  have hr2 : r ^ 2 = 1 := by simpa using hr
  -- `γ' = r u` entrywise
  have hentry : ∀ i j, γ' i j = r * u i j := by
    have e : γ' = u * (u⁻¹ * γ') := by group
    intro i j
    rw [e, Matrix.SpecialLinearGroup.coe_mul, ← hrz]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hint : ∀ i j, γ' i j = ((γ i j : ℤ) : ℝ) := fun i j => by simp [γ']
  have close : ∀ n m : ℤ, |(n : ℝ) - m| < 1 → n = m := fun n m hnm => by
    have : |n - m| < 1 := by exact_mod_cast hnm
    rw [Int.abs_lt_one_iff, sub_eq_zero] at this
    exact this
  have hu' : ∀ i j, |u i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < 1 / 2 := hu
  have hr1 : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linarith
    · right; linarith
  -- the integer entries are within `1/2` of the integers `r δ_ij`
  have hscal : ∀ i j, γ' i j = r * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    have hb : |γ' i j - r * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < 1 := by
      rw [hentry, ← mul_sub, abs_mul]
      rcases hr1 with rfl | rfl <;> simp only [abs_one, abs_neg, one_mul] <;> linarith [hu' i j]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, r * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = (m : ℝ) := by
      rcases hr1 with rfl | rfl
      · refine ⟨(1 : Matrix (Fin 2) (Fin 2) ℤ) i j, ?_⟩
        rw [one_mul, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      · refine ⟨-(1 : Matrix (Fin 2) (Fin 2) ℤ) i j, ?_⟩
        rw [Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
    rw [hm, hint] at hb ⊢
    exact_mod_cast close _ _ hb
  show (γ' : PSL(2, ℝ)) = 1
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, hr, ?_⟩
  ext i j
  rw [hscal]
  fin_cases i <;> fin_cases j <;> simp

/-- **Example A** (§2.2; l. 769). The modular group is Fuchsian.
Modelling: Mathlib's `discreteSpecialLinearGroupIntRange` is the SL(2,ℝ)/GL version, a different object. -/
theorem exampleA_isFuchsian : IsFuchsian modularGroup := by
  rw [IsFuchsian, discreteTopology_iff_tendsto_one]
  intro T hT hlim
  -- `U = {g : |g_ij − δ_ij| < 1/2}` maps onto a neighbourhood of `1` (the quotient map is open)
  set U : Set SL(2, ℝ) := {g | ∀ i j, |g i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < 1 / 2} with hUdef
  have hUo : IsOpen U := by
    have c : ∀ i j : Fin 2, Continuous fun g : SL(2, ℝ) => g i j := fun i j =>
      (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply id continuous_id i)
    simp only [hUdef, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (((c i j).sub continuous_const).abs) continuous_const
  have h1U : (1 : SL(2, ℝ)) ∈ U := fun i j => by simp
  have hnhds : ((QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) '' U) ∈ 𝓝 (1 : PSL(2, ℝ)) :=
    (QuotientGroup.isOpenMap_coe (N := Subgroup.center SL(2, ℝ)) U hUo).mem_nhds ⟨1, h1U, rfl⟩
  filter_upwards [hlim hnhds] with n hn
  obtain ⟨u, huU, hu⟩ := hn
  obtain ⟨γ, hγ⟩ := hT n
  rw [← hγ] at hu ⊢
  exact k92e_mod_aux γ u huU hu

/-- **Lemma 2.2.4** (§2.2; l. 775). For `z₀ ∈ ℍ` and compact `K ⊆ ℍ`, `{T ∈ PSL(2,ℝ) | T(z₀) ∈ K}` is compact.
[misprint] The book writes `w₀` for `z₀`. -/
theorem lemma2_2_4 (z₀ : ℍ) {K : Set ℍ} (hK : IsCompact K) : IsCompact {T : PSL(2, ℝ) | T • z₀ ∈ K} := by
  exact k92e_compact_preimage z₀ hK

/-- **Lemma 2.2.5** (§2.2; l. 827). If Γ acts properly discontinuously on ℍ and `p` is fixed by some `T ∈ Γ`,
`T ≠ Id`, then some neighbourhood `W` of `p` contains no other point fixed by a non-identity element of Γ. -/
theorem lemma2_2_5 (Γ : Subgroup PSL(2, ℝ)) (h : ActsProperlyDiscontinuously Γ ℍ) (p : ℍ)
    (hp : ∃ T ∈ Γ, T ≠ 1 ∧ T • p = p) :
    ∃ W ∈ 𝓝 p, ∀ q ∈ W, q ≠ p → ∀ T ∈ Γ, T • q = q → T = 1 := by
  -- `hp` is not needed: the conclusion holds at every point
  have _ := hp
  -- the finitely many `g ∈ Γ` with `0 < ρ(g p, p) ≤ 1` move `p` by at least some `δ > 0`
  have hF := h p (Metric.closedBall p 1) (isCompact_closedBall p 1)
  obtain ⟨δ, hδ, hδF⟩ := k92e_finite_pos
    (hF.subset (t := {g : Γ | ({g • p} ∩ Metric.closedBall p 1).Nonempty ∧ g • p ≠ p}) fun g hg => hg.1)
    (fun g : Γ => dist (g • p) p) fun g hg => dist_pos.2 hg.2
  refine ⟨Metric.ball p (min δ 1 / 2), Metric.ball_mem_nhds p (by positivity), fun q hq hqp T hT hTq => ?_⟩
  have hd : dist (T • p) p < min δ 1 := by
    have hiso : dist (T • p) (T • q) = dist p q := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective T
      rw [k92_psl_smul_mk, k92_psl_smul_mk, dist_smul]
    have hq' : dist q p < min δ 1 / 2 := Metric.mem_ball.1 hq
    calc dist (T • p) p ≤ dist (T • p) (T • q) + dist (T • q) p := dist_triangle _ _ _
      _ = dist q p + dist q p := by rw [hiso, hTq, dist_comm]
      _ < min δ 1 := by linarith
  by_cases hTp : T • p = p
  · exact k92e_eq_one_of_two_fixed hqp hTq hTp
  · exfalso
    have hmem : (⟨T, hT⟩ : Γ) ∈ {g : Γ | ({g • p} ∩ Metric.closedBall p 1).Nonempty ∧ g • p ≠ p} :=
      ⟨⟨T • p, rfl, Metric.mem_closedBall.2 (le_of_lt (lt_of_lt_of_le hd (min_le_right _ _)))⟩, hTp⟩
    have h1 := hδF _ hmem
    rw [Subgroup.mk_smul] at h1
    have h2 := lt_of_lt_of_le hd (min_le_left _ _)
    linarith

/-- **Theorem 2.2.6** (§2.2; l. 839). Γ ≤ PSL(2,ℝ) is Fuchsian iff it acts properly discontinuously on ℍ. -/
theorem thm2_2_6 (Γ : Subgroup PSL(2, ℝ)) : IsFuchsian Γ ↔ ActsProperlyDiscontinuously Γ ℍ := by
  constructor
  · -- `{T ∈ Γ | T z ∈ K}` = Γ ∩ (compact set of Lemma 2.2.4), finite
    intro hΓ x K hK
    refine (k92e_finite_of_compact hΓ (k92e_compact_preimage x hK)).subset ?_
    rintro g ⟨y, hy, hyK⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy] at hyK
    exact hyK
  · -- a point `s` fixed by no non-identity element (Lemma 2.2.5) is moved uniformly by `Γ ∖ {1}`
    intro hpd
    obtain ⟨s, hs⟩ : ∃ s : ℍ, ∀ T ∈ Γ, T • s = s → T = 1 := by
      by_cases hI : ∃ T ∈ Γ, T ≠ 1 ∧ T • UpperHalfPlane.I = UpperHalfPlane.I
      · obtain ⟨W, hW, hWfix⟩ := lemma2_2_5 Γ hpd _ hI
        obtain ⟨q, hqW, hqI⟩ := k92e_exists_ne_mem hW
        exact ⟨q, fun T hT hTq => hWfix q hqW hqI T hT hTq⟩
      · refine ⟨UpperHalfPlane.I, fun T hT hTI => ?_⟩
        by_contra h1
        exact hI ⟨T, hT, h1, hTI⟩
    have hF := hpd s (Metric.closedBall s 1) (isCompact_closedBall s 1)
    obtain ⟨δ, hδ, hδF⟩ := k92e_finite_pos
      (hF.subset (t := {g : Γ | ({g • s} ∩ Metric.closedBall s 1).Nonempty ∧ g ≠ 1}) fun g hg => hg.1)
      (fun g : Γ => dist (g • s) s) fun g hg => dist_pos.2 fun he =>
        hg.2 (Subtype.ext (hs g g.2 he))
    refine k92e_discrete_of_sep s s (lt_min hδ one_pos) fun S hS hS1 => ?_
    have hpos := dist_nonneg (x := S • s) (y := s)
    by_cases hin : dist (S • s) s ≤ 1
    · have h1 := hδF ⟨S, hS⟩ ⟨⟨S • s, rfl, Metric.mem_closedBall.2 hin⟩, fun h => hS1 (congrArg Subtype.val h)⟩
      rw [Subgroup.mk_smul] at h1
      have h2 := min_le_left δ 1
      linarith
    · have := min_le_right δ 1
      linarith

/-- **Corollary 2.2.7** (§2.2; l. 843). Γ acts properly discontinuously on ℍ iff every orbit `Γz` is a discrete
subset of ℍ.
Modelling: "discrete subset" in the induced-topology sense of l. 709 (D-4). -/
theorem cor2_2_7 (Γ : Subgroup PSL(2, ℝ)) :
    ActsProperlyDiscontinuously Γ ℍ ↔ ∀ z : ℍ, DiscreteTopology (MulAction.orbit Γ z) := by
  constructor
  · -- a properly discontinuous orbit has no accumulation point, in particular none of its own points
    intro hpd z
    rw [discreteTopology_subtype_iff]
    intro y _
    have := (k92e_pd_iff.1 hpd z).1 y
    rwa [AccPt, Filter.not_neBot] at this
  · -- discrete orbits: if `Tₙ → 1` in Γ, then eventually `Tₙ` fixes `i` and `2i`, so `Tₙ = 1`
    intro hdisc
    refine (thm2_2_6 Γ).1 ?_
    rw [IsFuchsian, discreteTopology_iff_tendsto_one]
    intro T hT hlim
    have hfix : ∀ s : ℍ, ∀ᶠ n in atTop, T n • s = s := by
      intro s
      have hd := discreteTopology_subtype_iff.1 (hdisc s) s ⟨1, one_smul _ _⟩
      rw [Filter.inf_principal_eq_bot, mem_nhdsWithin] at hd
      obtain ⟨U, hUo, hsU, hU⟩ := hd
      have hconv : Tendsto (fun n => T n • s) atTop (𝓝 s) := by
        have := ((k92e_smul_cont s).tendsto 1).comp hlim
        rwa [Function.comp_def, one_smul] at this
      filter_upwards [hconv (hUo.mem_nhds hsU)] with n hn
      by_contra hne
      exact hU ⟨hn, hne⟩ ⟨⟨T n, hT n⟩, rfl⟩
    set s₂ : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ two_pos
    have hne : UpperHalfPlane.I ≠ s₂ := by
      intro h
      have := congrArg UpperHalfPlane.im h
      norm_num [s₂] at this
    filter_upwards [hfix UpperHalfPlane.I, hfix s₂] with n h1 h2
    exact k92e_eq_one_of_two_fixed hne h1 h2

/-- **Corollary 2.2.8** (§2.2; l. 847). The fixed points of elliptic elements of a Fuchsian group do not
accumulate in ℍ. -/
theorem cor2_2_8 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (w : ℍ) :
    ¬ AccPt w (𝓟 {z : ℍ | ∃ T ∈ Γ, IsElliptic T ∧ T • z = z}) := by
  intro hacc
  -- an elliptic `T` fixing `z ∈ B(w, 1)` moves `w` by less than `2`; there are finitely many such `T ∈ Γ`,
  -- each with a single fixed point in ℍ
  set S := {z : ℍ | ∃ T ∈ Γ, IsElliptic T ∧ T • z = z}
  have hfin := k92e_finite_of_compact hΓ (k92e_compact_preimage w (isCompact_closedBall w 2))
  have hsub : S ∩ Metric.ball w 1 ⊆ ⋃ g ∈ {g : Γ | (g : PSL(2, ℝ)) ∈ {T : PSL(2, ℝ) | T • w ∈ Metric.closedBall w 2}},
      {z : ℍ | IsElliptic (g : PSL(2, ℝ)) ∧ (g : PSL(2, ℝ)) • z = z} := by
    rintro z ⟨⟨T, hT, hTe, hTz⟩, hzw⟩
    refine Set.mem_biUnion (x := ⟨T, hT⟩) ?_ ⟨hTe, hTz⟩
    show T • w ∈ Metric.closedBall w 2
    have hiso : dist (T • w) (T • z) = dist w z := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective T
      rw [k92_psl_smul_mk, k92_psl_smul_mk, dist_smul]
    have hz : dist z w < 1 := Metric.mem_ball.1 hzw
    rw [Metric.mem_closedBall]
    calc dist (T • w) w ≤ dist (T • w) (T • z) + dist (T • z) w := dist_triangle _ _ _
      _ = dist z w + dist z w := by rw [hiso, hTz, dist_comm]
      _ ≤ 2 := by linarith
  have hfin2 : (S ∩ Metric.ball w 1).Finite := by
    refine Set.Finite.subset (hfin.biUnion fun g _ => ?_) hsub
    -- an elliptic transformation has a single fixed point in ℍ
    refine Set.Subsingleton.finite fun z₁ hz₁ z₂ hz₂ => ?_
    obtain ⟨p, hp⟩ := fixedBy_of_isElliptic hz₁.1
    have e : ∀ z : ℍ, (g : PSL(2, ℝ)) • z = z → z = p := fun z hz => by
      have hmem : (Sum.inl z : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) := by
        show (g : PSL(2, ℝ)) • (Sum.inl z : Hbar) = Sum.inl z
        exact congrArg Sum.inl hz
      rw [hp] at hmem
      exact Sum.inl.inj hmem
    rw [e z₁ hz₁.2, e z₂ hz₂.2]
  have hacc' : AccPt w (𝓟 (S ∩ Metric.ball w 1)) := by
    rw [accPt_iff_nhds] at hacc ⊢
    intro U hU
    obtain ⟨z, ⟨hzU, hzS⟩, hzw⟩ := hacc (U ∩ Metric.ball w 1) (Filter.inter_mem hU (Metric.ball_mem_nhds w one_pos))
    exact ⟨z, ⟨hzU.1, hzS, hzU.2⟩, hzw⟩
  exact (k92e_infinite_of_accPt hacc') hfin2

/-- **Definition** (§2.2; l. 855). The limit set Λ(Γ): all limit points in `ℂ ∪ {∞}` of orbits `Γz`, `z ∈ ℍ`.
Modelling: limits of `T_n(z)` along sequences of distinct `T_n ∈ Γ` (l. 853). -/
def limitSet (Γ : Subgroup PSL(2, ℝ)) : Set ExtPlane :=
  {α | ∃ z : ℍ, ∃ T : ℕ → Γ, Function.Injective T ∧ Tendsto (fun n => toExtH (T n • z)) atTop (𝓝 α)}

/-- **Unlabelled** (§2.2; l. 853–857; cited at l. 1560). For Fuchsian Γ, `Λ(Γ) ⊆ ℝ ∪ {∞}`. -/
theorem limitSet_subset_boundary {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    limitSet Γ ⊆ pointsAtInfinity := by
  rintro α ⟨z, T, hTinj, hTlim⟩
  induction α using OnePoint.rec with
  | infty => exact Set.mem_insert _ _
  | coe w =>
    -- the orbit points lie in ℍ, so `Im w ≥ 0`; `Im w > 0` would contradict proper discontinuity
    have hconv : Tendsto (fun n => ((T n • z : ℍ) : ℂ)) atTop (𝓝 w) :=
      (OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff).2 hTlim
    have him : 0 ≤ w.im :=
      ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hconv)
        (Filter.Eventually.of_forall fun n => (T n • z).im_pos.le)
    rcases him.eq_or_lt with h0 | hpos
    · refine Set.mem_insert_of_mem _ ⟨w.re, ?_⟩
      show (((w.re : ℝ) : ℂ) : ExtPlane) = (w : ExtPlane)
      congr 1
      exact Complex.ext rfl (by simp [h0])
    · exfalso
      set w' : ℍ := ⟨w, hpos⟩
      have hconv' : Tendsto (fun n => T n • z) atTop (𝓝 w') :=
        UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.2 hconv
      have hF := (thm2_2_6 Γ).1 hΓ z (Metric.closedBall w' 1) (isCompact_closedBall w' 1)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
        (hconv' (Metric.closedBall_mem_nhds w' one_pos))
      refine Set.infinite_of_injective_forall_mem (s := {g : Γ | ({g • z} ∩ Metric.closedBall w' 1).Nonempty})
        (f := fun n : ℕ => T (n + N)) (fun a b hab => ?_) (fun n => ⟨T (n + N) • z, rfl, hN _ (by omega)⟩) hF
      exact Nat.add_right_cancel (hTinj hab)

end Katok1992
