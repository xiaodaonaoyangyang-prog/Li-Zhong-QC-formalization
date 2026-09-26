/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionK_Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Section L: Arc Topology
## HOL Light: Section L (Lines 21112–24219)

Simple arc compactness, arc restrictions, reparameterization, polar
coordinates, and the `cut_arc` operation for splitting an arc at an
interior point.  Also the crucial `graph_disk` separation lemma.

### Key HOL Light results
- Simple arcs are compact, nonempty subsets of ℝ²
- `cis` and `norm2`: polar coordinate tools
- `simple_arc_end_trans`: joining two arcs
- `simple_arc_end_cut`: cutting an arc at an interior point
- `simple_arc_end_restriction`: extracting a subarc
- `simple_arc_end_inj`: uniqueness of arcs with given endpoints
- `simple_closed_cut`: cutting a closed curve into two arcs
- `graph_disk`: separation lemma for planar graphs
-/

open Set Topology Metric Real

noncomputable section

/-! ## Definitions: norm2 and cis -/

/-- Norm in E2 as distance to origin.
    HOL Light: `norm2` (line 21565). -/
def norm2 (x : E2') : ℝ := ‖x‖

/-- Point on the unit circle at angle `x`.
    HOL Light: `cis` (line 21566). -/
def cis (x : ℝ) : E2' := point (cos x, sin x)

/-! ## Norm / polar coordinate lemmas -/

/-- norm2(cis x) = 1.
    HOL Light: `norm2_cis` (line 21568). -/
theorem norm2_cis (x : ℝ) : norm2 (cis x) = 1 := by
  simp only [norm2, cis]
  rw [EuclideanSpace.norm_eq]
  norm_num [Fin.sum_univ_two, point, sq_abs, sin_sq_add_cos_sq]

/-- norm2(x) = 0 ↔ x = 0.
    HOL Light: `norm2_0` (line 21593). -/
theorem norm2_zero_iff {x : E2'} : norm2 x = 0 ↔ x = 0 := by
  simp [norm2, norm_eq_zero]

/-- norm2(r • cis x) = |r|.
    HOL Light: `norm2_scale_cis` (line 21674). -/
theorem norm2_scale_cis (r : ℝ) (x : ℝ) :
    norm2 (r • cis x) = |r| := by
  unfold norm2 cis
  simp [norm_smul, EuclideanSpace.norm_eq,
    Fin.sum_univ_two, point, sq_abs]

/-- Polar representation is injective on [0,2π) × [0,∞).
    HOL Light: `polar_inj` (line 21708). -/
theorem polar_inj {r r' x x' : ℝ}
    (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hx : x ∈ Ico 0 (2 * π)) (hx' : x' ∈ Ico 0 (2 * π))
    (heq : r • cis x = r' • cis x') :
    (r = 0 ∧ r' = 0) ∨ (r = r' ∧ x = x') := by
  have hrr' : r = r' := by
    have h1 := norm2_scale_cis r x
    rw [heq] at h1; rw [norm2_scale_cis] at h1
    rw [abs_of_nonneg hr', abs_of_nonneg hr] at h1; exact h1.symm
  rcases eq_or_lt_of_le hr with rfl | hr_pos
  · exact Or.inl ⟨rfl, hrr'.symm⟩
  · right; refine ⟨hrr', ?_⟩
    rw [hrr'] at heq
    have hne : r' ≠ 0 := ne_of_gt (hrr' ▸ hr_pos)
    have hcis : cis x = cis x' := by
      have h := congr_arg (r'⁻¹ • ·) heq
      simp only [inv_smul_smul₀ hne] at h; exact h
    have hcos : cos x = cos x' := by
      have h := congr_arg (fun z : E2' =>
        (WithLp.equiv 2 (Fin 2 → ℝ)) z 0) hcis
      simp only [cis, point] at h; exact h
    have hsin : sin x = sin x' := by
      have h := congr_arg (fun z : E2' =>
        (WithLp.equiv 2 (Fin 2 → ℝ)) z 1) hcis
      simp only [cis, point] at h; exact h
    have hd : cos (x - x') = 1 := by
      rw [cos_sub, hcos, hsin]; nlinarith [sin_sq_add_cos_sq x']
    rw [Real.cos_eq_one_iff] at hd; obtain ⟨n, hn⟩ := hd
    have : n = 0 := by
      by_contra hn0
      rcases ne_iff_lt_or_gt.mp hn0 with h | h
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
        nlinarith [hx.1, hx'.2, Real.pi_pos]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith [hx.2, hx'.1, Real.pi_pos]
    subst this; simp at hn; linarith

/-- Every point in E2' has a polar representation.
    HOL Light: `polar_exist` (line 21973). -/
theorem polar_exist (x : E2') :
    ∃ r : ℝ, ∃ t, t ∈ Ico 0 (2 * π) ∧ 0 ≤ r ∧ x = r • cis t := by
  by_cases hx : x = 0
  · exact ⟨0, 0, ⟨le_refl _, by positivity⟩, le_refl _, by simp [hx]⟩
  · set z : ℂ := ⟨(WithLp.equiv 2 (Fin 2 → ℝ)) x 0,
      (WithLp.equiv 2 (Fin 2 → ℝ)) x 1⟩
    set θ := z.arg
    set t := if 0 ≤ θ then θ else θ + 2 * π
    have hcos_t : cos t = cos θ := by
      simp only [t]; split_ifs <;> simp [cos_add_two_pi]
    have hsin_t : sin t = sin θ := by
      simp only [t]; split_ifs <;> simp [sin_add_two_pi]
    have hnorm_eq : ‖z‖ = ‖x‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, EuclideanSpace.norm_eq]
      congr 1; simp [z, Fin.sum_univ_two, sq_abs]
    have ht_lo : 0 ≤ t := by
      simp only [t]; split_ifs with h
      · exact h
      · linarith [Complex.neg_pi_lt_arg z]
    have ht_hi : t < 2 * π := by
      simp only [t]; split_ifs with h
      · linarith [Complex.arg_le_pi z, Real.pi_pos]
      · linarith [Complex.arg_le_pi z]
    have hre := Complex.norm_mul_cos_arg z
    have him := Complex.norm_mul_sin_arg z
    rw [hnorm_eq] at hre him
    have heq : x = ‖x‖ • cis t := by
      ext i; fin_cases i <;>
        simp only [cis, point]
      · change z.re = ‖x‖ * cos t; rw [hcos_t, ← hre]
      · change z.im = ‖x‖ * sin t; rw [hsin_t, ← him]
    exact ⟨‖x‖, t, ⟨ht_lo, ht_hi⟩, norm_nonneg _, heq⟩

/-! ## Simple arc basic properties -/

/-- A simple arc is compact.
    HOL Light: `simple_arc_compact` (line 21114). -/
theorem isSimpleArc_compact {C : Set E2'} (hC : IsSimpleArc C) :
    IsCompact C := by
  obtain ⟨f, rfl, hcont, _⟩ := hC
  exact (isCompact_Icc).image hcont

/-- A simple arc is nonempty.
    HOL Light: `simple_arc_nonempty` (line 21129). -/
theorem isSimpleArc_nonempty {C : Set E2'} (hC : IsSimpleArc C) :
    C.Nonempty := by
  obtain ⟨f, rfl, _, _⟩ := hC
  exact ⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩

/-- A simple arc is a subset of E2' (trivial in Lean).
    HOL Light: `simple_arc_euclid` (line 23390). -/
theorem isSimpleArc_subset_univ {C : Set E2'} (_hC : IsSimpleArc C) :
    C ⊆ univ := subset_univ C

/-- Endpoints of a simple arc end are distinct.
    HOL Light: `simple_arc_end_distinct` (line 22577). -/
theorem isSimpleArcEnd_distinct {C : Set E2'} {v v' : E2'}
    (h : IsSimpleArcEnd C v v') : v ≠ v' := by
  obtain ⟨f, _, _, hinj, hf0, hf1⟩ := h
  intro heq
  have : (0 : ℝ) = 1 := hinj (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) (by rw [hf0, hf1, heq])
  linarith

/-- Image is empty iff domain is empty.
    HOL Light: `image_empty` (line 21218). -/
theorem image_empty_iff {α β : Type*} (f : α → β) (S : Set α) :
    f '' S = ∅ ↔ S = ∅ := Set.image_eq_empty

/-! ## Set operation helpers -/

/-- Subsets preserved under union.
    HOL Light: `subset_union_pair` (line 22038). -/
theorem subset_union_pair {α : Type*} {A B A' B' : Set α}
    (hA : A ⊆ A') (hB : B ⊆ B') : A ∪ B ⊆ A' ∪ B' :=
  union_subset_union hA hB

/-- Subsets preserved under intersection.
    HOL Light: `subset_inter_pair` (line 22048). -/
theorem subset_inter_pair {α : Type*} {A B A' B' : Set α}
    (hA : A ⊆ A') (hB : B ⊆ B') : A ∩ B ⊆ A' ∩ B' :=
  inter_subset_inter hA hB

/-- Bijection implies image equals codomain.
    HOL Light: `bij_imp_image` (line 22592). -/
theorem bijOn_image_eq {α β : Type*} {f : α → β} {S : Set α} {T : Set β}
    (hbij : BijOn f S T) : f '' S = T :=
  hbij.image_eq

/-! ## Arc joining, cutting, and restriction -/

/-- Join two arcs with a common endpoint.
    HOL Light: `simple_arc_end_trans` (line 22100). -/
theorem isSimpleArcEnd_trans {C C' : Set E2'} {v v' v'' : E2'}
    (hC : IsSimpleArcEnd C v v')
    (hC' : IsSimpleArcEnd C' v' v'')
    (hinter : C ∩ C' = {v'}) :
    IsSimpleArcEnd (C ∪ C') v v'' :=
  isSimpleArcEnd_concat hC hC' hinter.le

/-- Extract a subarc between two closed sets.
    HOL Light: `simple_arc_end_restriction` (line 22071). -/
theorem isSimpleArcEnd_restriction {C K K' : Set E2'}
    (hC : IsSimpleArc C)
    (hKcl : IsClosed K) (hK'cl : IsClosed K')
    (hdisj : C ∩ K ∩ K' = ∅)
    (hCK : (C ∩ K).Nonempty)
    (hCK' : (C ∩ K').Nonempty) :
    ∃ C' v v', C' ⊆ C ∧ IsSimpleArcEnd C' v v' ∧
      C' ∩ K = {v} ∧ C' ∩ K' = {v'} := by
  obtain ⟨f, rfl, hcont, hinj⟩ := hC
  obtain ⟨t₁, ht₁, hft₁K, hfirst₁⟩ :=
    preimage_first hcont.continuousOn hKcl hCK
  obtain ⟨t₂, ht₂, hft₂K', hfirst₂⟩ :=
    preimage_first hcont.continuousOn hK'cl hCK'
  have hne : t₁ ≠ t₂ := by
    intro heq; subst heq
    have : f t₁ ∈ f '' Icc 0 1 ∩ K ∩ K' :=
      ⟨⟨mem_image_of_mem f ht₁, hft₁K⟩, hft₂K'⟩
    rw [hdisj] at this; exact this.elim
  -- Core: given first A-hit at ta < first B-hit tb, extract subarc
  suffices core : ∀ ta tb : ℝ, ∀ A B : Set E2',
      ta ∈ Icc (0 : ℝ) 1 → tb ∈ Icc (0 : ℝ) 1 → ta < tb →
      f ta ∈ A → f tb ∈ B → IsClosed A →
      (∀ s, s ∈ Ico 0 ta → f s ∉ A) →
      (∀ s, s ∈ Ico 0 tb → f s ∉ B) →
      (f '' Icc 0 1 ∩ A ∩ B = ∅) →
      ∃ C' v v', C' ⊆ f '' Icc 0 1 ∧ IsSimpleArcEnd C' v v' ∧
        C' ∩ A = {v} ∧ C' ∩ B = {v'} by
    rcases lt_or_gt_of_ne hne with h | h
    · exact core t₁ t₂ K K' ht₁ ht₂ h hft₁K hft₂K' hKcl hfirst₁ hfirst₂ hdisj
    · have hdisj' : f '' Icc 0 1 ∩ K' ∩ K = ∅ := by
        rw [← hdisj]; ext x
        simp only [mem_inter_iff]
        exact ⟨fun ⟨⟨hx, hK'⟩, hK⟩ => ⟨⟨hx, hK⟩, hK'⟩,
               fun ⟨⟨hx, hK⟩, hK'⟩ => ⟨⟨hx, hK'⟩, hK⟩⟩
      obtain ⟨C', v, v', hsub, harc, hAv, hBv'⟩ :=
        core t₂ t₁ K' K ht₂ ht₁ h hft₂K' hft₁K hK'cl hfirst₂ hfirst₁ hdisj'
      exact ⟨C', v', v, hsub, isSimpleArcEnd_symm harc, hBv', hAv⟩
  -- Prove the core
  intro ta tb A B hta htb hab hfA hfB hAcl hfirstA hfirstB hdisj'
  -- Find last A-hit on [ta, tb] via reversed preimage_first
  set rev := fun s => f (ta + tb - s) with rev_def
  have rev_cont : ContinuousOn rev (Icc ta tb) :=
    (hcont.comp (continuous_const.sub continuous_id)).continuousOn
  have rev_meet : (rev '' Icc ta tb ∩ A).Nonempty := by
    refine ⟨f ta, ?_, hfA⟩
    exact ⟨tb, ⟨le_of_lt hab, le_refl _⟩,
      show rev tb = f ta by simp only [rev_def]; congr 1; ring⟩
  obtain ⟨s₀, hs₀, hrs₀A, hrevfirst⟩ :=
    preimage_first rev_cont hAcl rev_meet
  set t₃ := ta + tb - s₀
  have ht₃ : t₃ ∈ Icc ta tb := ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩
  have hft₃A : f t₃ ∈ A := hrs₀A
  -- For s ∈ (t₃, tb]: f(s) ∉ A
  have hfnotA : ∀ s ∈ Ioc t₃ tb, f s ∉ A := by
    intro s ⟨hlt, hle⟩ hfs
    exact hrevfirst (ta + tb - s) ⟨by linarith, by linarith⟩
      (show rev (ta + tb - s) ∈ A by
        simp only [rev_def]; convert hfs using 2; ring)
  -- For s ∈ [t₃, tb) ⊆ [0, tb): f(s) ∉ B
  have hfnotB : ∀ s ∈ Ico t₃ tb, f s ∉ B := fun s hs =>
    hfirstB s ⟨le_trans hta.1 (le_trans ht₃.1 hs.1), hs.2⟩
  -- t₃ < tb (otherwise f(tb) ∈ A ∩ B ∩ C)
  have h₃b : t₃ < tb := by
    rcases lt_or_eq_of_le ht₃.2 with h | h
    · exact h
    · exfalso
      have : f tb ∈ f '' Icc 0 1 ∩ A ∩ B :=
        ⟨⟨mem_image_of_mem f htb, h ▸ hft₃A⟩, hfB⟩
      rw [hdisj'] at this; exact this.elim
  -- Reparametrize f|[t₃, tb] to [0, 1]
  obtain ⟨g, hg_img, hg0, hg1, hg_inj, hg_cont⟩ :=
    arc_restrict (le_trans hta.1 ht₃.1) h₃b htb.2 zero_lt_one hinj hcont
  refine ⟨g '' Icc 0 1, g 0, g 1,
    hg_img ▸ Set.image_mono (show Icc t₃ tb ⊆ Icc (0 : ℝ) 1 from
      fun _ hx => ⟨(hta.1.trans ht₃.1).trans hx.1, hx.2.trans htb.2⟩),
    ⟨g, rfl, hg_cont, hg_inj, rfl, rfl⟩, ?_, ?_⟩
  · -- g '' [0,1] ∩ A = {g 0}
    rw [hg_img, hg0]; ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hxA⟩
      have : s = t₃ := by
        by_contra hne
        exact hfnotA s ⟨lt_of_le_of_ne hs.1 (Ne.symm hne), hs.2⟩ hxA
      exact congr_arg f this
    · rintro rfl; exact ⟨⟨t₃, ⟨le_refl _, le_of_lt h₃b⟩, rfl⟩, hft₃A⟩
  · -- g '' [0,1] ∩ B = {g 1}
    rw [hg_img, hg1]; ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hxB⟩
      have : s = tb := by
        by_contra hne
        exact hfnotB s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩ hxB
      exact congr_arg f this
    · rintro rfl; exact ⟨⟨tb, ⟨le_of_lt h₃b, le_refl _⟩, rfl⟩, hfB⟩

/-- A simple arc is homeomorphic to [0,1]: there is a continuous
    bijection from [0,1] to C with continuous inverse.
    HOL Light: `simple_arc_homeo` (line 22476). -/
theorem isSimpleArc_isClosedEmbedding {C : Set E2'} (hC : IsSimpleArc C) :
    ∃ f : ℝ → E2', Continuous f ∧ InjOn f (Icc 0 1) ∧
      f '' Icc 0 1 = C ∧
      IsClosedEmbedding ((Icc (0 : ℝ) 1).restrict f) := by
  obtain ⟨f, rfl, hcont, hinj⟩ := hC
  exact ⟨f, hcont, hinj, rfl,
    (hcont.continuousOn.restrict).isClosedEmbedding hinj.injective⟩

/-- Cut a simple arc at an interior point.
    HOL Light: `simple_arc_end_cut` (line 23741). -/
theorem isSimpleArcEnd_cut {C : Set E2'} {v v' v'' : E2'}
    (hC : IsSimpleArcEnd C v v')
    (hv'' : v'' ∈ C) (hne : v'' ≠ v) (hne' : v'' ≠ v') :
    ∃ C₁ C₂, IsSimpleArcEnd C₁ v v'' ∧ IsSimpleArcEnd C₂ v'' v' ∧
      C₁ ∩ C₂ = {v''} ∧ C₁ ∪ C₂ = C := by
  obtain ⟨f, hfC, hcont, hinj, hf0, hf1⟩ := hC
  -- Find the parameter t for v''
  rw [hfC] at hv''
  obtain ⟨t, ht, hft⟩ := hv''
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at hft; exact hne (hft ▸ hf0)
  have ht1 : t ≠ 1 := by
    intro h; rw [h] at hft; exact hne' (hft ▸ hf1)
  have ht_open : 0 < t ∧ t < 1 := by
    constructor <;> [exact lt_of_le_of_ne ht.1 (Ne.symm ht0);
      exact lt_of_le_of_ne ht.2 ht1]
  -- Build C₁ = f '' [0,t] and C₂ = f '' [t,1]
  set C₁ := f '' Icc 0 t
  set C₂ := f '' Icc t 1
  -- Reparametrize C₁ to [0,1]
  obtain ⟨g₁, hg₁cont, hg₁inj, hg₁_0, hg₁_1, hg₁_img⟩ :=
    arc_reparameter_gen hcont
      (hinj.mono (Icc_subset_Icc_right ht.2)) zero_lt_one ht_open.1
  -- Reparametrize C₂ to [0,1]
  obtain ⟨g₂, hg₂cont, hg₂inj, hg₂_0, hg₂_1, hg₂_img⟩ :=
    arc_reparameter_gen hcont
      (hinj.mono (Icc_subset_Icc_left ht.1)) zero_lt_one
      (by linarith [ht_open.2] : t < 1)
  refine ⟨C₁, C₂, ⟨g₁, hg₁_img, hg₁cont, hg₁inj,
      by rw [hg₁_0, hf0], by rw [hg₁_1, hft]⟩,
    ⟨g₂, hg₂_img, hg₂cont, hg₂inj,
      by rw [hg₂_0, hft], by rw [hg₂_1, hf1]⟩, ?_, ?_⟩
  · -- C₁ ∩ C₂ = {v''}
    ext x; simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨u, hu, hfu⟩⟩
      have hsu : s = u :=
        hinj (Icc_subset_Icc_right ht.2 hs)
          (Icc_subset_Icc_left ht.1 hu) hfu.symm
      have hst : s = t :=
        le_antisymm hs.2 (hsu ▸ hu.1)
      rw [hst]; exact hft
    · intro hx; subst hx
      exact ⟨⟨t, ⟨le_of_lt ht_open.1, le_refl t⟩, hft⟩,
        ⟨t, ⟨le_refl t, le_of_lt ht_open.2⟩, hft⟩⟩
  · -- C₁ ∪ C₂ = C
    rw [hfC]; ext x; simp only [mem_union, mem_image]
    constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨s, Icc_subset_Icc_right ht.2 hs, rfl⟩
      · exact ⟨s, Icc_subset_Icc_left ht.1 hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      by_cases h : s ≤ t
      · left; exact ⟨s, ⟨hs.1, h⟩, rfl⟩
      · right; exact ⟨s, ⟨le_of_lt (not_le.mp h), hs.2⟩, rfl⟩

/-- Two arcs with the same endpoints inside a simple arc are equal.
    HOL Light: `simple_arc_end_inj` (line 23398). -/
theorem isSimpleArcEnd_inj {A B C : Set E2'} {v v' : E2'}
    (hA : IsSimpleArcEnd A v v')
    (hB : IsSimpleArcEnd B v v')
    (hC : IsSimpleArc C) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    A = B := by
  obtain ⟨h, rfl, hcontH, hinjH⟩ := hC
  obtain ⟨fA, hAeq, hcontA, hinjA, hfA0, hfA1⟩ := hA
  obtain ⟨fB, hBeq, hcontB, hinjB, hfB0, hfB1⟩ := hB
  -- φ = invFunOn h [0,1] is the inverse of h restricted to [0,1]
  set φ := Function.invFunOn h (Icc (0 : ℝ) 1)
  have hφ_left : ∀ t ∈ Icc (0 : ℝ) 1, φ (h t) = t :=
    hinjH.leftInvOn_invFunOn
  -- φ is continuous on h '' [0,1]: h restricted to [0,1] is a closed embedding,
  -- giving a homeomorphism ↑(Icc 0 1) ≃ₜ ↑(h '' Icc 0 1); φ agrees with its
  -- symm on the range, hence inherits continuity.
  have hφ_cont : ContinuousOn φ (h '' Icc 0 1) := by
    have hemb := (hcontH.continuousOn.restrict).isClosedEmbedding
      (hinjH.injective)
    set e := hemb.isEmbedding.toHomeomorph
    -- φ agrees with Subtype.val ∘ e.symm on h '' [0,1] (as a subtype)
    have to_rng : ∀ y, y ∈ h '' Icc 0 1 →
        y ∈ range ((Icc (0 : ℝ) 1).restrict h) := by
      intro y hy; obtain ⟨x, hx, rfl⟩ := hy; exact ⟨⟨x, hx⟩, rfl⟩
    have hφ_eq : ∀ y (hy : y ∈ h '' Icc 0 1),
        φ y = (e.symm ⟨y, to_rng y hy⟩).val := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := (mem_image h _ _).mp hy
      rw [hφ_left t ht]
      exact (congrArg Subtype.val
        (hemb.isEmbedding.toHomeomorph_symm_apply ⟨t, ht⟩)).symm
    rw [Metric.continuousOn_iff]
    intro y hy ε hε
    -- e.symm is continuous on the subtype; transfer via hφ_eq
    have hy_rng : y ∈ range ((Icc (0 : ℝ) 1).restrict h) := by
      obtain ⟨t, ht, rfl⟩ := (mem_image h _ _).mp hy; exact ⟨⟨t, ht⟩, rfl⟩
    have hcont_sub : Continuous (Subtype.val ∘ e.symm :
        ↑(range ((Icc 0 1).restrict h)) → ℝ) :=
      continuous_subtype_val.comp e.symm.continuous
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont_sub
      (⟨y, hy_rng⟩ : ↑(range _)) ε hε
    refine ⟨δ, hδ, fun z hz hdist => ?_⟩
    have hz_rng : z ∈ range ((Icc (0 : ℝ) 1).restrict h) := by
      obtain ⟨t, ht, rfl⟩ := (mem_image h _ _).mp hz; exact ⟨⟨t, ht⟩, rfl⟩
    rw [hφ_eq y hy, hφ_eq z hz]
    exact hball ⟨z, hz_rng⟩ (by simpa [Subtype.dist_eq] using hdist)
  -- For each arc (A or B), define g = φ ∘ f : [0,1] → ℝ, continuous injective.
  -- By IVT, g is mono or anti, so g '' [0,1] = Icc (min (φ v) (φ v')) (max ...).
  -- Since A and B share endpoints, φ '' A = φ '' B, so A = B.
  -- gA continuous and injective
  have hfA_sub : fA '' Icc 0 1 ⊆ h '' Icc 0 1 := hAeq ▸ hAC
  have hfB_sub : fB '' Icc 0 1 ⊆ h '' Icc 0 1 := hBeq ▸ hBC
  have hgA_cont : ContinuousOn (φ ∘ fA) (Icc 0 1) :=
    hφ_cont.comp hcontA.continuousOn
      (fun x hx => hfA_sub (mem_image_of_mem fA hx))
  have hgA_inj : InjOn (φ ∘ fA) (Icc 0 1) := by
    intro a ha b hb hab; simp only [Function.comp] at hab
    have ha' := hfA_sub (mem_image_of_mem fA ha)
    have hb' := hfA_sub (mem_image_of_mem fA hb)
    obtain ⟨ta, hta, hta_eq⟩ := ha'; obtain ⟨tb, htb, htb_eq⟩ := hb'
    rw [← hta_eq, hφ_left ta hta, ← htb_eq, hφ_left tb htb] at hab
    exact hinjA ha hb (hta_eq.symm.trans (hab ▸ htb_eq))
  -- gB continuous and injective
  have hgB_cont : ContinuousOn (φ ∘ fB) (Icc 0 1) :=
    hφ_cont.comp hcontB.continuousOn
      (fun x hx => hfB_sub (mem_image_of_mem fB hx))
  have hgB_inj : InjOn (φ ∘ fB) (Icc 0 1) := by
    intro a ha b hb hab; simp only [Function.comp] at hab
    have ha' := hfB_sub (mem_image_of_mem fB ha)
    have hb' := hfB_sub (mem_image_of_mem fB hb)
    obtain ⟨ta, hta, hta_eq⟩ := ha'; obtain ⟨tb, htb, htb_eq⟩ := hb'
    rw [← hta_eq, hφ_left ta hta, ← htb_eq, hφ_left tb htb] at hab
    exact hinjB ha hb (hta_eq.symm.trans (hab ▸ htb_eq))
  -- By IVT, each is mono or anti; in all 4 cases the images are the same
  -- because endpoints match: (φ ∘ fA) 0 = φ v = (φ ∘ fB) 0, etc.
  -- Helper: φ '' (f '' [0,1]) = (φ ∘ f) '' [0,1]
  have hφ_fA : ∀ x ∈ fA '' Icc 0 1, x ∈ h '' Icc 0 1 := fun x hx => hfA_sub hx
  have hφ_fB : ∀ x ∈ fB '' Icc 0 1, x ∈ h '' Icc 0 1 := fun x hx => hfB_sub hx
  -- Both images are determined by {φ v, φ v'}: either [φ v, φ v'] or [φ v', φ v]
  -- In all cases they are the same set Icc (min (φ v) (φ v')) (max (φ v) (φ v'))
  have img_eq : (φ ∘ fA) '' Icc 0 1 = (φ ∘ fB) '' Icc 0 1 := by
    -- Determine image of gA
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one hgA_cont hgA_inj with
      hmonoA | hantiA <;>
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one hgB_cont hgB_inj with
      hmonoB | hantiB
    · -- Both mono: image = [g(0), g(1)]
      rw [hgA_cont.image_Icc_of_monotoneOn zero_le_one hmonoA.monotoneOn,
          hgB_cont.image_Icc_of_monotoneOn zero_le_one hmonoB.monotoneOn]
      simp [Function.comp, hfA0, hfA1, hfB0, hfB1]
    · -- A mono, B anti: contradiction — endpoints force φ v < φ v' and φ v > φ v'
      exfalso
      have h1 := hmonoA (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
        zero_lt_one
      have h2 := hantiB (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
        zero_lt_one
      simp only [Function.comp, hfA0, hfA1, hfB0, hfB1] at h1 h2
      linarith
    · exfalso
      have h1 := hantiA (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
        zero_lt_one
      have h2 := hmonoB (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
        zero_lt_one
      simp only [Function.comp, hfA0, hfA1, hfB0, hfB1] at h1 h2
      linarith
    · rw [hgA_cont.image_Icc_of_antitoneOn zero_le_one hantiA.antitoneOn,
          hgB_cont.image_Icc_of_antitoneOn zero_le_one hantiB.antitoneOn]
      simp [Function.comp, hfA0, hfA1, hfB0, hfB1]
  -- φ '' A = φ '' B, and φ is injective on h '' [0,1]
  rw [hAeq, hBeq]
  rw [show φ ∘ fA '' Icc 0 1 = φ '' (fA '' Icc 0 1) from image_comp φ fA _] at img_eq
  rw [show φ ∘ fB '' Icc 0 1 = φ '' (fB '' Icc 0 1) from image_comp φ fB _] at img_eq
  have hφ_inj : InjOn φ (h '' Icc 0 1) := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ heq
    rw [hφ_left s hs, hφ_left t ht] at heq
    exact congrArg h heq
  exact (hφ_inj.image_eq_image_iff hφ_fA hφ_fB).mp img_eq

/-- Parametrize a simple closed curve with prescribed basepoint.
    HOL Light: `simple_closed_curve_pt` (line 23845). -/
theorem isSimpleClosedCurve_pt {C : Set E2'} {v : E2'}
    (hC : IsSimpleClosedCurve C) (hv : v ∈ C) :
    ∃ f : ℝ → E2', C = f '' Icc 0 1 ∧ Continuous f ∧
      InjOn f (Ico 0 1) ∧ f 0 = v ∧ f 0 = f 1 := by
  obtain ⟨f, hfC, hcont, hinj, hperiod⟩ := hC
  rw [hfC] at hv; obtain ⟨t₀, ht₀, hft₀⟩ := hv
  rcases eq_or_lt_of_le ht₀.1 with rfl | h0
  · exact ⟨f, hfC, hcont, hinj, hft₀ ▸ rfl, hft₀ ▸ hperiod⟩
  rcases eq_or_lt_of_le ht₀.2 with ht1 | h1
  · subst ht1; rw [← hperiod] at hft₀
    exact ⟨f, hfC, hcont, hinj, hft₀ ▸ rfl, hft₀ ▸ hperiod⟩
  -- Now 0 < t₀ < 1.
  set g : ℝ → E2' := fun s =>
    if s ≤ 1 - t₀ then f (s + t₀) else f (s + t₀ - 1)
  have g_alt : ∀ s, g s =
      if s + t₀ ≤ 1 then f (s + t₀) else f (s + t₀ - 1) := by
    intro s; simp only [g]
    congr 1; exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  refine ⟨g, ?img, ?cont, ?inj, ?base, ?period⟩
  case img =>
    rw [hfC]; ext x; constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [g_alt, mem_image]
      by_cases ht₀t : t₀ ≤ t
      · refine ⟨t - t₀, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
        simp only [show t - t₀ + t₀ ≤ 1 from by linarith [ht.2], ite_true]; ring_nf
      · push Not at ht₀t
        refine ⟨t - t₀ + 1, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
        split_ifs with hle
        · -- t + 1 ≤ 1 so t = 0; f(t+1) = f(1) = f(0) = f(t)
          have ht0 : t = 0 := by linarith [ht.1]
          subst ht0; rw [show (0 : ℝ) - t₀ + 1 + t₀ = 1 from by ring]; exact hperiod.symm
        · congr 1; ring
    · rintro ⟨s, hs, rfl⟩
      simp only [g_alt, mem_image]
      by_cases hle : s + t₀ ≤ 1
      · simp only [hle, ite_true]
        exact ⟨s + t₀, ⟨by linarith [hs.1], hle⟩, rfl⟩
      · push Not at hle
        simp only [show ¬(s + t₀ ≤ 1) from by linarith, ite_false]
        exact ⟨s + t₀ - 1, ⟨by linarith, by linarith [hs.2]⟩, rfl⟩
  case cont =>
    show Continuous g
    exact Continuous.if_le
      (hcont.comp (continuous_id.add continuous_const))
      (hcont.comp ((continuous_id.add continuous_const).sub continuous_const))
      continuous_id continuous_const
      (fun s (hs : s = 1 - t₀) => by
        have h2 : s + t₀ - 1 = 0 := by linarith
        have h1 : s + t₀ = 1 := by linarith
        rw [h2, h1, hperiod])
  case inj =>
    intro a ha b hb hgab
    rw [g_alt, g_alt] at hgab
    have h0I : (0 : ℝ) ∈ Ico 0 1 := ⟨le_refl _, one_pos⟩
    by_cases ha_le : a + t₀ ≤ 1 <;> by_cases hb_le : b + t₀ ≤ 1
    · -- Both a + t₀ ≤ 1 and b + t₀ ≤ 1
      simp only [ha_le, hb_le, ite_true] at hgab
      rcases eq_or_lt_of_le ha_le with ha1 | ha_lt
      · rcases eq_or_lt_of_le hb_le with hb1 | hb_lt
        · linarith
        · rw [ha1, ← hperiod] at hgab
          have hbI : b + t₀ ∈ Ico 0 1 := ⟨by linarith [hb.1], hb_lt⟩
          linarith [hinj h0I hbI hgab, hb.1]
      · rcases eq_or_lt_of_le hb_le with hb1 | hb_lt
        · rw [hb1, ← hperiod] at hgab
          have haI : a + t₀ ∈ Ico 0 1 := ⟨by linarith [ha.1], ha_lt⟩
          linarith [hinj haI h0I hgab, ha.1]
        · have haI : a + t₀ ∈ Ico 0 1 := ⟨by linarith [ha.1], ha_lt⟩
          have hbI : b + t₀ ∈ Ico 0 1 := ⟨by linarith [hb.1], hb_lt⟩
          linarith [hinj haI hbI hgab]
    · -- a + t₀ ≤ 1, b + t₀ > 1
      push Not at hb_le
      simp only [ha_le, show ¬(b + t₀ ≤ 1) from by linarith, ite_true, ite_false] at hgab
      have hbI : b + t₀ - 1 ∈ Ico 0 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
      rcases eq_or_lt_of_le ha_le with ha1 | ha_lt
      · -- a + t₀ = 1: f(1) = f(b+t₀-1), use periodicity → f(0) = f(b+t₀-1)
        rw [ha1, ← hperiod] at hgab
        linarith [hinj h0I hbI hgab]
      · -- a + t₀ < 1: f(a+t₀) = f(b+t₀-1), injectivity gives a + t₀ = b + t₀ - 1
        have haI : a + t₀ ∈ Ico 0 1 := ⟨by linarith [ha.1], ha_lt⟩
        linarith [hinj haI hbI hgab, ha.1, hb.2]
    · -- a + t₀ > 1, b + t₀ ≤ 1: symmetric
      push Not at ha_le
      simp only [show ¬(a + t₀ ≤ 1) from by linarith, hb_le,
        ite_false, ite_true] at hgab
      have haI : a + t₀ - 1 ∈ Ico 0 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
      rcases eq_or_lt_of_le hb_le with hb1 | hb_lt
      · rw [hb1, ← hperiod] at hgab
        linarith [hinj haI h0I hgab]
      · have hbI : b + t₀ ∈ Ico 0 1 := ⟨by linarith [hb.1], hb_lt⟩
        linarith [hinj haI hbI hgab, ha.2, hb.1]
    · -- Both a + t₀ > 1 and b + t₀ > 1
      push Not at ha_le hb_le
      simp only [show ¬(a + t₀ ≤ 1) from by linarith,
        show ¬(b + t₀ ≤ 1) from by linarith, ite_false] at hgab
      have haI : a + t₀ - 1 ∈ Ico 0 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
      have hbI : b + t₀ - 1 ∈ Ico 0 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
      linarith [hinj haI hbI hgab]
  case base =>
    show g 0 = v
    simp only [g, show (0 : ℝ) ≤ 1 - t₀ from by linarith, ite_true,
      zero_add, hft₀]
  case period =>
    show g 0 = g 1
    simp only [g, show (0 : ℝ) ≤ 1 - t₀ from by linarith, ite_true, zero_add,
      show ¬((1 : ℝ) ≤ 1 - t₀) from by linarith, ite_false,
      show (1 : ℝ) + t₀ - 1 = t₀ from by ring]

/-- Segment of a closed curve parametrization is a simple arc.
    HOL Light: `simple_arc_segment` (line 24160). -/
theorem isSimpleArcEnd_segment {f : ℝ → E2'} {u v : ℝ}
    (hcont : Continuous f)
    (hinj : InjOn f (Ico 0 1))
    (hperiod : f 0 = f 1)
    (huv : 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧ (0 < u ∨ v < 1)) :
    IsSimpleArcEnd (f '' Icc u v) (f u) (f v) := by
  have huv' : u < v := huv.2.1
  -- f is injective on [u,v]
  have hinj_uv : InjOn f (Icc u v) := by
    rcases huv.2.2.2 with hu_pos | hv_lt
    · -- 0 < u, so [u,v] ⊆ [u,1] ⊆ (0,1]
      intro s hs t ht hst
      -- Handle t = 1 or s = 1 vs both < 1
      by_cases hs1 : s < 1 <;> by_cases ht1 : t < 1
      · exact hinj ⟨le_trans (le_of_lt hu_pos) hs.1, hs1⟩
          ⟨le_trans (le_of_lt hu_pos) ht.1, ht1⟩ hst
      · push Not at ht1
        have htv : t = 1 := le_antisymm (ht.2.trans huv.2.2.1) ht1
        have : f s = f 0 := by rw [hst, htv, hperiod]
        have := hinj ⟨le_trans (le_of_lt hu_pos) hs.1, hs1⟩
          ⟨le_refl 0, by linarith [Real.pi_pos]⟩ this
        linarith [hs.1]
      · push Not at hs1
        have hsv : s = 1 := le_antisymm (hs.2.trans huv.2.2.1) hs1
        have : f t = f 0 := by rw [← hst, hsv, hperiod]
        have := hinj ⟨le_trans (le_of_lt hu_pos) ht.1, ht1⟩
          ⟨le_refl 0, by linarith [Real.pi_pos]⟩ this
        linarith [ht.1]
      · push Not at hs1 ht1
        have : s = 1 := le_antisymm (hs.2.trans huv.2.2.1) hs1
        have : t = 1 := le_antisymm (ht.2.trans huv.2.2.1) ht1
        linarith
    · -- v < 1, so [u,v] ⊆ [0,v] ⊂ [0,1)
      exact hinj.mono fun x (hx : x ∈ Icc u v) =>
        (show x ∈ Ico 0 1 from ⟨huv.1.trans hx.1, hx.2.trans_lt hv_lt⟩)
  obtain ⟨g, hgcont, hginj, hg0, hg1, hgimg⟩ :=
    arc_reparameter_gen hcont hinj_uv zero_lt_one huv'
  exact ⟨g, hgimg, hgcont, hginj, by rw [hg0], by rw [hg1]⟩

/-- Cut a simple closed curve at two points.
    HOL Light: `simple_closed_cut` (line 23945). -/
theorem isSimpleClosedCurve_cut {C : Set E2'} {v v' : E2'}
    (hC : IsSimpleClosedCurve C) (hv : v ∈ C) (hv' : v' ∈ C) (hne : v ≠ v') :
    ∃ C₁ C₂, IsSimpleArcEnd C₁ v v' ∧ IsSimpleArcEnd C₂ v v' ∧
      C₁ ∪ C₂ = C ∧ C₁ ∩ C₂ = {v, v'} := by
  -- Get parametrization with f(0) = v
  obtain ⟨f, hfC, hcont, hinj, hf0, hperiod⟩ := isSimpleClosedCurve_pt hC hv
  -- Find t with f(t) = v', 0 < t < 1
  rw [hfC] at hv'; obtain ⟨t, ht, hft⟩ := hv'
  have ht_ne0 : t ≠ 0 := by
    rintro rfl; exact hne (hf0.symm.trans hft)
  have ht_ne1 : t ≠ 1 := by
    rintro rfl; exact hne (hf0.symm.trans (hperiod.symm ▸ hft))
  have h0t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_ne0)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 ht_ne1
  refine ⟨f '' Icc 0 t, f '' Icc t 1, ?_, ?_, ?_, ?_⟩
  · -- IsSimpleArcEnd (f '' [0,t]) v v'
    have := isSimpleArcEnd_segment hcont hinj hperiod
      ⟨le_refl 0, h0t, le_of_lt ht1, Or.inr ht1⟩
    rwa [hf0, hft] at this
  · -- IsSimpleArcEnd (f '' [t,1]) v' v
    have := isSimpleArcEnd_segment hcont hinj hperiod
      ⟨le_of_lt h0t, ht1, le_refl 1, Or.inl h0t⟩
    rw [hft, hperiod.symm, hf0] at this
    exact isSimpleArcEnd_symm this
  · -- f '' [0,t] ∪ f '' [t,1] = C
    rw [hfC, ← Set.image_union]
    congr 1; ext x; constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans (le_of_lt ht1)⟩
      · exact ⟨le_trans (le_of_lt h0t) hx.1, hx.2⟩
    · intro hx
      by_cases hle : x ≤ t
      · left; exact ⟨hx.1, hle⟩
      · right; exact ⟨le_of_lt (not_le.mp hle), hx.2⟩
  · -- f '' [0,t] ∩ f '' [t,1] = {v, v'}
    ext x; constructor
    · rintro ⟨⟨s₁, hs₁, rfl⟩, s₂, hs₂, hfs⟩
      -- f s₁ = f s₂ with s₁ ∈ [0,t], s₂ ∈ [t,1]
      by_cases hs_eq : s₁ = s₂
      · -- s₁ = s₂ → both in [0,t] ∩ [t,1] = {t}
        have : s₁ = t := le_antisymm hs₁.2 (hs_eq ▸ hs₂.1)
        rw [this, hft]; exact Or.inr rfl
      · -- s₁ ≠ s₂ → use injectivity
        by_cases hs₂1 : s₂ < 1
        · -- Both in Ico 0 1
          have hs₁I : s₁ ∈ Ico 0 1 :=
            ⟨hs₁.1, lt_of_le_of_lt hs₁.2 ht1⟩
          have hs₂I : s₂ ∈ Ico 0 1 :=
            ⟨le_trans (le_of_lt h0t) hs₂.1, hs₂1⟩
          exact absurd (hinj hs₁I hs₂I hfs.symm) hs_eq
        · -- s₂ = 1 → f s₁ = f 1 = f 0, so s₁ = 0
          push Not at hs₂1
          have hs₂_eq : s₂ = 1 := le_antisymm hs₂.2 hs₂1
          rw [hs₂_eq, ← hperiod] at hfs
          have hs₁I : s₁ ∈ Ico 0 1 :=
            ⟨hs₁.1, lt_of_le_of_lt hs₁.2 ht1⟩
          have h0I : (0 : ℝ) ∈ Ico 0 1 :=
            ⟨le_refl 0, zero_lt_one⟩
          have := hinj hs₁I h0I hfs.symm
          rw [this, hf0]; exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨0, ⟨le_refl 0, le_of_lt h0t⟩, hf0⟩,
               ⟨1, ⟨le_of_lt ht1, le_refl 1⟩, hperiod ▸ hf0⟩⟩
      · exact ⟨⟨t, ⟨le_of_lt h0t, le_refl t⟩, hft⟩,
               ⟨t, ⟨le_refl t, le_of_lt ht1⟩, hft⟩⟩

/-- Extension of continuous function from [a,b] to ℝ.
    HOL Light: `cont_extend_real_lemma` (line 23120). -/
theorem continuous_extend_Icc {a b : ℝ} {Y : Type*}
    [TopologicalSpace Y] [MetricSpace Y]
    {f : ℝ → Y} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) :
    ∃ g : ℝ → Y, Continuous g ∧ ∀ x ∈ Icc a b, f x = g x := by
  have hab' : a ≤ b := le_of_lt hab
  let f' : Set.Icc a b → Y := Set.restrict (Icc a b) f
  have hf'cont : Continuous f' :=
    continuousOn_iff_continuous_restrict.mp hcont
  exact ⟨Set.IccExtend hab' f', hf'cont.Icc_extend',
    fun x hx => (Set.IccExtend_of_mem hab' f' hx).symm⟩

/-! ## Graph disk lemma -/

/-- Separation lemma for finite planar graphs: there exists a radius r > 0
    such that closed balls around distinct vertices are disjoint, and
    each edge avoids the closed ball of any non-incident vertex.
    HOL Light: `graph_disk` (line 21302). -/
theorem graph_disk {G : HolGraph E2' (Set E2')}
    (hplane : IsPlaneGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty) :
    ∃ r : ℝ, 0 < r ∧
      (∀ v v', v ∈ G.vertexSet → v' ∈ G.vertexSet → v ≠ v' →
        Metric.closedBall v r ∩ Metric.closedBall v' r = ∅) ∧
      (∀ e v, e ∈ G.edgeSet → v ∈ G.vertexSet → v ∉ G.inc e →
        e ∩ Metric.closedBall v r = ∅) := by
  -- Helper: edges are compact and nonempty
  have hedge_compact : ∀ e ∈ G.edgeSet, IsCompact e := by
    intro e he
    obtain ⟨v, v', _, _, _, harc⟩ := hplane.edges_are_arcs e he
    exact isSimpleArc_compact (isSimpleArcEnd_isSimpleArc harc)
  have hedge_nonempty : ∀ e ∈ G.edgeSet, (e : Set E2').Nonempty := by
    intro e he
    obtain ⟨v, v', _, _, _, harc⟩ := hplane.edges_are_arcs e he
    exact isSimpleArc_nonempty (isSimpleArcEnd_isSimpleArc harc)
  -- Helper: v ∉ G.inc e implies v ∉ e (for vertices)
  have hnotmem : ∀ e ∈ G.edgeSet, ∀ v ∈ G.vertexSet,
      v ∉ G.inc e → v ∉ e :=
    fun e he v hv hinc hmem => hinc (hplane.vertex_on_edge e he v hv hmem)
  -- Collect positive distance bounds
  -- For distinct vertices: dist v v' / 2 > 0
  -- For non-incident (e,v): setDist {v} e > 0
  -- Take min bound and halve
  -- Set S of all relevant positive values
  let Vf := hfin_v.toFinset
  let Ef := hfin_e.toFinset
  -- Build the set of all bounds
  have hVf_mem : ∀ v, v ∈ Vf ↔ v ∈ G.vertexSet :=
    fun v => Finite.mem_toFinset hfin_v
  have hEf_mem : ∀ e, e ∈ Ef ↔ e ∈ G.edgeSet :=
    fun e => Finite.mem_toFinset hfin_e
  -- There exist two distinct vertices (from any edge)
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨u₀, w₀, huw, hinc_e⟩ := G.edge_pair e₀ he₀
  have hu₀ : u₀ ∈ G.vertexSet := by
    have := (G.well_formed e₀ he₀).1
    rw [hinc_e] at this; exact this (mem_insert u₀ {w₀})
  have hw₀ : w₀ ∈ G.vertexSet := by
    have := (G.well_formed e₀ he₀).1
    rw [hinc_e] at this
    exact this (mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr rfl)))
  -- Build finsets of bounds
  -- A' = vertex-vertex distances / 2
  let A : Finset ℝ := (Vf ×ˢ Vf).image (fun p => dist p.1 p.2 / 2)
      |>.filter (0 < ·)
  -- B' = setDist {v} e for non-incident pairs
  let B : Finset ℝ := (Ef ×ˢ Vf).image (fun p => setDist {p.2} p.1)
      |>.filter (0 < ·)
  let S := A ∪ B
  -- S is nonempty: dist u₀ w₀ / 2 > 0
  have hd_pos : 0 < dist u₀ w₀ / 2 :=
    div_pos (dist_pos.mpr huw) two_pos
  have hA_nonempty : A.Nonempty := by
    refine ⟨dist u₀ w₀ / 2, Finset.mem_filter.mpr ⟨?_, hd_pos⟩⟩
    exact Finset.mem_image.mpr ⟨(u₀, w₀), Finset.mem_product.mpr
      ⟨(hVf_mem u₀).mpr hu₀, (hVf_mem w₀).mpr hw₀⟩, rfl⟩
  have hS_nonempty : S.Nonempty :=
    hA_nonempty.mono (Finset.subset_union_left)
  -- All elements of S are positive
  have hS_pos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hA | hB
    · exact (Finset.mem_filter.mp hA).2
    · exact (Finset.mem_filter.mp hB).2
  -- Take r = S.min' / 2
  let m := S.min' hS_nonempty
  have hm_pos : 0 < m := hS_pos m (Finset.min'_mem S hS_nonempty)
  have hm_le : ∀ x ∈ S, m ≤ x := fun x hx => Finset.min'_le S x hx
  use m / 2
  refine ⟨by linarith, ?_, ?_⟩
  · -- Vertex-vertex: closed balls disjoint
    intro v v' hv hv' hvv'
    rw [Set.eq_empty_iff_forall_notMem]
    intro x ⟨hxv, hxv'⟩
    rw [Metric.mem_closedBall] at hxv hxv'
    have hd : dist v v' ≤ m := by
      have h1 : dist v x ≤ m / 2 := (dist_comm x v ▸ hxv)
      have h2 : dist x v' ≤ m / 2 := hxv'
      linarith [dist_triangle v x v']
    have hd2 : dist v v' / 2 ∈ A := by
      refine Finset.mem_filter.mpr ⟨?_, div_pos (dist_pos.mpr hvv') two_pos⟩
      exact Finset.mem_image.mpr ⟨(v, v'), Finset.mem_product.mpr
        ⟨(hVf_mem v).mpr hv, (hVf_mem v').mpr hv'⟩, rfl⟩
    have hm_le_d : m ≤ dist v v' / 2 :=
      hm_le _ (Finset.mem_union.mpr (Or.inl hd2))
    linarith
  · -- Edge-vertex: edge avoids closed ball
    intro e₁ v₁ he₁ hv₁ hninc₁
    rw [Set.eq_empty_iff_forall_notMem]
    intro x ⟨hxe, hxv⟩
    rw [Metric.mem_closedBall] at hxv
    -- setDist {v₁} e₁ is positive and attained
    have hv_notin_e : v₁ ∉ e₁ := hnotmem e₁ he₁ v₁ hv₁ hninc₁
    have hcompact_e : IsCompact e₁ := hedge_compact e₁ he₁
    have hnonempty_e : (e₁ : Set E2').Nonempty := hedge_nonempty e₁ he₁
    obtain ⟨_, hp_mem, p', hp', hsd_eq⟩ :=
      compact_distance isCompact_singleton hcompact_e
        ⟨v₁, Set.mem_singleton v₁⟩ hnonempty_e
    rw [Set.mem_singleton_iff] at hp_mem
    have hsd_pos : 0 < setDist {v₁} e₁ := by
      rw [hsd_eq, hp_mem]
      exact dist_pos.mpr (fun h => hv_notin_e (h ▸ hp'))
    -- setDist {v₁} e₁ ∈ B ⊆ S
    have hsd_mem : setDist {v₁} e₁ ∈ B := by
      refine Finset.mem_filter.mpr ⟨?_, hsd_pos⟩
      exact Finset.mem_image.mpr ⟨(e₁, v₁), Finset.mem_product.mpr
        ⟨(hEf_mem e₁).mpr he₁, (hVf_mem v₁).mpr hv₁⟩, rfl⟩
    have hm_le_sd : m ≤ setDist {v₁} e₁ :=
      hm_le _ (Finset.mem_union.mpr (Or.inr hsd_mem))
    -- But setDist {v₁} e₁ ≤ dist v₁ x ≤ m / 2
    have hsd_le : setDist {v₁} e₁ ≤ dist v₁ x :=
      setDist_le_dist (Set.mem_singleton v₁) hxe
    have hxv_comm : dist v₁ x ≤ m / 2 := dist_comm x v₁ ▸ hxv
    linarith

end
