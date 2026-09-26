/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionW_RectagGraphs

/-!
# Section X: Rational Approximation
## HOL Light: Section X (Lines 45373–46342)

Epsilon-translations, homeomorphism properties of translations/scalings,
and rational approximation of points in ℝ².
The main result `graph_int_model` shows that any planar graph with bounded
degree can be realized on integer-coordinate hyperplane support.

### Key HOL Light definitions
- `eps_translate`: Directional translation (horizontal or vertical)
- `eps_hyper`: Directional hyperplane (vertical line if eps=true, horizontal if eps=false)
- `eps_scale`: Directional scaling
- `graph_support_eps`: Graph supported by eps-hyperplanes
- `iso_support_eps_pair`: Pairs (H,E) with H isomorphic to G and supported by E
- `count_iso_eps_pair`: Count of positive-parameter hyperplanes in support
- `graph_int_model`: Main result — planar graphs have integer-coordinate models
-/

namespace JordanCurveTheorem
open Set

/-! ## §X.1 Directional translations and scalings -/

/-- Directional translation: horizontal if `eps = true`, vertical if `eps = false`.
    HOL Light: `eps_translate_def` (line 45386). -/
def epsTranslate (eps : Bool) : ℝ → E2' → E2' :=
  if eps then hTranslate else vTranslate

/-- HOL Light: `eps_translate` (line 45389). -/
theorem epsTranslate_def (eps : Bool) (r : ℝ) :
    epsTranslate eps r = if eps then hTranslate r else vTranslate r := by
  cases eps <;> rfl

/-- Directional translation homeomorphism.
    HOL Light: `homeomorphism_eps_translate` (line 45399). -/
noncomputable def epsTranslate_homeomorph (eps : Bool) (r : ℝ) : E2' ≃ₜ E2' :=
  if eps then hTranslate_homeomorph r else vTranslate_homeomorph r

/-- The `epsTranslate_homeomorph` homeomorphism agrees pointwise with `epsTranslate`:
    applying the homeomorphism to a point `x` yields the same result as `epsTranslate eps r x`.
    HOL Light: `homeomorphism_eps_translate` (line 45399). -/
theorem epsTranslate_homeomorph_eq (eps : Bool) (r : ℝ) (x : E2') :
    epsTranslate_homeomorph eps r x = epsTranslate eps r x := by
  cases eps <;> rfl

/-- Directional hyperplane: vertical line (x = z) if `eps = true`,
    horizontal line (y = z) if `eps = false`.
    HOL Light: `eps_hyper` (line 45409). -/
def epsHyper (eps : Bool) (z : ℝ) : Set E2' :=
  if eps then hyperplane2 0 z else hyperplane2 1 z

/-- HOL Light: `eps_hyper_translate` (line 45412). -/
theorem epsHyper_translate (eps : Bool) (r z : ℝ) :
    epsTranslate eps r '' epsHyper eps z = epsHyper eps (z + r) := by
  cases eps <;> simp [epsTranslate, epsHyper, hyperplane1_hTranslate, hyperplane2_vTranslate]

/-- HOL Light: `eps_hyper_translate_perp` (line 45423). -/
theorem epsHyper_translate_perp (eps : Bool) (r z : ℝ) :
    epsTranslate eps r '' epsHyper (!eps) z = epsHyper (!eps) z := by
  cases eps <;> simp [epsTranslate, epsHyper, hyperplane2_hTranslate, hyperplane1_vTranslate]

/-- Directional scaling: r_scale if `eps = true`, u_scale if `eps = false`.
    HOL Light: `eps_scale` (line 45434). -/
noncomputable def epsScale (eps : Bool) : ℝ → E2' → E2' :=
  if eps then rScale else uScale

/-- HOL Light: `eps_hyper_scale_perp` (line 45437). -/
theorem epsHyper_scale_perp (eps : Bool) (r z : ℝ) (hr : 0 < r) :
    epsScale eps r '' epsHyper (!eps) z = epsHyper (!eps) z := by
  cases eps <;> simp [epsScale, epsHyper, hyperplane1_uScale hr, hyperplane2_rScale hr]

/-- HOL Light: `eps_hyper_scale` (line 45448). -/
theorem epsHyper_scale (eps : Bool) (r z : ℝ) (hr : 0 < r) :
    epsScale eps r '' epsHyper eps z =
      epsHyper eps (if 0 < z then r * z else z) := by
  cases eps <;> simp [epsScale, epsHyper, hyperplane1_rScale hr, hyperplane2_uScale hr]

/-- Directional scaling homeomorphism.
    HOL Light: `homeomorphism_eps_scale` (line 45459). -/
noncomputable def epsScale_homeomorph (eps : Bool) {r : ℝ} (hr : 0 < r) : E2' ≃ₜ E2' :=
  if eps then rScale_homeomorph hr else uScale_homeomorph hr

/-! ## §X.2 Graph support and isomorphism pairs -/

/-- Graph supported by epsilon-hyperplanes.
    HOL Light: `graph_support_eps` (line 45468). -/
def graphSupportEps (G : HolGraph E2' (Set E2')) (E : Set (Set E2')) : Prop :=
  IsGoodPlaneGraph G ∧ E.Finite ∧
  (∀ e ∈ G.edgeSet, e ⊆ ⋃₀ E) ∧
  (∀ v ∈ G.vertexSet, epsHyper true (v 0) ∈ E ∧ epsHyper false (v 1) ∈ E) ∧
  (∀ e ∈ E, ∃ z eps, e = epsHyper eps z) ∧
  (∀ z eps, z ≤ 0 ∧ epsHyper eps z ∈ E → ∃ j : ℕ, z = -↑j)

/-- Pairs (H, E) where H is isomorphic to G and supported by E.
    HOL Light: `iso_support_eps_pair` (line 45476). -/
def isoSupportEpsPair {V E₀ : Type*} (G : HolGraph V E₀)
    (p : HolGraph E2' (Set E2') × Set (Set E2')) : Prop :=
  GraphIsomorphic G p.1 ∧ graphSupportEps p.1 p.2

/-- HOL Light: `eps_hyper_ne` (line 45480). -/
theorem epsHyper_ne (z z' : ℝ) (eps : Bool) :
    epsHyper eps z ≠ epsHyper (!eps) z' := by
  cases eps <;> simp [epsHyper, hyperplane_ne, Ne.symm (hyperplane_ne z' z)]

/-- HOL Light: `eps_hyper_inj` (line 45490). -/
theorem epsHyper_inj (z z' : ℝ) (eps eps' : Bool) :
    epsHyper eps z = epsHyper eps' z' ↔ eps = eps' ∧ z = z' := by
  constructor
  · intro h
    cases eps <;> cases eps' <;>
      simp only [epsHyper, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Fin.isValue, true_and, false_and] at h ⊢
    · exact hyperplane2_1_injective h
    · exact absurd h (Ne.symm (hyperplane_ne z' z))
    · exact absurd h (hyperplane_ne z z')
    · exact hyperplane2_0_injective h
  · rintro ⟨rfl, rfl⟩; rfl

/-- HOL Light: `iso_support_eps_nonempty` (line 45510). -/
theorem isoSupportEpsPair_nonempty {V E₀ : Type*} (G : HolGraph V E₀)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    ∃ p, isoSupportEpsPair G p := by
  obtain ⟨H, S, hiso, hfin, hgood, hedge, hvert, hS_hyp⟩ :=
    graph_support_init G hplanar hfin_e hfin_v hne hdeg
  refine ⟨(H, S), hiso, hgood, hfin, hedge, fun v hv => hvert v hv,
    fun e he => ?_, fun z eps ⟨hle, hmem⟩ => ?_⟩
  · obtain ⟨z, _, rfl | rfl⟩ := hS_hyp e he
    · exact ⟨z, true, rfl⟩
    · exact ⟨z, false, rfl⟩
  · exfalso
    obtain ⟨w, hw, h | h⟩ := hS_hyp _ hmem
    · have := ((epsHyper_inj z w eps true).mp h).2; linarith
    · have := ((epsHyper_inj z w eps false).mp h).2; linarith

/-! ## §X.3 Counting and minimization -/

/-- Count of positive-parameter hyperplanes in support.
    HOL Light: `count_iso_eps_pair` (line 45551). -/
noncomputable def countIsoEpsPair
    (p : HolGraph E2' (Set E2') × Set (Set E2')) : ℕ :=
  ({e ∈ p.2 | ∃ z eps, 0 < z ∧ e = epsHyper eps z}).ncard

/-- HOL Light: `iso_support_eps_finite` (line 45555). -/
theorem isoSupportEps_finite {V E₀ : Type*} (G : HolGraph V E₀)
    (H : HolGraph E2' (Set E2')) (E : Set (Set E2'))
    (h : isoSupportEpsPair G (H, E)) :
    {e ∈ E | ∃ z eps, 0 < z ∧ e = epsHyper eps z}.Finite :=
  h.2.2.1.subset fun _ hx => hx.1

/-- HOL Light: `iso_eps_support0` (line 45568). -/
theorem isoEpsSupport0 {V E₀ : Type*} (G : HolGraph V E₀)
    (H : HolGraph E2' (Set E2')) (E : Set (Set E2'))
    (h : isoSupportEpsPair G (H, E))
    (hcount : countIsoEpsPair (H, E) = 0) :
    IsGoodPlaneGraph H ∧ E.Finite ∧
    (∀ e ∈ H.edgeSet, e ⊆ ⋃₀ E) ∧
    (∀ v ∈ H.vertexSet, epsHyper true (v 0) ∈ E ∧ epsHyper false (v 1) ∈ E) ∧
    (∀ e ∈ E, ∃ z eps, e = epsHyper eps z) ∧
    (∀ z eps, epsHyper eps z ∈ E → ∃ j : ℕ, z = -↑j) := by
  obtain ⟨hgood, hfinE, hedge, hvert, hform, hint⟩ := h.2
  refine ⟨hgood, hfinE, hedge, hvert, hform,
    fun z eps hmem => ?_⟩
  by_cases hpos : 0 < z
  · exfalso
    have hfin' := isoSupportEps_finite G H E h
    have : 0 < countIsoEpsPair (H, E) :=
      (Set.ncard_pos (hs := hfin')).mpr
        ⟨_, hmem, z, eps, hpos, rfl⟩
    omega
  · exact hint z eps ⟨not_lt.mp hpos, hmem⟩
/-- When the isometric support count is positive, there exists a minimal positive offset `z`
    and direction `eps` such that `epsHyper eps z ∈ E` and no smaller positive `w` satisfies
    `epsHyper eps w ∈ E`. -/
theorem isoSupportEps_min {V E₀ : Type*} (G : HolGraph V E₀)
    (H : HolGraph E2' (Set E2')) (E : Set (Set E2'))
    (h : isoSupportEpsPair G (H, E))
    (hcount : 0 < countIsoEpsPair (H, E)) :
    ∃ z eps, 0 < z ∧ epsHyper eps z ∈ E ∧
      ∀ w, 0 < w → w < z → epsHyper eps w ∉ E := by
  have hfin' := isoSupportEps_finite G H E h
  have hne := (Set.ncard_pos (hs := hfin')).mp hcount
  obtain ⟨_, he₀E, z₀, eps₀, hz₀, rfl⟩ := hne
  have hpre : ((epsHyper eps₀) ⁻¹' E).Finite :=
    h.2.2.1.preimage (fun a _ b _ hab =>
      ((epsHyper_inj a b eps₀ eps₀).mp hab).2)
  have hZfin :
      {z : ℝ | 0 < z ∧ epsHyper eps₀ z ∈ E}.Finite :=
    hpre.subset fun z ⟨_, hz⟩ => hz
  let ZF := hZfin.toFinset
  have hZFne : ZF.Nonempty :=
    hZfin.toFinset_nonempty.mpr ⟨z₀, hz₀, he₀E⟩
  let z_min := ZF.min' hZFne
  have hz_mem :=
    hZfin.mem_toFinset.mp (Finset.min'_mem ZF hZFne)
  refine ⟨z_min, eps₀, hz_mem.1, hz_mem.2,
    fun w hw hwlt => ?_⟩
  intro hmem_w
  exact absurd (Finset.min'_le ZF w
    (hZfin.mem_toFinset.mpr ⟨hw, hmem_w⟩))
    (not_le.mpr hwlt)

/-! ## §X.4 Image preservation -/

/-- HOL Light: `graph_eps_scale_image` (line 45676). -/
theorem graphEpsScale_image (G : HolGraph E2' (Set E2'))
    (E : Set (Set E2')) (eps : Bool) {r : ℝ} (hr : 0 < r)
    (h : graphSupportEps G E) :
    graphSupportEps (planeGraphImage (epsScale_homeomorph eps hr) G h.1.1)
      (IMAGE2 (epsScale eps r) E) := by
  obtain ⟨hgood, hfinE, hedge, hvert, hform, hint⟩ := h
  set f := epsScale_homeomorph eps hr with hf_def
  have hfeq : ∀ x, f x = epsScale eps r x := by
    intro x; simp only [hf_def, epsScale_homeomorph, epsScale]; cases eps <;> rfl
  have hset_eq : ∀ S, f '' S = epsScale eps r '' S :=
    fun S => Set.image_congr fun x _ => hfeq x
  refine ⟨planeGraphImage_goodPlaneGraph f G hgood, hfinE.image _, ?_, ?_, ?_, ?_⟩
  · -- Edge subset
    rintro _ ⟨e, he, rfl⟩
    calc f '' e ⊆ f '' ⋃₀ E := Set.image_mono (hedge e he)
      _ = ⋃₀ ((f '' ·) '' E) := Set.image_sUnion
      _ = ⋃₀ IMAGE2 (epsScale eps r) E := by
          congr 1; ext S; constructor
          · rintro ⟨T, hT, rfl⟩; refine ⟨T, hT, ?_⟩; exact (hset_eq T).symm
          · rintro ⟨T, hT, rfl⟩; refine ⟨T, hT, ?_⟩; exact hset_eq T
  · -- Vertex hyperplanes
    rintro _ ⟨v', hv', rfl⟩
    obtain ⟨h0, h1⟩ := hvert v' hv'
    constructor
    · -- epsHyper true ((f v') 0) ∈ IMAGE2
      suffices hsuff : epsScale eps r '' epsHyper true (v' 0) =
          epsHyper true ((f v') 0) by
        exact hsuff ▸ Set.mem_image_of_mem _ h0
      conv_rhs => rw [show f v' = epsScale eps r v' from hfeq v']
      cases eps with
      | false =>
        have h1 := epsHyper_scale_perp false r (v' 0) hr
        simp only [Bool.not_false] at h1
        have h2 : (v' : Fin 2 → ℝ) 0 = ((epsScale false r v' : E2') : Fin 2 → ℝ) 0 := by
          simp [epsScale, uScale]; split_ifs <;> simp
        exact h1.trans (congrArg (epsHyper true) h2)
      | true =>
        have h1 := epsHyper_scale true r (v' 0) hr
        have h2 : (if (0 : ℝ) < (v' : Fin 2 → ℝ) 0 then r * (v' : Fin 2 → ℝ) 0
            else (v' : Fin 2 → ℝ) 0) =
            ((epsScale true r v' : E2') : Fin 2 → ℝ) 0 := by
          simp [epsScale, rScale]; split_ifs <;> simp
        exact h1.trans (congrArg (epsHyper true) h2)
    · -- epsHyper false ((f v') 1) ∈ IMAGE2
      suffices hsuff : epsScale eps r '' epsHyper false (v' 1) =
          epsHyper false ((f v') 1) by
        exact hsuff ▸ Set.mem_image_of_mem _ h1
      conv_rhs => rw [show f v' = epsScale eps r v' from hfeq v']
      cases eps with
      | false =>
        have h1 := epsHyper_scale false r (v' 1) hr
        have h2 : (if (0 : ℝ) < (v' : Fin 2 → ℝ) 1 then r * (v' : Fin 2 → ℝ) 1
            else (v' : Fin 2 → ℝ) 1) =
            ((epsScale false r v' : E2') : Fin 2 → ℝ) 1 := by
          simp [epsScale, uScale]; split_ifs <;> simp
        exact h1.trans (congrArg (epsHyper false) h2)
      | true =>
        have h1 := epsHyper_scale_perp true r (v' 1) hr
        simp only [Bool.not_true] at h1
        have h2 : (v' : Fin 2 → ℝ) 1 = ((epsScale true r v' : E2') : Fin 2 → ℝ) 1 := by
          simp [epsScale, rScale]; split_ifs <;> simp
        exact h1.trans (congrArg (epsHyper false) h2)
  · -- Form
    rintro _ ⟨S, hSE, rfl⟩
    obtain ⟨z, eps', rfl⟩ := hform S hSE
    simp only [] at *
    by_cases hee : eps' = eps
    · rw [hee, epsHyper_scale eps r z hr]
      exact ⟨_, _, rfl⟩
    · have hee' : eps' = !eps := by cases eps <;> cases eps' <;> simp_all
      rw [hee', epsHyper_scale_perp eps r z hr]
      exact ⟨_, _, rfl⟩
  · -- Nonpositive integer
    intro z eps' ⟨hle, hmem⟩
    simp only [IMAGE2, Set.mem_image] at hmem
    obtain ⟨S, hSE, hS_eq⟩ := hmem
    obtain ⟨z', eps'', rfl⟩ := hform S hSE
    by_cases hee : eps'' = eps
    · rw [hee, epsHyper_scale eps r z' hr] at hS_eq
      obtain ⟨rfl, heq⟩ := (epsHyper_inj _ _ _ _).mp hS_eq
      split_ifs at heq with hz'
      · linarith [mul_pos hr hz']
      · rw [← heq]; exact hint z' eps ⟨not_lt.mp hz', hee ▸ hSE⟩
    · have hee' : eps'' = !eps := by cases eps <;> cases eps'' <;> simp_all
      rw [hee', epsHyper_scale_perp eps r z' hr] at hS_eq
      obtain ⟨-, rfl⟩ := (epsHyper_inj _ _ _ _).mp hS_eq
      exact hint z' (!eps) ⟨hle, hee' ▸ hSE⟩

/-- HOL Light: `graph_eps_translate_image` (line 45791). -/
theorem graphEpsTranslate_image (G : HolGraph E2' (Set E2'))
    (E : Set (Set E2')) (eps : Bool) (r : ℝ)
    (hr_int : ∃ j : ℕ, -(↑j : ℝ) = r)
    (hr_gap : ∀ w, 0 < w → w < -r → epsHyper eps w ∉ E)
    (h : graphSupportEps G E) :
    graphSupportEps (planeGraphImage (epsTranslate_homeomorph eps r) G h.1.1)
      (IMAGE2 (epsTranslate eps r) E) := by
  obtain ⟨hgood, hfinE, hedge, hvert, hform, hint⟩ := h
  set f := epsTranslate_homeomorph eps r with hf_def
  have hfeq : ∀ x, f x = epsTranslate eps r x := by
    intro x; simp only [hf_def, epsTranslate_homeomorph, epsTranslate]; cases eps <;> rfl
  have hset_eq : ∀ S, f '' S = epsTranslate eps r '' S :=
    fun S => Set.image_congr fun x _ => hfeq x
  obtain ⟨j₀, hj₀⟩ := hr_int
  refine ⟨planeGraphImage_goodPlaneGraph f G hgood, hfinE.image _, ?_, ?_, ?_, ?_⟩
  · -- Edge subset
    rintro _ ⟨e, he, rfl⟩
    calc f '' e ⊆ f '' ⋃₀ E := Set.image_mono (hedge e he)
      _ = ⋃₀ ((f '' ·) '' E) := Set.image_sUnion
      _ = ⋃₀ IMAGE2 (epsTranslate eps r) E := by
          congr 1; ext S; constructor
          · rintro ⟨T, hT, rfl⟩; refine ⟨T, hT, ?_⟩; exact (hset_eq T).symm
          · rintro ⟨T, hT, rfl⟩; refine ⟨T, hT, ?_⟩; exact hset_eq T
  · -- Vertex hyperplanes
    rintro _ ⟨v', hv', rfl⟩
    obtain ⟨h0, h1⟩ := hvert v' hv'
    constructor
    · -- epsHyper true ((f v') 0) ∈ IMAGE2
      suffices hsuff : epsTranslate eps r '' epsHyper true (v' 0) =
          epsHyper true ((f v') 0) by
        exact hsuff ▸ Set.mem_image_of_mem _ h0
      conv_rhs => rw [show f v' = epsTranslate eps r v' from hfeq v']
      cases eps with
      | false =>
        have h1 := epsHyper_translate_perp false r (v' 0)
        simp only [Bool.not_false] at h1
        have h2 : (v' : Fin 2 → ℝ) 0 =
            ((epsTranslate false r v' : E2') : Fin 2 → ℝ) 0 := by
          simp [epsTranslate, vTranslate]
        exact h1.trans (congrArg (epsHyper true) h2)
      | true =>
        have h1 := epsHyper_translate true r (v' 0)
        have h2 : (v' : Fin 2 → ℝ) 0 + r =
            ((epsTranslate true r v' : E2') : Fin 2 → ℝ) 0 := by
          simp [epsTranslate, hTranslate]
        exact h1.trans (congrArg (epsHyper true) h2)
    · -- epsHyper false ((f v') 1) ∈ IMAGE2
      suffices hsuff : epsTranslate eps r '' epsHyper false (v' 1) =
          epsHyper false ((f v') 1) by
        exact hsuff ▸ Set.mem_image_of_mem _ h1
      conv_rhs => rw [show f v' = epsTranslate eps r v' from hfeq v']
      cases eps with
      | false =>
        have h1 := epsHyper_translate false r (v' 1)
        have h2 : (v' : Fin 2 → ℝ) 1 + r =
            ((epsTranslate false r v' : E2') : Fin 2 → ℝ) 1 := by
          simp [epsTranslate, vTranslate]
        exact h1.trans (congrArg (epsHyper false) h2)
      | true =>
        have h1 := epsHyper_translate_perp true r (v' 1)
        simp only [Bool.not_true] at h1
        have h2 : (v' : Fin 2 → ℝ) 1 =
            ((epsTranslate true r v' : E2') : Fin 2 → ℝ) 1 := by
          simp [epsTranslate, hTranslate]
        exact h1.trans (congrArg (epsHyper false) h2)
  · -- Form
    rintro _ ⟨S, hSE, rfl⟩
    obtain ⟨z, eps', rfl⟩ := hform S hSE
    simp only [] at *
    by_cases hee : eps' = eps
    · rw [hee, epsHyper_translate eps r z]
      exact ⟨_, _, rfl⟩
    · have hee' : eps' = !eps := by cases eps <;> cases eps' <;> simp_all
      rw [hee', epsHyper_translate_perp eps r z]
      exact ⟨_, _, rfl⟩
  · -- Nonpositive integer
    intro z eps' ⟨hle, hmem⟩
    simp only [IMAGE2, Set.mem_image] at hmem
    obtain ⟨S, hSE, hS_eq⟩ := hmem
    obtain ⟨z', eps'', rfl⟩ := hform S hSE
    by_cases hee : eps'' = eps
    · rw [hee, epsHyper_translate eps r z'] at hS_eq
      obtain ⟨rfl, heq⟩ := (epsHyper_inj _ _ _ _).mp hS_eq
      -- heq : z' + r = z
      by_cases hz0 : z = 0
      · exact ⟨0, by simp [hz0]⟩
      · -- z < 0 (z ≤ 0 and z ≠ 0)
        have hz_neg : z < 0 := lt_of_le_of_ne hle hz0
        have hz' : z' = z + ↑j₀ := by linarith [hj₀]
        have hz'_le : z' ≤ 0 := by
          by_contra hz'_pos
          push Not at hz'_pos
          have hz'_lt : z' < -r := by linarith [hj₀]
          exact hr_gap z' hz'_pos (by linarith [hj₀]) (hee ▸ hSE)
        obtain ⟨j₁, hj₁⟩ := hint z' eps ⟨hz'_le, hee ▸ hSE⟩
        exact ⟨j₁ + j₀, by push_cast; linarith [hj₁, hj₀]⟩
    · have hee' : eps'' = !eps := by cases eps <;> cases eps'' <;> simp_all
      rw [hee', epsHyper_translate_perp eps r z'] at hS_eq
      obtain ⟨-, rfl⟩ := (epsHyper_inj _ _ _ _).mp hS_eq
      exact hint z' (!eps) ⟨hle, hee' ▸ hSE⟩

/-! ## §X.5 Count invariance -/

/-- HOL Light: `count_iso_scale` (line 45945). -/
theorem countIso_scale (G : HolGraph E2' (Set E2'))
    (E : Set (Set E2')) (eps : Bool) {r : ℝ} (hr : 0 < r)
    (h : graphSupportEps G E) :
    countIsoEpsPair (G, E) =
      countIsoEpsPair (planeGraphImage (epsScale_homeomorph eps hr) G h.1.1,
        IMAGE2 (epsScale eps r) E) := by
  simp only [countIsoEpsPair, IMAGE2]
  have hinj : Function.Injective
      (epsScale eps r '' · : Set E2' → Set E2') := by
    intro A B hab
    have : Function.Injective (epsScale eps r) := by
      cases eps
      · exact (uScale_bijective hr).injective
      · exact (rScale_bijective hr).injective
    exact this.image_injective hab
  rw [show {e ∈ (epsScale eps r '' ·) '' E |
        ∃ z eps, 0 < z ∧ e = epsHyper eps z} =
      (epsScale eps r '' ·) ''
        {e ∈ E | ∃ z eps, 0 < z ∧ e = epsHyper eps z}
      from ?_]
  · exact (Set.ncard_image_of_injective _
      hinj).symm
  · ext e
    simp only [Set.mem_sep_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨S, hSE, rfl⟩, z, eps', hz, heq⟩
      obtain ⟨z', eps'', rfl⟩ :=
        h.2.2.2.2.1 S hSE
      refine ⟨epsHyper eps'' z', ⟨hSE, ?_⟩, rfl⟩
      by_cases hee : eps'' = eps
      · rw [hee,
          epsHyper_scale eps r z' hr] at heq
        obtain ⟨rfl, heq'⟩ :=
          (epsHyper_inj _ _ _ _).mp heq
        split_ifs at heq' with hz'
        · exact ⟨z', eps,  hz',
            by rw [hee]⟩
        · rw [← heq'] at hz; linarith
      · have hee' : eps'' = !eps := by
          cases eps <;> cases eps'' <;> simp_all
        rw [hee',
          epsHyper_scale_perp eps r z' hr]
          at heq
        have hinj :=
          (epsHyper_inj z' z (!eps) eps').mp heq
        rw [hee', hinj.2]
        exact ⟨z, !eps, hz, rfl⟩
    · rintro ⟨S, ⟨hSE, z', eps', hz', rfl⟩, rfl⟩
      refine ⟨Set.mem_image_of_mem _ hSE, ?_⟩
      by_cases hee : eps' = eps
      · rw [hee, epsHyper_scale eps r z' hr]
        exact ⟨r * z', eps,
          mul_pos hr hz', by simp [hz']⟩
      · have hee' : eps' = !eps := by
          cases eps <;> cases eps' <;> simp_all
        rw [hee',
          epsHyper_scale_perp eps r z' hr]
        exact ⟨z', !eps, hz', rfl⟩

/-- HOL Light: `count_iso_translate` (line 46033). -/
theorem countIso_translate (G : HolGraph E2' (Set E2'))
    (E : Set (Set E2')) (eps : Bool)
    (h : graphSupportEps G E)
    (hgap : ∀ w, 0 < w → w < 1 → epsHyper eps w ∉ E)
    (hmem : epsHyper eps 1 ∈ E) :
    countIsoEpsPair (G, E) =
      countIsoEpsPair (planeGraphImage (epsTranslate_homeomorph eps (-1)) G h.1.1,
        IMAGE2 (epsTranslate eps (-1)) E) + 1 := by
  simp only [countIsoEpsPair]
  set A := {e ∈ E | ∃ z eps', 0 < z ∧ e = epsHyper eps' z}
  set im := (epsTranslate eps (-1) '' · : Set E2' → Set E2')
  set B := {e ∈ im '' E | ∃ z eps', 0 < z ∧ e = epsHyper eps' z}
  -- Injectivity of im
  have hinj : Function.Injective im := by
    intro a b hab
    have : Function.Injective (epsTranslate eps (-1)) := by
      cases eps
      · exact (vTranslate_bijective (-1)).injective
      · exact (hTranslate_bijective (-1)).injective
    exact this.image_injective hab
  -- Key facts
  have hfinA : A.Finite := h.2.1.subset fun _ hx => hx.1
  have hmemA : epsHyper eps 1 ∈ A := ⟨hmem, 1, eps, one_pos, rfl⟩
  -- ncard A = ncard (A \ {epsHyper eps 1}) + 1
  have hncard_split : (A \ {epsHyper eps 1}).ncard + 1 = A.ncard :=
    Set.ncard_diff_singleton_add_one hmemA hfinA
  -- B = im '' (A \ {epsHyper eps 1})
  have hB_eq : B = im '' (A \ {epsHyper eps 1}) := by
    ext e; simp only [B, A, im, Set.mem_sep_iff, Set.mem_image,
      Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · -- e ∈ B → e ∈ im '' (A \ {epsHyper eps 1})
      rintro ⟨⟨S, hSE, rfl⟩, z₁, eps₁, hz₁, heq⟩
      obtain ⟨z', eps'', rfl⟩ := h.2.2.2.2.1 S hSE
      refine ⟨epsHyper eps'' z', ⟨⟨hSE, ?_⟩, ?_⟩, rfl⟩
      · -- epsHyper eps'' z' ∈ A (i.e., ∃ positive param)
        by_cases hee : eps'' = eps
        · -- same direction: image is epsHyper eps (z' - 1)
          rw [hee, epsHyper_translate eps (-1) z'] at heq
          obtain ⟨rfl, heq'⟩ := (epsHyper_inj _ _ _ _).mp heq
          have : z' + -1 > 0 := by linarith
          exact ⟨z', eps, by linarith, by rw [hee]⟩
        · -- perp direction: image is epsHyper (!eps) z'
          have hee' : eps'' = !eps := by
            cases eps <;> cases eps'' <;> simp_all
          rw [hee', epsHyper_translate_perp eps (-1) z'] at heq
          obtain ⟨-, rfl⟩ := (epsHyper_inj _ _ _ _).mp heq
          exact ⟨z', !eps, by linarith, by rw [hee']⟩
      · -- epsHyper eps'' z' ≠ epsHyper eps 1
        by_cases hee : eps'' = eps
        · rw [hee, epsHyper_translate eps (-1) z'] at heq
          obtain ⟨rfl, heq'⟩ := (epsHyper_inj _ _ _ _).mp heq
          rw [epsHyper_inj]; intro ⟨_, h1⟩
          linarith
        · intro h_eq
          obtain ⟨h_eps, _⟩ := (epsHyper_inj _ _ _ _).mp h_eq
          exact hee (h_eps.trans rfl)
    · -- e ∈ im '' (A \ {epsHyper eps 1}) → e ∈ B
      rintro ⟨S, ⟨⟨hSE, z', eps', hz', rfl⟩, hne⟩, rfl⟩
      refine ⟨Set.mem_image_of_mem _ hSE, ?_⟩
      by_cases hee : eps' = eps
      · -- same direction
        rw [hee, epsHyper_translate eps (-1) z']
        have hne' : z' ≠ 1 := by
          intro h_eq; apply hne; rw [hee, h_eq]
        have hz'_ge : z' ≥ 1 := by
          by_contra h_lt
          push Not at h_lt
          exact (hgap z' hz' (by linarith)) (hee ▸ hSE)
        have hz'_gt : z' > 1 := lt_of_le_of_ne hz'_ge (Ne.symm hne')
        exact ⟨z' + -1, eps, by linarith, rfl⟩
      · -- perp direction
        have hee' : eps' = !eps := by
          cases eps <;> cases eps' <;> simp_all
        simp only [hee', epsHyper_translate_perp eps (-1) z']
        exact ⟨z', !eps, hz', rfl⟩
  rw [show {e | e ∈ IMAGE2 (epsTranslate eps (-1)) E ∧
        ∃ z eps', 0 < z ∧ e = epsHyper eps' z} = B from by
      ext e; simp only [Set.mem_setOf_eq, B, im, IMAGE2]]
  rw [hB_eq, Set.ncard_image_of_injective _ hinj]
  omega

/-! ## §X.6 Integer model existence -/

/-- HOL Light: `iso_support_min_int` (line 46161). -/
theorem isoSupport_min_int {V E₀ : Type*} (G : HolGraph V E₀)
    (H : HolGraph E2' (Set E2')) (E : Set (Set E2'))
    (h : isoSupportEpsPair G (H, E))
    (hcount : 0 < countIsoEpsPair (H, E)) :
    ∃ H' E', isoSupportEpsPair G (H', E') ∧
      countIsoEpsPair (H', E') = countIsoEpsPair (H, E) ∧
      ∃ eps, epsHyper eps 1 ∈ E' ∧
        ∀ w, 0 < w → w < 1 → epsHyper eps w ∉ E' := by
  obtain ⟨z, eps, hz, hmemE, hmin⟩ :=
    isoSupportEps_min G H E h hcount
  have hz_inv : 0 < z⁻¹ := inv_pos.mpr hz
  let H' := planeGraphImage
    (epsScale_homeomorph eps hz_inv) H h.2.1.1
  let E'' := IMAGE2 (epsScale eps z⁻¹) E
  have hsupp' :=
    graphEpsScale_image H E eps hz_inv h.2
  have hcount' :=
    (countIso_scale H E eps hz_inv h.2).symm
  have hiso' := graphIsomorphic_trans h.1
    (planeGraphImage_iso
      (epsScale_homeomorph eps hz_inv) H h.2.1.1)
  refine ⟨H', E'', ⟨hiso', hsupp'⟩, hcount',
    eps, ?_, fun w hw hwlt => ?_⟩
  · -- epsHyper eps 1 ∈ E''
    have key : epsScale eps z⁻¹ '' epsHyper eps z =
        epsHyper eps 1 := by
      rw [epsHyper_scale eps z⁻¹ z hz_inv]
      simp [hz, inv_mul_cancel₀ hz.ne']
    exact key ▸
      Set.mem_image_of_mem
        (epsScale eps z⁻¹ '' ·) hmemE
  · -- minimality
    intro hmemw
    simp only [E'', IMAGE2, Set.mem_image] at hmemw
    obtain ⟨S, hSE, hS_eq⟩ := hmemw
    obtain ⟨z', eps', rfl⟩ :=
      h.2.2.2.2.2.1 S hSE
    by_cases hee : eps' = eps
    · -- eps' = eps case
      rw [hee, epsHyper_scale eps z⁻¹ z' hz_inv]
        at hS_eq
      rw [hee] at hSE
      have hinj :=
        ((epsHyper_inj _ w eps eps).mp hS_eq).2
      split_ifs at hinj with hz'
      · have hzw : z' = z * w := by
          calc z' = z * (z⁻¹ * z') := by
                rw [← mul_assoc,
                  mul_inv_cancel₀ hz.ne', one_mul]
            _ = z * w := by rw [hinj]
        exact absurd (hzw ▸ hSE) (hmin (z * w)
          (mul_pos hz hw) (by nlinarith))
      · linarith
    · -- eps' ≠ eps, so eps' = !eps
      have heps : eps' = !eps := by
        cases eps <;> cases eps' <;> simp_all
      rw [heps,
        epsHyper_scale_perp eps z⁻¹ z' hz_inv]
        at hS_eq
      exact absurd hS_eq
        (Ne.symm (epsHyper_ne w z' eps))

/-- HOL Light: `iso_int_model_lemma` (line 46255). -/
theorem iso_int_model_lemma {V E₀ : Type*} (G : HolGraph V E₀)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    ∃ H E, isoSupportEpsPair G (H, E) ∧ countIsoEpsPair (H, E) = 0 := by
  obtain ⟨p, hp⟩ :=
    isoSupportEpsPair_nonempty G hplanar hfin_e hfin_v hne hdeg
  obtain ⟨H₀, E₀⟩ := p
  suffices ∀ n (H : HolGraph E2' (Set E2'))
      (E : Set (Set E2')),
      isoSupportEpsPair G (H, E) →
      countIsoEpsPair (H, E) = n →
      ∃ H' E', isoSupportEpsPair G (H', E') ∧
        countIsoEpsPair (H', E') = 0 from
    this _ H₀ E₀ hp rfl
  intro n
  induction n with
  | zero =>
    intro H E hiso hc; exact ⟨H, E, hiso, hc⟩
  | succ n ih =>
    intro H E hiso hc
    have hcount : 0 < countIsoEpsPair (H, E) := by
      omega
    obtain ⟨H₁, E₁, hiso₁, hcount₁, eps, hmem₁,
        hgap₁⟩ :=
      isoSupport_min_int G H E hiso hcount
    have hsupp₁ := hiso₁.2
    have htr := graphEpsTranslate_image H₁ E₁ eps
      (-1) ⟨1, by norm_num⟩ (by simpa using hgap₁)
      hsupp₁
    have hcount_tr := countIso_translate H₁ E₁ eps
      hsupp₁ hgap₁ hmem₁
    set H₂ := planeGraphImage
      (epsTranslate_homeomorph eps (-1)) H₁
      hsupp₁.1.1
    set E₂ := IMAGE2 (epsTranslate eps (-1)) E₁
    have hiso₂ : isoSupportEpsPair G (H₂, E₂) :=
      ⟨graphIsomorphic_trans hiso₁.1
        (planeGraphImage_iso _ H₁ hsupp₁.1.1), htr⟩
    have hc₂ : countIsoEpsPair (H₂, E₂) = n := by
      omega
    exact ih H₂ E₂ hiso₂ hc₂

/-- Any planar graph with bounded degree can be realized with integer-coordinate
    hyperplane support. This is the main result of Section X.
    HOL Light: `graph_int_model` (line 46313). -/
theorem graph_int_model {V E₀ : Type*} (G : HolGraph V E₀)
    (hplanar : IsPlanarGraph G)
    (hfin_e : G.edgeSet.Finite) (hfin_v : G.vertexSet.Finite)
    (hne : G.edgeSet.Nonempty)
    (hdeg : ∀ v, (G.edgeAround v).ncard ≤ 4) :
    ∃ (H : HolGraph E2' (Set E2')) (E : Set (Set E2')),
      GraphIsomorphic G H ∧ IsGoodPlaneGraph H ∧ E.Finite ∧
      (∀ e ∈ H.edgeSet, e ⊆ ⋃₀ E) ∧
      (∀ v ∈ H.vertexSet,
        epsHyper true (v 0) ∈ E ∧ epsHyper false (v 1) ∈ E) ∧
      (∀ e ∈ E, ∃ z eps, e = epsHyper eps z) ∧
      (∀ z eps, epsHyper eps z ∈ E → ∃ j : ℕ, z = -↑j) := by
  obtain ⟨H, E, hiso, hcount⟩ :=
    iso_int_model_lemma G hplanar hfin_e hfin_v hne hdeg
  obtain ⟨hgood, hfin, hedge, hvert, hform, hint⟩ :=
    isoEpsSupport0 G H E hiso hcount
  exact ⟨H, E, hiso.1, hgood, hfin, hedge, hvert,
    hform, hint⟩

end JordanCurveTheorem
