import References.Pommerenke1992.Ch08.S06_LacunarySeries
import References.LehtoVirtanen1973.Ch03.S04_ModuleArcFamilies
import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain

/-!
# Pommerenke 1992, Ch. 9 §9.2 The Module of a Curve Family

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 9 *Curve Families and Capacity*, §9.2; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 449–748.

* Definition (curve family in the Borel set `B`, P2 l. 451: "open, halfopen or closed arcs or curves in `B`"; used in
  Propositions 9.1–9.3) — `IsCurveFamilyIn`
* Definition (admissible function, (9.2.1), P2 l. 451–457; used in every module argument, P2 l. 1256, 1609, 3378,
  3523, 3637) — exists: `LehtoVirtanen1973.IsAdmissibleFor` `LehtoVirtanen1973.rhoLengthH` (a non-negative Borel
  function of the plane with values in [0, ∞] whose ρ-length, the integral against the linear measure over the point
  set of the member, is at least 1; LV imposes the inequality only on the locally rectifiable members, which gives the
  same module: the remaining Jordan arcs and curves form a family of module zero,
  LehtoVirtanen1973.arcFamilyModule_nonrectifiable, and a module-zero part does not change a module; ρ is defined on
  all of ℂ, and ρ = 0 off B changes nothing)
* Definition (the module `mod Γ`, (9.2.2), P2 l. 459–465; cited "(9.2.2)" at P2 l. 1266, 3637) — exists:
  `LehtoVirtanen1973.arcFamilyModule` (LV III (4.3): the infimum of the area integral of ρ² over the admissible ρ,
  values in [0, ∞], no normalizing factor; the book's area over B equals the area over ℂ for the admissible ρ that
  vanish off B, and these realize the infimum)
* Example 9.1 ((9.2.3), (9.2.5); U+, the example's claim (9.2.5) is cited as a result at P2 l. 3256, 3317, 3378 and in
  Exercise 9.2.2) — `example9_1`
* Example 9.2 ((9.2.6), (9.2.7); U+, (9.2.7) is cited as a result at P2 l. 657, 671, 1304, 1334, 3274 and in Exercise
  9.2.2) — `example9_2_a`, `example9_2_b`
* Proposition 9.1 ((9.2.8); cited at P2 l. 671, 1266, 1493, 3317, 3378, "conformally invariant" at P2 l. 3256) —
  `prop9_1`
* Proposition 9.2, first sentence (monotonicity; cited at P2 l. 1274, 1304, 1334, 1493, 3317, "monotone" at P2
  l. 3256) — `prop9_2_a`
* Proposition 9.2, (9.2.11) (subadditivity) — exists: `LehtoVirtanen1973.eq3_4_5` (LV III (4.5) for families indexed
  by ℕ; a finite family is padded with empty families, of module zero)
* Proposition 9.2, last sentence (`mod Γ₀ = 0 ⇒ mod(Γ ∪ Γ₀) = mod Γ`) — exists: `LehtoVirtanen1973.eq3_4_6` (LV III
  (4.6), the same statement)
* Proposition 9.3 ((9.2.12), (9.2.13); cited at P2 l. 624, 671, 1334, 3236, 3535) — `prop9_3_a`, `prop9_3_b`
* Proposition 9.4 (cited at P2 l. 3272 and in Exercises 9.2.1, 9.2.2) — `prop9_4`
* Proposition 9.5 (Teichmüller module theorem, Tei38; (9.2.14), (9.2.15); cited at P2 l. 3280) — `prop9_5`
* Formula (9.2.18) (Grötzsch's estimate, quoted from LeVi73, pp. 53–61; U+, named in the index, "Grötzsch module
  theorem 202") — `eq9_2_18`
* Formula (9.2.19) (Teichmüller's estimate, quoted from LeVi73; U+, cited "Teichmüller's estimate (9.2.19)" at P2
  l. 3553) — `eq9_2_19`

Helpers (Pommerenke's families written as sets): `joiningArcFamily` (the curves in `D` that connect `A` and `B`),
`separatingCurveFamily` (the Jordan curves in `D` that separate `A` and `B`).

Not items (DESIGN §3): "the integral is the area of `B` with respect to `ρ(z)|dz|`" and "if `B ⊆ B'` then `Γ` is
also a curve family in `B'` with the same module" (P2 l. 465; a remark, built into the modelling: the densities live
on `ℂ`); (9.2.4) and the Schwarz-inequality argument (steps of Example 9.1); the image family `f(Γ)` (P2 l. 514; a
notation, written `(fun C => OnePoint.map f '' C) '' Γ`); (9.2.9), (9.2.10) (the proof of Proposition 9.1) and "The
module is monotone and subadditive" (P2 l. 536, an announcement); "`1/mod Γ` is called the extremal length" (P2
l. 576; never used afterwards, every later statement uses the module; it would be
`LehtoVirtanen1973.arcFamilyExtremalLength`); Figs. 9.2–9.4 and the proofs of Propositions 9.2–9.4; (9.2.16)
(U−: "It follows from (7) and (12)"; not cited); (9.2.17) and the proof of Proposition 9.5 (area theorem, Schwarz's
inequality); "There are also estimates in the opposite direction due to Grötzsch and Teichmüller" (P2 l. 703, the
introduction of (9.2.18), (9.2.19)); Exercises 9.2.1–9.2.5.

**Conventions.** As in §9.1. A curve family is a set of point sets of `ℂ̂` (`Set (Set ExtPlane)`), the members being
Jordan arcs (open, half-open or closed, `LehtoVirtanen1973.IsJordanArc`) or Jordan curves (`IsJordanCurve`), and
`mod Γ` is `LehtoVirtanen1973.arcFamilyModule Γ` in `[0, ∞]` (leader ruling QD2). The book's curves that connect two
sets are the closed Jordan arcs with one end point in each set and all other points in the domain
(`joiningArcFamily`, the form of `LehtoVirtanen1973.module_quad_joining_arcs`); the open or half-open connecting
curves of the book give the same modules, since each of them contains, or is the interior of, such an arc. The image
of a family under a map `f : ℂ → ℂ` is `(fun C => OnePoint.map f '' C) '' Γ`. The inverse `1/mod` is the inverse of
`[0, ∞]` (`1/0 = ∞`, the book's convention in (9.2.13), P2 l. 585). The families of Proposition 9.3 are indexed by a
countable type, so that finite and infinite families are both covered.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsJordanCurve)
open LehtoVirtanen1973 (arcFamilyModule IsJordanArc IsArcFromTo Separates IsRingDomain)

/-- **Definition** (§9.2, P2 l. 451). `Γ` is a curve family in the Borel set `B ⊆ ℂ`: it consists of open, half-open
or closed arcs or curves in `B`.
Modelling: a family of point sets of `ℂ̂` whose members are Jordan arcs (`LehtoVirtanen1973.IsJordanArc`, the images
of open, half-open or closed intervals) or Jordan curves, all contained in `B` (so in `ℂ`); the Borel measurability
of `B` is a separate hypothesis where the book states it. -/
def IsCurveFamilyIn (Γ : Set (Set ExtPlane)) (B : Set ℂ) : Prop :=
  ∀ C ∈ Γ, (IsJordanArc C ∨ IsJordanCurve C) ∧ C ⊆ toExt B

/-- The family of all curves in `D` that connect `A` and `B` (helper, §9.2; Examples 9.1, 9.2, Proposition 9.4 and
`Γ_E(r)` of §9.4): the closed Jordan arcs `C` from a point `p ∈ A` to a point `q ∈ B` whose other points lie in `D`.
Modelling: the form of `LehtoVirtanen1973.module_quad_joining_arcs`; see the file header for the book's open and
half-open connecting curves. -/
def joiningArcFamily (D A B : Set ExtPlane) : Set (Set ExtPlane) :=
  {C | ∃ p ∈ A, ∃ q ∈ B, IsArcFromTo C p q ∧ C \ {p, q} ⊆ D}

/-- The family of all Jordan curves in `D` that separate `A` and `B` (helper, §9.2; Example 9.2, Proposition 9.5,
(9.2.18), (9.2.19)): `A` and `B` lie in different components of the complement of the curve (LV's `Separates`, the
form of `LehtoVirtanen1973.module_ring_separating_curves`). -/
def separatingCurveFamily (D A B : Set ExtPlane) : Set (Set ExtPlane) :=
  {C | IsJordanCurve C ∧ C ⊆ D ∧ Separates C A B}

/-- A homeomorphism of `ℂ̂` maps Jordan curves to Jordan curves (helper for Proposition 9.2). -/
theorem pom92_isJordanCurve_image (e : ExtPlane ≃ₜ ExtPlane) {C : Set ExtPlane} (hC : IsJordanCurve C) :
    IsJordanCurve (e '' C) := by
  obtain ⟨g, hgc, hgi, rfl⟩ := hC
  exact ⟨e ∘ g, e.continuous.comp hgc, e.injective.comp hgi, range_comp e g⟩

/-- A Jordan arc contains no Jordan curve (helper for Proposition 9.2): read through the parametrization of the arc, a
Jordan curve inside it would be a continuous injective map of the circle into `ℝ`. -/
theorem pom92_not_isJordanCurve_subset_isJordanArc {K A : Set ExtPlane} (hK : IsJordanCurve K)
    (hA : IsJordanArc A) (hKA : K ⊆ A) : False := by
  obtain ⟨g, hgc, hgi, rfl⟩ := hK
  obtain ⟨I, -, -, γ, hγ, rfl⟩ := hA
  have hmem : ∀ z, g z ∈ range (I.domRestrict γ) := fun z => by
    obtain ⟨t, ht, htz⟩ := hKA (mem_range_self z)
    exact ⟨⟨t, ht⟩, htz⟩
  refine LiZhongQC.wd_j_not_injective_circle_real
    (f := fun z => ((hγ.toHomeomorph.symm ⟨g z, hmem z⟩ : I) : ℝ)) ?_ ?_
  · exact continuous_subtype_val.comp (hγ.toHomeomorph.symm.continuous.comp (hgc.subtype_mk hmem))
  · intro z w hzw
    apply hgi
    have h := congrArg hγ.toHomeomorph (Subtype.ext hzw)
    simp only [Homeomorph.apply_symm_apply, Subtype.mk.injEq] at h
    exact h

/-- A Jordan arc or curve contained in a locally rectifiable arc or curve of `ℂ̂` is locally rectifiable (helper for
Propositions 9.2 and 9.3). Arcs: `LehtoVirtanen1973.lv34_isLocRectifiableExt_of_subset_arc`. A Jordan curve `C'`
cannot lie in a Jordan arc (`pom92_not_isJordanCurve_subset_isJordanArc`), so the Möbius image of `C` is a
rectifiable Jordan curve of the finite plane, and every Jordan arc in the image of `C'` is a Jordan arc in it. -/
theorem pom92_isLocRectifiableExt_of_subset {C C' : Set ExtPlane} (hC' : IsJordanArc C' ∨ IsJordanCurve C')
    (hsub : C' ⊆ C) (hC : LehtoVirtanen1973.IsLocRectifiableExt C) : LehtoVirtanen1973.IsLocRectifiableExt C' := by
  rcases hC' with harc | hcurve
  · exact LehtoVirtanen1973.lv34_isLocRectifiableExt_of_subset_arc hC harc hsub
  obtain ⟨T, ⟨a, b, c, d, had, rfl⟩, C'', hTC, hC''⟩ := hC
  have hsub' : LiZhongQC.mobiusExt a b c d '' C' ⊆ toExt C'' := by
    rw [← hTC]
    exact image_mono hsub
  have heq : toExt (References.finitePart (LiZhongQC.mobiusExt a b c d '' C')) =
      LiZhongQC.mobiusExt a b c d '' C' :=
    image_preimage_eq_of_subset (hsub'.trans (image_subset_range _ _))
  have hfun : ⇑(LiZhongQC.mobiusHomeomorph a b c d had) = LiZhongQC.mobiusExt a b c d :=
    funext (LiZhongQC.mobiusHomeomorph_apply had)
  have hcurve' : IsJordanCurve (LiZhongQC.mobiusExt a b c d '' C') := by
    rw [← hfun]
    exact pom92_isJordanCurve_image _ hcurve
  rcases hC'' with ⟨harc, -⟩ | ⟨-, hrc⟩
  · exact (pom92_not_isJordanCurve_subset_isJordanArc hcurve' harc hsub').elim
  refine ⟨LiZhongQC.mobiusExt a b c d, ⟨a, b, c, d, had, rfl⟩, _, heq.symm,
    Or.inr ⟨?_, fun C₃ h₃ harc₃ => hrc C₃ ?_ harc₃⟩⟩
  · rw [heq]
    exact hcurve'
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := hsub' (show ((z : ExtPlane)) ∈ LiZhongQC.mobiusExt a b c d '' C' from h₃ hz)
    rwa [← OnePoint.coe_injective hyz]

/-- A family each of whose members contains a member of `Γ'` has module at most `mod Γ'` (helper for Propositions
9.2 and 9.3): an admissible `ρ` for `Γ'` is admissible for `Γ`. -/
theorem pom92_module_le_of_forall_subset {Γ Γ' : Set (Set ExtPlane)}
    (hΓ' : ∀ C' ∈ Γ', IsJordanArc C' ∨ IsJordanCurve C') (h : ∀ C ∈ Γ, ∃ C' ∈ Γ', C' ⊆ C) :
    arcFamilyModule Γ ≤ arcFamilyModule Γ' := by
  refine LehtoVirtanen1973.lv34_le_module fun ρ hρ => LehtoVirtanen1973.lv34_module_le ⟨hρ.1, fun C hC hr => ?_⟩
  obtain ⟨C', hC', hsub⟩ := h C hC
  exact (hρ.2 C' hC' (pom92_isLocRectifiableExt_of_subset (hΓ' C' hC') hsub hr)).trans
    (LehtoVirtanen1973.lv34_rhoLengthH_mono hsub)

/-- Restricting `ρ` to a Borel set `B` that contains `C` does not change the `ρ`-length of `C` (helper for
Proposition 9.3). -/
theorem pom92_rhoLengthH_indicator {B : Set ℂ} (hB : MeasurableSet B) {C : Set ExtPlane} (hC : C ⊆ toExt B)
    (ρ : ℂ → ℝ≥0∞) : LehtoVirtanen1973.rhoLengthH (B.indicator ρ) C = LehtoVirtanen1973.rhoLengthH ρ C := by
  have hCB : References.finitePart C ⊆ B := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hC (show ((z : ExtPlane)) ∈ C from hz)
    rwa [← OnePoint.coe_injective hyz]
  unfold LehtoVirtanen1973.rhoLengthH
  rw [lintegral_indicator hB, Measure.restrict_restrict hB, inter_eq_self_of_subset_right hCB]

/-- The series rule for finitely many indices (helper for Proposition 9.3, (9.2.13)). For admissible `ρ_k` of finite
positive areas `A_k` (`k ∈ G`), the density `Σ_k c_k 1_{B_k} ρ_k` with the weights `c_k = A_k⁻¹ / Σ_j A_j⁻¹` is
admissible for `Γ`, and, the `B_k` being disjoint, its area is at most `Σ_k c_k² A_k = (Σ_k A_k⁻¹)⁻¹`. -/
theorem pom92_series_finset {ι : Type*} {B : ι → Set ℂ} (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) {Γs : ι → Set (Set ExtPlane)}
    (hΓs : ∀ k, IsCurveFamilyIn (Γs k) (B k)) {Γ : Set (Set ExtPlane)}
    (hcont : ∀ C ∈ Γ, ∀ k, ∃ C' ∈ Γs k, C' ⊆ C) (G : Finset ι) {ρ : ι → ℂ → ℝ≥0∞}
    (hρ : ∀ k ∈ G, LehtoVirtanen1973.IsAdmissibleFor (Γs k) (ρ k))
    (hpos : ∀ k ∈ G, LiZhongQC.rhoArea (ρ k) univ ≠ 0) (hfin : ∀ k ∈ G, LiZhongQC.rhoArea (ρ k) univ ≠ ⊤) :
    arcFamilyModule Γ * ∑ k ∈ G, (LiZhongQC.rhoArea (ρ k) univ)⁻¹ ≤ 1 := by
  rcases G.eq_empty_or_nonempty with hG | ⟨j, hj⟩
  · rw [hG, Finset.sum_empty, mul_zero]
    exact zero_le_one
  set A : ι → ℝ≥0∞ := fun k => LiZhongQC.rhoArea (ρ k) univ with hA
  set S := ∑ k ∈ G, (A k)⁻¹ with hS
  have hS0 : S ≠ 0 := (lt_of_lt_of_le (ENNReal.inv_pos.2 (hfin j hj))
    (Finset.single_le_sum (f := fun k => (A k)⁻¹) (fun k _ => zero_le) hj)).ne'
  have hStop : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun k hk => ENNReal.inv_ne_top.2 (hpos k hk)
  set σ : ι → ℂ → ℝ≥0∞ := fun k => (B k).indicator (ρ k) with hσ
  have hσm : ∀ k ∈ G, Measurable (σ k) := fun k hk => (hρ k hk).1.indicator (hB k)
  set c : ι → ℝ≥0∞ := fun k => (A k)⁻¹ * S⁻¹ with hc
  -- the density `Σ_k c_k σ_k` is admissible for `Γ`
  have hadm : LehtoVirtanen1973.IsAdmissibleFor Γ fun z => ∑ k ∈ G, c k * σ k z := by
    refine ⟨Finset.measurable_sum G fun k hk => measurable_const.mul (hσm k hk), fun C hC hr => ?_⟩
    have h1 : ∀ k ∈ G, 1 ≤ LehtoVirtanen1973.rhoLengthH (σ k) C := fun k hk => by
      obtain ⟨C', hC', hsub⟩ := hcont C hC k
      calc 1 ≤ LehtoVirtanen1973.rhoLengthH (ρ k) C' :=
            (hρ k hk).2 C' hC' (pom92_isLocRectifiableExt_of_subset (hΓs k C' hC').1 hsub hr)
        _ = LehtoVirtanen1973.rhoLengthH (σ k) C' :=
            (pom92_rhoLengthH_indicator (hB k) (hΓs k C' hC').2 _).symm
        _ ≤ LehtoVirtanen1973.rhoLengthH (σ k) C := LehtoVirtanen1973.lv34_rhoLengthH_mono hsub
    calc (1 : ℝ≥0∞) = ∑ k ∈ G, c k := by
          show 1 = ∑ k ∈ G, (A k)⁻¹ * S⁻¹
          rw [← Finset.sum_mul, ← hS, ENNReal.mul_inv_cancel hS0 hStop]
      _ ≤ ∑ k ∈ G, c k * LehtoVirtanen1973.rhoLengthH (σ k) C :=
          Finset.sum_le_sum fun k hk => le_mul_of_one_le_right (zero_le) (h1 k hk)
      _ = LehtoVirtanen1973.rhoLengthH (fun z => ∑ k ∈ G, c k * σ k z) C := by
          unfold LehtoVirtanen1973.rhoLengthH
          beta_reduce
          rw [lintegral_finsetSum (f := fun k z => c k * σ k z) G fun k hk => (hσm k hk).const_mul _]
          exact Finset.sum_congr rfl fun k hk => (lintegral_const_mul _ (hσm k hk)).symm
  -- at each point at most one `σ_k` is non-zero
  have hpt : ∀ z, (∑ k ∈ G, c k * σ k z) ^ 2 = ∑ k ∈ G, c k ^ 2 * σ k z ^ 2 := fun z => by
    by_cases hz : ∃ i ∈ G, z ∈ B i
    · obtain ⟨i, hi, hzi⟩ := hz
      have h0 : ∀ k ∈ G, k ≠ i → σ k z = 0 := fun k _ hki =>
        indicator_of_notMem (fun hzk => disjoint_left.1 (hdisj hki) hzk hzi) _
      rw [Finset.sum_eq_single i (fun k hk hki => by rw [h0 k hk hki, mul_zero]) (fun h => absurd hi h),
        Finset.sum_eq_single i (fun k hk hki => by rw [h0 k hk hki, zero_pow two_ne_zero, mul_zero])
          (fun h => absurd hi h), mul_pow]
    · have h0 : ∀ k ∈ G, σ k z = 0 := fun k hk => indicator_of_notMem (fun hzk => hz ⟨k, hk, hzk⟩) _
      rw [Finset.sum_eq_zero fun k hk => by rw [h0 k hk, mul_zero],
        Finset.sum_eq_zero fun k hk => by rw [h0 k hk, zero_pow two_ne_zero, mul_zero], zero_pow two_ne_zero]
  -- the area of the density
  have hσA : ∀ k ∈ G, ∫⁻ z, σ k z ^ 2 ≤ A k := fun k _ => by
    show ∫⁻ z, σ k z ^ 2 ≤ ∫⁻ z in univ, ρ k z ^ 2
    rw [Measure.restrict_univ]
    exact lintegral_mono fun z => pow_le_pow_left₀ (zero_le) (indicator_le_self _ _ z) 2
  have hcA : ∀ k ∈ G, c k ^ 2 * A k = (A k)⁻¹ * S⁻¹ ^ 2 := fun k hk => by
    show ((A k)⁻¹ * S⁻¹) ^ 2 * A k = (A k)⁻¹ * S⁻¹ ^ 2
    calc ((A k)⁻¹ * S⁻¹) ^ 2 * A k = (A k)⁻¹ * S⁻¹ ^ 2 * ((A k)⁻¹ * A k) := by ring
      _ = (A k)⁻¹ * S⁻¹ ^ 2 := by rw [ENNReal.inv_mul_cancel (hpos k hk) (hfin k hk), mul_one]
  have harea : LiZhongQC.rhoArea (fun z => ∑ k ∈ G, c k * σ k z) univ ≤ S⁻¹ := by
    calc LiZhongQC.rhoArea (fun z => ∑ k ∈ G, c k * σ k z) univ = ∑ k ∈ G, c k ^ 2 * ∫⁻ z, σ k z ^ 2 := by
          unfold LiZhongQC.rhoArea
          rw [Measure.restrict_univ]
          simp_rw [hpt]
          rw [lintegral_finsetSum (f := fun k z => c k ^ 2 * σ k z ^ 2) G
            fun k hk => ((hσm k hk).pow_const 2).const_mul _]
          exact Finset.sum_congr rfl fun k hk => lintegral_const_mul _ ((hσm k hk).pow_const 2)
      _ ≤ ∑ k ∈ G, c k ^ 2 * A k :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hσA k hk) (zero_le)
      _ = S⁻¹ := by
          rw [Finset.sum_congr rfl hcA, ← Finset.sum_mul, ← hS]
          calc S * S⁻¹ ^ 2 = S⁻¹ * (S * S⁻¹) := by ring
            _ = S⁻¹ := by rw [ENNReal.mul_inv_cancel hS0 hStop, mul_one]
  calc arcFamilyModule Γ * S ≤ S⁻¹ * S :=
        mul_le_mul_of_nonneg_right ((LehtoVirtanen1973.lv34_module_le hadm).trans harea) (zero_le)
    _ = 1 := ENNReal.inv_mul_cancel hS0 hStop

/-- **Example 9.1** (§9.2, (9.2.3)–(9.2.5); P2 l. 470–498; U+: (9.2.5) is cited as a result at P2 l. 3256, 3317,
3378 and in Exercise 9.2.2). Let `Γ` be the family of all curves `C` in the rectangle
(9.2.3) `G = {x + iy : 0 < x < a, 0 < y < b}` that connect its two horizontal sides. Then (9.2.5) `mod Γ = a/b`.
Modelling: `G` is `LiZhongQC.rectangle a b` with `a, b > 0`; the horizontal sides are the closed segments
`[0, a]` and `[ib, a + ib]`; the connecting curves are `joiningArcFamily`. -/
theorem example9_1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    arcFamilyModule (joiningArcFamily (toExt (LiZhongQC.rectangle a b))
        (toExt {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ a}) (toExt {z : ℂ | z.im = b ∧ 0 ≤ z.re ∧ z.re ≤ a})) =
      ENNReal.ofReal (a / b) := by
  sorry

/-- **Example 9.2** (§9.2, (9.2.6), (9.2.7); P2 l. 500–512; U+: (9.2.7) is cited as a result at P2 l. 657, 671, 1304,
1334, 3274 and in Exercise 9.2.2), first part. Consider the annulus (9.2.6) `H = {z : r₁ < |z| < r₂}`
(`0 ≤ r₁ < r₂ < ∞`). Let `Γ` be the family of curves in `H` that connect the two boundary components. Then (9.2.7)
`mod Γ = 2π/log(r₂/r₁)`; if `r₁ = 0` then `mod Γ = 0`.
Modelling: `H` is `LiZhongQC.annulus r₁ r₂`; its boundary components are the circles `|z| = r₁` and `|z| = r₂`,
the first being the point `0` when `r₁ = 0` (`sphere 0 0 = {0}`); the two cases are stated separately, so that
`log(r₂/0)` does not occur. -/
theorem example9_2_a {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) :
    (0 < r₁ → arcFamilyModule (joiningArcFamily (toExt (LiZhongQC.annulus r₁ r₂)) (toExt (sphere 0 r₁))
        (toExt (sphere 0 r₂))) = ENNReal.ofReal (2 * π / Real.log (r₂ / r₁))) ∧
      (r₁ = 0 → arcFamilyModule (joiningArcFamily (toExt (LiZhongQC.annulus r₁ r₂)) (toExt (sphere 0 r₁))
        (toExt (sphere 0 r₂))) = 0) := by
  sorry

/-- **Example 9.2** (§9.2, (9.2.7); P2 l. 506–510), second part. For the annulus `H = {r₁ < |z| < r₂}`, the family
`Γ'` of the curves in `H` that separate the two boundary components has `mod Γ' = (2π)⁻¹ log(r₂/r₁)`.
Modelling: `0 < r₁` (for `r₁ = 0` the book's formula has no value); the separating curves are the Jordan curves in
`H` that separate the two boundary circles (`separatingCurveFamily`). -/
theorem example9_2_b {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    arcFamilyModule (separatingCurveFamily (toExt (LiZhongQC.annulus r₁ r₂)) (toExt (sphere 0 r₁))
        (toExt (sphere 0 r₂))) = ENNReal.ofReal (Real.log (r₂ / r₁) / (2 * π)) := by
  sorry

/-- **Proposition 9.1** (§9.2, (9.2.8); P2 l. 516–520; cited at P2 l. 671, 1266, 1493, 3317, 3378, and "conformally
invariant" at P2 l. 3256). Let `Γ` be a curve family in the domain `G`. If `f` maps `G` conformally into `ℂ` then
(9.2.8) `mod f(Γ) = mod Γ`.
Modelling: `G ⊆ ℂ` open and connected; "conformally into `ℂ`" is analytic and injective in `G`; `f(Γ)` consists of
the image curves `f(C)`, `C ∈ Γ` (`OnePoint.map f`, which is `f` on the finite points). -/
theorem prop9_1 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f G)
    (hinj : InjOn f G) {Γ : Set (Set ExtPlane)} (hΓ : IsCurveFamilyIn Γ G) :
    arcFamilyModule ((fun C => OnePoint.map f '' C) '' Γ) = arcFamilyModule Γ := by
  sorry

/-- **Proposition 9.2** (§9.2; P2 l. 538; cited at P2 l. 1274, 1304, 1334, 1493, 3317, and "monotone" at P2 l. 3256),
first sentence. If `Γ ⊆ Γ'` or if, for every `C ∈ Γ`, there exists `C' ∈ Γ'` with `C' ⊆ C`, then
`mod Γ ≤ mod Γ'`.
Modelling: `Γ` and `Γ'` are curve families (in `ℂ`). Stated as a new theorem rather than a pointer to LV's two
monotonicity lemmas (Q9.3): `LehtoVirtanen1973.arcFamilyModule_mono` is the case `Γ ⊆ Γ'`, and
`LehtoVirtanen1973.arcFamilyModule_mono_subarc` the case where every `C'` is a Jordan arc; a family in which some
members contain an arc of `Γ'` and others are Jordan curves of `Γ'` (a Jordan curve contained in `C` is `C` itself)
is covered by neither lemma, and combining them with subadditivity only gives `mod Γ ≤ 2 mod Γ'`. -/
theorem prop9_2_a {Γ Γ' : Set (Set ExtPlane)} (hΓ : IsCurveFamilyIn Γ univ) (hΓ' : IsCurveFamilyIn Γ' univ)
    (h : Γ ⊆ Γ' ∨ ∀ C ∈ Γ, ∃ C' ∈ Γ', C' ⊆ C) : arcFamilyModule Γ ≤ arcFamilyModule Γ' := by
  have _ := hΓ
  rcases h with h | h
  · exact LehtoVirtanen1973.arcFamilyModule_mono h
  · exact pom92_module_le_of_forall_subset (fun C' hC' => (hΓ' C' hC').1) h

/-- **Proposition 9.3** (§9.2, (9.2.12); P2 l. 564–568; cited at P2 l. 671, 1334, 3236, 3535), first part. Let `Γ_k`
be curve families in disjoint Borel sets `B_k`. If `⋃_k Γ_k ⊆ Γ` then (9.2.12) `Σ_k mod Γ_k ≤ mod Γ`.
Modelling: the index `k` runs through a countable type (finite or countably infinite families); the sets `B_k` are
pairwise disjoint; `Γ` is a curve family (in `ℂ`); the sum is taken in `[0, ∞]`. -/
theorem prop9_3_a {ι : Type*} [Countable ι] {B : ι → Set ℂ} (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) {Γs : ι → Set (Set ExtPlane)}
    (hΓs : ∀ k, IsCurveFamilyIn (Γs k) (B k)) {Γ : Set (Set ExtPlane)} (hΓ : IsCurveFamilyIn Γ univ)
    (hsub : ⋃ k, Γs k ⊆ Γ) :
    ∑' k, arcFamilyModule (Γs k) ≤ arcFamilyModule Γ := by
  have _ := hΓ
  refine LehtoVirtanen1973.lv34_le_module fun ρ hρ => ?_
  -- `1_{B_k} ρ` is admissible for `Γ_k`
  have hk : ∀ k, arcFamilyModule (Γs k) ≤ ∫⁻ z in B k, ρ z ^ 2 := fun k => by
    have hadm : LehtoVirtanen1973.IsAdmissibleFor (Γs k) ((B k).indicator ρ) := by
      refine ⟨hρ.1.indicator (hB k), fun C hC hr => ?_⟩
      rw [pom92_rhoLengthH_indicator (hB k) (hΓs k C hC).2]
      exact hρ.2 C (hsub (mem_iUnion.2 ⟨k, hC⟩)) hr
    calc arcFamilyModule (Γs k) ≤ LiZhongQC.rhoArea ((B k).indicator ρ) univ :=
          LehtoVirtanen1973.lv34_module_le hadm
      _ = ∫⁻ z in B k, ρ z ^ 2 := by
          unfold LiZhongQC.rhoArea
          rw [Measure.restrict_univ, ← lintegral_indicator (hB k)]
          refine lintegral_congr fun z => ?_
          by_cases hz : z ∈ B k
          · rw [indicator_of_mem hz, indicator_of_mem hz]
          · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_pow two_ne_zero]
  calc ∑' k, arcFamilyModule (Γs k) ≤ ∑' k, ∫⁻ z in B k, ρ z ^ 2 := ENNReal.tsum_le_tsum hk
    _ = ∫⁻ z in ⋃ k, B k, ρ z ^ 2 := (lintegral_iUnion hB hdisj _).symm
    _ ≤ LiZhongQC.rhoArea ρ univ := by
        unfold LiZhongQC.rhoArea
        rw [Measure.restrict_univ]
        exact setLIntegral_le_lintegral _ _

/-- **Proposition 9.3** (§9.2, (9.2.13); P2 l. 570–574; cited at P2 l. 624 in the proof of Proposition 9.4), second
part. Let `Γ_k` be curve families in disjoint Borel sets `B_k`. If `Γ` is a curve family in `B` and if each `C ∈ Γ`
contains some `C_k ∈ Γ_k` for every `k`, then (9.2.13) `1/mod Γ ≥ Σ_k 1/mod Γ_k`.
Modelling: as in `prop9_3_a`; `B` is a Borel set; the inverses and the sum are taken in `[0, ∞]`, with `1/0 = ∞` (the
book's proof obtains the case `Σ_k 1/mod Γ_k = ∞` "as a limit", P2 l. 585). -/
theorem prop9_3_b {ι : Type*} [Countable ι] {B : ι → Set ℂ} (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) {Γs : ι → Set (Set ExtPlane)}
    (hΓs : ∀ k, IsCurveFamilyIn (Γs k) (B k)) {B₀ : Set ℂ} (hB₀ : MeasurableSet B₀) {Γ : Set (Set ExtPlane)}
    (hΓ : IsCurveFamilyIn Γ B₀) (hcont : ∀ C ∈ Γ, ∀ k, ∃ C' ∈ Γs k, C' ⊆ C) :
    ∑' k, (arcFamilyModule (Γs k))⁻¹ ≤ (arcFamilyModule Γ)⁻¹ := by
  classical
  have _ := hB₀
  have _ := hΓ
  -- `mod Γ_k = 0` for some `k`: then `mod Γ = 0` by monotonicity
  by_cases h0 : ∃ k, arcFamilyModule (Γs k) = 0
  · obtain ⟨k, hk⟩ := h0
    have hM : arcFamilyModule Γ = 0 :=
      le_antisymm ((pom92_module_le_of_forall_subset (fun C' hC' => (hΓs k C' hC').1)
        fun C hC => hcont C hC k).trans hk.le) (zero_le)
    rw [hM, ENNReal.inv_zero]
    exact le_top
  have h0' : ∀ k, arcFamilyModule (Γs k) ≠ 0 := fun k hk => h0 ⟨k, hk⟩
  -- otherwise `(Σ_k (mod Γ_k)⁻¹) mod Γ ≤ 1`, over finite sets of indices, up to a factor `1 + δ`
  rw [ENNReal.le_inv_iff_mul_le, ← ENNReal.tsum_mul_right, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ0 : (1 : ℝ≥0∞) + δ ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
  have hδt : (1 : ℝ≥0∞) + δ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.coe_ne_top⟩
  have hex : ∀ k, ∃ ρ : ℂ → ℝ≥0∞, arcFamilyModule (Γs k) ≠ ⊤ →
      LehtoVirtanen1973.IsAdmissibleFor (Γs k) ρ ∧ LiZhongQC.rhoArea ρ univ < arcFamilyModule (Γs k) * (1 + δ) := by
    intro k
    by_cases htop : arcFamilyModule (Γs k) = ⊤
    · exact ⟨0, fun h => absurd htop h⟩
    · have hlt : arcFamilyModule (Γs k) < arcFamilyModule (Γs k) * (1 + δ) := by
        rw [mul_add, mul_one]
        exact ENNReal.lt_add_right htop (mul_ne_zero (h0' k) (ENNReal.coe_ne_zero.2 hδ.ne'))
      obtain ⟨ρ, hadm, hρ⟩ := LehtoVirtanen1973.lv34_exists_lt hlt
      exact ⟨ρ, fun _ => ⟨hadm, hρ⟩⟩
  choose ρ hρ using hex
  set G := F.filter fun k => arcFamilyModule (Γs k) ≠ ⊤ with hG
  have hGt : ∀ k ∈ G, arcFamilyModule (Γs k) ≠ ⊤ := fun k hk => (Finset.mem_filter.1 hk).2
  have hApos : ∀ k ∈ G, LiZhongQC.rhoArea (ρ k) univ ≠ 0 := fun k hk =>
    (lt_of_lt_of_le (pos_iff_ne_zero.2 (h0' k)) (LehtoVirtanen1973.lv34_module_le (hρ k (hGt k hk)).1)).ne'
  have hAfin : ∀ k ∈ G, LiZhongQC.rhoArea (ρ k) univ ≠ ⊤ := fun k hk => ne_top_of_lt (hρ k (hGt k hk)).2
  have hinv : ∀ k ∈ G, (arcFamilyModule (Γs k))⁻¹ ≤ (1 + δ) * (LiZhongQC.rhoArea (ρ k) univ)⁻¹ :=
    fun k hk => by
      calc (arcFamilyModule (Γs k))⁻¹ = (1 + δ) * (arcFamilyModule (Γs k) * (1 + δ))⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl (h0' k)) (Or.inl (hGt k hk)), mul_comm, mul_assoc,
              ENNReal.inv_mul_cancel hδ0 hδt, mul_one]
        _ ≤ (1 + δ) * (LiZhongQC.rhoArea (ρ k) univ)⁻¹ :=
            mul_le_mul_of_nonneg_left (ENNReal.inv_le_inv.2 (hρ k (hGt k hk)).2.le) (zero_le)
  -- the indices with `mod Γ_k = ∞` contribute nothing
  have hsplit : ∑ k ∈ F, (arcFamilyModule (Γs k))⁻¹ * arcFamilyModule Γ =
      ∑ k ∈ G, (arcFamilyModule (Γs k))⁻¹ * arcFamilyModule Γ := by
    rw [hG, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [not_ne_iff.1 h, ENNReal.inv_top, zero_mul]
  rw [hsplit]
  calc ∑ k ∈ G, (arcFamilyModule (Γs k))⁻¹ * arcFamilyModule Γ
      ≤ ∑ k ∈ G, (1 + δ) * (LiZhongQC.rhoArea (ρ k) univ)⁻¹ * arcFamilyModule Γ :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hinv k hk) (zero_le)
    _ = (1 + δ) * (arcFamilyModule Γ * ∑ k ∈ G, (LiZhongQC.rhoArea (ρ k) univ)⁻¹) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (1 + δ) * 1 := mul_le_mul_of_nonneg_left (pom92_series_finset hB hdisj hΓs hcont G
        (fun k hk => (hρ k (hGt k hk)).1) hApos hAfin) (zero_le)
    _ = 1 + δ := mul_one _

/-- **Proposition 9.4** (§9.2; P2 l. 613–619; cited at P2 l. 3272, in the proof of Proposition 11.8, and in
Exercises 9.2.1, 9.2.2). Let the domain `G` be symmetric with respect to `ℝ` and let `G⁺ = {Im z > 0} ∩ G`,
`A⁺ ⊆ {Im z > 0} ∩ ∂G`, furthermore `G⁻`, `A⁻` the reflected sets in `{Im z < 0}`. If
`Γ = {curves C in G from A⁻ to A⁺}` and `Γ^± = {curves C in G^± from ℝ to A^±}`, then
`mod Γ⁺ = mod Γ⁻ = 2 mod Γ`.
Modelling: `G ⊆ ℂ` open and connected with `z ∈ G ⟺ z̄ ∈ G`; `∂G` is the frontier in `ℂ`; `A⁻ = {z̄ : z ∈ A⁺}`,
`G⁻ = G ∩ {Im z < 0}`. "From `ℝ`" is read as "from a point of `ℝ ∩ G`" (Q9.6(h)): the proof joins `C⁺` and its
reflection at their common point on `ℝ` into a curve of `Γ`, which must lie in `G`. -/
theorem prop9_4 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hsymm : ∀ z : ℂ, z ∈ G ↔ conj z ∈ G)
    {Ap : Set ℂ} (hAp : Ap ⊆ {z | 0 < z.im} ∩ frontier G) :
    arcFamilyModule (joiningArcFamily (toExt ({z | 0 < z.im} ∩ G)) (toExt {z ∈ G | z.im = 0}) (toExt Ap)) =
        arcFamilyModule (joiningArcFamily (toExt ({z | z.im < 0} ∩ G)) (toExt {z ∈ G | z.im = 0})
          (toExt ((fun z => conj z) '' Ap))) ∧
      arcFamilyModule (joiningArcFamily (toExt ({z | 0 < z.im} ∩ G)) (toExt {z ∈ G | z.im = 0}) (toExt Ap)) =
        2 * arcFamilyModule (joiningArcFamily (toExt G) (toExt ((fun z => conj z) '' Ap)) (toExt Ap)) := by
  sorry

/-- **Proposition 9.5** (§9.2; one of the Teichmüller module theorems, Tei38; P2 l. 643–655; cited at P2 l. 3280, in
the proof of Proposition 11.8). Let `0 < r₁ < r₂` and `T_j = {|z| = r_j}` for `j = 1, 2`. Let the Jordan curve `J`
separate `T₁` and `T₂` and let `Γ_j` denote the family of Jordan curves that separate `T_j` and `J`. If (9.2.14)
`mod Γ₁ + mod Γ₂ > (2π)⁻¹ log(r₂/r₁) − ε` (`0 < ε < 1/36`), then, with an absolute constant `K`, (9.2.15)
`1 ≤ max_{z ∈ J} |z| / min_{z ∈ J} |z| < 1 + K √(ε log(1/ε))`.
Modelling: `K` is absolute (`∃ K, ∀ r₁ r₂ J ε`); `J ⊆ ℂ`, with `J` separating `T₁` and `T₂` (LV's `Separates`);
(9.2.14) is written `(2π)⁻¹ log(r₂/r₁) < mod Γ₁ + mod Γ₂ + ε` in `[0, ∞]` (equivalent, the modules being
non-negative), so no truncation of a negative right side occurs. `J` is compact, nonempty and avoids `0` (it
separates `T₁` from `T₂`), so the maximum and the minimum of `|z|` on `J` are its `sSup` and `sInf`, and the minimum
is positive. -/
theorem prop9_5 : ∃ K : ℝ, ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∀ J : Set ℂ, IsJordanCurve (toExt J) →
    Separates (toExt J) (toExt (sphere 0 r₁)) (toExt (sphere 0 r₂)) → ∀ ε : ℝ, 0 < ε → ε < 1 / 36 →
    ENNReal.ofReal (Real.log (r₂ / r₁) / (2 * π)) <
        arcFamilyModule (separatingCurveFamily univ (toExt (sphere 0 r₁)) (toExt J)) +
          arcFamilyModule (separatingCurveFamily univ (toExt (sphere 0 r₂)) (toExt J)) + ENNReal.ofReal ε →
      1 ≤ sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) ∧
        sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) <
          1 + K * Real.sqrt (ε * Real.log (1 / ε)) := by
  sorry

/-- **Formula (9.2.18)** (§9.2; Grötzsch's estimate, quoted from LeVi73, pp. 53–61; P2 l. 703–709; named in the index,
"Grötzsch module theorem 202"). Let `G` be a doubly connected domain and `Γ` the family of Jordan curves that separate
the two boundary components. If `G ⊆ 𝔻` and if `G` separates `{0, z₁}` from `𝕋`, then (9.2.18)
`2π mod Γ < log(4/|z₁|)`.
Modelling: "doubly connected" is `LehtoVirtanen1973.IsRingDomain`; the curves of `Γ` lie in `G` and separate the two
components of `ℂ̂ ∖ G`, which contain `0` and `∞` (separating the boundary components is the same for a curve in
`G`); `z₁ ≠ 0` is the book's tacit assumption (for `z₁ = 0` the right side is `log(4/0)`, and `mod Γ` is unbounded). -/
theorem eq9_2_18 {G : Set ℂ} (hG : IsRingDomain (toExt G)) (hGD : G ⊆ unitDisc) {z₁ : ℂ} (hz₁ : z₁ ≠ 0)
    (hsep : Separates (toExt G) {((0 : ℂ) : ExtPlane), (z₁ : ExtPlane)} (toExt (sphere 0 1))) :
    ENNReal.ofReal (2 * π) * arcFamilyModule (separatingCurveFamily (toExt G)
        (connectedComponentIn (toExt G)ᶜ ((0 : ℂ) : ExtPlane)) (connectedComponentIn (toExt G)ᶜ extInf)) <
      ENNReal.ofReal (Real.log (4 / ‖z₁‖)) := by
  sorry

/-- **Formula (9.2.19)** (§9.2; Teichmüller's estimate, quoted from LeVi73; P2 l. 711–715; cited "Teichmüller's
estimate (9.2.19)" at P2 l. 3553, in the proof of Theorem 11.13). Let `G` be a doubly connected domain and `Γ` the
family of Jordan curves that separate the two boundary components. If `G ⊆ ℂ` separates `{0, z₁}` from `{z₂, ∞}`, then
(9.2.19) `2π mod Γ < log(16(|z₁| + |z₂|)/|z₁|)`.
Modelling: as in `eq9_2_18`; `z₁ ≠ 0` is tacit, as there (`z₂ ≠ 0` follows from the separation). -/
theorem eq9_2_19 {G : Set ℂ} (hG : IsRingDomain (toExt G)) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0)
    (hsep : Separates (toExt G) {((0 : ℂ) : ExtPlane), (z₁ : ExtPlane)} {(z₂ : ExtPlane), extInf}) :
    ENNReal.ofReal (2 * π) * arcFamilyModule (separatingCurveFamily (toExt G)
        (connectedComponentIn (toExt G)ᶜ ((0 : ℂ) : ExtPlane)) (connectedComponentIn (toExt G)ᶜ extInf)) <
      ENNReal.ofReal (Real.log (16 * (‖z₁‖ + ‖z₂‖) / ‖z₁‖)) := by
  sorry

end Pommerenke1992
