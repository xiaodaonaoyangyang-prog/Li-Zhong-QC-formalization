import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties
import References.LehtoVirtanen1973.Ch03.S02_AbsoluteContinuity
import LiZhongQC.Ch01.S03_ExtremalLength

/-!
# Lehto–Virtanen, Chapter III §4: Module of a family of arcs or curves

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §4
(pp. 132–136; `full.md` P1:3887–4076).

Conventions. As in Chapter I, this section works with point sets of the whole plane `ℂ̄` (P1:3891). A family of arcs
or curves is a set `𝒞 : Set (Set ExtPlane)` of point sets, the book's members being Jordan arcs (Ch. I
`IsJordanArc`) or Jordan curves (`LiZhongQC.IsJordanCurve`) of `ℂ̄`. Members that are not locally rectifiable arcs or
curves do not affect the module (P1:3915), so the module is defined, and the statements are made, for arbitrary sets
of subsets of `ℂ̄`; for families of Jordan arcs or curves this is the book's module. Measures and integrals of sets
containing `∞` are taken of their finite parts (`τ(A) = τ(A − {∞})`, P1:3891): areas are `volume` of
`References.finitePart A`, and `∫_C ρ |dz|` is the integral over the finite part of `C` with respect to the linear
measure `μH[1]`, as in (2.7) (`rhoLengthH`). The functions `ρ` are non-negative Borel functions of the finite plane
with values in `[0, ∞]` (`ℂ → ℝ≥0∞`, `Measurable`); their value at `∞` never enters. The module and the extremal
length are `ℝ≥0∞`-valued. The `L^p` notions of §4.4 are Mathlib's, for the area measure restricted to the set.

* Definition (extension `τ(A) = τ(A − {∞})` of measures and integrals to sets of the plane containing `∞`, §4.1) —
  exists: `References.finitePart` (a measure or an integral of a set A of the extended plane is taken of its finite
  part)
* Definition (locally rectifiable arc containing `∞`, §4.1; for arcs and curves of the finite plane, §2.6; transported
  by linear conformal mappings) — `IsLocRectifiableExt`
* Definition (`∫_C ρ |dz|` over a locally rectifiable arc or curve, §4.1, by (2.7)) — `rhoLengthH`
* Definition (`m_ρ(Ω)`, (4.2), §4.1) — exists: `LiZhongQC.rhoArea` (the integral of the square of ρ over a set of the
  finite plane; m_ρ(Ω) is its value on the whole finite plane, the point ∞ being discarded)
* Definition (admissible function, (4.1); module `M(𝒞)`, (4.3); extremal length `1/M(𝒞)`, §4.1) —
  `IsAdmissibleFor`, `arcFamilyModule`, `arcFamilyExtremalLength`
* Unlabelled (§4.2, P1:3923–3939): the module is monotonic, for `𝒞₁ ⊃ 𝒞₂` and when every member of `𝒞₂` has a
  subarc belonging to `𝒞₁` — `arcFamilyModule_mono`, `arcFamilyModule_mono_subarc`
* Formula (4.5) (§4.2) — `eq3_4_5`
* Formula (4.6) (§4.2) — `eq3_4_6`
* Lemma 4.1 (§4.3, Fuglede) — `lemma3_4_1`
* Unlabelled (§4.3, P1:4007–4017): a family of arcs and curves which possess a common point has module zero —
  `arcFamilyModule_eq_zero_of_common_point`
* Unlabelled (§4.3, P1:4019): the family of all non-rectifiable arcs and curves has module zero —
  `arcFamilyModule_nonrectifiable`
* Definition (the class `L^p(A)`, the `L^p`-norm and the `L^p` metric, §4.4) — exists: `MeasureTheory.MemLp`,
  `MeasureTheory.eLpNorm`, `MeasureTheory.Lp` (for the area measure restricted to A; the metric space identifies
  functions equal almost everywhere; LV: 1 ≤ p < ∞, P1:4021, a range covered by Mathlib's exponent in [0, ∞])
* Lemma 4.2 (§4.4, Fuglede) — `lemma3_4_2`

Formula (4.4) (P1:3917–3921: if all members of `𝒞` lie in a Borel set `B`, the infimum (4.3) may be taken over the
admissible functions vanishing outside `B`) is immediate and not cited later (the "(4.4)" cited at P1:5619, 5637 is
Chapter IV's own formula); the second sentence of P1:3893 (removing `∞` from a locally rectifiable arc through `∞`
leaves two locally rectifiable subarcs, to which §2 applies) is explanatory and subsumed by `rhoLengthH`, which
integrates over the finite part of the arc; the introduction of §4.1 (P1:3889) and the third sentence of P1:3891 (the
extended area measure need not be the infimum over open coverings) are explanatory. None is stated (inventory:
omitted).

The two module notions. Chapter I (I.4, I.6) models the book's "deliberately indefinite" curve and density classes
by the project's locally rectifiable curves and densities (LiZhongQC.LRCurve, LiZhongQC.densitiesP0; leader
decision Q3), the precision announced for III.4 in footnote 7; this section formalizes LV's own module of point-set
families (`arcFamilyModule`). No comparison between the two is stated here; LV's identities `M(𝒞) = M(Q)`,
`M(𝒞′) = M(B)/2π` and `M(𝒞″) = 2π/M(B)` are stated in IV.3.4 (module_quad_joining_arcs,
module_ring_separating_curves, module_ring_joining_arcs).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane toExt IsJordanCurve IsMobius)
open References (finitePart)

/-! ## §4.1 Generalization of the notion of module -/

/-- **Definition** (locally rectifiable arc or curve of the plane, Ch. III §4.1). A Jordan arc `C` of `ℂ̄` is locally
rectifiable if it can be transformed by a linear conformal mapping (a Möbius transformation of `ℂ̄`) into a
locally rectifiable arc of the finite plane (§2.6); a Jordan curve of `ℂ̄` is locally rectifiable if it can be so
transformed into a rectifiable Jordan curve of the finite plane (§2.6: all its subarcs rectifiable).
Modelling: the book states this for the arcs containing `∞` (P1:3893) and uses §2.6 for the arcs and curves of the
finite plane; the uniform formulation covers both, since the identity is a Möbius transformation and a Möbius
transformation whose pole is not on `C` preserves the local rectifiability of arcs of the finite plane (it is
locally bi-Lipschitz off its pole). For the curves (compact) "locally rectifiable" is "rectifiable"; the book's
wording for curves through `∞` is supplied in the same way as for arcs. Equivalently (P1:3605), a curve through `∞`
is locally rectifiable when both arcs of a division into two subarcs are; since the curves through `∞` share the
point `∞`, by `arcFamilyModule_eq_zero_of_common_point` and `eq3_4_6` this choice does not affect any module. -/
def IsLocRectifiableExt (C : Set ExtPlane) : Prop :=
  ∃ T : ExtPlane → ExtPlane, IsMobius T ∧ ∃ C' : Set ℂ, T '' C = toExt C' ∧
    (IsLocRectifiableArc C' ∨ IsRectifiableJordanCurve C')

/-- **Definition** (`∫_C ρ |dz|`, Ch. III §4.1). For a non-negative Borel function `ρ` and a locally rectifiable arc
or curve `C` of `ℂ̄`, `∫_C ρ |dz|` is the integral of `ρ` with respect to the linear measure on `C` ((2.7), where
`dl` is also written `|dz|`), the point `∞` being discarded (P1:3891–3893).
Modelling: the lower integral over the finite part of `C` with respect to the one-dimensional Hausdorff measure
`μH[1]` (the linear measure of §1.8). The value is defined for every set `C`; it is used only for locally rectifiable
arcs and curves. -/
def rhoLengthH (ρ : ℂ → ℝ≥0∞) (C : Set ExtPlane) : ℝ≥0∞ := ∫⁻ z in finitePart C, ρ z ∂μH[1]

/-- **Definition** (admissible function, Ch. III §4.1, (4.1)). A non-negative Borel function `ρ` is admissible for
the family `𝒞` if `∫_C ρ |dz| ≥ 1` (4.1) for every locally rectifiable `C ∈ 𝒞`.
Modelling: `ρ` is defined on the finite plane (its value at `∞` never enters, P1:3891) and may take the value `∞`.
-/
def IsAdmissibleFor (𝒞 : Set (Set ExtPlane)) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ C ∈ 𝒞, IsLocRectifiableExt C → 1 ≤ rhoLengthH ρ C

/-- **Definition** (module of a family of arcs or curves, Ch. III §4.1, (4.2)–(4.3)). `M(𝒞) = inf_ρ m_ρ(Ω)`, the
infimum of `m_ρ(Ω) = ∬_Ω ρ² dσ` (4.2) over the functions `ρ` admissible for `𝒞`.
Modelling: `m_ρ(Ω)` is `LiZhongQC.rhoArea ρ univ`, the area integral over the finite plane (`Ω − {∞}`). The
infimum is never taken over the empty set: the constant `∞` is admissible, a locally rectifiable arc or curve having
positive linear measure. -/
def arcFamilyModule (𝒞 : Set (Set ExtPlane)) : ℝ≥0∞ :=
  ⨅ (ρ : ℂ → ℝ≥0∞) (_ : IsAdmissibleFor 𝒞 ρ), LiZhongQC.rhoArea ρ univ

/-- **Definition** (extremal length of a family of arcs or curves, Ch. III §4.1): the number `1/M(𝒞)`.
Modelling: the inverse in `[0, ∞]` (`1/0 = ∞`, `1/∞ = 0`). -/
def arcFamilyExtremalLength (𝒞 : Set (Set ExtPlane)) : ℝ≥0∞ := (arcFamilyModule 𝒞)⁻¹

/-! ## §4.2 Properties of the generalized module -/

/-- The `ρ`-length is monotone in the point set (helper for §4.2). -/
theorem lv34_rhoLengthH_mono {ρ : ℂ → ℝ≥0∞} {C₁ C₂ : Set ExtPlane} (h : C₁ ⊆ C₂) :
    rhoLengthH ρ C₁ ≤ rhoLengthH ρ C₂ := by
  unfold rhoLengthH
  exact lintegral_mono_set (preimage_mono h)

/-- The module is at most the `ρ`-area of an admissible `ρ` (helper for §4.2). -/
theorem lv34_module_le {𝒞 : Set (Set ExtPlane)} {ρ : ℂ → ℝ≥0∞} (h : IsAdmissibleFor 𝒞 ρ) :
    arcFamilyModule 𝒞 ≤ LiZhongQC.rhoArea ρ univ := by
  unfold arcFamilyModule
  exact iInf₂_le ρ h

/-- A lower bound for the `ρ`-areas of all admissible `ρ` is a lower bound for the module (helper for §4.2). -/
theorem lv34_le_module {𝒞 : Set (Set ExtPlane)} {a : ℝ≥0∞}
    (h : ∀ ρ, IsAdmissibleFor 𝒞 ρ → a ≤ LiZhongQC.rhoArea ρ univ) : a ≤ arcFamilyModule 𝒞 := by
  unfold arcFamilyModule
  exact le_iInf₂ h

/-- Every bound strictly above the module is exceeded by the `ρ`-area of some admissible `ρ` (helper for §4.2). -/
theorem lv34_exists_lt {𝒞 : Set (Set ExtPlane)} {a : ℝ≥0∞} (h : arcFamilyModule 𝒞 < a) :
    ∃ ρ, IsAdmissibleFor 𝒞 ρ ∧ LiZhongQC.rhoArea ρ univ < a := by
  unfold arcFamilyModule at h
  obtain ⟨ρ, hρ⟩ := iInf_lt_iff.1 h
  obtain ⟨hadm, hlt⟩ := iInf_lt_iff.1 hρ
  exact ⟨ρ, hadm, hlt⟩

/-- A homeomorphism of `ℂ̄` maps Jordan arcs to Jordan arcs (helper for §4.2). -/
theorem lv34_isJordanArc_image (e : ExtPlane ≃ₜ ExtPlane) {C : Set ExtPlane} (hC : IsJordanArc C) :
    IsJordanArc (e '' C) := by
  obtain ⟨I, hI, hIn, γ, hγ, rfl⟩ := hC
  exact ⟨I, hI, hIn, e ∘ γ, e.isEmbedding.comp hγ, image_comp e γ I⟩

/-- A Jordan arc contained in a locally rectifiable arc or curve of `ℂ̄` is locally rectifiable (helper for §4.2):
the Möbius transformation that carries the arc or curve to a locally rectifiable arc or rectifiable Jordan curve of
the finite plane carries the subarc to a Jordan arc of the finite plane, and the closed subarcs of the image are closed
Jordan arcs in the image of the original arc or curve. -/
theorem lv34_isLocRectifiableExt_of_subset_arc {C C₁ : Set ExtPlane} (hC : IsLocRectifiableExt C)
    (hC₁ : IsJordanArc C₁) (hsub : C₁ ⊆ C) : IsLocRectifiableExt C₁ := by
  obtain ⟨T, ⟨a, b, c, d, had, rfl⟩, C', hTC, hC'⟩ := hC
  have hsub' : LiZhongQC.mobiusExt a b c d '' C₁ ⊆ toExt C' := by
    rw [← hTC]
    exact image_mono hsub
  have heq : toExt (finitePart (LiZhongQC.mobiusExt a b c d '' C₁)) = LiZhongQC.mobiusExt a b c d '' C₁ :=
    image_preimage_eq_of_subset (hsub'.trans (image_subset_range _ _))
  have hfp : finitePart (LiZhongQC.mobiusExt a b c d '' C₁) ⊆ C' := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hsub' (show ((z : ExtPlane)) ∈ LiZhongQC.mobiusExt a b c d '' C₁ from hz)
    rwa [← OnePoint.coe_injective hyz]
  have hfun : ⇑(LiZhongQC.mobiusHomeomorph a b c d had) = LiZhongQC.mobiusExt a b c d :=
    funext (LiZhongQC.mobiusHomeomorph_apply had)
  have harc : IsJordanArc (toExt (finitePart (LiZhongQC.mobiusExt a b c d '' C₁))) := by
    rw [heq, ← hfun]
    exact lv34_isJordanArc_image _ hC₁
  refine ⟨LiZhongQC.mobiusExt a b c d, ⟨a, b, c, d, had, rfl⟩, _, heq.symm, Or.inl ⟨harc, fun C₃ h₃ hcl => ?_⟩⟩
  rcases hC' with ⟨-, hloc⟩ | ⟨-, hrc⟩
  · exact hloc C₃ (h₃.trans hfp) hcl
  · exact hrc C₃ (h₃.trans hfp) ⟨Icc 0 1, ordConnected_Icc, ⟨0, by simp, 1, by simp, zero_ne_one⟩, hcl⟩

/-- **Unlabelled** (Ch. III §4.2, P1:3923–3931). The module is monotonic: if `𝒞₁ ⊃ 𝒞₂`, then
`M(𝒞₁) ≥ M(𝒞₂)`. -/
theorem arcFamilyModule_mono {𝒞₁ 𝒞₂ : Set (Set ExtPlane)} (h : 𝒞₂ ⊆ 𝒞₁) :
    arcFamilyModule 𝒞₂ ≤ arcFamilyModule 𝒞₁ := by
  exact lv34_le_module fun ρ hρ => lv34_module_le ⟨hρ.1, fun C hC hr => hρ.2 C (h hC) hr⟩

/-- **Unlabelled** (Ch. III §4.2, P1:3933–3939). If to every `C₂ ∈ 𝒞₂` there corresponds a `C₁ ∈ 𝒞₁` which is a
subarc of `C₂`, then `M(𝒞₁) ≥ M(𝒞₂)`.
Modelling: a subarc of `C₂` is a Jordan arc of `ℂ̄` contained in `C₂`. -/
theorem arcFamilyModule_mono_subarc {𝒞₁ 𝒞₂ : Set (Set ExtPlane)}
    (h : ∀ C₂ ∈ 𝒞₂, ∃ C₁ ∈ 𝒞₁, C₁ ⊆ C₂ ∧ IsJordanArc C₁) :
    arcFamilyModule 𝒞₂ ≤ arcFamilyModule 𝒞₁ := by
  refine lv34_le_module fun ρ hρ => lv34_module_le ⟨hρ.1, fun C₂ hC₂ hr => ?_⟩
  obtain ⟨C₁, hC₁, hsub, harc⟩ := h C₂ hC₂
  exact (hρ.2 C₁ hC₁ (lv34_isLocRectifiableExt_of_subset_arc hr harc hsub)).trans (lv34_rhoLengthH_mono hsub)

/-- **Formula (4.5)** (Ch. III §4.2). The module is subadditive: if `𝒞 = ⋃_{n ≥ 1} 𝒞ₙ`, then
`M(𝒞) ≤ ∑_{n ≥ 1} M(𝒞ₙ)` (4.5).
Modelling: the families are indexed by `ℕ`; the sum is taken in `[0, ∞]`. -/
theorem eq3_4_5 (𝒞 : ℕ → Set (Set ExtPlane)) :
    arcFamilyModule (⋃ n, 𝒞 n) ≤ ∑' n, arcFamilyModule (𝒞 n) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  -- admissible `ρₙ` with `m_{ρₙ}(Ω) < M(𝒞ₙ) + δₙ`
  have hex : ∀ n, ∃ ρ, IsAdmissibleFor (𝒞 n) ρ ∧ LiZhongQC.rhoArea ρ univ < arcFamilyModule (𝒞 n) + δ n :=
    fun n => lv34_exists_lt (ENNReal.lt_add_right
      (ne_top_of_le_ne_top hlt.ne (ENNReal.le_tsum (f := fun n => arcFamilyModule (𝒞 n)) n))
      (ENNReal.coe_ne_zero.2 (hδ n).ne'))
  choose ρ hρ hρlt using hex
  -- their supremum is admissible for the union, and its square is at most `∑ ρₙ²`
  have hadm : IsAdmissibleFor (⋃ n, 𝒞 n) fun z => ⨆ n, ρ n z := by
    refine ⟨Measurable.iSup fun n => (hρ n).1, fun C hC hr => ?_⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hC
    exact ((hρ n).2 C hn hr).trans (lintegral_mono fun z => le_iSup (fun k => ρ k z) n)
  calc arcFamilyModule (⋃ n, 𝒞 n) ≤ LiZhongQC.rhoArea (fun z => ⨆ n, ρ n z) univ := lv34_module_le hadm
    _ ≤ ∑' n, LiZhongQC.rhoArea (ρ n) univ := by
        unfold LiZhongQC.rhoArea
        rw [← lintegral_tsum fun n => ((hρ n).1.pow_const 2).aemeasurable]
        refine lintegral_mono fun z => ?_
        show (⨆ n, ρ n z) ^ 2 ≤ ∑' n, ρ n z ^ 2
        rw [ENNReal.iSup_pow]
        exact iSup_le fun n => ENNReal.le_tsum (f := fun n => ρ n z ^ 2) n
    _ ≤ ∑' n, (arcFamilyModule (𝒞 n) + δ n) := ENNReal.tsum_le_tsum fun n => (hρlt n).le
    _ = ∑' n, arcFamilyModule (𝒞 n) + ∑' n, (δ n : ℝ≥0∞) := ENNReal.tsum_add
    _ ≤ ∑' n, arcFamilyModule (𝒞 n) + ε := add_le_add le_rfl hδε.le

/-- **Formula (4.6)** (Ch. III §4.2). `M(𝒞 ∪ 𝒞₀) = M(𝒞)` if `M(𝒞₀) = 0` (4.6). -/
theorem eq3_4_6 {𝒞 𝒞₀ : Set (Set ExtPlane)} (h₀ : arcFamilyModule 𝒞₀ = 0) :
    arcFamilyModule (𝒞 ∪ 𝒞₀) = arcFamilyModule 𝒞 := by
  refine le_antisymm ?_ (arcFamilyModule_mono subset_union_left)
  have hU : 𝒞 ∪ 𝒞₀ = ⋃ n : ℕ, if n = 0 then 𝒞 else 𝒞₀ := by
    ext C
    rw [mem_union, mem_iUnion]
    constructor
    · rintro (hC | hC)
      · exact ⟨0, by rwa [ite_eq_left rfl]⟩
      · exact ⟨1, by rwa [ite_eq_right one_ne_zero]⟩
    · rintro ⟨n, hn⟩
      split_ifs at hn
      · exact Or.inl hn
      · exact Or.inr hn
  calc arcFamilyModule (𝒞 ∪ 𝒞₀) ≤ ∑' n : ℕ, arcFamilyModule (if n = 0 then 𝒞 else 𝒞₀) := by
        rw [hU]
        exact eq3_4_5 _
    _ = arcFamilyModule 𝒞 := by
        rw [tsum_eq_single 0 fun n hn => by rw [ite_eq_right hn, h₀], ite_eq_left rfl]

/-! ## §4.3 Families of zero module -/

/-- **Lemma 4.1** (Ch. III §4.3, Fuglede). A necessary and sufficient condition for `M(𝒞)` to vanish is the existence
of a non-negative Borel function `ρ₀` which is square integrable over the plane and satisfies `∫_C ρ₀ |dz| = ∞` for
every locally rectifiable `C ∈ 𝒞`.
Modelling: "square integrable over the plane" is `m_{ρ₀}(Ω) = ∬ ρ₀² dσ < ∞` (`LiZhongQC.rhoArea ρ₀ univ < ⊤`). -/
theorem lemma3_4_1 (𝒞 : Set (Set ExtPlane)) :
    arcFamilyModule 𝒞 = 0 ↔ ∃ ρ₀ : ℂ → ℝ≥0∞, Measurable ρ₀ ∧ LiZhongQC.rhoArea ρ₀ univ < ⊤ ∧
      ∀ C ∈ 𝒞, IsLocRectifiableExt C → rhoLengthH ρ₀ C = ⊤ := by
  sorry

/-- **Unlabelled** (Ch. III §4.3, P1:4007–4017). The module of a family `𝒞` vanishes if all arcs and curves of `𝒞`
possess a common point `z₀` (finite or `∞`). -/
theorem arcFamilyModule_eq_zero_of_common_point {𝒞 : Set (Set ExtPlane)} {z₀ : ExtPlane}
    (h : ∀ C ∈ 𝒞, z₀ ∈ C) : arcFamilyModule 𝒞 = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §4.3, P1:4019). The family of all non-rectifiable arcs and curves has module zero.
Modelling: the rectifiable arcs and curves are those of §2.6, which lie in the finite plane (`IsRectifiableArc`,
`IsRectifiableJordanCurve`); an arc or curve through `∞` is not rectifiable, as the book's function
`ρ₀(z) = 1/(1 + |z| log |z|)`, which makes `∫_C ρ₀ |dz|` infinite on all of them, shows. -/
theorem arcFamilyModule_nonrectifiable :
    arcFamilyModule {C : Set ExtPlane |
      (IsJordanArc C ∧ ¬ ∃ C' : Set ℂ, C = toExt C' ∧ IsRectifiableArc C') ∨
        (IsJordanCurve C ∧ ¬ ∃ C' : Set ℂ, C = toExt C' ∧ IsRectifiableJordanCurve C')} = 0 := by
  sorry

/-! ## §4.4 Modules and `L²`-convergence -/

/-- **Lemma 4.2** (Ch. III §4.4, Fuglede). Let `fₙ`, `n = 1, 2, …`, be a sequence of Borel functions belonging to the
class `L²` in a Borel set `B` and converging to a Borel function `f` in the `L²` metric. Then there exists a
subsequence `f_{n_k}` such that `lim_{k → ∞} ∫_C |f_{n_k} − f| |dz| = 0` (4.7) for all locally rectifiable arcs
`C ⊂ B`, with the exception of a family of module zero.
Modelling: `B` is a set of the plane `ℂ̄` whose finite part is a Borel set; the functions are finite `ℂ`-valued Borel
functions of the finite plane (D2); `L²` and the `L²` metric refer to the area measure restricted to the finite part
of `B`. The sequence is indexed by `ℕ` and the subsequence is `fn (φ k)` with `φ` strictly increasing; the
exceptional family `𝒞₀` has module zero. -/
theorem lemma3_4_2 {B : Set ExtPlane} (hB : MeasurableSet (finitePart B)) {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfn : ∀ n, Measurable (fn n)) (hfnL2 : ∀ n, MemLp (fn n) 2 (volume.restrict (finitePart B)))
    (hf : Measurable f)
    (hconv : Tendsto (fun n => eLpNorm (fn n - f) 2 (volume.restrict (finitePart B))) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ 𝒞₀ : Set (Set ExtPlane), arcFamilyModule 𝒞₀ = 0 ∧
      ∀ C : Set ExtPlane, IsJordanArc C → IsLocRectifiableExt C → C ⊆ B → C ∉ 𝒞₀ →
        Tendsto (fun k => rhoLengthH (fun z => ‖fn (φ k) z - f z‖ₑ) C) atTop (𝓝 0) := by
  sorry

end LehtoVirtanen1973
