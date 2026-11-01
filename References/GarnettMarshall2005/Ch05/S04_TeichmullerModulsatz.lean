import LiZhongQC.Lemmas.KrausNehari
import References.GarnettMarshall2005.Ch05.S03_ReducedExtremalDistance
import References.Gehring1978.S1_Introduction

/-!
# Garnett–Marshall, Chapter V §4: Teichmüller's Modulsatz

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V §4 (pp. 166–173;
`full.md` P1:7169–7498).

Conventions of the section, as modelled here. The annulus `Ω = {R₁ < |z| < R₂}`, the continuum `J` and the ring
domains `Ω₁`, `Ω₂` are subsets of `ℂ`, seen in `ℂ*` through `LiZhongQC.toExt` where a notion of `ℂ*` is used. A
continuum is a compact connected (hence non-empty) set. "`J` separates `Ω` into disjoint ring domains `Ω₁`, `Ω₂`" is
read: `Ω₁` and `Ω₂` are disjoint components of `Ω \ J` which are ring domains (`LehtoVirtanen1973.IsRingDomain`), with
the boundary circles as stated (the setting of Figure V.1; the helper `IsModulsatzConfig`). The module `mod` of a ring
domain is `ringModGM` (Ch. IV §1, the book's normalization `(1/2π) log(R/r)`, values in `[0, ∞]`). A "simply
connected domain" `G ⊆ ℂ` is `Gehring1978.IsHypSimplyConnectedExt (toExt G)`: every use here has a conformal map of
`𝔻` onto `G`, so the complement of `G` in `ℂ*` has at least two points. The reduced modulus `M(G)` is real valued
(`reducedModulus`, `reducedModulusInf`). "If `δ > 0` is sufficiently small, then there is a `C < ∞` independent of `J`
and `δ`" (Theorems 4.1, 4.2) is read with absolute constants: `∃ δ₀ > 0, ∃ C, ∀ J, ∀ δ ∈ (0, δ₀)` (inventory C12(b));
`δ₀ < 1` may be assumed, so `δ log(1/δ) > 0` and the square root in (4.3), (4.6) is never taken of a negative
number. `sup_J |z| / inf_J |z|` is the quotient of the real supremum and infimum of `|z|` over the compact set `J`;
here `inf_J |z| > 0` since `0 ∉ J`.

* Formula (4.1) (§4) — `eq5_4_1`
* Theorem 4.1 (Teichmüller's Modulsatz, §4; (4.2), (4.3)) — `thm5_4_1`
* Definition (simply connected domain, §4, P1:7198; used throughout V §4–§6) — exists:
  `Gehring1978.IsHypSimplyConnectedExt` (for the image in the extended plane of a plane set: open, connected, simply
  connected, with at least two points outside; every use of the book has a conformal map of the disc onto the domain)
* Definition (`M_ρ(G)`, §4, P1:7198–7201) — omitted: a notation, written out as the module of G minus the closed
  disc of radius ρ about 0 wherever it occurs
* Formula (4.4) (§4) — `eq5_4_4`
* Unlabelled (§4, P1:7210–7220): for a conformal map `φ : 𝔻 → G` with `φ(0) = 0`,
  `lim_{ρ→0} M_ρ(G) + (log ρ)/2π = (1/2π) log |φ'(0)|` — `tendsto_modulus_add_log`
* Definition (reduced modulus `M(G)` for `0 ∈ G` and for `∞ ∈ G`, §4, P1:7222–7226) — `reducedModulus`,
  `reducedModulusInf`
* Theorem 4.2 (Teichmüller's special Modulsatz, §4; (4.5), (4.6)) — `thm5_4_2`
* Corollary 4.3 (§4; (4.10)–(4.12); [CORRECTION]: `ε₀ < 1`, and `R₀ ≤ R` in (4.11)) — `cor5_4_3`

Helper (not a book notion): `IsModulsatzConfig` (the configuration of (4.1) and Theorem 4.1).

Corrections and readings: Theorem 4.1 prints "independent of Ω and δ" (P1:7190; the glyph is lost in the OCR — the
byte 0x03 there is this OCR's Ω, as in P1:7171 "separates Ω into"; the page image is not in the archive); `C` is
absolute — independent of `Ω` (i.e. of `R₁`, `R₂`), of `J` and of `δ` — as the derivation from Theorem 4.2 through
(4.4) gives (inventory C11(1)). Corollary 4.3 is false as printed, for `R → 1⁺` and for `ε₀ ≥ 1`; it is stated
for `ε₀ < 1` and, in (4.11), for `R₀ ≤ R ≤ e` with `C = C(ε₀, R₀)` [CORRECTION] (the excluded values `ε = 1` and a
vanishing denominator of inventory C11(3) no longer occur; `ε = 0` is the equality case of (4.13)). The
paragraph opening the case `R > e` of the proof of Corollary 4.3 is lost in the OCR (P1:7453–7468; proof only). App. K
cites "Theorem V.4.2" for `ω ≪ Λ₁ ≪ ω` (P3:5898): that is Theorem VI.4.2 [misprint] (inventory C11(7)), not
`thm5_4_2`.

Near misses (not the same theorem): `LehtoVirtanen1973.teichmuller_module_theorem` and
`LiZhongQC.thm5_3_teichmuller_modulus_theorem` are Teichmüller's extremal bound for ring domains separating
`{0, z₁}` from `{z₂, ∞}` (GM's Exercise IV.5(b), (E.2), P1:6562–6568, "Teichmüller's module theorem"), not the
Modulsatz of this section.

Not stated (inventory U−): the sentence "Theorem 4.1 says that if equality approximately holds in (4.1) then `J` is
approximately a circle centered at 0" (P1:7182, motivation); Teichmüller derived the Modulsatz from his special
Modulsatz (P1:7196, history); `2πM(G) = γ_{∂G}` when `∞ ∈ G` by Example III.1.1, and `M(G₁) + M(G₂) ≤ 0` with equality
when `J` is a circle (P1:7228–7234; not cited, the second is (4.1) passed to the limit and motivates (4.5)); "by
inequality (4.4), Theorem 4.1 is a corollary of Theorem 4.2" (P1:7248, the derivation); (4.13), `d_{Ω∖σ}(Γ₁, Γ₂) ≥
(1/2π) log R` by the extension rule, with equality for the radial slit (P1:7351–7357, immediate and used in the same
paragraph); the remarks that weaker forms of (4.3) and (4.11) are easier to prove (Exercise 4) and that Teichmüller's
slit cardioid shows (4.6) and (4.3) sharp (P1:7487–7497). (4.7)–(4.9) are steps of the proof of Theorem 4.2, and
(4.14)–(4.16) steps of the proof of Corollary 4.3.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf unitDisc annulus IsConformalOnto)
open LehtoVirtanen1973 (IsRingDomain extChartInv)
open References (finitePart)
open Gehring1978 (IsHypSimplyConnectedExt)

/-- Helper (Stage A, T0; bounded ring domains). A conformal map `ψ` of a ring domain `B` of `ℂ̄` with `∞ ∉ closure B`
onto the annulus `{r < |w| < R}` is, on the finite part `U = B ∩ ℂ` (open, bounded, `B = toExt U`), a plane conformal
bijection `U → {r < |w| < R}` with a plane conformal inverse `g`. -/
theorem gm5_ring_plane {B : Set ExtPlane} (hB : IsRingDomain B) {ψ : ExtPlane → ExtPlane} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hψ : LehtoVirtanen1973.IsConformalMap ψ B) (hψB : ψ '' B = toExt (annulus r R))
    (hbdd : extInf ∉ closure B) :
    ∃ g : ℂ → ℂ, B = toExt (finitePart B) ∧ Bornology.IsBounded (finitePart B) ∧ IsOpen (finitePart B) ∧
      IsConformalOnto (LehtoVirtanen1973.finiteMap ψ) (finitePart B) (annulus r R) ∧
      IsConformalOnto g (annulus r R) (finitePart B) ∧
      (∀ z ∈ finitePart B, g (LehtoVirtanen1973.finiteMap ψ z) = z) ∧
      ∀ w ∈ annulus r R, LehtoVirtanen1973.finiteMap ψ (g w) = w := by
  obtain ⟨⟨hBo, -⟩, hcont, hinj, hdiff⟩ := hψ
  have hBo' : IsOpen B := hBo
  set U := finitePart B with hU
  have hopen : IsOpen U := hBo'.preimage OnePoint.continuous_coe
  have hinfB : extInf ∉ B := fun h => hbdd (subset_closure h)
  have hBU : B = toExt U := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      refine ⟨fun h => absurd h hinfB, ?_⟩
      rintro ⟨z, _, hz⟩
      exact absurd hz (OnePoint.coe_ne_infty z)
    | coe z =>
      constructor
      · intro h; exact ⟨z, h, rfl⟩
      · rintro ⟨w, hw, hwz⟩; exact OnePoint.coe_injective hwz ▸ hw
  have hbd : Bornology.IsBounded U := by
    obtain ⟨s, ⟨-, hsc⟩, hs⟩ := (OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_iff.1
      ((isClosed_closure.isOpen_compl).mem_nhds (show extInf ∈ (closure B)ᶜ from hbdd))
    refine hsc.isBounded.subset fun z hz => ?_
    by_contra hzs
    have : (z : ExtPlane) ∈ (closure B)ᶜ := hs (Or.inl ⟨z, hzs, rfl⟩)
    exact this (subset_closure hz)
  have hfin : ∀ z ∈ U, ∃ w ∈ annulus r R, ψ (z : ExtPlane) = (w : ExtPlane) := fun z hz => by
    have : ψ (z : ExtPlane) ∈ toExt (annulus r R) := hψB ▸ mem_image_of_mem ψ hz
    obtain ⟨w, hw, hwz⟩ := this
    exact ⟨w, hw, hwz.symm⟩
  have hfm : ∀ z ∈ U, LehtoVirtanen1973.finiteMap ψ z ∈ annulus r R ∧
      ψ (z : ExtPlane) = ((LehtoVirtanen1973.finiteMap ψ z : ℂ) : ExtPlane) := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hfin z hz
    have : LehtoVirtanen1973.finiteMap ψ z = w := gm4d_finiteMap_coe ψ w z hwz
    rw [this]
    exact ⟨hw, hwz⟩
  have hdiffz : ∀ z ∈ U, DifferentiableAt ℂ (LehtoVirtanen1973.finiteMap ψ) z := fun z hz =>
    LehtoVirtanen1973.lv12_differentiableAt_of_localRep hopen (fun w hw => (hfm w hw).2) hz (hdiff _ hz)
  have hconf : IsConformalOnto (LehtoVirtanen1973.finiteMap ψ) U (annulus r R) := by
    refine ⟨fun z hz => (hdiffz z hz).differentiableWithinAt, fun a ha b hb hab => ?_, ?_⟩
    · apply OnePoint.coe_injective
      apply hinj ha hb
      rw [(hfm a ha).2, (hfm b hb).2, hab]
    · ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hfm z hz).1
      · intro hw
        have : (w : ExtPlane) ∈ ψ '' B := hψB ▸ ⟨w, hw, rfl⟩
        obtain ⟨p, hp, hpw⟩ := this
        induction p using OnePoint.rec with
        | infty => exact absurd hp hinfB
        | coe z =>
          refine ⟨z, hp, ?_⟩
          exact gm4d_finiteMap_coe ψ w z hpw
  have hbij : Set.BijOn (LehtoVirtanen1973.finiteMap ψ) U (annulus r R) :=
    ⟨fun z hz => (hfm z hz).1, hconf.2.1, hconf.2.2.symm.subset⟩
  have hinv : Set.BijOn (Function.invFunOn (LehtoVirtanen1973.finiteMap ψ) U) (annulus r R) U :=
    hbij.symm hbij.invOn_invFunOn.symm
  obtain ⟨-, hd⟩ := RMT.differentiableOn_invFunOn_of_injOn hopen hconf.1 hconf.2.1
  rw [hconf.2.2] at hd
  exact ⟨Function.invFunOn (LehtoVirtanen1973.finiteMap ψ) U, hBU, hbd, hopen, hconf, ⟨hd, hinv.injOn, hinv.image_eq⟩,
    fun z hz => hbij.invOn_invFunOn.1 hz, fun w hw => hbij.invOn_invFunOn.2 hw⟩

/-- Helper (Stage A): `annulus r R` is open. -/
theorem gm5_isOpen_annulus (r R : ℝ) : IsOpen (annulus r R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- Helper (Stage A): the upper bound `λ_U(Γ) ≤ 2π/log(R/r)` when `Γ` contains the conformal images of all circles. -/
theorem gm5_extLen_le {U : Set ℂ} {g : ℂ → ℂ} {r R : ℝ} {Γ : Set (Set ℂ)} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hΓ : ∀ s ∈ Ioo r R, g '' sphere 0 s ∈ Γ) :
    extremalLengthGM U Γ ≤ ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  have hAo := gm5_isOpen_annulus r R
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hρm, hρ0, hρt⟩ := gm4a_mem_densitiesP0.1 hρ
  set ρ' : ℂ → ℝ≥0∞ := (annulus r R).indicator fun w => ρ (g w) * ‖deriv g w‖ₑ with hρ'
  have harea : LiZhongQC.rhoArea ρ' (annulus r R) = LiZhongQC.rhoArea ρ U := by
    rw [hρ']; exact LiZhongQC.rhoArea_pullback hAo hg ρ
  have hρ'P : ρ' ∈ LiZhongQC.densitiesP0 (annulus r R) :=
    ⟨LiZhongQC.measurable_pullback_density hAo hg.1.continuousOn hρm, harea ▸ hρ0, harea ▸ hρt⟩
  set Γ' : Set (Set ℂ) := {γ' | ∃ s ∈ Ioo r R, γ' = sphere 0 s} with hΓ'
  have hratio := gm4c_annulus_circles_ratio_le_ae hr hrR (Γ := Γ')
    (fun s hs => ⟨sphere 0 s, ⟨s, hs, rfl⟩, ae_eq_refl _⟩) hρ'P
  have hlen : pathRhoLength Γ ρ ≤ pathRhoLength Γ' ρ' := by
    refine le_iInf₂ fun γ' hγ' => ?_
    obtain ⟨s, hs, rfl⟩ := hγ'
    have hsub : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
      rw [mem_sphere_zero_iff_norm] at hz
      exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩
    have hmeas : MeasurableSet (sphere (0 : ℂ) s) := isClosed_sphere.measurableSet
    have := gm4b_lintegral_image_conformal hAo hg hmeas hsub hρm
    refine (iInf₂_le (g '' sphere 0 s) (hΓ s hs)).trans (le_of_eq ?_)
    rw [this]
    refine setLIntegral_congr_fun hmeas fun z hz => ?_
    simp only [hρ', indicator_of_mem (hsub hz)]
  calc pathRhoLength Γ ρ ^ 2 / LiZhongQC.rhoArea ρ U
      ≤ pathRhoLength Γ' ρ' ^ 2 / LiZhongQC.rhoArea ρ' (annulus r R) := by
        rw [harea]
        gcongr
    _ ≤ _ := hratio

/-- Helper (Stage A): a decreasing intersection of compact connected sets of `ℂ` is connected. -/
theorem gm5_nested_connected {F : ℕ → Set ℂ} (hc : ∀ n, IsCompact (F n)) (hconn : ∀ n, IsConnected (F n))
    (hanti : Antitone F) : IsConnected (⋂ n, F n) := by
  have hne : (⋂ n, F n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F (fun i => hanti (Nat.le_succ i))
      (fun n => (hconn n).nonempty) (hc 0) (fun n => (hc n).isClosed)
  refine ⟨hne, ?_⟩
  set K := ⋂ n, F n with hK
  have hKc : IsCompact K := (hc 0).of_isClosed_subset (isClosed_iInter fun n => (hc n).isClosed)
    (iInter_subset _ 0)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hKuv hKdis
  have hK1 : IsCompact (K ∩ u) := hKc.inter_right hu
  have hK2 : IsCompact (K ∩ v) := hKc.inter_right hv
  have hdisj : Disjoint (K ∩ u) (K ∩ v) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzK, hzu⟩ ⟨-, hzv⟩
    have : z ∈ K ∩ (u ∩ v) := ⟨hzK, hzu, hzv⟩
    rw [hKdis] at this
    exact this
  obtain ⟨U₁, U₂, hU₁, hU₂, h1, h2, hU12⟩ := SeparatedNhds.of_isCompact_isCompact hK1 hK2 hdisj
  have hKU : K ⊆ U₁ ∪ U₂ := fun z hz => by
    rcases hKuv hz with h | h
    · exact Or.inl (h1 ⟨hz, h⟩)
    · exact Or.inr (h2 ⟨hz, h⟩)
  have hex : ∃ n, F n ⊆ U₁ ∪ U₂ := by
    by_contra hno
    push Not at hno
    have hne : (⋂ n, F n ∩ (U₁ ∪ U₂)ᶜ).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun n => F n ∩ (U₁ ∪ U₂)ᶜ)
        (fun i => inter_subset_inter (hanti (Nat.le_succ i)) subset_rfl) (fun n => ?_) ?_ (fun n => ?_)
      · obtain ⟨z, hz, hz'⟩ := not_subset.1 (hno n)
        exact ⟨z, hz, hz'⟩
      · exact (hc 0).inter_right (hU₁.union hU₂).isClosed_compl
      · exact (hc n).isClosed.inter (hU₁.union hU₂).isClosed_compl
    obtain ⟨z, hz⟩ := hne
    rw [mem_iInter] at hz
    exact (hz 0).2 (hKU (mem_iInter.2 fun n => (hz n).1))
  obtain ⟨n, hn⟩ := hex
  rcases (hconn n).isPreconnected.subset_or_subset hU₁ hU₂ hU12 hn with h | h
  · left
    intro z hz
    rcases hKuv hz with hzu | hzv
    · exact hzu
    · exfalso
      have a1 : z ∈ U₁ := h (iInter_subset F n hz)
      have a2 : z ∈ U₂ := h2 ⟨hz, hzv⟩
      exact Set.disjoint_left.1 hU12 a1 a2
  · right
    intro z hz
    rcases hKuv hz with hzu | hzv
    · exfalso
      have a1 : z ∈ U₁ := h1 ⟨hz, hzu⟩
      have a2 : z ∈ U₂ := h (iInter_subset F n hz)
      exact Set.disjoint_left.1 hU12 a1 a2
    · exact hzv

/-- Helper (Stage A): a ring domain has two distinct components of its complement; the frontier is not preconnected. -/
theorem gm5_frontier_not_conn {B : Set ExtPlane} (hB : IsRingDomain B) : ¬ IsPreconnected (frontier B) := by
  obtain ⟨⟨hBo, hBc⟩, -, hcard⟩ := hB
  intro hpre
  have hfin : Finite (ConnectedComponents ↥Bᶜ) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨a, b, hab, -⟩ := Nat.card_eq_two_iff.1 hcard
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  have hxy : connectedComponentIn Bᶜ (x : ExtPlane) ≠ connectedComponentIn Bᶜ (y : ExtPlane) := by
    intro h
    apply hab
    rw [ConnectedComponents.coe_eq_coe]
    have hy : (y : ExtPlane) ∈ connectedComponentIn Bᶜ (x : ExtPlane) := by
      rw [h]; exact mem_connectedComponentIn y.2
    rw [connectedComponentIn_eq_image x.2] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rw [this] at hy'
    exact connectedComponent_eq hy'
  have hfrB : frontier B ⊆ Bᶜ := fun f hf hfB => hf.2 (interior_maximal subset_rfl hBo hfB)
  have hBne : B.Nonempty := hBc.nonempty
  by_cases hfne : (frontier B).Nonempty
  · obtain ⟨f, hf⟩ := hfne
    have hfsub : frontier B ⊆ connectedComponentIn Bᶜ f := hpre.subset_connectedComponentIn hf hfrB
    -- a component different from that of `f`
    obtain ⟨z, hzB, hzf⟩ : ∃ z : ExtPlane, z ∈ Bᶜ ∧
        connectedComponentIn Bᶜ z ≠ connectedComponentIn Bᶜ f := by
      by_cases h1 : connectedComponentIn Bᶜ (x : ExtPlane) = connectedComponentIn Bᶜ f
      · refine ⟨y, y.2, fun h2 => hxy ?_⟩
        rw [h1, h2]
      · exact ⟨x, x.2, h1⟩
    set E' := connectedComponentIn Bᶜ z with hE'
    have hdisjE : Disjoint E' (connectedComponentIn Bᶜ f) := by
      rw [Set.disjoint_left]
      intro w hw hwf
      exact hzf ((connectedComponentIn_eq hw).trans (connectedComponentIn_eq hwf).symm)
    have hzE : z ∈ E' := mem_connectedComponentIn hzB
    have hclosed : IsClosed E' := by
      have hcl : closure E' ⊆ E' := by
        have hpc : IsPreconnected (closure E') := isPreconnected_connectedComponentIn.closure
        have hsub : closure E' ⊆ Bᶜ := closure_minimal (connectedComponentIn_subset _ _) hBo.isClosed_compl
        exact hpc.subset_connectedComponentIn (subset_closure hzE) hsub
      exact closure_subset_iff_isClosed.1 hcl
    have hopen : IsOpen E' := by
      rw [isOpen_iff_mem_nhds]
      intro e he
      have heB : e ∈ Bᶜ := connectedComponentIn_subset _ _ he
      have hefr : e ∉ frontier B := fun h => Set.disjoint_left.1 hdisjE he (hfsub h)
      have hecl : e ∉ closure B := by
        rw [closure_eq_interior_union_frontier, hBo.interior_eq]
        rintro (h | h)
        · exact heB h
        · exact hefr h
      obtain ⟨V, ⟨hVo, heV, hVc⟩, hVsub⟩ := (LocallyConnectedSpace.open_connected_basis e).mem_iff.1
        (isClosed_closure.isOpen_compl.mem_nhds hecl)
      have hVB : V ⊆ Bᶜ := fun w hw hwB => hVsub hw (subset_closure hwB)
      have : V ⊆ connectedComponentIn Bᶜ e := hVc.isPreconnected.subset_connectedComponentIn heV hVB
      refine Filter.mem_of_superset (hVo.mem_nhds heV) ?_
      rw [hE', connectedComponentIn_eq he]
      exact this
    have huniv : E' = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨z, hzE⟩
    obtain ⟨bpt, hbpt⟩ := hBne
    have : bpt ∈ E' := huniv ▸ mem_univ bpt
    exact connectedComponentIn_subset _ _ this hbpt
  · -- the frontier is empty: `B` is clopen
    rw [not_nonempty_iff_eq_empty] at hfne
    have hBcl : IsClosed B := by
      rw [← closure_subset_iff_isClosed, closure_eq_interior_union_frontier, hBo.interior_eq, hfne, union_empty]
    have huniv : B = univ := IsClopen.eq_univ ⟨hBcl, hBo⟩ hBne
    exact (huniv ▸ x.2 : (x : ExtPlane) ∈ (univ : Set ExtPlane)ᶜ) (mem_univ _)

/-- Helper (Stage A, T2; the frontier components). If `Cin`, `Cout` are disjoint compact connected sets of `ℂ`, the
connected components of `toExt Cin ∪ toExt Cout` are `toExt Cin` and `toExt Cout`. -/
theorem gm5_frontier_comps {Cin Cout : Set ℂ} (hc₁ : IsConnected Cin) (hc₂ : IsConnected Cout)
    (hk₁ : IsCompact Cin) (hk₂ : IsCompact Cout) (hd : Disjoint Cin Cout) :
    (∀ x ∈ toExt Cin, connectedComponentIn (toExt Cin ∪ toExt Cout) x = toExt Cin) ∧
      ∀ x ∈ toExt Cout, connectedComponentIn (toExt Cin ∪ toExt Cout) x = toExt Cout := by
  have hcl₁ : IsClosed (toExt Cin) := (hk₁.image OnePoint.continuous_coe).isClosed
  have hcl₂ : IsClosed (toExt Cout) := (hk₂.image OnePoint.continuous_coe).isClosed
  have hp₁ : IsPreconnected (toExt Cin) := hc₁.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hp₂ : IsPreconnected (toExt Cout) := hc₂.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hdE : Disjoint (toExt Cin) (toExt Cout) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    exact Set.disjoint_left.1 hd hp (OnePoint.coe_injective hqp ▸ hq)
  have key : ∀ {K₁ K₂ : Set ExtPlane}, IsClosed K₁ → IsClosed K₂ → IsPreconnected K₁ → Disjoint K₁ K₂ →
      ∀ x ∈ K₁, connectedComponentIn (K₁ ∪ K₂) x = K₁ := by
    intro K₁ K₂ h1 h2 hp hd x hx
    refine subset_antisymm ?_ (hp.subset_connectedComponentIn hx subset_union_left)
    have hx' : x ∈ connectedComponentIn (K₁ ∪ K₂) x := mem_connectedComponentIn (Or.inl hx)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn K₁ K₂ h1 h2
      (connectedComponentIn_subset _ _) (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, hz1, hz2⟩
        exact Set.disjoint_left.1 hd hz1 hz2) with h | h
    · exact h
    · exact absurd (h hx') (Set.disjoint_left.1 hd hx)
  refine ⟨key hcl₁ hcl₂ hp₁ hdE, ?_⟩
  intro x hx
  rw [union_comm]
  exact key hcl₂ hcl₁ hp₂ hdE.symm x hx

/-- Helper (Stage A, T5; a set meeting every ray has `|dw|/|w|`-length at least `2π`). -/
theorem gm5_angle {S : Set ℂ} (hS : MeasurableSet S) (h0 : (0 : ℂ) ∉ S)
    (hray : ∀ θ : ℝ, ∃ t : ℝ, 0 < t ∧ ((t : ℂ) * exp (θ * I)) ∈ S) :
    ENNReal.ofReal (2 * π) ≤ ∫⁻ w in S, ENNReal.ofReal (1 / ‖w‖) ∂μH[1] := by
  have hsub : Ioo (-π) π ⊆ arg '' (S ∩ slitPlane) := by
    intro θ hθ
    obtain ⟨t, ht, hmem⟩ := hray θ
    have harg : arg ((t : ℂ) * exp (θ * I)) = θ := by
      rw [arg_real_mul _ ht, exp_mul_I]
      exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
    have hne : (t : ℂ) * exp (θ * I) ≠ 0 := fun h => h0 (h ▸ hmem)
    exact ⟨_, ⟨hmem, mem_slitPlane_iff_arg.2 ⟨by rw [harg]; exact hθ.2.ne, hne⟩⟩, harg⟩
  calc ENNReal.ofReal (2 * π) = μH[1] (Ioo (-π) π) := by
        rw [hausdorffMeasure_real, Real.volume_Ioo]
        congr 1
        ring
    _ ≤ μH[1] (arg '' (S ∩ slitPlane)) := measure_mono hsub
    _ ≤ ∫⁻ z in S ∩ slitPlane, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] :=
        gm4b_hausdorff_arg_le (hS.inter isOpen_slitPlane.measurableSet) inter_subset_right
    _ ≤ ∫⁻ z in S, ENNReal.ofReal ‖z‖⁻¹ ∂μH[1] := lintegral_mono_set inter_subset_left
    _ = ∫⁻ w in S, ENNReal.ofReal (1 / ‖w‖) ∂μH[1] := by simp only [one_div]

/-- Helper (Stage A): the closure of the inner part of `g(annulus)` lies in `U` or in the inner cluster set. -/
theorem gm5_closure_in {U : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} {Cin : Set ℂ} (hg : IsConformalOnto g (annulus r R) U)
    (hCin : ∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})) (hsR : s < R) :
    closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < s}) ⊆ U ∪ Cin := by
  intro p hp
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose w hw hxw using hxmem
  have hK : IsCompact ({w : ℂ | r ≤ ‖w‖} ∩ closedBall 0 s) :=
    (isCompact_closedBall 0 s).inter_left (isClosed_le continuous_const continuous_norm)
  have hwK : ∀ n, w n ∈ {w : ℂ | r ≤ ‖w‖} ∩ closedBall 0 s := fun n =>
    ⟨(hw n).1.le, mem_closedBall_zero_iff.2 (hw n).2.le⟩
  obtain ⟨q, hqK, φ, hφ, hqlim⟩ := hK.tendsto_subseq hwK
  have hqn : r ≤ ‖q‖ := hqK.1
  have hqs : ‖q‖ ≤ s := mem_closedBall_zero_iff.1 hqK.2
  have hlim : Tendsto (fun n => g (w (φ n))) atTop (𝓝 p) := by
    have := hxlim.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, hxw]
  rcases hqn.lt_or_eq with hrq | hrq
  · left
    have hqA : q ∈ annulus r R := ⟨hrq, lt_of_le_of_lt hqs hsR⟩
    have hgq : Tendsto (fun n => g (w (φ n))) atTop (𝓝 (g q)) :=
      (hg.1.continuousOn.continuousAt (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const) |>.mem_nhds hqA)).tendsto.comp hqlim
    have : p = g q := tendsto_nhds_unique hlim hgq
    rw [this]
    exact hg.2.2 ▸ mem_image_of_mem g hqA
  · right
    refine (hCin p).2 fun ε hε => mem_closure_of_tendsto hlim ?_
    have hn : Tendsto (fun n => ‖w (φ n)‖) atTop (𝓝 r) := by
      rw [hrq]; exact (continuous_norm.tendsto q).comp hqlim
    filter_upwards [hn.eventually (gt_mem_nhds (by linarith : r < r + ε))] with n hn
    exact ⟨w (φ n), ⟨(hw (φ n)).1, hn⟩, rfl⟩

/-- Helper (Stage A): the closure of the outer part of `g(annulus)` lies in `U` or in the outer cluster set. -/
theorem gm5_closure_out {U : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} {Cout : Set ℂ} (hg : IsConformalOnto g (annulus r R) U)
    (hCout : ∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})) (hrs : r < s) :
    closure (g '' {w | s < ‖w‖ ∧ ‖w‖ < R}) ⊆ U ∪ Cout := by
  intro p hp
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose w hw hxw using hxmem
  have hK : IsCompact ({w : ℂ | s ≤ ‖w‖} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_norm)
  have hwK : ∀ n, w n ∈ {w : ℂ | s ≤ ‖w‖} ∩ closedBall 0 R := fun n =>
    ⟨(hw n).1.le, mem_closedBall_zero_iff.2 (hw n).2.le⟩
  obtain ⟨q, hqK, φ, hφ, hqlim⟩ := hK.tendsto_subseq hwK
  have hqn : s ≤ ‖q‖ := hqK.1
  have hqs : ‖q‖ ≤ R := mem_closedBall_zero_iff.1 hqK.2
  have hlim : Tendsto (fun n => g (w (φ n))) atTop (𝓝 p) := by
    have := hxlim.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, hxw]
  rcases hqs.lt_or_eq with hrq | hrq
  · left
    have hqA : q ∈ annulus r R := ⟨lt_of_lt_of_le hrs hqn, hrq⟩
    have hgq : Tendsto (fun n => g (w (φ n))) atTop (𝓝 (g q)) :=
      (hg.1.continuousOn.continuousAt (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const) |>.mem_nhds hqA)).tendsto.comp hqlim
    have : p = g q := tendsto_nhds_unique hlim hgq
    rw [this]
    exact hg.2.2 ▸ mem_image_of_mem g hqA
  · right
    refine (hCout p).2 fun ε hε => mem_closure_of_tendsto hlim ?_
    have hn : Tendsto (fun n => ‖w (φ n)‖) atTop (𝓝 R) := by
      rw [← hrq]; exact (continuous_norm.tendsto q).comp hqlim
    filter_upwards [hn.eventually (lt_mem_nhds (by linarith : R - ε < R))] with n hn
    exact ⟨w (φ n), ⟨hn, (hw (φ n)).2⟩, rfl⟩

/-- Helper (Stage A): a conformal map `g` of an open set is an embedding of that set (as a subtype). -/
theorem gm5_conformal_embedding {A V : Set ℂ} {g : ℂ → ℂ} (hA : IsOpen A) (hg : IsConformalOnto g A V) :
    IsEmbedding (A.domRestrict g) := by
  have hcont : Continuous (A.domRestrict g) := hg.1.continuousOn.domRestrict
  have hinj : Function.Injective (A.domRestrict g) := fun a b h => Subtype.ext (hg.2.1 a.2 b.2 h)
  have hopen : IsOpenMap (A.domRestrict g) := by
    intro W hW
    obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
    have : A.domRestrict g '' (Subtype.val ⁻¹' W') = g '' (A ∩ W') := by
      ext y
      simp only [mem_image, mem_preimage, Set.domRestrict_apply, Subtype.exists, mem_inter_iff]
      constructor
      · rintro ⟨a, ha, haW, rfl⟩; exact ⟨a, ⟨ha, haW⟩, rfl⟩
      · rintro ⟨a, ⟨ha, haW⟩, rfl⟩; exact ⟨a, ha, haW, rfl⟩
    rw [this]
    exact (RMT.differentiableOn_invFunOn_of_injOn (hA.inter hW') (hg.1.mono inter_subset_left)
      (hg.2.1.mono inter_subset_left)).1
  exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isEmbedding

/-- Helper (Stage A): the conformal image of an embedded arc inside the domain is an embedded arc. -/
theorem gm5_arc_embedding {A V : Set ℂ} {g : ℂ → ℂ} (hA : IsOpen A) (hg : IsConformalOnto g A V) {I : Set ℝ}
    {k : ℝ → ℂ} (hk : IsEmbedding (I.domRestrict k)) (hkA : ∀ t ∈ I, k t ∈ A) :
    IsEmbedding (I.domRestrict (fun t => g (k t))) := by
  have hkA' : IsEmbedding (fun x : I => (⟨k x, hkA x x.2⟩ : A)) := by
    refine IsEmbedding.of_comp (g := (Subtype.val : A → ℂ)) ?_ continuous_subtype_val hk
    exact Continuous.subtype_mk hk.continuous _
  exact (gm5_conformal_embedding hA hg).comp hkA'

/-- Helper (Stage A, T3a): the analytic Jordan curve `g(|w| = s)` is a path curve in `U`. -/
theorem gm5_circle_pathCurve {U : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} (hr : 0 < r)
    (hg : IsConformalOnto g (annulus r R) U) (hs : s ∈ Ioo r R) : IsPathCurve U (g '' sphere 0 s) := by
  have hs0 : 0 < s := hr.trans hs.1
  have hAo := gm5_isOpen_annulus r R
  have hk := gm4b_circle_arc_emb hs0
  set k₁ : ℝ → ℂ := fun θ => (s : ℂ) * exp (θ * I) with hk₁
  set k₂ : ℝ → ℂ := fun θ => -((s : ℂ) * exp (θ * I)) with hk₂
  have hnorm : ∀ θ : ℝ, ‖k₁ θ‖ = s := fun θ => by
    simp only [hk₁]
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hsubA : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩
  have hk₁A : ∀ t ∈ Ioo (-π) π, k₁ t ∈ annulus r R := fun t _ =>
    hsubA (by rw [mem_sphere_zero_iff_norm]; exact hnorm t)
  have hk₂A : ∀ t ∈ Ioo (-π) π, k₂ t ∈ annulus r R := fun t _ =>
    hsubA (by rw [mem_sphere_zero_iff_norm, hk₂, norm_neg]; exact hnorm t)
  have hemb₁ := gm5_arc_embedding hAo hg hk hk₁A
  have hk₂emb : IsEmbedding ((Ioo (-π) π).domRestrict k₂) := (Homeomorph.neg ℂ).isEmbedding.comp hk
  have hemb₂ := gm5_arc_embedding hAo hg hk₂emb hk₂A
  have hfin : μH[1] (g '' sphere 0 s) < ⊤ := by
    have hmeas : MeasurableSet (sphere (0 : ℂ) s) := isClosed_sphere.measurableSet
    refine lt_of_le_of_lt (gm4b_hausdorff_image_le hAo hg hmeas hsubA) ?_
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) s).exists_bound_of_continuousOn
      (f := fun z => deriv g z) (by
        intro z hz
        exact (hg.1.analyticOnNhd hAo z (hsubA hz)).deriv.continuousAt.continuousWithinAt)
    calc ∫⁻ z in sphere 0 s, ‖deriv g z‖ₑ ∂μH[1] ≤ ∫⁻ _z : ℂ in sphere 0 s, ENNReal.ofReal C ∂μH[1] := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hC z hz)
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (gm4b_hausdorff_sphere_lt_top hs0)
  have hnt : (Ioo (-π) π).Nontrivial := ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos⟩, 1, ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩, by norm_num⟩
  have hsub₁ : (fun t => g (k₁ t)) '' Ioo (-π) π ⊆ g '' sphere 0 s := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨k₁ t, by rw [mem_sphere_zero_iff_norm]; exact hnorm t, rfl⟩
  have hsub₂ : (fun t => g (k₂ t)) '' Ioo (-π) π ⊆ g '' sphere 0 s := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨k₂ t, by rw [mem_sphere_zero_iff_norm, hk₂, norm_neg]; exact hnorm t, rfl⟩
  have hArc₁ := gm4b_isRectifiableArc_of_embedding ordConnected_Ioo hnt hemb₁ ((measure_mono hsub₁).trans_lt hfin)
  have hArc₂ := gm4b_isRectifiableArc_of_embedding ordConnected_Ioo hnt hemb₂ ((measure_mono hsub₂).trans_lt hfin)
  have hUsub : g '' sphere 0 s ⊆ U := hg.2.2 ▸ image_mono hsubA
  refine ⟨fun n => if n = 0 then (fun t => g (k₁ t)) '' Ioo (-π) π else (fun t => g (k₂ t)) '' Ioo (-π) π,
    fun n => ?_, ?_⟩
  · by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact ⟨hArc₁, hsub₁.trans hUsub⟩
    · simp only [hn, ↓reduceIte]
      exact ⟨hArc₂, hsub₂.trans hUsub⟩
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwn : ‖w‖ = s := mem_sphere_zero_iff_norm.1 hw
      by_cases harg : arg w = π
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp only [one_ne_zero, ↓reduceIte]
        refine ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos⟩, ?_⟩
        have h := norm_mul_exp_arg_mul_I w
        rw [harg, hwn, exp_pi_mul_I] at h
        simp only [hk₂, ofReal_zero, zero_mul, exp_zero, mul_one]
        rw [← h]
        ring_nf
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp only [↓reduceIte]
        refine ⟨arg w, ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) harg⟩, ?_⟩
        have h := norm_mul_exp_arg_mul_I w
        rw [hwn] at h
        simp only [hk₁]
        rw [h]
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte] at hn
        exact hsub₁ hn
      · simp only [h0, ↓reduceIte] at hn
        exact hsub₂ hn

/-- Helper (Stage A): the conformal image of an open subset of the domain is open. -/
theorem gm5_image_open {A V : Set ℂ} {g : ℂ → ℂ} {W : Set ℂ} (hg : IsConformalOnto g A V) (hW : IsOpen W)
    (hWA : W ⊆ A) : IsOpen (g '' W) :=
  (RMT.differentiableOn_invFunOn_of_injOn hW (hg.1.mono hWA) (hg.2.1.mono hWA)).1

/-- Helper (Stage A, T3; the conformal circles separate). For `s ∈ (r, R)` the analytic Jordan curve `g({|w| = s})`
belongs to the family of curves in `U` separating the two ends `Cin` and `Cout`. -/
theorem gm5_circle_sep {U : Set ℂ} {g : ℂ → ℂ} {r R : ℝ} {Cin Cout : Set ℂ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hbdd : Bornology.IsBounded U)
    (hCin : ∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε}))
    (hCout : ∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R}))
    (hdisj : Disjoint Cin Cout) (hfr : frontier (toExt U) = toExt Cin ∪ toExt Cout) {s : ℝ} (hs : s ∈ Ioo r R) :
    g '' sphere 0 s ∈ separatingFamily U Cin Cout := by
  have hs0 : 0 < s := hr.trans hs.1
  have hAo := gm5_isOpen_annulus r R
  have hUo : IsOpen U := by
    have := gm5_image_open hg hAo subset_rfl
    rwa [hg.2.2] at this
  have hsubA : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩
  -- the clusters sets avoid `U`
  have hfrU : ∀ p : ℂ, (p : ExtPlane) ∈ frontier (toExt U) → p ∉ U := by
    intro p hp hpU
    have hopen : IsOpen (toExt U) := OnePoint.isOpenEmbedding_coe.isOpenMap _ hUo
    have : (p : ExtPlane) ∈ interior (toExt U) := interior_maximal subset_rfl hopen ⟨p, hpU, rfl⟩
    exact hp.2 this
  have hCinU : ∀ p ∈ Cin, p ∉ U := fun p hp => hfrU p (hfr ▸ Or.inl ⟨p, hp, rfl⟩)
  have hCoutU : ∀ p ∈ Cout, p ∉ U := fun p hp => hfrU p (hfr ▸ Or.inr ⟨p, hp, rfl⟩)
  refine ⟨gm5_circle_pathCurve hr hg hs, ?_, ?_⟩
  · obtain ⟨k, hkc, hk01, hksph⟩ := gm4b_circle_closed hs0
    refine ⟨{g '' sphere 0 s}, finite_singleton _, by simp, fun c hc => Or.inr ?_⟩
    rw [mem_singleton_iff.1 hc]
    refine ⟨fun t => g (k t), ?_, by simp only [hk01], by rw [hksph, image_image]⟩
    refine hg.1.continuousOn.comp hkc fun t ht => hsubA (hksph ▸ mem_image_of_mem k ht)
  · rintro x hx ⟨⟨pi, hpi, hpiC⟩, ⟨po, hpo, hpoC⟩⟩
    set Ain : Set ℂ := {w | r < ‖w‖ ∧ ‖w‖ < s} with hAin
    set Aout : Set ℂ := {w | s < ‖w‖ ∧ ‖w‖ < R} with hAout
    have hAinO : IsOpen Ain := isOpen_lt continuous_const continuous_norm |>.inter
      (isOpen_lt continuous_norm continuous_const)
    have hAoutO : IsOpen Aout := isOpen_lt continuous_const continuous_norm |>.inter
      (isOpen_lt continuous_norm continuous_const)
    have hAinA : Ain ⊆ annulus r R := fun w hw => ⟨hw.1, hw.2.trans hs.2⟩
    have hAoutA : Aout ⊆ annulus r R := fun w hw => ⟨hs.1.trans hw.1, hw.2⟩
    have hdis : Disjoint (g '' Ain) (g '' Aout) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := hg.2.1 (hAoutA hb) (hAinA ha) hab
      rw [this] at hb
      linarith [ha.2, hb.1]
    have hcov : U \ g '' sphere 0 s ⊆ g '' Ain ∪ g '' Aout := by
      rintro z ⟨hzU, hzγ⟩
      rw [← hg.2.2] at hzU
      obtain ⟨w, hwA, rfl⟩ := hzU
      have hne : ‖w‖ ≠ s := fun h => hzγ ⟨w, mem_sphere_zero_iff_norm.2 h, rfl⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨w, ⟨hwA.1, h⟩, rfl⟩
      · exact Or.inr ⟨w, ⟨h, hwA.2⟩, rfl⟩
    have hxU : x ∈ U := hx.1
    set K := connectedComponentIn (U \ g '' sphere 0 s) x with hK
    have hxK : x ∈ K := mem_connectedComponentIn hx
    have hKsub : K ⊆ g '' Ain ∪ g '' Aout := (connectedComponentIn_subset _ _).trans hcov
    have hxcov := hcov hx
    rcases hxcov with hxin | hxout
    · have hKin : K ⊆ g '' Ain :=
        isPreconnected_connectedComponentIn.subset_left_of_subset_union (gm5_image_open hg hAinO hAinA)
          (gm5_image_open hg hAoutO hAoutA) hdis hKsub ⟨x, hxK, hxin⟩
      have := gm5_closure_in hg hCin hs.2 (closure_mono hKin hpo)
      rcases this with h | h
      · exact hCoutU po hpoC h
      · exact Set.disjoint_left.1 hdisj h hpoC
    · have hKout : K ⊆ g '' Aout :=
        isPreconnected_connectedComponentIn.subset_right_of_subset_union (gm5_image_open hg hAinO hAinA)
          (gm5_image_open hg hAoutO hAoutA) hdis hKsub ⟨x, hxK, hxout⟩
      have := gm5_closure_out hg hCout hs.1 (closure_mono hKout hpi)
      rcases this with h | h
      · exact hCinU pi hpiC h
      · exact Set.disjoint_left.1 hdisj hpiC h

/-- Helper (Stage A): an open round annulus piece is preconnected. -/
theorem gm5_annulus_conn {a : ℝ} (ha : 0 ≤ a) (b : ℝ) : IsPreconnected {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} := by
  have hc : IsPreconnected (Ioo a b ×ˢ (univ : Set ℝ)) := isPreconnected_Ioo.prod isPreconnected_univ
  have himg := hc.image (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (by
    have : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
      simp only [LiZhongQC.kn_circleMap_eq]
      fun_prop
    exact this.continuousOn)
  convert himg using 1
  ext z
  simp only [Set.mem_ofPred_eq, mem_image, mem_prod, mem_Ioo, mem_univ, and_true, Prod.exists]
  constructor
  · intro hz
    refine ⟨‖z‖, Complex.arg z, hz, ?_⟩
    rw [circleMap_zero, ← Complex.norm_mul_exp_arg_mul_I z]
    simp [Complex.norm_mul_exp_arg_mul_I]
  · rintro ⟨r, θ, hr, rfl⟩
    rw [norm_circleMap_zero, abs_of_nonneg (ha.trans hr.1.le)]
    exact hr

/-- Helper (Stage A): the inner cluster set is compact, connected and misses `U`. -/
theorem gm5_cin_props {U : Set ℂ} {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hbdd : Bornology.IsBounded U) :
    IsCompact {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})} ∧
      IsConnected {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})} ∧
      ∀ p ∈ {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})}, p ∉ U := by
  have hAo := gm5_isOpen_annulus r R
  set Cin : Set ℂ := {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})} with hCin
  have hcl : IsCompact (closure U) := hbdd.isCompact_closure
  set δ : ℕ → ℝ := fun n => (R - r) / ((n : ℝ) + 2) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos (by linarith) (by positivity)
  have hδR : ∀ n, δ n < R - r := fun n => by
    rw [hδ, div_lt_iff₀ (by positivity)]
    nlinarith [(by linarith : (0 : ℝ) < R - r), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδanti : Antitone δ := fun m n hmn => by
    simp only [hδ]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
  have hsubA : ∀ n, {w : ℂ | r < ‖w‖ ∧ ‖w‖ < r + δ n} ⊆ annulus r R := fun n w hw =>
    ⟨hw.1, by linarith [hw.2, hδR n]⟩
  set F : ℕ → Set ℂ := fun n => closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + δ n}) with hF
  have hFsubU : ∀ n, g '' {w | r < ‖w‖ ∧ ‖w‖ < r + δ n} ⊆ U := fun n =>
    hg.2.2 ▸ image_mono (hsubA n)
  have hFc : ∀ n, IsCompact (F n) := fun n =>
    hcl.of_isClosed_subset isClosed_closure (closure_mono (hFsubU n))
  have hFconn : ∀ n, IsConnected (F n) := fun n => by
    refine ⟨?_, ?_⟩
    · have hw₁ : (((r + δ n / 2 : ℝ)) : ℂ) ∈ {w : ℂ | r < ‖w‖ ∧ ‖w‖ < r + δ n} := by
        have h0 : (0 : ℝ) ≤ r + δ n / 2 := by linarith [hδpos n]
        simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg h0]
        constructor <;> linarith [hδpos n]
      have hne : (g '' {w : ℂ | r < ‖w‖ ∧ ‖w‖ < r + δ n}).Nonempty := ⟨_, mem_image_of_mem g hw₁⟩
      exact hne.closure
    · exact ((gm5_annulus_conn hr.le (r + δ n)).image g (hg.1.continuousOn.mono (hsubA n))).closure
  have hFanti : Antitone F := fun m n hmn => by
    refine closure_mono (image_mono fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 ?_⟩)
    linarith [hδanti hmn]
  have hCeq : Cin = ⋂ n, F n := by
    ext p
    simp only [hCin, Set.mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      exact h (δ n) (hδpos n)
    · intro h ε hε
      have hex : ∃ n : ℕ, δ n < ε := by
        have : Tendsto δ atTop (𝓝 0) := tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact (this.eventually (gt_mem_nhds hε)).exists
      obtain ⟨n, hn⟩ := hex
      have hsub : {w : ℂ | r < ‖w‖ ∧ ‖w‖ < r + δ n} ⊆ {w : ℂ | r < ‖w‖ ∧ ‖w‖ < r + ε} :=
        fun w hw => ⟨hw.1, by linarith [hw.2]⟩
      exact closure_mono (image_mono hsub) (h n)
  refine ⟨?_, ?_, ?_⟩
  · rw [hCeq]
    exact (hFc 0).of_isClosed_subset (isClosed_iInter fun n => isClosed_closure) (iInter_subset _ 0)
  · rw [hCeq]
    exact gm5_nested_connected hFc hFconn hFanti
  · intro p hp hpU
    have hpg : p ∈ g '' annulus r R := hg.2.2 ▸ hpU
    obtain ⟨w₀, hw₀, rfl⟩ := hpg
    set ε : ℝ := (‖w₀‖ - r) / 2 with hε
    have hεpos : 0 < ε := by have := hw₀.1; rw [hε]; linarith
    set W : Set ℂ := {w | r + ε < ‖w‖ ∧ ‖w‖ < R} with hW
    have hWo : IsOpen W := isOpen_lt continuous_const continuous_norm |>.inter
      (isOpen_lt continuous_norm continuous_const)
    have hWA : W ⊆ annulus r R := fun w hw => ⟨by linarith [hw.1], hw.2⟩
    have hdisj : Disjoint (g '' W) (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε}) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hbA : b ∈ annulus r R := ⟨hb.1, by
        have := hw₀.2
        have : ‖w₀‖ ≤ R := this.le
        rw [hε] at hb
        linarith [hb.2]⟩
      have := hg.2.1 hbA (hWA ha) hab
      rw [this] at hb
      linarith [ha.1, hb.2]
    have hmem : g w₀ ∈ g '' W := ⟨w₀, ⟨by rw [hε]; linarith [hw₀.1], hw₀.2⟩, rfl⟩
    have hd2 := hdisj.closure_right (gm5_image_open hg hWo hWA)
    exact Set.disjoint_left.1 hd2 hmem (hp ε hεpos)

/-- Helper (Stage A): the outer cluster set is compact, connected and misses `U`. -/
theorem gm5_cout_props {U : Set ℂ} {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hbdd : Bornology.IsBounded U) :
    IsCompact {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})} ∧
      IsConnected {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})} ∧
      ∀ p ∈ {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})}, p ∉ U := by
  have hAo := gm5_isOpen_annulus r R
  set Cout : Set ℂ := {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})} with hCout
  have hcl : IsCompact (closure U) := hbdd.isCompact_closure
  set δ : ℕ → ℝ := fun n => (R - r) / ((n : ℝ) + 2) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos (by linarith) (by positivity)
  have hδR : ∀ n, δ n < R - r := fun n => by
    rw [hδ, div_lt_iff₀ (by positivity)]
    nlinarith [(by linarith : (0 : ℝ) < R - r), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδanti : Antitone δ := fun m n hmn => by
    simp only [hδ]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
  have hsubA : ∀ n, {w : ℂ | R - δ n < ‖w‖ ∧ ‖w‖ < R} ⊆ annulus r R := fun n w hw =>
    ⟨by linarith [hw.1, hδR n], hw.2⟩
  set F : ℕ → Set ℂ := fun n => closure (g '' {w | R - δ n < ‖w‖ ∧ ‖w‖ < R}) with hF
  have hFsubU : ∀ n, g '' {w | R - δ n < ‖w‖ ∧ ‖w‖ < R} ⊆ U := fun n =>
    hg.2.2 ▸ image_mono (hsubA n)
  have hFc : ∀ n, IsCompact (F n) := fun n =>
    hcl.of_isClosed_subset isClosed_closure (closure_mono (hFsubU n))
  have hFconn : ∀ n, IsConnected (F n) := fun n => by
    refine ⟨?_, ?_⟩
    · have hw₁ : (((R - δ n / 2 : ℝ)) : ℂ) ∈ {w : ℂ | R - δ n < ‖w‖ ∧ ‖w‖ < R} := by
        have h0 : (0 : ℝ) ≤ R - δ n / 2 := by linarith [hδpos n, hδR n]
        simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg h0]
        constructor <;> linarith [hδpos n]
      have hne : (g '' {w : ℂ | R - δ n < ‖w‖ ∧ ‖w‖ < R}).Nonempty := ⟨_, mem_image_of_mem g hw₁⟩
      exact hne.closure
    · have h0 : 0 ≤ R - δ n := by linarith [hδR n]
      exact ((gm5_annulus_conn h0 R).image g (hg.1.continuousOn.mono (hsubA n))).closure
  have hFanti : Antitone F := fun m n hmn => by
    refine closure_mono (image_mono fun w hw => ⟨lt_of_le_of_lt ?_ hw.1, hw.2⟩)
    linarith [hδanti hmn]
  have hCeq : Cout = ⋂ n, F n := by
    ext p
    simp only [hCout, Set.mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      exact h (δ n) (hδpos n)
    · intro h ε hε
      have hex : ∃ n : ℕ, δ n < ε := by
        have : Tendsto δ atTop (𝓝 0) := tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact (this.eventually (gt_mem_nhds hε)).exists
      obtain ⟨n, hn⟩ := hex
      have hsub : {w : ℂ | R - δ n < ‖w‖ ∧ ‖w‖ < R} ⊆ {w : ℂ | R - ε < ‖w‖ ∧ ‖w‖ < R} :=
        fun w hw => ⟨by linarith [hw.1], hw.2⟩
      exact closure_mono (image_mono hsub) (h n)
  refine ⟨?_, ?_, ?_⟩
  · rw [hCeq]
    exact (hFc 0).of_isClosed_subset (isClosed_iInter fun n => isClosed_closure) (iInter_subset _ 0)
  · rw [hCeq]
    exact gm5_nested_connected hFc hFconn hFanti
  · intro p hp hpU
    have hpg : p ∈ g '' annulus r R := hg.2.2 ▸ hpU
    obtain ⟨w₀, hw₀, rfl⟩ := hpg
    set ε : ℝ := (R - ‖w₀‖) / 2 with hε
    have hεpos : 0 < ε := by have := hw₀.2; rw [hε]; linarith
    set W : Set ℂ := {w | r < ‖w‖ ∧ ‖w‖ < R - ε} with hW
    have hWo : IsOpen W := isOpen_lt continuous_const continuous_norm |>.inter
      (isOpen_lt continuous_norm continuous_const)
    have hWA : W ⊆ annulus r R := fun w hw => ⟨hw.1, by linarith [hw.2]⟩
    have hdisj : Disjoint (g '' W) (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R}) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hbA : b ∈ annulus r R := ⟨by
        have := hw₀.1
        rw [hε] at hb
        linarith [hb.1], hb.2⟩
      have := hg.2.1 hbA (hWA ha) hab
      rw [this] at hb
      linarith [ha.2, hb.1]
    have hmem : g w₀ ∈ g '' W := ⟨w₀, ⟨hw₀.1, by rw [hε]; linarith [hw₀.2]⟩, rfl⟩
    have hd2 := hdisj.closure_right (gm5_image_open hg hWo hWA)
    exact Set.disjoint_left.1 hd2 hmem (hp ε hεpos)

/-- Helper (Stage A): the frontier of a bounded open set of `ℂ`, in `ℂ̄`. -/
theorem gm5_frontier_toExt {U : Set ℂ} (hUo : IsOpen U) (hbdd : Bornology.IsBounded U) :
    frontier (toExt U) = toExt (closure U \ U) := by
  have hopen : IsOpen (toExt U) := OnePoint.isOpenEmbedding_coe.isOpenMap _ hUo
  have hcpt : IsCompact (toExt (closure U)) := hbdd.isCompact_closure.image OnePoint.continuous_coe
  have hcl : closure (toExt U) = toExt (closure U) := by
    refine subset_antisymm (closure_minimal (image_mono subset_closure) hcpt.isClosed) ?_
    exact image_closure_subset_closure_image OnePoint.continuous_coe
  rw [frontier, hcl, hopen.interior_eq]
  exact (Set.image_sdiff OnePoint.coe_injective _ _).symm

/-- Helper (Stage A, T1; the two ends of a bounded ring domain). Let `g : {r < |w| < R} → U` be conformal onto a bounded
ring domain `U`. The cluster sets `Cin` (as `|w| → r`) and `Cout` (as `|w| → R`) of `g` are non-empty, compact,
connected and disjoint, and the frontier of `U` is `Cin ∪ Cout`; hence `Cin` and `Cout` are the two
components of the frontier. -/
theorem gm5_ends {U : Set ℂ} {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hbdd : Bornology.IsBounded U) (hU : IsRingDomain (toExt U)) :
    ∃ Cin Cout : Set ℂ,
      (∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})) ∧
      (∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})) ∧
      IsCompact Cin ∧ IsCompact Cout ∧ IsConnected Cin ∧ IsConnected Cout ∧ Disjoint Cin Cout ∧
      frontier (toExt U) = toExt Cin ∪ toExt Cout := by
  have hAo := gm5_isOpen_annulus r R
  have hUo : IsOpen U := by
    have := gm5_image_open hg hAo subset_rfl
    rwa [hg.2.2] at this
  obtain ⟨hk1, hc1, hU1⟩ := gm5_cin_props hr hrR hg hbdd
  obtain ⟨hk2, hc2, hU2⟩ := gm5_cout_props hr hrR hg hbdd
  set Cin : Set ℂ := {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})} with hCin
  set Cout : Set ℂ := {p : ℂ | ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})} with hCout
  -- the frontier is `Cin ∪ Cout`
  have hfr : closure U \ U = Cin ∪ Cout := by
    ext p
    constructor
    · rintro ⟨hpcl, hpU⟩
      set m : ℝ := (r + R) / 2 with hm
      have hm1 : r < m := by rw [hm]; linarith
      have hm2 : m < R := by rw [hm]; linarith
      have hdecomp : U = g '' {w | r < ‖w‖ ∧ ‖w‖ < m} ∪ g '' sphere 0 m ∪ g '' {w | m < ‖w‖ ∧ ‖w‖ < R} := by
        rw [← hg.2.2, ← image_union, ← image_union]
        congr 1
        ext w
        simp only [annulus, Set.mem_ofPred_eq, mem_union, mem_sphere_zero_iff_norm]
        constructor
        · rintro ⟨h1, h2⟩
          rcases lt_trichotomy ‖w‖ m with h | h | h
          · exact Or.inl (Or.inl ⟨h1, h⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨h, h2⟩
        · rintro ((h | h) | h)
          · exact ⟨h.1, h.2.trans hm2⟩
          · exact ⟨h ▸ hm1, h ▸ hm2⟩
          · exact ⟨hm1.trans h.1, h.2⟩
      have hsphcl : IsClosed (g '' sphere 0 m) := by
        refine (isCompact_sphere (0 : ℂ) m |>.image_of_continuousOn (hg.1.continuousOn.mono ?_)).isClosed
        intro z hz
        rw [mem_sphere_zero_iff_norm] at hz
        exact ⟨hz ▸ hm1, hz ▸ hm2⟩
      rw [hdecomp, closure_union, closure_union, hsphcl.closure_eq] at hpcl
      rcases hpcl with (h | h) | h
      · rcases gm5_closure_in (Cin := Cin) hg (fun q => Iff.rfl) hm2 h with h' | h'
        · exact absurd h' hpU
        · exact Or.inl h'
      · exact absurd (hdecomp ▸ (Or.inl (Or.inr h) : p ∈ _ ∪ _ ∪ _)) hpU
      · rcases gm5_closure_out (Cout := Cout) hg (fun q => Iff.rfl) hm1 h with h' | h'
        · exact absurd h' hpU
        · exact Or.inr h'
    · intro hp
      set ε : ℝ := (R - r) / 2 with hε
      have hεpos : 0 < ε := by rw [hε]; linarith
      rcases hp with hp | hp
      · refine ⟨?_, hU1 p hp⟩
        have := hp ε hεpos
        refine closure_mono ?_ this
        exact hg.2.2 ▸ image_mono fun w hw => ⟨hw.1, by linarith [hw.2]⟩
      · refine ⟨?_, hU2 p hp⟩
        have := hp ε hεpos
        refine closure_mono ?_ this
        exact hg.2.2 ▸ image_mono fun w hw => ⟨by linarith [hw.1], hw.2⟩
  have hfrU : frontier (toExt U) = toExt Cin ∪ toExt Cout := by
    rw [gm5_frontier_toExt hUo hbdd, hfr, LiZhongQC.toExt, image_union]
    rfl
  refine ⟨Cin, Cout, fun q => Iff.rfl, fun q => Iff.rfl, hk1, hk2, hc1, hc2, ?_, hfrU⟩
  rw [Set.disjoint_left]
  intro p hp1 hp2
  apply gm5_frontier_not_conn hU
  rw [hfrU]
  exact IsPreconnected.union (p : ExtPlane) ⟨p, hp1, rfl⟩ ⟨p, hp2, rfl⟩
    (hc1.isPreconnected.image _ OnePoint.continuous_coe.continuousOn)
    (hc2.isPreconnected.image _ OnePoint.continuous_coe.continuousOn)

/-- Helper (Stage A, T4; separating curves meet every ray). Let `ψ : U → {r < |w| < R}` be conformal with inverse `g`.
Every curve `γ` of the family separating `Cin` from `Cout` has an image `ψ(γ)` meeting every ray from `0`. -/
theorem gm5_sep_rays {U : Set ℂ} {g ψ : ℂ → ℂ} {r R : ℝ} {Cin Cout : Set ℂ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hψ : IsConformalOnto ψ U (annulus r R))
    (hgψ : ∀ z ∈ U, g (ψ z) = z) (hψg : ∀ w ∈ annulus r R, ψ (g w) = w) (hbdd : Bornology.IsBounded U)
    (hCin : ∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε}))
    (hCout : ∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R}))
    {γ : Set ℂ} (hγ : γ ∈ separatingFamily U Cin Cout) (θ : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ((t : ℂ) * exp (θ * I)) ∈ ψ '' γ := by
  by_contra hno
  push Not at hno
  set u : ℂ := exp (θ * I) with hu
  have hun : ‖u‖ = 1 := norm_exp_ofReal_mul_I θ
  have hgn : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ) * u‖ = t := fun t ht => by
    rw [norm_mul, hun, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]
  have hmem : ∀ t ∈ Ioo r R, (t : ℂ) * u ∈ annulus r R := fun t ht =>
    ⟨by rw [hgn t (hr.trans ht.1).le]; exact ht.1, by rw [hgn t (hr.trans ht.1).le]; exact ht.2⟩
  set arc : Set ℂ := (fun t : ℝ => g ((t : ℂ) * u)) '' Ioo r R with harc
  have harcU : arc ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hg.2.2 ▸ mem_image_of_mem g (hmem t ht)
  have harcγ : arc ⊆ U \ γ := by
    refine fun z hz => ⟨harcU hz, ?_⟩
    obtain ⟨t, ht, rfl⟩ := hz
    intro hzγ
    exact hno t (hr.trans ht.1) ⟨_, hzγ, hψg _ (hmem t ht)⟩
  have hgcont : ContinuousOn (fun t : ℝ => g ((t : ℂ) * u)) (Ioo r R) :=
    hg.1.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * u).continuousOn (fun t ht => hmem t ht)
  have hconn : IsPreconnected arc := isPreconnected_Ioo.image _ hgcont
  set m : ℂ := g ((((r + R) / 2 : ℝ) : ℂ) * u) with hm
  have hmarc : m ∈ arc := ⟨(r + R) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hK : arc ⊆ connectedComponentIn (U \ γ) m := hconn.subset_connectedComponentIn hmarc harcγ
  have hcpt : IsCompact (closure U) := hbdd.isCompact_closure
  -- cluster points of the arc at the two ends
  have key : ∀ c : ℕ → ℝ, (∀ n, c n ∈ Ioo r R) → ∃ p ∈ closure arc, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => g (((c (φ n) : ℝ) : ℂ) * u)) atTop (𝓝 p) := by
    intro c hc
    have hxU : ∀ n, g (((c n : ℝ) : ℂ) * u) ∈ closure U := fun n =>
      subset_closure (hg.2.2 ▸ mem_image_of_mem g (hmem _ (hc n)))
    obtain ⟨p, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hxU
    refine ⟨p, mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n => ⟨c (φ n), hc _, rfl⟩), φ, hφ, hlim⟩
  have hpin : ∃ p ∈ closure arc, p ∈ Cin := by
    set c : ℕ → ℝ := fun n => r + (R - r) / (n + 2) with hc
    have hcI : ∀ n, c n ∈ Ioo r R := fun n => by
      have hn : (0 : ℝ) < n + 2 := by positivity
      refine ⟨by simp only [hc]; have : 0 < (R - r) / (n + 2) := div_pos (by linarith) hn; linarith, ?_⟩
      simp only [hc]
      have : (R - r) / (n + 2) < R - r := by
        rw [div_lt_iff₀ hn]; nlinarith [(by linarith : (0 : ℝ) < R - r), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hct : Tendsto c atTop (𝓝 r) := by
      have : Tendsto (fun n : ℕ => (R - r) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa [hc] using this.const_add r
    obtain ⟨p, hp, φ, hφ, hlim⟩ := key c hcI
    refine ⟨p, hp, (hCin p).2 fun ε hε => ?_⟩
    refine mem_closure_of_tendsto hlim ?_
    have hev : ∀ᶠ n in atTop, c (φ n) < r + ε :=
      (hct.comp hφ.tendsto_atTop).eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    refine ⟨((c (φ n) : ℝ) : ℂ) * u, ⟨?_, ?_⟩, rfl⟩
    · rw [hgn _ (hr.trans (hcI _).1).le]; exact (hcI _).1
    · rw [hgn _ (hr.trans (hcI _).1).le]; exact hn
  have hpout : ∃ p ∈ closure arc, p ∈ Cout := by
    set c : ℕ → ℝ := fun n => R - (R - r) / (n + 2) with hc
    have hcI : ∀ n, c n ∈ Ioo r R := fun n => by
      have hn : (0 : ℝ) < n + 2 := by positivity
      have h1 : 0 < (R - r) / (n + 2) := div_pos (by linarith) hn
      have h2 : (R - r) / (n + 2) < R - r := by
        rw [div_lt_iff₀ hn]; nlinarith [(by linarith : (0 : ℝ) < R - r), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact ⟨by simp only [hc]; linarith, by simp only [hc]; linarith⟩
    have hct : Tendsto c atTop (𝓝 R) := by
      have : Tendsto (fun n : ℕ => (R - r) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa [hc] using (this.const_sub R)
    obtain ⟨p, hp, φ, hφ, hlim⟩ := key c hcI
    refine ⟨p, hp, (hCout p).2 fun ε hε => ?_⟩
    refine mem_closure_of_tendsto hlim ?_
    have hev : ∀ᶠ n in atTop, R - ε < c (φ n) :=
      (hct.comp hφ.tendsto_atTop).eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    refine ⟨((c (φ n) : ℝ) : ℂ) * u, ⟨?_, ?_⟩, rfl⟩
    · rw [hgn _ (hr.trans (hcI _).1).le]; exact hn
    · rw [hgn _ (hr.trans (hcI _).1).le]; exact (hcI _).2
  obtain ⟨pi, hpi, hpiC⟩ := hpin
  obtain ⟨po, hpo, hpoC⟩ := hpout
  exact hγ.2.2 m (harcγ hmarc) ⟨⟨pi, closure_mono hK hpi, hpiC⟩, ⟨po, closure_mono hK hpo, hpoC⟩⟩

/-- Helper (Stage A): the lower bound `λ_U(Γ) ≥ 2π/log(R/r)` for the family separating the two ends. -/
theorem gm5_extLen_ge {U : Set ℂ} {g ψ : ℂ → ℂ} {r R : ℝ} {Cin Cout : Set ℂ} (hr : 0 < r) (hrR : r < R)
    (hg : IsConformalOnto g (annulus r R) U) (hψ : IsConformalOnto ψ U (annulus r R))
    (hgψ : ∀ z ∈ U, g (ψ z) = z) (hψg : ∀ w ∈ annulus r R, ψ (g w) = w) (hbdd : Bornology.IsBounded U)
    (hCin : ∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε}))
    (hCout : ∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})) :
    ENNReal.ofReal (2 * π / Real.log (R / r)) ≤ extremalLengthGM U (separatingFamily U Cin Cout) := by
  have hAo := gm5_isOpen_annulus r R
  have hUo : IsOpen U := by
    have := (RMT.differentiableOn_invFunOn_of_injOn hAo hg.1 hg.2.1).1
    rwa [hg.2.2] at this
  obtain ⟨hmem, hA, -⟩ := gm4b_annulus_metric hr hrR (c := 1) one_pos
  set ρ₁ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / ‖z‖) with hρ₁
  have hρ₁m : Measurable ρ₁ := hmem.1
  set ρ₀ : ℂ → ℝ≥0∞ := U.indicator fun z => ρ₁ (ψ z) * ‖deriv ψ z‖ₑ with hρ₀
  have harea : LiZhongQC.rhoArea ρ₀ U = ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
    rw [hρ₀, LiZhongQC.rhoArea_pullback hUo hψ ρ₁]
    exact hA
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have hρ₀P : ρ₀ ∈ LiZhongQC.densitiesP0 U := by
    refine ⟨LiZhongQC.measurable_pullback_density hUo hψ.1.continuousOn hρ₁m, ?_, ?_⟩
    · rw [harea]; exact ENNReal.ofReal_pos.2 (by positivity)
    · rw [harea]; exact ENNReal.ofReal_lt_top
  have hL : ENNReal.ofReal (2 * π) ≤ pathRhoLength (separatingFamily U Cin Cout) ρ₀ := by
    rw [gm4a_pathRhoLength_eq]
    refine le_iInf₂ fun γ hγ => ?_
    have hpc := hγ.1
    have hγU : γ ⊆ U := gm4a_isPathCurve_subset hpc
    have hγm : MeasurableSet γ := gm4b_isPathCurve_measurableSet hpc
    have hSm : MeasurableSet (ψ '' γ) :=
      hγm.image_of_continuousOn_injOn (hψ.1.continuousOn.mono hγU) (hψ.2.1.mono hγU)
    have hSA : ψ '' γ ⊆ annulus r R := by
      rintro _ ⟨z, hz, rfl⟩
      exact hψ.2.2 ▸ mem_image_of_mem ψ (hγU hz)
    have h0 : (0 : ℂ) ∉ ψ '' γ := fun h => by
      have h1 : r < ‖(0 : ℂ)‖ := (hSA h).1
      rw [norm_zero] at h1
      linarith
    have hang := gm5_angle hSm h0 (gm5_sep_rays hr hrR hg hψ hgψ hψg hbdd hCin hCout hγ)
    have heq := gm4b_lintegral_image_conformal hUo hψ hγm hγU hρ₁m
    calc ENNReal.ofReal (2 * π) ≤ ∫⁻ w in ψ '' γ, ENNReal.ofReal (1 / ‖w‖) ∂μH[1] := hang
      _ = ∫⁻ z in γ, ρ₀ z ∂μH[1] := by
        rw [heq]
        refine setLIntegral_congr_fun hγm fun z hz => ?_
        simp only [hρ₀, indicator_of_mem (hγU hz)]
  have harith : ENNReal.ofReal (2 * π / Real.log (R / r)) =
      ENNReal.ofReal (2 * π) ^ 2 / ENNReal.ofReal (2 * π * 1 ^ 2 * Real.log (R / r)) := by
    rw [← ENNReal.ofReal_pow (by positivity), one_pow, mul_one,
      ← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * π * Real.log (R / r))]
    congr 1
    field_simp
  rw [harith]
  refine le_trans ?_ (le_iSup₂ (f := fun ρ (_ : ρ ∈ LiZhongQC.densitiesP0 U) =>
    pathRhoLength (separatingFamily U Cin Cout) ρ ^ 2 / LiZhongQC.rhoArea ρ U) ρ₀ hρ₀P)
  rw [harea]
  gcongr

/-- Helper (Stage A): the family of separating curves is symmetric in the two sets. -/
theorem gm5_sepFamily_symm (U A B : Set ℂ) : separatingFamily U B A = separatingFamily U A B := by
  ext γ
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx hh => h3 x hx ⟨hh.2, hh.1⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx hh => h3 x hx ⟨hh.2, hh.1⟩⟩

/-- Helper (Stage A): the finite part of `toExt C` is `C`. -/
theorem gm5_finitePart_toExt (C : Set ℂ) : finitePart (toExt C) = C := by
  ext z
  constructor
  · rintro ⟨w, hw, h⟩
    exact OnePoint.coe_injective h ▸ hw
  · intro h
    exact ⟨z, h, rfl⟩

/-- **Helper (Stage A): the module of a bounded ring domain** (the bounded case of `ringModGM_annulus`, without the
extremal-metric clause): if `ψ` maps the ring domain `B` conformally onto `{r < |w| < R}` and `∞ ∉ closure B`, then
`mod(B) = (1/2π) log(R/r)`, and every pair of points of different components of `∂B` gives it. -/
theorem gm5_ringMod_bounded {B : Set ExtPlane} (hB : IsRingDomain B) {ψ : ExtPlane → ExtPlane} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hψ : LehtoVirtanen1973.IsConformalMap ψ B) (hψB : ψ '' B = toExt (annulus r R))
    (hbdd : extInf ∉ closure B) :
    ringModGM B = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) ∧
      ∀ x ∈ frontier B, ∀ y ∈ frontier B,
        connectedComponentIn (frontier B) x ≠ connectedComponentIn (frontier B) y →
          (extremalLengthGM (finitePart B) (ringSepFamily B x y))⁻¹ = ringModGM B := by
  obtain ⟨g, hBU, hUb, hUo, hψc, hgc, hgψ, hψg⟩ := gm5_ring_plane hB hr hrR hψ hψB hbdd
  set U := finitePart B with hU
  have hring : IsRingDomain (toExt U) := hBU ▸ hB
  obtain ⟨Cin, Cout, hCin, hCout, hk1, hk2, hc1, hc2, hdisj, hfr⟩ := gm5_ends hr hrR hgc hUb hring
  have hfrB : frontier B = toExt Cin ∪ toExt Cout := by
    have := hfr
    rwa [← hBU] at this
  obtain ⟨hcomp1, hcomp2⟩ := gm5_frontier_comps hc1 hc2 hk1 hk2 hdisj
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have hval : extremalLengthGM U (separatingFamily U Cin Cout) = ENNReal.ofReal (2 * π / Real.log (R / r)) :=
    le_antisymm (gm5_extLen_le hr hrR hgc fun s hs => gm5_circle_sep hr hrR hgc hUb hCin hCout hdisj hfr hs)
      (gm5_extLen_ge hr hrR hgc hψc hgψ hψg hUb hCin hCout)
  have hinv : (extremalLengthGM U (separatingFamily U Cin Cout))⁻¹ =
      ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
    rw [hval, ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    field_simp
  have hpair : ∀ x ∈ frontier B, ∀ y ∈ frontier B,
      connectedComponentIn (frontier B) x ≠ connectedComponentIn (frontier B) y →
        (extremalLengthGM U (ringSepFamily B x y))⁻¹ = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
    intro x hx y hy hne
    rw [hfrB] at hx hy hne
    rcases hx with hxi | hxo <;> rcases hy with hyi | hyo
    · exact absurd ((hcomp1 x hxi).trans (hcomp1 y hyi).symm) hne
    · rw [ringSepFamily, hfrB, hcomp1 x hxi, hcomp2 y hyo, gm5_finitePart_toExt, gm5_finitePart_toExt]
      exact hinv
    · rw [ringSepFamily, hfrB, hcomp2 x hxo, hcomp1 y hyi, gm5_finitePart_toExt, gm5_finitePart_toExt,
        gm5_sepFamily_symm]
      exact hinv
    · exact absurd ((hcomp2 x hxo).trans (hcomp2 y hyo).symm) hne
  have hne12 : toExt Cin ≠ toExt Cout := fun h => by
    obtain ⟨p, hp⟩ := hc1.nonempty
    have : (p : ExtPlane) ∈ toExt Cout := h ▸ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := this
    exact Set.disjoint_left.1 hdisj hp (OnePoint.coe_injective hqp ▸ hq)
  have hmod : ringModGM B = ENNReal.ofReal (1 / (2 * π) * Real.log (R / r)) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => iSup_le fun hne => ?_
      exact (hpair x hx y hy hne).le
    · obtain ⟨p, hp⟩ := hc1.nonempty
      obtain ⟨q, hq⟩ := hc2.nonempty
      have hxp : (p : ExtPlane) ∈ frontier B := hfrB ▸ Or.inl ⟨p, hp, rfl⟩
      have hyq : (q : ExtPlane) ∈ frontier B := hfrB ▸ Or.inr ⟨q, hq, rfl⟩
      have hne : connectedComponentIn (frontier B) (p : ExtPlane) ≠
          connectedComponentIn (frontier B) (q : ExtPlane) := by
        rw [hfrB, hcomp1 _ ⟨p, hp, rfl⟩, hcomp2 _ ⟨q, hq, rfl⟩]
        exact hne12
      refine le_iSup_of_le (p : ExtPlane) (le_iSup_of_le hxp (le_iSup_of_le (q : ExtPlane)
        (le_iSup_of_le hyq (le_iSup_of_le hne ?_))))
      exact (hpair _ hxp _ hyq hne).ge
  exact ⟨hmod, fun x hx y hy hne => (hpair x hx y hy hne).trans hmod.symm⟩

/-- The configuration of Teichmüller's Modulsatz (helper, Ch. V §4, P1:7171): `0 < R₁ < R₂`, `J` is a continuum
(compact and connected) in the annulus `Ω = {R₁ < |z| < R₂}`, and `Ω₁`, `Ω₂` are disjoint components of `Ω \ J`
which are ring domains of `ℂ*`, with `{|z| = R₁} ⊆ ∂Ω₁` and `{|z| = R₂} ⊆ ∂Ω₂` (so `J` separates the two boundary
circles of `Ω`). -/
def IsModulsatzConfig (R₁ R₂ : ℝ) (J Ω₁ Ω₂ : Set ℂ) : Prop :=
  0 < R₁ ∧ R₁ < R₂ ∧ IsCompact J ∧ IsConnected J ∧ J ⊆ annulus R₁ R₂ ∧
    (∃ z ∈ annulus R₁ R₂ \ J, connectedComponentIn (annulus R₁ R₂ \ J) z = Ω₁) ∧
    (∃ z ∈ annulus R₁ R₂ \ J, connectedComponentIn (annulus R₁ R₂ \ J) z = Ω₂) ∧ Disjoint Ω₁ Ω₂ ∧
    IsRingDomain (toExt Ω₁) ∧ IsRingDomain (toExt Ω₂) ∧ sphere (0 : ℂ) R₁ ⊆ frontier Ω₁ ∧
    sphere (0 : ℂ) R₂ ⊆ frontier Ω₂

/-- Helper (Stage B1): a round annulus is open and connected. -/
theorem gm5_annulus_oc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : IsOpen (annulus a b) ∧ IsConnected (annulus a b) :=
  ⟨gm5_isOpen_annulus a b, ⟨(((a + b) / 2 : ℝ) : ℂ), by
    have : ‖(((a + b) / 2 : ℝ) : ℂ)‖ = (a + b) / 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    show a < ‖(((a + b) / 2 : ℝ) : ℂ)‖ ∧ ‖(((a + b) / 2 : ℝ) : ℂ)‖ < b
    rw [this]
    constructor <;> linarith⟩, gm5_annulus_conn ha b⟩

/-- Helper (Stage B1): in the configuration, `Ω₁` and `Ω₂` are domains inside the annulus. -/
theorem gm5_conf_comp {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) : IsOpen Ω ∧ IsConnected Ω ∧ Ω ⊆ annulus R₁ R₂ := by
  obtain ⟨-, -, hJk, -, hJA, ⟨z₁, hz₁, hΩ₁⟩, ⟨z₂, hz₂, hΩ₂⟩, -⟩ := hconf
  have hJcl : IsClosed J := hJk.isClosed
  have hAJ : IsOpen (annulus R₁ R₂ \ J) := (gm5_isOpen_annulus R₁ R₂).sdiff hJcl
  rcases hΩ with rfl | rfl
  · rw [← hΩ₁]
    exact ⟨hAJ.connectedComponentIn, isConnected_connectedComponentIn_iff.2 hz₁,
      (connectedComponentIn_subset _ _).trans sdiff_subset⟩
  · rw [← hΩ₂]
    exact ⟨hAJ.connectedComponentIn, isConnected_connectedComponentIn_iff.2 hz₂,
      (connectedComponentIn_subset _ _).trans sdiff_subset⟩

/-- Helper (Stage B1): the shells next to the boundary circles belong to `Ω₁` and `Ω₂`, and `J` lies between them. -/
theorem gm5_shells {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    ∃ a b : ℝ, R₁ < a ∧ a < b ∧ b < R₂ ∧ annulus R₁ a ⊆ Ω₁ ∧ annulus b R₂ ⊆ Ω₂ ∧ J ⊆ annulus a b := by
  obtain ⟨hR1, hR12, hJk, hJconn, hJA, ⟨z₁, hz₁, hΩ₁⟩, ⟨z₂, hz₂, hΩ₂⟩, hdisj, -, -, hs1, hs2⟩ := hconf
  have hJne := hJconn.nonempty
  obtain ⟨zm, hzm, hmin⟩ := hJk.exists_isMinOn hJne continuous_norm.continuousOn
  obtain ⟨zM, hzM, hmax⟩ := hJk.exists_isMaxOn hJne continuous_norm.continuousOn
  have hmin' : ∀ z ∈ J, ‖zm‖ ≤ ‖z‖ := fun z hz => isMinOn_iff.1 hmin z hz
  have hmax' : ∀ z ∈ J, ‖z‖ ≤ ‖zM‖ := fun z hz => isMaxOn_iff.1 hmax z hz
  have hm1 : R₁ < ‖zm‖ := (hJA hzm).1
  have hM2 : ‖zM‖ < R₂ := (hJA hzM).2
  have hmM : ‖zm‖ ≤ ‖zM‖ := hmin' zM hzM
  set a : ℝ := (R₁ + ‖zm‖) / 2 with ha
  set b : ℝ := (‖zM‖ + R₂) / 2 with hb
  have haR : R₁ < a := by rw [ha]; linarith
  have ham : a < ‖zm‖ := by rw [ha]; linarith
  have hbM : ‖zM‖ < b := by rw [hb]; linarith
  have hbR : b < R₂ := by rw [hb]; linarith
  have hR1' : 0 ≤ R₁ := hR1.le
  have hΩ₁sub : Ω₁ ⊆ annulus R₁ R₂ \ J := hΩ₁ ▸ connectedComponentIn_subset _ _
  have hΩ₂sub : Ω₂ ⊆ annulus R₁ R₂ \ J := hΩ₂ ▸ connectedComponentIn_subset _ _
  refine ⟨a, b, haR, ham.trans (hmM.trans_lt hbM), hbR, ?_, ?_,
    fun z hz => ⟨ham.trans_le (hmin' z hz), (hmax' z hz).trans_lt hbM⟩⟩
  · -- the inner shell
    have hsub : annulus R₁ a ⊆ annulus R₁ R₂ \ J := fun z hz =>
      ⟨⟨hz.1, hz.2.trans (ham.trans (hmM.trans_lt hM2))⟩, fun hzJ => absurd (hz.2.trans ham) (not_lt.2 (hmin' z hzJ))⟩
    have hq : ((R₁ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₁ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR1']
    have hcl : ((R₁ : ℝ) : ℂ) ∈ closure Ω₁ := (hs1 hq).1
    obtain ⟨w, hwΩ, hw⟩ := Metric.mem_closure_iff.1 hcl (a - R₁) (by linarith)
    have hwA : w ∈ annulus R₁ R₂ := (hΩ₁sub hwΩ).1
    have hwsh : w ∈ annulus R₁ a := by
      refine ⟨hwA.1, ?_⟩
      have h1 : ‖w‖ ≤ ‖((R₁ : ℝ) : ℂ)‖ + dist w ((R₁ : ℝ) : ℂ) := by
        calc ‖w‖ = ‖((R₁ : ℝ) : ℂ) + (w - ((R₁ : ℝ) : ℂ))‖ := by ring_nf
          _ ≤ _ := (norm_add_le _ _).trans (by rw [dist_eq_norm])
      rw [Complex.norm_real, Real.norm_of_nonneg hR1', dist_comm] at h1
      linarith
    have hpre : IsPreconnected (annulus R₁ a) := gm5_annulus_conn hR1' a
    have hwc : w ∈ connectedComponentIn (annulus R₁ R₂ \ J) z₁ := hΩ₁ ▸ hwΩ
    rw [← hΩ₁, connectedComponentIn_eq hwc]
    exact hpre.subset_connectedComponentIn hwsh hsub
  · -- the outer shell
    have hR2' : 0 ≤ R₂ := (hR1.trans hR12).le
    have hsub : annulus b R₂ ⊆ annulus R₁ R₂ \ J := fun z hz =>
      ⟨⟨(hm1.trans_le hmM).trans hbM |>.trans hz.1, hz.2⟩,
        fun hzJ => absurd ((hmax' z hzJ).trans_lt hbM) (not_lt.2 hz.1.le)⟩
    have hq : ((R₂ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₂ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR2']
    have hcl : ((R₂ : ℝ) : ℂ) ∈ closure Ω₂ := (hs2 hq).1
    obtain ⟨w, hwΩ, hw⟩ := Metric.mem_closure_iff.1 hcl (R₂ - b) (by linarith)
    have hwA : w ∈ annulus R₁ R₂ := (hΩ₂sub hwΩ).1
    have hwsh : w ∈ annulus b R₂ := by
      refine ⟨?_, hwA.2⟩
      have h1 : ‖((R₂ : ℝ) : ℂ)‖ ≤ ‖w‖ + dist w ((R₂ : ℝ) : ℂ) := by
        calc ‖((R₂ : ℝ) : ℂ)‖ = ‖w + (((R₂ : ℝ) : ℂ) - w)‖ := by ring_nf
          _ ≤ ‖w‖ + ‖((R₂ : ℝ) : ℂ) - w‖ := norm_add_le _ _
          _ = ‖w‖ + dist w ((R₂ : ℝ) : ℂ) := by rw [dist_comm, dist_eq_norm]
      rw [Complex.norm_real, Real.norm_of_nonneg hR2'] at h1
      have hd : dist w ((R₂ : ℝ) : ℂ) < R₂ - b := by rw [dist_comm]; exact hw
      linarith
    have hpre : IsPreconnected (annulus b R₂) := gm5_annulus_conn (hR1.le.trans (hm1.le.trans (hmM.trans hbM.le))) R₂
    have hwc : w ∈ connectedComponentIn (annulus R₁ R₂ \ J) z₂ := hΩ₂ ▸ hwΩ
    rw [← hΩ₂, connectedComponentIn_eq hwc]
    exact hpre.subset_connectedComponentIn hwsh hsub

/-- Helper (Stage B1): a set which is the disjoint union of two closed, non-empty, preconnected sets has exactly
two connected components. -/
theorem gm5_two_components {X : Type*} [TopologicalSpace X] {S₁ S₂ F : Set X} (h₁ : IsClosed S₁)
    (h₂ : IsClosed S₂) (hd : Disjoint S₁ S₂) (hp₁ : IsPreconnected S₁) (hp₂ : IsPreconnected S₂)
    (hn₁ : S₁.Nonempty) (hn₂ : S₂.Nonempty) (hF : F = S₁ ∪ S₂) :
    Nat.card (ConnectedComponents ↥F) = 2 := by
  subst hF
  classical
  obtain ⟨p₁, hp₁m⟩ := hn₁
  obtain ⟨p₂, hp₂m⟩ := hn₂
  set P₁ : ↥(S₁ ∪ S₂) := ⟨p₁, Or.inl hp₁m⟩ with hP₁
  set P₂ : ↥(S₁ ∪ S₂) := ⟨p₂, Or.inr hp₂m⟩ with hP₂
  set T₁ : Set ↥(S₁ ∪ S₂) := {x | x.1 ∈ S₁} with hT₁def
  set T₂ : Set ↥(S₁ ∪ S₂) := {x | x.1 ∈ S₂} with hT₂def
  have hT₁c : IsClosed T₁ := h₁.preimage continuous_subtype_val
  have hT₂c : IsClosed T₂ := h₂.preimage continuous_subtype_val
  have hT₂eq : T₂ = T₁ᶜ := by
    ext x
    simp only [hT₁def, hT₂def, Set.mem_ofPred_eq, mem_compl_iff]
    rcases x.2 with h | h
    · exact ⟨fun hn => absurd h (Set.disjoint_left.1 hd.symm hn), fun hn => absurd h hn⟩
    · exact ⟨fun _ hn => Set.disjoint_left.1 hd hn h, fun _ => h⟩
  have hT₁o : IsOpen T₁ := by
    have : T₁ = T₂ᶜ := by rw [hT₂eq, compl_compl]
    rw [this]; exact hT₂c.isOpen_compl
  have hT₂o : IsOpen T₂ := hT₂eq ▸ hT₁c.isOpen_compl
  have hpT₁ : IsPreconnected T₁ := by
    have : Subtype.val '' T₁ = S₁ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, Or.inl hz⟩, hz, rfl⟩
    exact (Topology.IsInducing.subtypeVal.isPreconnected_image).1 (by rw [this]; exact hp₁)
  have hpT₂ : IsPreconnected T₂ := by
    have : Subtype.val '' T₂ = S₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, Or.inr hz⟩, hz, rfl⟩
    exact (Topology.IsInducing.subtypeVal.isPreconnected_image).1 (by rw [this]; exact hp₂)
  rw [Nat.card_eq_two_iff]
  refine ⟨(P₁ : ConnectedComponents _), (P₂ : ConnectedComponents _), ?_, ?_⟩
  · intro h
    rw [ConnectedComponents.coe_eq_coe] at h
    have hmem : P₂ ∈ connectedComponent P₁ := h ▸ mem_connectedComponent
    have hP₁T : P₁ ∈ T₁ := hp₁m
    have := (show IsClopen T₁ from ⟨hT₁c, hT₁o⟩).connectedComponent_subset hP₁T hmem
    exact Set.disjoint_left.1 hd this hp₂m
  · ext q
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases x.2 with hx | hx
    · left
      rw [ConnectedComponents.coe_eq_coe]
      have : x ∈ T₁ := hx
      exact connectedComponent_eq (hpT₁.subset_connectedComponent this (show P₁ ∈ T₁ from hp₁m))
    · right
      rw [ConnectedComponents.coe_eq_coe]
      have : x ∈ T₂ := hx
      exact connectedComponent_eq (hpT₂.subset_connectedComponent this (show P₂ ∈ T₂ from hp₂m))

/-- Helper (Stage B1): the exterior `{b ≤ |z|}` together with `∞` is preconnected in `ℂ̄`. -/
theorem gm5_outer_conn {b : ℝ} (hb : 0 < b) : IsPreconnected (toExt {z : ℂ | b ≤ ‖z‖} ∪ {extInf}) := by
  set T : Set ℂ := {z | b ≤ ‖z‖} with hT
  have hTc : IsPreconnected T := by
    have hc : IsPreconnected (Ici b ×ˢ (univ : Set ℝ)) := isPreconnected_Ici.prod isPreconnected_univ
    have himg := hc.image (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (by
      have : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
        simp only [LiZhongQC.kn_circleMap_eq]
        fun_prop
      exact this.continuousOn)
    convert himg using 1
    ext z
    simp only [hT, Set.mem_ofPred_eq, mem_image, mem_prod, mem_Ici, mem_univ, and_true, Prod.exists]
    constructor
    · intro hz
      refine ⟨‖z‖, Complex.arg z, hz, ?_⟩
      rw [circleMap_zero, ← Complex.norm_mul_exp_arg_mul_I z]
      simp [Complex.norm_mul_exp_arg_mul_I]
    · rintro ⟨r, θ, hr, rfl⟩
      rw [norm_circleMap_zero, abs_of_nonneg (hb.le.trans hr)]
      exact hr
  have hpT : IsPreconnected (toExt T) := hTc.image _ OnePoint.continuous_coe.continuousOn
  have hinf : extInf ∈ closure (toExt T) := by
    have ht : Tendsto (fun t : ℝ => ((t : ℂ) : ExtPlane)) atTop (𝓝 extInf) := by
      refine OnePoint.tendsto_coe_infty.comp ?_
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      refine Tendsto.congr' ?_ tendsto_id
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp [abs_of_nonneg ht]
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop b] with t ht
    refine ⟨(t : ℂ), ?_, rfl⟩
    simp only [hT, Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg (hb.le.trans ht)]
    exact ht
  exact hpT.subset_closure subset_union_left
    (union_subset subset_closure (singleton_subset_iff.2 hinf))

/-- Helper (Stage B1): the identity is a conformal map of the round annulus (in the sense of Lehto–Virtanen). -/
theorem gm5_id_conformal {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    LehtoVirtanen1973.IsConformalMap id (toExt (annulus a b)) := by
  obtain ⟨hAo, hAc⟩ := gm5_annulus_oc ha hab
  refine ⟨⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ hAo,
    ⟨hAc.nonempty.image _, hAc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn⟩⟩,
    continuousOn_id, Function.injective_id.injOn, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have : LehtoVirtanen1973.localRep id (w : ExtPlane) = fun ζ => ζ := by
    funext ζ
    show (w + ζ : ℂ) - w = ζ
    ring
  rw [this]
  exact differentiableAt_id

/-- Helper (Stage B1): a round annulus `{a < |z| < b}`, `0 < a < b`, is a ring domain of `ℂ̄`. -/
theorem gm5_annulus_isRing {a b : ℝ} (ha : 0 < a) (hab : a < b) : IsRingDomain (toExt (annulus a b)) := by
  obtain ⟨hAo, hAc⟩ := gm5_annulus_oc ha.le hab
  have hb : 0 < b := ha.trans hab
  set T : Set ℂ := {z | b ≤ ‖z‖} with hT
  set S₁ : Set ExtPlane := toExt (closedBall 0 a) with hS₁
  set S₂ : Set ExtPlane := toExt T ∪ {extInf} with hS₂
  have hS₁c : IsClosed S₁ := ((isCompact_closedBall (0 : ℂ) a).image OnePoint.continuous_coe).isClosed
  have hS₂c : IsClosed S₂ := by
    have : S₂ = (toExt (ball (0 : ℂ) b))ᶜ := by
      ext x
      induction x using OnePoint.rec with
      | infty =>
        simp only [hS₂, mem_union, mem_singleton_iff, mem_compl_iff, and_true, toExt, mem_image]
        constructor
        · rintro _ ⟨w, _, hw⟩; exact absurd hw (OnePoint.coe_ne_infty w)
        · intro _; exact Or.inr trivial
      | coe z =>
        simp only [hS₂, mem_union, mem_singleton_iff, mem_compl_iff, toExt, mem_image, hT, Set.mem_ofPred_eq]
        constructor
        · rintro (⟨w, hw, hwz⟩ | h)
          · rintro ⟨v, hv, hvz⟩
            have hwv : w = v := (OnePoint.coe_injective hwz).trans (OnePoint.coe_injective hvz).symm
            rw [hwv] at hw
            exact absurd (mem_ball_zero_iff.1 hv) (not_lt.2 hw)
          · exact absurd h (OnePoint.coe_ne_infty z)
        · intro h
          left
          refine ⟨z, ?_, rfl⟩
          by_contra hlt
          exact h ⟨z, mem_ball_zero_iff.2 (not_le.1 hlt), rfl⟩
    rw [this]
    exact (OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball).isClosed_compl
  have hunion : (toExt (annulus a b))ᶜ = S₁ ∪ S₂ := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [mem_compl_iff, mem_union, hS₂, mem_singleton_iff, or_true, iff_true]
      rintro ⟨w, _, hw⟩; exact OnePoint.coe_ne_infty w hw
    | coe z =>
      simp only [mem_compl_iff, mem_union, hS₁, hS₂, toExt, mem_image, hT, Set.mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro h
        by_cases h1 : ‖z‖ ≤ a
        · exact Or.inl ⟨z, mem_closedBall_zero_iff.2 h1, rfl⟩
        · refine Or.inr (Or.inl ⟨z, ?_, rfl⟩)
          by_contra h2
          exact h ⟨z, ⟨not_le.1 h1, not_le.1 h2⟩, rfl⟩
      · rintro (⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩ | h) ⟨v, hv, hvz⟩
        · have := OnePoint.coe_injective (hwz.trans hvz.symm)
          rw [← this] at hv
          exact absurd (mem_closedBall_zero_iff.1 hw) (not_le.2 hv.1)
        · have := OnePoint.coe_injective (hwz.trans hvz.symm)
          rw [← this] at hv
          exact absurd hw (not_le.2 hv.2)
        · exact OnePoint.coe_ne_infty z h
  have hd : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨w, hw, rfl⟩ (⟨v, hv, hvw⟩ | h)
    · have := OnePoint.coe_injective hvw
      rw [this] at hv
      exact absurd (mem_closedBall_zero_iff.1 hw) (not_le.2 (lt_of_lt_of_le hab hv))
    · exact OnePoint.coe_ne_infty w h
  have hp₁ : IsPreconnected S₁ :=
    (convex_closedBall (0 : ℂ) a).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hp₂ : IsPreconnected S₂ := gm5_outer_conn hb
  refine ⟨⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ hAo,
    ⟨hAc.nonempty.image _, hAc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn⟩⟩, by norm_num, ?_⟩
  refine gm5_two_components hS₁c hS₂c hd hp₁ hp₂ ⟨_, ⟨0, mem_closedBall_self ha.le, rfl⟩⟩ ⟨extInf, Or.inr rfl⟩ hunion

/-- Helper (Stage B1; the circle case). If `J = {|z| = r}`, the two ring domains are the two round annuli. -/
theorem gm5_circle_comps {R₁ R₂ r : ℝ} {Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ (sphere 0 r) Ω₁ Ω₂) :
    R₁ < r ∧ r < R₂ ∧ Ω₁ = annulus R₁ r ∧ Ω₂ = annulus r R₂ := by
  obtain ⟨hR1, hR12, -, hJconn, hJA, ⟨z₁, hz₁, hΩ₁⟩, ⟨z₂, hz₂, hΩ₂⟩, hdisj, -, -, hs1, hs2⟩ := hconf
  obtain ⟨p, hp⟩ := hJconn.nonempty
  have hpr : ‖p‖ = r := mem_sphere_zero_iff_norm.1 hp
  have hpA := hJA hp
  have hr1 : R₁ < r := hpr ▸ hpA.1
  have hr2 : r < R₂ := hpr ▸ hpA.2
  have hr0 : 0 < r := hR1.trans hr1
  refine ⟨hr1, hr2, ?_⟩
  set I := annulus R₁ r with hI
  set O := annulus r R₂ with hO
  have hIo := gm5_isOpen_annulus R₁ r
  have hOo := gm5_isOpen_annulus r R₂
  have hIc : IsPreconnected I := gm5_annulus_conn hR1.le r
  have hOc : IsPreconnected O := gm5_annulus_conn hr0.le R₂
  have hIO : Disjoint I O := by
    rw [Set.disjoint_left]
    intro z hzI hzO
    exact absurd hzI.2 (not_lt.2 hzO.1.le)
  have hcov : annulus R₁ R₂ \ sphere 0 r ⊆ I ∪ O := by
    rintro z ⟨⟨h1, h2⟩, h3⟩
    rw [mem_sphere_zero_iff_norm] at h3
    rcases lt_or_gt_of_ne h3 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩
  have hΩ₁sub : Ω₁ ⊆ annulus R₁ R₂ \ sphere 0 r := hΩ₁ ▸ connectedComponentIn_subset _ _
  have hΩ₂sub : Ω₂ ⊆ annulus R₁ R₂ \ sphere 0 r := hΩ₂ ▸ connectedComponentIn_subset _ _
  have hΩ₁c : IsPreconnected Ω₁ := hΩ₁ ▸ isPreconnected_connectedComponentIn
  have hΩ₂c : IsPreconnected Ω₂ := hΩ₂ ▸ isPreconnected_connectedComponentIn
  have hz₁Ω : z₁ ∈ Ω₁ := hΩ₁ ▸ mem_connectedComponentIn hz₁
  have hz₂Ω : z₂ ∈ Ω₂ := hΩ₂ ▸ mem_connectedComponentIn hz₂
  have h1I : Ω₁ ⊆ I := by
    rcases hΩ₁c.subset_or_subset hIo hOo hIO ((hΩ₁sub).trans hcov) with h | h
    · exact h
    · exfalso
      have hq : ((R₁ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₁ := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR1.le]
      have hcl : ((R₁ : ℝ) : ℂ) ∈ closure Ω₁ := (hs1 hq).1
      have := closure_mono h hcl
      have hO' : closure O ⊆ {z | r ≤ ‖z‖} := closure_minimal (fun z hz => hz.1.le)
        (isClosed_le continuous_const continuous_norm)
      have := hO' this
      rw [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg hR1.le] at this
      linarith
  have h2O : Ω₂ ⊆ O := by
    rcases hΩ₂c.subset_or_subset hIo hOo hIO ((hΩ₂sub).trans hcov) with h | h
    · exfalso
      have hq : ((R₂ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₂ := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (hR1.le.trans hR12.le)]
      have hcl : ((R₂ : ℝ) : ℂ) ∈ closure Ω₂ := (hs2 hq).1
      have := closure_mono h hcl
      have hI' : closure I ⊆ {z | ‖z‖ ≤ r} := closure_minimal (fun z hz => hz.2.le)
        (isClosed_le continuous_norm continuous_const)
      have := hI' this
      rw [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg (hR1.le.trans hR12.le)] at this
      linarith
    · exact h
  have hIsub : I ⊆ annulus R₁ R₂ \ sphere 0 r := fun z hz =>
    ⟨⟨hz.1, hz.2.trans hr2⟩, fun h => by rw [mem_sphere_zero_iff_norm] at h; exact absurd hz.2 (not_lt.2 h.ge)⟩
  have hOsub : O ⊆ annulus R₁ R₂ \ sphere 0 r := fun z hz =>
    ⟨⟨hr1.trans hz.1, hz.2⟩, fun h => by rw [mem_sphere_zero_iff_norm] at h; exact absurd hz.1 (not_lt.2 h.le)⟩
  constructor
  · refine subset_antisymm h1I ?_
    rw [← hΩ₁]
    exact hIc.subset_connectedComponentIn (h1I hz₁Ω) hIsub
  · refine subset_antisymm h2O ?_
    rw [← hΩ₂]
    exact hOc.subset_connectedComponentIn (h2O hz₂Ω) hOsub

/-- Helper (Stage B1): the module of a round annulus. -/
theorem gm5_annulus_mod {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ringModGM (toExt (annulus a b)) = ENNReal.ofReal (1 / (2 * π) * Real.log (b / a)) := by
  have hcpt : IsCompact (toExt (closedBall (0 : ℂ) b)) :=
    (isCompact_closedBall (0 : ℂ) b).image OnePoint.continuous_coe
  have hsub : toExt (annulus a b) ⊆ toExt (closedBall (0 : ℂ) b) :=
    image_mono fun w hw => mem_closedBall_zero_iff.2 hw.2.le
  have hbdd : extInf ∉ closure (toExt (annulus a b)) := fun h =>
    OnePoint.infty_notMem_image_coe (closure_minimal hsub hcpt.isClosed h)
  have := gm5_ringMod_bounded (gm5_annulus_isRing ha hab) (ψ := id) ha hab (gm5_id_conformal ha.le hab)
    (by rw [image_id]) hbdd
  exact this.1

/-- Helper (Stage B1): the inverse extremal length of the family separating the circles of the round annulus. -/
theorem gm5_annulus_sep_inv {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (extremalLengthGM (annulus a b) (separatingFamily (annulus a b) (sphere 0 a) (sphere 0 b)))⁻¹ =
      ENNReal.ofReal (1 / (2 * π) * Real.log (b / a)) := by
  have h := gm4c_annulus_slit_sep_value ha hab (S := ∅) (Θ := ∅) Set.finite_empty (by simp)
  have hlog : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).2 hab)
  rw [sdiff_empty] at h
  have h' : extremalLengthGM (annulus a b) (separatingFamily (annulus a b) (sphere 0 a) (sphere 0 b)) =
      ENNReal.ofReal (2 * π / Real.log (b / a)) := h
  rw [h', ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- Helper (Stage B1): `Ω₁` and `Ω₂` are ring domains. -/
theorem gm5_conf_ring {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) : IsRingDomain (toExt Ω) := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -⟩ := hconf
  rcases hΩ with rfl | rfl
  · exact h1
  · exact h2

/-- Helper (Stage B1): a bounded set has `∞` outside the closure of its image in `ℂ̄`. -/
theorem gm5_infty_notMem_closure {S : Set ℂ} {R : ℝ} (h : S ⊆ closedBall 0 R) :
    extInf ∉ closure (toExt S) := by
  have hcpt : IsCompact (toExt (closedBall (0 : ℂ) R)) :=
    (isCompact_closedBall (0 : ℂ) R).image OnePoint.continuous_coe
  exact fun hc => OnePoint.infty_notMem_image_coe (closure_minimal (image_mono h) hcpt.isClosed hc)

/-- Helper (Stage B1): points with the same class in `ConnectedComponents` have the same `connectedComponentIn`. -/
theorem gm5_compIn_eq_of_class {F : Set ExtPlane} {x y : ExtPlane} (hx : x ∈ F) (hy : y ∈ F)
    (h : (ConnectedComponents.mk (⟨x, hx⟩ : ↥F)) = ConnectedComponents.mk (⟨y, hy⟩ : ↥F)) :
    connectedComponentIn F x = connectedComponentIn F y := by
  rw [ConnectedComponents.coe_eq_coe] at h
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy, h]

/-- Helper (Stage B1): in a type with exactly two elements, two distinct elements exhaust it. -/
theorem gm5_card_two {α : Type*} (h : Nat.card α = 2) {u v : α} (huv : u ≠ v) (q : α) : q = u ∨ q = v := by
  obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ x, x = a ∨ x = b := fun x => by
    have : x ∈ ({a, b} : Set α) := hall ▸ mem_univ x
    simpa using this
  by_contra hno
  push Not at hno
  rcases hmem u with hu | hu <;> rcases hmem v with hv | hv <;> rcases hmem q with hq | hq <;>
    first | exact huv (hu.trans hv.symm) | exact hno.1 (hq.trans hu.symm) | exact hno.2 (hq.trans hv.symm)

/-- Helper (Stage B1): the complement of a ring domain of the annulus configuration has no one-point component. -/
theorem gm5_nondeg {Ω : Set ℂ} {R₁ R₂ ρ : ℝ} (hR1 : 0 < R₁) (hR12 : R₁ < R₂) (hΩA : Ω ⊆ annulus R₁ R₂)
    (hring : IsRingDomain (toExt Ω)) (hρ0 : 0 < ρ) (hρ : sphere (0 : ℂ) ρ ⊆ Ω) :
    ∀ x ∈ (toExt Ω)ᶜ, connectedComponentIn (toExt Ω)ᶜ x ≠ {x} := by
  have hcard := hring.2.2
  set Bc : Set ExtPlane := (toExt Ω)ᶜ with hBc
  -- two open sets covering `Bc`
  set P : Set ExtPlane := toExt (ball (0 : ℂ) ρ) with hP
  set Qs : Set ExtPlane := (toExt (closedBall (0 : ℂ) ρ))ᶜ with hQs
  have hPo : IsOpen P := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
  have hQo : IsOpen Qs := (((isCompact_closedBall (0 : ℂ) ρ).image OnePoint.continuous_coe).isClosed).isOpen_compl
  have hPQ : Disjoint P Qs := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ h
    exact h ⟨z, ball_subset_closedBall hz, rfl⟩
  have hcov : Bc ⊆ P ∪ Qs := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (by rintro ⟨w, _, hw⟩; exact OnePoint.coe_ne_infty w hw)
    | coe z =>
      by_cases hz : ‖z‖ < ρ
      · exact Or.inl ⟨z, mem_ball_zero_iff.2 hz, rfl⟩
      · right
        rintro ⟨w, hw, hwz⟩
        have hwz' := OnePoint.coe_injective hwz
        rw [hwz'] at hw
        have hle : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 hw
        have : ‖z‖ = ρ := le_antisymm hle (not_lt.1 hz)
        exact hx ⟨z, hρ (mem_sphere_zero_iff_norm.2 this), rfl⟩
  have h0 : ((0 : ℂ) : ExtPlane) ∈ Bc := by
    rintro ⟨w, hw, hw0⟩
    have := OnePoint.coe_injective hw0
    rw [this] at hw
    have h1 := (hΩA hw).1
    rw [norm_zero] at h1
    linarith
  have hinf : extInf ∈ Bc := by
    rintro ⟨w, _, hw⟩; exact OnePoint.coe_ne_infty w hw
  have h0P : ((0 : ℂ) : ExtPlane) ∈ P := ⟨0, by rw [mem_ball_zero_iff, norm_zero]; exact hρ0, rfl⟩
  have hinfQ : extInf ∈ Qs := by
    rintro ⟨w, _, hw⟩; exact OnePoint.coe_ne_infty w hw
  have hne : (ConnectedComponents.mk (⟨((0 : ℂ) : ExtPlane), h0⟩ : ↥Bc)) ≠
      ConnectedComponents.mk (⟨extInf, hinf⟩ : ↥Bc) := by
    intro h
    have hE := gm5_compIn_eq_of_class h0 hinf h
    have hsub : connectedComponentIn Bc ((0 : ℂ) : ExtPlane) ⊆ P ∪ Qs :=
      (connectedComponentIn_subset _ _).trans hcov
    rcases isPreconnected_connectedComponentIn.subset_or_subset hPo hQo hPQ hsub with h1 | h1
    · have : extInf ∈ connectedComponentIn Bc ((0 : ℂ) : ExtPlane) := hE ▸ mem_connectedComponentIn hinf
      exact Set.disjoint_left.1 hPQ (h1 this) hinfQ
    · exact Set.disjoint_left.1 hPQ h0P (h1 (mem_connectedComponentIn h0))
  have hcls := gm5_card_two hcard hne
  intro x hx hxeq
  have hR2 : 0 < R₂ := hR1.trans hR12
  -- the component of `0` contains `↑R₁`
  have hin0 : ((R₁ : ℝ) : ℂ) ∈ closedBall (0 : ℂ) R₁ := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR1.le]
  have hsub0 : toExt (closedBall (0 : ℂ) R₁) ⊆ Bc := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have := OnePoint.coe_injective hwz
    rw [this] at hw
    exact absurd (mem_closedBall_zero_iff.1 hz) (not_le.2 (hΩA hw).1)
  have hpre0 : IsPreconnected (toExt (closedBall (0 : ℂ) R₁)) :=
    (convex_closedBall (0 : ℂ) R₁).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have h0comp : (((R₁ : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn Bc ((0 : ℂ) : ExtPlane) :=
    hpre0.subset_connectedComponentIn ⟨0, mem_closedBall_self hR1.le, rfl⟩ hsub0 ⟨_, hin0, rfl⟩
  -- the component of `∞` contains `↑R₂`
  have hsubI : toExt {z : ℂ | R₂ ≤ ‖z‖} ∪ {extInf} ⊆ Bc := by
    rintro _ (⟨z, hz, rfl⟩ | h)
    · rintro ⟨w, hw, hwz⟩
      have := OnePoint.coe_injective hwz
      rw [this] at hw
      exact absurd (hΩA hw).2 (not_lt.2 hz)
    · rw [mem_singleton_iff.1 h]; exact hinf
  have hinfcomp : (((R₂ : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn Bc extInf :=
    (gm5_outer_conn hR2).subset_connectedComponentIn (Or.inr rfl) hsubI
      (Or.inl ⟨((R₂ : ℝ) : ℂ), by
        simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg hR2.le]
        exact le_rfl, rfl⟩)
  have hne0 : (((R₁ : ℝ) : ℂ) : ExtPlane) ≠ ((0 : ℂ) : ExtPlane) := fun h =>
    hR1.ne' (by simpa using OnePoint.coe_injective h)
  have hneinf : (((R₂ : ℝ) : ℂ) : ExtPlane) ≠ extInf := OnePoint.coe_ne_infty _
  rcases hcls (ConnectedComponents.mk ⟨x, hx⟩) with hcl | hcl
  · have heq := gm5_compIn_eq_of_class hx h0 hcl
    rw [hxeq] at heq
    have h1 : ((0 : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := heq ▸ mem_connectedComponentIn h0
    have h2 : (((R₁ : ℝ) : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := heq ▸ h0comp
    exact hne0 ((mem_singleton_iff.1 h2).trans (mem_singleton_iff.1 h1).symm)
  · have heq := gm5_compIn_eq_of_class hx hinf hcl
    rw [hxeq] at heq
    have h1 : extInf ∈ ({x} : Set ExtPlane) := heq ▸ mem_connectedComponentIn hinf
    have h2 : (((R₂ : ℝ) : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := heq ▸ hinfcomp
    exact hneinf ((mem_singleton_iff.1 h2).trans (mem_singleton_iff.1 h1).symm)

/-- Helper (Stage B1; models of the two ring domains). In the configuration of Theorem 4.1, `Ω₁` and `Ω₂` are each
conformally equivalent to a round annulus `{r₁ < |w| < r₂}`, `0 < r₁ < r₂` (Theorem 2.1(iii)); the map is a conformal
map of `Ω` in the sense of Lehto–Virtanen, as Stage A consumes it. -/
theorem gm5_ring_model {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ∃ ψ : ExtPlane → ExtPlane,
      LehtoVirtanen1973.IsConformalMap ψ (toExt Ω) ∧ ψ '' toExt Ω = toExt (annulus r₁ r₂) := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  obtain ⟨hΩo, hΩc, hΩA⟩ := gm5_conf_comp hconf hΩ
  have hring := gm5_conf_ring hconf hΩ
  -- a full circle inside `Ω`
  obtain ⟨a, b, haR, hab, hbR, hshell1, hshell2, -⟩ := gm5_shells hconf
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ sphere (0 : ℂ) ρ ⊆ Ω := by
    rcases hΩ with rfl | rfl
    · refine ⟨(R₁ + a) / 2, by linarith, fun z hz => hshell1 ?_⟩
      rw [mem_sphere_zero_iff_norm] at hz
      exact ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
    · refine ⟨(b + R₂) / 2, by linarith, fun z hz => hshell2 ?_⟩
      rw [mem_sphere_zero_iff_norm] at hz
      exact ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
  have hnd := gm5_nondeg hR1 hR12 hΩA hring hρ0 hρ
  have hdc : LiZhongQC.IsDoublyConnected Ω := ⟨hΩo, hΩc, hring.2.2⟩
  obtain ⟨r₁, r₂, hr₁, hr₁₂, f, hf⟩ := LiZhongQC.thm2_1_canonical_form_annulus hdc hnd
  set ψ : ExtPlane → ExtPlane := fun p => OnePoint.elim p extInf (fun z => ((f z : ℂ) : ExtPlane)) with hψ
  have hψc : ∀ z : ℂ, ψ (z : ExtPlane) = ((f z : ℂ) : ExtPlane) := fun z => rfl
  refine ⟨r₁, r₂, hr₁, hr₁₂, ψ, ?_, ?_⟩
  · refine ⟨⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩo,
      ⟨hΩc.nonempty.image _, hΩc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn⟩⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hfc : ContinuousAt f z := (hf.1.differentiableAt (hΩo.mem_nhds hz)).continuousAt
      have : ContinuousAt ψ (z : ExtPlane) := by
        rw [ContinuousAt, ← OnePoint.isOpenEmbedding_coe.map_nhds_eq, tendsto_map'_iff]
        exact (OnePoint.continuous_coe.continuousAt.tendsto.comp hfc)
      exact this.continuousWithinAt
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
      rw [hψc, hψc] at h
      rw [hf.2.1 ha hb (OnePoint.coe_injective h)]
    · rintro _ ⟨z, hz, rfl⟩
      have hloc : LehtoVirtanen1973.localRep ψ (z : ExtPlane) = fun ζ => f (z + ζ) - f z := rfl
      rw [hloc]
      have hd : DifferentiableAt ℂ f (z + 0) := by
        rw [add_zero]; exact hf.1.differentiableAt (hΩo.mem_nhds hz)
      exact ((hd.comp (0 : ℂ) (differentiableAt_const z |>.add differentiableAt_id)).sub_const (f z))
  · ext x
    induction x using OnePoint.rec with
    | infty =>
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, h⟩
        exact absurd ((hψc z).symm.trans h) (OnePoint.coe_ne_infty _)
      · rintro ⟨w, _, hw⟩; exact absurd hw (OnePoint.coe_ne_infty w)
    | coe w =>
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, h⟩
        rw [hψc] at h
        exact ⟨f z, hf.2.2 ▸ mem_image_of_mem f hz, h⟩
      · rintro ⟨v, hv, hvw⟩
        rw [← hf.2.2] at hv
        obtain ⟨z, hz, rfl⟩ := hv
        exact ⟨z, ⟨z, hz, rfl⟩, by rw [hψc]; exact hvw⟩

/-- Helper (Stage A): the closure of the inner part of `g(annulus)` lies in `U` or in the inner cluster set. -/
theorem gm5_closure_in2 {U : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} {Cin : Set ℂ} (hg : IsConformalOnto g (annulus r R) U)
    (hCin : ∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < r + ε})) (hsR : s < R) :
    closure (g '' {w | r < ‖w‖ ∧ ‖w‖ < s}) ⊆ g '' {w | r < ‖w‖ ∧ ‖w‖ ≤ s} ∪ Cin := by
  intro p hp
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose w hw hxw using hxmem
  have hK : IsCompact ({w : ℂ | r ≤ ‖w‖} ∩ closedBall 0 s) :=
    (isCompact_closedBall 0 s).inter_left (isClosed_le continuous_const continuous_norm)
  have hwK : ∀ n, w n ∈ {w : ℂ | r ≤ ‖w‖} ∩ closedBall 0 s := fun n =>
    ⟨(hw n).1.le, mem_closedBall_zero_iff.2 (hw n).2.le⟩
  obtain ⟨q, hqK, φ, hφ, hqlim⟩ := hK.tendsto_subseq hwK
  have hqn : r ≤ ‖q‖ := hqK.1
  have hqs : ‖q‖ ≤ s := mem_closedBall_zero_iff.1 hqK.2
  have hlim : Tendsto (fun n => g (w (φ n))) atTop (𝓝 p) := by
    have := hxlim.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, hxw]
  rcases hqn.lt_or_eq with hrq | hrq
  · left
    have hqA : q ∈ annulus r R := ⟨hrq, lt_of_le_of_lt hqs hsR⟩
    have hgq : Tendsto (fun n => g (w (φ n))) atTop (𝓝 (g q)) :=
      (hg.1.continuousOn.continuousAt (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const) |>.mem_nhds hqA)).tendsto.comp hqlim
    have : p = g q := tendsto_nhds_unique hlim hgq
    rw [this]
    exact ⟨q, ⟨hrq, hqs⟩, rfl⟩
  · right
    refine (hCin p).2 fun ε hε => mem_closure_of_tendsto hlim ?_
    have hn : Tendsto (fun n => ‖w (φ n)‖) atTop (𝓝 r) := by
      rw [hrq]; exact (continuous_norm.tendsto q).comp hqlim
    filter_upwards [hn.eventually (gt_mem_nhds (by linarith : r < r + ε))] with n hn
    exact ⟨w (φ n), ⟨(hw (φ n)).1, hn⟩, rfl⟩

/-- Helper (Stage A): the closure of the outer part of `g(annulus)` lies in `U` or in the outer cluster set. -/
theorem gm5_closure_out2 {U : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} {Cout : Set ℂ} (hg : IsConformalOnto g (annulus r R) U)
    (hCout : ∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | R - ε < ‖w‖ ∧ ‖w‖ < R})) (hrs : r < s) :
    closure (g '' {w | s < ‖w‖ ∧ ‖w‖ < R}) ⊆ g '' {w | s ≤ ‖w‖ ∧ ‖w‖ < R} ∪ Cout := by
  intro p hp
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose w hw hxw using hxmem
  have hK : IsCompact ({w : ℂ | s ≤ ‖w‖} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_norm)
  have hwK : ∀ n, w n ∈ {w : ℂ | s ≤ ‖w‖} ∩ closedBall 0 R := fun n =>
    ⟨(hw n).1.le, mem_closedBall_zero_iff.2 (hw n).2.le⟩
  obtain ⟨q, hqK, φ, hφ, hqlim⟩ := hK.tendsto_subseq hwK
  have hqn : s ≤ ‖q‖ := hqK.1
  have hqs : ‖q‖ ≤ R := mem_closedBall_zero_iff.1 hqK.2
  have hlim : Tendsto (fun n => g (w (φ n))) atTop (𝓝 p) := by
    have := hxlim.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, hxw]
  rcases hqs.lt_or_eq with hrq | hrq
  · left
    have hqA : q ∈ annulus r R := ⟨lt_of_lt_of_le hrs hqn, hrq⟩
    have hgq : Tendsto (fun n => g (w (φ n))) atTop (𝓝 (g q)) :=
      (hg.1.continuousOn.continuousAt (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const) |>.mem_nhds hqA)).tendsto.comp hqlim
    have : p = g q := tendsto_nhds_unique hlim hgq
    rw [this]
    exact ⟨q, ⟨hqn, hrq⟩, rfl⟩
  · right
    refine (hCout p).2 fun ε hε => mem_closure_of_tendsto hlim ?_
    have hn : Tendsto (fun n => ‖w (φ n)‖) atTop (𝓝 R) := by
      rw [← hrq]; exact (continuous_norm.tendsto q).comp hqlim
    filter_upwards [hn.eventually (lt_mem_nhds (by linarith : R - ε < R))] with n hn
    exact ⟨w (φ n), ⟨hn, (hw (φ n)).2⟩, rfl⟩

/-- Helper (Stage B1): a point of `A` in the closure of a component of `A \ J`, but not in it, lies in `J`. -/
theorem gm5_frontier_in_J {A J Ω : Set ℂ} {z : ℂ} (hA : IsOpen A) (hJ : IsClosed J) (hz : z ∈ A \ J)
    (hΩ : connectedComponentIn (A \ J) z = Ω) {p : ℂ} (hpA : p ∈ A) (hp : p ∈ closure Ω) (hpΩ : p ∉ Ω) : p ∈ J := by
  by_contra hpJ
  have hAJ : IsOpen (A \ J) := hA.sdiff hJ
  have hpAJ : p ∈ A \ J := ⟨hpA, hpJ⟩
  obtain ⟨w, hwC, hwΩ⟩ := mem_closure_iff.1 hp _ hAJ.connectedComponentIn (mem_connectedComponentIn hpAJ)
  have h1 : connectedComponentIn (A \ J) p = connectedComponentIn (A \ J) w := connectedComponentIn_eq hwC
  have h2 : connectedComponentIn (A \ J) z = connectedComponentIn (A \ J) w := connectedComponentIn_eq (hΩ ▸ hwΩ)
  apply hpΩ
  rw [← hΩ, h2, ← h1]
  exact mem_connectedComponentIn hpAJ

/-- Helper (Stage B1): the facts about a configuration domain next to its adjacent boundary circle `c`. -/
theorem gm5_conf_facts {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) :
    ∃ c c' : ℝ, ((c = R₁ ∧ c' = R₂) ∨ (c = R₂ ∧ c' = R₁)) ∧ sphere (0 : ℂ) c ⊆ frontier Ω ∧
      Disjoint (closure Ω) (sphere (0 : ℂ) c') ∧ frontier Ω ⊆ sphere (0 : ℂ) c ∪ J ∧
      ∀ q ∈ sphere (0 : ℂ) c, ∃ ε > 0, ball q ε ∩ annulus R₁ R₂ ⊆ Ω := by
  obtain ⟨a, b, haR, hab, hbR, hshell1, hshell2, hJab⟩ := gm5_shells hconf
  obtain ⟨hΩo, -, hΩA⟩ := gm5_conf_comp hconf hΩ
  have hdisj : Disjoint Ω₁ Ω₂ := hconf.2.2.2.2.2.2.2.1
  obtain ⟨hR1, hR12, hJk, hJconn, hJA, ⟨z₁, hz₁, hΩ₁⟩, ⟨z₂, hz₂, hΩ₂⟩, -, -, -, hs1, hs2⟩ := hconf
  have hAo := gm5_isOpen_annulus R₁ R₂
  have hJcl : IsClosed J := hJk.isClosed
  have hint : interior Ω = Ω := hΩo.interior_eq
  rcases hΩ with rfl | rfl
  · refine ⟨R₁, R₂, Or.inl ⟨rfl, rfl⟩, hs1, ?_, ?_, ?_⟩
    · have hle : Ω ⊆ {z | ‖z‖ ≤ b} := fun z hz => by
        by_contra hlt
        exact Set.disjoint_left.1 hdisj hz (hshell2 ⟨not_le.1 hlt, (hΩA hz).2⟩)
      have hcl : closure Ω ⊆ {z | ‖z‖ ≤ b} := closure_minimal hle
        (isClosed_le continuous_norm continuous_const)
      rw [Set.disjoint_left]
      intro p hp hps
      have := hcl hp
      rw [mem_sphere_zero_iff_norm] at hps
      simp only [Set.mem_ofPred_eq] at this
      linarith
    · intro p hp
      have hcl : closure Ω ⊆ {z | R₁ ≤ ‖z‖} := closure_minimal (fun z hz => (hΩA hz).1.le)
        (isClosed_le continuous_const continuous_norm)
      have hle : closure Ω ⊆ {z | ‖z‖ ≤ b} := closure_minimal (fun z hz => by
        by_contra hlt
        exact Set.disjoint_left.1 hdisj hz (hshell2 ⟨not_le.1 hlt, (hΩA hz).2⟩))
        (isClosed_le continuous_norm continuous_const)
      have hpcl := hp.1
      have hpnot : p ∉ Ω := fun h => hp.2 (interior_maximal subset_rfl hΩo h)
      have h1 : R₁ ≤ ‖p‖ := hcl hpcl
      have h2 : ‖p‖ ≤ b := hle hpcl
      rcases h1.lt_or_eq with h1' | h1'
      · right
        exact gm5_frontier_in_J hAo hJcl hz₁ hΩ₁ ⟨h1', h2.trans_lt hbR⟩ hpcl hpnot
      · left
        rw [mem_sphere_zero_iff_norm]; exact h1'.symm
    · intro q hq
      refine ⟨a - R₁, by linarith, fun z hz => hshell1 ⟨(hz.2).1, ?_⟩⟩
      have hqn : ‖q‖ = R₁ := mem_sphere_zero_iff_norm.1 hq
      have : ‖z‖ ≤ ‖q‖ + dist z q := by
        calc ‖z‖ = ‖q + (z - q)‖ := by ring_nf
          _ ≤ ‖q‖ + ‖z - q‖ := norm_add_le _ _
          _ = ‖q‖ + dist z q := by rw [dist_eq_norm]
      have hd : dist z q < a - R₁ := hz.1
      linarith
  · refine ⟨R₂, R₁, Or.inr ⟨rfl, rfl⟩, hs2, ?_, ?_, ?_⟩
    · have hle : Ω ⊆ {z | a ≤ ‖z‖} := fun z hz => by
        by_contra hlt
        exact Set.disjoint_left.1 hdisj (hshell1 ⟨(hΩA hz).1, not_le.1 hlt⟩) hz
      have hcl : closure Ω ⊆ {z | a ≤ ‖z‖} := closure_minimal hle (isClosed_le continuous_const continuous_norm)
      rw [Set.disjoint_left]
      intro p hp hps
      have := hcl hp
      rw [mem_sphere_zero_iff_norm] at hps
      simp only [Set.mem_ofPred_eq] at this
      linarith
    · intro p hp
      have hcl : closure Ω ⊆ {z | ‖z‖ ≤ R₂} := closure_minimal (fun z hz => (hΩA hz).2.le)
        (isClosed_le continuous_norm continuous_const)
      have hle : closure Ω ⊆ {z | a ≤ ‖z‖} := closure_minimal (fun z hz => by
        by_contra hlt
        exact Set.disjoint_left.1 hdisj (hshell1 ⟨(hΩA hz).1, not_le.1 hlt⟩) hz)
        (isClosed_le continuous_const continuous_norm)
      have hpcl := hp.1
      have hpnot : p ∈ Ω → False := fun h => hp.2 (interior_maximal subset_rfl hΩo h)
      have h1 : ‖p‖ ≤ R₂ := hcl hpcl
      have h2 : a ≤ ‖p‖ := hle hpcl
      rcases h1.lt_or_eq with h1' | h1'
      · right
        exact gm5_frontier_in_J hAo hJcl hz₂ hΩ₂ ⟨haR.trans_le h2, h1'⟩ hpcl hpnot
      · left
        rw [mem_sphere_zero_iff_norm]; exact h1'
    · intro q hq
      refine ⟨R₂ - b, by linarith, fun z hz => hshell2 ⟨?_, (hz.2).2⟩⟩
      have hqn : ‖q‖ = R₂ := mem_sphere_zero_iff_norm.1 hq
      have : ‖q‖ ≤ ‖z‖ + dist z q := by
        calc ‖q‖ = ‖z + (q - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖q - z‖ := norm_add_le _ _
          _ = ‖z‖ + dist z q := by rw [dist_comm, dist_eq_norm]
      have hd : dist z q < R₂ - b := hz.1
      linarith

/-- Helper (Stage B1): `IsSeparatingIn` is symmetric in the two sets. -/
theorem gm5_isSeparatingIn_symm {Ω S E F : Set ℂ} (h : IsSeparatingIn Ω S E F) : IsSeparatingIn Ω S F E :=
  fun x hx hh => h x hx ⟨hh.2, hh.1⟩

/-- Helper (Stage B1; the topological core). The curve `γ` of the domain `Ω ⊆ A` splits `A \ γ` into two open parts, one
whose closure reaches only the circle `sc` (outside `A`), the other only `A` and the part of `A` outside `Ω`; hence no
component of `A \ γ` has closure meeting both `sc` and `sc'`. -/
theorem gm5_sep_core {A Ω γ VP VQ Q sc sc' : Set ℂ} (hA : IsOpen A) (hΩA : Ω ⊆ A) (hγ : γ ⊆ Ω) (hγc : IsClosed γ)
    (hVPo : IsOpen VP) (hVQo : IsOpen VQ) (hdisj : Disjoint VP VQ) (hcov : VP ∪ VQ = Ω \ γ)
    (hscA : Disjoint sc A) (hQA : Q ⊆ A) (hscsc : Disjoint sc sc')
    (hVP : closure VP ⊆ VP ∪ γ ∪ sc) (hVQ : closure VQ ⊆ VQ ∪ γ ∪ Q)
    (hnear : Disjoint (closure (A \ Ω)) sc) (hfar : Disjoint (closure Ω) sc') :
    IsSeparatingIn A γ sc sc' := by
  have hVPΩ : VP ⊆ Ω := fun z hz => (hcov ▸ Or.inl hz : z ∈ Ω \ γ).1
  have hVQΩ : VQ ⊆ Ω := fun z hz => (hcov ▸ Or.inr hz : z ∈ Ω \ γ).1
  set N₁ := VP with hN₁
  set N₂ := VQ ∪ (A \ Ω) with hN₂
  have hsplit : A \ γ = N₁ ∪ N₂ := by
    ext z
    constructor
    · rintro ⟨hzA, hzγ⟩
      by_cases hzΩ : z ∈ Ω
      · have : z ∈ Ω \ γ := ⟨hzΩ, hzγ⟩
        rw [← hcov] at this
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hzA, hzΩ⟩)
    · rintro (h | h | h)
      · exact ⟨hΩA (hVPΩ h), fun hg => (hcov ▸ Or.inl h : z ∈ Ω \ γ).2 hg⟩
      · exact ⟨hΩA (hVQΩ h), fun hg => (hcov ▸ Or.inr h : z ∈ Ω \ γ).2 hg⟩
      · exact ⟨h.1, fun hg => h.2 (hγ hg)⟩
  have hN₂o : IsOpen N₂ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hx with hx | hx
    · exact Filter.mem_of_superset (hVQo.mem_nhds hx) (fun z hz => Or.inl hz)
    · -- `x ∈ A \ Ω`
      have hxcl : x ∉ closure VP ∪ γ := by
        rintro (h | h)
        · rcases hVP h with (h' | h') | h'
          · exact hx.2 (hVPΩ h')
          · exact hx.2 (hγ h')
          · exact Set.disjoint_left.1 hscA h' hx.1
        · exact hx.2 (hγ h)
      have hclo : IsClosed (closure VP ∪ γ) := isClosed_closure.union hγc
      have hW : (closure VP ∪ γ)ᶜ ∩ A ∈ nhds x :=
        Filter.inter_mem (hclo.isOpen_compl.mem_nhds hxcl) (hA.mem_nhds hx.1)
      refine Filter.mem_of_superset hW fun z hz => ?_
      have hzAg : z ∈ A \ γ := ⟨hz.2, fun hg => hz.1 (Or.inr hg)⟩
      rw [hsplit] at hzAg
      rcases hzAg with h | h
      · exact absurd (Or.inl (subset_closure h)) hz.1
      · exact h
  have hN12 : Disjoint N₁ N₂ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rcases hz2 with h | h
    · exact Set.disjoint_left.1 hdisj hz1 h
    · exact h.2 (hVPΩ hz1)
  rintro x hx ⟨⟨p, hpK, hpsc⟩, ⟨p', hp'K, hp'sc'⟩⟩
  have hKsub : connectedComponentIn (A \ γ) x ⊆ N₁ ∪ N₂ :=
    (connectedComponentIn_subset _ _).trans (hsplit ▸ subset_rfl)
  rcases isPreconnected_connectedComponentIn.subset_or_subset hVPo hN₂o hN12 hKsub with h | h
  · have hp'VP := hVP (closure_mono h hp'K)
    rcases hp'VP with (h1 | h1) | h1
    · exact Set.disjoint_left.1 hfar (subset_closure (hVPΩ h1)) hp'sc'
    · exact Set.disjoint_left.1 hfar (subset_closure (hγ h1)) hp'sc'
    · exact Set.disjoint_left.1 hscsc h1 hp'sc'
  · have hcl : closure (connectedComponentIn (A \ γ) x) ⊆ closure VQ ∪ closure (A \ Ω) := by
      refine (closure_mono h).trans ?_
      rw [hN₂, closure_union]
    rcases hcl hpK with h1 | h1
    · rcases hVQ h1 with (h2 | h2) | h2
      · exact Set.disjoint_left.1 hscA hpsc (hΩA (hVQΩ h2))
      · exact Set.disjoint_left.1 hscA hpsc (hΩA (hγ h2))
      · exact Set.disjoint_left.1 hscA hpsc (hQA h2)
    · exact Set.disjoint_left.1 hnear h1 hpsc

/-- Helper (Stage B1; the conformal circles separate the boundary circles of the annulus). In the configuration of
Theorem 4.1, if `g` maps the annulus `{r₁ < |w| < r₂}` conformally onto `Ω₁` or `Ω₂`, then for every `s ∈ (r₁, r₂)` the
analytic Jordan curve `g({|w| = s})` is a curve of the family separating the two boundary circles of
`{R₁ < |z| < R₂}`. -/
theorem gm5_circles_mem {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) {g : ℂ → ℂ}
    (hg : IsConformalOnto g (annulus r₁ r₂) Ω) {s : ℝ} (hs : s ∈ Ioo r₁ r₂) :
    g '' sphere 0 s ∈ separatingFamily (annulus R₁ R₂) (sphere 0 R₁) (sphere 0 R₂) := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hJk : IsCompact J := hconf.2.2.1
  have hJA : J ⊆ annulus R₁ R₂ := hconf.2.2.2.2.1
  obtain ⟨hΩo, hΩc, hΩA⟩ := gm5_conf_comp hconf hΩ
  have hring := gm5_conf_ring hconf hΩ
  have hAo := gm5_isOpen_annulus R₁ R₂
  have hs0 : 0 < s := hr₁.trans hs.1
  have hbdd : Bornology.IsBounded Ω :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R₂)).subset fun z hz => mem_closedBall_zero_iff.2 (hΩA hz).2.le
  have hsubA : sphere (0 : ℂ) s ⊆ annulus r₁ r₂ := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩
  have hγΩ : g '' sphere 0 s ⊆ Ω := hg.2.2 ▸ image_mono hsubA
  have hγc : IsClosed (g '' sphere 0 s) :=
    ((isCompact_sphere (0 : ℂ) s).image_of_continuousOn (hg.1.continuousOn.mono hsubA)).isClosed
  refine ⟨gm4a_isPathCurve_mono hΩA (gm5_circle_pathCurve hr₁ hg hs), ?_, ?_⟩
  · obtain ⟨k, hkc, hk01, hksph⟩ := gm4b_circle_closed hs0
    refine ⟨{g '' sphere 0 s}, finite_singleton _, by simp, fun c hc => Or.inr ?_⟩
    rw [mem_singleton_iff.1 hc]
    refine ⟨fun t => g (k t), ?_, by simp only [hk01], by rw [hksph, image_image]⟩
    exact hg.1.continuousOn.comp hkc fun t ht => hsubA (hksph ▸ mem_image_of_mem k ht)
  -- the separation
  obtain ⟨Cin, Cout, hCin, hCout, hk1, hk2, hc1, hc2, hdisjC, hfr⟩ := gm5_ends hr₁ hr₁₂ hg hbdd hring
  obtain ⟨c, c', hcc, hsc, hfar, hfrJ, hnear'⟩ := gm5_conf_facts hconf hΩ
  have hfrC : frontier Ω = Cin ∪ Cout := by
    have h1 : frontier (toExt Ω) = toExt (closure Ω \ Ω) := gm5_frontier_toExt hΩo hbdd
    have h2 : frontier Ω = closure Ω \ Ω := by rw [frontier, hΩo.interior_eq]
    rw [h2]
    have : toExt (closure Ω \ Ω) = toExt (Cin ∪ Cout) := by rw [← h1, hfr]; exact (image_union _ _ _).symm
    exact OnePoint.coe_injective.image_injective this
  -- the ends and the circle `c`
  have hcpos : 0 < c := by rcases hcc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> linarith
  have hcA : Disjoint (sphere (0 : ℂ) c) (annulus R₁ R₂) := by
    rw [Set.disjoint_left]
    intro z hz hzA
    rw [mem_sphere_zero_iff_norm] at hz
    rcases hcc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact absurd hzA.1 (not_lt.2 hz.le)
    · exact absurd hzA.2 (not_lt.2 hz.ge)
  have hccne : Disjoint (sphere (0 : ℂ) c) (sphere (0 : ℂ) c') := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [mem_sphere_zero_iff_norm] at hz hz'
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hsphc : IsConnected (sphere (0 : ℂ) c) :=
    isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) hcpos.le
  have hcl1 : IsClosed Cin := hk1.isClosed
  have hcl2 : IsClosed Cout := hk2.isClosed
  have hsphsub : sphere (0 : ℂ) c ⊆ Cin ∪ Cout := hfrC ▸ hsc
  have hside : sphere (0 : ℂ) c ⊆ Cin ∨ sphere (0 : ℂ) c ⊆ Cout := by
    refine isPreconnected_iff_subset_of_disjoint_closed.1 hsphc.isPreconnected Cin Cout hcl1 hcl2 hsphsub ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz1, hz2⟩
    exact Set.disjoint_left.1 hdisjC hz1 hz2
  -- both ends: `P` contains the circle `c`; `P ⊆ circle c`; the other end `Q ⊆ J`
  have hPQ : ∀ P Q : Set ℂ, IsClosed P → IsConnected P → Disjoint P Q → P ∪ Q = frontier Ω →
      sphere (0 : ℂ) c ⊆ P → P ⊆ sphere (0 : ℂ) c ∧ Q ⊆ J := by
    intro P Q hPc hPconn hPQd hPQ hscP
    have hPfr : P ⊆ frontier Ω := hPQ ▸ subset_union_left
    have hQfr : Q ⊆ frontier Ω := hPQ ▸ subset_union_right
    constructor
    · have hPsub : P ⊆ sphere (0 : ℂ) c ∪ J := hPfr.trans hfrJ
      have hdJ : Disjoint (sphere (0 : ℂ) c) J := hcA.mono_right hJA
      rcases isPreconnected_iff_subset_of_disjoint_closed.1 hPconn.isPreconnected (sphere (0 : ℂ) c) J
        isClosed_sphere hJk.isClosed hPsub (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨-, hz1, hz2⟩
          exact Set.disjoint_left.1 hdJ hz1 hz2) with h | h
      · exact h
      · obtain ⟨z, hz⟩ := hsphc.nonempty
        exact absurd (h (hscP hz)) (Set.disjoint_left.1 hdJ hz)
    · intro z hz
      rcases hfrJ (hQfr hz) with h | h
      · exact absurd (hscP h) (Set.disjoint_right.1 hPQd hz)
      · exact h
  -- the two sides of the circle
  set γ : Set ℂ := g '' sphere 0 s with hγdef
  set Ain : Set ℂ := {w | r₁ < ‖w‖ ∧ ‖w‖ < s} with hAin
  set Aout : Set ℂ := {w | s < ‖w‖ ∧ ‖w‖ < r₂} with hAout
  have hAinO : IsOpen Ain := isOpen_lt continuous_const continuous_norm |>.inter
    (isOpen_lt continuous_norm continuous_const)
  have hAoutO : IsOpen Aout := isOpen_lt continuous_const continuous_norm |>.inter
    (isOpen_lt continuous_norm continuous_const)
  have hAinA : Ain ⊆ annulus r₁ r₂ := fun w hw => ⟨hw.1, hw.2.trans hs.2⟩
  have hAoutA : Aout ⊆ annulus r₁ r₂ := fun w hw => ⟨hs.1.trans hw.1, hw.2⟩
  have hdisjIO : Disjoint (g '' Ain) (g '' Aout) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have := hg.2.1 (hAoutA hb) (hAinA ha) hab
    rw [this] at hb
    linarith [ha.2, hb.1]
  have hcovIO : g '' Ain ∪ g '' Aout = Ω \ γ := by
    ext z
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · refine ⟨hg.2.2 ▸ mem_image_of_mem g (hAinA hw), ?_⟩
        rintro ⟨w', hw', hww⟩
        have := hg.2.1 (hsubA hw') (hAinA hw) hww
        rw [this, mem_sphere_zero_iff_norm] at hw'
        exact absurd hw.2 (not_lt.2 hw'.ge)
      · refine ⟨hg.2.2 ▸ mem_image_of_mem g (hAoutA hw), ?_⟩
        rintro ⟨w', hw', hww⟩
        have := hg.2.1 (hsubA hw') (hAoutA hw) hww
        rw [this, mem_sphere_zero_iff_norm] at hw'
        exact absurd hw.1 (not_lt.2 hw'.le)
    · rintro ⟨hzΩ, hzγ⟩
      rw [← hg.2.2] at hzΩ
      obtain ⟨w, hwA, rfl⟩ := hzΩ
      have hne : ‖w‖ ≠ s := fun h => hzγ ⟨w, mem_sphere_zero_iff_norm.2 h, rfl⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨w, ⟨hwA.1, h⟩, rfl⟩
      · exact Or.inr ⟨w, ⟨h, hwA.2⟩, rfl⟩
  have hnear : Disjoint (closure (annulus R₁ R₂ \ Ω)) (sphere (0 : ℂ) c) := by
    rw [Set.disjoint_left]
    intro p hp hpc
    obtain ⟨ε, hε, hsub⟩ := hnear' p hpc
    obtain ⟨w, hwb, hwA⟩ := mem_closure_iff.1 hp (ball p ε) isOpen_ball (mem_ball_self hε)
    exact hwA.2 (hsub ⟨hwb, hwA.1⟩)
  have hcore : ∀ VP VQ Q : Set ℂ, IsOpen VP → IsOpen VQ → Disjoint VP VQ → VP ∪ VQ = Ω \ γ → Q ⊆ J →
      closure VP ⊆ VP ∪ γ ∪ sphere (0 : ℂ) c → closure VQ ⊆ VQ ∪ γ ∪ Q →
      IsSeparatingIn (annulus R₁ R₂) γ (sphere (0 : ℂ) c) (sphere (0 : ℂ) c') :=
      fun VP VQ Q hVPo hVQo hd hcov hQJ hVP hVQ =>
    gm5_sep_core hAo hΩA hγΩ hγc hVPo hVQo hd hcov hcA (hQJ.trans hJA) hccne hVP hVQ hnear hfar
  have hsep : IsSeparatingIn (annulus R₁ R₂) γ (sphere (0 : ℂ) c) (sphere (0 : ℂ) c') := by
    have hγsplit : g '' {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ s} ⊆ g '' Ain ∪ γ := by
      rintro _ ⟨w, hw, rfl⟩
      rcases hw.2.lt_or_eq with h | h
      · exact Or.inl ⟨w, ⟨hw.1, h⟩, rfl⟩
      · exact Or.inr ⟨w, mem_sphere_zero_iff_norm.2 h, rfl⟩
    have hγsplit' : g '' {w | s ≤ ‖w‖ ∧ ‖w‖ < r₂} ⊆ g '' Aout ∪ γ := by
      rintro _ ⟨w, hw, rfl⟩
      rcases hw.1.lt_or_eq with h | h
      · exact Or.inl ⟨w, ⟨h, hw.2⟩, rfl⟩
      · exact Or.inr ⟨w, mem_sphere_zero_iff_norm.2 h.symm, rfl⟩
    rcases hside with hP | hP
    · obtain ⟨hPs, hQJ⟩ := hPQ Cin Cout hcl1 hc1 hdisjC hfrC.symm hP
      refine hcore (g '' Ain) (g '' Aout) Cout (gm5_image_open hg hAinO hAinA) (gm5_image_open hg hAoutO hAoutA)
        hdisjIO hcovIO hQJ ?_ ?_
      · intro p hp
        rcases gm5_closure_in2 hg hCin hs.2 hp with h | h
        · rcases hγsplit h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
        · exact Or.inr (hPs h)
      · intro p hp
        rcases gm5_closure_out2 hg hCout hs.1 hp with h | h
        · rcases hγsplit' h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
        · exact Or.inr h
    · obtain ⟨hPs, hQJ⟩ := hPQ Cout Cin hcl2 hc2 hdisjC.symm (by rw [union_comm]; exact hfrC.symm) hP
      refine hcore (g '' Aout) (g '' Ain) Cin (gm5_image_open hg hAoutO hAoutA) (gm5_image_open hg hAinO hAinA)
        hdisjIO.symm (by rw [union_comm]; exact hcovIO) hQJ ?_ ?_
      · intro p hp
        rcases gm5_closure_out2 hg hCout hs.1 hp with h | h
        · rcases hγsplit' h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
        · exact Or.inr (hPs h)
      · intro p hp
        rcases gm5_closure_in2 hg hCin hs.2 hp with h | h
        · rcases hγsplit h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
        · exact Or.inr h
  rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsep
  · exact gm5_isSeparatingIn_symm hsep

/-- Helper (Stage B1): the module of a configuration domain, its conformal circles, and their extremal length. -/
theorem gm5_conf_model {R₁ R₂ : ℝ} {J Ω₁ Ω₂ Ω : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂)
    (hΩ : Ω = Ω₁ ∨ Ω = Ω₂) :
    ∃ (r₁ r₂ : ℝ) (g : ℂ → ℂ), 0 < r₁ ∧ r₁ < r₂ ∧ IsConformalOnto g (annulus r₁ r₂) Ω ∧
      ringModGM (toExt Ω) = ENNReal.ofReal (1 / (2 * π) * Real.log (r₂ / r₁)) := by
  obtain ⟨-, -, hΩA⟩ := gm5_conf_comp hconf hΩ
  have hring := gm5_conf_ring hconf hΩ
  have hR2 : 0 ≤ R₂ := (hconf.1.trans hconf.2.1).le
  obtain ⟨r₁, r₂, h1, h12, ψ, hψ, hψB⟩ := gm5_ring_model hconf hΩ
  have hbdd : extInf ∉ closure (toExt Ω) := gm5_infty_notMem_closure (R := R₂) fun z hz =>
    mem_closedBall_zero_iff.2 (hΩA hz).2.le
  obtain ⟨g, hBU, hUb, hUo, hψc, hgc, hgψ, hψg⟩ := gm5_ring_plane hring h1 h12 hψ hψB hbdd
  rw [gm5_finitePart_toExt] at hgc
  exact ⟨r₁, r₂, g, h1, h12, hgc, (gm5_ringMod_bounded hring h1 h12 hψ hψB hbdd).1⟩

/-- Helper (Stage B1): `mod Ω₁ + mod Ω₂ ≤ mod A` (the parallel rule applied to the conformal circles). -/
theorem gm5_mod_add_le {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    ringModGM (toExt Ω₁) + ringModGM (toExt Ω₂) ≤ ENNReal.ofReal (1 / (2 * π) * Real.log (R₂ / R₁)) := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hdisj : Disjoint Ω₁ Ω₂ := hconf.2.2.2.2.2.2.2.1
  obtain ⟨hΩ₁o, hΩ₁c, hΩ₁A⟩ := gm5_conf_comp hconf (Or.inl rfl)
  obtain ⟨hΩ₂o, hΩ₂c, hΩ₂A⟩ := gm5_conf_comp hconf (Or.inr rfl)
  obtain ⟨hAo, hAc⟩ := gm5_annulus_oc hR1.le hR12
  -- the circle families
  have hcirc : ∀ Ω : Set ℂ, (Ω = Ω₁ ∨ Ω = Ω₂) → ∃ C : Set (Set ℂ), IsPathFamily Ω C ∧
      C ⊆ separatingFamily (annulus R₁ R₂) (sphere 0 R₁) (sphere 0 R₂) ∧
      ringModGM (toExt Ω) ≤ (extremalLengthGM Ω C)⁻¹ := by
    intro Ω hΩ
    obtain ⟨r₁, r₂, g, h1, h12, hg, hmod⟩ := gm5_conf_model hconf hΩ
    set C : Set (Set ℂ) := {γ | ∃ s ∈ Ioo r₁ r₂, γ = g '' sphere 0 s} with hC
    have hmid : (r₁ + r₂) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
    refine ⟨C, ⟨⟨_, (r₁ + r₂) / 2, hmid, rfl⟩, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact gm5_circle_pathCurve h1 hg hs
    · rintro _ ⟨s, hs, rfl⟩
      exact gm5_circles_mem hconf hΩ h1 h12 hg hs
    · have hle := gm5_extLen_le h1 h12 hg (Γ := C) fun s hs => ⟨s, hs, rfl⟩
      have hlog : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div h1).2 h12)
      rw [hmod]
      calc ENNReal.ofReal (1 / (2 * π) * Real.log (r₂ / r₁))
          = (ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)))⁻¹ := by
            rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
            congr 1
            field_simp
        _ ≤ _ := ENNReal.inv_le_inv.2 hle
  obtain ⟨C₁, hC₁, hCs₁, hm₁⟩ := hcirc Ω₁ (Or.inl rfl)
  obtain ⟨C₂, hC₂, hCs₂, hm₂⟩ := hcirc Ω₂ (Or.inr rfl)
  have hΓ : IsPathFamily (annulus R₁ R₂) (separatingFamily (annulus R₁ R₂) (sphere 0 R₁) (sphere 0 R₂)) := by
    obtain ⟨γ₀, hγ₀⟩ := hC₁.1
    exact ⟨⟨γ₀, hCs₁ hγ₀⟩, fun γ hγ => hγ.1⟩
  have hpar := parallel_rule hΩ₁o hΩ₂o hdisj ⟨hAo, hAc⟩ (union_subset hΩ₁A hΩ₂A) hC₁ hC₂ hΓ (by
    rintro γ (hγ | hγ)
    · exact ⟨γ, hCs₁ hγ, subset_rfl⟩
    · exact ⟨γ, hCs₂ hγ, subset_rfl⟩)
  exact (add_le_add hm₁ hm₂).trans (hpar.trans (gm5_annulus_sep_inv hR1 hR12).le)

/-- **Formula (4.1)** (Ch. V §4; cited at P1:7182 and P1:7228 "then by (4.1)"). Let `Ω = {R₁ < |z| < R₂}` and let
`J ⊆ Ω` be a continuum that separates `Ω` into disjoint ring domains `Ω₁`, `Ω₂` with `{|z| = R₁} ⊆ ∂Ω₁` and
`{|z| = R₂} ⊆ ∂Ω₂`. By the serial rule (4.1) `mod(Ω₁) + mod(Ω₂) ≤ mod(Ω) = (1/2π) log(R₂/R₁)`, and equality holds in
(4.1) if `J` is a circle `{|z| = r}`.
Modelling: the configuration is `IsModulsatzConfig` (module docstring); `mod` is `ringModGM` of the image in `ℂ*`,
and the sum is taken in `[0, ∞]`; the equality case is stated for every circle `J = {|z| = r}` of the configuration
(then `R₁ < r < R₂`). The formula was checked against the equation image. -/
theorem eq5_4_1 {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    ringModGM (toExt Ω₁) + ringModGM (toExt Ω₂) ≤ ringModGM (toExt (annulus R₁ R₂)) ∧
      ringModGM (toExt (annulus R₁ R₂)) = ENNReal.ofReal (1 / (2 * π) * Real.log (R₂ / R₁)) ∧
      ((∃ r : ℝ, J = sphere 0 r) →
        ringModGM (toExt Ω₁) + ringModGM (toExt Ω₂) = ringModGM (toExt (annulus R₁ R₂))) := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have h2 := gm5_annulus_mod hR1 hR12
  refine ⟨?_, h2, ?_⟩
  · rw [h2]
    exact gm5_mod_add_le hconf
  · rintro ⟨r, rfl⟩
    obtain ⟨hr1, hr2, rfl, rfl⟩ := gm5_circle_comps hconf
    have hr0 : 0 < r := hR1.trans hr1
    rw [gm5_annulus_mod hR1 hr1, gm5_annulus_mod hr0 hr2, h2,
      ← ENNReal.ofReal_add (by have := Real.log_pos ((one_lt_div hR1).2 hr1); positivity)
        (by have := Real.log_pos ((one_lt_div hr0).2 hr2); positivity)]
    congr 1
    rw [← mul_add, ← Real.log_mul (div_pos hr0 hR1).ne' (div_pos (hr0.trans hr2) hr0).ne']
    congr 2
    field_simp

/-- **Formula (4.4)** (Ch. V §4; cited at P1:7248, "By inequality (4.4), Theorem 4.1 is a corollary of
Theorem 4.2"). Let `G` be a simply connected domain such that `0 ∈ G`. For small `ρ` define
`M_ρ = M_ρ(G) = mod(G \ B̄(0, ρ))`. As in (3.1), (4.4) `M_ρ + (log ρ)/2π ≤ M_{ρ'} + (log ρ')/2π` if `ρ' < ρ`.
Modelling: `G ⊆ ℂ` with `Gehring1978.IsHypSimplyConnectedExt (toExt G)`; "small `ρ`" is `B̄(0, ρ) ⊆ G` (then
`G \ B̄(0, ρ)` is a ring domain and `0 ∈ G`), and `0 < ρ' < ρ`; `M_ρ` is written out (`ringModGM`); the inequality is
taken in `EReal`, where the moduli (in `[0, ∞]`) and the real logarithms add without junk. The formula was checked
against the equation image. -/
theorem eq5_4_4 {G : Set ℂ} (hG : IsHypSimplyConnectedExt (toExt G)) {ρ ρ' : ℝ} (hρ' : 0 < ρ') (hρρ' : ρ' < ρ)
    (hρG : closedBall (0 : ℂ) ρ ⊆ G) :
    ((ringModGM (toExt (G \ closedBall 0 ρ)) : ℝ≥0∞) : EReal) + ((Real.log ρ / (2 * π) : ℝ) : EReal) ≤
      ((ringModGM (toExt (G \ closedBall 0 ρ')) : ℝ≥0∞) : EReal) + ((Real.log ρ' / (2 * π) : ℝ) : EReal) := by
  sorry

/-- **Unlabelled** (Ch. V §4, P1:7210–7220; the link between `M_ρ(G)` and the reduced modulus, used at P1:7222 to
define `M(G)` and at P1:7248 to derive Theorem 4.1 from Theorem 4.2). Let `φ : 𝔻 → G` be a conformal mapping with
`φ(0) = 0`. Then for small `ρ`, `M_ρ(G) = mod(𝔻 \ φ⁻¹(B̄(0, ρ)))`, so that by the proof of Lemma 3.1
`lim_{ρ→0} M_ρ + (log ρ)/2π = (1/2π) log |φ'(0)|`.
Modelling: `φ` maps `𝔻` conformally onto `G ⊆ ℂ` (`LiZhongQC.IsConformalOnto`; then `G` is a simply connected
domain with `0 ∈ G`); `φ⁻¹(B̄(0, ρ))` is the preimage in `𝔻`; "for small `ρ`" is "for all `ρ > 0` near `0`"; the
moduli are finite there (a conjunct), so the real limit through `ENNReal.toReal` sees no junk; `φ'(0) ≠ 0`. -/
theorem tendsto_modulus_add_log {G : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc G) (hφ0 : φ 0 = 0) :
    (∀ᶠ ρ in 𝓝[>] (0 : ℝ), ringModGM (toExt (G \ closedBall 0 ρ)) =
        ringModGM (toExt (unitDisc \ φ ⁻¹' closedBall 0 ρ)) ∧ ringModGM (toExt (G \ closedBall 0 ρ)) < ⊤) ∧
      Tendsto (fun ρ : ℝ => (ringModGM (toExt (G \ closedBall 0 ρ))).toReal + Real.log ρ / (2 * π)) (𝓝[>] 0)
        (𝓝 (1 / (2 * π) * Real.log ‖deriv φ 0‖)) := by
  sorry

/-- **Definition** (reduced modulus, Ch. V §4, P1:7222; cited at P1:7228–7239 and in the index "reduced modulus,
168"). For a simply connected domain `G` with `0 ∈ G` and a conformal map `φ : 𝔻 → G` with `φ(0) = 0`, the reduced
modulus of `G` is `M(G) = (1/2π) log |φ'(0)|`.
Modelling: `G ⊆ ℂ`; the value over all such maps `φ` (two of them differ by a rotation of `𝔻`, so `|φ'(0)|` does not
depend on `φ` and the set is a single point). Junk: `0` when there is no such map (`G = ℂ`, `0 ∉ G`, or `G` not
simply connected); every statement using it has a simply connected `G ∋ 0` with at least two points of `ℂ*` outside
(so the map exists). -/
def reducedModulus (G : Set ℂ) : ℝ :=
  sSup {m : ℝ | ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc G ∧ φ 0 = 0 ∧ m = 1 / (2 * π) * Real.log ‖deriv φ 0‖}

/-- **Definition** (reduced modulus of a domain containing `∞`, Ch. V §4, P1:7222–7226). If `G ⊆ ℂ*` is simply
connected and `∞ ∈ G`, the reduced modulus of `G` is defined by `M(G) = (1/2π) log |(1/ψ)'(0)|`, where
`ψ : 𝔻 → G` is a conformal map with `ψ(0) = ∞`.
Modelling: `1/ψ` maps `𝔻` conformally onto the chart image `1/G = {w : 1/w ∈ G}` (with `1/0 = ∞`: the inverse chart
`LehtoVirtanen1973.extChartInv ∞`) and sends `0` to `0`, so `M(G)` is the reduced modulus of `1/G`. The chart image is
a plane domain containing `0` when `0 ∉ G`, the case of the book (Theorem 4.2); otherwise no such map exists and the
value is the junk `0` of `reducedModulus`. The formula was checked against the equation image. -/
def reducedModulusInf (G : Set ExtPlane) : ℝ :=
  reducedModulus {w : ℂ | extChartInv extInf w ∈ G}

/-- Helper: membership in the finite part. -/
theorem gm5_mem_finitePart (G : Set ExtPlane) (z : ℂ) : z ∈ finitePart G ↔ (z : ExtPlane) ∈ G := Iff.rfl

/-- Helper (topology): a component `G` of the complement of a closed connected non-empty set `K` of `ℂ̄` is open and
has connected complement. -/
theorem gm5_compl_comp {K : Set ExtPlane} (hK : IsClosed K) (hKc : IsConnected K) {x : ExtPlane} :
    IsOpen (connectedComponentIn Kᶜ x) ∧ IsConnected (connectedComponentIn Kᶜ x)ᶜ := by
  have hKo : IsOpen Kᶜ := hK.isOpen_compl
  have hGo : ∀ y : ExtPlane, IsOpen (connectedComponentIn Kᶜ y) := fun y => hKo.connectedComponentIn
  -- closures of components stay in the component or in `K`
  have hcl : ∀ y : ExtPlane, y ∉ K → closure (connectedComponentIn Kᶜ y) ⊆
      connectedComponentIn Kᶜ y ∪ K := by
    intro y hy w hw
    by_cases hwK : w ∈ K
    · exact Or.inr hwK
    · left
      have hwKc : w ∈ Kᶜ := hwK
      have hw' : w ∈ connectedComponentIn Kᶜ w := mem_connectedComponentIn hwKc
      obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.1 hw _ (hGo w) hw'
      have : connectedComponentIn Kᶜ w = connectedComponentIn Kᶜ y := by
        rw [connectedComponentIn_eq hu2, ← connectedComponentIn_eq hu1]
      rw [← this]
      exact hw'
  have hcl' : ∀ y : ExtPlane, y ∉ K → (closure (connectedComponentIn Kᶜ y) ∩ K).Nonempty := by
    intro y hy
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hsub : closure (connectedComponentIn Kᶜ y) ⊆ connectedComponentIn Kᶜ y := by
      intro w hw
      rcases hcl y hy hw with h | h
      · exact h
      · have : w ∈ closure (connectedComponentIn Kᶜ y) ∩ K := ⟨hw, h⟩
        rw [hne] at this
        exact this.elim
    have hclopen : IsClopen (connectedComponentIn Kᶜ y) :=
      ⟨closure_subset_iff_isClosed.1 hsub, hGo y⟩
    have hy' : y ∈ connectedComponentIn Kᶜ y := mem_connectedComponentIn (show y ∈ Kᶜ from hy)
    have huniv := hclopen.eq_univ ⟨y, hy'⟩
    obtain ⟨k, hk⟩ := hKc.nonempty
    have : k ∈ connectedComponentIn Kᶜ y := huniv ▸ mem_univ k
    exact connectedComponentIn_subset _ _ this hk
  refine ⟨hGo x, ?_⟩
  set G := connectedComponentIn Kᶜ x with hG
  have hGc : Gᶜ = ⋃ y : ↥Gᶜ, (K ∪ connectedComponentIn Kᶜ (y : ExtPlane)) := by
    ext w
    simp only [mem_iUnion, mem_union, Subtype.exists]
    constructor
    · intro hw
      by_cases hwK : w ∈ K
      · exact ⟨w, hw, Or.inl hwK⟩
      · exact ⟨w, hw, Or.inr (mem_connectedComponentIn (show w ∈ Kᶜ from hwK))⟩
    · rintro ⟨y, hy, hwy⟩
      rcases hwy with h | h
      · intro hwG
        exact (connectedComponentIn_subset Kᶜ x hwG) h
      · intro hwG
        have hyK : y ∈ Kᶜ := by
          by_contra hyK
          rw [connectedComponentIn_eq_empty hyK] at h
          exact h
        have e1 := connectedComponentIn_eq h
        have e2 := connectedComponentIn_eq hwG
        have : y ∈ G := by
          rw [hG, e2, ← e1]
          exact mem_connectedComponentIn hyK
        exact hy this
  rw [hGc]
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := hKc.nonempty
    have hkG : k ∈ Gᶜ := fun hkG => (connectedComponentIn_subset Kᶜ x hkG) hk
    exact ⟨k, mem_iUnion.2 ⟨⟨k, hkG⟩, Or.inl hk⟩⟩
  · refine isPreconnected_iUnion (ι := ↥Gᶜ) ?_ ?_
    · obtain ⟨k, hk⟩ := hKc.nonempty
      exact ⟨k, mem_iInter.2 fun i => Or.inl hk⟩
    · rintro ⟨y, hy⟩
      by_cases hyK : y ∈ K
      · have : connectedComponentIn Kᶜ y = ∅ := connectedComponentIn_eq_empty (fun h => h hyK)
        simp only [this, union_empty]
        exact hKc.isPreconnected
      · obtain ⟨p, hp1, hp2⟩ := hcl' y hyK
        have heq : K ∪ connectedComponentIn Kᶜ y = K ∪ closure (connectedComponentIn Kᶜ y) := by
          refine subset_antisymm (union_subset_union_right _ subset_closure) ?_
          intro w hw
          rcases hw with h | h
          · exact Or.inl h
          · rcases hcl y hyK h with h' | h'
            · exact Or.inr h'
            · exact Or.inl h'
        simp only
        rw [heq]
        exact IsPreconnected.union p hp2 hp1 hKc.isPreconnected
          (isPreconnected_connectedComponentIn.closure)

/-- Helper: Riemann mapping for a domain with connected complement in `ℂ̄`. -/
theorem gm5_riemann {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hc : IsConnected (toExt U)ᶜ)
    (hne : Uᶜ.Nonempty) {z₀ : ℂ} (hz₀ : z₀ ∈ U) : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc U ∧ φ 0 = z₀ := by
  obtain ⟨f, hcomp, hbij⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hUo hUc hne
    (LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl hUo hUc hc) hz₀
  refine ⟨Function.invFunOn f U, ?_, ?_⟩
  · have hinv : Set.BijOn (Function.invFunOn f U) RMT.disc U := hbij.symm hbij.invOn_invFunOn.symm
    obtain ⟨_, hd⟩ := RMT.differentiableOn_invFunOn_of_injOn hUo hcomp.diff hcomp.injOn
    refine ⟨?_, hinv.injOn, hinv.image_eq⟩
    have : f '' U = RMT.disc := hbij.image_eq
    rw [this] at hd
    exact hd
  · have : Function.invFunOn f U (f z₀) = z₀ := hbij.invOn_invFunOn.1 hz₀
    rw [hcomp.center] at this
    exact this

/-- Helper: a component of the complement of a continuum `J ⊆ ℂ`, not containing `∞`, is a plane domain with a
Riemann map. -/
theorem gm5_comp_domain {J : Set ℂ} (hJc : IsCompact J) (hJ : IsConnected J) {z₀ : ℂ}
    (hz : (z₀ : ExtPlane) ∉ toExt J) (hinf : extInf ∉ connectedComponentIn (toExt J)ᶜ (z₀ : ExtPlane)) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc (finitePart (connectedComponentIn (toExt J)ᶜ (z₀ : ExtPlane))) ∧
      φ 0 = z₀ := by
  have hK : IsClosed (toExt J) := (hJc.image OnePoint.continuous_coe).isClosed
  have hKc : IsConnected (toExt J) := hJ.image _ OnePoint.continuous_coe.continuousOn
  obtain ⟨hGo, hGc⟩ := gm5_compl_comp hK hKc
  set G := connectedComponentIn (toExt J)ᶜ (z₀ : ExtPlane) with hG
  set U : Set ℂ := finitePart G with hU
  have hGU : toExt U = G := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [toExt, mem_image, hU, gm5_mem_finitePart]
      constructor
      · rintro ⟨z, _, hzz⟩
        exact absurd hzz (OnePoint.coe_ne_infty z)
      · intro h; exact absurd h hinf
    | coe z =>
      simp only [toExt, mem_image, hU, gm5_mem_finitePart]
      constructor
      · rintro ⟨w, hw, hwz⟩
        rw [← OnePoint.coe_injective hwz]; exact hw
      · intro h; exact ⟨z, h, rfl⟩
  have hUo : IsOpen U := hGo.preimage OnePoint.continuous_coe
  have hz0 : z₀ ∈ U := mem_connectedComponentIn hz
  have hUc : IsConnected U := by
    refine ⟨⟨z₀, hz0⟩, ?_⟩
    have : IsPreconnected (((↑) : ℂ → ExtPlane) '' U) := by
      have : ((↑) : ℂ → ExtPlane) '' U = G := hGU
      rw [this]; exact isPreconnected_connectedComponentIn
    exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 this
  have hne : Uᶜ.Nonempty := by
    obtain ⟨j, hj⟩ := hJ.nonempty
    refine ⟨j, fun hjU => ?_⟩
    exact (connectedComponentIn_subset _ _ hjU) ⟨j, hj, rfl⟩
  have hc : IsConnected (toExt U)ᶜ := by rw [hGU]; exact hGc
  exact gm5_riemann hUo hUc hc hne hz0

/-- Helper: `G₁ = component of 0`, `G₂ = component of ∞`, both in the complement of `toExt J`. -/
theorem gm5_comp_eq {J : Set ℂ} {G₁ G₂ : Set ExtPlane}
    (h1 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₁)
    (h2 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₂)
    (h0 : ((0 : ℂ) : ExtPlane) ∈ G₁) (hinf : extInf ∈ G₂) :
    G₁ = connectedComponentIn (toExt J)ᶜ ((0 : ℂ) : ExtPlane) ∧
      G₂ = connectedComponentIn (toExt J)ᶜ extInf := by
  obtain ⟨z₁, _, rfl⟩ := h1
  obtain ⟨z₂, _, rfl⟩ := h2
  exact ⟨connectedComponentIn_eq h0, connectedComponentIn_eq hinf⟩

/-- Helper (I-5a, T1c). The component of `0` and the component of `∞` of `ℂ* \ J` are different, so every ray from `0`
(with the point `∞`) is a connected set joining them and meets `J`: for every direction `v` with `|v| = 1` there are
`t > 0` and `z ∈ J` with `z = t v`. -/
theorem gm5_ray {J : Set ℂ} {G₁ G₂ : Set ExtPlane} (hJc : IsCompact J)
    (h1 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₁)
    (h2 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₂) (hd : Disjoint G₁ G₂)
    (h0 : ((0 : ℂ) : ExtPlane) ∈ G₁) (hinf : extInf ∈ G₂) {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ t : ℝ, 0 < t ∧ ((t : ℂ) * v) ∈ J := by
  obtain ⟨e1, e2⟩ := gm5_comp_eq h1 h2 h0 hinf
  by_contra hno
  push Not at hno
  set X : Set ExtPlane := (toExt J)ᶜ with hX
  have h0X : ((0 : ℂ) : ExtPlane) ∈ X := by
    obtain ⟨z, hz, rfl⟩ := h1
    exact connectedComponentIn_subset _ _ h0
  set R : Set ℂ := (fun t : ℝ => (t : ℂ) * v) '' Ici 0 with hR
  have hRJ : ∀ z ∈ R, z ∉ J := by
    rintro _ ⟨t, ht, rfl⟩ hJt
    rcases (show 0 ≤ t from ht).lt_or_eq with hlt | heq
    · exact hno t hlt hJt
    · subst heq
      apply h0X
      have : (0 : ℂ) ∈ J := by simpa using hJt
      exact ⟨0, this, rfl⟩
  have hRc : IsPreconnected R :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * v).continuousOn
  set S : Set ExtPlane := ((↑) : ℂ → ExtPlane) '' R with hS
  have hSc : IsPreconnected S := hRc.image _ OnePoint.continuous_coe.continuousOn
  have hinfS : extInf ∈ closure S := by
    have ht : Tendsto (fun t : ℝ => (((t : ℂ) * v : ℂ) : ExtPlane)) atTop (𝓝 extInf) := by
      refine OnePoint.tendsto_coe_infty.comp ?_
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      refine Tendsto.congr' ?_ tendsto_id
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp [hv, abs_of_nonneg ht]
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact ⟨(t : ℂ) * v, ⟨t, ht, rfl⟩, rfl⟩
  have hSX : S ⊆ X := by
    rintro _ ⟨z, hz, rfl⟩ hzK
    obtain ⟨j, hj, hjz⟩ := hzK
    rw [OnePoint.coe_injective hjz] at hj
    exact hRJ z hz hj
  have hinfX : extInf ∈ X := by
    obtain ⟨z, _, rfl⟩ := h2
    exact connectedComponentIn_subset _ _ hinf
  have hT : IsPreconnected (S ∪ {extInf}) :=
    hSc.subset_closure subset_union_left (union_subset subset_closure (singleton_subset_iff.2 hinfS))
  have hTX : S ∪ {extInf} ⊆ X := union_subset hSX (singleton_subset_iff.2 hinfX)
  have h0S : ((0 : ℂ) : ExtPlane) ∈ S ∪ {extInf} :=
    Or.inl ⟨(0 : ℂ), ⟨(0 : ℝ), mem_Ici.2 le_rfl, by simp⟩, rfl⟩
  have := hT.subset_connectedComponentIn h0S hTX (Or.inr rfl)
  rw [← e1] at this
  exact Set.disjoint_left.1 hd this hinf

/-- Helper (I-5a, T1). Topology and the Riemann mapping theorem for Theorem 4.2: the components `G₁ ∋ 0`, `G₂ ∋ ∞` of
the complement of the continuum `J` have connected complements in `ℂ*`, so there are conformal maps `φ₁ : 𝔻 → G₁ ∩ ℂ`
and `φ₂ : 𝔻 → {w | extChartInv ∞ w ∈ G₂}` (the chart image of `G₂`, a plane domain containing `0`) fixing `0`. -/
theorem gm5_exists_maps {J : Set ℂ} {G₁ G₂ : Set ExtPlane} (hJc : IsCompact J) (hJ : IsConnected J)
    (h1 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₁)
    (h2 : ∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₂) (hd : Disjoint G₁ G₂)
    (h0 : ((0 : ℂ) : ExtPlane) ∈ G₁) (hinf : extInf ∈ G₂) :
    ∃ φ₁ φ₂ : ℂ → ℂ, IsConformalOnto φ₁ unitDisc (finitePart G₁) ∧ φ₁ 0 = 0 ∧
      IsConformalOnto φ₂ unitDisc {w : ℂ | extChartInv extInf w ∈ G₂} ∧ φ₂ 0 = 0 := by
  obtain ⟨e1, e2⟩ := gm5_comp_eq h1 h2 h0 hinf
  set X : Set ExtPlane := (toExt J)ᶜ with hX
  have hG1X : G₁ ⊆ X := by obtain ⟨z, _, rfl⟩ := h1; exact connectedComponentIn_subset _ _
  have hG2X : G₂ ⊆ X := by obtain ⟨z, _, rfl⟩ := h2; exact connectedComponentIn_subset _ _
  have h0X : ((0 : ℂ) : ExtPlane) ∈ X := hG1X h0
  have hinfG1 : extInf ∉ G₁ := fun h => Set.disjoint_left.1 hd h hinf
  have h0G2 : ((0 : ℂ) : ExtPlane) ∉ G₂ := fun h => Set.disjoint_left.1 hd h0 h
  have h0J : (0 : ℂ) ∉ J := fun h => h0X ⟨0, h, rfl⟩
  -- first map
  have hA : ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc (finitePart G₁) ∧ φ 0 = 0 := by
    have := gm5_comp_domain hJc hJ (z₀ := 0) h0X (by rw [← e1]; exact hinfG1)
    rw [← e1] at this
    exact this
  obtain ⟨φ₁, hφ₁, hφ₁0⟩ := hA
  -- the inversion
  have hdet : (0 : ℂ) * 0 - 1 * 1 ≠ 0 := by norm_num
  set σ : ExtPlane ≃ₜ ExtPlane := LiZhongQC.mobiusHomeomorph 0 1 1 0 hdet with hσ
  have hσc : ∀ z : ℂ, z ≠ 0 → σ (z : ExtPlane) = ((z⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    rw [hσ, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_coe (by simpa using hz)]
    simp [LiZhongQC.mobiusFn]
  have hσ0 : σ ((0 : ℂ) : ExtPlane) = extInf := by
    rw [hσ, LiZhongQC.mobiusHomeomorph_apply]
    exact LiZhongQC.mobiusExt_coe_of_eq_zero (by simp)
  have hσinf : σ extInf = ((0 : ℂ) : ExtPlane) := by
    rw [hσ, LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_infty_of_ne one_ne_zero]
    simp
  have hσσ : ∀ x : ExtPlane, σ (σ x) = x := by
    intro x
    induction x using OnePoint.rec with
    | infty => rw [hσinf, hσ0]
    | coe z =>
      by_cases hz : z = 0
      · subst hz; rw [hσ0, hσinf]
      · rw [hσc z hz, hσc _ (inv_ne_zero hz), inv_inv]
  have hchart : ∀ w : ℂ, extChartInv extInf w = σ (w : ExtPlane) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [hσ0]
      show (if (0 : ℂ) = 0 then extInf else (((0 : ℂ)⁻¹ : ℂ) : ExtPlane)) = extInf
      simp
    · rw [hσc w hw]
      show (if w = 0 then extInf else ((w⁻¹ : ℂ) : ExtPlane)) = _
      simp only [hw, ↓reduceIte]
  -- the image continuum
  set J₂ : Set ℂ := (fun z => z⁻¹) '' J with hJ₂
  have hinvc : ContinuousOn (fun z : ℂ => z⁻¹) J := continuousOn_inv₀.mono (fun z hz => by
    exact fun h => h0J (by rwa [mem_singleton_iff.1 h] at hz))
  have hJ₂c : IsCompact J₂ := hJc.image_of_continuousOn hinvc
  have hJ₂conn : IsConnected J₂ := hJ.image _ hinvc
  have hσJ : σ '' toExt J = toExt J₂ := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z⁻¹, ⟨z, hz, rfl⟩, (hσc z (fun h => h0J (h ▸ hz))).symm⟩
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, hσc z (fun h => h0J (h ▸ hz))⟩
  have hσX : σ '' X = (toExt J₂)ᶜ := by
    rw [hX, σ.image_compl, hσJ]
  have hinfX : extInf ∈ X := hG2X hinf
  have hcomp : σ '' G₂ = connectedComponentIn (toExt J₂)ᶜ ((0 : ℂ) : ExtPlane) := by
    rw [e2, σ.image_connectedComponentIn hinfX, hσX, hσinf]
  have h0J₂ : ((0 : ℂ) : ExtPlane) ∉ toExt J₂ := by
    rw [← hσJ]
    rintro ⟨y, ⟨z, hz, rfl⟩, hy0⟩
    have := congrArg σ hy0
    rw [hσσ, hσ0] at this
    exact OnePoint.coe_ne_infty z this
  have hinf₂ : extInf ∉ connectedComponentIn (toExt J₂)ᶜ ((0 : ℂ) : ExtPlane) := by
    rw [← hcomp]
    rintro ⟨x, hx, hxinf⟩
    have : x = ((0 : ℂ) : ExtPlane) := by
      have := congrArg σ hxinf
      rwa [hσσ, hσinf] at this
    exact h0G2 (this ▸ hx)
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := gm5_comp_domain hJ₂c hJ₂conn (z₀ := 0) h0J₂ hinf₂
  rw [← hcomp] at hφ₂
  have hset : {w : ℂ | extChartInv extInf w ∈ G₂} = finitePart (σ '' G₂) := by
    ext w
    simp only [Set.mem_ofPred_eq, gm5_mem_finitePart, hchart]
    constructor
    · intro h; exact ⟨_, h, hσσ _⟩
    · rintro ⟨x, hx, hxw⟩
      have : σ (w : ExtPlane) = x := by rw [← hxw, hσσ]
      rw [this]; exact hx
  exact ⟨φ₁, φ₂, hφ₁, hφ₁0, by rw [hset]; exact hφ₂, hφ₂0⟩

/-- Helper (I-5a, T2). The reduced modulus is bounded by the value `(1/2π) log |φ'(0)|` of *every* conformal map
`φ : 𝔻 → G` with `φ(0) = 0` (Schwarz's lemma for `φ⁻¹ ∘ φ'`; the supremum in `reducedModulus` is over such maps). -/
theorem gm5_reducedModulus_le {G : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc G) (h0 : φ 0 = 0) :
    reducedModulus G ≤ 1 / (2 * π) * Real.log ‖deriv φ 0‖ := by
  obtain ⟨hdiff, hinj, himg⟩ := hφ
  have hU : IsOpen (unitDisc) := isOpen_ball
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨hopen, hinvd⟩ := RMT.differentiableOn_invFunOn_of_injOn hU hdiff hinj
  have hne : deriv φ 0 ≠ 0 := RMT.deriv_ne_zero_of_injOn hU hdiff hinj h0mem
  refine csSup_le ⟨_, φ, ⟨hdiff, hinj, himg⟩, h0, rfl⟩ ?_
  rintro m ⟨φ', ⟨hd', hi', hm'⟩, h0', rfl⟩
  have hne' : deriv φ' 0 ≠ 0 := RMT.deriv_ne_zero_of_injOn hU hd' hi' h0mem
  set g := Function.invFunOn φ unitDisc ∘ φ' with hg
  have hmaps : MapsTo φ' unitDisc (φ '' unitDisc) := fun z hz => himg ▸ hm' ▸ mem_image_of_mem φ' hz
  have hgφ : ∀ z ∈ unitDisc, φ (g z) = φ' z := by
    intro z hz
    obtain ⟨x, hx, hxe⟩ := hmaps hz
    exact Function.invFunOn_eq (f := φ) (s := unitDisc) (b := φ' z) ⟨x, hx, hxe⟩
  have hgmem : ∀ z ∈ unitDisc, g z ∈ unitDisc := by
    intro z hz
    obtain ⟨x, hx, hxe⟩ := hmaps hz
    exact Function.invFunOn_mem (f := φ) (s := unitDisc) (b := φ' z) ⟨x, hx, hxe⟩
  have hg0 : g 0 = 0 := by
    have this : φ (g 0) = φ 0 := by rw [hgφ 0 h0mem, h0', h0]
    exact hinj (hgmem 0 h0mem) h0mem this
  have hgd : DifferentiableOn ℂ g unitDisc := hinvd.comp hd' hmaps
  have hmapsb : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
    intro z hz
    rw [hg0]
    exact ball_subset_closedBall (hgmem z hz)
  have hsch : ‖deriv g 0‖ ≤ 1 := by
    have := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hmapsb one_pos
    simpa using this
  have hev : φ' =ᶠ[𝓝 0] φ ∘ g := by
    filter_upwards [hU.mem_nhds h0mem] with z hz
    exact (hgφ z hz).symm
  have hφd : DifferentiableAt ℂ φ (g 0) := by
    rw [hg0]; exact hdiff.differentiableAt (hU.mem_nhds h0mem)
  have hgda : DifferentiableAt ℂ g 0 := hgd.differentiableAt (hU.mem_nhds h0mem)
  have hder : deriv φ' 0 = deriv φ 0 * deriv g 0 := by
    rw [hev.deriv_eq]
    have := deriv_comp (x := (0 : ℂ)) hφd hgda
    simpa [Function.comp, hg0] using this
  have hle : ‖deriv φ' 0‖ ≤ ‖deriv φ 0‖ := by
    rw [hder, norm_mul]
    calc ‖deriv φ 0‖ * ‖deriv g 0‖ ≤ ‖deriv φ 0‖ * 1 := mul_le_mul_of_nonneg_left hsch (norm_nonneg _)
      _ = _ := mul_one _
  have hpos : 0 < ‖deriv φ' 0‖ := norm_pos_iff.2 hne'
  have hlog := Real.log_le_log hpos hle
  have : 0 ≤ 1 / (2 * π) := by positivity
  exact mul_le_mul_of_nonneg_left hlog this

/-- Helper (Bessel's inequality, finitely many modes, on `[0, 2π]`). -/
theorem gm5_bessel {f : ℝ → ℂ} (hf : Continuous f) (K : Finset ℤ) (c : ℤ → ℂ)
    (hc : ∀ j ∈ K, ∫ θ in (0 : ℝ)..2 * π, f θ * exp (-(j : ℂ) * θ * I) = 2 * π * c j) :
    2 * π * ∑ j ∈ K, ‖c j‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2 := by
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  set e : ℤ → ℝ → ℂ := fun j θ => exp ((j : ℂ) * θ * I) with he
  have he_cont : ∀ j, Continuous (e j) := fun j =>
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have he_conj : ∀ j θ, (starRingEnd ℂ) (e j θ) = exp (-(j : ℂ) * θ * I) := by
    intro j θ
    simp only [he]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
    ring
  have he_orth : ∀ j l, ∫ θ in (0 : ℝ)..2 * π, e j θ * (starRingEnd ℂ) (e l θ) = if j = l then 2 * π else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst hjl
      simp only [ite_true]
      have : ∀ θ : ℝ, e j θ * (starRingEnd ℂ) (e j θ) = 1 := by
        intro θ
        rw [he_conj]
        simp only [he]
        rw [← Complex.exp_add]
        ring_nf
        simp
      simp_rw [this]
      simp
    · simp only [hjl, ↓reduceIte, Complex.ofReal_zero]
      have hk : (j - l : ℤ) ≠ 0 := sub_ne_zero.2 hjl
      have : ∀ θ : ℝ, e j θ * (starRingEnd ℂ) (e l θ) = exp (((j - l : ℤ) : ℂ) * I * θ) := by
        intro θ
        rw [he_conj]
        simp only [he]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp_rw [this]
      exact LiZhongQC.kn_integral_exp _ hk
  set k : ℝ → ℂ := fun θ => ∑ j ∈ K, c j * e j θ with hk_def
  have hk_cont : Continuous k := continuous_finsetSum _ fun j _ => continuous_const.mul (he_cont j)
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f θ - k θ‖ ^ 2 :=
    intervalIntegral.integral_nonneg hpi fun θ _ => sq_nonneg _
  have hpt : ∀ θ, ‖f θ - k θ‖ ^ 2 = ‖f θ‖ ^ 2 - 2 * (f θ * (starRingEnd ℂ) (k θ)).re + (k θ * (starRingEnd ℂ) (k θ)).re := by
    intro θ
    have h1 : (k θ * (starRingEnd ℂ) (k θ)).re = Complex.normSq (k θ) := by rw [Complex.mul_conj]; simp
    simp only [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_sub, h1]
    ring
  have hfk : ∀ j ∈ K, IntervalIntegrable (fun θ => f θ * (starRingEnd ℂ) (e j θ)) volume 0 (2 * π) := fun j _ =>
    (hf.mul (Complex.continuous_conj.comp (he_cont j))).intervalIntegrable _ _
  -- cross term
  have hcross : ∫ θ in (0 : ℝ)..2 * π, f θ * (starRingEnd ℂ) (k θ) = ((2 * π * ∑ j ∈ K, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    have : ∀ θ, f θ * (starRingEnd ℂ) (k θ) = ∑ j ∈ K, (starRingEnd ℂ) (c j) * (f θ * (starRingEnd ℂ) (e j θ)) := by
      intro θ
      simp only [hk_def, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum fun j hj => (hfk j hj).const_mul _]
    have : ∀ j ∈ K, ∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (c j) * (f θ * (starRingEnd ℂ) (e j θ)) = 2 * π * ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      have h1 : ∀ θ, f θ * (starRingEnd ℂ) (e j θ) = f θ * exp (-(j : ℂ) * θ * I) := fun θ => by rw [he_conj]
      simp_rw [h1]
      rw [hc j hj, ← mul_assoc, mul_comm ((starRingEnd ℂ) (c j)) _]
      rw [mul_assoc, Complex.conj_mul']
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    push_cast
    ring
  -- ‖k‖²
  have hkk : ∫ θ in (0 : ℝ)..2 * π, k θ * (starRingEnd ℂ) (k θ) = ((2 * π * ∑ j ∈ K, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    have : ∀ θ, k θ * (starRingEnd ℂ) (k θ) = ∑ j ∈ K, ∑ l ∈ K, (c j * (starRingEnd ℂ) (c l)) * (e j θ * (starRingEnd ℂ) (e l θ)) := by
      intro θ
      simp only [hk_def, map_sum, map_mul, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    simp_rw [this]
    have hint : ∀ j ∈ K, ∀ l ∈ K, IntervalIntegrable (fun θ => (c j * (starRingEnd ℂ) (c l)) * (e j θ * (starRingEnd ℂ) (e l θ)))
        volume 0 (2 * π) := fun j _ l _ =>
      (continuous_const.mul ((he_cont j).mul (Complex.continuous_conj.comp (he_cont l)))).intervalIntegrable _ _
    have hint2 : ∀ j ∈ K, IntervalIntegrable (fun θ => ∑ l ∈ K, (c j * (starRingEnd ℂ) (c l)) * (e j θ * (starRingEnd ℂ) (e l θ)))
        volume 0 (2 * π) := fun j _ =>
      (continuous_finsetSum _ fun l _ => continuous_const.mul ((he_cont j).mul
        (Complex.continuous_conj.comp (he_cont l)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint2]
    have hj : ∀ j ∈ K, ∫ θ in (0 : ℝ)..2 * π, ∑ l ∈ K, (c j * (starRingEnd ℂ) (c l)) * (e j θ * (starRingEnd ℂ) (e l θ)) =
        2 * π * ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum fun l hl => hint j hj l hl]
      simp_rw [intervalIntegral.integral_const_mul, he_orth]
      rw [Finset.sum_eq_single j]
      · simp only [ite_true]
        rw [mul_comm, Complex.mul_conj']
        push_cast
        ring
      · intro l _ hlj
        simp [Ne.symm hlj]
      · intro h; exact absurd hj h
    rw [Finset.sum_congr rfl hj, ← Finset.mul_sum]
    push_cast
    ring
  have hre : ∀ g : ℝ → ℂ, Continuous g → ∫ θ in (0 : ℝ)..2 * π, (g θ).re = (∫ θ in (0 : ℝ)..2 * π, g θ).re := by
    intro g hg
    have := Complex.reCLM.intervalIntegral_comp_comm (hg.intervalIntegrable (μ := volume) 0 (2 * π))
    simpa using this
  have hcont1 : Continuous fun θ => f θ * (starRingEnd ℂ) (k θ) := hf.mul (Complex.continuous_conj.comp hk_cont)
  have hcont2 : Continuous fun θ => k θ * (starRingEnd ℂ) (k θ) := hk_cont.mul (Complex.continuous_conj.comp hk_cont)
  have hI : ∫ θ in (0 : ℝ)..2 * π, ‖f θ - k θ‖ ^ 2 =
      (∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2) - 2 * (2 * π * ∑ j ∈ K, ‖c j‖ ^ 2) + 2 * π * ∑ j ∈ K, ‖c j‖ ^ 2 := by
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun θ => ‖f θ‖ ^ 2) volume 0 (2 * π) :=
      (hf.norm.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => 2 * (f θ * (starRingEnd ℂ) (k θ)).re) volume 0 (2 * π) :=
      (continuous_const.mul (Complex.continuous_re.comp hcont1)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun θ => (k θ * (starRingEnd ℂ) (k θ)).re) volume 0 (2 * π) :=
      (Complex.continuous_re.comp hcont2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, hre _ hcont1, hre _ hcont2, hcross, hkk, Complex.ofReal_re]
  linarith [hnonneg, hI]

/-- Helper (mode formula): for `f` holomorphic on a neighbourhood of `closedBall 0 r`, the `n`-th Fourier coefficient of
`θ ↦ f (r e^{iθ})` is `r^n f⁽ⁿ⁾(0)/n!`. -/
theorem gm5_mode {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) * exp (-(n : ℂ) * θ * I) =
      2 * π * (r ^ n * (iteratedDeriv n f 0 / (n.factorial : ℂ))) := by
  have key := hf.circleIntegral_one_div_sub_center_pow_smul hr n
  unfold circleIntegral at key
  simp only [sub_zero, deriv_circleMap, smul_eq_mul] at key
  have e : ∀ θ : ℝ, circleMap 0 r θ * I * (1 / circleMap 0 r θ ^ (n + 1) * f (circleMap 0 r θ)) =
      I * ((r : ℂ) ^ n)⁻¹ * (f (circleMap 0 r θ) * exp (-(n : ℂ) * θ * I)) := by
    intro θ
    have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    rw [circleMap_zero]
    have : exp (-(n : ℂ) * θ * I) = (exp (θ * I) ^ n)⁻¹ := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; ring
    rw [this]
    have hex : exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    ring
  simp_rw [e] at key
  rw [intervalIntegral.integral_const_mul] at key
  have hrn : ((r : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 hr.ne')
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hne : I * ((r : ℂ) ^ n)⁻¹ ≠ 0 := mul_ne_zero I_ne_zero (inv_ne_zero hrn)
  apply mul_left_cancel₀ hne
  rw [key]
  field_simp

/-- Helper (area of an annular image, lower bound from a bound on the circle integrals of `|g'|²`). -/
theorem gm5_area_lower {g g' : ℂ → ℂ} {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ)
    (hder : ∀ w ∈ ball (0 : ℂ) ρ \ closedBall 0 ε, HasDerivAt g (g' w) w)
    (hinj : InjOn g (ball (0 : ℂ) ρ \ closedBall 0 ε))
    (hcont : ContinuousOn g' (ball (0 : ℂ) ρ \ closedBall 0 ε))
    {W : ℝ → ℝ} (hW : ContinuousOn W (Icc ε ρ)) (hW0 : ∀ s ∈ Ioo ε ρ, 0 ≤ W s)
    (hlow : ∀ s ∈ Ioo ε ρ, W s ≤ ∫ θ in Ioo (-π) π, ‖g' (circleMap 0 s θ)‖ ^ 2) :
    ENNReal.ofReal (∫ s in ε..ρ, s * W s) ≤ volume (g '' (ball (0 : ℂ) ρ \ closedBall 0 ε)) := by
  have hAm : MeasurableSet (ball (0 : ℂ) ρ \ closedBall 0 ε) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hf' : ∀ w ∈ ball (0 : ℂ) ρ \ closedBall 0 ε, HasFDerivWithinAt g
      (((1 : ℂ →L[ℂ] ℂ).smulRight (g' w)).restrictScalars ℝ)
      (ball (0 : ℂ) ρ \ closedBall 0 ε) w := fun w hw =>
    ((hder w hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm hf' hinj (fun _ => 1)
  rw [setLIntegral_one] at key
  rw [key]
  have hvol : ∫⁻ w in ball (0 : ℂ) ρ \ closedBall 0 ε, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g' w)).restrictScalars ℝ).det| * 1
      = ∫⁻ w in ball (0 : ℂ) ρ \ closedBall 0 ε, ENNReal.ofReal (‖g' w‖ ^ 2) := by
    refine setLIntegral_congr_fun hAm fun w _ => ?_
    rw [LiZhongQC.kn_det_smulRight, mul_one, abs_of_nonneg (by positivity)]
  rw [hvol]
  have hpolar := Complex.lintegral_comp_polarCoord_symm
    ((ball (0 : ℂ) ρ \ closedBall 0 ε).indicator fun w => ENNReal.ofReal (‖g' w‖ ^ 2))
  rw [lintegral_indicator hAm] at hpolar
  rw [← hpolar]
  have hrect : Ioo ε ρ ×ˢ Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun x hx => lt_trans hε hx.1) le_rfl
  have hrectm : MeasurableSet (Ioo ε ρ ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have hmem : ∀ p ∈ Ioo ε ρ ×ˢ Ioo (-π) π,
      Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ \ closedBall 0 ε := by
    intro p hp
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_trans hε hp.1.1)]
    constructor
    · rw [mem_ball_zero_iff, hn]
      exact hp.1.2
    · rw [mem_closedBall_zero_iff, hn]
      exact not_le.2 hp.1.1
  have hcongr : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ \ closedBall 0 ε).indicator
        (fun w => ENNReal.ofReal (‖g' w‖ ^ 2)) (Complex.polarCoord.symm p) =
      ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ‖g' (circleMap 0 p.1 p.2)‖ ^ 2) := by
    refine setLIntegral_congr_fun hrectm fun p hp => ?_
    rw [Set.indicator_of_mem (hmem p hp), smul_eq_mul, LiZhongQC.kn_polar_symm_eq,
      ENNReal.ofReal_mul (lt_trans hε hp.1.1).le]
  have hmono : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal (p.1 * ‖g' (circleMap 0 p.1 p.2)‖ ^ 2) ≤
      ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ \ closedBall 0 ε).indicator
        (fun w => ENNReal.ofReal (‖g' w‖ ^ 2)) (Complex.polarCoord.symm p) := by
    rw [← hcongr]
    exact lintegral_mono_set hrect
  refine le_trans ?_ hmono
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Ioo ε ρ ×ˢ Ioo (-π) π) =
      ((volume : Measure ℝ).restrict (Ioo ε ρ)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hcm : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    simp only [LiZhongQC.kn_circleMap_eq]
    fun_prop
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖g' (circleMap 0 p.1 p.2)‖ ^ 2)
      (Ioo ε ρ ×ˢ Ioo (-π) π) := by
    have hmaps : ∀ p ∈ Ioo ε ρ ×ˢ Ioo (-π) π, circleMap 0 p.1 p.2 ∈ ball (0 : ℂ) ρ \ closedBall 0 ε :=
      fun p hp => by rw [← LiZhongQC.kn_polar_symm_eq]; exact hmem p hp
    exact continuousOn_fst.mul ((hcont.comp hcm.continuousOn hmaps).norm.pow 2)
  have hae : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 * ‖g' (circleMap 0 p.1 p.2)‖ ^ 2))
      (((volume : Measure ℝ).restrict (Ioo ε ρ)).prod
        ((volume : Measure ℝ).restrict (Ioo (-π) π))) := by
    rw [← hprod]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hcont2.aemeasurable hrectm)
  have htonelli : ∫⁻ p in Ioo ε ρ ×ˢ Ioo (-π) π,
      ENNReal.ofReal (p.1 * ‖g' (circleMap 0 p.1 p.2)‖ ^ 2) =
      ∫⁻ r in Ioo ε ρ, ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (r * ‖g' (circleMap 0 r θ)‖ ^ 2) := by
    rw [hprod, lintegral_prod _ hae]
  rw [htonelli]
  have hinner : ∀ r ∈ Ioo ε ρ,
      ENNReal.ofReal (r * W r) ≤ ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (r * ‖g' (circleMap 0 r θ)‖ ^ 2) := by
    intro r hr
    have hr0 : 0 < r := lt_trans hε hr.1
    have hmemc : ∀ θ : ℝ, circleMap 0 r θ ∈ ball (0 : ℂ) ρ \ closedBall 0 ε := fun θ => by
      constructor
      · rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hr.2
      · rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact not_le.2 hr.1
    have hc : Continuous fun θ : ℝ => r * ‖g' (circleMap 0 r θ)‖ ^ 2 :=
      continuous_const.mul ((hcont.comp_continuous (continuous_circleMap 0 r) hmemc).norm.pow 2)
    have hint : Integrable (fun θ : ℝ => r * ‖g' (circleMap 0 r θ)‖ ^ 2)
        (volume.restrict (Ioo (-π) π)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).1
        (hc.intervalIntegrable _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hlow r hr) hr0.le
  have hcontW : ContinuousOn (fun s : ℝ => s * W s) (uIcc ε ρ) := by
    rw [uIcc_of_le hερ.le]
    exact continuousOn_id.mul hW
  have hint2 : Integrable (fun r : ℝ => r * W r) (volume.restrict (Ioo ε ρ)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hερ.le).1 hcontW.intervalIntegrable
  calc ENNReal.ofReal (∫ s in ε..ρ, s * W s)
      = ENNReal.ofReal (∫ r in Ioo ε ρ, r * W r) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hερ.le]
    _ = ∫⁻ r in Ioo ε ρ, ENNReal.ofReal (r * W r) := by
        refine ofReal_integral_eq_lintegral_ofReal hint2 ?_
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun r hr => ?_
        have : 0 < r := lt_trans hε hr.1
        have := hW0 r hr
        simp only [Pi.zero_apply]
        positivity
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hinner

/-- Helper: the circle integral over `(-π, π)` equals the one over `(0, 2π)` (periodicity). -/
theorem gm5_circle_Ioo (G : ℂ → ℝ) (s : ℝ) :
    ∫ θ in Ioo (-π) π, G (circleMap 0 s θ) = ∫ θ in (0 : ℝ)..2 * π, G (circleMap 0 s θ) := by
  have hper : Function.Periodic (fun θ : ℝ => G (circleMap 0 s θ)) (2 * π) :=
    (periodic_circleMap 0 s).comp G
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), hshift]

/-- Helper: the Taylor coefficients of `deriv φ`. -/
theorem gm5_coeff_deriv (φ : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (deriv φ) 0 / (n.factorial : ℂ) =
      ((n + 1 : ℕ) : ℂ) * (iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)) := by
  rw [iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- Helper: lower bound for the circle integral of `|φ'|²`. -/
theorem gm5_circle_phi {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1)) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (N : ℕ) :
    2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) *
        (((n + 1 : ℕ) : ℝ) * ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖) ^ 2 ≤
      ∫ θ in Ioo (-π) π, ‖deriv φ (circleMap 0 s θ)‖ ^ 2 := by
  have hd : DifferentiableOn ℂ (deriv φ) (ball (0 : ℂ) 1) := hφ.deriv isOpen_ball
  have hdc : DifferentiableOn ℂ (deriv φ) (closedBall (0 : ℂ) s) := hd.mono (closedBall_subset_ball hs1)
  have hcont : Continuous fun θ : ℝ => deriv φ (circleMap 0 s θ) :=
    hdc.continuousOn.comp_continuous (continuous_circleMap 0 s) fun θ => by
      rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hs]
  rw [gm5_circle_Ioo (fun w => ‖deriv φ w‖ ^ 2)]
  set K : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ)) with hK
  set c : ℤ → ℂ := fun j => (s : ℂ) ^ j.toNat * (iteratedDeriv j.toNat (deriv φ) 0 / (j.toNat.factorial : ℂ)) with hc
  have hbes := gm5_bessel hcont K c (by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    have := gm5_mode hs hdc n
    simp only [hc, Int.toNat_natCast]
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp)
  refine le_trans (le_of_eq ?_) hbes
  rw [hK, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [hc, Int.toNat_natCast]
  rw [gm5_coeff_deriv, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have : ‖((n + 1 : ℕ) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) := Complex.norm_natCast _
  rw [this, pow_mul]
  ring

/-- Helper: `Φ' = -w⁻² + h'` for `h w = w G₂(w)`, away from `0`. -/
theorem gm5_phi'_eq {F : ℂ → ℂ} (hF : LiZhongQC.knHyp F) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hw0 : w ≠ 0) :
    LiZhongQC.knPhi' F w = -((w ^ 2)⁻¹) + deriv (fun v => v * LiZhongQC.knG₂ F v) w := by
  have hh : DifferentiableAt ℂ (fun v => v * LiZhongQC.knG₂ F v) w :=
    differentiableAt_id.mul (hF.analyticAt_G₂ hw).differentiableAt
  have hd1 := hF.hasDerivAt_phi hw hw0
  have hev : LiZhongQC.knPhi F =ᶠ[𝓝 w] fun v => v⁻¹ + LiZhongQC.knG1 F + v * LiZhongQC.knG₂ F v := by
    filter_upwards [isOpen_ne.mem_nhds hw0] with v hv
    rw [LiZhongQC.knPhi, hF.G_expand2 v]
    field_simp
  have hd2 : HasDerivAt (fun v => v⁻¹ + LiZhongQC.knG1 F + v * LiZhongQC.knG₂ F v)
      (-((w ^ 2)⁻¹) + deriv (fun v => v * LiZhongQC.knG₂ F v) w) w := by
    have h1 := (hasDerivAt_inv hw0)
    have h2 := (h1.add_const (LiZhongQC.knG1 F)).add hh.hasDerivAt
    convert h2 using 1
  exact hd1.unique (hd2.congr_of_eventuallyEq hev)

/-- Helper: lower bound for the circle integral of `|Φ'|²`. -/
theorem gm5_circle_Phi {F : ℂ → ℂ} (hF : LiZhongQC.knHyp F) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (N : ℕ) :
    2 * π * (((s ^ 2)⁻¹) ^ 2 + ∑ n ∈ Finset.range N, s ^ (2 * n) *
        (((n + 1 : ℕ) : ℝ) * ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 /
          ((n + 1).factorial : ℂ)‖) ^ 2) ≤
      ∫ θ in Ioo (-π) π, ‖LiZhongQC.knPhi' F (circleMap 0 s θ)‖ ^ 2 := by
  set h : ℂ → ℂ := fun w => w * LiZhongQC.knG₂ F w with hh
  have hd : DifferentiableOn ℂ h (ball (0 : ℂ) 1) := fun w hw =>
    (differentiableAt_id.mul (hF.analyticAt_G₂ hw).differentiableAt).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (deriv h) (closedBall (0 : ℂ) s) :=
    (hd.deriv isOpen_ball).mono (closedBall_subset_ball hs1)
  have hcont : Continuous fun θ : ℝ => LiZhongQC.knPhi' F (circleMap 0 s θ) :=
    hF.continuous_phi'_circle hs hs1
  rw [gm5_circle_Ioo (fun w => ‖LiZhongQC.knPhi' F w‖ ^ 2)]
  set K : Finset ℤ := insert (-2) ((Finset.range N).image (fun n : ℕ => (n : ℤ))) with hK
  set c : ℤ → ℂ := fun j => if j = -2 then -(((s : ℂ) ^ 2)⁻¹) else
    (s : ℂ) ^ j.toNat * (iteratedDeriv j.toNat (deriv h) 0 / (j.toNat.factorial : ℂ)) with hc
  have hmem : ∀ θ : ℝ, circleMap 0 s θ ∈ ball (0 : ℂ) 1 ∧ circleMap 0 s θ ≠ 0 :=
    fun θ => LiZhongQC.kn_circleMap_mem hs hs1 θ
  have hbes := gm5_bessel hcont K c (by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · simp only [hc, ↓reduceIte]
      have := hF.int_alpha hs hs1
      have e : ∀ θ : ℝ, LiZhongQC.knPhi' F (circleMap 0 s θ) * exp (-(((-2 : ℤ) : ℂ)) * θ * I) =
          LiZhongQC.knPhi' F (circleMap 0 s θ) * exp (2 * θ * I) := fun θ => by push_cast; ring_nf
      simp_rw [e]
      rw [this]
      have : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
      field_simp
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj'
      have hne : ((n : ℤ)) ≠ -2 := by omega
      simp only [hc, hne, ↓reduceIte, Int.toNat_natCast]
      have hmode := gm5_mode hs hd' n
      -- split `Φ' = -(w²)⁻¹ + h'`
      have hsplit : ∀ θ : ℝ, LiZhongQC.knPhi' F (circleMap 0 s θ) * exp (-(((n : ℤ) : ℂ)) * θ * I) =
          deriv h (circleMap 0 s θ) * exp (-(n : ℂ) * θ * I) +
            (-(((s : ℂ) ^ 2)⁻¹) * exp (-((n + 2 : ℕ) : ℂ) * θ * I)) := by
        intro θ
        rw [gm5_phi'_eq hF (hmem θ).1 (hmem θ).2, circleMap_zero]
        have hex : exp (-((n + 2 : ℕ) : ℂ) * θ * I) = exp (-(n : ℂ) * θ * I) * (exp (θ * I) ^ 2)⁻¹ := by
          rw [← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
          congr 1; push_cast; ring
        rw [hex]
        have hex0 := Complex.exp_ne_zero ((θ : ℂ) * I)
        have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
        push_cast
        field_simp
        simp only [hh]
        ring
      have hAc : Continuous fun θ : ℝ => deriv h (circleMap 0 s θ) * exp (-(n : ℂ) * θ * I) :=
        (hd'.continuousOn.comp_continuous (continuous_circleMap 0 s) fun θ => by
          rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hs]).mul
          (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
      have hBc : Continuous fun θ : ℝ => -(((s : ℂ) ^ 2)⁻¹) * exp (-((n + 2 : ℕ) : ℂ) * θ * I) :=
        continuous_const.mul (Complex.continuous_exp.comp
          ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
      simp_rw [hsplit]
      rw [intervalIntegral.integral_add (hAc.intervalIntegrable _ _) (hBc.intervalIntegrable _ _), hmode]
      have hB : ∫ θ in (0 : ℝ)..2 * π, -(((s : ℂ) ^ 2)⁻¹) * exp (-((n + 2 : ℕ) : ℂ) * θ * I) = 0 := by
        rw [intervalIntegral.integral_const_mul]
        have h0 := LiZhongQC.kn_integral_exp (-((n + 2 : ℕ) : ℤ)) (by omega)
        have e : ∀ θ : ℝ, exp (-((n + 2 : ℕ) : ℂ) * θ * I) = exp (((-((n + 2 : ℕ) : ℤ) : ℤ) : ℂ) * I * θ) := by
          intro θ; push_cast; ring_nf
        simp_rw [e]
        rw [h0, mul_zero]
      rw [hB, add_zero])
  refine le_trans (le_of_eq ?_) hbes
  have hnot : (-2 : ℤ) ∉ (Finset.range N).image (fun n : ℕ => (n : ℤ)) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro n _ h; omega
  have h1 : ‖c (-2)‖ ^ 2 = ((s ^ 2)⁻¹) ^ 2 := by
    simp only [hc, ↓reduceIte]
    rw [norm_neg, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have h2 : ∑ n ∈ Finset.range N, ‖c (n : ℤ)‖ ^ 2 = ∑ n ∈ Finset.range N, s ^ (2 * n) *
      (((n + 1 : ℕ) : ℝ) * ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 /
        ((n + 1).factorial : ℂ)‖) ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hne : ((n : ℤ)) ≠ -2 := by omega
    simp only [hc, hne, ↓reduceIte, Int.toNat_natCast]
    rw [gm5_coeff_deriv, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have : ‖((n + 1 : ℕ) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) := Complex.norm_natCast _
    rw [this, pow_mul]
    ring
  rw [hK, Finset.sum_insert hnot, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h), h1, h2]

/-- Helper: `∫_ε^ρ s · 2π Σ s^{2n} q_n ds`. -/
theorem gm5_int_poly {ε ρ : ℝ} (N : ℕ) (q : ℕ → ℝ) :
    ∫ s in ε..ρ, s * (2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n) =
      π * ∑ n ∈ Finset.range N, q n / ((n : ℝ) + 1) * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) := by
  have hterm : ∀ n ∈ Finset.range N, ∫ s in ε..ρ, s * (2 * π * (s ^ (2 * n) * q n)) =
      2 * π * q n * ((ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) / ((2 * n + 1 : ℕ) + 1)) := by
    intro n _
    have : ∀ s : ℝ, s * (2 * π * (s ^ (2 * n) * q n)) = (2 * π * q n) * s ^ (2 * n + 1) := fun s => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_pow]
  have hsplit : ∀ s : ℝ, s * (2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n) =
      ∑ n ∈ Finset.range N, s * (2 * π * (s ^ (2 * n) * q n)) := fun s => by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_finsetSum fun n _ => (by fun_prop : Continuous fun s : ℝ =>
    s * (2 * π * (s ^ (2 * n) * q n))).intervalIntegrable _ _]
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  field_simp
  ring

/-- Helper: the area of the annular image `φ(ε < |z| < ρ)`, lower bound (area theorem, part 1). -/
theorem gm5_area_phi {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hinj : InjOn φ (ball (0 : ℂ) 1)) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ : ρ < 1) (N : ℕ) :
    ENNReal.ofReal (π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
        ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2))) ≤
      volume (φ '' (ball (0 : ℂ) ρ \ closedBall 0 ε)) := by
  have hsub : ball (0 : ℂ) ρ \ closedBall 0 ε ⊆ ball (0 : ℂ) 1 := fun w hw =>
    ball_subset_ball hρ.le hw.1
  have hd : DifferentiableOn ℂ (deriv φ) (ball (0 : ℂ) 1) := hφ.deriv isOpen_ball
  set q : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) *
    ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖) ^ 2 with hq
  have hlow := gm5_area_lower (g := φ) (g' := deriv φ) hε hερ
    (fun w hw => (hφ.differentiableAt (isOpen_ball.mem_nhds (hsub hw))).hasDerivAt)
    (hinj.mono hsub) (hd.continuousOn.mono hsub)
    (W := fun s => 2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n)
    (by fun_prop) (fun s hs => by
      have hs0 : 0 < s := lt_trans hε hs.1
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hs0.le _) (sq_nonneg _)))
    (fun s hs => by
      have := gm5_circle_phi hφ (lt_trans hε hs.1) (lt_trans hs.2 hρ) N
      simpa [hq] using this)
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hlow
  rw [gm5_int_poly]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [hq]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Helper: the area of the annular image `Φ(ε < |w| < ρ)`, lower bound (area theorem, part 2). -/
theorem gm5_area_Phi {F : ℂ → ℂ} (hF : LiZhongQC.knHyp F) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ : ρ < 1)
    (N : ℕ) :
    ENNReal.ofReal (π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
        ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 *
          (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2))) ≤
      volume (LiZhongQC.knPhi F '' (ball (0 : ℂ) ρ \ closedBall 0 ε)) := by
  have hsub := LiZhongQC.kn_annulus_subset hε hρ
  set q : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) *
    ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖) ^ 2 with hq
  have hlow := gm5_area_lower (g := LiZhongQC.knPhi F) (g' := LiZhongQC.knPhi' F) hε hερ
    (fun w hw => hF.hasDerivAt_phi (hsub hw).1 (hsub hw).2)
    (hF.phi_injOn.mono hsub) (hF.continuousOn_phi'.mono hsub)
    (W := fun s => 2 * π * (((s ^ 2)⁻¹) ^ 2 + ∑ n ∈ Finset.range N, s ^ (2 * n) * q n))
    (by
      refine continuousOn_const.mul (ContinuousOn.add ?_ (by fun_prop))
      refine ((continuousOn_id.pow 2).inv₀ ?_).pow 2
      intro s hs
      exact pow_ne_zero 2 (by linarith [hs.1] : s ≠ 0))
    (fun s hs => by
      have hs0 : 0 < s := lt_trans hε hs.1
      exact mul_nonneg (by positivity) (add_nonneg (by positivity)
        (Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hs0.le _) (sq_nonneg _))))
    (fun s hs => by
      have := gm5_circle_Phi hF (lt_trans hε hs.1) (lt_trans hs.2 hρ) N
      simpa [hq] using this)
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hlow
  have e1 : ∀ s : ℝ, s * (2 * π * (((s ^ 2)⁻¹) ^ 2 + ∑ n ∈ Finset.range N, s ^ (2 * n) * q n)) =
      2 * π * s * (0 ^ 2 + ((s ^ 2)⁻¹) ^ 2) + s * (2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n) := by
    intro s; ring
  simp_rw [e1]
  have hc1 : IntervalIntegrable (fun s : ℝ => 2 * π * s * (0 ^ 2 + ((s ^ 2)⁻¹) ^ 2)) volume ε ρ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hερ.le]
    refine (continuousOn_const.mul continuousOn_id).mul (continuousOn_const.add ?_)
    refine ((continuousOn_id.pow 2).inv₀ ?_).pow 2
    intro s hs
    exact pow_ne_zero 2 (by linarith [hs.1] : s ≠ 0)
  have hc2 : IntervalIntegrable (fun s : ℝ => s * (2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n)) volume ε ρ :=
    (by fun_prop : Continuous fun s : ℝ => s * (2 * π * ∑ n ∈ Finset.range N, s ^ (2 * n) * q n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc1 hc2, LiZhongQC.kn_ftc hε hερ, gm5_int_poly]
  have : ∀ n : ℕ, q n / ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) *
      ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 := by
    intro n
    simp only [hq]
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  simp_rw [this]
  ring

/-- Helper (I-5a, T5b). Interior covering: `f` holomorphic in a neighbourhood of `closedBall 0 r`, injective in the open
ball, `f(0) = 0`, with `|f| ≥ m` on `|z| = r`. Then `B(0, m) ⊆ f(B(0, r))`. -/
theorem gm5_cover_disc {f : ℂ → ℂ} {r m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) (hinj : InjOn f (ball (0 : ℂ) r)) (h0 : f 0 = 0)
    (hV : ∀ z : ℂ, ‖z‖ = r → m ≤ ‖f z‖) : ball (0 : ℂ) m ⊆ f '' ball (0 : ℂ) r := by
  have hopen : IsOpen (f '' ball (0 : ℂ) r) :=
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hf.mono ball_subset_closedBall) hinj).1
  have hcpt : IsCompact (f '' closedBall (0 : ℂ) r) := (isCompact_closedBall 0 r).image_of_continuousOn hf.continuousOn
  have hclose : closure (f '' ball (0 : ℂ) r) ⊆ f '' closedBall (0 : ℂ) r :=
    closure_minimal (image_mono ball_subset_closedBall) hcpt.isClosed
  refine (isPreconnected_ball : IsPreconnected (ball (0 : ℂ) m)).subset_of_closure_inter_subset hopen
    ⟨0, mem_ball_self hm, ⟨0, mem_ball_self hr, h0⟩⟩ ?_
  rintro w ⟨hwc, hwV⟩
  obtain ⟨z, hz, rfl⟩ := hclose hwc
  rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with hlt | heq
  · exact ⟨z, mem_ball_zero_iff.2 hlt, rfl⟩
  · exact absurd (hV z heq) (not_le.2 (mem_ball_zero_iff.1 hwV))

/-- Helper (I-5a, T5). Exterior covering: `f` holomorphic and injective in the punctured disc `0 < |z| < r`, continuous
up to `|z| = r`, with a pole at `0` (`|f| → ∞`). If an open connected set `V` contains a neighbourhood of `∞` and misses
`f({|z| = r})`, then `V ⊆ f({0 < |z| < r})`. (Open mapping plus connectedness of `V`; no degree theory.) -/
theorem gm5_cover_pole {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r \ {0}))
    (hinj : InjOn f (ball (0 : ℂ) r \ {0})) (hpole : Tendsto (fun z => ‖f z‖) (𝓝[≠] (0 : ℂ)) atTop)
    {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V) (hVinf : ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → w ∈ V)
    (hV : ∀ z : ℂ, ‖z‖ = r → f z ∉ V) : V ⊆ f '' (ball (0 : ℂ) r \ {0}) := by
  have hUo : IsOpen (ball (0 : ℂ) r \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hsub : ball (0 : ℂ) r \ {0} ⊆ closedBall (0 : ℂ) r \ {0} := sdiff_subset_sdiff_left ball_subset_closedBall
  have hopen : IsOpen (f '' (ball (0 : ℂ) r \ {0})) :=
    (RMT.differentiableOn_invFunOn_of_injOn hUo (hf.mono hsub) hinj).1
  obtain ⟨R, hR⟩ := hVinf
  have hnon : (V ∩ f '' (ball (0 : ℂ) r \ {0})).Nonempty := by
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), R < ‖f z‖ := hpole.eventually_gt_atTop R
    have h2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball (0 : ℂ) r :=
      eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
    have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    obtain ⟨z, hz1, hz2, hz3⟩ := (h1.and (h2.and h3)).exists
    exact ⟨f z, hR _ hz1, z, ⟨hz2, hz3⟩, rfl⟩
  refine hVc.subset_of_closure_inter_subset hopen hnon ?_
  rintro w ⟨hwc, hwV⟩
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 (hpole.eventually_gt_atTop (‖w‖ + 1))
  have hK : IsCompact (f '' (closedBall (0 : ℂ) r \ ball 0 ε)) := by
    refine IsCompact.image_of_continuousOn ((isCompact_closedBall 0 r).diff isOpen_ball) ?_
    refine hf.continuousOn.mono (sdiff_subset_sdiff_right ?_)
    intro x hx
    rw [mem_singleton_iff.1 hx]
    exact mem_ball_self hε
  have hwK : w ∈ f '' (closedBall (0 : ℂ) r \ ball 0 ε) := by
    refine hK.isClosed.closure_subset_iff.2 le_rfl ?_
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨b, ⟨z, hz, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hwc (min e 1) (lt_min he one_pos)
    refine ⟨f z, ⟨z, ⟨ball_subset_closedBall hz.1, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
    · intro hzε
      have hz0 : z ≠ 0 := hz.2
      have := hεs ⟨hzε, hz0⟩
      have h1 : ‖f z‖ < ‖w‖ + 1 := by
        have h2 := norm_sub_norm_le (f z) w
        have h3 : ‖f z - w‖ = dist w (f z) := by rw [dist_comm, dist_eq_norm]
        have h4 : dist w (f z) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
        linarith
      have h5 : ‖w‖ + 1 < ‖f z‖ := this
      linarith
  obtain ⟨z, ⟨hz, hzε⟩, rfl⟩ := hwK
  rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with hlt | heq
  · refine ⟨z, ⟨mem_ball_zero_iff.2 hlt, ?_⟩, rfl⟩
    intro h0
    exact hzε (by rw [mem_singleton_iff.1 h0]; exact mem_ball_self hε)
  · exact absurd hwV (hV z heq)

/-- Helper: the exterior of a closed disc in `ℂ` is preconnected. -/
theorem gm5_compl_closedBall_conn (R : ℝ) : IsPreconnected (closedBall (0 : ℂ) R)ᶜ := by
  have hc : IsPreconnected (Ioi R ×ˢ (univ : Set ℝ)) := isPreconnected_Ioi.prod isPreconnected_univ
  have himg := hc.image (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (by
    have : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
      simp only [LiZhongQC.kn_circleMap_eq]
      fun_prop
    exact this.continuousOn)
  convert himg using 1
  ext z
  simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le, mem_image, mem_prod, mem_Ioi, mem_univ, and_true,
    Prod.exists]
  constructor
  · intro hz
    refine ⟨‖z‖, Complex.arg z, hz, ?_⟩
    rw [circleMap_zero, ← Complex.norm_mul_exp_arg_mul_I z]
    simp [Complex.norm_mul_exp_arg_mul_I]
  · rintro ⟨r, θ, hr, rfl⟩
    rw [norm_circleMap_zero]
    exact lt_of_lt_of_le hr (le_abs_self r)

/-- Helper: left inverse of `A_a`. -/
theorem gm5_knA_left {a : ℂ} (ha : ‖a‖ < 1) (ζ : ℂ) :
    (LiZhongQC.knA a ζ - a * (starRingEnd ℂ) (LiZhongQC.knA a ζ)) / ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = ζ := by
  have hpos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hne : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  rw [div_eq_iff hne, LiZhongQC.knA_apply]
  simp only [map_add, map_mul, Complex.conj_conj]
  push_cast
  linear_combination (-ζ) * Complex.mul_conj' a

/-- Helper: the complement of a closed ellipse `g + A_a(closedBall 0 R)` is open, preconnected and contains a
neighbourhood of `∞`. -/
theorem gm5_ellipse_compl {a : ℂ} (ha : ‖a‖ < 1) (g : ℂ) (R : ℝ) :
    IsOpen ((fun ζ => g + LiZhongQC.knA a ζ) '' closedBall (0 : ℂ) R)ᶜ ∧
      IsPreconnected ((fun ζ => g + LiZhongQC.knA a ζ) '' closedBall (0 : ℂ) R)ᶜ ∧
      ∃ R' : ℝ, ∀ w : ℂ, R' < ‖w‖ → w ∈ ((fun ζ => g + LiZhongQC.knA a ζ) '' closedBall (0 : ℂ) R)ᶜ := by
  set ψ : ℂ → ℂ := fun ζ => g + LiZhongQC.knA a ζ with hψ
  have hcont : Continuous ψ := by
    refine continuous_const.add ?_
    exact (LiZhongQC.knA a).continuous_of_finiteDimensional
  have hcpt : IsCompact (ψ '' closedBall (0 : ℂ) R) := (isCompact_closedBall 0 R).image hcont
  refine ⟨hcpt.isClosed.isOpen_compl, ?_, ?_⟩
  · have heq : (ψ '' closedBall (0 : ℂ) R)ᶜ = ψ '' (closedBall (0 : ℂ) R)ᶜ := by
      ext w
      simp only [mem_compl_iff, mem_image, not_exists, not_and]
      constructor
      · intro hw
        refine ⟨(((w - g) - a * (starRingEnd ℂ) (w - g)) / ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)), ?_, ?_⟩
        · intro hmem
          exact hw _ hmem (by simp only [hψ]; rw [LiZhongQC.knA_inv_apply ha]; ring)
        · simp only [hψ]; rw [LiZhongQC.knA_inv_apply ha]; ring
      · rintro ⟨ζ, hζ, rfl⟩ ζ' hζ' hζζ'
        have h1 : LiZhongQC.knA a ζ' = LiZhongQC.knA a ζ := by simpa [hψ] using hζζ'
        have := gm5_knA_left ha ζ'
        rw [h1, gm5_knA_left ha ζ] at this
        exact hζ (this ▸ hζ')
    rw [heq]
    exact (gm5_compl_closedBall_conn R).image ψ hcont.continuousOn
  · obtain ⟨R', hR'⟩ := hcpt.isBounded.exists_norm_le
    exact ⟨R', fun w hw hmem => absurd (hR' w hmem) (not_le.2 hw)⟩

/-- Helper: `Φ = 1/F` has a pole at `0`. -/
theorem gm5_Phi_pole {F : ℂ → ℂ} (hF : LiZhongQC.knHyp F) :
    Tendsto (fun z => ‖LiZhongQC.knPhi F z‖) (𝓝[≠] (0 : ℂ)) atTop := by
  have hG : Tendsto (fun z => ‖LiZhongQC.knG F z‖) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h1 : ‖LiZhongQC.knG F 0‖ = 1 := by rw [hF.G_zero, norm_one]
    have := (hF.analyticAt_G (mem_ball_self one_pos)).continuousAt.norm.tendsto
    rw [h1] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_norm_zero.mono_left nhdsWithin_le_nhds, by
      filter_upwards [self_mem_nhdsWithin] with z hz using norm_pos_iff.2 hz⟩
  have hinv : Tendsto (fun z : ℂ => ‖z‖⁻¹) (𝓝[≠] (0 : ℂ)) atTop := tendsto_inv_nhdsGT_zero.comp hnorm
  have hhalf : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (1 / 2 : ℝ) < ‖LiZhongQC.knG F z‖ :=
    hG.eventually (lt_mem_nhds (by norm_num))
  refine tendsto_atTop_mono' _ ?_ (hinv.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hhalf, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  simp only [LiZhongQC.knPhi, norm_div]
  rw [div_eq_mul_inv ‖LiZhongQC.knG F z‖ ‖z‖]
  have : (0 : ℝ) ≤ ‖z‖⁻¹ := by positivity
  nlinarith

/-- Helper (area theorem, one value of `ε`): the two annular images lie in the ellipse and are disjoint, so their
areas add up to at most the area of the ellipse. -/
theorem gm5_area_ineq {F φ : ℂ → ℂ} (hF : LiZhongQC.knHyp F) (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hinj : InjOn φ (ball (0 : ℂ) 1))
    (hdisj : Disjoint (φ '' ball (0 : ℂ) 1) (LiZhongQC.knPhi F '' (ball (0 : ℂ) 1 \ {0})))
    {a g : ℂ} (ha : ‖a‖ < 1) {R ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ : ρ < 1) (hR : 0 ≤ R)
    (hcont : ∀ w ∈ ball (0 : ℂ) ρ \ closedBall 0 ε,
      LiZhongQC.knPhi F w ∈ (fun ζ => g + LiZhongQC.knA a ζ) '' closedBall (0 : ℂ) R) (N : ℕ) :
    π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
        ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 *
          (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) +
      π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
        ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) ≤
      (1 - ‖a‖ ^ 2) * (π * R ^ 2) := by
  set A : Set ℂ := ball (0 : ℂ) ρ \ closedBall 0 ε with hA
  set E : Set ℂ := (fun ζ => g + LiZhongQC.knA a ζ) '' closedBall (0 : ℂ) R with hE
  have hAsub := LiZhongQC.kn_annulus_subset hε hρ
  have hAo : IsOpen A := isOpen_ball.sdiff Metric.isClosed_closedBall
  obtain ⟨hVo, hVc, R', hR'⟩ := gm5_ellipse_compl ha g R
  set ε' : ℝ := (ε + ρ) / 2 with hε'
  have hεε' : ε < ε' := by rw [hε']; linarith
  have hε'ρ : ε' < ρ := by rw [hε']; linarith
  have hε'0 : 0 < ε' := lt_trans hε hεε'
  have hdiffΦ : DifferentiableOn ℂ (LiZhongQC.knPhi F) (closedBall (0 : ℂ) ε' \ {0}) := by
    intro w hw
    have hw1 : w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw.1) (lt_trans hε'ρ hρ)
    exact (hF.hasDerivAt_phi hw1 hw.2).differentiableAt.differentiableWithinAt
  have hsub' : ball (0 : ℂ) ε' \ {0} ⊆ ball (0 : ℂ) 1 \ {0} := fun w hw =>
    ⟨ball_subset_ball (lt_trans hε'ρ hρ).le hw.1, hw.2⟩
  have hcover : Eᶜ ⊆ LiZhongQC.knPhi F '' (ball (0 : ℂ) ε' \ {0}) :=
    gm5_cover_pole hε'0 hdiffΦ (hF.phi_injOn.mono hsub') (gm5_Phi_pole hF) hVo hVc ⟨R', hR'⟩ (by
      intro z hz hzV
      refine hzV (hcont z ⟨?_, ?_⟩)
      · rw [mem_ball_zero_iff, hz]; exact hε'ρ
      · rw [mem_closedBall_zero_iff, hz]; exact not_le.2 hεε')
  -- the two images lie in the ellipse
  have hφE : φ '' A ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hnot
    obtain ⟨w, hw, hwe⟩ := hcover hnot
    exact Set.disjoint_left.1 hdisj (mem_image_of_mem φ ((hAsub hz).1)) ⟨w, hsub' hw, hwe⟩
  have hΦE : LiZhongQC.knPhi F '' A ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcont z hz
  have hdisjA : Disjoint (φ '' A) (LiZhongQC.knPhi F '' A) :=
    Disjoint.mono (image_mono fun z hz => (hAsub hz).1) (image_mono hAsub) hdisj
  have hΦopen : IsOpen (LiZhongQC.knPhi F '' A) := by
    have hd : DifferentiableOn ℂ (LiZhongQC.knPhi F) A := fun w hw =>
      (hF.hasDerivAt_phi (hAsub hw).1 (hAsub hw).2).differentiableAt.differentiableWithinAt
    exact (RMT.differentiableOn_invFunOn_of_injOn hAo hd (hF.phi_injOn.mono hAsub)).1
  have hvol := measure_union (μ := volume) hdisjA hΦopen.measurableSet
  have hsum : volume (φ '' A) + volume (LiZhongQC.knPhi F '' A) ≤ volume E := by
    rw [← hvol]
    exact measure_mono (union_subset hφE hΦE)
  rw [hE, LiZhongQC.kn_volume_ellipse ha g hR] at hsum
  have h1 := gm5_area_phi hφ hinj hε hερ hρ N
  have h2 := gm5_area_Phi hF hε hερ hρ N
  have hnn1 : 0 ≤ π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
      ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) := by
    refine mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun n _ => ?_)
    refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
    exact pow_le_pow_left₀ hε.le hερ.le _
  have hnn2 : 0 ≤ π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
      ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 *
        (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) := by
    have hinv : (ρ ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hε.le hερ.le 2)
    refine add_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hinv)) (mul_nonneg Real.pi_pos.le
      (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (sub_nonneg.2 ?_)))
    exact pow_le_pow_left₀ hε.le hερ.le _
  have hle := (add_le_add h1 h2).trans hsum
  rw [← ENNReal.ofReal_add hnn1 hnn2] at hle
  have hR0 : 0 ≤ (1 - ‖a‖ ^ 2) * (π * R ^ 2) := by
    have : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    positivity
  have := (ENNReal.ofReal_le_ofReal_iff hR0).1 hle
  linarith

/-- Helper (I-5a, T3). The area theorem for a disjoint pair (Pommerenke's proof, (4.7) in the book): `F` normalized
(`LiZhongQC.knHyp`: holomorphic and injective in `𝔻`, `F(0) = 0`, `F'(0) = 1`), `Φ = 1/F = 1/w + g₁ + h(w)` with
`h(w) = w·G₂(w) = Σ_{n≥1} β_n wⁿ`, and `φ` holomorphic and injective in `𝔻` with `φ(0) = 0` and `φ(𝔻) ∩ Φ(𝔻 \ {0}) = ∅`
(`φ = Σ a_n zⁿ`). Then `Σ_{n≥1} n (|a_n|² + |β_n|²) ≤ 1` (all partial sums). -/
theorem gm5_area_theorem {F φ : ℂ → ℂ} (hF : LiZhongQC.knHyp F) (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hinj : InjOn φ (ball (0 : ℂ) 1)) (h0 : φ 0 = 0)
    (hdisj : Disjoint (φ '' ball (0 : ℂ) 1) (LiZhongQC.knPhi F '' (ball (0 : ℂ) 1 \ {0}))) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
      (‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 +
        ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2) ≤ 1 := by
  set c : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) *
    (‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 +
      ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2) with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => by positivity
  -- Step 1: for every `ρ < 1`, `Σ c_n ρ^{2n+2} ≤ ρ⁻²`
  have step1 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∑ n ∈ Finset.range N, c n * ρ ^ (2 * n + 2) ≤ (ρ ^ 2)⁻¹ := by
    intro ρ hρ0 hρ1
    obtain ⟨K, ε₀, hK, hε₀, hcontain⟩ := hF.containment hρ0 hρ1
    set g2 : ℝ := ‖LiZhongQC.knG2 F‖ with hg2
    have key : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < ρ → ε < 1 / (g2 + 1) →
        ∑ n ∈ Finset.range N, c n * ρ ^ (2 * n + 2) ≤
          (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 + ∑ n ∈ Finset.range N, c n * ε ^ (2 * n + 2) := by
      intro ε hε hε0 hερ hε1
      have hna : ‖LiZhongQC.knG2 F * (ε : ℂ) ^ 2‖ = g2 * ε ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
      have hlt : g2 * ε ^ 2 < 1 := by
        have h1 : ε * (g2 + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hε1
        have hg0 : 0 ≤ g2 := norm_nonneg _
        have : ε < 1 := by nlinarith
        nlinarith [mul_nonneg hg0 hε.le]
      have hineq := gm5_area_ineq hF hφ hinj hdisj (a := LiZhongQC.knG2 F * (ε : ℂ) ^ 2)
        (g := LiZhongQC.knG1 F) (R := ε⁻¹ + K * ε ^ 2) (by rw [hna]; exact hlt) hε hερ hρ1
        (by positivity) (hcontain ε hε hε0) N
      rw [hna] at hineq
      have hpow : (ε⁻¹ + K * ε ^ 2) ^ 2 = (ε ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 := by
        field_simp
        ring
      have hfac : (1 - (g2 * ε ^ 2) ^ 2) * (π * (ε⁻¹ + K * ε ^ 2) ^ 2) ≤ π * (ε⁻¹ + K * ε ^ 2) ^ 2 := by
        have : 0 ≤ (g2 * ε ^ 2) ^ 2 := sq_nonneg _
        have h2 : 0 ≤ π * (ε⁻¹ + K * ε ^ 2) ^ 2 := by positivity
        nlinarith
      have hsplit : π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
          ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 *
            (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) +
          π * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
            ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) =
          π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) := by
        have hS : (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
            ‖iteratedDeriv (n + 1) (fun w => w * LiZhongQC.knG₂ F w) 0 / ((n + 1).factorial : ℂ)‖ ^ 2 *
              (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2))) +
            (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) *
              ‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2))) =
            ∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only [hc]
          ring
        linear_combination π * hS
      rw [hsplit, hpow] at hineq
      have h3 : π * ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) + π * ∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) ≤
          π * ((ε ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4) := by
        rw [hpow] at hfac
        exact hineq.trans hfac
      have h4 : ∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) ≤
          (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 := by
        have h5 : π * (∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2))) ≤
            π * ((ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4) := by linarith
        exact le_of_mul_le_mul_left h5 Real.pi_pos
      have h6 : ∑ n ∈ Finset.range N, c n * (ρ ^ (2 * n + 2) - ε ^ (2 * n + 2)) =
          ∑ n ∈ Finset.range N, c n * ρ ^ (2 * n + 2) - ∑ n ∈ Finset.range N, c n * ε ^ (2 * n + 2) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring
      linarith
    -- let `ε → 0⁺`
    have hlim : Tendsto (fun ε : ℝ => (ρ ^ 2)⁻¹ + 2 * K * ε + K ^ 2 * ε ^ 4 +
        ∑ n ∈ Finset.range N, c n * ε ^ (2 * n + 2)) (𝓝[>] 0)
        (𝓝 ((ρ ^ 2)⁻¹ + 2 * K * 0 + K ^ 2 * 0 ^ 4 + ∑ n ∈ Finset.range N, c n * 0 ^ (2 * n + 2))) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine Continuous.tendsto ?_ 0
      fun_prop
    have hval : (ρ ^ 2)⁻¹ + 2 * K * 0 + K ^ 2 * 0 ^ 4 + ∑ n ∈ Finset.range N, c n * (0 : ℝ) ^ (2 * n + 2) =
        (ρ ^ 2)⁻¹ := by
      simp
    rw [hval] at hlim
    refine ge_of_tendsto hlim ?_
    have hδ : (0 : ℝ) < min (min ε₀ ρ) (1 / (g2 + 1)) := by
      have : 0 < g2 + 1 := by positivity
      positivity
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine key ε hε.1 ?_ ?_ ?_
    · exact lt_of_lt_of_le hε.2 ((min_le_left _ _).trans (min_le_left _ _))
    · exact lt_of_lt_of_le hε.2 ((min_le_left _ _).trans (min_le_right _ _))
    · exact lt_of_lt_of_le hε.2 (min_le_right _ _)
  -- Step 2: let `ρ → 1⁻`
  have hlim2 : Tendsto (fun ρ : ℝ => ∑ n ∈ Finset.range N, c n * ρ ^ (2 * n + 2)) (𝓝[<] 1)
      (𝓝 (∑ n ∈ Finset.range N, c n * 1 ^ (2 * n + 2))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine Continuous.tendsto ?_ 1
    fun_prop
  have hlim3 : Tendsto (fun ρ : ℝ => (ρ ^ 2)⁻¹) (𝓝[<] 1) (𝓝 ((1 ^ 2 : ℝ)⁻¹)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((continuous_id.pow 2).continuousAt.inv₀ (by norm_num)).tendsto
  have := le_of_tendsto_of_tendsto hlim2 hlim3 (by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with ρ hρ
    exact step1 ρ hρ.1 hρ.2)
  simpa using this

/-- Helper (I-5a, T4). Cauchy–Schwarz for the tail of a power series on the disc: if `h` is holomorphic in `𝔻` with
Taylor coefficients `c_n = h⁽ⁿ⁾(0)/n!` and `Σ_{k<N} (m+k) |c_{m+k}|² ≤ S` for all `N`, then for `|z| < 1`
`|h(z) - Σ_{n<m} c_n zⁿ|² ≤ S · log (1/(1 - |z|²))`. -/
theorem gm5_cs {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {m : ℕ} (hm : 1 ≤ m) {S : ℝ}
    (hS : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((m + k : ℕ) : ℝ) *
      ‖iteratedDeriv (m + k) h 0 / ((m + k).factorial : ℂ)‖ ^ 2 ≤ S) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖h z - ∑ n ∈ Finset.range m, (iteratedDeriv n h 0 / (n.factorial : ℂ)) * z ^ n‖ ^ 2 ≤
      S * Real.log (1 / (1 - ‖z‖ ^ 2)) := by
  have hzb : z ∈ ball (0 : ℂ) 1 := by simpa using hz
  have hsum := Complex.hasSum_taylorSeries_on_ball hh hzb
  set c : ℕ → ℂ := fun n => iteratedDeriv n h 0 / (n.factorial : ℂ) with hc
  have hterm : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n h 0 = c n * z ^ n := by
    intro n
    simp only [sub_zero, smul_eq_mul, hc]
    field_simp
  simp only [hterm] at hsum
  have htail : HasSum (fun k => c (k + m) * z ^ (k + m)) (h z - ∑ n ∈ Finset.range m, c n * z ^ n) :=
    (hasSum_nat_add_iff' m).2 hsum
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hS0 : 0 ≤ S := by simpa using hS 0
  set L := Real.log (1 / (1 - r ^ 2)) with hL
  have hx : |r ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hLeq : -Real.log (1 - r ^ 2) = L := by
    rw [hL, one_div, Real.log_inv]
  rw [hLeq] at hlog
  -- partial sums of the majorant
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖c (k + m)‖ * r ^ (k + m) ≤ Real.sqrt (S * L) := by
    intro N
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range N)
      (r := fun k => ‖c (k + m)‖ * r ^ (k + m))
      (f := fun k => ((k + m : ℕ) : ℝ) * ‖c (k + m)‖ ^ 2)
      (g := fun k => (r ^ 2) ^ (k + m) / ((k + m : ℕ) : ℝ))
      (fun k _ => by positivity) (fun k _ => by positivity) (fun k _ => by
        have hkm : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by
          have : 0 < k + m := by omega
          exact_mod_cast this
        have hpw : (r ^ 2) ^ (k + m) = (r ^ (k + m)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        apply le_of_eq
        rw [hpw, mul_pow]
        field_simp)
    have hf : ∑ k ∈ Finset.range N, ((k + m : ℕ) : ℝ) * ‖c (k + m)‖ ^ 2 ≤ S := by
      refine le_trans (le_of_eq ?_) (hS N)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [add_comm k m]
    have hg : ∑ k ∈ Finset.range N, (r ^ 2) ^ (k + m) / ((k + m : ℕ) : ℝ) ≤ L := by
      have h1 : ∑ k ∈ Finset.range N, (r ^ 2) ^ (k + m) / ((k + m : ℕ) : ℝ) =
          ∑ j ∈ Finset.Ico (m - 1) (m - 1 + N), (r ^ 2) ^ (j + 1) / ((j : ℝ) + 1) := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : m - 1 + k + 1 = k + m := by omega
        have h2 : ((m - 1 + k : ℕ) : ℝ) + 1 = ((k + m : ℕ) : ℝ) := by
          rw [← this]; push_cast; ring
        rw [this, h2]
      rw [h1]
      exact sum_le_hasSum _ (fun j _ => by positivity) hlog
    have hSL := mul_le_mul hf hg (Finset.sum_nonneg fun k _ => by positivity) hS0
    have hx0 : ∑ k ∈ Finset.range N, ‖c (k + m)‖ * r ^ (k + m) ≤
        |∑ k ∈ Finset.range N, ‖c (k + m)‖ * r ^ (k + m)| := le_abs_self _
    exact hx0.trans (Real.abs_le_sqrt (hcs.trans hSL))
  have hLnn : 0 ≤ L := hlog.nonneg fun n => by positivity
  have hsm : Summable fun k => ‖c (k + m)‖ * r ^ (k + m) :=
    summable_of_sum_range_le (fun k => by positivity) hpart
  have htsum : ∑' k, ‖c (k + m)‖ * r ^ (k + m) ≤ Real.sqrt (S * L) :=
    hsm.tsum_le_of_sum_range_le hpart
  have hnorm : ‖h z - ∑ n ∈ Finset.range m, c n * z ^ n‖ ≤ Real.sqrt (S * L) := by
    rw [← htail.tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [norm_mul, norm_pow] using hsm
    · simpa [norm_mul, norm_pow] using htsum
  have := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [Real.sq_sqrt (mul_nonneg hS0 hLnn)] at this
  exact this

/-- Helper: the elementary numerical estimates of the proof of Thm 4.2 (with `r = 1 - 4πδ`). -/
theorem gm5_numeric :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ a : ℝ, Real.exp (-(2 * π * δ)) ≤ a →
      4 * π * δ < 1 / 1000 ∧ 0 < 1 - 4 * π * δ ∧ 1 - 4 * π * δ < 1 ∧
      0 < a * (1 - 4 * π * δ) - Real.sqrt (4 * π * δ * Real.log (1 / δ)) ∧
      (2 * (1 / (1 - 4 * π * δ) + Real.sqrt (4 * π * δ * Real.log (1 / δ))) -
          (a * (1 - 4 * π * δ) - Real.sqrt (4 * π * δ * Real.log (1 / δ)))) /
        (a * (1 - 4 * π * δ) - Real.sqrt (4 * π * δ * Real.log (1 / δ))) ≤
        1 + 300 * Real.sqrt (δ * Real.log (1 / δ)) := by
  refine ⟨1 / 100000000, by norm_num, by norm_num, ?_⟩
  intro δ hδ hδ0 a ha
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hπ0 : 0 < π := Real.pi_pos
  have hx : 4 * π * δ < 1 / 1000 := by nlinarith
  have hr0 : 0 < 1 - 4 * π * δ := by linarith
  have hr1 : 1 - 4 * π * δ < 1 := by nlinarith
  refine ⟨hx, hr0, hr1, ?_⟩
  set L : ℝ := Real.log (1 / δ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ hδ]
    nlinarith
  -- `δ L ≤ 2 √δ`
  have hLδ : δ * L ≤ 2 * Real.sqrt δ := by
    have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hss : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ.le
    have h1 : L = 2 * Real.log (1 / Real.sqrt δ) := by
      rw [hL, show (1 / δ) = (1 / Real.sqrt δ) ^ 2 by rw [one_div, one_div, inv_pow, sq, hss], Real.log_pow]
      norm_num
    have h2 : Real.log (1 / Real.sqrt δ) ≤ 1 / Real.sqrt δ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : L ≤ 2 / Real.sqrt δ := by
      rw [h1]
      have : 2 * (1 / Real.sqrt δ - 1) ≤ 2 / Real.sqrt δ := by
        rw [mul_sub, mul_one_div]; linarith
      linarith
    calc δ * L ≤ δ * (2 / Real.sqrt δ) := mul_le_mul_of_nonneg_left h3 hδ.le
      _ = 2 * Real.sqrt δ := by
        rw [mul_div_assoc', div_eq_iff hs.ne']
        nlinarith [hss]
  set t : ℝ := Real.sqrt (δ * L) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hsδ : Real.sqrt δ ≤ 1 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    linarith
  have ht2 : t ≤ 1 / 50 := by
    rw [ht, Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hδt : δ ≤ t := by
    rw [ht]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  set E : ℝ := Real.sqrt (4 * π * δ * L) with hE
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hEt : E ≤ 4 * t := by
    rw [hE, ht]
    have : 4 * π * δ * L = (4 * π) * (δ * L) := by ring
    rw [this, Real.sqrt_mul (by positivity)]
    have : Real.sqrt (4 * π) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  -- bounds on `a`
  have ha1 : 1 - 2 * π * δ ≤ a := by
    have := Real.add_one_le_exp (-(2 * π * δ))
    linarith
  have hm0 : 1 - 6 * π * δ - E ≤ a * (1 - 4 * π * δ) - E := by
    have : (1 - 2 * π * δ) * (1 - 4 * π * δ) ≤ a * (1 - 4 * π * δ) := mul_le_mul_of_nonneg_right ha1 hr0.le
    nlinarith [sq_nonneg (π * δ)]
  have hMr : 1 / (1 - 4 * π * δ) ≤ 1 + 8 * π * δ := by
    rw [div_le_iff₀ hr0]
    nlinarith [sq_nonneg (π * δ)]
  have hm1 : (1 / 2 : ℝ) ≤ a * (1 - 4 * π * δ) - E := by nlinarith
  refine ⟨by linarith, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  have hδ' : 28 * π * δ ≤ 28 * π * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hm1 ht0]

/-- Helper: the estimates on the circle `|z| = 1 - 4πδ` from the area theorem. -/
theorem gm5_core_est {F φ : ℂ → ℂ} (hF : LiZhongQC.knHyp F) (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hinj : InjOn φ (ball (0 : ℂ) 1)) (h0 : φ 0 = 0)
    (hdisj : Disjoint (φ '' ball (0 : ℂ) 1) (LiZhongQC.knPhi F '' (ball (0 : ℂ) 1 \ {0})))
    {δ : ℝ} (hδ : 0 < δ) (hx : 4 * π * δ < 1 / 1000) (hδ1 : δ < 1 / 3)
    (hA : Real.exp (-(2 * π * δ)) ≤ ‖deriv φ 0‖) {z : ℂ} (hz : ‖z‖ = 1 - 4 * π * δ) :
    ‖deriv φ 0‖ ≤ 1 ∧ ‖φ z - deriv φ 0 * z‖ ≤ Real.sqrt (4 * π * δ * Real.log (1 / δ)) ∧
      ‖LiZhongQC.knPhi F z - z⁻¹ - LiZhongQC.knG1 F‖ ≤ Real.sqrt (4 * π * δ * Real.log (1 / δ)) := by
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hπ0 : 0 < π := Real.pi_pos
  have harea := gm5_area_theorem hF hφ hinj h0 hdisj
  set A : ℂ := deriv φ 0 with hAdef
  set h : ℂ → ℂ := fun w => w * LiZhongQC.knG₂ F w with hh
  have hhd : DifferentiableOn ℂ h (ball (0 : ℂ) 1) := fun w hw =>
    (differentiableAt_id.mul (hF.analyticAt_G₂ hw).differentiableAt).differentiableWithinAt
  have hh0 : h 0 = 0 := by simp [hh]
  -- the first coefficient
  have hc1 : iteratedDeriv 1 φ 0 / ((1).factorial : ℂ) = A := by
    rw [iteratedDeriv_one]; simp
    exact hAdef.symm
  have hAle : ‖A‖ ≤ 1 := by
    have := harea 1
    simp only [Finset.range_one, Finset.sum_singleton, zero_add] at this
    rw [hc1] at this
    simp only [Nat.cast_one, one_mul] at this
    nlinarith [sq_nonneg ‖iteratedDeriv 1 h 0 / ((1).factorial : ℂ)‖, norm_nonneg A]
  set s : ℝ := 1 - ‖A‖ ^ 2 with hs
  have hs0 : 0 ≤ s := by nlinarith [norm_nonneg A]
  have hs1 : s ≤ 4 * π * δ := by
    have h1 : 1 - 2 * π * δ ≤ ‖A‖ := by
      have := Real.add_one_le_exp (-(2 * π * δ))
      linarith
    have h2 : 0 ≤ 1 - 2 * π * δ := by nlinarith
    nlinarith [sq_nonneg (π * δ)]
  have hr0 : 0 < 1 - 4 * π * δ := by linarith
  have hr1 : ‖z‖ < 1 := by rw [hz]; nlinarith
  -- tail sums
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), ((n + 1 : ℕ) : ℝ) *
      (‖iteratedDeriv (n + 1) φ 0 / ((n + 1).factorial : ℂ)‖ ^ 2 +
        ‖iteratedDeriv (n + 1) h 0 / ((n + 1).factorial : ℂ)‖ ^ 2) =
      (‖A‖ ^ 2 + ‖iteratedDeriv 1 h 0 / ((1).factorial : ℂ)‖ ^ 2) +
        ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) *
          (‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 +
            ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖ ^ 2) := by
    intro N
    rw [Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    · simp only [zero_add, Nat.cast_one, one_mul, hc1]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [show k + 1 + 1 = 2 + k by omega]
  have hnn : ∀ N : ℕ, 0 ≤ ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) *
          (‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 +
            ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖ ^ 2) := fun N =>
    Finset.sum_nonneg fun k _ => by positivity
  have hS2 : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) *
      ‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 ≤ s := by
    intro N
    have h1 := harea (N + 1)
    rw [hsplit] at h1
    have h2 : ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) * ‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 ≤
        ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) *
          (‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 +
            ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖ ^ 2) :=
      Finset.sum_le_sum fun k _ => by
        have : 0 ≤ ((2 + k : ℕ) : ℝ) := by positivity
        nlinarith [sq_nonneg ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖]
    nlinarith [sq_nonneg ‖iteratedDeriv 1 h 0 / ((1).factorial : ℂ)‖]
  have hS1 : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((1 + k : ℕ) : ℝ) *
      ‖iteratedDeriv (1 + k) h 0 / ((1 + k).factorial : ℂ)‖ ^ 2 ≤ s := by
    intro N
    rcases N with _ | N
    · simpa using hs0
    · have h1 := harea (N + 1)
      rw [hsplit] at h1
      rw [Finset.sum_range_succ']
      have e : ∀ k : ℕ, (1 + (k + 1) : ℕ) = 2 + k := fun k => by omega
      simp only [e, add_zero, Nat.cast_one, one_mul, Nat.factorial_one, Nat.cast_one]
      have h2 : ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) * ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖ ^ 2 ≤
        ∑ k ∈ Finset.range N, ((2 + k : ℕ) : ℝ) *
          (‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖ ^ 2 +
            ‖iteratedDeriv (2 + k) h 0 / ((2 + k).factorial : ℂ)‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => by
          have : 0 ≤ ((2 + k : ℕ) : ℝ) := by positivity
          nlinarith [sq_nonneg ‖iteratedDeriv (2 + k) φ 0 / ((2 + k).factorial : ℂ)‖]
      nlinarith [sq_nonneg ‖iteratedDeriv 1 h 0 / ((1).factorial : ℂ)‖]
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hz2 : δ ≤ 1 - ‖z‖ ^ 2 := by
    have hxp : 0 < 4 * π * δ := by positivity
    have h3 : δ ≤ 4 * π * δ := by nlinarith [Real.pi_gt_three]
    rw [hz]
    nlinarith [mul_pos hxp hxp, mul_lt_mul_of_pos_left hx hxp]
  have hz3 : 0 < 1 - ‖z‖ ^ 2 := by linarith
  have hLz : Real.log (1 / (1 - ‖z‖ ^ 2)) ≤ Real.log (1 / δ) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ hz2)
  have hLnn : 0 ≤ Real.log (1 / (1 - ‖z‖ ^ 2)) :=
    Real.log_nonneg ((one_le_div hz3).2 (by nlinarith [sq_nonneg ‖z‖]))
  have hbound : s * Real.log (1 / (1 - ‖z‖ ^ 2)) ≤ 4 * π * δ * Real.log (1 / δ) :=
    mul_le_mul hs1 hLz hLnn (by positivity)
  refine ⟨hAle, ?_, ?_⟩
  · have h1 := gm5_cs hφ (m := 2) (by norm_num) hS2 hr1
    have e : ∑ n ∈ Finset.range 2, (iteratedDeriv n φ 0 / (n.factorial : ℂ)) * z ^ n = A * z := by
      simp [Finset.sum_range_succ, h0, hAdef]
    rw [e] at h1
    exact Real.le_sqrt_of_sq_le (h1.trans hbound)
  · have h1 := gm5_cs hhd (m := 1) le_rfl hS1 hr1
    have e : ∑ n ∈ Finset.range 1, (iteratedDeriv n h 0 / (n.factorial : ℂ)) * z ^ n = 0 := by
      simp [hh0]
    rw [e, sub_zero] at h1
    have e2 : LiZhongQC.knPhi F z - z⁻¹ - LiZhongQC.knG1 F = h z := by
      rw [LiZhongQC.knPhi, hF.G_expand2 z, hh]
      field_simp
      ring
    rw [e2]
    exact Real.le_sqrt_of_sq_le (h1.trans hbound)

/-- Helper: `J` lies outside `B(0, m)` and inside `B̄(b₀, M)` (the covering arguments of the proof of Thm 4.2). -/
theorem gm5_J_bounds {J : Set ℂ} {φ₁ φ₂ : ℂ → ℂ} {r m M : ℝ} {b₀ : ℂ} (hr : 0 < r) (hr1 : r < 1) (hm : 0 < m)
    (hφ₁ : DifferentiableOn ℂ φ₁ (ball (0 : ℂ) 1)) (hi₁ : InjOn φ₁ (ball (0 : ℂ) 1)) (h₁0 : φ₁ 0 = 0)
    (hmc : ∀ z : ℂ, ‖z‖ = r → m ≤ ‖φ₁ z‖) (hJ1 : ∀ z ∈ J, z ∉ φ₁ '' ball (0 : ℂ) 1)
    (hφ₂ : DifferentiableOn ℂ φ₂ (ball (0 : ℂ) 1)) (hi₂ : InjOn φ₂ (ball (0 : ℂ) 1)) (h₂0 : φ₂ 0 = 0)
    (hMc : ∀ z : ℂ, ‖z‖ = r → ‖(φ₂ z)⁻¹ - b₀‖ ≤ M)
    (hJ2 : ∀ z ∈ J, z ∉ (fun w => (φ₂ w)⁻¹) '' (ball (0 : ℂ) 1 \ {0})) :
    ∀ z ∈ J, m ≤ ‖z‖ ∧ ‖z - b₀‖ ≤ M := by
  have hcb : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hr1
  intro z hz
  constructor
  · by_contra hlt
    have hzm : z ∈ ball (0 : ℂ) m := mem_ball_zero_iff.2 (not_le.1 hlt)
    exact hJ1 z hz (image_mono (ball_subset_ball hr1.le) (gm5_cover_disc hr hm (hφ₁.mono hcb)
      (hi₁.mono (ball_subset_ball hr1.le)) h₁0 hmc hzm))
  · by_contra hlt
    have hne : ∀ w ∈ closedBall (0 : ℂ) r, w ≠ 0 → φ₂ w ≠ 0 := by
      intro w hw hw0 h
      exact hw0 (hi₂ (hcb hw) (mem_ball_self one_pos) (h.trans h₂0.symm))
    set V : Set ℂ := (fun ζ => b₀ + LiZhongQC.knA 0 ζ) '' closedBall (0 : ℂ) M with hV
    obtain ⟨hVo, hVc, hVinf⟩ := gm5_ellipse_compl (a := 0) (by simp) b₀ M
    have hVeq : V = closedBall b₀ M := by
      ext w
      simp only [hV, LiZhongQC.knA_apply, zero_mul, add_zero, mem_image, mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨ζ, hζ, rfl⟩
        simpa using hζ
      · intro hw
        exact ⟨w - b₀, by simpa using hw, by ring⟩
    have hdiff : DifferentiableOn ℂ (fun w => (φ₂ w)⁻¹) (closedBall (0 : ℂ) r \ {0}) := fun w hw =>
      (((hφ₂.differentiableAt (isOpen_ball.mem_nhds (hcb hw.1))).inv (hne w hw.1 hw.2))).differentiableWithinAt
    have hinj : InjOn (fun w => (φ₂ w)⁻¹) (ball (0 : ℂ) r \ {0}) := by
      intro x hx y hy hxy
      have hx0 := hne x (ball_subset_closedBall hx.1) hx.2
      have hy0 := hne y (ball_subset_closedBall hy.1) hy.2
      have : φ₂ x = φ₂ y := inv_injective hxy
      exact hi₂ (hcb (ball_subset_closedBall hx.1)) (hcb (ball_subset_closedBall hy.1)) this
    have hpole : Tendsto (fun w => ‖(φ₂ w)⁻¹‖) (𝓝[≠] (0 : ℂ)) atTop := by
      have hc : ContinuousAt φ₂ 0 := (hφ₂.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).continuousAt
      have h1 : Tendsto (fun w => ‖φ₂ w‖) (𝓝[≠] (0 : ℂ)) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := hc.tendsto.norm
          rw [h₂0, norm_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
            (isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1)) : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ball (0 : ℂ) 1)]
            with w hw hw1
          exact norm_pos_iff.2 fun h => hw (hi₂ hw1 (mem_ball_self one_pos) (h.trans h₂0.symm))
      have := tendsto_inv_nhdsGT_zero.comp h1
      exact this.congr fun w => by simp [Function.comp, norm_inv]
    have hcov : Vᶜ ⊆ (fun w => (φ₂ w)⁻¹) '' (ball (0 : ℂ) r \ {0}) :=
      gm5_cover_pole hr hdiff hinj hpole hVo hVc hVinf (by
        intro w hw hwV
        apply hwV
        rw [hVeq, mem_closedBall, dist_eq_norm]
        exact hMc w hw)
    have hzV : z ∈ Vᶜ := by
      rw [mem_compl_iff, hVeq, mem_closedBall, dist_eq_norm]
      exact not_le.2 (not_le.1 hlt)
    obtain ⟨w, hw, hwz⟩ := hcov hzV
    exact hJ2 z hz ⟨w, ⟨ball_subset_ball hr1.le hw.1, hw.2⟩, hwz⟩

/-- Helper: the ratio `sup_J |z| / inf_J |z|` from the bounds `m ≤ |z|` and `|z - b₀| ≤ M` on `J` and the rays. -/
theorem gm5_ratio {J : Set ℂ} {b₀ : ℂ} {m M : ℝ} (hm : 0 < m) (hJ : ∀ z ∈ J, m ≤ ‖z‖ ∧ ‖z - b₀‖ ≤ M)
    (hray : ∀ v : ℂ, ‖v‖ = 1 → ∃ t : ℝ, 0 < t ∧ ((t : ℂ) * v) ∈ J) :
    sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) ≤ (2 * M - m) / m := by
  obtain ⟨t₁, ht₁, hJne⟩ := hray 1 (by simp)
  have hne : (J).Nonempty := ⟨_, hJne⟩
  have hb : ‖b₀‖ ≤ M - m := by
    by_cases hb0 : b₀ = 0
    · obtain ⟨z₀, hz₀⟩ := hne
      have := hJ z₀ hz₀
      rw [hb0, norm_zero]
      have h2 : m ≤ M := by
        have := this.2
        rw [hb0, sub_zero] at this
        linarith [this, (hJ z₀ hz₀).1]
      linarith
    · have hn : 0 < ‖b₀‖ := norm_pos_iff.2 hb0
      set v : ℂ := -(b₀ / (‖b₀‖ : ℂ)) with hv
      have hv1 : ‖v‖ = 1 := by
        rw [hv, norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']
      obtain ⟨t, ht, htJ⟩ := hray v hv1
      have h1 : ‖(t : ℂ) * v‖ = t := by rw [norm_mul, hv1, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
      have h2 : ‖(t : ℂ) * v - b₀‖ = t + ‖b₀‖ := by
        have : (t : ℂ) * v - b₀ = -(((t / ‖b₀‖ + 1 : ℝ) : ℂ) * b₀) := by
          rw [hv]
          have : (‖b₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
          push_cast
          field_simp
          ring
        rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        field_simp
      obtain ⟨hmt, hMt⟩ := hJ _ htJ
      rw [h1] at hmt
      rw [h2] at hMt
      linarith
  have hsup : sSup ((fun z : ℂ => ‖z‖) '' J) ≤ 2 * M - m := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨z, hz, rfl⟩
    have := (hJ z hz).2
    have h3 : ‖z‖ ≤ ‖z - b₀‖ + ‖b₀‖ := by
      calc ‖z‖ = ‖(z - b₀) + b₀‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hinf : m ≤ sInf ((fun z : ℂ => ‖z‖) '' J) :=
    le_csInf (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact (hJ z hz).1)
  have hMm : 0 ≤ 2 * M - m := by
    obtain ⟨z₀, hz₀⟩ := hne
    have := hJ z₀ hz₀
    have h3 : ‖z₀‖ ≤ ‖z₀ - b₀‖ + ‖b₀‖ := by
      calc ‖z₀‖ = ‖(z₀ - b₀) + b₀‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [this.1, this.2]
  exact div_le_div₀ hMm hsup hm hinf

/-- Helper (I-5a, T6, the analytic core of Theorem 4.2). Absolute constants `δ₀ < 1`, `C`; `J` a compact set of
`ℂ`; `φ₁`, `φ₂` holomorphic and injective in `𝔻` with `φ_i(0) = 0`; `J` misses `φ₁(𝔻)` and `1/φ₂(𝔻 \ {0})`; the
two images are disjoint; every ray from `0` meets `J`; and `(1/2π)(log |φ₁'(0)| + log |φ₂'(0)|) ≥ -δ`
(the reduced moduli of `G₁` and `1/G₂`). Then `sup_J |z| / inf_J |z| ≤ 1 + C √(δ log (1/δ))`. -/
theorem gm5_core :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∃ C : ℝ, ∀ (J : Set ℂ) (φ₁ φ₂ : ℂ → ℂ), IsCompact J →
      DifferentiableOn ℂ φ₁ (ball (0 : ℂ) 1) → InjOn φ₁ (ball (0 : ℂ) 1) → φ₁ 0 = 0 →
      DifferentiableOn ℂ φ₂ (ball (0 : ℂ) 1) → InjOn φ₂ (ball (0 : ℂ) 1) → φ₂ 0 = 0 →
      (∀ z ∈ J, z ∉ φ₁ '' ball (0 : ℂ) 1) → (∀ z ∈ J, z ∉ (fun w => (φ₂ w)⁻¹) '' (ball (0 : ℂ) 1 \ {0})) →
      Disjoint (φ₁ '' ball (0 : ℂ) 1) ((fun w => (φ₂ w)⁻¹) '' (ball (0 : ℂ) 1 \ {0})) →
      (∀ v : ℂ, ‖v‖ = 1 → ∃ t : ℝ, 0 < t ∧ ((t : ℂ) * v) ∈ J) →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        -δ ≤ 1 / (2 * π) * Real.log ‖deriv φ₁ 0‖ + 1 / (2 * π) * Real.log ‖deriv φ₂ 0‖ →
          sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) ≤
            1 + C * Real.sqrt (δ * Real.log (1 / δ)) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hnum⟩ := gm5_numeric
  refine ⟨min δ₀ (1 / 4), lt_min hδ₀ (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), 300, ?_⟩
  intro J φ₁ φ₂ hJc hφ₁ hi₁ h₁0 hφ₂ hi₂ h₂0 hJ1 hJ2 hdisj hray δ hδ hδδ₀ hmod
  have hδ₀' : δ < δ₀ := lt_of_lt_of_le hδδ₀ (min_le_left _ _)
  have hδ4 : δ < 1 / 4 := lt_of_lt_of_le hδδ₀ (min_le_right _ _)
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hp : deriv φ₂ 0 ≠ 0 := RMT.deriv_ne_zero_of_injOn isOpen_ball hφ₂ hi₂ h0mem
  have hq : deriv φ₁ 0 ≠ 0 := RMT.deriv_ne_zero_of_injOn isOpen_ball hφ₁ hi₁ h0mem
  set p : ℂ := deriv φ₂ 0 with hpdef
  set q : ℂ := deriv φ₁ 0 with hqdef
  -- the normalisations
  set F : ℂ → ℂ := fun w => φ₂ w / p with hFdef
  have hF : LiZhongQC.knHyp F := by
    refine ⟨hφ₂.div_const p, ?_, by simp [hFdef, h₂0], ?_⟩
    · intro x hx y hy hxy
      exact hi₂ hx hy (by simpa [hFdef, div_left_inj' hp] using hxy)
    · simp only [hFdef]
      rw [deriv_div_const]
      exact div_self hp
  set φ : ℂ → ℂ := fun z => p * φ₁ z with hφdef
  have hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := hφ₁.const_mul p
  have hφi : InjOn φ (ball (0 : ℂ) 1) := fun x hx y hy hxy =>
    hi₁ hx hy (mul_left_cancel₀ hp hxy)
  have hφ0 : φ 0 = 0 := by simp [hφdef, h₁0]
  have hPhi : ∀ w, w ≠ 0 → w ∈ ball (0 : ℂ) 1 → LiZhongQC.knPhi F w = p * (φ₂ w)⁻¹ := by
    intro w hw0 hw
    rw [hF.phi_eq w, hFdef]
    simp only
    rw [inv_div]
    ring
  have hdisj' : Disjoint (φ '' ball (0 : ℂ) 1) (LiZhongQC.knPhi F '' (ball (0 : ℂ) 1 \ {0})) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, ⟨hw, hw0⟩, hwz⟩
    rw [hPhi w hw0 hw] at hwz
    have : φ₁ z = (φ₂ w)⁻¹ := mul_left_cancel₀ hp (by simpa [hφdef] using hwz.symm)
    exact Set.disjoint_left.1 hdisj (mem_image_of_mem φ₁ hz) ⟨w, ⟨hw, hw0⟩, this.symm⟩
  have hder : deriv φ 0 = p * q := by
    simp only [hφdef]
    rw [deriv_const_mul _ (hφ₁.differentiableAt (isOpen_ball.mem_nhds h0mem))]
  -- the modulus hypothesis
  have hApos : 0 < ‖deriv φ 0‖ := by
    rw [hder]; exact norm_pos_iff.2 (mul_ne_zero hp hq)
  have hlogA : -(2 * π * δ) ≤ Real.log ‖deriv φ 0‖ := by
    rw [hder, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hp) (norm_ne_zero_iff.2 hq)]
    have h2π : 0 < 2 * π := by positivity
    have : -δ * (2 * π) ≤ (1 / (2 * π) * Real.log ‖q‖ + 1 / (2 * π) * Real.log ‖p‖) * (2 * π) :=
      mul_le_mul_of_nonneg_right hmod h2π.le
    have e : (1 / (2 * π) * Real.log ‖q‖ + 1 / (2 * π) * Real.log ‖p‖) * (2 * π) =
        Real.log ‖q‖ + Real.log ‖p‖ := by field_simp
    rw [e] at this
    linarith
  have hexp : Real.exp (-(2 * π * δ)) ≤ ‖deriv φ 0‖ := (Real.le_log_iff_exp_le hApos).1 hlogA
  -- numeric facts
  obtain ⟨hx, hr0, hr1, hmpos, hratio⟩ := hnum δ hδ hδ₀' ‖deriv φ 0‖ hexp
  have hδ3 : δ < 1 / 3 := by linarith
  set E : ℝ := Real.sqrt (4 * π * δ * Real.log (1 / δ)) with hEdef
  set r : ℝ := 1 - 4 * π * δ with hrdef
  set a : ℝ := ‖deriv φ 0‖ with hadef
  have hβ : 0 < ‖p‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hp)
  set m : ℝ := ‖p‖⁻¹ * (a * r - E) with hm
  set M : ℝ := ‖p‖⁻¹ * (1 / r + E) with hM
  set b₀ : ℂ := p⁻¹ * LiZhongQC.knG1 F with hb₀
  have hmpos' : 0 < m := mul_pos hβ hmpos
  have hmc : ∀ z : ℂ, ‖z‖ = r → m ≤ ‖φ₁ z‖ := by
    intro z hz
    obtain ⟨_, h2, _⟩ := gm5_core_est hF hφd hφi hφ0 hdisj' hδ hx hδ3 hexp hz
    have h3 : a * r - E ≤ ‖φ z‖ := by
      have : ‖deriv φ 0 * z‖ - ‖φ z - deriv φ 0 * z‖ ≤ ‖φ z‖ := by
        have := norm_sub_norm_le (deriv φ 0 * z) (deriv φ 0 * z - φ z)
        rw [sub_sub_cancel, norm_sub_rev] at this
        linarith
      rw [norm_mul, hz] at this
      linarith
    have h4 : φ₁ z = p⁻¹ * φ z := by
      simp only [hφdef]; field_simp
    rw [h4, norm_mul, norm_inv]
    exact mul_le_mul_of_nonneg_left h3 hβ.le
  have hMc : ∀ z : ℂ, ‖z‖ = r → ‖(φ₂ z)⁻¹ - b₀‖ ≤ M := by
    intro z hz
    obtain ⟨_, _, h3⟩ := gm5_core_est hF hφd hφi hφ0 hdisj' hδ hx hδ3 hexp hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
    have hz1 : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hz]; linarith
    have e : (φ₂ z)⁻¹ - b₀ = p⁻¹ * (z⁻¹ + (LiZhongQC.knPhi F z - z⁻¹ - LiZhongQC.knG1 F)) := by
      rw [hPhi z hz0 hz1, hb₀]
      field_simp
      ring
    rw [e, norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hβ.le
    rw [norm_inv, hz, one_div]
    exact add_le_add le_rfl h3
  have hJb := gm5_J_bounds (r := r) (m := m) (M := M) (b₀ := b₀) hr0 hr1 hmpos' hφ₁ hi₁ h₁0 hmc hJ1 hφ₂ hi₂ h₂0
    hMc hJ2
  have hrat := gm5_ratio hmpos' hJb hray
  refine hrat.trans ?_
  have e2 : (2 * M - m) / m = (2 * (1 / r + E) - (a * r - E)) / (a * r - E) := by
    rw [hM, hm, show 2 * (‖p‖⁻¹ * (1 / r + E)) - ‖p‖⁻¹ * (a * r - E) =
      ‖p‖⁻¹ * (2 * (1 / r + E) - (a * r - E)) by ring, mul_div_mul_left _ _ hβ.ne']
  rw [e2]
  exact hratio

/-- **Theorem 4.2** (Teichmüller's special Modulsatz, Ch. V §4; cited at P1:7196, 7248, 7268). Let `J` be a continuum
and let `G₁` and `G₂` be disjoint components of `ℂ* \ J` such that `0 ∈ G₁` and `∞ ∈ G₂`. If (4.5)
`M(G₁) + M(G₂) ≥ −δ` and if `δ > 0` is sufficiently small, then there is a `C < ∞` independent of `J` and `δ` such
that (4.6) `sup_J |z| / inf_J |z| ≤ 1 + C √(δ log(1/δ))`.
Modelling: `J ⊆ ℂ` (since `∞ ∈ G₂`) is compact and connected; `G₁`, `G₂` are components of `ℂ* \ J`; `M(G₁)` is
`reducedModulus` of the plane domain `G₁` and `M(G₂)` is `reducedModulusInf G₂` (the components of the complement of
a continuum are simply connected, and `J` has more than one point because `G₁ ≠ G₂`, so both are values of the
definition, not junk); `δ₀` and `C` are absolute constants (module docstring); `0 ∈ G₁` gives `inf_J |z| > 0`. The
formulas (4.5) and (4.6) were checked against the equation images. -/
theorem thm5_4_2 :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∃ C : ℝ, ∀ (J : Set ℂ) (G₁ G₂ : Set ExtPlane), IsCompact J → IsConnected J →
      (∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₁) →
      (∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₂) → Disjoint G₁ G₂ →
      ((0 : ℂ) : ExtPlane) ∈ G₁ → extInf ∈ G₂ → ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        -δ ≤ reducedModulus (finitePart G₁) + reducedModulusInf G₂ →
          sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) ≤
            1 + C * Real.sqrt (δ * Real.log (1 / δ)) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, C, hcore⟩ := gm5_core
  refine ⟨δ₀, hδ₀, hδ₀1, C, ?_⟩
  intro J G₁ G₂ hJc hJ h1 h2 hd h0 hinf δ hδ hδδ₀ hmod
  obtain ⟨φ₁, φ₂, hc1, h10, hc2, h20⟩ := gm5_exists_maps hJc hJ h1 h2 hd h0 hinf
  have hm1 := gm5_reducedModulus_le hc1 h10
  have hm2 := gm5_reducedModulus_le hc2 h20
  have hG1 : G₁ ⊆ (toExt J)ᶜ := by
    obtain ⟨z, _, rfl⟩ := h1
    exact connectedComponentIn_subset _ _
  have hG2 : G₂ ⊆ (toExt J)ᶜ := by
    obtain ⟨z, _, rfl⟩ := h2
    exact connectedComponentIn_subset _ _
  have hchart : ∀ ζ : ℂ, ζ ≠ 0 → extChartInv extInf ζ = ((ζ⁻¹ : ℂ) : ExtPlane) := by
    intro ζ hζ
    show (if ζ = 0 then extInf else ((ζ⁻¹ : ℂ) : ExtPlane)) = _
    simp only [hζ, ↓reduceIte]
  have him1 : φ₁ '' ball (0 : ℂ) 1 = finitePart G₁ := hc1.2.2
  have him2 : φ₂ '' ball (0 : ℂ) 1 = {w : ℂ | extChartInv extInf w ∈ G₂} := hc2.2.2
  have hψ : ∀ x ∈ (fun w => (φ₂ w)⁻¹) '' (ball (0 : ℂ) 1 \ {0}), ((x : ℂ) : ExtPlane) ∈ G₂ := by
    rintro _ ⟨w, ⟨hw, hw0⟩, rfl⟩
    have hne : φ₂ w ≠ 0 := by
      intro h
      exact hw0 (hc2.2.1 hw (mem_ball_self one_pos)
        (h.trans h20.symm))
    have hmem : φ₂ w ∈ {w : ℂ | extChartInv extInf w ∈ G₂} := him2 ▸ mem_image_of_mem φ₂ hw
    have hmem' : extChartInv extInf (φ₂ w) ∈ G₂ := hmem
    rw [hchart _ hne] at hmem'
    exact hmem'
  refine hcore J φ₁ φ₂ hJc hc1.1 hc1.2.1 h10 hc2.1 hc2.2.1 h20 ?_ ?_ ?_
    (fun v hv => gm5_ray hJc h1 h2 hd h0 hinf hv) δ hδ hδδ₀ ?_
  · intro z hz hzim
    rw [him1] at hzim
    exact hG1 hzim ⟨z, hz, rfl⟩
  · intro z hz hzim
    exact hG2 (hψ z hzim) ⟨z, hz, rfl⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    rw [him1] at hx
    exact Set.disjoint_left.1 hd hx (hψ x hx')
  · have hm2' : reducedModulusInf G₂ ≤ 1 / (2 * π) * Real.log ‖deriv φ₂ 0‖ := hm2
    linarith

/-- Helper (Stage B2): the inversion maps an annulus into the inverted annulus. -/
theorem gm5_inv_annulus {a b : ℝ} (ha : 0 < a) {Ω : Set ℂ} (h : Ω ⊆ annulus a b) :
    (fun z : ℂ => z⁻¹) '' Ω ⊆ annulus b⁻¹ a⁻¹ := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨h1, h2⟩ := h hz
  have hz0 : 0 < ‖z‖ := ha.trans h1
  rw [annulus, mem_ofPred_eq, norm_inv]
  exact ⟨inv_strictAnti₀ hz0 h2, inv_strictAnti₀ ha h1⟩

/-- Helper (Stage B2): differentiability at `0` in the form used: `|φ(w)| ≤ (1 + ε) |φ'(0)| |w|` for small `w`. -/
theorem gm5_phi_small {φ : ℂ → ℂ} (hd : DifferentiableAt ℂ φ 0) (h0 : φ 0 = 0) (hne : deriv φ 0 ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ w : ℂ, ‖w‖ ≤ δ₁ → ‖φ w‖ ≤ (1 + ε) * ‖deriv φ 0‖ * ‖w‖ := by
  have hc : 0 < ‖deriv φ 0‖ := norm_pos_iff.2 hne
  have hlo := hd.hasDerivAt.isLittleO.def (c := ε * ‖deriv φ 0‖) (by positivity)
  rw [Metric.eventually_nhds_iff_ball] at hlo
  obtain ⟨δ, hδ, hball⟩ := hlo
  refine ⟨δ / 2, by positivity, fun w hw => ?_⟩
  have hwb : w ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff]; linarith
  have h1 := hball w hwb
  simp only [sub_zero, h0, smul_eq_mul] at h1
  calc ‖φ w‖ = ‖(φ w - w * deriv φ 0) + w * deriv φ 0‖ := by ring_nf
    _ ≤ ‖φ w - w * deriv φ 0‖ + ‖w * deriv φ 0‖ := norm_add_le _ _
    _ ≤ ε * ‖deriv φ 0‖ * ‖w‖ + ‖w‖ * ‖deriv φ 0‖ := by
        rw [norm_mul]
        gcongr
    _ = (1 + ε) * ‖deriv φ 0‖ * ‖w‖ := by ring

/-- Helper (Stage B2; Schwarz). Two conformal maps `φ, φ' : 𝔻 → G` fixing `0` satisfy `|φ'(0)| ≤ |φ(0)|`. -/
theorem gm5_deriv_le {G : Set ℂ} {φ φ' : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc G) (h0 : φ 0 = 0)
    (hφ' : IsConformalOnto φ' unitDisc G) (h0' : φ' 0 = 0) : ‖deriv φ' 0‖ ≤ ‖deriv φ 0‖ := by
  obtain ⟨hdiff, hinj, himg⟩ := hφ
  obtain ⟨hd', hi', hm'⟩ := hφ'
  have hU : IsOpen (unitDisc) := isOpen_ball
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨hopen, hinvd⟩ := RMT.differentiableOn_invFunOn_of_injOn hU hdiff hinj
  set g := Function.invFunOn φ unitDisc ∘ φ' with hg
  have hmaps : MapsTo φ' unitDisc (φ '' unitDisc) := fun z hz => himg ▸ hm' ▸ mem_image_of_mem φ' hz
  have hgφ : ∀ z ∈ unitDisc, φ (g z) = φ' z := by
    intro z hz
    obtain ⟨x, hx, hxe⟩ := hmaps hz
    exact Function.invFunOn_eq (f := φ) (s := unitDisc) (b := φ' z) ⟨x, hx, hxe⟩
  have hgmem : ∀ z ∈ unitDisc, g z ∈ unitDisc := by
    intro z hz
    obtain ⟨x, hx, hxe⟩ := hmaps hz
    exact Function.invFunOn_mem (f := φ) (s := unitDisc) (b := φ' z) ⟨x, hx, hxe⟩
  have hg0 : g 0 = 0 := by
    have this : φ (g 0) = φ 0 := by rw [hgφ 0 h0mem, h0', h0]
    exact hinj (hgmem 0 h0mem) h0mem this
  have hgd : DifferentiableOn ℂ g unitDisc := hinvd.comp hd' hmaps
  have hmapsb : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
    intro z hz
    rw [hg0]
    exact ball_subset_closedBall (hgmem z hz)
  have hsch : ‖deriv g 0‖ ≤ 1 := by
    have := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hmapsb one_pos
    simpa using this
  have hev : φ' =ᶠ[𝓝 0] φ ∘ g := by
    filter_upwards [hU.mem_nhds h0mem] with z hz
    exact (hgφ z hz).symm
  have hφd : DifferentiableAt ℂ φ (g 0) := by
    rw [hg0]; exact hdiff.differentiableAt (hU.mem_nhds h0mem)
  have hgda : DifferentiableAt ℂ g 0 := hgd.differentiableAt (hU.mem_nhds h0mem)
  have hder : deriv φ' 0 = deriv φ 0 * deriv g 0 := by
    rw [hev.deriv_eq]
    have := deriv_comp (x := (0 : ℂ)) hφd hgda
    simpa [Function.comp, hg0] using this
  rw [hder, norm_mul]
  calc ‖deriv φ 0‖ * ‖deriv g 0‖ ≤ ‖deriv φ 0‖ * 1 := mul_le_mul_of_nonneg_left hsch (norm_nonneg _)
    _ = _ := mul_one _

/-- Helper (Stage B2): the reduced modulus of a simply connected plane domain is the value `(1/2π) log |φ'(0)|` of
*any* conformal map `φ : 𝔻 → G` with `φ(0) = 0` (the supremum in `reducedModulus` is over a single value: Schwarz). -/
theorem gm5_red_eq {G : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc G) (h0 : φ 0 = 0) :
    reducedModulus G = 1 / (2 * π) * Real.log ‖deriv φ 0‖ := by
  have hS : {m : ℝ | ∃ φ : ℂ → ℂ, IsConformalOnto φ unitDisc G ∧ φ 0 = 0 ∧
      m = 1 / (2 * π) * Real.log ‖deriv φ 0‖} = {1 / (2 * π) * Real.log ‖deriv φ 0‖} := by
    ext m
    constructor
    · rintro ⟨φ', hφ', h0', rfl⟩
      have h1 := gm5_deriv_le hφ h0 hφ' h0'
      have h2 := gm5_deriv_le hφ' h0' hφ h0
      rw [mem_singleton_iff, le_antisymm h1 h2]
    · rintro rfl
      exact ⟨φ, hφ, h0, rfl⟩
  rw [reducedModulus, hS, csSup_singleton]

/-- Helper (Stage B2): in a configuration, the facts about `B̄(0,R₁) ∪ Ω₁` next to the circle `|z| = R₁`. -/
theorem gm5_conf_side1 {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    IsOpen (closedBall (0 : ℂ) R₁ ∪ Ω₁) ∧ IsClosed (closedBall (0 : ℂ) R₁ ∪ Ω₁ ∪ J) ∧
      IsPreconnected (closedBall (0 : ℂ) R₁ ∪ Ω₁) ∧ Disjoint (closedBall (0 : ℂ) R₁ ∪ Ω₁) J := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hJc : IsCompact J := hconf.2.2.1
  have hJA : J ⊆ annulus R₁ R₂ := hconf.2.2.2.2.1
  obtain ⟨hΩo, hΩc, hΩA⟩ := gm5_conf_comp hconf (Or.inl rfl)
  have hsph : sphere (0 : ℂ) R₁ ⊆ frontier Ω₁ := hconf.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c, c', hcc, -, hfar, hfr, hnear⟩ := gm5_conf_facts hconf (Or.inl rfl)
  have hp0 : ((R₁ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₁ := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR1.le]
  have hc : c = R₁ := by
    rcases hcc with ⟨h, -⟩ | ⟨-, rfl⟩
    · exact h
    · exact absurd (frontier_subset_closure (hsph hp0)) (fun h => Set.disjoint_left.1 hfar h hp0)
  subst hc
  have hJdisj : Disjoint (closedBall (0 : ℂ) c ∪ Ω₁) J := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) hzJ
    · exact absurd (hJA hzJ).1 (not_lt.2 (mem_closedBall_zero_iff.1 hz))
    · have : Ω₁ ⊆ annulus c R₂ \ J := by
        obtain ⟨z₀, hz₀, hcomp⟩ := hconf.2.2.2.2.2.1
        rw [← hcomp]
        exact connectedComponentIn_subset _ _
      exact (this hz).2 hzJ
  refine ⟨?_, ?_, ?_, hJdisj⟩
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    rcases hp with hp | hp
    · by_cases hpn : ‖p‖ < c
      · exact Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hpn))
          (fun z hz => Or.inl (ball_subset_closedBall hz))
      · have hpc : ‖p‖ = c := le_antisymm (mem_closedBall_zero_iff.1 hp) (not_lt.1 hpn)
        obtain ⟨ε, hε, hεΩ⟩ := hnear p (mem_sphere_zero_iff_norm.2 hpc)
        refine Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self (lt_min hε (sub_pos.2 hR12)))
          : ball p (min ε (R₂ - c)) ∈ 𝓝 p) (fun z hz => ?_)
        by_cases hzc : ‖z‖ ≤ c
        · exact Or.inl (mem_closedBall_zero_iff.2 hzc)
        · refine Or.inr (hεΩ ⟨mem_ball.2 (lt_of_lt_of_le hz (min_le_left _ _)), not_le.1 hzc, ?_⟩)
          have h1 := (mem_ball.1 hz).trans_le (min_le_right _ _)
          have h2 : ‖z‖ ≤ ‖p‖ + dist z p := by
            have := norm_le_norm_add_norm_sub' z p
            rw [dist_eq_norm]
            linarith
          linarith
    · exact Filter.mem_of_superset (hΩo.mem_nhds hp) (fun z hz => Or.inr hz)
  · refine isClosed_of_closure_subset ?_
    rw [closure_union, closure_union, isClosed_closedBall.closure_eq, hJc.isClosed.closure_eq]
    rintro z ((hz | hz) | hz)
    · exact Or.inl (Or.inl hz)
    · have hcl := closure_eq_interior_union_frontier Ω₁
      rw [hΩo.interior_eq] at hcl
      rw [hcl] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · rcases hfr hz with h | h
        · exact Or.inl (Or.inl (sphere_subset_closedBall h))
        · exact Or.inr h
    · exact Or.inr hz
  · have hC : IsPreconnected (Ω₁ ∪ sphere (0 : ℂ) c) :=
      hΩc.isPreconnected.subset_closure subset_union_left (by
        intro z hz
        rcases hz with hz | hz
        · exact subset_closure hz
        · exact frontier_subset_closure (hsph hz))
    have hB : IsPreconnected (closedBall (0 : ℂ) c) := (convex_closedBall _ _).isPreconnected
    have := hB.union ((c : ℝ) : ℂ) (sphere_subset_closedBall hp0) (Or.inr hp0 |> fun h => by exact h) hC
    convert this using 1
    ext z
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl (sphere_subset_closedBall h)

/-- Helper (Stage B2): in a configuration, the facts about `Ω₂ ∪ {R₂ ≤ |z|}` next to the circle `|z| = R₂`. -/
theorem gm5_conf_side2 {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    IsOpen (Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖}) ∧ IsClosed (Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖} ∪ J) ∧
      IsPreconnected (toExt (Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖}) ∪ {extInf}) ∧ Disjoint (Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖}) J ∧
      Disjoint (closedBall (0 : ℂ) R₁ ∪ Ω₁) (Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖}) := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hR2 : 0 < R₂ := hR1.trans hR12
  have hJc : IsCompact J := hconf.2.2.1
  have hJA : J ⊆ annulus R₁ R₂ := hconf.2.2.2.2.1
  obtain ⟨hΩo, hΩc, hΩA⟩ := gm5_conf_comp hconf (Or.inr rfl)
  obtain ⟨hΩ₁o, -, hΩ₁A⟩ := gm5_conf_comp hconf (Or.inl rfl)
  have hdisj12 : Disjoint Ω₁ Ω₂ := hconf.2.2.2.2.2.2.2.1
  have hsph : sphere (0 : ℂ) R₂ ⊆ frontier Ω₂ := hconf.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨c, c', hcc, -, hfar, hfr, hnear⟩ := gm5_conf_facts hconf (Or.inr rfl)
  have hp0 : ((R₂ : ℝ) : ℂ) ∈ sphere (0 : ℂ) R₂ := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR2.le]
  have hc : c = R₂ := by
    rcases hcc with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact absurd (frontier_subset_closure (hsph hp0)) (fun h => Set.disjoint_left.1 hfar h hp0)
    · exact h
  subst hc
  have hΩ₂J : Ω₂ ⊆ annulus R₁ c \ J := by
    obtain ⟨z₀, hz₀, hcomp⟩ := hconf.2.2.2.2.2.2.1
    rw [← hcomp]
    exact connectedComponentIn_subset _ _
  have hJdisj : Disjoint (Ω₂ ∪ {z : ℂ | c ≤ ‖z‖}) J := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) hzJ
    · exact (hΩ₂J hz).2 hzJ
    · exact absurd (hJA hzJ).2 (not_lt.2 hz)
  refine ⟨?_, ?_, ?_, hJdisj, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    rcases hp with hp | hp
    · exact Filter.mem_of_superset (hΩo.mem_nhds hp) (fun z hz => Or.inl hz)
    · by_cases hpn : c < ‖p‖
      · exact Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hpn)
          (fun z hz => Or.inr (show c ≤ ‖z‖ from le_of_lt hz))
      · have hpc : ‖p‖ = c := le_antisymm (not_lt.1 hpn) hp
        obtain ⟨ε, hε, hεΩ⟩ := hnear p (mem_sphere_zero_iff_norm.2 hpc)
        refine Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self (lt_min hε (sub_pos.2 hR12)))
          : ball p (min ε (c - R₁)) ∈ 𝓝 p) (fun z hz => ?_)
        by_cases hzc : c ≤ ‖z‖
        · exact Or.inr hzc
        · refine Or.inl (hεΩ ⟨mem_ball.2 (lt_of_lt_of_le hz (min_le_left _ _)), ?_, not_le.1 hzc⟩)
          have h1 := (mem_ball.1 hz).trans_le (min_le_right _ _)
          have h2 : ‖p‖ ≤ ‖z‖ + dist z p := by
            have := norm_le_norm_add_norm_sub' p z
            rw [dist_comm, dist_eq_norm] at *
            rw [norm_sub_rev] at this
            linarith [dist_eq_norm z p, norm_sub_rev z p]
          linarith
  · refine isClosed_of_closure_subset ?_
    rw [closure_union, closure_union, (isClosed_le continuous_const continuous_norm).closure_eq,
      hJc.isClosed.closure_eq]
    rintro z ((hz | hz) | hz)
    · have hcl := closure_eq_interior_union_frontier Ω₂
      rw [hΩo.interior_eq] at hcl
      rw [hcl] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · rcases hfr hz with h | h
        · exact Or.inl (Or.inr (le_of_eq (mem_sphere_zero_iff_norm.1 h).symm))
        · exact Or.inr h
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  · have hO := gm5_outer_conn hR2
    have hC : IsPreconnected (toExt Ω₂ ∪ toExt (sphere (0 : ℂ) c)) := by
      refine (hΩc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).subset_closure
        (s := toExt Ω₂) subset_union_left ?_
      rintro _ (hz | ⟨z, hz, rfl⟩)
      · exact subset_closure hz
      · exact image_closure_subset_closure_image OnePoint.continuous_coe
          ⟨z, frontier_subset_closure (hsph hz), rfl⟩
    have hp1 : ((c : ℝ) : ℂ) ∈ {z : ℂ | c ≤ ‖z‖} := by
      show c ≤ ‖((c : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_of_nonneg hR2.le]
    have hU := hC.union (((c : ℝ) : ℂ) : ExtPlane) (Or.inr ⟨_, hp0, rfl⟩)
      (Or.inl ⟨_, hp1, rfl⟩) hO
    convert hU using 1
    ext x
    simp only [toExt, image_union, mem_union]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro ((h | ⟨z, hz, rfl⟩) | (h | h))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨z, le_of_eq (mem_sphere_zero_iff_norm.1 hz).symm, rfl⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact absurd (hΩA hz').1 (not_lt.2 (mem_closedBall_zero_iff.1 hz))
    · exact absurd (show c ≤ ‖z‖ from hz') (not_le.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hR12))
    · exact Set.disjoint_left.1 hdisj12 hz hz'
    · exact absurd (hΩ₁A hz).2 (not_lt.2 (show c ≤ ‖z‖ from hz'))

/-- Helper (Stage B2): a preconnected open piece `G` of `K` whose complement in `K` is open is a component. -/
theorem gm5_comp_of_clopen {K G : Set ExtPlane} (hG : IsPreconnected G) (hGK : G ⊆ K) (hGo : IsOpen G)
    (hH : IsOpen (K \ G)) {z : ExtPlane} (hz : z ∈ G) : connectedComponentIn K z = G := by
  refine le_antisymm ?_ (hG.subset_connectedComponentIn hz hGK)
  have hsub : connectedComponentIn K z ⊆ G ∪ (K \ G) := fun x hx =>
    by_cases (fun h : x ∈ G => Or.inl h) (fun h => Or.inr ⟨connectedComponentIn_subset _ _ hx, h⟩) |> fun f => f
  rcases isPreconnected_connectedComponentIn.subset_or_subset hGo hH (Set.disjoint_sdiff_right) hsub with h | h
  · exact h
  · exact absurd (h (mem_connectedComponentIn (hGK hz))) (fun hh => hh.2 hz)

/-- Helper (Stage B2; topology of the configuration of Theorem 4.1). The component `G₁` of `ℂ* \ J` through `0` is
`B̄(0, R₁) ∪ Ω₁`, and the chart image at `∞` of the component `G₂` through `∞` is `B̄(0, 1/R₂) ∪ (1/Ω₂)`. -/
theorem gm5_conf_G {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    ∃ G₁ G₂ : Set ExtPlane,
      (∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₁) ∧
      (∃ z ∈ (toExt J)ᶜ, connectedComponentIn (toExt J)ᶜ z = G₂) ∧ Disjoint G₁ G₂ ∧
      ((0 : ℂ) : ExtPlane) ∈ G₁ ∧ extInf ∈ G₂ ∧ finitePart G₁ = closedBall 0 R₁ ∪ Ω₁ ∧
      {w : ℂ | extChartInv extInf w ∈ G₂} = closedBall 0 R₂⁻¹ ∪ (fun z : ℂ => z⁻¹) '' Ω₂ := by
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hR2 : 0 < R₂ := hR1.trans hR12
  have hJc : IsCompact J := hconf.2.2.1
  obtain ⟨hΩ₁o, -, hΩ₁A⟩ := gm5_conf_comp hconf (Or.inl rfl)
  obtain ⟨hΩ₂o, -, hΩ₂A⟩ := gm5_conf_comp hconf (Or.inr rfl)
  obtain ⟨ho1, hcl1, hpc1, hdJ1⟩ := gm5_conf_side1 hconf
  obtain ⟨ho2, hcl2, hpc2, hdJ2, hd12⟩ := gm5_conf_side2 hconf
  set T₁ : Set ℂ := closedBall (0 : ℂ) R₁ ∪ Ω₁ with hT₁
  set Y : Set ℂ := Ω₂ ∪ {z : ℂ | R₂ ≤ ‖z‖} with hY
  have hT₁b : Bornology.IsBounded (T₁ ∪ J) := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R₂)).subset ?_
    rintro z ((hz | hz) | hz)
    · exact mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans hR12.le)
    · exact mem_closedBall_zero_iff.2 (hΩ₁A hz).2.le
    · exact mem_closedBall_zero_iff.2 (hconf.2.2.2.2.1 hz).2.le
  -- the side of `0`
  have hG₁K : toExt T₁ ⊆ (toExt J)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have := OnePoint.coe_injective hwz
    subst this
    exact Set.disjoint_left.1 hdJ1 hz hw
  have hH₁ : IsOpen ((toExt J)ᶜ \ toExt T₁) := by
    have : (toExt J)ᶜ \ toExt T₁ = (toExt (T₁ ∪ J))ᶜ := by
      ext x
      simp only [toExt, image_union, Set.mem_sdiff, mem_compl_iff, mem_union]
      tauto
    rw [this]
    exact OnePoint.isOpen_compl_image_coe.2 ⟨hcl1, (Metric.isCompact_of_isClosed_isBounded hcl1 hT₁b)⟩
  have hc0 : ((0 : ℂ) : ExtPlane) ∈ toExt T₁ := ⟨0, Or.inl (mem_closedBall_self hR1.le), rfl⟩
  -- the side of `∞`
  have hG₂ : IsOpen (toExt Y ∪ {extInf}) := by
    rw [OnePoint.isOpen_iff_of_mem' (Or.inr rfl)]
    have hpre : ((↑) ⁻¹' (toExt Y ∪ {extInf}) : Set ℂ) = Y := by
      ext z
      simp only [toExt, mem_preimage, mem_union, mem_image, mem_singleton_iff]
      constructor
      · rintro (⟨w, hw, hwz⟩ | h)
        · exact OnePoint.coe_injective hwz ▸ hw
        · exact absurd h (OnePoint.coe_ne_infty z)
      · intro hz
        exact Or.inl ⟨z, hz, rfl⟩
    rw [hpre]
    refine ⟨?_, ho2⟩
    refine Metric.isCompact_of_isClosed_isBounded ho2.isClosed_compl ?_
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R₂)).subset fun z hz => ?_
    refine mem_closedBall_zero_iff.2 (le_of_lt (not_le.1 fun h => hz (Or.inr h)))
  have hG₂K : toExt Y ∪ {extInf} ⊆ (toExt J)ᶜ := by
    rintro x (⟨z, hz, rfl⟩ | rfl) ⟨w, hw, hwz⟩
    · have := OnePoint.coe_injective hwz
      subst this
      exact Set.disjoint_left.1 hdJ2 hz hw
    · exact OnePoint.coe_ne_infty w hwz
  have hH₂ : IsOpen ((toExt J)ᶜ \ (toExt Y ∪ {extInf})) := by
    have : (toExt J)ᶜ \ (toExt Y ∪ {extInf}) = toExt (Y ∪ J)ᶜ := by
      ext x
      induction x using OnePoint.rec with
      | infty =>
        simp only [toExt, Set.mem_sdiff, mem_compl_iff, mem_union, mem_singleton_iff, mem_image, not_true_eq_false,
          and_false, or_true]
        tauto
      | coe z =>
        simp only [toExt, Set.mem_sdiff, mem_compl_iff, mem_union, mem_singleton_iff, mem_image]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨z, ?_, rfl⟩
          rintro (hz | hz)
          · exact h2 (Or.inl ⟨z, hz, rfl⟩)
          · exact h1 ⟨z, hz, rfl⟩
        · rintro ⟨w, hw, hwz⟩
          have := OnePoint.coe_injective hwz
          subst this
          refine ⟨?_, ?_⟩
          · rintro ⟨v, hv, hvw⟩
            exact hw (Or.inr (OnePoint.coe_injective hvw ▸ hv))
          · intro h
            rcases h with ⟨v, hv, hvw⟩ | h
            · exact hw (Or.inl (OnePoint.coe_injective hvw ▸ hv))
            · exact OnePoint.coe_ne_infty w h
    rw [this]
    exact OnePoint.isOpen_image_coe.2 hcl2.isOpen_compl
  have hinfG : extInf ∈ toExt Y ∪ {extInf} := Or.inr rfl
  have hG₁c : IsPreconnected (toExt T₁) := hpc1.image _ OnePoint.continuous_coe.continuousOn
  refine ⟨toExt T₁, toExt Y ∪ {extInf},
    ⟨_, hG₁K hc0, gm5_comp_of_clopen hG₁c hG₁K (OnePoint.isOpen_image_coe.2 ho1) hH₁ hc0⟩,
    ⟨_, hG₂K hinfG, gm5_comp_of_clopen hpc2 hG₂K hG₂ hH₂ hinfG⟩, ?_, hc0, hinfG,
    gm5_finitePart_toExt T₁, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨z, hz, rfl⟩ (⟨w, hw, hwz⟩ | h)
    · have := OnePoint.coe_injective hwz
      subst this
      exact Set.disjoint_left.1 hd12 hz hw
    · exact OnePoint.coe_ne_infty z h
  · ext w
    have hchart : w ≠ 0 → extChartInv extInf w = ((w⁻¹ : ℂ) : ExtPlane) := fun hw => by
      show (if w = 0 then extInf else ((w⁻¹ : ℂ) : ExtPlane)) = _
      simp only [hw, ↓reduceIte]
    simp only [mem_ofPred_eq, mem_union, mem_image, mem_closedBall_zero_iff]
    by_cases hw : w = 0
    · subst hw
      have : extChartInv extInf 0 = extInf := by
        show (if (0 : ℂ) = 0 then extInf else _) = _
        simp
      rw [this]
      exact ⟨fun _ => Or.inl (by rw [norm_zero]; exact (inv_pos.2 hR2).le), fun _ => Or.inr rfl⟩
    · rw [hchart hw]
      have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
      constructor
      · rintro (⟨v, hv, hvw⟩ | h)
        · have := OnePoint.coe_injective hvw
          subst this
          rcases hv with hv | hv
          · exact Or.inr ⟨w⁻¹, hv, inv_inv w⟩
          · refine Or.inl ?_
            have hv' : R₂ ≤ ‖w‖⁻¹ := by
              have : R₂ ≤ ‖w⁻¹‖ := hv
              rwa [norm_inv] at this
            have := inv_anti₀ hR2 hv'
            rwa [inv_inv] at this
        · exact absurd h (OnePoint.coe_ne_infty _)
      · rintro (h | ⟨v, hv, hvw⟩)
        · refine Or.inl ⟨w⁻¹, Or.inr ?_, rfl⟩
          show R₂ ≤ ‖w⁻¹‖
          rw [norm_inv]
          calc R₂ = (R₂⁻¹)⁻¹ := (inv_inv R₂).symm
            _ ≤ ‖w‖⁻¹ := inv_anti₀ hw0 h
        · refine Or.inl ⟨w⁻¹, Or.inl ?_, rfl⟩
          rw [← hvw, inv_inv]
          exact hv

/-- Helper (Stage B2): homeomorphic spaces have equally many connected components. -/
theorem gm5_card_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) := by
  have hco : Topology.IsCoinducing h := h.isQuotientMap.isCoinducing
  exact Nat.card_congr (hco.connectedComponentsHomeomorph (fun y => by
    have : h ⁻¹' {y} = {h.symm y} := by
      ext x; simp only [mem_preimage, mem_singleton_iff]; exact (h.toEquiv.eq_symm_apply).symm
    rw [this]; exact isConnected_singleton)).toEquiv

/-- Helper (Stage B2): the inversion `z ↦ 1/z` of `ℂ̄` (a Möbius homeomorphism), on finite nonzero points. -/
theorem gm5_inv_apply {z : ℂ} (hz : z ≠ 0) :
    LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num) (z : ExtPlane) = ((z⁻¹ : ℂ) : ExtPlane) := by
  rw [LiZhongQC.mobiusHomeomorph_apply, LiZhongQC.mobiusExt_coe (by simpa using hz)]
  simp [LiZhongQC.mobiusFn]

/-- Helper (Stage B2): the inversion image of a set of nonzero finite points. -/
theorem gm5_inv_image {Ω : Set ℂ} (h : (0 : ℂ) ∉ Ω) :
    LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num) '' toExt Ω = toExt ((fun z : ℂ => z⁻¹) '' Ω) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z⁻¹, ⟨z, hz, rfl⟩, (gm5_inv_apply (fun h0 => h (h0 ▸ hz))).symm⟩
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, gm5_inv_apply (fun h0 => h (h0 ▸ hz))⟩

/-- Helper (Stage B2): the inverted domain is a domain, and has the ring-domain property. -/
theorem gm5_inv_ring {Ω : Set ℂ} (h : (0 : ℂ) ∉ Ω) (hring : IsRingDomain (toExt Ω)) :
    IsRingDomain (toExt ((fun z : ℂ => z⁻¹) '' Ω)) := by
  set e := LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num) with he
  rw [← gm5_inv_image h]
  obtain ⟨⟨hGo, hGc⟩, h2, hcard⟩ := hring
  refine ⟨⟨e.isOpenMap _ hGo, hGc.image _ e.continuous.continuousOn⟩, h2, ?_⟩
  have hcompl : (e '' toExt Ω)ᶜ = e '' (toExt Ω)ᶜ := (Set.image_compl_eq e.bijective).symm
  have hh : (↥(toExt Ω)ᶜ ≃ₜ ↥(e '' toExt Ω)ᶜ) := (e.image _).trans (Homeomorph.setCongr hcompl.symm)
  rw [← hcard]
  exact (gm5_card_homeo hh).symm

/-- Helper (Stage B2): the inversion transports a conformal map of `Ω` (`0 ∉ Ω`) to a conformal map of `1/Ω`. -/
theorem gm5_inv_conformal {Ω : Set ℂ} (h : (0 : ℂ) ∉ Ω) {ψ : ExtPlane → ExtPlane}
    (hψ : LehtoVirtanen1973.IsConformalMap ψ (toExt Ω)) :
    LehtoVirtanen1973.IsConformalMap (ψ ∘ LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num))
      (toExt ((fun z : ℂ => z⁻¹) '' Ω)) := by
  set e := LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num) with he
  obtain ⟨hdom, hcont, hinj, hdiff⟩ := hψ
  have h1 := gm5_inv_image h
  have hX0 : (0 : ℂ) ∉ (fun z : ℂ => z⁻¹) '' Ω := by
    rintro ⟨z, hz, hz0⟩
    exact h (by rw [inv_eq_zero.1 hz0] at hz; exact hz)
  have h2 : e '' toExt ((fun z : ℂ => z⁻¹) '' Ω) = toExt Ω := by
    rw [gm5_inv_image hX0, image_image]
    simp only [inv_inv, image_id']
  have hmaps : MapsTo e (toExt ((fun z : ℂ => z⁻¹) '' Ω)) (toExt Ω) := fun x hx => h2 ▸ mem_image_of_mem e hx
  refine ⟨⟨?_, ?_⟩, hcont.comp e.continuous.continuousOn hmaps, hinj.comp e.injective.injOn hmaps, ?_⟩
  · rw [← h1]; exact e.isOpenMap _ hdom.1
  · rw [← h1]; exact hdom.2.image _ e.continuous.continuousOn
  · rintro z ⟨a, ⟨v, hv, rfl⟩, rfl⟩
    have hv0 : v ≠ 0 := fun h0 => h (h0 ▸ hv)
    have hd : DifferentiableAt ℂ (LehtoVirtanen1973.localRep ψ (v : ExtPlane)) 0 := hdiff (v : ExtPlane) ⟨v, hv, rfl⟩
    have hg : DifferentiableAt ℂ (fun ζ : ℂ => (v⁻¹ + ζ)⁻¹ - v) 0 := by
      refine DifferentiableAt.sub ?_ (differentiableAt_const _)
      exact DifferentiableAt.inv (by fun_prop) (by simpa using hv0)
    have hd' : DifferentiableAt ℂ (LehtoVirtanen1973.localRep ψ (v : ExtPlane))
        ((fun ζ : ℂ => (v⁻¹ + ζ)⁻¹ - v) 0) := by simpa using hd
    have hcomp := DifferentiableAt.comp (0 : ℂ) hd' hg
    refine hcomp.congr_of_eventuallyEq ?_
    have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), v⁻¹ + ζ ≠ 0 := by
      have : ContinuousAt (fun ζ : ℂ => v⁻¹ + ζ) 0 := by fun_prop
      exact this.eventually_ne (by simpa using hv0)
    filter_upwards [hev] with ζ hζ
    simp only [LehtoVirtanen1973.localRep, Function.comp_apply, LehtoVirtanen1973.extChartInv,
      OnePoint.elim_some, he]
    rw [gm5_inv_apply (inv_ne_zero hv0), gm5_inv_apply hζ, inv_inv, add_sub_cancel]

/-- Helper (Stage B2; conformal invariance of the module under the inversion). The inverted ring domain `1/Ω₂` is a
ring domain and has the same module as `Ω₂`. -/
theorem gm5_inv_ring_mod {R₁ R₂ : ℝ} {J Ω₁ Ω₂ : Set ℂ} (hconf : IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂) :
    IsRingDomain (toExt ((fun z : ℂ => z⁻¹) '' Ω₂)) ∧
      ringModGM (toExt ((fun z : ℂ => z⁻¹) '' Ω₂)) = ringModGM (toExt Ω₂) := by
  have hR1 : 0 < R₁ := hconf.1
  obtain ⟨-, -, hΩA⟩ := gm5_conf_comp hconf (Or.inr rfl)
  have hring := gm5_conf_ring hconf (Or.inr rfl)
  have h0 : (0 : ℂ) ∉ Ω₂ := fun h => absurd (hΩA h).1 (by rw [norm_zero]; exact not_lt.2 hR1.le)
  have hringX := gm5_inv_ring h0 hring
  obtain ⟨r₁, r₂, h1, h12, ψ, hψ, hψB⟩ := gm5_ring_model hconf (Or.inr rfl)
  have hinv := gm5_inv_annulus hR1 hΩA
  have hbX : extInf ∉ closure (toExt ((fun z : ℂ => z⁻¹) '' Ω₂)) := gm5_infty_notMem_closure (R := R₁⁻¹) fun z hz =>
    mem_closedBall_zero_iff.2 (hinv hz).2.le
  have hb2 : extInf ∉ closure (toExt Ω₂) := gm5_infty_notMem_closure (R := R₂) fun z hz =>
    mem_closedBall_zero_iff.2 (hΩA hz).2.le
  have hX0 : (0 : ℂ) ∉ (fun z : ℂ => z⁻¹) '' Ω₂ := by
    rintro ⟨z, hz, hz0⟩
    exact h0 (by rw [inv_eq_zero.1 hz0] at hz; exact hz)
  have himg : (ψ ∘ LiZhongQC.mobiusHomeomorph 0 1 1 0 (by norm_num)) '' toExt ((fun z : ℂ => z⁻¹) '' Ω₂) =
      toExt (annulus r₁ r₂) := by
    rw [image_comp, gm5_inv_image hX0, image_image]
    simp only [inv_inv, image_id']
    exact hψB
  refine ⟨hringX, ?_⟩
  rw [(gm5_ringMod_bounded hringX h1 h12 (gm5_inv_conformal h0 hψ) himg hbX).1,
    (gm5_ringMod_bounded hring h1 h12 hψ hψB hb2).1]

/-- Helper (Stage B2; canonical annulus model of a ring domain with a full circle inside). -/
theorem gm5_ring_model_gen {Ω : Set ℂ} {R₁ R₂ ρ : ℝ} (hR1 : 0 < R₁) (hR12 : R₁ < R₂) (hΩA : Ω ⊆ annulus R₁ R₂)
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hring : IsRingDomain (toExt Ω)) (hρ0 : 0 < ρ)
    (hρ : sphere (0 : ℂ) ρ ⊆ Ω) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ∃ ψ : ExtPlane → ExtPlane,
      LehtoVirtanen1973.IsConformalMap ψ (toExt Ω) ∧ ψ '' toExt Ω = toExt (annulus r₁ r₂) := by
  have hnd := gm5_nondeg hR1 hR12 hΩA hring hρ0 hρ
  have hdc : LiZhongQC.IsDoublyConnected Ω := ⟨hΩo, hΩc, hring.2.2⟩
  obtain ⟨r₁, r₂, hr₁, hr₁₂, f, hf⟩ := LiZhongQC.thm2_1_canonical_form_annulus hdc hnd
  set ψ : ExtPlane → ExtPlane := fun p => OnePoint.elim p extInf (fun z => ((f z : ℂ) : ExtPlane)) with hψ
  have hψc : ∀ z : ℂ, ψ (z : ExtPlane) = ((f z : ℂ) : ExtPlane) := fun z => rfl
  refine ⟨r₁, r₂, hr₁, hr₁₂, ψ, ?_, ?_⟩
  · refine ⟨⟨OnePoint.isOpenEmbedding_coe.isOpenMap _ hΩo,
      ⟨hΩc.nonempty.image _, hΩc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn⟩⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hfc : ContinuousAt f z := (hf.1.differentiableAt (hΩo.mem_nhds hz)).continuousAt
      have : ContinuousAt ψ (z : ExtPlane) := by
        rw [ContinuousAt, ← OnePoint.isOpenEmbedding_coe.map_nhds_eq, tendsto_map'_iff]
        exact (OnePoint.continuous_coe.continuousAt.tendsto.comp hfc)
      exact this.continuousWithinAt
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
      rw [hψc, hψc] at h
      rw [hf.2.1 ha hb (OnePoint.coe_injective h)]
    · rintro _ ⟨z, hz, rfl⟩
      have hloc : LehtoVirtanen1973.localRep ψ (z : ExtPlane) = fun ζ => f (z + ζ) - f z := rfl
      rw [hloc]
      have hd : DifferentiableAt ℂ f (z + 0) := by
        rw [add_zero]; exact hf.1.differentiableAt (hΩo.mem_nhds hz)
      exact ((hd.comp (0 : ℂ) (differentiableAt_const z |>.add differentiableAt_id)).sub_const (f z))
  · ext x
    induction x using OnePoint.rec with
    | infty =>
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, h⟩
        exact absurd ((hψc z).symm.trans h) (OnePoint.coe_ne_infty _)
      · rintro ⟨w, _, hw⟩; exact absurd hw (OnePoint.coe_ne_infty w)
    | coe w =>
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, h⟩
        rw [hψc] at h
        exact ⟨f z, hf.2.2 ▸ mem_image_of_mem f hz, h⟩
      · rintro ⟨v, hv, hvw⟩
        rw [← hf.2.2] at hv
        obtain ⟨z, hz, rfl⟩ := hv
        exact ⟨z, ⟨z, hz, rfl⟩, by rw [hψc]; exact hvw⟩

/-- Helper (Stage B2): every point of the circle `|z| = R` is a limit of points of `G \ B̄(0, R)` when `B̄(0, R) ⊆ G`
and `G` is open. -/
theorem gm5_sphere_mem_closure {G : Set ℂ} {R : ℝ} (hGo : IsOpen G) (hR : 0 < R)
    (hRG : closedBall (0 : ℂ) R ⊆ G) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    z ∈ closure (G \ closedBall 0 R) := by
  rw [mem_sphere_zero_iff_norm] at hz
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hGo z (hRG (mem_closedBall_zero_iff.2 hz.le))
  set t : ℝ := min δ ε / (2 * R) with ht
  have ht0 : 0 < t := by positivity
  refine ⟨((1 + t : ℝ) : ℂ) * z, ⟨hεG ?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have : ((1 + t : ℝ) : ℂ) * z - z = (t : ℂ) * z := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, hz, ht]
    calc min δ ε / (2 * R) * R = min δ ε / 2 := by field_simp
      _ < ε := by linarith [min_le_right δ ε, lt_min hδ hε]
  · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hz]
    nlinarith
  · rw [dist_eq_norm]
    have : z - ((1 + t : ℝ) : ℂ) * z = -((t : ℂ) * z) := by push_cast; ring
    rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, hz, ht]
    calc min δ ε / (2 * R) * R = min δ ε / 2 := by field_simp
      _ < δ := by linarith [min_le_left δ ε, lt_min hδ hε]

/-- Helper (Stage B2; the ends of `G \ B̄(0, R)`). In the canonical annulus model of the ring `G \ B̄(0, R)`, one of the
two ends has cluster set the circle `|z| = R` and the other has its cluster set in `ℂ \ G`. -/
theorem gm5_key_ends {G : Set ℂ} {R r₁ r₂ : ℝ} {g : ℂ → ℂ} (hGo : IsOpen G) (hbdd : Bornology.IsBounded G)
    (hR : 0 < R) (hRG : closedBall (0 : ℂ) R ⊆ G) (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hg : IsConformalOnto g (annulus r₁ r₂) (G \ closedBall 0 R))
    (hring : IsRingDomain (toExt (G \ closedBall 0 R))) :
    ∃ Cin Cout : Set ℂ,
      (∀ p, p ∈ Cin ↔ ∀ ε > 0, p ∈ closure (g '' {w | r₁ < ‖w‖ ∧ ‖w‖ < r₁ + ε})) ∧
      (∀ p, p ∈ Cout ↔ ∀ ε > 0, p ∈ closure (g '' {w | r₂ - ε < ‖w‖ ∧ ‖w‖ < r₂})) ∧
      ((Cin = sphere 0 R ∧ Cout ⊆ Gᶜ) ∨ (Cout = sphere 0 R ∧ Cin ⊆ Gᶜ)) := by
  set U := G \ closedBall 0 R with hU
  have hUb : Bornology.IsBounded U := hbdd.subset sdiff_subset
  have hUo : IsOpen U := hGo.sdiff isClosed_closedBall
  obtain ⟨Cin, Cout, hCin, hCout, hCinc, hCoutc, hCinconn, hCoutconn, hdisj, hfr⟩ :=
    gm5_ends hr₁ hr₁₂ hg hUb hring
  refine ⟨Cin, Cout, hCin, hCout, ?_⟩
  have hFr : closure U \ U = Cin ∪ Cout := by
    have h1 := gm5_frontier_toExt hUo hUb
    have h2 : toExt (closure U \ U) = toExt (Cin ∪ Cout) := by
      rw [← h1, hfr]
      simp only [toExt, image_union]
    exact OnePoint.coe_injective.image_injective h2
  set S := sphere (0 : ℂ) R with hS
  have hSG : S ⊆ G := fun z hz => hRG (sphere_subset_closedBall hz)
  have hSFr : S ⊆ closure U \ U := fun z hz =>
    ⟨gm5_sphere_mem_closure hGo hR hRG hz, fun h => h.2 (sphere_subset_closedBall hz)⟩
  have hFrS : closure U \ U ⊆ S ∪ Gᶜ := by
    rintro z ⟨hzc, hzU⟩
    by_cases hzG : z ∈ G
    · left
      have hzB : z ∈ closedBall (0 : ℂ) R := by
        by_contra h
        exact hzU ⟨hzG, h⟩
      have hge : R ≤ ‖z‖ := by
        have hcl : closure U ⊆ {w : ℂ | R ≤ ‖w‖} :=
          closure_minimal (fun w hw => le_of_lt (not_le.1 fun h => hw.2 (mem_closedBall_zero_iff.2 h)))
            (isClosed_le continuous_const continuous_norm)
        exact hcl hzc
      exact mem_sphere_zero_iff_norm.2 (le_antisymm (mem_closedBall_zero_iff.1 hzB) hge)
    · exact Or.inr hzG
  have hSconn : IsPreconnected S :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) hR.le).isPreconnected
  have hSne : S.Nonempty := ⟨(R : ℂ), by
    rw [hS, mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hR.le]⟩
  have hSsub : S ⊆ Cin ∪ Cout := hFr ▸ hSFr
  have hGc : IsClosed Gᶜ := hGo.isClosed_compl
  -- `S` lies in one end
  have hone := (isPreconnected_iff_subset_of_disjoint_closed.1 hSconn) Cin Cout hCinc.isClosed hCoutc.isClosed hSsub
    (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hz1, hz2⟩
      exact Set.disjoint_left.1 hdisj hz1 hz2)
  -- a connected closed set inside the frontier meeting `S` lies in `S`
  have hend : ∀ C : Set ℂ, IsClosed C → IsPreconnected C → C ⊆ closure U \ U → (S ∩ C).Nonempty → C ⊆ S := by
    intro C hCc hCp hCsub hne
    have hsub := hCsub.trans hFrS
    have h2 := (isPreconnected_iff_subset_of_disjoint_closed.1 hCp) S Gᶜ isClosed_sphere hGc hsub
      (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨-, hz1, hz2⟩
        exact hz2 (hSG hz1))
    rcases h2 with h | h
    · exact h
    · obtain ⟨z, hzS, hzC⟩ := hne
      exact absurd (hSG hzS) (h hzC)
  have hCinFr : Cin ⊆ closure U \ U := hFr ▸ subset_union_left
  have hCoutFr : Cout ⊆ closure U \ U := hFr ▸ subset_union_right
  rcases hone with h | h
  · have hCS : Cin ⊆ S := hend Cin hCinc.isClosed hCinconn.isPreconnected hCinFr
      (by obtain ⟨z, hz⟩ := hSne; exact ⟨z, hz, h hz⟩)
    have hCe : Cin = S := le_antisymm hCS h
    refine Or.inl ⟨hCe, fun z hz => ?_⟩
    rcases hFrS (hCoutFr hz) with hzS | hzG
    · exact absurd (hCe ▸ hzS) (Set.disjoint_right.1 hdisj hz)
    · exact hzG
  · have hCS : Cout ⊆ S := hend Cout hCoutc.isClosed hCoutconn.isPreconnected hCoutFr
      (by obtain ⟨z, hz⟩ := hSne; exact ⟨z, hz, h hz⟩)
    have hCe : Cout = S := le_antisymm hCS h
    refine Or.inr ⟨hCe, fun z hz => ?_⟩
    rcases hFrS (hCinFr hz) with hzS | hzG
    · exact absurd (hCe ▸ hzS) (Set.disjoint_left.1 hdisj hz)
    · exact hzG

/-- Helper (Stage B2): the flip `w ↦ r₁ r₂ / w` of the annulus `r₁ < |w| < r₂`. -/
theorem gm5_flip_conformal {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    IsConformalOnto (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) (annulus r₁ r₂) (annulus r₁ r₂) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hc : 0 < r₁ * r₂ := mul_pos hr₁ hr₂
  have hnorm : ∀ x : ℂ, ‖((r₁ * r₂ : ℝ) : ℂ) / x‖ = r₁ * r₂ / ‖x‖ := fun x => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hne : ∀ x ∈ annulus r₁ r₂, x ≠ 0 := fun x hx h0 => by
    have := hx.1
    rw [h0, norm_zero] at this
    linarith
  have hinv : ∀ x : ℂ, x ≠ 0 → ((r₁ * r₂ : ℝ) : ℂ) / (((r₁ * r₂ : ℝ) : ℂ) / x) = x := fun x hx => by
    have : ((r₁ * r₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, ?_⟩
  · exact (differentiableAt_const _ |>.div differentiableAt_id (hne x hx)).differentiableWithinAt
  · have := congrArg (fun w => ((r₁ * r₂ : ℝ) : ℂ) / w) h
    simp only [hinv x (hne x hx), hinv y (hne y hy)] at this
    exact this
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : 0 < ‖x‖ := hr₁.trans hx.1
      rw [annulus, mem_ofPred_eq, hnorm, div_lt_iff₀ hx0, lt_div_iff₀ hx0]
      constructor <;> nlinarith [hx.1, hx.2]
    · intro hy
      have hy0 : y ≠ 0 := hne y hy
      have hyn : 0 < ‖y‖ := hr₁.trans hy.1
      refine ⟨((r₁ * r₂ : ℝ) : ℂ) / y, ?_, hinv y hy0⟩
      rw [annulus, mem_ofPred_eq, hnorm, div_lt_iff₀ hyn, lt_div_iff₀ hyn]
      constructor <;> nlinarith [hy.1, hy.2]

/-- Helper (Stage B2): the four images of the sub-annuli under the flip. -/
theorem gm5_flip_images {r₁ r₂ s : ℝ} (hr₁ : 0 < r₁) (hsr : s ∈ Ioo r₁ r₂) :
    (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) '' {w | r₁ < ‖w‖ ∧ ‖w‖ < s} = {w | r₁ * r₂ / s < ‖w‖ ∧ ‖w‖ < r₂} ∧
    (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) '' {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ s} = {w | r₁ * r₂ / s ≤ ‖w‖ ∧ ‖w‖ < r₂} ∧
    (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) '' {w | s < ‖w‖ ∧ ‖w‖ < r₂} = {w | r₁ < ‖w‖ ∧ ‖w‖ < r₁ * r₂ / s} ∧
    (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) '' {w | s ≤ ‖w‖ ∧ ‖w‖ < r₂} = {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ r₁ * r₂ / s} := by
  have hr₂ : 0 < r₂ := hr₁.trans (hsr.1.trans hsr.2)
  have hs : 0 < s := hr₁.trans hsr.1
  have hc : 0 < r₁ * r₂ := mul_pos hr₁ hr₂
  have hnorm : ∀ x : ℂ, ‖((r₁ * r₂ : ℝ) : ℂ) / x‖ = r₁ * r₂ / ‖x‖ := fun x => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hcne : ((r₁ * r₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hinv : ∀ x : ℂ, x ≠ 0 → ((r₁ * r₂ : ℝ) : ℂ) / (((r₁ * r₂ : ℝ) : ℂ) / x) = x := fun x hx => by
    field_simp
  -- generic: the image of `{w | P ‖w‖}` is `{w | Q ‖w‖}` when `P t ↔ Q (c / t)` for `t > 0` and `P` forces `t > 0`
  have key : ∀ P Q : ℝ → Prop, (∀ t, P t → 0 < t) → (∀ t, Q t → 0 < t) → (∀ t, 0 < t → (P t ↔ Q (r₁ * r₂ / t))) →
      (fun w : ℂ => ((r₁ * r₂ : ℝ) : ℂ) / w) '' {w | P ‖w‖} = {w | Q ‖w‖} := by
    intro P Q hP hQ hPQ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : 0 < ‖x‖ := hP _ hx
      show Q ‖((r₁ * r₂ : ℝ) : ℂ) / x‖
      rw [hnorm]
      exact (hPQ _ hx0).1 hx
    · intro hy
      have hyn : 0 < ‖y‖ := hQ _ hy
      have hy0 : y ≠ 0 := norm_pos_iff.1 hyn
      refine ⟨((r₁ * r₂ : ℝ) : ℂ) / y, ?_, hinv y hy0⟩
      show P ‖((r₁ * r₂ : ℝ) : ℂ) / y‖
      rw [hnorm]
      have hpos : 0 < r₁ * r₂ / ‖y‖ := by positivity
      rw [hPQ _ hpos, div_div_cancel₀ hc.ne']
      exact hy
  have hdiv : ∀ t : ℝ, 0 < t → ∀ a : ℝ, 0 < a → (a < r₁ * r₂ / t ↔ t < r₁ * r₂ / a) := by
    intro t ht a ha
    rw [lt_div_iff₀ ht, lt_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  have hcs : r₁ * r₂ / s * s = r₁ * r₂ := div_mul_cancel₀ _ hs.ne'
  have hrr : r₁ * r₂ / r₂ = r₁ := by field_simp
  have hrr' : r₁ * r₂ / r₁ = r₂ := by field_simp
  refine ⟨key (fun t => r₁ < t ∧ t < s) (fun t => r₁ * r₂ / s < t ∧ t < r₂) (fun t ht => hr₁.trans ht.1)
      (fun t ht => lt_of_le_of_lt (by positivity) ht.1) ?_,
    key (fun t => r₁ < t ∧ t ≤ s) (fun t => r₁ * r₂ / s ≤ t ∧ t < r₂) (fun t ht => hr₁.trans ht.1)
      (fun t ht => lt_of_lt_of_le (by positivity) ht.1) ?_,
    key (fun t => s < t ∧ t < r₂) (fun t => r₁ < t ∧ t < r₁ * r₂ / s) (fun t ht => hs.trans ht.1)
      (fun t ht => hr₁.trans ht.1) ?_,
    key (fun t => s ≤ t ∧ t < r₂) (fun t => r₁ < t ∧ t ≤ r₁ * r₂ / s) (fun t ht => lt_of_lt_of_le hs ht.1)
      (fun t ht => hr₁.trans ht.1) ?_⟩
  · intro t ht
    have e1 : r₁ * r₂ / s < r₁ * r₂ / t ↔ t < s := div_lt_div_iff_of_pos_left hc hs ht
    have e2 : r₁ * r₂ / t < r₂ ↔ r₁ < t := by rw [div_lt_iff₀ ht]; constructor <;> intro h <;> nlinarith
    rw [e1, e2, and_comm]
  · intro t ht
    have e1 : r₁ * r₂ / s ≤ r₁ * r₂ / t ↔ t ≤ s := div_le_div_iff_of_pos_left hc hs ht
    have e2 : r₁ * r₂ / t < r₂ ↔ r₁ < t := by rw [div_lt_iff₀ ht]; constructor <;> intro h <;> nlinarith
    rw [e1, e2, and_comm]
  · intro t ht
    have e1 : r₁ < r₁ * r₂ / t ↔ t < r₂ := by rw [lt_div_iff₀ ht]; constructor <;> intro h <;> nlinarith
    have e2 : r₁ * r₂ / t < r₁ * r₂ / s ↔ s < t := div_lt_div_iff_of_pos_left hc ht hs
    rw [e1, e2, and_comm]
  · intro t ht
    have e1 : r₁ < r₁ * r₂ / t ↔ t < r₂ := by rw [lt_div_iff₀ ht]; constructor <;> intro h <;> nlinarith
    have e2 : r₁ * r₂ / t ≤ r₁ * r₂ / s ↔ s ≤ t := div_le_div_iff_of_pos_left hc ht hs
    rw [e1, e2, and_comm]

/-- Helper (Stage B2; the canonical model of the ring `G \ B̄(0, R)` with its orientation). `G` is a bounded plane
domain with `B̄(0, R) ⊆ G` and `G \ B̄(0, R)` a ring domain: it is mapped onto by a conformal `g` of an annulus
`r₁ < |w| < r₂`; the module is `(1/2π) log (r₂/r₁)`; the inner end of the annulus goes to the circle `|z| = R`, the
outer end to `ℂ \ G` (the two ends are the two components of the boundary: `∂G` is outside `B̄(0, R)`). -/
theorem gm5_key_model {G : Set ℂ} {R : ℝ} (hGo : IsOpen G) (hbdd : Bornology.IsBounded G) (hR : 0 < R)
    (hRG : closedBall (0 : ℂ) R ⊆ G) (hring : IsRingDomain (toExt (G \ closedBall 0 R))) :
    ∃ r₁ r₂ : ℝ, ∃ g : ℂ → ℂ, 0 < r₁ ∧ r₁ < r₂ ∧ IsConformalOnto g (annulus r₁ r₂) (G \ closedBall 0 R) ∧
      ringModGM (toExt (G \ closedBall 0 R)) = ENNReal.ofReal (1 / (2 * π) * Real.log (r₂ / r₁)) ∧
      (∀ s ∈ Ioo r₁ r₂, closure (g '' {w | r₁ < ‖w‖ ∧ ‖w‖ < s}) ⊆
        g '' {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ s} ∪ sphere 0 R) ∧
      (∀ s ∈ Ioo r₁ r₂, closure (g '' {w | s < ‖w‖ ∧ ‖w‖ < r₂}) ⊆
        g '' {w | s ≤ ‖w‖ ∧ ‖w‖ < r₂} ∪ Gᶜ) := by
  set U := G \ closedBall 0 R with hU
  have hUo : IsOpen U := hGo.sdiff isClosed_closedBall
  obtain ⟨M, hM⟩ := hbdd.subset_closedBall (0 : ℂ)
  have hRM : R ≤ M := by
    have : ((R : ℝ) : ℂ) ∈ G := hRG (by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR.le])
    have := mem_closedBall_zero_iff.1 (hM this)
    rwa [Complex.norm_real, Real.norm_of_nonneg hR.le] at this
  have hUA : U ⊆ annulus R (M + 1) := fun z hz =>
    ⟨not_le.1 fun h => hz.2 (mem_closedBall_zero_iff.2 h),
      lt_of_le_of_lt (mem_closedBall_zero_iff.1 (hM hz.1)) (by linarith)⟩
  -- a full circle inside `U`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open hGo hRG
  have hρ : sphere (0 : ℂ) (R + δ / 2) ⊆ U := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine ⟨hδU ?_, fun h => ?_⟩
    · rw [Metric.mem_thickening_iff]
      refine ⟨((R / (R + δ / 2) : ℝ) : ℂ) * z, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, hz, Real.norm_of_nonneg (by positivity)]
        field_simp
        exact le_rfl
      · rw [dist_eq_norm]
        have : z - ((R / (R + δ / 2) : ℝ) : ℂ) * z = ((1 - R / (R + δ / 2) : ℝ) : ℂ) * z := by push_cast; ring
        rw [this, norm_mul, Complex.norm_real, hz, Real.norm_of_nonneg]
        · have : (1 - R / (R + δ / 2)) * (R + δ / 2) = δ / 2 := by field_simp; ring
          rw [this]; linarith
        · rw [sub_nonneg, div_le_one (by positivity)]; linarith
    · rw [mem_closedBall_zero_iff, hz] at h
      linarith
  have hUc : IsConnected U := by
    have h1 := hring.1.2
    refine ⟨?_, ?_⟩
    · obtain ⟨x, ⟨z, hz, rfl⟩⟩ := h1.nonempty
      exact ⟨z, hz⟩
    · exact OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h1.isPreconnected
  obtain ⟨r₁, r₂, h1, h12, ψ, hψ, hψB⟩ := gm5_ring_model_gen hR (by linarith : R < M + 1) hUA hUo hUc hring
    (by positivity : 0 < R + δ / 2) hρ
  have hbd : extInf ∉ closure (toExt U) := gm5_infty_notMem_closure (R := M + 1) fun z hz =>
    mem_closedBall_zero_iff.2 (hUA hz).2.le
  obtain ⟨g, hBU, hUb, hUo', hψc, hgc, hgψ, hψg⟩ := gm5_ring_plane hring h1 h12 hψ hψB hbd
  rw [gm5_finitePart_toExt] at hgc
  have hmod := (gm5_ringMod_bounded hring h1 h12 hψ hψB hbd).1
  obtain ⟨Cin, Cout, hCin, hCout, hcase⟩ := gm5_key_ends hGo hbdd hR hRG h1 h12 hgc hring
  rcases hcase with ⟨hCe, hCG⟩ | ⟨hCe, hCG⟩
  · refine ⟨r₁, r₂, g, h1, h12, hgc, hmod, fun s hs => ?_, fun s hs => ?_⟩
    · have := gm5_closure_in2 hgc hCin hs.2
      rwa [hCe] at this
    · exact (gm5_closure_out2 hgc hCout hs.1).trans (union_subset_union_right _ hCG)
  · set f : ℂ → ℂ := fun w => ((r₁ * r₂ : ℝ) : ℂ) / w with hf
    have hfc := gm5_flip_conformal h1 h12
    have hg' : IsConformalOnto (fun w => g (f w)) (annulus r₁ r₂) U := hgc.comp hfc
    have himg : ∀ A : Set ℂ, (fun w => g (f w)) '' A = g '' (f '' A) := fun A => Set.image_comp g f A
    refine ⟨r₁, r₂, fun w => g (f w), h1, h12, hg', hmod, fun s hs => ?_, fun s hs => ?_⟩
    · obtain ⟨e1, e2, -, -⟩ := gm5_flip_images h1 hs
      rw [himg, himg, e1, e2]
      have hrs : r₁ < r₁ * r₂ / s := by
        rw [lt_div_iff₀ (h1.trans hs.1)]; nlinarith [hs.2]
      have := gm5_closure_out2 hgc hCout hrs
      rwa [hCe] at this
    · obtain ⟨-, -, e3, e4⟩ := gm5_flip_images h1 hs
      rw [himg, himg, e3, e4]
      have hrs : r₁ * r₂ / s < r₂ := by
        rw [div_lt_iff₀ (h1.trans hs.1)]; nlinarith [hs.1, h1.trans hs.1]
      exact (gm5_closure_in2 hgc hCin hrs).trans (union_subset_union_right _ hCG)

/-- Helper (Stage B2): a conformal circle contained in `A` belongs to the separating family of `A` as soon as it
separates (the path-curve and closed-curve conditions are automatic). -/
theorem gm5_mem_sepFamily {U A E Fs : Set ℂ} {g : ℂ → ℂ} {r R s : ℝ} (hr : 0 < r)
    (hg : IsConformalOnto g (annulus r R) U) (hs : s ∈ Ioo r R) (hUA : U ⊆ A)
    (hsep : IsSeparatingIn A (g '' sphere 0 s) E Fs) : g '' sphere 0 s ∈ separatingFamily A E Fs := by
  have hs0 : 0 < s := hr.trans hs.1
  have hsubA : sphere (0 : ℂ) s ⊆ annulus r R := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩
  refine ⟨?_, ?_, hsep⟩
  · obtain ⟨sn, hsn, heq⟩ := gm5_circle_pathCurve hr hg hs
    exact ⟨sn, fun n => ⟨(hsn n).1, (hsn n).2.trans hUA⟩, heq⟩
  · obtain ⟨k, hkc, hk01, hksph⟩ := gm4b_circle_closed hs0
    refine ⟨{g '' sphere 0 s}, finite_singleton _, by simp, fun c hc => Or.inr ?_⟩
    rw [mem_singleton_iff.1 hc]
    refine ⟨fun t => g (k t), ?_, by simp only [hk01], by rw [hksph, image_image]⟩
    exact hg.1.continuousOn.comp hkc fun t ht => hsubA (hksph ▸ mem_image_of_mem k ht)

/-- Helper (Stage B2; topological core of the separation in the annulus `s' < |z| < 1`): if `A \ γ` is covered by two
disjoint open sets, the first containing the inner circle and having closure off the outer circle, then `γ`
separates the two circles. -/
theorem gm5_sepW_core {s' : ℝ} {γ N₁ N₂ : Set ℂ} (hN₁o : IsOpen N₁) (hN₂o : IsOpen N₂) (hdisj : Disjoint N₁ N₂)
    (hcov : annulus s' 1 \ γ ⊆ N₁ ∪ N₂) (h1 : Disjoint (closure N₁) (sphere 0 1)) (hsph : sphere (0 : ℂ) s' ⊆ N₁) :
    IsSeparatingIn (annulus s' 1) γ (sphere 0 s') (sphere 0 1) := by
  rintro x hx ⟨⟨p, hpK, hps⟩, ⟨q, hqK, hqs⟩⟩
  have hKsub : connectedComponentIn (annulus s' 1 \ γ) x ⊆ N₁ ∪ N₂ :=
    (connectedComponentIn_subset _ _).trans hcov
  rcases isPreconnected_connectedComponentIn.subset_or_subset hN₁o hN₂o hdisj hKsub with h | h
  · exact Set.disjoint_left.1 h1 (closure_mono h hqK) hqs
  · have hp : p ∈ closure N₂ := closure_mono h hpK
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hp N₁ hN₁o (hsph hps)
    exact Set.disjoint_left.1 hdisj hy1 hy2

/-- Helper (Stage B2): `F` maps `{ρ' ≤ |u|}` into the annulus `s' < |z| < 1`. -/
theorem gm5_F_inW {G : Set ℂ} {φ F : ℂ → ℂ} {ρ' s' : ℝ} (hF : IsConformalOnto F G unitDisc)
    (hφF : ∀ u ∈ G, φ (F u) = u) (hs' : ∀ w : ℂ, ‖w‖ ≤ s' → ‖φ w‖ < ρ') {u : ℂ} (hu : u ∈ G) (hρu : ρ' ≤ ‖u‖) :
    F u ∈ annulus s' 1 := by
  refine ⟨?_, mem_ball_zero_iff.1 (hF.mapsTo hu)⟩
  by_contra hle
  have := hs' _ (not_lt.1 hle)
  rw [hφF u hu] at this
  exact absurd hρu (not_le.2 this)

/-- Helper (Stage B2; separation, circles). `φ : 𝔻 → G` is conformal with inverse `F`, `B̄(0, R) ⊆ G`, and
`φ(B̄(0, s')) ⊆ B(0, ρ')`, `ρ' < t < R`: the curve `F({|u| = t})` separates the two boundary circles of the annulus
`s' < |z| < 1` in it. -/
theorem gm5_sepW_circle {G : Set ℂ} {φ F : ℂ → ℂ} {R ρ' s' t : ℝ} (hGo : IsOpen G)
    (hφ : IsConformalOnto φ unitDisc G) (hF : IsConformalOnto F G unitDisc)
    (hFφ : ∀ z ∈ unitDisc, F (φ z) = z) (hφF : ∀ u ∈ G, φ (F u) = u) (hRG : closedBall (0 : ℂ) R ⊆ G)
    (hs0 : 0 < s') (hs1 : s' < 1) (hs' : ∀ w : ℂ, ‖w‖ ≤ s' → ‖φ w‖ < ρ') (ht : t ∈ Ioo ρ' R) :
    F '' sphere 0 t ∈ separatingFamily (annulus s' 1) (sphere 0 s') (sphere 0 1) := by
  have hρ' : 0 < ρ' := lt_of_le_of_lt (norm_nonneg _) (hs' 0 (by simp [hs0.le]))
  have hA'G : annulus ρ' R ⊆ G := fun u hu => hRG (mem_closedBall_zero_iff.2 hu.2.le)
  have hg1 : IsConformalOnto F (annulus ρ' R) (F '' annulus ρ' R) := ⟨hF.1.mono hA'G, hF.2.1.mono hA'G, rfl⟩
  have hUW : F '' annulus ρ' R ⊆ annulus s' 1 := by
    rintro _ ⟨u, hu, rfl⟩
    exact gm5_F_inW hF hφF hs' (hA'G hu) hu.1.le
  refine gm5_mem_sepFamily hρ' hg1 ht hUW ?_
  have hcont : ContinuousOn (fun z => ‖φ z‖) unitDisc := hφ.1.continuousOn.norm
  set N₁ : Set ℂ := unitDisc ∩ (fun z => ‖φ z‖) ⁻¹' Iio t with hN₁
  set N₂ : Set ℂ := unitDisc ∩ (fun z => ‖φ z‖) ⁻¹' Ioi t with hN₂
  have htG : closedBall (0 : ℂ) t ⊆ G := fun u hu => hRG (closedBall_subset_closedBall ht.2.le hu)
  refine gm5_sepW_core (N₁ := N₁) (N₂ := N₂) (hcont.isOpen_inter_preimage isOpen_ball isOpen_Iio)
    (hcont.isOpen_inter_preimage isOpen_ball isOpen_Ioi) ?_ ?_ ?_ ?_
  · rw [Set.disjoint_left]
    rintro z ⟨-, hz1⟩ ⟨-, hz2⟩
    have h1 : ‖φ z‖ < t := hz1
    have h2 : t < ‖φ z‖ := hz2
    linarith
  · rintro z ⟨hzW, hzγ⟩
    have hz1 : z ∈ unitDisc := mem_ball_zero_iff.2 hzW.2
    have hne : ‖φ z‖ ≠ t := fun h => hzγ ⟨φ z, mem_sphere_zero_iff_norm.2 h, hFφ z hz1⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hz1, h⟩
    · exact Or.inr ⟨hz1, h⟩
  · have hK : IsCompact (F '' closedBall (0 : ℂ) t) :=
      (isCompact_closedBall _ _).image_of_continuousOn (hF.1.continuousOn.mono htG)
    have hsub : N₁ ⊆ F '' closedBall (0 : ℂ) t := by
      rintro z ⟨hz1, hz2⟩
      exact ⟨φ z, mem_closedBall_zero_iff.2 (le_of_lt hz2), hFφ z hz1⟩
    have hcl := closure_minimal hsub hK.isClosed
    rw [Set.disjoint_left]
    intro z hz hz1
    have : z ∈ unitDisc := by
      obtain ⟨u, hu, rfl⟩ := hcl hz
      exact hF.mapsTo (htG hu)
    rw [mem_sphere_zero_iff_norm] at hz1
    rw [unitDisc, mem_ball_zero_iff] at this
    linarith
  · intro p hp
    rw [mem_sphere_zero_iff_norm] at hp
    refine ⟨mem_ball_zero_iff.2 (hp ▸ hs1), ?_⟩
    show ‖φ p‖ < t
    exact (hs' p hp.le).trans ht.1

/-- Helper (Stage B2; separation, conformal circles of the ring). Same setting; `g` is the oriented model of
`G \ B̄(0, R)` of `gm5_key_model` and `r₁ < s < r₂`: the curve `F(g({|w| = s}))` separates the two boundary circles of
`s' < |z| < 1` in it. -/
theorem gm5_sepW_g {G : Set ℂ} {φ F g : ℂ → ℂ} {R ρ' s' r₁ r₂ s : ℝ} (hGo : IsOpen G)
    (hbdd : Bornology.IsBounded G)
    (hφ : IsConformalOnto φ unitDisc G) (hF : IsConformalOnto F G unitDisc)
    (hFφ : ∀ z ∈ unitDisc, F (φ z) = z) (hφF : ∀ u ∈ G, φ (F u) = u) (hRG : closedBall (0 : ℂ) R ⊆ G)
    (hρ'R : ρ' < R) (hs0 : 0 < s') (hs1 : s' < 1) (hs' : ∀ w : ℂ, ‖w‖ ≤ s' → ‖φ w‖ < ρ')
    (hr₁ : 0 < r₁) (hg : IsConformalOnto g (annulus r₁ r₂) (G \ closedBall 0 R)) (hsr : s ∈ Ioo r₁ r₂)
    (hin : closure (g '' {w | r₁ < ‖w‖ ∧ ‖w‖ < s}) ⊆ g '' {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ s} ∪ sphere 0 R)
    (hout : closure (g '' {w | s < ‖w‖ ∧ ‖w‖ < r₂}) ⊆ g '' {w | s ≤ ‖w‖ ∧ ‖w‖ < r₂} ∪ Gᶜ) :
    (fun w => F (g w)) '' sphere 0 s ∈ separatingFamily (annulus s' 1) (sphere 0 s') (sphere 0 1) := by
  have hρ' : 0 < ρ' := lt_of_le_of_lt (norm_nonneg _) (hs' 0 (by simp [hs0.le]))
  have hΩG : G \ closedBall 0 R ⊆ G := sdiff_subset
  have hFΩ : IsConformalOnto F (G \ closedBall 0 R) (F '' (G \ closedBall 0 R)) :=
    ⟨hF.1.mono hΩG, hF.2.1.mono hΩG, rfl⟩
  have hg2 : IsConformalOnto (fun w => F (g w)) (annulus r₁ r₂) (F '' (G \ closedBall 0 R)) := hFΩ.comp hg
  have hUW : F '' (G \ closedBall 0 R) ⊆ annulus s' 1 := by
    rintro _ ⟨u, hu, rfl⟩
    refine gm5_F_inW hF hφF hs' hu.1 ?_
    have : R < ‖u‖ := not_le.1 fun h => hu.2 (mem_closedBall_zero_iff.2 h)
    linarith
  refine gm5_mem_sepFamily hr₁ hg2 hsr hUW ?_
  -- the pieces of `G`
  set Ain : Set ℂ := {w | r₁ < ‖w‖ ∧ ‖w‖ < s} with hAin
  set Aout : Set ℂ := {w | s < ‖w‖ ∧ ‖w‖ < r₂} with hAout
  have hAinO : IsOpen Ain := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hAoutO : IsOpen Aout := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hAinA : Ain ⊆ annulus r₁ r₂ := fun w hw => ⟨hw.1, hw.2.trans hsr.2⟩
  have hAoutA : Aout ⊆ annulus r₁ r₂ := fun w hw => ⟨hsr.1.trans hw.1, hw.2⟩
  have hginj := hg.2.1
  have hgmaps : ∀ w ∈ annulus r₁ r₂, g w ∈ G \ closedBall 0 R := fun w hw => hg.mapsTo hw
  set P : Set ℂ := closedBall 0 R ∪ g '' Ain with hP
  set Q' : Set ℂ := g '' {w | s ≤ ‖w‖ ∧ ‖w‖ < r₂} with hQ'
  have hPQ : P = G \ Q' := by
    ext z
    constructor
    · rintro (hz | ⟨w, hw, rfl⟩)
      · refine ⟨hRG hz, ?_⟩
        rintro ⟨w, hw, rfl⟩
        exact (hgmaps w ⟨hsr.1.trans_le hw.1, hw.2⟩).2 hz
      · refine ⟨(hgmaps w (hAinA hw)).1, ?_⟩
        rintro ⟨v, hv, hvw⟩
        have := hginj ⟨hsr.1.trans_le hv.1, hv.2⟩ (hAinA hw) hvw
        subst this
        linarith [hw.2, hv.1]
    · rintro ⟨hzG, hzQ⟩
      by_cases hz : z ∈ closedBall (0 : ℂ) R
      · exact Or.inl hz
      · right
        have hzΩ : z ∈ g '' annulus r₁ r₂ := by rw [hg.2.2]; exact ⟨hzG, hz⟩
        obtain ⟨w, hw, rfl⟩ := hzΩ
        refine ⟨w, ⟨hw.1, ?_⟩, rfl⟩
        by_contra hle
        exact hzQ ⟨w, ⟨not_lt.1 hle, hw.2⟩, rfl⟩
  have hPo : IsOpen P := by
    have hcl : closure Q' ⊆ Q' ∪ Gᶜ := by
      have hset : {w : ℂ | s ≤ ‖w‖ ∧ ‖w‖ < r₂} = Aout ∪ sphere 0 s := by
        ext w
        simp only [hAout, mem_union, mem_ofPred_eq, mem_sphere_zero_iff_norm]
        constructor
        · rintro ⟨h1, h2⟩
          rcases lt_or_eq_of_le h1 with h | h
          · exact Or.inl ⟨h, h2⟩
          · exact Or.inr h.symm
        · rintro (⟨h1, h2⟩ | h)
          · exact ⟨h1.le, h2⟩
          · exact ⟨h.ge, h ▸ hsr.2⟩
      have hQ'eq : Q' = g '' Aout ∪ g '' sphere 0 s := by
        rw [hQ', hset, image_union]
      have hsphc : IsCompact (g '' sphere 0 s) :=
        (isCompact_sphere _ _).image_of_continuousOn (hg.1.continuousOn.mono fun z hz => by
          rw [mem_sphere_zero_iff_norm] at hz
          exact ⟨hz ▸ hsr.1, hz ▸ hsr.2⟩)
      have hsphQ : g '' sphere 0 s ⊆ Q' := by
        rintro _ ⟨w, hw, rfl⟩
        rw [mem_sphere_zero_iff_norm] at hw
        exact ⟨w, ⟨hw.ge, hw ▸ hsr.2⟩, rfl⟩
      have hclQ : closure Q' = closure (g '' Aout) ∪ g '' sphere 0 s := by
        rw [hQ'eq, closure_union, hsphc.isClosed.closure_eq]
      rw [hclQ]
      rintro z (hz | hz)
      · rcases hout hz with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact Or.inl (hsphQ hz)
    have : P = G ∩ (closure Q')ᶜ := by
      rw [hPQ]
      ext z
      constructor
      · rintro ⟨hzG, hzQ⟩
        exact ⟨hzG, fun h => by
          rcases hcl h with h' | h'
          · exact hzQ h'
          · exact h' hzG⟩
      · rintro ⟨hzG, hzc⟩
        exact ⟨hzG, fun h => hzc (subset_closure h)⟩
    rw [this]
    exact hGo.inter isClosed_closure.isOpen_compl
  have hQo : IsOpen (g '' Aout) := gm5_image_open hg hAoutO hAoutA
  have hcont : ContinuousOn φ unitDisc := hφ.1.continuousOn
  set N₁ : Set ℂ := unitDisc ∩ φ ⁻¹' P with hN₁
  set N₂ : Set ℂ := unitDisc ∩ φ ⁻¹' (g '' Aout) with hN₂
  refine gm5_sepW_core (N₁ := N₁) (N₂ := N₂) (hcont.isOpen_inter_preimage isOpen_ball hPo)
    (hcont.isOpen_inter_preimage isOpen_ball hQo) ?_ ?_ ?_ ?_
  · rw [Set.disjoint_left]
    rintro z ⟨-, hz1⟩ ⟨-, ⟨w, hw, hwz⟩⟩
    have hz1' : φ z ∈ P := hz1
    rw [hPQ] at hz1'
    exact hz1'.2 ⟨w, ⟨hw.1.le, hw.2⟩, hwz⟩
  · rintro z ⟨hzW, hzγ⟩
    have hz1 : z ∈ unitDisc := mem_ball_zero_iff.2 hzW.2
    have hzG : φ z ∈ G := hφ.mapsTo hz1
    by_cases hz : φ z ∈ closedBall (0 : ℂ) R
    · exact Or.inl ⟨hz1, Or.inl hz⟩
    · have hzΩ : φ z ∈ g '' annulus r₁ r₂ := by rw [hg.2.2]; exact ⟨hzG, hz⟩
      obtain ⟨w, hw, hwz⟩ := hzΩ
      have hne : ‖w‖ ≠ s := fun h => hzγ ⟨w, mem_sphere_zero_iff_norm.2 h, by
        show F (g w) = z
        rw [hwz, hFφ z hz1]⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hz1, Or.inr ⟨w, ⟨hw.1, h⟩, hwz⟩⟩
      · exact Or.inr ⟨hz1, ⟨w, ⟨h, hw.2⟩, hwz⟩⟩
  · have hKsub : closure P ⊆ G := by
      have : closure P ⊆ closedBall 0 R ∪ (g '' {w | r₁ < ‖w‖ ∧ ‖w‖ ≤ s} ∪ sphere 0 R) := by
        rw [hP, closure_union, isClosed_closedBall.closure_eq]
        exact union_subset_union_right _ hin
      intro z hz
      rcases this hz with h | h | h
      · exact hRG h
      · obtain ⟨w, hw, rfl⟩ := h
        exact (hgmaps w ⟨hw.1, hw.2.trans_lt hsr.2⟩).1
      · exact hRG (sphere_subset_closedBall h)
    have hKc : IsCompact (closure P) := by
      refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
      exact (hbdd.subset (hP ▸ (union_subset (hRG) (fun z hz => by
        obtain ⟨w, hw, rfl⟩ := hz
        exact (hgmaps w (hAinA hw)).1)) : P ⊆ G)).closure
    have hK : IsCompact (F '' closure P) := hKc.image_of_continuousOn (hF.1.continuousOn.mono hKsub)
    have hsub : N₁ ⊆ F '' closure P := by
      rintro z ⟨hz1, hz2⟩
      exact ⟨φ z, subset_closure hz2, hFφ z hz1⟩
    have hcl := closure_minimal hsub hK.isClosed
    rw [Set.disjoint_left]
    intro z hz hz1
    have : z ∈ unitDisc := by
      obtain ⟨u, hu, rfl⟩ := hcl hz
      exact hF.mapsTo (hKsub hu)
    rw [mem_sphere_zero_iff_norm] at hz1
    rw [unitDisc, mem_ball_zero_iff] at this
    linarith
  · intro p hp
    rw [mem_sphere_zero_iff_norm] at hp
    refine ⟨mem_ball_zero_iff.2 (hp ▸ hs1), Or.inl ?_⟩
    exact mem_closedBall_zero_iff.2 ((hs' p hp.le).trans hρ'R).le

/-- Helper (Stage B2): from `λ ≤ 2π/L` to the module-side inequality. -/
theorem gm5_inv_extLen {L : ℝ} (hL : 0 < L) {l : ℝ≥0∞} (h : l ≤ ENNReal.ofReal (2 * π / L)) :
    ENNReal.ofReal (1 / (2 * π) * L) ≤ l⁻¹ := by
  calc ENNReal.ofReal (1 / (2 * π) * L) = (ENNReal.ofReal (2 * π / L))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
        congr 1
        field_simp
    _ ≤ l⁻¹ := ENNReal.inv_le_inv.2 h

/-- Helper (Stage B2; the two-ring comparison). With `φ : 𝔻 → G` conformal, `φ(B̄(0, s')) ⊆ B(0, ρ')`,
`ρ' < R` and `B̄(0, R) ⊆ G`: `mod(B(0,R) \ B̄(0,ρ')) + mod(G \ B̄(0,R)) ≤ (1/2π) log (1/s')` (parallel rule in the
annulus `s' < |z| < 1`, after pulling back by `φ⁻¹`). -/
theorem gm5_key_ineq {G : Set ℂ} {φ : ℂ → ℂ} {R ρ' s' : ℝ} (hφ : IsConformalOnto φ unitDisc G) (hR : 0 < R)
    (hRG : closedBall (0 : ℂ) R ⊆ G) (hbdd : Bornology.IsBounded G)
    (hring : IsRingDomain (toExt (G \ closedBall 0 R))) (hρ' : 0 < ρ') (hρ'R : ρ' < R) (hs0 : 0 < s')
    (hs1 : s' < 1) (hs' : ∀ w : ℂ, ‖w‖ ≤ s' → ‖φ w‖ < ρ') :
    ENNReal.ofReal (1 / (2 * π) * Real.log (R / ρ')) + ringModGM (toExt (G \ closedBall 0 R)) ≤
      ENNReal.ofReal (1 / (2 * π) * Real.log (1 / s')) := by
  have hGo : IsOpen G := hφ.isOpen isOpen_ball
  obtain ⟨r₁, r₂, g, hr₁, hr₁₂, hg, hmod, hin, hout⟩ := gm5_key_model hGo hbdd hR hRG hring
  have hF : IsConformalOnto (Function.invFunOn φ unitDisc) G unitDisc := hφ.symm isOpen_ball
  set F := Function.invFunOn φ unitDisc with hFdef
  have hFφ : ∀ z ∈ unitDisc, F (φ z) = z := fun z hz => hφ.2.1.leftInvOn_invFunOn hz
  have hφF : ∀ u ∈ G, φ (F u) = u := fun u hu =>
    Function.invFunOn_eq (hφ.2.2 ▸ hu : u ∈ φ '' unitDisc)
  have hA'G : annulus ρ' R ⊆ G := fun u hu => hRG (mem_closedBall_zero_iff.2 hu.2.le)
  have hΩo : IsOpen (G \ closedBall 0 R) := hGo.sdiff isClosed_closedBall
  set D₁ := F '' annulus ρ' R with hD₁
  set D₂ := F '' (G \ closedBall 0 R) with hD₂
  set W := annulus s' 1 with hW
  have hg1 : IsConformalOnto F (annulus ρ' R) D₁ := ⟨hF.1.mono hA'G, hF.2.1.mono hA'G, rfl⟩
  have hFΩ : IsConformalOnto F (G \ closedBall 0 R) D₂ := ⟨hF.1.mono sdiff_subset, hF.2.1.mono sdiff_subset, rfl⟩
  have hg2 : IsConformalOnto (fun w => F (g w)) (annulus r₁ r₂) D₂ := hFΩ.comp hg
  have hD₁o : IsOpen D₁ := gm5_image_open hF (gm5_isOpen_annulus _ _) hA'G
  have hD₂o : IsOpen D₂ := gm5_image_open hF hΩo sdiff_subset
  have hFmaps : ∀ u ∈ G, F u ∈ unitDisc := fun u hu => hF.mapsTo hu
  have hinW : ∀ u ∈ G, ρ' ≤ ‖u‖ → F u ∈ W := by
    intro u hu hρu
    refine ⟨?_, mem_ball_zero_iff.1 (hFmaps u hu)⟩
    by_contra hle
    have := hs' _ (not_lt.1 hle)
    rw [hφF u hu] at this
    exact absurd hρu (not_le.2 this)
  have hD₁W : D₁ ⊆ W := by
    rintro _ ⟨u, hu, rfl⟩
    exact hinW u (hA'G hu) hu.1.le
  have hD₂W : D₂ ⊆ W := by
    rintro _ ⟨u, hu, rfl⟩
    refine hinW u hu.1 ?_
    have : R < ‖u‖ := not_le.1 fun h => hu.2 (mem_closedBall_zero_iff.2 h)
    linarith
  have hdisj : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have : v = u := hF.2.1 hv.1 (hA'G hu) huv
    subst this
    exact hv.2 (mem_closedBall_zero_iff.2 hu.2.le)
  obtain ⟨hWo, hWc⟩ := gm5_annulus_oc hs0.le hs1
  set Γ₁ : Set (Set ℂ) := {γ | ∃ t ∈ Ioo ρ' R, γ = F '' sphere 0 t} with hΓ₁
  set Γ₂ : Set (Set ℂ) := {γ | ∃ s ∈ Ioo r₁ r₂, γ = (fun w => F (g w)) '' sphere 0 s} with hΓ₂
  set Γ := separatingFamily W (sphere 0 s') (sphere 0 1) with hΓ
  have hmem₁ : ∀ γ ∈ Γ₁, γ ∈ Γ := by
    rintro _ ⟨t, ht, rfl⟩
    exact gm5_sepW_circle hGo hφ hF hFφ hφF hRG hs0 hs1 hs' ht
  have hmem₂ : ∀ γ ∈ Γ₂, γ ∈ Γ := by
    rintro _ ⟨s, hs, rfl⟩
    exact gm5_sepW_g hGo hbdd hφ hF hFφ hφF hRG hρ'R hs0 hs1 hs' hr₁ hg hs (hin s hs) (hout s hs)
  have hmid₁ : (ρ' + R) / 2 ∈ Ioo ρ' R := ⟨by linarith, by linarith⟩
  have hmid₂ : (r₁ + r₂) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
  have hP₁ : IsPathFamily D₁ Γ₁ :=
    ⟨⟨_, (ρ' + R) / 2, hmid₁, rfl⟩, by
      rintro _ ⟨t, ht, rfl⟩
      exact gm5_circle_pathCurve hρ' hg1 ht⟩
  have hP₂ : IsPathFamily D₂ Γ₂ :=
    ⟨⟨_, (r₁ + r₂) / 2, hmid₂, rfl⟩, by
      rintro _ ⟨s, hs, rfl⟩
      exact gm5_circle_pathCurve hr₁ hg2 hs⟩
  have hPΓ : IsPathFamily W Γ := ⟨⟨_, hmem₁ _ ⟨_, hmid₁, rfl⟩⟩, fun γ hγ => hγ.1⟩
  have hpar := parallel_rule hD₁o hD₂o hdisj ⟨hWo, hWc⟩ (union_subset hD₁W hD₂W) hP₁ hP₂ hPΓ (by
    rintro γ (hγ | hγ)
    · exact ⟨γ, hmem₁ γ hγ, subset_rfl⟩
    · exact ⟨γ, hmem₂ γ hγ, subset_rfl⟩)
  rw [gm5_annulus_sep_inv hs0 hs1] at hpar
  -- the first ring: round annulus `ρ' < |u| < R`
  set C₀ : Set (Set ℂ) := {γ | ∃ t ∈ Ioo ρ' R, γ = sphere 0 t} with hC₀
  have hA'ex : extremalLengthGM D₁ Γ₁ ≤ ENNReal.ofReal (2 * π / Real.log (R / ρ')) := by
    have himg : Γ₁ = image F '' C₀ := by
      ext γ
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨sphere 0 t, ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, rfl⟩
    have h1 : extremalLengthGM D₁ (image F '' C₀) ≤ extremalLengthGM (annulus ρ' R) C₀ :=
      gm4b_extremalLength_image_le (gm5_isOpen_annulus _ _) hg1 (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨isClosed_sphere.measurableSet, fun z hz => by
          rw [mem_sphere_zero_iff_norm] at hz
          exact ⟨hz ▸ ht.1, hz ▸ ht.2⟩⟩)
    have h2 : extremalLengthGM (annulus ρ' R) C₀ ≤ ENNReal.ofReal (2 * π / Real.log (R / ρ')) :=
      gm5_extLen_le (g := id) hρ' hρ'R ⟨differentiableOn_id, Function.injective_id.injOn, image_id _⟩
        (fun s hs => ⟨s, hs, image_id _⟩)
    rw [himg]
    exact h1.trans h2
  have hlogA : 0 < Real.log (R / ρ') := Real.log_pos ((one_lt_div hρ').2 hρ'R)
  have hB₁ := gm5_inv_extLen hlogA hA'ex
  -- the second ring: the model `g`
  set C₁ : Set (Set ℂ) := {γ | ∃ s ∈ Ioo r₁ r₂, γ = g '' sphere 0 s} with hC₁
  have hB₂ : ringModGM (toExt (G \ closedBall 0 R)) ≤ (extremalLengthGM D₂ Γ₂)⁻¹ := by
    have himg : Γ₂ = image F '' C₁ := by
      ext γ
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨g '' sphere 0 s, ⟨s, hs, rfl⟩, (image_comp F g _).symm⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, (image_comp F g _).symm⟩
    have h1 : extremalLengthGM D₂ Γ₂ ≤ extremalLengthGM (G \ closedBall 0 R) C₁ := by
      rw [himg]
      refine gm4b_extremalLength_image_le hΩo hFΩ ?_
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (isClosed_sphere.measurableSet).image_of_continuousOn_injOn
          (hg.1.continuousOn.mono fun z hz => by
            rw [mem_sphere_zero_iff_norm] at hz
            exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩) (hg.2.1.mono fun z hz => by
            rw [mem_sphere_zero_iff_norm] at hz
            exact ⟨hz ▸ hs.1, hz ▸ hs.2⟩)
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_sphere_zero_iff_norm] at hz
        exact hg.mapsTo ⟨hz ▸ hs.1, hz ▸ hs.2⟩
    have h2 : extremalLengthGM (G \ closedBall 0 R) C₁ ≤ ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) :=
      gm5_extLen_le hr₁ hr₁₂ hg (fun s hs => ⟨s, hs, rfl⟩)
    have hlog : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr₁).2 hr₁₂)
    rw [hmod]
    exact (gm5_inv_extLen hlog h2).trans (ENNReal.inv_le_inv.2 h1)
  exact (add_le_add hB₁ hB₂).trans hpar

/-- Helper (Stage B2; the key inequality). For a bounded simply connected `G ∋ 0` with conformal `φ : 𝔻 → G`,
`φ(0) = 0` and `B̄(0, R) ⊆ G` such that `G \ B̄(0, R)` is a ring domain: `mod(G \ B̄(0,R)) + (log R)/2π ≤
(1/2π) log |φ'(0)|`, the module being finite. (This is (4.4) and the limit formula for `M_ρ(G)` at `ρ = R`.) -/
theorem gm5_key {G : Set ℂ} {φ : ℂ → ℂ} {R : ℝ} (hφ : IsConformalOnto φ unitDisc G) (hφ0 : φ 0 = 0) (hR : 0 < R)
    (hRG : closedBall (0 : ℂ) R ⊆ G) (hbdd : Bornology.IsBounded G)
    (hring : IsRingDomain (toExt (G \ closedBall 0 R))) :
    ringModGM (toExt (G \ closedBall 0 R)) < ⊤ ∧
      (ringModGM (toExt (G \ closedBall 0 R))).toReal + Real.log R / (2 * π) ≤
        1 / (2 * π) * Real.log ‖deriv φ 0‖ := by
  have hne : deriv φ 0 ≠ 0 :=
    LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hφ.1 hφ.2.1 (mem_ball_self one_pos)
  have hd : DifferentiableAt ℂ φ 0 := hφ.1.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  set c := ‖deriv φ 0‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 hne
  set m := ringModGM (toExt (G \ closedBall 0 R)) with hm
  -- for each `ε > 0`, the two-ring comparison with suitable `ρ'`, `s'`
  have hε : ∀ ε : ℝ, 0 < ε → m ≠ ⊤ ∧ m.toReal + Real.log R / (2 * π) ≤ 1 / (2 * π) * Real.log c + ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hsm⟩ := gm5_phi_small hd hφ0 hne hε
    set k : ℝ := (1 + 2 * ε) * c with hk
    have hk0 : 0 < k := by positivity
    set ρ' : ℝ := min (R / 2) (k * min δ₁ (1 / 2)) with hρ'
    have hρ'0 : 0 < ρ' := lt_min (by linarith) (by positivity)
    have hρ'R : ρ' < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set s' : ℝ := ρ' / k with hs'
    have hs0 : 0 < s' := by positivity
    have hs'm : s' ≤ min δ₁ (1 / 2) := by
      rw [hs', div_le_iff₀ hk0, mul_comm]
      exact min_le_right _ _
    have hs1 : s' < 1 := lt_of_le_of_lt (hs'm.trans (min_le_right _ _)) (by norm_num)
    have hsφ : ∀ w : ℂ, ‖w‖ ≤ s' → ‖φ w‖ < ρ' := by
      intro w hw
      have h1 := hsm w (hw.trans (hs'm.trans (min_le_left _ _)))
      calc ‖φ w‖ ≤ (1 + ε) * c * ‖w‖ := h1
        _ ≤ (1 + ε) * c * s' := by gcongr
        _ < ρ' := by
          rw [hs', hk]
          have : (1 + ε) * c * ρ' < (1 + 2 * ε) * c * ρ' := by
            have : 0 < c * ρ' := by positivity
            nlinarith
          calc (1 + ε) * c * (ρ' / ((1 + 2 * ε) * c)) = ((1 + ε) * c * ρ') / ((1 + 2 * ε) * c) := by ring
            _ < ((1 + 2 * ε) * c * ρ') / ((1 + 2 * ε) * c) := by
              apply div_lt_div_of_pos_right this (by positivity)
            _ = ρ' := by field_simp
    have hineq := gm5_key_ineq hφ hR hRG hbdd hring hρ'0 hρ'R hs0 hs1 hsφ
    have hlt : m ≠ ⊤ := by
      intro htop
      rw [← hm, htop, add_top] at hineq
      exact absurd hineq (by simp)
    refine ⟨hlt, ?_⟩
    have ha : 0 ≤ 1 / (2 * π) * Real.log (R / ρ') :=
      mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hρ'0).2 hρ'R.le))
    have hb : 0 ≤ 1 / (2 * π) * Real.log (1 / s') :=
      mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hs0).2 hs1.le))
    have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hineq
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hlt, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at htr
    -- `log(R/ρ') + 2π m ≤ log(1/s') = log k - log ρ'`
    have e1 : Real.log (R / ρ') = Real.log R - Real.log ρ' := Real.log_div hR.ne' hρ'0.ne'
    have e2 : Real.log (1 / s') = Real.log k - Real.log ρ' := by
      rw [hs', one_div, inv_div, Real.log_div hk0.ne' hρ'0.ne']
    have e3 : Real.log k = Real.log (1 + 2 * ε) + Real.log c := by
      rw [hk, Real.log_mul (by positivity) hc0.ne']
    have e4 : Real.log (1 + 2 * ε) ≤ 2 * ε := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * ε by positivity)
      linarith
    rw [e1, e2, e3] at htr
    have hπ : 0 < 2 * π := by positivity
    have : m.toReal + Real.log R / (2 * π) ≤ (Real.log (1 + 2 * ε) + Real.log c) / (2 * π) := by
      have h5 : 1 / (2 * π) * (Real.log R - Real.log ρ') + m.toReal ≤
          1 / (2 * π) * (Real.log (1 + 2 * ε) + Real.log c - Real.log ρ') := htr
      have h6 : Real.log R / (2 * π) = 1 / (2 * π) * Real.log R := by ring
      have h7 : (Real.log (1 + 2 * ε) + Real.log c) / (2 * π) = 1 / (2 * π) * (Real.log (1 + 2 * ε) + Real.log c) := by
        ring
      rw [h6, h7]
      nlinarith
    refine this.trans ?_
    have : (Real.log (1 + 2 * ε) + Real.log c) / (2 * π) ≤ (2 * ε + Real.log c) / (2 * π) := by
      gcongr
    refine this.trans ?_
    have hε' : 2 * ε / (2 * π) ≤ ε := by
      rw [div_le_iff₀ hπ]
      nlinarith [Real.pi_gt_three]
    calc (2 * ε + Real.log c) / (2 * π) = 2 * ε / (2 * π) + 1 / (2 * π) * Real.log c := by ring
      _ ≤ _ := by linarith
  refine ⟨lt_top_iff_ne_top.2 (hε 1 one_pos).1, ?_⟩
  exact le_of_forall_pos_le_add fun ε hε0 => (hε ε hε0).2

/-- **Theorem 4.1** (Teichmüller's Modulsatz, Ch. V §4; cited at P1:7196, 7248, in the proof of Corollary 4.3,
P1:7413, in the proof of Theorem 5.7, P2:30, in the Notes, P2:421, in Exercise V.4, P2:521, 559, and in Exercise IV.5,
P1:6568, "a weak version of Theorem 4.1 of Chapter V 'Der Modulsatz'"). In the situation of (4.1), if
(4.2) `mod(Ω₁) + mod(Ω₂) ≥ (1/2π) log(R₂/R₁) − δ` and if `δ > 0` is sufficiently small, then there is a `C < ∞`
independent of `Ω` and `δ` [the glyph `Ω` is lost in the OCR, P1:7190] such that
(4.3) `sup_J |z| / inf_J |z| ≤ 1 + C √(δ log(1/δ))`.
Modelling: the configuration is `IsModulsatzConfig`; `δ₀` and `C` are absolute constants, chosen before the
configuration (module docstring; the constant does not depend on `R₁`, `R₂` either, since the theorem is derived from
Theorem 4.2 through (4.4)); (4.2) is stated in `[0, ∞]` with `ENNReal.ofReal` of the right side, which is equivalent
to the real inequality (when `(1/2π) log(R₂/R₁) − δ ≤ 0` both hold trivially); `inf_J |z| ≥ R₁ > 0`. The formulas
(4.2) and (4.3) were checked against the equation images. -/
theorem thm5_4_1 :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∃ C : ℝ, ∀ (R₁ R₂ : ℝ) (J Ω₁ Ω₂ : Set ℂ), IsModulsatzConfig R₁ R₂ J Ω₁ Ω₂ →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ENNReal.ofReal (1 / (2 * π) * Real.log (R₂ / R₁) - δ) ≤ ringModGM (toExt Ω₁) + ringModGM (toExt Ω₂) →
          sSup ((fun z : ℂ => ‖z‖) '' J) / sInf ((fun z : ℂ => ‖z‖) '' J) ≤
            1 + C * Real.sqrt (δ * Real.log (1 / δ)) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, C, hmain⟩ := thm5_4_2
  refine ⟨δ₀, hδ₀, hδ₀1, C, ?_⟩
  intro R₁ R₂ J Ω₁ Ω₂ hconf δ hδ hδδ₀ h42
  have hR1 : 0 < R₁ := hconf.1
  have hR12 : R₁ < R₂ := hconf.2.1
  have hR2 : 0 < R₂ := hR1.trans hR12
  have hJc : IsCompact J := hconf.2.2.1
  have hJk : IsConnected J := hconf.2.2.2.1
  obtain ⟨G₁, G₂, h1, h2, hd, h0, hinf, hG₁, hG₂⟩ := gm5_conf_G hconf
  refine hmain J G₁ G₂ hJc hJk h1 h2 hd h0 hinf δ hδ hδδ₀ ?_
  obtain ⟨φ₁, φ₂, hc1, h10, hc2, h20⟩ := gm5_exists_maps hJc hJk h1 h2 hd h0 hinf
  have hΩ₁A := (gm5_conf_comp hconf (Or.inl rfl)).2.2
  have hΩ₂A := (gm5_conf_comp hconf (Or.inr rfl)).2.2
  have hring₁ := gm5_conf_ring hconf (Or.inl rfl)
  obtain ⟨hring₂, hmod₂⟩ := gm5_inv_ring_mod hconf
  have hinv := gm5_inv_annulus hR1 hΩ₂A
  -- the side of `0`
  have e1 : finitePart G₁ \ closedBall 0 R₁ = Ω₁ := by
    rw [hG₁]
    ext z
    constructor
    · rintro ⟨hz | hz, hz'⟩
      · exact absurd hz hz'
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, fun h => absurd (mem_closedBall_zero_iff.1 h) (not_le.2 (hΩ₁A hz).1)⟩
  have hb1 : Bornology.IsBounded (finitePart G₁) := by
    rw [hG₁]
    exact isBounded_closedBall.union ((isBounded_closedBall (x := (0 : ℂ)) (r := R₂)).subset fun z hz =>
      mem_closedBall_zero_iff.2 (hΩ₁A hz).2.le)
  have hRG1 : closedBall (0 : ℂ) R₁ ⊆ finitePart G₁ := by
    rw [hG₁]
    exact subset_union_left
  obtain ⟨hlt1, hk1⟩ := gm5_key hc1 h10 hR1 hRG1 hb1 (by rw [e1]; exact hring₁)
  rw [e1] at hlt1 hk1
  -- the side of `∞`
  have hc2' : IsConformalOnto φ₂ unitDisc (closedBall 0 R₂⁻¹ ∪ (fun z : ℂ => z⁻¹) '' Ω₂) := hG₂ ▸ hc2
  have hR2i : 0 < R₂⁻¹ := inv_pos.2 hR2
  have e2 : (closedBall 0 R₂⁻¹ ∪ (fun z : ℂ => z⁻¹) '' Ω₂) \ closedBall 0 R₂⁻¹ = (fun z : ℂ => z⁻¹) '' Ω₂ := by
    ext z
    constructor
    · rintro ⟨hz | hz, hz'⟩
      · exact absurd hz hz'
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, fun h => absurd (mem_closedBall_zero_iff.1 h) (not_le.2 (hinv hz).1)⟩
  have hb2 : Bornology.IsBounded (closedBall 0 R₂⁻¹ ∪ (fun z : ℂ => z⁻¹) '' Ω₂) :=
    isBounded_closedBall.union ((isBounded_closedBall (x := (0 : ℂ)) (r := R₁⁻¹)).subset fun z hz =>
      mem_closedBall_zero_iff.2 (hinv hz).2.le)
  have hRG2 : closedBall (0 : ℂ) R₂⁻¹ ⊆ closedBall 0 R₂⁻¹ ∪ (fun z : ℂ => z⁻¹) '' Ω₂ := subset_union_left
  obtain ⟨hlt2, hk2⟩ := gm5_key hc2' h20 hR2i hRG2 hb2 (by rw [e2]; exact hring₂)
  rw [e2, hmod₂] at hlt2 hk2
  -- the reduced moduli
  rw [reducedModulusInf, gm5_red_eq hc1 h10, gm5_red_eq hc2 h20]
  have hx := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hlt1.ne, hlt2.ne⟩) h42
  rw [ENNReal.toReal_add hlt1.ne hlt2.ne, ENNReal.toReal_ofReal'] at hx
  have hx' := (le_max_left _ _).trans hx
  have e3 : 1 / (2 * π) * Real.log (R₂ / R₁) = Real.log R₂ / (2 * π) - Real.log R₁ / (2 * π) := by
    rw [Real.log_div hR2.ne' hR1.ne']
    ring
  rw [Real.log_inv, neg_div] at hk2
  rw [e3] at hx'
  linarith

/-- **Corollary 4.3** (Ch. V §4; cited at P1:7357, in Exercise V.4, P2:521, and in Chapter VIII, P2:4233 "by Corollary
V.4.3 or Exercise V.4" and P2:4537, where it is applied to a connected piece of `∂Ω` in an annulus). Let `R > 1`, let
`Ω = {1 < |z| < R}` be the annulus with boundary curves `Γ₁ = {|z| = 1}` and `Γ₂ = {|z| = R}`, let `σ` be a curve in `Ω`
joining `1 ∈ Γ₁` to `Γ₂`, and assume (4.10) `sup_σ |arg z| = ε`. If `ε < ε₀ < π`, there is a constant `C = C(ε₀)` such
that if `1 < R ≤ e` then (4.11) `d_{Ω∖σ}(Γ₁, Γ₂) ≥ (1/2π) log R + Cε²/log(1/ε)`, while if `R > e` then (4.12)
`d_{Ω∖σ}(Γ₁, Γ₂) ≥ (1/2π) log R + (C/log R) ε²/(log log R + log(1/ε))`.
Modelling: `σ = f([0, 1])` for a continuous `f` with `f(0) = 1`, `|f(1)| = R` and `f((0, 1)) ⊆ Ω` (a curve joining `1`
to `Γ₂` in `Ω`; it need not be simple); `arg` is the principal argument (`σ` does not meet the negative axis, as
`ε < π`); `ε` is given by (4.10); one constant `C > 0` serves both cases, as in the book (a constant `C ≤ 0` would make
the claims weaker than (4.13)); `ε > 0` (for `ε = 0` the claims are the equality case of (4.13)); the bounds are
compared with `d_{Ω∖σ}` through `ENNReal.ofReal`, which is harmless when a bound is negative (then the book's inequality
is trivial too). The formulas (4.10)–(4.12) were checked against the equation images.
[CORRECTION] Corollary 4.3 is false as printed. (i) (4.11) cannot hold with `C` independent of `R ∈ (1, e]`: for
`σ = {(1 + t(R − 1))e^{iεt} : 0 ≤ t ≤ 1}` the radial segments at angles `θ ∈ (ε, 2π)` join `Γ₁` to `Γ₂` in `Ω ∖ σ`, so
`d_{Ω∖σ}(Γ₁, Γ₂) ≤ log R/(2π − ε)`, and the excess over `(1/2π) log R` is at most `ε log R/(2π(2π − ε)) → 0` as
`R → 1⁺`; the proof's "`≥ log B/2π − Cδ`" (P1:7386) hides `C = 2π²/(log R)²`. (ii) For `ε₀ ≥ 1` the right sides of
(4.11) (`ε → 1⁻`) and (4.12) (`ε → (log R)⁻`, `e < R < e^{ε₀}`) tend to `+∞`, while `d_{Ω∖σ}(Γ₁, Γ₂) ≤ log R/(2π − 2ε)`.
Stated for `ε₀ < 1` and, in (4.11), for `R₀ ≤ R ≤ e` with `C = C(ε₀, R₀)`: the proof's constants are uniform there, and
the case `R > e` of the proof uses (4.11) only for `R ∈ (√e, e]`. The uses in Ch. VIII (P2:4233, 4537) also need angles
`1 ≤ sup|arg| < π`, which the printed formulas cannot express (their right sides blow up as `ε → 1`); the book's proof
gives `ε ≤ C√(δ log(1/δ))` for all `ε < ε₀ < π`, but no corrected formula of the book states it. Chapter VIII applies
the corollary to continua that need not be path images (P2:4233, 4537); that reading is Part D's. -/
theorem cor5_4_3 {ε₀ R₀ : ℝ} (hε₀ : ε₀ < 1) (hR₀ : 1 < R₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (f : ℝ → ℂ) (ε : ℝ), 1 < R → ContinuousOn f (Icc 0 1) → f 0 = 1 → ‖f 1‖ = R →
      f '' Ioo 0 1 ⊆ annulus 1 R → ε = sSup ((fun z : ℂ => |arg z|) '' (f '' Icc 0 1)) → 0 < ε → ε < ε₀ →
        (R₀ ≤ R → R ≤ Real.exp 1 →
          ENNReal.ofReal (1 / (2 * π) * Real.log R + C * ε ^ 2 / Real.log (1 / ε)) ≤
            extremalDistGM (annulus 1 R \ f '' Icc 0 1) (sphere 0 1) (sphere 0 R)) ∧
        (Real.exp 1 < R →
          ENNReal.ofReal (1 / (2 * π) * Real.log R +
              C / Real.log R * (ε ^ 2 / (Real.log (Real.log R) + Real.log (1 / ε)))) ≤
            extremalDistGM (annulus 1 R \ f '' Icc 0 1) (sphere 0 1) (sphere 0 R)) := by
  sorry

end GarnettMarshall2005
