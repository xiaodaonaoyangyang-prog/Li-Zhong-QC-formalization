import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain

/-!
# Lehto–Virtanen, Chapter I §7: Characterization of quasiconformality with the help of ring domains

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §7
(pp. 38–41; `full.md` P1:1032–1136).

The module inequalities are multiplied out (`M(B) ≤ K M(B′)` for `M(B)/K ≤ M(B′)`), in `ℝ≥0∞`.

* Definition (maximal dilatation of ring domains, §7.1) — omitted: not cited; its content is the ring
  characterization below
* Theorem 7.1 (§7.1) — `thm1_7_1`
* Theorem 7.2 (§7.2) — `thm1_7_2`
* Unlabelled (§7.2, P1:1135): characterization of `K`-quasiconformality by ring domains —
  `isKQuasiconformal_iff_ring`
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-- Helper (Ch. I §7, Theorem 7.4 without closure). Components of the complement of a set `F ⊆ ℂ̄` agree with the
equality of the classes in `ConnectedComponents ↥F`. -/
theorem lv17_cc_eq_iff {F : Set ExtPlane} {x y : ExtPlane} (hx : x ∈ F) (hy : y ∈ F) :
    (ConnectedComponents.mk (⟨x, hx⟩ : F) = ConnectedComponents.mk (⟨y, hy⟩ : F)) ↔
      connectedComponentIn F x = connectedComponentIn F y := by
  rw [ConnectedComponents.coe_eq_coe, connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy]
  exact ⟨fun h => by rw [h], fun h => Subtype.val_injective.image_injective h⟩

/-- Helper (Ch. I §7, Theorem 7.4 without closure). The circle `|z| = r` separates `0` from `∞` in the complement of an
annulus `a < |z| < b`, `a < r < b`. -/
theorem lv17_annulus_compl_ne {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    connectedComponentIn (toExt (LiZhongQC.annulus a b))ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt (LiZhongQC.annulus a b))ᶜ extInf := by
  intro heq
  set r : ℝ := (a + b) / 2 with hr
  set E1 := (toExt (LiZhongQC.annulus a b))ᶜ with hE1
  have h0 : ((0 : ℂ) : ExtPlane) ∈ E1 := by
    rw [hE1, LiZhongQC.coe_mem_compl_toExt_iff]
    intro h
    have := h.1
    simp at this
    linarith
  have hinf : extInf ∈ E1 := LiZhongQC.extInf_mem_compl_toExt _
  have hS : IsPreconnected (connectedComponentIn E1 ((0 : ℂ) : ExtPlane)) := isPreconnected_connectedComponentIn
  have hsub : connectedComponentIn E1 ((0 : ℂ) : ExtPlane) ⊆ E1 := connectedComponentIn_subset _ _
  have h0S : ((0 : ℂ) : ExtPlane) ∈ connectedComponentIn E1 ((0 : ℂ) : ExtPlane) := mem_connectedComponentIn h0
  have hiS : extInf ∈ connectedComponentIn E1 ((0 : ℂ) : ExtPlane) := by
    rw [heq]; exact mem_connectedComponentIn hinf
  set O1 : Set ExtPlane := ((↑) : ℂ → ExtPlane) '' Metric.ball (0 : ℂ) r with hO1
  set O2 : Set ExtPlane := (((↑) : ℂ → ExtPlane) '' Metric.closedBall (0 : ℂ) r)ᶜ with hO2
  have hO1o : IsOpen O1 := OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
  have hO2o : IsOpen O2 :=
    (((isCompact_closedBall (0 : ℂ) r).image OnePoint.continuous_coe).isClosed).isOpen_compl
  have hcov : connectedComponentIn E1 ((0 : ℂ) : ExtPlane) ⊆ O1 ∪ O2 := by
    intro x hx
    have hxE := hsub hx
    induction x using OnePoint.rec with
    | infty =>
      right
      rintro ⟨w, -, hw⟩
      exact OnePoint.coe_ne_infty w hw
    | coe w =>
      have hw : w ∉ LiZhongQC.annulus a b := LiZhongQC.coe_mem_compl_toExt_iff.1 hxE
      by_cases hwr : ‖w‖ < r
      · left; exact ⟨w, by simpa using hwr, rfl⟩
      · right
        rintro ⟨v, hv, hvw⟩
        have hvw' := OnePoint.coe_injective hvw
        subst hvw'
        have hv' : ‖v‖ ≤ r := by simpa using hv
        have : ‖v‖ = r := le_antisymm hv' (not_lt.1 hwr)
        apply hw
        refine ⟨?_, ?_⟩ <;> simp only [this, hr] <;> linarith
  have hdisj : Disjoint O1 O2 := by
    rw [Set.disjoint_left]
    rintro x ⟨w, hw, rfl⟩ h2
    exact h2 ⟨w, Metric.ball_subset_closedBall hw, rfl⟩
  have hl := hS.subset_left_of_subset_union hO1o hO2o hdisj hcov ⟨_, h0S, ⟨0, by simp [hr]; linarith, rfl⟩⟩
  have : extInf ∈ O1 := hl hiS
  obtain ⟨w, -, hw⟩ := this
  exact OnePoint.coe_ne_infty w hw


/-- Helper (Ch. I §7, Theorem 7.4 without closure). An annulus `a < |z| < b` contained in a doubly connected domain
`U ∌ 0` of the plane separates the two components of the complement of `U` (the one through `0` and the one through
`∞`). -/
theorem lv17_sep_annulus {U : Set ℂ} {a b : ℝ} (hU : LiZhongQC.IsDoublyConnected U) (h0 : (0 : ℂ) ∉ U)
    (ha : 0 < a) (hab : a < b) (hsub : LiZhongQC.annulus a b ⊆ U) :
    LiZhongQC.SeparatesComplement (LiZhongQC.annulus a b) U := by
  set E := (toExt U)ᶜ with hE
  set E1 := (toExt (LiZhongQC.annulus a b))ᶜ with hE1
  have hEE1 : E ⊆ E1 := compl_subset_compl.2 (image_mono hsub)
  have h0E : ((0 : ℂ) : ExtPlane) ∈ E := LiZhongQC.coe_mem_compl_toExt_iff.2 h0
  have hiE : extInf ∈ E := LiZhongQC.extInf_mem_compl_toExt _
  have hne := lv17_annulus_compl_ne ha hab
  -- the two classes of `0` and `∞` in the complement of `U` differ
  have hc0i : ConnectedComponents.mk (⟨((0 : ℂ) : ExtPlane), h0E⟩ : E) ≠
      ConnectedComponents.mk (⟨extInf, hiE⟩ : E) := by
    intro h
    rw [lv17_cc_eq_iff] at h
    apply hne
    have h1 : extInf ∈ connectedComponentIn E1 ((0 : ℂ) : ExtPlane) :=
      connectedComponentIn_mono _ hEE1 (h ▸ mem_connectedComponentIn hiE)
    exact connectedComponentIn_eq h1
  have hcard : Nat.card (ConnectedComponents ↥E) = 2 := hU.2.2
  obtain ⟨p, q, hpq, hpqU⟩ := Nat.card_eq_two_iff.1 hcard
  have hmem : ∀ c : ConnectedComponents ↥E, c = p ∨ c = q := fun c => by
    have : c ∈ ({p, q} : Set (ConnectedComponents ↥E)) := hpqU ▸ mem_univ c
    simpa using this
  intro x hx y hy hxy
  have hcxy : ConnectedComponents.mk (⟨x, hx⟩ : E) ≠ ConnectedComponents.mk (⟨y, hy⟩ : E) := fun h =>
    hxy ((lv17_cc_eq_iff hx hy).1 h)
  -- `x` lies with `0` and `y` with `∞`, or conversely
  have hcase : (ConnectedComponents.mk (⟨x, hx⟩ : E) = ConnectedComponents.mk (⟨((0 : ℂ) : ExtPlane), h0E⟩ : E) ∧
      ConnectedComponents.mk (⟨y, hy⟩ : E) = ConnectedComponents.mk (⟨extInf, hiE⟩ : E)) ∨
      (ConnectedComponents.mk (⟨x, hx⟩ : E) = ConnectedComponents.mk (⟨extInf, hiE⟩ : E) ∧
      ConnectedComponents.mk (⟨y, hy⟩ : E) = ConnectedComponents.mk (⟨((0 : ℂ) : ExtPlane), h0E⟩ : E)) := by
    rcases hmem (ConnectedComponents.mk (⟨x, hx⟩ : E)) with h1 | h1 <;>
    rcases hmem (ConnectedComponents.mk (⟨y, hy⟩ : E)) with h2 | h2 <;>
    rcases hmem (ConnectedComponents.mk (⟨((0 : ℂ) : ExtPlane), h0E⟩ : E)) with h3 | h3 <;>
    rcases hmem (ConnectedComponents.mk (⟨extInf, hiE⟩ : E)) with h4 | h4 <;>
    first
      | (exfalso; exact hcxy (h1.trans h2.symm))
      | (exfalso; exact hc0i (h3.trans h4.symm))
      | (left; exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩)
      | (right; exact ⟨h1.trans h4.symm, h2.trans h3.symm⟩)
  -- transport to the complement of the annulus
  have key : ∀ {z : ExtPlane} (hz : z ∈ E) {t : ExtPlane} (ht : t ∈ E),
      ConnectedComponents.mk (⟨z, hz⟩ : E) = ConnectedComponents.mk (⟨t, ht⟩ : E) →
        connectedComponentIn E1 z = connectedComponentIn E1 t := by
    intro z hz t ht h
    have hc := (lv17_cc_eq_iff hz ht).1 h
    have : t ∈ connectedComponentIn E1 z :=
      connectedComponentIn_mono _ hEE1 (by rw [hc]; exact mem_connectedComponentIn ht)
    exact connectedComponentIn_eq this
  refine ⟨x, hEE1 hx, y, hEE1 hy, connectedComponentIn_mono _ hEE1, connectedComponentIn_mono _ hEE1, ?_⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [key hx h0E h1, key hy hiE h2]; exact hne
  · rw [key hx hiE h1, key hy h0E h2]; exact hne.symm


/-- Helper (Ch. I §7, Theorem 7.4 without closure). A `K`-quasiconformal mapping of an annulus `1 < |z| < R` cannot map it
onto a set `S` with `0 ∉ S` which contains the punctured disc `0 < |z| < 1`: the images of the sub-annuli
`a < |z| < b` have module `≤ K log (b/a) ≤ K log R` (Theorem 7.4), but contain the annulus `ρ < |z| < 1/2` for each `ρ` and
all `a, b` close enough to `1, R`, hence have module `≥ log (1/(2ρ))` (Theorem 4.10), which is unbounded as `ρ → 0`. -/
theorem lv17_no_degenerate_image {G : ℂ → ℂ} {R K : ℝ} (hR : 1 < R) (hG : LiZhongQC.IsKQC G (LiZhongQC.annulus 1 R) K)
    (hT0 : (0 : ℂ) ∉ G '' LiZhongQC.annulus 1 R) (hT : LiZhongQC.annulus 0 1 ⊆ G '' LiZhongQC.annulus 1 R) : False := by
  have hK1 : 1 ≤ K := hG.2.1
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨hc, hi, himg, hcinv⟩ := hG.2.2.1
  set A := LiZhongQC.annulus 1 R with hA
  set S := G '' A with hS
  have hdcA : ∀ {a b : ℝ}, 0 < a → a < b → LiZhongQC.IsDoublyConnected (LiZhongQC.annulus a b) := fun {a b} ha hab => by
    have := LiZhongQC.nf_g_isDoublyConnected_annulusAt 0 ha hab
    simpa [LiZhongQC.annulusAt, LiZhongQC.annulus] using this
  have hmain : ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 → Real.log (1 / 2 / ρ) ≤ K * Real.log R := by
    intro ρ hρ hρ2
    set C : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 2) ∩ (Metric.ball (0 : ℂ) ρ)ᶜ with hC
    have hCc : IsCompact C := (isCompact_closedBall (0 : ℂ) (1 / 2)).inter_right Metric.isOpen_ball.isClosed_compl
    have hCT : C ⊆ LiZhongQC.annulus 0 1 := by
      rintro z ⟨h1, h2⟩
      have h1' : ‖z‖ ≤ 1 / 2 := by simpa using h1
      have h2' : ρ ≤ ‖z‖ := by simpa using h2
      exact ⟨by linarith, by linarith⟩
    have hCS : C ⊆ S := hCT.trans hT
    have hCne : C.Nonempty := ⟨(ρ : ℂ), by
      refine ⟨?_, ?_⟩
      · simp [abs_of_pos hρ]; linarith
      · simp [abs_of_pos hρ]⟩
    set K' : Set ℂ := Function.invFunOn G A '' C with hK'
    have hK'c : IsCompact K' := hCc.image_of_continuousOn (hcinv.mono hCS)
    have hK'A : K' ⊆ A := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, hxz⟩ := hCS hz
      exact Function.invFunOn_mem ⟨x, hx, hxz⟩
    obtain ⟨m, hm, hmin⟩ := hK'c.exists_isMinOn (hCne.image _) (continuous_norm.continuousOn)
    obtain ⟨M, hM, hmax⟩ := hK'c.exists_isMaxOn (hCne.image _) (continuous_norm.continuousOn)
    have hm1 : 1 < ‖m‖ := (hK'A hm).1
    have hMR : ‖M‖ < R := (hK'A hM).2
    have hmM : ‖m‖ ≤ ‖M‖ := hmin hM
    set a : ℝ := (1 + ‖m‖) / 2 with ha
    set b : ℝ := (‖M‖ + R) / 2 with hb
    have ha1 : 1 < a := by rw [ha]; linarith
    have hab : a < b := by rw [ha, hb]; linarith
    have hbR : b < R := by rw [hb]; linarith
    have hK'ab : K' ⊆ LiZhongQC.annulus a b := fun k hk =>
      ⟨by have := hmin hk; simp only [Set.mem_ofPred_eq] at this; rw [ha]; linarith,
       by have := hmax hk; simp only [Set.mem_ofPred_eq] at this; rw [hb]; linarith⟩
    have hsubU : LiZhongQC.annulus ρ (1 / 2) ⊆ G '' LiZhongQC.annulus a b := by
      intro z hz
      have hzC : z ∈ C := ⟨by simpa using hz.2.le, by simpa using hz.1.le⟩
      obtain ⟨x, hx, hxz⟩ := hCS hzC
      refine ⟨Function.invFunOn G A z, hK'ab ⟨z, hzC, rfl⟩, ?_⟩
      exact Function.invFunOn_eq ⟨x, hx, hxz⟩
    have hBD : closure (toExt (LiZhongQC.annulus a b)) ⊆ toExt A := by
      have hbdd : Bornology.IsBounded (LiZhongQC.annulus a b) :=
        (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := b)).subset fun z hz => by
          simpa using hz.2.le
      rw [LiZhongQC.closure_toExt_eq_toExt_closure_of_isBounded hbdd]
      refine image_mono ?_
      have hcl : closure (LiZhongQC.annulus a b) ⊆ {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} :=
        closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
          ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      exact hcl.trans fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
    obtain ⟨hdcU, -, hup⟩ := LiZhongQC.thm7_4_dcModulus_quasi_invariance hG (hdcA (by linarith) hab) hBD
    have h0U : (0 : ℂ) ∉ G '' LiZhongQC.annulus a b := fun h =>
      hT0 (image_mono (fun z hz => (⟨by linarith [hz.1], by linarith [hz.2]⟩ : z ∈ A)) h)
    have hsep := lv17_sep_annulus hdcU h0U hρ hρ2 hsubU
    have hmono := LiZhongQC.thm4_10_dcModulus_mono hdcU (hdcA hρ hρ2) hsubU hsep
    rw [LiZhongQC.dcModulus_annulus hρ hρ2] at hmono
    rw [LiZhongQC.dcModulus_annulus (by linarith) hab] at hup
    have hlogpos : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have h1 := hmono.trans hup
    rw [← ENNReal.ofReal_mul hK0, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hlogpos)] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hK0)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  set ρ : ℝ := Real.exp (-(K * Real.log R + 1)) / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ2 : ρ < 1 / 2 := by
    rw [hρ]
    have : Real.exp (-(K * Real.log R + 1)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 ≤ K * Real.log R := mul_nonneg hK0 (Real.log_nonneg hR.le)
      linarith
    linarith
  have h := hmain ρ hρ0 hρ2
  have hval : Real.log (1 / 2 / ρ) = K * Real.log R + 1 := by
    rw [hρ, show (1 : ℝ) / 2 / (Real.exp (-(K * Real.log R + 1)) / 2) = Real.exp (K * Real.log R + 1) by
      rw [Real.exp_neg]; field_simp, Real.log_exp]
  linarith

/-- Helper (Ch. I §7, ring-module bridge). A homeomorphism of `ℂ̄` preserves the number of components of the complement
of a set. -/
theorem lv17_card_cc_image (e : ExtPlane ≃ₜ ExtPlane) (B : Set ExtPlane) :
    Nat.card (ConnectedComponents ↥(e '' B)ᶜ) = Nat.card (ConnectedComponents ↥Bᶜ) := by
  have h : (e '' B)ᶜ = e '' Bᶜ := (image_compl_eq e.bijective).symm
  let H : ↥Bᶜ ≃ₜ ↥(e '' B)ᶜ := (e.image Bᶜ).trans (Homeomorph.setCongr h.symm)
  refine Nat.card_congr
    { toFun := H.symm.continuous.connectedComponentsMap
      invFun := H.continuous.connectedComponentsMap
      left_inv := fun c => ?_
      right_inv := fun c => ?_ }
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp

/-- Helper (Ch. I §7, ring-module bridge). The module of a ring domain depends only on the set of its canonical
annuli `(r₁, r₂)`. -/
theorem lv17_ringModule_congr {B B' : Set ExtPlane}
    (h : ∀ (r₁ : ℝ) (r₂ : ℝ≥0∞), (∃ f : ExtPlane → ExtPlane, IsCanonicalRingMap B f r₁ r₂) ↔
      ∃ f : ExtPlane → ExtPlane, IsCanonicalRingMap B' f r₁ r₂) : ringModule B = ringModule B' := by
  have hif : (∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ ∧ (r₁ = 0 ∨ r₂ = ⊤)) ↔
      ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B' f r₁ r₂ ∧ (r₁ = 0 ∨ r₂ = ⊤) := by
    constructor
    · rintro ⟨f, r₁, r₂, hc, hd⟩
      obtain ⟨g, hg⟩ := (h r₁ r₂).1 ⟨f, hc⟩
      exact ⟨g, r₁, r₂, hg, hd⟩
    · rintro ⟨f, r₁, r₂, hc, hd⟩
      obtain ⟨g, hg⟩ := (h r₁ r₂).2 ⟨f, hc⟩
      exact ⟨g, r₁, r₂, hg, hd⟩
  have hsup : (⨆ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞) (_ : IsCanonicalRingMap B f r₁ r₂),
        ENNReal.ofReal (Real.log (r₂.toReal / r₁))) =
      ⨆ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞) (_ : IsCanonicalRingMap B' f r₁ r₂),
        ENNReal.ofReal (Real.log (r₂.toReal / r₁)) := by
    apply le_antisymm
    · refine iSup_le fun f => iSup_le fun r₁ => iSup_le fun r₂ => iSup_le fun hc => ?_
      obtain ⟨f', hf'⟩ := (h r₁ r₂).1 ⟨f, hc⟩
      exact le_iSup_of_le f' (le_iSup_of_le r₁ (le_iSup_of_le r₂ (le_iSup_of_le hf' le_rfl)))
    · refine iSup_le fun f => iSup_le fun r₁ => iSup_le fun r₂ => iSup_le fun hc => ?_
      obtain ⟨f', hf'⟩ := (h r₁ r₂).2 ⟨f, hc⟩
      exact le_iSup_of_le f' (le_iSup_of_le r₁ (le_iSup_of_le r₂ (le_iSup_of_le hf' le_rfl)))
  unfold ringModule
  by_cases hd : ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B f r₁ r₂ ∧ (r₁ = 0 ∨ r₂ = ⊤)
  · simp only [hd, hif.1 hd, ite_true]
  · have hd' : ¬ ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap B' f r₁ r₂ ∧
        (r₁ = 0 ∨ r₂ = ⊤) := fun h' => hd (hif.2 h')
    simp only [hd, hd', ite_false, hsup]

/-- Helper (Ch. I §7, ring-module bridge). A conformal mapping of a domain `toExt U` onto `toExt T` (`U, T ⊆ ℂ`) is,
read on `ℂ`, a conformal equivalence of `U` onto `T`. -/
theorem lv17_finite_part {U T : Set ℂ} (hU : IsOpen U) {W : ExtPlane → ExtPlane}
    (hW : IsConformalMap W (toExt U)) (hWi : W '' toExt U = toExt T) :
    LiZhongQC.IsConformalOnto (finiteMap W) U T := by
  have hfin : ∀ z ∈ U, W (z : ExtPlane) = ((finiteMap W z : ℂ) : ExtPlane) := fun z hz => by
    have : W (z : ExtPlane) ∈ toExt T := hWi ▸ mem_image_of_mem W ⟨z, hz, rfl⟩
    obtain ⟨a, -, ha⟩ := this
    simp [finiteMap, finiteValue, ← ha]
  refine ⟨fun z hz => ?_, fun z₁ h₁ z₂ h₂ h => ?_, ?_⟩
  · exact (lv12_differentiableAt_of_localRep hU hfin hz (hW.2.2.2 _ ⟨z, hz, rfl⟩)).differentiableWithinAt
  · have := hW.2.2.1 ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩ (by rw [hfin z₁ h₁, hfin z₂ h₂, h])
    exact OnePoint.coe_injective this
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : W (z : ExtPlane) ∈ toExt T := hWi ▸ mem_image_of_mem W ⟨z, hz, rfl⟩
      obtain ⟨a, ha, hax⟩ := this
      rw [hfin z hz] at hax
      rwa [← OnePoint.coe_injective hax]
    · intro hy
      have : ((y : ℂ) : ExtPlane) ∈ W '' toExt U := hWi ▸ ⟨y, hy, rfl⟩
      obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := this
      exact ⟨z, hz, OnePoint.coe_injective (by rw [← hfin z hz]; exact hx)⟩

/-- Helper (Ch. I §7, ring-module bridge). A conformal equivalence of a domain `V ⊆ ℂ` onto `U`, read on `ℂ̄`, is a
conformal mapping of `toExt V` onto `toExt U`. -/
theorem lv17_lift {h : ℂ → ℂ} {U V : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V)
    (hd : DifferentiableOn ℂ h V) (hb : Set.BijOn h V U) :
    IsConformalMap (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) (toExt V) ∧
      (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) '' toExt V = toExt U := by
  have hVd : IsDomainExt (toExt V) :=
    ⟨OnePoint.isOpen_image_coe.2 hV, hVc.image _ OnePoint.continuous_coe.continuousOn⟩
  refine ⟨lv15_isConformalMap_of_differentiableAt hVd ?_ ?_ finite_empty ?_, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [OnePoint.continuousAt_coe]
    exact OnePoint.continuous_coe.continuousAt.comp (hd.differentiableAt (hV.mem_nhds hζ)).continuousAt
  · rintro _ ⟨ζ₁, h₁, rfl⟩ _ ⟨ζ₂, h₂, rfl⟩ h12
    exact congrArg _ (hb.injOn h₁ h₂ (OnePoint.coe_injective h12))
  · intro ζ hζ _ _
    obtain ⟨u, hu, hue⟩ := hζ
    obtain rfl := OnePoint.coe_injective hue
    have hfm : finiteMap (fun z => ((h (finiteValue z) : ℂ) : ExtPlane)) = h := rfl
    rw [hfm]
    exact hd.differentiableAt (hV.mem_nhds hu)
  · show _ '' (((↑) : ℂ → ExtPlane) '' V) = ((↑) : ℂ → ExtPlane) '' U
    rw [image_image, ← hb.image_eq, image_image]
    rfl

/-- Helper (Ch. I §7, ring-module bridge). The punctured disc `0 < |z| < s` is conformally equivalent to the punctured
unit disc. -/
theorem lv17_annulus_zero_equiv {s : ℝ} (hs : 0 < s) :
    LiZhongQC.ConformallyEquivalent (LiZhongQC.annulus 0 s) LiZhongQC.puncturedDisc := by
  refine ⟨fun z => z / (s : ℂ), ?_, ?_, ?_⟩
  · exact (differentiableOn_id.div_const _)
  · intro z₁ _ z₂ _ h
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    exact (div_left_inj' hs').1 h
  · ext w
    constructor
    · rintro ⟨z, ⟨hz0, hzs⟩, rfl⟩
      show 0 < ‖z / (s : ℂ)‖ ∧ ‖z / (s : ℂ)‖ < 1
      simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
      exact ⟨by positivity, by rw [div_lt_one hs]; exact hzs⟩
    · rintro ⟨hw0, hw1⟩
      refine ⟨w * s, ⟨?_, ?_⟩, ?_⟩
      · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]; positivity
      · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
        nlinarith
      · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        field_simp

/-- Helper (Ch. I §7, ring-module bridge). The exterior `r < |z|` of a disc is conformally equivalent to the punctured
unit disc (by `z ↦ r / z`). -/
theorem lv17_exterior_equiv {r : ℝ} (hr : 0 < r) :
    LiZhongQC.ConformallyEquivalent {z : ℂ | r < ‖z‖} LiZhongQC.puncturedDisc := by
  have hne : ∀ z : ℂ, r < ‖z‖ → z ≠ 0 := fun z hz h0 => by
    rw [h0, norm_zero] at hz; linarith
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨fun z => (r : ℂ) / z, ?_, ?_, ?_⟩
  · intro z hz
    exact (differentiableAt_const _ |>.div differentiableAt_id (hne z hz)).differentiableWithinAt
  · intro z₁ h₁ z₂ h₂ h
    have h1 := hne z₁ h₁
    have h2 := hne z₂ h₂
    field_simp at h
    exact h.symm
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzpos : 0 < ‖z‖ := by simp only [Set.mem_ofPred_eq] at hz; linarith
      show 0 < ‖(r : ℂ) / z‖ ∧ ‖(r : ℂ) / z‖ < 1
      simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact ⟨by positivity, by rw [div_lt_one hzpos]; exact hz⟩
    · rintro ⟨hw0, hw1⟩
      have hw : w ≠ 0 := norm_pos_iff.1 hw0
      refine ⟨(r : ℂ) / w, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        rw [lt_div_iff₀ hw0]; nlinarith
      · field_simp

/-- Helper (Ch. I §7, finite model). A fractional linear transformation is a conformal mapping of every domain of `ℂ̄`. -/
theorem lv17_isConformalMap_mobius {M : ExtPlane → ExtPlane} (hM : IsMobius M) {U : Set ExtPlane}
    (hU : IsDomainExt U) : IsConformalMap M U := by
  obtain ⟨e, rfl, -⟩ := lv15_mobius_homeomorph hM
  exact lv15_isConformalMap_of_differentiableAt hU e.continuous.continuousOn e.injective.injOn finite_empty
    fun ζ _ hζ _ => lv15_differentiableAt_finiteMap_mobius hM hζ

/-- Helper (Ch. I §7, finite model). Every point `p` of `ℂ̄` is carried to `∞` by a fractional linear transformation, a
homeomorphism of `ℂ̄` whose inverse is again a fractional linear transformation. -/
theorem lv17_mobius_to_infty (p : ExtPlane) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, IsMobius ⇑e ∧ IsMobius ⇑e.symm ∧ e p = extInf := by
  have hT : ∃ T : ExtPlane → ExtPlane, IsMobius T ∧ T p = extInf := by
    by_cases hp : p = extInf
    · refine ⟨LiZhongQC.mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
      rw [hp]
      exact LiZhongQC.mobiusExt_infty_of_eq rfl
    · obtain ⟨a, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hp
      exact ⟨LiZhongQC.mobiusExt 0 1 1 (-a), ⟨0, 1, 1, -a, by norm_num, rfl⟩,
        LiZhongQC.mobiusExt_coe_of_eq_zero (by ring)⟩
  obtain ⟨T, hT, hTp⟩ := hT
  obtain ⟨e, rfl, he⟩ := lv15_mobius_homeomorph hT
  exact ⟨e, hT, he, hTp⟩

/-- Helper (Ch. I §7, ring-module bridge). A set `toExt B₀`, `B₀ ⊆ ℂ`, is a ring domain of `ℂ̄` iff `B₀` is a doubly
connected domain in Li Zhong's sense. -/
theorem lv17_isRingDomain_toExt_iff (B₀ : Set ℂ) :
    IsRingDomain (toExt B₀) ↔ LiZhongQC.IsDoublyConnected B₀ := by
  have ho : IsOpen (toExt B₀) ↔ IsOpen B₀ := OnePoint.isOpen_image_coe
  have hc : IsConnected (toExt B₀) ↔ IsConnected B₀ :=
    ⟨fun h => ⟨h.nonempty.of_image,
        OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h.isPreconnected⟩,
      fun h => h.image _ OnePoint.continuous_coe.continuousOn⟩
  unfold IsRingDomain IsNTuplyConnected LiZhongQC.IsDoublyConnected LiZhongQC.IsNConnected IsDomainExt
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h3⟩
    exact ⟨ho.1 h1, hc.1 h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨ho.2 h1, hc.2 h2⟩, one_lt_two, h3⟩

/-- Helper (Ch. I §7, ring-module bridge). The module `M(B)` of a ring domain of the finite plane is Li Zhong's modulus
`dcModulus`: a canonical mapping of `B` onto `{r₁ < |z| < r₂}` is, read on `ℂ`, a conformal equivalence, and the
degenerate cases `r₁ = 0` / `r₂ = ∞` are exactly the infinite modulus (`aqc_dcModulus_eq_top_iff`). -/
theorem lv17_ringModule_toExt {B₀ : Set ℂ} (hB : LiZhongQC.IsDoublyConnected B₀) :
    ringModule (toExt B₀) = LiZhongQC.dcModulus B₀ := by
  have hopen : IsOpen B₀ := hB.1
  have hconn : IsConnected B₀ := hB.2.1
  -- a canonical mapping is a conformal equivalence of `B₀` with the canonical annulus
  have K1 : ∀ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap (toExt B₀) f r₁ r₂ →
      LiZhongQC.ConformallyEquivalent B₀ {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} :=
    fun f r₁ r₂ hc => ⟨_, lv17_finite_part hopen hc.2.2.1 hc.2.2.2⟩
  -- lift of a conformal equivalence to a canonical mapping
  have K2 : ∀ (T : Set ℂ) (r₁ : ℝ) (r₂ : ℝ≥0∞), 0 ≤ r₁ → ENNReal.ofReal r₁ < r₂ →
      T = {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} → LiZhongQC.ConformallyEquivalent B₀ T →
        ∃ f : ExtPlane → ExtPlane, IsCanonicalRingMap (toExt B₀) f r₁ r₂ := by
    rintro T r₁ r₂ h0 h1 rfl ⟨F, hF⟩
    obtain ⟨hW, hWi⟩ := lv17_lift hopen hconn hF.1 ⟨fun x hx => by
        have := mem_image_of_mem F hx
        rwa [hF.2.2] at this, hF.2.1, by rw [Set.SurjOn, hF.2.2]⟩
    exact ⟨_, h0, h1, hW, hWi⟩
  by_cases htop : LiZhongQC.dcModulus B₀ = ⊤
  · -- degenerate: a canonical mapping onto the punctured plane or the punctured disc
    have hnoproper : ¬ ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧
        LiZhongQC.ConformallyEquivalent B₀ (LiZhongQC.annulus r₁ r₂) := by
      rintro ⟨r₁, r₂, h₁, h₂, h⟩
      rw [LiZhongQC.dcModulus_eq_of_equiv hopen h₁ h₂ h] at htop
      exact ENNReal.ofReal_ne_top htop
    have hdeg : ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap (toExt B₀) f r₁ r₂ ∧
        (r₁ = 0 ∨ r₂ = ⊤) := by
      rcases LiZhongQC.thm2_1_canonical_form hB with hP | hP | ⟨r₁, r₂, h₁, h₂, hP⟩
      · obtain ⟨f, hf⟩ := K2 LiZhongQC.puncturedPlane 0 ⊤ le_rfl (by simp) (by
          ext z; simp [LiZhongQC.puncturedPlane, norm_pos_iff]) hP
        exact ⟨f, 0, ⊤, hf, Or.inl rfl⟩
      · obtain ⟨f, hf⟩ := K2 LiZhongQC.puncturedDisc 0 (ENNReal.ofReal 1) le_rfl (by simp) (by
          ext z
          simp only [LiZhongQC.puncturedDisc, LiZhongQC.annulus, Set.mem_ofPred_eq]
          rw [ENNReal.ofReal_lt_ofReal_iff one_pos]) hP
        exact ⟨f, 0, _, hf, Or.inl rfl⟩
      · exact absurd ⟨r₁, r₂, h₁, h₂, hP⟩ hnoproper
    unfold ringModule
    rw [htop]
    simp only [hdeg, ite_true]
  · -- non-degenerate
    have hex : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ LiZhongQC.ConformallyEquivalent B₀ (LiZhongQC.annulus r₁ r₂) := by
      by_contra h
      apply htop
      unfold LiZhongQC.dcModulus
      simp only [h, ite_false]
    obtain ⟨a₁, a₂, ha₁, ha₂, hA⟩ := hex
    have hdc : LiZhongQC.dcModulus B₀ = ENNReal.ofReal (Real.log (a₂ / a₁)) :=
      LiZhongQC.dcModulus_eq_of_equiv hopen ha₁ ha₂ hA
    have hnd : ¬ ∃ (f : ExtPlane → ExtPlane) (r₁ : ℝ) (r₂ : ℝ≥0∞), IsCanonicalRingMap (toExt B₀) f r₁ r₂ ∧
        (r₁ = 0 ∨ r₂ = ⊤) := by
      rintro ⟨f, r₁, r₂, hc, hd⟩
      have h1 := K1 f r₁ r₂ hc
      have h2 : LiZhongQC.ConformallyEquivalent {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂}
          (LiZhongQC.annulus a₁ a₂) := (h1.symm hopen).trans hA
      by_cases hr2 : r₂ = ⊤
      · by_cases hr1 : r₁ = 0
        · apply LiZhongQC.thm2_1_canonical_unique_plane_annulus ha₁ ha₂
          have : {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} = LiZhongQC.puncturedPlane := by
            ext z; simp [hr1, hr2, LiZhongQC.puncturedPlane, norm_pos_iff]
          rwa [this] at h2
        · have hr1pos : 0 < r₁ := lt_of_le_of_ne hc.1 (Ne.symm hr1)
          apply LiZhongQC.thm2_1_canonical_unique_disc_annulus ha₁ ha₂
          have : {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} = {z : ℂ | r₁ < ‖z‖} := by
            ext z; simp [hr2]
          rw [this] at h2
          exact ((lv17_exterior_equiv hr1pos).symm (isOpen_lt continuous_const continuous_norm)).trans h2
      · have hr1 : r₁ = 0 := hd.resolve_right hr2
        have hs : 0 < r₂.toReal := ENNReal.toReal_pos (by
          have := hc.2.1; rw [hr1] at this; simpa using this.ne') hr2
        apply LiZhongQC.thm2_1_canonical_unique_disc_annulus ha₁ ha₂
        have : {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} = LiZhongQC.annulus 0 r₂.toReal := by
          ext z
          simp only [hr1, Set.mem_ofPred_eq, LiZhongQC.annulus]
          rw [← ENNReal.ofReal_toReal hr2, ENNReal.ofReal_lt_ofReal_iff hs, ENNReal.toReal_ofReal hs.le]
        rw [this] at h2
        exact ((lv17_annulus_zero_equiv hs).symm (LiZhongQC.isOpen_annulus 0 _)).trans h2
    unfold ringModule
    simp only [hnd, ite_false]
    rw [hdc]
    apply le_antisymm
    · refine iSup_le fun f => iSup_le fun r₁ => iSup_le fun r₂ => iSup_le fun hc => ?_
      have hr2 : r₂ ≠ ⊤ := fun h => hnd ⟨f, r₁, r₂, hc, Or.inr h⟩
      have hr1 : r₁ ≠ 0 := fun h => hnd ⟨f, r₁, r₂, hc, Or.inl h⟩
      have hr1pos : 0 < r₁ := lt_of_le_of_ne hc.1 (Ne.symm hr1)
      have hlt : r₁ < r₂.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hc.1 hr2).1 hc.2.1
      have h1 := K1 f r₁ r₂ hc
      have : {z : ℂ | r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂} = LiZhongQC.annulus r₁ r₂.toReal := by
        ext z
        simp only [Set.mem_ofPred_eq, LiZhongQC.annulus]
        rw [← ENNReal.ofReal_toReal hr2, ENNReal.ofReal_lt_ofReal_iff (hr1pos.trans hlt), ENNReal.toReal_ofReal (hr1pos.trans hlt).le]
      rw [this] at h1
      have := LiZhongQC.dcModulus_eq_of_equiv hopen hr1pos hlt h1
      rw [hdc] at this
      exact this.symm.le
    · obtain ⟨f, hf⟩ := K2 (LiZhongQC.annulus a₁ a₂) a₁ (ENNReal.ofReal a₂) ha₁.le
        ((ENNReal.ofReal_lt_ofReal_iff (ha₁.trans ha₂)).2 ha₂) (by
          ext z
          simp only [Set.mem_ofPred_eq, LiZhongQC.annulus]
          rw [ENNReal.ofReal_lt_ofReal_iff (ha₁.trans ha₂)]) hA
      refine le_iSup_of_le f (le_iSup_of_le a₁ (le_iSup_of_le (ENNReal.ofReal a₂) (le_iSup_of_le hf ?_)))
      rw [ENNReal.toReal_ofReal (ha₁.trans ha₂).le]

/-- Helper (Ch. I §7, ring-module bridge). A fractional linear transformation of `ℂ̄` carries a ring domain to a ring
domain of the same module (the module is a conformal invariant, here for a Möbius homeomorphism). -/
theorem lv17_ringModule_mobius (e : ExtPlane ≃ₜ ExtPlane) (he : IsMobius ⇑e) (hes : IsMobius ⇑e.symm)
    {B : Set ExtPlane} (hB : IsRingDomain B) : IsRingDomain (e '' B) ∧ ringModule (e '' B) = ringModule B := by
  obtain ⟨hdom, h2, hcard⟩ := hB
  refine ⟨⟨⟨e.isOpenMap _ hdom.1, hdom.2.image e e.continuous.continuousOn⟩, h2, ?_⟩, ?_⟩
  · rw [lv17_card_cc_image]; exact hcard
  · refine lv17_ringModule_congr fun r₁ r₂ => ⟨?_, ?_⟩
    · rintro ⟨g, hg0, hg1, hg2, hg3⟩
      have hc : IsConformalMap (g ∘ ⇑e.symm.symm) (e.symm '' (e '' B)) :=
        lv15_isConformalMap_comp_symm e.symm he hg2
      rw [lv15_symm_image_image] at hc
      refine ⟨g ∘ ⇑e, hg0, hg1, hc, ?_⟩
      rw [image_comp, hg3]
    · rintro ⟨f, hf0, hf1, hf2, hf3⟩
      refine ⟨f ∘ ⇑e.symm, hf0, hf1, lv15_isConformalMap_comp_symm e hes hf2, ?_⟩
      rw [image_comp, lv15_symm_image_image, hf3]

/-- Helper (Ch. I §7, finite model). A `K`-quasiconformal mapping `w` of a ring domain `B` of `ℂ̄` onto a ring domain
`B′` is, after fractional linear changes of variable on both sides (sending a complementary point of `B`, resp. `B′`,
to `∞`), a `K`-quasiconformal mapping `f` in Li Zhong's sense between doubly connected domains of the finite plane
with the same modules. -/
theorem lv17_finite_model {w : ExtPlane → ExtPlane} {B B' : Set ExtPlane} {K : ℝ} (hB : IsRingDomain B)
    (hB' : IsRingDomain B') (hw : IsKQuasiconformal w B K) (hwB : w '' B = B') :
    ∃ (B₀ B₀' : Set ℂ) (f : ℂ → ℂ), LiZhongQC.IsDoublyConnected B₀ ∧ LiZhongQC.IsDoublyConnected B₀' ∧
      ringModule B = LiZhongQC.dcModulus B₀ ∧ ringModule B' = LiZhongQC.dcModulus B₀' ∧
      LiZhongQC.IsKQC f B₀ K ∧ f '' B₀ = B₀' := by
  have key : ∀ {B : Set ExtPlane}, IsRingDomain B →
      ∃ e : ExtPlane ≃ₜ ExtPlane, IsMobius ⇑e ∧ IsMobius ⇑e.symm ∧ ∃ B₀ : Set ℂ, e '' B = toExt B₀ ∧
        LiZhongQC.IsDoublyConnected B₀ ∧ ringModule B = LiZhongQC.dcModulus B₀ := by
    intro B hB
    have hcard := hB.2.2
    have hne : Nonempty (ConnectedComponents ↥Bᶜ) := (Nat.card_pos_iff.1 (by rw [hcard]; norm_num)).1
    obtain ⟨c⟩ := hne
    obtain ⟨⟨a, ha⟩, -⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨e, he, hes, hea⟩ := lv17_mobius_to_infty a
    obtain ⟨hring1, hmod1⟩ := lv17_ringModule_mobius e he hes hB
    have hinf : extInf ∉ e '' B := fun h => by
      rw [← hea] at h
      exact ha (e.injective.mem_set_image.1 h)
    have heq : e '' B = toExt (finitePart (e '' B)) := by
      ext z
      constructor
      · intro hz
        have hz' : z ≠ extInf := by
          rintro rfl
          exact hinf hz
        obtain ⟨ζ, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hz'
        exact ⟨ζ, hz, rfl⟩
      · rintro ⟨ζ, hζ, rfl⟩
        exact hζ
    have hdc : LiZhongQC.IsDoublyConnected (finitePart (e '' B)) := by
      rw [← lv17_isRingDomain_toExt_iff, ← heq]
      exact hring1
    refine ⟨e, he, hes, finitePart (e '' B), heq, hdc, ?_⟩
    calc ringModule B = ringModule (e '' B) := hmod1.symm
      _ = ringModule (toExt (finitePart (e '' B))) := by rw [← heq]
      _ = LiZhongQC.dcModulus (finitePart (e '' B)) := lv17_ringModule_toExt hdc
  obtain ⟨T, hT, hTs, B₀, hTB, hB₀, hM⟩ := key hB
  obtain ⟨S, hS, hSs, B₀', hSB, hB₀', hM'⟩ := key hB'
  have hdom1 : IsDomainExt (T '' B) := (lv17_ringModule_mobius T hT hTs hB).1.1
  -- `S ∘ w ∘ T⁻¹` is `K`-quasiconformal on `T(B)`
  have hq1 : IsKQuasiconformal (⇑T.symm) (T '' B) 1 :=
    conformal_isKQuasiconformal_one (lv17_isConformalMap_mobius hTs hdom1)
  have hq2 : IsKQuasiconformal w (⇑T.symm '' (T '' B)) K := by
    rw [lv15_symm_image_image]; exact hw
  have hq12 := kqc_comp hq1 hq2
  have himg1 : (w ∘ ⇑T.symm) '' (T '' B) = B' := by
    rw [image_comp, lv15_symm_image_image, hwB]
  have hq3 : IsKQuasiconformal S ((w ∘ ⇑T.symm) '' (T '' B)) 1 := by
    rw [himg1]; exact conformal_isKQuasiconformal_one (lv17_isConformalMap_mobius hS hB'.1)
  have hq := kqc_comp hq12 hq3
  rw [one_mul, mul_one] at hq
  have himg2 : (S ∘ (w ∘ ⇑T.symm)) '' (T '' B) = toExt B₀' := by
    rw [image_comp, himg1, hSB]
  have hcore := lv13_isKQC_of_isKQuasiconformal hq
  have hset : {z : ℂ | (z : ExtPlane) ∈ T '' B ∧ (S ∘ (w ∘ ⇑T.symm)) (z : ExtPlane) ≠ extInf} = B₀ := by
    ext z
    constructor
    · rintro ⟨hz, -⟩
      rw [hTB] at hz
      obtain ⟨a, ha, haz⟩ := hz
      rwa [← OnePoint.coe_injective haz]
    · intro hz
      have hz1 : (z : ExtPlane) ∈ T '' B := by rw [hTB]; exact ⟨z, hz, rfl⟩
      refine ⟨hz1, fun h => ?_⟩
      have : (S ∘ (w ∘ ⇑T.symm)) (z : ExtPlane) ∈ toExt B₀' := himg2 ▸ mem_image_of_mem _ hz1
      obtain ⟨a, -, ha⟩ := this
      exact OnePoint.coe_ne_infty a (ha.trans h)
  rw [hset] at hcore
  refine ⟨B₀, B₀', finiteMap (S ∘ (w ∘ ⇑T.symm)), hB₀, hB₀', hM, ?_, hcore, ?_⟩
  · exact hM'
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 : (z : ExtPlane) ∈ T '' B := by rw [hTB]; exact ⟨z, hz, rfl⟩
      have : (S ∘ (w ∘ ⇑T.symm)) (z : ExtPlane) ∈ toExt B₀' := himg2 ▸ mem_image_of_mem _ hz1
      obtain ⟨a, ha, hae⟩ := this
      show finiteValue ((S ∘ (w ∘ ⇑T.symm)) (z : ExtPlane)) ∈ B₀'
      rw [← hae]
      exact ha
    · intro hy
      have : ((y : ℂ) : ExtPlane) ∈ (S ∘ (w ∘ ⇑T.symm)) '' (T '' B) := himg2 ▸ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := this
      rw [hTB] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, hz, by show finiteValue ((S ∘ (w ∘ ⇑T.symm)) (z : ExtPlane)) = y; rw [hxy]; rfl⟩

/-- Helper (Ch. I §7, Theorem 7.4 without closure). If `f` is `K`-quasiconformal on `D`, and `B ⊆ D` and `f(B)` are
doubly connected domains, then `M(f(B)) ≤ K M(B)`. No assumption `B̄ ⊆ D` is made: the closure condition of Li Zhong's
`thm7_4_dcModulus_quasi_invariance` is only used there to show that `f(B)` is non-degenerate. Here that is the point
(exhaustion of the canonical annulus of `B` by sub-annuli, whose images have module `≤ K log(b/a)` by `thm7_4` but
would have module `→ ∞` if `f(B)` had a point complementary component). -/
theorem lv17_dcModulus_image_le {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f D K) {B : Set ℂ}
    (hB : LiZhongQC.IsDoublyConnected B) (hBD : B ⊆ D) (hB' : LiZhongQC.IsDoublyConnected (f '' B)) :
    LiZhongQC.dcModulus (f '' B) ≤ ENNReal.ofReal K * LiZhongQC.dcModulus B := by
  obtain ⟨hD, hK1, hhom, -⟩ := id hf
  have hK0 : 0 ≤ K := by linarith
  have hKpos : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  by_cases hdeg : ∃ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x = {x}
  · rw [(LiZhongQC.aqc_dcModulus_eq_top_iff hB).2 hdeg, ENNReal.mul_top hKpos]
    exact le_top
  push Not at hdeg
  -- canonical annulus of `B`, rescaled to inner radius `1`
  obtain ⟨r₁, r₂, h₁, h₂, hBeq⟩ := LiZhongQC.thm2_1_canonical_form_annulus hB hdeg
  set R : ℝ := r₂ / r₁ with hRdef
  have hR : 1 < R := by rw [hRdef, lt_div_iff₀ h₁, one_mul]; exact h₂
  have hBA : LiZhongQC.ConformallyEquivalent B (LiZhongQC.annulus 1 R) :=
    hBeq.trans ((LiZhongQC.annulus_conformallyEquivalent_iff h₁ h₂ one_pos hR).2 (by rw [hRdef, div_one]))
  have hMB : LiZhongQC.dcModulus B = ENNReal.ofReal (Real.log R) := by
    rw [LiZhongQC.dcModulus_eq_of_equiv hB.1 one_pos hR hBA, div_one]
  obtain ⟨φ, hφ⟩ := hBA
  have hφinv : LiZhongQC.IsConformalOnto (Function.invFunOn φ B) (LiZhongQC.annulus 1 R) B := hφ.symm hB.1
  have h1 : LiZhongQC.IsKQC (Function.invFunOn φ B) (LiZhongQC.annulus 1 R) 1 :=
    LiZhongQC.isKQC_one_of_conformal (LiZhongQC.isOpen_annulus 1 R) hφinv
  have h2 : LiZhongQC.IsKQC (f ∘ Function.invFunOn φ B) (LiZhongQC.annulus 1 R) (1 * K) :=
    LiZhongQC.thm7_1_comp h1 hf (by rw [hφinv.2.2]; exact hBD)
  have himg2 : (f ∘ Function.invFunOn φ B) '' LiZhongQC.annulus 1 R = f '' B := by
    rw [image_comp, hφinv.2.2]
  by_cases hdeg' : ∀ y ∈ (toExt (f '' B))ᶜ, connectedComponentIn (toExt (f '' B))ᶜ y ≠ {y}
  · -- both non-degenerate: the annulus argument of Theorem 7.4
    obtain ⟨s₁, s₂, hs₁, hs₂, hB'eq⟩ := LiZhongQC.thm2_1_canonical_form_annulus hB' hdeg'
    set R' : ℝ := s₂ / s₁ with hR'def
    have hR' : 1 < R' := by rw [hR'def, lt_div_iff₀ hs₁, one_mul]; exact hs₂
    have hB'A' : LiZhongQC.ConformallyEquivalent (f '' B) (LiZhongQC.annulus 1 R') :=
      hB'eq.trans ((LiZhongQC.annulus_conformallyEquivalent_iff hs₁ hs₂ one_pos hR').2
        (by rw [hR'def, div_one]))
    have hMB' : LiZhongQC.dcModulus (f '' B) = ENNReal.ofReal (Real.log R') := by
      rw [LiZhongQC.dcModulus_eq_of_equiv hB'.1 one_pos hR' hB'A', div_one]
    obtain ⟨ψ, hψ⟩ := hB'A'
    have h3 : LiZhongQC.IsKQC ψ (f '' B) 1 := LiZhongQC.isKQC_one_of_conformal hB'.1 hψ
    have h4 : LiZhongQC.IsKQC (ψ ∘ (f ∘ Function.invFunOn φ B)) (LiZhongQC.annulus 1 R) (1 * K * 1) :=
      LiZhongQC.thm7_1_comp h2 h3 (by rw [himg2])
    obtain ⟨-, -, hg, hmod⟩ := h4
    have himg4 : (ψ ∘ (f ∘ Function.invFunOn φ B)) '' LiZhongQC.annulus 1 R = LiZhongQC.annulus 1 R' := by
      rw [image_comp, himg2, hψ.2.2]
    rw [himg4] at hg
    have hlog : Real.log R' ≤ K * Real.log R := by
      refine LiZhongQC.aqc_log_le_of_quad_bound hR hR' hK0 hg fun Q hQ => ?_
      obtain ⟨Q', hQ', hle⟩ := hmod Q hQ
      exact ⟨Q', hQ', by simpa using hle⟩
    rw [hMB, hMB', ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal hlog
  · -- the image is degenerate: impossible
    exfalso
    push Not at hdeg'
    obtain ⟨y, hy, hypt⟩ := hdeg'
    have htop : LiZhongQC.dcModulus (f '' B) = ⊤ := (LiZhongQC.aqc_dcModulus_eq_top_iff hB').2 ⟨y, hy, hypt⟩
    rcases LiZhongQC.thm2_1_canonical_form hB' with hP | hP | ⟨s₁, s₂, hs₁, hs₂, hP⟩
    · obtain ⟨ψ, hψ⟩ := hP
      have h3 : LiZhongQC.IsKQC ψ (f '' B) 1 :=
        LiZhongQC.isKQC_one_of_conformal hB'.1 hψ
      have h4 : LiZhongQC.IsKQC (ψ ∘ (f ∘ Function.invFunOn φ B)) (LiZhongQC.annulus 1 R) (1 * K * 1) :=
        LiZhongQC.thm7_1_comp h2 h3 (by rw [himg2])
      have himg4 : (ψ ∘ (f ∘ Function.invFunOn φ B)) '' LiZhongQC.annulus 1 R = LiZhongQC.puncturedPlane := by
        rw [image_comp, himg2, hψ.2.2]
      rw [one_mul, mul_one] at h4
      refine lv17_no_degenerate_image hR h4 ?_ ?_ <;> rw [himg4]
      · simp [LiZhongQC.puncturedPlane]
      · intro z hz
        simp only [LiZhongQC.puncturedPlane, mem_compl_iff, mem_singleton_iff]
        rintro rfl
        simpa [LiZhongQC.annulus] using hz.1
    · obtain ⟨ψ, hψ⟩ := hP
      have h3 : LiZhongQC.IsKQC ψ (f '' B) 1 :=
        LiZhongQC.isKQC_one_of_conformal hB'.1 hψ
      have h4 : LiZhongQC.IsKQC (ψ ∘ (f ∘ Function.invFunOn φ B)) (LiZhongQC.annulus 1 R) (1 * K * 1) :=
        LiZhongQC.thm7_1_comp h2 h3 (by rw [himg2])
      have himg4 : (ψ ∘ (f ∘ Function.invFunOn φ B)) '' LiZhongQC.annulus 1 R = LiZhongQC.puncturedDisc := by
        rw [image_comp, himg2, hψ.2.2]
      rw [one_mul, mul_one] at h4
      refine lv17_no_degenerate_image hR h4 ?_ ?_ <;> rw [himg4]
      · simp [LiZhongQC.puncturedDisc, LiZhongQC.annulus]
      · exact fun z hz => hz
    · rw [LiZhongQC.dcModulus_eq_of_equiv hB'.1 hs₁ hs₂ hP] at htop
      exact ENNReal.ofReal_ne_top htop

/-- **Theorem 7.1** (Ch. I §7.1). If there exists a `K`-quasiconformal mapping `w` of the ring domain `B` onto the
ring domain `B′`, then `M(B)/K ≤ M(B′) ≤ K M(B)`. No assumption is made on the boundary behaviour of `w`.
Modelling: `M(B)/K ≤ M(B′)` is multiplied out as `M(B) ≤ K M(B′)` in `ℝ≥0∞` (no division junk). -/
theorem thm1_7_1 {w : ExtPlane → ExtPlane} {B B' : Set ExtPlane} {K : ℝ} (hB : IsRingDomain B)
    (hB' : IsRingDomain B') (hw : IsKQuasiconformal w B K) (hwB : w '' B = B') :
    ringModule B ≤ ENNReal.ofReal K * ringModule B' ∧ ringModule B' ≤ ENNReal.ofReal K * ringModule B := by
  obtain ⟨B₀, B₀', f, hB₀, hB₀', hM, hM', hf, hfB⟩ := lv17_finite_model hB hB' hw hwB
  have hg := LiZhongQC.thm7_2_inv hf
  have hgB : Function.invFunOn f B₀ '' B₀' = B₀ := by
    rw [← hfB]
    exact hf.2.2.1.2.1.leftInvOn_invFunOn.image_image
  rw [hM, hM']
  refine ⟨?_, ?_⟩
  · have := lv17_dcModulus_image_le (D := f '' B₀) hg (B := B₀') hB₀' (by rw [hfB])
      (by rw [hgB]; exact hB₀)
    rw [hgB] at this
    exact this
  · have := lv17_dcModulus_image_le hf hB₀ subset_rfl (by rw [hfB]; exact hB₀')
    rwa [hfB] at this

/-- **Theorem 7.2** (Ch. I §7.2). Let `w` be a sense-preserving homeomorphism of a domain `G`. If the inequality
`M(w(B)) ≤ K M(B)` holds for every ring domain `B`, `B̄ ⊂ G`, then `w` is a `K`-quasiconformal mapping. -/
theorem thm1_7_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G)
    (hB : ∀ B, IsRingDomain B → closure B ⊆ G → ringModule (w '' B) ≤ ENNReal.ofReal K * ringModule B) :
    IsKQuasiconformal w G K := by
  sorry

/-- **Unlabelled** (Ch. I §7.2, P1:1135). A sense-preserving homeomorphism `w` of a domain `G` is `K`-quasiconformal
in `G` if and only if the module condition `M(w(B)) ≤ K M(B)` holds for every ring domain `B`, `B̄ ⊂ G`. -/
theorem isKQuasiconformal_iff_ring {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) :
    IsKQuasiconformal w G K ↔
      ∀ B, IsRingDomain B → closure B ⊆ G → ringModule (w '' B) ≤ ENNReal.ofReal K * ringModule B := by
  sorry

end LehtoVirtanen1973
