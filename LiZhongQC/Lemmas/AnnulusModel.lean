import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.ConnectedComplement
import LiZhongQC.RiemannMapping
import LiZhongQC.Lemmas.Mobius
import LiZhongQC.Lemmas.JordanBridge

/-!
# The analytic-Jordan-curve annulus model (Theorem 2.1 case (iii), piece A)
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **PIECE A — FROZEN.** Owner -d0. -/
theorem exists_analytic_annulus_model_of_isDoublyConnected {B : Set ℂ}
    (hB : IsDoublyConnected B)
    (hnd : ∀ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x ≠ {x}) :
    ∃ (K : Set ℂ) (Φ : ℂ → ℂ),
      K ⊆ unitDisc ∧ IsCompact K ∧ IsConnected K ∧ K.Nontrivial ∧
      ConformallyEquivalent B (unitDisc \ K) ∧
      DifferentiableOn ℂ Φ (univ \ K) ∧
      BijOn Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖} ∧
      IsJordanCurve (toExt (Φ '' sphere 0 1)) ∧
      (∃ r : ℝ, 1 < r ∧ ∀ ζ ∈ Φ '' sphere 0 1, r ≤ ‖ζ‖) ∧
      (∃ A Bext : Set ℂ, IsOpen A ∧ IsOpen Bext ∧ IsConnected A ∧ IsConnected Bext ∧
        Disjoint A Bext ∧ Disjoint A (Φ '' sphere 0 1) ∧ Disjoint Bext (Φ '' sphere 0 1) ∧
        A ∪ Bext ∪ Φ '' sphere 0 1 = univ ∧
        Bornology.IsBounded A ∧ ¬ Bornology.IsBounded Bext ∧
        A = closedBall 0 1 ∪ Φ '' (unitDisc \ K) ∧
        IsConnected (A \ closedBall 0 1) ∧
        (∃ r : ℝ, 1 < r ∧ {ζ : ℂ | 1 < ‖ζ‖ ∧ ‖ζ‖ < r} ⊆ A) ∧
        closedBall 0 1 ⊆ A ∧ IsPathConnected Aᶜ) := by
  -- STAGE 1 (sub-piece 1): already proven elsewhere.
  obtain ⟨K, hKunit, hKcpt, hKconn, hKnt, hBequiv⟩ :=
    exists_conformallyEquivalent_diff_compact_of_isDoublyConnected hB hnd
  obtain ⟨f, hfdiff, hfinj, hfimg⟩ := hBequiv
  have hfcont : ContinuousOn f B := hfdiff.continuousOn
  have hUDKconn : IsConnected (unitDisc \ K) := by
    rw [← hfimg]; exact hB.2.1.image f hfcont
  -- STAGE 2: `univ \ K` is preconnected.
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    hKcpt.exists_isMaxOn hKconn.nonempty continuous_norm.continuousOn
  set M : ℝ := ‖z₀‖ with hMdef
  have hM1 : M < 1 := by
    have := hKunit hz₀K
    rwa [unitDisc, mem_ball, dist_zero_right] at this
  have hM0 : 0 ≤ M := norm_nonneg _
  have hKM : ∀ z ∈ K, ‖z‖ ≤ M := fun z hz => hz₀max hz
  set Text : Set ℂ := {z : ℂ | M < ‖z‖} with hTextdef
  have hTextPreconn : IsPreconnected Text := isPreconnected_setOf_lt_norm hM0
  have hUDKPreconn : IsPreconnected (unitDisc \ K) := hUDKconn.2
  have hcover : univ \ K = (unitDisc \ K) ∪ Text := by
    ext z
    simp only [mem_diff, mem_univ, true_and, mem_union, hTextdef, mem_setOf_eq]
    constructor
    · intro hzK
      by_cases hz1 : z ∈ unitDisc
      · exact Or.inl ⟨hz1, hzK⟩
      · right
        have h1 : (1:ℝ) ≤ ‖z‖ := by
          rw [unitDisc, mem_ball, dist_zero_right, not_lt] at hz1; exact hz1
        linarith
    · rintro (⟨-, hz2⟩ | hz2)
      · exact hz2
      · intro hzK
        have := hKM z hzK
        linarith
  have hw0mem : ((M + 1) / 2 : ℝ) * (1 : ℂ) ∈ unitDisc \ K ∩ Text := by
    have hnorm : ‖((M + 1) / 2 : ℝ) * (1 : ℂ)‖ = (M + 1) / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_one, mul_one]
    constructor
    · constructor
      · rw [unitDisc, mem_ball, dist_zero_right, hnorm]; linarith
      · intro hmem
        have := hKM _ hmem
        rw [hnorm] at this
        linarith
    · show M < ‖((M + 1) / 2 : ℝ) * (1 : ℂ)‖
      rw [hnorm]; linarith
  have hKcPreconn : IsPreconnected (univ \ K) := by
    rw [hcover]
    exact IsPreconnected.union _ hw0mem.1 hw0mem.2 hUDKPreconn hTextPreconn
  have hKcNonempty : (univ \ K).Nonempty := ⟨_, mem_univ _, hw0mem.1.2⟩
  have hKcIsConnected : IsConnected (univ \ K) := ⟨hKcNonempty, hKcPreconn⟩
  -- STAGE 3: the inversion `φ` about a point `a₀ ∈ K`.
  obtain ⟨a₀, ha₀⟩ := hKconn.nonempty
  set φ : ℂ → ℂ := fun z => (z - a₀)⁻¹ with hφdef
  have hφdiff : DifferentiableOn ℂ φ (univ \ K) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => z - a₀) (univ \ K) := by fun_prop
    apply hd.inv
    intro z hz hzeq
    rw [sub_eq_zero] at hzeq
    exact hz.2 (hzeq ▸ ha₀)
  have hφne : ∀ z ∈ univ \ K, φ z ≠ 0 := by
    intro z hz
    show (z - a₀)⁻¹ ≠ 0
    apply inv_ne_zero
    intro hzeq
    rw [sub_eq_zero] at hzeq
    exact hz.2 (hzeq ▸ ha₀)
  have hφinj : InjOn φ (univ \ K) := by
    intro z1 _ z2 _ heq
    exact sub_left_inj.mp (inv_inj.mp heq)
  set W : Set ℂ := insert 0 (φ '' (univ \ K)) with hWdef
  have h0W : (0:ℂ) ∈ W := mem_insert _ _
  have hVo : IsOpen (univ \ K) := isOpen_univ.sdiff hKcpt.isClosed
  have hφVopen : IsOpen (φ '' (univ \ K)) :=
    (RMT.differentiableOn_invFunOn_of_injOn hVo hφdiff hφinj).1
  -- a radius `R` with `K ⊆ closedBall a₀ R`
  have hRbd : ∀ z ∈ K, ‖z - a₀‖ ≤ 2 * M := by
    intro z hz
    calc ‖z - a₀‖ ≤ ‖z‖ + ‖a₀‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hKM z hz) (hKM a₀ ha₀)
      _ = 2 * M := by ring
  have hR0 : 0 < 2 * M + 1 := by linarith
  set R : ℝ := 2 * M + 1 with hRdef
  have hRbd' : ∀ z ∈ K, ‖z - a₀‖ < R := fun z hz => lt_of_le_of_lt (hRbd z hz) (by linarith)
  have hballsub : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < R⁻¹ → (a₀ + w⁻¹) ∈ univ \ K ∧ φ (a₀ + w⁻¹) = w := by
    intro w hw0 hwR
    have hwne : w ≠ 0 := fun h => by rw [h, norm_zero] at hw0; exact lt_irrefl _ hw0
    have hnormw : ‖(a₀ + w⁻¹) - a₀‖ = ‖w‖⁻¹ := by
      rw [add_sub_cancel_left, norm_inv]
    have hgt : R < ‖(a₀ + w⁻¹) - a₀‖ := by
      rw [hnormw]
      rwa [lt_inv_comm₀ hw0 hR0] at hwR
    refine ⟨⟨mem_univ _, fun hmem => ?_⟩, ?_⟩
    · exact absurd (hRbd' _ hmem) (not_lt.mpr hgt.le)
    · show (a₀ + w⁻¹ - a₀)⁻¹ = w
      rw [add_sub_cancel_left, inv_inv]
  have hballW : ball (0:ℂ) R⁻¹ ⊆ W := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    rcases eq_or_ne w 0 with rfl | hwne
    · exact h0W
    · have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hwne
      obtain ⟨hmem, heq⟩ := hballsub w hw0 hw
      exact Or.inr ⟨a₀ + w⁻¹, hmem, heq⟩
  have hR0' : 0 < R⁻¹ := inv_pos.mpr hR0
  have hIsOpenW : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hx with rfl | hxmem
    · exact Filter.mem_of_superset
        (isOpen_ball.mem_nhds (mem_ball_self hR0')) hballW
    · exact Filter.mem_of_superset (hφVopen.mem_nhds hxmem) (subset_insert _ _)
  have hφVpreconn : IsPreconnected (φ '' (univ \ K)) :=
    hKcPreconn.image φ hφdiff.continuousOn
  have h0closure : (0:ℂ) ∈ closure (φ '' (univ \ K)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set w : ℂ := ((min ε R⁻¹ / 2 : ℝ) : ℂ) with hwdef
    have hw0 : 0 < ‖w‖ := by
      rw [hwdef, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      positivity
    have hwR : ‖w‖ < R⁻¹ := by
      rw [hwdef, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc min ε R⁻¹ / 2 ≤ R⁻¹ / 2 := by gcongr; exact min_le_right _ _
        _ < R⁻¹ := by linarith [hR0']
    obtain ⟨hmem, heq⟩ := hballsub w hw0 hwR
    refine ⟨w, ⟨a₀ + w⁻¹, hmem, heq⟩, ?_⟩
    rw [dist_zero_left]
    rw [hwdef, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc min ε R⁻¹ / 2 ≤ ε / 2 := by gcongr; exact min_le_left _ _
      _ < ε := by linarith
  have hWpreconn : IsPreconnected W := by
    apply IsPreconnected.subset_closure hφVpreconn (subset_insert _ _)
    exact insert_subset_iff.mpr ⟨h0closure, subset_closure⟩
  have hWconn : IsConnected W := ⟨⟨0, h0W⟩, hWpreconn⟩
  -- STAGE 4: `(toExt W)ᶜ` is connected, via the sphere Möbius map sending `a₀ ↦ ∞`.
  have hφinjGlobal : ∀ z1 z2 : ℂ, z1 ≠ a₀ → z2 ≠ a₀ → φ z1 = φ z2 → z1 = z2 := by
    intro z1 z2 _ _ heq
    exact sub_left_inj.mp (inv_inj.mp heq)
  have hWceq : ∀ z : ℂ, z ∉ W ↔ z ∈ φ '' (K \ {a₀}) := by
    intro z
    constructor
    · intro hzW
      have hz0 : z ≠ 0 := fun h => hzW (h ▸ h0W)
      set k : ℂ := a₀ + z⁻¹ with hkdef
      have hka₀ : k ≠ a₀ := by
        intro h
        rw [hkdef] at h
        have hz' : z⁻¹ = 0 := by linear_combination h
        exact hz0 (inv_eq_zero.mp hz')
      have hφk : φ k = z := by
        show (k - a₀)⁻¹ = z
        rw [hkdef, add_sub_cancel_left, inv_inv]
      have hkK : k ∈ K := by
        by_contra hkK
        exact hzW (Or.inr ⟨k, ⟨mem_univ _, hkK⟩, hφk⟩)
      exact ⟨k, ⟨hkK, hka₀⟩, hφk⟩
    · rintro ⟨k, ⟨hkK, hka₀⟩, hφkz⟩ hmem
      rcases hmem with heq0 | ⟨z', hz', heqz⟩
      · rw [← hφkz] at heq0
        exact hka₀ (sub_eq_zero.mp (inv_eq_zero.mp heq0))
      · have hz'a₀ : z' ≠ a₀ := fun h => hz'.2 (h ▸ ha₀)
        have := hφinjGlobal z' k hz'a₀ hka₀ (heqz.trans hφkz.symm)
        exact hz'.2 (this ▸ hkK)
  have hmobDet : (0:ℂ) * (-a₀) - 1 * 1 ≠ 0 := by simp
  set m : ExtPlane → ExtPlane := mobiusExt 0 1 1 (-a₀) with hmdef
  have hmcont : Continuous m := continuous_mobiusExt hmobDet
  have hma₀ : m (a₀ : ExtPlane) = extInf := by
    rw [hmdef]; exact mobiusExt_coe_of_eq_zero (by ring)
  have hmk : ∀ k : ℂ, k ≠ a₀ → m (k : ExtPlane) = (φ k : ExtPlane) := by
    intro k hk
    have hcz : (1:ℂ) * k + (-a₀) ≠ 0 := fun h => hk (by linear_combination h)
    rw [hmdef, mobiusExt_coe (z := k) hcz, OnePoint.coe_eq_coe]
    show (0 * k + 1) / (1 * k + -a₀) = (k - a₀)⁻¹
    rw [show (0:ℂ) * k + 1 = 1 from by ring, show (1:ℂ) * k + -a₀ = k - a₀ from by ring, one_div]
  have heqSet : (toExt W)ᶜ = m '' (toExt K) := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      constructor
      · intro _
        exact ⟨(a₀ : ExtPlane), coe_mem_toExt_iff.mpr ha₀, hma₀⟩
      · intro _
        exact extInf_mem_compl_toExt W
    | coe z =>
      rw [coe_mem_compl_toExt_iff]
      constructor
      · intro hzW
        obtain ⟨k, hkKa, hφkz⟩ := hWceq z |>.mp hzW
        exact ⟨(k : ExtPlane), coe_mem_toExt_iff.mpr hkKa.1, by
          rw [hmk k hkKa.2, hφkz]⟩
      · rintro ⟨x, hx, hxz⟩
        induction x using OnePoint.rec with
        | infty => exact absurd hx (extInf_notMem_toExt K)
        | coe k =>
          have hkK : k ∈ K := coe_mem_toExt_iff.mp hx
          by_cases hka₀ : k = a₀
          · rw [hka₀, hma₀] at hxz
            simp at hxz
          · rw [hmk k hka₀] at hxz
            have hφkz : φ k = z := OnePoint.coe_eq_coe.mp hxz
            rw [hWceq]
            exact ⟨k, ⟨hkK, hka₀⟩, hφkz⟩
  have hKextConn : IsConnected (toExt K) :=
    hKconn.image _ OnePoint.continuous_coe.continuousOn
  have hWcConn : IsConnected (toExt W)ᶜ := by
    rw [heqSet]; exact hKextConn.image m hmcont.continuousOn
  -- STAGE 5: apply RMT to `W`, then invert back through `φ` to get `Φ`.
  have hWne : Wᶜ.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hKnt
    by_cases hxa₀ : x = a₀
    · have hya₀ : y ≠ a₀ := fun h => hxy (hxa₀.trans h.symm)
      exact ⟨φ y, (hWceq (φ y)).mpr ⟨y, ⟨hy, hya₀⟩, rfl⟩⟩
    · exact ⟨φ x, (hWceq (φ x)).mpr ⟨x, ⟨hx, hxa₀⟩, rfl⟩⟩
  have hHsqrt : RMT.HasHolomorphicSqrt W :=
    hasHolomorphicSqrt_of_isConnected_compl hIsOpenW hWconn hWcConn
  obtain ⟨ψ, hψ, hψbij⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hIsOpenW hWconn hWne hHsqrt h0W
  have hφVsubW : φ '' (univ \ K) ⊆ W := subset_insert _ _
  have hψφne : ∀ z ∈ univ \ K, ψ (φ z) ≠ 0 := by
    intro z hz hcon
    have : φ z = 0 := hψ.injOn (hφVsubW ⟨z, hz, rfl⟩) h0W (by rw [hcon, hψ.center])
    exact hφne z hz this
  set Φ : ℂ → ℂ := fun z => (ψ (φ z))⁻¹ with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ (univ \ K) := by
    apply DifferentiableOn.inv
    · exact hψ.diff.comp hφdiff (fun z hz => hφVsubW ⟨z, hz, rfl⟩)
    · exact hψφne
  have hΦmapsto : MapsTo Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖} := by
    intro z hz
    have hmem : φ z ∈ W := hφVsubW ⟨z, hz, rfl⟩
    have hlt1 : ‖ψ (φ z)‖ < 1 := by
      have := hψbij.mapsTo hmem
      rwa [mem_ball, dist_zero_right] at this
    have hpos : 0 < ‖ψ (φ z)‖ := norm_pos_iff.mpr (hψφne z hz)
    show 1 < ‖(ψ (φ z))⁻¹‖
    rw [norm_inv]
    rw [lt_inv_comm₀ one_pos hpos]
    simpa using hlt1
  have hΦinj : InjOn Φ (univ \ K) := by
    intro z1 hz1 z2 hz2 heq
    have h1 : φ z1 ∈ W := hφVsubW ⟨z1, hz1, rfl⟩
    have h2 : φ z2 ∈ W := hφVsubW ⟨z2, hz2, rfl⟩
    have heq' : ψ (φ z1) = ψ (φ z2) := inv_inj.mp heq
    exact hφinj hz1 hz2 (hψ.injOn h1 h2 heq')
  have hΦsurj : SurjOn Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖} := by
    intro ζ hζ
    simp only [mem_setOf_eq] at hζ
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ; linarith
    have hζinv : ζ⁻¹ ∈ RMT.disc := by
      rw [mem_ball, dist_zero_right, norm_inv]
      rw [inv_lt_one_iff₀]
      right; linarith
    obtain ⟨w, hwW, hψw⟩ := hψbij.surjOn hζinv
    have hw0 : w ≠ 0 := by
      intro hcon
      rw [hcon, hψ.center] at hψw
      exact (inv_ne_zero hζ0) hψw.symm
    have hwφ : w ∈ φ '' (univ \ K) := by
      rcases hwW with h | h
      · exact absurd h hw0
      · exact h
    obtain ⟨z, hz, hφz⟩ := hwφ
    refine ⟨z, hz, ?_⟩
    show (ψ (φ z))⁻¹ = ζ
    rw [hφz, hψw, inv_inv]
  have hΦbij : BijOn Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖} := ⟨hΦmapsto, hΦinj, hΦsurj⟩
  -- sphere 0 1 lies inside `univ \ K` (K is compact inside the *open* unit disc).
  have hSphereSub : sphere (0:ℂ) 1 ⊆ univ \ K := by
    intro z hz
    refine ⟨mem_univ _, fun hzK => ?_⟩
    have := hKM z hzK
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  -- STAGE 6: the curve is an (abstract) Jordan curve.
  have hΦcont : ContinuousOn Φ (univ \ K) := hΦdiff.continuousOn
  have hcircle_sphere : ∀ c : Circle, (c : ℂ) ∈ sphere (0:ℂ) 1 :=
    fun c => mem_sphere_zero_iff_norm.2 (Circle.norm_coe c)
  have hcurveJordan : IsJordanCurve (toExt (Φ '' sphere (0:ℂ) 1)) := by
    refine ⟨fun c => ((Φ (c : ℂ) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
    · have hc1 : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
      have hc2 : ContinuousOn Φ (range ((↑) : Circle → ℂ)) := by
        apply hΦcont.mono
        rintro _ ⟨c, rfl⟩
        exact hSphereSub (hcircle_sphere c)
      exact OnePoint.continuous_coe.comp (hc2.comp_continuous hc1 (fun c => mem_range_self c))
    · intro c1 c2 heq
      simp only [OnePoint.coe_eq_coe] at heq
      have := hΦinj (hSphereSub (hcircle_sphere c1)) (hSphereSub (hcircle_sphere c2)) heq
      exact Subtype.coe_injective this
    · ext y
      induction y using OnePoint.rec with
      | infty =>
        simp only [mem_range]
        constructor
        · rintro ⟨c, hc⟩; exact absurd hc (by simp)
        · rintro ⟨z, -, hz⟩; exact absurd hz (by simp)
      | coe w =>
        simp only [mem_range, coe_mem_toExt_iff]
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨(c : ℂ), hcircle_sphere c, OnePoint.coe_eq_coe.mp hc⟩
        · rintro ⟨z, hzs, hzeq⟩
          refine ⟨⟨z, hzs⟩, ?_⟩
          show ((Φ z : ℂ) : ExtPlane) = (w : ExtPlane)
          rw [hzeq]
  -- STAGE 7: the curve stays at a definite distance outside the unit circle.
  have hSphereCompact : IsCompact (sphere (0:ℂ) 1) := isCompact_sphere 0 1
  have hSphereNonempty : (sphere (0:ℂ) 1).Nonempty :=
    ⟨(1:ℂ), by rw [mem_sphere_zero_iff_norm]; exact norm_one⟩
  obtain ⟨z₁, hz₁s, hz₁min⟩ := hSphereCompact.exists_isMinOn hSphereNonempty
    (hΦcont.mono hSphereSub |>.norm)
  have hr1 : 1 < ‖Φ z₁‖ := hΦmapsto (hSphereSub hz₁s)
  have hdistBound : ∃ r : ℝ, 1 < r ∧ ∀ ζ ∈ Φ '' sphere (0:ℂ) 1, r ≤ ‖ζ‖ := by
    refine ⟨‖Φ z₁‖, hr1, ?_⟩
    rintro ζ ⟨z, hz, rfl⟩
    exact hz₁min hz
  -- STAGE 8: `‖Φ z‖ → ∞` as `‖z‖ → ∞` (ψ is continuous at the interior point `0`, `ψ 0 = 0`).
  have hψcontAt0 : ContinuousAt ψ 0 :=
    (hψ.diff.differentiableAt (hIsOpenW.mem_nhds h0W)).continuousAt
  have hΦinfty : ∀ C : ℝ, ∃ Rc : ℝ, ∀ z ∈ univ \ K, Rc < ‖z‖ → C < ‖Φ z‖ := by
    intro C
    set ε : ℝ := 1 / (max C 0 + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hψcontAt0 ε hεpos
    refine ⟨‖a₀‖ + δ⁻¹, fun z hz hzR => ?_⟩
    have hza₀ : δ⁻¹ < ‖z - a₀‖ := by
      have h1 : ‖a₀‖ + δ⁻¹ < ‖z‖ := hzR
      calc δ⁻¹ = ‖a₀‖ + δ⁻¹ - ‖a₀‖ := by ring
        _ < ‖z‖ - ‖a₀‖ := by linarith
        _ ≤ ‖z - a₀‖ := by
            have := norm_sub_norm_le z a₀
            linarith
    have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδpos
    have hza₀pos : 0 < ‖z - a₀‖ := lt_trans hδinv hza₀
    have hφzsmall : ‖φ z‖ < δ := by
      show ‖(z - a₀)⁻¹‖ < δ
      rw [norm_inv, inv_lt_comm₀ hza₀pos hδpos]
      exact hza₀
    have hψφz : dist (ψ (φ z)) (ψ 0) < ε := hδ (by rwa [dist_zero_right])
    rw [hψ.center, dist_zero_right] at hψφz
    have hψφzpos : 0 < ‖ψ (φ z)‖ := norm_pos_iff.mpr (hψφne z hz)
    show C < ‖(ψ (φ z))⁻¹‖
    rw [norm_inv]
    calc C ≤ max C 0 := le_max_left _ _
      _ < max C 0 + 1 := by linarith
      _ = ε⁻¹ := by rw [hεdef, one_div, inv_inv]
      _ < (‖ψ (φ z)‖)⁻¹ := by
          rw [inv_lt_inv₀ hεpos hψφzpos]
          exact hψφz
  -- STAGE 9: `Φ '' {1 ≤ ‖w‖}` is closed (sequential argument via `hΦinfty` + compactness).
  set S : Set ℂ := {w : ℂ | 1 ≤ ‖w‖} with hSdef
  have hSsubV : S ⊆ univ \ K := by
    intro z hz
    refine ⟨mem_univ _, fun hzK => ?_⟩
    have := hKM z hzK
    rw [hSdef, mem_setOf_eq] at hz
    linarith
  have hΦScont : ContinuousOn Φ S := hΦcont.mono hSsubV
  have hΦSclosed : IsClosed (Φ '' S) := by
    rw [← isSeqClosed_iff_isClosed]
    intro ζseq ζlim hζmem hζtendsto
    choose wseq hwseqS hwseqeq using hζmem
    have hwseqV : ∀ n, wseq n ∈ univ \ K := fun n => hSsubV (hwseqS n)
    have hζbdd := isBounded_range_of_tendsto ζseq hζtendsto
    obtain ⟨Cb, hCb⟩ := hζbdd.exists_norm_le
    obtain ⟨Rc, hRc⟩ := hΦinfty Cb
    have hwbdd : ∀ n, ‖wseq n‖ ≤ Rc := by
      intro n
      by_contra hcon
      push Not at hcon
      have hgt := hRc (wseq n) (hwseqV n) hcon
      rw [hwseqeq n] at hgt
      exact absurd (hCb (ζseq n) (mem_range_self n)) (not_le.mpr hgt)
    have hwmemball : ∀ n, wseq n ∈ closedBall (0 : ℂ) Rc := fun n => by
      rw [mem_closedBall, dist_zero_right]; exact hwbdd n
    obtain ⟨winf, hwinfmem, σ, hσmono, hσtendsto⟩ :=
      (isCompact_closedBall (0 : ℂ) Rc).tendsto_subseq hwmemball
    have hwinfS : winf ∈ S := by
      rw [hSdef, mem_setOf_eq]
      have hlim : Tendsto (fun n => ‖wseq (σ n)‖) atTop (𝓝 ‖winf‖) :=
        (continuous_norm.tendsto winf).comp hσtendsto
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => hwseqS (σ n))
    have hwinfV : winf ∈ univ \ K := hSsubV hwinfS
    have hΦcontAt : ContinuousAt Φ winf :=
      (hΦdiff.differentiableAt (hVo.mem_nhds hwinfV)).continuousAt
    have hζsubtendsto1 : Tendsto (fun n => ζseq (σ n)) atTop (𝓝 (Φ winf)) := by
      have heqfun : (fun n => ζseq (σ n)) = (fun n => Φ (wseq (σ n))) :=
        funext fun n => (hwseqeq (σ n)).symm
      rw [heqfun]
      exact hΦcontAt.tendsto.comp hσtendsto
    have hζsubtendsto2 : Tendsto (fun n => ζseq (σ n)) atTop (𝓝 ζlim) :=
      hζtendsto.comp hσmono.tendsto_atTop
    have hζeq : ζlim = Φ winf := tendsto_nhds_unique hζsubtendsto2 hζsubtendsto1
    exact ⟨winf, hwinfS, hζeq.symm⟩
  -- STAGE 10: a point of `K` is approached from `unitDisc \ K` along a segment from `a₀`.
  set b : ℂ := ((M + 1) / 2 : ℝ) * (1 : ℂ) with hbdef
  have hbmem : b ∈ unitDisc \ K := hw0mem.1
  have ha₀norm : ‖a₀‖ < 1 := by have := hKunit ha₀; rwa [unitDisc, mem_ball, dist_zero_right] at this
  have hbnorm : ‖b‖ < 1 := by have := hbmem.1; rwa [unitDisc, mem_ball, dist_zero_right] at this
  set γseg : ℝ → ℂ := fun t => a₀ + (t : ℂ) * (b - a₀) with hγdef
  have hγsub : ∀ t ∈ Icc (0:ℝ) 1, γseg t ∈ unitDisc := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have heq : γseg t = (((1:ℝ) - t : ℝ) : ℂ) * a₀ + ((t:ℝ) : ℂ) * b := by
      show a₀ + (t:ℂ) * (b - a₀) = (((1:ℝ) - t : ℝ) : ℂ) * a₀ + ((t:ℝ) : ℂ) * b
      push_cast
      ring
    rw [unitDisc, mem_ball, dist_zero_right, heq]
    have hstep1 : ‖(((1:ℝ) - t : ℝ) : ℂ) * a₀ + ((t:ℝ) : ℂ) * b‖
        ≤ ‖(((1:ℝ) - t : ℝ) : ℂ) * a₀‖ + ‖((t:ℝ) : ℂ) * b‖ := norm_add_le _ _
    have hstep2 : ‖(((1:ℝ) - t : ℝ) : ℂ) * a₀‖ + ‖((t:ℝ) : ℂ) * b‖ = (1-t) * ‖a₀‖ + t * ‖b‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
    set d : ℝ := min (1 - ‖a₀‖) (1 - ‖b‖) with hddef
    have hdpos : 0 < d := lt_min (by linarith) (by linarith)
    have h1 : (1-t)*(1-‖a₀‖) ≥ (1-t)*d := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have h2 : t*(1-‖b‖) ≥ t*d := mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
    nlinarith [hstep1, hstep2, h1, h2, hdpos]
  have hγ0K : γseg 0 = a₀ := by show a₀ + (0:ℂ)*(b-a₀) = a₀; ring
  have hγ1nK : γseg 1 ∉ K := by
    have : γseg 1 = b := by show a₀ + (1:ℂ)*(b-a₀) = b; ring
    rw [this]; exact hbmem.2
  set Tset : Set ℝ := {t ∈ Icc (0:ℝ) 1 | γseg t ∈ K} with hTsetdef
  have hTsetne : Tset.Nonempty := ⟨0, ⟨left_mem_Icc.mpr zero_le_one, hγ0K ▸ ha₀⟩⟩
  have hTsetbdd : BddAbove Tset := ⟨1, fun t ht => ht.1.2⟩
  have hTsetclosed : IsClosed Tset := by
    have : Tset = Icc (0:ℝ) 1 ∩ γseg ⁻¹' K :=
      Set.ext fun t => by rw [hTsetdef]; simp [mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact isClosed_Icc.inter (hKcpt.isClosed.preimage (by fun_prop))
  set tstar : ℝ := sSup Tset with htstardef
  have htstarmem : tstar ∈ Tset := hTsetclosed.csSup_mem hTsetne hTsetbdd
  have htstarlt1 : tstar < 1 := by
    rcases lt_or_eq_of_le htstarmem.1.2 with h | h
    · exact h
    · exact absurd (h ▸ htstarmem.2) hγ1nK
  set q : ℂ := γseg tstar with hqdef
  have hqK : q ∈ K := htstarmem.2
  have hγcont : Continuous γseg := by fun_prop
  set tn : ℕ → ℝ := fun n => tstar + (1 - tstar) / (n + 1) with htndef
  have htnIcc : ∀ n, tn n ∈ Icc (0:ℝ) 1 := by
    intro n
    have hpos : 0 < (1 - tstar) / ((n:ℝ) + 1) := div_pos (by linarith) (by positivity)
    have hle : (1 - tstar) / ((n:ℝ) + 1) ≤ 1 - tstar :=
      div_le_self (by linarith) (by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
    rw [htndef]
    exact ⟨by linarith [htstarmem.1.1], by linarith⟩
  have htnnotmem : ∀ n, tn n ∉ Tset := by
    intro n hmem
    have hle := le_csSup hTsetbdd hmem
    have hpos : 0 < (1 - tstar) / ((n:ℝ) + 1) := div_pos (by linarith) (by positivity)
    rw [htndef] at hle
    simp only at hle
    linarith
  have hzn_mem : ∀ n, γseg (tn n) ∈ unitDisc \ K :=
    fun n => ⟨hγsub (tn n) (htnIcc n), fun hmem => htnnotmem n ⟨htnIcc n, hmem⟩⟩
  have htn_tendsto : Tendsto tn atTop (𝓝 tstar) := by
    have h0 : Tendsto (fun n : ℕ => (1 - tstar) / ((n:ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 - tstar)
      simpa [mul_one_div, div_eq_mul_inv] using this
    have hconst : Tendsto (fun _ : ℕ => tstar) atTop (𝓝 tstar) := tendsto_const_nhds
    have := hconst.add h0
    simpa [htndef] using this
  have hzn_tendsto : Tendsto (fun n => γseg (tn n)) atTop (𝓝 q) :=
    (hγcont.tendsto tstar).comp htn_tendsto
  -- `ψ`'s inverse is differentiable (hence continuous) on `disc`.
  have hinvψdiff : DifferentiableOn ℂ (Function.invFunOn ψ W) RMT.disc := by
    have := (RMT.differentiableOn_invFunOn_of_injOn hIsOpenW hψ.diff hψ.injOn).2
    rwa [hψbij.image_eq] at this
  have hinvψleft : ∀ w ∈ W, Function.invFunOn ψ W (ψ w) = w :=
    fun w hw => hψ.injOn.leftInvOn_invFunOn hw
  -- for every `ε > 0`, `Φ` gets within `ε` of the unit circle somewhere in `unitDisc \ K`.
  have hΦnear1 : ∀ ε : ℝ, 0 < ε → ∃ z ∈ unitDisc \ K, ‖Φ z‖ < 1 + ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hallge : ∀ n : ℕ, 1 + ε ≤ ‖Φ (γseg (tn n))‖ := fun n => hcon _ (hzn_mem n)
    set vn : ℕ → ℂ := fun n => φ (γseg (tn n)) with hvndef
    have hvnW : ∀ n, vn n ∈ W := fun n => hφVsubW ⟨_, ⟨mem_univ _, (hzn_mem n).2⟩, rfl⟩
    have hψvnbdd : ∀ n, ‖ψ (vn n)‖ ≤ (1 + ε)⁻¹ := by
      intro n
      have h2 : Φ (γseg (tn n)) = (ψ (vn n))⁻¹ := rfl
      have h3 : ‖Φ (γseg (tn n))‖ = ‖ψ (vn n)‖⁻¹ := by rw [h2, norm_inv]
      have hpos : 0 < ‖ψ (vn n)‖ := norm_pos_iff.mpr (hψφne _ ⟨mem_univ _, (hzn_mem n).2⟩)
      have h4 := hallge n
      rw [h3] at h4
      exact (le_inv_comm₀ hpos (by linarith)).mpr h4
    have hψvnmem : ∀ n, ψ (vn n) ∈ closedBall (0:ℂ) (1+ε)⁻¹ := fun n => by
      rw [mem_closedBall, dist_zero_right]; exact hψvnbdd n
    obtain ⟨ζinf, hζinfmem, σ, hσmono, hσtendsto⟩ :=
      (isCompact_closedBall (0:ℂ) (1+ε)⁻¹).tendsto_subseq hψvnmem
    have hεinv_lt_one : (1+ε)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; linarith
    have hζinfdisc : ζinf ∈ RMT.disc := by
      rw [mem_ball, dist_zero_right]
      rw [mem_closedBall, dist_zero_right] at hζinfmem
      linarith
    have hinvψcontAt : ContinuousAt (Function.invFunOn ψ W) ζinf :=
      (hinvψdiff.differentiableAt (isOpen_ball.mem_nhds hζinfdisc)).continuousAt
    have hvnsubtendsto : Tendsto (fun n => vn (σ n)) atTop (𝓝 (Function.invFunOn ψ W ζinf)) := by
      have heqfun : (fun n => vn (σ n)) =
          (fun n => Function.invFunOn ψ W (ψ (vn (σ n)))) :=
        funext fun n => (hinvψleft (vn (σ n)) (hvnW (σ n))).symm
      rw [heqfun]
      exact hinvψcontAt.tendsto.comp hσtendsto
    set winf : ℂ := Function.invFunOn ψ W ζinf with hwinfdef2
    have hwinfW : winf ∈ W := by
      rw [hwinfdef2]
      exact hψbij.surjOn.mapsTo_invFunOn hζinfdisc
    -- but `vn (σ n) = φ (γseg (tn (σ n)))`, and `γseg (tn (σ n)) → q ∈ K`
    have hzsubtendsto : Tendsto (fun n => γseg (tn (σ n))) atTop (𝓝 q) :=
      hzn_tendsto.comp hσmono.tendsto_atTop
    by_cases hqa₀ : q = a₀
    · -- `vn (σ n) → ∞` in norm, contradicting convergence to the finite `winf`
      have hsub_tendsto : Tendsto (fun n => γseg (tn (σ n)) - a₀) atTop (𝓝 (q - a₀)) :=
        hzsubtendsto.sub tendsto_const_nhds
      rw [hqa₀, sub_self] at hsub_tendsto
      have hnormtendsto : Tendsto (fun n => ‖γseg (tn (σ n)) - a₀‖) atTop (𝓝 0) := by
        simpa using hsub_tendsto.norm
      obtain ⟨Cb2, hCb2⟩ := (isBounded_range_of_tendsto _ hvnsubtendsto).exists_norm_le
      have hCb2nonneg : 0 ≤ Cb2 := le_trans (norm_nonneg _) (hCb2 _ (mem_range_self 0))
      have hCb2pos : (0:ℝ) < Cb2 + 1 := by linarith
      rw [Metric.tendsto_atTop] at hnormtendsto
      obtain ⟨N, hN⟩ := hnormtendsto (Cb2 + 1)⁻¹ (inv_pos.mpr hCb2pos)
      have hd0 : ‖γseg (tn (σ N)) - a₀‖ < (Cb2 + 1)⁻¹ := by
        have := hN N le_rfl; rwa [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at this
      have hzne : γseg (tn (σ N)) - a₀ ≠ 0 := by
        intro h
        apply (hzn_mem (σ N)).2
        rw [sub_eq_zero] at h
        rw [h]; exact ha₀
      have hd0pos : 0 < ‖γseg (tn (σ N)) - a₀‖ := norm_pos_iff.mpr hzne
      have hvnNeq : vn (σ N) = (γseg (tn (σ N)) - a₀)⁻¹ := rfl
      have hvnNnorm : ‖vn (σ N)‖ > Cb2 := by
        rw [hvnNeq, norm_inv]
        have := (lt_inv_comm₀ hd0pos hCb2pos).mp hd0
        linarith
      exact absurd (hCb2 (vn (σ N)) (mem_range_self N)) (not_le.mpr hvnNnorm)
    · -- `vn (σ n) → φ q ∈ Wᶜ`, contradicting convergence to the finite `winf ∈ W`
      have hφcontq : ContinuousAt φ q :=
        (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hqa₀)
      have hvnsubtendsto2 : Tendsto (fun n => vn (σ n)) atTop (𝓝 (φ q)) :=
        hφcontq.tendsto.comp hzsubtendsto
      have hveq : φ q = winf := tendsto_nhds_unique hvnsubtendsto2 hvnsubtendsto
      have hφqWc : φ q ∉ W := (hWceq (φ q)).mpr ⟨q, ⟨hqK, hqa₀⟩, rfl⟩
      exact hφqWc (hveq ▸ hwinfW)
  -- STAGE 11: extract a limit point of norm exactly `1` in `closure (Φ '' (unitDisc \ K))`.
  choose zk hzkmem hzknorm using fun k : ℕ => hΦnear1 (1 / (k + 1)) (by positivity)
  have hzkbdd : ∀ k, Φ (zk k) ∈ closedBall (0:ℂ) 2 := by
    intro k
    rw [mem_closedBall, dist_zero_right]
    have h1 : (1:ℝ) / (k+1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    linarith [hzknorm k]
  obtain ⟨ζinf2, hζinf2mem, τ, hτmono, hτtendsto⟩ :=
    (isCompact_closedBall (0:ℂ) 2).tendsto_subseq hzkbdd
  have hζinf2norm : ‖ζinf2‖ = 1 := by
    have h1 : Tendsto (fun k => ‖Φ (zk (τ k))‖) atTop (𝓝 ‖ζinf2‖) :=
      (continuous_norm.tendsto ζinf2).comp hτtendsto
    have h2 : Tendsto (fun k : ℕ => (1:ℝ) + 1 / ((τ k : ℝ) + 1)) atTop (𝓝 1) := by
      have : Tendsto (fun k : ℕ => (1:ℝ) / ((τ k : ℝ) + 1)) atTop (𝓝 0) := by
        have hcomp := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (hτmono.tendsto_atTop)
        exact hcomp
      simpa using tendsto_const_nhds.add this
    have h3 : ∀ k, 1 ≤ ‖Φ (zk (τ k))‖ := fun k =>
      (hΦmapsto ⟨mem_univ _, (hzkmem (τ k)).2⟩).le
    have h4 : ∀ k, ‖Φ (zk (τ k))‖ ≤ 1 + 1 / ((τ k : ℝ) + 1) := fun k => (hzknorm (τ k)).le
    exact le_antisymm (le_of_tendsto_of_tendsto' h1 h2 h4) (ge_of_tendsto' h1 h3)
  have hζinf2closedBall : ζinf2 ∈ closedBall (0:ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, hζinf2norm]
  have hζinf2closure : ζinf2 ∈ closure (Φ '' (unitDisc \ K)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at hτtendsto
    obtain ⟨N, hN⟩ := hτtendsto ε hε
    refine ⟨Φ (zk (τ N)), ⟨zk (τ N), hzkmem (τ N), rfl⟩, ?_⟩
    rw [dist_comm]; exact hN N le_rfl
  -- STAGE 12: `A' := closedBall 0 1 ∪ Φ '' (unitDisc \ K)` is preconnected.
  have hΦUDKcontOn : ContinuousOn Φ (unitDisc \ K) := hΦcont.mono (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hΦUDKpreconn : IsPreconnected (Φ '' (unitDisc \ K)) := hUDKPreconn.image Φ hΦUDKcontOn
  have hclosedBallPreconn : IsPreconnected (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).isPreconnected
  set A' : Set ℂ := closedBall (0:ℂ) 1 ∪ Φ '' (unitDisc \ K) with hA'def
  have ht_preconn : IsPreconnected (insert ζinf2 (Φ '' (unitDisc \ K))) :=
    hΦUDKpreconn.subset_closure (subset_insert _ _)
      (insert_subset_iff.mpr ⟨hζinf2closure, subset_closure⟩)
  have hA'preconn : IsPreconnected A' := by
    have hunion := IsPreconnected.union' (s := insert ζinf2 (Φ '' (unitDisc \ K)))
      (t := closedBall (0:ℂ) 1) ⟨ζinf2, mem_insert _ _, hζinf2closedBall⟩
      ht_preconn hclosedBallPreconn
    have heq : insert ζinf2 (Φ '' (unitDisc \ K)) ∪ closedBall (0:ℂ) 1 = A' := by
      rw [hA'def]
      ext w
      simp only [mem_union, mem_insert_iff]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (h ▸ hζinf2closedBall)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
    rwa [heq] at hunion
  have hA'ne : A'.Nonempty := ⟨0, Or.inl (mem_closedBall_self zero_le_one)⟩
  -- STAGE 13: identify `A'` with the bounded piece via `jordan_curve_theorem_complex_bounded`.
  obtain ⟨A, Bext, hAo, hBexto, hAconn, hBextconn, hABdisj, hACdisj, hBCdisj, hUnion,
      hAbdd, hBextUnbdd⟩ := jordan_curve_theorem_complex_bounded hcurveJordan
  have hwVofmem : ∀ w : ℂ, 1 < ‖w‖ → w ∈ univ \ K :=
    fun w hw => ⟨mem_univ _, fun hmem => by have := hKM w hmem; linarith⟩
  have hA'disj_curve : Disjoint A' (Φ '' sphere (0:ℂ) 1) := by
    rw [Set.disjoint_left]
    intro ζ hζA' hζc
    obtain ⟨r, hr1, hrb⟩ := hdistBound
    have hrle := hrb ζ hζc
    rcases hζA' with h1 | h1
    · rw [mem_closedBall, dist_zero_right] at h1; linarith
    · obtain ⟨z1, hz1, hz1eq⟩ := h1
      obtain ⟨z2, hz2, hz2eq⟩ := hζc
      have heq := hΦinj ⟨mem_univ _, hz1.2⟩ (hSphereSub hz2) (hz1eq.trans hz2eq.symm)
      have hz1lt : ‖z1‖ < 1 := by have h1 : dist z1 0 < 1 := hz1.1; rwa [dist_zero_right] at h1
      rw [heq] at hz1lt
      rw [mem_sphere_zero_iff_norm] at hz2
      linarith
  have hΦextPreconn : IsPreconnected (Φ '' {w : ℂ | 1 < ‖w‖}) :=
    (isPreconnected_setOf_lt_norm (le_refl (0:ℝ) |>.trans zero_le_one)).image Φ
      (hΦcont.mono (fun z hz => hwVofmem z hz))
  have hΦextNe : (Φ '' {w : ℂ | 1 < ‖w‖}).Nonempty := ⟨Φ 2, 2, by norm_num, rfl⟩
  have hΦextUnbdd : ¬ Bornology.IsBounded (Φ '' {w : ℂ | 1 < ‖w‖}) := by
    intro hbdd
    obtain ⟨Cb3, hCb3⟩ := hbdd.exists_norm_le
    obtain ⟨Rc3, hRc3⟩ := hΦinfty (Cb3 + 1)
    set w3 : ℂ := ((max Rc3 2 + 1 : ℝ) : ℂ) with hw3def
    have hw3gt1 : (1:ℝ) < ‖w3‖ := by
      rw [hw3def, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := le_max_right Rc3 2; linarith
    have hw3gtRc3 : Rc3 < ‖w3‖ := by
      rw [hw3def, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := le_max_left Rc3 2; linarith
    have h1 := hRc3 w3 (hwVofmem w3 hw3gt1) hw3gtRc3
    have h2 := hCb3 (Φ w3) ⟨w3, hw3gt1, rfl⟩
    linarith
  have hΦextDisjCurve : Disjoint (Φ '' {w : ℂ | 1 < ‖w‖}) (Φ '' sphere (0:ℂ) 1) := by
    rw [Set.disjoint_left]
    rintro ζ ⟨w, hw, rfl⟩ ⟨z, hz, hzeq⟩
    have heq := hΦinj (hwVofmem w hw) (hSphereSub hz) hzeq.symm
    rw [heq] at hw
    rw [mem_sphere_zero_iff_norm] at hz
    simp only [mem_setOf_eq] at hw
    linarith
  have hΦextSubAB : Φ '' {w : ℂ | 1 < ‖w‖} ⊆ A ∪ Bext := by
    rintro ζ ⟨w, hw, rfl⟩
    have hmem : Φ w ∈ A ∪ Bext ∪ Φ '' sphere (0:ℂ) 1 := hUnion ▸ mem_univ _
    rcases hmem with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (Set.disjoint_left.mp hΦextDisjCurve ⟨w, hw, rfl⟩)
  have hΦextInBext : Φ '' {w : ℂ | 1 < ‖w‖} ⊆ Bext := by
    rcases hΦextPreconn.subset_or_subset hAo hBexto hABdisj hΦextSubAB with h | h
    · exact absurd (hAbdd.subset h) hΦextUnbdd
    · exact h
  have hA'disjExt : Disjoint A' (Φ '' {w : ℂ | 1 < ‖w‖}) := by
    rw [Set.disjoint_left]
    intro ζ hζA' hζext
    obtain ⟨w, hw, rfl⟩ := hζext
    rcases hζA' with h1 | h1
    · rw [mem_closedBall, dist_zero_right] at h1
      have h2 := hΦmapsto (hwVofmem w hw)
      simp only [mem_setOf_eq] at h2
      linarith
    · obtain ⟨z1, hz1, hz1eq⟩ := h1
      have heq := hΦinj ⟨mem_univ _, hz1.2⟩ (hwVofmem w hw) hz1eq
      have hz1lt : ‖z1‖ < 1 := by have h1 : dist z1 0 < 1 := hz1.1; rwa [dist_zero_right] at h1
      rw [heq] at hz1lt
      simp only [mem_setOf_eq] at hw
      linarith
  have hUniv3 : A' ∪ Φ '' sphere (0:ℂ) 1 ∪ Φ '' {w : ℂ | 1 < ‖w‖} = univ := by
    rw [hA'def]
    ext ζ
    simp only [mem_union, mem_univ, iff_true]
    by_cases hζ1 : ζ ∈ closedBall (0:ℂ) 1
    · exact Or.inl (Or.inl (Or.inl hζ1))
    · rw [mem_closedBall, dist_zero_right, not_le] at hζ1
      obtain ⟨z, hz, hzeq⟩ := hΦsurj (show ζ ∈ {ζ:ℂ|1<‖ζ‖} from hζ1)
      by_cases hzs : z ∈ unitDisc
      · exact Or.inl (Or.inl (Or.inr ⟨z, ⟨hzs, hz.2⟩, hzeq⟩))
      · rw [unitDisc, mem_ball, dist_zero_right, not_lt] at hzs
        rcases eq_or_lt_of_le hzs with h | h
        · exact Or.inl (Or.inr ⟨z, by rw [mem_sphere_zero_iff_norm]; exact h.symm, hzeq⟩)
        · exact Or.inr ⟨z, h, hzeq⟩
  have hExtOpen : IsOpen (Φ '' {w : ℂ | 1 < ‖w‖}) := by
    have hUo : IsOpen ({w : ℂ | 1 < ‖w‖}) := isOpen_lt continuous_const continuous_norm
    have hUsub : {w : ℂ | 1 < ‖w‖} ⊆ univ \ K := fun w hw => hwVofmem w hw
    exact (RMT.differentiableOn_invFunOn_of_injOn hUo (hΦdiff.mono hUsub)
      (hΦinj.mono hUsub)).1
  -- `A'ᶜ = Φ '' S`, giving `A'` open from `hΦSclosed`.
  have hA'ceq : A'ᶜ = Φ '' S := by
    apply Set.eq_of_subset_of_subset
    · intro ζ hζ
      have hmem : ζ ∈ A' ∪ Φ '' sphere (0:ℂ) 1 ∪ Φ '' {w : ℂ | 1 < ‖w‖} := hUniv3 ▸ mem_univ _
      rcases hmem with (h | h) | h
      · exact absurd h hζ
      · obtain ⟨z, hz, hzeq⟩ := h
        exact ⟨z, le_of_eq (mem_sphere_zero_iff_norm.mp hz).symm, hzeq⟩
      · obtain ⟨w, hw, hweq⟩ := h
        simp only [mem_setOf_eq] at hw
        exact ⟨w, hw.le, hweq⟩
    · rintro ζ ⟨w, hw, rfl⟩ hmem
      rw [hSdef, mem_setOf_eq] at hw
      rcases eq_or_lt_of_le hw with h | h
      · exact Set.disjoint_left.mp hA'disj_curve hmem ⟨w, by rw [mem_sphere_zero_iff_norm]; exact h.symm, rfl⟩
      · exact Set.disjoint_left.mp hA'disjExt hmem ⟨w, h, rfl⟩
  have hA'open : IsOpen A' := by
    rw [← compl_compl A', isOpen_compl_iff, hA'ceq]
    exact hΦSclosed
  have hAsub3 : A ⊆ A' ∪ Φ '' {w : ℂ | 1 < ‖w‖} := by
    intro ζ hζ
    have hmem : ζ ∈ A' ∪ Φ '' sphere (0:ℂ) 1 ∪ Φ '' {w : ℂ | 1 < ‖w‖} := hUniv3 ▸ mem_univ _
    rcases hmem with (h | h) | h
    · exact Or.inl h
    · exact absurd h (Set.disjoint_left.mp hACdisj hζ)
    · exact Or.inr h
  have hAsubA' : A ⊆ A' := by
    rcases hAconn.2.subset_or_subset hA'open hExtOpen hA'disjExt hAsub3 with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hAconn.1
      exact absurd (h.trans hΦextInBext hx) (Set.disjoint_left.mp hABdisj hx)
  have hA'sub3 : A' ⊆ A ∪ Bext := by
    intro ζ hζ
    have hmem2 : ζ ∈ A ∪ Bext ∪ Φ '' sphere (0:ℂ) 1 := hUnion ▸ mem_univ _
    rcases hmem2 with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (Set.disjoint_left.mp hA'disj_curve hζ)
  have hA'subA : A' ⊆ A := by
    rcases hA'preconn.subset_or_subset hAo hBexto hABdisj hA'sub3 with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hAconn.1
      exact absurd (h (hAsubA' hx)) (Set.disjoint_left.mp hABdisj hx)
  have hAeqA' : A = A' := Set.Subset.antisymm hAsubA' hA'subA
  -- STAGE 14: assemble the final four conjuncts about `A`.
  have hAeqUnion : A = closedBall (0:ℂ) 1 ∪ Φ '' (unitDisc \ K) := hAeqA'.trans hA'def
  have hclosedBallSubA : closedBall (0:ℂ) 1 ⊆ A := by rw [hAeqUnion]; exact subset_union_left
  have hΦUDKdisjClosedBall : Disjoint (Φ '' (unitDisc \ K)) (closedBall (0:ℂ) 1) := by
    rw [Set.disjoint_left]
    rintro ζ ⟨z, hz, rfl⟩ hmem
    rw [mem_closedBall, dist_zero_right] at hmem
    have := hΦmapsto ⟨mem_univ _, hz.2⟩
    simp only [mem_setOf_eq] at this
    linarith
  have hAsubClosedBall : A \ closedBall (0:ℂ) 1 = Φ '' (unitDisc \ K) := by
    rw [hAeqUnion]
    ext ζ
    simp only [mem_diff, mem_union]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact absurd h h2
      · exact h
    · intro h
      exact ⟨Or.inr h, Set.disjoint_right.mp hΦUDKdisjClosedBall.symm h⟩
  have hAminusConn : IsConnected (A \ closedBall (0:ℂ) 1) := by
    rw [hAsubClosedBall]
    exact ⟨hUDKconn.nonempty.image Φ, hΦUDKpreconn⟩
  obtain ⟨r0, hr0gt1, hr0b⟩ := hdistBound
  have hballr0SubA : ball (0:ℂ) r0 ⊆ A := by
    have hballPreconn : IsPreconnected (ball (0:ℂ) r0) := (convex_ball (0:ℂ) r0).isPreconnected
    have hballDisjCurve : Disjoint (ball (0:ℂ) r0) (Φ '' sphere (0:ℂ) 1) := by
      rw [Set.disjoint_left]
      intro ζ hζ1 hζ2
      rw [mem_ball, dist_zero_right] at hζ1
      have := hr0b ζ hζ2
      linarith
    have hballSubAB : ball (0:ℂ) r0 ⊆ A ∪ Bext := by
      intro ζ hζ
      have hmem2 : ζ ∈ A ∪ Bext ∪ Φ '' sphere (0:ℂ) 1 := hUnion ▸ mem_univ _
      rcases hmem2 with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (Set.disjoint_left.mp hballDisjCurve hζ)
    rcases hballPreconn.subset_or_subset hAo hBexto hABdisj hballSubAB with h | h
    · exact h
    · exfalso
      have h0A : (0:ℂ) ∈ A := hclosedBallSubA (mem_closedBall_self zero_le_one)
      have h0ball : (0:ℂ) ∈ ball (0:ℂ) r0 := by rw [mem_ball, dist_zero_right, norm_zero]; linarith
      exact absurd (h h0ball) (Set.disjoint_left.mp hABdisj h0A)
  have hcollar : ∃ r : ℝ, 1 < r ∧ {ζ : ℂ | 1 < ‖ζ‖ ∧ ‖ζ‖ < r} ⊆ A :=
    ⟨r0, hr0gt1, fun ζ hζ => hballr0SubA (by rw [mem_ball, dist_zero_right]; exact hζ.2)⟩
  -- `Aᶜ = Φ '' S` is path-connected.
  have hAceq : Aᶜ = Φ '' S := hAeqA' ▸ hA'ceq
  have hSpathconn : IsPathConnected S := by
    have hrank : (1:Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]; norm_num
    have hspherepc : IsPathConnected (sphere (0:ℂ) 1) := isPathConnected_sphere hrank 0 zero_le_one
    have hSphereSub' : sphere (0:ℂ) 1 ⊆ S := fun z hz => by
      rw [hSdef, mem_setOf_eq]; exact le_of_eq (mem_sphere_zero_iff_norm.mp hz).symm
    set p0 : ℂ := 1 with hp0def
    have hp0S : p0 ∈ sphere (0:ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hp0def]; exact norm_one
    refine ⟨p0, hSphereSub' hp0S, fun w hw => ?_⟩
    rw [hSdef, mem_setOf_eq] at hw
    have hwne : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
    set u : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ) * w with hudef
    have hunorm : ‖u‖ = 1 := by
      rw [hudef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne)]
    have huS : u ∈ sphere (0:ℂ) 1 := mem_sphere_zero_iff_norm.mpr hunorm
    have hj1 : JoinedIn S w u := by
      apply JoinedIn.ofLine (F := S) (x := w) (y := u)
        (f := fun t : ℝ => (((1 - t) + t * ‖w‖⁻¹ : ℝ) : ℂ) * w)
      · fun_prop
      · show (((1 - (0:ℝ)) + (0:ℝ) * ‖w‖⁻¹ : ℝ) : ℂ) * w = w
        norm_num
      · show (((1 - (1:ℝ)) + (1:ℝ) * ‖w‖⁻¹ : ℝ) : ℂ) * w = u
        rw [hudef]; norm_num
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨ht0, ht1⟩ := ht
        have hwinv0 : (0:ℝ) ≤ ‖w‖⁻¹ := inv_nonneg.mpr (norm_nonneg w)
        have hcoefnn : (0:ℝ) ≤ (1 - t) + t * ‖w‖⁻¹ := by nlinarith
        rw [hSdef, mem_setOf_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoefnn]
        have hexpand : ((1 - t) + t * ‖w‖⁻¹) * ‖w‖ = (1 - t) * ‖w‖ + t := by
          field_simp
        rw [hexpand]
        nlinarith
    have hj2 : JoinedIn S u p0 :=
      (hspherepc.joinedIn u huS p0 hp0S).mono hSphereSub'
    exact (hj1.trans hj2).symm
  have hAcpathconn : IsPathConnected Aᶜ := by
    rw [hAceq]
    exact hSpathconn.image' hΦScont
  refine ⟨K, Φ, hKunit, hKcpt, hKconn, hKnt, ⟨f, hfdiff, hfinj, hfimg⟩, hΦdiff, hΦbij,
    hcurveJordan, ⟨r0, hr0gt1, hr0b⟩, A, Bext, hAo, hBexto, hAeqA' ▸ hAconn, hBextconn, hABdisj,
    hACdisj, hBCdisj, hUnion, hAeqA' ▸ hAbdd, hBextUnbdd, hAeqUnion, hAminusConn, hcollar,
    hclosedBallSubA, hAcpathconn⟩
end LiZhongQC
