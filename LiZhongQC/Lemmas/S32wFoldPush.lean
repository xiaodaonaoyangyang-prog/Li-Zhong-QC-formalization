import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.SchottkyCollarFromDouble

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section Common

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

include hd in
/-- The half `ιd(S)` of the double misses the punctures `Pd`. -/
theorem s32w_double_range_off_Pd : ∀ x : S, ιd x ∉ (↑Pd : Set Xd.carrier) := by
  classical
  intro x hx
  obtain ⟨e, -, het, -, -, hPd⟩ := s31pp_endpoints_exhaust F hd
  have hx' : ιd x ∈ Pd := hx
  rw [hPd] at hx'
  rcases Finset.mem_union.1 hx' with h | h
  · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
    have hoff := s31pp_endpoint_off_halves F hd (Finset.mem_coe.1 p.2) (het p)
    exact hoff.1 ⟨x, by rw [hp]⟩
  · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
    have hoff := s31pp_endpoint_off_halves F hd (Finset.mem_coe.1 p.2) (het p)
    refine hoff.2 ⟨x, ?_⟩
    change J (ιd x) = e p
    rw [← hp, hd.involution.1]

end Common

section Push

/-- A chart-local inward push: for a chart `w` of `X` with target `ball 0 r`, a cut-off `ψ ≥ 0` with compact support
inside the chart (positive on `‖w x‖ < r/2`), and a continuous family `P t` of maps, `P 0 = id`, which is the
identity off the chart and adds `i t ψ` to the chart coordinate for `t ∈ [0, 1]`. -/
theorem s32w_chart_push {X : Type*} [TopologicalSpace X] [T2Space X] (w : OpenPartialHomeomorph X ℂ)
    {r : ℝ} (hr : 0 < r) (htar : w.target = ball (0 : ℂ) r) :
    ∃ (ψ : X → ℝ) (P : ℝ → X → X),
      Continuous ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∀ x ∈ w.source, ‖w x‖ < r / 2 → 0 < ψ x) ∧
      Continuous (fun q : ℝ × X => P q.1 q.2) ∧ (∀ x, P 0 x = x) ∧
      (∀ t x, x ∉ w.source → P t x = x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ w.source,
        P t x ∈ w.source ∧ w (P t x) = w x + Complex.I * ((t * ψ x : ℝ) : ℂ)) := by
  classical
  let ψ : X → ℝ := fun x => if x ∈ w.source then r / 4 * max 0 (1 - 2 * ‖w x‖ / r) else 0
  let cl : ℝ → ℝ := fun t => min 1 (max 0 t)
  let P : ℝ → X → X := fun t x =>
    if x ∈ w.source then w.symm (w x + Complex.I * ((cl t * ψ x : ℝ) : ℂ)) else x
  have hψs : ∀ x ∈ w.source, ψ x = r / 4 * max 0 (1 - 2 * ‖w x‖ / r) := fun x hx => if_pos hx
  have hψn : ∀ x, x ∉ w.source → ψ x = 0 := fun x hx => if_neg hx
  have hψnn : ∀ x, 0 ≤ ψ x := by
    intro x
    by_cases hx : x ∈ w.source
    · rw [hψs x hx]
      positivity
    · rw [hψn x hx]
  have hψle : ∀ x, ψ x ≤ r / 4 := by
    intro x
    by_cases hx : x ∈ w.source
    · rw [hψs x hx]
      have h1 : max 0 (1 - 2 * ‖w x‖ / r) ≤ 1 := by
        refine max_le zero_le_one ?_
        have : 0 ≤ 2 * ‖w x‖ / r := by positivity
        linarith
      nlinarith
    · rw [hψn x hx]
      linarith
  have hψpos : ∀ x ∈ w.source, ‖w x‖ < r / 2 → 0 < ψ x := by
    intro x hx hlt
    rw [hψs x hx]
    have : 0 < 1 - 2 * ‖w x‖ / r := by
      have : 2 * ‖w x‖ / r < 1 := by
        rw [div_lt_one hr]
        linarith
      linarith
    exact mul_pos (by linarith) (lt_max_of_lt_right this)
  have hψbig : ∀ x ∈ w.source, 0 < ψ x → ‖w x‖ < r / 2 := by
    intro x hx hpos
    by_contra hcon
    push_neg at hcon
    rw [hψs x hx] at hpos
    have h1 : 1 - 2 * ‖w x‖ / r ≤ 0 := by
      have : 1 ≤ 2 * ‖w x‖ / r := by
        rw [le_div_iff₀ hr]
        linarith
      linarith
    rw [max_eq_left h1] at hpos
    simp at hpos
  have hcl : ∀ t, 0 ≤ cl t ∧ cl t ≤ 1 := fun t =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have htgt : ∀ t x, x ∈ w.source →
      w x + Complex.I * ((cl t * ψ x : ℝ) : ℂ) ∈ w.target := by
    intro t x hx
    have hwx : w x ∈ w.target := w.map_source hx
    rw [htar] at hwx ⊢
    by_cases hp : 0 < ψ x
    · have h1 := hψbig x hx hp
      rw [mem_ball_zero_iff] at hwx ⊢
      have hle : cl t * ψ x ≤ ψ x := by nlinarith [hψnn x, (hcl t).1, (hcl t).2]
      calc ‖w x + Complex.I * ((cl t * ψ x : ℝ) : ℂ)‖
          ≤ ‖w x‖ + ‖Complex.I * ((cl t * ψ x : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖w x‖ + cl t * ψ x := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg (hcl t).1 (hψnn x))]
        _ < r := by
          have := hψle x
          linarith
    · have : ψ x = 0 := le_antisymm (not_lt.1 hp) (hψnn x)
      simpa [this] using hwx
  set T : Set X := w.symm '' closedBall (0 : ℂ) (r / 2) with hTdef
  have hsubt : closedBall (0 : ℂ) (r / 2) ⊆ w.target := by
    rw [htar]
    exact closedBall_subset_ball (by linarith)
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : ℂ) (r / 2)).image_of_continuousOn (w.continuousOn_symm.mono hsubt)
  have hTsrc : T ⊆ w.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact w.map_target (hsubt hz)
  have hψ0 : ∀ x, x ∉ T → ψ x = 0 := by
    intro x hxT
    by_cases hx : x ∈ w.source
    · rw [hψs x hx]
      have hgt : r / 2 < ‖w x‖ := by
        by_contra hcon
        push_neg at hcon
        exact hxT ⟨w x, by simpa [mem_closedBall_zero_iff] using hcon, w.left_inv hx⟩
      have h1 : 1 - 2 * ‖w x‖ / r < 0 := by
        have : 1 < 2 * ‖w x‖ / r := by
          rw [lt_div_iff₀ hr]
          linarith
        linarith
      rw [max_eq_left h1.le]
      simp
    · exact hψn x hx
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ w.source
    · have hw : ContinuousAt w x := w.continuousAt hx
      have hf : ContinuousAt (fun y => r / 4 * max 0 (1 - 2 * ‖w y‖ / r)) x := by fun_prop
      refine hf.congr ?_
      filter_upwards [w.open_source.mem_nhds hx] with y hy
      exact (hψs y hy).symm
    · have hxT : x ∉ T := fun h => hx (hTsrc h)
      have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hTc.isClosed.isOpen_compl.mem_nhds hxT] with y hy
        exact hψ0 y hy
      exact continuousAt_const.congr hev.symm
  have hPc : Continuous (fun q : ℝ × X => P q.1 q.2) := by
    refine continuous_iff_continuousAt.2 fun q => ?_
    obtain ⟨t, x⟩ := q
    by_cases hx : x ∈ w.source
    · have hw : ContinuousAt w x := w.continuousAt hx
      have hcc : Continuous cl := by fun_prop
      have ha : ContinuousAt
          (fun q : ℝ × X => w q.2 + Complex.I * ((cl q.1 * ψ q.2 : ℝ) : ℂ)) (t, x) := by
        have h1 : ContinuousAt (fun q : ℝ × X => w q.2) (t, x) := hw.comp continuousAt_snd
        have h2 : ContinuousAt (fun q : ℝ × X => cl q.1 * ψ q.2) (t, x) :=
          (hcc.continuousAt.comp continuousAt_fst).mul (hψc.continuousAt.comp continuousAt_snd)
        exact h1.add (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp h2))
      have hsym : ContinuousAt w.symm (w x + Complex.I * ((cl t * ψ x : ℝ) : ℂ)) :=
        w.continuousAt_symm (htgt t x hx)
      have hcomp : ContinuousAt (w.symm ∘ fun q : ℝ × X =>
          w q.2 + Complex.I * ((cl q.1 * ψ q.2 : ℝ) : ℂ)) (t, x) :=
        ContinuousAt.comp (g := w.symm) hsym ha
      refine hcomp.congr ?_
      have hn : ∀ᶠ q : ℝ × X in 𝓝 (t, x), q.2 ∈ w.source :=
        continuousAt_snd.preimage_mem_nhds (w.open_source.mem_nhds hx)
      filter_upwards [hn] with q hq
      simp only [Function.comp, P, if_pos hq]
    · have hxT : x ∉ T := fun h => hx (hTsrc h)
      have hn : ∀ᶠ q : ℝ × X in 𝓝 (t, x), q.2 ∈ Tᶜ :=
        continuousAt_snd.preimage_mem_nhds (hTc.isClosed.isOpen_compl.mem_nhds hxT)
      have hev : ∀ᶠ q : ℝ × X in 𝓝 (t, x), P q.1 q.2 = q.2 := by
        filter_upwards [hn] with q hq
        by_cases hy : q.2 ∈ w.source
        · have h0 : ψ q.2 = 0 := hψ0 _ hq
          simp only [P, if_pos hy, h0, mul_zero, Complex.ofReal_zero, add_zero]
          exact w.left_inv hy
        · simp only [P, if_neg hy]
      exact continuousAt_snd.congr (hev.mono fun q hq => hq.symm)
  have hcl0 : cl 0 = 0 := by simp [cl]
  refine ⟨ψ, P, hψc, hψnn, hψpos, hPc, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ w.source
    · simp only [P, if_pos hx, hcl0, zero_mul, Complex.ofReal_zero, mul_zero, add_zero]
      exact w.left_inv hx
    · simp only [P, if_neg hx]
  · intro t x hx
    simp only [P, if_neg hx]
  · intro t ht x hx
    have hct : cl t = t := by
      simp only [cl]
      rw [max_eq_right ht.1, min_eq_right ht.2]
    have hmem := htgt t x hx
    rw [hct] at hmem
    simp only [P, if_pos hx, hct]
    exact ⟨w.map_target hmem, w.right_inv hmem⟩

end Push

section Compose

/-- Composition of finitely many continuous push families: the composite family fixes `A`-points, starts at `id`, and
sends every point `x` of `K` for which some member pushes it into `A` (at time `1`) into `A`. -/
theorem s32w_push_compose {X : Type*} [TopologicalSpace X] (A K : Set X)
    (L : List (ℝ → X → X))
    (hc : ∀ P ∈ L, Continuous (fun q : ℝ × X => P q.1 q.2))
    (h0 : ∀ P ∈ L, ∀ x, P 0 x = x)
    (hA : ∀ P ∈ L, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ A, P t x ∈ A)
    (hK : ∀ P ∈ L, ∀ x ∈ K, P 1 x ∈ A ∨ P 1 x = x) :
    ∃ H : ℝ → X → X, Continuous (fun q : ℝ × X => H q.1 q.2) ∧ (∀ x, H 0 x = x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ A, H t x ∈ A) ∧
      (∀ x ∈ K, (∃ P ∈ L, P 1 x ∈ A) → H 1 x ∈ A) := by
  induction L with
  | nil =>
    refine ⟨fun _ x => x, continuous_snd, fun _ => rfl, fun _ _ _ hx => hx, ?_⟩
    rintro x - ⟨P, hP, -⟩
    exact absurd hP (by simp)
  | cons P L ih =>
    have hPm : P ∈ P :: L := List.mem_cons.2 (Or.inl rfl)
    obtain ⟨H, hHc, hH0, hHA, hHK⟩ := ih
      (fun Q hQ => hc Q (List.mem_cons.2 (Or.inr hQ)))
      (fun Q hQ => h0 Q (List.mem_cons.2 (Or.inr hQ)))
      (fun Q hQ => hA Q (List.mem_cons.2 (Or.inr hQ)))
      (fun Q hQ => hK Q (List.mem_cons.2 (Or.inr hQ)))
    refine ⟨fun t x => H t (P t x), ?_, ?_, ?_, ?_⟩
    · have h1 : Continuous (fun q : ℝ × X => (q.1, P q.1 q.2)) :=
        continuous_fst.prodMk (hc P hPm)
      exact hHc.comp h1
    · intro x
      show H 0 (P 0 x) = x
      rw [h0 P hPm x, hH0]
    · intro t ht x hx
      exact hHA t ht _ (hA P hPm t ht x hx)
    · rintro x hxK ⟨Q, hQ, hQA⟩
      have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      rcases List.mem_cons.1 hQ with rfl | hQL
      · exact hHA 1 h1 _ hQA
      · rcases hK P hPm x hxK with hPA | hPx
        · exact hHA 1 h1 _ hPA
        · show H 1 (P 1 x) ∈ A
          rw [hPx]
          exact hHK x hxK ⟨Q, hQL, hQA⟩

end Compose

section Family

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

include hd in
/-- The pushing family on the double: continuous in `(t, x)`, `H 0 = id`, keeps the half `range ιd` in itself for
`t ∈ [0, 1]`, and pushes every fixed point into the half at time `1`. -/
theorem s32w_push_family : ∃ H : ℝ → Xd.carrier → Xd.carrier,
    Continuous (fun q : ℝ × Xd.carrier => H q.1 q.2) ∧ (∀ x, H 0 x = x) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ range ιd, H t x ∈ range ιd) ∧
    (∀ x, J x = x → H 1 x ∈ range ιd) := by
  classical
  have hKc : IsCompact {x : Xd.carrier | J x = x} :=
    (isClosed_eq J.continuous continuous_id).isCompact
  have hspec : ∀ p : Xd.carrier, ∃ (P : ℝ → Xd.carrier → Xd.carrier) (U : Set Xd.carrier),
      Continuous (fun q : ℝ × Xd.carrier => P q.1 q.2) ∧ (∀ x, P 0 x = x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ range ιd, P t x ∈ range ιd) ∧
      (∀ x, J x = x → P 1 x ∈ range ιd ∨ P 1 x = x) ∧
      U ∈ 𝓝 p ∧ (J p = p → ∀ x ∈ U, J x = x → P 1 x ∈ range ιd) := by
    intro p
    by_cases hp : J p = p
    · obtain ⟨wc, r, hr, hps, hw0, htar, -, -, hJ, hhalf, hfix⟩ := s31qc_fixed_chart hd hp
      obtain ⟨ψ, P, hψc, hψnn, hψpos, hPc, hP0, hPn, hPs⟩ := s32w_chart_push wc hr htar
      have himpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ wc.source,
          (wc (P t x)).im = (wc x).im + t * ψ x := by
        intro t ht x hx
        rw [(hPs t ht x hx).2]
        simp
      refine ⟨P, wc.source ∩ wc ⁻¹' ball (0 : ℂ) (r / 2), hPc, hP0, ?_, ?_, ?_, ?_⟩
      · intro t ht x hx
        by_cases hxs : x ∈ wc.source
        · have h1 : 0 < (wc x).im := (hhalf x hxs).2 hx
          have h2 : 0 < (wc (P t x)).im := by
            rw [himpos t ht x hxs]
            have := mul_nonneg ht.1 (hψnn x)
            linarith
          exact (hhalf _ (hPs t ht x hxs).1).1 h2
        · rw [hPn t x hxs]
          exact hx
      · intro x hx
        by_cases hxs : x ∈ wc.source
        · have h0 : (wc x).im = 0 := (hfix x hxs).2 hx
          by_cases hψ : 0 < ψ x
          · left
            have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
            have h2 : 0 < (wc (P 1 x)).im := by
              rw [himpos 1 h1 x hxs, h0]
              linarith
            exact (hhalf _ (hPs 1 h1 x hxs).1).1 h2
          · right
            have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
            have hz : ψ x = 0 := le_antisymm (not_lt.1 hψ) (hψnn x)
            obtain ⟨hmem, hval⟩ := hPs 1 h1 x hxs
            rw [hz] at hval
            simp only [mul_zero, Complex.ofReal_zero, add_zero] at hval
            exact wc.injOn hmem hxs hval
        · right
          exact hPn 1 x hxs
      · refine Filter.inter_mem (wc.open_source.mem_nhds hps) ?_
        exact (wc.continuousAt hps).preimage_mem_nhds (by rw [hw0]; exact ball_mem_nhds _ (half_pos hr))
      · intro _ x hxU hx
        obtain ⟨hxs, hxb⟩ := hxU
        have h0 : (wc x).im = 0 := (hfix x hxs).2 hx
        have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
        have hψ : 0 < ψ x := hψpos x hxs (by simpa using hxb)
        have h2 : 0 < (wc (P 1 x)).im := by
          rw [himpos 1 h1 x hxs, h0]
          linarith
        exact (hhalf _ (hPs 1 h1 x hxs).1).1 h2
    · exact ⟨fun _ x => x, univ, continuous_snd, fun _ => rfl, fun _ _ _ hx => hx,
        fun x _ => Or.inr rfl, univ_mem, fun h => absurd h hp⟩
  choose P U hPc hP0 hPA hPK hU hUcov using hspec
  obtain ⟨t, htK, htcov⟩ := hKc.elim_nhds_subcover U (fun p _ => hU p)
  obtain ⟨H, hHc, hH0, hHA, hHK⟩ := s32w_push_compose (range ιd) {x : Xd.carrier | J x = x}
    (t.toList.map P)
    (fun Q hQ => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hQ
      exact hPc p)
    (fun Q hQ => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hQ
      exact hP0 p)
    (fun Q hQ => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hQ
      exact hPA p)
    (fun Q hQ => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hQ
      exact hPK p)
  refine ⟨H, hHc, hH0, hHA, fun x hx => ?_⟩
  have hxm : x ∈ {x : Xd.carrier | J x = x} := hx
  obtain ⟨p, hpt, hxU⟩ := Set.mem_iUnion₂.1 (htcov hxm)
  exact hHK x hx ⟨P p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hpt, rfl⟩,
    hUcov p (htK p hpt) x hxU hx⟩

end Family

section Main

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

include hd in
/-- Fold the punctured double onto the closed half and push it into the half: a retraction `ρ` of the punctured
double onto the surface with `ρ ∘ ι ≃ id`. -/
theorem s32w_fold_push :
    ∃ (G : C(S, ↥(puncturedOpens Pd))) (ρ : C(↥(puncturedOpens Pd), S)),
      (∀ x, (G x : Xd.carrier) = ιd x) ∧
      ContinuousMap.Homotopic (ρ.comp G) (ContinuousMap.id S) := by
  classical
  have hoff := s32w_double_range_off_Pd F hd
  obtain ⟨H, hHc, hH0, hHA, hHK⟩ := s32w_push_family F hd
  have hAo : IsOpen (range ιd) := hd.embedding.isOpen_range
  let G : C(S, ↥(puncturedOpens Pd)) :=
    ⟨fun x => ⟨ιd x, hoff x⟩, hd.embedding.continuous.subtype_mk _⟩
  have hyD : ∀ y : ↥(puncturedOpens Pd), (y : Xd.carrier) ∉ (↑Pd : Set Xd.carrier) :=
    fun y => y.2
  have hJP : ∀ x : Xd.carrier, x ∉ (↑Pd : Set Xd.carrier) → J x ∉ (↑Pd : Set Xd.carrier) := by
    intro x hx hJx
    apply hx
    have h1 : J (J x) ∈ J '' (↑Pd : Set Xd.carrier) := ⟨J x, hJx, rfl⟩
    rw [hd.Pd_invariant] at h1
    rwa [hd.involution.1] at h1
  -- the fold
  let r : ↥(puncturedOpens Pd) → Xd.carrier := fun y =>
    if (y : Xd.carrier) ∈ closure (range ιd) then (y : Xd.carrier) else J y
  have hrc : Continuous r := by
    refine Continuous.if (fun y hy => ?_) continuous_subtype_val
      (J.continuous.comp continuous_subtype_val)
    have h1 := (continuous_subtype_val.frontier_preimage_subset (closure (range ιd))) hy
    have h2 : (y : Xd.carrier) ∈ frontier (range ιd) := frontier_closure_subset h1
    have h3 : (y : Xd.carrier) ∈ frontier (range ιd) \ (↑Pd : Set Xd.carrier) := ⟨h2, hyD y⟩
    rw [← hd.fixed_curves] at h3
    exact h3.symm
  have hrcl : ∀ y : ↥(puncturedOpens Pd), r y ∈ closure (range ιd) := by
    intro y
    by_cases hy : (y : Xd.carrier) ∈ closure (range ιd)
    · simp only [r, if_pos hy]
      exact hy
    · simp only [r, if_neg hy]
      have hcov : (y : Xd.carrier) ∈ (univ : Set Xd.carrier) := mem_univ _
      rw [← hd.cover] at hcov
      rcases hcov with ((h | h) | h) | h
      · exact absurd (subset_closure h) hy
      · obtain ⟨s, hs⟩ := h
        apply subset_closure
        refine ⟨s, ?_⟩
        have hs' : J (ιd s) = (y : Xd.carrier) := hs
        rw [← hs', hd.involution.1]
      · have h' := h
        rw [hd.fixed_curves] at h'
        exact absurd (frontier_subset_closure h'.1) hy
      · exact absurd h (hyD y)
  have hrD : ∀ y : ↥(puncturedOpens Pd), r y ∉ (↑Pd : Set Xd.carrier) := by
    intro y
    by_cases hy : (y : Xd.carrier) ∈ closure (range ιd)
    · simp only [r, if_pos hy]
      exact hyD y
    · simp only [r, if_neg hy]
      exact hJP _ (hyD y)
  have hmem : ∀ y : ↥(puncturedOpens Pd), H 1 (r y) ∈ range ιd := by
    intro y
    by_cases hA : r y ∈ range ιd
    · exact hHA 1 ⟨zero_le_one, le_rfl⟩ _ hA
    · have hfr : r y ∈ frontier (range ιd) := by
        rw [hAo.frontier_eq]
        exact ⟨hrcl y, hA⟩
      have hK : r y ∈ {x | J x = x} := by
        rw [hd.fixed_curves]
        exact ⟨hfr, hrD y⟩
      exact hHK _ hK
  have hrG : ∀ x : S, r (G x) = ιd x := by
    intro x
    have hx : ((G x : ↥(puncturedOpens Pd)) : Xd.carrier) ∈ closure (range ιd) :=
      subset_closure ⟨x, rfl⟩
    simp only [r, if_pos hx]
    rfl
  let e' : S ≃ₜ range ιd := hd.embedding.isEmbedding.toHomeomorph
  let ρ : C(↥(puncturedOpens Pd), S) :=
    ⟨fun y => e'.symm ⟨H 1 (r y), hmem y⟩,
      e'.symm.continuous.comp
        (Continuous.subtype_mk (hHc.comp (continuous_const.prodMk hrc)) hmem)⟩
  have hmemH : ∀ (t : unitInterval) (x : S), H (1 - (t : ℝ)) (ιd x) ∈ range ιd := by
    intro t x
    exact hHA _ ⟨sub_nonneg.2 t.2.2, sub_le_self _ t.2.1⟩ _ ⟨x, rfl⟩
  let Hh : ContinuousMap.Homotopy (ρ.comp G) (ContinuousMap.id S) :=
    { toFun := fun p => e'.symm ⟨H (1 - (p.1 : ℝ)) (ιd p.2), hmemH p.1 p.2⟩
      continuous_toFun := by
        exact e'.symm.continuous.comp
          (Continuous.subtype_mk
            (hHc.comp ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
              (hd.embedding.continuous.comp continuous_snd))) fun p => hmemH p.1 p.2)
      map_zero_left := by
        intro x
        show e'.symm ⟨H (1 - ((0 : unitInterval) : ℝ)) (ιd x), _⟩ = e'.symm ⟨H 1 (r (G x)), _⟩
        congr 1
        apply Subtype.ext
        show H (1 - ((0 : unitInterval) : ℝ)) (ιd x) = H 1 (r (G x))
        rw [hrG x]
        simp
      map_one_left := by
        intro x
        show e'.symm ⟨H (1 - ((1 : unitInterval) : ℝ)) (ιd x), _⟩ = x
        have h1 : H (1 - ((1 : unitInterval) : ℝ)) (ιd x) = ιd x := by
          simp [hH0]
        have h2 : e'.symm ⟨H (1 - ((1 : unitInterval) : ℝ)) (ιd x), hmemH 1 x⟩ =
            e'.symm ⟨ιd x, ⟨x, rfl⟩⟩ := by
          congr 1
          exact Subtype.ext h1
        rw [h2]
        exact hd.embedding.isEmbedding.toHomeomorph_symm_apply x }
  exact ⟨G, ρ, fun x => rfl, ⟨Hh⟩⟩

end Main

section Descend

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F₁ : FiniteTypeStructure S g n m) {Xd₁ : ClosedRS.{u}}
  {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₁ : Finset Xd₁.carrier}
  (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)

include hd₁ in
/-- Descent of a homotopy of maps between punctured doubles to the surfaces (the folding step of the restriction). -/
theorem s32w_descend_homotopy {S₀ : Type*} [TopologicalSpace S₀] {Xd₀ : ClosedRS.{u}}
    {Pd₀ : Finset Xd₀.carrier} {f f₀ : C(S₀, S)}
    {v h : C(↥(puncturedOpens Pd₀), ↥(puncturedOpens Pd₁))}
    {G₀ : C(S₀, ↥(puncturedOpens Pd₀))} {G₁ : C(S, ↥(puncturedOpens Pd₁))}
    (hG₁ : ∀ x, (G₁ x : Xd₁.carrier) = ιd₁ x)
    (hv : ∀ x, v (G₀ x) = G₁ (f x)) (hh : ∀ x, h (G₀ x) = G₁ (f₀ x))
    (hvh : ContinuousMap.Homotopic v h) : ContinuousMap.Homotopic f f₀ := by
  obtain ⟨G', ρ, hG', hρ⟩ := s32w_fold_push F₁ hd₁
  have hGG : G' = G₁ := by
    ext x
    exact (hG' x).trans (hG₁ x).symm
  subst hGG
  have e1 : ContinuousMap.Homotopic f ((ρ.comp G').comp f) := by
    have := ContinuousMap.Homotopic.comp hρ (ContinuousMap.Homotopic.refl f)
    rw [ContinuousMap.id_comp] at this
    exact this.symm
  have e2 : ContinuousMap.Homotopic ((ρ.comp G').comp f) ((ρ.comp G').comp f₀) := by
    have hl : (ρ.comp G').comp f = ρ.comp (v.comp G₀) := by
      ext x
      simp [hv]
    have hr : (ρ.comp G').comp f₀ = ρ.comp (h.comp G₀) := by
      ext x
      simp [hh]
    rw [hl, hr]
    exact ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl ρ) (ContinuousMap.Homotopic.comp hvh (ContinuousMap.Homotopic.refl G₀))
  have e3 : ContinuousMap.Homotopic ((ρ.comp G').comp f₀) f₀ := by
    have := ContinuousMap.Homotopic.comp hρ (ContinuousMap.Homotopic.refl f₀)
    rwa [ContinuousMap.id_comp] at this
  exact e1.trans (e2.trans e3)

end Descend

end LiZhongQC
