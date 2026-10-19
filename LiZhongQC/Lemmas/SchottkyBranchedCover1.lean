import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Convex

/-!
# Connected double covers of a punctured disc

A path connected two-sheeted covering `q : Y → D*_r` of the punctured disc is the squaring map:
there is an open embedding `w : Y → ℂ` onto `D*_{√r}` with `w² = q` (`s82bc_dstar_double_cover`).
-/

open Set Complex Topology

noncomputable section
namespace LiZhongQC

universe u

/-- The exponential map from a left half plane onto a punctured disc is a covering map. -/
theorem s82bc_exp_covering (r : ℝ) (hr : 0 < r)
    (E : {u : ℂ // u.re < Real.log r} → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r})
    (hE : ∀ u, (E u : ℂ) = Complex.exp u.1) : IsCoveringMap E := by
  let e' : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, z.exp_ne_zero⟩
  let t : Set {z : ℂ // z ≠ 0} := {z | ‖z.1‖ < r}
  have h1 : IsCoveringMap (t.restrictPreimage e') := Complex.isCoveringMap_exp.restrictPreimage t
  have hset : {u : ℂ | u.re < Real.log r} = e' ⁻¹' t := by
    ext u
    simp only [mem_setOf_eq, mem_preimage, t, e', Complex.norm_exp]
    rw [← Real.exp_lt_exp, Real.exp_log hr]
  let A : {u : ℂ // u.re < Real.log r} ≃ₜ ↥(e' ⁻¹' t) := Homeomorph.setCongr hset
  let B : ↥t ≃ₜ {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r} :=
    { toFun := fun z => ⟨z.1.1, norm_pos_iff.mpr z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, norm_pos_iff.mp z.2.1⟩, z.2.2⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h2 := (h1.comp_homeomorph A).homeomorph_comp B
  convert h2 using 1
  funext u
  exact Subtype.ext (hE u)

/-- In a two-element set, the middle one of three elements differing from it is determined. -/
theorem s82bc_two_pts {α : Type*} {s : Set α} (hs : s.ncard = 2) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hba : b ≠ a) (hbc : b ≠ c) : a = c := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp hs
  simp only [mem_insert_iff, mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all

/-- **Lifting the exponential to a two-sheeted cover of a punctured disc.**  Let `q : Y → D*` be a
two-sheeted covering of the punctured disc of radius `r` with `Y` path connected.  Then the
exponential `exp : {Re u < log r} → D*` lifts to `ℓ : H → Y`, which is onto, and `ℓ v = ℓ u` for
`v = u + 2πik` exactly when `k` is even. -/
theorem s82bc_dstar_lift {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y]
    (r : ℝ) (hr : 0 < r) (q : Y → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r}) (hq : IsCoveringMap q)
    (hfib : ∀ z, (q ⁻¹' {z}).ncard = 2) :
    ∃ ℓ : C({u : ℂ // u.re < Real.log r}, Y), (∀ u, (q (ℓ u) : ℂ) = Complex.exp u.1) ∧
      Function.Surjective ℓ ∧
      ∀ (k : ℤ) (u v : {u : ℂ // u.re < Real.log r}),
        v.1 = u.1 + k * (2 * Real.pi * Complex.I) → (ℓ v = ℓ u ↔ Even k) := by
  classical
  have hmem : ∀ u : {u : ℂ // u.re < Real.log r},
      0 < ‖Complex.exp u.1‖ ∧ ‖Complex.exp u.1‖ < r := by
    intro u
    refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
    rw [Complex.norm_exp]
    calc Real.exp u.1.re < Real.exp (Real.log r) := Real.exp_lt_exp.mpr u.2
      _ = r := Real.exp_log hr
  let E : {u : ℂ // u.re < Real.log r} → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r} :=
    fun u => ⟨Complex.exp u.1, hmem u⟩
  have hEcov : IsCoveringMap E := s82bc_exp_covering r hr E (fun u => rfl)
  have hEc : Continuous E := hEcov.continuous
  have hconv : Convex ℝ {u : ℂ | u.re < Real.log r} := convex_halfSpace_re_lt _
  have hopen : IsOpen {u : ℂ | u.re < Real.log r} :=
    isOpen_lt Complex.continuous_re continuous_const
  have : SimplyConnectedSpace {u : ℂ // u.re < Real.log r} := by
    have : ContractibleSpace {u : ℂ // u.re < Real.log r} :=
      Convex.contractibleSpace hconv ⟨((Real.log r - 1 : ℝ) : ℂ), by
        show (((Real.log r - 1 : ℝ) : ℂ)).re < Real.log r
        rw [Complex.ofReal_re]; linarith⟩
    exact SimplyConnectedSpace.ofContractible _
  haveI : LocallyPathConnectedSpace {u : ℂ // u.re < Real.log r} := hopen.locallyPathConnectedSpace
  obtain ⟨a⟩ : Nonempty Y := inferInstance
  have hu₀re : (Complex.log (q a : ℂ)).re < Real.log r := by
    rw [Complex.log_re]
    exact Real.log_lt_log (norm_pos_iff.mpr (norm_pos_iff.mp (q a).2.1)) (q a).2.2
  let u₀ : {u : ℂ // u.re < Real.log r} := ⟨Complex.log (q a : ℂ), hu₀re⟩
  have hu₀ : E u₀ = q a :=
    Subtype.ext (Complex.exp_log (norm_pos_iff.mp (q a).2.1))
  obtain ⟨ℓ, ⟨hℓ0, hℓq⟩, -⟩ := hq.existsUnique_continuousMap_lifts ⟨E, hEc⟩ u₀ a hu₀.symm
  have hℓE : ∀ u, q (ℓ u) = E u := fun u => congrFun hℓq u
  have hsurj : Function.Surjective ℓ := by
    intro y
    let γ : Path a y := PathConnectedSpace.somePath a y
    let δ : C(unitInterval, {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r}) :=
      ⟨fun t => q (γ t), hq.continuous.comp γ.continuous⟩
    have hδ0 : δ 0 = E u₀ := by
      show q (γ 0) = E u₀
      rw [γ.source, hu₀]
    have hΓ : E ∘ (hEcov.liftPath δ u₀ hδ0) = δ := hEcov.liftPath_lifts δ u₀ hδ0
    have heq : ℓ ∘ (hEcov.liftPath δ u₀ hδ0) = γ := by
      refine hq.eq_of_comp_eq (ℓ.continuous.comp (hEcov.liftPath δ u₀ hδ0).continuous)
        γ.continuous ?_ 0 ?_
      · funext t
        simp only [Function.comp_apply]
        rw [hℓE]
        exact congrFun hΓ t
      · simp only [Function.comp_apply]
        rw [hEcov.liftPath_zero, hℓ0, γ.source]
    exact ⟨hEcov.liftPath δ u₀ hδ0 1, by simpa using congrFun heq 1⟩
  refine ⟨ℓ, fun u => by rw [hℓE], hsurj, ?_⟩
  have hre : ∀ (u : {u : ℂ // u.re < Real.log r}) (k : ℤ),
      (u.1 + k * (2 * Real.pi * Complex.I)).re < Real.log r := by
    intro u k
    have : (u.1 + k * (2 * Real.pi * Complex.I)).re = u.1.re := by simp
    rw [this]; exact u.2
  let T : {u : ℂ // u.re < Real.log r} → {u : ℂ // u.re < Real.log r} :=
    fun u => ⟨u.1 + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I), hre u 1⟩
  have hTc : Continuous T :=
    Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
  have hET : ∀ u, E (T u) = E u := fun u => Subtype.ext (by
    show Complex.exp (u.1 + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = Complex.exp u.1
    rw [Int.cast_one, one_mul]; exact Complex.exp_periodic u.1)
  have hqT : ∀ u, q (ℓ (T u)) = q (ℓ u) := fun u => by rw [hℓE, hℓE, hET]
  -- a period `p` of `ℓ` propagates to all multiples
  have hper : ∀ p : ℤ, (∀ w v : {u : ℂ // u.re < Real.log r},
      v.1 = w.1 + p * (2 * Real.pi * Complex.I) → ℓ v = ℓ w) →
      ∀ (k : ℤ) (u v : {u : ℂ // u.re < Real.log r}),
        v.1 = u.1 + (k * p : ℤ) * (2 * Real.pi * Complex.I) → ℓ v = ℓ u := by
    intro p hp k
    induction k using Int.induction_on with
    | zero =>
      intro u v hv
      have : v = u := Subtype.ext (by simpa using hv)
      rw [this]
    | succ i ih =>
      intro u v hv
      let v' : {u : ℂ // u.re < Real.log r} := ⟨v.1 - (p : ℂ) * (2 * Real.pi * Complex.I),
        by
          have : (v.1 - (p : ℂ) * (2 * Real.pi * Complex.I)).re = v.1.re := by simp
          rw [this]; exact v.2⟩
      have h1 : ℓ v' = ℓ u := ih u v' (by
        show v.1 - (p : ℂ) * (2 * Real.pi * Complex.I) = _
        rw [hv]; push_cast; ring)
      rw [← h1]
      exact hp v' v (by show v.1 = v.1 - (p : ℂ) * (2 * Real.pi * Complex.I) + _; ring)
    | pred i ih =>
      intro u v hv
      let v' : {u : ℂ // u.re < Real.log r} := ⟨v.1 + (p : ℂ) * (2 * Real.pi * Complex.I),
        by
          have : (v.1 + (p : ℂ) * (2 * Real.pi * Complex.I)).re = v.1.re := by simp
          rw [this]; exact v.2⟩
      have h1 : ℓ v' = ℓ u := ih u v' (by
        show v.1 + (p : ℂ) * (2 * Real.pi * Complex.I) = _
        rw [hv]; push_cast; ring)
      rw [← h1]
      exact (hp v v' (by show v.1 + (p : ℂ) * (2 * Real.pi * Complex.I) = _; rfl)).symm
  -- `ℓ (u + 2πi) ≠ ℓ u`
  have hfibre : ∀ u, (q ⁻¹' {E u}).ncard = 2 := fun u => hfib _
  have hne : ∀ u, ℓ (T u) ≠ ℓ u := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u₁, hu₁⟩ := hcon
    have hall : ℓ ∘ T = ℓ :=
      hq.eq_of_comp_eq (ℓ.continuous.comp hTc) ℓ.continuous (funext hqT) u₁ hu₁
    have hall' : ∀ w v : {u : ℂ // u.re < Real.log r},
        v.1 = w.1 + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) → ℓ v = ℓ w := by
      intro w v hv
      have : v = T w := Subtype.ext hv
      rw [this]; exact congrFun hall w
    obtain ⟨x, y, hxy, hfx⟩ := Set.ncard_eq_two.mp (hfib (q a))
    have hax : a ∈ q ⁻¹' {q a} := rfl
    rw [hfx] at hax
    obtain ⟨a', hqa', hna'⟩ : ∃ a', q a' = q a ∧ a' ≠ a := by
      rcases hax with h | h
      · refine ⟨y, ?_, ?_⟩
        · have : y ∈ q ⁻¹' {q a} := by rw [hfx]; simp
          exact this
        · rw [h]; exact hxy.symm
      · refine ⟨x, ?_, ?_⟩
        · have : x ∈ q ⁻¹' {q a} := by rw [hfx]; simp
          exact this
        · rw [h]; exact hxy
    obtain ⟨u₂, hu₂⟩ := hsurj a'
    have hexp : Complex.exp u₂.1 = Complex.exp u₀.1 := by
      have h1 : (E u₂ : ℂ) = Complex.exp u₂.1 := rfl
      have h2 : (E u₀ : ℂ) = Complex.exp u₀.1 := rfl
      rw [← h1, ← h2, hu₀, ← hℓE, hu₂, hqa']
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have := hper 1 hall' k u₀ u₂ (by rw [hk]; simp)
    exact hna' (by rw [← hu₂, this, hℓ0])
  have hTT : ∀ w, ℓ (T (T w)) = ℓ w := by
    intro w
    have hm : ∀ z, z ∈ q ⁻¹' {E w} → z = ℓ w ∨ z = ℓ (T w) := by
      intro z hz
      have h2 := hfibre w
      by_cases hzw : z = ℓ w
      · exact Or.inl hzw
      · refine Or.inr ?_
        exact (s82bc_two_pts h2 (a := z) (b := ℓ w) (c := ℓ (T w)) hz
          (by show q (ℓ w) = E w; exact hℓE w) (by show q (ℓ (T w)) = E w; rw [hℓE, hET])
          (Ne.symm hzw) (Ne.symm (hne w)))
    have h3 : ℓ (T (T w)) ∈ q ⁻¹' {E w} := by
      show q (ℓ (T (T w))) = E w; rw [hℓE, hET, hET]
    have := hm _ h3
    rcases this with h | h
    · exact h
    · exact absurd h (hne (T w))
  intro k u v hv
  have hev : ∀ (m : ℤ) (u v : {u : ℂ // u.re < Real.log r}),
      v.1 = u.1 + (m * 2 : ℤ) * (2 * Real.pi * Complex.I) → ℓ v = ℓ u := by
    refine hper 2 ?_
    intro w v hv
    have : v = T (T w) := Subtype.ext (by
      show v.1 = w.1 + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      rw [hv]; push_cast; ring)
    rw [this]; exact hTT w
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · -- even
    subst hm
    exact ⟨fun _ => ⟨m, by ring⟩, fun _ => hev m u v (by rw [hv]; push_cast; ring)⟩
  · -- odd
    subst hm
    constructor
    · intro h
      exfalso
      let u' : {u : ℂ // u.re < Real.log r} := ⟨u.1 + (m * 2 : ℤ) * (2 * Real.pi * Complex.I),
        hre u _⟩
      have h1 : ℓ u' = ℓ u := hev m u u' rfl
      have h2 : v = T u' := Subtype.ext (by
        show v.1 = u.1 + ((m * 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        rw [hv]; push_cast; ring)
      exact hne u' (by rw [← h2, h1, h])
    · intro h
      exfalso
      obtain ⟨j, hj⟩ := h
      omega

/-- **Connected double covers of a punctured disc are squaring maps.**  If `q : Y → D*_r` is a
two-sheeted covering with `Y` path connected, there is an open embedding `w : Y → ℂ` onto the
punctured disc of radius `√r` with `w² = q`. -/
theorem s82bc_dstar_double_cover {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y]
    (r : ℝ) (hr : 0 < r) (q : Y → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r}) (hq : IsCoveringMap q)
    (hfib : ∀ z, (q ⁻¹' {z}).ncard = 2) :
    ∃ w : Y → ℂ, Continuous w ∧ IsOpenMap w ∧ Function.Injective w ∧
      range w = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < Real.sqrt r} ∧ ∀ y, w y ^ 2 = (q y : ℂ) := by
  classical
  obtain ⟨ℓ, hℓq, hsurj, hpar⟩ := s82bc_dstar_lift r hr q hq hfib
  -- `ℓ` is a local homeomorphism
  have hmem : ∀ u : {u : ℂ // u.re < Real.log r},
      0 < ‖Complex.exp u.1‖ ∧ ‖Complex.exp u.1‖ < r := by
    intro u
    refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
    rw [Complex.norm_exp]
    calc Real.exp u.1.re < Real.exp (Real.log r) := Real.exp_lt_exp.mpr u.2
      _ = r := Real.exp_log hr
  let E : {u : ℂ // u.re < Real.log r} → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r} :=
    fun u => ⟨Complex.exp u.1, hmem u⟩
  have hEcov : IsCoveringMap E := s82bc_exp_covering r hr E (fun u => rfl)
  have hqℓ : q ∘ ℓ = E := funext fun u => Subtype.ext (hℓq u)
  have hℓlh : IsLocalHomeomorph ℓ := by
    refine IsLocalHomeomorph.of_comp ?_ hq.isLocalHomeomorph ℓ.continuous
    rw [hqℓ]; exact hEcov.isLocalHomeomorph
  have hℓopen : IsOpenMap ℓ := hℓlh.isOpenMap
  have hℓquot : Topology.IsQuotientMap ℓ := hℓopen.isQuotientMap ℓ.continuous hsurj
  -- the square root coordinate
  let G : {u : ℂ // u.re < Real.log r} → ℂ := fun u => Complex.exp (u.1 / 2)
  have hopen : IsOpen {u : ℂ | u.re < Real.log r} := isOpen_lt Complex.continuous_re continuous_const
  have hGopen : IsOpenMap G := by
    have h1 : IsOpenMap (fun u : {u : ℂ // u.re < Real.log r} => u.1 / 2) := by
      have : (fun u : {u : ℂ // u.re < Real.log r} => u.1 / 2) =
          (fun z : ℂ => z / 2) ∘ Subtype.val := rfl
      rw [this]
      exact (IsOpenMap.of_inverse (f' := fun z : ℂ => 2 * z) (by fun_prop) (by intro z; ring)
        (by intro z; ring)).comp (hopen.isOpenMap_subtype_val)
    exact Complex.isOpenMap_exp.comp h1
  have hGc : Continuous G := by fun_prop
  -- `G` is constant on the fibres of `ℓ`
  have hGfib : ∀ u v, ℓ u = ℓ v → G u = G v := by
    intro u v h
    have hE : Complex.exp u.1 = Complex.exp v.1 := by rw [← hℓq u, ← hℓq v, h]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE
    have hev : Even k := (hpar k v u hk).mp h
    obtain ⟨m, rfl⟩ := hev
    show Complex.exp (u.1 / 2) = Complex.exp (v.1 / 2)
    rw [hk]
    have : (v.1 + ((m + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) / 2 =
        v.1 / 2 + (m : ℤ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- injectivity of `G` modulo `ℓ`
  have hGinj : ∀ u v, G u = G v → ℓ u = ℓ v := by
    intro u v h
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have hk : u.1 = v.1 + ((m * 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have : u.1 = 2 * (u.1 / 2) := by ring
      rw [this, hm]; push_cast; ring
    exact (hpar (m * 2) v u hk).mpr ⟨m, by ring⟩
  have hsurj' := hsurj
  choose s hs using hsurj'
  let w : Y → ℂ := fun y => G (s y)
  have hwℓ : ∀ u, w (ℓ u) = G u := fun u => hGfib _ _ (hs (ℓ u))
  have hwc : Continuous w := by
    rw [hℓquot.continuous_iff]
    have : w ∘ ℓ = G := funext hwℓ
    rw [this]; exact hGc
  refine ⟨w, hwc, ?_, ?_, ?_, ?_⟩
  · intro U hU
    have : w '' U = G '' (ℓ ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨u, rfl⟩ := hsurj y
        exact ⟨u, hy, (hwℓ u).symm⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨ℓ u, hu, hwℓ u⟩
    rw [this]
    exact hGopen _ (hU.preimage ℓ.continuous)
  · intro y y' h
    obtain ⟨u, rfl⟩ := hsurj y
    obtain ⟨u', rfl⟩ := hsurj y'
    rw [hwℓ, hwℓ] at h
    exact hGinj u u' h
  · have hrange : range w = range G := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨u, rfl⟩ := hsurj y
        exact ⟨u, (hwℓ u).symm⟩
      · rintro ⟨u, rfl⟩
        exact ⟨ℓ u, hwℓ u⟩
    rw [hrange]
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      have hn : ‖G u‖ = Real.exp (u.1.re / 2) := by
        show ‖Complex.exp (u.1 / 2)‖ = _
        rw [Complex.norm_exp]; simp
      refine ⟨by rw [hn]; exact Real.exp_pos _, ?_⟩
      rw [hn, Real.lt_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
      calc Real.exp ((2 : ℕ) * (u.1.re / 2)) = Real.exp u.1.re := by congr 1; push_cast; ring
        _ < Real.exp (Real.log r) := Real.exp_lt_exp.mpr u.2
        _ = r := Real.exp_log hr
    · rintro ⟨hz0, hz1⟩
      have hz : z ≠ 0 := norm_pos_iff.mp hz0
      rw [Real.lt_sqrt hz0.le] at hz1
      have hre : (2 * Complex.log z).re < Real.log r := by
        have h2 : (2 * Complex.log z).re = 2 * (Complex.log z).re := by simp
        rw [h2, Complex.log_re]
        have : Real.log (‖z‖ ^ 2) < Real.log r := Real.log_lt_log (by positivity) hz1
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      refine ⟨⟨2 * Complex.log z, hre⟩, ?_⟩
      show Complex.exp (2 * Complex.log z / 2) = z
      rw [mul_div_cancel_left₀ _ (two_ne_zero), Complex.exp_log hz]
  · intro y
    obtain ⟨u, rfl⟩ := hsurj y
    rw [hwℓ, hℓq]
    show Complex.exp (u.1 / 2) ^ 2 = Complex.exp u.1
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

end LiZhongQC
