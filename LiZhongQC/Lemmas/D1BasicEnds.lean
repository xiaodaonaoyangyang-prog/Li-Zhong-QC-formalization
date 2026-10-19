import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- R. Finite representatives of DISTINCT removed ordinary spherical orbits.
Infinity contributes only if ordinary, and is merged with an E orbit when necessary.
The lower bound comes from the three orbit-inequivalent witnesses of hE3. -/
theorem s36d1_removed_orbits (hΓ : IsFuchsian Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    (hE3 : ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      ∀ i ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ j ∈ ({e₁, e₂, e₃} : Finset ℝ), ∀ γ ∈ Γ, (γ 1 0 : ℝ) * i + γ 1 1 ≠ 0 → h36p_m γ (i : ℂ) = (j : ℂ) → i = j) :
    ∃ (k : ℕ) (a : Fin k → ExtPlane), 3 ≤ k ∧
      (∀ i, a i = extInf ∨ ∃ s ∈ E, a i = ((s : ℂ) : ExtPlane)) ∧ (∀ i, a i ∈ ordinarySet Γ) ∧
      (∀ i j γ, γ ∈ Γ → mobiusSL (slRealToComplex γ) (a i) = a j → i = j) ∧
      (∀ p : ExtPlane, p ∈ ordinarySet Γ →
      (p = extInf ∨ ∃ s ∈ E, p = ((s : ℂ) : ExtPlane)) →
      ∃ i, ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) (a i)) := by
  classical
  -- Finite orbit selection and the hE3 bound need no discreteness; retain hΓ.
  have _ := hΓ
  let B : Finset ExtPlane :=
    (insert extInf (E.image (fun s : ℝ => ((s : ℂ) : ExtPlane)))).filter
      (fun p => p ∈ ordinarySet Γ)
  have hB : ∀ p : ExtPlane, p ∈ B ↔
      (p = extInf ∨ ∃ s ∈ E, p = ((s : ℂ) : ExtPlane)) ∧ p ∈ ordinarySet Γ := by
    intro p
    constructor
    · intro hp
      obtain ⟨hs, ho⟩ := Finset.mem_filter.mp hp
      refine ⟨?_, ho⟩
      rcases Finset.mem_insert.mp hs with hinf | hs
      · exact Or.inl hinf
      · obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hs
        exact Or.inr ⟨s, hs, heq.symm⟩
    · rintro ⟨hs, ho⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, ho⟩
      rcases hs with hinf | ⟨s, hs, heq⟩
      · exact Finset.mem_insert.mpr (Or.inl hinf)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨s, hs, heq.symm⟩))
  let R : Setoid B :=
    { r := fun p q => ∃ γ ∈ Γ, p.val = mobiusSL (slRealToComplex γ) q.val
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro p
          refine ⟨1, Γ.one_mem, ?_⟩
          rw [k24_slReal_one, k24_mobiusSL_one]
        · intro p q hpq
          obtain ⟨γ, hγ, heq⟩ := hpq
          refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
          rw [heq, k24_slReal_inv, k24_mobiusSL_inv_apply]
        · intro p q r hpq hqr
          obtain ⟨γ, hγ, hpq⟩ := hpq
          obtain ⟨δ, hδ, hqr⟩ := hqr
          refine ⟨γ * δ, Γ.mul_mem hγ hδ, ?_⟩
          rw [k24_slReal_mul, k24_mobiusSL_mul, ← hqr]
          exact hpq }
  let Q := Quotient R
  letI : Fintype Q := Fintype.ofFinite Q
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  let a : Fin (Fintype.card Q) → ExtPlane := fun i => (e i).out.val
  have haB : ∀ i, a i ∈ B := fun i => (e i).out.property
  have hseed : ∀ i, a i = extInf ∨ ∃ s ∈ E, a i = ((s : ℂ) : ExtPlane) :=
    fun i => ((hB (a i)).mp (haB i)).1
  have hord : ∀ i, a i ∈ ordinarySet Γ :=
    fun i => ((hB (a i)).mp (haB i)).2
  have hsep : ∀ i j γ, γ ∈ Γ →
      mobiusSL (slRealToComplex γ) (a i) = a j → i = j := by
    intro i j γ hγ heq
    have hr : R.r (e j).out (e i).out := ⟨γ, hγ, heq.symm⟩
    have hq : e j = e i := by
      have h := Quotient.sound hr
      simpa only [Quotient.out_eq] using h
    exact (e.injective hq).symm
  have hcomplete : ∀ p : ExtPlane, p ∈ ordinarySet Γ →
      (p = extInf ∨ ∃ s ∈ E, p = ((s : ℂ) : ExtPlane)) →
      ∃ i, ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) (a i) := by
    intro p hp hs
    let b : B := ⟨p, (hB p).mpr ⟨hs, hp⟩⟩
    let q : Q := Quotient.mk R b
    let i : Fin (Fintype.card Q) := e.symm q
    have hq : Quotient.mk R b = Quotient.mk R (e i).out := by
      rw [Quotient.out_eq]
      exact (e.apply_symm_apply q).symm
    have hr := Quotient.exact hq
    change ∃ γ ∈ Γ, p = mobiusSL (slRealToComplex γ) (a i) at hr
    obtain ⟨γ, hγ, heq⟩ := hr
    exact ⟨i, γ, hγ, heq⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h12, h13, h23, hthree⟩ := hE3
  have hfiniteOrd : ∀ x ∈ E, ((x : ℂ) : ExtPlane) ∈ ordinarySet Γ := by
    intro x hx
    change ((x : ℂ) : ExtPlane) ∈ extRealLine ∧
      ((x : ℂ) : ExtPlane) ∉ fuchsianLimitSet Γ
    refine ⟨Or.inl ?_, hE x hx⟩
    exact ⟨(x : ℂ), by change (x : ℂ).im = 0; exact Complex.ofReal_im x, rfl⟩
  have hfiniteB : ∀ x ∈ E, ((x : ℂ) : ExtPlane) ∈ B := by
    intro x hx
    exact (hB _).mpr ⟨Or.inr ⟨x, hx, rfl⟩, hfiniteOrd x hx⟩
  have hsphere : ∀ x ∈ ({x₁, x₂, x₃} : Finset ℝ),
      ∀ y ∈ ({x₁, x₂, x₃} : Finset ℝ), ∀ γ ∈ Γ,
      mobiusSL (slRealToComplex γ) ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) →
      x = y := by
    intro x hx y hy γ hγ heq
    have hd : (γ 1 0 : ℂ) * (x : ℂ) + γ 1 1 ≠ 0 := by
      intro hd
      have hinf : mobiusSL (slRealToComplex γ) ((x : ℂ) : ExtPlane) = extInf :=
        s36x_msl_inf γ hd
      exact OnePoint.coe_ne_infty (y : ℂ) (heq.symm.trans hinf)
    have hdR : (γ 1 0 : ℝ) * x + γ 1 1 ≠ 0 := by exact_mod_cast hd
    have hcoe : mobiusSL (slRealToComplex γ) ((x : ℂ) : ExtPlane) =
        ((h36p_m γ (x : ℂ) : ℂ) : ExtPlane) := s36x_msl_coe γ hd
    exact hthree x hx y hy γ hγ hdR (OnePoint.coe_injective (hcoe.symm.trans heq))
  let b₁ : B := ⟨((x₁ : ℂ) : ExtPlane), hfiniteB x₁ hx₁⟩
  let b₂ : B := ⟨((x₂ : ℂ) : ExtPlane), hfiniteB x₂ hx₂⟩
  let b₃ : B := ⟨((x₃ : ℂ) : ExtPlane), hfiniteB x₃ hx₃⟩
  let q₁ : Q := Quotient.mk R b₁
  let q₂ : Q := Quotient.mk R b₂
  let q₃ : Q := Quotient.mk R b₃
  have hq12 : q₁ ≠ q₂ := by
    intro heq
    obtain ⟨γ, hγ, hxy⟩ := Quotient.exact heq
    exact h12 (hsphere x₂ (by simp) x₁ (by simp) γ hγ hxy.symm).symm
  have hq13 : q₁ ≠ q₃ := by
    intro heq
    obtain ⟨γ, hγ, hxy⟩ := Quotient.exact heq
    exact h13 (hsphere x₃ (by simp) x₁ (by simp) γ hγ hxy.symm).symm
  have hq23 : q₂ ≠ q₃ := by
    intro heq
    obtain ⟨γ, hγ, hxy⟩ := Quotient.exact heq
    exact h23 (hsphere x₃ (by simp) x₂ (by simp) γ hγ hxy.symm).symm
  have hk : 3 ≤ Fintype.card Q := by
    calc
      3 = ({q₁, q₂, q₃} : Finset Q).card := by simp [hq12, hq13, hq23]
      _ ≤ Fintype.card Q := Finset.card_le_univ _
  exact ⟨Fintype.card Q, a, hk, hseed, hord, hsep, hcomplete⟩

/-- G0. Explicit spherical core in the trivial-up-to-sign branch. The whole
sphere is ordinary. No F1 cusp or funnel data is consumed. -/
theorem s36d1_trivial_core (hΓ : IsFuchsian Γ)
    (hel : ∀ γ ∈ Γ, γ = 1 ∨ γ = -1) :
    ∃ L : Set ExtPlane, IsCompact L ∧ L ⊆ (fuchsianLimitSet Γ)ᶜ ∧
      ∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ →
        ∃ γ ∈ Γ, mobiusSL (slRealToComplex γ) p ∈ L := by
  have hempty : {y : ExtPlane | y ∈ closure (toExt upperHalf) ∧
      ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ mobiusSL (slRealToComplex γ) y = y} = ∅ := by
    ext y
    constructor
    · rintro ⟨hy, γ, hγ, h1, hm1, hfix⟩
      rcases hel γ hγ with he | he
      · exact (h1 he).elim
      · exact (hm1 he).elim
    · intro hy
      exact hy.elim
  have hlim : fuchsianLimitSet Γ ⊆ (∅ : Set ExtPlane) := by
    have h := h36q_limitSet_subset_closure_fix hΓ
    rw [hempty, closure_empty] at h
    exact h
  refine ⟨univ, isCompact_univ, ?_, ?_⟩
  · intro p hp
    exact fun h => hlim h
  · intro p hp
    exact ⟨1, Γ.one_mem, mem_univ _⟩

/-- E. PRODUCE exhaustive coverage by the compact core and small end tails.
Lift x using hPsurj, apply the complete spherical double-core cover, then use K's
coverage alternative or the height-above-two cusp tail formula. Ω-invariance
ensures every transferred representative is finite and in Ω. Take r=max (1/2) q. -/
theorem s36d1_exhaustive_ends {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hΓ : IsFuchsian Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ)
    {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ))))
    {P : ℂ → S} (hPsurj : P '' Ω = univ)
    (hPfib : ∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z))
    (hPloc : ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {k c : ℕ} (A : Fin c → Matrix.SpecialLinearGroup (Fin 2) ℝ) (L : Set ExtPlane)
    (hcover : ∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ → ∃ γ ∈ Γ,
      mobiusSL (slRealToComplex γ) p ∈ L ∨
      ∃ i : Fin c, ∃ τ : UpperHalfPlane, 2 < τ.im ∧
        (mobiusSL (slRealToComplex γ) p = (((A i • τ : UpperHalfPlane) : ℂ) : ExtPlane) ∨
         mobiusSL (slRealToComplex γ) p = ((conj ((A i • τ : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane)))
    (ψ : Fin k → ℂ → S) (χ : (Fin c ⊕ Fin c) → ℂ → S)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hχtail : ∀ i (τ : UpperHalfPlane), 2 < τ.im →
      (∃ w : ℂ, w ≠ 0 ∧ ‖w‖ ≤ q ∧ χ (Sum.inl i) w = P ((A i • τ : UpperHalfPlane) : ℂ)) ∧
      (∃ w : ℂ, w ≠ 0 ∧ ‖w‖ ≤ q ∧ χ (Sum.inr i) w = P (conj ((A i • τ : UpperHalfPlane) : ℂ))))
    (K : Set S) (hKcover : ∀ z ∈ Ω, (z : ExtPlane) ∈ L → P z ∈ K ∨
      ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ (1 / 2 : ℝ) ∧ ψ i w = P z) :
    ∃ r : ℝ, r < 1 ∧ (∀ x : S, x ∈ K ∨
      (∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ ψ i w = x) ∨
      ∃ j w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ χ j w = x) := by
  -- These frozen inputs are used by the chart/core producers, not by this
  -- final covering transfer once their stated conclusions have been supplied.
  have _ := hE
  have _ := hPloc
  have _ := hq0
  have hact := (s36a_omega hΓ hΩ).2.2
  have hPinv : ∀ γ ∈ Γ, ∀ z ∈ Ω, P (h36p_m γ z) = P z := by
    intro γ hγ z hz
    exact ((hPfib z hz (h36p_m γ z) (hact γ hγ z hz).2).mpr ⟨γ, hγ, rfl⟩).symm
  refine ⟨max (1 / 2 : ℝ) q, max_lt (by norm_num) hq1, ?_⟩
  intro x
  have hx : x ∈ P '' Ω := by
    rw [hPsurj]
    exact mem_univ x
  obtain ⟨z, hz, hPz⟩ := hx
  obtain ⟨γ, hγ, hγz⟩ := hcover (z : ExtPlane) ((hΩ z).mp hz).1
  let v := h36p_m γ z
  have hv : v ∈ Ω := (hact γ hγ z hz).2
  have hPv : P v = x := (hPinv γ hγ z hz).trans hPz
  have hmob : mobiusSL (slRealToComplex γ) (z : ExtPlane) = (v : ExtPlane) :=
    s36x_msl_coe γ (hact γ hγ z hz).1
  rw [hmob] at hγz
  rcases hγz with hvL | ⟨i, τ, hτ, heq⟩
  · rcases hKcover v hv hvL with hvK | ⟨j, w, hw, hrw, heq⟩
    · exact Or.inl (hPv ▸ hvK)
    · exact Or.inr (Or.inl ⟨j, w, hw,
        hrw.trans (le_max_left _ _), heq.trans hPv⟩)
  · obtain ⟨hu, hl⟩ := hχtail i τ hτ
    rcases heq with heq | heq
    · have hvτ : v = ((A i • τ : UpperHalfPlane) : ℂ) := OnePoint.coe_injective heq
      obtain ⟨w, hw, hqw, hwP⟩ := hu
      have hPτ : P ((A i • τ : UpperHalfPlane) : ℂ) = x :=
        (congrArg P hvτ).symm.trans hPv
      exact Or.inr (Or.inr ⟨Sum.inl i, w, hw,
        hqw.trans (le_max_right _ _), hwP.trans hPτ⟩)
    · have hvτ : v = conj ((A i • τ : UpperHalfPlane) : ℂ) := OnePoint.coe_injective heq
      obtain ⟨w, hw, hqw, hwP⟩ := hl
      have hPτ : P (conj ((A i • τ : UpperHalfPlane) : ℂ)) = x :=
        (congrArg P hvτ).symm.trans hPv
      exact Or.inr (Or.inr ⟨Sum.inr i, w, hw,
        hqw.trans (le_max_right _ _), hwP.trans hPτ⟩)

/-- A. Finite atlas assembly and reindexing. Reindex the disjoint sum
Fin k + (Fin c + Fin c) by Fin (k+c+c); intersect the two escape neighborhoods
and take the minimum of their positive lower bounds. Thus 3 ≤ k gives 3 ≤ n.
This is purely finite bookkeeping, with no geometric or compactness hypotheses
hidden beyond the conclusions of P, C, X, K and E. -/
theorem s36d1_assemble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {k c : ℕ}
    (ψ : Fin k → ℂ → S) (χ : (Fin c ⊕ Fin c) → ℂ → S)
    (K : Set S) (r : ℝ) (hK : IsCompact K) (hr : r < 1)
    (hψchart : ∀ i, InjOn (ψ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ψ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (ψ i '' V))
    (hψdisj : ∀ i j, i ≠ j →
      Disjoint (ψ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (ψ j '' {w | w ≠ 0 ∧ ‖w‖ < 1}))
    (hψescape : ∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i w, w ≠ 0 → ‖w‖ < 1 → ψ i w ∈ N → δ ≤ ‖w‖)
    (hχchart : ∀ i, InjOn (χ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (χ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (χ i '' V))
    (hχdisj : ∀ i j, i ≠ j →
      Disjoint (χ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (χ j '' {w | w ≠ 0 ∧ ‖w‖ < 1}))
    (hχescape : ∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i w, w ≠ 0 → ‖w‖ < 1 → χ i w ∈ N → δ ≤ ‖w‖)
    (hcross : ∀ i j, Disjoint (ψ i '' {w | w ≠ 0 ∧ ‖w‖ < 1})
      (χ j '' {w | w ≠ 0 ∧ ‖w‖ < 1}))
    (hcover : ∀ x : S, x ∈ K ∨
      (∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ ψ i w = x) ∨
      ∃ j w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ χ j w = x) :
    ∃ φ : Fin (k + c + c) → ℂ → S,
      (∀ i, InjOn (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (φ i '' V)) ∧
      (∀ i j, i ≠ j →
      Disjoint (φ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (φ j '' {w | w ≠ 0 ∧ ‖w‖ < 1})) ∧
      (∀ x : S, x ∈ K ∨ ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ φ i w = x) ∧
      (∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i w, w ≠ 0 → ‖w‖ < 1 → φ i w ∈ N → δ ≤ ‖w‖) := by
  classical
  -- Compactness and r < 1 are retained in the frozen bookkeeping contract;
  -- the atlas conclusions themselves use only the given cover and end data.
  have _ := hK
  have _ := hr
  let J := Fin k ⊕ (Fin c ⊕ Fin c)
  let e : J ≃ Fin (k + c + c) :=
    (Fintype.equivFin J).trans (finCongr (by
      change Fintype.card (Fin k ⊕ (Fin c ⊕ Fin c)) = k + c + c
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega))
  let f : J → ℂ → S := Sum.elim ψ χ
  have hfchart : ∀ i : J, InjOn (f i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (f i '' V) := by
    intro i
    rcases i with i | i
    · exact hψchart i
    · exact hχchart i
  have hfdisj : ∀ i j : J, i ≠ j →
      Disjoint (f i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (f j '' {w | w ≠ 0 ∧ ‖w‖ < 1}) := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact hψdisj i j (fun h => hij (congrArg Sum.inl h))
    · exact hcross i j
    · exact (hcross j i).symm
    · exact hχdisj i j (fun h => hij (congrArg Sum.inr h))
  have hfcover : ∀ x : S, x ∈ K ∨
      ∃ i : J, ∃ w : ℂ, w ≠ 0 ∧ ‖w‖ ≤ r ∧ f i w = x := by
    intro x
    rcases hcover x with hx | hx | hx
    · exact Or.inl hx
    · obtain ⟨i, w, hw, hrw, heq⟩ := hx
      exact Or.inr ⟨Sum.inl i, w, hw, hrw, heq⟩
    · obtain ⟨i, w, hw, hrw, heq⟩ := hx
      exact Or.inr ⟨Sum.inr i, w, hw, hrw, heq⟩
  have hfescape : ∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ),
      ∀ i : J, ∀ w, w ≠ 0 → ‖w‖ < 1 → f i w ∈ N → δ ≤ ‖w‖ := by
    intro x
    obtain ⟨N, hN, δ, hδ, hNδ⟩ := hψescape x
    obtain ⟨M, hM, ε, hε, hMε⟩ := hχescape x
    refine ⟨N ∩ M, inter_mem hN hM, min δ ε, lt_min hδ hε, ?_⟩
    intro i w hw hw1 hwNM
    rcases i with i | i
    · exact (min_le_left δ ε).trans (hNδ i w hw hw1 hwNM.1)
    · exact (min_le_right δ ε).trans (hMε i w hw hw1 hwNM.2)
  refine ⟨(fun i => f (e.symm i)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact hfchart (e.symm i)
  · intro i j hij
    exact hfdisj (e.symm i) (e.symm j) (fun heq => hij (e.symm.injective heq))
  · intro x
    rcases hfcover x with hx | ⟨i, w, hw, hrw, heq⟩
    · exact Or.inl hx
    · refine Or.inr ⟨e i, w, hw, hrw, ?_⟩
      simpa only [e.symm_apply_apply] using heq
  · intro x
    obtain ⟨N, hN, δ, hδ, hδN⟩ := hfescape x
    exact ⟨N, hN, δ, hδ, fun i w hw hw1 hwN => hδN (e.symm i) w hw hw1 hwN⟩

end LiZhongQC
