import LiZhongQC.Lemmas.FoundationQuotient

/-! F1 B4, part one: gluing of a bi-infinite arc chain, the cycle cocycle, rigidity of
translated exposed arcs, cycle indices and properness of a periodic chain. No stub imports. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- On `[k, k + 1]` the glued chain `t ↦ F ⌊t⌋ (fract t)` is the `k`-th piece. -/
theorem s36b4_glue_eq {X : Type*} (F : ℤ → ℝ → X) (hglue : ∀ k : ℤ, F k 1 = F (k + 1) 0)
    (k : ℤ) {t : ℝ} (ht : t ∈ Icc (k : ℝ) (k + 1)) :
    F ⌊t⌋ (Int.fract t) = F k (t - k) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · have hf : ⌊t⌋ = k + 1 := by
      rw [Int.floor_eq_iff, h]
      push_cast
      constructor <;> linarith
    rw [← Int.self_sub_floor, hf, h]
    have e1 : (k : ℝ) + 1 - ((k + 1 : ℤ) : ℝ) = 0 := by push_cast; ring
    have e2 : (k : ℝ) + 1 - (k : ℝ) = 1 := by ring
    rw [e1, e2, hglue k]
  · have hf : ⌊t⌋ = k := Int.floor_eq_iff.2 ⟨ht.1, h⟩
    rw [← Int.self_sub_floor, hf]

/-- A bi-infinite chain of continuous pieces with matching endpoints is continuous. -/
theorem s36b4_glue_continuous {X : Type*} [TopologicalSpace X] (F : ℤ → ℝ → X)
    (hF : ∀ k, Continuous (F k)) (hglue : ∀ k : ℤ, F k 1 = F (k + 1) 0) :
    Continuous (fun t : ℝ => F ⌊t⌋ (Int.fract t)) := by
  refine continuous_iff_continuousAt.2 fun t => continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · -- from the left: the piece `⌈t⌉ - 1`
    set k : ℤ := ⌈t⌉ - 1 with hk
    have hk1 : (k : ℝ) < t := by
      rw [hk]
      push_cast
      linarith [Int.ceil_lt_add_one t]
    have hk2 : t ≤ (k : ℝ) + 1 := by
      rw [hk]
      push_cast
      linarith [Int.le_ceil t]
    have hc : ContinuousWithinAt (fun x : ℝ => F k (x - k)) (Iic t) t :=
      ((hF k).comp (continuous_id.sub continuous_const)).continuousWithinAt
    refine hc.congr_of_eventuallyEq ?_ (s36b4_glue_eq F hglue k ⟨hk1.le, hk2⟩)
    filter_upwards [Ioc_mem_nhdsLE hk1] with x hx
    exact s36b4_glue_eq F hglue k ⟨hx.1.le, hx.2.trans hk2⟩
  · -- from the right: the piece `⌊t⌋`
    set k : ℤ := ⌊t⌋ with hk
    have hk1 : (k : ℝ) ≤ t := Int.floor_le t
    have hk2 : t < (k : ℝ) + 1 := Int.lt_floor_add_one t
    have hc : ContinuousWithinAt (fun x : ℝ => F k (x - k)) (Ici t) t :=
      ((hF k).comp (continuous_id.sub continuous_const)).continuousWithinAt
    refine hc.congr_of_eventuallyEq ?_ (s36b4_glue_eq F hglue k ⟨hk1, hk2.le⟩)
    filter_upwards [Ico_mem_nhdsGE hk2] with x hx
    exact s36b4_glue_eq F hglue k ⟨hk1.trans hx.1, hx.2.le⟩

/-- The cocycle of a periodic label sequence: `g 0 = 1`, `g (k + 1) = g k * u k`, and the
shift by one period multiplies on the left by the ordered product of one period. -/
theorem s36b4_cocycle {G : Type*} [Group G] (u : ℤ → G) (ell : ℕ)
    (hper : ∀ k : ℤ, u (k + ell) = u k) :
    ∃ g : ℤ → G, g 0 = 1 ∧ (∀ k : ℤ, g (k + 1) = g k * u k) ∧
      ∀ k : ℤ, g (k + ell) = (List.ofFn (fun j : Fin ell => u ((j : ℕ) : ℤ))).prod * g k := by
  let Pn : ℕ → G := fun m => Nat.rec (1 : G) (fun j p => p * u (j : ℤ)) m
  let Qn : ℕ → G := fun m => Nat.rec (u (-1))⁻¹ (fun j q => q * (u (-((j : ℤ) + 2)))⁻¹) m
  let g : ℤ → G := fun k => Int.rec (fun m => Pn m) (fun m => Qn m) k
  have hP : ∀ m : ℕ, Pn (m + 1) = Pn m * u (m : ℤ) := fun m => rfl
  have hQ : ∀ m : ℕ, Qn (m + 1) = Qn m * (u (-((m : ℤ) + 2)))⁻¹ := fun m => rfl
  have hgN : ∀ m : ℕ, g (m : ℤ) = Pn m := fun m => rfl
  have hgS : ∀ m : ℕ, g (Int.negSucc m) = Qn m := fun m => rfl
  have h1 : ∀ k : ℤ, g (k + 1) = g k * u k := by
    intro k
    cases k with
    | ofNat m =>
      show g ((m : ℤ) + 1) = g (m : ℤ) * u (m : ℤ)
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, hgN, hgN, hP]
    | negSucc m =>
      rw [hgS]
      cases m with
      | zero =>
        rw [show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) by rfl, hgN]
        show (1 : G) = Qn 0 * u (Int.negSucc 0)
        show (1 : G) = (u (-1))⁻¹ * u (Int.negSucc 0)
        rw [show Int.negSucc 0 = -1 by rfl, inv_mul_cancel]
      | succ j =>
        rw [show Int.negSucc (j + 1) + 1 = Int.negSucc j by
          simp only [Int.negSucc_eq]; push_cast; ring, hgS, hQ,
          show Int.negSucc (j + 1) = -((j : ℤ) + 2) by simp only [Int.negSucc_eq]; push_cast; ring,
          inv_mul_cancel_right]
  have hPell : ∀ m : ℕ, Pn m = (List.ofFn (fun j : Fin m => u ((j : ℕ) : ℤ))).prod := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [hP, ih, List.ofFn_succ', List.prod_concat]
      rfl
  refine ⟨g, rfl, h1, fun k => ?_⟩
  rw [← hPell, ← hgN]
  induction k using Int.induction_on with
  | zero => rw [zero_add]; exact (mul_one _).symm
  | succ i ih =>
    rw [show (i : ℤ) + 1 + ell = (i + ell) + 1 by ring, h1 ((i : ℤ) + ell), ih, h1 (i : ℤ), hper,
      mul_assoc]
  | pred i ih =>
    have e1 := h1 (-(i : ℤ) - 1 + ell)
    have e2 := h1 (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + ell + 1 = -(i : ℤ) + ell by ring, ih, hper] at e1
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at e2
    rw [e2, ← mul_assoc] at e1
    exact (mul_right_cancel e1).symm

/-- Rigidity of translated exposed arcs on half-open parameters: a group element carrying
one arc point to another fixes the arc, the parameter, and is `±1`. -/
theorem s36b4_arc_rigidity {n : ℕ} (a : Fin n → unitInterval → UpperHalfPlane)
    (σ : Equiv.Perm (Fin n)) (d : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ i j γ, γ ∈ Γ → ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∀ s : unitInterval, γ • a i t = a j s → i = j ∧ (γ = 1 ∨ γ = -1) ∧ t = s)
    (hdj : ∀ i, d i ∈ Γ ∧ a i 1 = d i • a (σ i) 0)
    (hend : ∀ i j γ, γ ∈ Γ → a i 1 = γ • a j 0 → j = σ i ∧ (γ = d i ∨ γ = -d i))
    (i i' : Fin n) (β : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hβ : β ∈ Γ)
    (s s' : unitInterval) (hs : (s : ℝ) < 1) (hs' : (s' : ℝ) < 1)
    (he : β • a i' s' = a i s) :
    i' = i ∧ s' = s ∧ (β = 1 ∨ β = -1) := by
  rcases eq_or_lt_of_le s'.2.1 with h0' | h0'
  · rcases eq_or_lt_of_le s.2.1 with h0 | h0
    · -- two vertices: use the incoming arc of `i`
      have hs0 : s = 0 := Subtype.ext h0.symm
      have hs0' : s' = 0 := Subtype.ext h0'.symm
      subst hs0
      subst hs0'
      set p := σ.symm i with hp
      have hσp : σ p = i := by rw [hp, Equiv.apply_symm_apply]
      obtain ⟨hdp, hap⟩ := hdj p
      have heq : a p 1 = (d p * β) • a i' 0 := by
        rw [hap, hσp, mul_smul, he]
      obtain ⟨hj, hγ⟩ := hend p i' (d p * β) (mul_mem hdp hβ) heq
      refine ⟨hj.trans hσp, rfl, ?_⟩
      rcases hγ with h | h
      · left
        exact mul_left_cancel (h.trans (mul_one _).symm)
      · right
        exact mul_left_cancel (h.trans (by rw [mul_neg, mul_one]))
    · exfalso
      have he' : β⁻¹ • a i s = a i' s' := by rw [← he, inv_smul_smul]
      obtain ⟨-, -, hss⟩ := hint i i' β⁻¹ (inv_mem hβ) s h0 hs s' he'
      have : (s : ℝ) = s' := congrArg Subtype.val hss
      linarith
  · obtain ⟨hii, hβ1, hss⟩ := hint i' i β hβ s' h0' hs' s he
    exact ⟨hii, hss, hβ1⟩

/-- Within one cycle of least length `ell`, equal positions differ by whole periods. -/
theorem s36b4_cycle_index {n : ℕ} (σ : Equiv.Perm (Fin n)) (r : Fin n) (ell : ℕ) (hell : 0 < ell)
    (hret : (σ ^ ell) r = r) (hmin : ∀ k : ℕ, 0 < k → k < ell → (σ ^ k) r ≠ r)
    (k k' : ℤ) (h : (σ ^ k) r = (σ ^ k') r) : ∃ q : ℤ, k = k' + q * ell := by
  have hellz : (0 : ℤ) < ell := by exact_mod_cast hell
  have hpow : ∀ q : ℤ, (σ ^ ((ell : ℤ) * q)) r = r := by
    intro q
    rw [zpow_mul, zpow_natCast]
    have hfix : ∀ m : ℤ, ((σ ^ ell) ^ m) r = r := by
      intro m
      induction m using Int.induction_on with
      | zero => simp
      | succ m ih => rw [zpow_add_one, Equiv.Perm.mul_apply, hret, ih]
      | pred m ih =>
        rw [zpow_sub_one, Equiv.Perm.mul_apply]
        have : ((σ ^ ell)⁻¹) r = r := by
          rw [Equiv.Perm.inv_eq_iff_eq, hret]
        rw [this, ih]
    exact hfix q
  have hm : (σ ^ (k - k')) r = r := by
    have e := congrArg (σ ^ (-k')) h
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← zpow_add, ← zpow_add, neg_add_cancel,
      zpow_zero, Equiv.Perm.one_apply] at e
    rwa [show k - k' = -k' + k by ring]
  set m := k - k' with hmdef
  have hdecomp := Int.mul_ediv_add_emod m ell
  have hj0 : 0 ≤ m % ell := Int.emod_nonneg m hellz.ne'
  have hj1 : m % ell < ell := Int.emod_lt_of_pos m hellz
  have hjr : (σ ^ (m % ell)) r = r := by
    have e : m % ell = m + (ell : ℤ) * (-(m / ell)) := by rw [mul_neg]; linarith
    rw [e, zpow_add, Equiv.Perm.mul_apply, hpow, hm]
  have hj : m % ell = 0 := by
    by_contra hne
    have hpos : 0 < (m % ell).toNat := by omega
    have hlt : (m % ell).toNat < ell := by omega
    apply hmin _ hpos hlt
    have : ((m % ell).toNat : ℤ) = m % ell := Int.toNat_of_nonneg hj0
    rw [← zpow_natCast, this, hjr]
  refine ⟨m / ell, ?_⟩
  rw [hj, add_zero] at hdecomp
  rw [mul_comm]
  linarith

/-- Iterating a periodicity `c (t + ell) = H • c t` over all integers. -/
theorem s36b4_periodic_zpow (c : ℝ → UpperHalfPlane) (ell : ℝ)
    (H : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hper : ∀ t, c (t + ell) = H • c t) :
    ∀ (q : ℤ) (t : ℝ), c (t + q * ell) = H ^ q • c t := by
  intro q
  induction q using Int.induction_on with
  | zero => intro t; simp
  | succ q ih =>
    intro t
    rw [show t + ((q : ℤ) + 1 : ℤ) * ell = (t + (q : ℤ) * ell) + ell by push_cast; ring, hper, ih,
      zpow_add_one, ← (Commute.self_zpow H (q : ℤ)).eq, mul_smul]
  | pred q ih =>
    intro t
    have e := hper (t + (-(q : ℤ) - 1 : ℤ) * ell)
    rw [show t + (-(q : ℤ) - 1 : ℤ) * ell + ell = t + (-(q : ℤ) : ℤ) * ell by push_cast; ring,
      ih] at e
    rw [zpow_sub_one, mul_smul]
    have e2 : H⁻¹ • (H ^ (-(q : ℤ)) • c t) = c (t + (-(q : ℤ) - 1 : ℤ) * ell) := by
      rw [e, inv_smul_smul]
    rw [← e2, ← mul_smul, ← mul_smul, (Commute.self_zpow H (-(q : ℤ))).inv_left.eq]

/-- A continuous chain, periodic under a group element of infinite order in a Fuchsian group,
is proper: preimages of compact sets are compact. -/
theorem s36b4_proper (hΓ : IsFuchsian Γ) (c : ℝ → UpperHalfPlane) (hc : Continuous c)
    (ell : ℝ) (hell : 0 < ell) (H : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hH : H ∈ Γ)
    (hper : ∀ t, c (t + ell) = H • c t) (hinj : Function.Injective (fun q : ℤ => H ^ q))
    (L : Set UpperHalfPlane) (hL : IsCompact L) : IsCompact (c ⁻¹' L) := by
  have hK0 : IsCompact (c '' Icc 0 ell) := isCompact_Icc.image hc
  set K := c '' Icc 0 ell ∪ L with hK
  have hS := hΓ K (hK0.union hL)
  have hQ : {q : ℤ | H ^ q ∈ {γ ∈ Γ | ((γ • ·) '' K ∩ K).Nonempty}}.Finite :=
    hS.preimage hinj.injOn
  obtain ⟨M, hM⟩ := hQ.bddAbove
  obtain ⟨M', hM'⟩ := hQ.bddBelow
  have hzp := s36b4_periodic_zpow c ell H hper
  refine Metric.isCompact_of_isClosed_isBounded (hL.isClosed.preimage hc) ?_
  refine (Metric.isBounded_Icc ((M' : ℝ) * ell) ((M : ℝ) * ell + ell)).subset ?_
  intro t ht
  set q : ℤ := ⌊t / ell⌋ with hq
  set t₀ : ℝ := t - q * ell with ht₀
  have h0 : 0 ≤ t₀ := by
    have := Int.floor_le (t / ell)
    rw [ht₀, hq]
    have := (le_div_iff₀ hell).1 this
    linarith
  have h1 : t₀ < ell := by
    have := Int.lt_floor_add_one (t / ell)
    rw [ht₀, hq]
    have := (div_lt_iff₀ hell).1 this
    rw [add_mul, one_mul] at this
    linarith
  have hct : c t = H ^ q • c t₀ := by
    rw [← hzp q t₀, ht₀, sub_add_cancel]
  have hqQ : q ∈ {q : ℤ | H ^ q ∈ {γ ∈ Γ | ((γ • ·) '' K ∩ K).Nonempty}} :=
    ⟨zpow_mem hH q, ⟨c t, ⟨c t₀, Or.inl ⟨t₀, ⟨h0, h1.le⟩, rfl⟩, hct.symm⟩, Or.inr ht⟩⟩
  have hqM : (q : ℝ) ≤ M := by exact_mod_cast hM hqQ
  have hqM' : (M' : ℝ) ≤ q := by exact_mod_cast hM' hqQ
  have htq : t = t₀ + q * ell := by rw [ht₀]; ring
  have hb1 := mul_le_mul_of_nonneg_right hqM' hell.le
  have hb2 := mul_le_mul_of_nonneg_right hqM hell.le
  constructor
  · rw [htq]
    linarith
  · rw [htq]
    linarith

/-- The lift of one least cycle of the transition permutation: a continuous chain of translated
exposed arcs in the frontier, periodic under the ordered first-return product, rigid under the
group up to whole periods, and containing every arc of the cycle. -/
theorem s36b4_cycle_path {U : Set UpperHalfPlane}
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    {n : ℕ} (a : Fin n → unitInterval → UpperHalfPlane)
    (σ : Equiv.Perm (Fin n)) (d : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hemb : ∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ frontier U)
    (hint : ∀ i j γ, γ ∈ Γ → ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∀ s : unitInterval, γ • a i t = a j s → i = j ∧ (γ = 1 ∨ γ = -1) ∧ t = s)
    (hdj : ∀ i, d i ∈ Γ ∧ a i 1 = d i • a (σ i) 0)
    (hend : ∀ i j γ, γ ∈ Γ → a i 1 = γ • a j 0 → j = σ i ∧ (γ = d i ∨ γ = -d i))
    (r : Fin n) (ell : ℕ) (hell : 0 < ell) (hret : (σ ^ ell) r = r)
    (hmin : ∀ k : ℕ, 0 < k → k < ell → (σ ^ k) r ≠ r) :
    ∃ (H : Matrix.SpecialLinearGroup (Fin 2) ℝ) (c : ℝ → UpperHalfPlane),
      H = (List.ofFn (fun k : Fin ell => d ((σ ^ (k : ℕ)) r))).prod ∧
      Continuous c ∧ (∀ t, c t ∈ frontier U) ∧ H ∈ Γ ∧ (∀ t, c (t + ell) = H • c t) ∧
      (∀ γ ∈ Γ, ∀ t t' : ℝ, γ • c t' = c t →
        ∃ q : ℤ, t = t' + q * ell ∧ (γ = H ^ q ∨ γ = -H ^ q)) ∧
      (∀ p : ℕ, p < ell → ∀ s : unitInterval, ∃ γ ∈ Γ, a ((σ ^ p) r) s = γ • c (p + s)) ∧
      (∀ t, ∃ k : ℤ, ∃ g ∈ Γ, ∃ s : unitInterval, (s : ℝ) < 1 ∧ c t = g • a ((σ ^ k) r) s) := by
  classical
  set H := (List.ofFn (fun k : Fin ell => d ((σ ^ (k : ℕ)) r))).prod with hHdef
  let idx : ℤ → Fin n := fun k => (σ ^ k) r
  have hidx1 : ∀ k : ℤ, idx (k + 1) = σ (idx k) := fun k => by
    show (σ ^ (k + 1)) r = σ ((σ ^ k) r)
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
  have hidxp : ∀ k : ℤ, idx (k + ell) = idx k := fun k => by
    show (σ ^ (k + (ell : ℤ))) r = (σ ^ k) r
    rw [zpow_add, zpow_natCast, Equiv.Perm.mul_apply, hret]
  obtain ⟨g, hg0, hg1, hgell⟩ := s36b4_cocycle (fun k => d (idx k)) ell (fun k => by
    show d (idx (k + ell)) = d (idx k)
    rw [hidxp])
  beta_reduce at hg1 hgell
  have hHeq : (List.ofFn (fun j : Fin ell => d (idx ((j : ℕ) : ℤ)))).prod = H := by
    rw [hHdef]
    congr 1
  simp only [hHeq] at hgell
  have hgΓ : ∀ k, g k ∈ Γ := by
    intro k
    induction k using Int.induction_on with
    | zero => rw [hg0]; exact one_mem Γ
    | succ i ih => rw [hg1]; exact mul_mem ih (hdj _).1
    | pred i ih =>
      have e := hg1 (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at e
      have e2 : g (-(i : ℤ) - 1) = g (-(i : ℤ)) * (d (idx (-(i : ℤ) - 1)))⁻¹ := by
        rw [e, mul_inv_cancel_right]
      rw [e2]
      exact mul_mem ih (inv_mem (hdj _).1)
  have hHΓ : H ∈ Γ := by
    have e := hgell 0
    rw [zero_add, hg0, mul_one] at e
    rw [← e]
    exact hgΓ _
  have hgq : ∀ (q : ℤ) (k : ℤ), g (k + q * ell) = H ^ q * g k := by
    intro q
    induction q using Int.induction_on with
    | zero => intro k; simp
    | succ q ih =>
      intro k
      rw [show k + ((q : ℤ) + 1) * ell = (k + (q : ℤ) * ell) + ell by ring, hgell, ih, zpow_add_one,
        ← mul_assoc, ← (Commute.self_zpow H (q : ℤ)).eq]
    | pred q ih =>
      intro k
      have e := hgell (k + (-(q : ℤ) - 1) * ell)
      rw [show k + (-(q : ℤ) - 1) * ell + ell = k + (-(q : ℤ)) * ell by ring, ih] at e
      rw [zpow_sub_one, ← (Commute.self_zpow H (-(q : ℤ))).inv_left.eq, mul_assoc, e,
        inv_mul_cancel_left]
  let F : ℤ → ℝ → UpperHalfPlane := fun k s => g k • a (idx k) (Set.projIcc 0 1 zero_le_one s)
  have hp0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp [Set.projIcc])
  have hp1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := Subtype.ext (by simp [Set.projIcc])
  have hglue : ∀ k : ℤ, F k 1 = F (k + 1) 0 := by
    intro k
    show g k • a (idx k) (Set.projIcc 0 1 zero_le_one 1) =
      g (k + 1) • a (idx (k + 1)) (Set.projIcc 0 1 zero_le_one 0)
    rw [hp0, hp1, (hdj (idx k)).2, hg1, hidx1, mul_smul]
  have hFc : ∀ k, Continuous (F k) := fun k =>
    (continuous_const_smul (g k)).comp (((hemb (idx k)).1.continuous).comp continuous_projIcc)
  set c : ℝ → UpperHalfPlane := fun t => F ⌊t⌋ (Int.fract t) with hcdef
  have hcc : Continuous c := s36b4_glue_continuous F hFc hglue
  have hfrI : ∀ γ ∈ Γ, ∀ x ∈ frontier U, γ • x ∈ frontier U := by
    intro γ hγ x hx
    have h1 : (fun τ : UpperHalfPlane => γ • τ) '' frontier U = frontier U := by
      calc
        (fun τ : UpperHalfPlane => γ • τ) '' frontier U =
            frontier ((fun τ : UpperHalfPlane => γ • τ) '' U) :=
          (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_frontier U
        _ = frontier U := by rw [hUi γ hγ]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  have hval : ∀ t, c t = g ⌊t⌋ • a (idx ⌊t⌋) (Set.projIcc 0 1 zero_le_one (Int.fract t)) :=
    fun t => rfl
  have hpf : ∀ t, ((Set.projIcc (0 : ℝ) 1 zero_le_one (Int.fract t) : unitInterval) : ℝ) =
      Int.fract t := fun t => by
    rw [Set.projIcc_of_mem _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩]
  have hcF : ∀ t, c t ∈ frontier U := fun t =>
    hfrI _ (hgΓ _) _ ((hemb _).2 ⟨_, rfl⟩)
  have hcper : ∀ t, c (t + ell) = H • c t := by
    intro t
    rw [hval, hval, Int.floor_add_natCast, Int.fract_add_natCast, hidxp, hgell, mul_smul]
  have hrig : ∀ γ ∈ Γ, ∀ t t' : ℝ, γ • c t' = c t →
      ∃ q : ℤ, t = t' + q * ell ∧ (γ = H ^ q ∨ γ = -H ^ q) := by
    intro γ hγ t t' he
    set k := ⌊t⌋ with hk
    set k' := ⌊t'⌋ with hk'
    set s := Set.projIcc (0 : ℝ) 1 zero_le_one (Int.fract t) with hs
    set s' := Set.projIcc (0 : ℝ) 1 zero_le_one (Int.fract t') with hs'
    have hs1 : (s : ℝ) < 1 := by rw [hs, hpf]; exact Int.fract_lt_one t
    have hs1' : (s' : ℝ) < 1 := by rw [hs', hpf]; exact Int.fract_lt_one t'
    have hβ : (g k)⁻¹ * γ * g k' ∈ Γ := mul_mem (mul_mem (inv_mem (hgΓ k)) hγ) (hgΓ k')
    have he' : γ • (g k' • a (idx k') s') = g k • a (idx k) s := he
    have heq : ((g k)⁻¹ * γ * g k') • a (idx k') s' = a (idx k) s := by
      rw [mul_smul, mul_smul, he', inv_smul_smul]
    obtain ⟨hii, hss, hβ1⟩ :=
      s36b4_arc_rigidity a σ d hint hdj hend (idx k) (idx k') _ hβ s s' hs1 hs1' heq
    obtain ⟨q, hq⟩ := s36b4_cycle_index σ r ell hell hret hmin k k' hii.symm
    have hfr : Int.fract t' = Int.fract t := by
      have e := congrArg Subtype.val hss
      rw [hs, hs', hpf, hpf] at e
      exact e
    refine ⟨q, ?_, ?_⟩
    · have h1 := Int.floor_add_fract t
      have h2 := Int.floor_add_fract t'
      have hkq : (k : ℝ) = k' + q * ell := by exact_mod_cast hq
      rw [← hk] at h1
      rw [← hk'] at h2
      linarith
    · have hgk : g k = H ^ q * g k' := by rw [hq, hgq]
      rcases hβ1 with h | h
      · left
        have e1 : γ * g k' = H ^ q * g k' := by
          calc γ * g k' = g k * ((g k)⁻¹ * γ * g k') := by group
            _ = H ^ q * g k' := by rw [h, mul_one, hgk]
        exact mul_right_cancel e1
      · right
        have e1 : γ * g k' = -H ^ q * g k' := by
          calc γ * g k' = g k * ((g k)⁻¹ * γ * g k') := by group
            _ = -(H ^ q * g k') := by rw [h, mul_neg, mul_one, hgk]
            _ = -H ^ q * g k' := (neg_mul _ _).symm
        exact mul_right_cancel e1
  have harc : ∀ p : ℕ, p < ell → ∀ s : unitInterval,
      ∃ γ ∈ Γ, a ((σ ^ p) r) s = γ • c (p + s) := by
    intro p _ s
    refine ⟨(g p)⁻¹, inv_mem (hgΓ p), ?_⟩
    have hmem : (p : ℝ) + s ∈ Icc (((p : ℤ) : ℝ)) (((p : ℤ) : ℝ) + 1) := by
      push_cast
      exact ⟨by linarith [s.2.1], by linarith [s.2.2]⟩
    have e := s36b4_glue_eq F hglue (p : ℤ) hmem
    have e2 : c ((p : ℝ) + s) = g p • a ((σ ^ p) r) s := by
      show F ⌊(p : ℝ) + s⌋ (Int.fract ((p : ℝ) + s)) = _
      rw [e]
      show g p • a (idx p) (Set.projIcc 0 1 zero_le_one ((p : ℝ) + s - (((p : ℤ) : ℝ)))) = _
      rw [show (p : ℝ) + s - (((p : ℤ) : ℝ)) = s by push_cast; ring, Set.projIcc_val]
      show g p • a ((σ ^ ((p : ℕ) : ℤ)) r) s = _
      rw [zpow_natCast]
    rw [e2, inv_smul_smul]
  have hrep : ∀ t, ∃ k : ℤ, ∃ g' ∈ Γ, ∃ s : unitInterval, (s : ℝ) < 1 ∧
      c t = g' • a ((σ ^ k) r) s :=
    fun t => ⟨⌊t⌋, g ⌊t⌋, hgΓ _, _, by rw [hpf]; exact Int.fract_lt_one t, rfl⟩
  exact ⟨H, c, rfl, hcc, hcF, hHΓ, hcper, hrig, harc, hrep⟩

end LiZhongQC
