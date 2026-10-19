import LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Group-theoretic pieces of `s83sg_geometric_system` (R83, S27; 下属1)

* `s83sg_sg_pow` [G2]: powers of the two generators of one handle of `surfaceGroup g` never coincide (characters).
* `s83sg_group_package` [G1]: a surjection `Θ : Γ₀ → surfaceGroup g` with kernel `±1` gives a standard system of
  generators of `Γ₀` modulo `±1`, with the surface relation up to sign and a non-commuting last pair (a map to `S₃`).
-/

open Complex Set

noncomputable section
namespace LiZhongQC

/-- **[G2]** powers of the two generators of one handle never coincide. -/
theorem s83sg_sg_pow (g : ℕ) (i : Fin g) (m n : ℤ)
    (h : (PresentedGroup.of (Sum.inl i : Fin g ⊕ Fin g) : surfaceGroup g) ^ m =
      (PresentedGroup.of (Sum.inr i : Fin g ⊕ Fin g) : surfaceGroup g) ^ n) : m = 0 ∧ n = 0 := by
  classical
  have hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inr i := Sum.inl_ne_inr
  have key : ∀ s : Fin g ⊕ Fin g, ∃ χ : Additive (surfaceGroup g) →+ ℂ,
      χ (Additive.ofMul (PresentedGroup.of s : surfaceGroup g)) = 1 ∧
      ∀ t, t ≠ s → χ (Additive.ofMul (PresentedGroup.of t : surfaceGroup g)) = 0 := by
    intro s
    obtain ⟨χ, hχ⟩ := (k22rr_sg_character_eval_bijective g).2 (fun t => if t = s then (1 : ℂ) else 0)
    exact ⟨χ, by simpa using congrFun hχ s, fun t ht => by simpa [ht] using congrFun hχ t⟩
  have hev : ∀ χ : Additive (surfaceGroup g) →+ ℂ,
      m • χ (Additive.ofMul (PresentedGroup.of (Sum.inl i) : surfaceGroup g)) =
        n • χ (Additive.ofMul (PresentedGroup.of (Sum.inr i) : surfaceGroup g)) := by
    intro χ
    have h1 := congrArg χ.toMultiplicativeRight h
    have ha : χ.toMultiplicativeRight ((PresentedGroup.of (Sum.inl i) : surfaceGroup g) ^ m) =
        (χ.toMultiplicativeRight (PresentedGroup.of (Sum.inl i) : surfaceGroup g)) ^ m := map_zpow _ _ _
    have hb : χ.toMultiplicativeRight ((PresentedGroup.of (Sum.inr i) : surfaceGroup g) ^ n) =
        (χ.toMultiplicativeRight (PresentedGroup.of (Sum.inr i) : surfaceGroup g)) ^ n := map_zpow _ _ _
    rw [ha, hb] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_zpow, toAdd_zpow] at h2
    exact h2
  obtain ⟨χa, ha1, ha0⟩ := key (Sum.inl i)
  obtain ⟨χb, hb1, hb0⟩ := key (Sum.inr i)
  have e1 := hev χa
  rw [ha1, ha0 _ hne.symm] at e1
  have e2 := hev χb
  rw [hb1, hb0 _ hne] at e2
  have e1' : (m : ℂ) = 0 := by simpa using e1
  have e2' : (n : ℂ) = 0 := by simpa using e2.symm
  exact ⟨by exact_mod_cast e1', by exact_mod_cast e2'⟩

/-- **[G1]** the group-theoretic package: from a surjection `Θ : Γ₀ → π₁` with kernel `±1`, a standard system
(`first`, `γg`, `δg`), non-commuting last pair, and the last pair maps to the last generators. -/
theorem s83sg_group_package {g : ℕ} (hg : 1 < g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (Θ : Γ₀ →* surfaceGroup g)
    (hΘs : Function.Surjective Θ)
    (hΘk : ∀ γ : Γ₀, Θ γ = 1 ↔ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1) :
    ∃ (first : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (γ' δ' : Γ₀),
      (∀ j, (first j).1 ∈ Γ₀ ∧ (first j).2 ∈ Γ₀) ∧
      Subgroup.closure (range (fun j => (first j).1) ∪ range (fun j => (first j).2) ∪
        {(γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ), (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ)}) ⊔
        Subgroup.zpowers (-1) = Γ₀ ⊔ Subgroup.zpowers (-1) ∧
      ((List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod *
          commutatorSL (γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
        (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod *
          commutatorSL (γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1) ∧
      (γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) * δ' ≠ δ' * γ' ∧
      Θ γ' = (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) ∧
      Θ δ' = (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
  choose ε hε using fun s : Fin (k + 2) ⊕ Fin (k + 2) => hΘs (PresentedGroup.of s)
  -- the index map `Fin (k + 2 - 1) → Fin (k + 2)` and the last index
  let ι : Fin (k + 2 - 1) → Fin (k + 2) := fun j => ⟨j.val, by omega⟩
  let lst : Fin (k + 2) := ⟨k + 2 - 1, by omega⟩
  set first : Fin (k + 2 - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun j => ((ε (Sum.inl (ι j)) : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (ε (Sum.inr (ι j)) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) with hfirst
  set γ' := ε (Sum.inl lst) with hγ'
  set δ' := ε (Sum.inr lst) with hδ'
  set s : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := range (fun j => (first j).1) ∪ range (fun j => (first j).2) ∪
    {(γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ), (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ)} with hs
  -- every chosen preimage lies in `s`
  have hεs : ∀ t, (ε t : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ s := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · by_cases hal : a < k + 2 - 1
      · exact Or.inl (Or.inl ⟨⟨a, hal⟩, rfl⟩)
      · have : (⟨a, ha⟩ : Fin (k + 2)) = lst := Fin.ext (by simp [lst]; omega)
        rw [this]
        exact Or.inr (Or.inl rfl)
    · by_cases hal : a < k + 2 - 1
      · exact Or.inl (Or.inr ⟨⟨a, hal⟩, rfl⟩)
      · have : (⟨a, ha⟩ : Fin (k + 2)) = lst := Fin.ext (by simp [lst]; omega)
        rw [this]
        exact Or.inr (Or.inr rfl)
  have hsΓ : s ⊆ Γ₀ := by
    rintro x ((⟨j, rfl⟩ | ⟨j, rfl⟩) | hx)
    · exact (ε _).2
    · exact (ε _).2
    · rcases hx with rfl | rfl
      · exact γ'.2
      · exact δ'.2
  -- `Θ` is onto from the subgroup generated by the chosen preimages
  have hT : (Subgroup.closure (range ε)).map Θ = ⊤ := by
    rw [MonoidHom.map_closure, ← range_comp]
    have : Θ ∘ ε = PresentedGroup.of := funext hε
    rw [this]
    exact PresentedGroup.closure_range_of _
  have hTs : ∀ w ∈ Subgroup.closure (range ε), (w : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Subgroup.closure s := by
    intro w hw
    have hle : Subgroup.closure (range ε) ≤ (Subgroup.closure s).comap Γ₀.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      exact Subgroup.subset_closure (hεs t)
    exact hle hw
  refine ⟨first, γ', δ', fun j => ⟨(ε _).2, (ε _).2⟩, ?_, ?_, ?_, hε _, hε _⟩
  · -- generation modulo `±1`
    refine le_antisymm (sup_le ((Subgroup.closure_le _).2 fun x hx => Subgroup.mem_sup_left (hsΓ hx))
      le_sup_right) (sup_le ?_ le_sup_right)
    intro x hx
    obtain ⟨w, hw, hwx⟩ := (hT ▸ Subgroup.mem_top (Θ ⟨x, hx⟩) : Θ ⟨x, hx⟩ ∈ (Subgroup.closure (range ε)).map Θ)
    have h1 : Θ (w⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hwx, inv_mul_cancel]
    have hx' : x = (w : Matrix.SpecialLinearGroup (Fin 2) ℝ) *
        ((w⁻¹ * ⟨x, hx⟩ : Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by simp
    rw [hx']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hTs w hw)) (Subgroup.mem_sup_right ?_)
    rcases (hΘk _).1 h1 with h2 | h2
    · rw [h2]
      exact Subgroup.one_mem _
    · rw [h2]
      exact Subgroup.mem_zpowers _
  · -- the surface relation up to sign
    set P : Γ₀ := (List.ofFn fun j : Fin (k + 2) =>
      ε (Sum.inl j) * ε (Sum.inr j) * (ε (Sum.inl j))⁻¹ * (ε (Sum.inr j))⁻¹).prod with hP
    have hΘP : Θ P = 1 := by
      rw [hP, map_list_prod, List.map_ofFn]
      have hcomp : (⇑Θ ∘ fun j : Fin (k + 2) =>
          ε (Sum.inl j) * ε (Sum.inr j) * (ε (Sum.inl j))⁻¹ * (ε (Sum.inr j))⁻¹) =
          fun j => PresentedGroup.mk _ (FreeGroup.of (Sum.inl j : Fin (k + 2) ⊕ Fin (k + 2)) *
            FreeGroup.of (Sum.inr j) * (FreeGroup.of (Sum.inl j))⁻¹ * (FreeGroup.of (Sum.inr j))⁻¹) := by
        funext j
        simp only [Function.comp_apply, map_mul, map_inv, hε]
        rfl
      rw [hcomp]
      refine Eq.trans ?_ (PresentedGroup.one_of_mem (Set.mem_singleton _))
      rw [map_list_prod, List.map_ofFn]
      try rfl
    have hPcoe : (P : Matrix.SpecialLinearGroup (Fin 2) ℝ) =
        (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod *
          commutatorSL (γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
      rw [hP, Subgroup.val_list_prod, List.map_ofFn, List.ofFn_succ', List.prod_concat]
      congr 1
    rw [← hPcoe]
    exact (hΘk P).1 hΘP
  · -- the last pair does not commute: a map to `S₃`
    intro hc
    have hc' : γ' * δ' = δ' * γ' := Subtype.ext (by simpa using hc)
    have h1 := congrArg Θ hc'
    rw [map_mul, map_mul, hγ', hδ', hε, hε] at h1
    let x : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let y : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    let f : Fin (k + 2) ⊕ Fin (k + 2) → Equiv.Perm (Fin 3) :=
      Sum.elim (fun i => if i = 0 then x else if i = lst then y else 1)
        (fun i => if i = 0 then y else if i = lst then x else 1)
    have hlst0 : lst ≠ 0 := by
      intro h0
      have := congrArg Fin.val h0
      simp [lst] at this
    have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin (k + 2) =>
        FreeGroup.of (Sum.inl i : Fin (k + 2) ⊕ Fin (k + 2)) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} : Set _),
        FreeGroup.lift f r = 1 := by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      rw [map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ', List.prod_cons, List.prod_concat]
      have hmid : (List.ofFn fun i : Fin k =>
          ((⇑(FreeGroup.lift f) ∘ fun i : Fin (k + 2) =>
            FreeGroup.of (Sum.inl i : Fin (k + 2) ⊕ Fin (k + 2)) * FreeGroup.of (Sum.inr i) *
              (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹) i.castSucc.succ)).prod = 1 := by
        apply List.prod_eq_one
        intro z hz
        rw [List.mem_ofFn] at hz
        obtain ⟨i, rfl⟩ := hz
        have h0 : (i.castSucc.succ : Fin (k + 2)) ≠ 0 := Fin.succ_ne_zero _
        have hl : (i.castSucc.succ : Fin (k + 2)) ≠ lst := by
          intro h'
          have := congrArg Fin.val h'
          simp [lst] at this
          omega
        simp [f, h0, hl]
      rw [hmid]
      have hl1 : (Fin.last k).succ = lst := Fin.ext (by simp [lst])
      simp only [Function.comp_apply, map_mul, map_inv, FreeGroup.lift_apply_of, hl1]
      simp [f, hlst0, x, y]
      decide
    have h2 := congrArg (PresentedGroup.toGroup hrel) h1
    have hfa : f (Sum.inl lst) = y := by simp [f, hlst0]
    have hfb : f (Sum.inr lst) = x := by simp [f, hlst0]
    erw [map_mul, map_mul, PresentedGroup.toGroup.of, PresentedGroup.toGroup.of] at h2
    change f (Sum.inl lst) * f (Sum.inr lst) = f (Sum.inr lst) * f (Sum.inl lst) at h2
    rw [hfa, hfb] at h2
    revert h2
    decide

end LiZhongQC
