import Mathlib

/-!
# Selberg's lemma for `SL(n, R)` (R83 S36, piece G1c helper, 下属1)

A finitely generated subgroup of `SL(n, R)`, `R` a commutative domain of characteristic `0`, has a torsion-free
subgroup of finite index. Route (Alperin, *An elementary account of Selberg's lemma*):
the entries of the generators span a finitely generated `ℤ`-subalgebra `A ⊆ R` (Noetherian, Jacobson, a domain of
characteristic `0`); two maximal ideals `m₁, m₂` with finite residue fields and coprime residue characteristics give
the congruence subgroup `Γ' = ker (Γ → SL(n, A/m₁)) ⊓ ker (Γ → SL(n, A/m₂))` of finite index; an element `1 + X` of
prime order `r` with `X ≡ 0 mod m` and `r ∉ m` is trivial (Krull intersection theorem, `m^{k+1}` is `m`-primary).
-/

open Matrix

noncomputable section

namespace LiZhongQC

/-- `ℤ` is a Jacobson ring: its nonzero primes are maximal, and `⊥` is the intersection of the ideals `(p)`. -/
theorem sel_int_jacobson : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_sInf_maximal]
  intro I hI
  by_cases h0 : I = ⊥
  · refine ⟨{J | J.IsMaximal}, fun J hJ => Or.inl hJ, ?_⟩
    subst h0
    refine le_antisymm bot_le fun x hx => ?_
    rw [Ideal.mem_sInf] at hx
    rw [Ideal.mem_bot]
    by_contra hne
    obtain ⟨p, hpx, hp⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hprime : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (Nat.cast_ne_zero.2 hp.ne_zero)).2 hpZ
    have hspan : (Ideal.span {(p : ℤ)}).IsMaximal :=
      IsPrime.to_maximal_ideal (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)
    have hxp := hx hspan
    rw [Ideal.mem_span_singleton] at hxp
    have h1 : p ∣ x.natAbs := Int.ofNat_dvd_left.1 hxp
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
    omega
  · have := hI
    exact ⟨{I}, by simpa using Or.inl (IsPrime.to_maximal_ideal h0), by simp⟩

/-- The residue field of a finitely generated `ℤ`-algebra at a maximal ideal is finite (Zariski's lemma over the
Jacobson ring `ℤ`). -/
theorem sel_finite_quotient {A : Type*} [CommRing A] [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] :
    Finite (A ⧸ m) := by
  have := sel_int_jacobson
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType ℤ (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ m) (Ideal.Quotient.mkₐ_surjective ℤ m)
  have : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  have hchar : ringChar (A ⧸ m) ≠ 0 := by
    intro h0
    have : CharP (A ⧸ m) 0 := ringChar.eq_iff.1 h0
    have : CharZero (A ⧸ m) := CharP.charP_to_charZero (A ⧸ m)
    exact Int.not_isField (isField_of_isIntegral_of_isField (algebraMap ℤ (A ⧸ m)).injective_int
      (Field.toIsField (A ⧸ m)))
  have : NeZero (ringChar (A ⧸ m)) := ⟨hchar⟩
  let : Algebra (ZMod (ringChar (A ⧸ m))) (A ⧸ m) := ZMod.algebra (A ⧸ m) (ringChar (A ⧸ m))
  have : Module.Finite (ZMod (ringChar (A ⧸ m))) (A ⧸ m) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod (ringChar (A ⧸ m))) (A ⧸ m)
  exact Module.finite_of_finite (ZMod (ringChar (A ⧸ m)))

/-- A finitely generated `ℤ`-algebra which is a domain of characteristic `0` has two maximal ideals such that no
prime number lies in both. -/
theorem sel_two_maximal {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
    ∃ m₁ m₂ : Ideal A, m₁.IsMaximal ∧ m₂.IsMaximal ∧ ∀ r : ℕ, r.Prime → (r : A) ∈ m₁ → (r : A) ∉ m₂ := by
  have := sel_int_jacobson
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal A
  let : Field (A ⧸ m₁) := Ideal.Quotient.field m₁
  have := sel_finite_quotient m₁
  obtain ⟨q, hq⟩ : ∃ q, ringChar (A ⧸ m₁) = q := ⟨_, rfl⟩
  have : CharP (A ⧸ m₁) q := hq ▸ ringChar.charP (A ⧸ m₁)
  have hq0 : q ≠ 0 := CharP.char_ne_zero_of_finite (A ⧸ m₁) q
  have hq1 : q ≠ 1 := hq ▸ CharP.ringChar_ne_one
  have hqA : ((q : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have : IsDomain (Localization.Away ((q : ℕ) : A)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hqA)
  obtain ⟨N, hN⟩ := Ideal.exists_maximal (Localization.Away ((q : ℕ) : A))
  have hN' := (IsLocalization.isMaximal_iff_isMaximal_disjoint
    (Localization.Away ((q : ℕ) : A)) (y := ((q : ℕ) : A)) N).1 hN
  refine ⟨m₁, N.under A, hm₁, hN'.1, fun r hr hr1 hr2 => hN'.2 ?_⟩
  have hcast : ((r : ℕ) : A ⧸ m₁) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m₁)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hr1
  have hdvd : q ∣ r := (CharP.cast_eq_zero_iff (A ⧸ m₁) q r).1 hcast
  rcases (Nat.dvd_prime hr).1 hdvd with h | h
  · exact absurd h hq1
  · subst h
    exact hr2

/-- Congruence kernels have no torsion prime to the residue characteristic: if `X ≡ 0 mod m` (`m` maximal in a
Noetherian domain), `(r : A) ∉ m` and `(1 + X)^r = 1`, then `X = 0`. -/
theorem sel_congr_torsion {A : Type*} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    {n : Type*} [Fintype n] [DecidableEq n] (m : Ideal A) [m.IsMaximal] {X : Matrix n n A}
    (hX : ∀ i j, X i j ∈ m) {r : ℕ} (hr : (r : A) ∉ m) (hpow : (1 + X) ^ r = 1) : X = 0 := by
  have hm_ne : m ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    rcases r with _ | s
    · exact absurd (by simp) hr
    · exact ⟨s, rfl⟩
  -- `m^{k+1}` is `m`-primary, and `r ∉ m`
  have hprim : ∀ k : ℕ, ∀ x : A, ((s + 1 : ℕ) : A) * x ∈ m ^ (k + 1) → x ∈ m ^ (k + 1) := by
    intro k x hx
    have hrad : (m ^ (k + 1)).radical = m := by
      rw [Ideal.radical_pow m (Nat.succ_ne_zero k), (‹m.IsMaximal›).isPrime.radical]
    have hP : (m ^ (k + 1)).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; infer_instance)
    rcases (Ideal.isPrimary_iff.1 hP).2 (by rwa [mul_comm] at hx) with h | h
    · exact h
    · exact absurd (hrad ▸ h) hr
  -- the binomial expansion of `(1 + X)^{s+1} = 1`, entrywise
  have hexp : ∀ a b, (∑ l ∈ Finset.range (s + 1 + 1), ((s + 1).choose l : A) * (X ^ l) a b) =
      (1 : Matrix n n A) a b := by
    intro a b
    have h := (Commute.one_right X).add_pow (s + 1)
    rw [add_comm X 1, hpow] at h
    have h2 := congrFun (congrFun h a) b
    rw [h2, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
  have hsplit : ∀ a b, ((s + 1 : ℕ) : A) * X a b +
      ∑ l ∈ Finset.range s, ((s + 1).choose (l + 1 + 1) : A) * (X ^ (l + 1 + 1)) a b = 0 := by
    intro a b
    have h := hexp a b
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
      one_mul] at h
    linear_combination h
  -- entries of products
  have hmul : ∀ (I J : Ideal A) (Y Z : Matrix n n A), (∀ a b, Y a b ∈ I) → (∀ a b, Z a b ∈ J) →
      ∀ a b, (Y * Z) a b ∈ I * J := by
    intro I J Y Z hY hZ a b
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (hY a l) (hZ l b)
  -- `X ≡ 0 mod m^{k+1}` for all `k`
  have hclaim : ∀ k : ℕ, ∀ a b, X a b ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro a b; simpa using hX a b
    | succ k ih =>
      have hpw : ∀ l : ℕ, ∀ a b, (X ^ (l + 1)) a b ∈ m ^ ((l + 1) * (k + 1)) := by
        intro l
        induction l with
        | zero => intro a b; simpa using ih a b
        | succ l ihl =>
          intro a b
          have h := hmul _ _ _ _ ihl ih a b
          rw [← pow_add] at h
          rw [pow_succ]
          convert h using 2
          ring
      intro a b
      apply hprim (k + 1)
      have hmem : ∑ l ∈ Finset.range s, ((s + 1).choose (l + 1 + 1) : A) * (X ^ (l + 1 + 1)) a b ∈
          m ^ (k + 1 + 1) := by
        refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
        refine Ideal.pow_le_pow_right ?_ (hpw (l + 1) a b)
        nlinarith
      have heq : ((s + 1 : ℕ) : A) * X a b =
          -∑ l ∈ Finset.range s, ((s + 1).choose (l + 1 + 1) : A) * (X ^ (l + 1 + 1)) a b := by
        linear_combination hsplit a b
      rw [heq]
      exact neg_mem hmem
  -- Krull's intersection theorem
  have hK := Ideal.iInf_pow_eq_bot_of_isDomain m hm_ne
  ext a b
  have hmem : X a b ∈ ⨅ i : ℕ, m ^ i := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · exact hclaim i a b
  rw [hK, Ideal.mem_bot] at hmem
  simpa using hmem

/-- Schreier: a subgroup of finite index in a finitely generated subgroup is finitely generated. -/
theorem sel_fg_of_relIndex {G : Type*} [Group G] {H K : Subgroup G} (hK : K.FG) (hHK : H ≤ K)
    (hi : H.relIndex K ≠ 0) : H.FG := by
  have : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
  have : (H.subgroupOf K).FiniteIndex := ⟨hi⟩
  have : Group.FG (H.subgroupOf K) := inferInstance
  have hH : Group.FG H := Group.fg_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hHK).surjective
  exact (Group.fg_iff_subgroup_fg H).1 hH

/-- **Selberg's lemma** for `SL(n, R)`, `R` a commutative domain of characteristic `0`. -/
theorem sel_selberg_generic {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {n : Type*} [Fintype n] [DecidableEq n] {Γ : Subgroup (Matrix.SpecialLinearGroup n R)} (hfg : Γ.FG) :
    ∃ Γ' : Subgroup (Matrix.SpecialLinearGroup n R), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧ Γ'.FG ∧
      ∀ g ∈ Γ', IsOfFinOrder g → g = 1 := by
  classical
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff Γ).1 hfg
  -- the `ℤ`-algebra generated by the entries of the generators
  set T : Finset R := hSfin.toFinset.biUnion fun s => Finset.univ.image fun p : n × n => (s : Matrix n n R) p.1 p.2 with hT
  set A : Subalgebra ℤ R := Algebra.adjoin ℤ (T : Set R) with hA
  have hFT : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset T)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : CharZero A := ⟨fun a b h => by
    have := congrArg (fun x : A => (x : R)) h
    simpa using this⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, hm₁₂⟩ := sel_two_maximal (A := A)
  have := hm₁
  have := hm₂
  have := sel_finite_quotient m₁
  have := sel_finite_quotient m₂
  -- the inclusion `SL(n, A) → SL(n, R)`
  set ι := Matrix.SpecialLinearGroup.map (n := n) (A.val : A →+* R) with hι
  have hιinj : Function.Injective ι := by
    intro g h hgh
    ext a b
    have := congrArg (fun x : Matrix.SpecialLinearGroup n R => (x : Matrix n n R) a b) hgh
    exact this
  have hΓ : Γ ≤ ι.range := by
    rw [← hS, Subgroup.closure_le]
    intro s hs
    have hent : ∀ a b, (s : Matrix n n R) a b ∈ A := fun a b => Algebra.subset_adjoin
      (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨s, hSfin.mem_toFinset.2 hs,
        Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩⟩))
    let M : Matrix n n A := fun a b => ⟨(s : Matrix n n R) a b, hent a b⟩
    have hM : M.det = 1 := by
      apply Subtype.val_injective
      have h1 := RingHom.map_det (A.val : A →+* R) M
      have h2 : (A.val : A →+* R).mapMatrix M = (s : Matrix n n R) := by
        ext a b
        rfl
      rw [h2, s.2] at h1
      simpa using h1
    refine ⟨⟨M, hM⟩, ?_⟩
    ext a b
    rfl
  -- the congruence subgroup
  set π₁ := Matrix.SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk m₁) with hπ₁
  set π₂ := Matrix.SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk m₂) with hπ₂
  set ΓA := Γ.comap ι with hΓA
  set K := π₁.ker ⊓ π₂.ker with hK
  have : π₁.ker.FiniteIndex := Subgroup.finiteIndex_ker π₁
  have : π₂.ker.FiniteIndex := Subgroup.finiteIndex_ker π₂
  have hKidx : K.index ≠ 0 := Subgroup.index_inf_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    (Subgroup.FiniteIndex.index_ne_zero)
  have hKrel : K.relIndex ΓA ≠ 0 := ne_zero_of_dvd_ne_zero hKidx (Subgroup.relIndex_dvd_index_of_normal K ΓA)
  have hle : (ΓA ⊓ K).map ι ≤ Γ := (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
  have hmapΓ : ΓA.map ι = Γ := Subgroup.map_comap_eq_self hΓ
  have hrel : ((ΓA ⊓ K).map ι).relIndex Γ ≠ 0 := by
    rw [← hmapΓ, Subgroup.relIndex_map_map_of_injective _ _ hιinj, Subgroup.inf_relIndex_left]
    exact hKrel
  refine ⟨(ΓA ⊓ K).map ι, hle, hrel, sel_fg_of_relIndex hfg hle hrel, ?_⟩
  -- torsion-freeness
  rintro g hg hfin
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hhK : h ∈ K := (Subgroup.mem_inf.1 hh).2
  have hhfin : IsOfFinOrder h := (hιinj.isOfFinOrder_iff).1 hfin
  suffices h = 1 by rw [this, map_one]
  by_contra hne
  have hord0 : orderOf h ≠ 0 := (orderOf_pos_iff.2 hhfin).ne'
  have hord1 : orderOf h ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hord1
  have hh'ord : orderOf (h ^ (orderOf h / r)) = r := orderOf_pow_orderOf_div hord0 hrd
  have hh'K : h ^ (orderOf h / r) ∈ K := K.pow_mem hhK _
  have hh'1 : h ^ (orderOf h / r) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hh'ord
    exact hr.one_lt.ne hh'ord
  have hpow : (h ^ (orderOf h / r)) ^ r = 1 := by
    have h1 := pow_orderOf_eq_one (h ^ (orderOf h / r))
    rwa [hh'ord] at h1
  set h' := h ^ (orderOf h / r) with hh'
  set X : Matrix n n A := (h' : Matrix n n A) - 1 with hX
  have h1X : 1 + X = (h' : Matrix n n A) := by
    rw [hX]
    abel
  have hXpow : (1 + X) ^ r = 1 := by
    rw [h1X, ← Matrix.SpecialLinearGroup.coe_pow, hpow, Matrix.SpecialLinearGroup.coe_one]
  have hXm : ∀ (m : Ideal A), Matrix.SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk m) h' = 1 →
      ∀ a b, X a b ∈ m := by
    intro m hm a b
    have h1 := congrArg (fun x : Matrix.SpecialLinearGroup n (A ⧸ m) => (x : Matrix n n (A ⧸ m)) a b) hm
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_one] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, hX, Matrix.sub_apply, map_sub, h1]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hK1 : π₁ h' = 1 := (Subgroup.mem_inf.1 hh'K).1
  have hK2 : π₂ h' = 1 := (Subgroup.mem_inf.1 hh'K).2
  have hX0 : X = 0 := by
    by_cases hr1 : (r : A) ∈ m₁
    · exact sel_congr_torsion m₂ (hXm m₂ hK2) (hm₁₂ r hr hr1) hXpow
    · exact sel_congr_torsion m₁ (hXm m₁ hK1) hr1 hXpow
  exact hh'1 (Subtype.ext ((sub_eq_zero.1 hX0).trans Matrix.SpecialLinearGroup.coe_one.symm))

/-- **Selberg's lemma** (for `SL(2, ℝ)`): a finitely generated subgroup has a finitely generated, torsion-free
subgroup of finite index. -/
theorem sel_selberg {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfg : Γ.FG) :
    ∃ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧ Γ'.FG ∧
      ∀ g ∈ Γ', IsOfFinOrder g → g = 1 :=
  sel_selberg_generic hfg

end LiZhongQC
