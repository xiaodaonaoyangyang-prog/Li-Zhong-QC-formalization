import Mathlib

/-! First genuine Hurwitz foundation: finite-order germ rigidity and faithful cyclic planar stabilizers. -/

open Filter Set
open scoped Topology

namespace LiZhongQC

/-- Iterates of a map fixing p retain strict derivative one at p. -/
theorem h84l_iterate_hasStrictDerivAt_one {f : ℂ → ℂ} {p : ℂ}
    (hf : HasStrictDerivAt f 1 p) (hfix : f p = p) (k : ℕ) :
    HasStrictDerivAt (f^[k]) 1 p := by
  induction k with
  | zero =>
      simpa only [Function.iterate_zero] using (hasStrictDerivAt_id p)
  | succ k hk =>
      have houter : HasStrictDerivAt (f^[k]) 1 (f p) := by
        simpa only [hfix] using hk
      have hcomp := houter.comp p hf
      simpa only [Function.iterate_succ, one_mul] using hcomp

/-- Finite-order rigidity for a germ with strict derivative one.
The finite orbit sum A(z)=Σ(k<N)f^[k](z) is an unnormalised average coordinate:
A'(p)=N≠0 and A∘f=A as germs. Its genuine local inverse forces f=id as germs.
Only an eventual iteration identity is required, not a global identity of f^[N]. -/
theorem h84l_periodic_germ_eq_id {f : ℂ → ℂ} {p : ℂ} {N : ℕ}
    (hf : HasStrictDerivAt f 1 p) (hfix : f p = p) (hN : 0 < N)
    (hperiod : (f^[N]) =ᶠ[𝓝 p] id) :
    f =ᶠ[𝓝 p] id := by
  classical
  let A : ℂ → ℂ := fun z => ∑ k ∈ Finset.range N, (f^[k]) z
  have hiter : ∀ k, HasStrictDerivAt (f^[k]) 1 p :=
    fun k => h84l_iterate_hasStrictDerivAt_one hf hfix k
  have hA : HasStrictDerivAt A (N : ℂ) p := by
    have hsum := HasStrictDerivAt.fun_sum
      (u := Finset.range N) (A := fun k => f^[k]) (A' := fun _ => (1 : ℂ))
      (fun k _ => hiter k)
    change HasStrictDerivAt (fun z => ∑ k ∈ Finset.range N, (f^[k]) z) (N : ℂ) p
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hsum
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hshift : ∀ z, A (f z) + z = A z + (f^[N]) z := by
    intro z
    change (∑ k ∈ Finset.range N, (f^[k]) (f z)) + z =
      (∑ k ∈ Finset.range N, (f^[k]) z) + (f^[N]) z
    simp_rw [← Function.iterate_succ_apply]
    have hfront :
        (∑ k ∈ Finset.range (N + 1), (f^[k]) z) =
          (∑ k ∈ Finset.range N, (f^[k + 1]) z) + z := by
      simpa only [Function.iterate_zero_apply] using
        (Finset.sum_range_succ' (fun k => (f^[k]) z) N)
    have hback :
        (∑ k ∈ Finset.range (N + 1), (f^[k]) z) =
          (∑ k ∈ Finset.range N, (f^[k]) z) + (f^[N]) z :=
      Finset.sum_range_succ (fun k => (f^[k]) z) N
    exact hfront.symm.trans hback
  have hAf : ∀ᶠ z in 𝓝 p, A (f z) = A z := by
    filter_upwards [hperiod] with z hz
    change (f^[N]) z = z at hz
    have h := hshift z
    rw [hz] at h
    exact add_right_cancel h
  have hleft := hA.eventually_left_inverse hN0
  have hcont : Tendsto f (𝓝 p) (𝓝 p) := by
    simpa only [hfix] using hf.hasDerivAt.continuousAt.tendsto
  have hleftf := hcont.eventually hleft
  filter_upwards [hAf, hleft, hleftf] with z hz hZ hF
  change f z = z
  rw [hz] at hF
  exact hF.symm.trans hZ

/-- A finite-order holomorphic germ tangent to the identity is the identity germ.
Analyticity supplies a strict derivative; no local identity is assumed. -/
theorem h84l_analytic_periodic_germ_eq_id {f : ℂ → ℂ} {p : ℂ} {N : ℕ}
    (hf : AnalyticAt ℂ f p) (hfix : f p = p) (hN : 0 < N)
    (hderiv : deriv f p = 1) (hperiod : (f^[N]) =ᶠ[𝓝 p] id) :
    f =ᶠ[𝓝 p] id := by
  have hs : HasStrictDerivAt f 1 p := by
    simpa only [hderiv] using hf.hasStrictDerivAt
  exact h84l_periodic_germ_eq_id hs hfix hN hperiod

/-- Identity propagation along a connected planar domain after finite-order germ rigidity.
This invokes the existing analytic identity principle rather than assuming continuation. -/
theorem h84l_holomorphic_periodic_eqOn_id {U : Set ℂ} {f : ℂ → ℂ} {p : ℂ} {N : ℕ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hp : p ∈ U)
    (hfix : f p = p) (hN : 0 < N) (hderiv : deriv f p = 1)
    (hperiod : (f^[N]) =ᶠ[𝓝 p] id) :
    EqOn f id U := by
  have hgerm := h84l_analytic_periodic_germ_eq_id (hf p hp) hfix hN hderiv hperiod
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hU hp hgerm

/-- The scalar derivative representation of a group of analytic permutations fixing p.
This is the ordinary tangent action in a chosen planar coordinate. Its multiplication
law is proved by the chain rule, and its values are automatically units because G is a group.
No faithfulness hypothesis is used to define this character. -/
noncomputable def h84l_derivativeCharacter {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm ℂ) {U : Set ℂ} {p : ℂ} (hp : p ∈ U)
    (hhol : ∀ g, AnalyticOnNhd ℂ (ρ g) U) (hfix : ∀ g, ρ g p = p) :
    G →* ℂ where
  toFun g := deriv (ρ g) p
  map_one' := by
    change deriv (⇑(ρ 1)) p = 1
    rw [map_one, Equiv.Perm.coe_one]
    exact deriv_id p
  map_mul' g h := by
    change deriv (⇑(ρ (g * h))) p = deriv (ρ g) p * deriv (ρ h) p
    have hg : HasDerivAt (ρ g) (deriv (ρ g) p) (ρ h p) := by
      rw [hfix h]
      exact (hhol g p hp).differentiableAt.hasDerivAt
    have hh := (hhol h p hp).differentiableAt.hasDerivAt
    rw [map_mul, Equiv.Perm.coe_mul]
    exact (hg.comp p hh).deriv

/-- The derivative character is faithful for a finite analytic action fixing p.
The hypothesis hfaith is ordinary faithfulness of the action on U: an element acting
pointwise as identity there is the group identity. It does not assume derivative faithfulness.
Finite order plus the orbit-sum lemma proves that the derivative kernel acts identically. -/
theorem h84l_derivativeCharacter_injective {G : Type*} [Group G] [Finite G]
    (ρ : G →* Equiv.Perm ℂ) {U : Set ℂ} {p : ℂ}
    (hp : p ∈ U) (hU : IsPreconnected U)
    (hhol : ∀ g, AnalyticOnNhd ℂ (ρ g) U) (hfix : ∀ g, ρ g p = p)
    (hfaith : ∀ g, EqOn (ρ g) id U → g = 1) :
    Function.Injective (h84l_derivativeCharacter ρ hp hhol hfix) := by
  let χ := h84l_derivativeCharacter ρ hp hhol hfix
  have hker : ∀ g, χ g = 1 → g = 1 := by
    intro g hg
    change deriv (ρ g) p = 1 at hg
    have hpow : (ρ g) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hperiod : ((ρ g : ℂ → ℂ)^[orderOf g]) =ᶠ[𝓝 p] id := by
      apply Filter.Eventually.of_forall
      intro z
      change ((ρ g : ℂ → ℂ)^[orderOf g]) z = z
      rw [Equiv.Perm.iterate_eq_pow, hpow]
      rfl
    have heq := h84l_holomorphic_periodic_eqOn_id
      (hhol g) hU hp (hfix g) (orderOf_pos g) hg hperiod
    exact hfaith g heq
  change Function.Injective χ
  intro a b hab
  have hmap : χ (a⁻¹ * b) = 1 := by
    calc
      χ (a⁻¹ * b) = χ (a⁻¹) * χ b := χ.map_mul _ _
      _ = χ (a⁻¹) * χ a := by rw [← hab]
      _ = χ (a⁻¹ * a) := (χ.map_mul _ _).symm
      _ = 1 := by rw [inv_mul_cancel, χ.map_one]
  exact inv_mul_eq_one.mp (hker (a⁻¹ * b) hmap)

/-- The same faithful tangent representation with its natural codomain of complex units. -/
theorem h84l_derivativeCharacter_units_injective {G : Type*} [Group G] [Finite G]
    (ρ : G →* Equiv.Perm ℂ) {U : Set ℂ} {p : ℂ}
    (hp : p ∈ U) (hU : IsPreconnected U)
    (hhol : ∀ g, AnalyticOnNhd ℂ (ρ g) U) (hfix : ∀ g, ρ g p = p)
    (hfaith : ∀ g, EqOn (ρ g) id U → g = 1) :
    Function.Injective (h84l_derivativeCharacter ρ hp hhol hfix).toHomUnits := by
  intro a b hab
  have hcoe := congrArg (fun u : ℂˣ => (u : ℂ)) hab
  have hscalar :
      h84l_derivativeCharacter ρ hp hhol hfix a =
        h84l_derivativeCharacter ρ hp hhol hfix b := by
    simpa only [MonoidHom.coe_toHomUnits] using hcoe
  exact h84l_derivativeCharacter_injective ρ hp hU hhol hfix hfaith hscalar

/-- A finite faithful analytic stabilizer in a planar coordinate is cyclic.
The analytic argument establishes injectivity; the final step reuses the existing
finite-subgroup-of-an-integral-domain theorem. This does not assume cyclicity. -/
theorem h84l_finite_analytic_stabilizer_isCyclic {G : Type*} [Group G] [Finite G]
    (ρ : G →* Equiv.Perm ℂ) {U : Set ℂ} {p : ℂ}
    (hp : p ∈ U) (hU : IsPreconnected U)
    (hhol : ∀ g, AnalyticOnNhd ℂ (ρ g) U) (hfix : ∀ g, ρ g p = p)
    (hfaith : ∀ g, EqOn (ρ g) id U → g = 1) :
    IsCyclic G := by
  exact isCyclic_of_injective_ringHom (h84l_derivativeCharacter ρ hp hhol hfix)
    (h84l_derivativeCharacter_injective ρ hp hU hhol hfix hfaith)

end LiZhongQC

