/-
  Laurent coefficients of a meromorphic germ, via the residue calculus (Miranda Ch. VI §2).

  `laurentCoeff g c n` is the coefficient of `(z − c)^n` in the Laurent expansion of `g` at `c`,
  defined through the residue: `coeff_n(g) = Res_c (g(z)·(z − c)^{−n−1})`.  This is the
  technically cheapest definition — `resAt` already carries germ-invariance, ℂ-linearity (on
  isolated singularities), and the two Cauchy evaluations needed for the anchor lemmas:

  * `laurentCoeff_eq_zero_of_lt_order` — coefficients below the meromorphic order vanish
    (`resAt = 0` on germs of order `≥ 0`, via the analytic factorization);
  * `laurentCoeff_order_ne_zero` — the *leading* coefficient (at `n = order`) is nonzero
    (Cauchy's integral formula `resAt_mul_inv_sub`);
  * `le_order_iff_laurentCoeff_eq_zero` — the order is `≥ k` iff all coefficients below `k`
    vanish.  This is the bridge that identifies `L(D)` with the kernel of the Laurent-tail
    truncation map `α_D` (Miranda Ch. VI, Lemma 2.2 / p. 181).

  Pure one-variable complex analysis — no manifold — reusable verbatim in every chart.
-/
import Jacobians.MeromorphicTrace.MeromorphicTrace

open Complex Filter Topology

namespace Jacobians.LaurentTail

open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

/-- The **`n`-th Laurent coefficient** of `g : ℂ → ℂ` at `c`: the residue at `c` of
`g(z)·(z − c)^{−n−1}` (for `g = ∑ aₖ (z−c)^k` the only term surviving the contour integral is
`k = n`, giving `aₙ`). -/
noncomputable def laurentCoeff (g : ℂ → ℂ) (c : ℂ) (n : ℤ) : ℂ :=
  resAt (g * (· - c) ^ (-n - 1)) c

theorem laurentCoeff_def (g : ℂ → ℂ) (c : ℂ) (n : ℤ) :
    laurentCoeff g c n = resAt (fun z => g z * (z - c) ^ (-n - 1)) c := rfl

/-- The Laurent monomial `(· − c)^k` is meromorphic at `c`. -/
theorem meromorphicAt_monomial (c : ℂ) (k : ℤ) : MeromorphicAt ((· - c) ^ k) c :=
  ((MeromorphicAt.id c).sub (MeromorphicAt.const c c)).zpow k

/-- `g·(· − c)^k` has an isolated singularity at `c` whenever `g` is meromorphic at `c`. -/
theorem holoPunctured_mul_monomial {g : ℂ → ℂ} {c : ℂ} (hg : MeromorphicAt g c) (k : ℤ) :
    HoloPunctured (g * (· - c) ^ k) c :=
  (hg.mul (meromorphicAt_monomial c k)).holoPunctured

/-- Laurent coefficients are **germ invariants**: functions agreeing on a punctured
neighbourhood of `c` have the same coefficients. -/
theorem laurentCoeff_congr {g₁ g₂ : ℂ → ℂ} {c : ℂ} (h : g₁ =ᶠ[𝓝[≠] c] g₂) (n : ℤ) :
    laurentCoeff g₁ c n = laurentCoeff g₂ c n := by
  refine resAt_congr ?_
  filter_upwards [h] with z hz
  show g₁ z * (z - c) ^ (-n - 1) = g₂ z * (z - c) ^ (-n - 1)
  rw [hz]

@[simp] theorem laurentCoeff_zero (c : ℂ) (n : ℤ) : laurentCoeff (0 : ℂ → ℂ) c n = 0 := by
  have h0 : ((0 : ℂ → ℂ) * (· - c) ^ (-n - 1)) = fun _ => (0 : ℂ) := by
    funext z
    show (0 : ℂ) * (z - c) ^ (-n - 1) = 0
    ring
  rw [laurentCoeff, h0, resAt_zero]

/-- ℂ-additivity of the Laurent coefficients (on meromorphic germs). -/
theorem laurentCoeff_add {g₁ g₂ : ℂ → ℂ} {c : ℂ} (h₁ : MeromorphicAt g₁ c)
    (h₂ : MeromorphicAt g₂ c) (n : ℤ) :
    laurentCoeff (g₁ + g₂) c n = laurentCoeff g₁ c n + laurentCoeff g₂ c n := by
  have hsplit : ((g₁ + g₂) * (· - c) ^ (-n - 1))
      = (g₁ * (· - c) ^ (-n - 1)) + (g₂ * (· - c) ^ (-n - 1)) := by
    funext z
    show (g₁ z + g₂ z) * (z - c) ^ (-n - 1)
      = g₁ z * (z - c) ^ (-n - 1) + g₂ z * (z - c) ^ (-n - 1)
    ring
  rw [laurentCoeff, hsplit,
    resAt_add (holoPunctured_mul_monomial h₁ _) (holoPunctured_mul_monomial h₂ _)]
  rfl

/-- ℂ-homogeneity of the Laurent coefficients (on meromorphic germs). -/
theorem laurentCoeff_smul {g : ℂ → ℂ} {c : ℂ} (a : ℂ) (hg : MeromorphicAt g c) (n : ℤ) :
    laurentCoeff (a • g) c n = a * laurentCoeff g c n := by
  have hsplit : ((a • g) * (· - c) ^ (-n - 1)) = a • (g * (· - c) ^ (-n - 1)) := by
    funext z
    show (a * g z) * (z - c) ^ (-n - 1) = a * (g z * (z - c) ^ (-n - 1))
    ring
  rw [laurentCoeff, hsplit, resAt_smul a (holoPunctured_mul_monomial hg _)]
  rfl

/-- **Residues of nonnegative-order germs vanish.**  If `F` is meromorphic at `c` with
`meromorphicOrderAt F c ≥ 0`, then `resAt F c = 0`: either `F` vanishes near `c`, or it agrees on
a punctured neighbourhood with the analytic function `(· − c)^m • G` (`m ≥ 0`, `G` analytic). -/
theorem resAt_eq_zero_of_nonneg_order {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (h : 0 ≤ meromorphicOrderAt F c) : resAt F c = 0 := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · have h0 : F =ᶠ[𝓝[≠] c] fun _ => (0 : ℂ) := meromorphicOrderAt_eq_top_iff.mp htop
    rw [resAt_congr h0, resAt_zero]
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    have hm0 : 0 ≤ m := by
      rw [← hm] at h
      exact_mod_cast h
    obtain ⟨G, hGana, _hGne, hGev⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hm.symm
    have hfun : (fun z => (z - c) ^ m • G z) = fun z => (z - c) ^ m.toNat • G z := by
      funext z
      congr 1
      conv_lhs => rw [← Int.toNat_of_nonneg hm0]
      exact zpow_natCast _ _
    have hana : AnalyticAt ℂ (fun z => (z - c) ^ m • G z) c := by
      rw [hfun]
      exact ((analyticAt_id.sub analyticAt_const).pow _).smul hGana
    rw [resAt_congr hGev, resAt_eq_zero_of_analyticAt hana]

/-- **Anchor (a): coefficients below the order vanish.** -/
theorem laurentCoeff_eq_zero_of_lt_order {g : ℂ → ℂ} {c : ℂ} {n : ℤ} (hg : MeromorphicAt g c)
    (hn : (n : WithTop ℤ) < meromorphicOrderAt g c) : laurentCoeff g c n = 0 := by
  have hmono : MeromorphicAt ((· - c) ^ (-n - 1) : ℂ → ℂ) c := meromorphicAt_monomial c _
  have hprod : MeromorphicAt (g * (· - c) ^ (-n - 1)) c := hg.mul hmono
  have horder : 0 ≤ meromorphicOrderAt (g * (· - c) ^ (-n - 1)) c := by
    rw [meromorphicOrderAt_mul hg hmono, meromorphicOrderAt_zpow_id_sub_const]
    cases hO : meromorphicOrderAt g c with
    | top => rw [WithTop.top_add]; exact le_top
    | coe m =>
      rw [hO] at hn
      have hnm : n < m := by exact_mod_cast hn
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      omega
  exact resAt_eq_zero_of_nonneg_order hprod horder

/-- **Anchor (a′): the leading coefficient is nonzero.**  If `g` has finite order `m` at `c`, its
`m`-th Laurent coefficient does not vanish (Cauchy's integral formula on the analytic factor). -/
theorem laurentCoeff_order_ne_zero {g : ℂ → ℂ} {c : ℂ} {m : ℤ} (hg : MeromorphicAt g c)
    (h : meromorphicOrderAt g c = (m : WithTop ℤ)) : laurentCoeff g c m ≠ 0 := by
  obtain ⟨G, hGana, hGne, hGev⟩ := (meromorphicOrderAt_eq_int_iff hg).mp h
  have hev : (g * (· - c) ^ (-m - 1)) =ᶠ[𝓝[≠] c] fun z => G z * (z - c)⁻¹ := by
    filter_upwards [hGev, self_mem_nhdsWithin] with z hz hzne
    have hsub : z - c ≠ 0 := sub_ne_zero.mpr hzne
    show g z * (z - c) ^ (-m - 1) = G z * (z - c)⁻¹
    rw [hz, smul_eq_mul]
    calc (z - c) ^ m * G z * (z - c) ^ (-m - 1)
        = G z * ((z - c) ^ m * (z - c) ^ (-m - 1)) := by ring
      _ = G z * (z - c) ^ (m + (-m - 1)) := by rw [zpow_add₀ hsub]
      _ = G z * (z - c)⁻¹ := by rw [show m + (-m - 1) = -1 by ring, zpow_neg_one]
  rw [laurentCoeff, resAt_congr hev, resAt_mul_inv_sub hGana]
  exact hGne

/-- **Anchor (b): order via coefficients.**  A meromorphic germ has order `≥ k` iff all its
Laurent coefficients of degree `< k` vanish. -/
theorem le_order_iff_laurentCoeff_eq_zero {g : ℂ → ℂ} {c : ℂ} (hg : MeromorphicAt g c) (k : ℤ) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt g c ↔ ∀ n : ℤ, n < k → laurentCoeff g c n = 0 := by
  constructor
  · intro hk n hn
    exact laurentCoeff_eq_zero_of_lt_order hg
      (lt_of_lt_of_le (by exact_mod_cast hn : (n : WithTop ℤ) < (k : WithTop ℤ)) hk)
  · intro hco
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have hmk : m < k := by
      rw [← hm] at hlt
      exact_mod_cast hlt
    exact laurentCoeff_order_ne_zero hg hm.symm (hco m hmk)

/-- Sanity check: the residue (`n = −1` coefficient) of the simple pole `(· − c)⁻¹` is `1`. -/
example (c : ℂ) : laurentCoeff (fun z => (z - c)⁻¹) c (-1) = 1 := by
  have hfun : ((fun z => (z - c)⁻¹) * (· - c) ^ (-(-1 : ℤ) - 1)) = fun z => (z - c)⁻¹ := by
    funext z
    show (z - c)⁻¹ * (z - c) ^ (-(-1 : ℤ) - 1) = (z - c)⁻¹
    norm_num
  rw [laurentCoeff, hfun, resAt_sub_inv]

end Jacobians.LaurentTail
