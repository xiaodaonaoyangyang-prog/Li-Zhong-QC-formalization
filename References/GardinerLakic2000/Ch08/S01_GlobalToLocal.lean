import References.GardinerLakic2000.Ch03.S11_AppendixEquivalenceProof
import References.GardinerLakic2000.Ch07.S04_UniquenessOfGeodesics

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.1 Global to local (with the chapter introduction)

Source `teichmuller.txt`, lines 6529–6589 (Chapter 8, introduction and §8.1).

* Definition (`QC(Γ, Γ′)`: quasiconformal self-maps `h` of ℍ with `h Γ h⁻¹ = Γ′`; for `Γ′ = Γ` the group `QC(Γ)` of
  Ch. 10, l. 7937, used from §8.1 on) — `IsQCConj`, `qcNormalizer`, with the boundary map `qcBdry`
* Definition (the geometric isomorphism `ρ_h([f]) = [f ∘ h⁻¹]`, l. 6531) — `IsRhoGamma`
* Definition (holomorphic automorphisms and biholomorphic maps of `T`, l. 6537; derivative at the basepoint, l. 6543)
  — `IsBasePointT`, `IsHolAutT`, `HasScalarDerivAtBase`
* Unlabelled (geometric isomorphisms are biholomorphic isometries, l. 6531; used at l. 6537, 6549) —
  `para8_0_geometric_hol`
* Theorem 1 (Cartan's uniqueness theorem, l. 6547) — `thm8_1`
* Definition (the Teichmüller disc `D_φ`, l. 6551) — exists: `GardinerLakic2000.teichmullerDisc` (batch B, §7.4)
* Lemma 1 (l. 6553) — `lemma8_1`
* Theorem 2 (l. 6581) — `thm8_2`

Not items: the outline l. 6537–6549 (the proof strategy of Theorems 8.9, 8.10); the density of Teichmüller discs
through the origin (l. 6588, a step of the proof of Theorem 2). Modelling (leader calibration of Part C, C0.1–C0.3):
`T` is the Fuchsian model `LiZhongQC.TeichGamma Γ` (`T(R)` for `R = ℍ/Γ`); a map of `T` is holomorphic when it maps
the holomorphic discs of batch B (`holDiscsT`, discs read in the Bers chart) to holomorphic discs [reading];
`G′([id]) = αI` is read in the Bers chart along those discs; quasiconformal maps of `ℍ` are maps `ℂ → ℂ`, `K`-q.c. on
`ℍ`, whose boundary values are read in the Riemann sphere: `qcBdry h : ExtPlane → ExtPlane` is the limit of `h` from
`ℍ`, and `IsQCConj` requires it to extend `h` continuously to the closure of `ℍ` in `ℂ̂` (so a point of `ℝ` may go to
`∞`; AUDIT5_GL L2: the former `ContinuousOn h (closure ℍ)` with finite values forced `h(∞) = ∞`, which lost the
mapping classes without a lift fixing `∞`); `ρ_h` is a relation (the class of `f^μ ∘ h⁻¹` is determined by its
boundary values on `ℝ̂`, up to a real Möbius normalization). Teichmüller discs use the unit-norm `φ ∈ A(Γ)` of
batch B.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC upperHalf lowerHalf unitDisc BeltramiGamma TeichGamma teichSetoidGamma teichDistanceGamma
  bersMapGamma fMuSym h36p_m IsFuchsian integrableAutomorphicQD phiArea IsFundamentalDomainH)

/-- Helper for `IsQCConj` (§8.1; AUDIT5_GL L2). The boundary map of a self-map `h` of `ℍ`, read in the Riemann sphere:
`qcBdry h p` is the limit of `h(q)` as `q → p` inside `ℍ` (`h` on `ℍ` viewed in `ℂ̂`). For a quasiconformal self-map
of `ℍ` this is the homeomorphism of `ℍ̄ ∪ {∞}` extending `h`; it may send a real point to `∞`. -/
def qcBdry (h : ℂ → ℂ) (p : LiZhongQC.ExtPlane) : LiZhongQC.ExtPlane :=
  limUnder (𝓝[LiZhongQC.toExt upperHalf] p) fun q : LiZhongQC.ExtPlane =>
    OnePoint.elim q LiZhongQC.extInf fun z => ((h z : ℂ) : LiZhongQC.ExtPlane)

/-- **Definition** (`QC(Γ, Γ′)`, Ch. 10, l. 7937; used from §8.1 on). `h` is a quasiconformal self-map of `ℍ` with
`h Γ h⁻¹ = Γ′`: every `γ ∈ Γ` is carried to some `γ′ ∈ Γ′` and conversely (on `ℍ`). Its boundary map `qcBdry h`
extends `h` continuously to the closure of `ℍ` in `ℂ̂` and maps `ℝ̂` onto `ℝ̂` (no normalization at `∞`). -/
def IsQCConj (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (h : ℂ → ℂ) : Prop :=
  (∃ K : ℝ, IsKQC h upperHalf K) ∧ h '' upperHalf = upperHalf ∧
    (∀ p ∈ closure (LiZhongQC.toExt upperHalf), Tendsto (fun q : LiZhongQC.ExtPlane =>
      OnePoint.elim q LiZhongQC.extInf fun z => ((h z : ℂ) : LiZhongQC.ExtPlane))
        (𝓝[LiZhongQC.toExt upperHalf] p) (𝓝 (qcBdry h p))) ∧
    qcBdry h '' LiZhongQC.extRealLine = LiZhongQC.extRealLine ∧
    (∀ γ ∈ Γ, ∃ γ' ∈ Γ', ∀ z ∈ upperHalf, h (h36p_m γ z) = h36p_m γ' (h z)) ∧
    ∀ γ' ∈ Γ', ∃ γ ∈ Γ, ∀ z ∈ upperHalf, h (h36p_m γ z) = h36p_m γ' (h z)

/-- **Definition** (`QC(Γ)`, l. 7937). The normalizer of `Γ` in the quasiconformal self-maps of `ℍ`. -/
def qcNormalizer (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) := {h | IsQCConj Γ Γ h}

/-- **Definition** (geometric isomorphism, l. 6531). `Φ : T(Γ) → T(Γ′)` is `ρ_h`, `[f] ↦ [f ∘ h⁻¹]`: whenever the
normalized solution of `ν` agrees on `ℝ̂` with `f^μ ∘ h⁻¹` up to a real Möbius map, `Φ[μ] = [ν]`. Read in `ℂ̂`:
`f^ν(h(x)) = A(f^μ(x))` for `x ∈ ℝ`, with the boundary map `qcBdry h` and `f^ν(∞) = ∞`. -/
def IsRhoGamma (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (h : ℂ → ℂ)
    (Φ : TeichGamma Γ → TeichGamma Γ') : Prop :=
  ∀ (μ : BeltramiGamma Γ) (ν : BeltramiGamma Γ'),
    (∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ x : ℝ,
      OnePoint.map (fMuSym ν.1.1) (qcBdry h ((x : ℂ) : LiZhongQC.ExtPlane)) =
        LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex A) ((fMuSym μ.1.1 x : ℂ) : LiZhongQC.ExtPlane)) →
      Φ (Quotient.mk (teichSetoidGamma Γ) μ) = Quotient.mk (teichSetoidGamma Γ') ν

/-- Helper (§8.1). `o` is the basepoint `[0]` of `T(Γ)`. -/
def IsBasePointT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (o : TeichGamma Γ) : Prop :=
  ∃ μ : BeltramiGamma Γ, (∀ z, μ.1.1 z = 0) ∧ o = Quotient.mk (teichSetoidGamma Γ) μ

/-- **Definition** (holomorphic automorphism / biholomorphic map of Teichmüller spaces, l. 6537; C0.2). `F` is a
bijection `T(Γ) → T(Γ′)` which, together with its inverse, maps holomorphic discs to holomorphic discs. -/
def IsHolAutT (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : TeichGamma Γ → TeichGamma Γ') : Prop :=
  (∀ f ∈ holDiscsT Γ, F ∘ f ∈ holDiscsT Γ') ∧
    ∃ G : TeichGamma Γ' → TeichGamma Γ, Function.LeftInverse G F ∧ Function.RightInverse G F ∧
      ∀ f ∈ holDiscsT Γ', G ∘ f ∈ holDiscsT Γ

/-- **Definition** (`G′([id]) = αI`, l. 6543, 6553; C0.2). The derivative of `G` at the basepoint `o` is `α` times the
identity, read in the Bers chart along the holomorphic discs through `o`. -/
def HasScalarDerivAtBase (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (G : TeichGamma Γ → TeichGamma Γ)
    (o : TeichGamma Γ) (α : ℂ) : Prop :=
  ∀ f ∈ holDiscsT Γ, f 0 = o → ∀ z ∈ lowerHalf,
    HasDerivAt (fun t => bersMapGamma Γ (G (f t)) z) (α * deriv (fun t => bersMapGamma Γ (f t) z) 0) 0

/-- **Unlabelled** (Ch. 8 introduction, l. 6531). A quasiconformal `h` with `h Γ h⁻¹ = Γ′` induces a geometric
isomorphism `ρ_h : T(Γ) → T(Γ′)`, which is biholomorphic and an isometry of Teichmüller's metric. -/
theorem para8_0_geometric_hol {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {h : ℂ → ℂ} (hh : IsQCConj Γ Γ' h) :
    ∃ Φ : TeichGamma Γ → TeichGamma Γ', IsRhoGamma Γ Γ' h Φ ∧ IsHolAutT Γ Γ' Φ ∧
      ∀ P Q, teichDistanceGamma (Φ P) (Φ Q) = teichDistanceGamma P Q := by
  sorry

/-- Helper for `thm8_1`: a slice `t ↦ G(t y) − t y` of a map `G` holomorphic on `U ⊇ B(0, r)` is holomorphic on the
closed disc `|t| ≤ s` whenever `s‖y‖ < r`. -/
theorem gl8_cartan_slice_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U)
    {r : ℝ} (hr : ball (0 : E) r ⊆ U) {G : E → E} (hG : DifferentiableOn ℂ G U) {y : E} {s : ℝ}
    (hsy : s * ‖y‖ < r) : DifferentiableOn ℂ (fun t : ℂ => G (t • y) - t • y) (closedBall 0 s) := by
  intro t ht
  have hts : ‖t‖ ≤ s := mem_closedBall_zero_iff.1 ht
  have hty : t • y ∈ U := hr (by
    rw [mem_ball_zero_iff, norm_smul]
    nlinarith [norm_nonneg y, norm_nonneg t])
  have hGd : DifferentiableAt ℂ G (t • y) := hG.differentiableAt (hU.mem_nhds hty)
  have h1 : DifferentiableAt ℂ (fun t : ℂ => t • y) t := differentiableAt_id.smul_const y
  exact ((hGd.comp t h1).sub h1).differentiableWithinAt

/-- Helper for `thm8_1`: the Taylor remainder of a holomorphic `g : ℂ → E` whose coefficients of order `< k` vanish.
If `g` is holomorphic on `|t| ≤ s` and bounded by `B` there, then `‖g(μ) − μ^k g^{(k)}(0)/k!‖ ≤ 4B(|μ|/s)^{k+1}`
for `|μ| ≤ s/2` (Taylor series and Cauchy's estimates). -/
theorem gl8_cartan_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {g : ℂ → E}
    {s B : ℝ} (hs : 0 < s) (hg : DifferentiableOn ℂ g (closedBall 0 s))
    (hB : ∀ t ∈ closedBall (0 : ℂ) s, ‖g t‖ ≤ B) {k : ℕ} (hlow : ∀ j < k, iteratedDeriv j g 0 = 0) {μ : ℂ}
    (hμ : ‖μ‖ ≤ s / 2) :
    ‖g μ - (k.factorial : ℂ)⁻¹ • μ ^ k • iteratedDeriv k g 0‖ ≤ 4 * B * (‖μ‖ / s) ^ (k + 1) := by
  have hμs : μ ∈ ball (0 : ℂ) s := by
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg μ]
  have hT := Complex.hasSum_taylorSeries_on_ball (hg.mono ball_subset_closedBall) hμs
  have hC : ∀ n : ℕ, ‖iteratedDeriv n g 0‖ ≤ n.factorial * B / s ^ n := fun n =>
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hs (hg.diffContOnCl_ball subset_rfl)
      (fun t ht => hB t (sphere_subset_closedBall ht))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hs.le))
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ‖μ‖ / s := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 / 2 := by
    rw [hq, div_le_iff₀ hs]
    linarith
  have hterm : ∀ n : ℕ, ‖(n.factorial : ℂ)⁻¹ • (μ - 0) ^ n • iteratedDeriv n g 0‖ ≤ B * q ^ n := by
    intro n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, sub_zero]
    calc (n.factorial : ℝ)⁻¹ * (‖μ‖ ^ n * ‖iteratedDeriv n g 0‖)
        ≤ (n.factorial : ℝ)⁻¹ * (‖μ‖ ^ n * (n.factorial * B / s ^ n)) := by gcongr; exact hC n
      _ = B * q ^ n := by
          rw [hq, div_pow]
          field_simp
  have hT' := (hasSum_nat_add_iff' (k + 1)).mpr hT
  have hsum : ∑ i ∈ Finset.range (k + 1), (i.factorial : ℂ)⁻¹ • (μ - 0) ^ i • iteratedDeriv i g 0 =
      (k.factorial : ℂ)⁻¹ • μ ^ k • iteratedDeriv k g 0 := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      rw [hlow i (Finset.mem_range.1 hi), smul_zero, smul_zero]), zero_add, sub_zero]
  rw [hsum] at hT'
  have hgeom : HasSum (fun n : ℕ => B * q ^ (n + (k + 1))) (B * q ^ (k + 1) * (1 - q)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left (B * q ^ (k + 1))
    convert this using 1
    funext n
    ring
  have hle := hT'.norm_le_of_bounded hgeom (fun n => hterm (n + (k + 1)))
  have h1q : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖g μ - (k.factorial : ℂ)⁻¹ • μ ^ k • iteratedDeriv k g 0‖ ≤ B * q ^ (k + 1) * (1 - q)⁻¹ := hle
    _ ≤ B * q ^ (k + 1) * 2 := by gcongr
    _ ≤ 4 * B * (‖μ‖ / s) ^ (k + 1) := by
        rw [← hq]
        nlinarith [pow_nonneg hq0 (k + 1)]

/-- Helper for `thm8_1`: coefficient extraction. If `g : ℂ → E` is holomorphic on `|t| < s` and
`‖g(t) − t^k a‖ ≤ K|t|^{k+1}` there, then `g^{(k)}(0) = k! a` (Cauchy's estimate on shrinking circles). -/
theorem gl8_cartan_extract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {g : ℂ → E}
    {s : ℝ} (hs : 0 < s) (hg : DifferentiableOn ℂ g (ball 0 s)) {k : ℕ} {a : E} {K : ℝ}
    (hK : ∀ t ∈ ball (0 : ℂ) s, ‖g t - t ^ k • a‖ ≤ K * ‖t‖ ^ (k + 1)) :
    iteratedDeriv k g 0 = (k.factorial : ℂ) • a := by
  have hgc : ContDiffAt ℂ k g 0 := (hg.contDiffOn isOpen_ball).contDiffAt (ball_mem_nhds 0 hs)
  have hpc : ContDiff ℂ k (fun t : ℂ => t ^ k) := contDiff_id.pow k
  have hmc : ContDiffAt ℂ k (fun t : ℂ => t ^ k • a) 0 := (hpc.smul contDiff_const).contDiffAt
  have hpow : iteratedDeriv k (fun t : ℂ => t ^ k • a) 0 = (k.factorial : ℂ) • a := by
    rw [iteratedDeriv_smul_const hpc.contDiffAt a, iteratedDeriv_fun_pow_zero]
    simp
  have hsplit : iteratedDeriv k (fun t => g t - t ^ k • a) 0 = iteratedDeriv k g 0 - (k.factorial : ℂ) • a := by
    rw [iteratedDeriv_fun_sub hgc hmc, hpow]
  -- Cauchy's estimate on circles of radius `ρ < s`
  have hbound : ∀ ρ : ℝ, 0 < ρ → ρ < s →
      ‖iteratedDeriv k (fun t => g t - t ^ k • a) 0‖ ≤ k.factorial * (K * ρ ^ (k + 1)) / ρ ^ k := by
    intro ρ hρ hρs
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ ?_ ?_
    · exact ((hg.mono (closedBall_subset_ball hρs)).sub
        (by fun_prop : Differentiable ℂ (fun t : ℂ => t ^ k • a)).differentiableOn).diffContOnCl_ball subset_rfl
    · intro t ht
      have ht' : ‖t‖ = ρ := mem_sphere_zero_iff_norm.1 ht
      have h := hK t (mem_ball_zero_iff.2 (by rw [ht']; exact hρs))
      rwa [ht'] at h
  have hzero : iteratedDeriv k (fun t => g t - t ^ k • a) 0 = 0 := by
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
    have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (s / 2) (ε / (k.factorial * (|K| + 1))) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρ]; exact lt_min (by positivity) (by positivity)
    have hρs : ρ < s := by
      rw [hρ]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hρε : ρ ≤ ε / (k.factorial * (|K| + 1)) := by rw [hρ]; exact min_le_right _ _
    have h := hbound ρ hρ0 hρs
    have e : (k.factorial : ℝ) * (K * ρ ^ (k + 1)) / ρ ^ k = k.factorial * K * ρ := by
      field_simp
      ring
    rw [e] at h
    have h2 : (k.factorial : ℝ) * K * ρ ≤ k.factorial * (|K| + 1) * ρ := by
      gcongr
      linarith [le_abs_self K]
    have h3 : (k.factorial : ℝ) * (|K| + 1) * ρ ≤ ε := by
      rw [le_div_iff₀ (by positivity)] at hρε
      linarith
    linarith
  rw [hsplit, sub_eq_zero] at hzero
  exact hzero

/-- Helper for `thm8_1`: a holomorphic `G` with `G(U) ⊆ U ⊆ B̄(0, M)` and `B(0, r) ⊆ U` is `2M/r`-Lipschitz on
`B(0, r/2)` (Cauchy's estimate for `t ↦ G(x + t v)` bounds `G′`; mean value inequality on the convex ball). -/
theorem gl8_cartan_lipG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U)
    {r M : ℝ} (hr0 : 0 < r) (hr : ball (0 : E) r ⊆ U) (hM : ∀ x ∈ U, ‖x‖ ≤ M) {G : E → E}
    (hG : DifferentiableOn ℂ G U) (hGU : MapsTo G U U) {a b : E} (ha : a ∈ ball (0 : E) (r / 2))
    (hb : b ∈ ball (0 : E) (r / 2)) : ‖G a - G b‖ ≤ 2 * M / r * ‖a - b‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (hr (mem_ball_self hr0)))
  have hdiff : ∀ x ∈ ball (0 : E) (r / 2), DifferentiableAt ℂ G x := fun x hx =>
    hG.differentiableAt (hU.mem_nhds (hr (ball_subset_ball (by linarith) hx)))
  have hbound : ∀ x ∈ ball (0 : E) (r / 2), ‖fderiv ℂ G x‖ ≤ 2 * M / r := by
    intro x hx
    have hx' : ‖x‖ < r / 2 := mem_ball_zero_iff.1 hx
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hvp : 0 < ‖v‖ := norm_pos_iff.2 hv
    -- the one-variable function `t ↦ G(x + t v)` on `|t| ≤ R = r/(2‖v‖)`
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r / (2 * ‖v‖) := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hR]; positivity
    have hRv : R * ‖v‖ = r / 2 := by rw [hR]; field_simp
    have hmem : ∀ t ∈ closedBall (0 : ℂ) R, x + t • v ∈ U := by
      intro t ht
      refine hr (mem_ball_zero_iff.2 ?_)
      have ht' : ‖t‖ ≤ R := mem_closedBall_zero_iff.1 ht
      calc ‖x + t • v‖ ≤ ‖x‖ + ‖t‖ * ‖v‖ := by rw [← norm_smul]; exact norm_add_le _ _
        _ ≤ ‖x‖ + R * ‖v‖ := by gcongr
        _ < r := by linarith
    have hφ : DifferentiableOn ℂ (fun t : ℂ => G (x + t • v)) (closedBall 0 R) := by
      intro t ht
      have h1 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) t :=
        (differentiableAt_id.smul_const v).const_add x
      exact ((hG.differentiableAt (hU.mem_nhds (hmem t ht))).comp t h1).differentiableWithinAt
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR0 (hφ.diffContOnCl_ball subset_rfl)
      (fun t ht => hM _ (hGU (hmem t (sphere_subset_closedBall ht))))
    have hderiv : deriv (fun t : ℂ => G (x + t • v)) 0 = fderiv ℂ G x v := by
      have h1 : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
      have h2 : HasFDerivAt G (fderiv ℂ G x) (x + (0 : ℂ) • v) := by
        rw [zero_smul, add_zero]
        exact (hdiff x hx).hasFDerivAt
      exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
    rw [hderiv] at hC
    calc ‖fderiv ℂ G x v‖ ≤ M / R := hC
      _ = 2 * M / r * ‖v‖ := by
          rw [hR]
          field_simp
  exact (convex_ball (0 : E) (r / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound hb ha

/-- Helper for `thm8_1`: the slice coefficients `c_k(y) = (d/dt)^k (G(t y) − t y)|_{t = 0}`, `k ≥ 1`, satisfy
`‖c_k(y) − c_k(y′)‖ ≤ k!(2M/r + 1)‖y − y′‖(4ρ/r)^{k−1}` for `‖y‖, ‖y′‖ ≤ ρ` (Cauchy's estimate on `|t| = r/(4ρ)`;
`G` is `2M/r`-Lipschitz on `B(0, r/2)` by Cauchy's estimate for `t ↦ G(x + t v)` and the mean value inequality). -/
theorem gl8_cartan_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set E}
    (hU : IsOpen U) {r M : ℝ} (hr0 : 0 < r) (hr : ball (0 : E) r ⊆ U) (hM : ∀ x ∈ U, ‖x‖ ≤ M) {G : E → E}
    (hG : DifferentiableOn ℂ G U) (hGU : MapsTo G U U) {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) {y y' : E}
    (hy : ‖y‖ ≤ ρ) (hy' : ‖y'‖ ≤ ρ) :
    ‖iteratedDeriv k (fun t : ℂ => G (t • y) - t • y) 0 - iteratedDeriv k (fun t : ℂ => G (t • y') - t • y') 0‖ ≤
      k.factorial * (2 * M / r + 1) * ‖y - y'‖ * (4 * ρ / r) ^ (k - 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (hr (mem_ball_self hr0)))
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r / (4 * ρ) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsρ : s * ρ = r / 4 := by rw [hs]; field_simp
  have hsy : s * ‖y‖ < r := by nlinarith [norm_nonneg y]
  have hsy' : s * ‖y'‖ < r := by nlinarith [norm_nonneg y']
  have h1 := gl8_cartan_slice_diff hU hr hG hsy
  have h2 := gl8_cartan_slice_diff hU hr hG hsy'
  have hc1 : ContDiffAt ℂ k (fun t : ℂ => G (t • y) - t • y) 0 :=
    ((h1.mono ball_subset_closedBall).contDiffOn isOpen_ball).contDiffAt (ball_mem_nhds 0 hs0)
  have hc2 : ContDiffAt ℂ k (fun t : ℂ => G (t • y') - t • y') 0 :=
    ((h2.mono ball_subset_closedBall).contDiffOn isOpen_ball).contDiffAt (ball_mem_nhds 0 hs0)
  rw [← iteratedDeriv_fun_sub hc1 hc2]
  -- the bound on the circle `|t| = s`
  have hbd : ∀ t ∈ sphere (0 : ℂ) s, ‖(G (t • y) - t • y) - (G (t • y') - t • y')‖ ≤
      (2 * M / r + 1) * (s * ‖y - y'‖) := by
    intro t ht
    have ht' : ‖t‖ = s := mem_sphere_zero_iff_norm.1 ht
    have hty : t • y ∈ ball (0 : E) (r / 2) := by
      rw [mem_ball_zero_iff, norm_smul, ht']
      nlinarith [norm_nonneg y]
    have hty' : t • y' ∈ ball (0 : E) (r / 2) := by
      rw [mem_ball_zero_iff, norm_smul, ht']
      nlinarith [norm_nonneg y']
    have hL := gl8_cartan_lipG hU hr0 hr hM hG hGU hty hty'
    have e : (G (t • y) - t • y) - (G (t • y') - t • y') = (G (t • y) - G (t • y')) - t • (y - y') := by
      rw [smul_sub]
      abel
    rw [e]
    calc ‖(G (t • y) - G (t • y')) - t • (y - y')‖ ≤ ‖G (t • y) - G (t • y')‖ + ‖t • (y - y')‖ := norm_sub_le _ _
      _ ≤ 2 * M / r * ‖t • y - t • y'‖ + ‖t • (y - y')‖ := by gcongr
      _ = (2 * M / r + 1) * (s * ‖y - y'‖) := by
          rw [← smul_sub, norm_smul, ht']
          ring
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hs0
    ((h1.sub h2).diffContOnCl_ball subset_rfl) hbd
  calc _ ≤ k.factorial * ((2 * M / r + 1) * (s * ‖y - y'‖)) / s ^ k := hC
    _ = k.factorial * (2 * M / r + 1) * ‖y - y'‖ * (4 * ρ / r) ^ (k - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        have hs' : 4 * ρ / r = s⁻¹ := by rw [hs, inv_div]
        have hs0' : s ≠ 0 := hs0.ne'
        have hr' : r ≠ 0 := hr0.ne'
        rw [Nat.add_sub_cancel, pow_succ, hs', inv_pow]
        field_simp

/-- Helper for `thm8_1`: iterating `H(y) = y + P(y) + O(‖y‖^{k+1})`, `k ≥ 2`, where `P(0) = 0` and
`‖P(y) − P(y′)‖ ≤ L‖y − y′‖ρ^{k−1}` for `‖y‖, ‖y′‖ ≤ ρ ≤ ρ₀`, gives `Hⁿ(y) = y + nP(y) + O(‖y‖^{k+1})` for each `n`. -/
theorem gl8_cartan_iterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H P : E → E} {k : ℕ} (hk : 2 ≤ k)
    {ρ₀ L B : ℝ} (hρ₀ : 0 < ρ₀) (hP0 : P 0 = 0)
    (hP : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ y y' : E, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ → ‖P y - P y'‖ ≤ L * ‖y - y'‖ * ρ ^ (k - 1))
    (hR : ∀ y : E, ‖y‖ ≤ ρ₀ → ‖H y - y - P y‖ ≤ B * ‖y‖ ^ (k + 1)) (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ ∀ y : E, ‖y‖ ≤ ρ → ‖H^[n] y - y - (n : ℂ) • P y‖ ≤ K * ‖y‖ ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hk1 : m + 2 - 1 = m + 1 := by omega
  rw [hk1] at hP
  obtain ⟨L', hL'0, hLL'⟩ : ∃ L' : ℝ, 0 ≤ L' ∧ L ≤ L' := ⟨max L 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B', hB'0, hBB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ B ≤ B' := ⟨max B 0, le_max_right _ _, le_max_left _ _⟩
  -- `‖P y‖ ≤ L′ ‖y‖^(m+2)`
  have hPy : ∀ y : E, ‖y‖ ≤ ρ₀ → ‖P y‖ ≤ L' * ‖y‖ ^ (m + 2) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [hP0]
    have h := hP ‖y‖ (norm_pos_iff.2 hy0) hy y 0 le_rfl (by simp)
    rw [hP0, sub_zero, sub_zero] at h
    calc ‖P y‖ ≤ L * ‖y‖ * ‖y‖ ^ (m + 1) := h
      _ ≤ L' * ‖y‖ * ‖y‖ ^ (m + 1) := by gcongr
      _ = L' * ‖y‖ ^ (m + 2) := by ring
  induction n with
  | zero => exact ⟨ρ₀, 0, hρ₀, fun y _ => by simp⟩
  | succ n ih =>
    obtain ⟨ρn, Kn, hρn, hKn⟩ := ih
    obtain ⟨Kn', hKn'0, hKK'⟩ : ∃ K' : ℝ, 0 ≤ K' ∧ Kn ≤ K' := ⟨max Kn 0, le_max_right _ _, le_max_left _ _⟩
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = n * L' + Kn' := ⟨_, rfl⟩
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (min ρn (ρ₀ / 2)) (min 1 (1 / (C + 1))) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by
      rw [hρ]
      exact lt_min (lt_min hρn (by positivity)) (lt_min one_pos (by positivity))
    refine ⟨ρ, B' * 2 ^ (m + 2 + 1) + Kn' + L' * C * 2 ^ (m + 1), hρ0, fun y hy => ?_⟩
    have hyn : ‖y‖ ≤ ρn := hy.trans (by rw [hρ]; exact (min_le_left _ _).trans (min_le_left _ _))
    have hy2 : ‖y‖ ≤ ρ₀ / 2 := hy.trans (by rw [hρ]; exact (min_le_left _ _).trans (min_le_right _ _))
    have hy1 : ‖y‖ ≤ 1 := hy.trans (by rw [hρ]; exact (min_le_right _ _).trans (min_le_left _ _))
    have hyC : ‖y‖ ≤ 1 / (C + 1) := hy.trans (by rw [hρ]; exact (min_le_right _ _).trans (min_le_right _ _))
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
    have hCy : C * ‖y‖ ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hyC
      nlinarith
    set z := H^[n] y with hz
    have hIH : ‖z - y - (n : ℂ) • P y‖ ≤ Kn' * ‖y‖ ^ (m + 2 + 1) :=
      (hKn y hyn).trans (by gcongr)
    have hpow : ‖y‖ ^ (m + 2 + 1) ≤ ‖y‖ ^ (m + 2) := pow_le_pow_of_le_one hy0 hy1 (by omega)
    -- `‖z − y‖ ≤ C ‖y‖^(m+2)`
    have hzy : ‖z - y‖ ≤ C * ‖y‖ ^ (m + 2) := by
      have hnP : ‖(n : ℂ) • P y‖ ≤ n * (L' * ‖y‖ ^ (m + 2)) := by
        rw [norm_smul, Complex.norm_natCast]
        gcongr
        exact hPy y (by linarith)
      calc ‖z - y‖ = ‖(z - y - (n : ℂ) • P y) + (n : ℂ) • P y‖ := by congr 1; abel
        _ ≤ ‖z - y - (n : ℂ) • P y‖ + ‖(n : ℂ) • P y‖ := norm_add_le _ _
        _ ≤ Kn' * ‖y‖ ^ (m + 2) + n * (L' * ‖y‖ ^ (m + 2)) := by
            gcongr
            exact hIH.trans (by gcongr)
        _ = C * ‖y‖ ^ (m + 2) := by rw [hC]; ring
    -- `‖z‖ ≤ 2 ‖y‖`
    have hpow2 : ‖y‖ ^ (m + 2) ≤ ‖y‖ := by
      calc ‖y‖ ^ (m + 2) = ‖y‖ ^ (m + 1) * ‖y‖ := pow_succ _ _
        _ ≤ 1 * ‖y‖ := by gcongr; exact pow_le_one₀ hy0 hy1
        _ = ‖y‖ := one_mul _
    have hz2 : ‖z‖ ≤ 2 * ‖y‖ := by
      have h1 : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
        calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      have h2 : C * ‖y‖ ^ (m + 2) ≤ ‖y‖ := by
        calc C * ‖y‖ ^ (m + 2) = C * ‖y‖ * ‖y‖ ^ (m + 1) := by ring
          _ ≤ 1 * ‖y‖ ^ (m + 1) := by gcongr
          _ = ‖y‖ ^ (m + 1) := one_mul _
          _ ≤ ‖y‖ := pow_le_of_le_one hy0 hy1 (by omega)
      linarith
    -- the three error terms
    have hz0 : ‖z‖ ≤ ρ₀ := by linarith
    have hE1 : ‖H z - z - P z‖ ≤ B' * 2 ^ (m + 2 + 1) * ‖y‖ ^ (m + 2 + 1) := by
      calc ‖H z - z - P z‖ ≤ B * ‖z‖ ^ (m + 2 + 1) := hR z hz0
        _ ≤ B' * (2 * ‖y‖) ^ (m + 2 + 1) := by gcongr
        _ = B' * 2 ^ (m + 2 + 1) * ‖y‖ ^ (m + 2 + 1) := by rw [mul_pow]; ring
    have hE3 : ‖P z - P y‖ ≤ L' * C * 2 ^ (m + 1) * ‖y‖ ^ (m + 2 + 1) := by
      rcases eq_or_ne y 0 with hy0' | hy0'
      · have hzy0 : z = y := by
          have h := hzy
          rw [hy0', norm_zero, zero_pow (by omega), mul_zero] at h
          rw [hy0']
          exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
        rw [hzy0, sub_self, norm_zero]
        positivity
      · have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0'
        have h := hP (2 * ‖y‖) (by positivity) (by linarith) z y hz2 (by linarith)
        calc ‖P z - P y‖ ≤ L * ‖z - y‖ * (2 * ‖y‖) ^ (m + 1) := h
          _ ≤ L' * (C * ‖y‖ ^ (m + 2)) * (2 * ‖y‖) ^ (m + 1) := by gcongr
          _ = L' * C * 2 ^ (m + 1) * (‖y‖ ^ (m + 2 + 1) * ‖y‖ ^ m) := by rw [mul_pow]; ring
          _ ≤ L' * C * 2 ^ (m + 1) * (‖y‖ ^ (m + 2 + 1) * 1) := by gcongr; exact pow_le_one₀ hy0 hy1
          _ = L' * C * 2 ^ (m + 1) * ‖y‖ ^ (m + 2 + 1) := by ring
    have e : H^[n + 1] y - y - ((n + 1 : ℕ) : ℂ) • P y =
        (H z - z - P z) + (z - y - (n : ℂ) • P y) + (P z - P y) := by
      rw [Function.iterate_succ_apply', ← hz, Nat.cast_succ, add_smul, one_smul]
      abel
    rw [e]
    calc ‖(H z - z - P z) + (z - y - (n : ℂ) • P y) + (P z - P y)‖
        ≤ ‖H z - z - P z‖ + ‖z - y - (n : ℂ) • P y‖ + ‖P z - P y‖ := norm_add₃_le
      _ ≤ B' * 2 ^ (m + 2 + 1) * ‖y‖ ^ (m + 2 + 1) + Kn' * ‖y‖ ^ (m + 2 + 1) +
          L' * C * 2 ^ (m + 1) * ‖y‖ ^ (m + 2 + 1) := by gcongr
      _ = (B' * 2 ^ (m + 2 + 1) + Kn' + L' * C * 2 ^ (m + 1)) * ‖y‖ ^ (m + 2 + 1) := by ring

/-- Helper for `thm8_1`: the identity theorem on a ball. If `H` is holomorphic on `U ⊇ B(c, ε)` and `H = id` near a
point `a ∈ B(c, ε)`, then `H = id` on `B(c, ε)` (the one-variable identity theorem on the complex lines through `a`,
whose traces on the ball are convex). -/
theorem gl8_cartan_ball_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set E}
    {H : E → E} (hH : DifferentiableOn ℂ H U) {c : E} {ε : ℝ} (hB : ball c ε ⊆ U) {a : E} (ha : a ∈ ball c ε)
    (hHa : H =ᶠ[𝓝 a] id) : EqOn H id (ball c ε) := by
  intro z hz
  -- the trace `S` of the ball on the complex line `t ↦ a + t (z − a)` is convex
  set f : ℂ →ₗ[ℝ] E := (LinearMap.toSpanSingleton ℂ E (z - a)).restrictScalars ℝ with hf
  have hfa : ∀ t : ℂ, f t = t • (z - a) := fun t => rfl
  set S : Set ℂ := f ⁻¹' ball (c - a) ε with hS
  have hmem : ∀ t : ℂ, t ∈ S ↔ a + t • (z - a) ∈ ball c ε := by
    intro t
    rw [hS, Set.mem_preimage, hfa, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm,
      show a + t • (z - a) - c = t • (z - a) - (c - a) by abel]
  have hSc : Convex ℝ S := (convex_ball (c - a) ε).linear_preimage f
  have hℓ : Continuous fun t : ℂ => a + t • (z - a) := by fun_prop
  have hSo : IsOpen S := by
    have hSe : S = (fun t : ℂ => a + t • (z - a)) ⁻¹' ball c ε := Set.ext hmem
    rw [hSe]
    exact isOpen_ball.preimage hℓ
  have h0 : (0 : ℂ) ∈ S := (hmem 0).2 (by simpa using ha)
  have h1 : (1 : ℂ) ∈ S := (hmem 1).2 (by simpa using hz)
  -- `φ(t) = H(a + t(z − a)) − (a + t(z − a))` is holomorphic on `S` and vanishes near `0`
  have hφ : DifferentiableOn ℂ (fun t : ℂ => H (a + t • (z - a)) - (a + t • (z - a))) S := by
    intro t ht
    have ht' := (hmem t).1 ht
    have hd : DifferentiableAt ℂ H (a + t • (z - a)) :=
      (hH.mono hB).differentiableAt (isOpen_ball.mem_nhds ht')
    have hl : DifferentiableAt ℂ (fun t : ℂ => a + t • (z - a)) t :=
      (differentiableAt_id.smul_const (z - a)).const_add a
    exact ((hd.comp t hl).sub hl).differentiableWithinAt
  have hφ0 : (fun t : ℂ => H (a + t • (z - a)) - (a + t • (z - a))) =ᶠ[𝓝 0] 0 := by
    have ht : Tendsto (fun t : ℂ => a + t • (z - a)) (𝓝 0) (𝓝 a) := by
      have := hℓ.tendsto 0
      simpa using this
    filter_upwards [ht.eventually hHa] with t h
    simp only [Pi.zero_apply, h, id_eq, sub_self]
  have hzero := (hφ.analyticOnNhd hSo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hSc.isPreconnected h0 hφ0 h1
  simp only [Pi.zero_apply, one_smul, add_sub_cancel] at hzero
  exact sub_eq_zero.1 hzero

/-- Helper for `thm8_1`: the inductive step. Let `H` be a holomorphic self-map of `U`, `B(0, r) ⊆ U ⊆ B̄(0, M)`,
whose slice coefficients `c_j(y) = (d/dt)^j (H(t y) − t y)|_{t = 0}` vanish for `j < k` (`k ≥ 2`) and `y ∈ B(0, r)`.
Then `c_k` vanishes on `B(0, r)`: `c_k` is `k`-homogeneous (`gl8_cartan_tail`, `gl8_cartan_extract`),
`H = id + c_k/k! + O(‖y‖^{k+1})` iterates to `Hⁿ = id + n c_k/k! + O_n(‖y‖^{k+1})` (`gl8_cartan_lip`,
`gl8_cartan_iterate`), so `n c_k(u)` is the `k`-th slice coefficient of `Hⁿ`, bounded independently of `n` by
Cauchy's estimate. -/
theorem gl8_cartan_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set E}
    (hU : IsOpen U) {r M : ℝ} (hr0 : 0 < r) (hr : ball (0 : E) r ⊆ U) (hM : ∀ x ∈ U, ‖x‖ ≤ M) {H : E → E}
    (hH : DifferentiableOn ℂ H U) (hHU : MapsTo H U U) {k : ℕ} (hk : 2 ≤ k)
    (hlow : ∀ j < k, ∀ y ∈ ball (0 : E) r, iteratedDeriv j (fun t : ℂ => H (t • y) - t • y) 0 = 0) :
    ∀ y ∈ ball (0 : E) r, iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 = 0 := by
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  -- the iterates are holomorphic self-maps of `U`
  have hHn : ∀ n : ℕ, DifferentiableOn ℂ (H^[n]) U ∧ MapsTo (H^[n]) U U := by
    intro n
    induction n with
    | zero => exact ⟨differentiableOn_id, mapsTo_id U⟩
    | succ n ih =>
      rw [Function.iterate_succ']
      exact ⟨hH.comp ih.1 ih.2, hHU.comp ih.2⟩
  -- slices of a self-map of `U` are bounded by `2M` on the discs `|t| ≤ s`, `s‖y‖ < r`
  have hbd : ∀ G : E → E, MapsTo G U U → ∀ y : E, ∀ s : ℝ, s * ‖y‖ < r →
      ∀ t ∈ closedBall (0 : ℂ) s, ‖G (t • y) - t • y‖ ≤ 2 * M := by
    intro G hGU y s hsy t ht
    have hts : ‖t‖ ≤ s := mem_closedBall_zero_iff.1 ht
    have hty : t • y ∈ U := hr (by
      rw [mem_ball_zero_iff, norm_smul]
      nlinarith [norm_nonneg y, norm_nonneg t])
    calc ‖G (t • y) - t • y‖ ≤ ‖G (t • y)‖ + ‖t • y‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM _ (hGU hty)) (hM _ hty)
      _ = 2 * M := by ring
  -- homogeneity `c_k(τ y) = τ^k c_k(y)`
  have hhom : ∀ y ∈ ball (0 : E) r, ∀ τ : ℂ,
      iteratedDeriv k (fun t : ℂ => H (t • (τ • y)) - t • (τ • y)) 0 =
        τ ^ k • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 := by
    intro y hy τ
    have hyr : ‖y‖ < r := mem_ball_zero_iff.1 hy
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r / (‖y‖ + 1) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    have hsy : s * ‖y‖ < r := by
      rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    obtain ⟨sτ, hsτ⟩ : ∃ sτ : ℝ, sτ = s / (2 * (‖τ‖ + 1)) := ⟨_, rfl⟩
    have hsτ0 : 0 < sτ := by rw [hsτ]; positivity
    have hsττ : sτ * ‖τ‖ ≤ s / 2 := by
      rw [hsτ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg τ]
    have hτy : sτ * ‖τ • y‖ < r := by
      rw [norm_smul, ← mul_assoc]
      nlinarith [norm_nonneg y]
    have hK : ∀ t ∈ ball (0 : ℂ) sτ, ‖(H (t • (τ • y)) - t • (τ • y)) -
        t ^ k • (τ ^ k • ((k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0))‖ ≤
        4 * (2 * M) * (‖τ‖ / s) ^ (k + 1) * ‖t‖ ^ (k + 1) := by
      intro t ht
      have ht' : ‖t‖ < sτ := mem_ball_zero_iff.1 ht
      have htτ : ‖t * τ‖ ≤ s / 2 := by
        rw [norm_mul]
        nlinarith [norm_nonneg τ, norm_nonneg t]
      have h := gl8_cartan_tail hs0 (gl8_cartan_slice_diff hU hr hH hsy) (hbd H hHU y s hsy)
        (fun j hj => hlow j hj y hy) htτ
      have e1 : t • (τ • y) = (t * τ) • y := smul_smul t τ y
      have e2 : t ^ k • (τ ^ k • ((k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0)) =
          (k.factorial : ℂ)⁻¹ • (t * τ) ^ k • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 := by
        simp only [smul_smul]
        congr 1
        ring
      rw [e1, e2]
      calc _ ≤ 4 * (2 * M) * (‖t * τ‖ / s) ^ (k + 1) := h
        _ = 4 * (2 * M) * (‖τ‖ / s) ^ (k + 1) * ‖t‖ ^ (k + 1) := by rw [norm_mul]; ring
    rw [gl8_cartan_extract hsτ0 ((gl8_cartan_slice_diff hU hr hH hτy).mono ball_subset_closedBall) hK]
    simp only [smul_smul]
    congr 1
    field_simp
  have hH0 : H 0 = 0 := by
    have h := hlow 0 (by omega) 0 (mem_ball_self hr0)
    simpa using h
  have hc0 : iteratedDeriv k (fun t : ℂ => H (t • (0 : E)) - t • (0 : E)) 0 = 0 := by
    have h := hhom 0 (mem_ball_self hr0) 0
    rw [smul_zero, zero_pow (by omega), zero_smul] at h
    exact h
  -- `P = c_k/k!`: Lipschitz-type bound and the expansion `H = id + P + O(‖y‖^{k+1})`
  have hP0 : (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • (0 : E)) - t • (0 : E)) 0 = 0 := by
    rw [hc0, smul_zero]
  have hP : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∀ y y' : E, ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      ‖(k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 -
        (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y') - t • y') 0‖ ≤
        (2 * M / r + 1) * (4 / r) ^ (k - 1) * ‖y - y'‖ * ρ ^ (k - 1) := by
    intro ρ hρ _ y y' hy hy'
    have h := gl8_cartan_lip hU hr0 hr hM hH hHU (by omega : 1 ≤ k) hρ hy hy'
    have hkpos : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    rw [← smul_sub, norm_smul, norm_inv, Complex.norm_natCast]
    calc (k.factorial : ℝ)⁻¹ * ‖iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 -
          iteratedDeriv k (fun t : ℂ => H (t • y') - t • y') 0‖
        ≤ (k.factorial : ℝ)⁻¹ * (k.factorial * (2 * M / r + 1) * ‖y - y'‖ * (4 * ρ / r) ^ (k - 1)) := by
          gcongr
      _ = (2 * M / r + 1) * (4 / r) ^ (k - 1) * ‖y - y'‖ * ρ ^ (k - 1) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hkpos.ne', one_mul]
          ring
  have hR : ∀ y : E, ‖y‖ ≤ r / 4 →
      ‖H y - y - (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0‖ ≤
        4 * (2 * M) * (2 / r) ^ (k + 1) * ‖y‖ ^ (k + 1) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [hc0, hH0]
      simp
    have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r / (2 * ‖y‖) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    have hsy : s * ‖y‖ < r := by
      rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have h1s : ‖(1 : ℂ)‖ ≤ s / 2 := by
      rw [norm_one, hs, div_div, le_div_iff₀ (by positivity)]
      linarith
    have h := gl8_cartan_tail hs0 (gl8_cartan_slice_diff hU hr hH hsy) (hbd H hHU y s hsy)
      (fun j hj => hlow j hj y (mem_ball_zero_iff.2 (by linarith))) h1s
    simp only [one_smul, one_pow, norm_one] at h
    calc _ ≤ 4 * (2 * M) * (1 / s) ^ (k + 1) := h
      _ = 4 * (2 * M) * (2 / r) ^ (k + 1) * ‖y‖ ^ (k + 1) := by
          rw [hs, one_div_div]
          ring
  have hit := fun n : ℕ => gl8_cartan_iterate (H := H)
    (P := fun y => (k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0) hk
    (by positivity : (0 : ℝ) < r / 4) hP0 hP hR n
  intro u hu
  -- `n c_k(u)` is the `k`-th slice coefficient of `Hⁿ`
  have hcoef : ∀ n : ℕ, iteratedDeriv k (fun t : ℂ => H^[n] (t • u) - t • u) 0 =
      (n : ℂ) • iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0 := by
    intro n
    obtain ⟨ρn, Kn, hρn, hKn⟩ := hit n
    obtain ⟨sn, hsn⟩ : ∃ sn : ℝ, sn = min ρn (r / 2) / (‖u‖ + 1) := ⟨_, rfl⟩
    have hmin : 0 < min ρn (r / 2) := lt_min hρn (by positivity)
    have hsn0 : 0 < sn := by rw [hsn]; positivity
    have hsnu : sn * ‖u‖ < min ρn (r / 2) := by
      rw [hsn, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    have hsnr : sn * ‖u‖ < r := by
      have := min_le_right ρn (r / 2)
      linarith
    have hK : ∀ t ∈ ball (0 : ℂ) sn, ‖(H^[n] (t • u) - t • u) -
        t ^ k • ((n : ℂ) • ((k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0))‖ ≤
        Kn * ‖u‖ ^ (k + 1) * ‖t‖ ^ (k + 1) := by
      intro t ht
      have ht' : ‖t‖ < sn := mem_ball_zero_iff.1 ht
      have htu : ‖t • u‖ ≤ ρn := by
        rw [norm_smul]
        have := min_le_left ρn (r / 2)
        nlinarith [norm_nonneg u, norm_nonneg t]
      have h : ‖H^[n] (t • u) - t • u - (n : ℂ) • ((k.factorial : ℂ)⁻¹ •
          iteratedDeriv k (fun s : ℂ => H (s • (t • u)) - s • (t • u)) 0)‖ ≤ Kn * ‖t • u‖ ^ (k + 1) :=
        hKn (t • u) htu
      rw [hhom u hu t] at h
      have e : (n : ℂ) • ((k.factorial : ℂ)⁻¹ • t ^ k • iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0) =
          t ^ k • ((n : ℂ) • ((k.factorial : ℂ)⁻¹ • iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0)) := by
        simp only [smul_smul]
        congr 1
        ring
      rw [e, norm_smul, mul_pow] at h
      calc _ ≤ Kn * (‖t‖ ^ (k + 1) * ‖u‖ ^ (k + 1)) := h
        _ = Kn * ‖u‖ ^ (k + 1) * ‖t‖ ^ (k + 1) := by ring
    rw [gl8_cartan_extract hsn0 ((gl8_cartan_slice_diff hU hr (hHn n).1 hsnr).mono ball_subset_closedBall) hK]
    simp only [smul_smul]
    congr 1
    field_simp
  -- Cauchy's estimate bounds `n ‖c_k(u)‖` independently of `n`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r / (‖u‖ + 1) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsu : s * ‖u‖ < r := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  have hbound : ∀ n : ℕ, (n : ℝ) * ‖iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0‖ ≤
      k.factorial * (2 * M) / s ^ k := by
    intro n
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hs0
      ((gl8_cartan_slice_diff hU hr (hHn n).1 hsu).diffContOnCl_ball subset_rfl)
      (fun t ht => hbd (H^[n]) (hHn n).2 u s hsu t (sphere_subset_closedBall ht))
    rwa [hcoef n, norm_smul, Complex.norm_natCast] at h
  by_contra hne
  have hpos : 0 < ‖iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0‖ := norm_pos_iff.2 hne
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (k.factorial * (2 * M) / s ^ k / ‖iteratedDeriv k (fun t : ℂ => H (t • u) - t • u) 0‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [hbound n]

/-- **Theorem 1** (Cartan's uniqueness theorem, §8.1, l. 6547). A biholomorphic self-map `H` of a bounded domain
containing the origin in a complex Banach space with `H(0) = 0` and `H′(0) = id` is the identity. -/
theorem thm8_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set E} (hU : IsOpen U)
    (hUc : IsConnected U) (hUb : Bornology.IsBounded U) (h0 : (0 : E) ∈ U) {H : E → E}
    (hH : DifferentiableOn ℂ H U) (hbij : BijOn H U U)
    (hinv : ∃ G : E → E, DifferentiableOn ℂ G U ∧ ∀ x ∈ U, G (H x) = x) (hH0 : H 0 = 0)
    (hD : fderiv ℂ H 0 = ContinuousLinearMap.id ℂ E) : EqOn H id U := by
  -- `hinv` and the surjectivity in `hbij` are not needed: Cartan's theorem only uses `H(U) ⊆ U`
  have _ := hinv
  have hHU : MapsTo H U U := hbij.1
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨M, hM'⟩ := hUb.subset_closedBall 0
  have hM : ∀ x ∈ U, ‖x‖ ≤ M := fun x hx => mem_closedBall_zero_iff.1 (hM' hx)
  -- all slice coefficients of `H − id` vanish on `B(0, r)` (strong induction on the order)
  have hall : ∀ k : ℕ, ∀ y ∈ ball (0 : E) r, iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
      · simp [hH0]
      · have h1 : HasFDerivAt H (fderiv ℂ H 0) ((0 : ℂ) • y) := by
          rw [zero_smul]
          exact (hH.differentiableAt (hU.mem_nhds h0)).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℂ => t • y) y 0 := by
          simpa using (hasDerivAt_id (0 : ℂ)).smul_const y
        have hd : HasDerivAt (fun t : ℂ => H (t • y) - t • y) (fderiv ℂ H 0 y - y) 0 :=
          (h1.comp_hasDerivAt (0 : ℂ) h2).sub h2
        rw [iteratedDeriv_one, hd.deriv, hD]
        simp
      · exact gl8_cartan_step hU hr0 hr hM hH hHU hk (fun j hj => ih j hj) y hy
  -- hence `H = id` on `B(0, r/2)`: the Taylor series of the slice at `t = 1` vanishes
  have hloc : ∀ y ∈ ball (0 : E) (r / 2), H y = y := by
    intro y hy
    have hy' : ‖y‖ < r / 2 := mem_ball_zero_iff.1 hy
    have hz : ∀ k : ℕ, iteratedDeriv k (fun t : ℂ => H (t • y) - t • y) 0 = 0 :=
      fun k => hall k y (mem_ball_zero_iff.2 (by linarith))
    have hsl := gl8_cartan_slice_diff hU hr hH (y := y) (s := 2) (by linarith)
    have hs := Complex.hasSum_taylorSeries_on_ball (hsl.mono ball_subset_closedBall)
      (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by rw [mem_ball, dist_zero_right, norm_one]; norm_num)
    simp only [hz, smul_zero, one_smul] at hs
    exact sub_eq_zero.1 (hs.unique hasSum_zero)
  -- the identity theorem on the connected `U` (`gl8_cartan_ball_id` on balls)
  have hsub : U ⊆ {x | ∀ᶠ z in 𝓝 x, H z = id z} := by
    refine hUc.isPreconnected.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨0, h0, ?_⟩ ?_
    · show ∀ᶠ z in 𝓝 (0 : E), H z = id z
      filter_upwards [ball_mem_nhds (0 : E) (half_pos hr0)] with z hz
      exact hloc z hz
    · rintro x ⟨hxc, hxU⟩
      obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 hU x hxU
      obtain ⟨a, haA, hax⟩ := Metric.mem_closure_iff.1 hxc ε hε0
      have hball := gl8_cartan_ball_id hH hε (mem_ball'.2 hax) haA
      show ∀ᶠ z in 𝓝 x, H z = id z
      filter_upwards [ball_mem_nhds x hε0] with z hz
      exact hball hz
  intro x hx
  exact (show ∀ᶠ z in 𝓝 x, H z = id z from hsub hx).self_of_nhds

/-- **Lemma 1** (§8.1, l. 6553). Let `G` be a holomorphic automorphism of `T` fixing the basepoint, with
`G′([id]) = αI`. Then `G([t|φ|/φ]) = [αt|φ|/φ]` for `|t| < 1` and every `φ ∈ A(R)` with `‖φ‖ = 1`; in particular
`G(D_φ) = D_φ` for every Teichmüller disc through the basepoint. -/
theorem lemma8_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {G : TeichGamma Γ → TeichGamma Γ} (hG : IsHolAutT Γ Γ G) {o : TeichGamma Γ}
    (ho : IsBasePointT Γ o) (hGo : G o = o) {α : ℂ} (hα : HasScalarDerivAtBase Γ G o α) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hφ1 : phiArea φ F = 1) :
    (∀ t ∈ unitDisc, ∀ μ ν : BeltramiGamma Γ, (∀ z ∈ upperHalf, μ.1.1 z = t * (conj (φ z) / ‖φ z‖)) →
      (∀ z ∈ upperHalf, ν.1.1 z = α * t * (conj (φ z) / ‖φ z‖)) →
        G (Quotient.mk (teichSetoidGamma Γ) μ) = Quotient.mk (teichSetoidGamma Γ) ν) ∧
      G '' teichmullerDisc Γ φ = teichmullerDisc Γ φ := by
  sorry

/-- **Theorem 2** (§8.1, l. 6581). A holomorphic automorphism of `T` fixing the basepoint with `G′([id]) = I` is the
identity. -/
theorem thm8_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {G : TeichGamma Γ → TeichGamma Γ} (hG : IsHolAutT Γ Γ G) {o : TeichGamma Γ} (ho : IsBasePointT Γ o)
    (hGo : G o = o) (hα : HasScalarDerivAtBase Γ G o 1) : ∀ P, G P = P := by
  sorry

end GardinerLakic2000
