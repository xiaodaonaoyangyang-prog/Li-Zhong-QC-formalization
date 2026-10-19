import References.LehtoVirtanen1973.Ch02.S08_QCContinuation

/-!
# Lehto–Virtanen, Chapter II §9: Circular dilatation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §9
(pp. 105–108; `full.md` P1:3095–3206).

The circular dilatation `H` is `ℝ≥0∞`-valued: it may be infinite. It is read in the charts of I.1.6 (`localRep`),
which give exactly the book's three cases: `w(z + ζ) - w(z)` at a finite point with a finite value, `w(1/ζ) - w(∞)`
at `z = ∞`, and `1/w` where `w(z) = ∞`. The distortion function `λ(K)` is `LiZhongQC.lambdaInv`, as in §6.3.

* Definition (circular dilatation `H` of a topological mapping, §9.1) — `circularDilatation`
* Unlabelled (§9.1, P1:3107–3113): at a regular point the circular dilatation equals the dilatation quotient —
  `circularDilatation_eq_dilQuot`
* Theorem 9.1 (§9.2, Mori) — `thm2_9_1`
* Formula (9.1) (§9.2; cited by number at P2:1034) — `eq2_9_1`
* Theorem 9.2 (§9.3, Lehto–Virtanen–Väisälä) — `thm2_9_2`
* Theorem 9.3 (§9.4) — `thm2_9_3`

Not stated (inventory: omitted): the equality `F = D = H` for regular quasiconformal mappings (P1:3115, immediate
from Theorem I.9.4 and the unlabelled item above); the example `w(z) = e^{-1/|z| + i arg z}` with `H(0) = 1`,
`F(0) = ∞` (P1:3117–3123); the asymptotic
expansion of `λ(K)` restated at P1:3158 (formula (6.10), stated in §6.4).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §9.1 Definition of the circular dilatation -/

/-- **Definition** (circular dilatation, Ch. II §9.1). For a topological mapping `w`,
`H_w(z) = limsup_{r → +0} max_α |w(z + re^{iα}) - w(z)| / min_α |w(z + re^{iα}) - w(z)|` for `z ≠ ∞`, `w(z) ≠ ∞`,
extended by `H_w(∞) = H_{w̃}(0)`, `w̃(z) = w(1/z)`, and `H_w(z) = H_{1/w}(z)` where `w(z) = ∞`.
Modelling: `ℝ≥0∞`-valued, the maximum and minimum over `α` being `⨆`, `⨅` over real `α`; the three cases are read
through `localRep`. The chart junk and the value `x/0 = ∞` occur only for large `r` or for mappings which are not
one-to-one near `z`; for a topological mapping they are not seen by the `limsup` as `r → +0`. -/
def circularDilatation (w : ExtPlane → ExtPlane) (z : ExtPlane) : ℝ≥0∞ :=
  limsup (fun r : ℝ => (⨆ α : ℝ, ‖localRep w z ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) /
    ⨅ α : ℝ, ‖localRep w z ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) (𝓝[>] 0)

/-- Helper (II §9.1). The local representation of `w` at any point `z` of `ℂ̄` vanishes at `0`: the charts are
centred at `z` and at `w(z)`. -/
theorem lv29_localRep_zero (w : ExtPlane → ExtPlane) (z : ExtPlane) : localRep w z 0 = 0 := by
  have hz : extChartInv z 0 = z := by
    induction z using OnePoint.rec with
    | infty => simp [extChartInv]
    | coe a => simp [extChartInv]
  show extChart (w z) (w (extChartInv z 0)) = 0
  rw [hz]
  generalize w z = q
  induction q using OnePoint.rec with
  | infty => rfl
  | coe a => simp [extChart]

/-- Helper (II §9.1). If `g(0) = 0` and `g` is differentiable at `0` with nonzero Jacobian, then
`max_α |g(re^{iα})| / min_α |g(re^{iα})|` tends to the dilatation quotient `D` of `g` at `0` as `r → +0`:
`g(re^{iα}) = r g′(0)e^{iα} + o(r)` uniformly in `α`, and `min_α |g′(0)e^{iα}| = ||g_z| − |g_{\bar z}|| > 0`. -/
theorem lv29_tendsto_ratio {g : ℂ → ℂ} (h0 : g 0 = 0) (hd : DifferentiableAt ℝ g 0)
    (hJ : LinearMap.det (fderiv ℝ g 0 : ℂ →ₗ[ℝ] ℂ) ≠ 0) :
    Tendsto (fun r : ℝ => (⨆ α : ℝ, ‖g ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) /
      ⨅ α : ℝ, ‖g ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (dilQuotient g 0))) := by
  set L := fderiv ℝ g 0 with hLdef
  set u : ℝ → ℂ := fun α => exp ((α : ℂ) * I) with hudef
  have hu : ∀ α, ‖u α‖ = 1 := fun α => Complex.norm_exp_ofReal_mul_I α
  -- `‖L(u α)‖` lies between `m = ||a| − |b|| > 0` and `|a| + |b|` (`a = g_z(0)`, `b = g_{\bar z}(0)`)
  have hab : ‖LiZhongQC.dz g 0‖ ≠ ‖LiZhongQC.dzbar g 0‖ := by
    intro h
    apply hJ
    rw [LiZhongQC.det_fderiv_eq_jacobian hd, LiZhongQC.jacobian, h]
    ring
  set m := |‖LiZhongQC.dz g 0‖ - ‖LiZhongQC.dzbar g 0‖| with hmdef
  have hm0 : 0 < m := abs_pos.2 (sub_ne_zero.2 hab)
  have hLu : ∀ α, ‖L (u α)‖ = ‖LiZhongQC.dz g 0 * u α + LiZhongQC.dzbar g 0 * starRingEnd ℂ (u α)‖ :=
    fun α => by rw [hLdef, LiZhongQC.fderiv_eq_dz_dzbar hd]
  have hlow : ∀ α, m ≤ ‖L (u α)‖ := fun α => by
    rw [hLu, hmdef]
    have h1 := abs_norm_sub_norm_le (LiZhongQC.dz g 0 * u α) (-(LiZhongQC.dzbar g 0 * starRingEnd ℂ (u α)))
    rw [sub_neg_eq_add, norm_neg, norm_mul, norm_mul, Complex.norm_conj, hu, mul_one, mul_one] at h1
    exact h1
  have hup : ∀ α, ‖L (u α)‖ ≤ ‖LiZhongQC.dz g 0‖ + ‖LiZhongQC.dzbar g 0‖ := fun α => by
    rw [hLu]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, hu, mul_one, mul_one]
  have hbA : BddAbove (range fun α => ‖L (u α)‖) := ⟨_, by rintro _ ⟨α, rfl⟩; exact hup α⟩
  have hbB : BddBelow (range fun α => ‖L (u α)‖) := ⟨0, by rintro _ ⟨α, rfl⟩; exact norm_nonneg _⟩
  set S := ⨆ α, ‖L (u α)‖ with hSdef
  set Iq := ⨅ α, ‖L (u α)‖ with hIdef
  have hI0 : 0 < Iq := hm0.trans_le (le_ciInf hlow)
  -- the dilatation quotient of `g` at `0` is `S / Iq`
  have hD : dilQuotient g 0 = S / Iq := by
    have e : ∀ α : ℝ, ‖dirDeriv g 0 α‖ = ‖L (u α)‖ := fun α => by
      rw [dirDeriv, norm_mul, show -((α : ℂ) * I) = ((-α : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    simp only [dilQuotient, e]
    rfl
  -- uniform first-order expansion: `|‖g(r u)‖ - r ‖L u‖| ≤ ε r` for small `r`
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hd.hasFDerivAt
  have hexp : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → ∀ α : ℝ,
      |‖g ((r : ℂ) * u α)‖ - r * ‖L (u α)‖| ≤ ε * r := fun ε hε => by
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hlo.def hε)
    refine ⟨δ, hδ, fun r hr hrδ α => ?_⟩
    have hn : ‖(r : ℂ) * u α‖ = r := by rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have h := hball (show dist ((r : ℂ) * u α) 0 < δ by rw [dist_zero_right, hn]; exact hrδ)
    simp only [zero_add, h0, sub_zero] at h
    have hL : L ((r : ℂ) * u α) = (r : ℂ) * L (u α) := by
      rw [← Complex.real_smul, map_smul, Complex.real_smul]
    rw [hL, hn] at h
    have h2 := abs_norm_sub_norm_le (g ((r : ℂ) * u α)) ((r : ℂ) * L (u α))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le] at h2
    linarith [h2.trans h, mul_comm ε r]
  -- the normalized maximum and minimum converge to `S` and `Iq`
  set A : ℝ → ℝ := fun r => ⨆ α, ‖g ((r : ℂ) * u α)‖ with hAdef
  set B : ℝ → ℝ := fun r => ⨅ α, ‖g ((r : ℂ) * u α)‖ with hBdef
  have hbnd : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), BddAbove (range fun α => ‖g ((r : ℂ) * u α)‖) ∧
      |A r / r - S| ≤ ε ∧ |B r / r - Iq| ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, hδb⟩ := hexp ε hε
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hr0 : 0 < r := hr.1
    have hb := hδb r hr.1 hr.2
    have hbA' : BddAbove (range fun α => ‖g ((r : ℂ) * u α)‖) := by
      refine ⟨r * (‖LiZhongQC.dz g 0‖ + ‖LiZhongQC.dzbar g 0‖) + ε * r, ?_⟩
      rintro _ ⟨α, rfl⟩
      have := hb α
      have := mul_le_mul_of_nonneg_left (hup α) hr0.le
      linarith [abs_le.1 (hb α)]
    have hbB' : BddBelow (range fun α => ‖g ((r : ℂ) * u α)‖) := ⟨0, by rintro _ ⟨α, rfl⟩; exact norm_nonneg _⟩
    refine ⟨hbA', ?_, ?_⟩
    · rw [abs_le]
      constructor
      · -- `S - ε ≤ A r / r`
        have : S ≤ A r / r + ε := by
          refine ciSup_le fun α => ?_
          have h1 : ‖g ((r : ℂ) * u α)‖ ≤ A r := le_ciSup hbA' α
          have h2 := (abs_le.1 (hb α)).1
          rw [← sub_le_iff_le_add, le_div_iff₀ hr0]
          nlinarith
        linarith
      · -- `A r / r ≤ S + ε`
        have : A r ≤ (S + ε) * r := by
          refine ciSup_le fun α => ?_
          have h1 : ‖L (u α)‖ ≤ S := le_ciSup hbA α
          have h2 := (abs_le.1 (hb α)).2
          nlinarith
        have := (div_le_iff₀ hr0).2 this
        linarith
    · rw [abs_le]
      constructor
      · -- `Iq - ε ≤ B r / r`
        have : (Iq - ε) * r ≤ B r := by
          refine le_ciInf fun α => ?_
          have h1 : Iq ≤ ‖L (u α)‖ := ciInf_le hbB α
          have h2 := (abs_le.1 (hb α)).1
          nlinarith
        have := (le_div_iff₀ hr0).2 this
        linarith
      · -- `B r / r ≤ Iq + ε`
        have : B r / r - ε ≤ Iq := by
          refine le_ciInf fun α => ?_
          have h1 : B r ≤ ‖g ((r : ℂ) * u α)‖ := ciInf_le hbB' α
          have h2 := (abs_le.1 (hb α)).2
          rw [sub_le_iff_le_add, div_le_iff₀ hr0]
          nlinarith
        linarith
  have hAt : Tendsto (fun r => A r / r) (𝓝[>] 0) (𝓝 S) :=
    Metric.tendsto_nhds.2 fun ε hε => by
      filter_upwards [hbnd (ε / 2) (half_pos hε)] with r hr
      rw [Real.dist_eq]
      linarith [hr.2.1]
  have hBt : Tendsto (fun r => B r / r) (𝓝[>] 0) (𝓝 Iq) :=
    Metric.tendsto_nhds.2 fun ε hε => by
      filter_upwards [hbnd (ε / 2) (half_pos hε)] with r hr
      rw [Real.dist_eq]
      linarith [hr.2.2]
  have hratio : Tendsto (fun r => (A r / r) / (B r / r)) (𝓝[>] 0) (𝓝 (S / Iq)) := hAt.div hBt hI0.ne'
  -- back to `ℝ≥0∞`: for small `r` the quotient is `ofReal (A r / B r)`
  rw [hD]
  refine (ENNReal.tendsto_ofReal hratio).congr' ?_
  filter_upwards [hbnd (Iq / 2) (half_pos hI0), self_mem_nhdsWithin] with r hr hr0
  obtain ⟨hbA', -, hBr⟩ := hr
  have hr0' : (0 : ℝ) < r := hr0
  have hBpos : 0 < B r := by
    have : Iq / 2 ≤ B r / r := by linarith [(abs_le.1 hBr).1]
    have := (div_pos hI0 two_pos).trans_le this
    exact (div_pos_iff_of_pos_right hr0').1 this
  have hbB' : BddBelow (range fun α => ‖g ((r : ℂ) * u α)‖) := ⟨0, by rintro _ ⟨α, rfl⟩; exact norm_nonneg _⟩
  have eA : (⨆ α : ℝ, ‖g ((r : ℂ) * u α)‖ₑ) = ENNReal.ofReal (A r) := by
    rw [hAdef, Monotone.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt ENNReal.ofReal_mono hbA']
    simp only [ofReal_norm]
  have eB : (⨅ α : ℝ, ‖g ((r : ℂ) * u α)‖ₑ) = ENNReal.ofReal (B r) := by
    rw [hBdef, Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt ENNReal.ofReal_mono hbB']
    simp only [ofReal_norm]
  show ENNReal.ofReal ((A r / r) / (B r / r)) =
    (⨆ α : ℝ, ‖g ((r : ℂ) * u α)‖ₑ) / ⨅ α : ℝ, ‖g ((r : ℂ) * u α)‖ₑ
  rw [eA, eB, ← ENNReal.ofReal_div_of_pos hBpos, div_div_div_cancel_right₀ hr0'.ne']

/-- **Unlabelled** (Ch. II §9.1, P1:3107–3113). If `z` is a regular point of the topological mapping `w` (also when
`z = ∞` or `w(z) = ∞`, by the invariance of `H` with respect to linear mappings), then `H(z) = D(z)`: the dilatation
quotient is the restriction of the circular dilatation to regular points (cited in IV.4.1 and V.2).
Modelling: `w` is a homeomorphism of `G` onto `w(G)` and `z` a regular point (I.1.6); `D(z)` is `dilQuot` (I.3.3,
I.9.4), read in the same charts. -/
theorem circularDilatation_eq_dilQuot {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsHomeoOn w G (w '' G))
    {z : ExtPlane} (hz : IsRegularPointOf w G z) : circularDilatation w z = ENNReal.ofReal (dilQuot w z) := by
  -- the homeomorphism hypothesis is idle: regularity at `z` carries the content
  have _ := hw
  obtain ⟨-, -, hd, hJ⟩ := hz
  exact (lv29_tendsto_ratio (lv29_localRep_zero w z) hd hJ).limsup_eq

/-! ## §9.2 Upper bounds for the circular dilatation -/

/-- Helper (II §9.2, the charts of I.1.6). Off `0`, the inverse chart at `z` is a `1`-quasiconformal map `T` of the
punctured plane (Li Zhong's Definition 7.1): `ζ ↦ a + ζ` at a finite point `z = a`, `ζ ↦ 1/ζ` at `z = ∞`. Its
values differ from `z`. -/
theorem lv29m_inner (z : ExtPlane) :
    ∃ T : ℂ → ℂ, LiZhongQC.IsKQC T {0}ᶜ 1 ∧
      ∀ ζ : ℂ, ζ ≠ 0 → extChartInv z ζ = ((T ζ : ℂ) : ExtPlane) ∧ ((T ζ : ℂ) : ExtPlane) ≠ z := by
  induction z using OnePoint.rec with
  | infty =>
    refine ⟨fun ζ => ζ⁻¹, LiZhongQC.isKQC_one_of_conformal isOpen_compl_singleton
      ⟨fun ζ hζ => (differentiableAt_inv hζ).differentiableWithinAt, inv_injective.injOn, rfl⟩,
      fun ζ hζ => ⟨?_, OnePoint.coe_ne_infty _⟩⟩
    simp [extChartInv, hζ]
  | coe a =>
    refine ⟨fun ζ => a + ζ, LiZhongQC.isKQC_one_of_conformal isOpen_compl_singleton
      ⟨((differentiable_const a).add differentiable_id).differentiableOn, (add_right_injective a).injOn, rfl⟩,
      fun ζ hζ => ⟨rfl, fun h => hζ ?_⟩⟩
    have h' : a + ζ = a + 0 := by rw [add_zero]; exact OnePoint.coe_injective h
    exact add_left_cancel h'

/-- Helper (II §9.2, the charts of I.1.6). On the finite points of an open set `W`, the chart at `p` is a
`1`-quasiconformal map `S`: `y ↦ y - c` with `W = ℂ` at a finite point `p = c`, and `y ↦ 1/y` with `W = ℂ ∖ {0}` at
`p = ∞`. The set `W` together with `p` is a neighbourhood of `p`, and `S` vanishes on `W` only at `p`. -/
theorem lv29m_outer (p : ExtPlane) :
    ∃ (S : ℂ → ℂ) (W : Set ℂ), LiZhongQC.IsKQC S W 1 ∧ (∀ y ∈ W, extChart p (y : ExtPlane) = S y) ∧
      insert p (toExt W) ∈ 𝓝 p ∧ ∀ y ∈ W, S y = 0 → (y : ExtPlane) = p := by
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨fun y => y⁻¹, {0}ᶜ, LiZhongQC.isKQC_one_of_conformal isOpen_compl_singleton
      ⟨fun ζ hζ => (differentiableAt_inv hζ).differentiableWithinAt, inv_injective.injOn, rfl⟩,
      fun y _ => rfl, ?_, fun y hy h => absurd (inv_eq_zero.1 h) hy⟩
    refine mem_of_superset (isOpen_compl_singleton.mem_nhds (OnePoint.infty_ne_coe 0)) fun q hq => ?_
    induction q using OnePoint.rec with
    | infty => exact mem_insert _ _
    | coe y =>
      exact mem_insert_of_mem _ ⟨y, fun h => hq (by rw [mem_singleton_iff.1 h]; exact mem_singleton _), rfl⟩
  | coe c =>
    refine ⟨fun y => y - c, univ, LiZhongQC.isKQC_one_of_conformal isOpen_univ
      ⟨(differentiable_id.sub_const c).differentiableOn, sub_left_injective.injOn, rfl⟩,
      fun y _ => rfl, ?_, fun y _ h => by rw [sub_eq_zero.1 h]⟩
    refine mem_of_superset (OnePoint.isOpen_range_coe.mem_nhds ⟨c, rfl⟩) ?_
    rintro _ ⟨y, rfl⟩
    exact mem_insert_of_mem _ ⟨y, mem_univ y, rfl⟩

/-- Helper (II §9.2). Let `w` be `K`-quasiconformal on `G` and `z ∈ G`; the cases `z = ∞` and `w(z) = ∞` are
included. Near `0`, the local representation of `w` at `z` is continuous and one-to-one. Off `0` it is
`K`-quasiconformal in Li Zhong's sense: there it is `S ∘ w ∘ T`, with the `1`-quasiconformal charts of
`lv29m_inner` and `lv29m_outer`. -/
theorem lv29m_chart {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    {z : ExtPlane} (hz : z ∈ G) :
    ∃ ρ : ℝ, 0 < ρ ∧ ContinuousOn (localRep w z) (Metric.ball 0 ρ) ∧ InjOn (localRep w z) (Metric.ball 0 ρ) ∧
      LiZhongQC.IsKQC (localRep w z) (Metric.ball 0 ρ \ {0}) K := by
  have hf := lv13_isKQC_of_isKQuasiconformal hw
  obtain ⟨hGd, hsp, -⟩ := hw
  have hG : IsOpen G := hGd.1
  have hc : ContinuousOn w G := hsp.1.1
  have hi : InjOn w G := hsp.1.2.1
  obtain ⟨T, hTq, hT⟩ := lv29m_inner z
  obtain ⟨S, W, hSq, hS, hN, hS0⟩ := lv29m_outer (w z)
  obtain ⟨h0, hcz⟩ := lv15_extChartInv z
  have hwz : ContinuousAt w z := hc.continuousAt (hG.mem_nhds hz)
  have hwc : ContinuousAt (fun ζ => w (extChartInv z ζ)) 0 :=
    ContinuousAt.comp (g := w) (by rw [h0]; exact hwz) hcz
  -- near `0` the chart stays in `G`, and `w` stays in the chart domain at `w z`
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), extChartInv z ζ ∈ G ∧ w (extChartInv z ζ) ∈ insert (w z) (toExt W) :=
    (hcz.eventually (by rw [h0]; exact hG.mem_nhds hz)).and (hwc.eventually (by
      show insert (w z) (toExt W) ∈ 𝓝 (w (extChartInv z 0))
      rw [h0]
      exact hN))
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.1 hev
  have hUo : IsOpen (Metric.ball (0 : ℂ) ρ \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  -- off `0` the local representation is `S ∘ finiteMap w ∘ T`
  have key : ∀ ζ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ((T ζ : ℂ) : ExtPlane) ∈ G ∧ ∃ y ∈ W,
      w ((T ζ : ℂ) : ExtPlane) = (y : ExtPlane) ∧ finiteMap w (T ζ) = y ∧ localRep w z ζ = S y ∧
        (y : ExtPlane) ≠ w z := by
    intro ζ hζ
    obtain ⟨hTe, hTz⟩ := hT ζ hζ.2
    obtain ⟨hG', hW'⟩ := hρb (show dist ζ 0 < ρ from hζ.1)
    rw [hTe] at hG' hW'
    have hne : w ((T ζ : ℂ) : ExtPlane) ≠ w z := fun h => hTz (hi hG' hz h)
    rcases mem_insert_iff.1 hW' with h | ⟨y, hy, hyeq⟩
    · exact absurd h hne
    · refine ⟨hG', y, hy, hyeq.symm, ?_, ?_, ?_⟩
      · show finiteValue (w ((T ζ : ℂ) : ExtPlane)) = y
        rw [← hyeq]
        rfl
      · show extChart (w z) (w (extChartInv z ζ)) = S y
        rw [hTe, ← hyeq]
        exact hS y hy
      · rw [hyeq]
        exact hne
  have hTU : LiZhongQC.IsKQC T (Metric.ball (0 : ℂ) ρ \ {0}) 1 :=
    LiZhongQC.ac_t_isKQC_restrict hTq hUo fun ζ hζ => hζ.2
  have h1 := LiZhongQC.thm7_1_comp hTU hf (by
    rintro _ ⟨ζ, hζ, rfl⟩
    obtain ⟨hG', y, -, hyeq, -⟩ := key ζ hζ
    exact ⟨hG', by rw [hyeq]; exact OnePoint.coe_ne_infty y⟩)
  have h2 := LiZhongQC.thm7_1_comp h1 hSq (by
    rintro _ ⟨ζ, hζ, rfl⟩
    obtain ⟨-, y, hy, -, hfy, -⟩ := key ζ hζ
    show finiteMap w (T ζ) ∈ W
    rw [hfy]
    exact hy)
  rw [one_mul, mul_one] at h2
  have hFU : LiZhongQC.IsKQC (localRep w z) (Metric.ball (0 : ℂ) ρ \ {0}) K :=
    LiZhongQC.ad_isKQC_congr h2 fun ζ hζ => by
      obtain ⟨-, y, -, -, hfy, hloc, -⟩ := key ζ hζ
      show localRep w z ζ = S (finiteMap w (T ζ))
      rw [hloc, hfy]
  -- the local representation vanishes only at `0`
  have hF0 : ∀ ζ ∈ Metric.ball (0 : ℂ) ρ \ {0}, localRep w z ζ ≠ 0 := fun ζ hζ h => by
    obtain ⟨-, y, hy, -, -, hloc, hne⟩ := key ζ hζ
    exact hne (hS0 y hy (hloc ▸ h))
  refine ⟨ρ, hρ, fun ζ hζ => ?_, fun ζ₁ h₁ ζ₂ h₂ h => ?_, hFU⟩
  · by_cases hζ0 : ζ = 0
    · subst hζ0
      exact (lv15_localRep_continuousAt hwz).continuousWithinAt
    · exact ((hFU.2.2.1.1 ζ ⟨hζ, hζ0⟩).continuousAt (hUo.mem_nhds ⟨hζ, hζ0⟩)).continuousWithinAt
  · by_cases e1 : ζ₁ = 0 <;> by_cases e2 : ζ₂ = 0
    · rw [e1, e2]
    · rw [e1, lv29_localRep_zero] at h
      exact absurd h.symm (hF0 ζ₂ ⟨h₂, e2⟩)
    · rw [e2, lv29_localRep_zero] at h
      exact absurd h (hF0 ζ₁ ⟨h₁, e1⟩)
    · exact hFU.2.2.1.2.1 ⟨h₁, e1⟩ ⟨h₂, e2⟩ h

/-- Helper (II §9.2, the separation in Mori's proof). Let `g` be continuous and one-to-one on an open set `E`
containing the closed disc `|ζ - q| ≤ b`, with `0 < a < b`. Let the image `g(A)` of the annulus
`A : a < |ζ - q| < b` be doubly connected. If `|u - q| ≤ a` and `|v - q| = b`, then `g(A)` separates `g(q), g(u)`
from `g(v), ∞`. -/
theorem lv29m_sep {g : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hc : ContinuousOn g E) (hi : InjOn g E) {q u v : ℂ}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hcl : Metric.closedBall q b ⊆ E)
    (hdc : LiZhongQC.IsDoublyConnected (g '' LiZhongQC.annulusAt q a b)) (hu : ‖u - q‖ ≤ a) (hv : ‖v - q‖ = b) :
    LiZhongQC.SeparatesSets (g '' LiZhongQC.annulusAt q a b) {((g q : ℂ) : ExtPlane), ((g u : ℂ) : ExtPlane)}
      {((g v : ℂ) : ExtPlane), extInf} := by
  have _hE := hE  -- openness of `E` is not needed: the balls are open
  set A := LiZhongQC.annulusAt q a b with hAdef
  set S : Set ExtPlane := (toExt (g '' A))ᶜ with hSdef
  set P : Set ExtPlane := toExt (g '' Metric.closedBall q a) with hPdef
  set U : Set ExtPlane := toExt (g '' Metric.ball q b) with hUdef
  have hAE : A ⊆ E := fun ζ hζ => hcl (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hζ.2.le)
  have hcbE : Metric.closedBall q a ⊆ E := (Metric.closedBall_subset_closedBall hab.le).trans hcl
  have hbE : Metric.ball q b ⊆ E := Metric.ball_subset_closedBall.trans hcl
  -- points of `E` outside `A` are not mapped into `g(A)`
  have hout : ∀ ζ ∈ E, ζ ∉ A → ((g ζ : ℂ) : ExtPlane) ∈ S := by
    rintro ζ hζ hζA ⟨_, ⟨η, hη, rfl⟩, h⟩
    have e := hi (hAE hη) hζ (OnePoint.coe_injective h)
    rw [e] at hη
    exact hζA hη
  -- the image `P` of the inner closed disc: connected, closed, in `ℂ̄ ∖ g(A)`, containing `g(q)` and `g(u)`
  have hPS : P ⊆ S := by
    rintro _ ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
    refine hout ζ (hcbE hζ) fun hA => ?_
    have h2 : ‖ζ - q‖ ≤ a := by rw [← dist_eq_norm]; exact hζ
    exact absurd hA.1 (not_lt.2 h2)
  have hPc : IsPreconnected P :=
    ((convex_closedBall q a).isPreconnected.image g (hc.mono hcbE)).image _ OnePoint.continuous_coe.continuousOn
  have hPcl : IsClosed P :=
    (((isCompact_closedBall q a).image_of_continuousOn (hc.mono hcbE)).image OnePoint.continuous_coe).isClosed
  have hqP : ((g q : ℂ) : ExtPlane) ∈ P := ⟨g q, ⟨q, Metric.mem_closedBall_self ha.le, rfl⟩, rfl⟩
  have huP : ((g u : ℂ) : ExtPlane) ∈ P :=
    ⟨g u, ⟨u, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hu, rfl⟩, rfl⟩
  have hqS : ((g q : ℂ) : ExtPlane) ∈ S := hPS hqP
  have hinfS : extInf ∈ S := by
    rintro ⟨w, -, hw⟩
    exact OnePoint.coe_ne_infty w hw
  have hvE : v ∈ E := hcl (by rw [Metric.mem_closedBall, dist_eq_norm, hv])
  have hvS : ((g v : ℂ) : ExtPlane) ∈ S := hout v hvE fun h => by
    have h2 := h.2
    rw [hv] at h2
    exact lt_irrefl b h2
  -- the image `U` of the open disc `|ζ - q| < b` is open (invariance of domain), and `S ∩ U ⊆ P`
  have hUo : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _
    (LiZhongQC.isOpen_image_of_continuousOn_injOn Metric.isOpen_ball (hc.mono hbE) (hi.mono hbE))
  have hSU : ∀ x ∈ S, x ∈ U → x ∈ P := by
    rintro _ hxS ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
    refine ⟨g ζ, ⟨ζ, ?_, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hζb : ‖ζ - q‖ < b := by rw [← dist_eq_norm]; exact hζ
    exact hxS ⟨g ζ, ⟨ζ, ⟨hlt, hζb⟩, rfl⟩, rfl⟩
  -- so the component of `g(q)` in `ℂ̄ ∖ g(A)` lies in `U`
  have hCU : connectedComponentIn S ((g q : ℂ) : ExtPlane) ⊆ U := by
    have hpre : IsPreconnected (connectedComponentIn S ((g q : ℂ) : ExtPlane)) :=
      isPreconnected_connectedComponentIn
    have hcov : connectedComponentIn S ((g q : ℂ) : ExtPlane) ⊆ U ∪ Pᶜ := by
      intro x hx
      by_cases hxP : x ∈ P
      · left
        obtain ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩ := hxP
        exact ⟨g ζ, ⟨ζ, Metric.closedBall_subset_ball hab hζ, rfl⟩, rfl⟩
      · exact Or.inr hxP
    have hdis : connectedComponentIn S ((g q : ℂ) : ExtPlane) ∩ (U ∩ Pᶜ) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx =>
        hx.2.2 (hSU x (connectedComponentIn_subset _ _ hx.1) hx.2.1)
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre U Pᶜ hUo hPcl.isOpen_compl hcov hdis with h | h
    · exact h
    · exact absurd hqP (h (mem_connectedComponentIn hqS))
  have hvC : ((g v : ℂ) : ExtPlane) ∉ connectedComponentIn S ((g q : ℂ) : ExtPlane) := fun h => by
    obtain ⟨_, ⟨ζ, hζ, rfl⟩, h'⟩ := hCU h
    have e := hi (hbE hζ) hvE (OnePoint.coe_injective h')
    rw [e, Metric.mem_ball, dist_eq_norm, hv] at hζ
    exact lt_irrefl b hζ
  have hinfC : extInf ∉ connectedComponentIn S ((g q : ℂ) : ExtPlane) := fun h => by
    obtain ⟨_, -, h'⟩ := hCU h
    exact OnePoint.coe_ne_infty _ h'
  have hne : connectedComponentIn S ((g q : ℂ) : ExtPlane) ≠ connectedComponentIn S extInf := fun h =>
    hinfC (h ▸ mem_connectedComponentIn hinfS)
  -- two components: `g(v)` lies in the component of `∞`
  have hunion := LiZhongQC.gsep_z_compl_eq_union_of_ne hdc hqS hinfS hne
  have hvinf : ((g v : ℂ) : ExtPlane) ∈ connectedComponentIn S extInf := by
    rcases hunion.subset hvS with h | h
    · exact absurd h hvC
    · exact h
  refine ⟨_, hqS, _, hinfS, ?_, ?_, hne⟩
  · exact insert_subset_iff.2 ⟨mem_connectedComponentIn hqS,
      singleton_subset_iff.2 (hPc.subset_connectedComponentIn hqP hPS huP)⟩
  · exact insert_subset_iff.2 ⟨hvinf, singleton_subset_iff.2 (mem_connectedComponentIn hinfS)⟩

/-- Helper (II §9.2, Mori's argument). Let `F` be continuous and one-to-one on an open set `D`, `p ∈ D`, and let `F`
be `K`-quasiconformal on `D ∖ {p}` (Li Zhong's Definition 7.1). Let `x, y ∈ D \ {p}` with `|x - p| ≤ |y - p|`, and
let the closed disc `|ζ - F(p)| ≤ |F(x) - F(p)|` lie in `F(D)`. Then `|F(x) - F(p)| ≤ e^{πK} |F(y) - F(p)|`.
Proof idea: when `|F(y) - F(p)| < |F(x) - F(p)|`, the preimage of the annulus between these radii, translated by
`-p`, separates `0, y - p` from `x - p, ∞`. Teichmüller's module theorem then bounds its module by
`2μ(1/√2) = π`, and its image has module `log(|F(x) - F(p)|/|F(y) - F(p)|) ≤ Kπ` (Li Zhong's Theorem 7.4). -/
theorem lv29m_core {F : ℂ → ℂ} {D : Set ℂ} {K : ℝ} {p x y : ℂ} (hD : IsOpen D) (hc : ContinuousOn F D)
    (hi : InjOn F D) (hK : LiZhongQC.IsKQC F (D \ {p}) K) (hp : p ∈ D) (hx : x ∈ D) (hy : y ∈ D) (hxp : x ≠ p)
    (hyp : y ≠ p) (hxy : ‖x - p‖ ≤ ‖y - p‖) (hball : Metric.closedBall (F p) ‖F x - F p‖ ⊆ F '' D) :
    ‖F x - F p‖ ≤ Real.exp (Real.pi * K) * ‖F y - F p‖ := by
  have hK1 : 1 ≤ K := hK.2.1
  have hE1 : 1 ≤ Real.exp (Real.pi * K) := Real.one_le_exp (by positivity)
  have ha : 0 < ‖F y - F p‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hyp (hi hy hp h))
  rcases le_or_gt ‖F x - F p‖ ‖F y - F p‖ with hle | hlt
  · exact hle.trans (le_mul_of_one_le_left ha.le hE1)
  -- `H = F⁻¹ - p` on `F(D)`
  have hgF : ∀ z ∈ D, Function.invFunOn F D (F z) = z := fun z hz => hi.leftInvOn_invFunOn hz
  have hEo : IsOpen (F '' D) := LiZhongQC.isOpen_image_of_continuousOn_injOn hD hc hi
  have hgc : ContinuousOn (Function.invFunOn F D) (F '' D) :=
    (LiZhongQC.qcl_f_isHomeomorphOnto_of_injOn hD hc hi).2.2.2
  have hgi : InjOn (Function.invFunOn F D) (F '' D) := Function.invFunOn_injOn_image F D
  set H : ℂ → ℂ := fun ζ => Function.invFunOn F D ζ - p with hHdef
  have hHc : ContinuousOn H (F '' D) := hgc.sub continuousOn_const
  have hHi : InjOn H (F '' D) := fun u hu v hv h => hgi hu hv (sub_left_injective h)
  -- `H` is `K`-quasiconformal on `F(D ∖ {p})` (Theorems 7.2 and 7.1 of Li Zhong)
  have hT : LiZhongQC.IsKQC (fun ζ : ℂ => ζ - p) univ 1 := LiZhongQC.isKQC_one_of_conformal isOpen_univ
    ⟨(differentiable_id.sub_const p).differentiableOn, sub_left_injective.injOn, rfl⟩
  have hH0 := LiZhongQC.thm7_1_comp (LiZhongQC.thm7_2_inv hK) hT (subset_univ _)
  rw [mul_one] at hH0
  have hH : LiZhongQC.IsKQC H (F '' (D \ {p})) K := LiZhongQC.ad_isKQC_congr hH0 fun ζ hζ => by
    obtain ⟨z, hz, rfl⟩ := hζ
    show Function.invFunOn F D (F z) - p = Function.invFunOn F (D \ {p}) (F z) - p
    rw [hgF z hz.1, (hi.mono sdiff_subset).leftInvOn_invFunOn hz]
  -- the annulus `|F(y) - F(p)| < |ζ - F(p)| < |F(x) - F(p)|` and its image
  have hA := LiZhongQC.nf_g_isDoublyConnected_annulusAt (F p) ha hlt
  have hAcl : closure (toExt (LiZhongQC.annulusAt (F p) ‖F y - F p‖ ‖F x - F p‖)) ⊆ toExt (F '' (D \ {p})) := by
    refine (LiZhongQC.nf_e_closure_toExt_subset ((isCompact_closedBall (F p) ‖F x - F p‖).diff
      (Metric.isOpen_ball (x := F p) (ε := ‖F y - F p‖))) fun ζ hζ => ⟨?_, ?_⟩).trans (image_mono ?_)
    · rw [Metric.mem_closedBall, dist_eq_norm]
      exact hζ.2.le
    · rw [Metric.mem_ball, dist_eq_norm, not_lt]
      exact hζ.1.le
    · rintro ζ ⟨hζb, hζa⟩
      obtain ⟨z, hz, rfl⟩ := hball hζb
      refine ⟨z, ⟨hz, fun hzp => hζa ?_⟩, rfl⟩
      rw [mem_singleton_iff.1 hzp]
      exact Metric.mem_ball_self ha
  obtain ⟨hdc, hmod, -⟩ := LiZhongQC.thm7_4_dcModulus_quasi_invariance hH hA hAcl
  -- `H(A)` separates `0, y - p` from `x - p, ∞`
  have hsep := lv29m_sep hEo hHc hHi ha hlt hball hdc (u := F y) (v := F x) le_rfl rfl
  have hHp : H (F p) = 0 := by
    show Function.invFunOn F D (F p) - p = 0
    rw [hgF p hp, sub_self]
  have hHy : H (F y) = y - p := by
    show Function.invFunOn F D (F y) - p = y - p
    rw [hgF y hy]
  have hHx : H (F x) = x - p := by
    show Function.invFunOn F D (F x) - p = x - p
    rw [hgF x hx]
  rw [hHp, hHy, hHx] at hsep
  have hT5 := LiZhongQC.thm5_3_teichmuller_modulus_theorem (sub_ne_zero.2 hyp) (sub_ne_zero.2 hxp) hdc hsep
  -- `μ(√(|y - p|/(|y - p| + |x - p|))) ≤ μ(1/√2) = π/2`, since `|x - p| ≤ |y - p|`
  have hy0 : 0 < ‖y - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hyp)
  have hx0 : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp)
  have hmu : LiZhongQC.grotzschMu (Real.sqrt (‖y - p‖ / (‖y - p‖ + ‖x - p‖))) ≤ Real.pi / 2 := by
    rw [← LiZhongQC.eq5_21]
    have hq0 : 0 < ‖y - p‖ / (‖y - p‖ + ‖x - p‖) := by positivity
    have hq1 : ‖y - p‖ / (‖y - p‖ + ‖x - p‖) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hq2 : 1 / 2 ≤ ‖y - p‖ / (‖y - p‖ + ‖x - p‖) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hs2 : 1 / Real.sqrt 2 = Real.sqrt (1 / 2) := by
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    refine LiZhongQC.grotzschMu_strictAntiOn.antitoneOn ⟨by positivity, ?_⟩ ⟨Real.sqrt_pos.2 hq0, ?_⟩ ?_
    · rw [hs2, Real.sqrt_lt' one_pos]
      norm_num
    · rw [Real.sqrt_lt' one_pos]
      linarith
    · rw [hs2]
      exact Real.sqrt_le_sqrt hq2
  -- `log(b/a) = M(A) ≤ K M(H(A)) ≤ Kπ`
  have hmodA := LiZhongQC.nf_e_dcModulus_annulusAt (F p) ha hlt
  have hfin : ENNReal.ofReal (Real.log (‖F x - F p‖ / ‖F y - F p‖)) ≤ ENNReal.ofReal (K * Real.pi) := by
    rw [← hmodA]
    calc LiZhongQC.dcModulus (LiZhongQC.annulusAt (F p) ‖F y - F p‖ ‖F x - F p‖)
        ≤ ENNReal.ofReal K * LiZhongQC.dcModulus (H '' LiZhongQC.annulusAt (F p) ‖F y - F p‖ ‖F x - F p‖) :=
          hmod
      _ ≤ ENNReal.ofReal K *
          ENNReal.ofReal (2 * LiZhongQC.grotzschMu (Real.sqrt (‖y - p‖ / (‖y - p‖ + ‖x - p‖)))) := by
          gcongr
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal Real.pi := by
          gcongr
          linarith
      _ = ENNReal.ofReal (K * Real.pi) := (ENNReal.ofReal_mul (by linarith)).symm
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  have h := Real.exp_le_exp.2 hfin
  rw [Real.exp_log (div_pos (ha.trans hlt) ha), div_le_iff₀ ha, mul_comm K] at h
  exact h

/-- Helper (II §9.2). Let `F` be continuous and one-to-one on `|ζ| < ρ`, with `F(0) = 0`, and `K`-quasiconformal
off `0`. Then `limsup_{r → +0} max_α |F(re^{iα})| / min_α |F(re^{iα})| ≤ e^{πK}`: for small `r` the core estimate
`lv29m_core` applies to any two points of the circle `|ζ| = r`. -/
theorem lv29m_ev {F : ℂ → ℂ} {ρ K : ℝ} (hρ : 0 < ρ) (hc : ContinuousOn F (Metric.ball 0 ρ))
    (hi : InjOn F (Metric.ball 0 ρ)) (h0 : F 0 = 0) (hK : LiZhongQC.IsKQC F (Metric.ball 0 ρ \ {0}) K) :
    limsup (fun r : ℝ => (⨆ α : ℝ, ‖F ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) /
      ⨅ α : ℝ, ‖F ((r : ℂ) * exp ((α : ℂ) * I))‖ₑ) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.exp (Real.pi * K)) := by
  have h0m : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  -- a disc about `0 = F(0)` inside the (open) image of the disc
  have hU : IsOpen (F '' Metric.ball 0 ρ) :=
    LiZhongQC.isOpen_image_of_continuousOn_injOn Metric.isOpen_ball hc hi
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, h0m, h0⟩
  -- `|F| < δ/2` near `0`
  have hFc : ContinuousAt F 0 := hc.continuousAt (Metric.isOpen_ball.mem_nhds h0m)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hFc (δ / 2) (by positivity)
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη hρ)] with r hr
  have hr0 : 0 < r := hr.1
  have hpt : ∀ α : ℝ, ‖(r : ℂ) * exp ((α : ℂ) * I)‖ = r := fun α => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hmem : ∀ α : ℝ, (r : ℂ) * exp ((α : ℂ) * I) ∈ Metric.ball (0 : ℂ) ρ := fun α => by
    rw [mem_ball_zero_iff, hpt]
    exact hr.2.trans_le (min_le_right _ _)
  have hsmall : ∀ α : ℝ, ‖F ((r : ℂ) * exp ((α : ℂ) * I))‖ < δ / 2 := fun α => by
    have h := hηb (x := (r : ℂ) * exp ((α : ℂ) * I)) (by
      rw [dist_zero_right, hpt]
      exact hr.2.trans_le (min_le_left _ _))
    rwa [h0, dist_zero_right] at h
  -- Mori's estimate for any two points of the circle `|ζ| = r`
  have hpair : ∀ α β : ℝ, ‖F ((r : ℂ) * exp ((α : ℂ) * I))‖ ≤
      Real.exp (Real.pi * K) * ‖F ((r : ℂ) * exp ((β : ℂ) * I))‖ := by
    intro α β
    have hne : ∀ γ : ℝ, (r : ℂ) * exp ((γ : ℂ) * I) ≠ 0 := fun γ h => by
      have h' := hpt γ
      rw [h, norm_zero] at h'
      exact hr0.ne h'
    have hxy : ‖(r : ℂ) * exp ((α : ℂ) * I) - 0‖ ≤ ‖(r : ℂ) * exp ((β : ℂ) * I) - 0‖ := by
      rw [sub_zero, sub_zero, hpt, hpt]
    have hball : Metric.closedBall (F 0) ‖F ((r : ℂ) * exp ((α : ℂ) * I)) - F 0‖ ⊆ F '' Metric.ball 0 ρ := by
      rw [h0, sub_zero]
      intro ζ hζ
      apply hδb
      rw [Metric.mem_closedBall] at hζ
      rw [Metric.mem_ball]
      linarith [hsmall α]
    have h := lv29m_core Metric.isOpen_ball hc hi hK h0m (hmem α) (hmem β) (hne α) (hne β) hxy hball
    rwa [h0, sub_zero, sub_zero] at h
  -- hence `max ≤ e^{πK} min` on the circle
  have hE0 : ENNReal.ofReal (Real.exp (Real.pi * K)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  refine ENNReal.div_le_of_le_mul (iSup_le fun α => ?_)
  rw [ENNReal.mul_iInf_of_ne hE0 ENNReal.ofReal_ne_top]
  refine le_iInf fun β => ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (hpair α β)

/-- **Theorem 9.1** (Ch. II §9.2, Mori). For a `K`-quasiconformal mapping, `H` is bounded by a number depending only
on `K` (the proof gives `e^{πK}`).
Modelling: `∀ K, ∃ C, ∀ G w z, …`; the bound holds at every point of the domain of the mapping. -/
theorem thm2_9_1 (K : ℝ) :
    ∃ C : ℝ, ∀ (G : Set ExtPlane) (w : ExtPlane → ExtPlane) (z : ExtPlane), IsKQuasiconformal w G K → z ∈ G →
      circularDilatation w z ≤ ENNReal.ofReal C := by
  refine ⟨Real.exp (Real.pi * K), fun G w z hw hz => ?_⟩
  obtain ⟨ρ, hρ, hc, hi, hK⟩ := lv29m_chart hw hz
  exact lv29m_ev hρ hc hi (lv29_localRep_zero w z) hK

/-- **Formula (9.1)** (Ch. II §9.2, derived in the proof of Theorem 9.1 and cited by number at P2:1034). Let
`w : G → G′` be a `K`-quasiconformal mapping of domains of the finite plane, `z₀ ∈ G`, and `r > 0` so small that the
closed disc `|z - z₀| ≤ r` lies in `G` and the closed disc `|w - w(z₀)| ≤ m₁(r)` lies in `G′`, where
`m₁(r) = max_{|z - z₀| = r} |w(z) - w(z₀)|` and `m₂(r) = min_{|z - z₀| = r} |w(z) - w(z₀)|`. Then
`m₁(r)/m₂(r) ≤ e^{πK}`.
Modelling: the domains are finite (`∞ ∉ G`, `∞ ∉ w(G)`), as in the proof; the maximum and the minimum over the
compact circle are `⨆`/`⨅` of a continuous function; the quotient is multiplied out. -/
theorem eq2_9_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    (hG : extInf ∉ G) (hG' : extInf ∉ w '' G) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ G) {r : ℝ} (hr : 0 < r)
    (hD : toExt (Metric.closedBall z₀ r) ⊆ G)
    (hD' : toExt (Metric.closedBall (finiteMap w z₀)
      (⨆ z : Metric.sphere z₀ r, ‖finiteMap w z - finiteMap w z₀‖)) ⊆ w '' G) :
    (⨆ z : Metric.sphere z₀ r, ‖finiteMap w z - finiteMap w z₀‖) ≤
      Real.exp (Real.pi * K) * ⨅ z : Metric.sphere z₀ r, ‖finiteMap w z - finiteMap w z₀‖ := by
  -- `w` read on its finite core `D` is `K`-quasiconformal in Li Zhong's sense
  have hf : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} K :=
    lv13_isKQC_of_isKQuasiconformal hw
  set D : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} with hDdef
  have hDo : IsOpen D := hf.1
  have hfc : ContinuousOn (finiteMap w) D := hf.2.2.1.1
  have hfi : InjOn (finiteMap w) D := hf.2.2.1.2.1
  have hK : LiZhongQC.IsKQC (finiteMap w) (D \ {z₀}) K :=
    LiZhongQC.ac_t_isKQC_restrict hf (hDo.sdiff isClosed_singleton) sdiff_subset
  have hcl : Metric.closedBall z₀ r ⊆ D := fun x hx => by
    have hxG : (x : ExtPlane) ∈ G := hD (mem_image_of_mem _ hx)
    exact ⟨hxG, fun h => hG' (h ▸ mem_image_of_mem w hxG)⟩
  have hz₀D : z₀ ∈ D := ⟨hz₀, fun h => hG' (h ▸ mem_image_of_mem w hz₀)⟩
  have hsD : Metric.sphere z₀ r ⊆ D := Metric.sphere_subset_closedBall.trans hcl
  have hbdd : BddAbove (range fun z : Metric.sphere z₀ r => ‖finiteMap w z - finiteMap w z₀‖) := by
    have hcont : ContinuousOn (fun x => ‖finiteMap w x - finiteMap w z₀‖) (Metric.sphere z₀ r) :=
      ((hfc.mono hsD).sub continuousOn_const).norm
    have h := (isCompact_sphere z₀ r).bddAbove_image hcont
    rwa [image_eq_range] at h
  -- the closed disc of radius `m₁(r)` about `w(z₀)` lies in the image of the finite core
  have himg : Metric.closedBall (finiteMap w z₀) (⨆ z : Metric.sphere z₀ r, ‖finiteMap w z - finiteMap w z₀‖) ⊆
      finiteMap w '' D := fun u hu => by
    obtain ⟨q, hq, hqu⟩ := hD' (mem_image_of_mem _ hu)
    induction q using OnePoint.rec with
    | infty => exact absurd hq hG
    | coe x =>
      refine ⟨x, ⟨hq, by rw [hqu]; exact OnePoint.coe_ne_infty u⟩, ?_⟩
      show finiteValue (w x) = u
      rw [hqu]
      rfl
  -- Mori's estimate for any two points of the circle
  have key : ∀ x ∈ Metric.sphere z₀ r, ∀ y ∈ Metric.sphere z₀ r,
      ‖finiteMap w x - finiteMap w z₀‖ ≤ Real.exp (Real.pi * K) * ‖finiteMap w y - finiteMap w z₀‖ := by
    intro x hx y hy
    have hxr : ‖x - z₀‖ = r := by rw [← dist_eq_norm]; exact hx
    have hyr : ‖y - z₀‖ = r := by rw [← dist_eq_norm]; exact hy
    have hne : ∀ t : ℂ, ‖t - z₀‖ = r → t ≠ z₀ := fun t ht h => by
      rw [h, sub_self, norm_zero] at ht
      exact hr.ne ht
    exact lv29m_core hDo hfc hfi hK hz₀D (hsD hx) (hsD hy) (hne x hxr) (hne y hyr) (by rw [hxr, hyr])
      ((Metric.closedBall_subset_closedBall (le_ciSup hbdd (⟨x, hx⟩ : Metric.sphere z₀ r))).trans himg)
  have : Nonempty (Metric.sphere z₀ r) := (NormedSpace.sphere_nonempty.2 hr.le).to_subtype
  have hE := Real.exp_pos (Real.pi * K)
  refine ciSup_le fun x => ?_
  have h1 : ‖finiteMap w x - finiteMap w z₀‖ / Real.exp (Real.pi * K) ≤
      ⨅ y : Metric.sphere z₀ r, ‖finiteMap w y - finiteMap w z₀‖ :=
    le_ciInf fun y => (div_le_iff₀ hE).2 (by rw [mul_comm]; exact key x x.2 y y.2)
  rw [div_le_iff₀ hE, mul_comm] at h1
  exact h1

/-! ## §9.3 Lower bound for the circular dilatation -/

/-- **Theorem 9.2** (Ch. II §9.3, Lehto–Virtanen–Väisälä). For every `ε > 0` there exists a `K`-quasiconformal
mapping for which `H(z) ≥ λ(K) - ε` (9.2) at some point `z`.
Modelling: `K ≥ 1` (for `K < 1` there is no `K`-quasiconformal mapping); (9.2) is written `λ(K) ≤ H(z) + ε` in
`ℝ≥0∞`, which avoids a truncated subtraction. The proof gives a mapping of the whole plane and `z = 0`; the statement
does not require this. -/
theorem thm2_9_2 {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : Set ExtPlane) (w : ExtPlane → ExtPlane) (z : ExtPlane), IsKQuasiconformal w G K ∧ z ∈ G ∧
      ENNReal.ofReal (LiZhongQC.lambdaInv K) ≤ circularDilatation w z + ENNReal.ofReal ε := by
  sorry

/-! ## §9.4 Supremum of the circular dilatation -/

/-- **Theorem 9.3** (Ch. II §9.4, quoted from Väisälä and the authors, without proof). In the family `𝒲` of
`K`-quasiconformal mappings `w` we have `sup_{w ∈ 𝒲} H_w(z) = λ(K)`.
[OCR] The source prints `ω` for `w`.
Modelling: `K ≥ 1` (for `K < 1` the family is empty); for every point `z`, the supremum is over all
`K`-quasiconformal mappings of domains `G ∋ z` (the value does not depend on `z`: translations, and at `∞` the
substitution `z ↦ 1/z` of the definition, carry the family at one point onto the family at another). -/
theorem thm2_9_3 {K : ℝ} (hK : 1 ≤ K) (z : ExtPlane) :
    ⨆ (G : Set ExtPlane) (w : ExtPlane → ExtPlane) (_ : IsKQuasiconformal w G K) (_ : z ∈ G),
      circularDilatation w z = ENNReal.ofReal (LiZhongQC.lambdaInv K) := by
  sorry

end LehtoVirtanen1973
