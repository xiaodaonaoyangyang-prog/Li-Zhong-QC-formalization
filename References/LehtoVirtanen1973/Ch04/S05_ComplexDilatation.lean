import References.LehtoVirtanen1973.Ch04.S01_AnalyticProperties
import References.LehtoVirtanen1973.Ch04.S04_CircularDilatation

/-!
# Lehto–Virtanen, Chapter IV §5: Complex dilatation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. IV §5
(pp. 182–189; `full.md` P1:5679–5938).

Conventions (as in §1). A quasiconformal mapping `w : G → G′` is a sense-preserving homeomorphism of a domain `G` of
`ℂ̄` (`IsQuasiconformalMap`, `IsKQuasiconformal`), with `G′ = w(G)`. "Differentiable" refers to finite points with
finite values (I.9): `w` is differentiable at `z : ℂ` with `w(z) ≠ ∞` when its finite part `finiteMap w` is (real
Fréchet differentiability); there `w_z`, `w_{\bar z}` are `LiZhongQC.dz`, `LiZhongQC.dzbar` of `finiteMap w` and
`∂_α w` is `dirDeriv`. The complex dilatation `κ` is `complexDilatationLV` (§5.1). "Almost everywhere in `G`" refers to
the area measure of the finite part of `G` (III.1, footnote 32): `∀ᵐ z : ℂ ∂(volume.restrict (finitePart G))`; the
points `∞` and `w⁻¹(∞)` are null. "Measurable" is Lebesgue measurability (`AEStronglyMeasurable` for the restricted
area measure). The derivatives `w_z`, `w_{\bar z}` of a function which is only absolutely continuous on lines (§5.3)
are the book's expressions `(w_x ∓ i w_y)/2` in the partial derivatives, `LiZhongQC.genDz`, `LiZhongQC.genDzbar` of
`LiZhongQC.partialX`, `LiZhongQC.partialY` (as in III.6).

* Formula (5.1) (§5.1; cited at P1:5703) — exists: `LehtoVirtanen1973.dirDeriv_eq_dz_add_dzbar` (Ch. I §9.4,
  P1:1390: the same formula at a finite point of differentiability)
* Formula (5.2) (§5.1) — `eq4_5_2`
* Definition (complex dilatation `κ = w_{\bar z}/w_z`, (5.3), §5.1) — `complexDilatationLV`
* Definition (direction of maximum distortion `α_M = (1/2) arg κ`, §5.1) — omitted: not used later in the book
* Formula (5.4) (§5.1) — `eq4_5_4`
* Formula (5.5) (§5.1), restated as (5.11) (§5.3) — `eq4_5_5`
* Unlabelled (§5.1, P1:5725): a quasiconformal mapping whose complex dilatation vanishes almost everywhere is
  conformal — `conformal_of_complexDilatation_ae_eq_zero`
* Formula (5.6) (§5.2) — `eq4_5_6_i`, `eq4_5_6_ii`
* Formula (5.7) (§5.2) — `eq4_5_7`
* Uniqueness theorem (§5.2) — `uniqueness_theorem`
* Formula (5.8) (§5.2) — omitted: the special case of (5.6) for a conformal mapping w, not cited later in the book
* Formula (5.9) (§5.2) — `eq4_5_9`
* Definition (Beltrami equation (5.10), §5.3) — omitted: terminology; the equation is written out in the two
  definitions of solutions below
* Definition (generalized solution, generalized `L^p`-solution of (5.10), §5.3) — `IsGeneralizedSolution`,
  `IsGeneralizedLpSolution`
* Theorem 5.1 (§5.3) — `thm4_5_1_i`, `thm4_5_1_ii`
* Definition (good approximation, §5.4) — `IsGoodApproximation`
* Definition (weak convergence in `G`, (5.12), §5.5) — `ConvergesWeaklyOnRectangles`
* Lemma 5.1 (§5.5, Bers) — `lemma4_5_1`
* Theorem 5.2 (§5.6, Bers) — `thm4_5_2`

Not stated (inventory: omitted): that `κ` is a Borel function (P1:5701; recalled at P1:5943, 5965 in V.1;
immediate: a quotient of derivatives of a continuous function; the measurability that V.1 uses is the second
conjunct of `thm4_5_1_i`); that the complex dilatation of a conformal mapping vanishes identically (P1:5725, since
`κ = 0` is equivalent to `D = 1`); that changing `κ` on a null set does not affect the generalized solutions (P1:5771,
immediate from the definitions); the remarks on condition 2 of the good approximation (P1:5805–5811) and the example
of §5.4 (P1:5813–5831) of mappings `wₙ → z` with `|κₙ| = 1 − ε` almost everywhere. The numbered formulas
(5.13)–(5.19) are steps of the proof of Theorem 5.2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt closedRect openRect partialX partialY genDz genDzbar)
open References (IsDomainExt finitePart)

/-! ## §5.1 Definition of the complex dilatation -/

/-- **Formula (5.2)** (Ch. IV §5.1). Let `w : G → G′` be `K`-quasiconformal and `z ∈ G` a finite point at which `w`
is differentiable. Then the dilatation condition (1.5), `max_α |∂_α w(z)| ≤ K min_α |∂_α w(z)|`, can be written in the
form `|w_{\bar z}(z)| ≤ (K - 1)/(K + 1) |w_z(z)|` (5.2).
Modelling: `w(z)` finite (the convention of I.9); the second inequality is multiplied by `K + 1 > 0`. -/
theorem eq4_5_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) {z : ℂ}
    (hz : (z : ExtPlane) ∈ G) (hfin : w z ≠ extInf) (hd : DifferentiableAt ℝ (finiteMap w) z) :
    (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) ≤ K * (⨅ α : ℝ, ‖dirDeriv (finiteMap w) z α‖) ↔
      (K + 1) * ‖LiZhongQC.dzbar (finiteMap w) z‖ ≤ (K - 1) * ‖LiZhongQC.dz (finiteMap w) z‖ := by
  -- pointwise `|w_{\bar z}| ≤ |w_z|` (sense-preservation, I.9.4), then (9.5)
  have h := sensePreserving_jacobian_nonneg hw.1 hw.2.1 hz hfin hd
  obtain ⟨hsup, hinf⟩ := eq1_9_5 hd h.2
  rw [hsup, hinf]
  constructor <;> intro h' <;> nlinarith [h']

/-- **Definition** (complex dilatation, Ch. IV §5.1, (5.3)). At a regular point `z` of `w` (`z` and `w(z)` finite)
`w_z(z) ≠ 0`, and the quotient `κ(z) = w_{\bar z}(z)/w_z(z)` is the complex dilatation of `w`; for a quasiconformal
mapping it exists almost everywhere in `G` (Theorem 1.4).
Modelling: `LiZhongQC.complexDilatation` (the quotient `dzbar/dz` of the real derivative) of the local representation
`localRep w z` at `0`, as Ch. I's `dilQuot`; at a finite point with a finite value `localRep w z` is
`ζ ↦ w(z + ζ) - w(z)` near `0`, so this is `w_{\bar z}(z)/w_z(z)`. Junk: the value where `w` is not differentiable
(`fderiv = 0`, so `0/0 = 0`), and the chart values at `z = ∞` and where `w(z) = ∞`, at which the book leaves `κ`
undefined. For a quasiconformal mapping these points form a null set (Theorem 1.4), and every statement uses `κ`
almost everywhere or at finite regular points with finite values. -/
def complexDilatationLV (w : ExtPlane → ExtPlane) (z : ExtPlane) : ℂ :=
  LiZhongQC.complexDilatation (localRep w z) 0

/-- Helper (Tier 3, finite-chart bridge). At a finite point `z` at which `w` is continuous and finite, the complex
dilatation `κ(z)` is Li Zhong's `complexDilatation` `w_{\bar z}/w_z` of `finiteMap w` at `z`. -/
theorem lv45_complexDilatationLV_eq {w : ExtPlane → ExtPlane} {z : ℂ} (hc : ContinuousAt w z)
    (hfin : w z ≠ extInf) : complexDilatationLV w z = LiZhongQC.complexDilatation (finiteMap w) z := by
  simp only [complexDilatationLV, LiZhongQC.complexDilatation, LiZhongQC.dz, LiZhongQC.dzbar,
    (lv41_chart hc hfin).2.1]

/-- Helper (Tier 3). At a finite regular point `z` with `w(z) ≠ ∞` of a quasiconformal `w`: `z` lies in the finite
core, `finiteMap w` is differentiable at `z` with `|w_{\bar z}| < |w_z|` (sense-preservation and `J ≠ 0`), and
`D(z) = (|w_z| + |w_{\bar z}|)/(|w_z| - |w_{\bar z}|)`, `|κ(z)| = |w_{\bar z}|/|w_z|`. -/
theorem lv45_regular {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z : ℂ}
    (hz : IsRegularPointOf w G z) (hfin : w z ≠ extInf) :
    z ∈ finiteCore w G ∧ DifferentiableAt ℝ (finiteMap w) z ∧
      ‖LiZhongQC.dzbar (finiteMap w) z‖ < ‖LiZhongQC.dz (finiteMap w) z‖ ∧
      dilQuot w z = (‖LiZhongQC.dz (finiteMap w) z‖ + ‖LiZhongQC.dzbar (finiteMap w) z‖) /
        (‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖) ∧
      ‖complexDilatationLV w z‖ = ‖LiZhongQC.dzbar (finiteMap w) z‖ / ‖LiZhongQC.dz (finiteMap w) z‖ := by
  obtain ⟨hint, hc, hd, hJ⟩ := hz
  obtain ⟨hdiff, -, hD, hJe⟩ := lv41_chart hc hfin
  have hzG : (z : ExtPlane) ∈ G := interior_subset hint
  have hdf : DifferentiableAt ℝ (finiteMap w) z := hdiff.1 hd
  have hsp := sensePreserving_jacobian_nonneg hw.1 hw.2.1 hzG hfin hdf
  -- `J ≠ 0` and `|w_{\bar z}| ≤ |w_z|` give `|w_{\bar z}| < |w_z|`
  have hlt : ‖LiZhongQC.dzbar (finiteMap w) z‖ < ‖LiZhongQC.dz (finiteMap w) z‖ := by
    rcases hsp.2.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hJ
      rw [hJe, LiZhongQC.det_fderiv_eq_jacobian hdf, LiZhongQC.jacobian, h]
      ring
  obtain ⟨hsup, hinf⟩ := eq1_9_5 hdf hsp.2
  refine ⟨⟨hzG, hfin⟩, hdf, hlt, ?_, ?_⟩
  · rw [hD, dilQuotient, hsup, hinf]
  · rw [lv45_complexDilatationLV_eq hc hfin, LiZhongQC.complexDilatation, norm_div]

/-- **Formula (5.4)** (Ch. IV §5.1). At every finite regular point `z` of the quasiconformal mapping `w` with
`w(z) ≠ ∞`, the dilatation quotient is `D(z) = (1 + |κ(z)|)/(1 - |κ(z)|)` (5.4).
Modelling: `D` is Ch. I's `dilQuot`, the book's quotient `max_α |∂_α w| / min_α |∂_α w|`, so this is a genuine
identity; at a regular point of a sense-preserving mapping `|κ(z)| < 1`, so the denominator does not vanish. -/
theorem eq4_5_4 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z : ℂ}
    (hz : IsRegularPointOf w G z) (hfin : w z ≠ extInf) :
    dilQuot w z = (1 + ‖complexDilatationLV w z‖) / (1 - ‖complexDilatationLV w z‖) := by
  obtain ⟨-, -, hlt, hD, hκ⟩ := lv45_regular hw hz hfin
  have ha : ‖LiZhongQC.dz (finiteMap w) z‖ ≠ 0 := ((norm_nonneg _).trans_lt hlt).ne'
  rw [hD, hκ, one_add_div ha, one_sub_div ha, div_div_div_cancel_right₀ ha]

/-- **Formula (5.5)** (Ch. IV §5.1), restated as **(5.11)** (§5.3). For a `K`-quasiconformal mapping `w`,
`|κ(z)| = (D(z) - 1)/(D(z) + 1) ≤ (K - 1)/(K + 1)` at every finite regular point `z` with `w(z) ≠ ∞`; that is, (5.11)
holds at every point where `κ(z)` is defined.
Modelling: the equality and the inequality are multiplied by `D(z) + 1 > 0` and `K + 1 > 0`. -/
theorem eq4_5_5 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) {z : ℂ}
    (hz : IsRegularPointOf w G z) (hfin : w z ≠ extInf) :
    ‖complexDilatationLV w z‖ * (dilQuot w z + 1) = dilQuot w z - 1 ∧
      (K + 1) * ‖complexDilatationLV w z‖ ≤ K - 1 := by
  have hq : IsQuasiconformalMap w G := ⟨hw.1, hw.2.1, lt_of_le_of_lt hw.2.2 ENNReal.ofReal_lt_top⟩
  obtain ⟨hzD, hdf, hlt, hD, hκ⟩ := lv45_regular hq hz hfin
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := lv13_isKQC_of_isKQuasiconformal hw
  -- the dilatation condition (1.5) at this point of differentiability
  have hdil := LiZhongQC.ac_t_dilatation_of_differentiableAt hk hzD hdf
  have ha : 0 < ‖LiZhongQC.dz (finiteMap w) z‖ := (norm_nonneg _).trans_lt hlt
  have hab : 0 < ‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖ := by linarith
  rw [hD, hκ]
  constructor
  · field_simp
    ring
  · rw [← mul_div_assoc, div_le_iff₀ ha]
    nlinarith [hdil]

/-- **Unlabelled** (Ch. IV §5.1, P1:5725; cited in V.1.1, P1:5965). If the complex dilatation of a quasiconformal
mapping `w : G → G′` vanishes almost everywhere in `G`, then `w` is conformal (it is `1`-quasiconformal by the
Analytic definition, and conformal by Theorem I.5.1). -/
theorem conformal_of_complexDilatation_ae_eq_zero {w : ExtPlane → ExtPlane} {G : Set ExtPlane}
    (hw : IsQuasiconformalMap w G)
    (hκ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w z = 0) :
    IsConformalMap w G := by
  obtain ⟨K, hk⟩ := lv41_isKQC hw
  obtain ⟨hG, hsp, -⟩ := hw
  have hD : IsOpen (finiteCore w G) := hk.1
  -- `κ = 0` a.e. gives `w_{\bar z} = 0` a.e. in the finite core (where `w_z = 0`, by (1.5))
  have hae : ∀ᵐ z ∂(volume.restrict (finiteCore w G)),
      ‖LiZhongQC.dz (finiteMap w) z‖ + ‖LiZhongQC.dzbar (finiteMap w) z‖ ≤
        1 * (‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖) := by
    rw [lv41_restrict_eq hsp.1.2.1] at hκ
    filter_upwards [hκ, ae_restrict_mem hD.measurableSet, LiZhongQC.thm9_4_dilatation_ae hk] with z h0 hz hdil
    rw [lv45_complexDilatationLV_eq (hsp.1.1.continuousAt (hG.1.mem_nhds hz.1)) hz.2,
      LiZhongQC.complexDilatation, div_eq_zero_iff] at h0
    have hb : LiZhongQC.dzbar (finiteMap w) z = 0 := by
      rcases h0 with h | h
      · exact h
      · rw [h, norm_zero] at hdil
        have hK : 1 ≤ K := hk.2.1
        exact norm_eq_zero.1 (by nlinarith [norm_nonneg (LiZhongQC.dzbar (finiteMap w) z)])
    rw [hb, norm_zero]
    linarith [norm_nonneg (LiZhongQC.dz (finiteMap w) z)]
  -- so `finiteMap w` is `1`-quasiconformal, hence conformal, in the finite core
  have hk1 : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) 1 :=
    (LiZhongQC.thm10_1_isKQC_iff hD le_rfl hk.2.2.1).2 ⟨LiZhongQC.thm9_1_isACL hk, hae⟩
  have hconf := LiZhongQC.thm7_3_one_qc_conformal hk1
  exact lv15_isConformalMap_of_differentiableAt hG hsp.1.1 hsp.1.2.1 Set.finite_empty fun ζ hζ hfin _ =>
    (hconf.1 ζ ⟨hζ, hfin⟩).differentiableAt (hD.mem_nhds ⟨hζ, hfin⟩)

/-! ## §5.2 Transformation formulae for the complex dilatation -/

/-- Helper (R1). For `a ≠ 0`, `e^{-2i arg a} = ā/a`; and for every `b`, `(b/a) e^{-2i arg b} = \overline{(b/a)} · ā/a`
(both sides vanish for `b = 0`). -/
theorem lv45_exp_arg {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    Complex.exp (-(2 * (a.arg : ℂ) * I)) = conj a / a ∧
      b / a * Complex.exp (-(2 * (b.arg : ℂ) * I)) = conj (b / a) * (conj a / a) := by
  have key : ∀ c : ℂ, c ≠ 0 → Complex.exp (-(2 * (c.arg : ℂ) * I)) = conj c / c := fun c hc => by
    have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
    have hc' := Complex.norm_mul_exp_arg_mul_I c
    conv_rhs => rw [← hc']
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_div_mul_left _ _ hn, ← Complex.exp_sub]
    congr 1
    ring
  refine ⟨key a ha, ?_⟩
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hca : conj a ≠ 0 := (map_ne_zero _).2 ha
    rw [key b hb, map_div₀]
    field_simp

/-- **Formula (5.6)** (Ch. IV §5.2), at a point. Let `w : G → G′` be quasiconformal and `f` quasiconformal in `G′`.
If `z` and `w(z)` are finite regular points of `w` and of `f`, respectively, and `f(w(z))` is finite, then
`κ_{f∘w}(z) = (κ_w(z) + κ_f(w(z)) e^{-2i arg w_z(z)}) / (1 + κ_w(z) κ_f(w(z)) e^{-2i arg w_{\bar z}(z)})` (5.6).
Modelling: stated as printed (page image, page_idx 188). [OCR] The OCR'd text reads `arg w_z(z)` in the exponent of the
denominator; the book prints `arg w_{\bar z}(z)`. Equivalently `κ_w e^{-2i arg w_{\bar z}} = conj(κ_w) e^{-2i arg w_z}`
(both are `conj(w_{\bar z})/w_z`); where `w_{\bar z}(z) = 0` the junk `arg 0 = 0` is harmless, since `κ_w(z) = 0` there.
At regular points of sense-preserving mappings `w_z(z) ≠ 0` and `|κ_w(z)|, |κ_f(w(z))| < 1`, so the denominator does not
vanish. -/
theorem eq4_5_6_i {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hf : IsQuasiconformalMap f (w '' G)) {z : ℂ} (hz : IsRegularPointOf w G z) (hwz : w z ≠ extInf)
    (hfz : IsRegularPointOf f (w '' G) (w z)) (hfwz : f (w z) ≠ extInf) :
    complexDilatationLV (f ∘ w) z =
      (complexDilatationLV w z +
          complexDilatationLV f (w z) * Complex.exp (-(2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I))) /
        (1 + complexDilatationLV w z * complexDilatationLV f (w z) *
          Complex.exp (-(2 * ((LiZhongQC.dzbar (finiteMap w) z).arg : ℂ) * I))) := by
  -- the finite charts at `z` and at `w z`
  obtain ⟨-, hdw, hltw, -, -⟩ := lv45_regular hw hz hwz
  have hcw : ContinuousAt w z := hz.2.1
  obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.1 hwz
  have hgz : finiteMap w z = ζ := by
    show finiteValue (w z) = ζ
    rw [← hζ]
    rfl
  have hcfw : ContinuousAt (f ∘ w) z := ContinuousAt.comp_of_eq hfz.2.1 hcw rfl
  have hfwz' : (f ∘ w) z ≠ extInf := hfwz
  rw [← hζ] at hfz hfwz
  obtain ⟨-, hdf, hltf, -, -⟩ := lv45_regular hf hfz hfwz
  have hcf : ContinuousAt f (ζ : ExtPlane) := hfz.2.1
  -- the three complex dilatations are Li Zhong's ones of the finite parts
  rw [lv45_complexDilatationLV_eq hcw hwz, ← hζ, lv45_complexDilatationLV_eq hcf hfwz,
    lv45_complexDilatationLV_eq hcfw hfwz']
  have hev : finiteMap (f ∘ w) =ᶠ[𝓝 z] finiteMap f ∘ finiteMap w := by
    have h1 : ∀ᶠ z' : ℂ in 𝓝 z, w z' ≠ extInf :=
      (hcw.comp OnePoint.continuous_coe.continuousAt).eventually_ne hwz
    filter_upwards [h1] with z' hz'
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.1 hz'
    show finiteValue (f (w z')) = finiteValue (f ((finiteValue (w z') : ℂ) : ExtPlane))
    rw [← hv]
    rfl
  have hμ : LiZhongQC.complexDilatation (finiteMap (f ∘ w)) z =
      LiZhongQC.complexDilatation (finiteMap f ∘ finiteMap w) z := by
    simp only [LiZhongQC.complexDilatation, LiZhongQC.dz, LiZhongQC.dzbar, hev.fderiv_eq]
  -- Li Zhong's composition formula (6.8)
  have ha : LiZhongQC.dz (finiteMap w) z ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt hltw)
  have hA : LiZhongQC.dz (finiteMap f) ζ ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt hltf)
  have hμw : ‖LiZhongQC.complexDilatation (finiteMap w) z‖ < 1 := by
    rw [LiZhongQC.complexDilatation, norm_div, div_lt_one (norm_pos_iff.2 ha)]
    exact hltw
  have hμf : ‖LiZhongQC.complexDilatation (finiteMap f) ζ‖ < 1 := by
    rw [LiZhongQC.complexDilatation, norm_div, div_lt_one (norm_pos_iff.2 hA)]
    exact hltf
  have hdf' : DifferentiableAt ℝ (finiteMap f) (finiteMap w z) := by rw [hgz]; exact hdf
  have h68 := LiZhongQC.eq6_8_complexDilatation_comp hdw hdf' ha (by rw [hgz]; exact hA) hμw
    (by rw [hgz]; exact hμf)
  rw [hgz] at h68
  rw [hμ, h68, (lv45_exp_arg ha (LiZhongQC.dzbar (finiteMap w) z)).1]
  -- the denominators: `μ_w μ_f e^{-2i arg w_{\bar z}} = \bar μ_w μ_f ā/a`
  have h2 := (lv45_exp_arg ha (LiZhongQC.dzbar (finiteMap w) z)).2
  have hden : LiZhongQC.complexDilatation (finiteMap w) z * LiZhongQC.complexDilatation (finiteMap f) ζ *
        Complex.exp (-(2 * ((LiZhongQC.dzbar (finiteMap w) z).arg : ℂ) * I)) =
      conj (LiZhongQC.complexDilatation (finiteMap w) z) * LiZhongQC.complexDilatation (finiteMap f) ζ *
        (conj (LiZhongQC.dz (finiteMap w) z) / LiZhongQC.dz (finiteMap w) z) := by
    unfold LiZhongQC.complexDilatation
    linear_combination (LiZhongQC.dzbar (finiteMap f) ζ / LiZhongQC.dz (finiteMap f) ζ) * h2
  rw [hden]

/-- Helper (WP6, W6-1). Almost every finite point `z` of the domain of a quasiconformal mapping `w` is a regular point
of `w` with `w(z) ≠ ∞`: on the finite core the finite part is differentiable with positive Jacobian almost everywhere
(Li Zhong's Theorems 9.3 and 9.6), and the chart representation is the finite part (`lv41_chart`). -/
theorem lv45_ae_regular {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) :
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), IsRegularPointOf w G z ∧ w z ≠ extInf := by
  obtain ⟨K, hk⟩ := lv41_isKQC hw
  obtain ⟨hG, hsp, -⟩ := hw
  rw [lv41_restrict_eq hsp.1.2.1]
  filter_upwards [ae_restrict_mem hk.1.measurableSet, LiZhongQC.thm9_3_differentiable_ae hk,
    LiZhongQC.thm9_6_cor2_jacobian_pos hk] with z hz hd hJ
  have hc : ContinuousAt w z := hsp.1.1.continuousAt (hG.1.mem_nhds hz.1)
  obtain ⟨hdiff, -, -, hJe⟩ := lv41_chart hc hz.2
  refine ⟨⟨by rw [hG.1.interior_eq]; exact hz.1, hc, hdiff.2 hd, ?_⟩, hz.2⟩
  rw [hJe, LiZhongQC.det_fderiv_eq_jacobian hd]
  exact hJ.ne'

/-- Helper (WP6, W6-1). For quasiconformal mappings `w : G → G′` and `f` of `G′`, almost every finite point `z` of `G`
is a regular point of `w` with `w(z)` finite, and `w(z)` is a regular point of `f` with `f(w(z))` finite: the points
of `G′` where this fails for `f` form a null set (`lv45_ae_regular`), and so does their preimage under `w`, the image
under the quasiconformal `w⁻¹` (`kqc_inv`, `qc_image_null`). -/
theorem lv45_ae_comp_regular {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hf : IsQuasiconformalMap f (w '' G)) :
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), IsRegularPointOf w G z ∧ w z ≠ extInf ∧
      IsRegularPointOf f (w '' G) (w z) ∧ f (w z) ≠ extInf := by
  obtain ⟨hG, hsp, hlt⟩ := hw
  have hGo' : IsOpen (w '' G) := invariance_of_open_sets hG.1 hsp.1.1 hsp.1.2.1
  -- the bad points of `f` in `w(G)`
  set B : Set ExtPlane := {q ∈ w '' G | ¬ (IsRegularPointOf f (w '' G) q ∧ f q ≠ extInf)} with hB
  have hBnull : volume (finitePart B) = 0 := by
    have h := lv45_ae_regular hf
    have hm : MeasurableSet (finitePart (w '' G)) := (hGo'.preimage OnePoint.continuous_coe).measurableSet
    rw [ae_restrict_iff' hm, ae_iff] at h
    refine measure_mono_null (fun q hq => ?_) h
    exact fun h' => hq.2 (h' hq.1)
  -- their preimage under `w` is the image under `w⁻¹`, a quasiconformal mapping of `w(G)`
  have hkw : IsKQuasiconformal w G (maxDilatationK w G).toReal :=
    ⟨hG, hsp, (ENNReal.ofReal_toReal hlt.ne).ge⟩
  have hinv := kqc_inv hkw
  have hinvq : IsQuasiconformalMap (Function.invFunOn w G) (w '' G) :=
    ⟨hinv.1, hinv.2.1, lt_of_le_of_lt hinv.2.2 ENNReal.ofReal_lt_top⟩
  have hPnull := qc_image_null hinvq (fun q hq => hq.1) hBnull
  have hP : ∀ᵐ z : ℂ ∂volume, ¬ ((z : ExtPlane) ∈ G ∧ w z ∈ B) := by
    refine measure_eq_zero_iff_ae_notMem.1 (measure_mono_null (fun z hz => ?_) hPnull)
    exact ⟨w z, hz.2, hsp.1.2.1.leftInvOn_invFunOn hz.1⟩
  have hw' : IsQuasiconformalMap w G := ⟨hG, hsp, hlt⟩
  filter_upwards [lv45_ae_regular hw', ae_restrict_of_ae hP,
    ae_restrict_mem (hG.1.preimage OnePoint.continuous_coe).measurableSet] with z hz hnP hzG
  refine ⟨hz.1, hz.2, ?_⟩
  by_contra hbad
  exact hnP ⟨hzG, mem_image_of_mem w hzG, hbad⟩

/-- **Formula (5.6)** (Ch. IV §5.2), almost everywhere. Let `w : G → G′` be quasiconformal and `f` quasiconformal in
`G′`. Then (5.6) holds almost everywhere in `G`.
Modelling: as printed, as in `eq4_5_6_i` (the exponent of the denominator has `arg w_{\bar z}(z)`; [OCR]). -/
theorem eq4_5_6_ii {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hf : IsQuasiconformalMap f (w '' G)) :
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
      complexDilatationLV (f ∘ w) z =
        (complexDilatationLV w z +
            complexDilatationLV f (w z) * Complex.exp (-(2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I))) /
          (1 + complexDilatationLV w z * complexDilatationLV f (w z) *
            Complex.exp (-(2 * ((LiZhongQC.dzbar (finiteMap w) z).arg : ℂ) * I))) := by
  filter_upwards [lv45_ae_comp_regular hw hf] with z h
  exact eq4_5_6_i hw hf h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **Formula (5.7)** (Ch. IV §5.2). Let `w : G → G′` be quasiconformal and `f` quasiconformal in `G′`. Then `f` is
conformal if and only if `κ_{f∘w}(z) = κ_w(z)` (5.7) almost everywhere in `G`.
Modelling: the hypothesis that `f` is quasiconformal is kept; by footnote 45 the conformality of `f` follows from
(5.7) only under this assumption. -/
theorem eq4_5_7 {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hf : IsQuasiconformalMap f (w '' G)) :
    IsConformalMap f (w '' G) ↔
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV (f ∘ w) z = complexDilatationLV w z := by
  constructor
  · -- `κ_f = 0` on `w(G)`, so (5.6) reduces to (5.7)
    intro hconf
    have hκf : ∀ q ∈ w '' G, complexDilatationLV f q = 0 := fun q hq => by
      unfold complexDilatationLV LiZhongQC.complexDilatation
      rw [(LiZhongQC.cauchyRiemann_iff.1 (hconf.2.2.2 q hq)).2, zero_div]
    filter_upwards [eq4_5_6_ii hw hf, lv45_ae_comp_regular hw hf] with z h hz
    rw [h, hκf _ (mem_image_of_mem w (interior_subset hz.1.1))]
    simp
  · -- (5.6) with `κ_{f∘w} = κ_w` forces `κ_f(w(z)) = 0` (`|κ_w|, |κ_f| < 1`), almost everywhere in `w(G)`
    intro hκ
    have hz0 : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV f (w z) = 0 := by
      filter_upwards [hκ, eq4_5_6_ii hw hf, lv45_ae_comp_regular hw hf] with z h1 h2 hz
      obtain ⟨hrw, hwz, hrf, hfwz⟩ := hz
      obtain ⟨-, -, -, -, hnw⟩ := lv45_regular hw hrw hwz
      obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.1 hwz
      rw [← hζ] at hrf hfwz h2
      obtain ⟨-, -, hltf, -, hnf⟩ := lv45_regular hf hrf hfwz
      obtain ⟨-, -, hltw, -, -⟩ := lv45_regular hw hrw hwz
      rw [← hζ]
      set a := complexDilatationLV w z with ha
      set b := complexDilatationLV f (ζ : ExtPlane) with hb
      set e₁ := Complex.exp (-(2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I)) with he₁
      set e₂ := Complex.exp (-(2 * ((LiZhongQC.dzbar (finiteMap w) z).arg : ℂ) * I)) with he₂
      have hn₁ : ‖e₁‖ = 1 := by
        rw [he₁, Complex.norm_exp]
        simp
      have hn₂ : ‖e₂‖ = 1 := by
        rw [he₂, Complex.norm_exp]
        simp
      have hna : ‖a‖ < 1 := by
        rw [hnw, div_lt_one ((norm_nonneg _).trans_lt hltw)]
        exact hltw
      have hnb : ‖b‖ < 1 := by
        rw [hnf, div_lt_one ((norm_nonneg _).trans_lt hltf)]
        exact hltf
      have hden : 1 + a * b * e₂ ≠ 0 := by
        intro h0
        have h' : ‖a * b * e₂‖ = 1 := by
          rw [show a * b * e₂ = -1 by linear_combination h0, norm_neg, norm_one]
        rw [norm_mul, norm_mul, hn₂, mul_one] at h'
        nlinarith [norm_nonneg a, norm_nonneg b]
      rw [h2, div_eq_iff hden] at h1
      have hfac : b * (e₁ - a * a * e₂) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 hfac with h | h
      · exact h
      · exfalso
        have h' : ‖a * a * e₂‖ = 1 := by rw [show a * a * e₂ = e₁ by linear_combination -h, hn₁]
        rw [norm_mul, norm_mul, hn₂, mul_one] at h'
        nlinarith [norm_nonneg a]
    -- transport to `w(G)` by the quasiconformal `w` (null sets go to null sets)
    refine conformal_of_complexDilatation_ae_eq_zero hf ?_
    have hGo' : IsOpen (w '' G) := invariance_of_open_sets hw.1.1 hw.2.1.1.1 hw.2.1.1.2.1
    have hm : MeasurableSet (finitePart G) := (hw.1.1.preimage OnePoint.continuous_coe).measurableSet
    have hm' : MeasurableSet (finitePart (w '' G)) := (hGo'.preimage OnePoint.continuous_coe).measurableSet
    rw [ae_restrict_iff' hm, ae_iff] at hz0
    rw [ae_restrict_iff' hm', ae_iff]
    have hsub : finitePart {z ∈ G | complexDilatationLV f (w z) ≠ 0} ⊆
        {a : ℂ | ¬(a ∈ finitePart G → complexDilatationLV f (w a) = 0)} := fun z hz h => hz.2 (h hz.1)
    have hnull := qc_image_null hw (A := {z ∈ G | complexDilatationLV f (w z) ≠ 0}) (fun z hz => hz.1)
      (measure_mono_null hsub hz0)
    refine measure_mono_null (fun ζ hζ => ?_) hnull
    obtain ⟨⟨z, hzG, hzζ⟩, hne⟩ := not_imp.1 hζ
    exact ⟨z, ⟨hzG, by rw [hzζ]; exact hne⟩, hzζ⟩

/-- Helper (D-II, uniqueness theorem). For quasiconformal mappings `w`, `w₁` of `G` with equal complex dilatations
almost everywhere, on the common finite core `D₀ = (G − {∞} − {w⁻¹(∞)}) ∩ (G − {∞} − {w₁⁻¹(∞)})` the finite part of
`w₁` is `φ ∘ finiteMap w` with `φ` complex differentiable on the open set `finiteMap w (D₀)` (Li Zhong's similarity
principle, `LiZhongQC.same_dilatation_conformal`). -/
theorem lv45_same_dilatation {w w₁ : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hw₁ : IsQuasiconformalMap w₁ G)
    (hκ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w₁ z = complexDilatationLV w z) :
    ∃ φ : ℂ → ℂ, IsOpen (finiteMap w '' (finiteCore w G ∩ finiteCore w₁ G)) ∧
      DifferentiableOn ℂ φ (finiteMap w '' (finiteCore w G ∩ finiteCore w₁ G)) ∧
        ∀ z ∈ finiteCore w G ∩ finiteCore w₁ G, finiteMap w₁ z = φ (finiteMap w z) := by
  obtain ⟨K, hk⟩ := lv41_isKQC hw
  obtain ⟨K₁, hk₁⟩ := lv41_isKQC hw₁
  obtain ⟨hG, hsp, -⟩ := hw
  obtain ⟨-, hsp₁, -⟩ := hw₁
  have hD₀o : IsOpen (finiteCore w G ∩ finiteCore w₁ G) := hk.1.inter hk₁.1
  have hkD := LiZhongQC.ac_t_isKQC_restrict hk hD₀o inter_subset_left
  have hk₁D := LiZhongQC.ac_t_isKQC_restrict hk₁ hD₀o inter_subset_right
  obtain ⟨hμ, hsol⟩ := LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hkD
  obtain ⟨-, hsol₁⟩ := LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hk₁D
  -- the two complex dilatations agree almost everywhere in the common finite core
  have hμeq : ∀ᵐ z ∂(volume.restrict (finiteCore w G ∩ finiteCore w₁ G)),
      LiZhongQC.complexDilatation (finiteMap w₁) z = LiZhongQC.complexDilatation (finiteMap w) z := by
    rw [lv41_restrict_eq hsp.1.2.1] at hκ
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hκ,
      ae_restrict_mem hD₀o.measurableSet] with z hz hzD
    rwa [lv45_complexDilatationLV_eq (hsp.1.1.continuousAt (hG.1.mem_nhds hzD.1.1)) hzD.1.2,
      lv45_complexDilatationLV_eq (hsp₁.1.1.continuousAt (hG.1.mem_nhds hzD.2.1)) hzD.2.2] at hz
  have hsol₁' : LiZhongQC.IsGenHomeoSolution (finiteMap w₁) (LiZhongQC.complexDilatation (finiteMap w))
      (finiteCore w G ∩ finiteCore w₁ G) 2 := by
    obtain ⟨hh, gx, gy, hgp, hbel⟩ := hsol₁
    refine ⟨hh, gx, gy, hgp, ?_⟩
    filter_upwards [hbel, hμeq] with z h1 h2
    rw [h1, h2]
  have hk01 : (K - 1) / (K + 1) < 1 := by
    have hK : 1 ≤ K := hk.2.1
    rw [div_lt_one (by linarith)]
    linarith
  -- Li Zhong's similarity principle
  obtain ⟨φ, hφ, hφeq⟩ := LiZhongQC.same_dilatation_conformal hD₀o hk01 hμ hsol hsol₁'
  refine ⟨φ, ?_, hφ.1, hφeq⟩
  exact LiZhongQC.isOpen_image_of_continuousOn_injOn hD₀o (hk.2.2.1.1.mono inter_subset_left)
    (hk.2.2.1.2.1.mono inter_subset_left)

/-- **Uniqueness theorem** (Ch. IV §5.2). Let `w : G → G′` be a quasiconformal mapping with the complex dilatation
`κ`. Then every quasiconformal mapping of `G` whose complex dilatation equals `κ` almost everywhere in `G` is of the
form `f ∘ w`, where `f` is a conformal mapping of `G′`. -/
theorem uniqueness_theorem {w w₁ : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hw₁ : IsQuasiconformalMap w₁ G)
    (hκ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w₁ z = complexDilatationLV w z) :
    ∃ f : ExtPlane → ExtPlane, IsConformalMap f (w '' G) ∧ ∀ z ∈ G, w₁ z = f (w z) := by
  obtain ⟨φ, hU, hφ, hφeq⟩ := lv45_same_dilatation hw hw₁ hκ
  obtain ⟨hG, hsp, -⟩ := hw
  obtain ⟨-, hsp₁, -⟩ := hw₁
  have hwi : InjOn w G := hsp.1.2.1
  have hgG : ∀ q ∈ w '' G, Function.invFunOn w G q ∈ G := fun q hq => by
    obtain ⟨x, hx, rfl⟩ := hq
    exact Function.invFunOn_mem ⟨x, hx, rfl⟩
  have hgw : ∀ x ∈ G, Function.invFunOn w G (w x) = x := fun x hx => hwi.leftInvOn_invFunOn hx
  have hwg : ∀ q ∈ w '' G, w (Function.invFunOn w G q) = q := fun q hq => by
    obtain ⟨x, hx, rfl⟩ := hq
    rw [hgw x hx]
  -- `f = w₁ ∘ w⁻¹` on `w(G)`
  refine ⟨fun q => w₁ (Function.invFunOn w G q), ?_, fun x hx => by simp only [hgw x hx]⟩
  refine lv15_isConformalMap_of_differentiableAt (invariance_of_domains hG hsp.1.1 hwi)
    (hsp₁.1.1.comp hsp.1.2.2.2 hgG) (fun q hq q' hq' h => ?_) (Set.finite_singleton (finiteValue (w extInf)))
    (fun ζ hζ hfin hζE => ?_)
  · rw [← hwg q hq, ← hwg q' hq', hsp₁.1.2.1 (hgG q hq) (hgG q' hq') h]
  · -- `ζ = w(a)` with `a` finite (`ζ ≠ w(∞)`) in the common finite core, where `f = φ` near `ζ`
    obtain ⟨x, hxG, hxζ⟩ := hζ
    induction x using OnePoint.rec with
    | infty =>
      exact absurd (show ζ = finiteValue (w extInf) by rw [hxζ]; rfl) hζE
    | coe a =>
      have hga : Function.invFunOn w G (ζ : ExtPlane) = a := by rw [← hxζ, hgw a hxG]
      have ha : a ∈ finiteCore w G ∩ finiteCore w₁ G :=
        ⟨⟨hxG, by rw [hxζ]; exact OnePoint.coe_ne_infty ζ⟩, ⟨hxG, by rwa [hga] at hfin⟩⟩
      have hζU : ζ ∈ finiteMap w '' (finiteCore w G ∩ finiteCore w₁ G) :=
        ⟨a, ha, by show finiteValue (w a) = ζ; rw [hxζ]; rfl⟩
      refine ((hφ ζ hζU).differentiableAt (hU.mem_nhds hζU)).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hζU] with ζ' hζ'
      obtain ⟨a', ha', rfl⟩ := hζ'
      have hwa' : w a' = ((finiteMap w a' : ℂ) : ExtPlane) := by
        obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 ha'.1.2
        show w a' = ((finiteValue (w a') : ℂ) : ExtPlane)
        rw [← hu]
        rfl
      show finiteValue (w₁ (Function.invFunOn w G ((finiteMap w a' : ℂ) : ExtPlane))) = φ (finiteMap w a')
      rw [← hwa', hgw a' ha'.1.1, ← hφeq a' ha']
      rfl

/-- Helper (WP6, W6-1b). Mappings that agree near `z` have the same complex dilatation at `z` (the chart
representation is a germ). -/
theorem lv45_complexDilatationLV_congr {w w' : ExtPlane → ExtPlane} {z : ExtPlane} (h : w =ᶠ[𝓝 z] w') :
    complexDilatationLV w z = complexDilatationLV w' z := by
  have hz : w z = w' z := h.eq_of_nhds
  obtain ⟨h0, hc⟩ := lv15_extChartInv z
  have h' : ∀ᶠ ζ in 𝓝 (0 : ℂ), w (extChartInv z ζ) = w' (extChartInv z ζ) :=
    hc.eventually (p := fun y => w y = w' y) (by rw [h0]; exact h)
  have hev : localRep w z =ᶠ[𝓝 0] localRep w' z := by
    filter_upwards [h'] with ζ hζ
    simp only [localRep, hz, hζ]
  unfold complexDilatationLV LiZhongQC.complexDilatation LiZhongQC.dz LiZhongQC.dzbar
  rw [hev.fderiv_eq]

/-- **Formula (5.9)** (Ch. IV §5.2). If `f` and `w` are quasiconformal mappings of the same domain `G`, then for
almost all `z ∈ G`, with `ζ = w(z)`,
`κ_{f∘w⁻¹}(ζ) = (κ_f(z) - κ_w(z)) / (1 - κ_f(z) conj(κ_w(z))) · e^{2i arg w_z(z)}` (5.9).
Modelling: `w⁻¹` is the inverse `Function.invFunOn w G` of `w` on `w(G)`. The exceptional null set contains the points
where `w` or `f` is not regular, where the denominator could vanish. -/
theorem eq4_5_9 {w f : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hf : IsQuasiconformalMap f G) :
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
      complexDilatationLV (f ∘ Function.invFunOn w G) (w z) =
        (complexDilatationLV f z - complexDilatationLV w z) /
            (1 - complexDilatationLV f z * conj (complexDilatationLV w z)) *
          Complex.exp (2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I) := by
  -- `g = f ∘ w⁻¹` is quasiconformal in `w(G)`, and `g ∘ w = f` in `G`
  obtain ⟨hG, hsp, hlt⟩ := hw
  have hw' : IsQuasiconformalMap w G := ⟨hG, hsp, hlt⟩
  have hkw : IsKQuasiconformal w G (maxDilatationK w G).toReal := ⟨hG, hsp, (ENNReal.ofReal_toReal hlt.ne).ge⟩
  have hkf : IsKQuasiconformal f G (maxDilatationK f G).toReal :=
    ⟨hf.1, hf.2.1, (ENNReal.ofReal_toReal hf.2.2.ne).ge⟩
  have himg : Function.invFunOn w G '' (w '' G) = G := hsp.1.2.1.invFunOn_image subset_rfl
  have hg : IsQuasiconformalMap (f ∘ Function.invFunOn w G) (w '' G) := by
    have h3 := kqc_comp (kqc_inv hkw) (by rw [himg]; exact hkf)
    exact ⟨h3.1, h3.2.1, lt_of_le_of_lt h3.2.2 ENNReal.ofReal_lt_top⟩
  have hgw : ∀ q ∈ G, ((f ∘ Function.invFunOn w G) ∘ w) q = f q := fun q hq => by
    show f (Function.invFunOn w G (w q)) = f q
    rw [hsp.1.2.1.leftInvOn_invFunOn hq]
  filter_upwards [lv45_ae_comp_regular hw' hg, lv45_ae_regular hf,
    ae_restrict_mem (hG.1.preimage OnePoint.continuous_coe).measurableSet] with z hz hzf hzG
  obtain ⟨hrw, hwz, hrg, hgwz⟩ := hz
  have h56 := eq4_5_6_i hw' hg hrw hwz hrg hgwz
  rw [lv45_complexDilatationLV_congr (Filter.eventuallyEq_of_mem (hG.1.mem_nhds hzG) hgw)] at h56
  -- the moduli of the three dilatations are `< 1` at the regular points
  obtain ⟨-, -, hltw, -, hnw⟩ := lv45_regular hw' hrw hwz
  obtain ⟨-, -, hltf, -, hnf⟩ := lv45_regular hf hzf.1 hzf.2
  obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.1 hwz
  have hrg' := hrg
  have hgwz' := hgwz
  rw [← hζ] at hrg' hgwz'
  obtain ⟨-, -, hltg, -, hng⟩ := lv45_regular hg hrg' hgwz'
  rw [hζ] at hng
  have ha : LiZhongQC.dz (finiteMap w) z ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt hltw)
  obtain ⟨he1, he2⟩ := lv45_exp_arg ha (LiZhongQC.dzbar (finiteMap w) z)
  have hkwq : complexDilatationLV w z = LiZhongQC.dzbar (finiteMap w) z / LiZhongQC.dz (finiteMap w) z := by
    rw [lv45_complexDilatationLV_eq hrw.2.1 hwz]
    rfl
  set kf := complexDilatationLV f z with hkf'
  set kw := complexDilatationLV w z with hkw'
  set kg := complexDilatationLV (f ∘ Function.invFunOn w G) (w z) with hkg'
  set e₁ := Complex.exp (-(2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I)) with he₁
  set e₂ := Complex.exp (-(2 * ((LiZhongQC.dzbar (finiteMap w) z).arg : ℂ) * I)) with he₂
  -- `κ_w e^{-2i arg w_{\bar z}} = conj κ_w e^{-2i arg w_z}`
  have hrel : kw * e₂ = conj kw * e₁ := by rw [hkwq, he2, he1]
  have hn₂ : ‖e₂‖ = 1 := by
    rw [he₂, Complex.norm_exp]
    simp
  have hlt1 : ∀ {x y : ℝ}, 0 ≤ x → x < y → x / y < 1 := fun hx hxy => (div_lt_one (hx.trans_lt hxy)).2 hxy
  have hnkw : ‖kw‖ < 1 := by rw [hnw]; exact hlt1 (norm_nonneg _) hltw
  have hnkf : ‖kf‖ < 1 := by rw [hnf]; exact hlt1 (norm_nonneg _) hltf
  have hnkg : ‖kg‖ < 1 := by rw [hng]; exact hlt1 (norm_nonneg _) hltg
  have hden1 : 1 + kw * kg * e₂ ≠ 0 := by
    intro h0
    have h' : ‖kw * kg * e₂‖ = 1 := by
      rw [show kw * kg * e₂ = -1 by linear_combination h0, norm_neg, norm_one]
    rw [norm_mul, norm_mul, hn₂, mul_one] at h'
    nlinarith [norm_nonneg kw, norm_nonneg kg]
  have hden2 : 1 - kf * conj kw ≠ 0 := by
    intro h0
    have h' : ‖kf * conj kw‖ = 1 := by
      rw [show kf * conj kw = 1 by linear_combination -h0, norm_one]
    rw [norm_mul, Complex.norm_conj] at h'
    nlinarith [norm_nonneg kw, norm_nonneg kf]
  have he₁0 : e₁ ≠ 0 := Complex.exp_ne_zero _
  rw [eq_div_iff hden1] at h56
  have hkey : kg * ((1 - kf * conj kw) * e₁) = kf - kw := by linear_combination -h56 + kf * kg * hrel
  have hexp : Complex.exp (2 * ((LiZhongQC.dz (finiteMap w) z).arg : ℂ) * I) = e₁⁻¹ := by
    rw [he₁, ← Complex.exp_neg]
    ring_nf
  rw [hexp, ← hkey]
  calc kg = kg * ((1 - kf * conj kw) * (1 - kf * conj kw)⁻¹) * (e₁ * e₁⁻¹) := by
        rw [mul_inv_cancel₀ hden2, mul_inv_cancel₀ he₁0, mul_one, mul_one]
    _ = kg * ((1 - kf * conj kw) * e₁) / (1 - kf * conj kw) * e₁⁻¹ := by ring

/-! ## §5.3 Beltrami's differential equation -/

/-- **Definition** (generalized solution of the Beltrami equation `w_{\bar z} = κ w_z` (5.10), Ch. IV §5.3). `w` is a
generalized solution of (5.10) in `G` if `w` is absolutely continuous on lines in `G` and its derivatives `w_z`,
`w_{\bar z}` (which exist almost everywhere by Lemma III.3.1) satisfy (5.10) almost everywhere in `G`.
Modelling: absolute continuity on lines in a domain of `ℂ̄` is `IsACLExt` (§1.1). The derivatives are the book's
expressions in the partial derivatives of the finite part, `(w_x ∓ i w_y)/2` (`genDz`, `genDzbar` of `partialX`,
`partialY`), not the Fréchet derivative: an ACL function need not be differentiable. The partial derivatives exist
almost everywhere (Lemma III.3.1), so their junk value `0` is seen only on a null set. `κ : ℂ → ℂ` need be defined
only almost everywhere (P1:5771); its standing assumptions (measurable, `sup |κ| < 1`, P1:5767) are hypotheses of
the statements. Defined for every `w : ℂ̄ → ℂ̄`. -/
def IsGeneralizedSolution (w : ExtPlane → ExtPlane) (κ : ℂ → ℂ) (G : Set ExtPlane) : Prop :=
  IsACLExt w G ∧ ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
    genDzbar (partialX (finiteMap w)) (partialY (finiteMap w)) z =
      κ z * genDz (partialX (finiteMap w)) (partialY (finiteMap w)) z

/-- **Definition** (generalized `L^p`-solution of the Beltrami equation (5.10), Ch. IV §5.3). `w` is a generalized
`L^p`-solution of (5.10) in `G` if it possesses `L^p`-derivatives in `G` and (5.10) holds almost everywhere in `G`.
Modelling: `L^p`-derivatives in a domain of `ℂ̄` are `HasLpDerivativesExt` (§1.1, real exponent `p ≥ 1`); the
derivatives in (5.10) as in `IsGeneralizedSolution`. Defined for every `w : ℂ̄ → ℂ̄`. -/
def IsGeneralizedLpSolution (w : ExtPlane → ExtPlane) (κ : ℂ → ℂ) (G : Set ExtPlane) (p : ℝ) : Prop :=
  HasLpDerivativesExt w G p ∧ ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
    genDzbar (partialX (finiteMap w)) (partialY (finiteMap w)) z =
      κ z * genDz (partialX (finiteMap w)) (partialY (finiteMap w)) z

/-- **Theorem 5.1** (Ch. IV §5.3), first part. A `K`-quasiconformal mapping `w` of the domain `G` is a generalized
`L²`-solution in `G` of the Beltrami equation (5.10), where `κ` is the complex dilatation of `w`.
Modelling: that (5.10) is a Beltrami equation in the book's sense (`κ` measurable with `sup |κ| < 1`, P1:5767) is
recorded by the last two conjuncts: `κ` is measurable and satisfies (5.11), `|κ| ≤ (K - 1)/(K + 1)` (multiplied
out), almost everywhere in `G`. -/
theorem thm4_5_1_i {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K) :
    IsGeneralizedLpSolution w (fun z => complexDilatationLV w z) G 2 ∧
      AEStronglyMeasurable (fun z : ℂ => complexDilatationLV w z) (volume.restrict (finitePart G)) ∧
      ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), (K + 1) * ‖complexDilatationLV w z‖ ≤ K - 1 := by
  have hq : IsQuasiconformalMap w G := ⟨hw.1, hw.2.1, lt_of_le_of_lt hw.2.2 ENNReal.ofReal_lt_top⟩
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K := lv13_isKQC_of_isKQuasiconformal hw
  have hK1 : 1 ≤ K := hk.2.1
  obtain ⟨hG, hsp, -⟩ := hw
  -- on the finite core, `κ` is Li Zhong's complex dilatation of `finiteMap w`
  have hκD : ∀ z ∈ finiteCore w G, complexDilatationLV w z = LiZhongQC.complexDilatation (finiteMap w) z :=
    fun z hz => lv45_complexDilatationLV_eq (hsp.1.1.continuousAt (hG.1.mem_nhds hz.1)) hz.2
  -- almost every point of `G` is a point of differentiability in the core satisfying (1.5)
  have hae : ∀ᵐ z ∂(volume.restrict (finitePart G)), z ∈ finiteCore w G ∧
      DifferentiableAt ℝ (finiteMap w) z ∧ ‖LiZhongQC.dz (finiteMap w) z‖ + ‖LiZhongQC.dzbar (finiteMap w) z‖ ≤
        K * (‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖) := by
    rw [lv41_restrict_eq hsp.1.2.1]
    filter_upwards [ae_restrict_mem hk.1.measurableSet, LiZhongQC.thm9_3_differentiable_ae hk,
      LiZhongQC.thm9_4_dilatation_ae hk] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨⟨thm4_1_2 hq, ?_⟩, ?_, ?_⟩
  · -- the Beltrami equation; where `w_z = 0` also `w_{\bar z} = 0` by (1.5), so the junk `κ = 0` is harmless
    filter_upwards [hae] with z ⟨hz, hd, hdil⟩
    simp only [genDz, genDzbar]
    rw [hκD z hz, LiZhongQC.partialX_eq_of_differentiableAt hd, LiZhongQC.partialY_eq_of_differentiableAt hd]
    change LiZhongQC.dzbar (finiteMap w) z =
      LiZhongQC.complexDilatation (finiteMap w) z * LiZhongQC.dz (finiteMap w) z
    rw [LiZhongQC.complexDilatation]
    by_cases h0 : LiZhongQC.dz (finiteMap w) z = 0
    · have hb : ‖LiZhongQC.dzbar (finiteMap w) z‖ = 0 := by
        rw [h0, norm_zero] at hdil
        nlinarith [norm_nonneg (LiZhongQC.dzbar (finiteMap w) z)]
      rw [norm_eq_zero.1 hb, h0, mul_zero]
    · rw [div_mul_cancel₀ _ h0]
  · -- `κ` agrees almost everywhere with the measurable `w_{\bar z}/w_z`
    have hm : Measurable (LiZhongQC.complexDilatation (finiteMap w)) :=
      (LiZhongQC.measurable_dzbar _).div (LiZhongQC.measurable_dz _)
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z ⟨hz, _, _⟩
    exact (hκD z hz).symm
  · -- (5.11)
    filter_upwards [hae] with z ⟨hz, _, hdil⟩
    rw [hκD z hz, LiZhongQC.complexDilatation, norm_div]
    rcases (norm_nonneg (LiZhongQC.dz (finiteMap w) z)).lt_or_eq with ha | ha
    · rw [← mul_div_assoc, div_le_iff₀ ha]
      nlinarith [hdil]
    · rw [← ha, div_zero, mul_zero]
      linarith

/-- **Theorem 5.1** (Ch. IV §5.3), converse part. If `κ` is a measurable function in `G` which satisfies (5.11),
`|κ(z)| ≤ (K - 1)/(K + 1)`, then every homeomorphic generalized solution of (5.10) in `G` is a `K`-quasiconformal
mapping of `G` with complex dilatation `κ(z)` for almost all `z ∈ G`.
Modelling: `G` is a domain of `ℂ̄`; `κ : ℂ → ℂ` on the finite part of `G` (the point `∞` is null); (5.11) is required
at every point of the finite part of `G`, as printed, and multiplied by `K + 1`. `w` is only assumed to be a
homeomorphism of `G` onto `w(G)` (the book proves that it is sense-preserving). `1 ≤ K` is the book's standing
`K ≥ 1` (harmonization H8), and it cannot be dropped: for `-1 ≤ K < 1` the multiplied-out (5.11) holds at no
point, but for `K < -1` it reads `‖κ‖ ≥ (K - 1)/(K + 1) > 1`, and the statement would be false (`w(z) = z + 2z̄` on
the finite plane, `κ ≡ 2`, `K = -3`: a sense-reversing affine homeomorphism solving (5.10)). -/
theorem thm4_5_1_ii {w : ExtPlane → ExtPlane} {κ : ℂ → ℂ} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hK : 1 ≤ K) (hκm : AEStronglyMeasurable κ (volume.restrict (finitePart G)))
    (hκ : ∀ z ∈ finitePart G, (K + 1) * ‖κ z‖ ≤ K - 1) (hw : IsHomeoOn w G (w '' G))
    (hsol : IsGeneralizedSolution w κ G) :
    IsKQuasiconformal w G K ∧ ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), complexDilatationLV w z = κ z := by
  have _ := hκm
  obtain ⟨hacl, heq⟩ := hsol
  obtain ⟨hDo, hhom⟩ := lv13_finiteCore_homeo hG.1 hw
  have hres : volume.restrict (finitePart G) = volume.restrict (finiteCore w G) := lv41_restrict_eq hw.2.1
  rw [hres] at heq
  -- at points of differentiability the equation reads `w_{\bar z} = κ w_z`
  have hbel : ∀ z, DifferentiableAt ℝ (finiteMap w) z →
      genDzbar (partialX (finiteMap w)) (partialY (finiteMap w)) z =
        κ z * genDz (partialX (finiteMap w)) (partialY (finiteMap w)) z →
      LiZhongQC.dzbar (finiteMap w) z = κ z * LiZhongQC.dz (finiteMap w) z := fun z hd h => by
    simp only [genDz, genDzbar] at h
    rw [LiZhongQC.partialX_eq_of_differentiableAt hd, LiZhongQC.partialY_eq_of_differentiableAt hd] at h
    exact h
  -- (5.11) gives Li Zhong's dilatation inequality almost everywhere in the finite core
  have hineq : ∀ᵐ z ∂(volume.restrict (finiteCore w G)),
      ‖LiZhongQC.dz (finiteMap w) z‖ + ‖LiZhongQC.dzbar (finiteMap w) z‖ ≤
        K * (‖LiZhongQC.dz (finiteMap w) z‖ - ‖LiZhongQC.dzbar (finiteMap w) z‖) := by
    filter_upwards [heq, ae_restrict_mem hDo.measurableSet] with z hz hzD
    by_cases hd : DifferentiableAt ℝ (finiteMap w) z
    · have hkz := hκ z hzD.1
      rw [hbel z hd hz, norm_mul]
      have h0 := mul_nonneg (norm_nonneg (LiZhongQC.dz (finiteMap w) z)) (sub_nonneg.2 hkz)
      nlinarith [norm_nonneg (κ z), norm_nonneg (LiZhongQC.dz (finiteMap w) z)]
    · simp [LiZhongQC.dz, LiZhongQC.dzbar, fderiv_zero_of_not_differentiableAt hd]
  -- so the finite part is `K`-q.c. on the finite core (Li Zhong's Theorem 10.1), and the converse bridge applies
  have hk : LiZhongQC.IsKQC (finiteMap w) (finiteCore w G) K :=
    (LiZhongQC.thm10_1_isKQC_iff hDo hK hhom).2 ⟨hacl, hineq⟩
  refine ⟨lv15_isKQuasiconformal_of_isKQC hG hw.1 hw.2.1 hk, ?_⟩
  -- the complex dilatation: `w_z ≠ 0` where the Jacobian is positive
  rw [hres]
  filter_upwards [heq, ae_restrict_mem hDo.measurableSet, LiZhongQC.thm9_3_differentiable_ae hk,
    LiZhongQC.thm9_6_cor2_jacobian_pos hk] with z hz hzD hd hJ
  rw [lv45_complexDilatationLV_eq (hw.1.continuousAt (hG.1.mem_nhds hzD.1)) hzD.2, LiZhongQC.complexDilatation,
    hbel z hd hz]
  have hdz : LiZhongQC.dz (finiteMap w) z ≠ 0 := fun h0 => by
    rw [LiZhongQC.jacobian, h0, norm_zero] at hJ
    nlinarith [norm_nonneg (LiZhongQC.dzbar (finiteMap w) z)]
  exact mul_div_cancel_right₀ _ hdz

/-! ## §5.4 Good approximation of a quasiconformal mapping -/

/-- **Definition** (good approximation, Ch. IV §5.4). Let `wₙ` be `K`-quasiconformal mappings of `G` with complex
dilatations `κₙ`, and `w` a quasiconformal mapping of `G` with complex dilatation `κ`. The sequence `wₙ` is a good
approximation of `w` if 1. `wₙ(z) → w(z)` uniformly on compact subsets of `G` (in the spherical metric if `G` contains
`∞` or `w⁻¹(∞)`), and 2. `κₙ(z) → κ(z)` almost everywhere in `G`.
Modelling: the book's standing data (a common `K` for the `wₙ`; `w` quasiconformal) are conjuncts. The uniform
convergence is always taken in the spherical metric (`TendstoUniformlyOnCompactsSph`); for a finite limit it is
equivalent, on compact sets, to euclidean uniform convergence. -/
def IsGoodApproximation (wn : ℕ → ExtPlane → ExtPlane) (w : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  (∃ K : ℝ, ∀ n, IsKQuasiconformal (wn n) G K) ∧ IsQuasiconformalMap w G ∧ TendstoUniformlyOnCompactsSph wn w G ∧
    ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
      Tendsto (fun n => complexDilatationLV (wn n) z) atTop (𝓝 (complexDilatationLV w z))

/-! ## §5.5 Weak convergence of the derivatives -/

/-- **Definition** (weak convergence in `G`, Ch. IV §5.5, (5.12)). The functions `fₙ`, locally integrable in the
domain `G`, converge weakly in `G` to the locally integrable function `f` if `lim_{n→∞} ∬_R (fₙ - f) dσ = 0` (5.12)
for every horizontal rectangle `R = {x + iy | a < x < b, c < y < d}`, `R̄ ⊂ G`.
Modelling: only the point set of `R` matters (`openRect`; its closure in `ℂ̄` is `closedRect`, so `R̄ ⊂ G` bounds `R`),
and "locally integrable in `G`" is local integrability on the finite part of `G`. Integrability repair (leader
decision, Part D): the book presupposes that every `fₙ` is locally integrable in `G`; here `fₙ` is only required to
be integrable on each test rectangle, for all large `n`. With the literal requirement Lemma 5.1 would be false: a
`K`-quasiconformal `wₙ` may take the value `∞` inside `G` for every `n` and still converge to a finite `w` (for
instance conformal mappings of the unit disc onto simply connected domains which reach `∞` through thinner and thinner
channels converge to the identity by Carathéodory's kernel theorem), and then `(wₙ)_z` is not integrable near
`wₙ⁻¹(∞)`; on a fixed `R̄ ⊂ G`, however, `wₙ` is finite for all large `n`. Requiring integrability on `R` also keeps
the junk value `0` of the integral of a non-integrable function out of (5.12). -/
def ConvergesWeaklyOnRectangles (fn : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (G : Set ExtPlane) : Prop :=
  LocallyIntegrableOn f (finitePart G) ∧
    ∀ a b c d : ℝ, a < b → c < d → toExt (closedRect a b c d) ⊆ G →
      (∀ᶠ n in atTop, IntegrableOn (fn n) (openRect a b c d)) ∧
        Tendsto (fun n => ∫ z in openRect a b c d, (fn n z - f z)) atTop (𝓝 0)

/-- **Lemma 5.1** (Ch. IV §5.5, Bers). Let `wₙ` be a sequence of `K`-quasiconformal mappings of `G` which converges
uniformly to a finite function `w` on compact subsets of `G`. Then the derivatives `(wₙ)_z` and `(wₙ)_{\bar z}`
converge weakly to `w_z` and `w_{\bar z}`, respectively.
Modelling: "finite" is `w(z) ≠ ∞` on `G`; the convergence is spherical (for a finite limit equivalent, on compact sets,
to euclidean uniform convergence). The limit is quasiconformal or constant (Theorem II.5.3), so all derivatives exist
almost everywhere, where the Fréchet-derivative expressions `LiZhongQC.dz`, `LiZhongQC.dzbar` of the finite parts are
the book's `w_z`, `w_{\bar z}`. Weak convergence is taken in the repaired sense of `ConvergesWeaklyOnRectangles`.
-/
theorem lemma4_5_1 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hw : ∀ z ∈ G, w z ≠ extInf)
    (hlim : TendstoUniformlyOnCompactsSph wn w G) :
    ConvergesWeaklyOnRectangles (fun n => LiZhongQC.dz (finiteMap (wn n))) (LiZhongQC.dz (finiteMap w)) G ∧
      ConvergesWeaklyOnRectangles (fun n => LiZhongQC.dzbar (finiteMap (wn n))) (LiZhongQC.dzbar (finiteMap w)) G := by
  sorry

/-! ## §5.6 A criterion for good approximation -/

/-- **Theorem 5.2** (Ch. IV §5.6, Bers). Let `wₙ` be a sequence of `K`-quasiconformal mappings of `G` which converges
to a quasiconformal mapping `w` with complex dilatation `κ`, uniformly on compact subsets of `G`. If the complex
dilatations `κₙ(z)` of `wₙ` tend to a limit `κ_∞(z)` almost everywhere in `G`, then `wₙ` is a good approximation to
`w`, i.e. `κ_∞(z) = κ(z)` almost everywhere in `G`.
Modelling: the limit `κ_∞` is a function `κlim : ℂ → ℂ` given with the almost-everywhere convergence; the
convergence of the mappings is spherical (see `IsGoodApproximation`). -/
theorem thm4_5_2 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    {κlim : ℂ → ℂ} (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hw : IsQuasiconformalMap w G)
    (hlim : TendstoUniformlyOnCompactsSph wn w G)
    (hκ : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
      Tendsto (fun n => complexDilatationLV (wn n) z) atTop (𝓝 (κlim z))) :
    (∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), κlim z = complexDilatationLV w z) ∧
      IsGoodApproximation wn w G := by
  sorry

end LehtoVirtanen1973
