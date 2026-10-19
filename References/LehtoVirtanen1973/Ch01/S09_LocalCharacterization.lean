import References.LehtoVirtanen1973.Ch01.S08_ExtensionTheorems
import LiZhongQC.Lemmas.RingCharacterization

/-!
# Lehto–Virtanen, Chapter I §9: Local characterization of quasiconformality

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. I §9
(pp. 47–51; `full.md` P1:1305–1494).

From §9 on, "differentiable" refers only to finite points and finite functions (P1:259): a mapping `w` of `ℂ̄` is
differentiable at a finite point `z₀` with `w(z₀) ≠ ∞` when its finite part `finiteMap w` is. The complex derivatives
are the project's `LiZhongQC.dz`, `LiZhongQC.dzbar` of the finite part.

* Definition (maximal dilatation at a point `F(z)`, §9.1) — `localMaxDil`
* Unlabelled (§9.1, P1:1317): `F` is a conformal invariant; the inverse mapping has the same `F` at the image point;
  `F(z) < ∞` iff `w` is quasiconformal in a neighbourhood of `z` — `localMaxDil_conformal_invariant`,
  `localMaxDil_inv`, `localMaxDil_lt_top_iff`
* Lemma 9.1 (§9.2) — `lemma1_9_1`
* Theorem 9.1 (§9.2) — `thm1_9_1`
* Theorem 9.2 (§9.3) — `thm1_9_2`
* Definition (complex derivatives `w_z`, `w_{\bar z}`, §9.4) — exists: `LiZhongQC.dz`, `LiZhongQC.dzbar` (defined
  from the real derivative fderiv; they equal the book's partial-derivative form at points of differentiability,
  the only use in §9)
* Definition (`o(z - z₀)`, `O(z - z₀)`, footnote 14) — exists: `Asymptotics.IsLittleO`, `Asymptotics.IsBigO`
* Unlabelled (§9.4, P1:1390): the directional derivative `∂_α w = w_z + w_{\bar z} e^{-2iα}` —
  `dirDeriv_eq_dz_add_dzbar`
* Formula (9.4), `J = |w_z|² - |w_{\bar z}|²` (§9.4) — exists: `LiZhongQC.det_fderiv_eq_jacobian` (at a point of
  differentiability, the determinant of the derivative is the difference of the squared moduli)
* Unlabelled (§9.4, P1:1399): a sense-preserving homeomorphism has `J ≥ 0`, i.e. `|w_{\bar z}| ≤ |w_z|`, at every
  finite point of differentiability — `sensePreserving_jacobian_nonneg`
* Formula (9.5) (§9.4) — `eq1_9_5`
* Definition (dilatation quotient `D(z)` at a regular point, at `∞` by an auxiliary linear mapping, §9.4) — exists:
  `LehtoVirtanen1973.dilQuot` (defined in §3)
* Theorem 9.3 (general dilatation condition, §9.5) — `thm1_9_3`
* Definition (square, §9.5) — `Quadrilateral.IsSquare`
* Unlabelled (§9.5, P1:1463, Remark): the dilatation condition for all squares implies the pointwise dilatation
  condition at every point of differentiability — `thm1_9_3_squares`
* Unlabelled (§9.6, P1:1473): for a quasiconformal mapping differentiable at `z`, `J(z) > 0`, `min_α |∂_α w(z)| > 0`
  and `w_z(z) ≠ 0` are equivalent — `tfae_regular`
* Corollary of Theorem 9.3 ((9.9), §9.6) — `thm1_9_3_cor`
* Theorem 9.4 (§9.6) — `thm1_9_4`

The upper semicontinuity (9.3) (P1:1349–1355, subsumed by Theorem 9.2) is not stated; the claim of the remark in
§9.5 on squares is stated because IV.3 uses it (P1:5423).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §9.1 Maximal dilatation at a point -/

/-- **Definition** (maximal dilatation at a point, Ch. I §9.1). For a sense-preserving homeomorphism `w` of the domain
`G` and `z ∈ G`, `F(z) = inf_{U_z} K(U_z)` over the neighbourhoods `U_z ⊂ G` of `z` (open neighbourhoods suffice,
`K` being monotone). -/
def localMaxDil (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (z : ExtPlane) : ℝ≥0∞ :=
  ⨅ (U : Set ExtPlane) (_ : IsOpen U) (_ : z ∈ U) (_ : U ⊆ G), maxDilatationK w U

/-- Helper (R1). A sense-preserving homeomorphism of `A` restricts to a sense-preserving homeomorphism of every
`V ⊆ A`: the inverse on `w(V)` is the inverse on `w(A)` there. -/
theorem lv19_sensePreserving_mono {w : ExtPlane → ExtPlane} {A V : Set ExtPlane} (hw : IsSensePreservingOn w A)
    (hVA : V ⊆ A) : IsSensePreservingOn w V := by
  obtain ⟨⟨hc, hi, -, hinv⟩, hpres⟩ := hw
  have hiV : InjOn w V := hi.mono hVA
  refine ⟨⟨hc.mono hVA, hiV, rfl, ?_⟩, fun D hD hDV => hpres D hD (hDV.trans hVA)⟩
  have heq : EqOn (Function.invFunOn w V) (Function.invFunOn w A) (w '' V) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hiV.leftInvOn_invFunOn hx, hi.leftInvOn_invFunOn (hVA hx)]
  exact (hinv.mono (image_mono hVA)).congr heq

/-- Helper (WP6, W6-5). The maximal dilatation is monotone in the domain: a smaller set has fewer quadrilaterals. -/
theorem lv19_maxDil_mono {w : ExtPlane → ExtPlane} {U V : Set ExtPlane} (hVU : V ⊆ U) :
    maxDilatationK w V ≤ maxDilatationK w U := by
  unfold maxDilatationK
  exact iSup₂_mono' fun Q hQ => ⟨Q, hQ.trans hVU, le_rfl⟩

/-- Helper (WP6, W6-5). `F(z) ≤ K(U)` for every open set `U` with `z ∈ U ⊆ G`. -/
theorem lv19_localMaxDil_le {w : ExtPlane → ExtPlane} {G U : Set ExtPlane} {z : ExtPlane} (hU : IsOpen U)
    (hzU : z ∈ U) (hUG : U ⊆ G) : localMaxDil w G z ≤ maxDilatationK w U := by
  unfold localMaxDil
  refine iInf_le_of_le U ?_
  refine iInf_le_of_le hU ?_
  refine iInf_le_of_le hzU ?_
  exact iInf_le_of_le hUG le_rfl

/-- Helper (WP6, W6-5; local ⇒ global). If `F(z) ≤ K` at every point of the domain `G` of a sense-preserving
homeomorphism `w`, then `K(G) ≤ K`. For `c > K` every point `z` of the finite core has a disc neighbourhood on which
`w` is `c`-quasiconformal, so the finite part is `c`-q.c. there in Li Zhong's sense (`lv13_isKQC_of_isKQuasiconformal`);
`LiZhongQC.s13x_removable` (with no exceptional set) makes it `c`-q.c. on the whole finite core, and the converse bridge
(`lv15_isKQuasiconformal_of_isKQC`) gives `K(G) ≤ c`. -/
theorem lv19_maxDil_le_of_local {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) (h : ∀ z ∈ G, localMaxDil w G z ≤ ENNReal.ofReal K) :
    maxDilatationK w G ≤ ENNReal.ofReal K := by
  obtain ⟨hDo, hhom⟩ := lv13_finiteCore_homeo hG.1 hw.1
  -- a finite point of `G` at which `w` is finite
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ℂ, (z₁ : ExtPlane) ∈ G ∧ w z₁ ≠ extInf := by
    obtain ⟨g, hg⟩ := hG.2.nonempty
    obtain ⟨z, hz⟩ := OnePoint.denseRange_coe.exists_mem_open hG.1 ⟨g, hg⟩
    have hzo : IsOpen (((↑) : ℂ → ExtPlane) ⁻¹' G) := hG.1.preimage OnePoint.continuous_coe
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hzo z hz
    have hz' : ((z + ε / 2 : ℂ) : ExtPlane) ∈ G := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [show (ε / 2 : ℂ) = ((ε / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith)
    by_cases hwz : w z = extInf
    · refine ⟨z + ε / 2, hz', fun h' => ?_⟩
      have h2 := OnePoint.coe_injective (hw.1.2.1 hz hz' (hwz.trans h'.symm))
      have : (ε / 2 : ℂ) = 0 := by linear_combination -h2
      have : ε = 0 := by exact_mod_cast (by linear_combination 2 * this : (ε : ℂ) = 0)
      linarith
    · exact ⟨z, hz, hwz⟩
  -- for every `c > K`, `c > 0`, the finite part is `c`-q.c. on the finite core
  have key : ∀ c : ℝ, K < c → 0 < c → maxDilatationK w G ≤ ENNReal.ofReal c := by
    intro c hKc hc
    have hlt : ENNReal.ofReal K < ENNReal.ofReal c := (ENNReal.ofReal_lt_ofReal_iff hc).2 hKc
    have hloc : ∀ z ∈ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
        U ⊆ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} ∧ LiZhongQC.IsKQC (finiteMap w) U c := by
      intro z hz
      have h1 := (h z hz.1).trans_lt hlt
      unfold localMaxDil at h1
      obtain ⟨V, h2⟩ := iInf_lt_iff.1 h1
      obtain ⟨hVo, h3⟩ := iInf_lt_iff.1 h2
      obtain ⟨hzV, h4⟩ := iInf_lt_iff.1 h3
      obtain ⟨hVG, hVlt⟩ := iInf_lt_iff.1 h4
      -- a disc around `z` in `V` and in the finite core
      have hO : IsOpen ((((↑) : ℂ → ExtPlane) ⁻¹' V) ∩ {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf}) :=
        (hVo.preimage OnePoint.continuous_coe).inter hDo
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO z ⟨hzV, hz⟩
      have hW : IsDomainExt (toExt (Metric.ball z r)) :=
        ⟨OnePoint.isOpen_image_coe.2 Metric.isOpen_ball,
          (Metric.isConnected_ball hr).image _ OnePoint.continuous_coe.continuousOn⟩
      have hWV : toExt (Metric.ball z r) ⊆ V := by
        rintro _ ⟨u, hu, rfl⟩
        exact (hball hu).1
      have hkW : IsKQuasiconformal w (toExt (Metric.ball z r)) c :=
        ⟨hW, lv19_sensePreserving_mono hw (hWV.trans hVG), (lv19_maxDil_mono hWV).trans hVlt.le⟩
      have hcore : {u : ℂ | (u : ExtPlane) ∈ toExt (Metric.ball z r) ∧ w u ≠ extInf} = Metric.ball z r := by
        ext u
        constructor
        · rintro ⟨⟨v, hv, hvu⟩, -⟩
          rw [← OnePoint.coe_injective hvu]
          exact hv
        · intro hu
          exact ⟨⟨u, hu, rfl⟩, (hball hu).2.2⟩
      have hk := lv13_isKQC_of_isKQuasiconformal hkW
      rw [hcore] at hk
      exact ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, fun u hu => (hball hu).2, hk⟩
    obtain ⟨U₁, -, -, -, hU₁⟩ := hloc z₁ hz₁
    have hk : LiZhongQC.IsKQC (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} c :=
      LiZhongQC.s13x_removable (L := ∅) hDo hU₁.2.1 hhom MeasureTheory.measure_empty
        (Filter.Eventually.of_forall fun x => by simp) (Filter.Eventually.of_forall fun y => by simp)
        fun z hz => hloc z hz.1
    exact (lv15_isKQuasiconformal_of_isKQC hG hw.1.1 hw.1.2.1 hk).2.2
  -- let `c = max K 0 + ε` tend to `max K 0`
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  have hmax : ENNReal.ofReal (max K 0) = ENNReal.ofReal K := by
    rcases le_total K 0 with hK | hK
    · rw [max_eq_right hK, ENNReal.ofReal_of_nonpos hK, ENNReal.ofReal_zero]
    · rw [max_eq_left hK]
  calc maxDilatationK w G ≤ ENNReal.ofReal (max K 0 + ε) :=
        key _ (by linarith [le_max_left K 0]) (by linarith [le_max_right K 0])
    _ = ENNReal.ofReal K + ε := by
        rw [ENNReal.ofReal_add (le_max_right _ _) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal, hmax]

/-- **Unlabelled** (Ch. I §9.1, P1:1317). `F(z)` is a conformal invariant: composing `w` with conformal mappings of
`w(G)` and of `G` does not change the maximal dilatation at corresponding points. -/
theorem localMaxDil_conformal_invariant {w φ ψ : ExtPlane → ExtPlane} {G : Set ExtPlane}
    (hw : IsSensePreservingOn w G) (hG : IsDomainExt G) (hφ : IsConformalMap φ (w '' G))
    (hψ : IsConformalMap ψ G) {z : ExtPlane} (hz : z ∈ G) :
    localMaxDil (φ ∘ w) G z = localMaxDil w G z ∧
      localMaxDil (w ∘ Function.invFunOn ψ G) (ψ '' G) (ψ z) = localMaxDil w G z := by
  sorry

/-- **Unlabelled** (Ch. I §9.1, P1:1317). The maximal dilatation of the inverse mapping at the image point of `z` is
also `F(z)`. -/
theorem localMaxDil_inv {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) {z : ExtPlane} (hz : z ∈ G) :
    localMaxDil (Function.invFunOn w G) (w '' G) (w z) = localMaxDil w G z := by
  sorry

/-- **Unlabelled** (Ch. I §9.1, P1:1317). `F(z)` is finite if and only if the mapping is quasiconformal in a
neighbourhood of `z`. -/
theorem localMaxDil_lt_top_iff {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) {z : ExtPlane} (hz : z ∈ G) :
    localMaxDil w G z < ⊤ ↔ ∃ U, IsDomainExt U ∧ z ∈ U ∧ U ⊆ G ∧ IsQuasiconformalMap w U := by
  have _ := hG
  have _ := hz
  constructor
  · intro hlt
    unfold localMaxDil at hlt
    obtain ⟨V, h2⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hVo, h3⟩ := iInf_lt_iff.1 h2
    obtain ⟨hzV, h4⟩ := iInf_lt_iff.1 h3
    obtain ⟨hVG, hVlt⟩ := iInf_lt_iff.1 h4
    -- the component of `z` in `V` (`ℂ̄` is locally connected)
    have hCV : connectedComponentIn V z ⊆ V := connectedComponentIn_subset V z
    have hCd : IsDomainExt (connectedComponentIn V z) :=
      ⟨hVo.connectedComponentIn, isConnected_connectedComponentIn_iff.2 hzV⟩
    exact ⟨connectedComponentIn V z, hCd, mem_connectedComponentIn hzV, hCV.trans hVG, hCd,
      lv19_sensePreserving_mono hw (hCV.trans hVG), (lv19_maxDil_mono hCV).trans_lt hVlt⟩
  · rintro ⟨U, hU, hzU, hUG, hq⟩
    unfold localMaxDil
    exact (lv19_localMaxDil_le hU.1 hzU hUG).trans_lt hq.2.2

/-! ## §9.2–9.3 Local and global maximal dilatation -/

/-- **Lemma 9.1** (Ch. I §9.2). The maximal dilatation of a sense-preserving homeomorphism of the domain `G` satisfies
`K(G) = sup_{z ∈ G} F(z)` (9.1). -/
theorem lemma1_9_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) : maxDilatationK w G = ⨆ z ∈ G, localMaxDil w G z := by
  apply le_antisymm
  · by_cases hM : (⨆ z ∈ G, localMaxDil w G z) = ⊤
    · rw [hM]
      exact le_top
    · have h := lv19_maxDil_le_of_local hG hw (K := (⨆ z ∈ G, localMaxDil w G z).toReal) fun z hz => by
        rw [ENNReal.ofReal_toReal hM]
        exact le_iSup₂ (f := fun z (_ : z ∈ G) => localMaxDil w G z) z hz
      rwa [ENNReal.ofReal_toReal hM] at h
  · exact iSup₂_le fun z hz => lv19_localMaxDil_le hG.1 hz subset_rfl

/-- **Theorem 9.1** (Ch. I §9.2). A sense-preserving homeomorphism of a domain `G` is `K`-quasiconformal if and only
if `F(z) ≤ K` at every point `z ∈ G`. -/
theorem thm1_9_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) : IsKQuasiconformal w G K ↔ ∀ z ∈ G, localMaxDil w G z ≤ ENNReal.ofReal K := by
  constructor
  · intro hk z hz
    exact (lv19_localMaxDil_le hG.1 hz subset_rfl).trans hk.2.2
  · intro h
    exact ⟨hG, hw, lv19_maxDil_le_of_local hG hw h⟩

/-- **Theorem 9.2** (Ch. I §9.3). A sense-preserving homeomorphism of a domain `G` satisfies
`F(z) = limsup_{ζ → z} F(ζ)` at every point `z ∈ G` (also when `F(z) = ∞`).
Modelling: the `limsup` is taken over `ζ ≠ z` (`𝓝[≠] z`), as the proof shows. -/
theorem thm1_9_2 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) {z : ExtPlane} (hz : z ∈ G) :
    localMaxDil w G z = limsup (localMaxDil w G) (𝓝[≠] z) := by
  sorry

/-! ## §9.4–9.6 Dilatation quotient at a regular point -/

/-- **Unlabelled** (Ch. I §9.4, P1:1390). At a point of differentiability, the derivative in the direction `α` is
`∂_α w(z₀) = w_z(z₀) + w_{\bar z}(z₀) e^{-2iα}`. -/
theorem dirDeriv_eq_dz_add_dzbar {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℝ f z₀) (α : ℝ) :
    dirDeriv f z₀ α = LiZhongQC.dz f z₀ + LiZhongQC.dzbar f z₀ * exp (-(2 * α * I)) := by
  -- `f′(z₀)h = w_z h + w_{z̄} h̄` with `h = e^{iα}`, `h̄ = e^{-iα}`
  have hconj : (starRingEnd ℂ) (exp (α * I)) = exp (-(α * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have h1 : exp (α * I) * exp (-(α * I)) = 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : exp (-(α * I)) * exp (-(α * I)) = exp (-(2 * α * I)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [dirDeriv, LiZhongQC.fderiv_eq_dz_dzbar hf, hconj]
  linear_combination LiZhongQC.dz f z₀ * h1 + LiZhongQC.dzbar f z₀ * h2

/-- **Unlabelled** (Ch. I §9.4, P1:1399). A sense-preserving homeomorphism `w` has `J(z₀) ≥ 0` (cf. §1.6), and so
`|w_{\bar z}(z₀)| ≤ |w_z(z₀)|`, at every finite point `z₀` with finite value at which it is differentiable.
Modelling: `z₀` and `w(z₀)` finite (the convention of §9). -/
theorem sensePreserving_jacobian_nonneg {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ G) (hfin : w z₀ ≠ extInf)
    (hd : DifferentiableAt ℝ (finiteMap w) z₀) :
    0 ≤ LinearMap.det (fderiv ℝ (finiteMap w) z₀ : ℂ →ₗ[ℝ] ℂ) ∧
      ‖LiZhongQC.dzbar (finiteMap w) z₀‖ ≤ ‖LiZhongQC.dz (finiteMap w) z₀‖ := by
  -- `finiteMap w` is a homeomorphism of the finite core, sense-preserving in Li Zhong's sense (bridge B1, B5)
  obtain ⟨hDo, hfc, hfi, -, -⟩ := lv13_finiteCore_homeo hG.1 hw.1
  have hsense : LiZhongQC.IsSensePreserving (finiteMap w) {z : ℂ | (z : ExtPlane) ∈ G ∧ w z ≠ extInf} :=
    fun Q hQ => lv13_image_isTopQuad hG.1 hw Q hQ
  have hle := LiZhongQC.rc_norm_dzbar_le hDo hfc hfi hsense ⟨hz₀, hfin⟩ hd
  refine ⟨?_, hle⟩
  rw [LiZhongQC.det_fderiv_eq_jacobian hd, LiZhongQC.jacobian]
  nlinarith [norm_nonneg (LiZhongQC.dzbar (finiteMap w) z₀)]

/-- **Formula (9.5)** (Ch. I §9.4). If `w` is differentiable at `z₀` and `|w_{\bar z}(z₀)| ≤ |w_z(z₀)|`, then
`max_α |∂_α w(z₀)| = |w_z(z₀)| + |w_{\bar z}(z₀)|` and `min_α |∂_α w(z₀)| = |w_z(z₀)| - |w_{\bar z}(z₀)|`.
Modelling: the book derives `|w_{\bar z}| ≤ |w_z|` from sense-preservation (`sensePreserving_jacobian_nonneg`) and
states (9.5) for a sense-preserving homeomorphism; the formula uses only this inequality. -/
theorem eq1_9_5 {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℝ f z₀)
    (hle : ‖LiZhongQC.dzbar f z₀‖ ≤ ‖LiZhongQC.dz f z₀‖) :
    (⨆ α : ℝ, ‖dirDeriv f z₀ α‖) = ‖LiZhongQC.dz f z₀‖ + ‖LiZhongQC.dzbar f z₀‖ ∧
      (⨅ α : ℝ, ‖dirDeriv f z₀ α‖) = ‖LiZhongQC.dz f z₀‖ - ‖LiZhongQC.dzbar f z₀‖ := by
  set a := ‖LiZhongQC.dz f z₀‖ with hadef
  set b := ‖LiZhongQC.dzbar f z₀‖ with hbdef
  set θ := arg (LiZhongQC.dz f z₀) with hθdef
  set φ := arg (LiZhongQC.dzbar f z₀) with hφdef
  have hz : LiZhongQC.dz f z₀ = (a : ℂ) * exp (θ * I) := (Complex.norm_mul_exp_arg_mul_I _).symm
  have hzb : LiZhongQC.dzbar f z₀ = (b : ℂ) * exp (φ * I) := (Complex.norm_mul_exp_arg_mul_I _).symm
  have hb0 : 0 ≤ b := norm_nonneg _
  -- `|∂_α w| = |w_z + w_{z̄} e^{-2iα}|` with `|e^{-2iα}| = 1`
  have hE : ∀ α : ℝ, ‖exp (-(2 * (α : ℂ) * I))‖ = 1 := fun α => by
    rw [Complex.norm_exp]
    simp
  have hdir : ∀ α : ℝ, ‖dirDeriv f z₀ α‖ = ‖LiZhongQC.dz f z₀ + LiZhongQC.dzbar f z₀ * exp (-(2 * α * I))‖ :=
    fun α => by rw [dirDeriv_eq_dz_add_dzbar hf α]
  have hup : ∀ α : ℝ, ‖dirDeriv f z₀ α‖ ≤ a + b := fun α => by
    rw [hdir]
    calc _ ≤ ‖LiZhongQC.dz f z₀‖ + ‖LiZhongQC.dzbar f z₀ * exp (-(2 * α * I))‖ := norm_add_le _ _
      _ = a + b := by rw [norm_mul, hE, mul_one]
  have hlow : ∀ α : ℝ, a - b ≤ ‖dirDeriv f z₀ α‖ := fun α => by
    rw [hdir]
    have h := norm_sub_le (LiZhongQC.dz f z₀ + LiZhongQC.dzbar f z₀ * exp (-(2 * α * I)))
      (LiZhongQC.dzbar f z₀ * exp (-(2 * α * I)))
    rw [add_sub_cancel_right, norm_mul, hE, mul_one] at h
    linarith
  -- the extremal directions: `w_{z̄} e^{-2iα} = ± |w_{z̄}| e^{iθ}`
  have hmax : ‖dirDeriv f z₀ ((φ - θ) / 2)‖ = a + b := by
    have e : exp (φ * I) * exp (-(2 * (((φ - θ) / 2 : ℝ) : ℂ) * I)) = exp (θ * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hdir, hz, hzb, mul_assoc, e, ← add_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmin : ‖dirDeriv f z₀ ((φ - θ - Real.pi) / 2)‖ = a - b := by
    have e : exp (φ * I) * exp (-(2 * (((φ - θ - Real.pi) / 2 : ℝ) : ℂ) * I)) = -exp (θ * I) := by
      rw [← Complex.exp_add, show φ * I + -(2 * (((φ - θ - Real.pi) / 2 : ℝ) : ℂ) * I) = θ * I + Real.pi * I by
        push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [hdir, hz, hzb, mul_assoc, e, mul_neg, ← sub_eq_add_neg, ← sub_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  constructor
  · exact ciSup_eq_of_forall_le_of_forall_lt_exists_gt hup fun x hx => ⟨_, hmax ▸ hx⟩
  · exact ciInf_eq_of_forall_ge_of_forall_gt_exists_lt hlow fun x hx => ⟨_, hmin ▸ hx⟩

/-- **Theorem 9.3** (Ch. I §9.5, general dilatation condition). If the quasiconformal mapping `w` of `G` is
differentiable at the point `z₀`, then `max_α |∂_α w(z₀)| ≤ F(z₀) min_α |∂_α w(z₀)|` (9.6).
Modelling: `z₀` and `w(z₀)` finite (the convention of §9); the inequality in `ℝ≥0∞`. -/
theorem thm1_9_3 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z₀ : ℂ}
    (hz₀ : (z₀ : ExtPlane) ∈ G) (hfin : w z₀ ≠ extInf) (hd : DifferentiableAt ℝ (finiteMap w) z₀) :
    ENNReal.ofReal (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z₀ α‖) ≤
      localMaxDil w G z₀ * ENNReal.ofReal (⨅ α : ℝ, ‖dirDeriv (finiteMap w) z₀ α‖) := by
  obtain ⟨hG, hsp, hlt⟩ := hw
  -- `|w_{\bar z}| ≤ |w_z|` at `z₀`, so `max = a + b` and `min = a - b` (9.5)
  have hle := (sensePreserving_jacobian_nonneg hG hsp hz₀ hfin hd).2
  obtain ⟨hsup, hinf⟩ := eq1_9_5 hd hle
  rw [hsup, hinf]
  -- (1.5) at `z₀` on every domain `V ∋ z₀`, `V ⊆ G`, on which `w` is quasiconformal
  have hloc : ∀ V : Set ExtPlane, IsDomainExt V → (z₀ : ExtPlane) ∈ V → V ⊆ G → maxDilatationK w V < ⊤ →
      ‖LiZhongQC.dz (finiteMap w) z₀‖ + ‖LiZhongQC.dzbar (finiteMap w) z₀‖ ≤
        (maxDilatationK w V).toReal * (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖) :=
    fun V hV hzV hVG hVt => by
      have hk := lv13_isKQC_of_isKQuasiconformal
        (⟨hV, lv19_sensePreserving_mono hsp hVG, by rw [ENNReal.ofReal_toReal hVt.ne]⟩ :
          IsKQuasiconformal w V (maxDilatationK w V).toReal)
      exact LiZhongQC.ac_t_dilatation_of_differentiableAt hk ⟨hzV, hfin⟩ hd
  have hGb := hloc G hG hz₀ subset_rfl hlt
  rcases (sub_nonneg.2 hle).eq_or_lt with h0 | hpos
  · -- `min = 0` forces `max = 0`
    rw [← h0, mul_zero] at hGb
    rw [← h0, ENNReal.ofReal_zero, mul_zero]
    exact le_of_eq (ENNReal.ofReal_eq_zero.2 hGb)
  · -- divide by `ofReal (a - b) ∈ (0, ∞)` and bound by every `K(U)`
    have hc0 : ENNReal.ofReal (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hpos).ne'
    have hct : ENNReal.ofReal (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    rw [← ENNReal.div_le_iff hc0 hct]
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hzU => le_iInf fun hUG => ?_
    rw [ENNReal.div_le_iff hc0 hct]
    by_cases hUt : maxDilatationK w U = ⊤
    · rw [hUt, ENNReal.top_mul hc0]
      exact le_top
    · -- a small disc `V` about `z₀` inside `U` is a domain with `K(V) ≤ K(U)`
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hU.preimage OnePoint.continuous_coe) z₀ hzU
      set V : Set ExtPlane := toExt (Metric.ball z₀ r) with hVdef
      have hVU : V ⊆ U := by
        rintro _ ⟨x, hx, rfl⟩
        exact hball hx
      have hVd : IsDomainExt V :=
        ⟨OnePoint.isOpen_image_coe.2 Metric.isOpen_ball,
          (Metric.isConnected_ball hr).image _ OnePoint.continuous_coe.continuousOn⟩
      have hzV : (z₀ : ExtPlane) ∈ V := ⟨z₀, Metric.mem_ball_self hr, rfl⟩
      have hKV : maxDilatationK w V ≤ maxDilatationK w U := by
        unfold maxDilatationK
        exact iSup₂_mono' fun Q hQ => ⟨Q, hQ.trans hVU, le_rfl⟩
      have hVt : maxDilatationK w V < ⊤ := hKV.trans_lt (lt_top_iff_ne_top.2 hUt)
      have h1 := hloc V hVd hzV (hVU.trans hUG) hVt
      calc ENNReal.ofReal (‖LiZhongQC.dz (finiteMap w) z₀‖ + ‖LiZhongQC.dzbar (finiteMap w) z₀‖)
          ≤ ENNReal.ofReal ((maxDilatationK w V).toReal *
              (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖)) :=
            ENNReal.ofReal_le_ofReal h1
        _ = maxDilatationK w V *
              ENNReal.ofReal (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖) := by
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt.ne]
        _ ≤ maxDilatationK w U *
              ENNReal.ofReal (‖LiZhongQC.dz (finiteMap w) z₀‖ - ‖LiZhongQC.dzbar (finiteMap w) z₀‖) :=
            by gcongr

/-- **Definition** (square, Ch. I §9.5): a quadrilateral whose domain is a Euclidean square, in any position, with
its corners as vertices (the image of `R(0, a, a + ia, ia)` under a similarity). -/
def Quadrilateral.IsSquare (Q : Quadrilateral) : Prop :=
  ∃ (a : ℝ) (α β : ℂ), 0 < a ∧ α ≠ 0 ∧ Q.dom = toExt ((fun z => α * z + β) '' LiZhongQC.rectangle a a) ∧
    ∀ i, Q.vert i = OnePoint.map (fun z => α * z + β) (LiZhongQC.rectVert a a i)

/-- **Unlabelled** (Ch. I §9.5, P1:1463, Remark after Theorem 9.3). If the sense-preserving homeomorphism `w` of the
domain `G` satisfies the dilatation condition `M(w(R)) ≤ K M(R)` for every square `R`, `R̄ ⊂ G`, then
`max_α |∂_α w(z)| ≤ K min_α |∂_α w(z)|` at every point `z ∈ G` at which `w` is differentiable (every square must be
taken into consideration, not only those with sides parallel to the axes).
Modelling: `z` and `w(z)` finite (the convention of §9). -/
theorem thm1_9_3_squares {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (hw : IsSensePreservingOn w G)
    (hR : ∀ R : Quadrilateral, R.IsSquare → closure R.dom ⊆ G →
      quadModule (w '' R.dom) (w ∘ R.vert) ≤ K * R.module)
    {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ G) (hfin : w z₀ ≠ extInf) (hd : DifferentiableAt ℝ (finiteMap w) z₀) :
    (⨆ α : ℝ, ‖dirDeriv (finiteMap w) z₀ α‖) ≤ K * ⨅ α : ℝ, ‖dirDeriv (finiteMap w) z₀ α‖ := by
  sorry

/-- **Unlabelled** (Ch. I §9.6, P1:1473). If the quasiconformal mapping `w` is differentiable at the point `z`, then
the three conditions `J(z) > 0`, `min_α |∂_α w(z)| > 0` and `w_z(z) ≠ 0` are equivalent.
Modelling: `z` and `w(z)` finite (the convention of §9). -/
theorem tfae_regular {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z₀ : ℂ}
    (hz₀ : (z₀ : ExtPlane) ∈ G) (hfin : w z₀ ≠ extInf) (hd : DifferentiableAt ℝ (finiteMap w) z₀) :
    List.TFAE [0 < LinearMap.det (fderiv ℝ (finiteMap w) z₀ : ℂ →ₗ[ℝ] ℂ),
      0 < ⨅ α : ℝ, ‖dirDeriv (finiteMap w) z₀ α‖, LiZhongQC.dz (finiteMap w) z₀ ≠ 0] := by
  obtain ⟨hG, hsp, hlt⟩ := hw
  have hk := lv13_isKQC_of_isKQuasiconformal
    (⟨hG, hsp, by rw [ENNReal.ofReal_toReal hlt.ne]⟩ : IsKQuasiconformal w G (maxDilatationK w G).toReal)
  -- (1.5) at `z₀`, `|w_{\bar z}| ≤ |w_z|`, and `min = a - b`
  have hdil := LiZhongQC.ac_t_dilatation_of_differentiableAt hk ⟨hz₀, hfin⟩ hd
  have hK1 : 1 ≤ (maxDilatationK w G).toReal := hk.2.1
  have hle := (sensePreserving_jacobian_nonneg hG hsp hz₀ hfin hd).2
  obtain ⟨-, hinf⟩ := eq1_9_5 hd hle
  rw [LiZhongQC.det_fderiv_eq_jacobian hd, LiZhongQC.jacobian, hinf]
  have hb0 := norm_nonneg (LiZhongQC.dzbar (finiteMap w) z₀)
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h h0
      rw [h0, norm_zero] at h
      linarith
    · intro h
      have ha : 0 < ‖LiZhongQC.dz (finiteMap w) z₀‖ := norm_pos_iff.2 h
      by_contra hc0
      have hc := not_lt.1 hc0
      nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ (maxDilatationK w G).toReal)]
  tfae_finish

/-- **Corollary of Theorem 9.3** (Ch. I §9.6). A quasiconformal mapping satisfies `D(z) ≤ F(z)` (9.9) at every regular
point `z` (at `∞` and where `w = ∞`, `D` is read in the charts). -/
theorem thm1_9_3_cor {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z : ExtPlane}
    (hz : IsRegularPointOf w G z) : ENNReal.ofReal (dilQuot w z) ≤ localMaxDil w G z := by
  sorry

/-- **Theorem 9.4** (Ch. I §9.6). A regular quasiconformal mapping of the domain `G` satisfies `D(z) = F(z)` for every
`z ∈ G`. -/
theorem thm1_9_4 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsRegularQuasiconformal w G) {z : ExtPlane}
    (hz : z ∈ G) : ENNReal.ofReal (dilQuot w z) = localMaxDil w G z := by
  sorry

end LehtoVirtanen1973
