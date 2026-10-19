import References.AstalaGehring1990.S1_Introduction
import References.Gehring1978.S1_Introduction
import References.Common.Quasidisk

/-!
# Astala–Gehring 1990, §2 Closure of `T`

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), §2; source `full.md` of `Astala-CricketsZippersBers-1990.pdf-e9a341c8…`, lines 47–115.

* Definition (hyperbolic density `ρ_D` with curvature `-4`, §2) — exists: `Gehring1978.hypDensity` (the same
  normalization, by the same author)
* Definition (the norm (2.1), `‖S_f‖_D = sup |S_f| ρ_D⁻²`, §2) — exists: `Gehring1978.hypNorm` (with the Schwarzian
  `LiZhongQC.schwarzian`)
* Theorem 2.2 — `thm2_2`
* Remark 2.3 (l. 107: the sufficiency of Theorem 2.2 with the disks `cr ≤ dist(z₀, ∂D)`; a labelled remark whose
  claim is used in the proofs of 2.4 and 3.1) — `rem2_3`
* Definition (a domain `D` is in `T̄`, l. 109) — `IsInTbar`
* Unlabelled (§2, l. 109: `D` is in `T̄` whenever `g(D)` is, `g` Möbius) — `isInTbar_of_mobius`
* Corollary 2.4 — `cor2_4`

**Conventions.**
- All quasiconformal maps are sense preserving (l. 49). The reference notions are those of Lehto–Virtanen
  (FOUNDATIONS.md), which include sense preservation:
  - a homeomorphism of `A` onto `A'` is `LehtoVirtanen1973.IsHomeoOn`;
  - a `K`-quasiconformal self-mapping of `ℂ̄` is `LehtoVirtanen1973.IsKQuasiconformal F univ K`.
- A quasidisk is `References.IsQuasidiskExt`.
- A domain `D = f(U)` is a subset of `ℂ̄`; it may contain `∞`.
- "A disk `B` in `D`" is an open euclidean disk `B(z₀, r)`, `r > 0`, contained in the finite part of `D`, as in the
  proofs (l. 81, 107). "`g|B` has a `K`-quasiconformal extension to `ℂ̄`" means that some `K`-quasiconformal
  self-mapping of `ℂ̄` agrees with `g` on `B`.
- `dist(z₀, ∂D)` is the euclidean distance from `z₀` to the finite boundary points of `D`. That set is nonempty, as
  `D` is simply connected of hyperbolic type, so the infimum is genuine.

Not items: the proofs, including the quotations of [L] and of the Koebe distortion theorem inside them (U−).
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace AstalaGehring1990

open LiZhongQC References
open LehtoVirtanen1973 (IsHomeoOn IsKQuasiconformal)

/-- **Theorem 2.2** (§2). Suppose that `f` is a conformal mapping of `U` onto `D`. Then `S_f` is in `T̄` if and only if
for each `K > 1` there exists a homeomorphism `g` of `D` onto a quasidisk such that for each disk `B` in `D`, `g|B`
has a `K`-quasiconformal extension to `ℂ̄`.
Modelling:
- `D = f(U) ⊆ ℂ̄` through `LiZhongQC.meroToExt`, and `g : ℂ̄ → ℂ̄` maps `D` homeomorphically onto the quasidisk
  `g(D)`.
- The disks and the extensions are as in the conventions of this file: euclidean disks, the reading of the proof of
  the sufficiency. Reading "disk" as any Möbius image of `U` in `D` would make the necessity stronger and the
  sufficiency weaker; the proof of the necessity covers that reading too. -/
theorem thm2_2 {f : ℂ → ℂ} (hf : IsUnivMero f unitDisc) {D : Set ExtPlane} (hD : meroToExt f '' unitDisc = D) :
    unitDisc.indicator (schwarzian f) ∈ closureE setT ↔
      ∀ K > (1 : ℝ), ∃ g : ExtPlane → ExtPlane, IsHomeoOn g D (g '' D) ∧ IsQuasidiskExt (g '' D) ∧
        ∀ (z₀ : ℂ) (r : ℝ), 0 < r → toExt (ball z₀ r) ⊆ D →
          ∃ G : ExtPlane → ExtPlane, IsKQuasiconformal G univ K ∧ ∀ z ∈ ball z₀ r, G z = g z := by
  sorry

/-- **Remark 2.3** (§2, l. 107; its claim is used in the proofs of Corollary 2.4 and Theorem 3.1). The proof of
Theorem 2.2 shows that `S_f` is in `T̄` if for some fixed `c ≥ 1` and each `K > 1` there exists a homeomorphism `g` of
`D` onto a quasidisk such that `g|B` has a `K`-quasiconformal extension to `ℂ̄` for all `B = B(z₀, r)` in `D` with
`c r ≤ dist(z₀, ∂D)`.
Modelling: as in `thm2_2`; the fixed `c` is a parameter of the statement. -/
theorem rem2_3 {f : ℂ → ℂ} (hf : IsUnivMero f unitDisc) {D : Set ExtPlane} (hD : meroToExt f '' unitDisc = D)
    {c : ℝ} (hc : 1 ≤ c)
    (hg : ∀ K > (1 : ℝ), ∃ g : ExtPlane → ExtPlane, IsHomeoOn g D (g '' D) ∧ IsQuasidiskExt (g '' D) ∧
      ∀ (z₀ : ℂ) (r : ℝ), 0 < r → toExt (ball z₀ r) ⊆ D → c * r ≤ infDist z₀ (finitePart (frontier D)) →
        ∃ G : ExtPlane → ExtPlane, IsKQuasiconformal G univ K ∧ ∀ z ∈ ball z₀ r, G z = g z) :
    unitDisc.indicator (schwarzian f) ∈ closureE setT := by
  sorry

/-- **Definition** (§2, l. 109). A domain `D ⊆ ℂ̄` is in `T̄`: `D = f(U)` for a conformal mapping `f` of `U` with `S_f`
in `T̄`. (The paper lets `S`, `T`, `T̄` also denote the families of such images; only `T̄` is used later.) -/
def IsInTbar (D : Set ExtPlane) : Prop :=
  ∃ f : ℂ → ℂ, IsUnivMero f unitDisc ∧ meroToExt f '' unitDisc = D ∧ unitDisc.indicator (schwarzian f) ∈ closureE setT

/-- Helper for `isInTbar_of_mobius` (§2): a function in normal form at `z` which agrees, on a punctured neighbourhood,
with a quotient `P/Q` of analytic germs without a common zero and with non-vanishing Wronskian `P′Q − PQ′` satisfies
the local condition of `LiZhongQC.IsLocUnivMero` at `z`: it is analytic with `u′ ≠ 0`, or it has a simple pole. -/
theorem ag2_ratio_loc {u P Q : ℂ → ℂ} {z : ℂ} (hu : MeromorphicNFAt u z) (hP : AnalyticAt ℂ P z)
    (hQ : AnalyticAt ℂ Q z) (hPQ : Q z = 0 → P z ≠ 0) (hW : deriv P z * Q z - P z * deriv Q z ≠ 0)
    (hgerm : u =ᶠ[𝓝[≠] z] fun w => P w / Q w) :
    (AnalyticAt ℂ u z ∧ deriv u z ≠ 0) ∨ (meromorphicOrderAt u z < 0 ∧
      AnalyticAt ℂ (fun w => (toMeromorphicNFAt u z w)⁻¹) z ∧ deriv (fun w => (toMeromorphicNFAt u z w)⁻¹) z ≠ 0) := by
  by_cases hQz : Q z = 0
  · -- a simple pole: `u = 1/H` with `H = Q/P`, `H(z) = 0`, `H′(z) ≠ 0`
    have hPz := hPQ hQz
    have hH : AnalyticAt ℂ (fun w => Q w / P w) z := hQ.div hP hPz
    have hHd : HasDerivAt (fun w => Q w / P w) ((deriv Q z * P z - Q z * deriv P z) / P z ^ 2) z :=
      hQ.differentiableAt.hasDerivAt.div hP.differentiableAt.hasDerivAt hPz
    have hH' : deriv (fun w => Q w / P w) z ≠ 0 := by
      rw [hHd.deriv]
      refine div_ne_zero ?_ (pow_ne_zero 2 hPz)
      rw [hQz] at hW ⊢
      intro h
      apply hW
      linear_combination -h
    have hH0 : (fun w => Q w / P w) z = 0 := by
      show Q z / P z = 0
      rw [hQz, zero_div]
    have hinvNF : MeromorphicNFAt (fun w => (Q w / P w)⁻¹) z := hH.meromorphicNFAt.inv
    have hgerm' : u =ᶠ[𝓝[≠] z] fun w => (Q w / P w)⁻¹ :=
      hgerm.trans (Filter.Eventually.of_forall fun w => (inv_div (Q w) (P w)).symm)
    have hloc : u =ᶠ[𝓝 z] fun w => (Q w / P w)⁻¹ :=
      (hu.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hinvNF).1 hgerm'
    have hord1 : meromorphicOrderAt (fun w => Q w / P w) z = 1 := by
      rw [hH.meromorphicOrderAt_eq, hH.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hH0 hH']
      rfl
    have hord : meromorphicOrderAt u z = -1 := by
      rw [meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds)]
      show meromorphicOrderAt (fun w => Q w / P w)⁻¹ z = -1
      rw [meromorphicOrderAt_inv, hord1]
    have hNF : toMeromorphicNFAt u z = u := toMeromorphicNFAt_eq_self.mpr hu
    rw [hNF]
    have hloc' : (fun w => (u w)⁻¹) =ᶠ[𝓝 z] fun w => Q w / P w := by
      filter_upwards [hloc] with w hw
      rw [hw, inv_inv]
    refine Or.inr ⟨by rw [hord]; decide, hH.congr hloc'.symm, ?_⟩
    rw [hloc'.deriv_eq]
    exact hH'
  · have hF : AnalyticAt ℂ (fun w => P w / Q w) z := hP.div hQ hQz
    have hloc : u =ᶠ[𝓝 z] fun w => P w / Q w :=
      (hu.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hF.meromorphicNFAt).1 hgerm
    have hFd : HasDerivAt (fun w => P w / Q w) ((deriv P z * Q z - P z * deriv Q z) / Q z ^ 2) z :=
      hP.differentiableAt.hasDerivAt.div hQ.differentiableAt.hasDerivAt hQz
    refine Or.inl ⟨hF.congr hloc.symm, ?_⟩
    rw [hloc.deriv_eq, hFd.deriv]
    exact div_ne_zero hW (pow_ne_zero 2 hQz)

/-- Helper for `isInTbar_of_mobius` (§2): a Möbius transformation `(a f + b)/(c f + d)` of a locally univalent
meromorphic `f`, converted to normal form on `D`, is locally univalent meromorphic. In a chart `f = G` or `f = 1/G`
of `f` it is the quotient `(aG + b)/(cG + d)`, resp. `(bG + a)/(dG + c)`, with Wronskian `±(ad − bc) G′ ≠ 0`
(`ag2_ratio_loc`). -/
theorem ag2_isLocUnivMero_mobius {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLocUnivMero f D) {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0) :
    IsLocUnivMero (toMeromorphicNFOn (fun w => (a * f w + b) / (c * f w + d)) D) D := by
  have hmero : MeromorphicOn (fun w => (a * f w + b) / (c * f w + d)) D := fun z hz => by
    have h := hf.1 z hz
    fun_prop
  have hNF := meromorphicNFOn_toMeromorphicNFOn (fun w => (a * f w + b) / (c * f w + d)) D
  refine ⟨hNF.meromorphicOn, fun z hz => ?_⟩
  obtain ⟨G, hG, hG', -, hchart⟩ := exists_chart_of_isLocUnivMero hf hz
  have hu := hmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have hdG : ∀ p q : ℂ, deriv (fun w => p * G w + q) z = p * deriv G z := fun p q =>
    ((hG.differentiableAt.hasDerivAt.const_mul p).add_const q).deriv
  have hlin : ∀ p q : ℂ, AnalyticAt ℂ (fun w => p * G w + q) z := fun p q =>
    (analyticAt_const.mul hG).add analyticAt_const
  rcases hchart with hfG | hfG
  · refine ag2_ratio_loc (P := fun w => a * G w + b) (Q := fun w => c * G w + d) (hNF hz) (hlin a b) (hlin c d)
      (fun hQ hP => hdet ?_) ?_ ?_
    · beta_reduce at hQ hP
      have hb : b = -(a * G z) := by linear_combination hP
      have hd : d = -(c * G z) := by linear_combination hQ
      rw [hb, hd]
      ring
    · rw [hdG, hdG]
      rw [show a * deriv G z * (c * G z + d) - (a * G z + b) * (c * deriv G z) = deriv G z * (a * d - b * c) by
        ring]
      exact mul_ne_zero hG' hdet
    · filter_upwards [hu, hfG] with w hw hw'
      simp only [hw, hw']
  · have hGne : ∀ᶠ w in 𝓝[≠] z, G w ≠ 0 :=
      hG.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon =>
        hG' ((Filter.EventuallyEq.deriv_eq hcon).trans (deriv_const z 0))
    refine ag2_ratio_loc (P := fun w => b * G w + a) (Q := fun w => d * G w + c) (hNF hz) (hlin b a) (hlin d c)
      (fun hQ hP => hdet ?_) ?_ ?_
    · beta_reduce at hQ hP
      have ha : a = -(b * G z) := by linear_combination hP
      have hc : c = -(d * G z) := by linear_combination hQ
      rw [ha, hc]
      ring
    · rw [hdG, hdG]
      rw [show b * deriv G z * (d * G z + c) - (b * G z + a) * (d * deriv G z) = -(deriv G z * (a * d - b * c)) by
        ring]
      exact neg_ne_zero.2 (mul_ne_zero hG' hdet)
    · filter_upwards [hu, hfG, hGne] with w hw hw' hw''
      simp only [hw, hw']
      have e1 : b * G w + a = (a * (G w)⁻¹ + b) * G w := by
        rw [add_mul, mul_assoc, inv_mul_cancel₀ hw'', mul_one]
        ring
      have e2 : d * G w + c = (c * (G w)⁻¹ + d) * G w := by
        rw [add_mul, mul_assoc, inv_mul_cancel₀ hw'', mul_one]
        ring
      rw [e1, e2, mul_div_mul_right _ _ hw'']

/-- **Unlabelled claim** (§2, l. 109; cited "as noted above" in the proof of Corollary 2.4). If `g` is a Möbius
transformation, then `D` is in `T̄` whenever `g(D)` is in `T̄`. -/
theorem isInTbar_of_mobius {D : Set ExtPlane} {g : ExtPlane → ExtPlane} (hg : IsMobius g) (hD : IsInTbar (g '' D)) :
    IsInTbar D := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hg
  obtain ⟨f, hf, himg, hT⟩ := hD
  -- `u = g⁻¹ ∘ f`, in normal form on the disc
  have hdet' : d * a - -b * -c ≠ 0 := by
    intro h
    apply hdet
    linear_combination h
  have hmero : MeromorphicOn (fun w => (d * f w + -b) / (-c * f w + a)) unitDisc := fun z hz => by
    have h := hf.1.1 z hz
    fun_prop
  set u := toMeromorphicNFOn (fun w => (d * f w + -b) / (-c * f w + a)) unitDisc with hu
  have hloc : IsLocUnivMero u unitDisc := ag2_isLocUnivMero_mobius hf.1 hdet'
  have hS : ∀ z ∈ unitDisc, schwarzian u z = schwarzian f z := fun z hz => by
    rw [schwarzian_congr (hmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz)]
    exact schwarzian_mobius_comp hf.1 hdet' hz
  have hUc : IsConnected unitDisc := (convex_ball (0 : ℂ) 1).isConnected (nonempty_ball.2 one_pos)
  have huniv : IsUnivMero u unitDisc := s21g_isUnivMero_of_schwarzian_eq isOpen_ball hUc hloc hf hS
  -- the `ℂ̄`-values of `u` are those of `g⁻¹ ∘ f`
  have hext : ∀ z ∈ unitDisc, meroToExt u z = mobiusExt d (-b) (-c) a (meroToExt f z) := by
    intro z hz
    obtain ⟨G, hG, hG', -, hfG⟩ := exists_chart_of_isLocUnivMero hf.1 hz
    refine s21g_c_meroToExt_mobius hG hG' hdet' hfG ?_
    filter_upwards [hmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz] with y hy _
    exact hy
  refine ⟨u, huniv, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hext z hz]
      obtain ⟨q, hq, hqe⟩ : meroToExt f z ∈ mobiusExt a b c d '' D := himg ▸ mem_image_of_mem _ hz
      rw [← hqe, mobiusExt_inv_apply hdet]
      exact hq
    · intro hp
      obtain ⟨z, hz, hze⟩ : mobiusExt a b c d p ∈ meroToExt f '' unitDisc := himg ▸ mem_image_of_mem _ hp
      exact ⟨z, hz, by rw [hext z hz, hze, mobiusExt_inv_apply hdet]⟩
  · have hind : unitDisc.indicator (schwarzian u) = unitDisc.indicator (schwarzian f) := by
      funext z
      by_cases hz : z ∈ unitDisc
      · rw [indicator_of_mem hz, indicator_of_mem hz, hS z hz]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz]
    rw [hind]
    exact hT

/-- **Corollary 2.4** (§2). A domain `D` is in `T̄` if for each `K > 1` there exists a `K`-quasiconformal self-mapping
`g` of `ℂ̄` with `g(D)` in `T̄`.
Modelling: "domain" is `References.IsDomainExt` (open and connected in `ℂ̄`). -/
theorem cor2_4 {D : Set ExtPlane} (hD : IsDomainExt D)
    (h : ∀ K > (1 : ℝ), ∃ g : ExtPlane → ExtPlane, IsKQuasiconformal g univ K ∧ IsInTbar (g '' D)) :
    IsInTbar D := by
  sorry

end AstalaGehring1990
