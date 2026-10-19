import References.Pommerenke1992.Ch01.S01_SetsAndCurves
import References.LehtoVirtanen1973.Ch01.S08_ExtensionTheorems
import LiZhongQC.Ch05.S19_Schwarzian

/-!
# Pommerenke 1992, Ch. 1 §1.2 Conformal Maps

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 313–493.

* Definition (conformal map of a domain `H ⊆ Ĉ` onto or into `G ⊆ Ĉ`; univalent function, §1.2.1) — exists:
  `LehtoVirtanen1973.IsConformalMap` (continuous, injective and analytic in the charts of the sphere, that is,
  meromorphic and injective; the image is stated separately)
* Definition (locally univalent function, §1.2.1 (c)) — exists: `LiZhongQC.IsLocUnivMero` (meromorphic, with a
  non-vanishing derivative at the finite values and only simple poles, the latter as a non-vanishing derivative of
  1/f; for analytic functions the statements write the non-vanishing of the derivative directly)
* Reflection Principle (quoted, §1.2.1) — `reflection_principle`
* Definition (simply connected domain, §1.2.2) — exists: `LehtoVirtanen1973.IsSimplyConnectedDomain` (a domain of
  the sphere with connected complement)
* Riemann Mapping Theorem (§1.2.2) — `riemann_mapping_theorem`
* Definition (Möbius transformations, the group `Möb`, §1.2.3) — exists: `LiZhongQC.IsMobius`
* Definition (the group `Möb(𝔻)`, §1.2.3) — `mobDisc`
* Formula (1.2.2) (the conformal maps of `𝔻` onto `𝔻` are `(cz + z₀)/(1 + z̄₀ c z)`) — exists:
  `LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc` `LiZhongQC.isConformalOnto_blaschke`
  `LiZhongQC.isConformalOnto_rot` (every conformal self-map of the disc is c (z - a)/(1 - ā z) with |c| = 1,
  |a| < 1; the converse direction is the composition of a rotation after a Blaschke factor, conformal self-maps by
  the second and third declarations; these are the maps (1.2.2) with z₀ = -c a)
* Formula (1.2.3) — `eq1_2_3`
* Formula (1.2.4) — `eq1_2_4`
* Definition (the non-euclidean metric `λ` (1.2.5); the non-euclidean segment, §1.2.4) — `hypDistD`,
  `nonEuclideanSegment`
* Unlabelled (§1.2.4, l. 405: the minimum in (1.2.5) is attained for the non-euclidean segment) —
  `hypDistD_attained`
* Formula (1.2.6) — `eq1_2_6`
* Formula (1.2.7) — `eq1_2_7`
* Formula (1.2.8) — `eq1_2_8`
* Definition (Stolz angle (1.2.10); angular limit (1.2.11); unrestricted limit (1.2.12), §1.2.5) — `stolzAngleP`,
  `HasAngularLimit`, `HasUnrestrictedLimit`
* Definition (spherical derivative (1.2.14), §1.2.6) — `sphericalDeriv`
* Definition (Schwarzian derivative (1.2.15), §1.2.6) — exists: `LiZhongQC.schwarzian` (the same formula; at a pole
  it is computed from 1/f, as by the inversion of the book)
* Formula (1.2.16) — `eq1_2_16`

Not items (DESIGN §3):
- the elementary properties (a), (b), (d), (e) of conformal maps (quoted from Ahlfors, not cited by label; (c) is
  the definition of local univalence above);
- the consequences of the Riemann mapping theorem at l. 364–366: every simply connected domain of `ℂ` is
  homeomorphic to `ℂ`, and, for `∞ ∈ G`, the map (1.2.1) of `𝔻*` onto `G` with `g(∞) = ∞`, "uniquely determined by
  arg b" (not cited);
- Liouville's theorem on conformal maps of `ℝⁿ`, `n > 2` (a quoted aside outside the subject of the book);
- "the Möbius transformations are the only conformal maps of `Ĉ`" and "Möbius transformations map circles onto
  circles" (l. 382) (standard, not cited);
- (1.2.9) (not cited);
- the bounded distance of Stolz angles from the radius (not cited);
- the notation `f(ζ)` for the angular limit (l. 459);
- the example (1.2.13);
- the rotation invariance of `f#` and the analyticity of `S_f` (not cited);
- (1.2.17) (not cited by number).

**Conventions.** Maps of domains of the sphere are the Lehto–Virtanen reference notions (`IsConformalMap`,
`IsSimplyConnectedDomain`, circles `IsGenCircle`, the reflection `genCircleReflection`, the chart representation
`localRep`). Maps of `𝔻` into `ℂ` are functions `ℂ → ℂ`. The book's non-euclidean metric has curvature `-4`; the
project's `LiZhongQC.metricDist` with the density `2/(1 - |z|²)` is `2λ`, and the constants of §1.3 depend on this
normalization, so `λ` is defined here with the density `1/(1 - |z|²)`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsMobius IsConformalOnto metricDist IsPathIn schwarzian LRCurve
  IsLocUnivMero)
open References (IsDomainExt)
open LehtoVirtanen1973 (IsConformalMap IsSimplyConnectedDomain IsGenCircle genCircleReflection localRep)

/-- **Reflection Principle** (§1.2.1, quoted from Ahlfors). Let `H, G` be domains and `H*, G*` their reflections in
the circles `C, B` of `Ĉ`, and suppose that `H ∩ C = ∅`, `G ∩ B = ∅`. If `f` is a conformal map of `H` onto `G` such
that `f(z) → B` as `z → C`, `z ∈ H`, then `f` can be extended to a conformal map of the set of interior points of
`H ∪ H* ∪ (C ∩ ∂H)`.
Modelling:
- "`f(z) → B` as `z → C`" means that every cluster value of `f` at a point of `C`, taken from `H`, lies on `B`; the
  circle `C` is compact.
- The extension is continuous, injective and analytic in the charts on that open set. It is stated through the
  conditions of `LehtoVirtanen1973.IsConformalMap` without connectedness, because the open set need not be connected
  when `C ∩ ∂H` is small. -/
theorem reflection_principle {H G C B : Set ExtPlane} (hH : IsDomainExt H) (hG : IsDomainExt G)
    (hC : IsGenCircle C) (hB : IsGenCircle B) (hHC : Disjoint H C) (hGB : Disjoint G B)
    {f : ExtPlane → ExtPlane} (hf : IsConformalMap f H) (hfG : f '' H = G)
    (hlim : ∀ p ∈ C, ∀ q, MapClusterPt q (𝓝[H] p) f → q ∈ B) :
    ∃ F : ExtPlane → ExtPlane, EqOn F f H ∧
      ContinuousOn F (interior (H ∪ genCircleReflection C '' H ∪ (C ∩ frontier H))) ∧
      InjOn F (interior (H ∪ genCircleReflection C '' H ∪ (C ∩ frontier H))) ∧
      ∀ z ∈ interior (H ∪ genCircleReflection C '' H ∪ (C ∩ frontier H)),
        DifferentiableAt ℂ (localRep F z) 0 := by
  sorry

/-- The inverse of a conformal map `g` of `𝔻` onto `G` (`Function.invFunOn g 𝔻`): holomorphic on `G`, a bijection
of `G` onto `𝔻`, a two-sided inverse, with `(g⁻¹)'(g(z)) = 1/g'(z)`. -/
theorem p92_1_inverse {g : ℂ → ℂ} {G : Set ℂ} (hg : IsConformalOnto g unitDisc G) :
    DifferentiableOn ℂ (Function.invFunOn g unitDisc) G ∧ BijOn (Function.invFunOn g unitDisc) G unitDisc ∧
      (∀ w ∈ G, g (Function.invFunOn g unitDisc w) = w) ∧
      (∀ z ∈ unitDisc, Function.invFunOn g unitDisc (g z) = z) ∧
      ∀ z ∈ unitDisc, HasDerivAt (Function.invFunOn g unitDisc) (deriv g z)⁻¹ (g z) := by
  obtain ⟨hd, hinj, himg⟩ := hg
  have hb : BijOn g unitDisc G := ⟨fun z hz => himg ▸ mem_image_of_mem g hz, hinj, himg.symm.subset⟩
  have hinvd := RMT.differentiableOn_invFunOn_of_injOn isOpen_ball hd hinj
  change IsOpen (g '' unitDisc) ∧ DifferentiableOn ℂ (Function.invFunOn g unitDisc) (g '' unitDisc) at hinvd
  rw [himg] at hinvd
  have hright : ∀ w ∈ G, g (Function.invFunOn g unitDisc w) = w := fun w hw =>
    Function.invFunOn_eq (show w ∈ g '' unitDisc from himg ▸ hw)
  have hleft : ∀ z ∈ unitDisc, Function.invFunOn g unitDisc (g z) = z := fun z hz =>
    hinj.leftInvOn_invFunOn hz
  refine ⟨hinvd.2, hb.invOn_invFunOn.symm.bijOn hb.surjOn.mapsTo_invFunOn hb.mapsTo, hright, hleft,
    fun z hz => ?_⟩
  have hgz : g z ∈ G := hb.mapsTo hz
  have hcont : ContinuousAt (Function.invFunOn g unitDisc) (g z) :=
    (hinvd.2.differentiableAt (hinvd.1.mem_nhds hgz)).continuousAt
  have hderiv : HasDerivAt g (deriv g z) (Function.invFunOn g unitDisc (g z)) := by
    rw [hleft z hz]
    exact (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hne : deriv g z ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hd hinj hz
  exact HasDerivAt.of_local_left_inverse hcont hderiv hne
    (Filter.eventually_of_mem (hinvd.1.mem_nhds hgz) hright)

/-- For a conformal map `g` of `𝔻` onto `G` with `g(0) = w₀` and `g'(0) = |g'(0)| e^{iα}`, the map
`w ↦ e^{iα} g⁻¹(w)` is a competitor of the project's Riemann mapping theorem (`RMT.IsCompetitor`: `G → 𝔻`, injective,
`w₀ ↦ 0`, positive derivative at `w₀`) and a bijection of `G` onto `𝔻`. -/
theorem p92_1_competitor {g : ℂ → ℂ} {G : Set ℂ} (hg : IsConformalOnto g unitDisc G) {w₀ : ℂ} (hg0 : g 0 = w₀)
    {α : ℝ} (hga : deriv g 0 = (‖deriv g 0‖ : ℂ) * exp (α * I)) :
    RMT.IsCompetitor G w₀ (fun w => exp (α * I) * Function.invFunOn g unitDisc w) ∧
      BijOn (fun w => exp (α * I) * Function.invFunOn g unitDisc w) G unitDisc := by
  obtain ⟨hd, hb, -, hleft, hder⟩ := p92_1_inverse hg
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hne : deriv g 0 ≠ 0 := LiZhongQC.kb_deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0
  have hnorm : (‖deriv g 0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
  have hrot := LiZhongQC.isConformalOnto_rot (c := exp (α * I)) (by rw [Complex.norm_exp_ofReal_mul_I])
  have hbij : BijOn (fun w => exp (α * I) * Function.invFunOn g unitDisc w) G unitDisc := by
    have hrb : BijOn (fun z => exp (α * I) * z) unitDisc unitDisc :=
      ⟨hrot.mapsTo, hrot.2.1, hrot.2.2.symm.subset⟩
    exact hrb.comp hb
  have hD : HasDerivAt (fun w => exp (α * I) * Function.invFunOn g unitDisc w)
      (exp (α * I) * (deriv g 0)⁻¹) w₀ := by
    have := (hder 0 h0).const_mul (exp (α * I))
    rwa [hg0] at this
  have hval : exp (α * I) * (deriv g 0)⁻¹ = ((‖deriv g 0‖⁻¹ : ℝ) : ℂ) := by
    have e : (deriv g 0)⁻¹ = ((‖deriv g 0‖ : ℂ))⁻¹ * (exp (α * I))⁻¹ := by
      conv_lhs => rw [hga]
      rw [mul_inv]
    rw [e, ← mul_assoc, mul_comm (exp (α * I)), mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one,
      Complex.ofReal_inv]
  refine ⟨⟨(hd.const_mul _), hbij.injOn, hbij.mapsTo, ?_, ?_, ?_⟩, hbij⟩
  · show exp (α * I) * Function.invFunOn g unitDisc w₀ = 0
    rw [← hg0, hleft 0 h0, mul_zero]
  · rw [hD.deriv, hval, Complex.ofReal_im]
  · rw [hD.deriv, hval, Complex.ofReal_re]
    exact inv_pos.2 (norm_pos_iff.2 hne)

/-- **Riemann Mapping Theorem** (§1.2.2). Let `G ⊊ ℂ` be a simply connected domain and let `w₀ ∈ G`,
`0 ≤ α < 2π`. Then there is a unique conformal map `f` of `𝔻` onto `G` such that `f(0) = w₀` and
`arg f'(0) = α`.
Modelling: "simply connected" is `LehtoVirtanen1973.IsSimplyConnectedDomain` of `G ⊆ Ĉ`; `arg f'(0) = α` is written
`f'(0) = |f'(0)| e^{iα}` (`f'(0) ≠ 0` for a conformal map), which avoids the branch of `arg`; uniqueness is equality
on `𝔻`. -/
theorem riemann_mapping_theorem {G : Set ℂ} (hG : IsSimplyConnectedDomain (toExt G)) (hGne : G ≠ univ)
    {w₀ : ℂ} (hw₀ : w₀ ∈ G) {α : ℝ} (hα : α ∈ Ico 0 (2 * π)) :
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc G ∧ f 0 = w₀ ∧
      deriv f 0 = (‖deriv f 0‖ : ℂ) * exp (α * I) ∧
      ∀ g : ℂ → ℂ, IsConformalOnto g unitDisc G → g 0 = w₀ →
        deriv g 0 = (‖deriv g 0‖ : ℂ) * exp (α * I) → EqOn g f unitDisc := by
  -- the range `0 ≤ α < 2π` only fixes the branch of `arg f'(0)`; it is not needed in this form
  have _hα : 0 ≤ α := hα.1
  obtain ⟨⟨hGo', hGc'⟩, hpre⟩ := hG
  have hGo : IsOpen G := OnePoint.isOpen_image_coe.1 hGo'
  have hGc : IsConnected G :=
    ⟨⟨w₀, hw₀⟩, (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 hGc'.2⟩
  have hcc : IsConnected (toExt G)ᶜ := ⟨⟨extInf, fun ⟨z, _, hz⟩ => OnePoint.coe_ne_infty z hz⟩, hpre⟩
  have hH := LiZhongQC.hasHolomorphicSqrt_of_isConnected_compl hGo hGc hcc
  obtain ⟨φ, hφ, hφb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hGo hGc (nonempty_compl.2 hGne) hH hw₀
  obtain ⟨hψd, hψb⟩ := RMT.invFunOn_riemannMap hGo hφ.diff hφ.injOn hφb
  set ψ := Function.invFunOn φ G with hψdef
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hψ0 : ψ 0 = w₀ := by
    rw [hψdef, ← hφ.center]
    exact hφ.injOn.leftInvOn_invFunOn hw₀
  have hφψ : ∀ y ∈ unitDisc, φ (ψ y) = y := fun y hy => Function.invFunOn_eq (hφb.surjOn hy)
  have hφd : HasDerivAt φ (deriv φ w₀) (ψ 0) := by
    rw [hψ0]
    exact (hφ.diff.differentiableAt (hGo.mem_nhds hw₀)).hasDerivAt
  have hφ0 : deriv φ w₀ ≠ 0 := fun h => by have := hφ.re_pos; rw [h] at this; simp at this
  have hψder : HasDerivAt ψ (deriv φ w₀)⁻¹ 0 :=
    HasDerivAt.of_local_left_inverse (hψd.differentiableAt (isOpen_ball.mem_nhds h0)).continuousAt hφd hφ0
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds h0) hφψ)
  have hreal : deriv φ w₀ = ((deriv φ w₀).re : ℂ) := Complex.ext (by simp) (by simp [hφ.im_zero])
  have hrot := LiZhongQC.isConformalOnto_rot (c := exp (α * I)) (by rw [Complex.norm_exp_ofReal_mul_I])
  have hψc : IsConformalOnto ψ unitDisc G := ⟨hψd, hψb.injOn, hψb.image_eq⟩
  have hfc : IsConformalOnto (ψ ∘ fun z => exp (α * I) * z) unitDisc G := hψc.comp hrot
  have hfd : HasDerivAt (ψ ∘ fun z => exp (α * I) * z) ((deriv φ w₀)⁻¹ * exp (α * I)) 0 := by
    have hr : HasDerivAt (fun z : ℂ => exp (α * I) * z) (exp (α * I)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (exp (α * I))
    have hψder' : HasDerivAt ψ (deriv φ w₀)⁻¹ (exp (α * I) * 0) := by rwa [mul_zero]
    exact hψder'.comp (0 : ℂ) hr
  have hfa : deriv (ψ ∘ fun z => exp (α * I) * z) 0 =
      (‖deriv (ψ ∘ fun z => exp (α * I) * z) 0‖ : ℂ) * exp (α * I) := by
    rw [hfd.deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, hreal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hφ.re_pos]
    push_cast
    rfl
  have hf0 : (ψ ∘ fun z => exp (α * I) * z) 0 = w₀ := by simp [hψ0]
  refine ⟨ψ ∘ fun z => exp (α * I) * z, hfc, hf0, hfa, fun g hg hg0 hga z hz => ?_⟩
  obtain ⟨hcg, hbg⟩ := p92_1_competitor hg hg0 hga
  obtain ⟨hcf, hbf⟩ := p92_1_competitor hfc hf0 hfa
  have huniq := RMT.riemannMap_unique hGo hGc hw₀ hcg hbg hcf hbf
  obtain ⟨-, -, hrf, -, -⟩ := p92_1_inverse hfc
  obtain ⟨-, -, -, hlg, -⟩ := p92_1_inverse hg
  have hgz : g z ∈ G := hg.2.2 ▸ mem_image_of_mem g hz
  have h1 := huniq hgz
  simp only at h1
  rw [hlg z hz] at h1
  have h2 : Function.invFunOn (ψ ∘ fun z => exp (α * I) * z) unitDisc (g z) = z :=
    (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  rw [← hrf (g z) hgz, h2]

/-- **Definition** (§1.2.3). The group `Möb(𝔻) = {τ ∈ Möb : τ(𝔻) = 𝔻}` of the conformal maps of `𝔻` onto `𝔻`. -/
def mobDisc : Set (ExtPlane → ExtPlane) :=
  {τ | IsMobius τ ∧ τ '' toExt unitDisc = toExt unitDisc}

/-- **Formula (1.2.3)** (§1.2.3; cited in §1.2). `(1 - |z|²)|τ'(z)| = 1 - |τ(z)|²` for `z ∈ 𝔻` and `τ ∈ Möb(𝔻)`.
Modelling: `τ` is a conformal map of `𝔻` onto `𝔻` (these are the maps of `Möb(𝔻)`, (1.2.2)), as in `eq1_2_4`. The
project's `LiZhongQC.poincareDensityDisc_rotBlaschke` is this identity for the explicit maps `c M_a`. -/
theorem eq1_2_3 {τ : ℂ → ℂ} (hτ : IsConformalOnto τ unitDisc unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) * ‖deriv τ z‖ = 1 - ‖τ z‖ ^ 2 := by
  obtain ⟨c, a, hc, ha, hEq⟩ := LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hτ
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hderiv : deriv τ z = deriv (fun w => c * LiZhongQC.blaschke a w) z :=
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hEq)
  have h := LiZhongQC.poincareDensityDisc_rotBlaschke hc ha hz'
  have hτz : τ z = c * LiZhongQC.blaschke a z := hEq hz
  rw [← hderiv, ← hτz] at h
  have hτzD : τ z ∈ unitDisc := hτ.2.2 ▸ mem_image_of_mem τ hz
  have hτ1 : ‖τ z‖ < 1 := mem_ball_zero_iff.1 hτzD
  have h1 : 0 < 1 - ‖τ z‖ ^ 2 := by nlinarith [norm_nonneg (τ z)]
  have h2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  simp only [LiZhongQC.poincareDensityDisc] at h
  rw [div_mul_eq_mul_div, div_eq_div_iff h1.ne' h2.ne'] at h
  linarith

/-- **Formula (1.2.4)** (§1.2.3; cited as (1.2.4)). If `f` is analytic in `𝔻`, `τ ∈ Möb(𝔻)` and `h = f ∘ τ`, then
`(1 - |z|²)|h'(z)| = (1 - |τ(z)|²)|f'(τ(z))|` for `z ∈ 𝔻`.
Modelling: `τ` is a conformal map of `𝔻` onto `𝔻` (these are the maps of `Möb(𝔻)`, (1.2.2)). -/
theorem eq1_2_4 {f τ : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hτ : IsConformalOnto τ unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) * ‖deriv (f ∘ τ) z‖ = (1 - ‖τ z‖ ^ 2) * ‖deriv f (τ z)‖ := by
  have hτz : τ z ∈ unitDisc := hτ.2.2 ▸ mem_image_of_mem τ hz
  have hfd : DifferentiableAt ℂ f (τ z) := hf.differentiableAt (isOpen_ball.mem_nhds hτz)
  have hτd : DifferentiableAt ℂ τ z := hτ.1.differentiableAt (isOpen_ball.mem_nhds hz)
  rw [deriv_comp z hfd hτd, norm_mul, ← eq1_2_3 hτ hz]
  ring

/-- **Definition (1.2.5)** (§1.2.4). The non-euclidean (hyperbolic) metric of `𝔻`:
`λ(z₁, z₂) = min_C ∫_C |dz|/(1 - |z|²)`, the minimum over the curves `C` in `𝔻` from `z₁` to `z₂`.
Modelling: the project's `LiZhongQC.metricDist` (the infimum over rectifiable curves) with the density
`1/(1 - |z|²)`; the value is finite for `z₁, z₂ ∈ 𝔻`, which is the domain of discourse. -/
def hypDistD (z₁ z₂ : ℂ) : ℝ :=
  (metricDist unitDisc (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))) z₁ z₂).toReal

/-- **Definition** (§1.2.4). The non-euclidean segment from `z₁` to `z₂` in `𝔻`: the arc from `z₁` to `z₂` of the
circle through them orthogonal to `𝕋`, that is, the image of the radius `[0, w]`, `w = (z₂ - z₁)/(1 - z̄₁ z₂)`, under
the map `u ↦ (u + z₁)/(1 + z̄₁ u)` of `Möb(𝔻)` (a segment when the circle is a line). -/
def nonEuclideanSegment (z₁ z₂ : ℂ) : Set ℂ :=
  {z | ∃ t ∈ Icc (0 : ℝ) 1,
    z = ((t : ℂ) * ((z₂ - z₁) / (1 - conj z₁ * z₂)) + z₁) /
      (1 + conj z₁ * ((t : ℂ) * ((z₂ - z₁) / (1 - conj z₁ * z₂))))}

/-- The `ρ`-length for the project's Poincaré density `2/(1 - |z|²)` is twice that for `1/(1 - |z|²)`. -/
theorem p92_1_rhoLength_two_mul (γ : LRCurve) :
    γ.rhoLength (fun z => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z)) =
      2 * γ.rhoLength (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))) := by
  have hρ : (fun z : ℂ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z)) =
      fun z => 2 * ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) := by
    funext z
    rw [LiZhongQC.poincareDensityDisc, show (2 : ℝ) / (1 - ‖z‖ ^ 2) = 2 * (1 / (1 - ‖z‖ ^ 2)) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [hρ]
  simp only [LiZhongQC.LRCurve.rhoLength, mul_assoc]
  exact MeasureTheory.lintegral_const_mul' _ _ (by simp)

/-- The project's Poincaré distance (density `2/(1 - |z|²)`) is twice the distance of the density `1/(1 - |z|²)`. -/
theorem p92_1_metricDist_two_mul (z₁ z₂ : ℂ) :
    metricDist unitDisc (fun z => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z)) z₁ z₂ =
      2 * metricDist unitDisc (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))) z₁ z₂ := by
  show (⨅ γ ∈ {γ : LRCurve | IsPathIn unitDisc z₁ z₂ γ},
      γ.rhoLength (fun z => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z))) =
    2 * ⨅ γ ∈ {γ : LRCurve | IsPathIn unitDisc z₁ z₂ γ}, γ.rhoLength (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)))
  simp only [p92_1_rhoLength_two_mul]
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by simp)]
  congr 1
  funext γ
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by simp)]

/-- (1.2.8) (the content of `eq1_2_8`, stated here for use in §1.2.4): from the project's `LiZhongQC.eq14_3`. -/
theorem p92_1_hypDistD_eq {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    hypDistD z₁ z₂ = 1 / 2 * Real.log ((1 + ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖) /
      (1 - ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖)) := by
  have h := LiZhongQC.eq14_3 h₁ h₂
  rw [p92_1_metricDist_two_mul] at h
  have hb : ‖(z₂ - z₁) / (1 - conj z₁ * z₂)‖ < 1 :=
    LiZhongQC.blaschke_mem_unitDisc (mem_ball_zero_iff.1 h₁) (mem_ball_zero_iff.1 h₂)
  have he : ‖(z₂ - z₁) / (1 - conj z₁ * z₂)‖ = ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖ := by
    rw [norm_div, norm_sub_rev]
  rw [he] at h hb
  have hx0 : 0 ≤ ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖ := by positivity
  have hL : 0 ≤ Real.log ((1 + ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖) / (1 - ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at h'
  simp only [ENNReal.toReal_ofNat] at h'
  unfold hypDistD
  linarith

/-- The pseudo-hyperbolic ratio `|z₁ - z₂|/|1 - z̄₁ z₂|` is invariant under the maps `c M_a` of `Möb(𝔻)`. -/
theorem p92_1_pseudo_rotBlaschke {c a z₁ z₂ : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) (h₁ : ‖z₁‖ < 1)
    (h₂ : ‖z₂‖ < 1) :
    ‖c * LiZhongQC.blaschke a z₁ - c * LiZhongQC.blaschke a z₂‖ /
        ‖1 - conj (c * LiZhongQC.blaschke a z₁) * (c * LiZhongQC.blaschke a z₂)‖ =
      ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖ := by
  have hD1 := LiZhongQC.blaschke_den_ne_zero ha h₁
  have hD2 := LiZhongQC.blaschke_den_ne_zero ha h₂
  have hD1' : (1 : ℂ) - a * conj z₁ ≠ 0 := by
    intro h0
    apply hD1
    have := congrArg conj h0
    simpa [mul_comm] using this
  have hD1c : (1 : ℂ) - z₁ * conj a ≠ 0 := by rwa [mul_comm]
  have hD2c : (1 : ℂ) - z₂ * conj a ≠ 0 := by rwa [mul_comm]
  have hD1'c : (1 : ℂ) - conj z₁ * a ≠ 0 := by rwa [mul_comm]
  have hcc : conj c * c = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hA : (1 : ℂ) - a * conj a ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    have : normSq a < 1 := LiZhongQC.normSq_lt_one_iff.mpr ha
    linarith
  have hX : c * LiZhongQC.blaschke a z₁ - c * LiZhongQC.blaschke a z₂ =
      c * (1 - a * conj a) * (z₁ - z₂) / ((1 - conj a * z₁) * (1 - conj a * z₂)) := by
    simp only [LiZhongQC.blaschke]
    field_simp
    ring
  have hY0 : 1 - conj (c * LiZhongQC.blaschke a z₁) * (c * LiZhongQC.blaschke a z₂) =
      1 - conj (LiZhongQC.blaschke a z₁) * LiZhongQC.blaschke a z₂ := by
    rw [map_mul]
    linear_combination (-(conj (LiZhongQC.blaschke a z₁) * LiZhongQC.blaschke a z₂)) * hcc
  have hY1 : 1 - conj (LiZhongQC.blaschke a z₁) * LiZhongQC.blaschke a z₂ =
      (1 - a * conj a) * (1 - conj z₁ * z₂) / ((1 - a * conj z₁) * (1 - conj a * z₂)) := by
    simp only [LiZhongQC.blaschke, map_div₀, map_sub, map_mul, map_one, Complex.conj_conj]
    field_simp
    ring
  have hn : ‖(1 : ℂ) - a * conj z₁‖ = ‖1 - conj a * z₁‖ := by
    rw [← Complex.norm_conj]
    simp [mul_comm]
  rw [hX, hY0, hY1]
  simp only [norm_div, norm_mul, hc, one_mul, hn]
  have hn1 : ‖(1 : ℂ) - a * conj a‖ ≠ 0 := norm_ne_zero_iff.2 hA
  have hn2 : ‖(1 : ℂ) - conj a * z₁‖ ≠ 0 := norm_ne_zero_iff.2 hD1
  have hn3 : ‖(1 : ℂ) - conj a * z₂‖ ≠ 0 := norm_ne_zero_iff.2 hD2
  field_simp

/-- (1.2.7) (the content of `eq1_2_7`, stated here for use in (1.2.6)). -/
theorem p92_1_hypDistD_inv {τ : ℂ → ℂ} (hτ : IsConformalOnto τ unitDisc unitDisc) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) : hypDistD (τ z₁) (τ z₂) = hypDistD z₁ z₂ := by
  obtain ⟨c, a, hc, ha, hEq⟩ := LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hτ
  have hτ₁ : τ z₁ ∈ unitDisc := hτ.2.2 ▸ mem_image_of_mem τ h₁
  have hτ₂ : τ z₂ ∈ unitDisc := hτ.2.2 ▸ mem_image_of_mem τ h₂
  rw [p92_1_hypDistD_eq hτ₁ hτ₂, p92_1_hypDistD_eq h₁ h₂, hEq h₁, hEq h₂,
    p92_1_pseudo_rotBlaschke hc ha (mem_ball_zero_iff.1 h₁) (mem_ball_zero_iff.1 h₂)]

/-- The triangle inequality (1.2.6) through the origin: `λ(a, b) ≤ λ(a, 0) + λ(0, b)`, from
`ρ(a, b) ≤ (|a| + |b|)/(1 + |a||b|)` for the pseudo-hyperbolic ratio `ρ`. -/
theorem p92_1_hypDistD_triangle_zero {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) :
    hypDistD a b ≤ hypDistD a 0 + hypDistD 0 b := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  rw [p92_1_hypDistD_eq ha hb, p92_1_hypDistD_eq ha h0, p92_1_hypDistD_eq h0 hb]
  simp only [sub_zero, mul_zero, map_zero, zero_mul, zero_sub, norm_neg, norm_one, div_one]
  set α := ‖a‖ with hα
  set β := ‖b‖ with hβ
  have hα0 : 0 ≤ α := norm_nonneg a
  have hβ0 : 0 ≤ β := norm_nonneg b
  have hN0 : 0 < ‖1 - conj a * b‖ := norm_pos_iff.2 (LiZhongQC.blaschke_den_ne_zero ha' hb')
  have hNle : ‖1 - conj a * b‖ ≤ 1 + α * β := by
    calc ‖1 - conj a * b‖ ≤ ‖(1 : ℂ)‖ + ‖conj a * b‖ := norm_sub_le _ _
      _ = 1 + α * β := by rw [norm_one, norm_mul, Complex.norm_conj]
  have hkey := LiZhongQC.normSq_blaschke_key a b
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, norm_sub_rev b a] at hkey
  set M := ‖a - b‖ with hM
  set N := ‖1 - conj a * b‖ with hN
  have hM0 : 0 ≤ M := norm_nonneg _
  set s := (α + β) / (1 + α * β) with hs
  have hab1 : 0 < 1 + α * β := by positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one hab1]
    nlinarith
  have hρs : M / N ≤ s := by
    rw [hs, div_le_div_iff₀ hN0 hab1]
    have hsq : (M * (1 + α * β)) ^ 2 ≤ ((α + β) * N) ^ 2 := by
      have hpos : 0 ≤ (1 - α ^ 2) * (1 - β ^ 2) := by
        apply mul_nonneg <;> nlinarith
      have hM2 : M ^ 2 = N ^ 2 - (1 - β ^ 2) * (1 - α ^ 2) := by linarith [hkey]
      have hid : ((α + β) * N) ^ 2 - (M * (1 + α * β)) ^ 2 =
          (1 - α ^ 2) * (1 - β ^ 2) * ((1 + α * β) ^ 2 - N ^ 2) := by
        rw [mul_pow, mul_pow, hM2]
        ring
      nlinarith [mul_nonneg hpos (sub_nonneg.2 (pow_le_pow_left₀ hN0.le hNle 2))]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  have hρ0 : 0 ≤ M / N := by positivity
  have hρ1 : M / N < 1 := lt_of_le_of_lt hρs hs1
  have hmono : (1 + M / N) / (1 - M / N) ≤ (1 + s) / (1 - s) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have e1 : 1 + s = (1 + α) * (1 + β) / (1 + α * β) := by
    rw [hs]
    field_simp
    ring
  have e2 : 1 - s = (1 - α) * (1 - β) / (1 + α * β) := by
    rw [hs]
    field_simp
    ring
  have hprod : (1 + s) / (1 - s) = (1 + α) / (1 - α) * ((1 + β) / (1 - β)) := by
    rw [e1, e2, div_div_div_cancel_right₀ hab1.ne', mul_div_mul_comm]
  have hpos1 : 0 < (1 + M / N) / (1 - M / N) := div_pos (by linarith) (by linarith)
  have hpa : 0 < (1 + α) / (1 - α) := div_pos (by linarith) (by linarith)
  have hpb : 0 < (1 + β) / (1 - β) := div_pos (by linarith) (by linarith)
  calc 1 / 2 * Real.log ((1 + M / N) / (1 - M / N)) ≤ 1 / 2 * Real.log ((1 + s) / (1 - s)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hpos1 hmono) (by norm_num)
    _ = 1 / 2 * Real.log ((1 + α) / (1 - α)) + 1 / 2 * Real.log ((1 + β) / (1 - β)) := by
        rw [hprod, Real.log_mul hpa.ne' hpb.ne']
        ring

/-- The radius `[0, w]` (`LiZhongQC.segCurve w`) is a rectifiable path in `𝔻` for `|w| < 1`. -/
theorem p92_1_isPathIn_segCurve {w : ℂ} (hw : ‖w‖ < 1) : IsPathIn unitDisc 0 w (LiZhongQC.segCurve w) := by
  refine ⟨⟨‖w‖₊, ?_⟩, by simp, by simp, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun a _ b _ => le_of_eq ?_
    rw [LiZhongQC.segCurve_apply, LiZhongQC.segCurve_apply, Complex.dist_eq, ← sub_mul, ← Complex.ofReal_sub,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  · rintro _ ⟨t, ht, rfl⟩
    show (LiZhongQC.segCurve w).toFun t ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, LiZhongQC.segCurve_norm ht.1]
    nlinarith [ht.2, norm_nonneg w]

/-- The density `1/(1 - |z|²)` of `λ` is invariant under the Blaschke factors: `ρ(z) = ρ(M_a z) |M_a'(z)|`. -/
theorem p92_1_density_blaschke {a z : ℂ} (ha : ‖a‖ < 1) (hz : z ∈ unitDisc) :
    ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) =
      ENNReal.ofReal (1 / (1 - ‖LiZhongQC.blaschke a z‖ ^ 2)) * ‖deriv (LiZhongQC.blaschke a) z‖ₑ := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h := LiZhongQC.poincareDensityDisc_rotBlaschke (norm_one : ‖(1 : ℂ)‖ = 1) ha hz'
  simp only [one_mul] at h
  have hb : ‖LiZhongQC.blaschke a z‖ < 1 := LiZhongQC.blaschke_mem_unitDisc ha hz'
  have h1 : 0 < 1 - ‖LiZhongQC.blaschke a z‖ ^ 2 := by nlinarith [norm_nonneg (LiZhongQC.blaschke a z)]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [LiZhongQC.poincareDensityDisc] at h
  have e : 1 / (1 - ‖LiZhongQC.blaschke a z‖ ^ 2) * ‖deriv (LiZhongQC.blaschke a) z‖ =
      (2 / (1 - ‖LiZhongQC.blaschke a z‖ ^ 2) * ‖deriv (LiZhongQC.blaschke a) z‖) / 2 := by ring
  rw [e, h]
  ring

/-- **Unlabelled claim** (§1.2.4, l. 405; part of the definition (1.2.5), cited with it). The minimum in (1.2.5) is
attained for the non-euclidean segment from `z₁` to `z₂`. -/
theorem hypDistD_attained {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    ∃ γ : LRCurve, IsPathIn unitDisc z₁ z₂ γ ∧ γ.closedTrace = nonEuclideanSegment z₁ z₂ ∧
      γ.rhoLength (fun z => ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))) = ENNReal.ofReal (hypDistD z₁ z₂) := by
  have h₁' : ‖z₁‖ < 1 := mem_ball_zero_iff.1 h₁
  have h₂' : ‖z₂‖ < 1 := mem_ball_zero_iff.1 h₂
  have hn₁ : ‖-z₁‖ < 1 := by rwa [norm_neg]
  set w := LiZhongQC.blaschke z₁ z₂ with hwdef
  have hw : ‖w‖ < 1 := LiZhongQC.blaschke_mem_unitDisc h₁' h₂'
  have hT := LiZhongQC.isConformalOnto_blaschke hn₁
  have hmaps : MapsTo (LiZhongQC.blaschke (-z₁)) unitDisc unitDisc := fun z hz =>
    hT.2.2 ▸ mem_image_of_mem _ hz
  obtain ⟨γ, hγeq, hγ⟩ := LiZhongQC.exists_isPathIn_comp isOpen_ball hT.1 hmaps (p92_1_isPathIn_segCurve hw)
  rw [LiZhongQC.blaschke_neg_zero, hwdef, LiZhongQC.blaschke_neg_blaschke h₁' h₂'] at hγ
  refine ⟨γ, hγ, ?_, ?_⟩
  · show γ.toFun '' Icc 0 1 = _
    ext z
    simp only [hγeq, Function.comp, LiZhongQC.segCurve_apply, mem_image,
      nonEuclideanSegment, mem_ofPred_eq, hwdef, LiZhongQC.blaschke, map_neg, sub_neg_eq_add, neg_mul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  · have htr : (LiZhongQC.segCurve w).trace ⊆ unitDisc := fun z hz =>
      (p92_1_isPathIn_segCurve hw).2.2.2 (image_mono Ioo_subset_Icc_self hz)
    rw [LiZhongQC.LRCurve.rhoLength_comp_of_isConformalOnto isOpen_ball hT
      (fun z hz => p92_1_density_blaschke hn₁ hz) htr hγeq]
    have hseg := LiZhongQC.rhoLength_segCurve_of_nonneg (norm_nonneg w) hw rfl
    rw [p92_1_rhoLength_two_mul] at hseg
    have hratio : ‖w‖ = ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖ := by
      rw [hwdef, LiZhongQC.blaschke, norm_div, norm_sub_rev]
    rw [p92_1_hypDistD_eq h₁ h₂, ← hratio]
    have hL : 0 ≤ Real.log ((1 + ‖w‖) / (1 - ‖w‖)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith [norm_nonneg w])
    rw [show Real.log ((1 + ‖w‖) / (1 - ‖w‖)) = 2 * (1 / 2 * Real.log ((1 + ‖w‖) / (1 - ‖w‖))) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at hseg
    exact (ENNReal.mul_right_inj (by norm_num) (by simp)).1 hseg

/-- **Formula (1.2.6)** (§1.2.4; cited as (1.2.6)). The triangle inequality
`λ(z₁, z₃) ≤ λ(z₁, z₂) + λ(z₂, z₃)` for `z₁, z₂, z₃ ∈ 𝔻`. -/
theorem eq1_2_6 {z₁ z₂ z₃ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) (h₃ : z₃ ∈ unitDisc) :
    hypDistD z₁ z₃ ≤ hypDistD z₁ z₂ + hypDistD z₂ z₃ := by
  have hb := LiZhongQC.isConformalOnto_blaschke (mem_ball_zero_iff.1 h₂)
  have hm : ∀ z ∈ unitDisc, LiZhongQC.blaschke z₂ z ∈ unitDisc := fun z hz =>
    hb.2.2 ▸ mem_image_of_mem _ hz
  rw [← p92_1_hypDistD_inv hb h₁ h₃, ← p92_1_hypDistD_inv hb h₁ h₂, ← p92_1_hypDistD_inv hb h₂ h₃,
    LiZhongQC.blaschke_self]
  exact p92_1_hypDistD_triangle_zero (hm z₁ h₁) (hm z₃ h₃)

/-- **Formula (1.2.7)** (§1.2.4; cited as (1.2.7)). The invariance `λ(τ(z₁), τ(z₂)) = λ(z₁, z₂)` for `τ ∈ Möb(𝔻)`.
Modelling: `τ` is a conformal map of `𝔻` onto `𝔻`, as in `eq1_2_4`. -/
theorem eq1_2_7 {τ : ℂ → ℂ} (hτ : IsConformalOnto τ unitDisc unitDisc) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc)
    (h₂ : z₂ ∈ unitDisc) : hypDistD (τ z₁) (τ z₂) = hypDistD z₁ z₂ := by
  exact p92_1_hypDistD_inv hτ h₁ h₂

/-- **Formula (1.2.8)** (§1.2.4; cited as (1.2.8)). For `z₁, z₂ ∈ 𝔻`,
`λ(z₁, z₂) = ½ log((1 + |z₁ - z₂|/|1 - z̄₁ z₂|)/(1 - |z₁ - z₂|/|1 - z̄₁ z₂|))`.
(The project's `LiZhongQC.eq14_3` is this formula for `2λ`.) -/
theorem eq1_2_8 {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    hypDistD z₁ z₂ = 1 / 2 * Real.log ((1 + ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖) /
      (1 - ‖z₁ - z₂‖ / ‖1 - conj z₁ * z₂‖)) := by
  exact p92_1_hypDistD_eq h₁ h₂

/-- **Definition (1.2.10)** (§1.2.5). The Stolz angle at `ζ ∈ 𝕋` with parameters `α, ρ`:
`Δ = {z ∈ 𝔻 : |arg(1 - ζ̄ z)| < α, |z - ζ| < ρ}`. The book requires `0 < α < π/2` and `ρ < 2 cos α`; these
conditions are imposed where Stolz angles are used. -/
def stolzAngleP (ζ : ℂ) (α ρ : ℝ) : Set ℂ :=
  {z | z ∈ unitDisc ∧ |arg (1 - conj ζ * z)| < α ∧ ‖z - ζ‖ < ρ}

/-- **Definition (1.2.11)** (§1.2.5; cited as (1.2.11)). The function `f` from `𝔻` to `Ĉ` has the angular limit `a` at
`ζ ∈ 𝕋`: `f(z) → a` as `z → ζ`, `z ∈ Δ`, for each Stolz angle `Δ` at `ζ`.
Modelling: `ζ ∈ 𝕋` is part of the definition (for `|ζ| > 1` the filters would be trivial). -/
def HasAngularLimit (f : ℂ → ExtPlane) (ζ : ℂ) (a : ExtPlane) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧
    ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α → Tendsto f (𝓝[stolzAngleP ζ α ρ] ζ) (𝓝 a)

/-- **Definition (1.2.12)** (§1.2.5). The function `f` from `𝔻` to `Ĉ` has the unrestricted limit `a` at `ζ ∈ 𝕋`:
`f(z) → a` as `z → ζ`, `z ∈ 𝔻`.
Modelling: `ζ ∈ 𝕋` is part of the definition, as for `HasAngularLimit`. -/
def HasUnrestrictedLimit (f : ℂ → ExtPlane) (ζ : ℂ) (a : ExtPlane) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧ Tendsto f (𝓝[unitDisc] ζ) (𝓝 a)

open scoped Classical in
/-- **Definition (1.2.14)** (§1.2.6). The spherical derivative `f#(z) = |f'(z)|/(1 + |f(z)|²)` of a meromorphic
function.
Modelling: as the project's `LiZhongQC.schwarzian`, the value depends only on the germ of `f`: at a point of
non-negative order it is computed from the normal form of `f` there; at a pole it is the value
`|(1/f)'(z)|/(1 + |1/f(z)|²) = |(1/f)'(z)|` of the book's limit, computed from `1/f` in normal form (`f#` is
invariant under `f ↦ 1/f`). Where `f` is not meromorphic the value is `0` (Mathlib's normal form is `0` there),
outside the domain of discourse. -/
def sphericalDeriv (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 ≤ meromorphicOrderAt f z then
    ‖deriv (toMeromorphicNFAt f z) z‖ / (1 + ‖toMeromorphicNFAt f z z‖ ^ 2)
  else
    ‖deriv (fun w => (toMeromorphicNFAt f z w)⁻¹) z‖ / (1 + ‖(toMeromorphicNFAt f z z)⁻¹‖ ^ 2)

/-- **Formula (1.2.16)** (§1.2.6; cited in §1.2.6). For a locally univalent meromorphic `f` and Möbius
transformations `σ, τ`: `S_{σ ∘ f ∘ τ}(z) = S_f(τ(z)) τ'(z)²`.
Modelling: `σ(w) = (a w + b)/(c w + d)`, `τ(z) = (a' z + b')/(c' z + d')` with non-zero determinants; `z` is a finite
point with `τ(z)` finite and in the domain `D` of `f`. The Schwarzian of the project is computed from the germ, with
poles by inversion. -/
theorem eq1_2_16 {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : IsLocUnivMero f D) {a b c d a' b' c' d' : ℂ}
    (hσ : a * d - b * c ≠ 0) (hτ : a' * d' - b' * c' ≠ 0) {z : ℂ} (hz : c' * z + d' ≠ 0)
    (hzD : (a' * z + b') / (c' * z + d') ∈ D) :
    schwarzian (fun w => (a * f ((a' * w + b') / (c' * w + d')) + b) /
        (c * f ((a' * w + b') / (c' * w + d')) + d)) z =
      schwarzian f ((a' * z + b') / (c' * z + d')) *
        deriv (fun w => (a' * w + b') / (c' * w + d')) z ^ 2 := by
  -- the openness of `D` is not needed: `f` is locally univalent at the point `τ(z) ∈ D`
  have _hD : IsOpen D := hD
  set T : ℂ → ℂ := fun w => (a' * w + b') / (c' * w + d') with hTdef
  have hTd : HasDerivAt T ((a' * d' - b' * c') / (c' * z + d') ^ 2) z := LiZhongQC.hasDerivAt_mobius hz
  have hTa : AnalyticAt ℂ T z :=
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hz
  have hT' : deriv T z ≠ 0 := by
    rw [hTd.deriv]
    exact div_ne_zero hτ (pow_ne_zero _ hz)
  have hST : schwarzian T z = 0 := LiZhongQC.schwarzian_mobius hτ z
  rcases hf.2 _ hzD with ⟨hA, hA'⟩ | ⟨-, hu, hu'⟩
  · have hg : AnalyticAt ℂ (f ∘ T) z := hA.comp_of_eq hTa rfl
    have hg' : deriv (f ∘ T) z ≠ 0 := by
      rw [deriv_comp z hA.differentiableAt hTa.differentiableAt]
      exact mul_ne_zero hA' hT'
    rw [show (fun w => (a * f (T w) + b) / (c * f (T w) + d)) = fun w => (a * (f ∘ T) w + b) / (c * (f ∘ T) w + d)
      from rfl, LiZhongQC.schwarzian_mobius_comp_analytic hg hg' hσ, LiZhongQC.eq19_1_chain_rule hTa hT' hA hA',
      hST, add_zero]
  · set z₀ := T z with hz₀
    set u : ℂ → ℂ := fun w => (toMeromorphicNFAt f z₀ w)⁻¹ with hudef
    have hfu : f =ᶠ[𝓝[≠] z₀] fun w => (u w)⁻¹ := by
      filter_upwards [(hf.1 z₀ hzD).eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [hudef, inv_inv]
      exact hw
    have hden : ∀ᶠ w in 𝓝 z, c' * w + d' ≠ 0 :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne hz
    have hTt : Tendsto T (𝓝[≠] z) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hTa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hden] with w hw hw'
      intro heq
      apply hw
      have h2 : (a' * w + b') * (c' * z + d') = (a' * z + b') * (c' * w + d') := by
        rw [← div_eq_div_iff hw' hz]
        exact heq
      have h3 : (a' * d' - b' * c') * (w - z) = 0 := by linear_combination h2
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hτ)
    have hfuT : (f ∘ T) =ᶠ[𝓝[≠] z] fun w => (u (T w))⁻¹ := hTt.eventually hfu
    have huT : AnalyticAt ℂ (u ∘ T) z := hu.comp_of_eq hTa rfl
    have huT' : deriv (u ∘ T) z ≠ 0 := by
      rw [deriv_comp z hu.differentiableAt hTa.differentiableAt]
      exact mul_ne_zero hu' hT'
    have hune : ∀ᶠ w in 𝓝[≠] z, (u ∘ T) w ≠ 0 := by
      refine huT.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => huT' ?_
      have hz0 : (u ∘ T) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := hcon
      rw [hz0.deriv_eq, deriv_const]
    have hdet : b * c - a * d ≠ 0 := fun hcon => hσ (by linear_combination -hcon)
    have hgerm : (fun w => (a * f (T w) + b) / (c * f (T w) + d)) =ᶠ[𝓝[≠] z]
        fun w => (b * (u ∘ T) w + a) / (d * (u ∘ T) w + c) := by
      filter_upwards [hfuT, hune] with w e hne
      simp only [Function.comp] at e hne ⊢
      rw [e]
      have e1 : a * (u (T w))⁻¹ + b = (b * u (T w) + a) / u (T w) := by field_simp; ring
      have e2 : c * (u (T w))⁻¹ + d = (d * u (T w) + c) / u (T w) := by field_simp; ring
      rw [e1, e2]
      rcases eq_or_ne (d * u (T w) + c) 0 with hd | hd
      · rw [hd, zero_div, div_zero, div_zero]
      · field_simp
    rw [LiZhongQC.schwarzian_congr hgerm, LiZhongQC.schwarzian_mobius_comp_analytic huT huT' hdet,
      LiZhongQC.eq19_1_chain_rule hTa hT' hu hu', hST, add_zero, LiZhongQC.schwarzian_congr hfu,
      LiZhongQC.schwarzian_inv hu hu']

end Pommerenke1992
