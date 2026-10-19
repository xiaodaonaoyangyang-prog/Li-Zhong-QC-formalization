import References.GardinerLakic2000.Ch16.S04_BeurlingAhlforsExtension

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.5 Welding

Source `teichmuller.txt`, lines 12124–12362 (Chapter 16, §16.5); Figure 16.2 from the second OCR (GL1:4819, image).

* Definition (the Riemann maps `f : ℍ* → Ω*`, `g : ℍ → Ω` with their boundary maps; the welding homeomorphism
  `h = g⁻¹ ∘ f`, l. 12125) — `IsRiemannMapLower`, `IsRiemannMapUpper`, `IsWeldingMap`
* Definition 4 (quasicircle, l. 12127) — exists: `LiZhongQC.IsQuasicircle`
* Lemma 5 (l. 12129) — `lemma16_5`
* Definition (the reverse triangle inequality (16.6), l. 12143–12147) — `IsSmallerArcTriple`, `HasReverseTriangle`
* Definition (symmetric homeomorphism of `ℝ̄`, l. 12153; the book's local charts) — `HasVanishingRatioDistortionReal`
* Definition 5 (symmetric quasicircle, l. 12151) — `IsSymmetricQuasicircle`
* Unlabelled (`C` is symmetric iff it is the image of `ℝ̄` under a q.c. map with `K_z → 1` uniformly at `ℝ̄`, l. 12153;
  used in Theorem 4) — `para16_5_symmetric_iff`
* Definition 6 (strong reverse triangle property, l. 12158) — `HasStrongReverseTriangle`
* Definition (`Λ̃₁`, `Λ̃₂`, the extremal lengths of the curves separating two arcs, l. 12163–12168) —
  `sepExtremalLength`
* Definition 7 (extremal length property, l. 12170) — `HasExtremalLengthProperty`
* Definition (disc template, canal, pond, height, canal length, separation, pond length, l. 12172–12182, Figure
  16.2) — `templateCanal`, `templatePond`, `IsDiscTemplateFor`
* Definition (allowable triple, l. 12184) — `IsAllowableTriple`
* Definition 8 (disc template property, l. 12186) — `HasDiscTemplateProperty`
* Theorem 4 (l. 12194) — `thm16_4`
* Lemma 6 (l. 12281) — `lemma16_6`
* Definition (the loops `γ₁`, `γ₂` surrounding an arc; `L₁`, `L₂`, l. 12305–12313) — `IsArcSurroundingLoop`
* Lemma 7 (l. 12319) — `lemma16_7`
* Lemma 8 (l. 12321) — `lemma16_8`

Not items: "any one of `f, g, h` determines the other two" (l. 12125, batch B's Lemma 6.3; U−); Ahlfors' criterion
(l. 12141, quoted, motivation only); (16.7)–(16.14) (proof of Theorem 4). Modelling (E0.6) [reading]: the quasicircle
`C` is normalized to pass through `∞` (all conditions are stated for this normalization), so `C ∖ {∞} ⊆ ℂ`, the
complementary domains `Ω, Ω* ⊆ ℂ` and the Riemann maps are `ℂ`-valued; a Riemann map of `ℍ*` (resp. `ℍ`) comes with
its boundary map on `ℝ` (limits, values in `ℂ̂`) and its value `d = f(∞)`. Points `a, b, c, d` are consecutive when
they are `f(s), f(t), f(u), f(∞)` with `s < t < u` for some Riemann map `f` (every point of `C` is some `f(∞)`), so
the arcs are images of intervals: `α_ab = f[s, t]`, `α_bc = f[t, u]`, `α_cd = f[u, ∞]`, `α_ad = f[−∞, s]`.
Distances are `LehtoVirtanen1973.sphericalDist`, diameters `LehtoVirtanen1973.sphericalDiam`. `Λ̃ = 2π / M(B)` for
the ring domain `B = ℂ̂ ∖ (α ∪ α′)` (`LehtoVirtanen1973.ringModule`; the family "homotopic to `γ₁`" is the separating
family). The disc template is read from Figure 16.2: after the rotation taking `b − a` to the positive axis, the
canal is `{−ρ ≤ x ≤ e, |y| ≤ η/2}` and the pond `{p₁ ≤ x ≤ p₂, |y| ≤ η/2}` in the disc `|z − a| ≤ ρ`; canal length
`ρ + e`, height `η`, separation `p₁ − e`, pond length `p₂ − p₁`. A symmetric homeomorphism of `ℝ̄` is read through
the book's charts (§16.6): `h` and `ĥ(x) = −1/h(−1/x)` have vanishing ratio distortion on `[−2, 2]`; welding maps are
normalized by `h(0) = 0`. In Lemmas 7–8 the four-point extremal lengths are batch D's `extremalLengthLoopRS` on
`X = ℂ ∖ {a, b, c}` (`d = ∞`) of a loop "surrounding" an arc: simple, essential, non-peripheral, with simple freely
homotopic representatives in every neighbourhood of the arc (`IsArcSurroundingLoop`); `Λ₁` is the plane extremal
length (`LiZhongQC.extremalLength`) of the closed curves in the template separating its pond from its canal. The book
calls both of Lemma 7's curves "surrounding `α_bc`"; they are read as the curves around `α_ab` and `α_bc` of
Definition 7 [misprint].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf realLine IsKQC complexDilatation qsRatio Loop
  FreelyHomotopic LRCurve)
open LehtoVirtanen1973 (sphericalDist sphericalDiam ringModule)

/-- **Definition** (§16.5, l. 12125). `f` is a Riemann map of `ℍ*` onto `Ω*`, with boundary map `fb` on `ℝ` and
`f(∞) = d`. -/
def IsRiemannMapLower (Ωs : Set ℂ) (f : ℂ → ℂ) (fb : ℝ → ExtPlane) (d : ExtPlane) : Prop :=
  DifferentiableOn ℂ f lowerHalf ∧ InjOn f lowerHalf ∧ f '' lowerHalf = Ωs ∧
    (∀ x : ℝ, Tendsto (fun z => (f z : ExtPlane)) (𝓝[lowerHalf] (x : ℂ)) (𝓝 (fb x))) ∧
    Tendsto (fun z => (f z : ExtPlane)) (Bornology.cobounded ℂ ⊓ 𝓟 lowerHalf) (𝓝 d)

/-- **Definition** (§16.5, l. 12125). `g` is a Riemann map of `ℍ` onto `Ω`, with boundary map `gb` and `g(∞) = d`. -/
def IsRiemannMapUpper (Ω : Set ℂ) (g : ℂ → ℂ) (gb : ℝ → ExtPlane) (d : ExtPlane) : Prop :=
  DifferentiableOn ℂ g upperHalf ∧ InjOn g upperHalf ∧ g '' upperHalf = Ω ∧
    (∀ x : ℝ, Tendsto (fun z => (g z : ExtPlane)) (𝓝[upperHalf] (x : ℂ)) (𝓝 (gb x))) ∧
    Tendsto (fun z => (g z : ExtPlane)) (Bornology.cobounded ℂ ⊓ 𝓟 upperHalf) (𝓝 d)

/-- **Definition** (welding homeomorphism, §16.5, l. 12125). `h = g⁻¹ ∘ f` on `ℝ̄` for Riemann maps `f : ℍ* → Ω*`,
`g : ℍ → Ω` with `f(∞) = g(∞)` (so that `h` fixes `∞`). -/
def IsWeldingMap (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (fb gb : ℝ → ExtPlane) (d : ExtPlane) (h : ℝ → ℝ) : Prop :=
  IsRiemannMapLower Ωs f fb d ∧ IsRiemannMapUpper Ω g gb d ∧ Continuous h ∧ StrictMono h ∧
    Tendsto h atTop atTop ∧ Tendsto h atBot atBot ∧ ∀ x : ℝ, fb x = gb (h x)

/-- Helper for `lemma16_5` (§16.5). Two disjoint open connected sets covering `Cᶜ` are the two complementary
components of the Jordan curve `C ∪ {∞}`. -/
theorem gl16_components {C Ω Ωs : Set ℂ} (hJ : LiZhongQC.IsJordanCurve (toExt C ∪ {extInf})) (hΩ : IsOpen Ω)
    (hΩs : IsOpen Ωs) (hc : IsConnected Ω) (hcs : IsConnected Ωs) (hdisj : Disjoint Ω Ωs) (hcov : Ω ∪ Ωs = Cᶜ) :
    LiZhongQC.AreComplementaryComponents (toExt C ∪ {extInf}) (toExt Ω) (toExt Ωs) := by
  have hS : (toExt C ∪ {extInf})ᶜ = toExt Ω ∪ toExt Ωs := by
    ext p
    rcases LiZhongQC.uq_j_eq_infty_or_coe p with rfl | ⟨z, rfl⟩
    · simp [LiZhongQC.wd_n_infty_notMem_toExt]
    · have hz : ((z : ℂ) : ExtPlane) ≠ extInf := OnePoint.coe_ne_infty z
      simp only [mem_compl_iff, mem_union, mem_singleton_iff, LiZhongQC.wd_n_coe_mem_toExt, hz, or_false]
      rw [← mem_union, hcov, mem_compl_iff]
  have hΩo : IsOpen (toExt Ω) := OnePoint.isOpen_image_coe.2 hΩ
  have hΩso : IsOpen (toExt Ωs) := OnePoint.isOpen_image_coe.2 hΩs
  have hdisj' : Disjoint (toExt Ω) (toExt Ωs) := (disjoint_image_iff OnePoint.coe_injective).2 hdisj
  have hcc : IsConnected (toExt Ω) := hc.image _ OnePoint.continuous_coe.continuousOn
  have hccs : IsConnected (toExt Ωs) := hcs.image _ OnePoint.continuous_coe.continuousOn
  obtain ⟨p₁, hp₁⟩ := hc.nonempty
  obtain ⟨p₂, hp₂⟩ := hcs.nonempty
  have hcomp : ∀ A B : Set ExtPlane, IsOpen A → IsOpen B → IsConnected A → Disjoint A B →
      (toExt C ∪ {extInf})ᶜ = A ∪ B → ∀ q ∈ A, A = connectedComponentIn (toExt C ∪ {extInf})ᶜ q := by
    intro A B hA hB hAc hAB hSAB q hq
    have hqS : q ∈ (toExt C ∪ {extInf})ᶜ := by
      rw [hSAB]
      exact Or.inl hq
    apply Subset.antisymm
    · exact hAc.isPreconnected.subset_connectedComponentIn hq (by rw [hSAB]; exact subset_union_left)
    · refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hA hB hAB ?_
        ⟨q, mem_connectedComponentIn hqS, hq⟩
      rw [← hSAB]
      exact connectedComponentIn_subset _ _
  have hp₁' : ((p₁ : ℂ) : ExtPlane) ∈ toExt Ω := ⟨p₁, hp₁, rfl⟩
  have hp₂' : ((p₂ : ℂ) : ExtPlane) ∈ toExt Ωs := ⟨p₂, hp₂, rfl⟩
  refine ⟨hJ, (p₁ : ExtPlane), ?_, (p₂ : ExtPlane), ?_, hcomp _ _ hΩo hΩso hcc hdisj' hS _ hp₁',
    hcomp _ _ hΩso hΩo hccs hdisj'.symm (by rw [hS, union_comm]) _ hp₂', ?_⟩
  · rw [hS]
    exact Or.inl hp₁'
  · rw [hS]
    exact Or.inr hp₂'
  · intro h
    have h1 : ((p₁ : ℂ) : ExtPlane) ∈ toExt Ωs := h ▸ hp₁'
    exact disjoint_left.1 hdisj' hp₁' h1

/-- Helper for `lemma16_5` (§16.5). `LiZhongQC.wd_backward` with the labels recorded. The welded homeomorphism `H`
(`Φ⁻¹ ∘ G⁻¹` on `ℍ̄`, `Ψ⁻¹` on `𝕃̄`, the original's construction, repeated here) maps `ℍ` onto `A₁` and `𝕃` onto `A₂`
and is holomorphic on `𝕃`. The original's conclusion records only that `H` is a homeomorphism, `K`-q.c. on `ℍ`,
`1`-q.c. on `𝕃` with `C = H(ℝ) ∪ {∞}`. `lemma16_5` needs the labels (the conformal half must map onto the prescribed
component `Ωs`), and they do not follow from that conclusion. -/
theorem gl16_wd_backward_labelled {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : LiZhongQC.AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : LiZhongQC.IsConformalOnto φ A₁ upperHalf) (hψ : LiZhongQC.IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : LiZhongQC.IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : LiZhongQC.IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane))
    {g : ℂ → ℂ} {G : ExtPlane → ExtPlane} {K : ℝ} (hg : IsKQC g upperHalf K) (hgs : g '' upperHalf = upperHalf)
    (hG : LiZhongQC.IsHomeoExtension g upperHalf upperHalf G)
    (hGh : ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane)) :
    ∃ H : ℂ → ℂ, LiZhongQC.IsHomeomorphOnto H univ univ ∧ IsKQC H upperHalf K ∧ IsKQC H lowerHalf 1 ∧
      C = toExt (H '' realLine) ∪ {extInf} ∧ H '' upperHalf = A₁ ∧ H '' lowerHalf = A₂ ∧
      DifferentiableOn ℂ H lowerHalf := by
  classical
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, hA₁eq, hA₂eq, hne⟩ := hC
  -- the two components are open and disjoint
  have hCo : IsOpen Cᶜ := by
    obtain ⟨γ, hγc, -, hγr⟩ := hJ
    rw [← hγr]
    exact (isCompact_range hγc).isClosed.isOpen_compl
  have hA₁o : IsOpen (toExt A₁) := by
    rw [hA₁eq]
    exact hCo.connectedComponentIn
  have hA₂o : IsOpen (toExt A₂) := by
    rw [hA₂eq]
    exact hCo.connectedComponentIn
  have hdisj : Disjoint (toExt A₁) (toExt A₂) := by
    rw [Set.disjoint_left]
    intro q hq₁ hq₂
    rw [hA₁eq] at hq₁
    rw [hA₂eq] at hq₂
    exact hne (by rw [hA₁eq, hA₂eq, connectedComponentIn_eq hq₁, connectedComponentIn_eq hq₂])
  -- `C` is the frontier of both components (F)
  have hfr₁ : frontier (toExt A₁) = C := LiZhongQC.wd_frontier_eq hJ ⟨p₁, hp₁, hA₁eq⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := LiZhongQC.wd_frontier_eq hJ ⟨p₂, hp₂, hA₂eq⟩ (Or.inr rfl) hψ hΨ
  have hCS₁ : C ⊆ closure (toExt A₁) := by
    rw [← hfr₁]
    exact frontier_subset_closure
  have hCS₂ : C ⊆ closure (toExt A₂) := by
    rw [← hfr₂]
    exact frontier_subset_closure
  -- the inverses of `Φ`, `Ψ`, `G` on the closures
  obtain ⟨hΦic, hΦim, hΦr, hΦl⟩ := LiZhongQC.wd_b_inv isClosed_closure hΦ.2.1 hΦ.2.2.1 hΦ.2.2.2
  obtain ⟨hΨic, hΨim, hΨr, hΨl⟩ := LiZhongQC.wd_b_inv isClosed_closure hΨ.2.1 hΨ.2.2.1 hΨ.2.2.2
  obtain ⟨hGic, hGim, hGr, hGl⟩ := LiZhongQC.wd_b_inv isClosed_closure hG.2.1 hG.2.2.1 hG.2.2.2
  have hGiU : ∀ z ∈ upperHalf, Function.invFunOn G (closure (toExt upperHalf)) (z : ExtPlane) =
      ((Function.invFunOn g upperHalf z : ℂ) : ExtPlane) ∧ Function.invFunOn g upperHalf z ∈ upperHalf :=
    fun z hz => LiZhongQC.wd_b_invFunOn_coe hG hgs hz
  have hΦiU : ∀ v ∈ upperHalf, Function.invFunOn Φ (closure (toExt A₁)) (v : ExtPlane) =
      ((Function.invFunOn φ A₁ v : ℂ) : ExtPlane) :=
    fun v hv => (LiZhongQC.wd_b_invFunOn_coe hΦ hφ.2.2 hv).1
  have hΨiL : ∀ z ∈ lowerHalf, Function.invFunOn Ψ (closure (toExt A₂)) (z : ExtPlane) =
      ((Function.invFunOn ψ A₂ z : ℂ) : ExtPlane) ∧ Function.invFunOn ψ A₂ z ∈ A₂ :=
    fun z hz => LiZhongQC.wd_b_invFunOn_coe hΨ hψ.2.2 hz
  set Φi := Function.invFunOn Φ (closure (toExt A₁))
  set Ψi := Function.invFunOn Ψ (closure (toExt A₂))
  set Gi := Function.invFunOn G (closure (toExt upperHalf))
  -- boundary identification: `Φ⁻¹(G⁻¹ y) = Ψ⁻¹ y ∈ C` for real `y`
  have hkey : ∀ y : ℝ, Φi (Gi (((y : ℝ) : ℂ) : ExtPlane)) = Ψi (((y : ℝ) : ℂ) : ExtPlane) ∧
      Ψi (((y : ℝ) : ℂ) : ExtPlane) ∈ C := by
    intro y
    have hyL := LiZhongQC.wd_b_real_mem_closure_lower y
    have hΨz : Ψ (Ψi (((y : ℝ) : ℂ) : ExtPlane)) = (((y : ℝ) : ℂ) : ExtPlane) := hΨr _ hyL
    have hzC : Ψi (((y : ℝ) : ℂ) : ExtPlane) ∈ C := by
      rw [← hfr₂, hA₂o.frontier_eq]
      refine ⟨hΨim hyL, ?_⟩
      rintro ⟨u, hu, hue⟩
      rw [← hue, hΨ.1 u hu] at hΨz
      have h1 : (ψ u).im < 0 := by
        have h2 : ψ u ∈ lowerHalf := by
          rw [← hψ.2.2]
          exact mem_image_of_mem ψ hu
        exact h2
      rw [OnePoint.coe_injective hΨz, Complex.ofReal_im] at h1
      exact lt_irrefl 0 h1
    have hzne : Ψi (((y : ℝ) : ℂ) : ExtPlane) ≠ extInf := by
      intro h0
      rw [h0, hΨinf] at hΨz
      exact OnePoint.coe_ne_infty _ hΨz.symm
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.1 hzne
    rw [← hw] at hzC hΨz ⊢
    obtain ⟨x, hx₁, hx₂⟩ := hh w hzC
    have hxy : (((h x : ℝ) : ℂ) : ExtPlane) = (((y : ℝ) : ℂ) : ExtPlane) := by
      rw [← hx₂, hΨz]
    have hGy : Gi (((y : ℝ) : ℂ) : ExtPlane) = (((x : ℝ) : ℂ) : ExtPlane) := by
      rw [← hxy, ← hGh x]
      exact hGl _ (LiZhongQC.wd_b_real_mem_closure_upper x)
    refine ⟨?_, hzC⟩
    rw [hGy, ← hx₁]
    exact hΦl _ (hCS₁ hzC)
  -- the three inverses fix `∞`
  have hGiinf : Gi extInf = extInf := by
    have hGeq := hGr _ LiZhongQC.wd_b_infty_mem_closure_upper
    rcases LiZhongQC.wd_b_closure_upper_cases (hGim LiZhongQC.wd_b_infty_mem_closure_upper) with
      h0 | ⟨x, hx⟩ | ⟨z, hz, hzeq⟩
    · exact h0
    · rw [hx, hGh x] at hGeq
      exact (OnePoint.coe_ne_infty _ hGeq).elim
    · rw [hzeq, hG.1 z hz] at hGeq
      exact (OnePoint.coe_ne_infty _ hGeq).elim
  have hΦiinf : Φi extInf = extInf := by
    have h0 := hΦl _ (hCS₁ hinf)
    rwa [hΦinf] at h0
  have hΨiinf : Ψi extInf = extInf := by
    have h0 := hΨl _ (hCS₂ hinf)
    rwa [hΨinf] at h0
  -- the welded map of `ℂ̄`: `Φ⁻¹ ∘ G⁻¹` on `ℍ̄`, `Ψ⁻¹` on `𝕃̄`
  obtain ⟨E, hE⟩ : ∃ E : ExtPlane → ExtPlane,
      ∀ p, E p = if p ∈ closure (toExt upperHalf) then Φi (Gi p) else Ψi p := ⟨_, fun p => rfl⟩
  have hEU : EqOn E (Φi ∘ Gi) (closure (toExt upperHalf)) := fun p hp => by
    rw [hE, ite_eq_left hp, Function.comp_apply]
  have hEL : EqOn E Ψi (closure (toExt lowerHalf)) := fun p hp => by
    by_cases hpU : p ∈ closure (toExt upperHalf)
    · rw [hE, ite_eq_left hpU]
      rcases LiZhongQC.wd_b_closure_inter hpU hp with rfl | ⟨y, rfl⟩
      · rw [hGiinf, hΦiinf, hΨiinf]
      · exact (hkey y).1
    · rw [hE, ite_eq_right hpU]
  have hEc : Continuous E := LiZhongQC.wd_b_paste (hΦic.comp hGic hGim) hΨic hEU hEL
  have hEinj : Function.Injective E := by
    -- a point of `ℍ̄` and a point off `ℍ̄` have different images
    have hsep : ∀ p q, p ∈ closure (toExt upperHalf) → q ∉ closure (toExt upperHalf) → E p ≠ E q := by
      intro p q hp hq hpq
      obtain ⟨z, hz, rfl⟩ := LiZhongQC.wd_b_not_mem_closure_upper hq
      rw [hEU hp, hE, ite_eq_right hq, (hΨiL z hz).1] at hpq
      have h1 : (Φi ∘ Gi) p ∈ closure (toExt A₁) := hΦim (hGim hp)
      rw [hpq] at h1
      exact disjoint_left.1 (hdisj.closure_left hA₂o) h1 ⟨_, (hΨiL z hz).2, rfl⟩
    intro p q hpq
    by_cases hp : p ∈ closure (toExt upperHalf) <;> by_cases hq : q ∈ closure (toExt upperHalf)
    · rw [hEU hp, hEU hq] at hpq
      have h1 : Gi p = Gi q := by
        rw [← hΦr _ (hGim hp), ← hΦr _ (hGim hq)]
        exact congrArg Φ hpq
      calc p = G (Gi p) := (hGr p hp).symm
        _ = G (Gi q) := by rw [h1]
        _ = q := hGr q hq
    · exact (hsep p q hp hq hpq).elim
    · exact (hsep q p hq hp hpq.symm).elim
    · obtain ⟨z, hz, rfl⟩ := LiZhongQC.wd_b_not_mem_closure_upper hp
      obtain ⟨w, hw, rfl⟩ := LiZhongQC.wd_b_not_mem_closure_upper hq
      rw [hE, ite_eq_right hp, hE, ite_eq_right hq] at hpq
      calc (z : ExtPlane) = Ψ (Ψi z) := (hΨr _ (subset_closure ⟨z, hz, rfl⟩)).symm
        _ = Ψ (Ψi w) := by rw [hpq]
        _ = w := hΨr _ (subset_closure ⟨w, hw, rfl⟩)
  have hEinf : E extInf = extInf := by
    rw [hEU LiZhongQC.wd_b_infty_mem_closure_upper, Function.comp_apply, hGiinf, hΦiinf]
  -- the plane map
  obtain ⟨hHcoe, hHhom⟩ := LiZhongQC.wd_b_plane_homeo hEc hEinj hEinf
  have hA₁o' : IsOpen A₁ := OnePoint.isOpen_image_coe.1 hA₁o
  have hA₂o' : IsOpen A₂ := OnePoint.isOpen_image_coe.1 hA₂o
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  -- the welded map on the two half-planes (the labels)
  have hHU' : ∀ z ∈ upperHalf, LiZhongQC.extToC (E z) =
      Function.invFunOn φ A₁ (Function.invFunOn g upperHalf z) := fun z hz => OnePoint.coe_injective (by
    rw [hHcoe z, hEU (subset_closure ⟨z, hz, rfl⟩), Function.comp_apply, (hGiU z hz).1, hΦiU _ (hGiU z hz).2])
  have hHL' : ∀ z ∈ lowerHalf, LiZhongQC.extToC (E z) = Function.invFunOn ψ A₂ z := fun z hz => by
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 LiZhongQC.wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    refine OnePoint.coe_injective ?_
    rw [hHcoe z, hE, ite_eq_right hzU]
    exact (hΨiL z hz).1
  refine ⟨fun z : ℂ => LiZhongQC.extToC (E z), hHhom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- on `ℍ`, `H = φ⁻¹ ∘ g⁻¹` is `K`-q.c.
    have hgi : IsKQC (Function.invFunOn g upperHalf) upperHalf K := by
      have h0 := LiZhongQC.thm7_2_inv hg
      rwa [hgs] at h0
    have hsub : Function.invFunOn g upperHalf '' upperHalf ⊆ upperHalf := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hGiU z hz).2
    have hcomp := LiZhongQC.thm7_1_comp hgi
      (LiZhongQC.isKQC_one_of_conformal LiZhongQC.isOpen_upperHalf (hφ.symm hA₁o')) hsub
    rw [mul_one] at hcomp
    refine LiZhongQC.ad_isKQC_congr hcomp fun z hz => OnePoint.coe_injective ?_
    show ((LiZhongQC.extToC (E z) : ℂ) : ExtPlane) =
      ((Function.invFunOn φ A₁ (Function.invFunOn g upperHalf z) : ℂ) : ExtPlane)
    rw [hHcoe z, hEU (subset_closure ⟨z, hz, rfl⟩), Function.comp_apply, (hGiU z hz).1,
      hΦiU _ (hGiU z hz).2]
  · -- on `𝕃`, `H = ψ⁻¹` is conformal
    refine LiZhongQC.ad_isKQC_congr (LiZhongQC.isKQC_one_of_conformal hLo (hψ.symm hA₂o'))
      fun z hz => OnePoint.coe_injective ?_
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 LiZhongQC.wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    show ((LiZhongQC.extToC (E z) : ℂ) : ExtPlane) = ((Function.invFunOn ψ A₂ z : ℂ) : ExtPlane)
    rw [hHcoe z, hE, ite_eq_right hzU]
    exact (hΨiL z hz).1
  · -- `C = H(ℝ) ∪ {∞}`
    have hreal : ∀ y : ℝ, E (((y : ℝ) : ℂ) : ExtPlane) = Ψi (((y : ℝ) : ℂ) : ExtPlane) := fun y => by
      rw [hEU (LiZhongQC.wd_b_real_mem_closure_upper y), Function.comp_apply]
      exact (hkey y).1
    apply Subset.antisymm
    · intro p hp
      by_cases hpinf : p = extInf
      · exact Or.inr hpinf
      obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hpinf
      obtain ⟨x, -, hx₂⟩ := hh w hp
      refine Or.inl ⟨LiZhongQC.extToC (E (((h x : ℝ) : ℂ) : ExtPlane)), ⟨((h x : ℝ) : ℂ), Complex.ofReal_im _, rfl⟩, ?_⟩
      rw [hHcoe, hreal, ← hx₂, hΨl _ (hCS₂ hp)]
    · rintro p (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | hp)
      · have hz' : ((z.re : ℝ) : ℂ) = z :=
          Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact (show z.im = 0 from hz).symm)
        show ((LiZhongQC.extToC (E z) : ℂ) : ExtPlane) ∈ C
        rw [hHcoe z, ← hz', hreal]
        exact (hkey z.re).2
      · rw [mem_singleton_iff] at hp
        rw [hp]
        exact hinf
  · -- `H(ℍ) = A₁`: `H = φ⁻¹ ∘ g⁻¹` there
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      show LiZhongQC.extToC (E z) ∈ A₁
      rw [hHU' z hz]
      have hv : Function.invFunOn g upperHalf z ∈ φ '' A₁ := by
        rw [hφ.2.2]
        exact (hGiU z hz).2
      exact Function.invFunOn_mem hv
    · intro a ha
      have hv : φ a ∈ upperHalf := by
        rw [← hφ.2.2]
        exact mem_image_of_mem φ ha
      have hz : g (φ a) ∈ upperHalf := by
        rw [← hgs]
        exact mem_image_of_mem g hv
      refine ⟨g (φ a), hz, ?_⟩
      show LiZhongQC.extToC (E (g (φ a))) = a
      rw [hHU' _ hz, hg.2.2.1.2.1.leftInvOn_invFunOn hv, hφ.2.1.leftInvOn_invFunOn ha]
  · -- `H(𝕃) = A₂`: `H = ψ⁻¹` there
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      show LiZhongQC.extToC (E z) ∈ A₂
      rw [hHL' z hz]
      exact (hΨiL z hz).2
    · intro a ha
      have hz : ψ a ∈ lowerHalf := by
        rw [← hψ.2.2]
        exact mem_image_of_mem ψ ha
      refine ⟨ψ a, hz, ?_⟩
      show LiZhongQC.extToC (E (ψ a)) = a
      rw [hHL' _ hz, hψ.2.1.leftInvOn_invFunOn ha]
  · -- holomorphic on `𝕃`: `H = ψ⁻¹` there
    exact (hψ.symm hA₂o').1.congr fun z hz => hHL' z hz

/-- **Lemma 5** (§16.5, l. 12129). Any quasicircle `C` is the image of `ℝ̄` under a quasiconformal self-map of `ℂ̄`
that is conformal in `ℍ*` and maps `ℍ` and `ℍ*` onto `Ω` and `Ω*`. -/
theorem lemma16_5 {C Ω Ωs : Set ℂ} (hC : LiZhongQC.IsQuasicircle (toExt C ∪ {extInf})) (hΩ : IsOpen Ω)
    (hΩs : IsOpen Ωs) (hc : IsConnected Ω) (hcs : IsConnected Ωs) (hdisj : Disjoint Ω Ωs) (hcov : Ω ∪ Ωs = Cᶜ) :
    ∃ (F : ℂ → ℂ) (K : ℝ), IsKQC F univ K ∧ F '' univ = univ ∧ F '' realLine = C ∧ F '' upperHalf = Ω ∧
      F '' lowerHalf = Ωs ∧ DifferentiableOn ℂ F lowerHalf := by
  have hinf : extInf ∈ toExt C ∪ {extInf} := Or.inr rfl
  obtain ⟨K₀, hK₀⟩ := hC
  have hJ := LiZhongQC.n18_isJordanCurve hK₀
  have hcomp := gl16_components hJ hΩ hΩs hc hcs hdisj hcov
  have hcomp' : LiZhongQC.AreComplementaryComponents (toExt C ∪ {extInf}) (toExt Ωs) (toExt Ω) := by
    obtain ⟨hJ', p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hcomp
    exact ⟨hJ', p₂, hp₂, p₁, hp₁, h₂, h₁, hne.symm⟩
  -- uniformizers of the two components, fixing `∞`
  obtain ⟨hD₁, hi₁⟩ := LiZhongQC.s18v_isJordanDomain hcomp hinf
  obtain ⟨hD₂, hi₂⟩ := LiZhongQC.s18v_isJordanDomain hcomp' hinf
  obtain ⟨φ, hφ, Φ, hΦ, hΦinf⟩ := LiZhongQC.s16p_uniformizer_inf hD₁ hi₁
  obtain ⟨ψ, hψ, Ψ, hΨ, hΨinf⟩ := LiZhongQC.s18v_uniformizer_lower hD₂ hi₂
  -- the welding and its quasiconformal extension to `ℍ`
  obtain ⟨h, hh⟩ := LiZhongQC.s18v_welding hinf hcomp hφ hψ hΦ hΨ hΦinf hΨinf
  obtain ⟨g, G, K, hg, hgs, hG, -, hGx⟩ := LiZhongQC.wd_forward hinf hcomp hφ hψ hΦ hΨ hΦinf hΨinf hh ⟨K₀, hK₀⟩
  -- the labelled welded homeomorphism
  obtain ⟨H, hH, hHU, hHL, hCH, hHup, hHlo, hHd⟩ :=
    gl16_wd_backward_labelled hinf hcomp hφ hψ hΦ hΨ hΦinf hΨinf hh hg hgs hG hGx
  have hK1 : 1 ≤ K := hg.2.1
  have hH' : LiZhongQC.IsHomeomorphOnto H univ (H '' univ) := by
    rw [hH.2.2.1]
    exact hH
  have hHK : IsKQC H univ K := LiZhongQC.wd_glue hK1 hH' hHU (hHL.mono hK1)
  exact ⟨H, K, hHK, hH.2.2.1, (LiZhongQC.tp_b2_eq_of_toExt_union hCH).symm, hHup, hHlo, hHd⟩

/-- Helper for (16.6) (§16.5, l. 12143). `a = fb s`, `b = fb t`, `c = fb u` with `s < t < u`, and the arc `fb[s, u]`
through `b` has spherical diameter at most that of the complementary arc `fb[u, ∞] ∪ fb[−∞, s]`. -/
def IsSmallerArcTriple (fb : ℝ → ExtPlane) (d : ExtPlane) (s t u : ℝ) : Prop :=
  s < t ∧ t < u ∧ sphericalDiam (fb '' Icc s u) ≤ sphericalDiam (fb '' Ici u ∪ fb '' Iic s ∪ {d})

/-- **Formula (16.6)** (the reverse triangle inequality, §16.5, l. 12143). For consecutive `a, b, c` with `b` on the
arc from `a` to `c` of smaller spherical diameter, `d(a, b) + d(b, c) ≤ λ d(a, c)`. -/
def HasReverseTriangle (Ωs : Set ℂ) (lam : ℝ) : Prop :=
  ∀ (f : ℂ → ℂ) (fb : ℝ → ExtPlane) (d : ExtPlane), IsRiemannMapLower Ωs f fb d → ∀ s t u : ℝ,
    IsSmallerArcTriple fb d s t u →
      sphericalDist (fb s) (fb t) + sphericalDist (fb t) (fb u) ≤ lam * sphericalDist (fb s) (fb u)

/-- **Definition** (symmetric homeomorphism of `ℝ̄`, §16.5, l. 12153, in the charts of §16.6). `h` and
`ĥ(x) = −1/h(−1/x)` distort symmetric triples in `[−2, 2]` by factors `1 + ε(t)`, `ε(t) → 0`. -/
def HasVanishingRatioDistortionReal (h : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t → -2 ≤ x - t → x + t ≤ 2 →
    (1 / (1 + ε t) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + ε t) ∧
    (1 / (1 + ε t) ≤ qsRatio (fun y => -1 / h (-1 / y)) x t ∧ qsRatio (fun y => -1 / h (-1 / y)) x t ≤ 1 + ε t)

/-- **Definition 5** (symmetric quasicircle, §16.5, l. 12151). The welding map of `C` is symmetric. -/
def IsSymmetricQuasicircle (Ω Ωs : Set ℂ) : Prop :=
  ∃ (f g : ℂ → ℂ) (fb gb : ℝ → ExtPlane) (d : ExtPlane) (h : ℝ → ℝ), IsWeldingMap Ω Ωs f g fb gb d h ∧ h 0 = 0 ∧
    HasVanishingRatioDistortionReal h

/-- **Unlabelled** (§16.5, l. 12153). `C` is a symmetric quasicircle iff there is a quasiconformal self-map `F` of the
plane mapping `ℝ̄` onto `C` with `K_z(F) → 1` uniformly as `z` approaches `ℝ̄` (read: `|μ_F(z)| → 0` as the chordal
distance `|Im z|/(1 + |z|²)` to `ℝ̄` tends to `0`). -/
theorem para16_5_symmetric_iff {C Ω Ωs : Set ℂ} (hC : LiZhongQC.IsQuasicircle (toExt C ∪ {extInf}))
    (hΩ : IsOpen Ω) (hΩs : IsOpen Ωs) (hc : IsConnected Ω) (hcs : IsConnected Ωs) (hdisj : Disjoint Ω Ωs)
    (hcov : Ω ∪ Ωs = Cᶜ) :
    IsSymmetricQuasicircle Ω Ωs ↔ ∃ (F : ℂ → ℂ) (K : ℝ), IsKQC F univ K ∧ F '' univ = univ ∧ F '' realLine = C ∧
      ∀ ε > 0, ∃ η > 0, ∀ z : ℂ, |z.im| < η * (1 + ‖z‖ ^ 2) → ‖complexDilatation F z‖ < ε := by
  sorry

/-- **Definition 6** (strong reverse triangle property, §16.5, l. 12158; [BP78]). For every `ε > 0` there is `δ > 0`
such that (16.6) holds with `λ = 1 + ε` for all `a, b, c` as in (16.6) lying in a disc of spherical radius `δ`. -/
def HasStrongReverseTriangle (Ωs : Set ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (f : ℂ → ℂ) (fb : ℝ → ExtPlane) (d : ExtPlane), IsRiemannMapLower Ωs f fb d →
    ∀ s t u : ℝ, IsSmallerArcTriple fb d s t u →
      (∃ w : ExtPlane, sphericalDist (fb s) w < δ ∧ sphericalDist (fb t) w < δ ∧ sphericalDist (fb u) w < δ) →
        sphericalDist (fb s) (fb t) + sphericalDist (fb t) (fb u) ≤ (1 + ε) * sphericalDist (fb s) (fb u)

/-- **Definition** (§16.5, l. 12163–12168). `Λ̃`: the extremal length of the closed curves separating the arcs `α` and
`α′` in `ℂ̂ ∖ (α ∪ α′)`, `2π / M(ℂ̂ ∖ (α ∪ α′))`. -/
def sepExtremalLength (α α' : Set ExtPlane) : ℝ≥0∞ := ENNReal.ofReal (2 * π) / ringModule (α ∪ α')ᶜ

/-- **Definition 7** (extremal length property, §16.5, l. 12170). For every point `d`, neighbourhood `U` of `d` and
`ε > 0` there is `δ > 0` such that `Λ̃₁ Λ̃₂ < 4 + ε` whenever `a, b, c` are consecutive, within `δ` of each other
and outside `U`. -/
def HasExtremalLengthProperty (Ωs : Set ℂ) : Prop :=
  ∀ (f : ℂ → ℂ) (fb : ℝ → ExtPlane) (d : ExtPlane), IsRiemannMapLower Ωs f fb d → ∀ U ∈ 𝓝 d, ∀ ε > 0, ∃ δ > 0,
    ∀ s t u : ℝ, s < t → t < u → sphericalDist (fb s) (fb t) < δ → sphericalDist (fb t) (fb u) < δ →
      sphericalDist (fb s) (fb u) < δ → fb s ∉ U → fb t ∉ U → fb u ∉ U →
        sepExtremalLength (fb '' Icc s t) (fb '' Ici u ∪ {d}) *
          sepExtremalLength (fb '' Icc t u) (fb '' Iic s ∪ {d}) < 4 + ENNReal.ofReal ε

/-- Helper (disc template, Figure 16.2). The canal `{a + u w : −ρ ≤ Re w ≤ e, |Im w| ≤ η/2}`, `u = (b − a)/|b − a|`. -/
def templateCanal (a b : ℂ) (ρ η e : ℝ) : Set ℂ :=
  {z | ∃ w : ℂ, z = a + (b - a) / (‖b - a‖ : ℂ) * w ∧ -ρ ≤ w.re ∧ w.re ≤ e ∧ |w.im| ≤ η / 2}

/-- Helper (disc template, Figure 16.2). The pond `{a + u w : p₁ ≤ Re w ≤ p₂, |Im w| ≤ η/2}`. -/
def templatePond (a b : ℂ) (η p₁ p₂ : ℝ) : Set ℂ :=
  {z | ∃ w : ℂ, z = a + (b - a) / (‖b - a‖ : ℂ) * w ∧ p₁ ≤ w.re ∧ w.re ≤ p₂ ∧ |w.im| ≤ η / 2}

/-- **Definition** (disc template for `a, b, c, d`, §16.5, l. 12172–12182, Figure 16.2). A disc of radius `ρ` centred
at `a` with a canal and a pond of height `η` along the diameter through `b`; the arc `α_bc` lies in the pond and the
arc `α_ad` lies in the canal or outside the disc. -/
def IsDiscTemplateFor (a b : ℂ) (ρ η e p₁ p₂ : ℝ) (αbc αad : Set ExtPlane) : Prop :=
  a ≠ b ∧ 0 < η ∧ 0 ≤ e ∧ e < p₁ ∧ p₁ < p₂ ∧ p₂ < ρ ∧ αbc ⊆ toExt (templatePond a b η p₁ p₂) ∧
    ∀ q ∈ αad, q = extInf ∨ ∃ z : ℂ, q = (z : ExtPlane) ∧ (z ∈ templateCanal a b ρ η e ∨ ρ < ‖z - a‖)

/-- **Definition** (allowable triple, §16.5, l. 12184). `a, b, c` are the images of `x − t, x, x + t` and lie outside
`U`. -/
def IsAllowableTriple (fb : ℝ → ExtPlane) (U : Set ExtPlane) (x t : ℝ) : Prop :=
  0 < t ∧ fb (x - t) ∉ U ∧ fb x ∉ U ∧ fb (x + t) ∉ U

/-- **Definition 8** (disc template property, §16.5, l. 12186). For every Riemann map `f` of `ℍ*` onto `Ω*`, every
neighbourhood `U` of `d = f(∞)` (with `B` bounding the ratios of `|a − b|, |b − c|, |a − c|` over allowable triples)
and every `0 < ε < 1` there is `δ > 0` such that every allowable triple in a disc of radius `δ` has a disc template
with canal length `≥ |a − b|/ε`, height `≤ ε|a − b|`, separation `≥ (1 − ε)|a − b|` and pond length between
`|a − b|/B` and `B|a − b|`. -/
def HasDiscTemplateProperty (Ωs : Set ℂ) : Prop :=
  ∀ (f : ℂ → ℂ) (fb : ℝ → ExtPlane) (d : ExtPlane), IsRiemannMapLower Ωs f fb d → ∀ U ∈ 𝓝 d, ∃ B : ℝ, 1 ≤ B ∧
    (∀ (x t : ℝ) (a b c : ℂ), IsAllowableTriple fb U x t → fb (x - t) = a → fb x = b → fb (x + t) = c →
      ‖a - b‖ ≤ B * ‖b - c‖ ∧ ‖b - c‖ ≤ B * ‖a - b‖ ∧ ‖a - c‖ ≤ B * ‖a - b‖ ∧ ‖a - b‖ ≤ B * ‖a - c‖) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, ∀ (x t : ℝ) (a b c w : ℂ), IsAllowableTriple fb U x t →
      fb (x - t) = a → fb x = b → fb (x + t) = c → ‖a - w‖ < δ → ‖b - w‖ < δ → ‖c - w‖ < δ →
        ∃ ρ η e p₁ p₂ : ℝ, IsDiscTemplateFor a b ρ η e p₁ p₂ (fb '' Icc x (x + t)) (fb '' Iic (x - t) ∪ {d}) ∧
          ‖a - b‖ / ε ≤ ρ + e ∧ η ≤ ε * ‖a - b‖ ∧ (1 - ε) * ‖a - b‖ ≤ p₁ - e ∧
          ‖a - b‖ / B ≤ p₂ - p₁ ∧ p₂ - p₁ ≤ B * ‖a - b‖

/-- **Theorem 4** (§16.5, l. 12194). For a quasicircle `C` the following are equivalent: (i) the welding map is
symmetric; (ii) `C` has the strong reverse triangle property; (iii) the disc template property; (iv) the extremal
length property. -/
theorem thm16_4 {C Ω Ωs : Set ℂ} (hC : LiZhongQC.IsQuasicircle (toExt C ∪ {extInf})) (hΩ : IsOpen Ω)
    (hΩs : IsOpen Ωs) (hc : IsConnected Ω) (hcs : IsConnected Ωs) (hdisj : Disjoint Ω Ωs) (hcov : Ω ∪ Ωs = Cᶜ) :
    List.TFAE [IsSymmetricQuasicircle Ω Ωs, HasStrongReverseTriangle Ωs, HasDiscTemplateProperty Ωs,
      HasExtremalLengthProperty Ωs] := by
  sorry

/-- **Lemma 6** (§16.5, l. 12281). Let `x₀ < ⋯ < xₙ` partition `[x₀, xₙ]` into intervals `J_i = [x_{i−1}, x_i]` such
that any two adjacent `k`-tuples of adjacent intervals (`k ≤ n/2`) have lengths within the factor `B`. Then
`|xₙ − x₀| ≥ (log₂ n) |J₁| / B`. -/
theorem lemma16_6 {n : ℕ} {x : ℕ → ℝ} {B : ℝ} (hB : 1 ≤ B) (hx : StrictMonoOn x (Iic n))
    (hadj : ∀ k i : ℕ, 1 ≤ k → i + 2 * k ≤ n →
      (x (i + k) - x i) / B ≤ x (i + 2 * k) - x (i + k) ∧ x (i + 2 * k) - x (i + k) ≤ B * (x (i + k) - x i)) :
    Real.logb 2 n * (x 1 - x 0) / B ≤ x n - x 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  have hq : 0 ≤ 1 + 1 / B := add_nonneg zero_le_one (one_div_nonneg.2 hB0.le)
  set m := Nat.log 2 n with hm
  have hpow : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hlt : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hd : 0 < x 1 - x 0 := sub_pos.2 (hx (show (0 : ℕ) ∈ Iic n from Nat.zero_le n)
    (show (1 : ℕ) ∈ Iic n from hn) one_pos)
  -- doubling: `(1 + 1/B)^j (x 1 − x 0) ≤ x (2^j) − x 0` for `2^j ≤ n`
  have hdouble : ∀ j : ℕ, 2 ^ j ≤ n → (1 + 1 / B) ^ j * (x 1 - x 0) ≤ x (2 ^ j) - x 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : 2 ^ j ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) hj
      have h1 := ih hj'
      have h2 := (hadj (2 ^ j) 0 Nat.one_le_two_pow (by rw [zero_add, ← pow_succ']; exact hj)).1
      rw [zero_add, zero_add, ← pow_succ'] at h2
      calc (1 + 1 / B) ^ (j + 1) * (x 1 - x 0) = (1 + 1 / B) * ((1 + 1 / B) ^ j * (x 1 - x 0)) := by ring
        _ ≤ (1 + 1 / B) * (x (2 ^ j) - x 0) := mul_le_mul_of_nonneg_left h1 hq
        _ = (x (2 ^ j) - x 0) + (x (2 ^ j) - x 0) / B := by ring
        _ ≤ (x (2 ^ j) - x 0) + (x (2 ^ (j + 1)) - x (2 ^ j)) := by linarith
        _ = x (2 ^ (j + 1)) - x 0 := by ring
  have hmono : x (2 ^ m) ≤ x n :=
    hx.monotoneOn (show 2 ^ m ∈ Iic n from hpow) (Set.mem_Iic.2 le_rfl) hpow
  -- Bernoulli and `logb 2 n < m + 1`
  have hbern : 1 + (m : ℝ) * (1 / B) ≤ (1 + 1 / B) ^ m :=
    one_add_mul_le_pow (by linarith [one_div_nonneg.2 hB0.le]) m
  have hlog : Real.logb 2 n < (m : ℝ) + 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hn),
      show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact_mod_cast hlt
  have h1B : 1 / B ≤ 1 := by
    rw [div_le_one hB0]
    exact hB
  have hfac : ((m : ℝ) + 1) / B ≤ 1 + (m : ℝ) * (1 / B) := by
    calc ((m : ℝ) + 1) / B = (m : ℝ) * (1 / B) + 1 / B := by ring
      _ ≤ (m : ℝ) * (1 / B) + 1 := by linarith
      _ = 1 + (m : ℝ) * (1 / B) := by ring
  calc Real.logb 2 n * (x 1 - x 0) / B ≤ ((m : ℝ) + 1) * (x 1 - x 0) / B := by
        rw [div_le_div_iff_of_pos_right hB0]
        exact mul_le_mul_of_nonneg_right hlog.le hd.le
    _ = ((m : ℝ) + 1) / B * (x 1 - x 0) := by ring
    _ ≤ (1 + (m : ℝ) * (1 / B)) * (x 1 - x 0) := mul_le_mul_of_nonneg_right hfac hd.le
    _ ≤ (1 + 1 / B) ^ m * (x 1 - x 0) := mul_le_mul_of_nonneg_right hbern hd.le
    _ ≤ x (2 ^ m) - x 0 := hdouble m hpow
    _ ≤ x n - x 0 := by linarith

/-- Helper (§16.5, l. 12305–12313). The loop `β` of `X` surrounds the arc `α`: it is simple, essential and not
peripheral, and has simple freely homotopic representatives in every neighbourhood of `α`. -/
def IsArcSurroundingLoop {X : TopologicalSpace.Opens ℂ} (α : Set ℂ) (β : Loop X) : Prop :=
  IsSimpleLoop β ∧ ¬ IsTrivialLoop β ∧ ¬ IsPeripheralLoop β ∧ ∀ r > 0, ∃ β' : Loop X, FreelyHomotopic β' β ∧
    IsSimpleLoop β' ∧ ∀ s : unitInterval, ((β'.2 s : X) : ℂ) ∈ thickening r α

/-- **Lemma 7** (§16.5, l. 12319). There is `c(ε) → 1` as `ε → 0` such that `c(ε) L ≥ Λ`: `Λ` is the extremal length
of the curves in a disc template for `a, b, c, d = ∞` (with parameter `ε` in (i)–(iii) of Definition 8) separating the
pond from the canal, and `L` the extremal length in `ℂ̂ ∖ {a, b, c, ∞}` of the loops surrounding `α_bc`.
[CORRECTION] (AUDIT5_GL1518 G15-1) With (i)–(iii) alone the pond may be arbitrarily longer than `α_bc`, and then
`Λ/L → ∞` (`a = 0`, `b = 1`, `c = 2`, pond `[1/2, P]`, `P → ∞`). The book's proof (l. 12330) uses a pond that ends at `c`:
the pond ends within `ε|b − c|` beyond `c` (`p₂ ≤ Re((c − a)/u) + ε|b − c|`, `u = (b − a)/|b − a|`), and the triple has
the ratio bound `B` of allowable triples (Definition 8); `c(ε)` depends on `B`. -/
theorem lemma16_7 (B : ℝ) (hB : 1 ≤ B) : ∃ cfun : ℝ → ℝ, Tendsto cfun (𝓝[>] 0) (𝓝 1) ∧
    ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (a b c : ℂ) (ρ η e p₁ p₂ : ℝ) (αbc αad : Set ExtPlane),
      IsDiscTemplateFor a b ρ η e p₁ p₂ αbc αad → ‖a - b‖ / ε ≤ ρ + e → η ≤ ε * ‖a - b‖ →
      (1 - ε) * ‖a - b‖ ≤ p₁ - e → (↑c : ExtPlane) ∈ αbc → (↑b : ExtPlane) ∈ αbc →
      ‖a - b‖ ≤ B * ‖b - c‖ → ‖b - c‖ ≤ B * ‖a - b‖ →
      p₂ ≤ ((c - a) / ((b - a) / (‖b - a‖ : ℂ))).re + ε * ‖b - c‖ →
      ∀ (X : TopologicalSpace.Opens ℂ), (X : Set ℂ) = {a, b, c}ᶜ → ∀ (αbcC : Set ℂ), toExt αbcC = αbc →
        ∀ β : Loop X, IsArcSurroundingLoop αbcC β →
          LiZhongQC.extremalLength {γ : LRCurve | γ.toFun 0 = γ.toFun 1 ∧
              γ.toFun '' Icc 0 1 ⊆ ball a ρ \ (templateCanal a b ρ η e ∪ templatePond a b η p₁ p₂) ∧
              ∀ z ∈ templatePond a b η p₁ p₂, ∀ w ∈ templateCanal a b ρ η e,
                connectedComponentIn (γ.toFun '' Icc 0 1)ᶜ z ≠ connectedComponentIn (γ.toFun '' Icc 0 1)ᶜ w} ≤
            ENNReal.ofReal (cfun ε) * extremalLengthLoopRS β := by
  sorry

/-- **Lemma 8** (§16.5, l. 12321). The product `L₁ L₂` of the extremal lengths in `ℂ̂ ∖ {a, b, c, ∞}` of the loops
surrounding `α_ab` and `α_bc` tends to `4` as `a, b, c` move through allowable triples into smaller neighbourhoods
of a point `p ≠ d` of `C`.
[CORRECTION] (AUDIT5_GL1518 G15-2) The book proves Lemma 8 inside iii) ⇒ iv) of Theorem 4, using the disc template
property ("the disc template property inequality with ε close to zero forces `b` to be arbitrarily near to the straight
line segment", l. 12336); it is assumed here (`hDT`). Without it the lemma is false: for the corner quasicircle
`[0, ∞) ∪ i[0, ∞)`, `f(z) = √(−z)`, `p = 0`, the triples `√t, 0, i√t` keep `L₁L₂ − 4` bounded away from `0`. -/
theorem lemma16_8 {C Ω Ωs : Set ℂ} (hC : LiZhongQC.IsQuasicircle (toExt C ∪ {extInf})) (hΩ : IsOpen Ω)
    (hΩs : IsOpen Ωs) (hc : IsConnected Ω) (hcs : IsConnected Ωs) (hdisj : Disjoint Ω Ωs) (hcov : Ω ∪ Ωs = Cᶜ)
    (hDT : HasDiscTemplateProperty Ωs) {f : ℂ → ℂ} {fb : ℝ → ExtPlane} (hf : IsRiemannMapLower Ωs f fb extInf) {U : Set ExtPlane} (hU : U ∈ 𝓝 extInf)
    {p : ℂ} (hp : p ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (x t : ℝ) (a b c : ℂ), IsAllowableTriple fb U x t → fb (x - t) = a → fb x = b → fb (x + t) = c →
      ‖a - p‖ < δ → ‖b - p‖ < δ → ‖c - p‖ < δ →
      ∀ (X : TopologicalSpace.Opens ℂ), (X : Set ℂ) = {a, b, c}ᶜ → ∀ (α₁ α₂ : Set ℂ),
        toExt α₁ = fb '' Icc (x - t) x → toExt α₂ = fb '' Icc x (x + t) →
        ∀ β₁ β₂ : Loop X, IsArcSurroundingLoop α₁ β₁ → IsArcSurroundingLoop α₂ β₂ →
          |(extremalLengthLoopRS β₁ * extremalLengthLoopRS β₂).toReal - 4| < ε := by
  sorry

end GardinerLakic2000
