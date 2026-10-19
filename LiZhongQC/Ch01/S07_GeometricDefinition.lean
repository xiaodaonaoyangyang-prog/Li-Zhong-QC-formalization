import LiZhongQC.Ch01.S06_C1Quasiconformal
import LiZhongQC.Ch01.S02_DoublyConnected
import LiZhongQC.Lemmas.RectangleQuad
import LiZhongQC.Lemmas.AnnulusQC

/-!
# §7 一般拟共形映射的几何定义 — The geometric definition of quasiconformal mappings

* Definition 7.1 (`K`-quasiconformal mappings, Pfluger–Ahlfors)   — `IsKQC`
* `C¹` quasiconformal maps and conformal maps are quasiconformal  — `isKQC_of_isC1Quasiconformal`,
                                                                   `isKQC_one_of_conformal`
* Theorem 7.1 (composition), Theorem 7.2 (inverse)
* Theorem 7.3 (`1`-quasiconformal maps are conformal)
* Theorem 7.4 (quasi-invariance of the modulus of doubly connected domains)
* the converse of Theorem 7.4 (Lehto)                             — `isKQC_of_dcModulus_bound`, stated in
                                                                   `Lemmas/RingCharacterization.lean`

## Orientation

The book requires `f` to be an orientation preserving homeomorphism, so that the image
`f(Q)(f(z₁),…,f(z₄))` of a quadrilateral is again a (positively oriented) quadrilateral.
We encode this by asking for the image quadrilateral to exist (`IsSensePreserving`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-- `f` is sense preserving on `D`: it maps every quadrilateral `Q` with `Q̄ ⊆ D` (vertices in
positive order) onto a quadrilateral `f(Q)(f(z₁),…,f(z₄))` (vertices again in positive
order). -/
def IsSensePreserving (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ Q : TopQuad, closure (toExt Q.dom) ⊆ toExt D → ∃ Q' : TopQuad, Q.IsImageUnder Q' f

/-- **Definition 7.1** (`K` 拟共形映射).  `f` is `K`-quasiconformal (`K`-q.c.) on the domain `D`:
an orientation preserving homeomorphism of `D` onto `f(D)` such that
`M(f(Q)) ≤ K M(Q)` for every quadrilateral `Q` with `Q̄ ⊆ D`. -/
def IsKQC (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  IsOpen D ∧ 1 ≤ K ∧ IsHomeomorphOnto f D (f '' D) ∧
    ∀ Q : TopQuad, closure (toExt Q.dom) ⊆ toExt D →
      ∃ Q' : TopQuad, Q.IsImageUnder Q' f ∧ Q'.modulus ≤ K * Q.modulus

/-- `f` is quasiconformal on `D` (for some `K`). -/
def IsQuasiconformal (f : ℂ → ℂ) (D : Set ℂ) : Prop := ∃ K : ℝ, IsKQC f D K

/-- A `K`-q.c. map is sense preserving. -/
theorem IsKQC.isSensePreserving {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    IsSensePreserving f D := fun Q hQ =>
  (hf.2.2.2 Q hQ).imp fun _ h => h.1

/-- A `K`-q.c. map is `K'`-q.c. for every `K' ≥ K`. -/
theorem IsKQC.mono {f : ℂ → ℂ} {D : Set ℂ} {K K' : ℝ} (hf : IsKQC f D K) (hK : K ≤ K') :
    IsKQC f D K' := by
  obtain ⟨hD, hK1, hhom, hmod⟩ := hf
  refine ⟨hD, hK1.trans hK, hhom, fun Q hQc => ?_⟩
  obtain ⟨Q', hQ', hle⟩ := hmod Q hQc
  exact ⟨Q', hQ', hle.trans (mul_le_mul_of_nonneg_right hK (modulus_pos Q).le)⟩

/-- Two quadrilaterals with the same domain and vertices are equal. -/
theorem TopQuad.ext_of_dom_vert {Q₁ Q₂ : TopQuad} (hd : Q₁.dom = Q₂.dom)
    (hv : Q₁.vert = Q₂.vert) : Q₁ = Q₂ := by
  cases Q₁
  cases Q₂
  subst hd
  subst hv
  rfl

/-- The image quadrilateral is unique. -/
theorem TopQuad.IsImageUnder.unique {Q Q₁ Q₂ : TopQuad} {f : ℂ → ℂ} (h₁ : Q.IsImageUnder Q₁ f)
    (h₂ : Q.IsImageUnder Q₂ f) : Q₁ = Q₂ :=
  TopQuad.ext_of_dom_vert (h₁.1.trans h₂.1.symm) (funext fun i => (h₁.2 i).trans (h₂.2 i).symm)

/-- §7.1: the lower bound `M(f(Q)) ≥ M(Q)/K` follows from the arbitrariness of `Q`. -/
theorem IsKQC.modulus_ge {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) (Q Q' : TopQuad)
    (hQ : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f) :
    Q.modulus / K ≤ Q'.modulus ∧ Q'.modulus ≤ K * Q.modulus := by
  obtain ⟨-, hK1, -, hmod⟩ := hf
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  obtain ⟨Q₁, hQ₁, hle₁⟩ := hmod Q hQ
  obtain ⟨Q₃, hQ₃, hle₃⟩ := hmod Q.rotate hQ
  have hrot : Q.rotate.IsImageUnder Q'.rotate f := ⟨hQ'.1, fun i => hQ'.2 (i + 1)⟩
  rw [hQ₁.unique hQ'] at hle₁
  rw [hQ₃.unique hrot] at hle₃
  refine ⟨?_, hle₁⟩
  rw [thm1_2_modulus_rotate Q, thm1_2_modulus_rotate Q', div_div,
    div_le_div_iff₀ (mul_pos (modulus_pos _) hK0) (modulus_pos _)]
  linarith

/-- §7.1: `C¹` quasiconformal maps satisfy Definition 7.1. -/
theorem isKQC_of_isC1Quasiconformal {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsC1Quasiconformal f D K) : IsKQC f D K :=
  ⟨hf.1, hf.2.1, hf.2.2.2.1, fun Q hQ =>
    (thm6_1_modulus_quasi_invariance hf Q hQ).imp fun _ h => ⟨h.1, h.2.2⟩⟩

/-- The image of a quadrilateral `Q` with `Q̄ ⊆ D` under a conformal map of `D` is a quadrilateral
conformally equivalent to `Q`. -/
theorem TopQuad.exists_image_conformal {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsConformalOnto f D D') {Q : TopQuad} (hQ : closure (toExt Q.dom) ⊆ toExt D) :
    ∃ Q' : TopQuad, Q.IsImageUnder Q' f ∧ Q.ConfEquiv Q' := by
  obtain ⟨hJ, hQv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := Q.isTopQuad
  set C := closure (toExt Q.dom) with hC
  set F : ExtPlane → ExtPlane := OnePoint.map f with hF
  have hQo : IsOpen Q.dom := hJ.1
  have hsubD : Q.dom ⊆ D := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hQ (subset_closure (mem_image_of_mem _ hz))
    rw [← OnePoint.coe_injective hwz]
    exact hw
  have hfQ : IsConformalOnto f Q.dom (f '' Q.dom) := ⟨hf.1.mono hsubD, hf.2.1.mono hsubD, rfl⟩
  have htoExt : ∀ S : Set ℂ, F '' toExt S = toExt (f '' S) := fun S => by
    simp only [toExt, image_image]
    rfl
  have hFC : ContinuousOn F C := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := hQ hp
    refine ContinuousAt.continuousWithinAt (OnePoint.continuousAt_coe.2 ?_)
    exact OnePoint.continuous_coe.continuousAt.comp
      (hf.1.continuousOn.continuousAt (hD.mem_nhds hz))
  have hFinj : InjOn F C := by
    intro p hp q hq hpq
    obtain ⟨z, hz, rfl⟩ := hQ hp
    obtain ⟨w, hw, rfl⟩ := hQ hq
    rw [hf.2.1 hz hw (OnePoint.coe_injective hpq)]
  have hFimg : F '' C = closure (toExt (f '' Q.dom)) := by
    refine subset_antisymm ?_ ?_
    · rw [← htoExt]
      exact hFC.image_closure
    · refine closure_minimal ?_ (isClosed_closure.isCompact.image_of_continuousOn hFC).isClosed
      rw [← htoExt]
      exact image_mono subset_closure
  have hext : IsHomeoExtension f Q.dom (f '' Q.dom) F := ⟨fun z _ => rfl, hFC, hFinj, hFimg⟩
  have hfo : IsOpen (f '' Q.dom) := hfQ.isOpen hQo
  have hfr : F '' frontier (toExt Q.dom) = frontier (toExt (f '' Q.dom)) :=
    hext.image_frontier hQo hfo rfl
  have hfrC : frontier (toExt Q.dom) ⊆ C := frontier_subset_closure
  have hinv : IsHomeoExtension (Function.invFunOn f Q.dom) (f '' Q.dom) Q.dom
      (Function.invFunOn F C) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzC : ((z : ℂ) : ExtPlane) ∈ C := subset_closure (mem_image_of_mem _ hz)
      rw [hfQ.2.1.leftInvOn_invFunOn hz]
      exact hFinj.leftInvOn_invFunOn hzC
    · rw [← hFimg]
      exact continuousOn_invFunOn_of_isClosed isClosed_closure hFC hFinj
    · rw [← hFimg]
      intro p hp q hq hpq
      calc p = F (Function.invFunOn F C p) := (Function.invFunOn_eq hp).symm
        _ = F (Function.invFunOn F C q) := by rw [hpq]
        _ = q := Function.invFunOn_eq hq
    · rw [← hFimg]
      exact hFinj.leftInvOn_invFunOn.image_image
  have hTQ : IsTopQuad (f '' Q.dom) (fun i => F (Q.vert i)) := by
    refine ⟨⟨hfo, hJ.2.1.image f (hf.1.continuousOn.mono hsubD), ?_⟩, fun i => ?_,
      φ ∘ Function.invFunOn f Q.dom, Φ ∘ Function.invFunOn F C, x, hφ.comp (hfQ.symm hQo),
      hΦ.comp hinv (hfQ.symm hQo).mapsTo, hx, fun i => ?_⟩
    · obtain ⟨γ, hγc, hγi, hγr⟩ := hJ.2.2
      have hγC : ∀ t, γ t ∈ C := fun t => hfrC (hγr ▸ mem_range_self t)
      refine ⟨F ∘ γ, hFC.comp_continuous hγc hγC,
        fun s t hst => hγi (hFinj (hγC s) (hγC t) hst), ?_⟩
      rw [range_comp, hγr, hfr]
    · rw [← hfr]
      exact mem_image_of_mem F (hQv i)
    · show Φ (Function.invFunOn F C (F (Q.vert i))) = _
      rw [hFinj.leftInvOn_invFunOn (hfrC (hQv i))]
      exact hΦv i
  exact ⟨⟨f '' Q.dom, fun i => F (Q.vert i), hTQ⟩, ⟨rfl, fun i => rfl⟩, f, F, hfQ, hext,
    fun i => rfl⟩

/-- §7.1: a conformal map is `1`-quasiconformal (hence `K`-q.c. for every `K ≥ 1`). -/
theorem isKQC_one_of_conformal {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsConformalOnto f D D') : IsKQC f D 1 := by
  refine ⟨hD, le_rfl, ⟨hf.1.continuousOn, hf.2.1, rfl, ?_⟩, fun Q hQ => ?_⟩
  · rw [hf.2.2]
    exact (hf.symm hD).1.continuousOn
  · obtain ⟨Q', hQ', hce⟩ := TopQuad.exists_image_conformal hD hf hQ
    exact ⟨Q', hQ', by rw [one_mul, thm1_3_modulus_conformal_invariant hce]⟩

/-- **Theorem 7.1**: if `f₁ : D₁ → D₁'` is `K₁`-q.c., `f₂ : D₂ → D₂'` is `K₂`-q.c. and
`D₁' ⊆ D₂`, then `f₂ ∘ f₁` is `K₁K₂`-q.c. -/
theorem thm7_1_comp {f₁ f₂ : ℂ → ℂ} {D₁ D₂ : Set ℂ} {K₁ K₂ : ℝ} (h₁ : IsKQC f₁ D₁ K₁)
    (h₂ : IsKQC f₂ D₂ K₂) (hsub : f₁ '' D₁ ⊆ D₂) : IsKQC (f₂ ∘ f₁) D₁ (K₁ * K₂) := by
  obtain ⟨hD₁, hK₁, ⟨hc₁, hi₁, -, hinv₁⟩, hQ₁⟩ := h₁
  obtain ⟨-, hK₂, ⟨hc₂, hi₂, -, hinv₂⟩, hQ₂⟩ := h₂
  have hmaps : MapsTo f₁ D₁ D₂ := fun z hz => hsub (mem_image_of_mem f₁ hz)
  refine ⟨hD₁, one_le_mul_of_one_le_of_one_le hK₁ hK₂,
    ⟨hc₂.comp hc₁ hmaps, hi₂.comp hi₁ hmaps, rfl, ?_⟩, fun Q hQ => ?_⟩
  · -- the inverse of `f₂ ∘ f₁` is `f₁⁻¹ ∘ f₂⁻¹`
    have hmaps' : MapsTo (Function.invFunOn f₂ D₂) ((f₂ ∘ f₁) '' D₁) (f₁ '' D₁) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Function.comp_apply, hi₂.leftInvOn_invFunOn (hmaps hz)]
      exact mem_image_of_mem f₁ hz
    refine (hinv₁.comp (hinv₂.mono ?_) hmaps').congr ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact mem_image_of_mem f₂ (hmaps hz)
    · rintro _ ⟨z, hz, rfl⟩
      rw [(hi₂.comp hi₁ hmaps).leftInvOn_invFunOn hz]
      show z = Function.invFunOn f₁ D₁ (Function.invFunOn f₂ D₂ (f₂ (f₁ z)))
      rw [hi₂.leftInvOn_invFunOn (hmaps hz), hi₁.leftInvOn_invFunOn hz]
  · obtain ⟨Q', hQ', hle'⟩ := hQ₁ Q hQ
    have hQ'c : closure (toExt Q'.dom) ⊆ toExt D₂ := by
      rw [hQ'.1]
      exact closure_toExt_image_subset hc₁ hQ hsub
    obtain ⟨Q'', hQ'', hle''⟩ := hQ₂ Q' hQ'c
    refine ⟨Q'', ⟨by rw [hQ''.1, hQ'.1, image_comp], fun i => ?_⟩, ?_⟩
    · rw [hQ''.2, hQ'.2]
      exact Option.map_map f₂ f₁ (Q.vert i)
    · calc Q''.modulus ≤ K₂ * Q'.modulus := hle''
        _ ≤ K₂ * (K₁ * Q.modulus) := mul_le_mul_of_nonneg_left hle' (by linarith)
        _ = K₁ * K₂ * Q.modulus := by ring

/-- **Step 1 for Theorem 7.2**: every point of an open set `D` sits in a rectangle-image
quadrilateral whose closure lies in `toExt D`. -/
theorem exists_topQuad_mem_closure_subset {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    ∃ Q : TopQuad, z ∈ Q.dom ∧ closure (toExt Q.dom) ⊆ toExt D := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD z hz
  set s : ℝ := ε / 2 with hsdef
  have hspos : 0 < s := by positivity
  set c : ℂ := z - ((s / 2 : ℝ) : ℂ) * (1 + I) with hcdef
  set e : ℂ ≃ₜ ℂ := Homeomorph.addRight c with hedef
  have heapp : ∀ w, e w = w + c := fun _ => rfl
  have hgconf : IsConformalOnto (⇑e) univ univ := by
    refine ⟨?_, ?_, ?_⟩
    · have hd : Differentiable ℂ (⇑e) := by
        have heq : (⇑e : ℂ → ℂ) = fun w => w + c := funext heapp
        rw [heq]
        exact differentiable_id.add (differentiable_const c)
      exact hd.differentiableOn
    · intro a _ b _ hab
      exact e.injective hab
    · rw [image_univ, e.surjective.range_eq]
  have hUsub : closure (toExt (rectangle s s)) ⊆ toExt (univ : Set ℂ) := by
    rw [closure_toExt_of_isBounded (isBounded_rectangle s s)]
    exact image_mono (subset_univ _)
  obtain ⟨Q', hQ', -⟩ :=
    TopQuad.exists_image_conformal isOpen_univ hgconf (Q := rectQuad hspos hspos) hUsub
  have hzmem : z ∈ Q'.dom := by
    rw [hQ'.1]
    have hzc : z - c = ((s / 2 : ℝ) : ℂ) * (1 + I) := by rw [hcdef]; ring
    refine ⟨z - c, ?_, by rw [heapp]; ring⟩
    show z - c ∈ rectangle s s
    rw [rectangle_eq_Ioo_reProdIm_Ioo, mem_reProdIm]
    have hre : (z - c).re = s / 2 := by rw [hzc]; simp
    have him : (z - c).im = s / 2 := by rw [hzc]; simp
    rw [hre, him]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hclos : closure (toExt Q'.dom) ⊆ toExt D := by
    rw [hQ'.1]
    have hKcompact : IsCompact (⇑e '' (Icc (0:ℝ) s ×ℂ Icc (0:ℝ) s)) :=
      (isCompact_Icc.reProdIm isCompact_Icc).image e.continuous
    have hKD : (⇑e '' (Icc (0:ℝ) s ×ℂ Icc (0:ℝ) s)) ⊆ D := by
      rintro _ ⟨w, hw, rfl⟩
      rw [mem_reProdIm] at hw
      apply hball
      rw [mem_ball]
      have hre : (e w - z).re = w.re - s / 2 := by rw [heapp, hcdef]; simp; ring
      have him : (e w - z).im = w.im - s / 2 := by rw [heapp, hcdef]; simp; ring
      calc dist (e w) z = ‖e w - z‖ := Complex.dist_eq _ _
        _ ≤ |(e w - z).re| + |(e w - z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ s / 2 + s / 2 := by
            rw [hre, him]
            have h1 : |w.re - s / 2| ≤ s / 2 := abs_le.2 ⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩
            have h2 : |w.im - s / 2| ≤ s / 2 := abs_le.2 ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
            linarith
        _ = s := by ring
        _ < ε := by rw [hsdef]; linarith
    have hKclosedExt : IsClosed (toExt (⇑e '' (Icc (0:ℝ) s ×ℂ Icc (0:ℝ) s))) :=
      (hKcompact.image OnePoint.continuous_coe).isClosed
    calc closure (toExt (⇑e '' rectangle s s))
        ⊆ closure (toExt (⇑e '' (Icc (0:ℝ) s ×ℂ Icc (0:ℝ) s))) := by
          refine closure_mono (image_mono (image_mono ?_))
          rw [rectangle_eq_Ioo_reProdIm_Ioo]
          intro p hp
          rw [mem_reProdIm] at hp ⊢
          exact ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
      _ = toExt (⇑e '' (Icc (0:ℝ) s ×ℂ Icc (0:ℝ) s)) := hKclosedExt.closure_eq
      _ ⊆ toExt D := image_mono hKD
  exact ⟨Q', hzmem, hclos⟩

/-- **Step 2 for Theorem 7.2**: the image of an open set under a `K`-q.c. map is open. -/
theorem isOpen_image_of_isKQC {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    IsOpen (f '' D) := by
  obtain ⟨hD, -, -, hQ⟩ := hf
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨Qz, hzQz, hQzD⟩ := exists_topQuad_mem_closure_subset hD hz
  obtain ⟨Q'', hQ'', -⟩ := hQ Qz hQzD
  have hQzsubD : Qz.dom ⊆ D := fun w hw => by
    obtain ⟨v, hv, hvw⟩ := hQzD (subset_closure (mem_image_of_mem _ hw))
    rw [← OnePoint.coe_injective hvw]; exact hv
  refine ⟨Q''.dom, ?_, Q''.isTopQuad.1.1, ?_⟩
  · rw [hQ''.1]; exact image_mono hQzsubD
  · rw [hQ''.1]; exact ⟨z, hzQz, rfl⟩

/-- **Theorem 7.2**: the inverse of a `K`-q.c. map is `K`-q.c.

Proved via the Riemann mapping theorem. For a sub-quadrilateral `Q'` with `Q̄' ⊆ toExt (f '' D)`,
`P := f⁻¹(Q'.dom)` is an open Jordan domain (`image_isJordanDomain_of_open`), uniformized onto
`upperHalf` and normalized so `Q'`'s four vertices land on finite reals
(`exists_conformalOnto_upperHalf_of_isJordanDomain`, `exists_uniformizer_finite_vertices`, both
from `Lemmas/ImageQuad`). Composing this uniformizer's boundary correspondence with `Q'`'s own
gives a self-homeomorphism of `∂upperHalf` that either preserves or reverses the cyclic order of
`Fin 4` (`dichotomy_frontier_upperHalf`, `Lemmas/Winding`). The orientation-reversing case is
excluded: applying it to the `IsKQC` witness quadrilateral for `Q''rev` (`v` with vertices
permuted by `-i`) and comparing against `Q'`'s own cyclic order via
`cyclicStrictMono_of_conformalOnto_upperHalf` (`S06`) would give both `CyclicStrictMono xQ'` and
`CyclicStrictMono (xQ' ∘ (- ·))`, impossible by `not_cyclicStrictMono_of_cyclicStrictMono_neg`
(`Lemmas/Winding`). What remains is the orientation-preserving case, which exhibits `f⁻¹(Q')`
directly as the required image quadrilateral of `Q'` under `Function.invFunOn f D`. -/
theorem thm7_2_inv {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    IsKQC (Function.invFunOn f D) (f '' D) K := by
  obtain ⟨hD, hK1, hhom, hmod⟩ := hf
  set g : ℂ → ℂ := Function.invFunOn f D with hgdef
  have hDopen : IsOpen (f '' D) := isOpen_image_of_isKQC ⟨hD, hK1, hhom, hmod⟩
  have hsymm : IsHomeomorphOnto g (f '' D) D := isHomeomorphOnto_invFunOn hhom
  have hsymm' : IsHomeomorphOnto g (f '' D) (g '' (f '' D)) := by
    have heq : g '' (f '' D) = D := hsymm.2.2.1
    rw [heq]; exact hsymm
  refine ⟨hDopen, hK1, hsymm', ?_⟩
  intro Q' hQ'sub
  have hQ'subF : Q'.dom ⊆ f '' D := fun w hw => by
    obtain ⟨p, hp, hpw⟩ := hQ'sub (subset_closure (mem_image_of_mem _ hw))
    rw [← OnePoint.coe_injective hpw]; exact hp
  have hQ'open : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hPeq : g '' Q'.dom = D ∩ f ⁻¹' Q'.dom := by
    ext a
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hQ'subF hw
      have hgfp : g (f p) = p := hhom.2.1.leftInvOn_invFunOn hp
      refine ⟨?_, ?_⟩
      · rw [hgfp]; exact hp
      · show f (g (f p)) ∈ Q'.dom
        rw [hgfp]; exact hw
    · rintro ⟨ha, hfa⟩
      exact ⟨f a, hfa, hhom.2.1.leftInvOn_invFunOn ha⟩
  have hPopen : IsOpen (g '' Q'.dom) := by
    rw [hPeq]; exact hhom.1.isOpen_inter_preimage hD hQ'open
  obtain ⟨hPJD, hPext, hPfr⟩ :=
    image_isJordanDomain_of_open hDopen hsymm.1 hsymm.2.1 hQ'sub hPopen
  have hPclosD : closure (toExt (g '' Q'.dom)) ⊆ toExt D :=
    closure_toExt_image_subset hsymm.1 hQ'sub (le_of_eq hsymm.2.2.1)
  have hPbdd : Bornology.IsBounded (g '' Q'.dom) := by
    apply isBounded_of_extInf_notMem_closure_toExt
    intro hmem
    exact extInf_notMem_toExt D (hPclosD hmem)
  obtain ⟨φP0, hφP0, ΦP0, hΦP0⟩ :=
    exists_conformalOnto_upperHalf_of_isJordanDomain hPJD hPbdd
  set v : Fin 4 → ExtPlane := fun i => OnePoint.map g (Q'.vert i) with hvdef
  have hvfr : ∀ i, v i ∈ frontier (toExt (g '' Q'.dom)) := fun i =>
    hPfr ▸ mem_image_of_mem _ (Q'.isTopQuad.2.1 i)
  obtain ⟨φP, ΦP, xP, hφP, hΦP, hxP⟩ :=
    exists_uniformizer_finite_vertices hPopen hφP0 hΦP0 hvfr
  -- step 4: orientation
  obtain ⟨hQ'J, hQ'v, φQ', ΦQ', xQ', hφQ', hΦQ', hxQ'cyc, hxQ'⟩ := Q'.isTopQuad
  have hΦQ'fr : ΦQ' '' frontier (toExt Q'.dom) = frontier (toExt upperHalf) :=
    IsHomeoExtension.image_frontier hQ'open scExt_isOpen_upperHalf hφQ'.2.2 hΦQ'
  have hΦPfr : ΦP '' frontier (toExt (g '' Q'.dom)) = frontier (toExt upperHalf) :=
    IsHomeoExtension.image_frontier hPopen scExt_isOpen_upperHalf hφP.2.2 hΦP
  set Ginv : ExtPlane → ExtPlane := Function.invFunOn ΦQ' (closure (toExt Q'.dom)) with hGinvdef
  have hΦQ'injC : InjOn ΦQ' (closure (toExt Q'.dom)) := hΦQ'.2.2.1
  have hGinvMaps : MapsTo Ginv (frontier (toExt upperHalf)) (frontier (toExt Q'.dom)) := by
    intro p hp
    rw [← hΦQ'fr] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqC : q ∈ closure (toExt Q'.dom) := frontier_subset_closure hq
    rw [hGinvdef]
    rw [hΦQ'injC.leftInvOn_invFunOn hqC]
    exact hq
  set F : ExtPlane → ExtPlane := ΦP ∘ (OnePoint.map g) ∘ Ginv with hFdef
  have hFmaps : MapsTo F (frontier (toExt upperHalf)) (frontier (toExt upperHalf)) := by
    intro p hp
    have h1 := hGinvMaps hp
    have h2 : OnePoint.map g (Ginv p) ∈ frontier (toExt (g '' Q'.dom)) :=
      hPfr ▸ mem_image_of_mem _ h1
    exact hΦPfr ▸ mem_image_of_mem _ h2
  have hGinvCont : ContinuousOn Ginv (closure (toExt upperHalf)) := by
    rw [← hΦQ'.2.2.2]
    exact continuousOn_invFunOn_of_isClosed isClosed_closure hΦQ'.2.1 hΦQ'.2.2.1
  have hGinvCont' : ContinuousOn Ginv (frontier (toExt upperHalf)) :=
    hGinvCont.mono frontier_subset_closure
  have hgCont' : ContinuousOn (OnePoint.map g) (frontier (toExt Q'.dom)) :=
    hPext.2.1.mono frontier_subset_closure
  have hgMaps : MapsTo (OnePoint.map g) (frontier (toExt Q'.dom)) (frontier (toExt (g '' Q'.dom))) :=
    fun q hq => hPfr ▸ mem_image_of_mem _ hq
  have hΦPcont' : ContinuousOn ΦP (frontier (toExt (g '' Q'.dom))) :=
    hΦP.2.1.mono frontier_subset_closure
  have hinnerCont : ContinuousOn ((OnePoint.map g) ∘ Ginv) (frontier (toExt upperHalf)) :=
    hgCont'.comp hGinvCont' hGinvMaps
  have hFcont : ContinuousOn F (frontier (toExt upperHalf)) :=
    hΦPcont'.comp hinnerCont (fun p hp => hgMaps (hGinvMaps hp))
  have hGinvInj : InjOn Ginv (closure (toExt upperHalf)) := by
    intro p hp q hq hpq
    rw [← hΦQ'.2.2.2] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    rw [hGinvdef] at hpq
    rw [hΦQ'injC.leftInvOn_invFunOn ha, hΦQ'injC.leftInvOn_invFunOn hb] at hpq
    rw [hpq]
  have hGinvInj' : InjOn Ginv (frontier (toExt upperHalf)) :=
    hGinvInj.mono frontier_subset_closure
  have hgInj' : InjOn (OnePoint.map g) (frontier (toExt Q'.dom)) :=
    hPext.2.2.1.mono frontier_subset_closure
  have hΦPinj' : InjOn ΦP (frontier (toExt (g '' Q'.dom))) :=
    hΦP.2.2.1.mono frontier_subset_closure
  have hinnerInj : InjOn ((OnePoint.map g) ∘ Ginv) (frontier (toExt upperHalf)) :=
    hgInj'.comp hGinvInj' hGinvMaps
  have hFinj : InjOn F (frontier (toExt upperHalf)) :=
    hΦPinj'.comp hinnerInj (fun p hp => hgMaps (hGinvMaps hp))
  have hleftInv : Set.LeftInvOn Ginv ΦQ' (frontier (toExt Q'.dom)) :=
    hΦQ'injC.leftInvOn_invFunOn.mono frontier_subset_closure
  have hGinvImg : Ginv '' frontier (toExt upperHalf) = frontier (toExt Q'.dom) := by
    rw [← hΦQ'fr]
    exact hleftInv.image_image
  have hFimg : F '' frontier (toExt upperHalf) = frontier (toExt upperHalf) := by
    rw [hFdef, Set.image_comp, Set.image_comp, hGinvImg, ← hPfr, hΦPfr]
  have hFvert : ∀ i, F (((xQ' i : ℝ) : ℂ) : ExtPlane) = (((xP i : ℝ) : ℂ) : ExtPlane) := by
    intro i
    show ΦP (OnePoint.map g (Ginv (((xQ' i : ℝ) : ℂ) : ExtPlane))) = _
    rw [← hxQ' i, hGinvdef]
    have hQvi : Q'.vert i ∈ closure (toExt Q'.dom) := frontier_subset_closure (Q'.isTopQuad.2.1 i)
    rw [hΦQ'injC.leftInvOn_invFunOn hQvi]
    exact hxP i
  have hfg_id : ∀ p ∈ closure (toExt Q'.dom), OnePoint.map f (OnePoint.map g p) = p := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z =>
      obtain ⟨w, hw, hwz⟩ := hQ'sub hp
      have hzeq : w = z := OnePoint.coe_injective hwz
      have hzD : z ∈ f '' D := hzeq ▸ hw
      show OnePoint.map f (OnePoint.map g ((z:ℂ) : ExtPlane)) = ((z:ℂ) : ExtPlane)
      rw [OnePoint.map_some, OnePoint.map_some]
      congr 1
      exact Function.invFunOn_eq hzD
  have hfgQ' : f '' (g '' Q'.dom) = Q'.dom := by
    rw [hPeq]
    apply subset_antisymm
    · rintro y ⟨a, ⟨-, hfa⟩, rfl⟩; exact hfa
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := hQ'subF hy
      exact ⟨a, ⟨ha, hy⟩, rfl⟩
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  rcases dichotomy_frontier_upperHalf hFcont hFinj hFimg with hpres | hrev
  · -- preserving orientation: Q'' := ⟨P, v, ...⟩ works directly
    have hxPcyc : CyclicStrictMono xP := hpres xQ' hxQ'cyc xP hFvert
    set Q'' : TopQuad := ⟨g '' Q'.dom, v, hPJD, hvfr, φP, ΦP, xP, hφP, hΦP, hxPcyc, hxP⟩
      with hQ''def
    have hQ''Image_g : Q'.IsImageUnder Q'' g := ⟨rfl, fun i => rfl⟩
    have hQ''Image_f : Q''.IsImageUnder Q' f := by
      refine ⟨hfgQ'.symm, fun i => ?_⟩
      show Q'.vert i = OnePoint.map f (v i)
      exact (hfg_id (Q'.vert i) (frontier_subset_closure (Q'.isTopQuad.2.1 i))).symm
    have hmodle : Q''.modulus ≤ K * Q'.modulus := by
      have h := (IsKQC.modulus_ge ⟨hD, hK1, hhom, hmod⟩ Q'' Q' hPclosD hQ''Image_f).1
      rw [div_le_iff₀ hK0] at h
      linarith [h]
    exact ⟨Q'', hQ''Image_g, hmodle⟩
  · -- reversing orientation: contradiction via W6/W7
    exfalso
    have hxPcyc' : CyclicStrictMono (fun i => xP (-i)) := hrev xQ' hxQ'cyc xP hFvert
    set Q''rev : TopQuad :=
      ⟨g '' Q'.dom, fun i => v (-i), hPJD, fun i => hvfr (-i), φP, ΦP, fun i => xP (-i), hφP, hΦP,
        hxPcyc', fun i => hxP (-i)⟩ with hQ''revdef
    obtain ⟨Qppp, hQpppImage, -⟩ := hmod Q''rev hPclosD
    have hQpppeq : Qppp.dom = Q'.dom := by rw [hQpppImage.1]; exact hfgQ'
    have hQpppvert : ∀ i, Qppp.vert i = Q'.vert (-i) := by
      intro i
      rw [hQpppImage.2 i]
      show OnePoint.map f (v (-i)) = Q'.vert (-i)
      exact hfg_id (Q'.vert (-i)) (frontier_subset_closure (Q'.isTopQuad.2.1 (-i)))
    obtain ⟨hQpppJ, hQpppv, phi3, Phi3, x3, hphi3, hPhi3, hx3cyc, hx3⟩ := Qppp.isTopQuad
    rw [hQpppeq] at hphi3 hPhi3
    have hvpts : ∀ i, Q'.vert (-i) ∈ closure (toExt Q'.dom) :=
      fun i => frontier_subset_closure (Q'.isTopQuad.2.1 (-i))
    have hx3p : ∀ i, Phi3 (Q'.vert (-i)) = (((x3 i : ℝ) : ℂ) : ExtPlane) := by
      intro i
      rw [← hQpppvert i]
      exact hx3 i
    have hyrev : CyclicStrictMono (fun i => xQ' (-i)) :=
      cyclicStrictMono_of_conformalOnto_upperHalf hQ'open hphi3 hPhi3 hφQ' hΦQ' hvpts hx3cyc hx3p
        (fun i => hxQ' (-i))
    exact not_cyclicStrictMono_of_cyclicStrictMono_neg hxQ'cyc hyrev

/-! ### Theorem 7.3, piece A -/


/-- **A1.** A boundary extension restricts to any subset of the domain. -/
theorem oqc_isHomeoExtension_restrict {f : ℂ → ℂ} {U V W : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) (hWU : W ⊆ U) :
    IsHomeoExtension f W (f '' W) F := by
  have hCWU : closure (toExt W) ⊆ closure (toExt U) := closure_mono (image_mono hWU)
  have hFC : ContinuousOn F (closure (toExt W)) := hF.2.1.mono hCWU
  have hFinj : InjOn F (closure (toExt W)) := hF.2.2.1.mono hCWU
  have htoExt : F '' toExt W = toExt (f '' W) := by
    ext p
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, mem_image_of_mem f hz, (hF.1 z (hWU hz)).symm⟩
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, hF.1 z (hWU hz)⟩
  have hFimg : F '' closure (toExt W) = closure (toExt (f '' W)) := by
    refine subset_antisymm ?_ ?_
    · rw [← htoExt]
      exact hFC.image_closure
    · refine closure_minimal ?_
        (isClosed_closure.isCompact.image_of_continuousOn hFC).isClosed
      rw [← htoExt]
      exact image_mono subset_closure
  exact ⟨fun z hz => hF.1 z (hWU hz), hFC, hFinj, hFimg⟩

/-- **A2.** The image of a quadrilateral `Q ⊆ U` (closure NOT required inside `U`) under a
conformal map of `U` with boundary extension `F` is a quadrilateral with vertices `F (Q.vert i)`,
conformally equivalent to `Q`. -/
theorem oqc_exists_image_conformal_ext {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F)
    {Q : TopQuad} (hQU : Q.dom ⊆ U) :
    ∃ Q' : TopQuad, Q'.dom = f '' Q.dom ∧ (∀ i, Q'.vert i = F (Q.vert i)) ∧ Q.ConfEquiv Q' := by
  obtain ⟨hJ, hQv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := Q.isTopQuad
  have hQo : IsOpen Q.dom := hJ.1
  have hfQ : IsConformalOnto f Q.dom (f '' Q.dom) := ⟨hf.1.mono hQU, hf.2.1.mono hQU, rfl⟩
  have hext : IsHomeoExtension f Q.dom (f '' Q.dom) F := oqc_isHomeoExtension_restrict hF hQU
  have hfo : IsOpen (f '' Q.dom) := hfQ.isOpen hQo
  have hfr : F '' frontier (toExt Q.dom) = frontier (toExt (f '' Q.dom)) :=
    hext.image_frontier hQo hfo rfl
  set C := closure (toExt Q.dom) with hC
  have hFC : ContinuousOn F C := hext.2.1
  have hFinj : InjOn F C := hext.2.2.1
  have hfrC : frontier (toExt Q.dom) ⊆ C := frontier_subset_closure
  have hinv : IsHomeoExtension (Function.invFunOn f Q.dom) (f '' Q.dom) Q.dom
      (Function.invFunOn F C) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzC : ((z : ℂ) : ExtPlane) ∈ C := subset_closure (mem_image_of_mem _ hz)
      rw [hfQ.2.1.leftInvOn_invFunOn hz, ← hext.1 z hz]
      exact hFinj.leftInvOn_invFunOn hzC
    · rw [← hext.2.2.2]
      exact continuousOn_invFunOn_of_isClosed isClosed_closure hFC hFinj
    · rw [← hext.2.2.2]
      intro p hp q hq hpq
      calc p = F (Function.invFunOn F C p) := (Function.invFunOn_eq hp).symm
        _ = F (Function.invFunOn F C q) := by rw [hpq]
        _ = q := Function.invFunOn_eq hq
    · rw [← hext.2.2.2]
      exact hFinj.leftInvOn_invFunOn.image_image
  have hTQ : IsTopQuad (f '' Q.dom) (fun i => F (Q.vert i)) := by
    refine ⟨⟨hfo, hJ.2.1.image f (hf.1.continuousOn.mono hQU), ?_⟩, fun i => ?_,
      φ ∘ Function.invFunOn f Q.dom, Φ ∘ Function.invFunOn F C, x, hφ.comp (hfQ.symm hQo),
      hΦ.comp hinv (hfQ.symm hQo).mapsTo, hx, fun i => ?_⟩
    · obtain ⟨γ, hγc, hγi, hγr⟩ := hJ.2.2
      have hγC : ∀ t, γ t ∈ C := fun t => hfrC (hγr ▸ mem_range_self t)
      refine ⟨F ∘ γ, hFC.comp_continuous hγc hγC,
        fun s t hst => hγi (hFinj (hγC s) (hγC t) hst), ?_⟩
      rw [range_comp, hγr, hfr]
    · rw [← hfr]
      exact mem_image_of_mem F (hQv i)
    · show Φ (Function.invFunOn F C (F (Q.vert i))) = _
      rw [hFinj.leftInvOn_invFunOn (hfrC (hQv i))]
      exact hΦv i
  exact ⟨⟨f '' Q.dom, fun i => F (Q.vert i), hTQ⟩, rfl, fun i => rfl, f, F, hfQ, hext, fun i => rfl⟩


/-! ### Theorem 7.3, piece B -/


/-- **B.** Under a `1`-q.c. map the image quadrilateral of Definition 7.1 has the SAME modulus. -/
theorem oqc_exists_image_modulus_eq {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) {Q : TopQuad}
    (hQ : closure (toExt Q.dom) ⊆ toExt D) :
    ∃ Q' : TopQuad, Q.IsImageUnder Q' f ∧ Q'.modulus = Q.modulus := by
  obtain ⟨Q', hQ', hle⟩ := hf.2.2.2 Q hQ
  refine ⟨Q', hQ', le_antisymm (by linarith [hle]) ?_⟩
  have hQsubD : Q.dom ⊆ D := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hQ (subset_closure (mem_image_of_mem _ hz))
    rwa [← OnePoint.coe_injective hwz]
  have hinvKQC : IsKQC (Function.invFunOn f D) (f '' D) 1 := thm7_2_inv hf
  have hQ'D : closure (toExt Q'.dom) ⊆ toExt (f '' D) := by
    rw [hQ'.1]
    exact closure_toExt_image_subset hf.2.2.1.1 hQ (subset_refl _)
  obtain ⟨Q'', hQ'', hle'⟩ := hinvKQC.2.2.2 Q' hQ'D
  have hLI : Set.LeftInvOn (Function.invFunOn f D) f D := hf.2.2.1.2.1.leftInvOn_invFunOn
  have hQ'Q : Q'.IsImageUnder Q (Function.invFunOn f D) := by
    refine ⟨?_, ?_⟩
    · rw [hQ'.1]
      exact ((hLI.mono hQsubD).image_image).symm
    · intro i
      obtain ⟨z, hzD, hzi⟩ := hQ (frontier_subset_closure (Q.isTopQuad.2.1 i))
      rw [hQ'.2 i, ← hzi]
      show (z : ExtPlane) = OnePoint.map (Function.invFunOn f D) (OnePoint.map f (z : ExtPlane))
      rw [show OnePoint.map f ((z : ℂ) : ExtPlane) = ((f z : ℂ) : ExtPlane) from rfl,
        show OnePoint.map (Function.invFunOn f D) ((f z : ℂ) : ExtPlane) =
          ((Function.invFunOn f D (f z) : ℂ) : ExtPlane) from rfl, hLI hzD]
  rw [hQ''.unique hQ'Q] at hle'
  linarith [hle']


/-! ### Theorem 7.3, piece D -/


/-- **D (owner -46) — the core.** Let `f` be `1`-q.c. on `D`, `Q̄ ⊆ D`, `Q'` the image quadrilateral, `φ`, `ψ`
standard conformal maps of `Q`, `Q'` onto `R(0,a,a+bi,bi)`, `R(0,a',a'+b'i,b'i)`.  Then the conjugated map
`g = ψ ∘ f ∘ φ⁻¹` carries the left sub-rectangle `(0,s)×(0,b)` onto `(0, (b'/b)s)×(0,b')`. -/
theorem oqc_conjugate_vertical {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) {Q Q' : TopQuad}
    (hQD : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f)
    {a b a' b' : ℝ} {φ ψ : ℂ → ℂ} (hφ : Q.IsStdConformalMap a b φ)
    (hψ : Q'.IsStdConformalMap a' b' ψ) {s : ℝ} (hs : 0 < s) (hsa : s < a) :
    ψ '' (f '' (Function.invFunOn φ Q.dom '' rectangle s b)) = rectangle (b' / b * s) b' := by
  obtain ⟨ha, hb, hφconf, Φ, hΦ, hΦv⟩ := hφ
  obtain ⟨ha', hb', hψconf, Ψ, hΨ, hΨv⟩ := hψ
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hDo : IsOpen D := hf.1
  have hfDc : ContinuousOn f D := hf.2.2.1.1
  have hfDi : InjOn f D := hf.2.2.1.2.1
  have hQ'domEq : Q'.dom = f '' Q.dom := hQ'.1
  have hQsubD : Q.dom ⊆ D := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hQD (subset_closure (mem_image_of_mem _ hz))
    rw [← OnePoint.coe_injective hwz]
    exact hw
  -- Step 1: a / b = a' / b'
  have hMQ : Q.modulus = a / b := modulus_eq_of_equivRect Q ⟨φ, ha, hb, hφconf, Φ, hΦ, hΦv⟩
  have hMQ' : Q'.modulus = a' / b' := modulus_eq_of_equivRect Q' ⟨ψ, ha', hb', hψconf, Ψ, hΨ, hΨv⟩
  have hab : a / b = a' / b' := by
    obtain ⟨Q'', hQ''img, hQ''mod⟩ := oqc_exists_image_modulus_eq hf hQD
    have hQ''eq : Q'' = Q' := hQ''img.unique hQ'
    rw [← hMQ, ← hMQ', ← hQ''mod, hQ''eq]
  have hsa' : (0 : ℝ) < a - s := by linarith
  -- global boundary extensions
  set Φinv : ℂ → ℂ := Function.invFunOn φ Q.dom with hΦinv_def
  set ΦInvExt : ExtPlane → ExtPlane := Function.invFunOn Φ (closure (toExt Q.dom)) with hΦInvExt_def
  have hΦinvConf : IsConformalOnto Φinv (rectangle a b) Q.dom := hφconf.symm hQo
  have hΦinvExtFact : IsHomeoExtension Φinv (rectangle a b) Q.dom ΦInvExt :=
    isHomeoExtension_invFunOn hφconf hΦ
  have hΦinvRab : Φinv '' rectangle a b = Q.dom := hΦinvConf.2.2
  have hfo : IsOpen (f '' Q.dom) := hQ'domEq ▸ hQ'o
  have hextQ' : IsHomeoExtension f Q.dom Q'.dom (OnePoint.map f) := by
    rw [hQ'domEq]
    exact (image_isJordanDomain_of_open hDo hfDc hfDi hQD hfo).2.1
  -- R₁, R₂: the two sub-rectangles of R(0,a,a+bi,bi)
  set R₁ : TopQuad := rectQuad hs hb with hR1_def
  set Rc : TopQuad := rectQuad hsa' hb with hRc_def
  have htrans : IsConformalOnto (fun z : ℂ => z + (s : ℂ)) univ univ := by
    refine ⟨(differentiable_id.add_const _).differentiableOn, ?_, ?_⟩
    · intro x _ y _ h
      simpa using h
    · ext z
      simp only [mem_image, mem_univ, true_and, iff_true]
      exact ⟨z - s, by ring⟩
  have hRcclosure : closure (toExt Rc.dom) ⊆ toExt (univ : Set ℂ) := by
    show closure (toExt (rectangle (a - s) b)) ⊆ toExt univ
    rw [closure_toExt_of_isBounded (isBounded_rectangle (a - s) b)]
    exact image_mono (subset_univ _)
  obtain ⟨R₂, hR2img, hR2ce⟩ := aqc_exists_image_conformal isOpen_univ htrans hRcclosure
  have hR1dom : R₁.dom = rectangle s b := rfl
  have hRcdom : Rc.dom = rectangle (a - s) b := rfl
  have hR2dom : R₂.dom = (fun z : ℂ => z + (s : ℂ)) '' rectangle (a - s) b := hR2img.1
  have hR1sub : R₁.dom ⊆ rectangle a b := by
    rw [hR1dom]
    rintro z ⟨hz1, hz2, hz3, hz4⟩
    exact ⟨hz1, hz2.trans hsa, hz3, hz4⟩
  have hR2sub : R₂.dom ⊆ rectangle a b := by
    rw [hR2dom]
    rintro z ⟨w, ⟨hw1, hw2, hw3, hw4⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] <;>
      linarith
  have hR1R2disj : Disjoint R₁.dom R₂.dom := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [hR1dom] at hz1
    rw [hR2dom] at hz2
    obtain ⟨hz1a, hz1b, hz1c, hz1d⟩ := hz1
    obtain ⟨w, ⟨hw1, hw2, hw3, hw4⟩, rfl⟩ := hz2
    simp only [Complex.add_re, Complex.ofReal_re] at hz1b
    linarith
  -- pull R₁, R₂ back into Q via Φinv
  obtain ⟨Q₁, hQ1dom, hQ1vert, hQ1ce⟩ :=
    oqc_exists_image_conformal_ext (isOpen_rectangle a b) hΦinvConf hΦinvExtFact hR1sub
  obtain ⟨Q₂, hQ2dom, hQ2vert, hQ2ce⟩ :=
    oqc_exists_image_conformal_ext (isOpen_rectangle a b) hΦinvConf hΦinvExtFact hR2sub
  have hQ1subQ : Q₁.dom ⊆ Q.dom := by rw [hQ1dom, ← hΦinvRab]; exact image_mono hR1sub
  have hQ2subQ : Q₂.dom ⊆ Q.dom := by rw [hQ2dom, ← hΦinvRab]; exact image_mono hR2sub
  have hΦinvInjRab : InjOn Φinv (rectangle a b) := hΦinvConf.2.1
  have hQ1Q2disj : Disjoint Q₁.dom Q₂.dom := by
    rw [hQ1dom, hQ2dom, Set.disjoint_left]
    rintro _ ⟨z1, hz1, rfl⟩ ⟨z2, hz2, heq⟩
    have hzeq := hΦinvInjRab (hR1sub hz1) (hR2sub hz2) heq.symm
    exact Set.disjoint_left.mp hR1R2disj hz1 (hzeq ▸ hz2)
  -- push Q₁, Q₂ forward under f (stub B: image quadrilateral with equal modulus)
  have hQ1closure : closure (toExt Q₁.dom) ⊆ toExt D :=
    (closure_mono (image_mono hQ1subQ)).trans hQD
  have hQ2closure : closure (toExt Q₂.dom) ⊆ toExt D :=
    (closure_mono (image_mono hQ2subQ)).trans hQD
  obtain ⟨Q₁', hQ1'img, hQ1'mod⟩ := oqc_exists_image_modulus_eq hf hQ1closure
  obtain ⟨Q₂', hQ2'img, hQ2'mod⟩ := oqc_exists_image_modulus_eq hf hQ2closure
  have hQ1'subQ' : Q₁'.dom ⊆ Q'.dom := by rw [hQ1'img.1, hQ'domEq]; exact image_mono hQ1subQ
  have hQ2'subQ' : Q₂'.dom ⊆ Q'.dom := by rw [hQ2'img.1, hQ'domEq]; exact image_mono hQ2subQ
  have hfDiQ : InjOn f Q.dom := hfDi.mono hQsubD
  have hQ1'Q2'disj : Disjoint Q₁'.dom Q₂'.dom := by
    rw [hQ1'img.1, hQ2'img.1, Set.disjoint_left]
    rintro _ ⟨z1, hz1, rfl⟩ ⟨z2, hz2, heq⟩
    have hzeq := hfDiQ (hQ1subQ hz1) (hQ2subQ hz2) heq.symm
    exact Set.disjoint_left.mp hQ1Q2disj hz1 (hzeq ▸ hz2)
  have hextQ1 : IsHomeoExtension f Q₁.dom Q₁'.dom (OnePoint.map f) := by
    have h := oqc_isHomeoExtension_restrict hextQ' hQ1subQ
    rwa [← hQ1'img.1] at h
  have hextQ2 : IsHomeoExtension f Q₂.dom Q₂'.dom (OnePoint.map f) := by
    have h := oqc_isHomeoExtension_restrict hextQ' hQ2subQ
    rwa [← hQ2'img.1] at h
  -- push Q₁', Q₂' forward under ψ
  obtain ⟨P₁, hP1dom, hP1vert, hP1ce⟩ :=
    oqc_exists_image_conformal_ext hQ'o hψconf hΨ hQ1'subQ'
  obtain ⟨P₂, hP2dom, hP2vert, hP2ce⟩ :=
    oqc_exists_image_conformal_ext hQ'o hψconf hΨ hQ2'subQ'
  have hψQ' : ψ '' Q'.dom = rectangle a' b' := hψconf.2.2
  have hP1sub : P₁.dom ⊆ rectangle a' b' := by rw [hP1dom, ← hψQ']; exact image_mono hQ1'subQ'
  have hP2sub : P₂.dom ⊆ rectangle a' b' := by rw [hP2dom, ← hψQ']; exact image_mono hQ2'subQ'
  have hψInjQ' : InjOn ψ Q'.dom := hψconf.2.1
  have hP1P2disj : Disjoint P₁.dom P₂.dom := by
    rw [hP1dom, hP2dom, Set.disjoint_left]
    rintro _ ⟨w1, hw1, rfl⟩ ⟨w2, hw2, heq⟩
    have hweq := hψInjQ' (hQ1'subQ' hw1) (hQ2'subQ' hw2) heq.symm
    exact Set.disjoint_left.mp hQ1'Q2'disj hw1 (hweq ▸ hw2)
  -- moduli
  have hR1mod : R₁.modulus = s / b := modulus_rectQuad hs hb
  have hRcmod : Rc.modulus = (a - s) / b := modulus_rectQuad hsa' hb
  have hR2mod : R₂.modulus = (a - s) / b :=
    (thm1_3_modulus_conformal_invariant hR2ce).symm.trans hRcmod
  have hQ1mod : Q₁.modulus = s / b := (thm1_3_modulus_conformal_invariant hQ1ce).symm.trans hR1mod
  have hQ2mod : Q₂.modulus = (a - s) / b :=
    (thm1_3_modulus_conformal_invariant hQ2ce).symm.trans hR2mod
  have hP1mod : P₁.modulus = s / b :=
    ((thm1_3_modulus_conformal_invariant hP1ce).symm.trans hQ1'mod).trans hQ1mod
  have hP2mod : P₂.modulus = (a - s) / b :=
    ((thm1_3_modulus_conformal_invariant hP2ce).symm.trans hQ2'mod).trans hQ2mod
  have hsum : P₁.modulus + P₂.modulus = a' / b' := by
    rw [hP1mod, hP2mod, ← hab, ← add_div]
    congr 1
    ring
  -- side-transport machinery
  have image_side_gen : ∀ (R S : TopQuad) {g : ℂ → ℂ} {G : ExtPlane → ExtPlane},
      IsConformalOnto g R.dom S.dom → IsHomeoExtension g R.dom S.dom G →
      (∀ i, S.vert i = G (R.vert i)) → ∀ i, G '' R.side i = S.side i := by
    intro R S g G hgconf hgext hvert i
    have h := TopQuad.image_side (S.isTopQuad.1.1) hgconf hgext i
    rw [← hvert i, ← hvert (i + 1), ← hvert (i + 2), ← TopQuad.side_eq_boundaryArc] at h
    exact h
  have image_side_gen_homeo : ∀ (R S : TopQuad) {g : ℂ → ℂ} {G : ExtPlane → ExtPlane},
      g '' R.dom = S.dom → IsHomeoExtension g R.dom S.dom G →
      (∀ i, S.vert i = G (R.vert i)) → ∀ i, G '' R.side i = S.side i := by
    intro R S g G himg hgext hvert i
    have h := aqc_image_side_homeo (S.isTopQuad.1.1) himg hgext i
    rw [← hvert i, ← hvert (i + 1), ← hvert (i + 2), ← TopQuad.side_eq_boundaryArc] at h
    exact h
  have hmapToExt : ∀ (g : ℂ → ℂ) (S : Set ℂ), OnePoint.map g '' toExt S = toExt (g '' S) := by
    intro g S
    simp only [toExt, image_image]
    rfl
  -- Φinv vertex correspondence on the whole rectangle a b
  have hΦinvExt_vert : ∀ i, Q.vert i = ΦInvExt (rectVert a b i) := by
    intro i
    have hmem : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    have h := hΦ.2.2.1.leftInvOn_invFunOn hmem
    rw [hΦv i] at h
    exact h.symm
  -- whole-rectangle side chain
  have hchainR : ∀ i, ΦInvExt '' (rectQuad ha hb).side i = Q.side i := fun i =>
    image_side_gen (rectQuad ha hb) Q hΦinvConf hΦinvExtFact hΦinvExt_vert i
  have hchainQ : ∀ i, OnePoint.map f '' Q.side i = Q'.side i := fun i =>
    image_side_gen_homeo Q Q' hQ'domEq.symm hextQ' hQ'.2 i
  have hchainQ' : ∀ i, Ψ '' Q'.side i = (rectQuad ha' hb').side i := fun i =>
    image_side_gen Q' (rectQuad ha' hb') hψconf hΨ (fun j => (hΨv j).symm) i
  have hchainWhole : ∀ i, Ψ '' (OnePoint.map f '' (ΦInvExt '' (rectQuad ha hb).side i)) =
      (rectQuad ha' hb').side i := by
    intro i
    rw [hchainR i, hchainQ i, hchainQ' i]
  -- base rectangle side facts
  have hRabside0 : (rectQuad ha hb).side 0 = toExt (Icc 0 a ×ℂ {0}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_bottom ha hb
  have hRabside2 : (rectQuad ha hb).side 2 = toExt (Icc 0 a ×ℂ {b}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_top ha hb
  have hRabside0' : (rectQuad ha' hb').side 0 = toExt (Icc 0 a' ×ℂ {0}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_bottom ha' hb'
  have hRabside2' : (rectQuad ha' hb').side 2 = toExt (Icc 0 a' ×ℂ {b'}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_top ha' hb'
  -- restricted conformal / extension data for R₁, R₂ → Q₁, Q₂ → Q₁', Q₂' → P₁, P₂
  have hΦinvConfQ1 : IsConformalOnto Φinv R₁.dom Q₁.dom :=
    ⟨hΦinvConf.1.mono hR1sub, hΦinvConf.2.1.mono hR1sub, hQ1dom.symm⟩
  have hΦinvConfQ2 : IsConformalOnto Φinv R₂.dom Q₂.dom :=
    ⟨hΦinvConf.1.mono hR2sub, hΦinvConf.2.1.mono hR2sub, hQ2dom.symm⟩
  have hextR1 : IsHomeoExtension Φinv R₁.dom Q₁.dom ΦInvExt := by
    have h := oqc_isHomeoExtension_restrict hΦinvExtFact hR1sub
    rwa [← hQ1dom] at h
  have hextR2 : IsHomeoExtension Φinv R₂.dom Q₂.dom ΦInvExt := by
    have h := oqc_isHomeoExtension_restrict hΦinvExtFact hR2sub
    rwa [← hQ2dom] at h
  have hψconfQ1' : IsConformalOnto ψ Q₁'.dom P₁.dom :=
    ⟨hψconf.1.mono hQ1'subQ', hψconf.2.1.mono hQ1'subQ', hP1dom.symm⟩
  have hψconfQ2' : IsConformalOnto ψ Q₂'.dom P₂.dom :=
    ⟨hψconf.1.mono hQ2'subQ', hψconf.2.1.mono hQ2'subQ', hP2dom.symm⟩
  have hextQ1' : IsHomeoExtension ψ Q₁'.dom P₁.dom Ψ := by
    have h := oqc_isHomeoExtension_restrict hΨ hQ1'subQ'
    rwa [← hP1dom] at h
  have hextQ2' : IsHomeoExtension ψ Q₂'.dom P₂.dom Ψ := by
    have h := oqc_isHomeoExtension_restrict hΨ hQ2'subQ'
    rwa [← hP2dom] at h
  have hchain1 : ∀ i, Ψ '' (OnePoint.map f '' (ΦInvExt '' R₁.side i)) = P₁.side i := by
    intro i
    rw [image_side_gen R₁ Q₁ hΦinvConfQ1 hextR1 hQ1vert i,
      image_side_gen_homeo Q₁ Q₁' hQ1'img.1.symm hextQ1 hQ1'img.2 i,
      image_side_gen Q₁' P₁ hψconfQ1' hextQ1' hP1vert i]
  have hchain2 : ∀ i, Ψ '' (OnePoint.map f '' (ΦInvExt '' R₂.side i)) = P₂.side i := by
    intro i
    rw [image_side_gen R₂ Q₂ hΦinvConfQ2 hextR2 hQ2vert i,
      image_side_gen_homeo Q₂ Q₂' hQ2'img.1.symm hextQ2 hQ2'img.2 i,
      image_side_gen Q₂' P₂ hψconfQ2' hextQ2' hP2vert i]
  -- concrete sides of R₁, Rc, R₂
  have hR1side0 : R₁.side 0 = toExt (Icc 0 s ×ℂ {0}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_bottom hs hb
  have hR1side2 : R₁.side 2 = toExt (Icc 0 s ×ℂ {b}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_top hs hb
  have hRcside0 : Rc.side 0 = toExt (Icc 0 (a - s) ×ℂ {0}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_bottom hsa' hb
  have hRcside2 : Rc.side 2 = toExt (Icc 0 (a - s) ×ℂ {b}) := by
    rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_top hsa' hb
  have hfo2 : IsOpen ((fun z : ℂ => z + (s : ℂ)) '' Rc.dom) := hR2img.1 ▸ R₂.isTopQuad.1.1
  have hextRc : IsHomeoExtension (fun z : ℂ => z + (s : ℂ)) Rc.dom
      ((fun z : ℂ => z + (s : ℂ)) '' Rc.dom) (OnePoint.map (fun z : ℂ => z + (s : ℂ))) :=
    (image_isJordanDomain_of_open isOpen_univ htrans.1.continuousOn htrans.2.1 hRcclosure
      hfo2).2.1
  have hextRc' : IsHomeoExtension (fun z : ℂ => z + (s : ℂ)) Rc.dom R₂.dom
      (OnePoint.map (fun z : ℂ => z + (s : ℂ))) := by
    rw [hR2img.1]; exact hextRc
  have hchainT : ∀ i, OnePoint.map (fun z : ℂ => z + (s : ℂ)) '' Rc.side i = R₂.side i := fun i =>
    image_side_gen_homeo Rc R₂ hR2img.1.symm hextRc' hR2img.2 i
  have hIccTrans : ∀ c : ℝ, (fun z : ℂ => z + (s : ℂ)) '' (Icc 0 (a - s) ×ℂ ({c} : Set ℝ)) =
      Icc s a ×ℂ ({c} : Set ℝ) := by
    intro c
    ext z
    simp only [mem_image, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨⟨hw1, hw2⟩, hw3⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re]; linarith
      · simp only [Complex.add_re, Complex.ofReal_re]; linarith
      · simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hw3
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      refine ⟨z - (s : ℂ), ⟨⟨?_, ?_⟩, ?_⟩, by ring⟩
      · simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      · simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      · simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hz3
  have hR2side0 : R₂.side 0 = toExt (Icc s a ×ℂ ({0} : Set ℝ)) := by
    rw [← hchainT 0, hRcside0, hmapToExt, hIccTrans 0]
  have hR2side2 : R₂.side 2 = toExt (Icc s a ×ℂ ({b} : Set ℝ)) := by
    rw [← hchainT 2, hRcside2, hmapToExt, hIccTrans b]
  -- containment in the sides of the full rectangle a b
  have hR1side0sub : R₁.side 0 ⊆ (rectQuad ha hb).side 0 := by
    rw [hR1side0, hRabside0]
    apply image_mono
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨hz1, hz2.trans hsa.le⟩, hz3⟩
  have hR1side2sub : R₁.side 2 ⊆ (rectQuad ha hb).side 2 := by
    rw [hR1side2, hRabside2]
    apply image_mono
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨hz1, hz2.trans hsa.le⟩, hz3⟩
  have hR2side0sub : R₂.side 0 ⊆ (rectQuad ha hb).side 0 := by
    rw [hR2side0, hRabside0]
    apply image_mono
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨by linarith, hz2⟩, hz3⟩
  have hR2side2sub : R₂.side 2 ⊆ (rectQuad ha hb).side 2 := by
    rw [hR2side2, hRabside2]
    apply image_mono
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨by linarith, hz2⟩, hz3⟩
  -- transport to sides of P₁, P₂ inside the sides of the image rectangle a' b'
  have hP1side0sub : P₁.side 0 ⊆ (rectQuad ha' hb').side 0 := by
    rw [← hchain1 0, ← hchainWhole 0]
    exact image_mono (image_mono (image_mono hR1side0sub))
  have hP1side2sub : P₁.side 2 ⊆ (rectQuad ha' hb').side 2 := by
    rw [← hchain1 2, ← hchainWhole 2]
    exact image_mono (image_mono (image_mono hR1side2sub))
  have hP2side0sub : P₂.side 0 ⊆ (rectQuad ha' hb').side 0 := by
    rw [← hchain2 0, ← hchainWhole 0]
    exact image_mono (image_mono (image_mono hR2side0sub))
  have hP2side2sub : P₂.side 2 ⊆ (rectQuad ha' hb').side 2 := by
    rw [← hchain2 2, ← hchainWhole 2]
    exact image_mono (image_mono (image_mono hR2side2sub))
  -- apply Theorem 4.7 in the image rectangle
  have hRectab' : (rectQuad ha' hb').IsRectangle := by
    have hid : (fun z : ℂ => Complex.exp (((0 : ℝ) : ℂ) * I) * z + 0) = id := by
      funext z; simp
    refine ⟨a', b', 0, 0, ha', hb', ?_, ?_⟩
    · show rectangle a' b' = (fun z => Complex.exp (((0 : ℝ) : ℂ) * I) * z + 0) '' rectangle a' b'
      rw [hid, Set.image_id]
    · intro i
      show rectVert a' b' i =
        OnePoint.map (fun z => Complex.exp (((0 : ℝ) : ℂ) * I) * z + 0) (rectVert a' b' i)
      rw [hid]
      simp
  have hQab'mod : (rectQuad ha' hb').modulus = a' / b' := modulus_rectQuad ha' hb'
  have hsum' : P₁.modulus + P₂.modulus = (rectQuad ha' hb').modulus := hsum.trans hQab'mod.symm
  obtain ⟨hP1rect, -, -⟩ :=
    (thm4_7_subadditive_eq_iff hRectab' hP1sub hP2sub hP1P2disj
      hP1side0sub hP1side2sub hP2side0sub hP2side2sub).mp hsum'
  -- vertex chase: P₁.vert 0 = 0, P₁.vert 3 = b' i
  have hQ1vert0 : Q₁.vert 0 = Q.vert 0 := by
    rw [hQ1vert 0, (rfl : R₁.vert 0 = rectVert a b 0)]
    exact (hΦinvExt_vert 0).symm
  have hQ1vert3 : Q₁.vert 3 = Q.vert 3 := by
    rw [hQ1vert 3, (rfl : R₁.vert 3 = rectVert a b 3)]
    exact (hΦinvExt_vert 3).symm
  have hQ1'vert0 : Q₁'.vert 0 = Q'.vert 0 := by
    rw [hQ1'img.2 0, hQ1vert0]; exact (hQ'.2 0).symm
  have hQ1'vert3 : Q₁'.vert 3 = Q'.vert 3 := by
    rw [hQ1'img.2 3, hQ1vert3]; exact (hQ'.2 3).symm
  have hP1vert0 : P₁.vert 0 = ((0 : ℂ) : ExtPlane) := by
    rw [hP1vert 0, hQ1'vert0, hΨv 0]; rfl
  have hP1vert3 : P₁.vert 3 = (((b' : ℂ) * I : ℂ) : ExtPlane) := by
    rw [hP1vert 3, hQ1'vert3, hΨv 3]; rfl
  obtain ⟨a₁, b₁, θ, c, ha1, hb1, hP1dom2, hP1vert2⟩ := hP1rect
  have e0 : ((0 : ℂ) : ExtPlane) =
      ((Complex.exp ((θ : ℂ) * I) * (0 : ℂ) + c : ℂ) : ExtPlane) := by
    have h := hP1vert2 0
    rw [hP1vert0, (rfl : rectVert a₁ b₁ 0 = ((0 : ℂ) : ExtPlane))] at h
    exact h
  have hc : c = 0 := by
    have h : (0 : ℂ) = Complex.exp ((θ : ℂ) * I) * (0 : ℂ) + c := OnePoint.coe_injective e0
    simpa using h.symm
  have e3 : (((b' : ℂ) * I : ℂ) : ExtPlane) =
      ((Complex.exp ((θ : ℂ) * I) * ((b₁ : ℂ) * I) + c : ℂ) : ExtPlane) := by
    have h := hP1vert2 3
    rw [hP1vert3, (rfl : rectVert a₁ b₁ 3 = (((b₁ : ℂ) * I : ℂ) : ExtPlane))] at h
    exact h
  have hexpb : Complex.exp ((θ : ℂ) * I) * (b₁ : ℂ) = (b' : ℂ) := by
    have h : (b' : ℂ) * I = Complex.exp ((θ : ℂ) * I) * ((b₁ : ℂ) * I) + c :=
      OnePoint.coe_injective e3
    rw [hc, add_zero] at h
    have hI : Complex.exp ((θ : ℂ) * I) * (b₁ : ℂ) * I = (b' : ℂ) * I := by
      linear_combination -h
    exact mul_right_cancel₀ Complex.I_ne_zero hI
  have hb1' : b₁ = b' := by
    have hnorm : ‖Complex.exp ((θ : ℂ) * I) * (b₁ : ℂ)‖ = ‖(b' : ℂ)‖ := by rw [hexpb]
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hb1.le, Real.norm_of_nonneg hb'.le] at hnorm
    exact hnorm
  have hexp1 : Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [hb1'] at hexpb
    have hb'ne : (b' : ℂ) ≠ 0 := by
      exact_mod_cast hb'.ne'
    exact mul_right_cancel₀ hb'ne (hexpb.trans (one_mul _).symm)
  have hP1domEq : P₁.dom = rectangle a₁ b' := by
    rw [hP1dom2, hc, hexp1, hb1']
    simp
  have hidz : (fun z : ℂ => (1 : ℂ) * z + 0) = id := by funext z; show (1:ℂ) * z + 0 = z; ring
  have hP1modEq : P₁.modulus = a₁ / b' := by
    rw [show P₁ = rectQuad ha1 hb' from
      TopQuad.ext_of_dom_vert hP1domEq (by
        funext i
        rw [hP1vert2 i, hc, hexp1, hb1', hidz]
        show OnePoint.map id (rectVert a₁ b' i) = (rectQuad ha1 hb').vert i
        have hmid : OnePoint.map (id : ℂ → ℂ) (rectVert a₁ b' i) = rectVert a₁ b' i := by simp
        rw [hmid]
        rfl)]
    exact modulus_rectQuad ha1 hb'
  have ha1eq : a₁ = b' / b * s := by
    have heq : a₁ / b' = s / b := hP1modEq.symm.trans hP1mod
    have hb'ne : (b' : ℝ) ≠ 0 := hb'.ne'
    have hbne : (b : ℝ) ≠ 0 := hb.ne'
    field_simp at heq
    field_simp
    linarith [heq]
  show ψ '' (f '' (Φinv '' rectangle s b)) = rectangle (b' / b * s) b'
  rw [show rectangle s b = R₁.dom from hR1dom.symm, show Φinv '' R₁.dom = Q₁.dom from hQ1dom.symm,
    show f '' Q₁.dom = Q₁'.dom from hQ1'img.1.symm, show ψ '' Q₁'.dom = P₁.dom from hP1dom.symm,
    hP1domEq, ha1eq]


/-! ### Theorem 7.3, piece E -/


theorem oqc_conjugate_horizontal {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) {Q Q' : TopQuad}
    (hQD : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f)
    {a b a' b' : ℝ} {φ ψ : ℂ → ℂ} (hφ : Q.IsStdConformalMap a b φ)
    (hψ : Q'.IsStdConformalMap a' b' ψ) {t : ℝ} (ht : 0 < t) (htb : t < b) :
    ψ '' (f '' (Function.invFunOn φ Q.dom '' rectangle a t)) = rectangle a' (a' / a * t) := by
  obtain ⟨ha, hb, hφc, Φ, hΦ, hΦv⟩ := hφ
  obtain ⟨ha', hb', hψc, Ψ, hΨ, hΨv⟩ := hψ
  set ρ : ℂ → ℂ := fun w => -I * w + (a : ℂ) * I with hρ_def
  set ρ' : ℂ → ℂ := fun w => -I * w + (a' : ℂ) * I with hρ'_def
  set σ' : ℂ → ℂ := fun w => I * w + (a' : ℂ) with hσ'_def
  have hσ'ρ' : ∀ w, σ' (ρ' w) = w := fun w => by
    simp only [hσ'_def, hρ'_def]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hQrot : Q.rotate.IsStdConformalMap b a (ρ ∘ φ) :=
    ⟨hb, ha, rectangle_rotation_conformal.comp hφc,
      (mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a)) ∘ Φ,
      hΦ.comp_homeomorph hφc.mapsTo _
        (fun w _ => by rw [mobiusHomeomorph_apply, rotation_mobiusExt_coe])
        rectangle_rotation_image,
      fun i => by
        show mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a) (Φ (Q.vert (i + 1))) =
          rectVert b a i
        rw [hΦv (i + 1), mobiusHomeomorph_apply, rectVert_rotation]⟩
  have hQ'rot : Q'.rotate.IsStdConformalMap b' a' (ρ' ∘ ψ) :=
    ⟨hb', ha', rectangle_rotation_conformal.comp hψc,
      (mobiusHomeomorph (-I) ((a' : ℂ) * I) 0 1 (rotation_det a')) ∘ Ψ,
      hΨ.comp_homeomorph hψc.mapsTo _
        (fun w _ => by rw [mobiusHomeomorph_apply, rotation_mobiusExt_coe])
        rectangle_rotation_image,
      fun i => by
        show mobiusHomeomorph (-I) ((a' : ℂ) * I) 0 1 (rotation_det a') (Ψ (Q'.vert (i + 1))) =
          rectVert b' a' i
        rw [hΨv (i + 1), mobiusHomeomorph_apply, rectVert_rotation]⟩
  have hQ'rotIU : Q.rotate.IsImageUnder Q'.rotate f := ⟨hQ'.1, fun i => hQ'.2 (i + 1)⟩
  have hQDrot : closure (toExt Q.rotate.dom) ⊆ toExt D := hQD
  have hD := oqc_conjugate_vertical hf hQDrot hQ'rotIU hQrot hQ'rot ht htb
  -- hD : (ρ' ∘ ψ) '' (f '' (invFunOn (ρ ∘ φ) Q.rotate.dom '' rectangle t a)) = rectangle (a'/a*t) a'
  have hpullback : ∀ (g : ℂ → ℂ) (c d : ℝ), IsConformalOnto g Q.dom (rectangle c d) →
      ∀ {T : Set ℂ}, T ⊆ rectangle c d →
        Function.invFunOn g Q.dom '' T = {z ∈ Q.dom | g z ∈ T} := by
    intro g c d hgc T hT
    ext z
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwdom : w ∈ g '' Q.dom := by rw [hgc.2.2]; exact hT hw
      refine ⟨Function.invFunOn_mem hwdom, ?_⟩
      rw [Function.invFunOn_eq hwdom]
      exact hw
    · rintro ⟨hz, hgz⟩
      exact ⟨g z, hgz, hgc.2.1.leftInvOn_invFunOn hz⟩
  have htsub : rectangle a t ⊆ rectangle a b := by
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4.trans htb⟩
  have htasub : rectangle t a ⊆ rectangle b a := by
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2.trans_le htb.le, h3, h4⟩
  have h1 := hpullback φ a b hφc htsub
  have h2 := hpullback (ρ ∘ φ) b a (rectangle_rotation_conformal.comp hφc) htasub
  have hiff : ∀ z ∈ Q.dom, ((ρ ∘ φ) z ∈ rectangle t a ↔ φ z ∈ rectangle a t) := by
    intro z hz
    have hφzab : φ z ∈ rectangle a b := by rw [← hφc.2.2]; exact mem_image_of_mem φ hz
    constructor
    · intro h
      rw [Function.comp_apply, ← (rectangle_rotation_conformal (a := a) (b := t)).2.2] at h
      obtain ⟨y, hy, hyeq⟩ := h
      have hyab : y ∈ rectangle a b := htsub hy
      rwa [(rectangle_rotation_conformal (a := a) (b := b)).2.1 hyab hφzab hyeq] at hy
    · intro h
      rw [Function.comp_apply, ← (rectangle_rotation_conformal (a := a) (b := t)).2.2]
      exact mem_image_of_mem ρ h
  have hdomeq : Function.invFunOn (ρ ∘ φ) Q.dom '' rectangle t a =
      Function.invFunOn φ Q.dom '' rectangle a t := by
    rw [h1, h2]
    ext z
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hz, hgz⟩
      exact ⟨hz, (hiff z hz).1 hgz⟩
    · rintro ⟨hz, hgz⟩
      exact ⟨hz, (hiff z hz).2 hgz⟩
  rw [show Q.rotate.dom = Q.dom from rfl, hdomeq, Set.image_comp] at hD
  have hσ'target : σ' '' rectangle (a' / a * t) a' = rectangle a' (a' / a * t) := by
    rw [← (rectangle_rotation_conformal (a := a') (b := a' / a * t)).2.2, ← Set.image_comp]
    have : σ' ∘ ρ' = id := funext hσ'ρ'
    rw [this, Set.image_id]
  have hcast : σ' '' (ρ' '' (ψ '' (f '' (Function.invFunOn φ Q.dom '' rectangle a t)))) =
      σ' '' rectangle (a' / a * t) a' := by rw [hD]
  rw [← Set.image_comp] at hcast
  have hid : σ' ∘ ρ' = id := funext hσ'ρ'
  rw [hid, Set.image_id, hσ'target] at hcast
  exact hcast


/-! ### Theorem 7.3, piece F -/


/-- A one-sided real squeeze: if `L < c*s` for every `s` strictly between `x` and `a`, and
`c*s ≤ L` for every `s` strictly between `0` and `x`, then `L = c*x`. Pure real-variable
epsilon bookkeeping, no topology. -/
theorem oqc_eq_of_bounds {L c x a : ℝ} (hc : 0 < c) (hx0 : 0 < x) (hxa : x < a)
    (hupper : ∀ s, x < s → s < a → L < c * s)
    (hlower : ∀ s, 0 < s → s < x → c * s ≤ L) :
    L = c * x := by
  have h1 : L ≤ c * x := by
    by_contra hL
    push Not at hL
    have hLcx : 0 < L - c * x := by linarith
    set m := min ((L - c * x) / c) (a - x) with hmdef
    have hm0 : 0 < m := lt_min (by positivity) (by linarith)
    set ε := m / 2 with hεdef
    have hε0 : 0 < ε := by positivity
    have hεltm : ε < m := by rw [hεdef]; linarith
    have hεlt1 : ε < (L - c * x) / c := hεltm.trans_le (min_le_left _ _)
    have hεlt2 : ε < a - x := hεltm.trans_le (min_le_right _ _)
    have hce : ε * c < L - c * x := (lt_div_iff₀ hc).mp hεlt1
    have := hupper (x + ε) (by linarith) (by linarith)
    nlinarith
  have h2 : c * x ≤ L := by
    by_contra hL
    push Not at hL
    have hLcx : 0 < c * x - L := by linarith
    set m := min ((c * x - L) / c) x with hmdef
    have hm0 : 0 < m := lt_min (by positivity) hx0
    set ε := m / 2 with hεdef
    have hε0 : 0 < ε := by positivity
    have hεltm : ε < m := by rw [hεdef]; linarith
    have hεlt1 : ε < (c * x - L) / c := hεltm.trans_le (min_le_left _ _)
    have hεlt2 : ε < x := hεltm.trans_le (min_le_right _ _)
    have hce : ε * c < c * x - L := (lt_div_iff₀ hc).mp hεlt1
    have := hlower (x - ε) (by linarith) (by linarith)
    nlinarith
  linarith

/-- **F (owner -0f, after D, E).** The conjugated map is the similarity `w ↦ (b'/b) w`: squeeze the real part
with D for `s ≷ Re w` (using injectivity of `g` on the rectangle for the lower bound) and the imaginary part
with E, and `a'/a = b'/b` from `a/b = a'/b'`. -/
theorem oqc_conjugate_eq_smul {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) {Q Q' : TopQuad}
    (hQD : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f)
    {a b a' b' : ℝ} {φ ψ : ℂ → ℂ} (hφ : Q.IsStdConformalMap a b φ)
    (hψ : Q'.IsStdConformalMap a' b' ψ) :
    ∀ z ∈ Q.dom, ψ (f z) = ((b' / b : ℝ) : ℂ) * φ z := by
  have ha0 : 0 < a := hφ.1
  have hb0 : 0 < b := hφ.2.1
  have ha'0 : 0 < a' := hψ.1
  have hb'0 : 0 < b' := hψ.2.1
  have hQdomD : Q.dom ⊆ D := fun z hz =>
    coe_mem_toExt_iff.mp (hQD (subset_closure (mem_image_of_mem _ hz)))
  have hfInj : InjOn f Q.dom := hf.2.2.1.2.1.mono hQdomD
  have hψInj : InjOn ψ Q'.dom := hψ.2.2.1.2.1
  have hmapsto : MapsTo f Q.dom Q'.dom := fun z hz => hQ'.1 ▸ mem_image_of_mem f hz
  have hcompInj : InjOn (fun z => ψ (f z)) Q.dom := hψInj.comp hfInj hmapsto
  -- `a/b = a'/b'`, hence `a'/a = b'/b`
  have hab_eq : a / b = a' / b' := by
    obtain ⟨Q'', hQ''img, hmodeq⟩ := oqc_exists_image_modulus_eq hf hQD
    have hQeq : Q'' = Q' := hQ''img.unique hQ'
    rw [hQeq, modulus_eq_of_equivRect Q ⟨φ, hφ⟩, modulus_eq_of_equivRect Q' ⟨ψ, hψ⟩] at hmodeq
    exact hmodeq.symm
  have hmul_eq : a * b' = a' * b := (div_eq_div_iff hb0.ne' hb'0.ne').mp hab_eq
  have ha'a_eq : a' / a = b' / b := by
    rw [div_eq_div_iff ha0.ne' hb0.ne']
    linear_combination -hmul_eq
  intro z hz
  set w := φ z with hwdef
  have hwab : w ∈ rectangle a b := hφ.2.2.1.2.2 ▸ mem_image_of_mem φ hz
  have hgw : ψ (f z) ∈ rectangle a' b' := hψ.2.2.1.2.2 ▸ mem_image_of_mem ψ (hmapsto hz)
  -- real part
  have hupperRe : ∀ s, w.re < s → s < a → (ψ (f z)).re < b' / b * s := by
    intro s hs1 hs2
    have hzmem : z ∈ Function.invFunOn φ Q.dom '' rectangle s b :=
      ⟨w, ⟨hwab.1, hs1, hwab.2.2.1, hwab.2.2.2⟩, hφ.2.2.1.2.1.leftInvOn_invFunOn hz⟩
    have hmem : ψ (f z) ∈ rectangle (b' / b * s) b' := by
      rw [← oqc_conjugate_vertical hf hQD hQ' hφ hψ (by linarith [hwab.1]) hs2]
      exact mem_image_of_mem ψ (mem_image_of_mem f hzmem)
    exact hmem.2.1
  have hlowerRe : ∀ s, 0 < s → s < w.re → b' / b * s ≤ (ψ (f z)).re := by
    intro s hs0 hsx
    have hsa : s < a := by linarith [hwab.2.1]
    have hzmem : z ∉ Function.invFunOn φ Q.dom '' rectangle s b := by
      rintro ⟨w', hw'mem, hw'eq⟩
      have hw'ab : w' ∈ rectangle a b :=
        ⟨hw'mem.1, by linarith [hw'mem.2.1], hw'mem.2.2.1, hw'mem.2.2.2⟩
      have hw'φ : w' ∈ φ '' Q.dom := hφ.2.2.1.2.2 ▸ hw'ab
      have heq : w = w' := by rw [hwdef, ← hw'eq]; exact Function.invFunOn_eq hw'φ
      rw [heq] at hsx
      linarith [hw'mem.2.1]
    have hnotmem : ψ (f z) ∉ rectangle (b' / b * s) b' := by
      rw [← oqc_conjugate_vertical hf hQD hQ' hφ hψ hs0 hsa]
      rintro ⟨_, ⟨z₁, hz₁mem, rfl⟩, heq⟩
      apply hzmem
      have hz₁Q : z₁ ∈ Q.dom := by
        obtain ⟨w', hw'mem, hw'eq⟩ := hz₁mem
        have hw'ab : w' ∈ rectangle a b :=
          ⟨hw'mem.1, by linarith [hw'mem.2.1], hw'mem.2.2.1, hw'mem.2.2.2⟩
        have hw'φ : w' ∈ φ '' Q.dom := hφ.2.2.1.2.2 ▸ hw'ab
        rw [← hw'eq]
        exact Function.invFunOn_mem hw'φ
      have hz₁z : z₁ = z := hcompInj hz₁Q hz heq
      exact hz₁z ▸ hz₁mem
    by_contra hcon
    push Not at hcon
    exact hnotmem ⟨hgw.1, hcon, hgw.2.2.1, hgw.2.2.2⟩
  have hRe : (ψ (f z)).re = b' / b * w.re :=
    oqc_eq_of_bounds (div_pos hb'0 hb0) hwab.1 hwab.2.1 hupperRe hlowerRe
  -- imaginary part, by the same argument using E and `a'/a`
  have hupperIm : ∀ t, w.im < t → t < b → (ψ (f z)).im < a' / a * t := by
    intro t ht1 ht2
    have hzmem : z ∈ Function.invFunOn φ Q.dom '' rectangle a t :=
      ⟨w, ⟨hwab.1, hwab.2.1, hwab.2.2.1, ht1⟩, hφ.2.2.1.2.1.leftInvOn_invFunOn hz⟩
    have hmem : ψ (f z) ∈ rectangle a' (a' / a * t) := by
      rw [← oqc_conjugate_horizontal hf hQD hQ' hφ hψ (by linarith [hwab.2.2.1]) ht2]
      exact mem_image_of_mem ψ (mem_image_of_mem f hzmem)
    exact hmem.2.2.2
  have hlowerIm : ∀ t, 0 < t → t < w.im → a' / a * t ≤ (ψ (f z)).im := by
    intro t ht0 htx
    have htb : t < b := by linarith [hwab.2.2.2]
    have hzmem : z ∉ Function.invFunOn φ Q.dom '' rectangle a t := by
      rintro ⟨w', hw'mem, hw'eq⟩
      have hw'ab : w' ∈ rectangle a b :=
        ⟨hw'mem.1, hw'mem.2.1, hw'mem.2.2.1, by linarith [hw'mem.2.2.2]⟩
      have hw'φ : w' ∈ φ '' Q.dom := hφ.2.2.1.2.2 ▸ hw'ab
      have heq : w = w' := by rw [hwdef, ← hw'eq]; exact Function.invFunOn_eq hw'φ
      rw [heq] at htx
      linarith [hw'mem.2.2.2]
    have hnotmem : ψ (f z) ∉ rectangle a' (a' / a * t) := by
      rw [← oqc_conjugate_horizontal hf hQD hQ' hφ hψ ht0 htb]
      rintro ⟨_, ⟨z₁, hz₁mem, rfl⟩, heq⟩
      apply hzmem
      have hz₁Q : z₁ ∈ Q.dom := by
        obtain ⟨w', hw'mem, hw'eq⟩ := hz₁mem
        have hw'ab : w' ∈ rectangle a b :=
          ⟨hw'mem.1, hw'mem.2.1, hw'mem.2.2.1, by linarith [hw'mem.2.2.2]⟩
        have hw'φ : w' ∈ φ '' Q.dom := hφ.2.2.1.2.2 ▸ hw'ab
        rw [← hw'eq]
        exact Function.invFunOn_mem hw'φ
      have hz₁z : z₁ = z := hcompInj hz₁Q hz heq
      exact hz₁z ▸ hz₁mem
    by_contra hcon
    push Not at hcon
    exact hnotmem ⟨hgw.1, hgw.2.1, hgw.2.2.1, hcon⟩
  have hIm : (ψ (f z)).im = a' / a * w.im :=
    oqc_eq_of_bounds (div_pos ha'0 ha0) hwab.2.2.1 hwab.2.2.2 hupperIm hlowerIm
  rw [ha'a_eq] at hIm
  apply Complex.ext
  · show (ψ (f z)).re = (((b' / b : ℝ) : ℂ) * w).re
    rw [hRe]
    simp [Complex.mul_re]
  · show (ψ (f z)).im = (((b' / b : ℝ) : ℂ) * w).im
    rw [hIm]
    simp [Complex.mul_im]



/-- On a quadrilateral `Q̄ ⊆ D`, a `1`-q.c. map factors as `ψ⁻¹ ∘ ((b'/b)·) ∘ φ` through the standard conformal
maps, hence is holomorphic there. -/
theorem oqc_differentiableOn_of_isKQC_one {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) {Q : TopQuad}
    (hQD : closure (toExt Q.dom) ⊆ toExt D) : DifferentiableOn ℂ f Q.dom := by
  obtain ⟨Q', hQ', -⟩ := oqc_exists_image_modulus_eq hf hQD
  obtain ⟨a, b, φ, hφ⟩ := thm1_1_exists_rectangle Q
  obtain ⟨a', b', ψ, hψ⟩ := thm1_1_exists_rectangle Q'
  have hsmul := oqc_conjugate_eq_smul hf hQD hQ' hφ hψ
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hφc : IsConformalOnto φ Q.dom (rectangle a b) := hφ.2.2.1
  have hψc : IsConformalOnto ψ Q'.dom (rectangle a' b') := hψ.2.2.1
  have hψinv : IsConformalOnto (Function.invFunOn ψ Q'.dom) (rectangle a' b') Q'.dom :=
    hψc.symm hQ'o
  -- `f = ψ⁻¹ ∘ (c • φ)` on `Q.dom`
  have hfeq : ∀ z ∈ Q.dom, f z = Function.invFunOn ψ Q'.dom (((b' / b : ℝ) : ℂ) * φ z) := by
    intro z hz
    rw [← hsmul z hz]
    have hfz : f z ∈ Q'.dom := by
      rw [hQ'.1]; exact mem_image_of_mem f hz
    exact (hψc.2.1.leftInvOn_invFunOn hfz).symm
  have hmaps : ∀ z ∈ Q.dom, ((b' / b : ℝ) : ℂ) * φ z ∈ rectangle a' b' := by
    intro z hz
    have hfz : f z ∈ Q'.dom := by
      rw [hQ'.1]; exact mem_image_of_mem f hz
    rw [← hsmul z hz, ← hψc.2.2]
    exact mem_image_of_mem ψ hfz
  exact (hψinv.1.comp ((differentiableOn_const _).mul hφc.1) hmaps).congr hfeq

/-- **Theorem 7.3** (保模映射): a `1`-quasiconformal map is conformal.

Proved (2026-09-21) from the `oqc_` pieces above: the conjugated map `ψ ∘ f ∘ φ⁻¹` between the standard
rectangles of a quadrilateral `Q̄ ⊆ D` and of its image is the similarity `w ↦ (b'/b) w`
(`oqc_conjugate_eq_smul`), so `f = ψ⁻¹ ∘ ((b'/b)·) ∘ φ` is holomorphic on `Q`; every point of `D` lies in
such a `Q`. -/
theorem thm7_3_one_qc_conformal {f : ℂ → ℂ} {D : Set ℂ} (hf : IsKQC f D 1) :
    IsConformalOnto f D (f '' D) := by
  refine ⟨?_, hf.2.2.1.2.1, rfl⟩
  intro z hz
  obtain ⟨Q, hzQ, hQD⟩ := exists_topQuad_mem_closure_subset hf.1 hz
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  exact ((oqc_differentiableOn_of_isKQC_one hf hQD).differentiableAt
    (hQo.mem_nhds hzQ)).differentiableWithinAt


/-- `B̄ ⊆ D` (in `ℂ̄`) gives `B ⊆ D`. -/
theorem subset_of_closure_toExt_subset {B D : Set ℂ} (hBD : closure (toExt B) ⊆ toExt D) :
    B ⊆ D := fun z hz => by
  obtain ⟨w, hw, hwz⟩ := hBD (subset_closure (mem_image_of_mem _ hz))
  rw [← OnePoint.coe_injective hwz]
  exact hw

/-- **Theorem 7.4, one direction**: `M(f(B)) ≤ K M(B)` for a `K`-q.c. `f` on `D ⊇ B̄` and a doubly
connected `B` whose image is doubly connected.  Degenerate case (`M(B) = ∞`): trivial.  Otherwise
`B` and `f(B)` are conformally equivalent to `{1<|z|<R}`, `{1<|w|<R'}` (Theorem 2.1, rescaled);
the conjugated map `ψ ∘ f ∘ φ⁻¹` is `K`-q.c. between the annuli (Theorem 7.1), and
`aqc_log_le_of_quad_bound` gives `ln R' ≤ K ln R`. -/
theorem dcModulus_image_le_of_isKQC {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {B : Set ℂ} (hB : IsDoublyConnected B) (hBD : closure (toExt B) ⊆ toExt D)
    (hB' : IsDoublyConnected (f '' B)) :
    dcModulus (f '' B) ≤ ENNReal.ofReal K * dcModulus B := by
  obtain ⟨hD, hK1, hhom, -⟩ := id hf
  have hK0 : 0 ≤ K := by linarith
  have hKpos : ENNReal.ofReal K ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hBsub : B ⊆ D := subset_of_closure_toExt_subset hBD
  have hfo : IsOpen (f '' D) := isOpen_image_of_isKQC hf
  by_cases hdeg : ∃ x ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ x = {x}
  · rw [(aqc_dcModulus_eq_top_iff hB).2 hdeg, ENNReal.mul_top hKpos]
    exact le_top
  push Not at hdeg
  -- the image is non-degenerate too (transport a one-point component back by `f⁻¹`)
  have hinvD : Function.invFunOn f D '' (f '' D) = D := hhom.2.1.leftInvOn_invFunOn.image_image
  have hinvB : Function.invFunOn f D '' (f '' B) = B :=
    (hhom.2.1.leftInvOn_invFunOn.mono hBsub).image_image
  have hB'D : closure (toExt (f '' B)) ⊆ toExt (f '' D) :=
    closure_toExt_image_subset hhom.1 hBD subset_rfl
  have hdeg' : ∀ y ∈ (toExt (f '' B))ᶜ, connectedComponentIn (toExt (f '' B))ᶜ y ≠ {y} := by
    intro y hy hypt
    have hinv : IsHomeomorphOnto (Function.invFunOn f D) (f '' D)
        (Function.invFunOn f D '' (f '' D)) := by
      rw [hinvD]; exact isHomeomorphOnto_invFunOn hhom
    have hinvo : IsOpen (Function.invFunOn f D '' (f '' D)) := by rw [hinvD]; exact hD
    obtain ⟨x, hx, hxpt⟩ :=
      aqc_exists_singleton_component_image hfo hinv hinvo hB' hB'D hy hypt
    rw [hinvB] at hx hxpt
    exact hdeg x hx hxpt
  -- canonical annuli, rescaled to inner radius `1`
  obtain ⟨r₁, r₂, h₁, h₂, hBeq⟩ := thm2_1_canonical_form_annulus hB hdeg
  obtain ⟨s₁, s₂, hs₁, hs₂, hB'eq⟩ := thm2_1_canonical_form_annulus hB' hdeg'
  set R : ℝ := r₂ / r₁ with hRdef
  set R' : ℝ := s₂ / s₁ with hR'def
  have hR : 1 < R := by rw [hRdef, lt_div_iff₀ h₁, one_mul]; exact h₂
  have hR' : 1 < R' := by rw [hR'def, lt_div_iff₀ hs₁, one_mul]; exact hs₂
  have hBA : ConformallyEquivalent B (annulus 1 R) :=
    hBeq.trans ((annulus_conformallyEquivalent_iff h₁ h₂ one_pos hR).2 (by rw [hRdef, div_one]))
  have hB'A' : ConformallyEquivalent (f '' B) (annulus 1 R') :=
    hB'eq.trans ((annulus_conformallyEquivalent_iff hs₁ hs₂ one_pos hR').2
      (by rw [hR'def, div_one]))
  have hMB : dcModulus B = ENNReal.ofReal (Real.log R) := by
    rw [dcModulus_eq_of_equiv hB.1 one_pos hR hBA, div_one]
  have hMB' : dcModulus (f '' B) = ENNReal.ofReal (Real.log R') := by
    rw [dcModulus_eq_of_equiv hB'.1 one_pos hR' hB'A', div_one]
  -- the conjugated map `g = ψ ∘ f ∘ φ⁻¹` between the annuli
  obtain ⟨φ, hφ⟩ := hBA
  obtain ⟨ψ, hψ⟩ := hB'A'
  have hφinv : IsConformalOnto (Function.invFunOn φ B) (annulus 1 R) B := hφ.symm hB.1
  have h1 : IsKQC (Function.invFunOn φ B) (annulus 1 R) 1 :=
    isKQC_one_of_conformal (isOpen_annulus 1 R) hφinv
  have h2 : IsKQC (f ∘ Function.invFunOn φ B) (annulus 1 R) (1 * K) :=
    thm7_1_comp h1 hf (by rw [hφinv.2.2]; exact hBsub)
  have h3 : IsKQC ψ (f '' B) 1 := isKQC_one_of_conformal hB'.1 hψ
  have himg2 : (f ∘ Function.invFunOn φ B) '' annulus 1 R = f '' B := by
    rw [image_comp, hφinv.2.2]
  have h4 : IsKQC (ψ ∘ (f ∘ Function.invFunOn φ B)) (annulus 1 R) (1 * K * 1) :=
    thm7_1_comp h2 h3 (by rw [himg2])
  obtain ⟨-, -, hg, hmod⟩ := h4
  have himg4 : (ψ ∘ (f ∘ Function.invFunOn φ B)) '' annulus 1 R = annulus 1 R' := by
    rw [image_comp, himg2, hψ.2.2]
  rw [himg4] at hg
  have hlog : Real.log R' ≤ K * Real.log R := by
    refine aqc_log_le_of_quad_bound hR hR' hK0 hg fun Q hQ => ?_
    obtain ⟨Q', hQ', hle⟩ := hmod Q hQ
    exact ⟨Q', hQ', by simpa using hle⟩
  rw [hMB, hMB', ← ENNReal.ofReal_mul hK0]
  exact ENNReal.ofReal_le_ofReal hlog

/-- **Theorem 7.4**: if `f` is `K`-q.c. on `D` and `B` is a doubly connected domain with
`B̄ ⊆ D`, then `f(B)` is doubly connected and `M(B)/K ≤ M(f(B)) ≤ K M(B)`.

Proved (2026-09-21) from `LiZhongQC.Lemmas.AnnulusQC`: the image is doubly connected
(`aqc_isDoublyConnected_image`); the inequality `M(f(B)) ≤ K M(B)` is `dcModulus_image_le_of_isKQC`
(canonical annuli by Theorem 2.1, the conjugated map is `K`-q.c. by Theorem 7.1, and
`aqc_log_le_of_quad_bound` gives `ln R' ≤ K ln R` without cutting the image domain); the other inequality
follows by applying it to `f⁻¹` (Theorem 7.2). -/
theorem thm7_4_dcModulus_quasi_invariance {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    {B : Set ℂ} (hB : IsDoublyConnected B) (hBD : closure (toExt B) ⊆ toExt D) :
    IsDoublyConnected (f '' B) ∧ dcModulus B ≤ ENNReal.ofReal K * dcModulus (f '' B) ∧
      dcModulus (f '' B) ≤ ENNReal.ofReal K * dcModulus B := by
  have hD : IsOpen D := hf.1
  have hhom : IsHomeomorphOnto f D (f '' D) := hf.2.2.1
  have hfo : IsOpen (f '' D) := isOpen_image_of_isKQC hf
  have hB' : IsDoublyConnected (f '' B) := aqc_isDoublyConnected_image hD hhom hfo hB hBD
  refine ⟨hB', ?_, dcModulus_image_le_of_isKQC hf hB hBD hB'⟩
  -- the other direction: apply the first to `f⁻¹` on `f(D)` and `f(B)`
  have hBsub : B ⊆ D := subset_of_closure_toExt_subset hBD
  have hinvB : Function.invFunOn f D '' (f '' B) = B :=
    (hhom.2.1.leftInvOn_invFunOn.mono hBsub).image_image
  have hB'D : closure (toExt (f '' B)) ⊆ toExt (f '' D) :=
    closure_toExt_image_subset hhom.1 hBD subset_rfl
  have h := dcModulus_image_le_of_isKQC (thm7_2_inv hf) hB' hB'D (by rw [hinvB]; exact hB)
  rwa [hinvB] at h

end LiZhongQC
