import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.SchottkyTerminal
import LiZhongQC.Lemmas.QDDimension
import LiZhongQC.Lemmas.S32wSymmetricExtension
import LiZhongQC.Lemmas.S32wFoldPush
import LiZhongQC.Lemmas.S32wHalvesSelfmap
import LiZhongQC.Lemmas.S32wPunctRestrict
import LiZhongQC.Lemmas.S32wSymmExtPunctured
import LiZhongQC.Lemmas.Thm321
import LiZhongQC.Lemmas.TeichmullerTransport
import LiZhongQC.Lemmas.S32wDTTeich
import LiZhongQC.Lemmas.TeichmullerCommutesReflection
import LiZhongQC.Lemmas.SchottkyDirectFinal

/-!
# §32.2 Theorem 32.4 (method of Ahlfors): book helper `s32w_thm32_4`

`s32w_thm32_4` is `thm32_4_existence_gnm` (S32:630) under a helper name.
* `m = 0`: it is Theorem 32.2 (`s82dx_thm32_2_existence_gn`, 下属3's helper).
* `m ≠ 0`, by doubling:
  1. the symmetric extension `f^d` (`s32w_symmetric_extension`) and its restriction to the punctured doubles;
  2. a Teichmüller or conformal map `f₁ ≃ f^d` there (`s82dx_thm32_2_existence_gn` on the type `(2g + m - 1, 2n, 0)`);
  3. `f₁` commutes with the reflections and maps the half to the half: `s82rc_eq32_3_teichmuller_commutes_reflection`
     (下属2's helper) in the Teichmüller case, `s32w_t324_biholo_commutes` in the conformal case;
  4. its restriction `f₀` to `S₀` is homotopic to `f` (`s32w_descend_homotopy`, W2(a));
  5. it carries the restricted Teichmüller data or is conformal.

The two consumed helpers are imported (`SchottkyDirectFinal`, 下属3; `TeichmullerCommutesReflection`, 下属2; book
statements renamed, the eq32_3 helper with `(hf : IsQCRS f)`). Helpers carry the prefix `s32w_t324_`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **[stub T4a1]** The punctured double carries the finite-type structure of type `(2g + m - 1, 2n, 0)`: the closed
double with the `2n` punctures `Pd` and no holes. -/
theorem s32w_t324_punctured_structure {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) :
    Nonempty (FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) := by
  classical
  refine ⟨{
      X := Xd
      P := Pd
      D := fun i => Fin.elim0 i
      ι := Subtype.val
      genus := hd.genus
      card_P := hd.card_Pd
      disc := fun i => Fin.elim0 i
      disjoint := fun i => Fin.elim0 i
      disjoint_P := fun i => Fin.elim0 i
      embedding := (puncturedOpens Pd).2.isOpenEmbedding_subtypeVal
      holomorphic := (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
      range_ι := ?_ }⟩
  rw [Subtype.range_coe_subtype]
  ext x
  simp [puncturedOpens]

/-- **[stub T4a2]** The double of a non-exceptional type with `m ≠ 0` is non-exceptional: the types doubling to
`(0,0), (0,1), (1,0), (0,2)` are exactly `(0,0,1), (0,0,2), (0,1,1)`. -/
theorem s32w_t324_double_nonexc {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) :
    ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := by
  intro h
  apply hex
  unfold IsExceptionalType at h ⊢
  rcases h with h | h | h | h | h | h | h <;>
  · have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun p => p.2.1) h
    have h3 := congrArg (fun p => p.2.2) h
    dsimp only at h1 h2 h3
    have key : (g = 0 ∧ n = 0 ∧ m = 1) ∨ (g = 0 ∧ n = 0 ∧ m = 2) ∨ (g = 0 ∧ n = 1 ∧ m = 1) := by omega
    rcases key with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

/-- **[stub T4b1]** A non-exceptional type `(g, n, 0)` other than `(0, 3)` has a nonzero admissible differential
(`s82td_finrank_interior`: the dimension `6g - 6 + 2n` is positive). -/
theorem s32w_t324_exists_q {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (h03 : (g, n) ≠ (0, 3))
    (F : FiniteTypeStructure S g n 0) : ∃ q ∈ admissibleQDInterior F, q ≠ 0 := by
  have hdim := s82td_finrank_interior hex F
  have hE : ∀ a b : ℕ, IsExceptionalType a b 0 → ¬ (g = a ∧ n = b) := by
    rintro a b hab ⟨rfl, rfl⟩
    exact hex hab
  have e1 := hE 0 0 (by unfold IsExceptionalType; decide)
  have e2 := hE 0 1 (by unfold IsExceptionalType; decide)
  have e3 := hE 1 0 (by unfold IsExceptionalType; decide)
  have e4 := hE 0 2 (by unfold IsExceptionalType; decide)
  have e5 : ¬ (g = 0 ∧ n = 3) := by
    rintro ⟨rfl, rfl⟩
    exact h03 rfl
  have hpos : 0 < Module.finrank ℝ (admissibleQDInterior F) := by
    have : (0 : ℤ) < (Module.finrank ℝ (admissibleQDInterior F) : ℤ) := by rw [hdim]; omega
    exact_mod_cast this
  haveI : Module.Finite ℝ (admissibleQDInterior F) := Module.finite_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩

/-- The identity is a Teichmüller map with `k = 0` for any nonzero holomorphic quadratic differential: at a regular
point a natural parameter exists by (25.2) and the local expression of the identity is the identity. -/
theorem s32w_t324_refl_teich {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {q : Y → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) : IsTeichmullerMap (Homeomorph.refl Y) q q 0 := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : Y, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  refine ⟨isQCRS_refl, hq, hne, hq, le_rfl, zero_lt_one, fun p hp => ⟨hp, ?_⟩, fun p n hpn => hpn⟩
  have hz₀ : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have han : AnalyticAt ℂ (q p) (chartAt ℂ p p) :=
    (hq'.2 p).analyticAt ((chartAt ℂ p).open_target.mem_nhds hz₀)
  obtain ⟨ζ, h1, h2, h3, h4⟩ := eq25_2_natural_parameter han hp
  refine ⟨ζ, ζ, ⟨h1, h2, h3, h4⟩, ⟨h1, h2, h3, h4⟩, ?_⟩
  filter_upwards [(chartAt ℂ p).open_target.mem_nhds hz₀] with z hz
  show ζ (chartAt ℂ p ((chartAt ℂ p).symm z)) = teichStretch 0 (ζ z)
  rw [(chartAt ℂ p).right_inv hz]
  simp [teichStretch]

/-- **[stub T4b2] The conformal case of (32.3)**: a biholomorphic map `f₁` of the punctured doubles homotopic to the
symmetric extension commutes with the reflections (`f₁⁻¹ ∘ J₁ ∘ f₁ ∘ J₀` is a biholomorphism homotopic to the identity,
hence the identity by `s82lc_thm32_1_uniqueness_gn`) and maps the half onto the half (`s32w_orientation_halves`). -/
theorem s32w_t324_biholo_commutes {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0) (f : S₀ ≃ₜ S)
    {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) (hfdQ : IsQCRS fd)
    {fdp : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hfdp : ∀ y, (fdp y : Xd₁.carrier) = fd y)
    {f₁ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hbi : IsBiholomorphic f₁)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (f₁ : C(puncturedOpens Pd₀, puncturedOpens Pd₁))) :
    (∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₁ y' : Xd₁.carrier) = J₁ (f₁ y)) ∧
      (fun y : puncturedOpens Pd₀ => (f₁ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} = range ιd₁ := by
  classical
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  have hexd := s32w_t324_double_nonexc hm hex
  -- the double type `(2g + m - 1, 2n)` is never `(0, 3)`: `2n` is even
  have h03 : (2 * g + m - 1, 2 * n) ≠ (0, 3) := by
    intro h
    have h2 := congrArg Prod.snd h
    dsimp only at h2
    omega
  obtain ⟨q, hq, hq0⟩ := s32w_t324_exists_q hexd h03 Fd₀
  have hqh : IsHolQuadDiff q := (admissibleQDInterior_holomorphic Fd₀).1 q hq
  obtain ⟨Q', hQ'⟩ := s32w_dt_teich_comp (Homeomorph.refl _) f₁ hbi (s32w_t324_refl_teich hqh hq0)
  have he : (Homeomorph.refl (puncturedOpens Pd₀)).trans f₁ = f₁ := by
    ext y
    rfl
  rw [he] at hQ'
  obtain ⟨K, hK⟩ := hfdQ
  have hf : IsQCRS f := ⟨K, s32w_se_restrict_isKQCRS F₀ F₁ hd₀ hd₁ hfd hK⟩
  exact s82rc_eq32_3_teichmuller_commutes_reflection hm hex F₀ F₁ hd₀ hd₁ Fd₀ f hf hfd hfdp ⟨hq, hQ'⟩ hhom

/-- **[stub T4c] Restriction to the half**: a homeomorphism of the punctured doubles mapping the half `ιd₀(S₀)` onto
the half `ιd₁(S)` restricts to a homeomorphism `f₀ : S₀ ≃ₜ S`, `ιd₁ ∘ f₀ = f₁ ∘ ιd₀`. -/
theorem s32w_t324_restrict_homeo {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f₁ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁)
    (hhalf : (fun y : puncturedOpens Pd₀ => (f₁ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} =
      range ιd₁) :
    ∃ f₀ : S₀ ≃ₜ S, ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x →
      (f₁ y : Xd₁.carrier) = ιd₁ (f₀ x) := by
  classical
  haveI : Nonempty S₀ := inferInstance
  haveI : Nonempty S := inferInstance
  set e₀ := hd₀.embedding.toOpenPartialHomeomorph ιd₀ with he₀
  set e₁ := hd₁.embedding.toOpenPartialHomeomorph ιd₁ with he₁
  have hoff₀ : ∀ x, ιd₀ x ∉ (↑Pd₀ : Set Xd₀.carrier) := s32w_double_range_off_Pd F₀ hd₀
  have hoff₁ : ∀ x, ιd₁ x ∉ (↑Pd₁ : Set Xd₁.carrier) := s32w_double_range_off_Pd F₁ hd₁
  set G₀ : S₀ → puncturedOpens Pd₀ := fun x => ⟨ιd₀ x, hoff₀ x⟩ with hG₀
  set G₁ : S → puncturedOpens Pd₁ := fun x => ⟨ιd₁ x, hoff₁ x⟩ with hG₁
  have hG₀c : Continuous G₀ := hd₀.embedding.continuous.subtype_mk _
  have hG₁c : Continuous G₁ := hd₁.embedding.continuous.subtype_mk _
  -- `f₁` maps the half into the half, and `f₁⁻¹` too
  have hin : ∀ x, (f₁ (G₀ x) : Xd₁.carrier) ∈ range ιd₁ := fun x =>
    hhalf ▸ ⟨G₀ x, mem_range_self x, rfl⟩
  have hin' : ∀ y, (f₁.symm (G₁ y) : Xd₀.carrier) ∈ range ιd₀ := by
    intro y
    have : ιd₁ y ∈ (fun y : puncturedOpens Pd₀ => (f₁ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} := by
      rw [hhalf]; exact mem_range_self y
    obtain ⟨z, hz, hzy⟩ := this
    have hz' : f₁.symm (G₁ y) = z := by
      rw [f₁.symm_apply_eq]; exact Subtype.ext hzy.symm
    rw [hz']; exact hz
  set φ : S₀ → S := fun x => e₁.symm (f₁ (G₀ x)) with hφ
  set ψ : S → S₀ := fun y => e₀.symm (f₁.symm (G₁ y)) with hψ
  have hφr : ∀ x, ιd₁ (φ x) = f₁ (G₀ x) := fun x => hd₁.embedding.toOpenPartialHomeomorph_right_inv ιd₁ (hin x)
  have hψr : ∀ y, ιd₀ (ψ y) = f₁.symm (G₁ y) := fun y =>
    hd₀.embedding.toOpenPartialHomeomorph_right_inv ιd₀ (hin' y)
  have hφc : Continuous φ := by
    have h1 : Continuous fun x => (f₁ (G₀ x) : Xd₁.carrier) := continuous_subtype_val.comp (f₁.continuous.comp hG₀c)
    refine (e₁.continuousOn_symm.comp_continuous h1 fun x => ?_)
    rw [hd₁.embedding.toOpenPartialHomeomorph_target]; exact hin x
  have hψc : Continuous ψ := by
    have h1 : Continuous fun y => (f₁.symm (G₁ y) : Xd₀.carrier) :=
      continuous_subtype_val.comp (f₁.symm.continuous.comp hG₁c)
    refine (e₀.continuousOn_symm.comp_continuous h1 fun y => ?_)
    rw [hd₀.embedding.toOpenPartialHomeomorph_target]; exact hin' y
  have hψφ : ∀ x, ψ (φ x) = x := by
    intro x
    apply hd₀.embedding.injective
    rw [hψr]
    have : G₁ (φ x) = f₁ (G₀ x) := Subtype.ext (hφr x)
    rw [this, f₁.symm_apply_apply]
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    apply hd₁.embedding.injective
    rw [hφr]
    have : G₀ (ψ y) = f₁.symm (G₁ y) := Subtype.ext (hψr y)
    rw [this, f₁.apply_symm_apply]
  refine ⟨⟨⟨φ, ψ, hψφ, hφψ⟩, hφc, hψc⟩, fun y x hyx => ?_⟩
  have : y = G₀ x := Subtype.ext hyx
  rw [this]
  exact (hφr x).symm

/-- A conj transport by an anticonformal involution is involutive on `(2,0)` families (the generic form of
`s31qd_conj_involutive`, whose proof this is with `K` given directly). -/
theorem s32w_t324_conj_involutive {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {K : B ≃ₜ B} (hK : IsAnticonformalInvolution K) {Q : B → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) :
    s31qr_transportOn univ K Complex.conjCLE.toLinearMap (s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q) =
      Q := by
  classical
  have hC : ∀ t : ℂ, Complex.conjCLE.toLinearMap t = conj t := fun t => rfl
  have hKK : ∀ y, K (K y) = y := hK.1
  have hinner : ∀ b : B,
      s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q b (chartAt ℂ b b) =
        conj (Q (K b) (chartAt ℂ (K b) (K b))) *
          deriv (fun v => conj (chartAt ℂ (K b) (K ((chartAt ℂ b).symm v))))
            (chartAt ℂ b b) ^ 2 := by
    intro b
    have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
      (chartAt ℂ b).map_source (mem_chart_source ℂ b)
    have e := s31dc_transport_eq univ K Complex.conjCLE.toLinearMap Q b hbt (mem_univ _)
    rw [(chartAt ℂ b).left_inv (mem_chart_source ℂ b)] at e
    exact e
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  swap
  · rw [s31dc_transport_off_target _ _ _ _ x hz, hQ.1 x z hz]
  obtain ⟨p, hp⟩ : ∃ p, p = (chartAt ℂ x).symm z := ⟨_, rfl⟩
  have hps : p ∈ (chartAt ℂ x).source := by rw [hp]; exact (chartAt ℂ x).map_target hz
  have e1 := s31dc_transport_eq univ K Complex.conjCLE.toLinearMap
    (s31qr_transportOn univ K Complex.conjCLE.toLinearMap Q) x hz (mem_univ _)
  rw [← hp] at e1
  rw [e1, hinner (K p), hKK p]
  simp only [hC]
  have hQx : Q x z = Q p (chartAt ℂ p p) * deriv (chartTransition p x) z ^ 2 := by
    have hh := hQ.2 p x z hz (by rw [← hp]; exact mem_chart_source ℂ p)
    have he : chartTransition p x z = chartAt ℂ p p := by
      change chartAt ℂ p ((chartAt ℂ x).symm z) = _
      rw [← hp]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hbt : chartAt ℂ (K p) (K p) ∈ (chartAt ℂ (K p)).target :=
    (chartAt ℂ (K p)).map_source (mem_chart_source ℂ (K p))
  have hsb : (chartAt ℂ (K p)).symm (chartAt ℂ (K p) (K p)) = K p :=
    (chartAt ℂ (K p)).left_inv (mem_chart_source ℂ (K p))
  let f : ℂ → ℂ := fun w => conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm w)))
  let g : ℂ → ℂ := fun v => conj (chartAt ℂ p (K ((chartAt ℂ (K p)).symm v)))
  have hf : DifferentiableAt ℂ f z :=
    s31q2_return_after_involution_chart K hK (id : B → B) x (K p) hz
      (by rw [← hp]; exact mem_chart_source ℂ (K p)) mdifferentiableAt_id
  have hg : DifferentiableAt ℂ g (chartAt ℂ (K p) (K p)) :=
    s31q2_return_after_involution_chart K hK (id : B → B) (K p) p hbt
      (by rw [hsb, hKK]; exact mem_chart_source ℂ p) mdifferentiableAt_id
  have hfz : f z = conj (chartAt ℂ (K p) (K p)) := by
    show conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm z))) = _
    rw [← hp]
  have hcontK : ContinuousAt (fun w => K ((chartAt ℂ x).symm w)) z :=
    K.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have hnb : (chartAt ℂ (K p)).source ∈ 𝓝 (K ((chartAt ℂ x).symm z)) :=
    (chartAt ℂ (K p)).open_source.mem_nhds (by rw [← hp]; exact mem_chart_source ℂ (K p))
  have hev : (fun w => chartAt ℂ p ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z]
      (conj ∘ g ∘ conj) ∘ f := by
    filter_upwards [hcontK.preimage_mem_nhds hnb] with w hw
    have hw' : K ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (K p)).source := hw
    show chartAt ℂ p ((chartAt ℂ x).symm w) =
      conj (conj (chartAt ℂ p (K ((chartAt ℂ (K p)).symm
        (conj (conj (chartAt ℂ (K p) (K ((chartAt ℂ x).symm w)))))))))
    simp only [Complex.conj_conj]
    rw [(chartAt ℂ (K p)).left_inv hw', hKK]
  have hcc : HasDerivAt (conj ∘ g ∘ conj) (conj (deriv g (chartAt ℂ (K p) (K p))))
      (conj (chartAt ℂ (K p) (K p))) := hg.hasDerivAt.conj_conj
  have hcc' : HasDerivAt (conj ∘ g ∘ conj) (conj (deriv g (chartAt ℂ (K p) (K p)))) (f z) := by
    rw [hfz]
    exact hcc
  have hder : conj (deriv g (chartAt ℂ (K p) (K p))) * deriv f z =
      deriv (chartTransition p x) z := by
    change _ = deriv (fun w => chartAt ℂ p ((chartAt ℂ x).symm w)) z
    rw [hev.deriv_eq]
    exact (hcc'.comp z hf.hasDerivAt).deriv.symm
  rw [hQx, ← hder]
  simp only [map_mul, map_pow, Complex.conj_conj]
  ring

/-- **[stub T4d] The extremal differential is symmetric**: if an admissible Teichmüller map `f₁` of the punctured
doubles commutes with the reflections, its differential `Q` is `Jd₀`-symmetric (`J₁ ∘ f₁ ∘ J₀ = f₁` is Teichmüller
for the conjugate-transported data; `s82td_data_unique` gives a positive factor, equal to `1` since the transport is
an involution).  For `k = 0` the initial differential is not determined by the map, hence `hk`. -/
theorem s32w_t324_Q_symm {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0)
    (Jd₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) (hJd₀ : ∀ y, (Jd₀ y : Xd₀.carrier) = J₀ y)
    {f₁ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} {Q : puncturedOpens Pd₀ → ℂ → ℂ}
    {Q' : puncturedOpens Pd₁ → ℂ → ℂ} {k : ℝ} (hf₁ : IsAdmissibleTeichmullerMap Fd₀ f₁ Q Q' k) (hk : 0 < k)
    (hJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₁ y' : Xd₁.carrier) = J₁ (f₁ y)) :
    ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (Jd₀ ((chartAt ℂ y).symm z))
          (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm w)))) z ^ 2 := by
  classical
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  haveI : ConnectedSpace (puncturedOpens Pd₁) := s32w_punctured_connectedSpace Pd₁
  let Jd₁ : puncturedOpens Pd₁ ≃ₜ puncturedOpens Pd₁ :=
    J₁.subtype (fun x => by
      show x ∉ (↑Pd₁ : Set Xd₁.carrier) ↔ J₁ x ∉ (↑Pd₁ : Set Xd₁.carrier)
      have key : ∀ y, y ∈ (↑Pd₁ : Set Xd₁.carrier) → J₁ y ∈ (↑Pd₁ : Set Xd₁.carrier) := fun y hy => by
        rw [← hd₁.Pd_invariant]; exact mem_image_of_mem J₁ hy
      exact ⟨fun hx hJx => hx (by have := key _ hJx; rwa [hd₁.involution.1] at this),
        fun hx hx' => hx (key _ hx')⟩)
  have hJd₁ : ∀ y, (Jd₁ y : Xd₁.carrier) = J₁ y := fun y => rfl
  have hA₀ : IsAnticonformalInvolution Jd₀ :=
    s32w_dt_opens_involution (puncturedOpens Pd₀) Jd₀ J₀ hd₀.involution hJd₀
  have hA₁ : IsAnticonformalInvolution Jd₁ :=
    s32w_dt_opens_involution (puncturedOpens Pd₁) Jd₁ J₁ hd₁.involution hJd₁
  have hcomm : ∀ y, f₁ (Jd₀ y) = Jd₁ (f₁ y) := fun y =>
    Subtype.ext (by rw [hJd₁]; exact hJ y (Jd₀ y) (hJd₀ y))
  -- `f₁` is also Teichmüller for the conj-transported data, so that data is a positive multiple of `Q`
  have hT := s32w_t324_conj_teich hA₀ hA₁ hf₁.2 hcomm
  obtain ⟨-, c, hc0, hc⟩ := s82td_data_unique hf₁.2 hT hk
  -- the factor is `1`: the transport is an involution
  have hQfam : IsDiffFamily 2 0 Q :=
    (hf₁.2.initial : IsDiffFamily 2 0 Q ∧ ∀ x, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target).1
  have hinv := s32w_t324_conj_involutive hA₀ hQfam
  rw [hc, s31qd_conj_transport_smul, hc, Complex.conj_ofReal, smul_smul] at hinv
  have hcc : (c : ℂ) * c = 1 := by
    obtain ⟨y, z, hyz⟩ : ∃ y z, Q y z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf₁.2.initial_ne (funext fun y => funext fun z => h y z)
    have h1 := congrFun (congrFun hinv y) z
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have h2 : ((c : ℂ) * c - 1) * Q y z = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hyz)
  have hc1 : c = 1 := by
    have h3 : c * c = 1 := by exact_mod_cast hcc
    nlinarith
  intro y z hz
  rw [← s31qd5_conj_transport_apply univ Jd₀ Q y hz (mem_univ _), hc, hc1]
  simp

/-- **Restriction of a `K`-q.c. map through holomorphic open embeddings**: if `f ∘ G₀ = G₁ ∘ f₀`, then `f₀` is
`K`-q.c. whenever `f` is (the proof of `s32w_se_restrict_isKQCRS` with `ιd₀, ιd₁` replaced by `G₀, G₁`). -/
theorem s32w_t324_restrict_isKQCRS {A' A B' B : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A']
    [IsManifold 𝓘(ℂ) ω A'] [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [TopologicalSpace B'] [ChartedSpace ℂ B'] [IsManifold 𝓘(ℂ) ω B'] [Nonempty B']
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {G₀ : A' → A} {G₁ : B' → B} (hG₀ : Topology.IsOpenEmbedding G₀) (hG₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hG₁ : Topology.IsOpenEmbedding G₁) (hG₁m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁)
    {f : A ≃ₜ B} {f₀ : A' ≃ₜ B'} (hrel : ∀ x, f (G₀ x) = G₁ (f₀ x)) {K : ℝ} (hK : IsKQCRS f K) :
    IsKQCRS f₀ K := by
  refine s32w_se_isKQCRS_of_local f₀ hK.1 fun x => ?_
  set e₁ := hG₁.toOpenPartialHomeomorph G₁ with he₁
  have hl₁ : ∀ b : B', e₁.symm (G₁ b) = b := fun b => hG₁.toOpenPartialHomeomorph_left_inv G₁
  set y := G₀ x with hy
  set cx := chartAt ℂ x with hcx
  set cy := chartAt ℂ y with hcy
  have hxs : x ∈ cx.source := mem_chart_source ℂ x
  have hys : y ∈ cy.source := mem_chart_source ℂ y
  -- `τ = φ_y ∘ G₀ ∘ φ_x⁻¹`
  set O₁ : Set ℂ := cx.target ∩ cx.symm ⁻¹' (G₀ ⁻¹' cy.source) with hO₁
  have hO₁o : IsOpen O₁ := cx.isOpen_inter_preimage_symm (cy.open_source.preimage hG₀.continuous)
  have hx₁ : cx x ∈ O₁ :=
    ⟨cx.map_source hxs, by show G₀ (cx.symm (cx x)) ∈ cy.source; rw [cx.left_inv hxs]; exact hys⟩
  have hτd : DifferentiableOn ℂ (fun w => cy (G₀ (cx.symm w))) O₁ := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cx.symm w := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cy (G₀ (cx.symm w)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ y) hw.2
    exact (mdifferentiableAt_iff_differentiableAt.1
      (h2.comp w ((hG₀m _).comp w h1))).differentiableWithinAt
  have hτi : InjOn (fun w => cy (G₀ (cx.symm w))) O₁ := by
    intro w hw v hv he
    exact cx.symm.injOn hw.1 hv.1 (hG₀.injective (cy.injOn hw.2 hv.2 he))
  have hτa : AnalyticAt ℂ (fun w => cy (G₀ (cx.symm w))) (cx x) := hτd.analyticAt (hO₁o.mem_nhds hx₁)
  have hτ' : deriv (fun w => cy (G₀ (cx.symm w))) (cx x) ≠ 0 := deriv_ne_zero_of_injOn hO₁o hτd hτi hx₁
  have hτz : (fun w => cy (G₀ (cx.symm w))) (cx x) = cy y := by
    show cy (G₀ (cx.symm (cx x))) = cy y; rw [cx.left_inv hxs]
  have hτV : (fun w => cy (G₀ (cx.symm w))) (cx x) ∈ localMapDomain f y := by
    rw [hτz]
    refine ⟨cy.map_source hys, ?_⟩
    show f (cy.symm (cy y)) ∈ (chartAt ℂ (f y)).source
    rw [cy.left_inv hys]; exact mem_chart_source ℂ _
  -- `σ = φ_{f₀ x} ∘ G₁⁻¹ ∘ φ_{f y}⁻¹`
  set cq := chartAt ℂ (f y) with hcq
  set cf := chartAt ℂ (f₀ x) with hcf
  have hfdy : f y = G₁ (f₀ x) := hrel x
  set O₂ : Set ℂ := cq.target ∩ cq.symm ⁻¹' (range G₁ ∩ e₁.symm ⁻¹' cf.source) with hO₂
  have hO₂o : IsOpen O₂ := by
    refine cq.isOpen_inter_preimage_symm ?_
    have : IsOpen (e₁.target ∩ e₁.symm ⁻¹' cf.source) := e₁.isOpen_inter_preimage_symm cf.open_source
    rwa [hG₁.toOpenPartialHomeomorph_target] at this
  have hqs : f y ∈ cq.source := mem_chart_source ℂ _
  have hv₂ : cq (f y) ∈ O₂ := ⟨cq.map_source hqs, by
    show cq.symm (cq (f y)) ∈ range G₁ ∩ e₁.symm ⁻¹' cf.source
    rw [cq.left_inv hqs, hfdy]
    exact ⟨mem_range_self _, by show e₁.symm (G₁ (f₀ x)) ∈ cf.source; rw [hl₁]; exact mem_chart_source ℂ _⟩⟩
  have hσd : DifferentiableOn ℂ (fun v => cf (e₁.symm (cq.symm v))) O₂ := by
    intro v hv
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cq.symm v := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) hv.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e₁.symm (cq.symm v) :=
      s31qr_open_embedding_inverse hG₁ hG₁m hv.2.1
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cf (e₁.symm (cq.symm v)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hv.2.2
    exact (mdifferentiableAt_iff_differentiableAt.1 (h3.comp v (h2.comp v h1))).differentiableWithinAt
  have hσi : InjOn (fun v => cf (e₁.symm (cq.symm v))) O₂ := by
    intro v hv w hw he
    have h1 := cf.injOn hv.2.2 hw.2.2 he
    obtain ⟨b, hb⟩ := hv.2.1
    obtain ⟨b', hb'⟩ := hw.2.1
    rw [← hb, ← hb', hl₁, hl₁] at h1
    exact cq.symm.injOn hv.1 hw.1 (by rw [← hb, ← hb', h1])
  have hFτ : localMapExpr f y ((fun w => cy (G₀ (cx.symm w))) (cx x)) = cq (f y) := by
    rw [hτz]
    show cq (f (cy.symm (cy y))) = cq (f y)
    rw [cy.left_inv hys]
  have hσa : AnalyticAt ℂ (fun v => cf (e₁.symm (cq.symm v)))
      (localMapExpr f y ((fun w => cy (G₀ (cx.symm w))) (cx x))) := by
    rw [hFτ]; exact hσd.analyticAt (hO₂o.mem_nhds hv₂)
  have hσ' : deriv (fun v => cf (e₁.symm (cq.symm v)))
      (localMapExpr f y ((fun w => cy (G₀ (cx.symm w))) (cx x))) ≠ 0 := by
    rw [hFτ]; exact deriv_ne_zero_of_injOn hO₂o hσd hσi hv₂
  have hev : ∀ᶠ w in 𝓝 (cx x), localMapExpr f₀ x w =
      (fun v => cf (e₁.symm (cq.symm v))) (localMapExpr f y ((fun w => cy (G₀ (cx.symm w))) w)) := by
    have hc1 : ContinuousAt cx.symm (cx x) := cx.continuousAt_symm (cx.map_source hxs)
    have h1 : ∀ᶠ w in 𝓝 (cx x), G₀ (cx.symm w) ∈ cy.source := by
      refine (hG₀.continuous.continuousAt.comp hc1).preimage_mem_nhds ?_
      show cy.source ∈ 𝓝 (G₀ (cx.symm (cx x)))
      rw [cx.left_inv hxs]; exact cy.open_source.mem_nhds hys
    have h2 : ∀ᶠ w in 𝓝 (cx x), f (G₀ (cx.symm w)) ∈ cq.source := by
      refine (f.continuous.continuousAt.comp
        (hG₀.continuous.continuousAt.comp hc1)).preimage_mem_nhds ?_
      show cq.source ∈ 𝓝 (f (G₀ (cx.symm (cx x))))
      rw [cx.left_inv hxs]; exact cq.open_source.mem_nhds hqs
    filter_upwards [h1, h2] with w hw1 hw2
    show cf (f₀ (cx.symm w)) = cf (e₁.symm (cq.symm (cq (f (cy.symm (cy (G₀ (cx.symm w))))))))
    rw [cy.left_inv hw1, cq.left_inv hw2, hrel, hl₁]
  obtain ⟨U, hUo, hzU, -, hUK⟩ := s26w_isKQC_local_comp (hK.2 y) hτV hτa hτ' hσa hσ' hev univ_mem
  exact ⟨U, hUo, hzU, hUK⟩

/-- The coordinate expression `φ_{G x} ∘ G ∘ φ_x⁻¹` of a holomorphic open embedding is analytic at the chart centre
with nonzero derivative. -/
theorem s32w_t324_emb_coord {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hG : Topology.IsOpenEmbedding G) (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (x : A') :
    AnalyticAt ℂ (fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) (chartAt ℂ x x) ∧
      (fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) (chartAt ℂ x x) = chartAt ℂ (G x) (G x) ∧
      deriv (fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) (chartAt ℂ x x) ≠ 0 := by
  have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hys : G x ∈ (chartAt ℂ (G x)).source := mem_chart_source ℂ (G x)
  set O₁ : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (G ⁻¹' (chartAt ℂ (G x)).source) with hO₁
  have hO₁o : IsOpen O₁ :=
    (chartAt ℂ x).isOpen_inter_preimage_symm ((chartAt ℂ (G x)).open_source.preimage hG.continuous)
  have hx₁ : chartAt ℂ x x ∈ O₁ := ⟨(chartAt ℂ x).map_source hxs, by
    show G ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ (chartAt ℂ (G x)).source
    rw [(chartAt ℂ x).left_inv hxs]; exact hys⟩
  have hτd : DifferentiableOn ℂ (fun w => chartAt ℂ (G x) (G ((chartAt ℂ x).symm w))) O₁ := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm w :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (G x)) (G ((chartAt ℂ x).symm w)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ (G x)) hw.2
    exact (mdifferentiableAt_iff_differentiableAt.1 (h2.comp w ((hGm _).comp w h1))).differentiableWithinAt
  have hτi : InjOn (fun w => chartAt ℂ (G x) (G ((chartAt ℂ x).symm w))) O₁ := by
    intro w hw v hv he
    exact (chartAt ℂ x).symm.injOn hw.1 hv.1 (hG.injective ((chartAt ℂ (G x)).injOn hw.2 hv.2 he))
  refine ⟨hτd.analyticAt (hO₁o.mem_nhds hx₁), ?_, deriv_ne_zero_of_injOn hO₁o hτd hτi hx₁⟩
  show chartAt ℂ (G x) (G ((chartAt ℂ x).symm (chartAt ℂ x x))) = _
  rw [(chartAt ℂ x).left_inv hxs]

/-- The pull-back by a holomorphic map, in the chart at `G x` (the transformation law, `s82lc_raw_local`). -/
theorem s32w_t324_emb_formula {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {Q : A → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) (x : A') {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hGz : G ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (G x)).source) :
    s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z =
      Q (G x) (chartAt ℂ (G x) (G ((chartAt ℂ x).symm z))) *
        deriv (fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) z ^ 2 := by
  rw [s31qd5_id_transport_apply univ G Q x hz (mem_univ _)]
  exact s82lc_raw_local hQ G x (G x) hz (hGm _) hGz

/-- Near the chart centre the pull-back is `Q_{G x} ∘ T · T'²`, `T = φ_{G x} ∘ G ∘ φ_x⁻¹`. -/
theorem s32w_t324_emb_eventually {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {Q : A → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) (x : A') :
    ∀ᶠ z in 𝓝 (chartAt ℂ x x), s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z =
      Q (G x) (chartAt ℂ (G x) (G ((chartAt ℂ x).symm z))) *
        deriv (fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) z ^ 2 := by
  have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hc : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxs
  have hcont : ContinuousAt (fun v => G ((chartAt ℂ x).symm v)) (chartAt ℂ x x) :=
    ContinuousAt.comp (g := G) (hGm _).continuousAt ((chartAt ℂ x).continuousAt_symm hc)
  have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ x x), G ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (G x)).source := by
    refine hcont.preimage_mem_nhds ((chartAt ℂ (G x)).open_source.mem_nhds ?_)
    show G ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ _
    rw [(chartAt ℂ x).left_inv hxs]; exact mem_chart_source ℂ _
  filter_upwards [h1, (chartAt ℂ x).open_target.mem_nhds hc] with z hz1 hz2
  exact s32w_t324_emb_formula hGm hQ x hz2 hz1

/-- Zero orders are preserved by the pull-back through a holomorphic open embedding. -/
theorem s32w_t324_emb_order {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hG : Topology.IsOpenEmbedding G) (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {Q : A → ℂ → ℂ}
    (hQ : IsHolQuadDiff Q) (x : A') :
    meromorphicOrderAt (s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x) (chartAt ℂ x x) =
      meromorphicOrderAt (Q (G x)) (chartAt ℂ (G x) (G x)) := by
  have hQ' : IsDiffFamily 2 0 Q ∧ ∀ a : A, DifferentiableOn ℂ (Q a) (chartAt ℂ a).target := hQ
  obtain ⟨hTa, hTc, hTd⟩ := s32w_t324_emb_coord hG hGm x
  set T : ℂ → ℂ := fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v)) with hT
  have hcG : chartAt ℂ (G x) (G x) ∈ (chartAt ℂ (G x)).target :=
    (chartAt ℂ (G x)).map_source (mem_chart_source ℂ _)
  have hQa : AnalyticAt ℂ (Q (G x)) (T (chartAt ℂ x x)) := by
    rw [hTc]; exact (hQ'.2 (G x)).analyticAt ((chartAt ℂ (G x)).open_target.mem_nhds hcG)
  have heq : s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x =ᶠ[𝓝 (chartAt ℂ x x)]
      (Q (G x) ∘ T) * deriv T ^ 2 := by
    filter_upwards [s32w_t324_emb_eventually hGm hQ'.1 x] with z hz
    rw [hz]; rfl
  have hd2 : meromorphicOrderAt (deriv T ^ 2) (chartAt ℂ x x) = ((0 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff (hTa.deriv.pow 2).meromorphicAt]
    refine ⟨deriv T ^ 2, hTa.deriv.pow 2, pow_ne_zero 2 hTd, ?_⟩
    filter_upwards with z
    simp
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul (hQa.comp hTa).meromorphicAt (hTa.deriv.pow 2).meromorphicAt, hd2,
    meromorphicOrderAt_comp_of_deriv_ne_zero hTa hTd, hTc]
  simp

/-- Regular points correspond under the pull-back through a holomorphic open embedding. -/
theorem s32w_t324_emb_regular {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hG : Topology.IsOpenEmbedding G) (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (Q : A → ℂ → ℂ) (x : A') :
    IsRegularPoint (s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) x ↔ IsRegularPoint Q (G x) := by
  obtain ⟨-, -, hTd⟩ := s32w_t324_emb_coord hG hGm x
  show s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x (chartAt ℂ x x) ≠ 0 ↔
    Q (G x) (chartAt ℂ (G x) (G x)) ≠ 0
  rw [s32w_dt_cv_id univ G Q (mem_univ x)]
  simp [hTd]

/-- Natural parameters pull back: `ζ ∘ T` is a natural parameter of the pull-back at `x`. -/
theorem s32w_t324_emb_natural {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hG : Topology.IsOpenEmbedding G) (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {Q : A → ℂ → ℂ}
    (hQ : IsDiffFamily 2 0 Q) (x : A') {ζ : ℂ → ℂ} (hζ : IsNaturalParameterAt Q (G x) ζ) :
    IsNaturalParameterAt (s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) x
      (ζ ∘ fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v))) := by
  obtain ⟨hTa, hTc, hTd⟩ := s32w_t324_emb_coord hG hGm x
  set T : ℂ → ℂ := fun v => chartAt ℂ (G x) (G ((chartAt ℂ x).symm v)) with hT
  have hTt : Tendsto T (𝓝 (chartAt ℂ x x)) (𝓝 (chartAt ℂ (G x) (G x))) := by
    rw [← hTc]; exact hTa.continuousAt.tendsto
  refine ⟨AnalyticAt.comp_of_eq hζ.1 hTa hTc, ?_, ?_, ?_⟩
  · show ζ (T (chartAt ℂ x x)) = 0
    rw [hTc]; exact hζ.2.1
  · rw [deriv_comp _ (by rw [hTc]; exact hζ.1.differentiableAt) hTa.differentiableAt, hTc]
    exact mul_ne_zero hζ.2.2.1 hTd
  · filter_upwards [hTa.eventually_analyticAt, hTt.eventually hζ.1.eventually_analyticAt,
      hTt.eventually hζ.2.2.2, s32w_t324_emb_eventually hGm hQ x] with z h1 h2 h3 h4
    rw [deriv_comp z h2.differentiableAt h1.differentiableAt, mul_pow, h3, h4]

/-- The pull-back of a holomorphic quadratic differential through a holomorphic map is holomorphic. -/
theorem s32w_t324_emb_hol {A' A : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A'] [IsManifold 𝓘(ℂ) ω A']
    [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A] {G : A' → A}
    (hGm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {Q : A → ℂ → ℂ} (hQ : IsHolQuadDiff Q) :
    IsHolQuadDiff (s31qr_transportOn univ G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) := by
  show IsDiffFamily 2 0 _ ∧ ∀ x, DifferentiableOn ℂ _ (chartAt ℂ x).target
  refine ⟨s31qr_transport_family univ G _
    (fun x z hz _ => s31qr_coordinate_differentiable x _ hz (mem_chart_source ℂ _) (hGm _)) Q, fun x z hz => ?_⟩
  refine (DifferentiableAt.congr_of_eventuallyEq (s82lc_raw_diff hQ G isOpen_univ (fun t _ => hGm t) x hz
    (mem_univ _)) ?_).differentiableWithinAt
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with w hw
  exact s31qd5_id_transport_apply univ G Q x hw (mem_univ _)

/-- **Restriction of a Teichmüller map through holomorphic open embeddings**: if `f ∘ G₀ = G₁ ∘ f₀` and `f` is a
Teichmüller map for `(Q, Q', k)`, then `f₀` is a Teichmüller map for the pull-backs. -/
theorem s32w_t324_teich_restrict {A' A B' B : Type*} [TopologicalSpace A'] [ChartedSpace ℂ A']
    [IsManifold 𝓘(ℂ) ω A'] [Nonempty A'] [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    [T2Space A] [ConnectedSpace A]
    [TopologicalSpace B'] [ChartedSpace ℂ B'] [IsManifold 𝓘(ℂ) ω B'] [Nonempty B']
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {G₀ : A' → A} {G₁ : B' → B} (hG₀ : Topology.IsOpenEmbedding G₀) (hG₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀)
    (hG₁ : Topology.IsOpenEmbedding G₁) (hG₁m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁)
    {f : A ≃ₜ B} {f₀ : A' ≃ₜ B'} (hrel : ∀ x, f (G₀ x) = G₁ (f₀ x)) {Q : A → ℂ → ℂ} {Q' : B → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f Q Q' k) :
    IsTeichmullerMap f₀ (s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q)
      (s31qr_transportOn univ G₁ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q') k := by
  have hQ := hf.initial
  have hQ' := hf.terminal
  have hQs : IsDiffFamily 2 0 Q ∧ ∀ a : A, DifferentiableOn ℂ (Q a) (chartAt ℂ a).target := hQ
  have hQ's : IsDiffFamily 2 0 Q' ∧ ∀ a : B, DifferentiableOn ℂ (Q' a) (chartAt ℂ a).target := hQ'
  obtain ⟨K, hK⟩ := hf.qc
  refine ⟨⟨K, s32w_t324_restrict_isKQCRS hG₀ hG₀m hG₁ hG₁m hrel hK⟩, s32w_t324_emb_hol hG₀m hQ, ?_,
    s32w_t324_emb_hol hG₁m hQ', hf.k_nonneg, hf.k_lt_one, ?_, ?_⟩
  · -- the pull-back is nonzero: otherwise `Q` vanishes near a point of the image, hence everywhere
    intro h0
    obtain ⟨x⟩ : Nonempty A' := inferInstance
    have hord := s32w_t324_emb_order hG₀ hG₀m hQ x
    rw [h0] at hord
    have htop : meromorphicOrderAt (Q (G₀ x)) (chartAt ℂ (G₀ x) (G₀ x)) = ⊤ := by
      rw [← hord, meromorphicOrderAt_eq_top_iff]
      filter_upwards with z
      rfl
    have hcG : chartAt ℂ (G₀ x) (G₀ x) ∈ (chartAt ℂ (G₀ x)).target :=
      (chartAt ℂ (G₀ x)).map_source (mem_chart_source ℂ _)
    have hQa : AnalyticAt ℂ (Q (G₀ x)) (chartAt ℂ (G₀ x) (G₀ x)) :=
      (hQs.2 (G₀ x)).analyticAt ((chartAt ℂ (G₀ x)).open_target.mem_nhds hcG)
    have hev : ∀ᶠ z in 𝓝 (chartAt ℂ (G₀ x) (G₀ x)), Q (G₀ x) z = 0 :=
      hQa.frequently_zero_iff_eventually_zero.1 (meromorphicOrderAt_eq_top_iff.1 htop).frequently
    exact hf.initial_ne (s82td_hol_eq_zero hQ (G₀ x) hev)
  · intro x hx
    have hGx : IsRegularPoint Q (G₀ x) := (s32w_t324_emb_regular hG₀ hG₀m Q x).1 hx
    obtain ⟨hreg', ζ, ζ', hζ, hζ', hr⟩ := hf.regular (G₀ x) hGx
    rw [hrel] at hreg' hζ'
    obtain ⟨hT₀a, hT₀c, -⟩ := s32w_t324_emb_coord hG₀ hG₀m x
    have hT₀t : Tendsto (fun v => chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm v))) (𝓝 (chartAt ℂ x x))
        (𝓝 (chartAt ℂ (G₀ x) (G₀ x))) := by
      rw [← hT₀c]; exact hT₀a.continuousAt.tendsto
    refine ⟨(s32w_t324_emb_regular hG₁ hG₁m Q' (f₀ x)).2 hreg', _, _, s32w_t324_emb_natural hG₀ hG₀m hQs.1 x hζ,
      s32w_t324_emb_natural hG₁ hG₁m hQ's.1 (f₀ x) hζ', ?_⟩
    have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hc : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxs
    have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ x x), f₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f₀ x)).source := by
      refine (ContinuousAt.comp (g := f₀) f₀.continuous.continuousAt
        ((chartAt ℂ x).continuousAt_symm hc)).preimage_mem_nhds ((chartAt ℂ (f₀ x)).open_source.mem_nhds ?_)
      show f₀ ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ _
      rw [(chartAt ℂ x).left_inv hxs]; exact mem_chart_source ℂ _
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ x x), G₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (G₀ x)).source := by
      refine (ContinuousAt.comp (g := G₀) hG₀.continuous.continuousAt
        ((chartAt ℂ x).continuousAt_symm hc)).preimage_mem_nhds ((chartAt ℂ (G₀ x)).open_source.mem_nhds ?_)
      show G₀ ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ _
      rw [(chartAt ℂ x).left_inv hxs]; exact mem_chart_source ℂ _
    filter_upwards [h1, h2, hT₀t.eventually hr] with z hz1 hz2 hz3
    have e : chartAt ℂ (G₁ (f₀ x)) (G₁ ((chartAt ℂ (f₀ x)).symm (localMapExpr f₀ x z))) =
        localMapExpr f (G₀ x) (chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm z))) := by
      show chartAt ℂ (G₁ (f₀ x)) (G₁ ((chartAt ℂ (f₀ x)).symm (chartAt ℂ (f₀ x) (f₀ ((chartAt ℂ x).symm z))))) =
        chartAt ℂ (f (G₀ x)) (f ((chartAt ℂ (G₀ x)).symm (chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm z)))))
      rw [(chartAt ℂ (f₀ x)).left_inv hz1, (chartAt ℂ (G₀ x)).left_inv hz2, hrel, hrel]
    show ζ' (chartAt ℂ (G₁ (f₀ x)) (G₁ ((chartAt ℂ (f₀ x)).symm (localMapExpr f₀ x z)))) =
      teichStretch k (ζ (chartAt ℂ (G₀ x) (G₀ ((chartAt ℂ x).symm z))))
    rw [e]
    exact hz3
  · intro x n hxn
    have h1 : IsZeroOfOrder Q (G₀ x) n := by
      show meromorphicOrderAt (Q (G₀ x)) _ = _
      rw [← s32w_t324_emb_order hG₀ hG₀m hQ x]
      exact hxn
    have h2 := hf.zero (G₀ x) n h1
    show meromorphicOrderAt (s31qr_transportOn univ G₁ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q' (f₀ x)) _ = _
    rw [s32w_t324_emb_order hG₁ hG₁m hQ' (f₀ x), ← hrel x]
    exact h2

/-- **[stub T4e1] Restriction of the Teichmüller data**: the restriction `f₀` of an admissible Teichmüller map `f₁`
of the punctured doubles with `Jd₀`-symmetric differential `Q` is an admissible Teichmüller map of `S₀` (for the
restriction of `Q`, an admissible differential of `F₀` by `s31qd_restriction`, and the pull-back of `Q'`). -/
theorem s32w_t324_restrict_teich {g n m : ℕ} (hm : m ≠ 0) (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (Fd₀ : FiniteTypeStructure (puncturedOpens Pd₀) (2 * g + m - 1) (2 * n) 0)
    (Jd₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) (hJd₀ : ∀ y, (Jd₀ y : Xd₀.carrier) = J₀ y)
    {f₁ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} {Q : puncturedOpens Pd₀ → ℂ → ℂ}
    {Q' : puncturedOpens Pd₁ → ℂ → ℂ} {k : ℝ} (hf₁ : IsAdmissibleTeichmullerMap Fd₀ f₁ Q Q' k) (hk : 0 < k)
    (hQ : ∀ y z, z ∈ (chartAt ℂ y).target →
      Q y z = conj (Q (Jd₀ ((chartAt ℂ y).symm z))
          (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => conj (chartAt ℂ (Jd₀ ((chartAt ℂ y).symm z)) (Jd₀ ((chartAt ℂ y).symm w)))) z ^ 2)
    {f₀ : S₀ ≃ₜ S} (hrel : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x →
      (f₁ y : Xd₁.carrier) = ιd₁ (f₀ x)) :
    ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k' : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k' := by
  classical
  haveI : Nonempty S₀ := inferInstance
  haveI : Nonempty S := inferInstance
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  obtain ⟨Qd, hQd, hQe0⟩ := Submodule.mem_map.1 hf₁.1
  have hQdA : IsAdmissibleQD Fd₀ Qd := hQd
  have hQe : Q = pullbackQD Fd₀ Qd := hQe0.symm
  obtain ⟨E, hE, hEι, hEP⟩ := s31qr_fd_compactification Xd₀ Pd₀ Fd₀
  obtain ⟨T, hT⟩ := s31qi_seam_fill F₀ hm hd₀
  have hQhol : IsHolQuadDiff Q := hf₁.2.initial
  have hQfam : IsDiffFamily 2 0 Q :=
    (hQhol : IsDiffFamily 2 0 Q ∧ ∀ x, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target).1
  have hQeq : Q = s31qr_transportOn univ Fd₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd := by
    rw [hQe]; exact s32w_dt_pullback_eq Fd₀ Qd
  have hι₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Fd₀.ι := Fd₀.holomorphic
  have hJa : IsAnticonformalInvolution Jd₀ :=
    s32w_dt_opens_involution (puncturedOpens Pd₀) Jd₀ J₀ hd₀.involution hJd₀
  obtain ⟨W, hWapp, hWa⟩ := s31dc_involution E hE hd₀.involution
  have hWι : ∀ s : puncturedOpens Pd₀, W (Fd₀.ι s) = Fd₀.ι (Jd₀ s) := fun s => by
    rw [hWapp, ← hEι s, E.symm_apply_apply, ← hEι (Jd₀ s), hJd₀]
  -- `Q` is fixed by the conj transport along `Jd₀` (this is `hQ`)
  have hKQ : s31qr_transportOn univ Jd₀ Complex.conjCLE.toLinearMap Q = Q := by
    funext y z
    by_cases hz : z ∈ (chartAt ℂ y).target
    · rw [s31qd5_conj_transport_apply univ Jd₀ Q y hz (mem_univ _)]
      exact (hQ y z hz).symm
    · rw [s31dc_transport_off_target _ _ _ _ y hz, hQfam.1 y z hz]
  -- hence `Qd` is fixed by the conj transport along `W = E ∘ J₀ ∘ E⁻¹`, compared at the chart centres
  have hRfam : IsDiffFamily 2 0 (s31qr_transportOn univ W Complex.conjCLE.toLinearMap Qd) :=
    s31qr_transport_family univ W _ (fun x z hz _ => s31qr_involution_coordinate W hWa x hz) Qd
  have hPinv : ∀ y ∈ Fd₀.P, W y ∈ Fd₀.P := by
    intro y hy
    rw [hWapp]
    have h1 : E.symm y ∈ Pd₀ := (hEP _).2 (by rwa [E.apply_symm_apply])
    have h2 : J₀ (E.symm y) ∈ (↑Pd₀ : Set Xd₀.carrier) := by
      rw [← hd₀.Pd_invariant]; exact mem_image_of_mem J₀ h1
    exact (hEP _).1 h2
  have hfixW : s31qr_transportOn univ W Complex.conjCLE.toLinearMap Qd = Qd := by
    apply s31qd5_eq_of_centers hRfam hQdA.1
    intro y
    by_cases hyP : y ∈ Fd₀.P
    · rw [s32w_dt_cv_conj univ W Qd (mem_univ y),
        (hQdA.2.2.1 (W y) (W y) (hPinv y hyP) (mem_chart_source ℂ _)).1,
        (hQdA.2.2.1 y y hyP (mem_chart_source ℂ _)).1]
      simp
    · have hyr : y ∈ range Fd₀.ι := by
        rw [Fd₀.range_ι]; simp [hyP]
      obtain ⟨s, rfl⟩ := hyr
      have hd := s82td_tau_deriv_ne_zero Fd₀ (Fd₀.ι s) s (mem_chart_source ℂ _)
      have hLeq : (fun s => W (Fd₀.ι s)) = fun s => Fd₀.ι (Jd₀ s) := funext hWι
      have hz : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
      have key2 : s31qr_transportOn univ Fd₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_transportOn univ W Complex.conjCLE.toLinearMap Qd) s (chartAt ℂ s s) =
          s31qr_transportOn univ Fd₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd s (chartAt ℂ s s) := by
        rw [s32w_dt_cv_comp_conj_inner Fd₀.ι (⇑W) (fun s => W (Fd₀.ι s)) (fun s => rfl) Qd (hι₀m s)
            (s31qd5_involution_coordinate_center W hWa (Fd₀.ι s)), hLeq,
          ← s32w_dt_cv_comp_conj_outer Jd₀ Fd₀.ι (fun s => Fd₀.ι (Jd₀ s)) (fun s => rfl) Qd
            (s31qd5_involution_coordinate_center Jd₀ hJa s)
            (Jd₀.continuous.continuousAt.comp ((chartAt ℂ s).continuousAt_symm hz)) (hι₀m _),
          ← hQeq, hKQ]
      rw [s32w_dt_cv_id univ Fd₀.ι _ (mem_univ _), s32w_dt_cv_id univ Fd₀.ι _ (mem_univ _)] at key2
      exact mul_right_cancel₀ (pow_ne_zero 2 hd) key2
  -- the restriction of `Qd` to `S₀` (`s31qd_restriction`)
  obtain ⟨⟨q₀, hq₀⟩, hqR⟩ := s31qd_restriction F₀ hm hd₀ Fd₀ E hE hEι hEP T hT hQdA (by
    rw [show (fun y : Fd₀.X.carrier => E (J₀ (E.symm y))) = ⇑W from (funext hWapp).symm]
    exact hfixW)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT ⟨q₀, hq₀⟩
  set Tq : Xd₀.carrier → ℂ → ℂ := T ⟨q₀, hq₀⟩ with hTq
  have hQdE : Qd = s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq := hqR.symm
  -- the half inclusions
  let G₀ : C(S₀, ↥(puncturedOpens Pd₀)) :=
    ⟨fun x => ⟨ιd₀ x, s32w_double_range_off_Pd F₀ hd₀ x⟩, hd₀.embedding.continuous.subtype_mk _⟩
  let G₁ : C(S, ↥(puncturedOpens Pd₁)) :=
    ⟨fun x => ⟨ιd₁ x, s32w_double_range_off_Pd F₁ hd₁ x⟩, hd₁.embedding.continuous.subtype_mk _⟩
  have hG₀ : ∀ x, (G₀ x : Xd₀.carrier) = ιd₀ x := fun x => rfl
  have hG₁ : ∀ x, (G₁ x : Xd₁.carrier) = ιd₁ x := fun x => rfl
  have hG₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₀ :=
    s32w_dt_mdiff_into_opens (puncturedOpens Pd₀) G₀ G₀.continuous ιd₀ hd₀.holomorphic hG₀
  have hG₁m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁ :=
    s32w_dt_mdiff_into_opens (puncturedOpens Pd₁) G₁ G₁.continuous ιd₁ hd₁.holomorphic hG₁
  have hG₀e : Topology.IsOpenEmbedding G₀ :=
    (Topology.IsOpenEmbedding.of_comp_iff _ (puncturedOpens Pd₀).2.isOpenEmbedding_subtypeVal).1 hd₀.embedding
  have hG₁e : Topology.IsOpenEmbedding G₁ :=
    (Topology.IsOpenEmbedding.of_comp_iff _ (puncturedOpens Pd₁).2.isOpenEmbedding_subtypeVal).1 hd₁.embedding
  have hEm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E : Xd₀.carrier → Fd₀.X.carrier) := hE.1
  have hEsm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E.symm : Fd₀.X.carrier → Xd₀.carrier) := hE.homeomorph_symm.1
  have hpb : IsHolQuadDiff (pullbackQD F₀ q₀) := s32p_pullbackQD_isHolQuadDiff F₀ hq₀
  have hpbfam : IsDiffFamily 2 0 (pullbackQD F₀ q₀) :=
    (hpb : IsDiffFamily 2 0 (pullbackQD F₀ q₀) ∧
      ∀ x, DifferentiableOn ℂ (pullbackQD F₀ q₀ x) (chartAt ℂ x).target).1
  -- (D2a) as an equality of quadratic-differential families, compared at the chart centres
  have hD2a : pullbackQD F₀ q₀ = s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q := by
    apply s31qd5_eq_of_centers hpbfam
    · exact s31qr_transport_family univ G₀ _
        (fun x z hz _ => s31qr_coordinate_differentiable x _ hz (mem_chart_source ℂ _) (hG₀m _)) Q
    · intro p
      have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun s => E (ιd₀ s)) p :=
        (hEm _).comp p (hd₀.holomorphic p)
      have hmd' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E.symm ((fun s => E (ιd₀ s)) p) := hEsm _
      have e1 : s31qr_transportOn univ G₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q p (chartAt ℂ p p) =
          s31qr_transportOn univ (fun s => E (ιd₀ s)) (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd p (chartAt ℂ p p) := by
        rw [hQeq]
        exact s32w_dt_cv_comp univ univ G₀ Fd₀.ι (fun s => E (ιd₀ s))
          (fun s => by rw [← hEι, hG₀]) Qd (mem_univ _) (mem_univ _) (hG₀m p) (hι₀m _)
      have e2 : s31qr_transportOn univ (fun s => E (ιd₀ s)) (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Qd p
            (chartAt ℂ p p) =
          s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq p (chartAt ℂ p p) := by
        rw [hQdE]
        exact s32w_dt_cv_comp univ univ (fun s => E (ιd₀ s)) E.symm ιd₀
          (fun s => (E.symm_apply_apply _).symm) Tq (mem_univ _) (mem_univ _) hmd hmd'
      have e3 : s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Tq p (chartAt ℂ p p) =
          s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_positiveData F₀ hd₀ q₀) p (chartAt ℂ p p) := by
        rw [s32w_dt_cv_id univ ιd₀ Tq (mem_univ _), s32w_dt_cv_id univ ιd₀ _ (mem_univ _)]
        have hz : chartAt ℂ (ιd₀ p) (ιd₀ p) ∈ (chartAt ℂ (ιd₀ p)).target :=
          (chartAt ℂ (ιd₀ p)).map_source (mem_chart_source ℂ _)
        have h3c : Tq (ιd₀ p) (chartAt ℂ (ιd₀ p) (ιd₀ p)) =
            s31qr_positiveData F₀ hd₀ q₀ (ιd₀ p) (chartAt ℂ (ιd₀ p) (ιd₀ p)) :=
          h3 (ιd₀ p) _ hz
            (by rw [(chartAt ℂ (ιd₀ p)).left_inv (mem_chart_source ℂ _)]; exact ⟨p, rfl⟩)
        rw [h3c]
      have e4 : s31qr_transportOn univ ιd₀ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
            (s31qr_positiveData F₀ hd₀ q₀) p (chartAt ℂ p p) =
          s31qr_transportOn univ F₀.ι (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q₀ p (chartAt ℂ p p) := by
        unfold s31qr_positiveData
        exact s32w_dt_cv_comp univ (range ιd₀) ιd₀ (s31qr_halfReturn F₀ hd₀) F₀.ι
          (fun s => (s31qr_halfReturn_image F₀ hd₀ s).symm) q₀ (mem_univ _) ⟨p, rfl⟩
          (hd₀.holomorphic p) (s31qr_halfReturn_holomorphic F₀ hd₀ ⟨p, rfl⟩)
      rw [s32w_dt_pullback_eq F₀ q₀, e1, e2, e3, e4]
  -- the restriction of `f₁` is a Teichmüller map for the pulled-back data
  have hrel' : ∀ x, f₁ (G₀ x) = G₁ (f₀ x) := fun x => Subtype.ext (hrel (G₀ x) x rfl)
  have hTr := s32w_t324_teich_restrict hG₀e hG₀m hG₁e hG₁m hrel' hf₁.2
  refine ⟨pullbackQD F₀ q₀, s31qr_transportOn univ G₁ (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q', k,
    Submodule.mem_map.2 ⟨q₀, hq₀, rfl⟩, ?_⟩
  rw [hD2a]
  exact hTr

/-- **[stub T4e2]** The restriction of a biholomorphic map of the punctured doubles to the halves is biholomorphic. -/
theorem s32w_t324_restrict_biholo {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f₁ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hbi : IsBiholomorphic f₁)
    {f₀ : S₀ ≃ₜ S} (hrel : ∀ (y : puncturedOpens Pd₀) (x : S₀), (y : Xd₀.carrier) = ιd₀ x →
      (f₁ y : Xd₁.carrier) = ιd₁ (f₀ x)) :
    IsBiholomorphic f₀ := by
  classical
  haveI : Nonempty S₀ := inferInstance
  haveI : Nonempty S := inferInstance
  have hoff₀ : ∀ x, ιd₀ x ∉ (↑Pd₀ : Set Xd₀.carrier) := s32w_double_range_off_Pd F₀ hd₀
  have hoff₁ : ∀ x, ιd₁ x ∉ (↑Pd₁ : Set Xd₁.carrier) := s32w_double_range_off_Pd F₁ hd₁
  have hG₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : S₀ => (⟨ιd₀ x, hoff₀ x⟩ : puncturedOpens Pd₀)) :=
    s78ra_mdifferentiable_opens_codRestrict hd₀.holomorphic (puncturedOpens Pd₀) hoff₀
  have hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun y : S => (⟨ιd₁ y, hoff₁ y⟩ : puncturedOpens Pd₁)) :=
    s78ra_mdifferentiable_opens_codRestrict hd₁.holomorphic (puncturedOpens Pd₁) hoff₁
  have hval₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : puncturedOpens Pd₀ → Xd₀.carrier) :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  have hval₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : puncturedOpens Pd₁ → Xd₁.carrier) :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  have hf₁s : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₁.symm : puncturedOpens Pd₁ → puncturedOpens Pd₀) :=
    (IsBiholomorphic.homeomorph_symm hbi).1
  have hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : S₀ => (f₁ ⟨ιd₀ x, hoff₀ x⟩ : Xd₁.carrier)) :=
    hval₁.comp (hbi.1.comp hG₀)
  have hpr' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun y : S => (f₁.symm ⟨ιd₁ y, hoff₁ y⟩ : Xd₀.carrier)) :=
    hval₀.comp (hf₁s.comp hG₁)
  have hrel' : ∀ x, ιd₁ (f₀ x) = (f₁ ⟨ιd₀ x, hoff₀ x⟩ : Xd₁.carrier) := fun x => (hrel _ x rfl).symm
  have hrel'' : ∀ y, ιd₀ (f₀.symm y) = (f₁.symm ⟨ιd₁ y, hoff₁ y⟩ : Xd₀.carrier) := by
    intro y
    have h1 : f₁ ⟨ιd₀ (f₀.symm y), hoff₀ _⟩ = ⟨ιd₁ y, hoff₁ y⟩ := by
      apply Subtype.ext
      rw [← hrel' (f₀.symm y), f₀.apply_symm_apply]
    rw [← h1, f₁.symm_apply_apply]
  have he₀ : (f₀ : S₀ → S) = fun x => Function.invFun ιd₁ (f₁ ⟨ιd₀ x, hoff₀ x⟩ : Xd₁.carrier) := by
    funext x
    rw [← hrel' x, Function.leftInverse_invFun hd₁.embedding.injective]
  have he₁ : (f₀.symm : S → S₀) = fun y => Function.invFun ιd₀ (f₁.symm ⟨ιd₁ y, hoff₁ y⟩ : Xd₀.carrier) := by
    funext y
    rw [← hrel'' y, Function.leftInverse_invFun hd₀.embedding.injective]
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₀ : S₀ → S) := by
    intro x
    rw [he₀]
    exact s82lc_invFun_mdifferentiableAt hd₁.embedding.injective hd₁.holomorphic (hpr x) ⟨f₀ x, hrel' x⟩
  have hmd' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₀.symm : S → S₀) := by
    intro y
    rw [he₁]
    exact s82lc_invFun_mdifferentiableAt hd₀.embedding.injective hd₀.holomorphic (hpr' y) ⟨f₀.symm y, hrel'' y⟩
  exact ⟨hmd, f₀.symm, hmd', fun x => f₀.symm_apply_apply x, fun y => f₀.apply_symm_apply y⟩

/-- **Theorem 32.4** (book helper; `thm32_4_existence_gnm`, S32:630, renamed). -/
theorem s32w_thm32_4 {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact s82dx_thm32_2_existence_gn hex F₀ F₁ f hf
  have hm : m ≠ 0 := hmpos.ne'
  obtain ⟨Xd₀, J₀, ιd₀, Pd₀, hd₀⟩ := exists_schottkyDouble hm F₀
  obtain ⟨Xd₁, J₁, ιd₁, Pd₁, hd₁⟩ := exists_schottkyDouble hm F₁
  obtain ⟨Fd₀⟩ := s32w_t324_punctured_structure F₀ hd₀
  obtain ⟨Fd₁⟩ := s32w_t324_punctured_structure F₁ hd₁
  have hexd := s32w_t324_double_nonexc hm hex
  obtain ⟨fd, hfd, hfdQ, -⟩ := s32w_symmetric_extension hm F₀ F₁ hd₀ hd₁ f hf
  obtain ⟨fdp, hfdp⟩ := s32w_double_punctured_restrict F₀ F₁ hd₀ hd₁ hfd
  have hfdpQ : IsQCRS fdp := s32w_isQCRS_restrict_punctured hfdp hfdQ
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  haveI : ConnectedSpace (puncturedOpens Pd₁) := s32w_punctured_connectedSpace Pd₁
  obtain ⟨f₁, hhom, hcase₀⟩ := s82dx_thm32_2_existence_gn hexd Fd₀ Fd₁ fdp hfdpQ
  -- a Teichmüller map with `k = 0` is biholomorphic (`s82td_k0_biholomorphic`)
  have hcase : IsBiholomorphic f₁ ∨ ∃ (Q : puncturedOpens Pd₀ → ℂ → ℂ) (Q' : puncturedOpens Pd₁ → ℂ → ℂ) (k : ℝ),
      0 < k ∧ IsAdmissibleTeichmullerMap Fd₀ f₁ Q Q' k := by
    rcases hcase₀ with hbi | ⟨Q, Q', k, hT⟩
    · exact Or.inl hbi
    · rcases hT.2.k_nonneg.lt_or_eq with hk | hk
      · exact Or.inr ⟨Q, Q', k, hk, hT⟩
      · rw [← hk] at hT
        exact Or.inl (s82td_k0_biholomorphic hT.2)
  have hsym : (∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (f₁ y' : Xd₁.carrier) = J₁ (f₁ y)) ∧
      (fun y : puncturedOpens Pd₀ => (f₁ y : Xd₁.carrier)) '' {y | (y : Xd₀.carrier) ∈ range ιd₀} =
        range ιd₁ := by
    rcases hcase with hbi | ⟨Q, Q', k, -, hT⟩
    · exact s32w_t324_biholo_commutes hm hex F₀ F₁ hd₀ hd₁ Fd₀ f hfd hfdQ hfdp hbi hhom
    · exact s82rc_eq32_3_teichmuller_commutes_reflection hm hex F₀ F₁ hd₀ hd₁ Fd₀ f hf hfd hfdp hT hhom
  obtain ⟨f₀, hrel⟩ := s32w_t324_restrict_homeo F₀ F₁ hd₀ hd₁ f₁ hsym.2
  -- the half inclusions and the descent of the homotopy (W2(a))
  let G₀ : C(S₀, puncturedOpens Pd₀) :=
    ⟨fun x => ⟨ιd₀ x, s32w_double_range_off_Pd F₀ hd₀ x⟩, hd₀.embedding.continuous.subtype_mk _⟩
  let G₁ : C(S, puncturedOpens Pd₁) :=
    ⟨fun x => ⟨ιd₁ x, s32w_double_range_off_Pd F₁ hd₁ x⟩, hd₁.embedding.continuous.subtype_mk _⟩
  have hv : ∀ x, (fdp : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) (G₀ x) = G₁ (f x) := fun x =>
    Subtype.ext (by
      show (fdp (G₀ x) : Xd₁.carrier) = ιd₁ (f x)
      rw [hfdp]; exact hfd.1 x)
  have hh : ∀ x, (f₁ : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) (G₀ x) = G₁ (f₀ x) := fun x =>
    Subtype.ext (hrel (G₀ x) x rfl)
  have hH : ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) :=
    s32w_descend_homotopy F₁ hd₁ (G₁ := G₁) (fun x => rfl) hv hh hhom
  refine ⟨f₀, hH, ?_⟩
  rcases hcase with hbi | ⟨Q, Q', k, hk, hT⟩
  · exact Or.inl (s32w_t324_restrict_biholo F₀ F₁ hd₀ hd₁ hbi hrel)
  · right
    let Jd₀ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀ :=
      J₀.subtype (fun x => by
        show x ∉ (↑Pd₀ : Set Xd₀.carrier) ↔ J₀ x ∉ (↑Pd₀ : Set Xd₀.carrier)
        have key : ∀ y, y ∈ (↑Pd₀ : Set Xd₀.carrier) → J₀ y ∈ (↑Pd₀ : Set Xd₀.carrier) := fun y hy => by
          rw [← hd₀.Pd_invariant]; exact mem_image_of_mem J₀ hy
        exact ⟨fun hx hJx => hx (by have := key _ hJx; rwa [hd₀.involution.1] at this),
          fun hx hx' => hx (key _ hx')⟩)
    have hJd₀ : ∀ y, (Jd₀ y : Xd₀.carrier) = J₀ y := fun y => rfl
    exact s32w_t324_restrict_teich hm F₀ F₁ hd₀ hd₁ Fd₀ Jd₀ hJd₀ hT hk
      (s32w_t324_Q_symm F₀ F₁ hd₀ hd₁ Fd₀ Jd₀ hJd₀ hT hk hsym.1) hrel

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Theorem 32.4**: let `S₀`, `S₁` be non-exceptional surfaces of type `(g, n, m)` and
`f : S₀ → S₁` a quasiconformal map.  Then the homotopy class of `f` contains a Teichmüller map whose
associated quadratic differential is admissible (or a conformal map).  (Method of Ahlfors.) -/
theorem thm32_4_existence_gnm {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsAdmissibleTeichmullerMap F₀ f₀ q q' k) := by
  exact s32w_thm32_4 hex F₀ F₁ f hf

end RelocatedS32

end LiZhongQC
