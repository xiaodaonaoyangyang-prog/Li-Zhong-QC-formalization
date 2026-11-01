import LiZhongQC.Ch07.S26_TeichmullerUniqueness
import LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# §27 Teichmüller 存在性定理 — Teichmüller's existence theorem

* §27.1 marked Riemann surfaces `(S, f)`, their equivalence and the Teichmüller space `T(S₀)`
                                                       — `MarkedRS`, `MarkedRS.Equiv`, `TeichSpace`
* normalized lifts `f̃` (`f̃(0) = 0, f̃(1) = 1, f̃(∞) = ∞`): existence after adjusting the
  projection, uniqueness; Theorem 27.1 (equivalence ⟺ equal boundary values), (27.1)–(27.3)
                                                       — `IsNormalizedLift`, `thm27_1`
* standard systems of generators (27.4), (27.5); the Fricke space `F(S₀)` and its coordinates
  `(σ₁, τ₁, λ₁, …, σ_{2g-2}, τ_{2g-2}, λ_{2g-2}) ∈ ℝ^{6g-6}`, (27.6)–(27.14)
                                                       — `StandardGenerators`, `frickeCoordinates`,
                                                         `IsFrickeCoords`, `frickeSpace`
* §27.2 the maps `Φ : T̃(S₀) → T(S₀)`, `Ψ : T(S₀) → F(S₀)`; Lemma 27.1 (`Ψ∘Φ` is continuous and
  injective), (27.15)–(27.17); Lemma 27.2 (`F(S₀)` is connected); Lemma 27.3 (no boundary point of
  `Ψ∘Φ(T̃(S₀))` lies in `F(S₀)`); `Ψ∘Φ` is a homeomorphism (Brouwer); Theorem 27.2 (existence)
                                                       — `IsDeformationPoint`, `lemma27_1_*`,
                                                         `lemma27_2_connected`, `lemma27_3_boundary`

## What is proved here

* `isQCRS_refl`, that the identity is quasiconformal: its local expression is
  `chartAt x ∘ (chartAt x).symm`, which is the identity on the chart target, so §7's
  `isKQC_one_of_conformal` applies.  (It used to inherit a `sorry` through that lemma; it has been
  axiom-clean since Theorem 1.1 was proved.)
* `hyperbolic_normal_form`: the normal form of a hyperbolic `γ ∈ SL(2, ℝ)` at its fixed points, and
  the fact that `(σ, τ, λ)` determines `γ` up to sign, by direct computation with the fixed-point
  formulas.

Everything else needs the normalized lifts of §13, the Fricke coordinates, or Brouwer's invariance
of domain for `Ψ∘Φ`.

The bijection `Φ : T̃(S₀) → T(S₀)` of §27.2 (`teichSpace_deformation_bijection`) is stated and proved in
`LiZhongQC.Lemmas.UniformizedTeichmuller` (moved there by leader decision, 2026-10-12): its existence half
is Hamilton's theorem (§36), which this chapter cannot import.

Theorem 27.2 (`thm27_2_existence`) is stated and proved in `LiZhongQC.Lemmas.UniformizedTeichmuller` (moved
there by leader decision, 2026-10-13): its proof is Hamilton's theorem (§36) on the uniformized surfaces, which
this chapter cannot import.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-! ## §27.1 Marked Riemann surfaces -/

/-- **§27.1 (标记 Riemann 曲面).**  A Riemann surface `X` of genus `g > 1` marked by a quasiconformal
homeomorphism `f : S₀ → X` (for closed surfaces an orientation preserving homeomorphism would
suffice; quasiconformality is required for uniformity with the open case). -/
structure MarkedRS where
  X : ClosedRS.{u}
  marking : S₀ ≃ₜ X.carrier
  qc : IsQCRS marking

variable {S₀}

/-- §27.1: two marked surfaces `(S, f)`, `(S₁, f₁)` are equivalent if there is a conformal map
`φ : S → S₁` with `φ ≃ f₁ ∘ f⁻¹` (i.e. `φ ∘ f ≃ f₁`). -/
def MarkedRS.Equiv (m₁ m₂ : MarkedRS S₀) : Prop :=
  ∃ c : m₁.X.carrier ≃ₜ m₂.X.carrier, IsBiholomorphic c ∧
    ContinuousMap.Homotopic ((m₁.marking.trans c : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
      (m₂.marking : C(S₀, m₂.X.carrier))

/-- §27.1: for `S = S₁`, `(S, f) ~ (S, f₁)` iff `f ≃ f₁`.

**Correction.**  Only the implication `f ≃ f₁ → (X, f) ~ (X, f₁)` is kept: the converse was **false**
(genus `2`, `f = id`, `f₁ = ι` the hyperelliptic involution: `(X, id) ~ (X, ι)` via `c = ι`, but `ι` is
not homotopic to the identity). -/
theorem markedRS_equiv_same_surface (X : ClosedRS.{u}) (f f₁ : S₀ ≃ₜ X.carrier) (hf : IsQCRS f)
    (hf₁ : IsQCRS f₁) {g : ℕ} (hg : 1 < g) (hX : HasGenus X.carrier g) :
    ContinuousMap.Homotopic (f : C(S₀, X.carrier)) (f₁ : C(S₀, X.carrier)) →
      MarkedRS.Equiv ⟨X, f, hf⟩ ⟨X, f₁, hf₁⟩ := by
  have _ := hg
  have _ := hX
  -- take `c = id`
  intro hhom
  exact ⟨Homeomorph.refl X.carrier, isBiholomorphic_id, hhom⟩

/-- §27.1: the relation `~` is an equivalence relation. -/
theorem markedRS_equiv_equivalence : Equivalence (MarkedRS.Equiv (S₀ := S₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- reflexivity: take the identity of `X`
    intro m
    exact ⟨Homeomorph.refl m.X.carrier, isBiholomorphic_id, ContinuousMap.Homotopic.refl _⟩
  · -- symmetry: take `c⁻¹`, and compose the homotopy with `c⁻¹`
    rintro m₁ m₂ ⟨c, hc, hh⟩
    refine ⟨c.symm, hc.homeomorph_symm, ?_⟩
    rw [coe_homeomorph_trans] at hh ⊢
    have hcancel :
        (c.symm : C(m₂.X.carrier, m₁.X.carrier)).comp (c : C(m₁.X.carrier, m₂.X.carrier))
          = ContinuousMap.id m₁.X.carrier := by
      ext x
      exact c.symm_apply_apply x
    have h1 := (ContinuousMap.Homotopic.refl
      (c.symm : C(m₂.X.carrier, m₁.X.carrier))).comp hh
    rw [← ContinuousMap.comp_assoc, hcancel, ContinuousMap.id_comp] at h1
    exact h1.symm
  · -- transitivity: compose the conformal maps, and the homotopies
    rintro m₁ m₂ m₃ ⟨c₁, hc₁, hh₁⟩ ⟨c₂, hc₂, hh₂⟩
    refine ⟨c₁.trans c₂, hc₂.comp hc₁, ?_⟩
    rw [coe_homeomorph_trans] at hh₁ hh₂
    rw [coe_homeomorph_trans, coe_homeomorph_trans]
    have h1 := (ContinuousMap.Homotopic.refl
      (c₂ : C(m₂.X.carrier, m₃.X.carrier))).comp hh₁
    rw [← ContinuousMap.comp_assoc] at h1
    exact h1.trans hh₂

variable (S₀)

/-- **§27.1 (Teichmüller 空间).**  The Teichmüller space `T(S₀) = {[S, f] : f : S₀ → S}` of equivalence
classes of marked Riemann surfaces. -/
def TeichSpace : Type (u + 1) := Quot (MarkedRS.Equiv (S₀ := S₀))

variable {S₀}

/-- The point `[S₀, id]` of `T(S₀)`. -/
def TeichSpace.basePoint [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hid : IsQCRS (Homeomorph.refl S₀)) : TeichSpace S₀ :=
  Quot.mk _ ⟨⟨S₀⟩, Homeomorph.refl S₀, hid⟩

/-- §27.1: the identity is quasiconformal (`1`-quasiconformal). -/
theorem isQCRS_refl [IsManifold 𝓘(ℂ) ω S₀] : IsQCRS (Homeomorph.refl S₀) := by
  refine ⟨1, le_rfl, fun x => ?_⟩
  -- the local expression of the identity is `φ ∘ φ⁻¹`, the identity on the chart target
  have hD : IsOpen (localMapDomain (Homeomorph.refl S₀) x) := by
    simpa [localMapDomain] using
      (chartAt ℂ x).symm.isOpen_inter_preimage (chartAt ℂ x).open_source
  have heq : ∀ z ∈ localMapDomain (Homeomorph.refl S₀) x,
      localMapExpr (Homeomorph.refl S₀) x z = id z := by
    intro z hz
    simp only [localMapDomain, Set.mem_inter_iff] at hz
    simpa [localMapExpr] using (chartAt ℂ x).right_inv hz.1
  refine isKQC_one_of_conformal hD ⟨differentiableOn_id.congr heq, ?_, rfl⟩
  intro z hz w hw hzw
  rw [heq z hz, heq w hw] at hzw
  exact hzw

/-! ### Normalized lifts -/

/-- §27.1 (规范化提升).  `F : ℍ → ℍ` is a normalized lift of `f : S₀ → S` with respect to the
universal coverings `p₀ : ℍ → S₀`, `p : ℍ → S`: a lift whose boundary correspondence `G` fixes
`0`, `1` and `∞`. -/
def IsNormalizedLift {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p₀ : UpperHalfPlane → S₀)
    (p : UpperHalfPlane → S) (f : S₀ → S) (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (G : ExtPlane → ExtPlane) : Prop :=
  IsLift p₀ p f F ∧ IsHomeoExtension (liftToC F) upperHalf upperHalf G ∧
    G ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ G ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
    G extInf = extInf

/-- The projection `p ∘ ψ⁻¹` for the Möbius transformation `ψ` of `ℍ` given by `A ∈ SL(2, ℝ)`. -/
def adjustProjection {S : Type u} (p : UpperHalfPlane → S) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (τ : UpperHalfPlane) : S :=
  p (A⁻¹ • τ)

/-- The conjugate group `A Γ A⁻¹`. -/
def conjGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  Γ.map (MulAut.conj A).toMonoidHom

/-- The action `τ ↦ A • τ` of `A ∈ SL(2, ℝ)` on `ℍ` is holomorphic. -/
theorem s27t_mdifferentiable_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => A • τ) := by
  have h := UpperHalfPlane.mdifferentiable_smul
    (g := Matrix.SpecialLinearGroup.mapGL ℝ A) (by simp)
  have e : (fun τ : UpperHalfPlane => A • τ) =
      (fun τ : UpperHalfPlane => (Matrix.SpecialLinearGroup.mapGL ℝ A) • τ) := by
    funext τ
    rfl
  rw [e]
  exact h

/-- §27.1: `(ℍ, p ∘ ψ⁻¹)` is again a universal covering of `S`, with covering group `ψ Γ ψ⁻¹`. -/
theorem adjustProjection_isUniformization {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsUniformization (conjGroup Γ A) (adjustProjection p A) := by
  obtain ⟨hcov, hhol, hsurj, hfib⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- covering: compose with the homeomorphism `τ ↦ A⁻¹ • τ`
    exact hcov.comp_homeomorph (Homeomorph.smul A⁻¹)
  · -- holomorphic
    exact hhol.comp (s27t_mdifferentiable_smul A⁻¹)
  · -- surjective
    intro x
    obtain ⟨τ, rfl⟩ := hsurj x
    refine ⟨A • τ, ?_⟩
    show p (A⁻¹ • A • τ) = p τ
    rw [inv_smul_smul]
  · -- the fibres are the orbits of `A Γ A⁻¹`
    intro τ₁ τ₂
    show p (A⁻¹ • τ₁) = p (A⁻¹ • τ₂) ↔ _
    rw [hfib]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨A * γ * A⁻¹, ⟨γ, hγ, by simp [MulAut.conj_apply]⟩, ?_⟩
      rw [mul_smul, mul_smul, h, smul_inv_smul]
    · rintro ⟨δ, ⟨γ, hγ, hγδ⟩, h⟩
      refine ⟨γ, hγ, ?_⟩
      have hδ : δ = A * γ * A⁻¹ := by
        rw [← hγδ]
        simp [MulAut.conj_apply]
      rw [hδ, mul_smul, mul_smul] at h
      rw [← h, inv_smul_smul]

/-- The lift of a homeomorphism of `ℍ`, viewed as a map of `ℂ`, maps `ℍ` onto `ℍ` (as in `h36t_image_extRealLine`). -/
theorem h36q_liftToC_image (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : liftToC F '' upperHalf = upperHalf := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : 0 < z.im := hz
    show 0 < (liftToC F z).im
    unfold liftToC
    simp only [hz', ↓reduceDIte]
    exact (F _).coe_im_pos
  · intro hw
    refine ⟨(F.symm (UpperHalfPlane.mk w hw) : ℂ), (F.symm _).coe_im_pos, ?_⟩
    unfold liftToC
    simp only [(F.symm _).coe_im_pos, ↓reduceDIte]
    show ((F (F.symm (UpperHalfPlane.mk w hw)) : UpperHalfPlane) : ℂ) = w
    rw [F.apply_symm_apply]

/-- On `ℍ` a homeomorphic extension of `liftToC F` is `F`. -/
theorem h36t_ext_coe {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) (τ : UpperHalfPlane) :
    G ((τ : ℂ) : ExtPlane) = ((F τ : ℂ) : ExtPlane) := by
  rw [hG.1 _ τ.coe_im_pos]
  unfold liftToC
  simp only [τ.coe_im_pos, ↓reduceDIte]

/-- The Möbius action of `g ∈ SL(2, ℝ)` on `ℂ̄` restricts to its action on `ℍ`. -/
theorem h36t_mobiusSL_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    mobiusSL (slRealToComplex g) ((τ : ℂ) : ExtPlane) = (((g • τ : UpperHalfPlane) : ℂ) : ExtPlane) := by
  rw [k24_mobiusSL_real, mobiusExt_coe (h36t_den_ne g τ), h36t_coe_smul]
  rfl

/-- `ℝ̂` is the frontier of `ℍ` in `ℂ̄`. -/
theorem h36t_extRealLine_eq_frontier : extRealLine = frontier (toExt upperHalf) := by
  rw [scExt_frontier_toExt_upperHalf]
  rfl

/-- `ℝ̂` lies in the closure of `ℍ` in `ℂ̄`. -/
theorem h36t_extRealLine_subset_closure : extRealLine ⊆ closure (toExt upperHalf) := by
  rw [h36t_extRealLine_eq_frontier]
  exact frontier_subset_closure

/-- A homeomorphic extension of `liftToC F` maps `ℝ̂` onto `ℝ̂`. -/
theorem h36t_image_extRealLine {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) : G '' extRealLine = extRealLine := by
  have himg : liftToC F '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : 0 < z.im := hz
      show 0 < (liftToC F z).im
      unfold liftToC
      simp only [hz', ↓reduceDIte]
      exact (F _).coe_im_pos
    · intro hw
      refine ⟨(F.symm (UpperHalfPlane.mk w hw) : ℂ), (F.symm _).coe_im_pos, ?_⟩
      unfold liftToC
      simp only [(F.symm _).coe_im_pos, ↓reduceDIte]
      show ((F (F.symm (UpperHalfPlane.mk w hw)) : UpperHalfPlane) : ℂ) = w
      rw [F.apply_symm_apply]
  rw [h36t_extRealLine_eq_frontier]
  exact IsHomeoExtension.image_frontier isOpen_upperHalf isOpen_upperHalf himg hG

/-- Post-composition with `A ∈ SL(2, ℝ)`: if `G` extends `liftToC F`, then `A ∘ G` extends `liftToC (A ∘ F)`
(`IsHomeoExtension.comp_homeomorph` with the homeomorphism `mobiusSL A` of `ℂ̄`). -/
theorem s27l_ext_smul {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsHomeoExtension (liftToC (F.trans (Homeomorph.smul A))) upperHalf upperHalf
      (mobiusSL (slRealToComplex A) ∘ G) := by
  have hmaps : MapsTo (liftToC F) upperHalf upperHalf := fun z hz => by
    rw [← h36q_liftToC_image F]
    exact mem_image_of_mem _ hz
  have he : ∀ w ∈ upperHalf, k24_mobiusSLHomeo (slRealToComplex A) (w : ExtPlane) =
      ((liftToC (fun τ : UpperHalfPlane => A • τ) w : ℂ) : ExtPlane) := by
    intro w hw
    have hw' : 0 < w.im := hw
    rw [k24_mobiusSLHomeo_coe, h23l_liftToC_eq _ hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    exact h36t_mobiusSL_coe A ⟨w, hw'⟩
  have himg : k24_mobiusSLHomeo (slRealToComplex A) '' toExt upperHalf = toExt upperHalf := by
    rw [k24_mobiusSLHomeo_coe, k24_mobiusSL_real]
    exact mobiusExt_image_toExt_upperHalf (by rw [k24_det_realR]; exact one_pos)
  have h := hG.comp_homeomorph hmaps (k24_mobiusSLHomeo (slRealToComplex A)) he himg
  refine s13x_th_isHomeoExtension_congr h fun z hz => ?_
  show liftToC (fun τ : UpperHalfPlane => A • τ) (liftToC F z) = liftToC (F.trans (Homeomorph.smul A)) z
  rw [h23l_liftToC_eq F hz, h23l_liftToC_coe, h23l_liftToC_eq _ hz]
  rfl

/-- A homeomorphic extension of `liftToC F` fixing `∞` maps every real point to a real point (it maps `ℝ̂` onto `ℝ̂`
and is injective on the closed half-plane). -/
theorem s27l_ext_real {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) (hinf : G extInf = extInf) (x : ℝ) :
    ∃ y : ℝ, G ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := by
  have hx : ((x : ℂ) : ExtPlane) ∈ extRealLine := Or.inl ⟨(x : ℂ), Complex.ofReal_im x, rfl⟩
  have hGx : G ((x : ℂ) : ExtPlane) ∈ extRealLine := by
    rw [← h36t_image_extRealLine hG]
    exact mem_image_of_mem G hx
  rcases hGx with ⟨z, hz, hzx⟩ | hGx
  · refine ⟨z.re, ?_⟩
    rw [← hzx]
    congr 1
    exact Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hz)
  · exfalso
    have h1 : G ((x : ℂ) : ExtPlane) = G extInf := by rw [hinf]; exact mem_singleton_iff.1 hGx
    have h2 := hG.2.2.1 (h36t_extRealLine_subset_closure hx)
      (h36t_extRealLine_subset_closure (Or.inr rfl)) h1
    exact OnePoint.coe_ne_infty _ h2

/-- Every point of `ℝ̂` is sent to `∞` by some `B ∈ SL(2, ℝ)`: `B = 1` for `∞`, and `B = (0, -1; 1, -r)`
(`z ↦ -1/(z - r)`) for `r ∈ ℝ`. -/
theorem s27l_exists_to_infty {ξ : ExtPlane} (hξ : ξ ∈ extRealLine) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, mobiusSL (slRealToComplex B) ξ = extInf := by
  rcases hξ with ⟨z, hz, rfl⟩ | hξ
  · have hz' : z.im = 0 := hz
    have hdet : (!![0, -1; 1, -z.re] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      rw [Matrix.det_fin_two_of]
      ring
    set B : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![0, -1; 1, -z.re], hdet⟩ with hB
    have b10 : B 1 0 = 1 := rfl
    have b11 : B 1 1 = -z.re := rfl
    refine ⟨B, ?_⟩
    rw [k24_mobiusSL_real]
    apply mobiusExt_coe_of_eq_zero
    rw [b10, b11]
    apply Complex.ext <;> simp [hz']
  · exact ⟨1, by rw [mem_singleton_iff.1 hξ, k24_slReal_one, k24_mobiusSL_one]⟩

/-- For real `a < b`, some `C ∈ SL(2, ℝ)` (the affine map `z ↦ (z - a)/(b - a)`) sends `a`, `b`, `∞` to `0`, `1`,
`∞`. -/
theorem s27l_exists_affine {a b : ℝ} (hab : a < b) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      mobiusSL (slRealToComplex C) ((a : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      mobiusSL (slRealToComplex C) ((b : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
      mobiusSL (slRealToComplex C) extInf = extInf := by
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = b - a :=
    ⟨Real.sqrt (b - a), Real.sqrt_pos.2 (sub_pos.2 hab), Real.sq_sqrt (sub_pos.2 hab).le⟩
  have hdet : (!![1 / s, -a / s; 0, s] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  set C : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![1 / s, -a / s; 0, s], hdet⟩ with hC
  have c00 : C 0 0 = 1 / s := rfl
  have c01 : C 0 1 = -a / s := rfl
  have c10 : C 1 0 = 0 := rfl
  have c11 : C 1 1 = s := rfl
  have hden : ∀ x : ℝ, C 1 0 * x + C 1 1 ≠ 0 := fun x => by
    rw [c10, c11, zero_mul, zero_add]
    exact hs0.ne'
  refine ⟨C, ?_, ?_, ?_⟩
  · rw [k24_mobiusSL_real, mobiusExt_ofReal_coe (hden a), c00, c01, c10, c11]
    congr 1
    have e : (1 / s * a + -a / s) / (0 * a + s) = 0 := by
      rw [show 1 / s * a + -a / s = 0 by ring, zero_div]
    rw [e, Complex.ofReal_zero]
  · rw [k24_mobiusSL_real, mobiusExt_ofReal_coe (hden b), c00, c01, c10, c11]
    congr 1
    have e : (1 / s * b + -a / s) / (0 * b + s) = 1 := by
      rw [zero_mul, zero_add, div_eq_one_iff_eq hs0.ne']
      field_simp
      nlinarith [hs2]
    rw [e, Complex.ofReal_one]
  · rw [k24_mobiusSL_real]
    exact mobiusExt_infty_of_eq (by rw [c10, Complex.ofReal_zero])

/-- §27.1: a quasiconformal map `f : S₀ → S` need not have a normalized lift for given projections,
but after replacing `p` by `p ∘ ψ⁻¹` for a suitable Möbius transformation `ψ` of `ℍ`, a normalized
lift exists.

**Correction.**  The hypotheses `[IsManifold 𝓘(ℂ) ω S₀]`, `[IsManifold 𝓘(ℂ) ω S]` were missing:
without holomorphically compatible charts (`[IsManifold 𝓘(ℂ) ω _]`) `IsQCRS`/`IsKQCRS` and
`IsUniformization` do not control the lift, and the statement was **false** (a copy of `ℍ` charted by the
radial stretches `w ↦ (w - x)|w - x|`, with a Lipschitz self-map having no homeomorphic extension, was a
counterexample). -/
theorem exists_normalizedLift {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S₀]
    [IsManifold 𝓘(ℂ) ω S] [T2Space S₀] [ConnectedSpace S₀] [T2Space S] [ConnectedSpace S]
    {Γ₀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} {p : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀)
    (hp : IsUniformization Γ p) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
      IsNormalizedLift p₀ (adjustProjection p A) f F G := by
  obtain ⟨K, hK⟩ := hf
  -- a lift `F₀` of `f`, `K`-q.c. (`h23l_lift_isKQC`), with a boundary extension `G₀` (Theorem 13.3)
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (f (p₀ UpperHalfPlane.I))
  obtain ⟨F₀, hF₀, -⟩ := exists_lift hp₀ hp f UpperHalfPlane.I τ₁ hτ₁
  obtain ⟨G₀, hG₀⟩ := thm13_3_boundary_correspondence isJordanDomain_upperHalf isJordanDomain_upperHalf
    ⟨K, h23l_lift_isKQC hp₀ hp hK hF₀⟩ (h36q_liftToC_image F₀)
  -- move `G₀ ∞ ∈ ℝ̂` to `∞` by some `B ∈ SL(2, ℝ)`
  have hinfR : G₀ extInf ∈ extRealLine := by
    rw [← h36t_image_extRealLine hG₀]
    exact mem_image_of_mem G₀ (Or.inr rfl)
  obtain ⟨B, hB⟩ := s27l_exists_to_infty hinfR
  have hF₁ : IsLift p₀ (adjustProjection p B) f (F₀.trans (Homeomorph.smul B)) := fun τ => by
    show p (B⁻¹ • B • F₀ τ) = f (p₀ τ)
    rw [inv_smul_smul]
    exact hF₀ τ
  have hF₁K := h23l_lift_isKQC hp₀ (adjustProjection_isUniformization hp B) hK hF₁
  have hG₁ := s27l_ext_smul hG₀ B
  -- the boundary values `h` of `B ∘ G₀` on `ℝ` are increasing (sense preservation, `b4_qs_monotone`)
  choose h hh using s27l_ext_real hG₁ hB
  have hmono := (b4_qs_monotone ⟨hF₁K, h36q_liftToC_image _, _, hG₁, hB, hh⟩).1
  -- normalize by the affine `C` sending `h 0 < h 1` to `0 < 1`: `A = C B`
  obtain ⟨C, hC0, hC1, hCinf⟩ := s27l_exists_affine (hmono zero_lt_one)
  have hh0 := hh 0
  have hh1 := hh 1
  rw [Complex.ofReal_zero] at hh0
  rw [Complex.ofReal_one] at hh1
  refine ⟨C * B, F₀.trans (Homeomorph.smul (C * B)), mobiusSL (slRealToComplex (C * B)) ∘ G₀,
    fun τ => ?_, s27l_ext_smul hG₀ (C * B), ?_, ?_, ?_⟩
  · show p ((C * B)⁻¹ • (C * B) • F₀ τ) = f (p₀ τ)
    rw [inv_smul_smul]
    exact hF₀ τ
  · show mobiusSL (slRealToComplex (C * B)) (G₀ ((0 : ℂ) : ExtPlane)) = ((0 : ℂ) : ExtPlane)
    rw [k24_slReal_mul, k24_mobiusSL_mul]
    rw [show mobiusSL (slRealToComplex B) (G₀ ((0 : ℂ) : ExtPlane)) = (((h 0 : ℝ) : ℂ) : ExtPlane) from hh0]
    exact hC0
  · show mobiusSL (slRealToComplex (C * B)) (G₀ ((1 : ℂ) : ExtPlane)) = ((1 : ℂ) : ExtPlane)
    rw [k24_slReal_mul, k24_mobiusSL_mul]
    rw [show mobiusSL (slRealToComplex B) (G₀ ((1 : ℂ) : ExtPlane)) = (((h 1 : ℝ) : ℂ) : ExtPlane) from hh1]
    exact hC1
  · show mobiusSL (slRealToComplex (C * B)) (G₀ extInf) = extInf
    rw [k24_slReal_mul, k24_mobiusSL_mul, hB]
    exact hCinf

/-- A real Möbius transformation fixing `∞`, `0` and `1` is the identity, on `ℂ̄` and on `ℍ` (`c = 0` from `∞`, then
`b = 0` from `0` and `a = d` from `1`). -/
theorem s27l_fix3 {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hinf : mobiusSL (slRealToComplex δ) extInf = extInf)
    (h0 : mobiusSL (slRealToComplex δ) ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    (h1 : mobiusSL (slRealToComplex δ) ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    (∀ q, mobiusSL (slRealToComplex δ) q = q) ∧ ∀ w : UpperHalfPlane, δ • w = w := by
  rw [k24_mobiusSL_real] at hinf h0 h1
  have hdetC : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := k24_det_real δ
  have hc : (δ 1 0 : ℂ) = 0 := (mem_mobiusFixedPoints_infty_iff _ _ _ _).1 hinf
  have e0 := (mem_mobiusFixedPoints_coe_iff hdetC 0).1 h0
  have e1 := (mem_mobiusFixedPoints_coe_iff hdetC 1).1 h1
  have hb : (δ 0 1 : ℂ) = 0 := by linear_combination -e0
  have hda : (δ 1 1 : ℂ) = δ 0 0 := by linear_combination e1 - hc + hb
  have ha : (δ 0 0 : ℂ) ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, zero_sub, hb, zero_mul, neg_zero] at hdetC
    exact zero_ne_one hdetC
  refine ⟨fun q => ?_, fun w => ?_⟩
  · rw [k24_mobiusSL_real]
    induction q using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq hc
    | coe z =>
      have hden : (δ 1 0 : ℂ) * z + δ 1 1 ≠ 0 := by
        rw [hc, zero_mul, zero_add, hda]
        exact ha
      rw [mobiusExt_coe hden, mobiusFn, hc, hb, hda, zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ ha]
  · apply UpperHalfPlane.ext
    show ((δ • w : UpperHalfPlane) : ℂ) = w
    rw [h36t_coe_smul, hc, hb, hda, zero_mul, zero_add, add_zero]
    exact mul_div_cancel_left₀ _ ha

/-- If `F₂ = m ∘ F₁` on `ℍ`, the extensions satisfy `G₂ = m ∘ G₁` on the closed half-plane (both sides are continuous
there and agree on the dense subset `ℍ`). -/
theorem s27l_ext_eqOn_smul {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁)
    (hG₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf G₂) {m : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hm : ∀ τ, F₂ τ = m • F₁ τ) :
    EqOn G₂ (fun x => mobiusSL (slRealToComplex m) (G₁ x)) (closure (toExt upperHalf)) := by
  refine Set.EqOn.of_subset_closure (s := toExt upperHalf) ?_ hG₂.2.1
    ((k22_t_continuous _).comp_continuousOn hG₁.2.1) subset_closure subset_rfl
  rintro _ ⟨z, hz, rfl⟩
  have e : ((z : ℂ) : ExtPlane) = (((UpperHalfPlane.mk z hz : UpperHalfPlane) : ℂ) : ExtPlane) := rfl
  show G₂ ((z : ℂ) : ExtPlane) = mobiusSL (slRealToComplex m) (G₁ ((z : ℂ) : ExtPlane))
  rw [e, h36t_ext_coe hG₂, h36t_ext_coe hG₁, hm, h36t_mobiusSL_coe]

/-- The points `0`, `1` and `∞` lie in the closed upper half-plane `closure (toExt ℍ)` of `ℂ̄`. -/
theorem s27l_mem_closure_01inf : ((0 : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) ∧
    ((1 : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) ∧ extInf ∈ closure (toExt upperHalf) :=
  ⟨h36t_extRealLine_subset_closure (Or.inl ⟨0, Complex.zero_im, rfl⟩),
    h36t_extRealLine_subset_closure (Or.inl ⟨1, Complex.one_im, rfl⟩),
    h36t_extRealLine_subset_closure (Or.inr rfl)⟩

/-- §27.1: for a fixed projection `p₀`, the normalized lift of `f` is unique (for whatever
projections `p₁`, `p₂` of `S`): `f̃₂ ∘ f̃₁⁻¹` is a conformal self-map of `ℍ` fixing `0, 1, ∞`.

**Correction.**  The hypothesis `[IsManifold 𝓘(ℂ) ω S]` was missing: with an atlas of radial stretches
on `S`, `p₁ = id` and `p₂` a bi-Lipschitz shear fixing `0, 1, ∞` are uniformizations whose normalized
lifts differ, and the statement was **false**.

**Correction (2026-09-26).**  The conclusion `G₁ = G₂` was **false**: `IsNormalizedLift` pins the extension `G`
down only on the closed upper half-plane, and its values elsewhere are arbitrary.  It is now `G₁ = G₂` on
`closure ℍ` (all that `thm27_1` and the Fricke coordinates use). -/
theorem normalizedLift_unique {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [T2Space S₀]
    [ConnectedSpace S₀] [T2Space S] [ConnectedSpace S] {Γ₀ Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} {p₁ p₂ : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀)
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) (f : S₀ ≃ₜ S)
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (h₁ : IsNormalizedLift p₀ p₁ f F₁ G₁) (h₂ : IsNormalizedLift p₀ p₂ f F₂ G₂) :
    F₁ = F₂ ∧ EqOn G₁ G₂ (closure (toExt upperHalf)) := by
  have _ := hp₀
  obtain ⟨hF₁, hG₁, h0₁, h1₁, hinf₁⟩ := h₁
  obtain ⟨hF₂, hG₂, h0₂, h1₂, hinf₂⟩ := h₂
  -- `Φ = F₂ ∘ F₁⁻¹` lifts the identity of `S` through `p₁`, `p₂`, so it is `1`-q.c., hence Möbius: `F₂ = m ∘ F₁`
  have hΦ : IsLift p₁ p₂ (Homeomorph.refl S) (F₁.symm.trans F₂) := fun τ => by
    show p₂ (F₂ (F₁.symm τ)) = p₁ τ
    rw [hF₂, ← hF₁, F₁.apply_symm_apply]
  have hK1 : IsKQCRS (Homeomorph.refl S) 1 := (isKQCRS_one_iff _).2 isBiholomorphic_id
  obtain ⟨m, hm⟩ := utm_eq_smul_of_isKQC_one _ (h23l_lift_isKQC hp₁ hp₂ hK1 hΦ)
  have hm' : ∀ τ, F₂ τ = m • F₁ τ := fun τ => by
    have h := hm (F₁ τ)
    rwa [Homeomorph.trans_apply, F₁.symm_apply_apply] at h
  have hEq := s27l_ext_eqOn_smul hG₁ hG₂ hm'
  -- the boundary map of `m` fixes `0`, `1`, `∞`, so `m` acts as the identity
  obtain ⟨hc0, hc1, hcinf⟩ := s27l_mem_closure_01inf
  have e0 : G₂ ((0 : ℂ) : ExtPlane) = mobiusSL (slRealToComplex m) (G₁ ((0 : ℂ) : ExtPlane)) := hEq hc0
  have e1 : G₂ ((1 : ℂ) : ExtPlane) = mobiusSL (slRealToComplex m) (G₁ ((1 : ℂ) : ExtPlane)) := hEq hc1
  have einf : G₂ extInf = mobiusSL (slRealToComplex m) (G₁ extInf) := hEq hcinf
  rw [h0₁, h0₂] at e0
  rw [h1₁, h1₂] at e1
  rw [hinf₁, hinf₂] at einf
  obtain ⟨hid, hidH⟩ := s27l_fix3 einf.symm e0.symm e1.symm
  refine ⟨Homeomorph.ext fun τ => ?_, fun x hx => ?_⟩
  · rw [hm', hidH]
  · have h : G₂ x = mobiusSL (slRealToComplex m) (G₁ x) := hEq hx
    rw [h, hid]

/-- The attracting fixed point `σ` of a hyperbolic `γ ∈ SL(2, ℝ)` (`|tr γ| > 2`): for `c ≠ 0` it is
`((a - d) + sgn(a + d) √((a+d)² - 4))/(2c)`; for `c = 0` it is `∞` when `|a| > 1` and `b/(d - a)`
otherwise.  (Junk value for non-hyperbolic `γ`.) -/
def attractingFixedPoint (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ExtPlane :=
  if γ 1 0 = 0 then (if 1 < |γ 0 0| then extInf else (((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) : ExtPlane))
  else ((((γ 0 0 - γ 1 1 + Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) /
    (2 * γ 1 0) : ℝ) : ℂ) : ExtPlane)

/-- The repelling fixed point `τ` of a hyperbolic `γ ∈ SL(2, ℝ)`. -/
def repellingFixedPoint (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ExtPlane :=
  if γ 1 0 = 0 then (if 1 < |γ 0 0| then (((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) : ExtPlane) else extInf)
  else ((((γ 0 0 - γ 1 1 - Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) /
    (2 * γ 1 0) : ℝ) : ℂ) : ExtPlane)

/-- The multiplier `λ > 1` of a hyperbolic transformation: the square of the larger eigenvalue
`((|a + d| + √((a+d)² - 4))/2)²`. -/
def multiplier (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  ((|γ 0 0 + γ 1 1| + Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) / 2) ^ 2

/-- Sign and square-root facts for a hyperbolic trace `|t| > 2`. -/
theorem hnf_sign_sqrt {t : ℝ} (ht : 2 < |t|) :
    (Real.sign t = -1 ∨ Real.sign t = 1) ∧ Real.sign t ^ 2 = 1 ∧ Real.sign t * |t| = t ∧
      0 < Real.sqrt (t ^ 2 - 4) ∧ Real.sqrt (t ^ 2 - 4) ^ 2 = t ^ 2 - 4 := by
  have h4 : 0 < t ^ 2 - 4 := by nlinarith [sq_abs t, abs_nonneg t]
  have ht0 : t ≠ 0 := by
    rintro rfl
    norm_num at ht
  have hs := Real.sign_apply_eq_of_ne_zero t ht0
  refine ⟨hs, ?_, ?_, Real.sqrt_pos.2 h4, Real.sq_sqrt h4.le⟩
  · rcases hs with h | h <;> rw [h] <;> norm_num
  · rcases lt_or_gt_of_ne ht0 with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]
      ring
    · rw [Real.sign_of_pos h, abs_of_pos h]
      ring

/-- The determinant of an element of `SL(2, ℝ)` in entries. -/
theorem hnf_sl2_det (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

/-- The algebra of the fixed points for `c ≠ 0`: with `2cσ = a - d + εs`, `2cτ = a - d - εs`, both are
fixed, `a - cτ = ε(|t| + s)/2 ≠ 0`, and `λ (a - cσ) = a - cτ` for `λ = ((|t| + s)/2)²`. -/
theorem hnf_core_ne {a b c d σ τ ε s : ℝ} (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (hε2 : ε ^ 2 = 1) (hεt : ε * |a + d| = a + d) (hs : 0 < s) (hs2 : s ^ 2 = (a + d) ^ 2 - 4)
    (hσ : 2 * c * σ = a - d + ε * s) (hτ : 2 * c * τ = a - d - ε * s) :
    c * σ ^ 2 + (d - a) * σ - b = 0 ∧ c * τ ^ 2 + (d - a) * τ - b = 0 ∧ a - c * τ ≠ 0 ∧
      ((|a + d| + s) / 2) ^ 2 * (a - c * σ) = a - c * τ := by
  have h4c : ∀ x : ℝ, 4 * c * (c * x ^ 2 + (d - a) * x - b) =
      (2 * c * x) ^ 2 + 2 * (d - a) * (2 * c * x) - 4 * b * c := fun x => by ring
  have h4 : (4 : ℝ) * c ≠ 0 := mul_ne_zero four_ne_zero hc
  have hε0 : ε ≠ 0 := by
    rintro rfl
    norm_num at hε2
  have hq : a - c * τ = ε * ((|a + d| + s) / 2) := by linear_combination -hτ / 2 - hεt / 2
  have hp : a - c * σ = ε * ((|a + d| - s) / 2) := by linear_combination -hσ / 2 - hεt / 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : 4 * c * (c * σ ^ 2 + (d - a) * σ - b) = 0 := by
      rw [h4c, hσ]
      linear_combination s ^ 2 * hε2 + hs2 + 4 * hdet
    exact (mul_eq_zero.1 h).resolve_left h4
  · have h : 4 * c * (c * τ ^ 2 + (d - a) * τ - b) = 0 := by
      rw [h4c, hτ]
      linear_combination s ^ 2 * hε2 + hs2 + 4 * hdet
    exact (mul_eq_zero.1 h).resolve_left h4
  · rw [hq]
    exact mul_ne_zero hε0 (by linarith [abs_nonneg (a + d)] : 0 < (|a + d| + s) / 2).ne'
  · rw [hp, hq]
    linear_combination (ε * (|a + d| + s) / 8) * sq_abs (a + d) - (ε * (|a + d| + s) / 8) * hs2

/-- `γ(z) - σ = (a - cσ)(z - σ)/(cz + d)` at a fixed point `σ`. -/
theorem hnf_mobiusFn_sub_of_fixed {a b c d σ z : ℂ} (hf : c * σ ^ 2 + (d - a) * σ - b = 0)
    (hz : c * z + d ≠ 0) : mobiusFn a b c d z - σ = (a - c * σ) * (z - σ) / (c * z + d) := by
  rw [mobiusFn, eq_div_iff hz, sub_mul, div_mul_cancel₀ _ hz]
  linear_combination -hf

/-- The cross-ratio normal form at two fixed points `σ, τ`. -/
theorem hnf_cross_ratio {a b c d σ τ L z : ℂ} (hfσ : c * σ ^ 2 + (d - a) * σ - b = 0)
    (hfτ : c * τ ^ 2 + (d - a) * τ - b = 0) (hq : a - c * τ ≠ 0) (hL : L * (a - c * σ) = a - c * τ)
    (hz : c * z + d ≠ 0) :
    (z - σ) / (z - τ) = L * ((mobiusFn a b c d z - σ) / (mobiusFn a b c d z - τ)) := by
  rw [hnf_mobiusFn_sub_of_fixed hfσ hz, hnf_mobiusFn_sub_of_fixed hfτ hz,
    div_div_div_cancel_right₀ hz, ← mul_div_assoc, ← mul_assoc L, hL, mul_div_mul_left _ _ hq]

/-- An upper-triangular Möbius map `z ↦ (az + b)/d` with `ad = 1` is `z ↦ a²z + ab`. -/
theorem hnf_mobiusFn_of_c_zero {a b d : ℂ} (had : a * d = 1) (z : ℂ) :
    mobiusFn a b 0 d z = a ^ 2 * z + a * b := by
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
  rw [mobiusFn, zero_mul, zero_add, div_eq_iff hd]
  linear_combination -(a * z + b) * had

/-- For `c ≠ 0` the attracting fixed point is finite. -/
theorem hnf_attr_exists {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) :
    ∃ σ : ℝ, attractingFixedPoint γ = ((σ : ℂ) : ExtPlane) :=
  ⟨_, by rw [attractingFixedPoint, if_neg hc]⟩

/-- For `c ≠ 0` the repelling fixed point is finite. -/
theorem hnf_rep_exists {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) :
    ∃ τ : ℝ, repellingFixedPoint γ = ((τ : ℂ) : ExtPlane) :=
  ⟨_, by rw [repellingFixedPoint, if_neg hc]⟩

/-- For `c ≠ 0`, the attracting fixed point `σ` satisfies `2cσ = a - d + sgn(a + d) √((a+d)² - 4)`. -/
theorem hnf_attr_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) {σ : ℝ}
    (h : attractingFixedPoint γ = ((σ : ℂ) : ExtPlane)) :
    2 * γ 1 0 * σ = γ 0 0 - γ 1 1 + Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4) := by
  rw [attractingFixedPoint, if_neg hc] at h
  rw [← Complex.ofReal_injective (OnePoint.coe_injective h)]
  field_simp

/-- For `c ≠ 0`, the repelling fixed point `τ` satisfies `2cτ = a - d - sgn(a + d) √((a+d)² - 4)`. -/
theorem hnf_rep_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) {τ : ℝ}
    (h : repellingFixedPoint γ = ((τ : ℂ) : ExtPlane)) :
    2 * γ 1 0 * τ = γ 0 0 - γ 1 1 - Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4) := by
  rw [repellingFixedPoint, if_neg hc] at h
  rw [← Complex.ofReal_injective (OnePoint.coe_injective h)]
  field_simp

/-- The fixed points for `c = 0`: `∞` and `b/(d - a)`, in the order given by `|a| > 1`. -/
theorem hnf_fixed_of_eq_zero {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 = 0) :
    (1 < |γ 0 0| → attractingFixedPoint γ = extInf ∧
      repellingFixedPoint γ = (((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) : ExtPlane)) ∧
    (¬ 1 < |γ 0 0| → attractingFixedPoint γ = (((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) : ExtPlane) ∧
      repellingFixedPoint γ = extInf) :=
  ⟨fun ha => ⟨by rw [attractingFixedPoint, if_pos hc, if_pos ha],
      by rw [repellingFixedPoint, if_pos hc, if_pos ha]⟩,
    fun ha => ⟨by rw [attractingFixedPoint, if_pos hc, if_neg ha],
      by rw [repellingFixedPoint, if_pos hc, if_neg ha]⟩⟩

/-- For `ad = 1` and `|a + d| > 2`: `a ≠ d`, and `(|a + d| + √((a + d)² - 4))/2` is the larger of
`|a|, |d|`. -/
theorem hnf_core_eq {a d : ℝ} (had : a * d = 1) (ht : 2 < |a + d|) :
    d - a ≠ 0 ∧ (1 < |a| → (|a + d| + Real.sqrt ((a + d) ^ 2 - 4)) / 2 = |a|) ∧
      (¬ 1 < |a| → (|a + d| + Real.sqrt ((a + d) ^ 2 - 4)) / 2 = |d|) := by
  have key : ∀ x y : ℝ, x * y = 1 → 1 < |x| →
      (|x + y| + Real.sqrt ((x + y) ^ 2 - 4)) / 2 = |x| := by
    intro x y hxy hx
    rw [show (x + y) ^ 2 - 4 = (x - y) ^ 2 by linear_combination 4 * hxy, Real.sqrt_sq_eq_abs]
    rcases lt_abs.1 hx with h | h
    · have hy : 0 < y := by nlinarith
      have hy1 : y < 1 := by nlinarith
      rw [abs_of_pos (by linarith : 0 < x + y), abs_of_pos (by linarith : 0 < x - y),
        abs_of_pos (by linarith : 0 < x)]
      ring
    · have hy : y < 0 := by nlinarith
      have hy1 : -1 < y := by nlinarith
      rw [abs_of_neg (by linarith : x + y < 0), abs_of_neg (by linarith : x - y < 0),
        abs_of_neg (by linarith : x < 0)]
      ring
  have hprod : |a| * |d| = 1 := by rw [← abs_mul, had, abs_one]
  refine ⟨fun h => ?_, key a d had, fun ha => ?_⟩
  · have hd : d = a := by linarith
    rw [hd] at hprod ht
    have h1 : |a| = 1 := by nlinarith [abs_nonneg a]
    rw [show a + a = 2 * a by ring, abs_mul, h1] at ht
    norm_num at ht
  · have hlt : |a| < 1 := by
      refine lt_of_le_of_ne (not_lt.1 ha) fun h1 => ?_
      rw [h1, one_mul] at hprod
      have := abs_add_le a d
      linarith
    have hd : 1 < |d| := by nlinarith [abs_nonneg a, abs_nonneg d]
    rw [add_comm a d]
    exact key d a (by rw [mul_comm]; exact had) hd

/-- Uniqueness for `c = 0`: the finite fixed point `b/(d - a)` and `a²` determine `γ` up to sign. -/
theorem hnf_unique_eq {a b c d a' b' c' d' : ℝ} (had : a * d = 1) (had' : a' * d' = 1)
    (hda : d - a ≠ 0) (hp : b' / (d' - a') = b / (d - a)) (hsq : a' ^ 2 = a ^ 2) (hc : c = 0)
    (hc' : c' = 0) :
    (a' = a ∧ b' = b ∧ c' = c ∧ d' = d) ∨ (a' = -a ∧ b' = -b ∧ c' = -c ∧ d' = -d) := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  subst hc hc'
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · subst h
    have hd : d' = d := mul_left_cancel₀ ha (had'.trans had.symm)
    subst hd
    exact Or.inl ⟨rfl, (div_left_inj' hda).1 hp, rfl, rfl⟩
  · subst h
    have hd : d' = -d := by
      have h1 : a * (-d') = a * d := by linear_combination had' - had
      have := mul_left_cancel₀ ha h1
      linarith
    subst hd
    rw [show -d - -a = -(d - a) by ring, div_neg, ← neg_div] at hp
    have := (div_left_inj' hda).1 hp
    exact Or.inr ⟨rfl, by linarith, by simp, rfl⟩

/-- Uniqueness for `c ≠ 0`: the fixed points and the multiplier determine `εγ`, `ε = sign tr γ`. -/
theorem hnf_unique_ne {a b c d a' b' c' d' σ τ ε ε' s s' : ℝ}
    (hdet : a * d - b * c = 1) (hdet' : a' * d' - b' * c' = 1) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hε2 : ε ^ 2 = 1) (hε2' : ε' ^ 2 = 1) (hεt : ε * |a + d| = a + d)
    (hεt' : ε' * |a' + d'| = a' + d') (hs : 0 < s) (hs' : 0 < s') (hs2 : s ^ 2 = (a + d) ^ 2 - 4)
    (hs2' : s' ^ 2 = (a' + d') ^ 2 - 4)
    (hσ : 2 * c * σ = a - d + ε * s) (hτ : 2 * c * τ = a - d - ε * s)
    (hσ' : 2 * c' * σ = a' - d' + ε' * s') (hτ' : 2 * c' * τ = a' - d' - ε' * s')
    (hlam : ((|a' + d'| + s') / 2) ^ 2 = ((|a + d| + s) / 2) ^ 2) :
    ε' * a' = ε * a ∧ ε' * b' = ε * b ∧ ε' * c' = ε * c ∧ ε' * d' = ε * d := by
  have hu : |a' + d'| + s' = |a + d| + s := by
    have h := (pow_left_inj₀ (by linarith [abs_nonneg (a' + d')]) (by linarith [abs_nonneg (a + d)])
      two_ne_zero).1 hlam
    linarith
  have hprod : ∀ v w : ℝ, v ^ 2 = w ^ 2 - 4 → (|w| - v) * (|w| + v) = 4 := by
    intro v w hv
    linear_combination sq_abs w - hv
  have hdiff : |a' + d'| - s' = |a + d| - s := by
    have h1 := hprod s (a + d) hs2
    have h2 := hprod s' (a' + d') hs2'
    rw [hu] at h2
    exact mul_right_cancel₀ (by linarith [abs_nonneg (a + d)] : 0 < |a + d| + s).ne'
      (h2.trans h1.symm)
  have hss : s' = s := by linarith
  have hct : ε * c * (σ - τ) = s := by linear_combination (ε / 2) * (hσ - hτ) + s * hε2
  have hct' : ε' * c' * (σ - τ) = s := by
    rw [← hss]
    linear_combination (ε' / 2) * (hσ' - hτ') + s' * hε2'
  have hστ : σ - τ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hct
    linarith
  have hC : ε' * c' = ε * c := mul_right_cancel₀ hστ (hct'.trans hct.symm)
  have h1 : 2 * (ε * c) * σ + 2 * (ε * d) = |a + d| + s := by
    linear_combination ε * hσ + (s + |a + d|) * hε2 - ε * hεt
  have h1' : 2 * (ε' * c') * σ + 2 * (ε' * d') = |a' + d'| + s' := by
    linear_combination ε' * hσ' + (s' + |a' + d'|) * hε2' - ε' * hεt'
  have hD : ε' * d' = ε * d := by linear_combination (h1' - h1) / 2 - σ * hC + hu / 2
  have hA : ε' * a' = ε * a := by
    linear_combination hD + (σ + τ) * hC - ε' / 2 * (hσ' + hτ') + ε / 2 * (hσ + hτ)
  have hf := (hnf_core_ne hdet hc hε2 hεt hs hs2 hσ hτ).1
  have hf' := (hnf_core_ne hdet' hc' hε2' hεt' hs' hs2' hσ' hτ').1
  refine ⟨hA, ?_, hC, hD⟩
  linear_combination -ε' * hf' + ε * hf + σ ^ 2 * hC + σ * (hD - hA)

/-- `ε'x' = εx` for `ε, ε' = ±1` means `x' = ±x` with one common sign. -/
theorem hnf_signs {ε ε' a b c d a' b' c' d' : ℝ} (hε : ε = -1 ∨ ε = 1) (hε' : ε' = -1 ∨ ε' = 1)
    (h : ε' * a' = ε * a ∧ ε' * b' = ε * b ∧ ε' * c' = ε * c ∧ ε' * d' = ε * d) :
    (a' = a ∧ b' = b ∧ c' = c ∧ d' = d) ∨ (a' = -a ∧ b' = -b ∧ c' = -c ∧ d' = -d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
  · exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Two elements of `SL(2, ℝ)` whose entries agree, or all agree up to sign, are equal up to sign. -/
theorem hnf_sl2_eq_or_eq_neg {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : (γ' 0 0 = γ 0 0 ∧ γ' 0 1 = γ 0 1 ∧ γ' 1 0 = γ 1 0 ∧ γ' 1 1 = γ 1 1) ∨
      (γ' 0 0 = -γ 0 0 ∧ γ' 0 1 = -γ 0 1 ∧ γ' 1 0 = -γ 1 0 ∧ γ' 1 1 = -γ 1 1)) :
    γ' = γ ∨ γ' = -γ := by
  rcases h with ⟨e00, e01, e10, e11⟩ | ⟨e00, e01, e10, e11⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j
    exacts [e00, e01, e10, e11]
  · right
    ext i j
    fin_cases i <;> fin_cases j
    exacts [e00, e01, e10, e11]

/-- §27.1: a hyperbolic `w = γ(z)` with attracting fixed point `σ` and repelling fixed point `τ`
(both finite) satisfies `(z - σ)/(z - τ) = λ (w - σ)/(w - τ)`, `λ > 1`; when `σ = ∞`,
`w - τ = λ(z - τ)`, and when `τ = ∞`, `w - σ = (z - σ)/λ`.  Conversely `γ` is determined by
`(σ, τ, λ)`.

Proof: write `γ = (a b; c d)`, `ε = sgn(a + d)` and `s = √((a + d)² - 4) > 0`.
* `c ≠ 0`: `σ` and `τ` are the roots of `cx² + (d - a)x - b`, with `a - cσ = ε(|a + d| - s)/2` and
  `a - cτ = ε(|a + d| + s)/2`, so `λ(a - cσ) = a - cτ`.  Since
  `γ(z) - σ = (a - cσ)(z - σ)/(cz + d)`, and likewise for `τ`, the cross-ratio form follows.
* `c = 0`: `ad = 1` and `γ(z) = a²z + ab`; the finite fixed point is `b/(d - a)`, and `λ` is `a²`
  if `|a| > 1` and `d²` otherwise.
* Uniqueness: `λ` determines `|a + d|` and `s`.  For `c ≠ 0`, the identities `c(σ - τ) = εs`,
  `2ε(cσ + d) = |a + d| + s`, `a - d = c(σ + τ)` and `b = cσ² + (d - a)σ` determine `εγ` from
  `(σ, τ, λ)`.  For `c = 0`, the finite fixed point and `a²` determine `γ` up to sign.  A mixed pair
  (`c = 0` for one element, `c ≠ 0` for the other) is impossible, because exactly one of the two
  has a fixed point at `∞`. -/
theorem hyperbolic_normal_form {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|) :
    1 < multiplier γ ∧ attractingFixedPoint γ ≠ repellingFixedPoint γ ∧
    (∀ σ τ : ℝ, attractingFixedPoint γ = ((σ : ℂ) : ExtPlane) →
      repellingFixedPoint γ = ((τ : ℂ) : ExtPlane) → ∀ z : ℂ, γ 1 0 * z + γ 1 1 ≠ 0 → z ≠ τ →
        mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z ≠ τ →
        (z - σ) / (z - τ) = multiplier γ * ((mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z - σ) /
          (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z - τ))) ∧
    (∀ τ : ℝ, attractingFixedPoint γ = extInf → repellingFixedPoint γ = ((τ : ℂ) : ExtPlane) →
      ∀ z : ℂ, mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z - τ = multiplier γ * (z - τ)) ∧
    (∀ σ : ℝ, attractingFixedPoint γ = ((σ : ℂ) : ExtPlane) → repellingFixedPoint γ = extInf →
      ∀ z : ℂ, mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z - σ = (z - σ) / multiplier γ) ∧
    ∀ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, 2 < |γ' 0 0 + γ' 1 1| →
      attractingFixedPoint γ' = attractingFixedPoint γ → repellingFixedPoint γ' = repellingFixedPoint γ →
      multiplier γ' = multiplier γ → γ' = γ ∨ γ' = -γ := by
  have hdet := hnf_sl2_det γ
  obtain ⟨hsg, hε2, hεt, hs, hs2⟩ := hnf_sign_sqrt hγ
  have hmul : multiplier γ =
      ((|γ 0 0 + γ 1 1| + Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) / 2) ^ 2 := rfl
  have hzero : γ 1 0 = 0 → γ 0 0 * γ 1 1 = 1 := fun hc => by
    rw [hc, mul_zero, sub_zero] at hdet
    exact hdet
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `λ > 1`
    rw [hmul]
    exact one_lt_pow₀ (by linarith) two_ne_zero
  · -- the two fixed points differ
    by_cases hc : γ 1 0 = 0
    · obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      by_cases ha : 1 < |γ 0 0|
      · rw [(h1 ha).1, (h1 ha).2]
        exact OnePoint.infty_ne_coe _
      · rw [(h2 ha).1, (h2 ha).2]
        exact OnePoint.coe_ne_infty _
    · obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
      obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
      have e1 := hnf_attr_eq hc hσ
      have e2 := hnf_rep_eq hc hτ
      rw [hσ, hτ]
      intro h
      have hστ : σ = τ := Complex.ofReal_injective (OnePoint.coe_injective h)
      subst hστ
      have hε0 : Real.sign (γ 0 0 + γ 1 1) ≠ 0 := by
        intro h0
        rw [h0] at hε2
        norm_num at hε2
      have h0 : Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4) = 0 := by linarith
      rcases mul_eq_zero.1 h0 with h0 | h0
      · exact hε0 h0
      · linarith
  · -- both fixed points finite
    intro σ τ hσ hτ z hz _ _
    by_cases hc : γ 1 0 = 0
    · exfalso
      obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      by_cases ha : 1 < |γ 0 0|
      · rw [(h1 ha).1] at hσ
        exact OnePoint.infty_ne_coe _ hσ
      · rw [(h2 ha).2] at hτ
        exact OnePoint.infty_ne_coe _ hτ
    · obtain ⟨f1, f2, hq, hL⟩ :=
        hnf_core_ne hdet hc hε2 hεt hs hs2 (hnf_attr_eq hc hσ) (hnf_rep_eq hc hτ)
      rw [← hmul] at hL
      exact hnf_cross_ratio (by exact_mod_cast f1) (by exact_mod_cast f2) (by exact_mod_cast hq)
        (by exact_mod_cast hL) hz
  · -- attracting point at `∞`
    intro τ hσ hτ z
    by_cases hc : γ 1 0 = 0
    · obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      by_cases ha : 1 < |γ 0 0|
      · have had := hzero hc
        obtain ⟨hda, hlama, -⟩ := hnf_core_eq had hγ
        rw [(h1 ha).2] at hτ
        have hτ' : τ * (γ 1 1 - γ 0 0) = γ 0 1 := by
          rw [← Complex.ofReal_injective (OnePoint.coe_injective hτ)]
          exact div_mul_cancel₀ _ hda
        have hm : multiplier γ = γ 0 0 ^ 2 := by rw [hmul, hlama ha, sq_abs]
        have hτc : (τ : ℂ) * ((γ 1 1 : ℂ) - (γ 0 0 : ℂ)) = (γ 0 1 : ℂ) := by exact_mod_cast hτ'
        have hadc : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) = 1 := by exact_mod_cast had
        rw [hm, hc, Complex.ofReal_zero, hnf_mobiusFn_of_c_zero hadc]
        push_cast
        linear_combination (-(γ 0 0 : ℂ)) * hτc + (τ : ℂ) * hadc
      · rw [(h2 ha).1] at hσ
        exact absurd hσ (OnePoint.coe_ne_infty _)
    · obtain ⟨σ, hσ'⟩ := hnf_attr_exists hc
      rw [hσ'] at hσ
      exact absurd hσ (OnePoint.coe_ne_infty _)
  · -- repelling point at `∞`
    intro σ hσ hτ z
    by_cases hc : γ 1 0 = 0
    · obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      by_cases ha : 1 < |γ 0 0|
      · rw [(h1 ha).2] at hτ
        exact absurd hτ (OnePoint.coe_ne_infty _)
      · have had := hzero hc
        obtain ⟨hda, -, hlamd⟩ := hnf_core_eq had hγ
        rw [(h2 ha).1] at hσ
        have hσ' : σ * (γ 1 1 - γ 0 0) = γ 0 1 := by
          rw [← Complex.ofReal_injective (OnePoint.coe_injective hσ)]
          exact div_mul_cancel₀ _ hda
        have hm : multiplier γ = γ 1 1 ^ 2 := by rw [hmul, hlamd ha, sq_abs]
        have hd : γ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one had
        have hσc : (σ : ℂ) * ((γ 1 1 : ℂ) - (γ 0 0 : ℂ)) = (γ 0 1 : ℂ) := by exact_mod_cast hσ'
        have hadc : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) = 1 := by exact_mod_cast had
        have hdc : (γ 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
        rw [hm, hc, Complex.ofReal_zero, hnf_mobiusFn_of_c_zero hadc]
        push_cast
        rw [eq_div_iff (pow_ne_zero 2 hdc)]
        linear_combination (z * ((γ 0 0 : ℂ) * (γ 1 1 : ℂ) + 1) + (γ 0 1 : ℂ) * (γ 1 1 : ℂ) - σ) * hadc -
          (γ 1 1 : ℂ) * hσc
    · obtain ⟨τ, hτ'⟩ := hnf_rep_exists hc
      rw [hτ'] at hτ
      exact absurd hτ (OnePoint.coe_ne_infty _)
  · -- uniqueness up to sign
    intro γ' hγ' hA hR hM
    have hdet' := hnf_sl2_det γ'
    obtain ⟨hsg', hε2', hεt', hs', hs2'⟩ := hnf_sign_sqrt hγ'
    have hmul' : multiplier γ' =
        ((|γ' 0 0 + γ' 1 1| + Real.sqrt ((γ' 0 0 + γ' 1 1) ^ 2 - 4)) / 2) ^ 2 := rfl
    by_cases hc : γ 1 0 = 0 <;> by_cases hc' : γ' 1 0 = 0
    · -- both upper triangular
      have had := hzero hc
      have had' : γ' 0 0 * γ' 1 1 = 1 := by
        rw [hc', mul_zero, sub_zero] at hdet'
        exact hdet'
      obtain ⟨hda, hlama, hlamd⟩ := hnf_core_eq had hγ
      obtain ⟨-, hlama', hlamd'⟩ := hnf_core_eq had' hγ'
      obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      obtain ⟨h1', h2'⟩ := hnf_fixed_of_eq_zero hc'
      by_cases ha : 1 < |γ 0 0|
      · have ha' : 1 < |γ' 0 0| := by
          by_contra ha'
          rw [(h1 ha).1, (h2' ha').1] at hA
          exact OnePoint.coe_ne_infty _ hA
        rw [(h1 ha).2, (h1' ha').2] at hR
        have hp := Complex.ofReal_injective (OnePoint.coe_injective hR)
        rw [hmul, hmul', hlama ha, hlama' ha', sq_abs, sq_abs] at hM
        exact hnf_sl2_eq_or_eq_neg (hnf_unique_eq had had' hda hp hM hc hc')
      · have ha' : ¬ 1 < |γ' 0 0| := by
          intro ha'
          rw [(h2 ha).1, (h1' ha').1] at hA
          exact OnePoint.infty_ne_coe _ hA
        rw [(h2 ha).1, (h2' ha').1] at hA
        have hp := Complex.ofReal_injective (OnePoint.coe_injective hA)
        rw [hmul, hmul', hlamd ha, hlamd' ha', sq_abs, sq_abs] at hM
        have hd : γ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one had
        have hM' : γ' 0 0 ^ 2 = γ 0 0 ^ 2 := by
          refine mul_right_cancel₀ (pow_ne_zero 2 hd) ?_
          linear_combination (-(γ' 0 0 ^ 2)) * hM + (γ' 0 0 * γ' 1 1 + 1) * had' -
            (γ 0 0 * γ 1 1 + 1) * had
        exact hnf_sl2_eq_or_eq_neg (hnf_unique_eq had had' hda hp hM' hc hc')
    · -- `γ` upper triangular, `γ'` not
      exfalso
      obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
      obtain ⟨σ', hσ'⟩ := hnf_attr_exists hc'
      obtain ⟨τ', hτ'⟩ := hnf_rep_exists hc'
      by_cases ha : 1 < |γ 0 0|
      · rw [(h1 ha).1, hσ'] at hA
        exact OnePoint.coe_ne_infty _ hA
      · rw [(h2 ha).2, hτ'] at hR
        exact OnePoint.coe_ne_infty _ hR
    · -- `γ'` upper triangular, `γ` not
      exfalso
      obtain ⟨h1', h2'⟩ := hnf_fixed_of_eq_zero hc'
      obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
      obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
      by_cases ha' : 1 < |γ' 0 0|
      · rw [(h1' ha').1, hσ] at hA
        exact OnePoint.infty_ne_coe _ hA
      · rw [(h2' ha').2, hτ] at hR
        exact OnePoint.infty_ne_coe _ hR
    · -- both with `c ≠ 0`
      obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
      obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
      rw [hσ] at hA
      rw [hτ] at hR
      rw [hmul, hmul'] at hM
      exact hnf_sl2_eq_or_eq_neg (hnf_signs hsg hsg'
        (hnf_unique_ne hdet hdet' hc hc' hε2 hε2' hεt hεt' hs hs' hs2 hs2'
          (hnf_attr_eq hc hσ) (hnf_rep_eq hc hτ) (hnf_attr_eq hc' hA) (hnf_rep_eq hc' hR) hM))

/-- The fixed point set of a Fuchsian group in `ℝ̂ = ℝ ∪ {∞}` (fixed points of the elements
`≠ ±I`). -/
def fuchsianFixedPoints (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℝ :=
  {x | ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0}

/-- `-1 ∈ SL(2, ℝ)` acts trivially on `ℍ`. -/
theorem s27g_neg_one_smul (τ : UpperHalfPlane) : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
  apply UpperHalfPlane.ext
  rw [h36t_coe_smul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  push_cast
  field_simp
  ring

/-- **Freeness**: the covering group of a uniformization acts freely (`γ • τ = τ` makes `τ ↦ γ • τ` a lift of `p`
through `p` fixing `τ`, hence the identity, so `γ = ±1` by `utm_sl2_eq_of_bounded_displacement`). -/
theorem s27g_actsFreely {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ActsFreely Γ := by
  intro γ hγ τ hτ
  have hcomp : p ∘ (fun z : UpperHalfPlane => γ • z) = p ∘ id := by
    funext z
    exact ((hp.2.2.2 z (γ • z)).2 ⟨γ, hγ, rfl⟩).symm
  have heq : (fun z : UpperHalfPlane => γ • z) = id :=
    hp.1.eq_of_comp_eq (continuous_const_smul γ) continuous_id hcomp τ hτ
  exact utm_sl2_eq_of_bounded_displacement γ (C := 0) fun z => by
    rw [show γ • z = z from congrFun heq z, dist_self]

/-- An elliptic `γ` (`|tr γ| < 2`) fixes a point of `ℍ`, namely `(a - d)/(2c) + i √(4 - (a+d)²)/(2|c|)`. -/
theorem s27g_elliptic_fixed {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : |γ 0 0 + γ 1 1| < 2) :
    ∃ τ : UpperHalfPlane, γ • τ = τ := by
  have hdet := hnf_sl2_det γ
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  have hsq : (γ 0 0 + γ 1 1) ^ 2 < 4 := by nlinarith
  have hc : γ 1 0 ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero, sub_zero] at hdet
    nlinarith [sq_nonneg (γ 0 0 - γ 1 1)]
  have h4 : 0 < 4 - (γ 0 0 + γ 1 1) ^ 2 := by linarith
  set s := Real.sqrt (4 - (γ 0 0 + γ 1 1) ^ 2) with hs
  have hs2 : s ^ 2 = 4 - (γ 0 0 + γ 1 1) ^ 2 := Real.sq_sqrt h4.le
  have hspos : 0 < s := Real.sqrt_pos.2 h4
  have hcabs : 0 < |γ 1 0| := abs_pos.2 hc
  set x := (γ 0 0 - γ 1 1) / (2 * γ 1 0) with hx
  set y := s / (2 * |γ 1 0|) with hy
  have hy0 : 0 < y := div_pos hspos (by positivity)
  have hxe : 2 * γ 1 0 * x = γ 0 0 - γ 1 1 := by
    rw [hx]
    field_simp
  have hye : 4 * γ 1 0 ^ 2 * y ^ 2 = s ^ 2 := by
    rw [hy, div_pow, mul_pow, sq_abs]
    field_simp
    ring
  refine ⟨⟨⟨x, y⟩, hy0⟩, ?_⟩
  apply UpperHalfPlane.ext
  rw [h36t_coe_smul, div_eq_iff (h36t_den_ne γ _)]
  apply Complex.ext
  · simp
    have key : 4 * γ 1 0 * (γ 0 0 * x + γ 0 1 - (x * (γ 1 0 * x + γ 1 1) - y * (γ 1 0 * y))) = 0 := by
      linear_combination (-(2 * γ 1 0 * x - (γ 0 0 - γ 1 1))) * hxe + hye + hs2 - 4 * hdet
    have h4c : 4 * γ 1 0 ≠ 0 := mul_ne_zero four_ne_zero hc
    have := (mul_eq_zero.1 key).resolve_left h4c
    linarith
  · simp
    linear_combination (-y) * hxe

/-- A covering group of a compact surface is not contained in `{±1}`: otherwise the compact set meeting every orbit
(`utm_exists_compact_translate`) would contain every point of `ℍ`, although `Im` is unbounded on `ℍ`. -/
theorem s27g_exists_ne_one {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp
  obtain ⟨M, hM⟩ := (hK.image UpperHalfPlane.continuous_im).bddAbove
  have hpos : 0 < max M 0 + 1 := by positivity
  set z : UpperHalfPlane := ⟨⟨0, max M 0 + 1⟩, hpos⟩ with hz
  obtain ⟨γ, hγ, hγz⟩ := hKz z
  have hfix : γ • z = z := by
    by_cases h1 : γ = 1
    · rw [h1, one_smul]
    · rw [hcon γ hγ h1]
      exact s27g_neg_one_smul z
  rw [hfix] at hγz
  have h1 : z.im ≤ M := hM ⟨z, hγz, rfl⟩
  have h2 : z.im = max M 0 + 1 := rfl
  linarith [le_max_left M 0]

/-- The entries of a conjugate `h γ h⁻¹` in `SL(2, ℝ)`. -/
theorem s27g_conj_apply (h γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (h * γ * h⁻¹) 0 0 = (h 0 0 * γ 0 0 + h 0 1 * γ 1 0) * h 1 1 - (h 0 0 * γ 0 1 + h 0 1 * γ 1 1) * h 1 0 ∧
    (h * γ * h⁻¹) 0 1 = -((h 0 0 * γ 0 0 + h 0 1 * γ 1 0) * h 0 1) + (h 0 0 * γ 0 1 + h 0 1 * γ 1 1) * h 0 0 ∧
    (h * γ * h⁻¹) 1 0 = (h 1 0 * γ 0 0 + h 1 1 * γ 1 0) * h 1 1 - (h 1 0 * γ 0 1 + h 1 1 * γ 1 1) * h 1 0 ∧
    (h * γ * h⁻¹) 1 1 = -((h 1 0 * γ 0 0 + h 1 1 * γ 1 0) * h 0 1) + (h 1 0 * γ 0 1 + h 1 1 * γ 1 1) * h 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Conjugation carries fixed points**: with `Q_γ(p, q) = c p² + (d - a) p q - b q²` (so `γ` fixes `[p : q] ∈ ℝ̂`
iff `Q_γ(p, q) = 0`), `Q_{hγh⁻¹}(h (p, q)) = Q_γ(p, q)`. -/
theorem s27g_fix_conj (h γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p q : ℝ) :
    (h * γ * h⁻¹) 1 0 * (h 0 0 * p + h 0 1 * q) ^ 2 + ((h * γ * h⁻¹) 1 1 - (h * γ * h⁻¹) 0 0) *
      (h 0 0 * p + h 0 1 * q) * (h 1 0 * p + h 1 1 * q) - (h * γ * h⁻¹) 0 1 * (h 1 0 * p + h 1 1 * q) ^ 2 =
    γ 1 0 * p ^ 2 + (γ 1 1 - γ 0 0) * p * q - γ 0 1 * q ^ 2 := by
  obtain ⟨e00, e01, e10, e11⟩ := s27g_conj_apply h γ
  have hdet := hnf_sl2_det h
  rw [e00, e01, e10, e11]
  linear_combination ((h 0 0 * h 1 1 - h 0 1 * h 1 0) + 1) *
    (γ 1 0 * p ^ 2 + (γ 1 1 - γ 0 0) * p * q - γ 0 1 * q ^ 2) * hdet

/-- The trace is invariant under conjugation. -/
theorem s27g_trace_conj (h γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (h * γ * h⁻¹) 0 0 + (h * γ * h⁻¹) 1 1 = γ 0 0 + γ 1 1 := by
  obtain ⟨e00, -, -, e11⟩ := s27g_conj_apply h γ
  have hdet := hnf_sl2_det h
  rw [e00, e11]
  linear_combination (γ 0 0 + γ 1 1) * hdet

/-- For `c ≠ 0`, `x = (a - d + σ)/(2c)` with `σ² = (a + d)² - 4` is a fixed point of `γ`. -/
theorem s27g_root_fixed {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) {σ : ℝ}
    (hσ : σ ^ 2 = (γ 0 0 + γ 1 1) ^ 2 - 4) :
    γ 1 0 * ((γ 0 0 - γ 1 1 + σ) / (2 * γ 1 0)) ^ 2 + (γ 1 1 - γ 0 0) * ((γ 0 0 - γ 1 1 + σ) / (2 * γ 1 0)) * 1 -
      γ 0 1 * 1 ^ 2 = 0 := by
  have hdet := hnf_sl2_det γ
  set x := (γ 0 0 - γ 1 1 + σ) / (2 * γ 1 0) with hx
  have hxe : 2 * γ 1 0 * x = γ 0 0 - γ 1 1 + σ := by
    rw [hx]
    field_simp
  have key : 4 * γ 1 0 * (γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x * 1 - γ 0 1 * 1 ^ 2) = 0 := by
    linear_combination (2 * γ 1 0 * x - γ 0 0 + γ 1 1 + σ) * hxe + hσ + 4 * hdet
  exact (mul_eq_zero.1 key).resolve_left (mul_ne_zero four_ne_zero hc)

/-- A non-elliptic `γ` (`|tr γ| ≥ 2`) fixes a point `[p : q]` of `ℝ̂`. -/
theorem s27g_fixed_vec {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : 2 ≤ |γ 0 0 + γ 1 1|) :
    ∃ p q : ℝ, (p ≠ 0 ∨ q ≠ 0) ∧ γ 1 0 * p ^ 2 + (γ 1 1 - γ 0 0) * p * q - γ 0 1 * q ^ 2 = 0 := by
  by_cases hc : γ 1 0 = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hc]; ring⟩
  · have h4 : 0 ≤ (γ 0 0 + γ 1 1) ^ 2 - 4 := by
      nlinarith [sq_abs (γ 0 0 + γ 1 1), abs_nonneg (γ 0 0 + γ 1 1)]
    exact ⟨_, 1, Or.inr one_ne_zero, s27g_root_fixed hc (Real.sq_sqrt h4)⟩

/-- A hyperbolic `γ` (`|tr γ| > 2`) fixes two distinct points `[p₁ : q₁] ≠ [p₂ : q₂]` of `ℝ̂`. -/
theorem s27g_hyp_two_fixed {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : 2 < |γ 0 0 + γ 1 1|) :
    ∃ p₁ q₁ p₂ q₂ : ℝ, γ 1 0 * p₁ ^ 2 + (γ 1 1 - γ 0 0) * p₁ * q₁ - γ 0 1 * q₁ ^ 2 = 0 ∧
      γ 1 0 * p₂ ^ 2 + (γ 1 1 - γ 0 0) * p₂ * q₂ - γ 0 1 * q₂ ^ 2 = 0 ∧ p₁ * q₂ - p₂ * q₁ ≠ 0 := by
  have hdet := hnf_sl2_det γ
  by_cases hc : γ 1 0 = 0
  · -- `∞` and `b/(d - a)`
    have had : γ 0 0 * γ 1 1 = 1 := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact hdet
    have hda : γ 1 1 - γ 0 0 ≠ 0 := (hnf_core_eq had h).1
    refine ⟨1, 0, γ 0 1 / (γ 1 1 - γ 0 0), 1, by rw [hc]; ring, ?_, by norm_num⟩
    rw [hc]
    field_simp
    ring
  · have h4 : 0 < (γ 0 0 + γ 1 1) ^ 2 - 4 := by
      nlinarith [sq_abs (γ 0 0 + γ 1 1), abs_nonneg (γ 0 0 + γ 1 1)]
    have hs := Real.sqrt_pos.2 h4
    have hs2 := Real.sq_sqrt h4.le
    have hs2' : (-Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) ^ 2 = (γ 0 0 + γ 1 1) ^ 2 - 4 := by
      rw [neg_sq]
      exact hs2
    refine ⟨_, 1, _, 1, s27g_root_fixed hc hs2, s27g_root_fixed hc hs2', ?_⟩
    rw [mul_one, mul_one, ← sub_div]
    refine div_ne_zero ?_ (mul_ne_zero two_ne_zero hc)
    intro h0
    have : 2 * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4) = 0 := by linear_combination h0
    linarith

/-- **No common fixed point without hyperbolic elements.**  If every element of the covering group of a compact
surface fixes `[p : q] ∈ ℝ̂` and has `|tr| ≤ 2`, then after conjugating `[p : q]` to `∞` (the covering group of
`adjustProjection p A`) every element is `±(z ↦ z + b)`, which preserves `Im`; but some element moves a point of large
imaginary part into a compact set. -/
theorem s27g_common_fixed_false {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S} (hp : IsUniformization Γ p₀)
    {p q : ℝ} (hpq : p ≠ 0 ∨ q ≠ 0)
    (hfix : ∀ h ∈ Γ, h 1 0 * p ^ 2 + (h 1 1 - h 0 0) * p * q - h 0 1 * q ^ 2 = 0)
    (htr : ∀ h ∈ Γ, |h 0 0 + h 1 1| ≤ 2) : False := by
  have hn : 0 < p ^ 2 + q ^ 2 := by
    rcases hpq with h | h
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![p / (p ^ 2 + q ^ 2), q / (p ^ 2 + q ^ 2); -q, p], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩
  have hA1 : A 0 0 * p + A 0 1 * q = 1 := by
    show p / (p ^ 2 + q ^ 2) * p + q / (p ^ 2 + q ^ 2) * q = 1
    field_simp
  have hA2 : A 1 0 * p + A 1 1 * q = 0 := by
    show -q * p + p * q = 0
    ring
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate (adjustProjection_isUniformization hp A)
  obtain ⟨M, hM⟩ := (hK.image UpperHalfPlane.continuous_im).bddAbove
  have hpos : 0 < max M 0 + 1 := by positivity
  set z : UpperHalfPlane := ⟨⟨0, max M 0 + 1⟩, hpos⟩ with hz
  obtain ⟨h', hh', hh'z⟩ := hKz z
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hh'
  have e : (MulAut.conj A).toMonoidHom h = A * h * A⁻¹ := by simp [MulAut.conj_apply]
  rw [e] at hh'z
  have hcov := s27g_fix_conj A h p q
  rw [hA1, hA2, hfix h hh] at hcov
  have hc0 : (A * h * A⁻¹) 1 0 = 0 := by linear_combination hcov
  have htr' := s27g_trace_conj A h
  have hdet' := hnf_sl2_det (A * h * A⁻¹)
  rw [hc0, mul_zero, sub_zero] at hdet'
  have htr2 : ((A * h * A⁻¹) 0 0 + (A * h * A⁻¹) 1 1) ^ 2 ≤ 2 ^ 2 := by
    rw [htr']
    exact sq_le_sq' (abs_le.1 (htr h hh)).1 (abs_le.1 (htr h hh)).2
  have hsq0 : ((A * h * A⁻¹) 0 0 - (A * h * A⁻¹) 1 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((A * h * A⁻¹) 0 0 - (A * h * A⁻¹) 1 1)]
  have had : (A * h * A⁻¹) 0 0 = (A * h * A⁻¹) 1 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq0
    linarith
  have hd2 : (A * h * A⁻¹) 1 1 * (A * h * A⁻¹) 1 1 = 1 := by
    linear_combination hdet' - (A * h * A⁻¹) 1 1 * had
  -- `A h A⁻¹` preserves `Im`
  have him : ((A * h * A⁻¹) • z).im = z.im := by
    show (((A * h * A⁻¹) • z : UpperHalfPlane) : ℂ).im = ((z : UpperHalfPlane) : ℂ).im
    rw [h36t_coe_smul, utm_im_mobius (hnf_sl2_det _), hc0, Complex.ofReal_zero, zero_mul, zero_add,
      Complex.normSq_ofReal, hd2, div_one]
  have h1 : ((A * h * A⁻¹) • z).im ≤ M := hM ⟨_, hh'z, rfl⟩
  rw [him] at h1
  have h2 : z.im = max M 0 + 1 := rfl
  linarith [le_max_left M 0]

/-- **Two fixed points.**  The covering group of a compact surface contains elements `γ₁, γ₂ ≠ ±1` fixing distinct
points `[p₁ : q₁] ≠ [p₂ : q₂]` of `ℝ̂`: a hyperbolic element has two; otherwise every element is parabolic or `±1`
(no elliptic ones, by freeness), a parabolic `γ₀ ≠ ±1` exists (`s27g_exists_ne_one`), some `h ∈ Γ` moves its fixed
point (`s27g_common_fixed_false`), and `h γ₀ h⁻¹` fixes the image (`s27g_fix_conj`). -/
theorem s27g_two_fixed {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S} (hp : IsUniformization Γ p₀) :
    ∃ (p₁ q₁ p₂ q₂ : ℝ) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ₁ ∈ Γ ∧ γ₂ ∈ Γ ∧ γ₁ ≠ 1 ∧ γ₁ ≠ -1 ∧
      γ₂ ≠ 1 ∧ γ₂ ≠ -1 ∧ γ₁ 1 0 * p₁ ^ 2 + (γ₁ 1 1 - γ₁ 0 0) * p₁ * q₁ - γ₁ 0 1 * q₁ ^ 2 = 0 ∧
      γ₂ 1 0 * p₂ ^ 2 + (γ₂ 1 1 - γ₂ 0 0) * p₂ * q₂ - γ₂ 0 1 * q₂ ^ 2 = 0 ∧ p₁ * q₂ - p₂ * q₁ ≠ 0 := by
  have hfree := s27g_actsFreely hp
  have htr1 : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, (γ = 1 ∨ γ = -1) → |γ 0 0 + γ 1 1| = 2 := by
    rintro γ (rfl | rfl)
    · norm_num
    · norm_num [Matrix.SpecialLinearGroup.coe_neg]
  have hnoell : ∀ γ ∈ Γ, 2 ≤ |γ 0 0 + γ 1 1| := by
    intro γ hγ
    by_contra hlt
    push Not at hlt
    obtain ⟨τ, hτ⟩ := s27g_elliptic_fixed hlt
    have := htr1 γ (hfree γ hγ τ hτ)
    linarith
  have hconj_ne : ∀ h γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ≠ 1 → γ ≠ -1 →
      h * γ * h⁻¹ ≠ 1 ∧ h * γ * h⁻¹ ≠ -1 := by
    intro h γ h1 h2
    constructor
    · intro e
      apply h1
      calc γ = h⁻¹ * (h * γ * h⁻¹) * h := by group
        _ = 1 := by rw [e]; group
    · intro e
      apply h2
      calc γ = h⁻¹ * (h * γ * h⁻¹) * h := by group
        _ = -1 := by rw [e, mul_neg_one, neg_mul, inv_mul_cancel]
  by_cases hhyp : ∃ γ ∈ Γ, 2 < |γ 0 0 + γ 1 1|
  · obtain ⟨γ, hγ, hh⟩ := hhyp
    obtain ⟨p₁, q₁, p₂, q₂, h1, h2, h12⟩ := s27g_hyp_two_fixed hh
    have hne1 : γ ≠ 1 := fun e => by
      have := htr1 γ (Or.inl e)
      linarith
    have hne2 : γ ≠ -1 := fun e => by
      have := htr1 γ (Or.inr e)
      linarith
    exact ⟨p₁, q₁, p₂, q₂, γ, γ, hγ, hγ, hne1, hne2, hne1, hne2, h1, h2, h12⟩
  · push Not at hhyp
    obtain ⟨γ₀, hγ₀, hne1, hne2⟩ := s27g_exists_ne_one hp
    obtain ⟨p, q, hpq, hfix⟩ := s27g_fixed_vec (hnoell γ₀ hγ₀)
    by_cases hall : ∀ h ∈ Γ, h 1 0 * p ^ 2 + (h 1 1 - h 0 0) * p * q - h 0 1 * q ^ 2 = 0
    · exact (s27g_common_fixed_false hp hpq hall hhyp).elim
    · push Not at hall
      obtain ⟨h, hh, hQ⟩ := hall
      obtain ⟨hc1, hc2⟩ := hconj_ne h γ₀ hne1 hne2
      refine ⟨p, q, h 0 0 * p + h 0 1 * q, h 1 0 * p + h 1 1 * q, γ₀, h * γ₀ * h⁻¹, hγ₀,
        Γ.mul_mem (Γ.mul_mem hh hγ₀) (Γ.inv_mem hh), hne1, hne2, hc1, hc2, hfix, ?_, ?_⟩
      · rw [s27g_fix_conj]
        exact hfix
      · intro e
        apply hQ
        linear_combination e

/-- **Orbits accumulate at every real point.**  For `x ∈ ℝ` and `ε > 0` some `h ∈ Γ` has `|h(i) - x| < ε`: with `K`
compact meeting every orbit and `K ⊆ B(i, R)`, move `z = x + t i` into `K` by `γ ∈ Γ`; then `h = γ⁻¹` has
`d(h(i), z) = d(i, γ z) ≤ R`, so `h(i)` lies in the Euclidean disc of centre `x + i t cosh R` and radius `t sinh R`
(`UpperHalfPlane.dist_le_iff_dist_coe_center_le`), and `|h(i) - x| ≤ t (sinh R + cosh R)`. -/
theorem s27g_orbit_near {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ Γ, ‖((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ) - (x : ℂ)‖ < ε := by
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall UpperHalfPlane.I).1 hK.isBounded
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right R 0
  have hsinh : 0 ≤ Real.sinh R' := Real.sinh_nonneg_iff.2 hR'0
  have hcosh : 0 < Real.cosh R' := Real.cosh_pos R'
  set E := Real.sinh R' + Real.cosh R' with hE
  have hEpos : 0 < E := by positivity
  set t := ε / (2 * E) with ht
  have htpos : 0 < t := by positivity
  set z : UpperHalfPlane := ⟨⟨x, t⟩, htpos⟩ with hz
  obtain ⟨γ, hγ, hγz⟩ := hKz z
  refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
  have hd : dist (γ⁻¹ • UpperHalfPlane.I) z ≤ R' := by
    have e : dist (γ⁻¹ • UpperHalfPlane.I) z = dist UpperHalfPlane.I (γ • z) := by
      rw [← dist_smul γ, smul_inv_smul]
    rw [e, dist_comm]
    exact (mem_closedBall.1 (hR hγz)).trans (le_max_left R 0)
  rw [UpperHalfPlane.dist_le_iff_dist_coe_center_le] at hd
  have hzim : z.im = t := rfl
  have hc : dist ((z.center R' : UpperHalfPlane) : ℂ) (x : ℂ) = t * Real.cosh R' := by
    rw [Complex.dist_of_re_eq]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.center_im, hzim, Complex.ofReal_im, Real.dist_eq, sub_zero,
        abs_of_pos (by positivity)]
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.center_re, Complex.ofReal_re]
      rfl
  rw [← dist_eq_norm]
  calc dist ((γ⁻¹ • UpperHalfPlane.I : UpperHalfPlane) : ℂ) (x : ℂ)
      ≤ dist ((γ⁻¹ • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ((z.center R' : UpperHalfPlane) : ℂ) +
        dist ((z.center R' : UpperHalfPlane) : ℂ) (x : ℂ) := dist_triangle _ _ _
    _ ≤ t * Real.sinh R' + t * Real.cosh R' := by
      rw [hc]
      rw [hzim] at hd
      linarith
    _ = t * E := by ring
    _ < ε := by
      rw [ht]
      field_simp
      linarith

/-- **The Möbius estimate.**  For `h ∈ SL(2, ℝ)` and distinct points `[p₁ : q₁] ≠ [p₂ : q₂]` of `ℝ̂`, one of them,
`[p : q]`, has a finite image `y = h[p : q]` with `|y - h(i)| ≤ B · Im h(i)`, `B = S²/|Δ|` (`S` the sum of the
`|p_k|, |q_k|`, `Δ = p₁q₂ - p₂q₁`): `y - h(i) = (p - q i)/(L (c i + d))` with `L = c p + d q`,
`Im h(i) = 1/|c i + d|²`, and the larger `|L_k|` bounds `(|c| + |d|) |Δ| / S ≥ |c i + d| |Δ| / S`. -/
theorem s27g_near_estimate (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) {p₁ q₁ p₂ q₂ : ℝ}
    (hΔ : p₁ * q₂ - p₂ * q₁ ≠ 0) :
    ∃ p q : ℝ, ((p = p₁ ∧ q = q₁) ∨ (p = p₂ ∧ q = q₂)) ∧ h 1 0 * p + h 1 1 * q ≠ 0 ∧
      ‖(((h 0 0 * p + h 0 1 * q) / (h 1 0 * p + h 1 1 * q) : ℝ) : ℂ) -
          ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ ≤
        (|p₁| + |p₂| + |q₁| + |q₂|) ^ 2 / |p₁ * q₂ - p₂ * q₁| * (h • UpperHalfPlane.I).im := by
  have hdet := hnf_sl2_det h
  have hdetC : (h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0 = 1 := by exact_mod_cast hdet
  have hD : (h 1 0 : ℂ) * Complex.I + h 1 1 ≠ 0 := by
    have e := h36t_den_ne h UpperHalfPlane.I
    rwa [UpperHalfPlane.coe_I] at e
  set ν := ‖(h 1 0 : ℂ) * Complex.I + h 1 1‖ with hν
  have hνpos : 0 < ν := norm_pos_iff.2 hD
  have hνle : ν ≤ |h 1 0| + |h 1 1| := by
    calc ν ≤ ‖(h 1 0 : ℂ) * Complex.I‖ + ‖((h 1 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |h 1 0| + |h 1 1| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
  have him : (h • UpperHalfPlane.I).im = 1 / ν ^ 2 := by
    show ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ).im = _
    rw [h36t_coe_smul, utm_im_mobius hdet, UpperHalfPlane.coe_I, Complex.I_im, Complex.normSq_eq_norm_sq]
  have hdiff : ∀ p q : ℝ, h 1 0 * p + h 1 1 * q ≠ 0 →
      ‖(((h 0 0 * p + h 0 1 * q) / (h 1 0 * p + h 1 1 * q) : ℝ) : ℂ) -
          ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ =
        ‖(p : ℂ) - q * Complex.I‖ / (|h 1 0 * p + h 1 1 * q| * ν) := by
    intro p q hL
    have hL' : ((h 1 0 * p + h 1 1 * q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
    rw [h36t_coe_smul, UpperHalfPlane.coe_I, Complex.ofReal_div, div_sub_div _ _ hL' hD, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    congr 2
    push_cast
    linear_combination ((p : ℂ) - q * Complex.I) * hdetC
  have main : ∀ p q : ℝ, |p| + |q| ≤ |p₁| + |p₂| + |q₁| + |q₂| →
      ν * |p₁ * q₂ - p₂ * q₁| ≤ |h 1 0 * p + h 1 1 * q| * (|p₁| + |p₂| + |q₁| + |q₂|) →
      h 1 0 * p + h 1 1 * q ≠ 0 ∧
      ‖(((h 0 0 * p + h 0 1 * q) / (h 1 0 * p + h 1 1 * q) : ℝ) : ℂ) -
          ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ ≤
        (|p₁| + |p₂| + |q₁| + |q₂|) ^ 2 / |p₁ * q₂ - p₂ * q₁| * (h • UpperHalfPlane.I).im := by
    intro p q hpq hL
    set S := |p₁| + |p₂| + |q₁| + |q₂| with hS
    set Δ := |p₁ * q₂ - p₂ * q₁| with hΔdef
    have hΔpos : 0 < Δ := abs_pos.2 hΔ
    have hS0 : 0 ≤ S := by positivity
    have hLpos : 0 < |h 1 0 * p + h 1 1 * q| := by
      by_contra hcon
      have h0 : |h 1 0 * p + h 1 1 * q| = 0 := le_antisymm (not_lt.1 hcon) (abs_nonneg _)
      rw [h0, zero_mul] at hL
      have := mul_pos hνpos hΔpos
      linarith
    have hL0 : h 1 0 * p + h 1 1 * q ≠ 0 := abs_pos.1 hLpos
    refine ⟨hL0, ?_⟩
    rw [hdiff p q hL0, him, div_le_iff₀ (by positivity)]
    have hn : ‖(p : ℂ) - q * Complex.I‖ ≤ S := by
      calc ‖(p : ℂ) - q * Complex.I‖ ≤ ‖(p : ℂ)‖ + ‖(q : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = |p| + |q| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ ≤ S := hpq
    have key : S ≤ S ^ 2 / Δ * (1 / ν ^ 2) * (|h 1 0 * p + h 1 1 * q| * ν) := by
      have e : S ^ 2 / Δ * (1 / ν ^ 2) * (|h 1 0 * p + h 1 1 * q| * ν) =
          S * (|h 1 0 * p + h 1 1 * q| * S) / (ν * Δ) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hL hS0
    exact hn.trans key
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    have e := abs_add_le a (-b)
    rwa [abs_neg, ← sub_eq_add_neg] at e
  have hc_le : |h 1 0| * |p₁ * q₂ - p₂ * q₁| ≤
      |h 1 0 * p₁ + h 1 1 * q₁| * |q₂| + |h 1 0 * p₂ + h 1 1 * q₂| * |q₁| := by
    rw [← abs_mul, ← abs_mul, ← abs_mul,
      show h 1 0 * (p₁ * q₂ - p₂ * q₁) = (h 1 0 * p₁ + h 1 1 * q₁) * q₂ - (h 1 0 * p₂ + h 1 1 * q₂) * q₁ by ring]
    exact habs _ _
  have hd_le : |h 1 1| * |p₁ * q₂ - p₂ * q₁| ≤
      |h 1 0 * p₂ + h 1 1 * q₂| * |p₁| + |h 1 0 * p₁ + h 1 1 * q₁| * |p₂| := by
    rw [← abs_mul, ← abs_mul, ← abs_mul,
      show h 1 1 * (p₁ * q₂ - p₂ * q₁) = (h 1 0 * p₂ + h 1 1 * q₂) * p₁ - (h 1 0 * p₁ + h 1 1 * q₁) * p₂ by ring]
    exact habs _ _
  have hνΔ : ν * |p₁ * q₂ - p₂ * q₁| ≤ (|h 1 0| + |h 1 1|) * |p₁ * q₂ - p₂ * q₁| :=
    mul_le_mul_of_nonneg_right hνle (abs_nonneg _)
  have hp₁ := abs_nonneg p₁
  have hp₂ := abs_nonneg p₂
  have hq₁ := abs_nonneg q₁
  have hq₂ := abs_nonneg q₂
  rcases le_total |h 1 0 * p₁ + h 1 1 * q₁| |h 1 0 * p₂ + h 1 1 * q₂| with h12 | h21
  · obtain ⟨hL0, hest⟩ := main p₂ q₂ (by linarith) (by
      have e1 := mul_le_mul_of_nonneg_right h12 hq₂
      have e2 := mul_le_mul_of_nonneg_right h12 hp₂
      nlinarith)
    exact ⟨p₂, q₂, Or.inr ⟨rfl, rfl⟩, hL0, hest⟩
  · obtain ⟨hL0, hest⟩ := main p₁ q₁ (by linarith) (by
      have e1 := mul_le_mul_of_nonneg_right h21 hq₁
      have e2 := mul_le_mul_of_nonneg_right h21 hp₁
      nlinarith)
    exact ⟨p₁, q₁, Or.inl ⟨rfl, rfl⟩, hL0, hest⟩

/-- §27.1: for a compact surface `S₀ = ℍ/G₀` the fixed points of the elements of `G₀` are dense
in `ℝ`. -/
theorem fuchsianFixedPoints_dense [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : Dense (fuchsianFixedPoints Γ₀) := by
  obtain ⟨p₁, q₁, p₂, q₂, γ₁, γ₂, hγ₁, hγ₂, h11, h12, h21, h22, hf₁, hf₂, hΔ⟩ := s27g_two_fixed hp₀
  set B := (|p₁| + |p₂| + |q₁| + |q₂|) ^ 2 / |p₁ * q₂ - p₂ * q₁| with hB
  have hB0 : 0 ≤ B := by positivity
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨h, hh, hnear⟩ := s27g_orbit_near hp₀ x (ε := ε / (B + 1)) (by positivity)
  obtain ⟨p, q, hpq, hL, hest⟩ := s27g_near_estimate h hΔ
  obtain ⟨γ, hγ, hγ1, hγ2, hfix⟩ : ∃ γ ∈ Γ₀, γ ≠ 1 ∧ γ ≠ -1 ∧
      γ 1 0 * p ^ 2 + (γ 1 1 - γ 0 0) * p * q - γ 0 1 * q ^ 2 = 0 := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨γ₁, hγ₁, h11, h12, hf₁⟩
    · exact ⟨γ₂, hγ₂, h21, h22, hf₂⟩
  set y := (h 0 0 * p + h 0 1 * q) / (h 1 0 * p + h 1 1 * q) with hy
  refine ⟨y, ?_, ?_⟩
  · rw [mem_ball, Real.dist_eq]
    set w : ℂ := ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ) with hw
    have him_le : (h • UpperHalfPlane.I).im ≤ ‖w - (x : ℂ)‖ := by
      have e := Complex.abs_im_le_norm (w - (x : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at e
      exact (le_abs_self _).trans e
    have hyx : |y - x| = ‖(y : ℂ) - (x : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hyx]
    calc ‖(y : ℂ) - (x : ℂ)‖ ≤ ‖(y : ℂ) - w‖ + ‖w - (x : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B * ‖w - (x : ℂ)‖ + ‖w - (x : ℂ)‖ := by
        have := mul_le_mul_of_nonneg_left him_le hB0
        linarith
      _ = (B + 1) * ‖w - (x : ℂ)‖ := by ring
      _ < (B + 1) * (ε / (B + 1)) := mul_lt_mul_of_pos_left hnear (by positivity)
      _ = ε := by field_simp
  · refine ⟨h * γ * h⁻¹, Γ₀.mul_mem (Γ₀.mul_mem hh hγ) (Γ₀.inv_mem hh), ?_, ?_, ?_⟩
    · intro e
      apply hγ1
      calc γ = h⁻¹ * (h * γ * h⁻¹) * h := by group
        _ = 1 := by rw [e]; group
    · intro e
      apply hγ2
      calc γ = h⁻¹ * (h * γ * h⁻¹) * h := by group
        _ = -1 := by rw [e, mul_neg_one, neg_mul, inv_mul_cancel]
    · have hcov := s27g_fix_conj h γ p q
      rw [hfix] at hcov
      have hyL : y * (h 1 0 * p + h 1 1 * q) = h 0 0 * p + h 0 1 * q := div_mul_cancel₀ _ hL
      rw [← hyL] at hcov
      have key : (h 1 0 * p + h 1 1 * q) ^ 2 * ((h * γ * h⁻¹) 1 0 * y ^ 2 +
          ((h * γ * h⁻¹) 1 1 - (h * γ * h⁻¹) 0 0) * y - (h * γ * h⁻¹) 0 1) = 0 := by
        linear_combination hcov
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hL)

/-- A real point lies in the closed upper half-plane `closure (toExt ℍ)` of `ℂ̄`. -/
theorem s27t_mem_closure_real (x : ℝ) : (((x : ℂ)) : ExtPlane) ∈ closure (toExt upperHalf) := by
  rw [scExt_closure_toExt_upperHalf]
  exact Or.inl ⟨(x : ℂ), by simp, rfl⟩

/-- A point of `ℍ` is not real. -/
theorem s27t_ne_real (u : UpperHalfPlane) (r : ℝ) : (u : ℂ) ≠ (r : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.ofReal_im] at him
  exact (ne_of_gt u.im_pos) him

/-- `t ↦ (A - t B)/(1 - t)` tends to `A` at `t → 0` along a sequence. -/
theorem s27t_tendsto_frac {A B : ℂ} {t : ℕ → ℂ} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (A - t n * B) / (1 - t n)) atTop (𝓝 A) := by
  have h1 : Tendsto (fun n => A - t n * B) atTop (𝓝 (A - 0 * B)) := tendsto_const_nhds.sub (ht.mul_const B)
  have h2 : Tendsto (fun n => 1 - t n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub ht
  have h3 : Tendsto (fun n => (A - t n * B) / (1 - t n)) atTop (𝓝 ((A - 0 * B) / (1 - 0))) :=
    h1.div h2 (by norm_num)
  rwa [zero_mul, sub_zero, sub_zero, div_one] at h3

/-- **Dynamics of a hyperbolic element.**  A finite fixed point `x` of a hyperbolic `γ` is the limit of every
orbit `δⁿ w` (`w ∈ ℍ`) of `δ = γ` (if `x` is attracting) or of `δ = γ⁻¹` (if `x` is repelling): by the normal
form `hyperbolic_normal_form` (the cross ratio for two finite fixed points, the affine forms when one fixed point
is `∞`). -/
theorem s27t_hyperbolic_dynamics {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|) {x : ℝ}
    (hx : γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0) :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, (δ = γ ∨ δ = γ⁻¹) ∧
      ∀ w : UpperHalfPlane, Tendsto (fun n : ℕ => (((δ ^ n) • w : UpperHalfPlane) : ℂ)) atTop (𝓝 (x : ℂ)) := by
  obtain ⟨hL1, hne, hcross, hinfA, hinfR, -⟩ := hyperbolic_normal_form hγ
  have hL0 : 0 < multiplier γ := lt_trans one_pos hL1
  have hLc : (multiplier γ : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hsmul : ∀ u : UpperHalfPlane,
      ((γ • u : UpperHalfPlane) : ℂ) = mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u := by
    intro u
    rw [h36t_coe_smul]
    rfl
  -- geometric decay `(1/λ)ⁿ → 0`, as a complex sequence
  have hpow : Tendsto (fun n : ℕ => ((multiplier γ : ℂ)⁻¹) ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hL0.le) (inv_lt_one_of_one_lt₀ hL1)
    have h' := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h'
    refine h'.congr fun n => ?_
    simp [Function.comp]
  by_cases hc : γ 1 0 = 0
  · -- `c = 0`: the fixed points are `∞` and `b/(d - a)`
    have had : γ 0 0 * γ 1 1 = 1 := by
      have h := hnf_sl2_det γ
      rw [hc, mul_zero, sub_zero] at h
      exact h
    obtain ⟨hda, -, -⟩ := hnf_core_eq had hγ
    have hxv : x = γ 0 1 / (γ 1 1 - γ 0 0) := by
      rw [eq_div_iff hda]
      rw [hc, zero_mul, zero_add] at hx
      linarith
    obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
    by_cases ha : 1 < |γ 0 0|
    · -- attracting `∞`, repelling `x`: iterate `γ⁻¹`
      obtain ⟨hA, hR⟩ := h1 ha
      rw [← hxv] at hR
      have key := hinfA x hA hR
      refine ⟨γ⁻¹, Or.inr rfl, fun w => ?_⟩
      have hstep : ∀ u : UpperHalfPlane,
          ((γ⁻¹ • u : UpperHalfPlane) : ℂ) - x = ((u : ℂ) - x) * (multiplier γ : ℂ)⁻¹ := by
        intro u
        have h := key ((γ⁻¹ • u : UpperHalfPlane) : ℂ)
        rw [← hsmul, smul_inv_smul] at h
        rw [h]
        field_simp
      have hiter : ∀ n : ℕ, (((γ⁻¹) ^ n • w : UpperHalfPlane) : ℂ) =
          ((w : ℂ) - x) * ((multiplier γ : ℂ)⁻¹) ^ n + x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul]
          have h := hstep ((γ⁻¹) ^ n • w)
          rw [ih] at h
          rw [pow_succ]
          linear_combination h
      have ht : Tendsto (fun n : ℕ => ((w : ℂ) - x) * ((multiplier γ : ℂ)⁻¹) ^ n + x) atTop
          (𝓝 (((w : ℂ) - x) * 0 + x)) := (hpow.const_mul _).add_const _
      rw [mul_zero, zero_add] at ht
      exact ht.congr fun n => (hiter n).symm
    · -- attracting `x`, repelling `∞`: iterate `γ`
      obtain ⟨hA, hR⟩ := h2 ha
      rw [← hxv] at hA
      have key := hinfR x hA hR
      refine ⟨γ, Or.inl rfl, fun w => ?_⟩
      have hstep : ∀ u : UpperHalfPlane,
          ((γ • u : UpperHalfPlane) : ℂ) - x = ((u : ℂ) - x) * (multiplier γ : ℂ)⁻¹ := by
        intro u
        rw [hsmul, key]
        field_simp
      have hiter : ∀ n : ℕ, ((γ ^ n • w : UpperHalfPlane) : ℂ) =
          ((w : ℂ) - x) * ((multiplier γ : ℂ)⁻¹) ^ n + x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul]
          have h := hstep (γ ^ n • w)
          rw [ih] at h
          rw [pow_succ]
          linear_combination h
      have ht : Tendsto (fun n : ℕ => ((w : ℂ) - x) * ((multiplier γ : ℂ)⁻¹) ^ n + x) atTop
          (𝓝 (((w : ℂ) - x) * 0 + x)) := (hpow.const_mul _).add_const _
      rw [mul_zero, zero_add] at ht
      exact ht.congr fun n => (hiter n).symm
  · -- `c ≠ 0`: two finite fixed points `σ ≠ τ`
    obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
    obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
    have hdet := hnf_sl2_det γ
    obtain ⟨-, hε2, hεt, hs, hs2⟩ := hnf_sign_sqrt hγ
    obtain ⟨fσ, fτ, -, -⟩ := hnf_core_ne hdet hc hε2 hεt hs hs2 (hnf_attr_eq hc hσ) (hnf_rep_eq hc hτ)
    have hστ : σ ≠ τ := by
      intro h
      apply hne
      rw [hσ, hτ, h]
    have hστc : (σ : ℂ) ≠ (τ : ℂ) := by exact_mod_cast hστ
    have hsum : γ 1 0 * (σ + τ) + (γ 1 1 - γ 0 0) = 0 := by
      have h : (σ - τ) * (γ 1 0 * (σ + τ) + (γ 1 1 - γ 0 0)) = 0 := by linear_combination fσ - fτ
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hστ)
    have hxστ : x = σ ∨ x = τ := by
      have h : (x - σ) * (γ 1 0 * (x - τ)) = 0 := by linear_combination hx - fσ + (σ - x) * hsum
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by have := (mul_eq_zero.1 h).resolve_left hc; linarith)
    -- the cross ratio `Φ(u) = (u - σ)/(u - τ)` satisfies `Φ(u) = λ Φ(γ u)`
    set Φ : UpperHalfPlane → ℂ := fun u => ((u : ℂ) - σ) / ((u : ℂ) - τ) with hΦdef
    have hΦ : ∀ u : UpperHalfPlane, Φ u = (multiplier γ : ℂ) * Φ (γ • u) := by
      intro u
      have h := hcross σ τ hσ hτ (u : ℂ) (h36t_den_ne γ u) (s27t_ne_real u τ)
        (by rw [← hsmul]; exact s27t_ne_real _ τ)
      simp only [hΦdef]
      rw [hsmul]
      exact h
    have hΦ1 : ∀ u : UpperHalfPlane, Φ u ≠ 1 := by
      intro u h
      simp only [hΦdef] at h
      rw [div_eq_one_iff_eq (sub_ne_zero.2 (s27t_ne_real u τ))] at h
      exact hστc (by linear_combination -h)
    have hΦ0 : ∀ u : UpperHalfPlane, Φ u ≠ 0 := by
      intro u h
      simp only [hΦdef] at h
      rcases div_eq_zero_iff.1 h with h | h
      · exact s27t_ne_real u σ (sub_eq_zero.1 h)
      · exact s27t_ne_real u τ (sub_eq_zero.1 h)
    -- solve for `u`: `u = (σ - Φ τ)/(1 - Φ)`
    have hsolve : ∀ u : UpperHalfPlane, (u : ℂ) = (σ - Φ u * τ) / (1 - Φ u) := by
      intro u
      rw [eq_div_iff (sub_ne_zero.2 (Ne.symm (hΦ1 u)))]
      simp only [hΦdef]
      field_simp [sub_ne_zero.2 (s27t_ne_real u τ)]
      ring
    rcases hxστ with hxσ | hxτ
    · -- `x = σ` is attracting: iterate `γ`
      rw [hxσ]
      refine ⟨γ, Or.inl rfl, fun w => ?_⟩
      have hiter : ∀ n : ℕ, Φ (γ ^ n • w) = Φ w * ((multiplier γ : ℂ)⁻¹) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul]
          have h := hΦ (γ ^ n • w)
          rw [ih] at h
          rw [pow_succ]
          field_simp
          linear_combination -h
      have ht : Tendsto (fun n : ℕ => Φ (γ ^ n • w)) atTop (𝓝 0) := by
        have h := hpow.const_mul (Φ w)
        rw [mul_zero] at h
        exact h.congr fun n => (hiter n).symm
      exact (s27t_tendsto_frac (A := (σ : ℂ)) (B := (τ : ℂ)) ht).congr fun n => (hsolve _).symm
    · -- `x = τ` is repelling: iterate `γ⁻¹`
      rw [hxτ]
      refine ⟨γ⁻¹, Or.inr rfl, fun w => ?_⟩
      have hiter : ∀ n : ℕ, (Φ ((γ⁻¹) ^ n • w))⁻¹ = (Φ w)⁻¹ * ((multiplier γ : ℂ)⁻¹) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul]
          have h := hΦ (γ⁻¹ • (γ⁻¹) ^ n • w)
          rw [smul_inv_smul] at h
          rw [h, mul_inv, ih, pow_succ]
          ring
      have ht : Tendsto (fun n : ℕ => (Φ ((γ⁻¹) ^ n • w))⁻¹) atTop (𝓝 0) := by
        have h := hpow.const_mul (Φ w)⁻¹
        rw [mul_zero] at h
        exact h.congr fun n => (hiter n).symm
      -- `u = (τ - Φ⁻¹ σ)/(1 - Φ⁻¹)`
      have hsolve' : ∀ u : UpperHalfPlane, (u : ℂ) = (τ - (Φ u)⁻¹ * σ) / (1 - (Φ u)⁻¹) := by
        intro u
        have h1 : 1 - (Φ u)⁻¹ ≠ 0 := by
          rw [sub_ne_zero]
          intro h
          exact hΦ1 u (by rw [← inv_inv (Φ u), ← h, inv_one])
        rw [eq_div_iff h1]
        simp only [hΦdef]
        have hu1 : (u : ℂ) - σ ≠ 0 := sub_ne_zero.2 (s27t_ne_real u σ)
        have hu2 : (u : ℂ) - τ ≠ 0 := sub_ne_zero.2 (s27t_ne_real u τ)
        rw [inv_div]
        field_simp
        ring
      exact (s27t_tendsto_frac (A := (τ : ℂ)) (B := (σ : ℂ)) ht).congr fun n => (hsolve' _).symm

/-- (27.2)–(27.3): if `f̃₁ ∘ γ ∘ f̃₁⁻¹ = γ₁ ∘ F ∘ γ ∘ F⁻¹ ∘ γ₁⁻¹` for all `γ ∈ G₀` (27.1), then at the
(attracting) fixed point `x` of every hyperbolic `γ ∈ G₀`, `f̃₁(x) = γ₁ ∘ F(x)` (take `n → ∞` in the
conjugated relation for `γⁿ`). -/
theorem eq27_3 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀)
    (hp₁ : IsUniformization Γ₁ p₁) {F₁ F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    {G₁ G : ExtPlane → ExtPlane} (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁)
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ₁ : γ₁ ∈ Γ₁) (hconj : ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = γ₁ • F (γ • F.symm (γ₁⁻¹ • τ)))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) (hhyp : 2 < |γ 0 0 + γ 1 1|) {x : ℝ}
    (hx : γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 = 0) :
    G₁ ((x : ℂ) : ExtPlane) = mobiusSL (slRealToComplex γ₁) (G ((x : ℂ) : ExtPlane)) := by
  have _ := hp₀
  have _ := hp₁
  have _ := hγ₁
  obtain ⟨δ, hδγ, hdyn⟩ := s27t_hyperbolic_dynamics hhyp hx
  have hδ : δ ∈ Γ₀ := by
    rcases hδγ with rfl | rfl
    exacts [hγ, Γ₀.inv_mem hγ]
  -- the relation along the orbit of `w₀ = i`
  have hrel : ∀ n : ℕ, F₁ (δ ^ n • UpperHalfPlane.I) =
      γ₁ • F (δ ^ n • F.symm (γ₁⁻¹ • F₁ UpperHalfPlane.I)) := by
    intro n
    have h := hconj (δ ^ n) (Γ₀.pow_mem hδ n) (F₁ UpperHalfPlane.I)
    rwa [F₁.symm_apply_apply] at h
  -- a homeomorphic extension takes the values of the map on `ℍ`
  have hext : ∀ {F' : UpperHalfPlane ≃ₜ UpperHalfPlane} {G' : ExtPlane → ExtPlane},
      IsHomeoExtension (liftToC F') upperHalf upperHalf G' → ∀ τ : UpperHalfPlane,
        G' (((τ : ℂ)) : ExtPlane) = (((F' τ : UpperHalfPlane) : ℂ) : ExtPlane) := by
    intro F' G' hG' τ
    rw [hG'.1 τ τ.coe_im_pos, h23l_liftToC_coe]
  -- along an orbit converging to `x`, the map tends to the extension at `x`
  have hlim : ∀ {F' : UpperHalfPlane ≃ₜ UpperHalfPlane} {G' : ExtPlane → ExtPlane},
      IsHomeoExtension (liftToC F') upperHalf upperHalf G' → ∀ w : UpperHalfPlane,
        Tendsto (fun n : ℕ => (((F' (δ ^ n • w) : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
          (𝓝 (G' (((x : ℂ)) : ExtPlane))) := by
    intro F' G' hG' w
    have hcont := hG'.2.1 _ (s27t_mem_closure_real x)
    have hseq : Tendsto (fun n : ℕ => ((((δ ^ n • w : UpperHalfPlane)) : ℂ) : ExtPlane)) atTop
        (𝓝[closure (toExt upperHalf)] (((x : ℂ)) : ExtPlane)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(OnePoint.continuous_coe.tendsto _).comp (hdyn w),
        Eventually.of_forall fun n => subset_closure ⟨_, (δ ^ n • w).coe_im_pos, rfl⟩⟩
    exact (hcont.tendsto.comp hseq).congr fun n => hext hG' _
  have h1 := hlim hG₁ UpperHalfPlane.I
  have h2 := ((k24_mobiusSLHomeo (slRealToComplex γ₁)).continuous.tendsto _).comp
    (hlim hG (F.symm (γ₁⁻¹ • F₁ UpperHalfPlane.I)))
  have h2' : Tendsto (fun n : ℕ => (((F₁ (δ ^ n • UpperHalfPlane.I) : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
      (𝓝 (mobiusSL (slRealToComplex γ₁) (G (((x : ℂ)) : ExtPlane)))) := by
    refine h2.congr fun n => ?_
    simp only [Function.comp, k24_mobiusSLHomeo_coe]
    rw [hrel n, h36t_mobiusSL_coe]
  exact tendsto_nhds_unique h1 h2'

/-- A relation `F ∘ γ = δ ∘ F` on `ℍ` extends to the homeomorphic extension on the closed
half-plane in `ℂ̄`. -/
theorem h36t_ext_equivariant {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf G) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγδ : ∀ τ, F (γ • τ) = δ • F τ) {x : ExtPlane} (hx : x ∈ closure (toExt upperHalf)) :
    G (mobiusSL (slRealToComplex γ) x) = mobiusSL (slRealToComplex δ) (G x) := by
  have hmaps : MapsTo (mobiusSL (slRealToComplex γ)) (closure (toExt upperHalf)) (closure (toExt upperHalf)) :=
    (MapsTo.closure (fun q hq => k24_real_mapsTo_upper γ hq) (k22_t_continuous _))
  refine Set.EqOn.of_subset_closure (f := fun x => G (mobiusSL (slRealToComplex γ) x))
    (g := fun x => mobiusSL (slRealToComplex δ) (G x)) (s := toExt upperHalf)
    (t := closure (toExt upperHalf)) ?_ ?_ ?_ subset_closure subset_rfl hx
  · rintro _ ⟨z, hz, rfl⟩
    have e : ((z : ℂ) : ExtPlane) = (((UpperHalfPlane.mk z hz : UpperHalfPlane) : ℂ) : ExtPlane) := rfl
    simp only
    rw [e, h36t_mobiusSL_coe, h36t_ext_coe hG, h36t_ext_coe hG, hγδ, h36t_mobiusSL_coe]
  · exact hG.2.1.comp (k22_t_continuous _).continuousOn hmaps
  · exact (k22_t_continuous _).comp_continuousOn hG.2.1

/-- Two elements of `SL(2, ℝ)` acting identically on `ℝ̂` act identically on `ℍ`. -/
theorem h36t_smul_eq_of_extRealLine {δ₀ δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : ∀ y ∈ extRealLine, mobiusSL (slRealToComplex δ₀) y = mobiusSL (slRealToComplex δ₁) y)
    (w : UpperHalfPlane) : δ₀ • w = δ₁ • w := by
  set δ := δ₀⁻¹ * δ₁ with hδ
  have hfix : ∀ y ∈ extRealLine, mobiusSL (slRealToComplex δ) y = y := by
    intro y hy
    rw [hδ, k24_slReal_mul, k24_mobiusSL_mul, ← h y hy, k24_slReal_inv, k24_mobiusSL_inv_apply]
  have hdetC : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by exact_mod_cast k24_det_realR δ
  have hinf : extInf ∈ mobiusFixedPoints (δ 0 0 : ℂ) (δ 0 1) (δ 1 0) (δ 1 1) := by
    show mobiusExt _ _ _ _ extInf = extInf
    rw [← k24_mobiusSL_real]
    exact hfix _ (Or.inr rfl)
  have hc : (δ 1 0 : ℂ) = 0 := (mem_mobiusFixedPoints_infty_iff _ _ _ _).1 hinf
  have hreal : ∀ x : ℝ, (((x : ℂ)) : ExtPlane) ∈ mobiusFixedPoints (δ 0 0 : ℂ) (δ 0 1) (δ 1 0) (δ 1 1) := by
    intro x
    show mobiusExt _ _ _ _ _ = _
    rw [← k24_mobiusSL_real]
    exact hfix _ (Or.inl ⟨(x : ℂ), Complex.ofReal_im x, rfl⟩)
  have h0 := (mem_mobiusFixedPoints_coe_iff hdetC _).1 (hreal 0)
  have h1 := (mem_mobiusFixedPoints_coe_iff hdetC _).1 (hreal 1)
  simp only [Complex.ofReal_zero, Complex.ofReal_one] at h0 h1
  have hb : (δ 0 1 : ℂ) = 0 := by linear_combination -h0
  have hda : (δ 1 1 : ℂ) = δ 0 0 := by linear_combination h1 - hc + hb
  have ha : (δ 0 0 : ℂ) ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, zero_sub, hb, zero_mul, neg_zero] at hdetC
    exact zero_ne_one hdetC
  have hδw : δ • w = w := by
    apply UpperHalfPlane.ext
    show ((δ • w : UpperHalfPlane) : ℂ) = w
    rw [h36t_coe_smul, hc, hb, hda, zero_mul, zero_add, add_zero]
    exact mul_div_cancel_left₀ _ ha
  have hmul : δ₁ • w = δ₀ • (δ • w) := by rw [hδ, smul_smul, mul_inv_cancel_left]
  rw [hmul, hδw]

/-- **D1**: if the two lifts have extensions agreeing on `ℝ̂`, the deck elements conjugate to the
same `γ` act identically on `ℍ`. -/
theorem h36t_deck_agree {F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₀ G₁ : ExtPlane → ExtPlane}
    (hG₀ : IsHomeoExtension (liftToC F₀) upperHalf upperHalf G₀)
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁) (hbd : ∀ x ∈ extRealLine, G₀ x = G₁ x)
    {γ δ₀ δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h₀ : ∀ τ, F₀ (γ • τ) = δ₀ • F₀ τ)
    (h₁ : ∀ τ, F₁ (γ • τ) = δ₁ • F₁ τ) (w : UpperHalfPlane) : δ₀ • w = δ₁ • w := by
  refine h36t_smul_eq_of_extRealLine (fun y hy => ?_) w
  rw [← h36t_image_extRealLine hG₀] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxc := h36t_extRealLine_subset_closure hx
  have hγx : mobiusSL (slRealToComplex γ) x ∈ extRealLine := k24_real_mapsTo_extRealLine γ hx
  rw [← h36t_ext_equivariant hG₀ h₀ hxc, hbd _ hγx, h36t_ext_equivariant hG₁ h₁ hxc, hbd x hx]

/-- **Fibres.**  If `F₁ γ F₁⁻¹ = F₂ γ F₂⁻¹` on `ℍ` for all `γ ∈ Γ₀`, the fibres of `p₁` lie in those of `p₂`: for
`δ ∈ Γ₁`, `F₁⁻¹ δ F₁` lifts the identity of `X₀`, so it is some `γ ∈ Γ₀` (`h23l_lifts_differ`), and
`δ = F₁ γ F₁⁻¹ = F₂ γ F₂⁻¹` preserves the fibres of `p₂`. -/
theorem s27l_fiber_transfer {X₀ X₁ X₂ : Type*} [TopologicalSpace X₀] [ChartedSpace ℂ X₀] [TopologicalSpace X₁]
    [ChartedSpace ℂ X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → X₀} {p₁ : UpperHalfPlane → X₁}
    {p₂ : UpperHalfPlane → X₂} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁) {f₁ : X₀ ≃ₜ X₁}
    {f₂ : X₀ → X₂} {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF₁ : IsLift p₀ p₁ f₁ F₁)
    (hF₂ : IsLift p₀ p₂ f₂ F₂) (hag : ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ))
    (τ τ' : UpperHalfPlane) (h : p₁ τ = p₁ τ') : p₂ τ = p₂ τ' := by
  obtain ⟨δ, hδ, rfl⟩ := (hp₁.2.2.2 τ τ').1 h
  have hp₀F : ∀ w, p₀ (F₁.symm w) = f₁.symm (p₁ w) := fun w => by
    have h' := hF₁ (F₁.symm w)
    rw [F₁.apply_symm_apply] at h'
    rw [h', f₁.symm_apply_apply]
  obtain ⟨γ, hγ, hγe⟩ := h23l_lifts_differ hp₀ (F₁ := fun σ => F₁.symm (δ • F₁ σ)) (F₂ := id)
    (F₁.symm.continuous.comp ((continuous_const_smul δ).comp F₁.continuous)) continuous_id (fun σ => by
      show p₀ (F₁.symm (δ • F₁ σ)) = p₀ σ
      rw [hp₀F, ← (hp₁.2.2.2 (F₁ σ) (δ • F₁ σ)).2 ⟨δ, hδ, rfl⟩, ← hp₀F, F₁.symm_apply_apply])
  have hγe' : ∀ σ, F₁.symm (δ • F₁ σ) = γ • σ := hγe
  have hδτ : δ • τ = F₂ (γ • F₂.symm τ) := by
    rw [← hag γ hγ τ, ← hγe' (F₁.symm τ), F₁.apply_symm_apply, F₁.apply_symm_apply]
  rw [hδτ, hF₂, ← (hp₀.2.2.2 (F₂.symm τ) (γ • F₂.symm τ)).2 ⟨γ, hγ, rfl⟩, ← hF₂, F₂.apply_symm_apply]

/-- **Descent is holomorphic.**  If `c ∘ p = q` with `p` a holomorphic covering and `q` holomorphic, then `c` is
holomorphic: near `p τ`, `c = q ∘ ψ⁻¹ ∘ φ_{p τ}` where `ψ = φ_{p τ} ∘ p` is conformal near `τ` (`h23l_chart_proj`,
Theorem 7.3), so its inverse is holomorphic. -/
theorem s27l_mdifferentiable_descend {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {p : UpperHalfPlane → X} {q : UpperHalfPlane → Y}
    (hcov : IsCoveringMap p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hsurj : Function.Surjective p)
    (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q) {c : X → Y} (hc : ∀ τ, c (p τ) = q τ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c := by
  intro x
  obtain ⟨τ, rfl⟩ := hsurj x
  obtain ⟨U, hUo, hτU, hUH, hUs, hψ⟩ :=
    h23l_chart_proj (τ := τ) hcov hhol _ (mem_chart_source ℂ _)
  have hconf := thm7_3_one_qc_conformal hψ
  set φ : ℂ → ℂ := fun z => chartAt ℂ (p τ) (p (UpperHalfPlane.ofComplex z)) with hφ
  have hVo : IsOpen (φ '' U) := hconf.isOpen hUo
  have hφτ : φ (τ : ℂ) = chartAt ℂ (p τ) (p τ) := by
    simp only [hφ, UpperHalfPlane.ofComplex_apply]
  have hW : (chartAt ℂ (p τ)).source ∩ chartAt ℂ (p τ) ⁻¹' (φ '' U) ∈ 𝓝 (p τ) := by
    refine ((chartAt ℂ (p τ)).continuousOn.isOpen_inter_preimage (chartAt ℂ (p τ)).open_source
      hVo).mem_nhds ⟨mem_chart_source ℂ (p τ), ?_⟩
    rw [mem_preimage, ← hφτ]
    exact mem_image_of_mem φ hτU
  have heq : c =ᶠ[𝓝 (p τ)]
      fun y => q (UpperHalfPlane.ofComplex (Function.invFunOn φ U (chartAt ℂ (p τ) y))) := by
    filter_upwards [hW] with y hy
    obtain ⟨w, hw, hwy⟩ := hy.2
    have hψw : Function.invFunOn φ U (chartAt ℂ (p τ) y) = w := by
      rw [← hwy]
      exact hconf.2.1.leftInvOn_invFunOn hw
    have hpw : p (UpperHalfPlane.ofComplex w) = y := (chartAt ℂ (p τ)).injOn (hUs w hw) hy.1 hwy
    show c y = q (UpperHalfPlane.ofComplex (Function.invFunOn φ U (chartAt ℂ (p τ) y)))
    rw [hψw, ← hc, hpw]
  have hψτ : Function.invFunOn φ U (chartAt ℂ (p τ) (p τ)) = (τ : ℂ) := by
    rw [← hφτ]
    exact hconf.2.1.leftInvOn_invFunOn hτU
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (p τ)) (p τ) :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ (p τ)) (mem_chart_source ℂ (p τ))
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn φ U) (chartAt ℂ (p τ) (p τ)) := by
    rw [← hφτ]
    exact mdifferentiableAt_iff_differentiableAt.2 (hconf.differentiableAt_invFunOn hUo hτU)
  have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) UpperHalfPlane.ofComplex
      (Function.invFunOn φ U (chartAt ℂ (p τ) (p τ))) := by
    rw [hψτ]
    exact UpperHalfPlane.mdifferentiableAt_ofComplex τ.coe_im_pos
  have h4 := hq (UpperHalfPlane.ofComplex (Function.invFunOn φ U (chartAt ℂ (p τ) (p τ))))
  exact (h4.comp (p τ) (h3.comp (p τ) (h2.comp (p τ) h1))).congr_of_eventuallyEq heq

/-- **Descent of the identity.**  If two uniformizations `p₁`, `p₂` have the same fibres, the identity of `ℍ` descends
to a biholomorphic homeomorphism `c` with `c ∘ p₁ = p₂` (`c = p₂ ∘ s₁` for a section `s₁` of `p₁`, holomorphic by
`s27l_mdifferentiable_descend`, with inverse `p₁ ∘ s₂`). -/
theorem s27l_descend_homeomorph {X₁ X₂ : Type*} [TopologicalSpace X₁] [ChartedSpace ℂ X₁]
    [IsManifold 𝓘(ℂ) ω X₁] [TopologicalSpace X₂] [ChartedSpace ℂ X₂] [IsManifold 𝓘(ℂ) ω X₂]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → X₁} {p₂ : UpperHalfPlane → X₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    (h12 : ∀ τ τ', p₁ τ = p₁ τ' → p₂ τ = p₂ τ') (h21 : ∀ τ τ', p₂ τ = p₂ τ' → p₁ τ = p₁ τ') :
    ∃ c : X₁ ≃ₜ X₂, IsBiholomorphic c ∧ ∀ τ, c (p₁ τ) = p₂ τ := by
  have hs₁ : ∀ x, p₁ (Function.surjInv hp₁.2.2.1 x) = x := Function.surjInv_eq hp₁.2.2.1
  have hs₂ : ∀ y, p₂ (Function.surjInv hp₂.2.2.1 y) = y := Function.surjInv_eq hp₂.2.2.1
  have hc : ∀ τ, p₂ (Function.surjInv hp₁.2.2.1 (p₁ τ)) = p₂ τ := fun τ => h12 _ _ (hs₁ (p₁ τ))
  have hc' : ∀ τ, p₁ (Function.surjInv hp₂.2.2.1 (p₂ τ)) = p₁ τ := fun τ => h21 _ _ (hs₂ (p₂ τ))
  have hcd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => p₂ (Function.surjInv hp₁.2.2.1 x)) :=
    s27l_mdifferentiable_descend (c := fun x => p₂ (Function.surjInv hp₁.2.2.1 x)) hp₁.1 hp₁.2.1 hp₁.2.2.1
      hp₂.2.1 hc
  have hcd' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun y => p₁ (Function.surjInv hp₂.2.2.1 y)) :=
    s27l_mdifferentiable_descend (c := fun y => p₁ (Function.surjInv hp₂.2.2.1 y)) hp₂.1 hp₂.2.1 hp₂.2.2.1
      hp₁.2.1 hc'
  have hl : Function.LeftInverse (fun y => p₁ (Function.surjInv hp₂.2.2.1 y))
      (fun x => p₂ (Function.surjInv hp₁.2.2.1 x)) := fun x => by
    obtain ⟨τ, rfl⟩ := hp₁.2.2.1 x
    show p₁ (Function.surjInv hp₂.2.2.1 (p₂ (Function.surjInv hp₁.2.2.1 (p₁ τ)))) = p₁ τ
    rw [hc, hc']
  have hr : Function.RightInverse (fun y => p₁ (Function.surjInv hp₂.2.2.1 y))
      (fun x => p₂ (Function.surjInv hp₁.2.2.1 x)) := fun y => by
    obtain ⟨τ, rfl⟩ := hp₂.2.2.1 y
    show p₂ (Function.surjInv hp₁.2.2.1 (p₁ (Function.surjInv hp₂.2.2.1 (p₂ τ)))) = p₂ τ
    rw [hc', hc]
  exact ⟨⟨⟨_, _, hl, hr⟩, hcd.continuous, hcd'.continuous⟩, ⟨hcd, _, hcd', hl, hr⟩, hc⟩

/-- **Bounded displacement.**  A continuous `Φ : ℍ → ℍ` commuting with the covering group of a compact surface moves
points a bounded hyperbolic distance: `dist (Φ τ) τ` is `Γ`-invariant and a compact set meets every orbit. -/
theorem s27l_bounded_displacement {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} (hp : IsUniformization Γ p)
    {Φ : UpperHalfPlane → UpperHalfPlane} (hΦc : Continuous Φ) (hΦ : ∀ γ ∈ Γ, ∀ τ, Φ (γ • τ) = γ • Φ τ) :
    ∃ D : ℝ, ∀ τ, dist (Φ τ) τ ≤ D := by
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp
  obtain ⟨D, hD⟩ := (hK.image (hΦc.dist continuous_id)).isBounded.bddAbove
  refine ⟨D, fun τ => ?_⟩
  obtain ⟨γ, hγ, hγτ⟩ := hKz τ
  have hinv : dist (Φ (γ • τ)) (γ • τ) = dist (Φ τ) τ := by rw [hΦ γ hγ τ, dist_smul]
  rw [← hinv]
  exact hD ⟨γ • τ, hγτ, rfl⟩

/-- A sequence of complex numbers whose norms tend to `∞` tends to `∞` in `ℂ̄`. -/
theorem s27l_tendsto_extInf {w : ℕ → ℂ} (h : Tendsto (fun n => ‖w n‖) atTop atTop) :
    Tendsto (fun n => ((w n : ℂ) : ExtPlane)) atTop (𝓝 extInf) := by
  have h1 : Tendsto w atTop (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 h
  rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact] at h1
  exact OnePoint.tendsto_coe_infty.comp h1

/-- A sequence of points of `ℍ` converging in `ℂ̄` converges within the closed half-plane. -/
theorem s27l_tendsto_within {u : ℕ → UpperHalfPlane} {ξ : ExtPlane}
    (hu : Tendsto (fun n => (((u n : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝 ξ)) :
    Tendsto (fun n => (((u n : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝[closure (toExt upperHalf)] ξ) :=
  tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall fun n => subset_closure ⟨_, (u n).coe_im_pos, rfl⟩⟩

/-- If `F₂ ∘ Φ = N ∘ F₁` and `u n → ξ`, `Φ (u n) → ξ` for a point `ξ` of the closed half-plane, the extensions satisfy
`G₂ ξ = N (G₁ ξ)` (continuity of `G₁`, `G₂` and `N` at `ξ`, uniqueness of limits). -/
theorem s27l_ext_eq_of_seq {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁)
    (hG₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf G₂) {N : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {Φ : UpperHalfPlane → UpperHalfPlane} (hΦ : ∀ τ, F₂ (Φ τ) = N • F₁ τ) {ξ : ExtPlane}
    (hξ : ξ ∈ closure (toExt upperHalf)) {u : ℕ → UpperHalfPlane}
    (hu : Tendsto (fun n => (((u n : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝 ξ))
    (hΦu : Tendsto (fun n => (((Φ (u n) : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝 ξ)) :
    G₂ ξ = mobiusSL (slRealToComplex N) (G₁ ξ) := by
  have h1 : Tendsto (fun n => G₂ (((Φ (u n) : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝 (G₂ ξ)) :=
    (hG₂.2.1 ξ hξ).tendsto.comp (s27l_tendsto_within hΦu)
  have h2 : Tendsto (fun n => mobiusSL (slRealToComplex N) (G₁ (((u n : UpperHalfPlane) : ℂ) : ExtPlane))) atTop
      (𝓝 (mobiusSL (slRealToComplex N) (G₁ ξ))) :=
    ((k22_t_continuous _).tendsto _).comp ((hG₁.2.1 ξ hξ).tendsto.comp (s27l_tendsto_within hu))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  show mobiusSL (slRealToComplex N) (G₁ (((u n : UpperHalfPlane) : ℂ) : ExtPlane)) =
    G₂ (((Φ (u n) : UpperHalfPlane) : ℂ) : ExtPlane)
  rw [h36t_ext_coe hG₁, h36t_mobiusSL_coe, ← hΦ, h36t_ext_coe hG₂]

/-- **Bounded displacement fixes the boundary.**  If `Φ : ℍ → ℍ` moves points by at most `D` and `F₂ ∘ Φ = N ∘ F₁`,
then `G₂ = N ∘ G₁` on `ℝ̂`: along `u n = x + i/(n+1)` (resp. `u n = (n+1) i`) both `u n` and `Φ (u n)` tend to `x`
(resp. `∞`), by `dist_coe_le` (resp. `im_div_exp_dist_le`). -/
theorem s27l_ext_eq_of_bounded {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf G₁)
    (hG₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf G₂) {N : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {Φ : UpperHalfPlane → UpperHalfPlane} (hΦ : ∀ τ, F₂ (Φ τ) = N • F₁ τ) {D : ℝ}
    (hD : ∀ τ, dist (Φ τ) τ ≤ D) :
    (∀ x : ℝ, G₂ ((x : ℂ) : ExtPlane) = mobiusSL (slRealToComplex N) (G₁ ((x : ℂ) : ExtPlane))) ∧
      G₂ extInf = mobiusSL (slRealToComplex N) (G₁ extInf) := by
  constructor
  · intro x
    have hpos : ∀ n : ℕ, 0 < ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im := fun n => by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add]
      positivity
    set u : ℕ → UpperHalfPlane := fun n => ⟨(x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I, hpos n⟩
      with hu
    have huim : ∀ n, (u n).im = 1 / ((n : ℝ) + 1) := fun n => by
      show ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im = _
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hu1 : Tendsto (fun n => ((u n : UpperHalfPlane) : ℂ)) atTop (𝓝 (x : ℂ)) := by
      have h := (((Complex.continuous_ofReal.tendsto 0).comp ht).mul_const Complex.I).const_add (x : ℂ)
      rw [Complex.ofReal_zero, zero_mul, add_zero] at h
      exact h
    have hsmall : Tendsto (fun n => ((Φ (u n) : UpperHalfPlane) : ℂ) - ((u n : UpperHalfPlane) : ℂ)) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1) * (Real.exp D - 1)) (fun n => ?_) ?_
      · rw [← dist_eq_norm, ← huim n]
        refine (UpperHalfPlane.dist_coe_le (Φ (u n)) (u n)).trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.2 (hD (u n))]) (u n).im_pos.le
      · have h := ht.mul_const (Real.exp D - 1)
        rwa [zero_mul] at h
    have hu2 : Tendsto (fun n => ((Φ (u n) : UpperHalfPlane) : ℂ)) atTop (𝓝 (x : ℂ)) := by
      have h := hsmall.add hu1
      rw [zero_add] at h
      exact h.congr fun n => sub_add_cancel _ _
    have hv1 : Tendsto (fun n => (((u n : UpperHalfPlane) : ℂ) : ExtPlane)) atTop (𝓝 ((x : ℂ) : ExtPlane)) :=
      (OnePoint.continuous_coe.tendsto _).comp hu1
    have hv2 : Tendsto (fun n => (((Φ (u n) : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
        (𝓝 ((x : ℂ) : ExtPlane)) :=
      (OnePoint.continuous_coe.tendsto _).comp hu2
    exact s27l_ext_eq_of_seq hG₁ hG₂ hΦ
      (h36t_extRealLine_subset_closure (Or.inl ⟨(x : ℂ), Complex.ofReal_im x, rfl⟩)) hv1 hv2
  · have hpos : ∀ n : ℕ, 0 < ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im := fun n => by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
        zero_mul, add_zero]
      positivity
    set u : ℕ → UpperHalfPlane := fun n => ⟨(((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I, hpos n⟩ with hu
    have huim : ∀ n, (u n).im = (n : ℝ) + 1 := fun n => by
      show ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im = _
      simp
    have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hu1 : Tendsto (fun n => ‖((u n : UpperHalfPlane) : ℂ)‖) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) hN
      rw [← huim n]
      exact Complex.im_le_norm _
    have hu2 : Tendsto (fun n => ‖((Φ (u n) : UpperHalfPlane) : ℂ)‖) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) (hN.atTop_div_const (Real.exp_pos D))
      have h1 := UpperHalfPlane.im_div_exp_dist_le (u n) (Φ (u n))
      rw [huim n, dist_comm] at h1
      have h2 : ((n : ℝ) + 1) / Real.exp D ≤ ((n : ℝ) + 1) / Real.exp (dist (Φ (u n)) (u n)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) (Real.exp_le_exp.2 (hD (u n)))
      exact h2.trans (h1.trans (Complex.im_le_norm _))
    exact s27l_ext_eq_of_seq hG₁ hG₂ hΦ (h36t_extRealLine_subset_closure (Or.inr rfl))
      (s27l_tendsto_extInf hu1) (s27l_tendsto_extInf hu2)

/-- **Theorem 27.1**: two marked Riemann surfaces `(S₁, f₁)`, `(S₂, f₂)` are equivalent iff the
normalized lifts of `f₁` and `f₂` have the same values on `ℝ`. -/
theorem thm27_1 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (m₁ m₂ : MarkedRS S₀)
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → m₁.X.carrier}
    {p₂ : UpperHalfPlane → m₂.X.carrier} (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {G₁ G₂ : ExtPlane → ExtPlane}
    (h₁ : IsNormalizedLift p₀ p₁ m₁.marking F₁ G₁) (h₂ : IsNormalizedLift p₀ p₂ m₂.marking F₂ G₂) :
    m₁.Equiv m₂ ↔ ∀ x : ℝ, G₁ ((x : ℂ) : ExtPlane) = G₂ ((x : ℂ) : ExtPlane) := by
  have _ := hg
  have _ := hS
  obtain ⟨hF₁, hG₁, h0₁, h1₁, hinf₁⟩ := h₁
  obtain ⟨hF₂, hG₂, h0₂, h1₂, hinf₂⟩ := h₂
  constructor
  · -- `⇒`: the lift of `c` is Möbius; normalized by Theorem 23.1, `Φ = F₂⁻¹ N F₁` commutes with `Γ₀`
    rintro ⟨c, hc, hhom⟩
    obtain ⟨τ₂, hτ₂⟩ := hp₂.2.2.1 (c (p₁ UpperHalfPlane.I))
    obtain ⟨C, hC, -⟩ := exists_lift hp₁ hp₂ c UpperHalfPlane.I τ₂ hτ₂
    obtain ⟨M, hM⟩ := utm_eq_smul_of_isKQC_one C
      (h23l_lift_isKQC hp₁ hp₂ ((isKQCRS_one_iff c).2 hc) hC)
    have hL : IsLift p₀ p₂ (m₁.marking.trans c) (F₁.trans C) := fun τ => by
      show p₂ (C (F₁ τ)) = c (m₁.marking (p₀ τ))
      rw [hC, hF₁]
    obtain ⟨γ₂, -, hrel⟩ := (thm23_1_homotopy_iff hp₀ hp₂ (m₁.marking.trans c) m₂.marking hL hF₂).1 hhom
    obtain ⟨N, hN⟩ : ∃ N : Matrix.SpecialLinearGroup (Fin 2) ℝ, N = γ₂⁻¹ * M := ⟨_, rfl⟩
    have hΦF : ∀ τ, F₂ (F₂.symm (N • F₁ τ)) = N • F₁ τ := fun τ => F₂.apply_symm_apply _
    have hΦc : Continuous fun τ => F₂.symm (N • F₁ τ) :=
      F₂.symm.continuous.comp ((continuous_const_smul N).comp F₁.continuous)
    have hΦγ : ∀ γ ∈ Γ₀, ∀ τ, F₂.symm (N • F₁ (γ • τ)) = γ • F₂.symm (N • F₁ τ) := by
      intro γ hγ τ
      have h := hrel γ hγ (C (F₁ τ))
      have e1 : (F₁.trans C).symm (C (F₁ τ)) = τ := (F₁.trans C).symm_apply_apply τ
      have e2 : γ₂⁻¹ • C (F₁ τ) = N • F₁ τ := by rw [hM, hN, mul_smul]
      rw [e1, e2] at h
      have h' : M • F₁ (γ • τ) = γ₂ • F₂ (γ • F₂.symm (N • F₁ τ)) := by
        rw [← hM]
        exact h
      have h'' : N • F₁ (γ • τ) = F₂ (γ • F₂.symm (N • F₁ τ)) := by
        calc N • F₁ (γ • τ) = γ₂⁻¹ • M • F₁ (γ • τ) := by rw [hN, mul_smul]
          _ = F₂ (γ • F₂.symm (N • F₁ τ)) := by rw [h', inv_smul_smul]
      rw [h'', F₂.symm_apply_apply]
    obtain ⟨D, hD⟩ := s27l_bounded_displacement hp₀ hΦc hΦγ
    obtain ⟨hreal, hinfty⟩ := s27l_ext_eq_of_bounded hG₁ hG₂ hΦF hD
    -- `N` fixes `0`, `1`, `∞`, so it is the identity
    have e0 := hreal 0
    have e1 := hreal 1
    rw [Complex.ofReal_zero, h0₁, h0₂] at e0
    rw [Complex.ofReal_one, h1₁, h1₂] at e1
    rw [hinf₁, hinf₂] at hinfty
    have hid := (s27l_fix3 hinfty.symm e0.symm e1.symm).1
    intro x
    rw [hreal x, hid]
  · -- `⇐`: `F₁ γ F₁⁻¹ = F₂ γ F₂⁻¹`, so the identity of `ℍ` descends to a biholomorphic `c`, and `c ∘ f₁ ≃ f₂`
    intro hbd
    have hbd' : ∀ y ∈ extRealLine, G₁ y = G₂ y := by
      rintro _ (⟨z, hz, rfl⟩ | hy)
      · have hz' : z = ((z.re : ℝ) : ℂ) :=
          Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hz)
        rw [hz']
        exact hbd z.re
      · rw [mem_singleton_iff.1 hy, hinf₁, hinf₂]
    have hag : ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
      intro γ hγ τ
      obtain ⟨δ₁, -, hδ₁⟩ := h23l_deck hp₀ hp₁ hF₁ hγ
      obtain ⟨δ₂, -, hδ₂⟩ := h23l_deck hp₀ hp₂ hF₂ hγ
      rw [hδ₁, hδ₂, F₁.apply_symm_apply, F₂.apply_symm_apply]
      exact h36t_deck_agree hG₁ hG₂ hbd' hδ₁ hδ₂ τ
    obtain ⟨c, hc, hcp⟩ := s27l_descend_homeomorph hp₁ hp₂
      (s27l_fiber_transfer hp₀ hp₁ hF₁ hF₂ hag)
      (s27l_fiber_transfer hp₀ hp₂ hF₂ hF₁ fun γ hγ τ => (hag γ hγ τ).symm)
    refine ⟨c, hc, ?_⟩
    have hL : IsLift p₀ p₂ (m₁.marking.trans c) F₁ := fun τ => by
      show p₂ (F₁ τ) = c (m₁.marking (p₀ τ))
      rw [← hF₁, hcp]
    refine (thm23_1_homotopy_iff hp₀ hp₂ (m₁.marking.trans c) m₂.marking hL hF₂).2
      ⟨1, Γ₂.one_mem, fun γ hγ τ => ?_⟩
    rw [inv_one, one_smul, one_smul]
    exact hag γ hγ τ

/-! ### Standard generators and the Fricke space -/

/-- The commutator γ δ γ⁻¹ δ⁻¹. -/
def commutatorSL (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  γ * δ * γ⁻¹ * δ⁻¹

/-- Γ is cocompact: ℍ/Γ is compact. -/
def IsCocompact (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  ∃ C : Set UpperHalfPlane, IsCompact C ∧ ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C

/-- §27.1 (标准生成元组).  A standard system of generators `γ₁, δ₁, …, γ_g, δ_g` of a Fuchsian group
`G₀` uniformizing a closed surface of genus `g` (lifted from `α₁, β₁, …, α_g, β_g ∈ π₁(S₀, p₀)`):
they generate `G₀`, satisfy the relation (27.4)
`γ₁ δ₁ γ₁⁻¹ δ₁⁻¹ ⋯ γ_g δ_g γ_g⁻¹ δ_g⁻¹ = I` (as matrices `= ±I`), and the normalization (27.5):
`δ_g(z) = λz` with `λ > 1` (`0` repelling, `∞` attracting) and `γ_g(1) = 1`.

**Correction (2026-09-26).**  (1) `generate` asked the generators to generate the matrix group `Γ` exactly, but a
uniformization's `Γ` may contain `-1`, which a standard system never generates (surface groups are Hopfian and the
lifted relation (27.4) is `+1` by Euler-class parity): `exists_standardGenerators` and `exists_inducedGenerators`
were **false**.  Generation is now modulo `±1`, i.e. of the Fuchsian group as Möbius maps, as the book means it.
(2) Nothing tied the number of pairs to the genus, so a system could be padded with a trivial last pair
`(1, δ_g)`, and `eq27_9_14_last_determined` and `eq27_12_d_ne_one` were **false**.  The new field `alternate` is
the book's remark after (27.5) that the fixed points of `γ_g` and `δ_g` alternate on `ℝ̂`. -/
structure StandardGenerators (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (g : ℕ) where
  /-- The pairs `(γⱼ, δⱼ)`, `j = 1, …, g - 1`. -/
  first : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ
  /-- `γ_g`. -/
  γg : Matrix.SpecialLinearGroup (Fin 2) ℝ
  /-- `δ_g`. -/
  δg : Matrix.SpecialLinearGroup (Fin 2) ℝ
  first_mem : ∀ j, (first j).1 ∈ Γ ∧ (first j).2 ∈ Γ
  γg_mem : γg ∈ Γ
  δg_mem : δg ∈ Γ
  generate : Subgroup.closure (range (fun j => (first j).1) ∪ range (fun j => (first j).2) ∪ {γg, δg}) ⊔
      Subgroup.zpowers (-1) = Γ ⊔ Subgroup.zpowers (-1)
  /-- (27.4). -/
  relation : (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = 1 ∨
    (List.ofFn fun j => commutatorSL (first j).1 (first j).2).prod * commutatorSL γg δg = -1
  /-- (27.5): `δ_g(z) = λ z`, `λ = (δ_g)₀₀² > 1`. -/
  δg_diagonal : δg 0 1 = 0 ∧ δg 1 0 = 0 ∧ 1 < δg 0 0 ^ 2
  /-- (27.5): `γ_g(1) = 1`. -/
  γg_fixes_one : γg 0 0 + γg 0 1 = γg 1 0 + γg 1 1
  /-- The fixed points of `γ_g` and `δ_g` alternate on `ℝ̂` (the remark after (27.5): `α_g`, `β_g` meet once):
  for `γ_g = (a b; c d)` the fixed points of `γ_g` have product `-b/c < 0`, so they separate `0` and `∞`. -/
  alternate : 0 < γg 0 1 * γg 1 0

-- exists_standardGenerators is stated and proved in LiZhongQC/Lemmas/StdGenSystem.lean
-- (it needs the standard-generator construction of StdGenSystem, built on top of this file).

/-- The Fricke coordinates `(σ, τ, λ)` of a hyperbolic transformation with finite fixed points. -/
def frickeTriple (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ × ℝ × ℝ :=
  ((extToC (attractingFixedPoint γ)).re, (extToC (repellingFixedPoint γ)).re, multiplier γ)

/-- §27.1: the Fricke coordinates `(σ₁, τ₁, λ₁, …, σ_{2g-2}, τ_{2g-2}, λ_{2g-2}) ∈ ℝ^{6g-6}` of a
standard system of generators: the coordinates of `γ₁, δ₁, …, γ_{g-1}, δ_{g-1}` (`γ_g` and `δ_g`
being determined by them). -/
def frickeCoordinates {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ}
    (G : StandardGenerators Γ g) : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) :=
  fun j => (frickeTriple (G.first j).1, frickeTriple (G.first j).2)

/-- The entries of a product in `SL(2, ℝ)`. -/
theorem s27t_mul_apply (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The entries of an inverse in `SL(2, ℝ)`: `(a b; c d)⁻¹ = (d -b; -c a)`. -/
theorem s27t_inv_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- The entries of `-A` in `SL(2, ℝ)`. -/
theorem s27t_neg_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) : (-A) i j = -(A i j) := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

/-- For diagonal `D`, the diagonal entries of `M = D γ D⁻¹ γ⁻¹`. -/
theorem s27t_M_entries (γ D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h01 : D 0 1 = 0) (h10 : D 1 0 = 0) :
    (D * γ * D⁻¹ * γ⁻¹) 0 0 = γ 0 0 * γ 1 1 - D 0 0 ^ 2 * (γ 0 1 * γ 1 0) ∧
    (D * γ * D⁻¹ * γ⁻¹) 1 1 = γ 0 0 * γ 1 1 - D 1 1 ^ 2 * (γ 0 1 * γ 1 0) := by
  have hdetD : D 0 0 * D 1 1 = 1 := by
    have h := hnf_sl2_det D
    rw [h01, h10] at h
    linarith
  obtain ⟨i00, i01, i10, i11⟩ := s27t_inv_apply D
  obtain ⟨j00, j01, j10, j11⟩ := s27t_inv_apply γ
  simp only [s27t_mul_apply, i00, i01, i10, i11, j00, j01, j10, j11, h01, h10]
  constructor
  · linear_combination (γ 0 0 * γ 1 1) * hdetD
  · linear_combination (γ 0 0 * γ 1 1) * hdetD

/-- `[γ, D]⁻¹ = D γ D⁻¹ γ⁻¹`. -/
theorem s27t_comm_inv (γ D : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (commutatorSL γ D)⁻¹ = D * γ * D⁻¹ * γ⁻¹ := by
  simp only [commutatorSL]
  group

/-- The determinant of a diagonal `D` with `D₀₀² > 1`, then `D₁₁² < 1` and `D₀₀ ≠ D₁₁`. -/
theorem s27t_diag_facts {D : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2) :
    D 0 0 * D 1 1 = 1 ∧ D 1 1 ^ 2 < 1 ∧ D 0 0 ≠ D 1 1 := by
  obtain ⟨h01, h10, h00⟩ := hD
  have hdetD : D 0 0 * D 1 1 = 1 := by
    have h := hnf_sl2_det D
    rw [h01, h10] at h
    linarith
  refine ⟨hdetD, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h1 : (D 0 0 * D 1 1) ^ 2 = 1 := by rw [hdetD]; norm_num
    nlinarith [h1, hcon, h00, mul_le_mul_of_nonneg_left hcon (le_of_lt (lt_trans one_pos h00))]
  · intro h
    rw [← h] at hdetD
    nlinarith [hdetD, h00]

/-- **The key inequality** (FIX-C): if the fixed points of `γ` and of the diagonal `D` alternate (`0 < bc`), then
`([γ, D]⁻¹)₁₁ = 1 + bc(1 - D₁₁²) > 1`. -/
theorem s27t_comm_inv_11 (γ D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2)
    (halt : 0 < γ 0 1 * γ 1 0) : 1 < (commutatorSL γ D)⁻¹ 1 1 := by
  rw [s27t_comm_inv, (s27t_M_entries γ D hD.1 hD.2.1).2]
  obtain ⟨-, hD11, -⟩ := s27t_diag_facts hD
  have hdetγ := hnf_sl2_det γ
  have hpos := mul_pos halt (sub_pos.2 hD11)
  nlinarith [hpos, hdetγ]

/-- The relation `η C = ±1` gives `η = ±C⁻¹`. -/
theorem s27t_eta_eq {η C : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : η * C = 1 ∨ η * C = -1) :
    η = C⁻¹ ∨ η = -C⁻¹ := by
  rcases h with h | h
  · exact Or.inl (eq_inv_of_mul_eq_one_left h)
  · right
    calc η = η * C * C⁻¹ := (mul_inv_cancel_right η C).symm
      _ = -1 * C⁻¹ := by rw [h]
      _ = -C⁻¹ := neg_one_mul _

/-- **Core of (27.9)–(27.14)**: the same `η`, two normalized last pairs `(γ, D)`, `(γ', D')` whose fixed points
alternate.  The same `η` forces the same sign in the relation, hence `[γ, D]⁻¹ = [γ', D']⁻¹`; then
`D₀₀² (1 - M₁₁) = M₀₀ - 1` gives `D₀₀² = D'₀₀²`, `D = ±D'`; `N = γ'⁻¹ γ` commutes with `D`, hence is diagonal, and
`γ(1) = 1 = γ'(1)` forces `N = ±1`. -/
theorem s27t_last_pair_core {η γ D γ' D' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2) (hD' : D' 0 1 = 0 ∧ D' 1 0 = 0 ∧ 1 < D' 0 0 ^ 2)
    (hrel : η * commutatorSL γ D = 1 ∨ η * commutatorSL γ D = -1)
    (hrel' : η * commutatorSL γ' D' = 1 ∨ η * commutatorSL γ' D' = -1)
    (hfix : γ 0 0 + γ 0 1 = γ 1 0 + γ 1 1) (hfix' : γ' 0 0 + γ' 0 1 = γ' 1 0 + γ' 1 1)
    (halt : 0 < γ 0 1 * γ 1 0) (halt' : 0 < γ' 0 1 * γ' 1 0) :
    (D = D' ∨ D = -D') ∧ (γ = γ' ∨ γ = -γ') := by
  obtain ⟨hdetD, hD11, hD0011⟩ := s27t_diag_facts hD
  obtain ⟨hdetD', hD'11, -⟩ := s27t_diag_facts hD'
  have hM := s27t_comm_inv_11 γ D hD halt
  have hM' := s27t_comm_inv_11 γ' D' hD' halt'
  -- the same `η` forces the same sign, hence `C⁻¹ = C'⁻¹`
  have hCC : (commutatorSL γ D)⁻¹ = (commutatorSL γ' D')⁻¹ := by
    rcases s27t_eta_eq hrel with h1 | h1 <;> rcases s27t_eta_eq hrel' with h2 | h2
    · exact h1.symm.trans h2
    · exfalso
      have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 1 1) (h1.symm.trans h2)
      simp only [s27t_neg_apply] at e
      linarith
    · exfalso
      have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 1 1) (h1.symm.trans h2)
      simp only [s27t_neg_apply] at e
      linarith
    · exact neg_inj.1 (h1.symm.trans h2)
  rw [s27t_comm_inv, s27t_comm_inv] at hCC
  rw [s27t_comm_inv] at hM hM'
  -- `μ² (1 - M₁₁) = M₀₀ - 1` for both pairs
  obtain ⟨e00, e11⟩ := s27t_M_entries γ D hD.1 hD.2.1
  obtain ⟨e00', e11'⟩ := s27t_M_entries γ' D' hD'.1 hD'.2.1
  have hdetγ := hnf_sl2_det γ
  have hdetγ' := hnf_sl2_det γ'
  have k1 : (D * γ * D⁻¹ * γ⁻¹) 0 0 - 1 = D 0 0 ^ 2 * (1 - (D * γ * D⁻¹ * γ⁻¹) 1 1) := by
    linear_combination e00 + D 0 0 ^ 2 * e11 + (1 + D 0 0 ^ 2) * hdetγ -
      (γ 0 1 * γ 1 0) * (D 0 0 * D 1 1 + 1) * hdetD
  have k1' : (D * γ * D⁻¹ * γ⁻¹) 0 0 - 1 = D' 0 0 ^ 2 * (1 - (D * γ * D⁻¹ * γ⁻¹) 1 1) := by
    rw [hCC]
    linear_combination e00' + D' 0 0 ^ 2 * e11' + (1 + D' 0 0 ^ 2) * hdetγ' -
      (γ' 0 1 * γ' 1 0) * (D' 0 0 * D' 1 1 + 1) * hdetD'
  have hsq : D 0 0 ^ 2 = D' 0 0 ^ 2 := by
    have h := k1.symm.trans k1'
    have hne : (1 - (D * γ * D⁻¹ * γ⁻¹) 1 1) ≠ 0 := by linarith
    exact mul_right_cancel₀ hne h
  have hD'00ne : D' 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdetD'
    simp at hdetD'
  -- `δ_g = ±δ_g'`
  have hδ : D = D' ∨ D = -D' := by
    apply hnf_sl2_eq_or_eq_neg
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · left
      refine ⟨h, by rw [hD.1, hD'.1], by rw [hD.2.1, hD'.2.1], ?_⟩
      have : D' 0 0 * (D 1 1 - D' 1 1) = 0 := by
        rw [h] at hdetD
        linear_combination hdetD - hdetD'
      have := (mul_eq_zero.1 this).resolve_left hD'00ne
      linarith
    · right
      refine ⟨h, by rw [hD.1, hD'.1]; simp, by rw [hD.2.1, hD'.2.1]; simp, ?_⟩
      have : D' 0 0 * (D 1 1 + D' 1 1) = 0 := by
        rw [h] at hdetD
        linear_combination -hdetD + hdetD'
      have := (mul_eq_zero.1 this).resolve_left hD'00ne
      linarith
  refine ⟨hδ, ?_⟩
  -- `D γ D⁻¹ γ⁻¹ = D γ' D⁻¹ γ'⁻¹`
  have hstar : D * γ * D⁻¹ * γ⁻¹ = D * γ' * D⁻¹ * γ'⁻¹ := by
    rw [hCC]
    rcases hδ with h | h
    · rw [h]
    · rw [h, inv_neg]
      simp only [neg_mul, mul_neg, neg_neg]
  have h3 : γ * D * γ⁻¹ = γ' * D * γ'⁻¹ := by
    calc γ * D * γ⁻¹ = (D⁻¹ * (D * γ * D⁻¹ * γ⁻¹))⁻¹ := by group
      _ = (D⁻¹ * (D * γ' * D⁻¹ * γ'⁻¹))⁻¹ := by rw [hstar]
      _ = γ' * D * γ'⁻¹ := by group
  -- `N = γ'⁻¹ γ` commutes with `D`, hence is diagonal
  have hND : (γ'⁻¹ * γ) * D = D * (γ'⁻¹ * γ) := by
    calc (γ'⁻¹ * γ) * D = γ'⁻¹ * (γ * D * γ⁻¹) * γ := by group
      _ = γ'⁻¹ * (γ' * D * γ'⁻¹) * γ := by rw [h3]
      _ = D * (γ'⁻¹ * γ) := by group
  generalize hN : γ'⁻¹ * γ = N at hND
  have hN01 : N 0 1 = 0 := by
    have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 0 1) hND
    simp only [s27t_mul_apply, hD.1] at e
    have : N 0 1 * (D 1 1 - D 0 0) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hD0011))
  have hN10 : N 1 0 = 0 := by
    have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 1 0) hND
    simp only [s27t_mul_apply, hD.2.1] at e
    have : N 1 0 * (D 0 0 - D 1 1) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hD0011)
  have hdetN : N 0 0 * N 1 1 = 1 := by
    have h := hnf_sl2_det N
    rw [hN01, hN10] at h
    linarith
  -- `γ = γ' N`, entrywise
  have hγN : γ = γ' * N := by rw [← hN, mul_inv_cancel_left]
  have f00 : γ 0 0 = γ' 0 0 * N 0 0 := by
    rw [hγN, s27t_mul_apply, hN10]; ring
  have f01 : γ 0 1 = γ' 0 1 * N 1 1 := by
    rw [hγN, s27t_mul_apply, hN01]; ring
  have f10 : γ 1 0 = γ' 1 0 * N 0 0 := by
    rw [hγN, s27t_mul_apply, hN10]; ring
  have f11 : γ 1 1 = γ' 1 1 * N 1 1 := by
    rw [hγN, s27t_mul_apply, hN01]; ring
  -- `γ(1) = 1` for both forces `N₀₀ = N₁₁`, hence `N = ±1`
  have hne : γ' 0 0 - γ' 1 0 ≠ 0 := by
    intro h0
    have h1 : γ' 1 1 = γ' 0 1 := by linarith
    have h2 : γ' 1 0 = γ' 0 0 := by linarith
    have : γ' 0 0 * γ' 1 1 - γ' 0 1 * γ' 1 0 = 0 := by rw [h1, h2]; ring
    rw [hdetγ'] at this
    norm_num at this
  have hrs : N 0 0 = N 1 1 := by
    have : (N 0 0 - N 1 1) * (γ' 0 0 - γ' 1 0) = 0 := by
      rw [f00, f01, f10, f11] at hfix
      linear_combination hfix - N 1 1 * hfix'
    have := (mul_eq_zero.1 this).resolve_right hne
    linarith
  have hr : N 0 0 = 1 ∨ N 0 0 = -1 := by
    have h : N 0 0 * N 0 0 = 1 := by
      calc N 0 0 * N 0 0 = N 0 0 * N 1 1 := by rw [← hrs]
        _ = 1 := hdetN
    exact mul_self_eq_one_iff.1 h
  apply hnf_sl2_eq_or_eq_neg
  rcases hr with h | h
  · left
    rw [f00, f01, f10, f11, ← hrs, h]
    simp
  · right
    rw [f00, f01, f10, f11, ← hrs, h]
    simp

/-- (27.9)–(27.14): in a standard system of generators of a cocompact torsion free Fuchsian group,
the first `2g - 2` elements determine `γ_g` and `δ_g`: writing `η = γ₁δ₁γ₁⁻¹δ₁⁻¹ ⋯ γ_{g-1}δ_{g-1}γ_{g-1}⁻¹δ_{g-1}⁻¹`
with matrix `(a b; c d)`, (27.9) `η γ_g = δ_g γ_g δ_g⁻¹` gives the linear system (27.10) for
`λ, a_g, b_g, c_g, d_g`, whose solvability condition (27.12) `λ(1 - d) = a - 1` determines `λ` since
`d ≠ 1` (`d = 1` would force `η` to be parabolic or the identity); then (27.11), (27.13), (27.14)
determine `γ_g`. -/
theorem eq27_9_14_last_determined {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ}
    (hg : 1 < g) (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ) (hfree' : ActsFreely Γ')
    (hc : IsCocompact Γ) (hc' : IsCocompact Γ') (G : StandardGenerators Γ g)
    (G' : StandardGenerators Γ' g) (hfirst : G.first = G'.first) :
    (G.δg = G'.δg ∨ G.δg = -G'.δg) ∧ (G.γg = G'.γg ∨ G.γg = -G'.γg) := by
  have _ := hg
  have _ := hΓ
  have _ := hΓ'
  have _ := hfree
  have _ := hfree'
  have _ := hc
  have _ := hc'
  -- both last pairs satisfy (27.4) with the same `η` (the same first `2g - 2` elements)
  have hrel' : (List.ofFn fun j => commutatorSL (G.first j).1 (G.first j).2).prod *
      commutatorSL G'.γg G'.δg = 1 ∨
      (List.ofFn fun j => commutatorSL (G.first j).1 (G.first j).2).prod *
      commutatorSL G'.γg G'.δg = -1 := by
    rw [hfirst]
    exact G'.relation
  exact s27t_last_pair_core G.δg_diagonal G'.δg_diagonal G.relation hrel' G.γg_fixes_one G'.γg_fixes_one
    G.alternate G'.alternate

/-- (27.12): the entry `d` of `η` is `≠ 1`: otherwise `a = 1`, `bc = 0`, and `η` would be parabolic
(`z ↦ z/(cz+1)` or `z ↦ z + b`) or the identity — impossible in a cocompact torsion free group,
the identity being excluded since `γ_g` and `δ_g` do not commute. -/
theorem eq27_12_d_ne_one {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (hg : 1 < g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hc : IsCocompact Γ) (G : StandardGenerators Γ g) :
    ((List.ofFn fun j => commutatorSL (G.first j).1 (G.first j).2).prod) 1 1 ≠ 1 ∧
      commutatorSL G.γg G.δg ≠ 1 ∧ commutatorSL G.γg G.δg ≠ -1 := by
  have _ := hg
  have _ := hΓ
  have _ := hfree
  have _ := hc
  -- by the alternation `G.alternate`, `M = [γ_g, δ_g]⁻¹` has `M₁₁ > 1`, and `η = ±M` by (27.4)
  have hM := s27t_comm_inv_11 G.γg G.δg G.δg_diagonal G.alternate
  refine ⟨?_, ?_, ?_⟩
  · rcases s27t_eta_eq G.relation with h | h
    · rw [h]
      exact ne_of_gt hM
    · rw [h, s27t_neg_apply]
      linarith
  · intro h1
    rw [h1, inv_one] at hM
    simp at hM
  · intro h1
    rw [h1, inv_neg_one] at hM
    simp at hM
    linarith

/-- `γ' ∈ SL(2, ℝ)` represents the map `F ∘ γ ∘ F⁻¹ : ℍ → ℍ`. -/
def RepresentsConj (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Prop :=
  ∀ τ : UpperHalfPlane, γ' • τ = F (γ • F.symm τ)

/-- §27.1: `G'` is the system `γⱼ(f) = f̃ ∘ γⱼ ∘ f̃⁻¹`, `δⱼ(f) = f̃ ∘ δⱼ ∘ f̃⁻¹` induced by the
normalized lift `f̃ = F` from the standard system `G`. -/
def IsInducedGenerators {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ}
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : StandardGenerators Γ g) (G' : StandardGenerators Γ' g) :
    Prop :=
  (∀ j, RepresentsConj F (G.first j).1 (G'.first j).1 ∧ RepresentsConj F (G.first j).2 (G'.first j).2) ∧
    RepresentsConj F G.γg G'.γg ∧ RepresentsConj F G.δg G'.δg

/-- An element of `SL(2, ℝ)` acting trivially on `ℍ` is `±1` (zero displacement). -/
theorem s27g_eq_one_of_smul_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : ∀ τ : UpperHalfPlane, γ • τ = τ) :
    γ = 1 ∨ γ = -1 :=
  utm_sl2_eq_of_bounded_displacement γ (C := 0) fun z => by rw [h z, dist_self]

/-- Representatives of `F ∘ γ ∘ F⁻¹` are multiplicative. -/
theorem s27g_rep_mul {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {γ₁ γ₂ δ₁ δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : RepresentsConj F γ₁ δ₁) (h₂ : RepresentsConj F γ₂ δ₂) : RepresentsConj F (γ₁ * γ₂) (δ₁ * δ₂) := by
  intro τ
  rw [mul_smul, h₂ τ, h₁, F.symm_apply_apply, mul_smul]

/-- Representatives of `F ∘ γ ∘ F⁻¹` are compatible with inverses. -/
theorem s27g_rep_inv {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : RepresentsConj F γ δ) : RepresentsConj F γ⁻¹ δ⁻¹ := by
  intro τ
  have e := h (F (γ⁻¹ • F.symm τ))
  rw [F.symm_apply_apply, smul_inv_smul, F.apply_symm_apply] at e
  exact inv_smul_eq_iff.2 e.symm

/-- `1` represents the identity. -/
theorem s27g_rep_one (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : RepresentsConj F 1 1 := fun τ => by
  rw [one_smul, one_smul, F.apply_symm_apply]

/-- `1` represents `F ∘ (-1) ∘ F⁻¹ = id`. -/
theorem s27g_rep_neg_one (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : RepresentsConj F (-1) 1 := fun τ => by
  rw [one_smul, s27g_neg_one_smul, F.apply_symm_apply]

/-- A representative of `F ∘ γ ∘ F⁻¹` is unique up to sign. -/
theorem s27g_rep_unique {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {γ δ δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : RepresentsConj F γ δ) (h' : RepresentsConj F γ δ') : δ' = δ ∨ δ' = -δ := by
  have hM : ∀ z : UpperHalfPlane, (δ⁻¹ * δ') • z = z := fun z => by
    rw [mul_smul, h' z, ← h z, inv_smul_smul]
  rcases s27g_eq_one_of_smul_eq hM with e | e
  · left
    calc δ' = δ * (δ⁻¹ * δ') := by group
      _ = δ := by rw [e, mul_one]
  · right
    calc δ' = δ * (δ⁻¹ * δ') := by group
      _ = -δ := by rw [e, mul_neg_one]

/-- Representatives of commutators. -/
theorem s27g_rep_comm {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {γ γ' δ δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : RepresentsConj F γ δ) (h₂ : RepresentsConj F γ' δ') :
    RepresentsConj F (commutatorSL γ γ') (commutatorSL δ δ') := by
  unfold commutatorSL
  exact s27g_rep_mul (s27g_rep_mul (s27g_rep_mul h₁ h₂) (s27g_rep_inv h₁)) (s27g_rep_inv h₂)

/-- Representatives of finite products `List.ofFn`. -/
theorem s27g_rep_prod {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (n : ℕ) :
    ∀ a b : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ j, RepresentsConj F (a j) (b j)) →
      RepresentsConj F (List.ofFn a).prod (List.ofFn b).prod := by
  induction n with
  | zero =>
    intro a b _
    simp only [List.ofFn_zero, List.prod_nil]
    exact s27g_rep_one F
  | succ n ih =>
    intro a b h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact s27g_rep_mul (h 0) (ih _ _ fun j => h j.succ)

/-- The deck correspondence as representatives: a lift `F` of `f` conjugates `γ ∈ Γ₀` to some `δ ∈ Γ`. -/
theorem s27g_rep_exists {S₁ : Type*} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    {Γ₀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} {p : UpperHalfPlane → S₁}
    (hp₀ : IsUniformization Γ₀ p₀) (hp : IsUniformization Γ p) {f : S₀ → S₁} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p₀ p f F) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) :
    ∃ δ ∈ Γ, RepresentsConj F γ δ := by
  obtain ⟨δ, hδ, h⟩ := h23l_deck hp₀ hp hF hγ
  exact ⟨δ, hδ, fun τ => by rw [h, F.apply_symm_apply]⟩

/-- The inverse of a lift of `f` is a lift of `f⁻¹`. -/
theorem s27g_isLift_symm {S₁ : Type*} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] {p₀ : UpperHalfPlane → S₀}
    {p : UpperHalfPlane → S₁} {f : S₀ ≃ₜ S₁} {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p f F) :
    IsLift p p₀ f.symm F.symm := by
  have _ : ChartedSpace ℂ S₀ := inferInstance
  intro τ
  have h := hF (F.symm τ)
  rw [F.apply_symm_apply] at h
  rw [h, f.symm_apply_apply]

/-- **Generation modulo `±1`.**  If `F` induces representatives of the generators of `Γ₀`, and every `δ ∈ Γ`
represents `F ∘ γ ∘ F⁻¹` for some `γ ∈ Γ₀`, the representatives generate `Γ` modulo `±1`: by induction over the
closure, every element of `Γ₀ ⊔ ⟨-1⟩` has a representative in the group generated by the representatives and `-1`,
and representatives are unique up to sign. -/
theorem s27g_generate {Γ₀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    {g : ℕ} (G : StandardGenerators Γ₀ g)
    (first' : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (γg' δg' : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hfirst : ∀ j, RepresentsConj F (G.first j).1 (first' j).1 ∧ RepresentsConj F (G.first j).2 (first' j).2)
    (hγ : RepresentsConj F G.γg γg') (hδ : RepresentsConj F G.δg δg')
    (hmem : ∀ j, (first' j).1 ∈ Γ ∧ (first' j).2 ∈ Γ) (hγm : γg' ∈ Γ) (hδm : δg' ∈ Γ)
    (hback : ∀ δ ∈ Γ, ∃ γ ∈ Γ₀, RepresentsConj F γ δ) :
    Subgroup.closure (range (fun j => (first' j).1) ∪ range (fun j => (first' j).2) ∪ {γg', δg'}) ⊔
      Subgroup.zpowers (-1) = Γ ⊔ Subgroup.zpowers (-1) := by
  set H := Subgroup.closure (range (fun j => (first' j).1) ∪ range (fun j => (first' j).2) ∪ {γg', δg'}) ⊔
    Subgroup.zpowers (-1) with hH
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hsub : ∀ x ∈ range (fun j => (first' j).1) ∪ range (fun j => (first' j).2) ∪ {γg', δg'}, x ∈ H :=
    fun x hx => Subgroup.mem_sup_left (Subgroup.subset_closure hx)
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [Subgroup.closure_le]
    rintro x ((⟨j, rfl⟩ | ⟨j, rfl⟩) | hx)
    · exact Subgroup.mem_sup_left (hmem j).1
    · exact Subgroup.mem_sup_left (hmem j).2
    · rcases hx with rfl | hx
      · exact Subgroup.mem_sup_left hγm
      · rw [mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.mem_sup_left hδm
  · refine sup_le ?_ le_sup_right
    intro δ hδΓ
    obtain ⟨γ, hγΓ₀, hγδ⟩ := hback δ hδΓ
    -- `γ` lies in the closure of the generators and `-1`
    have hγcl : γ ∈ Subgroup.closure
        ((range (fun j => (G.first j).1) ∪ range (fun j => (G.first j).2) ∪ {G.γg, G.δg}) ∪ {-1}) := by
      rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, G.generate]
      exact Subgroup.mem_sup_left hγΓ₀
    -- every element of that closure has a representative in `H`
    have key : ∀ x ∈ Subgroup.closure
        ((range (fun j => (G.first j).1) ∪ range (fun j => (G.first j).2) ∪ {G.γg, G.δg}) ∪ {-1}),
        ∃ δ₀ ∈ H, RepresentsConj F x δ₀ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with (((⟨j, rfl⟩ | ⟨j, rfl⟩) | hx) | hx)
        · exact ⟨_, hsub _ (Or.inl (Or.inl ⟨j, rfl⟩)), (hfirst j).1⟩
        · exact ⟨_, hsub _ (Or.inl (Or.inr ⟨j, rfl⟩)), (hfirst j).2⟩
        · rcases hx with rfl | hx
          · exact ⟨_, hsub _ (Or.inr (Or.inl rfl)), hγ⟩
          · rw [mem_singleton_iff] at hx
            rw [hx]
            exact ⟨_, hsub _ (Or.inr (Or.inr rfl)), hδ⟩
        · rw [mem_singleton_iff] at hx
          rw [hx]
          exact ⟨1, H.one_mem, s27g_rep_neg_one F⟩
      | one => exact ⟨1, H.one_mem, s27g_rep_one F⟩
      | mul x y _ _ hx hy =>
        obtain ⟨δx, hδx, hx⟩ := hx
        obtain ⟨δy, hδy, hy⟩ := hy
        exact ⟨δx * δy, H.mul_mem hδx hδy, s27g_rep_mul hx hy⟩
      | inv x _ hx =>
        obtain ⟨δx, hδx, hx⟩ := hx
        exact ⟨δx⁻¹, H.inv_mem hδx, s27g_rep_inv hx⟩
    obtain ⟨δ₀, hδ₀, hγδ₀⟩ := key γ hγcl
    rcases s27g_rep_unique hγδ₀ hγδ with rfl | rfl
    · exact hδ₀
    · rw [← neg_one_mul]
      exact H.mul_mem hneg hδ₀

/-- **(27.4) for the induced system**: the product of the induced commutators represents `F ∘ (±1) ∘ F⁻¹ = id`,
hence is `±1`. -/
theorem s27g_relation {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    {g : ℕ} (G : StandardGenerators Γ₀ g)
    (first' : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (γg' δg' : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hfirst : ∀ j, RepresentsConj F (G.first j).1 (first' j).1 ∧ RepresentsConj F (G.first j).2 (first' j).2)
    (hγ : RepresentsConj F G.γg γg') (hδ : RepresentsConj F G.δg δg') :
    (List.ofFn fun j => commutatorSL (first' j).1 (first' j).2).prod * commutatorSL γg' δg' = 1 ∨
      (List.ofFn fun j => commutatorSL (first' j).1 (first' j).2).prod * commutatorSL γg' δg' = -1 := by
  have hR := s27g_rep_mul (s27g_rep_prod (F := F) (g - 1) _ _ fun j => s27g_rep_comm (hfirst j).1 (hfirst j).2)
    (s27g_rep_comm hγ hδ)
  have h1 : RepresentsConj F ((List.ofFn fun j => commutatorSL (G.first j).1 (G.first j).2).prod *
      commutatorSL G.γg G.δg) 1 := by
    rcases G.relation with e | e
    · rw [e]
      exact s27g_rep_one F
    · rw [e]
      exact s27g_rep_neg_one F
  rcases s27g_rep_unique h1 hR with e | e
  · exact Or.inl e
  · exact Or.inr e

/-- **The extension commutes with the Möbius maps on `closure ℍ`.**  If `δ` represents `F ∘ γ ∘ F⁻¹`, then
`Gb ∘ γ = δ ∘ Gb` on the closed upper half-plane of `ℂ̄`: both sides are continuous there and agree on `ℍ`. -/
theorem s27g_bdry_rel {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR : RepresentsConj F γ δ) :
    EqOn (Gb ∘ mobiusSL (slRealToComplex γ)) (mobiusSL (slRealToComplex δ) ∘ Gb) (closure (toExt upperHalf)) := by
  have hcγ : Continuous (mobiusSL (slRealToComplex γ)) := (k24_mobiusSLHomeo _).continuous
  have hcδ : Continuous (mobiusSL (slRealToComplex δ)) := (k24_mobiusSLHomeo _).continuous
  have hmaps : MapsTo (mobiusSL (slRealToComplex γ)) (closure (toExt upperHalf)) (closure (toExt upperHalf)) :=
    Set.MapsTo.closure (fun q hq => k24_real_mapsTo_upper γ hq) hcγ
  refine Set.EqOn.of_subset_closure ?_ (hG.2.1.comp hcγ.continuousOn hmaps) (hcδ.comp_continuousOn hG.2.1)
    subset_closure subset_rfl
  rintro _ ⟨z, hz, rfl⟩
  have hz' : 0 < z.im := hz
  set τ : UpperHalfPlane := ⟨z, hz'⟩ with hτ
  have hzτ : z = (τ : ℂ) := rfl
  simp only [Function.comp_apply]
  rw [hzτ, h36t_mobiusSL_coe, hG.1 _ (γ • τ).coe_im_pos, h23l_liftToC_coe, hG.1 _ τ.coe_im_pos, h23l_liftToC_coe,
    h36t_mobiusSL_coe, hR, F.symm_apply_apply]

/-- A real Möbius map sends the real point `x` to the finite point `y` only if `c x + d ≠ 0` and
`a x + b = y (c x + d)`. -/
theorem s27g_mob_real_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {x y : ℝ}
    (h : mobiusSL (slRealToComplex γ) ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane)) :
    γ 1 0 * x + γ 1 1 ≠ 0 ∧ γ 0 0 * x + γ 0 1 = y * (γ 1 0 * x + γ 1 1) := by
  rw [k24_mobiusSL_real] at h
  by_cases hd : (γ 1 0 : ℂ) * x + γ 1 1 = 0
  · rw [mobiusExt_coe_of_eq_zero hd] at h
    exact absurd h (OnePoint.infty_ne_coe _)
  · rw [mobiusExt_coe hd] at h
    have h' := OnePoint.coe_injective h
    have hd' : γ 1 0 * x + γ 1 1 ≠ 0 := by exact_mod_cast hd
    refine ⟨hd', ?_⟩
    have e : (γ 0 0 : ℂ) * x + γ 0 1 = (y : ℂ) * ((γ 1 0 : ℂ) * x + γ 1 1) := by
      rw [← h', mobiusFn, div_mul_cancel₀ _ hd]
    exact_mod_cast e

/-- Conversely, `c x + d ≠ 0` and `a x + b = y (c x + d)` give `γ(x) = y`. -/
theorem s27g_mob_real_of {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {x y : ℝ} (hd : γ 1 0 * x + γ 1 1 ≠ 0)
    (hy : γ 0 0 * x + γ 0 1 = y * (γ 1 0 * x + γ 1 1)) :
    mobiusSL (slRealToComplex γ) ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := by
  have hd' : (γ 1 0 : ℂ) * x + γ 1 1 ≠ 0 := by exact_mod_cast hd
  have hy' : (γ 0 0 : ℂ) * x + γ 0 1 = (y : ℂ) * ((γ 1 0 : ℂ) * x + γ 1 1) := by exact_mod_cast hy
  rw [k24_mobiusSL_real, mobiusExt_coe hd', mobiusFn, hy', mul_div_assoc, div_self hd', mul_one]

/-- A real Möbius map fixes `∞` iff `c = 0`. -/
theorem s27g_mob_infty {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} :
    mobiusSL (slRealToComplex γ) extInf = extInf ↔ γ 1 0 = 0 := by
  rw [k24_mobiusSL_real]
  constructor
  · intro h
    by_contra hc
    have hc' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [mobiusExt_infty_of_ne hc'] at h
    exact OnePoint.coe_ne_infty _ h
  · intro hc
    exact mobiusExt_infty_of_eq (by rw [hc, Complex.ofReal_zero])

/-- **The boundary map on `ℝ`.**  A normalized extension `Gb` (fixing `0, 1, ∞`) maps `ℝ` into `ℝ` by a continuous
injective `g`, which is increasing because `g 0 = 0 < 1 = g 1`. -/
theorem s27g_bdry_real {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) (hG0 : Gb ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    (hG1 : Gb ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) (hGinf : Gb extInf = extInf) :
    ∃ g : ℝ → ℝ, (∀ x : ℝ, Gb ((x : ℂ) : ExtPlane) = ((g x : ℂ) : ExtPlane)) ∧ StrictMono g ∧ g 0 = 0 ∧ g 1 = 1 := by
  have hcl : ∀ x : ℝ, ((x : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := s27t_mem_closure_real
  have hinf_cl : extInf ∈ closure (toExt upperHalf) := by
    rw [scExt_closure_toExt_upperHalf]
    exact Or.inr rfl
  have hreal : ∀ x : ℝ, ∃ y : ℝ, Gb ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := by
    intro x
    have hmem : Gb ((x : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := by
      rw [← hG.2.2.2]
      exact mem_image_of_mem Gb (hcl x)
    rw [scExt_closure_toExt_upperHalf] at hmem
    rcases hmem with ⟨w, hw, hwe⟩ | hinf
    · have hw0 : w.im = 0 := by
        rcases (show 0 ≤ w.im from hw).lt_or_eq with hpos | h0
        · exfalso
          set τ : UpperHalfPlane := F.symm ⟨w, hpos⟩ with hτ
          have hGτ : Gb ((τ : ℂ) : ExtPlane) = ((w : ℂ) : ExtPlane) := by
            rw [hG.1 _ τ.coe_im_pos, h23l_liftToC_coe, hτ, F.apply_symm_apply]
          have e := hG.2.2.1 (subset_closure ⟨_, τ.coe_im_pos, rfl⟩) (hcl x) (hGτ.trans hwe)
          have e2 := congrArg Complex.im (OnePoint.coe_injective e)
          rw [Complex.ofReal_im] at e2
          exact (ne_of_gt τ.im_pos) e2
        · exact h0.symm
      refine ⟨w.re, ?_⟩
      rw [← hwe]
      congr 1
      apply Complex.ext <;> simp [hw0]
    · exfalso
      have hinf' : Gb ((x : ℂ) : ExtPlane) = extInf := hinf
      exact OnePoint.coe_ne_infty _ (hG.2.2.1 (hcl x) hinf_cl (hinf'.trans hGinf.symm))
  choose g hg using hreal
  have hgc : Continuous g := by
    have h1 : Continuous (fun x : ℝ => Gb ((x : ℂ) : ExtPlane)) :=
      hG.2.1.comp_continuous (OnePoint.continuous_coe.comp Complex.continuous_ofReal) hcl
    have h2 : g = fun x : ℝ => (extToC (Gb ((x : ℂ) : ExtPlane))).re := by
      funext x
      rw [hg x]
      simp [extToC]
    rw [h2]
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.2 fun x => ?_)
    have hx : ContinuousAt extToC (Gb ((x : ℂ) : ExtPlane)) := by
      rw [hg x]
      refine OnePoint.continuousAt_coe.2 ?_
      have e : (extToC ∘ ((↑) : ℂ → ExtPlane)) = id := by
        funext z
        rfl
      rw [e]
      exact continuousAt_id
    exact ContinuousAt.comp (f := fun x : ℝ => Gb ((x : ℂ) : ExtPlane)) hx h1.continuousAt
  have hgi : Function.Injective g := by
    intro x x' h
    have e : Gb ((x : ℂ) : ExtPlane) = Gb ((x' : ℂ) : ExtPlane) := by rw [hg, hg, h]
    have e2 := OnePoint.coe_injective (hG.2.2.1 (hcl x) (hcl x') e)
    exact_mod_cast e2
  have hg0 : g 0 = 0 := by
    have e := hg 0
    rw [Complex.ofReal_zero, hG0] at e
    have e2 := OnePoint.coe_injective e
    exact_mod_cast e2.symm
  have hg1 : g 1 = 1 := by
    have e := hg 1
    rw [Complex.ofReal_one, hG1] at e
    have e2 := OnePoint.coe_injective e
    exact_mod_cast e2.symm
  rcases hgc.strictMono_of_inj hgi with hm | ha
  · exact ⟨g, hg, hm, hg0, hg1⟩
  · exfalso
    have e := ha (zero_lt_one' ℝ)
    rw [hg0, hg1] at e
    linarith

/-- A scalar `γ` (`b = c = 0`, `a = d`) acts trivially on `ℍ`. -/
theorem s27g_smul_self_of_scalar {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h01 : γ 0 1 = 0) (h10 : γ 1 0 = 0)
    (h : γ 0 0 = γ 1 1) (τ : UpperHalfPlane) : γ • τ = τ := by
  have hdet := hnf_sl2_det γ
  rw [h01, h10, h] at hdet
  have hd : γ 1 1 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    norm_num at hdet
  have hd' : (γ 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
  apply UpperHalfPlane.ext
  rw [h36t_coe_smul, h01, h10, h, Complex.ofReal_zero, zero_mul, zero_add, add_zero, mul_div_right_comm,
    div_self hd', one_mul]

/-- **(27.5) for the induced `δ_g`.**  If `δ` is diagonal with `δ₀₀² > 1` and `δ'` represents `F ∘ δ ∘ F⁻¹`, then
`δ'` is diagonal with `δ'₀₀² > 1`: the extension `Gb` fixes `∞` and `0`, which are therefore fixed by `δ'`
(`s27g_bdry_rel`), and `δ'(1) = δ'₀₀² = g(δ₀₀²) > g(1) = 1` since `g` is increasing. -/
theorem s27g_diag {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) (hG0 : Gb ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    (hGinf : Gb extInf = extInf) {g : ℝ → ℝ} (hg : ∀ x : ℝ, Gb ((x : ℂ) : ExtPlane) = ((g x : ℂ) : ExtPlane))
    (hmono : StrictMono g) (hg1 : g 1 = 1) {δ δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hδ : δ 0 1 = 0 ∧ δ 1 0 = 0 ∧ 1 < δ 0 0 ^ 2) (hR : RepresentsConj F δ δ') :
    δ' 0 1 = 0 ∧ δ' 1 0 = 0 ∧ 1 < δ' 0 0 ^ 2 := by
  obtain ⟨h01, h10, h00⟩ := hδ
  obtain ⟨hdetD, -, -⟩ := s27t_diag_facts ⟨h01, h10, h00⟩
  have hd0 : δ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdetD
  have hrel := s27g_bdry_rel hG hR
  have hinf_cl : extInf ∈ closure (toExt upperHalf) := by
    rw [scExt_closure_toExt_upperHalf]
    exact Or.inr rfl
  -- `∞` is fixed
  have h10' : δ' 1 0 = 0 := by
    have e := hrel hinf_cl
    simp only [Function.comp_apply] at e
    rw [s27g_mob_infty.2 h10, hGinf] at e
    exact s27g_mob_infty.1 e.symm
  -- `0` is fixed
  have h01' : δ' 0 1 = 0 := by
    have e := hrel (s27t_mem_closure_real 0)
    simp only [Function.comp_apply] at e
    have e0 : mobiusSL (slRealToComplex δ) (((0 : ℝ) : ℂ) : ExtPlane) = (((0 : ℝ) : ℂ) : ExtPlane) :=
      s27g_mob_real_of (by rw [h10]; simpa using hd0) (by rw [h01]; ring)
    rw [e0, Complex.ofReal_zero, hG0] at e
    have e' : mobiusSL (slRealToComplex δ') (((0 : ℝ) : ℂ) : ExtPlane) = (((0 : ℝ) : ℂ) : ExtPlane) := by
      rw [Complex.ofReal_zero]
      exact e.symm
    obtain ⟨-, e2⟩ := s27g_mob_real_eq e'
    simpa using e2
  refine ⟨h01', h10', ?_⟩
  -- `δ(1) = δ₀₀²`
  have e := hrel (s27t_mem_closure_real 1)
  simp only [Function.comp_apply] at e
  have e1 : mobiusSL (slRealToComplex δ) (((1 : ℝ) : ℂ) : ExtPlane) = (((δ 0 0 ^ 2 : ℝ) : ℂ) : ExtPlane) :=
    s27g_mob_real_of (by rw [h10]; simpa using hd0) (by rw [h01, h10]; linear_combination (-(δ 0 0)) * hdetD)
  rw [e1, hg, hg 1, hg1] at e
  obtain ⟨-, e2⟩ := s27g_mob_real_eq e.symm
  have hdet' := hnf_sl2_det δ'
  rw [h01', h10'] at hdet' e2
  have hgt : 1 < g (δ 0 0 ^ 2) := lt_of_eq_of_lt hg1.symm (hmono h00)
  have e3 : δ' 0 0 = g (δ 0 0 ^ 2) * δ' 1 1 := by linear_combination e2
  have hsq : δ' 0 0 ^ 2 = g (δ 0 0 ^ 2) := by linear_combination δ' 0 0 * e3 + g (δ 0 0 ^ 2) * hdet'
  rw [hsq]
  exact hgt

/-- **(27.5) for the induced `γ_g`**: `γ'(1) = 1`, since `Gb` fixes `1` (`s27g_bdry_rel`). -/
theorem s27g_fixes_one {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) (hG1 : Gb ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane))
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR : RepresentsConj F γ γ')
    (hfix : γ 0 0 + γ 0 1 = γ 1 0 + γ 1 1) : γ' 0 0 + γ' 0 1 = γ' 1 0 + γ' 1 1 := by
  have hdet := hnf_sl2_det γ
  have hden : γ 1 0 * 1 + γ 1 1 ≠ 0 := by
    intro h0
    have h1 : γ 1 1 = -γ 1 0 := by linarith
    have h2 : γ 0 1 = -γ 0 0 := by linarith
    rw [h1, h2] at hdet
    linarith
  have e1 : mobiusSL (slRealToComplex γ) (((1 : ℝ) : ℂ) : ExtPlane) = (((1 : ℝ) : ℂ) : ExtPlane) :=
    s27g_mob_real_of hden (by linarith)
  have e := s27g_bdry_rel hG hR (s27t_mem_closure_real 1)
  simp only [Function.comp_apply] at e
  rw [e1, Complex.ofReal_one, hG1] at e
  have e' : mobiusSL (slRealToComplex γ') (((1 : ℝ) : ℂ) : ExtPlane) = (((1 : ℝ) : ℂ) : ExtPlane) := by
    rw [Complex.ofReal_one]
    exact e.symm
  obtain ⟨-, e2⟩ := s27g_mob_real_eq e'
  linarith

/-- **The alternation for the induced `γ_g`.**  `γ` fixes `1` and `u = -b/c < 0`; `g` is increasing with `g 0 = 0`,
so `γ'` fixes `1` and `v = g u < 0`, whence `b' = -c' v` and `b'c' = -c'² v > 0` (`c' = 0` would make `γ'`, hence
`γ`, act trivially, i.e. `γ = ±1`, against `bc > 0`). -/
theorem s27g_alternate {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) {g : ℝ → ℝ}
    (hg : ∀ x : ℝ, Gb ((x : ℂ) : ExtPlane) = ((g x : ℂ) : ExtPlane)) (hmono : StrictMono g) (hg0 : g 0 = 0)
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR : RepresentsConj F γ γ')
    (hfix : γ 0 0 + γ 0 1 = γ 1 0 + γ 1 1) (hfix' : γ' 0 0 + γ' 0 1 = γ' 1 0 + γ' 1 1)
    (halt : 0 < γ 0 1 * γ 1 0) : 0 < γ' 0 1 * γ' 1 0 := by
  have hdet := hnf_sl2_det γ
  have hc : γ 1 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at halt
    exact lt_irrefl 0 halt
  have hc2 : 0 < γ 1 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc))
  set u : ℝ := -(γ 0 1 / γ 1 0) with hu
  have huc : u * γ 1 0 = -γ 0 1 := by
    rw [hu]
    field_simp
  have hu0 : u < 0 := by
    have e : u * γ 1 0 ^ 2 = -(γ 0 1 * γ 1 0) := by linear_combination γ 1 0 * huc
    by_contra hcon
    push Not at hcon
    have := mul_nonneg hcon hc2.le
    linarith
  have hden : γ 1 0 * u + γ 1 1 ≠ 0 := by
    intro h0
    have e1 : γ 1 1 = γ 0 1 := by linear_combination h0 - huc
    have e2 : γ 0 0 = γ 1 0 := by linarith
    rw [e1, e2] at hdet
    have : (0 : ℝ) = 1 := by linear_combination hdet
    norm_num at this
  have hy : γ 0 0 * u + γ 0 1 = u * (γ 1 0 * u + γ 1 1) := by
    linear_combination (1 - u) * huc + u * hfix
  have eu : mobiusSL (slRealToComplex γ) ((u : ℂ) : ExtPlane) = ((u : ℂ) : ExtPlane) := s27g_mob_real_of hden hy
  have e := s27g_bdry_rel hG hR (s27t_mem_closure_real u)
  simp only [Function.comp_apply] at e
  rw [eu, hg u] at e
  obtain ⟨-, e2⟩ := s27g_mob_real_eq e.symm
  have hv : g u < 0 := lt_of_lt_of_eq (hmono hu0) hg0
  have key : (1 - g u) * (γ' 0 1 + γ' 1 0 * g u) = 0 := by linear_combination e2 - g u * hfix'
  have hb' : γ' 0 1 = -(γ' 1 0 * g u) := by
    have h1 := (mul_eq_zero.1 key).resolve_left (by linarith)
    linarith
  have hc' : γ' 1 0 ≠ 0 := by
    intro h0
    have hb0 : γ' 0 1 = 0 := by rw [hb', h0, zero_mul, neg_zero]
    have had : γ' 0 0 = γ' 1 1 := by
      rw [hb0, h0] at hfix'
      linarith
    have htriv := s27g_smul_self_of_scalar hb0 h0 had
    have hγtriv : ∀ σ : UpperHalfPlane, γ • σ = σ := by
      intro σ
      have e3 := hR (F σ)
      rw [htriv, F.symm_apply_apply] at e3
      exact (F.injective e3).symm
    rcases s27g_eq_one_of_smul_eq hγtriv with rfl | rfl
    · simp at halt
    · simp [s27t_neg_apply] at halt
  have hc'2 : 0 < γ' 1 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc'))
  rw [hb']
  calc (0 : ℝ) < -g u * γ' 1 0 ^ 2 := mul_pos (by linarith) hc'2
    _ = -(γ' 1 0 * g u) * γ' 1 0 := by ring

/-- §27.1: for a normalized lift `f̃` of `f : S₀ → S` with covering group `G`, the induced system
`γ₁(f), δ₁(f), …, γ_g(f), δ_g(f)` is a standard system of generators of `G` (the normalization of
`δ_g(f)` follows from `lim_{n → ±∞} δ_g(f)ⁿ = ∞, 0`). -/
theorem exists_inducedGenerators [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    (m : MarkedRS S₀) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → m.X.carrier}
    (hp : IsUniformization Γ p) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hF : IsNormalizedLift p₀ p m.marking F Gb) :
    ∃ G' : StandardGenerators Γ g, IsInducedGenerators F G G' := by
  have _ := hg
  have _ := hS
  obtain ⟨hLift, hG, hG0, hG1, hGinf⟩ := hF
  have hrep : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ, RepresentsConj F γ δ := fun γ hγ => s27g_rep_exists hp₀ hp hLift hγ
  choose r hrΓ hrR using hrep
  have hback : ∀ δ ∈ Γ, ∃ γ ∈ Γ₀, RepresentsConj F γ δ := by
    intro δ hδ
    obtain ⟨γ, hγ, h⟩ := h23l_deck hp hp₀ (s27g_isLift_symm hLift) hδ
    exact ⟨γ, hγ, fun τ => by rw [← h, F.apply_symm_apply]⟩
  obtain ⟨gb, hgb, hmono, hgb0, hgb1⟩ := s27g_bdry_real hG hG0 hG1 hGinf
  set first' : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun j => (r _ (G.first_mem j).1, r _ (G.first_mem j).2) with hfirst'
  have hfirst : ∀ j, RepresentsConj F (G.first j).1 (first' j).1 ∧ RepresentsConj F (G.first j).2 (first' j).2 :=
    fun j => ⟨hrR _ _, hrR _ _⟩
  have hmem : ∀ j, (first' j).1 ∈ Γ ∧ (first' j).2 ∈ Γ := fun j => ⟨hrΓ _ _, hrΓ _ _⟩
  have hfix' := s27g_fixes_one hG hG1 (hrR _ G.γg_mem) G.γg_fixes_one
  exact ⟨⟨first', r _ G.γg_mem, r _ G.δg_mem, hmem, hrΓ _ _, hrΓ _ _,
    s27g_generate G first' _ _ hfirst (hrR _ _) (hrR _ _) hmem (hrΓ _ _) (hrΓ _ _) hback,
    s27g_relation G first' _ _ hfirst (hrR _ _) (hrR _ _),
    s27g_diag hG hG0 hGinf hgb hmono hgb1 G.δg_diagonal (hrR _ _), hfix',
    s27g_alternate hG hgb hmono hgb0 (hrR _ _) G.γg_fixes_one hfix' G.alternate⟩, hfirst, hrR _ _, hrR _ _⟩

/-- `c ∈ ℝ^{6g-6}` are Fricke coordinates of the marked surface `m` (with respect to the fixed
uniformization `p₀` of `S₀` and the standard system `G`): the coordinates of the system induced by
a normalized lift of the marking. -/
def IsFrickeCoords {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) (m : MarkedRS S₀) (c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → m.X.carrier)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (Gb : ExtPlane → ExtPlane) (G' : StandardGenerators Γ g),
    IsUniformization Γ p ∧ IsNormalizedLift p₀ p m.marking F Gb ∧ IsInducedGenerators F G G' ∧
      c = frickeCoordinates G'

/-- **§27.1 (Fricke 空间).**  `F(S₀) ⊆ ℝ^{6g-6}`: the Fricke coordinates of all marked surfaces. -/
def frickeSpace {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) : Set (Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
  {c | ∃ m : MarkedRS S₀, IsFrickeCoords p₀ G m c}

/-! ### Uniformization transport (UT): a non-book helper block (s27t stage U, coordinator 553e2d)

Every marked surface `(S, f)` of `S₀ = ℍ/Γ₀` is uniformized by TRANSPORTING the given `p₀`.  There is no
uniformization of an abstract surface, no invariance of domain, no Riemann–Roch and no `exists_qc_in_homotopy_class`.

1. `μ = s27u_liftCoeff p₀ f`, the Beltrami coefficient of `f ∘ p₀` read in charts, is measurable, bounded by
   `k = (K - 1)/(K + 1) < 1` and `Γ₀`-compatible (U1–U3).
2. `w = f^μ = s27u_fSym μ`, the normalized solution for the symmetric extension, commutes with `z ↦ z̄` and maps `ℍ`
   onto `ℍ` (U4, U4', copies of S33); `F = w|ℍ` (U5).
3. `F ∘ γ ∘ F⁻¹` is conformal, hence Möbius, for `γ ∈ Γ₀` (U6); so `Γ = s27u_conjGroup Γ₀ F` is `F Γ₀ F⁻¹`.
4. `p = f ∘ p₀ ∘ F⁻¹ = s27u_proj p₀ f F` is holomorphic (U7), and a covering whose fibres are the `Γ`-orbits
   (`s27u_isUniformization`, proved).
5. `F` is a normalized lift of `f`, with boundary map `G = w` on `ℂ̄` (`s27u_isNormalizedLift`, proved).

The final forms are `s27u_uniformization_transport` (explicit `F`, `Γ`, `p`, `G`) and `s27u_exists_uniformization`
(for `m : MarkedRS S₀`).  U10 and U11 are optional helpers for the E2 bridge; nothing here uses them. -/

/-- **The lifted Beltrami coefficient** of `f ∘ p₀` ((23.5), the complex dilatation of a lift of `f`).  At `z ∈ ℍ` it
is the complex dilatation at `z` of `w ↦ φ_y(f(p₀ w))`, where `φ_y` is the chart of `S` at the image point
`y = f(p₀ z)`, read in the coordinate of `ℍ` itself; off `ℍ` it is `0`, so a bounded one lies in `M` (`BeltramiH`).
It depends only on `p₀` and `f`: another chart at the image point changes the expression by a holomorphic transition,
which leaves the dilatation unchanged (`s23_dilatation_comp_left`).  For every uniformization `p` of `S` and every lift
`F` of `f` it is the complex dilatation of `F` (U10, `s27u_liftCoeff_eq_dilatation`). -/
def s27u_liftCoeff {X S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (p₀ : UpperHalfPlane → X) (f : X → S) :
    ℂ → ℂ :=
  upperHalf.indicator fun z => complexDilatation (fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))) z

/-- Verbatim copy of S33 `symmetricExtension` (S33 imports S27, so it cannot be imported here);
`s27u_symExt = symmetricExtension` holds by `rfl`.  (33.3): the symmetric extension `μ(z) = conj μ(z̄)` of `μ` to the
lower half-plane. -/
def s27u_symExt (μ : ℂ → ℂ) (z : ℂ) : ℂ := if z.im < 0 then conj (μ (conj z)) else μ z

/-- Verbatim copy of S33 `fMuSym` (S33 imports S27, so it cannot be imported here); `s27u_fSym = fMuSym` holds by
`rfl`.  `f^μ`: the normalized solution, fixing `0, 1, ∞`, of the Beltrami equation with the symmetrically extended
coefficient `s27u_symExt μ`. -/
def s27u_fSym (μ : ℂ → ℂ) : ℂ → ℂ := normalizedSolution (s27u_symExt μ)

/-- Verbatim copy of S33 `b33_d_conjGroup` (S33 imports S27, so it cannot be imported here);
`s27u_conjGroup = b33_d_conjGroup` holds by `rfl`.  The conjugate group `F Γ F⁻¹ = {γ' | ∃ γ ∈ Γ, F ∘ γ = γ' ∘ F}`
of `Γ` by a map `F : ℍ → ℍ`: a subgroup for every `F`.  It always contains `-1` (take `γ = 1`). -/
def s27u_conjGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : UpperHalfPlane → UpperHalfPlane) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) where
  carrier := {γ' | ∃ γ ∈ Γ, ∀ τ, F (γ • τ) = γ' • F τ}
  mul_mem' := by
    rintro a b ⟨γa, hγa, ha⟩ ⟨γb, hγb, hb⟩
    exact ⟨γa * γb, Γ.mul_mem hγa hγb, fun τ => by rw [mul_smul, ha, hb, mul_smul]⟩
  one_mem' := ⟨1, Γ.one_mem, fun τ => by rw [one_smul, one_smul]⟩
  inv_mem' := by
    rintro a ⟨γ, hγ, h⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, fun τ => ?_⟩
    have h' := h (γ⁻¹ • τ)
    rw [smul_inv_smul] at h'
    rw [h', inv_smul_smul]

/-- The transported projection `p = f ∘ p₀ ∘ F⁻¹ : ℍ → S`. -/
def s27u_proj {X S : Type*} (p₀ : UpperHalfPlane → X) (f : X → S) (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (τ : UpperHalfPlane) : S :=
  f (p₀ (F.symm τ))

/-- `utm_pext p₀` agrees with `p₀` at the points of `ℍ`. -/
theorem s27u_pext_coe {X : Type*} (p₀ : UpperHalfPlane → X) (τ : UpperHalfPlane) :
    utm_pext p₀ (τ : ℂ) = p₀ τ := by
  simp only [utm_pext, τ.coe_im_pos, ↓reduceDIte]

/-- The lifted coefficient at a point of `ℍ`. -/
theorem s27u_liftCoeff_of_mem {X S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (p₀ : UpperHalfPlane → X)
    (f : X → S) {z : ℂ} (hz : z ∈ upperHalf) :
    s27u_liftCoeff p₀ f z = complexDilatation (fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))) z := by
  exact indicator_of_mem hz _

/-- The lifted coefficient vanishes off `ℍ`. -/
theorem s27u_liftCoeff_of_not_mem {X S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (p₀ : UpperHalfPlane → X)
    (f : X → S) {z : ℂ} (hz : z ∉ upperHalf) : s27u_liftCoeff p₀ f z = 0 := by
  exact indicator_of_notMem hz _

/-- **[U1, stub] Local form of the lifted coefficient.**  Near every `z₀ ∈ ℍ`, `μ = s27u_liftCoeff p₀ f` is, at EVERY
point, the complex dilatation of one `K`-q.c. map.  Write `p̂₀ = utm_pext p₀`, `y₀ = f(p̂₀ z₀)` and
`g = φ_{y₀} ∘ f ∘ p̂₀`.  There is an open `U ∋ z₀` inside `ℍ` on which `f ∘ p̂₀` stays in the chart source at `y₀`,
`g` is `K`-q.c., and `μ = μ_g` pointwise.

*Why true.*
- `g` is `K`-q.c. near `z₀`.  Near `z₀`, `g = L ∘ ψ₀`, where `ψ₀ = φ_x ∘ p₀ ∘ ofComplex` is conformal (`x = p₀ z₀`,
  `h23l_chart_proj`) and `L = localMapExpr f x` is `K`-q.c. (`hf.2 x`).  Conclude with `thm7_1_comp` and
  `ad_isKQC_congr`, exactly as in `h23l_lift_isKQC` but without the second chart.
- `μ = μ_g` on `U`.  At `z ∈ U` the defining chart of `μ` is the one at `f(p̂₀ z)`.  Near `z` the two chart expressions
  differ by the transition `T = φ_{f(p̂₀ z)} ∘ φ_{y₀}⁻¹`, which is holomorphic with a holomorphic local inverse.  So
  `μ_{T ∘ g}(z) = μ_g(z)` (`s23_dilatation_comp_left`).

*Reuse.*
- S23: `h23l_chart_proj` l.810, `h23l_lift_isKQC` l.980 (template), `s23_transition` l.105, `s23_transition_inv`
  l.60, `s23_transition_mem` l.69, `s23_dilatation_comp_left` l.154, `s23_localMapDomain_isOpen` l.215,
  `s23_h_center` l.656.
- S07 `thm7_1_comp` l.181; S09 `ac_t_isKQC_restrict` l.6555; S13 `ad_isKQC_congr` l.5796.
- Here: `utm_a_pext_eq`, `utm_a_continuousAt`, `s27u_liftCoeff_of_mem`.  The chart bookkeeping is as in UTM
  `utm_liftQD_local` (l.455).

*Estimate.*  150–250 lines. -/
theorem s27u_liftCoeff_local [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ upperHalf ∧
      (∀ w ∈ U, f (utm_pext p₀ w) ∈ (chartAt ℂ (f (utm_pext p₀ z₀))).source) ∧
      IsKQC (fun w => chartAt ℂ (f (utm_pext p₀ z₀)) (f (utm_pext p₀ w))) U K ∧
      ∀ z ∈ U, s27u_liftCoeff p₀ f z =
        complexDilatation (fun w => chartAt ℂ (f (utm_pext p₀ z₀)) (f (utm_pext p₀ w))) z := by
  have hz₀' : 0 < z₀.im := hz₀
  have hpz₀ : utm_pext p₀ z₀ = p₀ ⟨z₀, hz₀'⟩ := s27u_pext_coe p₀ ⟨z₀, hz₀'⟩
  obtain ⟨U₀, hU₀o, hz₀U₀, hU₀H, hU₀s, hψ₀⟩ :=
    h23l_chart_proj (τ := ⟨z₀, hz₀'⟩) hp₀.1 hp₀.2.1 _ (mem_chart_source ℂ _)
  rw [hpz₀]
  set x : S₀ := p₀ ⟨z₀, hz₀'⟩
  set ψ₀ : ℂ → ℂ := fun z => chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z))
  set U : Set ℂ := U₀ ∩ ψ₀ ⁻¹' localMapDomain f x
  have hUo : IsOpen U :=
    hψ₀.2.2.1.1.isOpen_inter_preimage hU₀o (s23_localMapDomain_isOpen f.continuous x)
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀U₀, ?_⟩
    show chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z₀)) ∈ localMapDomain f x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz₀']
    exact (s23_h_center f x).1
  -- on `U`, `p̂₀ = φ_x⁻¹ ∘ ψ₀`
  have hpw : ∀ w ∈ U, utm_pext p₀ w = (chartAt ℂ x).symm (ψ₀ w) := fun w hw => by
    rw [utm_a_pext_eq p₀ (hU₀H hw.1)]
    exact ((chartAt ℂ x).left_inv (hU₀s w hw.1)).symm
  have hsrc : ∀ w ∈ U, f (utm_pext p₀ w) ∈ (chartAt ℂ (f x)).source := fun w hw => by
    rw [hpw w hw]
    exact hw.2.2
  -- `g = L ∘ ψ₀` on `U`, with `ψ₀` `1`-q.c. and `L = localMapExpr f x` `K`-q.c.
  have hgK : IsKQC (fun w => chartAt ℂ (f x) (f (utm_pext p₀ w))) U K := by
    have h1 := ac_t_isKQC_restrict hψ₀ hUo inter_subset_left
    have h2 := thm7_1_comp h1 (hf.2 x) (by rintro _ ⟨w, hw, rfl⟩; exact hw.2)
    rw [one_mul] at h2
    refine ad_isKQC_congr h2 fun w hw => ?_
    show chartAt ℂ (f x) (f (utm_pext p₀ w)) = chartAt ℂ (f x) (f ((chartAt ℂ x).symm (ψ₀ w)))
    rw [hpw w hw]
  refine ⟨U, hUo, hz₀U, fun w hw => hU₀H hw.1, hsrc, hgK, fun z hz => ?_⟩
  -- at `z ∈ U` the defining chart (at `f(p̂₀ z)`) differs from the one at `f x` by a holomorphic transition
  rw [s27u_liftCoeff_of_mem p₀ f (hU₀H hz.1)]
  set y := f (utm_pext p₀ z)
  set g : ℂ → ℂ := fun w => chartAt ℂ (f x) (f (utm_pext p₀ w))
  have hev : (fun w => chartAt ℂ y (f (utm_pext p₀ w))) =ᶠ[𝓝 z] chartTransition y (f x) ∘ g := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    show _ = chartAt ℂ y ((chartAt ℂ (f x)).symm (chartAt ℂ (f x) (f (utm_pext p₀ w))))
    rw [(chartAt ℂ (f x)).left_inv (hsrc w hw)]
  have hgz : g z ∈ (chartAt ℂ (f x)).target := (chartAt ℂ (f x)).map_source (hsrc z hz)
  have hgz' : (chartAt ℂ (f x)).symm (g z) ∈ (chartAt ℂ y).source := by
    show (chartAt ℂ (f x)).symm (chartAt ℂ (f x) (f (utm_pext p₀ z))) ∈ _
    rw [(chartAt ℂ (f x)).left_inv (hsrc z hz)]
    exact mem_chart_source ℂ y
  obtain ⟨hT1, hT2, -⟩ := s23_transition_mem hgz hgz'
  have hc : ContinuousAt g z := (hgK.2.2.1.1 z hz).continuousAt (hUo.mem_nhds hz)
  have h1 : complexDilatation (fun w => chartAt ℂ y (f (utm_pext p₀ w))) z =
      complexDilatation (chartTransition y (f x) ∘ g) z := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  rw [h1]
  exact s23_dilatation_comp_left hc (s23_transition y (f x) hgz hgz').1 (s23_transition (f x) y hT1 hT2).1
    (s23_transition_inv y (f x) hgz hgz')

/-- **[U2, stub] Automorphy (23.5) of the lifted coefficient, at every point of `ℍ`.**  For `γ ∈ Γ₀`,
`μ(z) = μ(γ z) (c z + d)²/conj((c z + d)²)`.  No quasiconformality or manifold hypothesis is needed.

*Why true.*  `p₀ ∘ γ = p₀`, since the fibres of `p₀` are the `Γ₀`-orbits.  So on all of `ℍ` the chart expressions at
`z` and at `γ z` satisfy `g_{γ z} ∘ γ = g_z`: both use the chart at `f(p₀ z) = f(p₀ (γ z))`.  Then
`μ_{g_z}(z) = μ_{g_{γ z}}(γ z) conj γ'(z)/γ'(z)` (`s23_dilatation_comp_right`), with `γ'(z) = (c z + d)⁻²`.

*Reuse.*  S23: `h23l_dilatation_conj` l.927 (the same computation for `liftToC F`), `h23l_b_mob` l.878,
`h23l_b_coe_smul` l.845, `h23l_b_det` l.851, `h23l_b_den_ne` l.858, `s23_dilatation_comp_right` l.162.  Here:
`s27u_liftCoeff_of_mem`, `utm_a_pext_eq`, `s27u_pext_coe`.

*Estimate.*  50–90 lines. -/
theorem s27u_liftCoeff_compat {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (f : S₀ → S) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀)
    {z : ℂ} (hz : z ∈ upperHalf) :
    s27u_liftCoeff p₀ f z = s27u_liftCoeff p₀ f ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  have hz' : 0 < z.im := hz
  -- `p̂₀ ∘ γ = p̂₀` on `ℍ`: the fibres of `p₀` are the `Γ₀`-orbits
  have hpγ : ∀ w : ℂ, 0 < w.im →
      utm_pext p₀ (((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) = utm_pext p₀ w := by
    intro w hw
    have e1 : ((γ • (⟨w, hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
        ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1) := h23l_b_coe_smul γ ⟨w, hw⟩
    have e2 : utm_pext p₀ w = p₀ ⟨w, hw⟩ := s27u_pext_coe p₀ ⟨w, hw⟩
    rw [← e1, s27u_pext_coe, e2]
    exact ((hp₀.2.2.2 ⟨w, hw⟩ (γ • ⟨w, hw⟩)).2 ⟨γ, hγ, rfl⟩).symm
  have hTz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf := by
    have e1 : ((γ • (⟨z, hz'⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
        ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := h23l_b_coe_smul γ ⟨z, hz'⟩
    show 0 < (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)).im
    rw [← e1]
    exact UpperHalfPlane.coe_im_pos _
  rw [s27u_liftCoeff_of_mem p₀ f hz, s27u_liftCoeff_of_mem p₀ f hTz, hpγ z hz']
  set g : ℂ → ℂ := fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))
  obtain ⟨hTd, hSd, hST, hTS, hTder⟩ := h23l_b_mob (h23l_b_det γ) (h23l_b_den_ne γ hz)
  -- `g ∘ γ = g` near `z`
  have hev : (g ∘ fun w => ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    show chartAt ℂ (f (utm_pext p₀ z))
        (f (utm_pext p₀ (((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)))) =
      chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))
    rw [hpγ w hw]
  have h2 := s23_dilatation_comp_right (g := g) hTd hSd hST hTS
  have h3 : complexDilatation (g ∘ fun w => ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) z =
      complexDilatation g z := by
    rw [complexDilatation, complexDilatation, dz, dzbar, dz, dzbar, hev.fderiv_eq]
  rw [← h3, h2, hTder]
  congr 1
  rw [map_div₀, map_one, div_div_div_cancel_left' _ _ one_ne_zero]

/-- The lifted coefficient is `Γ₀`-compatible (from U2, at every point of `ℍ`). -/
theorem s27u_liftCoeff_isGammaCompatible {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (f : S₀ → S) : IsGammaCompatible Γ₀ (s27u_liftCoeff p₀ f) := by
  exact fun _ hγ => ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun _ hz =>
    s27u_liftCoeff_compat hp₀ f hγ hz

/-- **[U3, stub] The lifted coefficient is a Beltrami coefficient on `ℍ` with `‖μ‖∞ ≤ (K - 1)/(K + 1)`.**

*Why true.*  By U1, every `z₀ ∈ ℍ` has an open `U ∋ z₀` on which `μ = μ_g` with `g` `K`-q.c.  There `μ_g` is
measurable (`measurable_dzbar`, `measurable_dz`, S06 l.790–794), and `‖μ_g‖ ≤ (K - 1)/(K + 1)` a.e.
(`isKQC_maxDilatation_le`, S10 l.353).  Countably many such `U` cover `ℍ` (`TopologicalSpace.isOpen_iUnion_countable`),
and measurability and the a.e. bound pass to countable unions (`aestronglyMeasurable_iUnion_iff`,
`ae_restrict_iUnion_iff`).

*Reuse.*  U1 (`s27u_liftCoeff_local`).  S33 `normalizedLift_beltrami_mem` (l.45) proves the same bound for a lift.

*Estimate.*  90–180 lines. -/
theorem s27u_liftCoeff_isBeltramiCoeff [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) :
    IsBeltramiCoeff (s27u_liftCoeff p₀ f) upperHalf ((K - 1) / (K + 1)) := by
  refine ⟨?_, s13x_ae_of_local (L := ∅) measure_empty fun z hz => ?_⟩
  · choose! W hWo hzW _hWH _hWs _hWK hμ using fun z (hz : z ∈ upperHalf) => s27u_liftCoeff_local hp₀ hf hz
    obtain ⟨T, hTsub, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_biUnion_countable upperHalf W fun z hz => hWo z hz
    have hcov : upperHalf ⊆ ⋃ z ∈ T, W z := by
      intro w hw
      rw [hTeq]
      exact mem_biUnion hw (hzW w hw)
    refine AEStronglyMeasurable.mono_set hcov ?_
    have : Countable T := hTc.to_subtype
    rw [biUnion_eq_iUnion, aestronglyMeasurable_iUnion_iff]
    rintro ⟨z, hz⟩
    have hm := (measurable_dzbar (fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w)))).div
      (measurable_dz (fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))))
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem (hWo z (hTsub hz)).measurableSet] with w hw
    exact (hμ z (hTsub hz) w hw).symm
  · obtain ⟨W, hWo, hzW, -, -, hWK, hμ⟩ := s27u_liftCoeff_local hp₀ hf hz.1
    refine ⟨W, hWo, hzW, ?_⟩
    filter_upwards [(isKQC_maxDilatation_le hWK).2, ae_restrict_mem hWo.measurableSet] with w hw hwW
    rw [hμ w hwW]
    exact hw

/-- **The lifted coefficient of a q.c. marking lies in `M(Γ₀)`**: it is an element of `M` (`BeltramiH`) and it is
`Γ₀`-compatible (from U2 and U3; `0` off `ℍ` by definition). -/
theorem s27u_liftCoeff_beltramiH [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} (hf : IsQCRS f) :
    ∃ μ : BeltramiH, μ.1 = s27u_liftCoeff p₀ f ∧ IsGammaCompatible Γ₀ μ.1 := by
  obtain ⟨K, hK⟩ := hf
  have hK1 : (1 : ℝ) ≤ K := hK.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨hm, hb⟩ := s27u_liftCoeff_isBeltramiCoeff hp₀ hK
  have hind : upperHalf.indicator (s27u_liftCoeff p₀ f) = s27u_liftCoeff p₀ f := by
    funext z
    by_cases hz : z ∈ upperHalf
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, s27u_liftCoeff_of_not_mem p₀ f hz]
  have hB : IsBeltramiCoeff (s27u_liftCoeff p₀ f) univ ((K - 1) / (K + 1)) := by
    rw [IsBeltramiCoeff, Measure.restrict_univ]
    refine ⟨?_, ?_⟩
    · rw [← hind]
      exact (aestronglyMeasurable_indicator_iff isOpen_upperHalf.measurableSet).2 hm
    · rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hb
      filter_upwards [hb] with z hz
      by_cases hzU : z ∈ upperHalf
      · exact hz hzU
      · rw [s27u_liftCoeff_of_not_mem p₀ f hzU, norm_zero]
        exact hk0
  refine ⟨⟨s27u_liftCoeff p₀ f, ⟨_, hk0, hk1, hB⟩, fun z hz => ?_⟩, rfl,
    s27u_liftCoeff_isGammaCompatible hp₀ f⟩
  exact s27u_liftCoeff_of_not_mem p₀ f fun h => absurd hz (not_le.2 (show 0 < z.im from h))

/-- Verbatim copy of S33 `bg_s_conj_preimage_upperHalf` (S33 imports S27, so it cannot be imported here).
Complex conjugation maps `𝕃` onto `ℍ`: the preimage of `ℍ` under `z ↦ z̄` is `𝕃`. -/
theorem s27u_b_s_conj_preimage_upperHalf : (fun z : ℂ => conj z) ⁻¹' upperHalf = lowerHalf := by
  ext z
  simp only [mem_preimage, upperHalf, lowerHalf, mem_ofPred_eq, Complex.conj_im, neg_pos]

/-- Verbatim copy of S33 `bg_s_beltrami` (S33 imports S27, so it cannot be imported here).
The symmetric extension of a Beltrami coefficient on `ℍ` bounded by `k` is a Beltrami coefficient on `ℂ` bounded
by `k`: on `𝕃` it is `conj ∘ μ ∘ conj`, conjugation maps `𝕃` measure-preservingly onto `ℍ`, and `ℝ` is null. -/
theorem s27u_b_s_beltrami {μ : ℂ → ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (s27u_symExt μ) univ k := by
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict lowerHalf)
      (volume.restrict upperHalf) := by
    have h := gzE_conj_measurePreserving.restrict_preimage isOpen_upperHalf.measurableSet
    rwa [s27u_b_s_conj_preimage_upperHalf] at h
  rw [IsBeltramiCoeff, Measure.restrict_univ]
  refine ⟨?_, ?_⟩
  · -- measurability: `conj ∘ μ ∘ conj` on `𝕃`, and `μ` on `{Im z ≥ 0} = ℍ ∪ ℝ` with `ℝ` null
    have hL : AEStronglyMeasurable (fun z => conj (μ (conj z))) (volume.restrict lowerHalf) :=
      Complex.continuous_conj.comp_aestronglyMeasurable (hμ.1.comp_measurePreserving hmp)
    have hC : AEStronglyMeasurable μ (volume.restrict lowerHalfᶜ) := by
      have hsplit : lowerHalfᶜ = upperHalf ∪ {z : ℂ | z.im = 0} := by
        ext z
        simp only [mem_compl_iff, lowerHalf, upperHalf, mem_union, mem_ofPred_eq, not_lt]
        constructor
        · intro h
          rcases h.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h.symm
        · rintro (h | h)
          · exact h.le
          · exact h.ge
      rw [hsplit, aestronglyMeasurable_union_iff]
      refine ⟨hμ.1, ?_⟩
      rw [Measure.restrict_eq_zero.2 gzE_volume_im_eq_zero]
      exact aestronglyMeasurable_zero_measure μ
    classical
    have heq : s27u_symExt μ = lowerHalf.piecewise (fun z => conj (μ (conj z))) μ := by
      funext z
      by_cases hz : z.im < 0
      · rw [Set.piecewise_eq_of_mem lowerHalf _ _ (show z ∈ lowerHalf from hz), s27u_symExt,
          ite_eq_left hz]
      · rw [Set.piecewise_eq_of_notMem lowerHalf _ _ (show z ∉ lowerHalf from hz), s27u_symExt,
          ite_eq_right hz]
    rw [heq]
    exact hL.piecewise isOpen_lowerHalf.measurableSet.nullMeasurableSet hC
  · -- the bound: `σ = μ` on `ℍ`, and `‖σ z‖ = ‖μ z̄‖` on `𝕃`
    refine k24_ae_of_halves ?_ ?_
    · filter_upwards [hμ.2, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2
      rw [s27u_symExt, ite_eq_right (not_lt.2 (le_of_lt h2))]
      exact h1
    · filter_upwards [hmp.quasiMeasurePreserving.ae hμ.2,
        ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 h2
      rw [s27u_symExt, ite_eq_left (show z.im < 0 from h2), Complex.norm_conj]
      exact h1

/-- **[U4, stub; COPY] The symmetric solution.**  This is S33 `bg_sym_spec` (l.374), verbatim up to the `s27u_` names.
For `‖μ‖ ≤ k < 1` a.e. on `ℍ`: the symmetric extension is a Beltrami coefficient on `ℂ` bounded by `k`; `f^μ` is its
normalized solution, `(1 + k)/(1 - k)`-q.c. on `ℂ`; and it is the only one.

*Why true.*  Proved in S33, axiom-clean; this exact statement is `s27u_probe_U4` in `s27t/stageU/U_truth_probe.lean`
(`:= bg_sym_spec hk₀ hk hμ`).  Apply Theorem 13.7 (`thm13_7_normalized_existence`, S13 l.5763) to the symmetric
coefficient.  Its measurability and bound hold because `z ↦ z̄` maps `𝕃` onto `ℍ` measure-preservingly and `ℝ` is
null.

*Copy.*  From S33: `bg_s_conj_preimage_upperHalf` l.173, `bg_s_beltrami` l.179, `bg_sym_spec` l.374.  S33 l.94–98
(`symmetricExtension`, `fMuSym`) are already `s27u_symExt`, `s27u_fSym` here.  Use S24 `k24_ae_of_halves` (l.54,
upstream) for `bg_ae_of_halves`.  Everything they use is upstream (S05 `gzE_conj_measurePreserving`,
`gzE_volume_im_eq_zero`).

*Estimate.*  ≈ 75 lines (copy). -/
theorem s27u_sym_spec {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (s27u_symExt μ) univ k ∧ IsNormalizedSolution (s27u_fSym μ) (s27u_symExt μ) ∧
      IsKQC (s27u_fSym μ) univ ((1 + k) / (1 - k)) ∧
      ∀ g : ℂ → ℂ, IsNormalizedSolution g (s27u_symExt μ) → g = s27u_fSym μ := by
  have hσ := s27u_b_s_beltrami hμ
  obtain ⟨f₀, hf₀, hK, huniq⟩ := thm13_7_normalized_existence hk₀ hk hσ
  have hex : ∃ f : ℂ → ℂ, IsNormalizedSolution f (s27u_symExt μ) := ⟨f₀, hf₀⟩
  have hspec : IsNormalizedSolution (s27u_fSym μ) (s27u_symExt μ) := by
    rw [s27u_fSym, normalizedSolution, dite_eq_left hex]
    exact hex.choose_spec
  have heq : s27u_fSym μ = f₀ := huniq _ hspec
  refine ⟨hσ, hspec, ?_, fun g hg => (huniq g hg).trans heq.symm⟩
  rw [heq]
  exact hK

/-- Verbatim copy of S33 `bg_dilatation_conj` (S33 imports S27, so it cannot be imported here).
The complex dilatation of the reflected map `z ↦ conj (f (conj z))` at `z` is the conjugate of that of `f` at
`conj z` (`abR_x_dz_dzbar_conj`; where `f` is not differentiable both sides vanish). -/
theorem s27u_b_dilatation_conj (f : ℂ → ℂ) (z : ℂ) :
    complexDilatation (fun w => conj (f (conj w))) z = conj (complexDilatation f (conj z)) := by
  by_cases hd : DifferentiableAt ℝ f (conj z)
  · obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hd
    rw [complexDilatation, complexDilatation, h1, h2, map_div₀]
  · have hd' : ¬ DifferentiableAt ℝ (fun w => conj (f (conj w))) z := by
      intro h
      apply hd
      have h' : DifferentiableAt ℝ (fun w => conj (f (conj w))) (conj (conj z)) := by
        rwa [Complex.conj_conj]
      simpa only [Complex.conj_conj] using (abR_x_dz_dzbar_conj h').1
    simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt hd']

/-- Verbatim copy of S33 `bg_s_symm_conj` (S33 imports S27, so it cannot be imported here).
The symmetric extension is symmetric off `ℝ`: `conj σ(z̄) = σ(z)` for `Im z ≠ 0`. -/
theorem s27u_b_s_symm_conj (μ : ℂ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    conj (s27u_symExt μ (conj z)) = s27u_symExt μ z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hc : ¬ (conj z).im < 0 := by
      rw [Complex.conj_im]
      linarith
    rw [s27u_symExt, ite_eq_right hc, s27u_symExt, ite_eq_left h]
  · have hc : (conj z).im < 0 := by
      rw [Complex.conj_im]
      linarith
    rw [s27u_symExt, ite_eq_left hc, Complex.conj_conj, Complex.conj_conj, s27u_symExt,
      ite_eq_right (not_lt.2 h.le)]

/-- Verbatim copy of S33 `bg_s_conj_comm` (S33 imports S27, so it cannot be imported here).
The unique normalized solution `f` for a symmetric extension commutes with the reflection `z ↦ z̄`:
`z ↦ conj f(z̄)` is again a normalized solution for it (`abR_x_isKQC_conj`, `bg_dilatation_conj`, and `bg_s_symm_conj`
off the null line `ℝ`), so it is `f` by uniqueness. -/
theorem s27u_b_s_conj_comm {μ f : ℂ → ℂ} (hN : IsNormalizedSolution f (s27u_symExt μ))
    (huniq : ∀ g : ℂ → ℂ, IsNormalizedSolution g (s27u_symExt μ) → g = f) (z : ℂ) :
    f (conj z) = conj (f z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hN
  have hgK : IsKQC (fun w => conj (f (conj w))) univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hgs : (fun w => conj (f (conj w))) '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ f '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [Complex.conj_conj, hv]⟩
  have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hgd : ∀ᵐ w, complexDilatation (fun w => conj (f (conj w))) w = s27u_symExt μ w := by
    filter_upwards [gzE_conj_measurePreserving.quasiMeasurePreserving.ae hd, hnull] with w hw1 hw2
    rw [s27u_b_dilatation_conj, hw1]
    exact s27u_b_s_symm_conj μ hw2
  have hg : IsNormalizedSolution (fun w => conj (f (conj w))) (s27u_symExt μ) :=
    ⟨⟨_, hgK⟩, hgs, by simp [h0], by simp [h1], hgd⟩
  have h := congrFun (huniq _ hg) z
  rw [← h, Complex.conj_conj]

/-- Verbatim copy of S33 `bg_s_not_swap` (S33 imports S27, so it cannot be imported here).
A `K`-q.c. self-map `Ψ` of `ℂ` which is real on `ℝ` and fixes `0` and `1` cannot map `ℍ` onto `𝕃`: otherwise `-Ψ`
would be a `K`-q.c. self-map of `ℍ` fixing `∞` with boundary values `x ↦ -Re Ψ(x)`, which are increasing by
`b4_qs_monotone` but take the values `0` at `0` and `-1` at `1` (the argument of `ut_w0_not_swap`). -/
theorem s27u_b_s_not_swap {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (hreal : ∀ x : ℝ, (Ψ x).im = 0) (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) : Ψ '' upperHalf ≠ lowerHalf := by
  intro hswap
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  set E : ExtPlane ≃ₜ ExtPlane := (e.trans (Homeomorph.neg ℂ)).onePointCongr with hEdef
  have hEc : ∀ z : ℂ, E (z : ExtPlane) = ((-Ψ z : ℂ) : ExtPlane) := fun z => by
    rw [hEdef, Homeomorph.onePointCongr_apply, OnePoint.map_some, Homeomorph.trans_apply,
      Homeomorph.coe_neg, he]
  obtain ⟨hK, -⟩ := b4_rat_affine_comp hΨ hs (0 : ℂ) (0 : ℂ) one_ne_zero (neg_ne_zero.2 one_ne_zero)
  have hfun : (fun z => (-1 : ℂ) * Ψ (1 * z + 0) + 0) = fun z => -Ψ z := by
    funext z
    simp
  rw [hfun] at hK
  have hgK : IsKQC (fun z => -Ψ z) upperHalf K :=
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hgs : (fun z => -Ψ z) '' upperHalf = upperHalf := by
    rw [← Set.image_image (fun w : ℂ => -w) Ψ, hswap]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (-z).im
      rw [Complex.neg_im]
      exact neg_pos.2 hz
    · intro hw
      refine ⟨-w, ?_, neg_neg w⟩
      show (-w).im < 0
      rw [Complex.neg_im]
      exact neg_neg_iff_pos.2 hw
  have htoExt : E '' toExt upperHalf = toExt upperHalf := by
    unfold toExt
    rw [Set.image_image]
    simp_rw [hEc]
    rw [← Set.image_image (fun w : ℂ => (w : ExtPlane)) (fun z => -Ψ z), hgs]
  have hext : IsHomeoExtension (fun z => -Ψ z) upperHalf upperHalf E := by
    refine ⟨fun z _ => hEc z, E.continuous.continuousOn, E.injective.injOn, ?_⟩
    rw [Homeomorph.image_closure, htoExt]
  have hmono := (b4_qs_monotone (h := fun x : ℝ => -(Ψ x).re)
    ⟨hgK, hgs, E, hext, rfl, fun x => by
      rw [hEc]
      congr 1
      exact Complex.ext (by simp) (by simp [hreal x])⟩).1
  have h01 := hmono (show (0 : ℝ) < 1 from one_pos)
  norm_num [h0, h1] at h01

/-- Verbatim copy of S33 `bg_s_image_upperHalf` (S33 imports S27, so it cannot be imported here).
A `K`-q.c. self-map `Ψ` of `ℂ` fixing `0` and `1` and commuting with `z ↦ z̄` maps `ℍ` onto `ℍ`: `Ψ(z)` is real
only for real `z` (symmetry and injectivity), so the connected set `Ψ(ℍ)` lies in `ℍ` or in `𝕃`; by symmetry and
surjectivity it is then all of `ℍ` or all of `𝕃`, and the latter is excluded by `bg_s_not_swap`. -/
theorem s27u_b_s_image_upperHalf {Ψ : ℂ → ℂ} {K : ℝ} (hΨ : IsKQC Ψ univ K) (hs : Ψ '' univ = univ)
    (h0 : Ψ 0 = 0) (h1 : Ψ 1 = 1) (hsym : ∀ z, Ψ (conj z) = conj (Ψ z)) : Ψ '' upperHalf = upperHalf := by
  obtain ⟨e, he⟩ := t1_homeomorph hΨ hs
  have hc : Continuous Ψ := he ▸ e.continuous
  have hinj : Function.Injective Ψ := he ▸ e.injective
  have hsurj : Function.Surjective Ψ := he ▸ e.surjective
  -- `Ψ` is real exactly on `ℝ`
  have hreal : ∀ x : ℝ, (Ψ x).im = 0 := fun x => by
    have h := hsym x
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hre : ∀ z : ℂ, z.im = 0 → (Ψ z).im = 0 := fun z hz => by
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by rw [hz, Complex.ofReal_im])
    rw [hz']
    exact hreal z.re
  have hnr : ∀ z : ℂ, z.im ≠ 0 → (Ψ z).im ≠ 0 := fun z hz him => by
    have h : Ψ (conj z) = Ψ z := by rw [hsym, Complex.conj_eq_iff_im.2 him]
    exact hz (Complex.conj_eq_iff_im.1 (hinj h))
  have hconj : ∀ z : ℂ, z.im < 0 → conj z ∈ upperHalf := fun z hz => by
    show 0 < (conj z).im
    rw [Complex.conj_im]
    linarith
  -- `Ψ(ℍ)` is preconnected and misses `ℝ`
  have hor : Ψ '' upperHalf ⊆ upperHalf ∨ Ψ '' upperHalf ⊆ lowerHalf := by
    refine (isConnected_upperHalf.isPreconnected.image Ψ hc.continuousOn).subset_or_subset
      isOpen_upperHalf isOpen_lowerHalf ?_ ?_
    · exact Set.disjoint_left.2 fun z h₁ h₂ => lt_asymm (show 0 < z.im from h₁) (show z.im < 0 from h₂)
    · rintro _ ⟨z, hz, rfl⟩
      rcases lt_or_gt_of_ne (hnr z (show 0 < z.im from hz).ne') with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases hor with hU | hU
  · refine subset_antisymm hU fun w hw => ?_
    obtain ⟨z, rfl⟩ := hsurj w
    have hw' : 0 < (Ψ z).im := hw
    rcases lt_trichotomy z.im 0 with h | h | h
    · have h2 : 0 < (Ψ (conj z)).im := hU (mem_image_of_mem Ψ (hconj z h))
      rw [hsym, Complex.conj_im] at h2
      linarith
    · rw [hre z h] at hw'
      exact absurd hw' (lt_irrefl 0)
    · exact ⟨z, h, rfl⟩
  · refine absurd (subset_antisymm hU fun w hw => ?_) (s27u_b_s_not_swap hΨ hs hreal h0 h1)
    obtain ⟨z, rfl⟩ := hsurj w
    have hw' : (Ψ z).im < 0 := hw
    rcases lt_trichotomy z.im 0 with h | h | h
    · have h2 : (Ψ (conj z)).im < 0 := hU (mem_image_of_mem Ψ (hconj z h))
      rw [hsym, Complex.conj_im] at h2
      linarith
    · rw [hre z h] at hw'
      exact absurd hw' (lt_irrefl 0)
    · exact ⟨z, h, rfl⟩

/-- **[U4', stub; COPY] `f^μ` preserves `ℍ`.**  This is S33 `fMuSym_upperHalf` (l.391), verbatim up to the `s27u_`
names.  `f^μ` maps `ℍ` onto `ℍ`, is real on `ℝ`, commutes with `z ↦ z̄`, and is `(1 + k)/(1 - k)`-q.c. on `ℍ` with
dilatation `μ` a.e.

*Why true.*  Proved in S33, axiom-clean; this exact statement is `s27u_probe_U4'` in `U_truth_probe.lean`.
`z ↦ conj f^μ(z̄)` is again a normalized solution, so it is `f^μ` (U4 uniqueness).  A symmetric q.c. self-map of `ℂ`
fixing `0` and `1` maps `ℍ` onto `ℍ`: a swap `ℍ → 𝕃` would make `x ↦ -Re Ψ(x)` increasing (`b4_qs_monotone`), yet
it sends `0 ↦ 0` and `1 ↦ -1`.

*Copy.*  From S33: `bg_dilatation_conj` l.122, `bg_s_symm_conj` l.227, `bg_s_conj_comm` l.243, `bg_s_not_swap` l.271,
`bg_s_image_upperHalf` l.318, `fMuSym_upperHalf` l.391.  All inputs are upstream: S13 `abR_x_isKQC_conj`,
`abR_x_dz_dzbar_conj`, `t1_homeomorph`; S17 `b4_rat_affine_comp`, `b4_qs_monotone`; S05 `isConnected_upperHalf`.

*Estimate.*  ≈ 180 lines (copy). -/
theorem s27u_fSym_upperHalf {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    s27u_fSym μ '' upperHalf = upperHalf ∧ (∀ x : ℝ, (s27u_fSym μ x).im = 0) ∧
      (∀ z, s27u_fSym μ (conj z) = conj (s27u_fSym μ z)) ∧ IsKQC (s27u_fSym μ) upperHalf ((1 + k) / (1 - k)) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (s27u_fSym μ) z = μ z := by
  obtain ⟨-, hN, hK, huniq⟩ := s27u_sym_spec hk₀ hk hμ
  have hsym : ∀ z, s27u_fSym μ (conj z) = conj (s27u_fSym μ z) := s27u_b_s_conj_comm hN huniq
  obtain ⟨-, hs, h0, h1, hd⟩ := hN
  have hreal : ∀ x : ℝ, (s27u_fSym μ x).im = 0 := fun x => by
    have h := hsym x
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  refine ⟨s27u_b_s_image_upperHalf hK hs h0 h1 hsym, hreal, hsym,
    ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _), ?_⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz1 hz2
  rw [hz1, s27u_symExt, ite_eq_right (not_lt.2 (le_of_lt hz2))]

/-- **[U5, stub; COPY] `w|ℍ` as a homeomorphism of `ℍ`.**  This is S33 `b33_d_homeo_upper` (l.3629), verbatim up to the
name.

*Why true.*  `w` is a homeomorphism of `ℂ` (`t1_homeomorph`, S13 l.4730) mapping `ℍ` onto `ℍ`; restrict it and its
inverse to `ℍ`.  This exact statement is `s27u_probe_U5` in `U_truth_probe.lean`.

*Estimate.*  ≈ 30 lines (copy). -/
theorem s27u_homeo_upper {f : ℂ → ℂ} {K : ℝ} (hK : IsKQC f univ K) (hs : f '' univ = univ)
    (hU : f '' upperHalf = upperHalf) : ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, ∀ τ, (F τ : ℂ) = f τ := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hiff : ∀ z : ℂ, 0 < z.im ↔ 0 < (e z).im := by
    intro z
    constructor
    · intro hz
      have hm : f z ∈ f '' upperHalf := mem_image_of_mem f hz
      rw [hU] at hm
      rw [he]
      exact hm
    · intro hz
      have hm : e z ∈ upperHalf := hz
      rw [he, ← hU] at hm
      obtain ⟨w, hw, hfw⟩ := hm
      rw [← he] at hfw
      rw [← e.injective hfw]
      exact hw
  have hiff' : ∀ τ : UpperHalfPlane, 0 < (e.symm τ).im := fun τ =>
    (hiff _).2 (by rw [e.apply_symm_apply]; exact τ.coe_im_pos)
  refine ⟨{ toFun := fun τ => ⟨e τ, (hiff τ).1 τ.coe_im_pos⟩
            invFun := fun τ => ⟨e.symm τ, hiff' τ⟩
            left_inv := fun τ => UpperHalfPlane.ext (by simp)
            right_inv := fun τ => UpperHalfPlane.ext (by simp)
            continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.2
              (e.continuous.comp UpperHalfPlane.continuous_coe)
            continuous_invFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.2
              (e.symm.continuous.comp UpperHalfPlane.continuous_coe) }, fun τ => ?_⟩
  show e τ = f τ
  rw [he]

/-- Verbatim copy of S33 `bg_conformal_of_dilatation_eq` (S33 imports S27, so it cannot be imported here).
Two quasiconformal maps of an open set `D` with a.e. equal complex dilatations differ by a conformal map: `g ∘ f⁻¹`
maps `f(D)` conformally onto `g(D)` (`same_dilatation_conformal`). -/
theorem s27u_b_conformal_of_dilatation_eq {f g : ℂ → ℂ} {D : Set ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f D K₁)
    (hg : IsKQC g D K₂) (h : ∀ᵐ z ∂(volume.restrict D), complexDilatation g z = complexDilatation f z) :
    IsConformalOnto (g ∘ Function.invFunOn f D) (f '' D) (g '' D) := by
  obtain ⟨hμ, hfs⟩ := thm10_2_genHomeoSolution_of_isKQC hf
  have hgs := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hg).2 h
  have hK1 : (1 : ℝ) ≤ K₁ := hf.2.1
  have hk : (K₁ - 1) / (K₁ + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal hf.1 hk hμ hfs hgs
  have heq : EqOn (g ∘ Function.invFunOn f D) φ (f '' D) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, hf.2.2.1.2.1.leftInvOn_invFunOn hz, hgφ z hz]
  exact ⟨hφ.1.congr heq, hφ.2.1.congr heq.symm, heq.image_eq.trans hφ.2.2⟩

/-- **[U6, stub] `F ∘ γ ∘ F⁻¹` is Möbius.**  Let `μ` be a `Γ₀`-compatible Beltrami coefficient on `ℍ` and
`F = f^μ|ℍ`.  For every `γ ∈ Γ₀` there is `γ' ∈ SL(2, ℝ)` with `F ∘ γ = γ' ∘ F` on `ℍ`.

*Why true.*  Write `w = f^μ` and `v = w ∘ γ`.
- Both are q.c. on `ℍ` (`thm7_1_comp`, with `γ` conformal on `ℍ`).
- They have the same dilatation a.e. on `ℍ`:
  - `μ_v(z) = μ_w(γ z)(c z + d)²/conj((c z + d)²)` (`k24_d_dil_mobius`, S24 l.79);
  - `μ_w(γ z) = μ(γ z)` a.e. (`s23_c2_ae_pullback`, S23 l.578, through `γ`);
  - then `Γ₀`-compatibility.
- Hence `v ∘ w⁻¹` is conformal from `w(ℍ) = ℍ` onto `v(ℍ) = ℍ`.  This is the similarity principle: copy S33
  `bg_conformal_of_dilatation_eq` (l.144, 15 lines, from `same_dilatation_conformal`, S13 l.3616).
- So `Φ = F ∘ γ ∘ F⁻¹` has a `1`-q.c. `liftToC`, and `utm_eq_smul_of_isKQC_one` (S23 l.1881) gives `Φ = γ' •`.

*Alternative (S33 route, machine-checked).*  `s27u_probe_U6` in `U_truth_probe.lean` proves this exact statement in
45 lines from S33 `b33_d_def` (l.3487), `b33_d_rel_iff` (l.3661) and U11, applied to `𝟙_ℍ μ ∈ M(Γ₀)`.  Inside S27
this needs a copy of `b33_d_def` with `b33_d_sym_compat`, `b33_d_pullback`, `b33_d_dil_comp`, `b33_d_mob_affine2`,
`b33_d_mob_pole2`, `b33_d_rescale`, `b33_d_rel_iff` and small helpers (≈ 340 lines).  The MOB core is upstream as S24
`k24_mob_core`, but it yields a complex Möbius map, not a real one.

*Reuse.*  U4, U4'; S23 `h23l_liftToC_eq` l.743, `h36t_coe_smul` l.1344; S07 `isKQC_one_of_conformal` l.171;
`Lemmas/Mobius` `mobiusFn_mem_upperHalf` l.301, `isConformalOnto_mobius_upperHalf` l.309.

*Estimate.*  120–220 lines. -/
theorem s27u_conj_mobius {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {μ : ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) (hΓ : IsGammaCompatible Γ₀ μ)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ τ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F (γ • τ) = γ' • F τ := by
  -- `w = f^μ` is q.c. on `ℂ` and on `ℍ`, maps `ℍ` onto `ℍ`, with dilatation `μ` a.e. on `ℍ` (U4, U4')
  obtain ⟨-, -, hwK, -⟩ := s27u_sym_spec hk₀ hk hμ
  obtain ⟨hwU, -, -, hwKU, hwd⟩ := s27u_fSym_upperHalf hk₀ hk hμ
  -- `γ` is a conformal self-map of `ℍ`
  have hdetR : 0 < γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [h]
    exact one_pos
  have hTc := isConformalOnto_mobius_upperHalf hdetR
  have hT1 := isKQC_one_of_conformal isOpen_upperHalf hTc
  -- `v = w ∘ γ` is q.c. on `ℍ`, maps `ℍ` onto `ℍ`, and has the dilatation of `w` a.e. on `ℍ`:
  -- `μ_v(z) = μ_w(γ z) (c z + d)²/conj((c z + d)²) = μ(γ z) (c z + d)²/conj((c z + d)²) = μ(z) = μ_w(z)`
  have hvK := thm7_1_comp hT1 hwK (subset_univ _)
  have hvU : (s27u_fSym μ ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' upperHalf = upperHalf := by
    rw [image_comp, hTc.2.2, hwU]
  have hpb : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (s27u_fSym μ)
      (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = μ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) :=
    s23_c2_ae_pullback (P := fun u => complexDilatation (s27u_fSym μ) u = μ u) hT1 hTc.2.2.subset hwd
  have hdil : ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (s27u_fSym μ ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z =
        complexDilatation (s27u_fSym μ) z := by
    filter_upwards [hpb, hΓ γ hγ, hwd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 h3 hz
    rw [k24_d_dil_mobius _ (h23l_b_det γ) (h23l_b_den_ne γ hz), h1, h3]
    exact h2.symm
  -- the similarity principle: `v ∘ w⁻¹` is a conformal self-map of `ℍ`
  have hconf : IsConformalOnto ((s27u_fSym μ ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) ∘
      Function.invFunOn (s27u_fSym μ) upperHalf) upperHalf upperHalf := by
    have h := s27u_b_conformal_of_dilatation_eq hwKU hvK hdil
    rwa [hwU, hvU] at h
  -- `Φ = F ∘ γ ∘ F⁻¹` is `v ∘ w⁻¹` on `ℍ`, hence `1`-q.c., hence Möbius (`utm_eq_smul_of_isKQC_one`)
  have hΦ : IsKQC (liftToC ((F.symm.trans (Homeomorph.smul γ)).trans F)) upperHalf 1 := by
    refine ad_isKQC_congr (isKQC_one_of_conformal isOpen_upperHalf hconf) fun z hz => ?_
    have hz' : 0 < z.im := hz
    have hwz : s27u_fSym μ ((F.symm ⟨z, hz'⟩ : UpperHalfPlane) : ℂ) = z := by
      rw [← hF, F.apply_symm_apply]
    have hinv := hwKU.2.2.1.2.1.leftInvOn_invFunOn (F.symm ⟨z, hz'⟩).coe_im_pos
    rw [hwz] at hinv
    show liftToC _ ((⟨z, hz'⟩ : UpperHalfPlane) : ℂ) = _
    rw [h23l_liftToC_coe, Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.smul_apply, hF,
      h36t_coe_smul, Function.comp_apply, Function.comp_apply, hinv]
    rfl
  obtain ⟨m, hm⟩ := utm_eq_smul_of_isKQC_one _ hΦ
  refine ⟨m, fun τ => ?_⟩
  have h := hm (F τ)
  rwa [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, Homeomorph.smul_apply] at h

/-- **[U7, stub] The transported projection is holomorphic**: `p = f ∘ p₀ ∘ F⁻¹`, where `F = f^μ|ℍ` and
`μ = s27u_liftCoeff p₀ f`.

*Why true.*
- Fix `τ₁` and `z₀ = F⁻¹ τ₁`.  U1 gives `U ∋ z₀` and `g = φ_{y₀} ∘ f ∘ p̂₀`, `K`-q.c. on `U` with `μ_g = μ` on `U`.
- Since `μ_w = μ` a.e. on `ℍ` (U4'), `g ∘ w⁻¹` is conformal on the open set `w(U) ∋ τ₁` (copy S33
  `bg_conformal_of_dilatation_eq`, l.144).
- On `w(U)`, `φ_{y₀} ∘ p ∘ ofComplex = g ∘ w⁻¹`, because `p(F z) = f(p₀ z)`.  So it is complex differentiable at `τ₁`.
- Near `τ₁`, `p = φ_{y₀}⁻¹ ∘ (φ_{y₀} ∘ p)`, which gives `MDifferentiableAt` (`UpperHalfPlane.mdifferentiableAt_iff`,
  `mdifferentiableAt_atlas_symm`; or `s23_mdifferentiableAt_iff`, S23 l.196, with the singleton chart of `ℍ`).

*Reuse.*  U1, U3, U4, U4'; S13 `same_dilatation_conformal` l.3616, `nxS_genHomeoSolution_congr` l.5656; S10
`thm10_2_genHomeoSolution_of_isKQC` l.387; S07 `isOpen_image_of_isKQC` l.281.

*Estimate.*  150–280 lines. -/
theorem s27u_proj_mdifferentiable [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ f) τ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p₀ f F) := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨-, -, -, hwK, hwd⟩ := s27u_fSym_upperHalf hk0 hk1 (s27u_liftCoeff_isBeltramiCoeff hp₀ hf)
  intro τ₁
  obtain ⟨σ, rfl⟩ : ∃ σ, F σ = τ₁ := ⟨F.symm τ₁, F.apply_symm_apply τ₁⟩
  have hz₀ : (σ : ℂ) ∈ upperHalf := σ.coe_im_pos
  obtain ⟨U, hUo, hz₀U, hUH, -, hgK, hμg⟩ := s27u_liftCoeff_local hp₀ hf hz₀
  set y₀ := f (utm_pext p₀ (σ : ℂ))
  set g : ℂ → ℂ := fun w => chartAt ℂ y₀ (f (utm_pext p₀ w))
  set W := s27u_fSym (s27u_liftCoeff p₀ f)
  have hWU := ac_t_isKQC_restrict hwK hUo hUH
  -- `g` and `w = f^μ` have the same dilatation a.e. on `U`, so `g ∘ w⁻¹` is conformal on `w(U)`
  have hae : ∀ᵐ z ∂(volume.restrict U), complexDilatation g z = complexDilatation W z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUH hwd, ae_restrict_mem hUo.measurableSet]
      with z h1 hz
    rw [h1, hμg z hz]
  have hconf := s27u_b_conformal_of_dilatation_eq hWU hgK hae
  have hVo : IsOpen (W '' U) := isOpen_image_of_isKQC hWU
  have hτ₁ : ((F σ : UpperHalfPlane) : ℂ) ∈ W '' U := ⟨(σ : ℂ), hz₀U, (hF σ).symm⟩
  -- the chart identity `φ_{y₀} ∘ p ∘ ofComplex = g ∘ w⁻¹` on `w(U)`
  have hkey : ∀ u ∈ W '' U, chartAt ℂ y₀ (s27u_proj p₀ f F (UpperHalfPlane.ofComplex u)) =
      (g ∘ Function.invFunOn W U) u := by
    rintro _ ⟨z, hz, rfl⟩
    have hzH : 0 < z.im := hUH hz
    have e0 : ((F ⟨z, hzH⟩ : UpperHalfPlane) : ℂ) = W z := hF ⟨z, hzH⟩
    rw [Function.comp_apply, hWU.2.2.1.2.1.leftInvOn_invFunOn hz, ← e0, UpperHalfPlane.ofComplex_apply]
    show chartAt ℂ y₀ (f (p₀ (F.symm (F ⟨z, hzH⟩)))) = chartAt ℂ y₀ (f (utm_pext p₀ z))
    rw [F.symm_apply_apply, utm_a_pext_eq p₀ hzH, UpperHalfPlane.ofComplex_apply_of_im_pos hzH]
  have hd : DifferentiableAt ℂ ((fun τ => chartAt ℂ y₀ (s27u_proj p₀ f F τ)) ∘ UpperHalfPlane.ofComplex)
      ((F σ : UpperHalfPlane) : ℂ) :=
    (hconf.1.differentiableAt (hVo.mem_nhds hτ₁)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hVo.mem_nhds hτ₁) fun u hu => hkey u hu)
  have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => chartAt ℂ y₀ (s27u_proj p₀ f F τ)) (F σ) :=
    UpperHalfPlane.mdifferentiableAt_iff.2 hd
  -- `p = φ_{y₀}⁻¹ ∘ (φ_{y₀} ∘ p)` near `F σ`
  have hproj : s27u_proj p₀ f F (F σ) = y₀ := by
    show f (p₀ (F.symm (F σ))) = f (utm_pext p₀ (σ : ℂ))
    rw [F.symm_apply_apply, s27u_pext_coe]
  have hsrc : s27u_proj p₀ f F (F σ) ∈ (chartAt ℂ y₀).source := by
    rw [hproj]
    exact mem_chart_source ℂ y₀
  have hcont : Continuous (s27u_proj p₀ f F) := f.continuous.comp (hp₀.1.continuous.comp F.symm.continuous)
  have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y₀).symm (chartAt ℂ y₀ (s27u_proj p₀ f F (F σ))) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ y₀) ((chartAt ℂ y₀).map_source hsrc)
  have hev : s27u_proj p₀ f F =ᶠ[𝓝 (F σ)]
      (chartAt ℂ y₀).symm ∘ fun τ => chartAt ℂ y₀ (s27u_proj p₀ f F τ) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds ((chartAt ℂ y₀).open_source.mem_nhds hsrc)] with τ hτ
    exact ((chartAt ℂ y₀).left_inv hτ).symm
  exact (hm2.comp (F σ) hm1).congr_of_eventuallyEq hev

/-- **`(ℍ, f ∘ p₀ ∘ F⁻¹)` uniformizes `S`, with covering group `F Γ₀ F⁻¹`** (proved from U2, U3, U6, U7).  The
covering property and surjectivity are formal: `f` and `F` are homeomorphisms.  The fibres: `p₀(F⁻¹ τ₁) = p₀(F⁻¹ τ₂)`
iff `γ F⁻¹ τ₁ = F⁻¹ τ₂` for some `γ ∈ Γ₀`, iff `γ' τ₁ = τ₂` for `γ' = F γ F⁻¹`, which is Möbius by U6. -/
theorem s27u_isUniformization [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ f) τ) :
    IsUniformization (s27u_conjGroup Γ₀ F) (s27u_proj p₀ f F) := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hconj : ∀ γ ∈ Γ₀, ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F (γ • τ) = γ' • F τ :=
    fun _ hγ => s27u_conj_mobius hk0 hk1 (s27u_liftCoeff_isBeltramiCoeff hp₀ hf)
      (s27u_liftCoeff_isGammaCompatible hp₀ f) hF hγ
  refine ⟨(hp₀.1.comp_homeomorph F.symm).homeomorph_comp f, s27u_proj_mdifferentiable hp₀ hf hF,
    fun y => ?_, fun τ₁ τ₂ => ?_⟩
  · obtain ⟨τ, hτ⟩ := hp₀.2.2.1 (f.symm y)
    refine ⟨F τ, ?_⟩
    show f (p₀ (F.symm (F τ))) = y
    rw [F.symm_apply_apply, hτ, f.apply_symm_apply]
  · show f (p₀ (F.symm τ₁)) = f (p₀ (F.symm τ₂)) ↔ _
    rw [f.injective.eq_iff, hp₀.2.2.2]
    constructor
    · rintro ⟨γ, hγ, h⟩
      obtain ⟨γ', hγ'⟩ := hconj γ hγ
      refine ⟨γ', ⟨γ, hγ, hγ'⟩, ?_⟩
      have h1 := hγ' (F.symm τ₁)
      rw [h, F.apply_symm_apply, F.apply_symm_apply] at h1
      exact h1.symm
    · rintro ⟨γ', ⟨γ, hγ, hγ'⟩, h⟩
      refine ⟨γ, hγ, ?_⟩
      have h1 := hγ' (F.symm τ₁)
      rw [F.apply_symm_apply, h] at h1
      rw [← h1, F.symm_apply_apply]

/-- **`F = w|ℍ` is a normalized lift of `f` for the projections `p₀` and `f ∘ p₀ ∘ F⁻¹`** (proved; formal).  Here `w`
is a q.c. homeomorphism of `ℂ` onto `ℂ` mapping `ℍ` onto `ℍ` and fixing `0` and `1`.  The boundary map is
`G = OnePoint.map w`, the homeomorphism of `ℂ̄` extending `w` (`t1_homeomorph`, `Homeomorph.onePointCongr`), which fixes
`0`, `1` and `∞`. -/
theorem s27u_isNormalizedLift {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {p₀ : UpperHalfPlane → S₀}
    (f : S₀ ≃ₜ S) {w : ℂ → ℂ} {K : ℝ} (hwK : IsKQC w univ K) (hws : w '' univ = univ)
    (hwU : w '' upperHalf = upperHalf) (hw0 : w 0 = 0) (hw1 : w 1 = 1) {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : ∀ τ, (F τ : ℂ) = w τ) : IsNormalizedLift p₀ (s27u_proj p₀ f F) f F (OnePoint.map w) := by
  have _ : ChartedSpace ℂ S₀ := inferInstance
  obtain ⟨e, he⟩ := t1_homeomorph hwK hws
  have hE : ⇑e.onePointCongr = OnePoint.map w := by
    funext q
    rw [Homeomorph.onePointCongr_apply, he]
  have hU' : OnePoint.map w '' toExt upperHalf = toExt upperHalf := by
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨w z, ?_, rfl⟩
      rw [← hwU]
      exact mem_image_of_mem w hz
    · rintro ⟨z, hz, rfl⟩
      rw [← hwU] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact ⟨(v : ExtPlane), ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨fun τ => ?_, ⟨fun z hz => ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩
  · show f (p₀ (F.symm (F τ))) = f (p₀ τ)
    rw [F.symm_apply_apply]
  · have hz' : 0 < z.im := hz
    have h1 : liftToC F z = w z := by
      rw [h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
      exact hF ⟨z, hz'⟩
    show ((w z : ℂ) : ExtPlane) = ((liftToC F z : ℂ) : ExtPlane)
    rw [h1]
  · rw [← hE]
    exact e.onePointCongr.continuous.continuousOn
  · rw [← hE]
    exact e.onePointCongr.injective.injOn
  · rw [← hE, Homeomorph.image_closure, hE, hU']
  · show ((w 0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
    rw [hw0]
  · show ((w 1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)
    rw [hw1]

/-- **Uniformization transport (UT), explicit form.**  Let `f : S₀ → S` be a q.c. homeomorphism of Riemann surfaces and
`p₀ : ℍ → S₀` a uniformization with group `Γ₀`.  Set `μ = s27u_liftCoeff p₀ f` and `w = f^μ = s27u_fSym μ`.  Then
there is a homeomorphism `F` of `ℍ` such that:
- `F = w|ℍ`;
- `p = f ∘ p₀ ∘ F⁻¹` uniformizes `S` with group `F Γ₀ F⁻¹`;
- `F` is a normalized lift of `f` for `p₀` and `p`, with boundary map `G = OnePoint.map w`, so `G = w` on `ℝ`;
- `w` is real on `ℝ`, and the complex dilatation of `F` is `μ` a.e. on `ℍ`.

Proved from U1–U7 (see the section header). -/
theorem s27u_uniformization_transport [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
      (∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ f) τ) ∧
      IsUniformization (s27u_conjGroup Γ₀ F) (s27u_proj p₀ f F) ∧
      IsNormalizedLift p₀ (s27u_proj p₀ f F) f F (OnePoint.map (s27u_fSym (s27u_liftCoeff p₀ f))) ∧
      (∀ x : ℝ, (s27u_fSym (s27u_liftCoeff p₀ f) x).im = 0) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (liftToC F) z = s27u_liftCoeff p₀ f z := by
  obtain ⟨K, hK⟩ := hf
  have hK1 : (1 : ℝ) ≤ K := hK.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hμ := s27u_liftCoeff_isBeltramiCoeff hp₀ hK
  obtain ⟨-, hN, hwK, -⟩ := s27u_sym_spec hk0 hk1 hμ
  obtain ⟨hwU, hreal, -, -, hwd⟩ := s27u_fSym_upperHalf hk0 hk1 hμ
  obtain ⟨F, hF⟩ := s27u_homeo_upper hwK hN.2.1 hwU
  refine ⟨F, hF, s27u_isUniformization hp₀ hK hF,
    s27u_isNormalizedLift f hwK hN.2.1 hwU hN.2.2.1 hN.2.2.2.1 hF, hreal, ?_⟩
  filter_upwards [hwd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
  rw [← h1]
  have hev : liftToC F =ᶠ[𝓝 z] s27u_fSym (s27u_liftCoeff p₀ f) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with v hv
    rw [h23l_liftToC_eq F hv, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < v.im from hv)]
    exact hF _
  simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]

/-- **Uniformization transport (UT) for marked surfaces.**  Every marked surface `m = (X, f)` of `S₀ = ℍ/Γ₀` has a
uniformization `p : ℍ → X` (group `Γ`) for which `f` has a normalized lift `F` with boundary map `G`.  Moreover `F` is
the normalized symmetric solution `f^μ|ℍ` of the lifted Beltrami coefficient `μ` of `f ∘ p₀`, and `G = f^μ` on `ℝ`.
(From `s27u_uniformization_transport`.) -/
theorem s27u_exists_uniformization [IsManifold 𝓘(ℂ) ω S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (m : MarkedRS S₀) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → m.X.carrier)
      (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
      IsUniformization Γ p ∧ IsNormalizedLift p₀ p m.marking F G ∧
        (∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ m.marking) τ) ∧
        ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((s27u_fSym (s27u_liftCoeff p₀ m.marking) x : ℂ) : ExtPlane) := by
  obtain ⟨F, hF, hU, hN, -, -⟩ := s27u_uniformization_transport hp₀ m.marking m.qc
  exact ⟨_, _, F, _, hU, hN, hF, fun _ => rfl⟩

/-- **[U10, stub; optional, for the E2 bridge] The lifted coefficient is the dilatation of every lift.**  For ANY
uniformization `p` of `S` and ANY lift `F` of `f` (`p ∘ F = f ∘ p₀`), `μ_{liftToC F}(z) = s27u_liftCoeff p₀ f z` at
every `z ∈ ℍ`.  The UT glue does not use it.

*Why true.*  On `ℍ`, `g_z = ψ ∘ liftToC F` exactly, where `ψ = φ_y ∘ p ∘ ofComplex` and `y = f(p₀ z) = p(F z)`.  `ψ` is
conformal near `F z` (`h23l_chart_proj`, S23 l.810, and `thm7_3_one_qc_conformal`) with a holomorphic local inverse
(`IsConformalOnto.symm`, `Lemmas/Conformal` l.122).  So `s23_dilatation_comp_left` (S23 l.154) applies.

*Estimate.*  60–110 lines. -/
theorem s27u_liftCoeff_eq_dilatation {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Γ₀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} {p : UpperHalfPlane → S}
    (hp₀ : IsUniformization Γ₀ p₀) (hp : IsUniformization Γ p) {f : S₀ → S} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p₀ p f F) {z : ℂ} (hz : z ∈ upperHalf) :
    complexDilatation (liftToC F) z = s27u_liftCoeff p₀ f z := by
  have _ := hp₀
  have hz' : 0 < z.im := hz
  -- `ψ = φ_y ∘ p ∘ ofComplex` (`y = p (F z)`) is conformal near `F z`, with a holomorphic local inverse
  obtain ⟨U, hUo, hFU, -, -, hψ⟩ :=
    h23l_chart_proj (τ := (F ⟨z, hz'⟩)) hp.1 hp.2.1 _ (mem_chart_source ℂ _)
  have hψc := thm7_3_one_qc_conformal hψ
  have hψV := isOpen_image_of_isKQC hψ
  have hψi := hψc.symm hUo
  have hgzU : liftToC F z ∈ U := by
    rw [h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact hFU
  have hcont : ContinuousAt (liftToC F) z :=
    (h23l_liftToC_continuousOn F.continuous z hz).continuousAt (isOpen_upperHalf.mem_nhds hz)
  have h1 := s23_dilatation_comp_left hcont (hψc.1.differentiableAt (hUo.mem_nhds hgzU))
    (hψi.1.differentiableAt (hψV.mem_nhds (mem_image_of_mem _ hgzU)))
    (Filter.eventually_of_mem (hUo.mem_nhds hgzU) fun u hu => hψc.2.1.leftInvOn_invFunOn hu)
  -- on `ℍ`, the chart expression of `f ∘ p₀` defining `μ(z)` is `ψ ∘ liftToC F` (`p ∘ F = f ∘ p₀`)
  have heq : EqOn ((fun u => chartAt ℂ (p (F ⟨z, hz'⟩)) (p (UpperHalfPlane.ofComplex u))) ∘ liftToC F)
      (fun w => chartAt ℂ (f (utm_pext p₀ z)) (f (utm_pext p₀ w))) upperHalf := by
    intro w hw
    have hw' : 0 < w.im := hw
    simp only [Function.comp_apply]
    rw [h23l_liftToC_eq F hw, UpperHalfPlane.ofComplex_apply, hF ⟨z, hz'⟩,
      hF (UpperHalfPlane.ofComplex w), utm_a_pext_eq p₀ hw', utm_a_pext_eq p₀ hz',
      UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  rw [s27u_liftCoeff_of_mem p₀ f hz, ← h1]
  exact abR_t_complexDilatation_congr isOpen_upperHalf heq hz

/-- **[U11, stub; optional, for the E2 bridge] `f^μ` depends only on the a.e. class of `μ` on `ℍ`.**

*Why true.*  The symmetric extensions agree a.e. on `ℂ`: on `ℍ` directly, on `𝕃` through the measure-preserving
`z ↦ z̄` (as in S33 `bg_s_beltrami`), and `ℝ` is null.  So `f^μ` is a normalized solution for `s27u_symExt ν`, hence
it is `f^ν` (U4 uniqueness).  This exact statement is `s27u_probe_U11` in `U_truth_probe.lean` (20 lines on top of
the S33 copies of U4).

*Estimate.*  35–60 lines. -/
theorem s27u_fSym_congr_ae {μ ν : ℂ → ℂ} {k k' : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hk₀' : 0 ≤ k') (hk' : k' < 1) (hν : IsBeltramiCoeff ν upperHalf k')
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), μ z = ν z) : s27u_fSym μ = s27u_fSym ν := by
  obtain ⟨-, hNμ, -, -⟩ := s27u_sym_spec hk₀ hk hμ
  obtain ⟨-, -, -, huν⟩ := s27u_sym_spec hk₀' hk' hν
  -- the symmetric extensions agree a.e. on `ℍ` and (through `z ↦ z̄`) on `𝕃`; `ℝ` is null
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict lowerHalf) (volume.restrict upperHalf) := by
    have h' := gzE_conj_measurePreserving.restrict_preimage isOpen_upperHalf.measurableSet
    rwa [s27u_b_s_conj_preimage_upperHalf] at h'
  have hae : ∀ᵐ z, s27u_symExt μ z = s27u_symExt ν z := by
    refine k24_ae_of_halves ?_ ?_
    · filter_upwards [h, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
      have hz' : ¬ z.im < 0 := not_lt.2 (le_of_lt (show 0 < z.im from hz))
      rw [s27u_symExt, s27u_symExt, ite_eq_right hz', ite_eq_right hz']
      exact h1
    · filter_upwards [hmp.quasiMeasurePreserving.ae h, ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
      have hz' : z.im < 0 := hz
      rw [s27u_symExt, s27u_symExt, ite_eq_left hz', ite_eq_left hz', h1]
  -- so `f^μ` is a normalized solution for `s27u_symExt ν`, hence it is `f^ν` (U4 uniqueness)
  obtain ⟨hq, hs, h0, h1, hd⟩ := hNμ
  refine huν _ ⟨hq, hs, h0, h1, ?_⟩
  filter_upwards [hd, hae] with z ha hb
  exact ha.trans hb

/-- **The Fricke coordinates do not see the sign**: `frickeTriple (-γ) = frickeTriple γ` (a copy of scout E's probe
`h27e_frickeTriple_neg`, `s27t/scout_E/h27e_reductions.lean`). -/
theorem s27f_frickeTriple_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    frickeTriple (-γ) = frickeTriple γ := by
  have hs : -γ 0 0 + -γ 1 1 = -(γ 0 0 + γ 1 1) := by ring
  have hA : attractingFixedPoint (-γ) = attractingFixedPoint γ := by
    rw [attractingFixedPoint, attractingFixedPoint]
    simp only [s27t_neg_apply, neg_eq_zero, abs_neg]
    split_ifs with h1 h2
    · rfl
    · rw [show -γ 1 1 - -γ 0 0 = -(γ 1 1 - γ 0 0) by ring, neg_div_neg_eq]
    · rw [hs, Real.sign_neg, neg_sq,
        show -γ 0 0 - -γ 1 1 + -Real.sign (γ 0 0 + γ 1 1) * √((γ 0 0 + γ 1 1) ^ 2 - 4) =
          -(γ 0 0 - γ 1 1 + Real.sign (γ 0 0 + γ 1 1) * √((γ 0 0 + γ 1 1) ^ 2 - 4)) by ring,
        show 2 * -γ 1 0 = -(2 * γ 1 0) by ring, neg_div_neg_eq]
  have hR : repellingFixedPoint (-γ) = repellingFixedPoint γ := by
    rw [repellingFixedPoint, repellingFixedPoint]
    simp only [s27t_neg_apply, neg_eq_zero, abs_neg]
    split_ifs with h1 h2
    · rw [show -γ 1 1 - -γ 0 0 = -(γ 1 1 - γ 0 0) by ring, neg_div_neg_eq]
    · rfl
    · rw [hs, Real.sign_neg, neg_sq,
        show -γ 0 0 - -γ 1 1 - -Real.sign (γ 0 0 + γ 1 1) * √((γ 0 0 + γ 1 1) ^ 2 - 4) =
          -(γ 0 0 - γ 1 1 - Real.sign (γ 0 0 + γ 1 1) * √((γ 0 0 + γ 1 1) ^ 2 - 4)) by ring,
        show 2 * -γ 1 0 = -(2 * γ 1 0) by ring, neg_div_neg_eq]
  have hM : multiplier (-γ) = multiplier γ := by
    rw [multiplier, multiplier]
    simp only [s27t_neg_apply]
    rw [hs, abs_neg, neg_sq]
  rw [frickeTriple, frickeTriple, hA, hR, hM]

/-- The commutator `[a, b]` does not see the signs of `a` and `b` (`-1` is central). -/
theorem s27f_comm_pm {a a' b b' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (ha : a = a' ∨ a = -a')
    (hb : b = b' ∨ b = -b') : commutatorSL a b = commutatorSL a' b' := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [commutatorSL, inv_neg, neg_mul, mul_neg, neg_neg]

/-- `±1` has trace `±2`. -/
theorem s27f_tr_pm_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : γ = 1 ∨ γ = -1) : |γ 0 0 + γ 1 1| = 2 := by
  rcases h with rfl | rfl
  · norm_num
  · norm_num [Matrix.SpecialLinearGroup.coe_neg]

/-- **A translation has arbitrarily small displacement.**  If `M` is upper triangular with equal diagonal entries
(`M = ±(1 b; 0 1)`, the map `z ↦ z + M₀₁ M₁₁`), then at `τ = i t` the displacement is at most `|M₀₁|/t`
(`UpperHalfPlane.dist_le_dist_coe_div_sqrt`), which is `< ε` for `t` large. -/
theorem s27f_translation_small {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h10 : M 1 0 = 0)
    (had : M 0 0 = M 1 1) {ε : ℝ} (hε : 0 < ε) : ∃ τ : UpperHalfPlane, dist (M • τ) τ < ε := by
  have hdet := hnf_sl2_det M
  rw [h10, mul_zero, sub_zero, had] at hdet
  have hdC : (M 1 1 : ℂ) * M 1 1 = 1 := by exact_mod_cast hdet
  have hd0 : (M 1 1 : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hdC
  have habs : |M 0 1 * M 1 1| = |M 0 1| := by
    rw [abs_mul]
    rcases mul_self_eq_one_iff.1 hdet with h | h <;> simp [h]
  have ht0 : 0 < |M 0 1| / ε + 1 := add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg _) hε.le) one_pos
  set t : ℝ := |M 0 1| / ε + 1 with ht
  set τ : UpperHalfPlane := ⟨⟨0, t⟩, ht0⟩ with hτ
  have hcoe : ((M • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + ((M 0 1 * M 1 1 : ℝ) : ℂ) := by
    rw [h36t_coe_smul, h10, had, Complex.ofReal_zero, zero_mul, zero_add, div_eq_iff hd0]
    push_cast
    linear_combination (-(M 0 1 : ℂ)) * hdC
  have him : (M • τ).im = t := by
    show ((M • τ : UpperHalfPlane) : ℂ).im = t
    rw [hcoe, Complex.add_im, Complex.ofReal_im, add_zero]
  refine ⟨τ, lt_of_le_of_lt (UpperHalfPlane.dist_le_dist_coe_div_sqrt _ _) ?_⟩
  rw [him, show τ.im = t from rfl, Real.sqrt_mul_self ht0.le, dist_eq_norm, hcoe, add_sub_cancel_left,
    Complex.norm_real, Real.norm_eq_abs, habs, div_lt_iff₀ ht0]
  have e : ε * (|M 0 1| / ε) = |M 0 1| := by field_simp
  rw [ht, mul_add, e, mul_one]
  linarith

/-- **A parabolic element has arbitrarily small displacement.**  For `|tr δ| = 2`, conjugate a fixed point `[p : q]` of
`δ` in `ℝ̂` (`s27g_fixed_vec`) to `∞` by `A`, as in `s27g_common_fixed_false`: `M = A δ A⁻¹` has `M₁₀ = 0`
(`s27g_fix_conj`), trace `±2` (`s27g_trace_conj`) and determinant `1`, so `M₀₀ = M₁₁`.  Then `s27f_translation_small`
applies to `M`, and `dist (δ (A⁻¹ τ)) (A⁻¹ τ) = dist (M τ) τ` (`dist_smul`). -/
theorem s27f_parabolic_small {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (htr : |δ 0 0 + δ 1 1| = 2) {ε : ℝ}
    (hε : 0 < ε) : ∃ w : UpperHalfPlane, dist (δ • w) w < ε := by
  obtain ⟨p, q, hpq, hfix⟩ := s27g_fixed_vec htr.ge
  have hn : 0 < p ^ 2 + q ^ 2 := by
    rcases hpq with h | h
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![p / (p ^ 2 + q ^ 2), q / (p ^ 2 + q ^ 2); -q, p], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩
  have hA1 : A 0 0 * p + A 0 1 * q = 1 := by
    show p / (p ^ 2 + q ^ 2) * p + q / (p ^ 2 + q ^ 2) * q = 1
    field_simp
  have hA2 : A 1 0 * p + A 1 1 * q = 0 := by
    show -q * p + p * q = 0
    ring
  have hcov := s27g_fix_conj A δ p q
  rw [hA1, hA2, hfix] at hcov
  have hc0 : (A * δ * A⁻¹) 1 0 = 0 := by linear_combination hcov
  have htr' := s27g_trace_conj A δ
  have hdet' := hnf_sl2_det (A * δ * A⁻¹)
  rw [hc0, mul_zero, sub_zero] at hdet'
  have h4 : ((A * δ * A⁻¹) 0 0 + (A * δ * A⁻¹) 1 1) ^ 2 = 4 := by
    rw [htr', ← sq_abs, htr]
    norm_num
  have hsq : ((A * δ * A⁻¹) 0 0 - (A * δ * A⁻¹) 1 1) ^ 2 = 0 := by linear_combination h4 - 4 * hdet'
  have had : (A * δ * A⁻¹) 0 0 = (A * δ * A⁻¹) 1 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  obtain ⟨τ, hτ⟩ := s27f_translation_small hc0 had hε
  refine ⟨A⁻¹ • τ, ?_⟩
  have e : dist (δ • A⁻¹ • τ) (A⁻¹ • τ) = dist ((A * δ * A⁻¹) • τ) τ := by
    rw [← dist_smul A, smul_inv_smul, mul_smul, mul_smul]
  rw [e]
  exact hτ

/-- **Positive displacement** (the local-injectivity step of prover X2's `utm_x2_isFuchsian`, stage E2,
`s27t/stageE2/work/e2p_X2.lean`).  For the covering group `Γ` of a compact surface and `δ ∈ Γ`, `δ ≠ ±1`, some `ε > 0`
bounds `dist (δ • w) w` from below.  Otherwise pick `wₙ` with `dist (δ wₙ) wₙ < 1/(n+1)`, move `wₙ` into the compact
`K` of `utm_exists_compact_translate` by `hₙ ∈ Γ`, and pass to a subsequence with `hₙ wₙ → a`.  The conjugates
`hₙ δ hₙ⁻¹ ∈ Γ` move `hₙ wₙ` by `dist (δ wₙ) wₙ → 0`, so for some `n` both points lie in a sheet `E.source` around `a`
on which `p` is injective (`IsCoveringMap.isLocalHomeomorph`).  They have the same image under `p`, hence
`hₙ δ hₙ⁻¹` fixes `hₙ wₙ` and is `±1` (`s27g_actsFreely`), and so is `δ`. -/
theorem s27f_disp_pos {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ) (h1 : δ ≠ 1) (h2 : δ ≠ -1) :
    ∃ ε > 0, ∀ w : UpperHalfPlane, ε ≤ dist (δ • w) w := by
  by_contra hcon
  push Not at hcon
  choose w hw using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp
  choose h hhΓ hhK using fun n => hKz (w n)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hhK
  have hd : ∀ k : ℕ, dist (h (φ k) • w (φ k)) ((h (φ k) * δ * (h (φ k))⁻¹) • (h (φ k) • w (φ k))) ≤
      1 / ((k : ℝ) + 1) := by
    intro k
    rw [dist_comm, mul_smul, mul_smul, inv_smul_smul, dist_smul]
    refine (hw (φ k)).le.trans ?_
    have hk : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hlim2 : Tendsto (fun k => (h (φ k) * δ * (h (φ k))⁻¹) • (h (φ k) • w (φ k))) atTop (𝓝 a) :=
    hlim.congr_dist (squeeze_zero (fun k => dist_nonneg) hd tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨E, haE, hpE⟩ := hp.1.isLocalHomeomorph a
  have hEn : E.source ∈ 𝓝 a := E.open_source.mem_nhds haE
  obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually_mem hEn).and (hlim2.eventually_mem hEn)).exists
  have hmem : h (φ k) * δ * (h (φ k))⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem (hhΓ _) hδ) (Γ.inv_mem (hhΓ _))
  have hpeq : p ((h (φ k) * δ * (h (φ k))⁻¹) • (h (φ k) • w (φ k))) = p (h (φ k) • w (φ k)) :=
    ((hp.2.2.2 _ _).2 ⟨_, hmem, rfl⟩).symm
  rw [hpE] at hpeq
  have hfix := E.injOn hk2 hk1 hpeq
  rcases s27g_actsFreely hp _ hmem _ hfix with e | e
  · apply h1
    calc δ = (h (φ k))⁻¹ * (h (φ k) * δ * (h (φ k))⁻¹) * h (φ k) := by group
      _ = 1 := by rw [e]; group
  · apply h2
    calc δ = (h (φ k))⁻¹ * (h (φ k) * δ * (h (φ k))⁻¹) * h (φ k) := by group
      _ = -1 := by rw [e, mul_neg_one, neg_mul, inv_mul_cancel]

/-- **The covering group of a compact surface is purely hyperbolic**: every `δ ∈ Γ`, `δ ≠ ±1`, has `|tr δ| > 2`.
An elliptic `δ` fixes a point of `ℍ` (`s27g_elliptic_fixed`), against freeness (`s27g_actsFreely`); a parabolic one
has arbitrarily small displacement (`s27f_parabolic_small`), against `s27f_disp_pos`. -/
theorem s27f_hyp {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ) (h1 : δ ≠ 1) (h2 : δ ≠ -1) :
    2 < |δ 0 0 + δ 1 1| := by
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨τ, hτ⟩ := s27g_elliptic_fixed hlt
    rcases s27g_actsFreely hp δ hδ τ hτ with e | e
    exacts [h1 e, h2 e]
  · obtain ⟨ε, hε, hdisp⟩ := s27f_disp_pos hp hδ h1 h2
    obtain ⟨w, hw⟩ := s27f_parabolic_small heq hε
    exact absurd (hdisp w) (not_le.2 hw)

/-- A real Möbius map fixes `0` iff `b = 0`. -/
theorem s27f_mob_zero {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} :
    mobiusSL (slRealToComplex γ) ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ↔ γ 0 1 = 0 := by
  have e0 : ((0 : ℂ) : ExtPlane) = (((0 : ℝ) : ℂ) : ExtPlane) := by rw [Complex.ofReal_zero]
  rw [e0]
  constructor
  · intro h
    obtain ⟨-, e⟩ := s27g_mob_real_eq h
    linarith
  · intro h
    have hdet := hnf_sl2_det γ
    rw [h, zero_mul, sub_zero] at hdet
    refine s27g_mob_real_of ?_ ?_
    · rw [mul_zero, zero_add]
      exact right_ne_zero_of_mul_eq_one hdet
    · rw [h]
      ring

/-- **Fixed points correspond.**  If `δ` represents `F ∘ γ ∘ F⁻¹` and the extension `Gb` fixes `ξ ∈ closure ℍ`, then
`γ` fixes `ξ` iff `δ` does: `Gb ∘ γ = δ ∘ Gb` on `closure ℍ` (`s27g_bdry_rel`), and `Gb` is injective there. -/
theorem s27f_fix_iff {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR : RepresentsConj F γ δ) {ξ : ExtPlane} (hξ : ξ ∈ closure (toExt upperHalf)) (hGξ : Gb ξ = ξ) :
    mobiusSL (slRealToComplex γ) ξ = ξ ↔ mobiusSL (slRealToComplex δ) ξ = ξ := by
  have e : Gb (mobiusSL (slRealToComplex γ) ξ) = mobiusSL (slRealToComplex δ) (Gb ξ) := s27g_bdry_rel hG hR hξ
  rw [hGξ] at e
  constructor
  · intro h
    rw [h, hGξ] at e
    exact e.symm
  · intro h
    rw [h] at e
    have hmaps : mobiusSL (slRealToComplex γ) ξ ∈ closure (toExt upperHalf) :=
      Set.MapsTo.closure (fun q hq => k24_real_mapsTo_upper γ hq) (k24_mobiusSLHomeo _).continuous hξ
    exact hG.2.2.1 hmaps hξ (e.trans hGξ.symm)

/-- `γ` fixes `∞` iff `δ` does, when `δ` represents `F ∘ γ ∘ F⁻¹` and `Gb ∞ = ∞`. -/
theorem s27f_fix_infty {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) (hGinf : Gb extInf = extInf)
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR : RepresentsConj F γ δ) : γ 1 0 = 0 ↔ δ 1 0 = 0 := by
  exact s27g_mob_infty.symm.trans ((s27f_fix_iff hG hR s27l_mem_closure_01inf.2.2 hGinf).trans s27g_mob_infty)

/-- `γ` fixes `0` iff `δ` does, when `δ` represents `F ∘ γ ∘ F⁻¹` and `Gb 0 = 0`. -/
theorem s27f_fix_zero {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb)
    (hG0 : Gb ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR : RepresentsConj F γ δ) : γ 0 1 = 0 ↔ δ 0 1 = 0 := by
  exact s27f_mob_zero.symm.trans ((s27f_fix_iff hG hR s27l_mem_closure_01inf.1 hG0).trans s27f_mob_zero)

/-- Two real points of `ℂ̄` with the same `Re ∘ extToC` are equal. -/
theorem s27f_coe_eq {r s : ℝ} (h : (extToC ((r : ℂ) : ExtPlane)).re = (extToC ((s : ℂ) : ExtPlane)).re) :
    ((r : ℂ) : ExtPlane) = ((s : ℂ) : ExtPlane) := by
  have e : r = s := by simpa [extToC] using h
  rw [e]

/-- **No swap of the fixed points.**  Let `δᵢ` represent `Fᵢ ∘ γ ∘ Fᵢ⁻¹`, for boundary maps `Gbᵢ` fixing `0`, `1` and
`∞`, with `δ₁`, `δ₂` hyperbolic and fixing `∞`, `∞` attracting for `δ₁` and repelling for `δ₂`.  Then the Fricke
triples differ.  If they agreed, the junk value `extToC ∞ = 0` would force both finite fixed points to be `0`.  Then
`δ₁`, `δ₂` and hence `γ` would be diagonal (`s27f_fix_infty`, `s27f_fix_zero`), with `γ ≠ ±1` since `δ₁` is
hyperbolic.  If `γ₀₀² > 1`, `s27g_diag` gives `δ₂₀₀² > 1`; if `γ₀₀² < 1`, it gives `(δ₁⁻¹)₀₀² > 1` for `γ⁻¹`.  Both
contradict the assumed types. -/
theorem s27f_no_swap {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb₁ Gb₂ : ExtPlane → ExtPlane}
    (hN₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf Gb₁ ∧ Gb₁ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      Gb₁ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ Gb₁ extInf = extInf)
    (hN₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf Gb₂ ∧ Gb₂ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      Gb₂ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ Gb₂ extInf = extInf)
    {γ δ₁ δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR₁ : RepresentsConj F₁ γ δ₁)
    (hR₂ : RepresentsConj F₂ γ δ₂) (hh₁ : 2 < |δ₁ 0 0 + δ₁ 1 1|) (hh₂ : 2 < |δ₂ 0 0 + δ₂ 1 1|)
    (hc₁ : δ₁ 1 0 = 0) (hc₂ : δ₂ 1 0 = 0) (ha₁ : 1 < |δ₁ 0 0|) (ha₂ : ¬ 1 < |δ₂ 0 0|)
    (hA : (extToC (attractingFixedPoint δ₁)).re = (extToC (attractingFixedPoint δ₂)).re)
    (hR : (extToC (repellingFixedPoint δ₁)).re = (extToC (repellingFixedPoint δ₂)).re) : False := by
  obtain ⟨hG₁, h0₁, h1₁, hinf₁⟩ := hN₁
  obtain ⟨hG₂, h0₂, h1₂, hinf₂⟩ := hN₂
  have hdet₁ : δ₁ 0 0 * δ₁ 1 1 = 1 := by
    have h := hnf_sl2_det δ₁
    rw [hc₁, mul_zero, sub_zero] at h
    exact h
  have hdet₂ : δ₂ 0 0 * δ₂ 1 1 = 1 := by
    have h := hnf_sl2_det δ₂
    rw [hc₂, mul_zero, sub_zero] at h
    exact h
  obtain ⟨hda₁, -, -⟩ := hnf_core_eq hdet₁ hh₁
  obtain ⟨hda₂, -, -⟩ := hnf_core_eq hdet₂ hh₂
  obtain ⟨k1, -⟩ := hnf_fixed_of_eq_zero hc₁
  obtain ⟨-, l2⟩ := hnf_fixed_of_eq_zero hc₂
  rw [(k1 ha₁).1, (l2 ha₂).1] at hA
  rw [(k1 ha₁).2, (l2 ha₂).2] at hR
  have e₂ : δ₂ 0 1 / (δ₂ 1 1 - δ₂ 0 0) = 0 := hA.symm
  have e₁ : δ₁ 0 1 / (δ₁ 1 1 - δ₁ 0 0) = 0 := hR
  have hb₁ : δ₁ 0 1 = 0 := (div_eq_zero_iff.1 e₁).resolve_right hda₁
  -- `γ` fixes `∞` and `0`: it is diagonal
  have hγc : γ 1 0 = 0 := (s27f_fix_infty hG₁ hinf₁ hR₁).2 hc₁
  have hγb : γ 0 1 = 0 := (s27f_fix_zero hG₁ h0₁ hR₁).2 hb₁
  have hdetγ : γ 0 0 * γ 1 1 = 1 := by
    have h := hnf_sl2_det γ
    rw [hγc, mul_zero, sub_zero] at h
    exact h
  obtain ⟨g₁, hg₁, hmono₁, -, hg1₁⟩ := s27g_bdry_real hG₁ h0₁ h1₁ hinf₁
  obtain ⟨g₂, hg₂, hmono₂, -, hg1₂⟩ := s27g_bdry_real hG₂ h0₂ h1₂ hinf₂
  rcases lt_trichotomy (γ 0 0 ^ 2) 1 with hlt | heq | hgt
  · -- `γ⁻¹` is diagonal with `(γ⁻¹)₀₀² = γ₁₁² > 1`, so `(δ₁⁻¹)₀₀² = δ₁₁₁² > 1`
    obtain ⟨i00, i01, i10, -⟩ := s27t_inv_apply γ
    have hγ11 : 1 < γ 1 1 ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hprod : γ 0 0 ^ 2 * γ 1 1 ^ 2 = 1 := by rw [← mul_pow, hdetγ, one_pow]
      nlinarith [mul_le_mul_of_nonneg_left hcon (sq_nonneg (γ 0 0))]
    have h := (s27g_diag hG₁ h0₁ hinf₁ hg₁ hmono₁ hg1₁ ⟨by rw [i01, hγb, neg_zero], by rw [i10, hγc, neg_zero],
      by rw [i00]; exact hγ11⟩ (s27g_rep_inv hR₁)).2.2
    obtain ⟨j00, -, -, -⟩ := s27t_inv_apply δ₁
    rw [j00] at h
    obtain ⟨-, hlt1, -⟩ := s27t_diag_facts ⟨hb₁, hc₁, (one_lt_sq_iff_one_lt_abs _).2 ha₁⟩
    linarith
  · -- `γ = ±1` would make `δ₁ = ±1`
    have had : γ 0 0 = γ 1 1 := by linear_combination γ 1 1 * heq - γ 0 0 * hdetγ
    have htriv := s27g_smul_self_of_scalar hγb hγc had
    have hδ₁ : ∀ τ : UpperHalfPlane, δ₁ • τ = τ := fun τ => by rw [hR₁, htriv, F₁.apply_symm_apply]
    have := s27f_tr_pm_one (s27g_eq_one_of_smul_eq hδ₁)
    linarith
  · -- `γ₀₀² > 1`, so `δ₂₀₀² > 1`
    have h := (s27g_diag hG₂ h0₂ hinf₂ hg₂ hmono₂ hg1₂ ⟨hγb, hγc, hgt⟩ hR₂).2.2
    exact ha₂ ((one_lt_sq_iff_one_lt_abs _).1 h)

/-- **Equal Fricke triples give equal representatives up to sign** (the step `(ii)` of (27.6)–(27.7)).  Let `δᵢ ∈ Γᵢ`
represent `Fᵢ ∘ γ ∘ Fᵢ⁻¹`, where `Γᵢ` uniformizes a compact surface and `Gbᵢ` extends `Fᵢ` fixing `0`, `1`, `∞`.
- If one `δᵢ` is `±1`, then `γ` acts trivially and so is the other (`s27g_rep_unique`).
- Otherwise both are hyperbolic (`s27f_hyp`), and `δ₁` fixes `∞` iff `δ₂` does (`s27f_fix_infty`, twice).
- The fixed points are then of the same kind, except in the swapped case excluded by `s27f_no_swap`.  So equal triples
  give equal fixed points and multipliers, and `hyperbolic_normal_form` concludes. -/
theorem s27f_pm_of_triple {S₁ S₂ : Type*} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [CompactSpace S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [CompactSpace S₂]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    {Gb₁ Gb₂ : ExtPlane → ExtPlane}
    (hN₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf Gb₁ ∧ Gb₁ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      Gb₁ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ Gb₁ extInf = extInf)
    (hN₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf Gb₂ ∧ Gb₂ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      Gb₂ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ Gb₂ extInf = extInf)
    {γ δ₁ δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ₁ : δ₁ ∈ Γ₁) (hδ₂ : δ₂ ∈ Γ₂)
    (hR₁ : RepresentsConj F₁ γ δ₁) (hR₂ : RepresentsConj F₂ γ δ₂) (ht : frickeTriple δ₁ = frickeTriple δ₂) :
    δ₁ = δ₂ ∨ δ₁ = -δ₂ := by
  -- a trivial representative forces the other one to be trivial
  have htriv : ∀ {F F' : UpperHalfPlane ≃ₜ UpperHalfPlane} {δ δ' : Matrix.SpecialLinearGroup (Fin 2) ℝ},
      RepresentsConj F γ δ → RepresentsConj F' γ δ' → (δ = 1 ∨ δ = -1) → δ' = δ ∨ δ' = -δ := by
    intro F F' δ δ' hR hR' hδ
    have hδτ : ∀ τ : UpperHalfPlane, δ • τ = τ := fun τ => by
      rcases hδ with rfl | rfl
      · exact one_smul _ _
      · exact s27g_neg_one_smul τ
    have hγ : ∀ σ : UpperHalfPlane, γ • σ = σ := fun σ => by
      have e := hR (F σ)
      rw [hδτ, F.symm_apply_apply] at e
      exact F.injective e.symm
    exact s27g_rep_unique (fun τ => by rw [hδτ, hγ, F'.apply_symm_apply]) hR'
  by_cases h₁ : δ₁ = 1 ∨ δ₁ = -1
  · rcases htriv hR₁ hR₂ h₁ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  by_cases h₂ : δ₂ = 1 ∨ δ₂ = -1
  · exact htriv hR₂ hR₁ h₂
  push Not at h₁ h₂
  have hh₁ := s27f_hyp hp₁ hδ₁ h₁.1 h₁.2
  have hh₂ := s27f_hyp hp₂ hδ₂ h₂.1 h₂.2
  have hc : δ₁ 1 0 = 0 ↔ δ₂ 1 0 = 0 :=
    (s27f_fix_infty hN₁.1 hN₁.2.2.2 hR₁).symm.trans (s27f_fix_infty hN₂.1 hN₂.2.2.2 hR₂)
  have huniq := (hyperbolic_normal_form hh₂).2.2.2.2.2 δ₁ hh₁
  simp only [frickeTriple, Prod.mk.injEq] at ht
  obtain ⟨hA, hR, hM⟩ := ht
  by_cases hc₁ : δ₁ 1 0 = 0
  · have hc₂ := hc.1 hc₁
    obtain ⟨k1, k2⟩ := hnf_fixed_of_eq_zero hc₁
    obtain ⟨l1, l2⟩ := hnf_fixed_of_eq_zero hc₂
    by_cases ha₁ : 1 < |δ₁ 0 0| <;> by_cases ha₂ : 1 < |δ₂ 0 0|
    · rw [(k1 ha₁).2, (l1 ha₂).2] at hR
      refine huniq (by rw [(k1 ha₁).1, (l1 ha₂).1]) ?_ hM
      rw [(k1 ha₁).2, (l1 ha₂).2]
      exact s27f_coe_eq hR
    · exact (s27f_no_swap hN₁ hN₂ hR₁ hR₂ hh₁ hh₂ hc₁ hc₂ ha₁ ha₂ hA hR).elim
    · exact (s27f_no_swap hN₂ hN₁ hR₂ hR₁ hh₂ hh₁ hc₂ hc₁ ha₂ ha₁ hA.symm hR.symm).elim
    · rw [(k2 ha₁).1, (l2 ha₂).1] at hA
      refine huniq ?_ (by rw [(k2 ha₁).2, (l2 ha₂).2]) hM
      rw [(k2 ha₁).1, (l2 ha₂).1]
      exact s27f_coe_eq hA
  · have hc₂ : δ₂ 1 0 ≠ 0 := fun h => hc₁ (hc.2 h)
    obtain ⟨σ₁, hσ₁⟩ := hnf_attr_exists hc₁
    obtain ⟨τ₁, hτ₁⟩ := hnf_rep_exists hc₁
    obtain ⟨σ₂, hσ₂⟩ := hnf_attr_exists hc₂
    obtain ⟨τ₂, hτ₂⟩ := hnf_rep_exists hc₂
    rw [hσ₁, hσ₂] at hA
    rw [hτ₁, hτ₂] at hR
    refine huniq ?_ ?_ hM
    · rw [hσ₁, hσ₂]
      exact s27f_coe_eq hA
    · rw [hτ₁, hτ₂]
      exact s27f_coe_eq hR

/-- **Equal boundary values give equal Fricke triples** (the direction `⇒` of (27.6)–(27.7)): if the extensions agree
on `ℝ` (and fix `∞`), the representatives of `Fᵢ ∘ γ ∘ Fᵢ⁻¹` act identically on `ℍ` (`h36t_deck_agree`), so they are
equal up to sign (`s27g_rep_unique`), and `frickeTriple` does not see the sign. -/
theorem s27f_triple_of_bdry {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb₁ Gb₂ : ExtPlane → ExtPlane}
    (hG₁ : IsHomeoExtension (liftToC F₁) upperHalf upperHalf Gb₁)
    (hG₂ : IsHomeoExtension (liftToC F₂) upperHalf upperHalf Gb₂) (hinf₁ : Gb₁ extInf = extInf)
    (hinf₂ : Gb₂ extInf = extInf) (hbd : ∀ x : ℝ, Gb₁ ((x : ℂ) : ExtPlane) = Gb₂ ((x : ℂ) : ExtPlane))
    {γ δ₁ δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hR₁ : RepresentsConj F₁ γ δ₁)
    (hR₂ : RepresentsConj F₂ γ δ₂) : frickeTriple δ₁ = frickeTriple δ₂ := by
  have hbd' : ∀ y ∈ extRealLine, Gb₁ y = Gb₂ y := by
    rintro _ (⟨z, hz, rfl⟩ | hy)
    · have hz' : z = ((z.re : ℝ) : ℂ) :=
        Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hz)
      rw [hz']
      exact hbd z.re
    · rw [mem_singleton_iff.1 hy, hinf₁, hinf₂]
  have h₁ : ∀ τ, F₁ (γ • τ) = δ₁ • F₁ τ := fun τ => by rw [hR₁, F₁.symm_apply_apply]
  have h₂ : ∀ τ, F₂ (γ • τ) = δ₂ • F₂ τ := fun τ => by rw [hR₂, F₂.symm_apply_apply]
  have hR : RepresentsConj F₂ γ δ₁ := fun τ => by
    rw [h36t_deck_agree hG₁ hG₂ hbd' h₁ h₂ τ]
    exact hR₂ τ
  rcases s27g_rep_unique hR₂ hR with h | h
  · rw [h]
  · rw [h, s27f_frickeTriple_neg]

/-- Representatives equal up to sign give equal conjugations `F₁ ∘ x ∘ F₁⁻¹ = F₂ ∘ x ∘ F₂⁻¹` on `ℍ`. -/
theorem s27f_agree_of_pm {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {x δ₁ δ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR₁ : RepresentsConj F₁ x δ₁) (hR₂ : RepresentsConj F₂ x δ₂) (h : δ₁ = δ₂ ∨ δ₁ = -δ₂) :
    ∀ τ, F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ) := by
  intro τ
  rw [← hR₁ τ, ← hR₂ τ]
  rcases h with rfl | rfl
  · rfl
  · rw [← neg_one_mul, mul_smul, s27g_neg_one_smul]

/-- **From the generators to the group**: if `F₁ ∘ x ∘ F₁⁻¹ = F₂ ∘ x ∘ F₂⁻¹` on `ℍ` for the elements `x` of a standard
system of `Γ₀`, then for every `γ ∈ Γ₀` (the equation is stable under products and inverses, holds for `±1`, and the
system generates `Γ₀` modulo `±1`, `StandardGenerators.generate`). -/
theorem s27f_agree_of_gens {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ}
    (G : StandardGenerators Γ₀ g) {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hgen : ∀ x ∈ range (fun j => (G.first j).1) ∪ range (fun j => (G.first j).2) ∪ {G.γg, G.δg},
      ∀ τ, F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ)) :
    ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  have key : ∀ x ∈ Subgroup.closure
      ((range (fun j => (G.first j).1) ∪ range (fun j => (G.first j).2) ∪ {G.γg, G.δg}) ∪ {-1}),
      ∀ τ, F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hgen x hx
      · rw [mem_singleton_iff] at hx
        intro τ
        rw [hx, s27g_neg_one_smul, s27g_neg_one_smul, F₁.apply_symm_apply, F₂.apply_symm_apply]
    | one =>
      intro τ
      rw [one_smul, one_smul, F₁.apply_symm_apply, F₂.apply_symm_apply]
    | mul x y _ _ hx hy =>
      intro τ
      have e := hx (F₁ (y • F₁.symm τ))
      rw [F₁.symm_apply_apply, hy τ, F₂.symm_apply_apply] at e
      rw [mul_smul, mul_smul]
      exact e
    | inv x _ hx =>
      intro τ
      have e := hx (F₁ (x⁻¹ • F₁.symm τ))
      rw [F₁.symm_apply_apply, smul_inv_smul, F₁.apply_symm_apply] at e
      calc F₁ (x⁻¹ • F₁.symm τ) = F₂ (F₂.symm (F₁ (x⁻¹ • F₁.symm τ))) := (F₂.apply_symm_apply _).symm
        _ = F₂ (x⁻¹ • x • F₂.symm (F₁ (x⁻¹ • F₁.symm τ))) := by rw [inv_smul_smul]
        _ = F₂ (x⁻¹ • F₂.symm (F₂ (x • F₂.symm (F₁ (x⁻¹ • F₁.symm τ))))) := by rw [F₂.symm_apply_apply]
        _ = F₂ (x⁻¹ • F₂.symm τ) := by rw [← e]
  intro γ hγ
  refine key γ ?_
  rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, G.generate]
  exact Subgroup.mem_sup_left hγ

/-- **Equal conjugations give equivalent marked surfaces** (the final assembly of `thm27_1` `⇐`): the identity of `ℍ`
descends to a biholomorphic `c : X₁ → X₂` (`s27l_fiber_transfer`, `s27l_descend_homeomorph`), and Theorem 23.1
(`thm23_1_homotopy_iff`, with `γ₁ = 1`) gives `c ∘ f₁ ≃ f₂`. -/
theorem s27f_equiv_of_agree [T2Space S₀] [ConnectedSpace S₀]
    {Γ₀ Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {m₁ m₂ : MarkedRS S₀} {p₁ : UpperHalfPlane → m₁.X.carrier}
    {p₂ : UpperHalfPlane → m₂.X.carrier} (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF₁ : IsLift p₀ p₁ m₁.marking F₁)
    (hF₂ : IsLift p₀ p₂ m₂.marking F₂) (hag : ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ)) :
    m₁.Equiv m₂ := by
  obtain ⟨c, hc, hcp⟩ := s27l_descend_homeomorph hp₁ hp₂
    (s27l_fiber_transfer hp₀ hp₁ hF₁ hF₂ hag)
    (s27l_fiber_transfer hp₀ hp₂ hF₂ hF₁ fun γ hγ τ => (hag γ hγ τ).symm)
  refine ⟨c, hc, ?_⟩
  have hL : IsLift p₀ p₂ (m₁.marking.trans c) F₁ := fun τ => by
    show p₂ (F₁ τ) = c (m₁.marking (p₀ τ))
    rw [← hF₁, hcp]
  refine (thm23_1_homotopy_iff hp₀ hp₂ (m₁.marking.trans c) m₂.marking hL hF₂).2
    ⟨1, Γ₂.one_mem, fun γ hγ τ => ?_⟩
  rw [inv_one, one_smul, one_smul]
  exact hag γ hγ τ

/-- (27.6)–(27.7): equivalent marked surfaces have the same induced generators, hence the same
Fricke coordinates; conversely equal induced generators give equal normalized lifts on `ℝ`
(at the fixed points, hence everywhere), so the marked surfaces are equivalent.  Thus
`T(S₀) → F(S₀)` is a well defined bijection (`F(S₀)` is a model of `T(S₀)`), and the Fricke
coordinates determine the point (`γ_g(f)`, `δ_g(f)` being determined by the others). -/
theorem thm27_fricke_bijection [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    (∀ m : MarkedRS S₀, ∃ c, IsFrickeCoords p₀ G m c) ∧
      ∀ (m₁ m₂ : MarkedRS S₀) (c₁ c₂ : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)),
        IsFrickeCoords p₀ G m₁ c₁ → IsFrickeCoords p₀ G m₂ c₂ → (m₁.Equiv m₂ ↔ c₁ = c₂) := by
  refine ⟨fun m => ?_, fun m₁ m₂ c₁ c₂ hc₁ hc₂ => ?_⟩
  · -- Part 1: uniformization transport, then the induced system
    obtain ⟨Γ, p, F, Gb, hp, hN, -⟩ := s27u_exists_uniformization hp₀ m
    obtain ⟨G', hG'⟩ := exists_inducedGenerators hg hS hp₀ G m hp hN
    exact ⟨_, Γ, p, F, Gb, G', hp, hN, hG', rfl⟩
  obtain ⟨Γ₁, p₁, F₁, Gb₁, G₁, hp₁, hN₁, hI₁, rfl⟩ := hc₁
  obtain ⟨Γ₂, p₂, F₂, Gb₂, G₂, hp₂, hN₂, hI₂, rfl⟩ := hc₂
  constructor
  · -- `⇒`: equal boundary values (Theorem 27.1), hence equal representatives up to sign
    intro heq
    have hbd := (thm27_1 hg hS hp₀ m₁ m₂ hp₁ hp₂ hN₁ hN₂).1 heq
    funext j
    exact Prod.ext (s27f_triple_of_bdry hN₁.2.1 hN₂.2.1 hN₁.2.2.2.2 hN₂.2.2.2.2 hbd (hI₁.1 j).1 (hI₂.1 j).1)
      (s27f_triple_of_bdry hN₁.2.1 hN₂.2.1 hN₁.2.2.2.2 hN₂.2.2.2.2 hbd (hI₁.1 j).2 (hI₂.1 j).2)
  · -- `⇐`: the first pairs agree up to sign, hence so does the last pair, hence all conjugations agree
    intro hc
    have hcj : ∀ j, frickeTriple (G₁.first j).1 = frickeTriple (G₂.first j).1 ∧
        frickeTriple (G₁.first j).2 = frickeTriple (G₂.first j).2 := fun j => Prod.ext_iff.1 (congrFun hc j)
    have hpm : ∀ j, ((G₁.first j).1 = (G₂.first j).1 ∨ (G₁.first j).1 = -(G₂.first j).1) ∧
        ((G₁.first j).2 = (G₂.first j).2 ∨ (G₁.first j).2 = -(G₂.first j).2) := fun j =>
      ⟨s27f_pm_of_triple hp₁ hp₂ hN₁.2 hN₂.2 (G₁.first_mem j).1 (G₂.first_mem j).1 (hI₁.1 j).1 (hI₂.1 j).1
        (hcj j).1, s27f_pm_of_triple hp₁ hp₂ hN₁.2 hN₂.2 (G₁.first_mem j).2 (G₂.first_mem j).2 (hI₁.1 j).2
        (hI₂.1 j).2 (hcj j).2⟩
    -- the same `η` for both systems, since commutators do not see signs
    have hη : (List.ofFn fun j => commutatorSL (G₁.first j).1 (G₁.first j).2).prod =
        (List.ofFn fun j => commutatorSL (G₂.first j).1 (G₂.first j).2).prod :=
      congrArg (fun f : Fin (g - 1) → Matrix.SpecialLinearGroup (Fin 2) ℝ => (List.ofFn f).prod)
        (funext fun j => s27f_comm_pm (hpm j).1 (hpm j).2)
    have hrel₂ : (List.ofFn fun j => commutatorSL (G₁.first j).1 (G₁.first j).2).prod *
        commutatorSL G₂.γg G₂.δg = 1 ∨ (List.ofFn fun j => commutatorSL (G₁.first j).1 (G₁.first j).2).prod *
        commutatorSL G₂.γg G₂.δg = -1 := by
      rw [hη]
      exact G₂.relation
    obtain ⟨hD, hΓg⟩ := s27t_last_pair_core G₁.δg_diagonal G₂.δg_diagonal G₁.relation hrel₂
      G₁.γg_fixes_one G₂.γg_fixes_one G₁.alternate G₂.alternate
    have hag := s27f_agree_of_gens G (F₁ := F₁) (F₂ := F₂) fun x hx => by
      rcases hx with ((⟨j, rfl⟩ | ⟨j, rfl⟩) | hx)
      · exact s27f_agree_of_pm (hI₁.1 j).1 (hI₂.1 j).1 (hpm j).1
      · exact s27f_agree_of_pm (hI₁.1 j).2 (hI₂.1 j).2 (hpm j).2
      · rcases hx with rfl | hx
        · exact s27f_agree_of_pm hI₁.2.1 hI₂.2.1 hΓg
        · rw [mem_singleton_iff] at hx
          rw [hx]
          exact s27f_agree_of_pm hI₁.2.2 hI₂.2.2 hD
    exact s27f_equiv_of_agree hp₀ hp₁ hp₂ hN₁.1 hN₂.1 hag

/-! ## §27.2 The existence theorem -/

/-- §27.2: the map `Φ : T̃(S₀) → T(S₀)`, `S_{q,k} ↦ [S_{q,k}, f]`, `f` the Teichmüller deformation
map: `p ∈ T(S₀)` is the image of `(q, k)`. -/
def IsDeformationPoint (q : S₀ → ℂ → ℂ) (k : ℝ) (p : TeichSpace S₀) : Prop :=
  ∃ (X : ClosedRS.{u}) (e : S₀ ≃ₜ X.carrier) (hqc : IsQCRS e) (q' : X.carrier → ℂ → ℂ),
    IsTeichDeformation q k X e q' ∧ p = Quot.mk _ ⟨X, e, hqc⟩

/-- The new parameter at a zero commutes with multiplication by an `(m+2)`-th root of unity `ε`:
`T(εζ) = ε T(ζ)`, since `|ε| = 1` and `conj(ε)^{m+2} = 1`. -/
theorem s27g_teichStretchZero_mul (k : ℝ) (m : ℕ) {ε : ℂ} (hε : ε ^ (m + 2) = 1) (ζ : ℂ) :
    teichStretchZero k m (ε * ζ) = ε * teichStretchZero k m ζ := by
  have hεn : ‖ε‖ = 1 := by
    have h := congrArg norm hε
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hεn
    exact zero_ne_one hεn
  unfold teichStretchZero
  by_cases hζ : ζ = 0
  · simp [hζ]
  · have hεζ : ε * ζ ≠ 0 := mul_ne_zero hε0 hζ
    rw [ite_eq_right hεζ, ite_eq_right hζ]
    have hc : (conj (ε * ζ) / ((‖ε * ζ‖ : ℝ) : ℂ)) ^ (m + 2) = (conj ζ / ((‖ζ‖ : ℝ) : ℂ)) ^ (m + 2) := by
      rw [map_mul, norm_mul, hεn, one_mul, mul_div_assoc, mul_pow, ← map_pow, hε, map_one, one_mul]
    rw [hc]
    ring

/-- Two natural parameters at a zero of order `m` (including `m = 0`, a regular point) differ by an
`(m+2)`-th root of unity: (25.3) for `m = 0`, (25.6) for `m > 0`. -/
theorem s27g_natural_zero_unique {φ ζ ζ₁ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}
    (hζ : AnalyticAt ℂ ζ z₀) (hζ₁ : AnalyticAt ℂ ζ₁ z₀) (h0 : ζ z₀ = 0) (h0₁ : ζ₁ z₀ = 0)
    (hd : deriv ζ z₀ ≠ 0) (hd₁ : deriv ζ₁ z₀ ≠ 0)
    (h : ∀ᶠ z in 𝓝 z₀, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (h₁ : ∀ᶠ z in 𝓝 z₀, φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ₁ z ^ m * deriv ζ₁ z ^ 2) :
    ∃ ε : ℂ, ε ^ (m + 2) = 1 ∧ ∀ᶠ z in 𝓝 z₀, ζ z = ε * ζ₁ z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : ∀ᶠ z in 𝓝 z₀, deriv ζ z ^ 2 = φ z := h.mono fun z hz => by
      rw [hz]
      push_cast
      ring
    have e₁ : ∀ᶠ z in 𝓝 z₀, deriv ζ₁ z ^ 2 = φ z := h₁.mono fun z hz => by
      rw [hz]
      push_cast
      ring
    have hne : φ z₀ ≠ 0 := by
      rw [← e.self_of_nhds]
      exact pow_ne_zero 2 hd
    rcases eq25_3_natural_parameter_unique hζ hζ₁ h0 h0₁ e e₁ hne with hs | hs
    · exact ⟨1, by norm_num, hs.mono fun z hz => by rw [hz, one_mul]⟩
    · exact ⟨-1, by norm_num, hs.mono fun z hz => by rw [hz, neg_one_mul]⟩
  · exact eq25_6_natural_parameter_zero_unique hm hζ hζ₁ h0 h0₁ hd hd₁ h h₁

/-- **The comparison map of two Teichmüller deformations is holomorphic.**  For two deformations
`(X₁, e₁)`, `(X₂, e₂)` of `S₀` for the same `(q, k)`, the map `c = e₂ ∘ e₁⁻¹ : X₁ → X₂` is holomorphic at `e₁ p`:
with `m` the order of `q` at `p`, the natural parameters of the two deformations at `p` differ by an `(m+2)`-th root
of unity `ε` (`s27g_natural_zero_unique`), which commutes with the stretch (`s27g_teichStretchZero_mul`), so
`ζ₂' ∘ c = ε ζ₁'` near `e₁ p` in the charts, and `c = ζ₂'⁻¹ ∘ (ε ζ₁')` is holomorphic. -/
theorem s27g_mdifferentiableAt [T2Space S₀] [ConnectedSpace S₀] {q : S₀ → ℂ → ℂ} {k : ℝ}
    {X₁ X₂ : ClosedRS.{u}} {e₁ : S₀ ≃ₜ X₁.carrier} {e₂ : S₀ ≃ₜ X₂.carrier}
    {q₁ : X₁.carrier → ℂ → ℂ} {q₂ : X₂.carrier → ℂ → ℂ}
    (h₁ : IsTeichDeformation q k X₁ e₁ q₁) (h₂ : IsTeichDeformation q k X₂ e₂ q₂) (p : S₀) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier) (e₁ p) := by
  obtain ⟨m, ζ₀, Z₀, hD⟩ := s26d_a_data_exists h₁.initial h₁.initial_ne p
  have _ := ζ₀
  have _ := Z₀
  obtain ⟨-, ζ₁, ζ₁', hn₁, hn₁', hl₁⟩ := h₁.zero p m hD.order
  obtain ⟨-, ζ₂, ζ₂', hn₂, hn₂', hl₂⟩ := h₂.zero p m hD.order
  obtain ⟨ε, hε, hζε⟩ := s27g_natural_zero_unique hn₂.1 hn₁.1 hn₂.2.1 hn₁.2.1 hn₂.2.2.1 hn₁.2.2.1
    hn₂.2.2.2 hn₁.2.2.2
  have hc : (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier) (e₁ p) = e₂ p := by
    simp
  have hsrc : (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier) (e₁ p) ∈ (chartAt ℂ (e₂ p)).source := by
    rw [hc]
    exact mem_chart_source ℂ (e₂ p)
  refine (s23_mdifferentiableAt_iff (mem_chart_source ℂ (e₁ p)) hsrc).2
    ⟨(e₁.symm.trans e₂).continuous.continuousAt, ?_⟩
  set L : ℂ → ℂ := fun w => chartAt ℂ (e₂ p) ((e₁.symm.trans e₂ : X₁.carrier → X₂.carrier)
    ((chartAt ℂ (e₁ p)).symm w)) with hLdef
  set w₀ : ℂ := chartAt ℂ (e₁ p) (e₁ p) with hw₀
  have hw₀t : w₀ ∈ (chartAt ℂ (e₁ p)).target := (chartAt ℂ (e₁ p)).map_source (mem_chart_source ℂ (e₁ p))
  have hw₀l : (chartAt ℂ (e₁ p)).symm w₀ = e₁ p := (chartAt ℂ (e₁ p)).left_inv (mem_chart_source ℂ (e₁ p))
  have hLw₀ : L w₀ = chartAt ℂ (e₂ p) (e₂ p) := by
    simp only [hLdef, hw₀l, hc]
  -- continuity of `L` at `w₀`
  have hLc : ContinuousAt L w₀ := by
    have h1 : ContinuousAt (chartAt ℂ (e₁ p)).symm w₀ := (chartAt ℂ (e₁ p)).continuousAt_symm hw₀t
    have h2 : ContinuousAt (fun w => (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier)
        ((chartAt ℂ (e₁ p)).symm w)) w₀ := (e₁.symm.trans e₂).continuous.continuousAt.comp h1
    have h3 : ContinuousAt (chartAt ℂ (e₂ p)) ((e₁.symm.trans e₂ : X₁.carrier → X₂.carrier)
        ((chartAt ℂ (e₁ p)).symm w₀)) := by
      rw [hw₀l, hc]
      exact (chartAt ℂ (e₂ p)).continuousAt (mem_chart_source ℂ (e₂ p))
    exact ContinuousAt.comp (f := fun w => (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier)
      ((chartAt ℂ (e₁ p)).symm w)) h3 h2
  -- the chart coordinate at `p` as a function of `w`
  set Z : ℂ → ℂ := fun w => chartAt ℂ p (e₁.symm ((chartAt ℂ (e₁ p)).symm w)) with hZdef
  have hZc : Tendsto Z (𝓝 w₀) (𝓝 (chartAt ℂ p p)) := by
    have h1 : ContinuousAt (chartAt ℂ (e₁ p)).symm w₀ := (chartAt ℂ (e₁ p)).continuousAt_symm hw₀t
    have h2 : ContinuousAt (fun w => e₁.symm ((chartAt ℂ (e₁ p)).symm w)) w₀ :=
      e₁.symm.continuous.continuousAt.comp h1
    have h3 : ContinuousAt (chartAt ℂ p) (e₁.symm ((chartAt ℂ (e₁ p)).symm w₀)) := by
      rw [hw₀l, e₁.symm_apply_apply]
      exact (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
    have h4 := (ContinuousAt.comp (f := fun w => e₁.symm ((chartAt ℂ (e₁ p)).symm w)) h3 h2).tendsto
    have e4 : (chartAt ℂ p ∘ fun w => e₁.symm ((chartAt ℂ (e₁ p)).symm w)) w₀ = chartAt ℂ p p := by
      rw [Function.comp_apply, hw₀l, e₁.symm_apply_apply]
    rw [e4] at h4
    exact h4
  -- eventually `e₁⁻¹ (φ⁻¹ w)` lies in the chart source at `p`
  have hsrc' : ∀ᶠ w in 𝓝 w₀, e₁.symm ((chartAt ℂ (e₁ p)).symm w) ∈ (chartAt ℂ p).source := by
    have h1 : ContinuousAt (chartAt ℂ (e₁ p)).symm w₀ := (chartAt ℂ (e₁ p)).continuousAt_symm hw₀t
    have h2 : ContinuousAt (fun w => e₁.symm ((chartAt ℂ (e₁ p)).symm w)) w₀ :=
      e₁.symm.continuous.continuousAt.comp h1
    have h3 : (chartAt ℂ p).source ∈ 𝓝 (e₁.symm ((chartAt ℂ (e₁ p)).symm w₀)) := by
      rw [hw₀l, e₁.symm_apply_apply]
      exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
    exact h2 h3
  have htgt : ∀ᶠ w in 𝓝 w₀, w ∈ (chartAt ℂ (e₁ p)).target :=
    (chartAt ℂ (e₁ p)).open_target.mem_nhds hw₀t
  have hNg : ∀ᶠ w in 𝓝 w₀, ζ₂' (L w) = ε * ζ₁' w := by
    filter_upwards [hZc.eventually hl₁, hZc.eventually hl₂, hZc.eventually hζε, hsrc', htgt]
      with w hw1 hw2 hw3 hw4 hw5
    have hZl : (chartAt ℂ p).symm (Z w) = e₁.symm ((chartAt ℂ (e₁ p)).symm w) :=
      (chartAt ℂ p).left_inv hw4
    have hloc1 : localMapExpr e₁ p (Z w) = w := by
      simp only [localMapExpr, hZl, e₁.apply_symm_apply]
      exact (chartAt ℂ (e₁ p)).right_inv hw5
    have hloc2 : localMapExpr e₂ p (Z w) = L w := by
      simp only [localMapExpr, hZl, hLdef]
      rfl
    rw [hloc1] at hw1
    rw [hloc2] at hw2
    rw [hw2, hw3, s27g_teichStretchZero_mul k m hε, ← hw1]
  have hN : AnalyticAt ℂ ζ₂' (L w₀) := by
    rw [hLw₀]
    exact hn₂'.1
  have hN' : deriv ζ₂' (L w₀) ≠ 0 := by
    rw [hLw₀]
    exact hn₂'.2.2.1
  have hF : DifferentiableAt ℂ (fun w => ε * ζ₁' w) w₀ :=
    (hn₁'.1.differentiableAt).const_mul ε
  exact s26d_a_differentiableAt_of_comp hLc hN hN' hF hNg

/-- `c = e₂ ∘ e₁⁻¹` is holomorphic everywhere (`s27g_mdifferentiableAt` at `p = e₁⁻¹ y`). -/
theorem s27g_mdifferentiable [T2Space S₀] [ConnectedSpace S₀] {q : S₀ → ℂ → ℂ} {k : ℝ}
    {X₁ X₂ : ClosedRS.{u}} {e₁ : S₀ ≃ₜ X₁.carrier} {e₂ : S₀ ≃ₜ X₂.carrier}
    {q₁ : X₁.carrier → ℂ → ℂ} {q₂ : X₂.carrier → ℂ → ℂ}
    (h₁ : IsTeichDeformation q k X₁ e₁ q₁) (h₂ : IsTeichDeformation q k X₂ e₂ q₂) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (e₁.symm.trans e₂ : X₁.carrier → X₂.carrier) := by
  intro y
  have h := s27g_mdifferentiableAt h₁ h₂ (e₁.symm y)
  rwa [e₁.apply_symm_apply] at h

/-- §27.2: `Φ` is well defined: all deformations `S_{q,k}` give the same point of `T(S₀)`
(by Theorem 26.2, any two are equivalent marked surfaces). -/
theorem isDeformationPoint_unique [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {q : S₀ → ℂ → ℂ} {k : ℝ} {p p' : TeichSpace S₀}
    (h : IsDeformationPoint q k p) (h' : IsDeformationPoint q k p') : p = p' := by
  have _ := hg
  have _ := hS
  obtain ⟨X₁, e₁, hqc₁, q₁, hT₁, rfl⟩ := h
  obtain ⟨X₂, e₂, hqc₂, q₂, hT₂, rfl⟩ := h'
  apply Quot.sound
  refine ⟨e₁.symm.trans e₂, ⟨s27g_mdifferentiable hT₁ hT₂, e₂.symm.trans e₁, s27g_mdifferentiable hT₂ hT₁,
    fun y => by simp, fun y => by simp⟩, ?_⟩
  have he : (e₁.trans (e₁.symm.trans e₂) : S₀ ≃ₜ X₂.carrier) = e₂ := by
    ext x
    simp
  show ContinuousMap.Homotopic ((e₁.trans (e₁.symm.trans e₂) : S₀ ≃ₜ X₂.carrier) : C(S₀, X₂.carrier))
    (e₂ : C(S₀, X₂.carrier))
  rw [he]

/-- The injectivity core of (27.15) (UTM's companion `lemma27_1_injective_of_uniformization` is derived from it; S29's
`s29_m_equiv_of_eq` is used in its one-line form `Quot.eqvGen_exact`).  Two Teichmüller deformations
`S_{q₁,k₁}`, `S_{q₂,k₂}` (`‖e qᵢ‖ = 1`, `0 < kᵢ < 1`) representing the same point of `T(S₀)`, `S₀ = ℍ/Γ₀`, have
`k₁ = k₂` and `q₁ = q₂`: the inverse trick (`utm_x_dil_le_of_equiv`, both ways) gives `k₁ = k₂` and `e₂ = c ∘ e₁`; then
`q₂ = r q₁` with `r > 0` ([S7b]), and `‖e qᵢ‖ = 1` forces `r = 1`. -/
theorem s27w_injective_core [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {q₁ q₂ : (holQuadDiffSubmodule S₀).restrictScalars ℝ} (hq₁ : ‖e q₁‖ = 1) (hq₂ : ‖e q₂‖ = 1)
    {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hk₂ : 0 < k₂) (hk₂' : k₂ < 1) {p : TeichSpace S₀}
    (h₁ : IsDeformationPoint q₁ k₁ p) (h₂ : IsDeformationPoint q₂ k₂ p)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : k₁ = k₂ ∧ q₁ = q₂ := by
  obtain ⟨X₁, e₁, hqc₁, q'₁, hT₁, rfl⟩ := h₁
  obtain ⟨X₂, e₂, hqc₂, q'₂, hT₂, hp⟩ := h₂
  obtain ⟨c, hc, hhom⟩ := markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact hp)
  have hTM₁ := teichDeformation_isTeichmullerMap hT₁
  have hTM₂ := teichDeformation_isTeichmullerMap hT₂
  obtain ⟨h12, hfun⟩ := utm_x_dil_le_of_equiv hg hS hTM₁ hTM₂ hc hhom hp₀
  obtain ⟨h21, -⟩ := utm_x_dil_le_of_equiv hg hS hTM₂ hTM₁ hc.homeomorph_symm (utm_x_homotopic_trans_symm hhom) hp₀
  have hk : k₁ = k₂ := utm_x_eq_of_ofReal_le hk₁.le hk₁' hk₂.le hk₂' h12 h21
  refine ⟨hk, ?_⟩
  subst hk
  obtain ⟨r, hr, hqr⟩ := utm_x_eq_smul_of_trans hk₁ hTM₁ hTM₂ hc (hfun rfl)
  have hq : q₂ = r • q₁ := by
    apply Subtype.ext
    rw [hqr, Submodule.coe_smul_of_tower]
    funext x z
    simp [Complex.real_smul]
  have hr1 : r = 1 := by
    have h := hq₂
    rw [hq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hq₁, mul_one] at h
    exact h
  rw [hq, hr1, one_smul]

/-- (27.15): if `[S_{q₁,k₁}, f₁] = [S_{q₂,k₂}, f₂]` with `k₂ ≤ k₁`, there is a conformal
`φ : S_{q₁,k₁} → S_{q₂,k₂}` with `f₁ ≃ φ ∘ f₂`, so by Theorem 26.2 `K[f₁] ≤ K[φ ∘ f₂] = K[f₂]`,
`k₁ = k₂`, and then `f₁ = φ ∘ f₂`, `q₁ = q₂` (for `q₁, q₂` normalized on the unit sphere `B`). -/
theorem lemma27_1_injective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {q₁ q₂ : (holQuadDiffSubmodule S₀).restrictScalars ℝ} (hq₁ : ‖e q₁‖ = 1) (hq₂ : ‖e q₂‖ = 1)
    {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hk₂ : 0 < k₂) (hk₂' : k₂ < 1) {p : TeichSpace S₀}
    (h₁ : IsDeformationPoint q₁ k₁ p) (h₂ : IsDeformationPoint q₂ k₂ p) : k₁ = k₂ ∧ q₁ = q₂ := by
  -- `S₀` is `ℍ/Γ₀` by the uniformization theorem (S22), and the injectivity core applies
  obtain ⟨Γ₀, p₀, -, -, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg hS
  exact s27w_injective_core hg hS e hq₁ hq₂ hk₁ hk₁' hk₂ hk₂' h₁ h₂ hp₀

/-! ### Stage T3 (s27t, coordinator 553e2d): Beltrami-deformed surfaces and the continuity of Fricke coordinates

A non-book helper block for `eq27_17_lifts_converge` (item 15), `lemma27_2_path` (item 17) and `lemma27_2_connected`
(item 18); prefix `s27v_`.  Seven stubs, everything else proved.

1. **`X^μ`** ([A1], [A2]; proved `s27v_exists_marked`).  For `μ ∈ M(Γ₀)` (a Beltrami coefficient on `ℍ`,
   `‖μ‖∞ ≤ k < 1`, `Γ₀`-compatible) there is a marked surface `(X^μ, e)` of `S₀` whose lifted coefficient
   `s27u_liftCoeff p₀ e` is `μ` a.e. on `ℍ`.  `X^μ` is the point set of `S₀` with the charts `f^μ ∘ (local sections of
   p₀)` ([A1]); `e ∘ p₀ ∘ (f^μ|ℍ)⁻¹` uniformizes it (U6, [A1]), `f^μ|ℍ` is a `K`-q.c. lift of `e`, so `e` is `K`-q.c.
   ([A2]) and its lifted coefficient is the dilatation of that lift (U10), i.e. `μ` (U4').
2. **Continuity** ([B1]–[B4]; proved `s27v_fricke_tendsto`).  If the lifted coefficients of marked surfaces `mₙ`
   converge a.e. on `ℍ` to that of `m`, with a common bound `k < 1`, then every choice of Fricke coordinates of `mₙ`
   converges to the Fricke coordinates of `m`.  Theorem 13.8 in sequential a.e. form on `Δ` ([B1]), carried to the
   symmetric plane solutions by the Cayley map ([B2]), gives `f^{μₙ} → f^μ` on `ℍ`; the representatives of
   `f^{μₙ} γ (f^{μₙ})⁻¹` converge up to sign ([B3]); `frickeTriple` is continuous at hyperbolic elements inside a
   regime `c = 0` / `c ≠ 0` ([B4]), and conjugation by normalized lifts preserves the regime (`s27f_fix_infty`).
3. **Teichmüller deformations** ([C1]: E2's S3 of `Lemmas/UniformizedTeichmuller`, restated on `s27u_liftCoeff`).  The
   lifted coefficient of a Teichmüller map with initial differential `q` is `k ψ̄/|ψ|`, `ψ = utm_liftQD q p₀ ≠ 0` a.e.
4. **Glue** (proved): `s27v_eq27_17`, `s27v_lemma27_2_path`, `s27v_lemma27_2_connected` are the three targets.

No stub is a book statement, and none implies W-IoD (invariance of domain in `ℝ^{6g-6}`), W-RR (`dim_ℝ Q(S₀) = 6g-6`),
W-QC (`exists_qc_in_homotopy_class`), W-TOP (classification of surfaces, `π₁`) or W-UC (uniformizing an abstract
surface): each is a local analytic or algebraic statement about data built from the fixed uniformization `p₀`. -/

/-- **The local deck step.**  Let `p₀ : ℍ → Y` be continuous with fibres the `Γ₀`-orbits, and let `E` be an open
partial homeomorphism with `⇑E = p₀` (a local inverse of `p₀` is `E.symm`).  If `p₀ η₀` lies in the target of `E`,
then near `η₀` the local lift `E.symm ∘ p₀` is one fixed `γ ∈ Γ₀`: `E.symm (p₀ η) = γ • η`.  (Both `E.symm (p₀ η)` and
`γ • η` lie in the source of `E` near `η₀` and have the same image `p₀ η` under the injective `E`.) -/
theorem s27v_a_deck {Y : Type*} [TopologicalSpace Y] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → Y} (hcont : Continuous p₀)
    (hfib : ∀ τ₁ τ₂ : UpperHalfPlane, p₀ τ₁ = p₀ τ₂ ↔ ∃ γ ∈ Γ₀, γ • τ₁ = τ₂)
    (E : OpenPartialHomeomorph UpperHalfPlane Y) (hE : ⇑E = p₀) {η₀ : UpperHalfPlane} (hη₀ : p₀ η₀ ∈ E.target) :
    ∃ γ ∈ Γ₀, ∀ᶠ η in 𝓝 η₀, E.symm (p₀ η) = γ • η := by
  have hs : E.symm (p₀ η₀) ∈ E.source := E.map_target hη₀
  have h1 : p₀ (E.symm (p₀ η₀)) = p₀ η₀ := by
    rw [← congrFun hE (E.symm (p₀ η₀))]
    exact E.right_inv hη₀
  obtain ⟨γ, hγ, hγe⟩ := (hfib η₀ (E.symm (p₀ η₀))).1 h1.symm
  refine ⟨γ, hγ, ?_⟩
  have hsγ : γ • η₀ ∈ E.source := by
    rw [hγe]
    exact hs
  filter_upwards [hcont.continuousAt.preimage_mem_nhds (E.open_target.mem_nhds hη₀),
    (continuous_const_smul γ).continuousAt.preimage_mem_nhds (E.open_source.mem_nhds hsγ)] with η ha hb
  refine E.injOn (E.map_target ha) hb ?_
  rw [E.right_inv ha, congrFun hE (γ • η)]
  exact (hfib η (γ • η)).2 ⟨γ, hγ, rfl⟩

/-- **The chart `F ∘ E⁻¹` of `X^μ`**: for an open partial homeomorphism `E : ℍ → Y` (a local branch of the covering)
and a homeomorphism `F` of `ℍ`, the open partial homeomorphism `y ↦ F (E⁻¹ y)` of `Y` into `ℂ`, with source the target
of `E` (`s27v_a_chart_source`). -/
def s27v_a_chart {Y : Type*} [TopologicalSpace Y] (E : OpenPartialHomeomorph UpperHalfPlane Y)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : OpenPartialHomeomorph Y ℂ :=
  E.symm.trans ((UpperHalfPlane.isOpenEmbedding_coe.comp F.isOpenEmbedding).toOpenPartialHomeomorph _)

/-- The chart `s27v_a_chart E F` sends `y` to `F (E⁻¹ y)`. -/
theorem s27v_a_chart_apply {Y : Type*} [TopologicalSpace Y] (E : OpenPartialHomeomorph UpperHalfPlane Y)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (y : Y) : s27v_a_chart E F y = F (E.symm y) := by
  rfl

/-- The source of the chart `s27v_a_chart E F` is the target of `E`. -/
theorem s27v_a_chart_source {Y : Type*} [TopologicalSpace Y] (E : OpenPartialHomeomorph UpperHalfPlane Y)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : (s27v_a_chart E F).source = E.target := by
  simp [s27v_a_chart]

/-- The inverse of the chart `s27v_a_chart E F`: every point `w` of its target lies in `ℍ`, and the chart's inverse
sends it to `E (F⁻¹ w)`. -/
theorem s27v_a_chart_symm {Y : Type*} [TopologicalSpace Y] (E : OpenPartialHomeomorph UpperHalfPlane Y)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {w : ℂ} (hw : w ∈ (s27v_a_chart E F).target) :
    0 < w.im ∧ (s27v_a_chart E F).symm w = E (F.symm (UpperHalfPlane.ofComplex w)) := by
  have hy : (s27v_a_chart E F).symm w ∈ E.target := by
    rw [← s27v_a_chart_source E F]
    exact (s27v_a_chart E F).map_target hw
  have h1 : ((F (E.symm ((s27v_a_chart E F).symm w)) : UpperHalfPlane) : ℂ) = w := by
    rw [← s27v_a_chart_apply]
    exact (s27v_a_chart E F).right_inv hw
  have h2 : UpperHalfPlane.ofComplex w = F (E.symm ((s27v_a_chart E F).symm w)) := by
    have h := UpperHalfPlane.ofComplex_apply (F (E.symm ((s27v_a_chart E F).symm w)))
    rw [h1] at h
    exact h
  refine ⟨by rw [← h1]; exact UpperHalfPlane.coe_im_pos _, ?_⟩
  rw [h2, F.symm_apply_apply, E.right_inv hy]

/-- **The transition function of `X^μ`.**  In the setting of `s27v_xmu_exists`, for a local branch `E` of `p₀`
(`⇑E = p₀`), the map `v ↦ F (E⁻¹ (p₀ (F⁻¹ v)))` is complex differentiable at every `v₀ ∈ ℍ` with `p₀ (F⁻¹ v₀)` in the
target of `E`: near `v₀` it is `v ↦ γ' • v` (the local deck step `s27v_a_deck` gives `E⁻¹ ∘ p₀ = γ`, and U6
`s27u_conj_mobius` gives `F γ = γ' F`). -/
theorem s27v_a_phi {Y : Type*} [TopologicalSpace Y] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → Y} (hcont : Continuous p₀)
    (hfib : ∀ τ₁ τ₂ : UpperHalfPlane, p₀ τ₁ = p₀ τ₂ ↔ ∃ γ ∈ Γ₀, γ • τ₁ = τ₂) {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) (hΓ : IsGammaCompatible Γ₀ μ)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ τ)
    (E : OpenPartialHomeomorph UpperHalfPlane Y) (hE : ⇑E = p₀) {v₀ : ℂ} (hv₀ : 0 < v₀.im)
    (hmem : p₀ (F.symm (UpperHalfPlane.ofComplex v₀)) ∈ E.target) :
    DifferentiableAt ℂ (fun v => ((F (E.symm (p₀ (F.symm (UpperHalfPlane.ofComplex v)))) : UpperHalfPlane) : ℂ))
      v₀ := by
  obtain ⟨γ, hγ, hev⟩ := s27v_a_deck hcont hfib E hE hmem
  obtain ⟨γ', hγ'⟩ := s27u_conj_mobius hk₀ hk hμ hΓ hF hγ
  have ht : Tendsto (fun v => F.symm (UpperHalfPlane.ofComplex v)) (𝓝 v₀)
      (𝓝 (F.symm (UpperHalfPlane.ofComplex v₀))) :=
    (F.symm.continuous.continuousAt.comp (UpperHalfPlane.mdifferentiableAt_ofComplex hv₀).continuousAt).tendsto
  have hd : DifferentiableAt ℂ
      ((UpperHalfPlane.coe ∘ fun τ : UpperHalfPlane => γ' • τ) ∘ UpperHalfPlane.ofComplex) v₀ :=
    UpperHalfPlane.mdifferentiableAt_iff.1
      ((UpperHalfPlane.mdifferentiable_coe.comp (s27t_mdifferentiable_smul γ')) ⟨v₀, hv₀⟩)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [ht.eventually hev] with v hv
  simp only [Function.comp_apply]
  rw [hv, hγ', Homeomorph.apply_symm_apply]

/-- **[A1, stub] The Beltrami-deformed complex structure `X^μ`.**  For a `Γ₀`-compatible Beltrami coefficient `μ` on
`ℍ` (`‖μ‖∞ ≤ k < 1`) and `F = f^μ|ℍ`, there is a closed Riemann surface `X` and a homeomorphism `e : S₀ → X` for which
the transported projection `e ∘ p₀ ∘ F⁻¹ : ℍ → X` is holomorphic.  (`X = ℍ/G^μ`, `G^μ = F Γ₀ F⁻¹`, realized on the
point set of `S₀`; `e` is the identity of points.)

*Why true.*  Write `w = f^μ`.
- *Charts.*  For `p ∈ S₀` pick `τ_p ∈ p₀⁻¹(p)` and a local inverse `s_p` of the covering `p₀` near `p`
  (`hp₀.1.isLocalHomeomorph τ_p`).  Put `ψ_p = w ∘ s_p`, an open partial homeomorphism `S₀ → ℂ` (`w|ℍ = F` is an open
  embedding `ℍ → ℂ`).
- *Holomorphic transitions.*  On an overlap, `s_p ∘ p₀ = γ` near each point for one `γ ∈ Γ₀` (both are continuous lifts
  of `p₀` agreeing at a point, fibres of `p₀` = `Γ₀`-orbits; uniqueness of lifts on a small ball).  So
  `ψ_p ∘ ψ_{p'}⁻¹ = F γ F⁻¹` there, which is Möbius (U6, `s27u_conj_mobius`), hence holomorphic.
- *Package.*  `s26d_a_package` (with `Q = 0`) turns the atlas into a closed Riemann surface `X` on the point set of
  `S₀` (T2, connected, compact are inherited), with `e` the identity of points and `chartAt (e p) (e x) = ψ_p x`.
- *Holomorphy of `e ∘ p₀ ∘ F⁻¹`.*  At `τ₁` with `p = p₀(F⁻¹ τ₁)`, in the chart `ψ_p`:
  `ψ_p(p₀(F⁻¹ τ)) = F(s_p(p₀(F⁻¹ τ))) = F(γ F⁻¹ τ) = γ' • τ` near `τ₁` (the local deck step again, and U6).

*Route.*  The atlas as in `s26d_a_exists` (S26 l.1561) + `s26d_a_package` (S26 l.1528); `ClosedRS` bundling as in
`exists_teichDeformation` (S26 l.1678).  The local deck step from `IsCoveringMap.eq_of_comp_eq` (Mathlib) and the fibre
clause `hp₀.2.2.2`; the prover may split it out as a helper.  `MDifferentiable` as in `s27u_proj_mdifferentiable`
(S27 l.3687, `s23_mdifferentiableAt_iff` S23 l.196, `UpperHalfPlane.mdifferentiableAt_iff`).

*Reuse.*  S27 `s27u_conj_mobius` (l.3620), `s27u_fSym_upperHalf` (l.3525), `s27u_homeo_upper` (l.3548),
`s27t_mdifferentiable_smul` (l.163); S23 `h23l_b_coe_smul` (l.845); Mathlib
`Topology.IsOpenEmbedding.toOpenPartialHomeomorph`, `UpperHalfPlane.isOpenEmbedding_coe`.

*Walls.*  None: `X` is built from `p₀` and `μ` together with its uniformization (no W-UC); nothing about homotopy
classes, `π₁`, dimensions or invariance of domain.

*Estimate.*  0.45–0.9k lines. -/
theorem s27v_xmu_exists [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hΓ : IsGammaCompatible Γ₀ μ) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ τ) :
    ∃ (X : ClosedRS.{u}) (e : S₀ ≃ₜ X.carrier), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p₀ e F) := by
  have hcont : Continuous p₀ := hp₀.1.continuous
  have hEx : ∀ x : S₀, ∃ E : OpenPartialHomeomorph UpperHalfPlane S₀, x ∈ E.target ∧ ⇑E = p₀ := by
    intro x
    obtain ⟨τ, rfl⟩ := hp₀.2.2.1 x
    obtain ⟨E, hτE, hpE⟩ := hp₀.1.isLocalHomeomorph τ
    refine ⟨E, ?_, hpE.symm⟩
    rw [hpE]
    exact E.map_source hτE
  choose E hEmem hEp using hEx
  have hΦ : ∀ (x : S₀) (v₀ : ℂ), 0 < v₀.im → p₀ (F.symm (UpperHalfPlane.ofComplex v₀)) ∈ (E x).target →
      DifferentiableAt ℂ (fun v => ((F ((E x).symm (p₀ (F.symm (UpperHalfPlane.ofComplex v)))) : UpperHalfPlane) : ℂ))
        v₀ :=
    fun x _ hv₀ hm => s27v_a_phi hcont hp₀.2.2.2 hk₀ hk hμ hΓ hF (E x) (hEp x) hv₀ hm
  have hcompat : ∀ x x' : S₀, ∀ w ∈ (s27v_a_chart (E x') F).target,
      (s27v_a_chart (E x') F).symm w ∈ (s27v_a_chart (E x) F).source →
      DifferentiableAt ℂ (fun w => s27v_a_chart (E x) F ((s27v_a_chart (E x') F).symm w)) w := by
    intro x x' w hw hwx
    obtain ⟨hwim, hsw⟩ := s27v_a_chart_symm (E x') F hw
    rw [s27v_a_chart_source, hsw, hEp x'] at hwx
    refine (hΦ x w hwim hwx).congr_of_eventuallyEq ?_
    filter_upwards [(s27v_a_chart (E x') F).open_target.mem_nhds hw] with v hv
    rw [s27v_a_chart_apply, (s27v_a_chart_symm (E x') F hv).2, hEp x']
  obtain ⟨X, τX, cs, h2, hc, hcp, hman, e, _q', -, hX⟩ := s26d_a_package (fun x => s27v_a_chart (E x) F)
    (fun x => by rw [s27v_a_chart_source]; exact hEmem x) hcompat (fun _ _ => 0) (fun _ _ _ => rfl)
    (fun _ => differentiableOn_const 0) (fun _ _ _ _ _ => (zero_mul _).symm)
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => e (p₀ (F.symm τ))) := by
    intro τ₁
    have hkey : ∀ τ, chartAt ℂ (e (p₀ (F.symm τ₁))) (e (p₀ (F.symm τ))) =
        ((F ((E (p₀ (F.symm τ₁))).symm (p₀ (F.symm τ))) : UpperHalfPlane) : ℂ) := fun τ => (hX _).1 _
    have hd : DifferentiableAt ℂ
        ((fun τ => chartAt ℂ (e (p₀ (F.symm τ₁))) (e (p₀ (F.symm τ)))) ∘ UpperHalfPlane.ofComplex) (τ₁ : ℂ) := by
      have h := hΦ (p₀ (F.symm τ₁)) τ₁ τ₁.coe_im_pos (by
        rw [UpperHalfPlane.ofComplex_apply]
        exact hEmem _)
      refine h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
      simp only [Function.comp_apply]
      exact hkey _
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => chartAt ℂ (e (p₀ (F.symm τ₁))) (e (p₀ (F.symm τ)))) τ₁ :=
      UpperHalfPlane.mdifferentiableAt_iff.2 hd
    have hsrc : e (p₀ (F.symm τ₁)) ∈ (chartAt ℂ (e (p₀ (F.symm τ₁)))).source := mem_chart_source ℂ _
    have hcp' : Continuous (fun τ => e (p₀ (F.symm τ))) := e.continuous.comp (hcont.comp F.symm.continuous)
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (e (p₀ (F.symm τ₁)))).symm
        (chartAt ℂ (e (p₀ (F.symm τ₁))) (e (p₀ (F.symm τ₁)))) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) ((chartAt ℂ _).map_source hsrc)
    have hev : (fun τ => e (p₀ (F.symm τ))) =ᶠ[𝓝 τ₁]
        (chartAt ℂ (e (p₀ (F.symm τ₁)))).symm ∘ fun τ => chartAt ℂ (e (p₀ (F.symm τ₁))) (e (p₀ (F.symm τ))) := by
      filter_upwards [hcp'.continuousAt.preimage_mem_nhds ((chartAt ℂ _).open_source.mem_nhds hsrc)] with τ hτ
      exact ((chartAt ℂ _).left_inv hτ).symm
    exact (hm2.comp τ₁ hm1).congr_of_eventuallyEq hev
  exact ⟨⟨X⟩, e, hhol⟩


/-- **[A2, stub] A homeomorphism with a `K`-q.c. lift is `K`-q.c.** (the converse of `h23l_lift_isKQC`, S23 l.980).  If
`p₀`, `p` uniformize `S₀`, `S` and `F` is a lift of `f : S₀ → S` (`p ∘ F = f ∘ p₀`) with `liftToC F` `K`-q.c. on `ℍ`,
then every local expression of `f` is `K`-q.c.

*Why true.*  Fix `x ∈ S₀` and `z₀` in the domain of `L = localMapExpr f x`; pick `τ₀` over `y₀ = φ_x⁻¹ z₀`.  Near `τ₀`,
`ψ₀ = φ_x ∘ p₀ ∘ ofComplex` is conformal (holomorphic and locally injective: `p₀` is a local homeomorphism and the
chart `φ_x` contains `y₀`), and near `F τ₀`, `ψ₁ = φ_{f x} ∘ p ∘ ofComplex` is conformal (`f y₀ ∈` source of `φ_{f x}`).
On a neighbourhood of `z₀`, `L = ψ₁ ∘ liftToC F ∘ ψ₀⁻¹` (`p ∘ F = f ∘ p₀`), which is `K`-q.c. (`thm7_1_comp` twice,
`thm7_2_inv`, `1 · K · 1 = K`); `L` is injective on its domain (`s23_c1_injOn_localMapExpr`), so `s23_lg` globalizes.

*Route/reuse.*  The template is `h23l_lift_isKQC` (S23 l.980) read backwards.  Conformality of `φ_x ∘ p₀` in a chart
at `x` (not only at `p₀ τ₀`): `h23l_chart_proj` (S23 l.810) plus the holomorphic transition (`s23_transition`, S23
l.105), or the pattern of UTM `utm_liftQD_local` (l.468).  S23 `s23_lg` (l.206), `s23_localMapDomain_isOpen` (l.215),
`s23_c1_injOn_localMapExpr` (l.448); S07 `thm7_1_comp` (l.181), `thm7_2_inv` (l.310), `isKQC_one_of_conformal`
(l.171); S09 `ac_t_isKQC_restrict` (l.6555); S13 `ad_isKQC_congr` (l.5796).

*Walls.*  None (a chart computation with given uniformizations).

*Estimate.*  0.15–0.3k lines. -/
theorem s27v_isKQCRS_of_lift [IsManifold 𝓘(ℂ) ω S₀] {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ₀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p : UpperHalfPlane → S} (hp₀ : IsUniformization Γ₀ p₀) (hp : IsUniformization Γ p) {f : S₀ ≃ₜ S}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p f F) {K : ℝ} (hK : IsKQC (liftToC F) upperHalf K) :
    IsKQCRS f K := by
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  refine ⟨hK1, fun x => s23_lg (s23_localMapDomain_isOpen f.continuous x) hK1
    (s23_c1_injOn_localMapExpr f.injective x) fun z₀ hz₀ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := hp₀.2.2.1 ((chartAt ℂ x).symm z₀)
  have hy₀ : p₀ τ₀ ∈ (chartAt ℂ x).source := by
    rw [hτ₀]
    exact (chartAt ℂ x).map_target hz₀.1
  have hfy : p (F τ₀) ∈ (chartAt ℂ (f x)).source := by
    rw [hF τ₀, hτ₀]
    exact hz₀.2
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ := h23l_chart_proj hp₀.1 hp₀.2.1 x hy₀
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ := h23l_chart_proj hp.1 hp.2.1 (f x) hfy
  set ψ₀ : ℂ → ℂ := fun z => chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z)) with hψ₀def
  set V : Set ℂ := U₀ ∩ liftToC F ⁻¹' U₁ with hVdef
  have hVo : IsOpen V :=
    ((h23l_liftToC_continuousOn F.continuous).mono hU₀H).isOpen_inter_preimage hU₀o hU₁o
  have hτV : (τ₀ : ℂ) ∈ V := by
    refine ⟨hτU₀, ?_⟩
    show liftToC F (τ₀ : ℂ) ∈ U₁
    rw [h23l_liftToC_coe]
    exact hτU₁
  have h1 := thm7_2_inv (ac_t_isKQC_restrict hψ₀ hVo inter_subset_left)
  have hinvV : ∀ w ∈ ψ₀ '' V, Function.invFunOn ψ₀ V w ∈ V ∧ ψ₀ (Function.invFunOn ψ₀ V w) = w := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨Function.invFunOn_mem ⟨v, hv, rfl⟩, Function.invFunOn_eq ⟨v, hv, rfl⟩⟩
  have h2 := thm7_1_comp h1 hK (by
    rintro _ ⟨w, hw, rfl⟩
    exact hU₀H (hinvV w hw).1.1)
  have h3 := thm7_1_comp h2 hψ₁ (by
    rintro _ ⟨w, hw, rfl⟩
    exact (hinvV w hw).1.2)
  rw [one_mul, mul_one] at h3
  set W : Set ℂ := ψ₀ '' V ∩ localMapDomain f x with hWdef
  have hWo : IsOpen W := h1.1.inter (s23_localMapDomain_isOpen f.continuous x)
  have hz₀W : z₀ ∈ W := by
    refine ⟨⟨(τ₀ : ℂ), hτV, ?_⟩, hz₀⟩
    show chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex (τ₀ : ℂ))) = z₀
    rw [UpperHalfPlane.ofComplex_apply, hτ₀, (chartAt ℂ x).right_inv hz₀.1]
  refine ⟨W, hWo, hz₀W, inter_subset_right,
    ad_isKQC_congr (ac_t_isKQC_restrict h3 hWo inter_subset_left) fun w hw => ?_⟩
  obtain ⟨hvV, hvw⟩ := hinvV w hw.1
  set v := Function.invFunOn ψ₀ V w
  have hvH : 0 < v.im := hU₀H hvV.1
  simp only [Function.comp_apply]
  rw [h23l_liftToC_eq F hvH, UpperHalfPlane.ofComplex_apply, hF, ← hvw]
  unfold localMapExpr
  rw [(chartAt ℂ x).left_inv (hU₀s v hvV.1)]

/-- **`(ℍ, e ∘ p₀ ∘ F⁻¹)` uniformizes the target** as soon as it is holomorphic (proved; the proof of
`s27u_isUniformization` with the holomorphy as a hypothesis instead of U7).  Covering and surjectivity are formal; the
fibres are the orbits of `F Γ₀ F⁻¹` because `F γ F⁻¹` is Möbius (U6). -/
theorem s27v_isUniformization {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hΓ : IsGammaCompatible Γ₀ μ) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ τ)
    (f : S₀ ≃ₜ S) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p₀ f F)) :
    IsUniformization (s27u_conjGroup Γ₀ F) (s27u_proj p₀ f F) := by
  have hconj : ∀ γ ∈ Γ₀, ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F (γ • τ) = γ' • F τ :=
    fun _ hγ => s27u_conj_mobius hk₀ hk hμ hΓ hF hγ
  refine ⟨(hp₀.1.comp_homeomorph F.symm).homeomorph_comp f, hhol, fun y => ?_, fun τ₁ τ₂ => ?_⟩
  · obtain ⟨τ, hτ⟩ := hp₀.2.2.1 (f.symm y)
    refine ⟨F τ, ?_⟩
    show f (p₀ (F.symm (F τ))) = y
    rw [F.symm_apply_apply, hτ, f.apply_symm_apply]
  · show f (p₀ (F.symm τ₁)) = f (p₀ (F.symm τ₂)) ↔ _
    rw [f.injective.eq_iff, hp₀.2.2.2]
    constructor
    · rintro ⟨γ, hγ, h⟩
      obtain ⟨γ', hγ'⟩ := hconj γ hγ
      refine ⟨γ', ⟨γ, hγ, hγ'⟩, ?_⟩
      have h1 := hγ' (F.symm τ₁)
      rw [h, F.apply_symm_apply, F.apply_symm_apply] at h1
      exact h1.symm
    · rintro ⟨γ', ⟨γ, hγ, hγ'⟩, h⟩
      refine ⟨γ, hγ, ?_⟩
      have h1 := hγ' (F.symm τ₁)
      rw [F.apply_symm_apply, h] at h1
      rw [← h1, F.symm_apply_apply]

/-- **`X^μ` as a marked surface** (proved from [A1], [A2], U4', U5, U6, U10): for `μ ∈ M(Γ₀)` there is a marked surface
of `S₀` whose lifted coefficient is `μ` a.e. on `ℍ`. -/
theorem s27v_exists_marked [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hΓ : IsGammaCompatible Γ₀ μ) :
    ∃ m : MarkedRS S₀, ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ m.marking z = μ z := by
  obtain ⟨-, hN, hwK, -⟩ := s27u_sym_spec hk₀ hk hμ
  obtain ⟨hwU, -, -, hwKU, hwd⟩ := s27u_fSym_upperHalf hk₀ hk hμ
  obtain ⟨F, hF⟩ := s27u_homeo_upper hwK hN.2.1 hwU
  obtain ⟨X, e, hhol⟩ := s27v_xmu_exists hp₀ hk₀ hk hμ hΓ hF
  have hU := s27v_isUniformization hp₀ hk₀ hk hμ hΓ hF e hhol
  have hL : IsLift p₀ (s27u_proj p₀ e F) e F := fun τ => by
    show e (p₀ (F.symm (F τ))) = e (p₀ τ)
    rw [F.symm_apply_apply]
  have hFeq : EqOn (liftToC F) (s27u_fSym μ) upperHalf := fun z hz => by
    rw [h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    exact hF _
  have hFK : IsKQC (liftToC F) upperHalf ((1 + k) / (1 - k)) := ad_isKQC_congr hwKU hFeq
  refine ⟨⟨X, e, ⟨_, s27v_isKQCRS_of_lift hp₀ hU hL hFK⟩⟩, ?_⟩
  filter_upwards [hwd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
  show s27u_liftCoeff p₀ e z = μ z
  rw [← s27u_liftCoeff_eq_dilatation hp₀ hU hL hz, ← h1]
  exact abR_t_complexDilatation_congr isOpen_upperHalf hFeq hz

/-- The Möbius map `D z = (i - z)/(i + z) = -C(z)` (`C` the Cayley map), which maps `ℍ` onto `Δ` and `0, 1, ∞` to
`1, i, -1` (the three points fixed by the disc normalization of `IsDiscNormalizedSolution`). -/
def s27v_dmap (z : ℂ) : ℂ := -cayley z

/-- The inverse `D⁻¹ w = C⁻¹(-w) = i(1 - w)/(1 + w)` of `s27v_dmap`, mapping `Δ` onto `ℍ`. -/
def s27v_dinv (w : ℂ) : ℂ := cayleyInv (-w)

/-- The Beltrami coefficient on `Δ` of `D ∘ f^μ ∘ D⁻¹`: `μ(D⁻¹ w) · conj(D⁻¹'(w))/D⁻¹'(w)`, where
`D⁻¹'(w) = -2i/(1 + w)²`, so the factor is `-(1 + w)²/conj((1 + w)²)` (modulus `1`). -/
def s27v_discCoeff (μ : ℂ → ℂ) (w : ℂ) : ℂ := -(μ (s27v_dinv w) * ((1 + w) ^ 2 / conj ((1 + w) ^ 2)))

/-- `D` maps `ℍ` into `Δ`. -/
theorem s27v_dmap_mem {z : ℂ} (hz : 0 < z.im) : s27v_dmap z ∈ unitDisc := by
  have h := cayley_mem_unitDisc hz
  rw [unitDisc, mem_ball_zero_iff] at h ⊢
  rwa [s27v_dmap, norm_neg]

/-- `D⁻¹ (D z) = z` on `ℍ`. -/
theorem s27v_dinv_dmap {z : ℂ} (hz : 0 < z.im) : s27v_dinv (s27v_dmap z) = z := by
  rw [s27v_dinv, s27v_dmap, neg_neg, cayleyInv_cayley hz]

/-- `D⁻¹` maps `Δ` conformally onto `ℍ` (`w ↦ -w`, then the inverse Cayley map). -/
theorem s27v_dinv_conformal : IsConformalOnto s27v_dinv unitDisc upperHalf := by
  have hneg : IsConformalOnto (fun w : ℂ => -w) unitDisc unitDisc := by
    refine ⟨differentiable_neg.differentiableOn, fun a _ b _ h => neg_injective h, ?_⟩
    ext w
    simp only [mem_image, unitDisc, mem_ball_zero_iff]
    exact ⟨fun ⟨v, hv, hvw⟩ => by rw [← hvw, norm_neg]; exact hv, fun hw => ⟨-w, by rwa [norm_neg], neg_neg w⟩⟩
  exact s35a_x_isConformalOnto_cayleyInv.comp hneg

/-- **[B1, stub] Theorem 13.8, sequential form with a.e. convergence** (disc normalization).  If the Beltrami
coefficients `μₙ → μ` a.e. on `Δ` with a common bound `k < 1`, the normalized self-maps of `Δ` (fixing `1, i, -1`)
converge pointwise on `Δ`.

*Why true.*  This is `abT_seq` (S13 l.8134) with the hypothesis "`μ(tₙ, z) → μ(t₀, z)` for every `z`" weakened to a.e.
convergence: that proof uses the pointwise convergence of the coefficients exactly once, inside `hgood`, where it only
needs it for a.e. `z` (it concludes an a.e. statement).  Everything else (the quotients `hₙ = fₙ ∘ f⁻¹`,
`ab_quotient`; the disc normalization `ab_normalize`; the reflection `ab_reflect`; `ab_tendsto_id`; `ab_mob_tendsto`,
`ab_mob_near_id`) is unchanged.

*Route.*  Copy the proof of `abT_seq` (S13 l.8134–8258) with `u n`, `t₀` replaced by `n`, the limit, and `hgood` taken
from `hconv` (`filter_upwards [ae_all_iff.2 hbd, hconv, ...]`).

*Reuse.*  S13 `ab_quotient` (l.6217), `ab_normalize` (l.6383), `ab_reflect` (l.7297), `ab_tendsto_id` (l.7979),
`ab_mob_tendsto` (l.8008), `ab_mob_near_id` (l.8080), `abT_abMob_one` (l.8091), `abT_ae_conj_inv` (l.8105),
`abT_dilatation_congr` (l.8109), `abT_ae_image` (l.8115).

*Walls.*  None (Theorem 13.8 is installed and clean).

*Estimate.*  0.12–0.2k lines. -/
theorem s27v_disc_seq {μn : ℕ → ℂ → ℂ} {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμn : ∀ n, IsBeltramiCoeff (μn n) unitDisc k) (hμ : IsBeltramiCoeff μ unitDisc k)
    (hconv : ∀ᵐ z ∂(volume.restrict unitDisc), Tendsto (fun n => μn n z) atTop (𝓝 (μ z)))
    {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hfn : ∀ n, IsDiscNormalizedSolution (fn n) (μn n))
    (hf : IsDiscNormalizedSolution f μ) : ∀ z ∈ unitDisc, Tendsto (fun n => fn n z) atTop (𝓝 (f z)) := by
  -- adapted from the proof of S13 `abT_seq` (`u n ↦ n`, `t₀ ↦` the limit); only `hgood` changes
  intro z hz
  have hΔo : IsOpen unitDisc := isOpen_ball
  have h0Δ : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h1k : 0 < 1 - k := by linarith
  obtain ⟨K₁, hf₀K⟩ := hf.1
  have hf₀img : f '' unitDisc = unitDisc := hf.2.1
  -- the quotients `hₙ = fₙ ∘ f⁻¹` (piece Q)
  set h : ℕ → ℂ → ℂ := fun n => fn n ∘ Function.invFunOn f unitDisc with hdef
  have hQ : ∀ n, ∃ H : ExtPlane → ExtPlane, IsKQC (h n) unitDisc (((1 + k) / (1 - k)) ^ 2) ∧
      h n '' unitDisc = unitDisc ∧ IsHomeoExtension (h n) unitDisc unitDisc H ∧
      H ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ H (I : ExtPlane) = (I : ExtPlane) ∧
      H ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        ‖complexDilatation (h n) (f z)‖ * (1 - k) ≤ ‖μn n z - μ z‖ := by
    intro n
    obtain ⟨h1, h2, ⟨H, hH, hH1, hHI, hHm⟩, h4⟩ := ab_quotient hk₀ hk (hμn n) hμ (hfn n) hf
    exact ⟨H, h1, h2, hH, hH1, hHI, hHm, h4⟩
  choose H hhK hhimg hH hH1 hHI hHm hbd using hQ
  -- the centres `aₙ = hₙ 0` and the normalized maps (piece N)
  set a : ℕ → ℂ := fun n => h n 0 with hadef
  have haΔ : ∀ n, a n ∈ unitDisc := fun n => by
    rw [← hhimg n]
    exact mem_image_of_mem _ h0Δ
  set Gd : ℕ → ℂ → ℂ := fun n z => abMob (h n 0) (h n z) with hGddef
  have hN : ∀ n, ∃ G : ExtPlane → ExtPlane, IsKQC (Gd n) unitDisc (((1 + k) / (1 - k)) ^ 2) ∧
      Gd n '' unitDisc = unitDisc ∧ Gd n 0 = 0 ∧ IsHomeoExtension (Gd n) unitDisc unitDisc G ∧
      (∀ z : ℂ, ‖z‖ = 1 → G (z : ExtPlane) = OnePoint.map (abMob (a n)) (H n (z : ExtPlane))) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (Gd n) z = complexDilatation (h n) z := by
    intro n
    obtain ⟨h1, h2, h3, ⟨G, hG, hGb⟩, h5⟩ := ab_normalize (hhK n) (hhimg n) (hH n)
    exact ⟨G, h1, h2, h3, hG, hGb, h5⟩
  choose G hGdK hGdimg hGd0 hG hGb hGdμ using hN
  -- the reflected maps (piece R)
  have hR := fun n => ab_reflect (hGdK n) (hGdimg n) (hGd0 n) (hG n)
  choose g hgK hgs hgeq hgb hgsym hgμ using hR
  -- boundary values of `gₙ`
  have hgbd : ∀ n (w : ℂ), ‖w‖ = 1 → H n (w : ExtPlane) = (w : ExtPlane) →
      g n w = abMob (a n) w := by
    intro n w hw hHw
    apply OnePoint.coe_injective
    rw [hgb n w hw, hGb n w hw, hHw]
    rfl
  have hg1 : ∀ n, g n 1 = 1 := fun n => by
    rw [hgbd n 1 (by simp) (hH1 n), abT_abMob_one (haΔ n)]
  have hg0 : ∀ n, g n 0 = 0 := fun n => (hgeq n h0Δ).trans (hGd0 n)
  have hgΔ : ∀ n, g n '' unitDisc = unitDisc := fun n => (image_congr (hgeq n)).trans (hGdimg n)
  -- the dilatations of `hₙ` tend to `0` a.e. in `Δ` (piece Q's bound, the a.e. convergence, property (N)):
  -- the only step that differs from `abT_seq`
  have hgood : ∀ᵐ z ∂(volume.restrict unitDisc),
      Tendsto (fun n => complexDilatation (h n) (f z)) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.2 hbd, hconv] with z hzb hc
    have hc' : Tendsto (fun n => ‖μn n z - μ z‖ / (1 - k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => μn n z - μ z) atTop (𝓝 0) := by
        simpa using hc.sub_const (μ z)
      simpa using h1.norm.div_const (1 - k)
    refine squeeze_zero_norm (fun n => ?_) hc'
    rw [le_div_iff₀ h1k]
    exact hzb n
  have hin : ∀ᵐ w ∂(volume.restrict unitDisc),
      Tendsto (fun n => complexDilatation (h n) w) atTop (𝓝 0) := by
    have h1 := abT_ae_image (p := fun w => Tendsto (fun n => complexDilatation (h n) w) atTop (𝓝 0))
      hf₀K hgood
    rwa [hf₀img] at h1
  have hGdin : ∀ᵐ w, w ∈ unitDisc → Tendsto (fun n => complexDilatation (Gd n) w) atTop (𝓝 0) := by
    have h1 := (ae_restrict_iff' hΔo.measurableSet).1 (hin.and (ae_all_iff.2 hGdμ))
    filter_upwards [h1] with w hw hwΔ
    obtain ⟨ht, heq⟩ := hw hwΔ
    exact ht.congr fun n => (heq n).symm
  have hout := abT_ae_conj_inv hGdin
  have hsph : ∀ᵐ w : ℂ, ‖w‖ ≠ 1 := by
    have h1 : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere volume 0 1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with w hw
    simpa [mem_sphere_zero_iff_norm] using hw
  have hμL : ∀ᵐ w, Tendsto (fun n => complexDilatation (g n) w) atTop (𝓝 0) := by
    filter_upwards [hGdin, hout, hsph, ae_all_iff.2 hgμ] with w hw1 hw2 hw3 hw4
    rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
    · have hwΔ : w ∈ unitDisc := mem_ball_zero_iff.2 hlt
      exact (hw1 hwΔ).congr fun n => (abT_dilatation_congr hΔo (hgeq n) hwΔ).symm
    · exact absurd heq hw3
    · have hwi : (conj w)⁻¹ ∈ unitDisc := by
        refine mem_ball_zero_iff.2 ?_
        rw [norm_inv, Complex.norm_conj]
        exact inv_lt_one_of_one_lt₀ hgt
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h2 := (hw2 hwi).norm
      rw [norm_zero] at h2
      exact h2.congr fun n => (hw4 n hgt).symm
  -- the symmetric normalized maps tend to the identity (piece L)
  have hL := ab_tendsto_id hgK hgs hgΔ hg0 hg1 hgsym hμL
  -- so the Möbius normalizations tend to the identity (piece M)
  have hgI : ∀ n, g n I = abMob (a n) I := fun n => hgbd n I (by simp) (hHI n)
  have hgm : ∀ n, g n (-1) = abMob (a n) (-1) := fun n => hgbd n (-1) (by simp) (hHm n)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    refine ab_mob_tendsto haΔ ?_ ?_
    · exact (hL I (by simp)).congr fun n => hgI n
    · exact (hL (-1) (by norm_num)).congr fun n => hgm n
  -- conclusion: `fₙ z = hₙ (f z) → f z`
  have hw₀ : f z ∈ unitDisc := by
    rw [← hf₀img]
    exact mem_image_of_mem _ hz
  have hleft : Function.invFunOn f unitDisc (f z) = z := hf₀K.2.2.1.2.1.leftInvOn_invFunOn hz
  have hfz : ∀ n, fn n z = h n (f z) := fun n => by
    simp only [hdef, Function.comp_apply, hleft]
  have hhw : ∀ n, ‖h n (f z)‖ ≤ 1 := fun n => by
    have : h n (f z) ∈ unitDisc := by
      rw [← hhimg n]
      exact mem_image_of_mem _ hw₀
    exact (mem_ball_zero_iff.1 this).le
  have hconv' : Tendsto (fun n => abMob (a n) (h n (f z))) atTop (𝓝 (f z)) :=
    (hL (f z) (by linarith [mem_ball_zero_iff.1 hw₀])).congr fun n => hgeq n hw₀
  have hnear := ab_mob_near_id ha0 hhw
  have hlim : Tendsto (fun n => h n (f z)) atTop (𝓝 (f z)) := by
    have h1 := hconv'.sub hnear
    rw [sub_zero] at h1
    exact h1.congr fun n => by ring
  exact hlim.congr fun n => (hfz n).symm

/-- A homeomorphism of `ℂ̄` which agrees with `φ` on `U`, where `φ(U) = V`, is a homeomorphic extension of
`φ : U → V`. -/
theorem s27v_b_isHomeoExtension_of_homeomorph {φ : ℂ → ℂ} {U V : Set ℂ} (E : ExtPlane ≃ₜ ExtPlane)
    (hE : ∀ z ∈ U, E (z : ExtPlane) = ((φ z : ℂ) : ExtPlane)) (himg : φ '' U = V) :
    IsHomeoExtension φ U V E := by
  have h1 : E '' toExt U = toExt V := by
    rw [← himg, toExt, toExt, image_image, image_image]
    exact image_congr hE
  refine ⟨hE, E.continuous.continuousOn, E.injective.injOn, ?_⟩
  rw [E.image_closure, h1]

/-- `D = s27v_dmap` maps `ℍ` conformally onto `Δ` (the Cayley map, then `w ↦ -w`). -/
theorem s27v_b_dmap_conformal : IsConformalOnto s27v_dmap upperHalf unitDisc := by
  have hneg : IsConformalOnto (fun w : ℂ => -w) unitDisc unitDisc := by
    refine ⟨differentiable_neg.differentiableOn, fun a _ b _ h => neg_injective h, ?_⟩
    ext w
    simp only [mem_image, unitDisc, mem_ball_zero_iff]
    exact ⟨fun ⟨v, hv, hvw⟩ => by rw [← hvw, norm_neg]; exact hv, fun hw => ⟨-w, by rwa [norm_neg], neg_neg w⟩⟩
  exact hneg.comp isConformalOnto_cayley

/-- `D (D⁻¹ w) = w` on `Δ`. -/
theorem s27v_b_dmap_dinv {w : ℂ} (hw : w ∈ unitDisc) : s27v_dmap (s27v_dinv w) = w := by
  have hw' : ‖-w‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.1 hw
  rw [s27v_dmap, s27v_dinv, cayley_cayleyInv hw', neg_neg]

/-- The derivative of `D⁻¹ w = i(1 - w)/(1 + w)`: `D⁻¹'(w) = -2i/(1 + w)²` for `w ≠ -1`. -/
theorem s27v_b_hasDerivAt_dinv {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt s27v_dinv (-2 * I / (1 + w) ^ 2) w := by
  have e : s27v_dinv = fun v => I * (1 - v) / (1 + v) := funext fun v => by
    simp only [s27v_dinv, cayleyInv]
    ring
  rw [e]
  have h := (((hasDerivAt_id' w).const_sub 1).const_mul I).div ((hasDerivAt_id' w).const_add 1) hw
  convert h using 1
  ring

/-- The determinant of `D`, `z ↦ (-z + i)/(z + i)`, is `-2i ≠ 0`. -/
theorem s27v_b_dext_det : (-1 : ℂ) * I - I * 1 ≠ 0 := by
  rw [show (-1 : ℂ) * I - I * 1 = -2 * I by ring]
  exact mul_ne_zero (by norm_num) I_ne_zero

/-- The Möbius homeomorphism `z ↦ (-z + i)/(z + i)` of `ℂ̄` agrees with `D = s27v_dmap` off the pole `-i`. -/
theorem s27v_b_dext_coe {z : ℂ} (hz : z + I ≠ 0) :
    mobiusHomeomorph (-1) I 1 I s27v_b_dext_det (z : ExtPlane) = ((s27v_dmap z : ℂ) : ExtPlane) := by
  rw [mobiusHomeomorph_apply, mobiusExt_coe (by rwa [one_mul])]
  congr 1
  simp only [mobiusFn, s27v_dmap, cayley, one_mul]
  rw [← neg_div]
  congr 1
  ring

/-- The Möbius homeomorphism `z ↦ (-z + i)/(z + i)` of `ℂ̄` sends `∞` to `-1`. -/
theorem s27v_b_dext_infty :
    mobiusHomeomorph (-1) I 1 I s27v_b_dext_det extInf = (((-1 : ℂ) : ℂ) : ExtPlane) := by
  rw [mobiusHomeomorph_apply, mobiusExt_infty_of_ne one_ne_zero, div_one]

/-- The dilatation factor of `D⁻¹`: `conj(D⁻¹'(w))/D⁻¹'(w) = -(1 + w)²/conj((1 + w)²)`. -/
theorem s27v_b_factor {w : ℂ} (hw : 1 + w ≠ 0) :
    conj (-2 * I / (1 + w) ^ 2) / (-2 * I / (1 + w) ^ 2) = -((1 + w) ^ 2 / conj ((1 + w) ^ 2)) := by
  have hq : (1 + w) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hq' : conj ((1 + w) ^ 2) ≠ 0 := (map_ne_zero _).2 hq
  rw [map_div₀, map_mul, map_neg, Complex.conj_I, map_ofNat]
  field_simp

/-- **[B2, stub] The Cayley transport of `f^μ`.**  For a Beltrami coefficient `μ` on `ℍ` (`‖μ‖∞ ≤ k < 1`), the
conjugate `D ∘ f^μ ∘ D⁻¹` (`D = s27v_dmap`) is the disc-normalized solution for `s27v_discCoeff μ`, which is a Beltrami
coefficient on `Δ` bounded by `k`.

*Why true.*
- `f^μ` maps `ℍ` onto `ℍ` and is `K`-q.c. there (U4', `s27u_fSym_upperHalf`); `D⁻¹ : Δ → ℍ` and `D : ℍ → Δ` are
  conformal; so `D ∘ f^μ ∘ D⁻¹` is a `K`-q.c. self-map of `Δ` (`thm7_1_comp`, `isKQC_one_of_conformal`).
- Dilatation: `μ_{D ∘ h} = μ_h` (`s23_dilatation_comp_left`) and `μ_{W ∘ D⁻¹}(w) = μ_W(D⁻¹ w) conj(D⁻¹')/D⁻¹'`
  (`s23_dilatation_comp_right`), with `D⁻¹'(w) = -2i/(1 + w)²`; `μ_W = μ` a.e. on `ℍ`, pulled back by the conformal
  `D⁻¹` (`s23_c2_ae_pullback`).  `|s27v_discCoeff μ| = |μ ∘ D⁻¹|`, measurable, `≤ k` a.e. on `Δ` (same pullback).
- Boundary map: `F = D̂ ∘ OnePoint.map (f^μ) ∘ D̂⁻¹` (Möbius extensions to `ℂ̄`, `t1_homeomorph`); it extends the map to
  `Δ̄`, maps `Δ̄` onto `Δ̄`, and fixes `1 = D 0`, `i = D 1`, `-1 = D ∞` because `f^μ` fixes `0, 1, ∞`.

*Route/reuse.*  S05 `cayley` (l.6177), `cayleyInv` (l.6180), `isConformalOnto_cayley` (l.6249), `cayley_image_disc`
(l.6139, the `ℂ̄` form); S23 `s35a_x_isConformalOnto_cayleyInv` (l.1596), `s23_dilatation_comp_left/right` (l.154/162),
`s23_c2_ae_pullback` (l.578); S13 `s13x_th_cayleyExt_coe`, `s13x_th_cayleyExt_image` (l.11142/11152, the Cayley map on
`ℂ̄`), `t1_homeomorph` (l.4730); `Lemmas/Mobius` `IsConformalOnto.comp` (l.356), `IsHomeoExtension.comp` (l.362); here
`s27v_dinv_conformal`, `s27v_dmap_mem`, `s27v_dinv_dmap`.

*Walls.*  None.

*Estimate.*  0.3–0.55k lines. -/
theorem s27v_fSym_disc {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (s27v_discCoeff μ) unitDisc k ∧
      IsDiscNormalizedSolution (fun w => s27v_dmap (s27u_fSym μ (s27v_dinv w))) (s27v_discCoeff μ) := by
  obtain ⟨-, hN, hgK, -⟩ := s27u_sym_spec hk₀ hk hμ
  obtain ⟨hgU, -, -, hgKU, hgd⟩ := s27u_fSym_upperHalf hk₀ hk hμ
  set g := s27u_fSym μ with hgdef
  set Φ : ℂ → ℂ := fun w => s27v_dmap (g (s27v_dinv w)) with hΦ
  have hD := s27v_b_dmap_conformal
  have hDi := s27v_dinv_conformal
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hdinvK : IsKQC s27v_dinv unitDisc 1 := isKQC_one_of_conformal hΔo hDi
  have hDK : IsKQC s27v_dmap upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf hD
  have hdinvU : ∀ w ∈ unitDisc, s27v_dinv w ∈ upperHalf := fun w hw => hDi.mapsTo hw
  have hgU' : ∀ z ∈ upperHalf, g z ∈ upperHalf := fun z hz => by
    rw [← hgU]
    exact mem_image_of_mem _ hz
  have h1w : ∀ w ∈ unitDisc, (1 : ℂ) + w ≠ 0 := fun w hw h0 => by
    have hn : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    rw [show w = -1 by linear_combination h0, norm_neg, norm_one] at hn
    exact lt_irrefl _ hn
  have hgc : Continuous g := continuousOn_univ.1 hgK.2.2.1.1
  -- the image
  have himg : Φ '' unitDisc = unitDisc := by
    have e : Φ '' unitDisc = s27v_dmap '' (g '' (s27v_dinv '' unitDisc)) := by
      simp only [hΦ, image_image]
    rw [e, hDi.2.2, hgU, hD.2.2]
  -- the dilatation
  have hdil : ∀ᵐ w ∂(volume.restrict unitDisc), complexDilatation Φ w = s27v_discCoeff μ w := by
    filter_upwards [s23_c2_ae_pullback hdinvK hDi.2.2.subset hgd,
      ae_restrict_mem hΔo.measurableSet] with w hw hwΔ
    have hz := hdinvU w hwΔ
    have hgz := hgU' _ hz
    have hderiv := s27v_b_hasDerivAt_dinv (h1w w hwΔ)
    have hDat : ∀ u ∈ upperHalf, DifferentiableAt ℂ s27v_dmap u := fun u hu =>
      hD.1.differentiableAt (isOpen_upperHalf.mem_nhds hu)
    have hDiat : ∀ u ∈ unitDisc, DifferentiableAt ℂ s27v_dinv u := fun u hu =>
      hDi.1.differentiableAt (hΔo.mem_nhds hu)
    have hST : ∀ᶠ v in 𝓝 w, s27v_dmap (s27v_dinv v) = v :=
      Filter.eventually_of_mem (hΔo.mem_nhds hwΔ) fun v hv => s27v_b_dmap_dinv hv
    have hTS : ∀ᶠ u in 𝓝 (s27v_dinv w), s27v_dinv (s27v_dmap u) = u :=
      Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz) fun u hu => s27v_dinv_dmap hu
    have hTS' : ∀ᶠ u in 𝓝 (g (s27v_dinv w)), s27v_dinv (s27v_dmap u) = u :=
      Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hgz) fun u hu => s27v_dinv_dmap hu
    have hR := s23_dilatation_comp_right (g := s27v_dmap ∘ g) hderiv.differentiableAt (hDat _ hz) hST hTS
    have hL := s23_dilatation_comp_left hgc.continuousAt (hDat _ hgz)
      (hDiat _ (hD.mapsTo hgz)) hTS'
    have hΦe : Φ = (s27v_dmap ∘ g) ∘ s27v_dinv := rfl
    rw [hΦe, hR, hL, hw, hderiv.deriv, s27v_b_factor (h1w w hwΔ), s27v_discCoeff, neg_mul_eq_mul_neg]
  -- quasiconformality
  have hs1 : s27v_dinv '' unitDisc ⊆ upperHalf := hDi.2.2.subset
  have hs2 : (g ∘ s27v_dinv) '' unitDisc ⊆ upperHalf := by
    rintro _ ⟨w, hw, rfl⟩
    exact hgU' _ (hdinvU w hw)
  have hΦK : IsKQC Φ unitDisc (1 * ((1 + k) / (1 - k)) * 1) :=
    thm7_1_comp (f₂ := s27v_dmap) (thm7_1_comp hdinvK hgKU hs1) hDK hs2
  refine ⟨⟨((measurable_dzbar Φ).div (measurable_dz Φ)).aestronglyMeasurable.congr hdil, ?_⟩,
    ⟨⟨_, hΦK⟩, himg, hdil, ?_⟩⟩
  · -- the bound
    filter_upwards [s23_c2_ae_pullback hdinvK hDi.2.2.subset hμ.2,
      ae_restrict_mem hΔo.measurableSet] with w hw hwΔ
    have hq : (1 + w) ^ 2 ≠ 0 := pow_ne_zero 2 (h1w w hwΔ)
    rw [s27v_discCoeff, norm_neg, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hq), mul_one]
    exact hw
  · -- the boundary map `D̂ ∘ ĝ ∘ D̂⁻¹`
    obtain ⟨e, he⟩ := t1_homeomorph hgK hN.2.1
    set Dx := mobiusHomeomorph (-1) I 1 I s27v_b_dext_det with hDx
    have hD0 : Dx ((0 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
      rw [hDx, s27v_b_dext_coe (by rw [zero_add]; exact I_ne_zero)]
      congr 1
      rw [s27v_dmap, cayley, zero_sub, zero_add, neg_div, div_self I_ne_zero, neg_neg]
    have h1I : (1 : ℂ) + I ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      simp at this
    have hD1 : Dx ((1 : ℂ) : ExtPlane) = (I : ExtPlane) := by
      rw [hDx, s27v_b_dext_coe h1I]
      congr 1
      rw [s27v_dmap, cayley, ← neg_div, div_eq_iff h1I]
      linear_combination (-1 : ℂ) * I_sq
    set E : ExtPlane ≃ₜ ExtPlane := Dx.symm.trans (e.onePointCongr.trans Dx) with hEdef
    have hEa : ∀ p, E p = Dx (OnePoint.map e (Dx.symm p)) := fun p => rfl
    have hEc : ∀ z : ℂ, E (Dx (z : ExtPlane)) = Dx ((g z : ℂ) : ExtPlane) := fun z => by
      rw [hEa, Dx.symm_apply_apply, OnePoint.map_some, he]
    refine ⟨E, s27v_b_isHomeoExtension_of_homeomorph E (fun w hw => ?_) himg, ?_, ?_, ?_⟩
    · have hz := hdinvU w hw
      have h1 := hEc (s27v_dinv w)
      rw [hDx, s27v_b_dext_coe (cayley_den_ne_zero hz), s27v_b_dext_coe (cayley_den_ne_zero (hgU' _ hz)),
        s27v_b_dmap_dinv hw] at h1
      exact h1
    · rw [← hD0, hEc 0, hN.2.2.1]
    · rw [← hD1, hEc 1, hN.2.2.2.1]
    · rw [← s27v_b_dext_infty, hEa, ← hDx, Dx.symm_apply_apply, OnePoint.map_infty]

/-- **Theorem 13.8 for the symmetric plane solutions** (proved from [B1], [B2]): if `μₙ → μ` a.e. on `ℍ` with a common
bound `k < 1`, then `f^{μₙ} → f^μ` pointwise on `ℍ`. -/
theorem s27v_fSym_tendsto {μn : ℕ → ℂ → ℂ} {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμn : ∀ n, IsBeltramiCoeff (μn n) upperHalf k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hconv : ∀ᵐ z ∂(volume.restrict upperHalf), Tendsto (fun n => μn n z) atTop (𝓝 (μ z))) :
    ∀ z ∈ upperHalf, Tendsto (fun n => s27u_fSym (μn n) z) atTop (𝓝 (s27u_fSym μ z)) := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hB := fun n => s27v_fSym_disc hk₀ hk (hμn n)
  have hB0 := s27v_fSym_disc hk₀ hk hμ
  -- the disc coefficients converge a.e. on `Δ` (pulled back through the conformal `D⁻¹`)
  have hdinv : IsKQC s27v_dinv unitDisc 1 := isKQC_one_of_conformal isOpen_ball s27v_dinv_conformal
  have hpb := s23_c2_ae_pullback hdinv s27v_dinv_conformal.2.2.subset hconv
  have hνconv : ∀ᵐ w ∂(volume.restrict unitDisc),
      Tendsto (fun n => s27v_discCoeff (μn n) w) atTop (𝓝 (s27v_discCoeff μ w)) := by
    filter_upwards [hpb] with w hw
    exact (hw.mul_const _).neg
  have h1 := s27v_disc_seq hk₀ hk (fun n => (hB n).1) hB0.1 hνconv (fun n => (hB n).2) hB0.2 _
    (s27v_dmap_mem hz')
  simp only [s27v_dinv_dmap hz'] at h1
  -- apply `D⁻¹`, continuous on `Δ`, and use `f^ν(ℍ) = ℍ`
  have hmem : ∀ ν : ℂ → ℂ, IsBeltramiCoeff ν upperHalf k → 0 < (s27u_fSym ν z).im := fun ν hν => by
    have h := (s27u_fSym_upperHalf hk₀ hk hν).1
    have hm : s27u_fSym ν z ∈ s27u_fSym ν '' upperHalf := mem_image_of_mem _ hz
    rw [h] at hm
    exact hm
  have hc : ContinuousAt s27v_dinv (s27v_dmap (s27u_fSym μ z)) :=
    (s27v_dinv_conformal.1.differentiableAt (isOpen_ball.mem_nhds (s27v_dmap_mem (hmem μ hμ)))).continuousAt
  have h2 := hc.tendsto.comp h1
  rw [s27v_dinv_dmap (hmem μ hμ)] at h2
  exact h2.congr fun n => s27v_dinv_dmap (hmem _ (hμn n))

/-- `-g` acts on `ℍ` as `g` does (`-1` acts trivially, `s27g_neg_one_smul`). -/
theorem s27v_c_neg_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) : (-g) • τ = g • τ := by
  rw [← neg_one_mul, mul_smul, s27g_neg_one_smul]

/-- The entries of `-g ∈ SL(2, ℝ)` are the negated entries of `g`. -/
theorem s27v_c_neg_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) : (-g) i j = -g i j := by
  simp [Matrix.SpecialLinearGroup.coe_neg]

/-- **[B3, stub] Convergence of the conjugated generators, up to sign.**  If the homeomorphisms `Fₙ → F` pointwise on
`ℍ` and `δₙ`, `δ` represent `Fₙ γ Fₙ⁻¹`, `F γ F⁻¹`, then suitable signs `εₙ = ±δₙ` converge to `δ` in `SL(2, ℝ)`.

*Why true.*  `δₙ (Fₙ τ) = Fₙ (γ τ)` for all `τ`.  Take `τ₁ ≠ τ₂`: `aᵢₙ = Fₙ τᵢ → F τᵢ = aᵢ` (distinct) and
`δₙ aᵢₙ = Fₙ(γ τᵢ) → F(γ τᵢ) = δ aᵢ`.  The action of `SL(2, ℝ)` on `ℍ` is proper (Mathlib `ProperSMul SL(2, ℝ) ℍ`), so
`(δₙ)` is relatively compact, and every cluster point `δ*` satisfies `δ* aᵢ = δ aᵢ` (`ContinuousSMul`); an element of
`SL(2, ℝ)` fixing two points of `ℍ` is `±1` (fixed points of a non-scalar real Möbius map in `ℍ` are unique:
`γ₁₀ z² + (γ₁₁ - γ₀₀) z - γ₀₁ = 0` has conjugate roots), so `δ* = ±δ`.  Choosing `εₙ` as the sign closer to `δ`, every
subsequence of `(εₙ)` has a further subsequence converging to `δ`.

*Reuse.*  Mathlib `UpperHalfPlane.instProperSMul` (ProperAction.lean l.122), `instContinuousSMulSL2R` (l.42),
`isProperMap_smul_I` (l.98); S27 `s27g_eq_one_of_smul_eq` (l.2447), `s27g_rep_unique` (l.2474), `s27g_neg_one_smul`
(l.986); S23 `h23l_b_coe_smul` (l.845).

*Walls.*  None (`SL(2, ℝ)` algebra and topology).

*Estimate.*  0.15–0.3k lines. -/
theorem s27v_rep_tendsto {Fn : ℕ → UpperHalfPlane ≃ₜ UpperHalfPlane} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hconv : ∀ τ, Tendsto (fun n => Fn n τ) atTop (𝓝 (F τ))) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {δn : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hRn : ∀ n, RepresentsConj (Fn n) γ (δn n))
    (hR : RepresentsConj F γ δ) :
    ∃ ε : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ n, ε n = δn n ∨ ε n = -δn n) ∧ Tendsto ε atTop (𝓝 δ) := by
  -- the pairing `P g = Σ δᵢⱼ gᵢⱼ` separates `δ` from `-δ`
  set P : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℝ := fun g =>
    δ 0 0 * g 0 0 + δ 0 1 * g 0 1 + δ 1 0 * g 1 0 + δ 1 1 * g 1 1 with hP
  have hPc : Continuous P := by
    simp only [hP]
    fun_prop
  have hPneg : ∀ g, P (-g) = -P g := fun g => by
    simp only [hP, s27v_c_neg_apply]
    ring
  have hPδ : 0 < P δ := by
    have hdet := hnf_sl2_det δ
    simp only [hP]
    nlinarith [sq_nonneg (δ 0 0 - δ 1 1), sq_nonneg (δ 0 1 + δ 1 0)]
  -- choose the sign with `P ≥ 0`
  obtain ⟨ε, hεpm, hεP⟩ : ∃ ε : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ n, ε n = δn n ∨ ε n = -δn n) ∧ ∀ n, 0 ≤ P (ε n) := by
    refine ⟨fun n => if 0 ≤ P (δn n) then δn n else -δn n, fun n => ?_, fun n => ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · dsimp only
      split_ifs with h
      · exact h
      · rw [hPneg]
        linarith
  refine ⟨ε, hεpm, ?_⟩
  have hkey : ∀ n σ, ε n • Fn n σ = Fn n (γ • σ) := fun n σ => by
    have e : ε n • Fn n σ = δn n • Fn n σ := by
      rcases hεpm n with h | h
      · rw [h]
      · rw [h, s27v_c_neg_smul]
    rw [e, hRn n, (Fn n).symm_apply_apply]
  have hkey0 : ∀ σ, δ • F σ = F (γ • σ) := fun σ => by rw [hR, F.symm_apply_apply]
  -- properness: all `ε n` lie in one compact set
  set a : ℕ → UpperHalfPlane × UpperHalfPlane := fun n => (Fn n (γ • UpperHalfPlane.I), Fn n UpperHalfPlane.I)
    with ha_def
  have ha : Tendsto a atTop (𝓝 (F (γ • UpperHalfPlane.I), F UpperHalfPlane.I)) :=
    (hconv _).prodMk_nhds (hconv _)
  have hC := ((ProperSMul.isProperMap_smul_pair (G := Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (X := UpperHalfPlane)).isCompact_preimage ha.isCompact_insert_range).image continuous_fst
  have hεC : ∀ n, ε n ∈ Prod.fst '' ((fun gx : Matrix.SpecialLinearGroup (Fin 2) ℝ × UpperHalfPlane =>
      (gx.1 • gx.2, gx.2)) ⁻¹' insert (F (γ • UpperHalfPlane.I), F UpperHalfPlane.I) (range a)) := fun n =>
    ⟨(ε n, Fn n UpperHalfPlane.I), Or.inr ⟨n, by simp only [ha_def, hkey]⟩, rfl⟩
  have _ : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  have _ : FirstCountableTopology (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.firstCountableTopology
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨x, -, φ, hφ, hx⟩ := hC.tendsto_subseq (fun n => hεC (ns n))
  refine ⟨φ, ?_⟩
  have hnsφ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hx' : Tendsto (fun n => ε (ns (φ n))) atTop (𝓝 x) := hx
  -- every such limit acts as `δ`
  have hxs : ∀ w : UpperHalfPlane, x • w = δ • w := by
    intro w
    obtain ⟨σ, rfl⟩ := F.surjective w
    have h1 : Tendsto (fun n => ε (ns (φ n)) • Fn (ns (φ n)) σ) atTop (𝓝 (x • F σ)) :=
      hx'.smul ((hconv σ).comp hnsφ)
    have h2 : Tendsto (fun n => ε (ns (φ n)) • Fn (ns (φ n)) σ) atTop (𝓝 (δ • F σ)) := by
      simp only [hkey, hkey0]
      exact (hconv _).comp hnsφ
    exact tendsto_nhds_unique h1 h2
  rcases s27g_rep_unique (F := Homeomorph.refl _) (γ := δ) (fun _ => rfl) (fun τ => hxs τ) with hxδ | hxδ
  · rwa [hxδ] at hx'
  · exfalso
    have h0 : 0 ≤ P x := ge_of_tendsto (hPc.continuousAt.tendsto.comp hx') (Eventually.of_forall fun n => hεP _)
    rw [hxδ, hPneg] at h0
    linarith

/-- **[B4, stub] Continuity of `frickeTriple` at a hyperbolic element, within its regime.**  If `εₙ → δ` in `SL(2, ℝ)`,
`δ` is hyperbolic, and every `εₙ` is in the regime of `δ` (`(εₙ)₁₀ = 0 ↔ δ₁₀ = 0`), then
`frickeTriple εₙ → frickeTriple δ`.

*Why true.*  The multiplier is a continuous function of the trace.  For `δ₁₀ ≠ 0` all `εₙ` use the branch
`((a - d) ± sgn(a + d) √((a + d)² - 4))/(2c)`, continuous at `δ` because `c ≠ 0` and `sgn(a + d)` is locally constant
near `|a + d| > 2`.  For `δ₁₀ = 0` all `εₙ` are upper triangular; `ad = 1`, `|a + d| > 2` give `|a| ≠ 1`, so eventually
`|(εₙ)₀₀| > 1` iff `|a| > 1`, and the fixed points are `∞` (whose junk value `extToC ∞ = 0` is constant) and
`b/(d - a)` with `d - a ≠ 0`, continuous at `δ`.

*Reuse.*  S27 `attractingFixedPoint` (l.529), `repellingFixedPoint` (l.535), `multiplier` (l.542), `hnf_sign_sqrt`
(l.546), `hnf_fixed_of_eq_zero` (l.645), `hnf_core_eq` (l.657), `hnf_sl2_det` (l.563); Mathlib
`Matrix.SpecialLinearGroup.continuous_apply`, `Real.continuous_sqrt`.

*Walls.*  None (real algebra).

*Estimate.*  0.12–0.25k lines. -/
theorem s27v_frickeTriple_tendsto {ε : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : Tendsto ε atTop (𝓝 δ)) (hδ : 2 < |δ 0 0 + δ 1 1|)
    (hreg : ∀ n, ε n 1 0 = 0 ↔ δ 1 0 = 0) :
    Tendsto (fun n => frickeTriple (ε n)) atTop (𝓝 (frickeTriple δ)) := by
  -- the entries, the trace and `√(tr² - 4)` converge; hence so does the multiplier
  have he : ∀ i j : Fin 2, Tendsto (fun n => ε n i j) atTop (𝓝 (δ i j)) := fun i j =>
    ((by fun_prop : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g i j).tendsto δ).comp h
  have ht : Tendsto (fun n => ε n 0 0 + ε n 1 1) atTop (𝓝 (δ 0 0 + δ 1 1)) := (he 0 0).add (he 1 1)
  have hsq : Tendsto (fun n => Real.sqrt ((ε n 0 0 + ε n 1 1) ^ 2 - 4)) atTop
      (𝓝 (Real.sqrt ((δ 0 0 + δ 1 1) ^ 2 - 4))) := ((ht.pow 2).sub_const 4).sqrt
  have hmul : Tendsto (fun n => multiplier (ε n)) atTop (𝓝 (multiplier δ)) :=
    ((ht.abs.add hsq).div_const 2).pow 2
  have hre : ∀ r : ℝ, (extToC ((r : ℂ) : ExtPlane)).re = r := fun _ => rfl
  suffices H : Tendsto (fun n => (extToC (attractingFixedPoint (ε n))).re) atTop
      (𝓝 (extToC (attractingFixedPoint δ)).re) ∧
      Tendsto (fun n => (extToC (repellingFixedPoint (ε n))).re) atTop
      (𝓝 (extToC (repellingFixedPoint δ)).re) from
    H.1.prodMk_nhds (H.2.prodMk_nhds hmul)
  by_cases hc : δ 1 0 = 0
  · -- `c = 0`: the fixed points are `∞` (junk value `0`) and `b/(d - a)`, in an eventually constant order
    have hcn : ∀ n, ε n 1 0 = 0 := fun n => (hreg n).2 hc
    have had : δ 0 0 * δ 1 1 = 1 := by
      have e := hnf_sl2_det δ
      rwa [hc, mul_zero, sub_zero] at e
    obtain ⟨hda, -, -⟩ := hnf_core_eq had hδ
    have hq : Tendsto (fun n => ε n 0 1 / (ε n 1 1 - ε n 0 0)) atTop (𝓝 (δ 0 1 / (δ 1 1 - δ 0 0))) :=
      (he 0 1).div ((he 1 1).sub (he 0 0)) hda
    by_cases ha : 1 < |δ 0 0|
    · have hev : ∀ᶠ n in atTop, 1 < |ε n 0 0| := (he 0 0).abs.eventually_const_lt ha
      obtain ⟨h1, h2⟩ := (hnf_fixed_of_eq_zero hc).1 ha
      rw [h1, h2, hre]
      refine ⟨tendsto_const_nhds.congr' ?_, hq.congr' ?_⟩
      · filter_upwards [hev] with n hn
        rw [((hnf_fixed_of_eq_zero (hcn n)).1 hn).1]
      · filter_upwards [hev] with n hn
        rw [((hnf_fixed_of_eq_zero (hcn n)).1 hn).2, hre]
    · have ha1 : |δ 0 0| < 1 := by
        rcases lt_or_eq_of_le (not_lt.1 ha) with h' | h'
        · exact h'
        · exfalso
          apply hda
          have h2 : δ 0 0 ^ 2 = 1 := by rw [← sq_abs, h']; norm_num
          linear_combination (-δ 1 1) * h2 + δ 0 0 * had
      have hev : ∀ᶠ n in atTop, ¬ 1 < |ε n 0 0| :=
        ((he 0 0).abs.eventually_lt_const ha1).mono fun n hn => not_lt.2 hn.le
      obtain ⟨h1, h2⟩ := (hnf_fixed_of_eq_zero hc).2 ha
      rw [h1, h2, hre]
      refine ⟨hq.congr' ?_, tendsto_const_nhds.congr' ?_⟩
      · filter_upwards [hev] with n hn
        rw [((hnf_fixed_of_eq_zero (hcn n)).2 hn).1, hre]
      · filter_upwards [hev] with n hn
        rw [((hnf_fixed_of_eq_zero (hcn n)).2 hn).2]
  · -- `c ≠ 0`: the explicit formulas, with `sgn(a + d)` eventually constant
    have hcn : ∀ n, ε n 1 0 ≠ 0 := fun n h0 => hc ((hreg n).1 h0)
    have ht0 : δ 0 0 + δ 1 1 ≠ 0 := fun h0 => by
      rw [h0, abs_zero] at hδ
      linarith
    have hsg : Tendsto (fun n => Real.sign (ε n 0 0 + ε n 1 1)) atTop (𝓝 (Real.sign (δ 0 0 + δ 1 1))) := by
      refine tendsto_const_nhds.congr' ?_
      rcases lt_or_gt_of_ne ht0 with hneg | hpos
      · filter_upwards [ht.eventually_lt_const hneg] with n hn
        rw [Real.sign_of_neg hneg, Real.sign_of_neg hn]
      · filter_upwards [ht.eventually_const_lt hpos] with n hn
        rw [Real.sign_of_pos hpos, Real.sign_of_pos hn]
    have hden : Tendsto (fun n => 2 * ε n 1 0) atTop (𝓝 (2 * δ 1 0)) := (he 1 0).const_mul 2
    have h2c : 2 * δ 1 0 ≠ 0 := mul_ne_zero two_ne_zero hc
    have hA : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ 1 0 ≠ 0 → (extToC (attractingFixedPoint γ)).re =
        (γ 0 0 - γ 1 1 + Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) / (2 * γ 1 0) :=
      fun γ hγ => by rw [attractingFixedPoint, ite_eq_right hγ, hre]
    have hR : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ 1 0 ≠ 0 → (extToC (repellingFixedPoint γ)).re =
        (γ 0 0 - γ 1 1 - Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) / (2 * γ 1 0) :=
      fun γ hγ => by rw [repellingFixedPoint, ite_eq_right hγ, hre]
    rw [hA δ hc, hR δ hc]
    refine ⟨?_, ?_⟩
    · simp only [hA _ (hcn _)]
      exact (((he 0 0).sub (he 1 1)).add (hsg.mul hsq)).div hden h2c
    · simp only [hR _ (hcn _)]
      exact (((he 0 0).sub (he 1 1)).sub (hsg.mul hsq)).div hden h2c

/-- **Convergence of one Fricke triple** (proved from [B3], [B4]): with `Fₙ → F` pointwise on `ℍ` (all normalized, with
boundary maps fixing `∞`), the representatives `δₙ` of `Fₙ γ Fₙ⁻¹` have `frickeTriple δₙ → frickeTriple δ`.  If `δ` is
`±1` so is every `δₙ` (`γ` acts trivially); otherwise `δ` is hyperbolic (`s27f_hyp`), the regime is that of `γ`
(`s27f_fix_infty`), and `frickeTriple` does not see the sign (`s27f_frickeTriple_neg`). -/
theorem s27v_triple_tendsto {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {Fn : ℕ → UpperHalfPlane ≃ₜ UpperHalfPlane} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    {Gbn : ℕ → ExtPlane → ExtPlane} {Gb : ExtPlane → ExtPlane}
    (hGn : ∀ n, IsHomeoExtension (liftToC (Fn n)) upperHalf upperHalf (Gbn n)) (hGninf : ∀ n, Gbn n extInf = extInf)
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb) (hGinf : Gb extInf = extInf)
    (hconv : ∀ τ, Tendsto (fun n => Fn n τ) atTop (𝓝 (F τ))) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {δn : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ) (hRn : ∀ n, RepresentsConj (Fn n) γ (δn n))
    (hR : RepresentsConj F γ δ) : Tendsto (fun n => frickeTriple (δn n)) atTop (𝓝 (frickeTriple δ)) := by
  by_cases h₁ : δ = 1 ∨ δ = -1
  · -- `γ` acts trivially, so every `δₙ` is `±1`
    have hδτ : ∀ τ : UpperHalfPlane, δ • τ = τ := fun τ => by
      rcases h₁ with rfl | rfl
      · exact one_smul _ _
      · exact s27g_neg_one_smul τ
    have hγ : ∀ σ : UpperHalfPlane, γ • σ = σ := fun σ => by
      have e := hR (F σ)
      rw [hδτ, F.symm_apply_apply] at e
      exact F.injective e.symm
    have hconst : ∀ n, frickeTriple (δn n) = frickeTriple δ := fun n => by
      have hτ : ∀ τ : UpperHalfPlane, δn n • τ = τ := fun τ => by
        rw [hRn n τ, hγ, (Fn n).apply_symm_apply]
      have hpm : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) ℝ, (ρ = 1 ∨ ρ = -1) → frickeTriple ρ = frickeTriple 1 := by
        rintro ρ (rfl | rfl)
        · rfl
        · exact s27f_frickeTriple_neg 1
      rw [hpm _ (s27g_eq_one_of_smul_eq hτ), hpm _ h₁]
    simp only [hconst]
    exact tendsto_const_nhds
  · push Not at h₁
    have hhyp := s27f_hyp hp hδ h₁.1 h₁.2
    obtain ⟨ε, hε, hεt⟩ := s27v_rep_tendsto hconv hRn hR
    have hreg : ∀ n, ε n 1 0 = 0 ↔ δ 1 0 = 0 := fun n => by
      have h1 := s27f_fix_infty (hGn n) (hGninf n) (hRn n)
      have h2 := s27f_fix_infty hG hGinf hR
      rcases hε n with h | h
      · rw [h]
        exact h1.symm.trans h2
      · rw [h, s27t_neg_apply, neg_eq_zero]
        exact h1.symm.trans h2
    refine (s27v_frickeTriple_tendsto hεt hhyp hreg).congr fun n => ?_
    rcases hε n with h | h
    · rw [h]
    · rw [h, s27f_frickeTriple_neg]

/-- **Continuity of the Fricke coordinates in the lifted coefficient** (proved from [B1]–[B4] and the installed UT and
Fricke bijection).  If the lifted coefficients of `mₙ` converge a.e. on `ℍ` to that of `m`, with a common bound `k < 1`,
then any Fricke coordinates of `mₙ` converge to any Fricke coordinates of `m`: by uniqueness they are the coordinates of
the systems induced by the UT lifts `f^{μₙ}|ℍ`, and these converge generator by generator. -/
theorem s27v_fricke_tendsto [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {mn : ℕ → MarkedRS S₀} {m : MarkedRS S₀} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμn : ∀ n, IsBeltramiCoeff (s27u_liftCoeff p₀ (mn n).marking) upperHalf k)
    (hμ : IsBeltramiCoeff (s27u_liftCoeff p₀ m.marking) upperHalf k)
    (hconv : ∀ᵐ z ∂(volume.restrict upperHalf),
      Tendsto (fun n => s27u_liftCoeff p₀ (mn n).marking z) atTop (𝓝 (s27u_liftCoeff p₀ m.marking z)))
    {cn : ℕ → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    (hcn : ∀ n, IsFrickeCoords p₀ G (mn n) (cn n)) (hc : IsFrickeCoords p₀ G m c) : Tendsto cn atTop (𝓝 c) := by
  -- UT for every `mₙ` and for `m`, and the induced systems
  choose Fn hFn using fun n => s27u_uniformization_transport hp₀ (mn n).marking (mn n).qc
  obtain ⟨F, hF, hU, hN, -, -⟩ := s27u_uniformization_transport hp₀ m.marking m.qc
  choose G' hG' using fun n => exists_inducedGenerators hg hS hp₀ G (mn n) (hFn n).2.1 (hFn n).2.2.1
  obtain ⟨G₀', hG₀'⟩ := exists_inducedGenerators hg hS hp₀ G m hU hN
  -- the given coordinates are those of the induced systems (Fricke coordinates are unique)
  have hbij := thm27_fricke_bijection hg hS hp₀ G
  have hcn' : ∀ n, cn n = frickeCoordinates (G' n) := fun n =>
    (hbij.2 (mn n) (mn n) _ _ (hcn n) ⟨_, _, Fn n, _, G' n, (hFn n).2.1, (hFn n).2.2.1, hG' n, rfl⟩).1
      (markedRS_equiv_equivalence.refl _)
  have hc' : c = frickeCoordinates G₀' :=
    (hbij.2 m m _ _ hc ⟨_, _, F, _, G₀', hU, hN, hG₀', rfl⟩).1 (markedRS_equiv_equivalence.refl _)
  -- `Fₙ → F` pointwise on `ℍ`
  have hpt := s27v_fSym_tendsto hk₀ hk hμn hμ hconv
  have hFconv : ∀ τ, Tendsto (fun n => Fn n τ) atTop (𝓝 (F τ)) := fun τ => by
    have h := hpt τ τ.coe_im_pos
    rw [← hF τ] at h
    exact UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.2 (h.congr fun n => ((hFn n).1 τ).symm)
  rw [hc']
  refine (tendsto_pi_nhds.2 fun j => ?_).congr fun n => (hcn' n).symm
  exact Tendsto.prodMk_nhds
    (s27v_triple_tendsto hU (fun n => (hFn n).2.2.1.2.1) (fun n => (hFn n).2.2.1.2.2.2.2) hN.2.1 hN.2.2.2.2 hFconv
      (G₀'.first_mem j).1 (fun n => ((hG' n).1 j).1) (hG₀'.1 j).1)
    (s27v_triple_tendsto hU (fun n => (hFn n).2.2.1.2.1) (fun n => (hFn n).2.2.1.2.2.2.2) hN.2.1 hN.2.2.2.2 hFconv
      (G₀'.first_mem j).2 (fun n => ((hG' n).1 j).2) (hG₀'.1 j).2)

/-- `IsBeltramiCoeff` is monotone in the bound. -/
theorem s27v_isBeltramiCoeff_mono {μ : ℂ → ℂ} {D : Set ℂ} {k k' : ℝ} (h : IsBeltramiCoeff μ D k) (hkk : k ≤ k') :
    IsBeltramiCoeff μ D k' := by
  exact ⟨h.1, h.2.mono fun _ hz => hz.trans hkk⟩

/-- A marked surface's lifted coefficient is a Beltrami coefficient on `ℍ` with some bound `k < 1` (U3). -/
theorem s27v_liftCoeff_bound [IsManifold 𝓘(ℂ) ω S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (m : MarkedRS S₀) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff (s27u_liftCoeff p₀ m.marking) upperHalf k := by
  obtain ⟨K, hK⟩ := m.qc
  have hK1 : (1 : ℝ) ≤ K := hK.1
  exact ⟨(K - 1) / (K + 1), div_nonneg (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith),
    s27u_liftCoeff_isBeltramiCoeff hp₀ hK⟩

/-- **Theorem 27.1 through UT**: two marked surfaces are equivalent iff the symmetric solutions of their lifted
coefficients agree on `ℝ` (`s27u_exists_uniformization` gives normalized lifts with boundary values `f^μ` on `ℝ`). -/
theorem s27v_equiv_iff_fSym [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (m₁ m₂ : MarkedRS S₀) :
    m₁.Equiv m₂ ↔ ∀ x : ℝ, s27u_fSym (s27u_liftCoeff p₀ m₁.marking) x = s27u_fSym (s27u_liftCoeff p₀ m₂.marking) x := by
  obtain ⟨Γ₁, p₁, F₁, G₁, hp₁, hN₁, -, hG₁⟩ := s27u_exists_uniformization hp₀ m₁
  obtain ⟨Γ₂, p₂, F₂, G₂, hp₂, hN₂, -, hG₂⟩ := s27u_exists_uniformization hp₀ m₂
  rw [thm27_1 hg hS hp₀ m₁ m₂ hp₁ hp₂ hN₁ hN₂]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · have e := h x
    rw [hG₁, hG₂] at e
    exact OnePoint.coe_injective e
  · rw [hG₁, hG₂, h x]

/-- **Equal lifted coefficients give equivalent marked surfaces** (U11 + `s27v_equiv_iff_fSym`). -/
theorem s27v_equiv_of_liftCoeff [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {m₁ m₂ : MarkedRS S₀}
    (h : ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ m₁.marking z = s27u_liftCoeff p₀ m₂.marking z) :
    m₁.Equiv m₂ := by
  obtain ⟨k₁, hk₁0, hk₁1, hμ₁⟩ := s27v_liftCoeff_bound hp₀ m₁
  obtain ⟨k₂, hk₂0, hk₂1, hμ₂⟩ := s27v_liftCoeff_bound hp₀ m₂
  refine (s27v_equiv_iff_fSym hg hS hp₀ m₁ m₂).2 fun x => ?_
  rw [s27u_fSym_congr_ae hk₁0 hk₁1 hμ₁ hk₂0 hk₂1 hμ₂ h]

/-- **Fricke coordinates are class invariants** (from `thm27_fricke_bijection`, ⇒). -/
theorem s27v_fricke_eq_of_equiv [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) {m₁ m₂ : MarkedRS S₀}
    (h : m₁.Equiv m₂) {c₁ c₂ : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} (hc₁ : IsFrickeCoords p₀ G m₁ c₁)
    (hc₂ : IsFrickeCoords p₀ G m₂ c₂) : c₁ = c₂ := by
  exact ((thm27_fricke_bijection hg hS hp₀ G).2 m₁ m₂ c₁ c₂ hc₁ hc₂).1 h

/-- **The base point `[S₀, id]`**: its Fricke coordinates are those of `G` (normalized lift `id`, induced system `G`;
a copy of scout E's probe `h27e_base_isFrickeCoords`), and its lifted coefficient vanishes a.e. on `ℍ` (U3 with `K = 1`,
the identity being biholomorphic). -/
theorem s27v_base [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {g : ℕ} (G : StandardGenerators Γ₀ g) :
    IsFrickeCoords p₀ G ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ (frickeCoordinates G) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ (Homeomorph.refl S₀) z = 0 := by
  refine ⟨⟨Γ₀, p₀, Homeomorph.refl _, id, G, hp₀, ⟨fun τ => rfl, ⟨fun z hz => ?_, continuousOn_id,
    injOn_id _, image_id _⟩, rfl, rfl, rfl⟩, ⟨fun j => ⟨fun τ => rfl, fun τ => rfl⟩, fun τ => rfl,
    fun τ => rfl⟩, rfl⟩, ?_⟩
  · have hz' : 0 < z.im := hz
    simp [liftToC, hz']
  · have h1 : IsKQCRS (Homeomorph.refl S₀) 1 := (isKQCRS_one_iff _).2 isBiholomorphic_id
    have h2 := (s27u_liftCoeff_isBeltramiCoeff hp₀ h1).2
    filter_upwards [h2] with z hz
    rw [show ((1 : ℝ) - 1) / (1 + 1) = 0 by norm_num] at hz
    exact norm_le_zero_iff.1 hz

/-- **The path of Lemma 27.2** (proved glue; the statement of `lemma27_2_path`).  With `μ` the lifted coefficient of
`m`, `t ↦ [X^{t̄ μ}]` (`t̄ = max 0 (min t 1)`, [A1]/[A2] via `s27v_exists_marked`) is a family of marked surfaces whose
lifted coefficients depend continuously (pointwise, with the bound of `μ`) on `t`; its Fricke coordinates are
continuous (`s27v_fricke_tendsto`, sequentially), equal to those of `[S₀, id]` at `0` and of `m` at `1`
(`s27v_equiv_of_liftCoeff`, `s27v_base`). -/
theorem s27v_lemma27_2_path [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    (m : MarkedRS S₀) {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} (hc : IsFrickeCoords p₀ G m c) :
    ∃ path : ℝ → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ), ContinuousOn path (Icc 0 1) ∧
      path 1 = c ∧ path 0 = frickeCoordinates G ∧ ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ frickeSpace p₀ G := by
  obtain ⟨k₀, hk0, hk1, hμ⟩ := s27v_liftCoeff_bound hp₀ m
  have hΓ := s27u_liftCoeff_isGammaCompatible hp₀ m.marking
  set μ : ℂ → ℂ := s27u_liftCoeff p₀ m.marking with hμdef
  -- the clamped parameter
  set cl : ℝ → ℝ := fun t => max 0 (min t 1) with hcldef
  have hcl0 : ∀ t, 0 ≤ cl t := fun t => le_max_left _ _
  have hcl1 : ∀ t, cl t ≤ 1 := fun t => max_le zero_le_one (min_le_right _ _)
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  -- the family `t̄ μ` in `M(Γ₀)`
  have hμt : ∀ t, IsBeltramiCoeff (fun z => (cl t : ℂ) * μ z) upperHalf k₀ := fun t => by
    refine ⟨aestronglyMeasurable_const.mul hμ.1, ?_⟩
    filter_upwards [hμ.2] with z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcl0 t)]
    calc cl t * ‖μ z‖ ≤ 1 * k₀ := mul_le_mul (hcl1 t) hz (norm_nonneg _) zero_le_one
      _ = k₀ := one_mul k₀
  have hΓt : ∀ t, IsGammaCompatible Γ₀ (fun z => (cl t : ℂ) * μ z) := fun t γ hγ => by
    filter_upwards [hΓ γ hγ] with z hz
    rw [hz, mul_assoc]
  choose M hM using fun t => s27v_exists_marked hp₀ hk0 hk1 (hμt t) (hΓt t)
  choose P hP using fun t => (thm27_fricke_bijection hg hS hp₀ G).1 (M t)
  have hMμ : ∀ t, IsBeltramiCoeff (s27u_liftCoeff p₀ (M t).marking) upperHalf k₀ := fun t => by
    refine ⟨(hμt t).1.congr ((ae_eq_comm).1 (hM t)), ?_⟩
    filter_upwards [(hμt t).2, hM t] with z h1 h2
    rw [h2]
    exact h1
  refine ⟨P, ?_, ?_, ?_, fun t _ => ⟨M t, hP t⟩⟩
  · -- continuity, sequentially (`s27v_fricke_tendsto`)
    refine (continuous_iff_seqContinuous.2 fun {u t₀} hu => ?_).continuousOn
    refine s27v_fricke_tendsto hg hS hp₀ G hk0 hk1 (fun n => hMμ (u n)) (hMμ t₀) ?_ (fun n => hP (u n)) (hP t₀)
    filter_upwards [ae_all_iff.2 fun n => hM (u n), hM t₀] with z h1 h2
    rw [h2]
    simp only [h1]
    have hcu : Tendsto (fun n => cl (u n)) atTop (𝓝 (cl t₀)) := (hclc.tendsto t₀).comp hu
    exact ((Complex.continuous_ofReal.tendsto _).comp hcu).mul_const _
  · -- `path 1 = c`: `M 1` has the lifted coefficient of `m`
    have hcl : cl 1 = 1 := by simp [hcldef]
    have hE : (M 1).Equiv m := s27v_equiv_of_liftCoeff hg hS hp₀ (by
      filter_upwards [hM 1] with z hz
      rw [hz, hcl, Complex.ofReal_one, one_mul])
    exact s27v_fricke_eq_of_equiv hg hS hp₀ G hE (hP 1) hc
  · -- `path 0 = frickeCoordinates G`: `M 0` has the lifted coefficient `0` of the base point
    have hcl : cl 0 = 0 := by simp [hcldef]
    obtain ⟨hb, hb0⟩ := s27v_base hp₀ G
    have hE : (M 0).Equiv ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ := s27v_equiv_of_liftCoeff hg hS hp₀ (by
      filter_upwards [hM 0, hb0] with z hz hz0
      rw [hz, hcl, Complex.ofReal_zero, zero_mul]
      exact hz0.symm)
    exact s27v_fricke_eq_of_equiv hg hS hp₀ G hE (hP 0) hb

/-- **Lemma 27.2** (proved glue; the statement of `lemma27_2_connected`): `F(S₀)` is path connected, every point being
joined to the base point `frickeCoordinates G` by the path of `s27v_lemma27_2_path` (`JoinedIn.ofLine`). -/
theorem s27v_lemma27_2_connected [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    IsPathConnected (frickeSpace p₀ G) := by
  refine ⟨frickeCoordinates G, ⟨_, (s27v_base hp₀ G).1⟩, fun {c} hc => ?_⟩
  obtain ⟨m, hm⟩ := hc
  obtain ⟨path, hcont, h1, h0, hmem⟩ := s27v_lemma27_2_path hg hS hp₀ G m hm
  exact JoinedIn.ofLine hcont h0 h1 (by rintro _ ⟨t, ht, rfl⟩; exact hmem t ht)

/-- **[C1, stub] The lifted coefficient of a Teichmüller map is `k ψ̄/|ψ|`** (E2's S3,
`utm_x_liftCoeff_teichmullerMap`, UTM l.2953, restated on `s27u_liftCoeff`), with `ψ = utm_liftQD q p₀ ≠ 0` a.e.

*Why true.*  Proved in UTM (axiom-clean): `utm_x1_lift_pointwise` (UTM l.2901) gives, at `z ∈ ℍ` with `ψ(z) ≠ 0`, the
chart-read dilatation `k ψ̄(z)/|ψ(z)|` (near `z` the map is `L_f ∘ h`, `h = φ_x ∘ p̂₀` a local biholomorphism,
`s23_dilatation_comp_right`, `s26b_pointwise`, `utm_liftQD_local`), which is `s27u_liftCoeff p₀ f z`
(`s27u_liftCoeff_of_mem`); the zeros of `ψ` in `ℍ` are countable (`utm_x1_liftQD_zeros_countable`, UTM l.2878: `ψ` is
holomorphic on `ℍ` and `≢ 0`).  The truth probe `T3_truth_probe.lean` derives this exact statement from the installed
UTM.

*Route.*  Either (MOVE, see `T3_AUDIT.md`) move `utm_pext`, `utm_liftQD`, `utm_a_*`, `utm_liftQD_local`,
`utm_liftQD_differentiableOn`, `utm_liftQD_ne`, `utm_x1_liftQD_zeros_countable`, `utm_x1_lift_pointwise`,
`utm_x_tcoeff` (UTM l.423–582, 2715, 2878–2951, ≈ 0.25k lines, inputs S23/S26 only) above this block and prove the stub
in ≈ 20 lines; or copy them here under the prefix `s27v_`.

*Walls.*  None (a local computation in charts).

*Estimate.*  0.02–0.05k after the MOVE; 0.25–0.4k as a copy. -/
theorem s27v_liftCoeff_teichmullerMap [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    ∀ᵐ z ∂(volume.restrict upperHalf), utm_liftQD q p₀ z ≠ 0 ∧
      s27u_liftCoeff p₀ f z = (k : ℂ) * conj (utm_liftQD q p₀ z) / (‖utm_liftQD q p₀ z‖ : ℂ) := by
  have hZ0 : volume {τ | τ ∈ upperHalf ∧ utm_liftQD q p₀ τ = 0} = 0 :=
    (utm_x1_liftQD_zeros_countable hf.initial hf.initial_ne hp₀).measure_zero _
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0)] with τ hτ hτZ
  have hψ : utm_liftQD q p₀ τ ≠ 0 := fun h0 => hτZ ⟨hτ, h0⟩
  refine ⟨hψ, ?_⟩
  rw [s27u_liftCoeff_of_mem p₀ f hτ]
  exact (utm_x1_lift_pointwise hp₀ hf hτ hψ).symm

/-- The lifted coefficient of a Teichmüller deformation with constant `k` is bounded by `k`
(U3 with `K = (1 + k)/(1 - k)`, `s26u_isKQCRS`). -/
theorem s27v_liftCoeff_deformation_bound [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier} {q' : X.carrier → ℂ → ℂ}
    (hT : IsTeichDeformation q k X e q') : IsBeltramiCoeff (s27u_liftCoeff p₀ e) upperHalf k := by
  have h := s27u_liftCoeff_isBeltramiCoeff hp₀ (s26u_isKQCRS hT)
  have h1 : 0 < 1 - k := by linarith [hT.k_lt_one]
  have e1 : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) = k := by
    field_simp
    ring
  rwa [e1] at h

/-- **(27.16)–(27.17)** (proved glue; the statement of `eq27_17_lifts_converge`).  The deformation surfaces `S_{qₙ,kₙ}`,
`S_{q,k}` are equivalent to `mₙ`, `m` (same Fricke coordinates, `thm27_fricke_bijection`); their lifted coefficients
are `kₙ ψ̄ₙ/|ψₙ|`, `k ψ̄/|ψ|` a.e. ([C1]), and `ψₙ → ψ` pointwise (`qₙ → q` pointwise, same charts), so they converge
a.e. (`ψ ≠ 0` a.e.), with the common bound `(1 + k)/2` along a tail (`kₙ → k < 1`); `s27v_fricke_tendsto` concludes. -/
theorem s27v_eq27_17 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {qn : ℕ → S₀ → ℂ → ℂ} {q : S₀ → ℂ → ℂ} (hqn : ∀ n, IsHolQuadDiff (qn n)) (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) {kn : ℕ → ℝ} {k : ℝ}
    (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1) (hk : 0 < k) (hk' : k < 1) (hkconv : Tendsto kn atTop (𝓝 k))
    {mn : ℕ → MarkedRS S₀} {m : MarkedRS S₀} (hmn : ∀ n, IsDeformationPoint (qn n) (kn n) (Quot.mk _ (mn n)))
    (hm : IsDeformationPoint q k (Quot.mk _ m)) {cn : ℕ → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} (hcn : ∀ n, IsFrickeCoords p₀ G (mn n) (cn n))
    (hc : IsFrickeCoords p₀ G m c) : Tendsto cn atTop (𝓝 c) := by
  have _ := hqn
  have _ := hq
  have _ := hne
  have _ := hkn
  have _ := hk
  choose X e hqc q' hT hpn using hmn
  obtain ⟨X₀, e₀, hqc₀, q'₀, hT₀, hp⟩ := hm
  -- the deformation surfaces have the Fricke coordinates of `mₙ`, `m`
  have hbij := thm27_fricke_bijection hg hS hp₀ G
  choose c' hc' using fun n => hbij.1 ⟨X n, e n, hqc n⟩
  obtain ⟨c'₀, hc'₀⟩ := hbij.1 ⟨X₀, e₀, hqc₀⟩
  have hcn' : ∀ n, cn n = c' n := fun n => s27v_fricke_eq_of_equiv hg hS hp₀ G
    (markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact (hpn n))) (hcn n) (hc' n)
  have hc0 : c = c'₀ := s27v_fricke_eq_of_equiv hg hS hp₀ G
    (markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact hp)) hc hc'₀
  -- a tail on which `kₙ < (1 + k)/2`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hkconv.eventually (gt_mem_nhds (show k < (1 + k) / 2 by linarith)))
  have hk2 : (1 + k) / 2 < 1 := by linarith
  have hk20 : 0 ≤ (1 + k) / 2 := by linarith
  -- the lifted differentials converge pointwise
  have hψ : ∀ z, Tendsto (fun n => utm_liftQD (qn n) p₀ z) atTop (𝓝 (utm_liftQD q p₀ z)) := fun z =>
    (hconv _ _).mul_const _
  have htail : Tendsto (fun n => c' (n + N)) atTop (𝓝 c'₀) := by
    refine s27v_fricke_tendsto hg hS hp₀ G (mn := fun n => ⟨X (n + N), e (n + N), hqc (n + N)⟩)
      (m := ⟨X₀, e₀, hqc₀⟩) hk20 hk2 (fun n => ?_) ?_ ?_ (fun n => hc' (n + N)) hc'₀
    · exact s27v_isBeltramiCoeff_mono (s27v_liftCoeff_deformation_bound hp₀ (hT (n + N)))
        (hN (n + N) (Nat.le_add_left N n)).le
    · exact s27v_isBeltramiCoeff_mono (s27v_liftCoeff_deformation_bound hp₀ hT₀) (by linarith)
    · filter_upwards [ae_all_iff.2 fun n => s27v_liftCoeff_teichmullerMap hp₀
          (teichDeformation_isTeichmullerMap (hT (n + N))),
        s27v_liftCoeff_teichmullerMap hp₀ (teichDeformation_isTeichmullerMap hT₀)] with z hzn hz
      show Tendsto (fun n => s27u_liftCoeff p₀ (e (n + N)) z) atTop (𝓝 (s27u_liftCoeff p₀ e₀ z))
      rw [hz.2]
      refine Tendsto.congr (fun n => ((hzn n).2).symm) ?_
      have hψN : Tendsto (fun n => utm_liftQD (qn (n + N)) p₀ z) atTop (𝓝 (utm_liftQD q p₀ z)) :=
        (hψ z).comp (tendsto_add_atTop_nat N)
      have hkN : Tendsto (fun n => kn (n + N)) atTop (𝓝 k) := hkconv.comp (tendsto_add_atTop_nat N)
      refine (((Complex.continuous_ofReal.tendsto k).comp hkN).mul
        ((Complex.continuous_conj.tendsto _).comp hψN)).div
        ((Complex.continuous_ofReal.tendsto _).comp hψN.norm) ?_
      exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz.1)
  rw [hc0]
  exact ((tendsto_add_atTop_iff_nat N).1 htail).congr fun n => (hcn' n).symm

/-- (27.16)–(27.17): if `qₙ → q` and `kₙ → k` (`k ∈ (0, 1)`), the normalized lifts `f̃ₙ` of the
deformation maps `fₙ : S₀ → S_{qₙ,kₙ}`, whose complex dilatations are `kₙ φ̄ₙ/|φₙ|`, converge to the
normalized lift `f̃` of `f : S₀ → S_{q,k}` (continuous dependence of quasiconformal maps on the
complex dilatation), and the induced generators converge: `γⱼ(fₙ) → γⱼ(f)`, `δⱼ(fₙ) → δⱼ(f)`. -/
theorem eq27_17_lifts_converge [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {qn : ℕ → S₀ → ℂ → ℂ} {q : S₀ → ℂ → ℂ} (hqn : ∀ n, IsHolQuadDiff (qn n)) (hq : IsHolQuadDiff q)
    (hne : q ≠ 0) (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) {kn : ℕ → ℝ} {k : ℝ}
    (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1) (hk : 0 < k) (hk' : k < 1) (hkconv : Tendsto kn atTop (𝓝 k))
    {mn : ℕ → MarkedRS S₀} {m : MarkedRS S₀} (hmn : ∀ n, IsDeformationPoint (qn n) (kn n) (Quot.mk _ (mn n)))
    (hm : IsDeformationPoint q k (Quot.mk _ m)) {cn : ℕ → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} (hcn : ∀ n, IsFrickeCoords p₀ G (mn n) (cn n))
    (hc : IsFrickeCoords p₀ G m c) : Tendsto cn atTop (𝓝 c) := by
  exact s27v_eq27_17 hg hS hp₀ G hqn hq hne hconv hkn hk hk' hkconv hmn hm hcn hc

/-- **The base point is no deformation point with `k > 0`** (the case `Ψ(0) = Ψ(v)`, `v ≠ 0`, of the injectivity
in Lemma 27.1).  If a biholomorphic `c : S₀ → X` is homotopic to the Teichmüller deformation map
`e' : S₀ → S_{q,k}`, then `k > 0` is impossible: `e'⁻¹` is a Teichmüller map with constant `k` ([S7a],
`utm_x_teichmullerMap_symm`) homotopic to the conformal `c⁻¹`, so `thm26_2_uniqueness_of_uniformization` on the
uniformized target `S₀ = ℍ/Γ₀` gives `(1 + k)/(1 - k) ≤ K[c⁻¹] ≤ 1`. -/
theorem s27w_not_base_equiv [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {q : S₀ → ℂ → ℂ} {k : ℝ} {X : ClosedRS.{u}}
    {e' : S₀ ≃ₜ X.carrier} {q' : X.carrier → ℂ → ℂ} (hT : IsTeichDeformation q k X e' q') (hk : 0 < k)
    {c : S₀ ≃ₜ X.carrier} (hc : IsBiholomorphic c)
    (hhom : ContinuousMap.Homotopic (c : C(S₀, X.carrier)) (e' : C(S₀, X.carrier)))
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : False := by
  have hX : HasGenus X.carrier g := hasGenus_of_homeomorph hS e'
  have hi := utm_x_teichmullerMap_symm (teichDeformation_isTeichmullerMap hT)
  have hc1 : IsKQCRS c.symm 1 := (isKQCRS_one_iff c.symm).2 hc.homeomorph_symm
  have hhom' : ContinuousMap.Homotopic ((e'.symm : X.carrier ≃ₜ S₀) : C(X.carrier, S₀))
      ((c.symm : X.carrier ≃ₜ S₀) : C(X.carrier, S₀)) := by
    have h1 := ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (c.symm : C(X.carrier, S₀))) hhom)
      (ContinuousMap.Homotopic.refl (e'.symm : C(X.carrier, S₀)))
    have ea : ((c.symm : C(X.carrier, S₀)).comp (c : C(S₀, X.carrier))).comp (e'.symm : C(X.carrier, S₀)) =
        (e'.symm : C(X.carrier, S₀)) := by
      ext x
      simp
    have eb : ((c.symm : C(X.carrier, S₀)).comp (e' : C(S₀, X.carrier))).comp (e'.symm : C(X.carrier, S₀)) =
        (c.symm : C(X.carrier, S₀)) := by
      ext x
      simp
    rw [ea, eb] at h1
    exact h1
  obtain ⟨hineq, -⟩ := thm26_2_uniqueness_of_uniformization hg hX hS hi ⟨1, hc1⟩ hhom' hp₀
  have hle : maxDilatationRS c.symm ≤ 1 := by simpa using maxDilatationRS_le hc1
  have h1k : 0 < 1 - k := by linarith [hT.k_lt_one]
  have hK : 1 < (1 + k) / (1 - k) := (one_lt_div h1k).2 (by linarith)
  have h2 := hineq.trans hle
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h2
  linarith

/-- **Lemma 27.1**: the composite `Ψ ∘ Φ : T̃(S₀) → F(S₀)` is a continuous injective map (with
`T̃(S₀)` the open unit ball of `ℝ^{6g-6}` via `(q, k) ↦ k · e(q)`, `‖e(q)‖ = 1`). -/
theorem lemma27_1_continuous_injective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ),
      ContinuousOn Ψ (ball 0 1) ∧ InjOn Ψ (ball 0 1) ∧
      ∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), ‖e q‖ = 1 → 0 < k → k < 1 →
        ∀ m : MarkedRS S₀, IsDeformationPoint q k (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ (k • e q)) := by
  have hbij := thm27_fricke_bijection hg hS hp₀ G
  -- a marked surface for every `v`: the deformation `S_{e⁻¹(v/‖v‖), ‖v‖}` for `0 < ‖v‖ < 1`, `[S₀, id]` at `0`
  have hMex : ∀ v : EuclideanSpace ℝ (Fin (6 * g - 6)), ∃ m : MarkedRS S₀,
      (v = 0 → m = ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩) ∧
      (v ≠ 0 → ‖v‖ < 1 → ∃ q' : m.X.carrier → ℂ → ℂ,
        IsTeichDeformation (e.symm (‖v‖⁻¹ • v) : S₀ → ℂ → ℂ) ‖v‖ m.X m.marking q') := by
    intro v
    by_cases hv : v ≠ 0 ∧ ‖v‖ < 1
    · have hq0 : (e.symm (‖v‖⁻¹ • v) : S₀ → ℂ → ℂ) ≠ 0 := by
        intro h0
        have h1 : e.symm (‖v‖⁻¹ • v) = 0 := Submodule.coe_eq_zero.1 h0
        rw [LinearEquiv.map_eq_zero_iff] at h1
        exact hv.1 ((smul_eq_zero.1 h1).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hv.1)))
      obtain ⟨X, e', q', hT⟩ := exists_teichDeformation (q := (e.symm (‖v‖⁻¹ • v) : S₀ → ℂ → ℂ))
        (e.symm (‖v‖⁻¹ • v)).2 hq0 (norm_nonneg v) hv.2
      exact ⟨⟨X, e', (teichDeformation_isTeichmullerMap hT).qc⟩, fun h => absurd h hv.1, fun _ _ => ⟨q', hT⟩⟩
    · exact ⟨⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩, fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
  choose M hM0 hMd using hMex
  choose Ψ hΨ using fun v => hbij.1 (M v)
  -- the lifted coefficient of `M v` is bounded by `‖v‖`
  have hbd : ∀ v : EuclideanSpace ℝ (Fin (6 * g - 6)), ‖v‖ < 1 →
      IsBeltramiCoeff (s27u_liftCoeff p₀ (M v).marking) upperHalf ‖v‖ := by
    intro v hv1
    by_cases hv0 : v = 0
    · subst hv0
      rw [hM0 0 rfl]
      have h1 : IsKQCRS (Homeomorph.refl S₀) 1 := (isKQCRS_one_iff _).2 isBiholomorphic_id
      exact s27v_isBeltramiCoeff_mono (s27u_liftCoeff_isBeltramiCoeff hp₀ h1) (by rw [norm_zero]; norm_num)
    · obtain ⟨q', hT⟩ := hMd v hv0 hv1
      exact s27v_liftCoeff_deformation_bound hp₀ hT
  -- `v` is recovered from `e⁻¹(v/‖v‖)` and `‖v‖`
  have hrec : ∀ w : EuclideanSpace ℝ (Fin (6 * g - 6)), w ≠ 0 →
      ‖e (e.symm (‖w‖⁻¹ • w))‖ = 1 ∧ ‖w‖ • e (e.symm (‖w‖⁻¹ • w)) = w := by
    intro w hw
    have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    rw [LinearEquiv.apply_symm_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw', smul_smul,
      mul_inv_cancel₀ hw', one_smul]
    exact ⟨rfl, rfl⟩
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · -- continuity, sequentially
    intro v hv
    have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_nhds_iff_seq_tendsto.2 fun u hu => ?_
    by_cases hv0 : v = 0
    · -- at `0`: the lifted coefficients are bounded by `‖u n‖ → 0` (`s27v_fricke_tendsto`)
      subst hv0
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hu.eventually_mem (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))))
      have hN' : ∀ n, ‖u (n + N)‖ < 1 / 2 := fun n => mem_ball_zero_iff.1 (hN (n + N) (Nat.le_add_left N n))
      have hb0 : ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p₀ (M 0).marking z = 0 := by
        rw [hM0 0 rfl]
        exact (s27v_base hp₀ G).2
      have hae : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ n,
          ‖s27u_liftCoeff p₀ (M (u (n + N))).marking z‖ ≤ ‖u (n + N)‖ :=
        ae_all_iff.2 fun n => (hbd _ (by linarith [hN' n])).2
      have htail : Tendsto (fun n => Ψ (u (n + N))) atTop (𝓝 (Ψ 0)) := by
        refine s27v_fricke_tendsto hg hS hp₀ G (mn := fun n => M (u (n + N))) (m := M 0) (k := 1 / 2)
          (by norm_num) (by norm_num)
          (fun n => s27v_isBeltramiCoeff_mono (hbd _ (by linarith [hN' n])) (hN' n).le)
          (s27v_isBeltramiCoeff_mono (hbd 0 (by rw [norm_zero]; norm_num)) (by rw [norm_zero]; norm_num)) ?_
          (fun n => hΨ (u (n + N))) (hΨ 0)
        filter_upwards [hae, hb0] with z hz hz0
        rw [hz0]
        have hn := (hu.comp (tendsto_add_atTop_nat N)).norm
        rw [norm_zero] at hn
        exact squeeze_zero_norm hz hn
      exact (tendsto_add_atTop_iff_nat N).1 htail
    · -- at `v ≠ 0`: (27.16)–(27.17), `eq27_17_lifts_converge`
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((hu.eventually_ne hv0).and (hu.eventually_mem (isOpen_ball.mem_nhds hv)))
      have hN' : ∀ n, u (n + N) ≠ 0 ∧ ‖u (n + N)‖ < 1 := fun n =>
        ⟨(hN (n + N) (Nat.le_add_left N n)).1, mem_ball_zero_iff.1 (hN (n + N) (Nat.le_add_left N n)).2⟩
      have huN : Tendsto (fun n => u (n + N)) atTop (𝓝 v) := hu.comp (tendsto_add_atTop_nat N)
      choose q'n hTn using fun n => hMd (u (n + N)) (hN' n).1 (hN' n).2
      obtain ⟨q'v, hTv⟩ := hMd v hv0 hv1
      have hdir : Tendsto (fun n => ‖u (n + N)‖⁻¹ • u (n + N)) atTop (𝓝 (‖v‖⁻¹ • v)) :=
        (huN.norm.inv₀ (norm_ne_zero_iff.2 hv0)).smul huN
      have hconv : ∀ x z, Tendsto (fun n => (e.symm (‖u (n + N)‖⁻¹ • u (n + N)) : S₀ → ℂ → ℂ) x z) atTop
          (𝓝 ((e.symm (‖v‖⁻¹ • v) : S₀ → ℂ → ℂ) x z)) := by
        intro x z
        let L : EuclideanSpace ℝ (Fin (6 * g - 6)) →ₗ[ℝ] ℂ :=
          (LinearMap.proj z).comp ((LinearMap.proj x).comp
            (((holQuadDiffSubmodule S₀).restrictScalars ℝ).subtype.comp e.symm.toLinearMap))
        exact (L.continuous_of_finiteDimensional.tendsto _).comp hdir
      have htail := eq27_17_lifts_converge hg hS hp₀ G
        (qn := fun n => (e.symm (‖u (n + N)‖⁻¹ • u (n + N)) : S₀ → ℂ → ℂ))
        (q := (e.symm (‖v‖⁻¹ • v) : S₀ → ℂ → ℂ)) (kn := fun n => ‖u (n + N)‖) (k := ‖v‖)
        (mn := fun n => M (u (n + N))) (m := M v)
        (fun n => (e.symm (‖u (n + N)‖⁻¹ • u (n + N))).2) (e.symm (‖v‖⁻¹ • v)).2 hTv.initial_ne hconv
        (fun n => ⟨norm_nonneg _, (hN' n).2⟩) (norm_pos_iff.2 hv0) hv1 huN.norm
        (fun n => ⟨(M (u (n + N))).X, (M (u (n + N))).marking, (M (u (n + N))).qc, q'n n, hTn n, rfl⟩)
        ⟨(M v).X, (M v).marking, (M v).qc, q'v, hTv, rfl⟩ (fun n => hΨ (u (n + N))) (hΨ v)
      exact (tendsto_add_atTop_iff_nat N).1 htail
  · -- injectivity: equal coordinates give equivalent marked surfaces (`thm27_fricke_bijection`)
    intro v hv v' hv' hΨv
    have hE : (M v).Equiv (M v') := (hbij.2 (M v) (M v') (Ψ v) (Ψ v') (hΨ v) (hΨ v')).2 hΨv
    have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
    have hv1' : ‖v'‖ < 1 := mem_ball_zero_iff.1 hv'
    by_cases hv0 : v = 0 <;> by_cases hv0' : v' = 0
    · rw [hv0, hv0']
    · exfalso
      rw [hv0, hM0 0 rfl] at hE
      obtain ⟨q', hT⟩ := hMd v' hv0' hv1'
      obtain ⟨c, hc, hhom⟩ := hE
      exact s27w_not_base_equiv hg hS hT (norm_pos_iff.2 hv0') (hc.comp isBiholomorphic_id) hhom hp₀
    · exfalso
      rw [hv0', hM0 0 rfl] at hE
      obtain ⟨q', hT⟩ := hMd v hv0 hv1
      obtain ⟨c, hc, hhom⟩ := markedRS_equiv_equivalence.symm hE
      exact s27w_not_base_equiv hg hS hT (norm_pos_iff.2 hv0) (hc.comp isBiholomorphic_id) hhom hp₀
    · obtain ⟨q', hT⟩ := hMd v hv0 hv1
      obtain ⟨q'', hT'⟩ := hMd v' hv0' hv1'
      obtain ⟨hk, hq⟩ := s27w_injective_core hg hS e (hrec v hv0).1 (hrec v' hv0').1 (norm_pos_iff.2 hv0) hv1
        (norm_pos_iff.2 hv0') hv1' ⟨(M v).X, (M v).marking, (M v).qc, q', hT, rfl⟩
        ⟨(M v').X, (M v').marking, (M v').qc, q'', hT', Quot.sound hE⟩ hp₀
      calc v = ‖v‖ • e (e.symm (‖v‖⁻¹ • v)) := (hrec v hv0).2.symm
        _ = ‖v'‖ • e (e.symm (‖v'‖⁻¹ • v')) := by rw [hq, hk]
        _ = v' := (hrec v' hv0').2
  · -- the coordinate clause: `Φ` is well defined (`isDeformationPoint_unique`) and Fricke coordinates are class
    -- invariants
    intro q k hq hk hk1 m hm
    set v := k • e q with hvdef
    have hvn : ‖v‖ = k := by rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos hk, hq, mul_one]
    have hv0 : v ≠ 0 := fun h => by rw [h, norm_zero] at hvn; linarith
    have hvq : e.symm (‖v‖⁻¹ • v) = q := by
      rw [hvn, hvdef, smul_smul, inv_mul_cancel₀ hk.ne', one_smul, LinearEquiv.symm_apply_apply]
    obtain ⟨q', hT⟩ := hMd v hv0 (by rw [hvn]; exact hk1)
    rw [hvq, hvn] at hT
    have hp : (Quot.mk _ (M v) : TeichSpace S₀) = Quot.mk _ m :=
      isDeformationPoint_unique hg hS ⟨(M v).X, (M v).marking, (M v).qc, q', hT, rfl⟩ hm
    have hE : (M v).Equiv m := markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact hp)
    obtain ⟨c, hc⟩ := hbij.1 m
    rwa [s27v_fricke_eq_of_equiv hg hS hp₀ G hE (hΨ v) hc]

/-- §27.2 (the proof of Lemma 27.2): the Beltrami coefficient `μ` of a normalized lift `f̃`
satisfies `μ(z) = μ(γ(z)) conj γ'(z)/γ'(z)` for `γ ∈ G₀`, and so does `μ_t = tμ`; the normalized
solutions `f̃_t` with dilatation `μ_t` are normalized lifts of quasiconformal maps
`f_t : S₀ → S_t = ℍ/G_t`, `G_t = f̃_t G₀ f̃_t⁻¹`, giving a path `t ↦ Ψ([S_t, f_t])` in `F(S₀)` from
`Ψ([S₀, id])` to `Ψ([S, f])`. -/
theorem lemma27_2_path [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    (m : MarkedRS S₀) {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)} (hc : IsFrickeCoords p₀ G m c) :
    ∃ path : ℝ → Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ), ContinuousOn path (Icc 0 1) ∧
      path 1 = c ∧ path 0 = frickeCoordinates G ∧ ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ frickeSpace p₀ G := by
  exact s27v_lemma27_2_path hg hS hp₀ G m hc

/-- **Lemma 27.2**: `F(S₀)` is (path) connected. -/
theorem lemma27_2_connected [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    IsPathConnected (frickeSpace p₀ G) := by
  exact s27v_lemma27_2_connected hg hS hp₀ G

/-- The image `Ψ ∘ Φ(T̃(S₀)) ⊆ F(S₀)`: the Fricke coordinates of the Teichmüller deformations. -/
def deformationImage {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) : Set (Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
  {c | ∃ (m : MarkedRS S₀) (q : S₀ → ℂ → ℂ) (k : ℝ), IsDeformationPoint q k (Quot.mk _ m) ∧
    IsFrickeCoords p₀ G m c}





/-- §27.2: the dilatation bound in the proof of Lemma 27.3: `K[f_t] ≤ (1 + t‖μ‖_∞)/(1 - t‖μ‖_∞) ≤ K[f]`
for `t ∈ [0, 1]`, so the Teichmüller deformation in the class of `(S_t, f_t)` has `k ≤ (K[f]-1)/(K[f]+1)`. -/
theorem lemma27_3_dilatation_bound [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (m : MarkedRS S₀) {q : S₀ → ℂ → ℂ} {k : ℝ}
    (h : IsDeformationPoint q k (Quot.mk _ m)) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS m.marking := by
  -- UTM's companion `lemma27_3_dilatation_bound_of_uniformization`, with the uniformization of the deformation
  -- surface `S_{q,k}` supplied by S22 (`s29_m_equiv_of_eq` inlined)
  obtain ⟨X, e, _hqc, _q', hT, hp⟩ := h
  obtain ⟨c, hc, hhom⟩ := (Equivalence.eqvGen_iff markedRS_equiv_equivalence).1 (Quot.eqvGen_exact hp)
  obtain ⟨hqcf, hle⟩ := s29_m_maxDil_conj_biholo m.qc (c₁ := Homeomorph.refl S₀) isBiholomorphic_id hc
  have h₁ : HasGenus X.carrier g := hasGenus_of_homeomorph hS e
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg h₁
  have hhom' : ContinuousMap.Homotopic (e : C(S₀, X.carrier))
      (((Homeomorph.refl S₀).trans (m.marking.trans c) : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier)) :=
    hhom.symm
  exact (thm26_2_uniqueness_of_uniformization hg hS h₁ (teichDeformation_isTeichmullerMap hT) hqcf hhom'
    hp₁).1.trans hle



/-! ### Helper moved up from `Lemmas/UniformizedTeichmuller` (s30t stage 0, leader decision): a uniformizing
group is Fuchsian (`utm_x2_isFuchsian`) -/

/-- **Proper discontinuity** (the content of [S6], placed before [S5], which uses it): for a uniformization `p` of
a Hausdorff surface and a compact `C ⊆ ℍ`, only finitely many `γ ∈ Γ` have `γ C ∩ C ≠ ∅`.  An injective sequence
`γₙ` with `γₙ cₙ ∈ C` has a subsequence with `cₙ → c`, `γₙ cₙ → c'`; `p c = p c'` gives `c' = g c`, and for large
`n` the points `cₙ`, `g⁻¹ γₙ cₙ` of one fibre lie in a sheet around `c`, so `g⁻¹ γₙ = ±1` (`ActsFreely`). -/
theorem utm_x2_isFuchsian {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    IsFuchsian Γ := by
  intro C hC
  by_contra hinf
  have hfree := s27g_actsFreely hp
  let e := Set.Infinite.natEmbedding _ hinf
  set γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun n => (e n : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    with hγs
  have hγinj : Function.Injective γs := fun m n h => e.injective (Subtype.ext h)
  have hγΓ : ∀ n, γs n ∈ Γ := fun n => (e n).2.1
  have hex : ∀ n, ∃ c ∈ C, γs n • c ∈ C := by
    intro n
    obtain ⟨_, ⟨c, hc, rfl⟩, hy⟩ := (e n).2.2
    exact ⟨c, hc, hy⟩
  choose c hcC hγcC using hex
  have hpair : ∀ n, (c n, γs n • c n) ∈ C ×ˢ C := fun n => ⟨hcC n, hγcC n⟩
  obtain ⟨⟨a, a'⟩, -, φ, hφ, hlim⟩ := (hC.prod hC).tendsto_subseq hpair
  have h1 : Tendsto (fun k => c (φ k)) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun k => γs (φ k) • c (φ k)) atTop (𝓝 a') := (continuous_snd.tendsto _).comp hlim
  have hpfib : ∀ n, p (γs n • c n) = p (c n) := fun n =>
    ((hp.2.2.2 (c n) (γs n • c n)).2 ⟨γs n, hγΓ n, rfl⟩).symm
  have hpa : p a = p a' := by
    have t1 : Tendsto (fun k => p (c (φ k))) atTop (𝓝 (p a)) := (hp.1.continuous.tendsto a).comp h1
    have t2 : Tendsto (fun k => p (γs (φ k) • c (φ k))) atTop (𝓝 (p a')) :=
      (hp.1.continuous.tendsto a').comp h2
    simp only [hpfib] at t2
    exact tendsto_nhds_unique t1 t2
  obtain ⟨g, hgΓ, hga⟩ := (hp.2.2.2 a a').1 hpa
  have h3 : Tendsto (fun k => (g⁻¹ * γs (φ k)) • c (φ k)) atTop (𝓝 a) := by
    have h := ((continuous_const_smul g⁻¹).tendsto a').comp h2
    rw [← hga, inv_smul_smul] at h
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, mul_smul]
  obtain ⟨E, haE, hpE⟩ := hp.1.isLocalHomeomorph a
  have hEn : E.source ∈ 𝓝 a := E.open_source.mem_nhds haE
  have hev : ∀ᶠ k in atTop, γs (φ k) = g ∨ γs (φ k) = g * -1 := by
    filter_upwards [h1 hEn, h3 hEn] with k hk1 hk3
    have hmem : g⁻¹ * γs (φ k) ∈ Γ := Γ.mul_mem (Γ.inv_mem hgΓ) (hγΓ _)
    have hpeq : p ((g⁻¹ * γs (φ k)) • c (φ k)) = p (c (φ k)) :=
      ((hp.2.2.2 (c (φ k)) _).2 ⟨_, hmem, rfl⟩).symm
    rw [hpE] at hpeq
    have hfix : (g⁻¹ * γs (φ k)) • c (φ k) = c (φ k) := E.injOn hk3 hk1 hpeq
    rcases hfree _ hmem _ hfix with h | h
    · exact Or.inl (inv_mul_eq_one.1 h).symm
    · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hinj : Function.Injective fun k => γs (φ (k + N)) := fun m n h =>
    add_right_cancel (hφ.injective (hγinj h))
  have hmem : ∀ k, γs (φ (k + N)) ∈ ({g, g * -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := fun k => by
    rcases hN (k + N) (Nat.le_add_left N k) with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact Set.infinite_of_injective_forall_mem hinj hmem (Set.toFinite _)

end LiZhongQC
