import LiZhongQC.Lemmas.SchottkyOneCellSVK
import LiZhongQC.Lemmas.SchottkyClosedSurface9
import LiZhongQC.Lemmas.SchottkyClosedSurface2
import LiZhongQC.Lemmas.SchottkyCircleFundamental

universe u

namespace LiZhongQC

open Set Metric Topology unitInterval DifferentialGeometry.Topology.VanKampen

/-- The one-cell pushout, with the quotient map recorded. -/
theorem s78dg_pushoutI_one_trivial' {G : Bool → Type*} [∀ b, Group (G b)] {H : Type*} [Group H]
    (φ : ∀ b, H →* G b) [Subsingleton (G true)] :
    ∃ T : Monoid.PushoutI φ ≃*
      (G false ⧸ Subgroup.normalClosure ((φ false).range : Set (G false))),
      ∀ g, T (Monoid.PushoutI.of false g) = QuotientGroup.mk g := by
  let N : Subgroup (G false) := Subgroup.normalClosure ((φ false).range : Set (G false))
  have hN : ∀ h : H, φ false h ∈ N := fun h =>
    Subgroup.subset_normalClosure ⟨h, rfl⟩
  have hof : ∀ h : H, (Monoid.PushoutI.of false (φ false h) : Monoid.PushoutI φ) = 1 := by
    intro h
    rw [Monoid.PushoutI.of_apply_eq_base, ← Monoid.PushoutI.of_apply_eq_base (φ := φ) true,
      Subsingleton.elim (φ true h) 1, map_one]
  let f : ∀ b, G b →* (G false ⧸ N) := by
    intro b
    cases b
    · exact QuotientGroup.mk' N
    · exact 1
  let k : H →* (G false ⧸ N) := (QuotientGroup.mk' N).comp (φ false)
  have hf : ∀ b, (f b).comp (φ b) = k := by
    intro b
    cases b
    · rfl
    · ext h
      change (1 : G false ⧸ N) = QuotientGroup.mk (φ false h)
      exact ((QuotientGroup.eq_one_iff _).2 (hN h)).symm
  let T : Monoid.PushoutI φ →* (G false ⧸ N) := Monoid.PushoutI.lift f k hf
  have hker : N ≤ (Monoid.PushoutI.of false : G false →* Monoid.PushoutI φ).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨h, rfl⟩
    exact hof h
  let S : (G false ⧸ N) →* Monoid.PushoutI φ :=
    QuotientGroup.lift N (Monoid.PushoutI.of false) (fun x hx => hker hx)
  have hTS : T.comp S = MonoidHom.id _ := by
    apply QuotientGroup.monoidHom_ext
    ext g
    simp [S, T, f]
  have hST : S.comp T = MonoidHom.id _ := by
    apply Monoid.PushoutI.hom_ext
    · intro b
      cases b
      · ext g
        simp [S, T, f]
      · ext g
        rw [Subsingleton.elim g 1]
        simp [S, T, f]
    · ext h
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [← Monoid.PushoutI.of_apply_eq_base (φ := φ) false]
      simp [hof h]
  refine ⟨MonoidHom.toMulEquiv T S hST hTS, fun g => ?_⟩
  show T (Monoid.PushoutI.of false g) = _
  simp only [T]
  rw [Monoid.PushoutI.lift_of]
  rfl


/-- **Van Kampen with a simply connected piece, kernel form.**  For open path-connected `U`, `V`
covering `X` with `U ∩ V` path-connected and `V` simply connected, `π₁(U) → π₁(X)` is surjective and
its kernel is the normal closure of the image of `π₁(U ∩ V)`. -/
theorem s78dg_svk_kernel {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace V] :
    Function.Surjective (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom ∧
      ∀ g, (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g = 1 ↔
        g ∈ Subgroup.normalClosure
          ((fundamentalGroupAmalgamation U V x₀ hx₀ false).range :
            Set (fundamentalGroupFactor U V x₀ hx₀ false)) := by
  have : Subsingleton (fundamentalGroupFactor U V x₀ hx₀ true) :=
    inferInstanceAs (Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)))
  obtain ⟨T, hT⟩ := s78dg_pushoutI_one_trivial' (fundamentalGroupAmalgamation U V x₀ hx₀)
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀
  have hcomp : ∀ g, e (Monoid.PushoutI.of false g) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g := fun g =>
    DFunLike.congr_fun (fundamentalGroupEquivAmalgamatedProduct_comp_left U V hU hV hcover x₀ hx₀) g
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨g0, hg0⟩ := QuotientGroup.mk_surjective (T (e.symm x))
    refine ⟨g0, ?_⟩
    have h1 : Monoid.PushoutI.of false g0 = e.symm x := T.injective (by rw [hT, hg0])
    rw [← hcomp, h1]
    exact e.apply_symm_apply x
  · intro g
    rw [← hcomp]
    constructor
    · intro h
      have h1 : Monoid.PushoutI.of false g = 1 := e.injective (by rw [h, map_one])
      have h2 := congrArg T h1
      rw [hT, map_one] at h2
      exact (QuotientGroup.eq_one_iff g).1 h2
    · intro hg
      have h3 : (QuotientGroup.mk g : _ ⧸ Subgroup.normalClosure
          ((fundamentalGroupAmalgamation U V x₀ hx₀ false).range :
            Set (fundamentalGroupFactor U V x₀ hx₀ false))) = 1 :=
        (QuotientGroup.eq_one_iff g).2 hg
      rw [← hT] at h3
      have h4 : Monoid.PushoutI.of false g = 1 := T.injective (by rw [h3, map_one])
      rw [h4, map_one]

/-- Kernel of a composite of two quotient maps, the second killing one more normal generator. -/
theorem s78dg_ker_comp {G G1 G2 : Type*} [Group G] [Group G1] [Group G2]
    (π : G →* G1) (ι : G1 →* G2) (S : Set G) (t : G)
    (hπ : Function.Surjective π) (hker : ∀ g, π g = 1 ↔ g ∈ Subgroup.normalClosure S)
    (hι : ∀ h, ι h = 1 ↔ h ∈ Subgroup.normalClosure ({π t} : Set G1)) :
    ∀ g, ι (π g) = 1 ↔ g ∈ Subgroup.normalClosure (insert t S) := by
  intro g
  constructor
  · intro h
    have h1 : π g ∈ Subgroup.normalClosure ({π t} : Set G1) := (hι _).1 h
    have h2 : Subgroup.normalClosure ({π t} : Set G1) =
        (Subgroup.normalClosure ({t} : Set G)).map π := by
      rw [Subgroup.map_normalClosure _ _ hπ, Set.image_singleton]
    rw [h2] at h1
    obtain ⟨u, hu, hug⟩ := h1
    have h3 : u⁻¹ * g ∈ Subgroup.normalClosure S := by
      rw [← hker, map_mul, map_inv, hug, inv_mul_cancel]
    have h4 : u ∈ Subgroup.normalClosure (insert t S) :=
      Subgroup.normalClosure_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hu
    have h5 : u⁻¹ * g ∈ Subgroup.normalClosure (insert t S) :=
      Subgroup.normalClosure_mono (Set.subset_insert _ _) h3
    have h6 := Subgroup.mul_mem _ h4 h5
    rwa [mul_inv_cancel_left] at h6
  · intro hg
    have hle : Subgroup.normalClosure (insert t S) ≤ (ι.comp π).ker := by
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rcases hx with rfl | hx
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, (hι _).2]
        exact Subgroup.subset_normalClosure rfl
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply,
          (hker x).2 (Subgroup.subset_normalClosure hx), map_one]
    exact hle hg

/-- **Kernel form of one-disc van Kampen, in a chart of `U`.**  Let `X = U ∪ V` (open, path
connected, `V` simply connected, `U ∩ V` path connected with cyclic `π₁` generated by `γ`) and
`A ≃ₜ U`.  If a loop `ℓ` of `A` corresponds to `γ`, then `π₁(A) → π₁(X)` is onto with kernel the
normal closure of `ℓ`. -/
theorem s78dg_svk_kernel_gen {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace V] {A : Type u} [TopologicalSpace A] (eA : A ≃ₜ ↥U) (a₀ : A)
    (hA : eA a₀ = leftBasepoint U x₀ hx₀.1)
    (γ : Path (overlapBasepoint U V x₀ hx₀) (overlapBasepoint U V x₀ hx₀))
    (hγ : ∀ z, z ∈ Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) (ℓ : Path a₀ a₀)
    (hℓ : ∀ t, ((eA (ℓ t) : ↥U) : X) = (((γ t : ↥(U ∩ V))) : X)) :
    Function.Surjective (FundamentalGroup.mapOfEq
      (⟨fun a => ((eA a : ↥U) : X), continuous_subtype_val.comp eA.continuous⟩ : C(A, X))
      (congrArg Subtype.val hA)) ∧
    ∀ δ, FundamentalGroup.mapOfEq
      (⟨fun a => ((eA a : ↥U) : X), continuous_subtype_val.comp eA.continuous⟩ : C(A, X))
      (congrArg Subtype.val hA) δ = 1 ↔
      δ ∈ Subgroup.normalClosure
        ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} :
          Set (FundamentalGroup A a₀)) := by
  obtain ⟨hs, hk⟩ := s78dg_svk_kernel U V hU hV hcover x₀ hx₀
  have hℓ' : FundamentalGroup.mapOfEq (⟨eA, eA.continuous⟩ : C(A, ↥U)) hA
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)) =
      fundamentalGroupAmalgamation U V x₀ hx₀ false
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
    have h1 : FundamentalGroup.mapOfEq (⟨eA, eA.continuous⟩ : C(A, ↥U)) hA
        (Path.Homotopic.Quotient.mk ℓ) = Path.Homotopic.Quotient.mk
          ((ℓ.map (⟨eA, eA.continuous⟩ : C(A, ↥U)).continuous).cast hA.symm hA.symm) :=
      s78dg_pi1_mapOfEq_mk _ a₀ _ hA ℓ _ (fun t => rfl)
    have h2 : FundamentalGroup.mapOfEq (interToLeft U V)
        (interToLeft_overlapBasepoint U V x₀ hx₀) (Path.Homotopic.Quotient.mk γ) =
        Path.Homotopic.Quotient.mk ((γ.map (interToLeft U V).continuous).cast
          (interToLeft_overlapBasepoint U V x₀ hx₀).symm
          (interToLeft_overlapBasepoint U V x₀ hx₀).symm) :=
      s78dg_pi1_mapOfEq_mk _ _ _ (interToLeft_overlapBasepoint U V x₀ hx₀) γ _ (fun t => rfl)
    have hp : ((ℓ.map (⟨eA, eA.continuous⟩ : C(A, ↥U)).continuous).cast hA.symm hA.symm) =
        ((γ.map (interToLeft U V).continuous).cast
          (interToLeft_overlapBasepoint U V x₀ hx₀).symm
          (interToLeft_overlapBasepoint U V x₀ hx₀).symm) := by
      ext t
      exact hℓ t
    change _ = FundamentalGroup.mapOfEq (interToLeft U V)
        (interToLeft_overlapBasepoint U V x₀ hx₀) (Path.Homotopic.Quotient.mk γ)
    rw [h1, h2, hp]
  let eAc : C(A, ↥U) := ⟨eA, eA.continuous⟩
  let g : C(A, X) := ⟨fun a => ((eA a : ↥U) : X), continuous_subtype_val.comp eA.continuous⟩
  let mA := FundamentalGroup.mapOfEq eAc hA
  have hmA : Function.Bijective mA :=
    s78dg_pi1_mapOfEq_bijective eAc a₀ _ hA (s78dg_pi1_homeo_bijective eA a₀)
  have hcomp : ∀ δ, (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom (mA δ) =
      FundamentalGroup.mapOfEq g (congrArg Subtype.val hA) δ := by
    intro δ
    induction δ using Quotient.inductionOn with
    | h ℓ' =>
      have h1 : mA (Path.Homotopic.Quotient.mk ℓ') = Path.Homotopic.Quotient.mk
          ((ℓ'.map eAc.continuous).cast hA.symm hA.symm) :=
        s78dg_pi1_mapOfEq_mk eAc a₀ _ hA ℓ' _ (fun t => rfl)
      have h2 : (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
          (Path.Homotopic.Quotient.mk ((ℓ'.map eAc.continuous).cast hA.symm hA.symm)) =
          Path.Homotopic.Quotient.mk ((ℓ'.map g.continuous).cast (congrArg Subtype.val hA).symm
            (congrArg Subtype.val hA).symm) :=
        s78dg_pi1_mapOfEq_mk (subsetToAmbient U) (leftBasepoint U x₀ hx₀.1) x₀
          (leftBasepoint_toAmbient U x₀ hx₀.1) _ _ (fun t => rfl)
      have h3 : FundamentalGroup.mapOfEq g (congrArg Subtype.val hA)
          (Path.Homotopic.Quotient.mk ℓ') = Path.Homotopic.Quotient.mk
            ((ℓ'.map g.continuous).cast (congrArg Subtype.val hA).symm
              (congrArg Subtype.val hA).symm) :=
        s78dg_pi1_mapOfEq_mk g a₀ _ (congrArg Subtype.val hA) ℓ' _ (fun t => rfl)
      exact (congrArg (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom h1).trans (h2.trans h3.symm)
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := hs x
    obtain ⟨δ, hδ⟩ := hmA.2 y
    exact ⟨δ, by rw [← hcomp, hδ, hy]⟩
  · intro δ
    rw [← hcomp, hk, s78dg_range_normalClosure _ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) hγ, ← hℓ']
    have hN : Subgroup.normalClosure
        ({mA (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ))} :
          Set (FundamentalGroup ↥U (leftBasepoint U x₀ hx₀.1))) =
        (Subgroup.normalClosure ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)} :
          Set (FundamentalGroup A a₀))).map mA := by
      rw [Subgroup.map_normalClosure _ _ hmA.2, Set.image_singleton]
    rw [hN]
    exact Subgroup.mem_map_iff_mem hmA.1

/-- Any space homeomorphic to the punctured unit disc has `π₁` generated by the image of the circle
of radius `1/2`, with a loop parametrised by `t ↦ Φ(½ e^{2πit})`. -/
theorem s78dg_punctured_gen {Y : Type*} [TopologicalSpace Y]
    (Φ : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} ≃ₜ Y) :
    ∃ (b : Y) (γ : Path b b),
      (∃ w : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, (w : ℂ) = ((1 / 2 : ℝ) : ℂ) ∧ b = Φ w) ∧
      (∀ t : I, ∃ w : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1},
        (w : ℂ) = (1 / 2 : ℝ) • ((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ) ∧
          γ t = Φ w) ∧
      ∀ z : FundamentalGroup Y b,
        z ∈ Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  obtain ⟨i, hi, hibij⟩ := s78dg_punctured_disc_pi1
  obtain ⟨γc, hγc, hgen⟩ := s78dg_circle_generator
  let Φc : C({z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, Y) := ⟨Φ, Φ.continuous⟩
  have hΦbij := s78dg_pi1_homeo_bijective Φ (i 0)
  refine ⟨Φ (i 0), ((γc.map i.continuous).map Φc.continuous), ⟨i 0, ?_, rfl⟩, ?_, ?_⟩
  · rw [hi]
    simp [AddCircle.homeomorphCircle_apply]
  · intro t
    refine ⟨i (γc t), ?_, rfl⟩
    rw [hi, hγc t]
    congr 2
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    congr 1
    simp
  · intro z
    obtain ⟨y, rfl⟩ := hΦbij.2 z
    obtain ⟨x, rfl⟩ := hibij.2 y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [map_zpow]
    rfl

/-- The annulus `1/R < |z| < R` is homeomorphic to the punctured unit disc, the circle `|z| = 1`
corresponding to `|w| = 1/2`. -/
theorem s78dg_annulus_homeo (R : ℝ) (hR : 1 < R) :
    ∃ Φ : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} ≃ₜ {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R},
      ∀ w, ‖(Φ w : ℂ)‖ = R ^ (2 * ‖(w : ℂ)‖ - 1) ∧
        ((Φ w : ℂ) = (R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖ : ℝ) • (w : ℂ)) := by
  have hR0 : 0 < R := by linarith
  have hL : 0 < Real.log R := Real.log_pos hR
  have hRinv : 0 < 1 / R := by positivity
  -- exponent bounds
  have hexp : ∀ w : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1},
      1 / R < R ^ (2 * ‖(w : ℂ)‖ - 1) ∧ R ^ (2 * ‖(w : ℂ)‖ - 1) < R := by
    intro w
    obtain ⟨h0, h1⟩ := w.2
    constructor
    · have : R ^ (-1 : ℝ) < R ^ (2 * ‖(w : ℂ)‖ - 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hR (by linarith)
      simpa [Real.rpow_neg_one] using this
    · have : R ^ (2 * ‖(w : ℂ)‖ - 1) < R ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hR (by linarith)
      simpa using this
  have hlogb : ∀ z : {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R},
      0 < Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2 ∧
        Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2 < 1 := by
    intro z
    obtain ⟨h0, h1⟩ := z.2
    have hpos : 0 < ‖(z : ℂ)‖ := hRinv.trans h0
    have hlo : -Real.log R < Real.log ‖(z : ℂ)‖ := by
      have h := Real.log_lt_log hRinv h0
      have e : Real.log (1 / R) = -Real.log R := by rw [one_div, Real.log_inv]
      linarith
    have hhi : Real.log ‖(z : ℂ)‖ < Real.log R := Real.log_lt_log hpos h1
    constructor
    · have : -1 < Real.log ‖(z : ℂ)‖ / Real.log R := by
        rw [lt_div_iff₀ hL]; linarith
      have e : Real.log ‖(z : ℂ)‖ / (2 * Real.log R) = (Real.log ‖(z : ℂ)‖ / Real.log R) / 2 := by
        field_simp
      rw [e]; linarith
    · have : Real.log ‖(z : ℂ)‖ / Real.log R < 1 := by
        rw [div_lt_iff₀ hL]; linarith
      have e : Real.log ‖(z : ℂ)‖ / (2 * Real.log R) = (Real.log ‖(z : ℂ)‖ / Real.log R) / 2 := by
        field_simp
      rw [e]; linarith
  let f : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} → {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R} := fun w =>
    ⟨(R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖ : ℝ) • (w : ℂ), by
      have hn := w.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hR0.le _) hn.le),
        div_mul_cancel₀ _ hn.ne']
      exact hexp w⟩
  let g : {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R} → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} := fun z =>
    ⟨((Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2) / ‖(z : ℂ)‖ : ℝ) • (z : ℂ), by
      have hpos : 0 < ‖(z : ℂ)‖ := hRinv.trans z.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hlogb z).1.le hpos.le),
        div_mul_cancel₀ _ hpos.ne']
      exact hlogb z⟩
  have hfn : ∀ w, ‖(f w : ℂ)‖ = R ^ (2 * ‖(w : ℂ)‖ - 1) := by
    intro w
    have hn := w.2.1
    change ‖(R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖ : ℝ) • (w : ℂ)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hR0.le _) hn.le),
      div_mul_cancel₀ _ hn.ne']
  have hgn : ∀ z, ‖(g z : ℂ)‖ = Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2 := by
    intro z
    have hpos : 0 < ‖(z : ℂ)‖ := hRinv.trans z.2.1
    change ‖((Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2) / ‖(z : ℂ)‖ : ℝ) • (z : ℂ)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hlogb z).1.le hpos.le),
      div_mul_cancel₀ _ hpos.ne']
  have hli : Function.LeftInverse g f := by
    intro w
    apply Subtype.ext
    have hn := w.2.1
    have hlog : Real.log ‖(f w : ℂ)‖ = (2 * ‖(w : ℂ)‖ - 1) * Real.log R := by
      rw [hfn w, Real.log_rpow hR0]
    have hq : Real.log ‖(f w : ℂ)‖ / (2 * Real.log R) + 1 / 2 = ‖(w : ℂ)‖ := by
      rw [hlog]; field_simp; ring
    change (((Real.log ‖(f w : ℂ)‖ / (2 * Real.log R) + 1 / 2) / ‖(f w : ℂ)‖ : ℝ) •
      ((R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖ : ℝ) • (w : ℂ))) = w
    rw [hq, hfn w, smul_smul]
    have hRp : (0 : ℝ) < R ^ (2 * ‖(w : ℂ)‖ - 1) := Real.rpow_pos_of_pos hR0 _
    have : ‖(w : ℂ)‖ / R ^ (2 * ‖(w : ℂ)‖ - 1) * (R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖) = 1 := by
      field_simp
    rw [this, one_smul]
  have hri : Function.RightInverse g f := by
    intro z
    apply Subtype.ext
    have hpos : 0 < ‖(z : ℂ)‖ := hRinv.trans z.2.1
    have hnn := (hlogb z).1
    have hpow : R ^ (2 * ‖(g z : ℂ)‖ - 1) = ‖(z : ℂ)‖ := by
      rw [hgn z, Real.rpow_def_of_pos hR0]
      have : Real.log R * (2 * (Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2) - 1) =
          Real.log ‖(z : ℂ)‖ := by
        field_simp; ring
      rw [this, Real.exp_log hpos]
    change ((R ^ (2 * ‖(g z : ℂ)‖ - 1) / ‖(g z : ℂ)‖ : ℝ) •
      (((Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2) / ‖(z : ℂ)‖ : ℝ) • (z : ℂ))) = z
    rw [hpow, hgn z, smul_smul]
    set n : ℝ := Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2 with hn
    have : ‖(z : ℂ)‖ / n * (n / ‖(z : ℂ)‖) = 1 := by
      have h1 : ‖(z : ℂ)‖ ≠ 0 := hpos.ne'
      have h2 : n ≠ 0 := hnn.ne'
      field_simp
    rw [this, one_smul]
  have hcf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    have hne : ∀ w : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, ‖(w : ℂ)‖ ≠ 0 := fun w => w.2.1.ne'
    have hc1 : Continuous fun w : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} =>
        (R ^ (2 * ‖(w : ℂ)‖ - 1) / ‖(w : ℂ)‖ : ℝ) :=
      (continuous_const.rpow ((continuous_const.mul (continuous_norm.comp continuous_subtype_val)).sub
        continuous_const) (fun _ => Or.inl hR0.ne')).div (continuous_norm.comp continuous_subtype_val) hne
    exact hc1.smul continuous_subtype_val
  have hcg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    have hne : ∀ z : {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R}, ‖(z : ℂ)‖ ≠ 0 :=
      fun z => (hRinv.trans z.2.1).ne'
    have hc1 : Continuous fun z : {z : ℂ // 1 / R < ‖z‖ ∧ ‖z‖ < R} =>
        ((Real.log ‖(z : ℂ)‖ / (2 * Real.log R) + 1 / 2) / ‖(z : ℂ)‖ : ℝ) :=
      (((Continuous.log (continuous_norm.comp continuous_subtype_val) hne).div_const _).add
        continuous_const).div (continuous_norm.comp continuous_subtype_val) hne
    exact hc1.smul continuous_subtype_val
  exact ⟨Homeomorph.mk ⟨f, g, hli, hri⟩ hcf hcg, fun w => ⟨hfn w, rfl⟩⟩

/-- The punctured open unit disc is path connected. -/
theorem s78dg_punctured_pc : PathConnectedSpace {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} := by
  have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
    (convex_Ioo (0 : ℝ) 1).prod convex_univ
  have hc : IsPathConnected (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
    hconv.isPathConnected ⟨(1 / 2, 0), by simp; norm_num⟩
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have himg : f '' (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) =
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      have hn : ‖f (r, θ)‖ = r := by
        change ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr.1]
      rw [Set.mem_setOf_eq, hn]
      exact hr
    · rintro ⟨h0, h1⟩
      refine ⟨(‖z‖, Complex.arg z), ⟨⟨h0, h1⟩, trivial⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  have : IsPathConnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := himg ▸ hc.image hf
  exact isPathConnected_iff_pathConnectedSpace.mp this


end LiZhongQC
