import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.QDDecompConjTransport
import LiZhongQC.Lemmas.QDDecompLinearAlgebra
import LiZhongQC.Lemmas.QDDecompExtFixed
import LiZhongQC.Lemmas.QDDecompRestriction

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- §31.2: the reflection `T : ω ↦ ω*` of `Q̃(S^d)` (`ω*` at `p` is the conjugate of `ω` at the mirror
point `p̄`, in the conjugate parameter) is a real linear involution, anti-linear over `ℂ`; the
symmetric differentials `Ω = {½(I + T)ω}` (identified with `Q̃(S₀)`) and the anti-symmetric ones
`Ω' = {½(I - T)ω} = iΩ` give `Q̃(S^d) = Ω ⊕ Ω'`, so `dim Ω = ½ dim Q̃(S^d)`. -/
theorem admissibleQD_double_decomposition [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    ∃ T : admissibleQDSpace Fd →ₗ[ℝ] admissibleQDSpace Fd, (∀ q, T (T q) = q) ∧
      (∀ (q : admissibleQDSpace Fd) (hq : (I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ) ∈ admissibleQDSpace Fd),
        (T ⟨(I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ), hq⟩ : Fd.X.carrier → ℂ → ℂ) =
          -((I : ℂ) • (T q : Fd.X.carrier → ℂ → ℂ))) ∧
      Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) = Module.finrank ℝ (admissibleQDSpace F) ∧
      Module.finrank ℝ (admissibleQDSpace Fd) = 2 * Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) := by
  classical
  -- `hex` is not needed: the decomposition holds for every type with `m ≠ 0`.
  have _hex := hex
  obtain ⟨T0, hT0⟩ := s31qi_seam_fill F hm hd
  obtain ⟨E, hE, hEι, hEP⟩ := s31qr_fd_compactification Xd Pd Fd
  -- the reflection `T`: conjugate transport along `E ∘ J ∘ E⁻¹`
  let Tf : (Fd.X.carrier → ℂ → ℂ) → (Fd.X.carrier → ℂ → ℂ) :=
    s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y))) Complex.conjCLE.toLinearMap
  have hS1 : ∀ q : admissibleQDSpace Fd, IsAdmissibleQD Fd (Tf q) := fun q =>
    s31qd_conj_admissible Xd Pd Fd E hE hEP hd.involution hd.Pd_invariant q.2
  let T : admissibleQDSpace Fd →ₗ[ℝ] admissibleQDSpace Fd :=
    { toFun := fun q => ⟨Tf q, hS1 q⟩
      map_add' := fun q r => by
        apply Subtype.ext
        change Tf ((q : Fd.X.carrier → ℂ → ℂ) + r) = Tf q + Tf r
        exact s31qr_transport_add _ _ _ _ _
      map_smul' := fun c q => by
        apply Subtype.ext
        change Tf (c • (q : Fd.X.carrier → ℂ → ℂ)) = c • Tf q
        exact s31qr_transport_real_smul _ _ _ c _ }
  -- conjugate linearity of `T`
  have hTI : ∀ q : admissibleQDSpace Fd,
      Tf ((I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ)) = -((I : ℂ) • Tf q) := by
    intro q
    have h := s31qd_conj_transport_smul (univ : Set Fd.X.carrier)
      (fun y : Fd.X.carrier => E (J (E.symm y))) (I : ℂ) (q : Fd.X.carrier → ℂ → ℂ)
    rw [Complex.conj_I, neg_smul] at h
    exact h
  have hTT : ∀ q, T (T q) = q := by
    intro q
    apply Subtype.ext
    change Tf (Tf q) = q
    have hq : IsAdmissibleQD Fd (q : Fd.X.carrier → ℂ → ℂ) := q.2
    exact s31qd_conj_involutive Xd Pd Fd E hE hd.involution hq.1
  -- the symmetric extension `ext` (as in `admissibleQD_symmetric_extension`)
  have hadm : ∀ q : admissibleQDSpace F,
      IsAdmissibleQD Fd (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (T0 q)) := by
    intro q
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT0 q
    refine s31qr_fd_transport_admissible Xd Pd Fd E hE hEP h1 h2 ?_
    intro a p hp hs
    exact ⟨h5 a p hp hs, s31qi_puncture_poles F hm hd q (T0 q) h3 h4 a p hp hs⟩
  let tr : (Xd.carrier → ℂ → ℂ) →ₗ[ℝ] (Fd.X.carrier → ℂ → ℂ) :=
    { toFun := s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
      map_add' := fun q r => s31qr_transport_add _ _ _ q r
      map_smul' := fun c q => s31qr_transport_real_smul _ _ _ c q }
  let ext : admissibleQDSpace F →ₗ[ℝ] admissibleQDSpace Fd :=
    { toFun := fun q => ⟨tr (T0 q), hadm q⟩
      map_add' := fun q r => by
        apply Subtype.ext
        change tr (T0 (q + r)) = tr (T0 q) + tr (T0 r)
        rw [map_add, map_add]
      map_smul' := fun c q => by
        apply Subtype.ext
        change tr (T0 (c • q)) = c • tr (T0 q)
        rw [map_smul, map_smul] }
  have hinj : Function.Injective ext := by
    rw [injective_iff_map_eq_zero]
    intro q hq0
    have h0 : tr (T0 q) = 0 := congrArg Subtype.val hq0
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT0 q
    have hzero := s31qi_transport_zero Xd Pd Fd E hE h1 h0
    apply Subtype.ext
    haveI : Nonempty S := inferInstance
    refine s31qr_positive_restriction_recover F hd q.2 ?_
    intro x z hz hp
    rw [← h3 x z hz hp]
    exact hzero x z hz
  -- `ext` lands in the fixed space of `T` (S5) and onto it (S6b)
  have hfixed : ∀ q : admissibleQDSpace F, ext q ∈ LinearMap.ker (T - LinearMap.id) := by
    intro q
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT0 q
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    apply Subtype.ext
    change Tf (tr (T0 q)) = tr (T0 q)
    exact s31qd_ext_fixed F hm hd Fd E hE hEP q h1 h2 h3 h4 h5
  let ext' : admissibleQDSpace F →ₗ[ℝ] LinearMap.ker (T - LinearMap.id) :=
    LinearMap.codRestrict _ ext hfixed
  have hbij : Function.Bijective ext' := by
    refine ⟨fun q r h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨Q, hQ⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hQ
    have hQfix : Tf (Q : Fd.X.carrier → ℂ → ℂ) = Q := congrArg Subtype.val hQ
    have hQa : IsAdmissibleQD Fd (Q : Fd.X.carrier → ℂ → ℂ) := Q.2
    obtain ⟨q, hq⟩ := s31qd_restriction F hm hd Fd E hE hEι hEP T0 hT0 hQa hQfix
    exact ⟨q, Subtype.ext (Subtype.ext hq)⟩
  -- the complex structure `q ↦ I • q` of `Q̃(Fd)` (no holes)
  letI : Infinite Xd.carrier :=
    Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x0, hx0⟩ := Pd.exists_notMem
  have hne : ((↑Pd : Set Xd.carrier)ᶜ).Nonempty :=
    ⟨x0, by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hx0⟩
  have hc : IsConnected ((↑Pd : Set Xd.carrier)ᶜ) :=
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      Pd.finite_toSet hne).isConnected
  letI : ConnectedSpace (puncturedOpens Pd) := Subtype.connectedSpace hc
  have hsmul := k31p_complex_smul Fd
  let jm : admissibleQDSpace Fd →ₗ[ℝ] admissibleQDSpace Fd :=
    { toFun := fun q => ⟨(I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ), hsmul I (q : Fd.X.carrier → ℂ → ℂ) q.2⟩
      map_add' := fun q r => by
        apply Subtype.ext
        change (I : ℂ) • ((q : Fd.X.carrier → ℂ → ℂ) + r) =
          (I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ) + (I : ℂ) • (r : Fd.X.carrier → ℂ → ℂ)
        exact smul_add _ _ _
      map_smul' := fun c q => by
        apply Subtype.ext
        change (I : ℂ) • (c • (q : Fd.X.carrier → ℂ → ℂ)) = c • ((I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ))
        exact smul_comm _ _ _ }
  have hjj : ∀ v, jm (jm v) = -v := by
    intro v
    apply Subtype.ext
    change (I : ℂ) • ((I : ℂ) • (v : Fd.X.carrier → ℂ → ℂ)) = -(v : Fd.X.carrier → ℂ → ℂ)
    rw [smul_smul, I_mul_I, neg_one_smul]
  have hTj : ∀ v, T (jm v) = -(jm (T v)) := by
    intro v
    apply Subtype.ext
    change Tf ((I : ℂ) • (v : Fd.X.carrier → ℂ → ℂ)) = -((I : ℂ) • Tf v)
    exact hTI v
  refine ⟨T, hTT, ?_, ((LinearEquiv.ofBijective ext' hbij).finrank_eq).symm,
    s31qd_conj_involution_finrank T jm hTT hjj hTj⟩
  intro q hq
  change Tf ((I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ)) = -((I : ℂ) • Tf q)
  exact hTI q

end LiZhongQC
