import LiZhongQC.ClusterSets
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Analytic seam compatibility for the actual Schottky quotient charts.
The hypotheses below describe continuous charts and holomorphy on one open
half only. Holomorphy at the seam is proved by the installed Schwarz theorem. -/

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- A continuous, conjugation-equivariant function on a symmetric open set
is analytic everywhere if it is holomorphic on the upper half. -/
theorem s78ra_analytic_of_conj_equivariant {O : Set ℂ}
    (hO : IsRealSymmetric O) {f : ℂ → ℂ}
    (hc : ContinuousOn f O)
    (hh : DifferentiableOn ℂ f (upperPart O))
    (he : ∀ z ∈ O, f (conj z) = conj (f z)) :
    AnalyticOnNhd ℂ f O := by
  have hr : ∀ z ∈ realPart O, (f z).im = 0 := by
    intro z hz
    have hz' : z ∈ O ∧ z.im = 0 := hz
    have h := he z hz'.1
    rw [Complex.conj_eq_iff_im.2 hz'.2] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hu : upperPart O ∪ realPart O ⊆ O := by
    intro z hz
    rcases hz with hz | hz <;> exact hz.1
  have hd := schwarz_reflection_segment hO hh (hc.mono hu) hr
  have heq : EqOn f (reflectExtend f) O := by
    intro z hz
    by_cases hi : 0 ≤ z.im
    · exact (reflectExtend_eq_of_im_nonneg f hi).symm
    · rw [reflectExtend_eq_of_im_neg f (lt_of_not_ge hi), he z hz,
        Complex.conj_conj]
  have hf : DifferentiableOn ℂ f O := hd.congr heq
  exact fun z hz => hf.analyticAt (hO.isOpen.mem_nhds hz)

/-- A chart intertwining a map J with conjugation also intertwines the
inverse chart. This uses only the actual chart inverse identities. -/
theorem s78ra_chart_inverse_conj {X : Type*} [TopologicalSpace X]
    (J : X → X) (u : OpenPartialHomeomorph X ℂ)
    (hu : ∀ x ∈ u.source, J x ∈ u.source ∧ u (J x) = conj (u x))
    {z : ℂ} (hz : z ∈ u.target) :
    conj z ∈ u.target ∧ u.symm (conj z) = J (u.symm z) := by
  have hx := hu (u.symm z) (u.symm.mapsTo hz)
  have he : u (J (u.symm z)) = conj z := by
    rw [hx.2, u.right_inv hz]
  constructor
  · rw [← he]
    exact u.mapsTo hx.1
  · rw [← he, u.left_inv hx.1]

/-- The coordinate overlap of two reflection-equivariant charts is an
open conjugation-symmetric set. No differentiability is used here. -/
theorem s78ra_chart_overlap_symmetric {X : Type*} [TopologicalSpace X]
    (J : X → X) (u v : OpenPartialHomeomorph X ℂ)
    (hu : ∀ x ∈ u.source, J x ∈ u.source ∧ u (J x) = conj (u x))
    (hv : ∀ x ∈ v.source, J x ∈ v.source ∧ v (J x) = conj (v x)) :
    IsRealSymmetric (u.symm.trans v).source := by
  have hs : ∀ z ∈ (u.symm.trans v).source,
      conj z ∈ (u.symm.trans v).source := by
    intro z hz
    change z ∈ u.target ∧ u.symm z ∈ v.source at hz
    change conj z ∈ u.target ∧ u.symm (conj z) ∈ v.source
    obtain ⟨hz', he⟩ := s78ra_chart_inverse_conj J u hu hz.1
    refine ⟨hz', ?_⟩
    rw [he]
    exact (hv (u.symm z) hz.2).1
  refine ⟨(u.symm.trans v).open_source, ?_⟩
  change conj '' (u.symm.trans v).source = (u.symm.trans v).source
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hs z hz
  · intro z hz
    exact ⟨conj z, hs z hz, Complex.conj_conj z⟩

/-- Transition functions of reflection-equivariant charts commute with
conjugation, including on the seam. -/
theorem s78ra_chart_transition_conj {X : Type*} [TopologicalSpace X]
    (J : X → X) (u v : OpenPartialHomeomorph X ℂ)
    (hu : ∀ x ∈ u.source, J x ∈ u.source ∧ u (J x) = conj (u x))
    (hv : ∀ x ∈ v.source, J x ∈ v.source ∧ v (J x) = conj (v x)) :
    ∀ z ∈ (u.symm.trans v).source,
      (v ∘ u.symm) (conj z) = conj ((v ∘ u.symm) z) := by
  intro z hz
  change z ∈ u.target ∧ u.symm z ∈ v.source at hz
  change v (u.symm (conj z)) = conj (v (u.symm z))
  rw [(s78ra_chart_inverse_conj J u hu hz.1).2]
  exact (hv (u.symm z) hz.2).2

/-- The analytic compatibility theorem used to install boundary charts on
the concrete double. Only the upper half transition needs an analytic proof;
the reflected half and the seam are consequences. -/
theorem s78ra_boundary_charts_compatible {X : Type*} [TopologicalSpace X]
    (J : X → X) (u v : OpenPartialHomeomorph X ℂ)
    (hu : ∀ x ∈ u.source, J x ∈ u.source ∧ u (J x) = conj (u x))
    (hv : ∀ x ∈ v.source, J x ∈ v.source ∧ v (J x) = conj (v x))
    (hh : DifferentiableOn ℂ (v ∘ u.symm)
      (upperPart (u.symm.trans v).source)) :
    AnalyticOnNhd ℂ (v ∘ u.symm) (u.symm.trans v).source := by
  exact s78ra_analytic_of_conj_equivariant
    (s78ra_chart_overlap_symmetric J u v hu hv)
    (u.symm.trans v).continuousOn hh
    (s78ra_chart_transition_conj J u v hu hv)

/-- The derivative of the reflected branch is the conjugate derivative at
the reflected point. This is the factor needed for quadratic-differential
coordinate changes, before squaring it. -/
theorem s78ra_reflected_hasDerivAt {f : ℂ → ℂ} {z a : ℂ}
    (hz : z.im < 0) (hf : HasDerivAt f a (conj z)) :
    HasDerivAt (reflectExtend f) (conj a) z := by
  have h : HasDerivAt (conj ∘ f ∘ conj) (conj a) z := by
    simpa only [Complex.conj_conj] using hf.conj_conj
  apply h.congr_of_eventuallyEq
  have hn : {w : ℂ | w.im < 0} ∈ 𝓝 z :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz
  filter_upwards [hn] with w hw
  exact reflectExtend_eq_of_im_neg f hw

/-- At a fixed point of reflection, the derivative of a holomorphic
reflection-equivariant transition is real. -/
theorem s78ra_deriv_real_at_seam {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ O) (hzi : z.im = 0)
    (hf : DifferentiableAt ℂ f z)
    (he : ∀ w ∈ O, f (conj w) = conj (f w)) :
    (deriv f z).im = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.2 hzi
  have h : HasDerivAt (conj ∘ f ∘ conj) (conj (deriv f z)) z := by
    simpa only [hc] using hf.hasDerivAt.conj_conj
  have heq : f =ᶠ[𝓝 z] (conj ∘ f ∘ conj) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    simp only [Function.comp_apply, he w hw, Complex.conj_conj]
  have hd : HasDerivAt f (conj (deriv f z)) z := h.congr_of_eventuallyEq heq
  exact Complex.conj_eq_iff_im.1 (hf.hasDerivAt.unique hd).symm

end LiZhongQC
