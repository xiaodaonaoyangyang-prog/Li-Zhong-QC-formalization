import LiZhongQC.Lemmas.QDSeamLocalAlgebra
import LiZhongQC.Lemmas.QDReflectAcrossArc
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.CaratheodoryJordan
import LiZhongQC.Lemmas.FiniteTypeUniquenessProof
import LiZhongQC.Lemmas.QDReflectionAfterHalves
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Frontier points of the chart image of a hole disc come from the frontier of the hole. -/
theorem s31qi_hole_frontier_back {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    {D : Set X} {x : X} {Jd : Set ℂ} (hDs : D ⊆ (chartAt ℂ x).source) (hJd : IsJordanDomain Jd)
    (hbd : Bornology.IsBounded Jd) (hcl : chartAt ℂ x '' D = closure Jd) (hDc : IsCompact D)
    (hclt : closure Jd ⊆ (chartAt ℂ x).target) {y : ℂ} (hy : y ∈ frontier Jd) :
    y ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm y ∈ frontier D := by
  have hycl : y ∈ closure Jd := frontier_subset_closure hy
  have hyt : y ∈ (chartAt ℂ x).target := hclt hycl
  rw [← hcl] at hycl
  obtain ⟨d, hdD, rfl⟩ := hycl
  have hsymm : (chartAt ℂ x).symm (chartAt ℂ x d) = d := (chartAt ℂ x).left_inv (hDs hdD)
  refine ⟨hyt, ?_⟩
  rw [hsymm]
  refine ⟨subset_closure hdD, fun hi => ?_⟩
  have hU : IsOpen ((chartAt ℂ x) '' interior D) :=
    (chartAt ℂ x).isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hDs)
  have hUsub : (chartAt ℂ x) '' interior D ⊆ closure Jd := by
    rw [← hcl]
    exact image_mono interior_subset
  have hint : chartAt ℂ x d ∈ interior (closure Jd) :=
    interior_maximal hUsub hU ⟨d, hi, rfl⟩
  have hjplane : IsJordanCurve (toExt (frontier Jd)) := by
    rw [← frontier_toExt_of_isBounded' hbd hJd.1]
    exact hJd.2.2
  have hJ := interior_closure_subset_of_isJordanCurve_frontier hJd.1 hJd.2.1 hbd hjplane hint
  exact hy.2 (by rw [hJd.1.interior_eq]; exact hJ)

/-- (C1) Local analytic seam germ in a preferred chart of `Xd`.  At a chart point `z₀` of a point `p₀`
of the fixed curve of `J` (not a puncture), the actual two-half coefficient data `s31qr_twoHalfData`
of an admissible `q` is, on the points of a small chart disc lying in the two halves, the restriction of
a single analytic function `H` on the whole disc.  The proof uses (A), (B) and the fixed-curve
collar coordinate; it is the coefficient-level form (no chain-rule transport is left to the glue step). -/
theorem s31qi_seam_local {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (q : admissibleQDSpace F) (x : Xd.carrier) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target)
    (hfix : J ((chartAt ℂ x).symm z₀) = (chartAt ℂ x).symm z₀)
    (hP : (chartAt ℂ x).symm z₀ ∉ Pd) :
    ∃ ε : ℝ, 0 < ε ∧ ball z₀ ε ⊆ (chartAt ℂ x).target ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball z₀ ε) ∧
        ∀ z ∈ ball z₀ ε, ((chartAt ℂ x).symm z ∈ range ιd ∨ (chartAt ℂ x).symm z ∈ range (J ∘ ιd)) →
          H z = s31qr_twoHalfData F hd (q : F.X.carrier → ℂ → ℂ) x z := by
  classical
  haveI : Nonempty S := inferInstance
  obtain ⟨j, wc, r, hr, hp₀, hwc0, hwt, hmd, hmds, hJw, hup, hreal, hcol⟩ :=
    s31qi_collar_from_hd F hm hd (p₀ := (chartAt ℂ x).symm z₀) hfix
  obtain ⟨xF, hDs, Jd, hJd, hbd, hclt, hcl, c, hc, hc', hper, hinj, hcf⟩ := F.disc j
  obtain ⟨r', hr'0, hr'r, κ, hκd, hκc, hκi, hκu, hκr, hκV, hlink⟩ :=
    hcol xF Jd hDs hJd hbd hcl hclt
  have hqa := q.2
  obtain ⟨hq1, hq2, -, hq4, hq5, -⟩ := hqa
  have hDc : IsCompact (F.D j) := s31eg_disc_compact (F.disc j)
  have hback : ∀ {y : ℂ}, y ∈ frontier Jd →
      y ∈ (chartAt ℂ xF).target ∧ (chartAt ℂ xF).symm y ∈ frontier (F.D j) := fun hy =>
    s31qi_hole_frontier_back hDs hJd hbd hcl hDc hclt hy
  -- the open half lies in the chart image of `F.ι`
  have hupper : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im →
      κ z ∈ (chartAt ℂ xF).target ∧ (chartAt ℂ xF).symm (κ z) ∈ range F.ι := by
    intro z hz hzi
    obtain ⟨s, -, hs2, hs3⟩ := hlink z hz hzi
    refine ⟨?_, ⟨s, ?_⟩⟩
    · rw [hs3]
      exact (chartAt ℂ xF).map_source hs2
    · rw [hs3]
      exact ((chartAt ℂ xF).left_inv hs2).symm ▸ rfl
  obtain ⟨G, hGa, hGs, hGe⟩ := s31qi_reflect_across_arc hJd hbd hc hc' hper hinj hcf hr'0
    (κ := κ) (Qc := (q : F.X.carrier → ℂ → ℂ) xF)
    hκd hκc hκi hκu hκr hκV
    (by
      refine (hq2 xF).mono ?_
      rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩
      exact hupper z hz hzi)
    (by
      refine (hq4 xF j).mono ?_
      rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩
      rcases hzi.eq_or_lt with h0 | hpos
      · have hz0 : z.im = 0 := h0.symm
        obtain ⟨ht, hf⟩ := hback (hκr ⟨hz, hz0⟩)
        exact ⟨ht, Or.inr hf⟩
      · obtain ⟨ht, hr⟩ := hupper z hz hpos
        exact ⟨ht, Or.inl hr⟩)
    (by
      intro γ a b hγ hsub t ht
      refine hq5 xF j γ a b hγ ?_ t ht
      intro y hy
      exact hback (hsub hy))
  exact s31qi_seam_local_algebra F hd hq1 x hz₀ wc hr'0 hp₀ hwc0 hmd hJw hup xF hκd hlink hGa
    hGs hGe


end LiZhongQC
