import LiZhongQC.Lemmas.GeodesicSmoothSide
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- An increasing bijective side parameter is continuous, including the two
endpoints. Applied to a side as `s25cv_par_continuous S.mono S.bij`; this also
works directly with the flat parameter fields returned by `s25cv_chain_fields`. -/
theorem s25cv_par_continuous {p : ℝ → ℝ} {a b : ℝ}
    (hm : StrictMonoOn p (Icc (0 : ℝ) 1))
    (hb : BijOn p (Icc (0 : ℝ) 1) (Icc a b)) :
    ContinuousOn p (Icc (0 : ℝ) 1) := by
  let H : Icc (0 : ℝ) 1 → Icc a b := fun x => ⟨p x.val, hb.1 x.property⟩
  have hHm : StrictMono H := fun x y hxy => hm x.property y.property hxy
  have hHs : Function.Surjective H := by
    intro y
    obtain ⟨x, hx, he⟩ := hb.2.2 y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hHc : Continuous H := (hHm.orderIsoOfSurjective H hHs).continuous
  exact continuousOn_iff_continuous_domRestrict.2 (continuous_subtype_val.comp hHc)

end LiZhongQC

