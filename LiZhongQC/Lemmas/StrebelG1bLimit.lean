import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace LiZhongQC

/-- The approved finite-error ENNReal limit bridge; source-only proof, not yet compiled. -/
theorem s36g_error_limit {A B C D : ℝ≥0∞}
    (hA : A < ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ε < ⊤ →
      A ≤ B + C * (A + (A + ε)) ^ (1 / 2 : ℝ) * ε ^ (1 / 2 : ℝ) + D * ε + ε) :
    A ≤ B := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have ht : Tendsto (fun ε : ℝ≥0∞ => ε) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 0) :=
    continuous_id.continuousWithinAt
  have hAc : Tendsto (fun _ : ℝ≥0∞ => A) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 A) :=
    tendsto_const_nhds
  have hs : Tendsto (fun ε : ℝ≥0∞ => A + (A + ε))
      (𝓝[>] (0 : ℝ≥0∞)) (𝓝 (A + A)) := by
    simpa only [add_zero] using hAc.add (hAc.add ht)
  have hp := Filter.Tendsto.ennrpow_const (1 / 2 : ℝ) hs
  have hz : Tendsto (fun ε : ℝ≥0∞ => ε ^ (1 / 2 : ℝ))
      (𝓝[>] (0 : ℝ≥0∞)) (𝓝 0) := by
    simpa [hhalf] using Filter.Tendsto.ennrpow_const (1 / 2 : ℝ) ht
  have hcp := ENNReal.Tendsto.const_mul hp (Or.inr hC)
  have hcpfin : C * (A + A) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hC
      (ENNReal.rpow_ne_top_of_nonneg hhalf.le (ENNReal.add_ne_top.2 ⟨hA.ne, hA.ne⟩))
  have he : Tendsto
      (fun ε : ℝ≥0∞ => C * (A + (A + ε)) ^ (1 / 2 : ℝ) * ε ^ (1 / 2 : ℝ))
      (𝓝[>] (0 : ℝ≥0∞)) (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.mul hcp (Or.inr ENNReal.zero_ne_top) hz (Or.inr hcpfin)
  have hd : Tendsto (fun ε : ℝ≥0∞ => D * ε) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr hD)
  have hBc : Tendsto (fun _ : ℝ≥0∞ => B) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 B) :=
    tendsto_const_nhds
  have htotal : Tendsto
      (fun ε : ℝ≥0∞ => B + C * (A + (A + ε)) ^ (1 / 2 : ℝ) * ε ^ (1 / 2 : ℝ) +
        D * ε + ε) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 B) := by
    simpa only [add_zero] using ((hBc.add he).add hd).add ht
  apply ge_of_tendsto htotal
  have hfin : ∀ᶠ ε : ℝ≥0∞ in 𝓝[>] (0 : ℝ≥0∞), ε < ⊤ :=
    ht.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) < ⊤ by simp))
  filter_upwards [self_mem_nhdsWithin, hfin] with ε hε hεfin
  exact h ε hε hεfin

end LiZhongQC
