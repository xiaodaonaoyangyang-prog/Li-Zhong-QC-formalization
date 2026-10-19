import LiZhongQC.Lemmas.QDDoubleDecomposition
import LiZhongQC.Lemmas.SchottkyTerminal

/-!
# Theorem 31.1: the dimension of the admissible quadratic differentials (§31.2)

`dim_ℝ Q̃(S₀) = 6g - 6 + 2n + 3m` for a non-exceptional surface of type `(g, n, m)`.  For `m = 0` this is
`admissibleQD_complex_finrank`; for `m ≠ 0` it follows from the Schottky double (`exists_schottkyDouble`),
the dimension (31.1) of `Q̃(S^d)` (`eq31_1_double_finrank`) and the decomposition
`Q̃(S^d) = Ω ⊕ iΩ` with `Ω ≅ Q̃(S₀)` (`admissibleQD_double_decomposition`).
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- The punctured double `Xd ∖ Pd` as a surface of type `(g', #Pd, 0)` (no holes; `ι` the inclusion). -/
theorem s31dm_punctured_fts {Xd : ClosedRS.{u}} (Pd : Finset Xd.carrier) {g' k : ℕ}
    (hg : HasGenus Xd.carrier g') (hk : Pd.card = k) :
    Nonempty (FiniteTypeStructure (puncturedOpens Pd) g' k 0) := by
  classical
  refine ⟨{ X := Xd
            P := Pd
            D := fun j => j.elim0
            ι := Subtype.val
            genus := hg
            card_P := hk
            disc := fun j => j.elim0
            disjoint := fun i => i.elim0
            disjoint_P := fun j => j.elim0
            embedding := (puncturedOpens Pd).isOpen.isOpenEmbedding_subtypeVal
            holomorphic := (contMDiff_subtype_val (n := ω) (U := puncturedOpens Pd)).mdifferentiable (by simp)
            range_ι := ?_ }⟩
  ext x
  simp [puncturedOpens]

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- **Theorem 31.1** (31.2), archive helper with the book statement of `thm31_1_admissibleQD_finrank`. -/
theorem s31dm_thm31_1 [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hex : ¬ IsExceptionalType g n m) :
    (Module.finrank ℝ (admissibleQDSpace F) : ℤ) = 6 * g - 6 + 2 * n + 3 * m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have h := (admissibleQD_complex_finrank F hex).2
    rw [h]
    push_cast
    ring
  · have hm : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
    obtain ⟨Xd, J, ιd, Pd, hd⟩ := exists_schottkyDouble hm F
    obtain ⟨Fd⟩ := s31dm_punctured_fts Pd hd.genus hd.card_Pd
    have hdim := eq31_1_double_finrank F hm hex hd Fd
    obtain ⟨T, -, -, hfix, htot⟩ := admissibleQD_double_decomposition F hm hex hd Fd
    rw [htot, hfix] at hdim
    push_cast at hdim
    linarith

/-- **Theorem 31.1** (31.2): for a non-exceptional surface `S₀` of type `(g, n, m)`,
`dim_ℝ Q̃(S₀) = 6g - 6 + 2n + 3m`. -/
theorem thm31_1_admissibleQD_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hex : ¬ IsExceptionalType g n m) :
    (Module.finrank ℝ (admissibleQDSpace F) : ℤ) = 6 * g - 6 + 2 * n + 3 * m := by
  exact s31dm_thm31_1 F hex

end LiZhongQC
