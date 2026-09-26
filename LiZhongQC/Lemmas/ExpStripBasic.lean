import LiZhongQC.Lemmas.Conformal

/-!
# expStrip / strip and their basic shift/openness facts (D3a, D3b, D3c)

Shared by every other leaf in the Theorem 2.1 case (iii) install.
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The log-lift of a region lying outside the closed unit disc. -/
def expStrip (A : Set ℂ) : Set ℂ := {z : ℂ | 0 < z.re ∧ Complex.exp z ∈ A}

/-- The open vertical strip `0 < Re z < d`. -/
def strip (d : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Ioo (0 : ℝ) d}

/-- D3a: `Σ = expStrip A` is invariant under the `2πi` shift. -/
theorem mem_expStrip_add_two_pi_I {A : Set ℂ} {z : ℂ} :
    z + 2 * (Real.pi : ℂ) * I ∈ expStrip A ↔ z ∈ expStrip A := by
  have hre : (z + 2 * (Real.pi : ℂ) * I).re = z.re := by simp
  have hexp : Complex.exp (z + 2 * (Real.pi : ℂ) * I) = Complex.exp z := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [expStrip, mem_setOf_eq, hre, hexp]

/-- D3b: the shifted map is another conformal map of `Σ` onto the same strip. -/
theorem isConformalOnto_comp_shift {A : Set ℂ} {d : ℝ} {g : ℂ → ℂ}
    (hg : IsConformalOnto g (expStrip A) (strip d)) :
    IsConformalOnto (fun z => g (z + 2 * (Real.pi : ℂ) * I)) (expStrip A) (strip d) := by
  obtain ⟨hgd, hginj, hgimg⟩ := hg
  have hshift : (fun z : ℂ => z + 2 * (Real.pi : ℂ) * I) '' expStrip A = expStrip A := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact mem_expStrip_add_two_pi_I.2 hz
    · intro hw
      exact ⟨w - 2 * (Real.pi : ℂ) * I, by
        refine mem_expStrip_add_two_pi_I.1 ?_
        simpa using hw, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · have hcomp : DifferentiableOn ℂ (g ∘ fun w : ℂ => w + 2 * (Real.pi : ℂ) * I)
        (expStrip A) := by
      intro z hz
      have hf : DifferentiableWithinAt ℂ (fun w : ℂ => w + 2 * (Real.pi : ℂ) * I)
          (expStrip A) z := by fun_prop
      exact DifferentiableWithinAt.comp z (hgd _ (mem_expStrip_add_two_pi_I.2 hz)) hf
        (fun w hw => mem_expStrip_add_two_pi_I.2 hw)
    exact hcomp
  · intro z₁ h₁ z₂ h₂ heq
    have := hginj (mem_expStrip_add_two_pi_I.2 h₁) (mem_expStrip_add_two_pi_I.2 h₂) heq
    linear_combination this
  · rw [show (fun z : ℂ => g (z + 2 * (Real.pi : ℂ) * I)) '' expStrip A
          = g '' ((fun z : ℂ => z + 2 * (Real.pi : ℂ) * I) '' expStrip A) from
        (Set.image_image _ _ _).symm, hshift, hgimg]

/-- D3c: `Σ` is open. -/
theorem isOpen_expStrip {A : Set ℂ} (hAo : IsOpen A) : IsOpen (expStrip A) := by
  have hEq : expStrip A = {z : ℂ | 0 < z.re} ∩ Complex.exp ⁻¹' A := Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (hAo.preimage Complex.continuous_exp)
end LiZhongQC
