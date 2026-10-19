import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem

/-!
# Pommerenke 1992, Ch. 1 §1.4 Sequences of Conformal Maps

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 796–866.

* Definition (kernel convergence with respect to `w₀`, (1.4.1)) — `KernelConverges`
* Unlabelled (§1.4, l. 814: the kernel limit is uniquely determined; cited in the proof of Theorem 1.8) —
  `kernelLimit_unique`
* Theorem 1.8 (Carathéodory kernel theorem) — `thm1_8`

Not items (DESIGN §3):
- "every subsequence also converges to `G`" (immediate);
- the example `Gₙ = ℂ ∖ (-∞, -1/n] ∖ [1/n, +∞)`;
- the remark on the formally different usual definition.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (unitDisc IsConformalOnto)

/-- **Definition (1.4.1)** (§1.4). Let `w₀ ∈ ℂ` and let `Gₙ` be domains with `w₀ ∈ Gₙ ⊆ ℂ`. Then `Gₙ → G` with
respect to `w₀` in the sense of kernel convergence if
(i) either `G = {w₀}`, or `G` is a domain `≠ ℂ` with `w₀ ∈ G` such that some neighbourhood of every `w ∈ G` lies in
`Gₙ` for large `n`;
(ii) for `w ∈ ∂G` there exist `wₙ ∈ ∂Gₙ` such that `wₙ → w` as `n → ∞`.
Modelling: the standing assumption on the `Gₙ` is part of the predicate. -/
def KernelConverges (G : ℕ → Set ℂ) (w₀ : ℂ) (Glim : Set ℂ) : Prop :=
  (∀ n, IsOpen (G n) ∧ IsConnected (G n) ∧ w₀ ∈ G n) ∧
    (Glim = {w₀} ∨
      (IsOpen Glim ∧ IsConnected Glim ∧ Glim ≠ univ ∧ w₀ ∈ Glim ∧
        ∀ w ∈ Glim, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n)) ∧
    ∀ w ∈ frontier Glim, ∃ wn : ℕ → ℂ, (∀ n, wn n ∈ frontier (G n)) ∧ Tendsto wn atTop (𝓝 w)

/-- **Unlabelled claim** (§1.4, l. 814, proved in the text; cited in the proof of Theorem 1.8). The limit of kernel
convergence is uniquely determined: if `Gₙ → G` and `Gₙ → G*` with respect to `w₀`, then `G = G*`. -/
theorem kernelLimit_unique {G : ℕ → Set ℂ} {w₀ : ℂ} {A B : Set ℂ} (hA : KernelConverges G w₀ A)
    (hB : KernelConverges G w₀ B) : A = B := by
  sorry

/-- **Theorem 1.8** (§1.4; Carathéodory's kernel theorem). Let `fₙ` map `𝔻` conformally onto `Gₙ` with `fₙ(0) = w₀`
and `fₙ'(0) > 0`. If `G = {w₀}` let `f(z) ≡ w₀`, otherwise let `f` map `𝔻` conformally onto `G` with `f(0) = w₀` and
`f'(0) > 0`. Then, as `n → ∞`, `fₙ → f` locally uniformly in `𝔻` if and only if `Gₙ → G` with respect to `w₀`.
Modelling: `f'(0) > 0` is `Re f'(0) > 0 ∧ Im f'(0) = 0`; the `Gₙ ⊆ ℂ` are the images `fₙ(𝔻)`. -/
theorem thm1_8 {f : ℕ → ℂ → ℂ} {G : ℕ → Set ℂ} {w₀ : ℂ}
    (hf : ∀ n, IsConformalOnto (f n) unitDisc (G n) ∧ f n 0 = w₀ ∧ 0 < (deriv (f n) 0).re ∧
      (deriv (f n) 0).im = 0)
    {g : ℂ → ℂ} {Glim : Set ℂ}
    (hg : (Glim = {w₀} ∧ ∀ z, g z = w₀) ∨
      (IsConformalOnto g unitDisc Glim ∧ g 0 = w₀ ∧ 0 < (deriv g 0).re ∧ (deriv g 0).im = 0)) :
    TendstoLocallyUniformlyOn f g atTop unitDisc ↔ KernelConverges G w₀ Glim := by
  sorry

end Pommerenke1992
