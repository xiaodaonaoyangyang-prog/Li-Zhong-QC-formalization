import LiZhongQC.Ch08.S29_TeichmullerMetric

/-!
# §30 模群的间断性 — Discontinuity of the modular group

* §30.1 the Poincaré metric of `S = ℍ/G`, the length `l[α]` of the shortest curve in the free
  homotopy class of a closed curve and the length spectrum      — `poincareLengthLoop`,
                                                                  `freeHomotopyLength`, `lengthSpectrum`
* §30.2 covering elements; Lemma 30.1 (parabolic ⟺ curve around a puncture); the generalized
  Schwarz lemma; Lemma 30.2 (`l[α] = ln λ²`)                    — `Covers`, `lemma30_1`,
                                                                  `generalized_schwarz`, `lemma30_2`
* §30.3 Theorem 30.1 (discreteness of the length spectrum)      — `thm30_1_discrete`
Theorem 30.2 (finitely many lengths determine the marked surface) has its statement and proof in
`LiZhongQC.Lemmas.LengthSpectrum`, which imports this completed module to use (30.1)–(30.4)
and the later free-homotopy and length helpers.
* §30.5 Lemma 30.3 (Wolpert, (30.5)–(30.9)); Theorem 30.3 (discontinuity of `Mod(S₀)`),
  (30.10)–(30.13), Hurwitz's theorem                            — `lemma30_3_wolpert`, `hurwitz`
* §30.6 Theorem 30.4 (`R_g` is Hausdorff)                       — (see the last bullet)
* Hurwitz's finiteness theorem, Theorems 30.3 and 30.4 and the proper discontinuity of the modular action are stated
  (same docstring and statement) and proved in `LiZhongQC.Lemmas.UniformizedTeichmuller`, whose proofs need that module
  (it is downstream of this file).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-! ## §30.1 The length spectrum -/

/-- The hyperbolic length `∫ |dz|/Im z` of a curve `c : [0,1] → ℍ`. -/
def hypLength (c : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ‖deriv c t‖ₑ / ENNReal.ofReal (c t).im

/-- §30.1: the Poincaré length of a closed curve `α` on `S = ℍ/G` (the length of any of its lifts
to `ℍ`, in the metric `|dz|/Im z`).

The lift is required to be **Lipschitz** on `[0,1]`, not merely continuous.  `hypLength` integrates
`deriv c`, which is junk `0` off the differentiable set; a singular reparametrisation of a genuine
lift (a Cantor-function change of variable) is a continuous lift of the same loop with `deriv = 0`
almost everywhere, so with `ContinuousOn` the infimum was `0` for every loop and
`freeHomotopyLength ≡ 0`.  Restricting to Lipschitz lifts loses nothing: the shortest curve in the
class is a smooth geodesic, and any rectifiable curve reparametrises by arclength to a Lipschitz one.
Same convention as `IsPathIn` (§14) and `IsPhiGeodesic` (§25).  See the README Corrections. -/
def poincareLengthLoop {S : Type u} [TopologicalSpace S] (p : UpperHalfPlane → S) (α : Loop S) : ℝ≥0∞ :=
  ⨅ (c : ℝ → ℂ) (_ : (∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1)) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ h : 0 < (c t).im, p ⟨c t, h⟩ = α.2.extend t), hypLength c

/-- Two loops `α`, `β` (with possibly different base points) are freely homotopic. -/
def FreelyHomotopic {S : Type u} [TopologicalSpace S] (α β : Loop S) : Prop :=
  ∃ H : C(unitInterval × unitInterval, S), (∀ t, H (0, t) = α.2 t) ∧ (∀ t, H (1, t) = β.2 t) ∧
    ∀ s, H (s, 0) = H (s, 1)

/-- §30.1: `l[α]`, the length of the shortest curve in the free homotopy class of the closed
curve `α`, for the Poincaré metric of `S = ℍ/G`. -/
def freeHomotopyLength {S : Type u} [TopologicalSpace S] (p : UpperHalfPlane → S) (α : Loop S) : ℝ≥0∞ :=
  ⨅ (β : Loop S) (_ : FreelyHomotopic α β), poincareLengthLoop p β

/-- §30.1: the length spectrum `{l[αₙ]}` of `S`, for a sequence `αₙ` of closed curves representing
all elements of `π₁(S)`. -/
def lengthSpectrumSeq {S : Type u} [TopologicalSpace S] (p : UpperHalfPlane → S) (α : ℕ → Loop S) : ℕ → ℝ≥0∞ :=
  fun n => freeHomotopyLength p (α n)

/-- The trace of `γ ∈ SL(2, ℝ)`. -/
def slTrace (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ := γ 0 0 + γ 1 1

/-- The translation length `ln λ²` of a hyperbolic element, `λ` its larger eigenvalue
(`λ = (|tr γ| + √(tr² γ - 4))/2`). -/
def translationLength (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ :=
  2 * Real.log ((|slTrace γ| + Real.sqrt (slTrace γ ^ 2 - 4)) / 2)

/-- The length spectrum of a Fuchsian group as a set: the translation lengths of its hyperbolic
elements. -/
def lengthSpectrum (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℝ :=
  {ℓ | ∃ γ ∈ Γ, 2 < |slTrace γ| ∧ ℓ = translationLength γ}

/-! ## §30.2 Lemmas -/

/-- §30.2: `γ ∈ G` covers the closed curve `α ⊆ S`: the lift of `α` from a point `z₀` over its
initial point ends at `γ(z₀)`. -/
def Covers {S : Type u} [TopologicalSpace S] (p : UpperHalfPlane → S) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (α : Loop S) : Prop :=
  ∃ c : ℝ → UpperHalfPlane, ContinuousOn c (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, p (c t) = α.2.extend t) ∧
    c 1 = γ • c 0

/-- `γ ∈ SL(2, ℝ)` is parabolic: `|tr γ| = 2`, `γ ≠ ±I`. -/
def IsParabolic (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop := |slTrace γ| = 2 ∧ γ ≠ 1 ∧ γ ≠ -1

/-- `γ ∈ SL(2, ℝ)` is hyperbolic: `|tr γ| > 2`. -/
def IsHyperbolic (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop := 2 < |slTrace γ|

/-- §30.2 (穿孔点): `U ⊆ S` is a neighbourhood of a puncture: `U` is conformally equivalent to
`{0 < |z| < 1}` by `φ`, and `z → 0` corresponds to leaving every compact subset of `S`. -/
def IsPunctureNbhd {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (U : Set S) (φ : S → ℂ) : Prop :=
  IsOpen U ∧ InjOn φ U ∧ φ '' U = puncturedDisc ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U ∧
    ∀ K : Set S, IsCompact K → ∃ r > 0, ∀ x ∈ U, ‖φ x‖ < r → x ∉ K

/-- The `n`-th power of a loop (`n ∈ ℕ`), by concatenation. -/
def loopNatPow {S : Type u} [TopologicalSpace S] (β : Loop S) : ℕ → Path β.1 β.1
  | 0 => Path.refl β.1
  | n + 1 => (loopNatPow β n).trans β.2

/-- The `n`-th power of a loop (`n ∈ ℤ`), negative powers using the reversed loop. -/
def loopPow {S : Type u} [TopologicalSpace S] (β : Loop S) (n : ℤ) : Loop S :=
  if 0 ≤ n then ⟨β.1, loopNatPow β n.toNat⟩ else ⟨β.1, loopNatPow ⟨β.1, β.2.symm⟩ (-n).toNat⟩


/-- The trace of `SL(2, ℝ)` is a conjugation invariant. -/
theorem slTrace_conj (A γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slTrace (A * γ * A⁻¹) = slTrace γ := by
  have htr : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      slTrace g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) := fun g => by
    simp [slTrace, Matrix.trace_fin_two]
  rw [htr, htr, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

/-- The translation length in terms of `arsinh`: `ln λ² = 2 arsinh (√(tr² - 4)/2)`. -/
theorem translationLength_eq_arsinh {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h4 : 0 ≤ slTrace γ ^ 2 - 4) :
    translationLength γ = 2 * Real.arsinh (√(slTrace γ ^ 2 - 4) / 2) := by
  rw [translationLength, Real.arsinh]
  have hs : √(1 + (√(slTrace γ ^ 2 - 4) / 2) ^ 2) = |slTrace γ| / 2 := by
    rw [div_pow, Real.sq_sqrt h4,
      show 1 + (slTrace γ ^ 2 - 4) / 2 ^ 2 = (|slTrace γ| / 2) ^ 2 by rw [div_pow, sq_abs]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hs]
  congr 2
  ring

/-- The displacement of `τ` under `γ = (a b; c d)`:
`d(τ, γτ) = 2 arsinh (|c τ² + (d - a) τ - b| / (2 Im τ))`, and the identity
`|c τ² + (d - a) τ - b|² = (Im τ)² (tr² - 4) + (c |τ|² + (d - a) Re τ - b)²`. -/
theorem dist_smul_eq_arsinh (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    dist τ (γ • τ) = 2 * Real.arsinh (‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ -
      (γ 0 1 : ℂ)‖ / (2 * τ.im)) ∧
    ‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - (γ 0 1 : ℂ)‖ ^ 2 =
      τ.im ^ 2 * (slTrace γ ^ 2 - 4) +
        (γ 1 0 * (τ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ : ℂ).re - γ 0 1 + γ 1 0 * τ.im ^ 2) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, γ 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, γ 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, γ 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, γ 1 1 = d := ⟨_, rfl⟩
  have hdet : a * d - b * c = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two, ha, hb, hc, hd] at h
    exact h
  have htr : slTrace γ = a + d := by rw [slTrace, ha, hd]
  rw [ha, hb, hc, hd, htr]
  have hy : 0 < τ.im := τ.im_pos
  obtain ⟨z, hz⟩ : ∃ z : ℂ, (τ : ℂ) = z := ⟨_, rfl⟩
  have hzim : z.im = τ.im := by rw [← hz, UpperHalfPlane.coe_im]
  rw [hz]
  have hD : (c : ℂ) * z + d ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, sub_zero] at him hre
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 him with h | h
      · exact h
      · rw [hzim] at h
        linarith
    rw [hc0, zero_mul, zero_add] at hre
    rw [hc0, hre] at hdet
    simp at hdet
  have hcoe : ((γ • τ : UpperHalfPlane) : ℂ) = (a * z + b) / (c * z + d) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self_apply, ha, hb, hc, hd, hz]
  have hN : 0 < Complex.normSq ((c : ℂ) * z + d) := Complex.normSq_pos.2 hD
  have him' : (γ • τ).im = τ.im / Complex.normSq ((c : ℂ) * z + d) := by
    rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im, div_sub_div_same]
    congr 1
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    rw [hzim]
    linear_combination τ.im * hdet
  have hnormD : ‖(c : ℂ) * z + d‖ ≠ 0 := norm_ne_zero_iff.2 hD
  have hdistC : dist z ((a * z + b) / (c * z + d)) =
      ‖(c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b‖ / ‖(c : ℂ) * z + d‖ := by
    rw [dist_eq_norm, show z - (a * z + b) / (c * z + d) =
      ((c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b) / (c * z + d) by
        rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]; ring, norm_div]
  have hsqrt : √(τ.im * (τ.im / Complex.normSq ((c : ℂ) * z + d))) =
      τ.im / ‖(c : ℂ) * z + d‖ := by
    rw [Complex.normSq_eq_norm_sq, show τ.im * (τ.im / ‖(c : ℂ) * z + d‖ ^ 2) =
      (τ.im / ‖(c : ℂ) * z + d‖) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  refine ⟨?_, ?_⟩
  · rw [UpperHalfPlane.dist_eq, him', ← hz, hcoe, hz, hdistC, hsqrt]
    congr 2
    field_simp
  · rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, zero_mul, add_zero, sub_zero]
    rw [hzim]
    linear_combination (-4 * τ.im ^ 2) * hdet

/-- Conjugating the translation `γ₁ : z ↦ z + 1`: `g γ₁ g⁻¹ = (1 - ac, a²; -c², 1 + ac)` for
`g = (a b; c d)`. -/
theorem conj_translation_entries {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * γ₁ * g⁻¹) 0 0 = 1 - g 0 0 * g 1 0 ∧ (g * γ₁ * g⁻¹) 0 1 = g 0 0 ^ 2 ∧
      (g * γ₁ * g⁻¹) 1 0 = -(g 1 0 ^ 2) ∧ (g * γ₁ * g⁻¹) 1 1 = 1 + g 0 0 * g 1 0 := by
  obtain ⟨e00, e01, e10, e11⟩ := h₁
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]
  simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

/-- §30.2 (the proof of Lemma 30.1): for a parabolic `γ₁ : z ↦ z + 1` in a Fuchsian group `G`,
every `β ∈ G` not a power of `γ₁` has `|c| ≥ 1`, hence `β(D) ∩ D = ∅` for `D = {Im z > 1}`, and
`G(D)/G ≅ D/⟨γ₁⟩` is a punctured disc.

*Correction.*  The hypothesis `hstab` (`γ₁` generates the stabilizer of `∞` in `Γ`, up to `±`) is
implicit in the book and is needed: for `Γ = ⟨z ↦ z + 1/2⟩` (a Fuchsian group), `γ₁ : z ↦ z + 1`
lies in `Γ`, and `β : z ↦ z + 1/2` is not `±γ₁ⁿ` but has `β 1 0 = 0`, so `1 ≤ |β 1 0|` fails.
With `hstab` the first conjunct is Shimizu's lemma.

Proof: `hstab` and `hnot` force `c = β 1 0 ≠ 0`.  Suppose `|c| < 1`.  The conjugates
`βₙ₊₁ = βₙ γ₁ βₙ⁻¹ ∈ Γ` satisfy `β γ₁ β⁻¹ = (1 - ac, a²; -c², 1 + ac)`
(`conj_translation_entries`).
* The lower-left entries give `|cₙ| = |c|^(2ⁿ)`, so the `βₙ` are pairwise distinct.
* The top-left entries satisfy `aₙ₊₁ = 1 - aₙcₙ`, so they stay bounded, and hence all entries
  stay bounded.
* By the displacement formula `dist_smul_eq_arsinh`, every `βₙ i` then lies in one closed ball
  around `i`.
Infinitely many distinct group elements therefore move a point of that compact ball into it,
which contradicts `IsFuchsian`.  The second conjunct follows from
`Im (βτ) = Im τ / |cτ + d|² ≤ 1/(c² Im τ) < 1`. -/
theorem parabolic_horoball_disjoint {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ₁ : γ₁ ∈ Γ) (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1)
    (hstab : ∀ β ∈ Γ, β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n)
    {β : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hβ : β ∈ Γ) (hnot : ∀ n : ℤ, β ≠ γ₁ ^ n ∧ β ≠ -γ₁ ^ n) :
    1 ≤ |β 1 0| ∧ ∀ τ : UpperHalfPlane, 1 < (τ : ℂ).im → ((β • τ : UpperHalfPlane) : ℂ).im ≤ 1 := by
  have hc0 : β 1 0 ≠ 0 := by
    intro h0
    obtain ⟨n, hn | hn⟩ := hstab β hβ h0
    · exact (hnot n).1 hn
    · exact (hnot n).2 hn
  have hc1 : 1 ≤ |β 1 0| := by
    by_contra hlt
    rw [not_le] at hlt
    have hcpos : 0 < |β 1 0| := abs_pos.2 hc0
    obtain ⟨seq, hseq0, hseqS⟩ : ∃ seq : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ,
        seq 0 = β ∧ ∀ n, seq (n + 1) = seq n * γ₁ * (seq n)⁻¹ :=
      ⟨fun n => Nat.rec β (fun _ g => g * γ₁ * g⁻¹) n, rfl, fun _ => rfl⟩
    have hmem : ∀ n, seq n ∈ Γ := by
      intro n
      induction n with
      | zero => rw [hseq0]; exact hβ
      | succ n ih => rw [hseqS]; exact Γ.mul_mem (Γ.mul_mem ih hγ₁) (Γ.inv_mem ih)
    have hcabs : ∀ n, |seq n 1 0| = |β 1 0| ^ (2 ^ n) := by
      intro n
      induction n with
      | zero => rw [hseq0, pow_zero, pow_one]
      | succ n ih =>
        rw [hseqS, (conj_translation_entries h₁ (seq n)).2.2.1, abs_neg, abs_pow, ih, ← pow_mul,
          pow_succ]
    have hcle : ∀ n, |seq n 1 0| ≤ |β 1 0| := fun n => by
      rw [hcabs]
      exact pow_le_of_le_one (abs_nonneg _) hlt.le (pow_ne_zero n two_ne_zero)
    -- the top-left entries stay bounded
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max |β 0 0| (1 / (1 - |β 1 0|)) := ⟨_, rfl⟩
    have hM1 : 1 + M * |β 1 0| ≤ M := by
      have h1 : 1 / (1 - |β 1 0|) ≤ M := hMdef ▸ le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at h1
      linarith
    have hM0 : 0 ≤ M := hMdef ▸ (abs_nonneg _).trans (le_max_left _ _)
    have habound : ∀ n, |seq n 0 0| ≤ M := by
      intro n
      induction n with
      | zero => rw [hseq0, hMdef]; exact le_max_left _ _
      | succ n ih =>
        rw [hseqS, (conj_translation_entries h₁ (seq n)).1]
        calc |1 - seq n 0 0 * seq n 1 0| ≤ 1 + |seq n 0 0| * |seq n 1 0| := by
              rw [← abs_mul]
              exact (abs_sub _ _).trans (by rw [abs_one])
          _ ≤ 1 + M * |β 1 0| :=
              add_le_add le_rfl (mul_le_mul ih (hcle n) (abs_nonneg _) hM0)
          _ ≤ M := hM1
    -- all entries stay bounded
    obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = M + (|β 0 1| + M ^ 2) + 1 + (|β 1 1| + (1 + M)) := ⟨_, rfl⟩
    have hBbound : ∀ n, |seq n 0 0| + |seq n 0 1| + |seq n 1 0| + |seq n 1 1| ≤ B := by
      intro n
      cases n with
      | zero =>
        rw [hseq0, hBdef]
        have ha := habound 0
        rw [hseq0] at ha
        nlinarith [abs_nonneg (β 0 1), abs_nonneg (β 1 1), sq_nonneg M]
      | succ n =>
        obtain ⟨e00, e01, e10, e11⟩ := conj_translation_entries h₁ (seq n)
        have ha := habound (n + 1)
        have hc := hcle (n + 1)
        rw [hseqS] at ha hc ⊢
        rw [e01, e11, hBdef]
        have h01 : |seq n 0 0 ^ 2| ≤ M ^ 2 := by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (habound n) 2
        have h11 : |1 + seq n 0 0 * seq n 1 0| ≤ 1 + M := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_one, abs_mul]
          have := habound n
          have := hcle n
          nlinarith [abs_nonneg (seq n 0 0), abs_nonneg (seq n 1 0)]
        nlinarith [abs_nonneg (β 0 1), abs_nonneg (β 1 1)]
    -- the orbit of `i` stays in a fixed closed ball
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * Real.arsinh (B / 2) := ⟨_, rfl⟩
    have hB0 : 0 ≤ B := le_trans (by positivity) (hBbound 0)
    have hR0 : 0 ≤ R := by
      rw [hRdef]
      exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.2 (by positivity))
    have hdist : ∀ n, dist UpperHalfPlane.I (seq n • UpperHalfPlane.I) ≤ R := by
      intro n
      rw [(dist_smul_eq_arsinh (seq n) UpperHalfPlane.I).1, hRdef, UpperHalfPlane.coe_I,
        UpperHalfPlane.I_im, mul_one]
      refine mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.2 ?_) (by norm_num)
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, mul_one,
        ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have := hBbound n
      have := abs_sub (seq n 1 1) (seq n 0 0)
      linarith
    have hK : IsCompact (closedBall UpperHalfPlane.I R) := isCompact_closedBall _ _
    have hT := hΓ _ hK
    have hrange : range seq ⊆ {g ∈ Γ | ((g • ·) '' closedBall UpperHalfPlane.I R ∩
        closedBall UpperHalfPlane.I R).Nonempty} := by
      rintro _ ⟨n, rfl⟩
      exact ⟨hmem n, seq n • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self hR0, rfl⟩,
        mem_closedBall.2 (by rw [dist_comm]; exact hdist n)⟩
    have hanti : StrictAnti fun n : ℕ => |β 1 0| ^ (2 ^ n) :=
      (pow_right_strictAnti₀ hcpos hlt).comp_strictMono
        (fun m n h => Nat.pow_lt_pow_right (by norm_num) h)
    have hinj : Function.Injective seq := by
      intro m n hmn
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => |g 1 0|) hmn
      simp only [hcabs] at h
      exact hanti.injective h
    exact Set.infinite_range_of_injective hinj (hT.subset hrange)
  refine ⟨hc1, fun τ hτ => ?_⟩
  have hdet : β 0 0 * β 1 1 - β 0 1 * β 1 0 = 1 := by
    have h := β.det_coe
    rwa [Matrix.det_fin_two] at h
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have hD : (β 1 0 : ℂ) * τ + β 1 1 ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.zero_im] at him
    rcases mul_eq_zero.1 him with h | h
    · exact hc0 h
    · linarith
  have hcoe : ((β • τ : UpperHalfPlane) : ℂ) = (β 0 0 * τ + β 0 1) / (β 1 0 * τ + β 1 1) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self_apply]
  have hN : 0 < Complex.normSq ((β 1 0 : ℂ) * τ + β 1 1) := Complex.normSq_pos.2 hD
  rw [hcoe, Complex.div_im, div_sub_div_same]
  have hnum : ((β 0 0 : ℂ) * τ + β 0 1).im * ((β 1 0 : ℂ) * τ + β 1 1).re -
      ((β 0 0 : ℂ) * τ + β 0 1).re * ((β 1 0 : ℂ) * τ + β 1 1).im = (τ : ℂ).im := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    linear_combination (τ : ℂ).im * hdet
  rw [hnum, div_le_one hN, Complex.normSq_apply]
  have hDim : ((β 1 0 : ℂ) * τ + β 1 1).im = β 1 0 * (τ : ℂ).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
  rw [hDim]
  have hc2 : 1 ≤ β 1 0 ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have h1 : (τ : ℂ).im ≤ (τ : ℂ).im ^ 2 := by nlinarith
  have h2 : (τ : ℂ).im ^ 2 ≤ β 1 0 ^ 2 * (τ : ℂ).im ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hc2
  nlinarith [mul_self_nonneg ((β 1 0 : ℂ) * τ + β 1 1).re]

/-- The derivative of the Cayley transform: `C'(z) = 2i/(z + i)²`. -/
theorem hasDerivAt_cayley {z : ℂ} (hz : z + I ≠ 0) :
    HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - I) 1 z := by simpa using (hasDerivAt_id z).sub_const I
  have h2 : HasDerivAt (fun w : ℂ => w + I) 1 z := by simpa using (hasDerivAt_id z).add_const I
  have h3 := h1.div h2 hz
  have hfun : cayley = fun w : ℂ => (w - I) / (w + I) := rfl
  rw [hfun]
  convert h3 using 1
  congr 1
  ring

/-- `1 - |C(z)|² = 4 Im z/|z + i|²`: the Cayley transform carries the disc density `2/(1-|w|²)`
to the half-plane density `1/Im z`. -/
theorem one_sub_norm_sq_cayley {z : ℂ} (hz : 0 < z.im) :
    1 - ‖cayley z‖ ^ 2 = 4 * z.im / normSq (z + I) := by
  have hden := cayley_den_ne_zero hz
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  rw [← Complex.normSq_eq_norm_sq, cayley, normSq_div, eq_div_iff hpos.ne', sub_mul, one_mul,
    div_mul_cancel₀ _ hpos.ne']
  linarith [normSq_cayley_key z]

/-- The inverse Cayley transform is holomorphic on the disc. -/
theorem differentiableOn_cayleyInv : DifferentiableOn ℂ cayleyInv unitDisc := by
  intro w hw
  have hden := cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
  refine DifferentiableAt.differentiableWithinAt ?_
  have hfun : cayleyInv = fun v : ℂ => I * (1 + v) / (1 - v) := rfl
  rw [hfun]
  exact (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) w).div
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - v) w) hden

/-- **Schwarz–Pick for the unit disc**: a holomorphic self-map of `Δ` does not increase the
Poincaré metric, `|f'(a)| (1 - |a|²) ≤ 1 - |f(a)|²`.

Mathlib's Schwarz lemma (`Complex.norm_deriv_le_one_of_mapsTo_ball`) bounds the derivative only
at the *centre* of the ball, and Mathlib has no Schwarz–Pick form.  Conjugating by Blaschke
factors supplies it: `g = M_{f a} ∘ f ∘ M_{-a}` satisfies `g 0 = 0`, because `M_{-a} 0 = a` and
`M_b b = 0`, so Schwarz applies at the centre; the chain rule gives
`g'(0) = (1 - |f a|²)⁻¹ · f'(a) · (1 - |a|²)`, and `‖g'(0)‖ ≤ 1` is the assertion.  Stated
multiplicatively to avoid dividing.  (Belongs with `Lemmas/DiscAutomorphism.lean`; kept here only
to stay out of a concurrently edited file.) -/
theorem schwarz_pick_unitDisc {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) {a : ℂ} (ha : a ∈ unitDisc) :
    ‖deriv f a‖ * (1 - ‖a‖ ^ 2) ≤ 1 - ‖f a‖ ^ 2 := by
  have hna : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hnna : ‖(-a)‖ < 1 := by rwa [norm_neg]
  have hnb : ‖f a‖ < 1 := mem_ball_zero_iff.mp (hmaps ha)
  have hz0 : ‖(0 : ℂ)‖ < 1 := by norm_num
  have hpa : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hpb : (0 : ℝ) < 1 - ‖f a‖ ^ 2 := by nlinarith [norm_nonneg (f a)]
  -- `M_{-a} 0 = a` and `M_{f a} (f a) = 0`, so the conjugate fixes the origin
  have hb0 : blaschke (-a) 0 = a := by simp [blaschke]
  have hbb : blaschke (f a) (f a) = 0 := by simp [blaschke]
  have hsub : ∀ z ∈ unitDisc, blaschke (-a) z ∈ unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hnna (mem_ball_zero_iff.mp hz))
  have hg0 : blaschke (f a) (f (blaschke (-a) 0)) = 0 := by
    rw [hb0]
    exact hbb
  have hmapsg : MapsTo (fun z => blaschke (f a) (f (blaschke (-a) z))) unitDisc unitDisc :=
    fun z hz => mem_ball_zero_iff.mpr
      (blaschke_mem_unitDisc hnb (mem_ball_zero_iff.mp (hmaps (hsub z hz))))
  have hdg : DifferentiableOn ℂ (fun z => blaschke (f a) (f (blaschke (-a) z))) unitDisc :=
    (differentiableOn_blaschke hnb).comp (hf.comp (differentiableOn_blaschke hnna) hsub)
      (fun z hz => hmaps (hsub z hz))
  -- Schwarz at the centre
  have hschwarz : ‖deriv (fun z => blaschke (f a) (f (blaschke (-a) z))) 0‖ ≤ 1 := by
    refine Complex.norm_deriv_le_one_of_mapsTo_ball hdg ?_ one_pos
    rw [hg0]
    exact fun z hz => ball_subset_closedBall (hmapsg hz)
  -- the chain rule at `0`
  have hfa : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  have h1 : HasDerivAt (blaschke (-a)) (1 - a * conj a) 0 := by
    have h := hasDerivAt_blaschke hnna hz0
    simpa using h
  have hfa' : HasDerivAt f (deriv f a) (blaschke (-a) 0) := by rw [hb0]; exact hfa
  have hk : HasDerivAt (fun z => f (blaschke (-a) z)) (deriv f a * (1 - a * conj a)) 0 :=
    hfa'.comp 0 h1
  have h3 : HasDerivAt (blaschke (f a))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2) (f (blaschke (-a) 0)) := by
    rw [hb0]
    exact hasDerivAt_blaschke hnb hnb
  have hchain0 : HasDerivAt (blaschke (f a) ∘ fun z => f (blaschke (-a) z))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2 *
        (deriv f a * (1 - a * conj a))) 0 := h3.comp 0 hk
  have hchain : HasDerivAt (fun z => blaschke (f a) (f (blaschke (-a) z)))
      ((1 - f a * conj (f a)) / (1 - conj (f a) * f a) ^ 2 *
        (deriv f a * (1 - a * conj a))) 0 := hchain0
  -- turn the three `1 - z z̄` factors into real numbers
  have hcb : (1 : ℂ) - f a * conj (f a) = ((1 - ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hcb' : (1 : ℂ) - conj (f a) * f a = ((1 - ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm]; exact hcb
  have hca : (1 : ℂ) - a * conj a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hchain.deriv, hcb, hcb', hca, norm_mul, norm_mul, norm_div, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hpa, abs_of_pos hpb, div_mul_eq_mul_div,
    div_le_one (by positivity)] at hschwarz
  nlinarith [hschwarz, hpb, norm_nonneg (deriv f a)]

/-- §30.2 (the classical Schwarz lemma behind it): a holomorphic self-map of `ℍ` does not increase
the Poincaré metric: `|F'(z)|/Im F(z) ≤ 1/Im z`. -/
theorem schwarz_pick_upperHalf {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalf) (hmaps : MapsTo F upperHalf upperHalf)
    {z : ℂ} (hz : z ∈ upperHalf) : ‖deriv F z‖ / (F z).im ≤ 1 / z.im := by
  have hzim : (0 : ℝ) < z.im := hz
  have hFz : F z ∈ upperHalf := hmaps hz
  have hFzim : (0 : ℝ) < (F z).im := hFz
  have hpz : (0 : ℝ) < normSq (z + I) := normSq_pos.mpr (cayley_den_ne_zero hzim)
  have hpF : (0 : ℝ) < normSq (F z + I) := normSq_pos.mpr (cayley_den_ne_zero hFzim)
  -- `f = C ∘ F ∘ C⁻¹` is a holomorphic self-map of the disc
  have hinv : ∀ w ∈ unitDisc, cayleyInv w ∈ upperHalf := fun w hw =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
  have hfmaps : MapsTo (fun w => cayley (F (cayleyInv w))) unitDisc unitDisc := fun w hw =>
    cayley_mem_unitDisc (hmaps (hinv w hw))
  have hfdiff : DifferentiableOn ℂ (fun w => cayley (F (cayleyInv w))) unitDisc :=
    isConformalOnto_cayley.1.comp (hF.comp differentiableOn_cayleyInv hinv)
      (fun w hw => hmaps (hinv w hw))
  have hcz : cayley z ∈ unitDisc := cayley_mem_unitDisc hzim
  have hpick := schwarz_pick_unitDisc hfdiff hfmaps hcz
  have hval : cayley (F (cayleyInv (cayley z))) = cayley (F z) := by rw [cayleyInv_cayley hzim]
  -- differentiate `f ∘ C = C ∘ F` at `z` to relate `f'(C z)` to `F'(z)`;
  -- this avoids ever differentiating `C⁻¹`
  have hfat : DifferentiableAt ℂ (fun w => cayley (F (cayleyInv w))) (cayley z) :=
    hfdiff.differentiableAt (isOpen_ball.mem_nhds hcz)
  have hFat : DifferentiableAt ℂ F z := hF.differentiableAt (isOpen_upperHalf.mem_nhds hz)
  have hd1 : HasDerivAt (fun w => cayley (F (cayleyInv (cayley w))))
      (deriv (fun w => cayley (F (cayleyInv w))) (cayley z) * (2 * I / (z + I) ^ 2)) z :=
    hfat.hasDerivAt.comp z (hasDerivAt_cayley (cayley_den_ne_zero hzim))
  have hev : (fun w => cayley (F (cayleyInv (cayley w)))) =ᶠ[nhds z] fun w => cayley (F w) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    rw [cayleyInv_cayley hw]
  have hd1' : HasDerivAt (fun w => cayley (F w))
      (deriv (fun w => cayley (F (cayleyInv w))) (cayley z) * (2 * I / (z + I) ^ 2)) z :=
    hd1.congr_of_eventuallyEq hev.symm
  have hd2 : HasDerivAt (fun w => cayley (F w)) (2 * I / (F z + I) ^ 2 * deriv F z) z :=
    (hasDerivAt_cayley (cayley_den_ne_zero hFzim)).comp z hFat.hasDerivAt
  have hkey := hd2.unique hd1'
  -- pass to norms
  have hnormz : ‖(2 : ℂ) * I / (z + I) ^ 2‖ = 2 / normSq (z + I) := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_pow, ← Complex.normSq_eq_norm_sq]
    norm_num
  have hnormF : ‖(2 : ℂ) * I / (F z + I) ^ 2‖ = 2 / normSq (F z + I) := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_pow, ← Complex.normSq_eq_norm_sq]
    norm_num
  have hnk : 2 / normSq (F z + I) * ‖deriv F z‖
      = ‖deriv (fun w => cayley (F (cayleyInv w))) (cayley z)‖ * (2 / normSq (z + I)) := by
    have h := congrArg norm hkey
    rwa [norm_mul, norm_mul, hnormz, hnormF] at h
  -- substitute the two density identities and clear denominators
  rw [hval, one_sub_norm_sq_cayley hzim, one_sub_norm_sq_cayley hFzim] at hpick
  rw [div_le_div_iff₀ hFzim hzim]
  field_simp at hnk hpick
  nlinarith [hnk, hpick, hpz, hpF, hzim, hFzim, norm_nonneg (deriv F z),
    mul_pos hpz hzim, mul_pos hpF hFzim]

/-- A curve `c`, Lipschitz on `[0, 1]`, as an `LRCurve` (locally Lipschitz, with the same constant). -/
def s30a_lr (c : ℝ → ℂ) (hc : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1)) : LRCurve :=
  ⟨c, fun _ hx => ⟨hc.choose, Icc 0 1, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), hc.choose_spec⟩⟩

/-- A holomorphic covering `p : ℍ → S` is conformal in the chart at `p w₀` on a neighbourhood of `w₀` (the data
behind S23 `h23l_chart_proj`). -/
theorem s30a_chart_conformal {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {p : UpperHalfPlane → S} (hcov : IsCoveringMap p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    (w₀ : UpperHalfPlane) :
    ∃ U : Set ℂ, IsOpen U ∧ (w₀ : ℂ) ∈ U ∧ U ⊆ upperHalf ∧
      IsConformalOnto (fun z => chartAt ℂ (p w₀) (p (UpperHalfPlane.ofComplex z))) U
        ((fun z => chartAt ℂ (p w₀) (p (UpperHalfPlane.ofComplex z))) '' U) := by
  obtain ⟨e, hτe, hpe⟩ := hcov.isLocalHomeomorph w₀
  set W : Set UpperHalfPlane := e.source ∩ p ⁻¹' (chartAt ℂ (p w₀)).source
  have hWo : IsOpen W := e.open_source.inter
    (hcov.continuous.isOpen_preimage _ (chartAt ℂ (p w₀)).open_source)
  set U : Set ℂ := upperHalf ∩ UpperHalfPlane.ofComplex ⁻¹' W
  have hsrc : UpperHalfPlane.ofComplex.source = upperHalf := by
    ext z
    simp [UpperHalfPlane.ofComplex, upperHalf]
  have hUo : IsOpen U := by
    have h := UpperHalfPlane.ofComplex.isOpen_inter_preimage hWo
    rwa [hsrc] at h
  have hτU : (w₀ : ℂ) ∈ U := by
    refine ⟨w₀.coe_im_pos, ?_⟩
    show UpperHalfPlane.ofComplex (w₀ : ℂ) ∈ W
    rw [UpperHalfPlane.ofComplex_apply]
    exact ⟨hτe, mem_chart_source ℂ (p w₀)⟩
  refine ⟨U, hUo, hτU, fun z hz => hz.1, fun z hz => ?_, fun z hz w hw hzw => ?_, rfl⟩
  · have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun z => chartAt ℂ (p w₀) (p (UpperHalfPlane.ofComplex z))) z :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ (p w₀)) hz.2.2).comp z
        ((hhol _).comp z (UpperHalfPlane.mdifferentiableAt_ofComplex hz.1))
    exact (mdifferentiableAt_iff_differentiableAt.1 h1).differentiableWithinAt
  · have h1 : p (UpperHalfPlane.ofComplex z) = p (UpperHalfPlane.ofComplex w) :=
      (chartAt ℂ (p w₀)).injOn hz.2.2 hw.2.2 hzw
    rw [hpe] at h1
    have h2 := e.injOn hz.2.1 hw.2.1 h1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz.1, UpperHalfPlane.ofComplex_apply_of_im_pos hw.1] at h2
    exact congrArg UpperHalfPlane.coe h2

/-- **The lift of a holomorphic map through a holomorphic covering is holomorphic**: if `p₂ ∘ F = ι ∘ p₁` with `p₁`
holomorphic, `p₂` a holomorphic covering and `ι` holomorphic, then `F`, read in `ℂ`, is holomorphic on `ℍ` (locally
`F = (φ ∘ p₂)⁻¹ ∘ φ ∘ ι ∘ p₁` for a chart `φ`, by `s30a_chart_conformal`). -/
theorem s30a_lift_differentiableOn {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {p₁ : UpperHalfPlane → X} {p₂ : UpperHalfPlane → Y} (hhol₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₁)
    (hcov₂ : IsCoveringMap p₂) (hhol₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₂) {ι : X → Y}
    (hι : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι) {F : UpperHalfPlane → UpperHalfPlane} (hFc : Continuous F)
    (hF : ∀ τ, p₂ (F τ) = ι (p₁ τ)) : DifferentiableOn ℂ (liftToC F) upperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  set τ := UpperHalfPlane.ofComplex z with hτ
  set w₀ := F τ with hw₀
  obtain ⟨U, hUo, hw₀U, -, hconf⟩ := s30a_chart_conformal hcov₂ hhol₂ w₀
  set φ := chartAt ℂ (p₂ w₀)
  set ψ := fun ζ => φ (p₂ (UpperHalfPlane.ofComplex ζ))
  set g := fun ζ => φ (ι (p₁ (UpperHalfPlane.ofComplex ζ)))
  have hg : DifferentiableAt ℂ g z := by
    have hsrc : ι (p₁ τ) ∈ φ.source := by
      rw [← hF]
      exact mem_chart_source ℂ _
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ (p₂ w₀)) hsrc).comp z
        ((hι _).comp z ((hhol₁ _).comp z (UpperHalfPlane.mdifferentiableAt_ofComplex hz')))
    exact mdifferentiableAt_iff_differentiableAt.1 h1
  have hcontF : ContinuousAt (liftToC F) z :=
    (h23l_liftToC_continuousOn hFc).continuousAt (isOpen_upperHalf.mem_nhds hz)
  have hFz : liftToC F z = (w₀ : ℂ) := h23l_liftToC_eq F hz
  have hev : ∀ᶠ ζ in 𝓝 z, liftToC F ζ ∈ U ∧ ζ ∈ upperHalf := by
    have h1 : U ∈ 𝓝 (liftToC F z) := by
      rw [hFz]
      exact hUo.mem_nhds hw₀U
    exact (hcontF.eventually_mem h1).and (isOpen_upperHalf.mem_nhds hz)
  have heq : (fun ζ => Function.invFunOn ψ U (g ζ)) =ᶠ[𝓝 z] liftToC F := by
    filter_upwards [hev] with ζ hζ
    have hψ : ψ (liftToC F ζ) = g ζ := by
      show φ (p₂ (UpperHalfPlane.ofComplex (liftToC F ζ))) = φ (ι (p₁ (UpperHalfPlane.ofComplex ζ)))
      rw [h23l_liftToC_eq F hζ.2, UpperHalfPlane.ofComplex_apply, hF]
    rw [← hψ]
    exact hconf.2.1.leftInvOn_invFunOn hζ.1
  have hinv : DifferentiableAt ℂ (Function.invFunOn ψ U) (g z) := by
    have hgz : g z = ψ (w₀ : ℂ) := by
      show φ (ι (p₁ τ)) = φ (p₂ (UpperHalfPlane.ofComplex (w₀ : ℂ)))
      rw [UpperHalfPlane.ofComplex_apply, hF]
    rw [hgz]
    exact hconf.differentiableAt_invFunOn hUo hw₀U
  exact ((hinv.comp z hg).congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- §30.2 (generalized Schwarz lemma): if `S₁ ⊆ S₂` is a sub-Riemann surface (an open subset,
uniformized by `p₁`) of `S₂` (uniformized by `p₂`), the Poincaré metric of `S₁` dominates that of
`S₂`: every closed curve in `S₁` is at least as long for `S₁` as for `S₂`.  Equality holds only for
`S₁ = S₂`. -/
theorem generalized_schwarz {S₂ : Type u} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [T2Space S₂]
    [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂] (U : TopologicalSpace.Opens S₂) [ConnectedSpace U]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → U} {p₂ : UpperHalfPlane → S₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) (α : Loop U) :
    poincareLengthLoop p₂ ⟨(α.1 : S₂), α.2.map continuous_subtype_val⟩ ≤ poincareLengthLoop p₁ α := by
  obtain ⟨τ₁, hτ₁⟩ := hp₂.2.2.1 ((p₁ UpperHalfPlane.I : U) : S₂)
  obtain ⟨F, hFc, hF, -⟩ := h23l_exists_continuous_lift hp₂.1
    (continuous_subtype_val.comp hp₁.1.continuous) (τ₀ := UpperHalfPlane.I) hτ₁
  have hF' : ∀ τ, p₂ (F τ) = ((p₁ τ : U) : S₂) := hF
  have hhol : DifferentiableOn ℂ (liftToC F) upperHalf :=
    s30a_lift_differentiableOn hp₁.2.1 hp₂.1 hp₂.2.1 (ι := Subtype.val)
      ((contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero) hFc hF'
  have hmaps : MapsTo (liftToC F) upperHalf upperHalf := fun z hz => by
    rw [h23l_liftToC_eq F hz]
    exact (F _).coe_im_pos
  refine le_iInf₂ fun c hc => ?_
  obtain ⟨hK, him, hlift⟩ := hc
  have hpath : IsPathIn upperHalf (c 0) (c 1) (s30a_lr c hK) :=
    ⟨hK, rfl, rfl, by rintro _ ⟨t, ht, rfl⟩; exact him t ht⟩
  obtain ⟨γ', hγ'eq, ⟨hK', -, -, -⟩⟩ := exists_isPathIn_comp isOpen_upperHalf hhol hmaps hpath
  set c₂ : ℝ → ℂ := liftToC F ∘ c with hc₂def
  have him₂ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c₂ t).im := fun t ht => hmaps (him t ht)
  have hK₂ : ∃ K : ℝ≥0, LipschitzOnWith K c₂ (Icc 0 1) := by
    obtain ⟨K', hK'⟩ := hK'
    rw [hγ'eq] at hK'
    exact ⟨K', hK'⟩
  refine (iInf₂_le c₂ ⟨hK₂, him₂, fun t ht h => ?_⟩).trans ?_
  · -- Schwarz–Pick, pointwise a.e.
    obtain ⟨K, hKc⟩ := hK
    have hK1 : LipschitzOnWith K c (uIcc 0 1) := by rwa [uIcc_of_le zero_le_one]
    have hdiff := ae_differentiableAt_of_lipschitzOn hK1
    unfold hypLength
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hdiff] with t ht hd
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hdt : DifferentiableAt ℝ c t := hd (by rw [uIcc_of_le zero_le_one]; exact htI)
    have hy₁ := him t htI
    have hy₂ := him₂ t htI
    have hFd : DifferentiableAt ℂ (liftToC F) (c t) := hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy₁)
    have hchain : deriv c₂ t = deriv (liftToC F) (c t) * deriv c t :=
      (hFd.hasDerivAt.comp t hdt.hasDerivAt).deriv
    have hsp := schwarz_pick_upperHalf hhol hmaps hy₁
    rw [hchain, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos hy₂,
      ← ENNReal.ofReal_div_of_pos hy₁]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul]
    have hb := norm_nonneg (deriv c t)
    calc ‖deriv (liftToC F) (c t)‖ * ‖deriv c t‖ / (c₂ t).im
        = ‖deriv c t‖ * (‖deriv (liftToC F) (c t)‖ / (liftToC F (c t)).im) := by
          simp only [hc₂def, Function.comp_apply]
          ring
      _ ≤ ‖deriv c t‖ * (1 / (c t).im) := mul_le_mul_of_nonneg_left hsp hb
      _ = ‖deriv c t‖ / (c t).im := by ring
  · -- `F ∘ c` lifts `ι ∘ α`
    have e1 : (⟨c₂ t, h⟩ : UpperHalfPlane) = F ⟨c t, him t ht⟩ := by
      apply UpperHalfPlane.ext
      show liftToC F (c t) = _
      rw [h23l_liftToC_eq F (him t ht), UpperHalfPlane.ofComplex_apply_of_im_pos (him t ht)]
    rw [e1, hF', hlift t ht (him t ht)]
    rfl

/-- §30.2: the Poincaré length of the curve `|ζ| = r` in the punctured disc `{0 < |ζ| < 1}` (covered
by `ℍ` via `ζ = e^{iz}`) is `2π/|ln r|`, which tends to `0` as `r → 0`. -/
theorem puncturedDisc_circle_length {r : ℝ} (hr₀ : 0 < r) (hr : r < 1) :
    hypLength (fun t => -Real.log r * I + 2 * π * t) = ENNReal.ofReal (2 * π / |Real.log r|) := by
  have hlogneg : Real.log r < 0 := Real.log_neg hr₀ hr
  have hpos : (0 : ℝ) < -Real.log r := by linarith
  set c : ℝ → ℂ := fun t => -Real.log r * I + 2 * π * t with hc
  -- the imaginary part is the constant `-log r`, and the derivative the constant `2π`
  have him : ∀ t : ℝ, (c t).im = -Real.log r := by
    intro t
    rw [hc]
    simp
  have hd : ∀ t : ℝ, HasDerivAt c (2 * (π : ℂ)) t := by
    intro t
    rw [hc]
    have hfun : (fun s : ℝ => -Real.log r * I + 2 * π * (s : ℂ))
        = fun s : ℝ => (-Real.log r * I) + (s : ℂ) * (2 * (π : ℂ)) := by
      funext s
      ring
    rw [hfun]
    exact (hasDerivAt_ofReal_mul (2 * (π : ℂ)) t).const_add _
  have hnorm : ‖(2 : ℂ) * (π : ℂ)‖ₑ = ENNReal.ofReal (2 * π) := by
    have hcast : (2 : ℂ) * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  -- the integrand is therefore constant
  have hconst : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖deriv c t‖ₑ / ENNReal.ofReal (c t).im
        = ENNReal.ofReal (2 * π) / ENNReal.ofReal (-Real.log r) := by
    intro t _
    rw [(hd t).deriv, him t, hnorm]
  rw [hypLength, setLIntegral_congr_fun measurableSet_Ioo hconst, setLIntegral_const,
    Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, abs_of_neg hlogneg,
    ENNReal.ofReal_div_of_pos hpos]

/-- §30.2: a hyperbolic `γ : z ↦ λ² z` (`λ > 1`) covers curves whose free homotopy class has shortest
length `ln λ²`: the segment of the imaginary axis from `i` to `λ² i` has length `ln λ²` and
projects to a closed curve covered by `γ`, and no curve covered by `γ` is shorter. -/
theorem hyperbolic_axis_segment {lam : ℝ} (hlam : 1 < lam) :
    hypLength (fun t => (1 + t * (lam ^ 2 - 1)) * I) = ENNReal.ofReal (Real.log (lam ^ 2)) := by
  have hApos : (0 : ℝ) < lam ^ 2 - 1 := by nlinarith
  set A : ℝ := lam ^ 2 - 1 with hA
  set c : ℝ → ℂ := fun t => (1 + t * (lam ^ 2 - 1)) * I with hc
  have hden : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + t * A := by
    intro t ht
    have h0 := ht.1
    nlinarith
  -- imaginary part and derivative of the vertical segment
  have him : ∀ t : ℝ, (c t).im = 1 + t * A := by
    intro t
    have hcoef : (1 : ℂ) + (t : ℂ) * ((lam : ℂ) ^ 2 - 1) = ((1 + t * A : ℝ) : ℂ) := by
      rw [hA]; push_cast; ring
    rw [hc]
    simp only [hcoef, Complex.mul_I_im, Complex.ofReal_re]
  have hd : ∀ t : ℝ, HasDerivAt c ((A : ℂ) * I) t := by
    intro t
    rw [hc]
    have hfun : (fun s : ℝ => (1 + (s : ℂ) * ((lam : ℂ) ^ 2 - 1)) * I)
        = fun s : ℝ => I + (s : ℂ) * ((A : ℂ) * I) := by
      funext s
      rw [hA]
      push_cast
      ring
    rw [hfun]
    exact (hasDerivAt_ofReal_mul ((A : ℂ) * I) t).const_add _
  have hnorm : ‖(A : ℂ) * I‖ₑ = ENNReal.ofReal A := by
    rw [← ofReal_norm, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hApos]
  -- the integrand is `A / (1 + tA)`
  have hconst : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖deriv c t‖ₑ / ENNReal.ofReal (c t).im = ENNReal.ofReal (A / (1 + t * A)) := by
    intro t ht
    rw [(hd t).deriv, him t, hnorm,
      ENNReal.ofReal_div_of_pos (hden t (Ioo_subset_Icc_self ht))]
  -- continuity, hence integrability, of that integrand
  have hcont : ContinuousOn (fun t : ℝ => A / (1 + t * A)) (Icc (0 : ℝ) 1) := by
    refine continuousOn_const.div (continuousOn_const.add
      (continuousOn_id.mul continuousOn_const)) ?_
    intro t ht
    exact (hden t ht).ne'
  have hintOn : IntegrableOn (fun t : ℝ => A / (1 + t * A)) (Ioo (0 : ℝ) 1) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun t : ℝ => A / (1 + t * A) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact le_of_lt (div_pos hApos (hden t (Ioo_subset_Icc_self ht)))
  -- the Bochner integral, by the fundamental theorem of calculus
  have hval : ∫ t in Ioo (0 : ℝ) 1, A / (1 + t * A) = Real.log (lam ^ 2) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Real.log (1 + s * A)) (A / (1 + t * A)) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hinner : HasDerivAt (fun s : ℝ => 1 + s * A) A t := by
        simpa using ((hasDerivAt_id t).mul_const A).const_add (1 : ℝ)
      exact hinner.log (hden t ht).ne'
    have hii : IntervalIntegrable (fun t : ℝ => A / (1 + t * A)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le zero_le_one]
      exact hcont
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii, one_mul, zero_mul,
      add_zero, Real.log_one, sub_zero, hA]
    congr 1
    ring
  rw [hypLength, setLIntegral_congr_fun measurableSet_Ioo hconst,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintOn hnn, hval]

/-- §30.2: the translation length is the minimal displacement `inf_τ d(τ, γτ)`, attained on the
axis of `γ`; and every real conjugation preserves it.

For `γ = (a b; c d)` and `Q(τ) = cτ² + (d - a)τ - b`, the distance formula of the upper
half-plane gives `d(τ, γτ) = 2 arsinh (|Q(τ)|/(2 Im τ))` (`dist_smul_eq_arsinh`).
Since `ad - bc = 1`, `|Q(τ)|² = (Im τ)² (tr² - 4) + (c|τ|² + (d - a) Re τ - b)²`.
Hence `d(τ, γτ) ≥ 2 arsinh (√(tr² - 4)/2) = ln λ²`, with equality on the axis
`c|τ|² + (d - a) Re τ - b = 0`; no diagonalization is needed.  The trace, and with it the
translation length, is a conjugation invariant (`slTrace_conj`). -/
theorem translationLength_eq_inf_dist {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ) :
    translationLength γ = ⨅ τ : UpperHalfPlane, dist τ (γ • τ) ∧
      (∃ τ : UpperHalfPlane, dist τ (γ • τ) = translationLength γ) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, translationLength (A * γ * A⁻¹) = translationLength γ := by
  have ht4 : 0 < slTrace γ ^ 2 - 4 := by
    have h2 : 2 < |slTrace γ| := hγ
    nlinarith [abs_nonneg (slTrace γ), sq_abs (slTrace γ)]
  have hTL := translationLength_eq_arsinh ht4.le
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have htr : slTrace γ = γ 0 0 + γ 1 1 := rfl
  -- the lower bound
  have hlow : ∀ τ : UpperHalfPlane, translationLength γ ≤ dist τ (γ • τ) := by
    intro τ
    obtain ⟨hd, hn⟩ := dist_smul_eq_arsinh γ τ
    have hy : 0 < τ.im := τ.im_pos
    rw [hTL, hd]
    refine mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.2 ?_) (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hle : τ.im * √(slTrace γ ^ 2 - 4) ≤
        ‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - (γ 0 1 : ℂ)‖ := by
      refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
      rw [mul_pow, Real.sq_sqrt ht4.le, hn]
      nlinarith [sq_nonneg (γ 1 0 * (τ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ : ℂ).re - γ 0 1 +
        γ 1 0 * τ.im ^ 2)]
    nlinarith
  -- a point on the axis
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : UpperHalfPlane,
      γ 1 0 * (τ₀ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ₀ : ℂ).re - γ 0 1 + γ 1 0 * τ₀.im ^ 2 = 0 := by
    by_cases hc : γ 1 0 = 0
    · have hda : γ 1 1 - γ 0 0 ≠ 0 := by
        intro h0
        have hsq : slTrace γ ^ 2 - 4 = (γ 1 1 - γ 0 0) ^ 2 := by
          rw [htr]
          linear_combination (4 : ℝ) * hdet + (4 * γ 0 1) * hc
        rw [hsq, h0] at ht4
        norm_num at ht4
      obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) + I := ⟨_, rfl⟩
      have hwre : w.re = γ 0 1 / (γ 1 1 - γ 0 0) := by
        rw [hw]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      have hwim : w.im = 1 := by
        rw [hw]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
      refine ⟨⟨w, by rw [hwim]; norm_num⟩, ?_⟩
      show γ 1 0 * w.re ^ 2 + (γ 1 1 - γ 0 0) * w.re - γ 0 1 + γ 1 0 * w.im ^ 2 = 0
      rw [hwre, hc, mul_div_cancel₀ (γ 0 1) hda]
      ring
    · have hy0 : 0 < √(slTrace γ ^ 2 - 4) / (2 * |γ 1 0|) := by
        have h1 := abs_pos.2 hc
        have h2 := Real.sqrt_pos.2 ht4
        positivity
      obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (((γ 0 0 - γ 1 1) / (2 * γ 1 0) : ℝ) : ℂ) +
          ((√(slTrace γ ^ 2 - 4) / (2 * |γ 1 0|) : ℝ) : ℂ) * I := ⟨_, rfl⟩
      have hwre : w.re = (γ 0 0 - γ 1 1) / (2 * γ 1 0) := by
        rw [hw]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      have hwim : w.im = √(slTrace γ ^ 2 - 4) / (2 * |γ 1 0|) := by
        rw [hw]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
      have hy2 : w.im ^ 2 = ((γ 0 0 + γ 1 1) ^ 2 - 4) / (4 * γ 1 0 ^ 2) := by
        rw [hwim, div_pow, Real.sq_sqrt ht4.le, mul_pow, sq_abs, htr]
        ring
      have key : ∀ x y : ℝ, x = (γ 0 0 - γ 1 1) / (2 * γ 1 0) →
          y = ((γ 0 0 + γ 1 1) ^ 2 - 4) / (4 * γ 1 0 ^ 2) →
          γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 + γ 1 0 * y =
            (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 - 1) / γ 1 0 := by
        rintro x y rfl rfl
        field_simp
        ring
      refine ⟨⟨w, by rw [hwim]; exact hy0⟩, ?_⟩
      show γ 1 0 * w.re ^ 2 + (γ 1 1 - γ 0 0) * w.re - γ 0 1 + γ 1 0 * w.im ^ 2 = 0
      rw [key w.re (w.im ^ 2) hwre hy2, hdet, sub_self, zero_div]
  have heq : dist τ₀ (γ • τ₀) = translationLength γ := by
    obtain ⟨hd, hn⟩ := dist_smul_eq_arsinh γ τ₀
    have hy : 0 < τ₀.im := τ₀.im_pos
    rw [hτ₀] at hn
    have hQ : ‖(γ 1 0 : ℂ) * (τ₀ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ₀ - (γ 0 1 : ℂ)‖ =
        τ₀.im * √(slTrace γ ^ 2 - 4) := by
      refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [hn, mul_pow, Real.sq_sqrt ht4.le]
      ring
    rw [hd, hQ, hTL]
    congr 2
    field_simp
  refine ⟨le_antisymm (le_ciInf hlow) ((ciInf_le ⟨0, ?_⟩ τ₀).trans heq.le), ⟨τ₀, heq⟩,
    fun A => by rw [translationLength, translationLength, slTrace_conj]⟩
  rintro _ ⟨τ, rfl⟩
  exact dist_nonneg

theorem arsinh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arsinh x ≤ x :=
  Real.sinh_le_sinh.1 (by rw [Real.sinh_arsinh]; exact Real.self_le_sinh_iff.2 hx)

/-- A parabolic element of `SL(2, ℝ)` moves some point of `ℍ` by less than any `ε > 0`: with
`tr² = 4` the displacement formula gives `d(τ, γτ) ≤ |c(x² + y²) + (d - a)x - b| / y`, which is
`|b|/N` at `τ = iN` when `c = 0`, and `|c| y` on the vertical line through the fixed point
`(a - d)/(2c)` when `c ≠ 0`. -/
theorem exists_dist_smul_lt_of_isParabolic {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : IsParabolic γ) {ε : ℝ} (hε : 0 < ε) : ∃ τ : UpperHalfPlane, dist τ (γ • τ) < ε := by
  have ht : slTrace γ ^ 2 - 4 = 0 := by rw [← sq_abs, hγ.1]; norm_num
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have htr : slTrace γ = γ 0 0 + γ 1 1 := rfl
  obtain ⟨E, hE⟩ : ∃ E : UpperHalfPlane → ℝ, ∀ τ : UpperHalfPlane, E τ =
      γ 1 0 * (τ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ : ℂ).re - γ 0 1 + γ 1 0 * τ.im ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hbound : ∀ τ : UpperHalfPlane, dist τ (γ • τ) ≤ |E τ| / τ.im := by
    intro τ
    obtain ⟨hd, hn⟩ := dist_smul_eq_arsinh γ τ
    rw [ht, mul_zero, zero_add, ← hE τ] at hn
    have hy : 0 < τ.im := τ.im_pos
    have hQ : ‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - (γ 0 1 : ℂ)‖ = |E τ| := by
      rw [← Real.sqrt_sq (norm_nonneg _), hn, Real.sqrt_sq_eq_abs]
    rw [hd, hQ]
    have hnn : 0 ≤ |E τ| / (2 * τ.im) := by positivity
    calc 2 * Real.arsinh (|E τ| / (2 * τ.im)) ≤ 2 * (|E τ| / (2 * τ.im)) :=
          mul_le_mul_of_nonneg_left (arsinh_le_self_of_nonneg hnn) (by norm_num)
      _ = |E τ| / τ.im := by rw [mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]
  by_cases hc : γ 1 0 = 0
  · obtain ⟨N, hN⟩ : ∃ N : ℝ, N = |γ 0 1| / ε + 1 := ⟨_, rfl⟩
    have hN0 : 0 < N := by rw [hN]; positivity
    have hpos : 0 < ((N : ℂ) * I).im := by simpa using hN0
    refine ⟨⟨(N : ℂ) * I, hpos⟩, lt_of_le_of_lt (hbound _) ?_⟩
    rw [hE]
    show |γ 1 0 * ((N : ℂ) * I).re ^ 2 + (γ 1 1 - γ 0 0) * ((N : ℂ) * I).re - γ 0 1 +
      γ 1 0 * ((N : ℂ) * I).im ^ 2| / ((N : ℂ) * I).im < ε
    have hre : ((N : ℂ) * I).re = 0 := by simp
    have him : ((N : ℂ) * I).im = N := by simp
    rw [hre, him, hc]
    simp only [zero_mul, mul_zero, zero_sub, add_zero, abs_neg]
    rw [div_lt_iff₀ hN0, hN, mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
    linarith
  · have hc' : 0 < |γ 1 0| := abs_pos.2 hc
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ε / (2 * |γ 1 0|) := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (γ 0 0 - γ 1 1) / (2 * γ 1 0) := ⟨_, rfl⟩
    have hpos : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy0
    refine ⟨⟨(x : ℂ) + (y : ℂ) * I, hpos⟩, lt_of_le_of_lt (hbound _) ?_⟩
    rw [hE]
    show |γ 1 0 * ((x : ℂ) + (y : ℂ) * I).re ^ 2 + (γ 1 1 - γ 0 0) * ((x : ℂ) + (y : ℂ) * I).re -
      γ 0 1 + γ 1 0 * ((x : ℂ) + (y : ℂ) * I).im ^ 2| / ((x : ℂ) + (y : ℂ) * I).im < ε
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [hre, him]
    have hkey : γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 =
        -((slTrace γ ^ 2 - 4) - 4 * (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 - 1)) / (4 * γ 1 0) := by
      rw [hx, htr]
      field_simp
      ring
    rw [show γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 + γ 1 0 * y ^ 2 = γ 1 0 * y ^ 2 by
      rw [hkey, ht, hdet]; ring]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2), div_lt_iff₀ hy0]
    have hcy : |γ 1 0| * y = ε / 2 := by
      rw [hy]
      field_simp
    calc |γ 1 0| * y ^ 2 = (|γ 1 0| * y) * y := by ring
      _ = ε / 2 * y := by rw [hcy]
      _ < ε * y := by nlinarith

/-- The hyperbolic length of a Lipschitz curve in `ℍ` is its length for the Poincaré density of `ℍ` (S14). -/
theorem s30a_hypLength_eq (c : ℝ → ℂ) (hc : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1))
    (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) :
    hypLength c = (s30a_lr c hc).rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z)) := by
  unfold hypLength LRCurve.rhoLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hpos : 0 < (c t).im := him t (Ioo_subset_Icc_self ht)
  show ‖deriv c t‖ₑ / ENNReal.ofReal (c t).im =
    ENNReal.ofReal (poincareDensity upperHalf (c t)) * ‖deriv c t‖ₑ
  rw [poincareDensity_upperHalf hpos, one_div, ENNReal.ofReal_inv_of_pos hpos, div_eq_mul_inv, mul_comm]

/-- **Length ≥ distance** for a Lipschitz curve in `ℍ`. -/
theorem s30a_dist_le_hypLength (c : ℝ → ℂ) (hc : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1))
    (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) :
    ENNReal.ofReal (dist (UpperHalfPlane.mk (c 0) (him 0 ⟨le_rfl, zero_le_one⟩))
      (UpperHalfPlane.mk (c 1) (him 1 ⟨zero_le_one, le_rfl⟩))) ≤ hypLength c := by
  rw [← poincareDist_upperHalf, s30a_hypLength_eq c hc him]
  unfold poincareDist metricDist
  refine iInf₂_le (s30a_lr c hc) ⟨hc, rfl, rfl, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact him t ht

/-- **The geodesic segment** `τ₁ → τ₂`: a Lipschitz curve of hyperbolic length `d(τ₁, τ₂)`. -/
theorem s30a_geodesic (τ₁ τ₂ : UpperHalfPlane) :
    ∃ c : ℝ → ℂ, (∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1)) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) ∧
      c 0 = τ₁ ∧ c 1 = τ₂ ∧ hypLength c = ENNReal.ofReal (dist τ₁ τ₂) := by
  obtain ⟨γ, ⟨hK, h0, h1, htr⟩, hlen, -⟩ := upperHalf_geodesic τ₁.coe_im_pos τ₂.coe_im_pos
  have him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (γ.toFun t).im := fun t ht => htr ⟨t, ht, rfl⟩
  refine ⟨γ.toFun, hK, him, h0, h1, ?_⟩
  rw [s30a_hypLength_eq γ.toFun hK him, ← poincareDist_upperHalf]
  exact hlen

/-- A uniformization is invariant under its covering group: `p (γ x) = p x` for `γ ∈ Γ`. -/
theorem s30a_p_smul {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (x : UpperHalfPlane) : p (γ • x) = p x :=
  ((hp.2.2.2 x (γ • x)).2 ⟨γ, hγ, rfl⟩).symm

/-- **Free homotopy ⇒ conjugate covering element.**  If `γ` covers `α`, `α ≃ β` freely, and `d` lifts `β`,
then `d 1 = (δγδ⁻¹) d 0` for some `δ ∈ Γ`. -/
theorem s30a_fh_fwd {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {α β : Loop S} (hcov : Covers p γ α)
    (hαβ : FreelyHomotopic α β) (d : C(unitInterval, UpperHalfPlane)) (hd : ∀ t, p (d t) = β.2 t) :
    ∃ δ ∈ Γ, d 1 = (δ * γ * δ⁻¹) • d 0 := by
  obtain ⟨c, hcc, hcp, hc1⟩ := hcov
  obtain ⟨H, hH0, hH1, hHs⟩ := hαβ
  set f₀ : C(unitInterval, UpperHalfPlane) :=
    ⟨fun t => c t, hcc.comp_continuous continuous_subtype_val fun t => t.2⟩
  have hf₀ : ∀ t, H (0, t) = p (f₀ t) := fun t => by
    rw [hH0, ← Path.extend_extends' α.2 t]
    exact (hcp t t.2).symm
  set Ht := hp.1.liftHomotopy H f₀ hf₀
  have hlift : ∀ x, p (Ht x) = H x := fun x => congrFun (hp.1.liftHomotopy_lifts H f₀ hf₀) x
  have hzero : ∀ t, Ht (0, t) = f₀ t := hp.1.liftHomotopy_zero H f₀ hf₀
  -- the deck element along the lifted homotopy is `γ`
  have hA : (fun s => Ht (s, 1)) = (fun s => γ • Ht (s, 0)) := by
    refine hp.1.eq_of_comp_eq (Ht.continuous.comp (continuous_id.prodMk continuous_const))
      ((continuous_const_smul γ).comp (Ht.continuous.comp (continuous_id.prodMk continuous_const))) ?_ 0 ?_
    · funext s
      simp only [Function.comp_apply]
      rw [hlift, s30a_p_smul hp hγ, hlift, hHs]
    · show Ht (0, 1) = γ • Ht (0, 0)
      rw [hzero, hzero]
      exact hc1
  -- compare the end of the lifted homotopy with `d`
  obtain ⟨δ, hδ, hδe⟩ := (hp.2.2.2 (Ht (1, 0)) (d 0)).1 (by rw [hlift, hd, ← hH1])
  have hB : (fun t => δ • Ht (1, t)) = (fun t => d t) := by
    refine hp.1.eq_of_comp_eq ((continuous_const_smul δ).comp
      (Ht.continuous.comp (continuous_const.prodMk continuous_id))) d.continuous ?_ 0 hδe
    funext t
    simp only [Function.comp_apply]
    rw [s30a_p_smul hp hδ, hlift, hH1, hd]
  refine ⟨δ, hδ, ?_⟩
  have e1 := congrFun hB 1
  have e0 := congrFun hB 0
  have eA := congrFun hA 1
  rw [← e1, ← e0, eA, mul_smul, mul_smul, inv_smul_smul]

/-- **Same covering element ⇒ freely homotopic.**  If `γ` covers `α` and `e` is a path in `ℍ` with
`e 1 = γ e 0` projecting to `β`, then `α ≃ β` freely (the geodesic homotopy between the lifts is
`γ`-equivariant). -/
theorem s30a_fh_bwd {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α)
    (e : C(unitInterval, UpperHalfPlane)) (he : e 1 = γ • e 0) (β : Loop S) (hβ : ∀ t, β.2 t = p (e t)) :
    FreelyHomotopic α β := by
  obtain ⟨c, hcc, hcp, hc1⟩ := hcov
  have hcI : Continuous fun x : unitInterval × unitInterval => c (x.2 : ℝ) :=
    hcc.comp_continuous (continuous_subtype_val.comp continuous_snd) fun x => x.2.2
  refine ⟨⟨fun x => p (c36_d_geod (c x.2) (e x.2) x.1), ?_⟩, fun t => ?_, fun t => ?_, fun s => ?_⟩
  · exact hp.1.continuous.comp (c36_d_geod_continuous.comp
      (hcI.prodMk ((e.continuous.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))))
  · show p (c36_d_geod (c t) (e t) ((0 : unitInterval) : ℝ)) = α.2 t
    rw [Set.Icc.coe_zero, h36t_geod_zero, hcp t t.2, Path.extend_extends']
  · show p (c36_d_geod (c t) (e t) ((1 : unitInterval) : ℝ)) = β.2 t
    rw [Set.Icc.coe_one, h36t_geod_one, hβ]
  · show p (c36_d_geod (c ((0 : unitInterval) : ℝ)) (e 0) s) = p (c36_d_geod (c ((1 : unitInterval) : ℝ)) (e 1) s)
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, hc1, he, h36t_geod_smul, s30a_p_smul hp hγ]

/-- The projection of a path `e` in `ℍ` with `p (e 1) = p (e 0)`, as a loop. -/
def s30a_projLoop {S : Type u} [TopologicalSpace S] (p : UpperHalfPlane → S) (hpc : Continuous p)
    (e : C(unitInterval, UpperHalfPlane)) (he : p (e 1) = p (e 0)) : Loop S :=
  ⟨p (e 0), ⟨⟨fun t => p (e t), hpc.comp e.continuous⟩, rfl, he⟩⟩

/-- A Lipschitz curve in `ℍ` as a path of `ℍ`. -/
def s30a_pathOf (c : ℝ → ℂ) (hc : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1))
    (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) : C(unitInterval, UpperHalfPlane) :=
  ⟨fun t => UpperHalfPlane.mk (c t) (him t t.2),
    Continuous.upperHalfPlaneMk (hc.choose_spec.continuousOn.comp_continuous continuous_subtype_val
      fun t => t.2) _⟩

/-- **Upper bound**: `l[α] ≤ d(τ, γτ)` for every `τ` (project the geodesic segment from `τ` to `γτ`). -/
theorem s30a_ub {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α)
    (τ : UpperHalfPlane) : freeHomotopyLength p α ≤ ENNReal.ofReal (dist τ (γ • τ)) := by
  obtain ⟨c, hK, him, hc0, hc1, hlen⟩ := s30a_geodesic τ (γ • τ)
  set e := s30a_pathOf c hK him
  have he0 : e 0 = τ := UpperHalfPlane.ext hc0
  have he1 : e 1 = γ • τ := UpperHalfPlane.ext hc1
  have he : e 1 = γ • e 0 := by rw [he0, he1]
  have hpe : p (e 1) = p (e 0) := by rw [he, s30a_p_smul hp hγ]
  refine (iInf₂_le (s30a_projLoop p hp.1.continuous e hpe)
    (s30a_fh_bwd hp hγ hcov e he _ fun t => rfl)).trans ?_
  refine (iInf₂_le c ⟨hK, him, fun t ht h => ?_⟩).trans hlen.le
  rw [Path.extend_apply _ ht]
  rfl

/-- **Lower bound**: `l[α] ≥ ℓ(γ)` for hyperbolic `γ` (a lift of a curve freely homotopic to `α` joins some `τ` to
a conjugate `δγδ⁻¹ τ`, and `ℓ(γ) = ℓ(δγδ⁻¹)` is the minimal displacement). -/
theorem s30a_lb {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hh : IsHyperbolic γ) {α : Loop S}
    (hcov : Covers p γ α) : ENNReal.ofReal (translationLength γ) ≤ freeHomotopyLength p α := by
  refine le_iInf₂ fun β hαβ => le_iInf₂ fun c hc => ?_
  obtain ⟨hK, him, hlift⟩ := hc
  set d := s30a_pathOf c hK him
  have hd : ∀ t, p (d t) = β.2 t := fun t => by
    rw [← Path.extend_extends' β.2 t]
    exact hlift t t.2 (him t t.2)
  obtain ⟨δ, -, hd1⟩ := s30a_fh_fwd hp hγ hcov hαβ d hd
  have hhyp' : IsHyperbolic (δ * γ * δ⁻¹) := by
    unfold IsHyperbolic
    rw [slTrace_conj]
    exact hh
  have htl : translationLength γ ≤ dist (d 0) (d 1) := by
    rw [hd1, ← (translationLength_eq_inf_dist hh).2.2 δ, (translationLength_eq_inf_dist hhyp').1]
    exact ciInf_le ⟨0, by rintro _ ⟨τ, rfl⟩; exact dist_nonneg⟩ (d 0)
  exact (ENNReal.ofReal_le_ofReal htl).trans (s30a_dist_le_hypLength c hK him)

/-- The length of a loop covered by a hyperbolic element is its translation length (the first half of Lemma 30.2,
without the unused hypotheses). -/
theorem s30a_len_hyp {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hh : IsHyperbolic γ) {α : Loop S}
    (hcov : Covers p γ α) : freeHomotopyLength p α = ENNReal.ofReal (translationLength γ) := by
  obtain ⟨τ₀, hτ₀⟩ := (translationLength_eq_inf_dist hh).2.1
  refine le_antisymm ?_ (s30a_lb hp hγ hh hcov)
  rw [← hτ₀]
  exact s30a_ub hp hγ hcov τ₀

/-- The length of a loop covered by a parabolic element or by `±1` is `0` (the second half of Lemma 30.2, without
the unused hypotheses). -/
theorem s30a_len_zero {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hz : γ = 1 ∨ γ = -1 ∨ IsParabolic γ) {α : Loop S}
    (hcov : Covers p γ α) : freeHomotopyLength p α = 0 := by
  rcases hz with rfl | rfl | hpar
  · refine le_antisymm ((s30a_ub hp hγ hcov UpperHalfPlane.I).trans ?_) bot_le
    rw [one_smul, dist_self, ENNReal.ofReal_zero]
  · refine le_antisymm ((s30a_ub hp hγ hcov UpperHalfPlane.I).trans ?_) bot_le
    rw [s27g_neg_one_smul, dist_self, ENNReal.ofReal_zero]
  · refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    obtain ⟨τ, hτ⟩ := exists_dist_smul_lt_of_isParabolic hpar (show (0 : ℝ) < ε from hε)
    rw [zero_add]
    exact (s30a_ub hp hγ hcov τ).trans
      (le_of_le_of_eq (ENNReal.ofReal_le_ofReal hτ.le) ENNReal.ofReal_coe_nnreal)

/-- **Lemma 30.2**: let `S = ℍ/G`, `G` a torsion free Fuchsian group, and let `γ ∈ G` cover the
closed curve `α ⊆ S`.  Then `l[α] = ln λ²`, `λ` the larger eigenvalue of the matrix of `γ`
(`l[α] = 0` when `γ` is parabolic). -/
theorem lemma30_2 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α) :
    (IsHyperbolic γ → freeHomotopyLength p α = ENNReal.ofReal (translationLength γ)) ∧
      (IsParabolic γ → freeHomotopyLength p α = 0) := by
  have _ := hΓ
  have _ := hfree
  exact ⟨fun hh => s30a_len_hyp hp hγ hh hcov, fun hpar => s30a_len_zero hp hγ (Or.inr (Or.inr hpar)) hcov⟩

/-- An element of `SL(2, ℝ)` with `|tr| < 2` is elliptic in Mathlib's sense (`discr < 0`): the
discriminant of a `2 × 2` matrix is `tr² - 4 det`, and `det = 1` here. -/
theorem isElliptic_mapGL_of_abs_slTrace_lt_two {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : |slTrace γ| < 2) : (Matrix.SpecialLinearGroup.mapGL ℝ γ).IsElliptic := by
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.det = 1 := by simp
  have htr : (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.trace = slTrace γ := by
    simp [slTrace, Matrix.trace_fin_two]
  have habs := abs_lt.1 h
  show (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.discr < 0
  rw [Matrix.discr_fin_two, hdet, htr]
  nlinarith [habs.1, habs.2]

/-- **§30.2 (the elliptic half).**  An element of `SL(2, ℝ)` with `|tr| < 2` has a fixed point in
`ℍ`: the fixed-point equation `c z² + (d - a) z - b = 0` has discriminant `tr² - 4 < 0`, so its two
roots are non-real conjugates and one of them lies in `ℍ`.  Mathlib supplies that root as
`UpperHalfPlane.fixedPt`. -/
theorem exists_smul_eq_self_of_abs_slTrace_lt_two {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : |slTrace γ| < 2) : ∃ τ : UpperHalfPlane, γ • τ = τ := by
  have hell := isElliptic_mapGL_of_abs_slTrace_lt_two h
  refine ⟨UpperHalfPlane.fixedPt _ hell, ?_⟩
  rw [MulAction.compHom_smul_def]
  exact (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp) hell).2 rfl

/-- **§30.2 (the elliptic half, as used for the covering group).**  A group acting freely on `ℍ`
has no elliptic elements besides `±I`: `|tr γ| ≥ 2` for every `γ ∈ Γ` with `γ ≠ ±1`.

This is the half of `cocompact_elements_hyperbolic` that needs no cocompactness — free action alone
rules out `|tr| < 2`. -/
theorem two_le_abs_slTrace_of_actsFreely {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hfree : ActsFreely Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (h1 : γ ≠ 1) (h2 : γ ≠ -1) : 2 ≤ |slTrace γ| := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨τ, hτ⟩ := exists_smul_eq_self_of_abs_slTrace_lt_two hlt
  rcases hfree γ hγ τ hτ with h | h
  · exact h1 h
  · exact h2 h

/-- **§30.2 (the elliptic half, restated as the parabolic dichotomy).**  For `Γ` acting freely,
every `γ ∈ Γ` other than `±I` is either parabolic or hyperbolic.  `cocompact_elements_hyperbolic`
is then exactly the statement that cocompactness rules out the parabolic case. -/
theorem isParabolic_or_isHyperbolic_of_actsFreely
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfree : ActsFreely Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    IsParabolic γ ∨ IsHyperbolic γ := by
  have h := two_le_abs_slTrace_of_actsFreely hfree hγ h1 h2
  rcases eq_or_lt_of_le h with heq | hlt
  · exact Or.inl ⟨heq.symm, h1, h2⟩
  · exact Or.inr hlt

/-- A uniform positive bound over a finite set, for a property that is monotone in the bound. -/
theorem exists_pos_forall_of_finite {α : Type*} {S : Set α} (hS : S.Finite) {P : α → ℝ → Prop}
    (hmono : ∀ a δ δ', δ' ≤ δ → P a δ → P a δ') (h : ∀ a ∈ S, ∃ δ > 0, P a δ) :
    ∃ δ > 0, ∀ a ∈ S, P a δ := by
  classical
  choose! d hd hPd using h
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image S d hS hne
    exact ⟨d a₀, hd a₀ ha₀, fun a ha => hmono a (d a) (d a₀) (hmin a ha) (hPd a ha)⟩

/-- §30.2: the covering group of a compact Riemann surface consists of hyperbolic elements
(besides `±I`).

The parabolic case is all that remains after `isParabolic_or_isHyperbolic_of_actsFreely`.  It needs
no parabolic normal form:
* **Small displacement.**  For `γ = (a b; c d)` with `tr² = 4`, the displacement formula
  `dist_smul_eq_arsinh` gives `d(τ, γτ) ≤ |c(x² + y²) + (d - a)x - b| / y`.  This is small at
  `τ = iN` when `c = 0`, and near the real axis on the vertical line through the fixed point
  `(a - d)/(2c)` when `c ≠ 0` (`exists_dist_smul_lt_of_isParabolic`).
* **Uniform lower bound.**  Let `C` be the compact set from cocompactness and `C'` its closed
  `1`-thickening.  By `IsFuchsian`, only finitely many `g ∈ Γ` with `g ≠ ±1` satisfy
  `g C' ∩ C' ≠ ∅`.  Each of them moves every point of `C` by at least some `δ_g > 0`: a minimum
  `0` over the compact `C` would be a fixed point, which `ActsFreely` excludes.
* **Contradiction.**  Choose `τ` moved by less than `min (min_g δ_g) 1`, and `σ ∈ Γ` with
  `στ ∈ C`.  Then `σγσ⁻¹ ≠ ±1` lies in that finite set, but it moves `στ ∈ C` by the same small
  amount, because `SL(2, ℝ)` acts by isometries. -/
theorem cocompact_elements_hyperbolic {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hc : IsCocompact Γ) : ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → IsHyperbolic γ := by
  intro γ hγ h1 h2
  rcases isParabolic_or_isHyperbolic_of_actsFreely hfree hγ h1 h2 with hpar | hhyp
  · exfalso
    obtain ⟨C, hC, hcov⟩ := hc
    have hC' : IsCompact (cthickening 1 C) := hC.cthickening
    have hCne : C.Nonempty := by
      obtain ⟨σ, -, hσ⟩ := hcov UpperHalfPlane.I
      exact ⟨_, hσ⟩
    obtain ⟨S, hSdef⟩ : ∃ S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ),
        S = {g ∈ Γ | ((g • ·) '' cthickening 1 C ∩ cthickening 1 C).Nonempty} ∩
          {g | g ≠ 1 ∧ g ≠ -1} := ⟨_, rfl⟩
    have hS : S.Finite := by
      rw [hSdef]
      exact (hΓ _ hC').subset inter_subset_left
    have hpos : ∀ g ∈ S, ∃ δ > 0, ∀ ρ ∈ C, δ ≤ dist ρ (g • ρ) := by
      intro g hg
      rw [hSdef] at hg
      have hcont : Continuous fun ρ : UpperHalfPlane => dist ρ (g • ρ) :=
        continuous_id.dist (continuous_const_smul g)
      obtain ⟨ρ₀, hρ₀, hmin⟩ := hC.exists_isMinOn hCne hcont.continuousOn
      refine ⟨dist ρ₀ (g • ρ₀), dist_pos.2 fun h => ?_, fun ρ hρ => isMinOn_iff.1 hmin ρ hρ⟩
      rcases hfree g hg.1.1 ρ₀ h.symm with h' | h'
      · exact hg.2.1 h'
      · exact hg.2.2 h'
    obtain ⟨δ, hδ, hδS⟩ := exists_pos_forall_of_finite hS
      (fun g δ δ' hle h ρ hρ => hle.trans (h ρ hρ)) hpos
    obtain ⟨τ, hτ⟩ := exists_dist_smul_lt_of_isParabolic hpar (lt_min hδ one_pos)
    obtain ⟨σ, hσ, hστ⟩ := hcov τ
    have hgρ : (σ * γ * σ⁻¹) • (σ • τ) = σ • (γ • τ) := by
      rw [mul_smul, mul_smul, inv_smul_smul]
    have hdist : dist (σ • τ) ((σ * γ * σ⁻¹) • (σ • τ)) = dist τ (γ • τ) := by
      rw [hgρ, dist_smul]
    have hγeq : γ = σ⁻¹ * (σ * γ * σ⁻¹) * σ := by group
    have hgS : σ * γ * σ⁻¹ ∈ S := by
      rw [hSdef]
      refine ⟨⟨Γ.mul_mem (Γ.mul_mem hσ hγ) (Γ.inv_mem hσ), (σ * γ * σ⁻¹) • (σ • τ),
        ⟨σ • τ, self_subset_cthickening C hστ, rfl⟩, ?_⟩, fun h => h1 ?_, fun h => h2 ?_⟩
      · refine mem_cthickening_of_dist_le _ (σ • τ) 1 C hστ ?_
        rw [dist_comm, hdist]
        exact (hτ.trans_le (min_le_right _ _)).le
      · rw [hγeq, h, mul_one, inv_mul_cancel]
      · rw [hγeq, h]
        simp
    have hle := hδS _ hgS (σ • τ) hστ
    rw [hdist] at hle
    exact absurd (hτ.trans_le (min_le_left _ _)) (not_lt.2 hle)
  · exact hhyp

/-! ## §30.3 Discreteness of the length spectrum -/

/-- §30.3 (the same in terms of the group): only finitely many conjugacy classes of `Γ` have
translation length `≤ L`; the length spectrum has no accumulation point.

Proof: for hyperbolic `γ` with `ℓ(γ) ≤ L`, `translationLength_eq_inf_dist` gives `τ` with
`d(τ, γτ) = ℓ(γ)`.  Move `τ` into the compact set `C` of cocompactness by some `σ ∈ Γ`.  Then
the conjugate `σγσ⁻¹` maps the point `στ ∈ C` into the closed `L`-thickening of `C`, so it lies
in the finite set that `IsFuchsian` gives for this compact set.  The finiteness of the lengths
follows because translation lengths are conjugation invariants (`slTrace_conj`). -/
theorem lengthSpectrum_discrete {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hc : IsCocompact Γ) (L : ℝ) :
    {ℓ ∈ lengthSpectrum Γ | ℓ ≤ L}.Finite ∧
      ∃ F : Finset (Matrix.SpecialLinearGroup (Fin 2) ℝ), ∀ γ ∈ Γ, IsHyperbolic γ →
        translationLength γ ≤ L → ∃ δ ∈ Γ, ∃ γ' ∈ F, γ = δ * γ' * δ⁻¹ := by
  have _ := hfree
  obtain ⟨C, hC, hcov⟩ := hc
  have hCL : IsCompact (cthickening L C) := hC.cthickening
  have hfin := hΓ _ hCL
  have hb : ∀ γ ∈ Γ, IsHyperbolic γ → translationLength γ ≤ L →
      ∃ δ ∈ Γ, ∃ γ' ∈ hfin.toFinset, γ = δ * γ' * δ⁻¹ := by
    intro γ hγ hhyp hL
    obtain ⟨τ, hτ⟩ := (translationLength_eq_inf_dist hhyp).2.1
    obtain ⟨σ, hσ, hστ⟩ := hcov τ
    refine ⟨σ⁻¹, Γ.inv_mem hσ, σ * γ * σ⁻¹, ?_, by group⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨Γ.mul_mem (Γ.mul_mem hσ hγ) (Γ.inv_mem hσ), (σ * γ * σ⁻¹) • (σ • τ),
      ⟨σ • τ, self_subset_cthickening C hστ, rfl⟩, ?_⟩
    refine mem_cthickening_of_dist_le _ (σ • τ) L C hστ ?_
    rw [show (σ * γ * σ⁻¹) • (σ • τ) = σ • (γ • τ) by rw [mul_smul, mul_smul, inv_smul_smul],
      dist_comm, dist_smul, hτ]
    exact hL
  refine ⟨?_, hfin.toFinset, hb⟩
  refine (hfin.toFinset.finite_toSet.image translationLength).subset ?_
  rintro ℓ ⟨⟨γ, hγ, htr, rfl⟩, hL⟩
  obtain ⟨δ, -, γ', hγ', rfl⟩ := hb γ hγ htr hL
  exact ⟨γ', hγ', by rw [translationLength, translationLength, slTrace_conj]⟩

/-- The translation length of a hyperbolic element is positive. -/
theorem s30a_tl_pos {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hh : IsHyperbolic γ) :
    0 < translationLength γ := by
  have h2 : 2 < |slTrace γ| := hh
  have ht4 : 0 < slTrace γ ^ 2 - 4 := by nlinarith [abs_nonneg (slTrace γ), sq_abs (slTrace γ)]
  rw [translationLength_eq_arsinh ht4.le]
  have h1 : 0 < √(slTrace γ ^ 2 - 4) / 2 := by positivity
  have := Real.arsinh_pos_iff.2 h1
  linarith

/-- Helper for `s30l_normalize`: the entries of the inverse in `SL(2, ℝ)`. -/
theorem s30l_inv_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    g⁻¹ 0 0 = g 1 1 ∧ g⁻¹ 0 1 = -g 0 1 ∧ g⁻¹ 1 0 = -g 1 0 ∧ g⁻¹ 1 1 = g 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Helper for `s30l_normalize`: the conjugate of `A Γ A⁻¹`'s membership in terms of `Γ`. -/
theorem s30l_mem_conjGroup {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {A g : Matrix.SpecialLinearGroup (Fin 2) ℝ} :
    g ∈ conjGroup Γ A ↔ ∃ h ∈ Γ, g = A * h * A⁻¹ := by
  unfold conjGroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp [MulAut.conj_apply]⟩

/-- Helper for `s30l_normalize`: a conjugate `A Γ A⁻¹` of a Fuchsian group is Fuchsian. -/
theorem s30l_isFuchsian_conj {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : IsFuchsian (conjGroup Γ A) := by
  intro C hC
  have hC' : IsCompact ((fun x : UpperHalfPlane => A⁻¹ • x) '' C) := hC.image (continuous_const_smul A⁻¹)
  refine ((hΓ _ hC').image (fun h => A * h * A⁻¹)).subset ?_
  rintro g ⟨hg, y, ⟨x, hxC, rfl⟩, hyC⟩
  obtain ⟨h, hh, rfl⟩ := s30l_mem_conjGroup.1 hg
  refine ⟨h, ⟨hh, A⁻¹ • (A * h * A⁻¹) • x, ⟨A⁻¹ • x, ⟨x, hxC, rfl⟩, ?_⟩, ⟨(A * h * A⁻¹) • x, hyC, rfl⟩⟩, rfl⟩
  show h • A⁻¹ • x = A⁻¹ • (A * h * A⁻¹) • x
  rw [mul_smul, mul_smul, inv_smul_smul]

/-- Helper for `s30l_normalize`: a parabolic (or any non-elliptic) element is conjugate to one fixing `∞`. -/
theorem s30l_exists_fix_infty {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 ≤ |γ 0 0 + γ 1 1|) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, (A * γ * A⁻¹) 1 0 = 0 := by
  obtain ⟨p, q, hpq, hQ⟩ := s27g_fixed_vec hγ
  have hn : 0 < p ^ 2 + q ^ 2 := by
    rcases hpq with h | h
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.2 h) 2
      rw [sq_abs] at this
      positivity
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![p / (p ^ 2 + q ^ 2), q / (p ^ 2 + q ^ 2); -q, p], by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring⟩
  have hA1 : A 0 0 * p + A 0 1 * q = 1 := by
    show p / (p ^ 2 + q ^ 2) * p + q / (p ^ 2 + q ^ 2) * q = 1
    field_simp
  have hA2 : A 1 0 * p + A 1 1 * q = 0 := by
    show -q * p + p * q = 0
    ring
  refine ⟨A, ?_⟩
  have hcov := s27g_fix_conj A γ p q
  rw [hA1, hA2, hQ] at hcov
  linear_combination hcov
/-- Helper for `s30l_normalize`: a dilation `g` (`c = 0`, `a² ≠ 1`) in a Fuchsian group `Γ'` that also contains a nontrivial
translation `τ₀` (`c = 0`, `a² = 1`, `b ≠ 0`) is impossible: the conjugates `gⁿ τ₀ g⁻ⁿ` (or with `g⁻¹`) are translations by
`(a²)ⁿ b → 0`, pairwise distinct elements moving `i` by less than `1`, contradicting discreteness. -/
theorem s30l_stab_sq_one {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : IsFuchsian Γ')
    {τ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hτ₀ : τ₀ ∈ Γ') (h10 : τ₀ 1 0 = 0) (hsq : τ₀ 0 0 ^ 2 = 1)
    (hb : τ₀ 0 1 ≠ 0) : ∀ g ∈ Γ', g 1 0 = 0 → g 0 0 ^ 2 = 1 := by
  intro g hg hg10
  by_contra hne
  have hdetg := hnf_sl2_det g
  rw [hg10, mul_zero, sub_zero] at hdetg
  have ha0 : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetg
  have hd0 : g 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdetg
  have hdsq : g 1 1 ^ 2 * g 0 0 ^ 2 = 1 := by
    have := congrArg (fun x => x ^ 2) hdetg
    simp only [one_pow] at this
    linear_combination this
  -- an element with `0 < a² < 1`
  obtain ⟨g', hg', hg'10, hk0, hk1, hdet'⟩ : ∃ g' ∈ Γ', g' 1 0 = 0 ∧ 0 < g' 0 0 ^ 2 ∧ g' 0 0 ^ 2 < 1 ∧
      g' 0 0 * g' 1 1 = 1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨g, hg, hg10, by positivity, h, hdetg⟩
    · refine ⟨g⁻¹, Γ'.inv_mem hg, ?_, ?_, ?_, ?_⟩
      · rw [(s30l_inv_apply g).2.2.1, hg10, neg_zero]
      · rw [(s30l_inv_apply g).1]
        positivity
      · rw [(s30l_inv_apply g).1]
        nlinarith [sq_nonneg (g 1 1), sq_nonneg (g 0 0)]
      · rw [(s30l_inv_apply g).1, (s30l_inv_apply g).2.2.2, mul_comm]
        exact hdetg
  set k : ℝ := g' 0 0 ^ 2 with hk
  have hde : τ₀ 1 1 = τ₀ 0 0 := by
    have hd := hnf_sl2_det τ₀
    rw [h10, mul_zero, sub_zero] at hd
    calc τ₀ 1 1 = τ₀ 0 0 ^ 2 * τ₀ 1 1 := by rw [hsq, one_mul]
      _ = τ₀ 0 0 * (τ₀ 0 0 * τ₀ 1 1) := by ring
      _ = τ₀ 0 0 := by rw [hd, mul_one]
  -- the conjugates
  have hseq : ∀ n : ℕ, ∃ τ ∈ Γ', τ 1 0 = 0 ∧ τ 0 0 = τ₀ 0 0 ∧ τ 1 1 = τ₀ 0 0 ∧ τ 0 1 = k ^ n * τ₀ 0 1 := by
    intro n
    induction n with
    | zero => exact ⟨τ₀, hτ₀, h10, rfl, hde, by simp⟩
    | succ n ih =>
      obtain ⟨τ, hτ, h1, h2, h3, h4⟩ := ih
      refine ⟨g' * τ * g'⁻¹, Γ'.mul_mem (Γ'.mul_mem hg' hτ) (Γ'.inv_mem hg'), ?_⟩
      obtain ⟨c00, c01, c10, c11⟩ := s27g_conj_apply g' τ
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [c10, hg'10, h1]
        ring
      · rw [c00, hg'10, h1, h2]
        linear_combination (τ₀ 0 0) * hdet'
      · rw [c11, hg'10, h1, h3]
        linear_combination (τ₀ 0 0) * hdet'
      · rw [c01, h1, h2, h3, h4]
        linear_combination (-(k ^ n * τ₀ 0 1)) * hk
  choose τ hτ using hseq
  set C : Set UpperHalfPlane := Metric.closedBall UpperHalfPlane.I 1 with hC
  have hCc : IsCompact C := isCompact_closedBall _ _
  have hSfin := hΓ' C hCc
  have hf0 : 0 < |τ₀ 0 1| := abs_pos.2 hb
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / |τ₀ 0 1| by positivity) hk1
  have hmem : ∀ m : ℕ, τ (N + m) ∈ {γ ∈ Γ' | ((γ • ·) '' C ∩ C).Nonempty} := by
    intro m
    obtain ⟨hm, h1, h2, h3, h4⟩ := hτ (N + m)
    have hb' : |τ (N + m) 0 1| < 1 := by
      rw [h4, abs_mul, abs_of_pos (pow_pos hk0 _)]
      calc k ^ (N + m) * |τ₀ 0 1| ≤ k ^ N * |τ₀ 0 1| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hk0.le hk1.le (Nat.le_add_right N m)) (abs_nonneg _)
        _ < 1 := by rwa [lt_div_iff₀ hf0] at hN
    have hnorm : ‖((τ (N + m) 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℂ) ^ 2 +
        (((τ (N + m) 1 1 : ℝ) : ℂ) - τ (N + m) 0 0) * (UpperHalfPlane.I : ℂ) - ((τ (N + m) 0 1 : ℝ) : ℂ)‖ =
        |τ (N + m) 0 1| := by
      rw [h1, h3, h2]
      simp
    have hd := (dist_smul_eq_arsinh (τ (N + m)) UpperHalfPlane.I).1
    rw [hnorm, UpperHalfPlane.I_im] at hd
    have hdle : dist UpperHalfPlane.I (τ (N + m) • UpperHalfPlane.I) ≤ |τ (N + m) 0 1| := by
      rw [hd]
      have := arsinh_le_self_of_nonneg (x := |τ (N + m) 0 1| / (2 * 1)) (by positivity)
      linarith
    refine ⟨hm, τ (N + m) • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self zero_le_one, rfl⟩, ?_⟩
    rw [hC, mem_closedBall, dist_comm]
    exact hdle.trans hb'.le
  have hinj : Function.Injective (fun m : ℕ => τ (N + m)) := by
    intro m m' h
    have h4 := (hτ (N + m)).2.2.2.2
    have h4' := (hτ (N + m')).2.2.2.2
    have h01 : τ (N + m) 0 1 = τ (N + m') 0 1 := by
      have := congrArg (fun x => x 0 1) h
      exact this
    rw [h4, h4'] at h01
    have h5 := mul_right_cancel₀ hb h01
    have h6 := pow_right_injective₀ hk0 hk1.ne h5
    omega
  exact (Set.infinite_of_injective_forall_mem hinj hmem) hSfin

/-- Helper for `s30l_normalize`: two elements of `SL(2, ℝ)` with equal entries are equal. -/
theorem s30l_eq_of_entries {β δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h00 : β 0 0 = δ 0 0) (h01 : β 0 1 = δ 0 1)
    (h10 : β 1 0 = δ 1 0) (h11 : β 1 1 = δ 1 1) : β = δ := by
  refine Matrix.SpecialLinearGroup.ext β δ fun i j => ?_
  fin_cases i <;> fin_cases j <;> assumption

/-- Helper for `s30l_normalize`: the integer powers of the translation `γ₁ : z ↦ z + 1`. -/
theorem s30l_zpow_entries {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1) (n : ℤ) :
    (γ₁ ^ n) 0 0 = 1 ∧ (γ₁ ^ n) 0 1 = n ∧ (γ₁ ^ n) 1 0 = 0 ∧ (γ₁ ^ n) 1 1 = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := h₁
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    obtain ⟨a, b, c, d⟩ := ih
    rw [zpow_add_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d, e00, e01, e10,
      e11]
    refine ⟨by ring, by push_cast; ring, by ring, by ring⟩
  | pred i ih =>
    obtain ⟨a, b, c, d⟩ := ih
    obtain ⟨i00, i01, i10, i11⟩ := s30l_inv_apply γ₁
    rw [zpow_sub_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d, i00, i01, i10, i11,
      e00, e01, e10, e11]
    refine ⟨by ring, by push_cast; ring, by ring, by ring⟩

/-- Helper for `s30l_normalize`: the entries of a product in `SL(2, ℝ)`. -/
theorem s30l_mul_entries (g h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 ∧ (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 ∧
      (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 ∧ (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for `s30l_normalize`: conjugating by a diagonal matrix `diag(s, 1/s)` scales the upper right entry by `s²`. -/
theorem s30l_conj_diag {D g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {s : ℝ} (hs : s ≠ 0) (d00 : D 0 0 = s)
    (d01 : D 0 1 = 0) (d10 : D 1 0 = 0) (d11 : D 1 1 = s⁻¹) :
    (D * g * D⁻¹) 0 0 = g 0 0 ∧ (D * g * D⁻¹) 0 1 = s ^ 2 * g 0 1 ∧ (D * g * D⁻¹) 1 0 = s⁻¹ ^ 2 * g 1 0 ∧
      (D * g * D⁻¹) 1 1 = g 1 1 := by
  obtain ⟨c00, c01, c10, c11⟩ := s27g_conj_apply D g
  rw [c00, c01, c10, c11, d00, d01, d10, d11]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Helper for `s30l_normalize`: an element `g` with `c = 0`, `a² = 1` moves `i` by at most `|b|` (it is the translation
`z ↦ z + a b`, `dist (i, i + t) = 2 arsinh(|t|/2) ≤ |t|`). -/
theorem s30l_dist_transl {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h10 : g 1 0 = 0) (hsq : g 0 0 ^ 2 = 1) :
    dist UpperHalfPlane.I (g • UpperHalfPlane.I) ≤ |g 0 1| := by
  have hd := hnf_sl2_det g
  rw [h10, mul_zero, sub_zero] at hd
  have hde : g 1 1 = g 0 0 := by
    calc g 1 1 = g 0 0 ^ 2 * g 1 1 := by rw [hsq, one_mul]
      _ = g 0 0 * (g 0 0 * g 1 1) := by ring
      _ = g 0 0 := by rw [hd, mul_one]
  have hnorm : ‖((g 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℂ) ^ 2 +
      (((g 1 1 : ℝ) : ℂ) - g 0 0) * (UpperHalfPlane.I : ℂ) - ((g 0 1 : ℝ) : ℂ)‖ = |g 0 1| := by
    rw [h10, hde]
    simp
  have hd2 := (dist_smul_eq_arsinh g UpperHalfPlane.I).1
  rw [hnorm, UpperHalfPlane.I_im] at hd2
  rw [hd2]
  have := arsinh_le_self_of_nonneg (x := |g 0 1| / (2 * 1)) (by positivity)
  linarith

/-- Helper for **Lemma 30.1** (§30.2), the book's normalization: for a parabolic `γ ∈ Γ` there is a conjugation `A` of
`ℍ` under which the covering group `AΓA⁻¹` contains `γ₁ : z ↦ z + 1`, generates the stabilizer of `∞` up to `±`
(`hstab`, the hypothesis of `parabolic_horoball_disjoint`; `γ₁` itself lies in the group only up to `±`, since
`Γ = ⟨-T⟩ ⊆ SL(2, ℝ)` is Fuchsian and contains `-T` but not `T`), and `A γ A⁻¹ = ±γ₁^m`, `m ≠ 0` (the book's "`γ = γ₁^m`, `m`
the highest power"). Proof: conjugate the fixed point of `γ` to `∞`; an element of `Γ` fixing `∞` is `z ↦ a²z + ab`, and a
dilation `a² ≠ 1` next to a translation contradicts discreteness (`IsFuchsian`, the conjugates `β⁻ⁿ γ βⁿ → 1`), so the
stabilizer is a discrete group of translations (up to `±`), which is cyclic (`AddSubgroup.dense_or_cyclic`); rescale its
generator to `z ↦ z + 1`. -/
theorem s30l_normalize {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hpar : IsParabolic γ) :
    ∃ (A γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (m : ℤ), (γ₁ ∈ conjGroup Γ A ∨ -γ₁ ∈ conjGroup Γ A) ∧
      (γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1) ∧
      (∀ β ∈ conjGroup Γ A, β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n) ∧ m ≠ 0 ∧
      (A * γ * A⁻¹ = γ₁ ^ m ∨ A * γ * A⁻¹ = -γ₁ ^ m) := by
  classical
  obtain ⟨htr, h1, h2⟩ := hpar
  have htrabs : |γ 0 0 + γ 1 1| = 2 := htr
  obtain ⟨A₀, hA₀⟩ := s30l_exists_fix_infty (le_of_eq htrabs.symm)
  have hΓ' : IsFuchsian (conjGroup Γ A₀) := s30l_isFuchsian_conj hΓ A₀
  have hγ'mem : A₀ * γ * A₀⁻¹ ∈ conjGroup Γ A₀ := s30l_mem_conjGroup.2 ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ' = A₀ * γ * A₀⁻¹ := ⟨_, rfl⟩
  rw [← hγ'def] at hA₀ hγ'mem
  have hdet' := hnf_sl2_det γ'
  rw [hA₀, mul_zero, sub_zero] at hdet'
  have htr' : |γ' 0 0 + γ' 1 1| = 2 := by rw [hγ'def, s27g_trace_conj]; exact htrabs
  have hsq' : γ' 0 0 ^ 2 = 1 := by
    have h4 : (γ' 0 0 + γ' 1 1) ^ 2 = 4 := by
      have := sq_abs (γ' 0 0 + γ' 1 1)
      rw [htr'] at this
      linarith
    have h5 : (γ' 0 0 - γ' 1 1) ^ 2 = 0 := by nlinarith
    have h6 : γ' 0 0 = γ' 1 1 := by
      have := (pow_eq_zero_iff two_ne_zero).1 h5
      linarith
    rw [← h6] at hdet'
    nlinarith
  have hda : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, g 1 0 = 0 → g 0 0 ^ 2 = 1 → g 1 1 = g 0 0 := by
    intro g hg10 hgsq
    have hd := hnf_sl2_det g
    rw [hg10, mul_zero, sub_zero] at hd
    calc g 1 1 = g 0 0 ^ 2 * g 1 1 := by rw [hgsq, one_mul]
      _ = g 0 0 * (g 0 0 * g 1 1) := by ring
      _ = g 0 0 := by rw [hd, mul_one]
  have hpm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, g 0 0 ^ 2 = 1 → g 0 0 = 1 ∨ g 0 0 = -1 := by
    intro g hg
    have : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination hg
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hb' : γ' 0 1 ≠ 0 := by
    intro hb0
    have hone : γ' = 1 ∨ γ' = -1 := by
      rcases hpm γ' hsq' with ha | ha
      · left
        exact s30l_eq_of_entries (by simp [ha]) (by simp [hb0]) (by simp [hA₀]) (by simp [hda γ' hA₀ hsq', ha])
      · right
        exact s30l_eq_of_entries (by simp [ha, Matrix.SpecialLinearGroup.coe_neg]) (by simp [hb0])
          (by simp [hA₀]) (by simp [hda γ' hA₀ hsq', ha, Matrix.SpecialLinearGroup.coe_neg])
    have hγeq : γ = A₀⁻¹ * γ' * A₀ := by rw [hγ'def]; group
    rcases hone with h | h
    · exact h1 (by rw [hγeq, h]; group)
    · exact h2 (by rw [hγeq, h]; simp)
  have hstab' := s30l_stab_sq_one hΓ' hγ'mem hA₀ hsq' hb'
  -- the group of translation lengths of `Γ' = A₀ Γ A₀⁻¹` at `∞`
  let T : AddSubgroup ℝ :=
    { carrier := {t | ∃ g ∈ conjGroup Γ A₀, g 1 0 = 0 ∧ g 0 0 ^ 2 = 1 ∧ g 0 1 = g 0 0 * t}
      zero_mem' := ⟨1, (conjGroup Γ A₀).one_mem, by simp, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨g₁, hg₁, a1, a2, a3⟩ ⟨g₂, hg₂, b1, b2, b3⟩
        obtain ⟨m00, m01, m10, m11⟩ := s30l_mul_entries g₁ g₂
        refine ⟨g₁ * g₂, (conjGroup Γ A₀).mul_mem hg₁ hg₂, ?_, ?_, ?_⟩
        · rw [m10, a1, b1]
          ring
        · rw [m00, b1, mul_zero, add_zero, mul_pow, a2, b2]
          ring
        · rw [m01, m00, b1, a3, b3, hda g₂ b1 b2]
          ring
      neg_mem' := by
        rintro _ ⟨g, hg, a1, a2, a3⟩
        obtain ⟨i00, i01, i10, i11⟩ := s30l_inv_apply g
        refine ⟨g⁻¹, (conjGroup Γ A₀).inv_mem hg, ?_, ?_, ?_⟩
        · rw [i10, a1, neg_zero]
        · rw [i00, hda g a1 a2]
          exact a2
        · rw [i01, i00, hda g a1 a2, a3]
          ring }
  have hmemT : ∀ t, t ∈ T ↔ ∃ g ∈ conjGroup Γ A₀, g 1 0 = 0 ∧ g 0 0 ^ 2 = 1 ∧ g 0 1 = g 0 0 * t := fun t => Iff.rfl
  have hγ'T : γ' 0 0 * γ' 0 1 ∈ T := by
    refine (hmemT _).2 ⟨γ', hγ'mem, hA₀, hsq', ?_⟩
    linear_combination (-(γ' 0 1)) * hsq'
  -- `T ∩ (0, 1)` is finite: such a `t` is `|b|` for an element moving `i` by less than `1`
  have hSfin := hΓ' (Metric.closedBall UpperHalfPlane.I 1) (isCompact_closedBall _ _)
  have hPfin : {t | t ∈ T ∧ 0 < t ∧ t < 1}.Finite := by
    refine (hSfin.image (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => |g 0 1|)).subset ?_
    rintro t ⟨ht, ht0, ht1⟩
    obtain ⟨g, hg, a1, a2, a3⟩ := (hmemT t).1 ht
    have habs : |g 0 1| = t := by
      have hg0 : |g 0 0| = 1 := by
        have := sq_abs (g 0 0)
        rw [a2] at this
        exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 this
      rw [a3, abs_mul, hg0, one_mul, abs_of_pos ht0]
    refine ⟨g, ⟨hg, g • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self zero_le_one, rfl⟩, ?_⟩, habs⟩
    rw [mem_closedBall, dist_comm]
    exact (s30l_dist_transl a1 a2).trans (by rw [habs]; exact ht1.le)
  obtain ⟨ε, hε0, hεdisj⟩ : ∃ ε > (0 : ℝ), Disjoint (T : Set ℝ) (Ioo 0 ε) := by
    by_cases hP : {t | t ∈ T ∧ 0 < t ∧ t < 1}.Nonempty
    · obtain ⟨m, hm, hmin⟩ := Set.exists_min_image _ id hPfin hP
      refine ⟨m, hm.2.1, Set.disjoint_left.2 fun t ht ⟨h0, hlt⟩ => ?_⟩
      exact absurd (hmin t ⟨ht, h0, hlt.trans hm.2.2⟩) (not_le.2 hlt)
    · exact ⟨1, one_pos, Set.disjoint_left.2 fun t ht ⟨h0, hlt⟩ => hP ⟨t, ht, h0, hlt⟩⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, T = AddSubgroup.closure {t₀} := by
    obtain ⟨g, hg⟩ := T.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      (AddSubgroup.isAddCyclic_of_disjoint_Ioo_zero hε0 hεdisj)
    exact ⟨g, by rw [← hg, AddSubgroup.zmultiples_eq_closure]⟩
  have ht₀mem : t₀ ∈ T := by
    rw [ht₀]
    exact AddSubgroup.subset_closure rfl
  have hn : ∀ t ∈ T, ∃ n : ℤ, t = n * t₀ := by
    intro t ht
    rw [ht₀, AddSubgroup.mem_closure_singleton] at ht
    obtain ⟨n, rfl⟩ := ht
    exact ⟨n, by simp⟩
  have ht₀ne : t₀ ≠ 0 := by
    intro h0
    obtain ⟨n, hn'⟩ := hn _ hγ'T
    rw [h0, mul_zero] at hn'
    have : γ' 0 0 * γ' 0 1 = 0 := hn'
    rcases mul_eq_zero.1 this with h | h
    · have := hpm γ' hsq'
      rcases this with h' | h' <;> rw [h'] at h <;> norm_num at h
    · exact hb' h
  -- `u = |t₀| > 0` generates `T` as well
  obtain ⟨u, hu0, huT, hu⟩ : ∃ u : ℝ, 0 < u ∧ u ∈ T ∧ ∀ t ∈ T, ∃ n : ℤ, t = n * u := by
    refine ⟨|t₀|, abs_pos.2 ht₀ne, ?_, fun t ht => ?_⟩
    · rcases abs_choice t₀ with h | h
      · rw [h]
        exact ht₀mem
      · rw [h]
        exact T.neg_mem ht₀mem
    · obtain ⟨n, rfl⟩ := hn t ht
      rcases abs_choice t₀ with h | h
      · exact ⟨n, by rw [h]⟩
      · exact ⟨-n, by rw [h]; push_cast; ring⟩
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 * u = 1 :=
    ⟨1 / Real.sqrt u, by positivity, by rw [div_pow, Real.sq_sqrt hu0.le]; field_simp⟩
  have hs : s ≠ 0 := hs0.ne'
  obtain ⟨D, hD00, hD01, hD10, hD11⟩ : ∃ D : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      D 0 0 = s ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = s⁻¹ :=
    ⟨⟨!![s, 0; 0, s⁻¹], by rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hs]; ring⟩, by simp, by simp, by simp, by simp⟩
  obtain ⟨γ₁, hγ₁0, hγ₁1, hγ₁2, hγ₁3⟩ : ∃ γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1 :=
    ⟨⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩, by simp, by simp, by simp, by simp⟩
  have h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1 := ⟨hγ₁0, hγ₁1, hγ₁2, hγ₁3⟩
  -- every element of `A Γ A⁻¹` fixing `∞` is `± γ₁^n`
  have hmain : ∀ β ∈ conjGroup Γ (D * A₀), β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n := by
    intro β hβ hβ10
    obtain ⟨h, hh, rfl⟩ := s30l_mem_conjGroup.1 hβ
    have hgmem : A₀ * h * A₀⁻¹ ∈ conjGroup Γ A₀ := s30l_mem_conjGroup.2 ⟨h, hh, rfl⟩
    have hconj : D * A₀ * h * (D * A₀)⁻¹ = D * (A₀ * h * A₀⁻¹) * D⁻¹ := by group
    obtain ⟨e00, e01, e10, e11⟩ := s30l_conj_diag (g := A₀ * h * A₀⁻¹) hs hD00 hD01 hD10 hD11
    rw [hconj] at hβ10
    rw [e10] at hβ10
    have hg10 : (A₀ * h * A₀⁻¹) 1 0 = 0 := by
      rcases mul_eq_zero.1 hβ10 with h' | h'
      · exact absurd h' (pow_ne_zero 2 (inv_ne_zero hs))
      · exact h'
    have hgsq := hstab' _ hgmem hg10
    have hgT : (A₀ * h * A₀⁻¹) 0 0 * (A₀ * h * A₀⁻¹) 0 1 ∈ T := by
      refine (hmemT _).2 ⟨_, hgmem, hg10, hgsq, ?_⟩
      linear_combination (-((A₀ * h * A₀⁻¹) 0 1)) * hgsq
    obtain ⟨n, hn'⟩ := hu _ hgT
    obtain ⟨z00, z01, z10, z11⟩ := s30l_zpow_entries h₁ n
    refine ⟨n, ?_⟩
    rw [hconj]
    have hd := hda _ hg10 hgsq
    rcases hpm _ hgsq with ha | ha
    · left
      refine s30l_eq_of_entries ?_ ?_ ?_ ?_
      · rw [e00, ha, z00]
      · rw [e01, z01]
        have : (A₀ * h * A₀⁻¹) 0 1 = n * u := by
          have := hn'
          rw [ha] at this
          linarith
        rw [this]
        linear_combination (n : ℝ) * hs2
      · rw [e10, hg10, z10]
        ring
      · rw [e11, hd, ha, z11]
    · right
      refine s30l_eq_of_entries ?_ ?_ ?_ ?_
      · rw [e00, ha, Matrix.SpecialLinearGroup.coe_neg]
        simp [z00]
      · rw [e01, Matrix.SpecialLinearGroup.coe_neg]
        simp only [Matrix.neg_apply, z01]
        have : (A₀ * h * A₀⁻¹) 0 1 = -(n * u) := by
          have := hn'
          rw [ha] at this
          linarith
        rw [this]
        linear_combination (-(n : ℝ)) * hs2
      · rw [e10, hg10, Matrix.SpecialLinearGroup.coe_neg]
        simp [z10]
      · rw [e11, hd, ha, Matrix.SpecialLinearGroup.coe_neg]
        simp [z11]
  -- `γ₁ = ±(D g₀ D⁻¹)` for the generator `g₀` of the translations
  have hgen : γ₁ ∈ conjGroup Γ (D * A₀) ∨ -γ₁ ∈ conjGroup Γ (D * A₀) := by
    obtain ⟨g₀, hg₀, a1, a2, a3⟩ := (hmemT u).1 huT
    obtain ⟨h, hh, hgdef⟩ := s30l_mem_conjGroup.1 hg₀
    have hconj : D * A₀ * h * (D * A₀)⁻¹ = D * g₀ * D⁻¹ := by rw [hgdef]; group
    obtain ⟨e00, e01, e10, e11⟩ := s30l_conj_diag (g := g₀) hs hD00 hD01 hD10 hD11
    have hd := hda g₀ a1 a2
    rcases hpm g₀ a2 with ha | ha
    · left
      refine s30l_mem_conjGroup.2 ⟨h, hh, ?_⟩
      rw [hconj]
      refine s30l_eq_of_entries ?_ ?_ ?_ ?_
      · rw [e00, ha, hγ₁0]
      · rw [e01, a3, ha, hγ₁1]
        linear_combination (-1 : ℝ) * hs2
      · rw [e10, a1, hγ₁2]
        ring
      · rw [e11, hd, ha, hγ₁3]
    · right
      refine s30l_mem_conjGroup.2 ⟨h, hh, ?_⟩
      rw [hconj]
      refine s30l_eq_of_entries ?_ ?_ ?_ ?_
      · rw [e00, ha, Matrix.SpecialLinearGroup.coe_neg]
        simp [hγ₁0]
      · rw [e01, a3, ha, Matrix.SpecialLinearGroup.coe_neg]
        simp only [Matrix.neg_apply, hγ₁1]
        linear_combination hs2
      · rw [e10, a1, Matrix.SpecialLinearGroup.coe_neg]
        simp [hγ₁2]
      · rw [e11, hd, ha, Matrix.SpecialLinearGroup.coe_neg]
        simp [hγ₁3]
  have hβmem : (D * A₀) * γ * (D * A₀)⁻¹ ∈ conjGroup Γ (D * A₀) := s30l_mem_conjGroup.2 ⟨γ, hγ, rfl⟩
  have hβeq : (D * A₀) * γ * (D * A₀)⁻¹ = D * γ' * D⁻¹ := by rw [hγ'def]; group
  have hβ10 : ((D * A₀) * γ * (D * A₀)⁻¹) 1 0 = 0 := by
    rw [hβeq, (s30l_conj_diag (g := γ') hs hD00 hD01 hD10 hD11).2.2.1, hA₀, mul_zero]
  obtain ⟨m, hm⟩ := hmain _ hβmem hβ10
  refine ⟨D * A₀, γ₁, m, hgen, h₁, hmain, ?_, hm⟩
  rintro rfl
  have hγeq : γ = (D * A₀)⁻¹ * ((D * A₀) * γ * (D * A₀)⁻¹) * (D * A₀) := by group
  rcases hm with h | h
  · rw [zpow_zero] at h
    exact h1 (by rw [hγeq, h]; group)
  · rw [zpow_zero] at h
    exact h2 (by rw [hγeq, h]; simp)

/-- Helper for `s30l_forward`: `-I` acts trivially on `ℍ`. -/
theorem s30l_neg_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : UpperHalfPlane) : (-g) • x = g • x := by
  have : -g = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g := by rw [neg_one_mul]
  rw [this, mul_smul, s27g_neg_one_smul]

/-- Helper for `s30l_forward`: the group `Γ' ∪ -Γ'` generated by `Γ'` and `-I` (same action on `ℍ`) is again a Fuchsian
group. -/
theorem s30l_pm_group (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    ∃ Γt : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ), (∀ g, g ∈ Γt ↔ g ∈ Γ' ∨ -g ∈ Γ') ∧
      (IsFuchsian Γ' → IsFuchsian Γt) := by
  let Γt : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    { carrier := {g | g ∈ Γ' ∨ -g ∈ Γ'}
      one_mem' := Or.inl Γ'.one_mem
      mul_mem' := by
        rintro g₁ g₂ (h₁ | h₁) (h₂ | h₂)
        · exact Or.inl (Γ'.mul_mem h₁ h₂)
        · refine Or.inr ?_
          rw [← mul_neg]
          exact Γ'.mul_mem h₁ h₂
        · refine Or.inr ?_
          rw [← neg_mul]
          exact Γ'.mul_mem h₁ h₂
        · refine Or.inl ?_
          rw [← neg_mul_neg]
          exact Γ'.mul_mem h₁ h₂
      inv_mem' := by
        rintro g (h | h)
        · exact Or.inl (Γ'.inv_mem h)
        · refine Or.inr ?_
          have : -g⁻¹ = (-g)⁻¹ := by
            refine (inv_eq_of_mul_eq_one_right ?_).symm
            rw [neg_mul_neg, mul_inv_cancel]
          rw [this]
          exact Γ'.inv_mem h }
  refine ⟨Γt, fun g => Iff.rfl, fun hΓ' C hC => ?_⟩
  refine ((hΓ' C hC).union ((hΓ' C hC).image (fun g => -g))).subset ?_
  rintro g ⟨hg, hne⟩
  rcases hg with h | h
  · exact Or.inl ⟨h, hne⟩
  · refine Or.inr ⟨-g, ⟨h, ?_⟩, neg_neg g⟩
    obtain ⟨y, ⟨x, hxC, hxy⟩, hyC⟩ := hne
    exact ⟨y, ⟨x, hxC, by rw [← hxy]; exact s30l_neg_smul g x⟩, hyC⟩

/-- Helper for `s30l_forward`: `γ₁ⁿ` acts on `ℍ` as the translation `z ↦ z + n`. -/
theorem s30l_transl_coe {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1) (n : ℤ) (x : UpperHalfPlane) :
    ((γ₁ ^ n • x : UpperHalfPlane) : ℂ) = (x : ℂ) + n := by
  obtain ⟨z00, z01, z10, z11⟩ := s30l_zpow_entries h₁ n
  rw [h36t_coe_smul, z00, z01, z10, z11]
  simp

/-- Helper for `s30l_forward`: for `|c| ≥ 1`, `Im (g κ) ≤ 1/Im κ`. -/
theorem s30l_im_smul_le {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : 1 ≤ |g 1 0|) (κ : UpperHalfPlane) :
    (g • κ).im ≤ 1 / κ.im := by
  have hκ : 0 < κ.im := κ.im_pos
  have hcoe : (g • κ).im = ((g • κ : UpperHalfPlane) : ℂ).im := rfl
  rw [hcoe, h36t_coe_smul, utm_im_mobius (hnf_sl2_det g)]
  have hκim : κ.im = (κ : ℂ).im := rfl
  have hc2 : 1 ≤ g 1 0 ^ 2 := by nlinarith [sq_abs (g 1 0), abs_nonneg (g 1 0)]
  have hnsq : (g 1 0 * (κ : ℂ).im) ^ 2 ≤ Complex.normSq ((g 1 0 : ℂ) * (κ : ℂ) + g 1 1) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_im, zero_mul, sub_zero, add_zero]
    nlinarith [sq_nonneg (g 1 0 * (κ : ℂ).re + g 1 1)]
  have hN : κ.im ^ 2 ≤ Complex.normSq ((g 1 0 : ℂ) * (κ : ℂ) + g 1 1) := by
    refine le_trans ?_ hnsq
    rw [mul_pow, ← hκim]
    nlinarith [sq_nonneg κ.im]
  have hNpos : 0 < Complex.normSq ((g 1 0 : ℂ) * (κ : ℂ) + g 1 1) := lt_of_lt_of_le (by positivity) hN
  rw [← hκim, div_le_div_iff₀ hNpos hκ]
  nlinarith

/-- Helper for `s30l_forward`: the cusp at `∞`. For `γ₁ : z ↦ z + 1` generating (up to `±`) the stabilizer of `∞` in the
Fuchsian group `Γ'` uniformizing `S` by `p`, with `γ₁` in `Γ'` up to `±`: (a) `p` is invariant under `γ₁ⁿ`;
(b) two points of the horodisc `{Im > 1}` with the same image differ by an integer; (c) a point `τ` of the horodisc
equivalent to `κ ∈ ℍ` has `Im τ ≤ max (Im κ) (1/Im κ)` (Shimizu: `β(D) ∩ D = ∅` for `β ∉ ⟨γ₁⟩`, `|c| ≥ 1`). -/
theorem s30l_cusp {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ' p)
    (hΓ' : IsFuchsian Γ') {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1) (hγ₁ : γ₁ ∈ Γ' ∨ -γ₁ ∈ Γ')
    (hstab : ∀ β ∈ Γ', β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n) :
    (∀ (n : ℤ) (x : UpperHalfPlane), p (γ₁ ^ n • x) = p x) ∧
    (∀ τ τ' : UpperHalfPlane, 1 < τ.im → 1 < τ'.im → p τ = p τ' → ∃ n : ℤ, (τ' : ℂ) = τ + n) ∧
    (∀ κ τ : UpperHalfPlane, 1 < τ.im → p τ = p κ → τ.im ≤ max κ.im (1 / κ.im)) := by
  obtain ⟨Γt, hΓt, hFt⟩ := s30l_pm_group Γ'
  have hFuch := hFt hΓ'
  have hγ₁t : γ₁ ∈ Γt := (hΓt _).2 hγ₁
  have hstabt : ∀ β ∈ Γt, β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n := by
    intro β hβ hβ10
    rcases (hΓt _).1 hβ with h | h
    · exact hstab β h hβ10
    · obtain ⟨n, hn | hn⟩ := hstab (-β) h (by simp [hβ10])
      · exact ⟨n, Or.inr (neg_eq_iff_eq_neg.1 hn)⟩
      · exact ⟨n, Or.inl (neg_inj.1 hn)⟩
  have hinv1 : ∀ x, p (γ₁ • x) = p x := by
    intro x
    rcases hγ₁ with h | h
    · exact s30a_p_smul hp h x
    · rw [← s30l_neg_smul γ₁ x]
      exact s30a_p_smul hp h x
  have ha : ∀ (n : ℤ) (x : UpperHalfPlane), p (γ₁ ^ n • x) = p x := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [zpow_add_one, mul_smul, ih, hinv1]
    | pred i ih =>
      intro x
      rw [zpow_sub_one, mul_smul, ih]
      have := hinv1 (γ₁⁻¹ • x)
      rw [smul_inv_smul] at this
      exact this.symm
  have key : ∀ g ∈ Γt, (¬ ∃ n : ℤ, g = γ₁ ^ n ∨ g = -γ₁ ^ n) →
      1 ≤ |g 1 0| ∧ ∀ τ : UpperHalfPlane, 1 < (τ : ℂ).im → ((g • τ : UpperHalfPlane) : ℂ).im ≤ 1 := by
    intro g hg hnot
    exact parabolic_horoball_disjoint hFuch hγ₁t h₁ hstabt hg fun n => ⟨fun h => hnot ⟨n, Or.inl h⟩, fun h => hnot ⟨n, Or.inr h⟩⟩
  have htrans : ∀ (n : ℤ) (x : UpperHalfPlane), ((γ₁ ^ n • x : UpperHalfPlane) : ℂ) = (x : ℂ) + n :=
    fun n x => s30l_transl_coe h₁ n x
  refine ⟨ha, ?_, ?_⟩
  · intro τ τ' h1 h1' hpeq
    obtain ⟨g, hg, hgτ⟩ := (hp.2.2.2 τ τ').1 hpeq
    have hgt : g ∈ Γt := (hΓt g).2 (Or.inl hg)
    by_cases hex : ∃ n : ℤ, g = γ₁ ^ n ∨ g = -γ₁ ^ n
    · obtain ⟨n, hn⟩ := hex
      refine ⟨n, ?_⟩
      rw [← hgτ]
      rcases hn with rfl | rfl
      · exact htrans n τ
      · rw [s30l_neg_smul]
        exact htrans n τ
    · exfalso
      have := (key g hgt hex).2 τ h1
      rw [hgτ] at this
      exact absurd this (not_le.2 h1')
  · intro κ τ h1 hpeq
    obtain ⟨g, hg, hgκ⟩ := (hp.2.2.2 κ τ).1 hpeq.symm
    have hgt : g ∈ Γt := (hΓt g).2 (Or.inl hg)
    by_cases hex : ∃ n : ℤ, g = γ₁ ^ n ∨ g = -γ₁ ^ n
    · obtain ⟨n, hn⟩ := hex
      refine le_max_of_le_left ?_
      have hτ : (τ : ℂ) = κ + n := by
        rw [← hgκ]
        rcases hn with rfl | rfl
        · exact htrans n κ
        · rw [s30l_neg_smul]
          exact htrans n κ
      have : τ.im = κ.im := by
        show (τ : ℂ).im = (κ : ℂ).im
        rw [hτ]
        simp
      exact this.le
    · refine le_max_of_le_right ?_
      have hc := (key g hgt hex).1
      rw [← hgκ]
      exact s30l_im_smul_le hc κ

/-- Helper for `s30l_forward`: the descent of a holomorphic function through a holomorphic covering, on the image of an open
set `D` on which `c ∘ p = q` (as `s27l_mdifferentiable_descend`, near `p τ` for `τ ∈ D`). -/
theorem s30l_mdiffOn_descend {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {p : UpperHalfPlane → X} (hcov : IsCoveringMap p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {D : Set UpperHalfPlane}
    (hD : IsOpen D) {q : UpperHalfPlane → ℂ} (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q) {c : X → ℂ}
    (hc : ∀ τ ∈ D, c (p τ) = q τ) : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c (p '' D) := by
  rintro _ ⟨τ, hτD, rfl⟩
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ⟩ :=
    h23l_chart_proj (τ := τ) hcov hhol _ (mem_chart_source ℂ _)
  have hconf₀ := thm7_3_one_qc_conformal hψ
  -- shrink to the part over `D`
  set U : Set ℂ := U₀ ∩ ((↑) : UpperHalfPlane → ℂ) '' D with hU
  have hUo : IsOpen U := hU₀o.inter (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap D hD)
  have hτU : (τ : ℂ) ∈ U := ⟨hτU₀, τ, hτD, rfl⟩
  set φ : ℂ → ℂ := fun z => chartAt ℂ (p τ) (p (UpperHalfPlane.ofComplex z)) with hφ
  have hconf : IsConformalOnto φ U (φ '' U) :=
    ⟨hconf₀.1.mono inter_subset_left, hconf₀.2.1.mono inter_subset_left, rfl⟩
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
    have hpw : p (UpperHalfPlane.ofComplex w) = y := (chartAt ℂ (p τ)).injOn (hU₀s w hw.1) hy.1 hwy
    have hwD : UpperHalfPlane.ofComplex w ∈ D := by
      obtain ⟨d, hd, hdw⟩ := hw.2
      rw [← hdw, UpperHalfPlane.ofComplex_apply]
      exact hd
    show c y = q (UpperHalfPlane.ofComplex (Function.invFunOn φ U (chartAt ℂ (p τ) y)))
    rw [hψw, ← hc _ hwD, hpw]
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

/-- Helper for `s30l_forward`: a compact subset of the base of a covering of `ℍ` lies under a compact subset of `ℍ`. -/
theorem s30l_compact_cover {X : Type*} [TopologicalSpace X] {p : UpperHalfPlane → X} (hcov : IsCoveringMap p)
    (hsurj : Function.Surjective p) {K : Set X} (hK : IsCompact K) :
    ∃ K' : Set UpperHalfPlane, IsCompact K' ∧ K ⊆ p '' K' := by
  have hopen : IsOpenMap p := hcov.isLocalHomeomorph.isOpenMap
  have hN : ∀ x : X, ∃ N : Set UpperHalfPlane, IsCompact N ∧ p '' N ∈ 𝓝 x := by
    intro x
    obtain ⟨τ, rfl⟩ := hsurj x
    obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds τ
    refine ⟨N, hNc, ?_⟩
    have : p '' interior N ∈ 𝓝 (p τ) :=
      (hopen _ isOpen_interior).mem_nhds ⟨τ, mem_interior_iff_mem_nhds.2 hNn, rfl⟩
    exact Filter.mem_of_superset this (image_mono interior_subset)
  choose N hNc hNn using hN
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x => p '' N x) (fun x _ => hNn x)
  refine ⟨⋃ x ∈ t, N x, t.finite_toSet.isCompact_biUnion fun x _ => hNc x, ?_⟩
  intro y hy
  obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.1 (htK hy)
  exact ⟨z, mem_iUnion₂.2 ⟨x, hx, hz⟩, rfl⟩

/-- Helper for `s30l_forward`: the lift of the powers of a loop. If `e` is a path in `ℍ` from `τ₁` to `κ τ₁` projecting to the
loop `L`, and `p ∘ κ = p`, then `Lⁿ` lifts to a path from `τ₁` to `κⁿ τ₁` (`Path.trans` of the lifts). -/
theorem s30l_lift_pow {S : Type u} [TopologicalSpace S] {p : UpperHalfPlane → S} {κ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hκ : ∀ x, p (κ • x) = p x) {τ₁ : UpperHalfPlane} (e : Path τ₁ (κ • τ₁)) (L : Loop S) (hL1 : L.1 = p τ₁)
    (hL : ∀ t, L.2 t = p (e t)) :
    ∀ n : ℕ, ∃ ê : Path τ₁ (κ ^ n • τ₁), ∀ t, p (ê t) = (loopNatPow L n) t := by
  have hκn : ∀ (n : ℕ) (x : UpperHalfPlane), p (κ ^ n • x) = p x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, mul_smul, ih, hκ]
  intro n
  induction n with
  | zero =>
    refine ⟨(Path.refl τ₁).cast rfl (by rw [pow_zero, one_smul]), fun t => ?_⟩
    show p τ₁ = (Path.refl L.1) t
    rw [Path.refl_apply, hL1]
  | succ n ih =>
    obtain ⟨ê, hê⟩ := ih
    let f : Path (κ ^ n • τ₁) (κ ^ (n + 1) • τ₁) :=
      (e.map (continuous_const_smul (κ ^ n))).cast rfl (by rw [pow_succ, mul_smul])
    refine ⟨ê.trans f, fun t => ?_⟩
    show p ((ê.trans f) t) = ((loopNatPow L n).trans L.2) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact hê _
    · show p (κ ^ n • e _) = L.2 _
      rw [hκn, hL]

/-- Helper for `s30l_forward`: the necessity in normalized form, for the uniformization `p` with covering group `Γ'`. -/
theorem s30l_forward_core {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ' p)
    (hΓ' : IsFuchsian Γ') {γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1) (hγ₁ : γ₁ ∈ Γ' ∨ -γ₁ ∈ Γ')
    (hstab : ∀ β ∈ Γ', β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ') {m : ℤ} (hm : m ≠ 0)
    (hγm : γ = γ₁ ^ m ∨ γ = -γ₁ ^ m) {α : Loop S} (hcov : Covers p γ α) :
    ∃ (U : Set S) (φ : S → ℂ) (β : Loop S) (r : ℝ) (n : ℤ), IsPunctureNbhd U φ ∧
      0 < r ∧ r < 1 ∧ range β.2 ⊆ U ∧ (∀ t : unitInterval, φ (β.2 t) = (r : ℂ) * exp (2 * π * I * (t : ℝ))) ∧
      n ≠ 0 ∧ FreelyHomotopic α (loopPow β n) := by
  classical
  obtain ⟨ha, hb, hc⟩ := s30l_cusp hp hΓ' h₁ hγ₁ hstab
  have htr := fun (n : ℤ) (x : UpperHalfPlane) => s30l_transl_coe h₁ n x
  obtain ⟨D, hD⟩ : ∃ D : Set UpperHalfPlane, D = {τ | 1 < τ.im} := ⟨_, rfl⟩
  have hDo : IsOpen D := by
    rw [hD]
    exact isOpen_lt continuous_const UpperHalfPlane.continuous_im
  have hDmem : ∀ τ : UpperHalfPlane, τ ∈ D ↔ 1 < τ.im := fun τ => by rw [hD]; rfl
  -- the function `q(τ) = exp(2πi(τ - i))`
  obtain ⟨q, hq⟩ : ∃ q : UpperHalfPlane → ℂ, q = fun τ : UpperHalfPlane => exp (2 * π * I * ((τ : ℂ) - I)) := ⟨_, rfl⟩
  have hqd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q := by
    have hg : Differentiable ℂ (fun z : ℂ => exp (2 * π * I * (z - I))) := by fun_prop
    rw [hq]
    exact hg.mdifferentiable.comp UpperHalfPlane.mdifferentiable_coe
  have hqper : ∀ (z : ℂ) (n : ℤ), exp (2 * π * I * ((z + n) - I)) = exp (2 * π * I * (z - I)) := by
    intro z n
    rw [show 2 * π * I * ((z + n) - I) = 2 * π * I * (z - I) + n * (2 * π * I) by ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hqnorm : ∀ τ : UpperHalfPlane, ‖q τ‖ = Real.exp (-(2 * π) * (τ.im - 1)) := by
    intro τ
    rw [hq]
    simp only
    rw [Complex.norm_exp]
    congr 1
    simp
  -- the coordinate `φ`
  obtain ⟨φ, hφdef⟩ : ∃ φ : S → ℂ, φ = fun x => if h : ∃ τ : UpperHalfPlane, 1 < τ.im ∧ p τ = x then
      q h.choose else 0 := ⟨_, rfl⟩
  have hφ : ∀ τ : UpperHalfPlane, 1 < τ.im → φ (p τ) = q τ := by
    intro τ hτ
    have hex : ∃ τ' : UpperHalfPlane, 1 < τ'.im ∧ p τ' = p τ := ⟨τ, hτ, rfl⟩
    rw [hφdef]
    simp only [dif_pos hex]
    obtain ⟨hτ', hpτ'⟩ := hex.choose_spec
    obtain ⟨n, hn⟩ := hb _ τ hτ' hτ hpτ'
    rw [hq]
    simp only
    rw [hn, hqper]
  refine ⟨p '' D, φ, ?_⟩
  have hU : IsPunctureNbhd (p '' D) φ := by
    refine ⟨hp.1.isLocalHomeomorph.isOpenMap D hDo, ?_, ?_, ?_, ?_⟩
    · -- injectivity
      rintro _ ⟨τ, hτ, rfl⟩ _ ⟨τ', hτ', rfl⟩ h
      have hτ1 := (hDmem τ).1 hτ
      have hτ'1 := (hDmem τ').1 hτ'
      rw [hφ τ hτ1, hφ τ' hτ'1, hq] at h
      simp only at h
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
      have hτeq : (τ : ℂ) = τ' + n := by
        have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        have := mul_left_cancel₀ h2π (by linear_combination hn : 2 * π * I * ((τ : ℂ) - I) =
          2 * π * I * ((τ' : ℂ) - I + n))
        linear_combination this
      have : γ₁ ^ n • τ' = τ := UpperHalfPlane.ext (by rw [htr, hτeq])
      rw [← this]
      exact ha n τ'
    · -- image
      ext w
      constructor
      · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
        have hτ1 := (hDmem τ).1 hτ
        rw [hφ τ hτ1]
        show 0 < ‖q τ‖ ∧ ‖q τ‖ < 1
        rw [hqnorm]
        refine ⟨Real.exp_pos _, ?_⟩
        rw [Real.exp_lt_one_iff]
        have : 0 < τ.im - 1 := by linarith
        have := Real.pi_pos
        nlinarith
      · rintro ⟨h0, h1⟩
        have hw : w ≠ 0 := norm_pos_iff.1 h0
        have hlog : Real.log ‖w‖ < 0 := Real.log_neg h0 h1
        have hapos : 0 < -Real.log ‖w‖ / (2 * π) := div_pos (neg_pos.2 hlog) (by positivity)
        obtain ⟨τc, hτim, hτq⟩ : ∃ τc : ℂ, τc.im = 1 + -Real.log ‖w‖ / (2 * π) ∧
            exp (2 * π * I * (τc - I)) = w := by
          refine ⟨((Complex.arg w / (2 * π) : ℝ) : ℂ) + ((1 + -Real.log ‖w‖ / (2 * π) : ℝ) : ℂ) * I, ?_, ?_⟩
          · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
              Complex.I_im]
            ring
          · have hq2 : 2 * π * I * (((Complex.arg w / (2 * π) : ℝ) : ℂ) +
                ((1 + -Real.log ‖w‖ / (2 * π) : ℝ) : ℂ) * I - I) = Complex.log w := by
              have hlogw : Complex.log w = (Real.log ‖w‖ : ℂ) + (w.arg : ℂ) * I := by
                apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
              have h2π : (2 * (π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
              have e2 : (2 * (π : ℂ)) * ((w.arg : ℂ) / (2 * π)) = w.arg := mul_div_cancel₀ _ h2π
              have e3 : (2 * (π : ℂ)) * ((Real.log ‖w‖ : ℂ) / (2 * π)) = Real.log ‖w‖ :=
                mul_div_cancel₀ _ h2π
              rw [hlogw]
              push_cast
              linear_combination I * e2 - I ^ 2 * e3 - (Real.log ‖w‖ : ℂ) * Complex.I_sq
            rw [hq2, Complex.exp_log hw]
        have hpos : 0 < τc.im := by rw [hτim]; linarith
        refine ⟨p ⟨τc, hpos⟩, ⟨⟨τc, hpos⟩, ?_, rfl⟩, ?_⟩
        · rw [hDmem]
          show 1 < τc.im
          rw [hτim]
          linarith
        · rw [hφ _ (by show 1 < τc.im; rw [hτim]; linarith), hq]
          exact hτq
    · exact s30l_mdiffOn_descend hp.1 hp.2.1 hDo hqd (fun τ hτ => hφ τ ((hDmem τ).1 hτ))
    · -- the end of the puncture leaves every compact set
      intro K hK
      obtain ⟨K', hK'c, hKsub⟩ := s30l_compact_cover hp.1 hp.2.2.1 hK
      have hcont : Continuous fun κ : UpperHalfPlane => max κ.im (1 / κ.im) :=
        UpperHalfPlane.continuous_im.max (continuous_const.div UpperHalfPlane.continuous_im
          (fun κ => κ.im_pos.ne'))
      obtain ⟨H₀, hH₀⟩ := (hK'c.image hcont).bddAbove
      refine ⟨Real.exp (-(2 * π) * (max H₀ 0 + 1)), Real.exp_pos _, ?_⟩
      rintro _ ⟨τ, hτ, rfl⟩ hlt hxK
      have hτ1 := (hDmem τ).1 hτ
      rw [hφ τ hτ1, hqnorm, Real.exp_lt_exp] at hlt
      obtain ⟨κ, hκ, hκp⟩ := hKsub hxK
      have h1 := hc κ τ hτ1 hκp.symm
      have h2 : max κ.im (1 / κ.im) ≤ H₀ := hH₀ ⟨κ, hκ, rfl⟩
      have := Real.pi_pos
      nlinarith [le_max_left H₀ 0]
  -- the loop `β(t) = p(t + 2i)` around the puncture
  obtain ⟨ee, hee⟩ : ∃ ee : C(unitInterval, UpperHalfPlane), ∀ t, (ee t : ℂ) = ((t : ℝ) : ℂ) + 2 * I := by
    refine ⟨⟨fun t => ⟨((t : ℝ) : ℂ) + 2 * I, ?_⟩, ?_⟩, fun t => rfl⟩
    · show 0 < (((t : ℝ) : ℂ) + 2 * I).im
      simp
    · exact UpperHalfPlane.isEmbedding_coe.continuous_iff.2
        ((Complex.continuous_ofReal.comp continuous_subtype_val).add continuous_const)
  have heeim : ∀ t, 1 < (ee t).im := by
    intro t
    show 1 < ((ee t : UpperHalfPlane) : ℂ).im
    rw [hee t]
    simp
  have he1 : ee 1 = γ₁ • ee 0 := by
    apply UpperHalfPlane.ext
    have := htr 1 (ee 0)
    rw [zpow_one] at this
    rw [this, hee, hee]
    simp
    ring
  have hinv1 : ∀ x, p (γ₁ • x) = p x := fun x => by simpa using ha 1 x
  have hinvm1 : ∀ x, p (γ₁⁻¹ • x) = p x := fun x => by simpa using ha (-1) x
  have hpe : p (ee 1) = p (ee 0) := by rw [he1]; exact hinv1 _
  let β : Loop S := s30a_projLoop p hp.1.continuous ee hpe
  have hβ : ∀ t, β.2 t = p (ee t) := fun t => rfl
  refine ⟨β, Real.exp (-(2 * π)), m, hU, Real.exp_pos _, ?_, ?_, ?_, hm, ?_⟩
  · exact Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  · rintro _ ⟨t, rfl⟩
    exact ⟨ee t, (hDmem _).2 (heeim t), (hβ t).symm⟩
  · intro t
    rw [hβ t, hφ (ee t) (heeim t), hq]
    simp only
    rw [hee t, show (2 * π * I * (((t : ℝ) : ℂ) + 2 * I - I)) =
      ((-(2 * π) : ℝ) : ℂ) + 2 * π * I * (t : ℝ) by push_cast; linear_combination (2 * (π : ℂ)) * Complex.I_sq,
      Complex.exp_add, Complex.ofReal_exp]
  · -- the free homotopy `α ≃ β^m`
    have hγact : ∀ x : UpperHalfPlane, γ • x = γ₁ ^ m • x := by
      intro x
      rcases hγm with rfl | rfl
      · rfl
      · exact s30l_neg_smul _ x
    let eP : Path (ee 0) (γ₁ • ee 0) := ⟨ee, rfl, he1⟩
    rcases le_or_gt 0 m with h0 | hneg
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      obtain ⟨ê, hê⟩ := s30l_lift_pow hinv1 eP β rfl (fun t => rfl) k
      refine s30a_fh_bwd hp hγ hcov (ê : C(unitInterval, UpperHalfPlane)) ?_ (loopPow β k) fun t => ?_
      · rw [hγact]
        show ê 1 = γ₁ ^ (k : ℤ) • ê 0
        rw [ê.target, ê.source, zpow_natCast]
      · simp only [loopPow, Int.natCast_nonneg, if_true, Int.toNat_natCast]
        exact (hê t).symm
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
      subst hk
      let e' : Path (ee 0) (γ₁⁻¹ • ee 0) :=
        (eP.symm.map (continuous_const_smul γ₁⁻¹)).cast (inv_smul_smul γ₁ (ee 0)).symm rfl
      let L' : Loop S := ⟨β.1, β.2.symm⟩
      obtain ⟨ê, hê⟩ := s30l_lift_pow hinvm1 e' L' rfl (fun t => by
        show β.2 (unitInterval.symm t) = p (γ₁⁻¹ • eP (unitInterval.symm t))
        rw [hinvm1]
        rfl) k
      refine s30a_fh_bwd hp hγ hcov (ê : C(unitInterval, UpperHalfPlane)) ?_ (loopPow β (-(k : ℤ))) fun t => ?_
      · rw [hγact]
        show ê 1 = γ₁ ^ (-(k : ℤ)) • ê 0
        rw [ê.target, ê.source, zpow_neg, zpow_natCast, inv_pow]
      · have hk0 : ¬ (0 ≤ -(k : ℤ)) := by omega
        show (if 0 ≤ -(k : ℤ) then _ else _ : Loop S).2 t = _
        rw [if_neg hk0]
        simp only [neg_neg, Int.toNat_natCast]
        exact (hê t).symm

/-- Helper for **Lemma 30.1** (§30.2), necessity: a covering element conjugate to `±γ₁^m` (`γ₁ : z ↦ z + 1` generating the
stabilizer of `∞`, `m ≠ 0`) gives the punctured-disc neighbourhood. In the conjugated uniformization `p′ = p ∘ A⁻¹` put
`U = p′({Im τ > 1})` and `φ(p′ τ) = exp(2πi(τ - i))`: `U` is open (`p′` is open), `φ` is injective on `U` and onto
`{0 < |ζ| < 1}` (`parabolic_horoball_disjoint`: `β(D) ∩ D = ∅` for `β ∉ ⟨γ₁⟩`; the descent of a holomorphic function through
the local conformal charts of `p′`, as in `s27l_mdifferentiable_descend`, gives `MDifferentiableOn`); `φ` leaves every
compact set as `ζ → 0` (a compact `K ⊆ S` lies under a compact `K̃ ⊆ ℍ`, and a point of `D` high above `K̃` is not
equivalent to a point of `K̃` by the same disjointness); `β(t) = p′(t + 2i)` runs once around `|ζ| = e^{-2π}`; and the
lift `t ↦ τ₁ + nt` of `β^n` (obtained by induction through `Path.map_trans`) is covered by `±γ₁^m`, `n = m`, so
`α ≃ β^n` by `s30a_fh_bwd`. -/
theorem s30l_forward {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {α : Loop S} (hcov : Covers p γ α) {A γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {m : ℤ}
    (hγ₁ : γ₁ ∈ conjGroup Γ A ∨ -γ₁ ∈ conjGroup Γ A) (h₁ : γ₁ 0 0 = 1 ∧ γ₁ 0 1 = 1 ∧ γ₁ 1 0 = 0 ∧ γ₁ 1 1 = 1)
    (hstab : ∀ β ∈ conjGroup Γ A, β 1 0 = 0 → ∃ n : ℤ, β = γ₁ ^ n ∨ β = -γ₁ ^ n) (hm : m ≠ 0)
    (hγm : A * γ * A⁻¹ = γ₁ ^ m ∨ A * γ * A⁻¹ = -γ₁ ^ m) :
    ∃ (U : Set S) (φ : S → ℂ) (β : Loop S) (r : ℝ) (n : ℤ), IsPunctureNbhd U φ ∧
      0 < r ∧ r < 1 ∧ range β.2 ⊆ U ∧ (∀ t : unitInterval, φ (β.2 t) = (r : ℂ) * exp (2 * π * I * (t : ℝ))) ∧
      n ≠ 0 ∧ FreelyHomotopic α (loopPow β n) := by
  have hp' := adjustProjection_isUniformization hp A
  have hΓ' := s30l_isFuchsian_conj hΓ A
  have hγ' : A * γ * A⁻¹ ∈ conjGroup Γ A := s30l_mem_conjGroup.2 ⟨γ, hγ, rfl⟩
  have hcov' : Covers (adjustProjection p A) (A * γ * A⁻¹) α := by
    obtain ⟨c, hcc, hcp, hc1⟩ := hcov
    refine ⟨fun t => A • c t, (continuous_const_smul A).comp_continuousOn hcc, fun t ht => ?_, ?_⟩
    · show p (A⁻¹ • A • c t) = α.2.extend t
      rw [inv_smul_smul]
      exact hcp t ht
    · show A • c 1 = (A * γ * A⁻¹) • A • c 0
      rw [hc1, mul_smul, mul_smul, inv_smul_smul]
  exact s30l_forward_core hp' hΓ' h₁ hγ₁ hstab hγ' hm hγm hcov'

/-- Helper for `s30l_backward`: the inverse `ψ = (φ|U)⁻¹` of the coordinate of a puncture neighbourhood is holomorphic on the
punctured disc (in the chart `χ` at `x₀ = ψ w₀`, `φ ∘ χ⁻¹` is injective holomorphic on an open set, hence conformal, with
holomorphic inverse). -/
theorem s30l_psi_mdiff {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S] {U : Set S}
    {φ : S → ℂ} (hU : IsPunctureNbhd U φ) {w₀ : ℂ} (hw₀ : w₀ ∈ puncturedDisc) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn φ U) w₀ := by
  obtain ⟨hUo, hinj, himg, hmd, -⟩ := hU
  have hw : w₀ ∈ φ '' U := by rw [himg]; exact hw₀
  obtain ⟨x₀, hx₀, rfl⟩ := hw
  set χ := chartAt ℂ x₀ with hχ
  set O : Set ℂ := χ '' (U ∩ χ.source) with hO
  have hOo : IsOpen O :=
    χ.isOpen_image_of_subset_source (hUo.inter χ.open_source) inter_subset_right
  have hOmem : χ x₀ ∈ O := ⟨x₀, ⟨hx₀, mem_chart_source ℂ x₀⟩, rfl⟩
  set g : ℂ → ℂ := fun c => φ (χ.symm c) with hg
  have hgd : DifferentiableOn ℂ g O := by
    rintro _ ⟨y, ⟨hyU, hys⟩, rfl⟩
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ (χ.symm (χ y)) := by
      rw [χ.left_inv hys]
      exact (hmd y hyU).mdifferentiableAt (hUo.mem_nhds hyU)
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.symm (χ y) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀) (χ.map_source hys)
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun c => φ (χ.symm c)) (χ y) := h1.comp (χ y) h2
    exact (mdifferentiableAt_iff_differentiableAt.1 h3).differentiableWithinAt
  have hginj : InjOn g O := by
    rintro _ ⟨y₁, ⟨hy₁U, hy₁s⟩, rfl⟩ _ ⟨y₂, ⟨hy₂U, hy₂s⟩, rfl⟩ h
    simp only [hg, χ.left_inv hy₁s, χ.left_inv hy₂s] at h
    rw [hinj hy₁U hy₂U h]
  have hconf : IsConformalOnto g O (g '' O) := ⟨hgd, hginj, rfl⟩
  have hVo : IsOpen (g '' O) := hconf.isOpen hOo
  have hgc : g (χ x₀) = φ x₀ := by simp only [hg, χ.left_inv (mem_chart_source ℂ x₀)]
  have heq : Function.invFunOn φ U =ᶠ[𝓝 (φ x₀)] fun w => χ.symm (Function.invFunOn g O w) := by
    have hmem : g '' O ∈ 𝓝 (φ x₀) := hVo.mem_nhds ⟨χ x₀, hOmem, hgc⟩
    filter_upwards [hmem] with w hw
    obtain ⟨c, ⟨y, ⟨hyU, hys⟩, rfl⟩, rfl⟩ := hw
    rw [hginj.leftInvOn_invFunOn ⟨y, ⟨hyU, hys⟩, rfl⟩, χ.left_inv hys]
    show Function.invFunOn φ U (φ (χ.symm (χ y))) = y
    rw [χ.left_inv hys]
    exact hinj.leftInvOn_invFunOn hyU
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn g O) (φ x₀) := by
    rw [← hgc]
    exact mdifferentiableAt_iff_differentiableAt.2 (hconf.differentiableAt_invFunOn hOo hOmem)
  have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.symm (Function.invFunOn g O (φ x₀)) := by
    have : Function.invFunOn g O (φ x₀) = χ x₀ := by
      rw [← hgc]
      exact hginj.leftInvOn_invFunOn hOmem
    rw [this]
    exact mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀) (χ.map_source (mem_chart_source ℂ x₀))
  exact (h3.comp (φ x₀) h2).congr_of_eventuallyEq heq

/-- Helper for `s30l_backward`: Schwarz–Pick for lengths. A holomorphic self-map of `ℍ` does not increase the hyperbolic
length of a Lipschitz curve (the pointwise estimate `schwarz_pick_upperHalf`, as in `generalized_schwarz`). -/
theorem s30l_hypLength_comp_le {F : UpperHalfPlane → UpperHalfPlane}
    (hhol : DifferentiableOn ℂ (liftToC F) upperHalf) {c : ℝ → ℂ}
    (hK : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1)) (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) :
    (∃ K : ℝ≥0, LipschitzOnWith K (liftToC F ∘ c) (Icc 0 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < ((liftToC F ∘ c) t).im) ∧ hypLength (liftToC F ∘ c) ≤ hypLength c := by
  have hmaps : MapsTo (liftToC F) upperHalf upperHalf := fun z hz => by
    rw [h23l_liftToC_eq F hz]
    exact (F _).coe_im_pos
  have hpath : IsPathIn upperHalf (c 0) (c 1) (s30a_lr c hK) :=
    ⟨hK, rfl, rfl, by rintro _ ⟨t, ht, rfl⟩; exact him t ht⟩
  obtain ⟨γ', hγ'eq, ⟨hK', -, -, -⟩⟩ := exists_isPathIn_comp isOpen_upperHalf hhol hmaps hpath
  set c₂ : ℝ → ℂ := liftToC F ∘ c with hc₂def
  have him₂ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c₂ t).im := fun t ht => hmaps (him t ht)
  have hK₂ : ∃ K : ℝ≥0, LipschitzOnWith K c₂ (Icc 0 1) := by
    obtain ⟨K', hK'⟩ := hK'
    rw [hγ'eq] at hK'
    exact ⟨K', hK'⟩
  refine ⟨hK₂, him₂, ?_⟩
  obtain ⟨K, hKc⟩ := hK
  have hK1 : LipschitzOnWith K c (uIcc 0 1) := by rwa [uIcc_of_le zero_le_one]
  have hdiff := ae_differentiableAt_of_lipschitzOn hK1
  unfold hypLength
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hdiff] with t ht hd
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hdt : DifferentiableAt ℝ c t := hd (by rw [uIcc_of_le zero_le_one]; exact htI)
  have hy₁ := him t htI
  have hy₂ := him₂ t htI
  have hFd : DifferentiableAt ℂ (liftToC F) (c t) := hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy₁)
  have hchain : deriv c₂ t = deriv (liftToC F) (c t) * deriv c t :=
    (hFd.hasDerivAt.comp t hdt.hasDerivAt).deriv
  have hsp := schwarz_pick_upperHalf hhol hmaps hy₁
  rw [hchain, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos hy₂,
    ← ENNReal.ofReal_div_of_pos hy₁]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul]
  have hb := norm_nonneg (deriv c t)
  calc ‖deriv (liftToC F) (c t)‖ * ‖deriv c t‖ / (c₂ t).im
      = ‖deriv c t‖ * (‖deriv (liftToC F) (c t)‖ / (liftToC F (c t)).im) := by
        simp only [hc₂def, Function.comp_apply]
        ring
    _ ≤ ‖deriv c t‖ * (1 / (c t).im) := mul_le_mul_of_nonneg_left hsp hb
    _ = ‖deriv c t‖ / (c t).im := by ring

/-- Helper for `s30l_backward`: a holomorphic self-map `F` of `ℍ` moves two points at the same height `y` and
horizontal distance `N` by at most `N / y` (the Schwarz–Pick length estimate on the horizontal segment). -/
theorem s30l_dist_translate {F : UpperHalfPlane → UpperHalfPlane} (hhol : DifferentiableOn ℂ (liftToC F) upperHalf)
    (a b : UpperHalfPlane) (hab : (a : ℂ).im = (b : ℂ).im) :
    dist (F a) (F b) ≤ ‖(b : ℂ) - a‖ / (a : ℂ).im := by
  set c : ℝ → ℂ := fun t => (a : ℂ) + (t : ℂ) * ((b : ℂ) - a) with hc
  have hcim : ∀ t : ℝ, (c t).im = (a : ℂ).im := fun t => by
    simp only [hc, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.sub_im, hab, sub_self, mul_zero]
  have hcd : ∀ t : ℝ, HasDerivAt c ((b : ℂ) - a) t := fun t =>
    (hasDerivAt_ofReal_mul ((b : ℂ) - a) t).const_add (a : ℂ)
  have hK : ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1) := by
    refine ⟨‖(b : ℂ) - a‖₊, LipschitzOnWith.of_dist_le_mul fun s _ t _ => ?_⟩
    simp only [hc, dist_eq_norm]
    rw [show (a : ℂ) + (s : ℂ) * ((b : ℂ) - a) - ((a : ℂ) + (t : ℂ) * ((b : ℂ) - a)) =
      ((s : ℂ) - t) * ((b : ℂ) - a) by ring, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, mul_comm]
    simp
  have him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im := fun t _ => by rw [hcim]; exact a.coe_im_pos
  obtain ⟨hK₂, him₂, hle⟩ := s30l_hypLength_comp_le hhol hK him
  have hd := s30a_dist_le_hypLength (liftToC F ∘ c) hK₂ him₂
  have hlen : hypLength c = ENNReal.ofReal (‖(b : ℂ) - a‖ / (a : ℂ).im) := by
    unfold hypLength
    have : ∀ t ∈ Ioo (0 : ℝ) 1, ‖deriv c t‖ₑ / ENNReal.ofReal (c t).im =
        ENNReal.ofReal (‖(b : ℂ) - a‖ / (a : ℂ).im) := by
      intro t _
      rw [(hcd t).deriv, hcim, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos a.coe_im_pos]
    rw [setLIntegral_congr_fun measurableSet_Ioo this, setLIntegral_const, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_one, mul_one]
  have e0 : UpperHalfPlane.mk ((liftToC F ∘ c) 0) (him₂ 0 ⟨le_rfl, zero_le_one⟩) = F a := by
    apply UpperHalfPlane.ext
    simp only [Function.comp_apply, hc, Complex.ofReal_zero, zero_mul, add_zero]
    exact h23l_liftToC_coe F a
  have e1 : UpperHalfPlane.mk ((liftToC F ∘ c) 1) (him₂ 1 ⟨zero_le_one, le_rfl⟩) = F b := by
    apply UpperHalfPlane.ext
    simp only [Function.comp_apply, hc, Complex.ofReal_one, one_mul, add_sub_cancel]
    exact h23l_liftToC_coe F b
  rw [e0, e1] at hd
  have := hd.trans (hle.trans_eq hlen)
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (norm_nonneg _) a.coe_im_pos.le)).1 this

/-- Helper for `s30l_backward`: a holomorphic self-map `Λ` of `ℍ` with `Λ(τ + n) = g Λ(τ)` for a hyperbolic `g` (and `n ≠ 0`)
cannot exist: `d(Λτ, gΛτ) ≥ translationLength g > 0`, but by Schwarz–Pick `d(Λ(iy), Λ(iy + n)) ≤ |n|/y → 0`. -/
theorem s30l_hyp_false {Λ : UpperHalfPlane → UpperHalfPlane} (hhol : DifferentiableOn ℂ (liftToC Λ) upperHalf)
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hh : IsHyperbolic g) {n : ℤ}
    (hΛ : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = τ + n → Λ τ' = g • Λ τ) : False := by
  have htl : 0 < translationLength g := s30a_tl_pos hh
  set y : ℝ := |(n : ℝ)| / translationLength g + 1 with hy
  have hy0 : 0 < y := by positivity
  set a : UpperHalfPlane := ⟨(y : ℂ) * I, by simp [hy0]⟩ with ha
  set b : UpperHalfPlane := ⟨(y : ℂ) * I + n, by simp [hy0]⟩ with hb
  have hba : (b : ℂ) = a + n := rfl
  have hab : (a : ℂ).im = (b : ℂ).im := by simp [ha, hb]
  have h1 := s30l_dist_translate hhol a b hab
  rw [hΛ a b hba] at h1
  have h2 : translationLength g ≤ dist (Λ a) (g • Λ a) := by
    rw [(translationLength_eq_inf_dist hh).1]
    exact ciInf_le ⟨0, by rintro _ ⟨τ, rfl⟩; exact dist_nonneg⟩ (Λ a)
  have hnorm : ‖(b : ℂ) - a‖ = |(n : ℝ)| := by
    rw [hba, add_sub_cancel_left]
    simp
  rw [hnorm] at h1
  have himy : (a : ℂ).im = y := by simp [ha]
  rw [himy] at h1
  have h3 : |(n : ℝ)| / y < translationLength g := by
    rw [div_lt_iff₀ hy0]
    have : |(n : ℝ)| / translationLength g * translationLength g = |(n : ℝ)| := by field_simp
    nlinarith
  linarith

/-- Helper for `s30l_backward`: the case `κ = ±1`. A holomorphic `Λ : ℍ → ℍ` with period `n ≠ 0` and
`p ∘ Λ = ψ ∘ exp(2πi ·)` is impossible when the puncture leaves every compact set. The Cayley transform of `Λ` is bounded,
periodic and holomorphic near `i∞`, so it has a limit `c′` there (`Function.Periodic.tendsto_at_I_inf`, Riemann's removable
singularity theorem). If `|c′| < 1` then `Λ` stays in a compact subset of `ℍ`, so `ψ(ζ)` stays in a compact set as
`ζ → 0`, contradicting the puncture; if `|c′| = 1` the cusp function has a local maximum modulus at `0`, hence is constant,
contradicting `|F(q)| < 1` for `q ≠ 0`. -/
theorem s30l_cusp_false {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S] {p : UpperHalfPlane → S} (hpc : Continuous p) {U : Set S}
    {φ : S → ℂ} (hU : IsPunctureNbhd U φ) {Λ : UpperHalfPlane → UpperHalfPlane}
    (hΛ : DifferentiableOn ℂ (liftToC Λ) upperHalf)
    (hΛp : ∀ τ : UpperHalfPlane, p (Λ τ) = Function.invFunOn φ U (exp (2 * π * I * (τ : ℂ)))) {n : ℤ} (hn : n ≠ 0)
    (hper : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = τ + n → Λ τ' = Λ τ) : False := by
  classical
  obtain ⟨hUo, hinj, himg, hmd, hleave⟩ := hU
  have hh : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  set h : ℝ := |(n : ℝ)| with hhdef
  have hfm : ∀ z : ℂ, 0 < z.im → liftToC Λ z ∈ upperHalf := fun z hz => by
    rw [h23l_liftToC_eq Λ hz]
    exact (Λ _).coe_im_pos
  set f : ℂ → ℂ := fun z => cayley (liftToC Λ z) with hf
  have hfnorm : ∀ z : ℂ, 0 < z.im → ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (cayley_mem_unitDisc (hfm z hz))
  have hfper : Function.Periodic f h := by
    intro z
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + (h : ℂ)).im := by simpa using hz
      show cayley (liftToC Λ (z + h)) = cayley (liftToC Λ z)
      congr 1
      rw [h23l_liftToC_eq Λ hz', h23l_liftToC_eq Λ hz]
      have e1 : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z :=
        by rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      have e2 : ((UpperHalfPlane.ofComplex (z + h) : UpperHalfPlane) : ℂ) = z + h :=
        by rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · have hhn : h = -(n : ℝ) := by rw [hhdef]; exact abs_of_neg (by exact_mod_cast hneg)
        exact (congrArg (fun x : UpperHalfPlane => (x : ℂ)) (hper (UpperHalfPlane.ofComplex (z + h))
          (UpperHalfPlane.ofComplex z) (by rw [e1, e2, hhn]; push_cast; ring))).symm
      · have hhn : h = (n : ℝ) := by rw [hhdef]; exact abs_of_pos (by exact_mod_cast hpos)
        exact congrArg (fun x : UpperHalfPlane => (x : ℂ)) (hper (UpperHalfPlane.ofComplex z)
          (UpperHalfPlane.ofComplex (z + h)) (by rw [e1, e2, hhn]; push_cast; ring))
    · have hz2 : ¬ 0 < (z + (h : ℂ)).im := by simpa using hz
      have e1 : liftToC Λ z = 0 := by unfold liftToC; simp [hz]
      have e2 : liftToC Λ (z + h) = 0 := by unfold liftToC; rw [dif_neg hz2]
      show cayley (liftToC Λ (z + h)) = cayley (liftToC Λ z)
      rw [e1, e2]
  have hpos : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, 0 < z.im :=
    (Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop 0))
  have hfhol : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ f z := by
    filter_upwards [hpos] with z hz
    have h1 : DifferentiableAt ℂ (liftToC Λ) z := hΛ.differentiableAt (isOpen_upperHalf.mem_nhds hz)
    have h2 : DifferentiableAt ℂ cayley (liftToC Λ z) :=
      (hasDerivAt_cayley (cayley_den_ne_zero (hfm z hz))).differentiableAt
    exact h2.comp z h1
  have hfbd : BoundedAtFilter (Filter.comap Complex.im Filter.atTop) f := by
    refine Asymptotics.isBigO_iff.2 ⟨1, ?_⟩
    filter_upwards [hpos] with z hz
    simpa using (hfnorm z hz).le
  have hlim := Function.Periodic.tendsto_at_I_inf hh hfper hfhol hfbd
  set c' : ℂ := Function.Periodic.cuspFunction h f 0 with hc'
  haveI : Filter.NeBot (Filter.comap Complex.im Filter.atTop) := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨x, hx⟩ := (Filter.mem_atTop_sets.1 ht)
    exact ⟨((x : ℝ) : ℂ) * I, by simpa using hx x le_rfl⟩
  have hc'le : ‖c'‖ ≤ 1 := by
    refine le_of_tendsto hlim.norm ?_
    filter_upwards [hpos] with z hz
    exact (hfnorm z hz).le
  have hmem1 : ∀ z : ℂ, 0 < z.im → exp (2 * π * I * z) ∈ puncturedDisc := by
    intro z hz
    have hre : (2 * π * I * z).re = -(2 * π) * z.im := by simp
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_exp]
      exact Real.exp_pos _
    · show ‖exp (2 * π * I * z)‖ < 1
      rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
      have := Real.pi_pos
      nlinarith
  rcases hc'le.lt_or_eq with hlt | heq1
  · -- `|c′| < 1`: `Λ` stays in a compact subset of `ℍ`
    have hw₀ : cayleyInv c' ∈ upperHalf := cayleyInv_mem_upperHalf hlt
    set w₀ : ℂ := cayleyInv c' with hw₀def
    have hw₀im : 0 < w₀.im := hw₀
    have hcayInv : ContinuousAt cayleyInv c' := by
      unfold cayleyInv
      exact (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
        (continuousAt_const.sub continuousAt_id) (cayleyInv_den_ne_zero hlt)
    have hlim2 : Filter.Tendsto (fun z => liftToC Λ z) (Filter.comap Complex.im Filter.atTop) (𝓝 w₀) := by
      have h1 := hcayInv.tendsto.comp hlim
      refine h1.congr' ?_
      filter_upwards [hpos] with z hz
      exact cayleyInv_cayley (hfm z hz)
    set ε : ℝ := w₀.im / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hball : Metric.closedBall w₀ ε ⊆ upperHalf := by
      intro w hw
      show 0 < w.im
      have h1 : |(w - w₀).im| ≤ ‖w - w₀‖ := Complex.abs_im_le_norm (w - w₀)
      have h2 : ‖w - w₀‖ ≤ ε := by simpa [dist_eq_norm] using hw
      have h3 := abs_le.1 (h1.trans h2)
      simp only [Complex.sub_im] at h3
      linarith [h3.1]
    set K' : Set UpperHalfPlane := ((↑) : UpperHalfPlane → ℂ) ⁻¹' Metric.closedBall w₀ ε with hK'
    have hK'c : IsCompact K' := by
      exact (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff
        (fun w hw => ⟨⟨w, hball hw⟩, rfl⟩)).2 (isCompact_closedBall _ _)
    have hKc : IsCompact (p '' K') := hK'c.image hpc
    obtain ⟨r, hr0, hr⟩ := hleave _ hKc
    have hev1 : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, liftToC Λ z ∈ Metric.closedBall w₀ ε :=
      hlim2.eventually (Metric.closedBall_mem_nhds w₀ hε0)
    have hev2 : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, ‖exp (2 * π * I * z)‖ < r := by
      have : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, -Real.log r / (2 * π) < z.im :=
        Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop _)
      filter_upwards [this] with z hz
      rw [Complex.norm_exp]
      have hre : (2 * π * I * z).re = -(2 * π) * z.im := by simp
      rw [hre]
      calc Real.exp (-(2 * π) * z.im) < Real.exp (Real.log r) := by
            apply Real.exp_lt_exp.2
            have := Real.pi_pos
            rw [div_lt_iff₀ (by positivity)] at hz
            nlinarith
        _ = r := Real.exp_log hr0
    obtain ⟨z, hz1, hz2, hz3⟩ := (hev1.and (hev2.and hpos)).exists
    set τ : UpperHalfPlane := UpperHalfPlane.ofComplex z with hτ
    have hτz : (τ : ℂ) = z := by rw [hτ, UpperHalfPlane.ofComplex_apply_of_im_pos hz3]
    have hΛτ : Λ τ ∈ K' := by
      show ((Λ τ : UpperHalfPlane) : ℂ) ∈ Metric.closedBall w₀ ε
      rw [← h23l_liftToC_eq Λ hz3]
      exact hz1
    have hx : p (Λ τ) ∈ p '' K' := mem_image_of_mem _ hΛτ
    have hwU : exp (2 * π * I * (τ : ℂ)) ∈ φ '' U := by
      rw [himg, hτz]
      exact hmem1 z hz3
    have hxU : Function.invFunOn φ U (exp (2 * π * I * (τ : ℂ))) ∈ U := Function.invFunOn_mem hwU
    have hφx : φ (Function.invFunOn φ U (exp (2 * π * I * (τ : ℂ)))) = exp (2 * π * I * (τ : ℂ)) :=
      Function.invFunOn_eq hwU
    rw [hΛp τ] at hx
    exact hr _ hxU (by rw [hφx, hτz]; exact hz2) hx
  · -- `|c′| = 1`: maximum modulus for the cusp function
    exfalso
    set F := Function.Periodic.cuspFunction h f with hF
    have hF0 : DifferentiableAt ℂ F 0 :=
      Function.Periodic.differentiableAt_cuspFunction_zero hh hfper hfhol hfbd
    have hFne := Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hfper hfhol
    have hFev : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ F q := by
      rw [eventually_nhdsWithin_iff] at hFne
      filter_upwards [hFne] with q hq
      by_cases hq0 : q = 0
      · rw [hq0]
        exact hF0
      · exact hq hq0
    have hFlt : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → ‖F q‖ < 1 := by
      intro q hq0 hq1
      rw [hF, Function.Periodic.cuspFunction_eq_of_nonzero h f hq0]
      apply hfnorm
      rw [Function.Periodic.im_invQParam]
      have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.2 hq0) hq1
      have hpos' : 0 < h / (2 * π) := by positivity
      have e : -h / (2 * π) * Real.log ‖q‖ = (h / (2 * π)) * (-Real.log ‖q‖) := by ring
      rw [e]
      exact mul_pos hpos' (neg_pos.2 hlog)
    have hn1 : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q‖ < 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
      simpa using hq
    have hmax : IsLocalMax (fun q => ‖F q‖) 0 := by
      filter_upwards [hn1] with q hq
      show ‖F q‖ ≤ ‖F 0‖
      have h1 : ‖F 0‖ = 1 := heq1
      rw [h1]
      by_cases hq0 : q = 0
      · rw [hq0]
        exact h1.le
      · exact (hFlt q hq0 hq).le
    have hconst := Complex.eventually_eq_of_isLocalMax_norm hFev hmax
    obtain ⟨q, ⟨hqc, hq1⟩, hqne⟩ := (((hconst.filter_mono nhdsWithin_le_nhds).and
      (hn1.filter_mono nhdsWithin_le_nhds)).and (self_mem_nhdsWithin (s := ({0} : Set ℂ)ᶜ) (a := 0))).exists
    have := hFlt q hqne hq1
    rw [hqc] at this
    have h1 : ‖F 0‖ = 1 := heq1
    linarith

/-- Helper for `s30l_backward`: `exp(2πi τ)` lies in the punctured unit disc for `τ ∈ ℍ`. -/
theorem s30l_exp_mem (τ : UpperHalfPlane) : exp (2 * π * I * (τ : ℂ)) ∈ puncturedDisc := by
  have hre : (2 * π * I * (τ : ℂ)).re = -(2 * π) * (τ : ℂ).im := by simp
  refine ⟨?_, ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_pos _
  · show ‖exp (2 * π * I * (τ : ℂ))‖ < 1
    rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
    have := Real.pi_pos
    have := τ.coe_im_pos
    nlinarith

/-- Helper for `s30l_backward`: a conjugate of a parabolic element is parabolic, and conversely. -/
theorem s30l_parabolic_of_conj {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : IsParabolic (δ * γ * δ⁻¹)) :
    IsParabolic γ := by
  obtain ⟨htr, h1, h2⟩ := h
  refine ⟨?_, fun e => h1 ?_, fun e => h2 ?_⟩
  · have := s27g_trace_conj δ γ
    show |γ 0 0 + γ 1 1| = 2
    rw [← this]
    exact htr
  · rw [e]
    group
  · rw [e]
    simp

/-- Helper for `s30l_backward`: the three cases for the deck element `g` with `Λ(τ + n) = g Λ(τ)`. -/
theorem s30l_back_core {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (hfree : ActsFreely Γ) {U : Set S} {φ : S → ℂ} (hU : IsPunctureNbhd U φ) {Λ : UpperHalfPlane → UpperHalfPlane}
    (hΛd : DifferentiableOn ℂ (liftToC Λ) upperHalf)
    (hΛp : ∀ τ : UpperHalfPlane, p (Λ τ) = Function.invFunOn φ U (exp (2 * π * I * (τ : ℂ))))
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : g ∈ Γ) {n : ℤ} (hn : n ≠ 0)
    (hgn : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = τ + n → Λ τ' = g • Λ τ) : IsParabolic g := by
  by_cases hpm : g = 1 ∨ g = -1
  · exfalso
    have htriv : ∀ x : UpperHalfPlane, g • x = x := by
      rcases hpm with rfl | rfl
      · exact fun x => one_smul _ _
      · exact s27g_neg_one_smul
    exact s30l_cusp_false hp.1.continuous hU hΛd hΛp hn fun τ τ' h => by rw [hgn τ τ' h, htriv]
  · push Not at hpm
    rcases isParabolic_or_isHyperbolic_of_actsFreely hfree hg hpm.1 hpm.2 with hpar | hhyp
    · exact hpar
    · exact (s30l_hyp_false hΛd hhyp hgn).elim

/-- Helper for **Lemma 30.1** (§30.2), sufficiency: if `α` is freely homotopic to `β^n` (`n ≠ 0`) for a loop `β` around a
puncture `(U, φ)`, then a covering element `γ` of `α` is parabolic. The universal cover of `U` is `ℍ`, via
`τ ↦ φ⁻¹(exp(2πiτ))`; it lifts through `p` to a holomorphic `Λ : ℍ → ℍ` (`h23l_exists_continuous_lift`, holomorphic because
`p` is a local conformal homeomorphism) with `Λ(τ + 1) = κ Λ(τ)` for a `κ ∈ Γ` covering `β` (uniqueness of lifts), and
`γ` is conjugate to `κ^n` (`s30a_fh_fwd`). `κ` is not elliptic (`ActsFreely`). If `κ` were hyperbolic, Schwarz–Pick for
`Λ` (the computation in `generalized_schwarz`) bounds the displacement `d(Λτ, κ Λτ) ≤ 1/Im τ → 0`, but a hyperbolic
element has displacement `≥ translationLength κ > 0` (`translationLength_eq_inf_dist`). If `κ = ±1` then `Λ` factors
through `exp(2πiτ)`, giving a bounded injective holomorphic `h : {0 < |ζ| < 1} → ℍ` with `p ∘ h = φ⁻¹`; by Riemann
removability and the open mapping theorem `h(ζ) → w₀ ∈ ℍ` as `ζ → 0` (a limit on `ℝ̂` would give an open set in `h(Δ)`
containing points outside `ℍ`), so `φ⁻¹(ζ) = p(h ζ)` stays in a compact set, contradicting "leaves every compact set". -/
theorem s30l_backward {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α)
    {U : Set S} {φ : S → ℂ} {β : Loop S} {r : ℝ} {n : ℤ} (hU : IsPunctureNbhd U φ) (hr0 : 0 < r) (hr1 : r < 1)
    (hβU : range β.2 ⊆ U) (hβφ : ∀ t : unitInterval, φ (β.2 t) = (r : ℂ) * exp (2 * π * I * (t : ℝ))) (hn : n ≠ 0)
    (hfh : FreelyHomotopic α (loopPow β n)) : IsParabolic γ := by
  classical
  haveI : Nonempty S := ⟨p UpperHalfPlane.I⟩
  have hU' := hU
  obtain ⟨hUo, hinj, himg, hmd, hleave⟩ := hU
  set ψ : ℂ → S := Function.invFunOn φ U with hψ
  have hψφ : ∀ x ∈ U, ψ (φ x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  -- the covering `ℍ → U`
  obtain ⟨lam, hlam⟩ : ∃ lam : UpperHalfPlane → S, lam = fun τ : UpperHalfPlane => ψ (exp (2 * π * I * (τ : ℂ))) := ⟨_, rfl⟩
  have hlamd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) lam := by
    intro τ
    rw [hlam]
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (exp (2 * π * I * (τ : ℂ))) := s30l_psi_mdiff hU' (s30l_exp_mem τ)
    have hg : Differentiable ℂ (fun z : ℂ => exp (2 * π * I * z)) := by fun_prop
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => exp (2 * π * I * (τ : ℂ))) τ :=
      (hg.mdifferentiable.comp UpperHalfPlane.mdifferentiable_coe) τ
    exact h1.comp τ h2
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (lam UpperHalfPlane.I)
  obtain ⟨Λ, hΛc, hΛp, -⟩ := h23l_exists_continuous_lift hp.1 hlamd.continuous
    (τ₀ := UpperHalfPlane.I) (τ₁ := τ₁) hτ₁
  have hΛd : DifferentiableOn ℂ (liftToC Λ) upperHalf :=
    s30a_lift_differentiableOn (X := S) (Y := S) (p₁ := lam) (p₂ := p) (ι := id) hlamd hp.1 hp.2.1
      mdifferentiable_id hΛc hΛp
  have hΛp' : ∀ τ : UpperHalfPlane, p (Λ τ) = ψ (exp (2 * π * I * (τ : ℂ))) := fun τ => by rw [hΛp, hlam]
  -- the shifts
  obtain ⟨sh, hsh, hshc⟩ : ∃ sh : ℤ → UpperHalfPlane → UpperHalfPlane,
      (∀ n τ, ((sh n τ : UpperHalfPlane) : ℂ) = τ + n) ∧ ∀ n, Continuous (sh n) :=
    ⟨fun n τ => ⟨(τ : ℂ) + n, by simpa using τ.coe_im_pos⟩, fun _ _ => rfl,
      fun n => UpperHalfPlane.isEmbedding_coe.continuous_iff.2
        (UpperHalfPlane.isEmbedding_coe.continuous.add continuous_const)⟩
  have hlamsh : ∀ n τ, lam (sh n τ) = lam τ := by
    intro n τ
    rw [hlam]
    simp only
    rw [hsh, show 2 * π * I * ((τ : ℂ) + n) = 2 * π * I * (τ : ℂ) + n * (2 * π * I) by ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- the deck element `κ` of the translation
  obtain ⟨κ, hκ, hκI⟩ : ∃ κ ∈ Γ, κ • Λ UpperHalfPlane.I = Λ (sh 1 UpperHalfPlane.I) :=
    (hp.2.2.2 (Λ UpperHalfPlane.I) (Λ (sh 1 UpperHalfPlane.I))).1 (by rw [hΛp, hΛp, hlamsh])
  have hΛs : ∀ τ, Λ (sh 1 τ) = κ • Λ τ := by
    intro τ
    have := hp.1.eq_of_comp_eq (hΛc.comp (hshc 1)) ((continuous_const_smul κ).comp hΛc) (by
      funext x
      simp only [Function.comp_apply]
      rw [hΛp, hlamsh, s30a_p_smul hp hκ, hΛp]) UpperHalfPlane.I hκI.symm
    exact congrFun this τ
  have hΛn : ∀ (n : ℤ) τ, Λ (sh n τ) = κ ^ n • Λ τ := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      intro τ
      have : sh 0 τ = τ := UpperHalfPlane.ext (by rw [hsh]; simp)
      rw [this]
      simp
    | succ i ih =>
      intro τ
      have : sh (i + 1) τ = sh 1 (sh i τ) := UpperHalfPlane.ext (by rw [hsh, hsh, hsh]; push_cast; ring)
      rw [this, hΛs, ih, ← mul_smul, zpow_add_one]
      congr 1
      exact Commute.self_zpow κ i
    | pred i ih =>
      intro τ
      have h1 : Λ (sh (-(i : ℤ)) τ) = κ • Λ (sh (-(i : ℤ) - 1) τ) := by
        rw [show sh (-(i : ℤ)) τ = sh 1 (sh (-(i : ℤ) - 1) τ) from
          UpperHalfPlane.ext (by rw [hsh, hsh, hsh]; push_cast; ring), hΛs]
      have h2 : Λ (sh (-(i : ℤ) - 1) τ) = κ⁻¹ • Λ (sh (-(i : ℤ)) τ) := by rw [h1, inv_smul_smul]
      rw [h2, ih, ← mul_smul, zpow_sub_one]
      congr 1
      exact (Commute.self_zpow κ (-(i : ℤ))).inv_left
  have hκp : ∀ x, p (κ • x) = p x := fun x => s30a_p_smul hp hκ x
  -- the loop `β` lifted along `Λ(t + s i)`, `exp(-2π s) = r`
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ Real.exp (-(2 * π * s)) = r := by
    have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
    refine ⟨-Real.log r / (2 * π), div_pos (neg_pos.2 hlog) (by positivity), ?_⟩
    rw [show -(2 * π * (-Real.log r / (2 * π))) = Real.log r by field_simp, Real.exp_log hr0]
  obtain ⟨ee, hee⟩ : ∃ ee : C(unitInterval, UpperHalfPlane),
      ∀ t, ee t = Λ ⟨((t : ℝ) : ℂ) + s * I, by simp [hs0]⟩ :=
    ⟨⟨fun t => Λ ⟨((t : ℝ) : ℂ) + s * I, by simp [hs0]⟩,
      hΛc.comp (UpperHalfPlane.isEmbedding_coe.continuous_iff.2
        ((Complex.continuous_ofReal.comp continuous_subtype_val).add continuous_const))⟩, fun _ => rfl⟩
  have he1 : ee 1 = κ • ee 0 := by
    rw [hee, hee, ← hΛs]
    congr 1
    apply UpperHalfPlane.ext
    rw [hsh]
    simp
    ring
  have hpt : ∀ t : unitInterval, p (ee t) = β.2 t := by
    intro t
    rw [hee, hΛp']
    have h1 : β.2 t = ψ (φ (β.2 t)) := (hψφ _ (hβU ⟨t, rfl⟩)).symm
    rw [h1, hβφ t]
    congr 1
    simp only
    rw [show 2 * π * I * (((t : ℝ) : ℂ) + s * I) = ((-(2 * π * s) : ℝ) : ℂ) + 2 * π * I * (t : ℝ) by
      push_cast; linear_combination (2 * (π : ℂ) * s) * Complex.I_sq, Complex.exp_add, ← Complex.ofReal_exp, hs]
  have hL1 : β.1 = p (ee 0) := ((hpt 0).trans β.2.source).symm
  have hfun : ∃ d : C(unitInterval, UpperHalfPlane), (∀ t, p (d t) = (loopPow β n).2 t) ∧ d 0 = ee 0 ∧
      d 1 = κ ^ n • ee 0 := by
    let eP : Path (ee 0) (κ • ee 0) := ⟨ee, rfl, he1⟩
    rcases le_or_gt 0 n with h0 | hneg
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      obtain ⟨ê, hê⟩ := s30l_lift_pow hκp eP β hL1 (fun t => (hpt t).symm) k
      refine ⟨ê, fun t => ?_, ê.source, ?_⟩
      · simp only [loopPow, Int.natCast_nonneg, if_true, Int.toNat_natCast]
        exact hê t
      · rw [show ((ê : C(unitInterval, UpperHalfPlane)) 1) = ê 1 from rfl, ê.target, zpow_natCast]
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
      subst hk
      have hκp' : ∀ x, p (κ⁻¹ • x) = p x := fun x => by
        have := hκp (κ⁻¹ • x)
        rw [smul_inv_smul] at this
        exact this.symm
      let e' : Path (ee 0) (κ⁻¹ • ee 0) :=
        (eP.symm.map (continuous_const_smul κ⁻¹)).cast (inv_smul_smul κ (ee 0)).symm rfl
      let L' : Loop S := ⟨β.1, β.2.symm⟩
      obtain ⟨ê, hê⟩ := s30l_lift_pow hκp' e' L' hL1 (fun t => by
        show β.2 (unitInterval.symm t) = p (κ⁻¹ • eP (unitInterval.symm t))
        rw [hκp', ← hpt]
        rfl) k
      refine ⟨ê, fun t => ?_, ê.source, ?_⟩
      · have hk0 : ¬ (0 ≤ -(k : ℤ)) := by omega
        show p _ = (if 0 ≤ -(k : ℤ) then _ else _ : Loop S).2 t
        rw [if_neg hk0]
        simp only [neg_neg, Int.toNat_natCast]
        exact hê t
      · rw [show ((ê : C(unitInterval, UpperHalfPlane)) 1) = ê 1 from rfl, ê.target, zpow_neg, zpow_natCast,
          inv_pow]
  obtain ⟨d, hd, hd0, hd1⟩ := hfun
  obtain ⟨δ, hδ, hδe⟩ := s30a_fh_fwd hp hγ hcov hfh d hd
  have hgΓ : δ * γ * δ⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hδ hγ) (Γ.inv_mem hδ)
  have hκn : κ ^ n ∈ Γ := zpow_mem hκ n
  have hgκ : δ * γ * δ⁻¹ = κ ^ n ∨ δ * γ * δ⁻¹ = -κ ^ n := by
    have hfix : ((κ ^ n)⁻¹ * (δ * γ * δ⁻¹)) • ee 0 = ee 0 := by
      rw [mul_smul]
      rw [hd0, hd1] at hδe
      rw [← hδe]
      exact inv_smul_smul _ _
    rcases hfree _ (Γ.mul_mem (Γ.inv_mem hκn) hgΓ) (ee 0) hfix with h | h
    · left
      exact (inv_mul_eq_one.1 h).symm
    · right
      calc δ * γ * δ⁻¹ = κ ^ n * ((κ ^ n)⁻¹ * (δ * γ * δ⁻¹)) := by group
        _ = κ ^ n * (-1) := by rw [h]
        _ = -κ ^ n := mul_neg_one _
  have hgn : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = τ + n → Λ τ' = (δ * γ * δ⁻¹) • Λ τ := by
    intro τ τ' h
    have : τ' = sh n τ := UpperHalfPlane.ext (by rw [h, hsh])
    rw [this, hΛn]
    rcases hgκ with e | e
    · rw [e]
    · rw [e, s30l_neg_smul]
  exact s30l_parabolic_of_conj (s30l_back_core hp hfree hU' hΛd hΛp' hgΓ hn hgn)

/-- **Lemma 30.1**: let `S = ℍ/G` and let `γ ∈ G` cover `α ⊆ S`.  Then `γ` is parabolic iff `α` is
freely homotopic to a power of a simple closed curve around a puncture of `S` (a curve `|ζ| = r` in
a puncture neighbourhood).  In particular the covering group of a compact surface has no parabolic
elements.

**Correction (2026-09-26).**  The right-hand side allowed `n = 0` (a null-homotopic `α`, covered by `γ = 1`, which
is not parabolic) and only asked `φ '' range β = sphere 0 r`, which a loop going out and back along the circle
satisfies while being null-homotopic; the statement was **false** (unconditional Lean refutation on
`Δ* = ℍ/⟨z ↦ z + 1⟩`).  Now `β` traverses the circle `|ζ| = r` once and `n ≠ 0`. -/
theorem lemma30_1 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α) :
    IsParabolic γ ↔ ∃ (U : Set S) (φ : S → ℂ) (β : Loop S) (r : ℝ) (n : ℤ), IsPunctureNbhd U φ ∧
      0 < r ∧ r < 1 ∧ range β.2 ⊆ U ∧ (∀ t : unitInterval, φ (β.2 t) = (r : ℂ) * exp (2 * π * I * (t : ℝ))) ∧
      n ≠ 0 ∧ FreelyHomotopic α (loopPow β n) := by
  constructor
  · intro hpar
    obtain ⟨A, γ₁, m, hγ₁, h₁, hstab, hm, hγm⟩ := s30l_normalize hΓ hγ hpar
    exact s30l_forward hp hΓ hγ hcov hγ₁ h₁ hstab hm hγm
  · rintro ⟨U, φ, β, r, n, hU, hr0, hr1, hβU, hβφ, hn, hfh⟩
    exact s30l_backward hp hΓ hfree hγ hcov hU hr0 hr1 hβU hβφ hn hfh

/-- Every loop is covered by some element of `Γ` (path lifting). -/
theorem s30a_exists_covers {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (α : Loop S) : ∃ γ ∈ Γ, Covers p γ α := by
  obtain ⟨e, he⟩ := hp.2.2.1 α.1
  have h0 : α.2.toContinuousMap 0 = p e := by rw [he]; exact α.2.source
  set L := hp.1.liftPath α.2.toContinuousMap e h0
  have hL : ∀ t, p (L t) = α.2 t := fun t => congrFun (hp.1.liftPath_lifts α.2.toContinuousMap e h0) t
  obtain ⟨γ, hγ, hγe⟩ := (hp.2.2.2 (L 0) (L 1)).1 (by rw [hL, hL, α.2.source, α.2.target])
  refine ⟨γ, hγ, fun t => L (Set.projIcc 0 1 zero_le_one t),
    (L.continuous.comp continuous_projIcc).continuousOn, fun t _ => ?_, ?_⟩
  · rw [hL]
    rfl
  · show L (Set.projIcc 0 1 zero_le_one 1) = γ • L (Set.projIcc 0 1 zero_le_one 0)
    rw [Set.projIcc_right, Set.projIcc_left]
    exact hγe.symm

/-- **Conjugate covering elements ⇒ freely homotopic loops.** -/
theorem s30a_fh_of_conj {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    {γ₁ γ₂ κ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ₁ : γ₁ ∈ Γ) (hκ : κ ∈ Γ)
    (h : ∀ x : UpperHalfPlane, γ₂ • x = (κ * γ₁ * κ⁻¹) • x) {α₁ α₂ : Loop S} (hcov₁ : Covers p γ₁ α₁)
    (hcov₂ : Covers p γ₂ α₂) : FreelyHomotopic α₁ α₂ := by
  obtain ⟨c₂, hcc₂, hcp₂, hc₂1⟩ := hcov₂
  set e : C(unitInterval, UpperHalfPlane) := ⟨fun t => κ⁻¹ • c₂ t,
    (continuous_const_smul _).comp (hcc₂.comp_continuous continuous_subtype_val fun t => t.2)⟩
  refine s30a_fh_bwd hp hγ₁ hcov₁ e ?_ α₂ fun t => ?_
  · show κ⁻¹ • c₂ ((1 : unitInterval) : ℝ) = γ₁ • κ⁻¹ • c₂ ((0 : unitInterval) : ℝ)
    rw [Set.Icc.coe_one, Set.Icc.coe_zero, hc₂1, h, mul_smul, mul_smul, inv_smul_smul]
  · show α₂.2 t = p (κ⁻¹ • c₂ t)
    rw [s30a_p_smul hp (Γ.inv_mem hκ), hcp₂ t t.2, Path.extend_extends']

/-- **Theorem 30.1** (长度谱的离散性): let `S` be a compact Riemann surface of genus `> 1` and `{αₙ}` a
sequence of closed curves representing all free homotopy classes.  For every `M > 0` only finitely
many `n` satisfy `l[αₙ] ≤ M`. -/
theorem thm30_1_discrete {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (α : ℕ → Loop S)
    (hrep : ∀ β : Loop S, ∃ n, FreelyHomotopic β (α n)) (hinj : ∀ m n, FreelyHomotopic (α m) (α n) → m = n)
    (M : ℝ) : {n | freeHomotopyLength p (α n) ≤ ENNReal.ofReal M}.Finite := by
  have _ := hg
  have _ := hrep
  have : CompactSpace S := hS.1
  have hF : IsFuchsian Γ := utm_x2_isFuchsian hp
  have hfree : ActsFreely Γ := s27g_actsFreely hp
  have hC : IsCocompact Γ := utm_exists_compact_translate hp
  choose γs hγs hcovs using fun n => s30a_exists_covers hp (α n)
  obtain ⟨-, F, hFprop⟩ := lengthSpectrum_discrete hF hfree hC M
  -- the loops with a given covering class form a subsingleton
  set S₀ : Set ℕ := {n | γs n = 1 ∨ γs n = -1}
  set Sc : Matrix.SpecialLinearGroup (Fin 2) ℝ → Set ℕ := fun γ' => {n | ∃ δ ∈ Γ, γs n = δ * γ' * δ⁻¹}
  have hpm : ∀ n ∈ S₀, ∀ x : UpperHalfPlane, γs n • x = x := by
    rintro n (h | h) x
    · rw [h, one_smul]
    · rw [h, s27g_neg_one_smul]
  have hS₀ : S₀.Subsingleton := by
    intro n hn m hm
    refine hinj n m (s30a_fh_of_conj hp (hγs n) Γ.one_mem (fun x => ?_) (hcovs n) (hcovs m))
    rw [hpm m hm, inv_one, mul_one, one_mul, hpm n hn]
  have hSc : ∀ γ', (Sc γ').Subsingleton := by
    rintro γ' n ⟨δ, hδ, hn⟩ m ⟨δ', hδ', hm⟩
    refine hinj n m (s30a_fh_of_conj hp (hγs n) (Γ.mul_mem hδ' (Γ.inv_mem hδ)) (fun x => ?_) (hcovs n)
      (hcovs m))
    rw [hm, hn]
    congr 1
    group
  refine ((hS₀.finite.union (F.finite_toSet.biUnion fun γ' _ => (hSc γ').finite))).subset ?_
  intro n hn
  by_cases h01 : γs n = 1 ∨ γs n = -1
  · exact Or.inl h01
  push Not at h01
  have hh : IsHyperbolic (γs n) := s27f_hyp hp (hγs n) h01.1 h01.2
  have hlen := s30a_len_hyp hp (hγs n) hh (hcovs n)
  have hle : freeHomotopyLength p (α n) ≤ ENNReal.ofReal M := hn
  rw [hlen] at hle
  have htl : translationLength (γs n) ≤ M := by
    rcases ENNReal.ofReal_le_ofReal_iff'.1 hle with h | h
    · exact h
    · exact absurd h (not_le.2 (s30a_tl_pos hh))
  obtain ⟨δ, hδ, γ', hγ', heq⟩ := hFprop (γs n) (hγs n) hh htl
  exact Or.inr (Set.mem_biUnion hγ' ⟨δ, hδ, heq⟩)

/-! ## §30.4 The length spectrum determines the Riemann surface -/

/-- Equal translation lengths of hyperbolic elements give equal squared traces (`ℓ = 2 arsinh (√(tr² - 4)/2)` is
injective in `tr²`). -/
theorem s30a_sq_of_tl_eq {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hh : IsHyperbolic γ)
    (hh' : IsHyperbolic γ') (h : translationLength γ = translationLength γ') :
    slTrace γ ^ 2 = slTrace γ' ^ 2 := by
  have h2 : 2 < |slTrace γ| := hh
  have h2' : 2 < |slTrace γ'| := hh'
  have ht4 : 0 < slTrace γ ^ 2 - 4 := by nlinarith [abs_nonneg (slTrace γ), sq_abs (slTrace γ)]
  have ht4' : 0 < slTrace γ' ^ 2 - 4 := by nlinarith [abs_nonneg (slTrace γ'), sq_abs (slTrace γ')]
  rw [translationLength_eq_arsinh ht4.le, translationLength_eq_arsinh ht4'.le] at h
  have h1 : Real.arsinh (√(slTrace γ ^ 2 - 4) / 2) = Real.arsinh (√(slTrace γ' ^ 2 - 4) / 2) := by linarith
  have h3 := Real.arsinh_injective h1
  have h4 : √(slTrace γ ^ 2 - 4) = √(slTrace γ' ^ 2 - 4) := by linarith
  have := (Real.sqrt_inj ht4.le ht4'.le).1 h4
  linarith

/-- Every element of a freely acting group is `±1`, parabolic (length `0`, `tr² = 4`) or hyperbolic. -/
theorem s30a_classify {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (hfree : ActsFreely Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {α : Loop S}
    (hcov : Covers p γ α) :
    (freeHomotopyLength p α = 0 ∧ slTrace γ ^ 2 = 4) ∨
      (IsHyperbolic γ ∧ freeHomotopyLength p α = ENNReal.ofReal (translationLength γ)) := by
  by_cases h1 : γ = 1
  · refine Or.inl ⟨s30a_len_zero hp hγ (Or.inl h1) hcov, ?_⟩
    subst h1
    simp [slTrace]
    norm_num
  by_cases h2 : γ = -1
  · refine Or.inl ⟨s30a_len_zero hp hγ (Or.inr (Or.inl h2)) hcov, ?_⟩
    subst h2
    simp [slTrace]
    norm_num
  rcases isParabolic_or_isHyperbolic_of_actsFreely hfree hγ h1 h2 with hpar | hh
  · refine Or.inl ⟨s30a_len_zero hp hγ (Or.inr (Or.inr hpar)) hcov, ?_⟩
    rw [← sq_abs, hpar.1]
    norm_num
  · exact Or.inr ⟨hh, s30a_len_hyp hp hγ hh hcov⟩

/-- (30.2)–(30.4): equal lengths give equal squared traces: if `γ`, `γ'` cover curves of the same
length then `tr²(A) = tr²(A')` for their matrices `A`, `A'`. -/
theorem eq30_2_trace_of_length {S S' : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [ChartedSpace ℂ S'] [T2Space S']
    [ConnectedSpace S'] [IsManifold 𝓘(ℂ) ω S'] {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} {p' : UpperHalfPlane → S'} (hp : IsUniformization Γ p)
    (hp' : IsUniformization Γ' p') (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ)
    (hfree' : ActsFreely Γ') {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ')
    {α : Loop S} {α' : Loop S'} (hcov : Covers p γ α) (hcov' : Covers p' γ' α')
    (hlen : freeHomotopyLength p α = freeHomotopyLength p' α') : slTrace γ ^ 2 = slTrace γ' ^ 2 := by
  have _ := hΓ
  have _ := hΓ'
  rcases s30a_classify hp hfree hγ hcov with ⟨h0, h4⟩ | ⟨hh, hl⟩ <;>
    rcases s30a_classify hp' hfree' hγ' hcov' with ⟨h0', h4'⟩ | ⟨hh', hl'⟩
  · rw [h4, h4']
  · exfalso
    rw [h0, hl'] at hlen
    exact (ENNReal.ofReal_pos.2 (s30a_tl_pos hh')).ne hlen
  · exfalso
    rw [hl, h0'] at hlen
    exact (ENNReal.ofReal_pos.2 (s30a_tl_pos hh)).ne' hlen
  · rw [hl, hl'] at hlen
    exact s30a_sq_of_tl_eq hh hh'
      ((ENNReal.ofReal_eq_ofReal_iff (s30a_tl_pos hh).le (s30a_tl_pos hh').le).1 hlen)


/-! ### (30.1) the group form: finitely many traces determine the normalized representation (`s30e1_`)

A non-book helper block for `eq30_1_generators_determined`.  Write `A = ρ(a_g)`, `B = ρ(b_g)` (the last pair).  The
clauses on `ρ` say that `B = diag(s, 1/s)` with `s² > 1` and `A` fixes `1` as its attracting fixed point.
*Words.*  For each of the `2g` generators `x`: `x`, `x A`, `x A⁻¹`, `x B`, `x B⁻¹`, `x A B`, `x (A B)⁻¹`, `x A B⁻¹`,
`x (A B⁻¹)⁻¹`; and `A B`, `A B⁻¹`.  *Signs.*  `tr(XY) + tr(XY⁻¹) = tr X tr Y`, so the two absolute values
`|tr XY|`, `|tr XY⁻¹|` fix the sign of `tr XY` as soon as `tr X tr Y ≠ 0` (`s30e1_sign`).
`s30e1_gen_hyperbolic`, `s30e1_base_off_axes`: `ρ` of a generator is hyperbolic and `A` shares no fixed point with `B`
(a discrete cocompact group has no parabolics, `[A, B]` would be one).  `s30e1_base_determined`: `A, B` are determined up
to sign by `|tr A|, |tr B|, |tr AB|, |tr AB⁻¹|` (the attracting clause gives the eigenvalue `(t + sgn t √(t²-4))/2`
of `A` at `1`).  `s30e1_gen_determined`: for the base pair `(A, B)` with `A` off the axes `0, ∞`, `{1, A, B, AB}` is a
basis of `M₂(ℝ)`, so a further generator `C` is determined up to sign by `tr C, tr CA, tr CB, tr CAB`. -/

/-- Signs: `slTrace` of the negative. -/
theorem s30e1_slTrace_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : slTrace (-γ) = -slTrace γ := by
  simp [slTrace]
  ring

/-- Signs: a `±` change of the second factor does not change `|tr|` of a product. -/
theorem s30e1_abs_tr_pm {X Y Y₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : Y₂ = Y ∨ Y₂ = -Y) :
    |slTrace (X * Y₂)| = |slTrace (X * Y)| := by
  rcases h with rfl | rfl
  · rfl
  · rw [mul_neg, s30e1_slTrace_neg, abs_neg]

/-- `±`-equality is stable under products. -/
theorem s30e1_pm_mul {A A₂ B B₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A₂ = A ∨ A₂ = -A)
    (hB : B₂ = B ∨ B₂ = -B) : A₂ * B₂ = A * B ∨ A₂ * B₂ = -(A * B) := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp [neg_mul, mul_neg]

/-- `±`-equality is stable under inverses. -/
theorem s30e1_pm_inv {A A₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A₂ = A ∨ A₂ = -A) :
    A₂⁻¹ = A⁻¹ ∨ A₂⁻¹ = -A⁻¹ := by
  rcases hA with rfl | rfl
  · exact Or.inl rfl
  · right
    refine inv_eq_of_mul_eq_one_right ?_
    rw [neg_mul_neg, mul_inv_cancel]

/-- `tr(XY) + tr(XY⁻¹) = tr X · tr Y` in `SL(2, ℝ)` (Cayley–Hamilton). -/
theorem s30e1_trace_identity (X Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slTrace (X * Y) + slTrace (X * Y⁻¹) = slTrace X * slTrace Y := by
  have h1 := s30l_mul_entries X Y
  have h2 := s30l_mul_entries X Y⁻¹
  have h3 := s27t_inv_apply Y
  simp only [slTrace]
  rw [h1.1, h1.2.2.2, h2.1, h2.2.2.2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2]
  ring

/-- Signs: if `|p'| = |p|`, `|q'| = |q|`, `p' + q' = p + q ≠ 0` then `p' = p`. -/
theorem s30e1_sign {p q p' q' : ℝ} (hp : |p'| = |p|) (hq : |q'| = |q|) (hs : p' + q' = p + q)
    (h0 : p + q ≠ 0) : p' = p := by
  rcases abs_eq_abs.1 hp with h | h
  · exact h
  · have hq' : q' = 2 * p + q := by linarith
    rw [hq'] at hq
    rcases abs_eq_abs.1 hq with h' | h'
    · linarith
    · exact absurd (by linarith) h0

/-- Signs: a `±` change of the first factor does not change `|tr|` of a product. -/
theorem s30e1_abs_tr_pm_left {X X₂ Y : Matrix.SpecialLinearGroup (Fin 2) ℝ} (h : X₂ = X ∨ X₂ = -X) :
    |slTrace (X₂ * Y)| = |slTrace (X * Y)| := by
  rcases h with rfl | rfl
  · rfl
  · rw [neg_mul, s30e1_slTrace_neg, abs_neg]

/-- Entries of a product (as rewrite rules). -/
theorem s30e1_mul00 (g h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 := (s30l_mul_entries g h).1

theorem s30e1_mul01 (g h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 := (s30l_mul_entries g h).2.1

theorem s30e1_mul10 (g h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := (s30l_mul_entries g h).2.2.1

theorem s30e1_mul11 (g h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := (s30l_mul_entries g h).2.2.2

/-- The determinant of `SL(2, ℝ)` in entries. -/
theorem s30e1_det (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  exact h

/-- A standard generator of the surface group has infinite order (a complex additive character separates it). -/
theorem s30e1_gen_pow_ne {g : ℕ} (s : Fin g ⊕ Fin g) {n : ℕ} (hn : n ≠ 0) (x : surfaceGroup g)
    (hx : x = PresentedGroup.of s) : x ^ n ≠ 1 := by
  classical
  obtain ⟨χ, hχ⟩ := (k22rr_sg_character_eval_bijective g).2 (fun i => if i = s then (1 : ℂ) else 0)
  intro h
  have h2 : χ.toMultiplicativeRight x = Multiplicative.ofAdd (1 : ℂ) := by
    have h0 : χ (Additive.ofMul (PresentedGroup.of s : surfaceGroup g)) = 1 := by
      simpa using congrFun hχ s
    rw [hx]
    exact congrArg Multiplicative.ofAdd h0
  have h1 : χ.toMultiplicativeRight (x ^ n) = (χ.toMultiplicativeRight x) ^ n := map_pow _ _ _
  rw [h, map_one, h2] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  simp at h3
  exact hn (by exact_mod_cast h3.symm)

/-- A parabolic element has no fixed point in `ℍ`. -/
theorem s30e1_parabolic_fixed_false {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsParabolic γ)
    (τ : UpperHalfPlane) : γ • τ ≠ τ := by
  intro h
  have ht : slTrace γ ^ 2 - 4 = 0 := by rw [← sq_abs, hγ.1]; norm_num
  obtain ⟨hd, hn⟩ := dist_smul_eq_arsinh γ τ
  rw [h, dist_self] at hd
  have hy : 0 < τ.im := τ.im_pos
  have hQ0 : ‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - (γ 0 1 : ℂ)‖ = 0 := by
    have h1 : Real.arsinh (‖(γ 1 0 : ℂ) * (τ : ℂ) ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * τ - (γ 0 1 : ℂ)‖ /
        (2 * τ.im)) = 0 := by linarith
    rw [Real.arsinh_eq_zero_iff, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  have hQ := norm_eq_zero.1 hQ0
  rw [hQ0, ht, mul_zero, zero_add] at hn
  have hE : γ 1 0 * (τ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ : ℂ).re - γ 0 1 + γ 1 0 * τ.im ^ 2 = 0 := by
    nlinarith [sq_nonneg (γ 1 0 * (τ : ℂ).re ^ 2 + (γ 1 1 - γ 0 0) * (τ : ℂ).re - γ 0 1 + γ 1 0 * τ.im ^ 2)]
  have hre := congrArg Complex.re hQ
  have him := congrArg Complex.im hQ
  have hτim : (τ : ℂ).im = τ.im := rfl
  have hτre : (τ : ℂ).re = τ.re := rfl
  simp only [hτre] at hE
  simp [pow_two] at hre him
  have hc : γ 1 0 = 0 := by
    have h2 : γ 1 0 * τ.im ^ 2 = 0 := by nlinarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (by positivity)
  have hda : γ 1 1 = γ 0 0 := by
    rw [hc] at him
    have : (γ 1 1 - γ 0 0) * τ.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact absurd h3 hy.ne'
  have hb : γ 0 1 = 0 := by
    rw [hc, hda] at hre
    linarith
  have hdet := s30e1_det γ
  rw [hc, hb, hda] at hdet
  have ha : γ 0 0 = 1 ∨ γ 0 0 = -1 := by
    have : (γ 0 0 - 1) * (γ 0 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases ha with ha | ha
  · exact hγ.2.1 (s30l_eq_of_entries (by simpa using ha) (by simpa using hb) (by simpa using hc)
      (by simpa [hda] using ha))
  · exact hγ.2.2 (s30l_eq_of_entries (by simpa using ha) (by simpa using hb) (by simpa using hc)
      (by simpa [hda] using ha))

/-- A cocompact Fuchsian group has no parabolic elements (no `ActsFreely` needed: the finitely many parabolic
elements that move a point of the fundamental set by `< 1` have positive minimal displacement). -/
theorem s30e1_no_parabolic {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hc : IsCocompact Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hpar : IsParabolic γ) : False := by
  obtain ⟨C, hC, hcov⟩ := hc
  have hC' : IsCompact (cthickening 1 C) := hC.cthickening
  have hCne : C.Nonempty := by
    obtain ⟨σ, -, hσ⟩ := hcov UpperHalfPlane.I
    exact ⟨_, hσ⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      S = {g ∈ Γ | ((g • ·) '' cthickening 1 C ∩ cthickening 1 C).Nonempty} ∩ {g | IsParabolic g} :=
    ⟨_, rfl⟩
  have hS : S.Finite := by
    rw [hSdef]
    exact (hΓ _ hC').subset inter_subset_left
  have hpos : ∀ g ∈ S, ∃ δ > 0, ∀ ρ ∈ C, δ ≤ dist ρ (g • ρ) := by
    intro g hg
    rw [hSdef] at hg
    have hcont : Continuous fun ρ : UpperHalfPlane => dist ρ (g • ρ) :=
      continuous_id.dist (continuous_const_smul g)
    obtain ⟨ρ₀, hρ₀, hmin⟩ := hC.exists_isMinOn hCne hcont.continuousOn
    exact ⟨dist ρ₀ (g • ρ₀), dist_pos.2 fun h => s30e1_parabolic_fixed_false hg.2 ρ₀ h.symm,
      fun ρ hρ => isMinOn_iff.1 hmin ρ hρ⟩
  obtain ⟨δ, hδ, hδS⟩ := exists_pos_forall_of_finite hS
    (fun g δ δ' hle h ρ hρ => hle.trans (h ρ hρ)) hpos
  obtain ⟨τ, hτ⟩ := exists_dist_smul_lt_of_isParabolic hpar (lt_min hδ one_pos)
  obtain ⟨σ, hσ, hστ⟩ := hcov τ
  have hgρ : (σ * γ * σ⁻¹) • (σ • τ) = σ • (γ • τ) := by
    rw [mul_smul, mul_smul, inv_smul_smul]
  have hdist : dist (σ • τ) ((σ * γ * σ⁻¹) • (σ • τ)) = dist τ (γ • τ) := by
    rw [hgρ, dist_smul]
  have hγeq : γ = σ⁻¹ * (σ * γ * σ⁻¹) * σ := by group
  have hgS : σ * γ * σ⁻¹ ∈ S := by
    rw [hSdef]
    refine ⟨⟨Γ.mul_mem (Γ.mul_mem hσ hγ) (Γ.inv_mem hσ), (σ * γ * σ⁻¹) • (σ • τ),
      ⟨σ • τ, self_subset_cthickening C hστ, rfl⟩, ?_⟩, ⟨?_, fun h => hpar.2.1 ?_, fun h => hpar.2.2 ?_⟩⟩
    · refine mem_cthickening_of_dist_le _ (σ • τ) 1 C hστ ?_
      rw [dist_comm, hdist]
      exact (hτ.trans_le (min_le_right _ _)).le
    · rw [slTrace_conj]
      exact hpar.1
    · rw [hγeq, h, mul_one, inv_mul_cancel]
    · rw [hγeq, h]
      simp
  have hle := hδS _ hgS (σ • τ) hστ
  rw [hdist] at hle
  exact absurd (hτ.trans_le (min_le_left _ _)) (not_lt.2 hle)

/-- **[stub 1]** `ρ` of a generator is hyperbolic, for an injective `ρ` with discrete cocompact image (no `ActsFreely`
hypothesis: generators have infinite order, elliptic elements of a Fuchsian group have finite order, and a cocompact
Fuchsian group has no parabolic elements). -/
theorem s30e1_gen_hyperbolic {g : ℕ} (hg : 1 < g) (ρ : surfaceGroup g →* Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hinj : Function.Injective ρ) (hF : IsFuchsian ρ.range) (hC : IsCocompact ρ.range)
    (s : Fin g ⊕ Fin g) : 2 < |slTrace (ρ (PresentedGroup.of s))| := by
  classical
  have hmem : ρ (PresentedGroup.of s : surfaceGroup g) ∈ ρ.range := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : surfaceGroup g, x = PresentedGroup.of s := ⟨_, rfl⟩
  have hne1 : ∀ n : ℕ, n ≠ 0 → ρ (PresentedGroup.of s : surfaceGroup g) ^ n ≠ 1 := fun n hn h => by
    rw [← hx] at h
    exact s30e1_gen_pow_ne s hn x hx (hinj (by rw [map_pow, h, map_one]))
  -- no elliptic elements: a power of an elliptic element fixes a point, so only finitely many powers differ
  have hge : 2 ≤ |slTrace (ρ (PresentedGroup.of s : surfaceGroup g))| := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨τ, hτ⟩ := exists_smul_eq_self_of_abs_slTrace_lt_two hlt
    have hfin := hF {τ} isCompact_singleton
    have hfix : ∀ n : ℕ, (ρ (PresentedGroup.of s : surfaceGroup g) ^ n) • τ = τ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, hτ, ih]
    have hmemn : ∀ n : ℕ, ρ (PresentedGroup.of s : surfaceGroup g) ^ n ∈
        {δ ∈ ρ.range | ((fun z => δ • z) '' {τ} ∩ {τ}).Nonempty} := fun n =>
      ⟨pow_mem hmem n, τ, ⟨τ, rfl, hfix n⟩, rfl⟩
    obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem hmemn
    apply hne1 (n - m) (by omega)
    refine mul_left_cancel (a := ρ (PresentedGroup.of s : surfaceGroup g) ^ m) ?_
    rw [← pow_add, Nat.add_sub_cancel' hmn.le, mul_one]
    exact heq.symm
  rcases hge.eq_or_lt with h | h
  · exfalso
    by_cases h1 : ρ (PresentedGroup.of s : surfaceGroup g) = 1
    · exact hne1 1 one_ne_zero (by simpa using h1)
    by_cases h2 : ρ (PresentedGroup.of s : surfaceGroup g) = -1
    · exact hne1 2 two_ne_zero (by rw [h2]; simp)
    exact s30e1_no_parabolic hF hC hmem ⟨h.symm, h1, h2⟩
  · exact h

/-- The commutator of an upper triangular matrix with a diagonal one has trace `2`. -/
theorem s30e1_comm_tr_upper {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hB01 : B 0 1 = 0) (hB10 : B 1 0 = 0)
    (hc : A 1 0 = 0) : slTrace (A * B * A⁻¹ * B⁻¹) = 2 := by
  have hdA := s30e1_det A
  have hdB := s30e1_det B
  rw [hc] at hdA
  rw [hB01, hB10] at hdB
  have ha : A 0 0 ≠ 0 := by
    intro h
    rw [h] at hdA
    simp at hdA
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hdB
    simp at hdB
  have hd : A 1 1 = (A 0 0)⁻¹ := by field_simp; linarith
  have ht : B 1 1 = (B 0 0)⁻¹ := by field_simp; linarith
  have i1 := s27t_inv_apply A
  have i2 := s27t_inv_apply B
  simp only [slTrace, s30e1_mul00, s30e1_mul01, s30e1_mul10, s30e1_mul11, i1.1, i1.2.1, i1.2.2.1, i1.2.2.2,
    i2.1, i2.2.1, i2.2.2.1, i2.2.2.2, hB01, hB10, hc, hd, ht]
  field_simp
  ring

/-- The commutator of a lower triangular matrix with a diagonal one has trace `2`. -/
theorem s30e1_comm_tr_lower {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hB01 : B 0 1 = 0) (hB10 : B 1 0 = 0)
    (hb : A 0 1 = 0) : slTrace (A * B * A⁻¹ * B⁻¹) = 2 := by
  have hdA := s30e1_det A
  have hdB := s30e1_det B
  rw [hb] at hdA
  rw [hB01, hB10] at hdB
  have ha : A 0 0 ≠ 0 := by
    intro h
    rw [h] at hdA
    simp at hdA
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hdB
    simp at hdB
  have hd : A 1 1 = (A 0 0)⁻¹ := by field_simp; linarith
  have ht : B 1 1 = (B 0 0)⁻¹ := by field_simp; linarith
  have i1 := s27t_inv_apply A
  have i2 := s27t_inv_apply B
  simp only [slTrace, s30e1_mul00, s30e1_mul01, s30e1_mul10, s30e1_mul11, i1.1, i1.2.1, i1.2.2.1, i1.2.2.2,
    i2.1, i2.2.1, i2.2.2.1, i2.2.2.2, hB01, hB10, hb, hd, ht]
  field_simp
  ring

/-- In the surface group of genus `g > 1` the commutator `[a_g, b_g]` does not have order `≤ 2`: a homomorphism to `S₃`
sends `a₀ ↦ (01)`, `b₀ ↦ (12)`, `a_g ↦ (12)`, `b_g ↦ (01)` and the other generators to `1`, so the relation holds and
`[a_g, b_g]` becomes a `3`-cycle. -/
theorem s30e1_comm_sq_ne {g : ℕ} (hg : 1 < g) (a b c : surfaceGroup g)
    (ha : a = PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)) (hb : b = PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))
    (hc : c = a * b * a⁻¹ * b⁻¹) : c ^ 2 ≠ 1 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
  have hLg : (⟨n + 2 - 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext (by simp)
  simp only [hLg] at ha hb
  let x : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let y : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let f : (Fin (n + 2) ⊕ Fin (n + 2)) → Equiv.Perm (Fin 3) :=
    Sum.elim (fun i => if i = 0 then x else if i = Fin.last (n + 1) then y else 1)
      (fun i => if i = 0 then y else if i = Fin.last (n + 1) then x else 1)
  have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin (n + 2) =>
      FreeGroup.of (Sum.inl i : Fin (n + 2) ⊕ Fin (n + 2)) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
      Set (FreeGroup (Fin (n + 2) ⊕ Fin (n + 2)))), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    rw [map_list_prod, List.map_ofFn]
    obtain ⟨t, ht⟩ : ∃ t : Fin (n + 2) → Equiv.Perm (Fin 3), ∀ i, t i =
        f (Sum.inl i) * f (Sum.inr i) * (f (Sum.inl i))⁻¹ * (f (Sum.inr i))⁻¹ := ⟨_, fun _ => rfl⟩
    have hfun : (FreeGroup.lift f ∘ fun i : Fin (n + 2) =>
        FreeGroup.of (Sum.inl i : Fin (n + 2) ⊕ Fin (n + 2)) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹) = t := by
      funext i
      rw [ht]
      simp only [Function.comp, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hfun]
    have hmid : ∀ i : Fin n, t i.succ.castSucc = 1 := by
      intro i
      have h1 : i.succ.castSucc ≠ 0 := by
        rw [Ne, Fin.ext_iff]
        simp
      have h2 : i.succ.castSucc ≠ Fin.last (n + 1) := by
        rw [Ne, Fin.ext_iff]
        have := i.2
        simp
        omega
      rw [ht]
      simp [f, h1, h2]
    have ht0 : t 0 = x * y * x⁻¹ * y⁻¹ := by
      rw [ht]
      simp [f]
    have htl : t (Fin.last (n + 1)) = y * x * y⁻¹ * x⁻¹ := by
      rw [ht]
      have : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
        rw [Ne, Fin.ext_iff]
        simp
      simp [f, this]
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ', List.prod_concat]
    rw [List.prod_eq_one (l := List.ofFn fun i : Fin n => t i.castSucc.succ) ?_]
    · simp only [Fin.succ_last, ht0, htl, one_mul]
      decide
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      rw [Fin.succ_castSucc]
      exact hmid i
  intro h
  let σ : surfaceGroup (n + 2) →* Equiv.Perm (Fin 3) := PresentedGroup.toGroup hrel
  have hσ : ∀ i, σ (PresentedGroup.of i) = f i := fun i => PresentedGroup.toGroup.of hrel
  have h1 := congrArg σ h
  rw [map_pow, map_one, hc, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb, hσ, hσ] at h1
  have h3 : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
    rw [Ne, Fin.ext_iff]
    simp
  simp [f, h3] at h1
  exact absurd h1 (by decide)

/-- **[stub 2]** For such a `ρ` with `ρ(b_g)` diagonal, `ρ(a_g)` has no fixed point among `0, ∞`: otherwise `[A, B]` is
`±1` or parabolic, which injectivity and cocompactness (and a homomorphism to `S₃`) rule out. -/
theorem s30e1_base_off_axes {g : ℕ} (hg : 1 < g) (ρ : surfaceGroup g →* Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hinj : Function.Injective ρ) (hF : IsFuchsian ρ.range) (hC : IsCocompact ρ.range)
    (hB01 : (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))) 0 1 = 0)
    (hB10 : (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))) 1 0 = 0) :
    (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 0 1 ≠ 0 ∧
      (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 1 0 ≠ 0 := by
  classical
  have hcomm : ¬ (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)) 1 0 = 0 ∨
      ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)) 0 1 = 0) := by
    intro h
    have htr : slTrace (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)) *
        ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩)) *
        (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)))⁻¹ *
        (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩)))⁻¹) = 2 := by
      rcases h with h | h
      · exact s30e1_comm_tr_upper hB01 hB10 h
      · exact s30e1_comm_tr_lower hB01 hB10 h
    obtain ⟨a, ha⟩ : ∃ a : surfaceGroup g, a = PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : surfaceGroup g, b = PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : surfaceGroup g, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
    have hρc : slTrace (ρ c) = 2 := by
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]
      exact htr
    have hmem : ρ c ∈ ρ.range := ⟨c, rfl⟩
    by_cases h1 : ρ c = 1
    · apply s30e1_comm_sq_ne hg a b c ha hb hc
      apply hinj
      rw [map_pow, h1, map_one]
      simp
    by_cases h2 : ρ c = -1
    · apply s30e1_comm_sq_ne hg a b c ha hb hc
      apply hinj
      rw [map_pow, h2, map_one]
      simp
    exact s30e1_no_parabolic hF hC hmem ⟨by rw [hρc]; norm_num, h1, h2⟩
  exact ⟨fun h => hcomm (Or.inr h), fun h => hcomm (Or.inl h)⟩

/-- `|s + 1/s|` determines `|s|` for `|s| > 1`. -/
theorem s30e1_diag_pm {s s₂ : ℝ} (hs : 1 < s ^ 2) (hs₂ : 1 < s₂ ^ 2) (h : |s₂ + s₂⁻¹| = |s + s⁻¹|) :
    s₂ = s ∨ s₂ = -s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hs₂0 : s₂ ≠ 0 := by
    rintro rfl
    norm_num at hs₂
  have h2 : (s₂ + s₂⁻¹) ^ 2 = (s + s⁻¹) ^ 2 := by
    rw [← sq_abs (s₂ + s₂⁻¹), h, sq_abs]
  have h3 : (s₂ ^ 2 - s ^ 2) * (s ^ 2 * s₂ ^ 2 - 1) = 0 := by
    field_simp at h2
    nlinarith [h2]
  have h4 : s ^ 2 * s₂ ^ 2 - 1 ≠ 0 := by nlinarith
  have h5 : s₂ ^ 2 = s ^ 2 := by
    have := (mul_eq_zero.1 h3).resolve_right h4
    linarith
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h5

/-- The attracting clause `σ = 1` in entries: for `c ≠ 0` the attracting fixed point of a hyperbolic `A = (a b; c d)` is
`((a - d) + sgn(a + d) √((a+d)² - 4))/(2c)`. -/
theorem s30e1_att_eq {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : A 1 0 ≠ 0)
    (h : attractingFixedPoint A = ((1 : ℂ) : ExtPlane)) :
    (A 0 0 - A 1 1) + Real.sign (slTrace A) * Real.sqrt (slTrace A ^ 2 - 4) = 2 * A 1 0 := by
  unfold attractingFixedPoint at h
  rw [if_neg hc] at h
  have h1 := OnePoint.coe_injective h
  have h2 : (A 0 0 - A 1 1 + Real.sign (A 0 0 + A 1 1) * Real.sqrt ((A 0 0 + A 1 1) ^ 2 - 4)) /
      (2 * A 1 0) = 1 := by
    exact_mod_cast h1
  have h3 := (div_eq_one_iff_eq (mul_ne_zero two_ne_zero hc)).1 h2
  simpa [slTrace] using h3

/-- The base pair `(A, B)` is determined by `tr A`, `tr AB`, the attracting clause and the row-sum clause. -/
theorem s30e1_core3 {A A' B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2) (hA1 : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hA'1 : A' 0 0 + A' 0 1 = A' 1 0 + A' 1 1) {σ r : ℝ}
    (hE : (A 0 0 - A 1 1) + σ * r = 2 * A 1 0) (hE' : (A' 0 0 - A' 1 1) + σ * r = 2 * A' 1 0)
    (ht : slTrace A' = slTrace A) (hu : slTrace (A' * B) = slTrace (A * B)) : A' = A := by
  obtain ⟨hB01, hB10, hB00⟩ := hB
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hB00
    norm_num at hB00
  have hB11 : B 1 1 = (B 0 0)⁻¹ := by
    have := s30e1_det B
    rw [hB01, hB10] at this
    field_simp
    linarith
  simp only [slTrace, s30e1_mul00, s30e1_mul11, hB01, hB10, hB11] at ht hu
  have ha : A' 0 0 = A 0 0 := by
    have h1 : (A' 0 0 - A 0 0) * (B 0 0 - (B 0 0)⁻¹) = 0 := by
      have : A' 1 1 = A 0 0 + A 1 1 - A' 0 0 := by linarith
      rw [this] at hu
      linarith
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exfalso
      have h2 : B 0 0 ^ 2 = 1 := by
        have h3 : B 0 0 * (B 0 0 - (B 0 0)⁻¹) = 0 := by rw [h, mul_zero]
        rw [mul_sub, mul_inv_cancel₀ hs] at h3
        nlinarith
      linarith
  have hd : A' 1 1 = A 1 1 := by linarith
  have hc : A' 1 0 = A 1 0 := by linarith
  have hb : A' 0 1 = A 0 1 := by linarith
  exact s30l_eq_of_entries ha hb hc hd

/-- **[stub 3]** The base pair is determined up to sign.  `B = diag(s, 1/s)`, `s² > 1`; `A` fixes `1` with `1` its
attracting fixed point; `|tr A| > 2`, `A₁₀ ≠ 0` (so the attracting fixed point is given by the generic formula). -/
theorem s30e1_base_determined {A B A₂ B₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2) (hB₂ : B₂ 0 1 = 0 ∧ B₂ 1 0 = 0 ∧ 1 < B₂ 0 0 ^ 2)
    (hA1 : A 0 0 + A 0 1 = A 1 0 + A 1 1) (hA₂1 : A₂ 0 0 + A₂ 0 1 = A₂ 1 0 + A₂ 1 1)
    (hAatt : attractingFixedPoint A = ((1 : ℂ) : ExtPlane))
    (hA₂att : attractingFixedPoint A₂ = ((1 : ℂ) : ExtPlane))
    (hAh : 2 < |slTrace A|) (hA₂h : 2 < |slTrace A₂|) (hA01 : A 0 1 ≠ 0) (hA10 : A 1 0 ≠ 0)
    (hA₂10 : A₂ 1 0 ≠ 0)
    (h1 : |slTrace A₂| = |slTrace A|) (h2 : |slTrace B₂| = |slTrace B|)
    (h3 : |slTrace (A₂ * B₂)| = |slTrace (A * B)|) (h4 : |slTrace (A₂ * B₂⁻¹)| = |slTrace (A * B⁻¹)|) :
    (A₂ = A ∨ A₂ = -A) ∧ (B₂ = B ∨ B₂ = -B) := by
  obtain ⟨hB01, hB10, hB00⟩ := hB
  obtain ⟨hB₂01, hB₂10, hB₂00⟩ := hB₂
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hB00
    norm_num at hB00
  have hs₂ : B₂ 0 0 ≠ 0 := by
    intro h
    rw [h] at hB₂00
    norm_num at hB₂00
  have hB11 : B 1 1 = (B 0 0)⁻¹ := by
    have := s30e1_det B
    rw [hB01, hB10] at this
    field_simp
    linarith
  have hB₂11 : B₂ 1 1 = (B₂ 0 0)⁻¹ := by
    have := s30e1_det B₂
    rw [hB₂01, hB₂10] at this
    field_simp
    linarith
  have hτ : slTrace B ≠ 0 := by
    intro h
    simp only [slTrace, hB11] at h
    have h1 : B 0 0 * (B 0 0 + (B 0 0)⁻¹) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_inv_cancel₀ hs] at h1
    nlinarith
  have hA0 : slTrace A ≠ 0 := by
    intro h
    rw [h] at hAh
    norm_num at hAh
  -- `B₂ = ± B`
  have hBpm : B₂ = B ∨ B₂ = -B := by
    have hd := s30e1_diag_pm hB00 hB₂00 (by simpa [slTrace, hB11, hB₂11] using h2)
    rcases hd with h | h
    · left
      refine s30l_eq_of_entries h ?_ ?_ ?_
      · rw [hB₂01, hB01]
      · rw [hB₂10, hB10]
      · rw [hB₂11, hB11, h]
    · right
      refine s30l_eq_of_entries (by simpa using h) ?_ ?_ ?_
      · simp [hB₂01, hB01]
      · simp [hB₂10, hB10]
      · simp [hB₂11, hB11, h]
  -- the sign of `A₂`
  obtain ⟨A', hA'pm, hA'tr⟩ : ∃ A', (A' = A₂ ∨ A' = -A₂) ∧ slTrace A' = slTrace A := by
    rcases abs_eq_abs.1 h1 with h | h
    · exact ⟨A₂, Or.inl rfl, h⟩
    · exact ⟨-A₂, Or.inr rfl, by rw [s30e1_slTrace_neg, h, neg_neg]⟩
  have u1 : |slTrace (A' * B)| = |slTrace (A * B)| :=
    (s30e1_abs_tr_pm_left (Y := B) hA'pm).trans ((s30e1_abs_tr_pm (X := A₂) hBpm).symm.trans h3)
  have u2 : |slTrace (A' * B⁻¹)| = |slTrace (A * B⁻¹)| :=
    (s30e1_abs_tr_pm_left (Y := B⁻¹) hA'pm).trans
      ((s30e1_abs_tr_pm (X := A₂) (s30e1_pm_inv hBpm)).symm.trans h4)
  have p1 : slTrace (A' * B) = slTrace (A * B) :=
    s30e1_sign u1 u2 (by rw [s30e1_trace_identity, s30e1_trace_identity, hA'tr])
      (by rw [s30e1_trace_identity]; exact mul_ne_zero hA0 hτ)
  have hE := s30e1_att_eq hA10 hAatt
  have hE₂ := s30e1_att_eq hA₂10 hA₂att
  have hAA : A' = A := by
    rcases hA'pm with rfl | rfl
    · rw [hA'tr] at hE₂
      exact s30e1_core3 ⟨hB01, hB10, hB00⟩ hA1 hA₂1 hE hE₂ hA'tr p1
    · have htr₂ : slTrace A₂ = -slTrace A := by
        rw [s30e1_slTrace_neg] at hA'tr
        linarith
      rw [htr₂, Real.sign_neg, neg_sq] at hE₂
      refine s30e1_core3 ⟨hB01, hB10, hB00⟩ hA1 ?_ hE ?_ hA'tr p1
      · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
        linarith
      · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
        linarith
  refine ⟨?_, hBpm⟩
  rcases hA'pm with h | h
  · exact Or.inl (h.symm.trans hAA)
  · exact Or.inr (neg_eq_iff_eq_neg.1 (h.symm.trans hAA))

/-- Real core of the reconstruction: four trace conditions on `D = C' - C` kill `D`. -/
theorem s30e1_det_real {s a b c d x y z w : ℝ} (hs : s ≠ 0) (hs2 : s ^ 2 ≠ 1) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : x + w = 0) (h2 : x * s + w * s⁻¹ = 0) (h3 : x * a + y * c + z * b + w * d = 0)
    (h4 : x * (a * s) + y * (c * s) + z * (b * s⁻¹) + w * (d * s⁻¹) = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have hw : w = -x := by linarith
  have hx : x = 0 := by
    rw [hw] at h2
    have h5 : x * (s ^ 2 - 1) = 0 := by
      field_simp at h2
      nlinarith [h2]
    rcases mul_eq_zero.1 h5 with h | h
    · exact h
    · exact absurd (by linarith) hs2
  rw [hx] at hw
  rw [hx, hw] at h3 h4
  have h5 : y * c + z * b = 0 := by linarith
  have h6 : y * c * s + z * b * s⁻¹ = 0 := by linarith
  have hz : z * b = 0 := by
    have h7 : z * b * (s⁻¹ - s) = 0 := by
      have : y * c = -(z * b) := by linarith
      rw [this] at h6
      linarith
    rcases mul_eq_zero.1 h7 with h | h
    · exact h
    · exfalso
      apply hs2
      have : s⁻¹ = s := by linarith
      have h8 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
      rw [this] at h8
      nlinarith
  have hz' : z = 0 := (mul_eq_zero.1 hz).resolve_right hb
  have hy : y * c = 0 := by rw [hz'] at h5; linarith
  exact ⟨hx, (mul_eq_zero.1 hy).resolve_right hc, hz', by simpa using hw⟩

/-- Reconstruction: with `B = diag(s, 1/s)`, `s² > 1`, and `A` off the axes, `{1, A, B, AB}` separates points of
`SL(2, ℝ)` by traces. -/
theorem s30e1_det_mat {A B C C' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2) (hb : A 0 1 ≠ 0) (hc : A 1 0 ≠ 0)
    (h0 : slTrace C' = slTrace C) (h1 : slTrace (C' * A) = slTrace (C * A))
    (h2 : slTrace (C' * B) = slTrace (C * B)) (h3 : slTrace (C' * (A * B)) = slTrace (C * (A * B))) :
    C' = C := by
  obtain ⟨hB01, hB10, hB00⟩ := hB
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hB00
    norm_num at hB00
  have hB11 : B 1 1 = (B 0 0)⁻¹ := by
    have := s30e1_det B
    rw [hB01, hB10] at this
    field_simp
    linarith
  have hs2 : B 0 0 ^ 2 ≠ 1 := by linarith
  simp only [slTrace, s30e1_mul00, s30e1_mul01, s30e1_mul10, s30e1_mul11, hB01, hB10, hB11] at h0 h1 h2 h3
  obtain ⟨e1, e2, e3, e4⟩ := s30e1_det_real (s := B 0 0) (a := A 0 0) (b := A 0 1) (c := A 1 0) (d := A 1 1)
    (x := C' 0 0 - C 0 0) (y := C' 0 1 - C 0 1) (z := C' 1 0 - C 1 0) (w := C' 1 1 - C 1 1) hs hs2 hb hc
    (by linarith) (by linarith) (by linarith) (by linarith)
  exact s30l_eq_of_entries (by linarith) (by linarith) (by linarith) (by linarith)

/-- **[stub 4]** A further generator `C` is determined up to sign by the eight absolute traces. -/
theorem s30e1_gen_determined {A B C C₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2) (hA01 : A 0 1 ≠ 0) (hA10 : A 1 0 ≠ 0) (hAh : 2 < |slTrace A|)
    (hC : 2 < |slTrace C|) (h0 : |slTrace C₂| = |slTrace C|)
    (h1 : |slTrace (C₂ * A)| = |slTrace (C * A)|) (h1' : |slTrace (C₂ * A⁻¹)| = |slTrace (C * A⁻¹)|)
    (h2 : |slTrace (C₂ * B)| = |slTrace (C * B)|) (h2' : |slTrace (C₂ * B⁻¹)| = |slTrace (C * B⁻¹)|)
    (h3 : |slTrace (C₂ * (A * B))| = |slTrace (C * (A * B))|)
    (h3' : |slTrace (C₂ * (A * B)⁻¹)| = |slTrace (C * (A * B)⁻¹)|)
    (h4 : |slTrace (C₂ * (A * B⁻¹))| = |slTrace (C * (A * B⁻¹))|)
    (h4' : |slTrace (C₂ * (A * B⁻¹)⁻¹)| = |slTrace (C * (A * B⁻¹)⁻¹)|) :
    C₂ = C ∨ C₂ = -C := by
  obtain ⟨hB01, hB10, hB00⟩ := hB
  have hs : B 0 0 ≠ 0 := by
    intro h
    rw [h] at hB00
    norm_num at hB00
  have hB11 : B 1 1 = (B 0 0)⁻¹ := by
    have := s30e1_det B
    rw [hB01, hB10] at this
    field_simp
    linarith
  have hτ : slTrace B ≠ 0 := by
    intro h
    simp only [slTrace, hB11] at h
    have h1 : B 0 0 * (B 0 0 + (B 0 0)⁻¹) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_inv_cancel₀ hs] at h1
    nlinarith
  have hA0 : slTrace A ≠ 0 := by
    intro h
    rw [h] at hAh
    norm_num at hAh
  have hC0 : slTrace C ≠ 0 := by
    intro h
    rw [h] at hC
    norm_num at hC
  obtain ⟨C', hC'pm, hC'tr⟩ : ∃ C', (C' = C₂ ∨ C' = -C₂) ∧ slTrace C' = slTrace C := by
    rcases abs_eq_abs.1 h0 with h | h
    · exact ⟨C₂, Or.inl rfl, h⟩
    · exact ⟨-C₂, Or.inr rfl, by rw [s30e1_slTrace_neg, h, neg_neg]⟩
  have t1 := (s30e1_abs_tr_pm_left (Y := A) hC'pm).trans h1
  have t1' := (s30e1_abs_tr_pm_left (Y := A⁻¹) hC'pm).trans h1'
  have t2 := (s30e1_abs_tr_pm_left (Y := B) hC'pm).trans h2
  have t2' := (s30e1_abs_tr_pm_left (Y := B⁻¹) hC'pm).trans h2'
  have t3 := (s30e1_abs_tr_pm_left (Y := A * B) hC'pm).trans h3
  have t3' := (s30e1_abs_tr_pm_left (Y := (A * B)⁻¹) hC'pm).trans h3'
  have t4 := (s30e1_abs_tr_pm_left (Y := A * B⁻¹) hC'pm).trans h4
  have t4' := (s30e1_abs_tr_pm_left (Y := (A * B⁻¹)⁻¹) hC'pm).trans h4'
  have p1 : slTrace (C' * A) = slTrace (C * A) :=
    s30e1_sign t1 t1' (by rw [s30e1_trace_identity, s30e1_trace_identity, hC'tr])
      (by rw [s30e1_trace_identity]; exact mul_ne_zero hC0 hA0)
  have p2 : slTrace (C' * B) = slTrace (C * B) :=
    s30e1_sign t2 t2' (by rw [s30e1_trace_identity, s30e1_trace_identity, hC'tr])
      (by rw [s30e1_trace_identity]; exact mul_ne_zero hC0 hτ)
  have p3 : slTrace (C' * (A * B)) = slTrace (C * (A * B)) := by
    by_cases hAB : slTrace (A * B) = 0
    · have hAB' : slTrace (A * B⁻¹) ≠ 0 := by
        intro h
        have := s30e1_trace_identity A B
        rw [hAB, h, zero_add] at this
        exact mul_ne_zero hA0 hτ this.symm
      have q4 : slTrace (C' * (A * B⁻¹)) = slTrace (C * (A * B⁻¹)) :=
        s30e1_sign t4 t4' (by rw [s30e1_trace_identity, s30e1_trace_identity, hC'tr])
          (by rw [s30e1_trace_identity]; exact mul_ne_zero hC0 hAB')
      have i1 := s30e1_trace_identity (C' * A) B
      have i2 := s30e1_trace_identity (C * A) B
      simp only [mul_assoc] at i1 i2
      rw [p1] at i1
      linarith
    · exact s30e1_sign t3 t3' (by rw [s30e1_trace_identity, s30e1_trace_identity, hC'tr])
        (by rw [s30e1_trace_identity]; exact mul_ne_zero hC0 hAB)
  have hCC : C' = C := s30e1_det_mat ⟨hB01, hB10, hB00⟩ hA01 hA10 hC'tr p1 p2 p3
  rcases hC'pm with h | h
  · exact Or.inl (h.symm.trans hCC)
  · exact Or.inr (neg_eq_iff_eq_neg.1 (h.symm.trans hCC))

/-- (30.1) (the group form of Theorem 30.2): there are finitely many words `w₁, …, w_N` in the
standard generators of the surface group of genus `g` such that two faithful discrete cocompact
representations `ρ₁, ρ₂` with `|tr ρ₁(wᵢ)| = |tr ρ₂(wᵢ)|` (`i ≤ N`) and normalized standard
generators have `ρ₁ = ρ₂` on the generators (up to sign), hence `G₁ = G₂`.

**Correction (2026-09-26).**  The previous conclusion (`SL(2, ℝ)`-conjugacy up to sign) was **false**: the mirror
representation `J ρ J` (`J = diag(1, -1)`) has the same traces but is not `SL(2, ℝ)`-conjugate to `ρ`.  The
statement now carries the book's (27.5) normalization of the last pair (`δ_g(z) = λz`, `λ > 1`; `γ_g(1) = 1`)
and the orientation clause that `1` is the **attracting** fixed point of `γ_g` (equivalently `a_g · b_g = +1`
in the orientation of `ℍ`): the normalization alone does not exclude the re-normalized mirror. -/
theorem eq30_1_generators_determined {g : ℕ} (hg : 1 < g) :
    ∃ (N : ℕ) (w : Fin N → surfaceGroup g), ∀ ρ₁ ρ₂ : surfaceGroup g →* Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Function.Injective ρ₁ → Function.Injective ρ₂ →
      IsFuchsian ρ₁.range → IsFuchsian ρ₂.range → IsCocompact ρ₁.range → IsCocompact ρ₂.range →
      (∀ ρ : surfaceGroup g →* Matrix.SpecialLinearGroup (Fin 2) ℝ, (ρ = ρ₁ ∨ ρ = ρ₂) →
        (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))) 0 1 = 0 ∧
        (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))) 1 0 = 0 ∧
        1 < (ρ (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩))) 0 0 ^ 2 ∧
        (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 0 0 +
            (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 0 1 =
          (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 1 0 +
            (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) 1 1 ∧
        attractingFixedPoint (ρ (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩))) = ((1 : ℂ) : ExtPlane)) →
      (∀ i, |slTrace (ρ₁ (w i))| = |slTrace (ρ₂ (w i))|) →
      ∀ x : surfaceGroup g, ρ₂ x = ρ₁ x ∨ ρ₂ x = -ρ₁ x := by
  classical
  let aL : surfaceGroup g := PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩)
  let bL : surfaceGroup g := PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩)
  let gen : Fin g ⊕ Fin g → surfaceGroup g := fun s => PresentedGroup.of s
  -- the words: nine for each generator `x`, and `a_g b_g`, `a_g b_g⁻¹`
  let word : (((Fin g ⊕ Fin g) × Fin 9) ⊕ Fin 2) → surfaceGroup g := fun j =>
    Sum.elim (fun p => ![gen p.1, gen p.1 * aL, gen p.1 * aL⁻¹, gen p.1 * bL, gen p.1 * bL⁻¹,
      gen p.1 * (aL * bL), gen p.1 * (aL * bL)⁻¹, gen p.1 * (aL * bL⁻¹), gen p.1 * (aL * bL⁻¹)⁻¹] p.2)
      (fun k => ![aL * bL, aL * bL⁻¹] k) j
  refine ⟨Fintype.card (((Fin g ⊕ Fin g) × Fin 9) ⊕ Fin 2), fun i => word ((Fintype.equivFin _).symm i), ?_⟩
  intro ρ₁ ρ₂ hi₁ hi₂ hF₁ hF₂ hC₁ hC₂ hnorm htr
  have hw : ∀ j, |slTrace (ρ₁ (word j))| = |slTrace (ρ₂ (word j))| := fun j => by
    simpa using htr (Fintype.equivFin _ j)
  obtain ⟨hB01₁, hB10₁, hB00₁, hA₁, hAatt₁⟩ := hnorm ρ₁ (Or.inl rfl)
  obtain ⟨hB01₂, hB10₂, hB00₂, hA₂, hAatt₂⟩ := hnorm ρ₂ (Or.inr rfl)
  have hAh₁ : 2 < |slTrace (ρ₁ aL)| := s30e1_gen_hyperbolic hg ρ₁ hi₁ hF₁ hC₁ (Sum.inl ⟨g - 1, by omega⟩)
  have hAh₂ : 2 < |slTrace (ρ₂ aL)| := s30e1_gen_hyperbolic hg ρ₂ hi₂ hF₂ hC₂ (Sum.inl ⟨g - 1, by omega⟩)
  have hoff₁ := s30e1_base_off_axes hg ρ₁ hi₁ hF₁ hC₁ hB01₁ hB10₁
  have hoff₂ := s30e1_base_off_axes hg ρ₂ hi₂ hF₂ hC₂ hB01₂ hB10₂
  have hwgen : ∀ s, |slTrace (ρ₁ (gen s))| = |slTrace (ρ₂ (gen s))| := fun s => by
    simpa [word] using hw (Sum.inl (s, 0))
  have hbase := s30e1_base_determined (A := ρ₁ aL) (B := ρ₁ bL) (A₂ := ρ₂ aL) (B₂ := ρ₂ bL)
    ⟨hB01₁, hB10₁, hB00₁⟩ ⟨hB01₂, hB10₂, hB00₂⟩ hA₁ hA₂ hAatt₁ hAatt₂ hAh₁ hAh₂ hoff₁.1 hoff₁.2 hoff₂.2
    (hwgen (Sum.inl ⟨g - 1, by omega⟩)).symm (hwgen (Sum.inr ⟨g - 1, by omega⟩)).symm
    (by simpa [word, map_mul] using (hw (Sum.inr 0)).symm)
    (by simpa [word, map_mul, map_inv] using (hw (Sum.inr 1)).symm)
  obtain ⟨hPA, hPB⟩ := hbase
  have hPAi := s30e1_pm_inv hPA
  have hPBi := s30e1_pm_inv hPB
  have hPAB := s30e1_pm_mul hPA hPB
  have hPABi := s30e1_pm_inv hPAB
  have hPAB' := s30e1_pm_mul hPA hPBi
  have hPAB'i := s30e1_pm_inv hPAB'
  have hgen : ∀ s, ρ₂ (gen s) = ρ₁ (gen s) ∨ ρ₂ (gen s) = -ρ₁ (gen s) := by
    intro s
    have key : ∀ (k : Fin 9) (Y₁ Y₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ),
        ρ₁ (word (Sum.inl (s, k))) = ρ₁ (gen s) * Y₁ → ρ₂ (word (Sum.inl (s, k))) = ρ₂ (gen s) * Y₂ →
        (Y₂ = Y₁ ∨ Y₂ = -Y₁) → |slTrace (ρ₂ (gen s) * Y₁)| = |slTrace (ρ₁ (gen s) * Y₁)| := by
      intro k Y₁ Y₂ e₁ e₂ hY
      rw [← s30e1_abs_tr_pm (X := ρ₂ (gen s)) hY, ← e₂, ← e₁]
      exact (hw _).symm
    exact s30e1_gen_determined (A := ρ₁ aL) (B := ρ₁ bL) (C := ρ₁ (gen s)) (C₂ := ρ₂ (gen s))
      ⟨hB01₁, hB10₁, hB00₁⟩ hoff₁.1 hoff₁.2 hAh₁
      (s30e1_gen_hyperbolic hg ρ₁ hi₁ hF₁ hC₁ s) (hwgen s).symm
      (key 1 _ _ (by simp [word, map_mul]) (by simp [word, map_mul]) hPA)
      (key 2 _ _ (by simp [word, map_mul, map_inv]) (by simp [word, map_mul, map_inv]) hPAi)
      (key 3 _ _ (by simp [word, map_mul]) (by simp [word, map_mul]) hPB)
      (key 4 _ _ (by simp [word, map_mul, map_inv]) (by simp [word, map_mul, map_inv]) hPBi)
      (key 5 _ _ (by simp [word, map_mul]) (by simp [word, map_mul]) hPAB)
      (key 6 _ _ (by simp [word, map_mul, map_inv]) (by simp [word, map_mul, map_inv]) hPABi)
      (key 7 _ _ (by simp [word, map_mul, map_inv]) (by simp [word, map_mul, map_inv]) hPAB')
      (key 8 _ _ (by simp [word, map_mul, map_inv]) (by simp [word, map_mul, map_inv]) hPAB'i)
  -- the generators generate: `ρ₂ x = ± ρ₁ x` is closed under products and inverses
  intro x
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : (Fin g ⊕ Fin g) → surfaceGroup g)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  refine Subgroup.closure_induction (p := fun x _ => ρ₂ x = ρ₁ x ∨ ρ₂ x = -ρ₁ x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, rfl⟩
    exact hgen s
  · simp
  · intro x y _ _ hx hy
    rw [map_mul, map_mul]
    exact s30e1_pm_mul hx hy
  · intro x _ hx
    rw [map_inv, map_inv]
    exact s30e1_pm_inv hx

/-! ## §30.5 Discontinuity of the action of the modular group -/

/-- (30.7): `ℍ/⟨z ↦ λ²z⟩` is the annulus `{exp(-2π²/ln λ²) < |w| < 1}` via
`w = exp(2πi ln z/ln λ²)`, of modulus `2π²/ln λ²`; (30.6) the moduli of the annuli
`ℍ/⟨γ⟩`, `ℍ/⟨γ'⟩` are quasi-invariant under the lifted map, which gives (30.9)
`1/K[F] ≤ ln λ²/ln λ'² ≤ K[F]`. -/
theorem eq30_7_annulus_modulus {lam : ℝ} (hlam : 1 < lam) :
    (∀ z ∈ upperHalf, ∀ w ∈ upperHalf, (∃ n : ℤ, w = (lam ^ 2) ^ n * z) ↔
      exp (2 * π * I * log z / Real.log (lam ^ 2)) = exp (2 * π * I * log w / Real.log (lam ^ 2))) ∧
    (fun z => exp (2 * π * I * log z / Real.log (lam ^ 2))) '' upperHalf =
      annulus (Real.exp (-(2 * π ^ 2) / Real.log (lam ^ 2))) 1 ∧
    dcModulus (annulus (Real.exp (-(2 * π ^ 2) / Real.log (lam ^ 2))) 1) =
      ENNReal.ofReal (2 * π ^ 2 / Real.log (lam ^ 2)) := by
  -- `L = ln λ² > 0`
  set L : ℝ := Real.log (lam ^ 2) with hLdef
  have hlam0 : 0 < lam := by linarith
  have hlam2 : 1 < lam ^ 2 := by nlinarith
  have hL : 0 < L := Real.log_pos hlam2
  have hL0 : L ≠ 0 := hL.ne'
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast hπ0
  -- the exponent in real coordinates
  have hexp : ∀ x y : ℝ, 2 * π * I * (↑x + ↑y * I) / (L : ℂ) =
      ↑(-(2 * π * y / L)) + ↑(2 * π * x / L) * I := by
    intro x y
    apply Complex.ext
    · simp [div_ofReal_re, div_ofReal_im]
      ring
    · simp [div_ofReal_re, div_ofReal_im]
  have hlog : ∀ z : ℂ, log z = ↑(Real.log ‖z‖) + ↑(arg z) * I := fun z => by
    apply Complex.ext
    · simp [log_re]
    · simp [log_im]
  -- the argument of a point of the upper half-plane lies in `(0, π)`
  have harg : ∀ z ∈ upperHalf, 0 < arg z ∧ arg z < π := by
    intro z hz
    have hz' : 0 < z.im := hz
    refine ⟨?_, arg_lt_pi_iff.2 (Or.inr hz'.ne')⟩
    rcases (arg_nonneg_iff.2 hz'.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (arg_eq_zero_iff.1 h.symm).2
      linarith
  have hne : ∀ z ∈ upperHalf, z ≠ 0 := fun z hz h => by
    have hz' : 0 < z.im := hz
    rw [h, zero_im] at hz'
    exact lt_irrefl _ hz'
  -- the modulus of the image
  have hnorm : ∀ z ∈ upperHalf,
      ‖exp (2 * π * I * log z / (L : ℂ))‖ = Real.exp (-(2 * π * arg z / L)) := by
    intro z hz
    rw [hlog z, hexp, Complex.norm_exp]
    congr 1
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- (a): the fibres of the map are the orbits of `z ↦ λ² z`
    intro z hz w hw
    have hc : ∀ n : ℤ, ((lam : ℂ) ^ 2) ^ n = (((lam ^ 2) ^ n : ℝ) : ℂ) := fun n => by
      push_cast
      ring
    have hcpos : ∀ n : ℤ, 0 < (lam ^ 2) ^ n := fun n => zpow_pos (by positivity) n
    have hexpn : ∀ n : ℤ, exp ((n : ℂ) * (L : ℂ)) = (((lam ^ 2) ^ n : ℝ) : ℂ) := fun n => by
      rw [show ((n : ℂ) * (L : ℂ)) = (((n : ℝ) * L : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
      congr 1
      rw [mul_comm, hLdef, ← Real.rpow_def_of_pos (by positivity), Real.rpow_intCast]
    constructor
    · rintro ⟨n, rfl⟩
      rw [hc, log_ofReal_mul (hcpos n) (hne z hz), Real.log_zpow]
      apply exp_eq_exp_iff_exists_int.2 ⟨-n, ?_⟩
      push_cast
      field_simp
      ring
    · intro h
      obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
      have h1 : 2 * π * I * ((log z - log w) / (L : ℂ)) = 2 * π * I * n := by
        have : 2 * π * I * ((log z - log w) / (L : ℂ)) =
            2 * π * I * log z / (L : ℂ) - 2 * π * I * log w / (L : ℂ) := by ring
        rw [this, hn]
        ring
      have h2 : (log z - log w) / (L : ℂ) = n := mul_left_cancel₀ h2πI h1
      have key : log z = log w + (n : ℂ) * (L : ℂ) := by
        rw [div_eq_iff hL'] at h2
        linear_combination h2
      have hz_eq : z = (((lam ^ 2) ^ n : ℝ) : ℂ) * w := by
        have e1 : z = exp (log z) := (exp_log (hne z hz)).symm
        rw [e1, key, exp_add, exp_log (hne w hw), mul_comm, hexpn]
      refine ⟨-n, ?_⟩
      have hn0 : ((lam : ℂ) ^ 2) ^ n ≠ 0 := zpow_ne_zero n (pow_ne_zero 2 (by exact_mod_cast hlam0.ne'))
      rw [zpow_neg, hz_eq, ← hc, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  · -- (b): the image is the annulus
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := harg z hz
      show Real.exp (-(2 * π ^ 2) / L) < ‖exp (2 * π * I * log z / (L : ℂ))‖ ∧
        ‖exp (2 * π * I * log z / (L : ℂ))‖ < 1
      rw [hnorm z hz]
      constructor
      · apply Real.exp_lt_exp.2
        rw [neg_div, neg_lt_neg_iff, div_lt_div_iff_of_pos_right hL]
        nlinarith [Real.pi_pos]
      · rw [← Real.exp_zero]
        apply Real.exp_lt_exp.2
        have : 0 < 2 * π * arg z / L := by positivity
        linarith
    · rintro ⟨hp1, hp2⟩
      have hp0 : p ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hp1
        exact absurd hp1 (not_lt.2 (Real.exp_pos _).le)
      have hlogp1 : -(2 * π ^ 2) / L < Real.log ‖p‖ := by
        rw [← Real.log_exp (-(2 * π ^ 2) / L)]
        exact Real.log_lt_log (Real.exp_pos _) hp1
      have hlogp2 : Real.log ‖p‖ < 0 := Real.log_neg (norm_pos_iff.2 hp0) hp2
      have hlogp1' : -(2 * π ^ 2) < L * Real.log ‖p‖ := by
        have := (div_lt_iff₀ hL).1 hlogp1
        linarith
      set y : ℝ := -(L * Real.log ‖p‖) / (2 * π) with hy
      set x : ℝ := L * arg p / (2 * π) with hx
      have hy0 : 0 < y := by
        rw [hy]
        apply div_pos _ (by positivity)
        nlinarith
      have hyπ : y < π := by
        rw [hy, div_lt_iff₀ (by positivity)]
        nlinarith
      have him : (↑x + ↑y * I : ℂ).im = y := by simp
      refine ⟨exp (↑x + ↑y * I), ?_, ?_⟩
      · show 0 < (exp (↑x + ↑y * I)).im
        rw [exp_im, him]
        have hre : (↑x + ↑y * I : ℂ).re = x := by simp
        rw [hre]
        exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ)
      · show exp (2 * π * I * log (exp (↑x + ↑y * I)) / (L : ℂ)) = p
        have e1 : -(2 * π * y / L) = Real.log ‖p‖ := by
          rw [hy]
          field_simp
        have e2 : 2 * π * x / L = arg p := by
          rw [hx]
          field_simp
        rw [log_exp (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; exact hyπ.le), hexp, e1, e2,
          ← hlog p, exp_log hp0]
  · -- (c): the modulus of the annulus
    have h1 : 0 < Real.exp (-(2 * π ^ 2) / L) := Real.exp_pos _
    have h2 : Real.exp (-(2 * π ^ 2) / L) < 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_lt_exp.2
      rw [neg_div]
      have : 0 < 2 * π ^ 2 / L := by positivity
      linarith
    rw [dcModulus_annulus h1 h2, one_div, Real.log_inv, Real.log_exp, neg_div, neg_neg]

/-- Helper for **Lemma 30.3** (§30.5): the normal form `z ↦ λ² z` of a hyperbolic element (the book's "不失一般性,
我们可以假定它们具有下列形式"). For hyperbolic `γ ∈ SL(2, ℝ)` some `A ∈ SL(2, ℝ)` conjugates `γ` to the dilation of `ℍ` by
`λ² > 1`, with `ln λ² = translationLength γ` (send the repelling and attracting fixed points on `ℝ̂` to `0` and `∞`, and
the orientation by `z ↦ -1/z` if necessary). -/
theorem s30w_conj_dilation {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ), 1 < lam ∧ Real.log (lam ^ 2) = translationLength γ ∧
      ∀ τ : UpperHalfPlane, (((A * γ * A⁻¹) • τ : UpperHalfPlane) : ℂ) = ((lam ^ 2 : ℝ) : ℂ) * (τ : ℂ) := by
  have ht : 2 < |γ 0 0 + γ 1 1| := hγ
  obtain ⟨hmul, hne, hcr, hinfτ, hinfσ, -⟩ := hyperbolic_normal_form ht
  obtain ⟨-, -, -, hspos, -⟩ := hnf_sign_sqrt ht
  set lam : ℝ := (|γ 0 0 + γ 1 1| + Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4)) / 2 with hlam
  have hmuleq : multiplier γ = lam ^ 2 := rfl
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : 1 < lam := by
    by_contra h
    push_neg at h
    have : lam ^ 2 ≤ 1 := by nlinarith
    rw [← hmuleq] at this
    linarith
  have hlam2 : (lam ^ 2 : ℝ) ≠ 0 := by positivity
  have hdet := hnf_sl2_det γ
  -- the Möbius normal form: some `A` with `A (γ z) = λ A z` on `ℍ`
  have key : ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z : UpperHalfPlane,
      ((A • (γ • z) : UpperHalfPlane) : ℂ) = ((lam ^ 2 : ℝ) : ℂ) * ((A • z : UpperHalfPlane) : ℂ) := by
    have hγz : ∀ z : UpperHalfPlane, ((γ • z : UpperHalfPlane) : ℂ) =
        mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z := fun z => h23l_b_coe_smul γ z
    have hlamc : ((lam ^ 2 : ℝ) : ℂ) = ((multiplier γ : ℝ) : ℂ) := by rw [hmuleq]
    by_cases hc : γ 1 0 = 0
    · by_cases ha : 1 < |γ 0 0|
      · obtain ⟨hA1, hR1⟩ := (hnf_fixed_of_eq_zero hc).1 ha
        set τ : ℝ := γ 0 1 / (γ 1 1 - γ 0 0) with hτ
        have hf := hinfτ τ hA1 hR1
        let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![1, -τ; 0, 1], by simp [Matrix.det_fin_two]⟩
        refine ⟨A, fun z => ?_⟩
        rw [h23l_b_coe_smul A, h23l_b_coe_smul A, hγz z, hlamc]
        have h1 : ((A 0 0 : ℝ) : ℂ) = 1 := by simp [A]
        have h2 : ((A 0 1 : ℝ) : ℂ) = -(τ : ℂ) := by simp [A]
        have h3 : ((A 1 0 : ℝ) : ℂ) = 0 := by simp [A]
        have h4 : ((A 1 1 : ℝ) : ℂ) = 1 := by simp [A]
        rw [h1, h2, h3, h4]
        have := hf z
        simp only [zero_mul, zero_add, div_one]
        linear_combination this
      · obtain ⟨hA1, hR1⟩ := (hnf_fixed_of_eq_zero hc).2 ha
        set σ : ℝ := γ 0 1 / (γ 1 1 - γ 0 0) with hσ
        have hf := hinfσ σ hA1 hR1
        let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![0, -1; 1, -σ], by simp [Matrix.det_fin_two]⟩
        refine ⟨A, fun z => ?_⟩
        rw [h23l_b_coe_smul A, h23l_b_coe_smul A, hγz z, hlamc]
        have h1 : ((A 0 0 : ℝ) : ℂ) = 0 := by simp [A]
        have h2 : ((A 0 1 : ℝ) : ℂ) = -1 := by simp [A]
        have h3 : ((A 1 0 : ℝ) : ℂ) = 1 := by simp [A]
        have h4 : ((A 1 1 : ℝ) : ℂ) = -(σ : ℂ) := by simp [A]
        rw [h1, h2, h3, h4]
        have hzσ : (z : ℂ) - σ ≠ 0 := sub_ne_zero.2 (s27t_ne_real z σ)
        have hmσ : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z : ℂ) - σ ≠ 0 := by
          rw [hf z]
          exact div_ne_zero hzσ (by exact_mod_cast (by linarith : (multiplier γ) ≠ 0))
        have hm0 : (multiplier γ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (multiplier γ) ≠ 0)
        have hf' := hf z
        simp only [zero_mul, zero_add, one_mul, ← sub_eq_add_neg]
        rw [hf']
        field_simp
    · -- `c ≠ 0`: finite fixed points `σ` (attracting) and `τ` (repelling)
      obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
      obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
      have hστ : σ ≠ τ := by
        intro h
        apply hne
        rw [hσ, hτ, h]
      have hcr' := hcr σ τ hσ hτ
      have hτσ : τ - σ ≠ 0 := sub_ne_zero.2 hστ.symm
      -- an orientation sign `ε = ±1` with `ε (τ - σ) = |τ - σ|`
      obtain ⟨ε, hε2, hεabs⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ε * (τ - σ) = |τ - σ| := by
        rcases lt_or_gt_of_ne hστ with h | h
        · exact ⟨1, by norm_num, by rw [abs_of_pos (by linarith)]; ring⟩
        · exact ⟨-1, by norm_num, by rw [abs_of_neg (by linarith)]; ring⟩
      have hdpos : 0 < |τ - σ| := abs_pos.2 hτσ
      obtain ⟨s, hs2⟩ : ∃ s : ℝ, s ^ 2 * |τ - σ| = 1 := ⟨1 / Real.sqrt |τ - σ|, by
        rw [div_pow, Real.sq_sqrt hdpos.le]
        field_simp⟩
      have hs0 : s ≠ 0 := by
        rintro rfl
        norm_num at hs2
      have hε0 : ε ≠ 0 := by
        rintro rfl
        norm_num at hε2
      let A : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
        ⟨!![ε * s, -(ε * s * τ); s, -(s * σ)], by
          rw [Matrix.det_fin_two_of]
          linear_combination (s ^ 2) * hεabs + hs2⟩
      have hAform : ∀ w : UpperHalfPlane, ((A • w : UpperHalfPlane) : ℂ) =
          (ε : ℂ) * ((w : ℂ) - τ) / ((w : ℂ) - σ) := by
        intro w
        have hwσ : (w : ℂ) - σ ≠ 0 := sub_ne_zero.2 (s27t_ne_real w σ)
        rw [h23l_b_coe_smul A]
        have e1 : ((A 0 0 : ℝ) : ℂ) = (ε : ℂ) * s := by simp [A]
        have e2 : ((A 0 1 : ℝ) : ℂ) = -((ε : ℂ) * s * τ) := by simp [A]
        have e3 : ((A 1 0 : ℝ) : ℂ) = s := by simp [A]
        have e4 : ((A 1 1 : ℝ) : ℂ) = -((s : ℂ) * σ) := by simp [A]
        rw [e1, e2, e3, e4]
        have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
        rw [div_eq_div_iff (by
          intro h
          apply hwσ
          have : (s : ℂ) * ((w : ℂ) - σ) = 0 := by linear_combination h
          exact (mul_eq_zero.1 this).resolve_left hs0') hwσ]
        ring
      refine ⟨A, fun z => ?_⟩
      rw [hAform, hAform, hlamc]
      have hzσ : (z : ℂ) - σ ≠ 0 := sub_ne_zero.2 (s27t_ne_real z σ)
      have hzτ : (z : ℂ) - τ ≠ 0 := sub_ne_zero.2 (s27t_ne_real z τ)
      have hgz : ((γ • z : UpperHalfPlane) : ℂ) = mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z := hγz z
      have hgσ : ((γ • z : UpperHalfPlane) : ℂ) - σ ≠ 0 := sub_ne_zero.2 (s27t_ne_real _ σ)
      have hgτ : ((γ • z : UpperHalfPlane) : ℂ) - τ ≠ 0 := sub_ne_zero.2 (s27t_ne_real _ τ)
      have hden : (γ 1 0 : ℂ) * (z : ℂ) + γ 1 1 ≠ 0 := h23l_b_den_ne γ z.2
      have hcross := hcr' z hden (s27t_ne_real z τ) (by rw [← hgz]; exact sub_ne_zero.1 hgτ)
      rw [← hgz] at hcross
      have hm0 : (multiplier γ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (multiplier γ) ≠ 0)
      rw [div_eq_iff hzτ] at hcross
      field_simp at hcross ⊢
      linear_combination (ε : ℂ) * hcross
  obtain ⟨A, hA⟩ := key
  refine ⟨A, lam, hlam1, ?_, fun τ => ?_⟩
  · show Real.log (lam ^ 2) = 2 * Real.log ((|slTrace γ| + Real.sqrt (slTrace γ ^ 2 - 4)) / 2)
    rw [Real.log_pow]
    rfl
  · have h := hA (A⁻¹ • τ)
    rw [smul_inv_smul] at h
    rw [mul_smul, mul_smul]
    exact h

/-- Helper for `s30w_log_le` (§30.5), (30.7) rescaled: `φ(z) = e^{2π²/L} exp(2πi log z / L)` (`L = ln λ²`) has the
`⟨λ²⟩`-orbits of `ℍ` as fibres and maps `ℍ` onto the annulus `{1 < |w| < e^{2π²/L}}`. -/
theorem s30w_phi_facts {lam : ℝ} (hlam : 1 < lam) :
    (∀ z ∈ upperHalf, ∀ w ∈ upperHalf,
      ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) * exp (2 * π * I * log z / Real.log (lam ^ 2)) =
        ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) * exp (2 * π * I * log w / Real.log (lam ^ 2)) ↔
        ∃ n : ℤ, w = ((lam : ℂ) ^ 2) ^ n * z) ∧
    (fun z : ℂ => ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) *
      exp (2 * π * I * log z / Real.log (lam ^ 2))) '' upperHalf =
      annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))) := by
  obtain ⟨h1, h2, -⟩ := eq30_7_annulus_modulus hlam
  have hlam2 : 1 < lam ^ 2 := by nlinarith
  have hL : 0 < Real.log (lam ^ 2) := Real.log_pos hlam2
  have hc : ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  refine ⟨fun z hz w hw => ?_, ?_⟩
  · rw [mul_right_inj' hc]
    exact (h1 z hz w hw).symm
  · set c : ℝ := Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) with hcdef
    have hcpos : 0 < c := Real.exp_pos _
    set a : ℝ := Real.exp (-(2 * π ^ 2) / Real.log (lam ^ 2)) with hadef
    have hac : a * c = 1 := by
      rw [hadef, hcdef, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    have hapos : 0 < a := Real.exp_pos _
    have himg : (fun z : ℂ => (c : ℂ) * exp (2 * π * I * log z / Real.log (lam ^ 2))) '' upperHalf =
        (fun u : ℂ => (c : ℂ) * u) '' ((fun z : ℂ => exp (2 * π * I * log z / Real.log (lam ^ 2))) '' upperHalf) := by
      rw [← image_comp]
      rfl
    rw [himg, h2]
    ext u
    simp only [mem_image, annulus, mem_setOf_eq]
    constructor
    · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
      constructor
      · calc (1 : ℝ) = a * c := hac.symm
          _ < ‖v‖ * c := by gcongr
          _ = c * ‖v‖ := mul_comm _ _
      · calc c * ‖v‖ < c * 1 := by gcongr
          _ = c := mul_one c
    · rintro ⟨hu1, hu2⟩
      refine ⟨u / c, ⟨?_, ?_⟩, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hcpos.le, lt_div_iff₀ hcpos]
        nlinarith
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hcpos.le, div_lt_one hcpos]
        exact hu2
      · field_simp

/-- Helper for `s30w_log_le`: `φ` is holomorphic on `ℍ`. -/
theorem s30w_phi_differentiableOn (L : ℝ) (c : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => (c : ℂ) * exp (2 * π * I * log z / L)) upperHalf := by
  intro z hz
  have hslit : z ∈ slitPlane := Or.inr (ne_of_gt hz)
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (differentiableAt_const _).mul
    ((((differentiableAt_const _).mul (differentiableAt_log hslit)).div_const _).cexp)

/-- Helper for `s30w_log_le`: `φ` is injective on a small disc around every point of `ℍ`: two points of a disc around
`z₀` with `‖w‖ = (λ²)^n ‖z‖`, `n ≠ 0`, would have norms differing by the factor `λ²`, but the norms in the
disc are within `m ± r`, `m = ‖z₀‖`, `r ≤ m (λ² - 1)/(λ² + 1)`. -/
theorem s30w_phi_injOn_ball {lam : ℝ} (hlam : 1 < lam) {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf) :
    ∃ r > (0 : ℝ), ball z₀ r ⊆ upperHalf ∧ InjOn (fun z : ℂ => ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) *
      exp (2 * π * I * log z / Real.log (lam ^ 2))) (ball z₀ r) := by
  obtain ⟨hfib, -⟩ := s30w_phi_facts hlam
  have hz₀' : 0 < z₀.im := hz₀
  have hlam2 : 1 < lam ^ 2 := by nlinarith
  have hm : 0 < ‖z₀‖ := norm_pos_iff.2 (fun h => by rw [h] at hz₀'; simp at hz₀')
  set m := ‖z₀‖ with hmdef
  set r := min z₀.im (m * (lam ^ 2 - 1) / (lam ^ 2 + 1)) with hrdef
  have hr0 : 0 < r := lt_min hz₀' (by positivity)
  have hr1 : r ≤ z₀.im := min_le_left _ _
  have hr2 : r ≤ m * (lam ^ 2 - 1) / (lam ^ 2 + 1) := min_le_right _ _
  have hr3 : r * (lam ^ 2 + 1) ≤ m * (lam ^ 2 - 1) := by
    rwa [le_div_iff₀ (by positivity)] at hr2
  have hsub : ball z₀ r ⊆ upperHalf := by
    intro z hz
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa using Complex.abs_im_le_norm (z - z₀)
    have h2 : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using hz
    show 0 < z.im
    have := abs_lt.1 (lt_of_le_of_lt h1 h2)
    linarith [this.1, hr1]
  refine ⟨r, hr0, hsub, fun z hz w hw hzw => ?_⟩
  obtain ⟨n, hn⟩ := (hfib z (hsub hz) w (hsub hw)).1 hzw
  by_cases hn0 : n = 0
  · rw [hn, hn0]
    simp
  exfalso
  have hnz : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using hz
  have hnw : ‖w - z₀‖ < r := by simpa [dist_eq_norm] using hw
  have hnorm_z : |‖z‖ - m| < r := lt_of_le_of_lt (abs_norm_sub_norm_le z z₀) hnz
  have hnorm_w : |‖w‖ - m| < r := lt_of_le_of_lt (abs_norm_sub_norm_le w z₀) hnw
  have hl : ‖(lam : ℂ)‖ = lam := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hwn : ‖w‖ = (lam ^ 2) ^ n * ‖z‖ := by
    rw [hn, norm_mul, norm_zpow, norm_pow, hl]
  obtain ⟨hz1, hz2⟩ := abs_lt.1 hnorm_z
  obtain ⟨hw1, hw2⟩ := abs_lt.1 hnorm_w
  have hzpos : 0 ≤ ‖z‖ := norm_nonneg _
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have h1 : (lam ^ 2) ^ n ≤ (lam ^ 2) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hlam2.le (by omega)
    rw [zpow_neg_one] at h1
    have h2 : ‖w‖ ≤ (lam ^ 2)⁻¹ * ‖z‖ := by
      rw [hwn]
      exact mul_le_mul_of_nonneg_right h1 hzpos
    have h3 : lam ^ 2 * ‖w‖ ≤ ‖z‖ := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ lam ^ 2)
      rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
    nlinarith [mul_pos (by positivity : (0 : ℝ) < lam ^ 2) (by linarith : 0 < ‖w‖ - m + r)]
  · have h1 : (lam ^ 2) ^ (1 : ℤ) ≤ (lam ^ 2) ^ n := zpow_le_zpow_right₀ hlam2.le (by omega)
    rw [zpow_one] at h1
    have h2 : lam ^ 2 * ‖z‖ ≤ ‖w‖ := by
      rw [hwn]
      exact mul_le_mul_of_nonneg_right h1 hzpos
    nlinarith [mul_pos (by positivity : (0 : ℝ) < lam ^ 2) (by linarith : 0 < ‖z‖ - m + r)]
/-- Helper for `s30w_log_le`: positive real scalars preserve `ℍ`, in the form `(λ²)^n z`. -/
theorem s30w_zpow_mem {lam : ℝ} (hlam : 0 < lam) (n : ℤ) {z : ℂ} (hz : z ∈ upperHalf) :
    ((lam : ℂ) ^ 2) ^ n * z ∈ upperHalf := by
  have hz' : 0 < z.im := hz
  have e : ((lam : ℂ) ^ 2) ^ n = (((lam ^ 2) ^ n : ℝ) : ℂ) := by push_cast; rfl
  show 0 < (((lam : ℂ) ^ 2) ^ n * z).im
  rw [e, Complex.im_ofReal_mul]
  exact mul_pos (zpow_pos (by positivity) n) hz'

/-- Helper for `s30w_log_le`: if `f(λ² z) = (λ′)² f(z)` on `ℍ` and `f` maps `ℍ` into `ℍ`, then
`f((λ²)^n z) = ((λ′)²)^n f(z)` for all integers `n`. -/
theorem s30w_pow_equivariant {lam lam' : ℝ} (hlam : 1 < lam) (hlam' : 1 < lam') {f : ℂ → ℂ}
    (hmaps : ∀ z ∈ upperHalf, f z ∈ upperHalf)
    (hcomm : ∀ z ∈ upperHalf, f (((lam ^ 2 : ℝ) : ℂ) * z) = ((lam' ^ 2 : ℝ) : ℂ) * f z) :
    ∀ n : ℤ, ∀ z ∈ upperHalf, f (((lam : ℂ) ^ 2) ^ n * z) = ((lam' : ℂ) ^ 2) ^ n * f z := by
  have hA : ((lam : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by linarith : lam ≠ 0))
  have hB : ((lam' : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by linarith : lam' ≠ 0))
  have hc : ∀ z ∈ upperHalf, f (((lam : ℂ) ^ 2) * z) = ((lam' : ℂ) ^ 2) * f z := fun z hz => by
    have := hcomm z hz
    push_cast at this
    exact this
  have hnat : ∀ k : ℕ, ∀ z ∈ upperHalf, f (((lam : ℂ) ^ 2) ^ k * z) = ((lam' : ℂ) ^ 2) ^ k * f z := by
    intro k
    induction k with
    | zero => intro z hz; simp
    | succ k ih =>
      intro z hz
      have hmem := s30w_zpow_mem (lam := lam) (by linarith) (k : ℤ) hz
      rw [zpow_natCast] at hmem
      have h1 := hc _ hmem
      rw [pow_succ' ((lam : ℂ) ^ 2) k, mul_assoc, h1, ih z hz, pow_succ' ((lam' : ℂ) ^ 2) k, mul_assoc]
  intro n z hz
  rcases le_or_gt 0 n with h | h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simpa using hnat k z hz
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    have hy : (((lam : ℂ) ^ 2) ^ m)⁻¹ * z ∈ upperHalf := by
      have := s30w_zpow_mem (lam := lam) (by linarith) (-(m : ℤ)) hz
      rwa [zpow_neg, zpow_natCast] at this
    have h1 := hnat m _ hy
    rw [mul_inv_cancel_left₀ (pow_ne_zero m hA)] at h1
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, h1, inv_mul_cancel_left₀ (pow_ne_zero m hB)]
/-- Helper for `s30w_log_le` (§30.5), (30.6): a `K`-q.c. self-map `F` of `ℍ` with `F(λ² z) = (λ′)² F(z)` descends
through `φ`, `φ′` to a `K`-q.c. homeomorphism `g` of the annulus `{1 < |w| < e^{2π²/ln λ²}}` onto
`{1 < |w| < e^{2π²/ln (λ′)²}}`: `g ∘ φ = φ′ ∘ F` (well defined and injective because the fibres are the orbits and
`F` is equivariant and injective), and locally `g = φ′ ∘ F ∘ (φ|U)⁻¹` with `φ|U`, `φ′|F(U)` conformal (`s23_lg`: being
`K`-q.c. is local). -/
theorem s30w_descent {lam lam' K : ℝ} (hlam : 1 < lam) (hlam' : 1 < lam') {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsKQC (liftToC F) upperHalf K)
    (hcomm : ∀ z ∈ upperHalf, liftToC F (((lam ^ 2 : ℝ) : ℂ) * z) = ((lam' ^ 2 : ℝ) : ℂ) * liftToC F z) :
    ∃ g : ℂ → ℂ, IsKQC g (annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)))) K ∧
      g '' annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))) =
        annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam' ^ 2))) := by
  obtain ⟨hfib, himg⟩ := s30w_phi_facts hlam
  obtain ⟨hfib', himg'⟩ := s30w_phi_facts hlam'
  obtain ⟨phi, hphi⟩ : ∃ phi : ℂ → ℂ, phi = fun z : ℂ =>
      ((Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) : ℝ) : ℂ) * exp (2 * π * I * log z / Real.log (lam ^ 2)) :=
    ⟨_, rfl⟩
  obtain ⟨phi', hphi'⟩ : ∃ phi' : ℂ → ℂ, phi' = fun z : ℂ =>
      ((Real.exp (2 * π ^ 2 / Real.log (lam' ^ 2)) : ℝ) : ℂ) * exp (2 * π * I * log z / Real.log (lam' ^ 2)) :=
    ⟨_, rfl⟩
  rw [← hphi] at himg
  rw [← hphi'] at himg'
  have hfib2 : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf, phi z = phi w ↔ ∃ n : ℤ, w = ((lam : ℂ) ^ 2) ^ n * z := by
    intro z hz w hw
    rw [hphi]
    exact hfib z hz w hw
  have hfib2' : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf, phi' z = phi' w ↔ ∃ n : ℤ, w = ((lam' : ℂ) ^ 2) ^ n * z := by
    intro z hz w hw
    rw [hphi']
    exact hfib' z hz w hw
  have hphid : DifferentiableOn ℂ phi upperHalf := by
    rw [hphi]
    exact s30w_phi_differentiableOn _ _
  have hphid' : DifferentiableOn ℂ phi' upperHalf := by
    rw [hphi']
    exact s30w_phi_differentiableOn _ _
  set f : ℂ → ℂ := liftToC F with hfdef
  have hfmaps : ∀ z ∈ upperHalf, f z ∈ upperHalf := fun z hz => by
    rw [hfdef, h23l_liftToC_eq F hz]
    exact (F _).coe_im_pos
  have hfcont : ContinuousOn f upperHalf := hF.2.2.1.1
  have hfinj : InjOn f upperHalf := hF.2.2.1.2.1
  have hfimg : f '' upperHalf = upperHalf := h36q_liftToC_image F
  have hpow := s30w_pow_equivariant hlam hlam' hfmaps hcomm
  have hphiA : ∀ z ∈ upperHalf, phi z ∈ annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))) := fun z hz => by
    rw [← himg]
    exact mem_image_of_mem _ hz
  have hphiA' : ∀ z ∈ upperHalf, phi' z ∈ annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam' ^ 2))) := fun z hz => by
    rw [← himg']
    exact mem_image_of_mem _ hz
  -- the descended map
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun w => phi' (f (Function.invFunOn phi upperHalf w)) := ⟨_, rfl⟩
  have hgphi : ∀ z ∈ upperHalf, g (phi z) = phi' (f z) := by
    intro z hz
    have hmem : phi z ∈ phi '' upperHalf := mem_image_of_mem _ hz
    have h1 := Function.invFunOn_mem hmem
    have h2 := Function.invFunOn_eq hmem
    rw [hgdef]
    show phi' (f (Function.invFunOn phi upperHalf (phi z))) = _
    set z₁ := Function.invFunOn phi upperHalf (phi z) with hz₁
    obtain ⟨n, hn⟩ := (hfib2 z₁ h1 z hz).1 h2
    have hfz : f z = ((lam' : ℂ) ^ 2) ^ n * f z₁ := by
      have := hpow n z₁ h1
      rwa [← hn] at this
    exact (hfib2' (f z₁) (hfmaps _ h1) (f z) (hfmaps z hz)).2 ⟨n, hfz⟩
  have hinj : InjOn g (annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)))) := by
    intro w₁ hw₁ w₂ hw₂ h
    rw [← himg] at hw₁ hw₂
    obtain ⟨z₁, hz₁, rfl⟩ := hw₁
    obtain ⟨z₂, hz₂, rfl⟩ := hw₂
    rw [hgphi z₁ hz₁, hgphi z₂ hz₂] at h
    obtain ⟨n, hn⟩ := (hfib2' _ (hfmaps z₁ hz₁) _ (hfmaps z₂ hz₂)).1 h
    have hmem := s30w_zpow_mem (lam := lam) (by linarith) n hz₁
    have : f z₂ = f (((lam : ℂ) ^ 2) ^ n * z₁) := by rw [hpow n z₁ hz₁]; exact hn
    have hz₂eq := hfinj hz₂ hmem this
    exact (hfib2 z₁ hz₁ z₂ hz₂).2 ⟨n, hz₂eq⟩
  have hgimg : g '' annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))) =
      annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam' ^ 2))) := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← himg] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [hgphi z hz]
      exact hphiA' _ (hfmaps z hz)
    · intro hu
      rw [← himg'] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      rw [← hfimg] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨phi z, hphiA z hz, hgphi z hz⟩
  -- local `K`-quasiconformality
  have hloc : ∀ w₀ ∈ annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))),
      ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧ U ⊆ annulus 1 (Real.exp (2 * π ^ 2 / Real.log (lam ^ 2))) ∧ IsKQC g U K := by
    intro w₀ hw₀
    rw [← himg] at hw₀
    obtain ⟨z₀, hz₀, rfl⟩ := hw₀
    obtain ⟨r, hr, hrsub, hrinj⟩ := s30w_phi_injOn_ball hlam hz₀
    obtain ⟨r', hr', hr'sub, hr'inj⟩ := s30w_phi_injOn_ball hlam' (hfmaps z₀ hz₀)
    rw [← hphi] at hrinj
    rw [← hphi'] at hr'inj
    set U₁ : Set ℂ := ball z₀ r ∩ f ⁻¹' ball (f z₀) r' with hU₁
    have hU₁o : IsOpen U₁ := (hfcont.mono hrsub).isOpen_inter_preimage isOpen_ball isOpen_ball
    have hz₀U : z₀ ∈ U₁ := ⟨mem_ball_self hr, mem_ball_self hr'⟩
    have hU₁H : U₁ ⊆ upperHalf := fun z hz => hrsub hz.1
    have hconf : IsConformalOnto phi U₁ (phi '' U₁) :=
      ⟨hphid.mono hU₁H, hrinj.mono inter_subset_left, rfl⟩
    have hVo : IsOpen (phi '' U₁) := hconf.isOpen hU₁o
    refine ⟨phi '' U₁, hVo, mem_image_of_mem _ hz₀U, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hphiA z (hU₁H hz)
    · have hσc := hconf.symm hU₁o
      have hσ : IsKQC (Function.invFunOn phi U₁) (phi '' U₁) 1 := isKQC_one_of_conformal hVo hσc
      have hfU : IsKQC f U₁ K := ac_t_isKQC_restrict hF hU₁o hU₁H
      have hfUo : IsOpen (f '' U₁) := isOpen_image_of_isKQC hfU
      have hfUsub : f '' U₁ ⊆ upperHalf := by
        rintro _ ⟨z, hz, rfl⟩
        exact hfmaps z (hU₁H hz)
      have hfUball : f '' U₁ ⊆ ball (f z₀) r' := by
        rintro _ ⟨z, hz, rfl⟩
        exact hz.2
      have hphi'conf : IsConformalOnto phi' (f '' U₁) (phi' '' (f '' U₁)) :=
        ⟨hphid'.mono hfUsub, hr'inj.mono hfUball, rfl⟩
      have hφ' : IsKQC phi' (f '' U₁) 1 := isKQC_one_of_conformal hfUo hphi'conf
      have h2 : IsKQC (f ∘ Function.invFunOn phi U₁) (phi '' U₁) (1 * K) :=
        thm7_1_comp hσ hfU (by rw [hσc.2.2])
      have h3 : IsKQC (phi' ∘ (f ∘ Function.invFunOn phi U₁)) (phi '' U₁) (1 * K * 1) :=
        thm7_1_comp h2 hφ' (by rw [image_comp, hσc.2.2])
      rw [one_mul, mul_one] at h3
      refine ad_isKQC_congr h3 fun w hw => ?_
      obtain ⟨z, hz, rfl⟩ := hw
      simp only [Function.comp_apply]
      rw [(hrinj.mono inter_subset_left).leftInvOn_invFunOn hz]
      exact hgphi z (hU₁H hz)
  exact ⟨g, s23_lg (isOpen_annulus _ _) hF.2.1 hinj hloc, hgimg⟩

/-- Helper for **Lemma 30.3** (§30.5), (30.6)–(30.9) for dilations. If a `K`-q.c. homeomorphism `F` of `ℍ` satisfies
`F(λ² z) = (λ′)² F(z)` (`λ, λ′ > 1`), then `ln λ² ≤ K ln (λ′)²`. The map descends through
`z ↦ exp(2πi log z / ln λ²)` (`eq30_7_annulus_modulus`: fibres = `⟨λ²⟩`-orbits, image the annulus of modulus
`2π²/ln λ²`) to a `K`-q.c. homeomorphism between the two annuli (`s23_lg`: being `K`-q.c. is local), and
`aqc_log_le_of_quad_bound` gives `2π²/ln (λ′)² ≤ K · 2π²/ln λ²`; the other inequality of (30.9) is this one for `F⁻¹`. -/
theorem s30w_log_le {lam lam' K : ℝ} (hlam : 1 < lam) (hlam' : 1 < lam') {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsKQC (liftToC F) upperHalf K)
    (hcomm : ∀ z ∈ upperHalf, liftToC F (((lam ^ 2 : ℝ) : ℂ) * z) = ((lam' ^ 2 : ℝ) : ℂ) * liftToC F z) :
    Real.log (lam ^ 2) ≤ K * Real.log (lam' ^ 2) := by
  obtain ⟨g, hgK, hgimg⟩ := s30w_descent hlam hlam' hF hcomm
  have hlam2 : 1 < lam ^ 2 := by nlinarith
  have hlam2' : 1 < lam' ^ 2 := by nlinarith
  have hL : 0 < Real.log (lam ^ 2) := Real.log_pos hlam2
  have hL' : 0 < Real.log (lam' ^ 2) := Real.log_pos hlam2'
  have hR : 1 < Real.exp (2 * π ^ 2 / Real.log (lam ^ 2)) := Real.one_lt_exp_iff.2 (by positivity)
  have hR' : 1 < Real.exp (2 * π ^ 2 / Real.log (lam' ^ 2)) := Real.one_lt_exp_iff.2 (by positivity)
  have hK0 : 0 ≤ K := by linarith [hF.2.1]
  obtain ⟨-, -, hg, hmod⟩ := id hgK
  rw [hgimg] at hg
  have h := aqc_log_le_of_quad_bound hR hR' hK0 hg fun Q hQ => hmod Q hQ
  rw [Real.log_exp, Real.log_exp] at h
  set L := Real.log (lam ^ 2)
  set L' := Real.log (lam' ^ 2)
  have hπ : 0 < π ^ 2 := by positivity
  -- `2π²/L′ ≤ K · 2π²/L` gives `L ≤ K L′`
  have h1 : 2 * π ^ 2 / L' * (L * L') ≤ K * (2 * π ^ 2 / L) * (L * L') :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have e1 : 2 * π ^ 2 / L' * (L * L') = 2 * π ^ 2 * L := by field_simp
  have e2 : K * (2 * π ^ 2 / L) * (L * L') = K * L' * (2 * π ^ 2) := by field_simp
  rw [e1, e2] at h1
  nlinarith

/-- Helper for `s30w_translation_le`: conjugating a `K`-q.c. self-map of `ℍ` by Möbius maps of `SL(2, ℝ)` keeps it
`K`-q.c. (`thm7_1_comp` with the `1`-q.c. Möbius maps). -/
theorem s30w_isKQC_conj {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {K : ℝ} (hF : IsKQC (liftToC F) upperHalf K)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsKQC (liftToC (((Homeomorph.smul A).trans F).trans (Homeomorph.smul B))) upperHalf K := by
  have hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, 0 < g 0 0 * g 1 1 - g 0 1 * g 1 0 := fun g => by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [h]
    exact one_pos
  have hAc := isConformalOnto_mobius_upperHalf (hdet A)
  have hBc := isConformalOnto_mobius_upperHalf (hdet B)
  have hA1 := isKQC_one_of_conformal isOpen_upperHalf hAc
  have hB1 := isKQC_one_of_conformal isOpen_upperHalf hBc
  have hFm : ∀ w ∈ upperHalf, liftToC F w ∈ upperHalf := fun w hw => by
    rw [h23l_liftToC_eq F hw]
    exact (F _).coe_im_pos
  have h1 := thm7_1_comp hA1 hF (by rw [hAc.2.2])
  have h2 := thm7_1_comp h1 hB1 (by
    rintro _ ⟨z, hz, rfl⟩
    exact hFm _ (mobiusFn_mem_upperHalf (hdet A) hz))
  rw [one_mul, mul_one] at h2
  refine ad_isKQC_congr h2 fun z hz => ?_
  have hz' : 0 < z.im := hz
  have e : UpperHalfPlane.ofComplex z = (⟨z, hz'⟩ : UpperHalfPlane) := UpperHalfPlane.ofComplex_apply_of_im_pos hz'
  have hA' : ((A • (⟨z, hz'⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
      mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) z := h23l_b_coe_smul A _
  rw [h23l_liftToC_eq _ hz, e, Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.smul_apply,
    Homeomorph.smul_apply, h23l_b_coe_smul B]
  simp only [Function.comp_apply]
  rw [← hA', h23l_liftToC_coe]
  rfl

/-- Helper for **Lemma 30.3** (§30.5), (30.9) in invariant form. If `F` is a `K`-q.c. homeomorphism of `ℍ` with
`F ∘ γ = δ ∘ F` for hyperbolic `γ, δ ∈ SL(2, ℝ)`, then `translationLength γ ≤ K · translationLength δ`. Conjugate `γ`
and `δ` to dilations (`s30w_conj_dilation`; `translationLength` is conjugation invariant,
`translationLength_eq_inf_dist`), `A₂ F A₁⁻¹` is `K`-q.c. (`thm7_1_comp`) and equivariant, and `s30w_log_le` applies
(with `z ↦ -1/z` composed to make the multiplier `> 1` if needed). -/
theorem s30w_translation_le {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ)
    (hδ : IsHyperbolic δ) {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {K : ℝ} (hF : IsKQC (liftToC F) upperHalf K)
    (hγδ : ∀ τ, F (γ • τ) = δ • F τ) : translationLength γ ≤ K * translationLength δ := by
  obtain ⟨A₁, lam, hlam, hlog, hA₁⟩ := s30w_conj_dilation hγ
  obtain ⟨A₂, lam', hlam', hlog', hA₂⟩ := s30w_conj_dilation hδ
  set F' : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    ((Homeomorph.smul A₁⁻¹).trans F).trans (Homeomorph.smul A₂) with hF'
  have hF'qc : IsKQC (liftToC F') upperHalf K := s30w_isKQC_conj hF A₁⁻¹ A₂
  have hF'γ : ∀ τ : UpperHalfPlane, F' ((A₁ * γ * A₁⁻¹) • τ) = (A₂ * δ * A₂⁻¹) • F' τ := by
    intro τ
    simp only [hF', Homeomorph.trans_apply, Homeomorph.smul_apply]
    rw [show A₁⁻¹ • (A₁ * γ * A₁⁻¹) • τ = γ • A₁⁻¹ • τ by
      rw [← mul_smul, ← mul_smul, show A₁⁻¹ * (A₁ * γ * A₁⁻¹) = γ * A₁⁻¹ by group], hγδ,
      show (A₂ * δ * A₂⁻¹) • A₂ • F (A₁⁻¹ • τ) = A₂ • δ • F (A₁⁻¹ • τ) by
      rw [← mul_smul, ← mul_smul, show A₂ * δ * A₂⁻¹ * A₂ = A₂ * δ by group]]
  have hcomm : ∀ z ∈ upperHalf, liftToC F' (((lam ^ 2 : ℝ) : ℂ) * z) = ((lam' ^ 2 : ℝ) : ℂ) * liftToC F' z := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hlam2 : (0 : ℝ) < lam ^ 2 := by positivity
    have hpos : 0 < (((lam ^ 2 : ℝ) : ℂ) * z).im := by
      rw [Complex.im_ofReal_mul]
      exact mul_pos hlam2 hz'
    have hmem : (((lam ^ 2 : ℝ) : ℂ) * z) ∈ upperHalf := hpos
    set τ : UpperHalfPlane := ⟨z, hz'⟩ with hτ
    have e1 : UpperHalfPlane.ofComplex z = τ := UpperHalfPlane.ofComplex_apply_of_im_pos hz'
    have e2 : UpperHalfPlane.ofComplex (((lam ^ 2 : ℝ) : ℂ) * z) = (A₁ * γ * A₁⁻¹) • τ := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
      exact (hA₁ τ).symm
    rw [h23l_liftToC_eq _ hmem, h23l_liftToC_eq _ hz, e1, e2, hF'γ]
    exact hA₂ (F' τ)
  have := s30w_log_le hlam hlam' hF'qc hcomm
  rw [hlog, hlog'] at this
  exact this

/-- Helper for `s30w_not_hyperbolic` (§30.5). A projective fixed vector `[p : q]` of `γ ∈ SL(2, ℝ)`
(`c p² + (d - a) p q - b q² = 0`) gives a fixed point of `mobiusSL γ` on `ℝ̂`: `p/q` (or `∞` when `q = 0`). -/
theorem s30w_fixed_of_vec {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {p q : ℝ} (hpq : p ≠ 0 ∨ q ≠ 0)
    (hQ : δ 1 0 * p ^ 2 + (δ 1 1 - δ 0 0) * p * q - δ 0 1 * q ^ 2 = 0) :
    (if q = 0 then extInf else ((((p / q : ℝ)) : ℂ) : ExtPlane)) ∈ extRealLine ∧
      mobiusSL (slRealToComplex δ) (if q = 0 then extInf else ((((p / q : ℝ)) : ℂ) : ExtPlane)) =
        (if q = 0 then extInf else ((((p / q : ℝ)) : ℂ) : ExtPlane)) := by
  have hdet := hnf_sl2_det δ
  rw [k24_mobiusSL_real]
  by_cases hq : q = 0
  · subst hq
    have hp : p ≠ 0 := hpq.resolve_right (not_not.2 rfl)
    have hc : δ 1 0 = 0 := by
      have h : δ 1 0 * p ^ 2 = 0 := by linear_combination hQ
      exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero 2 hp)
    simp only [if_true]
    refine ⟨Or.inr rfl, ?_⟩
    rw [mobiusExt_infty_of_eq (by exact_mod_cast hc)]
  · simp only [hq, ite_false]
    have hQx : δ 1 0 * (p / q) ^ 2 + (δ 1 1 - δ 0 0) * (p / q) - δ 0 1 = 0 := by
      have h : q ^ 2 * (δ 1 0 * (p / q) ^ 2 + (δ 1 1 - δ 0 0) * (p / q) - δ 0 1) = 0 := by
        field_simp
        linear_combination hQ
      exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 2 hq)
    refine ⟨Or.inl ⟨((p / q : ℝ) : ℂ), by simp [realLine], rfl⟩, ?_⟩
    have hne : δ 1 0 * (p / q) + δ 1 1 ≠ 0 := by
      intro h0
      -- then `a x + b = 0` too, so both rows are orthogonal to `(x, 1)`: `det = 0`
      have h1 : δ 0 0 * (p / q) + δ 0 1 = 0 := by linear_combination (-1 : ℝ) * hQx + (p / q) * h0
      have : (δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0) = 0 := by
        linear_combination δ 0 0 * h0 - δ 1 0 * h1
      rw [hdet] at this
      exact one_ne_zero this
    rw [mobiusExt_ofReal_coe hne]
    congr 2
    rw [div_eq_iff hne]
    linear_combination (-1 : ℝ) * hQx

/-- Helper for `s30w_not_hyperbolic`: a fixed point of `mobiusSL γ` on `ℝ̂` is `[p : q]` for a projective fixed
vector. -/
theorem s30w_vec_of_fixed {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {u : ExtPlane} (hu : u ∈ extRealLine)
    (hfix : mobiusSL (slRealToComplex δ) u = u) :
    ∃ p q : ℝ, (p ≠ 0 ∨ q ≠ 0) ∧ δ 1 0 * p ^ 2 + (δ 1 1 - δ 0 0) * p * q - δ 0 1 * q ^ 2 = 0 ∧
      u = (if q = 0 then extInf else ((((p / q : ℝ)) : ℂ) : ExtPlane)) := by
  rw [k24_mobiusSL_real] at hfix
  rcases hu with ⟨z, hz, rfl⟩ | hinf
  · have hzim : z.im = 0 := hz
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) := ⟨z.re, Complex.ext (by simp) (by simpa using hzim)⟩
    refine ⟨x, 1, Or.inr one_ne_zero, ?_, by simp⟩
    by_cases h0 : δ 1 0 * x + δ 1 1 = 0
    · rw [mobiusExt_ofReal_coe_of_eq_zero h0] at hfix
      exact absurd hfix (by simp)
    · rw [mobiusExt_ofReal_coe h0] at hfix
      have h1 := Complex.ofReal_injective (OnePoint.coe_injective hfix)
      rw [div_eq_iff h0] at h1
      linear_combination (-1 : ℝ) * h1
  · rw [Set.mem_singleton_iff] at hinf
    subst hinf
    refine ⟨1, 0, Or.inl one_ne_zero, ?_, by simp⟩
    by_cases hc : δ 1 0 = 0
    · rw [hc]
      ring
    · rw [mobiusExt_ofReal_infty hc] at hfix
      exact absurd hfix (by simp [extInf])

/-- Helper for `s30w_not_hyperbolic`: distinct points `[p₁ : q₁] ≠ [p₂ : q₂]` of `ℝ̂` have `p₁ q₂ - p₂ q₁ ≠ 0`. -/
theorem s30w_det_ne_of_ne {p₁ q₁ p₂ q₂ : ℝ} (h₁ : p₁ ≠ 0 ∨ q₁ ≠ 0) (h₂ : p₂ ≠ 0 ∨ q₂ ≠ 0)
    (hne : (if q₁ = 0 then extInf else ((((p₁ / q₁ : ℝ)) : ℂ) : ExtPlane)) ≠
      (if q₂ = 0 then extInf else ((((p₂ / q₂ : ℝ)) : ℂ) : ExtPlane))) : p₁ * q₂ - p₂ * q₁ ≠ 0 := by
  intro hD
  apply hne
  by_cases hq₁ : q₁ = 0
  · have hp₁ : p₁ ≠ 0 := h₁.resolve_right (not_not.2 hq₁)
    have hq₂ : q₂ = 0 := by
      rw [hq₁, mul_zero, sub_zero] at hD
      exact (mul_eq_zero.1 hD).resolve_left hp₁
    simp [hq₁, hq₂]
  · by_cases hq₂ : q₂ = 0
    · exfalso
      have hp₂ : p₂ ≠ 0 := h₂.resolve_right (not_not.2 hq₂)
      rw [hq₂, mul_zero, zero_sub, neg_eq_zero] at hD
      exact (mul_ne_zero hp₂ hq₁) hD
    · simp only [hq₁, hq₂, ite_false]
      have h : p₁ / q₁ = p₂ / q₂ := by
        rw [div_eq_div_iff hq₁ hq₂]
        linarith
      rw [h]

/-- Helper for `s30w_not_hyperbolic`: converse, `p₁ q₂ - p₂ q₁ ≠ 0` gives distinct points of `ℝ̂`. -/
theorem s30w_ne_of_det_ne {p₁ q₁ p₂ q₂ : ℝ} (hD : p₁ * q₂ - p₂ * q₁ ≠ 0) :
    (if q₁ = 0 then extInf else ((((p₁ / q₁ : ℝ)) : ℂ) : ExtPlane)) ≠
      (if q₂ = 0 then extInf else ((((p₂ / q₂ : ℝ)) : ℂ) : ExtPlane)) := by
  intro h
  apply hD
  by_cases hq₁ : q₁ = 0
  · by_cases hq₂ : q₂ = 0
    · rw [hq₁, hq₂]
      ring
    · simp [hq₁, hq₂] at h
  · by_cases hq₂ : q₂ = 0
    · simp [hq₁, hq₂] at h
    · simp only [hq₁, hq₂, ite_false] at h
      have h' := Complex.ofReal_injective (OnePoint.coe_injective h)
      rw [div_eq_div_iff hq₁ hq₂] at h'
      linarith

/-- Helper for `s30w_not_hyperbolic`: a parabolic element has no two distinct projective fixed vectors. The discriminant
of `c p² + (d - a) p q - b q²` is `(a + d)² - 4 = 0`; for a form vanishing at two independent vectors it is a square
times `(p₁ q₂ - p₂ q₁)²`, so the form is `0` and `γ = ±1`. -/
theorem s30w_parabolic_not_two_fixed {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsParabolic γ)
    {p₁ q₁ p₂ q₂ : ℝ} (hQ₁ : γ 1 0 * p₁ ^ 2 + (γ 1 1 - γ 0 0) * p₁ * q₁ - γ 0 1 * q₁ ^ 2 = 0)
    (hQ₂ : γ 1 0 * p₂ ^ 2 + (γ 1 1 - γ 0 0) * p₂ * q₂ - γ 0 1 * q₂ ^ 2 = 0) (hD : p₁ * q₂ - p₂ * q₁ ≠ 0) :
    False := by
  obtain ⟨htr, h1, h2⟩ := hγ
  have hdet := hnf_sl2_det γ
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  have hdisc : (d - a) ^ 2 + 4 * b * c = 0 := by
    have h4 : (a + d) ^ 2 = 4 := by
      have : |a + d| ^ 2 = 4 := by rw [show slTrace γ = a + d from rfl] at htr; rw [htr]; norm_num
      rwa [sq_abs] at this
    linear_combination h4 - 4 * hdet
  -- the polarization `M` and the identity `M² = disc · D²`
  set M := 2 * c * p₁ * p₂ + (d - a) * (p₁ * q₂ + p₂ * q₁) - 2 * b * q₁ * q₂ with hM
  have hMsq : M ^ 2 = ((d - a) ^ 2 + 4 * b * c) * (p₁ * q₂ - p₂ * q₁) ^ 2 := by
    rw [hM]
    linear_combination (4 * (c * p₂ ^ 2 + (d - a) * p₂ * q₂ - b * q₂ ^ 2)) * hQ₁
  have hM0 : M = 0 := by
    rw [hdisc, zero_mul] at hMsq
    exact pow_eq_zero_iff (two_ne_zero) |>.1 hMsq
  have hD2 : (p₁ * q₂ - p₂ * q₁) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hc0 : c = 0 := by
    have h : c * (p₁ * q₂ - p₂ * q₁) ^ 2 = 0 := by
      rw [hM] at hM0
      linear_combination q₂ ^ 2 * hQ₁ + q₁ ^ 2 * hQ₂ - q₁ * q₂ * hM0
    exact (mul_eq_zero.1 h).resolve_right hD2
  have hb0 : b = 0 := by
    have h : b * (p₁ * q₂ - p₂ * q₁) ^ 2 = 0 := by
      rw [hM] at hM0
      linear_combination (-1 : ℝ) * (p₁ ^ 2 * hQ₂ + p₂ ^ 2 * hQ₁ - p₁ * p₂ * hM0)
    exact (mul_eq_zero.1 h).resolve_right hD2
  have hda : d - a = 0 := by
    rw [hc0, hb0] at hdisc
    have : (d - a) ^ 2 = 0 := by linear_combination hdisc
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hadd : a * a = 1 := by
    rw [hc0, hb0] at hdet
    have hd : d = a := by linarith
    rw [hd] at hdet
    linear_combination hdet
  have ha : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination hadd
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases ha with ha | ha
  · apply h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d] at * <;> first | assumption | linarith
  · apply h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d] at * <;> first | assumption | linarith

/-- Helper for **Lemma 30.3** (§30.5): the book's "因而 `γ′` 也是抛物型元素". If `F` is a `K`-q.c. homeomorphism of `ℍ`
with `F ∘ γ = δ ∘ F` and `γ = ±I` or `γ` is parabolic, then `δ` is not hyperbolic. `F` extends to a homeomorphism `G` of
`closure ℍ` in `ℂ̄` (Theorem 13.3, `thm13_3_boundary_correspondence`) with `G (γ x) = δ (G x)`
(`h36t_ext_equivariant`) and `G` maps `ℝ̂` onto `ℝ̂` (`h36t_image_extRealLine`); a parabolic `γ` has one fixed point on
`ℝ̂`, a hyperbolic `δ` has two, and `G` is a bijection between the two fixed point sets; `γ = ±I` forces `δ = ±I`
(`s27g_eq_one_of_smul_eq`). -/
theorem s30w_not_hyperbolic {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {K : ℝ}
    (hF : IsKQC (liftToC F) upperHalf K) (hγδ : ∀ τ, F (γ • τ) = δ • F τ)
    (hγ : γ = 1 ∨ γ = -1 ∨ IsParabolic γ) : ¬ IsHyperbolic δ := by
  intro hδh
  have hδt : 2 < |δ 0 0 + δ 1 1| := hδh
  have hsurj := F.surjective
  rcases hγ with h1 | h1 | hpar
  · -- `γ = 1`: `δ` fixes every point of `ℍ`, so `δ = ±1`, of trace `±2`
    have hδ : ∀ w : UpperHalfPlane, δ • w = w := by
      intro w
      obtain ⟨τ, rfl⟩ := hsurj w
      have h := hγδ τ
      rw [h1, one_smul] at h
      exact h.symm
    have := s27f_tr_pm_one (s27g_eq_one_of_smul_eq hδ)
    linarith
  · have hδ : ∀ w : UpperHalfPlane, δ • w = w := by
      intro w
      obtain ⟨τ, rfl⟩ := hsurj w
      have h := hγδ τ
      rw [h1, s27g_neg_one_smul] at h
      exact h.symm
    have := s27f_tr_pm_one (s27g_eq_one_of_smul_eq hδ)
    linarith
  · -- `γ` parabolic: the boundary map `G` carries the two fixed points of `δ` on `ℝ̂` to two fixed points of `γ`
    obtain ⟨G, hG⟩ := thm13_3_boundary_correspondence isJordanDomain_upperHalf isJordanDomain_upperHalf
      ⟨K, hF⟩ (h36q_liftToC_image F)
    obtain ⟨p₁, q₁, p₂, q₂, hQ₁, hQ₂, hD⟩ := s27g_hyp_two_fixed hδt
    have hv₁ : p₁ ≠ 0 ∨ q₁ ≠ 0 := by
      by_contra h
      push Not at h
      apply hD
      rw [h.1, h.2]
      ring
    have hv₂ : p₂ ≠ 0 ∨ q₂ ≠ 0 := by
      by_contra h
      push Not at h
      apply hD
      rw [h.1, h.2]
      ring
    obtain ⟨hw₁R, hw₁⟩ := s30w_fixed_of_vec hv₁ hQ₁
    obtain ⟨hw₂R, hw₂⟩ := s30w_fixed_of_vec hv₂ hQ₂
    have hne := s30w_ne_of_det_ne hD
    have himg := h36t_image_extRealLine hG
    have hclos : extRealLine ⊆ closure (toExt upperHalf) := h36t_extRealLine_subset_closure
    have hmaps : MapsTo (mobiusSL (slRealToComplex γ)) (closure (toExt upperHalf)) (closure (toExt upperHalf)) :=
      (MapsTo.closure (fun q hq => k24_real_mapsTo_upper γ hq) (k22_t_continuous _))
    -- the preimages are fixed points of `γ` on `ℝ̂`
    have hpre : ∀ w ∈ extRealLine, mobiusSL (slRealToComplex δ) w = w →
        ∃ u ∈ extRealLine, G u = w ∧ mobiusSL (slRealToComplex γ) u = u := by
      intro w hw hfix
      rw [← himg] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨u, hu, rfl, ?_⟩
      refine hG.2.2.1 (hmaps (hclos hu)) (hclos hu) ?_
      rw [h36t_ext_equivariant hG hγδ (hclos hu), hfix]
    obtain ⟨u₁, hu₁, hGu₁, hfu₁⟩ := hpre _ hw₁R hw₁
    obtain ⟨u₂, hu₂, hGu₂, hfu₂⟩ := hpre _ hw₂R hw₂
    have hu12 : u₁ ≠ u₂ := by
      intro h
      apply hne
      rw [← hGu₁, ← hGu₂, h]
    obtain ⟨p₁', q₁', hv₁', hQ₁', rfl⟩ := s30w_vec_of_fixed hu₁ hfu₁
    obtain ⟨p₂', q₂', hv₂', hQ₂', rfl⟩ := s30w_vec_of_fixed hu₂ hfu₂
    exact s30w_parabolic_not_two_fixed hpar hQ₁' hQ₂' (s30w_det_ne_of_ne hv₁' hv₂' hu12)

/-- **Lemma 30.3 (Wolpert)** (30.5): for a quasiconformal map `f : S₁ → S₂` of Riemann surfaces with
hyperbolic universal covering and any closed curve `α ⊆ S₁`,
`l[α]/K[f] ≤ l[f(α)] ≤ K[f] l[α]`. -/
theorem lemma30_3_wolpert {S₁ S₂ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [T2Space S₁]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [T2Space S₂]
    [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂] {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂} (hp₁ : IsUniformization Γ₁ p₁)
    (hp₂ : IsUniformization Γ₂ p₂) (f : S₁ ≃ₜ S₂) {K : ℝ} (hf : IsKQCRS f K) (α : Loop S₁) :
    freeHomotopyLength p₁ α / ENNReal.ofReal K ≤ freeHomotopyLength p₂ ⟨f α.1, α.2.map f.continuous⟩ ∧
      freeHomotopyLength p₂ ⟨f α.1, α.2.map f.continuous⟩ ≤ ENNReal.ofReal K * freeHomotopyLength p₁ α := by
  classical
  have hfree₁ := s27g_actsFreely hp₁
  have hfree₂ := s27g_actsFreely hp₂
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  -- a covering element of `α`, a lift `F` of `f` and the deck element `δ` of `F ∘ γ ∘ F⁻¹`
  obtain ⟨γ, hγ, hcov⟩ := s30a_exists_covers hp₁ α
  obtain ⟨τ₀, hτ₀⟩ := hp₁.2.2.1 α.1
  obtain ⟨τ₁, hτ₁⟩ := hp₂.2.2.1 (f α.1)
  obtain ⟨F, hF, -⟩ := exists_lift hp₁ hp₂ f τ₀ τ₁ (by rw [hτ₁, hτ₀])
  obtain ⟨δ, hδ, hFγ⟩ := h23l_deck hp₁ hp₂ hF hγ
  have hFqc : IsKQC (liftToC F) upperHalf K := h23l_lift_isKQC hp₁ hp₂ hf hF
  have hFsymm : IsLift p₂ p₁ f.symm F.symm := by
    intro τ
    have h := hF (F.symm τ)
    rw [F.apply_symm_apply] at h
    rw [h, f.symm_apply_apply]
  have hFsqc : IsKQC (liftToC F.symm) upperHalf K :=
    h23l_lift_isKQC hp₂ hp₁ (s29_m_isKQCRS_symm hf) hFsymm
  have hFγ' : ∀ τ, F.symm (δ • τ) = γ • F.symm τ := fun τ => by
    have h := hFγ (F.symm τ)
    rw [F.apply_symm_apply] at h
    rw [← h, F.symm_apply_apply]
  have hcov' : Covers p₂ δ ⟨f α.1, α.2.map f.continuous⟩ := by
    obtain ⟨c, hcc, hcp, hc1⟩ := hcov
    refine ⟨fun t => F (c t), F.continuous.comp_continuousOn hcc, fun t ht => ?_, ?_⟩
    · rw [hF, hcp t ht]
      show f (α.2.extend t) = (α.2.map f.continuous).extend t
      rw [Path.extend_apply _ ht, Path.extend_apply _ ht]
      rfl
    · show F (c 1) = δ • F (c 0)
      rw [hc1, hFγ]
  -- a non-hyperbolic element of a covering group is `±I` or parabolic
  have dich : ∀ {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}, ActsFreely Γ →
      ∀ {x : Matrix.SpecialLinearGroup (Fin 2) ℝ}, x ∈ Γ → ¬ IsHyperbolic x →
        x = 1 ∨ x = -1 ∨ IsParabolic x := by
    intro Γ hfree x hx hnh
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = -1
    · exact Or.inr (Or.inl h2)
    rcases isParabolic_or_isHyperbolic_of_actsFreely hfree hx h1 h2 with h | h
    · exact Or.inr (Or.inr h)
    · exact absurd h hnh
  -- `γ` is hyperbolic iff `δ` is (the book's "因而 γ′ 也是抛物型元素", in both directions)
  have hiff : IsHyperbolic γ ↔ IsHyperbolic δ := by
    constructor
    · intro hγh
      by_contra hδh
      exact s30w_not_hyperbolic hFsqc hFγ' (dich hfree₂ hδ hδh) hγh
    · intro hδh
      by_contra hγh
      exact s30w_not_hyperbolic hFqc hFγ (dich hfree₁ hγ hγh) hδh
  by_cases hh : IsHyperbolic γ
  · have hh' := hiff.1 hh
    have e1 := s30a_len_hyp hp₁ hγ hh hcov
    have e2 := s30a_len_hyp hp₂ hδ hh' hcov'
    have l1 : translationLength γ ≤ K * translationLength δ := s30w_translation_le hh hh' hFqc hFγ
    have l2 : translationLength δ ≤ K * translationLength γ := s30w_translation_le hh' hh hFsqc hFγ'
    rw [e1, e2]
    constructor
    · rw [ENNReal.div_le_iff (by simpa using hKpos) ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (translationLength γ) ≤ ENNReal.ofReal (K * translationLength δ) :=
            ENNReal.ofReal_le_ofReal l1
        _ = ENNReal.ofReal K * ENNReal.ofReal (translationLength δ) := ENNReal.ofReal_mul hKpos.le
        _ = ENNReal.ofReal (translationLength δ) * ENNReal.ofReal K := mul_comm _ _
    · calc ENNReal.ofReal (translationLength δ) ≤ ENNReal.ofReal (K * translationLength γ) :=
            ENNReal.ofReal_le_ofReal l2
        _ = ENNReal.ofReal K * ENNReal.ofReal (translationLength γ) := ENNReal.ofReal_mul hKpos.le
  · -- neither is hyperbolic: both lengths are `0` (`l[α] = 0` for `±I` and parabolic elements)
    have hh' : ¬ IsHyperbolic δ := fun h => hh (hiff.2 h)
    have e1 := s30a_len_zero hp₁ hγ (dich hfree₁ hγ hh) hcov
    have e2 := s30a_len_zero hp₂ hδ (dich hfree₂ hδ hh') hcov'
    rw [e1, e2]
    simp

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]


/-- §30.5: the action of `Mod(S₀)` on `T(S₀)` is discontinuous: the orbit of every point has no
limit point in `T(S₀)`. -/
def ModActionDiscontinuous (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Prop :=
  ∀ τ τ₁ : TeichSpace S₀, ¬ ∃ σ : ℕ → ModTransform S₀,
    (∀ i j, i ≠ j → ¬ ContinuousMap.Homotopic ((σ i).1 : C(S₀, S₀)) ((σ j).1 : C(S₀, S₀))) ∧
    ∃ τn : ℕ → TeichSpace S₀, (∀ n, ModAction (σ n) τ (τn n)) ∧
      Tendsto (fun n => teichDistance (τn n) τ₁) atTop (𝓝 0)

/-- The translates `γ K` (`γ ∈ Γ`) of a compact `K ⊆ ℍ` by a Fuchsian group `Γ` form a locally finite family. -/
theorem s30b_locallyFinite {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    LocallyFinite (fun γ : Γ => (fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K) := by
  intro τ
  obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds τ
  refine ⟨N, hNn, ?_⟩
  have hfin := hΓ (K ∪ N) (hK.union hNc)
  refine (hfin.preimage (Subtype.val_injective.injOn)).subset ?_
  rintro ⟨γ, hγ⟩ ⟨_, ⟨z, hz, rfl⟩, hzN⟩
  exact ⟨hγ, γ • z, ⟨z, Or.inl hz, rfl⟩, Or.inr hzN⟩

/-- **Finite generation.**  If the translates of a compact `K ⊆ ℍ` by a Fuchsian group `Γ` cover `ℍ`, then `Γ` is
generated by the finitely many `γ ∈ Γ` with `γ K ∩ K ≠ ∅`: the union `A` of the translates `γ K` with `γ` in the
generated subgroup `H` and the union `B` of the others are closed (local finiteness), disjoint and cover `ℍ`, so
`A = ℍ` by connectedness. -/
theorem s30b_generate {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hcov : ∀ z : UpperHalfPlane, ∃ γ ∈ Γ, γ • z ∈ K) :
    Γ ≤ Subgroup.closure {γ ∈ Γ | ((fun z => γ • z) '' K ∩ K).Nonempty} := by
  classical
  set H := Subgroup.closure {γ ∈ Γ | ((fun z => γ • z) '' K ∩ K).Nonempty} with hHdef
  have hLF := s30b_locallyFinite hΓ hK
  have hcl : ∀ γ : Γ, IsClosed ((fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K) := fun γ =>
    (hK.image (continuous_const_smul _)).isClosed
  set fA : Γ → Set UpperHalfPlane := fun γ =>
    if (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H then (fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K
    else ∅ with hfA
  set fB : Γ → Set UpperHalfPlane := fun γ =>
    if (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H then ∅
    else (fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K with hfB
  have hfA_of : ∀ γ : Γ, (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H →
      fA γ = (fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K := fun γ h => by
    simp only [hfA, h, ite_true]
  have hfA_not : ∀ γ : Γ, (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∉ H → fA γ = ∅ := fun γ h => by
    simp only [hfA, h, ite_false]
  have hfB_of : ∀ γ : Γ, (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∉ H →
      fB γ = (fun z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' K := fun γ h => by
    simp only [hfB, h, ite_false]
  have hfB_not : ∀ γ : Γ, (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H → fB γ = ∅ := fun γ h => by
    simp only [hfB, h, ite_true]
  set A : Set UpperHalfPlane := ⋃ γ : Γ, fA γ with hAdef
  set B : Set UpperHalfPlane := ⋃ γ : Γ, fB γ with hBdef
  have hAc : IsClosed A := by
    refine (hLF.subset fun γ => ?_).isClosed_iUnion fun γ => ?_
    · by_cases h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H
      · rw [hfA_of γ h]
      · rw [hfA_not γ h]
        exact empty_subset _
    · by_cases h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H
      · rw [hfA_of γ h]
        exact hcl γ
      · rw [hfA_not γ h]
        exact isClosed_empty
  have hBc : IsClosed B := by
    refine (hLF.subset fun γ => ?_).isClosed_iUnion fun γ => ?_
    · by_cases h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H
      · rw [hfB_not γ h]
        exact empty_subset _
      · rw [hfB_of γ h]
    · by_cases h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H
      · rw [hfB_not γ h]
        exact isClosed_empty
      · rw [hfB_of γ h]
        exact hcl γ
  have hcover : ∀ τ, τ ∈ A ∨ τ ∈ B := by
    intro τ
    obtain ⟨γ, hγ, hγτ⟩ := hcov τ
    have hmem : γ⁻¹ ∈ Γ := Γ.inv_mem hγ
    have himg : τ ∈ (fun z => γ⁻¹ • z) '' K := ⟨γ • τ, hγτ, inv_smul_smul γ τ⟩
    by_cases hH : γ⁻¹ ∈ H
    · left
      refine mem_iUnion.2 ⟨⟨γ⁻¹, hmem⟩, ?_⟩
      rw [hfA_of ⟨γ⁻¹, hmem⟩ hH]
      exact himg
    · right
      refine mem_iUnion.2 ⟨⟨γ⁻¹, hmem⟩, ?_⟩
      rw [hfB_of ⟨γ⁻¹, hmem⟩ hH]
      exact himg
  have hdisj : ∀ τ, τ ∈ A → τ ∈ B → False := by
    intro τ hA hB
    obtain ⟨⟨h, hhΓ⟩, hh⟩ := mem_iUnion.1 hA
    obtain ⟨⟨γ, hγΓ⟩, hγ⟩ := mem_iUnion.1 hB
    by_cases hhH : h ∈ H
    · by_cases hγH : γ ∈ H
      · rw [hfB_not ⟨γ, hγΓ⟩ hγH] at hγ
        exact hγ
      · rw [hfA_of ⟨h, hhΓ⟩ hhH] at hh
        rw [hfB_of ⟨γ, hγΓ⟩ hγH] at hγ
        obtain ⟨a, ha, rfl⟩ := hh
        obtain ⟨b, hb, hba⟩ := hγ
        have hE : h⁻¹ * γ ∈ H := by
          refine Subgroup.subset_closure ⟨Γ.mul_mem (Γ.inv_mem hhΓ) hγΓ, (h⁻¹ * γ) • b, ⟨b, hb, rfl⟩, ?_⟩
          rw [mul_smul]
          simp only at hba
          rw [hba, inv_smul_smul]
          exact ha
        apply hγH
        have : γ = h * (h⁻¹ * γ) := by group
        rw [this]
        exact H.mul_mem hhH hE
    · rw [hfA_not ⟨h, hhΓ⟩ hhH] at hh
      exact hh
  have hAo : IsOpen A := by
    have : A = Bᶜ := by
      ext τ
      constructor
      · intro hA hB
        exact hdisj τ hA hB
      · intro hB
        rcases hcover τ with h | h
        · exact h
        · exact absurd h hB
    rw [this]
    exact hBc.isOpen_compl
  have hKne : K.Nonempty := by
    obtain ⟨γ, -, hγ⟩ := hcov UpperHalfPlane.I
    exact ⟨_, hγ⟩
  have hKA : K ⊆ A := by
    intro z hz
    refine mem_iUnion.2 ⟨⟨1, Γ.one_mem⟩, ?_⟩
    rw [hfA_of ⟨1, Γ.one_mem⟩ H.one_mem]
    exact ⟨z, hz, one_smul _ z⟩
  have hAuniv : A = univ := by
    rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h | h
    · obtain ⟨z, hz⟩ := hKne
      have := hKA hz
      rw [h] at this
      exact absurd this (notMem_empty z)
    · exact h
  intro γ hγ
  by_contra hγH
  obtain ⟨z, hz⟩ := hKne
  have hB : γ • z ∈ B := by
    refine mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
    rw [hfB_of ⟨γ, hγ⟩ hγH]
    exact ⟨z, hz, rfl⟩
  exact hdisj _ (by rw [hAuniv]; exact mem_univ _) hB

/-- Conjugations `F₁ x F₁⁻¹`, `F₂ x F₂⁻¹` agreeing for `x` in a set `S` agree on the subgroup generated by `S`. -/
theorem s30b_agree_closure {S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hgen : ∀ x ∈ S, ∀ τ, F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ)) :
    ∀ x ∈ Subgroup.closure S, ∀ τ, F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
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

/-- `liftToC F` maps `ℍ` into `ℍ`. -/
theorem s30b_liftToC_mem {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {w : ℂ} (hw : w ∈ upperHalf) :
    liftToC F w ∈ upperHalf := by
  have h := h23l_liftToC_coe F ⟨w, hw⟩
  have e : ((⟨w, hw⟩ : UpperHalfPlane) : ℂ) = w := rfl
  rw [e] at h
  show 0 < (liftToC F w).im
  rw [h]
  exact (F _).im_pos

/-- The Cayley conjugate `C ∘ F ∘ C⁻¹` of a `K`-q.c. lift `F` is a `K`-q.c. self-map of `Δ`. -/
theorem s30b_disc_conj {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {K : ℝ} (hF : IsKQC (liftToC F) upperHalf K) :
    IsKQC (cayley ∘ (liftToC F ∘ cayleyInv)) unitDisc K ∧
      ∀ z ∈ unitDisc, (cayley ∘ (liftToC F ∘ cayleyInv)) z ∈ unitDisc := by
  have h1 : IsKQC cayleyInv unitDisc 1 := isKQC_one_of_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
  have h2 : IsKQC (liftToC F ∘ cayleyInv) unitDisc (1 * K) :=
    thm7_1_comp h1 hF (by rw [s35a_x_isConformalOnto_cayleyInv.2.2])
  have h3 : IsKQC cayley upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley
  have himg : (liftToC F ∘ cayleyInv) '' unitDisc ⊆ upperHalf := by
    rintro _ ⟨z, hz, rfl⟩
    exact s30b_liftToC_mem (cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hz))
  have h4 := thm7_1_comp h2 h3 himg
  rw [one_mul, mul_one] at h4
  refine ⟨h4, fun z hz => cayley_mem_unitDisc ?_⟩
  exact himg ⟨z, hz, rfl⟩

/-- `C⁻¹(0) = i`. -/
theorem s30b_cayleyInv_zero : cayleyInv 0 = Complex.I := by
  simp [cayleyInv]

/-- The lift is recovered from its Cayley conjugate. -/
theorem s30b_recover (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (τ : UpperHalfPlane) :
    cayleyInv ((cayley ∘ (liftToC F ∘ cayleyInv)) (cayley (τ : ℂ))) = (F τ : ℂ) := by
  simp only [Function.comp_apply]
  rw [cayleyInv_cayley τ.im_pos, h23l_liftToC_coe, cayleyInv_cayley (F τ).im_pos]

/-- The Cayley conjugate of `F⁻¹` inverts the Cayley conjugate of `F` on `Δ`. -/
theorem s30b_conj_symm (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {z : ℂ} (hz : z ∈ unitDisc) :
    (cayley ∘ (liftToC F.symm ∘ cayleyInv)) ((cayley ∘ (liftToC F ∘ cayleyInv)) z) = z := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set τ : UpperHalfPlane := ⟨cayleyInv z, cayleyInv_mem_upperHalf hz'⟩ with hτ
  have e1 : cayleyInv z = (τ : ℂ) := rfl
  simp only [Function.comp_apply]
  rw [e1, h23l_liftToC_coe, cayleyInv_cayley (F τ).im_pos, h23l_liftToC_coe, F.symm_apply_apply, ← e1,
    cayley_cayleyInv hz']

/-- A locally uniformly convergent sequence converges locally uniformly along every sequence of indices tending to
`∞`. -/
theorem s30b_tlu_comp {Φ : ℕ → ℂ → ℂ} {Φl : ℂ → ℂ} {D : Set ℂ} (h : TendstoLocallyUniformlyOn Φ Φl atTop D)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) : TendstoLocallyUniformlyOn (fun n => Φ (φ n)) Φl atTop D := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hφ.eventually hev⟩

/-- A locally uniform limit of `K`-q.c. self-maps of `Δ` is constant on `Δ`, or it is `K`-q.c. on `Δ` and maps `Δ`
into `Δ` (Theorem 8.2; the image is open inside the closed disc). -/
theorem s30b_limit_cases {Φ : ℕ → ℂ → ℂ} {Φl : ℂ → ℂ} {K : ℝ} (hqc : ∀ n, IsKQC (Φ n) unitDisc K)
    (hmaps : ∀ n, ∀ z ∈ unitDisc, Φ n z ∈ unitDisc) (hlim : TendstoLocallyUniformlyOn Φ Φl atTop unitDisc) :
    (∃ c : ℂ, ∀ z ∈ unitDisc, Φl z = c) ∨ (IsKQC Φl unitDisc K ∧ ∀ z ∈ unitDisc, Φl z ∈ unitDisc) := by
  have hcb : ∀ z ∈ unitDisc, Φl z ∈ closedBall (0 : ℂ) 1 := fun z hz =>
    isClosed_closedBall.mem_of_tendsto (hlim.tendsto_at hz)
      (Eventually.of_forall fun n => ball_subset_closedBall (hmaps n z hz))
  rcases thm8_2_limit (D := unitDisc) Metric.isBounded_ball (isConnected_ball one_pos) hqc hlim with h | hq
  · exact Or.inl h
  · refine Or.inr ⟨hq, ?_⟩
    have hopen := isOpen_image_of_isKQC hq
    have hsub : Φl '' unitDisc ⊆ interior (closedBall (0 : ℂ) 1) :=
      hopen.subset_interior_iff.2 (by rintro _ ⟨z, hz, rfl⟩; exact hcb z hz)
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at hsub
    intro z hz
    exact hsub ⟨z, hz, rfl⟩

/-- A locally uniform limit of `K`-q.c. self-maps of `Δ` whose values at `0` stay in a compact subset of `Δ` maps
`Δ` into `Δ`. -/
theorem s30b_limit_mapsTo {Φ : ℕ → ℂ → ℂ} {Φl : ℂ → ℂ} {K : ℝ} (hqc : ∀ n, IsKQC (Φ n) unitDisc K)
    (hmaps : ∀ n, ∀ z ∈ unitDisc, Φ n z ∈ unitDisc) (hlim : TendstoLocallyUniformlyOn Φ Φl atTop unitDisc)
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ unitDisc) (h0 : ∀ n, Φ n 0 ∈ C) :
    ∀ z ∈ unitDisc, Φl z ∈ unitDisc := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hl0 : Φl 0 ∈ C := hC.isClosed.mem_of_tendsto (hlim.tendsto_at h0D) (Eventually.of_forall h0)
  rcases s30b_limit_cases hqc hmaps hlim with ⟨c, hc⟩ | ⟨-, h⟩
  · intro z hz
    rw [hc z hz, ← hc 0 h0D]
    exact hCD hl0
  · exact h

/-- A map that is `K`-q.c. on `D` for every `K > 1` is `1`-q.c. on `D` (the image quadrilateral is unique). -/
theorem s30b_isKQC_one_of_forall {f : ℂ → ℂ} {D : Set ℂ} (h : ∀ K : ℝ, 1 < K → IsKQC f D K) :
    IsKQC f D 1 := by
  obtain ⟨hD, -, hhom, hmod⟩ := h 2 one_lt_two
  refine ⟨hD, le_rfl, hhom, fun Q hQ => ?_⟩
  obtain ⟨Q', hQ', -⟩ := hmod Q hQ
  refine ⟨Q', hQ', ?_⟩
  rw [one_mul]
  have hQpos := modulus_pos Q
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hK : 1 < 1 + ε / Q.modulus := by
    have := div_pos hε hQpos
    linarith
  obtain ⟨Q'', hQ'', hle⟩ := (h _ hK).2.2.2 Q hQ
  rw [hQ''.unique hQ'] at hle
  calc Q'.modulus ≤ (1 + ε / Q.modulus) * Q.modulus := hle
    _ = Q.modulus + ε := by rw [add_mul, one_mul, div_mul_cancel₀ _ hQpos.ne']

/-- **Descent.**  A homeomorphism `F` of `ℍ` conjugating `Γ_X` into `Γ_Y` and whose inverse conjugates `Γ_Y` into
`Γ_X` (elementwise, as maps of `ℍ`) is the lift of a homeomorphism `X → Y`. -/
theorem s30b_descend {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (h₁ : ∀ γ ∈ ΓX, ∃ δ ∈ ΓY, ∀ τ, F (γ • τ) = δ • F τ)
    (h₂ : ∀ δ ∈ ΓY, ∃ γ ∈ ΓX, ∀ τ, F.symm (δ • τ) = γ • F.symm τ) :
    ∃ c : X ≃ₜ Y, IsLift pX pY c F := by
  obtain ⟨H₁, hH₁⟩ := h23l_homotopy_descend (Ht := fun τ (_ : unitInterval) => F τ) hX hY
    (F.continuous.comp continuous_fst) (fun γ hγ => by
      obtain ⟨δ, hδ, h⟩ := h₁ γ hγ
      exact ⟨δ, hδ, fun τ _ => h τ⟩)
  obtain ⟨H₂, hH₂⟩ := h23l_homotopy_descend (Ht := fun τ (_ : unitInterval) => F.symm τ) hY hX
    (F.symm.continuous.comp continuous_fst) (fun δ hδ => by
      obtain ⟨γ, hγ, h⟩ := h₂ δ hδ
      exact ⟨γ, hγ, fun τ _ => h τ⟩)
  have e₁ : ∀ τ, H₁ (0, pX τ) = pY (F τ) := fun τ => hH₁ 0 τ
  have e₂ : ∀ τ, H₂ (0, pY τ) = pX (F.symm τ) := fun τ => hH₂ 0 τ
  have hl : Function.LeftInverse (fun y => H₂ (0, y)) (fun x => H₁ (0, x)) := by
    intro x
    obtain ⟨τ, rfl⟩ := hX.2.2.1 x
    simp only
    rw [e₁, e₂, F.symm_apply_apply]
  have hr : Function.RightInverse (fun y => H₂ (0, y)) (fun x => H₁ (0, x)) := by
    intro y
    obtain ⟨τ, rfl⟩ := hY.2.2.1 y
    simp only
    rw [e₂, e₁, F.apply_symm_apply]
  refine ⟨⟨⟨fun x => H₁ (0, x), fun y => H₂ (0, y), hl, hr⟩,
    H₁.continuous.comp (continuous_const.prodMk continuous_id),
    H₂.continuous.comp (continuous_const.prodMk continuous_id)⟩, fun τ => (e₁ τ).symm⟩

/-- **The conformal limit.**  Let `G n : X → Y` be `K n`-q.c. homeomorphisms of closed surfaces `X = ℍ/Γ_X`,
`Y = ℍ/Γ_Y` with `K n → 1`.  Then some `G n` is homotopic to a homeomorphism `c : X → Y` whose lift to `ℍ` is a
Möbius map `A ∈ SL(2, ℝ)`.

Normalized lifts `F n` and their inverses, conjugated to `Δ` by the Cayley map, have locally uniform subsequential
limits `Φ`, `Ψ` (Theorem 8.1).  `Φ` maps `Δ` into `Δ` by the normalization, and `Ψ ∘ Φ = id`, so neither limit is
constant; both are q.c. (Theorem 8.2), `Φ ∘ Ψ = id`, and `Φ` is `K'`-q.c. for every `K' > 1`, hence `1`-q.c.: the
limit lift is Möbius.  On the finite generating set of `Γ_X` the deck elements of the `F n` take finitely many
values; along a value taken infinitely often the limit has the deck elements of some `F n`, so it descends to `c`,
and Theorem 23.1 gives `c ≃ G n`. -/
theorem s30b_conformal_limit {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [T2Space Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    (G : ℕ → X ≃ₜ Y) (K : ℕ → ℝ) (hG : ∀ n, IsKQCRS (G n) (K n)) (hK : Tendsto K atTop (𝓝 1)) :
    ∃ n, ∃ c : X ≃ₜ Y, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ τ, pY (A • τ) = c (pX τ)) ∧
      ContinuousMap.Homotopic (c : C(X, Y)) (G n : C(X, Y)) := by
  classical
  obtain ⟨K₀, hK₀⟩ := hK.bddAbove_range
  have hKle : ∀ n, K n ≤ K₀ := fun n => hK₀ ⟨n, rfl⟩
  obtain ⟨KX, hKX, hcovX⟩ := utm_exists_compact_translate hX
  obtain ⟨KY, hKY, hcovY⟩ := utm_exists_compact_translate hY
  -- normalized lifts
  have hlift : ∀ n, ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, IsLift pX pY (G n) F ∧
      F UpperHalfPlane.I ∈ KY := by
    intro n
    obtain ⟨τ₁, hτ₁⟩ := hY.2.2.1 (G n (pX UpperHalfPlane.I))
    obtain ⟨δ, hδ, hδK⟩ := hcovY τ₁
    have hp : pY (δ • τ₁) = G n (pX UpperHalfPlane.I) := by
      rw [← hτ₁]
      exact ((hY.2.2.2 τ₁ (δ • τ₁)).2 ⟨δ, hδ, rfl⟩).symm
    obtain ⟨F, hF, hF0⟩ := exists_lift hX hY (G n) UpperHalfPlane.I (δ • τ₁) hp
    exact ⟨F, hF, hF0 ▸ hδK⟩
  choose F hF hFK using hlift
  have hFqc : ∀ n, IsKQC (liftToC (F n)) upperHalf (K n) := fun n => h23l_lift_isKQC hX hY (hG n) (hF n)
  have hFqc' : ∀ n, IsKQC (liftToC (F n).symm) upperHalf (K n) := fun n =>
    h23l_lift_isKQC hY hX (s29_m_isKQCRS_symm (hG n)) (s27g_isLift_symm (hF n))
  -- Cayley conjugates of the lifts and of their inverses
  set Φ : ℕ → ℂ → ℂ := fun n => cayley ∘ (liftToC (F n) ∘ cayleyInv) with hΦ
  set Ψ : ℕ → ℂ → ℂ := fun n => cayley ∘ (liftToC (F n).symm ∘ cayleyInv) with hΨ
  have hΦqc : ∀ n, IsKQC (Φ n) unitDisc (K n) := fun n => (s30b_disc_conj (hFqc n)).1
  have hΨqc : ∀ n, IsKQC (Ψ n) unitDisc (K n) := fun n => (s30b_disc_conj (hFqc' n)).1
  have hΦmaps : ∀ n, ∀ z ∈ unitDisc, Φ n z ∈ unitDisc := fun n => (s30b_disc_conj (hFqc n)).2
  have hΨmaps : ∀ n, ∀ z ∈ unitDisc, Ψ n z ∈ unitDisc := fun n => (s30b_disc_conj (hFqc' n)).2
  have hΨΦ : ∀ n, ∀ z ∈ unitDisc, Ψ n (Φ n z) = z := fun n z hz => s30b_conj_symm (F n) hz
  have hΦΨ : ∀ n, ∀ z ∈ unitDisc, Φ n (Ψ n z) = z := fun n z hz => by
    have h := s30b_conj_symm (F n).symm hz
    rwa [Homeomorph.symm_symm] at h
  have hΦqc₀ : ∀ n, IsKQC (Φ n) unitDisc K₀ := fun n => (hΦqc n).mono (hKle n)
  have hΨqc₀ : ∀ n, IsKQC (Ψ n) unitDisc K₀ := fun n => (hΨqc n).mono (hKle n)
  have hΦbd : ∀ n, ∀ z ∈ unitDisc, ‖Φ n z‖ ≤ 1 := fun n z hz => (mem_ball_zero_iff.mp (hΦmaps n z hz)).le
  have hΨbd : ∀ n, ∀ z ∈ unitDisc, ‖Ψ n z‖ ≤ 1 := fun n z hz => (mem_ball_zero_iff.mp (hΨmaps n z hz)).le
  -- a common convergent subsequence
  obtain ⟨φ₁, hφ₁, Φl, hlimΦ₁⟩ := thm8_1_normal_family (D := unitDisc) Metric.isBounded_ball
    (isConnected_ball one_pos) hΦqc₀ hΦbd
  obtain ⟨φ₂, hφ₂, Ψl, hlimΨ₂⟩ := thm8_1_normal_family (D := unitDisc) Metric.isBounded_ball
    (isConnected_ball one_pos) (fun n => hΨqc₀ (φ₁ n)) (fun n => hΨbd (φ₁ n))
  set φ : ℕ → ℕ := fun n => φ₁ (φ₂ n) with hφdef
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hlimΦ : TendstoLocallyUniformlyOn (fun n => Φ (φ n)) Φl atTop unitDisc :=
    s30b_tlu_comp hlimΦ₁ hφ₂.tendsto_atTop
  have hlimΨ : TendstoLocallyUniformlyOn (fun n => Ψ (φ n)) Ψl atTop unitDisc := hlimΨ₂
  have hΦlc : ContinuousOn Φl unitDisc :=
    hlimΦ.continuousOn (Eventually.of_forall fun n => (hΦqc₀ (φ n)).2.2.1.1).frequently
  have hΨlc : ContinuousOn Ψl unitDisc :=
    hlimΨ.continuousOn (Eventually.of_forall fun n => (hΨqc₀ (φ n)).2.2.1.1).frequently
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h12D : ((1 : ℂ) / 2) ∈ unitDisc := by
    show ((1 : ℂ) / 2) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    norm_num
  -- `Φl` maps `Δ` into `Δ` (the values at `0` stay in the compact `C(K_Y)`)
  set C₀ : Set ℂ := (fun τ : UpperHalfPlane => cayley (τ : ℂ)) '' KY with hC₀
  have hcayc : Continuous (fun τ : UpperHalfPlane => cayley (τ : ℂ)) := by
    have : (fun τ : UpperHalfPlane => cayley (τ : ℂ)) =
        fun τ : UpperHalfPlane => ((τ : ℂ) - Complex.I) / ((τ : ℂ) + Complex.I) := rfl
    rw [this]
    exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.add continuous_const) fun τ => cayley_den_ne_zero τ.im_pos
  have hC₀c : IsCompact C₀ := hKY.image hcayc
  have hC₀D : C₀ ⊆ unitDisc := by
    rintro _ ⟨τ, -, rfl⟩
    exact cayley_mem_unitDisc τ.im_pos
  have hΦ0 : ∀ n, Φ n 0 = cayley (F n UpperHalfPlane.I : ℂ) := by
    intro n
    simp only [hΦ, Function.comp_apply, s30b_cayleyInv_zero]
    rw [← UpperHalfPlane.coe_I, h23l_liftToC_coe]
  have hΦlD : ∀ z ∈ unitDisc, Φl z ∈ unitDisc :=
    s30b_limit_mapsTo (fun n => hΦqc₀ (φ n)) (fun n => hΦmaps (φ n)) hlimΦ hC₀c hC₀D
      (fun n => by rw [hΦ0]; exact ⟨_, hFK (φ n), rfl⟩)
  -- `Ψl ∘ Φl = id` on `Δ`, so neither limit is constant
  have hΨΦl : ∀ z ∈ unitDisc, Ψl (Φl z) = z := by
    intro z hz
    have h1 : Tendsto (fun n => Ψ (φ n) (Φ (φ n) z)) atTop (𝓝 (Ψl (Φl z))) :=
      hlimΨ.tendsto_comp (hΨlc _ (hΦlD z hz)) (hΦlD z hz)
        (tendsto_nhdsWithin_iff.2 ⟨hlimΦ.tendsto_at hz, Eventually.of_forall fun n => hΦmaps _ z hz⟩)
    have h2 : (fun n => Ψ (φ n) (Φ (φ n) z)) = fun _ => z := funext fun n => hΨΦ (φ n) z hz
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hne : ∀ c : ℂ, ¬ ∀ z ∈ unitDisc, Φl z = c := by
    intro c hc
    have h0 := hΨΦl 0 h0D
    have h1 := hΨΦl _ h12D
    rw [hc 0 h0D] at h0
    rw [hc _ h12D, h0] at h1
    norm_num at h1
  have hΨl : IsKQC Ψl unitDisc K₀ ∧ ∀ z ∈ unitDisc, Ψl z ∈ unitDisc := by
    rcases s30b_limit_cases (fun n => hΨqc₀ (φ n)) (fun n => hΨmaps (φ n)) hlimΨ with ⟨c, hc⟩ | h
    · exfalso
      have h0 := hΨΦl 0 h0D
      have h1 := hΨΦl _ h12D
      rw [hc _ (hΦlD 0 h0D)] at h0
      rw [hc _ (hΦlD _ h12D), h0] at h1
      norm_num at h1
    · exact h
  have hΦΨl : ∀ z ∈ unitDisc, Φl (Ψl z) = z := by
    intro z hz
    have h1 : Tendsto (fun n => Φ (φ n) (Ψ (φ n) z)) atTop (𝓝 (Φl (Ψl z))) :=
      hlimΦ.tendsto_comp (hΦlc _ (hΨl.2 z hz)) (hΨl.2 z hz)
        (tendsto_nhdsWithin_iff.2 ⟨hlimΨ.tendsto_at hz, Eventually.of_forall fun n => hΨmaps _ z hz⟩)
    have h2 : (fun n => Φ (φ n) (Ψ (φ n) z)) = fun _ => z := funext fun n => hΦΨ (φ n) z hz
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- `Φl` is `K'`-q.c. for every `K' > 1`, hence `1`-q.c.
  have hΦl1 : IsKQC Φl unitDisc 1 := by
    refine s30b_isKQC_one_of_forall fun K' hK' => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hK.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hK'))
    have hq : ∀ n, IsKQC (Φ (φ (n + N))) unitDisc K' := fun n =>
      (hΦqc (φ (n + N))).mono (hN (n + N) (Nat.le_add_left N n)).le
    have hl : TendstoLocallyUniformlyOn (fun n => Φ (φ (n + N))) Φl atTop unitDisc :=
      s30b_tlu_comp hlimΦ (tendsto_add_atTop_nat N)
    rcases thm8_2_limit (D := unitDisc) Metric.isBounded_ball (isConnected_ball one_pos) hq hl with
      ⟨c, hc⟩ | h
    · exact absurd hc (hne c)
    · exact h
  -- the limit lift `F∞ = C⁻¹ ∘ Φl ∘ C`, a homeomorphism of `ℍ` with inverse `C⁻¹ ∘ Ψl ∘ C`
  have hΦlH : ∀ τ : UpperHalfPlane, 0 < (cayleyInv (Φl (cayley (τ : ℂ)))).im := fun τ =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp (hΦlD _ (cayley_mem_unitDisc τ.im_pos)))
  have hΨlH : ∀ τ : UpperHalfPlane, 0 < (cayleyInv (Ψl (cayley (τ : ℂ)))).im := fun τ =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp (hΨl.2 _ (cayley_mem_unitDisc τ.im_pos)))
  have hciD : ContinuousOn cayleyInv unitDisc := differentiableOn_cayleyInv.continuousOn
  have hFc : Continuous (fun τ : UpperHalfPlane => (⟨cayleyInv (Φl (cayley (τ : ℂ))), hΦlH τ⟩ : UpperHalfPlane)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.2 (hciD.comp_continuous (hΦlc.comp_continuous hcayc
      fun τ => cayley_mem_unitDisc τ.im_pos) fun τ => hΦlD _ (cayley_mem_unitDisc τ.im_pos))
  have hGc : Continuous (fun τ : UpperHalfPlane => (⟨cayleyInv (Ψl (cayley (τ : ℂ))), hΨlH τ⟩ : UpperHalfPlane)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.2 (hciD.comp_continuous (hΨlc.comp_continuous hcayc
      fun τ => cayley_mem_unitDisc τ.im_pos) fun τ => hΨl.2 _ (cayley_mem_unitDisc τ.im_pos))
  let Finf : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    { toFun := fun τ => ⟨cayleyInv (Φl (cayley (τ : ℂ))), hΦlH τ⟩
      invFun := fun τ => ⟨cayleyInv (Ψl (cayley (τ : ℂ))), hΨlH τ⟩
      left_inv := fun τ => by
        apply UpperHalfPlane.ext
        show cayleyInv (Ψl (cayley (cayleyInv (Φl (cayley (τ : ℂ)))))) = τ
        rw [cayley_cayleyInv (mem_ball_zero_iff.mp (hΦlD _ (cayley_mem_unitDisc τ.im_pos))),
          hΨΦl _ (cayley_mem_unitDisc τ.im_pos), cayleyInv_cayley τ.im_pos]
      right_inv := fun τ => by
        apply UpperHalfPlane.ext
        show cayleyInv (Φl (cayley (cayleyInv (Ψl (cayley (τ : ℂ)))))) = τ
        rw [cayley_cayleyInv (mem_ball_zero_iff.mp (hΨl.2 _ (cayley_mem_unitDisc τ.im_pos))),
          hΦΨl _ (cayley_mem_unitDisc τ.im_pos), cayleyInv_cayley τ.im_pos]
      continuous_toFun := hFc
      continuous_invFun := hGc }
  have hFinf1 : IsKQC (liftToC Finf) upperHalf 1 := by
    have h1 : IsKQC cayley upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley
    have h2 : IsKQC cayleyInv unitDisc 1 := isKQC_one_of_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
    have h3 := thm7_1_comp h1 hΦl1 (by rintro _ ⟨z, hz, rfl⟩; exact cayley_mem_unitDisc hz)
    have h4 := thm7_1_comp h3 h2 (by rintro _ ⟨z, hz, rfl⟩; exact hΦlD _ (cayley_mem_unitDisc hz))
    simp only [mul_one] at h4
    refine ad_isKQC_congr h4 fun z hz => ?_
    have hz' : 0 < z.im := hz
    rw [h23l_liftToC_eq Finf hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    rfl
  obtain ⟨A, hA⟩ := utm_eq_smul_of_isKQC_one Finf hFinf1
  -- the lifts converge pointwise to `F∞`
  have hconv : ∀ τ : UpperHalfPlane, Tendsto (fun n => F (φ n) τ) atTop (𝓝 (Finf τ)) := by
    intro τ
    have hτD : cayley (τ : ℂ) ∈ unitDisc := cayley_mem_unitDisc τ.im_pos
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    have hci : ContinuousAt cayleyInv (Φl (cayley (τ : ℂ))) :=
      (differentiableOn_cayleyInv.differentiableAt (isOpen_ball.mem_nhds (hΦlD _ hτD))).continuousAt
    have h1 := hci.tendsto.comp (hlimΦ.tendsto_at hτD)
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply]
    exact s30b_recover (F (φ n)) τ
  -- the finite generating set `E` of `Γ_X` and the deck elements of the lifts on it
  set E : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {γ ∈ ΓX | ((fun z => γ • z) '' KX ∩ KX).Nonempty}
    with hEdef
  have hEfin : E.Finite := utm_x2_isFuchsian hX KX hKX
  have hgen := s30b_generate (utm_x2_isFuchsian hX) hKX hcovX
  set C : Set UpperHalfPlane := KY ∪ ⋃ γ ∈ E, insert (Finf (γ • UpperHalfPlane.I))
    (range fun n => F (φ n) (γ • UpperHalfPlane.I)) with hCdef
  have hCc : IsCompact C :=
    hKY.union (hEfin.isCompact_biUnion fun γ _ => (hconv (γ • UpperHalfPlane.I)).isCompact_insert_range)
  have hdeck : ∀ n, ∀ γ ∈ ΓX, ∃ δ ∈ ΓY, ∀ τ, F n (γ • τ) = δ • F n τ :=
    fun n γ hγ => h23l_deck hX hY (hF n) hγ
  choose δ hδΓ hδ using hdeck
  set Fin' : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {d ∈ ΓY | ((fun z => d • z) '' C ∩ C).Nonempty}
    with hFindef
  have hFinfin : Fin'.Finite := utm_x2_isFuchsian hY C hCc
  have hmemFin : ∀ n, ∀ e : E, δ (φ n) e.1 e.2.1 ∈ Fin' := by
    intro n e
    refine ⟨hδΓ _ _ _, δ (φ n) e.1 e.2.1 • F (φ n) UpperHalfPlane.I,
      ⟨F (φ n) UpperHalfPlane.I, Or.inl (hFK _), rfl⟩, ?_⟩
    rw [← hδ]
    refine Or.inr (mem_iUnion₂.2 ⟨e.1, e.2, ?_⟩)
    exact mem_insert_of_mem _ ⟨n, rfl⟩
  have : Finite E := hEfin.to_subtype
  have : Finite Fin' := hFinfin.to_subtype
  -- a value of the deck elements on `E` taken infinitely often
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber
    (fun n : ℕ => fun e : E => (⟨δ (φ n) e.1 e.2.1, hmemFin n e⟩ : Fin'))
  set Sv : Set ℕ := (fun n : ℕ => fun e : E => (⟨δ (φ n) e.1 e.2.1, hmemFin n e⟩ : Fin')) ⁻¹' {v} with hSv
  have hSinf : Sv.Infinite := Set.infinite_coe_iff.1 hv
  have hSmem : ∀ n ∈ Sv, ∀ x (hx : x ∈ E), δ (φ n) x hx.1 = (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    fun n hn x hx => congrArg Subtype.val (congrFun (Set.mem_singleton_iff.1 hn) ⟨x, hx⟩)
  have hSne : (atTop ⊓ 𝓟 Sv).NeBot := by
    have h := frequently_iff_neBot.1 ((Nat.frequently_atTop_iff_infinite (p := fun n => n ∈ Sv)).2 hSinf)
    rwa [Set.ofPred_mem_eq] at h
  have hSev : ∀ᶠ n in atTop ⊓ 𝓟 Sv, n ∈ Sv := mem_inf_of_right (mem_principal_self Sv)
  -- along that value, `F∞` has the same deck elements on `E`
  have hlimE : ∀ x (hx : x ∈ E), ∀ τ, Finf (x • τ) = (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • Finf τ := by
    intro x hx τ
    have h1 : Tendsto (fun n => F (φ n) (x • τ)) (atTop ⊓ 𝓟 Sv) (𝓝 (Finf (x • τ))) :=
      (hconv _).mono_left inf_le_left
    have h2 : Tendsto (fun n => (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F (φ n) τ) (atTop ⊓ 𝓟 Sv)
        (𝓝 ((v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • Finf τ)) :=
      ((continuous_const_smul _).tendsto _).comp ((hconv τ).mono_left inf_le_left)
    have h3 : (fun n => F (φ n) (x • τ)) =ᶠ[atTop ⊓ 𝓟 Sv]
        fun n => (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F (φ n) τ := by
      filter_upwards [hSev] with n hn
      rw [hδ (φ n) x hx.1, hSmem n hn x hx]
    exact tendsto_nhds_unique (h1.congr' h3) h2
  obtain ⟨n₀, hn₀⟩ := hSinf.nonempty
  have hagE : ∀ x ∈ E, ∀ τ, Finf (x • Finf.symm τ) = F (φ n₀) (x • (F (φ n₀)).symm τ) := by
    intro x hx τ
    rw [hlimE x hx, hδ (φ n₀) x hx.1, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      hSmem n₀ hn₀ x hx]
  have hag := s30b_agree_closure hagE
  -- `F∞` descends to `c : X → Y`
  have hdeckI : ∀ γ ∈ ΓX, ∃ d ∈ ΓY, ∀ τ, Finf (γ • τ) = d • Finf τ := by
    intro γ hγ
    obtain ⟨d, hd, h⟩ := h23l_deck hX hY (hF (φ n₀)) hγ
    refine ⟨d, hd, fun τ => ?_⟩
    have e := hag γ (hgen hγ) (Finf τ)
    rw [Homeomorph.symm_apply_apply, h, Homeomorph.apply_symm_apply] at e
    exact e
  have hdeckI' : ∀ d ∈ ΓY, ∃ γ ∈ ΓX, ∀ τ, Finf.symm (d • τ) = γ • Finf.symm τ := by
    intro d hd
    obtain ⟨γ, hγ, h⟩ := h23l_deck hY hX (s27g_isLift_symm (hF (φ n₀))) hd
    refine ⟨γ, hγ, fun τ => ?_⟩
    have e := hag γ (hgen hγ) τ
    have h' : F (φ n₀) (γ • (F (φ n₀)).symm τ) = d • τ := by
      rw [← h, Homeomorph.apply_symm_apply]
    rw [h'] at e
    rw [← e, Homeomorph.symm_apply_apply]
  obtain ⟨c, hc⟩ := s30b_descend hX hY Finf hdeckI hdeckI'
  -- Theorem 23.1: `c ≃ G (φ n₀)`
  have hhom : ContinuousMap.Homotopic (c : C(X, Y)) (G (φ n₀) : C(X, Y)) := by
    refine (thm23_1_homotopy_iff hX hY c (G (φ n₀)) hc (hF (φ n₀))).2 ⟨1, ΓY.one_mem, fun γ hγ τ => ?_⟩
    rw [inv_one, one_smul, one_smul]
    exact hag γ (hgen hγ) τ
  exact ⟨φ n₀, c, A, fun τ => by rw [← hA, hc], hhom⟩

/-- Pointwise equal loops are freely homotopic. -/
theorem s30b_fh_of_eq {Z : Type*} [TopologicalSpace Z] {α β : Loop Z} (h : ∀ t, α.2 t = β.2 t) :
    FreelyHomotopic α β :=
  ⟨⟨fun x => α.2 x.2, α.2.continuous.comp continuous_snd⟩, fun t => rfl, fun t => h t,
    fun s => by simp⟩

/-- Free homotopy is symmetric. -/
theorem s30b_fh_symm {Z : Type*} [TopologicalSpace Z] {α β : Loop Z} (h : FreelyHomotopic α β) :
    FreelyHomotopic β α := by
  obtain ⟨H, h0, h1, hc⟩ := h
  refine ⟨⟨fun x => H (unitInterval.symm x.1, x.2),
    H.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)⟩,
    fun t => ?_, fun t => ?_, fun s => hc _⟩
  · show H (unitInterval.symm 0, t) = β.2 t
    rw [unitInterval.symm_zero]
    exact h1 t
  · show H (unitInterval.symm 1, t) = α.2 t
    rw [unitInterval.symm_one]
    exact h0 t

/-- Free homotopy is transitive. -/
theorem s30b_fh_trans {Z : Type*} [TopologicalSpace Z] {α β γ : Loop Z} (h₁ : FreelyHomotopic α β)
    (h₂ : FreelyHomotopic β γ) : FreelyHomotopic α γ := by
  obtain ⟨H₁, h10, h11, hc1⟩ := h₁
  obtain ⟨H₂, h20, h21, hc2⟩ := h₂
  let F : ContinuousMap.Homotopy (α.2 : C(unitInterval, Z)) (β.2 : C(unitInterval, Z)) :=
    { toContinuousMap := H₁, map_zero_left := h10, map_one_left := h11 }
  let G : ContinuousMap.Homotopy (β.2 : C(unitInterval, Z)) (γ.2 : C(unitInterval, Z)) :=
    { toContinuousMap := H₂, map_zero_left := h20, map_one_left := h21 }
  refine ⟨(F.trans G).toContinuousMap, fun t => (F.trans G).apply_zero t, fun t => (F.trans G).apply_one t,
    fun s => ?_⟩
  show (F.trans G) (s, 0) = (F.trans G) (s, 1)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hc1 _
  · exact hc2 _

/-- A continuous map sends freely homotopic loops to freely homotopic loops. -/
theorem s30b_fh_map {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T] {f : Z → T} (hf : Continuous f)
    {α β : Loop Z} (h : FreelyHomotopic α β) : FreelyHomotopic ⟨f α.1, α.2.map hf⟩ ⟨f β.1, β.2.map hf⟩ := by
  obtain ⟨H, h0, h1, hc⟩ := h
  refine ⟨⟨fun x => f (H x), hf.comp H.continuous⟩, fun t => ?_, fun t => ?_, fun s => ?_⟩
  · show f (H (0, t)) = f (α.2 t)
    rw [h0]
  · show f (H (1, t)) = f (β.2 t)
    rw [h1]
  · show f (H (s, 0)) = f (H (s, 1))
    rw [hc]

/-- Homotopic maps send a loop to freely homotopic loops. -/
theorem s30b_fh_of_homotopic {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T] {f g : C(Z, T)}
    (h : f.Homotopic g) (α : Loop Z) :
    FreelyHomotopic ⟨f α.1, α.2.map f.continuous⟩ ⟨g α.1, α.2.map g.continuous⟩ := by
  obtain ⟨H⟩ := h
  refine ⟨⟨fun x => H (x.1, α.2 x.2), H.continuous.comp (continuous_fst.prodMk
    (α.2.continuous.comp continuous_snd))⟩, fun t => H.apply_zero _, fun t => H.apply_one _, fun s => ?_⟩
  show H (s, α.2 0) = H (s, α.2 1)
  rw [Path.source, Path.target]

/-- `l[α]` depends only on the free homotopy class of `α`. -/
theorem s30b_fhl_congr {Z : Type*} [TopologicalSpace Z] (p : UpperHalfPlane → Z) {α β : Loop Z}
    (h : FreelyHomotopic α β) : freeHomotopyLength p α = freeHomotopyLength p β := by
  apply le_antisymm
  · exact le_iInf₂ fun γ hγ => iInf₂_le γ (s30b_fh_trans h hγ)
  · exact le_iInf₂ fun γ hγ => iInf₂_le γ (s30b_fh_trans (s30b_fh_symm h) hγ)

/-- The denominator `c z + d` of `A ∈ SL(2, ℝ)` does not vanish on `ℍ`. -/
theorem s30b_den_ne (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    (A 1 0 : ℂ) * z + A 1 1 ≠ 0 :=
  h36t_den_ne A ⟨z, hz⟩

/-- `A z - A w = (z - w)/((c z + d)(c w + d))`. -/
theorem s30b_mob_sub (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z w : ℂ} (hz : (A 1 0 : ℂ) * z + A 1 1 ≠ 0)
    (hw : (A 1 0 : ℂ) * w + A 1 1 ≠ 0) :
    utm_b_mob A z - utm_b_mob A w = (z - w) / (((A 1 0 : ℂ) * z + A 1 1) * ((A 1 0 : ℂ) * w + A 1 1)) := by
  have hdet : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  unfold utm_b_mob
  rw [div_sub_div _ _ hz hw]
  congr 1
  linear_combination (z - w) * hdet

/-- The Möbius image of a Lipschitz curve in `ℍ` is Lipschitz. -/
theorem s30b_mob_lipschitz (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {c : ℝ → ℂ} {K : ℝ≥0}
    (hc : LipschitzOnWith K c (Icc 0 1)) (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) :
    ∃ K' : ℝ≥0, LipschitzOnWith K' (utm_b_mob A ∘ c) (Icc 0 1) := by
  have hcc : ContinuousOn c (Icc 0 1) := hc.continuousOn
  have hDc : ContinuousOn (fun t => ‖(A 1 0 : ℂ) * c t + A 1 1‖) (Icc 0 1) :=
    ((continuousOn_const.mul hcc).add continuousOn_const).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hDc
  set μ := ‖(A 1 0 : ℂ) * c t₀ + A 1 1‖ with hμ
  have hμ0 : 0 < μ := norm_pos_iff.2 (s30b_den_ne A (him t₀ ht₀))
  refine ⟨K * (Real.toNNReal (1 / μ ^ 2)), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hDx : μ ≤ ‖(A 1 0 : ℂ) * c x + A 1 1‖ := isMinOn_iff.1 hmin x hx
  have hDy : μ ≤ ‖(A 1 0 : ℂ) * c y + A 1 1‖ := isMinOn_iff.1 hmin y hy
  have hlip : dist (c x) (c y) ≤ K * dist x y := hc.dist_le_mul x hx y hy
  simp only [Function.comp_apply, dist_eq_norm]
  rw [s30b_mob_sub A (s30b_den_ne A (him x hx)) (s30b_den_ne A (him y hy)), norm_div, norm_mul]
  rw [dist_eq_norm, dist_eq_norm] at hlip
  have hprod : μ ^ 2 ≤ ‖(A 1 0 : ℂ) * c x + A 1 1‖ * ‖(A 1 0 : ℂ) * c y + A 1 1‖ := by
    rw [sq]
    exact mul_le_mul hDx hDy hμ0.le (hμ0.le.trans hDx)
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  rw [div_le_iff₀ (mul_pos (norm_pos_iff.2 (s30b_den_ne A (him x hx)))
    (norm_pos_iff.2 (s30b_den_ne A (him y hy))))]
  calc ‖c x - c y‖ ≤ K * ‖x - y‖ := hlip
    _ = ↑K * (1 / μ ^ 2) * ‖x - y‖ * μ ^ 2 := by field_simp
    _ ≤ ↑K * (1 / μ ^ 2) * ‖x - y‖ *
        (‖(A 1 0 : ℂ) * c x + A 1 1‖ * ‖(A 1 0 : ℂ) * c y + A 1 1‖) := by gcongr

/-- The derivative of a unimodular Möbius map: `((a z + b)/(c z + d))' = 1/(c z + d)²`. -/
theorem s30b_mob_hasDerivAt (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : (A 1 0 : ℂ) * z + A 1 1 ≠ 0) :
    HasDerivAt (utm_b_mob A) (1 / ((A 1 0 : ℂ) * z + A 1 1) ^ 2) z := by
  have hdet : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have h := (((hasDerivAt_id' z).const_mul (A 0 0 : ℂ)).add_const (A 0 1 : ℂ)).div
    (((hasDerivAt_id' z).const_mul (A 1 0 : ℂ)).add_const (A 1 1 : ℂ)) hz
  refine h.congr_deriv ?_
  congr 1
  linear_combination hdet

/-- The hyperbolic length is Möbius invariant (for curves in `ℍ` on `[0, 1]`, continuous on `[0, 1]`). -/
theorem s30b_hypLength_mob (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {c : ℝ → ℂ}
    (hcc : ContinuousOn c (Icc 0 1)) (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c t).im) :
    hypLength (utm_b_mob A ∘ c) = hypLength c := by
  unfold hypLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hz := him t htI
  have hD := s30b_den_ne A hz
  have hct : ContinuousAt c t := hcc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have himA : (utm_b_mob A (c t)).im = (c t).im / Complex.normSq ((A 1 0 : ℂ) * c t + A 1 1) :=
    utm_im_mobius (by have h := A.det_coe; rw [Matrix.det_fin_two] at h; exact h) (c t)
  have hN : 0 < Complex.normSq ((A 1 0 : ℂ) * c t + A 1 1) := Complex.normSq_pos.2 hD
  by_cases hd : DifferentiableAt ℝ c t
  · have hmob := s30b_mob_hasDerivAt A hD
    have hcomp : HasDerivAt (utm_b_mob A ∘ c) (1 / ((A 1 0 : ℂ) * c t + A 1 1) ^ 2 * deriv c t) t :=
      hmob.comp t hd.hasDerivAt
    simp only [Function.comp_apply]
    rw [hcomp.deriv, himA]
    have hnorm : ‖1 / ((A 1 0 : ℂ) * c t + A 1 1) ^ 2 * deriv c t‖ =
        ‖deriv c t‖ / Complex.normSq ((A 1 0 : ℂ) * c t + A 1 1) := by
      rw [norm_mul, norm_div, norm_one, norm_pow, Complex.normSq_eq_norm_sq]
      ring
    rw [← ofReal_norm, ← ofReal_norm, hnorm, ← ENNReal.ofReal_div_of_pos (div_pos hz hN),
      ← ENNReal.ofReal_div_of_pos hz]
    congr 1
    field_simp
  · -- neither `c` nor `A ∘ c` is differentiable at `t`
    have hd' : ¬ DifferentiableAt ℝ (utm_b_mob A ∘ c) t := by
      intro hAc
      apply hd
      have hmz := utm_b_mob_im_pos A hz
      have hback : c =ᶠ[𝓝 t] (utm_b_mob A⁻¹ ∘ (utm_b_mob A ∘ c)) := by
        have hev : ∀ᶠ s in 𝓝 t, 0 < (c s).im :=
          hct.eventually (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)
        filter_upwards [hev] with s hs
        simp only [Function.comp_apply]
        rw [utm_b_mob_smul A hs, utm_b_mob_coe, inv_smul_smul]
      have hD' : (A⁻¹ 1 0 : ℂ) * utm_b_mob A (c t) + A⁻¹ 1 1 ≠ 0 := s30b_den_ne A⁻¹ hmz
      have h2 : DifferentiableAt ℝ (utm_b_mob A⁻¹ ∘ (utm_b_mob A ∘ c)) t :=
        ((s30b_mob_hasDerivAt A⁻¹ hD').differentiableAt.restrictScalars ℝ).comp t hAc
      exact h2.congr_of_eventuallyEq hback
    simp only [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd',
      enorm_zero, ENNReal.zero_div]

/-- `l_{p_Y}[c ∘ β] ≤ l_{p_X}[β]` for one loop, when `c` lifts to the Möbius map `A`. -/
theorem s30b_pll_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} {c : X → Y} (hc : Continuous c) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ τ, pY (A • τ) = c (pX τ)) (β : Loop X) :
    poincareLengthLoop pY ⟨c β.1, β.2.map hc⟩ ≤ poincareLengthLoop pX β := by
  unfold poincareLengthLoop
  refine le_iInf₂ fun b hb => ?_
  obtain ⟨⟨K, hK⟩, him, hlift⟩ := hb
  obtain ⟨K', hK'⟩ := s30b_mob_lipschitz A hK him
  refine iInf₂_le_of_le (utm_b_mob A ∘ b) ⟨⟨K', hK'⟩, fun t ht => utm_b_mob_im_pos A (him t ht),
    fun t ht h => ?_⟩ (s30b_hypLength_mob A hK.continuousOn him).le
  have e : (⟨(utm_b_mob A ∘ b) t, h⟩ : UpperHalfPlane) = A • (⟨b t, him t ht⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext (utm_b_mob_smul A (him t ht))
  rw [e, hA, hlift t ht (him t ht), Path.extend_apply _ ht, Path.extend_apply _ ht]
  rfl

/-- `l_{p_Y}[c ∘ α] ≤ l_{p_X}[α]` when `c` lifts to the Möbius map `A`. -/
theorem s30b_fhl_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} {c : X → Y} (hc : Continuous c) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ τ, pY (A • τ) = c (pX τ)) (α : Loop X) :
    freeHomotopyLength pY ⟨c α.1, α.2.map hc⟩ ≤ freeHomotopyLength pX α :=
  le_iInf₂ fun β hβ => iInf₂_le_of_le ⟨c β.1, β.2.map hc⟩ (s30b_fh_map hc hβ) (s30b_pll_le hc A hA β)

/-- **Möbius invariance of `l[α]`.**  If a homeomorphism `c : X → Y` lifts to the Möbius map `A`, then
`l_{p_Y}[c ∘ α] = l_{p_X}[α]`. -/
theorem s30b_fhl_eq_of_mob {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (c : X ≃ₜ Y) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ τ, pY (A • τ) = c (pX τ)) (α : Loop X) :
    freeHomotopyLength pY ⟨c α.1, α.2.map c.continuous⟩ = freeHomotopyLength pX α := by
  have hB : ∀ τ, pX (A⁻¹ • τ) = c.symm (pY τ) := fun τ => by
    have h := hA (A⁻¹ • τ)
    rw [smul_inv_smul] at h
    rw [h, c.symm_apply_apply]
  refine le_antisymm (s30b_fhl_le c.continuous A hA α) ?_
  have h1 := s30b_fhl_le c.symm.continuous A⁻¹ hB ⟨c α.1, α.2.map c.continuous⟩
  have h2 : freeHomotopyLength pX α = freeHomotopyLength pX
      ⟨c.symm (c α.1), (α.2.map c.continuous).map c.symm.continuous⟩ :=
    s30b_fhl_congr pX (s30b_fh_of_eq fun t => by simp)
  rw [h2]
  exact h1

/-- `K[G] ≤ e^{2ε}` from `½ ln K[G] < ε`. -/
theorem s30b_maxDil_le_of_half_log_lt {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B] {G : A ≃ₜ B} (hG : IsQCRS G) [Nonempty A] {ε : ℝ}
    (h : (1 / 2 : ℝ) * Real.log (maxDilatationRS G).toReal < ε) :
    maxDilatationRS G ≤ ENNReal.ofReal (Real.exp (2 * ε)) := by
  have hne := s29_m_maxDilatationRS_ne_top hG
  have h1 := s29_m_one_le_toReal hG
  have hlog : Real.log (maxDilatationRS G).toReal < 2 * ε := by linarith
  have hlt : (maxDilatationRS G).toReal < Real.exp (2 * ε) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < (maxDilatationRS G).toReal)]
    exact Real.exp_lt_exp.2 hlog
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hlt.le

/-- `d_T([a], [b]) < ε` gives a q.c. `G : a.X → b.X` with `G ∘ a ≃ b` and `K[G] ≤ e^{2ε}`. -/
theorem s30b_small_map {Z : Type u} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (a b : MarkedRS Z) {ε : ℝ} (h : teichDistance (Quot.mk _ a : TeichSpace Z) (Quot.mk _ b) < ε) :
    ∃ G : a.X.carrier ≃ₜ b.X.carrier, IsQCRS G ∧ maxDilatationRS G ≤ ENNReal.ofReal (Real.exp (2 * ε)) ∧
      ContinuousMap.Homotopic ((a.marking.trans G : Z ≃ₜ b.X.carrier) : C(Z, b.X.carrier))
        (b.marking : C(Z, b.X.carrier)) := by
  have hinf : sInf (s29_m_teichSet (Quot.mk _ a : TeichSpace Z) (Quot.mk _ b)) < ε := h
  obtain ⟨d, hd, hdlt⟩ := exists_lt_of_csInf_lt (s29_m_teichSet_nonempty _ _) hinf
  obtain ⟨n₁, n₂, G₀, hn₁, hn₂, hG₀, hhom, rfl⟩ := hd
  obtain ⟨G, hG, hle, hhom'⟩ := s29_m_transport (s29_m_equiv_of_eq hn₁) (s29_m_equiv_of_eq hn₂) hG₀ hhom
  have : Nonempty n₁.X.carrier := ConnectedSpace.toNonempty
  exact ⟨G, hG, hle.trans (s30b_maxDil_le_of_half_log_lt hG₀ hdlt), hhom'⟩

/-- `σ ∘ m` is quasiconformal for a modular transformation `σ` and a marking `m`. -/
theorem s30b_isQCRS_trans {Z : Type u} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (h : ModTransform Z) (m : MarkedRS Z) : IsQCRS (h.1.trans m.marking) := by
  obtain ⟨K₁, hK₁⟩ := h.2.2
  obtain ⟨K₂, hK₂⟩ := m.qc
  exact ⟨_, (eq23_4 hK₁ hK₂).1⟩

/-- `σ* [m] = [m.X, m ∘ σ]`: the representative of the image may be taken over `m` itself. -/
theorem s30b_modAction_eq {Z : Type u} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (h : ModTransform Z) (m : MarkedRS Z) {q : TeichSpace Z} (hq : ModAction h (Quot.mk _ m) q) :
    q = Quot.mk _ (⟨m.X, h.1.trans m.marking, s30b_isQCRS_trans h m⟩ : MarkedRS Z) := by
  obtain ⟨m', hqc, hmm', rfl⟩ := hq
  apply Quot.sound
  obtain ⟨c, hc, hhom⟩ := s29_m_equiv_of_eq hmm'.symm
  refine ⟨c, hc, ?_⟩
  have h1 := hhom.comp (ContinuousMap.Homotopic.refl (h.1 : C(Z, Z)))
  exact h1

/-- (30.10)–(30.13) (the proof of Theorem 30.3): if `[S, f ∘ σₖ] → [S₁, f₁]`, the extremal maps
`gₖ : S₁ → S` in the classes of `f ∘ σₖ ∘ f₁⁻¹` have `K[gₖ] → 1`, hence by Wolpert's lemma
`l[gₖ(β)] → l[β]` (30.10) for every closed curve `β`; by discreteness the lengths `l[f ∘ σₖ(αₙ)]`
eventually equal `l[f₁(αₙ)]` (30.13), so `[S, f ∘ σₖ] = [S, f₁]` for large `k`, giving infinitely
many conformal automorphisms of `S` — contradicting Hurwitz. -/
theorem eq30_13_eventually_equal {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (α : ℕ → Loop S₀)
    (hrep : ∀ β : Loop S₀, ∃ n, FreelyHomotopic β (α n)) (m : MarkedRS S₀) (m₁ : MarkedRS S₀)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → m.X.carrier} (hp : IsUniformization Γ p)
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → m₁.X.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) (σ : ℕ → ModTransform S₀) {τn : ℕ → TeichSpace S₀}
    (hσ : ∀ n, ModAction (σ n) (Quot.mk _ m) (τn n))
    (hconv : Tendsto (fun n => teichDistance (τn n) (Quot.mk _ m₁)) atTop (𝓝 0)) (n : ℕ) :
    ∀ᶠ k in atTop, freeHomotopyLength p ⟨m.marking ((σ k).1 (α n).1), ((α n).2.map (σ k).1.continuous).map m.marking.continuous⟩ =
      freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩ := by
  classical
  have _ := hg
  have _ := hS
  have _ := hrep
  have _ : T2Space S₀ := inferInstance
  have _ : ConnectedSpace S₀ := inferInstance
  have _ : CompactSpace S₀ := inferInstance
  -- the points `σₖ* [m] = [m.X, m ∘ σₖ]`
  let a : ℕ → MarkedRS S₀ := fun k => ⟨m.X, (σ k).1.trans m.marking, s30b_isQCRS_trans (σ k) m⟩
  have hτ : ∀ k, τn k = Quot.mk _ (a k) := fun k => s30b_modAction_eq (σ k) m (hσ k)
  let d : ℕ → ℝ := fun k => teichDistance (Quot.mk _ (a k) : TeichSpace S₀) (Quot.mk _ m₁)
  have hdconv : Tendsto d atTop (𝓝 0) := by
    have e : (fun k => teichDistance (τn k) (Quot.mk MarkedRS.Equiv m₁)) = d := funext fun k => by
      simp only [d, hτ k]
    exact e ▸ hconv
  -- maps `G k : m.X → m₁.X` with `G k ∘ m ∘ σₖ ≃ m₁` and `K[G k] ≤ e^{2(d k + 1/(k+1))}`
  have hG : ∀ k, ∃ G : m.X.carrier ≃ₜ m₁.X.carrier, IsQCRS G ∧
      maxDilatationRS G ≤ ENNReal.ofReal (Real.exp (2 * (d k + 1 / ((k : ℝ) + 1)))) ∧
      ContinuousMap.Homotopic (((a k).marking.trans G : S₀ ≃ₜ m₁.X.carrier) : C(S₀, m₁.X.carrier))
        (m₁.marking : C(S₀, m₁.X.carrier)) := fun k =>
    s30b_small_map (a k) m₁ (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      show d k < d k + 1 / ((k : ℝ) + 1)
      linarith)
  choose G hGqc hGle hGhom using hG
  -- a map `c ≃ G k` with a Möbius lift gives the equality at `k`
  have KC : ∀ (c : m.X.carrier ≃ₜ m₁.X.carrier) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ τ, p₁ (A • τ) = c (p τ)) → ∀ k,
      ContinuousMap.Homotopic (c : C(m.X.carrier, m₁.X.carrier)) (G k : C(m.X.carrier, m₁.X.carrier)) →
      freeHomotopyLength p ⟨m.marking ((σ k).1 (α n).1),
          ((α n).2.map (σ k).1.continuous).map m.marking.continuous⟩ =
        freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩ := by
    intro c A hA k hk
    rw [← s30b_fhl_eq_of_mob c A hA]
    apply s30b_fhl_congr
    have hmaps : ContinuousMap.Homotopic (((a k).marking.trans c : S₀ ≃ₜ m₁.X.carrier) : C(S₀, m₁.X.carrier))
        (m₁.marking : C(S₀, m₁.X.carrier)) := by
      have h1 := hk.comp (ContinuousMap.Homotopic.refl ((a k).marking : C(S₀, m.X.carrier)))
      rw [← coe_homeomorph_trans, ← coe_homeomorph_trans] at h1
      exact h1.trans (hGhom k)
    have h2 := s30b_fh_of_homotopic hmaps (α n)
    refine s30b_fh_trans ?_ (s30b_fh_trans h2 ?_)
    · exact s30b_fh_of_eq fun t => rfl
    · exact s30b_fh_of_eq fun t => rfl
  -- otherwise infinitely many `k` fail
  by_contra hcon
  have hI : {k | freeHomotopyLength p ⟨m.marking ((σ k).1 (α n).1),
      ((α n).2.map (σ k).1.continuous).map m.marking.continuous⟩ ≠
      freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩}.Infinite :=
    Nat.frequently_atTop_iff_infinite.1 (Filter.not_eventually.1 hcon)
  let e := hI.natEmbedding
  let E : ℕ → ℕ := fun j => (e j).1
  have hEinj : Function.Injective E := fun i j h => e.injective (Subtype.ext h)
  have hEt : Tendsto E atTop atTop := by
    have := hEinj.tendsto_cofinite
    rwa [Nat.cofinite_eq_atTop] at this
  -- along them `K[G] → 1`, so some of them is homotopic to a map with a Möbius lift
  let Kj : ℕ → ℝ := fun j => Real.exp (2 * (d (E j) + 1 / ((E j : ℝ) + 1)))
  have hGK : ∀ j, IsKQCRS (G (E j)) (Kj j) := by
    intro j
    have hd0 : 0 ≤ d (E j) := s29_m_teichDistance_nonneg _ _
    have h1 : (0 : ℝ) ≤ 1 / ((E j : ℝ) + 1) := by positivity
    exact s29_m_isKQCRS_of_le (hGqc _) (Real.one_le_exp (by linarith)) (hGle _)
  have hKj : Tendsto Kj atTop (𝓝 1) := by
    have h1 := hdconv.comp hEt
    have h2 : Tendsto (fun j => 1 / ((E j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hEt
    have h3 := (Real.continuous_exp.tendsto _).comp ((h1.add h2).const_mul 2)
    simpa [Kj, Function.comp_def] using h3
  obtain ⟨j, c, A, hA, hhom⟩ := s30b_conformal_limit hp hp₁ (fun j => G (E j)) Kj hGK hKj
  exact (e j).2 (KC c A hA (E j) hhom)

/-! ## §30.6 `R_g` is a Hausdorff space -/

/-- §30.6: the `ε`-neighbourhood of `[S] ∈ R_g`: the projection of the `ε`-ball about a point
`[S, f]` over it (independent of the choice of `[S, f]` by the isometry of modular
transformations). -/
def moduliNbhd {g : ℕ} (r : ModuliSpace.{u} g) (ε : ℝ) : Set (ModuliSpace.{u} g) :=
  {r' | ∃ p p' : TeichSpace S₀, LiesOver p r ∧ LiesOver p' r' ∧ teichDistance p p' < ε}

end LiZhongQC
