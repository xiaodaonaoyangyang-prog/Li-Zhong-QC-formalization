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
* §30.4 Theorem 30.2 (finitely many lengths determine the marked surface), (30.1)–(30.4)
                                                                — `thm30_2_length_spectrum_determines`
* §30.5 Lemma 30.3 (Wolpert, (30.5)–(30.9)); Theorem 30.3 (discontinuity of `Mod(S₀)`),
  (30.10)–(30.13), Hurwitz's theorem                            — `lemma30_3_wolpert`, `thm30_3`,
                                                                  `hurwitz`
* §30.6 Theorem 30.4 (`R_g` is Hausdorff)                       — `thm30_4_hausdorff`
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
  sorry

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

/-- §30.2 (generalized Schwarz lemma): if `S₁ ⊆ S₂` is a sub-Riemann surface (an open subset,
uniformized by `p₁`) of `S₂` (uniformized by `p₂`), the Poincaré metric of `S₁` dominates that of
`S₂`: every closed curve in `S₁` is at least as long for `S₁` as for `S₂`.  Equality holds only for
`S₁ = S₂`. -/
theorem generalized_schwarz {S₂ : Type u} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [T2Space S₂]
    [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂] (U : TopologicalSpace.Opens S₂) [ConnectedSpace U]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → U} {p₂ : UpperHalfPlane → S₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂) (α : Loop U) :
    poincareLengthLoop p₂ ⟨(α.1 : S₂), α.2.map continuous_subtype_val⟩ ≤ poincareLengthLoop p₁ α := by
  sorry

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

/-- **Lemma 30.2**: let `S = ℍ/G`, `G` a torsion free Fuchsian group, and let `γ ∈ G` cover the
closed curve `α ⊆ S`.  Then `l[α] = ln λ²`, `λ` the larger eigenvalue of the matrix of `γ`
(`l[α] = 0` when `γ` is parabolic). -/
theorem lemma30_2 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) {α : Loop S} (hcov : Covers p γ α) :
    (IsHyperbolic γ → freeHomotopyLength p α = ENNReal.ofReal (translationLength γ)) ∧
      (IsParabolic γ → freeHomotopyLength p α = 0) := by
  sorry

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

/-- **Theorem 30.1** (长度谱的离散性): let `S` be a compact Riemann surface of genus `> 1` and `{αₙ}` a
sequence of closed curves representing all free homotopy classes.  For every `M > 0` only finitely
many `n` satisfy `l[αₙ] ≤ M`. -/
theorem thm30_1_discrete {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (α : ℕ → Loop S)
    (hrep : ∀ β : Loop S, ∃ n, FreelyHomotopic β (α n)) (hinj : ∀ m n, FreelyHomotopic (α m) (α n) → m = n)
    (M : ℝ) : {n | freeHomotopyLength p (α n) ≤ ENNReal.ofReal M}.Finite := by
  sorry

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

/-! ## §30.4 The length spectrum determines the Riemann surface -/

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
  sorry

/-- **Theorem 30.2** (由长度谱确定 Riemann 曲面).  Let `S₁`, `S₂` be compact Riemann surfaces of genus
`g > 1`, `f : S₁ → S₂` an orientation preserving homeomorphism, `{αₙ}` a sequence of closed curves
in `S₁` representing all elements of `π₁(S₁)`, `βₙ = f(αₙ)`.  There is `N`, depending only on
`{αₙ}` and `g`, such that `l[αₙ] = l[βₙ]` for `n = 1, …, N` implies that the homotopy class of `f`
contains a conformal map. -/
theorem thm30_2_length_spectrum_determines {S₁ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g) (h₁ : HasGenus S₁ g)
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁} (hp₁ : IsUniformization Γ₁ p₁)
    (α : ℕ → Loop S₁) (hrep : ∀ β : Loop S₁, ∃ n, FreelyHomotopic β (α n)) :
    ∃ N : ℕ, ∀ (S₂ : Type u) [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [T2Space S₂] [ConnectedSpace S₂]
      [IsManifold 𝓘(ℂ) ω S₂] (h₂ : HasGenus S₂ g) (Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₂ : UpperHalfPlane → S₂) (hp₂ : IsUniformization Γ₂ p₂) (f : S₁ ≃ₜ S₂) (hf : IsOrientationPreservingRS f),
      (∀ n ≤ N, freeHomotopyLength p₁ (α n) = freeHomotopyLength p₂ ⟨f (α n).1, (α n).2.map f.continuous⟩) →
      ∃ φ : S₁ ≃ₜ S₂, IsBiholomorphic φ ∧ ContinuousMap.Homotopic (f : C(S₁, S₂)) (φ : C(S₁, S₂)) := by
  sorry

/-- (30.1) (the group form of Theorem 30.2): there are finitely many words `w₁, …, w_N` in the
standard generators of the surface group of genus `g` such that two faithful discrete cocompact
representations `ρ₁, ρ₂` with `|tr ρ₁(wᵢ)| = |tr ρ₂(wᵢ)|` (`i ≤ N`) and normalized standard
generators have `ρ₁ = ρ₂` on the generators (up to sign), hence `G₁ = G₂`. -/
theorem eq30_1_generators_determined {g : ℕ} (hg : 1 < g) :
    ∃ (N : ℕ) (w : Fin N → surfaceGroup g), ∀ ρ₁ ρ₂ : surfaceGroup g →* Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Function.Injective ρ₁ → Function.Injective ρ₂ →
      IsFuchsian ρ₁.range → IsFuchsian ρ₂.range → IsCocompact ρ₁.range → IsCocompact ρ₂.range →
      (∀ i, |slTrace (ρ₁ (w i))| = |slTrace (ρ₂ (w i))|) →
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ x : surfaceGroup g,
        ρ₂ x = A * ρ₁ x * A⁻¹ ∨ ρ₂ x = -(A * ρ₁ x * A⁻¹) := by
  sorry

/-! ## §30.5 Discontinuity of the action of the modular group -/

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
  sorry

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

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §30.5: the length spectrum of a marked surface `(S, f)`: `{l[f(αₙ)]}`; it depends only on the
class `[S, f] ∈ T(S₀)`, and (Theorem 30.2) two points of `T(S₀)` with the same first `N` terms
coincide. -/
theorem markedLengthSpectrum_wellDefined {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (α : ℕ → Loop S₀)
    (hrep : ∀ β : Loop S₀, ∃ n, FreelyHomotopic β (α n)) :
    ∃ N : ℕ, ∀ (m₁ m₂ : MarkedRS S₀) (Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₁ : UpperHalfPlane → m₁.X.carrier) (p₂ : UpperHalfPlane → m₂.X.carrier),
      IsUniformization Γ₁ p₁ → IsUniformization Γ₂ p₂ →
      ((m₁.Equiv m₂) ↔ ∀ n ≤ N, freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩ =
        freeHomotopyLength p₂ ⟨m₂.marking (α n).1, (α n).2.map m₂.marking.continuous⟩) := by
  sorry

/-- §30.5 (Hurwitz's theorem, finiteness): a compact Riemann surface of genus `g > 1` has only finitely many
conformal automorphisms.  (Stated separately from `hurwitz` by user decision, 2026-09-26, so that it can be proved
for surfaces given as `ℍ/Γ` as a companion; `hurwitz` below still contains it.) -/
theorem hurwitz_finite {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.Finite := by
  sorry

/-- §30.5 (Hurwitz's theorem): a compact Riemann surface of genus `g > 1` has at most `84(g - 1)`
conformal automorphisms.  (The finiteness conjunct stays here: `Set.ncard` of an infinite set is `0` in Lean, so the
bound alone would not say that the automorphism group is finite.  It is also stated on its own as
`hurwitz_finite`.) -/
theorem hurwitz {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.Finite ∧ {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.ncard ≤ 84 * (g - 1) := by
  sorry

/-- §30.5: the action of `Mod(S₀)` on `T(S₀)` is discontinuous: the orbit of every point has no
limit point in `T(S₀)`. -/
def ModActionDiscontinuous (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Prop :=
  ∀ τ τ₁ : TeichSpace S₀, ¬ ∃ σ : ℕ → ModTransform S₀,
    (∀ i j, i ≠ j → ¬ ContinuousMap.Homotopic ((σ i).1 : C(S₀, S₀)) ((σ j).1 : C(S₀, S₀))) ∧
    ∃ τn : ℕ → TeichSpace S₀, (∀ n, ModAction (σ n) τ (τn n)) ∧
      Tendsto (fun n => teichDistance (τn n) τ₁) atTop (𝓝 0)

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
  sorry

/-- **Theorem 30.3**: for a compact Riemann surface `S₀` of genus `g > 1`, the modular group
`Mod(S₀)` acts discontinuously on `T(S₀)`. -/
theorem thm30_3 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) : ModActionDiscontinuous S₀ := by
  sorry

/-- §30.5 (proper discontinuity, equivalent form): for every `p` and `R > 0`, up to homotopy only
finitely many modular transformations move some point of the `d_T`-ball of radius `R` about `p`
into that ball. -/
theorem modAction_properly_discontinuous {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (p : TeichSpace S₀) (R : ℝ) :
    ∃ F : Finset (ModTransform S₀), ∀ h : ModTransform S₀,
      (∃ q q', teichDistance p q < R ∧ ModAction h q q' ∧ teichDistance p q' < R) →
        ∃ h' ∈ F, ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) := by
  sorry

/-! ## §30.6 `R_g` is a Hausdorff space -/

/-- §30.6: the `ε`-neighbourhood of `[S] ∈ R_g`: the projection of the `ε`-ball about a point
`[S, f]` over it (independent of the choice of `[S, f]` by the isometry of modular
transformations). -/
def moduliNbhd {g : ℕ} (r : ModuliSpace.{u} g) (ε : ℝ) : Set (ModuliSpace.{u} g) :=
  {r' | ∃ p p' : TeichSpace S₀, LiesOver p r ∧ LiesOver p' r' ∧ teichDistance p p' < ε}

/-- **Theorem 30.4**: for `g > 1`, `R_g = T_g/Mod_g` is a Hausdorff space: distinct points of `R_g`
have disjoint `ε`-neighbourhoods. -/
theorem thm30_4_hausdorff {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {r r' : ModuliSpace.{u} g} (hne : r ≠ r') :
    ∃ ε > 0, Disjoint (moduliNbhd (S₀ := S₀) r ε) (moduliNbhd (S₀ := S₀) r' ε) := by
  sorry

end LiZhongQC
