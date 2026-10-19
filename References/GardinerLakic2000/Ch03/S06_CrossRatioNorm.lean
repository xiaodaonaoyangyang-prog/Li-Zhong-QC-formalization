import References.GardinerLakic2000.Ch03.S05_TeichmullerInfinitesimalNorm

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.6 Cross-ratio norm on `Z(Λ)`

Source `teichmuller.txt`, lines 2635–2784 (Chapter 3, §3.6); Figure 3.1 from the second OCR (GL8:2566–2570, image
`b345335a…jpg`).

* Definition (the cross-ratio `cr(z₁, z₂, z₃, z₄) = MT/(LR)`, l. 2639; used in Ch. 6, 16) — `crossRatioGL`
* Formula (3.24) (the infinitesimal cross-ratio distortion `V(z₁, z₂, z₃, z₄)`, l. 2646–2651) — `crDistortion`
* Formulas (3.25), (3.26) (`‖V_μ‖_cr ≤ ‖μ‖∞`, l. 2657–2677; the first inequality of Theorem 11) — `eq3_26`
* Definition 8 (the infinitesimal cross-ratio norm, l. 2665) — `crNorm`
* Lemma 1 (l. 2682) — `lemma3_1`
* Lemma 2 (Möbius invariance, l. 2690) — `lemma3_2`
* Lemma 3 (l. 2700; cited in §3.9) — `lemma3_3_a`, `lemma3_3_b`
* Definition (`Z_cr`, the functions with finite cross-ratio norm modulo quadratic polynomials, l. 2733) — `zCrSet`
* Theorem 8 (l. 2735) — `thm3_8`
* Definition (the four-pole differentials `φ_Q` of norm 1, l. 2768–2774, 3102, 3112–3118; used in Cors. 2, 3) —
  `phiQ`, `phiQInf`
* Formula (3.28) (`‖V_μ‖_cr = sup_Q |L(φ_Q)|`, l. 2778; cited in Cors. 2, 3) — `eq3_28`

Not items: (3.27) (l. 2764) and `‖I‖ ≤ 1` (l. 2783), immediate from (3.26) and (3.28); the growth remarks (l. 2731,
U−). Modelling:
- Figure 3.1 (lost in `teichmuller.txt`, present in GL8): `L = z₂ − z₁`, `M = z₃ − z₂`, `R = z₄ − z₃`, `T = z₁ − z₄`,
  and `V′(L) = (V(z₂) − V(z₁))/(z₂ − z₁)` etc. (as Exercise 7, l. 3605); `ρ` is the Poincaré density of
  `ℂ̄ ∖ {0, 1, ∞}` (`poincareDensityGL`, curvature −4).
- `Λ : Set ExtPlane` is closed; the cross-ratio norm is the supremum over quadruples of distinct finite points of `Λ`
  [reading]. The book normalizes `V(∞) = 0` by `V(z) = o(z²)` (l. 2698); where the book uses quadruples with `∞`
  (Lemma 7 of the Appendix, the proof of Theorem 12) the three-point form `crDistortionInf` of l. 3199, 3284 is used.
- Lemma 3: the family `𝓕₁` of the proof (fields vanishing at `0, 1, ∞`) is written into the hypotheses of both parts
  [reading]: without it no constant `C(R, ‖V‖_cr)` exists (`V = N z²` has `‖V‖_cr = 0`). "`V(z) ≤ D|z| log|z|`" reads
  `|V(z)|`, "`max{z₁, z₂}`" reads `max{|z₁|, |z₂|}` [misprint; so also GL8:2633].
- Lemma 2 is stated for Möbius maps `B` that keep the finite parts finite (`B(∞) ∉ Λ`), the case where the finite
  cross-ratio norm is invariant.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane normalizedCauchyTOn IsBeltramiCoeff)

/-- **Definition** (§3.6, l. 2639). `cr(z₁, z₂, z₃, z₄) = MT/(LR) = (z₃ − z₂)(z₁ − z₄)/((z₂ − z₁)(z₄ − z₃))`. -/
def crossRatioGL (z₁ z₂ z₃ z₄ : ℂ) : ℂ := (z₃ - z₂) * (z₁ - z₄) / ((z₂ - z₁) * (z₄ - z₃))

/-- **Formula (3.24)** (§3.6, l. 2646–2651). `V(z₁, z₂, z₃, z₄) = cr(Q) ρ(cr(Q)) (V′(L) − V′(M) + V′(R) − V′(T))`,
`ρ` the Poincaré density of `ℂ̄ ∖ {0, 1, ∞}`, `V′(L) = (V(z₂) − V(z₁))/(z₂ − z₁)` and similarly for `M`, `R`, `T`. -/
def crDistortion (V : ℂ → ℂ) (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  crossRatioGL z₁ z₂ z₃ z₄ * (poincareDensityGL {w : ℂ | w ≠ 0 ∧ w ≠ 1} (crossRatioGL z₁ z₂ z₃ z₄) : ℂ) *
    ((V z₂ - V z₁) / (z₂ - z₁) - (V z₃ - V z₂) / (z₃ - z₂) + (V z₄ - V z₃) / (z₄ - z₃) -
      (V z₁ - V z₄) / (z₁ - z₄))

/-- Helper (§3.6, l. 3199, 3284). The distortion `V(a, b, c, ∞)` of a quadruple with the point `∞`, for `V` vanishing
at `∞`: `cr ρ(cr) ((V(b) − V(a))/(b − a) − (V(c) − V(b))/(c − b))`, `cr = (c − b)/(a − b)`. -/
def crDistortionInf (V : ℂ → ℂ) (a b c : ℂ) : ℂ :=
  (c - b) / (a - b) * (poincareDensityGL {w : ℂ | w ≠ 0 ∧ w ≠ 1} ((c - b) / (a - b)) : ℂ) *
    ((V b - V a) / (b - a) - (V c - V b) / (c - b))

/-- **Definition 8** (§3.6, l. 2665). The infinitesimal cross-ratio norm `‖V‖_cr = sup_Q |V(z₁, z₂, z₃, z₄)|` over the
quadruples of distinct (finite) points of `Λ`. -/
def crNorm (Λ : Set ExtPlane) (V : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (z : Fin 4 → ℂ) (_ : Function.Injective z ∧ ∀ i, (z i : ExtPlane) ∈ Λ),
    (‖crDistortion V (z 0) (z 1) (z 2) (z 3)‖₊ : ℝ≥0∞)

/-- **Formula (3.26)** (§3.6, l. 2677). For every bounded Beltrami coefficient `μ`, `‖V_μ‖_cr ≤ ‖μ‖∞`. -/
theorem eq3_26 (Λ : Set ExtPlane) {μ : ℂ → ℂ} (hμ : ∃ k : ℝ, IsBeltramiCoeff μ univ k) :
    crNorm Λ (normalizedCauchyTOn univ μ) ≤ eLpNorm μ ⊤ volume := by
  sorry

/-- Helper for `lemma3_1`: the bracket of (3.24) of a quadratic polynomial vanishes. -/
theorem gl3_bracket_quadratic {a b c z₁ z₂ z₃ z₄ : ℂ} (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄)
    (h41 : z₄ ≠ z₁) (V : ℂ → ℂ) (hV : ∀ z ∈ ({z₁, z₂, z₃, z₄} : Set ℂ), V z = a * z ^ 2 + b * z + c) :
    (V z₂ - V z₁) / (z₂ - z₁) - (V z₃ - V z₂) / (z₃ - z₂) + (V z₄ - V z₃) / (z₄ - z₃) -
      (V z₁ - V z₄) / (z₁ - z₄) = 0 := by
  have hdd : ∀ x y : ℂ, x ≠ y → ((a * y ^ 2 + b * y + c) - (a * x ^ 2 + b * x + c)) / (y - x) = a * (x + y) + b := by
    intro x y hxy
    rw [div_eq_iff (sub_ne_zero.2 hxy.symm)]
    ring
  rw [hV z₁ (by simp), hV z₂ (by simp), hV z₃ (by simp), hV z₄ (by simp), hdd _ _ h12, hdd _ _ h23, hdd _ _ h34,
    hdd _ _ h41]
  ring

/-- Helper for `lemma3_1`: for distinct `z₁, …, z₄`, `cr(z₁, z₂, z₃, z₄) ∉ {0, 1}` and the distortion vanishes only
when the bracket of (3.24) does. -/
theorem gl3_bracket_of_distortion {V : ℂ → ℂ} {z₁ z₂ z₃ z₄ : ℂ} (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄)
    (h41 : z₄ ≠ z₁) (h13 : z₁ ≠ z₃) (h24 : z₂ ≠ z₄) (h : crDistortion V z₁ z₂ z₃ z₄ = 0) :
    (V z₂ - V z₁) / (z₂ - z₁) - (V z₃ - V z₂) / (z₃ - z₂) + (V z₄ - V z₃) / (z₄ - z₃) -
      (V z₁ - V z₄) / (z₁ - z₄) = 0 := by
  have hcr0 : crossRatioGL z₁ z₂ z₃ z₄ ≠ 0 := by
    unfold crossRatioGL
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.2 h23.symm) (sub_ne_zero.2 h41.symm))
      (mul_ne_zero (sub_ne_zero.2 h12.symm) (sub_ne_zero.2 h34.symm))
  have hcr1 : crossRatioGL z₁ z₂ z₃ z₄ ≠ 1 := by
    unfold crossRatioGL
    intro h1
    rw [div_eq_one_iff_eq (mul_ne_zero (sub_ne_zero.2 h12.symm) (sub_ne_zero.2 h34.symm))] at h1
    have : (z₃ - z₁) * (z₄ - z₂) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact h13 (sub_eq_zero.1 h).symm
    · exact h24 (sub_eq_zero.1 h).symm
  have hρ := gl3_density_pos hcr0 hcr1
  unfold crDistortion at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h hcr0
    · exact absurd (Complex.ofReal_eq_zero.1 h) hρ.ne'
  · exact h

/-- **Lemma 1** (§3.6, l. 2682). `‖V‖_cr = 0` if and only if `V` is the restriction to `Λ` of a quadratic
polynomial. -/
theorem lemma3_1 (Λ : Set ExtPlane) (V : ℂ → ℂ) :
    crNorm Λ V = 0 ↔ ∃ a b c : ℂ, ∀ z : ℂ, (z : ExtPlane) ∈ Λ → V z = a * z ^ 2 + b * z + c := by
  constructor
  · intro h0
    have hall : ∀ z₁ z₂ z₃ z₄ : ℂ, (z₁ : ExtPlane) ∈ Λ → (z₂ : ExtPlane) ∈ Λ → (z₃ : ExtPlane) ∈ Λ →
        (z₄ : ExtPlane) ∈ Λ → z₁ ≠ z₂ → z₂ ≠ z₃ → z₃ ≠ z₄ → z₄ ≠ z₁ → z₁ ≠ z₃ → z₂ ≠ z₄ →
        (V z₂ - V z₁) / (z₂ - z₁) - (V z₃ - V z₂) / (z₃ - z₂) + (V z₄ - V z₃) / (z₄ - z₃) -
          (V z₁ - V z₄) / (z₁ - z₄) = 0 := by
      intro z₁ z₂ z₃ z₄ m₁ m₂ m₃ m₄ h12 h23 h34 h41 h13 h24
      refine gl3_bracket_of_distortion h12 h23 h34 h41 h13 h24 ?_
      have h21 := h12.symm
      have h32 := h23.symm
      have h43 := h34.symm
      have h14 := h41.symm
      have h31 := h13.symm
      have h42 := h24.symm
      have hinj : Function.Injective ![z₁, z₂, z₃, z₄] := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have hmem : ∀ i, ((![z₁, z₂, z₃, z₄] i : ℂ) : ExtPlane) ∈ Λ := by
        intro i
        fin_cases i <;> simpa
      have h1 := ENNReal.iSup_eq_zero.1 h0 ![z₁, z₂, z₃, z₄]
      have h2 := ENNReal.iSup_eq_zero.1 h1 ⟨hinj, hmem⟩
      simpa using h2
    by_cases h3 : ∃ z₁ z₂ z₃ : ℂ, (z₁ : ExtPlane) ∈ Λ ∧ (z₂ : ExtPlane) ∈ Λ ∧ (z₃ : ExtPlane) ∈ Λ ∧
        z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₁ ≠ z₃
    · -- Newton interpolation through three points of `Λ`
      obtain ⟨z₁, z₂, z₃, m₁, m₂, m₃, h12, h23, h13⟩ := h3
      have s12 : z₂ - z₁ ≠ 0 := sub_ne_zero.2 h12.symm
      have s23 : z₃ - z₂ ≠ 0 := sub_ne_zero.2 h23.symm
      have s13 : z₃ - z₁ ≠ 0 := sub_ne_zero.2 h13.symm
      set D₁ := (V z₂ - V z₁) / (z₂ - z₁) with hD₁
      set D₂ := ((V z₃ - V z₂) / (z₃ - z₂) - D₁) / (z₃ - z₁) with hD₂
      refine ⟨D₂, D₁ - D₂ * (z₁ + z₂), V z₁ - D₁ * z₁ + D₂ * z₁ * z₂, fun z hz => ?_⟩
      have hQ : D₂ * z ^ 2 + (D₁ - D₂ * (z₁ + z₂)) * z + (V z₁ - D₁ * z₁ + D₂ * z₁ * z₂) =
          V z₁ + D₁ * (z - z₁) + D₂ * (z - z₁) * (z - z₂) := by ring
      rw [hQ]
      by_cases e1 : z = z₁
      · rw [e1]; ring
      by_cases e2 : z = z₂
      · rw [e2, hD₁]; field_simp; ring
      by_cases e3 : z = z₃
      · rw [e3, hD₂, hD₁]; field_simp; ring
      have hB := hall z₁ z₂ z₃ z m₁ m₂ m₃ hz h12 h23 (Ne.symm e3) e1 h13 (Ne.symm e2)
      have s3 : z - z₃ ≠ 0 := sub_ne_zero.2 e3
      have s1 : z₁ - z ≠ 0 := sub_ne_zero.2 (Ne.symm e1)
      have key : ((V z₂ - V z₁) / (z₂ - z₁) - (V z₃ - V z₂) / (z₃ - z₂) + (V z - V z₃) / (z - z₃) -
          (V z₁ - V z) / (z₁ - z)) * ((z - z₃) * (z₁ - z)) =
          (V z - (V z₁ + D₁ * (z - z₁) + D₂ * (z - z₁) * (z - z₂))) * (z₁ - z₃) := by
        rw [hD₂, hD₁]
        field_simp
        ring
      rw [hB, zero_mul] at key
      have := (mul_eq_zero.1 key.symm).resolve_right (sub_ne_zero.2 h13)
      exact sub_eq_zero.1 this
    · push Not at h3
      by_cases h2 : ∃ u v : ℂ, (u : ExtPlane) ∈ Λ ∧ (v : ExtPlane) ∈ Λ ∧ u ≠ v
      · obtain ⟨u, v, mu, mv, huv⟩ := h2
        have s : v - u ≠ 0 := sub_ne_zero.2 huv.symm
        refine ⟨0, (V v - V u) / (v - u), V u - (V v - V u) / (v - u) * u, fun z hz => ?_⟩
        by_cases eu : z = u
        · rw [eu]; ring
        by_cases ev : z = v
        · rw [ev]; field_simp; ring
        exact absurd (h3 u v z mu mv hz huv (fun h => ev h.symm)).symm eu
      · push Not at h2
        by_cases h1 : ∃ u : ℂ, (u : ExtPlane) ∈ Λ
        · obtain ⟨u, mu⟩ := h1
          refine ⟨0, 0, V u, fun z hz => ?_⟩
          rw [h2 z u hz mu]
          ring
        · push Not at h1
          exact ⟨0, 0, 0, fun z hz => absurd hz (h1 z)⟩
  · rintro ⟨a, b, c, hq⟩
    refine ENNReal.iSup_eq_zero.2 fun z => ENNReal.iSup_eq_zero.2 fun hz => ?_
    obtain ⟨hinj, hmem⟩ := hz
    have hB := gl3_bracket_quadratic (hinj.ne (by decide : (0 : Fin 4) ≠ 1)) (hinj.ne (by decide : (1 : Fin 4) ≠ 2))
      (hinj.ne (by decide : (2 : Fin 4) ≠ 3)) (hinj.ne (by decide : (3 : Fin 4) ≠ 0)) V (by
        intro y hy
        simp only [mem_insert_iff, mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> exact hq _ (hmem _))
    unfold crDistortion
    rw [hB, mul_zero]
    simp

/-- Helper for `lemma3_2`: the cross-ratio is Möbius invariant. -/
theorem gl3_cr_mob {a b c d : ℂ} (had : a * d - b * c ≠ 0) {z₁ z₂ z₃ z₄ : ℂ} (h₁ : c * z₁ + d ≠ 0)
    (h₂ : c * z₂ + d ≠ 0) (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0) (h12 : z₁ ≠ z₂) (h34 : z₃ ≠ z₄) :
    crossRatioGL ((a * z₁ + b) / (c * z₁ + d)) ((a * z₂ + b) / (c * z₂ + d)) ((a * z₃ + b) / (c * z₃ + d))
      ((a * z₄ + b) / (c * z₄ + d)) = crossRatioGL z₁ z₂ z₃ z₄ := by
  unfold crossRatioGL
  rw [gl3_mob_sub h₂ h₃, gl3_mob_sub h₄ h₁, gl3_mob_sub h₁ h₂, gl3_mob_sub h₃ h₄]
  have s12 : z₂ - z₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have s34 : z₄ - z₃ ≠ 0 := sub_ne_zero.2 h34.symm
  field_simp

/-- Helper for `lemma3_2`: the bracket of (3.24) is invariant under the pull-back `W = (V ∘ B)/B′` of a vector field:
each divided difference of `W` differs from that of `V` at the image points by `c(u_{i+1} + u_i)/(ad − bc)`,
`u_i = V(Bzᵢ)(czᵢ + d)`, which cancels in the alternating sum. -/
theorem gl3_bracket_mob {a b c d : ℂ} {V W : ℂ → ℂ}
    (hW : ∀ z, c * z + d ≠ 0 → W z = V ((a * z + b) / (c * z + d)) * (c * z + d) ^ 2 / (a * d - b * c))
    {z₁ z₂ z₃ z₄ : ℂ} (h₁ : c * z₁ + d ≠ 0) (h₂ : c * z₂ + d ≠ 0) (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0)
    (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) :
    (W z₂ - W z₁) / (z₂ - z₁) - (W z₃ - W z₂) / (z₃ - z₂) + (W z₄ - W z₃) / (z₄ - z₃) - (W z₁ - W z₄) / (z₁ - z₄) =
      (V ((a * z₂ + b) / (c * z₂ + d)) - V ((a * z₁ + b) / (c * z₁ + d))) /
          ((a * z₂ + b) / (c * z₂ + d) - (a * z₁ + b) / (c * z₁ + d)) -
        (V ((a * z₃ + b) / (c * z₃ + d)) - V ((a * z₂ + b) / (c * z₂ + d))) /
          ((a * z₃ + b) / (c * z₃ + d) - (a * z₂ + b) / (c * z₂ + d)) +
        (V ((a * z₄ + b) / (c * z₄ + d)) - V ((a * z₃ + b) / (c * z₃ + d))) /
          ((a * z₄ + b) / (c * z₄ + d) - (a * z₃ + b) / (c * z₃ + d)) -
        (V ((a * z₁ + b) / (c * z₁ + d)) - V ((a * z₄ + b) / (c * z₄ + d))) /
          ((a * z₁ + b) / (c * z₁ + d) - (a * z₄ + b) / (c * z₄ + d)) := by
  rw [hW z₁ h₁, hW z₂ h₂, hW z₃ h₃, hW z₄ h₄, gl3_mob_sub h₁ h₂, gl3_mob_sub h₂ h₃, gl3_mob_sub h₃ h₄,
    gl3_mob_sub h₄ h₁]
  generalize V ((a * z₁ + b) / (c * z₁ + d)) = v₁
  generalize V ((a * z₂ + b) / (c * z₂ + d)) = v₂
  generalize V ((a * z₃ + b) / (c * z₃ + d)) = v₃
  generalize V ((a * z₄ + b) / (c * z₄ + d)) = v₄
  have s12 : z₂ - z₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have s23 : z₃ - z₂ ≠ 0 := sub_ne_zero.2 h23.symm
  have s34 : z₄ - z₃ ≠ 0 := sub_ne_zero.2 h34.symm
  have s41 : z₁ - z₄ ≠ 0 := sub_ne_zero.2 h41.symm
  field_simp
  ring

/-- **Lemma 2** (§3.6, l. 2690). `‖V(B(z))/B′(z)‖_cr = ‖V(z)‖_cr` for every Möbius transformation `B` (on `B⁻¹(Λ)`,
for `B` keeping the finite parts finite: `B(∞) ∉ Λ`). -/
theorem lemma3_2 {Λ : Set ExtPlane} (V : ℂ → ℂ) {a b c d : ℂ} (had : a * d - b * c ≠ 0)
    (hinf : c ≠ 0 → ((a / c : ℂ) : ExtPlane) ∉ Λ) :
    crNorm {x : ExtPlane | ∃ z : ℂ, x = z ∧ c * z + d ≠ 0 ∧ (((a * z + b) / (c * z + d) : ℂ) : ExtPlane) ∈ Λ}
        (fun z => V ((a * z + b) / (c * z + d)) / deriv (fun w => (a * w + b) / (c * w + d)) z) =
      crNorm Λ V := by
  set W : ℂ → ℂ := fun z => V ((a * z + b) / (c * z + d)) / deriv (fun w => (a * w + b) / (c * w + d)) z with hWdef
  have hW : ∀ z, c * z + d ≠ 0 → W z = V ((a * z + b) / (c * z + d)) * (c * z + d) ^ 2 / (a * d - b * c) := by
    intro z hz
    rw [hWdef]
    simp only
    rw [gl3_mob_deriv hz]
    field_simp
  have hmem : ∀ w : ℂ, (w : ExtPlane) ∈ {x : ExtPlane | ∃ z : ℂ, x = z ∧ c * z + d ≠ 0 ∧
      (((a * z + b) / (c * z + d) : ℂ) : ExtPlane) ∈ Λ} ↔
        c * w + d ≠ 0 ∧ (((a * w + b) / (c * w + d) : ℂ) : ExtPlane) ∈ Λ := by
    intro w
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      rw [OnePoint.coe_injective hz]
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨w, rfl, h1, h2⟩
  -- the distortion of `W` at `z` is the distortion of `V` at `B ∘ z`
  have hdist : ∀ z : Fin 4 → ℂ, Function.Injective z → (∀ i, c * z i + d ≠ 0) →
      crDistortion W (z 0) (z 1) (z 2) (z 3) =
        crDistortion V ((a * z 0 + b) / (c * z 0 + d)) ((a * z 1 + b) / (c * z 1 + d))
          ((a * z 2 + b) / (c * z 2 + d)) ((a * z 3 + b) / (c * z 3 + d)) := by
    intro z hz he
    unfold crDistortion
    rw [gl3_cr_mob had (he 0) (he 1) (he 2) (he 3) (hz.ne (by decide)) (hz.ne (by decide)),
      gl3_bracket_mob hW (he 0) (he 1) (he 2) (he 3) (hz.ne (by decide)) (hz.ne (by decide))
        (hz.ne (by decide)) (hz.ne (by decide))]
  -- `B` is injective on `{cz + d ≠ 0}`, with inverse `w ↦ (dw − b)/(a − cw)`
  have hBinj : ∀ z w : ℂ, c * z + d ≠ 0 → c * w + d ≠ 0 →
      (a * z + b) / (c * z + d) = (a * w + b) / (c * w + d) → z = w := by
    intro z w hz hw h
    have h' := gl3_mob_sub (a := a) (b := b) hz hw
    rw [h, sub_self, eq_comm, div_eq_zero_iff, mul_eq_zero] at h'
    rcases h' with (h' | h') | h'
    · exact absurd h' had
    · exact (sub_eq_zero.1 h').symm
    · exact absurd h' (mul_ne_zero hz hw)
  have hden : ∀ w : ℂ, (w : ExtPlane) ∈ Λ → a - c * w ≠ 0 := by
    intro w hw h0
    by_cases hc : c = 0
    · rw [hc, zero_mul, sub_zero] at h0
      exact had (by rw [h0, hc]; ring)
    · have : w = a / c := by field_simp; linear_combination -h0
      exact hinf hc (this ▸ hw)
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    obtain ⟨hinj, hzm⟩ := hz
    have he : ∀ i, c * z i + d ≠ 0 := fun i => ((hmem (z i)).1 (hzm i)).1
    set w : Fin 4 → ℂ := fun i => (a * z i + b) / (c * z i + d) with hw
    have hwinj : Function.Injective w := fun i j h => hinj (hBinj _ _ (he i) (he j) h)
    have hwm : ∀ i, (w i : ExtPlane) ∈ Λ := fun i => ((hmem (z i)).1 (hzm i)).2
    rw [hdist z hinj he]
    exact le_iSup₂_of_le (f := fun (w : Fin 4 → ℂ) (_ : Function.Injective w ∧ ∀ i, (w i : ExtPlane) ∈ Λ) =>
      ((‖crDistortion V (w 0) (w 1) (w 2) (w 3)‖₊ : ℝ≥0∞))) w ⟨hwinj, hwm⟩ le_rfl
  · refine iSup₂_le fun w hw => ?_
    obtain ⟨hinj, hwm⟩ := hw
    have hd : ∀ i, a - c * w i ≠ 0 := fun i => hden (w i) (hwm i)
    set z : Fin 4 → ℂ := fun i => (d * w i - b) / (a - c * w i) with hz
    have e1 : ∀ i, a * z i + b = (a * d - b * c) * w i / (a - c * w i) := by
      intro i
      rw [hz]
      simp only
      rw [eq_div_iff (hd i), add_mul, mul_assoc, div_mul_cancel₀ _ (hd i)]
      ring
    have e2 : ∀ i, c * z i + d = (a * d - b * c) / (a - c * w i) := by
      intro i
      rw [hz]
      simp only
      rw [eq_div_iff (hd i), add_mul, mul_assoc, div_mul_cancel₀ _ (hd i)]
      ring
    have he : ∀ i, c * z i + d ≠ 0 := fun i => by rw [e2 i]; exact div_ne_zero had (hd i)
    have hBz : ∀ i, (a * z i + b) / (c * z i + d) = w i := by
      intro i
      rw [e1 i, e2 i, div_div_div_cancel_right₀ (hd i), mul_div_cancel_left₀ _ had]
    have hzinj : Function.Injective z := fun i j h => hinj (by rw [← hBz i, ← hBz j, h])
    have hzm : ∀ i, (z i : ExtPlane) ∈ {x : ExtPlane | ∃ z : ℂ, x = z ∧ c * z + d ≠ 0 ∧
        (((a * z + b) / (c * z + d) : ℂ) : ExtPlane) ∈ Λ} := fun i =>
      (hmem (z i)).2 ⟨he i, by rw [hBz i]; exact hwm i⟩
    have h := hdist z hzinj he
    rw [hBz 0, hBz 1, hBz 2, hBz 3] at h
    rw [← h]
    exact le_iSup₂_of_le (f := fun (z : Fin 4 → ℂ) (_ : Function.Injective z ∧ ∀ i, (z i : ExtPlane) ∈
      {x : ExtPlane | ∃ z : ℂ, x = z ∧ c * z + d ≠ 0 ∧ (((a * z + b) / (c * z + d) : ℂ) : ExtPlane) ∈ Λ}) =>
      ((‖crDistortion W (z 0) (z 1) (z 2) (z 3)‖₊ : ℝ≥0∞))) z ⟨hzinj, hzm⟩ le_rfl

/-- **[CORRECTION]** (AUDIT4 G2) `lemma3_3_a`, `lemma3_3_b` carry the extra hypothesis `‖V(a, b, c, ∞)‖ ≤ M` (the quadruples through
`∞`, `crDistortionInf`): `crNorm` ranges over finite quadruples only, and for `Λ ∩ ℂ` bounded (`∞` isolated) the hypothesis
`V(z)/z² → 0` is empty; `Λ = {0, 1, 3, 5, ∞}`, `V = t z (z − 1)` has `crNorm = 0` and unbounded values.
**Lemma 3** (§3.6, l. 2700), first part. `V` with `‖V‖_cr < ∞`, normalized to vanish at `0, 1, ∞` (all in `Λ`),
is continuous on `Λ`, and for every `R > 0`, `|V(z₁) − V(z₂)| ≤ C |z₁ − z₂| log(1/|z₁ − z₂|)` for `z₁, z₂ ∈ Λ`,
`|z₁ − z₂| < 1/2`, `|z₁|, |z₂| ≤ R`, `C` depending only on `R` and `‖V‖_cr`. -/
theorem lemma3_3_a (R M : ℝ) :
    ∃ C : ℝ, ∀ (Λ : Set ExtPlane) (V : ℂ → ℂ), IsClosed Λ → ((0 : ℂ) : ExtPlane) ∈ Λ →
      ((1 : ℂ) : ExtPlane) ∈ Λ → (OnePoint.infty : ExtPlane) ∈ Λ → V 0 = 0 → V 1 = 0 →
      Tendsto (fun z => V z / z ^ 2) (cocompact ℂ ⊓ 𝓟 {z : ℂ | (z : ExtPlane) ∈ Λ}) (𝓝 0) →
      crNorm Λ V ≤ ENNReal.ofReal M →
      (∀ a b c : ℂ, (a : ExtPlane) ∈ Λ → (b : ExtPlane) ∈ Λ → (c : ExtPlane) ∈ Λ → a ≠ b → b ≠ c → a ≠ c →
        ‖crDistortionInf V a b c‖ ≤ M) →
        ContinuousOn V {z : ℂ | (z : ExtPlane) ∈ Λ} ∧
        ∀ z₁ z₂ : ℂ, (z₁ : ExtPlane) ∈ Λ → (z₂ : ExtPlane) ∈ Λ → ‖z₁ - z₂‖ < 1 / 2 → ‖z₁‖ ≤ R → ‖z₂‖ ≤ R →
          ‖V z₁ - V z₂‖ ≤ C * ‖z₁ - z₂‖ * Real.log (1 / ‖z₁ - z₂‖) := by
  sorry

/-- **Lemma 3** (§3.6, l. 2700), second part. If `V` vanishes at `0, 1, ∞`, then `|V(z)| ≤ D |z| log |z|` for
`z ∈ Λ`, `|z| > 2`, `D` depending only on `‖V‖_cr`. -/
theorem lemma3_3_b (M : ℝ) :
    ∃ D : ℝ, ∀ (Λ : Set ExtPlane) (V : ℂ → ℂ), IsClosed Λ → ((0 : ℂ) : ExtPlane) ∈ Λ →
      ((1 : ℂ) : ExtPlane) ∈ Λ → (OnePoint.infty : ExtPlane) ∈ Λ → V 0 = 0 → V 1 = 0 →
      Tendsto (fun z => V z / z ^ 2) (cocompact ℂ ⊓ 𝓟 {z : ℂ | (z : ExtPlane) ∈ Λ}) (𝓝 0) →
      crNorm Λ V ≤ ENNReal.ofReal M →
      (∀ a b c : ℂ, (a : ExtPlane) ∈ Λ → (b : ExtPlane) ∈ Λ → (c : ExtPlane) ∈ Λ → a ≠ b → b ≠ c → a ≠ c →
        ‖crDistortionInf V a b c‖ ≤ M) →
        ∀ z : ℂ, (z : ExtPlane) ∈ Λ → 2 < ‖z‖ → ‖V z‖ ≤ D * ‖z‖ * Real.log ‖z‖ := by
  sorry

/-- **Definition** (§3.6, l. 2733). `Z_cr`: the complex-valued functions on `Λ` with finite cross-ratio norm (the
quotient by the quadratic polynomials is taken in `thm3_8` through `crNorm`, whose kernel they are). -/
def zCrSet (Λ : Set ExtPlane) : Set (ℂ → ℂ) := {V | crNorm Λ V < ⊤}

/-- **Theorem 8** (§3.6, l. 2735). `Z_cr` is a Banach space with the norm `‖[V]‖ = ‖V‖_cr`: every Cauchy sequence
converges. -/
theorem thm3_8 {Λ : Set ExtPlane} (hΛ : IsClosed Λ) {V : ℕ → ℂ → ℂ} (hV : ∀ n, V n ∈ zCrSet Λ)
    (hcauchy : ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N, crNorm Λ (V m - V n) < ε) :
    ∃ W ∈ zCrSet Λ, Tendsto (fun n => crNorm Λ (V n - W)) atTop (𝓝 0) := by
  sorry

/-- **Definition** (§3.6, l. 2768–2774; §3.9, l. 3112–3118). The rational quadratic differential `φ_Q` with simple
poles at the four finite points of `Q` and `∬_ℂ |φ_Q| = 1`: `c/((z − z₁)(z − z₂)(z − z₃)(z − z₄))`, `c > 0` (the
book's `φ_Q` is determined up to a unimodular factor). -/
def phiQ (Q : Fin 4 → ℂ) (w : ℂ) : ℂ :=
  ((∫ v, ‖((v - Q 0) * (v - Q 1) * (v - Q 2) * (v - Q 3))⁻¹‖)⁻¹ : ℝ) *
    ((w - Q 0) * (w - Q 1) * (w - Q 2) * (w - Q 3))⁻¹

/-- **Definition** (§3.6, l. 2768; the quadruple `(1, 0, z, ∞)`). The four-pole differential of norm 1 for a quadruple
containing `∞`: `c/((z − z₁)(z − z₂)(z − z₃))`, `c > 0`. -/
def phiQInf (Q : Fin 3 → ℂ) (w : ℂ) : ℂ :=
  ((∫ v, ‖((v - Q 0) * (v - Q 1) * (v - Q 2))⁻¹‖)⁻¹ : ℝ) * ((w - Q 0) * (w - Q 1) * (w - Q 2))⁻¹

/-- **Formula (3.28)** (§3.6, l. 2778). For the functional `L = [μ]`, `‖V_μ‖_cr = sup_Q |L(φ_Q)|` over the quadruples
of distinct points of `Λ`. -/
theorem eq3_28 (Λ : Set ExtPlane) {μ : ℂ → ℂ} (hμ : ∃ k : ℝ, IsBeltramiCoeff μ univ k) :
    crNorm Λ (normalizedCauchyTOn univ μ) =
      ⨆ (Q : Fin 4 → ℂ) (_ : Function.Injective Q ∧ ∀ i, (Q i : ExtPlane) ∈ Λ),
        (‖∫ z, μ z * phiQ Q z‖₊ : ℝ≥0∞) := by
  sorry

end GardinerLakic2000
