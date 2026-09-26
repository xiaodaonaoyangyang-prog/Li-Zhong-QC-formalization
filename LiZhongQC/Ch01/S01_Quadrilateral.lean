import LiZhongQC.Basic
import LiZhongQC.Lemmas.Mobius
import LiZhongQC.Lemmas.RectangleRigidity
import LiZhongQC.Lemmas.SchwarzChristoffelRect

/-!
# §1 拓扑四边形的共形模 — The conformal modulus of a topological quadrilateral

* Definition 1.1 (topological quadrilateral)            — `IsTopQuad`, `TopQuad`
* §1.2 conformal equivalence of quadrilaterals          — `TopQuad.ConfEquiv`
* Theorem 1.1 (every quadrilateral is conformally a rectangle, unique up to similarity)
                                                         — `thm1_1_exists_rectangle`,
                                                           `thm1_1_rectangle_unique`
* Definition 1.2 (conformal modulus)                    — `quadModulusOf`, `TopQuad.modulus`
* Theorem 1.2 (`M(Q(z₁,z₂,z₃,z₄)) = 1/M(Q(z₂,z₃,z₄,z₁))`) — `thm1_2_modulus_rotate`
* Theorem 1.3 (conformal invariance)                    — `thm1_3_modulus_conformal_invariant`

## Encoding of "positive order"

The book orders the four vertices along the positively oriented boundary.  We encode
this by the existence of a conformal map of the Jordan domain onto the upper half-plane,
extending homeomorphically to the closures in `ℂ̄`, which sends the vertices to real
numbers in *cyclically* increasing order.  By the Riemann mapping theorem and the
boundary correspondence theorem this is equivalent to the book's condition, and the
cyclic formulation is manifestly invariant under the relabelling `Q ↦ Q(z₂,z₃,z₄,z₁)`.

The modulus is defined for raw data `(D, (z₁,z₂,z₃,z₄))` (`quadModulusOf`), so that
specific quadrilaterals such as `ℍ(∞,-1,0,ρ)` can be used in definitions without first
proving that they are quadrilaterals.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal Real

noncomputable section

namespace LiZhongQC

/-- Four real numbers in cyclically strictly increasing order: some cyclic shift of the
sequence is strictly increasing. -/
def CyclicStrictMono (x : Fin 4 → ℝ) : Prop :=
  ∃ k : Fin 4, StrictMono fun i => x (i + k)

/-- **Definition 1.1** (拓扑四边形).  `(D, (z₁,z₂,z₃,z₄))` is a topological quadrilateral
`D(z₁,z₂,z₃,z₄)`: `D` is a Jordan domain and `z₁,…,z₄ ∈ ∂D` are four boundary points in
positive cyclic order. -/
def IsTopQuad (D : Set ℂ) (v : Fin 4 → ExtPlane) : Prop :=
  IsJordanDomain D ∧ (∀ i, v i ∈ frontier (toExt D)) ∧
    ∃ (φ : ℂ → ℂ) (Φ : ExtPlane → ExtPlane) (x : Fin 4 → ℝ),
      IsConformalOnto φ D upperHalf ∧ IsHomeoExtension φ D upperHalf Φ ∧
        CyclicStrictMono x ∧ ∀ i, Φ (v i) = (((x i : ℝ) : ℂ) : ExtPlane)

/-- A topological quadrilateral `Q(z₁,z₂,z₃,z₄)` (bundled form of `IsTopQuad`). -/
structure TopQuad where
  /-- The Jordan domain `Q`. -/
  dom : Set ℂ
  /-- The vertices `z₁, z₂, z₃, z₄` (possibly `∞`). -/
  vert : Fin 4 → ExtPlane
  isTopQuad : IsTopQuad dom vert

/-- The relabelled quadrilateral `D(z₂,z₃,z₄,z₁)` is again a quadrilateral. -/
theorem IsTopQuad.rotate {D : Set ℂ} {v : Fin 4 → ExtPlane} (h : IsTopQuad D v) :
    IsTopQuad D (fun i => v (i + 1)) := by
  obtain ⟨hJ, hv, φ, Φ, x, h₁, h₂, ⟨k, hk⟩, h₃⟩ := h
  refine ⟨hJ, fun i => hv (i + 1), φ, Φ, fun i => x (i + 1), h₁, h₂, ⟨k - 1, ?_⟩,
    fun i => h₃ (i + 1)⟩
  have e : ∀ i : Fin 4, i + (k - 1) + 1 = i + k := fun i => by
    rw [add_assoc, sub_add_cancel]
  simpa only [e] using hk

namespace TopQuad

/-- `Q(z₂,z₃,z₄,z₁)`: the same domain and vertices, with the second vertex taken as the
first one.  Its first pair of opposite sides is the second pair of sides of `Q`. -/
def rotate (Q : TopQuad) : TopQuad := ⟨Q.dom, fun i => Q.vert (i + 1), Q.isTopQuad.rotate⟩

/-- The boundary side `(zᵢ, zᵢ₊₁)` of `Q` (indices mod 4), as a closed arc of `∂Q ⊆ ℂ̄`:
the two vertices together with the component of `∂Q ∖ {zᵢ, zᵢ₊₁}` not containing `zᵢ₊₂`.
Sides `0` and `2` form the first pair of opposite sides, sides `1` and `3` the second. -/
def side (Q : TopQuad) (i : Fin 4) : Set ExtPlane :=
  {p ∈ frontier (toExt Q.dom) | p = Q.vert i ∨ p = Q.vert (i + 1) ∨
    connectedComponentIn (frontier (toExt Q.dom) \ {Q.vert i, Q.vert (i + 1)}) p ≠
      connectedComponentIn (frontier (toExt Q.dom) \ {Q.vert i, Q.vert (i + 1)}) (Q.vert (i + 2))}

/-- §1.2 Two quadrilaterals are conformally equivalent: a conformal map of the domains
whose boundary extension maps vertices to the corresponding vertices. -/
def ConfEquiv (Q Q' : TopQuad) : Prop :=
  ∃ (f : ℂ → ℂ) (F : ExtPlane → ExtPlane), IsConformalOnto f Q.dom Q'.dom ∧
    IsHomeoExtension f Q.dom Q'.dom F ∧ ∀ i, F (Q.vert i) = Q'.vert i

/-- `Q'` is the image `f(Q)(f(z₁),f(z₂),f(z₃),f(z₄))` of `Q` under a map `f` of the plane
(used when the closure of `Q` lies in the domain of `f`, so that all vertices are finite). -/
def IsImageUnder (Q Q' : TopQuad) (f : ℂ → ℂ) : Prop :=
  Q'.dom = f '' Q.dom ∧ ∀ i, Q'.vert i = OnePoint.map f (Q.vert i)

end TopQuad

/-- The vertices `0, a, a + bi, bi` of the rectangle `R(0, a, a+bi, bi)`. -/
def rectVert (a b : ℝ) : Fin 4 → ExtPlane :=
  ![((0 : ℂ) : ExtPlane), (((a : ℝ) : ℂ) : ExtPlane), (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane),
    (((b : ℂ) * I : ℂ) : ExtPlane)]

/-- `f` is a standard conformal map (标准共形映射, §4.3) of `D(z₁,…,z₄)` onto the rectangle
`R(0, a, a+bi, bi)`: conformal, extending homeomorphically to the closures, and sending
the vertices `zᵢ` to `0, a, a+bi, bi` respectively. -/
def IsStdConformalMap (D : Set ℂ) (v : Fin 4 → ExtPlane) (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  0 < a ∧ 0 < b ∧ IsConformalOnto f D (rectangle a b) ∧
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f D (rectangle a b) F ∧
      ∀ i, F (v i) = rectVert a b i

/-- `D(z₁,…,z₄)` is conformally equivalent to the rectangle `R(0, a, a+bi, bi)`. -/
def EquivRect (D : Set ℂ) (v : Fin 4 → ExtPlane) (a b : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsStdConformalMap D v a b f

/-- **Definition 1.2** (共形模), for raw data: `M(D(z₁,…,z₄)) = a/b` where `D(z₁,…,z₄)` is
conformally equivalent to `R(0, a, a+bi, bi)` (well defined by Theorem 1.1). -/
def quadModulusOf (D : Set ℂ) (v : Fin 4 → ExtPlane) : ℝ :=
  sSup {m : ℝ | ∃ a b : ℝ, EquivRect D v a b ∧ m = a / b}

namespace TopQuad

/-- `f` is a standard conformal map of `Q` onto `R(0,a,a+bi,bi)`. -/
def IsStdConformalMap (Q : TopQuad) (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  LiZhongQC.IsStdConformalMap Q.dom Q.vert a b f

/-- `Q` is conformally equivalent to the rectangle `R(0, a, a+bi, bi)`. -/
def EquivRect (Q : TopQuad) (a b : ℝ) : Prop := LiZhongQC.EquivRect Q.dom Q.vert a b

/-- **Definition 1.2** (共形模): the conformal modulus `M(Q)`. -/
def modulus (Q : TopQuad) : ℝ := quadModulusOf Q.dom Q.vert

/-- "`Q` is a rectangle with vertices `z₁, z₂, z₃, z₄`": its domain and vertices are those
of `R(0,a,a+bi,bi)` moved by an orientation preserving rigid motion. -/
def IsRectangle (Q : TopQuad) : Prop :=
  ∃ (a b θ : ℝ) (c : ℂ), 0 < a ∧ 0 < b ∧
    Q.dom = (fun z => exp (θ * I) * z + c) '' rectangle a b ∧
    ∀ i, Q.vert i = OnePoint.map (fun z => exp (θ * I) * z + c) (rectVert a b i)

end TopQuad

/-! ## Theorem 1.1 -/

/-- The sign information carried by four reals in cyclically increasing order, used to
normalize them by a real Möbius transformation. -/
theorem cyclicStrictMono_signs {x : Fin 4 → ℝ} (hx : CyclicStrictMono x) :
    0 < (x 2 - x 3) * (x 2 - x 1) * (x 1 - x 3) ∧
      (x 2 - x 3) * (x 0 - x 1) / ((x 2 - x 1) * (x 0 - x 3)) < 0 ∧
      x 2 - x 1 ≠ 0 ∧ x 1 - x 3 ≠ 0 ∧ x 0 - x 3 ≠ 0 ∧ x 2 - x 3 ≠ 0 := by
  obtain ⟨j, hj⟩ := hx
  have h01 := hj (show (0 : Fin 4) < 1 by decide)
  have h12 := hj (show (1 : Fin 4) < 2 by decide)
  have h23 := hj (show (2 : Fin 4) < 3 by decide)
  fin_cases j <;> simp at h01 h12 h23 <;>
    refine ⟨?_, ?_, fun h => by linarith, fun h => by linarith, fun h => by linarith,
      fun h => by linarith⟩
  · nlinarith [mul_pos (mul_pos (sub_pos.2 h23) (sub_pos.2 h12)) (sub_pos.2 (h12.trans h23))]
  · exact div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) (by linarith))
      (mul_neg_of_pos_of_neg (by linarith) (by linarith))
  · nlinarith [mul_pos (mul_pos (sub_pos.2 h12) (sub_pos.2 h01)) (sub_pos.2 (h01.trans h12))]
  · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))
  · nlinarith [mul_pos (mul_pos (sub_pos.2 h01) (sub_pos.2 (h01.trans (h12.trans h23))))
      (sub_pos.2 (h12.trans h23))]
  · exact div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) (by linarith))
      (mul_neg_of_neg_of_pos (by linarith) (by linarith))
  · nlinarith [mul_pos (mul_pos (sub_pos.2 (h01.trans (h12.trans h23))) (sub_pos.2 h23))
      (sub_pos.2 (h01.trans h12))]
  · exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))

/-- First step of the proof of **Theorem 1.1**: every quadrilateral is conformally equivalent
to a half-plane quadrilateral `U(-1/k, -1, 1, 1/k)` with `0 < k < 1`.

Following the book: starting from the conformal map `φ` of `Q` onto `ℍ` (which sends the
vertices to reals `x₁, x₂, x₃, x₄` in cyclic order), compose with a Möbius transformation of `ℍ`
onto itself sending `x₁, x₂, x₃, x₄` to `-1/k, -1, 1, 1/k`; the number `k` is determined by the
cross ratio.  The transformation is the composition of `S : (x₂, x₃, x₄) ↦ (0, 1, ∞)`, which sends
`x₁` to some `λ < 0`, and `R : (0, 1, ∞, λ) ↦ (-1, 1, 1/k, -1/k)` with
`λ = -(1-k)²/(4k)`. -/
theorem thm1_1_halfPlane_normalForm (Q : TopQuad) :
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧ ∃ (φ : ℂ → ℂ) (Φ : ExtPlane → ExtPlane),
      IsConformalOnto φ Q.dom upperHalf ∧ IsHomeoExtension φ Q.dom upperHalf Φ ∧
      Φ (Q.vert 0) = (((-1 / k : ℝ) : ℂ) : ExtPlane) ∧ Φ (Q.vert 1) = (((-1 : ℝ) : ℂ) : ExtPlane) ∧
      Φ (Q.vert 2) = (((1 : ℝ) : ℂ) : ExtPlane) ∧ Φ (Q.vert 3) = (((1 / k : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨-, -, φ, Φ, x, hφ, hΦ, hcyc, hx⟩ := Q.isTopQuad
  obtain ⟨hdet, hlam, h21, h13, h03, h23⟩ := cyclicStrictMono_signs hcyc
  -- the cross-ratio parameter `λ = S(x₁) < 0` and the modulus parameter `k`
  obtain ⟨lam, hlam_def⟩ :
      ∃ lam : ℝ, lam = (x 2 - x 3) * (x 0 - x 1) / ((x 2 - x 1) * (x 0 - x 3)) := ⟨_, rfl⟩
  rw [← hlam_def] at hlam
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = -lam := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (μ ^ 2 + μ) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = μ ^ 2 + μ := by rw [hs]; exact Real.sq_sqrt (by positivity)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 + 2 * μ - 2 * s := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; nlinarith [mul_nonneg hs0 hμpos.le]
  have hk1 : k < 1 := by rw [hk]; nlinarith [mul_nonneg hs0 hμpos.le]
  have hk0' : k ≠ 0 := hk0.ne'
  have hl4 : lam * (4 * k) = -(1 - k) ^ 2 := by
    have hlm : lam = -μ := by linarith
    rw [hlm, hk]
    linear_combination 4 * hs2
  -- the Möbius transformation `S`
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℝ, a₁ = x 2 - x 3 := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : ℝ, b₁ = -((x 2 - x 3) * x 1) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = x 2 - x 1 := ⟨_, rfl⟩
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : ℝ, d₁ = -((x 2 - x 1) * x 3) := ⟨_, rfl⟩
  have hdetS : 0 < a₁ * d₁ - b₁ * c₁ := by
    have e : a₁ * d₁ - b₁ * c₁ = (x 2 - x 3) * (x 2 - x 1) * (x 1 - x 3) := by
      rw [ha₁, hb₁, hc₁, hd₁]; ring
    rw [e]; exact hdet
  -- the Möbius transformation `R`
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℝ, a₂ = -2 := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : ℝ, b₂ = 1 - k := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = -2 * k := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d₂ : ℝ, d₂ = k - 1 := ⟨_, rfl⟩
  have hdetR : 0 < a₂ * d₂ - b₂ * c₂ := by
    rw [ha₂, hb₂, hc₂, hd₂]; nlinarith
  have hS' : (a₁ : ℂ) * d₁ - b₁ * c₁ ≠ 0 := by exact_mod_cast hdetS.ne'
  have hR' : (a₂ : ℂ) * d₂ - b₂ * c₂ ≠ 0 := by exact_mod_cast hdetR.ne'
  set eS := mobiusHomeomorph a₁ b₁ c₁ d₁ hS' with heS_def
  set eR := mobiusHomeomorph a₂ b₂ c₂ d₂ hR' with heR_def
  have hSconf := isConformalOnto_mobius_upperHalf hdetS
  have hRconf := isConformalOnto_mobius_upperHalf hdetR
  have heS : ∀ w ∈ upperHalf, eS (w : ExtPlane) = ((mobiusFn a₁ b₁ c₁ d₁ w : ℂ) : ExtPlane) :=
    fun w hw => by
      rw [heS_def, mobiusHomeomorph_apply]
      exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetS.ne' hw)
  have heR : ∀ w ∈ upperHalf, eR (w : ExtPlane) = ((mobiusFn a₂ b₂ c₂ d₂ w : ℂ) : ExtPlane) :=
    fun w hw => by
      rw [heR_def, mobiusHomeomorph_apply]
      exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetR.ne' hw)
  have himgS : eS '' toExt upperHalf = toExt upperHalf := by
    rw [heS_def]; exact mobiusExt_image_toExt_upperHalf hdetS
  have himgR : eR '' toExt upperHalf = toExt upperHalf := by
    rw [heR_def]; exact mobiusExt_image_toExt_upperHalf hdetR
  have hconf1 := hSconf.comp hφ
  have hext1 := hΦ.comp_homeomorph hφ.mapsTo eS heS himgS
  have hconf2 := hRconf.comp hconf1
  have hext2 := hext1.comp_homeomorph hconf1.mapsTo eR heR himgR
  refine ⟨k, hk0, hk1, _, _, hconf2, hext2, ?_, ?_, ?_, ?_⟩
  · -- `x₁ ↦ λ ↦ -1/k`
    have hden : c₁ * x 0 + d₁ ≠ 0 := by
      rw [show c₁ * x 0 + d₁ = (x 2 - x 1) * (x 0 - x 3) by rw [hc₁, hd₁]; ring]
      exact mul_ne_zero h21 h03
    have hval : (a₁ * x 0 + b₁) / (c₁ * x 0 + d₁) = lam := by
      rw [hlam_def, show a₁ * x 0 + b₁ = (x 2 - x 3) * (x 0 - x 1) by rw [ha₁, hb₁]; ring,
        show c₁ * x 0 + d₁ = (x 2 - x 1) * (x 0 - x 3) by rw [hc₁, hd₁]; ring]
    have hden' : c₂ * lam + d₂ ≠ 0 := by
      have e : c₂ * lam + d₂ = -((1 - k) * (1 + k)) / 2 := by
        rw [hc₂, hd₂]
        linear_combination (-1 / 2 : ℝ) * hl4
      rw [e]
      exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (sub_ne_zero.2 (ne_of_gt hk1))
        (add_pos one_pos hk0).ne')) two_ne_zero
    have hval' : (a₂ * lam + b₂) / (c₂ * lam + d₂) = -1 / k := by
      rw [div_eq_div_iff hden' hk0', ha₂, hb₂, hc₂, hd₂]
      linear_combination -hl4
    simp only [Function.comp_apply, hx 0, heS_def, heR_def, mobiusHomeomorph_apply]
    rw [mobiusExt_ofReal_coe hden, hval, mobiusExt_ofReal_coe hden', hval']
  · -- `x₂ ↦ 0 ↦ -1`
    have hden : c₁ * x 1 + d₁ ≠ 0 := by
      rw [show c₁ * x 1 + d₁ = (x 2 - x 1) * (x 1 - x 3) by rw [hc₁, hd₁]; ring]
      exact mul_ne_zero h21 h13
    have hval : (a₁ * x 1 + b₁) / (c₁ * x 1 + d₁) = 0 := by
      rw [show a₁ * x 1 + b₁ = 0 by rw [ha₁, hb₁]; ring, zero_div]
    have hden' : c₂ * 0 + d₂ ≠ 0 := by
      rw [hd₂, mul_zero, zero_add]
      exact sub_ne_zero.2 hk1.ne
    have hval' : (a₂ * 0 + b₂) / (c₂ * 0 + d₂) = -1 := by
      rw [div_eq_iff hden', hb₂, hd₂]
      ring
    simp only [Function.comp_apply, hx 1, heS_def, heR_def, mobiusHomeomorph_apply]
    rw [mobiusExt_ofReal_coe hden, hval, mobiusExt_ofReal_coe hden', hval']
  · -- `x₃ ↦ 1 ↦ 1`
    have hden : c₁ * x 2 + d₁ ≠ 0 := by
      rw [show c₁ * x 2 + d₁ = (x 2 - x 1) * (x 2 - x 3) by rw [hc₁, hd₁]; ring]
      exact mul_ne_zero h21 h23
    have hval : (a₁ * x 2 + b₁) / (c₁ * x 2 + d₁) = 1 := by
      rw [div_eq_one_iff_eq hden]
      rw [ha₁, hb₁, hc₁, hd₁]
      ring
    have hden' : c₂ * 1 + d₂ ≠ 0 := by
      rw [hc₂, hd₂]
      intro h
      linarith
    have hval' : (a₂ * 1 + b₂) / (c₂ * 1 + d₂) = 1 := by
      rw [div_eq_one_iff_eq hden', ha₂, hb₂, hc₂, hd₂]
      ring
    simp only [Function.comp_apply, hx 2, heS_def, heR_def, mobiusHomeomorph_apply]
    rw [mobiusExt_ofReal_coe hden, hval, mobiusExt_ofReal_coe hden', hval']
  · -- `x₄ ↦ ∞ ↦ 1/k`
    have hden : c₁ * x 3 + d₁ = 0 := by
      rw [hc₁, hd₁]; ring
    have hc₂' : c₂ ≠ 0 := by
      rw [hc₂]; exact mul_ne_zero (by norm_num) hk0'
    have hval' : a₂ / c₂ = 1 / k := by
      rw [div_eq_div_iff hc₂' hk0', ha₂, hc₂]
      ring
    simp only [Function.comp_apply, hx 3, heS_def, heR_def, mobiusHomeomorph_apply]
    rw [mobiusExt_ofReal_coe_of_eq_zero hden, mobiusExt_ofReal_infty hc₂', hval']

/-- **Theorem 1.1** (existence).  Every topological quadrilateral is conformally equivalent
to some rectangle `R(0, a, a+bi, bi)`. -/
theorem thm1_1_exists_rectangle (Q : TopQuad) : ∃ a b : ℝ, Q.EquivRect a b := by
  obtain ⟨k, hk₀, hk₁, φ, Φ, hφ, hΦ, h0, h1, h2, h3⟩ := thm1_1_halfPlane_normalForm Q
  obtain ⟨ha, hb⟩ := scSide_pos hk₀ hk₁
  have hv := scMapExt_prevertices hk₀ hk₁
  refine ⟨scSideA k, scSideB k, scMap k ∘ φ, ha, hb, (isConformalOnto_scMap hk₀ hk₁).comp hφ,
    scMapExt k ∘ Φ, (isHomeoExtension_scMap hk₀ hk₁).comp hΦ hφ.mapsTo, fun i => ?_⟩
  fin_cases i
  · show scMapExt k (Φ (Q.vert 0)) = rectVert (scSideA k) (scSideB k) 0
    rw [h0]
    exact hv 0
  · show scMapExt k (Φ (Q.vert 1)) = rectVert (scSideA k) (scSideB k) 1
    rw [h1]
    exact hv 1
  · show scMapExt k (Φ (Q.vert 2)) = rectVert (scSideA k) (scSideB k) 2
    rw [h2]
    exact hv 2
  · show scMapExt k (Φ (Q.vert 3)) = rectVert (scSideA k) (scSideB k) 3
    rw [h3]
    exact hv 3

/-- The inverse of a continuous injection on a compact set is continuous on the image. -/
theorem continuousOn_invFunOn_image_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [Nonempty X] {F : X → Y} {K : Set X} (hK : IsCompact K)
    (hF : ContinuousOn F K) (hinj : InjOn F K) :
    ContinuousOn (Function.invFunOn F K) (F '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨F '' (K ∩ t), ((hK.inter_right ht).image_of_continuousOn
    (hF.mono inter_subset_left)).isClosed, ?_⟩
  ext w
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hwt, p, hp, rfl⟩
    rw [hinj.leftInvOn_invFunOn hp] at hwt
    exact ⟨⟨p, ⟨hp, hwt⟩, rfl⟩, p, hp, rfl⟩
  · rintro ⟨⟨p, ⟨hpK, hpt⟩, rfl⟩, -⟩
    rw [hinj.leftInvOn_invFunOn hpK]
    exact ⟨hpt, p, hpK, rfl⟩

/-- The closure in `ℂ̄` of a bounded set of `ℂ` is the image of its closure in `ℂ` (it does not
contain `∞`). -/
theorem closure_toExt_eq_toExt_closure_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A) :
    closure (toExt A) = toExt (closure A) := by
  unfold toExt
  refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
    (image_closure_subset_closure_image OnePoint.continuous_coe)
  exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hA.isCompact_closure⟩

/-- **Theorem 1.1** (uniqueness).  All rectangles conformally equivalent to `Q` differ only
by a similarity. -/
theorem thm1_1_rectangle_unique (Q : TopQuad) {a b a' b' : ℝ} (h : Q.EquivRect a b)
    (h' : Q.EquivRect a' b') : ∃ c : ℝ, 0 < c ∧ a' = c * a ∧ b' = c * b := by
  obtain ⟨f, ha, hb, hf, F, hF, hFv⟩ := h
  obtain ⟨f', ha', hb', hf', F', hF', hF'v⟩ := h'
  have hDo : IsOpen Q.dom := Q.isTopQuad.1.1
  have hKc : IsCompact (closure (toExt Q.dom)) := isClosed_closure.isCompact
  have hbdd : ∀ c d : ℝ, Bornology.IsBounded (rectangle c d) := fun c d => by
    rw [rectangle_eq_Ioo_reProdIm_Ioo]
    exact (Metric.isBounded_Ioo 0 c).reProdIm (Metric.isBounded_Ioo 0 d)
  have hclR : closure (toExt (rectangle a b)) = toExt (closure (rectangle a b)) :=
    closure_toExt_eq_toExt_closure_of_isBounded (hbdd a b)
  have hclR' : closure (toExt (rectangle a' b')) = toExt (closure (rectangle a' b')) :=
    closure_toExt_eq_toExt_closure_of_isBounded (hbdd a' b')
  have hmemR : ∀ z ∈ closure (rectangle a b), (z : ExtPlane) ∈ closure (toExt (rectangle a b)) :=
    fun z hz => by
      rw [hclR]
      exact mem_image_of_mem _ hz
  -- the continuous inverse of `F` on the closed rectangle
  have himF : F '' closure (toExt Q.dom) = closure (toExt (rectangle a b)) := hF.2.2.2
  have hFinvc : ContinuousOn (Function.invFunOn F (closure (toExt Q.dom)))
      (closure (toExt (rectangle a b))) := by
    rw [← himF]
    exact continuousOn_invFunOn_image_of_isCompact hKc hF.2.1 hF.2.2.1
  have hFinv_mem : ∀ w ∈ closure (toExt (rectangle a b)),
      Function.invFunOn F (closure (toExt Q.dom)) w ∈ closure (toExt Q.dom) := fun w hw => by
    rw [← himF] at hw
    exact Function.invFunOn_mem hw
  have hFFinv : ∀ w ∈ closure (toExt (rectangle a b)),
      F (Function.invFunOn F (closure (toExt Q.dom)) w) = w := fun w hw => by
    rw [← himF] at hw
    exact Function.invFunOn_eq hw
  have hFinvF : ∀ p ∈ closure (toExt Q.dom),
      Function.invFunOn F (closure (toExt Q.dom)) (F p) = p :=
    fun p hp => hF.2.2.1.leftInvOn_invFunOn hp
  -- the composite `G = F' ∘ F⁻¹` of the closed rectangles
  have hGc : ContinuousOn (fun w => F' (Function.invFunOn F (closure (toExt Q.dom)) w))
      (closure (toExt (rectangle a b))) :=
    hF'.2.1.comp hFinvc hFinv_mem
  have hGinj : InjOn (fun w => F' (Function.invFunOn F (closure (toExt Q.dom)) w))
      (closure (toExt (rectangle a b))) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 := hF'.2.2.1 (hFinv_mem w₁ hw₁) (hFinv_mem w₂ hw₂) heq
    rw [← hFFinv w₁ hw₁, ← hFFinv w₂ hw₂, h1]
  have hGimg : (fun w => F' (Function.invFunOn F (closure (toExt Q.dom)) w)) ''
      closure (toExt (rectangle a b)) = closure (toExt (rectangle a' b')) := by
    rw [← hF'.2.2.2]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hFinv_mem u hu, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨F p, ?_, ?_⟩
      · rw [← himF]
        exact mem_image_of_mem F hp
      · show F' (Function.invFunOn F (closure (toExt Q.dom)) (F p)) = F' p
        rw [hFinvF p hp]
  -- the induced map `g` of the closed rectangles in `ℂ`
  have hg_spec : ∀ z w : ℂ, F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)) =
      (w : ExtPlane) → Function.invFun ((↑) : ℂ → ExtPlane)
        (F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane))) = w := by
    intro z w hzw
    apply OnePoint.coe_injective
    rw [Function.invFun_eq ⟨w, hzw.symm⟩, hzw]
  have hG_coe : ∀ z ∈ closure (rectangle a b), ∃ w ∈ closure (rectangle a' b'),
      F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)) = (w : ExtPlane) := by
    intro z hz
    have h1 : F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)) ∈
        closure (toExt (rectangle a' b')) := by
      rw [← hGimg]
      exact mem_image_of_mem _ (hmemR z hz)
    rw [hclR'] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    exact ⟨w, hw, hwe.symm⟩
  set g : ℂ → ℂ := fun z => Function.invFun ((↑) : ℂ → ExtPlane)
    (F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane))) with hg
  have hgG : ∀ z ∈ closure (rectangle a b),
      (g z : ExtPlane) = F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hG_coe z hz
    rw [hw]
    exact congrArg _ (hg_spec z w hw)
  have hgc : ContinuousOn g (closure (rectangle a b)) := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    have h1 : ContinuousOn
        (fun z : ℂ => F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)))
        (closure (rectangle a b)) :=
      hGc.comp OnePoint.continuous_coe.continuousOn hmemR
    exact h1.congr fun z hz => hgG z hz
  have hginj : InjOn g (closure (rectangle a b)) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have h1 : F' (Function.invFunOn F (closure (toExt Q.dom)) (z₁ : ExtPlane)) =
        F' (Function.invFunOn F (closure (toExt Q.dom)) (z₂ : ExtPlane)) := by
      rw [← hgG z₁ hz₁, ← hgG z₂ hz₂, heq]
    exact OnePoint.coe_injective (hGinj (hmemR z₁ hz₁) (hmemR z₂ hz₂) h1)
  have hgimg : g '' closure (rectangle a b) = closure (rectangle a' b') := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hGw⟩ := hG_coe z hz
      rw [show g z = w from hg_spec z w hGw]
      exact hw
    · intro hw
      have h1 : (w : ExtPlane) ∈ (fun w => F' (Function.invFunOn F (closure (toExt Q.dom)) w)) ''
          closure (toExt (rectangle a b)) := by
        rw [hGimg, hclR']
        exact mem_image_of_mem _ hw
      obtain ⟨p, hp, hpw⟩ := h1
      rw [hclR] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      exact ⟨z, hz, hg_spec z w hpw⟩
  -- on the open rectangle, `g = f' ∘ f⁻¹`, which is conformal
  have hginv : IsConformalOnto (f' ∘ Function.invFunOn f Q.dom) (rectangle a b)
      (rectangle a' b') := hf'.comp (hf.symm hDo)
  have hgEq : EqOn g (f' ∘ Function.invFunOn f Q.dom) (rectangle a b) := by
    intro z hz
    have hz' : z ∈ f '' Q.dom := by
      rw [hf.2.2]
      exact hz
    have hpD : Function.invFunOn f Q.dom z ∈ Q.dom := Function.invFunOn_mem hz'
    have hfp : f (Function.invFunOn f Q.dom z) = z := Function.invFunOn_eq hz'
    have hpK : ((Function.invFunOn f Q.dom z : ℂ) : ExtPlane) ∈ closure (toExt Q.dom) :=
      subset_closure (mem_image_of_mem _ hpD)
    have hFp : F ((Function.invFunOn f Q.dom z : ℂ) : ExtPlane) = (z : ExtPlane) := by
      rw [hF.1 _ hpD, hfp]
    have hGz : F' (Function.invFunOn F (closure (toExt Q.dom)) (z : ExtPlane)) =
        ((f' (Function.invFunOn f Q.dom z) : ℂ) : ExtPlane) := by
      rw [← hFp, hFinvF _ hpK, hF'.1 _ hpD]
    exact hg_spec z _ hGz
  have hgconf : IsConformalOnto g (rectangle a b) (rectangle a' b') :=
    ⟨hginv.1.congr hgEq, hginv.2.1.congr hgEq.symm, hgEq.image_eq.trans hginv.2.2⟩
  -- the vertices
  have hvert : ∀ i : Fin 4,
      F' (Function.invFunOn F (closure (toExt Q.dom)) (rectVert a b i)) = rectVert a' b' i := by
    intro i
    have hvK : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (Q.isTopQuad.2.1 i)
    rw [← hFv i, hFinvF _ hvK, hF'v i]
  have hv0 : rectVert a b 0 = ((0 : ℂ) : ExtPlane) := rfl
  have hv1 : rectVert a b 1 = (((a : ℝ) : ℂ) : ExtPlane) := rfl
  have hv2 : rectVert a b 2 = (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv3 : rectVert a b 3 = (((b : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv0' : rectVert a' b' 0 = ((0 : ℂ) : ExtPlane) := rfl
  have hv1' : rectVert a' b' 1 = (((a' : ℝ) : ℂ) : ExtPlane) := rfl
  have hv2' : rectVert a' b' 2 = (((a' : ℂ) + (b' : ℂ) * I : ℂ) : ExtPlane) := rfl
  have hv3' : rectVert a' b' 3 = (((b' : ℂ) * I : ℂ) : ExtPlane) := rfl
  have h0 : g 0 = 0 := hg_spec 0 0 (by have := hvert 0; rwa [hv0, hv0'] at this)
  have h1 : g (a : ℂ) = (a' : ℂ) := hg_spec _ _ (by have := hvert 1; rwa [hv1, hv1'] at this)
  have h2 : g ((a : ℂ) + (b : ℂ) * I) = (a' : ℂ) + (b' : ℂ) * I :=
    hg_spec _ _ (by have := hvert 2; rwa [hv2, hv2'] at this)
  have h3 : g ((b : ℂ) * I) = (b' : ℂ) * I := hg_spec _ _ (by have := hvert 3; rwa [hv3, hv3'] at this)
  -- rigidity of rectangles
  obtain ⟨hab, -⟩ := rect_rigidity ha hb ha' hb' hgconf hgc hginj hgimg h0 h1 h2 h3
  refine ⟨a' / a, div_pos ha' ha, (div_mul_cancel₀ a' ha.ne').symm, ?_⟩
  rw [hab]
  exact (div_mul_cancel₀ b' hb.ne').symm

/-- The modulus is the ratio `a/b` of any rectangle conformally equivalent to `Q`
(the set in `quadModulusOf` is the singleton `{a/b}` by Theorem 1.1). -/
theorem modulus_eq_of_equivRect (Q : TopQuad) {a b : ℝ} (h : Q.EquivRect a b) :
    Q.modulus = a / b := by
  have hset : {m : ℝ | ∃ a b : ℝ, EquivRect Q.dom Q.vert a b ∧ m = a / b} = {a / b} := by
    ext m
    constructor
    · rintro ⟨a', b', h', rfl⟩
      obtain ⟨c, hc, rfl, rfl⟩ := thm1_1_rectangle_unique Q h h'
      exact mul_div_mul_left a b hc.ne'
    · rintro rfl
      exact ⟨a, b, h, rfl⟩
  unfold TopQuad.modulus quadModulusOf
  rw [hset, csSup_singleton]

/-- The modulus of a quadrilateral is positive. -/
theorem modulus_pos (Q : TopQuad) : 0 < Q.modulus := by
  obtain ⟨a, b, h⟩ := thm1_1_exists_rectangle Q
  rw [modulus_eq_of_equivRect Q h]
  obtain ⟨_, ha, hb, -⟩ := h
  exact div_pos ha hb

/-- The Schwarz–Christoffel computation in the proof of **Theorem 1.1**: the function
`w = ∫_{-1/k}^{z} dζ/√((1-ζ²)(1-k²ζ²))` maps `U(-1/k,-1,1,1/k)` onto a rectangle with sides
`a = ∫_{1}^{1/k} dx/√((x²-1)(1-k²x²))` and `b = ∫_{-1}^{1} dx/√((1-x²)(1-k²x²))`.

*Correction.*  The book writes `a = ∫_{-1/k}^{-1} dx/√((1-x²)(1-k²x²))`.  On `(-1/k, -1)` one
has `1 - x² < 0` and `1 - k²x² > 0`, so that integrand is imaginary; substituting `x ↦ -x` and
taking the positive root gives the real form used here.  `b` is unaffected. -/
theorem thm1_1_elliptic_modulus {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    quadModulusOf upperHalf ![(((-1 / k : ℝ) : ℂ) : ExtPlane), (((-1 : ℝ) : ℂ) : ExtPlane),
      (((1 : ℝ) : ℂ) : ExtPlane), (((1 / k : ℝ) : ℂ) : ExtPlane)] =
      (∫ x in (1 : ℝ)..(1 / k), 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))) /
        (∫ x in (-1 : ℝ)..1, 1 / Real.sqrt ((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))) := by
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 4 → ExtPlane, v = ![(((-1 / k : ℝ) : ℂ) : ExtPlane),
      (((-1 : ℝ) : ℂ) : ExtPlane), (((1 : ℝ) : ℂ) : ExtPlane), (((1 / k : ℝ) : ℂ) : ExtPlane)] :=
    ⟨_, rfl⟩
  rw [← hvdef]
  have hvj : ∀ j : Fin 4, v j = (((scPrevertex k j : ℝ) : ℂ) : ExtPlane) := by
    intro j
    rw [hvdef]
    fin_cases j <;> rfl
  have hQ : IsTopQuad upperHalf v := by
    refine ⟨scExt_isJordanDomain_upperHalf, fun i => ?_, id, id, scPrevertex k,
      ⟨differentiableOn_id, injOn_id _, image_id _⟩, scExt_isHomeoExtension_id upperHalf,
      ⟨0, ?_⟩, fun i => ?_⟩
    · rw [hvj]
      exact scExt_ofReal_mem_frontier_toExt_upperHalf _
    · simpa using scPrevertex_strictMono hk₀ hk₁
    · rw [hvj]
      rfl
  have hE : EquivRect upperHalf v (scSideA k) (scSideB k) :=
    ⟨scMap k, (scSide_pos hk₀ hk₁).1, (scSide_pos hk₀ hk₁).2, isConformalOnto_scMap hk₀ hk₁,
      scMapExt k, isHomeoExtension_scMap hk₀ hk₁, fun i => by
        rw [hvj]
        exact scMapExt_prevertices hk₀ hk₁ i⟩
  exact modulus_eq_of_equivRect ⟨upperHalf, v, hQ⟩ hE

/-! ## Theorems 1.2 and 1.3 -/

/-- The rigid motion `w ↦ -i w + a i` maps `R(0,a,a+bi,bi)` conformally onto `R(0,b,b+ai,ai)`. -/
theorem rectangle_rotation_conformal {a b : ℝ} :
    IsConformalOnto (fun w : ℂ => -I * w + (a : ℂ) * I) (rectangle a b) (rectangle b a) := by
  refine ⟨(by fun_prop : Differentiable ℂ fun w : ℂ => -I * w + (a : ℂ) * I).differentiableOn,
    fun w₁ _ w₂ _ h => ?_, ?_⟩
  · simp only at h
    exact mul_left_cancel₀ (neg_ne_zero.2 I_ne_zero) (add_right_cancel h)
  · ext u
    simp only [mem_image, rectangle, mem_setOf_eq]
    constructor
    · rintro ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
      have hre : (-I * w + (a : ℂ) * I).re = w.im := by simp
      have him : (-I * w + (a : ℂ) * I).im = a - w.re := by simp; ring
      rw [hre, him]
      exact ⟨h3, h4, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨(a : ℂ) + I * u, ?_, ?_⟩
      · have hre : ((a : ℂ) + I * u).re = a - u.im := by simp; ring
        have him : ((a : ℂ) + I * u).im = u.re := by simp
        rw [hre, him]
        exact ⟨by linarith, by linarith, h1, h2⟩
      · linear_combination (-u) * I_sq

/-- The rigid motion `w ↦ -i w + a i` as a map of `ℂ̄`. -/
theorem rotation_mobiusExt_coe (a : ℝ) (z : ℂ) :
    mobiusExt (-I) ((a : ℂ) * I) 0 1 (z : ExtPlane) = ((-I * z + (a : ℂ) * I : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simp)]
  congr 1
  simp [mobiusFn]

theorem rotation_det (a : ℝ) : (-I) * 1 - (a : ℂ) * I * 0 ≠ 0 := by simp

theorem rectangle_rotation_image {a b : ℝ} :
    mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a) '' toExt (rectangle a b) =
      toExt (rectangle b a) := by
  simp only [toExt]
  rw [← (rectangle_rotation_conformal (a := a) (b := b)).2.2, ← image_comp, ← image_comp]
  congr 1
  funext z
  simp only [Function.comp_apply, mobiusHomeomorph_apply, rotation_mobiusExt_coe]

/-- The rigid motion `w ↦ -i w + a i` sends the vertices `a, a+bi, bi, 0` of `R(0,a,a+bi,bi)` to the
vertices `0, b, b+ai, ai` of `R(0,b,b+ai,ai)`. -/
theorem rectVert_rotation {a b : ℝ} (i : Fin 4) :
    mobiusExt (-I) ((a : ℂ) * I) 0 1 (rectVert a b (i + 1)) = rectVert b a i := by
  fin_cases i
  · show mobiusExt (-I) ((a : ℂ) * I) 0 1 (((a : ℝ) : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
    rw [rotation_mobiusExt_coe]
    congr 1
    ring
  · show mobiusExt (-I) ((a : ℂ) * I) 0 1 (((a : ℂ) + (b : ℂ) * I : ℂ) : ExtPlane) =
      (((b : ℝ) : ℂ) : ExtPlane)
    rw [rotation_mobiusExt_coe]
    congr 1
    linear_combination (-(b : ℂ)) * I_sq
  · show mobiusExt (-I) ((a : ℂ) * I) 0 1 (((b : ℂ) * I : ℂ) : ExtPlane) =
      (((b : ℂ) + (a : ℂ) * I : ℂ) : ExtPlane)
    rw [rotation_mobiusExt_coe]
    congr 1
    linear_combination (-(b : ℂ)) * I_sq
  · show mobiusExt (-I) ((a : ℂ) * I) 0 1 ((0 : ℂ) : ExtPlane) = (((a : ℂ) * I : ℂ) : ExtPlane)
    rw [rotation_mobiusExt_coe]
    congr 1
    ring

/-- **Theorem 1.2**: `M(Q(z₁,z₂,z₃,z₄)) = 1 / M(Q(z₂,z₃,z₄,z₁))`.

If `f` maps `Q(z₁,z₂,z₃,z₄)` onto `R(0,a,a+bi,bi)`, then `w ↦ -i w + a i` composed with `f` maps
`Q(z₂,z₃,z₄,z₁)` onto `R(0,b,b+ai,ai)`, whose modulus is `b/a`. -/
theorem thm1_2_modulus_rotate (Q : TopQuad) : Q.modulus = 1 / Q.rotate.modulus := by
  obtain ⟨a, b, f, ha, hb, hf, F, hF, hv⟩ := thm1_1_exists_rectangle Q
  have hrot : Q.rotate.EquivRect b a := by
    refine ⟨(fun w : ℂ => -I * w + (a : ℂ) * I) ∘ f, hb, ha, rectangle_rotation_conformal.comp hf,
      (mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a)) ∘ F,
      hF.comp_homeomorph hf.mapsTo _ (fun w _ => ?_) rectangle_rotation_image, fun i => ?_⟩
    · rw [mobiusHomeomorph_apply, rotation_mobiusExt_coe]
    · show mobiusHomeomorph (-I) ((a : ℂ) * I) 0 1 (rotation_det a) (F (Q.vert (i + 1))) =
        rectVert b a i
      rw [hv (i + 1), mobiusHomeomorph_apply, rectVert_rotation]
  rw [modulus_eq_of_equivRect Q ⟨f, ha, hb, hf, F, hF, hv⟩, modulus_eq_of_equivRect Q.rotate hrot,
    one_div_div]

/-- **Theorem 1.3**: the modulus of a topological quadrilateral is a conformal invariant.

Compose the conformal equivalence `Q → Q'` with a standard conformal map of `Q'` onto a
rectangle. -/
theorem thm1_3_modulus_conformal_invariant {Q Q' : TopQuad} (h : Q.ConfEquiv Q') :
    Q.modulus = Q'.modulus := by
  obtain ⟨f, F, hf, hF, hv⟩ := h
  obtain ⟨a, b, g, ha, hb, hg, G, hG, hvG⟩ := thm1_1_exists_rectangle Q'
  have hQ : Q.EquivRect a b :=
    ⟨g ∘ f, ha, hb, hg.comp hf, G ∘ F, hG.comp hF hf.mapsTo, fun i => by
      simp only [Function.comp_apply, hv i, hvG i]⟩
  rw [modulus_eq_of_equivRect Q hQ, modulus_eq_of_equivRect Q' ⟨g, ha, hb, hg, G, hG, hvG⟩]

end LiZhongQC
