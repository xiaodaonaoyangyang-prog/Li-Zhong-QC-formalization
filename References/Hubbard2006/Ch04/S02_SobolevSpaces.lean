import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.2: The Sobolev spaces `ℋ¹(U)` and `Cℋ¹(U)` (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 3258–3460.

**Conventions.** A function `f : ℂ → ℂ` is read on an open set `U ⊂ ℂ`. Its distributional first partials are a pair
`(g, h)` of functions with `∂f/∂x = g`, `∂f/∂y = h` in the sense of distributions on `U` (`IsH1With`). The Jacobian of
a pair of partials is `Jac = Re g · Im h − Im g · Re h` (`jacGen`); for `f` of class `C¹` it is
`LiZhongQC.jacobian f`. The norm of the real derivative matrix `[Df]` is the operator norm
`|f_z| + |f_z̄|` (`dNorm`); in the semi-norms (4.2.1) the Hilbert–Schmidt norm `|g|² + |h|²` is used
(it defines the same
topology, `‖M‖ ≤ ‖M‖_HS ≤ √2 ‖M‖`).

* Def. 4.2.1 (the space `ℋ¹(U)` of functions with distributional derivatives locally in `L²`; its subspace `Cℋ¹(U)` of
  continuous functions; the semi-norms (4.2.1)) — `IsH1With`, `IsH1`, `IsCH1`, `ch1Seminorm`
* Prop. 4.2.3 (`C^∞` functions are dense in `Cℋ¹(U)`) — `prop4_2_3`
* Prop. 4.2.4 (Jacobian formula for proper maps in `Cℋ¹`) — `prop4_2_4`
* Prop. 4.2.7 (a homeomorphism that is `K`-quasiconformal off a real line is `K`-quasiconformal) — `prop4_2_7`
* Prop. 4.2.11 (1) (composition with `C¹` functions stays in `Cℋ¹`) — `prop4_2_11_a`, `prop4_2_11_a'` (with the correction `jacobian k ≠ 0`)
* Prop. 4.2.11 (2) (calculus formulas for Jacobians and norms of composites) — `prop4_2_11_b`, `prop4_2_11_b'`
* Cor. 4.2.6 (area of the image equals the integral of the Jacobian, for any orientation-preserving homeomorphism in
  `Cℋ¹`; the installed LiZhongQC area formula assumes `K`-quasiconformality, a near miss) — `cor4_2_6`
* Cor. 4.2.12 (composition of quasiconformal maps with conformal maps) — exists: `GardinerLakic2000.prop1_1_c`
* Exercises 4.2.2, 4.2.5, 4.2.8–4.2.10 — omitted: exercise
-/

open Set MeasureTheory
open scoped ContDiff

namespace Hubbard2006

open LiZhongQC

/-- **`g`, `h` are the distributional partial derivatives of `f` in `U`, locally in `L²`** (Definition 4.2.1, H1:3258):
`U` is open, `f`, `g`, `h` are in `L²` on every compact subset of `U`, and for every compactly supported `C^∞` test
function `φ` with support in `U`, `∫ f ∂φ/∂x = −∫ g φ` and `∫ f ∂φ/∂y = −∫ h φ`. -/
def IsH1With (f g h : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧
    (∀ C ⊆ U, IsCompact C →
      MemLp f 2 (volume.restrict C) ∧ MemLp g 2 (volume.restrict C) ∧ MemLp h 2 (volume.restrict C)) ∧
    ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, f z * fderiv ℝ φ z 1 = -∫ z, g z * φ z) ∧ (∫ z, f z * fderiv ℝ φ z Complex.I = -∫ z, h z * φ z)

/-- **The Sobolev space `ℋ¹(U)`** (Definition 4.2.1): the functions with distributional derivatives locally in `L²`. -/
def IsH1 (f : ℂ → ℂ) (U : Set ℂ) : Prop := ∃ g h : ℂ → ℂ, IsH1With f g h U

/-- **The space `Cℋ¹(U)`** (Definition 4.2.1): the continuous functions of `ℋ¹(U)`. -/
def IsCH1 (f : ℂ → ℂ) (U : Set ℂ) : Prop := ContinuousOn f U ∧ IsH1 f U

/-- **The semi-norm (4.2.1) on a compact set `X ⊂ U`** (H1:3270): `sup_X |f| + ∫_X ‖[Df]‖²`, with `(g, h)` the
partials of `f` and the Hilbert–Schmidt norm `|g|² + |h|²` of `[Df]`. -/
noncomputable def ch1Seminorm (f g h : ℂ → ℂ) (X : Set ℂ) : ℝ :=
  (⨆ z : X, ‖f z‖) + ∫ z in X, (‖g z‖ ^ 2 + ‖h z‖ ^ 2)

/-- **The Jacobian of a pair of partials** `(g, h) = (f_x, f_y)`: `Jac = Re g · Im h − Im g · Re h =
|f_z|² − |f_z̄|²` (H1:3317). -/
def jacGen (g h : ℂ → ℂ) (z : ℂ) : ℝ := (g z).re * (h z).im - (g z).im * (h z).re

/-- **The operator norm of the derivative matrix** `[Df] = (f_x, f_y)`: `|f_z| + |f_z̄|`, with `f_z = (g − i h)/2`,
`f_z̄ = (g + i h)/2` (`LiZhongQC.genDz`, `LiZhongQC.genDzbar`). -/
noncomputable def dNorm (g h : ℂ → ℂ) (z : ℂ) : ℝ := ‖genDz g h z‖ + ‖genDzbar g h z‖

/-- **Proposition 4.2.3** (H1:3280). The `C^∞` functions are dense in `Cℋ¹(U)`: for a continuous `f ∈ ℋ¹(U)` with
partials `(g, h)`, every compact `X ⊂ U` and `ε > 0`, there is a `C^∞` function `φ` on `U` with
`‖f − φ‖_X < ε` for the semi-norm (4.2.1) (the topology of `Cℋ¹(U)` is defined by these semi-norms for all compact
`X`; a finite family of compact sets is covered by their union). -/
theorem prop4_2_3 {U : Set ℂ} {f g h : ℂ → ℂ} (hf : ContinuousOn f U) (hH : IsH1With f g h U)
    {X : Set ℂ} (hXU : X ⊆ U) (hX : IsCompact X) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℂ → ℂ, ContDiffOn ℝ ∞ φ U ∧
      ch1Seminorm (fun z => f z - φ z) (fun z => g z - fderiv ℝ φ z 1)
        (fun z => h z - fderiv ℝ φ z Complex.I) X < ε := by
  sorry

/-- **Proposition 4.2.4 (Jacobian formula)** (H1:3317). Let `U`, `V` be connected open subsets of `ℂ` and
`f : U → V` a proper map in `Cℋ¹` with partials `(g, h)`. Then there is an integer `d` (the degree of `f`) with
`d ∫_V φ = ∫_U (φ ∘ f) · Jac f` for every continuous function `φ` with compact support in `V`. *Reading:* the degree
(defined in the book by the action of `f*` on `H_c²`) is not modelled; the formula determines `d` uniquely (take
`φ ≥ 0`, `φ ≢ 0`), and the statement is that this integer exists (it is `deg f`). -/
theorem prop4_2_4 {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) (hV : IsOpen V) (hVc : IsConnected V)
    {f g h : ℂ → ℂ} (hf : ContinuousOn f U) (hmaps : MapsTo f U V)
    (hproper : ∀ C ⊆ V, IsCompact C → IsCompact (U ∩ f ⁻¹' C)) (hH : IsH1With f g h U) :
    ∃ d : ℤ, ∀ φ : ℂ → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (d : ℂ) * ∫ z in V, φ z = ∫ z in U, φ (f z) * (jacGen g h z : ℂ) := by
  sorry

/-- **Corollary 4.2.6 (Area and the Jacobian)** (H1:3345). Let `U`, `V ⊂ ℂ` be bounded open sets and `f : U → V` an
orientation-preserving homeomorphism in `Cℋ¹(U)` with partials `(g, h)`. Then for every open `W ⊂ U`,
`Area f(W) = ∫_W Jac f`. -/
theorem cor4_2_6 {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hUb : Bornology.IsBounded U)
    (hVb : Bornology.IsBounded V) {f g h : ℂ → ℂ} (hhom : IsHomeomorphOnto f U V) (hsp : IsSensePreserving f U)
    (hH : IsH1With f g h U) {W : Set ℂ} (hW : IsOpen W) (hWU : W ⊆ U) :
    volume (f '' W) = ∫⁻ z in W, ENNReal.ofReal (jacGen g h z) := by
  sorry

/-- A real affine line of the plane: `{p + t v | t ∈ ℝ}`, `v ≠ 0`. -/
def IsRealLine (l : Set ℂ) : Prop := ∃ p v : ℂ, v ≠ 0 ∧ l = {z | ∃ t : ℝ, z = p + t * v}

/-- **Proposition 4.2.7** (H1:3361). Let `U`, `V ⊂ ℂ` be open, `l` a real line, and `f : U → V` a homeomorphism that is
`K`-quasiconformal on `U ∖ l` (`LiZhongQC.IsKQC`). Then `f` is `K`-quasiconformal on `U`. -/
theorem prop4_2_7 {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {f : ℂ → ℂ} (hhom : IsHomeomorphOnto f U V)
    {l : Set ℂ} (hl : IsRealLine l) {K : ℝ} (hK : IsKQC f (U \ l) K) : IsKQC f U K := by
  sorry

/-- **Proposition 4.2.11 (1), first half** (H1:3414). If `f ∈ Cℋ¹(U)` and `g` is `C¹` on an open neighbourhood `W` of
`f(U)`, then `g ∘ f ∈ Cℋ¹(U)`. -/
theorem prop4_2_11_a {U W : Set ℂ} {f g : ℂ → ℂ} (hf : IsCH1 f U) (hW : IsOpen W) (hfW : f '' U ⊆ W)
    (hg : ContDiffOn ℝ 1 g W) : IsCH1 (g ∘ f) U := by
  sorry

/-- **Proposition 4.2.11 (1), second half** (H1:3414). If `f ∈ Cℋ¹(U)` and `k : V → U` is `C¹`, then
`f ∘ k ∈ Cℋ¹(V)` (`k` maps the open set `V` into `U`). *Correction to the book:* `k` needs the non-degeneracy
`jacobian k ≠ 0` (as in `prop4_2_11_b'`); without it the statement is false, e.g. `k(x, y) = (x, 0)` restricts `f` to a
line, where an `ℋ¹` function has only an `H^{1/2}` trace (take `f = Σ a_k cos(2^k x) e^{−2^k |y|}` with
`a_k = 2^{−k} k^{−1/2}`). -/
theorem prop4_2_11_a' {U V : Set ℂ} {f k : ℂ → ℂ} (hf : IsCH1 f U) (hV : IsOpen V) (hk : ContDiffOn ℝ 1 k V)
    (hkU : MapsTo k V U) (hJ : ∀ z ∈ V, jacobian k z ≠ 0) : IsCH1 (f ∘ k) V := by
  sorry

/-- **Proposition 4.2.11 (2), `g ∘ f`** (H1:3414). With `f ∈ Cℋ¹(U)` with partials `(p, q)` and `g` of class `C¹`
near `f(U)`, and `(a, b)` partials of `g ∘ f`, almost everywhere in `U`:
`Jac (g ∘ f) = (Jac g ∘ f) · Jac f` and `‖[D(g ∘ f)]‖ ≤ ‖[Dg ∘ f]‖ · ‖[Df]‖` (formulas (4.2.17), (4.2.18)). -/
theorem prop4_2_11_b {U W : Set ℂ} {f g p q a b : ℂ → ℂ} (hfp : IsH1With f p q U) (hW : IsOpen W)
    (hfW : f '' U ⊆ W) (hg : ContDiffOn ℝ 1 g W) (hgf : IsH1With (g ∘ f) a b U) :
    (∀ᵐ z ∂(volume.restrict U), jacGen a b z = jacobian g (f z) * jacGen p q z) ∧
      (∀ᵐ z ∂(volume.restrict U), dNorm a b z ≤ (‖dz g (f z)‖ + ‖dzbar g (f z)‖) * dNorm p q z) := by
  sorry

/-- **Proposition 4.2.11 (2), `f ∘ k`** (H1:3414). With `f ∈ Cℋ¹(U)` with partials `(p, q)` and `k : V → U` of
class `C¹` with nowhere vanishing Jacobian (*reading:* then the a.e. values `(p, q)(k z)` are well defined), and
`(a, b)` partials of `f ∘ k`, almost everywhere in `V`: `Jac (f ∘ k) = (Jac f ∘ k) · Jac k` and
`‖[D(f ∘ k)]‖ ≤ ‖[Df ∘ k]‖ · ‖[Dk]‖`. -/
theorem prop4_2_11_b' {U V : Set ℂ} {f k p q a b : ℂ → ℂ} (hfp : IsH1With f p q U) (hV : IsOpen V)
    (hk : ContDiffOn ℝ 1 k V) (hkU : MapsTo k V U) (hJ : ∀ z ∈ V, jacobian k z ≠ 0)
    (hfk : IsH1With (f ∘ k) a b V) :
    (∀ᵐ z ∂(volume.restrict V), jacGen a b z = jacGen p q (k z) * jacobian k z) ∧
      (∀ᵐ z ∂(volume.restrict V), dNorm a b z ≤ dNorm p q (k z) * (‖dz k z‖ + ‖dzbar k z‖)) := by
  sorry

end Hubbard2006
