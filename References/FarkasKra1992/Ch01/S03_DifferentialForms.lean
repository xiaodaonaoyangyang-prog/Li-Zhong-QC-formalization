import References.FarkasKra1992.Ch01.S02_TopologyOfRiemannSurfaces
import References.Forster1981.Ch01.S10_TheIntegrationOfDifferentialForms
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Farkas–Kra, Chapter I §3: Differential forms

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. I §3 (`full.md` FK1:855–1174).

Conventions: forms are those of `Forster1981` Part A (coefficient model): a 1-form is a pair `(u, v)` of families of
coefficients of `dz` and `dz̄` in the preferred chart at each point (`Forster1981.Form1`; that the pair is a well defined
form, i.e. satisfies the transformation law (3.1.2), is `Form1.IsForm`, assumed in the statements), a 2-form the coefficient
of `dz ∧ dz̄` (`Forster1981.Form2`; `dz ∧ dz̄ = −2i dx ∧ dy`, (3.2.3)). Exterior derivative `d`, `∂ = d′`, `∂̄ = d″`,
the exterior product, line and surface integrals, harmonic functions (`Forster1981.IsHarmonicOn`: `d′d″f = 0` for smooth
`f`) and closed/exact forms are Forster's (`C^∞` in place of FK's `C¹`/`C²` classes; every statement below is for smooth
data). The conjugation `*` (3.7.1) is `starForm`. "Smooth" in the statements is `Form1.IsSmoothOn`. A *domain* `Y` is
open.

* I.3.1–I.3.2 (0-, 1-, 2-forms, complex notation) — exists: `Forster1981.Form1`, `Forster1981.Form2`, `Forster1981.Form1.IsForm`
* I.3.3 (exterior algebra) — exists: `Forster1981.Form1.wedge`
* I.3.4 (integrals of forms over chains) — exists: `Forster1981.HasCurveIntegralRS`, `Forster1981.HasIntegral2`
* I.3.5 (exterior derivative) — exists: `Forster1981.Form1.d`
* I.3.5 Stokes' theorem — deferred: chains and regions with piecewise differentiable boundary (Forster's 10.19 covers discs and annuli)
* I.3.6 (`∂`, `∂̄`) — exists: `Forster1981.Form1.dHol`, `Forster1981.Form1.dBar`
* I.3.7 (conjugation `*` on 1-forms) — `starForm`
* I.3.8 (exact and closed forms, harmonic functions) — exists: `Forster1981.Form1.IsExact`, `Forster1981.Form1.IsClosed`, `Forster1981.IsHarmonicOn`
* I.3.8 (co-exact, co-closed, harmonic forms) — `IsCoExact`, `IsCoClosed`, `IsHarmonicForm`
* I.3.8 (3.8.1) — `para1_3_8`
* Proposition I.3.8 — `prop1_3_8`
* I.3.9 (holomorphic 1-form) — `IsHolomorphicForm`
* Proposition I.3.9, part (a) — `prop1_3_9_a`
* Proposition I.3.9, part (b) — `prop1_3_9_b`
* I.3.10 (harmonic forms and their decomposition) — `conjForm`, `para1_3_10_a`, `para1_3_10_b`
* Theorem I.3.11 — `thm1_3_11`
* Corollary I.3.11 — `cor1_3_11`

Omitted (U−): I.3.7 on functions and 2-forms (not used), `** = (−1)^k`, the geometric interpretation of `*df`, the
remarks on well-definedness, the pairing `⟨c, ω⟩` of I.3.8 (Forster's periods), the remark after I.3.4.
-/

open scoped Manifold ContDiff Topology ComplexConjugate
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The conjugation `*` of 1-forms** (Ch. I §3.7, (3.7.1)–(3.7.2)). For `ω = f dx + g dy`, `*ω = −g dx + f dy`; in complex
notation `ω = u dz + v dz̄`, `*ω = −i u dz + i v dz̄`. -/
def starForm (w : Form1 X) : Form1 X := (fun x z => -Complex.I * w.1 x z, fun x z => Complex.I * w.2 x z)

/-- **The complex conjugate form** (Ch. I §3.10, helper). For `ω = u dz + v dz̄`, `ω̄ = v̄ dz + ū dz̄`. -/
def conjForm (w : Form1 X) : Form1 X := (fun x z => conj (w.2 x z), fun x z => conj (w.1 x z))

/-- **Co-exact** (Ch. I §3.8). A 1-form `ω` is *co-exact* (on `Y`) if `*ω` is exact. -/
def IsCoExact (w : Form1 X) (Y : Set X) : Prop := (starForm w).IsExact Y

/-- **Co-closed** (Ch. I §3.8). A 1-form `ω` is *co-closed* (on `Y`) if `*ω` is closed. -/
def IsCoClosed (w : Form1 X) (Y : Set X) : Prop := (starForm w).IsClosed Y

/-- **Harmonic 1-form** (Ch. I §3.8). A 1-form `ω` is *harmonic* (on `Y`) provided it is locally given by `df` with `f` a
harmonic function. -/
def IsHarmonicForm (w : Form1 X) (Y : Set X) : Prop :=
  ∀ a ∈ Y, ∃ V ∈ 𝓝 a, V ⊆ Y ∧ ∃ f : X → ℂ, IsHarmonicOn f V ∧ Form1.EqOn w (dForm f) V

/-- **Holomorphic 1-form** (Ch. I §3.9). A 1-form `ω` is *holomorphic* (on `Y`) provided that locally `ω = df` with `f`
holomorphic. (Near miss: `Forster1981.Form1.IsHolomorphicOn`, of type `(1, 0)` with holomorphic coefficient; the two agree,
Proposition I.3.9(b).) -/
def IsHolomorphicForm (w : Form1 X) (Y : Set X) : Prop :=
  ∀ a ∈ Y, ∃ V ∈ 𝓝 a, V ⊆ Y ∧ ∃ f : X → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f V ∧ Form1.EqOn w (dForm f) V

/-- **Unlabelled** (Ch. I §3.8, formula (3.8.1)). For every smooth function `f`, `−2i ∂̄∂f = Δf = d*df`: in the chart at
`x`, the coefficient of `d(*df)` (a multiple of `dz ∧ dz̄`, with `dx ∧ dy = (i/2) dz ∧ dz̄`) is `(i/2) Δ(f ∘ φ_x⁻¹)`. -/
theorem para1_3_8 {f : X → ℂ} (hf : ∀ x, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x) (x : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    Form1.d (starForm (dForm f)) x z =
      (Complex.I / 2) * Laplacian.laplacian (fun u => f ((chartAt ℂ x).symm u)) z := by
  sorry

/-- **Proposition I.3.8** (Ch. I §3.8). A differential `ω` is harmonic if and only if it is closed and co-closed. -/
theorem prop1_3_8 {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) :
    IsHarmonicForm w Y ↔ w.IsClosed Y ∧ IsCoClosed w Y := by
  sorry

/-- **Proposition I.3.9(a)** (Ch. I §3.9). If `u` is a harmonic function on `M`, then `∂u` is a holomorphic differential. -/
theorem prop1_3_9_a {u : X → ℂ} (hu : IsHarmonicOn u univ) : IsHolomorphicForm (dFormHol u) univ := by
  sorry

/-- **Proposition I.3.9(b)** (Ch. I §3.9). A differential `ω = u dz + v dz̄` is holomorphic if and only if `v = 0` and `u` is a
holomorphic function (of the local coordinate).
[CORRECTION, FK-fix3] The right side is read on `Y` (local form of `Forster1981.Form1.IsHolomorphicOn`: the `dz̄` coefficient
vanishes and the `dz` coefficient is differentiable at the chart points over `Y`). `Forster1981.Form1.IsHolomorphicOn` demands `w.2 = 0`
on all of `X`, so for `Y ≠ univ` the old statement failed: `w = d(χ z̄)` with `χ = 0` on `Y`, `χ ≠ 0` elsewhere (AUDITR2_FK R2FK-2). For
`Y = univ` the right side is `w.IsHolomorphicOn univ`. -/
theorem prop1_3_9_b {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) :
    IsHolomorphicForm w Y ↔
      ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → w.2 x z = 0 ∧ DifferentiableAt ℂ (w.1 x) z := by
  sorry

/-- **Unlabelled** (Ch. I §3.10, FK1:1115–1131). For a smooth differential `ω = u dz + v dz̄`, `ω` is harmonic if and only if
`u` and `v̄` are holomorphic. -/
theorem para1_3_10_a {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) (hs : w.IsSmoothOn Y) :
    IsHarmonicForm w Y ↔ (Form1.IsHolomorphicOn ((w.1, 0) : Form1 X) Y ∧ Form1.IsHolomorphicOn (((conjForm w).1, 0) : Form1 X) Y) := by
  sorry

/-- **Unlabelled** (Ch. I §3.10, FK1:1127–1131). If `ω` is harmonic, there are unique holomorphic differentials `ω₁` and `ω₂`
with `ω = ω₁ + ω̄₂` (uniqueness on `Y`). -/
theorem para1_3_10_b {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) (hh : IsHarmonicForm w Y) :
    (∃ ω₁ ω₂ : Form1 X, ω₁.IsForm ∧ ω₂.IsForm ∧ ω₁.IsHolomorphicOn Y ∧ ω₂.IsHolomorphicOn Y ∧
      Form1.EqOn w (ω₁ + conjForm ω₂) Y) ∧
    ∀ ω₁ ω₂ ω₁' ω₂' : Form1 X, ω₁.IsHolomorphicOn Y → ω₂.IsHolomorphicOn Y → ω₁'.IsHolomorphicOn Y →
      ω₂'.IsHolomorphicOn Y → Form1.EqOn w (ω₁ + conjForm ω₂) Y → Form1.EqOn w (ω₁' + conjForm ω₂') Y →
      Form1.EqOn ω₁ ω₁' Y ∧ Form1.EqOn ω₂ ω₂' Y := by
  sorry

/-- **Theorem I.3.11** (Ch. I §3.11). A differential form `ω` is holomorphic if and only if `ω = α + i*α` for some harmonic
differential `α` (on `Y`). -/
theorem thm1_3_11 {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) :
    IsHolomorphicForm w Y ↔
      ∃ α : Form1 X, α.IsForm ∧ IsHarmonicForm α Y ∧ Form1.EqOn w (α + Complex.I • starForm α) Y := by
  sorry

/-- **Corollary I.3.11** (Ch. I §3.11). A differential `ω` is holomorphic if and only if it is closed and `*ω = −iω`. -/
theorem cor1_3_11 {w : Form1 X} (hw : w.IsForm) {Y : Set X} (hY : IsOpen Y) :
    IsHolomorphicForm w Y ↔ w.IsClosed Y ∧ Form1.EqOn (starForm w) (-Complex.I • w) Y := by
  sorry

end FarkasKra1992
