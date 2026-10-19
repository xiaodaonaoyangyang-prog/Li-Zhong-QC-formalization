import References.FarkasKra1992.Ch01.S03_DifferentialForms

/-!
# Farkas–Kra, Chapter I §4: Integration formulae

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. I §4 (`full.md` FK1:1175–1346).

Conventions: as in `Ch01/S03_DifferentialForms`. Surface integrals of compactly supported 2-forms are
`Forster1981.HasIntegral2`. The Hilbert space `L²` of I.4.2 is modelled by the area integral of a density
(`HasAreaIntegral`: a Lebesgue integral over `Y`, evaluated through a locally finite smooth partition of unity subordinate
to charts) of the densities `ω ∧ *ω̄ = 2(|u|² + |v|²) dx ∧ dy` and `ω₁ ∧ *ω̄₂ = 2(u₁ū₂ + v₁v̄₂) dx ∧ dy` (I.4.2). The
elements of `L²` are measurable 1-forms (`IsMeasForm1`: the transformation laws hold almost everywhere) with finite norm
(`IsL2Form1`); forms that agree almost everywhere are identified in the statements that use them (as in the book).

* Theorem I.4.1 (integration by parts) — deferred: regions with piecewise differentiable boundary (no model of boundary integrals on a region)
* Corollary I.4.1, part 1 (`∫_{δD} ω = 0` for a closed `ω`) — deferred: regions with piecewise differentiable boundary
* Corollary I.4.1, part 2 — `cor1_4_1_b`
* I.4.2 (area integral over `Y`, measurable forms, the space `L²`, norm, inner product) — `HasAreaIntegral`, `IsMeasForm1`, `IsL2Form1`, `HasL2Inner`
* Proposition I.4.3 — deferred: regions with piecewise differentiable boundary
* Proposition I.4.4 and Corollary — deferred: regions with piecewise differentiable boundary
* Proposition I.4.5 — deferred: regions with piecewise differentiable boundary
* Proposition I.4.6 and Corollary — deferred: regions with piecewise differentiable boundary
* Proposition I.4.7 — deferred: regions with piecewise differentiable boundary

Omitted (U−): the symmetry identities `(ω₁, ω₂) = conj (ω₂, ω₁)` and `(*ω₁, *ω₂) = (ω₁, ω₂)` of I.4.2 (checks that
the pairing is a Hilbert space inner product).
-/

open scoped Manifold ContDiff Topology ComplexConjugate
open Set Filter MeasureTheory Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Integral of a density over `Y`** (Ch. I §4.2, helper). `v = ∬_Y f dx dy` for a family of coefficients `f x : ℂ → ℂ`
(`f x` is the density in the preferred chart at `x`): there are a locally finite smooth partition of unity `ρ_k` with
`supp ρ_k` inside the chart domain of `n_k`, such that every `ρ_k f` is integrable over `Y`, the integrals are
absolutely summable, and `v = Σ_k ∫_{Y ∩ chart} ρ_k f`. (Independent of the partition when `f` satisfies the
transformation law of a `(1, 1)` density.) -/
def HasAreaIntegral (f : X → ℂ → ℂ) (Y : Set X) (v : ℂ) : Prop :=
  ∃ (n : ℕ → X) (ρ : ℕ → X → ℝ),
    (∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun a => (ρ k a : ℂ)) ∧ tsupport (ρ k) ⊆ (chartAt ℂ (n k)).source ∧
      ∀ a, 0 ≤ ρ k a) ∧
    (∀ a, ∑' k, ρ k a = 1) ∧ (∀ a, ∃ U ∈ 𝓝 a, {k | (U ∩ tsupport (ρ k)).Nonempty}.Finite) ∧
    (∀ k, IntegrableOn (fun z => (ρ k ((chartAt ℂ (n k)).symm z) : ℂ) * f (n k) z)
      ((chartAt ℂ (n k)).target ∩ (chartAt ℂ (n k)).symm ⁻¹' Y)) ∧
    Summable (fun k => ∫ z in (chartAt ℂ (n k)).target ∩ (chartAt ℂ (n k)).symm ⁻¹' Y,
      ‖(ρ k ((chartAt ℂ (n k)).symm z) : ℂ) * f (n k) z‖) ∧
    v = ∑' k, ∫ z in (chartAt ℂ (n k)).target ∩ (chartAt ℂ (n k)).symm ⁻¹' Y,
      (ρ k ((chartAt ℂ (n k)).symm z) : ℂ) * f (n k) z

/-- **Measurable 1-form** (Ch. I §4.2). A *measurable 1-form* `ω = u dz + v dz̄`: `u` and `v` are measurable functions of the
local coordinates, and the transformation laws of `dz`, `dz̄` hold almost everywhere (two forms are identified when they
coincide almost everywhere). -/
def IsMeasForm1 (w : Form1 X) : Prop :=
  LiZhongQC.IsDiffFamilyAE 1 0 w.1 ∧ LiZhongQC.IsDiffFamilyAE 0 1 w.2 ∧ ∀ x, Measurable (w.1 x) ∧ Measurable (w.2 x)

/-- **Square integrable 1-form on `Y`** (Ch. I §4.2). A measurable 1-form with
`‖ω‖²_Y = ∬_Y ω ∧ *ω̄ = ∬_Y 2(|u|² + |v|²) dx ∧ dy < ∞`. -/
def IsL2Form1 (Y : Set X) (w : Form1 X) : Prop :=
  IsMeasForm1 w ∧ ∃ r : ℝ, HasAreaIntegral (fun x z => ((2 * (‖w.1 x z‖ ^ 2 + ‖w.2 x z‖ ^ 2) : ℝ) : ℂ)) Y r

/-- **The inner product of `L²`** (Ch. I §4.2). `(ω₁, ω₂)_Y = ∬_Y ω₁ ∧ *ω̄₂ = ∬_Y 2(u₁ū₂ + v₁v̄₂) dx ∧ dy` equals `v`. The
square of the norm is `HasL2Inner Y ω ω ‖ω‖²`. -/
def HasL2Inner (Y : Set X) (w₁ w₂ : Form1 X) (v : ℂ) : Prop :=
  HasAreaIntegral (fun x z => 2 * (w₁.1 x z * conj (w₂.1 x z) + w₁.2 x z * conj (w₂.2 x z))) Y v

/-- **Corollary I.4.1, part 2** (Ch. I §4.1, Corollary 2). Let `f` be a function and `ω` a 1-form on the Riemann surface
`M`. If either `f` or `ω` has compact support, then `∬_M f dω − ∬_M ω ∧ df = 0`.
Modelling: `C^∞` data in place of `C¹`; the two integrals exist (compact support) and are equal. -/
theorem cor1_4_1_b {f : X → ℂ} {w : Form1 X} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (hw : w.IsForm)
    (hws : w.IsSmoothOn univ) (hc : HasCompactSupport f ∨ ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, w.pointValue x = (0, 0)) :
    ∃ v : ℂ, HasIntegral2 (Form2.smulFun f w.d) v ∧ HasIntegral2 (w.wedge (dForm f)) v := by
  sorry

end FarkasKra1992
