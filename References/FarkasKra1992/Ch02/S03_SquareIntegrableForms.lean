import References.FarkasKra1992.Ch02.S02_WeylsLemma
import References.FarkasKra1992.Ch01.S04_IntegrationFormulae

/-!
# Farkas–Kra, Chapter II §3: The Hilbert space of square integrable forms

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. II §3 (`full.md` FK1:1665–1891).

Conventions: `L²(M)` is the space of square integrable measurable 1-forms of `Ch01/S04_IntegrationFormulae`
(`IsL2Form1 univ`, inner product `HasL2Inner univ`), forms equal almost everywhere being identified (`AEEqForm`). "Smooth" is
`C^∞` (as in the book's chapter II) and "closed", "exact", "co-closed", "co-exact", "harmonic" are those of
`Ch01/S03_DifferentialForms`. The closure `E` of `{df ; f smooth with compact support}` in `L²(M)`, the space
`E* = {ω ; *ω ∈ E}` and the orthogonal complements `E^⊥`, `E*^⊥` are sets of square integrable forms
(`spaceE`, `spaceEstar`, `spaceEperp`, `spaceEstarperp`); `H = E^⊥ ∩ E*^⊥` is `spaceH`. The Hilbert space facts used
(orthogonal decompositions, closedness) are statements about these sets: a decomposition `ω = e + e* + h` that is unique up to
equality almost everywhere.

* II.3.1 (the spaces `E`, `E*`, `E^⊥`, `E*^⊥`) — `AEEqForm`, `IsL2Limit`, `spaceE`, `spaceEstar`, `spaceEperp`, `spaceEstarperp`
* II.3.1 (the orthogonal decompositions (3.1.1), (3.2.1) and the space `H`) — `spaceH`, `para2_3_1`
* Proposition II.3.2, part (a) — `prop2_3_2_a`
* Proposition II.3.2, part (b) — `prop2_3_2_b`
* II.3.3 (the form `η_c` associated with a simple closed curve `c`) and Proposition II.3.3 — `IsSimpleClosedCurve`, `prop2_3_3`
* Proposition II.3.4, part (a) — `prop2_3_4_a`
* Proposition II.3.4, part (b) — `prop2_3_4_b`
* Theorem II.3.5 — `thm2_3_5`
* Corollary II.3.5, part (a) — `cor2_3_5_a`
* Corollary II.3.5, part (b) — `cor2_3_5_b`
* Corollary II.3.5, part (b′) — `cor2_3_5_c`
* II.3.6 (first de Rham cohomology `H¹(M) ≅ H` of a compact surface) — `para2_3_6`
* Theorem II.3.7, part (a) — `thm2_3_7_a`
* Theorem II.3.7, part (b) — `thm2_3_7_b`
* Theorem II.3.7, part (c) — `thm2_3_7_c`
* Theorem II.3.8 — `thm2_3_8`

Omitted (U−): the Remark with the diagram (Figure II.6), the Caution after Corollary II.3.5, the pairing `H₁ × H¹ → ℂ` of
II.3.6 (it is `Forster1981.period` against closed forms).
-/

open scoped Manifold ContDiff Topology ComplexConjugate
open Set Filter MeasureTheory Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Equality almost everywhere of 1-forms** (Ch. II §3.1, helper). Two 1-forms coincide almost everywhere if their
coefficients coincide almost everywhere in the chart image of every point. -/
def AEEqForm (w₁ w₂ : Form1 X) : Prop :=
  ∀ x, w₁.1 x =ᵐ[volume.restrict (chartAt ℂ x).target] w₂.1 x ∧ w₁.2 x =ᵐ[volume.restrict (chartAt ℂ x).target] w₂.2 x

/-- **Convergence in `L²(M)`** (Ch. II §3.1, helper). `ω = lim ω_n` in the norm of `L²(M)`: for every `ε > 0` and all large `n`
the square of the norm of `ω − ω_n` is `< ε`. -/
def IsL2Limit (w : Form1 X) (s : ℕ → Form1 X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ∃ r : ℝ, HasL2Inner univ (w - s n) (w - s n) r ∧ r < ε

/-- **The space `E`** (Ch. II §3.1). The `L²(M)` closure of `{df ; f is a smooth function on M with compact support}`:
the square integrable forms `ω` with `ω = lim df_n` in `L²(M)` for smooth `f_n` of compact support. -/
def spaceE : Set (Form1 X) :=
  {w | IsL2Form1 univ w ∧ ∃ f : ℕ → X → ℂ, (∀ n, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f n) ∧ HasCompactSupport (f n)) ∧
    IsL2Limit w (fun n => dForm (f n))}

/-- **The space `E*`** (Ch. II §3.1). `E* = {ω ∈ L²(M) ; *ω ∈ E}`. -/
def spaceEstar : Set (Form1 X) := {w | IsL2Form1 univ w ∧ starForm w ∈ (spaceE : Set (Form1 X))}

/-- **The orthogonal complement `E^⊥`** (Ch. II §3.1). `E^⊥ = {ω ∈ L²(M) ; (ω, df) = 0 for all smooth `f` with compact support}`. -/
def spaceEperp : Set (Form1 X) :=
  {w | IsL2Form1 univ w ∧ ∀ f : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f → HasCompactSupport f → HasL2Inner univ w (dForm f) 0}

/-- **The orthogonal complement `E*^⊥`** (Ch. II §3.1). `E*^⊥ = {ω ∈ L²(M) ; (ω, *df) = 0 for all smooth `f` with compact
support}`. -/
def spaceEstarperp : Set (Form1 X) :=
  {w | IsL2Form1 univ w ∧
    ∀ f : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f → HasCompactSupport f → HasL2Inner univ w (starForm (dForm f)) 0}

/-- **The space `H`** (Ch. II §3.2). `H = E^⊥ ∩ E*^⊥`. -/
def spaceH : Set (Form1 X) := spaceEperp ∩ spaceEstarperp

/-- **Unlabelled** (Ch. II §3.1–3.2, (3.1.1) and (3.2.1)). The orthogonal decomposition `L²(M) = E ⊕ E* ⊕ H`: every
square integrable form `ω` is, uniquely up to almost everywhere equality, a sum `ω = e + e* + h` with `e ∈ E`, `e* ∈ E*`,
`h ∈ H`, and the three spaces are mutually orthogonal. -/
theorem para2_3_1 :
    (∀ w : Form1 X, IsL2Form1 univ w → ∃ e a h : Form1 X, e ∈ spaceE ∧ a ∈ spaceEstar ∧ h ∈ spaceH ∧
      AEEqForm w (e + a + h)) ∧
    (∀ e a h e' a' h' : Form1 X, e ∈ spaceE → a ∈ spaceEstar → h ∈ spaceH → e' ∈ spaceE → a' ∈ spaceEstar →
      h' ∈ spaceH → AEEqForm (e + a + h) (e' + a' + h') → AEEqForm e e' ∧ AEEqForm a a' ∧ AEEqForm h h') ∧
    (∀ e a h : Form1 X, e ∈ spaceE → a ∈ spaceEstar → h ∈ spaceH →
      HasL2Inner univ e a 0 ∧ HasL2Inner univ e h 0 ∧ HasL2Inner univ a h 0) := by
  sorry

/-- **Proposition II.3.2(a)** (Ch. II §3.2). Let `α ∈ L²(M)` be smooth. Then `α ∈ E*^⊥` if and only if `α` is closed. -/
theorem prop2_3_2_a {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hl : IsL2Form1 univ w) :
    w ∈ (spaceEstarperp : Set (Form1 X)) ↔ w.IsClosed univ := by
  sorry

/-- **Proposition II.3.2(b)** (Ch. II §3.2). Let `α ∈ L²(M)` be smooth. Then `α ∈ E^⊥` if and only if `α` is co-closed. -/
theorem prop2_3_2_b {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hl : IsL2Form1 univ w) :
    w ∈ (spaceEperp : Set (Form1 X)) ↔ IsCoClosed w univ := by
  sorry

/-- **Simple closed curve** (Ch. II §3.3, helper). A closed piecewise differentiable curve `c : [0, 1] → M` with `c(0) = c(1)`
which is injective on `[0, 1)`. -/
def IsSimpleClosedCurve (c : C(unitInterval, X)) : Prop :=
  IsPiecewiseC1 c ∧ c 0 = c 1 ∧ InjOn c {t | t < 1}

/-- **Proposition II.3.3** (Ch. II §3.3). Let `c` be a simple closed curve on `M`. There is a smooth real closed 1-form `η_c`
with compact support (the form associated with `c`, built from a strip around `c`) such that for every closed smooth
`α ∈ L²(M)`, `∫_c α = (α, *η_c)`. -/
theorem prop2_3_3 {c : C(unitInterval, X)} (hc : IsSimpleClosedCurve c) :
    ∃ η : Form1 X, η.IsForm ∧ η.IsSmoothOn univ ∧ η.IsClosed univ ∧ conjForm η = η ∧
      (∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, η.pointValue x = (0, 0)) ∧
      ∀ α : Form1 X, α.IsForm → α.IsSmoothOn univ → α.IsClosed univ → IsL2Form1 univ α →
        ∃ v : ℂ, HasCurveIntegralRS α c v ∧ HasL2Inner univ α (starForm η) v := by
  sorry

/-- **Proposition II.3.4(a)** (Ch. II §3.4). Let `α ∈ L²(M)` be smooth. Then `α` is exact if and only if `(α, β) = 0` for all
co-closed smooth differentials `β` of compact support. -/
theorem prop2_3_4_a {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hl : IsL2Form1 univ w) :
    w.IsExact univ ↔ ∀ β : Form1 X, β.IsForm → β.IsSmoothOn univ → IsCoClosed β univ →
      (∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, β.pointValue x = (0, 0)) → HasL2Inner univ w β 0 := by
  sorry

/-- **Proposition II.3.4(b)** (Ch. II §3.4). Let `α ∈ L²(M)` be smooth. Then `α` is co-exact if and only if `(α, β) = 0` for
all closed smooth differentials `β` of compact support. -/
theorem prop2_3_4_b {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hl : IsL2Form1 univ w) :
    IsCoExact w univ ↔ ∀ β : Form1 X, β.IsForm → β.IsSmoothOn univ → β.IsClosed univ →
      (∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, β.pointValue x = (0, 0)) → HasL2Inner univ w β 0 := by
  sorry

/-- **Theorem II.3.5** (Ch. II §3.5). The Hilbert space `H` consists of the harmonic differentials in `L²(M)`: a form is in `H`
if and only if it is square integrable and equal almost everywhere to a harmonic differential. -/
theorem thm2_3_5 {w : Form1 X} :
    w ∈ (spaceH : Set (Form1 X)) ↔ IsL2Form1 univ w ∧ ∃ h : Form1 X, h.IsForm ∧ IsHarmonicForm h univ ∧ AEEqForm w h := by
  sorry

/-- **Corollary II.3.5(a)** (Ch. II §3.5). The `L²(M)` closure of the square integrable closed differentials is `E ⊕ H` (and that
of the square integrable co-closed differentials is `E* ⊕ H`; the second statement is the first applied to `*`): `ω ∈ E ⊕ H` if
and only if `ω` is an `L²(M)` limit of smooth square integrable closed forms. -/
theorem cor2_3_5_a {w : Form1 X} (hl : IsL2Form1 univ w) :
    (∃ e h : Form1 X, e ∈ spaceE ∧ h ∈ spaceH ∧ AEEqForm w (e + h)) ↔
      ∃ s : ℕ → Form1 X, (∀ n, (s n).IsForm ∧ (s n).IsSmoothOn univ ∧ (s n).IsClosed univ ∧ IsL2Form1 univ (s n)) ∧
        IsL2Limit w s := by
  sorry

/-- **Corollary II.3.5(b)** (Ch. II §3.5). The square integrable smooth differentials are dense in `L²(M)`. -/
theorem cor2_3_5_b {w : Form1 X} (hl : IsL2Form1 univ w) :
    ∃ s : ℕ → Form1 X, (∀ n, (s n).IsForm ∧ (s n).IsSmoothOn univ ∧ IsL2Form1 univ (s n)) ∧ IsL2Limit w s := by
  sorry

/-- **Corollary II.3.5(b′)** (Ch. II §3.5). The smooth differentials with compact support are dense in `L²(M)`. -/
theorem cor2_3_5_c {w : Form1 X} (hl : IsL2Form1 univ w) :
    ∃ s : ℕ → Form1 X, (∀ n, (s n).IsForm ∧ (s n).IsSmoothOn univ ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, (s n).pointValue x = (0, 0)) ∧ IsL2Limit w s := by
  sorry

/-- **Unlabelled** (Ch. II §3.6, (3.6.1)). For a compact Riemann surface `M`, the first de Rham cohomology group `H¹(M)`
(smooth closed forms modulo smooth exact forms) is isomorphic to the harmonic differentials: every smooth closed form is
cohomologous to a unique harmonic form. -/
theorem para2_3_6 [CompactSpace X] {α : Form1 X} (hα : α.IsForm) (hs : α.IsClosed univ) :
    ∃ h : Form1 X, h.IsForm ∧ IsHarmonicForm h univ ∧ (α - h).IsExact univ ∧
      ∀ h' : Form1 X, h'.IsForm → IsHarmonicForm h' univ → (α - h').IsExact univ → Form1.EqOn h h' univ := by
  sorry

/-- **Theorem II.3.7(a)** (Ch. II §3.7). A sufficient condition for the existence of a non-zero harmonic differential on a
Riemann surface `M` is the existence of a square integrable closed differential which is not exact: then `H` contains a
form that is not almost everywhere zero. -/
theorem thm2_3_7_a {α : Form1 X} (hα : α.IsForm) (hs : α.IsSmoothOn univ) (hc : α.IsClosed univ)
    (hl : IsL2Form1 univ α) (hne : ¬ α.IsExact univ) :
    ∃ h : Form1 X, h ∈ spaceH ∧ ¬ AEEqForm h 0 := by
  sorry

/-- **Theorem II.3.7(b)** (Ch. II §3.7). If `M` is compact, the condition of part (a) is also necessary: a non-zero harmonic
differential in `H` gives a closed, square integrable, smooth form which is not exact (the form itself). -/
theorem thm2_3_7_b [CompactSpace X] {h : Form1 X} (hh : h ∈ spaceH) (hn : ¬ AEEqForm h 0) :
    ∃ α : Form1 X, α.IsForm ∧ α.IsSmoothOn univ ∧ α.IsClosed univ ∧ IsL2Form1 univ α ∧ ¬ α.IsExact univ := by
  sorry

/-- **Theorem II.3.7(c)** (Ch. II §3.7). Explicitly, for every closed (smooth) `ω ∈ L²(M)`, there exists `ω₂ ∈ H` (a harmonic
differential) such that `∫_c ω = ∫_c ω₂` for all closed curves `c` on `M`. -/
theorem thm2_3_7_c {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hc : w.IsClosed univ)
    (hl : IsL2Form1 univ w) :
    ∃ w₂ : Form1 X, w₂.IsForm ∧ w₂.IsSmoothOn univ ∧ w₂ ∈ spaceH ∧
      ∀ c : C(unitInterval, X), IsPiecewiseC1 c → c 0 = c 1 → ∀ v : ℂ,
        HasCurveIntegralRS w c v ↔ HasCurveIntegralRS w₂ c v := by
  sorry

/-- **Theorem II.3.8** (Ch. II §3.8). If the Riemann surface `M` carries a closed curve `c` that does not separate (`M ∖ c` is
connected), then there exists a closed non-exact differential in `L²(M)` and therefore a non-zero harmonic differential. -/
theorem thm2_3_8 {c : C(unitInterval, X)} (hc : IsSimpleClosedCurve c) (hsep : IsConnected (range c)ᶜ) :
    (∃ α : Form1 X, α.IsForm ∧ α.IsSmoothOn univ ∧ α.IsClosed univ ∧ IsL2Form1 univ α ∧ ¬ α.IsExact univ) ∧
      ∃ h : Form1 X, h ∈ spaceH ∧ ¬ AEEqForm h 0 := by
  sorry

end FarkasKra1992
