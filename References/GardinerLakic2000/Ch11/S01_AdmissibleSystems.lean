import References.GardinerLakic2000.Ch10.S05_AutomorphismGroups

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.1 Admissible systems (with the chapter introduction)

Source `teichmuller.txt`, lines 8306–8377 (Chapter 11, introduction and §11.1).

* Definition (horizontal, regular, closed trajectory, l. 8308–8314) — `IsHorizClosedTraj`
* Definition (ring domain and core curve, l. 8314) — `IsAnnulusMap`, `IsSweptAnnulus`, `IsPhiRingDomain`,
  `IsCoreCurve`
* Definition (Jenkins–Strebel differential, l. 8315; used in Ch. 8, 12) — `IsNullSetRS`, `IsJSDecomp`,
  `IsJenkinsStrebel`
* Definition (Jenkins–Strebel direction; JS differentials with more than one direction, l. 8339) — `IsJSDirection`
* Definition 1 (admissible system of closed curves, l. 8342; also l. 8319) — `IsSimpleLoop`, `IsTrivialLoop`,
  `IsPeripheralLoop`, `IsAdmissibleSystem`
* Lemma 1 (l. 8347) — `lemma11_1_a`, `lemma11_1_b`
* Definition (compatible admissible systems, l. 8376) — `AreCompatibleSystems`

Not items: the introduction's claims (at most `3g − 3 + n` annuli; density of Jenkins–Strebel differentials; a JS
differential with two directions and finitely many annuli lives on a surface of finite type, l. 8315–8339: the first is
Lemma 1, the last Theorem 5, the density is not proved in the book); (11.2), (11.3) (proof). Modelling: surface level
(C0.1). Closed curves are `LiZhongQC.Loop` with free homotopy `LiZhongQC.FreelyHomotopic`; "homotopic to a puncture" is
"freely homotopic to a loop inside a puncture neighbourhood" (`LiZhongQC.IsPunctureNbhd`); closed trajectories are loops
that are horizontal arcs (`LiZhongQC.IsHorizontalArcRS`); annuli are holomorphic injective images of round annuli
`{1 < |z| < r}` (`LiZhongQC.annulus`). A ring domain of `φ` (`IsPhiRingDomain`) depends on the quadratic differential;
its plane counterpart without `φ` is `LehtoVirtanen1973.IsRingDomain` (any doubly connected domain of `ℂ̂`), a different
notion, hence the distinct name. Null sets are null in every chart. The surfaces of Lemma 1 are of finite analytic type
(batch B's `IsFiniteAnalyticType`) with `d = 3g − 3 + n > 0` as stated.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop FreelyHomotopic IsPunctureNbhd annulus IsHorizontalArcRS)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§11 introduction, l. 8308–8314). The closed curve `β` is a horizontal, regular, closed trajectory
of `φ`: in the charts along `β` it is a horizontal trajectory arc (`φ(β) β′² > 0`, so `β` avoids the zeros of `φ`),
read by the project's `LiZhongQC.IsHorizontalArcRS`. -/
def IsHorizClosedTraj (φ : R → ℂ → ℂ) (β : Loop R) : Prop := IsHorizontalArcRS φ β.2

/-- Helper (§11 introduction). `e` is a conformal map of the round annulus `{1 < |z| < r}` onto the open set
`A ⊆ R`. -/
def IsAnnulusMap (A : Set R) (r : ℝ) (e : ℂ → R) : Prop :=
  1 < r ∧ IsOpen A ∧ InjOn e (annulus 1 r) ∧ e '' annulus 1 r = A ∧
    ∀ z ∈ annulus 1 r, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e z

/-- Helper (§11 introduction, l. 8314). `A` is an annulus swept out by horizontal regular closed trajectories of
`φ`. -/
def IsSweptAnnulus (φ : R → ℂ → ℂ) (A : Set R) : Prop :=
  (∃ (r : ℝ) (e : ℂ → R), IsAnnulusMap A r e) ∧
    ∀ y ∈ A, ∃ β : Loop R, IsHorizClosedTraj φ β ∧ range β.2 ⊆ A ∧ y ∈ range β.2

/-- **Definition** (ring domain, §11 introduction, l. 8314). A maximal annulus swept out by horizontal regular closed
trajectories of `φ`. -/
def IsPhiRingDomain (φ : R → ℂ → ℂ) (A : Set R) : Prop :=
  IsSweptAnnulus φ A ∧ ∀ A' : Set R, A ⊆ A' → IsSweptAnnulus φ A' → A' = A

/-- **Definition** (core curve, §11 introduction, l. 8314). A horizontal regular closed trajectory contained in a ring
domain. -/
def IsCoreCurve (φ : R → ℂ → ℂ) (A : Set R) (β : Loop R) : Prop :=
  IsPhiRingDomain φ A ∧ IsHorizClosedTraj φ β ∧ range β.2 ⊆ A

/-- Helper (§11). `N ⊆ R` has measure zero (in every chart). -/
def IsNullSetRS (N : Set R) : Prop := ∀ x : R, volume (chartAt ℂ x '' (N ∩ (chartAt ℂ x).source)) = 0

/-- Helper (§11 introduction, l. 8315). `φ ∈ A(R)` and, up to a set of measure zero, `R` is the disjoint union of the
ring domains `A_j` of `φ`. -/
def IsJSDecomp {ι : Type*} (φ : R → ℂ → ℂ) (A : ι → Set R) : Prop :=
  φ ∈ integrableHolQDSet R ∧ (∀ j, IsPhiRingDomain φ (A j)) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
    IsNullSetRS (⋃ j, A j)ᶜ

/-- **Definition** (Jenkins–Strebel differential, §11 introduction, l. 8315). `φ ∈ A(R)` such that, up to a set of
measure zero, `R` is the disjoint union of (countably many) ring domains of `φ`. -/
def IsJenkinsStrebel (φ : R → ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set R), IsJSDecomp φ A

/-- **Definition** (§11 introduction, l. 8339). `c` (`|c| = 1`) is a Jenkins–Strebel direction of `φ`: `cφ` is a
Jenkins–Strebel differential. -/
def IsJSDirection (φ : R → ℂ → ℂ) (c : ℂ) : Prop := ‖c‖ = 1 ∧ IsJenkinsStrebel (fun x z => c * φ x z)

/-- Helper for **Definition 1** (§11.1). A simple closed curve: injective on `[0, 1)`. -/
def IsSimpleLoop (β : Loop R) : Prop :=
  ∀ s t : unitInterval, (s : ℝ) < 1 → (t : ℝ) < 1 → β.2 s = β.2 t → s = t

/-- Helper for **Definition 1** (§11.1). A homotopically trivial closed curve. -/
def IsTrivialLoop (β : Loop R) : Prop := FreelyHomotopic β ⟨β.1, Path.refl β.1⟩

/-- Helper for **Definition 1** (§11.1). A closed curve homotopic to a puncture: freely homotopic to a closed curve
inside a puncture neighbourhood. -/
def IsPeripheralLoop (β : Loop R) : Prop :=
  ∃ (U : Set R) (ψ : R → ℂ), IsPunctureNbhd U ψ ∧ ∃ γ : Loop R, range γ.2 ⊆ U ∧ FreelyHomotopic β γ

/-- **Definition 1** (admissible system, §11.1, l. 8342). (a) each `α_i` is simple and no two intersect; (b) no two are
homotopic; (c) none is homotopically trivial or homotopic to a puncture.
[CORRECTION/modelling] (AUDITR2_GL614 R2-1) `FreelyHomotopic` is homotopy of *oriented* loops, but the book's curves are
unoriented classes. Without the reversed-loop clause in (b) a curve and a disjoint parallel copy traversed the other way are
admissible, and `lemma11_1_a` fails (once-punctured torus: two curves, bound `1`). So (b) also excludes `α i ≃ (α j)⁻¹`. -/
def IsAdmissibleSystem {ι : Type*} (α : ι → Loop R) : Prop :=
  (∀ i, IsSimpleLoop (α i)) ∧ (∀ i j, i ≠ j → Disjoint (range (α i).2) (range (α j).2)) ∧
    (∀ i j, i ≠ j → ¬ FreelyHomotopic (α i) (α j) ∧ ¬ FreelyHomotopic (α i) ⟨(α j).1, (α j).2.symm⟩) ∧
    ∀ i, ¬ IsTrivialLoop (α i) ∧ ¬ IsPeripheralLoop (α i)

/-- **Lemma 1** (§11.1, l. 8347), the bound. On a surface of finite analytic type `(g, n)` with `d = 3g − 3 + n` (four
or more punctures in genus `0`, one or more in genus `1`), an admissible system has at most `d` elements. -/
theorem lemma11_1_a [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {g n : ℕ} (hR : IsFiniteAnalyticType R g n)
    (hg0 : g = 0 → 4 ≤ n) (hg1 : g = 1 → 1 ≤ n) {ι : Type*} (α : ι → Loop R) (hα : IsAdmissibleSystem α) :
    Finite ι ∧ Nat.card ι ≤ 3 * g + n - 3 := by
  sorry

/-- **Lemma 1** (§11.1, l. 8347), the completion. Every admissible system of `k < d` curves can be completed by
`d − k` curves to an admissible system of `d` curves. -/
theorem lemma11_1_b [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {g n : ℕ} (hR : IsFiniteAnalyticType R g n)
    (hg0 : g = 0 → 4 ≤ n) (hg1 : g = 1 → 1 ≤ n) {k : ℕ} (α : Fin k → Loop R) (hα : IsAdmissibleSystem α)
    (hk : k < 3 * g + n - 3) :
    ∃ (β : Fin (3 * g + n - 3) → Loop R) (e : Fin k ↪ Fin (3 * g + n - 3)), IsAdmissibleSystem β ∧
      ∀ i, β (e i) = α i := by
  sorry

/-- **Definition** (compatible admissible systems, §11.1, l. 8376). Each curve of either system is homotopic to a
curve of the other. -/
def AreCompatibleSystems {ι κ : Type*} (α : ι → Loop R) (α' : κ → Loop R) : Prop :=
  (∀ i, ∃ j, FreelyHomotopic (α i) (α' j) ∨ FreelyHomotopic (α i) ⟨(α' j).1, (α' j).2.symm⟩) ∧
    ∀ j, ∃ i, FreelyHomotopic (α' j) (α i) ∨ FreelyHomotopic (α' j) ⟨(α i).1, (α i).2.symm⟩

end GardinerLakic2000
