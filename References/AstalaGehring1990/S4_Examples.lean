import References.AstalaGehring1990.S3_ComplementOfAQuasiarc

/-!
# Astala–Gehring 1990, §4 Examples

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), §4; source `full.md` of `Astala-CricketsZippersBers-1990.pdf-e9a341c8…`, lines 255–439.

* Definition (asymptotically conformal quasiarc, l. 259) — `IsAsymptoticallyConformal`
* Theorem 4.1 — `thm4_1`
* Definition (an arc which is a graph, l. 285) — `IsGraph`
* Theorem 4.3 — `thm4_3`
* Corollary 4.5 — `cor4_5`
* Definition (the ratio `r(z_j)` of a triple, l. 341; interlocking sequence, l. 347) — `ratioR`, `IsInterlocking`
* Theorem 4.9 — `thm4_9`

Not items (DESIGN §3):
- the claim of l. 259–265 that the triples of an asymptotically conformal arc in `ℂ` satisfy
  `(|z₁ - z₂| + |z₂ - z₃|)/|z₁ - z₃| → 1`, which is not cited later (U−);
- the map (4.2) and the condition (4.4), both inside proofs;
- Example 4.12 (the dovetail polygon: interlocking for `ϑ < π/2`, a graph for `ϑ ≥ π/2`), an example;
- Remark 4.13 (simple zippers).

**Conventions.**
- Lines are the euclidean lines of `ℂ`, without `∞`. The proof of 4.3 normalizes an unbounded graph `α` with the
  endpoints `0` and `∞` to be a graph for the vertical lines. With lines through `∞`, `α ∩ λ` would then contain `∞`
  and a finite point, so it would not be connected.
- "`0` is an interior point of `α`" means `0 ∈ α` and `0` is neither endpoint of `α`.
- Arcs with given endpoints are `LehtoVirtanen1973.IsArcFromTo`, and quasiconformality is
  `LehtoVirtanen1973.IsKQuasiconformal` / `LehtoVirtanen1973.IsQuasiconformalMap` (FOUNDATIONS.md).
- Sequences are indexed from `1`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace AstalaGehring1990

open LiZhongQC References
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap IsArcFromTo)

/-- **Definition** (§4, l. 259). A quasiarc `α` is asymptotically conformal if, for each `K > 1`, `α = g(I)`, where
`g` is quasiconformal in `ℂ̄` and `K`-quasiconformal in a neighborhood `V` of `I = [0, ∞]`.
Modelling: `V` is an open subset of `ℂ̄` containing `I` (it contains `∞`). `LehtoVirtanen1973.IsKQuasiconformal`
requires a domain, so `V` is connected. This loses nothing, because the component of a neighbourhood that contains
the connected set `I` is again a neighbourhood of `I`. -/
def IsAsymptoticallyConformal (α : Set ExtPlane) : Prop :=
  IsQuasiarc α ∧ ∀ K > (1 : ℝ), ∃ g : ExtPlane → ExtPlane, IsQuasiconformalMap g univ ∧ α = g '' halfAxisExt ∧
    ∃ V : Set ExtPlane, IsOpen V ∧ halfAxisExt ⊆ V ∧ IsKQuasiconformal g V K

/-- **Theorem 4.1** (§4). If `α` is an asymptotically conformal quasiarc, then `D = ℂ̄ ∖ α` is in `T̄`. -/
theorem thm4_1 {α : Set ExtPlane} (hα : IsAsymptoticallyConformal α) : IsInTbar αᶜ := by
  sorry

/-- **Definition** (§4, l. 285). An arc `α` is a graph if for each line `λ` parallel to some fixed line, the set
`α ∩ λ` is either connected or empty.
Modelling: the lines are the euclidean lines `c + ℝ v` of `ℂ` (fixed direction `v ≠ 0`); "connected or empty" is
`IsPreconnected`. -/
def IsGraph (α : Set ExtPlane) : Prop :=
  ∃ v : ℂ, v ≠ 0 ∧ ∀ c : ℂ, IsPreconnected (finitePart α ∩ {z : ℂ | ∃ t : ℝ, z = c + t * v})

/-- **Theorem 4.3** (§4). If `α` is a quasiarc which is a graph, then `D = ℂ̄ ∖ α` is in `T̄`.
[CORRECTION] Added hypothesis `hinf`: `∞ ∉ α`, or `∞` is an endpoint of `α`. The proof (l. 289) treats only these
cases (it normalizes an unbounded `α` to have the endpoints `0` and `∞`). With `∞` an interior point the statement is
false: `α = A ∪ (−A) ∪ {∞}`, `A = ⋃_{n ≥ 0} 5ⁿ Π` for a suitable stepped polygon `Π` from `1` to `5`, is a
self-similar quasiarc and a graph for the vertical lines, while `α' = 1/α` has `0` as an interior point,
`(1/5) α' ⊆ α'`, and is a graph in no direction. Corollary 4.5 then gives `ℂ̄ ∖ α' ∉ T̄`, and the Möbius invariance
of `T̄` (`isInTbar_of_mobius`) would give `ℂ̄ ∖ α' ∈ T̄` from the uncorrected statement (leader's audit,
2026-09-28). -/
theorem thm4_3 {α : Set ExtPlane} (hα : IsQuasiarc α) (hg : IsGraph α)
    (hinf : extInf ∈ α → ∃ p : ExtPlane, IsArcFromTo α p extInf) : IsInTbar αᶜ := by
  sorry

/-- **Corollary 4.5** (§4). Suppose that `α` is a quasiarc, that `0` is an interior point of `α`, and that
`f(α) ⊆ α` for `f(z) = az` with some `a` in `B(0, 1) ∖ {0}`. Then `D = ℂ̄ ∖ α` is in `T̄` if and only if `α` is a
graph.
Modelling: "interior point": `0 ∈ α` and `0` differs from both endpoints of the arc (`LehtoVirtanen1973.IsArcFromTo`);
`f` acts on `ℂ̄` by `OnePoint.map` (fixing `∞`); the OCR's "for some `a`" refers to the homothety `f(z) = az` of
l. 335. -/
theorem cor4_5 {α : Set ExtPlane} (hα : IsQuasiarc α)
    (h0 : ∃ p q : ExtPlane, IsArcFromTo α p q ∧ ((0 : ℂ) : ExtPlane) ∈ α ∧ ((0 : ℂ) : ExtPlane) ≠ p ∧
      ((0 : ℂ) : ExtPlane) ≠ q)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (ha0 : a ≠ 0) (hf : OnePoint.map (fun z : ℂ => a * z) '' α ⊆ α) :
    IsInTbar αᶜ ↔ IsGraph α := by
  sorry

/-- **Definition** (§4, l. 341). For a triple of points `z_{j-1}, z_j, z_{j+1}` of `ℂ`,
`r(z_j) = (z_{j+1} - z_j)/(z_{j-1} - z_j)`; here `ratioR z_{j-1} z_j z_{j+1}`. The triples of every use have
`z_{j-1} ≠ z_j`. -/
def ratioR (u v w : ℂ) : ℂ :=
  (w - v) / (u - v)

/-- **Definition** (§4, l. 347–359). Let `α` be a subarc, with endpoints `0` and `∞`, of a quasicircle `γ`. A sequence
of distinct points `z_j` of `α` is interlocking if there exist constants `0 < a, b < ∞`, disjoint neighborhoods `V_j`
of `z_j` and a component `G` of `ℂ̄ ∖ γ` with the following properties:
- (4.6) `|r(z_j)| ≤ a` for `j ≥ 2`;
- (4.7) if `w_{j-1} ∈ G ∩ V_{j-1}`, `w_j ∈ G ∩ V_j`, `w_{j+1} ∈ G` and `|r(z_j) - r(w_j)| ≤ b` for some `j ≥ 2`, then
  `w_{j+1} ∈ V_{j+1}`;
- (4.8) `dia(V_j)/|z_j| → 0` as `j → ∞`.

Modelling:
- The setting (`α`, `γ`, endpoints) is part of the hypotheses of `thm4_9`.
- Indices start at `1`, so `z 0` and `V 0` play no role.
- `V_j ⊆ ℂ`; the `w`'s are finite points of `G`, and `r(w_j)` is formed from `w_{j-1}, w_j, w_{j+1}`.
- The diameter in (4.8) is `Metric.ediam` in `ℝ≥0∞`, so that an unbounded `V_j` is not given diameter `0`. -/
def IsInterlocking (α γ : Set ExtPlane) (z : ℕ → ℂ) : Prop :=
  (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → z i ≠ z j) ∧ (∀ j : ℕ, 1 ≤ j → (z j : ExtPlane) ∈ α) ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ V : ℕ → Set ℂ, (∀ j : ℕ, 1 ≤ j → V j ∈ 𝓝 (z j)) ∧
      (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (V i) (V j)) ∧
      ∃ G : Set ExtPlane, (∃ p ∉ γ, G = connectedComponentIn γᶜ p) ∧
        (∀ j : ℕ, 2 ≤ j → ‖ratioR (z (j - 1)) (z j) (z (j + 1))‖ ≤ a) ∧
        (∀ j : ℕ, 2 ≤ j → ∀ w₀ w₁ w₂ : ℂ, (w₀ : ExtPlane) ∈ G → w₀ ∈ V (j - 1) → (w₁ : ExtPlane) ∈ G →
          w₁ ∈ V j → (w₂ : ExtPlane) ∈ G →
          ‖ratioR (z (j - 1)) (z j) (z (j + 1)) - ratioR w₀ w₁ w₂‖ ≤ b → w₂ ∈ V (j + 1)) ∧
        Tendsto (fun j : ℕ => Metric.ediam (V j) / (‖z j‖₊ : ℝ≥0∞)) atTop (𝓝 0)

/-- **Theorem 4.9** (§4). If `α` is a quasiarc that contains an interlocking sequence, then `D = ℂ̄ ∖ α` is not in
`T̄`.
Modelling: the setting of the definition is explicit: `α` lies in a quasicircle `γ` (so it is a subarc of `γ`) and
has the endpoints `0` and `∞`; the sequence is interlocking with respect to `γ`. -/
theorem thm4_9 {α γ : Set ExtPlane} (hα : IsQuasiarc α) (hγ : IsQuasicircle γ) (hαγ : α ⊆ γ)
    (hend : IsArcFromTo α ((0 : ℂ) : ExtPlane) extInf)
    {z : ℕ → ℂ} (hz : IsInterlocking α γ z) : ¬ IsInTbar αᶜ := by
  sorry

end AstalaGehring1990
