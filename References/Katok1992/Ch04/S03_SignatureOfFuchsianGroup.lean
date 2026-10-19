import References.Katok1992.Ch04.S02_CocompactGroups
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Katok 1992, Ch. 4 §4.3 The signature of a Fuchsian group

S. Katok, *Fuchsian Groups* (1992), Chapter 4, §4.3; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 2023–2200.

* Definition (the signature `(g; m₁, …, m_r)` of a cocompact group; its extension `(g; m₁, …, m_r; s)`; (4.3.4);
  l. 2025, 2171) — `HasCompactifiedGenus`, `HasSignature`
* Theorem 4.3.1 (the area of the quotient; l. 2027) — `thm4_3_1`
* Theorem 4.3.2 (Poincaré's theorem: existence of a group with a given signature; l. 2055) — `thm4_3_2`
* Corollary 4.3.3 (a Fuchsian group without fixed points with quotient of genus `g > 1`; l. 2118) — `cor4_3_3`
* Example C (the group `Γ₈` of signature `(2; −)`; l. 2121) — omitted: example (explicit matrices of a generator system;
  the existence is Theorem 4.3.2)
* Unlabelled (the presentation of a group with signature `(g; m₁, …, m_r; s)`; l. 2160–2195) — `thm4_3_presentation`
* Unlabelled (no group has signature with non-positive area, e.g. `(1; −)`; l. 2175) — `para4_3_nonexistence`
* Unlabelled (the area of the quotient from the signature, Exercise 4.11; l. 2189) — covered by `thm4_3_1`
  (cocompact case) and `thm4_3_area` (with cusps)

**Conventions.** The signature of `Γ` is read from the quotient `Γ\ℍ`: `m` lists the *periods* of `Γ` (`HasPeriods`, the orders of
the non-conjugate maximal finite cyclic subgroups), `s` is the *parabolic class number* (the number of conjugacy classes of
maximal parabolic subgroups, `maxParabolicClasses`), and `g` is the genus of the quotient. For a non-cocompact group
the quotient `Γ\ℍ` is not compact, and its genus is that of its *compactification* by `s` points: `HasCompactifiedGenus Γ g s`
says that there is a Hausdorff connected space `S` with an open embedding `Γ\ℍ → S` whose complement has `s` points and
`HasGenus S g` (`LiZhongQC.HasGenus`: `S` compact with the fundamental group of the surface group of genus `g`). For a
cocompact group `s = 0` and `S = Γ\ℍ`. Triangle groups with an angle `π/∞` are signatures with `s > 0` in this model.
The area `μ(Γ\ℍ)` is `quotientArea`.

**Near misses.** `FarkasKra1992.HasSignature` and `FarkasKra1992.signatureChar` (Ch. IV §9.1: groups of finite type over an
invariant domain of a Kleinian group, with a Riemann surface structure on the quotient; ν = ∞ for punctures); there the
signature and the characteristic `χ = 2p − 2 + Σ(1 − 1/ν_j)` are defined for Kleinian groups.
-/

open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups ENNReal Real

noncomputable section

namespace Katok1992

/-- **Definition** (§4.3; l. 2025, 2171). The quotient `Γ\ℍ` has genus `g` after the addition of `s` points: there is a
topological space `S` and an open embedding `e : Γ\ℍ → S` whose image has a complement of exactly `s` points, with `S`
a compact surface of genus `g` (`HasGenus`). `S` is required to be Hausdorff (and connected): without it the added points
could have `S` as their only neighbourhood, `S` would be contractible and `HasGenus S 0` would hold for every cusped group.
With `T2Space S` each added point compactifies exactly one cusp end, as in the book's compactification. -/
def HasCompactifiedGenus (Γ : Subgroup PSL(2, ℝ)) (g s : ℕ) : Prop :=
  ∃ (S : Type) (_ : TopologicalSpace S) (_ : T2Space S) (_ : ConnectedSpace S)
    (e : MulAction.orbitRel.Quotient Γ ℍ → S),
    Topology.IsOpenEmbedding e ∧ (range e)ᶜ.encard = s ∧ LiZhongQC.HasGenus S g

/-- **Definition** (§4.3; l. 2025, 2171, (4.3.4)). `Γ` has *signature* `(g; m₁, …, m_r; s)`: the quotient `Γ\ℍ` has genus `g`
(of its compactification by `s` points), `Γ` has `r` conjugacy classes of maximal finite cyclic subgroups, of orders
`m₁, …, m_r` (`HasPeriods`), and `s` conjugacy classes of maximal parabolic subgroups. For `s = 0` this is the signature
`(g; m₁, …, m_r)` of a cocompact group. -/
def HasSignature (Γ : Subgroup PSL(2, ℝ)) (g : ℕ) {r : ℕ} (m : Fin r → ℕ) (s : ℕ) : Prop :=
  HasPeriods Γ m ∧ Nat.card (maxParabolicClasses Γ) = s ∧ HasCompactifiedGenus Γ g s

/-- **Theorem 4.3.1** (§4.3; l. 2027). Let `Γ` (cocompact) have signature `(g; m₁, …, m_r)`. Then
`μ(Γ\ℍ) = 2π [(2g − 2) + Σ_{i=1}^r (1 − 1/m_i)]`. -/
theorem thm4_3_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hc : IsCocompact Γ) {g r : ℕ} {m : Fin r → ℕ}
    (hs : HasSignature Γ g m 0) :
    quotientArea Γ = ENNReal.ofReal (2 * π * ((2 * (g : ℝ) - 2) + ∑ i, (1 - 1 / (m i : ℝ)))) := by
  sorry

/-- **Unlabelled** (§4.3; l. 2175–2195, Exercise 4.11). With cusps: if `Γ` has signature `(g; m₁, …, m_r; s)` and finite area,
`μ(Γ\ℍ) = 2π [(2g − 2) + Σ_{i=1}^r (1 − 1/m_i) + s]`. -/
theorem thm4_3_area {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hμ : quotientArea Γ < ⊤) {g r s : ℕ} {m : Fin r → ℕ}
    (hs : HasSignature Γ g m s) :
    quotientArea Γ = ENNReal.ofReal (2 * π * ((2 * (g : ℝ) - 2) + ∑ i, (1 - 1 / (m i : ℝ)) + s)) := by
  sorry

/-- **Theorem 4.3.2** (Poincaré's theorem; §4.3; l. 2055). If `g ≥ 0`, `r ≥ 0`, `m_i ≥ 2` are integers and
`(2g − 2) + Σ_{i=1}^r (1 − 1/m_i) > 0`, then there exists a Fuchsian group with signature `(g; m₁, …, m_r)`. -/
theorem thm4_3_2 {g r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, 2 ≤ m i)
    (hpos : 0 < (2 * (g : ℝ) - 2) + ∑ i, (1 - 1 / (m i : ℝ))) :
    ∃ Γ : Subgroup PSL(2, ℝ), IsFuchsian Γ ∧ IsCocompact Γ ∧ HasSignature Γ g m 0 := by
  sorry

/-- **Corollary 4.3.3** (§4.3; l. 2118). For any integer `g > 1` there exists a Fuchsian group acting on `ℍ` without fixed
points such that `Γ\ℍ` has genus `g`. -/
theorem cor4_3_3 {g : ℕ} (hg : 1 < g) :
    ∃ Γ : Subgroup PSL(2, ℝ), IsFuchsian Γ ∧ (∀ T ∈ Γ, T ≠ 1 → ∀ z : ℍ, T • z ≠ z) ∧ IsCocompact Γ ∧
      LiZhongQC.HasGenus (MulAction.orbitRel.Quotient Γ ℍ) g := by
  sorry

/-- **Unlabelled** (§4.3; l. 2160–2195). A group `Γ` with signature `(g; m₁, …, m_r; s)` has the presentation
`⟨A₁, B₁, …, A_g, B_g, X₁, …, X_r, P₁, …, P_s | X_k^{m_k} = P₁ ⋯ P_s X₁ ⋯ X_r ∏ [A_i, B_i] = Id⟩`: there are
`A_i, B_i, X_k, P_t ∈ Γ` generating `Γ`, such that the kernel of the induced homomorphism from the free group on these
generators to `Γ` is the normal closure of the relations. (The product of the commutators is taken in the order of the
book, with `[A, B] = A B A⁻¹ B⁻¹`.) The `X_k` are elliptic of order `m_k` and the `P_t` parabolic, as in the book. -/
theorem thm4_3_presentation {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hμ : quotientArea Γ < ⊤) {g r s : ℕ}
    {m : Fin r → ℕ} (hs : HasSignature Γ g m s) :
    ∃ (A B : Fin g → PSL(2, ℝ)) (X : Fin r → PSL(2, ℝ)) (P : Fin s → PSL(2, ℝ)),
      (∀ i, A i ∈ Γ ∧ B i ∈ Γ) ∧ (∀ k, X k ∈ Γ ∧ orderOf (X k) = m k) ∧ (∀ t, P t ∈ Γ ∧ IsParabolic (P t)) ∧
        Subgroup.closure (range A ∪ range B ∪ range X ∪ range P) = Γ ∧
        (FreeGroup.lift (Sum.elim (Sum.elim (Sum.elim A B) X) P :
            (((Fin g ⊕ Fin g) ⊕ Fin r) ⊕ Fin s) → PSL(2, ℝ))).ker =
          Subgroup.normalClosure
            ({w | ∃ k : Fin r, w = FreeGroup.of (Sum.inl (Sum.inr k)) ^ m k} ∪
              {w | w = (List.ofFn fun t : Fin s => FreeGroup.of (Sum.inr t)).prod *
                  (List.ofFn fun k : Fin r => FreeGroup.of (Sum.inl (Sum.inr k))).prod *
                  (List.ofFn fun i : Fin g =>
                    (FreeGroup.of (Sum.inl (Sum.inl (Sum.inl i))) * FreeGroup.of (Sum.inl (Sum.inl (Sum.inr i))) *
                      (FreeGroup.of (Sum.inl (Sum.inl (Sum.inl i))))⁻¹ * (FreeGroup.of (Sum.inl (Sum.inl (Sum.inr i))))⁻¹ :
                      FreeGroup (((Fin g ⊕ Fin g) ⊕ Fin r) ⊕ Fin s))).prod}) := by
  sorry

/-- **Unlabelled** (§4.3; l. 2170–2174). If `2π [(2g − 2) + Σ (1 − 1/m_i)] ≤ 0` there is no Fuchsian group with signature
`(g; m₁, …, m_r)`; in particular none with signature `(1; −)`. -/
theorem para4_3_nonexistence {g r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, 2 ≤ m i)
    (hle : (2 * (g : ℝ) - 2) + ∑ i, (1 - 1 / (m i : ℝ)) ≤ 0) :
    ¬ ∃ Γ : Subgroup PSL(2, ℝ), IsFuchsian Γ ∧ IsCocompact Γ ∧ HasSignature Γ g m 0 := by
  sorry

end Katok1992
