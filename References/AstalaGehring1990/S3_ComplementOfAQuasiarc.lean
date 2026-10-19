import References.AstalaGehring1990.S2_ClosureOfT

/-!
# Astala–Gehring 1990, §3 The complement of a quasiarc

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), §3; source `full.md` of `Astala-CricketsZippersBers-1990.pdf-e9a341c8…`, lines 117–253.

* Definition (the closed positive half `I = [0, ∞]` of the extended real axis; quasiarc, l. 119) — `halfAxisExt`,
  `IsQuasiarc`
* Theorem 3.1 (Cricket Theorem) — `thm3_1_cricket`
* Lemma 3.4 — `lemma3_4`
* Definition (`s`-quasisymmetric map, l. 189) — `IsSQuasisymmetric`
* Lemma 3.6 — `lemma3_6`
* Lemma 3.8 — `lemma3_8`

Not items (DESIGN §3):
- Remark 3.2 (l. 123, the spring-steel picture behind the name);
- the estimate (3.3) and the theorem of Teichmüller, both quoted inside proofs;
- the proofs of 3.1, 3.4, 3.6 and 3.8.

**Conventions.** The Lehto–Virtanen reference notions are used (FOUNDATIONS.md):
- (`K`-)quasiconformal maps of domains of `ℂ̄`: `LehtoVirtanen1973.IsKQuasiconformal` and
  `LehtoVirtanen1973.IsQuasiconformalMap` (sense preserving). A self-mapping of `ℂ̄` is the case `G = univ`.
- homeomorphisms: `LehtoVirtanen1973.IsHomeoOn`.
- arcs: `LehtoVirtanen1973.IsClosedJordanArc`. A subarc of `γ` is a closed Jordan arc contained in `γ`.
- Finite values of a map of `ℂ̄` at points where they are finite: `LehtoVirtanen1973.finiteMap`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace AstalaGehring1990

open LiZhongQC References
open LehtoVirtanen1973 (IsHomeoOn IsKQuasiconformal IsQuasiconformalMap IsClosedJordanArc IsSensePreservingOn
  finiteMap)

/-- **Definition** (§3, l. 119). The closed positive half `I = [0, ∞]` of the extended real axis, a subset of `ℂ̄`. -/
def halfAxisExt : Set ExtPlane :=
  toExt {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ {extInf}

/-- **Definition** (§3, l. 119). `α ⊆ ℂ̄` is a quasiarc: the image of `I = [0, ∞]` under a quasiconformal mapping of
`ℂ̄`. -/
def IsQuasiarc (α : Set ExtPlane) : Prop :=
  ∃ F : ExtPlane → ExtPlane, IsQuasiconformalMap F univ ∧ α = F '' halfAxisExt

/-- **Theorem 3.1 (Cricket Theorem)** (§3). Suppose that `α` is a subarc of a quasicircle `γ` in `ℂ̄`. Then
`D = ℂ̄ ∖ α` is in `T̄` if and only if for each `K > 1` there exists a sense preserving `K`-quasiconformal
self-mapping `h` of `ℂ̄` such that `h(z) = z` in `γ ∖ α` and `h(α) ∪ α` is a quasicircle.
Modelling: a subarc of `γ` is a closed Jordan arc contained in `γ`; quasicircles are `LiZhongQC.IsQuasicircle`. -/
theorem thm3_1_cricket {α γ : Set ExtPlane} (hγ : IsQuasicircle γ) (hα : IsClosedJordanArc α) (hαγ : α ⊆ γ) :
    IsInTbar αᶜ ↔ ∀ K > (1 : ℝ), ∃ h : ExtPlane → ExtPlane, IsKQuasiconformal h univ K ∧ (∀ p ∈ γ \ α, h p = p) ∧
      IsQuasicircle (h '' α ∪ α) := by
  sorry

/-- **Lemma 3.4** (§3). For each `0 < a < ∞` there exists `0 < b = b(a) < ∞` with the following property. If `g` is
`K`-quasiconformal in `ℂ̄` with `1 ≤ K ≤ e^{a/b}`, and if `g` fixes `z₁, z₂, ∞`, then (3.5)
`|g(z) - z| ≤ b |z₁ - z₂| log K` for `z` in `B(z₁, a |z₁ - z₂|)`.
Modelling: "three points" gives `z₁ ≠ z₂`. `g` fixes `∞` and is injective, so `g(z)` is finite for finite `z`; the
conclusion names this finite value `w`. -/
theorem lemma3_4 {a : ℝ} (ha : 0 < a) :
    ∃ b > (0 : ℝ), ∀ (g : ExtPlane → ExtPlane) (K : ℝ), IsKQuasiconformal g univ K → 1 ≤ K → K ≤ Real.exp (a / b) →
      g extInf = extInf → ∀ z₁ z₂ : ℂ, z₁ ≠ z₂ → g z₁ = z₁ → g z₂ = z₂ →
        ∀ z ∈ ball z₁ (a * ‖z₁ - z₂‖), ∃ w : ℂ, g z = w ∧ ‖w - z‖ ≤ b * ‖z₁ - z₂‖ * Real.log K := by
  sorry

/-- **Definition** (§3, l. 189; after Väisälä [V2]). For `0 < s < ∞`, a continuous map `g` of `E ⊆ ℂ` into `ℂ` is
`s`-quasisymmetric if for each three points `z, z', z''` of `E`,
`s ≤ |(z' - z)/(z'' - z)| ≤ 1/s` implies `|(g(z') - g(z))/(g(z'') - g(z))| ≤ |(z' - z)/(z'' - z)| + s`.
Modelling:
- `g` is injective on `E`. Väisälä's quasisymmetric maps are embeddings, and the book's quotient
  `(g(z') - g(z))/(g(z'') - g(z))` presupposes `g(z'') ≠ g(z)`.
- With injectivity the conclusion can be cleared of its denominator:
  `|g(z') - g(z)| ≤ (|(z' - z)/(z'' - z)| + s) |g(z'') - g(z)|`. This is equivalent and avoids the junk value of
  `x / 0`.
- In the hypothesis, `z'' = z` gives the quotient `0 < s`, so the condition is vacuous, as intended. -/
def IsSQuasisymmetric (g : ℂ → ℂ) (E : Set ℂ) (s : ℝ) : Prop :=
  0 < s ∧ ContinuousOn g E ∧ InjOn g E ∧ ∀ z ∈ E, ∀ z' ∈ E, ∀ z'' ∈ E, s ≤ ‖(z' - z) / (z'' - z)‖ →
    ‖(z' - z) / (z'' - z)‖ ≤ 1 / s → ‖g z' - g z‖ ≤ (‖(z' - z) / (z'' - z)‖ + s) * ‖g z'' - g z‖

/-- **Lemma 3.6** (§3). For each `s > 0` there exist `t > 0` and `K > 1` with the following property: if `g` is
`K`-quasiconformal and satisfies `|g(z) - z| ≤ t r` in `B(z₀, 2r)`, then `g` is `s`-quasisymmetric in `B̄(z₀, r)`.
Modelling:
- "`K`-quasiconformal" is read as `K`-quasiconformal in `B(z₀, 2r)`, the weakest reading, which is how the proof of
  Theorem 3.1 applies the lemma; `r > 0`.
- The bound makes `g(z)` finite on the disk, and the `s`-quasisymmetry is that of the finite map
  `LehtoVirtanen1973.finiteMap g`. -/
theorem lemma3_6 {s : ℝ} (hs : 0 < s) :
    ∃ t > (0 : ℝ), ∃ K > (1 : ℝ), ∀ (g : ExtPlane → ExtPlane) (z₀ : ℂ) (r : ℝ), 0 < r →
      IsKQuasiconformal g (toExt (ball z₀ (2 * r))) K →
      (∀ z ∈ ball z₀ (2 * r), ∃ w : ℂ, g z = w ∧ ‖w - z‖ ≤ t * r) →
        IsSQuasisymmetric (finiteMap g) (closedBall z₀ r) s := by
  sorry

/-- **Lemma 3.8** (§3; from Tukia–Väisälä [TV]). For each `K > 1` there exists `s > 0` with the following property:
if `g` is an `s`-quasisymmetric homeomorphism of a closed disk `B`, then `g|B` has a homeomorphic extension to `ℂ̄`
which is `K`-quasiconformal in `ℂ̄ ∖ B`.
Modelling:
- `B = B̄(z₀, r)`, `r > 0`. An `s`-quasisymmetric `g` is continuous and injective, so on the compact disk it is a
  homeomorphism onto its image. The extension is a homeomorphism of `ℂ̄` onto `ℂ̄` which is `K`-quasiconformal in
  the domain `ℂ̄ ∖ B`.
- [CORRECTION] Added hypothesis: `g` is sense preserving on `B` (`LehtoVirtanen1973.IsSensePreservingOn`).
  Literally, under the paper's convention that all quasiconformal maps are sense preserving (l. 49), the lemma is
  false. The reflection `z ↦ z̄` of a disk is an isometry, hence `s`-quasisymmetric for every `s`. Every homeomorphic
  extension of it reverses the orientation of `ℂ̄`, so it is not quasiconformal in `ℂ̄ ∖ B`. The only application,
  in the proof of Theorem 3.1, has `g` quasiconformal in `B(z₀, 2r)` and so sense preserving. -/
theorem lemma3_8 {K : ℝ} (hK : 1 < K) :
    ∃ s > (0 : ℝ), ∀ (g : ℂ → ℂ) (z₀ : ℂ) (r : ℝ), 0 < r →
      IsSensePreservingOn (OnePoint.map g) (toExt (closedBall z₀ r)) → IsSQuasisymmetric g (closedBall z₀ r) s →
        ∃ G : ExtPlane → ExtPlane, IsHomeoOn G univ univ ∧ (∀ z ∈ closedBall z₀ r, G z = g z) ∧
          IsKQuasiconformal G (toExt (closedBall z₀ r))ᶜ K := by
  sorry

end AstalaGehring1990
