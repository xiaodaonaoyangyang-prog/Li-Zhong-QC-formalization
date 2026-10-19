import References.Miyachi2008.S03_NecessaryCondition

/-!
# Miyachi 2008, §1.3, §4–§6: Characterization of the image of the asymptotic Bers map for the unit disk

H. Miyachi, *Image of asymptotic Bers map*, J. Math. Soc. Japan **60** (2008), 1255–1276; journal pages `p. n`.
Conventions: as in `S02_AsymptoticBersMap` and `S03_NecessaryCondition`; `Γ = 1` is `⊥ : Subgroup SL(2, ℝ)`, `D*` is `𝕃`, `S¹ = ∂D*`
is `frontier (toExt lowerHalf) = ℝ ∪ {∞}`, `cl(D*)` is the closure in `Ĉ` (`ExtPlane`).

* Definition (locally univalent quasiregular mapping on a domain, p. 1257) — `IsLocUnivQuasireg`
* Definition (quasiloop, p. 1257) — `IsQuasiloop`
* Definition (condition (c) of Theorem 1: `f_φ` extends as a locally univalent quasiregular mapping on a neighborhood of `cl(D*)`, p. 1257) — `HasLocUnivQuasiregExt`
* Definition (condition (d) of Theorem 1: continuous extension to `cl(D*)`, locally injective, with quasiloop image of `S¹`, p. 1257) — `HasQuasiloopExt`
* Theorem 1 (characterization of the preimage, p. 1257; proof §4–§5, pp. 1262–1266) — `thm1`
* Proposition 4.1 ((b) implies (c), p. 1263) — `prop4_1`
* Proposition 4.2 ((c) implies (a), p. 1265) — `prop4_2`
* Corollary 1 (topology of developing mappings, p. 1258; proof §6, p. 1267) — `cor1`
* Corollary 2 (necessary condition for the interior, p. 1258; proof §6, p. 1267) — `cor2`

Omitted (U−): Lemma 4.1 and Lemma 4.2 (the fans `S₁(a, r)`, `S₂(a, r, R)` and the union `S₃(k, r)`; steps inside the proof of
Proposition 4.1, p. 1263–1265), the Remark in §5 (the cubic map `z³` on `ℍ`, the condition "locally injective" cannot be dropped
from (d); p. 1266–1267).
Reading: in Corollary 2 the complement `Ĉ ∖ f_φ(D)` is the complement of `f_φ(D*)` (the paper's `D` is `D*`, the domain of `f_φ`).
Reading: the finite covering property of Corollary 1 counts the preimages `f_φ⁻¹(w)` in `D*` of every `w ∈ Ĉ` (Section 6, p. 1267).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Miyachi2008

open LiZhongQC (lowerHalf toExt ExtPlane meroToExt schwarzian IsLocUnivMero IsUnivMero bersMapGamma)
open GardinerLakic2000 (cuspFormsL)
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap)

/-- **Locally univalent quasiregular mapping** (p. 1257). `F` is locally univalent quasiregular on the open set `N ⊆ Ĉ`: every
point of `N` has a neighborhood in `N` on which `F` is `K`-quasiconformal, with a constant `K` depending only on `F`. -/
def IsLocUnivQuasireg (F : ExtPlane → ExtPlane) (N : Set ExtPlane) : Prop :=
  ∃ K : ℝ, ∀ x ∈ N, ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ IsKQuasiconformal F V K

/-- **Quasiloop** (p. 1257). The set `C ⊆ Ĉ` is a quasiloop (the image of a map `γ` of `S ⊆ Ĉ`, here `S` is `S¹`, such that for any
`z₀ ∈ S` there is a neighborhood `U₀` of `z₀` and a quasiconformal mapping on `U₀` that agrees with `γ` on `S ∩ U₀`). -/
def IsQuasiloop (S C : Set ExtPlane) : Prop :=
  ∃ γ : ExtPlane → ExtPlane, γ '' S = C ∧ ∀ z₀ ∈ S, ∃ U₀ : Set ExtPlane, IsOpen U₀ ∧ z₀ ∈ U₀ ∧
    ∃ G : ExtPlane → ExtPlane, IsQuasiconformalMap G U₀ ∧ ∀ z ∈ S ∩ U₀, G z = γ z

/-- **Condition (c) of Theorem 1** (p. 1257). The developing mapping `f` is extended as a locally univalent quasiregular mapping on
a neighborhood of `cl(D*)` (in `Ĉ`). -/
def HasLocUnivQuasiregExt (f : ℂ → ℂ) : Prop :=
  ∃ N : Set ExtPlane, IsOpen N ∧ closure (toExt lowerHalf) ⊆ N ∧
    ∃ F : ExtPlane → ExtPlane, IsLocUnivQuasireg F N ∧ ∀ z ∈ lowerHalf, F z = meroToExt f z

/-- **Condition (d) of Theorem 1** (p. 1257). `f` has a continuous extension `F` on `cl(D*)` with the property that `F` is locally
injective on `cl(D*)` and the image `F(S¹)` is a quasiloop. -/
def HasQuasiloopExt (f : ℂ → ℂ) : Prop :=
  ∃ F : ExtPlane → ExtPlane, ContinuousOn F (closure (toExt lowerHalf)) ∧ (∀ z ∈ lowerHalf, F z = meroToExt f z) ∧
    (∀ x ∈ closure (toExt lowerHalf), ∃ V ∈ 𝓝 x, InjOn F (V ∩ closure (toExt lowerHalf))) ∧
    IsQuasiloop (frontier (toExt lowerHalf)) (F '' frontier (toExt lowerHalf))

/-- **Theorem 1** (characterization of the preimage; p. 1257). For `φ ∈ B(1)` with developing mapping `f_φ` the following four
conditions are equivalent: (a) the class `[φ] ∈ B̂(1)` is contained in the image `𝒜𝒯₁` of `AT(D)` under the asymptotic Bers map;
(b) `φ` has the quasiconformal extension property at ends; (c) `f_φ` is extended as a locally univalent quasiregular mapping on a
neighborhood of `cl(D*)`; (d) `f_φ` has a continuous extension on `cl(D*)` with the property that `f_φ` is locally injective on
`cl(D*)` and the image `f_φ(S¹)` is a quasiloop. -/
theorem thm1 {φ : ℂ → ℂ} (hφ : φ ∈ cuspFormsL ⊥) {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) :
    List.TFAE [bHatMk ⊥ φ hφ ∈ asymBersImage ⊥, HasQCExtPropertyEnds ⊥ φ, HasLocUnivQuasiregExt f, HasQuasiloopExt f] := by
  sorry

/-- **Proposition 4.1** (p. 1263). Let `f` be a locally univalent function on `D*` whose Schwarzian derivative has the
quasiconformal extension property at ends. Then `f` extends to a locally univalent quasiregular mapping on a neighborhood of
`cl(D*)` ((b) implies (c) of Theorem 1). -/
theorem prop4_1 {φ : ℂ → ℂ} {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) (hφ : HasQCExtPropertyEnds ⊥ φ) :
    HasLocUnivQuasiregExt f := by
  sorry

/-- **Proposition 4.2** (p. 1265). Let `f` be a locally univalent function on `D*`. Suppose that `f` extends to a locally univalent
quasiregular mapping on a neighborhood of `cl(D*)`. Then `𝒮(f) ∈ B(1)` and there is `ψ ∈ 𝒯₁` such that `𝒮(f) − ψ ∈ B₀(1)`
((c) implies (a) of Theorem 1). Modelling: `𝒮(f)` is the form `φ` on `𝕃` extended by `0`. -/
theorem prop4_2 {f : ℂ → ℂ} (hf : IsLocUnivMero f lowerHalf) (hext : HasLocUnivQuasiregExt f) :
    ∃ φ : ℂ → ℂ, φ ∈ cuspFormsL ⊥ ∧ (∀ z ∈ lowerHalf, φ z = schwarzian f z) ∧
      ∃ ψ ∈ Set.range (bersMapGamma ⊥), φ - ψ ∈ bZero ⊥ := by
  sorry

/-- **Corollary 1** (topology of developing mappings; p. 1258). Let `φ ∈ B(1)`. When the class `[φ]` is in `𝒜𝒯₁`, the developing
mapping `f_φ` admits a continuous extension on `cl(D*)` and is a finite covering map onto its image: there is `N > 0` such that
the number of preimages `f_φ⁻¹(w)` is at most `N` for every `w ∈ Ĉ`. -/
theorem cor1 {φ : ℂ → ℂ} (hφ : φ ∈ cuspFormsL ⊥) (h : bHatMk ⊥ φ hφ ∈ asymBersImage ⊥) {f : ℂ → ℂ}
    (hf : IsDevelopingMap φ f) :
    (∃ F : ExtPlane → ExtPlane, ContinuousOn F (closure (toExt lowerHalf)) ∧ ∀ z ∈ lowerHalf, F z = meroToExt f z) ∧
      ∃ N : ℕ, ∀ w : ExtPlane, {z ∈ lowerHalf | meroToExt f z = w}.Finite ∧ {z ∈ lowerHalf | meroToExt f z = w}.ncard ≤ N := by
  sorry

/-- **Corollary 2** (necessary condition for the interior; p. 1258). For `φ ∈ B(1)`, suppose that `f_φ` is univalent. Then the
complement `Ĉ ∖ f_φ(D*)` is locally connected, provided that the class `[φ]` is in `𝒜𝒯₁`. -/
theorem cor2 {φ : ℂ → ℂ} (hφ : φ ∈ cuspFormsL ⊥) {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) (hu : IsUnivMero f lowerHalf)
    (h : bHatMk ⊥ φ hφ ∈ asymBersImage ⊥) : LocallyConnectedSpace ↥((meroToExt f '' lowerHalf)ᶜ) := by
  sorry

end Miyachi2008
