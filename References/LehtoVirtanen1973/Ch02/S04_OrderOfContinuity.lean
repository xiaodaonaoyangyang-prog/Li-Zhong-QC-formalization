import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC

/-!
# Lehto–Virtanen, Chapter II §4: Order of continuity of quasiconformal mappings

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §4
(pp. 68–71; `full.md` P1:2122–2219).

The continuity notions of this section are defined with respect to the spherical metric `k = sphericalDist`
(P1:2126). A family of mappings of a domain `G` is a set `𝒲` of maps `ExtPlane → ExtPlane`, only their values on `G`
mattering; a single mapping `w` is the family `{w}` (footnote 19). "`w` omits the value `a`" is `a ∉ w(G)`.

* Definition (equicontinuity of a family at a point and in a set, §4.1) — `IsEquicontinuousAtSph`,
  `IsEquicontinuousOnSph`
* Theorem 4.1 (§4.1) — `thm2_4_1`
* Theorem 4.2 (§4.1) — `thm2_4_2_i`, `thm2_4_2_ii`
* Unlabelled (§4.1, P1:2176): a family of `K`-quasiconformal mappings whose values at two points stay apart is
  equicontinuous at every other point — `equicontinuousAt_of_two_points`
* Definition (Hölder continuity of a family at a point; uniform Hölder continuity in a set, §4.2, footnote 19) —
  `IsHolderAtSph`, `IsUniformlyHolderOnSph`
* Theorem 4.3 (§4.2) — `thm2_4_3`
* Unlabelled (§4.2, P1:2208): a `K`-quasiconformal mapping is uniformly Hölder continuous with exponent `1/K` in
  every compact subset — `kqc_uniformlyHolder`

The immediate remark that Hölder continuity at a point implies equicontinuity there (P1:2186, first sentence; the second
sentence, the converse for families of `K`-quasiconformal mappings, is also U−: Theorem 4.3 sharpens it), the examples
`wₙ(z) = 2ⁿz` (P1:2176) and `w(z) = z|z|^{1/K - 1}` (P1:2212–2218), and the proof steps (4.1), (4.2), (4.4) are not
stated (inventory: omitted).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §4.1 Equicontinuity -/

/-- **Definition** (equicontinuity at a point, Ch. II §4.1). A family `𝒲` of mappings of a domain `G` into the plane
is equicontinuous at the point `z₀ ∈ G` if to every `ε > 0` there corresponds a neighbourhood `U` of `z₀` such that
`sup_{w ∈ 𝒲, z ∈ U} k(w(z), w(z₀)) < ε`.
Modelling: the supremum condition is written pointwise, `k(w(z), w(z₀)) < ε` for all `w ∈ 𝒲` and `z ∈ U`, which gives
the same notion (apply it with `ε/2`); the neighbourhood is taken inside `G`, where the mappings are defined. -/
def IsEquicontinuousAtSph (𝒲 : Set (ExtPlane → ExtPlane)) (G : Set ExtPlane) (z₀ : ExtPlane) : Prop :=
  ∀ ε > 0, ∃ U ∈ 𝓝 z₀, U ⊆ G ∧ ∀ w ∈ 𝒲, ∀ z ∈ U, sphericalDist (w z) (w z₀) < ε

/-- **Definition** (equicontinuity in a set, Ch. II §4.1). The family `𝒲` is equicontinuous in the set `E ⊂ G` if it
is equicontinuous at every point of `E`. -/
def IsEquicontinuousOnSph (𝒲 : Set (ExtPlane → ExtPlane)) (G E : Set ExtPlane) : Prop :=
  ∀ z₀ ∈ E, IsEquicontinuousAtSph 𝒲 G z₀

/-- **Theorem 4.1** (Ch. II §4.1). Let `𝒲` be a family of `K`-quasiconformal mappings of the domain `G`. If every
mapping `w ∈ 𝒲` omits two values whose spherical distance is greater than a fixed positive number `d`, then `𝒲` is
equicontinuous in `G`.
Modelling: that `G` is a domain is stated separately, since the quasiconformality hypotheses say nothing about `G`
when `𝒲` is empty. -/
theorem thm2_4_1 {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d)
    (homit : ∀ w ∈ 𝒲, ∃ a b : ExtPlane, a ∉ w '' G ∧ b ∉ w '' G ∧ d < sphericalDist a b) :
    IsEquicontinuousOnSph 𝒲 G G := by
  sorry

/-- **Theorem 4.2, 1°** (Ch. II §4.1). A family `𝒲` of `K`-quasiconformal mappings of the domain `G` is
equicontinuous in `G` if there exists a number `d > 0` such that every mapping `w ∈ 𝒲` omits one value `a` and, for
two fixed points `z₁, z₂ ∈ G`, the distances `k(w(zᵢ), a)`, `i = 1, 2`, are greater than `d`.
Modelling: the two fixed points are distinct, `z₁ ≠ z₂`. For `z₁ = z₂` the statement is false: the conformal mappings
`wₙ(z) = nz` of the finite plane omit `a = ∞` and `k(wₙ(0), ∞) = π/2 > 1 = d` with `z₁ = z₂ = 0`, but they are not
equicontinuous at `0`. `G` is a domain as in `thm2_4_1`. -/
theorem thm2_4_2_i {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d) {z₁ z₂ : ExtPlane} (hz₁ : z₁ ∈ G) (hz₂ : z₂ ∈ G)
    (h₁₂ : z₁ ≠ z₂)
    (homit : ∀ w ∈ 𝒲, ∃ a : ExtPlane, a ∉ w '' G ∧ d < sphericalDist (w z₁) a ∧ d < sphericalDist (w z₂) a) :
    IsEquicontinuousOnSph 𝒲 G G := by
  sorry

/-- **Theorem 4.2, 2°** (Ch. II §4.1). A family `𝒲` of `K`-quasiconformal mappings of the domain `G` is
equicontinuous in `G` if there exists a number `d > 0` such that for three fixed points `z₁, z₂, z₃ ∈ G` the distances
`k(w(zᵢ), w(zⱼ))`, `i, j = 1, 2, 3`, `i ≠ j`, are greater than `d` for every mapping `w ∈ 𝒲`.
Modelling: the three points are `z 0, z 1, z 2`; `G` is a domain as in `thm2_4_1`. -/
theorem thm2_4_2_ii {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d) {z : Fin 3 → ExtPlane} (hz : ∀ i, z i ∈ G)
    (hsep : ∀ w ∈ 𝒲, ∀ i j, i ≠ j → d < sphericalDist (w (z i)) (w (z j))) :
    IsEquicontinuousOnSph 𝒲 G G := by
  sorry

/-- **Unlabelled** (Ch. II §4.1, P1:2176). If `𝒲` is a family of `K`-quasiconformal mappings of the domain `G` and
there exist two points `z₁, z₂ ∈ G` such that `k(w(z₁), w(z₂)) > d > 0` for every mapping `w ∈ 𝒲`, then `𝒲` is
equicontinuous at every point of `G` other than `z₁` and `z₂` (cited in §5.3). -/
theorem equicontinuousAt_of_two_points {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ}
    (hG : IsDomainExt G) (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d) {z₁ z₂ : ExtPlane}
    (hz₁ : z₁ ∈ G) (hz₂ : z₂ ∈ G) (hsep : ∀ w ∈ 𝒲, d < sphericalDist (w z₁) (w z₂)) :
    IsEquicontinuousOnSph 𝒲 G (G \ {z₁, z₂}) := by
  sorry

/-! ## §4.2 Hölder continuity -/

/-- **Definition** (Hölder continuity at a point, Ch. II §4.2). The family `𝒲` of mappings of the domain `G` is Hölder
continuous with exponent `α` at the point `z₀ ∈ G` if the Hölder condition `k(w(z), w(z₀)) ≤ C k(z, z₀)^α` (4.3) is
satisfied with a fixed `C` for all `w ∈ 𝒲` and `z ∈ G`. By footnote 19 this also defines the Hölder continuity of a
single mapping `w`, the family `{w}`.
Modelling: the book's restriction `α > 0` is not part of the definition; the statements use the exponents `1/K` of a
family of `K`-quasiconformal mappings (`K ≥ 1`) and `α > 0`. The condition `z₀ ∈ G` is not built in; every use
supplies it. -/
def IsHolderAtSph (𝒲 : Set (ExtPlane → ExtPlane)) (G : Set ExtPlane) (α : ℝ) (z₀ : ExtPlane) : Prop :=
  ∃ C : ℝ, ∀ w ∈ 𝒲, ∀ z ∈ G, sphericalDist (w z) (w z₀) ≤ C * sphericalDist z z₀ ^ α

/-- **Definition** (uniform Hölder continuity, Ch. II §4.2). If `E` is a subset of `G` and (4.3) holds with fixed `α`
and `C` for all `w ∈ 𝒲`, `z ∈ G` and `z₀ ∈ E`, then `𝒲` is uniformly Hölder continuous with exponent `α` in `E`.
The condition `E ⊆ G` is not built in; every use supplies it. -/
def IsUniformlyHolderOnSph (𝒲 : Set (ExtPlane → ExtPlane)) (G : Set ExtPlane) (α : ℝ) (E : Set ExtPlane) : Prop :=
  ∃ C : ℝ, ∀ w ∈ 𝒲, ∀ z₀ ∈ E, ∀ z ∈ G, sphericalDist (w z) (w z₀) ≤ C * sphericalDist z z₀ ^ α

/-- **Theorem 4.3** (Ch. II §4.2). A family `𝒲` of `K`-quasiconformal mappings which is equicontinuous in a domain `G`
is uniformly Hölder continuous with exponent `1/K` in every compact subset of `G`. -/
theorem thm2_4_3 {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (heq : IsEquicontinuousOnSph 𝒲 G G) {F : Set ExtPlane}
    (hF : IsCompact F) (hFG : F ⊆ G) : IsUniformlyHolderOnSph 𝒲 G (1 / K) F := by
  sorry

/-- **Unlabelled** (Ch. II §4.2, P1:2208–2210). A `K`-quasiconformal mapping of a domain `G` is uniformly Hölder
continuous with exponent `1/K` in every compact subset of `G` (the special case `𝒲 = {w}` of Theorem 4.3; cited in
§7.3 as "the remark at the end of 4.2"). -/
theorem kqc_uniformlyHolder {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w G K)
    {F : Set ExtPlane} (hF : IsCompact F) (hFG : F ⊆ G) : IsUniformlyHolderOnSph {w} G (1 / K) F := by
  sorry

end LehtoVirtanen1973
