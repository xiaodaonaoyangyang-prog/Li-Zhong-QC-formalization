import References.LehtoVirtanen1973.Ch01.S05_TwoBasicProperties
import References.LehtoVirtanen1973.Ch02.S04_OrderOfContinuity

/-!
# Lehto–Virtanen, Chapter II §5: Convergence theorems for quasiconformal mappings

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §5
(pp. 71–79; `full.md` P1:2220–2366).

Sequences of mappings are indexed by `ℕ` (the book's `n = 1, 2, …`) and are treated as the family of their members
where a family notion of §4 is applied. "`wₙ` converges in `G`" (to `w`) is pointwise convergence in `ℂ̄` at every
point of `G`, the topology of `ℂ̄` being that of the spherical metric; "uniformly in every compact subset" is
`TendstoUniformlyOnCompactsSph` (I.5.2). For mappings `wₙ : G → G′ₙ` the image domains are `G′ₙ = wₙ(G)`.
"`G` has at least two boundary points" is `∃ a b ∈ Fr G, a ≠ b`.

* Definition (everywhere dense set, §5.1, footnote 20) — exists: `derivedSet` (A is everywhere dense in G, every
  point of G being a limit point of A, is written G ⊆ derivedSet A)
* Lemma 5.1 (§5.1) — `lemma2_5_1`
* Definition (normal family, §5.1) — `IsNormalFamilySph`
* Definition (closed normal family, §5.1) — omitted: never used again in the book
* Lemma 5.2 (§5.1) — `lemma2_5_2`
* Unlabelled (§5.1–5.2, P1:2238, 2248): equicontinuity, Hölder continuity and normality of a family of
  `K`-quasiconformal mappings are equivalent — `kqcFamily_tfae`
* Theorem 5.1 (§5.2) — `thm2_5_1_i`, `thm2_5_1_ii`, `thm2_5_1_iii`, `thm2_5_1_omit_two`
* Theorem 5.2 (§5.3) — `thm2_5_2`
* Theorem 5.3 (§5.4) — `thm2_5_3`
* Definition (kernel `N{Eₙ}` of a sequence of sets, §5.5) — `setKernel`
* Theorem 5.4 (§5.6) — `thm2_5_4`
* Lemma 5.3 (§5.6) — `lemma2_5_3`
* Unlabelled (§5.6, P1:2339–2343): case B, the kernel of the image domains is the plane punctured at the value taken
  at all but one point — `setKernel_caseB`
* Unlabelled (§5.6, P1:2345): case C, a constant limit lies neither in the kernel of the image domains nor in the
  kernel of their complements — `setKernel_caseC`
* Theorem 5.5 (§5.6) — `thm2_5_5`
* Unlabelled (§5.7, P1:2355–2359; cited as "the results of II.5" at P1:6015, P2:325): for a domain with a single
  boundary point `a`, in the cases A and B the kernel of the image domains is the plane punctured at one point, onto
  which `w` maps in case A — `setKernel_onePointBoundary_i`, `setKernel_onePointBoundary_ii`

The discussion of the cases A–C for convergence on an everywhere dense set (§5.3, P1:2264–2274; summarized by Theorem
5.2, with examples), the immediate remark that the kernel is open (P1:2315, first sentence; the second sentence, that
the kernel of a sequence of domains need not be connected, is also U−), the second sentence of P1:2347 (the kernels of a
constant sequence of domains), and the rest of §5.7 (the whole plane, trivial, P1:2353; the constant case with its
example, P1:2361–2365) are not stated (inventory: omitted).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §5.1 Normal families -/

/-- **Lemma 5.1** (Ch. II §5.1). Let `wₙ`, `n = 1, 2, …`, be a sequence of mappings, equicontinuous in a domain `G`,
and `E` an everywhere dense subset of `G`. If the sequence `wₙ` converges at every point of `E`, then it is uniformly
convergent in every compact subset of `G`.
Modelling: "everywhere dense in `G`" is `G ⊆ derivedSet E` (footnote 20); the conclusion names the limit `w` (`ℂ̄` is
compact, so a uniformly Cauchy sequence converges uniformly). -/
theorem lemma2_5_1 {wn : ℕ → ExtPlane → ExtPlane} {G E : Set ExtPlane} (hG : IsDomainExt G)
    (heq : IsEquicontinuousOnSph (range wn) G G) (hEG : E ⊆ G) (hE : G ⊆ derivedSet E)
    (hconv : ∀ a ∈ E, ∃ c : ExtPlane, Tendsto (fun n => wn n a) atTop (𝓝 c)) :
    ∃ w : ExtPlane → ExtPlane, TendstoUniformlyOnCompactsSph wn w G := by
  sorry

/-- **Definition** (normal family, Ch. II §5.1). A family `𝒲` of continuous mappings of the domain `G` is normal if
every sequence of elements of `𝒲` contains a subsequence which converges uniformly in every compact subset of `G`.
Modelling: the continuity of the members on `G` is part of the definition; the limit of the subsequence is named
(`ℂ̄` is compact). -/
def IsNormalFamilySph (𝒲 : Set (ExtPlane → ExtPlane)) (G : Set ExtPlane) : Prop :=
  (∀ w ∈ 𝒲, ContinuousOn w G) ∧
    ∀ wn : ℕ → ExtPlane → ExtPlane, (∀ n, wn n ∈ 𝒲) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ExtPlane → ExtPlane, TendstoUniformlyOnCompactsSph (wn ∘ φ) w G

/-- **Lemma 5.2** (Ch. II §5.1). A family of mappings which is equicontinuous in a domain `G` is normal. -/
theorem lemma2_5_2 {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} (hG : IsDomainExt G)
    (heq : IsEquicontinuousOnSph 𝒲 G G) : IsNormalFamilySph 𝒲 G := by
  sorry

/-! ## §5.2 Normality criteria for families of quasiconformal mappings -/

/-- **Unlabelled** (Ch. II §5.1–5.2, P1:2238, 2248). The equicontinuity, Hölder continuity and normality of a family
of `K`-quasiconformal mappings of a domain `G` are equivalent concepts. (LV's remark that a normal family of
continuous mappings is equicontinuous, P1:2238, is "easy to see" and not cited; it is covered here only for
families of `K`-quasiconformal mappings.)
Modelling: Hölder continuity of the family in `G` is Hölder continuity at every point of `G` with some positive
exponent (by Theorem 4.3 the exponent `1/K` can be taken). -/
theorem kqcFamily_tfae {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) :
    List.TFAE [IsEquicontinuousOnSph 𝒲 G G, ∀ z₀ ∈ G, ∃ α > 0, IsHolderAtSph 𝒲 G α z₀, IsNormalFamilySph 𝒲 G] := by
  sorry

/-- **Theorem 5.1, 1°** (Ch. II §5.2). A family `𝒲` of `K`-quasiconformal mappings of the domain `G` is normal if
there is a number `d > 0` such that every mapping `w ∈ 𝒲` omits two values whose spherical distance is greater than
`d`.
Modelling: `G` is a domain as in `thm2_4_1`. -/
theorem thm2_5_1_i {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d)
    (homit : ∀ w ∈ 𝒲, ∃ a b : ExtPlane, a ∉ w '' G ∧ b ∉ w '' G ∧ d < sphericalDist a b) :
    IsNormalFamilySph 𝒲 G := by
  sorry

/-- **Theorem 5.1, 2°** (Ch. II §5.2). A family `𝒲` of `K`-quasiconformal mappings of the domain `G` is normal if
there is a number `d > 0` such that every mapping `w ∈ 𝒲` omits one value `a` and at two fixed points `z₁, z₂ ∈ G`
takes values such that the distances `k(w(zᵢ), a)`, `i = 1, 2`, are greater than `d`.
Modelling: as in Theorem 4.2, 1° (`thm2_4_2_i`), the two fixed points are distinct, `z₁ ≠ z₂`. For `z₁ = z₂` the
statement is false: the conformal mappings `wₙ(z) = nz` of the finite plane omit `a = ∞` and
`k(wₙ(0), ∞) = π/2 > 1 = d` with `z₁ = z₂ = 0`, but no subsequence converges uniformly near `0` (the pointwise limit
is `0` at `0` and `∞` elsewhere). `G` is a domain as in `thm2_4_1`. -/
theorem thm2_5_1_ii {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d) {z₁ z₂ : ExtPlane} (hz₁ : z₁ ∈ G) (hz₂ : z₂ ∈ G)
    (h₁₂ : z₁ ≠ z₂)
    (homit : ∀ w ∈ 𝒲, ∃ a : ExtPlane, a ∉ w '' G ∧ d < sphericalDist (w z₁) a ∧ d < sphericalDist (w z₂) a) :
    IsNormalFamilySph 𝒲 G := by
  sorry

/-- **Theorem 5.1, 3°** (Ch. II §5.2). A family `𝒲` of `K`-quasiconformal mappings of the domain `G` is normal if
there is a number `d > 0` such that every mapping `w ∈ 𝒲` takes values at three fixed points `z₁, z₂, z₃ ∈ G` such
that the distances `k(w(zᵢ), w(zⱼ))`, `i, j = 1, 2, 3`, `i ≠ j`, are greater than `d`.
Modelling: the three points are `z 0, z 1, z 2`; `G` is a domain as in `thm2_4_1`. -/
theorem thm2_5_1_iii {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K d : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) (hd : 0 < d) {z : Fin 3 → ExtPlane} (hz : ∀ i, z i ∈ G)
    (hsep : ∀ w ∈ 𝒲, ∀ i j, i ≠ j → d < sphericalDist (w (z i)) (w (z j))) :
    IsNormalFamilySph 𝒲 G := by
  sorry

/-- **Theorem 5.1**, last sentence (Ch. II §5.2). In particular a family `𝒲` of `K`-quasiconformal mappings of the
domain `G` is normal if all mappings `w ∈ 𝒲` omit two fixed values.
Modelling: the two values are distinct, `a ≠ b`; `G` is a domain as in `thm2_4_1`. -/
theorem thm2_5_1_omit_two {𝒲 : Set (ExtPlane → ExtPlane)} {G : Set ExtPlane} {K : ℝ} (hG : IsDomainExt G)
    (h𝒲 : ∀ w ∈ 𝒲, IsKQuasiconformal w G K) {a b : ExtPlane} (hab : a ≠ b)
    (homit : ∀ w ∈ 𝒲, a ∉ w '' G ∧ b ∉ w '' G) : IsNormalFamilySph 𝒲 G := by
  sorry

/-! ## §5.3 Classification of the limit functions -/

/-- **Theorem 5.2** (Ch. II §5.3). If `wₙ` is a sequence of `K`-quasiconformal mappings of the domain `G` and `wₙ`
converges everywhere in `G` to a limit function `w`, then `w` is either a continuous non-constant function, or a
mapping of `G` onto two points, or a constant. In the first case the sequence `wₙ` converges uniformly in every compact
subset of `G`; in the second the limit function `w` takes one of its values at only one point `a` of `G` and the
convergence is uniform in every compact subset of `G - {a}`.
Modelling: a three-way disjunction; in the second case `w` takes the value `c₁` at `a` and `c₂ ≠ c₁` elsewhere in
`G`. -/
theorem thm2_5_2 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) :
    (ContinuousOn w G ∧ (∃ z₁ ∈ G, ∃ z₂ ∈ G, w z₁ ≠ w z₂) ∧ TendstoUniformlyOnCompactsSph wn w G) ∨
      (∃ a ∈ G, ∃ c₁ c₂ : ExtPlane, c₁ ≠ c₂ ∧ w a = c₁ ∧ (∀ z ∈ G, z ≠ a → w z = c₂) ∧
        TendstoUniformlyOnCompactsSph wn w (G \ {a})) ∨
      ∃ c : ExtPlane, ∀ z ∈ G, w z = c := by
  sorry

/-! ## §5.4 Quasiconformal limit functions -/

/-- **Theorem 5.3** (Ch. II §5.4). The limit function `w` of a sequence `wₙ` of `K`-quasiconformal mappings convergent
in `G` is either a constant, a mapping of `G` onto two points, or a `K`-quasiconformal mapping of `G`. -/
theorem thm2_5_3 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) :
    (∃ c : ExtPlane, ∀ z ∈ G, w z = c) ∨ (∃ c₁ c₂ : ExtPlane, c₁ ≠ c₂ ∧ w '' G = {c₁, c₂}) ∨
      IsKQuasiconformal w G K := by
  sorry

/-! ## §5.5 Kernel of a sequence of sets -/

/-- **Definition** (kernel of a sequence of sets, Ch. II §5.5). The kernel `N{Eₙ}` of a sequence of point sets `Eₙ` is
the set `⋃_{m ≥ 1} (⋂_{n ≥ m} Eₙ)°`, where `(⋂ Eₙ)°` is the interior of `⋂ Eₙ`: a point `z` belongs to `N{Eₙ}` if and
only if there exist a neighbourhood `U` of `z` and a number `m` such that `U ⊂ Eₙ` for `n ≥ m`.
Modelling: the sequence is indexed from `0`; the kernel does not depend on finitely many terms. -/
def setKernel (E : ℕ → Set ExtPlane) : Set ExtPlane := ⋃ m, interior (⋂ n ≥ m, E n)

/-! ## §5.6 Mappings of a domain with at least two boundary points -/

/-- **Theorem 5.4** (Ch. II §5.6). Let `wₙ : G → G′ₙ` be `K`-quasiconformal mappings of a domain `G` with at least two
boundary points. If the sequence `wₙ` converges in `G` to a quasiconformal mapping `w`, then `w(G) = G′` coincides with
a component of `N{G′ₙ}`.
Modelling: `G′ₙ = wₙ(G)`; a component of `N{G′ₙ}` is the connected component in `N{G′ₙ}` of one of its points. -/
theorem thm2_5_4 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hbd : ∃ a ∈ frontier G, ∃ b ∈ frontier G, a ≠ b)
    (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) (hw : IsQuasiconformalMap w G) :
    ∃ c ∈ setKernel (fun n => wn n '' G), w '' G = connectedComponentIn (setKernel (fun n => wn n '' G)) c := by
  sorry

/-- **Lemma 5.3** (Ch. II §5.6). Let `G` be a domain possessing at least two boundary points and `wₙ : G → G′ₙ` a
sequence of `K`-quasiconformal mappings which converges in `G`. Then the limit function `w = lim wₙ` takes no value
lying in `N{G′ₙ}` at two different points of `G`. -/
theorem lemma2_5_3 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hbd : ∃ a ∈ frontier G, ∃ b ∈ frontier G, a ≠ b)
    (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) :
    ∀ z₁ ∈ G, ∀ z₂ ∈ G, w z₁ = w z₂ → w z₁ ∈ setKernel (fun n => wn n '' G) → z₁ = z₂ := by
  sorry

/-- **Unlabelled** (Ch. II §5.6, P1:2339–2343, case B). In the situation of Lemma 5.3, let the limit function `w` be a
mapping of `G` onto two points, taking the value `c₁` at a single point `z₁ ∈ G` and `c₂ ≠ c₁` at all other points of
`G`. Then the set `N{G′ₙ}` is the whole plane with `c₂` removed. -/
theorem setKernel_caseB {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hbd : ∃ a ∈ frontier G, ∃ b ∈ frontier G, a ≠ b)
    (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) {z₁ c₂ : ExtPlane} (hz₁ : z₁ ∈ G)
    (hc : w z₁ ≠ c₂) (hw : ∀ z ∈ G, z ≠ z₁ → w z = c₂) :
    setKernel (fun n => wn n '' G) = {c₂}ᶜ := by
  sorry

/-- **Unlabelled** (Ch. II §5.6, P1:2345, case C). In the situation of Lemma 5.3, let the limit function `w` be a
mapping of `G` onto a single point `c`. Then `c` belongs neither to `N{G′ₙ}` nor to `N{-G′ₙ}`, `-G′ₙ` being the
complement of `G′ₙ`. -/
theorem setKernel_caseC {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K) (hbd : ∃ a ∈ frontier G, ∃ b ∈ frontier G, a ≠ b)
    (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) {c : ExtPlane} (hw : ∀ z ∈ G, w z = c) :
    c ∉ setKernel (fun n => wn n '' G) ∧ c ∉ setKernel (fun n => (wn n '' G)ᶜ) := by
  sorry

/-- **Unlabelled** (Ch. II §5.7, P1:2355–2359, case A). Let `G` be a domain with a single boundary point `a` and
`wₙ` a sequence of `K`-quasiconformal mappings of `G` converging in `G` to a `K`-quasiconformal mapping `w`. Then the
kernel `N{G′ₙ}` of the image domains is the plane punctured at one point, and `w` maps `G` onto `N{G′ₙ}`.
Modelling: `G = ℂ̄ \ {a}`; the puncture is `w(a)` for the extension of Theorem I.8.1. -/
theorem setKernel_onePointBoundary_i {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {a : ExtPlane}
    {K : ℝ} (hwn : ∀ n, IsKQuasiconformal (wn n) {a}ᶜ K)
    (hlim : ∀ z ∈ ({a}ᶜ : Set ExtPlane), Tendsto (fun n => wn n z) atTop (𝓝 (w z)))
    (hw : IsKQuasiconformal w {a}ᶜ K) :
    ∃ b : ExtPlane, setKernel (fun n => wn n '' {a}ᶜ) = {b}ᶜ ∧ w '' {a}ᶜ = {b}ᶜ := by
  sorry

/-- **Unlabelled** (Ch. II §5.7, P1:2355–2359, case B). Let `G` be a domain with a single boundary point `a` and
`wₙ` a sequence of `K`-quasiconformal mappings of `G` converging in `G` to a mapping `w` of `G` onto two points, the
value `c₂` taken everywhere except at a single point `z₁`. Then the kernel `N{G′ₙ}` is the plane punctured at `c₂`
(the single boundary point of `N{G′ₙ}` is the value taken at all but one point). -/
theorem setKernel_onePointBoundary_ii {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {a : ExtPlane}
    {K : ℝ} (hwn : ∀ n, IsKQuasiconformal (wn n) {a}ᶜ K)
    (hlim : ∀ z ∈ ({a}ᶜ : Set ExtPlane), Tendsto (fun n => wn n z) atTop (𝓝 (w z)))
    {z₁ c₂ : ExtPlane} (hz₁ : z₁ ≠ a) (hc : w z₁ ≠ c₂) (hw : ∀ z, z ≠ a → z ≠ z₁ → w z = c₂) :
    setKernel (fun n => wn n '' {a}ᶜ) = {c₂}ᶜ := by
  sorry

/-- **Theorem 5.5** (Ch. II §5.6). Let `G` be a domain possessing at least two boundary points and `wₙ` a sequence of
`K`-quasiconformal mappings of `G` onto a fixed domain `G′`. If `wₙ` converges in `G`, the limit function
`w = lim wₙ` is either a `K`-quasiconformal mapping of `G` onto `G′` or a mapping of `G` onto a boundary point of
`G′`. -/
theorem thm2_5_5 {wn : ℕ → ExtPlane → ExtPlane} {w : ExtPlane → ExtPlane} {G G' : Set ExtPlane} {K : ℝ}
    (hwn : ∀ n, IsKQuasiconformal (wn n) G K ∧ wn n '' G = G')
    (hbd : ∃ a ∈ frontier G, ∃ b ∈ frontier G, a ≠ b)
    (hlim : ∀ z ∈ G, Tendsto (fun n => wn n z) atTop (𝓝 (w z))) :
    (IsKQuasiconformal w G K ∧ w '' G = G') ∨ ∃ c ∈ frontier G', ∀ z ∈ G, w z = c := by
  sorry

end LehtoVirtanen1973
