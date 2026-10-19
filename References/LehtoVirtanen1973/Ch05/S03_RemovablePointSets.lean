import References.LehtoVirtanen1973.Ch01.S09_LocalCharacterization

/-!
# Lehto–Virtanen, Chapter V §3: Removable point sets

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §3
(pp. 199–207; `full.md` second part P2:127–308).

Throughout §3, `G` is a domain of `ℂ̄`, `E ⊂ G` a point set and `K` a number with `1 ≤ K < ∞` (P2:131). The local
maximal dilatation `F` is `localMaxDil w G` (I.9.1, `ℝ≥0∞`-valued). The area of a set of `ℂ̄` is that of its finite
part, and the linear measure is the one-dimensional Hausdorff measure `μH[1]` (III.1.8) of the finite part; a set has
σ-finite linear measure when `μH[1]` restricted to it is σ-finite (III.1.2: it is a countable union of sets of finite
linear measure). The book's range `1 ≤ K` is a hypothesis of every statement about removability: for `K < 1` the
classes `𝒲₁`, `𝒲₂`, `𝒲₃` contain no mapping (when `G − E ≠ ∅`), removability is then vacuous, and the independence
of `K` and the consequences of removability with respect to `𝒲₃` would fail. In §3.6, `E` is compact (P2:283).

* Definition (the classes `𝒲₁`, `𝒲₂`, `𝒲₃` with the condition (3.1); removability with respect to them, §3.1) —
  `IsRemovableW1`, `IsRemovableW2`, `IsRemovableW3`
* Unlabelled (§3.2, P2:157; proved at P2:197, 265, 279): removability does not depend on `K` —
  `isRemovableW1_indep_K`, `isRemovableW2_indep_K`, `isRemovableW3_indep_K`
* Lemma 3.1 (§3.2) — `lemma5_3_1_i`, `lemma5_3_1_ii`, `lemma5_3_1_iii`
* Theorem 3.1 (§3.3) — `thm5_3_1`
* Unlabelled (§3.3, P2:181, 197; recalled at P2:201, 299, 307): Theorem 3.1 solves the removability problem for `𝒲₁`:
  a set is removable with respect to `𝒲₁` if and only if every compact subset has area zero — `isRemovableW1_iff`
* Theorem 3.2 (§3.4, Strebel) — `thm5_3_2`
* Lemma 3.2 (§3.5) — `lemma5_3_2`
* Unlabelled (§3.5, P2:267, 273; announced at P2:147, recalled at P2:307): a set removable with respect to `𝒲₃` has
  area zero, is removable with respect to `𝒲₁` and `𝒲₂`, and so are its subsets with respect to `𝒲₃` —
  `isRemovableW3_volume_eq_zero`, `isRemovableW3_isRemovableW12`, `isRemovableW3_mono`
* Theorem 3.3 (§3.5, cf. Pesin) — `thm5_3_3`
* Unlabelled (§3.6, P2:281): removability with respect to `𝒲₃` is equivalent to the conformal extendability of all
  conformal mappings of `G − E` — `isRemovableW3_iff_conformalExtension`
* Definition (null class `O_AD`, §3.6) — `IsNullClassOAD`
* Equivalence theorem (§3.6, quoted from Sario and Ahlfors–Beurling) — `oad_equivalence_theorem`
* Unlabelled (§3.6, P2:295; cited at P2:303, 307): for compact `E`, removability with respect to `𝒲₃` is
  equivalent to `E ∈ O_AD` — `isRemovableW3_iff_isNullClassOAD`
* Unlabelled (§3.6, P2:297, quoted from Ahlfors–Beurling; cited at P2:303): every compact set of zero linear measure
  belongs to `O_AD` — `isNullClassOAD_of_hausdorffMeasure_eq_zero`
* Unlabelled (§3.7, P2:301, from the example IV.2.2): there are sets of dimension `1` which are not removable with
  respect to `𝒲₂` — `exists_dimH_one_not_isRemovableW2`
* Unlabelled (§3.7, P2:303–305): there are sets of finite linear measure which are not removable with respect to
  `𝒲₃`, for example a segment — `exists_hausdorffMeasure_lt_top_not_isRemovableW3`
* Unlabelled (§3.7, P2:307, quoted from Sario): there are compact sets of dimension `2` in `O_AD`, hence removable
  with respect to `𝒲₂` and `𝒲₃` — `exists_removable_dimH_two`

Not stated (inventory: omitted, U−): the reformulation of the three removability notions when `G - E` is a domain
(P2:145, a restatement of the definitions); the monotonicity of removability with respect to `𝒲₁` and `𝒲₂` (P2:147,
immediate from the definitions); that Theorems I.8.1 and I.8.3 are special cases (P2:149, a restatement of
`thm1_8_1`, `thm1_8_3`); the Remark on an alternative definition of removability (P2:151–155, not adopted by the
book); the necessity of the condition of Theorem 3.1 for removability with respect to `𝒲₂` (P2:201: immediate from
`isRemovableW1_iff`, since `𝒲₁` is a subclass of `𝒲₂`); the set-up of §3.6 that `-E` is a domain, with footnote 47
on its converse (P2:283, a remark of the set-up; its assumptions, `E` compact and `G − E` a domain, are hypotheses of
the statements of §3.6 and part of `exists_removable_dimH_two`); Koebe's slit-domain theorem quoted inside the proof
of Lemma 3.2 (P2:271); and footnote 48 (the complement of a compact set of zero linear measure is connected).
Footnote 46 is bibliographic. The recollection at P2:307 that the inner area of a set removable with respect to `𝒲₂`
or `𝒲₃` vanishes is `isRemovableW1_iff` (with P2:201) and `isRemovableW3_volume_eq_zero`. The book's own proof of the
independence of `K` for `𝒲₃` (P2:279) derives it from Theorem 3.3.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane)
open References (IsDomainExt finitePart)

/-! ## §3.1 Three problems of removability -/

/-- **Definition** (removability with respect to the class `𝒲₁`, Ch. V §3.1). The class `𝒲₁` consists of all
quasiconformal mappings of `G` whose local maximal dilatation satisfies `sup_{z ∈ G − E} F(z) ≤ K` (3.1). The set `E`
is removable with respect to `𝒲₁` if all mappings of this class are `K`-quasiconformal in the whole domain `G`.
Modelling: the class is not reified; (3.1) is `F(z) ≤ K` at every point of `G − E`. Junk: for `K < 1` (outside the
book's range `1 ≤ K < ∞`) the class is empty when `G − E ≠ ∅` and the predicate holds vacuously; every statement
assumes `1 ≤ K`. -/
def IsRemovableW1 (G E : Set ExtPlane) (K : ℝ) : Prop :=
  ∀ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G → (∀ z ∈ G \ E, localMaxDil w G z ≤ ENNReal.ofReal K) →
    IsKQuasiconformal w G K

/-- **Definition** (removability with respect to the class `𝒲₂`, Ch. V §3.1). The class `𝒲₂` consists of all
sense-preserving homeomorphisms of `G` satisfying (3.1); `E` is removable with respect to `𝒲₂` if all mappings of this
class are `K`-quasiconformal in the whole domain `G`.
Modelling and junk value (`K < 1`) as for `IsRemovableW1`. -/
def IsRemovableW2 (G E : Set ExtPlane) (K : ℝ) : Prop :=
  ∀ w : ExtPlane → ExtPlane, IsSensePreservingOn w G → (∀ z ∈ G \ E, localMaxDil w G z ≤ ENNReal.ofReal K) →
    IsKQuasiconformal w G K

/-- **Definition** (removability with respect to the class `𝒲₃`, Ch. V §3.1). The class `𝒲₃`, which is only defined
when `G − E` is a domain, consists of all `K`-quasiconformal mappings of `G − E`; `E` is removable with respect to
`𝒲₃` if every mapping of this class can be extended to a `K`-quasiconformal mapping of `G`.
Modelling: "`G − E` is a domain" is a conjunct, since the class (and so the removability) is defined only then; an
extension is a `K`-quasiconformal mapping of `G` which agrees with the mapping on `G − E`. Junk: for `K < 1` the
class is empty and the second conjunct holds vacuously; every statement assumes `1 ≤ K`. -/
def IsRemovableW3 (G E : Set ExtPlane) (K : ℝ) : Prop :=
  IsDomainExt (G \ E) ∧ ∀ w : ExtPlane → ExtPlane, IsKQuasiconformal w (G \ E) K →
    ∃ W : ExtPlane → ExtPlane, IsKQuasiconformal W G K ∧ EqOn W w (G \ E)

/-! ## §3.2 Independence of the removability on the maximal dilatation -/

/-- **Unlabelled** (Ch. V §3.2, P2:157; for `𝒲₁` shown at P2:197 from Theorem 3.1). The value of `K` has no influence
on the removability problem for `𝒲₁`: if a set is removable with respect to `𝒲₁` for some value of `K`, then the same
is true for every other `K`.
Modelling: `1 ≤ K` and `1 ≤ K′` are the book's range of `K` (P2:131); for `K < 1` removability is vacuous, and the
claim would make every set removable. -/
theorem isRemovableW1_indep_K {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K K' : ℝ} (hK : 1 ≤ K)
    (hK' : 1 ≤ K') (h : IsRemovableW1 G E K) : IsRemovableW1 G E K' := by
  sorry

/-- **Unlabelled** (Ch. V §3.2, P2:157; for `𝒲₂` shown at P2:265). If a set is removable with respect to `𝒲₂` for some
value of `K`, then the same is true for every other `K`.
Modelling: as for `isRemovableW1_indep_K`. -/
theorem isRemovableW2_indep_K {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K K' : ℝ} (hK : 1 ≤ K)
    (hK' : 1 ≤ K') (h : IsRemovableW2 G E K) : IsRemovableW2 G E K' := by
  sorry

/-- **Unlabelled** (Ch. V §3.2, P2:157; for `𝒲₃` shown at P2:279 from Theorem 3.3). If a set is removable with respect
to `𝒲₃` for some value of `K`, then the same is true for every other `K`.
Modelling: as for `isRemovableW1_indep_K`. -/
theorem isRemovableW3_indep_K {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K K' : ℝ} (hK : 1 ≤ K)
    (hK' : 1 ≤ K') (h : IsRemovableW3 G E K) : IsRemovableW3 G E K' := by
  sorry

/-- **Lemma 3.1** (Ch. V §3.2), for the class `𝒲₁`. Let `E ⊂ G` be a set which is removable with respect to `𝒲₁` for
`K = 1`. Then `E` has no interior points and is removable relative to `𝒲₁` for every `K`.
Modelling: interior points in `ℂ̄`; "every `K`" is every `K` of the book's range `1 ≤ K`. -/
theorem lemma5_3_1_i {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) (h : IsRemovableW1 G E 1) :
    interior E = ∅ ∧ ∀ K : ℝ, 1 ≤ K → IsRemovableW1 G E K := by
  sorry

/-- **Lemma 3.1** (Ch. V §3.2), for the class `𝒲₂`. Let `E ⊂ G` be a set which is removable with respect to `𝒲₂` for
`K = 1`. Then `E` has no interior points and is removable relative to `𝒲₂` for every `K`.
Modelling: as for `lemma5_3_1_i`. -/
theorem lemma5_3_1_ii {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) (h : IsRemovableW2 G E 1) :
    interior E = ∅ ∧ ∀ K : ℝ, 1 ≤ K → IsRemovableW2 G E K := by
  sorry

/-- **Lemma 3.1** (Ch. V §3.2), for the class `𝒲₃`. Let `E ⊂ G` be a set which is removable with respect to `𝒲₃` for
`K = 1`. Then `E` has no interior points and is removable relative to `𝒲₃` for every `K`.
Modelling: as for `lemma5_3_1_i`. -/
theorem lemma5_3_1_iii {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) (h : IsRemovableW3 G E 1) :
    interior E = ∅ ∧ ∀ K : ℝ, 1 ≤ K → IsRemovableW3 G E K := by
  sorry

/-! ## §3.3 Removability of a set with respect to the class `𝒲₁` -/

/-- **Theorem 3.1** (Ch. V §3.3). Let `G` be a domain and `E` a subset of `G`. Then
`sup_{z ∈ G} F(z) = sup_{z ∈ G − E} F(z)` for the local maximal dilatation of every quasiconformal mapping of `G` if
and only if every compact subset of `E` has zero area.
Modelling: the suprema in `ℝ≥0∞`; the compact subsets are compact subsets of `ℂ̄` (they may contain `∞`), and their
area is that of their finite parts. `E` need not be measurable. -/
theorem thm5_3_1 {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) :
    (∀ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G →
        ⨆ z ∈ G, localMaxDil w G z = ⨆ z ∈ G \ E, localMaxDil w G z) ↔
      ∀ C ⊆ E, IsCompact C → volume (finitePart C) = 0 := by
  sorry

/-- **Unlabelled** (Ch. V §3.3, P2:181 and P2:197; recalled at P2:201, 299, 307). "For the class `𝒲₁` the removability
problem is solved" by Theorem 3.1: a set `E ⊂ G` is removable with respect to `𝒲₁` if and only if every compact subset
of `E` has zero area, i.e. the inner area of `E` vanishes; in particular this does not depend on `K` (P2:197).
Modelling: `1 ≤ K`, the book's range (for `K < 1` the class `𝒲₁` is empty when `G − E ≠ ∅`, and removability holds
vacuously); the compact subsets and their areas as in `thm5_3_1`. A quasiconformal mapping of `G` is
`K`-quasiconformal if and only if `F ≤ K` in `G` (Theorem I.9.1), so the claim is Theorem 3.1 read for one `K`, its
necessity half by the mapping of Theorem 2.2 constructed in the proof (P2:191). -/
theorem isRemovableW1_iff {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K : ℝ} (hK : 1 ≤ K) :
    IsRemovableW1 G E K ↔ ∀ C ⊆ E, IsCompact C → volume (finitePart C) = 0 := by
  sorry

/-! ## §3.4 Removability of a set with respect to `𝒲₂` -/

/-- **Theorem 3.2** (Ch. V §3.4, Strebel). If every compact subset of the set `E ⊂ G` has σ-finite linear measure, then
`sup_{z ∈ G} F(z) = sup_{z ∈ G − E} F(z)` for every sense-preserving homeomorphism of the domain `G`.
Modelling: σ-finite linear measure of a compact `C ⊆ ℂ̄`: the one-dimensional Hausdorff measure restricted to the
finite part of `C` is σ-finite; the suprema in `ℝ≥0∞` (for a sense-preserving homeomorphism `F` may be `∞`). -/
theorem thm5_3_2 {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G)
    (hσ : ∀ C ⊆ E, IsCompact C → SigmaFinite ((μH[1] : Measure ℂ).restrict (finitePart C)))
    {w : ExtPlane → ExtPlane} (hw : IsSensePreservingOn w G) :
    ⨆ z ∈ G, localMaxDil w G z = ⨆ z ∈ G \ E, localMaxDil w G z := by
  sorry

/-! ## §3.5 Removability of a set with respect to `𝒲₃` -/

/-- **Lemma 3.2** (Ch. V §3.5). Let `E` be a subset of the domain `G` such that `G − E` is a domain. If the area of `E`
is positive, then there exists a conformal mapping of `G − E` which cannot be quasiconformally extended to `G`.
Modelling: the area is the (outer) area of the finite part of `E`; the conformal mapping may take the value `∞` (the
proof maps `G − E` onto a slit domain); "cannot be quasiconformally extended" means that no quasiconformal mapping of
`G` agrees with it on `G − E`. -/
theorem lemma5_3_2 {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) (hGE : IsDomainExt (G \ E))
    (hpos : 0 < volume (finitePart E)) :
    ∃ f : ExtPlane → ExtPlane, IsConformalMap f (G \ E) ∧
      ¬ ∃ W : ExtPlane → ExtPlane, IsQuasiconformalMap W G ∧ EqOn W f (G \ E) := by
  sorry

/-- **Unlabelled** (Ch. V §3.5, P2:267, from Lemma 3.2). Every set removable with respect to `𝒲₃` has area zero.
Modelling: `1 ≤ K`, the book's range (for `K < 1` removability with respect to `𝒲₃` only says that `G − E` is a
domain). -/
theorem isRemovableW3_volume_eq_zero {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K : ℝ} (hK : 1 ≤ K)
    (h : IsRemovableW3 G E K) : volume (finitePart E) = 0 := by
  sorry

/-- **Unlabelled** (Ch. V §3.5, P2:273; recalled at P2:307). A set which is removable with respect to `𝒲₃` is
removable also with respect to `𝒲₁` and `𝒲₂` (it has area zero, so it has no interior points, and a quasiconformal
mapping of `G − E` can be extended to `E` in at most one way).
Modelling: the same `K`, with `1 ≤ K` as in `isRemovableW3_volume_eq_zero`. -/
theorem isRemovableW3_isRemovableW12 {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K : ℝ} (hK : 1 ≤ K)
    (h : IsRemovableW3 G E K) : IsRemovableW1 G E K ∧ IsRemovableW2 G E K := by
  sorry

/-- **Unlabelled** (Ch. V §3.5, P2:273; announced at P2:147). Every subset of a set removable with respect to `𝒲₃` is
removable (with respect to `𝒲₃`).
Modelling: the subset `E′` is one for which `G − E′` is a domain, since the class `𝒲₃` of `E′`, and so its
removability, is defined only then (the book leaves this proviso implicit); `1 ≤ K` as in
`isRemovableW3_volume_eq_zero`. -/
theorem isRemovableW3_mono {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) {K : ℝ} (hK : 1 ≤ K)
    (h : IsRemovableW3 G E K) {E' : Set ExtPlane} (hE' : E' ⊆ E) (hGE' : IsDomainExt (G \ E')) :
    IsRemovableW3 G E' K := by
  sorry

/-- **Theorem 3.3** (Ch. V §3.5, cf. Pesin). Let `G` be a domain and `E` a subset of `G` such that `G − E` is also a
domain. If every conformal mapping of `G − E` has a quasiconformal extension to `G`, then every `K`-quasiconformal
mapping of `G − E` can be extended to a `K`-quasiconformal mapping of `G`.
Modelling: an extension is a mapping of `G` which agrees with the given one on `G − E`; the conformal mappings may
take the value `∞`. No hypothesis `1 ≤ K` is needed: for `K < 1` there is no `K`-quasiconformal mapping. -/
theorem thm5_3_3 {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G) (hGE : IsDomainExt (G \ E))
    (hconf : ∀ f : ExtPlane → ExtPlane, IsConformalMap f (G \ E) →
      ∃ W : ExtPlane → ExtPlane, IsQuasiconformalMap W G ∧ EqOn W f (G \ E))
    {K : ℝ} {w : ExtPlane → ExtPlane} (hw : IsKQuasiconformal w (G \ E) K) :
    ∃ W : ExtPlane → ExtPlane, IsKQuasiconformal W G K ∧ EqOn W w (G \ E) := by
  sorry

/-! ## §3.6 A function-theoretical removability problem -/

/-- **Unlabelled** (Ch. V §3.6, P2:281). Since the removability problem for `𝒲₃` is independent of `K`, it is
equivalent to the purely function-theoretical problem: `E` is removable with respect to `𝒲₃` if and only if every
conformal mapping of `G − E` can be extended to a conformal mapping of `G`.
Modelling: `E ⊂ G` with `G − E` a domain (the book's standing assumption for `𝒲₃`; compactness is assumed only from
P2:283 on); `1 ≤ K`, the book's range; an extension agrees with the mapping on `G − E`. -/
theorem isRemovableW3_iff_conformalExtension {G E : Set ExtPlane} (hG : IsDomainExt G) (hE : E ⊆ G)
    (hGE : IsDomainExt (G \ E)) {K : ℝ} (hK : 1 ≤ K) :
    IsRemovableW3 G E K ↔ ∀ f : ExtPlane → ExtPlane, IsConformalMap f (G \ E) →
      ∃ F : ExtPlane → ExtPlane, IsConformalMap F G ∧ EqOn F f (G \ E) := by
  sorry

/-- **Definition** (null class `O_AD`, Ch. V §3.6). `E` belongs to the null class `O_AD` if there exists no
non-constant analytic function `f` defined in `-E` such that `∬_{-E} |f′|² dσ < ∞`.
Modelling: `-E` is the complement of `E` in `ℂ̄`; `f` is a finite analytic function on the finite part of `-E`, and the
Dirichlet integral is taken over that finite part. When `∞ ∉ E` the book's `f` is also analytic at `∞`, and for a
finite Dirichlet integral this is automatic: if `f = Σ aₙ zⁿ` in `R < |z| < ∞`, then
`∬_{R < |z| < R′} |f′|² dσ = π Σ_{n ≠ 0} n |aₙ|² (R′^{2n} - R^{2n})`, which stays bounded as `R′ → ∞` only if `aₙ = 0`
for `n ≥ 1`. "Non-constant" is: two points of the finite part of `-E` with different values (the book uses `O_AD`
for compact `E` with `-E` a domain, P2:283, whose finite part is connected). For `E` not closed the finite part of
`-E` is not open and `DifferentiableOn` there does not give complex derivatives, so `deriv` may take its junk value
`0`; this case is outside the book's use (every statement assumes `IsCompact E`). For `E = ℂ̄` (`-E = ∅`) the
predicate holds vacuously; statements exclude it (`E` is a compact subset of a domain `G` with `G − E` a domain, or
of zero linear measure). -/
def IsNullClassOAD (E : Set ExtPlane) : Prop :=
  ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (finitePart Eᶜ) ∧
    (∃ a ∈ finitePart Eᶜ, ∃ b ∈ finitePart Eᶜ, f a ≠ f b) ∧ ∫⁻ z in finitePart Eᶜ, ‖deriv f z‖ₑ ^ 2 < ⊤

/-- **Equivalence theorem** (Ch. V §3.6, quoted from Sario and Ahlfors–Beurling). Let `E` be a compact subset of the
domain `G` such that `G − E` is a domain. The set `E` belongs to the null class `O_AD` if and only if every conformal
mapping of `G − E` can be extended to a conformal mapping of `G`.
Modelling: the standing assumptions of §3.6 (P2:283) are hypotheses; an extension agrees with the mapping on
`G − E`. -/
theorem oad_equivalence_theorem {G E : Set ExtPlane} (hG : IsDomainExt G) (hEc : IsCompact E) (hE : E ⊆ G)
    (hGE : IsDomainExt (G \ E)) :
    IsNullClassOAD E ↔ ∀ f : ExtPlane → ExtPlane, IsConformalMap f (G \ E) →
      ∃ F : ExtPlane → ExtPlane, IsConformalMap F G ∧ EqOn F f (G \ E) := by
  sorry

/-- **Unlabelled** (Ch. V §3.6, P2:295; cited at P2:303, 307). By the Equivalence theorem, the removability of `E` with
respect to `𝒲₃` is equivalent to `E ∈ O_AD`, provided that `E` is a compact subset of `G` and `G − E` is a domain.
Modelling: `1 ≤ K`, the book's range. -/
theorem isRemovableW3_iff_isNullClassOAD {G E : Set ExtPlane} (hG : IsDomainExt G) (hEc : IsCompact E)
    (hE : E ⊆ G) (hGE : IsDomainExt (G \ E)) {K : ℝ} (hK : 1 ≤ K) : IsRemovableW3 G E K ↔ IsNullClassOAD E := by
  sorry

/-- **Unlabelled** (Ch. V §3.6, P2:297, quoted from Ahlfors–Beurling; cited at P2:303). Every set `E` of zero linear
measure belongs to `O_AD`.
Modelling: `E` compact, the standing assumption of §3.6 (P2:283; P2:303 restates the claim for compact sets); the
linear measure is `μH[1]` of the finite part of `E`. -/
theorem isNullClassOAD_of_hausdorffMeasure_eq_zero {E : Set ExtPlane} (hEc : IsCompact E)
    (hE : (μH[1] : Measure ℂ) (finitePart E) = 0) : IsNullClassOAD E := by
  sorry

/-! ## §3.7 Examples -/

/-- **Unlabelled** (Ch. V §3.7, P2:301). The condition of Theorem 3.2 cannot be improved very much: by the example
IV.2.2 (a non-quasiconformal homeomorphism of a square with `F(z) = 1` outside a set of dimension `1`) there exist
sets of dimension `1` which are not removable with respect to `𝒲₂`.
Modelling: `E ⊂ G`, `G` a domain; not removable for any `K ≥ 1` (removability does not depend on `K`, 3.2). -/
theorem exists_dimH_one_not_isRemovableW2 :
    ∃ G E : Set ExtPlane, IsDomainExt G ∧ E ⊆ G ∧ dimH (finitePart E) = 1 ∧ ∀ K : ℝ, 1 ≤ K → ¬ IsRemovableW2 G E K := by
  sorry

/-- **Unlabelled** (Ch. V §3.7, P2:303–305). The sufficient condition of 3.6 (a compact set of zero linear measure is
removable with respect to `𝒲₃`) cannot be sharpened very much either: there exist sets of finite linear measure which
are not removable with respect to `𝒲₃`. A simple example is a segment.
Modelling: stated existentially, like `exists_dimH_one_not_isRemovableW2` (the book's example is a segment). The
witness lies in the setting of 3.6 with which the claim is compared (P2:283): `E` is a compact subset of the domain `G`
and `G − E` is a domain, so that the non-removability is not merely the failure of `G − E` to be a domain (a conjunct
of `IsRemovableW3`). The linear measure is `μH[1]` of the finite part of `E`; not removable for any `K ≥ 1`
(removability does not depend on `K`, 3.2). -/
theorem exists_hausdorffMeasure_lt_top_not_isRemovableW3 :
    ∃ G E : Set ExtPlane, IsDomainExt G ∧ IsCompact E ∧ E ⊆ G ∧ IsDomainExt (G \ E) ∧
      (μH[1] : Measure ℂ) (finitePart E) < ⊤ ∧ ∀ K : ℝ, 1 ≤ K → ¬ IsRemovableW3 G E K := by
  sorry

/-- **Unlabelled** (Ch. V §3.7, P2:307, quoted from Sario). The inner area of a set which is removable with respect to
`𝒲₂` or `𝒲₃` vanishes (3.4, 3.5). As concerns the sharpness of this necessary condition: the Cartesian product `E` of
two congruent Cantor sets `E(p₁, p₂, …)` on the axes belongs to `O_AD` (and so is removable for `𝒲₃` by 3.6) provided
that their linear measure is zero; with `pₙ = (n + 1)⁻¹` moreover `dim E = 2` (Lemma III.1.2). Since sets removable for
`𝒲₃` are also removable for `𝒲₂`, there exist sets of dimension `2` which are removable with respect to `𝒲₂` and `𝒲₃`.
Modelling: stated existentially, the Cantor sets of III.2.9 not being formalized (leader decision D4); the whole
sentence is stated, with the setting of 3.6 (P2:283): `E` is a compact subset of the domain `G` and `G − E` is a
domain, where `E ∈ O_AD` is the removability with respect to `𝒲₃` (`isRemovableW3_iff_isNullClassOAD`). Without this
setting `E = ℂ̄` would be a witness, `IsNullClassOAD` holding vacuously for it. Removable for every `K ≥ 1`
(removability does not depend on `K`, 3.2). -/
theorem exists_removable_dimH_two :
    ∃ G E : Set ExtPlane, IsDomainExt G ∧ IsCompact E ∧ E ⊆ G ∧ IsDomainExt (G \ E) ∧ IsNullClassOAD E ∧
      dimH (finitePart E) = 2 ∧ ∀ K : ℝ, 1 ≤ K → IsRemovableW2 G E K ∧ IsRemovableW3 G E K := by
  sorry

end LehtoVirtanen1973
