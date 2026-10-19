import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties
import References.LehtoVirtanen1973.Ch03.S02_AbsoluteContinuity

/-!
# Lehto–Virtanen, Chapter III §3: Differentiability of mappings of plane domains

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §3
(pp. 127–132; `full.md` P1:3705–3886).

Conventions. `G` and `G′` are domains of the finite plane (`IsOpen G ∧ IsConnected G`); functions are finite
complex-valued functions `f : ℂ → ℂ` (their values off `G` do not enter), and a homeomorphism `f : G → G′` is
`LiZhongQC.IsHomeomorphOnto f G G'`. The partial derivatives `f_x`, `f_y` are the project's `LiZhongQC.partialX`,
`LiZhongQC.partialY`, the derivatives of `t ↦ f(z + t)` and `t ↦ f(z + it)` at `t = 0` (junk value `0` where they do
not exist); "`f_x` exists and is finite at `z`" is `DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0`, and the values
`f_x(z)`, `f_y(z)` are used only at points where the partial derivatives exist. From §3.3 on the book assumes that
`f` is sense-preserving (P1:3821); this standing hypothesis is `IsSensePreservingOn (OnePoint.map f) (toExt G)`
(Ch. I §1.5, for the extension of `f` to `ℂ̄` which fixes `∞`; the value at `∞` does not matter, `G` being a set of
the finite plane). "Almost everywhere" refers to the Lebesgue area measure (the exceptional set has outer measure
zero), "measurable" is null-measurable and "Borel" is `MeasurableSet` / `Measurable`, as in §1. The Jacobian `J` is
`partialJacobian f`, defined from the partial derivatives as in the book; integrals of `J` are the lower integrals of
`ofReal J`, which is faithful because `J ≥ 0` almost everywhere (recorded in `lemma3_3_3_i`).

* Unlabelled (§3.1, P1:3709, quoted from Saks): for a finite continuous function in a domain, the set of the points
  where `f_x` (resp. `f_y`) exists and is finite is a Borel set, and `f_x` (resp. `f_y`) is a Borel function in this
  set — `partials_borel`
* Definition (bounded variation on lines, §3.1, footnote 36) — `IsBVL`
* Definition (absolutely continuous on lines, §3.1, footnote 36) — exists: `LiZhongQC.IsACL` (continuity in the set,
  and absolute continuity on almost all horizontal and vertical closed segments of every closed rectangle contained
  in the set; footnote 36 allows the closed segments instead of the open ones; the set is arbitrary, here the domain)
* Unlabelled (§3.1, P1:3717; used with Lemma 3.1 at P1:5025, 5105, 5225, 5421, 5673, 5769): absolute continuity on
  lines implies bounded variation on lines — `isBVL_of_isACL`
* Lemma 3.1 (§3.1) — `lemma3_3_1`
* Definition (differentiability of `f` at `z₀`, §3.2, as in I.9) — exists: `DifferentiableAt` (over the reals: the
  expansion f(z) = f(z₀) + f_x(z₀)(x − x₀) + f_y(z₀)(y − y₀) + o(z − z₀) is real Fréchet differentiability)
* Theorem 3.1 (§3.2, Gehring–Lehto) — exists: `LiZhongQC.lemma9_1_menchoff` (for an open set D, which includes the
  domains of the book, and a homeomorphism of D onto its image D′, the image not required to be a domain; hypothesis:
  both partial derivatives exist and are finite almost everywhere in D; conclusion: f is real differentiable almost
  everywhere in D; the exceptional sets are Lebesgue null sets, as in the book)
* Definition (Jacobian `J = (i/2)(f_x f̄_y − f̄_x f_y)` of a function with partial derivatives, §3.3) —
  `partialJacobian`
* Lemma 3.2 (§3.3) — `lemma3_3_2`
* Unlabelled (§3.4, P1:3855, footnote 35): if the (sense-preserving) homeomorphism has finite partial derivatives
  almost everywhere, then `J = μ′_f` almost everywhere — `arealDeriv_eq_jacobian_ae`
* Lemma 3.3 (§3.4) — `lemma3_3_3_i`, `lemma3_3_3_ii`, `lemma3_3_3_iii`
* Lemma 3.4 (§3.4) — `lemma3_3_4`
* Lemma 3.5 (§3.4) — `lemma3_3_5_i`, `lemma3_3_5_ii`

Not stated (inventory: omitted): the remark opening §3.2 that the existence of the partial derivatives at a point does
not imply differentiability there (P1:3739); the Remark after Theorem 3.1 that the theorem also holds for
continuous open mappings (P1:3819, not cited later); the remark that `J = μ′_f` for sufficiently regular homeomorphisms
(P1:3827, subsumed by Lemma 3.2); the step towards Lemma 3.4 that `f⁻¹` is absolutely continuous in the compact subsets
of `G′` if and only if `f` maps no set of positive measure onto a null set (P1:3871, used only to derive Lemma 3.4).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (toExt closedRect)

/-! ## §3.1 Existence of partial derivatives -/

/-- **Unlabelled** (Ch. III §3.1, P1:3709, quoted from Saks). Let `f` be a complex-valued finite continuous function
in a domain `G` of the finite plane. The set of the points of `G` at which `f_x` exists and is finite is a Borel set,
and `f_x` is a Borel function in this set; the same holds for `f_y`.
Modelling: the book states this for the points where `f_x` and `f_y` both exist; its proof of Lemma 3.1 (P1:3723)
uses it for `f_x` alone, which is stated here (the joint statement follows by intersection). "Borel function in `S`"
is the measurability of the restriction to the subtype `S`, whose σ-algebra is the trace of the Borel sets
(footnote 33). -/
theorem partials_borel {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : ContinuousOn f G) :
    MeasurableSet {z ∈ G | DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0} ∧
      Measurable ({z ∈ G | DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0}.domRestrict
        (LiZhongQC.partialX f)) ∧
    MeasurableSet {z ∈ G | DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0} ∧
      Measurable ({z ∈ G | DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0}.domRestrict
        (LiZhongQC.partialY f)) := by
  sorry

/-- **Definition** (bounded variation on lines, Ch. III §3.1). A function `f`, continuous in `G`, is of bounded
variation on lines in `G`: in every rectangle `R = {x + iy | a < x < b, c < y < d}` with `R̄ ⊂ G`, `f` is of bounded
variation as a function of `x` on almost all horizontal segments `I_y` and as a function of `y` on almost all
vertical segments `I_x` of `R`.
Modelling: the shape of the project's `LiZhongQC.IsACL` (absolute continuity on lines, the companion notion of the
book), with bounded variation in place of absolute continuity. The closed segments of `R̄` are used, which
footnote 36 allows; for a function continuous on `R̄` the variation on a closed segment equals that on the open
one. -/
def IsBVL (f : ℂ → ℂ) (G : Set ℂ) : Prop :=
  ContinuousOn f G ∧ ∀ a b c d : ℝ, a < b → c < d → closedRect a b c d ⊆ G →
    (∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
        BoundedVariationOn (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (Icc c d)) ∧
      ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
        BoundedVariationOn (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (Icc a b)

/-- **Lemma 3.1** (Ch. III §3.1). A function `f` of bounded variation on lines in `G` possesses finite partial
derivatives almost everywhere in `G`.
Modelling: `G` is a domain of the finite plane (the setting of §3.1, P1:3709). -/
theorem lemma3_3_1 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : IsBVL f G) :
    ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 := by
  sorry

/-- **Unlabelled** (Ch. III §3.1, P1:3717; the bridge in the later applications of Lemma 3.1 to ACL mappings,
P1:5025, 5105, 5225, 5421, 5673, 5769). Since absolute continuity on a segment implies bounded variation, `f` is of
bounded variation on lines in `G` if it is absolutely continuous on lines in `G`. -/
theorem isBVL_of_isACL {G : Set ℂ} {f : ℂ → ℂ} (hf : LiZhongQC.IsACL f G) : IsBVL f G := by
  sorry

/-! ## §3.3 Areal derivative and Jacobian of a homeomorphism -/

/-- **Definition** (Jacobian, Ch. III §3.3). At a point where `f = u + iv` has finite partial derivatives, the
Jacobian of `f` is `J = (i/2)(f_x f̄_y − f̄_x f_y) = u_x v_y − u_y v_x` (`= |f_z|² − |f_{z̄}|²`).
Modelling: defined from the partial derivatives `LiZhongQC.partialX f`, `LiZhongQC.partialY f`, as in the book
(leader decision D7). Where a partial derivative does not exist its junk value `0` enters; every statement uses `J`
only at points where both partial derivatives exist (almost everywhere by hypothesis, or at a point of
differentiability). At points of real differentiability it equals the project's `LiZhongQC.jacobian`. -/
def partialJacobian (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (LiZhongQC.partialX f z).re * (LiZhongQC.partialY f z).im -
    (LiZhongQC.partialY f z).re * (LiZhongQC.partialX f z).im

/-- **Lemma 3.2** (Ch. III §3.3). Let the (sense-preserving) homeomorphism `f : G → G′` of domains of the finite
plane be differentiable at a point `z₀ ∈ G`. Then `f` has a finite areal derivative at `z₀` and `μ′_f(z₀) = J(z₀)`.
Modelling: the areal derivative is the limit of `m(f(Q))/m(Q)` over the closed squares `Q ∋ z₀` (the derivative
`HasSetFnDerivAt` of the set function `μ_f` of §2.4, which asserts its existence; the book's proof takes all closed
squares containing `z₀`). The value `ofReal J(z₀)` is finite; `μ′_f(z₀) = J(z₀)` includes `J(z₀) ≥ 0`, which is
stated as the first conjunct so that `ofReal` is faithful. -/
theorem lemma3_3_2 {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ G) (hd : DifferentiableAt ℝ f z₀) :
    0 ≤ partialJacobian f z₀ ∧
      HasSetFnDerivAt (homeoSetFn volume f G) G z₀ (ENNReal.ofReal (partialJacobian f z₀)) := by
  sorry

/-! ## §3.4 Integration of the Jacobian -/

/-- **Unlabelled** (Ch. III §3.4, P1:3855; footnote 35). If the (sense-preserving) homeomorphism `f : G → G′` has
finite partial derivatives almost everywhere in `G`, then `J(z) = μ′_f(z)` for almost all `z ∈ G`.
Modelling: at almost every `z` the areal derivative exists (`HasSetFnDerivAt`) and equals `ofReal J(z)` with
`J(z) ≥ 0`; the last conjunct restates this for `arealDeriv`, whose junk value is thereby not relied on. -/
theorem arealDeriv_eq_jacobian_ae {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G')
    {f : ℂ → ℂ} (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    ∀ᵐ z ∂(volume.restrict G), 0 ≤ partialJacobian f z ∧
      HasSetFnDerivAt (homeoSetFn volume f G) G z (ENNReal.ofReal (partialJacobian f z)) ∧
      arealDeriv f G z = ENNReal.ofReal (partialJacobian f z) := by
  sorry

/-- **Lemma 3.3** (Ch. III §3.4), the inequality. If the (sense-preserving) homeomorphism `f : G → G′` possesses
finite partial derivatives almost everywhere in `G`, then `∬_B J dσ ≤ m(f(B))` for every Borel set `B ⊂ G`.
Modelling: the first conjunct records `J ≥ 0` almost everywhere in `G` (by Lemma 3.2 and Theorem 3.1), so that the
lower integral of `ofReal J` is the book's integral of `J`. -/
theorem lemma3_3_3_i {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    (∀ᵐ z ∂(volume.restrict G), 0 ≤ partialJacobian f z) ∧
      ∀ B : Set ℂ, MeasurableSet B → B ⊆ G → ∫⁻ z in B, ENNReal.ofReal (partialJacobian f z) ≤ volume (f '' B) := by
  sorry

/-- **Lemma 3.3** (Ch. III §3.4), the case of equality. Under the hypotheses of `lemma3_3_3_i`, equality
`∬_B J dσ = m(f(B))` holds for every Borel set `B ⊂ G` if and only if `f` is locally absolutely continuous in `G`.
Modelling: `J ≥ 0` almost everywhere by `lemma3_3_3_i`, so `ofReal J` changes nothing. -/
theorem lemma3_3_3_ii {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    (∀ B : Set ℂ, MeasurableSet B → B ⊆ G → ∫⁻ z in B, ENNReal.ofReal (partialJacobian f z) = volume (f '' B)) ↔
      IsLocAbsContHomeo volume volume f G := by
  sorry

/-- **Lemma 3.3** (Ch. III §3.4), measurable sets. If, under the hypotheses of `lemma3_3_3_i`, `f` is locally
absolutely continuous in `G`, then `∬_A J dσ = m(f(A))` even for every measurable set `A ⊂ G`.
Modelling: as in `lemma3_3_3_ii`. -/
theorem lemma3_3_3_iii {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G')
    {f : ℂ → ℂ} (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0)
    (hac : IsLocAbsContHomeo volume volume f G) :
    ∀ A ⊆ G, NullMeasurableSet A volume → ∫⁻ z in A, ENNReal.ofReal (partialJacobian f z) = volume (f '' A) := by
  sorry

/-- **Lemma 3.4** (Ch. III §3.4). Let the (sense-preserving) homeomorphism `f : G → G′` be locally absolutely
continuous in `G` and have finite partial derivatives almost everywhere in `G`. The Jacobian `J` of `f` is positive
almost everywhere in `G` if and only if the inverse `f⁻¹ : G′ → G` is locally absolutely continuous in `G′`.
Modelling: `f⁻¹` is `Function.invFunOn f G`. -/
theorem lemma3_3_4 {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hac : IsLocAbsContHomeo volume volume f G)
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0) :
    (∀ᵐ z ∂(volume.restrict G), 0 < partialJacobian f z) ↔
      IsLocAbsContHomeo volume volume (Function.invFunOn f G) G' := by
  sorry

/-- **Lemma 3.5** (Ch. III §3.4), `g` non-negative. Let the (sense-preserving) homeomorphism `f : G → G′` and its
inverse `f⁻¹` be locally absolutely continuous in their respective domains, and let `f` have finite partial
derivatives almost everywhere in `G`. Let `g` be a non-negative measurable function in `G′`. Then
`∬_A g(f(z)) J(z) dσ = ∬_{f(A)} g dσ` for every measurable set `A ⊂ G`.
Modelling: `g` is `ℝ≥0∞`-valued (a non-negative function of the book, possibly infinite) and measurable for the area
measure on `G′`; `J ≥ 0` almost everywhere by `lemma3_3_3_i`, so `ofReal J` changes nothing, and `∞ · 0 = 0` is the
book's convention (§1.4). -/
theorem lemma3_3_5_i {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hac : IsLocAbsContHomeo volume volume f G) (hac' : IsLocAbsContHomeo volume volume (Function.invFunOn f G) G')
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0)
    {g : ℂ → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict G')) {A : Set ℂ} (hAG : A ⊆ G)
    (hA : NullMeasurableSet A volume) :
    ∫⁻ z in A, g (f z) * ENNReal.ofReal (partialJacobian f z) = ∫⁻ w in f '' A, g w := by
  sorry

/-- **Lemma 3.5** (Ch. III §3.4), `g` integrable. Let `f : G → G′` be as in `lemma3_3_5_i` and let `g` be a
complex-valued function integrable in `G′`. Then `∬_A g(f(z)) J(z) dσ = ∬_{f(A)} g dσ` for every measurable set
`A ⊂ G`.
Modelling: `g` is finite `ℂ`-valued (D2); the integrals are Bochner integrals, and the integrability over `A` of the
left integrand (a finite integral in the book) is stated. -/
theorem lemma3_3_5_ii {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hsp : IsSensePreservingOn (OnePoint.map f) (toExt G))
    (hac : IsLocAbsContHomeo volume volume f G) (hac' : IsLocAbsContHomeo volume volume (Function.invFunOn f G) G')
    (hpart : ∀ᵐ z ∂(volume.restrict G), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0)
    {g : ℂ → ℂ} (hg : IntegrableOn g G') {A : Set ℂ} (hAG : A ⊆ G) (hA : NullMeasurableSet A volume) :
    IntegrableOn (fun z => g (f z) * (partialJacobian f z : ℂ)) A ∧
      ∫ z in A, g (f z) * (partialJacobian f z : ℂ) = ∫ w in f '' A, g w := by
  sorry

end LehtoVirtanen1973
