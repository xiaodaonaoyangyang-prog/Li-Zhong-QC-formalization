import References.LehtoVirtanen1973.Ch03.S03_Differentiability
import References.LehtoVirtanen1973.Ch03.S04_ModuleArcFamilies
import References.LehtoVirtanen1973.Ch03.S05_Approximation

/-!
# Lehto–Virtanen, Chapter III §6: Functions with `L^p`-derivatives

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §6
(pp. 143–154; `full.md` P1:4325–4732).

Conventions (see also §2–§5). `G` always denotes a domain of the finite plane (P1:4329): `IsOpen G ∧ IsConnected G`
for `G : Set ℂ`. The partial derivatives `f_x`, `f_y` are `LiZhongQC.partialX f`, `LiZhongQC.partialY f` (the
derivatives along horizontal and vertical lines, with the junk value `0` where they do not exist); for the functions
of this section they exist almost everywhere (Lemma 3.1) and enter only through `L^p` conditions, integrals and
almost-everywhere equalities, so the junk values on a null set are never seen. `f_z = (f_x − i f_y)/2` and
`f_{z̄} = (f_x + i f_y)/2` are `LiZhongQC.genDz`, `LiZhongQC.genDzbar` of the two partials. The exponents of `L^p`
are real, `1 ≤ p < ∞` (harmonization rule H6), and "`g` belongs to `L^p` in every compact subset of `G`" is
`MemLp g (ENNReal.ofReal p) (volume.restrict K)` for every compact `K ⊂ G`. `C¹` in `G` is `ContDiffOn ℝ 1 · G`;
`C_0^∞` (§5.4) is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ∧ HasCompactSupport` (a bare `⊤` would mean analyticity).
"A Jordan domain `D`, `D̄ ⊂ G`" is `IsJordanDomainExt (toExt D) ∧ closure (toExt D) ⊆ toExt G`, the closure being
taken in `ℂ̄`, so that `D` is bounded, as in the book; its boundary is rectifiable if it is a rectifiable Jordan
curve in the sense of §2.6 (`IsRectifiableJordanCurve`). The positively oriented boundary `∂D` (I.1.4) is given by
the positively oriented parametrizations of Ch. I (`IsPositiveBoundaryParam`), and `∫_{∂D} f dg` (§2.10–2.11) is
the classical Stieltjes integral over one period of such a parametrization. A homeomorphism `w` of `G` onto `G′` is
`LiZhongQC.IsHomeomorphOnto w G G'`; arcs of the finite plane are Jordan arcs of Ch. I lying in `ℂ`.

* Definition (function with `L^p`-derivatives, §6.1) — `HasLpDerivatives`
* Unlabelled (§6.1, P1:4337; used tacitly at P1:5849 and P2:1747): a function with `L^p`-derivatives has
  `L^q`-derivatives for `1 ≤ q ≤ p` — `hasLpDerivatives_mono_exponent`
* Definition (absolutely continuous in the sense of Tonelli, §6.1) — omitted: a second name for the functions with
  L¹-derivatives, not used again in the book
* Definition (the Stieltjes integral `∫_{∂D} f dg` over the positively oriented boundary of a Jordan domain, §6.2,
  from §2.6 and §2.11) — `HasBoundaryIntegral`, `boundaryIntegral`
* Formula (2.11) of §2.11 for Jordan curves (§2.6, P1:3605; used P1:4633), for orientation-preserving and
  orientation-reversing homeomorphisms — `eq3_2_11_curve`, `eq3_2_11_curve_reversing`
* Lemma 6.1 (§6.2), with its condition (6.1) — `IsGreenRectanglePair`, `lemma3_6_1`
* Lemma 6.2 (§6.3) — `lemma3_6_2_i`, `lemma3_6_2_ii`, `lemma3_6_2_iii`
* Lemma 6.3 (§6.4) — `lemma3_6_3`
* Green's formula (§6.5, generalized Green's formula; footnote 38) — `green_formula_i`, `green_formula_ii`
* Formula (6.17) (§6.5) — `eq3_6_17`
* Theorem 6.1 (§6.6) — `thm3_6_1`
* Lemma 6.4 (§6.7) — `lemma3_6_4`
* Theorem 6.2 (§6.8, Väisälä) — `thm3_6_2`

Not stated (inventory: omitted): the classical Green
formula for `C²` functions assumed in the proof of Green's formula (P1:4553, Apostol); footnote 38 ("the requirement `g
∈ C²` can clearly be replaced by a much weaker one"); the remark after Lemma 6.4 on continuously differentiable `w`,
`w⁻¹` (P1:4689). The numbered formulas (6.2)–(6.10), (6.12)–(6.16), (6.18) and (6.20)–(6.25) are steps of proofs.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane toExt IsACL partialX partialY closedRect openRect genDz genDzbar IsHomeomorphOnto)
open References (IsJordanDomainExt)

/-! ## §6.1 Definition of a function with `L^p`-derivatives -/

/-- **Definition** (function with `L^p`-derivatives, Ch. III §6.1). The finite complex-valued function `f` defined
in the domain `G` has `L^p`-derivatives, `p ≥ 1`: 1. `f` is absolutely continuous on lines in `G` (§3.1); 2. the
partial derivatives `f_x`, `f_y` belong to `L^p` in every compact subset of `G`.
Modelling: ACL is `LiZhongQC.IsACL` (continuity included, as in the book); the exponent is real, and the statements
assume `1 ≤ p` (the book's range) and that `G` is a domain. -/
def HasLpDerivatives (f : ℂ → ℂ) (G : Set ℂ) (p : ℝ) : Prop :=
  IsACL f G ∧ ∀ K ⊆ G, IsCompact K →
    MemLp (partialX f) (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp (partialY f) (ENNReal.ofReal p) (volume.restrict K)

/-- **Unlabelled** (Ch. III §6.1, P1:4337; used tacitly at P1:5849 and P2:1747). It follows from Hölder's inequality
that a function with `L^p`-derivatives also has `L^q`-derivatives for `q ≤ p`.
Modelling: `1 ≤ q` (the book's range of `L^q`); `G` a domain. -/
theorem hasLpDerivatives_mono_exponent {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} {p q : ℝ}
    (hf : HasLpDerivatives f G p) (hq : 1 ≤ q) (hqp : q ≤ p) : HasLpDerivatives f G q := by
  sorry

/-! ## §6.2 Integral transformations for functions with `L^p`-derivatives -/

/-- **Definition** (`∫_{∂D} f dg`, Ch. III §6.2, from §2.6 and §2.11). The Stieltjes integral of `f` with respect to
`g` over the boundary `∂D` of the Jordan domain `D` of the finite plane, positively oriented with respect to `D`
(I.1.4), exists and equals `L`: `D` has a positively oriented boundary parametrization `γ` in the finite plane, and
for every such `γ` the classical Stieltjes integral `∫_0^1 f(γ(t)) dg(γ(t))` over one period exists and equals `L`.
Modelling: the book splits `∂D` into two arcs and adds the integrals (2.10) over them (P1:3605); for continuous `f`
and `g` of bounded variation on `∂D` this is the integral over one period of any positively oriented
parametrization (additivity and invariance under monotone reparametrization), so the value does not depend on the
parametrization, which is what the universal quantifier records. -/
def HasBoundaryIntegral (D : Set ℂ) (f g : ℂ → ℂ) (L : ℂ) : Prop :=
  (∃ γ : ℝ → ℂ, IsPositiveBoundaryParam (toExt D) (fun t => (γ t : ExtPlane))) ∧
    ∀ γ : ℝ → ℂ, IsPositiveBoundaryParam (toExt D) (fun t => (γ t : ExtPlane)) →
      HasRiemannStieltjesIntegral (f ∘ γ) (g ∘ γ) 0 1 L

open Classical in
/-- The integral `∫_{∂D} f dg` (Ch. III §6.2): the value `L` of `HasBoundaryIntegral`, which is unique when it
exists. Junk value `0` when it does not exist (outside the book's domain: `D` a bounded Jordan domain, `f`
continuous and `g` continuous of bounded variation on `∂D`); statements assert existence through
`HasBoundaryIntegral`. -/
def boundaryIntegral (D : Set ℂ) (f g : ℂ → ℂ) : ℂ :=
  if h : ∃ L, HasBoundaryIntegral D f g L then h.choose else 0

/-- **Formula (2.11)** for Jordan curves (Ch. III §2.11 with §2.6, P1:3605: "the same is true if `C` is a Jordan
curve; we only need to divide `C` into two subarcs"; used at P1:4633). Let `D`, `D′` be Jordan domains of the finite
plane with rectifiable boundaries and `w` a homeomorphism of `∂D` onto `∂D′` which carries the positive orientation
of `∂D` onto that of `∂D′`. Then, for continuous functions `f`, `g` on `∂D`, `g` of bounded variation,
`∫_{∂D} f dg = ∫_{∂D′} (f ∘ w⁻¹) d(g ∘ w⁻¹)`.
Modelling: `D` and `D′` are bounded (a rectifiable Jordan curve lies in the finite plane); the orientation
condition is that `w ∘ γ` is a positively oriented boundary parametrization of `D′` for every such `γ` of `D`;
`w⁻¹` is `invFunOn w (frontier D)`; the existence of both integrals and their equality are stated together. -/
theorem eq3_2_11_curve {D D' : Set ℂ} (hD : IsJordanDomainExt (toExt D)) (hD' : IsJordanDomainExt (toExt D'))
    (hDr : IsRectifiableJordanCurve (frontier D)) (hD'r : IsRectifiableJordanCurve (frontier D')) {w : ℂ → ℂ}
    (hw : IsHomeomorphOnto w (frontier D) (frontier D'))
    (hor : ∀ γ : ℝ → ℂ, IsPositiveBoundaryParam (toExt D) (fun t => (γ t : ExtPlane)) →
      IsPositiveBoundaryParam (toExt D') (fun t => (w (γ t) : ExtPlane)))
    {f g : ℂ → ℂ} (hf : ContinuousOn f (frontier D)) (hg : ContinuousOn g (frontier D))
    (hgbv : variationOnCurve g (frontier D) < ⊤) :
    ∃ L : ℂ, HasBoundaryIntegral D f g L ∧
      HasBoundaryIntegral D' (f ∘ Function.invFunOn w (frontier D)) (g ∘ Function.invFunOn w (frontier D)) L := by
  sorry

/-- **Formula (2.11)** for Jordan curves, orientation-reversing case (Ch. III §2.11 with §2.6, P1:3605). Let `D`,
`D′` and `w` be as in `eq3_2_11_curve`, except that `w` carries the positive orientation of `∂D` onto the negative
orientation of `∂D′`. Then `∫_{∂D} f dg = −∫_{∂D′} (f ∘ w⁻¹) d(g ∘ w⁻¹)` (the book's (2.11) with the orientation
induced by `w`, which is the reverse of the positive one).
Modelling: the orientation condition is that `t ↦ w(γ(−t))` is a positively oriented boundary parametrization of
`D′` for every positively oriented `γ` of `D`; otherwise as in `eq3_2_11_curve`. -/
theorem eq3_2_11_curve_reversing {D D' : Set ℂ} (hD : IsJordanDomainExt (toExt D))
    (hD' : IsJordanDomainExt (toExt D')) (hDr : IsRectifiableJordanCurve (frontier D))
    (hD'r : IsRectifiableJordanCurve (frontier D')) {w : ℂ → ℂ} (hw : IsHomeomorphOnto w (frontier D) (frontier D'))
    (hrev : ∀ γ : ℝ → ℂ, IsPositiveBoundaryParam (toExt D) (fun t => (γ t : ExtPlane)) →
      IsPositiveBoundaryParam (toExt D') (fun t => (w (γ (-t)) : ExtPlane)))
    {f g : ℂ → ℂ} (hf : ContinuousOn f (frontier D)) (hg : ContinuousOn g (frontier D))
    (hgbv : variationOnCurve g (frontier D) < ⊤) :
    ∃ L : ℂ, HasBoundaryIntegral D f g L ∧
      HasBoundaryIntegral D' (f ∘ Function.invFunOn w (frontier D)) (g ∘ Function.invFunOn w (frontier D)) (-L) := by
  sorry

/-- The condition of Lemma 6.1 (Ch. III §6.2): the functions `g` and `h` belong to `L^p` in every compact subset of
`G`, and for every rectangle `R = {x + iy | a < x < b, c < y < d}` with sides parallel to the axes and `R̄ ⊂ G`,
`∫_{∂R} f dx = −∬_R g dσ` and `∫_{∂R} f dy = ∬_R h dσ` (6.1).
Modelling: for the continuous `f` of Lemma 6.1 the boundary integrals over the positively oriented `∂R` are the
ordinary integrals `∫_{∂R} f dx = ∫_a^b (f(x + ic) − f(x + id)) dx` (as in the book's proof, P1:4352) and
`∫_{∂R} f dy = ∫_c^d (f(b + iy) − f(a + iy)) dy`; the double integrals exist since `g`, `h` are integrable over the
compact `R̄`. -/
def IsGreenRectanglePair (f g h : ℂ → ℂ) (G : Set ℂ) (p : ℝ) : Prop :=
  (∀ K ⊆ G, IsCompact K → MemLp g (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp h (ENNReal.ofReal p) (volume.restrict K)) ∧
    ∀ a b c d : ℝ, a < b → c < d → closedRect a b c d ⊆ G →
      (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) = -∫ z in openRect a b c d, g z ∧
        (∫ y in c..d, f (b + y * I)) - (∫ y in c..d, f (a + y * I)) = ∫ z in openRect a b c d, h z

/-- **Lemma 6.1** (Ch. III §6.2). A function `f` which is finite and continuous in `G` possesses `L^p`-derivatives
in `G` if and only if there exist two functions `g` and `h` belonging to `L^p` in every compact subset of `G` such
that (6.1) holds for every rectangle `R`, `R̄ ⊂ G`, with sides parallel to the axes. In this case `f_x = h`,
`f_y = g` almost everywhere in `G`.
Modelling: the condition is `IsGreenRectanglePair f g h G p`; `1 ≤ p`. -/
theorem lemma3_6_1 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : ContinuousOn f G) {p : ℝ}
    (hp : 1 ≤ p) :
    (HasLpDerivatives f G p ↔ ∃ g h : ℂ → ℂ, IsGreenRectanglePair f g h G p) ∧
      ∀ g h : ℂ → ℂ, IsGreenRectanglePair f g h G p →
        partialX f =ᵐ[volume.restrict G] h ∧ partialY f =ᵐ[volume.restrict G] g := by
  sorry

/-! ## §6.3 Approximation of functions with `L^p`-derivatives -/

/-- **Lemma 6.2**, first assertion (Ch. III §6.3). Let `f`, `g`, `h` be three functions defined in the domain `G`,
`g` and `h` belonging to `L^p` in every compact subset of `G`, and let `fₙ` be continuously differentiable functions
in `G` such that for every compact subset `F` of `G`: 1. `fₙ − f → 0` uniformly in `F`; 2.
`∬_F |∂fₙ/∂x − h|^p dσ → 0` and `∬_F |∂fₙ/∂y − g|^p dσ → 0`. Then `f` has `L^p`-derivatives in `G` and `f_x = h`,
`f_y = g` almost everywhere in `G`.
Modelling: `1 ≤ p`; the integrals are `∫⁻` of `‖·‖ₑ ^ p`. -/
theorem lemma3_6_2_i {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {p : ℝ} (hp : 1 ≤ p) {f g h : ℂ → ℂ}
    (hgh : ∀ K ⊆ G, IsCompact K → MemLp g (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp h (ENNReal.ofReal p) (volume.restrict K))
    {fn : ℕ → ℂ → ℂ} (hfn : ∀ n, ContDiffOn ℝ 1 (fn n) G)
    (h₁ : ∀ F ⊆ G, IsCompact F → TendstoUniformlyOn fn f atTop F)
    (h₂ : ∀ F ⊆ G, IsCompact F →
      Tendsto (fun n => ∫⁻ z in F, ‖partialX (fn n) z - h z‖ₑ ^ p) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫⁻ z in F, ‖partialY (fn n) z - g z‖ₑ ^ p) atTop (𝓝 0)) :
    HasLpDerivatives f G p ∧ partialX f =ᵐ[volume.restrict G] h ∧ partialY f =ᵐ[volume.restrict G] g := by
  sorry

/-- **Lemma 6.2**, converse (Ch. III §6.3). If `f` has `L^p`-derivatives in the domain `G`, there exists a sequence
of functions `fₙ ∈ C_0^∞` satisfying conditions 1 and 2 of `lemma3_6_2_i` with `h = f_x`, `g = f_y`, for every
compact subset `F` of `G`.
Modelling: `1 ≤ p`; `C_0^∞` as in the module docstring. -/
theorem lemma3_6_2_ii {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {p : ℝ} (hp : 1 ≤ p) {f : ℂ → ℂ}
    (hf : HasLpDerivatives f G p) :
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) ∧ HasCompactSupport (fn n)) ∧
      ∀ F ⊆ G, IsCompact F → TendstoUniformlyOn fn f atTop F ∧
        Tendsto (fun n => ∫⁻ z in F, ‖partialX (fn n) z - partialX f z‖ₑ ^ p) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫⁻ z in F, ‖partialY (fn n) z - partialY f z‖ₑ ^ p) atTop (𝓝 0) := by
  sorry

/-- **Lemma 6.2**, compact support (Ch. III §6.3). If `f` has `L^p`-derivatives in the domain `G` and the support of
`f` is a compact subset of `G`, then the functions `fₙ ∈ C_0^∞` of `lemma3_6_2_ii` can be chosen so that the
conditions 1 and 2 hold with `F` replaced by `G`.
Modelling: `f` is defined in `G` only, so its support is that of `f|_G`: `f` vanishes in `G` outside a compact set
`K ⊂ G`; `1 ≤ p`. -/
theorem lemma3_6_2_iii {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {p : ℝ} (hp : 1 ≤ p) {f : ℂ → ℂ}
    (hf : HasLpDerivatives f G p) (hsupp : ∃ K ⊆ G, IsCompact K ∧ ∀ z ∈ G \ K, f z = 0) :
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) ∧ HasCompactSupport (fn n)) ∧
      TendstoUniformlyOn fn f atTop G ∧
      Tendsto (fun n => ∫⁻ z in G, ‖partialX (fn n) z - partialX f z‖ₑ ^ p) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ z in G, ‖partialY (fn n) z - partialY f z‖ₑ ^ p) atTop (𝓝 0) := by
  sorry

/-! ## §6.4 Approximation in the finite plane -/

/-- **Lemma 6.3** (Ch. III §6.4). Let `f` be absolutely continuous on lines in the finite plane `Ω` and suppose
that its partial derivatives belong to `L²(Ω)`. Then there exists a sequence of functions `fₙ` of the class `C_0^∞`
such that 1. `fₙ(z) → f(z)` uniformly in every bounded set; 2. `∬_Ω |f_x − (fₙ)_x|² dσ → 0` and
`∬_Ω |f_y − (fₙ)_y|² dσ → 0`. -/
theorem lemma3_6_3 {f : ℂ → ℂ} (hf : IsACL f univ) (hfx : MemLp (partialX f) 2 volume)
    (hfy : MemLp (partialY f) 2 volume) :
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) ∧ HasCompactSupport (fn n)) ∧
      (∀ S : Set ℂ, Bornology.IsBounded S → TendstoUniformlyOn fn f atTop S) ∧
      Tendsto (fun n => ∫⁻ z, ‖partialX f z - partialX (fn n) z‖ₑ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ z, ‖partialY f z - partialY (fn n) z‖ₑ ^ 2) atTop (𝓝 0) := by
  sorry

/-! ## §6.5 Generalized Green's formula -/

/-- **Green's formula** (Ch. III §6.5), first case. Let `f` and `g` have `L^p`- and `L^q`-derivatives, respectively,
in the domain `G`, where `1/p + 1/q = 1`. If `D`, `D̄ ⊂ G`, is a Jordan domain with a rectifiable boundary on which
`g` is of bounded variation, then `∫_{∂D} f dg = ∬_D (f_x g_y − f_y g_x) dσ` (6.11).
Modelling: `p` and `q` are conjugate real exponents, so `1 < p, q < ∞` (the book's `L^q` requires `q < ∞`, and its
proof treats `p > 1` only, P1:4573); "`g` of bounded variation on `∂D`" is `variationOnCurve g (Fr D) < ∞` (§2.10);
the integrand on the right is integrable over `D` by Hölder's inequality (`D̄` is a compact subset of `G`), so the
Bochner integral is the book's; the conclusion asserts that `∫_{∂D} f dg` exists. -/
theorem green_formula_i {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : ℂ → ℂ} (hf : HasLpDerivatives f G p) (hg : HasLpDerivatives g G q) {D : Set ℂ}
    (hD : IsJordanDomainExt (toExt D)) (hDG : closure (toExt D) ⊆ toExt G)
    (hDr : IsRectifiableJordanCurve (frontier D)) (hgbv : variationOnCurve g (frontier D) < ⊤) :
    HasBoundaryIntegral D f g (∫ z in D, (partialX f z * partialY g z - partialY f z * partialX g z)) := by
  sorry

/-- **Green's formula** (Ch. III §6.5), second case. The relation (6.11)
`∫_{∂D} f dg = ∬_D (f_x g_y − f_y g_x) dσ` holds for every Jordan domain `D`, `D̄ ⊂ G`, with a rectifiable boundary
if `f` has `L¹`-derivatives in the domain `G` and `g` belongs to the class `C²` in `G`.
Modelling: `g ∈ C²` in `G` is `ContDiffOn ℝ 2 g G`; it makes `g` of bounded variation on the rectifiable `∂D`, and
the integrand on the right is integrable over `D` (`g_x`, `g_y` are bounded on `D̄`); the conclusion asserts that
`∫_{∂D} f dg` exists. -/
theorem green_formula_ii {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f g : ℂ → ℂ} (hf : HasLpDerivatives f G 1)
    (hg : ContDiffOn ℝ 2 g G) {D : Set ℂ} (hD : IsJordanDomainExt (toExt D)) (hDG : closure (toExt D) ⊆ toExt G)
    (hDr : IsRectifiableJordanCurve (frontier D)) :
    HasBoundaryIntegral D f g (∫ z in D, (partialX f z * partialY g z - partialY f z * partialX g z)) := by
  sorry

/-- **Formula (6.17)** (Ch. III §6.5, Example). If `f` has `L¹`-derivatives in `G`, then
`∫_{∂D} f dz = 2i ∬_D f_{z̄} dσ` and `∫_{∂D} f dz̄ = −2i ∬_D f_z dσ` (6.17) for every Jordan domain `D`, `D̄ ⊂ G`, with
a rectifiable boundary (Green's formula with `g(z) = z` and `g(z) = z̄`).
[OCR?] The example is OCR'd as "`g(z) = 1/z`" (P1:4603, inline OCR, unverifiable against the print); (6.17)
requires `g(z) = z̄`.
Modelling: `f_z`, `f_{z̄}` are built from the partials (module docstring); they are integrable over `D`, so the
Bochner integrals are the book's; the conclusion asserts that the boundary integrals exist. -/
theorem eq3_6_17 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : HasLpDerivatives f G 1)
    {D : Set ℂ} (hD : IsJordanDomainExt (toExt D)) (hDG : closure (toExt D) ⊆ toExt G)
    (hDr : IsRectifiableJordanCurve (frontier D)) :
    HasBoundaryIntegral D f id (2 * I * ∫ z in D, genDzbar (partialX f) (partialY f) z) ∧
      HasBoundaryIntegral D f (fun z => conj z) (-2 * I * ∫ z in D, genDz (partialX f) (partialY f) z) := by
  sorry

/-! ## §6.6 Absolute continuity of homeomorphisms with `L²`-derivatives -/

/-- **Theorem 6.1** (Ch. III §6.6). A homeomorphism `w` of the domain `G`, having `L²`-derivatives in `G`, is locally
absolutely continuous in `G`.
Modelling: `w` is a homeomorphism of `G` onto `w(G)`; local absolute continuity is that of the set function `μ_w`
for the area measure (§2.2); no orientation hypothesis (the proof assumes sense-preservation "without loss of
generality", P1:4615). -/
theorem thm3_6_1 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {w : ℂ → ℂ} (hw : IsHomeomorphOnto w G (w '' G))
    (hL : HasLpDerivatives w G 2) : IsLocAbsContHomeo volume volume w G := by
  sorry

/-! ## §6.7 Composition of functions with `L^p`-derivatives -/

/-- **Lemma 6.4** (Ch. III §6.7). Let `w = u + iv : G → G′` and its inverse `w⁻¹ = x + iy` be homeomorphisms which
have `L^p`-derivatives with `p ≥ 2` in `G` and `G′`, and let `f` be a function with `L^q`-derivatives in `G′`, where
`1/p + 1/q = 1`. Then `f ∘ w` has `L¹`-derivatives in `G`, and the chain rule (6.19)
`(f ∘ w)_x = (f_u ∘ w) u_x + (f_v ∘ w) v_x`, `(f ∘ w)_y = (f_u ∘ w) u_y + (f_v ∘ w) v_y` holds almost everywhere
in `G`.
Modelling: `G′` is a domain; `w⁻¹` is `invFunOn w G`; `u_x = Re w_x`, `v_x = Im w_x` (similarly for `y`), and
`f_u`, `f_v` are the partials of `f` in the `w = u + iv`-plane evaluated at `w(z)`; their junk values on a null set
`N ⊂ G′` are not seen almost everywhere in `G`, `w⁻¹(N)` being null (`w⁻¹` is locally absolutely continuous by
Theorem 6.1). No orientation hypothesis, as printed. -/
theorem lemma3_6_4 {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {w : ℂ → ℂ}
    (hw : IsHomeomorphOnto w G G') {p q : ℝ} (hp : 2 ≤ p) (hpq : p.HolderConjugate q)
    (hwL : HasLpDerivatives w G p) (hwL' : HasLpDerivatives (Function.invFunOn w G) G' p) {f : ℂ → ℂ}
    (hf : HasLpDerivatives f G' q) :
    HasLpDerivatives (f ∘ w) G 1 ∧ ∀ᵐ z ∂(volume.restrict G),
      partialX (f ∘ w) z =
          partialX f (w z) * ((partialX w z).re : ℂ) + partialY f (w z) * ((partialX w z).im : ℂ) ∧
        partialY (f ∘ w) z =
          partialX f (w z) * ((partialY w z).re : ℂ) + partialY f (w z) * ((partialY w z).im : ℂ) := by
  sorry

/-! ## §6.8 Absolute continuity on arbitrary arcs -/

/-- **Theorem 6.2** (Ch. III §6.8, Väisälä). Let `f` be a function with `L²`-derivatives in `G`. Then `f` is
absolutely continuous on all arcs `C`, `C̄ ⊂ G`, with the exception of a family of module zero.
Modelling: the exceptional family consists of the Jordan arcs `C` of the finite plane with `C̄ ⊂ G` on which `f` is
not absolutely continuous as a function of the arc length (§2.10, `IsAbsContOnArc`); the arcs that are not locally
rectifiable belong to it, and they do not change the module (§4.3). The module is that of §4 (`arcFamilyModule`),
on the arcs regarded as subsets of `ℂ̄`. -/
theorem thm3_6_2 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : HasLpDerivatives f G 2) :
    arcFamilyModule (toExt '' {C : Set ℂ | IsJordanArc (toExt C) ∧ closure (toExt C) ⊆ toExt G ∧
      ¬ IsAbsContOnArc f C}) = 0 := by
  sorry

end LehtoVirtanen1973
