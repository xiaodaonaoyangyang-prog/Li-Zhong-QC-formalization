import LiZhongQC.Ch11.S36_Hamilton
import LiZhongExternal.Topology.InvarianceOfDomain

/-!
# Companions of the §23/§26 uniqueness statements for surfaces given as `ℍ/Γ` (`utm_`)

The book statements `thm23_1_cor`, `conformal_unique_extremal`, `lemma26_1`, `lemma26_2`, `thm26_2_uniqueness`,
`eq26_15_16` and `teichmullerMap_isExtremal` are stated for an abstract closed surface; their proofs need a Fuchsian
uniformization of the surface (`thm22_3_classification`, not yet formalized), so they remain unproved (user decision,
2026-09-26).  This module proves **companions** `<name>_of_uniformization`: the book statement, byte-identical, plus
only the uniformization data `{Γ} {p} (hp : IsUniformization Γ p)` of the surface that the proof uses.  Each book
statement follows from its companion and `thm22_3_classification` (the derivation is not formalized here).

**Installment 1** (s26t Stage C, coordinator 553e2d, 2026-09-26): `thm23_1_cor_of_uniformization` and
`conformal_unique_extremal_of_uniformization`.  The lift `F` of a biholomorphic `φ ≃ id` is Möbius, normalized by
Theorem 23.1 it commutes with `Γ₀`, its displacement is `Γ₀`-invariant hence bounded on the compact quotient, so it is
`±1` and `φ = id`.

**Installment 2** (2026-09-26): `lemma26_1_of_uniformization` (Lemma 26.1, in the FIX-1 form, for `S₀ = ℍ/Γ₀`): the
lifted differential `utm_liftQD`, lifts of horizontal arcs and of lengths to `ℍ`, the bounded displacement of the
`Γ₀`-commuting lift of `f ≃ id`, and `fx_arc_shortest` carried to `ℍ` by the Cayley map.

**Installments 3-4** (2026-09-26): `lemma26_2_of_uniformization` (from Lemma 26.1 on `ℍ/Γ₀` and the S26 book
averaging `lemma26_2_averaging`), and, for a target surface `S₁ = ℍ/Γ₁`, `thm26_2_uniqueness_of_uniformization`,
`eq26_15_16_of_uniformization`, `teichmullerMap_isExtremal_of_uniformization` (the inequality (26.11)-(26.14)
and the equality analysis (26.15)-(26.16), with `thm23_1_cor_of_uniformization` on `S₁`).

**Installment 5** (2026-09-26): `lemma27_3_dilatation_bound_of_uniformization` (§27, for a marked surface
`m = (X, f)` with `X = ℍ/Γ₁`), from `thm26_2_uniqueness_of_uniformization` on the deformation surface.

**Installment 6** (2026-09-26): Teichmüller's existence theorem (§27.2) for `S₀ = ℍ/Γ₀`, as the companions
`lemma27_1_injective_of_uniformization` ((27.15)), `teichSpace_deformation_bijection_of_uniformization` (`Φ` is a
bijection) and `thm27_2_existence_qc_of_uniformization` (Theorem 27.2 in the quasiconformal variant, for
`S = ℍ/Γ₁`).  Hamilton's route (§36): the lifted Beltrami coefficient of a marked surface has an extremal
representative, `0` or `k φ̄/|φ|` (`exists_extremal_mod_boundary`, `thm36_2_finite_type`; `dim Q(S₀) < ∞` by Montel
and the descent of automorphic forms); the classes are identified through the uniformization transport of S27
(`s27u_uniformization_transport`) and Theorem 27.1; uniqueness is Theorem 26.2 on the inverse Teichmüller map.

**Installment 7** (2026-09-27): the §29/§30 companions (Part 6) `teichDistance_eq_of_eq_zero_of_uniformization`,
`hurwitz_finite_of_uniformization`, `modAction_properly_discontinuous_of_uniformization`, `thm30_3_of_uniformization`
and `thm30_4_hausdorff_of_uniformization`, from the key lemma `utm_y_kl` (`K₀`-q.c. maps between `ℍ/Γ` surfaces fall
into finitely many homotopy classes: normal families of normalized lifts, finitely many deck actions on generators)
and the S30 helpers of `eq30_13_eventually_equal` (`s30b_`).

**Installment 8** (2026-09-27): the §32 companion `eq32_2_symmetric_lift_of_uniformization` (Part 7): the lifted
Teichmüller map commutes with the covering transformations `h₀`, `h₁` of the double covers, for a target `X₁' = ℍ/Γ₁`,
by Theorem 26.2 (uniqueness companion) applied to `h₀ ≫ ftil₀ ≫ h₁⁻¹`.

**Book statements moved here** (leader decision, 2026-10-12; docstring and statement unchanged): §27.2
`teichSpace_deformation_bijection` (from Ch07/S27) and (32.2) `eq32_2_symmetric_lift` (from Ch09/S32), each proved
from its companion and the uniformization theorem `s22hg_exists_fuchsian_uniformization` (S22).

**Book statement moved here** (leader decision, 2026-10-13; docstring and statement unchanged): Theorem 27.2
`thm27_2_existence` (from Ch07/S27), proved from its quasiconformal companion, the uniformization theorem
`s22hg_exists_fuchsian_uniformization` (S22) and §24.2 `exists_qc_in_homotopy_class` (S24).

**Book statement moved here** (leader decision, 2026-10-13; docstring and statement unchanged): Theorem 26.1
`thm26_1_extremal_exists` (from Ch07/S26), proved from Theorem 27.2 (`thm27_2_existence`) on `ULift` copies of the
two surfaces in a common universe (`utm_ul_`), so that `eq26_2_limit_of_bounded_dilatation` is not used.
**(26.2) bounded-dilatation limits:** `eq26_2_limit_of_bounded_dilatation` (from Ch07/S26),
with paired general-K lifts, finite-deck descent and a liminf bound for the same limit
(`eq262_`); the original independent source/target universes are preserved.

-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section

namespace LiZhongQC

universe u v

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-! Parts 1–4 (the §23/§26 uniqueness companions for `ℍ/Γ` and their helpers) and the E2 pieces [S7a], [S7b],
`utm_x_tcoeff`, S3 at a point and the inverse trick are in `LiZhongQC.Lemmas.UniformizedUniqueness`. -/

/-- **Companion of `lemma27_3_dilatation_bound`** for a marked surface `m = (X, f)` with `X = ℍ/Γ₁`: if `m` is the
point of `T(S₀)` of the Teichmüller deformation `(q, k)`, then `(1 + k)/(1 - k) ≤ K[f]`.  The deformation map
`e : S₀ → S_{q,k}` is homotopic to `c ∘ f` (`c : X → S_{q,k}` the conformal map of the equivalence), so
`thm26_2_uniqueness_of_uniformization`, with the uniformization `c ∘ p₁` of `S_{q,k}`, gives
`(1 + k)/(1 - k) ≤ K[c ∘ f] ≤ K[f]`.

*Derivation note:* the book statement `lemma27_3_dilatation_bound` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of `m.X`). -/
theorem lemma27_3_dilatation_bound_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (m : MarkedRS S₀) {q : S₀ → ℂ → ℂ} {k : ℝ}
    (h : IsDeformationPoint q k (Quot.mk _ m))
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → m.X.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS m.marking := by
  obtain ⟨X, e, _hqc, _q', hT, hp⟩ := h
  obtain ⟨c, hc, hhom⟩ := s29_m_equiv_of_eq hp
  obtain ⟨hqcf, hle⟩ := s29_m_maxDil_conj_biholo m.qc (c₁ := Homeomorph.refl S₀) isBiholomorphic_id hc
  have h₁ : HasGenus X.carrier g := hasGenus_of_homeomorph hS e
  have hhom' : ContinuousMap.Homotopic (e : C(S₀, X.carrier))
      (((Homeomorph.refl S₀).trans (m.marking.trans c) : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier)) :=
    hhom.symm
  exact (thm26_2_uniqueness_of_uniformization hg hS h₁ (teichDeformation_isTeichmullerMap hT) hqcf hhom'
    (utm_isUniformization_comp hp₁ c hc)).1.trans hle

/-! ## Part 5. Teichmüller's existence theorem for `S₀ = ℍ/Γ₀` via Hamilton's theorem (§36): the E2 interface

`utm_x_` (s27t stage E2, coordinator 553e2d): the stubs [S1]–[S7b] (sorried, each with its truth argument, route,
reuse and estimate) and the proved glue for the companions `lemma27_1_injective_of_uniformization`,
`teichSpace_deformation_bijection_of_uniformization` and `thm27_2_existence_qc_of_uniformization`.

*Existence* (`utm_x_existence_core`): the lifted Beltrami coefficient `μ ∈ M(Γ₀)` of a marked surface ([S1]) has an
extremal representative `μ₀ ∼ μ` (`exists_extremal_mod_boundary`), which is `0` or `k φ̄/|φ|` (`thm36_2_finite_type`;
`hfin` from `dim Q(S₀) < ∞` and the descent [S4], no Riemann–Roch); a Teichmüller map has the lifted coefficient
`k ψ̄/|ψ|` ([S3]); equal boundary values of `f^μ` give equal classes (the uniformization transport [S2a] and the
bridge [S2b]).  *Uniqueness* (`utm_x_dil_le_of_equiv`): the inverse of a Teichmüller map is a Teichmüller map
([S7a]) with target `S₀ = ℍ/Γ₀`, so `thm26_2_uniqueness_of_uniformization` applies; then equal dilatations give
proportional differentials ([S7b]).  The walls avoided by every stub: W-IoD (invariance of domain in `ℝ^{6g-6}`), W-RR
(`dim_ℝ Q(S₀) = 6g - 6`), W-QC (`exists_qc_in_homotopy_class`), W-TOP (classification of surfaces), W-UC
(uniformizing an abstract surface). -/

/-- The base point `[S₀, id]` of `T(S₀)` as a marked surface. -/
def utm_x_base (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] : MarkedRS S₀ :=
  ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩

/-- **The lifted Beltrami coefficient** of a marked surface `m = (X, f)`: `μ` is, a.e. on `ℍ`, the complex dilatation
of `f ∘ p₀` read in the chart of `X` at the image point, `τ ↦ μ_{w ↦ φ_{f(p₀ τ)}(f(p₀ w))}(τ)`. -/
def utm_x_liftCoeff (p₀ : UpperHalfPlane → S₀) (m : MarkedRS S₀) (μ : ℂ → ℂ) : Prop :=
  ∀ᵐ τ ∂(volume.restrict upperHalf), μ τ =
    complexDilatation (fun w => chartAt ℂ (m.marking (utm_pext p₀ τ)) (m.marking (utm_pext p₀ w))) τ

/-- A quasiconformal homeomorphism `f : S₀ → S` onto a closed Riemann surface `S` (in the universe of `S₀`) as a
marked surface `(S, f)`: `S` bundled as a `ClosedRS` (compactness is an instance, e.g. from `HasGenus S g`). -/
def utm_x_marked {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [CompactSpace S] [IsManifold 𝓘(ℂ) ω S] (f : S₀ ≃ₜ S) (hf : IsQCRS f) : MarkedRS S₀ :=
  ⟨⟨S⟩, f, hf⟩

/-! ### The stubs -/

/-- [S1, stub] **The lifted Beltrami coefficient exists.**  For a marked surface `m = (X, f)` there is `μ ∈ M(Γ₀)`
(bounded by some `k < 1`, `0` on the closed lower half-plane, `Γ₀`-compatible) with `utm_x_liftCoeff p₀ m μ`.

*Truth:* near `τ₀ ∈ ℍ` put `x = p₀ τ₀` and `h = φ_x ∘ p̂`, holomorphic and injective with `h' ≠ 0`
(`utm_liftQD_local`); for `τ` near `τ₀` the expression `w ↦ φ_{f(p̂ τ)}(f(p̂ w))` equals, near `τ`, `T ∘ L ∘ h` with
`L = localMapExpr f x` (`K`-q.c., `K` from `m.qc`) and `T` a holomorphic chart transition of `X`, so its dilatation
at `τ` is `μ_L(h τ) conj h'(τ)/h'(τ)` (`s23_dilatation_comp_left/right`) and `|·| ≤ (K-1)/(K+1)` a.e. (Theorems 9.3,
9.4; `h` preserves null sets).  Define `μ` pointwise by that dilatation on `ℍ` and `0` off `ℍ`; it is a.e. strongly
measurable (on each set of a countable cover of `ℍ` it agrees a.e. with the dilatation of the fixed map `L ∘ h`).
`Γ₀`-compatibility: `p̂ ∘ γ = p̂` on `ℍ` (`utm_b_pext_mob`), so the pre-composition by `γ` gives the factor
`(cz+d)²/conj((cz+d)²)` (`s23_dilatation_comp_right`, as in `h23l_dilatation_conj`).

*Route/reuse:* `utm_liftQD_local` (this file l.460), `utm_a_differentiableAt` (l.441), `utm_b_pext_mob` (l.890);
S23 `s23_dilatation_comp_left` (l.154), `s23_dilatation_comp_right` (l.162), `h23l_dilatation_conj` (l.927); S09
`thm9_3_differentiable_ae` (l.4868), `thm9_4_dilatation_ae` (l.6763); the indicator/measurability pattern of S33
`normalizedLift_beltrami_mem` (l.45).  *Estimate:* 0.4–0.7k lines.

*Walls:* none.  A local statement about `f ∘ p₀` in the charts of `X`: `X` is not uniformized (no W-UC), no homotopy
class is changed (no W-QC, no W-TOP), no dimension (no W-RR), no invariance of domain (no W-IoD). -/
theorem utm_x_exists_liftCoeff [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (m : MarkedRS S₀) : ∃ μ : BeltramiGamma Γ₀, utm_x_liftCoeff p₀ m μ.1.1 := by
  -- the installed UT coefficient `s27u_liftCoeff p₀ f` lies in `M(Γ₀)`; on `ℍ` it is the chart-read dilatation
  -- (`s27u_liftCoeff_of_mem`, stated with `utm_pext`)
  obtain ⟨μ, hμ, hΓ⟩ := s27u_liftCoeff_beltramiH hp₀ m.qc
  refine ⟨⟨μ, hΓ⟩, ?_⟩
  unfold utm_x_liftCoeff
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with τ hτ
  show μ.1 τ = _
  rw [hμ, s27u_liftCoeff_of_mem p₀ m.marking hτ]

/-- [S2a, stub] **Uniformization transport (UT): holomorphy.**  If `μ ∈ M(Γ₀)` is the lifted coefficient of
`m = (X, f)` and `F : ℍ ≃ₜ ℍ` is the map induced by `f^μ = fMuSym μ`, then `D = f ∘ p₀ ∘ F⁻¹ : ℍ → X` is holomorphic.
(The rest of UT, `IsUniformization (b33_d_conjGroup Γ₀ F) D`, is the proved glue `utm_x_transport`.)

*Truth:* fix `w₀ = F τ₀`, `x = p₀ τ₀`, `y = f x`, and an open `U ∋ τ₀` in `ℍ` on which `h = φ_x ∘ p̂` is injective
(`utm_liftQD_local`) and `f(p̂ U)` lies in the chart of `y`.  On `U`, `g = φ_y ∘ f ∘ p̂ = L ∘ h` (`L` the local
expression of `f` at `x`) is `K`-q.c., and its complex dilatation is `μ` a.e.: the hypothesis `hμ` reads it in the
chart at `f(p̂ τ)`, which differs from `φ_y` by a holomorphic transition (`s23_dilatation_comp_left`).  `fMuSym μ` is
q.c. on `ℍ` with dilatation `μ` a.e. (`fMuSym_upperHalf`).  Hence `g ∘ (fMuSym μ)⁻¹` is conformal on `fMuSym μ (U)`
(`bg_conformal_of_dilatation_eq`), and on that open set it is `φ_y ∘ D`; so `D` is holomorphic at `w₀`.

*Route/reuse:* S33 `fMuSym_upperHalf` (l.391), `bg_conformal_of_dilatation_eq` (l.144), `b33_d_homeo_upper` (l.3629);
`utm_liftQD_local` (this file l.460); S23 `s23_dilatation_comp_left` (l.154), `lift_isKQC_automorphic` (l.1042, the
pattern "local expression composed with local sections of `p₀` is `K`-q.c."); S09 `ac_t_isKQC_restrict` (l.6555);
Mathlib `mdifferentiableAt_iff`, `UpperHalfPlane.mdifferentiableAt_ofComplex`.  *Estimate:* 0.5–0.9k.

*Walls:* none.  This is the measurable Riemann mapping theorem (installed, `thm13_7`) used on `ℍ`: it uniformizes a
quasiconformal image of the already uniformized `S₀`, not an abstract surface (no W-UC); the marking is given (no W-QC,
no W-TOP); no dimension (no W-RR), no invariance of domain (no W-IoD). -/
theorem utm_x_transport_mdifferentiable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {m : MarkedRS S₀} {μ : BeltramiGamma Γ₀} (hμ : utm_x_liftCoeff p₀ m μ.1.1)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : ∀ τ : UpperHalfPlane, (F τ : ℂ) = fMuSym μ.1.1 τ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => m.marking (p₀ (F.symm w))) := by
  obtain ⟨K, hK⟩ := m.qc
  have hK1 : (1 : ℝ) ≤ K := hK.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨k, hk0', hk1', hμk⟩ := bg_beltramiH_upper μ.1
  -- `μ` is the UT coefficient `s27u_liftCoeff p₀ f` a.e. on `ℍ`, so `f^μ` is the UT map (U11; `fMuSym = s27u_fSym`)
  have hae : ∀ᵐ z ∂(volume.restrict upperHalf), μ.1.1 z = s27u_liftCoeff p₀ m.marking z := by
    filter_upwards [hμ, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
    rw [h1, s27u_liftCoeff_of_mem p₀ m.marking hz]
  have heq : fMuSym μ.1.1 = s27u_fSym (s27u_liftCoeff p₀ m.marking) :=
    s27u_fSym_congr_ae hk0' hk1' hμk hk0 hk1 (s27u_liftCoeff_isBeltramiCoeff hp₀ hK) hae
  have hF' : ∀ τ, (F τ : ℂ) = s27u_fSym (s27u_liftCoeff p₀ m.marking) τ := fun τ => by
    rw [hF τ, heq]
  -- U7: the transported projection `s27u_proj p₀ f F = f ∘ p₀ ∘ F⁻¹` is holomorphic
  exact s27u_proj_mdifferentiable hp₀ hK hF'

/-- [S2b, stub] **The bridge: equal boundary values give equivalent marked surfaces.**  Let `Dᵢ` uniformize `mᵢ.X`
with group `b33_d_conjGroup Γ₀ Fᵢ`, where `Fᵢ` is the map of `ℍ` induced by `f^{μᵢ}` and lifts `mᵢ.marking`
(`Dᵢ ∘ Fᵢ = mᵢ.marking ∘ p₀`), as produced by UT (`utm_x_transport`).  If `f^{μ₁} = f^{μ₂}` on `ℝ`
(`teichSetoidGamma`), then `m₁ ∼ m₂`.

*Truth:* `Fᵢ` is a normalized lift of `mᵢ.marking` for `(p₀, Dᵢ)` (`f^{μᵢ}` fixes `0, 1, ∞`), whose boundary extension
is `f^{μᵢ}` on `ℂ̂` (a homeomorphism of `ℂ̂` preserving `ℍ`, so `IsHomeoExtension` holds); the boundary values agree,
so `thm27_1` (⇐) gives `m₁ ∼ m₂`.  Directly (independently of `thm27_1`): `χᵢ(γ) = Fᵢ γ Fᵢ⁻¹` is Möbius (`b33_d_def`)
and `χ₁(γ) = χ₂(γ)` because they agree on `f^{μ₁}(ℝ) = f^{μ₂}(ℝ)` (the (⇐) half of the proof of `chi_eq_iff`, which
does not use its density hypothesis; `b33_d_ext_real`); so the two groups coincide, `c := D₂ ∘ D₁⁻¹ : X₁ → X₂` is a
well defined biholomorphism, and `F₁`, `F₂` are lifts of `c ∘ m₁.marking` and `m₂.marking` for `(p₀, D₂)` inducing the
same isomorphism, hence homotopic maps (`thm23_1_homotopy_iff` (⇐) with `γ₁ = 1`).

*Route/reuse:* S27 `thm27_1` (l.980, being proved in wave t12-L), `IsNormalizedLift` (l.145); `Homeomorph.onePointCongr`
for the extension; or S33 `b33_d_def` (l.3487), `b33_d_rel_iff` (l.3661), `b33_d_ext_real` (l.3754), the (⇐) block of
`chi_eq_iff` (l.4014), S23 `thm23_1_homotopy_iff` (l.1523), `IsCoveringMap.eq_of_comp_eq`.  *Estimate:* 0.1–0.2k via
`thm27_1`; 0.6–1k without it.

*Walls:* none.  Both surfaces come uniformized in the hypotheses (no W-UC); the homotopy is built between given maps
(no W-QC, no W-TOP); no dimension (no W-RR), no invariance of domain (no W-IoD).  It is a special case of `thm27_1`
(⇐), not a book statement. -/
theorem utm_x_equiv_of_boundary [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {m₁ m₂ : MarkedRS S₀} {μ₁ μ₂ : BeltramiGamma Γ₀}
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {D₁ : UpperHalfPlane → m₁.X.carrier}
    {D₂ : UpperHalfPlane → m₂.X.carrier} (hF₁ : ∀ τ : UpperHalfPlane, (F₁ τ : ℂ) = fMuSym μ₁.1.1 τ)
    (hF₂ : ∀ τ : UpperHalfPlane, (F₂ τ : ℂ) = fMuSym μ₂.1.1 τ) (hD₁ : ∀ τ, D₁ (F₁ τ) = m₁.marking (p₀ τ))
    (hD₂ : ∀ τ, D₂ (F₂ τ) = m₂.marking (p₀ τ)) (hU₁ : IsUniformization (b33_d_conjGroup Γ₀ F₁) D₁)
    (hU₂ : IsUniformization (b33_d_conjGroup Γ₀ F₂) D₂) (h12 : teichSetoidGamma Γ₀ μ₁ μ₂) :
    m₁.Equiv m₂ := by
  -- `Fᵢ` is a normalized lift of `mᵢ.marking` for `(p₀, Dᵢ)` with boundary map `OnePoint.map f^{μᵢ}`: `Dᵢ` is the
  -- transported projection `s27u_proj p₀ mᵢ.marking Fᵢ` (by `hDᵢ`), so the UT glue `s27u_isNormalizedLift` applies
  have hNL : ∀ (m : MarkedRS S₀) (μ : BeltramiGamma Γ₀) (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
      (D : UpperHalfPlane → m.X.carrier), (∀ τ : UpperHalfPlane, (F τ : ℂ) = fMuSym μ.1.1 τ) →
      (∀ τ, D (F τ) = m.marking (p₀ τ)) → IsNormalizedLift p₀ D m.marking F (OnePoint.map (fMuSym μ.1.1)) := by
    intro m μ F D hF hD
    obtain ⟨k, hk0, hk1, hμk⟩ := bg_beltramiH_upper μ.1
    obtain ⟨-, hN, hK, -⟩ := bg_sym_spec hk0 hk1 hμk
    obtain ⟨hU, -⟩ := fMuSym_upperHalf hk0 hk1 hμk
    have hDe : D = s27u_proj p₀ m.marking F := by
      funext w
      rw [← F.apply_symm_apply w, hD]
      show m.marking (p₀ (F.symm w)) = m.marking (p₀ (F.symm (F (F.symm w))))
      rw [F.symm_apply_apply]
    rw [hDe]
    exact s27u_isNormalizedLift m.marking hK hN.2.1 hU hN.2.2.1 hN.2.2.2.1 hF
  -- equal boundary values on `ℝ` (`teichSetoidGamma`), so Theorem 27.1 (⇐) gives `m₁ ∼ m₂`
  refine (thm27_1 hg hS hp₀ m₁ m₂ hU₁ hU₂ (hNL m₁ μ₁ F₁ D₁ hF₁ hD₁) (hNL m₂ μ₂ F₂ D₂ hF₂ hD₂)).2 fun x => ?_
  rw [OnePoint.map_some, OnePoint.map_some, h12 x]

/-- [S3, stub] **The Teichmüller identity.**  The lifted coefficient of a Teichmüller map `f : S₀ → X` with initial
differential `q` is `k ψ̄/|ψ|`, `ψ = utm_liftQD q p₀` the lift of `q`.

*Truth:* by `teichmullerMap_beltrami`, in the chart at `x` the local expression `L` of `f` has dilatation
`k q̄ₓ/|qₓ|` a.e. on its domain.  Near `τ` with `x = p₀ τ`, `h = φ_x ∘ p̂`, the expression read at the image point is
`T ∘ L ∘ h` (`T` a holomorphic transition), with dilatation `μ_L(h τ) conj h'/h' = k conj(qₓ(h τ) h'²)/|qₓ(h τ) h'²|`
(`s23_dilatation_comp_left/right`), and `qₓ(h τ) h'(τ)² = ψ(τ)` (`utm_liftQD_local`); the exceptional sets are null
(preimages of null sets under the local biholomorphism `h`, plus the countable zero set of `ψ`).

*Route/reuse:* S26 `teichmullerMap_beltrami` (l.2699), `s26u_zeros_countable` (l.1910); `utm_liftQD_local` (this file
l.460); S23 `s23_dilatation_comp_left` (l.154), `s23_dilatation_comp_right` (l.162); a countable cover of `ℍ` by the
neighbourhoods `U` of `utm_liftQD_local`.  *Estimate:* 0.3–0.6k.

*Walls:* none: a local computation in charts (no W-UC, W-QC, W-TOP, W-RR, W-IoD). -/
theorem utm_x_liftCoeff_teichmullerMap [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {X : ClosedRS.{u}} {f : S₀ ≃ₜ X.carrier} {q : S₀ → ℂ → ℂ}
    {q' : X.carrier → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    utm_x_liftCoeff p₀ ⟨X, f, hf.qc⟩ (utm_x_tcoeff k (utm_liftQD q p₀)) := by
  have hZ0 : volume {τ | τ ∈ upperHalf ∧ utm_liftQD q p₀ τ = 0} = 0 :=
    (utm_x1_liftQD_zeros_countable hf.initial hf.initial_ne hp₀).measure_zero _
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0)] with τ hτ hτZ
  exact utm_x1_lift_pointwise hp₀ hf hτ fun h0 => hτZ ⟨hτ, h0⟩

/-- A closed Euclidean disc `closedBall c r` with `r < Im c` lies in `ℍ`. -/
theorem utm_x2_closedBall_subset {c : ℂ} {r : ℝ} (hr : r < c.im) : closedBall c r ⊆ upperHalf := by
  intro z hz
  have h1 : |z.im - c.im| ≤ ‖z - c‖ := by
    have h := abs_im_le_norm (z - c)
    rwa [Complex.sub_im] at h
  have h2 : ‖z - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  have h3 := neg_abs_le (z.im - c.im)
  show 0 < z.im
  linarith

/-- The trace on `ℍ` of a closed Euclidean disc `closedBall c r` with `r < Im c` is compact. -/
theorem utm_x2_isCompact_preimage {c : ℂ} {r : ℝ} (hr : r < c.im) :
    IsCompact (UpperHalfPlane.coe ⁻¹' closedBall c r) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_iff, image_preimage_eq_of_subset]
  · exact isCompact_closedBall c r
  · intro z hz
    exact ⟨⟨z, utm_x2_closedBall_subset hr hz⟩, rfl⟩

/-- **Evenly covered discs.**  Every `τ ∈ ℍ` is the centre of a Euclidean disc of radius `r < Im τ` on which the
uniformization `p` is injective (`p` is a local homeomorphism). -/
theorem utm_x2_disc {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (τ : UpperHalfPlane) : ∃ r : ℝ, 0 < r ∧ r < τ.im ∧ InjOn p (UpperHalfPlane.coe ⁻¹' ball (τ : ℂ) r) := by
  obtain ⟨E, hτE, hpE⟩ := hp.1.isLocalHomeomorph τ
  have ho : IsOpen (UpperHalfPlane.coe '' E.source) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ E.open_source
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 ho τ ⟨τ, hτE, rfl⟩
  have him := τ.im_pos
  refine ⟨min ε (τ.im / 2), lt_min hε (by linarith), (min_le_right _ _).trans_lt (by linarith), ?_⟩
  have hsub : UpperHalfPlane.coe ⁻¹' ball (τ : ℂ) (min ε (τ.im / 2)) ⊆ E.source := by
    intro σ hσ
    obtain ⟨σ', hσ', he⟩ := hεsub (ball_subset_ball (min_le_left _ _) hσ)
    rwa [← UpperHalfPlane.ext he]
  rw [hpE]
  exact E.injOn.mono hsub

/-- [S5, stub] **A fundamental domain.**  The covering group `Γ₀` of the compact `S₀ = ℍ/Γ₀` has a measurable
fundamental domain in the sense of `IsFundamentalDomainH` (every orbit meets `F`, orbits meet `interior F` at most
once, `F \ interior F` is null).

*Truth:* cover the compact `K` meeting every orbit (`utm_exists_compact_translate`) by finitely many open discs
`B₁, …, Bₙ`, `closure Bᵢ ⊆ ℍ`, on each of which `p₀` is injective (evenly covered), and put
`F = ⋃ᵢ (Bᵢ \ ⋃_{j<i} Γ₀ Bⱼ)`.  The first disc met by an orbit contains a point of it in `F`; two points of `F` in one
orbit lie in one `Bᵢ`, where `p₀` is injective, so `F` is even a strict fundamental set.  `Γ₀ Bⱼ` is open, so `F` is
Borel, and `F \ interior F` lies in the union of the circles `γ(∂Bⱼ)` (`Γ₀` is countable, the family `{γ Bⱼ}` is
locally finite by proper discontinuity [S6]), a null set.  (Alternatively a Dirichlet domain.)

*Route/reuse:* S23 `utm_exists_compact_translate` (l.1790); `IsCoveringMap.isLocalHomeomorph`; [S6] for local
finiteness; Möbius images of circles (Lemmas/Mobius).  *Estimate:* 0.6–1.2k (the Dirichlet route 1.3–2.5k).

*Walls:* none: point-set topology and measure on `ℍ` for the given `Γ₀` (no Gauss–Bonnet; no W-UC, W-QC, W-TOP, W-RR,
W-IoD). -/
theorem utm_x_exists_fundamentalDomain [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : ∃ F : Set ℂ, IsFundamentalDomainH Γ₀ F := by
  have hF := utm_x2_isFuchsian hp₀
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp₀
  choose r hr0 hrim hrinj using utm_x2_disc hp₀
  set B : UpperHalfPlane → Set UpperHalfPlane := fun σ => UpperHalfPlane.coe ⁻¹' ball (σ : ℂ) (r σ) with hBdef
  set D : UpperHalfPlane → Set UpperHalfPlane := fun σ => UpperHalfPlane.coe ⁻¹' closedBall (σ : ℂ) (r σ)
    with hDdef
  have hBo : ∀ σ, IsOpen (B σ) := fun σ => isOpen_ball.preimage UpperHalfPlane.continuous_coe
  have hBD : ∀ σ, B σ ⊆ D σ := fun σ => preimage_mono ball_subset_closedBall
  have hDc : ∀ σ, IsCompact (D σ) := fun σ => utm_x2_isCompact_preimage (hrim σ)
  have hDcl : ∀ σ, IsClosed (D σ) := fun σ => isClosed_closedBall.preimage UpperHalfPlane.continuous_coe
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover B fun σ _ =>
    (hBo σ).mem_nhds (show (σ : ℂ) ∈ ball (σ : ℂ) (r σ) from mem_ball_self (hr0 σ))
  set C := ⋃ σ ∈ t, D σ with hCdef
  have hC : IsCompact C := t.isCompact_biUnion fun σ _ => hDc σ
  set G := {γ ∈ Γ₀ | ((γ • ·) '' C ∩ C).Nonempty} with hGdef
  have hG : G.Finite := hF C hC
  have hwo : IsWellOrder UpperHalfPlane WellOrderingRel := WellOrderingRel.isWellOrder
  have hwf : WellFounded (WellOrderingRel (α := UpperHalfPlane)) := hwo.wf
  set Fσ : UpperHalfPlane → Set UpperHalfPlane := fun σ =>
    {τ | τ ∈ B σ ∧ ∀ σ' ∈ t, WellOrderingRel σ' σ → ∀ γ ∈ Γ₀, γ • τ ∉ B σ'} with hFσdef
  set F' := ⋃ σ ∈ t, Fσ σ with hF'def
  have hcl : ∀ σ, IsClosed {τ : UpperHalfPlane | ∀ σ' ∈ t, WellOrderingRel σ' σ → ∀ γ ∈ Γ₀, γ • τ ∉ B σ'} := by
    intro σ
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun σ' => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun γ =>
      isClosed_iInter fun _ => ?_
    exact (hBo σ').isClosed_compl.preimage (continuous_const_smul γ)
  have hFσm : ∀ σ, MeasurableSet (Fσ σ) := fun σ => (hBo σ).measurableSet.inter (hcl σ).measurableSet
  refine ⟨UpperHalfPlane.coe '' F', ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨τ, -, rfl⟩
    exact τ.coe_im_pos
  · exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.2
      (Finset.measurableSet_biUnion t fun σ _ => hFσm σ)
  · intro τ
    obtain ⟨γ₀, hγ₀, hK₀⟩ := hKz τ
    have hne : {σ | σ ∈ t ∧ ∃ γ ∈ Γ₀, γ • τ ∈ B σ}.Nonempty := by
      obtain ⟨σ, hσt, hσ⟩ := mem_iUnion₂.1 (htK hK₀)
      exact ⟨σ, hσt, γ₀, hγ₀, hσ⟩
    obtain ⟨hσ₀t, γ, hγ, hγB⟩ := hwf.min_mem _ hne
    refine ⟨γ, hγ, γ • τ, mem_iUnion₂.2 ⟨hwf.min _ hne, hσ₀t, hγB, fun σ' hσ't hR γ' hγ' hB => ?_⟩, rfl⟩
    refine hwf.not_lt_min {σ | σ ∈ t ∧ ∃ γ ∈ Γ₀, γ • τ ∈ B σ} ⟨hσ't, γ' * γ, Γ₀.mul_mem hγ' hγ, ?_⟩ hR
    rwa [mul_smul]
  · rintro τ₁ τ₂ h₁ h₂ ⟨γ, hγ, hγτ⟩
    obtain ⟨τ₁', h₁', he₁⟩ := interior_subset h₁
    obtain ⟨τ₂', h₂', he₂⟩ := interior_subset h₂
    rw [UpperHalfPlane.ext he₁] at h₁'
    rw [UpperHalfPlane.ext he₂] at h₂'
    obtain ⟨σ₁, hσ₁t, hB₁, hF₁⟩ := mem_iUnion₂.1 h₁'
    obtain ⟨σ₂, hσ₂t, hB₂, hF₂⟩ := mem_iUnion₂.1 h₂'
    rcases trichotomous_of WellOrderingRel σ₁ σ₂ with h | h | h
    · refine absurd ?_ (hF₂ σ₁ hσ₁t h γ⁻¹ (Γ₀.inv_mem hγ))
      rwa [← hγτ, inv_smul_smul]
    · subst h
      exact hrinj σ₁ hB₁ hB₂ ((hp₀.2.2.2 τ₁ τ₂).2 ⟨γ, hγ, hγτ⟩)
    · refine absurd ?_ (hF₁ σ₂ hσ₂t h γ hγ)
      rwa [hγτ]
  · -- `F \ interior F ⊆ coe '' (F' \ interior F')`
    have hsub1 : UpperHalfPlane.coe '' F' \ interior (UpperHalfPlane.coe '' F') ⊆
        UpperHalfPlane.coe '' (F' \ interior F') := by
      rintro _ ⟨⟨τ, hτ, rfl⟩, hni⟩
      refine ⟨τ, ⟨hτ, fun hi => hni ?_⟩, rfl⟩
      exact UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.image_interior_subset F' ⟨τ, hi, rfl⟩
    -- `F' \ interior F'` lies in finitely many Möbius preimages of circles
    have hsub2 : F' \ interior F' ⊆ ⋃ σ' ∈ (t : Set UpperHalfPlane), ⋃ γ ∈ G,
        {τ : UpperHalfPlane | ((γ • τ : UpperHalfPlane) : ℂ) ∈ sphere (σ' : ℂ) (r σ')} := by
      rintro τ ⟨hτ, hni⟩
      obtain ⟨σ, hσt, hBσ, hFσ⟩ := mem_iUnion₂.1 hτ
      by_contra hcon
      simp only [mem_iUnion₂, not_exists] at hcon
      apply hni
      set V := B σ ∩ ⋂ σ' ∈ {σ' | σ' ∈ t ∧ WellOrderingRel σ' σ}, ⋂ γ ∈ G,
        (fun τ : UpperHalfPlane => γ • τ) ⁻¹' (D σ')ᶜ with hV
      have hVo : IsOpen V := by
        refine (hBo σ).inter (Set.Finite.isOpen_biInter (t.finite_toSet.subset fun x hx => hx.1)
          fun σ' _ => ?_)
        exact Set.Finite.isOpen_biInter hG fun γ _ => (hDcl σ').isOpen_compl.preimage (continuous_const_smul γ)
      have hτV : τ ∈ V := by
        refine ⟨hBσ, mem_iInter₂.2 fun σ' hσ' => mem_iInter₂.2 fun γ hγG => ?_⟩
        intro hD
        have hnB : γ • τ ∉ B σ' := hFσ σ' hσ'.1 hσ'.2 γ hγG.1
        refine hcon σ' (Finset.mem_coe.2 hσ'.1) γ hγG ?_
        rw [← closedBall_sdiff_ball]
        exact ⟨hD, hnB⟩
      have hVF : V ⊆ F' := by
        rintro w ⟨hwB, hwV⟩
        refine mem_iUnion₂.2 ⟨σ, hσt, hwB, fun σ' hσ't hR γ hγ hγw => ?_⟩
        have hγG : γ ∈ G := ⟨hγ, γ • w, ⟨w, mem_iUnion₂.2 ⟨σ, hσt, hBD σ hwB⟩, rfl⟩,
          mem_iUnion₂.2 ⟨σ', hσ't, hBD σ' hγw⟩⟩
        exact (mem_iInter₂.1 (mem_iInter₂.1 hwV σ' ⟨hσ't, hR⟩) γ hγG) (hBD σ' hγw)
      exact mem_interior.2 ⟨V, hVF, hVo, hτV⟩
    refine measure_mono_null (hsub1.trans (image_mono hsub2)) ?_
    rw [image_iUnion₂]
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun σ' _ => ?_
    rw [image_iUnion₂]
    refine (measure_biUnion_null_iff hG.countable).2 fun γ _ => ?_
    refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (f := utm_b_mob γ⁻¹) ?_ (Measure.addHaar_sphere volume (σ' : ℂ) (r σ')))
    · rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨_, hτ, ?_⟩
      rw [utm_b_mob_coe, inv_smul_smul]
    · intro z hz
      have hzim : 0 < z.im := utm_x2_closedBall_subset (hrim σ') (sphere_subset_closedBall hz)
      exact (((utm_b_mob_differentiableOn γ⁻¹ z hzim).differentiableAt
        (isOpen_upperHalf.mem_nhds hzim)).restrictScalars ℝ).differentiableWithinAt

/-- [S6, stub] **The covering group is Fuchsian.**  `Γ₀` acts properly discontinuously: for compact `C ⊆ ℍ` only
finitely many `γ ∈ Γ₀` have `γ C ∩ C ≠ ∅`.

*Truth:* the maps `τ ↦ γ τ`, `γ ∈ Γ₀`, are the deck transformations of the covering `p₀` (fibres = orbits,
`IsCoveringMap.eq_of_comp_eq`), each Möbius map coming from at most two matrices `±γ`.  If infinitely many distinct
`γₙ` had `γₙ cₙ = c'ₙ` with `cₙ, c'ₙ ∈ C`, pass to `cₙ → c`, `c'ₙ → c'`; `p₀ c = p₀ c'` (`S₀` Hausdorff), so
`c' = γ c`, and for large `n` both `cₙ` and `γ⁻¹ γₙ cₙ` lie in one sheet over a neighbourhood of `p₀ c`, whence
`γ⁻¹ γₙ cₙ = cₙ` and `γₙ = ±γ` (`ActsFreely`, `s27g_actsFreely`): a contradiction.

*Route/reuse:* `IsCoveringMap` API (evenly covered neighbourhoods), `s27g_actsFreely` (installed S27), compactness of
`C` (sequential, `ℍ` is metrizable).  *Estimate:* 0.2–0.4k.

*Walls:* none: covering-space topology of the given `p₀` (no W-UC, W-QC, W-TOP, W-RR, W-IoD). -/
theorem utm_x_isFuchsian [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : IsFuchsian Γ₀ := by
  exact utm_x2_isFuchsian hp₀

/-- The restriction `q ↦ ψ|_K` of the lifted differential `ψ = utm_liftQD q p₀` to a set `K ⊆ ℍ`, as a `ℂ`-linear
map `Q(S₀) → C(K, ℂ)`. -/
def utm_x2_restrL [IsManifold 𝓘(ℂ) ω S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {K : Set ℂ} (hK : K ⊆ upperHalf) :
    holQuadDiffSubmodule S₀ →ₗ[ℂ] C(K, ℂ) where
  toFun q := ⟨fun z => utm_liftQD (q : S₀ → ℂ → ℂ) p₀ z,
    ((utm_liftQD_differentiableOn q.2 hp₀).continuousOn.mono hK).domRestrict⟩
  map_add' q₁ q₂ := by
    ext z
    exact utm_x_liftQD_add _ _ p₀ z
  map_smul' c q := by
    ext z
    exact utm_x_liftQD_smul _ p₀ c z

/-- [S-i, stub] **`Q(S₀)` is finite dimensional** (for the compact `S₀ = ℍ/Γ₀`, without a given basis `e`).

*Truth:* `q ↦ ψ = utm_liftQD q p₀` is injective (`utm_liftQD_ne`) with image the holomorphic weight-`4` automorphic
forms ([S4]).  `|ψ(z)| (Im z)²` is `Γ₀`-invariant (`utm_b_liftQD_automorphic`, `Im(γz) = Im z/|cz+d|²`), hence
bounded by its maximum on the compact `K` meeting every orbit (`utm_exists_compact_translate`): `N(ψ) = sup_K |ψ| Im²`
is a norm on the image, which embeds it into `C(K, ℂ)`.  Its closed unit ball is compact: `|ψ| ≤ (Im z)⁻²` on `ℍ` is a
locally uniform bound, Montel gives a locally uniformly convergent subsequence, the limit is automorphic and
holomorphic, hence again a lift ([S4]), and the convergence is uniform on `K`.  Riesz
(`FiniteDimensional.of_isCompact_closedBall₀`) gives finite dimension.

*Route/reuse:* S35 `h35_montel_loc` (l.8227); `utm_liftQD_ne` (this file l.555), `utm_liftQD_differentiableOn`
(l.531), `utm_b_liftQD_automorphic` (l.903); S23 `utm_exists_compact_translate` (l.1790); [S4]; Mathlib
`FiniteDimensional.of_isCompact_closedBall₀`, `BoundedContinuousFunction`/`ContinuousMap` sup norm.
*Estimate:* 0.6–1.2k (split if needed: the invariant bound 0.15k; Montel + Riesz 0.5–1k).

*Walls:* finiteness only: the dimension `6g - 6` (W-RR, `thm22_5`) is neither used nor implied; only the given
`ℍ/Γ₀` is involved (no W-UC, W-QC, W-TOP, W-IoD). -/
theorem utm_x_finite_holQuadDiff [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : Module.Finite ℂ (holQuadDiffSubmodule S₀) := by
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp₀
  set Kc : Set ℂ := UpperHalfPlane.coe '' K with hKcdef
  have hKcc : IsCompact Kc := hK.image UpperHalfPlane.continuous_coe
  have hKcU : Kc ⊆ upperHalf := by
    rintro _ ⟨τ, -, rfl⟩
    exact τ.coe_im_pos
  have hmemK : ∀ z (hz : 0 < z.im), ∃ γ ∈ Γ₀, utm_b_mob γ z ∈ Kc := by
    intro z hz
    obtain ⟨γ, hγ, hγK⟩ := hKz ⟨z, hz⟩
    exact ⟨γ, hγ, _, hγK, (utm_b_mob_smul γ hz).symm⟩
  have _ : CompactSpace ↥Kc := isCompact_iff_compactSpace.1 hKcc
  set Λ := utm_x2_restrL hp₀ hKcU with hΛ
  have hΛapp : ∀ (q : holQuadDiffSubmodule S₀) (z : ↥Kc), Λ q z = utm_liftQD (q : S₀ → ℂ → ℂ) p₀ z :=
    fun _ _ => rfl
  -- `Λ` is injective: a lift vanishing on `K` vanishes on `ℍ` (automorphy), so `q = 0` (`utm_liftQD_ne`)
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq0
    by_contra hne
    have hne' : (q : S₀ → ℂ → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨z, hz, hψ⟩ := utm_liftQD_ne q.2 hne' hp₀
    obtain ⟨γ, hγ, hγK⟩ := hmemK z hz
    have h2 : utm_liftQD (q : S₀ → ℂ → ℂ) p₀ (utm_b_mob γ z) = 0 := by
      have h := DFunLike.congr_fun hq0 ⟨_, hγK⟩
      rw [hΛapp] at h
      exact h
    rw [← utm_b_liftQD_automorphic (q : S₀ → ℂ → ℂ) hp₀ hγ hz, h2, zero_mul] at hψ
    exact hψ rfl
  -- a bound for `Im` on `K`
  obtain ⟨R, hR⟩ := hKcc.isBounded.exists_norm_le
  -- the range `V` of `Λ` has a compact closed unit ball
  have hV : FiniteDimensional ℂ (LinearMap.range Λ) := by
    refine FiniteDimensional.of_isCompact_closedBall₀ ℂ (r := 1) one_pos ?_
    refine isCompact_iff_isSeqCompact.2 fun u hu => ?_
    choose q hq using fun n => LinearMap.mem_range.1 (u n).2
    set ψ : ℕ → ℂ → ℂ := fun n => utm_liftQD (q n : S₀ → ℂ → ℂ) p₀ with hψdef
    have hψapp : ∀ n z, ψ n z = utm_liftQD (q n : S₀ → ℂ → ℂ) p₀ z := fun _ _ => rfl
    have hbK : ∀ n, ∀ z ∈ Kc, ‖ψ n z‖ ≤ 1 := by
      intro n z hz
      have h1 : ‖(u n : C(↥Kc, ℂ))‖ ≤ 1 := by
        have h := hu n
        rw [mem_closedBall_zero_iff] at h
        exact h
      have h2 := (ContinuousMap.norm_le _ zero_le_one).1 h1 ⟨z, hz⟩
      rw [← hq n, hΛapp] at h2
      rw [hψapp]
      exact h2
    have hbH : ∀ n, ∀ z ∈ upperHalf, ‖ψ n z‖ * z.im ^ 2 ≤ R ^ 2 := by
      intro n z hz
      obtain ⟨γ, hγ, hγK⟩ := hmemK z hz
      rw [hψapp, ← utm_x2_norm_mul_im_sq _ hp₀ hγ hz]
      have hA := hbK n _ hγK
      rw [hψapp] at hA
      have hB : (utm_b_mob γ z).im ^ 2 ≤ R ^ 2 := by
        have h1 := hR _ hγK
        have h0 : 0 < (utm_b_mob γ z).im := utm_b_mob_im_pos γ hz
        have h2 : (utm_b_mob γ z).im ≤ ‖utm_b_mob γ z‖ :=
          (le_abs_self _).trans (Complex.abs_im_le_norm _)
        nlinarith
      calc ‖utm_liftQD (q n : S₀ → ℂ → ℂ) p₀ (utm_b_mob γ z)‖ * (utm_b_mob γ z).im ^ 2 ≤ 1 * R ^ 2 :=
            mul_le_mul hA hB (sq_nonneg _) zero_le_one
        _ = R ^ 2 := one_mul _
    have hdiff : ∀ n, DifferentiableOn ℂ (ψ n) upperHalf := fun n => utm_liftQD_differentiableOn (q n).2 hp₀
    have hloc : ∀ z ∈ upperHalf, ∃ δ > 0, ball z δ ⊆ upperHalf ∧
        ∃ M : ℝ, ∀ n, ∀ w ∈ ball z δ, ‖ψ n w‖ ≤ M := by
      intro z hz
      have hz' : 0 < z.im := hz
      have hball : ∀ w ∈ ball z (z.im / 2), z.im / 2 < w.im := by
        intro w hw
        have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
          have h := Complex.abs_im_le_norm (w - z)
          rwa [Complex.sub_im] at h
        have h2 : ‖w - z‖ < z.im / 2 := by rwa [mem_ball, dist_eq_norm] at hw
        have h3 := neg_abs_le (w.im - z.im)
        linarith
      refine ⟨z.im / 2, by positivity, fun w hw => ?_, 4 * R ^ 2 / z.im ^ 2, fun n w hw => ?_⟩
      · show 0 < w.im
        linarith [hball w hw]
      · have hw' := hball w hw
        have hwpos : 0 < w.im := by linarith
        have h1 := hbH n w hwpos
        have h2 := norm_nonneg (ψ n w)
        rw [le_div_iff₀ (by positivity)]
        have h3 : z.im ^ 2 ≤ 4 * w.im ^ 2 := by nlinarith
        nlinarith
    obtain ⟨φ, hφ, g, hg, hlim⟩ := h35_montel_loc isOpen_upperHalf ψ hdiff hloc
    -- the limit is automorphic of weight `4`, hence a lift (the descent [S4])
    have hgΓ : ∀ γ ∈ Γ₀, ∀ z ∈ upperHalf,
        g ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = g z := by
      intro γ hγ z hz
      have hz' : 0 < z.im := hz
      have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz'⟩
      have t1 := hlim.tendsto_at (show utm_b_mob γ z ∈ upperHalf from utm_b_mob_im_pos γ hz')
      have t2 := hlim.tendsto_at hz
      have heq : ∀ k, ψ (φ k) (utm_b_mob γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ (φ k) z := by
        intro k
        rw [hψapp, hψapp, ← utm_b_liftQD_automorphic _ hp₀ hγ hz']
        field_simp
      have t3 := t1.div_const (((γ 1 0 : ℂ) * z + γ 1 1) ^ 4)
      simp only [heq] at t3
      exact tendsto_nhds_unique t3 t2
    obtain ⟨q', hq', hq'g⟩ := utm_x_descent hp₀ hg hgΓ
    have hconv : Tendsto (u ∘ φ) atTop (𝓝 ⟨Λ ⟨q', hq'⟩, LinearMap.mem_range_self Λ _⟩) := by
      rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_tendstoUniformly]
      have hU := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.1
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalf).1 hlim Kc hKcU hKcc)
      convert hU using 1
      · funext k x
        simp only [Function.comp_apply]
        rw [← hq (φ k), hΛapp]
      · funext x
        rw [Function.comp_apply, ← hq'g x (hKcU x.2)]
        rfl
    exact ⟨_, isClosed_closedBall.mem_of_tendsto hconv (Eventually.of_forall fun k => hu (φ k)), φ, hφ, hconv⟩
  exact Module.Finite.equiv (LinearEquiv.ofInjective Λ hinj).symm

/-- The transport `c_* q'` of a quadratic differential `q'` on `S₁` by a homeomorphism `c : S₁ ≃ₜ S₂`: in the chart
at `y`, `w ↦ q'_s(T w) T'(w)²` with `s = c⁻¹(φ_y⁻¹ w)` and `T = φ_s ∘ c⁻¹ ∘ φ_y⁻¹` (the chart at the point itself), and
`0` off the chart target. -/
def utm_x1_pushQD {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] (c : S₁ ≃ₜ S₂) (q' : S₁ → ℂ → ℂ) :
    S₂ → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator fun w =>
  q' (c.symm ((chartAt ℂ y).symm w))
      (chartAt ℂ (c.symm ((chartAt ℂ y).symm w)) (c.symm ((chartAt ℂ y).symm w))) *
    deriv (fun v => chartAt ℂ (c.symm ((chartAt ℂ y).symm w)) (c.symm ((chartAt ℂ y).symm v))) w ^ 2

/-- `T = φ_x ∘ c⁻¹ ∘ φ_y⁻¹` is holomorphic at every `w` of the chart target at `y` with `c⁻¹(φ_y⁻¹ w)` in the chart
source at `x` (`c⁻¹` is holomorphic, `s23_mdifferentiableAt_iff`). -/
theorem utm_x1_T_differentiableAt {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : IsBiholomorphic c) (x : S₁) (y : S₂) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hwx : c.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v))) w := by
  have h := ((s23_mdifferentiableAt_iff (f := c.symm) (y := x) ((chartAt ℂ y).map_target hw) hwx).1
    (hc.homeomorph_symm.1 ((chartAt ℂ y).symm w))).2
  rwa [(chartAt ℂ y).right_inv hw] at h

/-- `T = φ_x ∘ c⁻¹ ∘ φ_y⁻¹` is holomorphic on the open set `W = {v ∈ φ_y(U_y) | c⁻¹(φ_y⁻¹ v) ∈ U_x}` and injective
there, so `T' ≠ 0` on `W` (`deriv_ne_zero_of_injOn`). -/
theorem utm_x1_T_on {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : IsBiholomorphic c) (x : S₁) (y : S₂) :
    IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source)) ∧
      DifferentiableOn ℂ (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v)))
        ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source)) ∧
      ∀ w ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source),
        deriv (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v))) w ≠ 0 := by
  have hWo : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source)) :=
    (chartAt ℂ y).isOpen_inter_preimage_symm (c.symm.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)
  have hd : DifferentiableOn ℂ (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v)))
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source)) :=
    fun v hv => (utm_x1_T_differentiableAt hc x y hv.1 hv.2).differentiableWithinAt
  refine ⟨hWo, hd, fun w hw => deriv_ne_zero_of_injOn hWo hd ?_ hw⟩
  intro v₁ hv₁ v₂ hv₂ h12
  have h1 : c.symm ((chartAt ℂ y).symm v₁) = c.symm ((chartAt ℂ y).symm v₂) :=
    (chartAt ℂ x).injOn hv₁.2 hv₂.2 h12
  have h2 := c.symm.injective h1
  rw [← (chartAt ℂ y).right_inv hv₁.1, ← (chartAt ℂ y).right_inv hv₂.1, h2]

/-- **Local form of the transport.**  For `w` in the chart target at `y` and any chart `x` of `S₁` whose source
contains `c⁻¹(φ_y⁻¹ w)`: `(c_* q')_y(w) = q'_x(T w) T'(w)²` with `T = φ_x ∘ c⁻¹ ∘ φ_y⁻¹` (the transformation law of
`q'` between the charts at `s = c⁻¹(φ_y⁻¹ w)` and `x`, and the chain rule). -/
theorem utm_x1_pushQD_local {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : IsBiholomorphic c) {q' : S₁ → ℂ → ℂ} (hq' : IsHolQuadDiff q')
    (y : S₂) (x : S₁) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target)
    (hwx : c.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    utm_x1_pushQD c q' y w = q' x (chartAt ℂ x (c.symm ((chartAt ℂ y).symm w))) *
      deriv (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v))) w ^ 2 := by
  set s := c.symm ((chartAt ℂ y).symm w) with hs
  show (chartAt ℂ y).target.indicator _ w = _
  rw [indicator_of_mem hw]
  show q' s (chartAt ℂ s s) * deriv (fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) w ^ 2 = _
  have hst : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
  have hss : (chartAt ℂ s).symm (chartAt ℂ s s) = s := (chartAt ℂ s).left_inv (mem_chart_source ℂ s)
  have hlaw := s26u_law hq' s x hst (by rw [hss]; exact hwx)
  have hT : chartTransition x s (chartAt ℂ s s) = chartAt ℂ x s := by
    show chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s s)) = chartAt ℂ x s
    rw [hss]
  rw [hT] at hlaw
  have hTd : DifferentiableAt ℂ (chartTransition x s) (chartAt ℂ s s) :=
    s23_transition_differentiableAt x s hst (by rw [hss]; exact hwx)
  have hgd : DifferentiableAt ℂ (fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) w :=
    utm_x1_T_differentiableAt hc s y hw (mem_chart_source ℂ s)
  have hcont : ContinuousAt (fun v => c.symm ((chartAt ℂ y).symm v)) w :=
    c.symm.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hw)
  have hev : (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v))) =ᶠ[𝓝 w]
      chartTransition x s ∘ fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v)) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s))]
      with v hv
    show chartAt ℂ x (c.symm ((chartAt ℂ y).symm v)) =
      chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))))
    rw [(chartAt ℂ s).left_inv hv]
  have hder : deriv (fun v => chartAt ℂ x (c.symm ((chartAt ℂ y).symm v))) w =
      deriv (chartTransition x s) (chartAt ℂ s s) *
        deriv (fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) w := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp w hgd.hasDerivAt).deriv
  rw [hder, hlaw]
  ring

/-- The transport `c_* q'` of a holomorphic quadratic differential by a biholomorphic `c` is a holomorphic quadratic
differential: `0` off the chart targets by definition, the transformation law and holomorphy from the local form
`utm_x1_pushQD_local` (with the chart at `s = c⁻¹(φ_y⁻¹ w)`). -/
theorem utm_x1_pushQD_isHolQuadDiff {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : IsBiholomorphic c) {q' : S₁ → ℂ → ℂ} (hq' : IsHolQuadDiff q') :
    IsHolQuadDiff (utm_x1_pushQD c q') := by
  have hq'' : IsDiffFamily 2 0 q' ∧ ∀ x : S₁, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hq'
  have key : IsDiffFamily 2 0 (utm_x1_pushQD c q') ∧
      ∀ y : S₂, DifferentiableOn ℂ (utm_x1_pushQD c q' y) (chartAt ℂ y).target := by
    refine ⟨⟨fun y w hw => ?_, fun y y' w hw hwy => ?_⟩, fun y w hw => ?_⟩
    · show (chartAt ℂ y).target.indicator _ w = 0
      rw [indicator_of_notMem hw]
    · rw [zpow_zero, mul_one, zpow_two]
      obtain ⟨hτt, -, hτeq⟩ := s23_transition_mem hw hwy
      have hsx : c.symm ((chartAt ℂ y).symm (chartTransition y y' w)) = c.symm ((chartAt ℂ y').symm w) := by
        rw [hτeq]
      have hsrc : c.symm ((chartAt ℂ y).symm (chartTransition y y' w)) ∈
          (chartAt ℂ (c.symm ((chartAt ℂ y').symm w))).source := by
        rw [hsx]
        exact mem_chart_source ℂ _
      rw [utm_x1_pushQD_local hc hq' y' (c.symm ((chartAt ℂ y').symm w)) hw (mem_chart_source ℂ _),
        utm_x1_pushQD_local hc hq' y (c.symm ((chartAt ℂ y').symm w)) hτt hsrc]
      have hτd := (s23_transition y y' hw hwy).1
      have hTd := utm_x1_T_differentiableAt hc (c.symm ((chartAt ℂ y').symm w)) y hτt hsrc
      have hev : (fun v => chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y').symm v))) =ᶠ[𝓝 w]
          (fun v => chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y).symm v))) ∘
            chartTransition y y' := by
        filter_upwards [((chartAt ℂ y').isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds ⟨hw, hwy⟩]
          with v hv
        show chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y').symm v)) =
          chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ y').symm v))))
        rw [(chartAt ℂ y).left_inv hv.2]
      have hder : deriv (fun v => chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y').symm v))) w =
          deriv (fun v => chartAt ℂ (c.symm ((chartAt ℂ y').symm w)) (c.symm ((chartAt ℂ y).symm v)))
            (chartTransition y y' w) * deriv (chartTransition y y') w := by
        rw [hev.deriv_eq]
        exact (hTd.hasDerivAt.comp w hτd.hasDerivAt).deriv
      rw [hder, hsx]
      ring
    · set s := c.symm ((chartAt ℂ y).symm w) with hs
      obtain ⟨hWo, hTd, -⟩ := utm_x1_T_on hc s y
      have hwW : w ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ s).source) :=
        ⟨hw, mem_chart_source ℂ s⟩
      have hdd := hTd.deriv hWo
      have hmem : chartAt ℂ s (c.symm ((chartAt ℂ y).symm w)) ∈ (chartAt ℂ s).target :=
        (chartAt ℂ s).map_source (mem_chart_source ℂ s)
      have h1 : DifferentiableAt ℂ (q' s) (chartAt ℂ s (c.symm ((chartAt ℂ y).symm w))) :=
        (hq''.2 s).differentiableAt ((chartAt ℂ s).open_target.mem_nhds hmem)
      have hF : DifferentiableAt ℂ (fun v => q' s (chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) *
          deriv (fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) v ^ 2) w :=
        (h1.comp w ((hTd w hwW).differentiableAt (hWo.mem_nhds hwW))).mul
          ((hdd.differentiableAt (hWo.mem_nhds hwW)).pow 2)
      have heq : utm_x1_pushQD c q' y =ᶠ[𝓝 w] fun v => q' s (chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) *
          deriv (fun v => chartAt ℂ s (c.symm ((chartAt ℂ y).symm v))) v ^ 2 :=
        Filter.eventuallyEq_of_mem (hWo.mem_nhds hwW) fun v hv => utm_x1_pushQD_local hc hq' y s hv.1 hv.2
      exact (hF.congr_of_eventuallyEq heq).differentiableWithinAt
  exact key

/-- **The transfer map at the centre.**  For `x ∈ S₁` and `y = c x`, `T = φ_x ∘ c⁻¹ ∘ φ_y⁻¹` is analytic at
`φ_y(y)` with `T' ≠ 0` there and `T(φ_y(y)) = φ_x(x)`, and near `φ_y(y)` it is holomorphic with
`(c_* q')_y = q'_x(T) T'²`. -/
theorem utm_x1_T_center {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : IsBiholomorphic c) {q' : S₁ → ℂ → ℂ} (hq' : IsHolQuadDiff q')
    (x : S₁) :
    AnalyticAt ℂ (fun v => chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm v))) (chartAt ℂ (c x) (c x)) ∧
      deriv (fun v => chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm v))) (chartAt ℂ (c x) (c x)) ≠ 0 ∧
      chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm (chartAt ℂ (c x) (c x)))) = chartAt ℂ x x ∧
      ∀ᶠ v in 𝓝 (chartAt ℂ (c x) (c x)),
        DifferentiableAt ℂ (fun v => chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm v))) v ∧
        utm_x1_pushQD c q' (c x) v = q' x (chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm v))) *
          deriv (fun v => chartAt ℂ x (c.symm ((chartAt ℂ (c x)).symm v))) v ^ 2 := by
  have hys : (chartAt ℂ (c x)).symm (chartAt ℂ (c x) (c x)) = c x := (chartAt ℂ (c x)).left_inv (mem_chart_source ℂ _)
  have hyW : chartAt ℂ (c x) (c x) ∈
      (chartAt ℂ (c x)).target ∩ (chartAt ℂ (c x)).symm ⁻¹' (c.symm ⁻¹' (chartAt ℂ x).source) := by
    refine ⟨(chartAt ℂ (c x)).map_source (mem_chart_source ℂ _), ?_⟩
    show c.symm ((chartAt ℂ (c x)).symm (chartAt ℂ (c x) (c x))) ∈ (chartAt ℂ x).source
    rw [hys, c.symm_apply_apply]
    exact mem_chart_source ℂ x
  obtain ⟨hWo, hTd, hTd0⟩ := utm_x1_T_on hc x (c x)
  refine ⟨hTd.analyticAt (hWo.mem_nhds hyW), hTd0 _ hyW, by rw [hys, c.symm_apply_apply], ?_⟩
  filter_upwards [hWo.mem_nhds hyW] with v hv
  exact ⟨hTd.differentiableAt (hWo.mem_nhds hv), utm_x1_pushQD_local hc hq' (c x) x hv.1 hv.2⟩

/-- [S-ii, stub] **A Teichmüller map followed by a conformal map is a Teichmüller map**, with the same initial
differential `q` and `k`, and terminal differential the transport of `q'` (the pull-back of `q'` by `c⁻¹`).

*Truth:* put `q''_y(w) = q'_x(T w) T'(w)²` on the chart target at `y`, `x = c⁻¹ y`, `T = φ_x ∘ c⁻¹ ∘ φ_y⁻¹`
(holomorphic, `T' ≠ 0`), and `0` elsewhere: a holomorphic quadratic differential on `S₂`.  `f.trans c` is q.c.
(`c` is `1`-q.c., `isKQCRS_one_iff`, `eq23_4`); regular points and zero orders are preserved by `c`; a natural parameter
`ζ'` of `q'` at `f p` gives the natural parameter `ζ' ∘ T` of `q''` at `c (f p)`, and
`(ζ' ∘ T)(localMapExpr (f.trans c) p z) = ζ'(localMapExpr f p z) = teichStretch k (ζ z)` near `φ_p(p)`.

*Route/reuse:* S26 `IsTeichmullerMap` (l.2440), `IsNaturalParameterAt` (l.929), `IsZeroOfOrder` (l.923); S23
`isKQCRS_one_iff` (l.716), `eq23_4` (l.649), `s23_transition` (l.105); S29 `s29_m_maxDil_conj_biholo` (l.216).
*Estimate:* 0.3–0.5k.

*Walls:* none: a local computation with the given maps (no W-UC, W-QC, W-TOP, W-RR, W-IoD). -/
theorem utm_x_teichmullerMap_trans [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {S₂ : Type*} [TopologicalSpace S₂]
    [ChartedSpace ℂ S₂] [T2Space S₂] [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂] {f : S₀ ≃ₜ S₁}
    {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) {c : S₁ ≃ₜ S₂}
    (hc : IsBiholomorphic c) : ∃ q'' : S₂ → ℂ → ℂ, IsTeichmullerMap (f.trans c) q q'' k := by
  obtain ⟨K, hK⟩ := hf.qc
  refine ⟨utm_x1_pushQD c q', ⟨_, (eq23_4 hK ((isKQCRS_one_iff c).2 hc)).1⟩, hf.initial, hf.initial_ne,
    utm_x1_pushQD_isHolQuadDiff hc hf.terminal, hf.k_nonneg, hf.k_lt_one, fun p hp => ?_, fun p n hn => ?_⟩
  · obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hf.regular p hp
    obtain ⟨hTan, hTd0, hT0, hTev⟩ := utm_x1_T_center hc hf.terminal (f p)
    obtain ⟨hζ'a, hζ'0, hζ'd, hζ'ev⟩ := hζ'
    have hTc : Tendsto (fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v)))
        (𝓝 (chartAt ℂ (c (f p)) (c (f p)))) (𝓝 (chartAt ℂ (f p) (f p))) := by
      have h := hTan.continuousAt.tendsto
      rwa [hT0] at h
    have hζ'an : AnalyticAt ℂ ζ'
        (chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm (chartAt ℂ (c (f p)) (c (f p)))))) := by
      rw [hT0]
      exact hζ'a
    have hnat : IsNaturalParameterAt (utm_x1_pushQD c q') (c (f p))
        (ζ' ∘ fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) := by
      refine ⟨hζ'a.comp_of_eq hTan hT0, by simp only [Function.comp_apply, hT0, hζ'0], ?_, ?_⟩
      · rw [deriv_comp (h := fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) _
          hζ'an.differentiableAt hTan.differentiableAt, hT0]
        exact mul_ne_zero hζ'd hTd0
      · filter_upwards [hTc.eventually hζ'ev, hTc.eventually hζ'a.eventually_analyticAt, hTev]
          with v h1 h2 h3
        rw [deriv_comp (h := fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) v
          h2.differentiableAt h3.1, mul_pow, h1, h3.2]
    refine ⟨?_, ζ, _, hζ, hnat, ?_⟩
    · show utm_x1_pushQD c q' (c (f p)) (chartAt ℂ (c (f p)) (c (f p))) ≠ 0
      rw [← hnat.2.2.2.self_of_nhds]
      exact pow_ne_zero 2 hnat.2.2.1
    · have hD := (s23_localMapDomain_isOpen (f.trans c).continuous p).mem_nhds (s23_h_center (f.trans c) p).1
      filter_upwards [hrel, hD] with z hz hzD
      show ζ' (chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm
        (chartAt ℂ (c (f p)) (c (f ((chartAt ℂ p).symm z))))))) = teichStretch k (ζ z)
      have h2 : c (f ((chartAt ℂ p).symm z)) ∈ (chartAt ℂ (c (f p))).source := hzD.2
      rw [(chartAt ℂ (c (f p))).left_inv h2, c.symm_apply_apply]
      exact hz
  · have h1 : meromorphicOrderAt (q' (f p)) (chartAt ℂ (f p) (f p)) = (n : ℤ) := hf.zero p n hn
    obtain ⟨hTan, hTd0, hT0, hTev⟩ := utm_x1_T_center hc hf.terminal (f p)
    show meromorphicOrderAt (utm_x1_pushQD c q' (c (f p))) (chartAt ℂ (c (f p)) (c (f p))) = (n : ℤ)
    have hev : utm_x1_pushQD c q' (c (f p)) =ᶠ[𝓝[≠] chartAt ℂ (c (f p)) (c (f p))]
        (fun v => deriv (fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) v ^ 2) *
          (q' (f p) ∘ fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) := by
      filter_upwards [nhdsWithin_le_nhds hTev] with v hv
      rw [hv.2, Pi.mul_apply, Function.comp_apply, mul_comm]
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_mul_of_ne_zero
      (g := fun v => deriv (fun v => chartAt ℂ (f p) (c.symm ((chartAt ℂ (c (f p))).symm v))) v ^ 2)
      (hTan.deriv.pow 2) (pow_ne_zero 2 hTd0), meromorphicOrderAt_comp_of_deriv_ne_zero hTan hTd0]
    exact (congrArg (meromorphicOrderAt (q' (f p))) hT0).trans h1

/-! ### Proved glue -/

/-- The lifted coefficient of the base point `[S₀, id]` is `0`: `φ_x ∘ p̂` is holomorphic. -/
theorem utm_x_liftCoeff_base [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : utm_x_liftCoeff p₀ (utm_x_base S₀) (fun _ => 0) := by
  unfold utm_x_liftCoeff
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with τ hτ
  have hd := utm_a_differentiableAt hp₀.2.1 (utm_pext p₀ τ) (w := τ) hτ (mem_chart_source ℂ _)
  have hb : dzbar (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) τ = 0 := (cauchyRiemann_iff.1 hd).2
  show (0 : ℂ) = dzbar (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) τ /
    dz (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) τ
  rw [hb, zero_div]

/-- **Uniformization transport (UT)**, from [S2a]: `D = f ∘ p₀ ∘ F⁻¹` uniformizes `m.X` with group
`b33_d_conjGroup Γ₀ F`, where `F` is the self-map of `ℍ` induced by `f^μ` (a covering: `p₀` composed with two
homeomorphisms; fibres: `F γ F⁻¹` is the Möbius map of `b33_d_def`). -/
theorem utm_x_transport [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {m : MarkedRS S₀} {μ : BeltramiGamma Γ₀} (hμ : utm_x_liftCoeff p₀ m μ.1.1) :
    ∃ (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (D : UpperHalfPlane → m.X.carrier),
      (∀ τ : UpperHalfPlane, (F τ : ℂ) = fMuSym μ.1.1 τ) ∧ (∀ τ, D (F τ) = m.marking (p₀ τ)) ∧
      IsUniformization (b33_d_conjGroup Γ₀ F) D := by
  obtain ⟨k, hk0, hk1, hμk⟩ := bg_beltramiH_upper μ.1
  obtain ⟨-, hN, hK, -⟩ := bg_sym_spec hk0 hk1 hμk
  obtain ⟨hU, -⟩ := fMuSym_upperHalf hk0 hk1 hμk
  obtain ⟨F, hF⟩ := b33_d_homeo_upper hK hN.2.1 hU
  refine ⟨F, fun w => m.marking (p₀ (F.symm w)), hF, fun τ => by simp, ?_, ?_, ?_, ?_⟩
  · exact (hp₀.1.comp_homeomorph F.symm).homeomorph_comp m.marking
  · exact utm_x_transport_mdifferentiable hp₀ hμ hF
  · intro y
    obtain ⟨τ, hτ⟩ := hp₀.2.2.1 (m.marking.symm y)
    exact ⟨F τ, by simp [hτ]⟩
  · intro w₁ w₂
    constructor
    · intro h
      have h' : p₀ (F.symm w₁) = p₀ (F.symm w₂) := m.marking.injective h
      obtain ⟨γ, hγ, hγw⟩ := (hp₀.2.2.2 _ _).1 h'
      obtain ⟨γ', hγ'⟩ := b33_d_def μ hγ
      have hrel := (b33_d_rel_iff hF γ γ').1 hγ'
      refine ⟨γ', ⟨γ, hγ, hrel⟩, ?_⟩
      have h1 := hrel (F.symm w₁)
      rw [hγw, F.apply_symm_apply, F.apply_symm_apply] at h1
      exact h1.symm
    · rintro ⟨γ', ⟨γ, hγ, hrel⟩, hγ'w⟩
      show m.marking (p₀ (F.symm w₁)) = m.marking (p₀ (F.symm w₂))
      congr 1
      refine (hp₀.2.2.2 _ _).2 ⟨γ, hγ, ?_⟩
      have h1 := hrel (F.symm w₁)
      rw [F.apply_symm_apply, hγ'w] at h1
      rw [← h1, F.symm_apply_apply]

/-- **The bridge [S2]** (UT on both sides, then [S2b]): lifted coefficients with equal boundary values of `f^μ` give
the same point of `T(S₀)`. -/
theorem utm_x_bridge [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {m₁ m₂ : MarkedRS S₀} {μ₁ μ₂ : BeltramiGamma Γ₀}
    (h₁ : utm_x_liftCoeff p₀ m₁ μ₁.1.1) (h₂ : utm_x_liftCoeff p₀ m₂ μ₂.1.1) (h12 : teichSetoidGamma Γ₀ μ₁ μ₂) :
    (Quot.mk _ m₁ : TeichSpace S₀) = Quot.mk _ m₂ := by
  obtain ⟨F₁, D₁, hF₁, hD₁, hU₁⟩ := utm_x_transport hp₀ h₁
  obtain ⟨F₂, D₂, hF₂, hD₂, hU₂⟩ := utm_x_transport hp₀ h₂
  exact Quot.sound (utm_x_equiv_of_boundary hg hS hp₀ hF₁ hF₂ hD₁ hD₂ hU₁ hU₂ h12)

/-- **`hfin` of `thm36_2_finite_type`** from `dim Q(S₀) < ∞` and the descent [S4]: the restrictions `𝟙_ℍ φ` of the
integrable automorphic forms lie in the range of the lift `utm_x_liftL` of the finite dimensional `Q(S₀)`. -/
theorem utm_x_hfin [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (hQ : Module.Finite ℂ (holQuadDiffSubmodule S₀)) (F : Set ℂ) :
    Module.Finite ℂ (Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ₀ F)) := by
  have hle : Submodule.span ℂ ((fun φ => upperHalf.indicator φ) '' integrableAutomorphicQD Γ₀ F) ≤
      LinearMap.range (utm_x_liftL p₀) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨hφd, -, hφΓ⟩ := hφ
    obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp₀ hφd hφΓ
    exact ⟨⟨q, hq⟩, Set.indicator_congr fun τ hτ => hqφ τ hτ⟩
  exact Submodule.finiteDimensional_of_le hle

/-- **The existence core** (the S36 route): every point of `T(S₀)` is `[S₀, id]` up to a conformal change of the
marking, or a Teichmüller deformation `S_{q,k}` with `q ≠ 0`, `0 < k < 1`.  The extremal representative `μ₀` of the
lifted coefficient (`exists_extremal_mod_boundary`) is `0` or `k φ̄/|φ|` (`thm36_2_finite_type`); `φ` descends to `q`
([S4]); the deformation `S_{q,k}` has the lifted coefficient `k ψ̄/|ψ| = μ₀` ([S3]); [S2] identifies the classes. -/
theorem utm_x_existence_core [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (hQ : Module.Finite ℂ (holQuadDiffSubmodule S₀)) (p : TeichSpace S₀) :
    (∃ m : MarkedRS S₀, p = Quot.mk _ m ∧ IsBiholomorphic m.marking) ∨
      ∃ (q : S₀ → ℂ → ℂ) (k : ℝ), IsHolQuadDiff q ∧ q ≠ 0 ∧ 0 < k ∧ k < 1 ∧ IsDeformationPoint q k p := by
  obtain ⟨m, rfl⟩ := Quot.exists_rep p
  obtain ⟨μ, hμ⟩ := utm_x_exists_liftCoeff hp₀ m
  have hΓ := utm_x_isFuchsian hp₀
  obtain ⟨μ₀, hμ₀μ, hext⟩ := exists_extremal_mod_boundary hΓ μ
  have hμμ₀ : teichSetoidGamma Γ₀ μ μ₀ := fun x => (hμ₀μ x).symm
  -- the case `μ₀ = 0`: `[m] = [S₀, id]`
  have hcase0 : (μ₀.1.1 =ᵐ[volume.restrict upperHalf] 0) →
      (∃ m' : MarkedRS S₀, (Quot.mk _ m : TeichSpace S₀) = Quot.mk _ m' ∧ IsBiholomorphic m'.marking) := by
    intro h0
    have hb : utm_x_liftCoeff p₀ (utm_x_base S₀) μ₀.1.1 := by
      have hb0 := utm_x_liftCoeff_base hp₀
      unfold utm_x_liftCoeff at hb0 ⊢
      filter_upwards [hb0, h0] with τ h1 h2
      rw [h2]
      exact h1
    exact ⟨utm_x_base S₀, utm_x_bridge hg hS hp₀ hμ hb hμμ₀, isBiholomorphic_id⟩
  set k := beltramiNormH μ₀.1.1 with hkdef
  by_cases hk0 : k = 0
  · refine Or.inl (hcase0 ?_)
    filter_upwards [c36_c_ae_le_normH μ₀.1] with z hz
    rw [← hkdef, hk0] at hz
    exact norm_le_zero_iff.1 hz
  have hkpos : 0 < k := lt_of_le_of_ne (beltramiNormH_nonneg _) (Ne.symm hk0)
  have hk1 : k < 1 := beltramiNormH_lt_one μ₀.1
  obtain ⟨F, hF⟩ := utm_x_exists_fundamentalDomain hp₀
  rcases thm36_2_finite_type hΓ (s27g_actsFreely hp₀) hF (utm_x_hfin hp₀ hQ F) μ₀ hext with
    h0 | ⟨φ, hφA, hφ1, _hφpair, hφμ⟩
  · exact Or.inl (hcase0 h0)
  -- the Teichmüller case: `μ₀ = k φ̄/|φ|`, `φ` the lift of `q`
  obtain ⟨hφd, -, hφΓ⟩ := hφA
  obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp₀ hφd hφΓ
  have hq0 : q ≠ 0 := by
    rintro rfl
    have hφ0 : ∀ τ ∈ upperHalf, φ τ = 0 := fun τ hτ => by
      rw [← hqφ τ hτ, show (0 : S₀ → ℂ → ℂ) = (0 : ℂ) • (0 : S₀ → ℂ → ℂ) by simp, utm_x_liftQD_smul, zero_mul]
    have h0 : phiArea φ F = 0 := by
      unfold phiArea
      rw [setLIntegral_congr_fun hF.2.1 (fun z hz => by rw [hφ0 z (hF.1 hz), norm_zero, ENNReal.ofReal_zero]),
        lintegral_zero]
    rw [h0] at hφ1
    exact zero_ne_one hφ1
  obtain ⟨X, e', q'', hT⟩ := exists_teichDeformation hq hq0 hkpos.le hk1
  have hTM := teichDeformation_isTeichmullerMap hT
  have hlift := utm_x_liftCoeff_teichmullerMap hp₀ hTM
  have hlift' : utm_x_liftCoeff p₀ ⟨X, e', hTM.qc⟩ μ₀.1.1 := by
    unfold utm_x_liftCoeff at hlift ⊢
    filter_upwards [hlift, hφμ, ae_restrict_mem isOpen_upperHalf.measurableSet] with τ h1 h2 hτ
    rw [h2, ← h1, utm_x_tcoeff, hqφ τ hτ]
  have heq := utm_x_bridge hg hS hp₀ hlift' hμ hμ₀μ
  exact Or.inr ⟨q, k, hq, hq0, hkpos, hk1, X, e', hTM.qc, q'', hT, heq.symm⟩

/-- A deformation point of `(q, k)` is one of `(r q, k)` for `r > 0` (`S_{rq,k} = S_{q,k}`, `teichDeformation_smul`). -/
theorem utm_x_isDeformationPoint_smul {q : S₀ → ℂ → ℂ} {k : ℝ} {p : TeichSpace S₀} (h : IsDeformationPoint q k p)
    {r : ℝ} (hr : 0 < r) : IsDeformationPoint ((r : ℂ) • q) k p := by
  obtain ⟨X, e, hqc, q', hT, hp⟩ := h
  exact ⟨X, e, hqc, (r : ℂ) • q', teichDeformation_smul hT hr, hp⟩

/-- A real linear isomorphism `Q(S₀) ≃ ℝⁿ` makes `Q(S₀)` finite dimensional over `ℂ`. -/
theorem utm_x_finite_of_equiv {n : ℕ}
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Module.Finite ℂ (holQuadDiffSubmodule S₀) := by
  have h1 : Module.Finite ℝ ((holQuadDiffSubmodule S₀).restrictScalars ℝ) := Module.Finite.equiv e.symm
  have h2 : Module.Finite ℂ ((holQuadDiffSubmodule S₀).restrictScalars ℝ) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
  exact Module.Finite.equiv (Submodule.restrictScalarsEquiv ℝ ℂ (S₀ → ℂ → ℂ) (holQuadDiffSubmodule S₀))

/-- **(iv) The conformal case.**  A biholomorphic `c : S₀ → S₁` is extremal in its homotopy class, and the unique
extremal map there (`K[c] = 1`; an extremal `h ≃ c` has `K[h] = 1`, so `conformal_unique_extremal_of_uniformization`
applies on `S₀ = ℍ/Γ₀`). -/
theorem utm_x_biholomorphic_extremal [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {c : S₀ ≃ₜ S₁} (hc : IsBiholomorphic c)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) :
    IsExtremalInHomotopyClass c ∧ ∀ h : S₀ ≃ₜ S₁, IsExtremalInHomotopyClass h →
      ContinuousMap.Homotopic (c : C(S₀, S₁)) (h : C(S₀, S₁)) → ⇑h = ⇑c := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have hc1 : IsKQCRS c 1 := (isKQCRS_one_iff c).2 hc
  have hcle : maxDilatationRS c ≤ 1 := by simpa using maxDilatationRS_le hc1
  refine ⟨⟨⟨1, hc1⟩, fun g' hg' _ => hcle.trans (s29_m_one_le_maxDilatationRS hg')⟩, fun h hh hch => ?_⟩
  have hle : maxDilatationRS h ≤ maxDilatationRS c := hh.2 c ⟨1, hc1⟩ hch.symm
  have h1 : maxDilatationRS h = 1 := le_antisymm (hle.trans hcle) (s29_m_one_le_maxDilatationRS hh.1)
  exact conformal_unique_extremal_of_uniformization hg h₀ h₁ hc hh.1 hch h1 hp₀

/-- **(iii) The marked surface `(S, f)`.**  `[S, f] = [m]` in `T(S₀)` gives a biholomorphic `c : S → m.X` with
`c ∘ f ≃ m.marking` (the carrier of `utm_x_marked f hf` is `S`). -/
theorem utm_x_marked_equiv {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [CompactSpace S] [IsManifold 𝓘(ℂ) ω S] {f : S₀ ≃ₜ S} {hf : IsQCRS f} {m : MarkedRS S₀}
    (h : (Quot.mk _ (utm_x_marked f hf) : TeichSpace S₀) = Quot.mk _ m) :
    ∃ c : S ≃ₜ m.X.carrier, IsBiholomorphic c ∧
      ContinuousMap.Homotopic ((f.trans c : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)) (m.marking : C(S₀, m.X.carrier)) :=
  s29_m_equiv_of_eq h

/-! ### The companions -/

/-- **Companion of `lemma27_1_injective`** (Lemma 27.1, (27.15), injectivity of `Φ`) for a surface given as `ℍ/Γ₀`:
two Teichmüller deformations `S_{q₁,k₁}`, `S_{q₂,k₂}` (`‖e qᵢ‖ = 1`, `0 < kᵢ < 1`) representing the same point of
`T(S₀)` have `k₁ = k₂` and `q₁ = q₂`.  The inverse trick (`utm_x_dil_le_of_equiv`, both ways) gives `k₁ = k₂` and
`e₂ = c ∘ e₁`; then `q₂ = r q₁` with `r > 0` ([S7b]), and `‖e qᵢ‖ = 1` forces `r = 1` (S27's
`s27w_injective_core`).

*Derivation note:* the book statement `lemma27_1_injective` follows from this companion plus `thm22_3_classification`
(a Fuchsian uniformization of the closed surface `S₀` of genus `g > 1`). -/
theorem lemma27_1_injective_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {q₁ q₂ : (holQuadDiffSubmodule S₀).restrictScalars ℝ} (hq₁ : ‖e q₁‖ = 1) (hq₂ : ‖e q₂‖ = 1)
    {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₁' : k₁ < 1) (hk₂ : 0 < k₂) (hk₂' : k₂ < 1) {p : TeichSpace S₀}
    (h₁ : IsDeformationPoint q₁ k₁ p) (h₂ : IsDeformationPoint q₂ k₂ p)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : k₁ = k₂ ∧ q₁ = q₂ := by
  exact s27w_injective_core hg hS e hq₁ hq₂ hk₁ hk₁' hk₂ hk₂' h₁ h₂ hp₀

/-- **Companion of `teichSpace_deformation_bijection`** (§27.2: `Φ : T̃(S₀) → T(S₀)` is a bijection) for a surface
given as `ℍ/Γ₀`: every point of `T(S₀)` is `[S₀, id]` (up to a conformal change of the marking) or `[S_{q,k}, f]` for a
unique `(q, k)` with `‖e q‖ = 1`, `0 < k < 1`.  Existence is `utm_x_existence_core` (Hamilton's theorem, S36) with `q`
normalized by `e`; uniqueness is `lemma27_1_injective_of_uniformization`.

*Derivation note:* the book statement `teichSpace_deformation_bijection` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of the closed surface `S₀` of genus `g > 1`). -/
theorem teichSpace_deformation_bijection_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) :
    ∀ p : TeichSpace S₀, (∃ m : MarkedRS S₀, p = Quot.mk _ m ∧ IsBiholomorphic m.marking) ∨
      ∃! qk : (holQuadDiffSubmodule S₀).restrictScalars ℝ × ℝ,
        ‖e qk.1‖ = 1 ∧ 0 < qk.2 ∧ qk.2 < 1 ∧ IsDeformationPoint qk.1 qk.2 p := by
  have hQ := utm_x_finite_of_equiv e
  intro p
  rcases utm_x_existence_core hg hS hp₀ hQ p with h | ⟨q, k, hq, hq0, hk0, hk1, hdef⟩
  · exact Or.inl h
  set qR : (holQuadDiffSubmodule S₀).restrictScalars ℝ := ⟨q, hq⟩ with hqRdef
  have hqR0 : qR ≠ 0 := fun h => hq0 (congrArg Subtype.val h)
  set c : ℝ := ‖e qR‖ with hcdef
  have hc : 0 < c := norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff e).2 hqR0)
  set q₁ : (holQuadDiffSubmodule S₀).restrictScalars ℝ := c⁻¹ • qR with hq₁def
  have hq₁n : ‖e q₁‖ = 1 := by
    rw [hq₁def, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, ← hcdef, inv_mul_cancel₀ hc.ne']
  have hq₁coe : (q₁ : S₀ → ℂ → ℂ) = ((c⁻¹ : ℝ) : ℂ) • q := by
    rw [hq₁def, Submodule.coe_smul_of_tower]
    funext x z
    simp [qR, Complex.real_smul]
  have hdef₁ : IsDeformationPoint (q₁ : S₀ → ℂ → ℂ) k p := by
    rw [hq₁coe]
    exact utm_x_isDeformationPoint_smul hdef (inv_pos.2 hc)
  refine Or.inr ⟨(q₁, k), ⟨hq₁n, hk0, hk1, hdef₁⟩, fun qk' ⟨h1', h2', h3', h4'⟩ => ?_⟩
  obtain ⟨hk, hqq⟩ := lemma27_1_injective_of_uniformization hg hS e h1' hq₁n h2' h3' hk0 hk1 h4' hdef₁ hp₀
  exact Prod.ext hqq hk

/-- **Companion of Theorem 27.2 (Teichmüller existence), in the quasiconformal variant (user decision 2026-09-26), for
surfaces given as `S₀ = ℍ/Γ₀` and `S = ℍ/Γ₁`.**  For a quasiconformal `f : S₀ → S` there is a Teichmüller map (or a
conformal map) `f₀` homotopic to `f`; it is extremal in its homotopy class, and it is the unique extremal map there.

The book statement `thm27_2_existence` assumes only that `f` preserves orientation; with that hypothesis the class of
`f` contains a quasiconformal map only by §24.2 (`exists_qc_in_homotopy_class`, not yet formalized), so the
quasiconformal variant is the one proved here.

*Derivation note:* the book statement follows from this companion plus `thm22_3_classification` (Fuchsian
uniformizations of `S₀` and `S`) and `exists_qc_in_homotopy_class` (a quasiconformal map in the class of `f`). -/
theorem thm27_2_existence_qc_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (h₀ : HasGenus S₀ g) (h₁ : HasGenus S g)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀)
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S}
    (hp₁ : IsUniformization Γ₁ p₁) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsTeichmullerMap f₀ q q' k) ∧
      IsExtremalInHomotopyClass f₀ ∧
      ∀ h : S₀ ≃ₜ S, IsExtremalInHomotopyClass h → ContinuousMap.Homotopic (f : C(S₀, S)) (h : C(S₀, S)) →
        ⇑h = ⇑f₀ := by
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S := h₁.1
  rcases utm_x_existence_core hg h₀ hp₀ (utm_x_finite_holQuadDiff hp₀) (Quot.mk _ (utm_x_marked f hf)) with
    ⟨m', hm', hbm⟩ | ⟨q, k, -, -, -, -, X, e, hqc, q', hT, hp⟩
  · -- `[S, f] = [S₀, id]` up to a conformal change: `f` is homotopic to a conformal map
    obtain ⟨c, hc, hhom⟩ := utm_x_marked_equiv hm'
    have hff₀ : ContinuousMap.Homotopic (f : C(S₀, S)) ((m'.marking.trans c.symm : S₀ ≃ₜ S) : C(S₀, S)) :=
      (utm_x_homotopic_trans_symm hhom).symm
    have hb0 := IsBiholomorphic.comp hc.homeomorph_symm hbm
    have hb : IsBiholomorphic (m'.marking.trans c.symm : S₀ ≃ₜ S) := hb0
    obtain ⟨hext, huniq⟩ := utm_x_biholomorphic_extremal hg h₀ h₁ hb hp₀
    exact ⟨m'.marking.trans c.symm, hff₀, Or.inl hb, hext, fun h hh hfh => huniq h hh (hff₀.symm.trans hfh)⟩
  · -- `[S, f] = [S_{q,k}, e]`: `f` is homotopic to the Teichmüller map `c⁻¹ ∘ e`
    obtain ⟨c, hc, hhom⟩ := utm_x_marked_equiv hp
    have hff₀ : ContinuousMap.Homotopic (f : C(S₀, S)) ((e.trans c.symm : S₀ ≃ₜ S) : C(S₀, S)) :=
      (utm_x_homotopic_trans_symm hhom).symm
    obtain ⟨q'', hT''⟩ := utm_x_teichmullerMap_trans (teichDeformation_isTeichmullerMap hT) hc.homeomorph_symm
    obtain ⟨hext, huniq⟩ := teichmullerMap_isExtremal_of_uniformization hg h₀ h₁ hT'' hp₁
    exact ⟨e.trans c.symm, hff₀, Or.inr ⟨q, q'', k, hT''⟩, hext, fun h hh hfh => huniq h hh (hff₀.symm.trans hfh)⟩

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §29.1: the infimum is attained at a Teichmüller map (or a conformal map): there is a Teichmüller
map `f₀ : S₁ → S₂` with `f₀ ≃ f₂ ∘ f₁⁻¹` and `d_T(τ₁, τ₂) = ½ ln K[f₀]`; the value does not depend on
the representatives `(Sⱼ, fⱼ)`. -/
theorem teichDistance_attained {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (m₁ m₂ : MarkedRS S₀) :
    ∃ f : m₁.X.carrier ≃ₜ m₂.X.carrier, IsExtremalInHomotopyClass f ∧
      (IsBiholomorphic f ∨ ∃ (q : m₁.X.carrier → ℂ → ℂ) (q' : m₂.X.carrier → ℂ → ℂ) (k : ℝ),
        IsTeichmullerMap f q q' k) ∧
      ContinuousMap.Homotopic ((m₁.marking.trans f : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
      teichDistance (Quot.mk _ m₁) (Quot.mk _ m₂) = (1 / 2) * Real.log (maxDilatationRS f).toReal := by
  classical
  have hX₁ : HasGenus m₁.X.carrier g := hasGenus_of_homeomorph hS m₁.marking
  have hX₂ : HasGenus m₂.X.carrier g := hasGenus_of_homeomorph hS m₂.marking
  letI : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg hX₁
  obtain ⟨Γ₂, p₂, -, -, hp₂⟩ := s22hg_exists_fuchsian_uniformization hg hX₂
  let F : m₁.X.carrier ≃ₜ m₂.X.carrier := m₁.marking.symm.trans m₂.marking
  -- The markings are already q.c.; no arbitrary-homeomorphism smoothing is needed.
  have hFqc : IsQCRS F := by
    obtain ⟨K₁, hK₁⟩ := m₁.qc
    obtain ⟨K₂, hK₂⟩ := m₂.qc
    exact ⟨_, (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1⟩
  obtain ⟨f₀, hFf₀, hshape, hext, -⟩ :=
    thm27_2_existence_qc_of_uniformization hg hX₁ hX₂ F hFqc hp₁ hp₂
  have hMF : ((m₁.marking.trans F : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier)) =
      (m₂.marking : C(S₀, m₂.X.carrier)) := by
    ext x
    change m₂.marking (m₁.marking.symm (m₁.marking x)) = m₂.marking x
    rw [m₁.marking.symm_apply_apply]
  have hmark : ContinuousMap.Homotopic
      ((m₁.marking.trans f₀ : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
      (m₂.marking : C(S₀, m₂.X.carrier)) := by
    have h2 := hFf₀.symm.comp
      (ContinuousMap.Homotopic.refl (m₁.marking : C(S₀, m₁.X.carrier)))
    rw [← coe_homeomorph_trans, ← coe_homeomorph_trans, hMF] at h2
    exact h2
  -- Cancel the marking on the source to compare homotopy classes of maps.
  have hcomp : ∀ G : m₁.X.carrier ≃ₜ m₂.X.carrier,
      ContinuousMap.Homotopic
        ((m₁.marking.trans G : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) →
      ContinuousMap.Homotopic (f₀ : C(m₁.X.carrier, m₂.X.carrier))
        (G : C(m₁.X.carrier, m₂.X.carrier)) := by
    intro G hG
    have h1 := hG.comp
      (ContinuousMap.Homotopic.refl (m₁.marking.symm : C(m₁.X.carrier, S₀)))
    have e1 : ((m₁.marking.trans G : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier)).comp
        (m₁.marking.symm : C(m₁.X.carrier, S₀)) = (G : C(m₁.X.carrier, m₂.X.carrier)) := by
      ext x
      change G (m₁.marking (m₁.marking.symm x)) = G x
      rw [m₁.marking.apply_symm_apply]
    have e2 : (m₂.marking : C(S₀, m₂.X.carrier)).comp
        (m₁.marking.symm : C(m₁.X.carrier, S₀)) = (F : C(m₁.X.carrier, m₂.X.carrier)) := by
      rfl
    rw [e1, e2] at h1
    exact hFf₀.symm.trans h1.symm
  refine ⟨f₀, hext, hshape, hmark, ?_⟩
  have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS f₀).toReal ∈
      s29_m_teichSet (Quot.mk _ m₁) (Quot.mk _ m₂) :=
    ⟨m₁, m₂, f₀, rfl, rfl, hext.1, hmark, rfl⟩
  -- Membership excludes the empty-set branch of the real sInf.
  change sInf (s29_m_teichSet (Quot.mk _ m₁) (Quot.mk _ m₂)) =
    (1 / 2 : ℝ) * Real.log (maxDilatationRS f₀).toReal
  apply le_antisymm
  · exact csInf_le (s29_m_teichSet_bddBelow _ _) hmem
  · apply le_csInf ⟨_, hmem⟩
    rintro d ⟨n₁, n₂, G, hn₁, hn₂, hG, hGHom, rfl⟩
    -- Transport every representative pair, rather than restricting the infimum.
    obtain ⟨G', hG', hle, hhom⟩ :=
      s29_m_transport (s29_m_equiv_of_eq hn₁) (s29_m_equiv_of_eq hn₂) hG hGHom
    have hmin : maxDilatationRS f₀ ≤ maxDilatationRS G' :=
      hext.2 G' hG' (hcomp G' hhom)
    exact (s29_m_half_log_mono hext.1 hG' hmin).trans
      (s29_m_half_log_mono hG' hG hle)

end

/-! ## Part 6. Companions of the §29/§30 statements for `S₀ = ℍ/Γ₀` (s30t, coordinator 553e2d)

`teichDistance_eq_of_eq_zero`, `hurwitz_finite`, `modAction_properly_discontinuous`, `thm30_3` and
`thm30_4_hausdorff` as companions `<name>_of_uniformization` (book statement + the section instances made explicit
+ only the uniformization data of `S₀`).  Key lemma: `K₀`-q.c. maps between `ℍ/Γ` surfaces fall into finitely many
homotopy classes (normal families of normalized lifts, finitely many deck actions on generators). -/

/-- If `K ≤ e^{2ε}` for every `ε > 0` (and `K ≠ ⊤`), then `K ≤ 1`.  (Scout B's `h30b_le_one_of_forall_exp`.) -/
theorem utm_y_le_one_of_forall_exp {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ ε > 0, K ≤ ENNReal.ofReal (Real.exp (2 * ε))) : K ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < K.toReal := by
    have := ENNReal.toReal_strict_mono hK hlt
    simpa using this
  set ε : ℝ := Real.log K.toReal / 4 with hε
  have hε0 : 0 < ε := by
    have := Real.log_pos h1
    rw [hε]
    positivity
  have h2 := h ε hε0
  have h3 : K.toReal ≤ Real.exp (2 * ε) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have h4 : Real.exp (2 * ε) < K.toReal := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < K.toReal)]
    apply Real.exp_lt_exp.2
    have := Real.log_pos h1
    rw [hε]
    linarith
  linarith

/-- **Companion of `teichDistance_eq_of_eq_zero`** (§29.1, the third metric axiom) for `S₀ = ℍ/Γ₀`:
`d_T(τ₁, τ₂) = 0` only if `τ₁ = τ₂`.  Every marked surface of `S₀` is uniformized by transport
(`s27u_exists_uniformization`); a Teichmüller map realizing the distance up to `ε`
(`thm27_2_existence_qc_of_uniformization`) has `K → 1`, and Theorem 26.2 for `ℍ/Γ` makes the classes equal.

*Derivation note:* the book statement `teichDistance_eq_of_eq_zero` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of `S₀`). -/
theorem teichDistance_eq_of_eq_zero_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∀ p q : TeichSpace S₀, teichDistance p q = 0 → p = q := by
  intro p q hpq
  obtain ⟨m₁, rfl⟩ := Quot.exists_rep p
  obtain ⟨m₂, rfl⟩ := Quot.exists_rep q
  -- uniformizations of `m₁.X` and `m₂.X` by transport, and the extremal map `f₀` of the class of `m₂ ∘ m₁⁻¹`
  obtain ⟨Γ₁, p₁, _, _, hp₁, _⟩ := s27u_exists_uniformization hp₀ m₁
  obtain ⟨Γ₂, p₂, _, _, hp₂, _⟩ := s27u_exists_uniformization hp₀ m₂
  have hX₁ : HasGenus m₁.X.carrier g := hasGenus_of_homeomorph hS m₁.marking
  have hX₂ : HasGenus m₂.X.carrier g := hasGenus_of_homeomorph hS m₂.marking
  have : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
  set f : m₁.X.carrier ≃ₜ m₂.X.carrier := m₁.marking.symm.trans m₂.marking with hfdef
  have hf : IsQCRS f := by
    obtain ⟨K₁, hK₁⟩ := m₁.qc
    obtain ⟨K₂, hK₂⟩ := m₂.qc
    exact ⟨_, (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1⟩
  obtain ⟨f₀, hff₀, -, hext, -⟩ := thm27_2_existence_qc_of_uniformization hg hX₁ hX₂ f hf hp₁ hp₂
  -- `f ∘ m₁ = m₂` pointwise
  have hmf : ((m₁.marking.trans f : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier)) =
      (m₂.marking : C(S₀, m₂.X.carrier)) := by
    ext x
    simp [hfdef]
  -- every competitor `G` (with `G ∘ m₁ ≃ m₂`) is homotopic to `f`
  have hcomp : ∀ G : m₁.X.carrier ≃ₜ m₂.X.carrier,
      ContinuousMap.Homotopic ((m₁.marking.trans G : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) →
      ContinuousMap.Homotopic (f : C(m₁.X.carrier, m₂.X.carrier)) (G : C(m₁.X.carrier, m₂.X.carrier)) := by
    intro G hG
    have h1 := hG.comp (ContinuousMap.Homotopic.refl (m₁.marking.symm : C(m₁.X.carrier, S₀)))
    have e1 : ((m₁.marking.trans G : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier)).comp
        (m₁.marking.symm : C(m₁.X.carrier, S₀)) = (G : C(m₁.X.carrier, m₂.X.carrier)) := by
      ext x
      simp
    have e2 : (m₂.marking : C(S₀, m₂.X.carrier)).comp (m₁.marking.symm : C(m₁.X.carrier, S₀)) =
        (f : C(m₁.X.carrier, m₂.X.carrier)) := by
      ext x
      simp [hfdef]
    rw [e1, e2] at h1
    exact h1.symm
  -- `d_T = 0` gives competitors with `K ≤ e^{2ε}` for every `ε > 0`, so `K[f₀] = 1` and `f₀` is conformal
  have hbound : ∀ ε > 0, maxDilatationRS f₀ ≤ ENNReal.ofReal (Real.exp (2 * ε)) := by
    intro ε hε
    obtain ⟨G, hG, hle, hhom⟩ := s30b_small_map m₁ m₂ (hpq.trans_lt hε)
    exact (hext.2 G hG (hff₀.symm.trans (hcomp G hhom))).trans hle
  have h1 : maxDilatationRS f₀ = 1 :=
    le_antisymm (utm_y_le_one_of_forall_exp (s29_m_maxDilatationRS_ne_top hext.1) hbound)
      (s29_m_one_le_maxDilatationRS hext.1)
  have hb : IsBiholomorphic f₀ := (isKQCRS_one_iff f₀).1 (utm_isKQCRS_one_of_maxDil hext.1 h1)
  refine Quot.sound ⟨f₀, hb, ?_⟩
  -- `f₀ ∘ m₁ ≃ f ∘ m₁ = m₂`
  have h2 := hff₀.symm.comp (ContinuousMap.Homotopic.refl (m₁.marking : C(S₀, m₁.X.carrier)))
  rw [← coe_homeomorph_trans, ← coe_homeomorph_trans, hmf] at h2
  exact h2

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §29.1 (the third metric axiom, split off from `teichDistance_metric`): `d_T(τ₁, τ₂) = 0` only if
`τ₁ = τ₂`; the Teichmüller map realizing the distance has `K = 1`, so it is conformal. -/
theorem teichDistance_eq_of_eq_zero {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    ∀ p q : TeichSpace S₀, teichDistance p q = 0 → p = q := by
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact teichDistance_eq_of_eq_zero_of_uniformization (S₀ := S₀) hg hS hp₀

end

/-- **The key lemma KL.**  For closed surfaces `X = ℍ/Γ_X`, `Y = ℍ/Γ_Y` and any `K₀`, every sequence of `K₀`-q.c.
homeomorphisms `Gₙ : X → Y` has two homotopic members.  Normalized lifts `Fₙ` (with `Fₙ(i)` in a fixed compact set),
conjugated to `Δ` by the Cayley map, have a locally uniformly convergent subsequence (Theorem 8.1) whose limit maps `Δ`
into `Δ` (Theorem 8.2, `s30b_limit_mapsTo`), so every `F_{φ n}(τ)` converges in `ℍ`; the deck elements of the lifts
on the finite generating set of `Γ_X` (`s30b_generate`) lie in a finite set, two of them agree (pigeonhole), and
Theorem 23.1 gives the homotopy.  (Scout B's `h30b_kl`.) -/
theorem utm_y_kl {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y]
    [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY) {K₀ : ℝ}
    (G : ℕ → X ≃ₜ Y) (hG : ∀ n, IsKQCRS (G n) K₀) :
    ∃ n n', n ≠ n' ∧ ContinuousMap.Homotopic (G n : C(X, Y)) (G n' : C(X, Y)) := by
  classical
  obtain ⟨KX, hKX, hcovX⟩ := utm_exists_compact_translate hX
  obtain ⟨KY, hKY, hcovY⟩ := utm_exists_compact_translate hY
  -- normalized lifts
  have hlift : ∀ n, ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, IsLift pX pY (G n) F ∧
      F UpperHalfPlane.I ∈ KY := by
    intro n
    obtain ⟨τ₁, hτ₁⟩ := hY.2.2.1 (G n (pX UpperHalfPlane.I))
    obtain ⟨δ, hδ, hδK⟩ := hcovY τ₁
    have hp : pY (δ • τ₁) = G n (pX UpperHalfPlane.I) := by
      rw [← hτ₁]
      exact ((hY.2.2.2 τ₁ (δ • τ₁)).2 ⟨δ, hδ, rfl⟩).symm
    obtain ⟨F, hF, hF0⟩ := exists_lift hX hY (G n) UpperHalfPlane.I (δ • τ₁) hp
    exact ⟨F, hF, hF0 ▸ hδK⟩
  choose F hF hFK using hlift
  have hFqc : ∀ n, IsKQC (liftToC (F n)) upperHalf K₀ := fun n => h23l_lift_isKQC hX hY (hG n) (hF n)
  -- Cayley conjugates and a convergent subsequence
  set Φ : ℕ → ℂ → ℂ := fun n => cayley ∘ (liftToC (F n) ∘ cayleyInv) with hΦ
  have hΦqc : ∀ n, IsKQC (Φ n) unitDisc K₀ := fun n => (s30b_disc_conj (hFqc n)).1
  have hΦmaps : ∀ n, ∀ z ∈ unitDisc, Φ n z ∈ unitDisc := fun n => (s30b_disc_conj (hFqc n)).2
  have hΦbd : ∀ n, ∀ z ∈ unitDisc, ‖Φ n z‖ ≤ 1 := fun n z hz => (mem_ball_zero_iff.mp (hΦmaps n z hz)).le
  obtain ⟨φ, hφ, Φl, hlim⟩ := thm8_1_normal_family (D := unitDisc) Metric.isBounded_ball
    (isConnected_ball one_pos) hΦqc hΦbd
  -- the values at `0` stay in the compact `cayley '' K_Y`
  set C₀ : Set ℂ := (fun τ : UpperHalfPlane => cayley (τ : ℂ)) '' KY with hC₀
  have hcayc : Continuous (fun τ : UpperHalfPlane => cayley (τ : ℂ)) := by
    have : (fun τ : UpperHalfPlane => cayley (τ : ℂ)) =
        fun τ : UpperHalfPlane => ((τ : ℂ) - Complex.I) / ((τ : ℂ) + Complex.I) := rfl
    rw [this]
    exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.add continuous_const) fun τ => cayley_den_ne_zero τ.im_pos
  have hC₀c : IsCompact C₀ := hKY.image hcayc
  have hC₀D : C₀ ⊆ unitDisc := by
    rintro _ ⟨τ, -, rfl⟩
    exact cayley_mem_unitDisc τ.im_pos
  have hΦ0 : ∀ n, Φ n 0 = cayley (F n UpperHalfPlane.I : ℂ) := by
    intro n
    simp only [hΦ, Function.comp_apply, s30b_cayleyInv_zero]
    rw [← UpperHalfPlane.coe_I, h23l_liftToC_coe]
  have hlimD := s30b_limit_mapsTo (fun n => hΦqc (φ n)) (fun n => hΦmaps (φ n)) hlim hC₀c hC₀D
    (fun n => by rw [hΦ0]; exact ⟨_, hFK (φ n), rfl⟩)
  -- every `F_{φ n} τ` converges in `ℍ`
  have hconv : ∀ τ : UpperHalfPlane, ∃ w : UpperHalfPlane,
      Tendsto (fun n => F (φ n) τ) atTop (𝓝 w) := by
    intro τ
    have hτD : cayley (τ : ℂ) ∈ unitDisc := cayley_mem_unitDisc τ.im_pos
    have hlD := hlimD _ hτD
    have hwH : cayleyInv (Φl (cayley (τ : ℂ))) ∈ upperHalf :=
      cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hlD)
    refine ⟨⟨_, hwH⟩, ?_⟩
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    have hci : ContinuousAt cayleyInv (Φl (cayley (τ : ℂ))) :=
      (differentiableOn_cayleyInv.differentiableAt (isOpen_ball.mem_nhds hlD)).continuousAt
    have h1 := hci.tendsto.comp (hlim.tendsto_at hτD)
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply]
    exact s30b_recover (F (φ n)) τ
  choose w hw using hconv
  -- the finite generating set `E` of `Γ_X`
  set E : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {γ ∈ ΓX | ((fun z => γ • z) '' KX ∩ KX).Nonempty}
    with hEdef
  have hEfin : E.Finite := utm_x2_isFuchsian hX KX hKX
  have hgen := s30b_generate (utm_x2_isFuchsian hX) hKX hcovX
  -- a compact set containing all the relevant values
  set C : Set UpperHalfPlane := KY ∪ ⋃ γ ∈ E, insert (w (γ • UpperHalfPlane.I))
    (range fun n => F (φ n) (γ • UpperHalfPlane.I)) with hCdef
  have hCc : IsCompact C :=
    hKY.union (hEfin.isCompact_biUnion fun γ _ => (hw (γ • UpperHalfPlane.I)).isCompact_insert_range)
  -- the deck elements
  have hdeck : ∀ n, ∀ γ ∈ ΓX, ∃ δ ∈ ΓY, ∀ τ, F n (γ • τ) = δ • F n τ :=
    fun n γ hγ => h23l_deck hX hY (hF n) hγ
  choose δ hδΓ hδ using hdeck
  set Fin' : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {d ∈ ΓY | ((fun z => d • z) '' C ∩ C).Nonempty}
    with hFindef
  have hFinfin : Fin'.Finite := utm_x2_isFuchsian hY C hCc
  have hmemFin : ∀ n, ∀ e : E, δ (φ n) e.1 e.2.1 ∈ Fin' := by
    intro n e
    refine ⟨hδΓ _ _ _, δ (φ n) e.1 e.2.1 • F (φ n) UpperHalfPlane.I,
      ⟨F (φ n) UpperHalfPlane.I, Or.inl (hFK _), rfl⟩, ?_⟩
    rw [← hδ]
    refine Or.inr (mem_iUnion₂.2 ⟨e.1, e.2, ?_⟩)
    exact mem_insert_of_mem _ ⟨n, rfl⟩
  have : Finite E := hEfin.to_subtype
  have : Finite Fin' := hFinfin.to_subtype
  obtain ⟨n, n', hnn', heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => fun e : E => (⟨δ (φ n) e.1 e.2.1, hmemFin n e⟩ : Fin'))
  have hδeq : ∀ e : E, δ (φ n) e.1 e.2.1 = δ (φ n') e.1 e.2.1 := fun e =>
    congrArg Subtype.val (congrFun heq e)
  -- the conjugations agree on `E`, hence on `Γ_X`
  have hagE : ∀ x ∈ E, ∀ τ, F (φ n) (x • (F (φ n)).symm τ) = F (φ n') (x • (F (φ n')).symm τ) := by
    intro x hx τ
    rw [hδ (φ n) x hx.1, hδ (φ n') x hx.1, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    exact congrArg (· • τ) (hδeq ⟨x, hx⟩)
  have hag := s30b_agree_closure hagE
  refine ⟨φ n, φ n', hφ.injective.ne hnn', ?_⟩
  refine (thm23_1_homotopy_iff hX hY (G (φ n)) (G (φ n')) (hF (φ n)) (hF (φ n'))).2
    ⟨1, ΓY.one_mem, fun γ hγ τ => ?_⟩
  rw [inv_one, one_smul, one_smul]
  exact hag γ (hgen hγ) τ

/-- **Companion of `hurwitz_finite`** (§30.5, Hurwitz's theorem, finiteness) for `S₀ = ℍ/Γ₀`: a compact Riemann
surface of genus `g > 1` has only finitely many conformal automorphisms.  Conformal automorphisms are `1`-q.c.; `1`-q.c.
self-maps of `S₀` fall into finitely many homotopy classes (normal families of lifts, finitely many deck
actions on generators), and a conformal automorphism homotopic to the identity is the identity
(`thm23_1_cor_of_uniformization`).

*Derivation note:* the book statement `hurwitz_finite` follows from this companion plus `thm22_3_classification`. -/
theorem hurwitz_finite_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.Finite := by
  -- infinitely many automorphisms: two of them, `φ ≠ ψ`, are homotopic (KL with `K₀ = 1`)
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  have hK : ∀ n, IsKQCRS (e n).1 1 := fun n => (isKQCRS_one_iff _).2 (e n).2
  obtain ⟨n, n', hne, hhom⟩ := utm_y_kl hp₀ hp₀ (fun n => (e n).1) hK
  set φ : S₀ ≃ₜ S₀ := (e n).1
  set ψ : S₀ ≃ₜ S₀ := (e n').1
  have hbφ : IsBiholomorphic φ := (e n).2
  have hbψ : IsBiholomorphic ψ := (e n').2
  have hb : IsBiholomorphic (φ.trans ψ.symm : S₀ ≃ₜ S₀) := by
    have := IsBiholomorphic.comp hbψ.homeomorph_symm hbφ
    exact this
  -- `ψ⁻¹ ∘ φ` is a conformal automorphism homotopic to the identity, hence the identity
  have hh : ContinuousMap.Homotopic ((φ.trans ψ.symm : S₀ ≃ₜ S₀) : C(S₀, S₀)) (ContinuousMap.id S₀) := by
    have h1 := (ContinuousMap.Homotopic.refl (ψ.symm : C(S₀, S₀))).comp hhom
    have e1 : (ψ.symm : C(S₀, S₀)).comp (φ : C(S₀, S₀)) = ((φ.trans ψ.symm : S₀ ≃ₜ S₀) : C(S₀, S₀)) := rfl
    have e2 : (ψ.symm : C(S₀, S₀)).comp (ψ : C(S₀, S₀)) = ContinuousMap.id S₀ := by
      ext x
      simp
    rw [e1, e2] at h1
    exact h1
  have hid := thm23_1_cor_of_uniformization hg hS _ hb hh hp₀
  apply hne
  apply e.injective
  apply Subtype.ext
  show φ = ψ
  ext x
  have hx : ψ.symm (φ x) = x := by
    have := congrFun hid x
    simpa using this
  calc φ x = ψ (ψ.symm (φ x)) := (ψ.apply_symm_apply _).symm
    _ = ψ x := by rw [hx]

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §30.5 (Hurwitz's theorem, finiteness): a compact Riemann surface of genus `g > 1` has only finitely many
conformal automorphisms.  (Stated separately from `hurwitz` by user decision, 2026-09-26, so that it can be proved
for surfaces given as `ℍ/Γ` as a companion; `hurwitz` below still contains it.) -/
theorem hurwitz_finite {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    {φ : S₀ ≃ₜ S₀ | IsBiholomorphic φ}.Finite := by
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact hurwitz_finite_of_uniformization (S₀ := S₀) hg hS hp₀

end

/-- If a modular transformation `h` moves a point of the `d_T`-ball `B([m], R)` into that ball, then `m ∘ h ≃ G ∘ m`
for an `e^{4R}`-q.c. self-map `G` of `m.X`: `d_T([m], [m ∘ h]) < 2R` (`modAction_isometry`, triangle inequality) and
`s30b_small_map`.  (Scout B's `h30b_small_disp`.) -/
theorem utm_y_small_disp [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) (m : MarkedRS S₀) {R : ℝ} (h : ModTransform S₀)
    (hP : ∃ q q', teichDistance (Quot.mk _ m) q < R ∧ ModAction h q q' ∧ teichDistance (Quot.mk _ m) q' < R) :
    ∃ G : m.X.carrier ≃ₜ m.X.carrier, IsKQCRS G (Real.exp (2 * (2 * R))) ∧
      ContinuousMap.Homotopic ((m.marking.trans G : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier))
        ((h.1.trans m.marking : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)) := by
  obtain ⟨q, q', hq, hqq', hq'⟩ := hP
  have hqc := s30b_isQCRS_trans h m
  set m' : MarkedRS S₀ := ⟨m.X, h.1.trans m.marking, hqc⟩
  have hpp' : ModAction h (Quot.mk _ m) (Quot.mk _ m') := ⟨m, hqc, rfl, rfl⟩
  have hiso : teichDistance q' (Quot.mk _ m') = teichDistance q (Quot.mk _ m) :=
    modAction_isometry hg hS h hqq' hpp'
  have hR0 : 0 < R := lt_of_le_of_lt (s29_m_teichDistance_nonneg _ _) hq
  have hd : teichDistance (Quot.mk _ m : TeichSpace S₀) (Quot.mk _ m') < 2 * R := by
    have t1 := s29_m_teichDistance_triangle (Quot.mk _ m : TeichSpace S₀) (Quot.mk _ m') q'
    have t2 : teichDistance (Quot.mk _ m' : TeichSpace S₀) q' = teichDistance q' (Quot.mk _ m') :=
      s29_m_teichDistance_symm _ _
    have t3 : teichDistance q (Quot.mk _ m : TeichSpace S₀) = teichDistance (Quot.mk _ m) q :=
      s29_m_teichDistance_symm _ _
    linarith
  obtain ⟨G, hG, hle, hhom⟩ := s30b_small_map m m' hd
  have h1 : (1 : ℝ) ≤ Real.exp (2 * (2 * R)) := Real.one_le_exp (by positivity)
  exact ⟨G, s29_m_isKQCRS_of_le hG h1 hle, hhom⟩

/-- From `G ∘ m ≃ m ∘ h`, `G' ∘ m ≃ m ∘ h'` and `G ≃ G'`, get `h ≃ h'` (compose with `m⁻¹`).  (Scout B's
`h30b_hom_of_hom`.) -/
theorem utm_y_hom_of_hom (m : MarkedRS S₀) {h h' : S₀ ≃ₜ S₀} {G G' : m.X.carrier ≃ₜ m.X.carrier}
    (hG : ContinuousMap.Homotopic ((m.marking.trans G : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier))
      ((h.trans m.marking : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)))
    (hG' : ContinuousMap.Homotopic ((m.marking.trans G' : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier))
      ((h'.trans m.marking : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)))
    (hGG : ContinuousMap.Homotopic (G : C(m.X.carrier, m.X.carrier)) (G' : C(m.X.carrier, m.X.carrier))) :
    ContinuousMap.Homotopic (h : C(S₀, S₀)) (h' : C(S₀, S₀)) := by
  have h1 := hGG.comp (ContinuousMap.Homotopic.refl (m.marking : C(S₀, m.X.carrier)))
  rw [← coe_homeomorph_trans, ← coe_homeomorph_trans] at h1
  have h2 := (hG.symm.trans h1).trans hG'
  have h3 := (ContinuousMap.Homotopic.refl (m.marking.symm : C(m.X.carrier, S₀))).comp h2
  have e : ∀ k : S₀ ≃ₜ S₀, (m.marking.symm : C(m.X.carrier, S₀)).comp
      ((k.trans m.marking : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)) = (k : C(S₀, S₀)) := by
    intro k
    ext x
    simp
  rw [e, e] at h3
  exact h3

/-- **Companion of `modAction_properly_discontinuous`** (§30.5) for `S₀ = ℍ/Γ₀`: up to homotopy only finitely many
modular transformations move some point of the `d_T`-ball of radius `R` about `p` into that ball.  Such a
transformation is realized, on a fixed representative `m` of `p`, by a `e^{4R}`-q.c. self-map of `m.X` (up to
homotopy), and those fall into finitely many homotopy classes.

*Derivation note:* the book statement `modAction_properly_discontinuous` follows from this companion plus
`thm22_3_classification`. -/
theorem modAction_properly_discontinuous_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (p : TeichSpace S₀) (R : ℝ)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ F : Finset (ModTransform S₀), ∀ h : ModTransform S₀,
      (∃ q q', teichDistance p q < R ∧ ModAction h q q' ∧ teichDistance p q' < R) →
        ∃ h' ∈ F, ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) := by
  classical
  obtain ⟨m, rfl⟩ := Quot.exists_rep p
  obtain ⟨ΓX, pX, _, _, hX, _⟩ := s27u_exists_uniformization hp₀ m
  -- the homotopy classes of the transformations moving a point of the ball into the ball are finitely many
  let st : Setoid (ModTransform S₀) :=
    { r := fun h h' => ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀))
      iseqv := ⟨fun _ => ContinuousMap.Homotopic.refl _, fun h => h.symm, fun h h' => h.trans h'⟩ }
  set T : Set (ModTransform S₀) := {h | ∃ q q', teichDistance (Quot.mk _ m) q < R ∧ ModAction h q q' ∧
    teichDistance (Quot.mk _ m) q' < R}
  have hfin : (Quotient.mk st '' T).Finite := by
    by_contra hinf
    let e := Set.Infinite.natEmbedding _ hinf
    have hex : ∀ n, ∃ h ∈ T, Quotient.mk st h = (e n).1 := fun n => (e n).2
    choose hs hsT hse using hex
    -- each is realized by an `e^{4R}`-q.c. self-map of `m.X`; KL gives two homotopic ones
    have hG : ∀ n, ∃ G : m.X.carrier ≃ₜ m.X.carrier, IsKQCRS G (Real.exp (2 * (2 * R))) ∧
        ContinuousMap.Homotopic ((m.marking.trans G : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier))
          (((hs n).1.trans m.marking : S₀ ≃ₜ m.X.carrier) : C(S₀, m.X.carrier)) :=
      fun n => utm_y_small_disp hg hS m (hs n) (hsT n)
    choose G hGK hGhom using hG
    obtain ⟨n, n', hne, hhom⟩ := utm_y_kl hX hX G hGK
    apply hne
    apply e.injective
    apply Subtype.ext
    rw [← hse n, ← hse n']
    exact Quotient.sound (utm_y_hom_of_hom m (hGhom n) (hGhom n') hhom)
  refine ⟨hfin.toFinset.image Quotient.out, fun h hh => ⟨Quotient.out (Quotient.mk st h), ?_, ?_⟩⟩
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨h, hh, rfl⟩)
  · exact st.symm (Quotient.mk_out (s := st) h)

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §30.5 (proper discontinuity, equivalent form): for every `p` and `R > 0`, up to homotopy only
finitely many modular transformations move some point of the `d_T`-ball of radius `R` about `p`
into that ball. -/
theorem modAction_properly_discontinuous {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (p : TeichSpace S₀) (R : ℝ) :
    ∃ F : Finset (ModTransform S₀), ∀ h : ModTransform S₀,
      (∃ q q', teichDistance p q < R ∧ ModAction h q q' ∧ teichDistance p q' < R) →
        ∃ h' ∈ F, ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) := by
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact modAction_properly_discontinuous_of_uniformization (S₀ := S₀) hg hS p R hp₀

end

/-- **Companion of `thm30_3`** (Theorem 30.3) for `S₀ = ℍ/Γ₀`: `Mod(S₀)` acts discontinuously on `T(S₀)`
(from `modAction_properly_discontinuous_of_uniformization` with `R = d_T(τ, τ₁) + 1`).

*Derivation note:* the book statement `thm30_3` follows from this companion plus `thm22_3_classification`. -/
theorem thm30_3_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ModActionDiscontinuous S₀ := by
  rintro τ τ₁ ⟨σ, hσ, τn, hτn, hconv⟩
  -- eventually every `σₖ` moves `τ` into the ball of radius `d_T(τ, τ₁) + 1` about `τ`: finitely many classes
  obtain ⟨F, hF⟩ := modAction_properly_discontinuous_of_uniformization hg hS τ (teichDistance τ τ₁ + 1) hp₀
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds one_pos))
  have hmem : ∀ k : ℕ, ∃ h' ∈ F, ContinuousMap.Homotopic ((σ (N + k)).1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) := by
    intro k
    refine hF (σ (N + k)) ⟨τ, τn (N + k), ?_, hτn _, ?_⟩
    · rw [s29_m_teichDistance_self]
      linarith [s29_m_teichDistance_nonneg τ τ₁]
    · have t := s29_m_teichDistance_triangle τ (τn (N + k)) τ₁
      have := hN (N + k) (Nat.le_add_right N k)
      linarith
  -- two of the pairwise non-homotopic `σ_{N+k}` fall into the same class: a contradiction
  choose h' hh'F hh' using hmem
  obtain ⟨k, k', hkk', heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨h' k, hh'F k⟩ : F))
  have e : h' k = h' k' := congrArg Subtype.val heq
  have e2 := hh' k'
  rw [← e] at e2
  exact hσ (N + k) (N + k') (by omega) ((hh' k).trans e2.symm)

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- **Theorem 30.3**: for a compact Riemann surface `S₀` of genus `g > 1`, the modular group
`Mod(S₀)` acts discontinuously on `T(S₀)`. -/
theorem thm30_3 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) : ModActionDiscontinuous S₀ := by
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact thm30_3_of_uniformization (S₀ := S₀) hg hS hp₀

end

/-- Conformal equivalence of closed surfaces of genus `g` is an equivalence relation.  (Scout B's
`h30b_rsce_equivalence`.) -/
theorem utm_y_rsce_equivalence (g : ℕ) :
    Equivalence (fun X Y : {X : ClosedRS.{u} // HasGenus X.carrier g} =>
      RSConformallyEquivalent X.1.carrier Y.1.carrier) := by
  refine ⟨fun X => ⟨id, isBiholomorphic_id⟩, ?_, ?_⟩
  · rintro X Y ⟨f, hfd, k, hkd, hl, hr⟩
    exact ⟨k, hkd, f, hfd, hr, hl⟩
  · rintro X Y Z ⟨f, hf⟩ ⟨h, hh⟩
    exact ⟨h ∘ f, hh.comp hf⟩

/-- Equal points of `R_g` are conformally equivalent surfaces.  (Scout B's `h30b_rsce_of_eq`.) -/
theorem utm_y_rsce_of_eq {g : ℕ} {X Y : {X : ClosedRS.{u} // HasGenus X.carrier g}}
    (h : (Quot.mk _ X : ModuliSpace.{u} g) = Quot.mk _ Y) : RSConformallyEquivalent X.1.carrier Y.1.carrier :=
  (Equivalence.eqvGen_iff (utm_y_rsce_equivalence g)).1 (Quot.eqvGen_exact h)

/-- A conformal equivalence of closed surfaces as a biholomorphic homeomorphism.  (Scout B's
`h30b_homeo_of_rsce`.) -/
theorem utm_y_homeo_of_rsce {X Y : ClosedRS.{u}} (h : RSConformallyEquivalent X.carrier Y.carrier) :
    ∃ c : X.carrier ≃ₜ Y.carrier, IsBiholomorphic c := by
  obtain ⟨f, hfd, k, hkd, hl, hr⟩ := h
  exact ⟨⟨⟨f, k, hl, hr⟩, hfd.continuous, hkd.continuous⟩, hfd, k, hkd, hl, hr⟩

/-- **KL, pigeonhole form**: for `K₀`-q.c. `Gₙ : X → Y` between `X = ℍ/Γ_X` and `Y = ℍ/Γ_Y`, some homotopy class
contains infinitely many `Gₙ` (the classes met are finitely many by `utm_y_kl`).  (Scout B's `h30b_klc`.) -/
theorem utm_y_klc {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y]
    [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY) {K₀ : ℝ}
    (G : ℕ → X ≃ₜ Y) (hG : ∀ n, IsKQCRS (G n) K₀) :
    ∃ n₀, {n | ContinuousMap.Homotopic (G n : C(X, Y)) (G n₀ : C(X, Y))}.Infinite := by
  let st : Setoid (X ≃ₜ Y) :=
    { r := fun a b => ContinuousMap.Homotopic (a : C(X, Y)) (b : C(X, Y))
      iseqv := ⟨fun _ => ContinuousMap.Homotopic.refl _, fun h => h.symm, fun h h' => h.trans h'⟩ }
  have hfin : (range fun n => Quotient.mk st (G n)).Finite := by
    by_contra hinf
    let e := Set.Infinite.natEmbedding _ hinf
    have hex : ∀ k, ∃ n, Quotient.mk st (G n) = (e k).1 := fun k => (e k).2
    choose ns hns using hex
    obtain ⟨k, k', hne, hhom⟩ := utm_y_kl hX hY (fun k => G (ns k)) (fun k => hG _)
    apply hne
    apply e.injective
    apply Subtype.ext
    rw [← hns k, ← hns k']
    exact Quotient.sound hhom
  have : Finite (range fun n => Quotient.mk st (G n)) := hfin.to_subtype
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber (fun n : ℕ => (⟨Quotient.mk st (G n), n, rfl⟩ :
    range fun n => Quotient.mk st (G n)))
  obtain ⟨n₀, hn₀⟩ := y.2
  refine ⟨n₀, (Set.infinite_coe_iff.1 hy).mono fun n hn => ?_⟩
  have h1 : Quotient.mk st (G n) = y.1 := congrArg Subtype.val (Set.mem_singleton_iff.1 hn)
  exact Quotient.exact (h1.trans hn₀.symm)

/-- **Companion of `thm30_4_hausdorff`** (Theorem 30.4) for `S₀ = ℍ/Γ₀`: `R_g` is a Hausdorff space.  If the
`ε`-neighbourhoods of `r ≠ r'` met for every `ε = 1/(n+1)`, the realizing marked surfaces would give maps between
representatives of `r` and `r'` with `K → 1`, finitely many homotopy classes, hence a conformal limit `r = r'`.

*Derivation note:* the book statement `thm30_4_hausdorff` follows from this companion plus `thm22_3_classification`. -/
theorem thm30_4_hausdorff_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {r r' : ModuliSpace.{u} g} (hne : r ≠ r')
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ ε > 0, Disjoint (moduliNbhd (S₀ := S₀) r ε) (moduliNbhd (S₀ := S₀) r' ε) := by
  have _ := hS
  by_contra hcon
  push Not at hcon
  -- for every `n`, points `[a], [b]` over `r, r'` and `[a'], [b']` over one point of `R_g`, `1/(n+1)`-close
  have hdata : ∀ n : ℕ, ∃ (a b a' b' : MarkedRS S₀) (ha : HasGenus a.X.carrier g)
      (hb : HasGenus b.X.carrier g) (ha' : HasGenus a'.X.carrier g) (hb' : HasGenus b'.X.carrier g),
      r = Quot.mk _ ⟨a.X, ha⟩ ∧ r' = Quot.mk _ ⟨b.X, hb⟩ ∧
      (Quot.mk _ ⟨a'.X, ha'⟩ : ModuliSpace.{u} g) = Quot.mk _ ⟨b'.X, hb'⟩ ∧
      teichDistance (Quot.mk _ a : TeichSpace S₀) (Quot.mk _ a') < 1 / ((n : ℝ) + 1) ∧
      teichDistance (Quot.mk _ b : TeichSpace S₀) (Quot.mk _ b') < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨r'', h1, h2⟩ := Set.not_disjoint_iff.1 (hcon (1 / ((n : ℝ) + 1)) (by positivity))
    obtain ⟨p₁, p₁'', ⟨a, ha, rfl, hra⟩, ⟨a', ha', rfl, hra'⟩, hd₁⟩ := h1
    obtain ⟨p₂, p₂'', ⟨b, hb, rfl, hrb⟩, ⟨b', hb', rfl, hrb'⟩, hd₂⟩ := h2
    exact ⟨a, b, a', b', ha, hb, ha', hb', hra, hrb, hra'.symm.trans hrb', hd₁, hd₂⟩
  choose a b a' b' ha hb ha' hb' hra hrb hr'' hd₁ hd₂ using hdata
  -- conformal identifications
  have hcA : ∀ n, ∃ c : (a 0).X.carrier ≃ₜ (a n).X.carrier, IsBiholomorphic c := fun n =>
    utm_y_homeo_of_rsce (utm_y_rsce_of_eq ((hra 0).symm.trans (hra n)))
  have hcB : ∀ n, ∃ c : (b n).X.carrier ≃ₜ (b 0).X.carrier, IsBiholomorphic c := fun n =>
    utm_y_homeo_of_rsce (utm_y_rsce_of_eq ((hrb n).symm.trans (hrb 0)))
  have hcM : ∀ n, ∃ c : (a' n).X.carrier ≃ₜ (b' n).X.carrier, IsBiholomorphic c := fun n =>
    utm_y_homeo_of_rsce (utm_y_rsce_of_eq (hr'' n))
  choose cA hcA using hcA
  choose cB hcB using hcB
  choose cM hcM using hcM
  -- maps with small dilatation
  have hG₁ : ∀ n, ∃ G : (a n).X.carrier ≃ₜ (a' n).X.carrier, IsQCRS G ∧
      maxDilatationRS G ≤ ENNReal.ofReal (Real.exp (2 * (1 / ((n : ℝ) + 1)))) := fun n => by
    obtain ⟨G, hG, hle, -⟩ := s30b_small_map (a n) (a' n) (hd₁ n)
    exact ⟨G, hG, hle⟩
  have hG₂ : ∀ n, ∃ G : (b' n).X.carrier ≃ₜ (b n).X.carrier, IsQCRS G ∧
      maxDilatationRS G ≤ ENNReal.ofReal (Real.exp (2 * (1 / ((n : ℝ) + 1)))) := fun n => by
    obtain ⟨G, hG, hle, -⟩ := s30b_small_map (b' n) (b n)
      ((s29_m_teichDistance_symm (Quot.mk _ (b' n) : TeichSpace S₀) (Quot.mk _ (b n))).trans_lt (hd₂ n))
    exact ⟨G, hG, hle⟩
  choose G₁ hG₁ hG₁le using hG₁
  choose G₂ hG₂ hG₂le using hG₂
  -- `H n : X → Y` through the conformal identifications, with `K[H n] ≤ e^{4/(n+1)}`
  have hL₁ := fun n => s29_m_maxDil_conj_biholo (hG₁ n) (hcA n) (hcM n)
  have hL₂ := fun n => s29_m_maxDil_conj_biholo (c₁ := Homeomorph.refl (b' n).X.carrier) (hG₂ n)
    (show IsBiholomorphic ((Homeomorph.refl (b' n).X.carrier : _ ≃ₜ _) : (b' n).X.carrier → (b' n).X.carrier)
      from isBiholomorphic_id) (hcB n)
  have hH : ∀ n, IsQCRS (((cA n).trans ((G₁ n).trans (cM n))).trans
      ((Homeomorph.refl (b' n).X.carrier).trans ((G₂ n).trans (cB n)))) ∧
      maxDilatationRS (((cA n).trans ((G₁ n).trans (cM n))).trans
        ((Homeomorph.refl (b' n).X.carrier).trans ((G₂ n).trans (cB n)))) ≤
        ENNReal.ofReal (Real.exp (2 * (2 / ((n : ℝ) + 1)))) := by
    intro n
    have : Nonempty (a 0).X.carrier := ConnectedSpace.toNonempty
    have : Nonempty (b' n).X.carrier := ConnectedSpace.toNonempty
    obtain ⟨hqc, hle⟩ := eq23_4 (s29_m_isKQCRS_maxDil (hL₁ n).1) (s29_m_isKQCRS_maxDil (hL₂ n).1)
    refine ⟨⟨_, hqc⟩, ?_⟩
    refine hle.trans ((mul_le_mul' ((hL₂ n).2.trans (hG₂le n)) ((hL₁ n).2.trans (hG₁le n))).trans ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply le_of_eq
    congr 2
    ring
  set H : ℕ → (a 0).X.carrier ≃ₜ (b 0).X.carrier := fun n => ((cA n).trans ((G₁ n).trans (cM n))).trans
      ((Homeomorph.refl (b' n).X.carrier).trans ((G₂ n).trans (cB n)))
  have hHK : ∀ n, IsKQCRS (H n) (Real.exp 4) := by
    intro n
    refine s29_m_isKQCRS_of_le (hH n).1 (Real.one_le_exp (by norm_num)) ((hH n).2.trans ?_)
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : 2 / ((n : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  -- uniformizations of the two surfaces; infinitely many `H n` in one class (KL)
  obtain ⟨ΓX, pX, _, _, hX, _⟩ := s27u_exists_uniformization hp₀ (a 0)
  obtain ⟨ΓY, pY, _, _, hY, _⟩ := s27u_exists_uniformization hp₀ (b 0)
  obtain ⟨n₀, hinf⟩ := utm_y_klc hX hY H hHK
  -- the extremal map of that class has `K = 1`, so `r = r'`
  obtain ⟨f₀, hff₀, -, hext, -⟩ :=
    thm27_2_existence_qc_of_uniformization hg (ha 0) (hb 0) (H n₀) (hH n₀).1 hX hY
  have hbound : ∀ ε > 0, maxDilatationRS f₀ ≤ ENNReal.ofReal (Real.exp (2 * ε)) := by
    intro ε hε
    obtain ⟨n, hn, hnlt⟩ := hinf.exists_gt ⌈2 / ε⌉₊
    have h1 : maxDilatationRS f₀ ≤ maxDilatationRS (H n) := hext.2 (H n) (hH n).1 (hff₀.symm.trans hn.symm)
    refine h1.trans ((hH n).2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
    have h2 : 2 / ε < (n : ℝ) := Nat.lt_of_ceil_lt hnlt
    have h3 : 2 / ((n : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at h2
      nlinarith
    linarith
  have : Nonempty (a 0).X.carrier := ConnectedSpace.toNonempty
  have h1 : maxDilatationRS f₀ = 1 :=
    le_antisymm (utm_y_le_one_of_forall_exp (s29_m_maxDilatationRS_ne_top hext.1) hbound)
      (s29_m_one_le_maxDilatationRS hext.1)
  have hbi : IsBiholomorphic f₀ := (isKQCRS_one_iff f₀).1 (utm_isKQCRS_one_of_maxDil hext.1 h1)
  exact hne ((hra 0).trans ((Quot.sound ⟨f₀, hbi⟩).trans (hrb 0).symm))

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- **Theorem 30.4**: for `g > 1`, `R_g = T_g/Mod_g` is a Hausdorff space: distinct points of `R_g`
have disjoint `ε`-neighbourhoods. -/
theorem thm30_4_hausdorff {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {r r' : ModuliSpace.{u} g} (hne : r ≠ r') :
    ∃ ε > 0, Disjoint (moduliNbhd (S₀ := S₀) r ε) (moduliNbhd (S₀ := S₀) r' ε) := by
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact thm30_4_hausdorff_of_uniformization (S₀ := S₀) hg hS hne hp₀

end

/-! ## Part 7. Companion of (32.2) for a target `X₁' = ℍ/Γ₁` (s31t, coordinator 553e2d)

`eq32_2_symmetric_lift` (§32, the lifted Teichmüller map commutes with the covering transformations) as the companion
`eq32_2_symmetric_lift_of_uniformization`: the book statement plus only a uniformization of `X₁'`. -/

/-- Pre-composition of a Teichmüller map by a biholomorphic homeomorphism is a Teichmüller map with the same `k`:
`h ≫ f = (f⁻¹ ≫ h⁻¹)⁻¹`, by `utm_x_teichmullerMap_symm` twice and `utm_x_teichmullerMap_trans`. -/
theorem utm_z_teichmullerMap_precomp {A B C : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [T2Space A]
    [ConnectedSpace A] [IsManifold 𝓘(ℂ) ω A] [TopologicalSpace B] [ChartedSpace ℂ B] [T2Space B]
    [ConnectedSpace B] [IsManifold 𝓘(ℂ) ω B] [TopologicalSpace C] [ChartedSpace ℂ C] [T2Space C]
    [ConnectedSpace C] [IsManifold 𝓘(ℂ) ω C] {f : B ≃ₜ C} {q : B → ℂ → ℂ} {q' : C → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) {h : A ≃ₜ B} (hh : IsBiholomorphic h) :
    ∃ (qa : A → ℂ → ℂ) (qc : C → ℂ → ℂ), IsTeichmullerMap (h.trans f) qa qc k := by
  have h1 := utm_x_teichmullerMap_symm hf
  obtain ⟨q'', h2⟩ := utm_x_teichmullerMap_trans h1 (IsBiholomorphic.homeomorph_symm hh)
  have h3 := utm_x_teichmullerMap_symm h2
  have heq : (f.symm.trans h.symm).symm = h.trans f := by
    ext x
    rfl
  rw [heq] at h3
  exact ⟨_, _, h3⟩

/-- **Companion of `eq32_2_symmetric_lift`** ((32.2)) for a target surface given as `X₁' = ℍ/Γ₁`: with `h₀`, `h₁`
biholomorphic self-maps (the covering transformations of the double covers) and `ftil` commuting with them, the
Teichmüller map `ftil₀ ≃ ftil` also commutes: `ftil₀ ∘ h₀ = h₁ ∘ ftil₀`.  `h₀ ≫ ftil₀ ≫ h₁⁻¹` is a Teichmüller map
with the same `k` (`utm_z_teichmullerMap_precomp`, `utm_x_teichmullerMap_trans`), homotopic to
`h₀ ≫ ftil ≫ h₁⁻¹ = ftil ≃ ftil₀`, so it equals `ftil₀` by `thm26_2_uniqueness_of_uniformization` on `X₁'`.

*Derivation note:* the book statement `eq32_2_symmetric_lift` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of the closed surface `X₁'` of genus `g' > 1`). -/
theorem eq32_2_symmetric_lift_of_uniformization {X₀' X₁' : ClosedRS.{u}} {g' : ℕ} (hg' : 1 < g')
    (h₀' : HasGenus X₀'.carrier g') (h₁' : HasGenus X₁'.carrier g') {h₀ : X₀'.carrier ≃ₜ X₀'.carrier}
    {h₁ : X₁'.carrier ≃ₜ X₁'.carrier} (hh₀ : IsBiholomorphic h₀) (hh₁ : IsBiholomorphic h₁)
    {ftil ftil₀ : X₀'.carrier ≃ₜ X₁'.carrier} (hsym : ∀ y, ftil (h₀ y) = h₁ (ftil y))
    {q : X₀'.carrier → ℂ → ℂ} {q' : X₁'.carrier → ℂ → ℂ} {k : ℝ} (hftil₀ : IsTeichmullerMap ftil₀ q q' k)
    (hhom : ContinuousMap.Homotopic (ftil : C(X₀'.carrier, X₁'.carrier)) (ftil₀ : C(X₀'.carrier, X₁'.carrier)))
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → X₁'.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) :
    ∀ y, ftil₀ (h₀ y) = h₁ (ftil₀ y) := by
  -- `G = h₀ ≫ f̃₀ ≫ h₁⁻¹`
  obtain ⟨qa, qc, hT1⟩ := utm_z_teichmullerMap_precomp hftil₀ hh₀
  obtain ⟨qG, hG⟩ := utm_x_teichmullerMap_trans hT1 (IsBiholomorphic.homeomorph_symm hh₁)
  set G : X₀'.carrier ≃ₜ X₁'.carrier := (h₀.trans ftil₀).trans h₁.symm
  -- `h₀ ≫ f̃ ≫ h₁⁻¹ = f̃`
  have hsym' : ((h₀.trans ftil).trans h₁.symm : X₀'.carrier ≃ₜ X₁'.carrier) = ftil := by
    ext y
    simp [hsym]
  -- `f̃ ≃ G`
  have hfG : ContinuousMap.Homotopic (ftil : C(X₀'.carrier, X₁'.carrier)) (G : C(X₀'.carrier, X₁'.carrier)) := by
    have h2 := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (h₁.symm : C(X₁'.carrier, X₁'.carrier)))
      (ContinuousMap.Homotopic.comp hhom (ContinuousMap.Homotopic.refl (h₀ : C(X₀'.carrier, X₀'.carrier))))
    have e1 : (h₁.symm : C(X₁'.carrier, X₁'.carrier)).comp ((ftil : C(X₀'.carrier, X₁'.carrier)).comp
        (h₀ : C(X₀'.carrier, X₀'.carrier))) = (ftil : C(X₀'.carrier, X₁'.carrier)) := by
      ext y
      simp [hsym]
    have e2 : (h₁.symm : C(X₁'.carrier, X₁'.carrier)).comp ((ftil₀ : C(X₀'.carrier, X₁'.carrier)).comp
        (h₀ : C(X₀'.carrier, X₀'.carrier))) = (G : C(X₀'.carrier, X₁'.carrier)) := by
      ext y
      rfl
    rw [e1, e2] at h2
    exact h2
  have hf₀G : ContinuousMap.Homotopic (ftil₀ : C(X₀'.carrier, X₁'.carrier)) (G : C(X₀'.carrier, X₁'.carrier)) :=
    hhom.symm.trans hfG
  -- uniqueness: `K[G] = (1+k)/(1-k)`, so `G = f̃₀`
  have hKG : maxDilatationRS G = ENNReal.ofReal ((1 + k) / (1 - k)) := (teichmullerMap_beltrami hG).2
  have hGeq := (thm26_2_uniqueness_of_uniformization hg' h₀' h₁' hftil₀ hG.qc hf₀G hp₁).2 hKG
  intro y
  have := congrFun hGeq y
  -- `h₁⁻¹ (f̃₀ (h₀ y)) = f̃₀ y`
  have h3 : h₁.symm (ftil₀ (h₀ y)) = ftil₀ y := this
  calc ftil₀ (h₀ y) = h₁ (h₁.symm (ftil₀ (h₀ y))) := (h₁.apply_symm_apply _).symm
    _ = h₁ (ftil₀ y) := by rw [h3]

/-- §27.2: every point of `T(S₀)` is `[S_{q,k}, f]` for a unique `(q, k)` with `‖e(q)‖ = 1`
(`q` irrelevant when `k = 0`): `Φ : T̃(S₀) → T(S₀)` is a bijection, so `T(S₀)` is described by
`6g - 6` real parameters. -/
theorem teichSpace_deformation_bijection [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∀ p : TeichSpace S₀, (∃ m : MarkedRS S₀, p = Quot.mk _ m ∧ IsBiholomorphic m.marking) ∨
      ∃! qk : (holQuadDiffSubmodule S₀).restrictScalars ℝ × ℝ,
        ‖e qk.1‖ = 1 ∧ 0 < qk.2 ∧ qk.2 < 1 ∧ IsDeformationPoint qk.1 qk.2 p := by
  -- `S₀` is `ℍ/Γ₀` by the uniformization theorem (S22); then the companion applies
  obtain ⟨Γ₀, p₀, -, -, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg hS
  exact teichSpace_deformation_bijection_of_uniformization hg hS e hp₀

/-- (32.2): with `h₀`, `h₁` the non-trivial covering transformations of the double covers, the
Teichmüller map `ftil₀ : S̃₀ → S̃` obtained from Theorem 27.2 satisfies `h₁ ∘ ftil₀ ∘ h₀⁻¹ = ftil₀`, i.e.
`h₁ ∘ ftil₀ = ftil₀ ∘ h₀` (by uniqueness, since `h₁ ∘ ftil₀ ∘ h₀⁻¹` is a Teichmüller map of the same dilatation
homotopic to `ftil₀`); hence `ftil₀` and its Beltrami differential descend to `S₀ → S`. -/
theorem eq32_2_symmetric_lift {X₀' X₁' : ClosedRS.{u}} {g' : ℕ} (hg' : 1 < g') (h₀' : HasGenus X₀'.carrier g')
    (h₁' : HasGenus X₁'.carrier g') {h₀ : X₀'.carrier ≃ₜ X₀'.carrier} {h₁ : X₁'.carrier ≃ₜ X₁'.carrier}
    (hh₀ : IsBiholomorphic h₀) (hh₁ : IsBiholomorphic h₁) {ftil ftil₀ : X₀'.carrier ≃ₜ X₁'.carrier}
    (hsym : ∀ y, ftil (h₀ y) = h₁ (ftil y)) {q : X₀'.carrier → ℂ → ℂ} {q' : X₁'.carrier → ℂ → ℂ} {k : ℝ}
    (hftil₀ : IsTeichmullerMap ftil₀ q q' k)
    (hhom : ContinuousMap.Homotopic (ftil : C(X₀'.carrier, X₁'.carrier)) (ftil₀ : C(X₀'.carrier, X₁'.carrier))) :
    ∀ y, ftil₀ (h₀ y) = h₁ (ftil₀ y) := by
  -- `X₁'` is `ℍ/Γ₁` by the uniformization theorem (S22); then the companion applies
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg' h₁'
  exact eq32_2_symmetric_lift_of_uniformization hg' h₀' h₁' hh₀ hh₁ hsym hftil₀ hhom hp₁

/-! ### §29.1 (29.1) ⟹ (29.2) and (29.2) ⟹ (29.1) (`s29_e12_`), moved here from `S29_TeichmullerMetric`

Teichmüller's argument (book (29.3)–(29.7)): for the extremal Teichmüller map `Fₙ : Sₙ → S` in the class of
`f ∘ fₙ⁻¹` (`teichDistance_attained`), `eq29_7` gives `exp(2 d_T) ‖ωₙ‖ ≤ ∬_S D[fₙ ∘ f⁻¹] dA_{ωₙ}` for the normalized
terminal differential `ωₙ` (`s29_e12_main`); `D[fₙ ∘ f⁻¹] → 1` a.e. and is uniformly bounded, and the `ωₙ` lie on the
unit sphere of a finite-dimensional space, so the right side is `≤ (1 + ε) ‖ωₙ‖` eventually (`s29_e12_dct`,
`s29_e12_ae`). -/

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- A positive real multiple of both differentials of a Teichmüller map gives a Teichmüller map (the natural
parameters scale by `√c` on both sides; the analogue of `teichDeformation_smul`). -/
theorem s29_e12_teichMap_smul {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {f : X ≃ₜ Y} {q : X → ℂ → ℂ} {q' : Y → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) {c : ℝ} (hc : 0 < c) :
    IsTeichmullerMap f ((c : ℂ) • q) ((c : ℂ) • q') k := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨hf.qc, (holQuadDiffSubmodule X).smul_mem (c : ℂ) hf.initial, smul_ne_zero hc0 hf.initial_ne,
    (holQuadDiffSubmodule Y).smul_mem (c : ℂ) hf.terminal, hf.k_nonneg, hf.k_lt_one, ?_, ?_⟩
  · intro p hp
    obtain ⟨hr, ζ, ζ', hζ, hζ', hrel⟩ := hf.regular p ((s26_isRegularPoint_smul hc0 p).1 hp)
    refine ⟨(s26_isRegularPoint_smul hc0 (f p)).2 hr, fun z => (Real.sqrt c : ℂ) * ζ z,
      fun w => (Real.sqrt c : ℂ) * ζ' w, s26_isNaturalParameterAt_smul hζ hc,
      s26_isNaturalParameterAt_smul hζ' hc, ?_⟩
    filter_upwards [hrel] with z hz
    rw [hz, s26_teichStretch_ofReal_mul]
  · intro p n hp
    exact (s26_isZeroOfOrder_smul hc0 (f p) n).2 (hf.zero p n ((s26_isZeroOfOrder_smul hc0 p n).1 hp))

/-- For a q.c. `h`, `‖ω‖ ≤ ∬ D[h] dA_ω`: a.e. `D ≥ 1`, on a chart partition subordinate to `h`
(`s29_e7_D_partition`, `utm_d_ae_good`). -/
theorem s29_e12_D_ge {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {h : X ≃ₜ Y} {K : ℝ} (hh : IsKQCRS h K) {om : X → ℂ → ℂ} (hq : IsHolQuadDiff om)
    (hne : om ≠ 0) :
    quadDiffNorm om ≤ surfaceIntegral om (fun x z =>
      ENNReal.ofReal (dilatationQuotient (localMapExprAt h x z) z)) := by
  have : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨p₀⟩ : Nonempty X := inferInstance
  obtain ⟨x, P, hP, hPV, -, -⟩ := utm_d_good_partition h h.continuous p₀
  rw [s29_e7_D_partition h hq hP]
  have h1 : quadDiffNorm om = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
      (1 : ℝ≥0∞) * ENNReal.ofReal ‖om (x i) z‖ :=
    s26v_surfaceIntegral_eq_tsum hq (fun _ => (1 : ℝ≥0∞)) hP
  rw [h1]
  refine ENNReal.tsum_le_tsum fun i => lintegral_mono_ae ?_
  filter_upwards [utm_d_ae_good hh hq hne (x i) (hP.1 i).2 (utm_d_piece_sub h (hPV i))] with z hz
  obtain ⟨hzE, hq0, hd, hlt, -⟩ := hz
  obtain ⟨-, -, hDeq, -⟩ := s29_e7_pointwise (q' := fun _ _ => (0 : ℂ)) (f := h) (q := om) (x i)
    (utm_d_piece_sub h (hPV i) hzE) hq0 hd hlt
  have hD1 : 1 ≤ dilatationQuotient (localMapExpr h (x i)) z := by
    have ha : 0 < ‖dz (localMapExpr h (x i)) z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
    have hm0 : 0 ≤ ‖complexDilatation (localMapExpr h (x i)) z‖ := norm_nonneg _
    have hm1 : ‖complexDilatation (localMapExpr h (x i)) z‖ < 1 := by
      unfold complexDilatation
      rw [norm_div]
      exact (div_lt_one ha).2 hlt
    unfold dilatationQuotient
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [hDeq]
  exact mul_le_mul' (ENNReal.one_le_ofReal.2 hD1) le_rfl

/-- **[stub A] Teichmüller's main inequality for a pair of marked surfaces, normalized.**  For marked surfaces
`m₁ = (S, f)`, `m₂ = (Sₙ, fₙ)` of `S₀` (genus `g > 1`) and any linear isomorphism `e` of `Q(S)` with `ℝ^{6g-6}`, there is
`ω ∈ Q(S)` with `‖e om‖ = 1` such that `exp(2 d_T([m₂], [m₁])) ‖ω‖ ≤ ∬_S D[fₙ ∘ f⁻¹] dA_ω`.
*Route:* `teichDistance_attained` for the pair `(m₂, m₁)` gives an extremal map `F : Sₙ → S` which is conformal or a
Teichmüller map with `d_T = ½ log K[F]`; in the Teichmüller case rescale `(q, q')` by `a > 0` so that `‖e (a q')‖ = 1`
(`teichDeformation_smul` for maps) and apply `eq29_7` to `‖a q'‖⁻¹`-normalized data (homogeneity); in the conformal
case `d_T = 0`, take any unit `ω` (`Q(S) ≠ 0`, `D ≥ 1` a.e., `s29_m_teichSet_nonneg`). -/
theorem s29_e12_main {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (m₁ m₂ : MarkedRS S₀)
    (e : (holQuadDiffSubmodule m₁.X.carrier).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ om : (holQuadDiffSubmodule m₁.X.carrier).restrictScalars ℝ, ‖e om‖ = 1 ∧
      ENNReal.ofReal (Real.exp (2 * teichDistance (Quot.mk _ m₂) (Quot.mk _ m₁))) *
          quadDiffNorm (om.1 : m₁.X.carrier → ℂ → ℂ) ≤
        surfaceIntegral (om.1 : m₁.X.carrier → ℂ → ℂ) fun x z =>
          ENNReal.ofReal (dilatationQuotient (localMapExprAt (m₁.marking.symm.trans m₂.marking) x z) z) := by
  classical
  have hX₁ : HasGenus m₁.X.carrier g := hasGenus_of_homeomorph hS m₁.marking
  have hX₂ : HasGenus m₂.X.carrier g := hasGenus_of_homeomorph hS m₂.marking
  have : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
  have : Nonempty m₂.X.carrier := ConnectedSpace.toNonempty
  obtain ⟨F, -, hshape, hFhom, hd⟩ := teichDistance_attained hg hS m₂ m₁
  obtain ⟨K₁, hK₁⟩ := m₁.qc
  obtain ⟨K₂, hK₂⟩ := m₂.qc
  have hh : IsKQCRS (m₁.marking.symm.trans m₂.marking) (K₁ * K₂) :=
    (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1
  rcases hshape with hbi | ⟨q, q', k, hF⟩
  · -- `F` conformal: `d_T = 0`; any unit `ω` works since `D ≥ 1` a.e.
    have hF1 : IsKQCRS F 1 := (isKQCRS_one_iff F).2 hbi
    have hmax : maxDilatationRS F = 1 :=
      le_antisymm (by simpa using maxDilatationRS_le hF1) (s29_m_one_le_maxDilatationRS ⟨1, hF1⟩)
    have hd0 : teichDistance (Quot.mk _ m₂) (Quot.mk _ m₁) = 0 := by
      rw [hd, hmax]
      simp
    have hpos : 0 < 6 * g - 6 := by omega
    set v : EuclideanSpace ℝ (Fin (6 * g - 6)) := EuclideanSpace.single ⟨0, hpos⟩ 1 with hv
    refine ⟨e.symm v, ?_, ?_⟩
    · rw [LinearEquiv.apply_symm_apply]
      simp [hv]
    · have hom0 : (e.symm v).1 ≠ 0 := by
        intro h0
        have : e.symm v = 0 := Subtype.ext h0
        have h1 : ‖v‖ = 0 := by
          have := congrArg e this
          rw [LinearEquiv.apply_symm_apply, map_zero] at this
          rw [this, norm_zero]
        simp [hv] at h1
      rw [hd0]
      simpa using s29_e12_D_ge hh (e.symm v).2 hom0
  · -- `F` a Teichmüller map with terminal differential `q'`: rescale and apply `eq29_7`
    have hK0 : 0 < (1 + k) / (1 - k) :=
      div_pos (by linarith [hF.k_nonneg]) (by linarith [hF.k_lt_one])
    have hmax : maxDilatationRS F = ENNReal.ofReal ((1 + k) / (1 - k)) := (teichmullerMap_beltrami hF).2
    have hdK : Real.exp (2 * teichDistance (Quot.mk _ m₂) (Quot.mk _ m₁)) = (1 + k) / (1 - k) := by
      rw [hd, hmax, ENNReal.toReal_ofReal hK0.le, ← mul_assoc, mul_one_div_cancel two_ne_zero,
        one_mul, Real.exp_log hK0]
    have hqn : quadDiffNorm q' = ENNReal.ofReal ((1 + k) / (1 - k)) * quadDiffNorm q :=
      s26w_quadDiffNorm_teich hF
    have hqpos : quadDiffNorm q ≠ 0 := s26_quadDiffNorm_pos hF.initial hF.initial_ne
    have hqfin : quadDiffNorm q ≠ ⊤ := (s26_quadDiffNorm_lt_top hF.initial).ne
    have hq'pos : quadDiffNorm q' ≠ 0 := by
      rw [hqn]
      exact mul_ne_zero (ENNReal.ofReal_pos.2 hK0).ne' hqpos
    have hq'fin : quadDiffNorm q' ≠ ⊤ := (s26_quadDiffNorm_lt_top hF.terminal).ne
    set a : ℝ := (quadDiffNorm q').toReal⁻¹ with ha
    have hr : 0 < (quadDiffNorm q').toReal := ENNReal.toReal_pos hq'pos hq'fin
    have hapos : 0 < a := inv_pos.2 hr
    have hFa := s29_e12_teichMap_smul hF hapos
    have hnorm : quadDiffNorm ((a : ℂ) • q') = 1 := by
      have := s26_surfaceIntegral_smul q' (fun _ _ => (1 : ℝ≥0∞)) (a : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hapos.le] at this
      change quadDiffNorm ((a : ℂ) • q') = _ at this
      rw [this]
      calc ENNReal.ofReal a * quadDiffNorm q' =
            ENNReal.ofReal a * ENNReal.ofReal (quadDiffNorm q').toReal := by
              rw [ENNReal.ofReal_toReal hq'fin]
        _ = 1 := by
              rw [← ENNReal.ofReal_mul hapos.le, ha, inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one]
    have hhomF : ContinuousMap.Homotopic (F : C(m₂.X.carrier, m₁.X.carrier))
        ((m₂.marking.symm.trans m₁.marking : m₂.X.carrier ≃ₜ m₁.X.carrier) :
          C(m₂.X.carrier, m₁.X.carrier)) := by
      have h1 := hFhom.comp (ContinuousMap.Homotopic.refl (m₂.marking.symm : C(m₂.X.carrier, S₀)))
      have e1 : ((m₂.marking.trans F : S₀ ≃ₜ m₁.X.carrier) : C(S₀, m₁.X.carrier)).comp
          (m₂.marking.symm : C(m₂.X.carrier, S₀)) = (F : C(m₂.X.carrier, m₁.X.carrier)) := by
        ext y
        simp
      have e2 : (m₁.marking : C(S₀, m₁.X.carrier)).comp (m₂.marking.symm : C(m₂.X.carrier, S₀)) =
          ((m₂.marking.symm.trans m₁.marking : m₂.X.carrier ≃ₜ m₁.X.carrier) :
            C(m₂.X.carrier, m₁.X.carrier)) := by
        ext y
        simp
      rw [e1, e2] at h1
      exact h1
    have h7 := eq29_7 hg hS hX₁ hX₂ ⟨K₁, hK₁⟩ ⟨K₂, hK₂⟩ hFa hhomF hnorm
    -- the unit vector `c w`, `w = a q'`
    set w : (holQuadDiffSubmodule m₁.X.carrier).restrictScalars ℝ :=
      ⟨(a : ℂ) • q', (holQuadDiffSubmodule _).smul_mem (a : ℂ) hF.terminal⟩ with hw
    have hw0 : w ≠ 0 := by
      intro h0
      have h1 : ((a : ℂ) • q') = 0 := congrArg Subtype.val h0
      have h2 : quadDiffNorm ((a : ℂ) • q') = 0 := by
        rw [h1]
        unfold quadDiffNorm
        exact s26_surfaceIntegral_eq_zero _ (fun x z => by simp)
      rw [hnorm] at h2
      exact one_ne_zero h2
    have hsne : 0 < ‖e w‖ := norm_pos_iff.2 (fun h0 => hw0 (e.injective (by simpa using h0)))
    set c : ℝ := ‖e w‖⁻¹ with hc
    have hcpos : 0 < c := inv_pos.2 hsne
    refine ⟨c • w, ?_, ?_⟩
    · rw [map_smul, norm_smul, Real.norm_of_nonneg hcpos.le, hc, inv_mul_cancel₀ hsne.ne']
    · have hfun : (c • w).1 = (c : ℂ) • w.1 := by
        funext x z
        simp [Complex.real_smul]
      have hqs := s26_surfaceIntegral_smul w.1 (fun _ _ => (1 : ℝ≥0∞)) (c : ℂ)
      have hDs := s26_surfaceIntegral_smul w.1 (fun x z =>
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (m₁.marking.symm.trans m₂.marking) x z) z)) (c : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hcpos.le] at hqs hDs
      rw [hdK, hfun]
      change ENNReal.ofReal ((1 + k) / (1 - k)) * quadDiffNorm ((c : ℂ) • w.1) ≤ _
      have hw1 : quadDiffNorm w.1 = 1 := hnorm
      change ENNReal.ofReal ((1 + k) / (1 - k)) * surfaceIntegral ((c : ℂ) • w.1) (fun _ _ => (1 : ℝ≥0∞)) ≤ _
      rw [hqs, hDs]
      change ENNReal.ofReal ((1 + k) / (1 - k)) * (ENNReal.ofReal c * quadDiffNorm w.1) ≤ _
      rw [hw1, mul_one, mul_comm]
      exact mul_le_mul' le_rfl h7

/-- **Domination by the coordinate basis.**  In every chart `|ω| ≤ ‖e ω‖ Σⱼ |bⱼ|`, `bⱼ = e⁻¹ eⱼ`. -/
theorem s29_e12_dom {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {N : ℕ}
    (e : (holQuadDiffSubmodule X).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (om : (holQuadDiffSubmodule X).restrictScalars ℝ) (x : X) (z : ℂ) :
    ‖om.1 x z‖ ≤ ‖e om‖ * ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 x z‖ := by
  have hrepr : om = ∑ j : Fin N, (e om j) • e.symm (EuclideanSpace.single j (1 : ℝ)) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    have h := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (e om)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h.symm
  have hval : om.1 x z = ∑ j : Fin N, ((e om j : ℝ) : ℂ) * (e.symm (EuclideanSpace.single j (1 : ℝ))).1 x z := by
    conv_lhs => rw [hrepr]
    simp [Complex.real_smul]
  rw [hval]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (e om) j) (norm_nonneg _)

/-- **`D` at the image-point chart equals `D` of the expression in any chart `c` containing the image.**
For `p = φ_x⁻¹ z` with `f p` in the source of the chart at `c`: `localMapExprAt f x z = σ ∘ g` near `z`,
`g = φ_c ∘ f ∘ φ_x⁻¹`, `σ = φ_{f p} ∘ φ_c⁻¹` holomorphic, so `∂ , ∂̄` get the same factor `σ'` (the proof of
`utm_d_exprAt` with an arbitrary chart centre `c` instead of `f x`). -/
theorem s29_e12_exprAt_gen {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {f : X → Y} (hf : Continuous f) (x : X) (c : Y) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hfz : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ c).source) :
    dilatationQuotient (localMapExprAt f x z) z =
      dilatationQuotient (fun w => chartAt ℂ c (f ((chartAt ℂ x).symm w))) z := by
  set p := (chartAt ℂ x).symm z with hp
  set g : ℂ → ℂ := fun w => chartAt ℂ c (f ((chartAt ℂ x).symm w)) with hg
  set b := g z with hb
  have hbt : b ∈ (chartAt ℂ c).target := (chartAt ℂ c).map_source hfz
  have hbs0 : (chartAt ℂ c).symm b = f p := (chartAt ℂ c).left_inv hfz
  have hbs : (chartAt ℂ c).symm b ∈ (chartAt ℂ (f p)).source := by
    rw [hbs0]; exact mem_chart_source ℂ (f p)
  set σ := chartTransition (f p) c with hσ
  obtain ⟨hσd, hσ0⟩ := s23_transition (f p) c hbt hbs
  obtain ⟨hm1, hm2, -⟩ := s23_transition_mem hbt hbs
  have hk : DifferentiableAt ℂ (chartTransition c (f p)) (σ b) :=
    s23_transition_differentiableAt c (f p) hm1 hm2
  have hkh := s23_transition_inv (f p) c hbt hbs
  have hgc : ContinuousAt g z := by
    have h1 : ContinuousAt (fun w => f ((chartAt ℂ x).symm w)) z :=
      hf.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
    exact ContinuousAt.comp (g := chartAt ℂ c) (f := fun w => f ((chartAt ℂ x).symm w))
      ((chartAt ℂ c).continuousAt hfz) h1
  have hGeq : localMapExprAt f x z =ᶠ[𝓝 z] σ ∘ g := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm
      (hf.isOpen_preimage _ (chartAt ℂ c).open_source)).mem_nhds ⟨hz, hfz⟩] with w hw
    have hw2 : f ((chartAt ℂ x).symm w) ∈ (chartAt ℂ c).source := hw.2
    simp only [localMapExprAt, hσ, hg, Function.comp_apply, chartTransition]
    rw [(chartAt ℂ c).left_inv hw2]
  obtain ⟨hW1, hW2⟩ := s23_wirtinger_comp_left hgc hσd hk hkh
  have e1 : dz (localMapExprAt f x z) z = deriv σ b * dz g z := by
    rw [← hW1]; unfold dz; rw [hGeq.fderiv_eq]
  have e2 : dzbar (localMapExprAt f x z) z = deriv σ b * dzbar g z := by
    rw [← hW2]; unfold dzbar; rw [hGeq.fderiv_eq]
  have hc : ‖deriv σ b‖ ≠ 0 := norm_ne_zero_iff.2 hσ0
  unfold dilatationQuotient complexDilatation
  rw [norm_div, e1, e2, norm_mul, norm_mul, mul_div_mul_left _ _ hc, ← norm_div]

/-- **Measurability of `D` read at the image-point chart.**  `Y` compact is covered by finitely many charts `c`; on
the open set where `f(φ_x⁻¹ z)` lies in the chart at `c`, `D` is `D` of the fixed function `φ_c ∘ f ∘ φ_x⁻¹`
(`s29_e12_exprAt_gen`), which is measurable (`s29_e7_measurable_D`). -/
theorem s29_e12_measurable_D_at {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y] {f : X → Y} (hf : Continuous f) (x : X) :
    AEMeasurable (fun z => dilatationQuotient (localMapExprAt f x z) z)
      (volume.restrict (chartAt ℂ x).target) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun c : Y => (chartAt ℂ c).source)
    (fun c => (chartAt ℂ c).open_source) (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source ℂ y⟩)
  set E : Y → Set ℂ := fun c => (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' (chartAt ℂ c).source)
    with hE
  have hEo : ∀ c, IsOpen (E c) := fun c =>
    (chartAt ℂ x).isOpen_inter_preimage_symm (hf.isOpen_preimage _ (chartAt ℂ c).open_source)
  have hcover : (chartAt ℂ x).target = ⋃ c : s, E c.1 := by
    ext z
    constructor
    · intro hz
      have := hs (mem_univ (f ((chartAt ℂ x).symm z)))
      simp only [mem_iUnion] at this
      obtain ⟨c, hcs, hc⟩ := this
      exact mem_iUnion.2 ⟨⟨c, hcs⟩, ⟨hz, hc⟩⟩
    · intro hz
      obtain ⟨c, hc⟩ := mem_iUnion.1 hz
      exact hc.1
  rw [hcover]
  refine aemeasurable_iUnion_iff.2 fun c => ?_
  set c := c.1
  have hae : (fun z => dilatationQuotient (localMapExprAt f x z) z) =ᵐ[volume.restrict (E c)]
      (fun z => dilatationQuotient (fun w => chartAt ℂ c (f ((chartAt ℂ x).symm w))) z) := by
    refine (ae_restrict_iff' (hEo c).measurableSet).2 (ae_of_all _ fun z hz => ?_)
    exact s29_e12_exprAt_gen hf x c hz.1 hz.2
  exact ((s29_e7_measurable_D _).aemeasurable).congr hae.symm

/-- **Null sets are chart independent.**  If `B ⊆ X` and every `p` has an open neighbourhood `W p` inside its chart
source with `φ_p (B ∩ W p)` null, then `φ_x (B ∩ source_x)` is null for every chart `x` (finitely many `W p` cover the
compact `X`; the transitions are differentiable and so map null sets to null sets). -/
theorem s29_e12_null_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [CompactSpace X] {B : Set X} (W : X → Set X) (hWo : ∀ p, IsOpen (W p)) (hWp : ∀ p, p ∈ W p)
    (hWs : ∀ p, W p ⊆ (chartAt ℂ p).source) (hB : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0) (x : X) :
    volume (chartAt ℂ x '' (B ∩ (chartAt ℂ x).source)) = 0 := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun p _ => mem_iUnion.2 ⟨p, hWp p⟩)
  have hsub : chartAt ℂ x '' (B ∩ (chartAt ℂ x).source) ⊆
      ⋃ p ∈ t, chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) := by
    rintro _ ⟨q, ⟨hqB, hqs⟩, rfl⟩
    have := ht (mem_univ q)
    simp only [mem_iUnion] at this
    obtain ⟨p, hpt, hqp⟩ := this
    exact mem_biUnion hpt ⟨q, ⟨⟨hqB, hqp⟩, hqs⟩, rfl⟩
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff t.countable_toSet).2 fun p _ => ?_
  set A : Set ℂ := chartAt ℂ p '' (B ∩ W p ∩ (chartAt ℂ x).source) with hAdef
  have hA0 : volume A = 0 :=
    measure_mono_null (image_mono (f := chartAt ℂ p)
      (show B ∩ W p ∩ (chartAt ℂ x).source ⊆ B ∩ W p from fun q hq => ⟨hq.1.1, hq.1.2⟩)) (hB p)
  have himg : chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) = chartTransition x p '' A := by
    ext w
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨chartAt ℂ p q, ⟨q, hq, rfl⟩, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q, hq, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
  rw [himg]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hA0
  rintro _ ⟨q, hq, rfl⟩
  have hz : chartAt ℂ p q ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (hWs p hq.1.2)
  have hzx : (chartAt ℂ p).symm (chartAt ℂ p q) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    exact hq.2
  exact ((s23_transition_differentiableAt x p hz hzx).restrictScalars ℝ).differentiableWithinAt

/-- `D(g) ≤ K` a.e. on the domain of a `K`-quasiconformal local expression. -/
theorem s29_e12_D_le_ae_local {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K) :
    ∀ᵐ z ∂(volume.restrict D), dilatationQuotient g z ≤ K := by
  filter_upwards [thm9_4_dilatation_ae hg, thm9_6_cor2_jacobian_pos hg] with z h1 h2
  have hlt : ‖dzbar g z‖ < ‖dz g z‖ := by
    unfold jacobian at h2
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have ha : 0 < ‖dz g z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  unfold dilatationQuotient complexDilatation
  rw [norm_div]
  have e1 : 1 + ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ + ‖dzbar g z‖) / ‖dz g z‖ := by field_simp
  have e2 : 1 - ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ - ‖dzbar g z‖) / ‖dz g z‖ := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ ha.ne', div_le_iff₀ (sub_pos.2 hlt)]
  exact h1

/-- **`D[h] ≤ K` almost everywhere in every chart** for a `K`-q.c. map `h` of closed surfaces, read at the image-point
chart (cover `X` by the open sets `U_p ∩ h⁻¹ U_{h p}`, where `D_at` is `D` of `localMapExpr h p`;
`s29_e12_null_cover`, `s29_e7_D_inv`). -/
theorem s29_e12_D_le_ae {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [CompactSpace X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {h : X ≃ₜ Y} {K : ℝ}
    (hh : IsKQCRS h K) (x : X) :
    ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      dilatationQuotient (localMapExprAt h x z) z ≤ K := by
  set B : Set X := {p | ¬ (dilatationQuotient (localMapExpr h p) (chartAt ℂ p p) ≤ K)} with hB
  set W : X → Set X := fun p => (chartAt ℂ p).source ∩ h ⁻¹' (chartAt ℂ (h p)).source with hW
  have hWo : ∀ p, IsOpen (W p) := fun p =>
    (chartAt ℂ p).open_source.inter (h.continuous.isOpen_preimage _ (chartAt ℂ (h p)).open_source)
  have hWp : ∀ p, p ∈ W p := fun p => ⟨mem_chart_source ℂ p, mem_chart_source ℂ (h p)⟩
  have hWs : ∀ p, W p ⊆ (chartAt ℂ p).source := fun p => inter_subset_left
  have hBnull : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0 := by
    intro p
    have hae := s29_e12_D_le_ae_local (hh.2 p)
    have hdom : MeasurableSet (localMapDomain h p) := (s23_localMapDomain_isOpen h.continuous p).measurableSet
    have hnull : volume {z | ¬ (z ∈ localMapDomain h p →
        dilatationQuotient (localMapExpr h p) z ≤ K)} = 0 :=
      (ae_restrict_iff' hdom).1 hae |> fun h' => by simpa [ae_iff] using h'
    refine measure_mono_null ?_ hnull
    rintro _ ⟨q, ⟨hqB, hqW⟩, rfl⟩
    have hqs : q ∈ (chartAt ℂ p).source := hqW.1
    have hz : chartAt ℂ p q ∈ localMapDomain h p := by
      refine ⟨(chartAt ℂ p).map_source hqs, ?_⟩
      show h ((chartAt ℂ p).symm (chartAt ℂ p q)) ∈ (chartAt ℂ (h p)).source
      rw [(chartAt ℂ p).left_inv hqs]
      exact hqW.2
    intro hcontra
    apply hqB
    have h1 := s29_e7_D_inv (⇑h) p (z := chartAt ℂ p q) ((chartAt ℂ p).map_source hqs)
    rw [(chartAt ℂ p).left_inv hqs] at h1
    have h2 := s29_e12_exprAt_gen h.continuous p (h p) (z := chartAt ℂ p q)
      ((chartAt ℂ p).map_source hqs) (by rw [(chartAt ℂ p).left_inv hqs]; exact hqW.2)
    calc dilatationQuotient (localMapExpr h q) (chartAt ℂ q q) =
          dilatationQuotient (localMapExprAt (⇑h) p (chartAt ℂ p q)) (chartAt ℂ p q) := h1.symm
      _ = dilatationQuotient (localMapExpr h p) (chartAt ℂ p q) := h2
      _ ≤ K := hcontra hz
  have hnullx := s29_e12_null_cover W hWo hWp hWs hBnull x
  refine (ae_restrict_iff' (chartAt ℂ x).open_target.measurableSet).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ hnullx
  intro z hz
  obtain ⟨hzt, hnot⟩ := not_imp.1 hz
  have hqs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hzt
  refine ⟨(chartAt ℂ x).symm z, ⟨?_, hqs⟩, (chartAt ℂ x).right_inv hzt⟩
  intro hle
  apply hnot
  rw [s29_e7_D_inv (⇑h) x hzt]
  exact hle

/-- `quadDiffNorm` is the partition sum for **any** chart partition. -/
theorem s29_e12_psum {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {q : X → ℂ → ℂ} (hq : IsHolQuadDiff q) {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    quadDiffNorm q = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖q (x i) z‖ := by
  have := s26v_surfaceIntegral_eq_tsum hq (fun _ => (1 : ℝ≥0∞)) hP
  unfold quadDiffNorm
  simpa only [one_mul] using this

/-- `|q_x|` is a.e.-measurable on a measurable subset of the chart target. -/
theorem s29_e12_meas_norm {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {q : X → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (x : X) {E : Set ℂ} (hEm : MeasurableSet E) (hE : E ⊆ (chartAt ℂ x).target) :
    AEMeasurable (fun z => ENNReal.ofReal ‖q x z‖) (volume.restrict E) := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : X, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hc : ContinuousOn (q x) E := (hq'.2 x).continuousOn.mono hE
  exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hEm).norm

/-- The pieces of a chart partition lie in the chart targets. -/
theorem s29_e12_piece_sub {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {x : ℕ → X} {P : ℕ → Set X}
    (hP : IsChartPartition X x P) (i : ℕ) : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := by
  rintro _ ⟨a, ha, rfl⟩
  exact (chartAt ℂ (x i)).map_source ((hP.1 i).1 ha)

/-- `Σᵢ ∫_{φᵢ Pᵢ} Σⱼ |bⱼ| = Σⱼ ‖bⱼ‖`. -/
theorem s29_e12_Gsum {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {N : ℕ}
    (e : (holQuadDiffSubmodule X).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ =
      ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := by
  have hint : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ =
      ∑ j : Fin N, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := fun i =>
    lintegral_finsetSum' _ fun j _ => s29_e12_meas_norm (e.symm _).2 (x i) (hP.1 i).2
      (s29_e12_piece_sub hP i)
  simp only [hint]
  rw [Summable.tsum_finsetSum (fun j _ => ENNReal.summable)]
  exact Finset.sum_congr rfl fun j _ => (s29_e12_psum (e.symm _).2 hP).symm

/-- **The Lipschitz-type estimate for the L¹ norm on `Q(X)`**: `‖ω‖ ≤ ‖ω'‖ + ‖e (ω - ω')‖ · A`,
`A = Σⱼ ‖bⱼ‖ < ∞`. -/
theorem s29_e12_key {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {N : ℕ}
    (e : (holQuadDiffSubmodule X).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P)
    (om om' : (holQuadDiffSubmodule X).restrictScalars ℝ) :
    quadDiffNorm om.1 ≤ quadDiffNorm om'.1 + ENNReal.ofReal ‖e (om - om')‖ *
      ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := by
  rw [s29_e12_psum om.2 hP, s29_e12_psum om'.2 hP, ← s29_e12_Gsum e hP, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left' (s29_e12_meas_norm om'.2 (x i) (hP.1 i).2 (s29_e12_piece_sub hP i))]
  refine lintegral_mono fun z => ?_
  have hd := s29_e12_dom e (om - om') (x i) z
  have hsub : (om - om').1 (x i) z = om.1 (x i) z - om'.1 (x i) z := rfl
  rw [hsub] at hd
  have h1 : ‖om.1 (x i) z‖ ≤ ‖om'.1 (x i) z‖ + ‖e (om - om')‖ *
      ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := by
    calc ‖om.1 (x i) z‖ = ‖om'.1 (x i) z + (om.1 (x i) z - om'.1 (x i) z)‖ := by rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right hd _)
  calc ENNReal.ofReal ‖om.1 (x i) z‖
      ≤ ENNReal.ofReal (‖om'.1 (x i) z‖ + ‖e (om - om')‖ *
          ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal ‖om'.1 (x i) z‖ + ENNReal.ofReal ‖e (om - om')‖ *
          ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := by
        refine (ENNReal.ofReal_add_le).trans (add_le_add_right (le_of_eq ?_) _)
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_sum_of_nonneg fun j _ => norm_nonneg _]
    _ = _ := by rw [add_comm]

/-- **A uniform positive lower bound for the L¹ norm on the unit sphere of `e`.** -/
theorem s29_e12_lower {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [CompactSpace X] [Nonempty X] {N : ℕ}
    (e : (holQuadDiffSubmodule X).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)) :
    ∃ c : ℝ, 0 < c ∧ ∀ om : (holQuadDiffSubmodule X).restrictScalars ℝ, ‖e om‖ = 1 →
      ENNReal.ofReal c ≤ quadDiffNorm om.1 := by
  by_cases hne : ∃ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1
  swap
  · exact ⟨1, one_pos, fun om hom => absurd ⟨e om, hom⟩ hne⟩
  obtain ⟨x, P, hP⟩ := s26_exists_chartPartition' (S := X)
  set A : ℝ≥0∞ := ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 with hA
  have hAfin : A ≠ ⊤ := (ENNReal.sum_lt_top.2 fun j _ => s26_quadDiffNorm_lt_top (e.symm _).2).ne
  set f : EuclideanSpace ℝ (Fin N) → ℝ := fun v => (quadDiffNorm (e.symm v).1).toReal with hf
  have hfin : ∀ v, quadDiffNorm (e.symm v).1 ≠ ⊤ := fun v => (s26_quadDiffNorm_lt_top (e.symm v).2).ne
  have hLip : ∀ v v', f v ≤ f v' + A.toReal * ‖v - v'‖ := by
    intro v v'
    have h := s29_e12_key e hP (e.symm v) (e.symm v')
    rw [← map_sub, LinearEquiv.apply_symm_apply] at h
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin v', ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin⟩) h
    rw [ENNReal.toReal_add (hfin v') (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    linarith
  have hlip : LipschitzWith A.toReal.toNNReal f := by
    refine LipschitzWith.of_dist_le_mul fun v v' => ?_
    rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg, Real.dist_eq, dist_eq_norm, abs_le]
    constructor
    · have := hLip v' v
      rw [norm_sub_rev] at this
      linarith
    · have := hLip v v'
      linarith
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).exists_isMinOn
    (by obtain ⟨v, hv⟩ := hne; exact ⟨v, by simpa using hv⟩) hlip.continuous.continuousOn
  have hv₀n : ‖v₀‖ = 1 := by simpa using hv₀
  have hpos : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 < f v := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hne0 : (e.symm v).1 ≠ 0 := by
      intro h0
      apply hv0
      have : e.symm v = 0 := Subtype.ext h0
      simpa using congrArg e this
    exact ENNReal.toReal_pos (s26_quadDiffNorm_pos (e.symm v).2 hne0) (hfin v)
  refine ⟨f v₀, hpos v₀ hv₀n, fun om hom => ?_⟩
  have h1 : f v₀ ≤ f (e om) := hmin (by simpa using hom)
  have h2 : f (e om) = (quadDiffNorm om.1).toReal := by simp [hf]
  rw [h2] at h1
  calc ENNReal.ofReal (f v₀) ≤ ENNReal.ofReal (quadDiffNorm om.1).toReal := ENNReal.ofReal_le_ofReal h1
    _ = quadDiffNorm om.1 := ENNReal.ofReal_toReal (by simpa using hfin (e om))

/-- **[stub B] Finite-dimensional dominated convergence.**  Let `S` be a closed surface of genus `g`, `e` a linear
isomorphism of `Q(S)` with `ℝ^N`, `hₙ : S → Sₙ` uniformly `K`-q.c. (eventually) with `D[hₙ] → 1` a.e. in every chart, and
`ωₙ ∈ Q(S)` with `‖e ωₙ‖ = 1`.  Then for every `ε > 0` eventually `∬ D[hₙ] dA_{ωₙ} ≤ (1 + ε) ‖ωₙ‖`.
*Route:* `ω = Σ cⱼ bⱼ` for the basis `bⱼ = e⁻¹ eⱼ`, `|cⱼ| ≤ 1`, so `|ωₙ| ≤ G := Σⱼ |bⱼ|` in every chart with
`Σᵢ ∫ G < ∞` (`Σⱼ ‖bⱼ‖`, `s26v_surfaceIntegral_eq_tsum`); dominated convergence for `(D[hₙ] - 1) G` on a chart partition
(`D ≤ K` a.e. by `utm_d_ae_good`) gives `ε'ₙ := ∬ (D[hₙ] - 1) G → 0`; and `‖ωₙ‖ ≥ c > 0` on the unit sphere (a fixed chart
disc `B`: `ω ↦ ∫_B |ω|` is continuous and positive on the compact sphere, `s26u_zeros_countable`, `utm_d_good_partition`
with prescribed first piece). -/
theorem s29_e12_dct {X : ClosedRS.{u}} {g : ℕ}
    (e : (holQuadDiffSubmodule X.carrier).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {Y : ℕ → ClosedRS.{u}} (h : ∀ n, X.carrier ≃ₜ (Y n).carrier) {K : ℝ}
    (hK : ∀ᶠ n in atTop, IsKQCRS (h n) K)
    (hconv : ∀ x : X.carrier, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      Tendsto (fun n => dilatationQuotient (localMapExprAt (h n) x z) z) atTop (𝓝 1))
    (om : ℕ → (holQuadDiffSubmodule X.carrier).restrictScalars ℝ) (hom : ∀ n, ‖e (om n)‖ = 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      surfaceIntegral (om n).1 (fun x z =>
          ENNReal.ofReal (dilatationQuotient (localMapExprAt (h n) x z) z)) ≤
        ENNReal.ofReal (1 + ε) * quadDiffNorm (om n).1 := by
  classical
  have : Nonempty X.carrier := ConnectedSpace.toNonempty
  obtain ⟨c, hc, hlow⟩ := s29_e12_lower e
  obtain ⟨x, P, hP⟩ := s26_exists_chartPartition' (S := X.carrier)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hK
  set G : ℕ → ℂ → ℝ≥0∞ := fun i z =>
    ∑ j : Fin (6 * g - 6), ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ with hG
  have hA : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z =
      ∑ j : Fin (6 * g - 6), quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := s29_e12_Gsum e hP
  have hAfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z ≠ ⊤ := by
    rw [hA]
    exact (ENNReal.sum_lt_top.2 fun j _ => s26_quadDiffNorm_lt_top (e.symm _).2).ne
  have hGfin : ∀ i z, G i z ≠ ⊤ := fun i z => ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
  have hgi : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hAfin (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, G i z) i)
  have hGmeas : ∀ i, AEMeasurable (G i) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i =>
    Finset.aemeasurable_fun_sum _ fun j _ =>
      s29_e12_meas_norm (e.symm _).2 (x i) (hP.1 i).2 (s29_e12_piece_sub hP i)
  set Dn : ℕ → ℕ → ℂ → ℝ := fun n i z => dilatationQuotient (localMapExprAt (h n) (x i) z) z with hDn
  set F : ℕ → ℕ → ℂ → ℝ≥0∞ := fun n i z => ENNReal.ofReal (Dn n i z - 1) * G i z with hF
  set a : ℕ → ℕ → ℝ≥0∞ := fun n i => ∫⁻ z in chartAt ℂ (x i) '' P i, F n i z with ha
  -- (1) for each piece, the remainders tend to `0` (dominated convergence on the piece)
  have hlimi : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 0) := by
    intro i
    have hmeasD : ∀ n, AEMeasurable (fun z => Dn n i z) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      fun n => (s29_e12_measurable_D_at (h n).continuous (x i)).mono_set (s29_e12_piece_sub hP i)
    have hmeasF : ∀ n, AEMeasurable (F n i) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun n =>
      (ENNReal.measurable_ofReal.comp_aemeasurable ((hmeasD n).sub_const 1)).mul (hGmeas i)
    have hbound : ∀ n, N0 ≤ n → ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        F n i z ≤ ENNReal.ofReal (K - 1) * G i z := by
      intro n hn
      have h1 := s29_e12_D_le_ae (hN0 n hn) (x i)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) h1] with z hz
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    have hfinb : ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (K - 1) * G i z ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgi i)
    have hlim : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        Tendsto (fun n => F n i z) atTop (𝓝 0) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) (hconv (x i))] with z hz
      have h1 : Tendsto (fun n => ENNReal.ofReal (Dn n i z - 1)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (hz.sub_const 1)
        simpa using this
      have := ENNReal.Tendsto.mul_const h1 (Or.inr (hGfin i z))
      simpa using this
    have hshift : Tendsto (fun n => a (n + N0) i) atTop (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict (chartAt ℂ (x i) '' P i)) (F := fun n z => F (n + N0) i z)
        (f := fun _ => (0 : ℝ≥0∞)) (fun z => ENNReal.ofReal (K - 1) * G i z)
        (fun n => hmeasF _) (fun n => hbound (n + N0) (by omega)) hfinb
        (hlim.mono fun z hz => hz.comp (tendsto_add_atTop_nat N0))
      simpa using this
    exact (tendsto_add_atTop_iff_nat N0).1 hshift
  -- (2) the series of remainders tends to `0` (dominated convergence for the counting measure)
  have hR : Tendsto (fun n => ∑' i, a n i) atTop (𝓝 0) := by
    have hbi : ∀ n, N0 ≤ n → ∀ i, a n i ≤ ENNReal.ofReal (K - 1) *
        ∫⁻ z in chartAt ℂ (x i) '' P i, G i z := by
      intro n hn i
      have h1 := s29_e12_D_le_ae (hN0 n hn) (x i)
      calc a n i ≤ ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (K - 1) * G i z := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) h1] with z hz
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hfin : (∫⁻ i, ENNReal.ofReal (K - 1) * (∫⁻ z in chartAt ℂ (x i) '' P i, G i z) ∂Measure.count) ≠ ⊤ := by
      rw [lintegral_count, ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
    have hser : Tendsto (fun n => ∫⁻ i, a (n + N0) i ∂Measure.count) atTop
        (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂Measure.count)) :=
      tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
        (F := fun n (i : ℕ) => a (n + N0) i)
        (f := fun _ => (0 : ℝ≥0∞))
        (fun i => ENNReal.ofReal (K - 1) * ∫⁻ z in chartAt ℂ (x i) '' P i, G i z)
        (fun n => Measurable.of_discrete) (fun n => ae_of_all _ fun i => hbi (n + N0) (by omega) i) hfin
        (ae_of_all _ fun i => (hlimi i).comp (tendsto_add_atTop_nat N0))
    simp only [lintegral_count, lintegral_zero] at hser
    exact (tendsto_add_atTop_iff_nat N0).1 hser
  -- (3) the estimate for each `n`
  have hεc : 0 < ENNReal.ofReal (ε * c) := ENNReal.ofReal_pos.2 (mul_pos hε hc)
  filter_upwards [hR.eventually (gt_mem_nhds hεc)] with n hRn
  have h1 : surfaceIntegral (om n).1 (fun x z =>
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (h n) x z) z)) ≤
      quadDiffNorm (om n).1 + ∑' i, a n i := by
    rw [s29_e7_D_partition (h n) (om n).2 hP, s29_e12_psum (om n).2 hP, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [ha]
    simp only [hF]
    rw [← lintegral_add_left' (s29_e12_meas_norm (om n).2 (x i) (hP.1 i).2 (s29_e12_piece_sub hP i))]
    refine lintegral_mono fun z => ?_
    have hd := s29_e12_dom e (om n) (x i) z
    rw [hom n, one_mul] at hd
    have hQG : ENNReal.ofReal ‖(om n).1 (x i) z‖ ≤ G i z := by
      refine (ENNReal.ofReal_le_ofReal hd).trans (le_of_eq ?_)
      rw [hG]
      exact ENNReal.ofReal_sum_of_nonneg fun j _ => norm_nonneg _
    have hD : ENNReal.ofReal (Dn n i z) ≤ 1 + ENNReal.ofReal (Dn n i z - 1) := by
      calc ENNReal.ofReal (Dn n i z) = ENNReal.ofReal (1 + (Dn n i z - 1)) := by rw [add_sub_cancel]
        _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (Dn n i z - 1) := ENNReal.ofReal_add_le
        _ = 1 + ENNReal.ofReal (Dn n i z - 1) := by rw [ENNReal.ofReal_one]
    calc ENNReal.ofReal (Dn n i z) * ENNReal.ofReal ‖(om n).1 (x i) z‖
        ≤ (1 + ENNReal.ofReal (Dn n i z - 1)) * ENNReal.ofReal ‖(om n).1 (x i) z‖ :=
          mul_le_mul' hD le_rfl
      _ = ENNReal.ofReal ‖(om n).1 (x i) z‖ + ENNReal.ofReal (Dn n i z - 1) *
            ENNReal.ofReal ‖(om n).1 (x i) z‖ := by rw [add_mul, one_mul]
      _ ≤ ENNReal.ofReal ‖(om n).1 (x i) z‖ + ENNReal.ofReal (Dn n i z - 1) * G i z :=
          add_le_add_right (mul_le_mul' le_rfl hQG) _
  calc _ ≤ quadDiffNorm (om n).1 + ∑' i, a n i := h1
    _ ≤ quadDiffNorm (om n).1 + ENNReal.ofReal (ε * c) := add_le_add_right hRn.le _
    _ ≤ quadDiffNorm (om n).1 + ENNReal.ofReal ε * quadDiffNorm (om n).1 := by
        refine add_le_add_right ?_ _
        rw [ENNReal.ofReal_mul hε.le]
        exact mul_le_mul' le_rfl (hlow (om n) (hom n))
    _ = ENNReal.ofReal (1 + ε) * quadDiffNorm (om n).1 := by
        rw [ENNReal.ofReal_add zero_le_one hε.le, ENNReal.ofReal_one, add_mul, one_mul, add_comm]

/-- **The analysis behind `D → 1`**: if `qₙ → q ≠ 0` and `kₙ → k < 1` then the bound `‖kₙ q̄ₙ/|qₙ| - k q̄/|q|‖/(1 - kₙ k)`
tends to `0`, so any `0 ≤ mₙ ≤` it has `(1 + mₙ)/(1 - mₙ) → 1`. -/
theorem s29_e12_ae_analysis {q : ℂ} {qn : ℕ → ℂ} {k : ℝ} {kn : ℕ → ℝ} {m : ℕ → ℝ} (hq0 : q ≠ 0)
    (hconv : Tendsto qn atTop (𝓝 q)) (hk : Tendsto kn atTop (𝓝 k)) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hm0 : ∀ n, 0 ≤ m n)
    (hm : ∀ n, m n ≤ ‖(kn n : ℂ) * conj (qn n) / (‖qn n‖ : ℂ) - (k : ℂ) * conj q / (‖q‖ : ℂ)‖ /
      (1 - kn n * k)) :
    Tendsto (fun n => (1 + m n) / (1 - m n)) atTop (𝓝 1) := by
  have hφ : ContinuousAt (fun w : ℂ => conj w / (‖w‖ : ℂ)) q := by
    refine (Complex.continuous_conj.continuousAt).div
      (Complex.continuous_ofReal.comp continuous_norm).continuousAt ?_
    simpa using hq0
  have h1 : Tendsto (fun n => conj (qn n) / (‖qn n‖ : ℂ)) atTop (𝓝 (conj q / (‖q‖ : ℂ))) :=
    hφ.tendsto.comp hconv
  have h2 : Tendsto (fun n => (kn n : ℂ) * (conj (qn n) / (‖qn n‖ : ℂ))) atTop
      (𝓝 ((k : ℂ) * (conj q / (‖q‖ : ℂ)))) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hk).mul h1
  have h3 : Tendsto (fun n => ‖(kn n : ℂ) * conj (qn n) / (‖qn n‖ : ℂ) - (k : ℂ) * conj q / (‖q‖ : ℂ)‖)
      atTop (𝓝 0) := by
    have := (h2.sub_const ((k : ℂ) * (conj q / (‖q‖ : ℂ)))).norm
    simp only [sub_self, norm_zero] at this
    refine this.congr fun n => ?_
    rw [mul_div_assoc, mul_div_assoc]
  have hden : Tendsto (fun n => 1 - kn n * k) atTop (𝓝 (1 - k * k)) :=
    tendsto_const_nhds.sub (hk.mul_const k)
  have hkk : 1 - k * k ≠ 0 := by nlinarith
  have hb : Tendsto (fun n => ‖(kn n : ℂ) * conj (qn n) / (‖qn n‖ : ℂ) - (k : ℂ) * conj q / (‖q‖ : ℂ)‖ /
      (1 - kn n * k)) atTop (𝓝 0) := by
    have := h3.div hden hkk
    rw [zero_div] at this
    exact this
  have hmz : Tendsto m atTop (𝓝 0) := squeeze_zero hm0 hm hb
  have h1 : Tendsto (fun n => 1 + m n) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hmz
  have h2 : Tendsto (fun n => 1 - m n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hmz
  have := h1.div h2 (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [add_zero, sub_zero, div_one] at this
  exact this

/-- **[stub C] `D[fₙ ∘ f⁻¹] → 1` almost everywhere** (book (29.3)–(29.4)).  For Teichmüller maps `e : S₀ → S` and
`eₙ : S₀ → Sₙ` with initial differentials `qₙ → q` pointwise and `kₙ → k`, the dilatation quotient of `eₙ ∘ e⁻¹` read at the
image-point chart tends to `1` for a.e. point of every chart of `S`.
*Route:* `eq29_3` gives, for a.e. `z` in the chart of `x' ∈ S₀`, `‖μ_{hₙ}(L z)‖ ≤ ‖kₙ q̄ₙ/|qₙ| - k q̄/|q|‖ / (1 - kₙ k) → 0`
(`q ≠ 0`, `qₙ ≠ 0` off a countable set, `qₙ → q`), so `D[hₙ](L z) → 1`; the exceptional set is carried from `S₀` to `S` by the
quasiconformal `L = localMapExpr e x'` (`s26w_lintegral_image`: `vol L(N) = ∫_N J = 0`), and `D` at the image-point chart is
chart independent (`s29_e7_D_inv`) so every chart of `S` is covered by the images of countably many charts of `S₀`. -/
theorem s29_e12_ae {X : ClosedRS.{u}} {e : S₀ ≃ₜ X.carrier} {q : S₀ → ℂ → ℂ} {q' : X.carrier → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap e q q' k) {Y : ℕ → ClosedRS.{u}} {en : ∀ n, S₀ ≃ₜ (Y n).carrier}
    {qn : ℕ → S₀ → ℂ → ℂ} {qn' : ∀ n, (Y n).carrier → ℂ → ℂ} {kn : ℕ → ℝ}
    (hfn : ∀ n, IsTeichmullerMap (en n) (qn n) (qn' n) (kn n))
    (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) (hkconv : Tendsto kn atTop (𝓝 k)) :
    ∀ x : X.carrier, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      Tendsto (fun n => dilatationQuotient (localMapExprAt (e.symm.trans (en n)) x z) z) atTop (𝓝 1) := by
  classical
  have hq := hf.initial
  have hne := hf.initial_ne
  have hk0 := hf.k_nonneg
  have hk1 := hf.k_lt_one
  obtain ⟨K, hK⟩ := hf.qc
  -- the exceptional points of `X`
  set B : Set X.carrier := {p | ¬ Tendsto (fun n => dilatationQuotient
    (localMapExpr (e.symm.trans (en n)) p) (chartAt ℂ p p)) atTop (𝓝 1)} with hB
  set W : X.carrier → Set X.carrier := fun p =>
    e '' ((chartAt ℂ (e.symm p)).source ∩ e ⁻¹' (chartAt ℂ p).source) with hW
  have hWo : ∀ p, IsOpen (W p) := fun p => e.isOpenMap _
    ((chartAt ℂ (e.symm p)).open_source.inter (e.continuous.isOpen_preimage _ (chartAt ℂ p).open_source))
  have hWp : ∀ p, p ∈ W p := fun p =>
    ⟨e.symm p, ⟨mem_chart_source ℂ _, by simpa using mem_chart_source ℂ p⟩, e.apply_symm_apply p⟩
  have hWs : ∀ p, W p ⊆ (chartAt ℂ p).source := by
    rintro p _ ⟨q₀, ⟨-, hq₀⟩, rfl⟩
    exact hq₀
  have hBnull : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0 := by
    intro p
    obtain ⟨x', rfl⟩ := e.surjective p
    set L := localMapExpr e x' with hL
    set dom := localMapDomain e x' with hdom
    have hdomo : IsOpen dom := s23_localMapDomain_isOpen e.continuous x'
    have hz1 : ∀ n, ∀ᵐ z ∂(volume.restrict dom),
        ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k) :=
      fun n => eq29_3 hf (hfn n) x'
    have hzq : ∀ᵐ z ∂(volume.restrict dom), q x' z ≠ 0 := by
      have h0 : volume {z | z ∈ (chartAt ℂ x').target ∧ q x' z = 0} = 0 :=
        (s26u_zeros_countable hq hne x').measure_zero _
      filter_upwards [ae_restrict_mem hdomo.measurableSet,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hzd hz hq0
      exact hz ⟨hzd.1, hq0⟩
    have hzn : ∀ n, ∀ᵐ z ∂(volume.restrict dom), qn n x' z ≠ 0 := by
      intro n
      have h0 : volume {z | z ∈ (chartAt ℂ x').target ∧ qn n x' z = 0} = 0 :=
        (s26u_zeros_countable (hfn n).initial (hfn n).initial_ne x').measure_zero _
      filter_upwards [ae_restrict_mem hdomo.measurableSet,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hzd hz hq0
      exact hz ⟨hzd.1, hq0⟩
    have hgood : ∀ᵐ z ∂(volume.restrict dom), q x' z ≠ 0 ∧ (∀ n, qn n x' z ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k) := by
      filter_upwards [hzq, ae_all_iff.2 hzn, ae_all_iff.2 hz1] with z a b c using ⟨a, b, c⟩
    set N : Set ℂ := {z | ¬ (z ∈ dom → (q x' z ≠ 0 ∧ (∀ n, qn n x' z ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k)))}
      with hN
    have hN0 : volume N = 0 := by
      have := (ae_restrict_iff' hdomo.measurableSet).1 hgood
      rw [ae_iff] at this
      exact this
    obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN0
    set s : Set ℂ := N' ∩ dom with hs
    have hs0 : volume s = 0 := measure_mono_null inter_subset_left hN'0
    have hinj : InjOn L s := by
      intro z₁ hz₁ z₂ hz₂ h
      have h1 := hz₁.2
      have h2 := hz₂.2
      have h3 : e ((chartAt ℂ x').symm z₁) = e ((chartAt ℂ x').symm z₂) :=
        (chartAt ℂ (e x')).injOn h1.2 h2.2 h
      have h4 := e.injective h3
      calc z₁ = (chartAt ℂ x') ((chartAt ℂ x').symm z₁) := ((chartAt ℂ x').right_inv h1.1).symm
        _ = (chartAt ℂ x') ((chartAt ℂ x').symm z₂) := by rw [h4]
        _ = z₂ := (chartAt ℂ x').right_inv h2.1
    have hLimg : volume (L '' s) = 0 := by
      have h := s26w_lintegral_image (g := L) (D := dom) (K := K)
        (fun z hz => ⟨dom, hdomo, hz, subset_rfl, hK.2 x'⟩) (hN'm.inter hdomo.measurableSet)
        inter_subset_right hinj (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_measure_zero s _ hs0] at h
      simpa using h
    refine measure_mono_null ?_ hLimg
    rintro _ ⟨q₁, ⟨hqB, hqW⟩, rfl⟩
    obtain ⟨q₀, ⟨hq₀s0, hq₀e⟩, rfl⟩ := hqW
    have hq₀s : q₀ ∈ (chartAt ℂ x').source := by simpa [e.symm_apply_apply] using hq₀s0
    have hzt : chartAt ℂ x' q₀ ∈ (chartAt ℂ x').target := (chartAt ℂ x').map_source hq₀s
    have hzd : chartAt ℂ x' q₀ ∈ dom := by
      refine ⟨hzt, ?_⟩
      show e ((chartAt ℂ x').symm (chartAt ℂ x' q₀)) ∈ (chartAt ℂ (e x')).source
      rw [(chartAt ℂ x').left_inv hq₀s]
      exact hq₀e
    have hLz : L (chartAt ℂ x' q₀) = chartAt ℂ (e x') (e q₀) := by
      show (chartAt ℂ (e x')) (e ((chartAt ℂ x').symm (chartAt ℂ x' q₀))) = _
      rw [(chartAt ℂ x').left_inv hq₀s]
    refine ⟨chartAt ℂ x' q₀, (⟨?_, hzd⟩ : chartAt ℂ x' q₀ ∈ N' ∩ dom), hLz⟩
    by_contra hzN
    have hzgood : q x' (chartAt ℂ x' q₀) ≠ 0 ∧ (∀ n, qn n x' (chartAt ℂ x' q₀) ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x')
            (localMapExpr e x' (chartAt ℂ x' q₀))) (localMapExpr e x' (chartAt ℂ x' q₀))‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' (chartAt ℂ x' q₀) -
            teichmullerBeltrami k q x' (chartAt ℂ x' q₀)‖ / (1 - kn n * k) := by
      by_contra hcon
      exact hzN (hNN' (show chartAt ℂ x' q₀ ∈ N from fun hh => hcon (hh hzd)))
    obtain ⟨hz0, -, hzb⟩ := hzgood
    apply hqB
    have hLt : L (chartAt ℂ x' q₀) ∈ (chartAt ℂ (e x')).target := by
      rw [hLz]
      exact (chartAt ℂ (e x')).map_source hq₀e
    have hU : ∀ n, dilatationQuotient (localMapExpr (e.symm.trans (en n)) (e q₀)) (chartAt ℂ (e q₀) (e q₀)) =
        dilatationQuotient (localMapExprAt (e.symm.trans (en n)) (e x') (L (chartAt ℂ x' q₀)))
          (L (chartAt ℂ x' q₀)) := by
      intro n
      rw [s29_e7_D_inv (⇑(e.symm.trans (en n))) (e x') hLt, hLz, (chartAt ℂ (e x')).left_inv hq₀e]
    simp only [hU]
    have := s29_e12_ae_analysis (q := q x' (chartAt ℂ x' q₀)) (qn := fun n => qn n x' (chartAt ℂ x' q₀))
      (k := k) (kn := kn) (m := fun n => ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x')
        (L (chartAt ℂ x' q₀))) (L (chartAt ℂ x' q₀))‖) hz0 (hconv x' _) hkconv hk0 hk1
      (fun n => norm_nonneg _) hzb
    exact this
  have hnull := s29_e12_null_cover W hWo hWp hWs hBnull
  intro x
  refine (ae_restrict_iff' (chartAt ℂ x).open_target.measurableSet).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ (hnull x)
  intro z hz
  obtain ⟨hzt, hnot⟩ := not_imp.1 hz
  have hqs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hzt
  refine ⟨(chartAt ℂ x).symm z, ⟨?_, hqs⟩, (chartAt ℂ x).right_inv hzt⟩
  intro hT
  apply hnot
  have hfun : (fun n => dilatationQuotient (localMapExprAt (e.symm.trans (en n)) x z) z) =
      fun n => dilatationQuotient (localMapExpr (e.symm.trans (en n)) ((chartAt ℂ x).symm z))
        (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) :=
    funext fun n => s29_e7_D_inv (⇑(e.symm.trans (en n))) x hzt
  rw [hfun]
  exact hT

/-- §29.1, (29.1) ⟹ (29.2): if `kₙ → k` and `ωₙ → ω` (coordinates in `Q(S₀)`, equivalently the
local coefficients), then `d_T([Sₙ, fₙ], [S, f]) → 0`. -/
theorem eq29_1_imp_eq29_2 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {qn : ℕ → S₀ → ℂ → ℂ}
    {q : S₀ → ℂ → ℂ} (hqn : ∀ n, IsHolQuadDiff (qn n)) (hq : IsHolQuadDiff q)
    (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) {kn : ℕ → ℝ} {k : ℝ}
    (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1) (hk : 0 ≤ k) (hk' : k < 1) (hkconv : Tendsto kn atTop (𝓝 k))
    {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀} (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n))
    (hp : IsDeformationPoint q k p) :
    Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0) := by
  classical
  -- `hqn`, `hq`, `hkn` follow from `hpn`, `hp` (the deformation data); the statement stays true without them
  have _ := hqn
  have _ := hq
  have _ := hkn
  obtain ⟨X, e, hqc, q', hT, hpX⟩ := hp
  choose Y en hqcn qn' hTn hpXn using hpn
  have hpn' : pn = fun n => (Quot.mk _ (⟨Y n, en n, hqcn n⟩ : MarkedRS S₀) : TeichSpace S₀) := funext hpXn
  subst hpn'
  subst hpX
  have hX : HasGenus X.carrier g := hasGenus_of_homeomorph hS e
  obtain ⟨-, eX, -⟩ := teichDeformationSpace_parameters (S₀ := X.carrier) hg hX
  have hTm : IsTeichmullerMap e q q' k := teichDeformation_isTeichmullerMap hT
  have hTnm : ∀ n, IsTeichmullerMap (en n) (qn n) (qn' n) (kn n) := fun n =>
    teichDeformation_isTeichmullerMap (hTn n)
  -- the extremal data: `ωₙ` on the unit sphere and the main inequality
  choose om hom homI using fun n => s29_e12_main hg hS (⟨X, e, hqc⟩ : MarkedRS S₀) ⟨Y n, en n, hqcn n⟩ eX
  -- the maps `hₙ = fₙ ∘ f⁻¹` are uniformly q.c. (eventually)
  have hKb : ∃ K : ℝ, ∀ᶠ n in atTop, IsKQCRS (e.symm.trans (en n)) K := by
    obtain ⟨K₁, hK₁⟩ := hqc
    have hk1 : k < (k + 1) / 2 := by linarith
    have hev : ∀ᶠ n in atTop, kn n < (k + 1) / 2 := hkconv.eventually (eventually_lt_nhds hk1)
    have hb0 : 0 ≤ (k + 1) / 2 := by linarith
    have hb1 : (k + 1) / 2 < 1 := by linarith
    refine ⟨K₁ * ((1 + (k + 1) / 2) / (1 - (k + 1) / 2)), ?_⟩
    filter_upwards [hev] with n hn
    have hKn : IsKQCRS (en n) ((1 + kn n) / (1 - kn n)) := s26u_isKQCRS (hTn n)
    have hkn0 : 0 ≤ kn n := (hTnm n).k_nonneg
    have hmono : (1 + kn n) / (1 - kn n) ≤ (1 + (k + 1) / 2) / (1 - (k + 1) / 2) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hKn' : IsKQCRS (en n) ((1 + (k + 1) / 2) / (1 - (k + 1) / 2)) :=
      s29_m_isKQCRS_of_le ⟨_, hKn⟩ (hKn.1.trans hmono)
        ((maxDilatationRS_le hKn).trans (ENNReal.ofReal_le_ofReal hmono))
    exact (eq23_4 (s29_m_isKQCRS_symm hK₁) hKn').1
  obtain ⟨K, hK⟩ := hKb
  have hae := s29_e12_ae hTm hTnm hconv hkconv
  have hd0 : ∀ n, 0 ≤ teichDistance (Quot.mk _ (⟨Y n, en n, hqcn n⟩ : MarkedRS S₀))
      (Quot.mk _ (⟨X, e, hqc⟩ : MarkedRS S₀)) := fun n => s29_m_teichDistance_nonneg _ _
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hd0 n), fun a ha => ?_⟩
  have hε : 0 < Real.exp a - 1 := by linarith [Real.add_one_lt_exp ha.ne']
  filter_upwards [s29_e12_dct eX (fun n => e.symm.trans (en n)) hK hae om hom hε] with n hn
  have hIn := homI n
  have hom0 : (om n).1 ≠ 0 := by
    intro h0
    have : om n = 0 := Subtype.ext h0
    have h1 := hom n
    rw [this, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hpos : quadDiffNorm (om n).1 ≠ 0 := s26_quadDiffNorm_pos (om n).2 hom0
  have hfin : quadDiffNorm (om n).1 ≠ ⊤ := (s26_quadDiffNorm_lt_top (om n).2).ne
  have h1 : ENNReal.ofReal (Real.exp (2 * teichDistance (Quot.mk _ (⟨Y n, en n, hqcn n⟩ : MarkedRS S₀))
      (Quot.mk _ (⟨X, e, hqc⟩ : MarkedRS S₀)))) * quadDiffNorm (om n).1 ≤
      ENNReal.ofReal (Real.exp a) * quadDiffNorm (om n).1 := by
    refine hIn.trans (hn.trans (le_of_eq ?_))
    rw [show (1 + (Real.exp a - 1)) = Real.exp a by ring]
  have h2 := (ENNReal.mul_le_mul_iff_left hpos hfin).1 h1
  have h3 := (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos a).le).1 h2
  have h4 := Real.exp_le_exp.1 h3
  linarith [hd0 n]

/-- §29.1, (29.2) ⟹ (29.1): if `d_T([Sₙ, fₙ], [S, f]) → 0` (with `(ωₙ, kₙ)`, `(ω, k)` the
normalized Teichmüller data, `‖e(ωₙ)‖ = ‖e(ω)‖ = 1`), then `kₙ → k` and, when `k ≠ 0`,
`ωₙ → ω` (by compactness of the unit sphere and the first part). -/
theorem eq29_2_imp_eq29_1 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {qn : ℕ → (holQuadDiffSubmodule S₀).restrictScalars ℝ} {q : (holQuadDiffSubmodule S₀).restrictScalars ℝ}
    (hqn : ∀ n, ‖e (qn n)‖ = 1) (hq : ‖e q‖ = 1) {kn : ℕ → ℝ} {k : ℝ} (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1)
    (hk : 0 ≤ k) (hk' : k < 1) {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀}
    (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n)) (hp : IsDeformationPoint q k p)
    (hconv : Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0)) :
    Tendsto kn atTop (𝓝 k) ∧ (k ≠ 0 → Tendsto (fun n => e (qn n)) atTop (𝓝 (e q))) := by
  classical
  have hid : IsQCRS (Homeomorph.refl S₀) := ⟨1, (isKQCRS_one_iff _).2 isBiholomorphic_id⟩
  -- `d_T(base, [S_{q,k}, f]) = ½ log((1+k)/(1-k))`, so `k = ψ(d)` with `ψ d = (e^{2d} - 1)/(e^{2d} + 1)`
  set ψ : ℝ → ℝ := fun d => (Real.exp (2 * d) - 1) / (Real.exp (2 * d) + 1) with hψ
  have hψc : Continuous ψ := by
    refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).div
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).add continuous_const) fun d => ?_
    positivity
  have hψk : ∀ t : ℝ, 0 ≤ t → t < 1 → ψ ((1 / 2) * Real.log ((1 + t) / (1 - t))) = t := by
    intro t ht0 ht1
    have h1 : 0 < 1 - t := by linarith
    have hR : 0 < (1 + t) / (1 - t) := div_pos (by linarith) h1
    simp only [hψ]
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, Real.exp_log hR]
    field_simp
    ring
  have hd : ∀ n, teichDistance (TeichSpace.basePoint hid) (pn n) =
      (1 / 2) * Real.log ((1 + kn n) / (1 - kn n)) := fun n => teichDistance_deformation hg hS hid (hpn n)
  have hd' : teichDistance (TeichSpace.basePoint hid) p = (1 / 2) * Real.log ((1 + k) / (1 - k)) :=
    teichDistance_deformation hg hS hid hp
  have hconv0 : Tendsto (fun n => teichDistance (TeichSpace.basePoint hid) (pn n)) atTop
      (𝓝 (teichDistance (TeichSpace.basePoint hid) p)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hconv
    have h1 := s29_m_teichDistance_triangle (TeichSpace.basePoint hid) (pn n) p
    have h2 := s29_m_teichDistance_triangle (TeichSpace.basePoint hid) p (pn n)
    have h3 := s29_m_teichDistance_symm p (pn n)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hkn' : Tendsto kn atTop (𝓝 k) := by
    have e2 : ψ (teichDistance (TeichSpace.basePoint hid) p) = k := by
      rw [hd']
      exact hψk _ hk hk'
    have := ((hψc.tendsto (teichDistance (TeichSpace.basePoint hid) p)).comp hconv0).congr
      (fun n => (by
        rw [hd n]
        exact hψk _ (hkn n).1 (hkn n).2 : ψ (teichDistance (TeichSpace.basePoint hid) (pn n)) = kn n))
    rw [e2] at this
    exact this
  refine ⟨hkn', fun hk0 => ?_⟩
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1).tendsto_subseq
    (x := fun n => e (qn (ns n))) (fun n => by simpa using hqn (ns n))
  refine ⟨φ, ?_⟩
  have ha1 : ‖a‖ = 1 := by simpa using ha
  have hqs : ‖e (e.symm a)‖ = 1 := by rw [LinearEquiv.apply_symm_apply]; exact ha1
  have hqs0 : (e.symm a).1 ≠ 0 := by
    intro h0
    have : e.symm a = 0 := Subtype.ext h0
    rw [this, map_zero, norm_zero] at hqs
    exact zero_ne_one hqs
  obtain ⟨X, e', q', hT⟩ := exists_teichDeformation (e.symm a).2 hqs0 hk hk'
  have hpstar : IsDeformationPoint (e.symm a).1 k
      (Quot.mk _ (⟨X, e', ⟨_, s26u_isKQCRS hT⟩⟩ : MarkedRS S₀)) := ⟨X, e', _, q', hT, rfl⟩
  have hmono : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hconv' : ∀ x z, Tendsto (fun n => (qn (ns (φ n))).1 x z) atTop (𝓝 ((e.symm a).1 x z)) := by
    intro x z
    let ℓ : EuclideanSpace ℝ (Fin (6 * g - 6)) →ₗ[ℝ] ℂ :=
      { toFun := fun v => (e.symm v).1 x z
        map_add' := fun v w => by simp
        map_smul' := fun c v => by simp [Complex.real_smul] }
    have hℓ : Continuous ℓ := ℓ.continuous_of_finiteDimensional
    have := (hℓ.tendsto a).comp hlim
    simpa [ℓ, Function.comp_def] using this
  have hres := eq29_1_imp_eq29_2 hg hS (qn := fun n => (qn (ns (φ n))).1) (q := (e.symm a).1)
    (fun n => (qn (ns (φ n))).2) (e.symm a).2 hconv' (kn := fun n => kn (ns (φ n))) (k := k)
    (fun n => hkn _) hk hk' (hkn'.comp hmono) (pn := fun n => pn (ns (φ n)))
    (p := (Quot.mk _ (⟨X, e', ⟨_, s26u_isKQCRS hT⟩⟩ : MarkedRS S₀))) (fun n => hpn _) hpstar
  -- `d_T(p, p*) = 0`, so `p = p*`
  have hd0 : teichDistance p (Quot.mk _ (⟨X, e', ⟨_, s26u_isKQCRS hT⟩⟩ : MarkedRS S₀)) = 0 := by
    refine le_antisymm ?_ (s29_m_teichDistance_nonneg _ _)
    have h1 : Tendsto (fun n => teichDistance p (pn (ns (φ n)))) atTop (𝓝 0) :=
      (hconv.comp hmono).congr fun n => s29_m_teichDistance_symm _ _
    have hsum : Tendsto (fun n => teichDistance p (pn (ns (φ n))) +
        teichDistance (Quot.mk _ (⟨X, e', ⟨_, s26u_isKQCRS hT⟩⟩ : MarkedRS S₀)) (pn (ns (φ n)))) atTop
        (𝓝 (0 + 0)) := h1.add (by
      refine hres.congr fun n => s29_m_teichDistance_symm _ _)
    rw [add_zero] at hsum
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hsum fun n =>
      s29_m_teichDistance_triangle _ _ _
  have heq := teichDistance_eq_of_eq_zero hg hS _ _ hd0
  have hinj := lemma27_1_injective hg hS e hq hqs hkpos hk' hkpos hk' hp (by rw [heq]; exact hpstar)
  have hqeq : q = e.symm a := hinj.2
  rw [hqeq, LinearEquiv.apply_symm_apply]
  exact hlim

end

/-! ### §29.1 Theorem 29.1 and §29.2 Theorem 29.2, moved here from `S29_TeichmullerMetric` (`s29_t1_`)

The parametrization `Φ : B → T(S₀)`, `Φ(k · e q) = [S_{q,k}, f]` (`s29_t1_param`: bijection of the open unit ball
`B ⊂ ℝ^{6g-6}`, from `teichSpace_deformation_bijection` and `lemma27_1_injective`), then the topology of the ball is the
one of `d_T` (`s29_t1_iff`: (29.1) ⟺ (29.2), from `eq29_1_imp_eq29_2` and `eq29_2_imp_eq29_1`).  For completeness
(Theorem 29.2): a Cauchy sequence is `d_T`-bounded, hence lies in a closed ball `‖v‖ ≤ r < 1`
(`s29_t1_ball_of_bdd`, using `d_T([S₀, id], Φ v) = ½ ln((1 + ‖v‖)/(1 - ‖v‖))`, `s29_t1_bound`), which is compact; a
subsequence converges in `d_T` by `s29_t1_iff`, and a Cauchy sequence with a convergent subsequence converges
(`s29_t1_cauchy_subseq`). -/

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- **[stub A] The parametrization of `T(S₀)` by the unit ball.**  For `g > 1` and a real linear isomorphism
`e : Q(S₀) ≃ ℝ^{6g-6}` there is `Φ : ℝ^{6g-6} → T(S₀)`, injective on the open unit ball and onto `T(S₀)`, with
`Φ(k · e q) = [S_{q,k}, f]` for `‖e q‖ = 1`, `0 < k < 1`; moreover every `Φ v`, `v` in the ball, is a deformation point
for the radius `‖v‖` and a normalized `q` (with `‖v‖ · e q = v` when `v ≠ 0`). -/
theorem s29_t1_param {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀,
      InjOn Φ (ball 0 1) ∧ (∀ p : TeichSpace S₀, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1, Φ v = p) ∧
      (∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), ‖e q‖ = 1 → 0 < k → k < 1 →
        IsDeformationPoint q k (Φ (k • e q))) ∧
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
        ∃ q : (holQuadDiffSubmodule S₀).restrictScalars ℝ, ‖e q‖ = 1 ∧ IsDeformationPoint q ‖v‖ (Φ v) ∧
          (v ≠ 0 → ‖v‖ • e q = v) := by
  classical
  have hid : IsQCRS (Homeomorph.refl S₀) := isQCRS_refl
  have hdimpos : 0 < 6 * g - 6 := by omega
  -- every point of `T(S₀)` with a biholomorphic marking is the base point
  have hbase : ∀ m : MarkedRS S₀, IsBiholomorphic m.marking →
      teichDistance (TeichSpace.basePoint hid) (Quot.mk _ m) = 0 := by
    intro m hm
    refine le_antisymm ?_ (s29_m_teichDistance_nonneg _ _)
    have h1 : IsKQCRS m.marking 1 := (isKQCRS_one_iff _).2 hm
    have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS (m.marking : S₀ → m.X.carrier)).toReal ∈
        s29_m_teichSet (TeichSpace.basePoint hid) (Quot.mk _ m) :=
      ⟨⟨⟨S₀⟩, Homeomorph.refl S₀, hid⟩, m, m.marking, rfl, rfl, ⟨1, h1⟩, by
        have : (((⟨⟨S₀⟩, Homeomorph.refl S₀, hid⟩ : MarkedRS S₀).marking.trans m.marking : S₀ ≃ₜ m.X.carrier) :
            C(S₀, m.X.carrier)) = (m.marking : C(S₀, m.X.carrier)) := by
          ext x
          simp
        rw [this], rfl⟩
    have hK : maxDilatationRS (m.marking : S₀ → m.X.carrier) = 1 :=
      le_antisymm (by simpa using maxDilatationRS_le h1) (s29_m_one_le_maxDilatationRS ⟨1, h1⟩)
    refine (csInf_le (s29_m_teichSet_bddBelow _ _) hmem).trans (le_of_eq ?_)
    rw [hK]
    simp
  -- a deformation point exists for every normalized `q` and `0 ≤ k < 1`
  have hex : ∀ u : EuclideanSpace ℝ (Fin (6 * g - 6)), ‖u‖ = 1 → ∀ k : ℝ, 0 ≤ k → k < 1 →
      ∃ p : TeichSpace S₀, IsDeformationPoint (e.symm u) k p := by
    intro u hu k hk hk'
    have hne : (e.symm u).1 ≠ 0 := by
      intro h0
      have h1 : e.symm u = 0 := Subtype.ext h0
      have h2 : u = 0 := by simpa using congrArg e h1
      rw [h2, norm_zero] at hu
      exact zero_ne_one hu
    obtain ⟨X, e', q', hT⟩ := exists_teichDeformation (e.symm u).2 hne hk hk'
    exact ⟨Quot.mk _ ⟨X, e', ⟨_, s26u_isKQCRS hT⟩⟩, X, e', ⟨_, s26u_isKQCRS hT⟩, q', hT, rfl⟩
  have hpt : ∀ v : EuclideanSpace ℝ (Fin (6 * g - 6)),
      ∃ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (p : TeichSpace S₀),
        v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1 →
          (‖e q‖ = 1 ∧ IsDeformationPoint q ‖v‖ p ∧ (v ≠ 0 → ‖v‖ • e q = v)) := by
    intro v
    by_cases hv : v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1
    · have hv1 : ‖v‖ < 1 := by simpa using hv
      by_cases hv0 : v = 0
      · set u : EuclideanSpace ℝ (Fin (6 * g - 6)) := EuclideanSpace.single ⟨0, hdimpos⟩ 1 with hu
        have hu1 : ‖u‖ = 1 := by simp [hu]
        obtain ⟨p, hp⟩ := hex u hu1 0 le_rfl one_pos
        refine ⟨e.symm u, p, fun _ => ⟨by rw [LinearEquiv.apply_symm_apply]; exact hu1, ?_, fun h => absurd hv0 h⟩⟩
        rw [hv0, norm_zero]
        exact hp
      · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
        set u : EuclideanSpace ℝ (Fin (6 * g - 6)) := ‖v‖⁻¹ • v with hu
        have hu1 : ‖u‖ = 1 := by
          rw [hu, norm_smul, norm_inv, norm_norm]
          exact inv_mul_cancel₀ hvn
        obtain ⟨p, hp⟩ := hex u hu1 ‖v‖ (norm_nonneg _) hv1
        refine ⟨e.symm u, p, fun _ => ⟨by rw [LinearEquiv.apply_symm_apply]; exact hu1, hp, fun _ => ?_⟩⟩
        rw [LinearEquiv.apply_symm_apply, hu, smul_smul, mul_inv_cancel₀ hvn, one_smul]
    · exact ⟨0, TeichSpace.basePoint hid, fun h => absurd h hv⟩
  choose Q P hQP using hpt
  have hdist : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      teichDistance (TeichSpace.basePoint hid) (P v) = (1 / 2) * Real.log ((1 + ‖v‖) / (1 - ‖v‖)) :=
    fun v hv => teichDistance_deformation hg hS hid (hQP v hv).2.1
  have hpos : ∀ k : ℝ, 0 < k → k < 1 → 0 < (1 / 2 : ℝ) * Real.log ((1 + k) / (1 - k)) := by
    intro k hk hk'
    have h1 : 0 < 1 - k := by linarith
    have : 1 < (1 + k) / (1 - k) := (one_lt_div h1).2 (by linarith)
    have := Real.log_pos this
    positivity
  have hzero : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1, v = 0 →
      teichDistance (TeichSpace.basePoint hid) (P v) = 0 := by
    intro v hv hv0
    rw [hdist v hv, hv0]
    simp
  -- `k • e q` is the parameter of `(q, k)`
  have hrep : ∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), ‖e q‖ = 1 → 0 < k → k < 1 →
      k • e q ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1 ∧ ‖k • e q‖ = k ∧ Q (k • e q) = q := by
    intro q k hq hk hk'
    have hn : ‖k • e q‖ = k := by rw [norm_smul, hq, mul_one, Real.norm_eq_abs, abs_of_pos hk]
    have hb : k • e q ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1 := by
      rw [mem_ball_zero_iff, hn]
      exact hk'
    refine ⟨hb, hn, ?_⟩
    have h0 : k • e q ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      exact hk.ne' hn.symm
    obtain ⟨-, -, hs⟩ := hQP _ hb
    have h1 := hs h0
    rw [hn] at h1
    have h2 : e (Q (k • e q)) = e q := smul_right_injective _ hk.ne' h1
    exact e.injective h2
  refine ⟨P, ?_, ?_, ?_, fun v hv => ⟨Q v, hQP v hv⟩⟩
  · -- injectivity on the ball
    intro v hv v' hv' h
    by_cases a : v = 0
    · by_cases b : v' = 0
      · rw [a, b]
      · exfalso
        have h1 := hzero v hv a
        rw [h, hdist v' hv'] at h1
        have hn' : 0 < ‖v'‖ := norm_pos_iff.2 b
        have := hpos ‖v'‖ hn' (by simpa using hv')
        linarith
    · by_cases b : v' = 0
      · exfalso
        have h1 := hzero v' hv' b
        rw [← h, hdist v hv] at h1
        have hn' : 0 < ‖v‖ := norm_pos_iff.2 a
        have := hpos ‖v‖ hn' (by simpa using hv)
        linarith
      · obtain ⟨hq, hd, hs⟩ := hQP v hv
        obtain ⟨hq', hd', hs'⟩ := hQP v' hv'
        have hn : 0 < ‖v‖ := norm_pos_iff.2 a
        have hn' : 0 < ‖v'‖ := norm_pos_iff.2 b
        rw [← h] at hd'
        have := lemma27_1_injective hg hS e hq hq' hn (by simpa using hv) hn' (by simpa using hv') hd hd'
        obtain ⟨hk, hqq⟩ := this
        rw [← hs a, ← hs' b, hk, hqq]
  · -- surjectivity
    intro p
    rcases teichSpace_deformation_bijection hg hS e p with ⟨m, rfl, hm⟩ | ⟨⟨q, k⟩, ⟨hq, hk0, hk1, hd⟩, -⟩
    · refine ⟨0, mem_ball_self one_pos, ?_⟩
      have h1 := hzero 0 (mem_ball_self one_pos) rfl
      have h2 := hbase m hm
      exact (teichDistance_eq_of_eq_zero hg hS _ _ h1).symm.trans (teichDistance_eq_of_eq_zero hg hS _ _ h2)
    · obtain ⟨hb, hn, hqq⟩ := hrep q k hq hk0 hk1
      refine ⟨k • e q, hb, ?_⟩
      have hd' := (hQP _ hb).2.1
      rw [hqq, hn] at hd'
      exact isDeformationPoint_unique hg hS hd' hd
  · -- the deformation clause
    intro q k hq hk0 hk1
    obtain ⟨hb, hn, hqq⟩ := hrep q k hq hk0 hk1
    have hd' := (hQP _ hb).2.1
    rw [hqq, hn] at hd'
    exact hd'

/-- **[stub B] `d_T(Φ v, [S₀, id])`.**  For a `Φ` as in `s29_t1_param` (every `Φ v` a deformation point for
`(q, ‖v‖)`, `‖e q‖ = 1`), `d_T([S₀, id], Φ v) = ½ ln((1 + ‖v‖)/(1 - ‖v‖))`. -/
theorem s29_t1_bound {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    (hid : IsQCRS (Homeomorph.refl S₀)) {Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀}
    (hdef : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      ∃ q : (holQuadDiffSubmodule S₀).restrictScalars ℝ, ‖e q‖ = 1 ∧ IsDeformationPoint q ‖v‖ (Φ v) ∧
        (v ≠ 0 → ‖v‖ • e q = v))
    {v : EuclideanSpace ℝ (Fin (6 * g - 6))} (hv : v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1) :
    teichDistance (TeichSpace.basePoint hid) (Φ v) = (1 / 2) * Real.log ((1 + ‖v‖) / (1 - ‖v‖)) := by
  obtain ⟨q, -, hd, -⟩ := hdef v hv
  exact teichDistance_deformation hg hS hid hd

/-- **[stub C] The topology of the ball is that of `d_T`** ((29.1) ⟺ (29.2)): for a `Φ` as in `s29_t1_param`,
`vₙ → v` in the ball iff `d_T(Φ vₙ, Φ v) → 0` (`v = 0`: by `s29_t1_bound`; `v ≠ 0`: `eq29_1_imp_eq29_2` and
`eq29_2_imp_eq29_1` with `kₙ = ‖vₙ‖`, `qₙ` the normalization of `vₙ`). -/
theorem s29_t1_iff {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀}
    (hdef : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      ∃ q : (holQuadDiffSubmodule S₀).restrictScalars ℝ, ‖e q‖ = 1 ∧ IsDeformationPoint q ‖v‖ (Φ v) ∧
        (v ≠ 0 → ‖v‖ • e q = v))
    (v : EuclideanSpace ℝ (Fin (6 * g - 6))) (vn : ℕ → EuclideanSpace ℝ (Fin (6 * g - 6)))
    (hv : v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1) (hvn : ∀ n, vn n ∈ ball 0 1) :
    Tendsto vn atTop (𝓝 v) ↔ Tendsto (fun n => teichDistance (Φ (vn n)) (Φ v)) atTop (𝓝 0) := by
  classical
  have hid : IsQCRS (Homeomorph.refl S₀) := isQCRS_refl
  have hv1 : ‖v‖ < 1 := by simpa using hv
  have hvn1 : ∀ n, ‖vn n‖ < 1 := fun n => by simpa using hvn n
  -- `ψ d = (e^{2d} - 1)/(e^{2d} + 1)` inverts `t ↦ ½ ln((1+t)/(1-t))`
  set ψ : ℝ → ℝ := fun d => (Real.exp (2 * d) - 1) / (Real.exp (2 * d) + 1) with hψ
  have hψc : Continuous ψ := by
    refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).div
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).add continuous_const) fun d => ?_
    positivity
  have hψk : ∀ t : ℝ, 0 ≤ t → t < 1 → ψ ((1 / 2) * Real.log ((1 + t) / (1 - t))) = t := by
    intro t ht0 ht1
    have h1 : 0 < 1 - t := by linarith
    have hR : 0 < (1 + t) / (1 - t) := div_pos (by linarith) h1
    simp only [hψ]
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, Real.exp_log hR]
    field_simp
    ring
  have hF : ContinuousAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) 0 :=
    continuousAt_const.mul (ContinuousAt.log ((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by norm_num)) (by norm_num))
  by_cases hv0 : v = 0
  · -- `v = 0`: `Φ 0` is the base point and `d_T(Φ vₙ, Φ 0) = ½ ln((1+‖vₙ‖)/(1-‖vₙ‖))`
    subst hv0
    obtain ⟨q0, -, hd0, -⟩ := hdef 0 hv
    have h0 : teichDistance (TeichSpace.basePoint hid) (Φ 0) = 0 := by
      rw [teichDistance_deformation hg hS hid hd0]
      simp
    have hΦ0 : TeichSpace.basePoint hid = Φ 0 := teichDistance_eq_of_eq_zero hg hS _ _ h0
    have hdn : ∀ n, teichDistance (Φ (vn n)) (Φ 0) =
        (1 / 2) * Real.log ((1 + ‖vn n‖) / (1 - ‖vn n‖)) := fun n => by
      rw [← hΦ0, s29_m_teichDistance_symm]
      exact s29_t1_bound hg hS e hid hdef (hvn n)
    simp only [hdn]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    constructor
    · intro h
      have := hF.tendsto.comp h
      simpa [Function.comp_def] using this
    · intro h
      have h1 := (hψc.tendsto 0).comp h
      have h0 : ψ 0 = 0 := by simp [hψ]
      rw [h0] at h1
      refine h1.congr fun n => ?_
      exact hψk _ (norm_nonneg _) (hvn1 n)
  · have hvn0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    obtain ⟨q0, hq01, hq02, hq03⟩ := hdef v hv
    have he0 : e q0 = ‖v‖⁻¹ • v := by
      calc e q0 = ‖v‖⁻¹ • (‖v‖ • e q0) := by rw [smul_smul, inv_mul_cancel₀ hvn0, one_smul]
        _ = ‖v‖⁻¹ • v := by rw [hq03 hv0]
    constructor
    · -- (29.1) ⟹ (29.2)
      intro hlim
      have hev : ∀ᶠ n in atTop, vn n ≠ 0 := hlim.eventually (isOpen_ne.mem_nhds hv0)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      suffices h : Tendsto (fun n => teichDistance (Φ (vn (n + N))) (Φ v)) atTop (𝓝 0) from
        (tendsto_add_atTop_iff_nat (f := fun n => teichDistance (Φ (vn n)) (Φ v)) N).1 h
      have hlim' : Tendsto (fun n => vn (n + N)) atTop (𝓝 v) := hlim.comp (tendsto_add_atTop_nat N)
      choose Qn hQn1 hQn2 hQn3 using fun n => hdef (vn (n + N)) (hvn _)
      have hlimE : Tendsto (fun n => e (Qn n)) atTop (𝓝 (e q0)) := by
        have h1 : Tendsto (fun n => ‖vn (n + N)‖⁻¹ • vn (n + N)) atTop (𝓝 (‖v‖⁻¹ • v)) :=
          (hlim'.norm.inv₀ hvn0).smul hlim'
        rw [he0]
        refine h1.congr fun n => ?_
        have hw : ‖vn (n + N)‖ ≠ 0 := norm_ne_zero_iff.2 (hN _ (Nat.le_add_left N n))
        calc ‖vn (n + N)‖⁻¹ • vn (n + N) = ‖vn (n + N)‖⁻¹ • (‖vn (n + N)‖ • e (Qn n)) := by
              rw [hQn3 n (hN _ (Nat.le_add_left N n))]
          _ = e (Qn n) := by rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
      have hconv : ∀ x z, Tendsto (fun n => (Qn n).1 x z) atTop (𝓝 (q0.1 x z)) := by
        intro x z
        let ℓ : EuclideanSpace ℝ (Fin (6 * g - 6)) →ₗ[ℝ] ℂ :=
          { toFun := fun w => (e.symm w).1 x z
            map_add' := fun w w' => by simp
            map_smul' := fun c w => by simp [Complex.real_smul] }
        have hℓ : Continuous ℓ := ℓ.continuous_of_finiteDimensional
        have := (hℓ.tendsto (e q0)).comp hlimE
        simpa [ℓ, Function.comp_def] using this
      exact eq29_1_imp_eq29_2 hg hS (qn := fun n => (Qn n).1) (q := q0.1) (fun n => (Qn n).2) q0.2 hconv
        (kn := fun n => ‖vn (n + N)‖) (k := ‖v‖) (fun n => ⟨norm_nonneg _, hvn1 _⟩) (norm_nonneg _) hv1
        hlim'.norm hQn2 hq02
    · -- (29.2) ⟹ (29.1)
      intro hd
      choose Qn hQn1 hQn2 hQn3 using fun n => hdef (vn n) (hvn n)
      have hres := eq29_2_imp_eq29_1 hg hS e (qn := Qn) (q := q0) hQn1 hq01 (kn := fun n => ‖vn n‖) (k := ‖v‖)
        (fun n => ⟨norm_nonneg _, hvn1 n⟩) (norm_nonneg _) hv1 (pn := fun n => Φ (vn n)) (p := Φ v) hQn2 hq02 hd
      have h2 := hres.2 hvn0
      have h3 : Tendsto (fun n => ‖vn n‖ • e (Qn n)) atTop (𝓝 (‖v‖ • e q0)) := hres.1.smul h2
      have h4 : ∀ n, ‖vn n‖ • e (Qn n) = vn n := by
        intro n
        by_cases h0 : vn n = 0
        · rw [h0, norm_zero, zero_smul]
        · exact hQn3 n h0
      simp only [h4] at h3
      rwa [hq03 hv0] at h3

/-- **[stub D] A `d_T`-bounded sequence lies in a closed ball.**  For a `Φ` as in `s29_t1_param` which is onto
`T(S₀)`: if `d_T([S₀, id], pₙ) ≤ M` for all `n`, then `pₙ = Φ vₙ` with `‖vₙ‖ ≤ r` for some `r < 1`
(`‖v‖ ≤ tanh M` by `s29_t1_bound`). -/
theorem s29_t1_ball_of_bdd {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    (hid : IsQCRS (Homeomorph.refl S₀)) {Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀}
    (hdef : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      ∃ q : (holQuadDiffSubmodule S₀).restrictScalars ℝ, ‖e q‖ = 1 ∧ IsDeformationPoint q ‖v‖ (Φ v) ∧
        (v ≠ 0 → ‖v‖ • e q = v))
    (hsurj : ∀ p : TeichSpace S₀, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1, Φ v = p)
    (p : ℕ → TeichSpace S₀) {M : ℝ} (hM : ∀ n, teichDistance (TeichSpace.basePoint hid) (p n) ≤ M) :
    ∃ r : ℝ, r < 1 ∧ ∃ vn : ℕ → EuclideanSpace ℝ (Fin (6 * g - 6)),
      (∀ n, vn n ∈ closedBall (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) r) ∧ (∀ n, vn n ∈ ball 0 1) ∧
      ∀ n, Φ (vn n) = p n := by
  classical
  choose vn hvn hvp using fun n => hsurj (p n)
  have hE : 0 < Real.exp (2 * M) := Real.exp_pos _
  have hb : ∀ n, ‖vn n‖ ≤ (Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1) := by
    intro n
    have hv := hvn n
    have hx : ‖vn n‖ < 1 := by simpa using hv
    have h := s29_t1_bound hg hS e hid hdef hv
    rw [hvp n] at h
    have hM' := hM n
    rw [h] at hM'
    have hx0 : 0 ≤ ‖vn n‖ := norm_nonneg _
    have h1 : 0 < 1 - ‖vn n‖ := by linarith
    have hR : 0 < (1 + ‖vn n‖) / (1 - ‖vn n‖) := div_pos (by linarith) h1
    have h2 : Real.log ((1 + ‖vn n‖) / (1 - ‖vn n‖)) ≤ 2 * M := by linarith
    have h3 : (1 + ‖vn n‖) / (1 - ‖vn n‖) ≤ Real.exp (2 * M) := (Real.log_le_iff_le_exp hR).1 h2
    have h4 : 1 + ‖vn n‖ ≤ Real.exp (2 * M) * (1 - ‖vn n‖) := (div_le_iff₀ h1).1 h3
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨(Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1), ?_, vn, fun n => ?_, hvn, hvp⟩
  · rw [div_lt_one (by positivity)]
    linarith
  · rw [mem_closedBall_zero_iff]
    exact hb n

end

/-- **[stub E] A Cauchy sequence with a convergent subsequence converges** (for a symmetric `d` with the triangle
inequality). -/
theorem s29_t1_cauchy_subseq {α : Type*} (d : α → α → ℝ) (hsymm : ∀ p q, d p q = d q p)
    (htri : ∀ p q r, d p q ≤ d p r + d q r) (p : ℕ → α)
    (hp : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d (p m) (p n) < ε) {φ : ℕ → ℕ} (hφ : StrictMono φ) {q : α}
    (hq : Tendsto (fun n => d (p (φ n)) q) atTop (𝓝 0)) : Tendsto (fun n => d (p n) q) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hp (ε / 2) (half_pos hε)
  obtain ⟨N', hN'⟩ := (Metric.tendsto_atTop.1 hq) (ε / 2) (half_pos hε)
  refine ⟨max N N', fun n hn => ?_⟩
  have h1 : d (p n) (p (φ (max N N'))) < ε / 2 :=
    hN n (le_trans (le_max_left _ _) hn) _ (le_trans (le_max_left _ _) (hφ.id_le _))
  have h2 : dist (d (p (φ (max N N'))) q) 0 < ε / 2 := hN' _ (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at h2
  have h3 := htri (p n) q (p (φ (max N N')))
  have h4 := hsymm q (p (φ (max N N')))
  rw [Real.dist_eq, sub_zero]
  have h5 : d (p n) q ≤ |d (p n) q| := le_abs_self _
  have h6 : -(d (p n) q) ≤ |d (p n) q| := neg_le_abs _
  have h7 : 0 ≤ d (p n) q := by
    have h8 := htri (p n) (p n) q
    have h9 := htri (p n) (p n) (p n)
    linarith
  rw [abs_of_nonneg h7]
  have := le_abs_self (d (p (φ (max N N'))) q)
  linarith

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- **Theorem 29.1**: with the Teichmüller metric, `T(S₀)` is homeomorphic to the unit ball of
`ℝ^{6g-6}` (`g > 1` the genus of `S₀`): the bijection `T̃(S₀) → T(S₀)` is a homeomorphism for the
ball topology and the Teichmüller metric. -/
theorem thm29_1 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀,
      InjOn Φ (ball 0 1) ∧ (∀ p : TeichSpace S₀, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1, Φ v = p) ∧
      (∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), ‖e q‖ = 1 → 0 < k → k < 1 →
        IsDeformationPoint q k (Φ (k • e q))) ∧
      ∀ (v : EuclideanSpace ℝ (Fin (6 * g - 6))) (vn : ℕ → EuclideanSpace ℝ (Fin (6 * g - 6))),
        v ∈ ball 0 1 → (∀ n, vn n ∈ ball 0 1) →
        (Tendsto vn atTop (𝓝 v) ↔ Tendsto (fun n => teichDistance (Φ (vn n)) (Φ v)) atTop (𝓝 0)) := by
  obtain ⟨Φ, h1, h2, h3, h4⟩ := s29_t1_param hg hS e
  exact ⟨Φ, h1, h2, h3, fun v vn hv hvn => s29_t1_iff hg hS e h4 v vn hv hvn⟩

/-- **Theorem 29.2**: `T(S₀)` with the Teichmüller metric is a complete metric space. -/
theorem thm29_2_complete {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (p : ℕ → TeichSpace S₀)
    (hp : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, teichDistance (p m) (p n) < ε) :
    ∃ q : TeichSpace S₀, Tendsto (fun n => teichDistance (p n) q) atTop (𝓝 0) := by
  classical
  obtain ⟨-, e, -⟩ := teichDeformationSpace_parameters hg hS
  have hid : IsQCRS (Homeomorph.refl S₀) := isQCRS_refl
  obtain ⟨Φ, -, hsurj, -, hdef⟩ := s29_t1_param hg hS e
  obtain ⟨M, hM⟩ := s29_m_cauchy_bounded_of_triangle (fun a b : TeichSpace S₀ => teichDistance a b)
    s29_m_teichDistance_triangle (TeichSpace.basePoint hid) p hp
  obtain ⟨r, hr, vn, hvc, hvb, hvp⟩ := s29_t1_ball_of_bdd hg hS e hid hdef hsurj p hM
  obtain ⟨v, hvr, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) r).tendsto_subseq hvc
  have hvball : v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1 := by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hvr) hr
  refine ⟨Φ v, ?_⟩
  refine s29_t1_cauchy_subseq (fun a b : TeichSpace S₀ => teichDistance a b) s29_m_teichDistance_symm
    s29_m_teichDistance_triangle p hp hφ (q := Φ v) ?_
  have h := (s29_t1_iff hg hS e hdef v (fun n => vn (φ n)) hvball (fun n => hvb _)).1 hlim
  refine h.congr fun n => ?_
  show teichDistance (Φ (vn (φ n))) (Φ v) = teichDistance (p (φ n)) (Φ v)
  rw [hvp]

end

/-- **Theorem 27.2 (Teichmüller 存在性定理).**  Let `S₀`, `S` be closed Riemann surfaces of genus `g > 1`
and `f : S₀ → S` an orientation preserving homeomorphism.  Then there is a Teichmüller map
`f₀ : S₀ → S` homotopic to `f` (`f₀ = h ∘ f₁` with `f₁` a Teichmüller deformation map and `h`
conformal; its initial differential is `q` and its terminal differential is the transport of `q₁`
by `h`).  Together with Theorem 26.2: the extremal map in every homotopy class exists, is unique,
and is a Teichmüller map (or conformal). -/
theorem thm27_2_existence [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (h₀ : HasGenus S₀ g) (h₁ : HasGenus S g)
    (f : S₀ ≃ₜ S) (hf : IsOrientationPreservingRS f) :
    ∃ f₀ : S₀ ≃ₜ S, ContinuousMap.Homotopic (f : C(S₀, S)) (f₀ : C(S₀, S)) ∧
      (IsBiholomorphic f₀ ∨ ∃ (q : S₀ → ℂ → ℂ) (q' : S → ℂ → ℂ) (k : ℝ), IsTeichmullerMap f₀ q q' k) ∧
      IsExtremalInHomotopyClass f₀ ∧
      ∀ h : S₀ ≃ₜ S, IsExtremalInHomotopyClass h → ContinuousMap.Homotopic (f : C(S₀, S)) (h : C(S₀, S)) →
        ⇑h = ⇑f₀ := by
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S := h₁.1
  -- §24.2: a quasiconformal map `q` in the class of `f`; both surfaces are `ℍ/Γ` (S22)
  obtain ⟨q, hq, hfq⟩ := exists_qc_in_homotopy_class h₀ h₁ f hf
  obtain ⟨Γ₀, p₀, -, -, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg h₀
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg h₁
  obtain ⟨f₀, h1, h2, h3, h4⟩ := thm27_2_existence_qc_of_uniformization hg h₀ h₁ q hq hp₀ hp₁
  exact ⟨f₀, hfq.trans h1, h2, h3, fun h hh hfh => h4 h hh (hfq.symm.trans hfh)⟩

/-! ### `ULift` copies of Riemann surfaces (`utm_ul_`, for `thm26_1_extremal_exists`): the universe transport -/

/-- The atlas of the `ULift` copy of a Riemann surface built from the single chart `Homeomorph.ulift`
(`ChartedSpace.comp`): `ulift ≫ c` for the charts `c` of the surface. -/
theorem utm_ul_atlas {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (e : OpenPartialHomeomorph (ULift X) ℂ)
    (he : e ∈ (letI : ChartedSpace X (ULift X) :=
      (Homeomorph.ulift.toOpenPartialHomeomorph).singletonChartedSpace (by simp)
     let : ChartedSpace ℂ (ULift X) := ChartedSpace.comp ℂ X (ULift X)
     atlas ℂ (ULift X))) :
    ∃ c ∈ atlas ℂ X, e = Homeomorph.ulift.toOpenPartialHomeomorph.trans c := by
  obtain ⟨e₁, he₁, c, hc, rfl⟩ := he
  refine ⟨c, hc, ?_⟩
  have h1 : e₁ = Homeomorph.ulift.toOpenPartialHomeomorph := he₁
  rw [h1]

/-- **Local expressions** of a map between `ULift` copies whose charts are `ulift ≫ chart`: they are those of the map
itself. -/
theorem utm_ul_local {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [ChartedSpace ℂ (ULift X)] [ChartedSpace ℂ (ULift Y)]
    (hX : ∀ x : ULift X, chartAt ℂ x = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ x.down))
    (hY : ∀ y : ULift Y, chartAt ℂ y = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ y.down))
    (φ : X → Y) (x : ULift X) :
    localMapExpr (fun a : ULift X => ULift.up (φ a.down)) x = localMapExpr φ x.down ∧
      localMapDomain (fun a : ULift X => ULift.up (φ a.down)) x = localMapDomain φ x.down := by
  refine ⟨?_, ?_⟩
  · funext z
    simp only [localMapExpr, hX, hY]
    rfl
  · ext z
    simp only [localMapDomain, hX, hY, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_target, Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff,
      mem_preimage, mem_univ, true_and, and_true, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    rfl

/-- The `ULift` copy of a homeomorphism has the same maximal dilatation, the same `K`-quasiconformality and the same
orientation behaviour (all are read in the charts, which are the same). -/
theorem utm_ul_transfer {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [ChartedSpace ℂ (ULift X)] [ChartedSpace ℂ (ULift Y)]
    (hX : ∀ x : ULift X, chartAt ℂ x = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ x.down))
    (hY : ∀ y : ULift Y, chartAt ℂ y = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ y.down))
    (φ : X ≃ₜ Y) :
    maxDilatationRS (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) =
        maxDilatationRS φ ∧
      (∀ K : ℝ, IsKQCRS (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm)) K ↔ IsKQCRS φ K) ∧
      (IsOrientationPreservingRS φ →
        IsOrientationPreservingRS (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm))) := by
  have hc : ((Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X ≃ₜ ULift Y) : ULift X → ULift Y) =
      fun a => ULift.up (φ a.down) := rfl
  have hl : ∀ x : ULift X,
      localMapExpr (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) x =
          localMapExpr φ x.down ∧
        localMapDomain (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) x =
          localMapDomain φ x.down := by
    intro x
    rw [hc]
    exact utm_ul_local hX hY φ x
  refine ⟨?_, fun K => ⟨fun h => ⟨h.1, fun x => ?_⟩, fun h => ⟨h.1, fun x => ?_⟩⟩, fun h x => ?_⟩
  · apply le_antisymm
    · refine iSup_le fun x => ?_
      rw [(hl x).1, (hl x).2]
      exact le_iSup (fun y => maxDilatation (localMapExpr φ y) (localMapDomain φ y)) x.down
    · refine iSup_le fun x => ?_
      have := le_iSup (fun y : ULift X => maxDilatation
        (localMapExpr (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) y)
        (localMapDomain (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) y)) (ULift.up x)
      rw [(hl _).1, (hl _).2] at this
      exact this
  · have := h.2 (ULift.up x)
    rw [(hl _).1, (hl _).2] at this
    exact this
  · rw [(hl x).1, (hl x).2]
    exact h.2 x.down
  · show IsSensePreserving (localMapExpr (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) x)
      (localMapDomain (Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X → ULift Y) x)
    rw [(hl x).1, (hl x).2]
    exact h x.down

/-- Homotopy classes are the same for a map and its `ULift` copy. -/
theorem utm_ul_homotopic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (φ ψ : X ≃ₜ Y) :
    ContinuousMap.Homotopic (φ : C(X, Y)) (ψ : C(X, Y)) ↔
      ContinuousMap.Homotopic ((Homeomorph.ulift.trans (φ.trans Homeomorph.ulift.symm) : ULift X ≃ₜ ULift Y) :
        C(ULift X, ULift Y))
        ((Homeomorph.ulift.trans (ψ.trans Homeomorph.ulift.symm) : ULift X ≃ₜ ULift Y) : C(ULift X, ULift Y)) := by
  have hup : ∀ χ : X ≃ₜ Y,
      ((Homeomorph.ulift.trans (χ.trans Homeomorph.ulift.symm) : ULift X ≃ₜ ULift Y) : C(ULift X, ULift Y)) =
        ((Homeomorph.ulift.symm : Y ≃ₜ ULift Y) : C(Y, ULift Y)).comp
          ((χ : C(X, Y)).comp ((Homeomorph.ulift : ULift X ≃ₜ X) : C(ULift X, X))) := fun χ => rfl
  have hdown : ∀ χ : X ≃ₜ Y, (χ : C(X, Y)) =
      ((Homeomorph.ulift : ULift Y ≃ₜ Y) : C(ULift Y, Y)).comp
        (((Homeomorph.ulift.trans (χ.trans Homeomorph.ulift.symm) : ULift X ≃ₜ ULift Y) : C(ULift X, ULift Y)).comp
          ((Homeomorph.ulift.symm : X ≃ₜ ULift X) : C(X, ULift X))) := fun χ => rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hup, hup]
    exact (ContinuousMap.Homotopic.refl _).comp (h.comp (ContinuousMap.Homotopic.refl _))
  · rw [hdown φ, hdown ψ]
    exact (ContinuousMap.Homotopic.refl _).comp (h.comp (ContinuousMap.Homotopic.refl _))

/-- The `ULift` copy of a closed surface of genus `g` has genus `g`. -/
theorem utm_ul_hasGenus {X : Type*} [TopologicalSpace X] {g : ℕ} (h : HasGenus X g) : HasGenus (ULift X) g := by
  have : CompactSpace X := h.1
  refine ⟨Homeomorph.ulift.symm.compactSpace, fun x => ?_⟩
  obtain ⟨e⟩ := h.2 x.down
  exact ⟨(fundamentalGroupMulEquivOfHomeomorph (Homeomorph.ulift : ULift X ≃ₜ X) rfl).trans e⟩

/-- The `ULift` copy of a Riemann surface, with the charts `ulift ≫ chart`, is a Riemann surface. -/
theorem utm_ul_isManifold {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [ChartedSpace ℂ (ULift X)]
    (hA : ∀ e ∈ atlas ℂ (ULift X), ∃ c ∈ atlas ℂ X, e = Homeomorph.ulift.toOpenPartialHomeomorph.trans c) :
    IsManifold 𝓘(ℂ) ω (ULift X) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω (ULift X) fun e e' he he' => ?_
  obtain ⟨c, hc, rfl⟩ := hA e he
  obtain ⟨c', hc', rfl⟩ := hA e' he'
  have hcc := (mem_groupoid_of_pregroupoid.mp (HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ)) hc hc')).1
  have hfun : (⇑((Homeomorph.ulift.toOpenPartialHomeomorph.trans c).symm.trans
      (Homeomorph.ulift.toOpenPartialHomeomorph.trans c')) : ℂ → ℂ) = ⇑(c.symm.trans c') := rfl
  have hsrc : ((Homeomorph.ulift.toOpenPartialHomeomorph.trans c).symm.trans
      (Homeomorph.ulift.toOpenPartialHomeomorph.trans c')).source = (c.symm.trans c').source := by
    ext z
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage, mem_univ, true_and, and_true,
      OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    rfl
  rw [hfun, hsrc]
  exact hcc

/-! ### Source-only interface for (26.2); package proofs await review and a separate grant. -/

/-- **P: paired general-K lift limit (package cap 850 LF including this header).**
Normalize all lifts in one compact target translate set, take a common strict subsequence of the
forward and inverse Cayley conjugates, and construct one limit lift. The explicit `EqOn` identities
tie both disc limits to that lift. No limit is selected later as a function of a new QC bound. -/
theorem eq262_paired_limit {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [T2Space Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    {K : ℝ} (G : ℕ → X ≃ₜ Y) (hG : ∀ n, IsKQCRS (G n) K) :
    ∃ (CY : Set UpperHalfPlane) (F : ℕ → UpperHalfPlane ≃ₜ UpperHalfPlane)
      (φ : ℕ → ℕ) (Φl Ψl : ℂ → ℂ) (Finf : UpperHalfPlane ≃ₜ UpperHalfPlane),
      IsCompact CY ∧ (∀ τ : UpperHalfPlane, ∃ δ ∈ ΓY, δ • τ ∈ CY) ∧
      (∀ n, IsLift pX pY (G n) (F n)) ∧ (∀ n, F n UpperHalfPlane.I ∈ CY) ∧ StrictMono φ ∧
      TendstoLocallyUniformlyOn
        (fun n => cayley ∘ (liftToC (F (φ n)) ∘ cayleyInv)) Φl atTop unitDisc ∧
      TendstoLocallyUniformlyOn
        (fun n => cayley ∘ (liftToC (F (φ n)).symm ∘ cayleyInv)) Ψl atTop unitDisc ∧
      MapsTo Φl unitDisc unitDisc ∧ MapsTo Ψl unitDisc unitDisc ∧
      (∀ z ∈ unitDisc, Ψl (Φl z) = z) ∧ (∀ z ∈ unitDisc, Φl (Ψl z) = z) ∧
      EqOn Φl (cayley ∘ (liftToC Finf ∘ cayleyInv)) unitDisc ∧
      EqOn Ψl (cayley ∘ (liftToC Finf.symm ∘ cayleyInv)) unitDisc ∧
      IsKQC (liftToC Finf) upperHalf K ∧
      (∀ τ : UpperHalfPlane, Tendsto (fun n => F (φ n) τ) atTop (𝓝 (Finf τ))) := by
  classical
  obtain ⟨CY, hCY, hcoverY⟩ := utm_exists_compact_translate hY
  have hlift : ∀ n, ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
      IsLift pX pY (G n) F ∧ F UpperHalfPlane.I ∈ CY := by
    intro n
    obtain ⟨τ₁, hτ₁⟩ := hY.2.2.1 (G n (pX UpperHalfPlane.I))
    obtain ⟨δ, hδ, hδCY⟩ := hcoverY τ₁
    have hp : pY (δ • τ₁) = G n (pX UpperHalfPlane.I) := by
      rw [← hτ₁]
      exact ((hY.2.2.2 τ₁ (δ • τ₁)).2 ⟨δ, hδ, rfl⟩).symm
    obtain ⟨F, hF, hFi⟩ := exists_lift hX hY (G n) UpperHalfPlane.I (δ • τ₁) hp
    exact ⟨F, hF, hFi ▸ hδCY⟩
  choose F hF hFK using hlift
  have hFqc : ∀ n, IsKQC (liftToC (F n)) upperHalf K :=
    fun n => h23l_lift_isKQC hX hY (hG n) (hF n)
  have hFqci : ∀ n, IsKQC (liftToC (F n).symm) upperHalf K :=
    fun n => h23l_lift_isKQC hY hX (s29_m_isKQCRS_symm (hG n))
      (s27g_isLift_symm (hF n))
  let Φ : ℕ → ℂ → ℂ := fun n => cayley ∘ (liftToC (F n) ∘ cayleyInv)
  let Ψ : ℕ → ℂ → ℂ := fun n => cayley ∘ (liftToC (F n).symm ∘ cayleyInv)
  have hΦqc : ∀ n, IsKQC (Φ n) unitDisc K := fun n => (s30b_disc_conj (hFqc n)).1
  have hΨqc : ∀ n, IsKQC (Ψ n) unitDisc K := fun n => (s30b_disc_conj (hFqci n)).1
  have hΦmaps : ∀ n, ∀ z ∈ unitDisc, Φ n z ∈ unitDisc :=
    fun n => (s30b_disc_conj (hFqc n)).2
  have hΨmaps : ∀ n, ∀ z ∈ unitDisc, Ψ n z ∈ unitDisc :=
    fun n => (s30b_disc_conj (hFqci n)).2
  have hΨΦ : ∀ n, ∀ z ∈ unitDisc, Ψ n (Φ n z) = z :=
    fun n z hz => s30b_conj_symm (F n) hz
  have hΦΨ : ∀ n, ∀ z ∈ unitDisc, Φ n (Ψ n z) = z := by
    intro n z hz
    have h := s30b_conj_symm (F n).symm hz
    simpa only [Homeomorph.symm_symm] using h
  have hΦbd : ∀ n, ∀ z ∈ unitDisc, ‖Φ n z‖ ≤ 1 :=
    fun n z hz => (mem_ball_zero_iff.mp (hΦmaps n z hz)).le
  have hΨbd : ∀ n, ∀ z ∈ unitDisc, ‖Ψ n z‖ ≤ 1 :=
    fun n z hz => (mem_ball_zero_iff.mp (hΨmaps n z hz)).le
  -- Extract the inverse limit only along the selected forward sequence.
  obtain ⟨φ₁, hφ₁, Φl, hlimΦ₁⟩ := thm8_1_normal_family (D := unitDisc)
    Metric.isBounded_ball (isConnected_ball one_pos) hΦqc hΦbd
  obtain ⟨φ₂, hφ₂, Ψl, hlimΨ₂⟩ := thm8_1_normal_family (D := unitDisc)
    Metric.isBounded_ball (isConnected_ball one_pos)
      (fun n => hΨqc (φ₁ n)) (fun n => hΨbd (φ₁ n))
  let φ : ℕ → ℕ := fun n => φ₁ (φ₂ n)
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hlimΦ : TendstoLocallyUniformlyOn (fun n => Φ (φ n)) Φl atTop unitDisc :=
    s30b_tlu_comp hlimΦ₁ hφ₂.tendsto_atTop
  have hlimΨ : TendstoLocallyUniformlyOn (fun n => Ψ (φ n)) Ψl atTop unitDisc := hlimΨ₂
  have hΦlc : ContinuousOn Φl unitDisc :=
    hlimΦ.continuousOn (Eventually.of_forall fun n => (hΦqc (φ n)).2.2.1.1).frequently
  have hΨlc : ContinuousOn Ψl unitDisc :=
    hlimΨ.continuousOn (Eventually.of_forall fun n => (hΨqc (φ n)).2.2.1.1).frequently
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hhalfD : ((1 : ℂ) / 2) ∈ unitDisc := by
    show ((1 : ℂ) / 2) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    norm_num
  have hcayc : Continuous (fun τ : UpperHalfPlane => cayley (τ : ℂ)) := by
    change Continuous (fun τ : UpperHalfPlane =>
      ((τ : ℂ) - Complex.I) / ((τ : ℂ) + Complex.I))
    exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.add continuous_const) fun τ => cayley_den_ne_zero τ.im_pos
  let C₀ : Set ℂ := (fun τ : UpperHalfPlane => cayley (τ : ℂ)) '' CY
  have hC₀c : IsCompact C₀ := hCY.image hcayc
  have hC₀D : C₀ ⊆ unitDisc := by
    rintro _ ⟨τ, _, rfl⟩
    exact cayley_mem_unitDisc τ.im_pos
  have hΦ0 : ∀ n, Φ n 0 = cayley (F n UpperHalfPlane.I : ℂ) := by
    intro n
    simp only [Φ, Function.comp_apply, s30b_cayleyInv_zero]
    rw [← UpperHalfPlane.coe_I, h23l_liftToC_coe]
  have hΦlD : MapsTo Φl unitDisc unitDisc :=
    s30b_limit_mapsTo (fun n => hΦqc (φ n)) (fun n => hΦmaps (φ n)) hlimΦ
      hC₀c hC₀D (fun n => by rw [hΦ0]; exact ⟨_, hFK (φ n), rfl⟩)
  -- Forward normalization gives an interior point at which to pass the inverse identity.
  have hΨΦl : ∀ z ∈ unitDisc, Ψl (Φl z) = z := by
    intro z hz
    have h1 : Tendsto (fun n => Ψ (φ n) (Φ (φ n) z)) atTop (𝓝 (Ψl (Φl z))) :=
      hlimΨ.tendsto_comp (hΨlc _ (hΦlD hz)) (hΦlD hz)
        (tendsto_nhdsWithin_iff.2 ⟨hlimΦ.tendsto_at hz,
          Eventually.of_forall fun n => hΦmaps _ z hz⟩)
    have h2 : (fun n => Ψ (φ n) (Φ (φ n) z)) = fun _ => z :=
      funext fun n => hΨΦ (φ n) z hz
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hΨl : IsKQC Ψl unitDisc K ∧ MapsTo Ψl unitDisc unitDisc := by
    rcases s30b_limit_cases (fun n => hΨqc (φ n)) (fun n => hΨmaps (φ n)) hlimΨ with
      ⟨c, hc⟩ | h
    · exfalso
      have h0 := hΨΦl 0 h0D
      have hhalf := hΨΦl _ hhalfD
      rw [hc _ (hΦlD h0D)] at h0
      rw [hc _ (hΦlD hhalfD), h0] at hhalf
      norm_num at hhalf
    · exact h
  have hΦΨl : ∀ z ∈ unitDisc, Φl (Ψl z) = z := by
    intro z hz
    have h1 : Tendsto (fun n => Φ (φ n) (Ψ (φ n) z)) atTop (𝓝 (Φl (Ψl z))) :=
      hlimΦ.tendsto_comp (hΦlc _ (hΨl.2 hz)) (hΨl.2 hz)
        (tendsto_nhdsWithin_iff.2 ⟨hlimΨ.tendsto_at hz,
          Eventually.of_forall fun n => hΨmaps _ z hz⟩)
    have h2 : (fun n => Φ (φ n) (Ψ (φ n) z)) = fun _ => z :=
      funext fun n => hΦΨ (φ n) z hz
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hΦinj : InjOn Φl unitDisc := by
    intro z hz w hw hzw
    calc z = Ψl (Φl z) := (hΨΦl z hz).symm
      _ = Ψl (Φl w) := congrArg Ψl hzw
      _ = w := hΨΦl w hw
  have hΦlK : IsKQC Φl unitDisc K :=
    UniversalTeichmuller.ut2_limit_isKQC isOpen_ball (fun n => hΦqc (φ n)) hlimΦ hΦinj
  have hΦlH : ∀ τ : UpperHalfPlane, 0 < (cayleyInv (Φl (cayley (τ : ℂ)))).im :=
    fun τ => cayleyInv_mem_upperHalf
      (mem_ball_zero_iff.mp (hΦlD (cayley_mem_unitDisc τ.im_pos)))
  have hΨlH : ∀ τ : UpperHalfPlane, 0 < (cayleyInv (Ψl (cayley (τ : ℂ)))).im :=
    fun τ => cayleyInv_mem_upperHalf
      (mem_ball_zero_iff.mp (hΨl.2 (cayley_mem_unitDisc τ.im_pos)))
  have hciD : ContinuousOn cayleyInv unitDisc := differentiableOn_cayleyInv.continuousOn
  have hFc : Continuous (fun τ : UpperHalfPlane =>
      (⟨cayleyInv (Φl (cayley (τ : ℂ))), hΦlH τ⟩ : UpperHalfPlane)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.2
      (hciD.comp_continuous (hΦlc.comp_continuous hcayc
        fun τ => cayley_mem_unitDisc τ.im_pos)
        fun τ => hΦlD (cayley_mem_unitDisc τ.im_pos))
  have hGc : Continuous (fun τ : UpperHalfPlane =>
      (⟨cayleyInv (Ψl (cayley (τ : ℂ))), hΨlH τ⟩ : UpperHalfPlane)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.2
      (hciD.comp_continuous (hΨlc.comp_continuous hcayc
        fun τ => cayley_mem_unitDisc τ.im_pos)
        fun τ => hΨl.2 (cayley_mem_unitDisc τ.im_pos))
  let Finf : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    { toFun := fun τ => ⟨cayleyInv (Φl (cayley (τ : ℂ))), hΦlH τ⟩
      invFun := fun τ => ⟨cayleyInv (Ψl (cayley (τ : ℂ))), hΨlH τ⟩
      left_inv := fun τ => by
        apply UpperHalfPlane.ext
        show cayleyInv (Ψl (cayley (cayleyInv (Φl (cayley (τ : ℂ)))))) = τ
        rw [cayley_cayleyInv (mem_ball_zero_iff.mp (hΦlD (cayley_mem_unitDisc τ.im_pos))),
          hΨΦl _ (cayley_mem_unitDisc τ.im_pos), cayleyInv_cayley τ.im_pos]
      right_inv := fun τ => by
        apply UpperHalfPlane.ext
        show cayleyInv (Φl (cayley (cayleyInv (Ψl (cayley (τ : ℂ)))))) = τ
        rw [cayley_cayleyInv (mem_ball_zero_iff.mp (hΨl.2 (cayley_mem_unitDisc τ.im_pos))),
          hΦΨl _ (cayley_mem_unitDisc τ.im_pos), cayleyInv_cayley τ.im_pos]
      continuous_toFun := hFc
      continuous_invFun := hGc }
  have hΦeq : EqOn Φl (cayley ∘ (liftToC Finf ∘ cayleyInv)) unitDisc := by
    intro z hz
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    let τ : UpperHalfPlane := ⟨cayleyInv z, cayleyInv_mem_upperHalf hz'⟩
    have hτ : (τ : ℂ) = cayleyInv z := rfl
    change Φl z = cayley (liftToC Finf (cayleyInv z))
    rw [← hτ, h23l_liftToC_coe]
    change Φl z = cayley (cayleyInv (Φl (cayley (τ : ℂ))))
    rw [hτ, cayley_cayleyInv hz', cayley_cayleyInv (mem_ball_zero_iff.mp (hΦlD hz))]
  have hΨeq : EqOn Ψl (cayley ∘ (liftToC Finf.symm ∘ cayleyInv)) unitDisc := by
    intro z hz
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    let τ : UpperHalfPlane := ⟨cayleyInv z, cayleyInv_mem_upperHalf hz'⟩
    have hτ : (τ : ℂ) = cayleyInv z := rfl
    change Ψl z = cayley (liftToC Finf.symm (cayleyInv z))
    rw [← hτ, h23l_liftToC_coe]
    change Ψl z = cayley (cayleyInv (Ψl (cayley (τ : ℂ))))
    rw [hτ, cayley_cayleyInv hz', cayley_cayleyInv (mem_ball_zero_iff.mp (hΨl.2 hz))]
  have hFinf : IsKQC (liftToC Finf) upperHalf K := by
    have h1 : IsKQC cayley upperHalf 1 :=
      isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley
    have h2 : IsKQC cayleyInv unitDisc 1 :=
      isKQC_one_of_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
    have h3 := thm7_1_comp h1 hΦlK
      (by rintro _ ⟨z, hz, rfl⟩; exact cayley_mem_unitDisc hz)
    have h4 := thm7_1_comp h3 h2
      (by rintro _ ⟨z, hz, rfl⟩; exact hΦlD (cayley_mem_unitDisc hz))
    simp only [one_mul, mul_one] at h4
    refine ad_isKQC_congr h4 fun z hz => ?_
    have hz' : 0 < z.im := hz
    rw [h23l_liftToC_eq Finf hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    rfl
  have hconv : ∀ τ : UpperHalfPlane,
      Tendsto (fun n => F (φ n) τ) atTop (𝓝 (Finf τ)) := by
    intro τ
    have hτD : cayley (τ : ℂ) ∈ unitDisc := cayley_mem_unitDisc τ.im_pos
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    have hci : ContinuousAt cayleyInv (Φl (cayley (τ : ℂ))) :=
      (differentiableOn_cayleyInv.differentiableAt (isOpen_ball.mem_nhds (hΦlD hτD))).continuousAt
    have h1 := hci.tendsto.comp (hlimΦ.tendsto_at hτD)
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply]
    exact s30b_recover (F (φ n)) τ
  exact ⟨CY, F, φ, Φl, Ψl, Finf, hCY, hcoverY, hF, hFK, hφ, hlimΦ, hlimΨ,
    hΦlD, hΨl.2, hΨΦl, hΦΨl, hΦeq, hΨeq, hFinf, hconv⟩

/-- **D: stabilization and descent of the chosen limit (package cap 550 LF including this header).**
The normalized lift values on a finite compact-overlap generating set have finitely many deck
choices. An infinite fibre identifies the action of this same `Finf` with one sequence member.
The output `IsLift` is explicitly `∀ τ, pY (Finf τ) = c (pX τ)`; the returned surface map is tied
to the already chosen lift. The homotopy direction is `c` to the selected sequence member. -/
theorem eq262_deck_descend {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [T2Space Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    (G : ℕ → X ≃ₜ Y) (F : ℕ → UpperHalfPlane ≃ₜ UpperHalfPlane) (φ : ℕ → ℕ)
    (Finf : UpperHalfPlane ≃ₜ UpperHalfPlane) (hF : ∀ n, IsLift pX pY (G n) (F n))
    {CY : Set UpperHalfPlane} (hCY : IsCompact CY) (hFK : ∀ n, F n UpperHalfPlane.I ∈ CY)
    (hconv : ∀ τ : UpperHalfPlane, Tendsto (fun n => F (φ n) τ) atTop (𝓝 (Finf τ))) :
    ∃ (c : X ≃ₜ Y) (n₀ : ℕ), IsLift pX pY c Finf ∧
      ContinuousMap.Homotopic (c : C(X, Y)) (G (φ n₀) : C(X, Y)) := by
  classical
  obtain ⟨KX, hKX, hcovX⟩ := utm_exists_compact_translate hX
  -- Stabilize the tuple of deck actions on a finite compact-overlap generating set.
  set E : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {γ ∈ ΓX | ((fun z => γ • z) '' KX ∩ KX).Nonempty} with hEdef
  have hEfin : E.Finite := utm_x2_isFuchsian hX KX hKX
  have hgen := s30b_generate (utm_x2_isFuchsian hX) hKX hcovX
  set C : Set UpperHalfPlane := CY ∪ ⋃ γ ∈ E, insert (Finf (γ • UpperHalfPlane.I))
    (range fun n => F (φ n) (γ • UpperHalfPlane.I)) with hCdef
  have hCc : IsCompact C :=
    hCY.union (hEfin.isCompact_biUnion fun γ _ =>
      (hconv (γ • UpperHalfPlane.I)).isCompact_insert_range)
  have hdeck : ∀ n, ∀ γ ∈ ΓX, ∃ δ ∈ ΓY, ∀ τ, F n (γ • τ) = δ • F n τ :=
    fun n γ hγ => h23l_deck hX hY (hF n) hγ
  choose δ hδΓ hδ using hdeck
  set Fin' : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {d ∈ ΓY | ((fun z => d • z) '' C ∩ C).Nonempty} with hFindef
  have hFinfin : Fin'.Finite := utm_x2_isFuchsian hY C hCc
  have hmemFin : ∀ n, ∀ e : E, δ (φ n) e.1 e.2.1 ∈ Fin' := by
    intro n e
    refine ⟨hδΓ _ _ _, δ (φ n) e.1 e.2.1 • F (φ n) UpperHalfPlane.I,
      ⟨F (φ n) UpperHalfPlane.I, Or.inl (hFK _), rfl⟩, ?_⟩
    rw [← hδ]
    refine Or.inr (mem_iUnion₂.2 ⟨e.1, e.2, ?_⟩)
    exact mem_insert_of_mem _ ⟨n, rfl⟩
  have : Finite E := hEfin.to_subtype
  have : Finite Fin' := hFinfin.to_subtype
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber
    (fun n : ℕ => fun e : E => (⟨δ (φ n) e.1 e.2.1, hmemFin n e⟩ : Fin'))
  set Sv : Set ℕ :=
    (fun n : ℕ => fun e : E => (⟨δ (φ n) e.1 e.2.1, hmemFin n e⟩ : Fin')) ⁻¹' {v} with hSv
  have hSinf : Sv.Infinite := Set.infinite_coe_iff.1 hv
  have hSmem : ∀ n ∈ Sv, ∀ x (hx : x ∈ E),
      δ (φ n) x hx.1 = (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    fun n hn x hx => congrArg Subtype.val (congrFun (Set.mem_singleton_iff.1 hn) ⟨x, hx⟩)
  have hSne : (atTop ⊓ 𝓟 Sv).NeBot := by
    have h := frequently_iff_neBot.1
      ((Nat.frequently_atTop_iff_infinite (p := fun n => n ∈ Sv)).2 hSinf)
    rwa [Set.ofPred_mem_eq] at h
  have hSev : ∀ᶠ n in atTop ⊓ 𝓟 Sv, n ∈ Sv :=
    mem_inf_of_right (mem_principal_self Sv)
  -- Uniqueness of limits identifies the action of the supplied Finf, without reselecting it.
  have hlimE : ∀ x (hx : x ∈ E), ∀ τ,
      Finf (x • τ) = (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • Finf τ := by
    intro x hx τ
    have h1 : Tendsto (fun n => F (φ n) (x • τ)) (atTop ⊓ 𝓟 Sv)
        (𝓝 (Finf (x • τ))) := (hconv _).mono_left inf_le_left
    have h2 : Tendsto
        (fun n => (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F (φ n) τ)
        (atTop ⊓ 𝓟 Sv)
        (𝓝 ((v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • Finf τ)) :=
      ((continuous_const_smul _).tendsto _).comp ((hconv τ).mono_left inf_le_left)
    have h3 : (fun n => F (φ n) (x • τ)) =ᶠ[atTop ⊓ 𝓟 Sv]
        fun n => (v ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • F (φ n) τ := by
      filter_upwards [hSev] with n hn
      rw [hδ (φ n) x hx.1, hSmem n hn x hx]
    exact tendsto_nhds_unique (h1.congr' h3) h2
  obtain ⟨n₀, hn₀⟩ := hSinf.nonempty
  have hagE : ∀ x ∈ E, ∀ τ,
      Finf (x • Finf.symm τ) = F (φ n₀) (x • (F (φ n₀)).symm τ) := by
    intro x hx τ
    rw [hlimE x hx, hδ (φ n₀) x hx.1,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, hSmem n₀ hn₀ x hx]
  have hag := s30b_agree_closure hagE
  have hdeckI : ∀ γ ∈ ΓX, ∃ d ∈ ΓY, ∀ τ, Finf (γ • τ) = d • Finf τ := by
    intro γ hγ
    obtain ⟨d, hd, h⟩ := h23l_deck hX hY (hF (φ n₀)) hγ
    refine ⟨d, hd, fun τ => ?_⟩
    have e := hag γ (hgen hγ) (Finf τ)
    rw [Homeomorph.symm_apply_apply, h, Homeomorph.apply_symm_apply] at e
    exact e
  -- Recover inverse equivariance from the inverse of the same selected sequence lift.
  have hdeckI' : ∀ d ∈ ΓY, ∃ γ ∈ ΓX,
      ∀ τ, Finf.symm (d • τ) = γ • Finf.symm τ := by
    intro d hd
    obtain ⟨γ, hγ, h⟩ := h23l_deck hY hX (s27g_isLift_symm (hF (φ n₀))) hd
    refine ⟨γ, hγ, fun τ => ?_⟩
    have e := hag γ (hgen hγ) τ
    have h' : F (φ n₀) (γ • (F (φ n₀)).symm τ) = d • τ := by
      rw [← h, Homeomorph.apply_symm_apply]
    rw [h'] at e
    rw [← e, Homeomorph.symm_apply_apply]
  obtain ⟨c, hc⟩ := s30b_descend hX hY Finf hdeckI hdeckI'
  have hhom : ContinuousMap.Homotopic (c : C(X, Y)) (G (φ n₀) : C(X, Y)) := by
    refine (thm23_1_homotopy_iff hX hY c (G (φ n₀)) hc (hF (φ n₀))).2
      ⟨1, ΓY.one_mem, fun γ hγ τ => ?_⟩
    rw [inv_one, one_smul, one_smul]
    exact hag γ (hgen hγ) τ
  exact ⟨c, n₀, hc, hhom⟩

/-- **L: liminf for the same descended limit (package cap 850 LF including this header).**
If `L < maxDilatationRS c`, choose one finite real R strictly between. A further strict
subsequence below R converges locally uniformly to the same `Φl`; the displayed `EqOn` and
`IsLift` hypotheses bind it to the same `Finf` and `c`. Installed QC limit, lift/descent and
maximal-dilatation APIs give `maxDilatationRS c ≤ ofReal R`, a contradiction. This contract
neither returns a new limit nor asks for pointwise surface convergence in place of lift convergence. -/
theorem eq262_same_limit_liminf {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [T2Space Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    {K : ℝ} (G : ℕ → X ≃ₜ Y) (hG : ∀ n, IsKQCRS (G n) K)
    (F : ℕ → UpperHalfPlane ≃ₜ UpperHalfPlane) (φ : ℕ → ℕ)
    (Finf : UpperHalfPlane ≃ₜ UpperHalfPlane) (Φl : ℂ → ℂ) (c : X ≃ₜ Y)
    (hF : ∀ n, IsLift pX pY (G n) (F n)) (hφ : StrictMono φ)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => cayley ∘ (liftToC (F (φ n)) ∘ cayleyInv)) Φl atTop unitDisc)
    (hinj : InjOn Φl unitDisc)
    (hident : EqOn Φl (cayley ∘ (liftToC Finf ∘ cayleyInv)) unitDisc)
    (hFinf : IsKQC (liftToC Finf) upperHalf K) (hc : IsLift pX pY c Finf) :
    maxDilatationRS c ≤ liminf (fun n => maxDilatationRS (G (φ n))) atTop := by
  classical
  -- The shared contract records strictness of the selected indices. This
  -- liminf argument only needs the given convergence along those indices.
  have _hselected_strict : StrictMono φ := hφ
  have hcK : IsKQCRS c K := s27v_isKQCRS_of_lift hX hY hc hFinf
  have hcqc : IsQCRS c := ⟨K, hcK⟩
  let a : ℕ → ℝ≥0∞ := fun n => maxDilatationRS (G (φ n))
  let L : ℝ≥0∞ := liminf a atTop
  have ha1 : ∀ n, (1 : ℝ≥0∞) ≤ a n := fun n =>
    s29_m_one_le_maxDilatationRS (show IsQCRS (G (φ n)) from ⟨K, hG (φ n)⟩)
  have haK : ∀ n, a n ≤ ENNReal.ofReal K := fun n =>
    maxDilatationRS_le (hG (φ n))
  have hL1 : (1 : ℝ≥0∞) ≤ L := by
    change (1 : ℝ≥0∞) ≤ liminf a atTop
    exact Filter.le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall ha1)
  have hLK : L ≤ ENNReal.ofReal K :=
    Filter.liminf_le_of_frequently_le' (Eventually.of_forall haK).frequently
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLK
  have hdtop : maxDilatationRS c ≠ ⊤ := s29_m_maxDilatationRS_ne_top hcqc
  -- Finiteness is established before converting either endpoint to a real.
  change maxDilatationRS c ≤ L
  by_contra hbad
  have hLd : L < maxDilatationRS c := lt_of_not_ge hbad
  have hreal : L.toReal < (maxDilatationRS c).toReal :=
    (ENNReal.toReal_lt_toReal hLtop hdtop).2 hLd
  obtain ⟨R, hLR, hRd⟩ := exists_between hreal
  have hL1real : (1 : ℝ) ≤ L.toReal := by
    have h := ENNReal.toReal_mono hLtop hL1
    simpa only [ENNReal.toReal_one] using h
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt hL1real hLR
  have hR0 : (0 : ℝ) < R := zero_lt_one.trans hR1
  have hLofR : L < ENNReal.ofReal R :=
    (ENNReal.lt_ofReal_iff_toReal_lt hLtop).2 hLR
  have hRofd : ENNReal.ofReal R < maxDilatationRS c :=
    (ENNReal.ofReal_lt_iff_lt_toReal hR0.le hdtop).2 hRd
  have hfreq : ∃ᶠ n in atTop, a n < ENNReal.ofReal R :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault)
      (show liminf a atTop < ENNReal.ofReal R from hLofR)
  obtain ⟨ν, hν, hνR⟩ := Filter.extraction_of_frequently_atTop hfreq
  -- Recover the actual smaller QC bound from maximal dilatation. The
  -- original fixed K bound alone cannot certify R-QC when R is smaller.
  have hGR : ∀ n, IsKQCRS (G (φ (ν n))) R := fun n =>
    s29_m_isKQCRS_of_le
      (show IsQCRS (G (φ (ν n))) from ⟨K, hG (φ (ν n))⟩)
      hR1.le (hνR n).le
  have hFR : ∀ n, IsKQC (liftToC (F (φ (ν n)))) upperHalf R := fun n =>
    h23l_lift_isKQC hX hY (hGR n) (hF (φ (ν n)))
  have hdiscR : ∀ n,
      IsKQC (cayley ∘ (liftToC (F (φ (ν n))) ∘ cayleyInv)) unitDisc R :=
    fun n => (s30b_disc_conj (hFR n)).1
  have hlimν : TendstoLocallyUniformlyOn
      (fun n => cayley ∘ (liftToC (F (φ (ν n))) ∘ cayleyInv)) Φl atTop unitDisc :=
    s30b_tlu_comp hlim hν.tendsto_atTop
  have hΦR : IsKQC Φl unitDisc R :=
    UniversalTeichmuller.ut2_limit_isKQC isOpen_ball hdiscR hlimν hinj
  -- The identity is with the original Finf, so this image condition and
  -- every subsequent QC bound concern the same chosen limit.
  have hΦmaps : ∀ z ∈ unitDisc, Φl z ∈ unitDisc := by
    intro z hz
    rw [hident hz]
    exact (s30b_disc_conj hFinf).2 z hz
  have hC : IsKQC cayley upperHalf 1 :=
    isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley
  have hCI : IsKQC cayleyInv unitDisc 1 :=
    isKQC_one_of_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
  have hcomp1 : IsKQC (Φl ∘ cayley) upperHalf (1 * R) :=
    thm7_1_comp hC hΦR (by
      rintro _ ⟨z, hz, rfl⟩
      exact cayley_mem_unitDisc hz)
  have hcomp2 : IsKQC (cayleyInv ∘ (Φl ∘ cayley)) upperHalf ((1 * R) * 1) :=
    thm7_1_comp hcomp1 hCI (by
      rintro _ ⟨z, hz, rfl⟩
      exact hΦmaps _ (cayley_mem_unitDisc hz))
  have hback : IsKQC (cayleyInv ∘ (Φl ∘ cayley)) upperHalf R := by
    simpa only [one_mul, mul_one] using hcomp2
  have hFinfR : IsKQC (liftToC Finf) upperHalf R := by
    refine ad_isKQC_congr hback ?_
    intro z hz
    change liftToC Finf z = cayleyInv (Φl (cayley z))
    calc
      liftToC Finf z = (Finf ⟨z, hz⟩ : ℂ) := h23l_liftToC_coe Finf ⟨z, hz⟩
      _ = cayleyInv ((cayley ∘ (liftToC Finf ∘ cayleyInv)) (cayley z)) :=
        (s30b_recover Finf ⟨z, hz⟩).symm
      _ = cayleyInv (Φl (cayley z)) :=
        congrArg cayleyInv (hident (cayley_mem_unitDisc hz)).symm
  have hcR : IsKQCRS c R := s27v_isKQCRS_of_lift hX hY hc hFinfR
  exact (not_lt_of_ge (maxDilatationRS_le hcR)) hRofd

/-- **Consumer of P, D and L (within the collective 550-LF consumer/framing/repair cap).**
Bounded-K maps between two compact uniformized surfaces have one strict subsequential limit,
homotopic to one selected member, with the selected-sequence liminf bound. -/
theorem eq262_uniformized_limit {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [T2Space Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y]
    {ΓX ΓY : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {pX : UpperHalfPlane → X}
    {pY : UpperHalfPlane → Y} (hX : IsUniformization ΓX pX) (hY : IsUniformization ΓY pY)
    {K : ℝ} (G : ℕ → X ≃ₜ Y) (hG : ∀ n, IsKQCRS (G n) K) :
    ∃ (φ : ℕ → ℕ) (c : X ≃ₜ Y), StrictMono φ ∧ IsKQCRS c K ∧
      (∃ n₀ : ℕ, ContinuousMap.Homotopic (c : C(X, Y)) (G (φ n₀) : C(X, Y))) ∧
      (∀ x, Tendsto (fun n => G (φ n) x) atTop (𝓝 (c x))) ∧
      maxDilatationRS c ≤ liminf (fun n => maxDilatationRS (G (φ n))) atTop := by
  obtain ⟨CY, F, φ, Φl, Ψl, Finf, hCY, _hcoverY, hF, hFK, hφ, hlimΦ, _hlimΨ,
    _hΦmaps, _hΨmaps, hΨΦ, _hΦΨ, hΦeq, _hΨeq, hFinf, hconv⟩ :=
    eq262_paired_limit hX hY G hG
  obtain ⟨c, n₀, hc, hhom⟩ := eq262_deck_descend hX hY G F φ Finf hF hCY hFK hconv
  have hcqc : IsKQCRS c K := s27v_isKQCRS_of_lift hX hY hc hFinf
  have hΦinj : InjOn Φl unitDisc := by
    intro z hz w hw hzw
    calc z = Ψl (Φl z) := (hΨΦ z hz).symm
      _ = Ψl (Φl w) := congrArg Ψl hzw
      _ = w := hΨΦ w hw
  have hmax := eq262_same_limit_liminf hX hY G hG F φ Finf Φl c
    hF hφ hlimΦ hΦinj hΦeq hFinf hc
  refine ⟨φ, c, hφ, hcqc, ⟨n₀, hhom⟩, ?_, hmax⟩
  intro x
  obtain ⟨τ, rfl⟩ := hX.2.2.1 x
  have hpoint := (hY.1.continuous.tendsto (Finf τ)).comp (hconv τ)
  rw [hc τ] at hpoint
  exact hpoint.congr fun n => hF (φ n) τ

/-- (26.2): in the homotopy class of `f*` there is a sequence `fₙ` with `K[fₙ] → inf K[f]`; the
lifts of a sequence with bounded dilatation have a locally uniformly convergent subsequence
whose limit is a `K`-quasiconformal map homotopic to `f*` (§26.1, the proof of Theorem 26.1). -/
theorem eq26_2_limit_of_bounded_dilatation [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) (f₀ : S₀ ≃ₜ S₁) {K : ℝ} (fn : ℕ → S₀ ≃ₜ S₁)
    (hK : ∀ n, IsKQCRS (fn n) K)
    (hhom : ∀ n, ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) ((fn n : S₀ ≃ₜ S₁) : C(S₀, S₁))) :
    ∃ (φ : ℕ → ℕ) (f : S₀ ≃ₜ S₁), StrictMono φ ∧ IsKQCRS f K ∧
      ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)) ∧
      (∀ x, Tendsto (fun n => fn (φ n) x) atTop (𝓝 (f x))) ∧
      maxDilatationRS f ≤ liminf (fun n => maxDilatationRS (fn (φ n))) atTop := by
  -- Reuse the installed common-universe charts and transport APIs.
  let : ChartedSpace S₀ (ULift.{v} S₀) :=
    (Homeomorph.ulift.toOpenPartialHomeomorph).singletonChartedSpace (by simp)
  let : ChartedSpace ℂ (ULift.{v} S₀) := ChartedSpace.comp ℂ S₀ (ULift.{v} S₀)
  let : ChartedSpace S₁ (ULift.{u} S₁) :=
    (Homeomorph.ulift.toOpenPartialHomeomorph).singletonChartedSpace (by simp)
  let : ChartedSpace ℂ (ULift.{u} S₁) := ChartedSpace.comp ℂ S₁ (ULift.{u} S₁)
  have hX : ∀ x : ULift.{v} S₀,
      chartAt ℂ x = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ x.down) := fun x => rfl
  have hY : ∀ y : ULift.{u} S₁,
      chartAt ℂ y = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ y.down) := fun y => rfl
  have : IsManifold 𝓘(ℂ) ω (ULift.{v} S₀) := utm_ul_isManifold fun e he => utm_ul_atlas e he
  have : IsManifold 𝓘(ℂ) ω (ULift.{u} S₁) := utm_ul_isManifold fun e he => utm_ul_atlas e he
  have : ConnectedSpace (ULift.{v} S₀) := Homeomorph.ulift.symm.surjective.connectedSpace
    Homeomorph.ulift.symm.continuous
  have : ConnectedSpace (ULift.{u} S₁) := Homeomorph.ulift.symm.surjective.connectedSpace
    Homeomorph.ulift.symm.continuous
  have h₀' := utm_ul_hasGenus (X := S₀) h₀
  have h₁' := utm_ul_hasGenus (X := S₁) h₁
  have : CompactSpace (ULift.{v} S₀) := h₀'.1
  have : CompactSpace (ULift.{u} S₁) := h₁'.1
  let G : ℕ → ULift.{v} S₀ ≃ₜ ULift.{u} S₁ :=
    fun n => Homeomorph.ulift.trans ((fn n).trans Homeomorph.ulift.symm)
  have hG : ∀ n, IsKQCRS (G n) K :=
    fun n => ((utm_ul_transfer hX hY (fn n)).2.1 K).2 (hK n)
  obtain ⟨ΓX, pX, _hΓX, _hfreeX, hpX⟩ :=
    s22hg_exists_fuchsian_uniformization (S := ULift.{v} S₀) hg h₀'
  obtain ⟨ΓY, pY, _hΓY, _hfreeY, hpY⟩ :=
    s22hg_exists_fuchsian_uniformization (S := ULift.{u} S₁) hg h₁'
  obtain ⟨φ, c, hφ, hcqc, ⟨n₀, hcmember⟩, hpoint, hmax⟩ := eq262_uniformized_limit hpX hpY G hG
  let f : S₀ ≃ₜ S₁ := Homeomorph.ulift.symm.trans (c.trans Homeomorph.ulift)
  have hfc :
      (Homeomorph.ulift.trans (f.trans Homeomorph.ulift.symm) : ULift.{v} S₀ ≃ₜ ULift.{u} S₁) = c := by
    ext x
    rfl
  have hTf := utm_ul_transfer hX hY f
  rw [hfc] at hTf
  have hclass : ContinuousMap.Homotopic
      ((Homeomorph.ulift.trans (f₀.trans Homeomorph.ulift.symm) : ULift.{v} S₀ ≃ₜ ULift.{u} S₁) :
        C(ULift.{v} S₀, ULift.{u} S₁)) (c : C(ULift.{v} S₀, ULift.{u} S₁)) := by
    have hmember : ContinuousMap.Homotopic
        ((Homeomorph.ulift.trans (f₀.trans Homeomorph.ulift.symm) : ULift.{v} S₀ ≃ₜ ULift.{u} S₁) :
          C(ULift.{v} S₀, ULift.{u} S₁)) (G (φ n₀) : C(ULift.{v} S₀, ULift.{u} S₁)) :=
      (utm_ul_homotopic f₀ (fn (φ n₀))).1 (hhom (φ n₀))
    exact hmember.trans hcmember.symm
  refine ⟨φ, f, hφ, (hTf.2.1 K).1 hcqc, ?_, ?_, ?_⟩
  · apply (utm_ul_homotopic f₀ f).2
    rw [hfc]
    exact hclass
  · intro x
    have hdown := ((Homeomorph.ulift : ULift.{u} S₁ ≃ₜ S₁).continuous.tendsto (c (ULift.up x))).comp
      (hpoint (ULift.up x))
    change Tendsto (fun n => fn (φ n) x) atTop (𝓝 (f x)) at hdown
    exact hdown
  · have hterms : (fun n => maxDilatationRS (G (φ n))) =
        (fun n => maxDilatationRS (fn (φ n))) := by
      funext n
      exact (utm_ul_transfer hX hY (fn (φ n))).1
    rw [hTf.1, hterms] at hmax
    exact hmax

/-- **Theorem 26.1**: in the Teichmüller extremal problem (closed surfaces of genus `g > 1`,
`f* : S₀ → S₁` an orientation preserving homeomorphism) an extremal map always exists. -/
theorem thm26_1_extremal_exists [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) (f₀ : S₀ ≃ₜ S₁) (hf₀ : IsOrientationPreservingRS f₀) :
    ∃ f : S₀ ≃ₜ S₁, ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)) ∧
      IsExtremalInHomotopyClass f := by
  -- both surfaces as `ULift` copies in the common universe `max u v`, with the charts `ulift ≫ chart`
  let : ChartedSpace S₀ (ULift.{v} S₀) :=
    (Homeomorph.ulift.toOpenPartialHomeomorph).singletonChartedSpace (by simp)
  let : ChartedSpace ℂ (ULift.{v} S₀) := ChartedSpace.comp ℂ S₀ (ULift.{v} S₀)
  let : ChartedSpace S₁ (ULift.{u} S₁) :=
    (Homeomorph.ulift.toOpenPartialHomeomorph).singletonChartedSpace (by simp)
  let : ChartedSpace ℂ (ULift.{u} S₁) := ChartedSpace.comp ℂ S₁ (ULift.{u} S₁)
  have hX : ∀ x : ULift.{v} S₀,
      chartAt ℂ x = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ x.down) := fun x => rfl
  have hY : ∀ y : ULift.{u} S₁,
      chartAt ℂ y = Homeomorph.ulift.toOpenPartialHomeomorph.trans (chartAt ℂ y.down) := fun y => rfl
  have : IsManifold 𝓘(ℂ) ω (ULift.{v} S₀) := utm_ul_isManifold fun e he => utm_ul_atlas e he
  have : IsManifold 𝓘(ℂ) ω (ULift.{u} S₁) := utm_ul_isManifold fun e he => utm_ul_atlas e he
  have : ConnectedSpace (ULift.{v} S₀) := Homeomorph.ulift.symm.surjective.connectedSpace
    Homeomorph.ulift.symm.continuous
  have : ConnectedSpace (ULift.{u} S₁) := Homeomorph.ulift.symm.surjective.connectedSpace
    Homeomorph.ulift.symm.continuous
  have h₀' := utm_ul_hasGenus (X := S₀) h₀
  have h₁' := utm_ul_hasGenus (X := S₁) h₁
  have : CompactSpace (ULift.{v} S₀) := h₀'.1
  have : CompactSpace (ULift.{u} S₁) := h₁'.1
  -- Theorem 27.2 for the copies: a Teichmüller (or conformal) map, extremal in the class of the copy of `f₀`
  obtain ⟨G, hG, -, hGext, -⟩ := thm27_2_existence hg h₀' h₁' _ ((utm_ul_transfer hX hY f₀).2.2 hf₀)
  -- back to `S₀ → S₁`
  set F : S₀ ≃ₜ S₁ := Homeomorph.ulift.symm.trans (G.trans Homeomorph.ulift) with hF
  have hFG : (Homeomorph.ulift.trans (F.trans Homeomorph.ulift.symm) : ULift.{v} S₀ ≃ₜ ULift.{u} S₁) = G := by
    ext x
    rfl
  have hT := utm_ul_transfer hX hY F
  rw [hFG] at hT
  refine ⟨F, (utm_ul_homotopic f₀ F).2 (by rw [hFG]; exact hG), ?_, fun f hf hFf => ?_⟩
  · obtain ⟨K, hK⟩ := hGext.1
    exact ⟨K, (hT.2.1 K).1 hK⟩
  · obtain ⟨K, hK⟩ := hf
    have hT' := utm_ul_transfer hX hY f
    have hle := hGext.2 _ ⟨K, (hT'.2.1 K).2 hK⟩ (by rw [← hFG]; exact (utm_ul_homotopic F f).1 hFf)
    rw [← hT.1, ← hT'.1]
    exact hle

/-! ### §27.2: the deformation image, relocated after the existence and parametrization results. -/

/-- Transfer Euclidean IoD to the actual Fricke coordinate type. -/
theorem s27io_fricke_image_open {g : ℕ} (hg : 1 < g)
    {Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
      Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    (hc : ContinuousOn Ψ (ball 0 1)) (hi : InjOn Ψ (ball 0 1)) :
    IsOpen (Ψ '' ball 0 1) := by
  have hdim : Module.finrank ℝ (Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (6 * g - 6))) := by
    simp [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin] <;> omega
  let A : (Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6)) := ContinuousLinearEquiv.ofFinrankEq hdim
  have hA : IsOpen ((fun v => A (Ψ v)) '' ball 0 1) :=
    LiZhongExternal.Topology.invariance_of_domain_innerProduct
      _ _ isOpen_ball (A.continuous.comp_continuousOn hc)
      (fun x hx y hy hxy => hi hx hy (A.injective hxy))
  have heq : (fun v => A (Ψ v)) '' ball 0 1 = A '' (Ψ '' ball 0 1) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Ψ v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  exact A.toHomeomorph.isOpen_image.1 (heq ▸ hA)

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- Normalize an existing deformation, retaining its parameter and marked class.
The positive rescaling uses the existing UTM convenience lemma. -/
theorem s27io_normalize {g : ℕ}
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6)))
    {q : S₀ → ℂ → ℂ} {k : ℝ} {p : TeichSpace S₀}
    (h : IsDeformationPoint q k p) :
    ∃ q₁ : (holQuadDiffSubmodule S₀).restrictScalars ℝ,
      ‖e q₁‖ = 1 ∧ IsDeformationPoint q₁ k p ∧ 0 ≤ k ∧ k < 1 := by
  obtain ⟨X, f, hqc, q', hT, hp⟩ := h
  let qR : (holQuadDiffSubmodule S₀).restrictScalars ℝ := ⟨q, hT.initial⟩
  have hqR : qR ≠ 0 := fun hz => hT.initial_ne (congrArg Subtype.val hz)
  have hn : 0 < ‖e qR‖ := norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff e).2 hqR)
  let q₁ : (holQuadDiffSubmodule S₀).restrictScalars ℝ := ‖e qR‖⁻¹ • qR
  have hnorm : ‖e q₁‖ = 1 := by
    change ‖e (‖e qR‖⁻¹ • qR)‖ = 1
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']
  have hcoe : (q₁ : S₀ → ℂ → ℂ) = ((‖e qR‖⁻¹ : ℝ) : ℂ) • q := by
    change ((‖e qR‖⁻¹ • qR : (holQuadDiffSubmodule S₀).restrictScalars ℝ) :
      S₀ → ℂ → ℂ) = _
    rw [Submodule.coe_smul_of_tower]
    funext x z
    simp [qR, Complex.real_smul]
  refine ⟨q₁, hnorm, ?_, hT.k_nonneg, hT.k_lt_one⟩
  rw [hcoe]
  exact utm_x_isDeformationPoint_smul
    ⟨X, f, hqc, q', hT, hp⟩ (inv_pos.2 hn)

/-- Exact image equality from the existing positive-parameter clause plus
explicit zero-parameter and realization clauses. Neither missing clause follows
by destructuring the published statement of Lemma 27.1 alone. -/
theorem s27io_image_eq {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6)))
    (Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
      Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))
    (hcoord : ∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ),
      ‖e q‖ = 1 → 0 < k → k < 1 → ∀ m : MarkedRS S₀,
      IsDeformationPoint q k (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ (k • e q)))
    (hzero : ∀ (m : MarkedRS S₀) (q : S₀ → ℂ → ℂ),
      IsDeformationPoint q 0 (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ 0))
    (hrealize : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      ∃ (m : MarkedRS S₀) (q : S₀ → ℂ → ℂ) (k : ℝ),
        IsDeformationPoint q k (Quot.mk _ m) ∧ IsFrickeCoords p₀ G m (Ψ v)) :
    deformationImage p₀ G = Ψ '' ball 0 1 := by
  ext c
  constructor
  · rintro ⟨m, q, k, hdef, hc⟩
    obtain ⟨q₁, hnorm, hdef₁, hk0, hk1⟩ := s27io_normalize e hdef
    by_cases hk : k = 0
    · subst k
      refine ⟨0, mem_ball_self (by norm_num), ?_⟩
      exact s27v_fricke_eq_of_equiv hg hS hp₀ G
        (markedRS_equiv_equivalence.refl m) (hzero m q hdef) hc
    · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
      refine ⟨k • e q₁, ?_, ?_⟩
      · apply mem_ball_zero_iff.2
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hkpos, hnorm, mul_one] using hk1
      · exact s27v_fricke_eq_of_equiv hg hS hp₀ G
          (markedRS_equiv_equivalence.refl m) (hcoord q₁ k hnorm hkpos hk1 m hdef₁) hc
  · rintro ⟨v, hv, rfl⟩
    exact hrealize v hv

/-- Final short consumer against the port endpoint, given the minimal map interface. -/
theorem s27io_open_consumer {g : ℕ} (hg : 1 < g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (G : StandardGenerators Γ₀ g)
    (hparam : ∃ Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
        Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ),
      ContinuousOn Ψ (ball 0 1) ∧ InjOn Ψ (ball 0 1) ∧
      deformationImage p₀ G = Ψ '' ball 0 1) :
    IsOpen (deformationImage p₀ G) := by
  obtain ⟨Ψ, hc, hi, himage⟩ := hparam
  rw [himage]
  exact s27io_fricke_image_open hg hc hi

end

/-- A genus greater than one supplies a unit direction in the chosen real coordinates. -/
theorem s27oi_unit_direction {g : ℕ} (hg : 1 < g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ q : (holQuadDiffSubmodule S₀).restrictScalars ℝ, ‖e q‖ = 1 := by
  letI : Nonempty (Fin (6 * g - 6)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin (6 * g - 6))) zero_le_one
  exact ⟨e.symm v, by simpa only [LinearEquiv.apply_symm_apply] using hv⟩

/-- A zero-parameter deformation has the base Fricke coordinates. -/
theorem s27oi_zero_coords [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g) {m : MarkedRS S₀} {q : S₀ → ℂ → ℂ}
    (hm : IsDeformationPoint q 0 (Quot.mk _ m))
    {c : Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    (hc : IsFrickeCoords p₀ G m c) : c = frickeCoordinates G := by
  obtain ⟨X, f, hqc, q', hT, hquot⟩ := hm
  let md : MarkedRS S₀ := ⟨X, f, hqc⟩
  let mb : MarkedRS S₀ := ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩
  have hmd : m.Equiv md :=
    markedRS_equiv_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact hquot)
  have hdb : md.Equiv mb := by
    apply s27v_equiv_of_liftCoeff hg hS hp₀
    filter_upwards [(s27v_liftCoeff_deformation_bound hp₀ hT).2,
      (s27v_base hp₀ G).2] with z hz hzb
    exact (norm_le_zero_iff.1 hz).trans hzb.symm
  exact s27v_fricke_eq_of_equiv hg hS hp₀ G
    (markedRS_equiv_equivalence.trans hmd hdb) hc (s27v_base hp₀ G).1

/-- Continuity and the positive-radius coordinate clause force the value at the origin. -/
theorem s27oi_origin [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6)))
    {Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
      Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    (hcont : ContinuousOn Ψ (ball 0 1))
    (hcoords : ∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ),
      ‖e q‖ = 1 → 0 < k → k < 1 → ∀ m : MarkedRS S₀,
      IsDeformationPoint q k (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ (k • e q))) :
    Ψ 0 = frickeCoordinates G := by
  classical
  obtain ⟨q, hq⟩ := s27oi_unit_direction hg e
  have hqne : (q : S₀ → ℂ → ℂ) ≠ 0 := by
    intro hz
    have hzq : q = 0 := Subtype.ext hz
    simp only [hzq, map_zero, norm_zero] at hq
    exact zero_ne_one hq
  let k : ℕ → ℝ := fun n => (1 / 2) ^ (n + 1)
  have hkpos : ∀ n, 0 < k n := fun n => pow_pos (by norm_num) _
  have hkle : ∀ n, k n ≤ 1 / 2 := by
    intro n
    dsimp [k]
    rw [pow_succ]
    have hn : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hklt : ∀ n, k n < 1 := fun n => lt_of_le_of_lt (hkle n) (by norm_num)
  have hkconv : Tendsto k atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp
      (tendsto_add_atTop_nat 1)
  have hex : ∀ n, ∃ (X : ClosedRS.{u}) (f : S₀ ≃ₜ X.carrier)
      (q' : X.carrier → ℂ → ℂ), IsTeichDeformation q (k n) X f q' := by
    intro n
    exact exists_teichDeformation q.2 hqne (hkpos n).le (hklt n)
  choose X f q' hT using hex
  let mn : ℕ → MarkedRS S₀ := fun n =>
    ⟨X n, f n, (teichDeformation_isTeichmullerMap (hT n)).qc⟩
  let mb : MarkedRS S₀ := ⟨⟨S₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩
  have hcn : ∀ n, IsFrickeCoords p₀ G (mn n) (Ψ (k n • e q)) := by
    intro n
    exact hcoords q (k n) hq (hkpos n) (hklt n) (mn n)
      ⟨X n, f n, (mn n).qc, q' n, hT n, rfl⟩
  have hμb : IsBeltramiCoeff (s27u_liftCoeff p₀ mb.marking) upperHalf (1 / 2) := by
    have hid : IsKQCRS (Homeomorph.refl S₀) 1 :=
      (isKQCRS_one_iff _).2 isBiholomorphic_id
    exact s27v_isBeltramiCoeff_mono (s27u_liftCoeff_isBeltramiCoeff hp₀ hid) (by norm_num)
  have hlim : Tendsto (fun n => Ψ (k n • e q)) atTop (𝓝 (frickeCoordinates G)) := by
    refine s27v_fricke_tendsto hg hS hp₀ G (mn := mn) (m := mb) (k := 1 / 2)
      (by norm_num) (by norm_num)
      (fun n => s27v_isBeltramiCoeff_mono
        (s27v_liftCoeff_deformation_bound hp₀ (hT n)) (hkle n)) hμb ?_ hcn (s27v_base hp₀ G).1
    have hae : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ n,
        ‖s27u_liftCoeff p₀ (mn n).marking z‖ ≤ k n :=
      ae_all_iff.2 fun n => (s27v_liftCoeff_deformation_bound hp₀ (hT n)).2
    filter_upwards [hae, (s27v_base hp₀ G).2] with z hz hzb
    change Tendsto _ atTop (𝓝 (s27u_liftCoeff p₀ (Homeomorph.refl S₀) z))
    rw [hzb]
    exact squeeze_zero_norm hz hkconv
  have hzero : (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) ∈ ball 0 1 :=
    mem_ball_self (by norm_num)
  have hΨ0 : ContinuousAt Ψ 0 :=
    (hcont 0 hzero).continuousAt (isOpen_ball.mem_nhds hzero)
  have hvconv : Tendsto (fun n => k n • e q) atTop (𝓝 0) := by
    simpa only [zero_smul] using hkconv.smul_const (e q)
  exact tendsto_nhds_unique (hΨ0.tendsto.comp hvconv) hlim

/-- The open-ball image of the map of Lemma 27.1 is the relational deformation image. -/
theorem s27oi_image [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6)))
    {Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
      Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)}
    (hcont : ContinuousOn Ψ (ball 0 1))
    (hcoords : ∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ),
      ‖e q‖ = 1 → 0 < k → k < 1 → ∀ m : MarkedRS S₀,
      IsDeformationPoint q k (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ (k • e q))) :
    Ψ '' ball 0 1 = deformationImage p₀ G := by
  classical
  have hΨ0 := s27oi_origin hg hS hp₀ G e hcont hcoords
  have hbij := thm27_fricke_bijection hg hS hp₀ G
  have hrealize : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1,
      ∃ (m : MarkedRS S₀) (q : S₀ → ℂ → ℂ) (k : ℝ),
        IsDeformationPoint q k (Quot.mk _ m) ∧ IsFrickeCoords p₀ G m (Ψ v) := by
    intro v hv
    have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
    by_cases hv0 : v = 0
    · subst v
      obtain ⟨q, hq⟩ := s27oi_unit_direction hg e
      have hqne : (q : S₀ → ℂ → ℂ) ≠ 0 := by
        intro hz
        have hzq : q = 0 := Subtype.ext hz
        simp only [hzq, map_zero, norm_zero] at hq
        exact zero_ne_one hq
      obtain ⟨X, f, q', hT⟩ := exists_teichDeformation q.2 hqne le_rfl zero_lt_one
      let m : MarkedRS S₀ := ⟨X, f, (teichDeformation_isTeichmullerMap hT).qc⟩
      have hm : IsDeformationPoint q 0 (Quot.mk _ m) := ⟨X, f, m.qc, q', hT, rfl⟩
      obtain ⟨c, hc⟩ := hbij.1 m
      have he := s27oi_zero_coords hg hS hp₀ G hm hc
      rw [he, ← hΨ0] at hc
      exact ⟨m, q, 0, hm, hc⟩
    · let q : (holQuadDiffSubmodule S₀).restrictScalars ℝ := e.symm (‖v‖⁻¹ • v)
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
      have hq : ‖e q‖ = 1 := by
        change ‖e (e.symm (‖v‖⁻¹ • v))‖ = 1
        rw [LinearEquiv.apply_symm_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
      have hrec : ‖v‖ • e q = v := by
        change ‖v‖ • e (e.symm (‖v‖⁻¹ • v)) = v
        rw [LinearEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ hvn, one_smul]
      have hqne : (q : S₀ → ℂ → ℂ) ≠ 0 := by
        intro hz
        have hzq : q = 0 := Subtype.ext hz
        simp only [hzq, map_zero, norm_zero] at hq
        exact zero_ne_one hq
      obtain ⟨X, f, q', hT⟩ := exists_teichDeformation q.2 hqne (norm_nonneg v) hv1
      let m : MarkedRS S₀ := ⟨X, f, (teichDeformation_isTeichmullerMap hT).qc⟩
      have hm : IsDeformationPoint q ‖v‖ (Quot.mk _ m) := ⟨X, f, m.qc, q', hT, rfl⟩
      have hc := hcoords q ‖v‖ hq (norm_pos_iff.2 hv0) hv1 m hm
      rw [hrec] at hc
      exact ⟨m, q, ‖v‖, hm, hc⟩
  have hzero : ∀ (m : MarkedRS S₀) (q : S₀ → ℂ → ℂ),
      IsDeformationPoint q 0 (Quot.mk _ m) → IsFrickeCoords p₀ G m (Ψ 0) := by
    intro m q hm
    obtain ⟨c, hc⟩ := hbij.1 m
    have he := s27oi_zero_coords hg hS hp₀ G hm hc
    rwa [he, ← hΨ0] at hc
  exact (s27io_image_eq hg hS hp₀ G e Ψ hcoords hzero hrealize).symm

/-- The proved minimal map input for s27io_open_consumer. -/
theorem s27oi_exists_map [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (6 * g - 6)) →
      Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ),
      ContinuousOn Ψ (ball 0 1) ∧ InjOn Ψ (ball 0 1) ∧
      deformationImage p₀ G = Ψ '' ball 0 1 := by
  obtain ⟨Ψ, hcont, hinj, hcoords⟩ := lemma27_1_continuous_injective hg hS hp₀ G e
  exact ⟨Ψ, hcont, hinj, (s27oi_image hg hS hp₀ G e hcont hcoords).symm⟩

/-- Every marked class has a deformation representative, including the conformal
class (`s29_t1_param`), so the two sets of Fricke coordinates agree. This equality
uses neither invariance of domain nor any openness or boundary theorem. -/
theorem s27io_deformationImage_eq_frickeSpace [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (G : StandardGenerators Γ₀ g) :
    deformationImage p₀ G = frickeSpace p₀ G := by
  -- Uniformization is retained to match the book's calling convention; the
  -- equality of these two relational images only needs surjectivity onto classes.
  have _hp₀ := hp₀
  obtain ⟨_, e, _⟩ := teichDeformationSpace_parameters hg hS
  obtain ⟨Φ, _, hsurj, _, hdef⟩ := s29_t1_param hg hS e
  ext c
  constructor
  · rintro ⟨m, q, k, _, hc⟩
    exact ⟨m, hc⟩
  · rintro ⟨m, hc⟩
    obtain ⟨v, hv, hvm⟩ := hsurj (Quot.mk _ m)
    obtain ⟨q, _, hq, _⟩ := hdef v hv
    rw [hvm] at hq
    exact ⟨m, q, ‖v‖, hq, hc⟩

/-- §27.2: by Lemma 27.1 and Brouwer's invariance of domain, `Ψ ∘ Φ(T̃(S₀))` is open. -/
theorem deformationImage_isOpen [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    IsOpen (deformationImage p₀ G) := by
  obtain ⟨_, e, _⟩ := teichDeformationSpace_parameters hg hS
  exact s27io_open_consumer hg G (s27oi_exists_map hg hS hp₀ G e)

/-- **Lemma 27.3**: no boundary point of `Ψ ∘ Φ(T̃(S₀))` lies in `F(S₀)`.  (Along the path
`t ↦ Ψ([S_t, f_t])` from `χ₀ = Ψ([S₀, id])` the first point `t*` outside the image would be a boundary
point; but for `tₙ → t*` the deformations `S_{qₙ,kₙ}` representing `[S_{tₙ}, f_{tₙ}]` have
`kₙ ≤ (K[f] - 1)/(K[f] + 1) < 1`, so they stay in a smaller ball and cannot approach the boundary
of `T̃(S₀)`.) -/
theorem lemma27_3_boundary [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    ∀ c ∈ frontier (deformationImage p₀ G), c ∉ frickeSpace p₀ G := by
  intro c hc hF
  rw [(deformationImage_isOpen hg hS hp₀ G).frontier_eq] at hc
  rw [← s27io_deformationImage_eq_frickeSpace hg hS hp₀ G] at hF
  exact hc.2 hF

/-- §27.2: `Ψ ∘ Φ` maps `T̃(S₀)` homeomorphically onto `F(S₀)`: the image is a connected open subset
of the connected set `F(S₀)` without boundary points in `F(S₀)`, hence all of `F(S₀)`; the
continuity of the inverse follows from continuity and injectivity on the ball (Brouwer). -/
theorem deformationImage_eq_frickeSpace [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [CompactSpace S₀] {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) :
    deformationImage p₀ G = frickeSpace p₀ G ∧ IsOpen (frickeSpace p₀ G) := by
  have heq := s27io_deformationImage_eq_frickeSpace hg hS hp₀ G
  exact ⟨heq, heq ▸ deformationImage_isOpen hg hS hp₀ G⟩

end LiZhongQC
