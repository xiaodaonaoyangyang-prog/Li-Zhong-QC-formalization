/-
# Extending homeomorphisms of `S¹`, and dependence on `φ` (Sections 3 and 4)

* The barycentric equation and the extension operator `E`
                                        — `baryEq`, `extension`
* Lemma 2 (continuity at the boundary)  — `extension_continuousAt_boundary`
                                          (proved)
* Theorem 1 (Φ is a diffeomorphism of `D`, homeomorphism of `D̄`)
                                        — `extension_isHomeomorphOn`,
                                          `extension_analyticOn_disk`
* Lemma 3                               — `lemma3_fourier_coeff`
* Proposition 2 (continuity of `E`)     — `extension_continuous_boundary`,
                                          `extension_analytic_jointly`
* Corollary                             — `extension_derivative_continuous`

Proved in full here: `barycenter_existsUnique`, the instance of Proposition 1
that makes `extension` well defined at all — so `extension` itself, and with it
every statement about `Φ = E(φ)` in this development, is now free of `sorryAx`;
`extension_eq_boundary` (`Φ = φ` on `S¹`); `extension_naturality` (conformal
naturality); `extension_id` (`E(id) = id`); the elementary four sine inequality
used at the end of the proof of Lemma 3 (`sin_add_lt_sin_add_sin`,
`four_sin_pos_of_pi_le`, `four_sin_pos`); and the whole non-analytic half of
the Jacobian part of Theorem 1 — implicit differentiation of (3.1)
(`baryFn_hasFDerivAt_graph`), its reading in Wirtinger form
(`wirt_implicit_of_graph_eq_zero`), the elimination identity
(`implicit_jacobian_identity`, `norm_lt_of_implicit`, `norm_ne_of_implicit`),
and their combinations `extension_jacobian_of_implicit` and
`extension_jacobian_ne_of_implicit`; `extension_analyticOn_disk`, the
real-analyticity half of Theorem 1; and, in Section 4,
`extension_continuous_boundary` outright together with the identification step
of `extension_analytic_jointly`, its corollary `extension_continuousOn_pair`,
and the Corollary `extension_derivative_continuous`.  The homeomorphism half of
Theorem 1 is assembled in `extension_isHomeomorphOn` from
`mapsTo_extension`, `continuousOn_extension` and the compactness argument
`exists_continuousOn_invOn_of_bijOn`, leaving only injectivity and surjectivity
to `extension_injOn_surjOn`.  The remark after
Theorem 1 (`extension_unique_characterization`) is proved outright, with
`extension_satisfies_unique_characterization` checking that its hypotheses are
not vacuous, and `lemma3_fourier_coeff_false` records that Lemma 3 was stated
without the orientation hypothesis it needs.

Lemma 2 is now proved, not cited: `extension_continuousAt_boundary` is free of
`sorryAx`.  So is `exists_analytic_baryEq_solution`, the analytic input to
Theorem 1 and Proposition 2, and with it `extension_analyticOn_disk` (the
real-analyticity half of Theorem 1), `continuousOn_extension` (`Φ` is
continuous on `D̄`), and the whole of Proposition 2 and its Corollary.  The
route is `analyticAt_baryFnMap` — (3.1) read inside the Banach algebra
`C(S¹, ℂ)`, where it is built from ring operations and inversion and is
therefore analytic — fed to `exists_analytic_implicit`, the analytic implicit
function theorem in Banach spaces, which is assembled here from two Mathlib
results that are not otherwise combined.

`extension_injOn_surjOn`, the topological half of Theorem 1, is proved too, and
no longer cited: §7's covering-space argument is carried out in `ProperLH`, on
the one covering-theoretic fact Mathlib is missing — that paths lift through a
proper local homeomorphism.

**Theorem 1 is proved.**  All three of its clauses —
`extension_isHomeomorphOn`, `extension_analyticOn_disk` and
`extension_jacobian_ne_zero` — are free of `sorryAx`, as are Proposition 2 and
the Corollary.

The last two pieces to go in were Lemma 3 and §4.3.  Lemma 3
(`lemma3_fourier_coeff`) has a Fourier half, identifying `c₁` and `c₋₁` with
the pairings of `φ` against `e^{∓iθ}` (`Lemma3.integral_eq_of_L2`), and a
determinant half, turning `|c₁|² − |c₋₁|²` into `4(ad − bc)` and proving
`ad − bc > 0` from the four-sine inequality (`Lemma3.det_pos`).  §4.3
(`exists_implicit_fderiv_z`) transports it to the `z`-derivative of (3.1) at
`(z, Φ(z))`, through conformal naturality (`ZDeriv.baryFn_naturality`) and
formula (3.2) at the origin (`ZDeriv.hasFDerivAt_baryFnMap_z_zero`).  Since
Theorem 1 holds for *both* orientations, this needs Lemma 3 in a form with no
orientation hypothesis, and `CircleLift` supplies it: every homeomorphism of
`S¹` has a strictly monotone lift of degree `±1`, so `|c₁| ≠ |c₋₁|` always,
with the sign recording the orientation.

`exists_implicit_fderiv_z_of_orient`, the *strict* `z`-derivative under
`HasIncreasingLift`, is proved too, so **this file is free of `sorry`**.
Sections 6 and 7 need the strict form because they require `Φ_z ≠ 0` rather
than a merely invertible differential.  What it costs beyond the nondegenerate
form is that the normalized map `χ = ψ_g ∘ φ ∘ ψ_k` must *inherit* `φ`'s
orientation, and for that a lift of a Möbius map of `S¹` has to be written
down: `CircleLift.mobLift r t = t + 2 arctan(r sin t/(1 - r cos t))`, whose
derivative is the Poisson kernel `(1 - r²)/(1 - 2r cos t + r²) > 0`.  The
section header before `CircleLift.mobLift` says how that fits together.

The sign matters, and getting it wrong is what `extension_jacobian_ne_zero_false`
records: the Jacobian clause of Theorem 1 used to be stated as
`|Φ_z̄| < |Φ_z|`, and `φ(ζ) = ζ⁻¹` refutes it, because `E(ζ ↦ ζ⁻¹) = conj`
(`extension_conj`).  Theorem 1 is true for every homeomorphism of `S¹`; it is
the *positivity* of the Jacobian, not its nonvanishing, that needs orientation.
-/
import Mathlib
import DouadyEarle.Basic

open MeasureTheory Real Set Complex

noncomputable section

/-! ## Section 3: the extension operator -/

/-- The barycentric equation at `z ∈ D` with candidate value `w`, for a
homeomorphism `φ` of `S¹` (formula (3.1)):
`F(z, w) = ⨍ (φ(ζ) - w)/(1 - conj(w) φ(ζ)) dη_z(ζ) = 0`. -/
def baryEq (φ : Circle → Circle) (z w : ℂ) : Prop :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
    (((φ (Circle.exp θ) : ℂ) - w) / (1 - star w * (φ (Circle.exp θ) : ℂ))) *
      (poissonKernelDisk z (Circle.exp θ) : ℂ) = 0

/-- The left-hand side of (3.1) as a function of the pair `(z, w)`: the
function the paper calls `F`, whose zero set in `w` defines `Φ`.  `baryEq` is
its vanishing, so the two are interchangeable; `baryFn` is the form needed when
`F` has to be differentiated. -/
def baryFn (φ : Circle → Circle) (z w : ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
    (((φ (Circle.exp θ) : ℂ) - w) / (1 - star w * (φ (Circle.exp θ) : ℂ))) *
      (poissonKernelDisk z (Circle.exp θ) : ℂ)

theorem baryEq_iff_baryFn (φ : Circle → Circle) (z w : ℂ) :
    baryEq φ z w ↔ baryFn φ z w = 0 := Iff.rfl

/-! ### Proposition 1 for `φ_*(η_z)`

The barycentric equation (3.1) is the vanishing of the average of `g_w` against
the measure `φ_*(η_z)`, and Proposition 1 is what makes that vanish at exactly
one point of `D`.  The measure has no density of its own — a homeomorphism of
`S¹` need not carry harmonic measure to an absolutely continuous measure, so
there is nothing to feed to `conformal_barycenter_existsUnique` — but it never
has to appear as one: (3.1) is an integral in `θ` against the *continuous*
Poisson density `P_z(e^{iθ})`, with the boundary point `e^{iθ}` replaced by
`φ(e^{iθ})`.  That is exactly the boundary family of
`avgDiskAut_zero_existsUnique`.

`Continuous φ` is needed and is not implied by `Function.Bijective φ`.  The
paper says "homeomorphism of `S¹`" throughout, so this is a hypothesis restored
rather than added, and `barycenter_existsUnique_false_of_nonintegrable` below
records exactly what it is buying: `baryEq` is a Bochner integral, so on any
`φ` for which the integrand fails to be integrable Lean's convention makes the
integral `0` and (3.1) then holds at *every* `w` at once, destroying
uniqueness. -/

/-- The Poisson kernel of an interior point, read along `θ ↦ e^{iθ}`, is a
probability density on `S¹`. -/
theorem isProbabilityDensity_poissonKernelDisk {z : ℂ} (hz : ‖z‖ < 1) :
    IsProbabilityDensity (fun θ : ℝ => poissonKernelDisk z (Circle.exp θ)) := by
  refine ⟨continuous_poissonKernelDisk_exp hz, fun θ => poissonKernelDisk_nonneg hz,
    fun θ => ?_, ?_⟩
  · show poissonKernelDisk z ((Circle.exp (θ + 2 * Real.pi) : Circle) : ℂ)
      = poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ)
    rw [coe_circle_exp_add_two_pi]
  · rw [integral_poissonKernel hz]
    field_simp

/-- The boundary values of a circle homeomorphism form a boundary family:
`θ ↦ φ(e^{iθ})` is continuous, unimodular, and injective on `(0, 2π)`. -/
theorem isBoundaryFamily_comp_circleExp {φ : Circle → Circle} (hφ : Function.Injective φ)
    (hφc : Continuous φ) : IsBoundaryFamily (fun θ : ℝ => ((φ (Circle.exp θ) : Circle) : ℂ)) := by
  refine ⟨continuous_subtype_val.comp (hφc.comp Circle.exp.continuous),
    fun θ => Circle.norm_coe _, fun θ θ' hθ hθ' heq => ?_⟩
  refine circle_exp_inj_on hθ hθ' ?_
  exact congrArg Subtype.val (hφ (Subtype.val_injective heq))

/-- (3.1) says exactly that `w` is a zero of the average of `g_w` over the
boundary family `θ ↦ φ(e^{iθ})` weighted by the Poisson density of `z`. -/
theorem baryEq_iff_avgDiskAut (φ : Circle → Circle) (z w : ℂ) :
    baryEq φ z w ↔ avgDiskAut (fun θ : ℝ => ((φ (Circle.exp θ) : Circle) : ℂ))
      (fun θ : ℝ => poissonKernelDisk z (Circle.exp θ)) w = 0 := by
  rw [baryEq, avgDiskAut]
  simp only [diskAut]

/-- Where `Continuous φ` is load-bearing.  Nothing in `Function.Bijective φ`
makes `θ ↦ φ(e^{iθ})` measurable — a bijection of `S¹` need not be — and
wherever the integrand of (3.1) is not integrable the equation degenerates to
`0 = 0` and holds at every `w` simultaneously.  So the uniqueness half of the
barycenter is exactly as strong as the measurability that continuity supplies.

This is stated conditionally rather than as an outright refutation: bijections
of `S¹` carrying a null set onto a non-measurable one exist by a Vitali-type
construction, but that construction is not formalized here, and I was not
willing to assert its conclusion without proving it. -/
theorem barycenter_existsUnique_false_of_nonintegrable (φ : Circle → Circle) (z : ℂ)
    (h : ∀ w : ℂ, ‖w‖ < 1 → ¬ IntervalIntegrable (fun θ : ℝ =>
        diskAut w ((φ (Circle.exp θ) : Circle) : ℂ)
          * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * Real.pi)) :
    ¬ ∃! w : ℂ, ‖w‖ < 1 ∧ baryEq φ z w := by
  have hbary : ∀ w : ℂ, ‖w‖ < 1 → baryEq φ z w := by
    intro w hw
    rw [baryEq_iff_avgDiskAut]
    simp only [avgDiskAut]
    rw [intervalIntegral.integral_undef (h w hw), mul_zero]
  rintro ⟨v, -, huniq⟩
  have h0 : (0:ℂ) = v := huniq 0 ⟨by norm_num, hbary 0 (by norm_num)⟩
  have h1 : ((1:ℂ) / 2) = v := huniq _ ⟨by norm_num, hbary _ (by norm_num)⟩
  rw [← h0] at h1
  norm_num at h1

/-- Existence and uniqueness of the barycenter of `φ_*(η_z)`: an instance of
`avgDiskAut_zero_existsUnique` for the boundary family `θ ↦ φ(e^{iθ})` and the
Poisson density of `z`. -/
theorem barycenter_existsUnique (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃! w : ℂ, ‖w‖ < 1 ∧ baryEq φ z w := by
  obtain ⟨w, ⟨hw, hz0⟩, huniq⟩ :=
    avgDiskAut_zero_existsUnique (isBoundaryFamily_comp_circleExp hφ.1 hφc)
      (isProbabilityDensity_poissonKernelDisk hz)
  refine ⟨w, ⟨hw, (baryEq_iff_avgDiskAut φ z w).2 hz0⟩, ?_⟩
  rintro y ⟨hy, hyb⟩
  exact huniq y ⟨hy, (baryEq_iff_avgDiskAut φ z y).1 hyb⟩

/-- Auxiliary conditional existence, matching the pattern in `Basic.lean`. -/
private theorem extension_aux (φ : Circle → Circle) (z : ℂ) :
    ∃ w : ℂ, (Function.Bijective φ ∧ Continuous φ ∧ ‖z‖ < 1) → (‖w‖ < 1 ∧ baryEq φ z w) := by
  by_cases h : Function.Bijective φ ∧ Continuous φ ∧ ‖z‖ < 1
  · obtain ⟨w, hw⟩ := (barycenter_existsUnique φ h.1 h.2.1 z h.2.2).exists
    exact ⟨w, fun _ => hw⟩
  · exact ⟨0, fun h' => absurd h' h⟩

open Classical in
/-- The Douady–Earle extension `Φ = E(φ) : D̄ → D̄` of a homeomorphism `φ` of
`S¹`: on `D` it is the conformal barycenter of `φ_*(η_z)`; on `S¹` it is `φ`
itself. -/
def extension (φ : Circle → Circle) (z : ℂ) : ℂ :=
  if _h : ‖z‖ < 1 then Classical.choose (extension_aux φ z)
  else if h2 : z ∈ Submonoid.unitSphere ℂ then (φ ⟨z, h2⟩ : ℂ)
  else 0

theorem extension_mem_disk (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) : ‖extension φ z‖ < 1 := by
  rw [extension, dite_eq_left hz]
  exact (Classical.choose_spec (extension_aux φ z) ⟨hφ, hφc, hz⟩).1

theorem extension_baryEq (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) : baryEq φ z (extension φ z) := by
  rw [extension, dite_eq_left hz]
  exact (Classical.choose_spec (extension_aux φ z) ⟨hφ, hφc, hz⟩).2

theorem extension_eq_boundary (φ : Circle → Circle) (ζ : Circle) :
    extension φ (ζ : ℂ) = (φ ζ : ℂ) := by
  have h1 : ‖(ζ : ℂ)‖ = 1 := Circle.norm_coe ζ
  have h2 : (ζ : ℂ) ∈ Submonoid.unitSphere ℂ := ζ.2
  rw [extension, dite_eq_right (by rw [h1]; norm_num), dite_eq_left h2]
  rw [show (⟨(ζ : ℂ), h2⟩ : Circle) = ζ from Subtype.ext rfl]

/-! ### Conformal naturality of the extension

Naturality can only hold on the closed disk: outside it `extension` takes the
junk value `0` (`extension_eq_zero_of_one_lt`), so the left side is `0` while
the right side is `g 0 = -λa`, which is nonzero whenever `a ≠ 0`.  The
hypothesis `‖z‖ ≤ 1` in `extension_naturality` is therefore necessary. -/

/-- Outside the closed disk `extension` is the junk value `0`. -/
theorem extension_eq_zero_of_one_lt (φ : Circle → Circle) (z : ℂ) (hz : 1 < ‖z‖) :
    extension φ z = 0 := by
  rw [extension, dite_eq_right (by linarith), dite_eq_right]
  intro hmem
  have : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hmem
  linarith

/-- Conformal naturality on `S¹`: there both sides are computed by
`extension_eq_boundary`. -/
theorem extension_naturality_boundary (φ : Circle → Circle) (g h : ℂ → ℂ)
    (ψg ψh : Circle → Circle)
    (hgb : ∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) (hhb : ∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ))
    (ζ : Circle) :
    extension (ψg ∘ φ ∘ ψh) (ζ : ℂ) = g (extension φ (h (ζ : ℂ))) := by
  rw [extension_eq_boundary (ψg ∘ φ ∘ ψh) ζ, hhb ζ, extension_eq_boundary φ (ψh ζ), hgb (φ (ψh ζ))]
  rfl

/-- Conformal naturality in `D` reduces, by the uniqueness half of
`barycenter_existsUnique`, to the transformed barycentric equation.  Combined
with `diskAut_apply_diskAut` — which says the integrand of (3.1) transforms by
a unimodular factor under `g` — what remains is the change of variables
`ζ ↦ ψh(ζ)` in the Poisson integral, i.e. `harmonicMeasureAvg_naturality`. -/
theorem extension_naturality_of_baryEq (φ : Circle → Circle) (g h : ℂ → ℂ)
    (ψg ψh : Circle → Circle) (hcomp : Function.Bijective (ψg ∘ φ ∘ ψh))
    (hcompc : Continuous (ψg ∘ φ ∘ ψh))
    (z : ℂ) (hz : ‖z‖ < 1)
    (hmem : ‖g (extension φ (h z))‖ < 1)
    (hbary : baryEq (ψg ∘ φ ∘ ψh) z (g (extension φ (h z)))) :
    extension (ψg ∘ φ ∘ ψh) z = g (extension φ (h z)) := by
  obtain ⟨w, -, huniq⟩ := barycenter_existsUnique (ψg ∘ φ ∘ ψh) hcomp hcompc z hz
  rw [huniq _ ⟨extension_mem_disk _ hcomp hcompc z hz, extension_baryEq _ hcomp hcompc z hz⟩,
    huniq _ ⟨hmem, hbary⟩]

/-- The barycentric equation (3.1) says exactly that the `η_z`-mean of
`g_w ∘ φ` vanishes. -/
theorem baryEq_iff_harmonicMeasureAvg (φ : Circle → Circle) (z w : ℂ) :
    baryEq φ z w ↔ harmonicMeasureAvg z (fun ζ => diskAut w ((φ ζ : ℂ))) = 0 := Iff.rfl

/-! ### `E(id) = id`

The one value of `E` this development can compute outright, and the reference
point for every statement about `Φ = E(φ)`.  It is a one-line consequence of the
mean value property: `baryEq id z z` says the `η_z`-mean of `g_z` vanishes, and
`g_z` is holomorphic on `D` and continuous on `D̄`, so its mean *is* its value
`g_z(z) = 0`. -/

theorem baryEq_id (z : ℂ) (hz : ‖z‖ < 1) : baryEq id z z := by
  rw [baryEq_iff_harmonicMeasureAvg]
  simp only [id_eq]
  have hplus : IsDiskAutPlus (diskAut z) := ⟨1, z, by simp, hz, by simp⟩
  have hmean : harmonicMeasureAvg z (fun ζ : Circle => diskAut z ((ζ : ℂ))) = diskAut z z :=
    harmonicMeasureAvg_eq_of_diffContOnCl (diskAut z) z hz (isDiskAutPlus_diffContOnCl _ hplus)
  rw [hmean, diskAut_self z hz]

/-- `E(id) = id` on the open disk, by uniqueness of the barycenter. -/
theorem extension_id (z : ℂ) (hz : ‖z‖ < 1) : extension id z = z := by
  have hbij : Function.Bijective (id : Circle → Circle) := Function.bijective_id
  obtain ⟨w, -, huniq⟩ := barycenter_existsUnique id hbij continuous_id z hz
  rw [huniq _ ⟨extension_mem_disk id hbij continuous_id z hz,
      extension_baryEq id hbij continuous_id z hz⟩,
    huniq _ ⟨hz, baryEq_id z hz⟩]

/-- Consequently `E(id)` has the identity as its differential throughout `D`. -/
theorem fderiv_extension_id {z : ℂ} (hz : ‖z‖ < 1) :
    fderiv ℝ (extension id) z = ContinuousLinearMap.id ℝ ℂ := by
  have heq : extension id =ᶠ[nhds z] id := by
    filter_upwards [Metric.ball_mem_nhds z (by linarith : (0:ℝ) < 1 - ‖z‖)] with w hw
    have hw1 : ‖w‖ < 1 := by
      have : ‖w - z‖ < 1 - ‖z‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ < 1 := by linarith
    exact extension_id w hw1
  rw [heq.fderiv_eq, fderiv_id]

/-- The interior case for orientation-preserving `g`: under `g` the integrand
of (3.1) picks up the unimodular constant of `diskAut_apply_diskAut`, which
comes out of the integral, and the change of variables `ζ ↦ ψh(ζ)` turns
`η_z` into `η_{h z}`. -/
theorem baryEq_naturality_plus (φ : Circle → Circle) (g h : ℂ → ℂ) (ψg ψh : Circle → Circle)
    (hg : IsDiskAutPlus g) (hh : IsDiskAut h)
    (hgb : ∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) (hhb : ∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ))
    (hφ : Function.Bijective φ) (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    baryEq (ψg ∘ φ ∘ ψh) z (g (extension φ (h z))) := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hlam' : star lam * lam = 1 := star_mul_self_of_norm_one hlam
  have hhz : ‖h z‖ < 1 := isDiskAut_mapsTo_disk h hh z hz
  have hw₀ : ‖extension φ (h z)‖ < 1 := extension_mem_disk φ hφ hφc (h z) hhz
  set w₀ := extension φ (h z) with hw₀def
  set c : ℂ := lam * ((1 - a * star w₀) / (1 - star a * w₀)) with hc
  rw [baryEq_iff_harmonicMeasureAvg]
  have hpt : (fun ζ : Circle => diskAut (g w₀) (((ψg ∘ φ ∘ ψh) ζ : ℂ)))
      = fun ζ : Circle => c * diskAut w₀ ((φ (ψh ζ) : ℂ)) := by
    funext ζ
    have h1 : (((ψg ∘ φ ∘ ψh) ζ : Circle) : ℂ) = g ((φ (ψh ζ) : ℂ)) := (hgb _).symm
    rw [h1, hform w₀, hform ((φ (ψh ζ) : ℂ)), hc]
    exact diskAut_apply_diskAut lam a w₀ _ hlam' ha hw₀ (le_of_eq (Circle.norm_coe _))
  rw [hpt, harmonicMeasureAvg_const_mul]
  have hcirc : ∀ ζ : Circle,
      (⟨h (ζ : ℂ), isDiskAut_maps_circle_to_circle h hh ζ⟩ : Circle) = ψh ζ :=
    fun ζ => Subtype.ext (hhb ζ)
  have hnat := harmonicMeasureAvg_naturality h hh z hz (fun u : Circle => diskAut w₀ ((φ u : ℂ)))
    (continuous_diskAut_comp w₀ hw₀ φ hφc)
  simp only [hcirc] at hnat
  rw [← hnat]
  have hbase : harmonicMeasureAvg (h z) (fun u : Circle => diskAut w₀ ((φ u : ℂ))) = 0 := by
    rw [← baryEq_iff_harmonicMeasureAvg]
    exact extension_baryEq φ hφ hφc (h z) hhz
  rw [hbase, mul_zero]

/-- The interior case for orientation-reversing `g`, via `diskAut_star` and
`harmonicMeasureAvg_star`. -/
theorem baryEq_naturality_minus (φ : Circle → Circle) (g h : ℂ → ℂ) (ψg ψh : Circle → Circle)
    (hg : IsDiskAutPlus (fun z => g (star z))) (hh : IsDiskAut h)
    (hgb : ∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) (hhb : ∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ))
    (hφ : Function.Bijective φ) (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    baryEq (ψg ∘ φ ∘ ψh) z (g (extension φ (h z))) := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hgu : ∀ u : ℂ, g u = lam * diskAut a (star u) := by
    intro u
    have h := hform (star u)
    simp only [star_star] at h
    exact h
  have hlam' : star lam * lam = 1 := star_mul_self_of_norm_one hlam
  have hhz : ‖h z‖ < 1 := isDiskAut_mapsTo_disk h hh z hz
  have hw₀ : ‖extension φ (h z)‖ < 1 := extension_mem_disk φ hφ hφc (h z) hhz
  set w₀ := extension φ (h z) with hw₀def
  set c : ℂ := lam * ((1 - a * star (star w₀)) / (1 - star a * star w₀)) with hc
  rw [baryEq_iff_harmonicMeasureAvg]
  have hpt : (fun ζ : Circle => diskAut (g w₀) (((ψg ∘ φ ∘ ψh) ζ : ℂ)))
      = fun ζ : Circle => c * star (diskAut w₀ ((φ (ψh ζ) : ℂ))) := by
    funext ζ
    have h1 : (((ψg ∘ φ ∘ ψh) ζ : Circle) : ℂ) = g ((φ (ψh ζ) : ℂ)) := (hgb _).symm
    rw [h1, hgu w₀, hgu ((φ (ψh ζ) : ℂ)), hc,
      diskAut_apply_diskAut lam a (star w₀) (star ((φ (ψh ζ) : ℂ))) hlam' ha
        (by rwa [norm_star]) (by rw [norm_star]; exact le_of_eq (Circle.norm_coe _)),
      diskAut_star]
  rw [hpt, harmonicMeasureAvg_const_mul]
  have hcirc : ∀ ζ : Circle,
      (⟨h (ζ : ℂ), isDiskAut_maps_circle_to_circle h hh ζ⟩ : Circle) = ψh ζ :=
    fun ζ => Subtype.ext (hhb ζ)
  have hnat := harmonicMeasureAvg_naturality h hh z hz
    (fun u : Circle => star (diskAut w₀ ((φ u : ℂ))))
    ((continuous_diskAut_comp w₀ hw₀ φ hφc).star)
  simp only [hcirc] at hnat
  rw [← hnat, harmonicMeasureAvg_star]
  have hbase : harmonicMeasureAvg (h z) (fun u : Circle => diskAut w₀ ((φ u : ℂ))) = 0 := by
    rw [← baryEq_iff_harmonicMeasureAvg]
    exact extension_baryEq φ hφ hφc (h z) hhz
  rw [hbase, star_zero, mul_zero]

/-- Conformal naturality of the extension: `E(ψg ∘ φ ∘ ψh) = g ∘ E(φ) ∘ h` for
`g, h ∈ G` with boundary values `ψg, ψh : S¹ → S¹`, on the closed disk.

The boundary case is `extension_naturality_boundary`; the interior case is
`extension_naturality_of_baryEq` fed by `baryEq_naturality_plus` /
`baryEq_naturality_minus`.  The only input not proved here is the conformal
invariance of harmonic measure, `harmonicMeasureAvg_naturality` (the Example
of Section 1), which is cited as a `sorry`. -/
theorem extension_naturality (φ : Circle → Circle) (g h : ℂ → ℂ) (ψg ψh : Circle → Circle)
    (hg : IsDiskAut g) (hh : IsDiskAut h)
    (hgb : ∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) (hhb : ∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ))
    (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hψg : Function.Bijective ψg) (hψh : Function.Bijective ψh)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    extension (ψg ∘ φ ∘ ψh) z = g (extension φ (h z)) := by
  have hψgc : Continuous ψg := by
    have hcg : Continuous fun ζ : Circle => g ((ζ : ℂ)) := continuous_isDiskAut_circle g hg
    have hval : (fun ζ : Circle => g ((ζ : ℂ))) = fun ζ : Circle => ((ψg ζ : Circle) : ℂ) :=
      funext fun ζ => hgb ζ
    rw [hval] at hcg
    exact continuous_induced_rng.2 hcg
  have hψhc : Continuous ψh := by
    have hch : Continuous fun ζ : Circle => h ((ζ : ℂ)) := continuous_isDiskAut_circle h hh
    have hval : (fun ζ : Circle => h ((ζ : ℂ))) = fun ζ : Circle => ((ψh ζ : Circle) : ℂ) :=
      funext fun ζ => hhb ζ
    rw [hval] at hch
    exact continuous_induced_rng.2 hch
  rcases lt_or_eq_of_le hz with hlt | heq
  · have hhz : ‖h z‖ < 1 := isDiskAut_mapsTo_disk h hh z hlt
    refine extension_naturality_of_baryEq φ g h ψg ψh (hψg.comp (hφ.comp hψh))
      (hψgc.comp (hφc.comp hψhc)) z hlt
      (isDiskAut_mapsTo_disk g hg _ (extension_mem_disk φ hφ hφc (h z) hhz)) ?_
    rcases hg with hp | hm
    · exact baryEq_naturality_plus φ g h ψg ψh hp hh hgb hhb hφ hφc z hlt
    · exact baryEq_naturality_minus φ g h ψg ψh hm hh hgb hhb hφ hφc z hlt
  · have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
    exact extension_naturality_boundary φ g h ψg ψh hgb hhb ⟨z, hmem⟩

/-! ### The analytic input to Theorem 1 and Proposition 2

The smoothness half of Theorem 1 and the whole of Proposition 2 come from one
place in the paper: the implicit function theorem applied to (3.1).  Stating
that once means making the boundary map a variable, and `C(S¹, S¹)` is not a
normed space — so `φ` is carried into `C(S¹, ℂ)` along `toComplexMap`, which is
one, and (3.1) is read there as `baryFnMap`.

The citation `exists_analytic_baryEq_solution` provides a local analytic
*branch of solutions* of (3.1) valued in `D`.  It says nothing about
`extension`.  That the branch is `E(φ)` is the uniqueness half of
`barycenter_existsUnique` — a theorem since it was proved, not a hypothesis —
and that step, `extension_eq_of_baryFnMap_eq_zero`, is what both
`extension_analyticOn_disk` and `extension_analytic_jointly` are built on. -/

/-- The `ℂ`-valued continuous map underlying a continuous self-map of `S¹`.
This is the embedding along which analyticity in `φ` is stated. -/
def toComplexMap (φ : C(Circle, Circle)) : C(Circle, ℂ) :=
  ⟨fun ζ => (φ ζ : ℂ), continuous_subtype_val.comp φ.continuous⟩

@[simp] theorem toComplexMap_apply (φ : C(Circle, Circle)) (ζ : Circle) :
    toComplexMap φ ζ = (φ ζ : ℂ) := rfl

theorem continuous_toComplexMap : Continuous toComplexMap := by
  have h : toComplexMap = fun φ : C(Circle, Circle) =>
      (⟨(fun x : Circle => (x : ℂ)), continuous_subtype_val⟩ : C(Circle, ℂ)).comp φ := rfl
  rw [h]
  exact ContinuousMap.continuous_postcomp _

theorem injective_toComplexMap : Function.Injective toComplexMap := by
  intro φ ψ h
  ext ζ
  exact congrArg (fun u : C(Circle, ℂ) => u ζ) h

/-- The left-hand side of (3.1) with the boundary map as a *variable*, ranging
over `C(S¹, ℂ)`.  At a genuine circle map it is `baryFn`
(`baryFnMap_toComplexMap`), so this is the parametrized form of the same
function. -/
def baryFnMap (z w : ℂ) (u : C(Circle, ℂ)) : ℂ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
    ((u (Circle.exp θ) - w) / (1 - star w * u (Circle.exp θ))) *
      (poissonKernelDisk z (Circle.exp θ) : ℂ)

theorem baryFnMap_toComplexMap (φ : C(Circle, Circle)) (z w : ℂ) :
    baryFnMap z w (toComplexMap φ) = baryFn φ z w := rfl

theorem baryEq_iff_baryFnMap (φ : C(Circle, Circle)) (z w : ℂ) :
    baryEq φ z w ↔ baryFnMap z w (toComplexMap φ) = 0 := Iff.rfl

/-! ### The analytic implicit function theorem, in Banach spaces

Mathlib has the inverse function theorem in Banach spaces
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) and, separately, the fact that the
inverse of a map with a power series expansion again has one
(`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`).  It does not put them
together.  Doing so gives the *analytic* inverse function theorem in Banach
spaces, and from it the implicit function theorem in the shape this section
needs: the unknown is a complex number, the parameter ranges over a real Banach
space — here `ℂ × C(S¹, ℂ)`, and the infinite-dimensional factor is the point.

Mathlib's own analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`) is one-dimensional, so it cannot be used
here. -/

section AnalyticIFT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The analytic inverse function theorem in Banach spaces.** -/
theorem exists_analytic_localInverse {f : E → F} {a : E} {i : E ≃L[ℝ] F}
    (hf : AnalyticAt ℝ f a) (hfd : HasStrictFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ g : F → E, AnalyticAt ℝ g (f a) ∧ g (f a) = a ∧ ∀ᶠ y in nhds (f a), f (g y) = y := by
  obtain ⟨p, hp⟩ := hf
  set R : OpenPartialHomeomorph E F := hfd.toOpenPartialHomeomorph f with hRdef
  have hcoe : ⇑R = f := hfd.toOpenPartialHomeomorph_coe
  have hmem : a ∈ R.source := hfd.mem_toOpenPartialHomeomorph_source
  have htgt : f a ∈ R.target := hfd.image_mem_toOpenPartialHomeomorph_target
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm (i : E →L[ℝ] F) := by
    have h1 : HasFDerivAt f ((continuousMultilinearCurryFin1 ℝ E F) (p 1)) a := hp.hasFDerivAt
    have h3 := h1.unique hfd.hasFDerivAt
    rw [← h3]
    simp
  have hpR : HasFPowerSeriesAt (⇑R) p a := by rw [hcoe]; exact hp
  have hsym := R.hasFPowerSeriesAt_symm hmem hpR hp1
  rw [hcoe] at hsym
  refine ⟨R.symm, hsym.analyticAt, ?_, ?_⟩
  · have h := R.left_inv hmem
    rwa [hcoe] at h
  · filter_upwards [R.open_target.mem_nhds htgt] with y hy
    have h := R.right_inv hy
    rwa [hcoe] at h

/-- **The analytic implicit function theorem**, in the form needed: the unknown
is a complex number, the parameter ranges over a real Banach space. -/
theorem exists_analytic_implicit {G : E → ℂ → ℂ} {e₀ : E} {y₀ : ℂ}
    (hG : AnalyticAt ℝ (fun q : E × ℂ => G q.1 q.2) (e₀, y₀)) (hzero : G e₀ y₀ = 0)
    (L : ℂ ≃L[ℝ] ℂ)
    (hL : HasFDerivAt (fun y : ℂ => G e₀ y) (L : ℂ →L[ℝ] ℂ) y₀) :
    ∃ h : E → ℂ, AnalyticAt ℝ h e₀ ∧ h e₀ = y₀ ∧ ∀ᶠ e in nhds e₀, G e (h e) = 0 := by
  classical
  set fstL : E × ℂ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℂ with hfstL
  set sndL : E × ℂ →L[ℝ] ℂ := ContinuousLinearMap.snd ℝ E ℂ with hsndL
  set inlL : E →L[ℝ] E × ℂ := (ContinuousLinearMap.id ℝ E).prod 0 with hinlL
  set inrL : ℂ →L[ℝ] E × ℂ := (0 : ℂ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℂ) with hinrL
  set M : E × ℂ →L[ℝ] ℂ := fderiv ℝ (fun q : E × ℂ => G q.1 q.2) (e₀, y₀) with hMdef
  have hM : HasFDerivAt (fun q : E × ℂ => G q.1 q.2) M (e₀, y₀) :=
    hG.differentiableAt.hasFDerivAt
  set A : E →L[ℝ] ℂ := M ∘L inlL with hAdef
  have hMinr : M ∘L inrL = (L : ℂ →L[ℝ] ℂ) := by
    have hslice : HasFDerivAt (fun y : ℂ => ((e₀, y) : E × ℂ)) inrL y₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) e₀ y₀).prodMk (hasFDerivAt_id (𝕜 := ℝ) y₀)
    have hcomp := hM.comp y₀ hslice
    simp only [Function.comp_def] at hcomp
    exact hcomp.unique hL
  have hsplit : ∀ q : E × ℂ, M q = A q.1 + (L : ℂ →L[ℝ] ℂ) q.2 := by
    intro q
    have hq : q = inlL q.1 + inrL q.2 := by
      simp [hinlL, hinrL]
    conv_lhs => rw [hq]
    rw [map_add]
    congr 1
    have hap := congrArg (fun T : ℂ →L[ℝ] ℂ => T q.2) hMinr
    simpa using hap
  set f₁ : (E × ℂ) →L[ℝ] (E × ℂ) := fstL.prod M with hf₁
  set f₂ : (E × ℂ) →L[ℝ] (E × ℂ) :=
    fstL.prod ((L.symm : ℂ →L[ℝ] ℂ) ∘L (sndL - A ∘L fstL)) with hf₂
  have happ₁ : ∀ q : E × ℂ, f₁ q = (q.1, M q) := fun q => rfl
  have happ₂ : ∀ q : E × ℂ, f₂ q = (q.1, (L.symm : ℂ →L[ℝ] ℂ) (q.2 - A q.1)) := fun q => rfl
  have hleft : Function.LeftInverse f₂ f₁ := by
    intro q
    rw [happ₁, happ₂]
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    show (L.symm : ℂ →L[ℝ] ℂ) (M q - A q.1) = q.2
    rw [hsplit q]
    simp
  have hright : Function.RightInverse f₂ f₁ := by
    intro q
    rw [happ₂, happ₁]
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    show M (q.1, (L.symm : ℂ →L[ℝ] ℂ) (q.2 - A q.1)) = q.2
    rw [hsplit]
    simp
  set i : (E × ℂ) ≃L[ℝ] (E × ℂ) := ContinuousLinearEquiv.equivOfInverse f₁ f₂ hleft hright with hi
  have hicoe : (i : (E × ℂ) →L[ℝ] (E × ℂ)) = f₁ := rfl
  set Ψ : E × ℂ → E × ℂ := fun q => (q.1, G q.1 q.2) with hΨdef
  have hΨa : AnalyticAt ℝ Ψ (e₀, y₀) := (fstL.analyticAt _).prod hG
  have hΨd : HasFDerivAt Ψ f₁ (e₀, y₀) := hasFDerivAt_fst.prodMk hM
  have hΨs : HasStrictFDerivAt Ψ (i : (E × ℂ) →L[ℝ] (E × ℂ)) (e₀, y₀) := by
    have h := hΨa.hasStrictFDerivAt
    rw [hΨd.fderiv] at h
    rw [hicoe]
    exact h
  obtain ⟨g, hga, hgfix, hgev⟩ := exists_analytic_localInverse hΨa hΨs
  have hΨ0 : Ψ (e₀, y₀) = (e₀, (0:ℂ)) := by rw [hΨdef]; simp [hzero]
  rw [hΨ0] at hga hgfix hgev
  refine ⟨fun e => (g (e, (0:ℂ))).2, ?_, ?_, ?_⟩
  · have hsl : AnalyticAt ℝ (fun e : E => (e, (0:ℂ))) e₀ := analyticAt_id.prod analyticAt_const
    have hc : AnalyticAt ℝ (fun e : E => g (e, (0:ℂ))) e₀ := by
      have h := AnalyticAt.comp (g := g) (f := fun e : E => ((e, (0:ℂ)) : E × ℂ)) hga hsl
      simpa [Function.comp_def] using h
    have h2 := AnalyticAt.comp (g := (sndL : E × ℂ → ℂ))
      (f := fun e : E => g (e, (0:ℂ))) (sndL.analyticAt _) hc
    simpa [Function.comp_def, hsndL] using h2
  · show (g (e₀, (0:ℂ))).2 = y₀
    rw [hgfix]
  · have hmap : Filter.Tendsto (fun e : E => (e, (0:ℂ))) (nhds e₀) (nhds (e₀, (0:ℂ))) :=
      (continuous_id.prodMk continuous_const).tendsto e₀
    filter_upwards [hmap.eventually hgev] with e he
    have h1 : (g (e, (0:ℂ))).1 = e := congrArg Prod.fst he
    have h2 : G (g (e, (0:ℂ))).1 (g (e, (0:ℂ))).2 = 0 := congrArg Prod.snd he
    rwa [h1] at h2
end AnalyticIFT

/-! ### (3.1) as a Banach-algebra expression, and its analyticity

`C(S¹, ℂ)` is a commutative unital Banach algebra, and that is the whole reason
this works: the integrand of (3.1),

    Π(z, w, u) = (1 - |z|²) · (u - w) · (1 - w̄u)⁻¹ · ((1 - z ῑ)(1 - z̄ ι))⁻¹,

is built from ring operations and *inversion* in that algebra, applied to maps
of `(z, w, u)` that are affine.  Inversion is analytic on the units
(`analyticAt_inverse`), so `Π` is real-analytic, and (3.1) is `Π` composed with
the continuous linear functional “mean over `S¹`” (`meanCLM`).  That is Lemma
2.1 of the notes, and it is where the Poisson kernel goes: `|ζ - z|²` is
`(1 - zζ̄)(1 - z̄ζ)` on the circle, so the kernel is a *product of two units of
the algebra* rather than a separate weight, and the functional `meanCLM` does
not depend on `z`.  Had the kernel been left in the functional, nothing would be
analytic in `z`.

The same expression differentiates in `w` by the product rule and
`hasFDerivAt_ringInverse`, giving formula (2.1) with the paper's two integrals
as coefficients; the Möbius identities (1.1) then turn those into
`-1/(1 - |w|²)` and `q/(1 - |w|²)` at a zero of (3.1), which is Lemma 4.1. -/

/-! ### Formula (3.3): the `w`-derivative is nondegenerate

This is the first of the two nondegeneracy facts the Jacobian needs, and unlike
the other it is elementary, so it is proved here rather than cited.

The paper's computation is that at a zero of (3.1) the two Wirtinger
coefficients of `F(z, ·)` are
`F_w = -1/(1 - |w|²)` and `F_w̄ = q/(1 - |w|²)`, where `q = ⨍ (g_w ∘ φ)² dη_z`.
So `|F_w̄| < |F_w|` is exactly `|q| < 1`, which is
`norm_harmonicMeasureAvg_sq_lt_one`.

`|q| ≤ 1` is immediate.  Strictness is where the content is, and the argument
is the one place in Section 3 where the *strict positivity* of the Poisson
kernel matters: if `|q| = 1` then the continuous nonnegative defect
`(1 - Re(q̄ (g_w ∘ φ)²)) · P(z, ·)` has vanishing integral, so it vanishes
identically on `(0, 2π)`, so `(g_w ∘ φ)² ≡ q`.  A unimodular function with
constant square takes at most two values; but `g_w ∘ φ ∘ exp` is injective on
`(0, 2π)`, which contains `π/2`, `π` and `3π/2`. -/

/-- **Formula (3.3)**, the `w`-derivative half of the Jacobian. -/
theorem norm_harmonicMeasureAvg_sq_lt_one (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖harmonicMeasureAvg z (fun ζ => (diskAut w ((φ ζ : Circle) : ℂ)) ^ 2)‖ < 1 := by
  set τ : Circle → ℂ := fun ζ => diskAut w ((φ ζ : Circle) : ℂ) with hτdef
  have hτ1 : ∀ ζ : Circle, ‖τ ζ‖ = 1 := fun ζ =>
    diskAut_norm_eq_one w _ hw (Circle.norm_coe _)
  have hτc : Continuous τ := by
    have hden : ∀ ζ : Circle, (1 : ℂ) - star w * ((φ ζ : Circle) : ℂ) ≠ 0 :=
      fun ζ => diskAut_denom_ne_zero _ _ hw (le_of_eq (Circle.norm_coe _))
    simp only [hτdef, diskAut]
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  set q : ℂ := harmonicMeasureAvg z (fun ζ => (τ ζ) ^ 2) with hqdef
  have hq1 : ‖q‖ ≤ 1 :=
    harmonicMeasureAvg_norm_le hz (hτc.fun_pow 2) (fun ζ => by rw [norm_pow, hτ1]; norm_num)
  by_contra hcon
  have hqeq : ‖q‖ = 1 := le_antisymm hq1 (not_lt.1 hcon)
  set g : ℝ → ℝ := fun θ =>
    (1 - (star q * (τ (Circle.exp θ)) ^ 2).re) * poissonKernelDisk z (Circle.exp θ) with hgdef
  have hPc : Continuous fun θ : ℝ => poissonKernelDisk z (Circle.exp θ) :=
    continuous_poissonKernelDisk_exp hz
  have hτec : Continuous fun θ : ℝ => τ (Circle.exp θ) := hτc.comp Circle.exp.continuous
  have hgc : Continuous g := by
    apply Continuous.mul _ hPc
    exact continuous_const.sub (Complex.continuous_re.comp (continuous_const.mul (hτec.pow 2)))
  have hdefnn : ∀ θ : ℝ, 0 ≤ 1 - (star q * (τ (Circle.exp θ)) ^ 2).re := by
    intro θ
    have hn : ‖star q * (τ (Circle.exp θ)) ^ 2‖ = 1 := by
      rw [norm_mul, norm_star, hqeq, norm_pow, hτ1]; norm_num
    have hle := Complex.re_le_norm (star q * (τ (Circle.exp θ)) ^ 2)
    rw [hn] at hle
    linarith
  have hgnn : ∀ θ : ℝ, 0 ≤ g θ := fun θ =>
    mul_nonneg (hdefnn θ) (poissonKernelDisk_nonneg hz)
  have hgint : ∫ θ in (0:ℝ)..(2 * Real.pi), g θ = 0 := by
    have hsplit : ∀ θ : ℝ, g θ = poissonKernelDisk z (Circle.exp θ)
        - Complex.reCLM (star q * (τ (Circle.exp θ)) ^ 2
            * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)) := by
      intro θ
      rw [hgdef]
      simp only [Complex.reCLM_apply,
        mul_comm (star q * (τ (Circle.exp θ)) ^ 2)
          ((poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ) : ℝ) : ℂ),
        Complex.re_ofReal_mul]
      ring
    have hcont2 : Continuous fun θ : ℝ => star q * (τ (Circle.exp θ)) ^ 2
        * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ) :=
      (continuous_const.mul (hτec.pow 2)).mul (Complex.continuous_ofReal.comp hPc)
    have hint2 : IntervalIntegrable (fun θ : ℝ => star q * (τ (Circle.exp θ)) ^ 2
        * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
      hcont2.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ => poissonKernelDisk z (Circle.exp θ)
        - Complex.reCLM (star q * (τ (Circle.exp θ)) ^ 2
            * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ))) (fun θ _ => hsplit θ)]
    have hint3 : IntervalIntegrable (fun θ : ℝ => Complex.reCLM (star q * (τ (Circle.exp θ)) ^ 2
        * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ))) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      exact Complex.reCLM.continuous.comp hcont2
    rw [intervalIntegral.integral_sub (hPc.intervalIntegrable _ _) hint3]
    have hcomm : (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.reCLM (star q * (τ (Circle.exp θ)) ^ 2
        * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)))
        = Complex.reCLM (∫ θ in (0:ℝ)..(2 * Real.pi), star q * (τ (Circle.exp θ)) ^ 2
          * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)) := by
      simpa [Function.comp_def] using Complex.reCLM.intervalIntegral_comp_comm hint2
    rw [hcomm, integral_poissonKernel hz]
    have hqq : ∫ θ in (0:ℝ)..(2 * Real.pi), star q * (τ (Circle.exp θ)) ^ 2
        * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)
        = star q * (((2 * Real.pi : ℝ) : ℂ) * q) := by
      rw [show (fun θ : ℝ => star q * (τ (Circle.exp θ)) ^ 2
          * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ))
          = fun θ : ℝ => star q * ((τ (Circle.exp θ)) ^ 2
            * ((poissonKernelDisk z (Circle.exp θ) : ℝ) : ℂ)) by funext θ; ring]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [hqdef, harmonicMeasureAvg, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Complex.ofReal_one, one_mul]
    rw [hqq]
    have hre : (star q * (((2 * Real.pi : ℝ) : ℂ) * q)).re = 2 * Real.pi := by
      rw [show star q * (((2 * Real.pi : ℝ) : ℂ) * q)
          = ((2 * Real.pi : ℝ) : ℂ) * (q * star q) by ring,
        Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hqeq]
      simp
    simp only [Complex.reCLM_apply, hre]
    ring
  have hzero : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), star q * (τ (Circle.exp θ)) ^ 2 = 1 := by
    intro θ hθ
    have hgz : g θ = 0 := by
      by_contra hne
      have hpos : 0 < g θ := lt_of_le_of_ne (hgnn θ) (Ne.symm hne)
      have hgt := intervalIntegral_pos_of_pos_at hgc hgnn hθ hpos
      rw [hgint] at hgt
      exact lt_irrefl 0 hgt
    have hPpos : 0 < poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ) :=
      poissonKernelDisk_pos hz (Circle.norm_coe _)
    have hre1 : (star q * (τ (Circle.exp θ)) ^ 2).re = 1 := by
      rw [hgdef] at hgz
      simp only at hgz
      rcases mul_eq_zero.1 hgz with h | h
      · linarith
      · exact absurd h (ne_of_gt hPpos)
    refine eq_one_of_norm_one_of_re_one ?_ hre1
    rw [norm_mul, norm_star, hqeq, norm_pow, hτ1]; norm_num
  have hinj : ∀ θ θ' : ℝ, θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi) → θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi) →
      τ (Circle.exp θ) = τ (Circle.exp θ') → θ = θ' := by
    intro θ θ' hθ hθ' h
    obtain ⟨-, -, hbf⟩ := isBoundaryFamily_comp_circleExp hφ.1 hφc
    exact hbf θ θ' hθ hθ' (diskAut_inj hw (le_of_eq (Circle.norm_coe _))
      (le_of_eq (Circle.norm_coe _)) h)
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hm1 : Real.pi / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hm2 : Real.pi ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hm3 : 3 * Real.pi / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hsq : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), (τ (Circle.exp θ)) ^ 2 = q := by
    intro θ hθ
    have h := hzero θ hθ
    have h2 : q * (star q * (τ (Circle.exp θ)) ^ 2) = q * 1 := by rw [h]
    rw [← mul_assoc, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hqeq] at h2
    simpa using h2
  set t₁ := τ (Circle.exp (Real.pi / 2)) with ht₁
  set t₂ := τ (Circle.exp Real.pi) with ht₂
  set t₃ := τ (Circle.exp (3 * Real.pi / 2)) with ht₃
  have he12 : t₁ ^ 2 = t₂ ^ 2 := by rw [ht₁, ht₂, hsq _ hm1, hsq _ hm2]
  have he13 : t₁ ^ 2 = t₃ ^ 2 := by rw [ht₁, ht₃, hsq _ hm1, hsq _ hm3]
  have hne12 : t₁ ≠ t₂ := fun h => by have := hinj _ _ hm1 hm2 h; linarith
  have hne13 : t₁ ≠ t₃ := fun h => by have := hinj _ _ hm1 hm3 h; linarith
  have hne23 : t₂ ≠ t₃ := fun h => by have := hinj _ _ hm2 hm3 h; linarith
  have hneg : ∀ a b : ℂ, a ^ 2 = b ^ 2 → a ≠ b → b = -a := by
    intro a b hab hne
    have hfac : (a - b) * (a + b) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h).symm (Ne.symm hne)
    · linear_combination h
  exact hne23 ((hneg t₁ t₂ he12 hne12).trans (hneg t₁ t₃ he13 hne13).symm)

/-- Integration against normalized arclength, as a real-linear functional. -/
def meanLM : C(Circle, ℂ) →ₗ[ℝ] ℂ where
  toFun f := (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ)
  map_add' f g := by
    have hf : IntervalIntegrable (fun θ : ℝ => f (Circle.exp θ)) volume 0 (2 * Real.pi) :=
      (f.continuous.comp Circle.exp.continuous).intervalIntegrable _ _
    have hg : IntervalIntegrable (fun θ : ℝ => g (Circle.exp θ)) volume 0 (2 * Real.pi) :=
      (g.continuous.comp Circle.exp.continuous).intervalIntegrable _ _
    simp only [ContinuousMap.add_apply]
    rw [intervalIntegral.integral_add hf hg]
    ring
  map_smul' r f := by
    simp only [ContinuousMap.smul_apply, RingHom.id_apply, Complex.real_smul]
    rw [intervalIntegral.integral_const_mul]
    ring

theorem meanLM_apply (f : C(Circle, ℂ)) :
    meanLM f = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ) := rfl

theorem norm_meanLM_le (f : C(Circle, ℂ)) : ‖meanLM f‖ ≤ 1 * ‖f‖ := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hle : ‖∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ)‖ ≤ ‖f‖ * |2 * Real.pi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun θ _ => f.norm_coe_le_norm _)
  have hnorm : ‖((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
    rw [sub_zero, abs_of_pos hpi]
  rw [habs] at hle
  rw [meanLM_apply, norm_mul, hnorm]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ)‖
      ≤ (2 * Real.pi)⁻¹ * (‖f‖ * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 * ‖f‖ := by field_simp

/-- Integration against normalized arclength on `S¹`, as a continuous real-linear
functional on `C(S¹, ℂ)`. -/
def meanCLM : C(Circle, ℂ) →L[ℝ] ℂ := LinearMap.mkContinuous meanLM 1 norm_meanLM_le

@[simp] theorem meanCLM_apply (f : C(Circle, ℂ)) :
    meanCLM f = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ) := rfl

/-- `ι(ζ) = ζ` as an element of `C(S¹, ℂ)`. -/
def iotaX : C(Circle, ℂ) := ⟨fun ζ => (ζ : ℂ), continuous_subtype_val⟩

/-- `ῑ(ζ) = conj ζ` as an element of `C(S¹, ℂ)`. -/
def iotaBarX : C(Circle, ℂ) :=
  ⟨fun ζ => star (ζ : ℂ), continuous_star.comp continuous_subtype_val⟩

/-- Evaluation of `ι`.  `simp only [iotaX, ContinuousMap.coe_mk]` no longer reaches this:
the body `fun ζ => (ζ : ℂ)` eta-reduces to `Subtype.val`, whose domain is `Circle` only
after unfolding, so `ContinuousMap.coe_mk` does not match. -/
theorem iotaX_apply (ζ : Circle) : iotaX ζ = (ζ : ℂ) := rfl

theorem norm_iotaX_le : ‖iotaX‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun ζ => le_of_eq (Circle.norm_coe ζ)

theorem norm_iotaBarX_le : ‖iotaBarX‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun ζ => by
    show ‖star ((ζ : Circle) : ℂ)‖ ≤ 1
    rw [norm_star]
    exact le_of_eq (Circle.norm_coe ζ)

theorem ringInverse_apply {f : C(Circle, ℂ)} (hf : IsUnit f) (ζ : Circle) :
    (Ring.inverse f) ζ = (f ζ)⁻¹ := by
  have h1 : f * Ring.inverse f = 1 := Ring.mul_inverse_cancel f hf
  have h2 : f ζ * (Ring.inverse f) ζ = 1 := by
    have h := congrArg (fun g : C(Circle, ℂ) => g ζ) h1
    simpa using h
  have hne : f ζ ≠ 0 := left_ne_zero_of_mul_eq_one h2
  field_simp
  linear_combination h2

theorem isUnit_one_sub_smul {c : ℂ} {v : C(Circle, ℂ)} (h : ‖c • v‖ < 1) :
    IsUnit ((1 : C(Circle, ℂ)) - c • v) := ⟨Units.oneSub _ h, rfl⟩

theorem norm_smul_lt_one {c : ℂ} {v : C(Circle, ℂ)} (h : ‖c‖ * ‖v‖ < 1) : ‖c • v‖ < 1 :=
  lt_of_le_of_lt (norm_smul_le c v) h

theorem one_sub_mul_star_self (z : ℂ) : (1:ℂ) - z * star z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem poisson_denom (z : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ((1:ℂ) - z * star ζ) * ((1:ℂ) - star z * ζ) = ((‖z - ζ‖ ^ 2 : ℝ) : ℂ) := by
  have hζζ : ζ * star ζ = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; norm_num
  have hkey : (z - ζ) * star (z - ζ) = ((‖z - ζ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← hkey, star_sub]
  linear_combination (z * star z - 1) * hζζ

/-- The integrand of (3.1), read inside the Banach algebra `C(S¹, ℂ)`:
`Π(z, w, u) = (1 - |z|²) · (u - w) · (1 - w̄u)⁻¹ · ((1 - z ῑ)(1 - z̄ ι))⁻¹`. -/
def bigPi (z w : ℂ) (u : C(Circle, ℂ)) : C(Circle, ℂ) :=
  ((1 : ℂ) - z * star z) •
    ((u - w • (1 : C(Circle, ℂ))) * Ring.inverse ((1 : C(Circle, ℂ)) - (star w) • u) *
      Ring.inverse (((1 : C(Circle, ℂ)) - z • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star z) • iotaX)))

theorem isUnit_Q {w : ℂ} {u : C(Circle, ℂ)} (hwu : ‖w‖ * ‖u‖ < 1) :
    IsUnit ((1 : C(Circle, ℂ)) - (star w) • u) := by
  refine isUnit_one_sub_smul (norm_smul_lt_one ?_)
  rwa [norm_star]

theorem isUnit_S {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit ((1 : C(Circle, ℂ)) - z • iotaBarX) := by
  refine isUnit_one_sub_smul (norm_smul_lt_one ?_)
  calc ‖z‖ * ‖iotaBarX‖ ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left norm_iotaBarX_le (norm_nonneg z)
    _ < 1 := by linarith

theorem isUnit_T {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit ((1 : C(Circle, ℂ)) - (star z) • iotaX) := by
  refine isUnit_one_sub_smul (norm_smul_lt_one ?_)
  rw [norm_star]
  calc ‖z‖ * ‖iotaX‖ ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left norm_iotaX_le (norm_nonneg z)
    _ < 1 := by linarith

theorem bigPi_apply {z w : ℂ} {u : C(Circle, ℂ)} (hz : ‖z‖ < 1) (hwu : ‖w‖ * ‖u‖ < 1)
    (ζ : Circle) :
    bigPi z w u ζ =
      ((u ζ - w) / (1 - star w * u ζ)) * ((poissonKernelDisk z ((ζ : Circle) : ℂ) : ℝ) : ℂ) := by
  have hST := (isUnit_S hz).mul (isUnit_T hz)
  rw [bigPi]
  simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, smul_eq_mul, ringInverse_apply (isUnit_Q hwu),
    ringInverse_apply hST]
  simp only [iotaX_apply, iotaBarX, ContinuousMap.coe_mk]
  rw [poisson_denom z (Circle.norm_coe ζ), one_sub_mul_star_self z, poissonKernelDisk]
  push_cast
  ring

theorem meanCLM_bigPi {z w : ℂ} {u : C(Circle, ℂ)} (hz : ‖z‖ < 1) (hwu : ‖w‖ * ‖u‖ < 1) :
    meanCLM (bigPi z w u) = baryFnMap z w u := by
  rw [meanCLM_apply, baryFnMap]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => bigPi_apply hz hwu (Circle.exp θ)

theorem analyticAt_star_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun y => star (f y)) x := by
  have h := AnalyticAt.comp (g := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) (f := f)
    (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).analyticAt (f x)) hf
  simpa [Function.comp_def, Complex.star_def] using h

theorem analyticAt_ringInverse_of_isUnit {f : C(Circle, ℂ)} (hf : IsUnit f) :
    AnalyticAt ℝ (Ring.inverse : C(Circle, ℂ) → C(Circle, ℂ)) f := by
  have h := analyticAt_inverse (𝕜 := ℝ) hf.unit
  rwa [hf.unit_spec] at h

set_option maxHeartbeats 2000000 in
/-- **Lemma 2.1**: `Π` is real-analytic in `(z, u, w)` wherever the three
denominators are units.  Everything is built from Banach-algebra operations, so
this is `AnalyticAt.mul`, `AnalyticAt.smul` and `analyticAt_inverse`. -/
theorem analyticAt_bigPi {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) :
    AnalyticAt ℝ (fun q : (ℂ × C(Circle, ℂ)) × ℂ => bigPi q.1.1 q.2 q.1.2) ((z₀, u₀), w₀) := by
  have hzq : AnalyticAt ℝ (fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.1.1) ((z₀, u₀), w₀) := by
    have h := AnalyticAt.comp (g := fun p : ℂ × C(Circle, ℂ) => p.1)
      (f := fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.1) (x := ((z₀, u₀), w₀))
      (analyticAt_fst (𝕜 := ℝ)) (analyticAt_fst (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  have huq : AnalyticAt ℝ (fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.1.2) ((z₀, u₀), w₀) := by
    have h := AnalyticAt.comp (g := fun p : ℂ × C(Circle, ℂ) => p.2)
      (f := fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.1) (x := ((z₀, u₀), w₀))
      (analyticAt_snd (𝕜 := ℝ)) (analyticAt_fst (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  have hwq : AnalyticAt ℝ (fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.2) ((z₀, u₀), w₀) := analyticAt_snd (𝕜 := ℝ)
  have hN : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => q.1.2 - q.2 • (1 : C(Circle, ℂ))) ((z₀, u₀), w₀) :=
    huq.sub (hwq.smul analyticAt_const)
  have hQ : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => (1 : C(Circle, ℂ)) - (star q.2) • q.1.2)
      ((z₀, u₀), w₀) :=
    analyticAt_const.sub ((analyticAt_star_comp hwq).smul huq)
  have hQinv : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ =>
        Ring.inverse ((1 : C(Circle, ℂ)) - (star q.2) • q.1.2)) ((z₀, u₀), w₀) := by
    have h := AnalyticAt.comp (g := (Ring.inverse : C(Circle, ℂ) → C(Circle, ℂ)))
      (f := fun q : (ℂ × C(Circle, ℂ)) × ℂ => (1 : C(Circle, ℂ)) - (star q.2) • q.1.2)
      (x := ((z₀, u₀), w₀)) (analyticAt_ringInverse_of_isUnit (isUnit_Q hwu)) hQ
    simpa [Function.comp_def] using h
  have hST : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => ((1 : C(Circle, ℂ)) - q.1.1 • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star q.1.1) • iotaX)) ((z₀, u₀), w₀) :=
    (analyticAt_const.sub (hzq.smul analyticAt_const)).mul
      (analyticAt_const.sub ((analyticAt_star_comp hzq).smul analyticAt_const))
  have hSTinv : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => Ring.inverse (((1 : C(Circle, ℂ)) - q.1.1 • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star q.1.1) • iotaX))) ((z₀, u₀), w₀) := by
    have h := AnalyticAt.comp (g := (Ring.inverse : C(Circle, ℂ) → C(Circle, ℂ)))
      (f := fun q : (ℂ × C(Circle, ℂ)) × ℂ => ((1 : C(Circle, ℂ)) - q.1.1 • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star q.1.1) • iotaX)) (x := ((z₀, u₀), w₀))
      (analyticAt_ringInverse_of_isUnit ((isUnit_S hz).mul (isUnit_T hz))) hST
    simpa [Function.comp_def] using h
  have hc : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => (1 : ℂ) - q.1.1 * star q.1.1) ((z₀, u₀), w₀) :=
    analyticAt_const.sub (hzq.mul (analyticAt_star_comp hzq))
  simp only [bigPi]
  exact hc.smul ((hN.mul hQinv).mul hSTinv)

theorem meanCLM_smul (c : ℂ) (f : C(Circle, ℂ)) : meanCLM (c • f) = c * meanCLM f := by
  simp only [meanCLM_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem isOpen_baryDomain :
    IsOpen {q : (ℂ × C(Circle, ℂ)) × ℂ | ‖q.1.1‖ < 1 ∧ ‖q.2‖ * ‖q.1.2‖ < 1} := by
  have h1 : IsOpen {q : (ℂ × C(Circle, ℂ)) × ℂ | ‖q.1.1‖ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {q : (ℂ × C(Circle, ℂ)) × ℂ | ‖q.2‖ * ‖q.1.2‖ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter h2

/-- **Lemma 2.1**, transported to `baryFnMap`: the left side of (3.1) is
real-analytic in `(z, u, w)` near any point where `|z| < 1` and `|w|‖u‖ < 1`. -/
theorem analyticAt_baryFnMap {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) :
    AnalyticAt ℝ (fun q : (ℂ × C(Circle, ℂ)) × ℂ => baryFnMap q.1.1 q.2 q.1.2)
      ((z₀, u₀), w₀) := by
  have hcomp : AnalyticAt ℝ
      (fun q : (ℂ × C(Circle, ℂ)) × ℂ => meanCLM (bigPi q.1.1 q.2 q.1.2)) ((z₀, u₀), w₀) := by
    have h := AnalyticAt.comp (g := (meanCLM : C(Circle, ℂ) → ℂ))
      (f := fun q : (ℂ × C(Circle, ℂ)) × ℂ => bigPi q.1.1 q.2 q.1.2) (x := ((z₀, u₀), w₀))
      (meanCLM.analyticAt _) (analyticAt_bigPi hz hwu)
    simpa [Function.comp_def] using h
  refine hcomp.congr ?_
  filter_upwards [isOpen_baryDomain.mem_nhds (show ((z₀, u₀), w₀) ∈
    {q : (ℂ × C(Circle, ℂ)) × ℂ | ‖q.1.1‖ < 1 ∧ ‖q.2‖ * ‖q.1.2‖ < 1} from ⟨hz, hwu⟩)] with q hq
  exact meanCLM_bigPi hq.1 hq.2

/-- `v ↦ v • 1`, as a real-linear map `ℂ → C(S¹, ℂ)`. -/
def cstX : ℂ →L[ℝ] C(Circle, ℂ) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (1 : C(Circle, ℂ))

/-- `v ↦ v̄ • u`, as a real-linear map `ℂ → C(S¹, ℂ)`. -/
def qmulX (u : C(Circle, ℂ)) : ℂ →L[ℝ] C(Circle, ℂ) :=
  ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).smulRight u

/-- The `w`-derivative of `Π`, as a real-linear map `ℂ → C(S¹, ℂ)`:
`v ↦ (1 - |z|²)·(-v·Q⁻¹ + v̄·(u - w)u Q⁻² ) R⁻¹`, formula (2.1). -/
def bigPiDerivW (z w : ℂ) (u : C(Circle, ℂ)) : ℂ →L[ℝ] C(Circle, ℂ) :=
  -((ContinuousLinearMap.id ℝ ℂ).smulRight
      (((1:ℂ) - z * star z) • (Ring.inverse ((1 : C(Circle, ℂ)) - (star w) • u)
        * Ring.inverse (((1 : C(Circle, ℂ)) - z • iotaBarX)
            * ((1 : C(Circle, ℂ)) - (star z) • iotaX)))))
    + (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).smulRight
        (((1:ℂ) - z * star z) • ((u - w • (1 : C(Circle, ℂ))) * u
          * Ring.inverse ((1 : C(Circle, ℂ)) - (star w) • u)
          * Ring.inverse ((1 : C(Circle, ℂ)) - (star w) • u)
          * Ring.inverse (((1 : C(Circle, ℂ)) - z • iotaBarX)
              * ((1 : C(Circle, ℂ)) - (star z) • iotaX)))))

set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_bigPi_w {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) :
    HasFDerivAt (fun w : ℂ => bigPi z₀ w u₀) (bigPiDerivW z₀ w₀ u₀) w₀ := by
  rw [bigPiDerivW]
  have hQu : IsUnit ((1 : C(Circle, ℂ)) - (star w₀) • u₀) := isUnit_Q hwu
  have hN : HasFDerivAt (fun w : ℂ => u₀ - w • (1 : C(Circle, ℂ))) (-cstX) w₀ := by
    have h := (hasFDerivAt_const u₀ w₀).sub (cstX.hasFDerivAt (x := w₀))
    have hfun : ((fun _ : ℂ => u₀) - ⇑cstX)
        = fun w : ℂ => u₀ - w • (1 : C(Circle, ℂ)) := by
      funext w; simp [cstX]
    rw [hfun, zero_sub] at h
    exact h
  have hQ : HasFDerivAt (fun w : ℂ => (1 : C(Circle, ℂ)) - (star w) • u₀) (-(qmulX u₀)) w₀ := by
    have h := (hasFDerivAt_const (1 : C(Circle, ℂ)) w₀).sub ((qmulX u₀).hasFDerivAt (x := w₀))
    have hfun : ((fun _ : ℂ => (1 : C(Circle, ℂ))) - ⇑(qmulX u₀))
        = fun w : ℂ => (1 : C(Circle, ℂ)) - (star w) • u₀ := by
      funext w; simp [qmulX, Complex.star_def]
    rw [hfun, zero_sub] at h
    exact h
  have hQiD : HasFDerivAt (fun w : ℂ => Ring.inverse ((1 : C(Circle, ℂ)) - (star w) • u₀))
      ((-(ContinuousLinearMap.mulLeftRight ℝ C(Circle, ℂ)
          (Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀))
          (Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀)))) ∘L (-(qmulX u₀))) w₀ := by
    have hpt := hasFDerivAt_ringInverse (𝕜 := ℝ) hQu.unit
    rw [hQu.unit_spec] at hpt
    have hinv : (((hQu.unit)⁻¹ : C(Circle, ℂ)ˣ) : C(Circle, ℂ))
        = Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀) := by
      rw [← Ring.inverse_unit hQu.unit, hQu.unit_spec]
    rw [hinv] at hpt
    exact hpt.comp w₀ hQ
  have hprod := hN.mul hQiD
  have hprod2 := hprod.mul (hasFDerivAt_const
    (Ring.inverse (((1 : C(Circle, ℂ)) - z₀ • iotaBarX)
      * ((1 : C(Circle, ℂ)) - (star z₀) • iotaX))) w₀)
  have hfin := hprod2.const_smul ((1:ℂ) - z₀ * star z₀)
  simp only [bigPi]
  refine hfin.congr_fderiv ?_
  ext v ζ
  simp only [add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.neg_apply, ContinuousMap.zero_apply,
    ContinuousMap.one_apply, smul_eq_mul, cstX, qmulX, Complex.conjCLE_apply,
    Complex.star_def, ContinuousLinearEquiv.coe_coe]
  ring

theorem smul_Rinv_apply {z : ℂ} (hz : ‖z‖ < 1) (g : C(Circle, ℂ)) (ζ : Circle) :
    ((((1:ℂ) - z * star z) • (g * Ring.inverse (((1 : C(Circle, ℂ)) - z • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star z) • iotaX)))) : C(Circle, ℂ)) ζ
      = g ζ * ((poissonKernelDisk z ((ζ : Circle) : ℂ) : ℝ) : ℂ) := by
  have hST := (isUnit_S hz).mul (isUnit_T hz)
  simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul,
    ringInverse_apply hST]
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, smul_eq_mul, iotaX_apply, iotaBarX, ContinuousMap.coe_mk]
  rw [poisson_denom z (Circle.norm_coe ζ), one_sub_mul_star_self z, poissonKernelDisk]
  push_cast
  ring

theorem meanCLM_eq_harmonicMeasureAvg {z : ℂ} {f : C(Circle, ℂ)} {F : Circle → ℂ}
    (hF : ∀ ζ : Circle, f ζ = F ζ * ((poissonKernelDisk z ((ζ : Circle) : ℂ) : ℝ) : ℂ)) :
    meanCLM f = harmonicMeasureAvg z F := by
  rw [meanCLM_apply, harmonicMeasureAvg]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => hF (Circle.exp θ)

set_option maxHeartbeats 2000000 in
/-- **Formula (2.1)**: the `w`-derivative of (3.1) is `v ↦ a·v + b·v̄`, with `a`
and `b` the two integrals of the paper. -/
theorem hasFDerivAt_baryFnMap_w {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) :
    HasFDerivAt (fun w : ℂ => baryFnMap z₀ w u₀)
      ((-(harmonicMeasureAvg z₀ (fun ζ => ((1:ℂ) - star w₀ * u₀ ζ)⁻¹)))
          • (ContinuousLinearMap.id ℝ ℂ)
        + (harmonicMeasureAvg z₀ (fun ζ => (u₀ ζ - w₀) * u₀ ζ
            * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹ * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹))
          • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) w₀ := by
  have hcomp : HasFDerivAt (fun w : ℂ => meanCLM (bigPi z₀ w u₀))
      (meanCLM ∘L bigPiDerivW z₀ w₀ u₀) w₀ :=
    meanCLM.hasFDerivAt.comp w₀ (hasFDerivAt_bigPi_w hz hwu)
  have htr : HasFDerivAt (fun w : ℂ => baryFnMap z₀ w u₀)
      (meanCLM ∘L bigPiDerivW z₀ w₀ u₀) w₀ := by
    refine hcomp.congr_of_eventuallyEq ?_
    have hopen : IsOpen {w : ℂ | ‖w‖ * ‖u₀‖ < 1} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hwu] with w hw
    exact (meanCLM_bigPi hz hw).symm
  have hA : meanCLM (((1:ℂ) - z₀ * star z₀) •
      (Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀)
        * Ring.inverse (((1 : C(Circle, ℂ)) - z₀ • iotaBarX)
            * ((1 : C(Circle, ℂ)) - (star z₀) • iotaX))))
      = harmonicMeasureAvg z₀ (fun ζ => ((1:ℂ) - star w₀ * u₀ ζ)⁻¹) := by
    refine meanCLM_eq_harmonicMeasureAvg (fun ζ => ?_)
    rw [smul_Rinv_apply hz]
    congr 1
    exact ringInverse_apply (isUnit_Q hwu) ζ
  have hB : meanCLM (((1:ℂ) - z₀ * star z₀) •
      ((u₀ - w₀ • (1 : C(Circle, ℂ))) * u₀
        * Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀)
        * Ring.inverse ((1 : C(Circle, ℂ)) - (star w₀) • u₀)
        * Ring.inverse (((1 : C(Circle, ℂ)) - z₀ • iotaBarX)
            * ((1 : C(Circle, ℂ)) - (star z₀) • iotaX))))
      = harmonicMeasureAvg z₀ (fun ζ => (u₀ ζ - w₀) * u₀ ζ
          * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹ * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹) := by
    refine meanCLM_eq_harmonicMeasureAvg (fun ζ => ?_)
    rw [smul_Rinv_apply hz]
    congr 1
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, ringInverse_apply (isUnit_Q hwu)]
    ring
  rw [meanCLM_smul] at hA hB
  refine htr.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, bigPiDerivW,
    add_apply, neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_id', id_eq,
    smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, map_add, map_neg, meanCLM_smul]
  rw [hA, hB]
  simp only [Complex.star_def]
  ring

/-! ### The Möbius identities (1.1), and the two coefficients -/

theorem mobius_id1 {w x : ℂ} (hd : (1:ℂ) - star w * x ≠ 0) :
    ((1:ℂ) - star w * x) * ((1:ℂ) + star w * diskAut w x) = (1:ℂ) - w * star w := by
  rw [diskAut]
  field_simp
  ring

theorem mobius_id2 {w x : ℂ} (hd : (1:ℂ) - star w * x ≠ 0) :
    ((1:ℂ) - w * star w) * ((x - w) * x)
      = (diskAut w x * diskAut w x + w * diskAut w x) * (((1:ℂ) - star w * x)
          * ((1:ℂ) - star w * x)) := by
  rw [diskAut]
  field_simp
  ring

theorem coeff_inv {w x : ℂ} (hκ : (1:ℂ) - w * star w ≠ 0) (hd : (1:ℂ) - star w * x ≠ 0) :
    ((1:ℂ) - star w * x)⁻¹
      = ((1:ℂ) - w * star w)⁻¹ * ((1:ℂ) + star w * diskAut w x) := by
  have h := mobius_id1 hd
  have h2 : ((1:ℂ) + star w * diskAut w x)
      = ((1:ℂ) - w * star w) * ((1:ℂ) - star w * x)⁻¹ := by
    field_simp
    linear_combination h
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

theorem coeff_sq {w x : ℂ} (hκ : (1:ℂ) - w * star w ≠ 0) (hd : (1:ℂ) - star w * x ≠ 0) :
    (x - w) * x * ((1:ℂ) - star w * x)⁻¹ * ((1:ℂ) - star w * x)⁻¹
      = ((1:ℂ) - w * star w)⁻¹ * (diskAut w x * diskAut w x + w * diskAut w x) := by
  have h := mobius_id2 hd
  have h2 : (diskAut w x * diskAut w x + w * diskAut w x)
      = ((1:ℂ) - w * star w) * ((x - w) * x)
        * (((1:ℂ) - star w * x)⁻¹ * ((1:ℂ) - star w * x)⁻¹) := by
    field_simp
    linear_combination -h
  rw [h2, show ((1:ℂ) - w * star w)⁻¹ * (((1:ℂ) - w * star w) * ((x - w) * x)
      * (((1:ℂ) - star w * x)⁻¹ * ((1:ℂ) - star w * x)⁻¹))
      = (((1:ℂ) - w * star w)⁻¹ * ((1:ℂ) - w * star w)) * ((x - w) * x
        * (((1:ℂ) - star w * x)⁻¹ * ((1:ℂ) - star w * x)⁻¹)) from by ring,
    inv_mul_cancel₀ hκ, one_mul]
  ring

theorem one_sub_star_mul_ne_zero {w : ℂ} {u : C(Circle, ℂ)} (hwu : ‖w‖ * ‖u‖ < 1) (ζ : Circle) :
    (1:ℂ) - star w * u ζ ≠ 0 := by
  intro h
  have h1 : star w * u ζ = 1 := by linear_combination -h
  have h2 : ‖star w * u ζ‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_star] at h2
  have h3 : ‖w‖ * ‖u ζ‖ ≤ ‖w‖ * ‖u‖ :=
    mul_le_mul_of_nonneg_left (u.norm_coe_le_norm ζ) (norm_nonneg w)
  linarith

theorem one_sub_mul_star_ne_zero' {w : ℂ} (hw : ‖w‖ < 1) : (1:ℂ) - w * star w ≠ 0 := by
  rw [one_sub_mul_star_self]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  nlinarith [norm_nonneg w]

theorem continuous_tau {w : ℂ} {u : C(Circle, ℂ)} (hwu : ‖w‖ * ‖u‖ < 1) :
    Continuous (fun ζ : Circle => diskAut w (u ζ)) := by
  simp only [diskAut]
  exact Continuous.div (by fun_prop) (by fun_prop) (one_sub_star_mul_ne_zero hwu)

/-- **Lemma 4.1**, first coefficient: at a zero of (3.1), `a = -1/(1 - |w|²)`. -/
theorem coeff_a_eq {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1) (hw : ‖w₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) (hbary : baryFnMap z₀ w₀ u₀ = 0) :
    harmonicMeasureAvg z₀ (fun ζ => ((1:ℂ) - star w₀ * u₀ ζ)⁻¹)
      = ((1:ℂ) - w₀ * star w₀)⁻¹ := by
  have hκ := one_sub_mul_star_ne_zero' hw
  have hτc := continuous_tau hwu
  have hbary' : harmonicMeasureAvg z₀ (fun ζ => diskAut w₀ (u₀ ζ)) = 0 := hbary
  have hfun : (fun ζ : Circle => ((1:ℂ) - star w₀ * u₀ ζ)⁻¹)
      = fun ζ : Circle => ((1:ℂ) - w₀ * star w₀)⁻¹
          * ((1:ℂ) + star w₀ * diskAut w₀ (u₀ ζ)) :=
    funext fun ζ => coeff_inv hκ (one_sub_star_mul_ne_zero hwu ζ)
  rw [hfun, harmonicMeasureAvg_const_mul]
  have hsplit : harmonicMeasureAvg z₀ (fun ζ => (1:ℂ) + star w₀ * diskAut w₀ (u₀ ζ)) = 1 := by
    rw [harmonicMeasureAvg_add (F := fun _ : Circle => (1:ℂ))
        (G := fun ζ : Circle => star w₀ * diskAut w₀ (u₀ ζ)) hz continuous_const
        (continuous_const.mul hτc),
      harmonicMeasureAvg_const_one z₀ hz, harmonicMeasureAvg_const_mul, hbary', mul_zero,
      add_zero]
  rw [hsplit, mul_one]

/-- **Lemma 4.1**, second coefficient: at a zero of (3.1), `b = q/(1 - |w|²)`. -/
theorem coeff_b_eq {z₀ w₀ : ℂ} {u₀ : C(Circle, ℂ)} (hz : ‖z₀‖ < 1) (hw : ‖w₀‖ < 1)
    (hwu : ‖w₀‖ * ‖u₀‖ < 1) (hbary : baryFnMap z₀ w₀ u₀ = 0) :
    harmonicMeasureAvg z₀ (fun ζ => (u₀ ζ - w₀) * u₀ ζ
        * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹ * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹)
      = ((1:ℂ) - w₀ * star w₀)⁻¹
        * harmonicMeasureAvg z₀ (fun ζ => (diskAut w₀ (u₀ ζ)) ^ 2) := by
  have hκ := one_sub_mul_star_ne_zero' hw
  have hτc := continuous_tau hwu
  have hbary' : harmonicMeasureAvg z₀ (fun ζ => diskAut w₀ (u₀ ζ)) = 0 := hbary
  have hfun : (fun ζ : Circle => (u₀ ζ - w₀) * u₀ ζ
      * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹ * ((1:ℂ) - star w₀ * u₀ ζ)⁻¹)
      = fun ζ : Circle => ((1:ℂ) - w₀ * star w₀)⁻¹
          * ((diskAut w₀ (u₀ ζ)) ^ 2 + w₀ * diskAut w₀ (u₀ ζ)) := by
    refine funext fun ζ => ?_
    rw [coeff_sq hκ (one_sub_star_mul_ne_zero hwu ζ), sq]
  rw [hfun, harmonicMeasureAvg_const_mul]
  congr 1
  rw [harmonicMeasureAvg_add (F := fun ζ : Circle => (diskAut w₀ (u₀ ζ)) ^ 2)
      (G := fun ζ : Circle => w₀ * diskAut w₀ (u₀ ζ)) hz (by fun_prop)
      (continuous_const.mul hτc),
    harmonicMeasureAvg_const_mul, hbary', mul_zero, add_zero]

/-- The linearization `v ↦ r⁻¹(-v + q v̄)` of (3.1) in the `w` variable is an
isomorphism as soon as `|q| < 1`.  This is Lemma 4.1's conclusion `|a| > |b|`,
with the inverse written out. -/
def wDerivEquiv {r : ℝ} (hr : r ≠ 0) {q : ℂ} (hq : ‖q‖ < 1) : ℂ ≃L[ℝ] ℂ := by
  refine ContinuousLinearEquiv.equivOfInverse
    ((-((r:ℂ)⁻¹)) • (ContinuousLinearMap.id ℝ ℂ)
      + ((r:ℂ)⁻¹ * q) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ))
    ((-((r:ℂ) * ((1 - ‖q‖ ^ 2 : ℝ) : ℂ)⁻¹)) • (ContinuousLinearMap.id ℝ ℂ)
      + ((-((r:ℂ) * ((1 - ‖q‖ ^ 2 : ℝ) : ℂ)⁻¹)) * q)
        • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) ?_ ?_ <;>
  · intro y
    have hrc : ((r : ℝ) : ℂ) ≠ 0 := by simpa using hr
    have hκ : (((1 - ‖q‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      nlinarith [norm_nonneg q]
    have hqq : q * (starRingEnd ℂ) q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul, map_add, map_mul, map_neg, map_inv₀,
      Complex.conj_conj, Complex.conj_ofReal]
    push_cast at hκ hqq ⊢
    field_simp
    linear_combination (-y) * hqq

set_option maxHeartbeats 2000000 in
/-- **The analytic input to Theorem 1 and Proposition 2, proved.**  (3.1) has a
local real-analytic branch of solutions, valued in `D`, jointly in the interior
point `z` and the boundary map `u`, the latter ranging over the Banach space
`C(S¹, ℂ)`.

Three things go into it.  *Analyticity* of (3.1) in `(z, w, u)` is
`analyticAt_baryFnMap`: everything is Banach-algebra arithmetic in `C(S¹, ℂ)`.
*A zero at the base point* is `barycenter_existsUnique`, already proved, so the
variational argument of the notes is not needed.  *Nondegeneracy of the
`w`-derivative there* is formula (2.1) (`hasFDerivAt_baryFnMap_w`) combined with
Lemma 4.1 (`coeff_a_eq`, `coeff_b_eq`, `norm_harmonicMeasureAvg_sq_lt_one`),
which identify it as `v ↦ (1 - |w|²)⁻¹(-v + q v̄)` with `|q| < 1`, invertible by
`wDerivEquiv`.  The implicit function theorem is then
`exists_analytic_implicit`.

Note what is *not* asserted: nothing about `extension`.  The branch is
characterized by solving (3.1) inside `D`, and it is `barycenter_existsUnique`
that identifies it with `E(φ)`, in `extension_eq_of_baryFnMap_eq_zero` just
below. -/
theorem exists_analytic_baryEq_solution (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1)
    (φ₀ : C(Circle, Circle)) (hφ₀ : Function.Bijective φ₀) :
    ∃ (W : Set (ℂ × C(Circle, ℂ))) (F : ℂ × C(Circle, ℂ) → ℂ),
      IsOpen W ∧ (z₀, toComplexMap φ₀) ∈ W ∧ AnalyticOn ℝ F W ∧
      ∀ p ∈ W, ‖p.1‖ < 1 → ‖F p‖ < 1 ∧ baryFnMap p.1 (F p) p.2 = 0 := by
  classical
  set u₀ : C(Circle, ℂ) := toComplexMap φ₀ with hu₀def
  have hu₀norm : ‖u₀‖ = 1 := by
    refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).2 fun ζ =>
      le_of_eq (Circle.norm_coe _)) ?_
    have h := u₀.norm_coe_le_norm 1
    rwa [show ‖u₀ 1‖ = 1 from Circle.norm_coe _] at h
  set w₀ : ℂ := extension φ₀ z₀ with hw₀def
  have hw₀lt : ‖w₀‖ < 1 := extension_mem_disk φ₀ hφ₀ φ₀.continuous z₀ hz₀
  have hbary : baryFnMap z₀ w₀ u₀ = 0 :=
    (baryEq_iff_baryFnMap φ₀ z₀ w₀).1 (extension_baryEq φ₀ hφ₀ φ₀.continuous z₀ hz₀)
  have hwu : ‖w₀‖ * ‖u₀‖ < 1 := by rw [hu₀norm, mul_one]; exact hw₀lt
  -- the coefficient `q` of formula (3.3), and Lemma 4.1
  set q : ℂ := harmonicMeasureAvg z₀ (fun ζ => (diskAut w₀ (u₀ ζ)) ^ 2) with hqdef
  have hq : ‖q‖ < 1 := norm_harmonicMeasureAvg_sq_lt_one φ₀ hφ₀ φ₀.continuous hz₀ hw₀lt
  set r : ℝ := 1 - ‖w₀‖ ^ 2 with hrdef
  have hr : r ≠ 0 := by
    rw [hrdef]
    nlinarith [norm_nonneg w₀]
  have hrc : ((1:ℂ) - w₀ * star w₀) = ((r : ℝ) : ℂ) := one_sub_mul_star_self w₀
  -- formula (2.1) with the coefficients of Lemma 4.1 substituted
  have hderiv : HasFDerivAt (fun w : ℂ => baryFnMap z₀ w u₀)
      ((wDerivEquiv hr hq : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w₀ := by
    have h := hasFDerivAt_baryFnMap_w hz₀ hwu
    rw [coeff_a_eq hz₀ hw₀lt hwu hbary, coeff_b_eq hz₀ hw₀lt hwu hbary, ← hqdef, hrc] at h
    exact h
  -- the analytic implicit function theorem
  obtain ⟨h, hha, hhfix, hhev⟩ := exists_analytic_implicit
    (G := fun e : ℂ × C(Circle, ℂ) => fun w : ℂ => baryFnMap e.1 w e.2)
    (e₀ := (z₀, u₀)) (y₀ := w₀) (analyticAt_baryFnMap hz₀ hwu) hbary (wDerivEquiv hr hq) hderiv
  -- the neighbourhood on which `h` is analytic, small and solves (3.1)
  have hnorm : ∀ᶠ e in nhds ((z₀, u₀) : ℂ × C(Circle, ℂ)), ‖h e‖ < 1 := by
    have hc : Filter.Tendsto (fun e : ℂ × C(Circle, ℂ) => ‖h e‖) (nhds (z₀, u₀))
        (nhds ‖h (z₀, u₀)‖) := (continuous_norm.continuousAt.comp hha.continuousAt)
    refine hc (isOpen_Iio.mem_nhds ?_)
    rw [hhfix]
    exact hw₀lt
  have hall : ∀ᶠ e in nhds ((z₀, u₀) : ℂ × C(Circle, ℂ)),
      AnalyticAt ℝ h e ∧ ‖h e‖ < 1 ∧ baryFnMap e.1 (h e) e.2 = 0 :=
    (hha.eventually_analyticAt).and (hnorm.and hhev)
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.1 hall
  exact ⟨W, h, hWopen, hWmem, fun p hp => ((hWsub hp).1).analyticWithinAt,
    fun p hp _ => ⟨(hWsub hp).2.1, (hWsub hp).2.2⟩⟩

/-- Any solution of (3.1) lying in `D` *is* the barycenter, so an analytic
branch of solutions is `E(φ)` wherever `φ` is a homeomorphism.  This is the
uniqueness half of `barycenter_existsUnique` and nothing else. -/
theorem extension_eq_of_baryFnMap_eq_zero (φ : C(Circle, Circle)) (hφ : Function.Bijective φ)
    {z : ℂ} (hz : ‖z‖ < 1) {w : ℂ} (hw : ‖w‖ < 1)
    (heq : baryFnMap z w (toComplexMap φ) = 0) : extension φ z = w := by
  obtain ⟨v, -, huniq⟩ := barycenter_existsUnique φ hφ φ.continuous z hz
  rw [huniq _ ⟨extension_mem_disk φ hφ φ.continuous z hz,
      extension_baryEq φ hφ φ.continuous z hz⟩,
    huniq _ ⟨hw, (baryEq_iff_baryFnMap φ z w).2 heq⟩]

/-- Freezing the boundary map is an affine, hence analytic, slice. -/
theorem analyticAt_slice (c : C(Circle, ℂ)) (z₀ : ℂ) :
    AnalyticAt ℝ (fun z : ℂ => (z, c)) z₀ :=
  analyticAt_id.prod analyticAt_const

/-! ### Lemma 2, and a limit taken in the wrong space

The statement of Lemma 2 was `ContinuousAt (extension φ) ζ` — continuity as a
function on `ℂ`.  That is **false**, and for a reason the file already records
elsewhere: outside the closed disk `extension` is the junk value `0`
(`extension_eq_zero_of_one_lt`), while on `S¹` it is `φ`, of modulus `1`.
Approaching `ζ` radially from outside therefore gives limit `0 ≠ φ(ζ)`.
`extension_continuousAt_boundary_false` proves it with `φ = id` and
`z_n = 1 + 1/(n+1)`.

`Φ` is a map of `D̄`, so the limit belongs in `D̄`: the paper's Lemma 2 is
`ContinuousWithinAt (extension φ) (closedBall 0 1) ζ`.  That is also exactly
what the one consumer, `continuousOn_extension`, needs.

`Function.Bijective φ` is restored at the same time: at a `φ` that is not a
homeomorphism `E(φ)` is `Classical.choose` over a failing hypothesis, so no
continuity statement about it can be justified. -/

/-- Lemma 2 is false as a statement about continuity in `ℂ`: outside `D̄` the
extension is the junk value `0`. -/
theorem extension_continuousAt_boundary_false :
    ¬ ∀ (φ : Circle → Circle), Continuous φ → ∀ ζ : Circle,
        ContinuousAt (extension φ) (ζ : ℂ) := by
  intro hbad
  have hc := hbad id continuous_id 1
  set u : ℕ → ℂ := fun n => (((1 : ℝ) + 1 / (n + 1) : ℝ) : ℂ) with hu
  have hru : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) + 1 / (n + 1) : ℝ)) Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop)).add h0
  have hu1 : Filter.Tendsto u Filter.atTop (nhds (((1 : Circle) : ℂ))) := by
    rw [Circle.coe_one]
    exact (Complex.continuous_ofReal.tendsto 1).comp hru
  have hval : ∀ n : ℕ, extension id (u n) = 0 := by
    intro n
    refine extension_eq_zero_of_one_lt id (u n) ?_
    have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
    have hn : ‖u n‖ = (1 : ℝ) + 1 / (n + 1) := by
      rw [hu]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    rw [hn]; linarith
  have h1 : Filter.Tendsto (fun n : ℕ => extension id (u n)) Filter.atTop
      (nhds (extension id ((1 : Circle) : ℂ))) := hc.tendsto.comp hu1
  have h2 : Filter.Tendsto (fun n : ℕ => extension id (u n)) Filter.atTop (nhds 0) := by
    simp [hval]
  have hlim := tendsto_nhds_unique h1 h2
  rw [extension_eq_boundary id (1 : Circle)] at hlim
  simp at hlim

/-! ### Lemma 2, proved

The proof is the paper's concentration argument, restructured so that neither
subsequences nor set integrals appear.

Two changes make that possible.

*The reference value is uniform in `w`.*  The paper fixes a subsequential limit
`w*` of `Φ(z_k)` and splits on whether `w* ∈ D` or `w* ∈ S¹`, because `g_{w_k}`
degenerates in the second case.  The exact difference formula
`g_w(u) - g_w(v) = (u - v)(1 - |w|²)/((1 - w̄u)(1 - w̄v))`
(`diskAut_sub_diskAut`, in `Basic.lean`) makes the split unnecessary: on the circle it gives
`|g_w(u) - g_w(v)| ≤ 4|u - v|/ε` for every `w ∈ D` with `|v - w| ≥ ε`
(`norm_diskAut_sub_diskAut_le`), and the bound does not degrade as `w → ∂D`,
because `1 - |w|² ≤ 2|v - w|` absorbs exactly the degeneration.  With no limit
point to name, the argument becomes a direct `ε`-`δ` estimate.

*The two cases are combined before integrating.*  Rather than integrating over
the bad set `C = φ⁻¹(S¹ \ I)` and its complement separately, the two bounds —
`|F| ≤ 1/2` where `φ(ζ)` is near `ω`, and `P(z, ζ) ≤ M` where it is not — are
combined into the single *pointwise* inequality `‖F‖·P ≤ (1/2)·P + M`, valid at
every `θ`.  `harmonicMeasureAvg_norm_le_split` then integrates it in one step.
So `C` never has to be measurable, and the concentration statement `∫_C P → 0`
is replaced by the pointwise Poisson bound `poissonKernelDisk_le_of_far`.

What comes out is: if `w = Φ(z)` were at distance `≥ ε` from `ω = φ(ξ)`, then
`1 = |g_w(ω)| = |F(z, w) - g_w(ω)| ≤ 1/2 + M`, so `M ≥ 1/2`, which bounds
`1 - |z|²` from below and so keeps `z` away from `ξ`. -/

/-- `|1 - w̄ u| = |u - w|` for `|u| = 1`: `1 - w̄u = u · conj(u - w)`. -/
theorem norm_one_sub_star_mul_of_norm_one (w : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖(1:ℂ) - star w * u‖ = ‖u - w‖ := by
  have huu : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hid : (1:ℂ) - star w * u = u * star (u - w) := by
    rw [star_sub]
    ring_nf
    rw [← huu]
    ring
  rw [hid, norm_mul, hu, one_mul, norm_star]


theorem norm_pos_one_sub_star_mul (w : ℂ) {u : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ < 1) :
    0 < ‖u - w‖ := by
  rw [norm_pos_iff, sub_ne_zero]
  intro h
  rw [h] at hu
  rw [hu] at hw
  exact lt_irrefl 1 hw

theorem norm_diskAut_sub_diskAut (w : ℂ) {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ < 1) :
    ‖diskAut w u - diskAut w v‖ = ‖u - v‖ * (1 - ‖w‖ ^ 2) / (‖u - w‖ * ‖v - w‖) := by
  have hnum : (1:ℂ) - star w * w = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [diskAut_sub_diskAut w u v hw (le_of_eq hu) (le_of_eq hv), norm_div, norm_mul, norm_mul,
    hnum, norm_one_sub_star_mul_of_norm_one w hu, norm_one_sub_star_mul_of_norm_one w hv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith [norm_nonneg w] : (0:ℝ) ≤ 1 - ‖w‖ ^ 2)]
  ring

/-- The uniform estimate behind Lemma 2.  If `w ∈ D` stays at distance at least
`ε` from the boundary point `v`, then `g_w` moves the points of the arc
`|u - v| ≤ ε/2` by at most `4|u - v|/ε` — and the bound does not degrade as
`w → ∂D`.  This is what replaces the paper's split into `w* ∈ D` and
`w* ∈ S¹`. -/
theorem norm_diskAut_sub_diskAut_le (w : ℂ) {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ < 1) {ε : ℝ} (hε : 0 < ε) (hwv : ε ≤ ‖v - w‖) (huv : ‖u - v‖ ≤ ε / 2) :
    ‖diskAut w u - diskAut w v‖ ≤ 4 * ‖u - v‖ / ε := by
  have hvw : 0 < ‖v - w‖ := lt_of_lt_of_le hε hwv
  have huw : ε / 2 ≤ ‖u - w‖ := by
    have := norm_sub_norm_le (v - w) (v - u)
    have h2 : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
    have h3 : (v - w) - (v - u) = u - w := by ring
    rw [h3, h2] at this
    linarith
  have huw' : 0 < ‖u - w‖ := lt_of_lt_of_le (by linarith) huw
  have hP : 1 - ‖w‖ ^ 2 ≤ 2 * ‖v - w‖ := by
    have h1 : 1 - ‖w‖ ≤ ‖v - w‖ := by
      have := norm_sub_norm_le v w
      rw [hv] at this; linarith
    nlinarith [norm_nonneg w, hw]
  have hP0 : (0:ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have ha : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
  rw [norm_diskAut_sub_diskAut w hu hv hw, div_le_div_iff₀ (by positivity) hε]
  calc ‖u - v‖ * (1 - ‖w‖ ^ 2) * ε
      ≤ ‖u - v‖ * (2 * ‖v - w‖) * ε := by
        nlinarith [mul_nonneg (mul_nonneg ha hε.le)
          (by linarith : (0:ℝ) ≤ 2 * ‖v - w‖ - (1 - ‖w‖ ^ 2))]
    _ ≤ ‖u - v‖ * (2 * ‖v - w‖) * (2 * ‖u - w‖) := by
        nlinarith [mul_nonneg (mul_nonneg ha (by linarith : (0:ℝ) ≤ 2 * ‖v - w‖))
          (by linarith : (0:ℝ) ≤ 2 * ‖u - w‖ - ε)]
    _ = 4 * ‖u - v‖ * (‖u - w‖ * ‖v - w‖) := by ring


/-- Away from the pole the Poisson kernel is small: `|z - ζ| ≥ r > 0` forces
`P(z, ζ) ≤ (1 - |z|²)/r²`. -/
theorem poissonKernelDisk_le_of_far {z ζ : ℂ} (hz : ‖z‖ < 1) {r : ℝ} (hr : 0 < r)
    (h : r ≤ ‖z - ζ‖) : poissonKernelDisk z ζ ≤ (1 - ‖z‖ ^ 2) / r ^ 2 := by
  have hnum : (0:ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [poissonKernelDisk]
  gcongr

/-- A refinement of `harmonicMeasureAvg_norm_le` with a *pointwise* bound of the
form `‖F‖·P ≤ s·P + M` rather than a uniform bound on `‖F‖`.  This is what makes
the concentration argument of Lemma 2 work with no set integrals: the two cases
(`F` small, or `P` small) are combined into one inequality before integrating. -/
theorem harmonicMeasureAvg_norm_le_split {z : ℂ} (hz : ‖z‖ < 1) {F : Circle → ℂ} {s M : ℝ}
    (hb : ∀ θ : ℝ, ‖F (Circle.exp θ)‖ * poissonKernelDisk z (Circle.exp θ)
        ≤ s * poissonKernelDisk z (Circle.exp θ) + M) :
    ‖harmonicMeasureAvg z F‖ ≤ s + M := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hcP : Continuous fun θ : ℝ => s * poissonKernelDisk z (Circle.exp θ) :=
    continuous_const.mul (continuous_poissonKernelDisk_exp hz)
  have hbound : ∀ᵐ θ ∂volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
      ‖F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)‖
        ≤ s * poissonKernelDisk z (Circle.exp θ) + M := by
    filter_upwards with θ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonKernelDisk_nonneg (ζ := (Circle.exp θ : ℂ)) hz)]
    exact hb θ
  have hle := intervalIntegral.norm_integral_le_of_norm_le hpi.le hbound
      ((hcP.add continuous_const).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hcP.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_poissonKernel hz,
    intervalIntegral.integral_const] at hle
  rw [harmonicMeasureAvg, norm_mul]
  have hnorm : ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi),
        F (Circle.exp θ) * (poissonKernelDisk z (Circle.exp θ) : ℂ)‖
      ≤ (2 * Real.pi)⁻¹ * (s * (2 * Real.pi) + (2 * Real.pi - 0) • M) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = s + M := by
        simp only [smul_eq_mul, sub_zero]
        field_simp


theorem extension_continuousAt_boundary (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (ξ : Circle) :
    ContinuousWithinAt (extension φ) (Metric.closedBall (0:ℂ) 1) (ξ : ℂ) := by
  set ω : ℂ := ((φ ξ : Circle) : ℂ) with hωdef
  have hωnorm : ‖ω‖ = 1 := Circle.norm_coe _
  have hfξ : extension φ (ξ : ℂ) = ω := extension_eq_boundary φ ξ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hδpos : (0:ℝ) < ε / 8 := by positivity
  have hgc : Continuous fun ζ : Circle => ((φ ζ : Circle) : ℂ) :=
    continuous_subtype_val.comp hφc
  obtain ⟨d, hd, hdspec⟩ := Metric.continuousAt_iff.1 (hgc.continuousAt (x := ξ)) (ε / 8) hδpos
  refine ⟨min (d / 2) (d ^ 2 / 128), by positivity, ?_⟩
  intro z hzmem hzdist
  have hzn : ‖z - (ξ : ℂ)‖ < min (d / 2) (d ^ 2 / 128) := by rwa [← dist_eq_norm]
  have hzd2 : ‖z - (ξ : ℂ)‖ < d / 2 := lt_of_lt_of_le hzn (min_le_left _ _)
  have hzd3 : ‖z - (ξ : ℂ)‖ < d ^ 2 / 128 := lt_of_lt_of_le hzn (min_le_right _ _)
  have hz1 : ‖z‖ ≤ 1 := by simpa using hzmem
  rw [hfξ, dist_eq_norm]
  rcases lt_or_eq_of_le hz1 with hzlt | hzeq
  · -- `z ∈ D`: the concentration argument
    set w : ℂ := extension φ z with hwdef
    have hw : ‖w‖ < 1 := extension_mem_disk φ hφ hφc z hzlt
    by_contra hcon
    push Not at hcon
    have hεω : ε ≤ ‖ω - w‖ := by rwa [norm_sub_rev]
    have hbary : harmonicMeasureAvg z (fun ζ => diskAut w ((φ ζ : Circle) : ℂ)) = 0 :=
      (baryEq_iff_harmonicMeasureAvg φ z w).1 (extension_baryEq φ hφ hφc z hzlt)
    have hconst : harmonicMeasureAvg z (fun _ : Circle => diskAut w ω) = diskAut w ω := by
      have h := harmonicMeasureAvg_const_mul z (diskAut w ω) (fun _ : Circle => (1 : ℂ))
      simpa [harmonicMeasureAvg_const_one z hzlt] using h
    have hcd : Continuous fun ζ : Circle => diskAut w ((φ ζ : Circle) : ℂ) := by
      have hden : ∀ ζ : Circle, (1 : ℂ) - star w * ((φ ζ : Circle) : ℂ) ≠ 0 :=
        fun ζ => diskAut_denom_ne_zero _ _ hw (le_of_eq (Circle.norm_coe _))
      simp only [diskAut]
      exact Continuous.div (by fun_prop) (by fun_prop) hden
    have hdiff : harmonicMeasureAvg z (fun ζ => diskAut w ω - diskAut w ((φ ζ : Circle) : ℂ))
        = diskAut w ω := by
      rw [harmonicMeasureAvg_sub hzlt continuous_const hcd, hbary, hconst, sub_zero]
    set M : ℝ := 2 * ((1 - ‖z‖ ^ 2) / (d / 2) ^ 2) with hMdef
    have hz2nn : (0:ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hM0 : 0 ≤ M := by rw [hMdef]; positivity
    have hpt : ∀ θ : ℝ, ‖diskAut w ω - diskAut w ((φ (Circle.exp θ) : Circle) : ℂ)‖
        * poissonKernelDisk z (Circle.exp θ)
          ≤ (1 / 2) * poissonKernelDisk z (Circle.exp θ) + M := by
      intro θ
      set u : ℂ := ((φ (Circle.exp θ) : Circle) : ℂ) with hudef
      have hu1 : ‖u‖ = 1 := Circle.norm_coe _
      have hP0 : 0 ≤ poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ) :=
        poissonKernelDisk_nonneg hzlt
      by_cases hgood : dist (Circle.exp θ) ξ < d
      · have huω : ‖u - ω‖ < ε / 8 := by
          have h := hdspec hgood
          rwa [dist_eq_norm] at h
        have hle : ‖diskAut w u - diskAut w ω‖ ≤ 4 * ‖u - ω‖ / ε :=
          norm_diskAut_sub_diskAut_le w hu1 hωnorm hw hε hεω (by linarith)
        have hhalf : ‖diskAut w ω - diskAut w u‖ ≤ 1 / 2 := by
          rw [norm_sub_rev]
          have h4 : 4 * ‖u - ω‖ / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
          linarith
        nlinarith [hP0, hM0]
      · push Not at hgood
        have hgood' : d ≤ ‖((Circle.exp θ : Circle) : ℂ) - (ξ : ℂ)‖ := by
          rw [← dist_eq_norm]; exact hgood
        have hfar : d / 2 ≤ ‖z - ((Circle.exp θ : Circle) : ℂ)‖ := by
          have hsplit : ((Circle.exp θ : Circle) : ℂ) - (ξ : ℂ)
              = (((Circle.exp θ : Circle) : ℂ) - z) + (z - (ξ : ℂ)) := by ring
          have h3 := norm_add_le (((Circle.exp θ : Circle) : ℂ) - z) (z - (ξ : ℂ))
          rw [← hsplit] at h3
          rw [norm_sub_rev z]
          linarith [hgood']
        have hPle : poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ)
            ≤ (1 - ‖z‖ ^ 2) / (d / 2) ^ 2 :=
          poissonKernelDisk_le_of_far hzlt (by linarith) hfar
        have hnle : ‖diskAut w ω - diskAut w u‖ ≤ 2 := by
          calc ‖diskAut w ω - diskAut w u‖ ≤ ‖diskAut w ω‖ + ‖diskAut w u‖ := norm_sub_le _ _
            _ = 2 := by rw [diskAut_norm_eq_one w ω hw hωnorm,
                diskAut_norm_eq_one w u hw hu1]; norm_num
        have hbad : ‖diskAut w ω - diskAut w u‖
            * poissonKernelDisk z ((Circle.exp θ : Circle) : ℂ) ≤ M := by
          rw [hMdef]
          nlinarith [norm_nonneg (diskAut w ω - diskAut w u), hP0, hPle, hnle]
        nlinarith [hP0]
    have hfin := harmonicMeasureAvg_norm_le_split
      (F := fun ζ : Circle => diskAut w ω - diskAut w ((φ ζ : Circle) : ℂ)) hzlt hpt
    rw [hdiff, diskAut_norm_eq_one w ω hw hωnorm] at hfin
    have hdd : (0:ℝ) < (d / 2) ^ 2 := by positivity
    have hq : (1:ℝ) / 4 ≤ (1 - ‖z‖ ^ 2) / (d / 2) ^ 2 := by rw [hMdef] at hfin; linarith
    rw [le_div_iff₀ hdd] at hq
    have hz2 : 1 - ‖z‖ ^ 2 ≤ 2 * ‖z - (ξ : ℂ)‖ := by
      have h1 : 1 - ‖z‖ ≤ ‖z - (ξ : ℂ)‖ := by
        have h := norm_sub_norm_le (ξ : ℂ) z
        rw [Circle.norm_coe] at h
        rw [norm_sub_rev]
        linarith
      nlinarith [norm_nonneg z, hzlt]
    nlinarith [hzd3, hz2, hq, mul_pos hd hd]
  · -- `z ∈ S¹`: the extension is `φ` there
    have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 hzeq
    rw [extension_eq_boundary φ ⟨z, hmem⟩]
    have hdd : dist (⟨z, hmem⟩ : Circle) ξ < d := by
      show dist z (ξ : ℂ) < d
      rw [dist_eq_norm]
      linarith
    have h := hdspec hdd
    rw [dist_eq_norm] at h
    linarith

/-- **Theorem 1**, real-analyticity part: `Φ` restricted to `D` is
real-analytic.  (Together with `extension_jacobian_ne_zero`, which gives the
nonvanishing Jacobian, this is the statement that `Φ` is a diffeomorphism of
`D` onto itself.)

The proof is the freezing of `exists_analytic_baryEq_solution` at a fixed
boundary map.  The slice `z ↦ (z, φ)` is affine, hence analytic
(`analyticAt_slice`), so `F ∘ slice` is analytic at `z₀`; and it agrees with
`E(φ)` on the open set where the slice lands in `W`, by
`extension_eq_of_baryFnMap_eq_zero`.  Analyticity is a local property, so that
is all that is needed. -/
theorem extension_analyticOn_disk (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    AnalyticOn ℝ (extension φ) (Metric.ball (0:ℂ) 1) := by
  intro z₀ hz₀mem
  have hz₀ : ‖z₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz₀mem
  set φ₀ : C(Circle, Circle) := ⟨φ, hφc⟩ with hφ₀def
  obtain ⟨W, F, hW, hmem, hFan, hsol⟩ := exists_analytic_baryEq_solution z₀ hz₀ φ₀ hφ
  set s : ℂ → ℂ × C(Circle, ℂ) := fun z => (z, toComplexMap φ₀) with hsdef
  have hsc : Continuous s := continuous_id.prodMk continuous_const
  set U : Set ℂ := (s ⁻¹' W) ∩ Metric.ball (0:ℂ) 1 with hU
  have hUopen : IsOpen U := (hW.preimage hsc).inter Metric.isOpen_ball
  have hz₀U : z₀ ∈ U := ⟨hmem, hz₀mem⟩
  have hFat : AnalyticAt ℝ F (s z₀) := (hW.analyticOn_iff_analyticOnNhd.mp hFan) _ hmem
  have hcomp : AnalyticAt ℝ (F ∘ s) z₀ := hFat.comp (analyticAt_slice _ z₀)
  refine (hcomp.congr ?_).analyticWithinAt
  filter_upwards [hUopen.mem_nhds hz₀U] with z hzU
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hzU.2
  obtain ⟨hnorm, heq0⟩ := hsol (s z) hzU.1 hz1
  exact (extension_eq_of_baryFnMap_eq_zero φ₀ hφ hz1 hnorm heq0).symm


/-! ### Theorem 1, the homeomorphism half

Three clauses, and they are of very different depths.

*Mapping into `D̄`* is free: `extension_mem_disk` inside, `extension_eq_boundary`
on `S¹`.

*Continuity on `D̄`* is analyticity inside (`extension_analyticOn_disk`) glued to
Lemma 2 on the boundary; no separate input.

*The continuous inverse* is free too, but for a topological reason rather than a
computation: `D̄` is compact and `ℂ` is Hausdorff, so a continuous bijection of
`D̄` onto itself is automatically a homeomorphism
(`exists_continuousOn_invOn_of_bijOn`).  The third clause of the theorem is
therefore implied by the first two.

What is left is injectivity and surjectivity on `D̄`, and that is the genuine
topology: `Φ` is a proper local diffeomorphism of `D` (the Jacobian half of
Theorem 1) whose boundary values are a homeomorphism of `S¹`, and one concludes
by a degree or covering-space argument.  Mathlib has neither invariance of
domain nor a degree theory for these, so it is cited, in
`extension_injOn_surjOn`. -/

/-- A continuous bijection of a compact set onto itself has a continuous
inverse. -/
theorem exists_continuousOn_invOn_of_bijOn {s : Set ℂ} (hs : IsCompact s) {f : ℂ → ℂ}
    (hf : ContinuousOn f s) (hbij : Set.BijOn f s s) :
    ∃ finv : ℂ → ℂ, ContinuousOn finv s ∧ Set.InvOn finv f s s := by
  classical
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  set f' : s → s := fun x => ⟨f x, hbij.mapsTo x.2⟩ with hf'def
  have hf'c : Continuous f' := Continuous.subtype_mk hf.domRestrict _
  have hf'b : Function.Bijective f' := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hbij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hfx⟩ := hbij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  set e : s ≃ s := Equiv.ofBijective f' hf'b with hedef
  set hom : s ≃ₜ s := Continuous.homeoOfEquivCompactToT2 (f := e) hf'c with hhom
  refine ⟨fun w => if h : w ∈ s then ((hom.symm ⟨w, h⟩ : s) : ℂ) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hres : (s.domRestrict fun w => if h : w ∈ s then ((hom.symm ⟨w, h⟩ : s) : ℂ) else 0)
        = fun x : s => ((hom.symm x : s) : ℂ) := by
      funext x
      show (if h : (x : ℂ) ∈ s then ((hom.symm ⟨(x : ℂ), h⟩ : s) : ℂ) else 0)
        = ((hom.symm x : s) : ℂ)
      rw [dite_eq_left x.2]
    rw [hres]
    exact continuous_subtype_val.comp hom.symm.continuous
  · intro x hx
    have hfx : f x ∈ s := hbij.mapsTo hx
    show (if h : f x ∈ s then ((hom.symm ⟨f x, h⟩ : s) : ℂ) else 0) = x
    rw [dite_eq_left hfx]
    have hval : hom ⟨x, hx⟩ = ⟨f x, hfx⟩ := rfl
    rw [← hval, Homeomorph.symm_apply_apply]
  · intro w hw
    show f (if h : w ∈ s then ((hom.symm ⟨w, h⟩ : s) : ℂ) else 0) = w
    rw [dite_eq_left hw]
    have hval : f ((hom.symm ⟨w, hw⟩ : s) : ℂ) = ((hom (hom.symm ⟨w, hw⟩) : s) : ℂ) := rfl
    rw [hval, Homeomorph.apply_symm_apply]

/-- `Φ` maps `D̄` into `D̄`: `extension_mem_disk` inside, `extension_eq_boundary`
on `S¹`. -/
theorem mapsTo_extension (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    Set.MapsTo (extension φ) (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  rcases lt_or_eq_of_le hz1 with hlt | heq
  · simpa using (extension_mem_disk φ hφ hφc z hlt).le
  · have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
    have hb : extension φ z = ((φ ⟨z, hmem⟩ : Circle) : ℂ) := extension_eq_boundary φ ⟨z, hmem⟩
    rw [hb]
    simp

/-- `Φ` is continuous on `D̄`: analytic inside, Lemma 2 on the boundary. -/
theorem continuousOn_extension (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) : ContinuousOn (extension φ) (Metric.closedBall (0:ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  rcases lt_or_eq_of_le hz1 with hlt | heq
  · have hball : z ∈ Metric.ball (0:ℂ) 1 := by simpa using hlt
    have han := Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp
      (extension_analyticOn_disk φ hφ hφc) z hball
    exact han.continuousAt.continuousWithinAt
  · have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
    exact extension_continuousAt_boundary φ hφ hφc ⟨z, hmem⟩

/-! ### The elementary inequality behind Lemma 3

The proof of Lemma 3 evaluates `|c₁|² - |c₋₁|²` as the integral (3.5) of the
sum `H(t, u)` of four sines (3.6), and concludes that the integral is positive
because *if `α₁, α₂, α₃, α₄` are positive numbers whose sum is `2π`, then
`∑ⱼ sin αⱼ > 0`*.  That fact is proved here. -/

/-- Strict subadditivity of the sine on `(0, π)`: for `0 < x, y < π` we have
`sin (x + y) < sin x + sin y`, because `sin x, sin y > 0` while `cos x, cos y < 1`. -/
theorem sin_add_lt_sin_add_sin {x y : ℝ} (hx : 0 < x) (hx' : x < Real.pi)
    (hy : 0 < y) (hy' : y < Real.pi) :
    Real.sin (x + y) < Real.sin x + Real.sin y := by
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx hx'
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy hy'
  have hcx : Real.cos x < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hx'.le hx
  have hcy : Real.cos y < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hy'.le hy
  rw [Real.sin_add]
  nlinarith

/-- The case of `four_sin_pos` in which the (necessarily unique) angle that is
at least `π` is the last one.  Writing `s = a + b + c ≤ π` we have
`sin d = sin (2π - s) = -sin s`, and `sin s < sin a + sin b + sin c` by two
applications of `sin_add_lt_sin_add_sin`. -/
theorem four_sin_pos_of_pi_le {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hd : 0 < d) (hsum : a + b + c + d = 2 * Real.pi) (hdpi : Real.pi ≤ d) :
    0 < Real.sin a + Real.sin b + Real.sin c + Real.sin d := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hbc : b + c < Real.pi := by linarith
  have h1 : Real.sin (b + c) < Real.sin b + Real.sin c :=
    sin_add_lt_sin_add_sin hb (by linarith) hc (by linarith)
  have h2 : Real.sin (a + (b + c)) < Real.sin a + Real.sin (b + c) :=
    sin_add_lt_sin_add_sin ha (by linarith) (by linarith) hbc
  have hd' : d = 2 * Real.pi - (a + (b + c)) := by linarith
  have h3 : Real.sin d = -Real.sin (a + (b + c)) := by rw [hd']; simp [Real.sin_sub]
  linarith

/-- **The four sine inequality of Section 3**: if `α₁, α₂, α₃, α₄` are positive
numbers whose sum is `2π`, then `∑ⱼ sin αⱼ > 0`.  This is the final step in the
proof of Lemma 3 (and it is used again in Section 10 to bound `H(t, u)` from
below). -/
theorem four_sin_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b + c + d = 2 * Real.pi) :
    0 < Real.sin a + Real.sin b + Real.sin c + Real.sin d := by
  -- At most one of the four angles can be `≥ π`, since they are positive with sum `2π`.
  rcases le_or_gt Real.pi a with h | ha'
  · have := four_sin_pos_of_pi_le hb hc hd ha (by linarith) h; linarith
  rcases le_or_gt Real.pi b with h | hb'
  · have := four_sin_pos_of_pi_le ha hc hd hb (by linarith) h; linarith
  rcases le_or_gt Real.pi c with h | hc'
  · have := four_sin_pos_of_pi_le ha hb hd hc (by linarith) h; linarith
  rcases le_or_gt Real.pi d with h | hd'
  · exact four_sin_pos_of_pi_le ha hb hc hd hsum h
  -- Otherwise every angle lies in `(0, π)` and all four sines are positive.
  have s1 := Real.sin_pos_of_pos_of_lt_pi ha ha'
  have s2 := Real.sin_pos_of_pos_of_lt_pi hb hb'
  have s3 := Real.sin_pos_of_pos_of_lt_pi hc hc'
  have s4 := Real.sin_pos_of_pos_of_lt_pi hd hd'
  linarith

/-! ### Lemma 3, and the orientation hypothesis that was lost

Lemma 3 is stated in the paper for an *orientation-preserving* homeomorphism,
and the formal statement asked only for `Function.Bijective φ`.  That is not a
harmless omission: the conclusion `|c₁| > |c₋₁|` is **false** without it, and
`ζ ↦ ζ⁻¹ = conj ζ` is a one-line counterexample.  It is a homeomorphism of
`S¹`, its Fourier series is the single term `ζ⁻¹`, so `c₁ = 0` and `c₋₁ = 1`
and the conclusion reads `0 > 1`.  Exactly the failure mode of Remark (10.8):
a hypothesis that is universal convention in the source, and therefore went
unwritten, was lost in transcription. -/

/-- `ζ ↦ ζ⁻¹ = conj ζ` is a homeomorphism of `S¹`; it reverses orientation. -/
theorem bijective_circle_inv : Function.Bijective (fun ζ : Circle => ζ⁻¹) :=
  inv_involutive.bijective

/-- **Lemma 3 is false without orientation**: `ζ ↦ ζ⁻¹` satisfies every
hypothesis and violates the conclusion.  Its Fourier expansion is exact and
finite — the partial sums are equal to it for `n ≥ 1`, so the `L²` error is
eventually `0` — and `c₁ = 0`, `c₋₁ = 1`. -/
theorem lemma3_fourier_coeff_false :
    ¬ ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ c : ℤ → ℂ,
      Filter.Tendsto (fun n : ℕ => ∫ θ in (0:ℝ)..(2 * Real.pi),
          ‖(φ (Circle.exp θ) : ℂ)
            - ∑ k ∈ Finset.Icc (-(n:ℤ)) n, c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2)
        Filter.atTop (nhds 0) →
      ‖c 1‖ > ‖c (-1)‖ := by
  intro hbad
  set c : ℤ → ℂ := fun k => if k = -1 then 1 else 0 with hcdef
  have hzero : ∀ n : ℕ, 1 ≤ n →
      (∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖((fun ζ : Circle => ζ⁻¹) (Circle.exp θ) : ℂ)
          - ∑ k ∈ Finset.Icc (-(n:ℤ)) n, c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2) = 0 := by
    intro n hn
    have hmem : (-1 : ℤ) ∈ Finset.Icc (-(n:ℤ)) (n:ℤ) := by
      have : (1:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
      simp only [Finset.mem_Icc]
      omega
    have hsum : ∀ θ : ℝ, ∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * (Circle.exp θ : ℂ) ^ k
        = ((Circle.exp θ : Circle) : ℂ) ^ (-1 : ℤ) := by
      intro θ
      rw [Finset.sum_eq_single (-1 : ℤ)]
      · simp [hcdef]
      · intro b _ hb
        simp [hcdef, hb]
      · intro hcon
        exact absurd hmem hcon
    have hpt : ∀ θ : ℝ, ‖((fun ζ : Circle => ζ⁻¹) (Circle.exp θ) : ℂ)
        - ∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2 = 0 := by
      intro θ
      rw [hsum θ]
      rw [show ((Circle.exp θ : Circle) : ℂ) ^ (-1 : ℤ) = (((Circle.exp θ)⁻¹ : Circle) : ℂ) by
        rw [Circle.coe_inv, zpow_neg, zpow_one]]
      simp
    simp only [hpt]
    simp
  have htend : Filter.Tendsto (fun n : ℕ => ∫ θ in (0:ℝ)..(2 * Real.pi),
      ‖((fun ζ : Circle => ζ⁻¹) (Circle.exp θ) : ℂ)
        - ∑ k ∈ Finset.Icc (-(n:ℤ)) n, c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2)
      Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hzero n hn).symm
  have hfin := hbad (fun ζ : Circle => ζ⁻¹) bijective_circle_inv c htend
  simp [hcdef] at hfin
  linarith

/-- `g_{w̄}(ū) = conj (g_w(u))`: the Möbius factors of `E` commute with
conjugation.  This is the disc automorphism half of the statement that `E`
intertwines `φ ↦ conj ∘ φ ∘ conj` with `Φ ↦ conj ∘ Φ ∘ conj`. -/
theorem diskAut_star_star (w u : ℂ) :
    diskAut (star w) (star u) = star (diskAut w u) := by
  simp only [diskAut, star_div₀, star_sub, star_mul, star_star, star_one]
  ring_nf

/-- **`E(ζ ↦ ζ⁻¹) = conj`.**  On `S¹`, `ζ⁻¹ = conj ζ`, and conjugation carries
the barycentric equation to itself: `g_{z̄}(conj ζ) = conj (g_z(ζ))` by
`diskAut_star_star`, and the Poisson kernel is real, so
`⨍ g_{z̄}(conj ζ) dη_z = conj (⨍ g_z(ζ) dη_z) = 0` by `baryEq_id`.  Uniqueness
of the barycentre (`barycenter_existsUnique`) does the rest. -/
theorem extension_conj (z : ℂ) (hz : ‖z‖ < 1) :
    extension (fun ζ : Circle => ζ⁻¹) z = star z := by
  have hbij := bijective_circle_inv
  have hcont : Continuous (fun ζ : Circle => ζ⁻¹) := continuous_inv
  obtain ⟨w, -, huniq⟩ := barycenter_existsUnique _ hbij hcont z hz
  have hstar : ‖star z‖ < 1 := by rwa [norm_star]
  have hbe : baryEq (fun ζ : Circle => ζ⁻¹) z (star z) := by
    rw [baryEq_iff_harmonicMeasureAvg]
    have hpt : (fun ζ : Circle => diskAut (star z) (((ζ⁻¹ : Circle) : ℂ)))
        = fun ζ : Circle => star (diskAut z ((ζ : ℂ))) := by
      funext ζ
      have hc : ((ζ⁻¹ : Circle) : ℂ) = star ((ζ : ℂ)) := by
        rw [Circle.coe_inv_eq_conj, Complex.star_def]
      rw [hc, diskAut_star_star]
    rw [hpt, harmonicMeasureAvg_star]
    have := (baryEq_iff_harmonicMeasureAvg id z z).1 (baryEq_id z hz)
    simp only [id_eq] at this
    rw [this, star_zero]
  rw [huniq _ ⟨extension_mem_disk _ hbij hcont z hz, extension_baryEq _ hbij hcont z hz⟩,
    huniq _ ⟨hstar, hbe⟩]

/-- **The Jacobian half of Theorem 1 is false with a sign.**  The statement
`extension_jacobian_ne_zero` used to carry — `|Φ_z̄| < |Φ_z|`, the paper's
`|Φ_z|² - |Φ_z̄|² > 0` — fails for `φ(ζ) = ζ⁻¹`, whose extension is `z ↦ z̄`:
there `Φ_z = 0` and `Φ_z̄ = 1`, and the claim reads `2 < 0`.

This is `lemma3_fourier_coeff_false` one level up.  The orientation hypothesis
that Lemma 3 needs was restored there, as `HasIncreasingLift`, but never
propagated to the Jacobian, which is where it would have been consumed.  The
repair is not to add the hypothesis to Theorem 1 — Theorem 1 is true as the
paper states it, for every homeomorphism of `S¹` — but to weaken the Jacobian
to what a diffeomorphism actually needs, `|Φ_z̄| ≠ |Φ_z|`.  The strict form is
kept as `extension_jacobian_pos`, with `HasIncreasingLift`. -/
theorem extension_jacobian_ne_zero_false :
    ¬ (∀ (φ : Circle → Circle), Function.Bijective φ → Continuous φ → ∀ z : ℂ, ‖z‖ < 1 →
        ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
            + Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖
          < ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
            - Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖) := by
  intro h
  have hstarfun : (fun w : ℂ => star w) = ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := by
    funext w
    simp
  have heq : extension (fun ζ : Circle => ζ⁻¹) =ᶠ[nhds (0:ℂ)] (fun w : ℂ => star w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0:ℂ) ∈ Metric.ball (0:ℂ) 1 by simp)]
      with w hw
    exact extension_conj w (by simpa using hw)
  have hfd : fderiv ℝ (extension (fun ζ : Circle => ζ⁻¹)) 0
      = ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := by
    rw [heq.fderiv_eq, hstarfun]
    exact ContinuousLinearMap.fderiv _
  have hbad := h _ bijective_circle_inv continuous_inv 0 (by norm_num)
  rw [hfd] at hbad
  have h1 : ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 1 = 1 := by simp
  have h2 : ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by simp
  rw [h1, h2] at hbad
  have e1 : (1 : ℂ) + Complex.I * (-Complex.I) = 2 := by
    linear_combination -Complex.I_mul_I
  have e2 : (1 : ℂ) - Complex.I * (-Complex.I) = 0 := by
    linear_combination Complex.I_mul_I
  rw [e1, e2] at hbad
  simp only [norm_zero] at hbad
  have hn2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hn2] at hbad
  linarith

/-- An orientation-preserving homeomorphism of `S¹`, in the form the proof of
Lemma 3 uses: an increasing lift `h : ℝ → ℝ` with `h(t + 2π) = h(t) + 2π` and
`φ(e^{it}) = e^{ih(t)}`.  Increasing is what "orientation preserving" means
once a lift is chosen, and the paper's argument works with the lift throughout.

The lift is packaged into the hypothesis rather than produced from `φ`, but not
because it is unavailable: `CircleLift.exists_strictMono_lift` *does* produce a
strictly monotone lift of degree `±1` for every homeomorphism of `S¹`.  What it
cannot do is choose the sign — that is the orientation, and an
orientation-reversing `φ` gets a decreasing lift.  So `HasIncreasingLift` is
exactly the orientation hypothesis, and is genuinely restrictive.

Where it *can* be discharged, it is: `CircleLift.hasIncreasingLift_of_isDiskAutPlus`
proves it for every element of `G₊`, and `CircleLift.hasIncreasingLift_comp`
propagates it through composition.  Those two are what let
`exists_implicit_fderiv_z_of_orient` transport the hypothesis from `φ` to the
normalized map. -/
def HasIncreasingLift (φ : Circle → Circle) : Prop :=
  ∃ h : ℝ → ℝ, StrictMono h ∧ (∀ t : ℝ, h (t + 2 * Real.pi) = h t + 2 * Real.pi) ∧
    ∀ t : ℝ, ((φ (Circle.exp t) : Circle) : ℂ) = Complex.exp (h t * Complex.I)

/-- What the increasing lift buys, and the point at which orientation enters
the proof of Lemma 3: for `t₁ < t₂ < t₃ < t₄ < t₁ + 2π` the four increments of
`h` are positive — that is `StrictMono h` — and they sum to `2π` — that is the
periodicity — so `four_sin_pos` applies to them.  For an orientation-reversing
`φ` the lift decreases and every increment changes sign, which is precisely
what `lemma3_fourier_coeff_false` exploits. -/
theorem four_sin_pos_of_lift {h : ℝ → ℝ} (hmono : StrictMono h)
    (hper : ∀ t : ℝ, h (t + 2 * Real.pi) = h t + 2 * Real.pi)
    {t₁ t₂ t₃ t₄ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h34 : t₃ < t₄)
    (h41 : t₄ < t₁ + 2 * Real.pi) :
    0 < Real.sin (h t₂ - h t₁) + Real.sin (h t₃ - h t₂) + Real.sin (h t₄ - h t₃)
          + Real.sin (h t₁ + 2 * Real.pi - h t₄) := by
  have a1 : 0 < h t₂ - h t₁ := sub_pos.2 (hmono h12)
  have a2 : 0 < h t₃ - h t₂ := sub_pos.2 (hmono h23)
  have a3 : 0 < h t₄ - h t₃ := sub_pos.2 (hmono h34)
  have a4 : 0 < h t₁ + 2 * Real.pi - h t₄ := by
    have hlt := hmono h41
    rw [hper] at hlt
    linarith
  exact four_sin_pos a1 a2 a3 a4 (by ring)

/-! ### Lemma 3, proved

The proof is Douady–Earle's, reorganized so that the four-sine inequality is
applied to *one* explicitly chosen quadruple rather than integrated over all of
them.  Write `φ(e^{it}) = e^{ih(t)}` with `h` an increasing lift.

**The Fourier half.**  `c₁` and `c₋₁` are the pairings of `φ` with `e^{∓iθ}`,
which `integral_eq_of_L2` extracts from the `L²` hypothesis: the pairing of a
trigonometric polynomial with a character is its coefficient
(`integral_partialSum`, by orthogonality), and `L²` convergence passes to the
pairing because `‖∫ g·w‖ ≤ ∫‖g‖ ≤ (2ε)⁻¹∫‖g‖² + πε` for every `ε > 0`
(`tendsto_integral_of_tendsto_integral_sq` — Cauchy–Schwarz in the only form
needed, proved from `0 ≤ (‖g‖ - ε)²`).  Writing `e^{i(h θ ∓ θ)}` in real and
imaginary parts turns `2π c₁` and `2π c₋₁` into

    (d + a) + i(c - b)    and    (d - a) + i(c + b),

with `a = ∫ sin t sin h t`, `b = ∫ sin t cos h t`, `c = ∫ cos t sin h t`,
`d = ∫ cos t cos h t`.  So `4π²(|c₁|² - |c₋₁|²) = 4(ad - bc)`, and **Lemma 3 is
exactly the positivity of the determinant `ad - bc`** (`det_pos`).

**The determinant half.**  `ad - bc` is the determinant of
`M = ∫₀²π u(t) v(t)ᵀ dt` with `u(t) = (cos t, sin t)` and
`v(t) = (cos h t, sin h t)`, and the Cauchy–Binet antisymmetrization gives

    2 det M = ∫₀²π ∫₀²π sin(t - s) sin(h t - h s) dt ds

(`A_eq`, proved by expanding the integrand and integrating in `t` first — no
Fubini is needed, the two variables separate).  Substituting `t = s + v`
(`N_shift`, by `2π`-periodicity of the integrand) turns the inner integral into
`∫₀²π sin v · sin(h(s+v) - h s) dv`.

Now split that at `π`.  The second half, after `v ↦ v + π`, is
`∫₀^π sin v · sin(h s + 2π - h(s+π+v)) dv` (`N_split`) — which is the *fourth*
term of the four-sine sum at the cyclically ordered quadruple

    s < s + v < s + π < s + π + v < s + 2π.

The other two terms of that sum are the first and fourth translated by `π`
(`G3_eq`, `G2_eq`), and translating by `π` does not change an integral over a
period.  So twice the double integral is

    ∫₀²π ∫₀^π sin v · [the four-sine sum at that quadruple] dv ds,

and the integrand is positive: `sin v > 0` on `(0, π)`, and the four-sine sum is
positive by `four_sin_pos_of_lift`.  That is `G_sum_pos`, and `det_pos` follows.

The choice of quadruple is what makes this work.  Douady–Earle's formula (3.5)
integrates over *all* ordered quadruples with a weight; the equally spaced pair
of gaps `(v, π - v, v, π - v)` used here is the one for which the weight
collapses to `sin v`, because the resulting four terms are already the two
distinct integrals `G₁, G₄` and their `π`-translates. -/

namespace Lemma3

/-- A bounded measurable function is interval integrable. -/
theorem intervalIntegrable_of_bound {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ t, |g t| ≤ C) (a b : ℝ) : IntervalIntegrable g volume a b := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  refine (intervalIntegrable_const (c := C)).mono_fun hg.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
  exact hb x

variable {h : ℝ → ℝ}

/-- `v ↦ sin v * f v` is interval integrable for bounded measurable `f`. -/
theorem ii_sin_mul {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ v, |f v| ≤ C)
    (a b : ℝ) : IntervalIntegrable (fun v => Real.sin v * f v) volume a b :=
  intervalIntegrable_of_bound (Real.measurable_sin.fun_mul hfm) (C := C)
    (fun v => by
      rw [abs_mul]
      calc |Real.sin v| * |f v| ≤ 1 * |f v| :=
            mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |f v| := one_mul _
        _ ≤ C := hfb v) a b

/-! ### The four coefficients -/

def aa (h : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..(2*Real.pi), Real.sin t * Real.sin (h t)
def bb (h : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..(2*Real.pi), Real.sin t * Real.cos (h t)
def cc (h : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..(2*Real.pi), Real.cos t * Real.sin (h t)
def dd (h : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..(2*Real.pi), Real.cos t * Real.cos (h t)

theorem ii_sin_sin (hm : Measurable h) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.sin t * Real.sin (h t)) volume a b :=
  intervalIntegrable_of_bound (by fun_prop) (C := 1) (fun t => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one t)).trans (Real.abs_sin_le_one _)) a b

theorem ii_sin_cos (hm : Measurable h) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.sin t * Real.cos (h t)) volume a b :=
  intervalIntegrable_of_bound (by fun_prop) (C := 1) (fun t => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one t)).trans (Real.abs_cos_le_one _)) a b

theorem ii_cos_sin (hm : Measurable h) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos t * Real.sin (h t)) volume a b :=
  intervalIntegrable_of_bound (by fun_prop) (C := 1) (fun t => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one t)).trans (Real.abs_sin_le_one _)) a b

theorem ii_cos_cos (hm : Measurable h) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos t * Real.cos (h t)) volume a b :=
  intervalIntegrable_of_bound (by fun_prop) (C := 1) (fun t => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one t)).trans (Real.abs_cos_le_one _)) a b

theorem N_eq (hm : Measurable h) (s : ℝ) :
    (∫ t in (0:ℝ)..(2*Real.pi), Real.sin (t - s) * Real.sin (h t - h s))
      = Real.cos s * Real.cos (h s) * aa h - Real.cos s * Real.sin (h s) * bb h
        - Real.sin s * Real.cos (h s) * cc h + Real.sin s * Real.sin (h s) * dd h := by
  have hpt : ∀ t : ℝ, Real.sin (t - s) * Real.sin (h t - h s)
      = (Real.cos s * Real.cos (h s)) * (Real.sin t * Real.sin (h t))
        - (Real.cos s * Real.sin (h s)) * (Real.sin t * Real.cos (h t))
        - (Real.sin s * Real.cos (h s)) * (Real.cos t * Real.sin (h t))
        + (Real.sin s * Real.sin (h s)) * (Real.cos t * Real.cos (h t)) := by
    intro t
    rw [Real.sin_sub, Real.sin_sub]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · rfl
  · exact ((ii_sin_sin hm _ _).const_mul _)
  · exact ((ii_sin_cos hm _ _).const_mul _)
  · exact (((ii_sin_sin hm _ _).const_mul _).sub ((ii_sin_cos hm _ _).const_mul _))
  · exact ((ii_cos_sin hm _ _).const_mul _)
  · exact ((((ii_sin_sin hm _ _).const_mul _).sub
      ((ii_sin_cos hm _ _).const_mul _)).sub ((ii_cos_sin hm _ _).const_mul _))
  · exact ((ii_cos_cos hm _ _).const_mul _)

/-- **The determinant identity.** -/
theorem A_eq (hm : Measurable h) :
    (∫ s in (0:ℝ)..(2*Real.pi), ∫ t in (0:ℝ)..(2*Real.pi),
        Real.sin (t - s) * Real.sin (h t - h s))
      = 2 * (aa h * dd h - bb h * cc h) := by
  have hN : ∀ s : ℝ, (∫ t in (0:ℝ)..(2*Real.pi), Real.sin (t - s) * Real.sin (h t - h s))
      = (Real.cos s * Real.cos (h s)) * aa h - (Real.cos s * Real.sin (h s)) * bb h
        - (Real.sin s * Real.cos (h s)) * cc h + (Real.sin s * Real.sin (h s)) * dd h := by
    intro s; rw [N_eq hm]
  simp only [hN]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  · show dd h * aa h - cc h * bb h - bb h * cc h + aa h * dd h = _
    ring
  · exact ((ii_cos_cos hm _ _).mul_const _)
  · exact ((ii_cos_sin hm _ _).mul_const _)
  · exact (((ii_cos_cos hm _ _).mul_const _).sub ((ii_cos_sin hm _ _).mul_const _))
  · exact ((ii_sin_cos hm _ _).mul_const _)
  · exact ((((ii_cos_cos hm _ _).mul_const _).sub
      ((ii_cos_sin hm _ _).mul_const _)).sub ((ii_sin_cos hm _ _).mul_const _))
  · exact ((ii_sin_sin hm _ _).mul_const _)

/-- **Step 2**: the inner integral in the gap variable `v = t - s`. -/
theorem N_shift (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) (s : ℝ) :
    (∫ t in (0:ℝ)..(2*Real.pi), Real.sin (t - s) * Real.sin (h t - h s))
      = ∫ v in (0:ℝ)..(2*Real.pi), Real.sin v * Real.sin (h (s + v) - h s) := by
  have hp : Function.Periodic (fun t => Real.sin (t - s) * Real.sin (h t - h s)) (2*Real.pi) := by
    intro t
    simp only
    rw [hper t, show t + 2*Real.pi - s = (t - s) + 2*Real.pi by ring, Real.sin_add_two_pi,
      show h t + 2*Real.pi - h s = (h t - h s) + 2*Real.pi by ring, Real.sin_add_two_pi]
  have h1 : (∫ t in (0:ℝ)..(2*Real.pi), Real.sin (t - s) * Real.sin (h t - h s))
      = ∫ t in s..(s + 2*Real.pi), Real.sin (t - s) * Real.sin (h t - h s) := by
    have hh := hp.intervalIntegral_add_eq s 0
    rw [zero_add] at hh
    exact hh.symm
  have key := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 2*Real.pi)
    (fun t => Real.sin (t - s) * Real.sin (h t - h s)) s
  simp only [zero_add] at key
  rw [h1, show s + 2*Real.pi = 2*Real.pi + s by ring, ← key]
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only
  rw [add_sub_cancel_right, add_comm v s]

/-! ### The four terms of the four-sine sum -/

def G1 (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..Real.pi, Real.sin v * Real.sin (h (s + v) - h s)
def G2 (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..Real.pi, Real.sin v * Real.sin (h (s + Real.pi) - h (s + v))
def G3 (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..Real.pi, Real.sin v * Real.sin (h (s + Real.pi + v) - h (s + Real.pi))
def G4 (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..Real.pi, Real.sin v * Real.sin (h s + 2*Real.pi - h (s + Real.pi + v))

theorem measurable_param (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    Measurable (fun s => ∫ v in (0:ℝ)..Real.pi, F (s, v)) := by
  have hrw : ∀ s : ℝ, (∫ v in (0:ℝ)..Real.pi, F (s, v))
      = ∫ v, F (s, v) ∂(volume.restrict (Set.Ioc (0:ℝ) Real.pi)) :=
    fun s => intervalIntegral.integral_of_le Real.pi_pos.le
  simp only [hrw]
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_G1 (hm : Measurable h) : Measurable (G1 h) :=
  measurable_param (fun p => Real.sin p.2 * Real.sin (h (p.1 + p.2) - h p.1))
    ((Real.measurable_sin.comp measurable_snd).mul (Real.measurable_sin.comp
      ((hm.comp (measurable_fst.add measurable_snd)).sub (hm.comp measurable_fst))))

theorem measurable_G2 (hm : Measurable h) : Measurable (G2 h) :=
  measurable_param (fun p => Real.sin p.2 * Real.sin (h (p.1 + Real.pi) - h (p.1 + p.2)))
    ((Real.measurable_sin.comp measurable_snd).mul (Real.measurable_sin.comp
      ((hm.comp (measurable_fst.add measurable_const)).sub
        (hm.comp (measurable_fst.add measurable_snd)))))

theorem measurable_G3 (hm : Measurable h) : Measurable (G3 h) :=
  measurable_param
    (fun p => Real.sin p.2 * Real.sin (h (p.1 + Real.pi + p.2) - h (p.1 + Real.pi)))
    ((Real.measurable_sin.comp measurable_snd).mul (Real.measurable_sin.comp
      ((hm.comp ((measurable_fst.add measurable_const).add measurable_snd)).sub
        (hm.comp (measurable_fst.add measurable_const)))))

theorem measurable_G4 (hm : Measurable h) : Measurable (G4 h) :=
  measurable_param
    (fun p => Real.sin p.2 * Real.sin (h p.1 + 2*Real.pi - h (p.1 + Real.pi + p.2)))
    ((Real.measurable_sin.comp measurable_snd).mul (Real.measurable_sin.comp
      (((hm.comp measurable_fst).add measurable_const).sub
        (hm.comp ((measurable_fst.add measurable_const).add measurable_snd)))))

theorem abs_integral_sin_mul_le (f : ℝ → ℝ) (hf : ∀ v, |f v| ≤ 1) :
    |∫ v in (0:ℝ)..Real.pi, Real.sin v * f v| ≤ Real.pi := by
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
    (f := fun v => Real.sin v * f v) (a := (0:ℝ)) (b := Real.pi) (fun v _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans (hf v))
  rw [Real.norm_eq_abs, one_mul, sub_zero, abs_of_pos Real.pi_pos] at hle
  exact hle

theorem ii_G1 (hm : Measurable h) (a b : ℝ) : IntervalIntegrable (G1 h) volume a b :=
  intervalIntegrable_of_bound (measurable_G1 hm)
    (fun _ => abs_integral_sin_mul_le _ (fun _ => Real.abs_sin_le_one _)) a b
theorem ii_G2 (hm : Measurable h) (a b : ℝ) : IntervalIntegrable (G2 h) volume a b :=
  intervalIntegrable_of_bound (measurable_G2 hm)
    (fun _ => abs_integral_sin_mul_le _ (fun _ => Real.abs_sin_le_one _)) a b
theorem ii_G3 (hm : Measurable h) (a b : ℝ) : IntervalIntegrable (G3 h) volume a b :=
  intervalIntegrable_of_bound (measurable_G3 hm)
    (fun _ => abs_integral_sin_mul_le _ (fun _ => Real.abs_sin_le_one _)) a b
theorem ii_G4 (hm : Measurable h) (a b : ℝ) : IntervalIntegrable (G4 h) volume a b :=
  intervalIntegrable_of_bound (measurable_G4 hm)
    (fun _ => abs_integral_sin_mul_le _ (fun _ => Real.abs_sin_le_one _)) a b

/-- **Step 3a**: splitting the `v`-integral at `π` turns the second half into
the *fourth* term of the four-sine sum. -/
theorem N_split (hm : Measurable h) (s : ℝ) :
    (∫ v in (0:ℝ)..(2*Real.pi), Real.sin v * Real.sin (h (s + v) - h s))
      = G1 h s + G4 h s := by
  have hii : ∀ a b : ℝ, IntervalIntegrable
      (fun v => Real.sin v * Real.sin (h (s + v) - h s)) volume a b :=
    fun a b => ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) a b
  rw [G1, ← intervalIntegral.integral_add_adjacent_intervals
    (hii 0 Real.pi) (hii Real.pi (2*Real.pi))]
  congr 1
  have key := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := Real.pi)
    (fun v => Real.sin v * Real.sin (h (s + v) - h s)) Real.pi
  simp only [zero_add] at key
  rw [show 2*Real.pi = Real.pi + Real.pi by ring, ← key, G4]
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only
  rw [show s + (v + Real.pi) = s + Real.pi + v by ring,
    show h s + 2*Real.pi - h (s + Real.pi + v)
      = -(h (s + Real.pi + v) - h s) + 2*Real.pi by ring,
    Real.sin_add_two_pi, Real.sin_neg, Real.sin_add_pi]
  ring

/-- `G3` is `G1` shifted by `π`. -/
theorem G3_eq (s : ℝ) : G3 h s = G1 h (s + Real.pi) := rfl

/-- `G2` is `G4` shifted by `π`. -/
theorem G2_eq (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) (s : ℝ) :
    G2 h s = G4 h (s + Real.pi) := by
  rw [G2, G4]
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only
  rw [show s + Real.pi + Real.pi + v = (s + v) + 2*Real.pi by ring, hper (s + v)]
  congr 2
  ring

theorem periodic_G1 (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) :
    Function.Periodic (G1 h) (2*Real.pi) := by
  intro s
  rw [G1, G1]
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only
  rw [show s + 2*Real.pi + v = (s + v) + 2*Real.pi by ring, hper (s + v), hper s]
  congr 2
  ring

theorem periodic_G4 (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) :
    Function.Periodic (G4 h) (2*Real.pi) := by
  intro s
  rw [G4, G4]
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only
  rw [show s + 2*Real.pi + Real.pi + v = (s + Real.pi + v) + 2*Real.pi by ring,
    hper (s + Real.pi + v), hper s]
  congr 2
  ring

theorem integral_shift_eq {F : ℝ → ℝ} (hFper : Function.Periodic F (2*Real.pi)) (c : ℝ) :
    (∫ s in (0:ℝ)..(2*Real.pi), F (s + c)) = ∫ s in (0:ℝ)..(2*Real.pi), F s := by
  rw [intervalIntegral.integral_comp_add_right F c, zero_add,
    show 2*Real.pi + c = c + 2*Real.pi by ring]
  have hh := hFper.intervalIntegral_add_eq c 0
  rw [zero_add] at hh
  exact hh

/-! ### Positivity, from the four-sine inequality -/

/-- **Step 4.**  The four terms, added under a single integral sign, are the
four-sine sum of `four_sin_pos_of_lift` at the cyclically ordered quadruple
`s < s + v < s + π < s + π + v < s + 2π`, weighted by `sin v > 0`. -/
theorem G_sum_pos (hmono : StrictMono h)
    (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) (s : ℝ) :
    0 < G1 h s + G2 h s + G3 h s + G4 h s := by
  have hm : Measurable h := hmono.monotone.measurable
  set S : ℝ → ℝ := fun v =>
    Real.sin (h (s + v) - h s) + Real.sin (h (s + Real.pi) - h (s + v))
      + Real.sin (h (s + Real.pi + v) - h (s + Real.pi))
      + Real.sin (h s + 2*Real.pi - h (s + Real.pi + v)) with hSdef
  have hSm : Measurable S := by rw [hSdef]; fun_prop
  have hSb : ∀ v, |S v| ≤ 4 := by
    intro v
    have e1 := abs_le.1 (Real.abs_sin_le_one (h (s + v) - h s))
    have e2 := abs_le.1 (Real.abs_sin_le_one (h (s + Real.pi) - h (s + v)))
    have e3 := abs_le.1 (Real.abs_sin_le_one (h (s + Real.pi + v) - h (s + Real.pi)))
    have e4 := abs_le.1 (Real.abs_sin_le_one (h s + 2*Real.pi - h (s + Real.pi + v)))
    simp only [hSdef]
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
  have hcomb : G1 h s + G2 h s + G3 h s + G4 h s
      = ∫ v in (0:ℝ)..Real.pi, Real.sin v * S v := by
    rw [G1, G2, G3, G4,
      ← intervalIntegral.integral_add
        (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _)
        (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _),
      ← intervalIntegral.integral_add
        (((ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _).add
          (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _)))
        (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _),
      ← intervalIntegral.integral_add
        ((((ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _).add
          (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _)).add
          (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _)))
        (ii_sin_mul (by fun_prop) (fun v => Real.abs_sin_le_one _) _ _)]
    refine intervalIntegral.integral_congr ?_
    intro v _
    simp only [hSdef]
    ring
  rw [hcomb]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (ii_sin_mul hSm hSb _ _) ?_ Real.pi_pos
  intro v hv
  refine mul_pos (Real.sin_pos_of_pos_of_lt_pi hv.1 hv.2) ?_
  rw [hSdef]
  exact four_sin_pos_of_lift hmono hper (t₁ := s) (t₂ := s + v) (t₃ := s + Real.pi)
    (t₄ := s + Real.pi + v) (by linarith [hv.1]) (by linarith [hv.2])
    (by linarith [hv.1]) (by linarith [hv.2])

/-- **Lemma 3, analytic core**: for an increasing `2π`-equivariant lift `h`,
the determinant `ad - bc` of `∫₀²π (cos t, sin t)(cos h t, sin h t)ᵀ dt` is
positive. -/
theorem det_pos (hmono : StrictMono h)
    (hper : ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) :
    0 < aa h * dd h - bb h * cc h := by
  have hm : Measurable h := hmono.monotone.measurable
  have hA2 : (∫ s in (0:ℝ)..(2*Real.pi), ∫ t in (0:ℝ)..(2*Real.pi),
      Real.sin (t - s) * Real.sin (h t - h s))
      = ∫ s in (0:ℝ)..(2*Real.pi), (G1 h s + G4 h s) := by
    refine intervalIntegral.integral_congr ?_
    intro s _
    simp only
    rw [N_shift hper s, N_split hm s]
  have hsum2 : (∫ s in (0:ℝ)..(2*Real.pi), (G1 h s + G4 h s))
      = (∫ s in (0:ℝ)..(2*Real.pi), G1 h s) + ∫ s in (0:ℝ)..(2*Real.pi), G4 h s :=
    intervalIntegral.integral_add (ii_G1 hm _ _) (ii_G4 hm _ _)
  have hkey : (∫ s in (0:ℝ)..(2*Real.pi), G1 h s) + (∫ s in (0:ℝ)..(2*Real.pi), G4 h s)
      = 2 * (aa h * dd h - bb h * cc h) := by
    rw [← hsum2, ← hA2, A_eq hm]
  have h31 : (∫ s in (0:ℝ)..(2*Real.pi), G3 h s) = ∫ s in (0:ℝ)..(2*Real.pi), G1 h s := by
    simp only [G3_eq]
    exact integral_shift_eq (periodic_G1 hper) Real.pi
  have h24 : (∫ s in (0:ℝ)..(2*Real.pi), G2 h s) = ∫ s in (0:ℝ)..(2*Real.pi), G4 h s := by
    simp only [G2_eq hper]
    exact integral_shift_eq (periodic_G4 hper) Real.pi
  have hsum : (∫ s in (0:ℝ)..(2*Real.pi), (G1 h s + G2 h s + G3 h s + G4 h s))
      = (∫ s in (0:ℝ)..(2*Real.pi), G1 h s) + (∫ s in (0:ℝ)..(2*Real.pi), G2 h s)
        + (∫ s in (0:ℝ)..(2*Real.pi), G3 h s) + ∫ s in (0:ℝ)..(2*Real.pi), G4 h s := by
    rw [intervalIntegral.integral_add
        (((ii_G1 hm _ _).add (ii_G2 hm _ _)).add (ii_G3 hm _ _)) (ii_G4 hm _ _),
      intervalIntegral.integral_add ((ii_G1 hm _ _).add (ii_G2 hm _ _)) (ii_G3 hm _ _),
      intervalIntegral.integral_add (ii_G1 hm _ _) (ii_G2 hm _ _)]
  have hpos : 0 < ∫ s in (0:ℝ)..(2*Real.pi), (G1 h s + G2 h s + G3 h s + G4 h s) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_
      (fun s _ => G_sum_pos hmono hper s) (by linarith [Real.pi_pos])
    exact (((ii_G1 hm _ _).add (ii_G2 hm _ _)).add (ii_G3 hm _ _)).add (ii_G4 hm _ _)
  rw [hsum, h31, h24] at hpos
  linarith


/-- Orthogonality of the characters: `∫₀²π e^{ijθ} dθ` is `2π` for `j = 0` and
`0` otherwise. -/
theorem integral_char (j : ℤ) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp ((j:ℂ) * θ * Complex.I))
      = if j = 0 then ((2*Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [ite_eq_right hj]
    have hne : ((j:ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Int.cast_eq_zero]
      exact hj
    have heq : ∀ θ : ℝ, Complex.exp ((j:ℂ) * θ * Complex.I)
        = Complex.exp (((j:ℂ) * Complex.I) * θ) := by
      intro θ; congr 1; ring
    simp only [heq]
    rw [integral_exp_mul_complex hne]
    have h1 : ((j:ℂ) * Complex.I) * ((2*Real.pi : ℝ) : ℂ)
        = (j:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by push_cast; ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- `ζ^k · e^{-imθ} = e^{i(k-m)θ}` on the circle. -/
theorem char_mul (k m : ℤ) (θ : ℝ) :
    ((Circle.exp θ : Circle) : ℂ) ^ k * Complex.exp (-(m:ℂ) * θ * Complex.I)
      = Complex.exp (((k - m : ℤ) : ℂ) * θ * Complex.I) := by
  rw [Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The `m`-th Fourier coefficient of a trigonometric polynomial. -/
theorem integral_partialSum (c : ℤ → ℂ) (n : ℕ) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(n:ℤ)) (n:ℤ)) :
    (∫ θ in (0:ℝ)..(2*Real.pi),
        (∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * ((Circle.exp θ : Circle) : ℂ) ^ k)
          * Complex.exp (-(m:ℂ) * θ * Complex.I))
      = ((2*Real.pi : ℝ) : ℂ) * c m := by
  have hexp : ∀ θ : ℝ,
      (∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * ((Circle.exp θ : Circle) : ℂ) ^ k)
          * Complex.exp (-(m:ℂ) * θ * Complex.I)
        = ∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),
            c k * Complex.exp (((k - m : ℤ) : ℂ) * θ * Complex.I) := by
    intro θ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [mul_assoc, char_mul]
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (Continuous.intervalIntegrable (by fun_prop) _ _))]
  rw [Finset.sum_eq_single m]
  · rw [intervalIntegral.integral_const_mul, integral_char, ite_eq_left (by ring)]
    ring
  · intro k _ hkm
    rw [intervalIntegral.integral_const_mul, integral_char, ite_eq_right (by omega), mul_zero]
  · intro hcon
    exact absurd hm hcon

/-- `∫ u ≤ (2ε)⁻¹ ∫ u² + πε` for `u ≥ 0`, whence `L²` convergence implies `L¹`
convergence.  This is Cauchy–Schwarz in the only form needed, proved from
`0 ≤ (u - ε)²`. -/
theorem tendsto_integral_of_tendsto_integral_sq {u : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (u n) volume 0 (2*Real.pi))
    (hsq : ∀ n, IntervalIntegrable (fun θ => (u n θ)^2) volume 0 (2*Real.pi))
    (hnn : ∀ n θ, 0 ≤ u n θ)
    (h2 : Filter.Tendsto (fun n => ∫ θ in (0:ℝ)..(2*Real.pi), (u n θ)^2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ θ in (0:ℝ)..(2*Real.pi), u n θ) Filter.atTop (nhds 0) := by
  have hπ := Real.pi_pos
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro δ hδ
  set ε : ℝ := δ / (4 * Real.pi) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hev : ∀ᶠ n in Filter.atTop,
      ‖∫ θ in (0:ℝ)..(2*Real.pi), (u n θ)^2‖ < ε * δ :=
    (NormedAddGroup.tendsto_nhds_zero.1 h2) (ε * δ) (by positivity)
  filter_upwards [hev] with n hn
  have hIsq_nn : 0 ≤ ∫ θ in (0:ℝ)..(2*Real.pi), (u n θ)^2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun θ _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hIsq_nn] at hn
  have hI_nn : 0 ≤ ∫ θ in (0:ℝ)..(2*Real.pi), u n θ :=
    intervalIntegral.integral_nonneg (by linarith) (fun θ _ => hnn n θ)
  have hpt : ∀ θ : ℝ, u n θ ≤ (1/(2*ε)) * (u n θ)^2 + ε/2 := by
    intro θ
    rw [← sub_nonneg]
    have hid : (1/(2*ε)) * (u n θ)^2 + ε/2 - u n θ = (u n θ - ε)^2/(2*ε) := by
      field_simp
      ring
    rw [hid]
    positivity
  have hmono : (∫ θ in (0:ℝ)..(2*Real.pi), u n θ)
      ≤ ∫ θ in (0:ℝ)..(2*Real.pi), ((1/(2*ε)) * (u n θ)^2 + ε/2) :=
    intervalIntegral.integral_mono_on (by linarith) (hint n)
      (((hsq n).const_mul _).add intervalIntegrable_const) (fun θ _ => hpt θ)
  rw [intervalIntegral.integral_add ((hsq n).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  rw [Real.norm_eq_abs, abs_of_nonneg hI_nn]
  have harith : (2*Real.pi - 0) • (ε/2) = Real.pi * ε := by
    simp only [smul_eq_mul, sub_zero]; ring
  rw [harith] at hmono
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hbound : (1/(2*ε)) * (∫ θ in (0:ℝ)..(2*Real.pi), (u n θ)^2) < δ/2 := by
    have h1 : (1/(2*ε)) * (∫ θ in (0:ℝ)..(2*Real.pi), (u n θ)^2) < (1/(2*ε)) * (ε * δ) :=
      mul_lt_mul_of_pos_left hn (by positivity)
    have h2' : (1/(2*ε)) * (ε * δ) = δ/2 := by field_simp
    rw [h2'] at h1
    exact h1
  have hπε : Real.pi * ε = δ/4 := by rw [hεdef]; field_simp
  rw [hπε] at hmono
  linarith


theorem intervalIntegrable_of_boundC {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ t, ‖g t‖ ≤ C) (a b : ℝ) : IntervalIntegrable g volume a b := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hb 0)
  refine (intervalIntegrable_const (c := ((C:ℝ):ℂ))).mono_fun hg.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  exact hb x

/-- `ζ^k = e^{ikθ}` on the circle. -/
theorem coe_exp_zpow (k : ℤ) (θ : ℝ) :
    ((Circle.exp θ : Circle) : ℂ) ^ k = Complex.exp ((k:ℂ) * θ * Complex.I) := by
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **`L²` convergence passes to the pairing with a unimodular weight.**  If the
trigonometric polynomials `P n` converge to `f` in `L²(0, 2π)` and
`∫ P n · w` is eventually the constant `L`, then `∫ f · w = L`. -/
theorem integral_eq_of_L2 {f : ℝ → ℂ} {P : ℕ → ℝ → ℂ} {w : ℝ → ℂ} {L : ℂ}
    (hfm : Measurable f) (hfb : ∀ θ, ‖f θ‖ ≤ 1)
    (hPc : ∀ n, Continuous (P n)) (hwc : Continuous w) (hwn : ∀ θ, ‖w θ‖ = 1)
    (hc : Filter.Tendsto (fun n => ∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - P n θ‖^2)
      Filter.atTop (nhds 0))
    (hP : ∀ᶠ n in Filter.atTop, (∫ θ in (0:ℝ)..(2*Real.pi), P n θ * w θ) = L) :
    (∫ θ in (0:ℝ)..(2*Real.pi), f θ * w θ) = L := by
  have hπ := Real.pi_pos
  have hfi : IntervalIntegrable f volume 0 (2*Real.pi) :=
    intervalIntegrable_of_boundC hfm hfb 0 (2*Real.pi)
  have hPi : ∀ n, IntervalIntegrable (P n) volume 0 (2*Real.pi) :=
    fun n => (hPc n).intervalIntegrable _ _
  have hdi : ∀ n, IntervalIntegrable (fun θ => f θ - P n θ) volume 0 (2*Real.pi) :=
    fun n => hfi.sub (hPi n)
  have hum : ∀ n, Measurable (fun θ => ‖f θ - P n θ‖) :=
    fun n => (hfm.sub (hPc n).measurable).norm
  have hui : ∀ n, IntervalIntegrable (fun θ => ‖f θ - P n θ‖) volume 0 (2*Real.pi) :=
    fun n => (hdi n).norm
  have hdle : ∀ n θ, ‖f θ - P n θ‖ ≤ 1 + ‖P n θ‖ := by
    intro n θ
    exact le_trans (norm_sub_le _ _) (add_le_add (hfb θ) le_rfl)
  have husq : ∀ n, IntervalIntegrable (fun θ => ‖f θ - P n θ‖^2) volume 0 (2*Real.pi) := by
    intro n
    have hPn := hPc n
    refine IntervalIntegrable.mono_fun
      ((by fun_prop : Continuous fun θ : ℝ => (1 + ‖P n θ‖)^2).intervalIntegrable _ _)
      ((hum n).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdle n θ) 2
  have hlim : Filter.Tendsto (fun n => ∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - P n θ‖)
      Filter.atTop (nhds 0) :=
    tendsto_integral_of_tendsto_integral_sq hui husq (fun _ _ => norm_nonneg _) hc
  have hev : ∀ᶠ n in Filter.atTop,
      ‖(∫ θ in (0:ℝ)..(2*Real.pi), f θ * w θ) - L‖
        ≤ ∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - P n θ‖ := by
    filter_upwards [hP] with n hn
    have hsplit : (∫ θ in (0:ℝ)..(2*Real.pi), (f θ - P n θ) * w θ)
        = (∫ θ in (0:ℝ)..(2*Real.pi), f θ * w θ) - L := by
      have hmulf : IntervalIntegrable (fun θ => f θ * w θ) volume 0 (2*Real.pi) :=
        intervalIntegrable_of_boundC (hfm.fun_mul hwc.measurable) (C := 1) (fun t => by
          rw [norm_mul, hwn, mul_one]; exact hfb t) _ _
      have hmulP : IntervalIntegrable (fun θ => P n θ * w θ) volume 0 (2*Real.pi) :=
        ((hPc n).mul hwc).intervalIntegrable _ _
      rw [show (fun θ => (f θ - P n θ) * w θ) = fun θ => f θ * w θ - P n θ * w θ from
          funext fun θ => sub_mul _ _ _,
        intervalIntegral.integral_sub hmulf hmulP, hn]
    rw [← hsplit]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith)) ?_
    refine le_of_eq (intervalIntegral.integral_congr ?_)
    intro θ _
    simp only
    rw [norm_mul, hwn, mul_one]
  have hle : ‖(∫ θ in (0:ℝ)..(2*Real.pi), f θ * w θ) - L‖ ≤ 0 := ge_of_tendsto hlim hev
  have := le_antisymm hle (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at this



/-- `e^{i h θ} e^{-i m θ} = cos(h θ - m θ) + i sin(h θ - m θ)`, integrated. -/
theorem integral_exp_h_mul (hmeas : Measurable h) (m : ℤ) :
    (∫ θ in (0:ℝ)..(2*Real.pi),
        Complex.exp ((h θ : ℂ) * Complex.I) * Complex.exp (-(m:ℂ) * (θ:ℂ) * Complex.I))
      = ((∫ θ in (0:ℝ)..(2*Real.pi), Real.cos (h θ - (m:ℝ)*θ) : ℝ) : ℂ)
        + ((∫ θ in (0:ℝ)..(2*Real.pi), Real.sin (h θ - (m:ℝ)*θ) : ℝ) : ℂ) * Complex.I := by
  have hpt : ∀ θ : ℝ,
      Complex.exp ((h θ : ℂ) * Complex.I) * Complex.exp (-(m:ℂ) * (θ:ℂ) * Complex.I)
        = ((Real.cos (h θ - (m:ℝ)*θ) : ℝ) : ℂ)
          + ((Real.sin (h θ - (m:ℝ)*θ) : ℝ) : ℂ) * Complex.I := by
    intro θ
    rw [← Complex.exp_add,
      show ((h θ : ℂ) * Complex.I + -(m:ℂ) * (θ:ℂ) * Complex.I)
        = ((h θ - (m:ℝ)*θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  simp only [hpt]
  have hci : IntervalIntegrable (fun θ : ℝ => ((Real.cos (h θ - (m:ℝ)*θ) : ℝ) : ℂ))
      volume 0 (2*Real.pi) :=
    intervalIntegrable_of_boundC (by fun_prop) (C := 1)
      (fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _) _ _
  have hsi : IntervalIntegrable (fun θ : ℝ => ((Real.sin (h θ - (m:ℝ)*θ) : ℝ) : ℂ))
      volume 0 (2*Real.pi) :=
    intervalIntegrable_of_boundC (by fun_prop) (C := 1)
      (fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _) _ _
  rw [intervalIntegral.integral_add hci (hsi.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]

theorem int_cos_one (hmeas : Measurable h) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Real.cos (h θ - ((1:ℤ):ℝ)*θ)) = dd h + aa h := by
  have hpt : ∀ θ : ℝ, Real.cos (h θ - ((1:ℤ):ℝ)*θ)
      = Real.cos θ * Real.cos (h θ) + Real.sin θ * Real.sin (h θ) := by
    intro θ
    push_cast
    rw [one_mul, Real.cos_sub]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_add (ii_cos_cos hmeas _ _) (ii_sin_sin hmeas _ _)]
  rfl

theorem int_sin_one (hmeas : Measurable h) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Real.sin (h θ - ((1:ℤ):ℝ)*θ)) = cc h - bb h := by
  have hpt : ∀ θ : ℝ, Real.sin (h θ - ((1:ℤ):ℝ)*θ)
      = Real.cos θ * Real.sin (h θ) - Real.sin θ * Real.cos (h θ) := by
    intro θ
    push_cast
    rw [one_mul, Real.sin_sub]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_sub (ii_cos_sin hmeas _ _) (ii_sin_cos hmeas _ _)]
  rfl

theorem int_cos_negone (hmeas : Measurable h) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Real.cos (h θ - ((-1:ℤ):ℝ)*θ)) = dd h - aa h := by
  have hpt : ∀ θ : ℝ, Real.cos (h θ - ((-1:ℤ):ℝ)*θ)
      = Real.cos θ * Real.cos (h θ) - Real.sin θ * Real.sin (h θ) := by
    intro θ
    push_cast
    rw [show h θ - (-1)*θ = h θ + θ by ring, Real.cos_add]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_sub (ii_cos_cos hmeas _ _) (ii_sin_sin hmeas _ _)]
  rfl

theorem int_sin_negone (hmeas : Measurable h) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Real.sin (h θ - ((-1:ℤ):ℝ)*θ)) = cc h + bb h := by
  have hpt : ∀ θ : ℝ, Real.sin (h θ - ((-1:ℤ):ℝ)*θ)
      = Real.cos θ * Real.sin (h θ) + Real.sin θ * Real.cos (h θ) := by
    intro θ
    push_cast
    rw [show h θ - (-1)*θ = h θ + θ by ring, Real.sin_add]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_add (ii_cos_sin hmeas _ _) (ii_sin_cos hmeas _ _)]
  rfl

theorem norm_sq_ofReal_add (x y : ℝ) :
    ‖((x:ℂ) + (y:ℂ) * Complex.I)‖^2 = x^2 + y^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- **Lemma 3.** -/
theorem lemma3 (φ : Circle → Circle) (hor : HasIncreasingLift φ) (c : ℤ → ℂ)
    (hc : Filter.Tendsto
      (fun n : ℕ => ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖(φ (Circle.exp θ) : ℂ)
          - ∑ k ∈ Finset.Icc (-(n:ℤ)) n, c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2)
      Filter.atTop (nhds 0)) :
    ‖c 1‖ > ‖c (-1)‖ := by
  obtain ⟨h, hmono, hper, hlift⟩ := hor
  have hmeas : Measurable h := hmono.monotone.measurable
  have hπ := Real.pi_pos
  have hfm : Measurable (fun θ : ℝ => Complex.exp ((h θ : ℂ) * Complex.I)) := by fun_prop
  have hfb : ∀ θ : ℝ, ‖Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 1 :=
    fun θ => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hPc : ∀ n : ℕ, Continuous (fun θ : ℝ =>
      ∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * ((Circle.exp θ : Circle) : ℂ) ^ k) := by
    intro n
    simp only [coe_exp_zpow]
    fun_prop
  have hcf : Filter.Tendsto
      (fun n : ℕ => ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖Complex.exp ((h θ : ℂ) * Complex.I)
          - ∑ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), c k * ((Circle.exp θ : Circle) : ℂ) ^ k‖ ^ 2)
      Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr (fun n => ?_) hc
    refine intervalIntegral.integral_congr ?_
    intro θ _
    simp only [hlift θ]
  have hkey : ∀ m : ℤ, (∫ θ in (0:ℝ)..(2*Real.pi),
      Complex.exp ((h θ : ℂ) * Complex.I) * Complex.exp (-(m:ℂ) * (θ:ℂ) * Complex.I))
      = ((2*Real.pi : ℝ) : ℂ) * c m := by
    intro m
    refine integral_eq_of_L2 hfm hfb hPc (by fun_prop) (fun θ => ?_) hcf ?_
    · rw [show (-(m:ℂ) * (θ:ℂ) * Complex.I) = (((-(m:ℝ) * θ : ℝ)) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · filter_upwards [Filter.eventually_ge_atTop m.natAbs] with n hn
      exact integral_partialSum c n m (by rw [Finset.mem_Icc]; omega)
  have hnn1 : (0:ℝ) ≤ ‖c 1‖ := norm_nonneg _
  have hnnm : (0:ℝ) ≤ ‖c (-1)‖ := norm_nonneg _
  have e1 : (2*Real.pi)^2 * ‖c 1‖^2 = (dd h + aa h)^2 + (cc h - bb h)^2 := by
    have hE : ((2*Real.pi : ℝ) : ℂ) * c 1
        = (((dd h + aa h : ℝ)) : ℂ) + (((cc h - bb h : ℝ)) : ℂ) * Complex.I := by
      rw [← hkey 1, integral_exp_h_mul hmeas 1, int_cos_one hmeas, int_sin_one hmeas]
    calc (2*Real.pi)^2 * ‖c 1‖^2 = ‖((2*Real.pi : ℝ) : ℂ) * c 1‖^2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          ring
      _ = _ := by rw [hE, norm_sq_ofReal_add]
  have e2 : (2*Real.pi)^2 * ‖c (-1)‖^2 = (dd h - aa h)^2 + (cc h + bb h)^2 := by
    have hE : ((2*Real.pi : ℝ) : ℂ) * c (-1)
        = (((dd h - aa h : ℝ)) : ℂ) + (((cc h + bb h : ℝ)) : ℂ) * Complex.I := by
      rw [← hkey (-1), integral_exp_h_mul hmeas (-1), int_cos_negone hmeas, int_sin_negone hmeas]
    calc (2*Real.pi)^2 * ‖c (-1)‖^2 = ‖((2*Real.pi : ℝ) : ℂ) * c (-1)‖^2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          ring
      _ = _ := by rw [hE, norm_sq_ofReal_add]
  have hdet := det_pos hmono hper
  have hpi2 : 0 < (2*Real.pi)^2 := by positivity
  have hdiff : (2*Real.pi)^2 * (‖c 1‖^2 - ‖c (-1)‖^2)
      = 4 * (aa h * dd h - bb h * cc h) := by
    have : (2*Real.pi)^2 * (‖c 1‖^2 - ‖c (-1)‖^2)
        = (2*Real.pi)^2 * ‖c 1‖^2 - (2*Real.pi)^2 * ‖c (-1)‖^2 := by ring
    rw [this, e1, e2]
    ring
  have hpos : 0 < (2*Real.pi)^2 * (‖c 1‖^2 - ‖c (-1)‖^2) := by rw [hdiff]; linarith
  have hsq : ‖c (-1)‖^2 < ‖c 1‖^2 := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hpos, mul_nonneg hpi2.le (sub_nonneg.2 hcon)]
  nlinarith [hsq, hnn1, hnnm]


end Lemma3

set_option linter.unusedVariables false in
/-- **Lemma 3**, corrected and **proved**: if `φ : S¹ → S¹` is an
*orientation-preserving* homeomorphism with Fourier series `φ(ζ) = ∑ cₙ ζⁿ`
(convergent in `L²(S¹)`), then `|c₁| > |c₋₁|`.

`hor` is the hypothesis that had been lost; without it the statement is refuted
by `lemma3_fourier_coeff_false`.  `hφ` is not used: an increasing lift already
forces `φ` to be injective, and surjectivity plays no role in the argument.  It
is kept because the paper states Lemma 3 for homeomorphisms.

The proof is `Lemma3.lemma3`; see the section header above for how it is
organized. -/
theorem lemma3_fourier_coeff (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hor : HasIncreasingLift φ)
    (c : ℤ → ℂ)
    (hc : Filter.Tendsto
      (fun n : ℕ => ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖(φ (Circle.exp θ) : ℂ) - ∑ k ∈ Finset.Icc (-(n:ℤ)) n, c k * (Circle.exp θ : ℂ) ^ k‖ ^ 2)
      Filter.atTop (nhds 0)) :
    ‖c 1‖ > ‖c (-1)‖ :=
  Lemma3.lemma3 φ hor c hc

/-! ### The lift dichotomy

Every homeomorphism of `S¹` has a strictly monotone lift of degree `±1`, and
`HasIncreasingLift` is the case of degree `+1`.  The file used to say that
Mathlib has no lifting theorem for circle maps.  It does:
`Circle.isCoveringMap_exp` says `Circle.exp` is a covering map, and `ℝ` is
simply connected and locally path connected, so
`IsCoveringMap.existsUnique_continuousMap_lifts` produces a *continuous* lift in
one line (`exists_continuous_lift`).

What is left is the elementary degree argument, and it is the reason the
dichotomy is stated here rather than assumed.  The lift shifts by an integer
multiple of `2π` over a period (`exists_deg`); that integer does not depend on
the base point, because a continuous function with all values in `2πℤ` cannot
take two of them without taking `2π m + π` in between (`deg_unique`); it is
nonzero, because a periodic lift would take some value twice inside a single
window, where `φ` is injective (`deg_ne_zero`); a nonzero degree makes the lift
injective on `ℝ`, hence strictly monotone (`injective_lift`,
`strictMono_or_strictAnti`); and the degree is then `±1`, because a degree of
`2` or more would make the lift take the value `h 0 + 2π` strictly inside
`(0, 2π)` (`deg_eq_one`).

With that, **Lemma 3 needs no orientation hypothesis in its nondegenerate
form**: `norm_fourier_ne` says the two Fourier integrals of any homeomorphism of
`S¹` have different moduli.  Which of them is larger is the orientation — the
increasing case is `det_pos` and the decreasing case is `det_neg`, obtained from
it by replacing the lift `h` with `-h`, which negates `ad - bc`. -/

namespace CircleLift

/-- Every continuous self-map of the circle lifts continuously through
`Circle.exp`.  `Circle.exp` is a covering map (`Circle.isCoveringMap_exp`) and
`ℝ` is simply connected and locally path connected, so the lifting criterion
applies. -/
theorem exists_continuous_lift (φ : Circle → Circle) (hφc : Continuous φ) :
    ∃ h : ℝ → ℝ, Continuous h ∧ ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t) := by
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (φ (Circle.exp 0))
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (⟨fun t : ℝ => φ (Circle.exp t), by fun_prop⟩ : C(ℝ, Circle)) 0 e₀ he₀
  exact ⟨F, F.continuous, fun t => congrFun hFlift t⟩

variable {φ : Circle → Circle} {h : ℝ → ℝ}

/-- Two points with the same lift value are the same point of the circle. -/
theorem eq_of_lift_eq (hφ : Function.Injective φ)
    (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t)) {t₁ t₂ : ℝ} (heq : h t₁ = h t₂) :
    ∃ m : ℤ, t₁ = t₂ + m * (2*Real.pi) := by
  rw [← Circle.exp_eq_exp]
  apply hφ
  rw [← hlift, ← hlift, heq]

/-- A lift is injective on every half-open window of length `2π`. -/
theorem injOn_lift (hφ : Function.Injective φ)
    (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t)) (a : ℝ) :
    Set.InjOn h (Set.Ico a (a + 2*Real.pi)) := by
  have hπ := Real.pi_pos
  intro t₁ h₁ t₂ h₂ heq
  obtain ⟨m, hm⟩ := eq_of_lift_eq hφ hlift heq
  rcases h₁ with ⟨h₁a, h₁b⟩
  rcases h₂ with ⟨h₂a, h₂b⟩
  have hm0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ (-1 : ℤ))
      nlinarith
    · have : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hgt
      nlinarith
  rw [hm0] at hm
  simpa using hm

/-- The lift shifts by an integer multiple of `2π` over a period. -/
theorem exists_deg (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t)) (t : ℝ) :
    ∃ m : ℤ, h (t + 2*Real.pi) = h t + m * (2*Real.pi) := by
  rw [← Circle.exp_eq_exp, hlift, hlift]
  congr 1
  rw [Circle.exp_eq_exp]
  exact ⟨1, by push_cast; ring⟩

/-- The degree does not depend on the base point: a continuous function whose
values all lie in `2πℤ` cannot take two of them, because the midpoint offset by
`π` would have to be in `2πℤ` too. -/
theorem deg_unique (hc : Continuous h)
    (hd : ∀ t : ℝ, ∃ m : ℤ, h (t + 2*Real.pi) = h t + m * (2*Real.pi))
    {t₁ t₂ : ℝ} {m₁ m₂ : ℤ}
    (h₁ : h (t₁ + 2*Real.pi) = h t₁ + m₁ * (2*Real.pi))
    (h₂ : h (t₂ + 2*Real.pi) = h t₂ + m₂ * (2*Real.pi)) : m₁ = m₂ := by
  have hπ := Real.pi_pos
  set g : ℝ → ℝ := fun t => h (t + 2*Real.pi) - h t with hgdef
  have hgc : Continuous g := by rw [hgdef]; fun_prop
  have hg₁ : g t₁ = m₁ * (2*Real.pi) := by rw [hgdef]; simp only; rw [h₁]; ring
  have hg₂ : g t₂ = m₂ * (2*Real.pi) := by rw [hgdef]; simp only; rw [h₂]; ring
  -- the key: `g` cannot skip over `m₁·2π + π`
  have key : ∀ (s₁ s₂ : ℝ) (n₁ n₂ : ℤ), g s₁ = n₁ * (2*Real.pi) → g s₂ = n₂ * (2*Real.pi) →
      n₁ < n₂ → False := by
    intro s₁ s₂ n₁ n₂ hs₁ hs₂ hlt
    have hn : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) := by exact_mod_cast hlt
    have hmem : g s₁ + Real.pi ∈ Set.uIcc (g s₁) (g s₂) := by
      refine Set.mem_uIcc.2 (Or.inl ⟨by linarith, ?_⟩)
      rw [hs₁, hs₂]
      nlinarith
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc (hgc.continuousOn (s := Set.uIcc s₁ s₂)) hmem
    obtain ⟨m, hm⟩ := hd t
    have hgt : g t = m * (2*Real.pi) := by rw [hgdef]; simp only; rw [hm]; ring
    rw [hgt, hs₁] at ht
    have : (2:ℝ) * (m : ℝ) = 2 * (n₁ : ℝ) + 1 := by
      have h2 : (m : ℝ) * (2*Real.pi) - (n₁ : ℝ) * (2*Real.pi) = Real.pi := by linarith
      have h3 : ((m : ℝ) - (n₁ : ℝ)) * (2*Real.pi) = Real.pi := by linarith [h2]
      have h4 : ((m : ℝ) - (n₁ : ℝ)) * 2 = 1 := by
        have := mul_right_cancel₀ (ne_of_gt hπ) (by linarith [h3] :
          (((m : ℝ) - (n₁ : ℝ)) * 2) * Real.pi = (1:ℝ) * Real.pi)
        exact this
      linarith
    have hz : (2*m : ℤ) = 2*n₁ + 1 := by exact_mod_cast this
    omega
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · exact absurd (key t₁ t₂ m₁ m₂ hg₁ hg₂ hlt) (by simp)
  · exact heq
  · exact absurd (key t₂ t₁ m₂ m₁ hg₂ hg₁ hgt) (by simp)

/-- A continuous injective real function on a closed interval is strictly
monotone one way or the other. -/
theorem strictMonoOn_or_antiOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b)) (hinj : Set.InjOn f (Set.Icc a b)) :
    StrictMonoOn f (Set.Icc a b) ∨ StrictAntiOn f (Set.Icc a b) := by
  rcases le_total (f a) (f b) with hle | hle
  · exact Or.inl (ContinuousOn.strictMonoOn_of_injOn_Icc hab hle hc hinj)
  · refine Or.inr ?_
    have hneg : StrictMonoOn (fun x => -f x) (Set.Icc a b) :=
      ContinuousOn.strictMonoOn_of_injOn_Icc hab (by simpa using hle) hc.neg
        (fun x hx y hy hxy => hinj hx hy (by simpa using hxy))
    intro x hx y hy hxy
    have := hneg hx hy hxy
    simpa using this

/-- Iterating the period relation. -/
theorem lift_per_int {d : ℤ} (hper : ∀ t, h (t + 2*Real.pi) = h t + d * (2*Real.pi)) :
    ∀ (t : ℝ) (k : ℤ), h (t + k * (2*Real.pi)) = h t + (k*d : ℤ) * (2*Real.pi) := by
  intro t k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have he : t + ((n:ℤ) + 1 : ℤ) * (2*Real.pi) = (t + ((n:ℤ) : ℝ) * (2*Real.pi)) + 2*Real.pi := by
        push_cast; ring
      rw [he, hper, ih]
      push_cast
      ring
  | pred n ih =>
      have he : (t + ((-(n:ℤ) - 1 : ℤ) : ℝ) * (2*Real.pi)) + 2*Real.pi
          = t + ((-(n:ℤ) : ℤ) : ℝ) * (2*Real.pi) := by push_cast; ring
      have h2 := hper (t + ((-(n:ℤ) - 1 : ℤ) : ℝ) * (2*Real.pi))
      rw [he, ih] at h2
      have : h (t + ((-(n:ℤ) - 1 : ℤ) : ℝ) * (2*Real.pi))
          = h t + ((-(n:ℤ) : ℤ) * d : ℤ) * (2*Real.pi) - d * (2*Real.pi) := by linarith
      rw [this]
      push_cast
      ring

/-- **The degree is nonzero.**  If it were `0` the lift would be `2π`-periodic,
and then a value strictly between `h 0` and `h π` would be attained once on
`(0, π)` and again on `(π, 2π)` — two distinct points of the window on which the
lift is injective. -/
theorem deg_ne_zero (hφ : Function.Injective φ) (hc : Continuous h)
    (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t))
    {d : ℤ} (hper : ∀ t, h (t + 2*Real.pi) = h t + d * (2*Real.pi)) : d ≠ 0 := by
  have hπ := Real.pi_pos
  intro hd0
  subst hd0
  have hinj := injOn_lift hφ hlift 0
  rw [zero_add] at hinj
  have hper0 : h (2*Real.pi) = h 0 := by
    have := hper 0
    simpa using this
  have h0mem : (0:ℝ) ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨le_rfl, by linarith⟩
  have hpimem : Real.pi ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨by linarith, by linarith⟩
  have hne : h 0 ≠ h Real.pi := fun hcon => by
    have := hinj h0mem hpimem hcon
    linarith
  set v : ℝ := (h 0 + h Real.pi)/2 with hv
  have hv0 : v ≠ h 0 := by rw [hv]; intro hcon; apply hne; linarith
  have hvpi : v ≠ h Real.pi := by rw [hv]; intro hcon; apply hne; linarith
  -- a preimage in (0, π)
  have hm1 : v ∈ Set.uIcc (h 0) (h Real.pi) := by
    rw [hv]
    rcases le_total (h 0) (h Real.pi) with hle | hle
    · exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
    · exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨t₁, ht₁mem, ht₁⟩ := intermediate_value_uIcc (hc.continuousOn (s := Set.uIcc 0 Real.pi)) hm1
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ Real.pi)] at ht₁mem
  -- a preimage in (π, 2π)
  have hm2 : v ∈ Set.uIcc (h Real.pi) (h (2*Real.pi)) := by
    rw [hper0, hv]
    rcases le_total (h 0) (h Real.pi) with hle | hle
    · exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
  obtain ⟨t₂, ht₂mem, ht₂⟩ :=
    intermediate_value_uIcc (hc.continuousOn (s := Set.uIcc Real.pi (2*Real.pi))) hm2
  rw [Set.uIcc_of_le (by linarith : Real.pi ≤ 2*Real.pi)] at ht₂mem
  -- they are distinct points of `Ico 0 (2π)`
  have ht₁lt : t₁ < Real.pi := by
    rcases lt_or_eq_of_le ht₁mem.2 with hlt | heq
    · exact hlt
    · exfalso
      apply hvpi
      rw [← heq, ht₁]
  have ht₂gt : Real.pi < t₂ := by
    rcases lt_or_eq_of_le ht₂mem.1 with hlt | heq
    · exact hlt
    · exfalso
      apply hvpi
      rw [heq, ht₂]
  have ht₂lt : t₂ < 2*Real.pi := by
    rcases lt_or_eq_of_le ht₂mem.2 with hlt | heq
    · exact hlt
    · exfalso
      rw [heq, hper0] at ht₂
      exact hv0 ht₂.symm
  have := hinj ⟨ht₁mem.1, by linarith⟩ ⟨by linarith, ht₂lt⟩ (by rw [ht₁, ht₂])
  linarith

/-- With a nonzero degree the lift is injective on all of `ℝ`. -/
theorem injective_lift (hφ : Function.Injective φ)
    (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t))
    {d : ℤ} (hd0 : d ≠ 0) (hper : ∀ t, h (t + 2*Real.pi) = h t + d * (2*Real.pi)) :
    Function.Injective h := by
  have hπ := Real.pi_pos
  intro t₁ t₂ heq
  obtain ⟨m, hm⟩ := eq_of_lift_eq hφ hlift heq
  have hk := lift_per_int hper t₂ m
  rw [← hm, heq] at hk
  have hmd : ((m*d : ℤ) : ℝ) * (2*Real.pi) = 0 := by linarith
  have : (m*d : ℤ) = 0 := by
    have h2 : ((m*d : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.1 hmd with h' | h'
      · exact h'
      · linarith
    exact_mod_cast h2
  have hm0 : m = 0 := by
    rcases Int.mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' hd0
  rw [hm0] at hm
  simpa using hm

/-- A continuous injective real function is strictly monotone one way or the
other. -/
theorem strictMono_or_strictAnti (hc : Continuous h) (hinj : Function.Injective h) :
    StrictMono h ∨ StrictAnti h := by
  have hgen : ∀ a b : ℝ, a ≤ b →
      StrictMonoOn h (Set.Icc a b) ∨ StrictAntiOn h (Set.Icc a b) :=
    fun a b hab => strictMonoOn_or_antiOn_Icc hab hc.continuousOn (hinj.injOn)
  have h01 : h 0 ≠ h 1 := fun hcon => by simpa using hinj hcon
  rcases lt_or_gt_of_ne h01 with hlt | hgt
  · refine Or.inl (fun x y hxy => ?_)
    set a : ℝ := min 0 x with ha
    set b : ℝ := max 1 y with hb
    have hab : a ≤ b := le_trans (min_le_left 0 x) (le_trans zero_le_one (le_max_left 1 y))
    have h0 : (0:ℝ) ∈ Set.Icc a b := ⟨min_le_left 0 x, le_trans zero_le_one (le_max_left 1 y)⟩
    have h1 : (1:ℝ) ∈ Set.Icc a b := ⟨le_trans (min_le_left 0 x) zero_le_one, le_max_left 1 y⟩
    have hx : x ∈ Set.Icc a b := ⟨min_le_right 0 x, le_trans hxy.le (le_max_right 1 y)⟩
    have hy : y ∈ Set.Icc a b := ⟨le_trans (min_le_right 0 x) hxy.le, le_max_right 1 y⟩
    rcases hgen a b hab with hm | hanti
    · exact hm hx hy hxy
    · exact absurd (hanti h0 h1 zero_lt_one) (by linarith)
  · refine Or.inr (fun x y hxy => ?_)
    set a : ℝ := min 0 x with ha
    set b : ℝ := max 1 y with hb
    have hab : a ≤ b := le_trans (min_le_left 0 x) (le_trans zero_le_one (le_max_left 1 y))
    have h0 : (0:ℝ) ∈ Set.Icc a b := ⟨min_le_left 0 x, le_trans zero_le_one (le_max_left 1 y)⟩
    have h1 : (1:ℝ) ∈ Set.Icc a b := ⟨le_trans (min_le_left 0 x) zero_le_one, le_max_left 1 y⟩
    have hx : x ∈ Set.Icc a b := ⟨min_le_right 0 x, le_trans hxy.le (le_max_right 1 y)⟩
    have hy : y ∈ Set.Icc a b := ⟨le_trans (min_le_right 0 x) hxy.le, le_max_right 1 y⟩
    rcases hgen a b hab with hm | hanti
    · exact absurd (hm h0 h1 zero_lt_one) (by linarith)
    · exact hanti hx hy hxy

/-- **The degree of an increasing lift is `1`.**  It is at least `1` by
monotonicity; if it were at least `2` the lift would take the value
`h 0 + 2π` somewhere strictly inside `(0, 2π)`, and that point would have the
same image as `0`. -/
theorem deg_eq_one (hφ : Function.Injective φ)
    (hlift : ∀ t : ℝ, Circle.exp (h t) = φ (Circle.exp t)) (hc : Continuous h)
    (hmono : StrictMono h) {d : ℤ} (hper : ∀ t, h (t + 2*Real.pi) = h t + d * (2*Real.pi)) :
    d = 1 := by
  have hπ := Real.pi_pos
  have hval : h (2*Real.pi) = h 0 + d * (2*Real.pi) := by
    have := hper 0
    simpa using this
  have hpos : h 0 < h (2*Real.pi) := hmono (by linarith)
  have hd1 : 1 ≤ d := by
    by_contra hcon
    have : d ≤ 0 := by omega
    have : (d : ℝ) ≤ 0 := by exact_mod_cast this
    nlinarith
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hd2' : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hmem : h 0 + 2*Real.pi ∈ Set.Icc (h 0) (h (2*Real.pi)) := by
    refine ⟨by linarith, ?_⟩
    rw [hval]
    nlinarith
  obtain ⟨t, htmem, ht⟩ :=
    intermediate_value_Icc (by linarith : (0:ℝ) ≤ 2*Real.pi) hc.continuousOn hmem
  have ht0 : 0 < t := by
    rcases lt_or_eq_of_le htmem.1 with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at ht; linarith
  have ht2 : t < 2*Real.pi := by
    rcases lt_or_eq_of_le htmem.2 with hlt | heq
    · exact hlt
    · exfalso; rw [heq, hval] at ht; nlinarith
  -- `t` and `0` have the same image under φ
  have hexp : Circle.exp (h t) = Circle.exp (h 0) := by
    rw [ht, Circle.exp_eq_exp]
    exact ⟨1, by push_cast; ring⟩
  rw [hlift, hlift] at hexp
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 (hφ hexp)
  rw [zero_add] at hm
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ (-1 : ℤ))
    nlinarith
  · rw [heq] at hm; simp at hm; linarith
  · have : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hgt
    nlinarith

/-- **The lift dichotomy.**  Every homeomorphism of `S¹` has a strictly
monotone lift of degree `±1`.  This is Mathlib's covering-space lifting
criterion (`Circle.isCoveringMap_exp`, `ℝ` simply connected and locally path
connected) plus the elementary degree argument. -/
theorem exists_strictMono_lift (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    ∃ h : ℝ → ℝ,
      ((StrictMono h ∧ ∀ t, h (t + 2*Real.pi) = h t + 2*Real.pi) ∨
       (StrictAnti h ∧ ∀ t, h (t + 2*Real.pi) = h t - 2*Real.pi)) ∧
      ∀ t : ℝ, ((φ (Circle.exp t) : Circle) : ℂ) = Complex.exp (h t * Complex.I) := by
  obtain ⟨h, hc, hlift⟩ := exists_continuous_lift φ hφc
  have hcoe : ∀ t : ℝ, ((φ (Circle.exp t) : Circle) : ℂ) = Complex.exp (h t * Complex.I) := by
    intro t
    rw [← hlift, Circle.coe_exp]
  -- a single degree
  obtain ⟨d, hd0⟩ := exists_deg hlift 0
  have hper : ∀ t : ℝ, h (t + 2*Real.pi) = h t + d * (2*Real.pi) := by
    intro t
    obtain ⟨m, hm⟩ := exists_deg hlift t
    rw [deg_unique hc (exists_deg hlift) hm hd0] at hm
    exact hm
  have hdne : d ≠ 0 := deg_ne_zero hφ.1 hc hlift hper
  have hinj : Function.Injective h := injective_lift hφ.1 hlift hdne hper
  rcases strictMono_or_strictAnti hc hinj with hmono | hanti
  · refine ⟨h, Or.inl ⟨hmono, ?_⟩, hcoe⟩
    have := deg_eq_one hφ.1 hlift hc hmono hper
    subst this
    intro t
    have := hper t
    simpa using this
  · -- apply the increasing case to `ζ ↦ (φ ζ)⁻¹`, whose lift is `-h`
    set ψ : Circle → Circle := fun ζ => (φ ζ)⁻¹ with hψ
    have hψinj : Function.Injective ψ := by
      intro a b hab
      exact hφ.1 (by simpa [hψ] using hab)
    have hψlift : ∀ t : ℝ, Circle.exp ((-h) t) = ψ (Circle.exp t) := by
      intro t
      rw [hψ]
      simp only [Pi.neg_apply, Circle.exp_neg, hlift]
    have hnegmono : StrictMono (-h) := fun x y hxy => by
      simpa using hanti hxy
    have hnegper : ∀ t, (-h) (t + 2*Real.pi) = (-h) t + ((-d : ℤ) : ℝ) * (2*Real.pi) := by
      intro t
      simp only [Pi.neg_apply]
      rw [hper t]
      push_cast
      ring
    have hd1 := deg_eq_one hψinj hψlift hc.neg hnegmono hnegper
    have hdm : d = -1 := by omega
    refine ⟨h, Or.inr ⟨hanti, ?_⟩, hcoe⟩
    intro t
    rw [hper t, hdm]
    push_cast
    ring

/-! ### Lemma 3 for either orientation -/

open Lemma3 in
theorem aa_neg (f : ℝ → ℝ) : aa (-f) = - aa f := by
  rw [aa, aa, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [Pi.neg_apply, Real.sin_neg]
  ring

open Lemma3 in
theorem bb_neg (f : ℝ → ℝ) : bb (-f) = bb f := by
  rw [bb, bb]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [Pi.neg_apply, Real.cos_neg]

open Lemma3 in
theorem cc_neg (f : ℝ → ℝ) : cc (-f) = - cc f := by
  rw [cc, cc, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [Pi.neg_apply, Real.sin_neg]
  ring

open Lemma3 in
theorem dd_neg (f : ℝ → ℝ) : dd (-f) = dd f := by
  rw [dd, dd]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [Pi.neg_apply, Real.cos_neg]

open Lemma3 in
/-- The determinant is *negative* for a decreasing lift: `-h` is increasing and
`det (-h) = -det h`. -/
theorem det_neg {f : ℝ → ℝ} (hanti : StrictAnti f)
    (hper : ∀ t, f (t + 2*Real.pi) = f t - 2*Real.pi) :
    aa f * dd f - bb f * cc f < 0 := by
  have hmono : StrictMono (-f) := fun x y hxy => by simpa using hanti hxy
  have hper' : ∀ t, (-f) (t + 2*Real.pi) = (-f) t + 2*Real.pi := by
    intro t
    simp only [Pi.neg_apply]
    rw [hper t]
    ring
  have hpos := det_pos hmono hper'
  rw [aa_neg, bb_neg, cc_neg, dd_neg] at hpos
  nlinarith

open Lemma3 in
/-- **Lemma 3 without an orientation hypothesis**, in the nondegenerate form:
for *every* homeomorphism of `S¹` the two Fourier integrals have different
moduli.  Which one is larger is the orientation. -/
theorem norm_fourier_ne (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    ‖∫ θ in (0:ℝ)..(2*Real.pi),
        ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖
      ≠ ‖∫ θ in (0:ℝ)..(2*Real.pi),
        ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖ := by
  obtain ⟨f, hmon, hcoe⟩ := exists_strictMono_lift φ hφ hφc
  have hmeas : Measurable f := by
    rcases hmon with ⟨hm, -⟩ | ⟨ha, -⟩
    · exact hm.monotone.measurable
    · exact ha.antitone.measurable
  have hrw : ∀ m : ℤ, (∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-((m:ℤ):ℂ) * (θ:ℂ) * Complex.I))
      = ∫ θ in (0:ℝ)..(2*Real.pi),
        Complex.exp ((f θ : ℂ) * Complex.I) * Complex.exp (-((m:ℤ):ℂ) * (θ:ℂ) * Complex.I) := by
    intro m
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hcoe θ]
  have e1 : ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2
      = (dd f + aa f)^2 + (cc f - bb f)^2 := by
    rw [hrw 1, integral_exp_h_mul hmeas 1, int_cos_one hmeas, int_sin_one hmeas,
      norm_sq_ofReal_add]
  have e2 : ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2
      = (dd f - aa f)^2 + (cc f + bb f)^2 := by
    rw [hrw (-1), integral_exp_h_mul hmeas (-1), int_cos_negone hmeas, int_sin_negone hmeas,
      norm_sq_ofReal_add]
  intro hcon
  have hsq : (dd f + aa f)^2 + (cc f - bb f)^2 = (dd f - aa f)^2 + (cc f + bb f)^2 := by
    rw [← e1, ← e2, hcon]
  have hdet : aa f * dd f - bb f * cc f = 0 := by nlinarith [hsq]
  rcases hmon with ⟨hm, hp⟩ | ⟨ha, hp⟩
  · have := det_pos hm hp
    linarith
  · have := det_neg ha hp
    linarith


/-! ### Orientation: the Möbius lift

The dichotomy above does not say which side of it a given `φ` falls on, and
`exists_implicit_fderiv_z_of_orient` needs exactly that for the *normalized*
map `χ = ψ_g ∘ φ ∘ ψ_k`: that `χ` inherits `φ`'s orientation.  Since
`HasIncreasingLift` is stable under composition (`hasIncreasingLift_comp` —
compose the lifts), what has to be shown is that the two Möbius factors
themselves have increasing lifts, and for that a lift has to be *written down*.

It is the Poisson kernel in disguise.  For real `r` with `|r| < 1`,

    (e^{it} - r)/(1 - r e^{it}) = e^{it} · conj(1 - r e^{it})/(1 - r e^{it}),

and writing `1 - r e^{it} = D(1 - iu)` with `D = 1 - r cos t > 0` and
`u = r sin t/D` turns the second factor into `(1 + iu)/(1 - iu) = e^{2i arctan u}`.
So `mobLift r t = t + 2 arctan(r sin t/(1 - r cos t))` is a lift
(`exp_mobLift`), its derivative is

    (1 - r²)/(1 - 2r cos t + r²) > 0

(`hasDerivAt_mobLift`), and `2π`-periodicity of `sin` and `cos` gives
`mobLift r (t + 2π) = mobLift r t + 2π`.  A general element of `G₊` is
`ζ ↦ λ(ζ - a)/(1 - āζ)`; writing `λ = e^{iθ₀}` and `a = r e^{iα}` factors it as
a rotation, `g_r`, and a rotation, so its lift is
`t ↦ θ₀ + α + mobLift r (t - α)` (`hasIncreasingLift_of_isDiskAutPlus`).

With that, `norm_fourier_lt` is Lemma 3 with its sign, in the form the
normalized map needs. -/

/-- The lift of `z ↦ (z - r)/(1 - r z)` for real `r`. -/
noncomputable def mobLift (r : ℝ) (t : ℝ) : ℝ :=
  t + 2 * Real.arctan (r * Real.sin t / (1 - r * Real.cos t))

/-- `|1 - r e^{it}|` has positive real part when `|r| < 1`. -/
theorem mob_denom_pos {r : ℝ} (hr : |r| < 1) (t : ℝ) : 0 < 1 - r * Real.cos t := by
  have h1 : |r * Real.cos t| ≤ |r| := by
    rw [abs_mul]
    calc |r| * |Real.cos t| ≤ |r| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg r)
      _ = |r| := mul_one _
  have := (abs_le.1 h1).1
  linarith [h1.trans_lt hr, (abs_le.1 h1).2]

/-- `|1 - r e^{it}|² = 1 - 2r cos t + r²`, the denominator of the Poisson
kernel, is positive: it is at least `(1 - |r|)²`. -/
theorem mob_quad_pos {r : ℝ} (hr : |r| < 1) (t : ℝ) : 0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  have h1 : 0 < 1 - r * Real.cos t := mob_denom_pos hr t
  nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (r * Real.sin t)]

theorem sq_lt_one_of_abs_lt_one {r : ℝ} (hr : |r| < 1) : r ^ 2 < 1 := by
  nlinarith [abs_nonneg r, sq_abs r]

/-- `e^{ix} = cos x + i sin x`, with the real `cos` and `sin`. -/
theorem exp_real_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `e^{ix}` is unimodular, in the form the factorizations below use. -/
theorem exp_mul_star_self (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I))
      = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem one_add_ofReal_mul_I_ne_zero (u : ℝ) : (1 : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_sub_ofReal_mul_I_ne_zero (u : ℝ) : (1 : ℂ) - (u : ℂ) * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

set_option maxHeartbeats 1000000 in
/-- `t + 2 arctan(r sin t/(1 - r cos t))` is a lift of `ζ ↦ (ζ - r)/(1 - rζ)`. -/
theorem exp_mobLift {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    Complex.exp (((mobLift r t : ℝ) : ℂ) * Complex.I)
        * ((1 : ℂ) - (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
      = Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ) := by
  set E : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hEdef
  set D : ℝ := 1 - r * Real.cos t with hDdef
  have hD : 0 < D := mob_denom_pos hr t
  set u : ℝ := r * Real.sin t / D with hudef
  have huD : u * D = r * Real.sin t := div_mul_cancel₀ _ hD.ne'
  have hDc : ((D : ℝ) : ℂ) = 1 - (r : ℂ) * ((Real.cos t : ℝ) : ℂ) := by
    rw [hDdef]; push_cast; ring
  have huDc : ((u : ℝ) : ℂ) * ((D : ℝ) : ℂ) = (r : ℂ) * ((Real.sin t : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) huD
  have hE : E = ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I :=
    exp_real_mul_I t
  have hEbar : (starRingEnd ℂ) E = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I := by
    rw [hE]; simp [Complex.ext_iff]
  -- the two factorizations
  have hden : (1 : ℂ) - (r : ℂ) * E = ((D : ℝ) : ℂ) * (1 - ((u : ℝ) : ℂ) * Complex.I) := by
    rw [hE]
    linear_combination (-1 : ℂ) * hDc + Complex.I * huDc
  have hconj : (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) E
      = ((D : ℝ) : ℂ) * (1 + ((u : ℝ) : ℂ) * Complex.I) := by
    rw [hEbar]
    linear_combination (-1 : ℂ) * hDc - Complex.I * huDc
  have hnum : E - (r : ℂ) = E * (((D : ℝ) : ℂ) * (1 + ((u : ℝ) : ℂ) * Complex.I)) := by
    rw [← hconj]
    linear_combination (r : ℂ) * exp_mul_star_self t
  -- the exponential of the lift
  set S : ℝ := Real.sqrt (1 + u ^ 2) with hSdef
  have hS2 : S ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  have hSpos : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hA : Complex.exp (((Real.arctan u : ℝ) : ℂ) * Complex.I)
      = ((1 : ℂ) + ((u : ℝ) : ℂ) * Complex.I) / ((S : ℝ) : ℂ) := by
    rw [exp_real_mul_I, Real.cos_arctan, Real.sin_arctan, ← hSdef]
    have : ((S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'
    push_cast
    field_simp
  have hexp : Complex.exp (((mobLift r t : ℝ) : ℂ) * Complex.I)
      = E * (((1 : ℂ) + ((u : ℝ) : ℂ) * Complex.I) ^ 2 / ((1 : ℂ) + ((u : ℝ) : ℂ) ^ 2)) := by
    have hsplit : ((mobLift r t : ℝ) : ℂ) * Complex.I
        = (t : ℂ) * Complex.I + (((Real.arctan u : ℝ) : ℂ) * Complex.I
            + ((Real.arctan u : ℝ) : ℂ) * Complex.I) := by
      rw [mobLift, ← hudef]; push_cast; ring
    have hS2c : ((S : ℝ) : ℂ) ^ 2 = (1 : ℂ) + ((u : ℝ) : ℂ) ^ 2 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hS2
    rw [hsplit, Complex.exp_add, Complex.exp_add, hA, ← hEdef, ← hS2c]
    ring
  -- put it together
  rw [hexp, hden, hnum]
  have hfac : (1 : ℂ) + ((u : ℝ) : ℂ) ^ 2
      = (1 + ((u : ℝ) : ℂ) * Complex.I) * (1 - ((u : ℝ) : ℂ) * Complex.I) := by
    linear_combination (((u : ℝ) : ℂ) ^ 2) * Complex.I_mul_I
  rw [hfac]
  have h1 := one_add_ofReal_mul_I_ne_zero u
  have h2 := one_sub_ofReal_mul_I_ne_zero u
  field_simp

/-- `h'(t) = (1 - r²)/(1 - 2r cos t + r²)`, the Poisson kernel. -/
theorem hasDerivAt_mobLift {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    HasDerivAt (mobLift r) ((1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)) t := by
  have hD : (0:ℝ) < 1 - r * Real.cos t := mob_denom_pos hr t
  have hQ : (0:ℝ) < 1 - 2 * r * Real.cos t + r ^ 2 := mob_quad_pos hr t
  have hd : HasDerivAt (fun s : ℝ => 1 - r * Real.cos s) (r * Real.sin t) t := by
    have h := (HasDerivAt.const_mul r (Real.hasDerivAt_cos t)).const_sub (1:ℝ)
    simpa using h
  have hn : HasDerivAt (fun s : ℝ => r * Real.sin s) (r * Real.cos t) t :=
    HasDerivAt.const_mul r (Real.hasDerivAt_sin t)
  have hq := hn.div hd hD.ne'
  have harc := (Real.hasDerivAt_arctan (r * Real.sin t / (1 - r * Real.cos t))).comp t hq
  have hfin : HasDerivAt (mobLift r)
      (1 + 2 * (1 / (1 + (r * Real.sin t / (1 - r * Real.cos t)) ^ 2)
        * ((r * Real.cos t * (1 - r * Real.cos t) - r * Real.sin t * (r * Real.sin t))
            / (1 - r * Real.cos t) ^ 2))) t :=
    (hasDerivAt_id t).add (HasDerivAt.const_mul 2 harc)
  refine hfin.congr_deriv ?_
  have h1q : 1 + (r * Real.sin t / (1 - r * Real.cos t)) ^ 2
      = (1 - 2 * r * Real.cos t + r ^ 2) / (1 - r * Real.cos t) ^ 2 := by
    field_simp
    linear_combination (r ^ 2) * Real.sin_sq_add_cos_sq t
  have h2 : r * Real.cos t * (1 - r * Real.cos t) - r * Real.sin t * (r * Real.sin t)
      = r * Real.cos t - r ^ 2 := by
    linear_combination (-(r ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [h1q, h2]
  field_simp
  ring

/-- The lift increases — which is to say that `ζ ↦ (ζ - r)/(1 - rζ)` preserves
orientation.  The derivative is the Poisson kernel, so this is where `|r| < 1`
is spent. -/
theorem strictMono_mobLift {r : ℝ} (hr : |r| < 1) : StrictMono (mobLift r) :=
  strictMono_of_deriv_pos fun t => by
    rw [(hasDerivAt_mobLift hr t).deriv]
    exact div_pos (by linarith [sq_lt_one_of_abs_lt_one hr]) (mob_quad_pos hr t)

/-- The lift has degree `+1`: `sin` and `cos` are `2π`-periodic, so only the
linear term moves. -/
theorem mobLift_add_two_pi (r t : ℝ) :
    mobLift r (t + 2 * Real.pi) = mobLift r t + 2 * Real.pi := by
  simp only [mobLift, Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

/-! ### Orientation is inherited -/

/-- Orientation is preserved by composition: compose the lifts. -/
theorem hasIncreasingLift_comp {φ ψ : Circle → Circle}
    (hφ : HasIncreasingLift φ) (hψ : HasIncreasingLift ψ) :
    HasIncreasingLift (φ ∘ ψ) := by
  obtain ⟨f, hfm, hfp, hfl⟩ := hφ
  obtain ⟨k, hkm, hkp, hkl⟩ := hψ
  refine ⟨f ∘ k, hfm.comp hkm, fun t => ?_, fun t => ?_⟩
  · simp only [Function.comp_apply, hkp t, hfp (k t)]
  · have hcirc : ψ (Circle.exp t) = Circle.exp (k t) := by
      apply Subtype.ext
      rw [hkl t, Circle.coe_exp]
    simp only [Function.comp_apply, hcirc, hfl (k t)]

set_option maxHeartbeats 1000000 in
/-- **An element of `G₊` induces an orientation-preserving map of `S¹`.** -/
theorem hasIncreasingLift_of_isDiskAutPlus {g : ℂ → ℂ} (hgp : IsDiskAutPlus g)
    (ψ : Circle → Circle) (hψ : ∀ ζ : Circle, ((ψ ζ : Circle) : ℂ) = g (ζ : ℂ)) :
    HasIncreasingLift ψ := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hgp
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) = lam := by
    obtain ⟨e, he⟩ := Circle.exp_surjective (⟨lam, mem_sphere_zero_iff_norm.2 hlam⟩ : Circle)
    exact ⟨e, by rw [← Circle.coe_exp, he]⟩
  set α : ℝ := Complex.arg a with hαdef
  set r : ℝ := ‖a‖ with hrdef
  have hra : ((r : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I) = a :=
    Complex.norm_mul_exp_arg_mul_I a
  have hrabs : |r| < 1 := by rw [hrdef, abs_of_nonneg (norm_nonneg a)]; exact ha
  refine ⟨fun t => θ₀ + α + mobLift r (t - α), ?_, ?_, ?_⟩
  · intro x y hxy
    have := strictMono_mobLift hrabs (show x - α < y - α by linarith)
    linarith
  · intro t
    show θ₀ + α + mobLift r (t + 2 * Real.pi - α)
      = θ₀ + α + mobLift r (t - α) + 2 * Real.pi
    rw [show t + 2 * Real.pi - α = (t - α) + 2 * Real.pi from by ring, mobLift_add_two_pi]
    ring
  · intro t
    set Λ : ℂ := Complex.exp ((α : ℂ) * Complex.I) with hΛ
    set F : ℂ := Complex.exp ((((t - α : ℝ)) : ℂ) * Complex.I) with hF
    have hΛc : Λ * (starRingEnd ℂ) Λ = 1 := exp_mul_star_self α
    have hE : Complex.exp ((t : ℂ) * Complex.I) = Λ * F := by
      rw [hΛ, hF, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hFnorm : ‖F‖ = 1 := by rw [hF]; exact Complex.norm_exp_ofReal_mul_I _
    have hrF : ‖(r : ℂ) * F‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hFnorm, mul_one]
      exact hrabs
    have hne : (1 : ℂ) - (r : ℂ) * F ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h] at hrF
      simp at hrF
    have hstar : star a = ((r : ℝ) : ℂ) * (starRingEnd ℂ) Λ := by
      rw [← hra]
      simp
    have hdenom : (1 : ℂ) - star a * Complex.exp ((t : ℂ) * Complex.I) = 1 - (r : ℂ) * F := by
      rw [hstar, hE]
      linear_combination (-((r : ℝ) : ℂ) * F) * hΛc
    have hnumer : Complex.exp ((t : ℂ) * Complex.I) - a = Λ * (F - (r : ℂ)) := by
      rw [hE, ← hra]
      ring
    have hkey := exp_mobLift hrabs (t - α)
    rw [← hF] at hkey
    rw [hψ (Circle.exp t), Circle.coe_exp, hform, diskAut, hdenom, hnumer]
    have hsplit : (((θ₀ + α + mobLift r (t - α) : ℝ)) : ℂ) * Complex.I
        = (θ₀ : ℂ) * Complex.I + ((α : ℂ) * Complex.I
            + (((mobLift r (t - α) : ℝ)) : ℂ) * Complex.I) := by
      push_cast; ring
    have hXval : Complex.exp ((((mobLift r (t - α) : ℝ)) : ℂ) * Complex.I)
        = (F - (r : ℂ)) / (1 - (r : ℂ) * F) := by
      rw [eq_div_iff hne]; exact hkey
    rw [hsplit, Complex.exp_add, Complex.exp_add, hθ₀, ← hΛ, hXval]
    ring

/-! ### Lemma 3 with a sign -/

open Lemma3 in
/-- **Lemma 3 with its sign**, in the form `exists_implicit_fderiv_z_of_orient`
consumes: for an orientation-preserving homeomorphism the `e^{-iθ}` pairing
dominates the `e^{iθ}` one.  This is `norm_fourier_ne` with `det_pos` used
instead of the dichotomy, and it needs no bijectivity — an increasing lift
already forces `φ` injective. -/
theorem norm_fourier_lt (φ : Circle → Circle) (hor : HasIncreasingLift φ) :
    ‖∫ θ in (0:ℝ)..(2*Real.pi),
        ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖
      < ‖∫ θ in (0:ℝ)..(2*Real.pi),
        ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖ := by
  obtain ⟨f, hm, hp, hcoe⟩ := hor
  have hmeas : Measurable f := hm.monotone.measurable
  have hrw : ∀ m : ℤ, (∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-((m:ℤ):ℂ) * (θ:ℂ) * Complex.I))
      = ∫ θ in (0:ℝ)..(2*Real.pi),
        Complex.exp ((f θ : ℂ) * Complex.I) * Complex.exp (-((m:ℤ):ℂ) * (θ:ℂ) * Complex.I) := by
    intro m
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hcoe θ]
  have e1 : ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2
      = (dd f + aa f)^2 + (cc f - bb f)^2 := by
    rw [hrw 1, integral_exp_h_mul hmeas 1, int_cos_one hmeas, int_sin_one hmeas,
      norm_sq_ofReal_add]
  have e2 : ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2
      = (dd f - aa f)^2 + (cc f + bb f)^2 := by
    rw [hrw (-1), integral_exp_h_mul hmeas (-1), int_cos_negone hmeas, int_sin_negone hmeas,
      norm_sq_ofReal_add]
  have hdet := det_pos hm hp
  have hsq : ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2
      < ‖∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)‖^2 := by
    rw [e1, e2]; nlinarith [hdet]
  nlinarith [hsq, norm_nonneg (∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I)),
    norm_nonneg (∫ θ in (0:ℝ)..(2*Real.pi),
      ((φ (Circle.exp θ) : Circle) : ℂ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I))]

/-! ### Orientation from three fixed points

The dichotomy plus the normalization `φ(1) = 1`, `φ(i) = i`, `φ(-1) = -1` decides
the orientation outright, with no reference to quasiconformality: the three
points are in positive cyclic order, and a decreasing lift reverses that order.
`hasIncreasingLift_of_fixes` is the argument, and it is what discharges
`HasIncreasingLift` for the boundary maps `φ^μ` of Sections 6 and 7, all of
which are normalized this way. -/

/-- Two real lifts of the same point of `S¹` differ by an integer multiple of
`2π`. -/
theorem sub_eq_int_mul_two_pi {x y : ℝ}
    (hxy : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) :
    ∃ n : ℤ, x = y + n * (2 * Real.pi) := by
  rw [Complex.exp_eq_exp_iff_exists_int] at hxy
  obtain ⟨n, hn⟩ := hxy
  refine ⟨n, ?_⟩
  have key : ((x : ℂ) - ((y : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)))) * Complex.I = 0 := by
    linear_combination hn
  rcases mul_eq_zero.1 key with h | h
  · have hc : (x : ℂ) = (y : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by linear_combination h
    exact_mod_cast hc
  · exact absurd h Complex.I_ne_zero

/-- **An orientation-reversing homeomorphism of `S¹` cannot fix `1`, `i` and
`-1`.**  So a homeomorphism that does fix them has an increasing lift.

The three points are in positive cyclic order, and a decreasing lift reverses
that order.  Concretely: normalize the lift so that `h 0 = 2πn`; then
`h (2π) = 2πn - 2π`, and `h` runs strictly down through that window.  Fixing
`i` pins `h (π/2)` to the one point of `π/2 + 2πℤ` inside it, namely
`2πn - 3π/2`; fixing `-1` then needs a point of `π + 2πℤ` in
`(2πn - 2π, 2πn - 3π/2)`, an interval of length `π/2` whose endpoints straddle
no such point. -/
theorem hasIncreasingLift_of_fixes (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (hfix1 : φ 1 = 1)
    (hfixI : φ (Circle.exp (Real.pi / 2)) = Circle.exp (Real.pi / 2))
    (hfixm : φ (Circle.exp Real.pi) = Circle.exp Real.pi) :
    HasIncreasingLift φ := by
  obtain ⟨h, hmon, hcoe⟩ := exists_strictMono_lift φ hφ hφc
  rcases hmon with ⟨hm, hp⟩ | ⟨ha, hp⟩
  · exact ⟨h, hm, hp, hcoe⟩
  exfalso
  have hπ := Real.pi_pos
  -- the three fixed points, read on the lift
  have e0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = Complex.exp ((h 0 : ℂ) * Complex.I) := by
    have := hcoe 0
    rw [Circle.exp_zero, hfix1] at this
    rw [← this]
    norm_num
  have e1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((h (Real.pi / 2) : ℂ) * Complex.I) := by
    have := hcoe (Real.pi / 2)
    rw [hfixI, Circle.coe_exp] at this
    exact this
  have e2 : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((h Real.pi : ℂ) * Complex.I) := by
    have := hcoe Real.pi
    rw [hfixm, Circle.coe_exp] at this
    exact this
  obtain ⟨n, hn⟩ := sub_eq_int_mul_two_pi e0.symm
  obtain ⟨b, hb⟩ := sub_eq_int_mul_two_pi e1.symm
  obtain ⟨c, hc⟩ := sub_eq_int_mul_two_pi e2.symm
  -- `hn : h 0 = 0 + n * (2π)`, `hb : h (π/2) = π/2 + b * (2π)`, `hc : h π = π + c * (2π)`
  have hper : h (2 * Real.pi) = h 0 - 2 * Real.pi := by
    have := hp 0
    rwa [zero_add] at this
  have d1 : h (Real.pi / 2) < h 0 := ha (by linarith)
  have d2 : h Real.pi < h (Real.pi / 2) := ha (by linarith)
  have d3 : h (2 * Real.pi) < h Real.pi := ha (by linarith)
  rw [hn] at hper d1
  rw [hb] at d1 d2
  rw [hc] at d2 d3
  rw [hper] at d3
  -- `b - n = -1`
  have hb1 : ((b : ℝ) - n) < 0 := by nlinarith
  have hb2 : (-2 : ℝ) < ((b : ℝ) - n) := by nlinarith
  have hbz : b - n = -1 := by
    have h1 : b - n < 0 := by exact_mod_cast (by push_cast; linarith : ((b - n : ℤ) : ℝ) < 0)
    have h2 : (-2 : ℤ) < b - n := by
      exact_mod_cast (by push_cast; linarith : (-2 : ℝ) < ((b - n : ℤ) : ℝ))
    omega
  have hbn : (b : ℝ) = (n : ℝ) - 1 := by
    have : ((b - n : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by rw [hbz]
    push_cast at this
    linarith
  rw [hbn] at d2
  -- `c - n ≤ -2` and `c - n ≥ -1`
  have hc1 : c - n ≤ -2 := by
    have : ((c - n : ℤ) : ℝ) < -1 := by push_cast; nlinarith
    have : c - n < -1 := by exact_mod_cast this
    omega
  have hc2 : -1 ≤ c - n := by
    have : (-2 : ℝ) < ((c - n : ℤ) : ℝ) := by push_cast; nlinarith
    have : (-2 : ℤ) < c - n := by exact_mod_cast this
    omega
  omega

end CircleLift

/-! ### Formula (3.2), and the `z`-derivative of (3.1)

This is §4.3 of the paper: the `z`-derivative of (3.1) at a point `(z, Φ(z))` is
Lemma 3 for the *normalized* boundary map, transported by conformal naturality.

The normalization is the pair of Möbius maps `g = g_{Φ(z)}` and `k = g_{-z}`,
which send `Φ(z) ↦ 0` and `0 ↦ z`; the normalized map is
`χ = ψ_g ∘ φ ∘ ψ_k`.  `baryFn_naturality` is the value identity behind
`baryEq_naturality_plus`, with the `w`-variable frozen at `Φ(z)` so that the
identity can be differentiated in the remaining variable:

    F(ξ, 0; χ) = c · F(k ξ, Φ(z); φ),   |c| = 1, `c` independent of `ξ`.

Differentiating at `ξ = 0` reads Lemma 3 off the left and `M` off the right.

On the left, `hasFDerivAt_bigPi_z_zero` is formula (3.2) at the origin.  At
`z = w = 0` the integrand of (3.1) collapses to `u`, and the only surviving
derivative comes from the Poisson denominator `(1 - z ῑ)(1 - z̄ ι)`, whose
inverse has derivative `-d` at the identity; so the `z`-derivative is
`v ↦ v·(u ῑ) + v̄·(u ι)` and, after `meanCLM`, `v ↦ c₁ v + c₋₁ v̄` with
`c±₁` the Fourier integrals of `χ`.

On the right, `k` is *holomorphic* and `k'(0) = 1 - |z|²` is a positive **real**
number.  That is what keeps the argument short: `M(κ v, 0) = κ·M(v, 0)` for real
`κ` by `ℝ`-linearity alone, so no Wirtinger chain rule is needed — the two
Wirtinger combinations of the composite are `cκ` times those of `M`, and `|cκ|`
cancels out of the comparison. -/

theorem continuous_diskAutToCircle (g : ℂ → ℂ) (hg : IsDiskAut g) :
    Continuous (diskAutToCircle g hg) :=
  continuous_induced_rng.2 (continuous_isDiskAut_circle g hg)

namespace ZDeriv

/-- `v ↦ v • g`, as a real-linear map `ℂ → C(S¹, ℂ)`. -/
def smulX (g : C(Circle, ℂ)) : ℂ →L[ℝ] C(Circle, ℂ) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight g

/-- `v ↦ v̄ • g`. -/
def smulBarX (g : C(Circle, ℂ)) : ℂ →L[ℝ] C(Circle, ℂ) :=
  ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).smulRight g

/-- At `z = w = 0` the integrand of (3.1) is just `u`. -/
theorem bigPi_zero_zero (u : C(Circle, ℂ)) : bigPi 0 0 u = u := by
  simp [bigPi]

theorem bigPi_zero_w (ξ : ℂ) (u : C(Circle, ℂ)) :
    bigPi ξ 0 u = ((1:ℂ) - ξ * star ξ) •
      (u * Ring.inverse (((1 : C(Circle, ℂ)) - ξ • iotaBarX)
        * ((1 : C(Circle, ℂ)) - (star ξ) • iotaX))) := by
  simp [bigPi]

/-- The `z`-derivative of `Π` at the origin: `v ↦ v·(u ῑ) + v̄·(u ι)`. -/
def bigPiDerivZ0 (u : C(Circle, ℂ)) : ℂ →L[ℝ] C(Circle, ℂ) :=
  smulX (u * iotaBarX) + smulBarX (u * iotaX)

set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_bigPi_z_zero (u : C(Circle, ℂ)) :
    HasFDerivAt (fun ξ : ℂ => bigPi ξ 0 u) (bigPiDerivZ0 u) 0 := by
  -- the scalar factor `1 - ξ ξ̄` has vanishing derivative at the origin
  have hsq : HasFDerivAt (fun ξ : ℂ => ξ * star ξ) (0 : ℂ →L[ℝ] ℂ) 0 := by
    have h1 : HasFDerivAt (fun ξ : ℂ => ξ) (ContinuousLinearMap.id ℝ ℂ) 0 := hasFDerivAt_id 0
    have h2 : HasFDerivAt (fun ξ : ℂ => star ξ)
        (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) 0 := by
      refine (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt
        (x := (0:ℂ))).congr_of_eventuallyEq ?_
      filter_upwards with ξ
      simp
    have h := h1.mul h2
    refine h.congr_fderiv ?_
    ext v
    simp
  have hc : HasFDerivAt (fun ξ : ℂ => (1:ℂ) - ξ * star ξ) (0 : ℂ →L[ℝ] ℂ) 0 := by
    have h := (hasFDerivAt_const (1:ℂ) (0:ℂ)).sub hsq
    have hfun : ((fun _ : ℂ => (1:ℂ)) - fun ξ : ℂ => ξ * star ξ)
        = fun ξ : ℂ => (1:ℂ) - ξ * star ξ := by funext ξ; simp
    rw [hfun] at h
    simpa using h
  -- the two affine factors
  have hA : HasFDerivAt (fun ξ : ℂ => (1 : C(Circle, ℂ)) - ξ • iotaBarX)
      (-(smulX iotaBarX)) 0 := by
    have h := (hasFDerivAt_const (1 : C(Circle, ℂ)) (0:ℂ)).sub
      ((smulX iotaBarX).hasFDerivAt (x := (0:ℂ)))
    have hfun : ((fun _ : ℂ => (1 : C(Circle, ℂ))) - ⇑(smulX iotaBarX))
        = fun ξ : ℂ => (1 : C(Circle, ℂ)) - ξ • iotaBarX := by
      funext ξ; simp [smulX]
    rw [hfun, zero_sub] at h
    exact h
  have hB : HasFDerivAt (fun ξ : ℂ => (1 : C(Circle, ℂ)) - (star ξ) • iotaX)
      (-(smulBarX iotaX)) 0 := by
    have h := (hasFDerivAt_const (1 : C(Circle, ℂ)) (0:ℂ)).sub
      ((smulBarX iotaX).hasFDerivAt (x := (0:ℂ)))
    have hfun : ((fun _ : ℂ => (1 : C(Circle, ℂ))) - ⇑(smulBarX iotaX))
        = fun ξ : ℂ => (1 : C(Circle, ℂ)) - (star ξ) • iotaX := by
      funext ξ; simp [smulBarX]
    rw [hfun, zero_sub] at h
    exact h
  have hS := hA.mul hB
  have hS0 : ((1 : C(Circle, ℂ)) - (0:ℂ) • iotaBarX)
      * ((1 : C(Circle, ℂ)) - (star (0:ℂ)) • iotaX) = 1 := by simp
  have hunit : IsUnit (((1 : C(Circle, ℂ)) - (0:ℂ) • iotaBarX)
      * ((1 : C(Circle, ℂ)) - (star (0:ℂ)) • iotaX)) := by rw [hS0]; exact isUnit_one
  have hpt := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  rw [hunit.unit_spec] at hpt
  have hinvval : (((hunit.unit)⁻¹ : C(Circle, ℂ)ˣ) : C(Circle, ℂ)) = 1 := by
    rw [← Ring.inverse_unit hunit.unit, hunit.unit_spec, hS0, Ring.inverse_one]
  rw [hinvval] at hpt
  have hinv := hpt.comp 0 hS
  have hmul := (hasFDerivAt_const u (0:ℂ)).mul hinv
  have hfin := hc.smul hmul
  simp only [bigPi_zero_w]
  refine hfin.congr_fderiv ?_
  ext v ζ
  simp only [bigPiDerivZ0, smulX, smulBarX, add_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, zero_apply, ContinuousLinearMap.coe_id',
    id_eq, ContinuousLinearMap.mulLeftRight_apply, ContinuousMap.smul_apply,
    ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.neg_apply, ContinuousMap.zero_apply, ContinuousMap.one_apply,
    smul_eq_mul, Complex.conjCLE_apply, Complex.star_def, map_zero,
    ContinuousLinearEquiv.coe_coe]
  ring

/-- **Formula (3.2) at the origin.**  The `z`-derivative of (3.1) at `(0,0)` is
`v ↦ c₁ v + c₋₁ v̄`, with `c₁ = ⨍ u(ζ) ζ̄` and `c₋₁ = ⨍ u(ζ) ζ`. -/
theorem hasFDerivAt_baryFnMap_z_zero (u : C(Circle, ℂ)) :
    HasFDerivAt (fun ξ : ℂ => baryFnMap ξ 0 u)
      ((meanCLM (u * iotaBarX)) • (ContinuousLinearMap.id ℝ ℂ)
        + (meanCLM (u * iotaX)) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) 0 := by
  have h0u : ‖(0:ℂ)‖ * ‖u‖ < 1 := by simp
  have heq : (fun ξ : ℂ => baryFnMap ξ 0 u) =ᶠ[nhds (0:ℂ)]
      fun ξ : ℂ => meanCLM (bigPi ξ 0 u) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show (0:ℂ) ∈ Metric.ball (0:ℂ) 1 by simp)] with ξ hξ
    exact (meanCLM_bigPi (by simpa using hξ) h0u).symm
  have hcomp := (meanCLM.hasFDerivAt (x := bigPi 0 0 u)).comp 0 (hasFDerivAt_bigPi_z_zero u)
  refine (hcomp.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, bigPiDerivZ0, smulX, smulBarX,
    add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_add, meanCLM_smul, smul_apply, smul_eq_mul]
  ring

theorem meanCLM_mul_iotaBar (u : C(Circle, ℂ)) :
    meanCLM (u * iotaBarX)
      = (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi),
          u (Circle.exp θ) * Complex.exp (-(((1:ℤ)):ℂ) * (θ:ℂ) * Complex.I) := by
  rw [meanCLM_apply]
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [ContinuousMap.mul_apply, iotaBarX, ContinuousMap.coe_mk]
  congr 1
  rw [Circle.coe_exp, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem meanCLM_mul_iota (u : C(Circle, ℂ)) :
    meanCLM (u * iotaX)
      = (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi),
          u (Circle.exp θ) * Complex.exp (-(((-1:ℤ)):ℂ) * (θ:ℂ) * Complex.I) := by
  rw [meanCLM_apply]
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [ContinuousMap.mul_apply, iotaX_apply]
  congr 1
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem baryFn_eq_harmonicMeasureAvg (φ : Circle → Circle) (z w : ℂ) :
    baryFn φ z w = harmonicMeasureAvg z (fun ζ => diskAut w ((φ ζ : ℂ))) := rfl

/-- **Quantitative conformal naturality of (3.1).**  This is the value identity
behind `baryEq_naturality_plus`, with the base point `w` left free so that it
can be differentiated in `ξ`.  The unimodular constant `c` comes from
`diskAut_apply_diskAut` and does not depend on `ξ`. -/
theorem baryFn_naturality (φ : Circle → Circle) (hφc : Continuous φ)
    (g k : ℂ → ℂ) (hg : IsDiskAutPlus g) (hk : IsDiskAut k) (ψg ψk : Circle → Circle)
    (hgb : ∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) (hkb : ∀ ζ : Circle, k (ζ : ℂ) = (ψk ζ : ℂ))
    (w : ℂ) (hw : ‖w‖ < 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ ξ : ℂ, ‖ξ‖ < 1 →
      baryFn (ψg ∘ φ ∘ ψk) ξ (g w) = c * baryFn φ (k ξ) w := by
  obtain ⟨lam, a, hlam, ha, hform⟩ := hg
  have hlam' : star lam * lam = 1 := star_mul_self_of_norm_one hlam
  refine ⟨lam * (((1:ℂ) - a * star w) / ((1:ℂ) - star a * w)), ?_, ?_⟩
  · have hden : (1 : ℂ) - star a * w ≠ 0 := diskAut_denom_ne_zero a w ha hw.le
    have hst : star ((1:ℂ) - a * star w) = (1:ℂ) - star a * w := by
      simp [star_sub, star_mul, mul_comm]
    have hn : ‖(1:ℂ) - a * star w‖ = ‖(1:ℂ) - star a * w‖ := by rw [← hst, norm_star]
    rw [norm_mul, hlam, one_mul, norm_div, hn, div_self]
    simpa using hden
  · intro ξ hξ
    rw [baryFn_eq_harmonicMeasureAvg, baryFn_eq_harmonicMeasureAvg]
    have hpt : (fun ζ : Circle => diskAut (g w) ((((ψg ∘ φ ∘ ψk) ζ : Circle) : ℂ)))
        = fun ζ : Circle =>
          (lam * (((1:ℂ) - a * star w) / ((1:ℂ) - star a * w))) * diskAut w ((φ (ψk ζ) : ℂ)) := by
      funext ζ
      have h1 : ((((ψg ∘ φ ∘ ψk) ζ : Circle)) : ℂ) = g ((φ (ψk ζ) : ℂ)) := (hgb _).symm
      rw [h1, hform w, hform ((φ (ψk ζ) : ℂ))]
      exact diskAut_apply_diskAut lam a w _ hlam' ha hw (le_of_eq (Circle.norm_coe _))
    rw [hpt, harmonicMeasureAvg_const_mul]
    congr 1
    have hcirc : ∀ ζ : Circle,
        (⟨k (ζ : ℂ), isDiskAut_maps_circle_to_circle k hk ζ⟩ : Circle) = ψk ζ :=
      fun ζ => Subtype.ext (hkb ζ)
    have hnat := harmonicMeasureAvg_naturality k hk ξ hξ
      (fun v : Circle => diskAut w ((φ v : ℂ))) (continuous_diskAut_comp w hw φ hφc)
    simp only [hcirc] at hnat
    exact hnat.symm

/-- `ξ ↦ g_{-z}(ξ)` sends `0` to `z`, and its derivative there is the *real*
number `1 - |z|²`. -/
theorem hasFDerivAt_diskAut_neg (z : ℂ) (hz : ‖z‖ < 1) :
    HasFDerivAt (fun ξ : ℂ => diskAut (-z) ξ)
      ((((1 - ‖z‖^2 : ℝ) : ℂ)) • (ContinuousLinearMap.id ℝ ℂ)) 0 := by
  have hden : ∀ ξ : ℂ, ‖ξ‖ < 1 → (1:ℂ) - star (-z) * ξ ≠ 0 := by
    intro ξ hξ
    simpa using diskAut_denom_ne_zero (-z) ξ (by simpa using hz) hξ.le
  have hN : HasDerivAt (fun ξ : ℂ => ξ - (-z)) 1 0 := (hasDerivAt_id (0:ℂ)).sub_const (-z)
  have hD : HasDerivAt (fun ξ : ℂ => (1:ℂ) - star (-z) * ξ) (-(star (-z))) 0 := by
    have h1 : HasDerivAt (fun ξ : ℂ => star (-z) * ξ) (star (-z)) 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).const_mul (star (-z))
    simpa using h1.const_sub (1:ℂ)
  have hD0 : (1:ℂ) - star (-z) * 0 ≠ 0 := by simp
  have hq := hN.div hD hD0
  have hval : ((1:ℂ) * ((1:ℂ) - star (-z) * 0) - ((0:ℂ) - (-z)) * (-(star (-z))))
      / ((1:ℂ) - star (-z) * 0) ^ 2 = ((1 - ‖z‖^2 : ℝ) : ℂ) := by
    rw [← one_sub_mul_star_self z]
    simp only [star_neg, mul_zero, sub_zero, zero_sub, neg_neg, one_mul, one_pow, div_one]
  rw [hval] at hq
  have hf := hq.hasFDerivAt
  refine (hf.restrictScalars ℝ).congr_fderiv ?_
  ext v
  simp [mul_comm]


set_option maxHeartbeats 2000000 in
/-- **The `z`-derivative of (3.1) is nondegenerate.** -/
theorem exists_implicit_fderiv_z' (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) (M : ℂ × ℂ →L[ℝ] ℂ)
    (hM : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z)) :
    ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      ≠ ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ := by
  have hw₀ : ‖extension φ z‖ < 1 := extension_mem_disk φ hφ hφc z hz
  have hgp : IsDiskAutPlus (diskAut (extension φ z)) :=
    ⟨1, extension φ z, by simp, hw₀, fun x => (one_mul _).symm⟩
  have hkp : IsDiskAutPlus (diskAut (-z)) :=
    ⟨1, -z, by simp, by simpa using hz, fun x => (one_mul _).symm⟩
  have hga : IsDiskAut (diskAut (extension φ z)) := Or.inl hgp
  have hka : IsDiskAut (diskAut (-z)) := Or.inl hkp
  -- the normalized boundary map
  have hψgb : Function.Bijective (diskAutToCircle (diskAut (extension φ z)) hga) :=
    bijective_diskAutToCircle_of_isDiskAut _ hga
  have hψkb : Function.Bijective (diskAutToCircle (diskAut (-z)) hka) :=
    bijective_diskAutToCircle_of_isDiskAut _ hka
  have hχb : Function.Bijective
      (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘ diskAutToCircle (diskAut (-z)) hka) :=
    hψgb.comp (hφ.comp hψkb)
  have hχc : Continuous
      (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘ diskAutToCircle (diskAut (-z)) hka) :=
    (continuous_diskAutToCircle _ hga).comp (hφc.comp (continuous_diskAutToCircle _ hka))
  -- naturality, with the base point of the `w`-variable frozen
  obtain ⟨c, hc1, hcnat⟩ := baryFn_naturality φ hφc (diskAut (extension φ z)) (diskAut (-z))
    hgp hka _ _ (diskAutToCircle_coe _ hga) (diskAutToCircle_coe _ hka) (extension φ z) hw₀
  have hgw : diskAut (extension φ z) (extension φ z) = 0 := by simp [diskAut]
  have hk0 : diskAut (-z) 0 = z := by simp [diskAut]
  -- the derivative of the normalized side, by formula (3.2)
  have hL : HasFDerivAt
      (fun ξ : ℂ => baryFn (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘
          diskAutToCircle (diskAut (-z)) hka) ξ 0)
      ((meanCLM (toComplexMap ⟨_, hχc⟩ * iotaBarX)) • (ContinuousLinearMap.id ℝ ℂ)
        + (meanCLM (toComplexMap ⟨_, hχc⟩ * iotaX))
            • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) 0 :=
    hasFDerivAt_baryFnMap_z_zero (toComplexMap ⟨_, hχc⟩)
  -- the derivative of the original side, by the chain rule through `g_{-z}`
  have hslice : HasFDerivAt (fun z' : ℂ => baryFn φ z' (extension φ z))
      (M.comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) (diskAut (-z) 0) := by
    rw [hk0]
    have hg : HasFDerivAt (fun z' : ℂ => (z', extension φ z))
        (ContinuousLinearMap.inl ℝ ℂ ℂ) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const (extension φ z) z)
    exact hM.comp z hg
  have hkd := hasFDerivAt_diskAut_neg z hz
  have hcomp := hslice.comp 0 hkd
  have hR := hcomp.const_mul c
  -- the two derivatives agree
  have heq : (fun ξ : ℂ => baryFn (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘
      diskAutToCircle (diskAut (-z)) hka) ξ 0)
      =ᶠ[nhds (0:ℂ)] fun ξ : ℂ => c * baryFn φ (diskAut (-z) ξ) (extension φ z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show (0:ℂ) ∈ Metric.ball (0:ℂ) 1 by simp)] with ξ hξ
    have := hcnat ξ (by simpa using hξ)
    rwa [hgw] at this
  have hunique := hL.unique (hR.congr_of_eventuallyEq heq)
  -- read off the two Wirtinger coefficients
  set A : ℂ := meanCLM (toComplexMap ⟨_, hχc⟩ * iotaBarX) with hA
  set B : ℂ := meanCLM (toComplexMap ⟨_, hχc⟩ * iotaX) with hB
  set κ : ℝ := 1 - ‖z‖^2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; nlinarith [norm_nonneg z]
  have hMreal : ∀ v : ℂ, M (((κ : ℝ) : ℂ) * v, 0) = ((κ : ℝ) : ℂ) * M (v, 0) := by
    intro v
    have : (((κ : ℝ) : ℂ) * v, (0:ℂ)) = (κ : ℝ) • (v, (0:ℂ)) := by
      simp [Prod.smul_mk, Complex.real_smul]
    rw [this, M.map_smul]
    simp [Complex.real_smul]
  have hval : ∀ v : ℂ, A * v + B * (starRingEnd ℂ) v = c * (((κ : ℝ) : ℂ) * M (v, 0)) := by
    intro v
    have h := congrFun (congrArg (fun T : ℂ →L[ℝ] ℂ => (T : ℂ → ℂ)) hunique) v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inl_apply] at h
    rw [h, ← hMreal v]
  -- the two combinations
  have hv1 := hval 1
  have hvI := hval Complex.I
  simp only [map_one, mul_one] at hv1
  rw [Complex.conj_I] at hvI
  have hI : Complex.I * (A * Complex.I + B * (-Complex.I))
      = Complex.I * (c * (((κ : ℝ) : ℂ) * M (Complex.I, 0))) := by rw [hvI]
  have hsum : 2 * B = c * (((κ : ℝ) : ℂ) * (M (1, 0) + Complex.I * M (Complex.I, 0))) := by
    linear_combination hv1 + hI + (B - A) * Complex.I_mul_I
  have hdif : 2 * A = c * (((κ : ℝ) : ℂ) * (M (1, 0) - Complex.I * M (Complex.I, 0))) := by
    linear_combination hv1 - hI + (A - B) * Complex.I_mul_I
  -- Lemma 3 for the normalized map
  have hne := CircleLift.norm_fourier_ne _ hχb hχc
  have hA' := meanCLM_mul_iotaBar (toComplexMap ⟨_, hχc⟩)
  have hB' := meanCLM_mul_iota (toComplexMap ⟨_, hχc⟩)
  simp only [toComplexMap_apply] at hA' hB'
  rw [← hA] at hA'
  rw [← hB] at hB'
  have hpine : ((2:ℂ) * (Real.pi:ℂ))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, mul_eq_zero, not_or]
    exact ⟨two_ne_zero, by exact_mod_cast ne_of_gt Real.pi_pos⟩
  have hAB : ‖A‖ ≠ ‖B‖ := by
    intro hcon
    apply hne
    rw [hA', hB', norm_mul, norm_mul] at hcon
    exact mul_left_cancel₀ (by simp) hcon
  intro hcon
  apply hAB
  have h1 : ‖2 * B‖ = ‖2 * A‖ := by
    rw [hsum, hdif, norm_mul, norm_mul, norm_mul, norm_mul, hcon]
  rw [norm_mul, norm_mul] at h1
  have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2] at h1
  linarith



/-! ### The same, with a sign

`exists_implicit_fderiv_z_of_orient'` is `exists_implicit_fderiv_z'` with `<` in
place of `≠`.  The proof is the same one — the same naturality, the same
formula (3.2), the same real positive `κ = 1 - |z|²` — with one line changed:
`CircleLift.norm_fourier_ne` is replaced by `CircleLift.norm_fourier_lt`, and
the orientation hypothesis that needs is supplied for `χ` by
`CircleLift.hasIncreasingLift_of_isDiskAutPlus` and
`CircleLift.hasIncreasingLift_comp`. -/

set_option maxHeartbeats 2000000 in
/-- **The `z`-derivative of (3.1), with a sign.** -/
theorem exists_implicit_fderiv_z_of_orient' (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) (z : ℂ) (hz : ‖z‖ < 1)
    (M : ℂ × ℂ →L[ℝ] ℂ)
    (hM : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z)) :
    ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      < ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ := by
  have hw₀ : ‖extension φ z‖ < 1 := extension_mem_disk φ hφ hφc z hz
  have hgp : IsDiskAutPlus (diskAut (extension φ z)) :=
    ⟨1, extension φ z, by simp, hw₀, fun x => (one_mul _).symm⟩
  have hkp : IsDiskAutPlus (diskAut (-z)) :=
    ⟨1, -z, by simp, by simpa using hz, fun x => (one_mul _).symm⟩
  have hga : IsDiskAut (diskAut (extension φ z)) := Or.inl hgp
  have hka : IsDiskAut (diskAut (-z)) := Or.inl hkp
  -- the normalized boundary map, and its orientation
  have hχc : Continuous
      (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘ diskAutToCircle (diskAut (-z)) hka) :=
    (continuous_diskAutToCircle _ hga).comp (hφc.comp (continuous_diskAutToCircle _ hka))
  have hχor : HasIncreasingLift
      (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘ diskAutToCircle (diskAut (-z)) hka) :=
    CircleLift.hasIncreasingLift_comp
      (CircleLift.hasIncreasingLift_of_isDiskAutPlus hgp _ (fun ζ => (diskAutToCircle_coe _ hga ζ).symm))
      (CircleLift.hasIncreasingLift_comp hor
        (CircleLift.hasIncreasingLift_of_isDiskAutPlus hkp _ (fun ζ => (diskAutToCircle_coe _ hka ζ).symm)))
  -- naturality, with the base point of the `w`-variable frozen
  obtain ⟨c, hc1, hcnat⟩ := baryFn_naturality φ hφc (diskAut (extension φ z)) (diskAut (-z))
    hgp hka _ _ (diskAutToCircle_coe _ hga) (diskAutToCircle_coe _ hka) (extension φ z) hw₀
  have hgw : diskAut (extension φ z) (extension φ z) = 0 := by simp [diskAut]
  have hk0 : diskAut (-z) 0 = z := by simp [diskAut]
  have hL : HasFDerivAt
      (fun ξ : ℂ => baryFn (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘
          diskAutToCircle (diskAut (-z)) hka) ξ 0)
      ((meanCLM (toComplexMap ⟨_, hχc⟩ * iotaBarX)) • (ContinuousLinearMap.id ℝ ℂ)
        + (meanCLM (toComplexMap ⟨_, hχc⟩ * iotaX))
            • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) 0 :=
    hasFDerivAt_baryFnMap_z_zero (toComplexMap ⟨_, hχc⟩)
  have hslice : HasFDerivAt (fun z' : ℂ => baryFn φ z' (extension φ z))
      (M.comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) (diskAut (-z) 0) := by
    rw [hk0]
    have hg : HasFDerivAt (fun z' : ℂ => (z', extension φ z))
        (ContinuousLinearMap.inl ℝ ℂ ℂ) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const (extension φ z) z)
    exact hM.comp z hg
  have hkd := hasFDerivAt_diskAut_neg z hz
  have hcomp := hslice.comp 0 hkd
  have hR := hcomp.const_mul c
  have heq : (fun ξ : ℂ => baryFn (diskAutToCircle (diskAut (extension φ z)) hga ∘ φ ∘
      diskAutToCircle (diskAut (-z)) hka) ξ 0)
      =ᶠ[nhds (0:ℂ)] fun ξ : ℂ => c * baryFn φ (diskAut (-z) ξ) (extension φ z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show (0:ℂ) ∈ Metric.ball (0:ℂ) 1 by simp)] with ξ hξ
    have := hcnat ξ (by simpa using hξ)
    rwa [hgw] at this
  have hunique := hL.unique (hR.congr_of_eventuallyEq heq)
  set A : ℂ := meanCLM (toComplexMap ⟨_, hχc⟩ * iotaBarX) with hA
  set B : ℂ := meanCLM (toComplexMap ⟨_, hχc⟩ * iotaX) with hB
  set κ : ℝ := 1 - ‖z‖^2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; nlinarith [norm_nonneg z]
  have hMreal : ∀ v : ℂ, M (((κ : ℝ) : ℂ) * v, 0) = ((κ : ℝ) : ℂ) * M (v, 0) := by
    intro v
    have : (((κ : ℝ) : ℂ) * v, (0:ℂ)) = (κ : ℝ) • (v, (0:ℂ)) := by
      simp [Prod.smul_mk, Complex.real_smul]
    rw [this, M.map_smul]
    simp [Complex.real_smul]
  have hval : ∀ v : ℂ, A * v + B * (starRingEnd ℂ) v = c * (((κ : ℝ) : ℂ) * M (v, 0)) := by
    intro v
    have h := congrFun (congrArg (fun T : ℂ →L[ℝ] ℂ => (T : ℂ → ℂ)) hunique) v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inl_apply] at h
    rw [h, ← hMreal v]
  have hv1 := hval 1
  have hvI := hval Complex.I
  simp only [map_one, mul_one] at hv1
  rw [Complex.conj_I] at hvI
  have hI : Complex.I * (A * Complex.I + B * (-Complex.I))
      = Complex.I * (c * (((κ : ℝ) : ℂ) * M (Complex.I, 0))) := by rw [hvI]
  have hsum : 2 * B = c * (((κ : ℝ) : ℂ) * (M (1, 0) + Complex.I * M (Complex.I, 0))) := by
    linear_combination hv1 + hI + (B - A) * Complex.I_mul_I
  have hdif : 2 * A = c * (((κ : ℝ) : ℂ) * (M (1, 0) - Complex.I * M (Complex.I, 0))) := by
    linear_combination hv1 - hI + (A - B) * Complex.I_mul_I
  -- Lemma 3 with a sign, for the normalized map
  have hA' := meanCLM_mul_iotaBar (toComplexMap ⟨_, hχc⟩)
  have hB' := meanCLM_mul_iota (toComplexMap ⟨_, hχc⟩)
  simp only [toComplexMap_apply] at hA' hB'
  rw [← hA] at hA'
  rw [← hB] at hB'
  have hpine : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    positivity
  have hAB : ‖B‖ < ‖A‖ := by
    rw [hA', hB', norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (CircleLift.norm_fourier_lt _ hχor) (norm_pos_iff.2 hpine)
  -- transport the sign back
  have hc2 : ‖(2:ℂ)‖ = 2 := by norm_num
  have hκc : ‖((κ : ℝ) : ℂ)‖ = κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  have h1 : 2 * ‖B‖ = κ * ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖ := by
    have h := congrArg norm hsum
    rw [norm_mul, norm_mul, norm_mul, hc1, hκc, one_mul, hc2] at h
    exact h
  have h2 : 2 * ‖A‖ = κ * ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ := by
    have h := congrArg norm hdif
    rw [norm_mul, norm_mul, norm_mul, hc1, hκc, one_mul, hc2] at h
    exact h
  exact lt_of_mul_lt_mul_left (by linarith) hκpos.le

end ZDeriv

/-! ### The Jacobian of `Φ` (Theorem 1)

The Jacobian of a real-differentiable `F : ℂ → ℂ` at `z` is
`|F_z|² - |F_z̄|²`, where `F_z = (dF(1) - i·dF(i))/2` and
`F_z̄ = (dF(1) + i·dF(i))/2`; it is *not* `‖dF(1)‖² - ‖dF(i)‖²`.  Indeed those
two norms coincide for every holomorphic `F` (`norm_fderiv_one_eq_norm_fderiv_I`
below), so a nonvanishing statement phrased with them would fail already for
`φ = id`, where `Φ = id` by conformal naturality.  The statement of
`extension_jacobian_ne_zero` is therefore phrased with `|Φ_z|` and `|Φ_z̄|`,
not with `‖dΦ(1)‖` and `‖dΦ(i)‖`.

It is phrased with `≠`, not `<`.  The paper writes `|Φ'_z|² - |Φ'_z̄|² > 0`,
but that is the orientation-preserving case: `E(ζ ↦ ζ⁻¹)` is `z ↦ z̄`, whose
Jacobian is `-1`, and `extension_jacobian_ne_zero_false` records the
refutation.  What Theorem 1 asserts, and all it needs, is that the differential
is invertible.  The strict form is `extension_jacobian_pos`. -/

/-- For a holomorphic `F` the two directional images `dF(1)` and `dF(i)` always
have equal norm. -/
theorem norm_fderiv_one_eq_norm_fderiv_I (F : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ F z) :
    ‖(fderiv ℝ F z) 1‖ = ‖(fderiv ℝ F z) Complex.I‖ := by
  have hmap := (fderiv ℂ F z).map_smul Complex.I (1:ℂ)
  simp only [smul_eq_mul, mul_one] at hmap
  rw [h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [hmap, norm_mul, Complex.norm_I, one_mul]

/-- **Implicit differentiation** in the proof of Theorem 1.  Differentiating
`F(z, Φ(z)) = 0` in `z` and in `z̄` gives, with `A = F_z`, `B = F_z̄`,
`P = F_w`, `Q = F_w̄`, `p = Φ_z` and `q = Φ_z̄`, the two equations below; they
imply the paper's formula
`|Φ_z|² - |Φ_z̄|² = (|F_z|² - |F_z̄|²)/(|F_w|² - |F_w̄|²)`
in the cross-multiplied form stated here (the two mixed terms `P Q̄ p q`
cancel). -/
theorem implicit_jacobian_identity (A B P Q p q : ℂ)
    (h1 : A + P * p + Q * star q = 0) (h2 : B + P * q + Q * star p = 0) :
    (Complex.normSq P - Complex.normSq Q) * (Complex.normSq p - Complex.normSq q)
      = Complex.normSq A - Complex.normSq B := by
  have hA : A = -(P * p + Q * star q) := by linear_combination h1
  have hB : B = -(P * q + Q * star p) := by linear_combination h2
  rw [hA, hB]
  simp only [Complex.normSq_apply, Complex.star_def, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The Jacobian step of Theorem 1: positivity of `|F_w|² - |F_w̄|²` (formula
(3.3)) together with positivity of `|F_z|² - |F_z̄|²` (Lemma 3, via (3.2):
`F_z(0,0) = c₁` and `F_z̄(0,0) = c₋₁`) forces the Jacobian of `Φ` to be
positive. -/
theorem norm_lt_of_implicit (A B P Q p q : ℂ)
    (h1 : A + P * p + Q * star q = 0) (h2 : B + P * q + Q * star p = 0)
    (hPQ : ‖Q‖ < ‖P‖) (hAB : ‖B‖ < ‖A‖) : ‖q‖ < ‖p‖ := by
  have key := implicit_jacobian_identity A B P Q p q h1 h2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at key
  have hP2 : 0 < ‖P‖ ^ 2 - ‖Q‖ ^ 2 := by nlinarith [norm_nonneg Q, norm_nonneg P]
  have hA2 : 0 < ‖A‖ ^ 2 - ‖B‖ ^ 2 := by nlinarith [norm_nonneg B, norm_nonneg A]
  have hp2 : 0 < ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
    rcases le_or_gt (‖p‖ ^ 2 - ‖q‖ ^ 2) 0 with hle | hgt
    · exact absurd key (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hP2.le hle])
    · exact hgt
  nlinarith [norm_nonneg q, norm_nonneg p]

/-- **The same elimination without the sign.**  `norm_lt_of_implicit` needs
both positivity facts to conclude `|Φ_z̄| < |Φ_z|`.  *Nondegeneracy* alone needs
neither: the identity says the two Jacobians agree up to a factor, so if
`|p| = |q|` the left-hand side vanishes and `|A| = |B|` follows.  Formula (3.3)
is not used at all.

This is the form Theorem 1 actually needs — a local diffeomorphism only asks
for an invertible differential — and, unlike the strict form, it is true for
every homeomorphism of the circle; see `extension_jacobian_ne_zero_false`. -/
theorem norm_ne_of_implicit (A B P Q p q : ℂ)
    (h1 : A + P * p + Q * star q = 0) (h2 : B + P * q + Q * star p = 0)
    (hAB : ‖B‖ ≠ ‖A‖) : ‖q‖ ≠ ‖p‖ := by
  intro hcon
  apply hAB
  have key := implicit_jacobian_identity A B P Q p q h1 h2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at key
  rw [hcon] at key
  have hzero : (‖P‖ ^ 2 - ‖Q‖ ^ 2) * (‖p‖ ^ 2 - ‖p‖ ^ 2) = 0 := by ring
  rw [hzero] at key
  have hsq : ‖B‖ ^ 2 = ‖A‖ ^ 2 := by linarith
  rw [← Real.sqrt_sq (norm_nonneg B), hsq, Real.sqrt_sq (norm_nonneg A)]

/-- **Implicit differentiation of (3.1), the analytic half.**  `Φ` solves
`F(z, Φ(z)) = 0` at *every* point of `D` — that is `extension_baryEq`, and it
holds on an open set — so the composite `z ↦ F(z, Φ(z))` is identically zero
near `z` and its differential vanishes.  By the chain rule that differential is
`v ↦ dF(v, dΦ(v))`, so `dF` annihilates the graph of `dΦ`.

This is the step the paper writes as "differentiate `F(z, Φ(z)) = 0`", and it
is the only place where the defining property of `Φ` enters the Jacobian
argument. -/
theorem baryFn_hasFDerivAt_graph (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) {z : ℂ} (hz : ‖z‖ < 1)
    {L : ℂ →L[ℝ] ℂ} (hΦ : HasFDerivAt (extension φ) L z)
    {M : ℂ × ℂ →L[ℝ] ℂ}
    (hF : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z)) :
    ∀ v : ℂ, M (v, L v) = 0 := by
  have hgraph : HasFDerivAt (fun z' : ℂ => (z', extension φ z'))
      ((ContinuousLinearMap.id ℝ ℂ).prod L) z := (hasFDerivAt_id z).prodMk hΦ
  have hcomp := HasFDerivAt.comp (g := fun p : ℂ × ℂ => baryFn φ p.1 p.2)
    (f := fun z' : ℂ => (z', extension φ z')) z hF hgraph
  simp only [Function.comp_def] at hcomp
  have hev : (fun _ : ℂ => (0:ℂ)) =ᶠ[nhds z] fun z' : ℂ => baryFn φ z' (extension φ z') := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with z' hz'
    exact ((baryEq_iff_baryFn φ z' _).1
      (extension_baryEq φ hφ hφc z' (mem_ball_zero_iff.1 hz'))).symm
  have hzero := (hcomp.congr_of_eventuallyEq hev).unique (hasFDerivAt_const (0:ℂ) z)
  intro v
  have hv := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) hzero
  simpa using hv

/-- **Implicit differentiation of (3.1), the algebraic half.**  A real-linear
`M : ℂ × ℂ → ℂ` annihilating the graph of a real-linear `L` gives the paper's
two equations
`F_z + F_w Φ_z + F_w̄ conj(Φ_z̄) = 0` and `F_z̄ + F_w Φ_z̄ + F_w̄ conj(Φ_z) = 0`.

Writing every real-linear map in Wirtinger form (`clm_apply_eq_wirt`) turns
`M(v, L v) = 0` into `X·v + Y·v̄ = 0` for all `v`, where `X` and `Y` are the two
brackets; testing at `v = 1` and `v = i` gives `X + Y = 0` and `i(X - Y) = 0`,
hence both vanish. -/
theorem wirt_implicit_of_graph_eq_zero {M : ℂ × ℂ →L[ℝ] ℂ} {L : ℂ →L[ℝ] ℂ}
    (h : ∀ v : ℂ, M (v, L v) = 0) {A B P Q p q : ℂ}
    (hA : A = (M (1, 0) - Complex.I * M (Complex.I, 0)) / 2)
    (hB : B = (M (1, 0) + Complex.I * M (Complex.I, 0)) / 2)
    (hP : P = (M (0, 1) - Complex.I * M (0, Complex.I)) / 2)
    (hQ : Q = (M (0, 1) + Complex.I * M (0, Complex.I)) / 2)
    (hp : p = (L 1 - Complex.I * L Complex.I) / 2)
    (hq : q = (L 1 + Complex.I * L Complex.I) / 2) :
    A + P * p + Q * star q = 0 ∧ B + P * q + Q * star p = 0 := by
  have hsplit : ∀ v b : ℂ, M (v, b) = M (v, 0) + M (0, b) := by
    intro v b
    rw [← map_add]
    norm_num
  have hMz : ∀ v : ℂ, M (v, 0) = A * v + B * star v := by
    intro v
    have := clm_apply_eq_wirt (M.comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at this
    rw [hA, hB]
    exact this
  have hMw : ∀ b : ℂ, M (0, b) = P * b + Q * star b := by
    intro b
    have := clm_apply_eq_wirt (M.comp (ContinuousLinearMap.inr ℝ ℂ ℂ)) b
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this
    rw [hP, hQ]
    exact this
  have hL : ∀ v : ℂ, L v = p * v + q * star v := by
    intro v
    rw [hp, hq]
    exact clm_apply_eq_wirt L v
  have key : ∀ v : ℂ,
      (A + P * p + Q * star q) * v + (B + P * q + Q * star p) * star v = 0 := by
    intro v
    have h1 := h v
    rw [hsplit v (L v), hMz v, hL v, hMw (p * v + q * star v),
      show star (p * v + q * star v) = star p * star v + star q * v by
        simp only [star_add, star_mul, star_star]; ring] at h1
    linear_combination h1
  have e1 := key 1
  simp only [star_one, mul_one] at e1
  have e2 := key Complex.I
  rw [show star Complex.I = -Complex.I from by simp] at e2
  have hd : (A + P * p + Q * star q) - (B + P * q + Q * star p) = 0 := by
    have hh := congrArg (fun t : ℂ => Complex.I * t) e2
    simp only [mul_zero] at hh
    linear_combination (-1 : ℂ) * hh
      + ((A + P * p + Q * star q) - (B + P * q + Q * star p)) * Complex.I_mul_I
  exact ⟨by linear_combination (e1 + hd) / 2, by linear_combination (e1 - hd) / 2⟩

/-- **Theorem 1, Jacobian part, from the implicit function data.**  This is the
whole of the paper's argument except the analytic input, and it is proved: the
two implicit differentiation equations come from `baryFn_hasFDerivAt_graph` and
`wirt_implicit_of_graph_eq_zero`, and `norm_lt_of_implicit` turns them,
together with the two positivity facts, into `|Φ_z̄| < |Φ_z|`.

The hypotheses are, in the paper's notation: `Φ` is differentiable at `z` with
differential `L`; `F` is differentiable at `(z, Φ(z))` with differential `M`;
`|F_w̄| < |F_w|` is formula (3.3); and `|F_z̄| < |F_z|` is Lemma 3.  The last two
are stated on `M` in the same `L1 ± i·Li` form as the conclusion, i.e. as
`2|F_w̄| < 2|F_w|` and `2|F_z̄| < 2|F_z|`. -/
theorem extension_jacobian_of_implicit (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1)
    (L : ℂ →L[ℝ] ℂ) (hΦ : HasFDerivAt (extension φ) L z)
    (M : ℂ × ℂ →L[ℝ] ℂ)
    (hF : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z))
    (hFw : ‖M (0, 1) + Complex.I * M (0, Complex.I)‖
      < ‖M (0, 1) - Complex.I * M (0, Complex.I)‖)
    (hFz : ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      < ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖) :
    ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        + Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖
      < ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        - Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖ := by
  have hhalf : ∀ x : ℂ, ‖x / 2‖ = ‖x‖ / 2 := by
    intro x; rw [norm_div]; norm_num
  obtain ⟨h1, h2⟩ := wirt_implicit_of_graph_eq_zero
    (baryFn_hasFDerivAt_graph φ hφ hφc hz hΦ hF) rfl rfl rfl rfl rfl rfl
  have hPQ : ‖(M (0, 1) + Complex.I * M (0, Complex.I)) / 2‖
      < ‖(M (0, 1) - Complex.I * M (0, Complex.I)) / 2‖ := by
    rw [hhalf, hhalf]; linarith
  have hAB : ‖(M (1, 0) + Complex.I * M (Complex.I, 0)) / 2‖
      < ‖(M (1, 0) - Complex.I * M (Complex.I, 0)) / 2‖ := by
    rw [hhalf, hhalf]; linarith
  have hkey := norm_lt_of_implicit _ _ _ _ _ _ h1 h2 hPQ hAB
  rw [hhalf, hhalf] at hkey
  rw [hΦ.fderiv]
  linarith

/-- **Theorem 1, Jacobian part, without the sign.**  The same implicit
differentiation as `extension_jacobian_of_implicit`, run through
`norm_ne_of_implicit` instead of `norm_lt_of_implicit`.  Two hypotheses
disappear: formula (3.3) is not needed at all, and Lemma 3 is needed only in
the weak form `|F_z̄| ≠ |F_z|`. -/
theorem extension_jacobian_ne_of_implicit (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1)
    (L : ℂ →L[ℝ] ℂ) (hΦ : HasFDerivAt (extension φ) L z)
    (M : ℂ × ℂ →L[ℝ] ℂ)
    (hF : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z))
    (hFz : ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      ≠ ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖) :
    ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        + Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖
      ≠ ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        - Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖ := by
  have hhalf : ∀ x : ℂ, ‖x / 2‖ = ‖x‖ / 2 := by
    intro x; rw [norm_div]; norm_num
  obtain ⟨h1, h2⟩ := wirt_implicit_of_graph_eq_zero
    (baryFn_hasFDerivAt_graph φ hφ hφc hz hΦ hF) rfl rfl rfl rfl rfl rfl
  have hAB : ‖(M (1, 0) + Complex.I * M (Complex.I, 0)) / 2‖
      ≠ ‖(M (1, 0) - Complex.I * M (Complex.I, 0)) / 2‖ := by
    rw [hhalf, hhalf]
    intro hc
    exact hFz (by linarith)
  have hkey := norm_ne_of_implicit _ _ _ _ _ _ h1 h2 hAB
  rw [hhalf, hhalf] at hkey
  rw [hΦ.fderiv]
  intro hc
  exact hkey (by rw [hc])

/-- Bullet 3 of `exists_implicit_fderiv`, **derived**: given only the derivative
formula (3.1) for the `w`-variable, the nondegeneracy `|F_w̄| < |F_w|` follows
from (3.3). -/
theorem baryFn_wirtW_nondegenerate (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (M : ℂ × ℂ →L[ℝ] ℂ)
    (hM : ∀ v : ℂ, M (0, v) = (((1 - ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ)
      * (-v + harmonicMeasureAvg z (fun ζ => (diskAut w ((φ ζ : Circle) : ℂ)) ^ 2) * star v)) :
    ‖M (0, 1) + Complex.I * M (0, Complex.I)‖
      < ‖M (0, 1) - Complex.I * M (0, Complex.I)‖ := by
  set q : ℂ := harmonicMeasureAvg z (fun ζ => (diskAut w ((φ ζ : Circle) : ℂ)) ^ 2) with hqdef
  set κ : ℝ := (1 - ‖w‖ ^ 2)⁻¹ with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact inv_pos.2 (by nlinarith [norm_nonneg w])
  have h1 : M (0, 1) = ((κ : ℝ) : ℂ) * (-1 + q) := by rw [hM]; simp
  have h2 : M (0, Complex.I) = ((κ : ℝ) : ℂ) * (-Complex.I + q * (-Complex.I)) := by
    rw [hM, Complex.star_def, Complex.conj_I]
  have hsum : M (0, 1) + Complex.I * M (0, Complex.I) = ((κ : ℝ) : ℂ) * (2 * q) := by
    rw [h1, h2]
    linear_combination (-((κ : ℝ) : ℂ) * (1 + q)) * Complex.I_mul_I
  have hdif : M (0, 1) - Complex.I * M (0, Complex.I) = ((κ : ℝ) : ℂ) * (-2) := by
    rw [h1, h2]
    linear_combination (((κ : ℝ) : ℂ) * (1 + q)) * Complex.I_mul_I
  have hnκ : ‖((κ : ℝ) : ℂ)‖ = κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  have hq := norm_harmonicMeasureAvg_sq_lt_one φ hφ hφc hz hw
  rw [← hqdef] at hq
  have hA : ‖((κ : ℝ) : ℂ) * (2 * q)‖ = κ * (2 * ‖q‖) := by
    rw [norm_mul, hnκ, norm_mul]; simp
  have hB : ‖((κ : ℝ) : ℂ) * (-2 : ℂ)‖ = κ * 2 := by
    rw [norm_mul, hnκ]; simp
  rw [hsum, hdif, hA, hB]
  nlinarith [hq, hκpos, norm_nonneg q]

/-- The last analytic input to the Jacobian half of Theorem 1, **proved**:
`|F_z̄| ≠ |F_z|` at `(z, Φ(z))`.

This is §4.3.  At the normalized point it is `|c₁| ≠ |c₋₁|`, which is Lemma 3
(`CircleLift.norm_fourier_ne`, the form that needs no orientation hypothesis);
the reduction to the normalized point is `ZDeriv.baryFn_naturality` together
with formula (3.2) at the origin, `ZDeriv.hasFDerivAt_baryFnMap_z_zero`.  See
the section header before `ZDeriv` for how the two fit together.

**This used to be stated with `<`, and in that form it is false.**  The strict
inequality says the Jacobian of `Φ` is *positive*, which is a statement about
orientation, and `φ(ζ) = ζ⁻¹` refutes it: `E(φ)(z) = z̄`, so `Φ_z = 0` and
`Φ_z̄ = 1`.  That is `extension_jacobian_ne_zero_false`, and it is the same
defect `lemma3_fourier_coeff_false` records one level down — the orientation
hypothesis of Lemma 3, restored there as `HasIncreasingLift`, was never
propagated up to the Jacobian.  Theorem 1 does not need it: `Φ` is a
diffeomorphism of `D` for *every* homeomorphism `φ` of `S¹`, orientation
reversing included, and what a diffeomorphism needs is an invertible
differential, not a positive one.  So the nondegenerate form is what is cited
here; the strict form survives, with the hypothesis it requires, as
`exists_implicit_fderiv_z_of_orient`.

This citation used to ask for four things.  Three of them are now proved:

* *`Φ` is real-differentiable at `z`* is `extension_analyticOn_disk`, which is
  no longer cited either — it comes from `exists_analytic_baryEq_solution`.
* *`F` is real-differentiable at `(z, Φ(z))`* is `analyticAt_baryFnMap`,
  restricted to the slice `u = φ`.
* *The `w`-derivative is `v ↦ (1 - |w|²)⁻¹(-v + q v̄)`* is
  `hasFDerivAt_baryFnMap_w` together with the Möbius identities of
  `coeff_a_eq` and `coeff_b_eq`; and `|q| < 1`, formula (3.3), is
  `norm_harmonicMeasureAvg_sq_lt_one`.

The fourth is this one, and it is no longer cited either. -/
theorem exists_implicit_fderiv_z (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) (M : ℂ × ℂ →L[ℝ] ℂ)
    (hM : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z)) :
    ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      ≠ ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ :=
  ZDeriv.exists_implicit_fderiv_z' φ hφ hφc z hz M hM

set_option maxHeartbeats 2000000 in
/-- The implicit-function data behind the Jacobian half of Theorem 1.  All four
clauses are proved; the `z`-derivative, `exists_implicit_fderiv_z`, is taken in
the nondegenerate form `≠`, which is the form that holds for every
homeomorphism of `S¹`.  The
third clause, the `w`-derivative, still carries formula (3.3) in the strict
form — that one *is* true unconditionally (`norm_harmonicMeasureAvg_sq_lt_one`),
because `|q| < 1` holds for every `φ`. -/
theorem exists_implicit_fderiv (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ (L : ℂ →L[ℝ] ℂ) (M : ℂ × ℂ →L[ℝ] ℂ),
      HasFDerivAt (extension φ) L z ∧
      HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z) ∧
      (∀ v : ℂ, M (0, v) = (((1 - ‖extension φ z‖ ^ 2)⁻¹ : ℝ) : ℂ)
        * (-v + harmonicMeasureAvg z
            (fun ζ => (diskAut (extension φ z) ((φ ζ : Circle) : ℂ)) ^ 2) * star v)) ∧
      ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
        ≠ ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ := by
  classical
  set φ₀ : C(Circle, Circle) := ⟨φ, hφc⟩ with hφ₀def
  set u₀ : C(Circle, ℂ) := toComplexMap φ₀ with hu₀def
  have hu₀norm : ‖u₀‖ = 1 := by
    refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).2 fun ζ =>
      le_of_eq (Circle.norm_coe _)) ?_
    have h := u₀.norm_coe_le_norm 1
    rwa [show ‖u₀ 1‖ = 1 from Circle.norm_coe _] at h
  set w₀ : ℂ := extension φ z with hw₀def
  have hw₀lt : ‖w₀‖ < 1 := extension_mem_disk φ hφ hφc z hz
  have hwu : ‖w₀‖ * ‖u₀‖ < 1 := by rw [hu₀norm, mul_one]; exact hw₀lt
  have hbary : baryFnMap z w₀ u₀ = 0 :=
    (baryEq_iff_baryFnMap φ₀ z w₀).1 (extension_baryEq φ hφ hφc z hz)
  -- `baryFn φ` is the slice of `baryFnMap` at `u₀`
  have hslice : (fun p : ℂ × ℂ => baryFn φ p.1 p.2)
      = fun p : ℂ × ℂ => baryFnMap p.1 p.2 u₀ := rfl
  -- Bullet 1: `Φ` is differentiable at `z`, because it is real-analytic there
  have hball : z ∈ Metric.ball (0:ℂ) 1 := by simpa using hz
  have hΦan : AnalyticAt ℝ (extension φ) z :=
    Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp
      (extension_analyticOn_disk φ hφ hφc) z hball
  -- Bullet 2: `F` is differentiable at `(z, Φ(z))`, by joint analyticity
  have hemb : AnalyticAt ℝ (fun p : ℂ × ℂ => ((p.1, u₀), p.2)) (z, w₀) :=
    (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
  have hFan : AnalyticAt ℝ (fun p : ℂ × ℂ => baryFnMap p.1 p.2 u₀) (z, w₀) := by
    have h := AnalyticAt.comp
      (g := fun q : (ℂ × C(Circle, ℂ)) × ℂ => baryFnMap q.1.1 q.2 q.1.2)
      (f := fun p : ℂ × ℂ => ((p.1, u₀), p.2)) (x := (z, w₀))
      (analyticAt_baryFnMap hz hwu) hemb
    simpa [Function.comp_def] using h
  set M : ℂ × ℂ →L[ℝ] ℂ := fderiv ℝ (fun p : ℂ × ℂ => baryFnMap p.1 p.2 u₀) (z, w₀) with hMdef
  have hM : HasFDerivAt (fun p : ℂ × ℂ => baryFnMap p.1 p.2 u₀) M (z, w₀) :=
    hFan.differentiableAt.hasFDerivAt
  -- Bullet 3: the `w`-partial of `M` is formula (2.1) with Lemma 4.1's coefficients
  have hMw : ∀ v : ℂ, M (0, v) = (((1 - ‖w₀‖ ^ 2)⁻¹ : ℝ) : ℂ)
      * (-v + harmonicMeasureAvg z (fun ζ => (diskAut w₀ (u₀ ζ)) ^ 2) * star v) := by
    set inrL : ℂ →L[ℝ] ℂ × ℂ := (0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ) with hinrL
    have hsl : HasFDerivAt (fun w : ℂ => ((z, w) : ℂ × ℂ)) inrL w₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) z w₀).prodMk (hasFDerivAt_id (𝕜 := ℝ) w₀)
    have hcomp := hM.comp w₀ hsl
    simp only [Function.comp_def] at hcomp
    have hD := hasFDerivAt_baryFnMap_w (z₀ := z) (w₀ := w₀) (u₀ := u₀) hz hwu
    rw [coeff_a_eq hz hw₀lt hwu hbary, coeff_b_eq hz hw₀lt hwu hbary] at hD
    have heq := hcomp.unique hD
    intro v
    have hval := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) heq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hinrL,
      ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.coe_id', id_eq, add_apply,
      smul_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul] at hval
    rw [hval, one_sub_mul_star_self w₀, ← Complex.ofReal_inv, Complex.star_def]
    ring
  refine ⟨fderiv ℝ (extension φ) z, M, hΦan.differentiableAt.hasFDerivAt, ?_, ?_, ?_⟩
  · rw [hslice]; exact hM
  · exact hMw
  · exact exists_implicit_fderiv_z φ hφ hφc z hz M (by rw [hslice]; exact hM)

/-- **Theorem 1**, Jacobian part: the Jacobian `|Φ_z|² - |Φ_z̄|²` of `Φ = E(φ)`
is *nonzero* at every `z ∈ D`, so `Φ` is a local diffeomorphism there.

The conclusion used to read `|Φ_z̄| < |Φ_z|`, i.e. a *positive* Jacobian, and
that is false — `extension_jacobian_ne_zero_false` refutes it with
`φ(ζ) = ζ⁻¹`, whose extension is `z ↦ z̄`.  The sign is a statement about
orientation and Theorem 1 does not assert it; `extension_jacobian_pos` does,
under `HasIncreasingLift`.

The proof is `extension_jacobian_ne_of_implicit` fed by
`exists_implicit_fderiv`, and **it is complete**: `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`.  Everything the paper argues —
differentiate `F(z, Φ(z)) = 0`, read the result in Wirtinger form, and
eliminate — is here; the differentiability of `Φ` and of `F` and the formula
for the `w`-derivative come from `exists_analytic_baryEq_solution` and the
Banach-algebra description of (3.1); and the `z`-derivative is
`exists_implicit_fderiv_z`, which is §4.3 reducing to Lemma 3.  Formula (3.3)
is not used at all on this path: the sign-free elimination does not need it, so
`norm_harmonicMeasureAvg_sq_lt_one` is required only for
`extension_jacobian_pos`. -/
theorem extension_jacobian_ne_zero (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        + Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖
      ≠ ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        - Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖ := by
  obtain ⟨L, M, hΦ, hF, -, hFz⟩ := exists_implicit_fderiv φ hφ hφc z hz
  exact extension_jacobian_ne_of_implicit φ hφ hφc z hz L hΦ M hF hFz

/-! ### Proper local homeomorphisms of the disc

This is §7 of the notes, and it is the last piece of Theorem 1.  `Φ|_D` is a
*proper local homeomorphism* of `D`: a local homeomorphism by the Jacobian half
just proved, and proper because `Φ` is continuous on the compact `D̄` and carries
`S¹` to `S¹`.  Such a map of a simply connected disc is a bijection.

Mathlib does not have that implication, and the usual route to it — a proper
local homeomorphism is a covering map — is expensive here, because building an
`IsCoveringMap` means building a `Trivialization` around every point.  None of
that is needed.  Mathlib's lifting machinery for *local* homeomorphisms
(`IsLocalHomeomorph.monodromy_theorem`, which needs only `IsSeparatedMap`, free
in a `T2Space`) already does everything a covering map would be used for, on one
condition: that paths lift.  So the only covering-theoretic input to supply is
`exists_path_lifts`, and the only place properness enters is
`exists_uniform_sections`, which makes the local sections of `p` live on a
neighbourhood of the base point that does not depend on which sheet they pass
through.  With that, Mathlib's own proof of path lifting for covering maps goes
through verbatim.

Injectivity is then §7(iii): the loop `p ∘ γ`, where `γ` joins two points of a
fibre, is null-homotopic because the disc is simply connected
(`Convex.contractibleSpace`), and lifting that null-homotopy identifies the two
points.  Surjectivity needs no lifting at all — the image is open because `p` is
a local homeomorphism and closed because `p` is proper. -/

namespace ProperLH

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- **Lemma A.**  For a proper local homeomorphism, the local sections can be
taken on a neighbourhood of `x` that does not depend on which point of the
fibre they pass through.  This is the only place properness is used. -/
theorem exists_uniform_sections [T2Space X] [LocallyCompactSpace X] {p : E → X}
    (hp : IsLocalHomeomorph p) (hproper : ∀ K : Set X, IsCompact K → IsCompact (p ⁻¹' K))
    (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ e ∈ p ⁻¹' V, ∃ s : X → E, ContinuousOn s V ∧ (∀ v ∈ V, p (s v) = v) ∧ s (p e) = e := by
  classical
  have hpc : Continuous p := hp.continuous
  have hfib : IsCompact (p ⁻¹' {x}) := hproper _ isCompact_singleton
  choose q hq hpq using hp
  obtain ⟨t, ht⟩ := hfib.elim_finite_subcover (fun e : (p ⁻¹' {x} : Set E) => (q (e : E)).source)
    (fun e => (q (e : E)).open_source) (fun e he => Set.mem_iUnion.2 ⟨⟨e, he⟩, hq e⟩)
  set W : Set E := ⋃ i ∈ t, (q ((i : (p ⁻¹' {x} : Set E)) : E)).source with hW
  have hWopen : IsOpen W := isOpen_biUnion fun i _ => (q _).open_source
  set V₀ : Set X := ⋂ i ∈ t, (q ((i : (p ⁻¹' {x} : Set E)) : E)).target with hV₀
  have hV₀open : IsOpen V₀ := isOpen_biInter_finset fun i _ => (q _).open_target
  have hxV₀ : x ∈ V₀ := by
    simp only [hV₀, Set.mem_iInter]
    intro i _
    have hmem := (q ((i : (p ⁻¹' {x} : Set E)) : E)).map_source (hq _)
    have : p ((i : (p ⁻¹' {x} : Set E)) : E) = x := i.2
    rwa [← hpq _, this] at hmem
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  have hC : IsCompact (p ⁻¹' K \ W) := (hproper K hKc).diff hWopen
  have hpCclosed : IsClosed (p '' (p ⁻¹' K \ W)) := (hC.image hpc).isClosed
  have hxpC : x ∉ p '' (p ⁻¹' K \ W) := by
    rintro ⟨c, ⟨-, hcW⟩, hcx⟩
    exact hcW (ht (show c ∈ p ⁻¹' {x} from hcx))
  set V : Set X := (interior K ∩ V₀) \ (p '' (p ⁻¹' K \ W)) with hVdef
  refine ⟨V, (isOpen_interior.inter hV₀open).sdiff hpCclosed,
    ⟨⟨mem_interior_iff_mem_nhds.2 hKn, hxV₀⟩, hxpC⟩, ?_⟩
  intro e he
  have hpe : p e ∈ interior K ∩ V₀ := he.1
  have heW : e ∈ W := by
    by_contra hne
    exact he.2 ⟨e, ⟨(interior_subset hpe.1 : p e ∈ K), hne⟩, rfl⟩
  obtain ⟨i, hit, hei⟩ := Set.mem_iUnion₂.1 heW
  refine ⟨(q ((i : (p ⁻¹' {x} : Set E)) : E)).symm, ?_, ?_, ?_⟩
  · refine (q _).continuousOn_symm.mono ?_
    intro v hv
    have := hv.1.2
    simp only [hV₀, Set.mem_iInter] at this
    exact this i hit
  · intro v hv
    have hvt : v ∈ (q ((i : (p ⁻¹' {x} : Set E)) : E)).target := by
      have := hv.1.2
      simp only [hV₀, Set.mem_iInter] at this
      exact this i hit
    have hcf := congrFun (hpq ((i : (p ⁻¹' {x} : Set E)) : E))
      ((q ((i : (p ⁻¹' {x} : Set E)) : E)).symm v)
    rw [hcf]
    exact (q _).right_inv hvt
  · have hcf := congrFun (hpq ((i : (p ⁻¹' {x} : Set E)) : E)) e
    rw [hcf]
    exact (q _).left_inv hei

/-- **Path lifting** for a proper local homeomorphism.  The proof is Mathlib's
for covering maps, with `exists_uniform_sections` in place of the
trivializations. -/
theorem exists_path_lifts [T2Space X] [LocallyCompactSpace X] {p : E → X}
    (hp : IsLocalHomeomorph p) (hproper : ∀ K : Set X, IsCompact K → IsCompact (p ⁻¹' K))
    (γ : C(↑unitInterval, X)) (e : E) (γ_0 : γ 0 = p e) :
    ∃ Γ : C(↑unitInterval, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  classical
  choose V hVopen hxV hsec using exists_uniform_sections hp hproper
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun x : X => (hVopen x).preimage γ.continuous)
      (fun s _ => Set.mem_iUnion.2 ⟨γ s, hxV _⟩)
  suffices h : ∀ n, ∃ Γ : ↑unitInterval → E, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
      (Set.Icc 0 (t n)).EqOn (p ∘ Γ) γ ∧ Γ 0 = e by
    obtain ⟨Γ, cont, eqOn, Γ_0⟩ := h n_max
    rw [h_max _ le_rfl] at cont eqOn
    exact ⟨⟨Γ, continuousOn_univ.mp
      (by convert! cont; rw [eq_comm, Set.eq_univ_iff_forall]; exact fun s => ⟨bot_le, le_top⟩)⟩,
      funext fun _ => eqOn ⟨bot_le, le_top⟩, Γ_0⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => e, continuous_const.continuousOn, fun s hs => ?_, rfl⟩
    rw [t_0, Set.Icc_self, Set.mem_singleton_iff] at hs
    subst hs
    exact γ_0.symm
  | succ n ih => ?_
  obtain ⟨Γ, cont, eqOn, Γ_0⟩ := ih
  obtain ⟨x, hx_sub⟩ := t_sub n
  have pΓtn : p (Γ (t n)) = γ (t n) := eqOn ⟨t_0 ▸ t_mono n.zero_le, le_rfl⟩
  have hmemV : Γ (t n) ∈ p ⁻¹' (V x) := by
    show p (Γ (t n)) ∈ V x
    rw [pΓtn]
    exact hx_sub ⟨le_rfl, t_mono n.le_succ⟩
  obtain ⟨sec, secCont, secLift, secPt⟩ := hsec x _ hmemV
  rw [pΓtn] at secPt
  refine ⟨fun s => if s ≤ t n then Γ s else sec (γ s),
    .if (fun s hs => ?_) (cont.mono fun _ h => ?_) ?_, fun s hs => ?_, ?_⟩
  · cases frontier_Iic_subset _ hs.2
    exact secPt.symm
  · rw [closure_le_eq continuous_id' continuous_const] at h
    exact ⟨h.1.1, h.2⟩
  · refine secCont.comp γ.continuous.continuousOn ?_
    intro s h
    simp only [not_le] at h
    exact hx_sub ⟨closure_lt_subset_le continuous_const continuous_subtype_val h.2, h.1.2⟩
  · rw [Function.comp_apply]
    split_ifs with hle
    · exact eqOn ⟨hs.1, hle⟩
    · exact secLift _ (hx_sub ⟨le_of_not_ge hle, hs.2⟩)
  · dsimp only
    rwa [ite_eq_left (t_0 ▸ t_mono n.zero_le)]

/-- A proper local homeomorphism onto a connected space is surjective: its image
is open (local homeomorphism) and closed (properness). -/
theorem surjective_of_proper [T2Space X] [LocallyCompactSpace X] [ConnectedSpace X] [Nonempty E]
    {p : E → X} (hp : IsLocalHomeomorph p)
    (hproper : ∀ K : Set X, IsCompact K → IsCompact (p ⁻¹' K)) :
    Function.Surjective p := by
  have hopen : IsOpen (Set.range p) := hp.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range p) := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
    have h1 : x ∈ interior K := mem_interior_iff_mem_nhds.2 hKn
    have h2 : interior K ∩ closure (Set.range p) ⊆ closure (interior K ∩ Set.range p) :=
      isOpen_interior.inter_closure
    have h3 : interior K ∩ Set.range p ⊆ p '' (p ⁻¹' K) := by
      rintro z ⟨hz1, w, rfl⟩
      exact ⟨w, (interior_subset hz1 : p w ∈ K), rfl⟩
    have h4 : IsClosed (p '' (p ⁻¹' K)) := ((hproper K hKc).image hp.continuous).isClosed
    have h5 : x ∈ p '' (p ⁻¹' K) := h4.closure_subset (closure_mono h3 (h2 ⟨h1, hx⟩))
    obtain ⟨w, -, rfl⟩ := h5
    exact ⟨w, rfl⟩
  rcases (isClopen_iff (s := Set.range p)).1 ⟨hclosed, hopen⟩ with h | h
  · exact absurd h (by simp [Set.range_eq_empty_iff])
  · intro x
    have : x ∈ Set.range p := h ▸ Set.mem_univ x
    exact this

/-- A proper local homeomorphism from a path-connected space onto a simply
connected space is injective.  This is §7(iii): lift the null-homotopy of the
loop `p ∘ γ`, where `γ` joins the two preimages. -/
theorem injective_of_proper [T2Space E] [T2Space X] [LocallyCompactSpace X]
    [PathConnectedSpace E] [SimplyConnectedSpace X] {p : E → X}
    (hp : IsLocalHomeomorph p)
    (hproper : ∀ K : Set X, IsCompact K → IsCompact (p ⁻¹' K)) :
    Function.Injective p := by
  classical
  have sep : IsSeparatedMap p := T2Space.isSeparatedMap p
  have inj : IsLocallyInjective p := hp.isLocallyInjective
  intro x₁ x₂ hx
  obtain ⟨γ⟩ := PathConnectedSpace.joined x₁ x₂
  -- the image loop
  set βc : C(↑unitInterval, X) := ⟨p ∘ γ, hp.continuous.comp γ.continuous⟩ with hβc
  have hβ0 : βc 0 = p x₁ := by simp [hβc]
  have hβ1 : βc 1 = p x₁ := by simp [hβc, ← hx]
  set β : Path (p x₁) (p x₁) := ⟨βc, hβ0, hβ1⟩ with hβ
  -- it is null-homotopic
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic β (Path.refl (p x₁))
  -- lift every stage of the homotopy, starting at `x₁`
  have hstart : ∀ t : ↑unitInterval, (H.curry t) 0 = p x₁ := by
    intro t
    rw [ContinuousMap.Homotopy.curry_apply]
    exact (H.eq_fst t (by simp)).trans hβ0
  choose Γ Γlifts Γ0 using fun t : ↑unitInterval =>
    exists_path_lifts hp hproper (H.curry t) x₁ (hstart t)
  have hmono := hp.monodromy_theorem sep H Γ
    (fun t s => by
      have h := congrFun (Γlifts t) s
      simpa [ContinuousMap.Homotopy.curry_apply] using h)
    (fun t => by rw [Γ0, Γ0]) 1
  -- the lift at time `0` is `γ`, the lift at time `1` is constant
  have h0 : Γ 0 = (γ : C(↑unitInterval, E)) := by
    refine ContinuousMap.ext fun s => congrFun (sep.eq_of_comp_eq inj (Γ 0).continuous
      γ.continuous ?_ 0 ?_) s
    · rw [Γlifts 0]
      ext s
      rw [ContinuousMap.Homotopy.curry_apply]
      exact H.apply_zero s
    · rw [Γ0]; exact γ.source.symm
  have h1 : Γ 1 = (ContinuousMap.const ↑unitInterval x₁) := by
    refine ContinuousMap.ext fun s => congrFun (sep.eq_of_comp_eq inj (Γ 1).continuous
      continuous_const ?_ 0 ?_) s
    · rw [Γlifts 1]
      ext s
      rw [ContinuousMap.Homotopy.curry_apply]
      exact H.apply_one s
    · rw [Γ0]; rfl
  rw [h0, h1] at hmono
  simpa using hmono

/-- A continuous, open, locally injective map is a local homeomorphism. -/
theorem isLocalHomeomorph_of_isOpenMap_isLocallyInjective {f : E → X} (hc : Continuous f)
    (ho : IsOpenMap f) (hi : IsLocallyInjective f) : IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hi x
  refine ⟨U, hUopen.mem_nhds hxU, Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hc.comp continuous_subtype_val) (fun a b hab => Subtype.ext (hUinj a.2 b.2 hab)) ?_⟩
  intro V hV
  have h1 : IsOpen ((Subtype.val : U → E) '' V) := hUopen.isOpenMap_subtype_val V hV
  have h2 : U.domRestrict f '' V = f '' ((Subtype.val : U → E) '' V) := by
    ext y
    simp only [Set.mem_image, Set.domRestrict_apply, Set.mem_image, exists_exists_and_eq_and]
  rw [h2]
  exact ho _ h1

end ProperLH

/-! ### The differential of `Φ` is invertible

`extension_jacobian_ne_zero` says `|Φ_z̄| ≠ |Φ_z|` in Wirtinger form.  Turning
that into an invertible `ℂ ≃L[ℝ] ℂ` is the same algebra as `wDerivEquiv` above,
for a general `ℝ`-linear `L = A·v + B·v̄`.  Only `|A|² - |B|² ≠ 0` is used — the
explicit inverse `y ↦ (Ā y - B ȳ)/(|A|² - |B|²)` does not care about the sign —
so the hypothesis is the nondegenerate one. -/

namespace WirtInv

/-- An `ℝ`-linear self-map `L` of `ℂ` whose Wirtinger derivatives satisfy
`|L_z̄| ≠ |L_z|` — that is, `‖L 1 + i·L i‖ ≠ ‖L 1 - i·L i‖` — is invertible. -/
theorem exists_equiv_of_wirtinger (L : ℂ →L[ℝ] ℂ)
    (h : ‖L 1 + Complex.I * L Complex.I‖ ≠ ‖L 1 - Complex.I * L Complex.I‖) :
    ∃ L' : ℂ ≃L[ℝ] ℂ, (L' : ℂ →L[ℝ] ℂ) = L := by
  set A : ℂ := (L 1 - Complex.I * L Complex.I) / 2 with hA
  set B : ℂ := (L 1 + Complex.I * L Complex.I) / 2 with hB
  have hnA : ‖A‖ = ‖L 1 - Complex.I * L Complex.I‖ / 2 := by
    rw [hA, norm_div]; norm_num
  have hnB : ‖B‖ = ‖L 1 + Complex.I * L Complex.I‖ / 2 := by
    rw [hB, norm_div]; norm_num
  have hBA : ‖B‖ ≠ ‖A‖ := by
    rw [hnA, hnB]
    intro hc
    exact h (by linarith)
  set d : ℝ := ‖A‖ ^ 2 - ‖B‖ ^ 2 with hd
  have hdne : ((d : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    rw [hd]
    intro hc
    apply hBA
    have hsq : ‖B‖ ^ 2 = ‖A‖ ^ 2 := by linarith
    rw [← Real.sqrt_sq (norm_nonneg B), hsq, Real.sqrt_sq (norm_nonneg A)]
  have hdcast : ((d : ℝ) : ℂ) = ((‖A‖ ^ 2 : ℝ) : ℂ) - ((‖B‖ ^ 2 : ℝ) : ℂ) := by
    rw [hd]; push_cast; ring
  have hAA : A * star A = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hBB : B * star B = ((‖B‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hLform : ∀ v : ℂ, L v = A * v + B * star v := by
    intro v
    have hv : v = ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im v).symm
    have hsv : star v = ((v.re : ℝ) : ℂ) - ((v.im : ℝ) : ℂ) * Complex.I := by
      rw [Complex.star_def]; simp [Complex.ext_iff]
    have hsplit : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
      simp only [Complex.real_smul, mul_one]; exact hv
    have key : ∀ (r m : ℝ) (a b : ℂ), ((r : ℝ) : ℂ) * a + ((m : ℝ) : ℂ) * b
        = ((a - Complex.I * b) / 2) * (((r : ℝ) : ℂ) + ((m : ℝ) : ℂ) * Complex.I)
          + ((a + Complex.I * b) / 2) * (((r : ℝ) : ℂ) - ((m : ℝ) : ℂ) * Complex.I) := by
      intro r m a b
      linear_combination (((m : ℝ) : ℂ) * b) * Complex.I_mul_I
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.real_smul]
    rw [hA, hB, key v.re v.im (L 1) (L Complex.I), ← hv, ← hsv]
  set M : ℂ →L[ℝ] ℂ :=
    (((d : ℝ) : ℂ)⁻¹ * star A) • (ContinuousLinearMap.id ℝ ℂ)
      + (-(((d : ℝ) : ℂ)⁻¹ * B)) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) with hM
  have hMform : ∀ y : ℂ, M y = ((d : ℝ) : ℂ)⁻¹ * (star A * y - B * star y) := by
    intro y
    simp only [hM, add_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      smul_eq_mul, ← Complex.star_def]
    ring
  refine ⟨ContinuousLinearEquiv.equivOfInverse L M ?_ ?_, rfl⟩
  · intro y
    rw [hMform, hLform y]
    have hst : star (A * y + B * star y) = star A * star y + star B * y := by
      simp only [star_add, star_mul, star_star]; ring
    rw [hst]
    have hgoal : star A * (A * y + B * star y) - B * (star A * star y + star B * y)
        = ((d : ℝ) : ℂ) * y := by
      rw [hdcast]; linear_combination (y : ℂ) * hAA - (y : ℂ) * hBB
    rw [hgoal, inv_mul_cancel_left₀ hdne]
  · intro y
    rw [hLform, hMform y]
    have hst : star (((d : ℝ) : ℂ)⁻¹ * (star A * y - B * star y))
        = ((d : ℝ) : ℂ)⁻¹ * (A * star y - star B * y) := by
      simp only [star_mul, star_sub, star_inv₀, Complex.star_def, Complex.conj_ofReal,
        Complex.conj_conj]
      ring
    rw [hst]
    have hinner : A * (star A * y - B * star y) + B * (A * star y - star B * y)
        = ((d : ℝ) : ℂ) * y := by
      rw [hdcast]; linear_combination (y : ℂ) * hAA - (y : ℂ) * hBB
    calc A * (((d : ℝ) : ℂ)⁻¹ * (star A * y - B * star y))
          + B * (((d : ℝ) : ℂ)⁻¹ * (A * star y - star B * y))
        = ((d : ℝ) : ℂ)⁻¹ * (A * (star A * y - B * star y)
            + B * (A * star y - star B * y)) := by ring
      _ = ((d : ℝ) : ℂ)⁻¹ * (((d : ℝ) : ℂ) * y) := by rw [hinner]
      _ = y := inv_mul_cancel_left₀ hdne y

end WirtInv

/-- `Φ` is a local homeomorphism at every interior point: it is real-analytic
there, and its differential is invertible by the Jacobian half of Theorem 1. -/
theorem exists_localHomeomorph_extension (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧ ⇑e = extension φ := by
  have hball : z ∈ Metric.ball (0:ℂ) 1 := by simpa using hz
  have hΦan : AnalyticAt ℝ (extension φ) z :=
    Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp
      (extension_analyticOn_disk φ hφ hφc) z hball
  obtain ⟨L, hL⟩ := WirtInv.exists_equiv_of_wirtinger (fderiv ℝ (extension φ) z)
    (extension_jacobian_ne_zero φ hφ hφc z hz)
  have hstrict : HasStrictFDerivAt (extension φ) (L : ℂ →L[ℝ] ℂ) z := by
    rw [hL]; exact hΦan.hasStrictFDerivAt
  exact ⟨hstrict.toOpenPartialHomeomorph (extension φ),
    hstrict.mem_toOpenPartialHomeomorph_source, hstrict.toOpenPartialHomeomorph_coe⟩

set_option maxHeartbeats 1000000 in
/-- **The topological half of Theorem 1**: `Φ` is injective on `D̄` and onto
`D̄`.  This used to be cited; it is now derived from the Jacobian half
(`extension_jacobian_ne_zero`) by the covering-space argument of §7. -/
theorem extension_injOn_surjOn (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    Set.InjOn (extension φ) (Metric.closedBall (0:ℂ) 1) ∧
      Set.SurjOn (extension φ) (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) := by
  classical
  have hDopen : IsOpen (Metric.ball (0:ℂ) 1) := Metric.isOpen_ball
  have hmaps : ∀ z ∈ Metric.ball (0:ℂ) 1, extension φ z ∈ Metric.ball (0:ℂ) 1 := by
    intro z hz
    simpa using extension_mem_disk φ hφ hφc z (by simpa using hz)
  have : LocallyCompactSpace (Metric.ball (0:ℂ) 1) := hDopen.locallyCompactSpace
  have : PathConnectedSpace (Metric.ball (0:ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.1
      ((convex_ball (0:ℂ) 1).isPathConnected ⟨0, by simp⟩)
  have : ContractibleSpace (Metric.ball (0:ℂ) 1) :=
    (convex_ball (0:ℂ) 1).contractibleSpace ⟨0, by simp⟩
  have : Nonempty (Metric.ball (0:ℂ) 1) := ⟨⟨0, by simp⟩⟩
  set p : Metric.ball (0:ℂ) 1 → Metric.ball (0:ℂ) 1 :=
    fun z => ⟨extension φ (z : ℂ), hmaps _ z.2⟩ with hpdef
  have hcontOn : ContinuousOn (extension φ) (Metric.ball (0:ℂ) 1) :=
    (continuousOn_extension φ hφ hφc).mono Metric.ball_subset_closedBall
  have hpcont : Continuous p :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.1 hcontOn) _
  have hlocinj : IsLocallyInjective p := by
    intro x
    obtain ⟨e, hxe, hecoe⟩ := exists_localHomeomorph_extension φ hφ hφc
      (mem_ball_zero_iff.1 x.2)
    refine ⟨(Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) ⁻¹' e.source,
      e.open_source.preimage continuous_subtype_val, hxe, ?_⟩
    intro a ha b hb hab
    have h1 : extension φ (a : ℂ) = extension φ (b : ℂ) := congrArg Subtype.val hab
    rw [← hecoe] at h1
    exact Subtype.ext (e.injOn ha hb h1)
  have hpopen : IsOpenMap p := by
    intro W hW
    have hWval : IsOpen ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' W) :=
      hDopen.isOpenMap_subtype_val W hW
    have hWsub : (Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' W ⊆ Metric.ball (0:ℂ) 1 := by
      rintro _ ⟨a, -, rfl⟩; exact a.2
    have himgopen :
        IsOpen (extension φ '' ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' W)) := by
      rw [isOpen_iff_forall_mem_open]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨e, hwe, hecoe⟩ := exists_localHomeomorph_extension φ hφ hφc
        (show ‖w‖ < 1 by simpa using hWsub hw)
      refine ⟨extension φ ''
        (((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' W) ∩ e.source),
        Set.image_mono Set.inter_subset_left, ?_, ⟨w, ⟨hw, hwe⟩, rfl⟩⟩
      rw [← hecoe]
      exact e.isOpen_image_of_subset_source (hWval.inter e.open_source) Set.inter_subset_right
    have heq : p '' W = (Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) ⁻¹'
        (extension φ '' ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' W)) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨(a : ℂ), ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨c, ⟨a, ha, rfl⟩, hc⟩
        exact ⟨a, ha, Subtype.ext hc⟩
    rw [heq]
    exact himgopen.preimage continuous_subtype_val
  have hlh : IsLocalHomeomorph p :=
    ProperLH.isLocalHomeomorph_of_isOpenMap_isLocallyInjective hpcont hpopen hlocinj
  have hproper : ∀ K : Set (Metric.ball (0:ℂ) 1), IsCompact K → IsCompact (p ⁻¹' K) := by
    intro K hK
    have hKcc : IsCompact ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' K) :=
      hK.image continuous_subtype_val
    have hKcD : (Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' K ⊆ Metric.ball (0:ℂ) 1 := by
      rintro _ ⟨a, -, rfl⟩; exact a.2
    have himg : (Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' (p ⁻¹' K)
        = Metric.closedBall (0:ℂ) 1
          ∩ (extension φ) ⁻¹' ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' K) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨Metric.ball_subset_closedBall a.2, ⟨p a, ha, rfl⟩⟩
      · rintro ⟨hz1, hz2⟩
        have hzD : z ∈ Metric.ball (0:ℂ) 1 := by
          rcases lt_or_eq_of_le (show ‖z‖ ≤ 1 by simpa using hz1) with hlt | heq
          · simpa using hlt
          · exfalso
            have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
            have hb : ‖extension φ z‖ = 1 := by
              rw [extension_eq_boundary φ ⟨z, hmem⟩]; exact Circle.norm_coe _
            have hlt : ‖extension φ z‖ < 1 := by simpa using hKcD hz2
            linarith
        obtain ⟨a, ha, hav⟩ := hz2
        refine ⟨⟨z, hzD⟩, ?_, rfl⟩
        show p ⟨z, hzD⟩ ∈ K
        have hpa : p ⟨z, hzD⟩ = a := Subtype.ext hav.symm
        rw [hpa]
        exact ha
    have hcl : IsClosed (Metric.closedBall (0:ℂ) 1
        ∩ (extension φ) ⁻¹' ((Subtype.val : Metric.ball (0:ℂ) 1 → ℂ) '' K)) :=
      (continuousOn_extension φ hφ hφc).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall hKcc.isClosed
    have hcpt := (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset hcl Set.inter_subset_left
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact hcpt
  have hinj := ProperLH.injective_of_proper hlh hproper
  have hsurj := ProperLH.surjective_of_proper hlh hproper
  constructor
  · intro z₁ h₁ z₂ h₂ heq
    have hn₁ : ‖z₁‖ ≤ 1 := by simpa using h₁
    have hn₂ : ‖z₂‖ ≤ 1 := by simpa using h₂
    rcases lt_or_eq_of_le hn₁ with hl₁ | he₁ <;> rcases lt_or_eq_of_le hn₂ with hl₂ | he₂
    · have hh := hinj (a₁ := ⟨z₁, by simpa using hl₁⟩) (a₂ := ⟨z₂, by simpa using hl₂⟩)
        (Subtype.ext heq)
      exact congrArg Subtype.val hh
    · exfalso
      have hm₂ : z₂ ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 he₂
      have hb : ‖extension φ z₂‖ = 1 := by
        rw [extension_eq_boundary φ ⟨z₂, hm₂⟩]; exact Circle.norm_coe _
      have hlt := extension_mem_disk φ hφ hφc z₁ hl₁
      rw [heq] at hlt
      linarith
    · exfalso
      have hm₁ : z₁ ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 he₁
      have hb : ‖extension φ z₁‖ = 1 := by
        rw [extension_eq_boundary φ ⟨z₁, hm₁⟩]; exact Circle.norm_coe _
      have hlt := extension_mem_disk φ hφ hφc z₂ hl₂
      rw [← heq] at hlt
      linarith
    · have hm₁ : z₁ ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 he₁
      have hm₂ : z₂ ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 he₂
      rw [extension_eq_boundary φ ⟨z₁, hm₁⟩, extension_eq_boundary φ ⟨z₂, hm₂⟩] at heq
      have hh := hφ.1 (Subtype.ext heq)
      exact congrArg Subtype.val hh
  · intro w hw
    have hn : ‖w‖ ≤ 1 := by simpa using hw
    rcases lt_or_eq_of_le hn with hl | he
    · obtain ⟨z, hz⟩ := hsurj ⟨w, by simpa using hl⟩
      exact ⟨(z : ℂ), Metric.ball_subset_closedBall z.2, congrArg Subtype.val hz⟩
    · have hm : w ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 he
      obtain ⟨ζ, hζ⟩ := hφ.2 ⟨w, hm⟩
      refine ⟨(ζ : ℂ), by simp [Metric.mem_closedBall], ?_⟩
      rw [extension_eq_boundary φ ζ, hζ]

/-- **Theorem 1**, homeomorphism part: `Φ = E(φ)` maps the closed disk
bijectively and continuously (both ways) onto itself. -/
theorem extension_isHomeomorphOn (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) :
    Set.BijOn (extension φ) (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) ∧
      ContinuousOn (extension φ) (Metric.closedBall (0:ℂ) 1) ∧
      ∃ ext_inv : ℂ → ℂ, ContinuousOn ext_inv (Metric.closedBall (0:ℂ) 1) ∧
        Set.InvOn ext_inv (extension φ)
          (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) := by
  obtain ⟨hinj, hsurj⟩ := extension_injOn_surjOn φ hφ hφc
  have hbij : Set.BijOn (extension φ) (Metric.closedBall (0:ℂ) 1) (Metric.closedBall (0:ℂ) 1) :=
    ⟨mapsTo_extension φ hφ hφc, hinj, hsurj⟩
  have hcont := continuousOn_extension φ hφ hφc
  exact ⟨hbij, hcont,
    exists_continuousOn_invOn_of_bijOn (isCompact_closedBall (0:ℂ) 1) hcont hbij⟩

/-! ### The Jacobian with a sign

`extension_jacobian_ne_zero` is Theorem 1's Jacobian clause, and it is
sign-free because Theorem 1 is: `E` extends orientation-reversing
homeomorphisms as happily as orientation-preserving ones, and `E(ζ ↦ ζ⁻¹)` is
`z ↦ z̄`, a perfectly good real-analytic diffeomorphism of `D` with negative
Jacobian.

Sections 6 and 7 of the paper are a different matter.  There `Φ` has to be a
*quasiconformal* map with `|μ| < 1`, and `μ = Φ_z̄/Φ_z` needs `Φ_z ≠ 0` — not
just `|Φ_z| ≠ |Φ_z̄|` — and the sign is exactly what supplies it.  So the strict
form is kept here, with the hypothesis it requires.  Both statements descend
from Lemma 3 through the change of variables of §4.3, which is proved in
`ZDeriv`; the difference between them is which form of Lemma 3 they use, and
`HasIncreasingLift` is what separates them.  Both are proved. -/

/-- **Lemma 3 in the form the strict Jacobian uses.**  This is
`exists_implicit_fderiv_z` with `<` in place of `≠`, and `hor` is what the
sign costs: without it the conclusion is refuted by
`extension_jacobian_ne_zero_false`.

**Proved**, and with it this file is free of `sorry`.  The proof is
`exists_implicit_fderiv_z`'s, through the same normalized map
`χ = ψ_{g_w} ∘ φ ∘ ψ_{g_{-z}}` and the same formula (3.2) at the origin, with
`CircleLift.norm_fourier_ne` replaced by `CircleLift.norm_fourier_lt` — Lemma 3
with its sign.

That replacement is the whole of the extra work, and it is not free: it asks
for `HasIncreasingLift χ`.  The dichotomy `CircleLift.exists_strictMono_lift`
gives `χ` a monotone lift but cannot say which way it runs, so the two Möbius
factors have to be handled by hand.  They are, in
`CircleLift.hasIncreasingLift_of_isDiskAutPlus`: for real `r` the map
`ζ ↦ (ζ - r)/(1 - rζ)` has the lift `t + 2 arctan(r sin t/(1 - r cos t))`,
whose derivative is the Poisson kernel and hence positive, and a general
element of `G₊` is that one conjugated by rotations.
`CircleLift.hasIncreasingLift_comp` then composes the three lifts. -/
theorem exists_implicit_fderiv_z_of_orient (φ : Circle → Circle)
    (hφ : Function.Bijective φ) (hφc : Continuous φ) (hor : HasIncreasingLift φ)
    (z : ℂ) (hz : ‖z‖ < 1) (M : ℂ × ℂ →L[ℝ] ℂ)
    (hM : HasFDerivAt (fun p : ℂ × ℂ => baryFn φ p.1 p.2) M (z, extension φ z)) :
    ‖M (1, 0) + Complex.I * M (Complex.I, 0)‖
      < ‖M (1, 0) - Complex.I * M (Complex.I, 0)‖ :=
  ZDeriv.exists_implicit_fderiv_z_of_orient' φ hφ hφc hor z hz M hM

/-- **Theorem 1, Jacobian part, with a sign**: for an orientation-preserving
`φ` the Jacobian of `Φ` is positive, not merely nonzero.

This is what Sections 6 and 7 use, through `wirtZ_extension_ne_zero`: a
positive Jacobian gives `Φ_z ≠ 0`, which a nonzero one does not.  Formula (3.3)
reappears here — `baryFn_wirtW_nondegenerate` — because the strict elimination
`norm_lt_of_implicit` needs both positivity facts, whereas the sign-free
`norm_ne_of_implicit` needs neither. -/
theorem extension_jacobian_pos (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        + Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖
      < ‖(fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) 1
        - Complex.I * (fderiv ℝ (extension φ) z : ℂ →L[ℝ] ℂ) Complex.I‖ := by
  obtain ⟨L, M, hΦ, hF, hform, -⟩ := exists_implicit_fderiv φ hφ hφc z hz
  have hFw := baryFn_wirtW_nondegenerate φ hφ hφc hz
    (extension_mem_disk φ hφ hφc z hz) M hform
  exact extension_jacobian_of_implicit φ hφ hφc z hz L hΦ M hF hFw
    (exists_implicit_fderiv_z_of_orient φ hφ hφc hor z hz M hF)

/-! ### The remark following Theorem 1: `E` is the *only* such operator

Three repairs before the remark can be proved.

*It is a statement about extension operators.*  The hypotheses said nothing
about `E' φ` extending `φ`, nor about it taking values in `D̄`.  Both are part
of what "extension operator" means, both are needed, and both are supplied by
`E` itself: `hbdry` is what settles the boundary, and `hmaps` is what keeps
`E' φ z` away from the pole of `g_w` in the last step.

*Naturality holds on `D̄`, not on `ℂ`.*  The hypothesis quantified over every
`z`.  Outside the closed disk `E` is the junk value `0`
(`extension_eq_zero_of_one_lt`) and naturality fails there — the file already
records this — so the old hypothesis was one that `E` itself does not satisfy,
while the old conclusion asserted `E' = E` outside the disk as well.  Both are
now cut to `‖z‖ ≤ 1`.

*The junk `φ` again.*  `E(φ)` is `Classical.choose` at a `φ` that is not a
homeomorphism, so the conclusion cannot speak about those; `hnat` and `hnorm`
are correspondingly asked only where `E` supplies them.

With those, `hnat` is *verbatim* `extension_naturality` and `hnorm` is
`extension_zero_of_mean_zero`, so the hypotheses are exactly "`E'` does what `E`
does", which is what a uniqueness statement should say.
`extension_satisfies_unique_characterization` below checks this is not vacuous.

The proof is the paper's normalization.  Given `φ` and `z ∈ D`, put
`w = E(φ)(z)` and move both to the origin: `φ' = ψ_{g_w} ∘ φ ∘ ψ_{g_{-z}}`.
Then `φ'` has mean value zero — because the mean over `S¹` is `⨍ · dη_0`, and
`harmonicMeasureAvg_naturality` transports `η_0` to `η_z` along `g_{-z}`, turning
the mean of `φ'` into `⨍ g_w ∘ φ dη_z`, which is exactly the barycentric
equation `baryEq φ z w`.  So `hnorm` gives `E' φ' 0 = 0`, `hnat` gives
`E' φ' 0 = g_w(E' φ z)`, and `g_w` kills only `w`. -/

/-- `E(φ)(0) = 0` exactly when `φ` has mean value zero: at the centre harmonic
measure is the uniform measure (`harmonicMeasureAvg_zero_eq`) and `g_0 = id`, so
(3.1) at `w = 0` *is* the vanishing of the mean.  Uniqueness of the barycenter
does the rest.  This is the normalization the remark refers to. -/
theorem extension_zero_of_mean_zero (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ)
    (hmean : (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (φ (Circle.exp θ) : ℂ) = 0) :
    extension φ 0 = 0 := by
  have hz : ‖(0:ℂ)‖ < 1 := by norm_num
  obtain ⟨v, -, huniq⟩ := barycenter_existsUnique φ hφ hφc 0 hz
  have hb0 : baryEq φ 0 0 := by
    rw [baryEq_iff_harmonicMeasureAvg, harmonicMeasureAvg_zero_eq]
    simpa [diskAut_zero_left] using hmean
  rw [huniq _ ⟨extension_mem_disk φ hφ hφc 0 hz, extension_baryEq φ hφ hφc 0 hz⟩,
    huniq _ ⟨hz, hb0⟩]

/-- The remark following Theorem 1: `E` is the unique conformally natural
extension operator normalized by `Φ(0) = 0` whenever `φ` has mean value zero. -/
theorem extension_unique_characterization (E' : (Circle → Circle) → ℂ → ℂ)
    (hmaps : ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
      ∀ z : ℂ, ‖z‖ < 1 → ‖E' φ z‖ ≤ 1)
    (hbdry : ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
      ∀ ζ : Circle, E' φ (ζ : ℂ) = (φ ζ : ℂ))
    (hnat : ∀ (φ : Circle → Circle) (g h : ℂ → ℂ) (ψg ψh : Circle → Circle),
      IsDiskAut g → IsDiskAut h →
      (∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) → (∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ)) →
      Function.Bijective φ → Continuous φ →
      Function.Bijective ψg → Function.Bijective ψh →
      ∀ z : ℂ, ‖z‖ ≤ 1 → E' (ψg ∘ φ ∘ ψh) z = g (E' φ (h z)))
    (hnorm : ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (φ (Circle.exp θ) : ℂ) = 0 →
      E' φ 0 = 0) :
    ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
      ∀ z : ℂ, ‖z‖ ≤ 1 → E' φ z = extension φ z := by
  intro φ hφ hφc z hz
  rcases lt_or_eq_of_le hz with hlt | heq
  · have hw : ‖extension φ z‖ < 1 := extension_mem_disk φ hφ hφc z hlt
    set w : ℂ := extension φ z with hwdef
    have hgap : IsDiskAutPlus (diskAut w) := ⟨1, w, by simp, hw, by simp⟩
    have hgbp : IsDiskAutPlus (diskAut (-z)) :=
      ⟨1, -z, by simp, by rwa [norm_neg], by simp⟩
    set ψa : Circle → Circle := diskAutToCircle (diskAut w) (Or.inl hgap) with hψa
    set ψb : Circle → Circle := diskAutToCircle (diskAut (-z)) (Or.inl hgbp) with hψb
    have hbψa : Function.Bijective ψa := bijective_diskAutToCircle _ hgap _
    have hbψb : Function.Bijective ψb := bijective_diskAutToCircle _ hgbp _
    have hb0 : diskAut (-z) 0 = z := by rw [diskAut_zero, neg_neg]
    have hFc : Continuous fun ζ : Circle => diskAut w ((φ ζ : ℂ)) :=
      continuous_diskAut_comp w hw φ hφc
    have hbij : Function.Bijective (ψa ∘ φ ∘ ψb) := hbψa.comp (hφ.comp hbψb)
    have hcont : Continuous (ψa ∘ φ ∘ ψb) :=
      (continuous_diskAutToCircle _ _).comp (hφc.comp (continuous_diskAutToCircle _ _))
    -- the normalized boundary map has mean value zero, by (3.1) at `z`
    have h1 : E' (ψa ∘ φ ∘ ψb) 0 = 0 := by
      refine hnorm (ψa ∘ φ ∘ ψb) hbij hcont ?_
      have hnatm := harmonicMeasureAvg_naturality (diskAut (-z)) (Or.inl hgbp) 0 (by norm_num)
        (fun ζ : Circle => diskAut w ((φ ζ : ℂ))) hFc
      have hzero : harmonicMeasureAvg z (fun ζ : Circle => diskAut w ((φ ζ : ℂ))) = 0 :=
        (baryEq_iff_harmonicMeasureAvg φ z w).1 (extension_baryEq φ hφ hφc z hlt)
      rw [hb0, hzero] at hnatm
      have hE := harmonicMeasureAvg_zero_eq
        (fun ζ : Circle => (((ψa ∘ φ ∘ ψb) ζ : Circle) : ℂ))
      rw [← hE]
      exact hnatm.symm
    have h3 : diskAut w (E' φ z) = 0 := by
      have h2 := hnat φ (diskAut w) (diskAut (-z)) ψa ψb (Or.inl hgap) (Or.inl hgbp)
        (fun _ => rfl) (fun _ => rfl) hφ hφc hbψa hbψb 0 (by simp)
      rw [hb0, h1] at h2
      exact h2.symm
    have hden := diskAut_denom_ne_zero w (E' φ z) hw (hmaps φ hφ hφc z hlt)
    rw [diskAut, div_eq_zero_iff] at h3
    rcases h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hden
  · have hmem : z ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
    exact (hbdry φ hφ hφc ⟨z, hmem⟩).trans (extension_eq_boundary φ ⟨z, hmem⟩).symm

/-- The hypotheses of `extension_unique_characterization` are consistent: `E`
satisfies all four, so the uniqueness statement is about a nonempty class. -/
theorem extension_satisfies_unique_characterization :
    (∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
        ∀ z : ℂ, ‖z‖ < 1 → ‖extension φ z‖ ≤ 1) ∧
      (∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
        ∀ ζ : Circle, extension φ (ζ : ℂ) = (φ ζ : ℂ)) ∧
      (∀ (φ : Circle → Circle) (g h : ℂ → ℂ) (ψg ψh : Circle → Circle),
        IsDiskAut g → IsDiskAut h →
        (∀ ζ : Circle, g (ζ : ℂ) = (ψg ζ : ℂ)) → (∀ ζ : Circle, h (ζ : ℂ) = (ψh ζ : ℂ)) →
        Function.Bijective φ → Continuous φ →
        Function.Bijective ψg → Function.Bijective ψh →
        ∀ z : ℂ, ‖z‖ ≤ 1 → extension (ψg ∘ φ ∘ ψh) z = g (extension φ (h z))) ∧
      (∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ →
        (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), (φ (Circle.exp θ) : ℂ) = 0 →
        extension φ 0 = 0) :=
  ⟨fun φ hφ hφc z hz => (extension_mem_disk φ hφ hφc z hz).le,
    fun φ _ _ ζ => extension_eq_boundary φ ζ,
    fun φ g h ψg ψh hg hh hgb hhb hφ hφc hψg hψh z hz =>
      extension_naturality φ g h ψg ψh hg hh hgb hhb hφ hφc hψg hψh z hz,
    extension_zero_of_mean_zero⟩

/-! ## Section 4: dependence on `φ`

The machinery is already in place: `toComplexMap`, `baryFnMap` and
`exists_analytic_baryEq_solution` were set up with (3.1) in Section 3, because
the smoothness half of Theorem 1 needs them too.  What is left here is the
statement of Proposition 2 itself, and one repair to it.

`E(φ)` is `Classical.choose` over `barycenter_existsUnique`, so at a `φ` that
is not a homeomorphism it is an opaque value about which nothing whatsoever is
provable — not even that it is `0`, since `Classical.choose` does not reduce.
The previous statement of `extension_analytic_jointly` quantified over *every*
`φ : C(S¹, S¹)`, and so asserted that a real-analytic function agrees with that
junk on a whole neighbourhood.  `Function.Bijective` is therefore the paper's
own hypothesis restored, not a convenience.  (The same statement also built its
elements of `C(S¹, ℂ)` with three `sorry`s standing in for the continuity
proofs, so it carried `sorryAx` in its *statement*; `toComplexMap` supplies
them.) -/

/-- **Proposition 2**, boundary continuity: for `ζ ∈ S¹`, `φ ↦ E(φ)(ζ)` is
continuous on `C(S¹, S¹)`.

On the boundary `E` is not doing anything: `extension_eq_boundary` says
`E(φ)(ζ) = φ(ζ)`, so this is continuity of evaluation at `ζ`.  No hypothesis on
`φ` is needed, and none is available — the boundary branch of `extension` is
the only one that is not `Classical.choose`. -/
theorem extension_continuous_boundary (ζ : Circle) :
    Continuous (fun φ : C(Circle, Circle) => extension φ (ζ : ℂ)) := by
  have h : (fun φ : C(Circle, Circle) => extension φ (ζ : ℂ))
      = fun φ : C(Circle, Circle) => ((φ ζ : Circle) : ℂ) :=
    funext fun φ => extension_eq_boundary φ ζ
  rw [h]
  fun_prop

/-- **Proposition 2**, interior analyticity: for `z ∈ D`, `(z, φ) ↦ E(φ)(z)` is
locally the restriction of a real-analytic map of an open subset of
`ℂ × C(S¹, ℂ)`.

The step that is proved here is the identification.  `exists_analytic_baryEq_solution`
produces *an* analytic branch of solutions of (3.1) taking values in `D`; that it
is `E(φ)` is the uniqueness half of `barycenter_existsUnique`, which since it was
proved is available as a theorem.  This is the first consequence of that work
outside the definition of `E` itself.

Uniqueness is also what forces the bijectivity hypothesis to appear here rather
than in the cited input: `barycenter_existsUnique` needs `φ` to be a
homeomorphism, and without it there is nothing to identify the branch with. -/
theorem extension_analytic_jointly (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) (φ₀ : C(Circle, Circle))
    (hφ₀ : Function.Bijective φ₀) :
    ∃ (W : Set (ℂ × C(Circle, ℂ))) (F : ℂ × C(Circle, ℂ) → ℂ),
      IsOpen W ∧ (z₀, toComplexMap φ₀) ∈ W ∧ AnalyticOn ℝ F W ∧
      ∀ (z : ℂ) (φ : C(Circle, Circle)), Function.Bijective φ → ‖z‖ < 1 →
        (z, toComplexMap φ) ∈ W → extension φ z = F (z, toComplexMap φ) := by
  obtain ⟨W, F, hW, hmem, hFan, hsol⟩ := exists_analytic_baryEq_solution z₀ hz₀ φ₀ hφ₀
  refine ⟨W, F, hW, hmem, hFan, fun z φ hbij hz hin => ?_⟩
  obtain ⟨hnorm, heq⟩ := hsol (z, toComplexMap φ) hin hz
  exact extension_eq_of_baryFnMap_eq_zero φ hbij hz hnorm heq

/-- The consequence Proposition 2 exists to provide: near a homeomorphism, `E`
is jointly continuous in the pair `(z, φ)`.  This is where `toComplexMap` earns
its place — being continuous, it pulls the open set of the analytic statement
back to an open set of `ℂ × C(S¹, S¹)`. -/
theorem extension_continuousOn_pair (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) (φ₀ : C(Circle, Circle))
    (hφ₀ : Function.Bijective φ₀) :
    ∃ (V : Set (ℂ × C(Circle, Circle))) (G : ℂ × C(Circle, Circle) → ℂ),
      IsOpen V ∧ (z₀, φ₀) ∈ V ∧ ContinuousOn G V ∧
      ∀ p ∈ V, Function.Bijective p.2 → ‖p.1‖ < 1 → extension p.2 p.1 = G p := by
  obtain ⟨W, F, hW, hmem, hFan, hEq⟩ := extension_analytic_jointly z₀ hz₀ φ₀ hφ₀
  set e : ℂ × C(Circle, Circle) → ℂ × C(Circle, ℂ) := fun p => (p.1, toComplexMap p.2) with he
  have hec : Continuous e := continuous_fst.prodMk (continuous_toComplexMap.comp continuous_snd)
  refine ⟨e ⁻¹' W, F ∘ e, hW.preimage hec, hmem, ?_, ?_⟩
  · exact hFan.continuousOn.comp hec.continuousOn (fun p hp => hp)
  · intro p hp hbij hz
    exact hEq p.1 p.2 hbij hz hp

/-- **Corollary to Proposition 2**: `φ ↦ ∂E(φ)/∂z(0)` and `φ ↦ ∂E(φ)/∂z̄(0)` are
continuous on `Homeo(S¹)`.  The two Wirtinger derivatives are `(dΦ(1) ∓ i dΦ(i))/2`,
so the statement is about the pair `(dΦ(1), dΦ(i))`; `continuousOn_wirt_extension_zero`
restates it in Wirtinger form once `wirtZ` is available.

The proof differentiates Proposition 2 in the first variable.  Freezing `φ`,
`E(φ)` agrees near `0` with the analytic `F` of `extension_analytic_jointly`
composed with the affine slice `z ↦ (z, φ)`, so
`dE(φ)(0) v = d F(0, φ) (v, 0)`; and `dF` is again analytic on `W`
(`AnalyticOnNhd.fderiv`), hence continuous there, so the right-hand side depends
continuously on `φ` through `toComplexMap`.

`ContinuousOn` on the homeomorphisms, rather than `Continuous` on all of
`C(S¹, S¹)`, for the reason given at the head of this section: off the
homeomorphisms `E(φ)` is `Classical.choose` over a hypothesis that fails, and
its differential at `0` is then an opaque value that no continuity statement can
be justified about.  As with `extension_analytic_jointly` this is not
refutable — there is nothing to know about the junk — but the global form
asserts what this development cannot support, and `Homeo(S¹)` is the paper's own
domain. -/
theorem extension_derivative_continuous :
    ContinuousOn (fun φ : C(Circle, Circle) =>
        ((fderiv ℝ (extension φ) 0 : ℂ →L[ℝ] ℂ) 1,
          (fderiv ℝ (extension φ) 0 : ℂ →L[ℝ] ℂ) Complex.I))
      {φ : C(Circle, Circle) | Function.Bijective φ} := by
  intro φ₀ hφ₀
  obtain ⟨W, F, hW, hmem, hFan, hEq⟩ := extension_analytic_jointly 0 (by norm_num) φ₀ hφ₀
  have hFnhd : AnalyticOnNhd ℝ F W := hW.analyticOn_iff_analyticOnNhd.mp hFan
  have hdF : ContinuousOn (fderiv ℝ F) W := hFnhd.fderiv.continuousOn
  set j : C(Circle, Circle) → ℂ × C(Circle, ℂ) := fun φ => (0, toComplexMap φ) with hjdef
  have hjc : Continuous j := continuous_const.prodMk continuous_toComplexMap
  have hVopen : IsOpen (j ⁻¹' W) := hW.preimage hjc
  have hφ₀V : φ₀ ∈ j ⁻¹' W := hmem
  set g : C(Circle, Circle) → ℂ × ℂ := fun φ =>
    (fderiv ℝ F (j φ) (1, 0), fderiv ℝ F (j φ) (Complex.I, 0)) with hgdef
  have h1 : ContinuousOn (fun φ : C(Circle, Circle) => fderiv ℝ F (j φ)) (j ⁻¹' W) :=
    hdF.comp hjc.continuousOn (fun φ hφ => hφ)
  have hgc : ContinuousOn g (j ⁻¹' W) :=
    (h1.clm_apply continuousOn_const).prodMk (h1.clm_apply continuousOn_const)
  have hagree : ∀ φ : C(Circle, Circle), φ ∈ j ⁻¹' W → Function.Bijective φ →
      ((fderiv ℝ (extension φ) 0 : ℂ →L[ℝ] ℂ) 1,
        (fderiv ℝ (extension φ) 0 : ℂ →L[ℝ] ℂ) Complex.I) = g φ := by
    intro φ hφV hbij
    have hmem0 : ((0 : ℂ), toComplexMap φ) ∈ W := hφV
    have hFd : HasFDerivAt F (fderiv ℝ F ((0:ℂ), toComplexMap φ)) ((0:ℂ), toComplexMap φ) :=
      (hFnhd _ hmem0).differentiableAt.hasFDerivAt
    have hslice : HasFDerivAt (fun z : ℂ => (z, toComplexMap φ))
        ((ContinuousLinearMap.id ℝ ℂ).prod 0) (0:ℂ) :=
      (hasFDerivAt_id (0:ℂ)).prodMk (hasFDerivAt_const (toComplexMap φ) (0:ℂ))
    have hcomp := HasFDerivAt.comp (g := F) (f := fun z : ℂ => (z, toComplexMap φ))
      (0:ℂ) hFd hslice
    simp only [Function.comp_def] at hcomp
    have hslc : Continuous (fun z : ℂ => (z, toComplexMap φ)) :=
      continuous_id.prodMk continuous_const
    have hUopen : IsOpen (((fun z : ℂ => (z, toComplexMap φ)) ⁻¹' W) ∩ Metric.ball (0:ℂ) 1) :=
      (hW.preimage hslc).inter Metric.isOpen_ball
    have h0U : (0:ℂ) ∈ ((fun z : ℂ => (z, toComplexMap φ)) ⁻¹' W) ∩ Metric.ball (0:ℂ) 1 :=
      ⟨hmem0, by simp⟩
    have hev : extension φ =ᶠ[nhds (0:ℂ)] fun z : ℂ => F (z, toComplexMap φ) := by
      filter_upwards [hUopen.mem_nhds h0U] with z hz
      have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
      exact hEq z φ hbij hz1 hz.1
    have hext := hcomp.congr_of_eventuallyEq hev
    rw [hext.fderiv]
    simp [hgdef, hjdef]
  have hgw : ContinuousWithinAt g {φ : C(Circle, Circle) | Function.Bijective φ} φ₀ :=
    (hgc.continuousAt (hVopen.mem_nhds hφ₀V)).continuousWithinAt
  refine hgw.congr_of_eventuallyEq ?_ (hagree φ₀ hφ₀V hφ₀)
  filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hφ₀V), self_mem_nhdsWithin] with φ hφV hbij
  exact hagree φ hφV hbij


/-- The Corollary's continuity statement at an arbitrary point of `D`, not only
at the origin.  The proof is the Corollary's, with `0` replaced by `z₀`
throughout: `extension_analytic_jointly` already takes the base point as a
parameter.  `complexDilatation (E(φ))` is built from this. -/
theorem extension_derivative_continuousOn (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) :
    ContinuousOn (fun φ : C(Circle, Circle) =>
        ((fderiv ℝ (extension φ) z₀ : ℂ →L[ℝ] ℂ) 1,
          (fderiv ℝ (extension φ) z₀ : ℂ →L[ℝ] ℂ) Complex.I))
      {φ : C(Circle, Circle) | Function.Bijective φ} := by
  intro φ₀ hφ₀
  obtain ⟨W, F, hW, hmem, hFan, hEq⟩ := extension_analytic_jointly z₀ hz₀ φ₀ hφ₀
  have hFnhd : AnalyticOnNhd ℝ F W := hW.analyticOn_iff_analyticOnNhd.mp hFan
  have hdF : ContinuousOn (fderiv ℝ F) W := hFnhd.fderiv.continuousOn
  set j : C(Circle, Circle) → ℂ × C(Circle, ℂ) := fun φ => (z₀, toComplexMap φ) with hjdef
  have hjc : Continuous j := continuous_const.prodMk continuous_toComplexMap
  have hVopen : IsOpen (j ⁻¹' W) := hW.preimage hjc
  have hφ₀V : φ₀ ∈ j ⁻¹' W := hmem
  set g : C(Circle, Circle) → ℂ × ℂ := fun φ =>
    (fderiv ℝ F (j φ) (1, 0), fderiv ℝ F (j φ) (Complex.I, 0)) with hgdef
  have h1 : ContinuousOn (fun φ : C(Circle, Circle) => fderiv ℝ F (j φ)) (j ⁻¹' W) :=
    hdF.comp hjc.continuousOn (fun φ hφ => hφ)
  have hgc : ContinuousOn g (j ⁻¹' W) :=
    (h1.clm_apply continuousOn_const).prodMk (h1.clm_apply continuousOn_const)
  have hagree : ∀ φ : C(Circle, Circle), φ ∈ j ⁻¹' W → Function.Bijective φ →
      ((fderiv ℝ (extension φ) z₀ : ℂ →L[ℝ] ℂ) 1,
        (fderiv ℝ (extension φ) z₀ : ℂ →L[ℝ] ℂ) Complex.I) = g φ := by
    intro φ hφV hbij
    have hmem0 : (z₀, toComplexMap φ) ∈ W := hφV
    have hFd : HasFDerivAt F (fderiv ℝ F (z₀, toComplexMap φ)) (z₀, toComplexMap φ) :=
      (hFnhd _ hmem0).differentiableAt.hasFDerivAt
    have hslice : HasFDerivAt (fun z : ℂ => (z, toComplexMap φ))
        ((ContinuousLinearMap.id ℝ ℂ).prod 0) z₀ :=
      (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const (toComplexMap φ) z₀)
    have hcomp := HasFDerivAt.comp (g := F) (f := fun z : ℂ => (z, toComplexMap φ))
      z₀ hFd hslice
    simp only [Function.comp_def] at hcomp
    have hslc : Continuous (fun z : ℂ => (z, toComplexMap φ)) :=
      continuous_id.prodMk continuous_const
    have hUopen : IsOpen (((fun z : ℂ => (z, toComplexMap φ)) ⁻¹' W) ∩ Metric.ball (0:ℂ) 1) :=
      (hW.preimage hslc).inter Metric.isOpen_ball
    have h0U : z₀ ∈ ((fun z : ℂ => (z, toComplexMap φ)) ⁻¹' W) ∩ Metric.ball (0:ℂ) 1 :=
      ⟨hmem0, by simpa [Metric.mem_ball, dist_zero_right] using hz₀⟩
    have hev : extension φ =ᶠ[nhds z₀] fun z : ℂ => F (z, toComplexMap φ) := by
      filter_upwards [hUopen.mem_nhds h0U] with z hz
      have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
      exact hEq z φ hbij hz1 hz.1
    have hext := hcomp.congr_of_eventuallyEq hev
    rw [hext.fderiv]
    simp [hgdef, hjdef]
  have hgw : ContinuousWithinAt g {φ : C(Circle, Circle) | Function.Bijective φ} φ₀ :=
    (hgc.continuousAt (hVopen.mem_nhds hφ₀V)).continuousWithinAt
  refine hgw.congr_of_eventuallyEq ?_ (hagree φ₀ hφ₀V hφ₀)
  filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hφ₀V), self_mem_nhdsWithin] with φ hφV hbij
  exact hagree φ hφV hbij

end
