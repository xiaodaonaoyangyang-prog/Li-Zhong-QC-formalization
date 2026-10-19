import References.GarnettMarshall2005.Ch03.S03_EnergyIntegral

/-!
# Garnett–Marshall, Chapter III §4: The equilibrium distribution

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §4 (pp. 82–89;
`full.md` P1:3764–4043).

Conventions as in §1–§3. `E` is a compact plane set, `Ω` the component of `ℂ* \ E` containing `∞`, `{Ω_n}` the
sequences of §1 and `E_n = ℂ \ Ω_n`, `Ê = ℂ \ Ω` (`filledSet`). `P(E)` is the set of Borel probability measures on
`ℂ` carried by `E` (`probMeasuresOn`). Weak-star convergence of measures is convergence of the integrals of every
bounded continuous function (`TendstoWeakStar`; for probability measures carried by a fixed compact set this is the
weak-star convergence in the dual of `C(E)` that the book uses). The energy `I(σ)` of a positive measure is `energy`
(values in `(−∞, +∞]`), the potential `U_μ` is `logPotential`. Capacity: before (4.8) the statements use the capacity
of compact sets (1.3) (`capacityCompact`, `robinConstantCompact`); from (4.8) on, the capacity of arbitrary sets
(`capacity`, `robinConstant`: the most general stage, leader ruling B1), which for compact sets is the same number by
(1.5). `γ(A) = log(1/Cap(A))` takes values in `[−∞, +∞]` (`+∞` for polar sets). Area is `volume` on `ℂ`, and the
length `|E*|` of a subset of `ℝ` is `volume` on `ℝ`.

* Definition (`P(E)`, the Borel probability measures on the compact set `E`, §4, P1:3766) — `probMeasuresOn`
* Theorem 4.1 (§4; (4.1)) — `thm3_4_1_a`, `thm3_4_1_b`, `thm3_4_1_c`
* Definition (the equilibrium distribution `μ_E` of a compact set `E` with `Cap(E) > 0`, the weak-star limit of the
  `μ_{E_n}`; its potential `U_{μ_E}` is the equilibrium potential, §4, P1:3776) — `equilibriumMeasure`
* Lemma 4.2 (§4; (4.2), (4.3)) — `lemma3_4_2_a`, `lemma3_4_2_b`
* Unlabelled (§4, (4.4) and P1:3862–3872): `μ_E` is carried by `∂Ê ⊂ E`, and `μ_E = μ_{∂E} = μ_Ê = μ_{∂Ê}` —
  `equilibriumMeasure_support_eq`
* Definition ((4.8), the capacity of a Borel set; Robin's constant `γ(A) = log(1/Cap(A))`, P1:3371 through (4.8),
  recalled at P1:4439, §4) — `capacity`, `robinConstant`
* Corollary 4.3 (§4) — `cor3_4_3_a`, `cor3_4_3_b`
* Unlabelled (§4, P1:3884–3888): `Cap(A) = 0` implies `Area(A) = 0` — `volume_eq_zero_of_capacity_eq_zero`
* Definition (polar set: a set of capacity zero, §4, P1:3890) — `IsPolarSet`
* Theorem 4.4 (§4; (4.9), (4.10), (4.11)) — `thm3_4_4_a`, `thm3_4_4_b`, `thm3_4_4_c`
* Theorem 4.5 (§4; (4.12)) — `thm3_4_5_a`, `thm3_4_5_b`
* Lemma 4.6 (§4; (4.13)) — `lemma3_4_6`
* Definition (the Cantor set `K = ⋂ K_n`, Example 4.7) — exists: `cantorSet` (Mathlib: the intersection of the
  sets preCantorSet n obtained from the unit interval by removing middle thirds, the book's K_n; a subset of the real
  line, seen in the plane through the coercion)
* Formula (4.14) (§4, Example 4.7; cited at P1:4539 and in App. D, P3:3467) — `eq3_4_14`
* Corollary 4.8 (Koebe one-quarter theorem, §4; (4.15)) — exists: `LiZhongQC.koebe_quarter` (the same hypotheses,
  holomorphic and one-to-one on the unit disc with f(0) = 0 and f′(0) = 1, and the same conclusion, the disc of
  radius 1/4 about 0 lies in the image of the unit disc)

Helper (not a book notion): `TendstoWeakStar` (the weak-star convergence the book uses with `P(E)`, P1:3766).

Not stated (inventory U−): "It follows that `μ_E` is the unique `μ ∈ P(E)` with `U_μ = γ(E)` almost everywhere `dμ`"
(P1:3776, a consequence of Theorem 4.1, not cited); in Theorem 4.5 circular projections can be replaced by vertical
projections (P1:3949, "the proof is the same", not cited); "there exist sets `E ⊂ ℝ` with `|E| = 0` but
`Cap(E) > 0`" (P1:3983; Example 4.7 is its proof); the remark "Theorem 4.5 provides another proof of the Koebe
one-quarter theorem I.4.1" (P1:4022, introducing Corollary 4.8). (4.5)–(4.7) are steps of the proof of Theorem 4.1,
and the map `ψ_*` of (4.13) is the image measure `Measure.map ψ`.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf)
open References (finitePart)

/-- **Definition** (`P(E)`, Ch. III §4, P1:3766). `P(E)` is the set of all Borel probability measures on the compact
set `E`.
Modelling: probability measures on `ℂ` that vanish off `E`. -/
def probMeasuresOn (E : Set ℂ) : Set (Measure ℂ) :=
  {μ | IsProbabilityMeasure μ ∧ μ Eᶜ = 0}

/-- Weak-star convergence of measures (helper, Ch. III §4, P1:3766 and Theorem 4.1; also used in §5): `μ_i → ν`
weak-star along the filter `l` if `∫ f dμ_i → ∫ f dν` for every bounded continuous real function `f`.
Modelling (leader ruling B3): for finite measures this is Mathlib's convergence in the narrow topology of
`FiniteMeasure`; a helper because the book's measures are `Measure`s. For probability measures carried by a fixed
compact set it is the book's weak-star convergence in the dual of the continuous functions on that set. -/
def TendstoWeakStar {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : ι → Measure X) (l : Filter ι)
    (ν : Measure X) : Prop :=
  ∀ f : BoundedContinuousFunction X ℝ, Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν))

/-- **Definition** (the equilibrium distribution, Ch. III §4, P1:3776, through Theorem 4.1). For a compact set `E`
with `Cap(E) > 0`, the sequence `{μ_{E_n}}` of equilibrium distributions of the sets `E_n = ℂ \ Ω_n` (§2) converges
weak-star to a measure `μ_E ∈ P(E)` that does not depend on the sequence `{E_n}`; by definition `μ_E` is the
equilibrium distribution of `E`, and `U_{μ_E}` is called the equilibrium potential.
Modelling (leader ruling B3): the value over all sequences `IsSmoothExhaustion` of `Ω` with `∞ ∈ Ω_n` of the weak-star
limit of `equilibriumMeasureFC (ℂ \ Ω_n)`, as the supremum of the set of such limits; the set is a single point when
`Cap(E) > 0` (Theorem 4.1, `thm3_4_1_a`; a weak-star limit of finite measures is unique). The equilibrium potential is
`logPotential (equilibriumMeasure E)` (no separate name). Junk: for `Cap(E) = 0` (outside the book's definition) the
supremum of the weak-star limits that exist along the sequences: the zero measure when there are none, `δ_p` for
`E = {p}`, and not necessarily a probability measure when the limits differ; every statement assumes
`Cap(E) > 0`. -/
def equilibriumMeasure (E : Set ℂ) : Measure ℂ :=
  sSup {μ : Measure ℂ | ∃ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion (unboundedComponentExt E) Ωs ∧
    (∀ n, extInf ∈ Ωs n) ∧ TendstoWeakStar (fun n => equilibriumMeasureFC (finitePart (Ωs n)ᶜ)) atTop μ}

/-- **Theorem 4.1** (Ch. III §4; cited at P1:3798, 3868, 3882, 3963, 4008, 4052, 4064, in Exercises 4 and 9, P1:5142,
5250, and in App. D, P3:3401, 3423, and App. E, P3:3739), first part. Assume `Cap(E) > 0`. Then the sequence
`{μ_n} = {μ_{E_n}}` converges weak-star to some `μ = μ_E ∈ P(E)`, and the limit does not depend on the choice of the
sequence `{E_n}`.
Modelling: `E` compact (the standing assumption of §4) and `Cap(E)` the capacity (1.3) of compact sets; the limit
along every sequence of §1 is the one measure `equilibriumMeasure E`, which is the independence of the sequence. -/
theorem thm3_4_1_a {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) :
    equilibriumMeasure E ∈ probMeasuresOn E ∧
      ∀ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion (unboundedComponentExt E) Ωs → (∀ n, extInf ∈ Ωs n) →
        TendstoWeakStar (fun n => equilibriumMeasureFC (finitePart (Ωs n)ᶜ)) atTop (equilibriumMeasure E) := by
  sorry

/-- **Theorem 4.1** (Ch. III §4), (4.1) (cited at P1:3798–3824, 3860, 4014, 4122). Assume `Cap(E) > 0`. Then
(4.1) `γ(E) = I(μ_E) = inf {I(σ) : σ ∈ P(E)}`.
Modelling: `E` compact; `γ(E)` is `robinConstantCompact E` and `I` is `energy`, both in `[−∞, +∞]` (the infimum is
over `P(E)`, where `I(σ) ∈ (−∞, +∞]`). -/
theorem thm3_4_1_b {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) :
    robinConstantCompact E = energy (equilibriumMeasure E) ∧
      robinConstantCompact E = ⨅ σ ∈ probMeasuresOn E, energy σ := by
  sorry

/-- **Theorem 4.1** (Ch. III §4), last part. Assume `Cap(E) > 0`. Then `I(σ) > γ(E)` for all `σ ∈ P(E)` with
`σ ≠ μ_E`. In other words, `μ_E` is the unique probability measure on `E` satisfying `γ(E) = I(μ_E)`.
Modelling: `E` compact; comparison in `[−∞, +∞]`. -/
theorem thm3_4_1_c {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) :
    ∀ σ ∈ probMeasuresOn E, σ ≠ equilibriumMeasure E → robinConstantCompact E < energy σ := by
  sorry

/-- Helper (Ch. III §4). The clamp `min (max r e⁻ⁿ) R'` (`R' ≥ 1`) is positive, and `−log` of it is bounded by `n + R'`. -/
theorem gm34_clamp_bound (r : ℝ) {R' : ℝ} (hR' : 1 ≤ R') (n : ℕ) :
    0 < min (max r (Real.exp (-(n : ℝ)))) R' ∧ |-Real.log (min (max r (Real.exp (-(n : ℝ)))) R')| ≤ n + R' := by
  have hε1 : Real.exp (-(n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp
  have hεpos : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hc : Real.exp (-(n : ℝ)) ≤ min (max r (Real.exp (-(n : ℝ)))) R' :=
    le_min (le_max_right _ _) (hε1.trans hR')
  have hpos : 0 < min (max r (Real.exp (-(n : ℝ)))) R' := lt_of_lt_of_le hεpos hc
  refine ⟨hpos, ?_⟩
  have h1 : -(n : ℝ) ≤ Real.log (min (max r (Real.exp (-(n : ℝ)))) R') := by
    have := Real.log_le_log hεpos hc
    rwa [Real.log_exp] at this
  have h2 : Real.log (min (max r (Real.exp (-(n : ℝ)))) R') ≤ R' := by
    refine (Real.log_le_log hpos (min_le_right _ _)).trans ?_
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hR')
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  constructor <;> linarith

/-- Helper (Ch. III §4, Lemma 4.6). The fibre `S ∩ ψ⁻¹{y}` of a continuous map on a compact set has a point of least real
part, and `sInf` of the real parts of the fibre is that least value. -/
theorem gm34_fiber_min {S : Set ℂ} (hS : IsCompact S) {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ S) {y : ℂ}
    (hy : y ∈ ψ '' S) :
    ∃ z ∈ S, ψ z = y ∧ z.re = sInf (Complex.re '' (S ∩ ψ ⁻¹' {y})) ∧
      ∀ z' ∈ S, ψ z' = y → z.re ≤ z'.re := by
  have hcl : IsClosed (S ∩ ψ ⁻¹' {y}) := hψ.preimage_isClosed_of_isClosed hS.isClosed isClosed_singleton
  have hF : IsCompact (S ∩ ψ ⁻¹' {y}) := hS.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨z0, hz0S, hz0y⟩ := hy
  obtain ⟨z, hz, hmin⟩ := hF.exists_isMinOn ⟨z0, hz0S, hz0y⟩ Complex.continuous_re.continuousOn
  have hleast : IsLeast (Complex.re '' (S ∩ ψ ⁻¹' {y})) z.re :=
    ⟨Set.mem_image_of_mem _ hz, by
      rintro _ ⟨z', hz', rfl⟩
      exact hmin hz'⟩
  refine ⟨z, hz.1, hz.2, hleast.csInf_eq.symm, fun z' hz'S hz'y => ?_⟩
  exact hmin ⟨hz'S, hz'y⟩

/-- Helper (Ch. III §4, Lemma 4.6). The fibre-minimum of the real part is a Borel function of `y`. -/
theorem gm34_fiber_min_measurable {S : Set ℂ} (hS : IsCompact S) {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ S) :
    Measurable fun y : ℂ => sInf (Complex.re '' (S ∩ ψ ⁻¹' {y})) := by
  refine measurable_of_Iic fun a => ?_
  have hset : (fun y : ℂ => sInf (Complex.re '' (S ∩ ψ ⁻¹' {y}))) ⁻¹' Set.Iic a =
      ψ '' (S ∩ {z | z.re ≤ a}) ∪ ((ψ '' S)ᶜ ∩ {_y | (0 : ℝ) ≤ a}) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_ofPred_eq]
    by_cases hy : y ∈ ψ '' S
    · obtain ⟨z, hzS, hzy, hzre, hzmin⟩ := gm34_fiber_min hS hψ hy
      constructor
      · intro h
        exact Or.inl ⟨z, ⟨hzS, show z.re ≤ a by rw [hzre]; exact h⟩, hzy⟩
      · rintro (⟨z', ⟨hz'S, hz'a⟩, hz'y⟩ | h)
        · have : sInf (Complex.re '' (S ∩ ψ ⁻¹' {y})) ≤ z'.re :=
            csInf_le ⟨z.re, by rintro _ ⟨w, hw, rfl⟩; exact hzmin w hw.1 hw.2⟩
              (Set.mem_image_of_mem _ ⟨hz'S, hz'y⟩)
          exact this.trans hz'a
        · exact absurd hy h.1
    · have hemp : S ∩ ψ ⁻¹' {y} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun hzS hzy => hy ⟨z, hzS, hzy⟩
      rw [hemp, Set.image_empty, Real.sInf_empty]
      constructor
      · intro h
        exact Or.inr ⟨hy, h⟩
      · rintro (⟨z', ⟨hz'S, -⟩, hz'y⟩ | h)
        · exact absurd ⟨z', hz'S, hz'y⟩ hy
        · exact h.2
  rw [hset]
  have hc1 : IsCompact (ψ '' (S ∩ {z | z.re ≤ a})) :=
    (hS.inter_right (isClosed_le Complex.continuous_re continuous_const)).image_of_continuousOn
      (hψ.mono Set.inter_subset_left)
  have hc2 : IsCompact (ψ '' S) := hS.image_of_continuousOn hψ
  refine hc1.isClosed.measurableSet.union ?_
  by_cases ha : (0 : ℝ) ≤ a
  · simpa [ha] using hc2.isClosed.measurableSet.compl
  · simp [ha]

/-- Helper (Ch. III §4, truncation of the logarithmic kernel). For a finite measure `m` and a measurable `w : X → ℂ`
with `‖w‖ ≤ R` almost everywhere, the bounded truncations `gₙ = −log (clamp ‖w‖ to [e⁻ⁿ, max R 1])` have integrals below
`∫ log⁺ (1/‖w‖) dm − ∫ log⁻ (1/‖w‖) dm` (lower integrals, in `EReal`), and that difference is their supremum. -/
theorem gm34_trunc_generic {X : Type*} [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m] {w : X → ℂ}
    (hw : Measurable w) {R : ℝ} (hR : ∀ᵐ x ∂m, ‖w x‖ ≤ R) :
    (∀ n : ℕ, ((∫ x, -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) (max R 1)) ∂m : ℝ) : EReal) ≤
        ((∫⁻ x, (-ENNReal.log ‖w x‖ₑ).toENNReal ∂m : ℝ≥0∞) : EReal) -
          ((∫⁻ x, (-(-ENNReal.log ‖w x‖ₑ)).toENNReal ∂m : ℝ≥0∞) : EReal)) ∧
      ((∫⁻ x, (-ENNReal.log ‖w x‖ₑ).toENNReal ∂m : ℝ≥0∞) : EReal) -
          ((∫⁻ x, (-(-ENNReal.log ‖w x‖ₑ)).toENNReal ∂m : ℝ≥0∞) : EReal) ≤
        ⨆ n : ℕ, ((∫ x, -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) (max R 1)) ∂m : ℝ) : EReal) := by
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  set g : ℕ → X → ℝ := fun n x => -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') with hg
  have hεpos : ∀ n : ℕ, 0 < Real.exp (-(n : ℝ)) := fun n => Real.exp_pos _
  have hε1 : ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ 1 := fun n => by
    rw [Real.exp_le_one_iff]
    simp
  have hmeas : ∀ n, Measurable (g n) := fun n =>
    (Real.measurable_log.comp ((hw.norm.max measurable_const).min measurable_const)).neg
  have hclamp_pos : ∀ (n : ℕ) (x : X), Real.exp (-(n : ℝ)) ≤ min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R' := fun n x =>
    le_min (le_max_right _ _) ((hε1 n).trans hR'1)
  have hbound : ∀ n x, |g n x| ≤ (n : ℝ) + R' := fun n x => by
    have h1 : -(n : ℝ) ≤ Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') := by
      have := Real.log_le_log (hεpos n) (hclamp_pos n x)
      rwa [Real.log_exp] at this
    have h2 : Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') ≤ R' := by
      refine (Real.log_le_log (lt_of_lt_of_le (hεpos n) (hclamp_pos n x)) (min_le_right _ _)).trans ?_
      have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hR'1)
      linarith
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hR0 : 0 ≤ R' := by linarith
    simp only [hg]
    rw [abs_le]
    constructor <;> linarith
  have hint : ∀ n, Integrable (g n) m := fun n =>
    Integrable.of_bound (hmeas n).aestronglyMeasurable ((n : ℝ) + R')
      (Filter.Eventually.of_forall fun x => by simpa using hbound n x)
  -- pointwise facts on the set `‖w x‖ ≤ R`
  have key : ∀ᵐ x ∂m, (∀ n, ENNReal.ofReal (-(g n x)) = (-(-ENNReal.log ‖w x‖ₑ)).toENNReal) ∧
      (∀ n, ENNReal.ofReal (g n x) ≤ (-ENNReal.log ‖w x‖ₑ).toENNReal) ∧
      ⨆ n, ENNReal.ofReal (g n x) = (-ENNReal.log ‖w x‖ₑ).toENNReal := by
    filter_upwards [hR] with x hx
    have hxR' : ‖w x‖ ≤ R' := hx.trans hRR'
    have hr0 : 0 ≤ ‖w x‖ := norm_nonneg _
    have hePos : ∀ n : ℕ, ‖w x‖ < Real.exp (-(n : ℝ)) → g n x = n := fun n h => by
      simp only [hg]
      rw [max_eq_right h.le, min_eq_left ((hε1 n).trans hR'1), Real.log_exp]
      ring
    have hegt : ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ ‖w x‖ → g n x = -Real.log ‖w x‖ := fun n h => by
      simp only [hg]
      rw [max_eq_left h, min_eq_left hxR']
    rcases hr0.eq_or_lt with h0 | hpos
    · have hw0 : ‖w x‖ₑ = 0 := by
        rw [← ofReal_norm, ← h0]
        simp
      have hP : (-ENNReal.log ‖w x‖ₑ).toENNReal = ⊤ := by simp [hw0]
      have hN : (-(-ENNReal.log ‖w x‖ₑ)).toENNReal = 0 := by simp [hw0]
      have hgn : ∀ n : ℕ, g n x = n := fun n => hePos n (by rw [← h0]; exact hεpos n)
      refine ⟨fun n => ?_, fun n => ?_, ?_⟩
      · rw [hN, hgn]
        simp
      · rw [hP]
        exact le_top
      · rw [hP]
        simp only [hgn, ENNReal.ofReal_natCast]
        exact ENNReal.iSup_natCast
    · have hw : ‖w x‖ₑ = ENNReal.ofReal ‖w x‖ := (ofReal_norm _).symm
      have hlog : ENNReal.log ‖w x‖ₑ = ((Real.log ‖w x‖ : ℝ) : EReal) := by
        rw [hw]
        exact ENNReal.log_ofReal_of_pos hpos
      have hP : (-ENNReal.log ‖w x‖ₑ).toENNReal = ENNReal.ofReal (-Real.log ‖w x‖) := by
        rw [hlog, ← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
      have hN : (-(-ENNReal.log ‖w x‖ₑ)).toENNReal = ENNReal.ofReal (Real.log ‖w x‖) := by
        rw [hlog, neg_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
      have hlt : ∀ n : ℕ, ‖w x‖ < Real.exp (-(n : ℝ)) → Real.log ‖w x‖ < -(n : ℝ) := fun n h => by
        have := Real.log_lt_log hpos h
        rwa [Real.log_exp] at this
      refine ⟨fun n => ?_, fun n => ?_, ?_⟩
      · rw [hN]
        rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
        · rw [hegt n h, neg_neg]
        · rw [hePos n h]
          have h1 : -(n : ℝ) ≤ 0 := by simp
          rw [ENNReal.ofReal_of_nonpos (by simp), ENNReal.ofReal_of_nonpos]
          exact ((hlt n h).trans_le h1).le
      · rw [hP]
        rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
        · rw [hegt n h]
        · rw [hePos n h]
          exact ENNReal.ofReal_le_ofReal (by linarith [hlt n h])
      · refine le_antisymm (iSup_le fun n => ?_) ?_
        · rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
          · rw [hegt n h, hP]
          · rw [hP, hePos n h]
            exact ENNReal.ofReal_le_ofReal (by linarith [hlt n h])
        · obtain ⟨n, hn⟩ := exists_nat_ge (-Real.log ‖w x‖)
          have hle : Real.exp (-(n : ℝ)) ≤ ‖w x‖ := by
            calc Real.exp (-(n : ℝ)) ≤ Real.exp (Real.log ‖w x‖) :=
                  Real.exp_le_exp.2 (by linarith)
              _ = ‖w x‖ := Real.exp_log hpos
          rw [hP, ← hegt n hle]
          exact le_iSup (fun n => ENNReal.ofReal (g n x)) n
  set Pf : X → ℝ≥0∞ := fun x => (-ENNReal.log ‖w x‖ₑ).toENNReal with hPf
  set Nf : X → ℝ≥0∞ := fun x => (-(-ENNReal.log ‖w x‖ₑ)).toENNReal with hNf
  set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂m with hA
  set B : ℝ≥0∞ := ∫⁻ x, Nf x ∂m with hB
  set p : ℝ≥0∞ := ∫⁻ x, Pf x ∂m with hp
  have hBn : ∀ n, ∫⁻ x, ENNReal.ofReal (-(g n x)) ∂m = B := fun n =>
    lintegral_congr_ae (by filter_upwards [key] with x hx using hx.1 n)
  have hAle : ∀ n, A n ≤ p := fun n =>
    lintegral_mono_ae (by filter_upwards [key] with x hx using hx.2.1 n)
  have hmono : Monotone fun n x => ENNReal.ofReal (g n x) := by
    refine monotone_nat_of_le_succ fun n x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hg]
    rw [neg_le_neg_iff]
    refine Real.log_le_log (lt_of_lt_of_le (hεpos (n + 1)) (hclamp_pos (n + 1) x)) ?_
    refine min_le_min (max_le_max le_rfl (Real.exp_le_exp.2 ?_)) le_rfl
    push_cast
    linarith
  have hpA : p = ⨆ n, A n := by
    have h := lintegral_iSup (μ := m) (f := fun n x => ENNReal.ofReal (g n x))
      (fun n => ENNReal.measurable_ofReal.comp (hmeas n)) hmono
    calc p = ∫⁻ x, ⨆ n, ENNReal.ofReal (g n x) ∂m :=
          lintegral_congr_ae (by filter_upwards [key] with x hx using hx.2.2.symm)
      _ = ⨆ n, A n := h
  have hAmono : Monotone A := fun a b hab => lintegral_mono fun x => hmono hab x
  have hAfin : ∀ n, A n ≠ ⊤ := fun n => by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (hbound n x)) :
        A n ≤ ∫⁻ _x, ENNReal.ofReal ((n : ℝ) + R') ∂m) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hBfin : B ≠ ⊤ := by
    rw [← hBn 0]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs _) (hbound 0 x)) :
        ∫⁻ x, ENNReal.ofReal (-(g 0 x)) ∂m ≤ ∫⁻ _x, ENNReal.ofReal (((0 : ℕ) : ℝ) + R') ∂m) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hI : ∀ n, ((∫ x, g n x ∂m : ℝ) : EReal) = (A n : EReal) - (B : EReal) := fun n => by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint n), EReal.coe_sub,
      EReal.coe_ennreal_toReal (hAfin n), hBn n, EReal.coe_ennreal_toReal hBfin]
  refine ⟨fun n => ?_, ?_⟩
  · rw [hI n]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hAle n)) le_rfl
  · show _ ≤ ⨆ n : ℕ, ((∫ x, g n x ∂m : ℝ) : EReal)
    simp only [hI]
    have hT : Tendsto (fun n => (A n : EReal)) atTop (𝓝 (p : EReal)) := by
      have : Tendsto A atTop (𝓝 p) := by
        rw [hpA]
        exact tendsto_atTop_iSup hAmono
      exact (continuous_coe_ennreal_ereal.tendsto _).comp this
    have hBr : (B : EReal) = ((B.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hBfin).symm
    have hT2 : Tendsto (fun n => (A n : EReal) - B) atTop (𝓝 ((p : EReal) - B)) := by
      simp_rw [sub_eq_add_neg, hBr, ← EReal.coe_neg]
      exact (EReal.continuousAt_add (p := ((p : EReal), ((-B.toReal : ℝ) : EReal)))
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
        (hT.prodMk_nhds tendsto_const_nhds)
    exact le_of_tendsto' hT2 fun n => le_iSup (fun n => (A n : EReal) - B) n

/-- Helper (Ch. III §4, (4.2)). Truncations of the kernel at a fixed point `z`: bounded continuous functions `fₙ` whose
integrals against any `ν ∈ P(E)` lie below `U_ν(z)` and have `U_ν(z)` as their supremum (the kernel is bounded below
on the compact set `E`; `fₙ = −log (clamp ‖ζ − z‖ to [e⁻ⁿ, eᴸ])`). -/
theorem gm34_logPotential_trunc {E : Set ℂ} (hE : IsCompact E) (z : ℂ) :
    ∃ f : ℕ → BoundedContinuousFunction ℂ ℝ, ∀ ν ∈ probMeasuresOn E,
      (∀ n, ((∫ ζ, f n ζ ∂ν : ℝ) : EReal) ≤ logPotential ν z) ∧
        logPotential ν z ≤ ⨆ n, ((∫ ζ, f n ζ ∂ν : ℝ) : EReal) := by
  obtain ⟨R, hR⟩ := hE.isBounded.subset_closedBall z
  have hR1 : (1 : ℝ) ≤ max R 1 := le_max_right _ _
  have hcont : ∀ n : ℕ, Continuous fun ζ : ℂ => -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) (max R 1)) :=
    fun n => Continuous.neg (Continuous.log
      (((continuous_id.sub continuous_const).norm.max continuous_const).min continuous_const)
      fun ζ => (gm34_clamp_bound ‖ζ - z‖ hR1 n).1.ne')
  refine ⟨fun n => BoundedContinuousFunction.ofNormedAddCommGroup _ (hcont n) ((n : ℝ) + max R 1)
    fun ζ => (gm34_clamp_bound ‖ζ - z‖ hR1 n).2, fun ν hν => ?_⟩
  obtain ⟨hνp, hνE⟩ := hν
  have := hνp
  have hae : ∀ᵐ ζ ∂ν, ‖(fun ζ : ℂ => ζ - z) ζ‖ ≤ R := by
    filter_upwards [(MeasureTheory.mem_ae_iff.2 hνE : E ∈ MeasureTheory.ae ν)] with ζ hζ
    simpa [dist_eq_norm] using hR hζ
  exact gm34_trunc_generic (measurable_id.sub measurable_const) hae

/-- Helper (Ch. III §4, (4.3)). Truncations of the kernel in two variables: bounded jointly continuous `Fₙ` whose
double integrals against any `ν ∈ P(E)` lie below `I(ν)` and have `I(ν)` as their supremum. -/
theorem gm34_energy_trunc {E : Set ℂ} (hE : IsCompact E) :
    ∃ F : ℕ → ℂ → ℂ → ℝ, (∀ n, Continuous fun p : ℂ × ℂ => F n p.1 p.2) ∧
      (∀ n, ∃ C : ℝ, ∀ z ζ, |F n z ζ| ≤ C) ∧ ∀ ν ∈ probMeasuresOn E,
        (∀ n, ((∫ z, ∫ ζ, F n z ζ ∂ν ∂ν : ℝ) : EReal) ≤ energy ν) ∧
          energy ν ≤ ⨆ n, ((∫ z, ∫ ζ, F n z ζ ∂ν ∂ν : ℝ) : EReal) := by
  obtain ⟨R, hR⟩ := hE.isBounded.subset_closedBall (0 : ℂ)
  have hR1 : (1 : ℝ) ≤ max (2 * R) 1 := le_max_right _ _
  have hcont : ∀ n : ℕ, Continuous fun p : ℂ × ℂ =>
      -Real.log (min (max ‖p.1 - p.2‖ (Real.exp (-(n : ℝ)))) (max (2 * R) 1)) :=
    fun n => Continuous.neg (Continuous.log
      ((((continuous_fst.sub continuous_snd).norm).max continuous_const).min continuous_const)
      fun p => (gm34_clamp_bound ‖p.1 - p.2‖ hR1 n).1.ne')
  refine ⟨fun n z ζ => -Real.log (min (max ‖z - ζ‖ (Real.exp (-(n : ℝ)))) (max (2 * R) 1)),
    hcont, fun n => ⟨(n : ℝ) + max (2 * R) 1, fun z ζ => (gm34_clamp_bound ‖z - ζ‖ hR1 n).2⟩, fun ν hν => ?_⟩
  obtain ⟨hνp, hνE⟩ := hν
  have := hνp
  have hEae : ∀ᵐ z ∂ν, z ∈ E := MeasureTheory.mem_ae_iff.2 hνE
  have hae : ∀ᵐ p ∂(ν.prod ν), ‖(fun p : ℂ × ℂ => p.1 - p.2) p‖ ≤ 2 * R := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hEae,
      Measure.quasiMeasurePreserving_snd.ae hEae] with p h1 h2
    have a1 := mem_closedBall_zero_iff.1 (hR h1)
    have a2 := mem_closedBall_zero_iff.1 (hR h2)
    calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  obtain ⟨h1, h2⟩ := gm34_trunc_generic (m := ν.prod ν) (measurable_fst.sub measurable_snd) hae
  have hI : ∀ n : ℕ, ∫ p, -Real.log (min (max ‖p.1 - p.2‖ (Real.exp (-(n : ℝ)))) (max (2 * R) 1)) ∂(ν.prod ν) =
      ∫ z, ∫ ζ, -Real.log (min (max ‖z - ζ‖ (Real.exp (-(n : ℝ)))) (max (2 * R) 1)) ∂ν ∂ν := fun n => by
    refine MeasureTheory.integral_prod _ ?_
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p : ℂ × ℂ,
        ‖-Real.log (min (max ‖p.1 - p.2‖ (Real.exp (-(n : ℝ)))) (max (2 * R) 1))‖ ≤ C :=
      ⟨(n : ℝ) + max (2 * R) 1, fun p => (gm34_clamp_bound ‖p.1 - p.2‖ hR1 n).2⟩
    exact Integrable.of_bound (hcont n).aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hmP : Measurable fun p : ℂ × ℂ => (-ENNReal.log ‖p.1 - p.2‖ₑ).toENNReal :=
    (EReal.continuous_toENNReal.measurable).comp
      (measurable_neg.comp (ENNReal.measurable_log.comp (measurable_fst.sub measurable_snd).enorm))
  have hmN : Measurable fun p : ℂ × ℂ => (-(-ENNReal.log ‖p.1 - p.2‖ₑ)).toENNReal :=
    (EReal.continuous_toENNReal.measurable).comp
      (measurable_neg.comp (measurable_neg.comp
        (ENNReal.measurable_log.comp (measurable_fst.sub measurable_snd).enorm)))
  have hen : energy ν = ((∫⁻ p, (-ENNReal.log ‖p.1 - p.2‖ₑ).toENNReal ∂(ν.prod ν) : ℝ≥0∞) : EReal) -
      ((∫⁻ p, (-(-ENNReal.log ‖p.1 - p.2‖ₑ)).toENNReal ∂(ν.prod ν) : ℝ≥0∞) : EReal) := by
    rw [lintegral_prod _ hmP.aemeasurable, lintegral_prod _ hmN.aemeasurable]
    rfl
  rw [hen]
  refine ⟨fun n => ?_, ?_⟩
  · rw [← hI n]
    exact h1 n
  · simp only [← hI]
    exact h2

/-- Helper (Ch. III §4). Weak-star convergence of probability measures on a compact set passes to the double integral
of a bounded jointly continuous function: `∬ F dμₖ dμₖ → ∬ F dμ dμ`. -/
theorem gm34_tendsto_double_integral {E : Set ℂ} (hE : IsCompact E) {μs : ℕ → Measure ℂ}
    (hμs : ∀ n, μs n ∈ probMeasuresOn E) {μ : Measure ℂ} (hμ : μ ∈ probMeasuresOn E)
    (hlim : TendstoWeakStar μs atTop μ) {F : ℂ → ℂ → ℝ} (hF : Continuous fun p : ℂ × ℂ => F p.1 p.2)
    (hb : ∃ C : ℝ, ∀ z ζ, |F z ζ| ≤ C) :
    Tendsto (fun k => ∫ z, ∫ ζ, F z ζ ∂μs k ∂μs k) atTop (𝓝 (∫ z, ∫ ζ, F z ζ ∂μ ∂μ)) := by
  obtain ⟨C, hC⟩ := hb
  have hFcz : ∀ z, Continuous (F z) := fun z => hF.comp (continuous_const.prodMk continuous_id)
  have hFcζ : ∀ ζ, Continuous fun z => F z ζ := fun ζ => hF.comp (continuous_id.prodMk continuous_const)
  have hFC : ∀ z ζ, ‖F z ζ‖ ≤ C := fun z ζ => by simpa using hC z ζ
  set G : Measure ℂ → ℂ → ℝ := fun ν z => ∫ ζ, F z ζ ∂ν with hG
  have hGb : ∀ ν : Measure ℂ, IsProbabilityMeasure ν → ∀ z, ‖G ν z‖ ≤ C := fun ν hν z => by
    have := norm_integral_le_of_norm_le_const (μ := ν) (C := C) (f := F z)
      (Filter.Eventually.of_forall fun ζ => hFC z ζ)
    simpa using this
  have hGc : ∀ ν : Measure ℂ, IsProbabilityMeasure ν → Continuous (G ν) := fun ν hν =>
    continuous_of_dominated (bound := fun _ => C) (fun z => (hFcz z).aestronglyMeasurable)
      (fun z => Filter.Eventually.of_forall fun ζ => hFC z ζ) (integrable_const C)
      (Filter.Eventually.of_forall fun ζ => hFcζ ζ)
  have hGi : ∀ ν : Measure ℂ, IsProbabilityMeasure ν → ∀ ρ : Measure ℂ, IsFiniteMeasure ρ → Integrable (G ν) ρ :=
    fun ν hν ρ hρ => Integrable.of_bound (hGc ν hν).aestronglyMeasurable C
      (Filter.Eventually.of_forall (hGb ν hν))
  have hprob : ∀ k, IsProbabilityMeasure (μs k) := fun k => (hμs k).1
  have hμp : IsProbabilityMeasure μ := hμ.1
  have hunif : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ E, |G (μs k) z - G μ z| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
      ((hE.prod hE).uniformContinuousOn_of_continuous hF.continuousOn) (ε / 3) (by positivity)
    obtain ⟨t, htE, htf, hcover⟩ := hE.finite_cover_balls hδ
    have hev : ∀ᶠ k in atTop, ∀ y ∈ t, |G (μs k) y - G μ y| < ε / 3 := by
      refine (Filter.eventually_all_finite htf).2 fun y _ => ?_
      have := hlim (BoundedContinuousFunction.ofNormedAddCommGroup (F y) (hFcz y) C (hFC y))
      have h2 := (Metric.tendsto_nhds.1 this) (ε / 3) (by positivity)
      filter_upwards [h2] with k hk
      simpa [Real.dist_eq] using hk
    have hcl : ∀ ν : Measure ℂ, ν ∈ probMeasuresOn E → ∀ z ∈ E, ∀ y ∈ E, dist z y < δ →
        |G ν z - G ν y| ≤ ε / 3 := by
      intro ν hν z hz y hy hzy
      have hνp := hν.1
      have hae : ∀ᵐ ζ ∂ν, ζ ∈ E := MeasureTheory.mem_ae_iff.2 hν.2
      have hsub : G ν z - G ν y = ∫ ζ, (F z ζ - F y ζ) ∂ν := by
        rw [hG]
        exact (integral_sub (Integrable.of_bound (hFcz z).aestronglyMeasurable C
          (Filter.Eventually.of_forall (hFC z))) (Integrable.of_bound (hFcz y).aestronglyMeasurable C
          (Filter.Eventually.of_forall (hFC y)))).symm
      rw [hsub, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := ν) (C := ε / 3) (f := fun ζ => F z ζ - F y ζ) (by
        filter_upwards [hae] with ζ hζ
        have hd : dist (z, ζ) (y, ζ) < δ := by
          rw [Prod.dist_eq]
          simpa using hzy
        have := hU (z, ζ) ⟨hz, hζ⟩ (y, ζ) ⟨hy, hζ⟩ hd
        rw [Real.dist_eq] at this
        exact (Real.norm_eq_abs _ ▸ this.le))
      simpa using this
    filter_upwards [hev] with k hk z hz
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hcover hz)
    have hyE := htE hy
    have a1 := abs_le.1 (hcl (μs k) (hμs k) z hz y hyE (Metric.mem_ball.1 hzy))
    have a2 := abs_le.1 (hk y hy).le
    have a3 := abs_le.1 (hcl μ hμ z hz y hyE (Metric.mem_ball.1 hzy))
    refine abs_le.2 ⟨by linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2], by linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]⟩
  have hsplit : ∀ k, ∫ z, ∫ ζ, F z ζ ∂μs k ∂μs k =
      ∫ z, (G (μs k) z - G μ z) ∂μs k + ∫ z, G μ z ∂μs k := fun k => by
    have := hprob k
    show ∫ z, G (μs k) z ∂μs k = _
    rw [integral_sub (hGi (μs k) (hprob k) _ inferInstance) (hGi μ hμp _ inferInstance)]
    ring
  have h1 : Tendsto (fun k => ∫ z, (G (μs k) z - G μ z) ∂μs k) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hunif (ε / 2) (by positivity)] with k hk
    have := hprob k
    have hae : ∀ᵐ z ∂μs k, z ∈ E := MeasureTheory.mem_ae_iff.2 (hμs k).2
    have hn := norm_integral_le_of_norm_le_const (μ := μs k) (C := ε / 2)
      (f := fun z => G (μs k) z - G μ z) (by
        filter_upwards [hae] with z hz
        rw [Real.norm_eq_abs]
        exact hk z hz)
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    simp only [probReal_univ, mul_one] at hn
    linarith
  have h2 := hlim (BoundedContinuousFunction.ofNormedAddCommGroup (G μ) (hGc μ hμp) C (hGb μ hμp))
  have h3 := h1.add h2
  simp only [zero_add] at h3
  refine h3.congr fun k => ?_
  exact (hsplit k).symm

/-- **Lemma 4.2** (Ch. III §4; cited at P1:3812, 3908 and in Exercise 7, P1:5216), (4.2). Let `E` be a compact set and
let `{μ_n}` be a sequence in `P(E)`. If `μ_n` converges weak-star to `μ ∈ P(E)`, then (4.2)
`U_μ(z) ≤ liminf U_{μ_n}(z)`, `z ∈ ℂ`.
Modelling: "H μ_n converges" (P1:3778) is "If μ_n converges" [OCR or misprint; inline, no crop]; the `liminf` is taken
in `[−∞, +∞]` (a complete lattice: no junk value). -/
theorem lemma3_4_2_a {E : Set ℂ} (hE : IsCompact E) {μs : ℕ → Measure ℂ} (hμs : ∀ n, μs n ∈ probMeasuresOn E)
    {μ : Measure ℂ} (hμ : μ ∈ probMeasuresOn E) (hlim : TendstoWeakStar μs atTop μ) :
    ∀ z : ℂ, logPotential μ z ≤ liminf (fun n => logPotential (μs n) z) atTop := by
  intro z
  obtain ⟨f, hf⟩ := gm34_logPotential_trunc hE z
  refine (hf μ hμ).2.trans (iSup_le fun n => ?_)
  have ht : Tendsto (fun k => ((∫ ζ, f n ζ ∂μs k : ℝ) : EReal)) atTop (𝓝 ((∫ ζ, f n ζ ∂μ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp (hlim (f n))
  calc ((∫ ζ, f n ζ ∂μ : ℝ) : EReal) = liminf (fun k => ((∫ ζ, f n ζ ∂μs k : ℝ) : EReal)) atTop :=
        ht.liminf_eq.symm
    _ ≤ liminf (fun k => logPotential (μs k) z) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => (hf (μs k) (hμs k)).1 n)

/-- **Lemma 4.2** (Ch. III §4), (4.3). Under the hypotheses of (4.2), (4.3) `I(μ) ≤ liminf I(μ_n)`.
Modelling: the `liminf` is taken in `[−∞, +∞]`. -/
theorem lemma3_4_2_b {E : Set ℂ} (hE : IsCompact E) {μs : ℕ → Measure ℂ} (hμs : ∀ n, μs n ∈ probMeasuresOn E)
    {μ : Measure ℂ} (hμ : μ ∈ probMeasuresOn E) (hlim : TendstoWeakStar μs atTop μ) :
    energy μ ≤ liminf (fun n => energy (μs n)) atTop := by
  obtain ⟨F, hFc, hFb, hF⟩ := gm34_energy_trunc hE
  refine (hF μ hμ).2.trans (iSup_le fun n => ?_)
  have ht : Tendsto (fun k => ((∫ z, ∫ ζ, F n z ζ ∂μs k ∂μs k : ℝ) : EReal)) atTop
      (𝓝 ((∫ z, ∫ ζ, F n z ζ ∂μ ∂μ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp (gm34_tendsto_double_integral hE hμs hμ hlim (hFc n) (hFb n))
  calc ((∫ z, ∫ ζ, F n z ζ ∂μ ∂μ : ℝ) : EReal)
      = liminf (fun k => ((∫ z, ∫ ζ, F n z ζ ∂μs k ∂μs k : ℝ) : EReal)) atTop := ht.liminf_eq.symm
    _ ≤ liminf (fun k => energy (μs k)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => (hF (μs k) (hμs k)).1 n)

/-- **Unlabelled** (Ch. III §4, (4.4), P1:3818–3824, and P1:3862–3872; (4.4) is cited at P1:3868, the support at
P1:4070 "the limit measure `μ_E` is supported on `∂Ω`", the equalities at P1:4112). For a compact set `E` with
`Cap(E) > 0`, the equilibrium distribution `μ_E` has support contained in (4.4) `∂(⋂_n E_n) = ∂Ê ⊂ E`, and by (1.4)
and the uniqueness in Theorem 4.1, `μ_E = μ_{∂E} = μ_Ê = μ_{∂Ê}`.
Modelling: "support contained in the closed set `∂Ê`" is `μ_E(ℂ \ ∂Ê) = 0`; `⋂ E_n = Ê` holds for every sequence of
§1 by definition, so (4.4) is stated with `∂Ê`, together with the inclusion `∂Ê ⊂ E`; the rest of the chain
(`∂Ê ⊂ ∂E`) is not stated. -/
theorem equilibriumMeasure_support_eq {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) :
    frontier (filledSet E) ⊆ E ∧ equilibriumMeasure E (frontier (filledSet E))ᶜ = 0 ∧
      equilibriumMeasure (frontier E) = equilibriumMeasure E ∧
      equilibriumMeasure (filledSet E) = equilibriumMeasure E ∧
      equilibriumMeasure (frontier (filledSet E)) = equilibriumMeasure E := by
  sorry

/-- **Definition** ((4.8), the capacity of a Borel set, Ch. III §4, P1:3874–3877). The capacity of any Borel set `A`
is `Cap(A) = sup {Cap(E) : E compact, E ⊂ A}`.
Modelling (leader ruling B1): defined for every `A ⊆ ℂ` (the statements use Borel sets, as the book does), with
values in `[0, ∞]`; `Cap(E)` of compact `E` is (1.3). For compact `A` the supremum is attained at `E = A` by (1.5),
so this extends `capacityCompact`. -/
def capacity (A : Set ℂ) : ℝ≥0∞ :=
  ⨆ (E : Set ℂ) (_ : E ⊆ A) (_ : IsCompact E), capacityCompact E

/-- **Definition** (Robin's constant of a set, Ch. III §4; the formula `γ(E) = log(1/Cap(E))` of P1:3371 through
(4.8), "recalled" at P1:4439–4442 for Borel sets). `γ(A) = log(1/Cap(A))`.
Modelling (leader ruling B1): `−log Cap(A)` with values in `[−∞, +∞]` (`ENNReal.log`): `γ(A) = +∞` exactly when
`Cap(A) = 0`, and `γ(A) = −∞` when `Cap(A) = ∞`. -/
def robinConstant (A : Set ℂ) : EReal :=
  -ENNReal.log (capacity A)

/-- **Corollary 4.3** (Ch. III §4; cited at P1:3884, 4112, 4379, 4395), first part. If `E` is compact and
`Cap(E) = 0`, then `I(μ) = +∞` for all `μ ∈ P(E)`.
Modelling: `Cap` is `capacity` (4.8), the most general capacity at this point of the book, equal to (1.3) for
compact `E`. -/
theorem cor3_4_3_a {E : Set ℂ} (hE : IsCompact E) (hcap : capacity E = 0) :
    ∀ μ ∈ probMeasuresOn E, energy μ = ⊤ := by
  sorry

/-- **Corollary 4.3** (Ch. III §4), second part. Consequently, if `A` is Borel with `Cap(A) = 0` and if `μ` is a
positive measure with `I(μ) < ∞`, then `μ(A) = 0`.
Modelling: "positive measure" is a finite positive Borel measure with compact support (the measures of §§2–3 for
which `I` is defined; without these hypotheses `energy` could take its junk value `⊥ < ∞`). -/
theorem cor3_4_3_b {A : Set ℂ} (hA : MeasurableSet A) (hcap : capacity A = 0) {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0) (hI : energy μ < ⊤) : μ A = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §4, P1:3884–3888; cited at P1:4379, "by the remark after Corollary 4.3"). In particular,
(4.8) and Corollary 4.3 imply that `Cap(A) = 0 ⟹ Area(A) = 0`.
Modelling: `A` Borel (the sets of (4.8)); area is Lebesgue measure `volume` on `ℂ`. -/
theorem volume_eq_zero_of_capacity_eq_zero {A : Set ℂ} (hA : MeasurableSet A) (hcap : capacity A = 0) :
    volume A = 0 := by
  sorry

/-- **Definition** (polar set, Ch. III §4, P1:3890). Sets of capacity zero are also called polar sets. -/
def IsPolarSet (A : Set ℂ) : Prop :=
  capacity A = 0

/-- **Theorem 4.4** (Ch. III §4; cited at P1:4367, 4379, 4397, 4419), (4.9). Let `E` be a compact set such that
`Cap(E) > 0` and let `μ_E` be the equilibrium distribution for `E`. Then (4.9) `U_{μ_E}(z) ≤ γ(E)`, `z ∈ ℂ`.
Modelling: `Cap` and `γ` are `capacity` and `robinConstant` (4.8); comparison in `[−∞, +∞]`. -/
theorem thm3_4_4_a {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacity E) :
    ∀ z : ℂ, logPotential (equilibriumMeasure E) z ≤ robinConstant E := by
  sorry

/-- **Theorem 4.4** (Ch. III §4), (4.10) (cited at P1:4355, 4395). Under the hypotheses of (4.9),
(4.10) `U_{μ_E}(z) = γ(E) − g_Ω(z, ∞) < γ(E)`, `z ∈ Ω = ℂ* \ Ê`.
Modelling: `Ω` is the component of `ℂ* \ E` containing `∞` (so `ℂ* \ Ê = Ω`), stated at its finite points; `g_Ω` is
`greenFunctionLim` (1.7); `γ(E)` is finite here (`Cap(E) > 0`), and the difference is taken in `[−∞, +∞]`. -/
theorem thm3_4_4_b {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacity E) {Ω : Set ExtPlane}
    (hΩ : Ω = unboundedComponentExt E) :
    ∀ z : ℂ, (z : ExtPlane) ∈ Ω →
      logPotential (equilibriumMeasure E) z = robinConstant E - (greenFunctionLim Ω z extInf : EReal) ∧
        logPotential (equilibriumMeasure E) z < robinConstant E := by
  sorry

/-- **Theorem 4.4** (Ch. III §4), (4.11). Under the hypotheses of (4.9),
(4.11) `Cap({z ∈ Ê : U_{μ_E}(z) ≠ γ(E)}) = 0`.
Modelling: `Cap` is `capacity` (4.8) (the set is Borel, `U_{μ_E}` being lower semicontinuous). -/
theorem thm3_4_4_c {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacity E) :
    capacity {z ∈ filledSet E | logPotential (equilibriumMeasure E) z ≠ robinConstant E} = 0 := by
  sorry

/-- **Theorem 4.5** (Ch. III §4; cited at P1:3949, 3983, 4022, 4036, 4566 and in Exercise 7, P1:5202), first part.
Suppose `ψ` is a contraction: `|ψ(z) − ψ(w)| ≤ |z − w|` for all `z, w ∈ E`. Then `Cap(ψ(E)) ≤ Cap(E)`.
Modelling: `E` compact (the standing "compact set `E`" of §4, P1:3766; `ψ(E)` is then compact; every later
citation, P1:3965, 4036, 4566, 4890 and Exercise 7, applies it to compact sets); `Cap` is `capacity` (4.8). -/
theorem thm3_4_5_a {E : Set ℂ} (hE : IsCompact E) {ψ : ℂ → ℂ} (hψ : ∀ z ∈ E, ∀ w ∈ E, ‖ψ z - ψ w‖ ≤ ‖z - w‖) :
    capacity (ψ '' E) ≤ capacity E := by
  sorry

/-- **Theorem 4.5** (Ch. III §4), second part ((4.12), cited at P1:3965, 4890). Consequently, if
`E* = {|z| : z ∈ E}` is the circular projection of `E` onto `ℝ`, then (4.12) `Cap(E) ≥ Cap(E*) ≥ |E*|/4`, where `|E*|`
denotes the length of `E*`.
Modelling: `E` compact; `E*` is a subset of `ℝ`, seen in `ℂ` through the coercion for its capacity, and its length
`|E*|` is its Lebesgue measure `volume` on `ℝ`; inequalities in `[0, ∞]`. The constant `1/4` was checked against the
equation image. -/
theorem thm3_4_5_b {E : Set ℂ} (hE : IsCompact E) :
    capacity (((↑) : ℝ → ℂ) '' ((fun z : ℂ => ‖z‖) '' E)) ≤ capacity E ∧
      volume ((fun z : ℂ => ‖z‖) '' E) / 4 ≤ capacity (((↑) : ℝ → ℂ) '' ((fun z : ℂ => ‖z‖) '' E)) := by
  sorry

/-- Helper (Ch. III §4, Lemma 4.6). A Borel section of a continuous map on a compact set: `s` is Borel, takes values in `E`
on `ψ(E)`, and `ψ (s y) = y` there. -/
theorem gm34_borel_section {E : Set ℂ} (hE : IsCompact E) {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ E) :
    ∃ s : ℂ → ℂ, Measurable s ∧ ∀ y ∈ ψ '' E, s y ∈ E ∧ ψ (s y) = y := by
  classical
  set m : Set ℂ → ℂ → ℝ := fun S y => sInf (Complex.re '' (S ∩ ψ ⁻¹' {y})) with hm
  set Eb : ℝ → Set ℂ := fun b => E ∩ {z | z.im ≤ b} with hEb
  have hEbc : ∀ b, IsCompact (Eb b) := fun b =>
    hE.inter_right (isClosed_le Complex.continuous_im continuous_const)
  have hψEb : ∀ b, ContinuousOn ψ (Eb b) := fun b => hψ.mono Set.inter_subset_left
  set ys : ℂ → ℝ := fun y => sInf (Complex.im '' (E ∩ ψ ⁻¹' {y} ∩ {z | z.re = m E y})) with hys
  -- the lexicographic minimiser on a fibre
  have hK : ∀ y ∈ ψ '' E, ∃ z1 ∈ E, ψ z1 = y ∧ z1.re = m E y ∧ z1.im = ys y ∧
      ∀ z' ∈ E, ψ z' = y → z'.re = m E y → z1.im ≤ z'.im := by
    intro y hy
    obtain ⟨z0, hz0E, hz0y, hz0re, hz0min⟩ := gm34_fiber_min hE hψ hy
    have hcl : IsClosed (E ∩ ψ ⁻¹' {y} ∩ {z | z.re = m E y}) :=
      (hψ.preimage_isClosed_of_isClosed hE.isClosed isClosed_singleton).inter
        (isClosed_eq Complex.continuous_re continuous_const)
    have hKc : IsCompact (E ∩ ψ ⁻¹' {y} ∩ {z | z.re = m E y}) :=
      hE.of_isClosed_subset hcl (fun z hz => hz.1.1)
    obtain ⟨z1, hz1, hmin⟩ := hKc.exists_isMinOn ⟨z0, ⟨hz0E, hz0y⟩, hz0re⟩
      Complex.continuous_im.continuousOn
    have hleast : IsLeast (Complex.im '' (E ∩ ψ ⁻¹' {y} ∩ {z | z.re = m E y})) z1.im :=
      ⟨Set.mem_image_of_mem _ hz1, by
        rintro _ ⟨z', hz', rfl⟩
        exact hmin hz'⟩
    exact ⟨z1, hz1.1.1, hz1.1.2, hz1.2, hleast.csInf_eq.symm, fun z' hz'E hz'y hz're =>
      hmin ⟨⟨hz'E, hz'y⟩, hz're⟩⟩
  have hiff : ∀ y ∈ ψ '' E, ∀ b : ℝ, ys y ≤ b ↔ y ∈ ψ '' Eb b ∧ m (Eb b) y = m E y := by
    intro y hy b
    obtain ⟨z0, hz0E, hz0y, hz0re, hz0min⟩ := gm34_fiber_min hE hψ hy
    obtain ⟨z1, hz1E, hz1y, hz1re, hz1im, hz1min⟩ := hK y hy
    constructor
    · intro h
      have hz1b : z1 ∈ Eb b := ⟨hz1E, show z1.im ≤ b by linarith⟩
      have hyb : y ∈ ψ '' Eb b := ⟨z1, hz1b, hz1y⟩
      obtain ⟨z2, hz2E, hz2y, hz2re, hz2min⟩ := gm34_fiber_min (hEbc b) (hψEb b) hyb
      refine ⟨hyb, ?_⟩
      show m (Eb b) y = m E y
      have e0 : m E y = z0.re := hz0re.symm
      have e2 : m (Eb b) y = z2.re := hz2re.symm
      have h1 : m (Eb b) y ≤ m E y := by
        rw [e2, ← hz1re]
        exact hz2min z1 hz1b hz1y
      have h2 : m E y ≤ m (Eb b) y := by
        rw [e0, e2]
        exact hz0min z2 hz2E.1 hz2y
      exact le_antisymm h1 h2
    · rintro ⟨hyb, hmy⟩
      obtain ⟨z2, hz2E, hz2y, hz2re, hz2min⟩ := gm34_fiber_min (hEbc b) (hψEb b) hyb
      have h1 : z1.im ≤ z2.im := hz1min z2 hz2E.1 hz2y (by rw [← hmy]; exact hz2re)
      have h2 : z2.im ≤ b := hz2E.2
      rw [← hz1im]
      exact h1.trans h2
  have hmeasm : ∀ S, IsCompact S → ContinuousOn ψ S → Measurable (m S) := fun S hS hψS =>
    gm34_fiber_min_measurable hS hψS
  have hmeasys : Measurable ys := by
    refine measurable_of_Iic fun b => ?_
    have hcE : IsCompact (ψ '' E) := hE.image_of_continuousOn hψ
    have hset : ys ⁻¹' Set.Iic b =
        (ψ '' Eb b ∩ {y | m (Eb b) y = m E y}) ∪ ((ψ '' E)ᶜ ∩ {_y | (0 : ℝ) ≤ b}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      by_cases hy : y ∈ ψ '' E
      · rw [hiff y hy b]
        constructor
        · exact Or.inl
        · rintro (h | h)
          · exact h
          · exact absurd hy h.1
      · have hemp : E ∩ ψ ⁻¹' {y} ∩ {z | z.re = m E y} = ∅ := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h _ => hy ⟨z, h.1, h.2⟩
        have h0 : ys y = 0 := by
          simp only [hys, hemp, Set.image_empty, Real.sInf_empty]
        rw [h0]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨⟨z', hz'b, hz'y⟩, -⟩ | h)
          · exact absurd ⟨z', hz'b.1, hz'y⟩ hy
          · exact h.2
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · refine ((hEbc b).image_of_continuousOn (hψEb b)).isClosed.measurableSet.inter ?_
      exact measurableSet_eq_fun (hmeasm _ (hEbc b) (hψEb b)) (hmeasm _ hE hψ)
    · by_cases hb : (0 : ℝ) ≤ b
      · simpa [hb] using hcE.isClosed.measurableSet.compl
      · simp [hb]
  refine ⟨fun y => ((m E y : ℝ) : ℂ) + ((ys y : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · exact (Complex.measurable_ofReal.comp (hmeasm E hE hψ)).add
      ((Complex.measurable_ofReal.comp hmeasys).mul_const Complex.I)
  · intro y hy
    obtain ⟨z1, hz1E, hz1y, hz1re, hz1im, -⟩ := hK y hy
    have hz : ((m E y : ℝ) : ℂ) + ((ys y : ℝ) : ℂ) * Complex.I = z1 := by
      apply Complex.ext <;> simp [hz1re, hz1im]
    show ((m E y : ℝ) : ℂ) + ((ys y : ℝ) : ℂ) * Complex.I ∈ E ∧
      ψ (((m E y : ℝ) : ℂ) + ((ys y : ℝ) : ℂ) * Complex.I) = y
    rw [hz]
    exact ⟨hz1E, hz1y⟩

/-- **Lemma 4.6** (Ch. III §4; cited at P1:3951 in the proof of Theorem 4.5). Let `E` be a compact set and let `ψ`
be a continuous map from `E` onto `ψ(E)`. For `ν ∈ P(E)` define `ψ_*(ν)` by (4.13) `ψ_*(ν)(A) = ν(ψ⁻¹(A))`. Then
`ψ_*` maps `P(E)` onto `P(ψ(E))`.
Modelling: `ψ : ℂ → ℂ` continuous on `E`; `ψ_*(ν)` is the image measure `Measure.map ψ ν` (it is (4.13) on Borel
sets: `ψ` agrees `ν`-almost everywhere with a Borel function, being continuous on the closed set `E` that carries
`ν`); "maps `P(E)` onto `P(ψ(E))`" is: into, and every element of `P(ψ(E))` is attained. -/
theorem lemma3_4_6 {E : Set ℂ} (hE : IsCompact E) {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ E) :
    (∀ ν ∈ probMeasuresOn E, ν.map ψ ∈ probMeasuresOn (ψ '' E)) ∧
      ∀ μ ∈ probMeasuresOn (ψ '' E), ∃ ν ∈ probMeasuresOn E, ν.map ψ = μ := by
  classical
  have hEm : MeasurableSet E := hE.isClosed.measurableSet
  have hψE : IsCompact (ψ '' E) := hE.image_of_continuousOn hψ
  have hψm : MeasurableSet (ψ '' E) := hψE.isClosed.measurableSet
  set ψ' : ℂ → ℂ := E.piecewise ψ (fun _ => 0) with hψ'
  have hm' : Measurable ψ' := hψ.measurable_piecewise continuousOn_const hEm
  have hψ'E : ∀ x ∈ E, ψ' x = ψ x := fun x hx => Set.piecewise_eq_of_mem E ψ _ hx
  have hae : ∀ ν : Measure ℂ, ν Eᶜ = 0 → ψ =ᵐ[ν] ψ' := fun ν hν => by
    filter_upwards [(MeasureTheory.mem_ae_iff.2 hν : E ∈ MeasureTheory.ae ν)] with x hx
    exact (hψ'E x hx).symm
  refine ⟨fun ν hν => ?_, fun μ hμ => ?_⟩
  · obtain ⟨hνp, hνE⟩ := hν
    rw [Measure.map_congr (hae ν hνE)]
    have := hνp
    refine ⟨inferInstance, ?_⟩
    rw [Measure.map_apply hm' hψm.compl]
    refine measure_mono_null (fun x hx => ?_) hνE
    by_contra hxE
    have hxE' : x ∈ E := not_not.1 hxE
    apply hx
    show ψ' x ∈ ψ '' E
    rw [hψ'E x hxE']
    exact Set.mem_image_of_mem ψ hxE'
  · obtain ⟨hμp, hμE⟩ := hμ
    obtain ⟨s, hs, hsE⟩ := gm34_borel_section hE hψ
    have := hμp
    refine ⟨μ.map s, ⟨inferInstance, ?_⟩, ?_⟩
    · rw [Measure.map_apply hs hEm.compl]
      refine measure_mono_null (fun y hy => ?_) hμE
      by_contra hyE
      exact hy (hsE y (not_not.1 hyE)).1
    · have hν0 : (μ.map s) Eᶜ = 0 := by
        rw [Measure.map_apply hs hEm.compl]
        refine measure_mono_null (fun y hy => ?_) hμE
        by_contra hyE
        exact hy (hsE y (not_not.1 hyE)).1
      rw [Measure.map_congr (hae _ hν0), Measure.map_map hm' hs]
      have : ψ' ∘ s =ᵐ[μ] id := by
        filter_upwards [(MeasureTheory.mem_ae_iff.2 hμE : ψ '' E ∈ MeasureTheory.ae μ)] with y hy
        obtain ⟨hs1, hs2⟩ := hsE y hy
        simp only [Function.comp_apply, id, hψ'E _ hs1, hs2]
      rw [Measure.map_congr this, Measure.map_id]

/-- **Formula (4.14)** (Ch. III §4, Example 4.7, P1:3985–4020; cited at P1:4539 in Example 7.2, and the set in App. D,
P3:3467: "The Cantor set, defined in Example III.4.7"). The Cantor set `K = ⋂_{n≥0} K_n` (`K_0 = [0, 1]`, `K_n`
obtained by removing the open middle third of each interval of `K_{n−1}`) satisfies (4.14) `Cap(K) ≥ 1/9`.
Modelling: `K` is Mathlib's `cantorSet` (the same construction) seen in `ℂ`; `Cap` is `capacity` (4.8), which equals
(1.3) on the compact set `K`; the constant `1/9` was checked against the equation image. -/
theorem eq3_4_14 : (1 / 9 : ℝ≥0∞) ≤ capacity (((↑) : ℝ → ℂ) '' cantorSet) := by
  sorry

end GarnettMarshall2005
