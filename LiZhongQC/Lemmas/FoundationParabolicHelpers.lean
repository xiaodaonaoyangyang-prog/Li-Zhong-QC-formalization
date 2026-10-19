import LiZhongQC.Lemmas.FoundationQuotient

/-! Source-only exact covering transport for a translation-periodic boundary. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- The full inverse image of the exponential period curve is exactly the original
unit-translation-invariant curve. No injectivity or separation assumption is used. -/
theorem ft1gc_periodic_exp_full_preimage (f : ℝ → ℂ)
    (hshift : ∀ t : ℝ, f (t + 1) = f t + 1) :
    {z : ℂ | Complex.exp (2 * Real.pi * I * z) ∈
      (fun t : ℝ => Complex.exp (2 * Real.pi * I * f t)) '' Icc 0 1} = range f := by
  let F : AddConstMap ℝ ℂ 1 1 := { toFun := f, map_add_const' := hshift }
  have htranslate : ∀ t : ℝ, ∀ n : ℤ, f (t + n) = f t + n := by
    intro t n
    exact AddConstMapClass.map_add_int F t n
  let e : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * I * f t)
  have hperiod : Function.Periodic e 1 := by
    intro t
    change Complex.exp (2 * Real.pi * I * f (t + 1)) =
      Complex.exp (2 * Real.pi * I * f t)
    rw [hshift, mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  ext z
  constructor
  · rintro ⟨t, ht, he⟩
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
    have hft : f t = z + n := by
      apply mul_left_cancel₀ hfactor
      linear_combination hn
    refine ⟨t + ((-n : ℤ) : ℝ), ?_⟩
    rw [htranslate]
    push_cast
    linear_combination hft
  · rintro ⟨t, rfl⟩
    have ht : t - (⌊t⌋ : ℤ) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩
    refine ⟨t - (⌊t⌋ : ℤ), ht, ?_⟩
    change e (t - (⌊t⌋ : ℤ)) = e t
    simpa only [mul_one] using hperiod.sub_int_mul_eq (x := t) (⌊t⌋ : ℤ)

/-- Restricting the exact covering identity to the upper half-plane introduces no
additional boundary components or missing integer translates. -/
theorem ft1gc_parabolic_exp_full_preimage (ρ : ℝ → UpperHalfPlane)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = (1 : ℝ) +ᵥ ρ t) :
    {τ : UpperHalfPlane | Complex.exp (2 * Real.pi * I * (τ : ℂ)) ∈
      (fun t : ℝ => Complex.exp (2 * Real.pi * I * (ρ t : ℂ))) '' Icc 0 1} = range ρ := by
  have hshift : ∀ t : ℝ, (ρ (t + 1) : ℂ) = (ρ t : ℂ) + 1 := by
    intro t
    rw [hperiod, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have heq := ft1gc_periodic_exp_full_preimage (fun t => (ρ t : ℂ)) hshift
  ext τ
  change (τ : ℂ) ∈ {z : ℂ | Complex.exp (2 * Real.pi * I * z) ∈
    (fun t : ℝ => Complex.exp (2 * Real.pi * I * (ρ t : ℂ))) '' Icc 0 1} ↔ τ ∈ range ρ
  rw [heq]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, UpperHalfPlane.ext ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

/-- Once the complement of the boundary has two connected open pieces, any connected
open set with exactly that boundary is one entire piece. This prevents the collar
argument from silently replacing the given W by a smaller chosen component. -/
theorem ft1gc_open_eq_one_of_two_sides {X : Type*} [TopologicalSpace X]
    (W U V : Set X) (hWo : IsOpen W) (hWc : IsConnected W)
    (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier W)ᶜ) :
    W = U ∨ W = V := by
  have hWsub : W ⊆ U ∪ V := by
    intro x hx
    rw [hcover]
    exact fun hxf => Set.disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hWo) hxf hx
  have hkey : ∀ T : Set X, IsPreconnected T → T ⊆ (frontier W)ᶜ → W ⊆ T → W = T := by
    intro T hTc hTfront hWT
    apply Set.Subset.antisymm hWT
    apply hTc.subset_of_closure_inter_subset hWo
    · obtain ⟨x, hx⟩ := hWc.nonempty
      exact ⟨x, hWT hx, hx⟩
    · rintro x ⟨hxcl, hxT⟩
      by_contra hxW
      apply hTfront hxT
      rw [hWo.frontier_eq]
      exact ⟨hxcl, hxW⟩
  rcases hWc.isPreconnected.subset_or_subset hUo hVo hUV hWsub with hWU | hWV
  · left
    exact hkey U hUc.isPreconnected (fun x hx => hcover ▸ Or.inl hx) hWU
  · right
    exact hkey V hVc.isPreconnected (fun x hx => hcover ▸ Or.inr hx) hWV



/-- A nonvanishing continuous function on a simply connected locally path connected
space has a continuous logarithm. Unlike the open-domain analytic log interface, this
applies to a closed disc and hence to the closed Jordan filling. -/
theorem ft1gc_continuous_log_on_simplyConnected
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (f : X → ℂ) (hf : Continuous f) (hne : ∀ x, f x ≠ 0) :
    ∃ L : X → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x) = f x := by
  have hnorm : ∀ x, (‖f x‖ : ℂ) ≠ 0 := fun x =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne x))
  have hmem : ∀ x, f x / (‖f x‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    intro x
    apply mem_sphere_zero_iff_norm.2
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne x))]
  let c : C(X, Circle) :=
    ⟨fun x => ⟨f x / (‖f x‖ : ℂ), hmem x⟩,
      Continuous.subtype_mk (hf.div (Complex.continuous_ofReal.comp (continuous_norm.comp hf)) hnorm) _⟩
  obtain ⟨Θ, ⟨-, hΘ⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    c x₀ (Complex.arg (c x₀ : ℂ)) (Circle.exp_arg (c x₀))
  have hkey : ∀ x, Complex.exp ((Θ x : ℝ) * I) = f x / (‖f x‖ : ℂ) := by
    intro x
    exact congrArg ((↑) : Circle → ℂ) (congrFun hΘ x)
  have hlogc : Continuous (fun x => (Real.log ‖f x‖ : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (hf.norm.log (fun x => norm_ne_zero_iff.2 (hne x)))
  refine ⟨fun x => (Real.log ‖f x‖ : ℂ) + (Θ x : ℝ) * I,
    hlogc.add ((Complex.continuous_ofReal.comp Θ.continuous).mul continuous_const), ?_⟩
  intro x
  have hlogexp : Complex.exp (Real.log ‖f x‖ : ℂ) = (‖f x‖ : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 (hne x))]
  rw [Complex.exp_add, hlogexp, hkey]
  field_simp [hnorm x] <;> ring

/-- The logarithm-lifting input applies on the closed unit disc itself, including
its boundary. Convexity supplies both contractibility and local path connectivity. -/
theorem ft1gc_continuous_log_on_closedDisc
    (f : Metric.closedBall (0 : ℂ) 1 → ℂ) (hf : Continuous f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ L : Metric.closedBall (0 : ℂ) 1 → ℂ,
      Continuous L ∧ ∀ z, Complex.exp (L z) = f z := by
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_self]
    exact zero_le_one
  letI : ContractibleSpace (Metric.closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace ⟨0, hzero⟩
  letI : LocallyPathConnectedSpace (Metric.closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  exact ft1gc_continuous_log_on_simplyConnected ⟨0, hzero⟩ f hf hne


end LiZhongQC
