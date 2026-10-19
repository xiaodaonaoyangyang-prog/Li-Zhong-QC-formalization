import LiZhongQC.Lemmas.HurwitzPowerModel
import Mathlib
import LiZhongQC.Ch06.S22_RiemannSurfaces
import Jacobians.CanonicalForms.CanonicalFormDifferential
import Jacobians.Surface.ContMDiffOmegaAnalytic
import Jacobians.MappingDegree.CriticalValuesFiniteGeneral
import LiZhongQC.Lemmas.HurwitzComplexQuotient
import LiZhongQC.Lemmas.HurwitzSharpDefect
import LiZhongQC.Lemmas.UniformizedTeichmuller

/-! Mechanically assembled round77 Hurwitz proof chain.
Original declarations and proof bodies are preserved in isolated sections.
See INPUT_MANIFEST.json and LINE_MAP.tsv for provenance. -/

-- BEGIN SOURCE: local_repair_003/HurwitzLocalPullback.lean
section h77_bundle_01_HurwitzLocalPullback

/-! Orders of meromorphic differentials pulled back by actual power coordinates.
The coefficient is f(z^e) times the derivative of z^e; poles are included. -/

open Set Filter
open scoped Topology

namespace LiZhongQC

/-- The analytic multiplicity of the centered power coordinate. -/
theorem h77d_power_analytic_order (e : ℕ) :
    analyticOrderAt (fun z : ℂ => z ^ e) 0 = (e : ℕ∞) := by
  have h := analyticOrderAt_pow (show AnalyticAt ℂ (id : ℂ → ℂ) 0 from analyticAt_id) e
  have heq : (id : ℂ → ℂ) ^ e = (fun z : ℂ => z ^ e) := by
    funext z
    rfl
  rw [heq] at h
  simpa using h

/-- A positive power coordinate is never locally constant, including at its branch point. -/
theorem h77d_power_not_eventuallyConst (e : ℕ) (he : e ≠ 0) :
    ¬ EventuallyConst (fun z : ℂ => z ^ e) (𝓝 0) := by
  rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
  simpa only [zero_pow he, sub_zero, h77d_power_analytic_order] using
    (show (e : ℕ∞) ≠ ⊤ from ENat.coe_ne_top e)

/-- Orders of arbitrary meromorphic coefficients multiply by the local degree. -/
theorem h77d_power_comp_order {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (e : ℕ) (he : e ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => f (z ^ e)) 0 =
      meromorphicOrderAt f 0 * (e : WithTop ℤ) := by
  have hf' : MeromorphicAt f ((0 : ℂ) ^ e) := by simpa only [zero_pow he] using hf
  have h := hf'.meromorphicOrderAt_comp (g := fun z : ℂ => z ^ e) (x := (0 : ℂ))
    (show AnalyticAt ℂ (fun z : ℂ => z ^ e) 0 by fun_prop)
    (h77d_power_not_eventuallyConst e he)
  change meromorphicOrderAt (fun z : ℂ => f (z ^ e)) 0 =
    meromorphicOrderAt f ((0 : ℂ) ^ e) *
      (analyticOrderAt (fun z : ℂ => z ^ e - (0 : ℂ) ^ e) 0).map Nat.cast at h
  simpa only [zero_pow he, sub_zero,
    h77d_power_analytic_order, ENat.map_natCast, WithTop.coe_natCast] using h

/-- The derivative of a positive power has order e-1 at its central point. -/
theorem h77d_power_derivative_order (e : ℕ) (he : e ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => (e : ℂ) * z ^ (e - 1)) 0 =
      ((e - 1 : ℕ) : WithTop ℤ) := by
  have hscalar : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he
  have hmul := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => z ^ (e - 1))
    (show AnalyticAt ℂ (fun _ : ℂ => (e : ℂ)) 0 from analyticAt_const) hscalar
  change meromorphicOrderAt ((fun _ : ℂ => (e : ℂ)) *
    (fun z : ℂ => z ^ (e - 1))) 0 = _ at hmul
  change meromorphicOrderAt ((fun _ : ℂ => (e : ℂ)) *
    (fun z : ℂ => z ^ (e - 1))) 0 = _
  rw [hmul]
  have hp := meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := 0) (n := e - 1)
  change meromorphicOrderAt (fun z : ℂ => (z - 0) ^ (e - 1)) 0 =
    ((e - 1 : ℕ) : WithTop ℤ) at hp
  simpa only [sub_zero] using hp

/-- The local divisor formula for a pulled-back meromorphic differential,
valid also when the coefficient vanishes identically as a germ. -/
theorem h77d_power_pullback_order {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (e : ℕ) (he : e ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => f (z ^ e) * ((e : ℂ) * z ^ (e - 1))) 0 =
      meromorphicOrderAt f 0 * (e : WithTop ℤ) + ((e - 1 : ℕ) : WithTop ℤ) := by
  have hf' : MeromorphicAt f ((0 : ℂ) ^ e) := by simpa only [zero_pow he] using hf
  have hc : MeromorphicAt (fun z : ℂ => f (z ^ e)) (0 : ℂ) :=
    hf'.comp_analyticAt (𝕜 := ℂ) (g := fun z : ℂ => z ^ e) (x := (0 : ℂ))
      (show AnalyticAt ℂ (fun z : ℂ => z ^ e) 0 by fun_prop)
  have hd : MeromorphicAt (fun z : ℂ => (e : ℂ) * z ^ (e - 1)) 0 := by fun_prop
  change meromorphicOrderAt ((fun z : ℂ => f (z ^ e)) *
    (fun z : ℂ => (e : ℂ) * z ^ (e - 1))) 0 = _
  rw [meromorphicOrderAt_mul hc hd, h77d_power_comp_order hf e he,
    h77d_power_derivative_order e he]

/-- The same formula uses the actual derivative, not an assumed Jacobian factor. -/
theorem h77d_power_pullback_deriv_order {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (e : ℕ) (he : e ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => f (z ^ e) * deriv (fun w : ℂ => w ^ e) z) 0 =
      meromorphicOrderAt f 0 * (e : WithTop ℤ) + ((e - 1 : ℕ) : WithTop ℤ) := by
  have hd : (fun z : ℂ => deriv (fun w : ℂ => w ^ e) z) =
      (fun z : ℂ => (e : ℂ) * z ^ (e - 1)) := by
    funext z
    exact (hasDerivAt_pow e z).deriv
  simpa only [hd] using h77d_power_pullback_order hf e he

/-- Finite integer orders give the usual e*k+e-1 ramification formula. -/
theorem h77d_power_pullback_order_int {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (e : ℕ) (he : e ≠ 0) (k : ℤ) (hk : meromorphicOrderAt f 0 = (k : WithTop ℤ)) :
    meromorphicOrderAt (fun z : ℂ => f (z ^ e) * ((e : ℂ) * z ^ (e - 1))) 0 =
      ((k * (e : ℤ) + (e : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  rw [h77d_power_pullback_order hf e he, hk]
  have he' : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  norm_cast
  rw [Nat.cast_sub he']
  ring

/-- The local formula survives equality of the actual coefficient germs.
This is the interface consumed after expressing a differential in power coordinates. -/
theorem h77d_power_pullback_order_of_eventuallyEq {f a : ℂ → ℂ}
    (hf : MeromorphicAt f 0) (e : ℕ) (he : e ≠ 0)
    (ha : a =ᶠ[𝓝[≠] 0] fun z : ℂ => f (z ^ e) * ((e : ℂ) * z ^ (e - 1))) :
    meromorphicOrderAt a 0 =
      meromorphicOrderAt f 0 * (e : WithTop ℤ) + ((e - 1 : ℕ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr ha]
  exact h77d_power_pullback_order hf e he

end LiZhongQC
end h77_bundle_01_HurwitzLocalPullback
-- END SOURCE: local_repair_003/HurwitzLocalPullback.lean

-- BEGIN SOURCE: chain_repair_002_sources/HurwitzOrbitCounting.lean
section h77_bundle_02_HurwitzOrbitCounting

/-! Exact fiber and stabilizer counting for an actual orbit quotient.
Only the defining orbit-fiber identity is assumed; local degrees will be supplied
by the analytic power-coordinate theorem. -/

open Set
open scoped BigOperators

namespace LiZhongQC

/-- Stabilizer cardinality is constant along an actual group orbit. -/
theorem h77d_stabilizer_card_eq_of_mem_orbit
    {G X : Type*} [Group G] [MulAction G X] {x y : X}
    (hy : y ∈ MulAction.orbit G x) :
    Nat.card (MulAction.stabilizer G y) = Nat.card (MulAction.stabilizer G x) := by
  rcases hy with ⟨g, hg⟩
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv).symm

/-- The natural-cardinality form of orbit-stabilizer, requiring no chosen enumeration. -/
theorem h77d_orbit_card_mul_stabilizer {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  simpa only [Nat.card_prod] using
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

/-- A map whose fibers are exactly orbits has finite fibers for a finite acting group. -/
theorem h77d_quotient_fiber_finite {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hπ : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y) (x : X) :
    {z : X | π z = π x}.Finite := by
  have hs : {z : X | π z = π x} = MulAction.orbit G x := by
    ext z
    change (π z = π x) ↔ ∃ g : G, g • x = z
    exact eq_comm.trans (hπ x z)
  rw [hs]
  exact Finite.finite_mulAction_orbit x

/-- Exact orbit-stabilizer counting on the actual projection fiber. -/
theorem h77d_quotient_fiber_card_mul_stabilizer
    {G X Y : Type*} [Group G] [MulAction G X]
    (π : X → Y) (hπ : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y) (x : X) :
    Nat.card {z : X // π z = π x} * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  have hs : {z : X | π z = π x} = MulAction.orbit G x := by
    ext z
    change (π z = π x) ↔ ∃ g : G, g • x = z
    exact eq_comm.trans (hπ x z)
  have hc := congrArg (fun s : Set X => Nat.card s) hs
  change Nat.card {z : X // π z = π x} = Nat.card (MulAction.orbit G x) at hc
  rw [hc]
  exact h77d_orbit_card_mul_stabilizer x

/-- The sum of stabilizer orders in each actual fiber equals the group order.
After the power-coordinate construction these are the analytic local degrees. -/
theorem h77d_quotient_fiber_sum_stabilizer
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hπ : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y)
    (x : X) [Fintype {z : X // π z = π x}] :
    (∑ z : {z : X // π z = π x}, Nat.card (MulAction.stabilizer G (z : X))) =
      Nat.card G := by
  have hc : ∀ z : {z : X // π z = π x},
      Nat.card (MulAction.stabilizer G (z : X)) = Nat.card (MulAction.stabilizer G x) := by
    intro z
    exact h77d_stabilizer_card_eq_of_mem_orbit ((hπ x z).mp z.property.symm)
  calc
    (∑ z : {z : X // π z = π x}, Nat.card (MulAction.stabilizer G (z : X))) =
        Fintype.card {z : X // π z = π x} * Nat.card (MulAction.stabilizer G x) := by
      simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ = Nat.card G := by
      rw [← Nat.card_eq_fintype_card]
      exact h77d_quotient_fiber_card_mul_stabilizer π hπ x

/-- Summing the ramification contributions e-1 over one fiber subtracts its
ordinary cardinality from the group order. Integer coefficients avoid truncated subtraction. -/
theorem h77d_quotient_fiber_ramification_sum
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hπ : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y)
    (x : X) [Fintype {z : X // π z = π x}] :
    (∑ z : {z : X // π z = π x}, ((Nat.card (MulAction.stabilizer G (z : X)) : ℤ) - 1)) =
      (Nat.card G : ℤ) - Nat.card {z : X // π z = π x} := by
  rw [Finset.sum_sub_distrib]
  have hc := congrArg (fun n : ℕ => (n : ℤ))
    (h77d_quotient_fiber_sum_stabilizer π hπ x)
  push_cast at hc
  rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

end LiZhongQC
end h77_bundle_02_HurwitzOrbitCounting
-- END SOURCE: chain_repair_002_sources/HurwitzOrbitCounting.lean

-- BEGIN SOURCE: proof_001/HurwitzCanonicalDegree.lean
section h77_bundle_03_HurwitzCanonicalDegree

/-! Canonical degree using analytic genus, without a topological HasGenus certificate.
This is the degree input for the actual quotient surface in the Hurwitz proof. -/

open scoped Manifold ContDiff

namespace LiZhongQC

/-- Riemann-Roch on D=0 and D=K gives the canonical degree on any actual
compact connected complex surface. The genus is the installed analytic genus. -/
theorem h77d_canonical_degree_analytic
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    {K : Divisor S} (hK : IsCanonicalDivisor K) :
    K.deg = 2 * (genus S : ℤ) - 2 := by
  have h0 := k22rr_riemann_roch_analytic hK (0 : Divisor S)
  have h1 := k22rr_riemann_roch_analytic hK K
  rw [sub_zero, ← k22rr_degree_eq (0 : Divisor S),
    Jacobians.Divisor.deg_zero] at h0
  rw [sub_self] at h1
  omega

/-- The analytic canonical degree is realized by an actual meromorphic differential. -/
theorem h77d_exists_canonical_degree_analytic
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] :
    ∃ K : Divisor S, IsCanonicalDivisor K ∧ K.deg = 2 * (genus S : ℤ) - 2 := by
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := S)
  exact ⟨K, hK, h77d_canonical_degree_analytic hK⟩

end LiZhongQC
end h77_bundle_03_HurwitzCanonicalDegree
-- END SOURCE: proof_001/HurwitzCanonicalDegree.lean

-- BEGIN SOURCE: chain_repair_004_sources/HurwitzMeromorphicPullback.lean
section h77_bundle_04_HurwitzMeromorphicPullback

/-! The actual pullback of a meromorphic cotangent section by a holomorphic map.
The construction uses the intrinsic differential and proves its coefficient formula. -/

open Set Filter
open scoped Manifold ContDiff Topology Bundle
open Jacobians.Dolbeault

namespace LiZhongQC

/-- Evaluation of a pulled-back covector in fixed source and target frames.
No meromorphy or nonvanishing assumption is used in this linear chain rule. -/
theorem h77d_pullback_frame
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    («π» : X → Y) {a q : X} {b : Y}
    (hq : q ∈ (chartAt ℂ a).source) (hpq : «π» q ∈ (chartAt ℂ b).source)
    (hπ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) «π» q)
    (σ : ∀ y, FormFiber Y y) :
    ((σ («π» q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q))
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) a).symmL ℂ q 1) =
    deriv (chartAt ℂ b ∘ «π» ∘ (chartAt ℂ a).symm) ((chartAt ℂ a) q) *
      σ («π» q) ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) b).symmL ℂ («π» q) 1) := by
  let E := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) b
  let v := mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) a).symmL ℂ q 1)
  have hbase : «π» q ∈ E.baseSet := hpq
  have hv : E.symmL ℂ («π» q) (E.continuousLinearMapAt ℂ («π» q) v) = v :=
    E.symmL_continuousLinearMapAt hbase v
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ b) («π» q) := by
    have h := mdifferentiableAt_extChartAt (I := 𝓘(ℂ)) (x := b) hpq
    exact h
  have hscalar : E.continuousLinearMapAt ℂ («π» q) v =
      deriv (chartAt ℂ b ∘ «π» ∘ (chartAt ℂ a).symm) ((chartAt ℂ a) q) := by
    have hE : E.continuousLinearMapAt ℂ («π» q) =
        mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ b) («π» q) := by
      change (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) b).continuousLinearMapAt
        ℂ («π» q) = _
      rw [TangentBundle.continuousLinearMapAt_trivializationAt hpq]
      rfl
    rw [hE]
    change mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ b) («π» q)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) a).symmL ℂ q 1)) = _
    rw [← mfderiv_comp_apply q hc hπ]
    exact mfderiv_apply_symmL_eq_deriv (chartAt ℂ b ∘ «π») hq (hc.comp q hπ)
  change σ («π» q) v = _
  calc
    σ («π» q) v = σ («π» q) (E.symmL ℂ («π» q) (E.continuousLinearMapAt ℂ («π» q) v)) :=
      congrArg (σ («π» q)) hv.symm
    _ = E.continuousLinearMapAt ℂ («π» q) v * σ («π» q) (E.symmL ℂ («π» q) 1) := by
      have hlin := (E.symmL ℂ («π» q)).map_smul
        (E.continuousLinearMapAt ℂ («π» q) v) (1 : ℂ)
      rw [smul_eq_mul, mul_one] at hlin
      rw [hlin, map_smul, smul_eq_mul]
    _ = _ := by rw [hscalar]

/-- Near each chart center, the actual pullback coefficient is the target coefficient
composed with the coordinate map and multiplied by its actual derivative. -/
theorem h77d_pullback_coefficient_eventuallyEq
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    («π» : X → Y) (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω «π»)
    (σ : ∀ y, FormFiber Y y) (x : X) :
    formCoeff (fun q => (σ («π» q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q)) x
      =ᶠ[𝓝 ((chartAt ℂ x) x)]
      fun z => deriv (chartAt ℂ («π» x) ∘ «π» ∘ (chartAt ℂ x).symm) z *
        formCoeff σ («π» x) ((chartAt ℂ («π» x) ∘ «π» ∘ (chartAt ℂ x).symm) z) := by
  have hx := mem_chart_source ℂ x
  have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hx)
  have hcont : ContinuousAt («π» ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    hπ.continuous.continuousAt.comp ((chartAt ℂ x).symm.continuousAt
      ((chartAt ℂ x).map_source hx))
  have hpre : («π» ∘ (chartAt ℂ x).symm) ⁻¹' (chartAt ℂ («π» x)).source ∈
      𝓝 ((chartAt ℂ x) x) := by
    apply hcont.preimage_mem_nhds
    change (chartAt ℂ («π» x)).source ∈ 𝓝 («π» ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
    rw [(chartAt ℂ x).left_inv hx]
    exact (chartAt ℂ («π» x)).open_source.mem_nhds (mem_chart_source ℂ («π» x))
  filter_upwards [htarget, hpre] with z hz hpz
  have hq : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).map_target hz
  have h := h77d_pullback_frame «π» (a := x) (q := (chartAt ℂ x).symm z)
    (b := «π» x) hq hpz
    (hπ.mdifferentiableAt (by decide)) σ
  rw [(chartAt ℂ x).right_inv hz] at h
  change σ («π» ((chartAt ℂ x).symm z))
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» ((chartAt ℂ x).symm z)
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ
        ((chartAt ℂ x).symm z) 1)) = _ at h
  change σ («π» ((chartAt ℂ x).symm z))
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» ((chartAt ℂ x).symm z)
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ
        ((chartAt ℂ x).symm z) 1)) = _
  rw [h]
  congr 1
  change σ («π» ((chartAt ℂ x).symm z)) _ =
    σ ((chartAt ℂ («π» x)).symm ((chartAt ℂ («π» x)) («π» ((chartAt ℂ x).symm z)))) _
  change «π» ((chartAt ℂ x).symm z) ∈ (chartAt ℂ («π» x)).source at hpz
  simp only [Function.comp_apply]
  rw [(chartAt ℂ («π» x)).left_inv hpz]
  rfl

/-- The intrinsic pullback section is meromorphic in every canonical chart. -/
theorem h77d_isMeromorphicOneForm_pullback
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    («π» : X → Y) (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω «π»)
    (σ : ∀ y, FormFiber Y y) (hσ : IsMeromorphicOneForm σ) :
    IsMeromorphicOneForm (fun q => (σ («π» q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q)) := by
  intro x
  let F : ℂ → ℂ := chartAt ℂ («π» x) ∘ «π» ∘ (chartAt ℂ x).symm
  have hF : AnalyticAt ℂ F ((chartAt ℂ x) x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hπ x
  have hFx : F ((chartAt ℂ x) x) = (chartAt ℂ («π» x)) («π» x) := by
    change (chartAt ℂ («π» x)) («π» ((chartAt ℂ x).symm ((chartAt ℂ x) x))) = _
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hm : MeromorphicAt (formCoeff σ («π» x)) (F ((chartAt ℂ x) x)) := by
    rw [hFx]
    exact hσ («π» x)
  have hc := hm.comp_analyticAt hF
  have hp := hF.deriv.meromorphicAt.mul hc
  exact hp.congr ((h77d_pullback_coefficient_eventuallyEq «π» hπ σ x).symm.filter_mono
    nhdsWithin_le_nhds)

/-- Existence of the actual pulled-back meromorphic differential, with its full
pointwise section and local coefficient identities. -/
theorem h77d_exists_meromorphic_pullback
    {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    («π» : X → Y) (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω «π»)
    (α : MeromorphicOneForm Y) :
    ∃ β : MeromorphicOneForm X,
      β.toFun = (fun q => (α.toFun («π» q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q)) ∧
      ∀ x, formCoeff β.toFun x =ᶠ[𝓝 ((chartAt ℂ x) x)]
        fun z => deriv (chartAt ℂ («π» x) ∘ «π» ∘ (chartAt ℂ x).symm) z *
          formCoeff α.toFun («π» x) ((chartAt ℂ («π» x) ∘ «π» ∘ (chartAt ℂ x).symm) z) := by
  let β : MeromorphicOneForm X :=
    ⟨fun q => (α.toFun («π» q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) «π» q),
      h77d_isMeromorphicOneForm_pullback «π» hπ α.toFun α.meromorphic⟩
  refine ⟨β, rfl, ?_⟩
  intro x
  exact h77d_pullback_coefficient_eventuallyEq «π» hπ α.toFun x

end LiZhongQC
end h77_bundle_04_HurwitzMeromorphicPullback
-- END SOURCE: chain_repair_004_sources/HurwitzMeromorphicPullback.lean

-- BEGIN SOURCE: proof_003/HurwitzDivisorSums.lean
section h77_bundle_05_HurwitzDivisorSums

/-! Finite divisor sums along fibers.
This is the algebraic consumer of actual orbit counting and actual local pullback orders;
it makes no geometric assertion about a map in its definitions. -/

open Set
open scoped BigOperators

namespace LiZhongQC

/-- Construct the weighted pullback as a genuinely finitely supported function.
Its degree is computed by regrouping the finite support over actual fibers. -/
theorem h77d_exists_weighted_pullback_divisor
    {X Y : Type*} (π : X → Y) (e : X → ℤ)
    (F : Y → Finset X) (hF : ∀ x y, x ∈ F y ↔ π x = y)
    (d : ℤ) (hsum : ∀ y, ∑ x ∈ F y, e x = d) (D : Y →₀ ℤ) :
    ∃ P : X →₀ ℤ,
      (∀ x, P x = e x * D (π x)) ∧ Finsupp.degree P = d * Finsupp.degree D := by
  classical
  let T := D.support.biUnion F
  have hsupport : ∀ x, e x * D (π x) ≠ 0 → x ∈ T := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨π x, Finsupp.mem_support_iff.mpr ?_, (hF x (π x)).mpr rfl⟩
    intro hz
    exact hx (by rw [hz, mul_zero])
  let P : X →₀ ℤ := Finsupp.onFinset T (fun x => e x * D (π x)) hsupport
  have hP : ∀ x, P x = e x * D (π x) := fun _ => Finsupp.onFinset_apply
  refine ⟨P, hP, ?_⟩
  have hmap : ∀ x ∈ T, π x ∈ D.support := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    rw [(hF x y).mp hxy]
    exact hy
  have hfilter : ∀ y ∈ D.support, T.filter (fun x => π x = y) = F y := by
    intro y hy
    ext x
    constructor
    · intro hx
      exact (hF x y).mpr (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨y, hy, hx⟩, (hF x y).mp hx⟩
  have hsumP : Finsupp.degree P = ∑ x ∈ T, e x * D (π x) := by
    change P.sum (fun _ n => n) = _
    exact Finsupp.sum_onFinset T _ hsupport (fun _ n => n) (fun _ _ => rfl)
  rw [hsumP, ← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    (∑ y ∈ D.support, ∑ x ∈ T with π x = y, e x * D (π x)) =
        ∑ y ∈ D.support, d * D y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hfilter y hy]
      calc
        (∑ x ∈ F y, e x * D (π x)) = ∑ x ∈ F y, e x * D y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(hF x y).mp hx]
        _ = d * D y := by rw [← Finset.sum_mul, hsum y]
    _ = d * Finsupp.degree D := by
      rw [Finsupp.degree_apply, Finset.mul_sum]

/-- Once the proved coefficient formula is substituted, the difference of the
two actual finite divisors has precisely the ramification coefficients. -/
theorem h77d_ramification_difference
    {X Y : Type*} (π : X → Y) (e : X → ℤ)
    (K P : X →₀ ℤ) (D : Y →₀ ℤ)
    (hP : ∀ x, P x = e x * D (π x))
    (hK : ∀ x, K x = e x * D (π x) + (e x - 1)) :
    (∀ x, (K - P) x = e x - 1) ∧ {x : X | e x ≠ 1}.Finite := by
  have hR : ∀ x, (K - P) x = e x - 1 := by
    intro x
    rw [Finsupp.sub_apply, hK x, hP x]
    ring
  refine ⟨hR, ?_⟩
  have hs : {x : X | e x ≠ 1} ⊆ (K - P).support := by
    intro x hx
    apply Finsupp.mem_support_iff.mpr
    rw [hR]
    exact sub_ne_zero.mpr hx
  exact (K - P).support.finite_toSet.subset hs

/-- Finite divisor subtraction gives the degree identity used in Riemann-Hurwitz.
All terms remain degrees of explicitly supplied finite divisors. -/
theorem h77d_ramification_degree_difference
    {X Y : Type*} (K P : X →₀ ℤ) (D : Y →₀ ℤ)
    (d : ℤ) (hP : Finsupp.degree P = d * Finsupp.degree D) :
    Finsupp.degree K = d * Finsupp.degree D + Finsupp.degree (K - P) := by
  rw [map_sub, hP]
  ring

end LiZhongQC
end h77_bundle_05_HurwitzDivisorSums
-- END SOURCE: proof_003/HurwitzDivisorSums.lean

-- BEGIN SOURCE: chain_repair_002_sources/HurwitzPullbackDivisor.lean
section h77_bundle_06_HurwitzPullbackDivisor

/-! Nontriviality and actual canonical divisor of a pulled-back meromorphic form.
Local multiplicity is derived from the analytic order of the actual coordinate map. -/

open Set Filter
open scoped Manifold ContDiff Topology
open Jacobians.Dolbeault

namespace LiZhongQC

/-- The local pullback order for an arbitrary nonconstant analytic map.
The integer r is the actual vanishing order of its derivative; its local degree is r+1. -/
theorem h77d_planar_pullback_order {f F : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicAt f (F c)) (hF : AnalyticAt ℂ F c)
    (hnc : ¬ EventuallyConst F (𝓝 c)) :
    ∃ r : ℕ,
      analyticOrderAt (fun z => F z - F c) c = ((r + 1 : ℕ) : ℕ∞) ∧
      meromorphicOrderAt (deriv F) c = (r : WithTop ℤ) ∧
      meromorphicOrderAt (fun z => deriv F z * f (F z)) c =
        (r : WithTop ℤ) + meromorphicOrderAt f (F c) * ((r + 1 : ℕ) : WithTop ℤ) := by
  have hne : analyticOrderAt (fun z => F z - F c) c ≠ ⊤ := by
    simpa only [eventuallyConst_iff_analyticOrderAt_sub_eq_top] using hnc
  have hadd := hF.analyticOrderAt_deriv_add_one
  have hdne : analyticOrderAt (deriv F) c ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hadd
    exact hne hadd.symm
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hdne
  have hdegree : analyticOrderAt (fun z => F z - F c) c = ((r + 1 : ℕ) : ℕ∞) := by
    rw [← hadd, ← hr]
    norm_cast
  have hdorder : meromorphicOrderAt (deriv F) c = (r : WithTop ℤ) := by
    rw [hF.deriv.meromorphicOrderAt_eq, ← hr, ENat.map_natCast, WithTop.coe_natCast]
  refine ⟨r, hdegree, hdorder, ?_⟩
  change meromorphicOrderAt (deriv F * (f ∘ F)) c = _
  rw [meromorphicOrderAt_mul hF.deriv.meromorphicAt (hf.comp_analyticAt hF),
    hdorder, hf.meromorphicOrderAt_comp hF hnc, hdegree, ENat.map_natCast,
    WithTop.coe_natCast]

section Surfaces

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- A globally nonconstant holomorphic map has a nonconstant coordinate germ at every point.
The installed analytic continuation theorem supplies this fact, not an interface assumption. -/
theorem h77d_chart_map_not_eventuallyConst (π : X → Y)
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap π) (x : X) :
    ¬ EventuallyConst (chartAt ℂ (π x) ∘ π ∘ (chartAt ℂ x).symm)
      (𝓝 ((chartAt ℂ x) x)) := by
  have hlocal :=
    Jacobians.Discharge.ContMDiff.Degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      (X := X) (Y := Y)
      Jacobians.Discharge.ContMDiff.Degree.clopennessOfLocallyConst_holds
  intro hconst
  rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hconst
  have hev := analyticOrderAt_eq_top.mp hconst
  apply hlocal π hπ hnc (π x) x rfl
  filter_upwards [hev] with z hz
  have hz' := sub_eq_zero.mp hz
  simpa only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hz'

/-- The order of the actual pulled-back form is computed from the actual coordinate map.
No divisor identity is assumed. -/
theorem h77d_pullback_form_order (π : X → Y)
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap π)
    (α : MeromorphicOneForm Y) (β : MeromorphicOneForm X)
    (hβ : β.toFun = fun q => (α.toFun (π q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) π q))
    (x : X) :
    ∃ r : ℕ,
      analyticOrderAt (fun z =>
        (chartAt ℂ (π x) ∘ π ∘ (chartAt ℂ x).symm) z - (chartAt ℂ (π x)) (π x))
        ((chartAt ℂ x) x) = ((r + 1 : ℕ) : ℕ∞) ∧
      β.formOrderW x = (r : WithTop ℤ) +
        α.formOrderW (π x) * ((r + 1 : ℕ) : WithTop ℤ) := by
  let F : ℂ → ℂ := chartAt ℂ (π x) ∘ π ∘ (chartAt ℂ x).symm
  have hFx : F ((chartAt ℂ x) x) = (chartAt ℂ (π x)) (π x) := by
    change (chartAt ℂ (π x)) (π ((chartAt ℂ x).symm ((chartAt ℂ x) x))) = _
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hF : AnalyticAt ℂ F ((chartAt ℂ x) x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hπ x
  have hm : MeromorphicAt (formCoeff α.toFun (π x)) (F ((chartAt ℂ x) x)) := by
    rw [hFx]
    exact α.meromorphic (π x)
  obtain ⟨r, hdegree, _hd, hord⟩ := h77d_planar_pullback_order hm hF
    (h77d_chart_map_not_eventuallyConst π hπ hnc x)
  refine ⟨r, ?_, ?_⟩
  · simpa only [hFx] using hdegree
  · change meromorphicOrderAt (formCoeff β.toFun x) ((chartAt ℂ x) x) =
      (r : WithTop ℤ) +
        meromorphicOrderAt (formCoeff α.toFun (π x)) ((chartAt ℂ (π x)) (π x)) *
          ((r + 1 : ℕ) : WithTop ℤ)
    rw [hβ, meromorphicOrderAt_congr
      ((h77d_pullback_coefficient_eventuallyEq π hπ α.toFun x).filter_mono nhdsWithin_le_nhds)]
    simpa only [hFx] using hord

/-- A nonzero meromorphic differential stays nonzero after pullback by a
nonconstant holomorphic map, including at every ramification point. -/
theorem h77d_pullback_form_order_ne_top (π : X → Y)
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap π)
    (α : MeromorphicOneForm Y) (hα : ∃ y, α.formOrderW y ≠ ⊤)
    (β : MeromorphicOneForm X)
    (hβ : β.toFun = fun q => (α.toFun (π q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) π q))
    (x : X) : β.formOrderW x ≠ ⊤ := by
  obtain ⟨r, _hr, hord⟩ := h77d_pullback_form_order π hπ hnc α β hβ x
  rw [hord]
  apply WithTop.add_ne_top.mpr
  exact ⟨WithTop.coe_ne_top, WithTop.mul_ne_top
    (MeromorphicOneForm.formOrderW_ne_top_of_exists α hα (π x)) WithTop.coe_ne_top⟩

/-- Construct the pulled-back form and its finite canonical divisor. Its coefficients
satisfy the ramification formula with the analytically derived local degree. -/
theorem h77d_exists_pullback_canonical_divisor (π : X → Y)
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap π)
    (α : MeromorphicOneForm Y) (hα : ∃ y, α.formOrderW y ≠ ⊤) :
    ∃ (β : MeromorphicOneForm X) (K : LiZhongQC.Divisor X),
      β.toFun = (fun q => (α.toFun (π q)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) π q)) ∧
      IsCanonicalDivisor K ∧
      (∀ x, β.formOrderW x = (K x : WithTop ℤ)) ∧
      ∀ x, ∃ r : ℕ,
        analyticOrderAt (fun z =>
          (chartAt ℂ (π x) ∘ π ∘ (chartAt ℂ x).symm) z - (chartAt ℂ (π x)) (π x))
          ((chartAt ℂ x) x) = ((r + 1 : ℕ) : ℕ∞) ∧
        (K x : WithTop ℤ) = (r : WithTop ℤ) +
          α.formOrderW (π x) * ((r + 1 : ℕ) : WithTop ℤ) := by
  obtain ⟨β, hβ, _hcoeff⟩ := h77d_exists_meromorphic_pullback π hπ α
  have hne := h77d_pullback_form_order_ne_top π hπ hnc α hα β hβ
  obtain ⟨K, hK⟩ := exists_form_divisor β hne
  let data : CanonicalForm17Data X :=
    { ω₀ := β
      nontrivial := ⟨Classical.choice (inferInstance : Nonempty X), hne _⟩
      K := K
      order_eq := hK }
  refine ⟨β, K, hβ, k22q_canonical_chart_coefficients data, hK, ?_⟩
  intro x
  obtain ⟨r, hdegree, hord⟩ := h77d_pullback_form_order π hπ hnc α β hβ x
  exact ⟨r, hdegree, (hK x).symm.trans hord⟩

end Surfaces
end LiZhongQC
end h77_bundle_06_HurwitzPullbackDivisor
-- END SOURCE: chain_repair_002_sources/HurwitzPullbackDivisor.lean

-- BEGIN SOURCE: proof_003/HurwitzOrbitDivisorDegree.lean
section h77_bundle_07_HurwitzOrbitDivisorDegree

/-! Divisor degree for actual finite group orbit fibers.
The weighted fiber sum is proved by orbit-stabilizer, not supplied as a hypothesis. -/

open Set
open scoped BigOperators

namespace LiZhongQC

/-- A finite group quotient supplies finite fiber enumerations and the exact sum
of the actual stabilizer orders on each fiber. -/
theorem h77d_orbit_fibers_with_degree
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hsurj : Function.Surjective π)
    (hfiber : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y) :
    ∃ F : Y → Finset X,
      (∀ x y, x ∈ F y ↔ π x = y) ∧
      ∀ y, (∑ x ∈ F y, (Nat.card (MulAction.stabilizer G x) : ℤ)) = (Nat.card G : ℤ) := by
  classical
  have hfin : ∀ y : Y, {x : X | π x = y}.Finite := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact h77d_quotient_fiber_finite π hfiber x
  let F : Y → Finset X := fun y => (hfin y).toFinset
  have hF : ∀ x y, x ∈ F y ↔ π x = y := by
    intro x y
    exact (hfin y).mem_toFinset
  refine ⟨F, hF, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  letI : Fintype {z : X // π z = π x} := (hfin (π x)).fintype
  rw [Finset.sum_subtype (F (π x)) (fun z => hF z (π x))]
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (h77d_quotient_fiber_sum_stabilizer π hfiber x)
  push_cast at h
  exact h

/-- The actual stabilizer-weighted pullback of every finite divisor has degree
equal to the group order times the original divisor degree. -/
theorem h77d_orbit_pullback_divisor_degree
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hsurj : Function.Surjective π)
    (hfiber : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y) (D : Y →₀ ℤ) :
    ∃ P : X →₀ ℤ,
      (∀ x, P x = (Nat.card (MulAction.stabilizer G x) : ℤ) * D (π x)) ∧
      Finsupp.degree P = (Nat.card G : ℤ) * Finsupp.degree D := by
  obtain ⟨F, hF, hsum⟩ := h77d_orbit_fibers_with_degree π hsurj hfiber
  exact h77d_exists_weighted_pullback_divisor π
    (fun x => (Nat.card (MulAction.stabilizer G x) : ℤ)) F hF (Nat.card G) hsum D

end LiZhongQC
end h77_bundle_07_HurwitzOrbitDivisorDegree
-- END SOURCE: proof_003/HurwitzOrbitDivisorDegree.lean

-- BEGIN SOURCE: ../gpt_20261014_round77_worker2_hurwitz_quotient/chain_repair_001/HurwitzPowerMultiplicity.lean
section h77_bundle_08_HurwitzPowerMultiplicity

/-! Local degree is unchanged by analytic coordinates with nonzero derivatives.
This identifies the canonical-chart multiplicity with a constructed power chart. -/

open Filter
open scoped Topology

namespace LiZhongQC

/-- A genuine power normal form determines the multiplicity of the actual map,
even when the source and target preferred coordinates are not the power coordinates. -/
theorem h77d_multiplicity_of_power_coordinates
    {F U V : ℂ → ℂ} {c : ℂ} (e : ℕ)
    (hF : AnalyticAt ℂ F c)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = c) (hUd : deriv U 0 ≠ 0)
    (hV : AnalyticAt ℂ V (F c)) (hVd : deriv V (F c) ≠ 0)
    (hpower : (fun z => V (F (U z)) - V (F c)) =ᶠ[𝓝 0] (fun z : ℂ => z ^ e)) :
    analyticOrderAt (fun z => F z - F c) c = (e : ℕ∞) := by
  have hH : AnalyticAt ℂ (fun z => F (U z)) 0 := by
    have hF' : AnalyticAt ℂ F (U 0) := by rw [hU0]; exact hF
    exact hF'.comp hU
  have hV' : AnalyticAt ℂ (fun w => V w - V (F c)) (F (U 0)) := by
    rw [hU0]
    exact hV.sub analyticAt_const
  have htarget :
      analyticOrderAt (fun z => V (F (U z)) - V (F c)) 0 =
        analyticOrderAt (fun z => F (U z) - F c) 0 := by
    have h := AnalyticAt.analyticOrderAt_comp
      (f := fun w => V w - V (F c)) (g := fun z => F (U z)) (z₀ := 0) hV' hH
    change analyticOrderAt (fun z => V (F (U z)) - V (F c)) 0 =
      analyticOrderAt (fun w => V w - V (F c)) (F (U 0)) *
        analyticOrderAt (fun z => F (U z) - F (U 0)) 0 at h
    simpa only [hU0,
      hV.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hVd, one_mul] using h
  have hsource :
      analyticOrderAt (fun z => F (U z) - F c) 0 =
        analyticOrderAt (fun z => F z - F c) c := by
    have h := analyticOrderAt_comp_of_deriv_ne_zero
      (f := fun z => F z - F c) (g := U) (z₀ := 0) hU hUd
    change analyticOrderAt (fun z => F (U z) - F c) 0 =
      analyticOrderAt (fun z => F z - F c) (U 0) at h
    simpa only [hU0] using h
  rw [← hsource, ← htarget, analyticOrderAt_congr hpower]
  exact h77d_power_analytic_order e

end LiZhongQC
end h77_bundle_08_HurwitzPowerMultiplicity
-- END SOURCE: ../gpt_20261014_round77_worker2_hurwitz_quotient/chain_repair_001/HurwitzPowerMultiplicity.lean

-- BEGIN SOURCE: ../gpt_20261014_round77_worker2_hurwitz_quotient/chain_repair_001/HurwitzChartMultiplicity.lean
section h77_bundle_09_HurwitzChartMultiplicity

/-! Transport a genuine manifold power chart to the preferred chart multiplicity. -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace LiZhongQC

/-- An analytic coordinate with analytic inverse has nonzero derivative. -/
theorem h77d_coordinate_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ) {z : ℂ}
    (hz : z ∈ e.source) (he : AnalyticAt ℂ e z)
    (hei : AnalyticAt ℂ e.symm (e z)) : deriv e z ≠ 0 := by
  intro hzero
  have hid : e.symm ∘ e =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact e.left_inv hw
  have h := deriv_comp z hei.differentiableAt he.differentiableAt
  rw [hid.deriv_eq, deriv_id, hzero, mul_zero] at h
  exact one_ne_zero h

/-- Two actual analytic surface coordinates give an analytic transition with
nonzero derivative, at every point of their common source. -/
theorem h77d_analytic_coordinate_transition
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (u v : OpenPartialHomeomorph X ℂ) (p : X)
    (hu : p ∈ u.source) (hv : p ∈ v.source)
    (huH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u u.source)
    (huiH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u.symm u.target)
    (hvH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v v.source)
    (hviH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v.symm v.target) :
    AnalyticAt ℂ (v ∘ u.symm) (u p) ∧ deriv (v ∘ u.symm) (u p) ≠ 0 := by
  have hUi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u.symm (u p) :=
    huiH.contMDiffAt (u.open_target.mem_nhds (u.mapsTo hu))
  have hV : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω v (u.symm (u p)) := by
    rw [u.left_inv hu]
    exact hvH.contMDiffAt (v.open_source.mem_nhds hv)
  have hA : AnalyticAt ℂ (v ∘ u.symm) (u p) :=
    (hV.comp (u p) hUi).contDiffAt.analyticAt
  have hVi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω v.symm (v p) :=
    hviH.contMDiffAt (v.open_target.mem_nhds (v.mapsTo hv))
  have hU : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u (v.symm (v p)) := by
    rw [v.left_inv hv]
    exact huH.contMDiffAt (u.open_source.mem_nhds hu)
  have hAi : AnalyticAt ℂ (u ∘ v.symm) (v p) :=
    (hU.comp (v p) hVi).contDiffAt.analyticAt
  refine ⟨hA, ?_⟩
  let e := u.symm.trans v
  have hmem : u p ∈ e.source := by
    change u p ∈ u.target ∧ u.symm (u p) ∈ v.source
    exact ⟨u.mapsTo hu, by rw [u.left_inv hu]; exact hv⟩
  have hei : AnalyticAt ℂ e.symm (e (u p)) := by
    change AnalyticAt ℂ (u ∘ v.symm) (v (u.symm (u p)))
    rw [u.left_inv hu]
    exact hAi
  exact h77d_coordinate_deriv_ne_zero e hmem hA hei

/-- A constructed power-chart identity yields the canonical-chart multiplicity
of the actual holomorphic map. No local degree or divisor formula is assumed. -/
theorem h77d_chart_multiplicity_of_power_model
    {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (π : X → Y) (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (p : X)
    (e : ℕ) (he : e ≠ 0)
    (u : OpenPartialHomeomorph X ℂ) (v : OpenPartialHomeomorph Y ℂ)
    (hu : p ∈ u.source) (hu0 : u p = 0) (hv : π p ∈ v.source)
    (huH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u u.source)
    (huiH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u.symm u.target)
    (hvH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v v.source)
    (hviH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v.symm v.target)
    (hpower : ∀ x ∈ u.source, v (π x) = (u x) ^ e) :
    analyticOrderAt (fun z =>
      (chartAt ℂ (π p) ∘ π ∘ (chartAt ℂ p).symm) z - (chartAt ℂ (π p)) (π p))
      ((chartAt ℂ p) p) = (e : ℕ∞) := by
  let F : ℂ → ℂ := chartAt ℂ (π p) ∘ π ∘ (chartAt ℂ p).symm
  let U : ℂ → ℂ := chartAt ℂ p ∘ u.symm
  let V : ℂ → ℂ := v ∘ (chartAt ℂ (π p)).symm
  have hui0 : u.symm 0 = p := by rw [← hu0, u.left_inv hu]
  have hU0 : U 0 = (chartAt ℂ p) p := by
    change (chartAt ℂ p) (u.symm 0) = _
    rw [hui0]
  have hFc : F ((chartAt ℂ p) p) = (chartAt ℂ (π p)) (π p) := by
    change (chartAt ℂ (π p)) (π ((chartAt ℂ p).symm ((chartAt ℂ p) p))) = _
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  obtain ⟨hUa, hUd⟩ := h77d_analytic_coordinate_transition u (chartAt ℂ p) p hu
    (mem_chart_source ℂ p) huH huiH (contMDiffOn_chart (I := 𝓘(ℂ)))
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)))
  rw [hu0] at hUa hUd
  obtain ⟨hVa, hVd⟩ := h77d_analytic_coordinate_transition (chartAt ℂ (π p)) v (π p)
    (mem_chart_source ℂ (π p)) hv (contMDiffOn_chart (I := 𝓘(ℂ)))
    (contMDiffOn_chart_symm (I := 𝓘(ℂ))) hvH hviH
  have hV0 : V (F ((chartAt ℂ p) p)) = 0 := by
    rw [hFc]
    change v ((chartAt ℂ (π p)).symm ((chartAt ℂ (π p)) (π p))) = 0
    rw [(chartAt ℂ (π p)).left_inv (mem_chart_source ℂ (π p)),
      hpower p hu, hu0, zero_pow he]
  have hnearU : ∀ᶠ z in 𝓝 0, z ∈ u.target := by
    have h := u.open_target.mem_nhds (u.mapsTo hu)
    rwa [hu0] at h
  have hUs : ∀ᶠ z in 𝓝 0, u.symm z ∈ (chartAt ℂ p).source := by
    have hcont := u.symm.continuousAt (show 0 ∈ u.target by simpa only [hu0] using u.mapsTo hu)
    apply hcont.preimage_mem_nhds
    rw [hui0]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have hYs : ∀ᶠ z in 𝓝 0, π (u.symm z) ∈ (chartAt ℂ (π p)).source := by
    have hcont := hπ.continuous.continuousAt.comp
      (u.symm.continuousAt (show 0 ∈ u.target by simpa only [hu0] using u.mapsTo hu))
    apply hcont.preimage_mem_nhds
    change (chartAt ℂ (π p)).source ∈ 𝓝 (π (u.symm 0))
    rw [hui0]
    exact (chartAt ℂ (π p)).open_source.mem_nhds (mem_chart_source ℂ (π p))
  have hlocal : (fun z => V (F (U z)) - V (F ((chartAt ℂ p) p))) =ᶠ[𝓝 0]
      (fun z : ℂ => z ^ e) := by
    filter_upwards [hnearU, hUs, hYs] with z hz hzs hzt
    rw [hV0, sub_zero]
    change v ((chartAt ℂ (π p)).symm
      ((chartAt ℂ (π p)) (π ((chartAt ℂ p).symm ((chartAt ℂ p) (u.symm z)))))) = _
    rw [(chartAt ℂ p).left_inv hzs, (chartAt ℂ (π p)).left_inv hzt,
      hpower _ (u.map_target hz), u.right_inv hz]
  have hF : AnalyticAt ℂ F ((chartAt ℂ p) p) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hπ p
  have h := h77d_multiplicity_of_power_coordinates e hF hUa hU0 hUd
    (hFc.symm ▸ hVa) (hFc.symm ▸ hVd) hlocal
  simpa only [hFc] using h

end LiZhongQC
end h77_bundle_09_HurwitzChartMultiplicity
-- END SOURCE: ../gpt_20261014_round77_worker2_hurwitz_quotient/chain_repair_001/HurwitzChartMultiplicity.lean

-- BEGIN SOURCE: chain_repair_002_sources/HurwitzRiemannHurwitz.lean
section h77_bundle_10_HurwitzRiemannHurwitz

/-! Riemann-Hurwitz consumer for the actual finite group quotient.
Only the geometric local multiplicity of its projection remains an input;
all divisor constructions, finite branching and degree identities are proved here. -/

open Set
open scoped Manifold ContDiff Topology
open Jacobians.Dolbeault

namespace LiZhongQC

/-- Riemann-Hurwitz from a genuine holomorphic orbit projection whose local
multiplicity is the stabilizer order. The latter is supplied by the actual power charts,
using h77d_multiplicity_of_power_coordinates, not by a global degree premise. -/
theorem h77d_riemann_hurwitz_of_quotient_multiplicity
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (π : X → Y) (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap π)
    (hsurj : Function.Surjective π)
    (hfiber : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y)
    (hloc : ∀ x, analyticOrderAt (fun z =>
        (chartAt ℂ (π x) ∘ π ∘ (chartAt ℂ x).symm) z - (chartAt ℂ (π x)) (π x))
        ((chartAt ℂ x) x) = (Nat.card (MulAction.stabilizer G x) : ℕ∞)) :
    ∃ R : X →₀ ℤ,
      (∀ x, R x = (Nat.card (MulAction.stabilizer G x) : ℤ) - 1) ∧
      {x : X | Nat.card (MulAction.stabilizer G x) ≠ 1}.Finite ∧
      2 * (genus X : ℤ) - 2 =
        (Nat.card G : ℤ) * (2 * (genus Y : ℤ) - 2) + Finsupp.degree R := by
  obtain ⟨D, hD⟩ := k22q_canonical_exists (S := Y)
  obtain ⟨data, hdata⟩ := k22rr_canonical_data hD
  obtain ⟨β, K, _hβ, hK, _hKorder, horders⟩ :=
    h77d_exists_pullback_canonical_divisor π hπ hnc data.ω₀ data.nontrivial
  have hDorder : ∀ y, data.ω₀.formOrderW y = (D y : WithTop ℤ) := by
    intro y
    rw [data.order_eq, hdata]
  obtain ⟨P, hP, hPdeg⟩ := h77d_orbit_pullback_divisor_degree π hsurj hfiber D
  have hcoeff : ∀ x, K x =
      (Nat.card (MulAction.stabilizer G x) : ℤ) * D (π x) +
        ((Nat.card (MulAction.stabilizer G x) : ℤ) - 1) := by
    intro x
    obtain ⟨r, hdegree, hord⟩ := horders x
    have hcard : r + 1 = Nat.card (MulAction.stabilizer G x) := by
      exact_mod_cast hdegree.symm.trans (hloc x)
    rw [hDorder] at hord
    have hKint : K x = (r : ℤ) + D (π x) * (r + 1 : ℕ) := by
      exact_mod_cast hord
    rw [← hcard, hKint]
    push_cast
    ring
  obtain ⟨hR, hfinite⟩ := h77d_ramification_difference π
    (fun x => (Nat.card (MulAction.stabilizer G x) : ℤ)) K P D hP hcoeff
  refine ⟨K - P, hR, ?_, ?_⟩
  · apply hfinite.subset
    intro x hx
    change (Nat.card (MulAction.stabilizer G x) : ℤ) ≠ 1
    intro heq
    apply hx
    exact_mod_cast heq
  · have hdeg := h77d_ramification_degree_difference K P D (Nat.card G) hPdeg
    have hKdeg := h77d_canonical_degree_analytic hK
    have hDdeg := h77d_canonical_degree_analytic hD
    change Finsupp.degree K = 2 * (genus X : ℤ) - 2 at hKdeg
    change Finsupp.degree D = 2 * (genus Y : ℤ) - 2 at hDdeg
    rw [hKdeg, hDdeg] at hdeg
    exact hdeg

end LiZhongQC
end h77_bundle_10_HurwitzRiemannHurwitz
-- END SOURCE: chain_repair_002_sources/HurwitzRiemannHurwitz.lean

-- BEGIN SOURCE: chain_repair_002_sources/HurwitzFiniteActionRH.lean
section h77_bundle_11_HurwitzFiniteActionRH

/-! Riemann-Hurwitz for the constructed finite analytic group quotient.
No global quotient, degree or divisor conclusion is supplied as a hypothesis. -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace LiZhongQC

/-- The genuine finite-action quotient satisfies Riemann-Hurwitz with analytic genus.
The quotient manifold, projection and power charts are all constructed from the action. -/
theorem h77d_finite_action_riemann_hurwitz
    {G X : Type*} [Group G] [Finite G]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    letI : T2Space (h84g_OrbitSpace ρ) := h84g_orbitSpace_t2 ρ
    letI : CompactSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_compact ρ
    letI : ConnectedSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_connected ρ
    ∃ c : ChartedSpace ℂ (h84g_OrbitSpace ρ),
      letI := c
      ∃ hM : IsManifold 𝓘(ℂ) ω (h84g_OrbitSpace ρ),
        letI := hM
        ∃ R : X →₀ ℤ,
          (∀ x, R x = (Nat.card (h84a_pointStabilizer ρ x) : ℤ) - 1) ∧
          {x : X | Nat.card (h84a_pointStabilizer ρ x) ≠ 1}.Finite ∧
          2 * (genus X : ℤ) - 2 =
            (Nat.card G : ℤ) * (2 * (genus (h84g_OrbitSpace ρ) : ℤ) - 2) +
              Finsupp.degree R := by
  classical
  letI : T2Space (h84g_OrbitSpace ρ) := h84g_orbitSpace_t2 ρ
  letI : CompactSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_compact ρ
  letI : ConnectedSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_connected ρ
  obtain ⟨c, hM, hπ, hmodels⟩ := h84g_exists_complex_quotient ρ hρ hHol
  letI := c
  letI : IsManifold 𝓘(ℂ) ω (h84g_OrbitSpace ρ) := hM
  letI : MulAction G X :=
    { smul := fun g x => ρ g x
      one_smul := by
        intro x
        change ρ 1 x = x
        rw [map_one, Homeomorph.one_apply]
      mul_smul := by
        intro g h x
        change ρ (g * h) x = ρ g (ρ h x)
        rw [map_mul, Homeomorph.mul_apply] }
  have hstab : ∀ x : X, MulAction.stabilizer G x = h84a_pointStabilizer ρ x := by
    intro x
    ext g
    rfl
  have hloc : ∀ x : X, analyticOrderAt (fun z =>
      (chartAt ℂ (h84g_orbitMap ρ x) ∘ h84g_orbitMap ρ ∘ (chartAt ℂ x).symm) z -
        (chartAt ℂ (h84g_orbitMap ρ x)) (h84g_orbitMap ρ x))
        ((chartAt ℂ x) x) = (Nat.card (MulAction.stabilizer G x) : ℕ∞) := by
    intro x
    obtain ⟨r, u, v, _hr, hu, hu0, _huT, huH, huiH, hvH, hviH, hvS, _hvT, hp⟩ :=
      hmodels x
    have hv : h84g_orbitMap ρ x ∈ v.source := by
      rw [hvS]
      exact ⟨x, hu, rfl⟩
    rw [hstab x]
    exact h77d_chart_multiplicity_of_power_model (h84g_orbitMap ρ) hπ x
      (Nat.card (h84a_pointStabilizer ρ x)) Nat.card_pos.ne'
      u v hu hu0 hv huH huiH hvH hviH hp
  have hnc : ¬ Jacobians.Discharge.IsConstantMap (h84g_orbitMap ρ) := by
    intro hconst
    change ∃ y, ∀ x, h84g_orbitMap ρ x = y at hconst
    obtain ⟨y, hy⟩ := hconst
    let x : X := Classical.choice (inferInstance : Nonempty X)
    have h := hloc x
    have heq : (fun z =>
        (chartAt ℂ (h84g_orbitMap ρ x) ∘ h84g_orbitMap ρ ∘ (chartAt ℂ x).symm) z -
          (chartAt ℂ (h84g_orbitMap ρ x)) (h84g_orbitMap ρ x)) = (0 : ℂ → ℂ) := by
      funext z
      change (chartAt ℂ (h84g_orbitMap ρ x)) (h84g_orbitMap ρ ((chartAt ℂ x).symm z)) -
        (chartAt ℂ (h84g_orbitMap ρ x)) (h84g_orbitMap ρ x) = 0
      rw [hy ((chartAt ℂ x).symm z), hy x, sub_self]
    rw [heq, analyticOrderAt_zero] at h
    exact (ENat.natCast_ne_top (Nat.card (MulAction.stabilizer G x))) h.symm
  have hfiber : ∀ x y : X,
      h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔ ∃ g : G, g • x = y :=
    h84g_orbitMap_eq_iff ρ
  obtain ⟨R, hR, hfinite, hRH⟩ :=
    h77d_riemann_hurwitz_of_quotient_multiplicity (h84g_orbitMap ρ) hπ hnc
      (h84g_orbitMap_surjective ρ) hfiber hloc
  refine ⟨c, hM, R, ?_, ?_, hRH⟩
  · intro x
    simpa only [hstab x] using hR x
  · simpa only [hstab] using hfinite

end LiZhongQC
end h77_bundle_11_HurwitzFiniteActionRH
-- END SOURCE: chain_repair_002_sources/HurwitzFiniteActionRH.lean

-- BEGIN SOURCE: chain_repair_003_sources/HurwitzBranchDefect.lean
section h77_bundle_12_HurwitzBranchDefect

/-! Enumerate the actual finite branch values and sum the ramification divisor
fiber by fiber to obtain the classical orbifold defect. -/

open Set
open scoped BigOperators

namespace LiZhongQC

/-- The branch orders and defect sum are constructed from the actual finite
ramification divisor and actual orbit fibers. -/
theorem h77d_branch_defect_of_ramification
    {G X Y : Type*} [Group G] [Finite G] [MulAction G X]
    (π : X → Y) (hsurj : Function.Surjective π)
    (hfiber : ∀ x y, π x = π y ↔ ∃ g : G, g • x = y)
    (R : X →₀ ℤ)
    (hR : ∀ x, R x = (Nat.card (MulAction.stabilizer G x) : ℤ) - 1) :
    ∃ (m : ℕ) (e : Fin m → ℕ),
      (∀ i, 2 ≤ e i) ∧
      ((Finsupp.degree R : ℤ) : ℝ) = (Nat.card G : ℝ) * ∑ i, (1 - 1 / (e i : ℝ)) := by
  classical
  obtain ⟨F, hF, hsum⟩ := h77d_orbit_fibers_with_degree π hsurj hfiber
  let B : Finset Y := R.support.image π
  have hrepresentative : ∀ y : B, ∃ x ∈ R.support, π x = (y : Y) := by
    intro y
    exact Finset.mem_image.mp y.property
  choose a ha hπa using hrepresentative
  let E : B → ℕ := fun y => Nat.card (MulAction.stabilizer G (a y))
  have hEpos : ∀ y, 0 < E y := by
    intro y
    exact Nat.card_pos
  have hEtwo : ∀ y, 2 ≤ E y := by
    intro y
    have hne : R (a y) ≠ 0 := Finsupp.mem_support_iff.mp (ha y)
    rw [hR] at hne
    have hEne : E y ≠ 1 := by
      intro h
      apply hne
      change (E y : ℤ) - 1 = 0
      rw [h]
      norm_num
    have hpos : 0 < E y := hEpos y
    omega
  have hconstant : ∀ y : B, ∀ x : X, π x = (y : Y) →
      Nat.card (MulAction.stabilizer G x) = E y := by
    intro y x hx
    apply h77d_stabilizer_card_eq_of_mem_orbit
    exact (hfiber (a y) x).mp ((hπa y).trans hx.symm)
  have hfilter : ∀ y : B,
      R.support.filter (fun x => π x = (y : Y)) = F y := by
    intro y
    ext x
    constructor
    · intro hx
      exact (hF x y).mpr (Finset.mem_filter.mp hx).2
    · intro hx
      have hxy := (hF x y).mp hx
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hxy⟩
      rw [hR, hconstant y x hxy]
      have htwo := hEtwo y
      exact sub_ne_zero.mpr (by exact_mod_cast (show E y ≠ 1 by omega))
  have hcontribution : ∀ y : B,
      (∑ x ∈ R.support with π x = (y : Y), (R x : ℝ)) =
        (Nat.card G : ℝ) * (1 - 1 / (E y : ℝ)) := by
    intro y
    have hcount : ((F y).card : ℤ) * (E y : ℤ) = (Nat.card G : ℤ) := by
      have h := hsum (y : Y)
      calc
        ((F y).card : ℤ) * (E y : ℤ) =
            ∑ x ∈ F y, (Nat.card (MulAction.stabilizer G x) : ℤ) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_congr rfl
          intro x hx
          rw [hconstant y x ((hF x y).mp hx)]
        _ = _ := h
    have hcountR : ((F y).card : ℝ) * (E y : ℝ) = (Nat.card G : ℝ) := by
      exact_mod_cast hcount
    have hEnz : (E y : ℝ) ≠ 0 := by exact_mod_cast (hEpos y).ne'
    rw [hfilter y]
    calc
      (∑ x ∈ F y, (R x : ℝ)) = ∑ _x ∈ F y, ((E y : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hR, hconstant y x ((hF x y).mp hx)]
        push_cast
        rfl
      _ = ((F y).card : ℝ) * ((E y : ℝ) - 1) := by simp <;> ring
      _ = (((F y).card : ℝ) * (E y : ℝ)) * (1 - 1 / (E y : ℝ)) := by
        field_simp [hEnz]
        <;> ring
      _ = _ := by rw [hcountR]
  have htotal : ((Finsupp.degree R : ℤ) : ℝ) =
      (Nat.card G : ℝ) * ∑ y : B, (1 - 1 / (E y : ℝ)) := by
    have hmap : ∀ x ∈ R.support, π x ∈ B := fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hdeg : ((Finsupp.degree R : ℤ) : ℝ) = ∑ x ∈ R.support, (R x : ℝ) := by
      rw [Finsupp.degree_apply]
      push_cast
      rfl
    rw [hdeg, ← Finset.sum_fiberwise_of_maps_to hmap]
    rw [← Finset.sum_coe_sort]
    calc
      (∑ y : B, ∑ x ∈ R.support with π x = (y : Y), (R x : ℝ)) =
          ∑ y : B, (Nat.card G : ℝ) * (1 - 1 / (E y : ℝ)) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hcontribution y
      _ = _ := (Finset.mul_sum _ _ _).symm
  let σ : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  refine ⟨Fintype.card B, fun i => E (σ i), fun i => hEtwo (σ i), ?_⟩
  rw [htotal]
  congr 1
  exact (Equiv.sum_comp σ (fun y : B => (1 - 1 / (E y : ℝ)))).symm

end LiZhongQC
end h77_bundle_12_HurwitzBranchDefect
-- END SOURCE: chain_repair_003_sources/HurwitzBranchDefect.lean

-- BEGIN SOURCE: chain_repair_002_sources/HurwitzTerminal.lean
section h77_bundle_13_HurwitzTerminal

/-! Terminal Hurwitz bound from the actual finite automorphism action,
the constructed quotient, the proved divisor formula and the sharp numerical defect. -/

open Set
open scoped Manifold ContDiff BigOperators

namespace LiZhongQC

/-- Every faithful finite analytic action on a compact surface of analytic genus
greater than one has order at most 84 times genus minus one. -/
theorem h77d_finite_analytic_action_bound
    {G X : Type*} [Group G] [Finite G]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g))
    (hg : 1 < genus X) : Nat.card G ≤ 84 * (genus X - 1) := by
  classical
  letI : T2Space (h84g_OrbitSpace ρ) := h84g_orbitSpace_t2 ρ
  letI : CompactSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_compact ρ
  letI : ConnectedSpace (h84g_OrbitSpace ρ) := h84g_orbitSpace_connected ρ
  obtain ⟨c, hM, R, hR, _hfinite, hRH⟩ := h77d_finite_action_riemann_hurwitz ρ hρ hHol
  letI := c
  letI : IsManifold 𝓘(ℂ) ω (h84g_OrbitSpace ρ) := hM
  letI : MulAction G X :=
    { smul := fun g x => ρ g x
      one_smul := by
        intro x
        change ρ 1 x = x
        rw [map_one, Homeomorph.one_apply]
      mul_smul := by
        intro g h x
        change ρ (g * h) x = ρ g (ρ h x)
        rw [map_mul, Homeomorph.mul_apply] }
  have hstab : ∀ x : X, MulAction.stabilizer G x = h84a_pointStabilizer ρ x := by
    intro x
    ext g
    rfl
  have hfiber : ∀ x y : X,
      h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔ ∃ g : G, g • x = y :=
    h84g_orbitMap_eq_iff ρ
  have hR' : ∀ x, R x = (Nat.card (MulAction.stabilizer G x) : ℤ) - 1 := by
    intro x
    simpa only [hstab x] using hR x
  obtain ⟨m, e, he, hdefect⟩ := h77d_branch_defect_of_ramification
    (h84g_orbitMap ρ) (h84g_orbitMap_surjective ρ) hfiber R hR'
  have hreal : 2 * (genus X : ℝ) - 2 =
      (Nat.card G : ℝ) * (2 * (genus (h84g_OrbitSpace ρ) : ℝ) - 2) +
        ((Finsupp.degree R : ℤ) : ℝ) := by
    exact_mod_cast hRH
  rw [hdefect, ← mul_add] at hreal
  have hn : 0 < Nat.card G := Nat.card_pos
  have hnR : (0 : ℝ) < Nat.card G := by exact_mod_cast hn
  have hgR : (1 : ℝ) < genus X := by exact_mod_cast hg
  have hd : 0 < 2 * (genus (h84g_OrbitSpace ρ) : ℝ) - 2 +
      ∑ i, (1 - 1 / (e i : ℝ)) := by
    by_contra h
    have hnonpos : (Nat.card G : ℝ) *
        (2 * (genus (h84g_OrbitSpace ρ) : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnR.le (le_of_not_gt h)
    linarith
  exact h84_hurwitz_order_bound e he hd hn hreal


end LiZhongQC
end h77_bundle_13_HurwitzTerminal
-- END SOURCE: chain_repair_002_sources/HurwitzTerminal.lean

