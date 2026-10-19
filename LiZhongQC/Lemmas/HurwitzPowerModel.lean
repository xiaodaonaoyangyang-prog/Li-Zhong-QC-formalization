import Mathlib
import LiZhongQC.Lemmas.HurwitzWeightedAverage

/-! Local power-map models for finite faithful analytic stabilizers.
Orbit fibers and a disk quotient homeomorphism are constructed explicitly. -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- Every tangent multiplier is a root of unity of degree equal to the group order. -/
theorem h84q_character_pow_card {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (g : H) : (χ g : ℂ) ^ Fintype.card H = 1 := by
  have h : (χ g) ^ Fintype.card H = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hc := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hc

/-- A faithful character contains all roots of unity of degree card H.
Injectivity and the exact complex root count give surjectivity onto those roots. -/
theorem h84q_character_covers_roots {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (hχ : Function.Injective χ) {u : ℂ}
    (hu : u ^ Fintype.card H = 1) :
    ∃ g : H, (χ g : ℂ) = u := by
  let f : H → rootsOfUnity (Fintype.card H) ℂ := fun g =>
    ⟨χ g, (mem_rootsOfUnity' _ _).mpr (h84q_character_pow_card χ g)⟩
  have hf : Function.Injective f := by
    intro g h hgh
    apply hχ
    exact congrArg (fun ζ : rootsOfUnity (Fintype.card H) ℂ => (ζ : ℂˣ)) hgh
  have hc : Nat.card H = Nat.card (rootsOfUnity (Fintype.card H) ℂ) := by
    calc
      Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
      _ = Nat.card (rootsOfUnity (Fintype.card H) ℂ) :=
        (Complex.card_rootsOfUnity (Fintype.card H)).symm
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2
  obtain ⟨g, hg⟩ := hs (rootsOfUnity.mkOfPowEq u hu)
  refine ⟨g, ?_⟩
  have hval := congrArg
    (fun ζ : rootsOfUnity (Fintype.card H) ℂ => ((ζ : ℂˣ) : ℂ)) hg
  simpa only [rootsOfUnity.coe_mkOfPowEq] using hval

/-- The fibers of the power map are exactly the orbits of the faithful character.
The zero fiber is handled separately, so division is used only with a nonzero denominator. -/
theorem h84q_power_fiber_iff_orbit {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (hχ : Function.Injective χ) (z w : ℂ) :
    z ^ Fintype.card H = w ^ Fintype.card H ↔
      ∃ g : H, w = (χ g : ℂ) * z := by
  constructor
  · intro hpow
    by_cases hz : z = 0
    · have hwPow : w ^ Fintype.card H = 0 := by
        rw [← hpow, hz, zero_pow Fintype.card_ne_zero]
      have hw : w = 0 := by
        by_contra hw
        exact (pow_ne_zero _ hw) hwPow
      refine ⟨1, ?_⟩
      rw [hw, hz, mul_zero]
    · have hu : (w / z) ^ Fintype.card H = 1 := by
        rw [div_pow, ← hpow, div_self (pow_ne_zero _ hz)]
      obtain ⟨g, hg⟩ := h84q_character_covers_roots χ hχ hu
      refine ⟨g, ?_⟩
      rw [hg, div_mul_cancel₀ w hz]
  · rintro ⟨g, rfl⟩
    rw [mul_pow, h84q_character_pow_card χ g, one_mul]

/-- Every fiber over a nonzero source value has exactly card H distinct points.
The bijection is g ↦ chi(g) z; freeness uses z ≠ 0 and character injectivity. -/
theorem h84q_power_fiber_card {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (hχ : Function.Injective χ) (z : ℂ) (hz : z ≠ 0) :
    Nat.card {w : ℂ // w ^ Fintype.card H = z ^ Fintype.card H} = Fintype.card H := by
  let f : H → {w : ℂ // w ^ Fintype.card H = z ^ Fintype.card H} := fun g =>
    ⟨(χ g : ℂ) * z, by rw [mul_pow, h84q_character_pow_card χ g, one_mul]⟩
  have hf : Function.Injective f := by
    intro g h hgh
    have hv := congrArg Subtype.val hgh
    change (χ g : ℂ) * z = (χ h : ℂ) * z at hv
    apply hχ
    apply Units.ext
    exact mul_right_cancel₀ hz hv
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨g, hg⟩ :=
      (h84q_power_fiber_iff_orbit χ hχ z (w : ℂ)).mp w.property.symm
    exact ⟨g, Subtype.ext hg.symm⟩
  calc
    Nat.card {w : ℂ // w ^ Fintype.card H = z ^ Fintype.card H} =
        Nat.card H := (Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)).symm
    _ = Fintype.card H := Nat.card_eq_fintype_card

/-- Finite tangent characters act by rotations. -/
theorem h84q_character_norm {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (g : H) : ‖(χ g : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (h84q_character_pow_card χ g) Fintype.card_ne_zero

/-- Centered disks are invariant under the actual tangent character. -/
theorem h84q_character_mapsTo_ball {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (g : H) (r : ℝ) :
    MapsTo (fun z => (χ g : ℂ) * z) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := by
  intro z hz
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
    h84q_character_norm χ g, one_mul] using hz

/-- The power map takes the radius-r disk into the radius-r^n disk. -/
theorem h84q_power_mapsTo_ball (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    MapsTo (fun z : ℂ => z ^ n) (Metric.ball 0 r) (Metric.ball 0 (r ^ n)) := by
  intro z hz
  have hz' : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hpow := pow_lt_pow_left₀ hz' (norm_nonneg z) hn
  simpa only [Metric.mem_ball, dist_zero_right, norm_pow] using hpow

/-- The explicit disk power map, including its range proof. -/
noncomputable def h84q_diskPower (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    Metric.ball (0 : ℂ) r → Metric.ball (0 : ℂ) (r ^ n) :=
  fun z => ⟨(z : ℂ) ^ n, h84q_power_mapsTo_ball n hn r z.property⟩

/-- The disk power map is continuous, open and onto the stated disk.
Surjectivity follows from complex roots and the exact norm-power identity. -/
theorem h84q_diskPower_isOpenQuotientMap (n : ℕ) (hn : n ≠ 0)
    (r : ℝ) (hr : 0 < r) : IsOpenQuotientMap (h84q_diskPower n hn r) := by
  letI : NeZero n := ⟨hn⟩
  have hglobal := Complex.isOpenQuotientMap_pow n
  refine ⟨?_, ?_, ?_⟩
  · intro w
    obtain ⟨z, hz⟩ := hglobal.surjective (w : ℂ)
    change z ^ n = (w : ℂ) at hz
    have hnorm : ‖z‖ ^ n < r ^ n := by
      rw [← norm_pow, hz]
      simpa only [Metric.mem_ball, dist_zero_right] using w.property
    have hzr : ‖z‖ < r := lt_of_pow_lt_pow_left₀ n hr.le hnorm
    have hzball : z ∈ Metric.ball (0 : ℂ) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hzr
    refine ⟨⟨z, hzball⟩, ?_⟩
    apply Subtype.ext
    exact hz
  · exact (hglobal.continuous.comp continuous_subtype_val).subtype_mk _
  · exact hglobal.isOpenMap.mapsToRestrict Metric.isOpen_ball
      (h84q_power_mapsTo_ball n hn r)

/-- The actual character orbit relation on a disk, before using faithfulness. -/
noncomputable def h84q_diskOrbitSetoid {H : Type*} [Group H]
    (χ : H →* ℂˣ) (r : ℝ) : Setoid (Metric.ball (0 : ℂ) r) where
  r z w := ∃ g : H, (w : ℂ) = (χ g : ℂ) * (z : ℂ)
  iseqv := by
    constructor
    · intro z
      refine ⟨1, ?_⟩
      rw [map_one, Units.val_one, one_mul]
    · intro z w hzw
      rcases hzw with ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      have hinv : (χ (g⁻¹) : ℂ) * (χ g : ℂ) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      rw [hg, ← mul_assoc, hinv, one_mul]
    · intro z w v hzw hwv
      rcases hzw with ⟨g, hg⟩
      rcases hwv with ⟨h, hh⟩
      refine ⟨h * g, ?_⟩
      rw [hh, hg, map_mul, Units.val_mul, mul_assoc]

/-- The orbit relation equals the equivalence relation defined by equal power-map values. -/
theorem h84q_diskOrbit_iff_power_eq {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (hχ : Function.Injective χ) (r : ℝ)
    (z w : Metric.ball (0 : ℂ) r) :
    h84q_diskOrbitSetoid χ r z w ↔
      h84q_diskPower (Fintype.card H) Fintype.card_ne_zero r z =
        h84q_diskPower (Fintype.card H) Fintype.card_ne_zero r w := by
  change (∃ g : H, (w : ℂ) = (χ g : ℂ) * (z : ℂ)) ↔ _
  rw [Subtype.ext_iff]
  exact (h84q_power_fiber_iff_orbit χ hχ (z : ℂ) (w : ℂ)).symm

/-- The actual orbit space of the disk is homeomorphic to the radius-r^card(H) disk.
The homeomorphism sends the orbit of z to z^card(H). -/
theorem h84q_diskOrbit_exists_homeomorph {H : Type*} [Group H] [Fintype H]
    (χ : H →* ℂˣ) (hχ : Function.Injective χ) (r : ℝ) (hr : 0 < r) :
    ∃ e : Quotient (h84q_diskOrbitSetoid χ r) ≃ₜ
        Metric.ball (0 : ℂ) (r ^ Fintype.card H),
      ∀ z : Metric.ball (0 : ℂ) r,
        e (Quotient.mk (h84q_diskOrbitSetoid χ r) z) =
          h84q_diskPower (Fintype.card H) Fintype.card_ne_zero r z := by
  let q : C(Metric.ball (0 : ℂ) r, Metric.ball (0 : ℂ) (r ^ Fintype.card H)) :=
    ⟨h84q_diskPower (Fintype.card H) Fintype.card_ne_zero r,
      (h84q_diskPower_isOpenQuotientMap (Fintype.card H) Fintype.card_ne_zero r hr).continuous⟩
  have hq : Topology.IsQuotientMap q :=
    (h84q_diskPower_isOpenQuotientMap (Fintype.card H) Fintype.card_ne_zero r hr).isQuotientMap
  let e₁ : Quotient (h84q_diskOrbitSetoid χ r) ≃ₜ Quotient (Setoid.ker q) :=
    Homeomorph.Quotient.congrRight (fun z w =>
      h84q_diskOrbit_iff_power_eq χ hχ r z w)
  let e₂ := hq.homeomorph
  refine ⟨e₁.trans e₂, ?_⟩
  intro z
  rfl

/-- Away from zero the power map has nonzero derivative and an actual local inverse. -/
theorem h84q_power_local_homeomorph_away_zero (n : ℕ) (hn : n ≠ 0)
    (z : ℂ) (hz : z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = (fun w => w ^ n) ∧ z ∈ e.source := by
  have hne : (n : ℂ) * z ^ (n - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hz)
  let hf := (hasStrictDerivAt_pow n z).hasStrictFDerivAt_equiv hne
  exact ⟨hf.toOpenPartialHomeomorph (fun w : ℂ => w ^ n), rfl,
    hf.mem_toOpenPartialHomeomorph_source⟩

/-- For degree greater than one, the central point is critical. -/
theorem h84q_power_deriv_zero (n : ℕ) (hn : 1 < n) :
    deriv (fun z : ℂ => z ^ n) 0 = 0 := by
  rw [deriv_pow_field]
  have hn' : n - 1 ≠ 0 := by omega
  rw [zero_pow hn', mul_zero]

/-- In a constructed linearizing coordinate, equal power values are precisely
the orbits of the original action on the common invariant source. -/
theorem h84q_linearized_power_fiber {H : Type*} [Group H] [Fintype H]
    (τ : H →* Equiv.Perm ℂ) (χ : H →* ℂˣ) (hχ : Function.Injective χ)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hInv : ∀ g, MapsTo (τ g) e.source e.source)
    (hLin : ∀ g w, w ∈ e.target → e (τ g (e.symm w)) = (χ g : ℂ) * w)
    {z w : ℂ} (hz : z ∈ e.source) (hw : w ∈ e.source) :
    (e z) ^ Fintype.card H = (e w) ^ Fintype.card H ↔
      ∃ g : H, τ g z = w := by
  have hCoord : ∀ g, e (τ g z) = (χ g : ℂ) * e z := by
    intro g
    have h := hLin g (e z) (e.mapsTo hz)
    rw [e.left_inv hz] at h
    exact h
  constructor
  · intro hpow
    obtain ⟨g, hg⟩ := (h84q_power_fiber_iff_orbit χ hχ (e z) (e w)).mp hpow
    refine ⟨g, e.injOn (hInv g hz) hw ?_⟩
    exact (hCoord g).trans hg.symm
  · rintro ⟨g, rfl⟩
    rw [hCoord g, mul_pow, h84q_character_pow_card χ g, one_mul]

/-- The local power model is obtained from a true effective analytic surface action.
The invariant chart and linearization are the already constructed ones; the new
power map has exactly the original action orbits as its fibers. -/
theorem h84q_surface_exists_power_model
    {H X : Type*} [Group H] [Finite H] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : H →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hFix : ∀ g, ρ g p = p)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (V : Set X) (U : Set ℂ) (τ : H →* Equiv.Perm ℂ) (χ : H →* ℂˣ)
      (e : OpenPartialHomeomorph ℂ ℂ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ (chartAt ℂ p).source ∧
      (∀ g, MapsTo (ρ g) V V) ∧ U = (chartAt ℂ p) '' V ∧
      (∀ g y, y ∈ V → τ g ((chartAt ℂ p) y) = (chartAt ℂ p) (ρ g y)) ∧
      Function.Injective χ ∧
      (chartAt ℂ p) p ∈ e.source ∧ e.source ⊆ U ∧ e ((chartAt ℂ p) p) = 0 ∧
      AnalyticOnNhd ℂ (fun z => (e z) ^ Nat.card H) e.source ∧
      (∀ g, MapsTo (τ g) e.source e.source) ∧
      (∀ z ∈ e.source, ∀ w ∈ e.source,
        (e z) ^ Nat.card H = (e w) ^ Nat.card H ↔ ∃ g : H, τ g z = w) := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨V, U, τ, χ, e, hVo, hpV, hV, hVI, hUeq, _hUo, _hUpc, _hpU,
    hChart, _hχDeriv, hχ, hpE, hEU, he0, _hDe, hAe, _hAi, hInv, _hTarget, hLin⟩ :=
    h84b_surface_exists_linearized_action ρ hρ p hFix hHol
  refine ⟨V, U, τ, χ, e, hVo, hpV, hV, hVI, hUeq, hChart, hχ,
    hpE, hEU, he0, hAe.pow (Nat.card H), hInv, ?_⟩
  intro z hz w hw
  rw [Nat.card_eq_fintype_card]
  exact h84q_linearized_power_fiber τ χ hχ e hInv hLin hz hw

end LiZhongQC

