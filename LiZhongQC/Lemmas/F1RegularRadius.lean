import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.SchottkyDirectD2

/-! A2 regular radius producer: source-only candidate; no compiler has been run. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Positive height and nonnegative hyperbolic radius are determined by b=h*cosh R and r=h*sinh R.
Only the radius conclusion is needed; no existence of a circle is being assumed geometrically. -/
theorem ft1gar_radius_eq_of_circle_parameters {a b R S : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : a * Real.cosh R = b * Real.cosh S)
    (hs : a * Real.sinh R = b * Real.sinh S) : R = S := by
  have ha2 : a ^ 2 = (a * Real.cosh R) ^ 2 - (a * Real.sinh R) ^ 2 := by
    linear_combination -a ^ 2 * Real.cosh_sq_sub_sinh_sq R
  have hb2 : b ^ 2 = (b * Real.cosh S) ^ 2 - (b * Real.sinh S) ^ 2 := by
    linear_combination -b ^ 2 * Real.cosh_sq_sub_sinh_sq S
  have hab2 : a ^ 2 = b ^ 2 := by rw [ha2, hb2, hc, hs]
  have hab : a = b := by nlinarith
  have hcosh : Real.cosh R = Real.cosh S := by
    rw [hab] at hc
    exact (mul_left_cancel₀ hb.ne') hc
  exact Real.cosh_injOn hR hS hcosh

/-- Three distinct points lie on hyperbolic spheres of at most one nonnegative radius.
No assumption of an existing circumcircle for an arbitrary triple is made. -/
theorem ft1gar_circumradius_unique {a b c x y : UpperHalfPlane} {R S : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hxa : dist x a = R) (hxb : dist x b = R) (hxc : dist x c = R)
    (hya : dist y a = S) (hyb : dist y b = S) (hyc : dist y c = S) : R = S := by
  have hax : dist (a : ℂ) (x.center R : ℂ) = x.im * Real.sinh R :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hbx : dist (b : ℂ) (x.center R : ℂ) = x.im * Real.sinh R :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hcx : dist (c : ℂ) (x.center R : ℂ) = x.im * Real.sinh R :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hay : dist (a : ℂ) (y.center S : ℂ) = y.im * Real.sinh S :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hby : dist (b : ℂ) (y.center S : ℂ) = y.im * Real.sinh S :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hcy : dist (c : ℂ) (y.center S : ℂ) = y.im * Real.sinh S :=
    UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (by rwa [dist_comm])
  have hcent : (x.center R : ℂ) = (y.center S : ℂ) := by
    by_contra hne
    have habC : (a : ℂ) ≠ (b : ℂ) := fun h => hab (UpperHalfPlane.ext h)
    rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        (V := ℂ) Complex.finrank_real_complex hne habC hax hbx hcx hay hby hcy with h | h
    · exact hac (UpperHalfPlane.ext h.symm)
    · exact hbc (UpperHalfPlane.ext h.symm)
  have him : x.im * Real.cosh R = y.im * Real.cosh S := by
    exact congrArg Complex.im hcent
  have hrad : x.im * Real.sinh R = y.im * Real.sinh S := by
    rw [← hax, ← hay, hcent]
  exact ft1gar_radius_eq_of_circle_parameters x.im_pos y.im_pos hR hS him hrad

/-- A countable set of centres has arbitrarily large positive regular radii.
The conclusion excludes actual pair tangencies and actual triples, not merely ncard junk. -/
theorem ft1gar_regular_radius_countable {O : Set UpperHalfPlane} (hO : O.Countable) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ a ∈ O, ∀ b ∈ O, a ≠ b → dist a b ≠ 2 * R) ∧
      (∀ (τ a b c : UpperHalfPlane), a ∈ O → b ∈ O → c ∈ O →
        dist τ a = R → dist τ b = R → dist τ c = R → a = b ∨ a = c ∨ b = c) := by
  classical
  let B : UpperHalfPlane → UpperHalfPlane → UpperHalfPlane → Set ℝ := fun a b c =>
    {R | a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 0 ≤ R ∧
      ∃ τ : UpperHalfPlane, dist τ a = R ∧ dist τ b = R ∧ dist τ c = R}
  have hB : ∀ a b c, (B a b c).Countable := by
    intro a b c
    apply Set.Subsingleton.countable
    intro R hR S hS
    obtain ⟨hab, hac, hbc, hR0, x, hxa, hxb, hxc⟩ := hR
    obtain ⟨-, -, -, hS0, y, hya, hyb, hyc⟩ := hS
    exact ft1gar_circumradius_unique hab hac hbc hR0 hS0 hxa hxb hxc hya hyb hyc
  let B₃ : Set ℝ := ⋃ a ∈ O, ⋃ b ∈ O, ⋃ c ∈ O, B a b c
  have hB₃ : B₃.Countable := hO.biUnion fun a _ =>
    hO.biUnion fun b _ => hO.biUnion fun c _ => hB a b c
  let B₂ : Set ℝ := (fun p : UpperHalfPlane × UpperHalfPlane => dist p.1 p.2 / 2) '' (O ×ˢ O)
  have hB₂ : B₂.Countable := (hO.prod hO).image _
  have hbad : (B₂ ∪ B₃).Countable := hB₂.union hB₃
  let M : ℝ := max R₀ 0
  have hex : ∃ R : ℝ, R ∈ Ioo M (M + 1) ∧ R ∉ B₂ ∪ B₃ := by
    by_contra h
    push_neg at h
    have hc : (Ioo M (M + 1)).Countable := hbad.mono h
    have hh := (Cardinal.Real.Ioo_countable_iff (x := M) (y := M + 1)).mp hc
    linarith
  obtain ⟨R, hRI, hRbad⟩ := hex
  have hR₀ : R₀ < R := (le_max_left R₀ 0).trans_lt hRI.1
  have hRpos : 0 < R := (le_max_right R₀ 0).trans_lt hRI.1
  refine ⟨R, hR₀, hRpos, ?_, ?_⟩
  · intro a ha b hb hab hdist
    have _ := hab
    apply hRbad
    apply Or.inl
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    dsimp
    linarith
  · intro τ a b c ha hb hc hτa hτb hτc
    by_cases hab : a = b
    · exact Or.inl hab
    by_cases hac : a = c
    · exact Or.inr (Or.inl hac)
    by_cases hbc : b = c
    · exact Or.inr (Or.inr hbc)
    exfalso
    apply hRbad
    apply Or.inr
    exact mem_biUnion ha (mem_biUnion hb (mem_biUnion hc
      (show R ∈ B a b c from ⟨hab, hac, hbc, hRpos.le, τ, hτa, hτb, hτc⟩)))

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Above any chosen radius one can choose a regular equal-radius orbit-circle
arrangement: no pair is externally tangent and no point lies on three circles with
different centres. Coincident centres from plus/minus matrices are counted only once. -/
theorem ft1ga_regular_orbit_radius (hΓ : IsFuchsian Γ) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ γ ∈ Γ, ∀ δ ∈ Γ,
        γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R) ∧
      (∀ τ : UpperHalfPlane,
        {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
        {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2) := by
  classical
  let O : Set UpperHalfPlane := {z | ∃ γ ∈ Γ, z = γ • UpperHalfPlane.I}
  have hOeq : O = (fun γ : Matrix.SpecialLinearGroup (Fin 2) ℝ => γ • UpperHalfPlane.I) '' (Γ : Set _) := by
    ext z
    constructor
    · intro hz
      obtain ⟨γ, hγ, hzγ⟩ := hz
      exact ⟨γ, hγ, hzγ.symm⟩
    · intro hz
      obtain ⟨γ, hγ, hγz⟩ := hz
      exact ⟨γ, hγ, hγz.symm⟩
  have hO : O.Countable := by
    rw [hOeq]
    exact (s82dx_countable hΓ UpperHalfPlane.I).image _
  obtain ⟨R, hR₀, hRpos, hpair, htriple⟩ := ft1gar_regular_radius_countable hO R₀
  refine ⟨R, hR₀, hRpos, ?_, ?_⟩
  · intro γ hγ δ hδ hne
    exact hpair _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩ hne
  · intro τ
    let L : Set UpperHalfPlane := {z | z ∈ O ∧ dist τ z = R}
    -- Finiteness is established before ncard is used, independently of triple exclusion.
    have hfin : L.Finite := by
      apply ((s82dx_finite_ball hΓ UpperHalfPlane.I τ R).image
        (fun γ : Matrix.SpecialLinearGroup (Fin 2) ℝ => γ • UpperHalfPlane.I)).subset
      intro z hz
      obtain ⟨γ, hγ, hzγ⟩ := hz.1
      refine ⟨γ, ⟨hγ, ?_⟩, hzγ.symm⟩
      rw [← hzγ, dist_comm, hz.2]
    change L.Finite ∧ L.ncard ≤ 2
    refine ⟨hfin, ?_⟩
    by_contra hlarge
    have hgt : 2 < L.ncard := Nat.lt_of_not_ge hlarge
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).mp hgt
    rcases htriple τ a b c ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h

end LiZhongQC
